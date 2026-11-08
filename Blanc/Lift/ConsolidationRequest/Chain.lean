import Blanc.Lift.ConsolidationRequest.Delivery
import Blanc.Lift.RequestQueue.Link

/-!
# The EIP-7251 contract over a kept history

`linked` places the consolidation contract in the shared chain link (`RequestQueue.Link`): a kept user frame is a
`Frame.submission` or `Frame.feeRead` (`exec_user_frame`), the request phase's call is a `Frame.system`, and a call's
return data is whole records (`drained_records`). `history_delivered` is the delivery over a history at covered forks
from storage representing a queue: storage at the end represents the model's queue, which holds exactly the
submissions not yet delivered, the blocks' type 2 requests are exactly the delivered records' bytes, and each block's
type 2 requests are whole records.

The SYSTEM_ADDRESS exclusion is discharged from the history's premises (no code there at the start, no sender,
authority or creation at it), as for EIP-8282.

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.
-/

namespace Blanc.Lift.ConsolidationRequest

open Jaune
open BuilderRequest (QueueState queueBase)
open RequestQueue (Step pushed Holds Delivered)
open RequestSystem
open SystemExecution.ConsolidationRequest.Amsterdam (sysShape)
open RequestQueue.Link (Linked kept blockDelivered)

/-- The record a kept frame at the contract submits: a caller other than the system with 96 calldata bytes gives
its caller and calldata, and nothing else gives one. -/
def keptRecord (f : Exec.Frame) : Option Record :=
  if h : f.sevm.caller ≠ systemAddress ∧ f.sevm.data.length = 96 then some (recordOf f.sevm h.2) else none

/-- The bytes a call returns for one record are a record's bytes. -/
theorem recordBytes_record (rd : B256 → B256) (h i : B256) : ∃ r : Record, recordBytes rd h i = r.out := by
  refine ⟨⟨(rd (SystemExecution.ConsolidationRequest.Amsterdam.recordKey h i)).toAdr,
    (rd (1 + SystemExecution.ConsolidationRequest.Amsterdam.recordKey h i)).toBytes ++
      (rd (2 + SystemExecution.ConsolidationRequest.Amsterdam.recordKey h i)).toBytes ++
      (rd (3 + SystemExecution.ConsolidationRequest.Amsterdam.recordKey h i)).toBytes,
    by simp only [List.length_append, B256.length_toBytes]⟩, ?_⟩
  unfold recordBytes Record.out
  have ha : (rd (SystemExecution.ConsolidationRequest.Amsterdam.recordKey h i) <<< 96).toBytes.sliceD 0 20 0 =
      (rd (SystemExecution.ConsolidationRequest.Amsterdam.recordKey h i)).toAdr.toBytes := by
    unfold List.sliceD
    rw [List.drop_zero, List.takeD_eq_take _ (by rw [B256.length_toBytes]; omega),
      WordByteCodecs.shift96_take20_toAdr_bytes]
  rw [ha]
  simp only [List.append_assoc]

/-- **A call's return data is whole records**, from any storage. -/
theorem drained_records (rd : B256 → B256) : ∃ rs : List Record, drained rd = rs.flatMap Record.out := by
  refine ⟨(List.range (drainCount sysShape.cap.word (rd 2) (rd 3)).toNat).map
    fun i => Classical.choose (recordBytes_record rd (rd 2) i.toB256), ?_⟩
  rw [List.flatMap_map]
  unfold drained RequestSystem.SysOutput.drained
  congr 1
  funext i
  exact Classical.choose_spec (recordBytes_record rd (rd 2) i.toB256)

/-- The consolidation contract's place in the chain link: type 2, every kept frame a step of `Frame`. -/
def linked : Linked queue where
  address := consolidationRequestPredeployAddress
  code := consolidationRequestCode
  ty := 2
  member := member
  runnable := ⟨by decide +kernel, by decide +kernel⟩
  beacon := by decide
  history := by decide
  ty_ne := by decide
  listed := by decide
  record? := keptRecord
  system_none := fun _ h => dite_eq_right fun c => c.1 h
  user := fun {f} {stat} entry fork caller => by
    obtain ⟨orig, e⟩ := entry
    obtain ⟨pc, sevm, pre, out, run, committed⟩ := f
    obtain ⟨hpc, target, code, stack, size, wf, hstat, dlen⟩ := e
    dsimp only at hpc target code stack size wf hstat dlen caller ⊢
    subst hpc
    cases out with
    | error err => simp only [Execution.commits, Bool.false_eq_true] at committed
    | ok post =>
        have hc : CoveredFork sevm.benvStat.fork := by rw [hstat]; exact fork
        cases exec_user_frame code hc stack size wf dlen caller run with
        | submission i o law =>
            refine ⟨(Frame.submission sevm pre post i o hc target caller law).toStep, rfl, rfl, ?_, rfl⟩
            change [recordOf sevm law.length] = (keptRecord ⟨0, sevm, pre, .ok post, run, committed⟩).toList
            unfold keptRecord
            rw [dite_eq_left ⟨caller, law.length⟩]
            rfl
        | feeRead i o empty law =>
            refine ⟨(Frame.feeRead sevm pre post i o hc target caller law).toStep, rfl, rfl, ?_, rfl⟩
            change [] = (keptRecord ⟨0, sevm, pre, .ok post, run, committed⟩).toList
            unfold keptRecord
            rw [dite_eq_right fun c => by
              have := c.2
              change sevm.data.length = 96 at this
              rw [empty] at this
              cases this]
            rfl
  system := fun {benv} {post} {out} fork code run => by
    refine ⟨(Frame.system benv post out fork code run).toStep, rfl, rfl, rfl, rfl, ?_⟩
    obtain ⟨out', run', -, -, ret⟩ := system_call_ok fork code
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj (run.symm.trans run'))
    rw [ret]
    exact drained_records _

/-- **EIP-7251 delivery over a kept history at covered forks.** From the canonical code and storage representing a
queue at the start, no code at SYSTEM_ADDRESS, no sender, authority or creation at it, and the word range over what
the history submits: storage at the end represents the model's queue, which holds exactly the submissions not yet
delivered, the blocks' type 2 requests are exactly the delivered records' bytes, in order, and each block's type 2
requests are whole records. -/
theorem history_delivered {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    (h : KeptHistory cfg start blocks stop) (covered : ∀ b ∈ blocks, CoveredFork b.fork)
    (code : start.state.getCode consolidationRequestPredeployAddress = consolidationRequestCode)
    (empty : start.state.getCode systemAddress = ByteArray.empty)
    (senders : ∀ b ∈ blocks, NoSenderAt systemAddress b.run.senders)
    (authorities : ∀ b ∈ blocks, NoAuthorityAt systemAddress b.run.senders)
    (creates : ∀ b ∈ blocks, NoCreateAt systemAddress b.run.roots)
    {st : QueueState Record} (rep : Holds queue (start.state.getStor consolidationRequestPredeployAddress) st)
    (slots : queueBase 4 (st.tail + ((kept consolidationRequestPredeployAddress blocks).filterMap keptRecord).length)
      ≤ 2 ^ 256)
    (count : st.count + ((kept consolidationRequestPredeployAddress blocks).filterMap keptRecord).length < 2 ^ 256) :
    ∃ k, ∃ st' : QueueState Record,
      Holds queue (stop.state.getStor consolidationRequestPredeployAddress) st' ∧
      st'.queue = (st.queue ++ (kept consolidationRequestPredeployAddress blocks).filterMap keptRecord).drop k ∧
      RequestQueue.Link.delivered 2 blocks =
        ((st.queue ++ (kept consolidationRequestPredeployAddress blocks).filterMap keptRecord).take k).flatMap
          Record.out ∧
      ∀ b ∈ blocks, ∃ rs : List Record, blockDelivered 2 b = rs.flatMap Record.out := by
  obtain ⟨steps, chain, subs, out, wholes⟩ :=
    RequestQueue.Link.history_chain linked h covered code empty senders authorities creates
  have hsub : RequestQueue.submissions steps = (kept consolidationRequestPredeployAddress blocks).filterMap keptRecord :=
    subs
  have d := chain.delivered rep (by rw [hsub]; exact slots) (by rw [hsub]; exact count)
  have queue := d.queue
  have output := d.output
  rw [hsub] at queue output
  rw [out] at output
  exact ⟨_, _, d.represents, queue, output, wholes⟩

end Blanc.Lift.ConsolidationRequest
