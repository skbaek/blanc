import Blanc.Lift.ConsolidationRequest.Chain
import Blanc.Lift.RequestQueue.Occurrence

/-! # EIP-7251 adapters for occurrence-indexed queue latency -/

namespace Blanc.Lift.ConsolidationRequest

open Jaune
open BuilderRequest (QueueState Represents queueSlot)
open RequestQueue

/-- Read the four stored words as the public 116-byte consolidation record. -/
def reading : RequestQueue.Occurrence.Reading queue where
  read := fun rd i =>
    (rd (queueSlot 4 i 0)).toAdr.toBytes ++ (rd (queueSlot 4 i 1)).toBytes ++
      (rd (queueSlot 4 i 2)).toBytes ++ (rd (queueSlot 4 i 3)).toBytes
  size := 116
  size_pos := by decide
  out_length := by
    intro r
    simp only [Record.out, Adr.toBytes, List.length_append, UInt32.length_toBytes,
      B128.length_toBytes, r.data_length]
  read_eq := by
    intro rd st rep i hi
    have live := rep.live i hi
    have w0 : rd (queueSlot 4 (st.head + i) 0) = st.queue[i].word 0 := live 0 (by decide)
    have w1 : rd (queueSlot 4 (st.head + i) 1) = st.queue[i].word 1 := live 1 (by decide)
    have w2 : rd (queueSlot 4 (st.head + i) 2) = st.queue[i].word 2 := live 2 (by decide)
    have w3 : rd (queueSlot 4 (st.head + i) 3) = st.queue[i].word 3 := live 3 (by decide)
    rw [w0, w1, w2, w3]
    change (st.queue[i].source.toB256).toAdr.toBytes ++ _ ++ _ ++ _ = st.queue[i].out
    rw [toAdr_toB256, List.append_assoc, List.append_assoc, ← List.append_assoc (Record.word _ 1).toBytes]
    exact congrArg (st.queue[i].source.toBytes ++ ·) (data_words _)

/-- User frames never drain; the request-phase system frame always drains. -/
theorem drainLinked : RequestQueue.Occurrence.DrainLinked linked where
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
            refine ⟨(Frame.submission sevm pre post i o hc target caller law).toStep,
              rfl, rfl, ?_, rfl, ?_⟩
            · change [recordOf sevm law.length] =
                (keptRecord ⟨0, sevm, pre, .ok post, run, committed⟩).toList
              unfold keptRecord
              rw [dite_eq_left ⟨caller, law.length⟩]
              rfl
            · intro next impossible
              cases impossible
        | feeRead i o empty law =>
            refine ⟨(Frame.feeRead sevm pre post i o hc target caller law).toStep,
              rfl, rfl, ?_, rfl, ?_⟩
            · change [] = (keptRecord ⟨0, sevm, pre, .ok post, run, committed⟩).toList
              unfold keptRecord
              rw [dite_eq_right fun c => by
                have := c.2
                change sevm.data.length = 96 at this
                rw [empty] at this
                cases this]
              rfl
            · intro next impossible
              cases impossible
  system := fun {benv} {post} {out} fork code run => by
    refine ⟨(Frame.system benv post out fork code run).toStep, rfl, rfl, rfl, rfl,
      ⟨sysExcess, rfl⟩, ?_⟩
    obtain ⟨out', run', -, -, ret⟩ := system_call_ok fork code
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj (run.symm.trans run'))
    rw [ret]
    exact drained_records _

end Blanc.Lift.ConsolidationRequest
