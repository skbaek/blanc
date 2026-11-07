import Blanc.Lift.BuilderRequest.ChainLink
import Blanc.Lift.BuilderRequest.Exit.Delivery

/-!
# The exit contract over a history

`history_delivers` is the public form: what the blocks output as builder exit requests is a prefix of what the kept
frames submitted, in order. `history_chain` is the proof-level form, on which `delivery`, `excess_dynamics` and
`later_quote` apply.

Retention only: no gas or liveness claim.
-/

namespace Blanc.Lift.BuilderRequest.Exit

open Jaune ChainLink
open Delivery
open Creation (address)

/-- The exit contract's place in the chain link. -/
def linked : Linked contract 4 where
  frames := frames
  code_eq := rfl
  classify := fun law => by
    cases law with
    | submission i o effect => exact .inl ⟨i, o, effect⟩
    | feeRead i o empty effect => exact .inr ⟨empty, i, o, effect⟩
  runnable := ⟨by decide +kernel, by decide +kernel⟩
  placed :=
    { precompile := KeptFork.forall (by decide) (by decide)
      beacon := by decide
      history := by decide }
  payload_ne := by decide
  ty_ne := by decide
  listed := by decide
  unlisted := fun f hf =>
    (by decide : ∀ f ∈ coveredForks, ∀ p ∈ f.ruleSet.requests, p.1 ≠ 4 ∧ p.2 ≠ address) f hf

/-- The records a history's kept frames at the contract submit, in order: a frame with the submission's calldata
length gives its record, the frame's caller as the source. -/
def submitted (blocks : List KeptBlock) : List Record :=
  (History.kept address blocks).filterMap fun f =>
    if h : f.sevm.data.length = 48 then some (recordOf f.sevm h) else none

/-- **Builder exit requests come out in order.** The bytes the blocks output as type 4 requests are a prefix of the
records the kept frames submitted, each in its output form, in order. -/
def DeliversInOrder (blocks : List KeptBlock) : Prop :=
  delivered 4 blocks <+: (submitted blocks).flatMap Record.out

variable {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}

/-- **The proof-level form.** From the deployed storage, the frames a history keeps at the contract are a chain of the
delivery sequence, one for one, whose output is the blocks' type 4 requests. So `delivery`, `excess_dynamics` and
`later_quote` hold of the history. -/
theorem history_chain (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = deployedStorage)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) :
    ∃ frames : List Frame, Chain deployedStorage frames (stop.state.getStor address) ∧
      Corresponds contract frames (History.kept address blocks) ∧ systemOutput frames = delivered 4 blocks := by
  have := ChainLink.history_chain linked h installed noSystemCode senders authorities creates
  rw [show start.state.getStor contract.address = deployedStorage from fresh] at this
  exact this

/-- **Exact delivery over a history at the exit contract.** From the code at its address on the deployed storage, what
the blocks output as type 4 requests is a prefix of what the kept frames submitted, in order. `few` is the word range,
stated on the count: a submission's fee can be 1 wei, so no budget of value below `2 ^ 256` bounds it. -/
theorem history_delivers (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = deployedStorage)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks)
    (few : (submitted blocks).length ≤ 2 ^ 64) : DeliversInOrder blocks := by
  obtain ⟨frames, chain, corr, out⟩ := history_chain h installed fresh noSystemCode senders authorities creates
  have hsub : Delivery.submissions frames = submitted blocks := corr.submissions
  obtain ⟨-, -, output⟩ := delivery chain (by rw [hsub]; omega)
  rw [hsub, out] at output
  unfold DeliversInOrder
  rw [output]
  exact take_flatMap_prefix _ _ _

/-! ## The fee over a history (O18, O21) -/

/-- The contract's target, as a number. -/
theorem target_toNat : contract.target.toNat = 2 := by decide

/-- **The exit contract's slot 0 is the inhibitor exactly while the history has kept nothing there.** It is deployed
inhibited, every user frame on the inhibitor reverts, and the first request call clears it for good: a history's system
calls have empty calldata. -/
theorem history_inhibited_iff (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = deployedStorage)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) (few : (submitted blocks).length ≤ 2 ^ 64) :
    (stop.state.getStor address).get 0 = B256.max ↔ History.kept address blocks = [] := by
  obtain ⟨frames, chain, corr, -⟩ := history_chain h installed fresh noSystemCode senders authorities creates
  have hsub : Delivery.submissions frames = submitted blocks := corr.submissions
  have range : 4 + 3 * (Delivery.submissions frames).length ≤ 2 ^ 256 := by rw [hsub]; omega
  have iff := (excess_dynamics chain range).1
  rw [Delivery.inhibitedAfter_requestPhase true corr.requestPhase] at iff
  rw [iff]
  generalize History.kept address blocks = kept at corr
  cases corr with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons m tail =>
      obtain ⟨latch, hsys⟩ := first_frame_system chain
      constructor
      · intro all
        have blocked := List.all_eq_true.mp ((Bool.true_and _).symm.trans all) (.system latch)
          (by rw [← hsys]; exact List.mem_cons_self)
        cases blocked
      · intro empty
        cases empty

/-- **The first frame a history keeps at the exit contract is a request call.** -/
theorem history_first_frame_system (h : KeptHistory cfg start blocks stop)
    (installed : start.state.getCode address = code) (fresh : start.state.getStor address = deployedStorage)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) {f : Exec.Frame} {rest : List Exec.Frame}
    (split : History.kept address blocks = f :: rest) : f.sevm.caller = systemAddress := by
  obtain ⟨frames, chain, corr, -⟩ := history_chain h installed fresh noSystemCode senders authorities creates
  rw [split] at corr
  obtain ⟨gs, g, hs, rfl, left, m, -⟩ := Corresponds.split (xs := []) corr
  cases left
  obtain ⟨latch, hsys⟩ := first_frame_system chain
  exact caller_of_keptEvent (m.event.symm.trans hsys)

/-- **Once anything is kept, the excess and count are at most what was submitted.** Slot 0 plus slot 1, in naturals, is
at most the number of submissions so far. -/
theorem history_excess_bound (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = deployedStorage)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) (few : (submitted blocks).length ≤ 2 ^ 64)
    (kept : History.kept address blocks ≠ []) :
    ((stop.state.getStor address).get 0).toNat + ((stop.state.getStor address).get 1).toNat ≤
      (submitted blocks).length := by
  obtain ⟨frames, chain, corr, -⟩ := history_chain h installed fresh noSystemCode senders authorities creates
  have hsub : Delivery.submissions frames = submitted blocks := corr.submissions
  have range : 4 + 3 * (Delivery.submissions frames).length ≤ 2 ^ 256 := by rw [hsub]; omega
  obtain ⟨he, hc⟩ := holds_slots (c := contract) (delivery chain range).1
  rw [he, hc, ← hsub]
  rcases (excess_dynamics chain range).2.1 with inhibited | bound
  · have stored : (stop.state.getStor address).get 0 = B256.max := by
      rw [← toB256_toNat ((stop.state.getStor address).get 0), he, inhibited]
      rfl
    exact absurd ((history_inhibited_iff h installed fresh noSystemCode senders authorities creates few).mp stored) kept
  · exact bound

/-- **A request call's excess update.** A kept frame with the system caller leaves `excess + count - 2` in slot 0, in
naturals, of the excess and count it found, and 0 on the inhibitor: the first call unlocks the contract. -/
theorem history_excess_update (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = deployedStorage)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) {xs ys : List Exec.Frame} {f : Exec.Frame}
    (split : History.kept address blocks = xs ++ f :: ys)
    (few : (xs.filterMap (submittedBy contract)).length ≤ 2 ^ 64) (caller : f.sevm.caller = systemAddress) :
    ((Devm.getStor f.post address).get 0).toNat =
      if excessAt address f = 2 ^ 256 - 1 then 0 else excessAt address f + countAt address f - 2 := by
  obtain ⟨frames, chain, corr, -⟩ := history_chain h installed fresh noSystemCode senders authorities creates
  rw [split] at corr
  have update := kept_excess_update chain corr deployed_represents (by show 4 + 3 * (0 + _) ≤ _; omega)
    (by show 0 + _ < _; omega) (by show _ + _ < _; rw [show load deployedQueue = 0 by decide]; omega) caller
  rw [target_toNat] at update
  exact update

/-- **A fee read in a history returns the fee the storage quotes.** With at most 2892 submissions before it, a kept
empty-calldata frame returns `fake_exponential(1, excess + max(0, count - 2), 17)` of the slots it found, as one word. -/
theorem history_fee_read (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = deployedStorage)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) {xs ys : List Exec.Frame} {f : Exec.Frame} {post : Devm}
    (split : History.kept address blocks = xs ++ f :: ys)
    (few : (xs.filterMap (submittedBy contract)).length ≤ 2892) (caller : f.sevm.caller ≠ systemAddress)
    (empty : f.sevm.data = []) (ran : f.out = .ok post) :
    post.output = (fakeExp 1 (excessAt address f + (countAt address f - 2)) 17).toB256.toBytes := by
  obtain ⟨frames, chain, corr, -⟩ := history_chain h installed fresh noSystemCode senders authorities creates
  rw [split] at corr
  exact kept_fee_read linked chain corr deployed_represents (by show 4 + 3 * (0 + _) ≤ _; omega)
    (by show 0 + _ < _; omega) (by decide) few caller empty ran

/-- **A submission in a history pays at least the fee the storage quotes.** A kept frame with a submission's calldata
length, with at most 2892 submissions before it, carries at least
`fake_exponential(1, excess + max(0, count - 2), 17)` of the slots it found. -/
theorem history_submission_pays (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = deployedStorage)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) {xs ys : List Exec.Frame} {f : Exec.Frame}
    (split : History.kept address blocks = xs ++ f :: ys)
    (few : (xs.filterMap (submittedBy contract)).length ≤ 2892) (length : f.sevm.data.length = 48) :
    fakeExp 1 (excessAt address f + (countAt address f - 2)) 17 ≤ f.sevm.value.toNat := by
  obtain ⟨frames, chain, corr, -⟩ := history_chain h installed fresh noSystemCode senders authorities creates
  rw [split] at corr
  have pays := kept_submission_pays chain corr deployed_represents (by show 4 + 3 * (0 + _) ≤ _; omega)
    (by show 0 + _ < _; omega) (by decide) few length
  unfold naturalFee at pays
  rw [target_toNat] at pays
  exact pays

/-- **A later fee read differs only by the submissions between.** With no system call from `f` up to a later fee read
`f'`, at most 2892 submissions before `f'`: `f'` returns the fee of the excess `f` found, and of the count `f` found plus
the submissions from `f` on. Nothing else in between moves it. -/
theorem history_later_fee_read (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = deployedStorage)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) {xs ys zs : List Exec.Frame} {f f' : Exec.Frame} {post : Devm}
    (split : History.kept address blocks = (xs ++ f :: ys) ++ f' :: zs)
    (few : ((xs ++ f :: ys).filterMap (submittedBy contract)).length ≤ 2892)
    (users : ∀ x ∈ f :: ys, x.sevm.caller ≠ systemAddress) (caller : f'.sevm.caller ≠ systemAddress)
    (empty : f'.sevm.data = []) (ran : f'.out = .ok post) :
    post.output = (fakeExp 1 (excessAt address f +
      (countAt address f + ((f :: ys).filterMap (submittedBy contract)).length - 2)) 17).toB256.toBytes := by
  obtain ⟨frames, chain, corr, -⟩ := history_chain h installed fresh noSystemCode senders authorities creates
  rw [split] at corr
  obtain ⟨he, hc⟩ := kept_later chain corr deployed_represents (by show 4 + 3 * (0 + _) ≤ _; omega)
    (by show 0 + _ < _; omega) users
  have read := kept_fee_read linked chain corr deployed_represents (by show 4 + 3 * (0 + _) ≤ _; omega)
    (by show 0 + _ < _; omega) (by decide) few caller empty ran
  rw [read]
  unfold naturalFee
  rw [he, hc]
  rfl

/-- **A submission paying the quote a kept fee read returned is admitted.** A later machine `b` holding the storage the
read found, with value covering the quote: the submission runs, at its stated charge and with its exact post state.
Frame level: gas sufficiency and the transaction envelope are not stated here. -/
theorem history_paying_quote_admitted (h : KeptHistory cfg start blocks stop)
    (installed : start.state.getCode address = code) (fresh : start.state.getStor address = deployedStorage)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) {f : Exec.Frame} {post : Devm} {q : B256}
    (mem : f ∈ History.kept address blocks) (caller : f.sevm.caller ≠ systemAddress) (empty : f.sevm.data = [])
    (ran : f.out = .ok post) (returned : post.output = q.toBytes) {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {l : StorageSteps sevm} (v : l.Valid) (same : Devm.getStor f.pre address = b.getStor address)
    (target : sevm.currentTarget = address) (hcode : sevm.code = code) (submitter : sevm.caller ≠ systemAddress)
    (hlen : sevm.data.length = 48) (dynamic : sevm.isStatic = false) (slack : gCallStipend < G)
    (pay : q.toNat ≤ sevm.value.toNat) :
    ∃ iterations, Nonempty (Exec 0 sevm (St b [] M (G + submissionGasOn l b M iterations))
      (.ok (Steps.submissionPost l (l.feeBase b) M (G + Steps.bodyRepay l (l.feeBase b) M)))) := by
  obtain ⟨frames, -, corr, -⟩ := history_chain h installed fresh noSystemCode senders authorities creates
  obtain ⟨g, m, hq⟩ := corr.quoted linked mem caller empty ran returned
  exact paying_quote_admitted v hq (m.before.trans same) target hcode submitter hlen dynamic slack pay

end Blanc.Lift.BuilderRequest.Exit
