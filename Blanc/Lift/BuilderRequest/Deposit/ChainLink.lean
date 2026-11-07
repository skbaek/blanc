import Blanc.Lift.BuilderRequest.ChainLink
import Blanc.Lift.BuilderRequest.Deposit.Delivery

/-!
# The deposit contract over a history

`history_delivers` is the public form: what the blocks output as builder deposit requests is a prefix of what the kept
frames submitted, in order. `history_chain` is the proof-level form, on which `delivery`, `excess_dynamics` and
`later_quote` apply.

Retention only: no gas or liveness claim.
-/

namespace Blanc.Lift.BuilderRequest.Deposit

open Jaune ChainLink
open Delivery
open Creation (address)

/-- The deposit contract's place in the chain link. -/
def linked : Linked contract 3 where
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
    (by decide : ∀ f ∈ coveredForks, ∀ p ∈ f.ruleSet.requests, p.1 ≠ 3 ∧ p.2 ≠ address) f hf

/-- The records a history's kept frames at the contract submit, in order: a frame with the submission's calldata
length gives its record. -/
def submitted (blocks : List KeptBlock) : List Record :=
  (History.kept address blocks).filterMap fun f =>
    if h : f.sevm.data.length = 184 then some (recordOf f.sevm h) else none

/-- **Builder deposit requests come out in order.** The bytes the blocks output as type 3 requests are a prefix of the
records the kept frames submitted, each in its output form, in order. -/
def DeliversInOrder (blocks : List KeptBlock) : Prop :=
  delivered 3 blocks <+: (submitted blocks).flatMap Record.out

variable {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}

/-- **The proof-level form.** From the deployed storage, the frames a history keeps at the contract are a chain of the
delivery sequence, one for one, whose output is the blocks' type 3 requests. So `delivery`, `excess_dynamics` and
`later_quote` hold of the history. -/
theorem history_chain (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = Stor.empty)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) :
    ∃ frames : List Frame, Chain Stor.empty frames (stop.state.getStor address) ∧
      Corresponds contract frames (History.kept address blocks) ∧ systemOutput frames = delivered 3 blocks := by
  have := ChainLink.history_chain linked h installed noSystemCode senders authorities creates
  rw [show start.state.getStor contract.address = Stor.empty from fresh] at this
  exact this

/-- **Exact delivery over a history at the deposit contract.** From the code at its address on the deployed storage,
what the blocks output as type 3 requests is a prefix of what the kept frames submitted, in order. `budget` is the word
range: all the value the kept frames at the contract carry is at most `2 ^ 256` wei, far above all the ether that
exists, and each submission carries at least 1 ETH (`range_of_budget`). -/
theorem history_delivers (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = Stor.empty)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks)
    (budget : History.paid address blocks ≤ 2 ^ 256) : DeliversInOrder blocks := by
  obtain ⟨frames, chain, corr, out⟩ := history_chain h installed fresh noSystemCode senders authorities creates
  obtain ⟨-, -, output⟩ := delivery_of_budget chain (corr.value_le.trans budget)
  have hsub : Delivery.submissions frames = submitted blocks := corr.submissions
  rw [hsub, out] at output
  unfold DeliversInOrder
  rw [output]
  exact take_flatMap_prefix _ _ _

/-! ## The fee over a history (O18, O21) -/

/-- The contract's target, as a number. -/
theorem target_toNat : contract.target.toNat = 8 := by decide

/-- **The deposit contract is never inhibited after a history.** A history's system calls are the request phase's, with
empty calldata, so slot 0 is never the inhibitor. -/
theorem history_not_inhibited (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = Stor.empty)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) (budget : History.paid address blocks ≤ 2 ^ 256) :
    (stop.state.getStor address).get 0 ≠ B256.max := by
  obtain ⟨frames, chain, corr, -⟩ := history_chain h installed fresh noSystemCode senders authorities creates
  intro inhibited
  have after := (excess_dynamics chain (range_of_budget (corr.value_le.trans budget))).1.mp inhibited
  rw [Delivery.inhibitedAfter_requestPhase false corr.requestPhase] at after
  cases after

/-- **The excess and count a history leaves are at most what it submitted.** Slot 0 plus slot 1, in naturals, is at most
the number of submissions so far. -/
theorem history_excess_bound (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = Stor.empty)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) (budget : History.paid address blocks ≤ 2 ^ 256) :
    ((stop.state.getStor address).get 0).toNat + ((stop.state.getStor address).get 1).toNat ≤
      (submitted blocks).length := by
  obtain ⟨frames, chain, corr, -⟩ := history_chain h installed fresh noSystemCode senders authorities creates
  have range := range_of_budget (corr.value_le.trans budget)
  have hsub : Delivery.submissions frames = submitted blocks := corr.submissions
  obtain ⟨he, hc⟩ := holds_slots (c := contract) (delivery chain range).1
  rw [he, hc, ← hsub]
  rcases (excess_dynamics chain range).2.1 with inhibited | bound
  · have stored : (stop.state.getStor address).get 0 = B256.max := by
      rw [← toB256_toNat ((stop.state.getStor address).get 0), he, inhibited]
      rfl
    exact absurd stored (history_not_inhibited h installed fresh noSystemCode senders authorities creates budget)
  · exact bound

/-- **Before the first system call slot 0 stays 0.** With no kept frame having the system caller, nothing has moved the
excess. -/
theorem history_excess_zero (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = Stor.empty)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) (budget : History.paid address blocks ≤ 2 ^ 256)
    (users : ∀ x ∈ History.kept address blocks, x.sevm.caller ≠ systemAddress) :
    (stop.state.getStor address).get 0 = 0 := by
  obtain ⟨frames, chain, corr, -⟩ := history_chain h installed fresh noSystemCode senders authorities creates
  exact (excess_dynamics chain (range_of_budget (corr.value_le.trans budget))).2.2 (corr.noSystem users)

/-- **A request call's excess update.** A kept frame with the system caller leaves `excess + count - 8` in slot 0, in
naturals, of the excess and count it found; on the inhibitor it would leave 0. -/
theorem history_excess_update (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = Stor.empty)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) {xs ys : List Exec.Frame} {f : Exec.Frame}
    (split : History.kept address blocks = xs ++ f :: ys)
    (few : (xs.filterMap (submittedBy contract)).length ≤ 2 ^ 64) (caller : f.sevm.caller = systemAddress) :
    ((Devm.getStor f.post address).get 0).toNat =
      if excessAt address f = 2 ^ 256 - 1 then 0 else excessAt address f + countAt address f - 8 := by
  obtain ⟨frames, chain, corr, -⟩ := history_chain h installed fresh noSystemCode senders authorities creates
  rw [split] at corr
  have update := kept_excess_update chain corr deployed_represents (by show 4 + 6 * (0 + _) ≤ _; omega)
    (by show 0 + _ < _; omega) (by show _ + _ < _; rw [show load deployedQueue = 0 by decide]; omega) caller
  rw [target_toNat] at update
  exact update

/-- **A fee read in a history returns the fee the storage quotes.** With at most 2892 submissions before it, a kept
empty-calldata frame returns `fake_exponential(1, excess + max(0, count - 8), 17)` of the slots it found, as one word. -/
theorem history_fee_read (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = Stor.empty)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) {xs ys : List Exec.Frame} {f : Exec.Frame} {post : Devm}
    (split : History.kept address blocks = xs ++ f :: ys)
    (few : (xs.filterMap (submittedBy contract)).length ≤ 2892) (caller : f.sevm.caller ≠ systemAddress)
    (empty : f.sevm.data = []) (ran : f.out = .ok post) :
    post.output = (fakeExp 1 (excessAt address f + (countAt address f - 8)) 17).toB256.toBytes := by
  obtain ⟨frames, chain, corr, -⟩ := history_chain h installed fresh noSystemCode senders authorities creates
  rw [split] at corr
  exact kept_fee_read linked chain corr deployed_represents (by show 4 + 6 * (0 + _) ≤ _; omega)
    (by show 0 + _ < _; omega) (by decide) few caller empty ran

/-- **The fee at count `i`, in a history.** With `i` submissions kept before a fee read, at most 2892, and no system
call among them: the read returns `fake_exponential(1, max(0, i - 8), 17)`, as one word. -/
theorem history_fee_at_count (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = Stor.empty)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) {xs ys : List Exec.Frame} {f : Exec.Frame} {post : Devm}
    (split : History.kept address blocks = xs ++ f :: ys)
    (few : (xs.filterMap (submittedBy contract)).length ≤ 2892)
    (users : ∀ x ∈ xs, x.sevm.caller ≠ systemAddress) (caller : f.sevm.caller ≠ systemAddress)
    (empty : f.sevm.data = []) (ran : f.out = .ok post) :
    post.output = (quotedFee (xs.filterMap (submittedBy contract)).length).toB256.toBytes := by
  obtain ⟨frames, chain, corr, -⟩ := history_chain h installed fresh noSystemCode senders authorities creates
  rw [split] at corr
  obtain ⟨he, hc⟩ := kept_slots chain corr deployed_represents (by show 4 + 6 * (0 + _) ≤ _; omega)
    (by show 0 + _ < _; omega) users
  have read := kept_fee_read linked chain corr deployed_represents (by show 4 + 6 * (0 + _) ≤ _; omega)
    (by show 0 + _ < _; omega) (by decide) few caller empty ran
  rw [read]
  unfold naturalFee quotedFee
  rw [he, hc]
  show (fakeExp 1 (0 + (0 + _ - 8)) 17).toB256.toBytes = _
  rw [Nat.zero_add, Nat.zero_add]

/-- **A submission in a history pays at least the fee the storage quotes.** A kept frame with a submission's calldata
length, with at most 2892 submissions before it, carries at least
`fake_exponential(1, excess + max(0, count - 8), 17)` of the slots it found. -/
theorem history_submission_pays (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = Stor.empty)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) {xs ys : List Exec.Frame} {f : Exec.Frame}
    (split : History.kept address blocks = xs ++ f :: ys)
    (few : (xs.filterMap (submittedBy contract)).length ≤ 2892) (length : f.sevm.data.length = 184) :
    fakeExp 1 (excessAt address f + (countAt address f - 8)) 17 ≤ f.sevm.value.toNat := by
  obtain ⟨frames, chain, corr, -⟩ := history_chain h installed fresh noSystemCode senders authorities creates
  rw [split] at corr
  have pays := kept_submission_pays chain corr deployed_represents (by show 4 + 6 * (0 + _) ≤ _; omega)
    (by show 0 + _ < _; omega) (by decide) few length
  unfold naturalFee at pays
  rw [target_toNat] at pays
  exact pays

/-- **A later fee read differs only by the submissions between.** With no system call from `f` up to a later fee read
`f'`, at most 2892 submissions before `f'`: `f'` returns the fee of the excess `f` found, and of the count `f` found plus
the submissions from `f` on. Nothing else in between moves it. -/
theorem history_later_fee_read (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = Stor.empty)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) {xs ys zs : List Exec.Frame} {f f' : Exec.Frame} {post : Devm}
    (split : History.kept address blocks = (xs ++ f :: ys) ++ f' :: zs)
    (few : ((xs ++ f :: ys).filterMap (submittedBy contract)).length ≤ 2892)
    (users : ∀ x ∈ f :: ys, x.sevm.caller ≠ systemAddress) (caller : f'.sevm.caller ≠ systemAddress)
    (empty : f'.sevm.data = []) (ran : f'.out = .ok post) :
    post.output = (fakeExp 1 (excessAt address f +
      (countAt address f + ((f :: ys).filterMap (submittedBy contract)).length - 8)) 17).toB256.toBytes := by
  obtain ⟨frames, chain, corr, -⟩ := history_chain h installed fresh noSystemCode senders authorities creates
  rw [split] at corr
  obtain ⟨he, hc⟩ := kept_later chain corr deployed_represents (by show 4 + 6 * (0 + _) ≤ _; omega)
    (by show 0 + _ < _; omega) users
  have read := kept_fee_read linked chain corr deployed_represents (by show 4 + 6 * (0 + _) ≤ _; omega)
    (by show 0 + _ < _; omega) (by decide) few caller empty ran
  rw [read]
  unfold naturalFee
  rw [he, hc]
  rfl

/-- **A submission paying the quote a kept fee read returned is admitted.** A later machine `b` holding the storage the
read found, with at least 1 ETH credited and value covering the credit plus the quote (`Admitted`): the submission runs,
at its stated charge and with its exact post state. Frame level: gas sufficiency and the transaction envelope are not
stated here. -/
theorem history_paying_quote_admitted (h : KeptHistory cfg start blocks stop)
    (installed : start.state.getCode address = code) (fresh : start.state.getStor address = Stor.empty)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) {f : Exec.Frame} {post : Devm} {q : B256}
    (mem : f ∈ History.kept address blocks) (caller : f.sevm.caller ≠ systemAddress) (empty : f.sevm.data = [])
    (ran : f.out = .ok post) (returned : post.output = q.toBytes) {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {l : StorageSteps sevm} (v : l.Valid) (same : Devm.getStor f.pre address = b.getStor address)
    (target : sevm.currentTarget = address) (hcode : sevm.code = code) (submitter : sevm.caller ≠ systemAddress)
    (hlen : sevm.data.length = 184) (dynamic : sevm.isStatic = false) (slack : gCallStipend < G)
    (pay : Admitted sevm q) :
    ∃ iterations, Nonempty (Exec 0 sevm (St b [] M (G + submissionGasOn l b M iterations))
      (.ok (Steps.submissionPost l (l.feeBase b) M (G + Steps.bodyRepay l (l.feeBase b) M)))) := by
  obtain ⟨frames, -, corr, -⟩ := history_chain h installed fresh noSystemCode senders authorities creates
  obtain ⟨g, m, hq⟩ := corr.quoted linked mem caller empty ran returned
  exact paying_quote_admitted v hq (m.before.trans same) target hcode submitter hlen dynamic slack pay

/-- **A backlog's decay, in a history.** Kept frames with no system call among them, then `k ≥ 1` request calls: the
excess the last call leaves is `n - 8 * k` in naturals, for the `n` submissions before them. So `max(0, n - 8)` after the
first call, falling by 8 per call to 0. Any fork the history allows for the backlog, and fee reads among it. -/
theorem history_backlog_decay (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = Stor.empty)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) (budget : History.paid address blocks ≤ 2 ^ 256)
    {backlog calls : List Exec.Frame} (split : History.kept address blocks = backlog ++ calls)
    (users : ∀ x ∈ backlog, x.sevm.caller ≠ systemAddress) (requests : ∀ x ∈ calls, x.sevm.caller = systemAddress)
    (some : 0 < calls.length) :
    ((stop.state.getStor address).get 0).toNat =
      (backlog.filterMap (submittedBy contract)).length - 8 * calls.length := by
  obtain ⟨frames, chain, corr, -⟩ := history_chain h installed fresh noSystemCode senders authorities creates
  have range := range_of_budget (corr.value_le.trans budget)
  have rep := (delivery chain range).1
  rw [split] at corr
  obtain ⟨gs, hs, rfl, left, right⟩ := corr.split_append
  have hsub := left.submissions
  rw [← hsub]
  have none := left.noSystem users
  have hev := events_calls (Corresponds.calls right requests)
  have hlen : hs.length = calls.length := right.length_eq
  have hrange : (submissions gs).length ≤ (submissions (gs ++ hs)).length := by
    rw [submissions_append, List.length_append]
    omega
  obtain ⟨k, hk⟩ : ∃ k, hs.length = k + 1 := ⟨hs.length - 1, by omega⟩
  have he : (queueAfter deployedQueue gs).excess = 0 := excess_noSystem _ _ _ none
  have hcnt : (queueAfter deployedQueue gs).count = (submissions gs).length :=
    (count_noSystem _ _ _ none).trans (Nat.zero_add _)
  have hsplit : queueAfter deployedQueue (gs ++ hs) =
      replay 64 8 (queueAfter deployedQueue gs) (List.replicate (k + 1) (.system false)) := by
    show replay 64 8 deployedQueue (events (gs ++ hs)) = _
    rw [show events (gs ++ hs) = events gs ++ events hs from List.map_append .., replay_append, hev, hk]
    rfl
  obtain ⟨h1, -⟩ := replay_calls_excess 64 8 (queueAfter deployedQueue gs) k (by rw [he]; decide)
    (by rw [he, hcnt]; omega)
  rw [(holds_slots (c := contract) rep).1, hsplit, h1, he, hcnt, Nat.zero_add, ← hlen, hk]
  rfl

end Blanc.Lift.BuilderRequest.Deposit
