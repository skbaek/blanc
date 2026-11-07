import Blanc.Lift.BuilderRequest.Deposit.Frames
import Blanc.Lift.BuilderRequest.Deposit.Latch
import Blanc.FakeExponentialEval
import Blanc.FakeExponentialGrowth

/-!
# What a pre-fork deposit backlog can cost, and how fast it drains

Before Amsterdam no system call runs at the deposit contract, so its count only grows and slot 0 stays
wherever it was. At slot 0 = 0, the bytes quote count `i` the fee `fake_exponential(1, i - 8, 17)`, and a
submission pays that and at least 1 ETH.

**What this is.** A statement about the sequence of quoted fees. It bounds what a budget can buy: under the
stated sequence, a budget below `backlogCost n` does not reach count `n`.

**What this is not.** It does not say a chain history had that cost, or that anyone has that budget: the
budget is a premise. It does not rule out that slot 0 is nonzero, or that a transaction's other effects
matter. Deposits that do not run through these frames are outside it.
-/

namespace Blanc.Lift.BuilderRequest.Deposit

open Jaune
open RequestSystem
open Creation (address)

/-! ## The cost -/

/-- The natural fee the bytes quote at count `i` with slot 0 at zero: `targetExcess 8 0 i` is `i - 8`
(`quotedExcess_toNat`). -/
def quotedFee (i : Nat) : Nat := fakeExp 1 (i - 8) 17

/-- One ETH, in wei: the smallest credit a submission's guards admit. -/
def oneEther : Nat := 10 ^ 18

/-- The sum over `i < n` of the fee quoted at count `i` plus the 1 ETH minimum credit. -/
def backlogCost : Nat → Nat
  | 0 => 0
  | n + 1 => backlogCost n + (quotedFee n + oneEther)

/-- The total of the first `n` payments of a sequence. -/
def paidTotal (paid : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => paidTotal paid n + paid n

/-- `paid` is a sequence of `n` deposits' payments, each at least the fee quoted at its count plus 1 ETH. -/
def PaysQuotes (paid : Nat → Nat) (n : Nat) : Prop :=
  ∀ i, i < n → quotedFee i + oneEther ≤ paid i

theorem backlogCost_lt_succ (n : Nat) : backlogCost n < backlogCost (n + 1) := by
  have : 0 < oneEther := by decide
  simp only [backlogCost]
  omega

/-- `backlogCost` is strictly increasing. -/
theorem backlogCost_strictMono {m n : Nat} (h : m < n) : backlogCost m < backlogCost n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | rfl
    · exact (ih hlt).trans (backlogCost_lt_succ n)
    · exact backlogCost_lt_succ m

/-- Reaching count `n` under the stated sequence costs at least `backlogCost n`. -/
theorem backlogCost_le_paidTotal {paid : Nat → Nat} {n : Nat} (h : PaysQuotes paid n) :
    backlogCost n ≤ paidTotal paid n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h n (by omega)
    simp only [backlogCost, paidTotal]
    omega

/-- **A budget below `backlogCost n` does not reach count `n`**, or any higher count, under the stated
sequence. The budget is a premise; this says nothing about a chain's history. -/
theorem budget_cannot_reach {budget n m : Nat} (low : budget < backlogCost n) (hm : n ≤ m)
    {paid : Nat → Nat} (h : PaysQuotes paid m) : budget < paidTotal paid m := by
  have h1 := backlogCost_le_paidTotal h
  rcases Nat.lt_or_eq_of_le hm with hlt | rfl
  · have := backlogCost_strictMono hlt
    omega
  · omega

/-- **The cost grows exponentially**: it passes `2 ^ k` by count `34 * (k + 1) + 9`. A lower bound with a
simple rate, not the true one, which is `e ^ (1 / 17)` per deposit. -/
theorem two_pow_le_backlogCost (k : Nat) : 2 ^ k ≤ backlogCost (34 * (k + 1) + 9) := by
  have hfee : 2 ^ k ≤ quotedFee (34 * (k + 1) + 8) := by
    have := FakeExponential.factor_mul_pow_le 1 (34 * (k + 1) + 8 - 8) 17 k 2 (by decide) (by omega)
    rwa [Nat.one_mul] at this
  simp only [backlogCost]
  omega

/-! ## Evaluating the fee -/

/-- The evaluator's fee at excess `e`, within a fuel far above the recurrence's length here. -/
def feeEval (e : Nat) : Nat :=
  match FakeExponentialEval.runFuel 512 e 17 1 17 with
  | some (_, out) => out / 17
  | none => 0

/-- `backlogCost` by the evaluator. -/
def backlogEval : Nat → Nat
  | 0 => 0
  | n + 1 => backlogEval n + (feeEval (n - 8) + oneEther)

/-- Every excess the instance uses passes the check, and the evaluator returns on it. -/
theorem instance_checks :
    (List.range 974).all (fun e =>
      RequestFeeWord.noWrapCheck e 512 1 17 0 && (FakeExponentialEval.runFuel 512 e 17 1 17).isSome) = true := by
  decide +kernel

theorem instance_check {e : Nat} (he : e ≤ 973) :
    RequestFeeWord.noWrapCheck e 512 1 17 0 = true ∧ (FakeExponentialEval.runFuel 512 e 17 1 17).isSome = true := by
  have := List.all_eq_true.mp instance_checks e (List.mem_range.mpr (by omega))
  simpa only [Bool.and_eq_true] using this

/-- **The domain holds** at every excess the instance uses. -/
theorem noWrapDomain_instance {e : Nat} (he : e ≤ 973) :
    ∃ iterations, RequestFeeWord.NoWrapDomain e.toB256 iterations := by
  obtain ⟨iterations, output, run, safe⟩ := RequestFeeWord.noWrap_of_check (instance_check he).1
  refine ⟨iterations, output, ?_⟩
  rw [B256.toNat_toB256_of_lt (by omega)]
  exact ⟨run, safe⟩

theorem feeEval_eq {e : Nat} (he : e ≤ 973) : feeEval e = fakeExp 1 e 17 := by
  have hs := (instance_check he).2
  unfold feeEval
  rcases hr : FakeExponentialEval.runFuel 512 e 17 1 17 with _ | ⟨iterations, out⟩
  · rw [hr] at hs
    cases hs
  · have run := FakeExponentialEval.run_of_runFuel hr
    simp only
    rw [run.output_eq]
    rfl

theorem backlogEval_eq {n : Nat} (hn : n ≤ 982) : backlogEval n = backlogCost n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backlogEval, backlogCost, quotedFee]
    rw [ih (by omega), feeEval_eq (by omega)]

/-! ## The instance -/

/-- 120,000,000 ETH, in wei. -/
def instanceBudget : Nat := 120000000 * oneEther

theorem backlogEval_981 : backlogEval 981 ≤ instanceBudget ∧ instanceBudget < backlogEval 982 := by
  decide +kernel

/-- **The instance.** A sequence of `n` deposits paying the quotes fits in 120,000,000 ETH exactly when
`n ≤ 981`. The budget is a premise. -/
theorem instance_reach (n : Nat) :
    (∃ paid, PaysQuotes paid n ∧ paidTotal paid n ≤ instanceBudget) ↔ n ≤ 981 := by
  have h981 := backlogEval_981.1
  have h982 := backlogEval_981.2
  rw [backlogEval_eq (by omega)] at h981 h982
  constructor
  · rintro ⟨paid, hp, ht⟩
    by_contra hn
    have := budget_cannot_reach h982 (by omega) hp
    omega
  · intro hn
    refine ⟨fun i => quotedFee i + oneEther, fun _ _ => Nat.le_refl _, ?_⟩
    have same : ∀ m, paidTotal (fun i => quotedFee i + oneEther) m = backlogCost m := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => simp only [paidTotal, backlogCost, ih]
    rw [same]
    rcases Nat.lt_or_eq_of_le hn with hlt | rfl
    · have := backlogCost_strictMono hlt
      omega
    · exact h981

/-! ## The tie to the bytes -/

/-- The excess the bytes compute at count `i` and slot 0 at zero is `i - 8`. -/
theorem quotedExcess_toNat {i : Nat} (hi : i < 2 ^ 256) :
    (targetExcess 8 0 i.toB256).toNat = i - 8 := by
  rw [targetExcess_toNat, B256.toNat_toB256_of_lt hi, show (8 : B256).toNat = 8 by decide,
    show (0 : B256).toNat = 0 by decide, Nat.zero_add]
  exact Nat.mod_eq_of_lt (by omega)

/-- The word excess at count `i` is the word of `i - 8`. -/
theorem quotedExcess_eq {i : Nat} (hi : i < 2 ^ 256) : targetExcess 8 0 i.toB256 = (i - 8).toB256 := by
  apply B256.toNat_inj
  rw [quotedExcess_toNat hi, B256.toNat_toB256_of_lt (by omega)]

/-- **The word fee is the natural fee at every count the instance uses.** Any executed word recurrence on
the excess the bytes compute at count `i ≤ 981`, slot 0 at zero, quotes `quotedFee i`. -/
theorem word_fee_eq {i iterations : Nat} {finalOutput : B256} (hi : i ≤ 981)
    (quote : WordFakeExponential.Run (targetExcess 8 0 i.toB256) 17 1 17 0 iterations finalOutput) :
    (finalOutput / (17 : B256)).toNat = quotedFee i := by
  rw [quotedExcess_eq (by omega)] at quote
  obtain ⟨_, domain⟩ := noWrapDomain_instance (e := i - 8) (by omega)
  have := (domain.word_result quote).2.1
  rwa [B256.toNat_toB256_of_lt (by omega)] at this

/-- A fee read at count `i ≤ 981` with slot 0 at zero returns `quotedFee i`. -/
theorem feeRead_quoted {sevm : Sevm} {pre post : Devm} {i iterations : Nat} {finalOutput : B256}
    (hi : i ≤ 981) (slot0 : pre.getStorVal sevm.currentTarget 0 = 0)
    (slot1 : pre.getStorVal sevm.currentTarget 1 = i.toB256)
    (read : UserPath.FeeRead 8 sevm pre post iterations finalOutput) :
    (finalOutput / (17 : B256)).toNat = quotedFee i := by
  have q := read.quote
  rw [storedExcess, slot0, slot1] at q
  exact word_fee_eq hi q

/-- **A submission at count `i ≤ 981` with slot 0 at zero pays at least the quote and 1 ETH**: the frame's
value is what `PaysQuotes` asks of `paid i`. -/
theorem submission_pays {sevm : Sevm} {l : StorageSteps sevm} {pre post : Devm} {i iterations : Nat} {finalOutput : B256}
    (hi : i ≤ 981) (slot0 : pre.getStorVal sevm.currentTarget 0 = 0)
    (slot1 : pre.getStorVal sevm.currentTarget 1 = i.toB256)
    (sub : SubmittedOn l pre post iterations finalOutput) :
    quotedFee i + oneEther ≤ sevm.value.toNat := by
  have q := sub.quote
  rw [storedExcess, slot0, slot1] at q
  have hfee := word_fee_eq hi q
  have h1 := sub.admitted.credited
  have h2 := sub.admitted.covered
  rw [hfee] at h2
  simp only [oneEther]
  omega

/-! ## The drain -/

/-- A call's drain, by length. -/
theorem drainedState_length {Record : Type} (cap : Nat) (target : B256) (st : QueueState Record) :
    (drainedState cap target st).queue.length = st.queue.length - cap := by
  unfold drainedState
  dsimp only
  split
  · simp only [List.length_nil]
    omega
  · simp only [List.length_drop]

/-- Repeated drains take `cap` records each. -/
theorem drained_iterate_length {Record : Type} (cap : Nat) (target : B256) (st : QueueState Record) (k : Nat) :
    ((drainedState cap target)^[k] st).queue.length = st.queue.length - k * cap := by
  induction k with
  | zero => simp only [Function.iterate_zero, id, Nat.zero_mul, Nat.sub_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply', drainedState_length, ih, Nat.add_mul, Nat.one_mul, Nat.sub_sub]

/-- **Repeated drains empty a queue of length `n` in `⌈n/64⌉` steps**, here `(n + 63) / 64`. -/
theorem drain_empties {Record : Type} (target : B256) (st : QueueState Record) :
    ((drainedState 64 target)^[(st.queue.length + 63) / 64] st).queue = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [drained_iterate_length]
  omega

/-- **And not fewer.** -/
theorem drain_not_fewer {Record : Type} (target : B256) (st : QueueState Record) {k : Nat}
    (hk : k < (st.queue.length + 63) / 64) : ((drainedState 64 target)^[k] st).queue ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [drained_iterate_length, List.length_nil] at this
  omega

/-- A queue of at most 981 records empties within 16 steps. -/
theorem drain_within_16 {n : Nat} (hn : n ≤ 981) : (n + 63) / 64 ≤ 16 := by omega

/-- A call's post state, as a function of the state. -/
def drainStep (σ : State) : State := sysState sysShape σ address

/-- **Repeated empty-calldata system calls drain the queue.** With no new submissions, `k` calls, each at
the state the last left, succeed, and their post storage represents the queue after `k` drains. -/
theorem system_calls_drain {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode address = code) {st : QueueState Record}
    (rep : Represents 6 Record.word (storOf benv.state address) st) (k : Nat) :
    Represents 6 Record.word (storOf (drainStep^[k] benv.state) address)
        ((drainedState 64 8)^[k] st) ∧
      (drainStep^[k] benv.state).getCode address = code ∧
      ∀ j, j < k → ∃ out,
        processCheckedSystemTransaction (benv.withState (drainStep^[j] benv.state)) address [] =
          .ok (drainStep^[j + 1] benv.state, out) := by
  induction k with
  | zero => exact ⟨rep, installed, fun _ h => absurd h (by omega)⟩
  | succ k ih =>
    obtain ⟨hrep, hcode, hcalls⟩ := ih
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine ⟨represents_sysState sysShape (by decide) rfl hrep, ?_, ?_⟩
    · exact (sysState_getCode _ _ _ _).trans hcode
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · exact hcalls j hlt
      · obtain ⟨out, h, _⟩ := call_at sysCall hfork _ hcode
        refine ⟨out, ?_⟩
        rw [Function.iterate_succ_apply']
        exact h

end Blanc.Lift.BuilderRequest.Deposit
