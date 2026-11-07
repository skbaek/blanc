import Blanc.Lift.BuilderRequest.Delivery
import Blanc.RequestFeeWordBound
import Blanc.FakeExponentialEval

/-!
# What a queue costs to fill and how fast it drains, and why the excess stays on the fee's domain

`Backlog.cost target floor n` is the sum over counts `i < n` of the fee the bytes quote at slot 0 zero, `fake_exponential(1, i - target, 17)`, plus a floor
each submission must also pay. It is about a sequence of fees: a budget below it cannot buy `n` such submissions. The budget is a premise, and it says
nothing of whether anyone has one.

`Chain.submissions_le_paid` is a statement over a chain of frames, with system calls allowed: a sequence paying less than the fee at excess 2892, about `2 ^ 245`
wei, never quotes above 2892, so every word quote there is the natural fee, at least 1 wei, and it makes no more submissions than the wei it paid.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune
open RequestSystem

namespace Backlog

/-- The natural fee the bytes quote at count `i` with slot 0 at zero. -/
def fee (target i : Nat) : Nat := fakeExp 1 (i - target) 17

/-- The sum over `i < n` of the fee quoted at count `i` plus a floor. -/
def cost (target floor : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => cost target floor n + (fee target n + floor)

/-- The total of the first `n` payments of a sequence. -/
def total (paid : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => total paid n + paid n

/-- `paid` is a sequence of `n` submissions' payments, each at least the fee quoted at its count plus the floor. -/
def Pays (target floor : Nat) (paid : Nat → Nat) (n : Nat) : Prop :=
  ∀ i, i < n → fee target i + floor ≤ paid i

variable {target floor : Nat}

theorem fee_pos (target i : Nat) : 1 ≤ fee target i := RequestFeeWord.fakeExp_pos _

/-- `cost` is strictly increasing: even with no floor, the fee is at least 1 wei. -/
theorem cost_strictMono {m n : Nat} (h : m < n) : cost target floor m < cost target floor n := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hf := fee_pos target n
    have hs : cost target floor (n + 1) = cost target floor n + (fee target n + floor) := rfl
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | rfl
    · have := ih hlt
      omega
    · omega

/-- A sequence of `n` such payments totals at least the cost. -/
theorem cost_le_total {paid : Nat → Nat} {n : Nat} (h : Pays target floor paid n) :
    cost target floor n ≤ total paid n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h n (by omega)
    simp only [cost, total]
    omega

/-- **A budget below the cost of `n` does not reach `n`,** or any higher count. -/
theorem budget_cannot_reach {budget n m : Nat} (low : budget < cost target floor n) (hm : n ≤ m)
    {paid : Nat → Nat} (h : Pays target floor paid m) : budget < total paid m := by
  have h1 := cost_le_total h
  rcases Nat.lt_or_eq_of_le hm with hlt | rfl
  · have := cost_strictMono (target := target) (floor := floor) hlt
    omega
  · omega

/-- **The cost grows exponentially:** it passes `2 ^ k` by count `34 * (k + 1) + target + 1`. A lower bound with a simple rate, not the true one,
which is `e ^ (1 / 17)` per submission. -/
theorem two_pow_le_cost (k : Nat) : 2 ^ k ≤ cost target floor (34 * (k + 1) + target + 1) := by
  have hfee : 2 ^ k ≤ fee target (34 * (k + 1) + target) := by
    have := FakeExponential.factor_mul_pow_le 1 (34 * (k + 1) + target - target) 17 k 2 (by decide) (by omega)
    rwa [Nat.one_mul] at this
  simp only [cost]
  omega

/-- The evaluator's fee at excess `e`. -/
def feeEval (e : Nat) : Nat :=
  match FakeExponentialEval.runFuel 512 e 17 1 17 with
  | some (_, out) => out / 17
  | none => 0

/-- `cost` by the evaluator. -/
def costEval (target floor : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => costEval target floor n + (feeEval (n - target) + floor)

/-- The evaluator returns at every excess up to 1000. -/
theorem eval_checks : (List.range 1001).all (fun e => (FakeExponentialEval.runFuel 512 e 17 1 17).isSome) = true := by
  decide +kernel

theorem feeEval_eq {e : Nat} (he : e ≤ 1000) : feeEval e = fakeExp 1 e 17 := by
  have hs := List.all_eq_true.mp eval_checks e (List.mem_range.mpr (by omega))
  unfold feeEval
  rcases hr : FakeExponentialEval.runFuel 512 e 17 1 17 with _ | ⟨iterations, out⟩
  · rw [hr] at hs
    cases hs
  · have run := FakeExponentialEval.run_of_runFuel hr
    simp only
    rw [run.output_eq]
    rfl

theorem costEval_eq {n : Nat} (hn : n ≤ 1001 + target) : costEval target floor n = cost target floor n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [costEval, cost, fee]
    rw [ih (by omega), feeEval_eq (by omega)]

/-- **What a budget reaches.** If the budget covers the cost of `k` and not of `k + 1`, a sequence paying the quotes fits it exactly when `n ≤ k`. -/
theorem reach_iff {budget k : Nat} (h1 : cost target floor k ≤ budget) (h2 : budget < cost target floor (k + 1)) (n : Nat) :
    (∃ paid, Pays target floor paid n ∧ total paid n ≤ budget) ↔ n ≤ k := by
  constructor
  · rintro ⟨paid, hp, ht⟩
    by_contra hn
    have := budget_cannot_reach h2 (by omega) hp
    omega
  · intro hn
    refine ⟨fun i => fee target i + floor, fun _ _ => Nat.le_refl _, ?_⟩
    have same : ∀ m, total (fun i => fee target i + floor) m = cost target floor m := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => simp only [total, cost, ih]
    rw [same]
    rcases Nat.lt_or_eq_of_le hn with hlt | rfl
    · have := cost_strictMono (target := target) (floor := floor) hlt
      omega
    · exact h1

variable {Record : Type}

/-- A call's drain, by length. -/
theorem drained_length (cap : Nat) (t : B256) (st : QueueState Record) :
    (drainedState cap t st).queue.length = st.queue.length - cap := by
  rw [Delivery.drainedState_queue, List.length_drop]

/-- `k` drains take `cap` records each. -/
theorem iterate_length (cap : Nat) (t : B256) (st : QueueState Record) (k : Nat) :
    ((drainedState cap t)^[k] st).queue.length = st.queue.length - k * cap := by
  induction k with
  | zero => simp only [Function.iterate_zero, id, Nat.zero_mul, Nat.sub_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply', drained_length, ih, Nat.add_mul, Nat.one_mul, Nat.sub_sub]

/-- **Repeated drains empty a queue of length `n` in `⌈n / cap⌉` steps.** -/
theorem drain_empties {cap : Nat} (hcap : 0 < cap) (t : B256) (st : QueueState Record) :
    ((drainedState cap t)^[(st.queue.length + (cap - 1)) / cap] st).queue = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [iterate_length]
  have := Nat.div_add_mod (st.queue.length + (cap - 1)) cap
  have hm := Nat.mod_lt (st.queue.length + (cap - 1)) hcap
  rw [Nat.mul_comm] at this
  omega

/-- **And not fewer.** -/
theorem drain_not_fewer {cap : Nat} (hcap : 0 < cap) (t : B256) (st : QueueState Record) {k : Nat}
    (hk : k < (st.queue.length + (cap - 1)) / cap) : ((drainedState cap t)^[k] st).queue ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [iterate_length, List.length_nil] at this
  have hk' : (k + 1) * cap ≤ st.queue.length + (cap - 1) := (Nat.le_div_iff_mul_le hcap).mp hk
  rw [Nat.add_mul, Nat.one_mul] at hk'
  omega

end Backlog

/-- **Repeated empty-calldata system calls drain the queue.** With no new submissions, `k` calls, each at the state the last left, succeed, and their post
storage represents the queue after `k` drains. -/
theorem SysCall.calls_drain {k : SysPath} (c : SysCall k) {w capN : Nat} {Record : Type} {words : Record → Nat → B256}
    (hcap : k.shape.cap.word.toNat = capN) (hnext : k.shape.next = excessNext k.shape.target.word)
    {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode c.target = k.code) {st : QueueState Record}
    (rep : Represents w words (storOf benv.state c.target) st) (m : Nat) :
    let drain := fun σ : State => sysState k.shape σ c.target
    Represents w words (storOf (drain^[m] benv.state) c.target) ((drainedState capN k.shape.target.word)^[m] st) ∧
      (drain^[m] benv.state).getCode c.target = k.code ∧
      ∀ j, j < m → ∃ out,
        processCheckedSystemTransaction (benv.withState (drain^[j] benv.state)) c.target [] =
          .ok (drain^[j + 1] benv.state, out) := by
  intro drain
  induction m with
  | zero => exact ⟨rep, installed, fun _ h => absurd h (by omega)⟩
  | succ m ih =>
    obtain ⟨hrep, hcode, hcalls⟩ := ih
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine ⟨represents_sysState k.shape hcap hnext hrep, ?_, ?_⟩
    · exact (sysState_getCode _ _ _ _).trans hcode
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · exact hcalls j hlt
      · obtain ⟨out, h, _⟩ := call_at c hfork _ hcode
        refine ⟨out, ?_⟩
        rw [Function.iterate_succ_apply']
        exact h

namespace Delivery

variable {c : Contract}

/-- What a chain of frames pays, summed over the values its frames carry. -/
def paidBy (frames : List (Frame c)) : Nat := (frames.map Frame.value).sum

theorem paidBy_cons (f : Frame c) (rest : List (Frame c)) : paidBy (f :: rest) = f.value + paidBy rest := by
  simp only [paidBy, List.map_cons, List.sum_cons]

/-- A submission's frame quotes, and its value covers the quote. -/
theorem Frame.quote_of_submission (f : Frame c) {r : c.Record} (he : f.event = .submission r) :
    ∃ q, f.quotedFee = some q ∧ q.toNat ≤ f.value := by
  cases f with
  | submission sevm pre post l i o rules target caller law =>
    exact ⟨_, rfl, c.paid law⟩
  | feeRead sevm pre post l i o rules target caller law => cases he
  | system benv data post out fork installed length run => cases he

/-- The quoted excess stays on the fee's domain: off the inhibitor, `excess + max(0, count - target)` is at most 2892; on it, the count is 0. -/
def OnDomain (c : Contract) (st : QueueState c.Record) : Prop :=
  (st.excess = 2 ^ 256 - 1 → st.count = 0) ∧
    (st.excess ≠ 2 ^ 256 - 1 → st.excess + (st.count - c.target.toNat) ≤ 2892)

/-- A contract with a small target and record width, so that a small count and tail are in word range. -/
structure Small (c : Contract) : Prop where
  target : c.target.toNat ≤ 1000
  width : c.width ≤ 8

theorem OnDomain.count_le {st : QueueState c.Record} (h : OnDomain c st) (s : Small c) : st.count ≤ 3892 := by
  have := s.target
  by_cases hm : st.excess = 2 ^ 256 - 1
  · rw [h.1 hm]
    omega
  · have := h.2 hm
    omega

/-- A system call keeps the excess on the domain. -/
theorem OnDomain.system {st : QueueState c.Record} (h : OnDomain c st) (s : Small c) (latch : Bool) :
    OnDomain c (step c.cap c.target st (.system latch)) := by
  cases latch
  · have hc : (step c.cap c.target st (.system false)).count = 0 := drainedState_count _ _ _
    have hx : (step c.cap c.target st (.system false)).excess = (drainedState c.cap c.target st).excess := rfl
    refine ⟨fun _ => hc, fun _ => ?_⟩
    rw [hc, hx]
    by_cases hm : st.excess = 2 ^ 256 - 1
    · rw [drainedState_excess, hm, inhibitor_toB256, excessNext_inhibitor]
      have hz : (0 : B256).toNat = 0 := rfl
      omega
    · have hb := h.2 hm
      have hcl := h.count_le s
      have hbig : 2892 + 3892 < (2 : Nat) ^ 256 := by decide
      rw [drained_excess_natural _ _ _ (by omega) hm]
      omega
  · refine ⟨fun _ => drainedState_count _ _ _, fun hne => absurd rfl hne⟩

/-- The tail after a list of frames is at most the tail before plus the submissions. -/
theorem queueAfter_tail_le (st : QueueState c.Record) (frames : List (Frame c)) :
    (queueAfter st frames).tail ≤ st.tail + (submissions frames).length := by
  induction frames generalizing st with
  | nil => exact Nat.le_add_right _ _
  | cons f rest ih =>
    have hs : (submissions (f :: rest)).length =
        (submitted [f.event]).length + (submissions rest).length := submitted_cons_length _ _
    have h1 := ih (step c.cap c.target st f.event)
    have h2 := step_tail_le c.cap c.target st f.event
    have hq : queueAfter st (f :: rest) = queueAfter (step c.cap c.target st f.event) rest := rfl
    rw [hq, hs]
    omega

/-- **A budget below the fee at excess 2892 keeps the fee on its domain.** On a chain from a represented queue on the domain, system calls allowed, with `M`
above the tail and everything paid: no submission quotes above 2892, so each pays the natural fee, at least 1 wei, and there are at most as many submissions as
wei paid. -/
theorem Chain.submissions_le_paid {s t : Stor} {frames : List (Frame c)} (chain : Chain s frames t) (small : Small c)
    {st : QueueState c.Record} (rep : Holds c s st) (dom : OnDomain c st)
    (low : paidBy frames < fakeExp 1 2892 17) (hm : st.tail + paidBy frames < 2 ^ 250) :
    (submissions frames).length ≤ paidBy frames := by
  induction chain generalizing st with
  | nil s => exact Nat.zero_le _
  | @cons s f rest t starts tail ih =>
    subst starts
    have hp := paidBy_cons f rest
    have hs : (submissions (f :: rest)).length =
        (submitted [f.event]).length + (submissions rest).length := submitted_cons_length _ _
    have hw := small.width
    have hcl := dom.count_le small
    have hbig : (2 : Nat) ^ 256 = 64 * 2 ^ 250 := by decide
    have hbig2 : 8000 ≤ (2 : Nat) ^ 250 := by decide
    have hslots : ∀ n, n ≤ 1 → queueBase c.width (st.tail + n) ≤ 2 ^ 256 := fun n hn => by
      have hmul : c.width * (st.tail + n) ≤ 8 * (st.tail + n) := Nat.mul_le_mul_right _ hw
      simp only [queueBase]
      rw [hbig]
      generalize (2 : Nat) ^ 250 = W at hm hbig2
      omega
    have hlen : (submitted [f.event]).length ≤ 1 := by
      cases f.event <;> simp only [submitted, List.length_cons, List.length_nil] <;> omega
    obtain ⟨hrep, -⟩ := f.step_holds rep (hslots _ hlen) (by
      generalize (2 : Nat) ^ 256 = W at hbig ⊢
      omega)
    rw [hs, hp]
    rcases he : f.event with r | _ | latch
    · obtain ⟨q, hq, hpay⟩ := f.quote_of_submission he
      have hoff : st.excess ≠ 2 ^ 256 - 1 := by
        intro hmax
        have h0 : f.before.get 0 = st.excess.toB256 := rep.excess
        rw [hmax, inhibitor_toB256] at h0
        exact f.quoted_active hq h0
      have hd := dom.2 hoff
      have hv := f.quote_natural rep hq hd
      have hpos := RequestFeeWord.fakeExp_pos (st.excess + (st.count - c.target.toNat))
      have hne : st.excess + (st.count - c.target.toNat) ≠ 2892 := by
        intro h2892
        rw [h2892] at hv
        omega
      have hstep : step c.cap c.target st f.event = submit st r := by rw [he]; rfl
      rw [he] at hrep
      have hdom : OnDomain c (submit st r) := by
        refine ⟨fun h => absurd h hoff, fun _ => ?_⟩
        show st.excess + (st.count + 1 - c.target.toNat) ≤ 2892
        omega
      have ih' := ih hrep (by rw [show step c.cap c.target st (.submission r) = submit st r from rfl]; exact hdom)
        (by omega) (by
          show st.tail + 1 + paidBy rest < _
          omega)
      have hl : (submitted [Event.submission r]).length = 1 := rfl
      rw [hl]
      omega
    · rw [he] at hrep
      have ih' := ih hrep dom (by omega) (by
        show st.tail + paidBy rest < _
        omega)
      have hl : (submitted [Event.feeRead (Record := c.Record)]).length = 0 := rfl
      rw [hl]
      omega
    · rw [he] at hrep
      have htl := step_tail_le c.cap c.target st (.system latch)
      have hl : (submitted [Event.system (Record := c.Record) latch]).length = 0 := rfl
      rw [hl] at htl ⊢
      have ih' := ih hrep (dom.system small latch) (by omega) (by omega)
      omega

end Delivery

end Blanc.Lift.BuilderRequest
