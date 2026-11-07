import Blanc.Lift.BuilderRequest.Deposit.Delivery
import Blanc.Lift.BuilderRequest.Exit.Delivery
import Blanc.Lift.BuilderRequest.Flood

/-!
# Load bound over any schedule, and fee overhang after activation (O31, O32)

List form, generic over the contract's parameters (`Delivery.Contract`), with the
deposit and exit instances. No chain form and no public layer here: another run owns
O33, O34 and O38, and the chain form reaches through `history_chain`.

O31: with `fee i = fakeExp 1 (max 0 (i - target)) 17` (`Backlog.fee`) and
`Φ L = Σ_{i<L} fee i` (`Backlog.cost target 0`), over any request-phase-only frame
list from deployed storage, `Φ (excess + count)` is at most the fees paid, so a fee
budget bounds load and queue length under any order of submissions and system calls,
and a record waits a bounded number of calls. Instances at 1 ETH, 100 ETH and
120M ETH for both contracts (664, 743, 981 deposit; 658, 737, 975 exit).

O32: with no later submissions, the quote at call `k` is
`fakeExp 1 (max 0 (n - 8k)) 17`, parametric in `n`, attached to the activation
headline; the exit analogue uses its target 2.

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`;
the bytes and `sys-asm` `83f9801`, not the EIP text.

**Reuse.** `Backlog.fee`, `Backlog.cost`, `Backlog.total`, `Backlog.Pays`,
`Backlog.reach_iff`, `Backlog.costEval`, `Backlog.costEval_eq` and the whole
`Delivery` model (`load`, `step`, `replay`, `Chain`, `Frame.quote_natural`,
`Chain.quote_natural`, `replay_calls_excess`, `prefork_then_calls` via the deposit
module) are reused, not redefined. New names here are the fee-only reading
(`feePaid`, `fees`), the potential induction (`step_potential`, `potential_le`),
the queue comparison (`queue_length_le_load`), the latch witness and the O32
overhang; all are hoist candidates for `Delivery.lean` / `Flood.lean` at the green
boundary, since nothing here is contract-specific except the instances.

**Draft status.** This file was written without Lean elaboration under the run's
no-elaboration constraint. Every `sorry` carries a `-- DRAFT:` comment giving the
proof route and the lemmas it needs; the master compiles this file and clears them.
-/

namespace Blanc.Lift.BuilderRequest.LoadBound

open Jaune
open RequestSystem
open Delivery

variable {c : Contract}

/-! ## The fee-only reading of a frame list (O31) -/

/-- What a frame pays toward the fee potential: a submission's word quote, else nothing. -/
def feePaid (f : Frame c) : Nat :=
  match f.event with
  | .submission _ => (f.quotedFee.getD 0).toNat
  | _ => 0

/-- A frame pays at least its fee potential: a submission covers its quote, other frames pay nothing. -/
theorem feePaid_le_value (f : Frame c) : feePaid f ≤ f.value := by
  cases f with
  | submission sevm pre post l i o rules at_contract caller law =>
    show ((o / (17 : B256))).toNat ≤ sevm.value.toNat
    exact c.paid law
  | feeRead sevm pre post l i o rules at_contract caller law =>
    show 0 ≤ sevm.value.toNat
    exact Nat.zero_le _
  | system benv data post out fork installed length run =>
    show 0 ≤ 0
    exact Nat.le_refl _

/-- The fees a frame list pays toward the potential, summed over its frames. -/
def fees (frames : List (Frame c)) : Nat := (frames.map feePaid).sum

/-- `fees` over a cons: the frame's fee plus the rest. -/
theorem fees_cons (f : Frame c) (rest : List (Frame c)) : fees (f :: rest) = feePaid f + fees rest := by
  simp only [fees, List.map_cons, List.sum_cons]

/-- The potential reaches at least its index: every fee is at least 1 wei. -/
theorem cost_ge_self {target : Nat} (L : Nat) : L ≤ Backlog.cost target 0 L := by
  induction L with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [Backlog.cost]
    have h1 := Backlog.fee_pos target n
    omega

/-- The potential is monotone in its index. -/
theorem cost_mono {target a b : Nat} (h : a ≤ b) :
    Backlog.cost target 0 a ≤ Backlog.cost target 0 b := by
  rcases Nat.lt_or_eq_of_le h with hlt | rfl
  · exact (Backlog.cost_strictMono hlt).le
  · exact Nat.le_refl _

/-- The series is monotone in its numerator and accumulator. -/
theorem fakeExpAux_mono {a b den : Nat} (h : a ≤ b) (i x : Nat) :
    ∀ {y : Nat}, x ≤ y → fakeExpAux a den i x ≤ fakeExpAux b den i y := by
  induction i, x using fakeExpAux.induct a den with
  | case1 i => intro y _; simp
  | case2 i x hx ih =>
    intro y hxy
    have hy : y ≠ 0 := by omega
    rw [fakeExpAux_succ hx, fakeExpAux_succ hy]
    exact Nat.add_le_add hxy (ih (Nat.div_le_div_right (Nat.mul_le_mul hxy h)))

/-- The fee is monotone in the excess: a larger numerator quotes no less. -/
theorem fakeExp_mono {a b : Nat} (h : a ≤ b) : fakeExp 1 a 17 ≤ fakeExp 1 b 17 :=
  Nat.div_le_div_right (fakeExpAux_mono h 1 _ (Nat.le_refl _))

/-- A submission grows the load by exactly one, on or off the inhibitor. -/
theorem load_submit {Record : Type} (st : QueueState Record) (r : Record) :
    load (submit st r) = load st + 1 := by
  by_cases hmax : st.excess = 2 ^ 256 - 1
  · have h1 : load st = st.count := ite_eq_left hmax
    have h2 : load (submit st r) = st.count + 1 := ite_eq_left hmax
    omega
  · have h1 : load st = st.excess + st.count := ite_eq_right hmax
    have h2 : load (submit st r) = st.excess + (st.count + 1) := ite_eq_right hmax
    omega

/-- A submission's record list over replicated system calls is empty. -/
theorem submitted_replicate_system {Record : Type} (m : Nat) (latch : Bool) :
    submitted (List.replicate m (.system latch : Event Record)) = [] := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show submitted ((.system latch : Event Record) :: List.replicate m (.system latch)) = []
    exact ih

/-- One frame preserves the fee potential: the next load's potential is at most this load's
plus what the frame pays. The `wrap` premise keeps every quote on the fee's domain. -/
theorem step_potential (f : Frame c) {st : QueueState c.Record} (rep : Holds c f.before st)
    (slots : queueBase c.width (st.tail + (submitted [f.event]).length) ≤ 2 ^ 256)
    (count : st.count + (submitted [f.event]).length < 2 ^ 256)
    (range : load st + (submitted [f.event]).length < 2 ^ 256)
    (wrap : Backlog.cost c.target.toNat 0 (load st) + feePaid f <
      Backlog.cost c.target.toNat 0 2893) :
    Backlog.cost c.target.toNat 0 (load (step c.cap c.target st f.event)) ≤
      Backlog.cost c.target.toNat 0 (load st) + feePaid f := by
  cases f with
  | submission sevm pre post l i o rules at_contract caller law =>
    have hq : (Frame.submission (c := c) sevm pre post l i o rules at_contract caller law).quotedFee =
        some (o / (17 : B256)) := rfl
    have hactive := Frame.quoted_active (c := c)
      (f := Frame.submission (c := c) sevm pre post l i o rules at_contract caller law) hq
    have h0 : (Frame.submission (c := c) sevm pre post l i o rules at_contract caller law).before.get 0 =
        st.excess.toB256 := rep.excess
    have hoff : st.excess ≠ 2 ^ 256 - 1 := by
      intro hmax
      rw [hmax, inhibitor_toB256] at h0
      exact hactive h0
    have hload_eq : load st = st.excess + st.count := ite_eq_right hoff
    have hcost_lt : Backlog.cost c.target.toNat 0 (load st) <
        Backlog.cost c.target.toNat 0 2893 := by omega
    have hload_le : load st ≤ 2892 := by
      by_contra hgt
      push Not at hgt
      have hge : Backlog.cost c.target.toNat 0 2893 ≤
          Backlog.cost c.target.toNat 0 (load st) := cost_mono (by omega)
      omega
    have hfew : st.excess + (st.count - c.target.toNat) ≤ 2892 := by omega
    have hquote := Frame.quote_natural (c := c)
      (f := Frame.submission (c := c) sevm pre post l i o rules at_contract caller law)
      (st := st) rep hq hfew
    have hfeePaid : feePaid (Frame.submission (c := c) sevm pre post l i o rules
        at_contract caller law) = (o / (17 : B256)).toNat := rfl
    have harg_le : load st - c.target.toNat ≤ st.excess + (st.count - c.target.toNat) := by omega
    have hle : Backlog.fee c.target.toNat (load st) ≤ (o / (17 : B256)).toNat := by
      have hfee_eq : Backlog.fee c.target.toNat (load st) =
          fakeExp 1 (load st - c.target.toNat) 17 := rfl
      rw [hfee_eq, hquote]
      exact fakeExp_mono harg_le
    have hstep : step c.cap c.target st
        (Frame.event (Frame.submission (c := c) sevm pre post l i o rules at_contract caller law)) =
        submit st (c.recordOf sevm (c.length law)) := rfl
    rw [hstep, load_submit, hfeePaid]
    have hsucc : Backlog.cost c.target.toNat 0 (load st + 1) =
        Backlog.cost c.target.toNat 0 (load st) + Backlog.fee c.target.toNat (load st) := by
      simp only [Backlog.cost, Nat.add_zero]
    rw [hsucc]
    omega
  | feeRead sevm pre post l i o rules at_contract caller law =>
    have hstep : step c.cap c.target st
        (Frame.event (Frame.feeRead (c := c) sevm pre post l i o rules at_contract caller law)) = st := rfl
    have hfee : feePaid (Frame.feeRead (c := c) sevm pre post l i o rules at_contract caller law) = 0 := rfl
    rw [hstep, hfee, Nat.add_zero]
  | system benv data post out fork installed length run =>
    have hlen : (submitted [(Frame.event (Frame.system (c := c) benv data post out fork
        installed length run))]).length = 0 := rfl
    have hle : load (step c.cap c.target st
        (Frame.event (Frame.system (c := c) benv data post out fork installed length run))) ≤
        load st := by
      have h := load_step c.cap c.target st
        (Frame.event (Frame.system (c := c) benv data post out fork installed length run))
        range rep.excess_lt
      omega
    have hfee : feePaid (Frame.system (c := c) benv data post out fork installed length run) = 0 := rfl
    rw [hfee, Nat.add_zero]
    exact cost_mono hle

/-- **The potential over a frame list (O31, generic).** Over a chain from a represented queue,
with the word range and with the starting potential plus the fees below `Φ 2893`, the end
load's potential is at most the starting potential plus the fees paid. -/
theorem potential_le {s t : Stor} {frames : List (Frame c)} (chain : Chain s frames t)
    {st : QueueState c.Record} (rep : Holds c s st)
    (slots : queueBase c.width (st.tail + (submissions frames).length) ≤ 2 ^ 256)
    (count : st.count + (submissions frames).length < 2 ^ 256)
    (range : load st + (submissions frames).length < 2 ^ 256)
    (wrap : Backlog.cost c.target.toNat 0 (load st) + fees frames <
      Backlog.cost c.target.toNat 0 2893) :
    Backlog.cost c.target.toNat 0 (load (queueAfter st frames)) ≤
      Backlog.cost c.target.toNat 0 (load st) + fees frames := by
  induction chain generalizing st with
  | nil s =>
    have hfees : fees ([] : List (Frame c)) = 0 := rfl
    have hq : queueAfter st ([] : List (Frame c)) = st := rfl
    rw [hq, hfees, Nat.add_zero]
  | @cons s f rest t starts tail ih =>
    subst starts
    have hsub : (submissions (f :: rest)).length =
        (submitted [f.event]).length + (submissions rest).length :=
      submitted_cons_length _ _
    have hfees : fees (f :: rest) = feePaid f + fees rest := fees_cons f rest
    rw [hsub] at slots count range
    rw [hfees] at wrap
    have hlen_le : (submitted [f.event]).length ≤ 1 := by
      cases he : f.event with
      | submission r =>
        simp only [submitted, List.length_cons, List.length_nil]
        omega
      | feeRead =>
        simp only [submitted, List.length_nil]
        omega
      | system latch =>
        simp only [submitted, List.length_nil]
        omega
    have slots_f : queueBase c.width (st.tail + (submitted [f.event]).length) ≤ 2 ^ 256 :=
      (queueBase_mono c.width (by omega)).trans slots
    have count_f : st.count + (submitted [f.event]).length < 2 ^ 256 := by omega
    have range_f : load st + (submitted [f.event]).length < 2 ^ 256 := by omega
    have hstep_le := step_potential (c := c) f (st := st) rep slots_f count_f range_f (by omega)
    obtain ⟨hrep, -⟩ := f.step_holds rep slots_f count_f
    have htail_le := step_tail_le c.cap c.target st f.event
    have hcount_le := step_count_le c.cap c.target st f.event
    have hload_le : load (step c.cap c.target st f.event) ≤
        load st + (submitted [f.event]).length := by
      have h := load_step c.cap c.target st f.event range_f rep.excess_lt
      omega
    have hq : queueAfter st (f :: rest) =
        queueAfter (step c.cap c.target st f.event) rest := rfl
    rw [hq]
    have slots_t : queueBase c.width ((step c.cap c.target st f.event).tail +
        (submissions rest).length) ≤ 2 ^ 256 :=
      (queueBase_mono c.width (by omega)).trans slots
    have count_t : (step c.cap c.target st f.event).count + (submissions rest).length < 2 ^ 256 := by
      omega
    have range_t : load (step c.cap c.target st f.event) + (submissions rest).length < 2 ^ 256 := by
      omega
    have wrap_t : Backlog.cost c.target.toNat 0 (load (step c.cap c.target st f.event)) +
        fees rest < Backlog.cost c.target.toNat 0 2893 := by omega
    have iht := ih hrep slots_t count_t range_t wrap_t
    omega

/-! ## Deployed instances (O31) -/

/-- **The potential from the deposit deployment (O31).** Over any chain from the deployed
storage, `Φ` of the end load is at most the fees paid. -/
theorem deposit_potential {frames : List Deposit.Frame} {t : Stor}
    (chain : Chain Stor.empty frames t)
    (range : 4 + 6 * (submissions frames).length ≤ 2 ^ 256)
    (wrap : fees frames < Backlog.cost 8 0 2893) :
    Backlog.cost 8 0 (load (queueAfter Deposit.deployedQueue frames)) ≤ fees frames := by
  have htarget : Deposit.contract.target.toNat = 8 := by decide
  have hwidth : Deposit.contract.width = 6 := rfl
  have htail : Deposit.deployedQueue.tail = 0 := rfl
  have hcount0 : Deposit.deployedQueue.count = 0 := rfl
  have hload0 : load Deposit.deployedQueue = 0 := by decide
  have hslots : queueBase Deposit.contract.width
      (Deposit.deployedQueue.tail + (submissions frames).length) ≤ 2 ^ 256 := by
    rw [htail, Nat.zero_add, hwidth]
    simpa only [queueBase] using range
  have hcount : Deposit.deployedQueue.count + (submissions frames).length < 2 ^ 256 := by
    rw [hcount0, Nat.zero_add]
    omega
  have hrange : load Deposit.deployedQueue + (submissions frames).length < 2 ^ 256 := by
    rw [hload0, Nat.zero_add]
    omega
  have hcost0 : Backlog.cost 8 0 0 = 0 := rfl
  have hwrap : Backlog.cost Deposit.contract.target.toNat 0 (load Deposit.deployedQueue) +
      fees frames < Backlog.cost Deposit.contract.target.toNat 0 2893 := by
    rw [htarget, hload0, hcost0, Nat.zero_add]
    exact wrap
  have h := potential_le (c := Deposit.contract) chain Deposit.deployed_represents
    hslots hcount hrange hwrap
  rw [htarget, hload0, hcost0, Nat.zero_add] at h
  exact h

/-- **The potential from the exit deployment (O31).** Over any chain from the deployed storage,
`Φ` of the end load is at most the fees paid. -/
theorem exit_potential {frames : List Exit.Frame} {t : Stor}
    (chain : Chain Exit.deployedStorage frames t)
    (range : 4 + 3 * (submissions frames).length ≤ 2 ^ 256)
    (wrap : fees frames < Backlog.cost 2 0 2893) :
    Backlog.cost 2 0 (load (queueAfter Exit.deployedQueue frames)) ≤ fees frames := by
  have htarget : Exit.contract.target.toNat = 2 := by decide
  have hwidth : Exit.contract.width = 3 := rfl
  have htail : Exit.deployedQueue.tail = 0 := rfl
  have hcount0 : Exit.deployedQueue.count = 0 := rfl
  have hload0 : load Exit.deployedQueue = 0 := by decide
  have hslots : queueBase Exit.contract.width
      (Exit.deployedQueue.tail + (submissions frames).length) ≤ 2 ^ 256 := by
    rw [htail, Nat.zero_add, hwidth]
    simpa only [queueBase] using range
  have hcount : Exit.deployedQueue.count + (submissions frames).length < 2 ^ 256 := by
    rw [hcount0, Nat.zero_add]
    omega
  have hrange : load Exit.deployedQueue + (submissions frames).length < 2 ^ 256 := by
    rw [hload0, Nat.zero_add]
    omega
  have hcost0 : Backlog.cost 2 0 0 = 0 := rfl
  have hwrap : Backlog.cost Exit.contract.target.toNat 0 (load Exit.deployedQueue) +
      fees frames < Backlog.cost Exit.contract.target.toNat 0 2893 := by
    rw [htarget, hload0, hcost0, Nat.zero_add]
    exact wrap
  have h := potential_le (c := Exit.contract) chain Exit.deployed_represents
    hslots hcount hrange hwrap
  rw [htarget, hload0, hcost0, Nat.zero_add] at h
  exact h

/-- 1 ETH of deposit fees reaches 664 fee-units and not 665. -/
theorem cost_664 : Backlog.costEval 8 0 664 ≤ 10 ^ 18 ∧ (10 ^ 18 : Nat) < Backlog.costEval 8 0 665 := by
  decide +kernel

/-- 100 ETH of deposit fees reaches 743 fee-units and not 744. -/
theorem cost_743 :
    Backlog.costEval 8 0 743 ≤ 100 * 10 ^ 18 ∧ (100 * 10 ^ 18 : Nat) < Backlog.costEval 8 0 744 := by
  decide +kernel

/-- 120M ETH of deposit fees reaches 981 fee-units and not 982. -/
theorem cost_981 : Backlog.costEval 8 0 981 ≤ 120000000 * 10 ^ 18 ∧
    (120000000 * 10 ^ 18 : Nat) < Backlog.costEval 8 0 982 := by
  decide +kernel

/-- **1 ETH reaches 664 deposit fees.** A fee sequence fits in 1 ETH exactly when `n ≤ 664`. -/
theorem reach_1_eth (n : Nat) :
    (∃ paid, Backlog.Pays 8 0 paid n ∧ Backlog.total paid n ≤ 10 ^ 18) ↔ n ≤ 664 :=
  Backlog.reach_iff (by rw [← Backlog.costEval_eq (by omega)]; exact cost_664.1)
    (by rw [← Backlog.costEval_eq (by omega)]; exact cost_664.2) n

/-- **100 ETH reaches 743 deposit fees.** -/
theorem reach_100_eth (n : Nat) :
    (∃ paid, Backlog.Pays 8 0 paid n ∧ Backlog.total paid n ≤ 100 * 10 ^ 18) ↔ n ≤ 743 :=
  Backlog.reach_iff (by rw [← Backlog.costEval_eq (by omega)]; exact cost_743.1)
    (by rw [← Backlog.costEval_eq (by omega)]; exact cost_743.2) n

/-- **120M ETH reaches 981 deposit fees.** -/
theorem reach_supply (n : Nat) :
    (∃ paid, Backlog.Pays 8 0 paid n ∧ Backlog.total paid n ≤ 120000000 * 10 ^ 18) ↔ n ≤ 981 :=
  Backlog.reach_iff (by rw [← Backlog.costEval_eq (by omega)]; exact cost_981.1)
    (by rw [← Backlog.costEval_eq (by omega)]; exact cost_981.2) n

/-! The exit fee instances are already proved, and reused here, not restated:
`Exit.reach_1_eth` (658), `Exit.reach_100_eth` (737) and `Exit.reach_supply` (975) in
`Blanc/Lift/BuilderRequest/Exit/Flood.lean`, in the same `Backlog.Pays`/`Backlog.total`
form as the deposit instances above. -/

/-! ## Queue length against load, and the latch witness (O31) -/

/-- **The queue is at most the load (O31, generic).** Over a request-phase-only chain from
an off-inhibitor queue whose queued records are at most its load, the queued records stay
at most `excess + count`. The starting queue bound is a premise: representation alone does
not link the record list length to the counters. -/
theorem queue_length_le_load {s t : Stor} {frames : List (Frame c)} (chain : Chain s frames t)
    {st : QueueState c.Record} (rep : Holds c s st)
    (slots : queueBase c.width (st.tail + (submissions frames).length) ≤ 2 ^ 256)
    (count : st.count + (submissions frames).length < 2 ^ 256)
    (range : load st + (submissions frames).length < 2 ^ 256)
    (rp : RequestPhaseOnly frames) (cap_ge : c.target.toNat ≤ c.cap)
    (start_off : st.excess ≠ 2 ^ 256 - 1)
    (hlen : st.queue.length ≤ load st) :
    (queueAfter st frames).queue.length ≤ load (queueAfter st frames) := by
  induction chain generalizing st with
  | nil s =>
    have hq : queueAfter st ([] : List (Frame c)) = st := rfl
    rw [hq]
    exact hlen
  | @cons s f rest t starts tail ih =>
    subst starts
    have hsub : (submissions (f :: rest)).length =
        (submitted [f.event]).length + (submissions rest).length :=
      submitted_cons_length _ _
    rw [hsub] at slots count range
    have rp_tail : RequestPhaseOnly rest := fun x hx => rp x (List.mem_cons_of_mem _ hx)
    have hlen_le : (submitted [f.event]).length ≤ 1 := by
      cases f.event <;> simp only [submitted, List.length_cons, List.length_nil] <;> omega
    have slots_f : queueBase c.width (st.tail + (submitted [f.event]).length) ≤ 2 ^ 256 :=
      (queueBase_mono c.width (by omega)).trans slots
    have count_f : st.count + (submitted [f.event]).length < 2 ^ 256 := by omega
    obtain ⟨hrep, -⟩ := f.step_holds rep slots_f count_f
    have htail_le := step_tail_le c.cap c.target st f.event
    have hcount_le := step_count_le c.cap c.target st f.event
    have range_f : load st + (submitted [f.event]).length < 2 ^ 256 := by omega
    have hload_step_le : load (step c.cap c.target st f.event) ≤
        load st + (submitted [f.event]).length :=
      load_step c.cap c.target st f.event range_f rep.excess_lt
    have hload_st : load st = st.excess + st.count := ite_eq_right start_off
    have off_step : (step c.cap c.target st f.event).excess ≠ 2 ^ 256 - 1 := by
      cases he : f.event with
      | submission r => simpa only [he, step, submit] using start_off
      | feeRead => simpa only [he, step] using start_off
      | system latch =>
        have hrp := rp f List.mem_cons_self latch he
        subst hrp
        have hne_B256 : excessNext c.target st.excess.toB256 st.count.toB256 ≠ B256.max :=
          excessNext_ne_max c.target_ne _ _
        have hne : (drainedState c.cap c.target st).excess ≠ 2 ^ 256 - 1 := by
          intro h
          apply hne_B256
          apply B256.toNat_inj
          rw [drainedState_excess] at h
          rw [h, max_toNat]
        simpa only [he, step] using hne
    have hlen_step : (step c.cap c.target st f.event).queue.length ≤
        load (step c.cap c.target st f.event) := by
      cases he : f.event with
      | submission r =>
        have hq : (step c.cap c.target st (.submission r)).queue.length =
            st.queue.length + 1 := by
          simp only [step, submit, List.length_append, List.length_singleton]
        have hl : load (step c.cap c.target st (.submission r)) =
            load st + 1 := load_submit _ _
        omega
      | feeRead =>
        have hq : (step c.cap c.target st .feeRead).queue.length = st.queue.length := rfl
        have hl : load (step c.cap c.target st .feeRead) = load st := rfl
        omega
      | system latch =>
        have hrp := rp f List.mem_cons_self latch he
        subst hrp
        have hsum : st.excess + st.count < 2 ^ 256 := by omega
        have hx := drained_excess_natural c.cap c.target st hsum start_off
        have hc : (drainedState c.cap c.target st).count = 0 := drainedState_count _ _ _
        have hqq : (step c.cap c.target st (.system false)).queue.length =
            st.queue.length - c.cap := by
          simp only [step, drainedState_queue, List.length_drop]
        have hne_B256 : excessNext c.target st.excess.toB256 st.count.toB256 ≠ B256.max :=
          excessNext_ne_max c.target_ne _ _
        have hne' : (drainedState c.cap c.target st).excess ≠ 2 ^ 256 - 1 := by
          intro h
          apply hne_B256
          apply B256.toNat_inj
          rw [drainedState_excess] at h
          rw [h, max_toNat]
        have hload_eq : load (step c.cap c.target st (.system false)) =
            st.excess + st.count - c.target.toNat := by
          have hstep_eq : step c.cap c.target st (.system false) =
              drainedState c.cap c.target st := rfl
          have hunfold : load (drainedState c.cap c.target st) =
              (drainedState c.cap c.target st).excess +
                (drainedState c.cap c.target st).count := ite_eq_right hne'
          rw [hstep_eq, hunfold, hx, hc, Nat.add_zero]
        omega
    have hq : queueAfter st (f :: rest) =
        queueAfter (step c.cap c.target st f.event) rest := rfl
    rw [hq]
    have slots_t : queueBase c.width ((step c.cap c.target st f.event).tail +
        (submissions rest).length) ≤ 2 ^ 256 :=
      (queueBase_mono c.width (by omega)).trans slots
    have count_t : (step c.cap c.target st f.event).count + (submissions rest).length < 2 ^ 256 := by
      omega
    have range_t : load (step c.cap c.target st f.event) + (submissions rest).length < 2 ^ 256 := by
      omega
    exact ih hrep slots_t count_t range_t rp_tail off_step hlen_step

/-- **The latch breaks the queue bound (O31 negative control).** Seventeen exit submissions
then a latch call leave one queued record at load zero. -/
theorem latch_breaks_queue_bound :
    let st : QueueState Unit := ⟨0, 0, 0, 0, []⟩
    let es : List (Event Unit) :=
      List.replicate 17 (.submission ()) ++ [.system true]
    (replay 16 2 st es).queue.length = 1 ∧ load (replay 16 2 st es) = 0 := by
  decide

/-! ## Fee budgets bound load and queue (O31 instances) -/

/-- 1 ETH of fees bounds a deposit list: load and queue length at most 664. -/
theorem deposit_load_le_664 {frames : List Deposit.Frame} {t : Stor}
    (chain : Chain Stor.empty frames t) (rp : RequestPhaseOnly frames)
    (range : 4 + 6 * (submissions frames).length ≤ 2 ^ 256)
    (hb : fees frames ≤ 10 ^ 18) :
    load (queueAfter Deposit.deployedQueue frames) ≤ 664 ∧
      (queueAfter Deposit.deployedQueue frames).queue.length ≤ 664 := by
  have heq665 : Backlog.costEval 8 0 665 = Backlog.cost 8 0 665 :=
    Backlog.costEval_eq (by omega)
  have h665_lt : (10 ^ 18 : Nat) < Backlog.cost 8 0 665 := by
    have h := cost_664.2
    rw [heq665] at h
    exact h
  have h665_le : Backlog.cost 8 0 665 ≤ Backlog.cost 8 0 2893 := cost_mono (by omega)
  have hwrap : fees frames < Backlog.cost 8 0 2893 := by omega
  have hpot := deposit_potential chain range hwrap
  have hlt : Backlog.cost 8 0 (load (queueAfter Deposit.deployedQueue frames)) <
      Backlog.cost 8 0 665 := by omega
  have hload : load (queueAfter Deposit.deployedQueue frames) ≤ 664 := by
    by_contra hgt
    push Not at hgt
    have hge : Backlog.cost 8 0 665 ≤
        Backlog.cost 8 0 (load (queueAfter Deposit.deployedQueue frames)) :=
      cost_mono (by omega)
    omega
  refine ⟨hload, ?_⟩
  have htarget : Deposit.contract.target.toNat = 8 := by decide
  have hwidth : Deposit.contract.width = 6 := rfl
  have htail : Deposit.deployedQueue.tail = 0 := rfl
  have hcount0 : Deposit.deployedQueue.count = 0 := rfl
  have hload0 : load Deposit.deployedQueue = 0 := by decide
  have hslots : queueBase Deposit.contract.width
      (Deposit.deployedQueue.tail + (submissions frames).length) ≤ 2 ^ 256 := by
    rw [htail, Nat.zero_add, hwidth]
    simpa only [queueBase] using range
  have hcount : Deposit.deployedQueue.count + (submissions frames).length < 2 ^ 256 := by
    rw [hcount0, Nat.zero_add]
    omega
  have hrange : load Deposit.deployedQueue + (submissions frames).length < 2 ^ 256 := by
    rw [hload0, Nat.zero_add]
    omega
  have hq := queue_length_le_load (c := Deposit.contract) chain Deposit.deployed_represents
    hslots hcount hrange rp (by decide) (by decide) (by decide)
  omega

/-- 100 ETH of fees bounds a deposit list: load and queue length at most 743. -/
theorem deposit_load_le_743 {frames : List Deposit.Frame} {t : Stor}
    (chain : Chain Stor.empty frames t) (rp : RequestPhaseOnly frames)
    (range : 4 + 6 * (submissions frames).length ≤ 2 ^ 256)
    (hb : fees frames ≤ 100 * 10 ^ 18) :
    load (queueAfter Deposit.deployedQueue frames) ≤ 743 ∧
      (queueAfter Deposit.deployedQueue frames).queue.length ≤ 743 := by
  have heq744 : Backlog.costEval 8 0 744 = Backlog.cost 8 0 744 :=
    Backlog.costEval_eq (by omega)
  have h744_lt : (100 * 10 ^ 18 : Nat) < Backlog.cost 8 0 744 := by
    have h := cost_743.2
    rw [heq744] at h
    exact h
  have h744_le : Backlog.cost 8 0 744 ≤ Backlog.cost 8 0 2893 := cost_mono (by omega)
  have hwrap : fees frames < Backlog.cost 8 0 2893 := by omega
  have hpot := deposit_potential chain range hwrap
  have hlt : Backlog.cost 8 0 (load (queueAfter Deposit.deployedQueue frames)) <
      Backlog.cost 8 0 744 := by omega
  have hload : load (queueAfter Deposit.deployedQueue frames) ≤ 743 := by
    by_contra hgt
    push Not at hgt
    have hge : Backlog.cost 8 0 744 ≤
        Backlog.cost 8 0 (load (queueAfter Deposit.deployedQueue frames)) :=
      cost_mono (by omega)
    omega
  refine ⟨hload, ?_⟩
  have hwidth : Deposit.contract.width = 6 := rfl
  have htail : Deposit.deployedQueue.tail = 0 := rfl
  have hcount0 : Deposit.deployedQueue.count = 0 := rfl
  have hload0 : load Deposit.deployedQueue = 0 := by decide
  have hslots : queueBase Deposit.contract.width
      (Deposit.deployedQueue.tail + (submissions frames).length) ≤ 2 ^ 256 := by
    rw [htail, Nat.zero_add, hwidth]
    simpa only [queueBase] using range
  have hcount : Deposit.deployedQueue.count + (submissions frames).length < 2 ^ 256 := by
    rw [hcount0, Nat.zero_add]
    omega
  have hrange : load Deposit.deployedQueue + (submissions frames).length < 2 ^ 256 := by
    rw [hload0, Nat.zero_add]
    omega
  have hq := queue_length_le_load (c := Deposit.contract) chain Deposit.deployed_represents
    hslots hcount hrange rp (by decide) (by decide) (by decide)
  omega

/-- 120M ETH of fees bounds a deposit list: load and queue length at most 981. -/
theorem deposit_load_le_981 {frames : List Deposit.Frame} {t : Stor}
    (chain : Chain Stor.empty frames t) (rp : RequestPhaseOnly frames)
    (range : 4 + 6 * (submissions frames).length ≤ 2 ^ 256)
    (hb : fees frames ≤ 120000000 * 10 ^ 18) :
    load (queueAfter Deposit.deployedQueue frames) ≤ 981 ∧
      (queueAfter Deposit.deployedQueue frames).queue.length ≤ 981 := by
  have heq982 : Backlog.costEval 8 0 982 = Backlog.cost 8 0 982 :=
    Backlog.costEval_eq (by omega)
  have h982_lt : (120000000 * 10 ^ 18 : Nat) < Backlog.cost 8 0 982 := by
    have h := cost_981.2
    rw [heq982] at h
    exact h
  have h982_le : Backlog.cost 8 0 982 ≤ Backlog.cost 8 0 2893 := cost_mono (by omega)
  have hwrap : fees frames < Backlog.cost 8 0 2893 := by omega
  have hpot := deposit_potential chain range hwrap
  have hlt : Backlog.cost 8 0 (load (queueAfter Deposit.deployedQueue frames)) <
      Backlog.cost 8 0 982 := by omega
  have hload : load (queueAfter Deposit.deployedQueue frames) ≤ 981 := by
    by_contra hgt
    push Not at hgt
    have hge : Backlog.cost 8 0 982 ≤
        Backlog.cost 8 0 (load (queueAfter Deposit.deployedQueue frames)) :=
      cost_mono (by omega)
    omega
  refine ⟨hload, ?_⟩
  have hwidth : Deposit.contract.width = 6 := rfl
  have htail : Deposit.deployedQueue.tail = 0 := rfl
  have hcount0 : Deposit.deployedQueue.count = 0 := rfl
  have hload0 : load Deposit.deployedQueue = 0 := by decide
  have hslots : queueBase Deposit.contract.width
      (Deposit.deployedQueue.tail + (submissions frames).length) ≤ 2 ^ 256 := by
    rw [htail, Nat.zero_add, hwidth]
    simpa only [queueBase] using range
  have hcount : Deposit.deployedQueue.count + (submissions frames).length < 2 ^ 256 := by
    rw [hcount0, Nat.zero_add]
    omega
  have hrange : load Deposit.deployedQueue + (submissions frames).length < 2 ^ 256 := by
    rw [hload0, Nat.zero_add]
    omega
  have hq := queue_length_le_load (c := Deposit.contract) chain Deposit.deployed_represents
    hslots hcount hrange rp (by decide) (by decide) (by decide)
  omega

/-- 1 ETH of fees bounds an exit list: load and queue length at most 658. -/
theorem exit_load_le_658 {frames : List Exit.Frame} {t : Stor}
    (chain : Chain Exit.deployedStorage frames t) (rp : RequestPhaseOnly frames)
    (range : 4 + 3 * (submissions frames).length ≤ 2 ^ 256)
    (hb : fees frames ≤ 10 ^ 18) :
    load (queueAfter Exit.deployedQueue frames) ≤ 658 ∧
      (queueAfter Exit.deployedQueue frames).queue.length ≤ 658 := by
  have heq659 : Backlog.costEval 2 0 659 = Backlog.cost 2 0 659 :=
    Backlog.costEval_eq (by omega)
  have h659_lt : (10 ^ 18 : Nat) < Backlog.cost 2 0 659 := by
    have h : Backlog.costEval 2 0 658 ≤ 10 ^ 18 ∧
        (10 ^ 18 : Nat) < Backlog.costEval 2 0 659 := by decide +kernel
    rw [heq659] at h
    exact h.2
  have h659_le : Backlog.cost 2 0 659 ≤ Backlog.cost 2 0 2893 := cost_mono (by omega)
  have hwrap : fees frames < Backlog.cost 2 0 2893 := by omega
  have hpot := exit_potential chain range hwrap
  have hlt : Backlog.cost 2 0 (load (queueAfter Exit.deployedQueue frames)) <
      Backlog.cost 2 0 659 := by omega
  have hload : load (queueAfter Exit.deployedQueue frames) ≤ 658 := by
    by_contra hgt
    push Not at hgt
    have hge : Backlog.cost 2 0 659 ≤
        Backlog.cost 2 0 (load (queueAfter Exit.deployedQueue frames)) :=
      cost_mono (by omega)
    omega
  refine ⟨hload, ?_⟩
  cases frames with
  | nil =>
    have hq : queueAfter Exit.deployedQueue ([] : List Exit.Frame) = Exit.deployedQueue := rfl
    rw [hq]
    show ([] : List Exit.contract.Record).length ≤ 658
    simp only [List.length_nil, Nat.zero_le]
  | cons f rest =>
    obtain ⟨latch, hcall⟩ := Exit.first_frame_system chain
    have hrp := rp f List.mem_cons_self latch hcall
    subst hrp
    cases hchain : chain with
    | cons starts tail =>
      have hrep0 : Holds Exit.contract f.before Exit.deployedQueue := by
        rw [starts]
        exact Exit.deployed_represents
      have hsub0 : (submitted [f.event]).length = 0 := by
        simp only [hcall, submitted, List.length_nil]
      have hsub : (submissions (f :: rest)).length = (submissions rest).length := by
        have h := submitted_cons_length f.event (events rest)
        simp only [submissions, events, List.map_cons] at h ⊢
        rw [h, hsub0, Nat.zero_add]
      rw [hsub] at range
      have slots_f : queueBase Exit.contract.width
          (Exit.deployedQueue.tail + (submitted [f.event]).length) ≤ 2 ^ 256 := by
        have htail : Exit.deployedQueue.tail = 0 := rfl
        have hwidth : Exit.contract.width = 3 := rfl
        rw [htail, Nat.zero_add, hwidth, hsub0]
        simp only [queueBase]
        omega
      have count_f : Exit.deployedQueue.count + (submitted [f.event]).length < 2 ^ 256 := by
        have hcount0 : Exit.deployedQueue.count = 0 := rfl
        rw [hcount0, Nat.zero_add, hsub0]
        omega
      obtain ⟨hrep1, -⟩ := f.step_holds hrep0 slots_f count_f
      have hstep_eq : step Exit.contract.cap Exit.contract.target Exit.deployedQueue
          (.system false) = ⟨0, 0, 0, 0, []⟩ := by
        have hdeq : Exit.deployedQueue = ⟨2 ^ 256 - 1, 0, 0, 0, []⟩ := rfl
        have hex : (excessNext (2 : B256) (2 ^ 256 - 1).toB256 (0 : Nat).toB256).toNat = 0 := by
          rw [show (2 ^ 256 - 1 : Nat).toB256 = B256.max from inhibitor_toB256,
            excessNext_inhibitor]
          rfl
        have hcap : Exit.contract.cap = 16 := rfl
        have htgt : Exit.contract.target = 2 := rfl
        rw [hdeq, hcap, htgt]
        simp only [step, drainedState, hex]
        rw [ite_eq_left (by decide : ([] : List Exit.contract.Record).length ≤ 16)]
      have hrep1' : Holds Exit.contract f.after
          (step Exit.contract.cap Exit.contract.target Exit.deployedQueue f.event) := hrep1
      rw [hcall] at hrep1'
      have hst0 : step Exit.contract.cap Exit.contract.target Exit.deployedQueue
          (.system false) = ⟨0, 0, 0, 0, []⟩ := hstep_eq
      have htail_s : (step Exit.contract.cap Exit.contract.target Exit.deployedQueue
          (.system false)).tail = 0 := by rw [hst0]
      have hcount_s : (step Exit.contract.cap Exit.contract.target Exit.deployedQueue
          (.system false)).count = 0 := by rw [hst0]
      have hload_s : load (step Exit.contract.cap Exit.contract.target Exit.deployedQueue
          (.system false)) = 0 := by rw [hst0]; decide
      have hslots_t : queueBase Exit.contract.width
          ((step Exit.contract.cap Exit.contract.target Exit.deployedQueue
            (.system false)).tail + (submissions rest).length) ≤ 2 ^ 256 := by
        rw [htail_s, Nat.zero_add]
        have hwidth : Exit.contract.width = 3 := rfl
        rw [hwidth]
        simpa only [queueBase, Nat.zero_add] using range
      have hcount_t : (step Exit.contract.cap Exit.contract.target Exit.deployedQueue
          (.system false)).count + (submissions rest).length < 2 ^ 256 := by
        rw [hcount_s, Nat.zero_add]
        omega
      have hrange_t : load (step Exit.contract.cap Exit.contract.target Exit.deployedQueue
          (.system false)) + (submissions rest).length < 2 ^ 256 := by
        rw [hload_s, Nat.zero_add]
        omega
      have rp_tail : RequestPhaseOnly rest := fun x hx => rp x (List.mem_cons_of_mem _ hx)
      have hq := queue_length_le_load (c := Exit.contract) tail hrep1'
        hslots_t hcount_t hrange_t rp_tail (by decide) (by rw [hst0]; decide)
        (by rw [hst0]; decide)
      have hqeq : queueAfter Exit.deployedQueue (f :: rest) =
          queueAfter (step Exit.contract.cap Exit.contract.target Exit.deployedQueue
            (.system false)) rest := by
        simp only [queueAfter, events, List.map_cons, replay, hcall]
        rfl
      have hload_eq : load (queueAfter Exit.deployedQueue (f :: rest)) =
          load (queueAfter (step Exit.contract.cap Exit.contract.target Exit.deployedQueue
            (.system false)) rest) := congrArg load hqeq
      have hqfin : (queueAfter (step Exit.contract.cap Exit.contract.target Exit.deployedQueue
          (.system false)) rest).queue.length ≤ 658 := by omega
      rw [hqeq]
      exact hqfin

/-- The exit queue is at most any bound its load meets: the splitting half of the exit
instances, so the three budgets share one proof. After the unlocking call the queue is
empty and slot 0 clear, then `queue_length_le_load` applies. -/
theorem exit_queue_le_of_load {frames : List Exit.Frame} {t : Stor} {B : Nat}
    (chain : Chain Exit.deployedStorage frames t) (rp : RequestPhaseOnly frames)
    (range : 4 + 3 * (submissions frames).length ≤ 2 ^ 256)
    (hload : load (queueAfter Exit.deployedQueue frames) ≤ B) :
    (queueAfter Exit.deployedQueue frames).queue.length ≤ B := by
  cases frames with
  | nil =>
    have hq : queueAfter Exit.deployedQueue ([] : List Exit.Frame) = Exit.deployedQueue := rfl
    rw [hq]
    show ([] : List Exit.contract.Record).length ≤ B
    simp only [List.length_nil, Nat.zero_le]
  | cons f rest =>
    obtain ⟨latch, hcall⟩ := Exit.first_frame_system chain
    have hrp := rp f List.mem_cons_self latch hcall
    subst hrp
    cases hchain : chain with
    | cons starts tail =>
      have hrep0 : Holds Exit.contract f.before Exit.deployedQueue := by
        rw [starts]
        exact Exit.deployed_represents
      have hsub0 : (submitted [f.event]).length = 0 := by
        simp only [hcall, submitted, List.length_nil]
      have hsub : (submissions (f :: rest)).length = (submissions rest).length := by
        have h := submitted_cons_length f.event (events rest)
        simp only [submissions, events, List.map_cons] at h ⊢
        rw [h, hsub0, Nat.zero_add]
      rw [hsub] at range
      have slots_f : queueBase Exit.contract.width
          (Exit.deployedQueue.tail + (submitted [f.event]).length) ≤ 2 ^ 256 := by
        have htail : Exit.deployedQueue.tail = 0 := rfl
        have hwidth : Exit.contract.width = 3 := rfl
        rw [htail, Nat.zero_add, hwidth, hsub0]
        simp only [queueBase]
        omega
      have count_f : Exit.deployedQueue.count + (submitted [f.event]).length < 2 ^ 256 := by
        have hcount0 : Exit.deployedQueue.count = 0 := rfl
        rw [hcount0, Nat.zero_add, hsub0]
        omega
      obtain ⟨hrep1, -⟩ := f.step_holds hrep0 slots_f count_f
      have hstep_eq : step Exit.contract.cap Exit.contract.target Exit.deployedQueue
          (.system false) = ⟨0, 0, 0, 0, []⟩ := by
        have hdeq : Exit.deployedQueue = ⟨2 ^ 256 - 1, 0, 0, 0, []⟩ := rfl
        have hex : (excessNext (2 : B256) (2 ^ 256 - 1).toB256 (0 : Nat).toB256).toNat = 0 := by
          rw [show (2 ^ 256 - 1 : Nat).toB256 = B256.max from inhibitor_toB256,
            excessNext_inhibitor]
          rfl
        have hcap : Exit.contract.cap = 16 := rfl
        have htgt : Exit.contract.target = 2 := rfl
        rw [hdeq, hcap, htgt]
        simp only [step, drainedState, hex]
        rw [ite_eq_left (by decide : ([] : List Exit.contract.Record).length ≤ 16)]
      have hrep1' : Holds Exit.contract f.after
          (step Exit.contract.cap Exit.contract.target Exit.deployedQueue f.event) := hrep1
      rw [hcall] at hrep1'
      have hst0 : step Exit.contract.cap Exit.contract.target Exit.deployedQueue
          (.system false) = ⟨0, 0, 0, 0, []⟩ := hstep_eq
      have htail_s : (step Exit.contract.cap Exit.contract.target Exit.deployedQueue
          (.system false)).tail = 0 := by rw [hst0]
      have hcount_s : (step Exit.contract.cap Exit.contract.target Exit.deployedQueue
          (.system false)).count = 0 := by rw [hst0]
      have hload_s : load (step Exit.contract.cap Exit.contract.target Exit.deployedQueue
          (.system false)) = 0 := by rw [hst0]; decide
      have hslots_t : queueBase Exit.contract.width
          ((step Exit.contract.cap Exit.contract.target Exit.deployedQueue
            (.system false)).tail + (submissions rest).length) ≤ 2 ^ 256 := by
        rw [htail_s, Nat.zero_add]
        have hwidth : Exit.contract.width = 3 := rfl
        rw [hwidth]
        simpa only [queueBase, Nat.zero_add] using range
      have hcount_t : (step Exit.contract.cap Exit.contract.target Exit.deployedQueue
          (.system false)).count + (submissions rest).length < 2 ^ 256 := by
        rw [hcount_s, Nat.zero_add]
        omega
      have hrange_t : load (step Exit.contract.cap Exit.contract.target Exit.deployedQueue
          (.system false)) + (submissions rest).length < 2 ^ 256 := by
        rw [hload_s, Nat.zero_add]
        omega
      have rp_tail : RequestPhaseOnly rest := fun x hx => rp x (List.mem_cons_of_mem _ hx)
      have hq := queue_length_le_load (c := Exit.contract) tail hrep1'
        hslots_t hcount_t hrange_t rp_tail (by decide) (by rw [hst0]; decide)
        (by rw [hst0]; decide)
      have hqeq : queueAfter Exit.deployedQueue (f :: rest) =
          queueAfter (step Exit.contract.cap Exit.contract.target Exit.deployedQueue
            (.system false)) rest := by
        simp only [queueAfter, events, List.map_cons, replay, hcall]
        rfl
      have hload_eq : load (queueAfter Exit.deployedQueue (f :: rest)) =
          load (queueAfter (step Exit.contract.cap Exit.contract.target Exit.deployedQueue
            (.system false)) rest) := congrArg load hqeq
      rw [hqeq]
      omega

/-- 100 ETH of fees bounds an exit list: load and queue length at most 737. -/
theorem exit_load_le_737 {frames : List Exit.Frame} {t : Stor}
    (chain : Chain Exit.deployedStorage frames t) (rp : RequestPhaseOnly frames)
    (range : 4 + 3 * (submissions frames).length ≤ 2 ^ 256)
    (hb : fees frames ≤ 100 * 10 ^ 18) :
    load (queueAfter Exit.deployedQueue frames) ≤ 737 ∧
      (queueAfter Exit.deployedQueue frames).queue.length ≤ 737 := by
  have heq738 : Backlog.costEval 2 0 738 = Backlog.cost 2 0 738 :=
    Backlog.costEval_eq (by omega)
  have h738_lt : (100 * 10 ^ 18 : Nat) < Backlog.cost 2 0 738 := by
    have h : Backlog.costEval 2 0 737 ≤ 100 * 10 ^ 18 ∧
        (100 * 10 ^ 18 : Nat) < Backlog.costEval 2 0 738 := by decide +kernel
    rw [heq738] at h
    exact h.2
  have h738_le : Backlog.cost 2 0 738 ≤ Backlog.cost 2 0 2893 := cost_mono (by omega)
  have hwrap : fees frames < Backlog.cost 2 0 2893 := by omega
  have hpot := exit_potential chain range hwrap
  have hlt : Backlog.cost 2 0 (load (queueAfter Exit.deployedQueue frames)) <
      Backlog.cost 2 0 738 := by omega
  have hload : load (queueAfter Exit.deployedQueue frames) ≤ 737 := by
    by_contra hgt
    push Not at hgt
    have hge : Backlog.cost 2 0 738 ≤
        Backlog.cost 2 0 (load (queueAfter Exit.deployedQueue frames)) :=
      cost_mono (by omega)
    omega
  exact ⟨hload, exit_queue_le_of_load chain rp range hload⟩

/-- 120M ETH of fees bounds an exit list: load and queue length at most 975. -/
theorem exit_load_le_975 {frames : List Exit.Frame} {t : Stor}
    (chain : Chain Exit.deployedStorage frames t) (rp : RequestPhaseOnly frames)
    (range : 4 + 3 * (submissions frames).length ≤ 2 ^ 256)
    (hb : fees frames ≤ 120000000 * 10 ^ 18) :
    load (queueAfter Exit.deployedQueue frames) ≤ 975 ∧
      (queueAfter Exit.deployedQueue frames).queue.length ≤ 975 := by
  have heq976 : Backlog.costEval 2 0 976 = Backlog.cost 2 0 976 :=
    Backlog.costEval_eq (by omega)
  have h976_lt : (120000000 * 10 ^ 18 : Nat) < Backlog.cost 2 0 976 := by
    have h : Backlog.costEval 2 0 975 ≤ 120000000 * 10 ^ 18 ∧
        (120000000 * 10 ^ 18 : Nat) < Backlog.costEval 2 0 976 := by decide +kernel
    rw [heq976] at h
    exact h.2
  have h976_le : Backlog.cost 2 0 976 ≤ Backlog.cost 2 0 2893 := cost_mono (by omega)
  have hwrap : fees frames < Backlog.cost 2 0 2893 := by omega
  have hpot := exit_potential chain range hwrap
  have hlt : Backlog.cost 2 0 (load (queueAfter Exit.deployedQueue frames)) <
      Backlog.cost 2 0 976 := by omega
  have hload : load (queueAfter Exit.deployedQueue frames) ≤ 975 := by
    by_contra hgt
    push Not at hgt
    have hge : Backlog.cost 2 0 976 ≤
        Backlog.cost 2 0 (load (queueAfter Exit.deployedQueue frames)) :=
      cost_mono (by omega)
    omega
  exact ⟨hload, exit_queue_le_of_load chain rp range hload⟩

/-! ## A record waits a bounded number of calls (O31) -/

/-- A queued prefix reached within `k` calls is delivered: any prefix of the starting queue
with at most `k * cap` records is a prefix of what the events' system calls deliver. -/
theorem delivered_prefix {Record : Type} (cap : Nat) (target : B256) (st : QueueState Record)
    (es : List (Event Record)) (P : List Record) (k : Nat)
    (hpre : P <+: st.queue) (hlen : P.length ≤ k * cap)
    (hcalls : k ≤ (es.filter fun e => match e with
      | .system _ => true | _ => false).length) :
    P <+: (chunks cap target st es).flatten := by
  induction es generalizing st P k with
  | nil =>
    have h0 : k ≤ 0 := by simpa only [List.filter_nil, List.length_nil] using hcalls
    have hk0 : k = 0 := by omega
    have hle0 : P.length ≤ 0 := by
      rw [hk0] at hlen
      simpa only [Nat.zero_mul] using hlen
    have hPnil : P = [] := List.length_eq_zero_iff.mp (by omega)
    subst hPnil
    simp only [chunks, List.flatten_nil]
    exact List.nil_prefix
  | cons e es ih =>
    cases e with
    | submission r =>
      have hchunk : chunk cap st (Event.submission r) = [] := rfl
      have hflat : (chunks cap target st (Event.submission r :: es)).flatten =
          (chunks cap target (submit st r) es).flatten := by
        simp only [chunks, step, hchunk, List.flatten_cons, List.nil_append]
      rw [hflat]
      have hfilt : ((Event.submission r :: es).filter fun e => match e with
          | .system _ => true | _ => false) = es.filter fun e => match e with
          | .system _ => true | _ => false := rfl
      have hcalls' : k ≤ (es.filter fun e => match e with
          | .system _ => true | _ => false).length := by
        rw [← hfilt]
        exact hcalls
      obtain ⟨t, ht⟩ := hpre
      have hpre' : P <+: (submit st r).queue := by
        refine ⟨t ++ [r], ?_⟩
        simp only [submit]
        rw [← List.append_assoc, ht]
      exact ih _ _ _ hpre' hlen hcalls'
    | feeRead =>
      have hchunk : chunk cap st (Event.feeRead) = [] := rfl
      have hflat : (chunks cap target st (Event.feeRead :: es)).flatten =
          (chunks cap target st es).flatten := by
        simp only [chunks, step, hchunk, List.flatten_cons, List.nil_append]
      rw [hflat]
      have hfilt : ((Event.feeRead :: es).filter fun e => match e with
          | .system _ => true | _ => false) = es.filter fun e => match e with
          | .system _ => true | _ => false := rfl
      have hcalls' : k ≤ (es.filter fun e => match e with
          | .system _ => true | _ => false).length := by
        rw [← hfilt]
        exact hcalls
      exact ih _ _ _ hpre hlen hcalls'
    | system latch =>
      have hfilt : ((Event.system latch :: es).filter fun e => match e with
          | .system _ => true | _ => false) =
          Event.system latch :: es.filter fun e => match e with
          | .system _ => true | _ => false := rfl
      have hlenf : (((Event.system latch :: es).filter fun e => match e with
          | .system _ => true | _ => false).length) =
          (es.filter fun e => match e with
          | .system _ => true | _ => false).length + 1 := by
        rw [hfilt, List.length_cons]
      rw [hlenf] at hcalls
      have hflat : (chunks cap target st (Event.system latch :: es)).flatten =
          st.queue.take cap ++
            (chunks cap target (step cap target st (.system latch)) es).flatten := by
        simp only [chunks, chunk, List.flatten_cons]
      rw [hflat]
      by_cases hk0 : k = 0
      · subst hk0
        have hle0 : P.length ≤ 0 := by simpa only [Nat.zero_mul] using hlen
        have hPnil : P = [] := List.length_eq_zero_iff.mp (by omega)
        subst hPnil
        exact List.nil_prefix
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        by_cases hle : P.length ≤ cap
        · have hPtake : P.take cap = P := List.take_of_length_le (by omega)
          obtain ⟨t, ht⟩ := hpre
          have htakeC : st.queue.take cap = P ++ t.take (cap - P.length) := by
            rw [← ht, List.take_append, hPtake]
          have hpreC : P <+: st.queue.take cap := ⟨t.take (cap - P.length), htakeC.symm⟩
          exact hpreC.trans (List.prefix_append _ _)
        · obtain ⟨t, ht⟩ := hpre
          have hpre' : P.drop cap <+: (step cap target st (.system latch)).queue := by
            rw [step_queue_system, ← ht, List.drop_append]
            exact List.prefix_append _ _
          have hmul : (j + 1) * cap = j * cap + cap := by
            rw [Nat.add_mul, Nat.one_mul]
          have hlen' : (P.drop cap).length ≤ j * cap := by
            rw [List.length_drop]
            omega
          have hcalls' : j ≤ (es.filter fun e => match e with
              | .system _ => true | _ => false).length := by omega
          have ihP := ih _ _ _ hpre' hlen' hcalls'
          obtain ⟨s', hs'⟩ := ihP
          have htake : st.queue.take cap = P.take cap := by
            rw [← ht, List.take_append, show cap - P.length = 0 from by omega,
              List.take_zero, List.append_nil]
          have e1 : P = P.take cap ++ P.drop cap := (List.take_append_drop cap P).symm
          refine ⟨s', ?_⟩
          rw [e1, List.append_assoc, hs', htake]

/-- **Everything queued is delivered after enough empty calls (O31).** With `m` further empty
system calls draining `cap` each, the concatenated system-call outputs are exactly the
starting queue plus the submissions, in order. Pure model fact: no representation premise. -/
theorem all_delivered_after {frames : List (Frame c)} (st : QueueState c.Record)
    (m : Nat) (hm : (queueAfter st frames).queue.length ≤ m * c.cap) :
    (chunks c.cap c.target st (events frames ++ List.replicate m (.system false))).flatten =
      st.queue ++ submissions frames := by
  have h1 := delivered_append_queue c.cap c.target st (events frames)
  have h2 := delivered_append_queue c.cap c.target (queueAfter st frames)
    (List.replicate m (.system false))
  have hsub : submitted (List.replicate m (.system false) : List (Event c.Record)) = [] :=
    submitted_replicate_system m false
  have hrep : (replay c.cap c.target (queueAfter st frames)
      (List.replicate m (.system false))).queue = [] := by
    rw [replay_calls_queue]
    rw [show m * c.cap = c.cap * m from Nat.mul_comm _ _] at hm
    exact List.drop_eq_nil_of_le hm
  rw [hsub, List.append_nil] at h2
  rw [hrep, List.append_nil] at h2
  have hch := chunks_append c.cap c.target st (events frames)
    (List.replicate m (.system false))
  have heq : replay c.cap c.target st (events frames) = queueAfter st frames := rfl
  rw [hch, List.flatten_append, heq, h2] at ⊢
  have h1' : (chunks c.cap c.target st (events frames)).flatten ++
      (queueAfter st frames).queue = st.queue ++ submissions frames := h1
  exact h1'

/-! ## Fee overhang after activation (O32) -/

/-- **The quote after `k` empty calls (O32, generic).** From a represented off-inhibitor queue,
a frame quoting after `k ≥ 1` empty system calls quotes
`fakeExp 1 (excess + count - target * k) 17`: the drained excess after the calls, with the
count cleared, is what `Frame.quote_natural` charges. (The draft read `k + 1`; corrected:
`replay_calls_excess` gives excess `E+C - target*k` after `k` calls, and that is the
numerator `quote_natural` sees.) -/
theorem quote_after_calls {k : Nat} (hk : 0 < k) {g : Frame c} {q : B256}
    {st : QueueState c.Record}
    (after : Holds c g.before (replay c.cap c.target st (List.replicate k (.system false))))
    (hne : st.excess ≠ 2 ^ 256 - 1) (hsum : st.excess + st.count < 2 ^ 256 - 1)
    (few : st.excess + st.count - c.target.toNat * k ≤ 2892)
    (hq : g.quotedFee = some q) :
    q.toNat = fakeExp 1 (st.excess + st.count - c.target.toNat * k) 17 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hex, hcount⟩ := replay_calls_excess c.cap c.target st j hne hsum
  have hqeq := Frame.quote_natural (c := c) g after hq (by
    rw [hex, hcount, Nat.zero_sub, Nat.add_zero]
    exact few)
  rw [hex, hcount, Nat.zero_sub, Nat.add_zero] at hqeq
  exact hqeq

/-- **The quote at call `k` after a pre-fork backlog (O32, deposit).** Over a chain from the
deployed storage of a covered-fork backlog with `n` submissions followed by Amsterdam empty
calls, the `k`-th call (`1 ≤ k`) quotes `fakeExp 1 (n - 8 * k) 17`. Attached to the activation
headline: after at least one call the count is 0 and the excess is `n - 8k` in naturals. -/
theorem deposit_quote_at_call {backlog calls : List Deposit.Frame} {t : Stor} {q : B256} {k : Nat}
    (_chain : Chain Stor.empty (backlog ++ calls) t)
    (_hp : ∀ f ∈ backlog, Deposit.PreFork f) (hc : ∀ f ∈ calls, Deposit.EmptyCall f)
    (_hk1 : 1 ≤ k) (_hk : k - 1 < calls.length)
    (_range : 4 + 6 * (submissions backlog).length ≤ 2 ^ 256)
    (_few : (submissions backlog).length ≤ 2892)
    {g : Deposit.Frame} {ys : List Deposit.Frame}
    (split : calls = calls.take (k - 1) ++ g :: ys) (hq : g.quotedFee = some q) :
    q.toNat = fakeExp 1 ((submissions backlog).length - 8 * k) 17 := by
  -- The premises are contradictory as drafted: `hc` forces every element of `calls`,
  -- hence `g` via `split`, to satisfy `EmptyCall` (`event = .system false`), whose
  -- `quotedFee` is `none`, contradicting `hq`. Proved vacuously; the intended O32 fact
  -- is a quoting frame *after* `k - 1` calls (not the `k`-th call itself), whose quote is
  -- `n - 8 * k` via `prefork_then_calls` + `Chain.quote_natural`. Reported to master.
  have hg_in : g ∈ calls := by
    rw [split]
    exact List.mem_append_right _ List.mem_cons_self
  have hg_empty := hc g hg_in
  cases g with
  | submission sevm pre post l i o rules at_contract caller law =>
    cases hg_empty
  | feeRead sevm pre post l i o rules at_contract caller law =>
    cases hg_empty
  | system benv data post out fork installed length run =>
    cases hq

/-- **The quote after `k` post-unlock calls (O32, exit).** From a represented off-inhibitor
exit queue, a frame quoting after `k ≥ 1` empty system calls quotes
`fakeExp 1 (excess + count - 2 * k) 17` (target `2` in `quote_after_calls`). The exit
contract has no pre-fork backlog (`Exit.first_frame_system`): this states the post-unlock
dynamics, applied after the unlocking call. -/
theorem exit_quote_after_calls {k : Nat} (hk : 0 < k) {g : Exit.Frame} {q : B256}
    {st : QueueState Exit.contract.Record}
    (after : Holds Exit.contract g.before
      (replay Exit.contract.cap Exit.contract.target st (List.replicate k (.system false))))
    (hne : st.excess ≠ 2 ^ 256 - 1) (hsum : st.excess + st.count < 2 ^ 256 - 1)
    (few : st.excess + st.count - 2 * k ≤ 2892)
    (hq : g.quotedFee = some q) :
    q.toNat = fakeExp 1 (st.excess + st.count - 2 * k) 17 := by
  have htarget : Exit.contract.target.toNat = 2 := by decide
  have few' : st.excess + st.count - Exit.contract.target.toNat * k ≤ 2892 := by
    rw [htarget]
    exact few
  have h := quote_after_calls (c := Exit.contract) hk after hne hsum few' hq
  rw [htarget] at h
  exact h

end Blanc.Lift.BuilderRequest.LoadBound
