import Blanc.Lift.BuilderRequest.Flood
import Blanc.Lift.BuilderRequest.Exit.Delivery

/-!
# The exit flood

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`; the bytes and `sys-asm` `83f9801`.

The exit contract has no 1 ETH floor: a submission pays only the fee, from 1 wei up, so a queue is cheap to start and the fee is what stops it. `backlogCost n` is the sum of the quotes,
at slot 0 zero, over counts below `n`, and it is exponential. So 1 ETH reaches 658 exits, 100 ETH reaches 737 and 120,000,000 ETH reaches 975, and 16 per call drains them in 42, 47
and 61 calls, not fewer.

**What this is not.** These bound a sequence of fees within one stretch with no system call: a budget is a premise, and a real chain drains in between. Across system calls,
`submissions_le_paid` still bounds the number of exits by the wei paid, and that is what closes the word range.
-/

namespace Blanc.Lift.BuilderRequest.Exit

open Jaune
open RequestSystem
open Delivery
open Creation (address)

/-- The sum over `i < n` of the fee quoted at count `i`, with slot 0 at zero: no floor. -/
abbrev backlogCost : Nat → Nat := Backlog.cost 2 0

/-- The natural fee quoted at count `i` with slot 0 at zero. -/
abbrev quotedFee : Nat → Nat := Backlog.fee 2

/-- 1 ETH in wei. -/
def oneEther : Nat := 10 ^ 18

theorem cost_658 : Backlog.costEval 2 0 658 ≤ oneEther ∧ oneEther < Backlog.costEval 2 0 659 := by decide +kernel
theorem cost_737 : Backlog.costEval 2 0 737 ≤ 100 * oneEther ∧ 100 * oneEther < Backlog.costEval 2 0 738 := by decide +kernel
theorem cost_975 : Backlog.costEval 2 0 975 ≤ 120000000 * oneEther ∧ 120000000 * oneEther < Backlog.costEval 2 0 976 := by
  decide +kernel

/-- **1 ETH reaches 658 exits.** A sequence of `n` submissions paying the quotes fits in 1 ETH exactly when `n ≤ 658`. -/
theorem reach_1_eth (n : Nat) : (∃ paid, Backlog.Pays 2 0 paid n ∧ Backlog.total paid n ≤ oneEther) ↔ n ≤ 658 :=
  Backlog.reach_iff (by rw [← Backlog.costEval_eq (by omega)]; exact cost_658.1)
    (by rw [← Backlog.costEval_eq (by omega)]; exact cost_658.2) n

/-- **100 ETH reaches 737 exits.** -/
theorem reach_100_eth (n : Nat) : (∃ paid, Backlog.Pays 2 0 paid n ∧ Backlog.total paid n ≤ 100 * oneEther) ↔ n ≤ 737 :=
  Backlog.reach_iff (by rw [← Backlog.costEval_eq (by omega)]; exact cost_737.1)
    (by rw [← Backlog.costEval_eq (by omega)]; exact cost_737.2) n

/-- **120,000,000 ETH reaches 975 exits.** -/
theorem reach_supply (n : Nat) :
    (∃ paid, Backlog.Pays 2 0 paid n ∧ Backlog.total paid n ≤ 120000000 * oneEther) ↔ n ≤ 975 :=
  Backlog.reach_iff (by rw [← Backlog.costEval_eq (by omega)]; exact cost_975.1)
    (by rw [← Backlog.costEval_eq (by omega)]; exact cost_975.2) n

/-- **The calls that drain each instance**: `⌈n / 16⌉` is 42, 47 and 61. -/
theorem calls_instances : (658 + 15) / 16 = 42 ∧ (737 + 15) / 16 = 47 ∧ (975 + 15) / 16 = 61 := by decide

/-- **Repeated drains empty a queue of length `n` in `⌈n / 16⌉` steps.** -/
theorem drain_empties {Record : Type} (t : B256) (st : QueueState Record) :
    ((drainedState 16 t)^[(st.queue.length + 15) / 16] st).queue = [] :=
  Backlog.drain_empties (by decide) t st

/-- **And not fewer.** -/
theorem drain_not_fewer {Record : Type} (t : B256) (st : QueueState Record) {k : Nat}
    (hk : k < (st.queue.length + 15) / 16) : ((drainedState 16 t)^[k] st).queue ≠ [] :=
  Backlog.drain_not_fewer (by decide) t st hk

/-- **Repeated empty-calldata system calls drain the exit queue.** With no new submissions, `k` calls succeed, each at the state the last left. -/
theorem system_calls_drain {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode address = code) {st : QueueState Record}
    (rep : Represents 3 Record.word (storOf benv.state address) st) (k : Nat) :
    let drain := fun σ : State => sysState sysShape σ address
    Represents 3 Record.word (storOf (drain^[k] benv.state) address) ((drainedState 16 2)^[k] st) ∧
      (drain^[k] benv.state).getCode address = code ∧
      ∀ j, j < k → ∃ out,
        processCheckedSystemTransaction (benv.withState (drain^[j] benv.state)) address [] =
          .ok (drain^[j + 1] benv.state, out) :=
  SysCall.calls_drain sysCall (capN := 16) (by decide) rfl hfork installed rep k

/-! ## The tie to the bytes -/

/-- The word fee is the natural fee at count `i` on the domain, with slot 0 at zero. -/
theorem word_fee_eq {i n : Nat} {out : B256} (hi : i ≤ 2894)
    (quote : WordFakeExponential.Run (targetExcess 2 0 i.toB256) 17 1 17 0 n out) :
    (out / (17 : B256)).toNat = quotedFee i := by
  have hx : targetExcess 2 0 i.toB256 = (i - 2).toB256 := by
    apply B256.toNat_inj
    rw [targetExcess_toNat, B256.toNat_toB256_of_lt (by omega), show (2 : B256).toNat = 2 by decide,
      show (0 : B256).toNat = 0 by decide, Nat.zero_add, B256.toNat_toB256_of_lt (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hx] at quote
  exact RequestFeeWord.word_fee_eq_natural (by omega) quote

/-- **A submission at count `i` on the domain, with slot 0 at zero, pays at least the quote.** -/
theorem submission_pays {sevm : Sevm} {l : StorageSteps sevm} {pre post : Devm} {i n : Nat} {out : B256}
    (hi : i ≤ 2894) (slot0 : pre.getStorVal sevm.currentTarget 0 = 0)
    (slot1 : pre.getStorVal sevm.currentTarget 1 = i.toB256) (sub : SubmittedOn l pre post n out) :
    quotedFee i ≤ sevm.value.toNat := by
  have q := sub.quote
  rw [storedExcess, slot0, slot1] at q
  rw [← word_fee_eq hi q]
  exact sub.covered

/-- The value a chain of exit frames pays. -/
abbrev paid (frames : List Frame) : Nat := paidBy frames

/-! ## The word range, from a budget -/

theorem contract_small : Small contract := ⟨by decide, by decide⟩

/-- The fee at excess 2892, above `2 ^ 245`. -/
theorem fee_2892 :
    fakeExp 1 2892 17 = 76059800903738432429721259523001950250726052916847211303159755524395288041 := by
  have h : FakeExponentialEval.runFuel 512 2892 17 1 17 =
      some (462, 1293016615363553351305261411891033154262342899586402592153715843914719896707) := by
    decide +kernel
  have out := (FakeExponentialEval.run_of_runFuel h).output_eq
  show fakeExpAux 2892 17 1 17 / 17 = _
  rw [← out]

/-- **There are at most as many exits as wei paid**, system calls allowed. On a chain from the deployed storage paying at most `2 ^ 245` wei, far above all the ether that exists, every
submission quotes on the fee's domain, where the fee is at least 1 wei. So the fee's 1-wei lower bound does not need to be assumed. Above that budget nothing is stated: past excess 2892 the word quote
wraps, and it is not shown to stay positive. -/
theorem submissions_le_paid {frames : List Frame} {t : Stor} (chain : Chain deployedStorage frames t)
    (hb : paid frames ≤ 2 ^ 245) : (submissions frames).length ≤ paid frames := by
  have h245 : (2 : Nat) ^ 245 < fakeExp 1 2892 17 := by
    rw [fee_2892]
    decide
  have h250 : (2 : Nat) ^ 245 < 2 ^ 250 := by decide
  change paidBy frames ≤ _ at hb
  refine chain.submissions_le_paid contract_small deployed_represents ⟨fun _ => rfl, fun hne => absurd rfl hne⟩
    (by omega) ?_
  show 0 + paidBy frames < _
  omega

/-- **The word range, from a budget.** The gap W13 left: `delivery`'s `4 + 3 * n ≤ 2 ^ 256` holds on any chain from the deployed storage paying at most `2 ^ 245` wei. -/
theorem range_of_budget {frames : List Frame} {t : Stor} (chain : Chain deployedStorage frames t)
    (hb : paid frames ≤ 2 ^ 245) : 4 + 3 * (submissions frames).length ≤ 2 ^ 256 := by
  have h := submissions_le_paid chain hb
  have hbig : (2 : Nat) ^ 256 = 2048 * 2 ^ 245 := by decide
  have hbig2 : 4 ≤ (2 : Nat) ^ 245 := by decide
  rw [hbig]
  generalize (2 : Nat) ^ 245 = W at hb hbig2
  omega

/-- **Exact delivery within a budget.** `delivery`, with the word range replaced by the sequence paying at most `2 ^ 245` wei in all. -/
theorem delivery_of_budget {frames : List Frame} {t : Stor} (chain : Chain deployedStorage frames t)
    (hb : paid frames ≤ 2 ^ 245) :
    Represents 3 Record.word (fun key => t.get key) (queueAfter deployedQueue frames) ∧
      (queueAfter deployedQueue frames).queue =
        (submissions frames).drop (deliveredRecords deployedQueue frames) ∧
      systemOutput frames =
        ((submissions frames).take (deliveredRecords deployedQueue frames)).flatMap Record.out :=
  delivery chain (range_of_budget chain hb)

/-- **`transaction_ok`'s `noAlias`, from a budget.** After a chain from the deployed storage paying at most `2 ^ 245` wei, the tail in slot 3 is below `2 ^ 253`. -/
theorem tail_lt_of_budget {frames : List Frame} {t : Stor} (chain : Chain deployedStorage frames t)
    (hb : paid frames ≤ 2 ^ 245) : (t.get 3).toNat < 2 ^ 253 := by
  have hn := submissions_le_paid chain hb
  have hd := (delivery_of_budget chain hb).1
  have htl := queueAfter_tail_le deployedQueue frames
  have h3 : t.get 3 = (queueAfter deployedQueue frames).tail.toB256 := hd.tail
  rw [h3, B256.toNat_toB256_of_lt hd.tail_lt]
  have ht0 : deployedQueue.tail = 0 := rfl
  have hbig : (2 : Nat) ^ 253 = 256 * 2 ^ 245 := by decide
  have hbig2 : 1 ≤ (2 : Nat) ^ 245 := by decide
  rw [hbig]
  generalize (2 : Nat) ^ 245 = W at hb hbig2
  omega

/-- The cost a chain with no system call pays, from a represented queue at excess 0. -/
theorem backlog_paid {s t : Stor} {frames : List Frame} (chain : Chain s frames t)
    {st : QueueState Record} (rep : Holds contract s st) (he : st.excess = 0)
    (none : NoSystem (events frames))
    (slots : queueBase 3 (st.tail + (submissions frames).length) ≤ 2 ^ 256)
    (count : st.count + (submissions frames).length < 2 ^ 256) :
    backlogCost (min (st.count + (submissions frames).length) 2895) ≤
      backlogCost (min st.count 2895) + paid frames := by
  induction chain generalizing st with
  | nil s =>
    show backlogCost (min (st.count + 0) 2895) ≤ _ + 0
    exact Nat.le_refl _
  | @cons s f rest t hb tail ih =>
    subst hb
    have tailNone : NoSystem (events rest) := fun x hx => none x (List.mem_cons_of_mem _ hx)
    have hs : (submissions (f :: rest)).length =
        (submitted [f.event]).length + (submissions rest).length := submitted_cons_length _ _
    have hp : paid (f :: rest) = f.value + paid rest := paidBy_cons f rest
    rw [hs] at slots count ⊢
    rw [hp]
    obtain ⟨hrep, -⟩ := f.step_holds rep ((queueBase_mono 3 (by omega)).trans slots) (by omega)
    have htail := step_tail_le contract.cap contract.target st f.event
    have hcount := step_count_le contract.cap contract.target st f.event
    have hsl : queueBase 3 ((step contract.cap contract.target st f.event).tail + (submissions rest).length) ≤ 2 ^ 256 :=
      (queueBase_mono 3 (by omega)).trans slots
    cases f with
    | submission sevm pre post l i o rules target caller law =>
      have hl : (submitted [Delivery.Frame.event
          (.submission sevm pre post l i o rules target caller law : Frame)]).length = 1 := rfl
      rw [hl] at count ⊢
      have ih' := ih hrep he tailNone hsl (by
        show st.count + 1 + _ < _
        omega)
      change backlogCost (min (st.count + 1 + _) 2895) ≤
        backlogCost (min (st.count + 1) 2895) + _ at ih'
      by_cases hi : st.count ≤ 2894
      · have s0 : pre.getStorVal sevm.currentTarget 0 = 0 := by
          rw [target]
          have : (pre.getStor address).get 0 = st.excess.toB256 := rep.excess
          rw [he] at this
          exact this
        have s1 : pre.getStorVal sevm.currentTarget 1 = st.count.toB256 := by
          rw [target]
          exact rep.count
        have pays := submission_pays hi s0 s1 law
        have hv : Delivery.Frame.value (.submission sevm pre post l i o rules target caller law : Frame) =
            sevm.value.toNat := rfl
        rw [hv, Nat.min_eq_left (by omega : st.count ≤ 2895)]
        rw [Nat.min_eq_left (by omega : st.count + 1 ≤ 2895)] at ih'
        rw [show st.count + (1 + (submissions rest).length) = st.count + 1 + (submissions rest).length by omega]
        have hstep : backlogCost (st.count + 1) = backlogCost st.count + (quotedFee st.count + 0) := rfl
        omega
      · rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
        omega
    | feeRead sevm pre post l i o rules target caller law =>
      have hl : (submitted [Delivery.Frame.event
          (.feeRead sevm pre post l i o rules target caller law : Frame)]).length = 0 := rfl
      rw [hl, Nat.zero_add] at count ⊢
      have ih' := ih hrep he tailNone hsl count
      change backlogCost (min (st.count + _) 2895) ≤ backlogCost (min st.count 2895) + _ at ih'
      omega
    | system benv data post out fork installed length run =>
      exact absurd rfl (none _ List.mem_cons_self _)

/-- **A budget bounds the count on the frames' chain.** From storage at excess 0, count 0, say after the first system call, on a chain with no system call: a sequence paying less than
`backlogCost n`, `n ≤ 2895`, makes fewer than `n` submissions. -/
theorem count_lt_of_budget {s t : Stor} {frames : List Frame} {n : Nat} (chain : Chain s frames t)
    {st : QueueState Record} (rep : Holds contract s st) (he : st.excess = 0) (hc : st.count = 0)
    (none : NoSystem (events frames))
    (slots : queueBase 3 (st.tail + (submissions frames).length) ≤ 2 ^ 256)
    (count : (submissions frames).length < 2 ^ 256)
    (low : paid frames < backlogCost n) (hn : n ≤ 2895) : (submissions frames).length < n := by
  have h := backlog_paid chain rep he none slots (by omega)
  rw [hc] at h
  have h0 : backlogCost (min 0 2895) = 0 := rfl
  rw [h0, Nat.zero_add, Nat.zero_add] at h
  by_contra hge
  have hmin : n ≤ min (submissions frames).length 2895 := by omega
  rcases Nat.lt_or_eq_of_le hmin with hlt | heq
  · have : backlogCost n < backlogCost (min (submissions frames).length 2895) := Backlog.cost_strictMono hlt
    omega
  · rw [← heq] at h
    omega

end Blanc.Lift.BuilderRequest.Exit
