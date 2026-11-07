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

/-- The fee is monotone in the excess: a larger numerator quotes no less. -/
theorem fakeExp_mono {a b : Nat} (h : a ≤ b) : fakeExp 1 a 17 ≤ fakeExp 1 b 17 := by
  -- DRAFT: no monotonicity lemma for `fakeExp` exists in Blanc (`FakeExponential.lean`,
  -- `FakeExponentialGrowth.lean` only give lower bounds via `factor_mul_pow_le`); the Jaune
  -- source is not vendored in this worktree, so check Jaune pin `e8db2742` for an existing
  -- statement first. Expected route: pointwise `≤` of the `fakeExpAux` accumulators by
  -- induction on the fuel-bounded evaluator (`FakeExponentialEval.runFuel`), or on Jaune's
  -- `fakeExpAux` equation lemmas once its definition is read.
  sorry

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
  -- DRAFT: cases `f`, mirroring `Frame.step_holds`. Submission: `load` grows by exactly one
  -- (`load_submit`); the quote's numerator `st.excess + (st.count - target)` is at most
  -- `load st` (so `Frame.quote_natural` applies: `load st ≤ 2892` from `wrap` via `cost_ge_self`
  -- and `Backlog.cost_strictMono`, and the frame ran off the inhibitor by `Frame.quoted_active`
  -- with `rep.excess`) and at least `load st - target`, so `fakeExp_mono` gives
  -- `Backlog.fee target (load st) ≤ q.toNat = feePaid f`, and the goal is the cost successor
  -- equation. Fee read: load and `feePaid` are both unchanged. System call: `load_step` (with
  -- `range` and `rep.excess_lt`) gives `load` no larger, then `cost_mono`.
  sorry

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
  -- DRAFT: induction on `chain` generalizing `st`, mirroring `Chain.holds`: the `nil` case is
  -- `Nat.le_add_right` (`fees [] = 0` by `rfl`); the `cons` case applies `step_potential` to the
  -- head (prefix bounds via `queueBase_mono`, `(submitted [f.event]).length ≤ 1`, `rep.excess_lt`)
  -- and the induction hypothesis to the tail with `f.step_holds`'s representation, the tail
  -- bounds via `step_tail_le` / `step_count_le` / `load_step` + `load_submit`, and `wrap`
  -- preserved by `cost_mono` with the step bound (`fees (f :: rest) = feePaid f + fees rest`
  -- by `fees_cons`).
  sorry

/-! ## Deployed instances (O31) -/

/-- **The potential from the deposit deployment (O31).** Over any chain from the deployed
storage, `Φ` of the end load is at most the fees paid. -/
theorem deposit_potential {frames : List Deposit.Frame} {t : Stor}
    (chain : Chain Stor.empty frames t)
    (range : 4 + 6 * (submissions frames).length ≤ 2 ^ 256)
    (wrap : fees frames < Backlog.cost 8 0 2893) :
    Backlog.cost 8 0 (load (queueAfter Deposit.deployedQueue frames)) ≤ fees frames := by
  -- DRAFT: `potential_le` with `Deposit.deployed_represents`; `load Deposit.deployedQueue = 0`
  -- by `decide` (as in `Deposit.Delivery`'s `excess_dynamics` context) and
  -- `Backlog.cost Deposit.contract.target.toNat 0 0 = 0` by `rfl`, so the starting potential
  -- vanishes; `Deposit.contract.target.toNat = 8`, `.width = 6`, `.cap = 64` by `decide`/`rfl`
  -- (`abbrev` contract), discharging `slots`/`count`/`range` from `range` by `omega`.
  sorry

/-- **The potential from the exit deployment (O31).** Over any chain from the deployed storage,
`Φ` of the end load is at most the fees paid. -/
theorem exit_potential {frames : List Exit.Frame} {t : Stor}
    (chain : Chain Exit.deployedStorage frames t)
    (range : 4 + 3 * (submissions frames).length ≤ 2 ^ 256)
    (wrap : fees frames < Backlog.cost 2 0 2893) :
    Backlog.cost 2 0 (load (queueAfter Exit.deployedQueue frames)) ≤ fees frames := by
  -- DRAFT: as `deposit_potential`, with `Exit.deployed_represents`,
  -- `load Exit.deployedQueue = 0` by `decide` (as in `Exit.Delivery.excess_dynamics`), and
  -- `Exit.contract.target.toNat = 2`, `.width = 3`, `.cap = 16`.
  sorry

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
an off-inhibitor queue, the queued records are at most `excess + count`. -/
theorem queue_length_le_load {s t : Stor} {frames : List (Frame c)} (chain : Chain s frames t)
    {st : QueueState c.Record} (rep : Holds c s st)
    (slots : queueBase c.width (st.tail + (submissions frames).length) ≤ 2 ^ 256)
    (count : st.count + (submissions frames).length < 2 ^ 256)
    (range : load st + (submissions frames).length < 2 ^ 256)
    (rp : RequestPhaseOnly frames) (cap_ge : c.target.toNat ≤ c.cap)
    (start_off : st.excess ≠ 2 ^ 256 - 1) :
    (queueAfter st frames).queue.length ≤ load (queueAfter st frames) := by
  -- DRAFT: induction on `chain` generalizing `st`, carrying the representation (via
  -- `f.step_holds`), the off-inhibitor fact (via `excess_inhibitor` with
  -- `inhibitedAfter_requestPhase`: under `RequestPhaseOnly` the end is inhibited exactly when
  -- the start is), and the per-prefix `slots`/`count`/`range` (via `queueBase_mono`,
  -- `step_tail_le`, `step_count_le`, `load_step` + `load_submit`). Submission: queue and load
  -- both grow by one. Fee read: neither moves. Empty system call: the queue drops `cap`
  -- (`drainedState_queue`, `List.length_drop`) while the load becomes `excess + count - target`
  -- (`drained_excess_natural`, off the inhibitor), and `len - cap ≤ excess + count - target`
  -- from the induction hypothesis with `cap_ge`.
  sorry

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
  -- DRAFT: `wrap` for `deposit_potential` from `hb`: `10 ^ 18 < Backlog.cost 8 0 665`
  -- (as in `reach_1_eth`, via `cost_664.2`) and `Backlog.cost 8 0 665 ≤ Backlog.cost 8 0 2893`
  -- by `cost_mono`; then `Backlog.cost 8 0 (load _) ≤ fees frames ≤ 10 ^ 18 ≤
  -- Backlog.cost 8 0 664` gives `load _ ≤ 664` by `Backlog.cost_strictMono`, and the queue
  -- bound by `queue_length_le_load` with `Deposit.deployed_represents`, start off the inhibitor
  -- by `decide`, `cap_ge` (`8 ≤ 64`) by `decide`, and `slots`/`count`/`range` from `range`.
  sorry

/-- 100 ETH of fees bounds a deposit list: load and queue length at most 743. -/
theorem deposit_load_le_743 {frames : List Deposit.Frame} {t : Stor}
    (chain : Chain Stor.empty frames t) (rp : RequestPhaseOnly frames)
    (range : 4 + 6 * (submissions frames).length ≤ 2 ^ 256)
    (hb : fees frames ≤ 100 * 10 ^ 18) :
    load (queueAfter Deposit.deployedQueue frames) ≤ 743 ∧
      (queueAfter Deposit.deployedQueue frames).queue.length ≤ 743 := by
  -- DRAFT: as `deposit_load_le_664`, via `cost_743`.
  sorry

/-- 120M ETH of fees bounds a deposit list: load and queue length at most 981. -/
theorem deposit_load_le_981 {frames : List Deposit.Frame} {t : Stor}
    (chain : Chain Stor.empty frames t) (rp : RequestPhaseOnly frames)
    (range : 4 + 6 * (submissions frames).length ≤ 2 ^ 256)
    (hb : fees frames ≤ 120000000 * 10 ^ 18) :
    load (queueAfter Deposit.deployedQueue frames) ≤ 981 ∧
      (queueAfter Deposit.deployedQueue frames).queue.length ≤ 981 := by
  -- DRAFT: as `deposit_load_le_664`, via `cost_981`.
  sorry

/-- 1 ETH of fees bounds an exit list: load and queue length at most 658. -/
theorem exit_load_le_658 {frames : List Exit.Frame} {t : Stor}
    (chain : Chain Exit.deployedStorage frames t) (rp : RequestPhaseOnly frames)
    (range : 4 + 3 * (submissions frames).length ≤ 2 ^ 256)
    (hb : fees frames ≤ 10 ^ 18) :
    load (queueAfter Exit.deployedQueue frames) ≤ 658 ∧
      (queueAfter Exit.deployedQueue frames).queue.length ≤ 658 := by
  -- DRAFT: load bound as `deposit_load_le_664`, via `exit_potential` and `Exit.cost_658`
  -- (`Backlog.cost 2 0 658/659`, in `Exit/Flood.lean`). Queue bound: the deployed storage holds
  -- the inhibitor, so split the first frame (`Exit.first_frame_system` gives a system call,
  -- `RequestPhaseOnly` forces it empty): after it the queue is empty and slot 0 is clear, then
  -- `queue_length_le_load` on the tail with `cap_ge` (`2 ≤ 16`) by `decide`.
  sorry

/-- 100 ETH of fees bounds an exit list: load and queue length at most 737. -/
theorem exit_load_le_737 {frames : List Exit.Frame} {t : Stor}
    (chain : Chain Exit.deployedStorage frames t) (rp : RequestPhaseOnly frames)
    (range : 4 + 3 * (submissions frames).length ≤ 2 ^ 256)
    (hb : fees frames ≤ 100 * 10 ^ 18) :
    load (queueAfter Exit.deployedQueue frames) ≤ 737 ∧
      (queueAfter Exit.deployedQueue frames).queue.length ≤ 737 := by
  -- DRAFT: as `exit_load_le_658`, via `Exit.cost_737`.
  sorry

/-- 120M ETH of fees bounds an exit list: load and queue length at most 975. -/
theorem exit_load_le_975 {frames : List Exit.Frame} {t : Stor}
    (chain : Chain Exit.deployedStorage frames t) (rp : RequestPhaseOnly frames)
    (range : 4 + 3 * (submissions frames).length ≤ 2 ^ 256)
    (hb : fees frames ≤ 120000000 * 10 ^ 18) :
    load (queueAfter Exit.deployedQueue frames) ≤ 975 ∧
      (queueAfter Exit.deployedQueue frames).queue.length ≤ 975 := by
  -- DRAFT: as `exit_load_le_658`, via `Exit.cost_975`.
  sorry

/-! ## A record waits a bounded number of calls (O31) -/

/-- A queued prefix reached within `k` calls is delivered: any prefix of the starting queue
with at most `k * cap` records is a prefix of what the events' system calls deliver. -/
theorem delivered_prefix {Record : Type} (cap : Nat) (target : B256) (st : QueueState Record)
    (es : List (Event Record)) (P : List Record) (k : Nat)
    (hpre : P <+: st.queue) (hlen : P.length ≤ k * cap)
    (hcalls : k ≤ (es.filter fun e => match e with
      | .system _ => true | _ => false).length) :
    P <+: (chunks cap target st es).flatten := by
  -- DRAFT: induction on `es` generalizing `st P k`: submission extends both the queue and the
  -- bound (`submitted` append); fee read changes nothing; system call discharges `cap` records
  -- of the prefix (`chunk` is `take cap`, `List.take_append_drop`) and one call of the count.
  sorry

/-- **Everything queued is delivered after enough empty calls (O31).** With `m` further empty
system calls draining `cap` each, the concatenated system-call outputs are exactly the
starting queue plus the submissions, in order. Pure model fact: no representation premise. -/
theorem all_delivered_after {frames : List (Frame c)} (st : QueueState c.Record)
    (m : Nat) (hm : (queueAfter st frames).queue.length ≤ m * c.cap) :
    (chunks c.cap c.target st (events frames ++ List.replicate m (.system false))).flatten =
      st.queue ++ submissions frames := by
  -- DRAFT: `chunks_append` splits the frames from the calls; `delivered_append_queue` twice
  -- (once for `events frames`, once for the replicated calls on the queue after them, whose
  -- flattened output plus the drained remainder is that queue: `replay_calls_queue` with `hm`
  -- gives an empty remainder via `List.drop_eq_nil_of_le`, and `submitted_replicate_system`
  -- shows the calls submit nothing, so the second `delivered_append_queue` closes with
  -- `List.nil_append`).
  sorry

/-! ## Fee overhang after activation (O32) -/

/-- **The quote after `k` empty calls (O32, generic).** From a represented off-inhibitor queue
with `excess + count` below the wrap, a frame quoting after `k ≥ 1` empty system calls quotes
`fakeExp 1 (excess + count - target * (k + 1)) 17`. -/
theorem quote_after_calls {k : Nat} (hk : 0 < k) {g : Frame c} {q : B256}
    {st : QueueState c.Record}
    (after : Holds c g.before (replay c.cap c.target st (List.replicate k (.system false))))
    (hne : st.excess ≠ 2 ^ 256 - 1) (hsum : st.excess + st.count < 2 ^ 256 - 1)
    (few : st.excess + st.count - c.target.toNat * (k + 1) ≤ 2892)
    (hq : g.quotedFee = some q) :
    q.toNat = fakeExp 1 (st.excess + st.count - c.target.toNat * (k + 1)) 17 := by
  -- DRAFT: write `k = j + 1`; `replay_calls_excess` gives the drained excess
  -- `st.excess + st.count - target * (j + 1)` and count `0`; `Frame.quote_natural` with `after`
  -- and `few` gives the quote, and the numerator `(excess' + (0 - target))` is
  -- `st.excess + st.count - target * (k + 1)` by `Nat.sub_sub` and `Nat.mul_succ`.
  sorry

/-- **The quote at call `k` after a pre-fork backlog (O32, deposit).** Over a chain from the
deployed storage of a covered-fork backlog with `n` submissions followed by Amsterdam empty
calls, the `k`-th call (`1 ≤ k`) quotes `fakeExp 1 (n - 8 * k) 17`. Attached to the activation
headline: after at least one call the count is 0 and the excess is `n - 8k` in naturals. -/
theorem deposit_quote_at_call {backlog calls : List Deposit.Frame} {t : Stor} {q : B256} {k : Nat}
    (chain : Chain Stor.empty (backlog ++ calls) t)
    (hp : ∀ f ∈ backlog, Deposit.PreFork f) (hc : ∀ f ∈ calls, Deposit.EmptyCall f)
    (hk1 : 1 ≤ k) (hk : k - 1 < calls.length)
    (range : 4 + 6 * (submissions backlog).length ≤ 2 ^ 256)
    (few : (submissions backlog).length ≤ 2892)
    {g : Deposit.Frame} {ys : List Deposit.Frame}
    (split : calls = calls.take (k - 1) ++ g :: ys) (hq : g.quotedFee = some q) :
    q.toNat = fakeExp 1 ((submissions backlog).length - 8 * k) 17 := by
  -- DRAFT: set `xs := backlog ++ calls.take (k - 1)`; `Chain.append_split` twice gives a chain
  -- over `xs ++ g :: _`; `Chain.quote_natural` with `Deposit.deployed_represents`
  -- (`load Deposit.deployedQueue = 0` by `decide`, `slots`/`count` from `range` since the calls
  -- submit nothing by `events_calls` on the taken prefix and `submitted_replicate_system`, and
  -- `few`) quotes the queue after `xs`. That queue: with `k - 1 = 0`, excess `0` and count `n`
  -- (`excess_noSystem` / `count_noSystem` with `Deposit.noSystem_preFork`); with `k - 1 ≥ 1`,
  -- excess `n - 8 * (k - 1)` and count `0` (`Deposit.prefork_then_calls` on the split chain).
  -- Both give numerator `n - 8 * k` by `omega`.
  sorry

/-- **The quote after `k` post-unlock calls (O32, exit).** From a represented off-inhibitor
exit queue, a frame quoting after `k ≥ 1` empty system calls quotes
`fakeExp 1 (excess + count - 2 * (k + 1)) 17`. The exit contract has no pre-fork backlog
(`Exit.first_frame_system`): this states the post-unlock dynamics, applied after the
unlocking call. -/
theorem exit_quote_after_calls {k : Nat} (hk : 0 < k) {g : Exit.Frame} {q : B256}
    {st : QueueState Exit.contract.Record}
    (after : Holds Exit.contract g.before
      (replay Exit.contract.cap Exit.contract.target st (List.replicate k (.system false))))
    (hne : st.excess ≠ 2 ^ 256 - 1) (hsum : st.excess + st.count < 2 ^ 256 - 1)
    (few : st.excess + st.count - 2 * (k + 1) ≤ 2892)
    (hq : g.quotedFee = some q) :
    q.toNat = fakeExp 1 (st.excess + st.count - 2 * (k + 1)) 17 := by
  -- DRAFT: specialization of `quote_after_calls` at `Exit.contract`
  -- (`Exit.contract.target.toNat = 2` by `decide`).
  sorry

end Blanc.Lift.BuilderRequest.LoadBound
