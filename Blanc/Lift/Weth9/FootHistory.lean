import Blanc.Lift.Weth9.FootFrame
import Blanc.ContractAdmissionSem
import Blanc.ExecutionHistoryAdmission
import Blanc.ExecutionTraceAdmission

/-!
# WETH9 footprint history: trace-local hash premises only

`weth9_history_preserves_solvent` (`Solvency.lean`) proves backing of a *deduplicated* booked ledger
and needs, at every entered frame, `AllowAdmitted`: the allowance slots that frame could write avoid
**every** address's balance slot — a universal statement over all addresses, which no collision
resistance implies and no proof can inhabit.

`weth9_history_footprint` replaces it by the Curve-style footprint form:

* **initial footprint, once**: a set `K₀` of tracked keys and `FootInv K₀` at the checkpoint — every
  nonzero storage word at the contract is at a fixed slot (`name`, `symbol`, `decimals`: slots
  0, 1, 2) or at a tracked key's slot; tracked slots are pairwise distinct and apart from the fixed
  slots; the tracked balance words, summed as natural numbers, are backed by the contract's ether.
  `FootInv.deployed` shows the empty footprint holds of deployment-shaped storage with no hash fact;
* **freshness, once**: `KeysFresh K₀ (historyTouchedKeys ca trace)` — the keys the trace's raw target
  frames (rolled-back ones included) may touch are tracked or on slots in no use, and touched keys
  sharing a slot are one key.  This is the whole hash premise: a *finite*, *trace-local*
  collision-freedom statement about the keys this trace mentions, not about all addresses;
* **conclusion**: the code is unchanged, and the footprint `FootInv (K₀ ∪ touched)` holds at the
  future state: every nonzero word sits at a fixed or tracked slot, and the tracked balance words
  total at most the contract's ether.

Nothing else is assumed of the trace: interpreter ingress, non-target movements, rollback and the
`CALL` of `withdraw` are discharged by the configured-history ladder, exactly as in Curve's
`c3crv_history_carried`.
-/

namespace Blanc.Lift.Weth9

open Jaune
open Blanc
open Blanc.Lift
open Blanc.ExecutionTrace

/-- The entry condition of the footprint ladder: the keys the frame's call may touch are tracked. -/
def footEntry (U : Key → Prop) : Sevm → Devm → Prop := fun sevm _ => ∀ k ∈ frameKeys sevm, U k

/-- **WETH9 frame soundness over a tracked universe, trace-admitted.** -/
theorem footSpec_soundAdmitted (ca : Adr) {U : Key → Prop} (hinj : KeyInj U) :
    (footSpec U).SoundAdmitted ca (footEntry U) := by
  intro sevm pre post hfork execution hrun hca admitted ih _ hpre
  subst hca
  have hin := lift_sound_in cert_check hrun.1 hfork execution
  exact foot_frame_post_in hinj (R := ⟨0, sevm, pre, .ok post, execution⟩) hfork hin
    (admitted.root rfl) admitted ih hpre

/-- **WETH9 frame preservation over a tracked universe, trace-admitted**: the form the trace rungs
consume. -/
theorem footSpec_preservesAdmitted (ca : Adr) {U : Key → Prop} (hinj : KeyInj U) :
    (footSpec U).PreservesAdmitted ca (footEntry U) :=
  (footSpec U).preserves_inv_admitted ca (footEntry U) (footSpec_soundAdmitted ca hinj)

/-- The keys the actual raw target entries of this history may touch, including entries whose
effects later roll back. -/
def historyTouchedKeys {cfg : ChainConfig} {checkpoint future : BlockChain}
    (ca : Adr) (trace : ConfiguredHistoryTrace cfg checkpoint future) : List Key :=
  trace.rawFrames.flatMap fun root =>
    if root.sevm.currentTarget = ca then frameKeys root.sevm else []

/-- The tracked universe: the initial keys together with every key a raw target entry may touch. -/
def historyKeyUniverse {cfg : ChainConfig} {checkpoint future : BlockChain}
    (ca : Adr) (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (initialKeys : Key → Prop) : Key → Prop :=
  Key.extend initialKeys (historyTouchedKeys ca trace)

/-- A raw target entry's keys belong to the trace-selected universe. -/
theorem touchedKeys_mem {cfg : ChainConfig} {checkpoint future : BlockChain}
    {ca : Adr} {trace : ConfiguredHistoryTrace cfg checkpoint future}
    {root : Exec.Deriv} (member : root ∈ trace.rawFrames)
    (target : root.sevm.currentTarget = ca) {k : Key} (touched : k ∈ frameKeys root.sevm) :
    k ∈ historyTouchedKeys ca trace := by
  apply List.mem_flatMap.mpr
  exact ⟨root, member, by simpa only [target, ite_true] using touched⟩

/-- **WETH9 history footprint (universe form).**  From one initial footprint `K₀` and the
trace-local freshness of the keys the trace touches, the future state carries the footprint over
`K₀ ∪ touched`: the deployed code is intact, every nonzero storage word sits at a fixed slot or a
tracked slot, the tracked slots are injective and off the fixed slots, and the tracked balance
words total at most the contract's ether. -/
theorem weth9_history_footprint_universe {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = weth9Sem.image)
    (sumNof : SumNof checkpoint.state.bal)
    (initial : FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca))
    (fresh : KeysFresh K₀ (historyTouchedKeys ca trace)) :
    some (future.state.getCode ca).toList = weth9Sem.image ∧ SumNof future.state.bal ∧
      FootInv (historyKeyUniverse ca trace K₀) (future.state.getStor ca)
        (future.state.bal ca) := by
  let U := historyKeyUniverse ca trace K₀
  have extended : FootInv U (checkpoint.state.getStor ca) (checkpoint.state.bal ca) :=
    initial.extend fresh
  have admitted : trace.FrameAdmitted ca (footEntry U) := by
    apply (trace.frameAdmitted_iff_rawFrames ca _).2
    intro root member target k hk
    exact Or.inr (touchedKeys_mem member target hk)
  have start : (footSpec U).StateInv ca checkpoint.state :=
    footSpec_stateInv_iff.mpr ⟨installed, sumNof, extended.support, extended.backed⟩
  have finish := trace.stateInv_admitted_sem (footSpec_preservesAdmitted ca extended.inj)
    admitted start
  obtain ⟨hcode, hside, hsup, hback⟩ := footSpec_stateInv_iff.mp finish
  exact ⟨hcode, hside, ⟨hsup, extended.inj, extended.apart, hback⟩⟩

/-- **WETH9 history footprint.**  A configured history from a checkpoint with the footprint `K₀`,
whose touched keys are fresh against it, ends in a state whose contract has the deployed code and a
footprint `K ⊆ K₀ ∪ touched`: every nonzero storage word is at a fixed slot or a tracked slot and
the tracked balance words total at most the contract's ether. -/
theorem weth9_history_footprint {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = weth9Sem.image)
    (sumNof : SumNof checkpoint.state.bal)
    (initial : FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca))
    (fresh : KeysFresh K₀ (historyTouchedKeys ca trace)) :
    some (future.state.getCode ca).toList = weth9Sem.image ∧
      ∃ K : Key → Prop, (∀ k, K k → K₀ k ∨ k ∈ historyTouchedKeys ca trace) ∧
        FootInv K (future.state.getStor ca) (future.state.bal ca) := by
  obtain ⟨hcode, -, hfoot⟩ := weth9_history_footprint_universe trace installed sumNof initial fresh
  exact ⟨hcode, historyKeyUniverse ca trace K₀, fun _ hk => hk, hfoot⟩

/-- **The ledger reading**: at the future state the tracked holders' stored balances are backed by
the contract's ether, in total and one by one, and an address on neither a fixed nor a tracked slot
books nothing. -/
theorem weth9_history_backed {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = weth9Sem.image)
    (sumNof : SumNof checkpoint.state.bal)
    (initial : FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca))
    (fresh : KeysFresh K₀ (historyTouchedKeys ca trace)) :
    trackedSum (historyKeyUniverse ca trace K₀) (future.state.getStor ca) ≤
        (future.state.bal ca).toNat ∧
      (∀ a, historyKeyUniverse ca trace K₀ (.bal a) →
        ((future.state.getStor ca).get (balSlot a)).toNat ≤ (future.state.bal ca).toNat) ∧
      (∀ a, balSlot a ∉ fixedSlots →
        (∀ k, historyKeyUniverse ca trace K₀ k → k.slot ≠ balSlot a) →
        (future.state.getStor ca).get (balSlot a) = 0) := by
  obtain ⟨-, -, hfoot⟩ := weth9_history_footprint_universe trace installed sumNof initial fresh
  exact ⟨hfoot.backed, fun a ha => hfoot.balance_le ha,
    fun a hfix hK => hfoot.balance_eq_zero hfix hK⟩

end Blanc.Lift.Weth9
