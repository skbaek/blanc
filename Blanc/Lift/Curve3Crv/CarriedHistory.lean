import Blanc.Lift.Curve3Crv.Ladder
import Blanc.ExecutionTraceAdmission
import Blanc.Lift.Curve3Crv.HistoryKeys

/-!
# Curve history from one carried model and live-key checkpoint

Keys are collected from actual raw target entries, including entries whose
effects later roll back. The independent collision condition on this universe
is therefore stronger than collision separation checked only against live
keys after rollback. The proof's live keys still extend dynamically.

The writer replay below carries concrete invocation and owner-answer evidence
from checked frame refinement. Its existential step list is not identified
with an exact trace-extracted invocation list; it states model reachability
from the one initial checkpoint, with no fresh conserving witness at entry.
`CommittedHistory.lean` (`c3crv_history_committed`) is the exact form: the model
run over the settlement-committed writer invocations extracted from the history.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune Blanc.ExecutionTrace

/-- Keys read or written by the actual raw target entries of this history.
Raw entries include failed or later rolled-back branches. -/
def historyTouchedKeys {cfg : ChainConfig} {checkpoint future : BlockChain}
    (ca : Adr) (trace : ConfiguredHistoryTrace cfg checkpoint future) : List Key :=
  trace.rawFrames.flatMap fun root =>
    if root.sevm.currentTarget = ca then
      callKeys root.sevm.caller (decodeCall root.sevm)
    else []

/-- The collision universe; initial live keys are supplemented only with keys
selected by actual raw entries. It is not the dynamic live-key carrier. -/
def historyKeyUniverse {cfg : ChainConfig} {checkpoint future : BlockChain}
    (ca : Adr) (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (initialKeys : Key → Prop) : Key → Prop :=
  Key.extend initialKeys (historyTouchedKeys ca trace)

/-- The independently recorded data of one writer invocation. -/
structure WriterInvocation where
  sevm : Sevm
  pre : Devm
  post : Devm
  ownerWord : Option B256

/-- A finite carried model replay with dynamic key extensions. Every appended
writer has a concrete deployed-code execution; its supplied owner word is
justified by that frame's actual static owner call. -/
inductive WriterReplay (ca : Adr) (initial : Blanc.Curve3Crv.State) (initialKeys : Key → Prop) :
    List WriterInvocation → Blanc.Curve3Crv.State → (Key → Prop) → Prop
  | nil : WriterReplay ca initial initialKeys [] initial initialKeys
  | snoc {frames : List WriterInvocation} {s : Blanc.Curve3Crv.State}
      {K : Key → Prop} {frame : WriterInvocation} {out : Blanc.Curve3Crv.Out}
      (prior : WriterReplay ca initial initialKeys frames s K)
      (execution : Exec 0 frame.sevm frame.pre (.ok frame.post))
      (target : frame.sevm.currentTarget = ca)
      (deployed : frame.sevm.code = code)
      (covered : CoveredFork frame.sevm.benvStat.fork)
      (writer : IsWriter (decodeCall frame.sevm))
      (owner : ∀ w, frame.ownerWord = some w →
        OwnerAnswer frame.sevm frame.pre s.minter w)
      (before : VyInv (Devm.getStor frame.pre ca) s K)
      (after : VyInv (Devm.getStor frame.post ca) out.1
        (Key.extend K (callKeys frame.sevm.caller (decodeCall frame.sevm))))
      (accepted : Blanc.Curve3Crv.step (c3ctx frame.sevm frame.ownerWord)
        (decodeCall frame.sevm) s = .ok out) :
      WriterReplay ca initial initialKeys (frames ++ [frame]) out.1
        (Key.extend K (callKeys frame.sevm.caller (decodeCall frame.sevm)))

/-- The live keys are exactly the initial keys plus keys touched by the
returned replay's writers. This identifies the replay's key carrier, not
its list with a trace-extracted list. -/
theorem WriterReplay.keys {ca : Adr} {initial : Blanc.Curve3Crv.State}
    {initialKeys : Key → Prop} {frames : List WriterInvocation}
    {s : Blanc.Curve3Crv.State} {K : Key → Prop}
    (replay : WriterReplay ca initial initialKeys frames s K) (k : Key) :
    K k ↔ initialKeys k ∨ k ∈ frames.flatMap
      (fun frame => callKeys frame.sevm.caller (decodeCall frame.sevm)) := by
  induction replay with
  | nil => simp
  | snoc prior execution target deployed covered writer owner before after accepted ih =>
      simp only [Key.extend, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.mem_append, ih, or_assoc]

/-- Carried state, reachable from one fixed initial checkpoint. The incoming
invariant supplies the witness at each later frame; admission supplies none. -/
def CarriedInvariant (ca : Adr) (initial : Blanc.Curve3Crv.State) (initialKeys U : Key → Prop)
    (stor : Stor) : Prop :=
  ∃ frames s K, WriterReplay ca initial initialKeys frames s K ∧
    (∀ k, K k → U k) ∧ VyInv stor s K

/-- A frame's independent conditions: bounded calldata and touched membership
in the collision universe. It contains no storage or conservation assertion. -/
def carriedEntry (U : Key → Prop) : Sevm → Devm → Prop := fun sevm _ =>
  sevm.data.length < 2 ^ 256 ∧ ∀ k ∈ callKeys sevm.caller (decodeCall sevm), U k

/-- Interpreter ingress is derived by the configured-history carrier. -/
def carriedFrameEntry (U : Key → Prop) : Sevm → Devm → Prop := fun sevm pre =>
  Exec.FreshEntry sevm pre ∧ carriedEntry U sevm pre

/-- A raw target entry's touched keys belong to the trace-selected universe. -/
theorem touchedKeys_mem {cfg : ChainConfig} {checkpoint future : BlockChain}
    {ca : Adr} {trace : ConfiguredHistoryTrace cfg checkpoint future}
    {root : Exec.Deriv} (member : root ∈ trace.rawFrames)
    (target : root.sevm.currentTarget = ca) {k : Key}
    (touched : k ∈ callKeys root.sevm.caller (decodeCall root.sevm)) :
    k ∈ historyTouchedKeys ca trace := by
  apply List.mem_flatMap.mpr
  exact ⟨root, member, by simpa only [target, ite_true] using touched⟩

/-- The history invariant supplies each later frame's model and live keys. -/
def c3crvCarriedSpec (ca : Adr) (initial : Blanc.Curve3Crv.State)
    (initialKeys U : Key → Prop) : ContractSpecSem :=
  ContractSpecSem.ofStorageOnly c3crvSem (CarriedInvariant ca initial initialKeys U)

/-- Frame soundness consumes the incoming carried witness. Admission asserts
only fresh interpreter ingress, calldata bound and universe membership. -/
theorem c3crvCarriedSpec_soundAdmitted (ca : Adr) (initial : Blanc.Curve3Crv.State)
    (initialKeys U : Key → Prop)
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) :
    (c3crvCarriedSpec ca initial initialKeys U).SoundAdmitted ca (carriedFrameEntry U) := by
  intro sevm pre post hfork execution deployed target admitted _ _ incoming
  subst target
  obtain ⟨⟨hstack, hmem⟩, hcd, touched⟩ := admitted.root rfl
  have carried : CarriedInvariant sevm.currentTarget initial initialKeys U
      (Devm.getStor pre sevm.currentTarget) :=
    ContractSpecSem.ofStorageOnly_preInv_iff.mp incoming.inv
  obtain ⟨frames, s, K, replay, included, invariant⟩ := carried
  have fresh := FreshKeys.of_universe injective apart included touched
  have refinement := c3crv_frame_refines_raw deployed hfork hcd hstack hmem
    invariant fresh execution
  refine ⟨trivial, ?_⟩
  show CarriedInvariant sevm.currentTarget initial initialKeys U
    (Devm.getStor post sevm.currentTarget)
  by_cases writer : IsWriter (decodeCall sevm)
  · obtain ⟨ow, owner, out, accepted, invariant', _⟩ := refinement.1 writer
    refine ⟨frames ++ [⟨sevm, pre, post, ow⟩], out.1,
      Key.extend K (callKeys sevm.caller (decodeCall sevm)), ?_, ?_, invariant'⟩
    · exact WriterReplay.snoc replay execution rfl deployed hfork writer owner
        invariant invariant' accepted
    · intro k hk
      rcases hk with hk | hk
      · exact included k hk
      · exact touched k hk
  · refine ⟨frames, s, K, replay, included, ?_⟩
    rw [(refinement.2 writer).1 sevm.currentTarget]
    exact invariant

/-- The frame preservation consumed by the actual configured-history ladder. -/
theorem c3crvCarriedSpec_preservesAdmitted (ca : Adr) (initial : Blanc.Curve3Crv.State)
    (initialKeys U : Key → Prop)
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) :
    (c3crvCarriedSpec ca initial initialKeys U).PreservesAdmitted ca (carriedFrameEntry U) :=
  (c3crvCarriedSpec ca initial initialKeys U).preserves_inv_admitted ca (carriedFrameEntry U)
    (c3crvCarriedSpec_soundAdmitted ca initial initialKeys U injective apart)

/-- A configured history carries one initial model and dynamically extends
its live keys. No later entry admits a storage abstraction or conservation.
The collision premise covers the initial keys and all actual raw target
entries, including rolled-back branches; it is conservative across rollback.

The returned writer list proves reachability from `initial`, with actual
successful target executions, owner-answer evidence, and pre/post storage
refinement at every step. It is not identified with an exact list extracted
from the history (see `c3crv_history_committed` for that identification).
Interpreter ingress, non-target movements and rollback
are discharged by the configured-history ladder. Initial storage/code
authentication and the truth of collision separation remain premises.

Superseded as a headline by `c3crv_history_committed`, which names the replayed invocations (the settlement-committed writer frames of the trace) instead of an existential replay. -/
theorem c3crv_history_carried {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initial : Blanc.Curve3Crv.State}
    {initialKeys : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = c3crvSem.image)
    (invariant : VyInv (checkpoint.state.getStor ca) initial initialKeys)
    (calldata : trace.FrameAdmitted ca (fun sevm _ => sevm.data.length < 2 ^ 256))
    (fresh : FreshKeys initialKeys (historyTouchedKeys ca trace)) :
    some (future.state.getCode ca).toList = c3crvSem.image ∧
      ∃ frames s K, WriterReplay ca initial initialKeys frames s K ∧
        (∀ k, K k → historyKeyUniverse ca trace initialKeys k) ∧
        VyInv (future.state.getStor ca) s K ∧ Blanc.Curve3Crv.Conserved s := by
  let U := historyKeyUniverse ca trace initialKeys
  have topology : VyInv (checkpoint.state.getStor ca) initial U := invariant.extend fresh
  have touched : trace.FrameAdmitted ca
      (fun sevm _ => ∀ k ∈ callKeys sevm.caller (decodeCall sevm), U k) := by
    apply (trace.frameAdmitted_iff_rawFrames ca _).2
    intro root member target k hk
    exact Or.inr (touchedKeys_mem member target hk)
  have admitted : trace.FrameAdmitted ca (carriedFrameEntry U) :=
    (trace.freshFrameAdmitted ca).and (calldata.and touched)
  have start : (c3crvCarriedSpec ca initial initialKeys U).StateInv ca checkpoint.state := by
    refine ⟨installed, trivial, ?_⟩
    exact ⟨[], initial, initialKeys, WriterReplay.nil, fun _ hk => Or.inl hk, invariant⟩
  have finish := trace.stateInv_admitted_sem
    (c3crvCarriedSpec_preservesAdmitted ca initial initialKeys U topology.inj topology.apart)
    admitted start
  obtain ⟨frames, s, K, replay, included, final⟩ := finish.inv
  exact ⟨finish.code, frames, s, K, replay, included, final, final.conserved⟩

end Blanc.Lift.Curve3Crv
