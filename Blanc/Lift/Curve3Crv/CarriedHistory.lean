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

end Blanc.Lift.Curve3Crv
