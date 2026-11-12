import Blanc.ExecutionKeptChain
import Blanc.ExecutionHistoryInCreateAvoid
import Blanc.ExecutionFrames

/-! Nonempty installed code excludes CREATE frames in an actual kept root.
This only transports the existing all-outcome execution theorem to kept frames. -/

namespace Blanc

open Jaune

/-- Derive the singleton-root creation exclusion from its actual entry state
and original execution, without assuming the kept-frame property. -/
theorem Root.noCreateAt_of_code (r : Root) (a : Adr)
    (hsg : r.evm.sta.benvStat.rules.stateGas = none)
    (present : (r.evm.dyna.getCode a).toList ≠ [])
    (self : r.evm.sta.codeAddress = none → r.evm.sta.currentTarget ≠ a) :
    NoCreateAt a [r] := by
  intro f member
  have member : f ∈ r.frames := by
    simpa only [keptAll, List.flatMap_cons, List.flatMap_nil, List.append_nil] using member
  unfold Root.frames at member
  split at member
  · exact ExecutionTrace.Exec.createAvoid_noStateGas r.run hsg present self (Blanc.Exec.Frame.rootDeriv f)
      (Exec.mem_rawFrameRoots_of_mem_committedFrames r.run f member)
  · exact (List.not_mem_nil member).elim

/-- A call at another target starts each actual root on the installed code.
Apply the existing execution exclusion root by root; no traversal is repeated. -/
theorem MessageRoots.noCreateAt_of_code {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (h : MessageRoots msg state out rs) (hsg : msg.benv.stat.rules.stateGas = none)
    (a : Adr) (present : (msg.benv.state.getCode a).toList ≠ [])
    (nondelegating : ¬ isValidDelegation (msg.benv.state.getCode a))
    (self : msg.currentTarget ≠ a) : NoCreateAt a rs := by
  intro f member
  obtain ⟨r, hr, hf⟩ := List.mem_flatMap.mp member
  have entry := h.entry_routing hr
  have kept := h.entry_kept hr present nondelegating
  have avoid := r.noCreateAt_of_code a
    (by rw [entry.2.2.1]; exact hsg)
    (by rw [kept.1]; exact present)
    (by intro _; rw [entry.2.1]; exact self)
  exact avoid f (List.mem_flatMap.mpr ⟨r, List.mem_cons_self, hf⟩)

theorem PreRoots.noCreateAt_of_code {benv : Benv} {st : State} {bal : BalBuilder} {rs : List Root}
    (h : PreRoots benv st bal rs) (hsg : benv.stat.rules.stateGas = none) (a : Adr)
    (present : (benv.state.getCode a).toList ≠ []) (nondelegating : ¬ isValidDelegation (benv.state.getCode a))
    (notBeacon : beaconRootsAddress ≠ a) (notHistory : historyStorageAddress ≠ a) : NoCreateAt a rs := by
  obtain ⟨beacon, beaconBal, br, hr, _, cb, _, ch, rfl⟩ := h
  have codeH := (cb.chain present nondelegating).2
  have avoidB : NoCreateAt a br := by
    unfold PreCall at cb
    split at cb
    · obtain ⟨out, roots⟩ := cb
      exact roots.noCreateAt_of_code hsg a present nondelegating notBeacon
    · rw [cb.2]
      intro f member
      cases member
  have avoidH : NoCreateAt a hr := by
    unfold PreCall at ch
    split at ch
    · obtain ⟨out, roots⟩ := ch
      exact roots.noCreateAt_of_code hsg a
        (by change (beacon.getCode a).toList ≠ []; rw [codeH]; exact present)
        (by change ¬ isValidDelegation (beacon.getCode a); rw [codeH]; exact nondelegating)
        notHistory
    · rw [ch.2]
      intro f member
      cases member
  intro f member
  rw [keptAll, List.flatMap_append, List.mem_append] at member
  rcases member with member | member
  · exact avoidB f member
  · exact avoidH f member
theorem RequestRoots.prague_noCreateAt_of_code
    {idx : Nat} {benv : Benv} {acc acc' : List Bytes} {bal bal' : BalBuilder} {final : State}
    {steps : List RequestStep}
    (h : RequestRoots idx pragueRequests benv acc bal final acc' bal' steps)
    (hsg : benv.stat.rules.stateGas = none) (a : Adr)
    (present : (benv.state.getCode a).toList ≠ []) (nondelegating : ¬ isValidDelegation (benv.state.getCode a))
    (notW : withdrawalRequestPredeployAddress ≠ a) (notC : consolidationRequestPredeployAddress ≠ a) :
    NoCreateAt a (requestRootsOf steps) := by
  cases h with
  | @cons typeW targetW restW benvW accW accW' balW balW' postW finalW outW rsW stepsW wRun wRoots later =>
    cases later with
    | cons cRun cRoots later =>
      cases later
      have avoidW := wRoots.noCreateAt_of_code hsg a present nondelegating notW
      have codeW := (wRoots.chain present nondelegating).2
      change postW.getCode a = benv.state.getCode a at codeW
      have avoidC := cRoots.noCreateAt_of_code hsg a
        (by change (postW.getCode a).toList ≠ []; rw [codeW]; exact present)
        (by change ¬ isValidDelegation (postW.getCode a); rw [codeW]; exact nondelegating)
        notC
      intro f member
      simp only [requestRootsOf, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        keptAll, List.flatMap_append, List.mem_append] at member
      rcases member with member | member
      · exact avoidW f member
      · exact avoidC f member

end Blanc
