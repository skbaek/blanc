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

end Blanc
