import Blanc.Lift.SettledFramePositions
import Blanc.ExecutionAccountingHistoryIn
import Blanc.ExecutionHistoricalAdmission
import Blanc.ExecutionHistory
import Blanc.ExecutionStagedAdmission

/-!
# Positional parents over In-histories

The positional-parent ladder (`Blanc/Lift/SettledFramePositions.lean`) is
already fork-free at its root: `parentLadder`'s root never uses its fork
premise. This module is its additive historical counterpart:
`parentLadderIn` is the same construction over
`AccountingLadderAdmittedIn F`, reusing the positional carrier, observation
and append, and `ConfiguredHistoryTraceIn.settledFrames_parent_of_codeAddress`
runs it through `configuredHistoryIn`, with admission from
`ConfiguredHistoryTraceIn.frameAdmitted_iff_rawFrames`.

The cost is premises the positional fact does not need intrinsically: the
invariant is consumed through `MessageRunReady` in the root, and the history
runner needs the `InstalledCert` NoDel arguments `K`/`image`, the stage
capabilities, and the Mac-owned reward funding. The Mac owns the call (its
W2); this module ships the send-side artifacts.
-/

namespace Blanc

open Jaune
open ExecutionAccountingReplay

/-- **The positional-parent ladder, over `F`**: a message root at `ca` runs at
code address `ca`, and every descendant has its positional parent in the
root's committed frames. The root proof is the body of `parentLadder`'s root,
which never uses the fork premise. -/
noncomputable def parentLadderIn {c : ContractSpecSem} (ca : Adr)
    (F : Fork → Prop)
    (preserves : c.PreservesAdmittedIn F ca (fun _ _ => True)) :
    AccountingLadderAdmittedIn F c ca (fun _ _ => True) where
  carrier := parentCarrier ca
  append := fun l r => PositionalParents.append l r
  tag _ _ := ()
  preserves := preserves
  view := parentObservation ca
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed admitted ready _ _ bound
    have sevmEq := congrArg Evm.sta evmEq
    dsimp only [initEvm] at sevmEq
    have rootCA : sevm.currentTarget = ca → sevm.codeAddress = some ca := by
      intro target
      rw [sevmEq] at target ⊢
      rcases ready.codeOrForeign with call | foreign
      · exact ready.ready.codeAddress call target
      · exact (foreign target).elim
    refine ⟨Exec.committedFrames run, ?_, by
      change Exec.committedFrames run = (Exec.committedFrames run).flatMap fun f => [f]
      rw [List.flatMap_singleton']⟩
    show PositionalParents ca (Exec.committedFrames run)
    rw [Exec.committedFrames, dite_eq_left committed]
    intro b f a split target ne
    cases b with
    | nil =>
        obtain ⟨rfl, -⟩ := List.cons.inj split
        exact (ne (rootCA target)).elim
    | cons g b =>
        obtain ⟨rfl, rest⟩ := List.cons.inj split
        rcases (Exec.descendantFrames_forest run rest).2 with ⟨child, -⟩ |
            ⟨b₁, G, b₂, hb, child, -, len⟩
        · refine ⟨[], _, b, rfl, child, ?_⟩
          show b.length < (Exec.descendantFrames run).length
          simp only [rest, List.append_eq, List.length_append, List.length_cons]
          omega
        · exact ⟨_ :: b₁, G, b₂, by rw [hb]; rfl, child, len⟩

namespace ExecutionTrace

namespace ConfiguredHistoryTraceIn

variable {F : Fork → Prop}
variable {C : ByteArray}

/-- **Positional parents of the settled frames, over `F`**: every settled
frame at `ca` whose code address is not `ca` was spawned by an earlier
settled frame whose block of descendants covers its position. -/
theorem settledFrames_parent_of_codeAddress {c : ContractSpecSem} {ca : Adr}
    (preserves : c.PreservesAdmittedIn F ca (fun _ _ => True)) {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (rewards : trace.RewardCreditsFunded)
    (inv : c.StateInv ca checkpoint.state)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    PositionalParents ca trace.settledFrames := by
  have admitted : trace.FrameAdmitted ca (fun _ _ => True) :=
    (trace.frameAdmitted_iff_rawFrames ca _).2 fun _ _ _ => trivial
  obtain ⟨steps, replay, observed⟩ :=
    (parentLadderIn ca F preserves).configuredHistoryIn trace admitted capabilities
      rewards inv K image
  change steps = trace.settledFrames.flatMap (fun f => [f]) at observed
  rw [List.flatMap_singleton'] at observed
  subst observed
  exact replay

end ConfiguredHistoryTraceIn

end ExecutionTrace

end Blanc
