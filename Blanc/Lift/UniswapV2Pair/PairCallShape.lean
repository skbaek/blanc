import Blanc.Lift.CallerProvenance
import Blanc.Lift.CallSiteChildren
import Blanc.Lift.ExactWalk
import Blanc.Lift.UniswapV2Pair.PairCallSites

/-!
# What the Pair runtime calls

The Pair issues non-static CALLs only from `_safeTransfer` (selector `transfer`, `0xa9059cbb`; reached
from `skim`, `swap` and `burn`) and from `swap`'s flash callback (selector `uniswapV2Call`,
`0x10d1e85c`).  Every other child it spawns is a STATICCALL (`balanceOf`, `feeTo`, ECRECOVER), hence
static.  `CallsTransferOrCallback run` states this for the direct committed children of one run.

`pair_callsTransferOrCallback` proves it for every successful Pair frame, whatever its selector, by
the certificate call-site argument: every direct child is spawned at a node of the frame's chain
(`Exec.childFrames_spawnedAt`); that node decodes CALL or STATICCALL (`CursorOK.exec_call_or_staticcall`);
a STATICCALL child is static; a CALL node sits at one of the three CALL sites (`pair_call_site`), whose
input selector the site facts `TransferSiteShape` and `CallbackSiteShape` give; and the child reads
exactly that selector (`Xinst.step_call_spawn_selector`).
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- Every non-static direct committed child of the run carries the `transfer` or the `uniswapV2Call`
selector. -/
def CallsTransferOrCallback {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : Prop :=
  ∀ c ∈ Exec.childFrames run, c.sevm.isStatic = false →
    Blanc.Sevm.selector c.sevm = 0xa9059cbb ∨ Blanc.Sevm.selector c.sevm = 0x10d1e85c

/-- **Pair call shape.**  Every successful frame of the Pair code, entered at pc `0` with an empty
stack and empty memory, whose chain keeps memory below `2 ^ 160`, calls non-statically only with the `transfer` or
the `uniswapV2Call` selector.
LANE-OPEN: conditional on TransferSiteShape, CallbackSiteShape. -/
theorem pair_callsTransferOrCallback (transfer : TransferSiteShape) (callback : CallbackSiteShape)
    {sevm : Sevm} {b post : Devm} {G : Nat} (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (bound : ChainMemoryBelow ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ (2 ^ 160)) :
    CallsTransferOrCallback run := by
  intro c member nonStatic
  obtain ⟨N, f, rsm, pc', cevm, chain, step, enter, childEq⟩ :=
    Exec.childFrames_spawnedAt run (.refl _) c member
  obtain ⟨x, hat, hx, -⟩ := Evm.step_spawn_inv step
  have sevmEq : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  have nodeFork : CoveredFork N.sevm.benvStat.fork := by rw [sevmEq]; exact fork
  obtain ⟨κ₀, -, ok₀⟩ := reach_of_parentPrefix cert_check rfl codeEq fork chain
  rcases ok₀.exec_call_or_staticcall hat with rfl | rfl
  · obtain ⟨κ, g, reach, ok, tree, site⟩ := pair_call_site rfl codeEq fork chain hat
    have stackNil : (St b [] Mem.empty G).stack = [] := rfl
    have memEmpty : (St b [] Mem.empty G).memory = Mem.empty := rfl
    have read : ∀ {sel : B256}, CallInputSelector N sel → Blanc.Sevm.selector c.sevm = sel := by
      intro sel ⟨g', c', v', ii, is, rest, hstack, hsel⟩
      rw [childEq, Xinst.step_call_spawn_selector nodeFork hx enter hstack, hsel]
    rcases site with here | here | here
    · exact Or.inr (read (callback rfl codeEq fork stackNil memEmpty bound rfl chain reach ok
        tree here))
    · exact Or.inl (read (transfer rfl codeEq fork stackNil memEmpty bound rfl chain reach ok
        tree (Or.inl here)))
    · exact Or.inl (read (transfer rfl codeEq fork stackNil memEmpty bound rfl chain reach ok
        tree (Or.inr here)))
  · have static : cevm.sta.isStatic = true :=
      (Frame.enter_run_isStatic enter).trans (Xinst.step_staticcall_spawn_isStatic hx)
    rw [childEq, static] at nonStatic
    cases nonStatic

end Blanc.Lift.UniswapV2Pair
