import Blanc.Lift.Curve3Pool.Walk.DispatchQuiet

/-!
# The dispatcher hands `remove_liquidity_imbalance` its body, on the actual derivation

From the frame's start (pc `0`, empty stack and memory) with the
`remove_liquidity_imbalance` selector: the shared prefix through
`remove_liquidity`'s test (`dq_to_3040`, reusing the quiet walk) jumps to `0x3040`,
and the `0x9fdaea0c` test falls through into the arm's body at `0x304f` with the
prologue's exact memory and no remaining-children change.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **The dispatcher hands `remove_liquidity_imbalance` its body** (past the arm's own
test), with the prologue's exact memory and the frame's remaining children unchanged. -/
theorem xa_dispatch_removeLiquidityImbalance {sevm : Sevm} {post b : Devm}
    {L : List Exec.Frame} {G : Nat} (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityImbalance)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x304f (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  have hne1 : Sevm.selector sevm ≠ 0xf446c1d0 := by rw [hsel]; decide
  have hne2 : Sevm.selector sevm ≠ 0xbb7b8b80 := by rw [hsel]; decide
  have hne3 : Sevm.selector sevm ≠ 0x3883e119 := by rw [hsel]; decide
  have hne4 : Sevm.selector sevm ≠ 0x4515cef3 := by rw [hsel]; decide
  have hne5 : Sevm.selector sevm ≠ 0x5e0d443f := by rw [hsel]; decide
  have hne6 : Sevm.selector sevm ≠ 0x07211ef7 := by rw [hsel]; decide
  have hne7 : Sevm.selector sevm ≠ 0x3df02124 := by rw [hsel]; decide
  have hne8 : Sevm.selector sevm ≠ 0xecb586a5 := by rw [hsel]; decide
  obtain ⟨G', h⟩ := dq_to_3040 hcode hlen hcd h hne1 hne2 hne3 hne4 hne5 hne6 hne7 hne8
  xs 0x3046 (.push [0x9f, 0xda, 0xea, 0x0c] (by decide)) ri_push  -- 3041 PUSH4 0x9fdaea0c
  xs 0x3048 (.push [0x00] (by decide)) ri_push  -- 3046 PUSH1 0x00
  xs 0x3049 (.reg .mload) ri_mload_vy0  -- 3048 MLOAD
  xs 0x304a (.reg .eq) ri_eq  -- 3049 EQ
  xs 0x304b (.reg .iszero) ri_iszero  -- 304a ISZERO
  xs 0x304e (.push [0x39, 0x91] (by decide)) ri_push  -- 304b PUSH2 0x3991
  xji 0x304f 0x3991 hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

end Blanc.Lift.Curve3Pool
