import Blanc.Composition.UniswapV2PairUsdcWeth9CheckpointF
import Blanc.Composition.UniswapV2PairUsdcWeth9CheckJoint
import Blanc.Lift.Usdc.FiniteFootprintF

/-!
# A computable support-free checker for the two-token joint checkpoint (F3)

`checkJoint2F pair usdc weth urows wrows prows base w` is `checkJoint2`
(`UniswapV2PairUsdcWeth9CheckJoint.lean`) with `checkUsdc` replaced by the support-free
`checkUsdcF`: the WETH9 side (`checkJoint … .one`), `token0 = usdc`, the Pair's USDC rows
(`checkUsdcHolder`, reused verbatim), `pair ≠ usdc`, and the no-precompile fact stay exactly as
they were.  `checkJoint2F_sound` is the soundness theorem, targeting `JointCheckpoint2F`.
`checkUsdcHolder_soundW` (`UniswapV2PairUsdcWeth9CheckJoint.lean`) is the holder-rows fact
under the weakened word-only premise: without support there is no `RowsSound`, but the proof of
`checkUsdcHolder_sound` reads only its `word` field, so the same walk closes over
`checkUsdcF_word`.

**Controls.** `u0F_accepts`: the checker accepts `U0` in the kernel.  The key control: `U0` with
one extra nonzero USDC word at the unlisted slot `0xdead` is still accepted by `checkJoint2F`
(`u0F_stray_accepted`) while `checkJoint2` rejects it (`u0_stray_rejected`) — support is no longer
needed.  The existing allowance and frozen mutants are rejected by `checkJoint2F` too
(`u0F_allowance_rejected`, `u0F_frozen_rejected`), in the kernel.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Lift.Weth9
  Blanc.Composition.UniswapV2PairWeth9Joint Blanc.Lift.FiniteCheckpoint

/-- **The support-free two-token joint checkpoint checker**: `checkJoint2` with `checkUsdcF` in
place of `checkUsdc`. -/
def checkJoint2F (pair usdc weth : Adr) (urows : List (Usdc.Key × B256))
    (wrows : List (Weth9.Key × B256)) (prows : List PairRow) (base : UniswapV2Pair.State)
    (w : Jaune.State) : Bool :=
  checkJoint pair weth wrows prows base .one w && Usdc.checkUsdcF usdc urows w &&
    decide (base.token0 = usdc) &&
    checkUsdcHolder urows (w.getStor usdc) pair base.reserve0.val && decide (pair ≠ usdc) &&
    decide (∀ f ∈ coveredForks, ¬ (Fork.ruleSet f).isPrecomp usdc)

/-- **Soundness of the support-free two-token joint checkpoint checker.** -/
theorem checkJoint2F_sound {pair usdc weth : Adr} {urows : List (Usdc.Key × B256)}
    {wrows : List (Weth9.Key × B256)} {prows : List PairRow} {base : UniswapV2Pair.State}
    {w : Jaune.State} (h : checkJoint2F pair usdc weth urows wrows prows base w = true) :
    JointCheckpoint2F pair usdc weth (rowKeys urows) (rowKeys wrows) (pairKeys prows)
      (rowsState base prows) w := by
  simp only [checkJoint2F, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hjoint, husdc⟩, htoken0⟩, hholder⟩, hapart⟩, hprecomp⟩ := h
  obtain ⟨installed, foot⟩ := Usdc.checkUsdcF_sound husdc
  obtain ⟨tracked, notFrozen, reserve, noAllowance⟩ :=
    checkUsdcHolder_soundW (Usdc.checkUsdcF_word husdc) hholder
  exact
    { weth9 := checkJoint_sound hjoint
      usdcInstalled := installed
      usdcFoot := foot
      token0 := htoken0
      tracked := tracked
      notFrozen := notFrozen
      noAllowance := noAllowance
      reserve := reserve
      apart := hapart
      usdcNotPrecompile := fun s hfork => hprecomp s.fork hfork }

/-! ## Controls -/

/-- **The support-free checker accepts `U0`** (kernel evaluation). -/
theorem u0F_accepts :
    checkJoint2F u0Pair Usdc.usdcProxy u0Weth u0UsdcRows u0WethRows u0PairRows u0Base
      (u0World u0UsdcStor) = true := by
  decide +kernel

/-- **Key control ("support no longer needed")**: `U0` with one extra nonzero USDC word at the
unlisted slot `0xdead` is still accepted by the support-free checker (kernel evaluation). -/
theorem u0F_stray_accepted :
    checkJoint2F u0Pair Usdc.usdcProxy u0Weth u0UsdcRows u0WethRows u0PairRows u0Base
      (u0World (u0UsdcStor.set 0xdead 1)) = true := by
  decide +kernel

/-- **Key control, second half**: the support-checking `checkJoint2` rejects that world
(kernel evaluation). -/
theorem u0_stray_rejected :
    checkJoint2 u0Pair Usdc.usdcProxy u0Weth u0UsdcRows u0WethRows u0PairRows u0Base
      (u0World (u0UsdcStor.set 0xdead 1)) = false := by
  decide +kernel

/-- **Allowance control (concrete)**: `U0` with the Pair's tracked USDC allowance to the spender
set to `7` is rejected by the support-free checker too (kernel evaluation). -/
theorem u0F_allowance_rejected :
    checkJoint2F u0Pair Usdc.usdcProxy u0Weth u0UsdcRows u0WethRows u0PairRows u0Base
      (u0World (u0UsdcStor.set (Usdc.allowSlot u0Pair u0Spender) 7)) = false := by
  decide +kernel

/-- **Frozen control (concrete)**: `U0` with the Pair's USDC balance word flagged (bit 255 set, the
balance bits unchanged) is rejected by the support-free checker too (kernel evaluation). -/
theorem u0F_frozen_rejected :
    checkJoint2F u0Pair Usdc.usdcProxy u0Weth u0UsdcRows u0WethRows u0PairRows u0Base
      (u0World (u0UsdcStor.set (Usdc.balSlot u0Pair) (Nat.toB256 (2 ^ 255 + 1000000)))) = false := by
  decide +kernel

end Blanc.Composition.UniswapV2PairUsdcWeth9
