import Blanc.Composition.UniswapV2PairUsdcWeth9LegsSync
import Blanc.Composition.UniswapV2PairWeth9MintLive

/-!
# mint's USDC `balanceOf` query (U9c)

mint's first query with USDC as `token0` (`mintUsdcRead0`, its gas-free skeleton and spec, from
`usdcReadLeg128_spec`), and the bridge WETH9's second query needs to read USDC's result through
its skeleton (`mintWethRead1_withGasLeft`).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

/-- **mint's WETH9 second query reads its first query's result up to gas.** -/
theorem mintWethRead1_withGasLeft (sevm : Sevm) (d : Devm) (R : List B256) (M : Mem)
    (r1 r0 toWord ρ : B256) (factoryGas x : Nat) :
    mintWethRead1 sevm (d.withGasLeft x) R M r1 r0 toWord ρ factoryGas =
      mintWethRead1 sevm d R M r1 r0 toWord ρ factoryGas := by
  unfold mintWethRead1 Devm.withGasLeft
  rw [afterSload_setMach, wethReadLeg_setMach sevm (afterSload sevm d 7) _ _ _ _ _
    { d.mach with gasLeft := x } (afterSload_stateGas (sevm := sevm) (base := d) (key := 7)).symm]
  rfl

end Blanc.Composition.UniswapV2PairWeth9Joint

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcLive

/-- **mint's first `balanceOf(pair)` query with USDC as `token0`**, at the reserve-cached world
`b`: its result and the call gas USDC's code determines, given the second query's call gas.  Reuses
U9a's `usdcReadLeg` over the predecessor's staging (`mintTail0`, `mintToken0`, `mintRead0Need`). -/
noncomputable def mintUsdcRead0 (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (r1 r0 toWord ρ : B256) (callGas1 : Nat) : Devm × Nat :=
  usdcReadLeg sevm (afterSload sevm b 6) (mintTail0 R r1 r0 toWord ρ) M 128 (mintToken0 sevm b)
    (mintRead0Need sevm callGas1)

/-- The gas-free skeleton of mint's USDC query result (what WETH9's second query reads). -/
noncomputable def mintUsdcRead0Skel (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (r1 r0 toWord ρ : B256) : Devm :=
  usdcBalanceSkel sevm (afterSload sevm b 6) (mintTail0 R r1 r0 toWord ρ) M 128 (mintToken0 sevm b)

/-- **mint's USDC first-query leg (USDC = token0), frame level.**  USDC installed at the token mint
loads from slot 6, not a precompile, two levels of call depth, the Pair not the admin word, stack
room, a well-formed memory, the call gas a word, room for USDC's view under the 63/64 rule:
`mintUsdcRead0` is `MintTokenHalf0` at the pinned values, the reply is the Pair's USDC balance bits,
and the result is the skeleton up to gas. -/
theorem mintUsdcRead0_spec {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {r1 r0 toWord ρ : B256} {callGas1 : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (depth : 2 ≤ sevm.depth)
    (inst : Usdc.UsdcInstalled (b.getStorVal sevm.currentTarget 6).toAdr (afterSload sevm b 6).state)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (b.getStorVal sevm.currentTarget 6).toAdr = false)
    (notAdmin : sevm.currentTarget ≠ Usdc.adminOf (afterSload sevm b 6).state
      (b.getStorVal sevm.currentTarget 6).toAdr)
    (stackRoom : R.length < 1011) (wf : Mem.Wf M)
    (fits : (mintUsdcRead0 sevm b R M r1 r0 toWord ρ callGas1).2 < 2 ^ 256)
    (room : usdcBalNeed sevm (afterSload sevm b 6) (mintTail0 R r1 r0 toWord ρ) M 128
        (mintToken0 sevm b) ≤
      except64th (mintRead0Need sevm callGas1 (mintUsdcRead0Skel sevm b R M r1 r0 toWord ρ) +
        usdcBalUsed sevm (afterSload sevm b 6) (mintTail0 R r1 r0 toWord ρ) M 128
          (mintToken0 sevm b))) :
    MintTokenHalf0 sevm b (mintUsdcRead0 sevm b R M r1 r0 toWord ρ callGas1).1 R M
        (mintUsdcRead0 sevm b R M r1 r0 toWord ρ callGas1).2 callGas1 r1 r0 toWord ρ ∧
      (mintUsdcRead0 sevm b R M r1 r0 toWord ρ callGas1).1.returnData =
        (Nat.toB256 (Usdc.balanceBits (((afterSload sevm b 6).state.getStor
          (b.getStorVal sevm.currentTarget 6).toAdr).get (Usdc.balSlot sevm.currentTarget)))).toBytes ∧
      (mintUsdcRead0 sevm b R M r1 r0 toWord ρ callGas1).1 =
        (mintUsdcRead0Skel sevm b R M r1 r0 toWord ρ).withGasLeft
          (mintUsdcRead0 sevm b R M r1 r0 toWord ρ callGas1).1.gasLeft := by
  have h := usdcReadLeg128_spec (sevm := sevm) (B := afterSload sevm b 6)
    (S := mintTail0 R r1 r0 toWord ρ) (M := M) (t := mintToken0 sevm b)
    (need := mintRead0Need sevm callGas1) (swapTokenWord_adr _) (mintRead0Need_gasFree sevm callGas1)
    fork (by rw [mintToken0, toAdr_toB256]; exact inst) depth
    (by rw [mintToken0, toAdr_toB256]; exact notPrecompile)
    (by rw [mintToken0, toAdr_toB256]; exact notAdmin)
    (by simp only [mintTail0, List.length_cons]; omega) wf fits room
  rw [mintToken0, toAdr_toB256] at h
  obtain ⟨code0, call0, success0, gas0, long0, ret, skel⟩ := h
  exact ⟨⟨code0, call0, success0, long0, gas0⟩, ret, skel⟩

end Blanc.Composition.UniswapV2PairUsdcWeth9
