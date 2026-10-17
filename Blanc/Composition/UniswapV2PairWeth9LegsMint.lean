import Blanc.Composition.UniswapV2PairWeth9LegsSync
import Blanc.Lift.UniswapV2Pair.MintForwardAccept

/-!
# The mint row's WETH9 `balanceOf` legs (C4(b), U8b1)

`pair_history_mint_live` takes `MintPrefixCallee`, whose `tokens` field (`MintBalanceForward`)
holds the two token `balanceOf(pair)` `STATICCALL`s.  For the WETH9 side, either `token0`
(`mintWethRead0`, fields `code0`/`call0`/`success0`/`long0`/`gas0`) or `token1` (`mintWethRead1`,
fields `code1`/`call1`/`success1`/`long1`/`gas1`), the query is the generic read leg at pointer
`128` and its spec gives those fields verbatim.  Code-only.  The factory `feeTo` call stays a
premise of the row.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

/-! ## mint, WETH9 = token0: the first query -/

section Mint0

variable (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem) (r1 r0 toWord ρ : B256) (callGas1 : Nat)

/-- The words under mint's first query's operands. -/
def mintTail0 : List B256 := 0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R

/-- The token mint's first query calls (slot 6, as the Pair loads it). -/
def mintToken0 : B256 := (b.getStorVal sevm.currentTarget 6).toAdr.toB256

/-- What mint needs left after its first query: the slot-7 read, the second request's staging and
the second query's call gas (`MintBalanceForward.gas0`). -/
def mintRead0Need (d0 : Devm) : Nat :=
  callGas1 + 5 + sloadCost sevm d0 7 +
    temporalAccountAccessCost (afterSload sevm d0 7) (d0.getStorVal sevm.currentTarget 7).toAdr + 219

end Mint0

/-- **mint's first `balanceOf(pair)` query when WETH9 is `token0`**, at the reserve-cached world
`b`: its result and the call gas WETH9's code determines, given the second query's call gas. -/
noncomputable def mintWethRead0 (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (r1 r0 toWord ρ : B256) (callGas1 : Nat) : Devm × Nat :=
  wethReadLeg sevm (afterSload sevm b 6) (mintTail0 R r1 r0 toWord ρ) M 128 (mintToken0 sevm b)
    (mintRead0Need sevm callGas1)

theorem mintRead0Need_gasFree (sevm : Sevm) (callGas1 : Nat) (d : Devm) (x : Nat) :
    mintRead0Need sevm callGas1 (d.withGasLeft x) = mintRead0Need sevm callGas1 d := by
  unfold mintRead0Need Devm.withGasLeft
  rw [afterSload_setMach]
  rfl

/-- **mint's WETH9 first-query leg (WETH9 = token0), frame level.**  WETH9's code at the token mint
loads from slot 6, not a precompile, call depth left, stack room, a well-formed memory, the call
gas a word, and room for WETH9's view: `mintWethRead0` meets `MintBalanceForward`'s `code0`,
`call0`, `success0`, `long0` and `gas0`, and replies with the pair's WETH9 balance. -/
theorem mintWethRead0_spec {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {r1 r0 toWord ρ : B256} {callGas1 : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (depth : sevm.depth ≠ 0)
    (wethCode : (afterSload sevm b 6).state.getCode (b.getStorVal sevm.currentTarget 6).toAdr =
      Weth9.code)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (b.getStorVal sevm.currentTarget 6).toAdr = false)
    (stackRoom : R.length < 1011) (wf : Mem.Wf M)
    (fits : (mintWethRead0 sevm b R M r1 r0 toWord ρ callGas1).2 < 2 ^ 256)
    (room : balUsed sevm (afterSload sevm b 6) (mintTail0 R r1 r0 toWord ρ) M 128 (mintToken0 sevm b) ≤
      except64th (mintRead0Need sevm callGas1 (wethBalanceSkel sevm (afterSload sevm b 6)
          (mintTail0 R r1 r0 toWord ρ) M 128 (mintToken0 sevm b)) +
        balUsed sevm (afterSload sevm b 6) (mintTail0 R r1 r0 toWord ρ) M 128 (mintToken0 sevm b))) :
    let d0 := (mintWethRead0 sevm b R M r1 r0 toWord ρ callGas1).1
    let callGas0 := (mintWethRead0 sevm b R M r1 r0 toWord ρ callGas1).2
    ((afterSload sevm b 6).getCode (b.getStorVal sevm.currentTarget 6).toAdr).size.toB256 ≠ 0 ∧
    Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (afterSload sevm b 6) (b.getStorVal sevm.currentTarget 6).toAdr)
        (callGas0.toB256 :: (b.getStorVal sevm.currentTarget 6).toAdr.toB256 ::
          128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          (b.getStorVal sevm.currentTarget 6).toAdr.toB256 :: 0 :: r1 :: r0 ::
          0 :: toWord :: ρ :: R) (balanceRequestMemory M sevm.currentTarget) callGas0)
      (.exec .staticcall) d0 ∧
    d0.stack = 1 :: 164 :: 0x70a08231 ::
      (b.getStorVal sevm.currentTarget 6).toAdr.toB256 :: 0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R ∧
    d0.gasLeft = callGas1 + 5 + sloadCost sevm d0 7 +
      temporalAccountAccessCost (afterSload sevm d0 7) (d0.getStorVal sevm.currentTarget 7).toAdr + 219 ∧
    32 ≤ d0.returnData.length ∧
    d0.returnData = ((afterSload sevm b 6).getStorVal (b.getStorVal sevm.currentTarget 6).toAdr
      (Weth9.balSlot sevm.currentTarget)).toBytes := by
  have h := wethReadLeg128_spec (sevm := sevm) (B := afterSload sevm b 6)
    (S := mintTail0 R r1 r0 toWord ρ) (M := M) (t := mintToken0 sevm b)
    (need := mintRead0Need sevm callGas1) (swapTokenWord_adr _) (mintRead0Need_gasFree sevm callGas1)
    fork (by rw [mintToken0, toAdr_toB256]; exact wethCode) depth
    (by rw [mintToken0, toAdr_toB256]; exact notPrecompile)
    (by simp only [mintTail0, List.length_cons]; omega) wf fits room
  rw [mintToken0, toAdr_toB256] at h
  exact h

/-! ## mint, WETH9 = token1: the second query -/

section Mint1

variable (sevm : Sevm) (d0 : Devm) (R : List B256) (M : Mem) (r1 r0 toWord ρ : B256)
  (factoryGas : Nat)

/-- The words under mint's second query's operands (the first reply word among them). -/
def mintTail1 : List B256 :=
  0 :: Bytes.toB256 (d0.returnData.take 32) :: r1 :: r0 :: 0 :: toWord :: ρ :: R

/-- What mint needs left after its second query: the factory read, its access and the `feeTo`
call gas (`MintPrefixCallee.tokens`'s `G + 70`). -/
def mintRead1Need (d1 : Devm) : Nat :=
  factoryGas + sloadCost sevm d1 5 +
    temporalAccountAccessCost (feeFactoryLoadWorld sevm d1) (feeFactoryWord sevm d1).toAdr + 360 + 70

end Mint1

/-- **mint's second `balanceOf(pair)` query when WETH9 is `token1`**, staged over the first query's
result `d0`: its result and the call gas WETH9's code determines, given the factory call's gas. -/
noncomputable def mintWethRead1 (sevm : Sevm) (d0 : Devm) (R : List B256) (M : Mem)
    (r1 r0 toWord ρ : B256) (factoryGas : Nat) : Devm × Nat :=
  wethReadLeg sevm (afterSload sevm d0 7) (mintTail1 d0 R r1 r0 toWord ρ)
    (balanceReplyMemory M sevm.currentTarget d0.returnData) 128 (syncToken1 sevm d0)
    (mintRead1Need sevm factoryGas)

theorem mintRead1Need_gasFree (sevm : Sevm) (factoryGas : Nat) (d : Devm) (x : Nat) :
    mintRead1Need sevm factoryGas (d.withGasLeft x) = mintRead1Need sevm factoryGas d := by
  unfold mintRead1Need feeFactoryLoadWorld feeFactoryWord Devm.withGasLeft
  rw [afterSload_setMach]
  rfl

/-- **mint's WETH9 second-query leg (WETH9 = token1), frame level.**  Over the first query's result
`d0`: WETH9's code at the token mint loads from slot 7, not a precompile, call depth left, stack
room, a well-formed memory, the call gas a word, and room for WETH9's view: `mintWethRead1` meets
`MintBalanceForward`'s `code1`, `call1`, `success1`, `long1` and `gas1` at the tail gas
`MintPrefixCallee.tokens` fixes, and replies with the pair's WETH9 balance. -/
theorem mintWethRead1_spec {sevm : Sevm} {d0 : Devm} {R : List B256} {M : Mem}
    {r1 r0 toWord ρ : B256} {factoryGas : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (depth : sevm.depth ≠ 0)
    (wethCode : (afterSload sevm d0 7).state.getCode (d0.getStorVal sevm.currentTarget 7).toAdr =
      Weth9.code)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (d0.getStorVal sevm.currentTarget 7).toAdr = false)
    (stackRoom : R.length < 1010) (wf : Mem.Wf M)
    (fits : (mintWethRead1 sevm d0 R M r1 r0 toWord ρ factoryGas).2 < 2 ^ 256)
    (room : balUsed sevm (afterSload sevm d0 7) (mintTail1 d0 R r1 r0 toWord ρ)
        (balanceReplyMemory M sevm.currentTarget d0.returnData) 128 (syncToken1 sevm d0) ≤
      except64th (mintRead1Need sevm factoryGas (wethBalanceSkel sevm (afterSload sevm d0 7)
          (mintTail1 d0 R r1 r0 toWord ρ) (balanceReplyMemory M sevm.currentTarget d0.returnData) 128
          (syncToken1 sevm d0)) +
        balUsed sevm (afterSload sevm d0 7) (mintTail1 d0 R r1 r0 toWord ρ)
          (balanceReplyMemory M sevm.currentTarget d0.returnData) 128 (syncToken1 sevm d0))) :
    let d1 := (mintWethRead1 sevm d0 R M r1 r0 toWord ρ factoryGas).1
    let callGas1 := (mintWethRead1 sevm d0 R M r1 r0 toWord ρ factoryGas).2
    ((afterSload sevm d0 7).getCode (d0.getStorVal sevm.currentTarget 7).toAdr).size.toB256 ≠ 0 ∧
    Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (afterSload sevm d0 7) (d0.getStorVal sevm.currentTarget 7).toAdr)
        (callGas1.toB256 :: (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 :: 0 ::
          Bytes.toB256 (d0.returnData.take 32) :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
        (balanceRequestMemory (balanceReplyMemory M sevm.currentTarget d0.returnData)
          sevm.currentTarget) callGas1) (.exec .staticcall) d1 ∧
    d1.stack = 1 :: 164 :: 0x70a08231 ::
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 :: 0 ::
      Bytes.toB256 (d0.returnData.take 32) :: r1 :: r0 :: 0 :: toWord :: ρ :: R ∧
    d1.gasLeft = (factoryGas + sloadCost sevm d1 5 +
      temporalAccountAccessCost (feeFactoryLoadWorld sevm d1) (feeFactoryWord sevm d1).toAdr + 360) + 70 ∧
    32 ≤ d1.returnData.length ∧
    d1.returnData = ((afterSload sevm d0 7).getStorVal (d0.getStorVal sevm.currentTarget 7).toAdr
      (Weth9.balSlot sevm.currentTarget)).toBytes := by
  have h := wethReadLeg128_spec (sevm := sevm) (B := afterSload sevm d0 7)
    (S := mintTail1 d0 R r1 r0 toWord ρ) (M := balanceReplyMemory M sevm.currentTarget d0.returnData)
    (t := syncToken1 sevm d0) (need := mintRead1Need sevm factoryGas) (swapTokenWord_adr _)
    (mintRead1Need_gasFree sevm factoryGas) fork (by rw [syncToken1, toAdr_toB256]; exact wethCode)
    depth (by rw [syncToken1, toAdr_toB256]; exact notPrecompile)
    (by simp only [mintTail1, List.length_cons]; omega)
    (by rw [← swapBalanceReply_128]; exact swapBalanceReply_wf wf) fits room
  rw [syncToken1, toAdr_toB256] at h
  exact h

end Blanc.Composition.UniswapV2PairWeth9Joint
