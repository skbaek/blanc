import Blanc.Composition.UniswapV2PairWeth9LegsSync
import Blanc.Lift.UniswapV2Pair.BurnForwardBody

/-!
# The burn row's WETH9 `balanceOf` legs (C4(b), U8b2)

`pair_history_burn_live` takes Burn's callees as `BurnForwardEnv`.  Its WETH9 reads are code-only:

* the two initial `balanceOf(pair)` queries (`BurnInitialCallee.call0`/`call1`), WETH9 as `token0`
  (`burnWethRead0`) or as `token1` (`burnWethRead1`), both at the fixed pointer `128`
  (`wethReadLeg128_spec`);
* the two final queries of the suffix (`BurnBackForwardEnv.first`/`second`, `SwapBalanceEnv`
  shaped), WETH9 as `token0` (`burnWethFinal0`) or `token1` (`burnWethFinal1`) (`wethReadLeg_spec`).

Each leg is the generic read leg at the need the record's next segment fixes; the need reads the
leg's result only off its gas-free columns.  No premise mentions WETH9's answer.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

/-! ## Masked token words -/

theorem burnAddrMask_and (x : B256) : (burnAddrMask &&& x) = x.toAdr.toB256 := by
  rw [B256.and_comm, show burnAddrMask = ~~~ addressMask from by decide, and_mask_word]

theorem and_burnAddrMask (x : B256) : (x &&& burnAddrMask) = x.toAdr.toB256 := by
  rw [show burnAddrMask = ~~~ addressMask from by decide, and_mask_word]

theorem swapTokenWord_burnT0 (sevm : Sevm) (b : Devm) :
    swapTokenWord (burnT0 sevm b) = burnT0 sevm b := by
  unfold burnT0
  rw [burnAddrMask_and, swapTokenWord_adr]

theorem swapTokenWord_burnT1 (sevm : Sevm) (b : Devm) :
    swapTokenWord (burnT1 sevm b &&& burnAddrMask) = burnT1 sevm b &&& burnAddrMask := by
  rw [and_burnAddrMask, swapTokenWord_adr]

/-! ## The initial reads -/

section Initial

variable (sevm : Sevm) (b : Devm) (R : List B256)

/-- The world the first initial query is staged over (before the callee is warmed). -/
def burnRead0World : Devm := burnTokensWorld sevm (burnReservedWorld sevm b)

/-- The words under the first initial query's request words. -/
def burnRead0Stack : List B256 := 0 :: burnT1 sevm b :: burnT0 sevm b :: burnInitLocals sevm b R

/-- What Burn needs left after its first initial query: the second request's staging and call gas
(`BurnInitialCallee.returnedGas0`). -/
def burnRead0Need (callGas1 : Nat) (d0 : Devm) : Nat := burnInitialGas1 sevm b d0 callGas1 + 64

/-- The words under the second initial query's request words. -/
def burnRead1Stack (d0 : Devm) : List B256 :=
  0 :: burnB0 d0 :: burnT1 sevm b :: burnT0 sevm b :: burnInitLocals sevm b R

end Initial

/-- **Burn's first initial `balanceOf(pair)` query when WETH9 is `token0`**: its result and the call
gas WETH9's code determines, given the second initial query's call gas `callGas1`. -/
noncomputable def burnWethRead0 (sevm : Sevm) (b : Devm) (R : List B256) (callGas1 : Nat) :
    Devm × Nat :=
  wethReadLeg sevm (burnRead0World sevm b) (burnRead0Stack sevm b R) getterInitMemory 128
    (burnT0 sevm b) (burnRead0Need sevm b callGas1)

/-- **Burn's second initial `balanceOf(pair)` query when WETH9 is `token1`**, over the first query's
result `d0`: its result and the call gas WETH9's code determines, given the fee caller's gas `T1`. -/
noncomputable def burnWethRead1 (sevm : Sevm) (b d0 : Devm) (R : List B256) (T1 : Nat) :
    Devm × Nat :=
  wethReadLeg sevm d0 (burnRead1Stack sevm b R d0) (burnMem1 sevm d0) 128
    (burnT1 sevm b &&& burnAddrMask) (fun _ => T1 + 64)

theorem burnRead0Need_gasFree (sevm : Sevm) (b : Devm) (callGas1 : Nat) (d : Devm) (x : Nat) :
    burnRead0Need sevm b callGas1 (d.withGasLeft x) = burnRead0Need sevm b callGas1 d := rfl

theorem burnMem1_wf (sevm : Sevm) (d0 : Devm) : Mem.Wf (burnMem1 sevm d0) :=
  (balanceReplyMemory_ptr d0.returnData
    (balanceRequestMemory_ptr getterInitMemory_ptr sevm.currentTarget)).wf

/-- **Burn's first initial WETH9 read (WETH9 = token0), frame level.**  WETH9's code at the cached
`token0` in the world after the lock, reserve and token loads, not a precompile, call depth left,
stack room, the call gas a word, and room for WETH9's view: `burnWethRead0` meets
`BurnInitialCallee`'s `code0`, `call0`, `success0`, `long0` and `returnedGas0`, and replies with the
pair's WETH9 balance there.  Code-only. -/
theorem burnWethRead0_spec {sevm : Sevm} {b : Devm} {R : List B256} {callGas1 : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (depth : sevm.depth ≠ 0)
    (wethCode : (burnRead0World sevm b).state.getCode (burnT0 sevm b).toAdr = Weth9.code)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (burnT0 sevm b).toAdr = false)
    (stackRoom : R.length < 1009)
    (fits : (burnWethRead0 sevm b R callGas1).2 < 2 ^ 256)
    (room : balUsed sevm (burnRead0World sevm b) (burnRead0Stack sevm b R) getterInitMemory 128
        (burnT0 sevm b) ≤
      except64th (burnRead0Need sevm b callGas1 (wethBalanceSkel sevm (burnRead0World sevm b)
          (burnRead0Stack sevm b R) getterInitMemory 128 (burnT0 sevm b)) +
        balUsed sevm (burnRead0World sevm b) (burnRead0Stack sevm b R) getterInitMemory 128
          (burnT0 sevm b))) :
    let d0 := (burnWethRead0 sevm b R callGas1).1
    let callGas0 := (burnWethRead0 sevm b R callGas1).2
    ((burnTokensWorld sevm (burnReservedWorld sevm b)).getCode
      (burnT0 sevm b).toAdr).size.toB256 ≠ 0 ∧
    Ninst.RunCompiled sevm
      (St (burnCall0World sevm b) (callGas0.toB256 :: burnT0 sevm b :: 128 :: 36 :: 128 :: 32 ::
        164 :: 0x70a08231 :: burnT0 sevm b :: 0 :: burnT1 sevm b :: burnT0 sevm b ::
        burnInitLocals sevm b R)
        (balanceRequestMemory getterInitMemory sevm.currentTarget) callGas0) (.exec .staticcall) d0 ∧
    d0.stack = 1 :: 164 :: 0x70a08231 :: burnT0 sevm b :: 0 :: burnT1 sevm b ::
      burnT0 sevm b :: burnInitLocals sevm b R ∧
    32 ≤ d0.returnData.length ∧
    d0.gasLeft = burnInitialGas1 sevm b d0 callGas1 + 64 ∧
    d0.returnData = ((burnRead0World sevm b).getStorVal (burnT0 sevm b).toAdr
      (Weth9.balSlot sevm.currentTarget)).toBytes := by
  obtain ⟨hcode, hrun, hstk, hgas, hlong, hret⟩ := wethReadLeg128_spec (sevm := sevm)
    (B := burnRead0World sevm b) (S := burnRead0Stack sevm b R) (M := getterInitMemory)
    (t := burnT0 sevm b) (need := burnRead0Need sevm b callGas1) (swapTokenWord_burnT0 sevm b)
    (burnRead0Need_gasFree sevm b callGas1) fork wethCode depth notPrecompile
    (by simp only [burnRead0Stack, burnInitLocals, List.length_cons]; omega)
    getterInitMemory_ptr.wf fits room
  exact ⟨hcode, hrun, hstk, hlong, hgas, hret⟩

/-- **Burn's second initial WETH9 read (WETH9 = token1), frame level.**  At the first query's result
world `d0`: WETH9's code at the masked `token1` there, not a precompile, call depth left, stack room,
the call gas a word, and room for WETH9's view: `burnWethRead1` meets `BurnInitialCallee`'s `code1`,
`call1`, `success1`, `long1` and `returnedGas1`, and replies with the pair's WETH9 balance at `d0`.
Code-only: nothing is assumed of the first query's callee. -/
theorem burnWethRead1_spec {sevm : Sevm} {b d0 : Devm} {R : List B256} {T1 : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (depth : sevm.depth ≠ 0)
    (wethCode : d0.state.getCode (burnT1 sevm b &&& burnAddrMask).toAdr = Weth9.code)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (burnT1 sevm b &&& burnAddrMask).toAdr = false)
    (stackRoom : R.length < 1008)
    (fits : (burnWethRead1 sevm b d0 R T1).2 < 2 ^ 256)
    (room : balUsed sevm d0 (burnRead1Stack sevm b R d0) (burnMem1 sevm d0) 128
        (burnT1 sevm b &&& burnAddrMask) ≤
      except64th (T1 + 64 + balUsed sevm d0 (burnRead1Stack sevm b R d0) (burnMem1 sevm d0) 128
        (burnT1 sevm b &&& burnAddrMask))) :
    let d1 := (burnWethRead1 sevm b d0 R T1).1
    let callGas1 := (burnWethRead1 sevm b d0 R T1).2
    (d0.getCode (burnT1 sevm b &&& burnAddrMask).toAdr).size.toB256 ≠ 0 ∧
    Ninst.RunCompiled sevm
      (St (burnCall1World sevm b d0) (callGas1.toB256 :: (burnT1 sevm b &&& burnAddrMask) ::
        128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 :: (burnT1 sevm b &&& burnAddrMask) :: 0 ::
        burnB0 d0 :: burnT1 sevm b :: burnT0 sevm b :: burnInitLocals sevm b R)
        (balanceRequestMemory (burnMem1 sevm d0) sevm.currentTarget) callGas1) (.exec .staticcall) d1 ∧
    d1.stack = 1 :: 164 :: 0x70a08231 :: (burnT1 sevm b &&& burnAddrMask) :: 0 ::
      burnB0 d0 :: burnT1 sevm b :: burnT0 sevm b :: burnInitLocals sevm b R ∧
    32 ≤ d1.returnData.length ∧
    d1.gasLeft = T1 + 64 ∧
    d1.returnData = (d0.getStorVal (burnT1 sevm b &&& burnAddrMask).toAdr
      (Weth9.balSlot sevm.currentTarget)).toBytes := by
  obtain ⟨hcode, hrun, hstk, hgas, hlong, hret⟩ := wethReadLeg128_spec (sevm := sevm)
    (B := d0) (S := burnRead1Stack sevm b R d0) (M := burnMem1 sevm d0)
    (t := burnT1 sevm b &&& burnAddrMask) (need := fun _ => T1 + 64) (swapTokenWord_burnT1 sevm b)
    (fun _ _ => rfl) fork wethCode depth notPrecompile
    (by simp only [burnRead1Stack, burnInitLocals, List.length_cons]; omega)
    (burnMem1_wf sevm d0) fits room
  exact ⟨hcode, hrun, hstk, hlong, hgas, hret⟩

end Blanc.Composition.UniswapV2PairWeth9Joint
