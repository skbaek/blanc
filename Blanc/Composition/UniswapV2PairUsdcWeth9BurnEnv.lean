import Blanc.Composition.UniswapV2PairUsdcWeth9LegsBurn
import Blanc.Composition.UniswapV2PairWeth9BurnEnvOne
import Blanc.Composition.UniswapV2PairWeth9XLegStatic

/-!
# Burn's callee environment with both tokens pinned (USDC = token0, WETH9 = token1; U9 freeze §3b, U9d)

`BurnForwardEnv` with all six token records pinned.  Pins in binding order (A17), each reading free
values or earlier pins; a WETH9 pin reads a USDC result through its gas-free skeleton, a USDC pin
reads WETH9's results through their call gases:

* initial queries: `read1` (WETH9, over `burnUsdcRead0Skel` and the free `factoryGas`), then
  `read0` (USDC, at `callGas1`);
* suffix: `final1` (WETH9's final query, over the three skeletons), `gas0` (USDC's final query's
  call gas, on WETH9's leg skeleton), `leg1` (WETH9's transfer, over USDC's leg skeleton), `leg0`
  (USDC's transfer, at `callGas1`), `final0` (USDC's final query's result).

`BurnEnvUW.fee_gas`: the pinned WETH9 read leaves exactly the fee caller's gas.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Lift.Usdc
  Blanc.Composition.UniswapV2PairWeth9Joint Blanc.Composition.UsdcLive
open Blanc.Composition.UniswapV2PairWeth9XLeg (StaticChildFresh wethRunKeys)


/-- `BurnBackForwardEnv` with both transfers and both final queries pinned. -/
structure BurnBackUW (sevm : Sevm) (b : Devm) (M : Mem) (p0 : B256) (w : BurnSuffixWords)
    (R : List B256) (G : Nat) where
  e1 : Devm
  balanceGas1 : Nat
  final1 : (e1, balanceGas1) = burnWethFinal1 sevm M p0 w R (burnUsdcLeg0Skel sevm b M p0 w R)
    (burnLeg1Skel sevm (burnUsdcLeg0Skel sevm b M p0 w R) M p0 w R)
    (burnUsdcFinal0Skel sevm M p0 w R (burnUsdcLeg0Skel sevm b M p0 w R)
      (burnLeg1Skel sevm (burnUsdcLeg0Skel sevm b M p0 w R) M p0 w R)) G
  balanceGas0 : Nat
  gas0 : balanceGas0 = (burnUsdcFinal0 sevm M p0 w R (burnUsdcLeg0Skel sevm b M p0 w R)
    (burnLeg1Skel sevm (burnUsdcLeg0Skel sevm b M p0 w R) M p0 w R) balanceGas1).2
  d1 : Devm
  callGas1 : Nat
  leg1 : (d1, callGas1) = burnWethLeg1 sevm (burnUsdcLeg0Skel sevm b M p0 w R) M p0 w R balanceGas0
  d0 : Devm
  callGas0 : Nat
  leg0 : (d0, callGas0) = burnUsdcLeg0 sevm b M p0 w R callGas1
  e0 : Devm
  final0 : e0 = (burnUsdcFinal0 sevm M p0 w R d0 d1 balanceGas1).1
  sentries : SwapUpdateSentries sevm e1 (burnSuffixSize M p0 w d0 d1) (burnSuffixPtr p0 d0 d1)
    w.reserve0 w.reserve1 (Bytes.toB256 (e0.returnData.take 32))
    (Bytes.toB256 (e1.returnData.take 32))
    (burnKLastGas sevm (burnSuffixUpdated sevm w e0 e1) w.feeFlag
      (burnEventRunGas G (swapSyncSize (burnSuffixSize M p0 w d0 d1) (burnSuffixPtr p0 d0 d1))
        (burnSuffixPtr p0 d0 d1) (burnSuffixUnlockCost sevm w e0 e1)))
  checkpoint : w.feeFlag ≠ 0 → gCallStipend <
    burnEventRunGas G (swapSyncSize (burnSuffixSize M p0 w d0 d1) (burnSuffixPtr p0 d0 d1))
      (burnSuffixPtr p0 d0 d1) (burnSuffixUnlockCost sevm w e0 e1) +
    sstoreCost sevm (afterSload sevm (burnSuffixUpdated sevm w e0 e1) 8) 11
      (reserve0Read ((burnSuffixUpdated sevm w e0 e1).getStorVal sevm.currentTarget 8) *
        reserve1Read ((burnSuffixUpdated sevm w e0 e1).getStorVal sevm.currentTarget 8))
  unlock : gCallStipend < G + 18 + burnSuffixUnlockCost sevm w e0 e1

section BurnBack

variable {sevm : Sevm} {b : Devm} {M : Mem} {p0 : B256} {w : BurnSuffixWords} {R : List B256}
  {G : Nat}

def BurnBackUW.gas (env : BurnBackUW sevm b M p0 w R G) : Nat :=
  env.callGas0 + safeTransferPreCharge M.size p0 + 24

/-- Both tokens' records put back (U9d proves the four records from the specs). -/
def BurnBackUW.toBack (env : BurnBackUW sevm b M p0 w R G)
    (transfer0 : SwapTransferCallForward sevm b (w.locals w.balance1 w.balance0 R) M M.size p0
      w.amount0 w.recipient w.token0 0x1698 env.callGas0
      (env.callGas1 + safeTransferPreCharge (burnSuffixMem1 M p0 w env.d0).size
        (swapMovedPointer p0 env.d0.returnData) + 24) env.d0)
    (transfer1 : SwapTransferCallForward sevm env.d0 (w.locals w.balance1 w.balance0 R)
      (burnSuffixMem1 M p0 w env.d0) (burnSuffixMem1 M p0 w env.d0).size
      (swapMovedPointer p0 env.d0.returnData) w.amount1 w.recipient w.token1 0x16a3 env.callGas1
      (env.balanceGas0 + 5 + swapRequestCharge env.d1 (burnSuffixMem2 M p0 w env.d0 env.d1).size
        (burnSuffixPtr p0 env.d0 env.d1) w.token0 72 + 16) env.d1)
    (first : SwapBalanceEnv sevm env.d1 (burnSuffixMem2 M p0 w env.d0 env.d1)
      (burnSuffixPtr p0 env.d0 env.d1) w.token0 (w.locals w.balance1 w.balance0 R) env.e0
      env.balanceGas0
      (env.balanceGas1 + 5 + swapRequestCharge env.e0
        (swapRequestSize (burnSuffixMem2 M p0 w env.d0 env.d1).size (burnSuffixPtr p0 env.d0 env.d1))
        (burnSuffixPtr p0 env.d0 env.d1) w.token1 83 + 21))
    (second : SwapBalanceEnv sevm env.e0
      (swapBalanceReply (burnSuffixMem2 M p0 w env.d0 env.d1) (burnSuffixPtr p0 env.d0 env.d1)
        sevm.currentTarget env.e0.returnData) (burnSuffixPtr p0 env.d0 env.d1) w.token1
      (w.locals w.balance1 (Bytes.toB256 (env.e0.returnData.take 32)) R) env.e1 env.balanceGas1
      (burnSuffixTailGas sevm M p0 w env.d0 env.d1 env.e0 env.e1 G)) :
    BurnBackForwardEnv sevm b M p0 w R G :=
  { d0 := env.d0, d1 := env.d1, e0 := env.e0, e1 := env.e1, callGas0 := env.callGas0,
    callGas1 := env.callGas1, balanceGas0 := env.balanceGas0, balanceGas1 := env.balanceGas1,
    transfer0 := transfer0, transfer1 := transfer1, first := first, second := second,
    sentries := env.sentries, checkpoint := env.checkpoint, unlock := env.unlock }

end BurnBack

/-- `BurnInitialCallee` with both initial queries removed: the lock and reserve charges and the
Pair's sentry at the (pinned) first call gas. -/
structure BurnInitialUW (sevm : Sevm) (b : Devm) (callGas0 : Nat) where
  lockLoad : Nat
  lockStore : Nat
  reserveLoad : Nat
  loadEq : lockLoad = sloadCost sevm b 12
  storeEq : lockStore = sstoreCost sevm (afterSload sevm b 12) 12 0
  reserveEq : reserveLoad = sloadCost sevm (burnLockedWorld sevm b) 8
  sentry : gCallStipend < burnInitialGas0 sevm b callGas0 + reserveLoad + 87 + lockStore

def BurnInitialUW.gas {sevm : Sevm} {b : Devm} {callGas0 : Nat} (c : BurnInitialUW sevm b callGas0) :
    Nat :=
  burnInitialGas0 sevm b callGas0 + c.reserveLoad + 100 + c.lockStore + c.lockLoad + 29

/-- **Burn's callee environment with both tokens pinned** (USDC = token0, WETH9 = token1).  Free:
the factory record's result `dF` and call gas `factoryGas`, the Pair's charges.  The factory `feeTo`
record (`fee`) stays a premise. -/
structure BurnEnvUW (sevm : Sevm) (b : Devm) (g : Nat) where
  dF : Devm
  factoryGas : Nat
  d1 : Devm
  callGas1 : Nat
  read1 : (d1, callGas1) = burnWethRead1 sevm b (burnUsdcRead0Skel sevm b [0x89afcb44]) [0x89afcb44]
    (burnFee1Gas sevm b (burnUsdcRead0Skel sevm b [0x89afcb44]) [0x89afcb44] factoryGas)
  d0 : Devm
  callGas0 : Nat
  read0 : (d0, callGas0) = burnUsdcRead0 sevm b [0x89afcb44] callGas1
  back : BurnBackUW sevm (burnBodyWorld sevm b d0 d1 dF)
    (burnBodyWorld sevm b d0 d1 dF).memory 128 (burnBodyWords sevm b d0 d1 dF) [0x89afcb44] (g + 64)
  fee : BurnFeeCallee sevm d1 dF (burnMem2 sevm d0 d1) (burnB0 d0) (burnT1 sevm b) (burnT0 sevm b)
    (burnR1 sevm b) (burnR0 sevm b) (burnRecipientWord sevm) 0x053d [0x89afcb44] back.gas
  feeGas : fee.factoryGas = factoryGas
  initial : BurnInitialUW sevm b callGas0

section BurnEnv

variable {sevm : Sevm} {b : Devm} {g : Nat}

abbrev BurnEnvUW.body (env : BurnEnvUW sevm b g) : Devm := burnBodyWorld sevm b env.d0 env.d1 env.dF

abbrev BurnEnvUW.words (env : BurnEnvUW sevm b g) : BurnSuffixWords :=
  burnBodyWords sevm b env.d0 env.d1 env.dF

def BurnEnvUW.gas (env : BurnEnvUW sevm b g) : Nat := env.initial.gas + 249

def BurnEnvUW.post (env : BurnEnvUW sevm b g) : Devm :=
  burnReturnPost (burnUnlockPost sevm (burnKLastPost sevm (burnSuffixUpdated sevm
      (burnBodyWords sevm b env.d0 env.d1 env.dF) env.back.e0 env.back.e1)
      (burnBodyWords sevm b env.d0 env.d1 env.dF).feeFlag)
      (burnBodyWords sevm b env.d0 env.d1 env.dF).recipient
      (burnBodyWords sevm b env.d0 env.d1 env.dF).amount0
      (burnBodyWords sevm b env.d0 env.d1 env.dF).amount1) [0x89afcb44]
    (burnEventMemory (swapSyncMemory (swapBalanceReply (swapBalanceReply
        (burnSuffixMem2 (burnBodyWorld sevm b env.d0 env.d1 env.dF).memory 128
          (burnBodyWords sevm b env.d0 env.d1 env.dF) env.back.d0 env.back.d1)
        (burnSuffixPtr 128 env.back.d0 env.back.d1) sevm.currentTarget env.back.e0.returnData)
        (burnSuffixPtr 128 env.back.d0 env.back.d1) sevm.currentTarget env.back.e1.returnData)
        (burnSuffixPtr 128 env.back.d0 env.back.d1)
        (updateFinalPackedWord sevm env.back.e1 (burnBodyWords sevm b env.d0 env.d1 env.dF).reserve0
          (burnBodyWords sevm b env.d0 env.d1 env.dF).reserve1
          (Bytes.toB256 (env.back.e0.returnData.take 32))
          (Bytes.toB256 (env.back.e1.returnData.take 32))))
      (burnSuffixPtr 128 env.back.d0 env.back.d1) (burnBodyWords sevm b env.d0 env.d1 env.dF).amount0
      (burnBodyWords sevm b env.d0 env.d1 env.dF).amount1)
    (burnSuffixPtr 128 env.back.d0 env.back.d1) (burnBodyWords sevm b env.d0 env.d1 env.dF).amount0
    (burnBodyWords sevm b env.d0 env.d1 env.dF).amount1 g

def BurnEnvUW.feeTo (env : BurnEnvUW sevm b g) : Adr :=
  (Bytes.toB256 (env.dF.returnData.take 32)).toAdr

def BurnEnvUW.balance0 (env : BurnEnvUW sevm b g) : B256 := Bytes.toB256 (env.d0.returnData.take 32)

def BurnEnvUW.balance1 (env : BurnEnvUW sevm b g) : B256 := Bytes.toB256 (env.d1.returnData.take 32)

def BurnEnvUW.final0 (env : BurnEnvUW sevm b g) : B256 :=
  Bytes.toB256 (env.back.e0.returnData.take 32)

def BurnEnvUW.final1 (env : BurnEnvUW sevm b g) : B256 :=
  Bytes.toB256 (env.back.e1.returnData.take 32)

/-- The factory query's staged state (`BurnFeeCallee.call`), as in `BurnEnvW1.factoryPre`. -/
def BurnEnvUW.factoryPre (env : BurnEnvUW sevm b g) : Devm :=
  St (feeFactoryCallWorld sevm (feeBurnWorld sevm env.d1))
    (env.fee.factoryGas.toB256 :: feeFactoryWord sevm (feeBurnWorld sevm env.d1) :: 128 :: 4 ::
      128 :: 32 :: 132 :: 0x017e7e58 :: feeFactoryWord sevm (feeBurnWorld sevm env.d1) :: 0 :: 0 ::
      burnR1 sevm b :: burnR0 sevm b :: 0x15e2 ::
      burnFeeLocalsAt sevm env.d1 (burnMem2 sevm env.d0 env.d1) (burnB0 env.d0) (burnT1 sevm b)
        (burnT0 sevm b) (burnR1 sevm b) (burnR0 sevm b) (burnRecipientWord sevm) 0x053d [0x89afcb44])
    (feeRequestMemory (feeBurnMemory (burnMem2 sevm env.d0 env.d1) sevm.currentTarget))
    env.fee.factoryGas

/-- **HASH-T over the factory query's child** (the one premise record left between WETH9's initial
query and its transfer): the WETH9 keys its frames touch are fresh against WETH9's universe.  USDC's
children need none: their posts are explicit (`usdcTransferCall`, `usdcBalanceCall`), and U9d
carries WETH9's facts across them by a storage-keeping lemma instead. -/
structure BurnEnvUW.XFresh (env : BurnEnvUW sevm b g) (weth : Adr) (UW : Weth9.Key → Prop) : Prop where
  factory : StaticChildFresh sevm env.factoryPre fun D => Weth9.KeysFresh UW (wethRunKeys weth D)

/-- **USDC's gas sentries**: each USDC leg's call gas a word, and room for USDC's run (proxy and
implementation) under the 63/64 rule. -/
structure BurnEnvUW.UsdcSentries (env : BurnEnvUW sevm b g) : Prop where
  fitsRead : env.callGas0 < 2 ^ 256
  roomRead : usdcBalNeed sevm (burnRead0World sevm b) (burnRead0Stack sevm b [0x89afcb44])
      getterInitMemory 128 (burnT0 sevm b) ≤
    except64th (burnRead0Need sevm b env.callGas1 (burnUsdcRead0Skel sevm b [0x89afcb44]) +
      usdcBalUsed sevm (burnRead0World sevm b) (burnRead0Stack sevm b [0x89afcb44])
        getterInitMemory 128 (burnT0 sevm b))
  fitsLeg : env.back.callGas0 < 2 ^ 256
  roomLeg : burnUsdcLeg0Budget sevm env.body env.body.memory 128 env.words [0x89afcb44] ≤
    except64th (burnUsdcLeg0Need sevm env.body env.body.memory 128 env.words [0x89afcb44]
        env.back.callGas1 +
      burnUsdcLeg0Used sevm env.body env.body.memory 128 env.words [0x89afcb44])
  fitsFinal : env.back.balanceGas0 < 2 ^ 256
  roomFinal : usdcBalNeed sevm env.back.d1 (env.words.locals env.words.balance1 env.words.balance0
        [0x89afcb44])
      (burnSuffixMem2 env.body.memory 128 env.words env.back.d0 env.back.d1)
      (burnSuffixPtr 128 env.back.d0 env.back.d1) env.words.token0 ≤
    except64th (burnFinal0Need env.body.memory 128 env.words env.back.d0 env.back.d1
        env.back.balanceGas1
        (burnUsdcFinal0Skel sevm env.body.memory 128 env.words [0x89afcb44] env.back.d0 env.back.d1) +
      usdcBalUsed sevm env.back.d1 (env.words.locals env.words.balance1 env.words.balance0
          [0x89afcb44])
        (burnSuffixMem2 env.body.memory 128 env.words env.back.d0 env.back.d1)
        (burnSuffixPtr 128 env.back.d0 env.back.d1) env.words.token0)

/-- **WETH9's gas sentries** (`BurnEnvW1.WethSentries`, verbatim over the pinned fields). -/
structure BurnEnvUW.WethSentries (env : BurnEnvUW sevm b g) : Prop where
  fitsRead : env.callGas1 < 2 ^ 256
  roomRead : balUsed sevm env.d0 (burnRead1Stack sevm b [0x89afcb44] env.d0) (burnMem1 sevm env.d0) 128
      (burnT1 sevm b &&& burnAddrMask) ≤
    except64th (burnFee1Gas sevm b env.d0 [0x89afcb44] env.factoryGas + 64 +
      balUsed sevm env.d0 (burnRead1Stack sevm b [0x89afcb44] env.d0) (burnMem1 sevm env.d0) 128
        (burnT1 sevm b &&& burnAddrMask))
  fitsLeg : env.back.callGas1 < 2 ^ 256
  roomLeg : burnLeg1Used sevm env.back.d0 env.body.memory 128 env.words [0x89afcb44] + gCallStipend ≤
    except64th (burnLeg1Need sevm env.back.d0 env.body.memory 128 env.words [0x89afcb44]
        env.back.balanceGas0 +
      burnLeg1Used sevm env.back.d0 env.body.memory 128 env.words [0x89afcb44])
  fitsFinal : env.back.balanceGas1 < 2 ^ 256
  roomFinal : balUsed sevm env.back.e0 (burnFinal1Stack env.words [0x89afcb44] env.back.e0)
      (burnFinal1Mem sevm env.body.memory 128 env.words env.back.d0 env.back.d1 env.back.e0)
      (burnSuffixPtr 128 env.back.d0 env.back.d1) env.words.token1 ≤
    except64th (burnFinal1Need sevm env.body.memory 128 env.words env.back.d0 env.back.d1 env.back.e0
        (g + 64) (wethBalanceSkel sevm env.back.e0 (burnFinal1Stack env.words [0x89afcb44] env.back.e0)
          (burnFinal1Mem sevm env.body.memory 128 env.words env.back.d0 env.back.d1 env.back.e0)
          (burnSuffixPtr 128 env.back.d0 env.back.d1) env.words.token1) +
      balUsed sevm env.back.e0 (burnFinal1Stack env.words [0x89afcb44] env.back.e0)
        (burnFinal1Mem sevm env.body.memory 128 env.words env.back.d0 env.back.d1 env.back.e0)
        (burnSuffixPtr 128 env.back.d0 env.back.d1) env.words.token1)

end BurnEnv

theorem burnRead1Skel_withGasLeft (sevm : Sevm) (b d0 : Devm) (R : List B256) (x : Nat) :
    burnRead1Skel sevm b (d0.withGasLeft x) R = burnRead1Skel sevm b d0 R := by
  change wethBalanceSkel sevm (d0.withGasLeft x) (burnRead1Stack sevm b R d0) (burnMem1 sevm d0) 128
    (burnT1 sevm b &&& burnAddrMask) = _
  rw [wethBalanceSkel_withGasLeft]
  rfl

/-- **The pinned WETH9 read leaves exactly the fee caller's gas** (`BurnEnvW1.fee_gas` over USDC's
skeleton). -/
theorem BurnEnvUW.fee_gas {sevm : Sevm} {b : Devm} {g : Nat} (env : BurnEnvUW sevm b g) :
    env.fee.gas = burnFee1Gas sevm b (burnUsdcRead0Skel sevm b [0x89afcb44]) [0x89afcb44]
      env.factoryGas := by
  obtain ⟨x, hx⟩ := burnWethRead1_skel sevm b (burnUsdcRead0Skel sevm b [0x89afcb44]) [0x89afcb44]
    (burnFee1Gas sevm b (burnUsdcRead0Skel sevm b [0x89afcb44]) [0x89afcb44] env.factoryGas)
  have hd1 : env.d1 = (burnRead1Skel sevm b (burnUsdcRead0Skel sevm b [0x89afcb44])
      [0x89afcb44]).withGasLeft x := by
    rw [← hx]
    exact congrArg Prod.fst env.read1
  unfold BurnFeeCallee.gas burnFee1Gas
  rw [env.feeGas, hd1]
  exact burnFeeGas_gasFree sevm _ _ x

end Blanc.Composition.UniswapV2PairUsdcWeth9
