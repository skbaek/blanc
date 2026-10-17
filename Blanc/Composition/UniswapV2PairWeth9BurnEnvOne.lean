import Blanc.Composition.UniswapV2PairWeth9BurnEnv
import Blanc.Composition.UniswapV2PairWeth9LegsBurn1

/-!
# C4(b): Burn's callee environment with WETH9 = token1 (U8h)

`BurnForwardEnv` with WETH9's three records removed: the second initial `balanceOf(pair)` query
(`BurnInitialCallee.code1`…`returnedGas1`), the second transfer (`BurnBackForwardEnv.transfer1`) and
the second final query (`BurnBackForwardEnv.second`).  Each is pinned to the leg WETH9's code
determines (`burnWethRead1`, `burnWethLeg1`, `burnWethFinal1`).  What stays: X = token0's initial
query, transfer and final query, the factory `feeTo` query, and the Pair's own charges and sentries.

**One-directional pins (A17).**  Every pin's right side reads only values bound before it:

* `back.leg` reads X's transfer result `d0` and X's final query's call gas `balanceGas0` (free
  fields declared before it);
* `back.final` reads `d0`, the pinned `d1` and X's final result `e0`;
* `read` reads X's initial result `d0` and the factory call's gas `factoryGas`, a free field declared
  before the WETH9 read.  The record's residual after the read is the fee caller's gas
  `fee.gas`, which reads the read's result only off its gas-free columns; `burnFee1Gas` evaluates it
  on the read's gas-free skeleton (`BurnEnvW1.fee_gas`), so no fixed point is left.  The factory
  record's own call gas is tied to `factoryGas` (`feeGas`).

`toInitial` / `toBack` put WETH9's records back.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

/-! ## The suffix -/

/-- `BurnBackForwardEnv` with WETH9 = token1's transfer and final query pinned. -/
structure BurnBackW1 (sevm : Sevm) (b : Devm) (M : Mem) (p0 : B256) (w : BurnSuffixWords)
    (R : List B256) (G : Nat) where
  d0 : Devm
  e0 : Devm
  callGas0 : Nat
  balanceGas0 : Nat
  d1 : Devm
  callGas1 : Nat
  leg : (d1, callGas1) = burnWethLeg1 sevm d0 M p0 w R balanceGas0
  e1 : Devm
  balanceGas1 : Nat
  final : (e1, balanceGas1) = burnWethFinal1 sevm M p0 w R d0 d1 e0 G
  transfer0 : SwapTransferCallForward sevm b (w.locals w.balance1 w.balance0 R) M M.size p0
    w.amount0 w.recipient w.token0 0x1698 callGas0
    (callGas1 + safeTransferPreCharge (burnSuffixMem1 M p0 w d0).size
      (swapMovedPointer p0 d0.returnData) + 24) d0
  first : SwapBalanceEnv sevm d1 (burnSuffixMem2 M p0 w d0 d1) (burnSuffixPtr p0 d0 d1) w.token0
    (w.locals w.balance1 w.balance0 R) e0 balanceGas0
    (balanceGas1 + 5 + swapRequestCharge e0
      (swapRequestSize (burnSuffixMem2 M p0 w d0 d1).size (burnSuffixPtr p0 d0 d1))
      (burnSuffixPtr p0 d0 d1) w.token1 83 + 21)
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

section Back

variable {sevm : Sevm} {b : Devm} {M : Mem} {p0 : B256} {w : BurnSuffixWords} {R : List B256}
  {G : Nat}

def BurnBackW1.gas (env : BurnBackW1 sevm b M p0 w R G) : Nat :=
  env.callGas0 + safeTransferPreCharge M.size p0 + 24

/-- WETH9's transfer and final query put back. -/
def BurnBackW1.toBack (env : BurnBackW1 sevm b M p0 w R G)
    (transfer1 : SwapTransferCallForward sevm env.d0 (w.locals w.balance1 w.balance0 R)
      (burnSuffixMem1 M p0 w env.d0) (burnSuffixMem1 M p0 w env.d0).size
      (swapMovedPointer p0 env.d0.returnData) w.amount1 w.recipient w.token1 0x16a3 env.callGas1
      (env.balanceGas0 + 5 + swapRequestCharge env.d1 (burnSuffixMem2 M p0 w env.d0 env.d1).size
        (burnSuffixPtr p0 env.d0 env.d1) w.token0 72 + 16) env.d1)
    (second : SwapBalanceEnv sevm env.e0
      (swapBalanceReply (burnSuffixMem2 M p0 w env.d0 env.d1) (burnSuffixPtr p0 env.d0 env.d1)
        sevm.currentTarget env.e0.returnData) (burnSuffixPtr p0 env.d0 env.d1) w.token1
      (w.locals w.balance1 (Bytes.toB256 (env.e0.returnData.take 32)) R) env.e1 env.balanceGas1
      (burnSuffixTailGas sevm M p0 w env.d0 env.d1 env.e0 env.e1 G)) :
    BurnBackForwardEnv sevm b M p0 w R G :=
  { d0 := env.d0, d1 := env.d1, e0 := env.e0, e1 := env.e1, callGas0 := env.callGas0,
    callGas1 := env.callGas1, balanceGas0 := env.balanceGas0, balanceGas1 := env.balanceGas1,
    transfer0 := env.transfer0, transfer1 := transfer1, first := env.first, second := second,
    sentries := env.sentries, checkpoint := env.checkpoint, unlock := env.unlock }

end Back

/-! ## The initial queries -/

/-- `BurnInitialCallee` with WETH9 = token1's query removed (its result `d1` and call gas
`callGas1` are bound outside, by the read pin). -/
structure BurnInitialW1 (sevm : Sevm) (b d0 : Devm) (R : List B256) (callGas1 : Nat) where
  callGas0 : Nat
  lockLoad : Nat
  lockStore : Nat
  reserveLoad : Nat
  loadEq : lockLoad = sloadCost sevm b 12
  storeEq : lockStore = sstoreCost sevm (afterSload sevm b 12) 12 0
  reserveEq : reserveLoad = sloadCost sevm (burnLockedWorld sevm b) 8
  sentry : gCallStipend < burnInitialGas0 sevm b callGas0 + reserveLoad + 87 + lockStore
  code0 : ((burnTokensWorld sevm (burnReservedWorld sevm b)).getCode
    (burnT0 sevm b).toAdr).size.toB256 ≠ 0
  call0 : Ninst.RunCompiled sevm
    (St (burnCall0World sevm b) (callGas0.toB256 :: burnT0 sevm b :: 128 :: 36 :: 128 :: 32 ::
      164 :: 0x70a08231 :: burnT0 sevm b :: 0 :: burnT1 sevm b :: burnT0 sevm b ::
      burnInitLocals sevm b R)
      (balanceRequestMemory getterInitMemory sevm.currentTarget) callGas0) (.exec .staticcall) d0
  success0 : d0.stack = 1 :: 164 :: 0x70a08231 :: burnT0 sevm b :: 0 :: burnT1 sevm b ::
    burnT0 sevm b :: burnInitLocals sevm b R
  long0 : 32 ≤ d0.returnData.length
  returnedGas0 : d0.gasLeft = burnInitialGas1 sevm b d0 callGas1 + 64

/-- WETH9's initial query put back. -/
def BurnInitialW1.toInitial {sevm : Sevm} {b d0 d1 : Devm} {R : List B256} {callGas1 T1 : Nat}
    (c : BurnInitialW1 sevm b d0 R callGas1)
    (code1 : (d0.getCode (burnT1 sevm b &&& burnAddrMask).toAdr).size.toB256 ≠ 0)
    (call1 : Ninst.RunCompiled sevm
      (St (burnCall1World sevm b d0) (callGas1.toB256 :: (burnT1 sevm b &&& burnAddrMask) ::
        128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 :: (burnT1 sevm b &&& burnAddrMask) :: 0 ::
        burnB0 d0 :: burnT1 sevm b :: burnT0 sevm b :: burnInitLocals sevm b R)
        (balanceRequestMemory (burnMem1 sevm d0) sevm.currentTarget) callGas1) (.exec .staticcall) d1)
    (success1 : d1.stack = 1 :: 164 :: 0x70a08231 :: (burnT1 sevm b &&& burnAddrMask) :: 0 ::
      burnB0 d0 :: burnT1 sevm b :: burnT0 sevm b :: burnInitLocals sevm b R)
    (long1 : 32 ≤ d1.returnData.length) (returnedGas1 : d1.gasLeft = T1 + 64) :
    BurnInitialCallee sevm b d0 d1 R T1 :=
  { callGas0 := c.callGas0, callGas1 := callGas1, lockLoad := c.lockLoad,
    lockStore := c.lockStore, reserveLoad := c.reserveLoad, loadEq := c.loadEq,
    storeEq := c.storeEq, reserveEq := c.reserveEq, sentry := c.sentry, code0 := c.code0,
    call0 := c.call0, success0 := c.success0, long0 := c.long0, returnedGas0 := c.returnedGas0,
    code1 := code1, call1 := call1, success1 := success1, long1 := long1,
    returnedGas1 := returnedGas1 }

def BurnInitialW1.gas {sevm : Sevm} {b d0 : Devm} {R : List B256} {callGas1 : Nat}
    (c : BurnInitialW1 sevm b d0 R callGas1) : Nat :=
  burnInitialGas0 sevm b c.callGas0 + c.reserveLoad + 100 + c.lockStore + c.lockLoad + 29

/-! ## The fee caller's gas on the read's skeleton -/

/-- The gas-free skeleton of the WETH9 query's result (token1 = WETH9). -/
def burnRead1Skel (sevm : Sevm) (b d0 : Devm) (R : List B256) : Devm :=
  wethBalanceSkel sevm d0 (burnRead1Stack sevm b R d0) (burnMem1 sevm d0) 128
    (burnT1 sevm b &&& burnAddrMask)

theorem burnWethRead1_skel (sevm : Sevm) (b d0 : Devm) (R : List B256) (T1 : Nat) :
    ∃ x, (burnWethRead1 sevm b d0 R T1).1 = (burnRead1Skel sevm b d0 R).withGasLeft x :=
  ⟨_, wethBalanceCallAt_eq _ _ _ _ _ _ _ _ _ _⟩

/-- The gas the fee caller (`BurnFeeCallee.gas`) needs at the WETH9 query's result, evaluated on
the query's gas-free skeleton, for the factory call gas `factoryGas`. -/
def burnFee1Gas (sevm : Sevm) (b d0 : Devm) (R : List B256) (factoryGas : Nat) : Nat :=
  feeMintEntryGas sevm (feeBurnWorld sevm (burnRead1Skel sevm b d0 R)) factoryGas +
    sloadCost sevm (burnRead1Skel sevm b d0 R) (transferBalanceSlot sevm.currentTarget) + 105

/-- The fee caller's gas reads its world only off the non-gas columns. -/
theorem burnFeeGas_gasFree (sevm : Sevm) (d : Devm) (factoryGas x : Nat) :
    feeMintEntryGas sevm (feeBurnWorld sevm (d.withGasLeft x)) factoryGas +
        sloadCost sevm (d.withGasLeft x) (transferBalanceSlot sevm.currentTarget) + 105 =
      feeMintEntryGas sevm (feeBurnWorld sevm d) factoryGas +
        sloadCost sevm d (transferBalanceSlot sevm.currentTarget) + 105 := by
  unfold feeMintEntryGas feeBurnWorld feeFactoryLoadWorld feeFactoryWord Devm.withGasLeft
  rw [afterSload_setMach, afterSload_setMach]
  rfl

/-! ## The whole environment -/

/-- **Burn's callee environment with WETH9 as token1.**  Pins in binding order: `read` (from the
free `d0`, `factoryGas`), then inside `back` `leg` and `final`. -/
structure BurnEnvW1 (sevm : Sevm) (b : Devm) (g : Nat) where
  d0 : Devm
  dF : Devm
  factoryGas : Nat
  d1 : Devm
  callGas1 : Nat
  read : (d1, callGas1) = burnWethRead1 sevm b d0 [0x89afcb44] (burnFee1Gas sevm b d0 [0x89afcb44]
    factoryGas)
  back : BurnBackW1 sevm (burnBodyWorld sevm b d0 d1 dF)
    (burnBodyWorld sevm b d0 d1 dF).memory 128 (burnBodyWords sevm b d0 d1 dF) [0x89afcb44] (g + 64)
  fee : BurnFeeCallee sevm d1 dF (burnMem2 sevm d0 d1) (burnB0 d0) (burnT1 sevm b) (burnT0 sevm b)
    (burnR1 sevm b) (burnR0 sevm b) (burnRecipientWord sevm) 0x053d [0x89afcb44] back.gas
  feeGas : fee.factoryGas = factoryGas
  initial : BurnInitialW1 sevm b d0 [0x89afcb44] callGas1

section Env

variable {sevm : Sevm} {b : Devm} {g : Nat}

/-- **The pinned read leaves exactly the fee caller's gas.**  The fee record's entry gas at the
pinned query result is `burnFee1Gas`, the argument the read pin was solved at. -/
theorem BurnEnvW1.fee_gas (env : BurnEnvW1 sevm b g) :
    env.fee.gas = burnFee1Gas sevm b env.d0 [0x89afcb44] env.factoryGas := by
  obtain ⟨x, hx⟩ := burnWethRead1_skel sevm b env.d0 [0x89afcb44]
    (burnFee1Gas sevm b env.d0 [0x89afcb44] env.factoryGas)
  have hd1 : env.d1 = (burnRead1Skel sevm b env.d0 [0x89afcb44]).withGasLeft x := by
    rw [← hx]
    exact congrArg Prod.fst env.read
  unfold BurnFeeCallee.gas burnFee1Gas
  rw [env.feeGas, hd1]
  exact burnFeeGas_gasFree sevm _ _ x

def BurnEnvW1.gas (env : BurnEnvW1 sevm b g) : Nat := env.initial.gas + 249

def BurnEnvW1.post (env : BurnEnvW1 sevm b g) : Devm :=
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

def BurnEnvW1.feeTo (env : BurnEnvW1 sevm b g) : Adr :=
  (Bytes.toB256 (env.dF.returnData.take 32)).toAdr

def BurnEnvW1.balance0 (env : BurnEnvW1 sevm b g) : B256 := Bytes.toB256 (env.d0.returnData.take 32)

def BurnEnvW1.balance1 (env : BurnEnvW1 sevm b g) : B256 := Bytes.toB256 (env.d1.returnData.take 32)

def BurnEnvW1.final0 (env : BurnEnvW1 sevm b g) : B256 :=
  Bytes.toB256 (env.back.e0.returnData.take 32)

def BurnEnvW1.final1 (env : BurnEnvW1 sevm b g) : B256 :=
  Bytes.toB256 (env.back.e1.returnData.take 32)

end Env

end Blanc.Composition.UniswapV2PairWeth9Joint
