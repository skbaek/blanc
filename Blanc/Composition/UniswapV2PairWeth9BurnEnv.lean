import Blanc.Composition.UniswapV2PairWeth9BurnWorld
import Blanc.Lift.UniswapV2Pair.BurnForwardAccept

/-!
# C4(b): Burn's callee environment with WETH9 = token0 (U8d)

`BurnForwardEnv` with WETH9's three records removed: the first initial `balanceOf(pair)` query
(`BurnInitialCallee.code0`…`returnedGas0`), the first transfer (`BurnBackForwardEnv.transfer0`) and
the first final query (`BurnBackForwardEnv.first`).  Each is pinned (`read`, `leg`, `final`) to the
leg WETH9's code determines (`burnWethRead0`, `burnWethLeg0`, `burnWethFinal0`, U8b2).  What stays:
token1's initial query, the factory `feeTo` query, token1's transfer and final query, and the Pair's
own charges and sentries.  `toInitial` / `toBack` / `toEnv` put WETH9's records back.

`burnGuards_of_model` is `BurnForwardEnv.guards_of_model` over only the records it reads.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

/-! ## The suffix -/

/-- `BurnBackForwardEnv` with WETH9 = token0's transfer and final query pinned. -/
structure BurnBackW0 (sevm : Sevm) (b : Devm) (M : Mem) (p0 : B256) (w : BurnSuffixWords)
    (R : List B256) (G : Nat) where
  d0 : Devm
  d1 : Devm
  e0 : Devm
  e1 : Devm
  callGas0 : Nat
  callGas1 : Nat
  balanceGas0 : Nat
  balanceGas1 : Nat
  leg : (d0, callGas0) = burnWethLeg0 sevm b M p0 w R callGas1
  final : (e0, balanceGas0) = burnWethFinal0 sevm M p0 w R d0 d1 balanceGas1
  transfer1 : SwapTransferCallForward sevm d0 (w.locals w.balance1 w.balance0 R)
    (burnSuffixMem1 M p0 w d0) (burnSuffixMem1 M p0 w d0).size (swapMovedPointer p0 d0.returnData)
    w.amount1 w.recipient w.token1 0x16a3 callGas1
    (balanceGas0 + 5 + swapRequestCharge d1 (burnSuffixMem2 M p0 w d0 d1).size
      (burnSuffixPtr p0 d0 d1) w.token0 72 + 16) d1
  second : SwapBalanceEnv sevm e0
    (swapBalanceReply (burnSuffixMem2 M p0 w d0 d1) (burnSuffixPtr p0 d0 d1) sevm.currentTarget
      e0.returnData) (burnSuffixPtr p0 d0 d1) w.token1
    (w.locals w.balance1 (Bytes.toB256 (e0.returnData.take 32)) R) e1 balanceGas1
    (burnSuffixTailGas sevm M p0 w d0 d1 e0 e1 G)
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

def BurnBackW0.gas (env : BurnBackW0 sevm b M p0 w R G) : Nat :=
  env.callGas0 + safeTransferPreCharge M.size p0 + 24

/-- WETH9's transfer and final query put back. -/
def BurnBackW0.toBack (env : BurnBackW0 sevm b M p0 w R G)
    (transfer0 : SwapTransferCallForward sevm b (w.locals w.balance1 w.balance0 R) M M.size p0
      w.amount0 w.recipient w.token0 0x1698 env.callGas0
      (env.callGas1 + safeTransferPreCharge (burnSuffixMem1 M p0 w env.d0).size
        (swapMovedPointer p0 env.d0.returnData) + 24) env.d0)
    (first : SwapBalanceEnv sevm env.d1 (burnSuffixMem2 M p0 w env.d0 env.d1)
      (burnSuffixPtr p0 env.d0 env.d1) w.token0
      (w.locals w.balance1 w.balance0 R) env.e0 env.balanceGas0
      (env.balanceGas1 + 5 + swapRequestCharge env.e0
        (swapRequestSize (burnSuffixMem2 M p0 w env.d0 env.d1).size (burnSuffixPtr p0 env.d0 env.d1))
        (burnSuffixPtr p0 env.d0 env.d1) w.token1 83 + 21)) :
    BurnBackForwardEnv sevm b M p0 w R G :=
  { d0 := env.d0, d1 := env.d1, e0 := env.e0, e1 := env.e1, callGas0 := env.callGas0,
    callGas1 := env.callGas1, balanceGas0 := env.balanceGas0, balanceGas1 := env.balanceGas1,
    transfer0 := transfer0, transfer1 := env.transfer1, first := first, second := env.second,
    sentries := env.sentries, checkpoint := env.checkpoint, unlock := env.unlock }

end Back

/-! ## The initial queries -/

/-- `BurnInitialCallee` with WETH9 = token0's query pinned. -/
structure BurnInitialW0 (sevm : Sevm) (b d0 d1 : Devm) (R : List B256) (T1 : Nat) where
  callGas0 : Nat
  callGas1 : Nat
  lockLoad : Nat
  lockStore : Nat
  reserveLoad : Nat
  loadEq : lockLoad = sloadCost sevm b 12
  storeEq : lockStore = sstoreCost sevm (afterSload sevm b 12) 12 0
  reserveEq : reserveLoad = sloadCost sevm (burnLockedWorld sevm b) 8
  sentry : gCallStipend < burnInitialGas0 sevm b callGas0 + reserveLoad + 87 + lockStore
  read : (d0, callGas0) = burnWethRead0 sevm b R callGas1
  code1 : (d0.getCode (burnT1 sevm b &&& burnAddrMask).toAdr).size.toB256 ≠ 0
  call1 : Ninst.RunCompiled sevm
    (St (burnCall1World sevm b d0) (callGas1.toB256 :: (burnT1 sevm b &&& burnAddrMask) ::
      128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 :: (burnT1 sevm b &&& burnAddrMask) :: 0 ::
      burnB0 d0 :: burnT1 sevm b :: burnT0 sevm b :: burnInitLocals sevm b R)
      (balanceRequestMemory (burnMem1 sevm d0) sevm.currentTarget) callGas1) (.exec .staticcall) d1
  success1 : d1.stack = 1 :: 164 :: 0x70a08231 :: (burnT1 sevm b &&& burnAddrMask) :: 0 ::
    burnB0 d0 :: burnT1 sevm b :: burnT0 sevm b :: burnInitLocals sevm b R
  long1 : 32 ≤ d1.returnData.length
  returnedGas1 : d1.gasLeft = T1 + 64

/-- WETH9's initial query put back. -/
def BurnInitialW0.toInitial {sevm : Sevm} {b d0 d1 : Devm} {R : List B256} {T1 : Nat}
    (c : BurnInitialW0 sevm b d0 d1 R T1)
    (code0 : ((burnTokensWorld sevm (burnReservedWorld sevm b)).getCode
      (burnT0 sevm b).toAdr).size.toB256 ≠ 0)
    (call0 : Ninst.RunCompiled sevm
      (St (burnCall0World sevm b) (c.callGas0.toB256 :: burnT0 sevm b :: 128 :: 36 :: 128 :: 32 ::
        164 :: 0x70a08231 :: burnT0 sevm b :: 0 :: burnT1 sevm b :: burnT0 sevm b ::
        burnInitLocals sevm b R)
        (balanceRequestMemory getterInitMemory sevm.currentTarget) c.callGas0) (.exec .staticcall) d0)
    (success0 : d0.stack = 1 :: 164 :: 0x70a08231 :: burnT0 sevm b :: 0 :: burnT1 sevm b ::
      burnT0 sevm b :: burnInitLocals sevm b R)
    (long0 : 32 ≤ d0.returnData.length)
    (returnedGas0 : d0.gasLeft = burnInitialGas1 sevm b d0 c.callGas1 + 64) :
    BurnInitialCallee sevm b d0 d1 R T1 :=
  { callGas0 := c.callGas0, callGas1 := c.callGas1, lockLoad := c.lockLoad,
    lockStore := c.lockStore, reserveLoad := c.reserveLoad, loadEq := c.loadEq,
    storeEq := c.storeEq, reserveEq := c.reserveEq, sentry := c.sentry, code0 := code0,
    call0 := call0, success0 := success0, long0 := long0, returnedGas0 := returnedGas0,
    code1 := c.code1, call1 := c.call1, success1 := c.success1, long1 := c.long1,
    returnedGas1 := c.returnedGas1 }

def BurnInitialW0.gas {sevm : Sevm} {b d0 d1 : Devm} {R : List B256} {T1 : Nat}
    (c : BurnInitialW0 sevm b d0 d1 R T1) : Nat :=
  burnInitialGas0 sevm b c.callGas0 + c.reserveLoad + 100 + c.lockStore + c.lockLoad + 29

/-! ## The whole environment -/

/-- **Burn's callee environment with WETH9 as token0.** -/
structure BurnEnvW0 (sevm : Sevm) (b : Devm) (g : Nat) where
  d0 : Devm
  d1 : Devm
  dF : Devm
  back : BurnBackW0 sevm (burnBodyWorld sevm b d0 d1 dF)
    (burnBodyWorld sevm b d0 d1 dF).memory 128 (burnBodyWords sevm b d0 d1 dF) [0x89afcb44] (g + 64)
  fee : BurnFeeCallee sevm d1 dF (burnMem2 sevm d0 d1) (burnB0 d0) (burnT1 sevm b) (burnT0 sevm b)
    (burnR1 sevm b) (burnR0 sevm b) (burnRecipientWord sevm) 0x053d [0x89afcb44] back.gas
  initial : BurnInitialW0 sevm b d0 d1 [0x89afcb44] fee.gas

section Env

variable {sevm : Sevm} {b : Devm} {g : Nat}

def BurnEnvW0.gas (env : BurnEnvW0 sevm b g) : Nat := env.initial.gas + 249

def BurnEnvW0.post (env : BurnEnvW0 sevm b g) : Devm :=
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

def BurnEnvW0.feeTo (env : BurnEnvW0 sevm b g) : Adr :=
  (Bytes.toB256 (env.dF.returnData.take 32)).toAdr

def BurnEnvW0.balance0 (env : BurnEnvW0 sevm b g) : B256 := Bytes.toB256 (env.d0.returnData.take 32)

def BurnEnvW0.balance1 (env : BurnEnvW0 sevm b g) : B256 := Bytes.toB256 (env.d1.returnData.take 32)

def BurnEnvW0.final0 (env : BurnEnvW0 sevm b g) : B256 :=
  Bytes.toB256 (env.back.e0.returnData.take 32)

def BurnEnvW0.final1 (env : BurnEnvW0 sevm b g) : B256 :=
  Bytes.toB256 (env.back.e1.returnData.take 32)

end Env

/-! ## The guards from the model -/

/-- **`BurnForwardEnv.guards_of_model` over the records it reads**: the model's Burn conditions at
the answers give the primitive guards. -/
theorem burnGuards_of_model {U K : WriterKey → Prop} {st : UniswapV2Pair.State}
    {sevm : Sevm} {b d0 d1 dF e0 e1 : Devm} (long1 : 32 ≤ d1.returnData.length)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (rowFee : U (.balance (Bytes.toB256 (dF.returnData.take 32)).toAdr))
    (conditions : BurnModelConditions st (writerContext sevm []) (Bytes.toB256 (d0.returnData.take 32))
      (Bytes.toB256 (d1.returnData.take 32)) (Bytes.toB256 (dF.returnData.take 32)).toAdr
      (Bytes.toB256 (e0.returnData.take 32)) (Bytes.toB256 (e1.returnData.take 32))) :
    BurnForwardGuards K st sevm b d0 d1 dF e0 e1 := by
  obtain ⟨_, nonstatic, unlocked, fee, amount0, amount1, burnPost, events, feeAccepted, priced,
    positive0, positive1, burned, final0, final1⟩ := conditions
  have lockedRep := rep.burn_locked_world (sevm := sevm) (b := b)
  rcases lockedRep.fixed with ⟨_, _, _, _, _, cache0, cache1, _, _, _, _, _⟩
  change burnR0 sevm b = Nat.toB256 st.reserve0.val at cache0
  change burnR1 sevm b = Nat.toB256 st.reserve1.val at cache1
  have natCache0 : (burnR0 sevm b).toNat = st.reserve0.val := by
    rw [cache0]
    exact B256.toNat_toB256_of_lt (lt_trans st.reserve0.isLt (by decide : 2 ^ 112 < 2 ^ 256))
  have natCache1 : (burnR1 sevm b).toNat = st.reserve1.val := by
    rw [cache1]
    exact B256.toNat_toB256_of_lt (lt_trans st.reserve1.isLt (by decide : 2 ^ 112 < 2 ^ 256))
  have reply0 := balanceReplyMemory_ptr d0.returnData
    (balanceRequestMemory_ptr getterInitMemory_ptr sevm.currentTarget)
  have answer1 : feeBurnBalance1 (burnMem2 sevm d0 d1) = Bytes.toB256 (d1.returnData.take 32) :=
    balanceReplyMemory_word reply0.wf sevm.currentTarget d1.returnData long1
  refine ⟨unlocked, nonstatic, ⟨fee, ?_, amount0, amount1, burnPost, events, ?_, positive0,
    positive1, burned⟩, ?_, final0, final1⟩
  · rw [natCache0, natCache1]
    exact feeAccepted
  · rw [answer1]
    exact priced
  · exact fun _ _ _ _ => Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub
      (fun k member => by rw [List.mem_singleton.mp member]; exact rowFee)

end Blanc.Composition.UniswapV2PairWeth9Joint
