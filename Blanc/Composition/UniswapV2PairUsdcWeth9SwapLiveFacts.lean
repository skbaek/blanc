import Blanc.Composition.UniswapV2PairUsdcWeth9LegsXferKeep
import Blanc.Composition.UniswapV2PairUsdcWeth9LegsRead
import Blanc.Composition.UniswapV2PairUsdcWeth9Joint
import Blanc.Composition.UniswapV2PairWeth9SwapLive
import Blanc.Lift.Usdc.HistoryEnd

/-!
# Frame facts for the USDC (token0) / WETH9 (token1) swap row (U9b)

* WETH9's `transfer` CALL keeps every other account's storage (`wethTransferCall_keepsStor`), so
  USDC's implementation slot and admin word survive WETH9's leg;
* WETH9's legs read the USDC results they are staged over only off non-gas fields
  (`swapWethLeg1_withGasLeft0`, `swapWethRead1_withGasLeft0`), so the pins over USDC's gas-free
  skeletons carry to the real results;
* code identity for USDC's three runtimes across any compiled step (`image_of_runCompiled`), and
  `UsdcInstalled` from the codes and the implementation slot (`usdcInstalled_of`).
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcLive

/-! ## WETH9's `transfer` keeps the other accounts' storage -/

section WethKeep

variable (sevm : Sevm) (W : Devm) (L : List B256) (M : Mem) (p amount toWord token rho : B256)

/-- **WETH9's `transfer` CALL writes storage at the token only.** -/
theorem wethTransferCall_keepsStor (cg : Nat) {a : Adr} (ha : a ≠ (tokenMask token).toAdr) :
    (wethTransferCall sevm W L M p amount toWord token rho cg).state.getStor a = W.state.getStor a := by
  generalize hs : initSevm (xferMsg sevm W L M p amount toWord token rho cg
    ((xferSplit W L M p amount toWord token rho cg).1 + xferExt W L M p amount toWord token rho)
    (xferSplit W L M p amount toWord token rho cg).2) = s
  have ht : s.currentTarget = (tokenMask token).toAdr := by
    rw [← hs]; unfold xferMsg; rw [callChildMsg_zero]; rfl
  have hb : (initDevm (xferMsg sevm W L M p amount toWord token rho cg
      ((xferSplit W L M p amount toWord token rho cg).1 + xferExt W L M p amount toWord token rho)
      (xferSplit W L M p amount toWord token rho cg).2)).state = W.state := by
    unfold xferMsg
    rw [callChildMsg_zero, vcsm_state]
    unfold xferParent xferWarm xferPopped
    rw [callSpawnParent_state, addAccessedAddress_setMach_state]
  have ne : s.currentTarget ≠ a := by rw [ht]; exact Ne.symm ha
  unfold wethTransferCall wethTransferCallAt
  rw [hs, (callChildPost_facts_zero _ _ _ (B256.toNat 0) rfl).2.2.2.1, weth9TransferPost_state, ← hb]
  change Devm.getStor (xferTailPost s (Weth9.pB1 s _ s.caller) s.caller (Sevm.dataWord s 4).toAdr
    (Sevm.dataWord s 36)) a = Devm.getStor _ a
  unfold xferTailPost
  simp only [addLog_getStor', afterSstore_getStor_ne _ _ _ _ _ ne, afterSload_getStor]

end WethKeep

/-! ## WETH9's legs read the USDC results only off non-gas fields -/

/-- WETH9's post-callback query reads the USDC query's result only off non-gas fields. -/
theorem swapWethRead1_withGasLeft0 (sevm : Sevm) (d : Devm) (M : Mem) (n : Nat) (p : B256)
    (w : SwapCutWords) (ρ : B256) (R : List B256) (G : Nat) (d0 : Devm) (x : Nat) :
    swapWethRead1 sevm d M n p w ρ R G (d0.withGasLeft x) = swapWethRead1 sevm d M n p w ρ R G d0 := by
  unfold swapWethRead1 readNeed readCharge readUsed readSkel readStack readMem
  simp only [withGasLeft_returnData, wethBalanceCall_withGasLeft, wethBalanceSkel_withGasLeft,
    balAcc_withGasLeft, balExt_withGasLeft, balUsed_withGasLeft]

theorem leg1Skel_withGasLeft0 (sevm : Sevm) (b : Devm) (st : UniswapV2Pair.State) (d0 : Devm)
    (x : Nat) : leg1Skel sevm b st (d0.withGasLeft x) = leg1Skel sevm b st d0 := by
  unfold leg1Skel leg1World leg1Mem leg1Ptr
  by_cases h : swapAmount0Out sevm = 0
  · simp only [swapOptWorld, swapOptMem, swapOptPtr, h, ↓reduceIte]
  · simp only [swapOptWorld, swapOptMem, swapOptPtr, h, ↓reduceIte, withGasLeft_returnData]
    rfl

/-- WETH9's `transfer` leg reads the USDC transfer's result only off non-gas fields. -/
theorem swapWethLeg1_withGasLeft0 (sevm : Sevm) (b : Devm) (st : UniswapV2Pair.State) (d0 : Devm)
    (x cgC Gc : Nat) :
    swapWethLeg1 sevm b st (d0.withGasLeft x) cgC Gc = swapWethLeg1 sevm b st d0 cgC Gc := by
  unfold swapWethLeg1 leg1Need leg1Charge leg1Skel leg1World leg1Mem leg1Ptr
  simp only [swapFrontCallbackGas_withGasLeft0]
  by_cases h : swapAmount0Out sevm = 0
  · simp only [swapOptWorld, swapOptMem, swapOptPtr, h, ↓reduceIte]
  · simp only [swapOptWorld, swapOptMem, swapOptPtr, h, ↓reduceIte, withGasLeft_returnData]
    rfl

/-! ## USDC's runtimes across the frame's crossings -/

/-- **A certified runtime survives a successful compiled step** from a staged state over `b`
(code identity: nonempty code is never replaced). -/
theorem image_of_runCompiled (sem : CodeSem) {sevm : Sevm} {b d : Devm} {S : List B256} {M : Mem}
    {G : Nat} {n : Ninst} {a : Adr} (run : Ninst.RunCompiled sevm (St b S M G) n d)
    (h : some (b.state.getCode a).toList = sem.image) :
    some (d.state.getCode a).toList = sem.image := by
  have nonempty : ((St b S M G).getCode a).toList ≠ [] := sem.ne_nil h.symm
  change some (d.getCode a).toList = sem.image
  rw [runCompiled_codePreserve run a nonempty]
  exact h

/-- `UsdcInstalled` from the three runtimes and the implementation slot. -/
theorem usdcInstalled_of {P : Adr} {w w' : Jaune.State} (inst : Usdc.UsdcInstalled P w)
    (proxy : some (w'.getCode P).toList = Usdc.proxySem.image)
    (impl : some (w'.getCode Usdc.usdcImpl).toList = Usdc.implSem.image)
    (lib : some (w'.getCode Usdc.usdcLib).toList = Usdc.libSem.image)
    (slot : (w'.getStor P).get Usdc.implSlot = (w.getStor P).get Usdc.implSlot) :
    Usdc.UsdcInstalled P w' :=
  ⟨proxy, impl, lib, slot.trans inst.slot, inst.implApart, inst.libApart⟩

/-- **USDC's three runtimes across a compiled step** (the callback, a token's crossing): with the
implementation slot kept, USDC is still installed. -/
theorem usdcInstalled_of_runCompiled {P : Adr} {sevm : Sevm} {b d : Devm} {S : List B256}
    {M : Mem} {G : Nat} {n : Ninst} (run : Ninst.RunCompiled sevm (St b S M G) n d)
    (inst : Usdc.UsdcInstalled P b.state)
    (slot : (d.state.getStor P).get Usdc.implSlot = Usdc.usdcImpl.toB256) :
    Usdc.UsdcInstalled P d.state :=
  usdcInstalled_of inst (image_of_runCompiled _ run inst.proxy) (image_of_runCompiled _ run inst.impl)
    (image_of_runCompiled _ run inst.lib) (slot.trans inst.slot.symm)

/-! ## The pinned two-token callee environments (shared by the row and its finite twin) -/

/-- The front environment with both tokens pinned: the WETH9 one's fields minus `transfer0`
(§10c, verbatim). -/
structure SwapFrontEnvUW (sevm : Sevm) (b : Devm) (st : UniswapV2Pair.State) (d0 d1 dC : Devm)
    (cg0 cg1 cgC Gc : Nat) : Prop where
  callback : swapDataLength sevm ≠ 0 → SwapCallbackCallForward sevm
    (swapFrontTransferWorld sevm b d0 d1) (swapLocalsStack sevm st)
    (swapFrontTransferMem sevm d0 d1) (swapFrontPtr sevm d0 d1) (swapRecipientWord sevm)
    (swapAmount0Out sevm) (swapAmount1Out sevm) (swapDataLength sevm) (swapDataStart sevm) cgC Gc dC
  sentry : gCallStipend < swapFrontTransferGas sevm b d0 d1 cg0 cg1 cgC Gc +
    sstoreCost sevm (afterSload sevm b 12) 12 0

/-- The back environment with both reads pinned (§10c plus `room0`). -/
structure SwapBackCalleeEnvUW (sevm : Sevm) (d : Devm) (M : Mem) (n : Nat) (p : B256)
    (w : SwapCutWords) (ρ : B256) (R : List B256) (G : Nat) where
  d0 : Devm
  d1 : Devm
  callGas0 : Nat
  callGas1 : Nat
  read1 : (d1, callGas1) = swapWethRead1 sevm d M n p w ρ R G (usdcRead0Skel sevm d M n p w ρ R)
  read0 : (d0, callGas0) = swapUsdcRead0 sevm d M n p w ρ R G callGas1
  room0 : usdcBalNeed sevm d (read0Stack w ρ R) M p w.token0 ≤
    except64th (read0Need n p w callGas1 (usdcRead0Skel sevm d M n p w ρ R) +
      usdcBalUsed sevm d (read0Stack w ρ R) M p w.token0)
  sentries : SwapUpdateSentries sevm d1 (swapRequestSize (swapRequestSize n p) p) p w.reserve0
    w.reserve1 (swapBalanceWord d0.returnData) (swapBalanceWord d1.returnData)
    (swapEventRunGas G (swapSyncSize (swapRequestSize (swapRequestSize n p) p) p) p
      (swapUnlockCost sevm d1 w.reserve0 w.reserve1 (swapBalanceWord d0.returnData)
        (swapBalanceWord d1.returnData)
        (swapInWord (swapBalanceWord d0.returnData) w.reserve0 w.amount0Out)
        (swapInWord (swapBalanceWord d1.returnData) w.reserve1 w.amount1Out)
        w.amount0Out w.amount1Out w.recipient))
  unlock : gCallStipend < G + 26 + swapUnlockCost sevm d1 w.reserve0 w.reserve1
    (swapBalanceWord d0.returnData) (swapBalanceWord d1.returnData)
    (swapInWord (swapBalanceWord d0.returnData) w.reserve0 w.amount0Out)
    (swapInWord (swapBalanceWord d1.returnData) w.reserve1 w.amount1Out)
    w.amount0Out w.amount1Out w.recipient

section UW
variable {sevm : Sevm} {d : Devm} {M : Mem} {n : Nat} {p : B256} {w : SwapCutWords} {ρ : B256}
  {R : List B256} {G : Nat}

def SwapBackCalleeEnvUW.gas (env : SwapBackCalleeEnvUW sevm d M n p w ρ R G) : Nat :=
  env.callGas0 + 5 + swapRequestCharge d n p w.token0 72 + 16

def SwapBackCalleeEnvUW.post (env : SwapBackCalleeEnvUW sevm d M n p w ρ R G) : Devm :=
  afterSstore sevm (swapLoggedWorld sevm env.d1 w.reserve0 w.reserve1
    (swapBalanceWord env.d0.returnData) (swapBalanceWord env.d1.returnData)
    (swapInWord (swapBalanceWord env.d0.returnData) w.reserve0 w.amount0Out)
    (swapInWord (swapBalanceWord env.d1.returnData) w.reserve1 w.amount1Out)
    w.amount0Out w.amount1Out w.recipient) 12 1

def SwapBackCalleeEnvUW.memory (env : SwapBackCalleeEnvUW sevm d M n p w ρ R G) : Mem :=
  swapEventMemory (swapSyncMemory (swapBalanceReply (swapBalanceReply M p sevm.currentTarget
      env.d0.returnData) p sevm.currentTarget env.d1.returnData) p
      (updateFinalPackedWord sevm env.d1 w.reserve0 w.reserve1
        (swapBalanceWord env.d0.returnData) (swapBalanceWord env.d1.returnData)))
    p (swapInWord (swapBalanceWord env.d0.returnData) w.reserve0 w.amount0Out)
    (swapInWord (swapBalanceWord env.d1.returnData) w.reserve1 w.amount1Out)
    w.amount0Out w.amount1Out

end UW

end Blanc.Composition.UniswapV2PairUsdcWeth9
