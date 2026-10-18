import Blanc.Composition.UniswapV2PairUsdcWeth9LegsSkim

/-!
# Skim's callee environment with both tokens pinned (USDC = token0, WETH9 = token1; U9e)

`SkimCalleeUW` is `SkimForwardEnv` with all four token records removed: USDC's query and transfer
(`read0`, `leg0`, the transfer's call gas `gasT0`) and WETH9's (`read1`, `leg1`, `gasT1`).  WETH9's
pins read USDC's results only through the skeletons `skimUsdcRead0Skel` / `skimUsdcLeg0Skel`
(A17); `skimWethRead1_gasFree` and `skimWethLeg1_gasFree` turn them into the real ones.

`skimWethLeg1_of_kept` is `skimWethLeg1_of_read` for an explicit X transfer: instead of the X-leg
quiescence under HASH-T over X's child, it takes WETH9's code and the covered reserve1 word at X's
transfer result directly (USDC's transfer keeps both: `usdcTransferCall_keeps`).
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Lift.Usdc
  Blanc.Composition.UniswapV2PairWeth9Joint Blanc.Composition.UsdcLive Blanc.Composition.UsdcToken

/-- **Skim's callee environment with both tokens pinned** (USDC = token0, WETH9 = token1).  Pins
in binding order (A17): WETH9's `gasT1`, `read1`, `leg1` read USDC's results only through the
skeletons `skimUsdcRead0Skel` / `skimUsdcLeg0Skel` (free values) and the residual `g`; USDC's
`gasT0` reads WETH9's query gas `callGasQ1`, `read0` reads `callGasT0`, `leg0` reads `qd0` and
`callGasQ1`.  What stays: the lock sentries. -/
structure SkimCalleeUW (sevm : Sevm) (b : Devm) (g : Nat) where
  callGasT1 : Nat
  gasT1 : callGasT1 = skimLeg1Gas sevm b (skimUsdcRead0Skel sevm b)
    (skimUsdcLeg0Skel sevm b (skimUsdcRead0Skel sevm b)) g
  qd1 : Devm
  callGasQ1 : Nat
  read1 : (qd1, callGasQ1) = skimWethRead1 sevm b (skimUsdcRead0Skel sevm b)
    (skimUsdcLeg0Skel sevm b (skimUsdcRead0Skel sevm b)) callGasT1
  dt1 : Devm
  leg1 : dt1 = (skimWethLeg1 sevm b (skimUsdcRead0Skel sevm b)
    (skimUsdcLeg0Skel sevm b (skimUsdcRead0Skel sevm b)) qd1 g).1
  callGasT0 : Nat
  gasT0 : callGasT0 = skimUsdcLeg0Gas sevm b callGasQ1
  qd0 : Devm
  callGasQ0 : Nat
  read0 : (qd0, callGasQ0) = skimUsdcRead0 sevm b callGasT0
  dt0 : Devm
  leg0 : dt0 = (skimUsdcLeg0 sevm b qd0 callGasQ1).1
  sentry : gCallStipend < ((((callGasQ0 + 5) +
      sloadCost sevm (syncLockedWorld sevm b) 6 +
      sloadCost sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7 +
      sloadCost sevm (afterSload sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7) 8 +
      swapStoreCost 96 128 + swapStoreCost 160 132 +
      temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr + 186)) +
      sstoreCost sevm (afterSload sevm b 12) 12 0)
  sentryU : gCallStipend < (g + 11) + sstoreCost sevm dt1 12 1

section SkimEnv

variable {sevm : Sevm} {b : Devm} {g : Nat}

def SkimCalleeUW.gas (env : SkimCalleeUW sevm b g) : Nat :=
  (env.callGasQ0 + 5) +
      sstoreCost sevm (afterSload sevm b 12) 12 0 +
      sloadCost sevm (syncLockedWorld sevm b) 6 +
      sloadCost sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7 +
      sloadCost sevm (afterSload sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7) 8 +
      swapStoreCost 96 128 + swapStoreCost 160 132 +
      temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr + 193 +
      sloadCost sevm b 12 + 23 + 63 + 123 + 63

def SkimCalleeUW.post (env : SkimCalleeUW sevm b g) : Devm :=
  St (afterSstore sevm env.dt1 12 1) [0xbc25cf77]
      (swapTransferMemory
        (((skimRequestMemory
          (swapTransferMemory
            (balanceReplyMemory getterInitMemory sevm.currentTarget env.qd0.returnData)
            128 (Bytes.toB256 (env.qd0.returnData.take 32) - skimReserve0 sevm b)
            (skimToWord sevm) env.dt0.returnData)
          (swapMovedPointer 128 env.dt0.returnData) sevm.currentTarget).extends
          [((swapMovedPointer 128 env.dt0.returnData).toNat, 36),
            ((swapMovedPointer 128 env.dt0.returnData).toNat, 32)]).write
          (swapMovedPointer 128 env.dt0.returnData).toNat (env.qd1.returnData.take 32))
        (swapMovedPointer 128 env.dt0.returnData)
        (Bytes.toB256 (env.qd1.returnData.take 32) -
          skimReserve1Word (env.dt0.getStorVal sevm.currentTarget 8))
        (skimToWord sevm) env.dt1.returnData) g

def SkimCalleeUW.balance0 (env : SkimCalleeUW sevm b g) : B256 :=
  Bytes.toB256 (env.qd0.returnData.take 32)

def SkimCalleeUW.balance1 (env : SkimCalleeUW sevm b g) : B256 :=
  Bytes.toB256 (env.qd1.returnData.take 32)

/-- X's transfer `CALL`'s staged state (`SkimForwardEnv.firstCallPre`), as in the W0/W1 envs. -/
def SkimCalleeUW.firstCallPre (env : SkimCalleeUW sevm b g) : Devm :=
  St env.qd0 (env.callGasT0.toB256 ::
      (skimToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      0 :: (128 + 164) :: 68 :: (128 + 164) :: 0 :: (68 + (128 + 164)) ::
      (skimToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: (Bytes.toB256 (env.qd0.returnData.take 32) - skimReserve0 sevm b) ::
      skimToWord sevm :: skimToken0 sevm b :: 0x1a2b ::
      skimToken1 sevm b :: skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
    (safeTransfer_dynamicCallMemory
      (balanceReplyMemory getterInitMemory sevm.currentTarget env.qd0.returnData) 128
      (Bytes.toB256 (env.qd0.returnData.take 32) - skimReserve0 sevm b) (skimToWord sevm))
    env.callGasT0

/-- Trace-local HASH-T for the first transfer (`SkimForwardEnv.FirstCallFresh`): the generic Pair
row's own premise, kept as the predecessor's rows keep it (even with the leg pinned). -/
def SkimCalleeUW.FirstCallFresh (env : SkimCalleeUW sevm b g) (U : WriterKey → Prop) : Prop :=
  ∃ R : Exec.Deriv, Blanc.Lift.StepIn R sevm env.firstCallPre (.exec .call) env.dt0 ∧
    WriterFreshKeys U (pairTraceKeys sevm.currentTarget R)

/-- **USDC's gas sentries**: the query's and the transfer's call gases words, room for USDC's runs
under the 63/64 rule. -/
structure SkimCalleeUW.UsdcSentries (env : SkimCalleeUW sevm b g) : Prop where
  fitsRead : env.callGasQ0 < 2 ^ 256
  roomRead : usdcBalNeed sevm (skimCachedWorld sevm b) (skimRead0Stack sevm b) getterInitMemory 128
      (skimToken0 sevm b) ≤
    except64th (skimRead0Need sevm env.callGasT0 (skimUsdcRead0Skel sevm b) +
      usdcBalUsed sevm (skimCachedWorld sevm b) (skimRead0Stack sevm b) getterInitMemory 128
        (skimToken0 sevm b))
  fitsLeg : env.callGasT0 < 2 ^ 256
  roomLeg : skimUsdcLeg0Budget sevm b env.qd0 ≤
    except64th (skimUsdcLeg0Need sevm b env.qd0 env.callGasQ1 + skimUsdcLeg0Used sevm b env.qd0)

/-- **WETH9's gas sentries** (`SkimCalleeW1.WethSentries`, verbatim over the pinned fields). -/
structure SkimCalleeUW.WethSentries (env : SkimCalleeUW sevm b g) : Prop where
  fitsRead : env.callGasQ1 < 2 ^ 256
  roomRead : balUsed sevm (afterSload sevm env.dt0 8) (skimRead1Stack sevm b env.dt0)
      ((skimRead1Base sevm b env.qd0 env.dt0).read 64 32).2 (skimRead1Ptr env.dt0) (skimT1 sevm b) ≤
    except64th (skimRead1Need sevm b env.qd0 env.dt0 env.callGasT1
        (wethBalanceSkel sevm (afterSload sevm env.dt0 8) (skimRead1Stack sevm b env.dt0)
          ((skimRead1Base sevm b env.qd0 env.dt0).read 64 32).2 (skimRead1Ptr env.dt0)
          (skimT1 sevm b)) +
      balUsed sevm (afterSload sevm env.dt0 8) (skimRead1Stack sevm b env.dt0)
        ((skimRead1Base sevm b env.qd0 env.dt0).read 64 32).2 (skimRead1Ptr env.dt0) (skimT1 sevm b))
  fitsLeg : env.callGasT1 < 2 ^ 256
  roomLeg : skimLeg1Used sevm b env.qd0 env.dt0 env.qd1 + gCallStipend ≤
    except64th (skimLeg1Need sevm b env.qd0 env.dt0 env.qd1 g +
      skimLeg1Used sevm b env.qd0 env.dt0 env.qd1)

end SkimEnv

/-! ## WETH9's legs read X's results off their non-gas fields -/

theorem temporalAccountAccessBase_setMach (B : Devm) (a : Adr) (m : Mach) :
    temporalAccountAccessBase (B.setMach m) a = (temporalAccountAccessBase B a).setMach m := by
  show (if a ∈ B.accessedAddresses then B.setMach m else addAccessedAddress (B.setMach m) a) =
    (if a ∈ B.accessedAddresses then B else addAccessedAddress B a).setMach m
  by_cases h : a ∈ B.accessedAddresses
  · simp only [h, ite_true]
  · simp only [h, ite_false]
    rfl

theorem temporalAccountAccessBase_stateGas (B : Devm) (a : Adr) :
    (temporalAccountAccessBase B a).stateGas = B.stateGas := by
  unfold temporalAccountAccessBase
  split <;> rfl

theorem afterSload_stateGas (sevm : Sevm) (B : Devm) (k : B256) :
    (afterSload sevm B k).stateGas = B.stateGas := by
  unfold afterSload
  split <;> rfl

/-- WETH9's read leg reads its world's machine only off its state-gas meter. -/
theorem wethReadLeg_setMach (sevm : Sevm) (B : Devm) (S : List B256) (M : Mem) (p t : B256)
    (need : Devm → Nat) (m : Mach) (h : m.stateGas = B.stateGas) :
    wethReadLeg sevm (B.setMach m) S M p t need = wethReadLeg sevm B S M p t need := by
  have hp : ∀ g, balPopped sevm (B.setMach m) S M p t g = balPopped sevm B S M p t g := by
    intro g
    unfold balPopped
    rw [temporalAccountAccessBase_setMach]
    have e : ((temporalAccountAccessBase B (balTok t)).setMach m).stateGas =
        (temporalAccountAccessBase B (balTok t)).stateGas := by
      rw [temporalAccountAccessBase_stateGas]
      exact h
    rw [e]
    rfl
  have ha : balAcc (B.setMach m) t = balAcc B t := by
    unfold balAcc
    rw [temporalAccountAccessBase_setMach]
    rfl
  have hm : ∀ g k f, balMsg sevm (B.setMach m) S M p t g k f = balMsg sevm B S M p t g k f := by
    intro g k f
    unfold balMsg balParent balWarm
    rw [hp]
    rfl
  have hq : ∀ g k, balParent sevm (B.setMach m) S M p t g k = balParent sevm B S M p t g k := by
    intro g k
    unfold balParent balWarm
    rw [hp]
  have he : balExt sevm (B.setMach m) S M p t = balExt sevm B S M p t := by
    unfold balExt
    rw [hp]
  unfold wethReadLeg readLegGas wethBalanceCall wethBalanceCallAt wethBalanceSkel balSplit balUsed
  simp only [hm, hq, he, ha]

theorem skimWethRead1_gasFree (sevm : Sevm) (b qd0 dt0 : Devm) (x y callGasT1 : Nat) :
    skimWethRead1 sevm b (qd0.withGasLeft x) (dt0.withGasLeft y) callGasT1 =
      skimWethRead1 sevm b qd0 dt0 callGasT1 := by
  have hs : afterSload sevm (dt0.withGasLeft y) 8 =
      (afterSload sevm dt0 8).setMach { dt0.mach with gasLeft := y } :=
    afterSload_setMach
  unfold skimWethRead1
  rw [hs, wethReadLeg_setMach _ _ _ _ _ _ _ _ (by rw [afterSload_stateGas]; rfl)]
  rfl

theorem skimWethLeg1_gasFree (sevm : Sevm) (b qd0 dt0 qd1 : Devm) (x y g : Nat) :
    skimWethLeg1 sevm b (qd0.withGasLeft x) (dt0.withGasLeft y) qd1 g =
      skimWethLeg1 sevm b qd0 dt0 qd1 g := by
  have hm : skimLeg1Mem sevm b (qd0.withGasLeft x) (dt0.withGasLeft y) qd1 =
      skimLeg1Mem sevm b qd0 dt0 qd1 := rfl
  have hp : skimRead1Ptr (dt0.withGasLeft y) = skimRead1Ptr dt0 := rfl
  have ha : skimLeg1Amount sevm (dt0.withGasLeft y) qd1 = skimLeg1Amount sevm dt0 qd1 := rfl
  unfold skimWethLeg1 skimLeg1Need skimLeg1Charge skimLeg1Used skimLeg1Skel
  rw [hm, hp, ha]

/-! ## WETH9's legs after an explicit X transfer -/

/-- **Skim's WETH9 legs after the other token's transfer (WETH9 = token1), with X's effect on WETH9
given.**  As `skimWethLeg1_of_read`, but from X's transfer result `dt0` directly: WETH9's code there
and the reserve1 word Skim loads at most the Pair's WETH9 balance there.  Then, with `qd1` the read
leg `skimWethRead1`'s own result, the read meets `qenv1` and `skimWethLeg1` is the `tenv1` record. -/
theorem skimWethLeg1_of_kept {sevm : Sevm} {b qd0 dt0 : Devm} {callGasT0 G0 callGasT1 g : Nat}
    {weth : Adr} (fork : CoveredFork sevm.benvStat.fork) (nonstatic : sevm.isStatic = false)
    (depth : sevm.depth ≠ 0)
    (tenv0 : SwapTransferCallForward sevm qd0 (skimLegStack sevm b) (skimLegMem sevm qd0)
      (skimLegMem sevm qd0).size 128 (skimLegAmount sevm b qd0) (skimToWord sevm)
      (skimToken0 sevm b) 0x1a2b callGasT0 G0 dt0)
    (token1 : (skimToken1 sevm b).toAdr = weth)
    (codeDt0 : dt0.state.getCode weth = Weth9.code)
    (cover : skimReserve1Word (dt0.getStorVal sevm.currentTarget 8) ≤
      dt0.getStorVal weth (Weth9.balSlot sevm.currentTarget))
    (notPrecompile : sevm.benvStat.rules.isPrecomp weth = false)
    (fitsRead : (skimWethRead1 sevm b qd0 dt0 callGasT1).2 < 2 ^ 256)
    (roomRead : balUsed sevm (afterSload sevm dt0 8) (skimRead1Stack sevm b dt0)
        ((skimRead1Base sevm b qd0 dt0).read 64 32).2 (skimRead1Ptr dt0) (skimT1 sevm b) ≤
      except64th (skimRead1Need sevm b qd0 dt0 callGasT1 (wethBalanceSkel sevm (afterSload sevm dt0 8)
          (skimRead1Stack sevm b dt0) ((skimRead1Base sevm b qd0 dt0).read 64 32).2
          (skimRead1Ptr dt0) (skimT1 sevm b)) +
        balUsed sevm (afterSload sevm dt0 8) (skimRead1Stack sevm b dt0)
          ((skimRead1Base sevm b qd0 dt0).read 64 32).2 (skimRead1Ptr dt0) (skimT1 sevm b)))
    (fits : (skimWethLeg1 sevm b qd0 dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1 g).2 < 2 ^ 256)
    (room : skimLeg1Used sevm b qd0 dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1 + gCallStipend ≤
      except64th (skimLeg1Need sevm b qd0 dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1 g +
        skimLeg1Used sevm b qd0 dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1)) :
    (((afterSload sevm dt0 8).getCode (skimT1 sevm b).toAdr).size.toB256 ≠ 0 ∧
      SkimQueryEnv sevm (temporalAccountAccessBase (afterSload sevm dt0 8) (skimT1 sevm b).toAdr)
        (skimRequestMemory (skimRead1Base sevm b qd0 dt0) (skimRead1Ptr dt0) sevm.currentTarget)
        (skimRead1Ptr dt0) (skimT1 sevm b)
        (((skimRead1Ptr dt0) + 36) :: 0x70a08231 :: skimT1 sevm b :: skimRead1Stack sevm b dt0)
        (skimWethRead1 sevm b qd0 dt0 callGasT1).1 (skimWethRead1 sevm b qd0 dt0 callGasT1).2
        (callGasT1 + safeTransferPreCharge (((skimRequestMemory (skimRead1Base sevm b qd0 dt0)
            (skimRead1Ptr dt0) sevm.currentTarget).extends
            [((skimRead1Ptr dt0).toNat, 36), ((skimRead1Ptr dt0).toNat, 32)]).write
            (skimRead1Ptr dt0).toNat
            ((skimWethRead1 sevm b qd0 dt0 callGasT1).1.returnData.take 32)).size
          (skimRead1Ptr dt0) + 12 + 80)) ∧
    SwapTransferCallForward sevm (skimWethRead1 sevm b qd0 dt0 callGasT1).1 (skimLegStack sevm b)
      (skimLeg1Mem sevm b qd0 dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1)
      (skimLeg1Mem sevm b qd0 dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1).size
      (skimRead1Ptr dt0) (skimLeg1Amount sevm dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1)
      (skimToWord sevm) (skimToken1 sevm b) 0x1aca
      (skimWethLeg1 sevm b qd0 dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1 g).2
      (skimLeg1Next sevm g (skimWethLeg1 sevm b qd0 dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1 g).1)
      (skimWethLeg1 sevm b qd0 dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1 g).1 := by
  have sloadState : (afterSload sevm dt0 8).state = dt0.state := by
    unfold afterSload
    split <;> rfl
  -- the memory after X's transfer
  have req0 := balanceRequestMemory_ptr getterInitMemory_ptr sevm.currentTarget
  have hs1 : memExtSize 96 128 32 = 160 := by decide
  have hs2 : memExtSize 160 132 32 = 192 := by decide
  rw [hs1, hs2] at req0
  have reply0 := balanceReplyMemory_ptr qd0.returnData req0
  have memN0 : PtrMem 128 (skimLegMem sevm qd0).size (skimLegMem sevm qd0) := by
    unfold skimLegMem
    rw [reply0.size]
    exact reply0
  obtain ⟨⟨n', memT⟩, -, lowerT, widthT, -⟩ :=
    skimTransferLayout (k := 161) fork
      (by simp only [skimLegStack, List.length_cons, List.length_nil]; omega)
      memN0 skimReply0_sentinel (by decide) (by decide) (by decide) tenv0
  change 128 ≤ (skimRead1Ptr dt0).toNat at lowerT
  change (skimRead1Ptr dt0).toNat + 1024 < 2 ^ 256 at widthT
  -- the read
  have token1' : (skimT1 sevm b).toAdr = weth := by rw [skimT1_toAdr, token1]
  have sloadCode : (afterSload sevm dt0 8).state.getCode (skimT1 sevm b).toAdr = Weth9.code := by
    rw [sloadState, token1']
    exact codeDt0
  obtain ⟨code1, qenv1, reply⟩ := skimWethRead1_spec (callGasT1 := callGasT1) fork depth memT
    lowerT widthT sloadCode (by rw [token1']; exact notPrecompile) fitsRead roomRead
  refine ⟨⟨code1, qenv1⟩, ?_⟩
  -- the transfer
  have qd1State : (skimWethRead1 sevm b qd0 dt0 callGasT1).1.state = dt0.state := by
    unfold skimWethRead1
    rw [wethReadLeg_state, sloadState]
  have storage : (skimWethRead1 sevm b qd0 dt0 callGasT1).1.getStorVal weth
      (Weth9.balSlot sevm.currentTarget) =
      (afterSload sevm dt0 8).getStorVal weth (Weth9.balSlot sevm.currentTarget) := by
    unfold skimWethRead1
    rw [wethReadLeg_getStorVal]
  have sloadStor : (afterSload sevm dt0 8).getStorVal weth (Weth9.balSlot sevm.currentTarget) =
      dt0.getStorVal weth (Weth9.balSlot sevm.currentTarget) := by
    unfold Devm.getStorVal Devm.getAcct
    rw [sloadState]
  rw [token1'] at reply
  have balance := skim_amount_le_balance
    (reserve := skimReserve1Word (dt0.getStorVal sevm.currentTarget 8)) reply storage
    (by rw [sloadStor]; exact cover)
  rw [← token1] at balance notPrecompile codeDt0
  have wfMem : Mem.Wf (skimLeg1Mem sevm b qd0 dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1) := by
    have memT' : PtrMem (skimRead1Ptr dt0) n' (skimRead1Base sevm b qd0 dt0) := memT
    unfold skimLeg1Mem
    rw [skimRequestMemory_eq sevm.currentTarget memT' (by omega) widthT]
    exact (((memT'.wf.extend 64 32).write _ _).write _ _).extends _ |>.write _ _
  exact skimWethLeg1_spec fork nonstatic depth (by rw [qd1State]; exact codeDt0) notPrecompile
    wfMem lowerT (by omega) balance fits room

end Blanc.Composition.UniswapV2PairUsdcWeth9
