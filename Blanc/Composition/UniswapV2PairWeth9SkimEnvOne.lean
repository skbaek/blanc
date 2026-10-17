import Blanc.Composition.UniswapV2PairWeth9SkimLive
import Blanc.Composition.UniswapV2PairWeth9LegsSkim1
import Blanc.Composition.UniswapV2PairWeth9BurnWorldOne

/-!
# C4(b): Skim's callee environment with WETH9 = token1 (U8h)

`SkimForwardEnv` with WETH9's query (`code1`, `qenv1`) and transfer (`tenv1`) removed.  Their results
and call gases are pinned in order: `gasT1` fixes the transfer's call gas from the free values (on
the query's gas-free skeleton, `skimLeg1Gas`), `read` fixes the query's result and call gas from it
(`skimWethRead1`), and `leg` fixes the transfer's result (`skimWethLeg1`).  What stays: X = token0's
query and transfer records, and the lock sentries.

`skimFirstCall_reserve1` is `SkimForwardEnv.firstCall_keeps`'s reserve1 conjunct, stated over the
records it reads (X's query and transfer `CALL`s) instead of a whole environment, so it can feed the
WETH9 leg before the environment exists: under trace-local HASH-T over X's transfer child, that child
leaves the locked Pair's reserve1 word.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

/-! ## The transfer's call gas on the query's skeleton -/

/-- The gas-free skeleton of skim's WETH9 query result (token1 = WETH9). -/
def skimRead1Skel (sevm : Sevm) (b qd0 dt0 : Devm) : Devm :=
  wethBalanceSkel sevm (afterSload sevm dt0 8) (skimRead1Stack sevm b dt0)
    ((skimRead1Base sevm b qd0 dt0).read 64 32).2 (skimRead1Ptr dt0) (skimT1 sevm b)

theorem skimWethRead1_skel (sevm : Sevm) (b qd0 dt0 : Devm) (callGasT1 : Nat) :
    ∃ x, (skimWethRead1 sevm b qd0 dt0 callGasT1).1 = (skimRead1Skel sevm b qd0 dt0).withGasLeft x :=
  ⟨_, wethBalanceCallAt_eq _ _ _ _ _ _ _ _ _ _⟩

/-- The WETH9 transfer leg reads the query's result only off its non-gas fields. -/
theorem skimWethLeg1_withGasLeft (sevm : Sevm) (b qd0 dt0 d : Devm) (g x : Nat) :
    skimWethLeg1 sevm b qd0 dt0 (d.withGasLeft x) g = skimWethLeg1 sevm b qd0 dt0 d g := rfl

/-- **The WETH9 transfer's call gas**, fixed by WETH9's code on the query's skeleton, given the
residual `g`. -/
noncomputable def skimLeg1Gas (sevm : Sevm) (b qd0 dt0 : Devm) (g : Nat) : Nat :=
  (skimWethLeg1 sevm b qd0 dt0 (skimRead1Skel sevm b qd0 dt0) g).2

/-- The transfer leg over the query's result is the leg over its skeleton. -/
theorem skimWethLeg1_read (sevm : Sevm) (b qd0 dt0 : Devm) (callGasT1 g : Nat) :
    skimWethLeg1 sevm b qd0 dt0 (skimWethRead1 sevm b qd0 dt0 callGasT1).1 g =
      skimWethLeg1 sevm b qd0 dt0 (skimRead1Skel sevm b qd0 dt0) g := by
  obtain ⟨x, hx⟩ := skimWethRead1_skel sevm b qd0 dt0 callGasT1
  rw [hx, skimWethLeg1_withGasLeft]

/-! ## The environment -/

/-- The words under X's query's request words (`SkimForwardEnv.qenv0`). -/
def skimQuery0Stack (sevm : Sevm) (b : Devm) : List B256 :=
  164 :: 0x70a08231 :: skimToken0 sevm b :: skimReserve0 sevm b :: 0x1a26 ::
    skimToWord sevm :: skimToken0 sevm b :: 0x1a2b :: skimToken1 sevm b ::
    skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77]

/-- **Skim's callee environment with WETH9 as token1.**  Pins in binding order: `gasT1` (from the
free `qd0`, `dt0`), `read` (from `gasT1`'s value), `leg` (from `read`'s result). -/
structure SkimCalleeW1 (sevm : Sevm) (b : Devm) (g : Nat) where
  qd0 : Devm
  dt0 : Devm
  callGasQ0 : Nat
  callGasT0 : Nat
  callGasT1 : Nat
  gasT1 : callGasT1 = skimLeg1Gas sevm b qd0 dt0 g
  qd1 : Devm
  callGasQ1 : Nat
  read : (qd1, callGasQ1) = skimWethRead1 sevm b qd0 dt0 callGasT1
  dt1 : Devm
  leg : dt1 = (skimWethLeg1 sevm b qd0 dt0 qd1 g).1
  code0 : (((skimCachedWorld sevm b).getCode
      (skimToken0 sevm b).toAdr).size.toB256) ≠ 0
  sentry : gCallStipend < ((((callGasQ0 + 5) +
      sloadCost sevm (syncLockedWorld sevm b) 6 +
      sloadCost sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7 +
      sloadCost sevm (afterSload sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7) 8 +
      swapStoreCost 96 128 + swapStoreCost 160 132 +
      temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr + 186)) +
      sstoreCost sevm (afterSload sevm b 12) 12 0)
  sentryU : gCallStipend < (g + 11) + sstoreCost sevm dt1 12 1
  qenv0 : SkimQueryEnv sevm
      (temporalAccountAccessBase (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr)
      (balanceRequestMemory getterInitMemory sevm.currentTarget) 128
      (skimToken0 sevm b) (skimQuery0Stack sevm b)
      qd0 callGasQ0 (((callGasT0 +
        safeTransferPreCharge (balanceReplyMemory getterInitMemory sevm.currentTarget
          qd0.returnData).size 128 + 12)) + 80)
  tenv0 : SwapTransferCallForward sevm qd0
      (skimToken1 sevm b :: skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
      (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
      ((balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData).size)
      128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
      (skimToWord sevm) (skimToken0 sevm b) 0x1a2b callGasT0
      (((callGasQ1 + 5) +
        sloadCost sevm dt0 8 +
        swapStoreCost
          (swapTransferMemory
            (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
            128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
            (skimToWord sevm) dt0.returnData).size
          (swapMovedPointer 128 dt0.returnData).toNat +
        swapStoreCost
          (memExtSize
            (swapTransferMemory
              (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
              128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
              (skimToWord sevm) dt0.returnData).size
            (swapMovedPointer 128 dt0.returnData).toNat 32)
          ((swapMovedPointer 128 dt0.returnData) + 4).toNat +
        temporalAccountAccessCost (afterSload sevm dt0 8)
          ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
            skimToken1 sevm b)).toAdr + 171)) dt0

section W1

variable {sevm : Sevm} {b : Devm} {g : Nat}

/-- WETH9's query and transfer put back. -/
def SkimCalleeW1.toEnv (env : SkimCalleeW1 sevm b g)
    (code1 : ((((afterSload sevm env.dt0 8).getCode
      ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
        skimToken1 sevm b)).toAdr)).size.toB256) ≠ 0)
    (qenv1 : SkimQueryEnv sevm
      (temporalAccountAccessBase (afterSload sevm env.dt0 8)
        ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
          skimToken1 sevm b)).toAdr)
      (skimRequestMemory
        (swapTransferMemory
          (balanceReplyMemory getterInitMemory sevm.currentTarget env.qd0.returnData)
          128 (Bytes.toB256 (env.qd0.returnData.take 32) - skimReserve0 sevm b)
          (skimToWord sevm) env.dt0.returnData)
        (swapMovedPointer 128 env.dt0.returnData) sevm.currentTarget)
      (swapMovedPointer 128 env.dt0.returnData)
      (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
        skimToken1 sevm b)
      (((swapMovedPointer 128 env.dt0.returnData) + 36) :: 0x70a08231 ::
        (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
          skimToken1 sevm b) ::
        skimReserve1Word (env.dt0.getStorVal sevm.currentTarget 8) :: 0x1a26 ::
        skimToWord sevm :: skimToken1 sevm b :: 0x1aca :: skimToken1 sevm b ::
        skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
      env.qd1 env.callGasQ1 (((env.callGasT1 +
        safeTransferPreCharge (((skimRequestMemory
          (swapTransferMemory
            (balanceReplyMemory getterInitMemory sevm.currentTarget env.qd0.returnData)
            128 (Bytes.toB256 (env.qd0.returnData.take 32) - skimReserve0 sevm b)
            (skimToWord sevm) env.dt0.returnData)
          (swapMovedPointer 128 env.dt0.returnData) sevm.currentTarget).extends
          [((swapMovedPointer 128 env.dt0.returnData).toNat, 36),
            ((swapMovedPointer 128 env.dt0.returnData).toNat, 32)]).write
          (swapMovedPointer 128 env.dt0.returnData).toNat
          (env.qd1.returnData.take 32)).size
          (swapMovedPointer 128 env.dt0.returnData) + 12)) + 80))
    (tenv1 : SwapTransferCallForward sevm env.qd1
      (skimToken1 sevm b :: skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
      (((skimRequestMemory
        (swapTransferMemory
          (balanceReplyMemory getterInitMemory sevm.currentTarget env.qd0.returnData)
          128 (Bytes.toB256 (env.qd0.returnData.take 32) - skimReserve0 sevm b)
          (skimToWord sevm) env.dt0.returnData)
        (swapMovedPointer 128 env.dt0.returnData) sevm.currentTarget).extends
        [((swapMovedPointer 128 env.dt0.returnData).toNat, 36),
          ((swapMovedPointer 128 env.dt0.returnData).toNat, 32)]).write
        (swapMovedPointer 128 env.dt0.returnData).toNat (env.qd1.returnData.take 32))
      ((((skimRequestMemory
        (swapTransferMemory
          (balanceReplyMemory getterInitMemory sevm.currentTarget env.qd0.returnData)
          128 (Bytes.toB256 (env.qd0.returnData.take 32) - skimReserve0 sevm b)
          (skimToWord sevm) env.dt0.returnData)
        (swapMovedPointer 128 env.dt0.returnData) sevm.currentTarget).extends
        [((swapMovedPointer 128 env.dt0.returnData).toNat, 36),
          ((swapMovedPointer 128 env.dt0.returnData).toNat, 32)]).write
        (swapMovedPointer 128 env.dt0.returnData).toNat (env.qd1.returnData.take 32)).size)
      (swapMovedPointer 128 env.dt0.returnData)
      (Bytes.toB256 (env.qd1.returnData.take 32) -
        skimReserve1Word (env.dt0.getStorVal sevm.currentTarget 8))
      (skimToWord sevm) (skimToken1 sevm b) 0x1aca env.callGasT1 (g +
        sstoreCost sevm env.dt1 12 1 + 22) env.dt1) :
    SkimForwardEnv sevm b g :=
  { qd0 := env.qd0, dt0 := env.dt0, qd1 := env.qd1, dt1 := env.dt1, callGasQ0 := env.callGasQ0,
    callGasT0 := env.callGasT0, callGasQ1 := env.callGasQ1, callGasT1 := env.callGasT1,
    code0 := env.code0, sentry := env.sentry, sentryU := env.sentryU, qenv0 := env.qenv0,
    tenv0 := env.tenv0, code1 := code1, qenv1 := qenv1, tenv1 := tenv1 }

/-- X's query's staged state (`SkimQueryEnv.call` of `qenv0`). -/
def SkimCalleeW1.readPre (env : SkimCalleeW1 sevm b g) : Devm :=
  St (temporalAccountAccessBase (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr)
    (env.callGasQ0.toB256 :: skimToken0 sevm b :: 128 :: 36 :: 128 :: 32 :: skimQuery0Stack sevm b)
    (balanceRequestMemory getterInitMemory sevm.currentTarget) env.callGasQ0

/-- X's transfer `CALL`'s staged state (`SkimForwardEnv.firstCallPre`). -/
def SkimCalleeW1.firstCallPre (env : SkimCalleeW1 sevm b g) : Devm :=
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

/-- Trace-local HASH-T for X's transfer (`SkimForwardEnv.FirstCallFresh`). -/
def SkimCalleeW1.FirstCallFresh (env : SkimCalleeW1 sevm b g) (U : WriterKey → Prop) : Prop :=
  ∃ R : Exec.Deriv, Blanc.Lift.StepIn R sevm env.firstCallPre (.exec .call) env.dt0 ∧
    WriterFreshKeys U (pairTraceKeys sevm.currentTarget R)

def SkimCalleeW1.gas (env : SkimCalleeW1 sevm b g) : Nat :=
  (env.callGasQ0 + 5) +
      sstoreCost sevm (afterSload sevm b 12) 12 0 +
      sloadCost sevm (syncLockedWorld sevm b) 6 +
      sloadCost sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7 +
      sloadCost sevm (afterSload sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7) 8 +
      swapStoreCost 96 128 + swapStoreCost 160 132 +
      temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr + 193 +
      sloadCost sevm b 12 + 23 + 63 + 123 + 63

def SkimCalleeW1.post (env : SkimCalleeW1 sevm b g) : Devm :=
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

def SkimCalleeW1.balance0 (env : SkimCalleeW1 sevm b g) : B256 :=
  Bytes.toB256 (env.qd0.returnData.take 32)

def SkimCalleeW1.balance1 (env : SkimCalleeW1 sevm b g) : B256 :=
  Bytes.toB256 (env.qd1.returnData.take 32)

end W1

/-! ## X's transfer keeps reserve1 -/

private theorem tAAB_getStor' (base : Devm) (a x : Adr) :
    Devm.getStor (temporalAccountAccessBase base a) x = Devm.getStor base x := by
  unfold temporalAccountAccessBase
  split <;> rfl

private theorem tAAB_getCode' (base : Devm) (a x : Adr) :
    (temporalAccountAccessBase base a).getCode x = base.getCode x := by
  unfold temporalAccountAccessBase
  split <;> rfl

private theorem St_getCode_eq' (x : Devm) (S : List B256) (M : Mem) (g : Nat) (a : Adr) :
    (St x S M g).getCode a = x.getCode a := rfl

/-- X's query leaves the cached world's Pair storage: the lock word written, nothing else. -/
theorem skimQuery_world {sevm : Sevm} {b qd0 : Devm} {S : List B256} {M : Mem} {G : Nat}
    {g t ii is oi os : B256} (fork : CoveredFork sevm.benvStat.fork)
    (call : Ninst.RunCompiled sevm (St (temporalAccountAccessBase (skimCachedWorld sevm b)
      (skimToken0 sevm b).toAdr) (g :: t :: ii :: is :: oi :: os :: S) M G) (.exec .staticcall) qd0) :
    ∀ a, Devm.getStor qd0 a = Devm.getStor (syncLockedWorld sevm b) a := by
  intro a
  rw [compiled_staticcall_stor fork call, tAAB_getStor']
  unfold skimCachedWorld
  rw [afterSload_getStor, afterSload_getStor, afterSload_getStor]

/-- **X's transfer leaves the locked Pair's reserve1** (`SkimForwardEnv.firstCall_keeps`'s
reserve1 conjunct over the two records it reads).  At a non-static skim frame whose storage
represents `current.state` and whose account holds the Pair code, under trace-local HASH-T over X's
transfer child against a separated universe holding the representation's rows. -/
theorem skimFirstCall_reserve1 {K U : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b : Devm} {g : Nat} (env : SkimCalleeW1 sevm b g)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (fork : CoveredFork sevm.benvStat.fork) (nonstatic : sevm.isStatic = false)
    (fresh : env.FirstCallFresh U) :
    reserve1Read (env.dt0.getStorVal sevm.currentTarget 8) =
      reserve1Read (env.qd0.getStorVal sevm.currentTarget 8) := by
  obtain ⟨R, call, keysFresh⟩ := fresh
  let pair := sevm.currentTarget
  let V := WriterExtend U (pairTraceKeys pair R)
  have injV : WriterInj V := inj.extend keysFresh
  have apartV : WriterApart V := apart.extend keysFresh
  have good : ∀ F ∈ Exec.rawFrameRoots R.exc, F.sevm.currentTarget = pair → LockedGood V F := by
    intro F member target F' inner same k touched
    exact Or.inr (List.mem_flatMap.mpr ⟨F', Exec.rawFrameRoots_trans member inner,
      by rw [ite_eq_left (same.trans target)]; exact touched⟩)
  have supply := lockedPairSupply injV apartV sem image pair
  have repCongr : ∀ st (s s' : Stor), (∀ k, s'.get k = s.get k) →
      LockedRep V st s → LockedRep V st s' := fun _ _ _ same r => LockedRep.congr same r
  have world : Devm.getStor env.qd0 pair = (Devm.getStor b pair).set 12 0 := by
    rw [skimQuery_world fork env.qenv0.call]
    unfold syncLockedWorld
    rw [afterSstore_getStor_self, afterSload_getStor]
  have cachedCode : (temporalAccountAccessBase (skimCachedWorld sevm b)
      (skimToken0 sevm b).toAdr).getCode pair = b.getCode pair := by
    rw [tAAB_getCode']
    unfold skimCachedWorld syncLockedWorld
    rw [afterSload_getCode, afterSload_getCode, afterSload_getCode, afterSstore_getCode,
      afterSload_getCode]
  have codeQ : env.qd0.getCode pair = b.getCode pair := by
    obtain ⟨xl, filled, steps⟩ := env.qenv0.call
    have slot : Xlot.Rel Devm.CodePreserve xl := by
      rcases xl with _ | ⟨evm, raw⟩
      · trivial
      · obtain ⟨childRun⟩ := filled
        cases raw <;> exact Exec.preserves_getCode childRun
    have preserve := Ninst.codePreserve_effectRec (.exec .staticcall) slot (steps 0)
    have nonempty := fun h => preserve pair h
    rw [St_getCode_eq'] at nonempty
    have nonempty' : ((temporalAccountAccessBase (skimCachedWorld sevm b)
        (skimToken0 sevm b).toAdr).getCode pair).toList ≠ [] := by
      rw [cachedCode]
      intro empty
      exact sem.ne_nil (installed.symm.trans (congrArg some empty)) rfl
    have kept := nonempty nonempty'
    exact kept.trans cachedCode
  let ctx := writerContext sevm []
  let frame1 := (skimSourceLockedFrame current ctx (skimRecipient sevm)).beginResume
    (skimRequest0 current ctx)
  let request1 := skimRequest1 current (skimRecipient sevm) 0
  have mutable1 : externalStatic frame1 request1 = false := by
    unfold externalStatic
    rw [show frame1.context.isStatic = sevm.isStatic from rfl, nonstatic]
    rfl
  have lockRep := rep.mint_lock_store
  obtain ⟨turns1, c1, _, _, turns1Exact, _, rep1, _, _, _⟩ :=
    mutable_call_turns (frame := frame1) (request := request1) supply repCongr sem image call
      (Or.inl rfl) rfl mutable1
      (by
        change some (env.qd0.getCode pair).toList = sem.image
        rw [codeQ]
        exact installed)
      ⟨K, fun k t => Or.inl (sub k t),
        by change WriterRep K (Devm.getStor env.qd0 pair) _; rw [world]; exact lockRep, rfl⟩
      rfl fork good
  obtain ⟨_, _, wrep1, _⟩ := rep1
  have core := driveTurns_locked_core ((mutableTranscript turns1 .done).work + 1) frame1 request1
    0 (mutableTranscript turns1 .done) rfl
  rw [ExactTurns.realizes turns1Exact _ (Nat.le_refl _)] at core
  change c1.state.economicCore = ({ current.state with unlocked := 0 } : UniswapV2Pair.State).economicCore
    at core
  simp only [State.economicCore, Prod.mk.injEq] at core
  obtain ⟨-, ⟨-, reserve1⟩, -⟩ := core
  have after := wrep1.fixed
  have before := lockRep.fixed
  rw [← world] at before
  obtain ⟨-, -, -, -, -, -, a8r1, -⟩ := after
  obtain ⟨-, -, -, -, -, -, b8r1, -⟩ := before
  exact a8r1.trans ((congrArg (fun r : Fin (2 ^ 112) => Nat.toB256 r.val) reserve1).trans b8r1.symm)

end Blanc.Composition.UniswapV2PairWeth9Joint
