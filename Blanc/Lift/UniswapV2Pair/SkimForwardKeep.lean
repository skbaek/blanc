import Blanc.Lift.UniswapV2Pair.SkimForwardAccept
import Blanc.Lift.UniswapV2Pair.LockedSupply
import Blanc.Lift.UniswapV2Pair.SkimSource

/-!
# Skim liveness: the first transfer keeps the lock-guarded Pair fields (derived)

`skim` re-reads the packed reserves (slot 8) after its first token transfer `CALL`, so its forward run
needs that `CALL` to leave reserve1 as it was. This module derives that fact instead of assuming it
(`SkimForwardEnv.firstCall_keeps`): while the `CALL` runs, the Pair is locked (slot 12 = 0, written
by the skim frame before the call); every Pair frame the callee enters and commits is one of the
lock-free entries (`lockedPairSupply`: mint, burn, swap, sync and skim cannot commit while locked,
the fallback reverts, every other entry writes only balance, allowance and nonce rows), and the
fold of `mutable_call_turns` carries the locked finite representation across the whole child,
whose model turns keep every lock-guarded field (`driveTurns_locked_core`). Failed and rolled-back
frames leave no write.

The only premise beyond the code, lock and representation facts is trace-local HASH-T:
`SkimForwardEnv.FirstCallFresh U`, the decoded mapping rows of the Pair frames that the actual
first transfer `CALL` enters are fresh against the separated universe `U`.

`SkimForwardEnv.run_of_model` is the skim forward run from the model's guards under that premise.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The decoded mapping rows of every raw frame of `root` whose storage owner is `pair` (the
rows its actual selector touches and the rows the static views it serves read). -/
def pairTraceKeys (pair : Adr) (root : Exec.Deriv) : List WriterKey :=
  (Exec.rawFrameRoots root.exc).flatMap fun F =>
    if F.sevm.currentTarget = pair then pairDecodedKeys F.sevm ++ staticViewDecodedKeys F.sevm
    else []

private theorem pairTraceKeys_contains {pair : Adr} {root F : Exec.Deriv}
    (member : F ∈ Exec.rawFrameRoots root.exc) (target : F.sevm.currentTarget = pair) :
    ∀ k ∈ pairDecodedKeys F.sevm ++ staticViewDecodedKeys F.sevm, k ∈ pairTraceKeys pair root :=
  fun k touched => List.mem_flatMap.mpr ⟨F, member, by rw [ite_eq_left target]; exact touched⟩

/-- The staged world of skim's first transfer `CALL` (the pre-state of `tenv0.call`). -/
def SkimForwardEnv.firstCallPre {sevm : Sevm} {b : Devm} {g : Nat}
    (env : SkimForwardEnv sevm b g) : Devm :=
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

-- `firstCallPre` is exactly the pre-state of the environment's own first transfer `CALL`.
example {sevm : Sevm} {b : Devm} {g : Nat} (env : SkimForwardEnv sevm b g) :
    Ninst.RunCompiled sevm env.firstCallPre (.exec .call) env.dt0 :=
  env.tenv0.call

/-- **Trace-local HASH-T for skim's first transfer.**  The first transfer `CALL` (from its actual
staged world to `dt0`) has a derivation `R` whose Pair frames' decoded mapping rows are fresh against
`U`. It constrains the hashes actually decoded by the Pair frames inside that one `CALL`, never all
keys of a shape, and says nothing about the callee's behaviour. -/
def SkimForwardEnv.FirstCallFresh {sevm : Sevm} {b : Devm} {g : Nat}
    (env : SkimForwardEnv sevm b g) (U : WriterKey → Prop) : Prop :=
  ∃ R : Exec.Deriv, Blanc.Lift.StepIn R sevm env.firstCallPre (.exec .call) env.dt0 ∧
    WriterFreshKeys U (pairTraceKeys sevm.currentTarget R)

private theorem St_getCode_eq (x : Devm) (S : List B256) (M : Mem) (g : Nat) (a : Adr) :
    (St x S M g).getCode a = x.getCode a := rfl

private theorem tAAB_getStor (base : Devm) (a x : Adr) :
    Devm.getStor (temporalAccountAccessBase base a) x = Devm.getStor base x := by
  unfold temporalAccountAccessBase
  split <;> rfl

private theorem tAAB_getCode (base : Devm) (a x : Adr) :
    (temporalAccountAccessBase base a).getCode x = base.getCode x := by
  unfold temporalAccountAccessBase
  split <;> rfl

/-- **The first skim transfer keeps the Pair's lock-guarded fields** (derived, not assumed).  At a
non-static skim frame whose storage represents `current.state` and whose account holds the Pair
code, the first transfer `CALL` leaves `totalSupply` (slot 0), the three packed reserve fields
(slot 8), both price accumulators (9, 10), `kLast` (11) and the lock (12) as they were at the `CALL`,
under trace-local HASH-T (`FirstCallFresh`) against a separated universe `U` containing the
representation's rows. -/
theorem SkimForwardEnv.firstCall_keeps {K U : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b : Devm} {g : Nat} (env : SkimForwardEnv sevm b g)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (fork : CoveredFork sevm.benvStat.fork) (nonstatic : sevm.isStatic = false)
    (fresh : env.FirstCallFresh U) :
    let pair := sevm.currentTarget
    env.dt0.getStorVal pair 0 = env.qd0.getStorVal pair 0 ∧
    reserve0Read (env.dt0.getStorVal pair 8) = reserve0Read (env.qd0.getStorVal pair 8) ∧
    reserve1Read (env.dt0.getStorVal pair 8) = reserve1Read (env.qd0.getStorVal pair 8) ∧
    reserveTimestampRead (env.dt0.getStorVal pair 8) =
      reserveTimestampRead (env.qd0.getStorVal pair 8) ∧
    env.dt0.getStorVal pair 9 = env.qd0.getStorVal pair 9 ∧
    env.dt0.getStorVal pair 10 = env.qd0.getStorVal pair 10 ∧
    env.dt0.getStorVal pair 11 = env.qd0.getStorVal pair 11 ∧
    env.dt0.getStorVal pair 12 = env.qd0.getStorVal pair 12 := by
  intro pair
  obtain ⟨R, call, keysFresh⟩ := fresh
  let V := WriterExtend U (pairTraceKeys pair R)
  have injV : WriterInj V := inj.extend keysFresh
  have apartV : WriterApart V := apart.extend keysFresh
  have good : ∀ F ∈ Exec.rawFrameRoots R.exc, F.sevm.currentTarget = pair → LockedGood V F := by
    intro F member target F' inner same k touched
    exact Or.inr (pairTraceKeys_contains (Exec.rawFrameRoots_trans member inner)
      (same.trans target) k touched)
  have supply := lockedPairSupply injV apartV sem image pair
  have repCongr : ∀ st (s s' : Stor), (∀ k, s'.get k = s.get k) →
      LockedRep V st s → LockedRep V st s' := fun _ _ _ same r => LockedRep.congr same r
  -- the staged world: the query left the cached world's storage and code
  have queried := compiled_staticcall_stor fork env.qenv0.call
  have world : Devm.getStor env.qd0 pair = (Devm.getStor b pair).set 12 0 := by
    rw [queried, tAAB_getStor]
    unfold skimCachedWorld syncLockedWorld
    rw [afterSload_getStor, afterSload_getStor, afterSload_getStor, afterSstore_getStor_self,
      afterSload_getStor]
  have cachedCode : (temporalAccountAccessBase (skimCachedWorld sevm b)
      (skimToken0 sevm b).toAdr).getCode pair = b.getCode pair := by
    rw [tAAB_getCode]
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
    rw [St_getCode_eq] at nonempty
    have nonempty' : ((temporalAccountAccessBase (skimCachedWorld sevm b)
        (skimToken0 sevm b).toAdr).getCode pair).toList ≠ [] := by
      rw [cachedCode]
      intro empty
      exact sem.ne_nil (installed.symm.trans (congrArg some empty)) rfl
    have kept := nonempty nonempty'
    exact kept.trans cachedCode
  -- the source frame at the call: locked, after the first query
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
      (by change some (env.qd0.getCode pair).toList = sem.image; rw [codeQ]; exact installed)
      ⟨K, fun k t => Or.inl (sub k t),
        by change WriterRep K (Devm.getStor env.qd0 pair) _; rw [world]; exact lockRep, rfl⟩
      rfl fork good
  obtain ⟨_, _, wrep1, _⟩ := rep1
  -- the model turns keep the locked core
  have core := driveTurns_locked_core ((mutableTranscript turns1 .done).work + 1) frame1 request1
    0 (mutableTranscript turns1 .done) rfl
  rw [ExactTurns.realizes turns1Exact _ (Nat.le_refl _)] at core
  change c1.state.economicCore = ({ current.state with unlocked := 0 } : State).economicCore
    at core
  simp only [State.economicCore, Prod.mk.injEq] at core
  obtain ⟨supply1, ⟨reserve0, reserve1⟩, stamp, ⟨price0, price1⟩, kLast, unlocked⟩ := core
  have after := wrep1.fixed
  have before := lockRep.fixed
  rw [← world] at before
  obtain ⟨a0, -, -, -, -, a8r0, a8r1, a8t, a9, a10, a11, a12⟩ := after
  obtain ⟨b0, -, -, -, -, b8r0, b8r1, b8t, b9, b10, b11, b12⟩ := before
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact a0.trans (supply1.trans b0.symm)
  · exact a8r0.trans ((congrArg (fun r : Fin (2 ^ 112) => Nat.toB256 r.val) reserve0).trans b8r0.symm)
  · exact a8r1.trans ((congrArg (fun r : Fin (2 ^ 112) => Nat.toB256 r.val) reserve1).trans b8r1.symm)
  · exact a8t.trans ((congrArg UInt32.toB256 stamp).trans b8t.symm)
  · exact a9.trans (price0.trans b9.symm)
  · exact a10.trans (price1.trans b10.symm)
  · exact a11.trans (kLast.trans b11.symm)
  · exact a12.trans (unlocked.trans b12.symm)

/-- **The skim forward run from the model.**  At a frame whose storage represents `current.state`,
the model's skim guards at the callee environment's actual answers give the pc-zero run of the
original bytes from `skim_bytecode_forward_consumes`, at gas `env.gas` and halting in `env.post`,
under trace-local HASH-T for the first transfer (`FirstCallFresh U`, `U` a separated universe
containing the representation's rows). The first transfer's preservation of reserve1 is
`firstCall_keeps`; the `_safeTransfer` helper is `safeTransfer_dynamic_forward`. -/
theorem SkimForwardEnv.run_of_model {K U : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b : Devm} {g : Nat} (env : SkimForwardEnv sevm b g)
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (abi : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (fresh : env.FirstCallFresh U)
    (conditions : SkimModelConditions current.state (writerContext sevm []) env.balance0
      env.balance1) :
    Nonempty (Exec 0 sevm (St b [] Mem.empty env.gas) (.ok env.post)) := by
  obtain ⟨_, nonstatic, unlocked, cover0, cover1⟩ := conditions
  have nonstaticSevm : sevm.isStatic = false := nonstatic
  have slots : ReserveSlotMatches current.state sevm b :=
    ⟨rep.fixed.2.2.2.2.2.1, rep.fixed.2.2.2.2.2.2.1, rep.fixed.2.2.2.2.2.2.2.1⟩
  obtain ⟨_, _, reserve0⟩ := skimCache_source slots rep.fixed.2.2.2.1 rep.fixed.2.2.2.2.1
  have nat0 : (Nat.toB256 current.state.reserve0.val).toNat = current.state.reserve0.val :=
    B256.toNat_toB256_of_lt (lt_trans current.state.reserve0.isLt (by decide))
  have nat1 : (Nat.toB256 current.state.reserve1.val).toNat = current.state.reserve1.val :=
    B256.toNat_toB256_of_lt (lt_trans current.state.reserve1.isLt (by decide))
  have wordCover0 : skimReserve0 sevm b ≤ Bytes.toB256 (env.qd0.returnData.take 32) := by
    rw [reserve0, B256.le_iff_toNat_le_toNat, nat0]
    exact cover0
  have wordCover1 : skimReserve1Word (env.dt0.getStorVal sevm.currentTarget 8) ≤
      Bytes.toB256 (env.qd1.returnData.take 32) := by
    have queried := compiled_staticcall_stor fork env.qenv0.call
    have staged : env.qd0.getStorVal sevm.currentTarget 8 = b.getStorVal sevm.currentTarget 8 :=
      calc env.qd0.getStorVal sevm.currentTarget 8
          = (Devm.getStor env.qd0 sevm.currentTarget).get 8 := rfl
        _ = (Devm.getStor (skimCachedWorld sevm b) sevm.currentTarget).get 8 := by
          rw [queried, tAAB_getStor]
        _ = b.getStorVal sevm.currentTarget 8 := by
          unfold skimCachedWorld syncLockedWorld
          rw [afterSload_getStor, afterSload_getStor, afterSload_getStor, afterSstore_getStor_self,
            Stor.get_set_ne _ (by decide : (12 : B256) ≠ 8), afterSload_getStor]
          rfl
    have kept := (env.firstCall_keeps rep inj apart sub sem image installed fork nonstaticSevm
      fresh).2.2.1
    rw [skimReserve1Word_eq, kept, staged, slots.2.1, B256.le_iff_toNat_le_toNat, nat1]
    exact cover1
  obtain ⟨run, _⟩ := skim_bytecode_forward_consumes invocation rep sem image installed
    freshOutput codeEq fork value size selector abi unlocked nonstatic env.code0
    env.sentry env.sentryU env.qenv0 env.tenv0 wordCover0 env.code1 env.qenv1 env.tenv1
    wordCover1
  exact ⟨run⟩

end Blanc.Lift.UniswapV2Pair
