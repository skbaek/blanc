import Blanc.Lift.UniswapV2Pair.SkimForwardKeep
import Blanc.Lift.AccountAccessState

/-!
# The skim forward run when the first transfer's effect on reserve1 is known

`SkimForwardEnv.run_of_model` derives that skim's first token transfer `CALL` keeps the Pair's
reserve1 word (`firstCall_keeps`) under trace-local HASH-T for that call (`FirstCallFresh`).  When
the first token's transfer is an explicit run of known code whose effect on other accounts' storage
is already proved (for example a token whose `transfer` writes only its own storage), that fact is
available directly, and no trace-local premise is needed.  `SkimForwardEnv.run_of_kept` is
`run_of_model` from that fact.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- **The skim forward run from the model, the first transfer's reserve1 given.**  As
`SkimForwardEnv.run_of_model`, with the first transfer's preservation of the packed reserve1 field
taken as `kept` instead of derived under `FirstCallFresh`. -/
theorem SkimForwardEnv.run_of_kept {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b : Devm} {g : Nat} (env : SkimForwardEnv sevm b g)
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (abi : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (kept : reserve1Read (env.dt0.getStorVal sevm.currentTarget 8) =
      reserve1Read (env.qd0.getStorVal sevm.currentTarget 8))
    (conditions : SkimModelConditions current.state (writerContext sevm []) env.balance0
      env.balance1) :
    Nonempty (Exec 0 sevm (St b [] Mem.empty env.gas) (.ok env.post)) := by
  obtain ⟨_, nonstatic, unlocked, cover0, cover1⟩ := conditions
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
          rw [queried, temporalAccountAccessBase_getStor]
        _ = b.getStorVal sevm.currentTarget 8 := by
          unfold skimCachedWorld syncLockedWorld
          rw [afterSload_getStor, afterSload_getStor, afterSload_getStor, afterSstore_getStor_self,
            Stor.get_set_ne _ (by decide : (12 : B256) ≠ 8), afterSload_getStor]
          rfl
    rw [skimReserve1Word_eq, kept, staged, slots.2.1, B256.le_iff_toNat_le_toNat, nat1]
    exact cover1
  obtain ⟨run, _⟩ := skim_bytecode_forward_consumes invocation rep sem image installed
    freshOutput codeEq fork value size selector abi unlocked nonstatic env.code0
    env.sentry env.sentryU env.qenv0 env.tenv0 wordCover0 env.code1 env.qenv1 env.tenv1
    wordCover1
  exact ⟨run⟩

end Blanc.Lift.UniswapV2Pair
