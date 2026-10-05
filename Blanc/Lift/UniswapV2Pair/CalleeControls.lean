import Blanc.Lift.RevertingCallee
import Blanc.Lift.UniswapV2Pair.SyncWalk
import Blanc.Lift.UniswapV2Pair.SkimSecondWalk
import Blanc.Lift.UniswapV2Pair.MintPrefixWalk

/-!
# U6 callee-premise controls: a failing token defeats liveness

Gas-exact liveness (goal row U6) must carry a callee premise. These controls show why, at
pc-zero EVM altitude and universally over raw runs: when the Pair's `token0` slot names an
account whose installed code is `revertingCode` (`PUSH0 PUSH0 REVERT`) and which is not a
precompile, there is NO successful raw run of `sync`, `skim` or `mint`, whatever the gas,
calldata or remaining state.

Each entry's first external observation is the `STATICCALL balanceOf(pair)` to `token0`. The
existing raw inverses (`sync_raw_inv`/`syncCallee_inv`, `skim_raw_inv`, the mint pc-zero
chain into `mintBalancePrefix_inv`) retain, for every successful run, the authentic
`StaticAnswered` witness of that child; `not_staticAnswered_of_reverting` refutes it.

Hence a liveness theorem with no callee premise — "every model-accepted `sync`/`skim`/`mint`
at a reachable state has a successful raw run" — is false at any reachable state whose
`token0` holds such code. These are controls, not an instantiation of the original host's
liveness theorem.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The `token0` address the Pair reads after its lock write is the entry slot's. -/
private theorem lockedToken0 {sevm : Sevm} {b : Devm} {tok : Adr}
    (token0 : (b.getStorVal sevm.currentTarget 6).toAdr = tok) :
    ((syncLockedWorld sevm b).getStorVal sevm.currentTarget 6).toAdr.toB256.toAdr = tok := by
  rw [toAdr_toB256]
  change ((Devm.getStor (afterSstore sevm (afterSload sevm b 12) 12 0)
    sevm.currentTarget).get 6).toAdr = tok
  rw [afterSstore_getStor_self, Stor.get_set_ne _ (by decide : (12 : B256) ≠ 6),
    afterSload_getStor]
  exact token0

/-- Account warming keeps every installed code. -/
private theorem warm_getCode (base : Devm) (a t : Adr) :
    (temporalAccountAccessBase base a).getCode t = base.getCode t := by
  unfold Devm.getCode Devm.getAcct
  rw [temporalAccountAccessBase_state]

/-- **U6 control (sync).** With a reverting, non-precompile `token0`, no raw pc-zero `sync`
run succeeds. -/
theorem sync_no_success_of_reverting_token0 {sevm : Sevm} {b post : Devm} {G : Nat} {tok : Adr}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (token0 : (b.getStorVal sevm.currentTarget 6).toAdr = tok)
    (tokenCode : b.getCode tok = revertingCode)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp tok)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) : False := by
  obtain ⟨_, _, _, _, _, callee, _⟩ := sync_raw_inv codeEq fork selector run
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, answered, _⟩ :=
    syncCallee_inv fork getterInitMemory_ptr callee
  unfold syncFirstToken at answered
  rw [lockedToken0 token0] at answered
  refine not_staticAnswered_of_reverting ?_ notPrecompile answered
  unfold syncFirstWorld syncLockedWorld
  rw [warm_getCode, afterSload_getCode, afterSstore_getCode, afterSload_getCode]
  exact tokenCode

/-- **U6 control (skim).** With a reverting, non-precompile `token0`, no raw pc-zero `skim`
run succeeds: its `balanceOf` query to `token0`, ahead of the transfer CALL, cannot answer. -/
theorem skim_no_success_of_reverting_token0 {sevm : Sevm} {b post : Devm} {G : Nat} {tok : Adr}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (token0 : (b.getStorVal sevm.currentTarget 6).toAdr = tok)
    (tokenCode : b.getCode tok = revertingCode)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp tok)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) : False := by
  obtain ⟨_, _, _, _, first⟩ := skim_raw_inv codeEq fork selector run
  unfold SkimFirstFacts at first
  obtain ⟨_, _, _, _, _, _, _, _, _, _, answered, _⟩ := first
  unfold skimToken0 at answered
  rw [lockedToken0 token0] at answered
  refine not_staticAnswered_of_reverting ?_ notPrecompile answered
  unfold skimCachedWorld syncLockedWorld
  rw [warm_getCode, afterSload_getCode, afterSload_getCode, afterSload_getCode,
    afterSstore_getCode, afterSload_getCode]
  exact tokenCode

/-- **U6 control (mint).** With a reverting, non-precompile `token0`, no raw pc-zero `mint`
run succeeds. -/
theorem mint_no_success_of_reverting_token0 {sevm : Sevm} {b post : Devm} {G : Nat} {tok : Adr}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (token0 : (b.getStorVal sevm.currentTarget 6).toAdr = tok)
    (tokenCode : b.getCode tok = revertingCode)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp tok)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) : False := by
  obtain ⟨f, entry, run'⟩ := lift_sound_in cert_check codeEq fork run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨_, _, _, guarded⟩ := syncGuards_inv run'
  obtain ⟨_, h⟩ := mintSelector_inv selector (SFunc.runP_iff_runCutP_nil.mp guarded)
  obtain ⟨_, _, _, callee, _⟩ := mintAbi_inv h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, answered, _⟩ :=
    mintBalancePrefix_inv fork getterInitMemory_ptr (SFunc.runP_iff_runCutP_nil.mp callee)
  have slot : ((afterSload sevm (mintLockedWorld sevm b) 8).getStorVal sevm.currentTarget
      6).toAdr.toB256.toAdr = tok := by
    rw [toAdr_toB256]
    change ((Devm.getStor (afterSload sevm (afterSstore sevm (afterSload sevm b 12) 12 0) 8)
      sevm.currentTarget).get 6).toAdr = tok
    rw [afterSload_getStor, afterSstore_getStor_self,
      Stor.get_set_ne _ (by decide : (12 : B256) ≠ 6), afterSload_getStor]
    exact token0
  rw [slot] at answered
  refine not_staticAnswered_of_reverting ?_ notPrecompile answered
  unfold mintLockedWorld
  rw [warm_getCode, afterSload_getCode, afterSload_getCode, afterSstore_getCode,
    afterSload_getCode]
  exact tokenCode

end Blanc.Lift.UniswapV2Pair
