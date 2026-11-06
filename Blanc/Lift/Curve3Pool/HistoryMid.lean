import Blanc.Lift.Curve3Pool.Safe
import Blanc.ExecutionHistoryInFrameEnv

/-!
# Curve 3pool: the committed history over historical forks, from trace-level premises

`History.lean` over a mid history inside a retained `HistFork` chain: the replay starts right after
one transaction of a block (the pool's creation, in the deployed form), and the readiness of the
identity precompile is derived from the full chain `full` whose raw frames contain the mid history's.

* `pool_mid_trace_admitted` — every pool frame of the mid history is admitted by `poolEntryAtH`;
* `PoolMidEnv` — the ENV premises, one bundle;
* `pool_mid_history` — the headline: the replay over exactly the settled non-static pool frames.

The premises keep the shape of `PoolTraceEnv`: the per-frame callback premise, and the trace-local
`parties`, `idEmpty`, `idNoAuthority`, `idNoFrame` and `sysNe`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc Blanc.ExecutionTrace

/-- The identity precompile is a precompile of every historical fork. -/
theorem pool_four_mem_precompilesH {f : Fork} (hf : HistFork f) :
    (4 : Adr) ∈ (Fork.ruleSet f).precompiles := by
  revert hf
  cases f <;> decide

/-- **The ENV premises of the pool's mid history**, at coins `cs` and token `tok`, inside the chain
`full` from `checkpoint`. -/
structure PoolMidEnv {cfg : ChainConfig} {checkpoint future : BlockChain} {start : Benv}
    (full : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (trace : MidHistoryTraceIn HistFork cfg start future) (pool : Adr) (cs : V3) (tok : Nat) :
    Prop where
  subset : trace.rawFrames ⊆ full.rawFrames
  callbacks : trace.FrameAdmitted pool
    (Exec.derivEntry fun D => PoolCallsKeep D ∧ PoolCoinCallsKeepToken D)
  parties : ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = pool →
    (∀ k : Fin 3, ¬ root.sevm.benvStat.rules.isPrecomp (adrOf (cs.get k))) ∧
      ¬ root.sevm.benvStat.rules.isPrecomp (adrOf tok)
  idEmpty : checkpoint.state.getCode 4 = ByteArray.empty
  idNoAuthority : full.NoAuthorityAt 4
  idNoFrame : ∀ root ∈ full.rawFrames, root.sevm.codeAddress = none →
    root.sevm.currentTarget ≠ 4
  sysNe : ∀ root ∈ full.systemRawFrames, root.sevm.currentTarget ≠ pool

/-- **Every pool frame of the mid history is admitted by `poolEntryAtH`.** -/
theorem pool_mid_trace_admitted {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {start : Benv} {cs : V3} {tok : Nat}
    {full : ConfiguredHistoryTraceIn HistFork cfg checkpoint future}
    {trace : MidHistoryTraceIn HistFork cfg start future}
    (env : PoolMidEnv full trace pool cs tok) :
    trace.FrameAdmitted pool (poolEntryAtH cs tok) := by
  have capabilities := BodyStageCapabilities.historical
  have callbacks := (trace.frameAdmitted_iff_rawFrames pool _).1 env.callbacks
  have ready := full.precompileReadyH capabilities (fun _ hf => pool_four_mem_precompilesH hf)
    env.idEmpty env.idNoAuthority env.idNoFrame
  have keep4 := full.childFrames_codeAt_keep capabilities env.idNoFrame
  apply (trace.frameAdmitted_iff_rawFrames pool _).2
  intro root member target
  have memberFull := env.subset member
  obtain ⟨hpc, hfork⟩ := trace.rootEntryIn root member
  have htx : root ∈ full.txRawFrames := by
    rcases full.rawFrames_system_or_tx root memberFull with hsys | htx
    · exact absurd target (env.sysNe root hsys)
    · exact htx
  obtain ⟨hnodeleg, hwarm⟩ := ready root htx
  obtain ⟨hcs, htk⟩ := env.parties root member target
  have hgas := full.gas_bound capabilities root memberFull
  refine ⟨trace.rawFrames_entered enteredCondition_fresh root member,
    trace.calldata_bound capabilities (fun _ hf => hf.dataNonZero_ge) root member, by omega,
    ⟨hnodeleg, hwarm, decide_eq_true (pool_four_mem_precompilesH hfork),
      hfork.stateGas_none⟩, hcs, htk, ?_⟩
  refine Exec.derivEntry_of_deriv hpc ⟨?_, ?_, keep4 root memberFull⟩
  · cases root with
    | mk pc sevm pre out run =>
      dsimp only at hpc
      subst hpc
      exact (callbacks _ member target out run).1
  · cases root with
    | mk pc sevm pre out run =>
      dsimp only at hpc
      subst hpc
      exact (callbacks _ member target out run).2

/-- **The pool model replays the committed mid history, over the historical forks.** From a mid
history's start with the runtime installed and the pool's storage at a `Checkpoint` of `s₀`, the
runtime stays installed and the outermost settled non-static pool frames, in trace order, are
authentic invocations replaying through `Model.step` from `s₀` to a state the future storage
abstracts at a `Checkpoint`, each entered at a `Checkpoint` of the state its prefix reaches. -/
theorem pool_mid_history {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {start : Benv} {s₀ : State}
    {full : ConfiguredHistoryTraceIn HistFork cfg checkpoint future}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (installed : some (start.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (start.state.getStor pool) s₀)
    (env : PoolMidEnv full trace pool s₀.coins s₀.token) :
    some (future.state.getCode pool).toList = poolSem.image ∧
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFramesMid pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧ PoolEntries s₀ invs ∧
      ∃ s, PoolRun s₀ invs s ∧ runPool s₀ invs = some s ∧
        Checkpoint (future.state.getStor pool) s ∧ s.coins = s₀.coins ∧ s.token = s₀.token := by
  obtain ⟨code, invs, obs, auth, ent, s, run, fold, hc, hcoins, htoken, -⟩ :=
    pool_mid_history_entries (poolParties_keeps s₀.coins s₀.token)
      (pool_frame_refines_atH s₀.coins s₀.token) trace installed initial ⟨rfl, rfl⟩
      (pool_mid_trace_admitted env)
  exact ⟨code, invs, obs, auth, ent, s, run, fold, hc, hcoins, htoken⟩

end Blanc.Lift.Curve3Pool
