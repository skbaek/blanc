import Blanc.Lift.Curve3Pool.HistoryMid

/-!
# The pool's mid history asking its keep premise only where the replay uses it

`PoolMidEnv.callbacks` asks every entered frame at the pool, of every outcome and at any storage, for
`PoolCallsKeep ∧ PoolCoinCallsKeepToken`. The replay reads it only at the frames it refines: committed,
non-static, entered at a `Checkpoint` of a state with the replay's coins and token (`PoolFrameRefinesInH`).

* `PoolKeepAt`: that premise, at exactly those frames. Its storage hypotheses come from the replay, so a
  discharge that needs the coins' addresses from the pool's storage is not circular;
* `pool_mid_history_at`: `pool_mid_history` under it.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc Blanc.ExecutionTrace

/-- The keep premises at the frames the replay refines. -/
def PoolKeepAt (cs : V3) (tok : Nat) (sevm : Sevm) (pre : Devm) : Prop :=
  ∀ (post : Devm) (exc : Exec 0 sevm pre (.ok post)) (s : State),
    sevm.isStatic = false → post.error = none →
    Checkpoint (pre.getStor sevm.currentTarget) s → PoolParties cs tok s →
    PoolCallsKeep ⟨0, sevm, pre, .ok post, exc⟩ ∧ PoolCoinCallsKeepToken ⟨0, sevm, pre, .ok post, exc⟩

/-- The entry condition at fixed parties with `PoolKeepAt`. -/
def poolEntryAtK (cs : V3) (tok : Nat) (sevm : Sevm) (pre : Devm) : Prop :=
  Exec.FreshEntry sevm pre ∧ sevm.data.length < 2 ^ 256 ∧ pre.gasMeasure < 2 ^ 256 ∧
    IdReadyH sevm pre ∧ (∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp (adrOf (cs.get k))) ∧
    ¬ sevm.benvStat.rules.isPrecomp (adrOf tok) ∧ PoolKeepAt cs tok sevm pre ∧
    Exec.derivEntry (fun D => ∀ c ∈ children D, c.post.getCode 4 = c.pre.getCode 4) sevm pre

theorem pool_frame_refines_atK (cs : V3) (tok : Nat) :
    PoolFrameRefinesInH (PoolParties cs tok) (poolEntryAtK cs tok) := by
  intro sevm pre post s exc hcode hfork hentry hstatic hpc herr hck hq
  obtain ⟨⟨hstack, hmem⟩, hcd, hgas, hid, hcs, htk, hkeep, hcode4⟩ := hentry
  obtain ⟨hk, hkT⟩ := hkeep post exc s hstatic herr hck hq
  have habs : Abstracts (entryStor ⟨0, sevm, pre, .ok post, exc⟩) s := hck.abs
  refine pool_frame_refines_envH exc hcode hfork hcd hstack hmem hgas hpc hck
    ⟨hk, hkT, hcode4 _ exc, hid, fun k => ?_, ?_⟩
  · rw [coinAdr_eq habs k, hq.1]
    exact hcs k
  · rw [tokenAdr_eq habs, hq.2]
    exact htk

/-- `PoolMidEnv` with `callbacks` at the frames the replay refines. -/
structure PoolMidEnvK {cfg : ChainConfig} {checkpoint future : BlockChain} {start : Benv}
    (full : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (trace : MidHistoryTraceIn HistFork cfg start future) (pool : Adr) (cs : V3) (tok : Nat) :
    Prop where
  subset : trace.rawFrames ⊆ full.rawFrames
  callbacks : trace.FrameAdmitted pool (PoolKeepAt cs tok)
  parties : ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = pool →
    (∀ k : Fin 3, ¬ root.sevm.benvStat.rules.isPrecomp (adrOf (cs.get k))) ∧
      ¬ root.sevm.benvStat.rules.isPrecomp (adrOf tok)
  idEmpty : checkpoint.state.getCode 4 = ByteArray.empty
  idNoAuthority : full.PragueNoAuthorityAt 4
  idNoFrame : ∀ root ∈ full.rawFrames, root.sevm.codeAddress = none →
    root.sevm.currentTarget ≠ 4
  sysNe : ∀ root ∈ full.systemRawFrames, root.sevm.currentTarget ≠ pool

/-- `PoolMidEnv` gives `PoolMidEnvK`: the stated `callbacks` is the stronger. -/
theorem PoolMidEnv.toK {cfg : ChainConfig} {checkpoint future : BlockChain} {start : Benv}
    {full : ConfiguredHistoryTraceIn HistFork cfg checkpoint future}
    {trace : MidHistoryTraceIn HistFork cfg start future} {pool : Adr} {cs : V3} {tok : Nat}
    (env : PoolMidEnv full trace pool cs tok) : PoolMidEnvK full trace pool cs tok where
  subset := env.subset
  callbacks := by
    apply (trace.frameAdmitted_iff_rawFrames pool _).2
    intro root member target post exc s _ _ _ _
    exact (trace.frameAdmitted_iff_rawFrames pool _).1 env.callbacks root member target _ exc
  parties := env.parties
  idEmpty := env.idEmpty
  idNoAuthority := env.idNoAuthority
  idNoFrame := env.idNoFrame
  sysNe := env.sysNe

theorem pool_mid_trace_admittedK {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {start : Benv} {cs : V3} {tok : Nat}
    {full : ConfiguredHistoryTraceIn HistFork cfg checkpoint future}
    {trace : MidHistoryTraceIn HistFork cfg start future}
    (env : PoolMidEnvK full trace pool cs tok) :
    trace.FrameAdmitted pool (poolEntryAtK cs tok) := by
  have capabilities := BodyStageCapabilities.historical
  have callbacks := (trace.frameAdmitted_iff_rawFrames pool _).1 env.callbacks
  have ready := full.precompileReadyPragueH capabilities (fun _ hf => pool_four_mem_precompilesH hf)
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
      hfork.stateGas_none⟩, hcs, htk, callbacks root member target, ?_⟩
  exact Exec.derivEntry_of_deriv hpc (keep4 root memberFull)

/-- **`pool_mid_history` under `PoolMidEnvK`.** -/
theorem pool_mid_history_at {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {start : Benv} {s₀ : State}
    {full : ConfiguredHistoryTraceIn HistFork cfg checkpoint future}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (installed : some (start.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (start.state.getStor pool) s₀)
    (env : PoolMidEnvK full trace pool s₀.coins s₀.token) :
    some (future.state.getCode pool).toList = poolSem.image ∧
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFramesMid pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧ PoolEntries s₀ invs ∧
      ∃ s, PoolRun s₀ invs s ∧ runPool s₀ invs = some s ∧
        Checkpoint (future.state.getStor pool) s ∧ s.coins = s₀.coins ∧ s.token = s₀.token := by
  obtain ⟨code, invs, obs, auth, ent, s, run, fold, hc, hcoins, htoken, -⟩ :=
    pool_mid_history_entries (poolParties_keeps s₀.coins s₀.token)
      (pool_frame_refines_atK s₀.coins s₀.token) trace installed initial ⟨rfl, rfl⟩
      (pool_mid_trace_admittedK env)
  exact ⟨code, invs, obs, auth, ent, s, run, fold, hc, hcoins, htoken⟩

end Blanc.Lift.Curve3Pool
