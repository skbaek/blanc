import Blanc.Lift.Curve3Pool.Safe
import Blanc.ExecutionHistoryInFrameEnv
import Blanc.ExecutionHistoryInPreCancun

/-!
# Curve 3pool: the committed history over historical forks, from trace-level premises

`History.lean` over a mid history inside a retained `HistFork` chain: the replay starts right after
one transaction of a block (the pool's creation, in the deployed form), and the readiness of the
identity precompile is derived from the full chain `full` whose raw frames contain the mid history's.

* `PoolKeepAt` — the keep premises at exactly the frames the replay refines: committed, non-static, running the
  pool's code, entered at a `Checkpoint` of a state with the replay's coins and token (`PoolFrameRefinesInH`). Its storage hypotheses
  come from the replay, so a discharge that needs the coins' addresses from the pool's storage is not circular;
* `pool_mid_trace_admitted` — every pool frame of the mid history is admitted by `poolEntryAtH`;
* `PoolMidEnv` — the ENV premises, one bundle;
* `pool_mid_history` — the headline: the replay over exactly the settled non-static pool frames.

The premises keep the shape of `PoolTraceEnv`, with `PoolKeepAt` as the per-frame callback premise, and the
trace-local `parties`, `idEmpty`, `idNoAuthority`, `idNoFrame` and `sysNe`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc Blanc.ExecutionTrace

/-- The identity precompile is a precompile of every historical fork. -/
theorem pool_four_mem_precompilesH {f : Fork} (hf : HistFork f) :
    (4 : Adr) ∈ (Fork.ruleSet f).precompiles := by
  revert hf
  cases f <;> decide

/-- The keep premises at the frames the replay refines. -/
def PoolKeepAt (cs : V3) (tok : Nat) (sevm : Sevm) (pre : Devm) : Prop :=
  ∀ (post : Devm) (exc : Exec 0 sevm pre (.ok post)) (s : State),
    sevm.code = code → pre.getCode sevm.currentTarget ≠ .empty → sevm.isStatic = false → post.error = none →
    Checkpoint (pre.getStor sevm.currentTarget) s → PoolParties cs tok s →
    PoolCallsKeep ⟨0, sevm, pre, .ok post, exc⟩ ∧ PoolCoinCallsKeepToken ⟨0, sevm, pre, .ok post, exc⟩

/-- The entry condition at fixed parties, over the historical forks: a fresh machine, calldata length and
gas words in range, the identity precompile ready, the fixed coins and token not precompiles under the
frame's rules, `PoolKeepAt`, and every direct child keeps the code at `4`. -/
def poolEntryAtH (cs : V3) (tok : Nat) (sevm : Sevm) (pre : Devm) : Prop :=
  Exec.FreshEntry sevm pre ∧ sevm.data.length < 2 ^ 256 ∧ pre.gasMeasure < 2 ^ 256 ∧
    IdReadyH sevm pre ∧ (∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp (adrOf (cs.get k))) ∧
    ¬ sevm.benvStat.rules.isPrecomp (adrOf tok) ∧ PoolKeepAt cs tok sevm pre ∧
    Exec.derivEntry (fun D => ∀ c ∈ children D, c.post.getCode 4 = c.pre.getCode 4) sevm pre

/-- **The frame refinement at fixed parties, over the historical forks.** -/
theorem pool_frame_refines_atH (cs : V3) (tok : Nat) :
    PoolFrameRefinesInH (PoolParties cs tok) (poolEntryAtH cs tok) := by
  intro sevm pre post s exc hcode hfork hentry hstatic hpc herr hck hq
  obtain ⟨⟨hstack, hmem⟩, hcd, hgas, hid, hcs, htk, hkeep, hcode4⟩ := hentry
  obtain ⟨hk, hkT⟩ := hkeep post exc s hcode hpc hstatic herr hck hq
  have habs : Abstracts (entryStor ⟨0, sevm, pre, .ok post, exc⟩) s := hck.abs
  refine pool_frame_refines_envH exc hcode hfork hcd hstack hmem hgas hpc hck
    ⟨hk, hkT, hcode4 _ exc, hid, fun k => ?_, ?_⟩
  · rw [coinAdr_eq habs k, hq.1]
    exact hcs k
  · rw [tokenAdr_eq habs, hq.2]
    exact htk

/-- **The premises of the pool's mid history other than its callbacks**, at coins `cs` and token `tok`, inside
the chain `full` from `checkpoint`. -/
structure PoolMidFacts {cfg : ChainConfig} {checkpoint future : BlockChain} {start : Benv}
    (full : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (trace : MidHistoryTraceIn HistFork cfg start future) (pool : Adr) (cs : V3) (tok : Nat) :
    Prop where
  subset : trace.rawFrames ⊆ full.rawFrames
  parties : ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = pool →
    (∀ k : Fin 3, ¬ root.sevm.benvStat.rules.isPrecomp (adrOf (cs.get k))) ∧
      ¬ root.sevm.benvStat.rules.isPrecomp (adrOf tok)
  idEmpty : checkpoint.state.getCode 4 = ByteArray.empty
  idNoAuthority : full.PragueNoAuthorityAt 4
  idNoFrame : ∀ root ∈ full.rawFrames, root.sevm.codeAddress = none →
    root.sevm.currentTarget ≠ 4
  sysNe : ∀ root ∈ full.systemRawFrames, root.sevm.currentTarget ≠ pool

/-- **The ENV premises of the pool's mid history**: the facts above and the keep premises. -/
structure PoolMidEnv {cfg : ChainConfig} {checkpoint future : BlockChain} {start : Benv}
    (full : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (trace : MidHistoryTraceIn HistFork cfg start future) (pool : Adr) (cs : V3) (tok : Nat) :
    Prop extends PoolMidFacts full trace pool cs tok where
  callbacks : trace.FrameAdmitted pool (PoolKeepAt cs tok)

/-- What the history gives every raw pool frame, apart from its callbacks. -/
theorem PoolMidFacts.entry {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {start : Benv} {cs : V3} {tok : Nat}
    {full : ConfiguredHistoryTraceIn HistFork cfg checkpoint future}
    {trace : MidHistoryTraceIn HistFork cfg start future}
    (env : PoolMidFacts full trace pool cs tok) {root : Exec.Deriv} (member : root ∈ trace.rawFrames)
    (target : root.sevm.currentTarget = pool) :
    Exec.FreshEntry root.sevm root.devm ∧ root.sevm.data.length < 2 ^ 256 ∧
      root.devm.gasMeasure < 2 ^ 256 ∧ IdReadyH root.sevm root.devm ∧
      (∀ k : Fin 3, ¬ root.sevm.benvStat.rules.isPrecomp (adrOf (cs.get k))) ∧
      ¬ root.sevm.benvStat.rules.isPrecomp (adrOf tok) ∧
      Exec.derivEntry (fun D => ∀ c ∈ children D, c.post.getCode 4 = c.pre.getCode 4) root.sevm root.devm := by
  have capabilities := BodyStageCapabilities.historical
  have ready := full.precompileReadyPragueH capabilities (fun _ hf => pool_four_mem_precompilesH hf)
    env.idEmpty env.idNoAuthority env.idNoFrame
  have keep4 := full.childFrames_codeAt_keep capabilities env.idNoFrame
  have memberFull := env.subset member
  obtain ⟨hpc, hfork⟩ := trace.rootEntryIn root member
  have htx : root ∈ full.txRawFrames := by
    rcases full.rawFrames_system_or_tx root memberFull with hsys | htx
    · exact absurd target (env.sysNe root hsys)
    · exact htx
  obtain ⟨hnodeleg, hwarm⟩ := ready root htx
  obtain ⟨hcs, htk⟩ := env.parties root member target
  have hgas := full.gas_bound capabilities root memberFull
  exact ⟨trace.rawFrames_entered enteredCondition_fresh root member,
    trace.calldata_bound capabilities (fun _ hf => hf.dataNonZero_ge) root member, by omega,
    ⟨hnodeleg, hwarm, decide_eq_true (pool_four_mem_precompilesH hfork),
      hfork.stateGas_none⟩, hcs, htk, Exec.derivEntry_of_deriv hpc (keep4 root memberFull)⟩

/-- **Every pool frame of the mid history is admitted by `poolEntryAtH`.** -/
theorem pool_mid_trace_admitted {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {start : Benv} {cs : V3} {tok : Nat}
    {full : ConfiguredHistoryTraceIn HistFork cfg checkpoint future}
    {trace : MidHistoryTraceIn HistFork cfg start future}
    (env : PoolMidEnv full trace pool cs tok) :
    trace.FrameAdmitted pool (poolEntryAtH cs tok) := by
  have callbacks := (trace.frameAdmitted_iff_rawFrames pool _).1 env.callbacks
  apply (trace.frameAdmitted_iff_rawFrames pool _).2
  intro root member target
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := env.entry member target
  exact ⟨h1, h2, h3, h4, h5, h6, callbacks root member target, h7⟩

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
