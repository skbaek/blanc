import Blanc.Composition.Curve3PoolSupply
import Blanc.Composition.Curve3PoolJointRoot
import Blanc.ExecutionAccountingPositionalHistory
import Blanc.ExecutionMidHistoryInRootCallers

/-!
# The pool and 3Crv over one historical mid history: minter persistence past the minter cut

`Curve3PoolSupply.lean`'s walk over the settled frames of a `MidHistoryTraceIn HistFork`, from a joint
checkpoint at the mid history's start:

* `c3crv_mid_view` — 3Crv's view replay to the end and at every settled frame no earlier non-static
  3Crv frame encloses (the frame carrier of `wholeFramePositionalLadderIn`);
* `pool_3crv_mid_history` — the pool's replay, 3Crv's replay, **minter persistence**, the **supply
  identity** and the per-invocation supply moves (`Mid3CrvHistory`), over one mid history;
* `joint_mid_history` — the same from `JointDeployment`'s minter cut, with the checkpoint's states the
  ones `joint_root_replay` gives.

The remaining premises are 3Crv's collision premise (`FreshKeys`) and the pool's `PoolMidEnv`. No premise
says who calls 3Crv: the pool sends no 3Crv invocation between its own frames (`gap_callers`), and it
originates no root because its code is installed (`settledRoots_caller_ne_of_stateInv`).
-/

namespace Blanc.Composition.Curve3PoolSupply

open Jaune Blanc Blanc.Lift Blanc.Lift.Token Blanc.Lift.Curve3Crv Blanc.ExecutionTrace
  Blanc.ExecutionAccountingReplay Blanc.Composition.Curve3CrvToken
open Blanc.Lift.Curve3Pool (PoolInvocation PoolRun PoolEntries poolSubtreeFrames)
open Blanc.Composition.Curve3Pool3CrvJoint (JointCheckpoint)

/-- **3Crv's view replay over a mid history**, to the end and at every settled frame no earlier
non-static 3Crv frame encloses. -/
theorem c3crv_mid_view {ca : Adr} {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    {initial : Blanc.Curve3Crv.State} {initialKeys : Key → Prop}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (installed : some (start.state.getCode ca).toList = c3crvSem.image)
    (invariant : VyInv (start.state.getStor ca) initial initialKeys)
    (fresh : FreshKeys initialKeys (midTouchedKeysIn ca trace)) :
    ViewReplayH (Key.extend initialKeys (midTouchedKeysIn ca trace)) (viewOf (start.state.getStor ca))
        (trace.settledFrames.flatMap (viewFrameObs ca)) (viewOf (future.state.getStor ca)) ∧
      ∀ {before : List Exec.Frame} {f : Exec.Frame} {after : List Exec.Frame},
        trace.settledFrames = before ++ f :: after →
        (∀ A ∈ before, A.Encloses f → ¬ (A.sevm.currentTarget = ca ∧ A.sevm.isStatic = false)) →
        ViewReplayH (Key.extend initialKeys (midTouchedKeysIn ca trace))
          (viewOf (start.state.getStor ca)) (before.flatMap (viewFrameObs ca))
          (viewOf (f.pre.state.getStor ca)) := by
  let U := Key.extend initialKeys (midTouchedKeysIn ca trace)
  have topology : VyInv (start.state.getStor ca) initial U := invariant.extend fresh
  have capabilities := BodyStageCapabilities.historical
  have startInv : (curveSpec U).StateInv ca start.state :=
    ⟨installed, trivial, ⟨initial, initialKeys, fun _ hk => Or.inl hk, invariant⟩⟩
  obtain ⟨steps, replay, observed⟩ :=
    (wholeFramePositionalLadderIn (F := HistFork) HistFork.stateGas_none (c := curveSpec U)
      (viewCarrierBy OwnerAnswerH ca U) (viewObservationBy OwnerAnswerH ca U) viewReplay_append
      (fun _ _ => ()) (fun _ _ => ()) (fun _ _ => rfl) (fun h => Subtype.ext (funext h))
      (fun _ hf => viewFrameObs_static hf) (fun _ hf => viewFrameObs_foreign hf)
      (c3crv_wholeFrameBy HistFork.stateGas_none (frameRefines_noStateGas HistFork.stateGas_none)
        ca U topology.inj topology.apart)
      (curveSpec_preservesAdmittedIn HistFork HistFork.stateGas_none ca U topology.inj
        topology.apart)).midHistoryIn trace (c3crv_mid_admittedH trace) capabilities
      (trace.rewardCreditsFunded capabilities) startInv c3crvInstalledCert.runtimeSafety rfl
  obtain ⟨⟨whole, wholeReplay, wholeObserved⟩, positional⟩ := framesCarrier_read replay observed
  refine ⟨?_, fun {before f after} split noOpaque => ?_⟩
  · change ViewReplayH U _ whole _ at wholeReplay
    change whole = _ at wholeObserved
    subst wholeObserved
    exact wholeReplay
  · obtain ⟨atSteps, atReplay, atObserved⟩ :=
      positional before f after split (Exec.NoOpaqueAbove.of_encloses noOpaque)
    change ViewReplayH U _ atSteps (viewOf (f.pre.state.getStor ca)) at atReplay
    change atSteps = _ at atObserved
    subst atObserved
    exact atReplay

/-- **What holds of the pool and 3Crv over one mid history** `trace` from model states `ps₀`, `cs₀`:

* the pool's runtime stays installed and its model replays exactly the committed pool frames, each
  invocation authentic, to a state its future storage abstracts at a `Checkpoint`, keeping coins and
  token;
* 3Crv's runtime stays installed and its model replays exactly its committed invocations to `cs`,
  abstracting its future storage;
* **minter persistence**: `cs.minter = pool`;
* **supply identity**: 3Crv's final supply plus the pool's committed burns equals the starting supply
  plus the pool's committed mints (`poolMinted`, `poolBurned`; word values);
* **per invocation**: the model step's raw effect, 3Crv's supply word across the invocation's frame
  moved by the step's own amounts, and the supply it observed (`SupplyObserved`). -/
def Mid3CrvHistory {cfg : ChainConfig} {start : Benv} {future : BlockChain} (pool c3 : Adr)
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (ps₀ : Curve3Pool.State) (cs₀ : Blanc.Curve3Crv.State) (K₀ : Key → Prop) : Prop :=
  some (future.state.getCode pool).toList = Curve3Pool.poolSem.image ∧
  some (future.state.getCode c3).toList = c3crvSem.image ∧
  ∃ invs : List PoolInvocation,
    invs.flatMap (fun i => poolSubtreeFrames pool i.frame) =
      Curve3Pool.committedPoolFramesMid pool trace ∧
    (∀ i ∈ invs, i.Authentic pool) ∧
    ∃ s, PoolRun ps₀ invs s ∧ Curve3Pool.runPool ps₀ invs = some s ∧
      Curve3Pool.Checkpoint (future.state.getStor pool) s ∧ s.coins = ps₀.coins ∧
      s.token = ps₀.token ∧
    ∃ cs, InvRunBy OwnerAnswerH cs₀ (midCommittedInvocationsIn c3 trace) cs ∧
      VyInv (future.state.getStor c3) cs
        (Key.extend K₀ (invocationKeys (midCommittedInvocationsIn c3 trace))) ∧
      cs.minter = pool ∧
      cs.totalSupply.toNat + poolBurned ps₀ invs = cs₀.totalSupply.toNat + poolMinted ps₀ invs ∧
      ∀ (pre : List PoolInvocation) (i : PoolInvocation) (post : List PoolInvocation)
        (sᵢ : Curve3Pool.State), invs = pre ++ i :: post → PoolRun ps₀ pre sᵢ →
        ∃ o, Curve3Pool.step sᵢ i.env (Curve3Pool.decodeCall i.frame.sevm) = some o ∧
          Curve3Pool.RawEffect (Blanc.Exec.Frame.rootDeriv i.frame) i.frame.post i.env o ∧
          supplyAt c3 i.frame.post.state + callsBurned o.calls =
            supplyAt c3 i.frame.pre.state + callsMinted o.calls ∧
          SupplyObserved c3 i

/-- **The pool and 3Crv over one historical mid history.** From a joint checkpoint at the mid
history's start with both runtimes installed, under the pool's `PoolMidEnv`, 3Crv's collision premise
(`FreshKeys`, its HASH-T) and `pool ≠ systemAddress`, `Mid3CrvHistory` holds. -/
theorem pool_3crv_mid_history {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {start : Benv} {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Key → Prop}
    {full : ConfiguredHistoryTraceIn HistFork cfg checkpoint future}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (poolInstalled : some (start.state.getCode pool).toList = Curve3Pool.poolSem.image)
    (c3Installed : some (start.state.getCode c3).toList = c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ start.state)
    (fresh : FreshKeys K₀ (midTouchedKeysIn c3 trace))
    (env : Curve3Pool.PoolMidEnv full trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress) :
    Mid3CrvHistory pool c3 trace ps₀ cs₀ K₀ := by
  let U := Key.extend K₀ (midTouchedKeysIn c3 trace)
  have topology : VyInv (start.state.getStor c3) cs₀ U := joint.c3.extend fresh
  have ready := c3crv_mid_readyH trace c3Installed joint.c3 fresh
  obtain ⟨viewEnd, viewAt⟩ := c3crv_mid_view trace c3Installed joint.c3 fresh
  have capabilities := BodyStageCapabilities.historical
  have rewards := trace.rewardCreditsFunded capabilities
  have callbacks := (trace.frameAdmitted_iff_rawFrames pool _).1 env.callbacks
  have roots : ∀ R ∈ trace.settledRoots, R.sevm.caller ≠ pool :=
    trace.settledRoots_caller_ne_of_stateInv
      (Curve3Pool.poolSpec_preservesAdmittedH pool (Curve3Pool.poolEntryAtH ps₀.coins ps₀.token))
      capabilities (Curve3Pool.pool_mid_trace_admitted env) rewards
      (c := Curve3Pool.poolSpec) ⟨poolInstalled, trivial, trivial⟩ Curve3Pool.pool_runtimeSafety rfl
      notSystem
  obtain ⟨Z, runZ, -⟩ := replay_run (fun _ hk => Or.inl hk) joint.c3 viewEnd
  have partiesTok : ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = pool →
      (∀ k : Fin 3, ¬ root.sevm.benvStat.rules.isPrecomp
        (Curve3Pool.adrOf (ps₀.coins.get k))) ∧
        ¬ root.sevm.benvStat.rules.isPrecomp (Curve3Pool.adrOf c3.toNat) := by
    rw [← joint.tokenIs]
    exact env.parties
  have W : WalkEnv trace.settledFrames trace.settledRoots (start.state.getStor c3) pool c3
      ps₀.coins cs₀ K₀ U :=
    { injective := topology.inj
      apartU := topology.apart
      forest := trace.settledFrames_eq
      ready := ready
      hK := fun _ hk => Or.inl hk
      invariant := joint.c3
      apart := joint.apart
      roots := roots
      view := fun split nonstatic => viewAt split (noOpaque_of_nonstatic ready split nonstatic)
      whole := ⟨Z, runZ⟩
      parties := fun f member =>
        partiesTok _ (trace.mem_rawFrames_of_mem_settledFrames f member)
      keepToken := fun f member target mutable st ck hcs hts => by
        have keep : Curve3Pool.PoolKeepAt ps₀.coins ps₀.token f.sevm f.pre :=
          callbacks _ (trace.mem_rawFrames_of_mem_settledFrames f member) target
        have ready0 := (ready f member).1
        obtain ⟨pc, sevm, pre, out, run, committed⟩ := f
        dsimp only at ready0 target mutable keep ck ⊢
        subst ready0
        cases out with
        | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
        | ok post =>
          exact (keep post run st mutable (Option.isNone_iff_eq_none.mp (by simpa only [Execution.commits] using committed))
            (by rw [show sevm.currentTarget = pool from target]; exact ck)
            ⟨hcs, hts.trans joint.tokenIs.symm⟩).2 }
  obtain ⟨code, invs, obs, auth, entries, s, run, fold, hc, hcoins, htoken⟩ :=
    Curve3Pool.pool_mid_history trace poolInstalled joint.poolCk env
  obtain ⟨Y, runY, minY, supY, steps⟩ := supply_whole W run entries auth obs joint.tokenIs
    joint.minterIs
  rw [viewObs_eq_committed ready] at runY
  obtain ⟨c3Code, cs, c3Run, -, final, -⟩ :=
    c3crv_mid_history_framesHist trace c3Installed joint.c3 fresh
  have hY : Y = cs := Option.some.inj (runY.symm.trans c3Run.runInvocations_eq)
  subst hY
  refine ⟨code, c3Code, invs, obs, auth, s, run, fold, hc, hcoins, htoken, Y, c3Run, final, minY,
    supY, ?_⟩
  intro pre i post sᵢ split hpre
  obtain ⟨o, hstep, hraw, -⟩ := PoolRun.split (split ▸ run) hpre
  exact ⟨o, hstep, hraw, StepSupplies.split (split ▸ steps) hpre o hstep⟩

open Blanc.Composition.Curve3PoolJointRoot in
/-- **From the joint deployment, past the minter cut.** After the minter assignment of a
`JointDeployment`, over any historical mid history starting right there, under its `PoolMidEnv` at the
constructor's coins and token and 3Crv's collision premise at the keys tracked at the cut, the
checkpoint's states are the replays `joint_root_replay` gives and `Mid3CrvHistory` holds from them. In
particular the pool stays 3Crv's minter over the whole history. -/
theorem joint_mid_history (j : JointDeployment) {checkpoint future : BlockChain}
    {full : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future}
    (trace : MidHistoryTraceIn HistFork mainnetChainConfig j.minterCut.afterBenv future)
    (fresh : FreshKeys j.c3Keys (midTouchedKeysIn Curve3Crv.Creation.tokenAddress trace))
    (env : Curve3Pool.PoolMidEnv full trace Curve3Pool.Creation.poolAddress
      Curve3Pool.Creation.coinsN Curve3Pool.Creation.tokenN) :
    ∃ (invs : List PoolInvocation) (ps : Curve3Pool.State) (cs : Blanc.Curve3Crv.State),
      invs.flatMap (fun i => poolSubtreeFrames Curve3Pool.Creation.poolAddress i.frame) =
        j.poolFrames ∧
      PoolRun (Curve3Pool.Creation.poolInitState Curve3Pool.Creation.deployTime.toNat) invs ps ∧
      InvRunBy OwnerAnswerH (Curve3Crv.Creation.curveDeployedState Curve3Crv.Creation.deployer)
        j.c3Invocations cs ∧
      JointCheckpoint Curve3Pool.Creation.poolAddress Curve3Crv.Creation.tokenAddress ps cs j.c3Keys
        j.cutState ∧
      Mid3CrvHistory Curve3Pool.Creation.poolAddress Curve3Crv.Creation.tokenAddress trace ps cs
        j.c3Keys := by
  obtain ⟨poolCode, c3Code, invs, ps, cs, obs, -, -, run, -, c3Run, joint⟩ := joint_root_replay j
  have hps := run.coins_token
  have envAt : Curve3Pool.PoolMidEnv full trace Curve3Pool.Creation.poolAddress ps.coins ps.token := by
    rw [hps.1, hps.2]
    exact env
  exact ⟨invs, ps, cs, obs, run, c3Run, joint,
    pool_3crv_mid_history trace poolCode c3Code joint fresh envAt (by decide)⟩

end Blanc.Composition.Curve3PoolSupply
