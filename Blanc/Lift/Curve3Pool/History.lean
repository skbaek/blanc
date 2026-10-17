import Blanc.Lift.Curve3Pool.Safe
import Blanc.Lift.Curve3Pool.Creation.Deploy
import Blanc.ExecutionTraceFrameEnv
import Blanc.ExecutionTraceFresh

/-!
# Curve 3pool: the committed history from trace-level premises (U2(b))

`pool_history_committed_with` (`Ladder.lean`) replays a configured history over any entry condition
under which every pool frame refines the model.  Here the entry condition is `poolEntryAt`
(`Safe.lean`) at the checkpoint's coins and token, and every part of it except the callback premise
is discharged from the trace (design §1.3, §2.2):

* fresh machine — `ConfiguredHistoryTrace.freshFrameAdmitted`;
* calldata and gas words in range — `calldata_bound`, `gas_bound` (R2, `< 2 ^ 64`);
* identity precompile ready at `4` — warm by the transaction pre-warm and undelegated by empty code
  (`ConfiguredHistoryTrace.precompileReady`), under the trace-local premises that `4` holds no code
  at the checkpoint, no authorization recovers to it, and no CREATE frame targets it; system frames
  never target the pool, whose 21199-byte runtime has no canonical system code's size
  (`ConfiguredHistoryTrace.system_ne_of_size`), under the canonical system code installed at the
  checkpoint and the matching trace-local system exclusions;
* children keep the code at `4` — `ConfiguredHistoryTrace.childFrames_codeAt_keep`, from the same
  "no CREATE frame targets `4`";
* coins and token not precompiles — a trace-local premise over the *fixed* addresses of the
  checkpoint's coins and token (`parties`), carried to every replayed frame by the model invariant
  `PoolParties`.

The only per-frame premise left is the callback premise (`callbacks`): every direct child of a pool
frame keeps the pool's storage (`PoolCallsKeep`) and every coin child keeps the token's storage
(`PoolCoinCallsKeepToken`, R1).  No premise names a hash.

* `pool_history_committed_derived` — the headline;
* `pool_history_initialized` — the same from the deployment's code and storage
  (`Creation.pool_deploy_covered` supplies both), at the constructor's model state.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc Blanc.ExecutionTrace

/-- The identity precompile is a precompile of every covered fork. -/
theorem pool_four_mem_precompiles {f : Fork} (hf : CoveredFork f) :
    (4 : Adr) ∈ (Fork.ruleSet f).precompiles :=
  hf.cases (motive := fun f => (4 : Adr) ∈ (Fork.ruleSet f).precompiles)
    (by decide) (by decide) (by decide) (by decide)

/-- The runtime's size is no canonical system code's size. -/
theorem pool_code_size_ne_system : ∀ p ∈ systemContracts, p.2.size ≠ code.size := by
  have hsize : code.size = 21199 := by
    have h := code_toList_length
    rwa [ByteArray.toList_eq_toList_data, Array.length_toList] at h
  intro p hp
  rw [hsize]
  simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> decide +kernel

/-- **Every pool frame of the history is admitted by `poolEntryAt`** at the checkpoint's coins and
token, from the callback premise and trace-local premises. -/
theorem pool_trace_admitted {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {cs : V3} {tok : Nat}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (callbacks : trace.FrameAdmitted pool
      (Exec.derivEntry fun D => PoolCallsKeep D ∧ PoolCoinCallsKeepToken D))
    (parties : ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = pool →
      (∀ k : Fin 3, ¬ root.sevm.benvStat.rules.isPrecomp (adrOf (cs.get k))) ∧
        ¬ root.sevm.benvStat.rules.isPrecomp (adrOf tok))
    (idEmpty : checkpoint.state.getCode 4 = ByteArray.empty)
    (idNoAuthority : trace.NoAuthorityAt 4)
    (idNoFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ 4)
    (sysInstalled : SystemCodeInstalled checkpoint.state)
    (sysNoAuthority : ∀ p ∈ systemContracts, trace.NoAuthorityAt p.1)
    (sysNoFrame : ∀ p ∈ systemContracts, ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1) :
    trace.FrameAdmitted pool (poolEntryAt cs tok) := by
  have fresh := trace.freshFrameAdmitted pool
  rw [trace.frameAdmitted_iff_rawFrames] at callbacks fresh ⊢
  have system := trace.system_ne_of_size sysInstalled sysNoAuthority sysNoFrame
    (code_eq_of_toList installed) pool_code_size_ne_system
  have ready := trace.precompileReady (fun _ hf => pool_four_mem_precompiles hf) idEmpty
    idNoAuthority idNoFrame
  have keep4 := trace.childFrames_codeAt_keep idNoFrame
  intro root member target
  obtain ⟨hpc, hfork⟩ := trace.rootEntry root member
  have htx : root ∈ trace.txRawFrames := by
    rcases trace.rawFrames_system_or_tx root member with hsys | htx
    · exact absurd target (system root hsys)
    · exact htx
  obtain ⟨hnodeleg, hwarm⟩ := ready root htx
  obtain ⟨hcs, htk⟩ := parties root member target
  have hgas := trace.gas_bound root member
  refine ⟨fresh root member target, trace.calldata_bound root member, by omega,
    ⟨hnodeleg, hwarm, decide_eq_true (pool_four_mem_precompiles hfork), hfork⟩, hcs, htk, ?_⟩
  refine Exec.derivEntry_of_deriv hpc ⟨?_, ?_, keep4 root member⟩
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

/-- **The pool model replays the committed history (U2(b)), with only the callback premise per
frame.**  In a configured history from a checkpoint with the certified runtime installed at `pool`
and the pool's storage at a `Checkpoint` abstracting `s₀`, the runtime is still installed, and the
outermost committed non-static pool frames, in trace order, are authentic invocations that replay
through `Model.step` from `s₀` to a state the future pool storage abstracts at a `Checkpoint`, with
the coins and the token unchanged (`pool_history_committed_with`'s conclusion).

Premises: CODE `installed`; INIT `initial`; the per-frame ENV premise `callbacks`; and trace-local
ENV premises — `parties` (the checkpoint's coins and token are not precompiles under any pool
frame's rules), `idEmpty`/`idNoAuthority`/`idNoFrame` (the identity precompile's account holds no
code at the checkpoint, no authorization recovers to it, no CREATE frame targets it), and
`sysInstalled`/`sysNoAuthority`/`sysNoFrame` (the canonical system code is installed at the
checkpoint and likewise protected). -/
theorem pool_history_committed_derived {pool : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {s₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (checkpoint.state.getStor pool) s₀)
    (callbacks : trace.FrameAdmitted pool
      (Exec.derivEntry fun D => PoolCallsKeep D ∧ PoolCoinCallsKeepToken D))
    (parties : ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = pool →
      (∀ k : Fin 3, ¬ root.sevm.benvStat.rules.isPrecomp (adrOf (s₀.coins.get k))) ∧
        ¬ root.sevm.benvStat.rules.isPrecomp (adrOf s₀.token))
    (idEmpty : checkpoint.state.getCode 4 = ByteArray.empty)
    (idNoAuthority : trace.NoAuthorityAt 4)
    (idNoFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ 4)
    (sysInstalled : SystemCodeInstalled checkpoint.state)
    (sysNoAuthority : ∀ p ∈ systemContracts, trace.NoAuthorityAt p.1)
    (sysNoFrame : ∀ p ∈ systemContracts, ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1) :
    some (future.state.getCode pool).toList = poolSem.image ∧
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFrames pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      ∃ s, PoolRun s₀ invs s ∧ runPool s₀ invs = some s ∧
        Checkpoint (future.state.getStor pool) s ∧ s.coins = s₀.coins ∧ s.token = s₀.token := by
  obtain ⟨code, invs, obs, auth, s, run, fold, hc, hcoins, htoken, -⟩ :=
    pool_history_committed_in (poolParties_keeps s₀.coins s₀.token)
      (pool_frame_refines_at s₀.coins s₀.token) trace installed initial ⟨rfl, rfl⟩
      (pool_trace_admitted trace installed callbacks parties idEmpty idNoAuthority idNoFrame
        sysInstalled sysNoAuthority sysNoFrame)
  exact ⟨code, invs, obs, auth, s, run, fold, hc, hcoins, htoken⟩

/-- **The committed history from the deployment.**  `pool_history_committed_derived` at a
checkpoint whose pool account holds what the recorded creation leaves
(`Creation.pool_deploy_covered`: the certified runtime and `deployedStor deployTime`), replaying
from the constructor's model state `poolInitState deployTime.toNat`. -/
theorem pool_history_initialized {pool : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (deployedCode : (checkpoint.state.getCode pool).toList = code.toList)
    (deployedStorage : checkpoint.state.getStor pool = Creation.deployedStor Creation.deployTime)
    (callbacks : trace.FrameAdmitted pool
      (Exec.derivEntry fun D => PoolCallsKeep D ∧ PoolCoinCallsKeepToken D))
    (parties : ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = pool →
      (∀ k : Fin 3, ¬ root.sevm.benvStat.rules.isPrecomp
        (adrOf ((Creation.poolInitState Creation.deployTime.toNat).coins.get k))) ∧
        ¬ root.sevm.benvStat.rules.isPrecomp
          (adrOf (Creation.poolInitState Creation.deployTime.toNat).token))
    (idEmpty : checkpoint.state.getCode 4 = ByteArray.empty)
    (idNoAuthority : trace.NoAuthorityAt 4)
    (idNoFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ 4)
    (sysInstalled : SystemCodeInstalled checkpoint.state)
    (sysNoAuthority : ∀ p ∈ systemContracts, trace.NoAuthorityAt p.1)
    (sysNoFrame : ∀ p ∈ systemContracts, ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1) :
    some (future.state.getCode pool).toList = poolSem.image ∧
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFrames pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      ∃ s, PoolRun (Creation.poolInitState Creation.deployTime.toNat) invs s ∧
        runPool (Creation.poolInitState Creation.deployTime.toNat) invs = some s ∧
        Checkpoint (future.state.getStor pool) s ∧
        s.coins = (Creation.poolInitState Creation.deployTime.toNat).coins ∧
        s.token = (Creation.poolInitState Creation.deployTime.toNat).token := by
  have initial : Checkpoint (checkpoint.state.getStor pool)
      (Creation.poolInitState Creation.deployTime.toNat) := by
    rw [deployedStorage]
    exact Creation.deployedStor_checkpoint (by decide)
  exact pool_history_committed_derived trace (by rw [deployedCode]; rfl) initial callbacks parties
    idEmpty idNoAuthority idNoFrame sysInstalled sysNoAuthority sysNoFrame

end Blanc.Lift.Curve3Pool
