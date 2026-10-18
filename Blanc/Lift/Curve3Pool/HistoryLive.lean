import Blanc.Lift.Curve3Pool.History
import Blanc.Lift.Curve3Pool.ExchangeLive
import Blanc.Lift.Curve3Pool.AddLiquidityLive
import Blanc.Lift.Curve3Pool.RemoveLiquidityLiveness
import Blanc.Lift.Curve3Pool.RemoveImbalanceLive
import Blanc.Lift.Curve3Pool.OneCoinLive

/-!
# Curve 3pool: liveness at every reachable state (U6, design §5.2)

`pool_history_committed_env` (`History.lean`) says the future storage of a configured history is
the checkpoint of the model state `s` reached by replaying the committed invocations.  The five
frame liveness theorems (`exchange_live`, `addLiquidity_live`, `removeLiquidity_live`,
`removeLiquidityImbalance_live`, `removeLiquidityOneCoin_live`) run a model-accepted call from a
frame whose pre-state's pool storage is a checkpoint of the model state, with each state-changing
callee call moving the world along a chain of fresh invariants.  Composing them, the
`c3crv_history_live` shape (`Curve3Crv/Liveness.lean`): at any frame of the pool whose pre-state is
the future state of a configured history, every call the model accepts at the replayed state
executes, under the frame liveness theorem's own callee premises.

* `PoolHistoryAt trace pool s₀ s` — the history conclusion at the replayed state `s`;
* `pool_history_reached` — the replayed state is a checkpoint of the frame's pool storage;
* `pool_history_exchange_live`, `pool_history_addLiquidity_live`,
  `pool_history_removeLiquidity_live`, `pool_history_removeLiquidityImbalance_live`,
  `pool_history_removeLiquidityOneCoin_live` — one per entry.

For the history from the deployment, `pool_history_initialized`'s premises give `installed` and
`initial` at `Creation.poolInitState Creation.deployTime.toNat`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.ExecutionTrace

/-- **The history conclusion at the replayed state `s`**: the committed invocations replayed from
`s₀` reach `s`, whose checkpoint the future pool storage holds, with the coins and token kept. -/
def PoolHistoryAt {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (pool : Adr) (s₀ s : State) : Prop :=
  ∃ invs : List PoolInvocation,
    invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFrames pool trace ∧
    (∀ i ∈ invs, i.Authentic pool) ∧ PoolRun s₀ invs s ∧ runPool s₀ invs = some s ∧
    Checkpoint (future.state.getStor pool) s ∧ s.coins = s₀.coins ∧ s.token = s₀.token

/-- **The replayed state at a frame of the future state**: after a configured history, a pool frame
whose pre-state is the future state reads the checkpoint of the replayed state. -/
theorem pool_history_reached {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {s₀ : State} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (checkpoint.state.getStor pool) s₀)
    (env : PoolTraceEnv trace pool s₀.coins s₀.token)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state) :
    some (future.state.getCode pool).toList = poolSem.image ∧
    ∃ s, PoolHistoryAt trace pool s₀ s ∧ Checkpoint (pre.getStor sevm.currentTarget) s := by
  obtain ⟨code, invs, obs, auth, s, run, fold, hc, hcoins, htoken⟩ :=
    pool_history_committed_env trace installed initial env
  have hstor : Devm.getStor pre sevm.currentTarget = future.state.getStor pool := by
    rw [target]
    show pre.state.getStor pool = _
    rw [state]
  refine ⟨code, s, ⟨invs, obs, auth, run, fold, hc, hcoins, htoken⟩, ?_⟩
  rw [hstor]
  exact hc

section Wrappers

variable {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {s₀ : State}

/-- **`exchange` is live at every reachable state** (`exchange_live` after any configured
history). -/
theorem pool_history_exchange_live (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (checkpoint.state.getStor pool) s₀)
    (env : PoolTraceEnv trace pool s₀.coins s₀.token)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state) :
    ∃ s, PoolHistoryAt trace pool s₀ s ∧
      ∀ {o : Out} {i j : Fin 3} {B1 B2 : B256} {W W' W'' : Devm → Prop} {U G : Nat}
        (_hcode : sevm.code = code) (_hfork : CoveredFork sevm.benvStat.fork)
        (_hstatic : sevm.isStatic = false) (_hdepth : sevm.depth ≠ 0)
        (_hlen : 4 ≤ sevm.data.length) (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selExchange)
        (_hi : i.val = (exI sevm).toNat) (_hj : j.val = (exJ sevm).toNat)
        (_hstep : step s (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) (decodeCall sevm) =
          some o)
        (_hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty) (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hWc : WClosed sevm W) (_hW'c : WClosed sevm W') (_hWb : W pre)
        (_hbal : i = feeIndex →
          CoinBalOkAt sevm W W ((pre.getStor sevm.currentTarget).get (coinSlot i)) B1 U
            0x3dc 0x440 ∧
          CoinBalOkAt sevm W' W' ((pre.getStor sevm.currentTarget).get (coinSlot i)) B2 U
            0x71c 0x780)
        (_hpull : CoinPullOkAt sevm W W' ((pre.getStor sevm.currentTarget).get (coinSlot i))
          (exDx sevm) U 0x600 0x6c0)
        (_hW''c : WClosed sevm W'')
        (_hpush : CoinPushOkAt sevm W' W'' ((pre.getStor sevm.currentTarget).get (coinSlot j))
          (Nat.toB256 (exPushAmt o)) U 0xb60 0xc00)
        (_hG : costExchange sevm pre s (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i j
          (exDx sevm).toNat + 4 * U ≤ G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ bp bq,
          pullIn (exEnv sevm i j bp bq) i (exDx sevm).toNat =
            pullIn (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i (exDx sevm).toNat ∧
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (exEnv sevm i j bp bq)
            o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state ∧ W'' post := by
  obtain ⟨-, s, hs, hck⟩ := pool_history_reached trace installed initial env target state
  exact ⟨s, hs, fun hcode hfork hstatic hdepth hlen hcd hsel hi hj hstep hcoin hpc hid hkeep hWc
    hW'c hWb hbal hpull hW''c hpush hG hGm => exchange_live hcode hfork hstatic hdepth hlen hcd hsel hi
    hj hck hstep hcoin hpc hid hkeep hWc hW'c hWb hbal hpull hW''c hpush hG hGm⟩

/-- **`add_liquidity` is live at every reachable state** (`addLiquidity_live` after any
configured history). -/
theorem pool_history_addLiquidity_live (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (checkpoint.state.getStor pool) s₀)
    (env : PoolTraceEnv trace pool s₀.coins s₀.token)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state) :
    ∃ s, PoolHistoryAt trace pool s₀ s ∧
      ∀ {o : Out} {T B1 B2 : B256} {W : Nat → Devm → Prop} {U G : Nat}
        (_hcode : sevm.code = code) (_hfork : CoveredFork sevm.benvStat.fork)
        (_hstatic : sevm.isStatic = false) (_hdepth : sevm.depth ≠ 0)
        (_hlen : 4 ≤ sevm.data.length) (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selAddLiquidity)
        (_hstep : step s (alEnvW sevm T.toNat B1.toNat B2.toNat) (decodeCall sevm) = some o)
        (_htok : ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr)
        (_hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty) (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hWc : ∀ j, j ≤ 4 → WClosed sevm (W j)) (_hWb : W 0 pre)
        (_hsup : SupplyOkAt sevm (W 0) (W 0) ((pre.getStor sevm.currentTarget).get tokenSlot) T U
          0x27c 0x2c0)
        (_hpull : ∀ k : Fin 3, k ≠ feeIndex → alAmt sevm k.val ≠ 0 →
          CoinPullOkAt sevm (W k) (W (k + 1)) ((pre.getStor sevm.currentTarget).get (coinSlot k))
            (alAmt sevm k.val) U 0x760 0x820)
        (_hskip : ∀ k : Fin 3, alAmt sevm k.val = 0 → ∀ b, W k b → W (k + 1) b)
        (_hfee : alAmt sevm 2 ≠ 0 →
          CoinBalOkAt sevm (W 2) (W 2) ((pre.getStor sevm.currentTarget).get (coinSlot 2)) B1 U
            0x53c 0x5a0 ∧
          CoinPullOkAt sevm (W 2) (W 3) ((pre.getStor sevm.currentTarget).get (coinSlot 2))
            (alAmt sevm 2) U 0x760 0x820 ∧
          CoinBalOkAt sevm (W 3) (W 3) ((pre.getStor sevm.currentTarget).get (coinSlot 2)) B2 U
            0x87c 0x8e0)
        (_hmint : MintOkAt sevm (W 3) (W 4) ((pre.getStor sevm.currentTarget).get tokenSlot)
          (Nat.toB256 (alMintAmt o)) U 0xc7c 0xd00)
        (_hG : costAddLiquidity s (alEnvW sevm T.toNat B1.toNat B2.toNat) (argV3 sevm 0) + 7 * U ≤
          G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure + 3000 < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ e : Env,
          e.supply = some T.toNat ∧ step s e (decodeCall sevm) = some o ∧
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post e o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state := by
  obtain ⟨-, s, hs, hck⟩ := pool_history_reached trace installed initial env target state
  exact ⟨s, hs, fun hcode hfork hstatic hdepth hlen hcd hsel hstep htok hcoin hpc hid hkeep hWc
    hWb hsup hpull hskip hfee hmint hG hGm => addLiquidity_live hcode hfork hstatic hdepth hlen
    hcd hsel hck hstep htok hcoin hpc hid hkeep hWc hWb hsup hpull hskip hfee hmint hG hGm⟩

/-- **`remove_liquidity` is live at every reachable state** (`removeLiquidity_live` after any
configured history). -/
theorem pool_history_removeLiquidity_live (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (checkpoint.state.getStor pool) s₀)
    (env : PoolTraceEnv trace pool s₀.coins s₀.token)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state) :
    ∃ s, PoolHistoryAt trace pool s₀ s ∧
      ∀ {o : Out} {T : B256} {W : Nat → Devm → Prop} {U G : Nat}
        (_hcode : sevm.code = code) (_hfork : CoveredFork sevm.benvStat.fork)
        (_hstatic : sevm.isStatic = false) (_hdepth : sevm.depth ≠ 0)
        (_hlen : 4 ≤ sevm.data.length) (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selRemoveLiquidity)
        (_hstep : step s (rlEnv sevm T) (decodeCall sevm) = some o)
        (_htok : ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr)
        (_hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty) (_hid : IdReady sevm pre)
        (_hckeep : ∀ k : Fin 3,
          CallKeeps sevm ((pre.getStor sevm.currentTarget).get (coinSlot k)))
        (_hsk : StaticKeeps sevm ((pre.getStor sevm.currentTarget).get tokenSlot))
        (_htk : CallKeeps sevm ((pre.getStor sevm.currentTarget).get tokenSlot))
        (_hWc : ∀ k, k ≤ 3 → WClosed sevm (W k)) (_hWb : W 0 pre)
        (_hsup : SupplyOk sevm (W 0) ((pre.getStor sevm.currentTarget).get tokenSlot) T U)
        (_hpush : ∀ k : Fin 3, CoinPushOkAt sevm (W k) (W (k + 1))
          ((pre.getStor sevm.currentTarget).get (coinSlot k))
          (balAt (pre.getStor sevm.currentTarget) k * rlAmt sevm / T) U 0x520 0x5c0)
        (_hburn : BurnOkTo sevm (W 3) (W 4) ((pre.getStor sevm.currentTarget).get tokenSlot)
          (rlAmt sevm) U)
        (_hG : 167000 + 5 * U ≤ G) (_hGm : (St pre [] Mem.empty G).gasMeasure < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post),
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (rlEnv sevm T) o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state := by
  obtain ⟨-, s, hs, hck⟩ := pool_history_reached trace installed initial env target state
  exact ⟨s, hs, fun hcode hfork hstatic hdepth hlen hcd hsel hstep htok hcoin hpc hid hckeep hsk
    htk hWc hWb hsup hpush hburn hG hGm => removeLiquidity_live hcode hfork hstatic hdepth hlen hcd
    hsel hck hstep htok hcoin hpc hid hckeep hsk htk hWc hWb hsup hpush hburn hG hGm⟩

/-- **`remove_liquidity_imbalance` is live at every reachable state**
(`removeLiquidityImbalance_live` after any configured history). -/
theorem pool_history_removeLiquidityImbalance_live
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (checkpoint.state.getStor pool) s₀)
    (env : PoolTraceEnv trace pool s₀.coins s₀.token)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state) :
    ∃ s, PoolHistoryAt trace pool s₀ s ∧
      ∀ {o : Out} {T : B256} {W : Nat → Devm → Prop} {U G : Nat}
        (_hcode : sevm.code = code) (_hfork : CoveredFork sevm.benvStat.fork)
        (_hstatic : sevm.isStatic = false) (_hdepth : sevm.depth ≠ 0)
        (_hlen : 4 ≤ sevm.data.length) (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selRemoveLiquidityImbalance)
        (_hstep : step s (rliEnvW sevm T.toNat) (decodeCall sevm) = some o)
        (_htok : ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr)
        (_hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty) (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hWc : ∀ j, j ≤ 4 → WClosed sevm (W j)) (_hWb : W 0 pre)
        (_hsup : SupplyOkAt sevm (W 0) (W 0) ((pre.getStor sevm.currentTarget).get tokenSlot) T U
          0x17c 0x1c0)
        (_hburn : BurnOkAt sevm (W 0) (W 1) ((pre.getStor sevm.currentTarget).get tokenSlot)
          (Nat.toB256 (rliBurnAmt o)) U 0x85c 0x8e0)
        (_hpush : ∀ k : Fin 3, rliAmt sevm k.val ≠ 0 → CoinPushOkAt sevm (W (k + 1)) (W (k + 2))
          ((pre.getStor sevm.currentTarget).get (coinSlot k)) (rliAmt sevm k.val) U 0xaa0 0xb40)
        (_hskip : ∀ k : Fin 3, rliAmt sevm k.val = 0 → ∀ b, W (k + 1) b → W (k + 2) b)
        (_hG : costImbalance s (rliEnvW sevm T.toNat) (argV3 sevm 0) + 5 * U ≤ G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure + 3000 < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post),
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (rliEnvW sevm T.toNat)
            o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state ∧ W 4 post := by
  obtain ⟨-, s, hs, hck⟩ := pool_history_reached trace installed initial env target state
  exact ⟨s, hs, fun hcode hfork hstatic hdepth hlen hcd hsel hstep htok hcoin hpc hid hkeep hWc
    hWb hsup hburn hpush hskip hG hGm => removeLiquidityImbalance_live hcode hfork hstatic hdepth
    hlen hcd hsel hck hstep htok hcoin hpc hid hkeep hWc hWb hsup hburn hpush hskip hG hGm⟩

/-- **`remove_liquidity_one_coin` is live at every reachable state**
(`removeLiquidityOneCoin_live` after any configured history). -/
theorem pool_history_removeLiquidityOneCoin_live
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (checkpoint.state.getStor pool) s₀)
    (env : PoolTraceEnv trace pool s₀.coins s₀.token)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state) :
    ∃ s, PoolHistoryAt trace pool s₀ s ∧
      ∀ {o : Out} {i : Fin 3} {T : B256} {W W' W'' : Devm → Prop} {U G : Nat}
        (_hcode : sevm.code = code) (_hfork : CoveredFork sevm.benvStat.fork)
        (_hstatic : sevm.isStatic = false) (_hdepth : sevm.depth ≠ 0)
        (_hlen : 4 ≤ sevm.data.length) (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin)
        (_hi : i.val = (ocI sevm).toNat)
        (_hstep : step s (ocEnv sevm i T.toNat) (decodeCall sevm) = some o)
        (_htok : ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr)
        (_hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty) (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hWc : WClosed sevm W) (_hW'c : WClosed sevm W') (_hWb : W pre)
        (_hsup : SupplyOkAt sevm W W ((pre.getStor sevm.currentTarget).get tokenSlot) T U
          0x2bc 0x300)
        (_hburn : BurnOkAt sevm W W' ((pre.getStor sevm.currentTarget).get tokenSlot)
          (ocAmt sevm) U 0x31c 0x3a0)
        (_hW''c : WClosed sevm W'')
        (_hpush : CoinPushOkAt sevm W' W'' ((pre.getStor sevm.currentTarget).get (coinSlot i))
          (Nat.toB256 (ocPushAmt o)) U 0x540 0x5e0)
        (_hG : costOneCoin s (ocEnv sevm i T.toNat) (ocAmt sevm).toNat i + 3 * U ≤ G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure + 2000 < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ T' : Nat,
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (ocEnv sevm i T') o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state ∧ W'' post := by
  obtain ⟨-, s, hs, hck⟩ := pool_history_reached trace installed initial env target state
  exact ⟨s, hs, fun hcode hfork hstatic hdepth hlen hcd hsel hi hstep htok hcoin hpc hid hkeep hWc
    hW'c hWb hsup hburn hW''c hpush hG hGm => removeLiquidityOneCoin_live hcode hfork hstatic hdepth
    hlen hcd hsel hi hck hstep htok hcoin hpc hid hkeep hWc hW'c hWb hsup hburn hW''c hpush hG hGm⟩

end Wrappers

end Blanc.Lift.Curve3Pool
