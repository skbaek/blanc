import Blanc.Lift.Curve3Pool.HistoryLive
import Blanc.Lift.Curve3Pool.ExactMessage

/-!
# Curve 3pool: exact-gas liveness at every reachable state, at message entry (U6)

The exact twins of `HistoryLive.lean`'s wrappers. After any configured history, for a message
`msg` to the pool whose state is the future state, the replayed state `s` is chosen once
(`pool_history_reached`); then each entry's message-entry exact theorem (`ExactMessage.lean`)
applies at `s`: with every premise, the model's words and the closed cost `c` fixed at the base
message, for every `R` with the entry's headroom the message entered with the grant `R + c`
executes, ends with exactly `R` gas, and has the model's effect.

* `pool_history_exchange_live_exact`, `pool_history_addLiquidity_live_exact`,
  `pool_history_removeLiquidity_live_exact`, `pool_history_removeLiquidityImbalance_live_exact`,
  `pool_history_removeLiquidityOneCoin_live_exact`.

`exchange` calls no 3Crv function, so `pool_history_exchange_live_exact` is already its composed
statement.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.ExecutionTrace Blanc.StableSwapNewton

section Wrappers

variable {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {s₀ : State}

/-- **`remove_liquidity` is live at every reachable state, with exact gas at message entry**
(`removeLiquidity_msg_exact` after any configured history). -/
theorem pool_history_removeLiquidity_live_exact
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (checkpoint.state.getStor pool) s₀)
    (env : PoolTraceEnv trace pool s₀.coins s₀.token)
    {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state) :
    ∃ s, PoolHistoryAt trace pool s₀ s ∧
      ∀ {o : Out} {T : B256} {W : Nat → Devm → Prop} {U : Nat} (P : RLExactCalls)
        (_hcode : (initSevm msg).code = code)
        (_hfork : CoveredFork (initSevm msg).benvStat.fork)
        (_hstatic : (initSevm msg).isStatic = false)
        (_hdepth : (initSevm msg).depth ≠ 0)
        (_hlen : 4 ≤ (initSevm msg).data.length)
        (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selRemoveLiquidity)
        (_hstep : step s (rlEnv (initSevm msg) T) (decodeCall (initSevm msg)) = some o)
        (_htok : ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr)
        (_hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg))
        (_hWc : ∀ k, k ≤ 3 → WClosed (initSevm msg) (W k))
        (_hWb : W 0 (initDevm msg))
        (_hP : RLExactPremises (initSevm msg) (initDevm msg) T W U P),
        ∀ R, 167000 + 5 * U ≤ R →
          R + rlExactCost (initSevm msg) (initDevm msg) T P < 2 ^ 256 →
          (∀ post (exc : Exec 0 (initSevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P)))
              (initDevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P))) (.ok post)),
            PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
              ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
          ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P)))
              (initDevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P))) (.ok post),
            exec (initEvm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P))) =
              .ok post ∧
            post.gasLeft = R ∧
            RawEffect ⟨0, _, _, .ok post, exc⟩ post (rlEnv (initSevm msg) T) o ∧
            Checkpoint (post.getStor msg.currentTarget) o.state := by
  obtain ⟨-, s, hs, hck⟩ := pool_history_reached (sevm := initSevm msg) (pre := initDevm msg)
    trace installed initial env target state
  exact ⟨s, hs, fun P hcode hfork hstatic hdepth hlen hcd hsel hstep htok hcoin hpc hid hWc hWb hP =>
    removeLiquidity_msg_exact P hcode hfork hstatic hdepth hlen hcd hsel hck hstep htok hcoin hpc hid hWc hWb hP⟩

/-- **`exchange` is live at every reachable state, with exact gas at message entry**
(`exchange_msg_exact` after any configured history). -/
theorem pool_history_exchange_live_exact
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (checkpoint.state.getStor pool) s₀)
    (env : PoolTraceEnv trace pool s₀.coins s₀.token)
    {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state) :
    ∃ s, PoolHistoryAt trace pool s₀ s ∧
      ∀ {o : Out} {i j : Fin 3} {B1 B2 : B256} {W W' W'' : Devm → Prop} {U : Nat} (P : ExchangeExactCalls)
        (_hcode : (initSevm msg).code = code)
        (_hfork : CoveredFork (initSevm msg).benvStat.fork)
        (_hstatic : (initSevm msg).isStatic = false)
        (_hdepth : (initSevm msg).depth ≠ 0)
        (_hlen : 4 ≤ (initSevm msg).data.length)
        (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selExchange)
        (_hi : i.val = (exI (initSevm msg)).toNat)
        (_hj : j.val = (exJ (initSevm msg)).toNat)
        (_hstep : step s (exEnv (initSevm msg) i j (exBalOpt i B1) (exBalOpt i B2))
          (decodeCall (initSevm msg)) = some o)
        (_hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg))
        (_hWc : WClosed (initSevm msg) W)
        (_hW'c : WClosed (initSevm msg) W')
        (_hWb : W (initDevm msg))
        (_hbal : i = feeIndex →
          StaticWordCallProfile (initSevm msg) W W
            (((initDevm msg).getStor msg.currentTarget).get (coinSlot i))
            (balanceOfData msg.currentTarget) B1 U 0x3dc 0x24 0x440 P.balD1 P.balN1 ∧
          StaticWordCallProfile (initSevm msg) W' W'
            (((initDevm msg).getStor msg.currentTarget).get (coinSlot i))
            (balanceOfData msg.currentTarget) B2 U 0x71c 0x24 0x780 P.balD2 P.balN2)
        (_hpull : MutableCallProfile (initSevm msg) W W'
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot i))
          (transferFromSel ++ msg.caller.toB256.toBytes ++ msg.currentTarget.toB256.toBytes ++
            (exDx (initSevm msg)).toBytes) RawCallOk U 0x600 0x64 0x6c0 P.pullD P.pullN)
        (_hW''c : WClosed (initSevm msg) W'')
        (_hpush : MutableCallProfile (initSevm msg) W' W''
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot j))
          (transferSel ++ msg.caller.toB256.toBytes ++ (Nat.toB256 (exPushAmt o)).toBytes) RawCallOk U
          0xb60 0x44 0xc00 P.pushD P.pushN),
        ∃ (x0 x1 x2 : B256) (amp v : Nat),
          xpChk ⟨(balAt ((initDevm msg).getStor msg.currentTarget) 0).toNat,
            (balAt ((initDevm msg).getStor msg.currentTarget) 1).toNat,
            (balAt ((initDevm msg).getStor msg.currentTarget) 2).toNat⟩ =
              some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
          aChk s (initSevm msg).benvStat.time.toNat = some amp ∧
          (∃ (hi3 : (exI (initSevm msg)).toNat < 3) (hj3 : (exJ (initSevm msg)).toNat < 3),
            getYChk amp ⟨(exI (initSevm msg)).toNat, hi3⟩ ⟨(exJ (initSevm msg)).toNat, hj3⟩
              (exW3 x0 x1 x2 (exI (initSevm msg)).toNat + exCred (initSevm msg) B1 B2 *
                exRate (exI (initSevm msg)).toNat / exR0).toNat (V3.mk x0.toNat x1.toNat x2.toNat).get =
              some v) ∧
          ∀ R, 60000 + U ≤ R →
            costExchange (initSevm msg) (initDevm msg) s
              (exEnv (initSevm msg) i j (exBalOpt i B1) (exBalOpt i B2)) i j
              (exDx (initSevm msg)).toNat + 4 * U ≤
                R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v →
            R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v < 2 ^ 256 →
            (∀ post (exc : Exec 0 (initSevm (msg.withGas
                  (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v)))
                (initDevm (msg.withGas
                  (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v))) (.ok post)),
              PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
                ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
            ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas
                  (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v)))
                (initDevm (msg.withGas
                  (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v))) (.ok post),
              exec (initEvm (msg.withGas
                (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v))) = .ok post ∧
              post.gasLeft = R ∧ ∃ bp bq,
              pullIn (exEnv (initSevm msg) i j bp bq) i (exDx (initSevm msg)).toNat =
                pullIn (exEnv (initSevm msg) i j (exBalOpt i B1) (exBalOpt i B2)) i
                  (exDx (initSevm msg)).toNat ∧
              RawEffect ⟨0, _, _, .ok post, exc⟩ post (exEnv (initSevm msg) i j bp bq) o ∧
              Checkpoint (post.getStor msg.currentTarget) o.state ∧ W'' post := by
  obtain ⟨-, s, hs, hck⟩ := pool_history_reached (sevm := initSevm msg) (pre := initDevm msg)
    trace installed initial env target state
  exact ⟨s, hs, fun P hcode hfork hstatic hdepth hlen hcd hsel hi hj hstep hcoin hpc hid hWc hW'c hWb hbal hpull hW''c hpush =>
    exchange_msg_exact P hcode hfork hstatic hdepth hlen hcd hsel hi hj hck hstep hcoin hpc hid hWc hW'c hWb hbal hpull hW''c hpush⟩

/-- **`add_liquidity` is live at every reachable state, with exact gas at message entry**
(`addLiquidity_msg_exact` after any configured history). -/
theorem pool_history_addLiquidity_live_exact
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (checkpoint.state.getStor pool) s₀)
    (env : PoolTraceEnv trace pool s₀.coins s₀.token)
    {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state) :
    ∃ s, PoolHistoryAt trace pool s₀ s ∧
      ∀ {o : Out} {T B1 B2 : B256} {W : Nat → Devm → Prop} {U : Nat} (P : ALExactCalls)
        (_hcode : (initSevm msg).code = code)
        (_hfork : CoveredFork (initSevm msg).benvStat.fork)
        (_hstatic : (initSevm msg).isStatic = false)
        (_hdepth : (initSevm msg).depth ≠ 0)
        (_hlen : 4 ≤ (initSevm msg).data.length)
        (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selAddLiquidity)
        (_hstep : step s (alEnvW (initSevm msg) T.toNat B1.toNat B2.toNat) (decodeCall (initSevm msg)) =
          some o)
        (_htok : ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr)
        (_hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg))
        (_hWc : ∀ j, j ≤ 4 → WClosed (initSevm msg) (W j))
        (_hWb : W 0 (initDevm msg))
        (_hskip : ∀ k : Fin 3, alAmt (initSevm msg) k.val = 0 → ∀ b, W k b → W (k + 1) b)
        (_hP : ALExactPremises (initSevm msg) ((initDevm msg).getStor msg.currentTarget) T B1 B2
          (Nat.toB256 (alMintAmt o)) W U P),
        ∃ (amp v0 v1 v2 : Nat) (xa xb xc : V3) (f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256),
          aChk s (initSevm msg).benvStat.time.toNat = some amp ∧
          xpChk ⟨(alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2
              0).toNat,
            (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 1).toNat,
            (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2
              2).toNat⟩ = some xb ∧
          getDChk xb.get amp 1 = some v1 ∧
          (T ≠ 0 →
            xpChk ⟨(balAt ((initDevm msg).getStor msg.currentTarget) 0).toNat,
              (balAt ((initDevm msg).getStor msg.currentTarget) 1).toNat,
              (balAt ((initDevm msg).getStor msg.currentTarget) 2).toNat⟩ = some xa ∧
            getDChk xa.get amp 1 = some v0 ∧
            RliFeeIter (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot))
              (((initDevm msg).getStor msg.currentTarget).get adminFeeSlot) (Nat.toB256 v0)
              (Nat.toB256 v1) (balAt ((initDevm msg).getStor msg.currentTarget) 0)
              (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 0)
              f0 s0 x0 ∧
            RliFeeIter (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot))
              (((initDevm msg).getStor msg.currentTarget).get adminFeeSlot) (Nat.toB256 v0)
              (Nat.toB256 v1) (balAt ((initDevm msg).getStor msg.currentTarget) 1)
              (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 1)
              f1 s1 x1 ∧
            RliFeeIter (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot))
              (((initDevm msg).getStor msg.currentTarget).get adminFeeSlot) (Nat.toB256 v0)
              (Nat.toB256 v1) (balAt ((initDevm msg).getStor msg.currentTarget) 2)
              (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 2)
              f2 s2 x2 ∧
            xpChk ⟨x0.toNat, x1.toNat, x2.toNat⟩ = some xc ∧ getDChk xc.get amp 1 = some v2) ∧
          ∀ R, 100000 + 5 * U ≤ R →
          costAddLiquidity s (alEnvW (initSevm msg) T.toNat B1.toNat B2.toNat) (argV3 (initSevm msg) 0) +
              7 * U ≤
            R + alExactCost (initSevm msg) (initDevm msg) P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0
              s1 s2 x0 x1 x2 →
          R + alExactCost (initSevm msg) (initDevm msg) P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1
              s2 x0 x1 x2 + 6000 < 2 ^ 256 →
          (∀ post (exc : Exec 0 (initSevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) P
                amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2)))
              (initDevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) P amp T B1 B2 xa xb
                xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) (.ok post)),
            PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
              ∀ c' ∈ Exec.childFrames exc, c'.post.getCode 4 = c'.pre.getCode 4) →
          ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) P
                amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2)))
              (initDevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) P amp T B1 B2 xa xb
                xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) (.ok post),
            exec (initEvm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) P amp T B1 B2 xa
              xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) = .ok post ∧
            post.gasLeft = R ∧
            ∃ e : Env, e.supply = some T.toNat ∧ step s e (decodeCall (initSevm msg)) = some o ∧
              RawEffect ⟨0, _, _, .ok post, exc⟩ post e o ∧
              Checkpoint (post.getStor msg.currentTarget) o.state := by
  obtain ⟨-, s, hs, hck⟩ := pool_history_reached (sevm := initSevm msg) (pre := initDevm msg)
    trace installed initial env target state
  exact ⟨s, hs, fun P hcode hfork hstatic hdepth hlen hcd hsel hstep htok hcoin hpc hid hWc hWb hskip hP =>
    addLiquidity_msg_exact P hcode hfork hstatic hdepth hlen hcd hsel hck hstep htok hcoin hpc hid hWc hWb hskip hP⟩

/-- **`remove_liquidity_imbalance` is live at every reachable state, with exact gas at message entry**
(`removeLiquidityImbalance_msg_exact` after any configured history). -/
theorem pool_history_removeLiquidityImbalance_live_exact
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (checkpoint.state.getStor pool) s₀)
    (env : PoolTraceEnv trace pool s₀.coins s₀.token)
    {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state) :
    ∃ s, PoolHistoryAt trace pool s₀ s ∧
      ∀ {o : Out} {T : B256} {W : Nat → Devm → Prop} {U : Nat} (P : RLIExactCalls)
        (_hcode : (initSevm msg).code = code)
        (_hfork : CoveredFork (initSevm msg).benvStat.fork)
        (_hstatic : (initSevm msg).isStatic = false)
        (_hdepth : (initSevm msg).depth ≠ 0)
        (_hlen : 4 ≤ (initSevm msg).data.length)
        (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selRemoveLiquidityImbalance)
        (_hstep : step s (rliEnvW (initSevm msg) T.toNat) (decodeCall (initSevm msg)) = some o)
        (_htok : ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr)
        (_hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg))
        (_hWc : ∀ j, j ≤ 4 → WClosed (initSevm msg) (W j))
        (_hWb : W 0 (initDevm msg))
        (_hP : RLIExactPremises (initSevm msg) ((initDevm msg).getStor msg.currentTarget) T
          (Nat.toB256 (rliBurnAmt o)) W U P)
        (_hskip : ∀ k : Fin 3, rliAmt (initSevm msg) k.val = 0 → ∀ b, W (k + 1) b → W (k + 2) b),
        ∃ w : RliWords, RliWordsPin (initSevm msg) (initDevm msg) s w ∧
          ∀ R, 66000 + 3 * U ≤ R →
            costImbalance s (rliEnvW (initSevm msg) T.toNat) (argV3 (initSevm msg) 0) + 5 * U ≤
              R + rliExactCost (initSevm msg) (initDevm msg) P T w →
            R + rliExactCost (initSevm msg) (initDevm msg) P T w + 3000 < 2 ^ 256 →
            (∀ post (exc : Exec 0
                (initSevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) P T w)))
                (initDevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) P T w)))
                (.ok post)),
              PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
                ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
            ∃ post, ∃ exc : Exec 0
                (initSevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) P T w)))
                (initDevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) P T w)))
                (.ok post),
              exec (initEvm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) P T w))) =
                .ok post ∧
              post.gasLeft = R ∧
              RawEffect ⟨0, _, _, .ok post, exc⟩ post (rliEnvW (initSevm msg) T.toNat) o ∧
              Checkpoint (post.getStor msg.currentTarget) o.state ∧ W 4 post := by
  obtain ⟨-, s, hs, hck⟩ := pool_history_reached (sevm := initSevm msg) (pre := initDevm msg)
    trace installed initial env target state
  exact ⟨s, hs, fun P hcode hfork hstatic hdepth hlen hcd hsel hstep htok hcoin hpc hid hWc hWb hP hskip =>
    removeLiquidityImbalance_msg_exact P hcode hfork hstatic hdepth hlen hcd hsel hck hstep htok hcoin hpc hid hWc hWb hP hskip⟩

/-- **`remove_liquidity_one_coin` is live at every reachable state, with exact gas at message entry**
(`removeLiquidityOneCoin_msg_exact` after any configured history). -/
theorem pool_history_removeLiquidityOneCoin_live_exact
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (checkpoint.state.getStor pool) s₀)
    (env : PoolTraceEnv trace pool s₀.coins s₀.token)
    {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state) :
    ∃ s, PoolHistoryAt trace pool s₀ s ∧
      ∀ {o : Out} {i : Fin 3} {T : B256} {W W' W'' : Devm → Prop} {U : Nat} (P : OCExactCalls)
        (_hcode : (initSevm msg).code = code)
        (_hfork : CoveredFork (initSevm msg).benvStat.fork)
        (_hstatic : (initSevm msg).isStatic = false)
        (_hdepth : (initSevm msg).depth ≠ 0)
        (_hlen : 4 ≤ (initSevm msg).data.length)
        (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selRemoveLiquidityOneCoin)
        (_hi : i.val = (ocI (initSevm msg)).toNat)
        (_hstep : step s (ocEnv (initSevm msg) i T.toNat) (decodeCall (initSevm msg)) = some o)
        (_htok : ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr)
        (_hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg))
        (_hWc : WClosed (initSevm msg) W)
        (_hW'c : WClosed (initSevm msg) W')
        (_hWb : W (initDevm msg))
        (_hW''c : WClosed (initSevm msg) W'')
        (_hP : OCExactPremises (initSevm msg) (initDevm msg) T (Nat.toB256 (ocPushAmt o)) W W' W'' U P),
        ∃ (amp : Nat) (x0 x1 x2 D0 y r0 r1 r2 y2 : B256) (hi3 : (ocI (initSevm msg)).toNat < 3),
          aChk s (initSevm msg).benvStat.time.toNat = some amp ∧
          xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
          getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1 = some D0.toNat ∧
          getYDChk amp ⟨(ocI (initSevm msg)).toNat, hi3⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get
            (D0 - ocAmt (initSevm msg) * D0 / T).toNat = some y.toNat ∧
          CwStep (Bytes.toB256 [0] = ocI (initSevm msg)) x0 (D0 - ocAmt (initSevm msg) * D0 / T) D0 y
            (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot)) x0 r0 ∧
          CwStep (Bytes.toB256 [1] = ocI (initSevm msg)) x1 (D0 - ocAmt (initSevm msg) * D0 / T) D0 y
            (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot)) x1 r1 ∧
          CwStep (Bytes.toB256 [2] = ocI (initSevm msg)) x2 (D0 - ocAmt (initSevm msg) * D0 / T) D0 y
            (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot)) x2 r2 ∧
          getYDChk amp ⟨(ocI (initSevm msg)).toNat, hi3⟩ (V3.mk r0.toNat r1.toNat r2.toNat).get
            (D0 - ocAmt (initSevm msg) * D0 / T).toNat = some y2.toNat ∧
          ∀ R, 131000 + 3 * U ≤ R →
          R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2 + 2000 <
            2 ^ 256 →
          (∀ post (exc : Exec 0 (initSevm (msg.withGas
                (R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2)))
              (initDevm (msg.withGas
                (R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2)))
              (.ok post)),
            PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
              ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
          ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas
                (R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2)))
              (initDevm (msg.withGas
                (R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2)))
              (.ok post),
            exec (initEvm (msg.withGas
              (R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2))) =
              .ok post ∧
            post.gasLeft = R ∧ ∃ T' : Nat,
            RawEffect ⟨0, _, _, .ok post, exc⟩ post (ocEnv (initSevm msg) i T') o ∧
            Checkpoint (post.getStor msg.currentTarget) o.state ∧ W'' post := by
  obtain ⟨-, s, hs, hck⟩ := pool_history_reached (sevm := initSevm msg) (pre := initDevm msg)
    trace installed initial env target state
  exact ⟨s, hs, fun P hcode hfork hstatic hdepth hlen hcd hsel hi hstep htok hcoin hpc hid hWc hW'c hWb hW''c hP =>
    removeLiquidityOneCoin_msg_exact P hcode hfork hstatic hdepth hlen hcd hsel hi hck hstep htok hcoin hpc hid hWc hW'c hWb hW''c hP⟩

end Wrappers

end Blanc.Lift.Curve3Pool
