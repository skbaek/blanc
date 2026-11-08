# Deployed-bytecode claim map: Curve 3pool StableSwap

## 5.11 Curve 3pool StableSwap: frame, history, liveness, arithmetic, and composition with 3Crv

The pool's `get_D` and `get_y` Newton loops are not exact integer optima, and the pool's virtual
price is not monotone at a fixed amplification. The statements below say what the bytes compute,
where the loops and the monotonicity fail, and what the composed history gives. A reader who needs
a monotonicity claim should read Section 7 items 45 to 47 first.

**What "the environment" means.** The functional model takes as input an environment `e`: the
header time, the caller, the value, the coins' `balanceOf(self)` readings and transfer outcomes,
and 3Crv's `totalSupply()`, `mint` and `burnFrom` outcomes. In the frame and history statements
below `e` is **what the frame observed from its own children**
(`Blanc.Lift.Curve3Pool.EnvOf` (`Blanc/Lift/Curve3Pool/Observe.lean:153`)), not an assumption: the
supply is the reply of the frame's first `totalSupply()` child, a success flag is a child that was
called with that selector and answered. One escape is part of that definition: a coin or token
answer is constrained only when its target enters a code frame (`framed`); for a target that is an
undelegated precompile, which leaves no child, the corresponding answer in `e` is unconstrained
(Section 7 item 54). The ENV premises of the tables say how the children behave (keep storage;
answer; fit a gas allowance), not what the model reads.

**Per-call callee premises.** A liveness theorem takes, for each state-changing or balance-reading
call site of the frame, a premise of one of the shapes `SupplyOkAt`, `CoinBalOkAt`, `CoinPushOkAt`,
`CoinPullOkAt`, `MintOkAt`, `BurnOkAt` (all instances of `StaticWordOkAt` or `MutCallOkAt`, in
`Blanc/Lift/Curve3Pool/LivePremises.lean`). Such a premise says: from **every** world `W` that holds
at the call site (an invariant the caller chooses), given at least `U` gas, the `CALL` (value 0) or
`STATICCALL` with exactly the pool's calldata for that site runs and succeeds; its reply passes
Vyper's `raw_call` success test (`RawCallOk`: empty, or a nonzero first word) or, for `totalSupply()`
and `balanceOf(self)`, is the named 32-byte word; the pool's storage is unchanged; at most `U` gas is
used; and the world left is in the next invariant `W'`. `WClosed` asks each invariant to survive the
pool's own steps. A state-changing call with a positive amount must land in a **fresh** invariant,
so a theorem takes a chain `W 0 → W 1 → …`, one step per state-changing call. Every liveness
theorem also takes the per-execution keep premise: for every execution of the frame from its entry,
every direct child keeps the pool's storage (`PoolCallsKeep`) and the code at address 4; it ranges
over the frame's own executions, not over arbitrary machines.

**Exact call profiles.** The exact-gas rows below take, at the same call sites, the stronger
premises `StaticWordCallProfile` and `MutableCallProfile`
[`Blanc.Lift.StaticWordCallProfile` (`Blanc/Lift/ExactCallProfile.lean:93`),
`Blanc.Lift.MutableCallProfile` (`Blanc/Lift/ExactCallProfile.lean:104`)]. Each fixes, before the
call's input gas, a debit function and a successor function of the caller's state, stack and
memory. From every world of `W`, given at least `U` gas, the call then runs with the reply,
storage and next-invariant conditions above, its whole charge is exactly the debit (at most `U`),
and the state it leaves is the successor except for its gas. The debit and successor functions
are parameters of the theorems. For a coin they are part of the environment premise: a coin's
gas use is the coin's, not a Blanc fact. For 3Crv the composed rows supply 3Crv's own.

**Frame and history**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| A successful pc-0 run of the installed 3pool runtime, entered fresh (empty stack and memory) at a pool storage that is a `Checkpoint` of a model state `s`, is accepted by the model's `step` on its decoded call at some environment `e` it observed, with the frame's raw effect: the post storage is a `Checkpoint` of the model's output state; the logs are the entry logs, then the children's logs, then the model's events; the return data is the model's; for a non-static frame the frame's state-changing children are the model's calls encoded at the stored coin and token addresses (for every target that enters a code frame); the coins and token are unchanged. All 38 selectors | `Blanc.Lift.Curve3Pool.pool_frame_refines_env` (`Blanc/Lift/Curve3Pool/Safe.lean:138`); the form the history consumes `Blanc.Lift.Curve3Pool.pool_frame_refines` (`Blanc/Lift/Curve3Pool/Safe.lean:162`); the pure relation `Blanc.Lift.Curve3Pool.rawEffect_refines` (`Blanc/Lift/Curve3Pool/Refine.lean:239`) | Frame / safety | CODE (the frame's code is the certified runtime); covered fork; calldata length and gas below 2^256; the target account holds code; INIT `Checkpoint`; ENV `PoolFrameEnv`: every direct child keeps the pool's storage, every child that runs at a coin (and is not 3Crv) keeps 3Crv's storage, every child keeps the code at address 4, the identity precompile at 4 is warm, undelegated and enabled (`IdReady`), and no coin and not the token is a precompile | The coin and 3Crv answers enter through `e`; the walks of the individual selectors are not restated here |
| Calldata shorter than four bytes, or a selector among none of the 38, has **no** successful run. A successful, committing static frame writes no storage at any address and emits no logs | `Blanc.Lift.Curve3Pool.pool_other_fails` (`Blanc/Lift/Curve3Pool/Walk/Fallback.lean:83`); `Blanc.Lift.Curve3Pool.pool_static_noEffect` (`Blanc/Lift/Curve3Pool/Walk/Fallback.lean:109`) | Frame / safety | CODE; a fresh entry with calldata and gas below 2^256 (fallback); a covered fork, code at the target and `post.error = none` (static) | A static frame's return bytes are the model's by the row above |
| After any configured history from a checkpoint at which the pool holds the certified runtime and its storage is a `Checkpoint` of `s₀`: the runtime is still installed; the outermost settlement-committed non-static pool frames, in trace order, are authentic invocations (committed, non-static, pc 0, at the pool, each with the environment it observed) whose subtrees flatten exactly to the settlement-committed non-static pool frames of the trace; they replay through the model's `step` from `s₀`, each accepted with its raw effect, to a state of which the end pool storage is a `Checkpoint`, with coins and token unchanged | `Blanc.Lift.Curve3Pool.pool_history_committed_derived` (`Blanc/Lift/Curve3Pool/History.lean:130`) in its bundled form `Blanc.Lift.Curve3Pool.pool_history_committed_env` (`Blanc/Lift/Curve3Pool/History.lean:217`); the replay form over any entry condition `Blanc.Lift.Curve3Pool.pool_history_committed_with` (`Blanc/Lift/Curve3Pool/Ladder.lean:401`) | History / safety, exact extraction | CODE (installed at the checkpoint); INIT `Checkpoint`; `PoolTraceEnv`: per frame, every direct child of an admitted pool frame keeps the pool's storage and every coin child keeps 3Crv's storage (`callbacks`, an ENV premise); trace-local: the checkpoint's coins and token are not precompiles under any pool frame's rules, the identity precompile has no code at the checkpoint, no authorization of any transaction recovers to it, no CREATE frame targets it, and no system frame targets the pool. No hash premise | Rolled-back frames are not in the replay; static frames contribute nothing. The fresh-entry, calldata, gas and identity-readiness conditions of the frame row are derived from the trace, not assumed |
| The same from the deployment: the checkpoint's pool code is the runtime and its storage is exactly what the recorded deployment leaves (`deployedStor`), replayed from the constructor's model state | `Blanc.Lift.Curve3Pool.pool_history_initialized` (`Blanc/Lift/Curve3Pool/History.lean:162`) | History / safety | as above, with `PoolTraceEnv` at the constructor's coins and token | The deployment row below |

**Liveness, sufficient gas** (sufficient-gas bounds with a closed cost, not exact-gas equalities; the exact-gas forms are the next table; Section 7 item 48)

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| After any configured history, at a pool frame of the future state (fresh machine holding gas `G`, non-static, depth not 0, selector `exchange`): if the model accepts the call at the replayed state under the frame's balance readings and `G ≥ costExchange … + 4·U`, then the frame executes successfully, its raw effect is the model's `exchange` step at an environment whose credited pull equals the model's `pullIn` under the premised readings, the post pool storage is a `Checkpoint` of the model's output, and the post world is in the last invariant | `Blanc.Lift.Curve3Pool.pool_history_exchange_live` (`Blanc/Lift/Curve3Pool/HistoryLive.lean:71`) over the frame theorem `Blanc.Lift.Curve3Pool.exchange_live` (`Blanc/Lift/Curve3Pool/ExchangeLive.lean:79`) | History and frame / live | the history premises of the history row; no coin is a precompile; identity readiness; the per-execution keep premise; `CoinPullOkAt` for the input coin and `CoinPushOkAt` for the output coin over a chain `W → W' → W''` (a `WClosed` triple); for the **fee-on-transfer index 2 only**, two `CoinBalOkAt` readings `B1`, `B2` around the pull; the gas premise with the per-call allowance `U`; `gasMeasure < 2^256` | `exchange` calls no 3Crv function, so this pool-level row is also its composed statement. `costExchange` is a function of the model state and arguments, `0` where the model reverts. The index-2 path is not instantiated (Section 7 item 53) |
| The same for `add_liquidity`, `remove_liquidity`, `remove_liquidity_imbalance` and `remove_liquidity_one_coin`, with the 3Crv calls taken as premises. The conclusions: `remove_liquidity` and `remove_liquidity_imbalance` give the raw effect at the premised supply; `remove_liquidity_imbalance` and `remove_liquidity_one_coin` also put the post world in the last invariant; `remove_liquidity_one_coin` gives the raw effect at **some** supply reading `T'`, not pinned to the premised `T`; `add_liquidity` gives **some** environment `e` whose supply is the premised `T` and at which the model accepts the call, and the raw effect at `e` | `Blanc.Lift.Curve3Pool.pool_history_addLiquidity_live` (`Blanc/Lift/Curve3Pool/HistoryLive.lean:119`), `Blanc.Lift.Curve3Pool.pool_history_removeLiquidity_live` (`Blanc/Lift/Curve3Pool/HistoryLive.lean:170`), `Blanc.Lift.Curve3Pool.pool_history_removeLiquidityImbalance_live` (`Blanc/Lift/Curve3Pool/HistoryLive.lean:209`), `Blanc.Lift.Curve3Pool.pool_history_removeLiquidityOneCoin_live` (`Blanc/Lift/Curve3Pool/HistoryLive.lean:252`); frame forms `Blanc.Lift.Curve3Pool.addLiquidity_live` (`Blanc/Lift/Curve3Pool/AddLiquidityLive.lean:161`), `Blanc.Lift.Curve3Pool.removeLiquidity_live` (`Blanc/Lift/Curve3Pool/RemoveLiquidityLiveness.lean:124`), `Blanc.Lift.Curve3Pool.removeLiquidityImbalance_live` (`Blanc/Lift/Curve3Pool/RemoveImbalanceLive.lean:70`), `Blanc.Lift.Curve3Pool.removeLiquidityOneCoin_live` (`Blanc/Lift/Curve3Pool/OneCoinLive.lean:72`) | History and frame / live | as the row above (including the per-execution keep premise), plus the 3Crv call premises `SupplyOkAt` / `SupplyOk`, `MintOkAt`, `BurnOkAt` / `BurnOkTo` over the same kind of chain; a coin premise per coin call (`CoinPullOkAt` for `add_liquidity`, `CoinPushOkAt` for the withdrawals; `add_liquidity` and `remove_liquidity_imbalance` skip a coin whose amount is zero; `add_liquidity`'s fee coin also takes the two `CoinBalOkAt` readings); gas `costAddLiquidity … + 7·U`, `167000 + 5·U` (`remove_liquidity`), `costImbalance … + 5·U`, `costOneCoin … + 3·U` | The 3Crv premises are discharged in the composed row below. Section 7 item 54 on the existential conclusions |
| **Composed with 3Crv.** At a pool frame of the future state of a configured history from a joint checkpoint, `remove_liquidity`, `add_liquidity`, `remove_liquidity_imbalance` and `remove_liquidity_one_coin` execute under the same gas bounds and with the same conclusions, with every 3Crv call premise discharged by the deployed 3Crv: 3Crv's state is stated **once, at the frame's entry** | `Blanc.Composition.Curve3Pool3CrvHeadlines.pool_3crv_removeLiquidity_live_entry` (`Blanc/Composition/Curve3Pool3CrvHeadlines.lean:163`), `Blanc.Composition.Curve3Pool3CrvHeadlines.pool_3crv_addLiquidity_live_entry` (`Blanc/Composition/Curve3Pool3CrvHeadlines.lean:237`), `Blanc.Composition.Curve3Pool3CrvHeadlines.pool_3crv_removeLiquidityImbalance_live_entry` (`Blanc/Composition/Curve3Pool3CrvHeadlines.lean:332`), `Blanc.Composition.Curve3Pool3CrvHeadlines.pool_3crv_removeLiquidityOneCoin_live_entry` (`Blanc/Composition/Curve3Pool3CrvHeadlines.lean:411`) | History and frame / live | the history premises (`JointCheckpoint`, both runtimes installed, `FreshKeys` over 3Crv's touched keys, `PoolTraceEnv`, `pool ≠ systemAddress`); at the frame: `C3Ready` (derived from the history: 3Crv's code at the token, the pool is 3Crv's minter, the pool's token slot names it); the per-execution keep premise; 3Crv's supply word at entry is `T`; `BurnFits` (withdrawals) or `MintFits` (`add_liquidity`) at 3Crv's entry storage; a **coin world chain** `V 0 → V 1 → …` of `WClosed` invariants that do not read 3Crv's storage (`C3Blind`), with `CoinPushOkAt` or `CoinPullOkAt` per coin over worlds that pin 3Crv's storage (`C3With`); `U ≥ 70000` | Section 7 items 42, 43 and 50. 3Crv's costs enter through `Blanc.Composition.Curve3PoolCalleeLive.c3crv_supplyOkAt` (`Blanc/Composition/Curve3PoolCalleeLive.lean:596`) and its siblings for `mint` and `burnFrom`, built on 3Crv's cost bounds such as `Blanc.Lift.Curve3Crv.live_totalSupply_le` (`Blanc/Lift/Curve3Crv/CostBounds.lean:84`) |
| **The callee premises are satisfiable.** With `Token20` coins and the deployed 3Crv, world chains exist that satisfy every **callee** premise (coin, supply, mint and burn calls) of the four frame theorems at `U = 80000` | `Blanc.Composition.Curve3Pool3CrvInstance.removeLiquidity_premises_satisfiable` (`Blanc/Composition/Curve3Pool3CrvLiveWitness.lean:126`), `Blanc.Composition.Curve3Pool3CrvInstance.addLiquidity_premises_satisfiable` (`Blanc/Composition/Curve3Pool3CrvLiveWitness.lean:196`), `Blanc.Composition.Curve3Pool3CrvInstance.removeLiquidityImbalance_premises_satisfiable` (`Blanc/Composition/Curve3Pool3CrvLiveWitness.lean:301`), `Blanc.Composition.Curve3Pool3CrvInstance.removeLiquidityOneCoin_premises_satisfiable` (`Blanc/Composition/Curve3Pool3CrvLiveWitness.lean:369`) | Witness / conditional | the coins hold `Token20`'s code and their ledgers cover the moves (`T20MoveFits`, `T20PullFits`), 3Crv holds its code with supply `T` and accepts the burn or mint, the accounts involved are distinct, not precompiles and not the pool | These witnesses discharge the callee premises only: not the per-execution keep premise, not the model step, and not agreement of the amounts with the model's outputs. The end-to-end instances below discharge all of them at one concrete entry each. None of the four `_live_entry` theorems is itself instantiated |

**Liveness, exact gas** (the sufficient-gas rows above remain, unchanged; Section 7 items 48 and 53)

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| At a pool frame whose storage is a `Checkpoint` of `s`, for each of the five entries: if the model accepts the call and every call of the frame is an exact call profile with the call data `P`, then a closed cost `c` is fixed before any residual gas, and for every residual `R` above the entry's headroom the frame entered with `R + c` has an actual successful execution with `post.gasLeft = R` exactly and the conclusion of the entry's sufficient-gas frame theorem (the same raw effect and `Checkpoint`, and where that theorem has them the post invariant and the existential environment). For `exchange`, `add_liquidity`, `remove_liquidity_imbalance` and `remove_liquidity_one_coin`, `c` also reads model words (`_A()`, the scaled balances, the checked `get_D`, `get_y` and `get_y_D` results, the fee-loop words), which the statement fixes, before `R`, by the model's own checks (`aChk`, `xpChk`, `getDChk`, `getYChk`, `getYDChk`, `RliFeeIter`, `CwStep`) | `Blanc.Lift.Curve3Pool.removeLiquidity_live_exact` (`Blanc/Lift/Curve3Pool/RemoveLiquidityExactFrame.lean:81`), `Blanc.Lift.Curve3Pool.exchange_live_exact` (`Blanc/Lift/Curve3Pool/ExchangeExactLive.lean:31`), `Blanc.Lift.Curve3Pool.addLiquidity_live_exact` (`Blanc/Lift/Curve3Pool/AddLiquidityExactFrame.lean:69`), `Blanc.Lift.Curve3Pool.removeLiquidityImbalance_live_exact` (`Blanc/Lift/Curve3Pool/RemoveLiquidityImbalanceExactFrame.lean:78`), `Blanc.Lift.Curve3Pool.removeLiquidityOneCoin_live_exact` (`Blanc/Lift/Curve3Pool/OneCoinExactFrame.lean:42`) | Frame / live, exact gas | the sufficient-gas frame row's premises, with each call premise replaced by its exact profile (`RLExactPremises`, `ALExactPremises`, `RLIExactPremises`, `OCExactPremises`; for `exchange` the input coin's `transferFrom`, the output coin's `transfer` and, at the fee-on-transfer index 2, the two `balanceOf(self)` profiles); the per-execution keep premise at the entry gas `R + c`; headroom `167000 + 5·U ≤ R` (`remove_liquidity`), `60000 + U ≤ R` (`exchange`), `100000 + 5·U ≤ R` (`add_liquidity`), `66000 + 3·U ≤ R` (`remove_liquidity_imbalance`), `131000 + 3·U ≤ R` (`remove_liquidity_one_coin`), and for `exchange`, `add_liquidity` and `remove_liquidity_imbalance` also the sufficient-gas row's bound at the entry gas (`costExchange … + 4·U ≤ R + c` and its siblings); the entry's gas measure below 2^256 (with 6000, 3000 and 2000 to spare for `add_liquidity`, `remove_liquidity_imbalance` and `remove_liquidity_one_coin`) | The closed costs are `Blanc.Lift.Curve3Pool.rlExactCost` (`Blanc/Lift/Curve3Pool/Walk/RemoveLiquidityExactSchedule.lean:235`), `Blanc.Lift.Curve3Pool.exExactCost` (`Blanc/Lift/Curve3Pool/Walk/ExchangeExactWalk.lean:735`), `Blanc.Lift.Curve3Pool.alExactCost` (`Blanc/Lift/Curve3Pool/AddLiquidityExactFrame.lean:34`), `Blanc.Lift.Curve3Pool.rliExactCost` (`Blanc/Lift/Curve3Pool/Walk/RliExactSchedule.lean:271`) and `Blanc.Lift.Curve3Pool.ocExactCost` (`Blanc/Lift/Curve3Pool/Walk/OneCoinExactSchedule.lean:198`): finite sums of stage charges at canonical intermediate states, functions of the entry, of `P` (the profiles' debit and successor functions) and of the pinned words. None reads the residual gas, and none is existential. Headroom and the no-wrap bound are separate premises, not part of `c`. The effect is the sufficient-gas theorem's at the same entry gas: an entry has one execution result |
| The same at a message `msg` to the pool: the premises, the model words and `c` are fixed at the base message's initial frame `(initSevm msg, initDevm msg)`; then for every `R` with the same headroom, the message with its gas grant replaced by `R + c`, `msg.withGas (R + c)`, executes (`exec (initEvm (msg.withGas (R + c))) = .ok post`) with `post.gasLeft = R` and the frame theorem's conclusion | `Blanc.Lift.Curve3Pool.removeLiquidity_msg_exact` (`Blanc/Lift/Curve3Pool/ExactMessage.lean:30`), `Blanc.Lift.Curve3Pool.exchange_msg_exact` (`Blanc/Lift/Curve3Pool/ExactMessage.lean:73`), `Blanc.Lift.Curve3Pool.addLiquidity_msg_exact` (`Blanc/Lift/Curve3Pool/ExactMessage.lean:164`), `Blanc.Lift.Curve3Pool.removeLiquidityImbalance_msg_exact` (`Blanc/Lift/Curve3Pool/ExactMessage.lean:259`), `Blanc.Lift.Curve3Pool.removeLiquidityOneCoin_msg_exact` (`Blanc/Lift/Curve3Pool/ExactMessage.lean:315`) | Message / live, exact gas | the frame row's premises at the base message's initial frame; the per-execution keep premise at the grant `R + c`; the same headroom; `R + c`, with the frame's margin, below 2^256 | `msg.withGas` replaces only the message's `gas` field. It is declared in Blanc, not by Jaune (`Blanc/Lift/StaticGasMessage.lean`). The premises and `c` are carried across the grant, so `c` is the same at every grant; no execution is carried across gas |
| After any configured history, for a message to the pool whose state is the future state: the replayed state `s` is chosen, separately in each theorem, before that entry's premises, and each entry's message-level exact form holds at `s` | `Blanc.Lift.Curve3Pool.pool_history_removeLiquidity_live_exact` (`Blanc/Lift/Curve3Pool/HistoryLiveExact.lean:32`), `Blanc.Lift.Curve3Pool.pool_history_exchange_live_exact` (`Blanc/Lift/Curve3Pool/HistoryLiveExact.lean:77`), `Blanc.Lift.Curve3Pool.pool_history_addLiquidity_live_exact` (`Blanc/Lift/Curve3Pool/HistoryLiveExact.lean:161`), `Blanc.Lift.Curve3Pool.pool_history_removeLiquidityImbalance_live_exact` (`Blanc/Lift/Curve3Pool/HistoryLiveExact.lean:248`), `Blanc.Lift.Curve3Pool.pool_history_removeLiquidityOneCoin_live_exact` (`Blanc/Lift/Curve3Pool/HistoryLiveExact.lean:302`) | History and message / live, exact gas | the history premises of the history row, then the message row's | `exchange` calls no 3Crv function, so `pool_history_exchange_live_exact` is also its composed statement. In the other four, 3Crv's calls are exact profiles taken as premises; the composed row below discharges them |
| **Composed with 3Crv.** At a message to the pool at the future state of a configured history from a joint checkpoint, `remove_liquidity`, `add_liquidity`, `remove_liquidity_imbalance` and `remove_liquidity_one_coin` execute with exact gas as in the history row, with 3Crv's `totalSupply()`, `mint` and `burnFrom` calls answered by the deployed 3Crv's own exact profiles, so no 3Crv call-profile premise remains (3Crv's supply word and `BurnFits`/`MintFits` are stated once, at the entry) | `Blanc.Composition.Curve3Pool3CrvHeadlinesExact.pool_3crv_removeLiquidity_live_exact` (`Blanc/Composition/Curve3Pool3CrvHeadlinesExact.lean:40`), `Blanc.Composition.Curve3Pool3CrvHeadlinesExact.pool_3crv_addLiquidity_live_exact` (`Blanc/Composition/Curve3Pool3CrvHeadlinesExact.lean:112`), `Blanc.Composition.Curve3Pool3CrvHeadlinesExact.pool_3crv_removeLiquidityImbalance_live_exact` (`Blanc/Composition/Curve3Pool3CrvHeadlinesExact.lean:239`), `Blanc.Composition.Curve3Pool3CrvHeadlinesExact.pool_3crv_removeLiquidityOneCoin_live_exact` (`Blanc/Composition/Curve3Pool3CrvHeadlinesExact.lean:323`) | History and message / live, exact gas | the sufficient-gas composed row's premises (the joint history premises; `C3Ready`, derived; 3Crv's supply word `T` and `BurnFits` or `MintFits` at the entry; the coin world chain `V` with `C3Blind` and `C3With`; `U ≥ 70000`), with each coin call an exact profile whose debit and successor functions are parameters; the per-execution keep premise at the grant; the message row's headroom and no-wrap bound | `c` is the entry's closed cost at 3Crv's named call data (`Blanc.Composition.Curve3Pool3CrvExactAssembly.rlC3Calls` (`Blanc/Composition/Curve3Pool3CrvExactAssembly.lean:38`) and its siblings), built from `Blanc.Composition.Curve3PoolCalleeExactProfiles.c3crv_supplyProfile` (`Blanc/Composition/Curve3PoolCalleeExactProfiles.lean:126`), `Blanc.Composition.Curve3PoolCalleeExactProfiles.c3crv_mintProfile` (`Blanc/Composition/Curve3PoolCalleeExactProfiles.lean:420`) and `Blanc.Composition.Curve3PoolCalleeExactProfiles.c3crv_burnProfile` (`Blanc/Composition/Curve3PoolCalleeExactProfiles.lean:463`). The coin profiles stay environment premises. None of the four is instantiated end to end |
| **The exact premise bundles are satisfiable.** With `Token20` coins and the deployed 3Crv's own exact profiles, each frame theorem's exact premise bundle (for `exchange`, its three profiles) holds at `U = 80000` for some call data `P`, for the four 3Crv-calling entries along the world chains of the sufficient-gas witnesses and for `exchange`, which has no sufficient-gas callee witness, along its own two coin worlds | `Blanc.Composition.Curve3Pool3CrvInstance.removeLiquidity_exactPremises_satisfiable` (`Blanc/Composition/Curve3Pool3CrvExactWitness.lean:30`), `Blanc.Composition.Curve3Pool3CrvInstance.addLiquidity_exactPremises_satisfiable` (`Blanc/Composition/Curve3Pool3CrvExactWitness.lean:89`), `Blanc.Composition.Curve3Pool3CrvInstance.removeLiquidityImbalance_exactPremises_satisfiable` (`Blanc/Composition/Curve3Pool3CrvExactWitness.lean:220`), `Blanc.Composition.Curve3Pool3CrvInstance.removeLiquidityOneCoin_exactPremises_satisfiable` (`Blanc/Composition/Curve3Pool3CrvExactWitness.lean:294`), `Blanc.Composition.Curve3Pool3CrvInstance.exchange_exactPremises_satisfiable` (`Blanc/Composition/Curve3Pool3CrvExactWitness.lean:361`) | Witness / conditional | as the sufficient-gas witnesses: the coins hold `Token20`'s code and their ledgers cover the moves, 3Crv holds its code with supply `T` and accepts the burn or mint, the accounts involved are distinct, not precompiles and not the pool; for `exchange`, coins `i ≠ j` | They witness the premise bundles of the frame theorems at the sufficient-gas witnesses' worlds (for `exchange`, at the exact witness's own worlds); the composed headlines' coin-chain hypotheses as stated are witnessed in the next row, their 3Crv and coin-ledger facts taken as world conditions. They do not discharge the per-execution keep premise or the model step, and the amounts are not tied to the model's outputs. No exact-gas theorem is instantiated end to end |
| **The composed headlines' coin-chain hypotheses hold as stated.** Over the composed headline's own history, a coin chain `V` that never reads 3Crv's storage (coins not yet called as at the entry; for `add_liquidity` also the fee coin's pulled ledger, so the world after the mint carries it), `U = 80000` and `Token20`'s own coin debit and successor functions meet, jointly and in the headline's text, each of the four composed exact headlines' coin-chain hypotheses `_hU`, `_hVc`, `_hVb`, `_hVs`, `_hskip` where present (`add_liquidity`, `remove_liquidity_imbalance`) and coin profiles (the 3Crv profiles are then 3Crv's own, through `*ExactPremises_c3crv`), and `_hpc` follows from the history; `_htok`, `_hcoin`, `_hT` and `_hburn`/`_hmint` are restated from the world conditions. Applied to the headline itself, its conclusion holds under its remaining hypotheses. The same holds for the four sufficient-gas composed rows | `Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_removeLiquidity_live_exact_literal` (`Blanc/Composition/Curve3Pool3CrvExactLiteralHeadlines.lean:66`), `Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_addLiquidity_live_exact_literal` (`Blanc/Composition/Curve3Pool3CrvExactLiteralHeadlines.lean:138`), `Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_removeLiquidityImbalance_live_exact_literal` (`Blanc/Composition/Curve3Pool3CrvExactLiteralHeadlines.lean:262`), `Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_removeLiquidityOneCoin_live_exact_literal` (`Blanc/Composition/Curve3Pool3CrvExactLiteralHeadlines.lean:345`), `Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_removeLiquidity_live_entry_literal` (`Blanc/Composition/Curve3Pool3CrvExactLiteralHeadlines.lean:454`), `Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_addLiquidity_live_entry_literal` (`Blanc/Composition/Curve3Pool3CrvExactLiteralHeadlines.lean:512`), `Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_removeLiquidityImbalance_live_entry_literal` (`Blanc/Composition/Curve3Pool3CrvExactLiteralHeadlines.lean:584`), `Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_removeLiquidityOneCoin_live_entry_literal` (`Blanc/Composition/Curve3Pool3CrvExactLiteralHeadlines.lean:652`) | Witness / conditional | the composed headline's history premises; taken as world conditions, not discharged: the frame is not static, not at depth `0`, at a covered fork; 3Crv holds its code with supply `T`, is not the pool and not a precompile (`C3Entry`); the coins hold `Token20`'s code, are distinct, not the pool, not 3Crv and not precompiles (`T20Coins`; for `remove_liquidity_one_coin`, coin `i` only, with `_hcoin` a hypothesis for all three coin words); their ledgers cover the calls (`T20MoveFits`, `T20PullFits`); 3Crv accepts the burn or mint (`_hburn`/`_hmint` as `BurnFits`, `MintFits`) | The call code and call data (`_hcode`, `_hlen`, `_hcd`, `_hsel`, and `_hi` for `remove_liquidity_one_coin`), the model step, `IdReady`, the per-execution keep premise, the headroom and the no-wrap bound stay hypotheses; no composed headline is instantiated end to end. The witnesses are `Blanc.Composition.Curve3Pool3CrvLiteralWitness.removeLiquidity_exact_literal_witness` (`Blanc/Composition/Curve3Pool3CrvExactLiteralWitness.lean:176`) and its siblings |

**End-to-end instances** (of the sufficient-gas frame theorems; no hypotheses; Section 7 item 53)

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| `remove_liquidity(600, [0, 0, 0])` runs: an actual successful execution of the pool's runtime from a concrete entry at gas 878,400 whose raw effect is the model's output (pushes 100, 200 and 300, burn 600) at supply 6,000, with the pool's checkpoint at the post | `Blanc.Composition.Curve3Pool3CrvInstance.rl_frame_live` (`Blanc/Composition/Curve3Pool3CrvLiveEndKeep.lean:121`) | Frame / live, instantiated | none | `removeLiquidity_live` with every premise discharged, the per-execution keep premise included. The entry is a frame at remaining call depth 1 (nested 1,023 calls deep) on a synthetic world |
| `remove_liquidity_one_coin(600, 1, 0)` runs at gas 878,400: burn 600, push 531 of coin 1, with the pool's checkpoint at the post | `Blanc.Composition.Curve3Pool3CrvInstance.oc_frame_live` (`Blanc/Composition/Curve3Pool3CrvLiveEndKeep.lean:132`) | Frame / live, instantiated | none | The raw effect is at **some** supply reading `T'`, as in the frame theorem |
| `remove_liquidity_imbalance([90, 180, 270], 600)` runs at gas 878,400: burn 541, pushes 90, 180 and 270, with the pool's checkpoint at the post and the post world in the theorem's last invariant | `Blanc.Composition.Curve3Pool3CrvInstance.rli_frame_live` (`Blanc/Composition/Curve3Pool3CrvLiveEndKeepRLI.lean:64`) | Frame / live, instantiated | none | The last conjunct is the world-chain invariant of the instance (3Crv at its burned storage, the coins as the pushes leave them) |
| `add_liquidity([100, 200, 300], 599)` runs at gas **1,110,000**: mint 599, with the pool's checkpoint at the post | `Blanc.Composition.Curve3Pool3CrvInstance.al_frame_live` (`Blanc/Composition/Curve3Pool3CrvLiveEndKeepAL.lean:71`) | Frame / live, instantiated | none | At **some** environment `e` whose supply is 6,000 and at which the model accepts the call. The frame's gas differs from the 878,400 of the concrete entry message |
| `exchange(0, 1, 100, 0)` runs from the transaction's entry frame: at any machine satisfying `ExFrame` (the closed instance's pool frame: remaining call depth 1,024, the transaction's entry frame, gas 878,400), an actual successful execution whose raw effect is the model's output (pull 100 of coin 0, push 132 of coin 1) | `Blanc.Composition.Curve3Pool3CrvInstance.ex_frame_live` (`Blanc/Composition/Curve3Pool3CrvCapstoneFrame.lean:107`) | Frame / live, instantiated | `ExFrame`, which the transaction's prepared message meets (`ex_prepared_frame`) | The coins' answers come from `Token20`'s code (`Blanc.Composition.Curve3Pool3CrvInstance.token20_coinPullOkAt` (`Blanc/Composition/Curve3Pool3CrvCoinAnswers.lean:20`), `Blanc.Composition.Curve3Pool3CrvInstance.token20_coinPushOkAt` (`Blanc/Composition/Curve3Pool3CrvCoinAnswers.lean:38`)), not from premises. The environment's balance readings are existential, with the credited pull equal to the model's |

**Closed instance**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| A finite synthetic world satisfies the joint pool-and-3Crv checkpoint, decided by a computable checker whose soundness is a theorem: the pool's storage is a `Checkpoint` of the model state, 3Crv's storage satisfies `VyInv` over the listed rows (conservation included), the pool's token is 3Crv and 3Crv's minter is the pool | `Blanc.Composition.Curve3Pool3CrvJoint.checkJoint_sound` (`Blanc/Composition/Curve3Pool3CrvCheckpoint.lean:345`); the first fixture `Blanc.Composition.Curve3Pool3CrvJoint.world_joint` (`Blanc/Composition/Curve3Pool3CrvCheckpoint.lean:456`); the closed-instance world `Blanc.Composition.Curve3Pool3CrvInstance.p0_joint` (`Blanc/Composition/Curve3Pool3CrvWorld.lean:81`) | Witness / closed | none for the fixtures (kernel evaluation of the checker) | The checkpoint predicate carries storage, minter and address facts, not installed code. The synthetic pool is at address `0x1000` (not a precompile under any covered fork) |
| **One signed `exchange` in one configured BPO2 block, with the composed U3 headline applied and every hypothesis discharged.** For every canonical world with representable total ether that agrees with the synthetic world `P0` on the touched accounts (the trader, the pool, 3Crv, three synthetic coins, addresses 4 and 0, and the four system addresses): the configured block carrying the type-2 transaction `exchange(0, 1, 100, 0)` is accepted by the chain's state transition; on a configured history of it the first replayed pool invocation decodes to `exchange(0, 1, 100, 0)` and is accepted by the model at the checkpoint state with its raw effect; the six U3 bounds hold at 3Crv's ledger supplies (`U3Ledger`); the model's output state has balances `[1100, 1868, 3000]` and its calls are `pull 0 trader 100` and `push 1 trader 132`; 3Crv's supply is unchanged; and the stored balances' `get_D` rises strictly (22177905188247 to 22178770202300), so `D/T` strictly increases | `Blanc.Composition.Curve3Pool3CrvInstance.curve3pool_closed_agreeing` (`Blanc/Composition/Curve3Pool3CrvCapstone.lean:101`); the concrete world `Blanc.Composition.Curve3Pool3CrvInstance.curve3pool_closed_instance` (`Blanc/Composition/Curve3Pool3CrvCapstone.lean:191`); the outcome predicate `Blanc.Composition.Curve3Pool3CrvInstance.ClosedExchangeOutcome` (`Blanc/Composition/Curve3Pool3CrvCapstone.lean:77`) | Closed instance / safety and witness | `AgreesP0 st`, canonical, `SumNof st.bal`. Nothing else: the code premises, the joint checkpoint, `FreshKeys` (no frame runs at 3Crv), and `PoolTraceEnv` are derived from the block's frames | The coins are `Token20` contracts (a synthetic ERC-20). The transaction succeeds: `Blanc.Composition.Curve3Pool3CrvInstance.ex_transaction` (`Blanc/Composition/Curve3Pool3CrvCapstoneTx.lean:72`); its signer is recovered by kernel evaluation (`Blanc.Composition.Curve3Pool3CrvInstance.exchange_recoveredSender` (`Blanc/Composition/Curve3Pool3CrvSigningRecover.lean:9`)). Section 7 item 50 |

**Newton-loop laws and the non-monotone parts**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| For positive balances and `A ≥ 1`, a non-reverting checked `get_D` returns a value `v` with `v + 1` strictly above the root `D*` of the StableSwap invariant, so `v ≥ ⌊D*⌋`, at **every** stopping tolerance and whether the loop stopped or ran out its 255 bodies | `Blanc.StableSwapNewton.getDChk_lower` (`Blanc/Lift/StableSwapNewton/D.lean:252`) | Model / safety | `getDChk x amp tol = some v`, every balance positive, `1 ≤ amp`. No coin answers | The rounding of `D_P` down is load-bearing: `Blanc.StableSwapNewton.getDCeil_breaks_lower` (`Blanc/Lift/StableSwapNewton/D.lean:347`) shows that rounding it up returns `⌊D*⌋ − 2` on a witness |
| `get_D` is not monotone in the balances: one more wei of coin 0 lowers `get_D` at `A = 1`, at stopping tolerance 1 and at tolerance 2 | `Blanc.StableSwapNewton.getD_not_mono` (`Blanc/Lift/StableSwapNewton/D.lean:311`) | Model / kernel counterexample | none (the witness balances are explicit) | The stopping tolerance is not what breaks monotonicity. At `A = 2000` on an explicit balance triple the loop cycles between two values and returns the last iterate `⌊D*⌋ + 2` after 255 bodies without reverting: `Blanc.StableSwapNewton.getD_cap_cycle` (`Blanc/Lift/StableSwapNewton/D.lean:282`) |
| A non-reverting checked `get_y_D` returns the floor root `r` of its floored-coefficient quadratic or `r + 1`, and `r + 1` only where the root-gap condition `rootGap` fails (so exactly `r` under `rootGap`). Linked to the bytecode: in a successful `calc_withdraw_one_coin` or `remove_liquidity_one_coin` frame, the first `get_y_D` call returned a word with this property, on the words the bytecode passed | `Blanc.StableSwapNewton.getYDChk_rootOrSucc` (`Blanc/Lift/StableSwapNewton/Y.lean:610`); `Blanc.Lift.Curve3Pool.pool_getYD_rootOrSucc_cwo` (`Blanc/Lift/Curve3Pool/U4Frames.lean:84`), `Blanc.Lift.Curve3Pool.pool_getYD_rootOrSucc_oneCoin` (`Blanc/Lift/Curve3Pool/U4Frames.lean:105`) | Model and frame / safety | `getYDChk … = some v`; the frame rows' premises (the `cwo` form needs only a `Checkpoint`, the token not a precompile and a fresh entry; the one-coin form `PoolFrameEnv`) | Exact floor is **not** claimed. The second `get_y_D` call of the same frames is `Blanc.Lift.Curve3Pool.pool_getYD2_rootOrSucc_cwo` (`Blanc/Lift/Curve3Pool/U4Frames.lean:127`) and `Blanc.Lift.Curve3Pool.pool_getYD2_rootOrSucc_oneCoin` (`Blanc/Lift/Curve3Pool/U4Frames.lean:148`) |
| A non-reverting checked `get_y` returns `r` or `r + 1` for the floor root `r` of its quadratic at `D = get_D(xp, amp)`, with `r + 1` only off `rootGap`; in a successful `exchange` frame its `get_y` call returned such a word | `Blanc.StableSwapNewton.getYChk_rootOrSucc` (`Blanc/Lift/StableSwapNewton/Y.lean:626`); `Blanc.Lift.Curve3Pool.pool_getY_rootOrSucc_exchange` (`Blanc/Lift/Curve3Pool/U4Frames.lean:171`); the same for the views `get_dy` and `get_dy_underlying`: `Blanc.Lift.Curve3Pool.pool_getY_rootOrSucc_dy` (`Blanc/Lift/Curve3Pool/U4Frames.lean:201`), `Blanc.Lift.Curve3Pool.pool_getY_rootOrSucc_dyu` (`Blanc/Lift/Curve3Pool/U4Frames.lean:232`) | Model and frame / safety | as above, with `PoolFrameEnv` for the `exchange` frame | The loop's cap is covered by the statement: the law holds of every non-reverting call (`Blanc.StableSwapNewton.loopYChk_rootOrSucc` (`Blanc/Lift/StableSwapNewton/Y.lean:564`)) |
| Exact floor is false for both: at states reached in the honest-world model, a successful checked `get_y_D` returns `1` where the floor root is `0`, and a successful checked `get_y` returns `1` where it is `0` (at `A = 100`) and `27029` where it is `27028` (at `A = 1000`) | `Blanc.Lift.Curve3Pool.U4Exactness.callee_not_floor` (`Blanc/Lift/Curve3Pool/U4ExactnessRefute.lean:113`); `Blanc.Lift.Curve3Pool.U4GetY.callee_not_floor` (`Blanc/Lift/Curve3Pool/U4GetYRefute.lean:91`); `Blanc.Lift.Curve3Pool.U4GetY.Primary.callee_not_floor` (`Blanc/Lift/Curve3Pool/U4GetYRefute.lean:203`) | Model / kernel counterexample | none (explicit histories) | Section 7 item 51. The `get_y_D` history: the recorded constructor's state, four owner ramps to `A = 873512`, a first deposit, one one-coin withdrawal. The `get_y` histories: a first deposit then one `exchange`, with `A = 100`; a ramp to `A = 1000`, a deposit, then one `exchange` |

**Virtual-price behaviour at a fixed amplification**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| **Virtual price is not monotone.** For each of `exchange`, `add_liquidity`, `remove_liquidity`, `remove_liquidity_imbalance`, `remove_liquidity_one_coin` and `donate_admin_fees`, a kernel-checked step at a state reached in the honest-world model, at which `_A()` is unchanged at the step's timestamp and `D'·T < D·T'` holds with `T > 0` the 3Crv supply before, `T'` after, and `D, D'` the checked `get_D` of the stored balances | `Blanc.Lift.Curve3Pool.u3_refuted_exchange` (`Blanc/Lift/Curve3Pool/U3Refute.lean:87`), `Blanc.Lift.Curve3Pool.u3_refuted_add_liquidity` (`Blanc/Lift/Curve3Pool/U3Refute.lean:138`), `Blanc.Lift.Curve3Pool.u3_refuted_remove_liquidity` (`Blanc/Lift/Curve3Pool/U3Refute.lean:160`), `Blanc.Lift.Curve3Pool.u3_refuted_remove_liquidity_imbalance` (`Blanc/Lift/Curve3Pool/U3Refute.lean:210`), `Blanc.Lift.Curve3Pool.u3_refuted_remove_liquidity_one_coin_deployed` (`Blanc/Lift/Curve3Pool/U3Refute.lean:233`), `Blanc.Lift.Curve3Pool.u3_refuted_donate_admin_fees` (`Blanc/Lift/Curve3Pool/U3Refute.lean:256`); parameter-range forms `Blanc.Lift.Curve3Pool.u3_refuted_exchange_deployed` (`Blanc/Lift/Curve3Pool/U3Refute.lean:116`) and `Blanc.Lift.Curve3Pool.u3_refuted_remove_liquidity_deployed` (`Blanc/Lift/Curve3Pool/U3Refute.lean:189`) | Model / kernel counterexample | none (explicit histories) | The shortfall in `D` is between one wei and about fifteen thousand wei in values of 10^19 to 10^28. The failing step is an operation, never a ramp. The histories deploy the model with chosen `A`, fee and admin fee (not the recorded constructor arguments), run honest synthetic coins and 3Crv, and several include outsiders' direct coin transfers to the pool ("gifts"). Section 7 items 45 and 51 |
| **Bounded failure** ("monotone up to the Newton-loop error"). At fixed `A` (the checked `_A()` is the same after the step at every time) and with `D`, `D'` the checked `get_D` of the stored balances before and after: `remove_liquidity` (positive `T`): `D·T' ≤ (D'+1)·T + E·T'`; `exchange`: `T' = T` and `D ≤ D' + yGap`; `add_liquidity` (positive `T`) and `remove_liquidity_imbalance`: there is a mid state whose balances are at most the result's and `D·T' ≤ (D' + E_mid)·T`; `remove_liquidity_one_coin`: `D·T' ≤ (D' + oneGap)·T`; `donate_admin_fees` (stored balances at most the observed coin balances): `T' = T`, `⌊D*⌋ ≤ D'` and `D ≤ D' + E`. Here `E = get_D − ⌊D*⌋ ≥ 0` at the stated state, and `yGap` (`Blanc.Lift.Curve3Pool.yGap` (`Blanc/Lift/Curve3Pool/U3Bounds.lean:562`)) and `oneGap` (`Blanc.Lift.Curve3Pool.oneGap` (`Blanc/Lift/Curve3Pool/U3Bounds.lean:695`)) are the `get_y` and `get_y_D` floor gaps: how far below the level `D` the landing point of the floor root lies, zero when the floor root plus 1 reaches the invariant at that level. They contain no loop error | `Blanc.Lift.Curve3Pool.U3Ledger` (`Blanc/Lift/Curve3Pool/U3Ledger.lean:21`) and `Blanc.Lift.Curve3Pool.U3Step` (`Blanc/Lift/Curve3Pool/U3History.lean:26`) hold of every accepted step (`Blanc.Lift.Curve3Pool.u3Step_of_step` (`Blanc/Lift/Curve3Pool/U3History.lean:71`); `Blanc.Lift.Curve3Pool.u3Ledger_of_step` (`Blanc/Lift/Curve3Pool/U3Ledger.lean:85`)); per operation `Blanc.Lift.Curve3Pool.u3_bound_exchange` (`Blanc/Lift/Curve3Pool/U3Bounds.lean:570`), `Blanc.Lift.Curve3Pool.u3_bound_remove_liquidity` (`Blanc/Lift/Curve3Pool/U3Bounds.lean:274`), `Blanc.Lift.Curve3Pool.u3_bound_remove_liquidity_one_coin` (`Blanc/Lift/Curve3Pool/U3Bounds.lean:702`), `Blanc.Lift.Curve3Pool.u3_bound_remove_liquidity_imbalance` (`Blanc/Lift/Curve3Pool/U3Bounds.lean:455`), `Blanc.Lift.Curve3Pool.u3_bound_add_liquidity` (`Blanc/Lift/Curve3Pool/U3Bounds.lean:395`), `Blanc.Lift.Curve3Pool.u3_bound_donate_admin_fees` (`Blanc/Lift/Curve3Pool/U3Bounds.lean:362`); history form `Blanc.Lift.Curve3Pool.pool_history_u3` (`Blanc/Lift/Curve3Pool/U3History.lean:97`) | Model, and history / safety | the model's own answers; for `add_liquidity`, `remove_liquidity_imbalance`, `exchange` and `remove_liquidity_one_coin`, `adminFee ≤ 10^10` at the pre-state; the history form takes the history premises, with `T` the supply the frame observed | No universal numeric cap is proved: the bounds are up to the named error terms. Section 7 items 44 and 45 |
| **Composed bound at 3Crv's ledger supply.** The same bounds over one configured history of the pool and 3Crv together, with `T` 3Crv's supply word at the frame's entry and `T'` at its post, no supply premise, and `supplyAfter T (model calls) = T'` | `Blanc.Composition.Curve3PoolSupply.pool_3crv_u3` (`Blanc/Composition/Curve3Pool3CrvU3.lean:99`); from the recorded deployment `Blanc.Composition.Curve3Pool3CrvHeadlines.pool_3crv_u3_deployed` (`Blanc/Composition/Curve3Pool3CrvHeadlines.lean:480`) | History / safety | the joint-history premises of the composition row below; the deployed form takes the joint checkpoint with the pool's state `Creation.poolInitState t₀` | In `pool_3crv_u3` the admin-fee side condition is kept by every replayed step if it holds at the checkpoint (`FeeBounded ps₀ → FeeBounded sᵢ`); `pool_3crv_u3_deployed` states `adminFee ≤ 10^10` outright (`Blanc.Lift.Curve3Pool.feeBounded_of_poolRun_init` (`Blanc/Lift/Curve3Pool/U3Ledger.lean:164`)). No joint checkpoint at `poolInitState` is instantiated (Section 7 item 49). Section 7 item 44 |

**Amplification**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| In the committed replay, every invocation ran at its block's **header** timestamp, which is its recorded time. At that time the model's `_A()` is the stored linear interpolation between `initial_A` and `future_A` (truncating, separately for a rising and a falling ramp) from the ramp start on, and is the constant `future_A` once the ramp has ended (so outside a ramp, and where `future_A_time = 0`); an accepted `ramp_A` meets the source's guards (duration at least `MIN_RAMP_TIME`, `0 < A < MAX_A`, factor at most `MAX_A_CHANGE` either way). After `stop_ramp_A`, `A` is constant at its value then | `Blanc.Lift.Curve3Pool.pool_history_amp` (`Blanc/Lift/Curve3Pool/AmpHistory.lean:84`); `Blanc.Lift.Curve3Pool.aChk_eq_aInterp` (`Blanc/Lift/Curve3Pool/U5.lean:60`), `Blanc.Lift.Curve3Pool.aChk_of_le` (`Blanc/Lift/Curve3Pool/U5.lean:51`), `Blanc.Lift.Curve3Pool.rampA_guards` (`Blanc/Lift/Curve3Pool/U5.lean:147`), `Blanc.Lift.Curve3Pool.stopRampA_const` (`Blanc/Lift/Curve3Pool/U5.lean:160`) | Model and history / safety | the history premises; for the interpolation: `future_A` below 2^256 and the source's one product `|future_A − initial_A|·(t − initial_A_time)` below 2^256 | The guards are read off an accepted ramp in one direction. Control: the recorded time is never the parent block's timestamp, `Blanc.Lift.Curve3Pool.pool_invocation_time_ne_parent` (`Blanc/Lift/Curve3Pool/AmpHistory.lean:128`), for a settled frame of one configured block whose timestamp is a word; and an explicit accepted ramp state at which the header time gives `A = 550` and the parent's timestamp gives `549`, `Blanc.Lift.Curve3Pool.u5_parent_time_control` (`Blanc/Lift/Curve3Pool/U5.lean:233`) |
| The exact root `⌊D*⌋` is non-decreasing in `A` at fixed positive balances, and `get_D` follows it only up to its loop error: `get_D(A) ≤ get_D(A') + (get_D(A) − ⌊D*⌋(A))` for `A ≤ A'`. A ramp alone can lower `D/T`: with one deposit and then a ramp from `A = 2000` to `A = 200`, and no operation after it, `get_D` falls from 200044801219456106169 to 192793226260180884069 at an unchanged supply | `Blanc.Lift.Curve3Pool.dMonoInA` (`Blanc/Lift/Curve3Pool/U5.lean:213`); `Blanc.Lift.Curve3Pool.u5_ramp_control` (`Blanc/Lift/Curve3Pool/U5.lean:189`) | Model / safety and control | positive balances, `1 ≤ A ≤ A'` (`dMonoInA`); the explicit honest-world history (control) | `dMonoInA` is **not** a monotonicity of `get_D` in `A`: its statement carries the error term. The ramp control is the negative control for the fixed-amplification statements; the bare inequality is `Blanc.Lift.Curve3Pool.u5_ramp_control_falls` (`Blanc/Lift/Curve3Pool/U5.lean:196`) |

**Composition with 3Crv**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| Over one configured history from a joint checkpoint in which 3Crv's `minter` is the pool: the pool history of the history row; 3Crv's model replays exactly its committed invocations to a state its future storage abstracts; the minter is still the pool (**persistence**); 3Crv's final supply plus the pool's committed burns equals the checkpoint supply plus the pool's committed mints (amounts read off the replayed steps' model calls, as words); per invocation, 3Crv's supply word at the frame's post plus the step's burned amounts equals its supply word at entry plus its minted amounts; and the supply the frame observed is 3Crv's supply word at the entry of its `totalSupply()` child | `Blanc.Composition.Curve3PoolSupply.pool_3crv_history` (`Blanc/Composition/Curve3PoolSupply.lean:566`) | History / safety, exact extraction | `JointCheckpoint`; both runtimes installed at the checkpoint; `FreshKeys` over 3Crv's touched keys (3Crv's HASH-T, inherited); `PoolTraceEnv`; `pool ≠ systemAddress` | The pool side takes no hash premise. Section 7 items 43 and 49 |
| 3Crv's own history statements used above | `Blanc.Lift.Curve3Crv.c3crv_history_committed_derived` (`Blanc/Lift/Curve3Crv/CommittedHistory.lean:230`); `Blanc.Composition.Curve3CrvToken.c3crv_history_supply` (`Blanc/Composition/Curve3CrvTokenCore.lean:247`); `Blanc.Composition.Curve3CrvToken.c3crv_history_at` (`Blanc/Composition/Curve3CrvPositional.lean:246`) | History / safety | the 3Crv premises of Section 5.3 | `c3crv_history_supply` additionally takes that every committed writer invocation the initial minter sends keeps the minter |
| A generic supply identity: along an accepted run of a token book with a minter/supply facet in which every message the minter sends keeps the minter, the minter persists and the final supply plus the burned amounts equals the initial supply plus the minted amounts. Control: a mutated 3Crv whose `mint` skips the caller check has **no** facet with 3Crv's minter and mint projections (a non-minter `mint(1, 1)` from address 0 is accepted) | `Blanc.Lift.Token.SupplyFacet.run_supply` (`Blanc/Lift/Token/Supply.lean:120`); control `Blanc.Composition.Curve3CrvToken.control_mutant_no_supplyFacet` (`Blanc/Composition/Curve3CrvTokenCore.lean:331`), restated `Blanc.Composition.Curve3Pool3CrvHeadlines.u8_control` (`Blanc/Composition/Curve3Pool3CrvHeadlines.lean:515`) | Model / safety and control | a `SupplyFacet` for the book | The identity of the row above is the instance at 3Crv's book; the control shows the minter rule is load-bearing for it |

**Deployment**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| On every covered fork, the pool's address is the CREATE address of the recorded deployer at nonce 43; the model constructor on the recorded arguments (`A = 100`, fee 4,000,000, admin fee 0) returns `poolInitState`; the recorded creation message (from the recorded deployer, zero value, 5,000,000 gas, empty world, the recorded block timestamp) is accepted, installs the 21,199-byte certified runtime at that address and leaves storage `deployedStor deployTime`, which is a `Checkpoint` of `poolInitState`; every storage word outside the pool's slots is zero | `Blanc.Lift.Curve3Pool.Creation.pool_deploy_covered` (`Blanc/Lift/Curve3Pool/Creation/Deploy.lean:292`); general form `Blanc.Lift.Curve3Pool.Creation.pool_create` (`Blanc/Lift/Curve3Pool/Creation/Deploy.lean:195`) | Deploy / INIT | none for the recorded message (closed). The general form takes zero value, at least 4,500,000 gas, a covered non-static fork, a code-size limit of at least 21,199 bytes and a timestamp whose kill deadline does not wrap. The creation input is `prefix ++ runtime ++ suffix` with the runtime the registered certified constant, not a second literal | A modeled message, not a validated transaction and not historical inclusion; the message does not check the deployer's nonce, which enters through the address. Statement control: a constructor call with any other fee is not abstracted by the deployed storage, `Blanc.Lift.Curve3Pool.Creation.deployedStor_wrong_fee` (`Blanc/Lift/Curve3Pool/Creation/Deploy.lean:168`). Section 7 item 52 |

**Non-claims.** Monotonicity of virtual price at a fixed amplification is **not** claimed: the
statements above say where it fails and bound the failure. Monotonicity across an amplification
ramp is not claimed. `get_D` is not claimed monotone in the balances or in `A`, and `get_y_D` and
`get_y` are not claimed to return the exact floor root. Nothing says that DAI, USDC or USDT satisfy
their per-call premises, sufficient-gas or exact: the premises are shown satisfiable only by a
synthetic ERC-20 (`Token20`) and the deployed 3Crv. None of the composed liveness theorems,
sufficient-gas or exact, is instantiated end to end; the end-to-end instances are of the
sufficient-gas frame theorems, at synthetic worlds, and only `exchange` is shown at a transaction's
entry frame. No exact-gas theorem is instantiated end to end. The closed instance is one fixed signed transaction on a synthetic
world on one fork; there is no transaction-level liveness for any other entry or calldata. The
counterexamples are statements about the honest-world model and the checked loop arithmetic, not
about the chain's live state. Nothing says that any price, fee or LP outcome is fair or safe, or
anything about MEV or oracle use. The admin's honesty is not claimed: `kill_me`, fee changes and
ramps are modeled as admin calls, not prevented. The 3Crv and pool deployments are not chained into
one history.

## Artifacts

| Contract | Address | Runtime bytes | keccak256 codehash | Creation transaction | Block |
|---|---|---:|---|---|---:|
| Curve 3pool StableSwap | 0xbEbc44782C7dB0a1A60Cb6fe97d0b483032FF1C7 | 21,199 | 0x954a1e212c557c85043985931498ffa3e2fcbe7dfe9cd61513f36eb47d6f4dfc | 0x20793bbf260912aae189d5d261ff003c9b9166da8191d8f9d63ff1c7722f3ac6 (deployer 0xbabe61887f1de2713c6f97e567623453d3c79f67, nonce 43) | 10,809,473 |

**The Curve 3pool row.** The 3pool's runtime was read by `eth_getCode` at finalized block
26,208,636 and is equal across five separately operated providers; its codehash equals the
`eth_getProof` code hash at three of them. The creation input (21,967 bytes) of the recorded
creation transaction was fetched from two providers and is equal byte for byte; it holds the
lifted runtime at bytes 488 to 21,686, followed by a 24-byte deploy tail and the constructor
arguments (owner, the DAI, USDC and USDT coins, the 3Crv token, amplification 100, fee 4,000,000
and admin fee 0). The lifted inputs are `scripts/lift/inputs/curve-3pool-runtime.hex` and
`scripts/lift/inputs/curve-3pool-creation.hex`. The compiler is Vyper 0.2.4 (`StableSwap3Pool.vy`,
a Sourcify full match). Nothing was recompiled: the refinement of Section 5.11 ties the bytes to
the source revision.

Compiler, from the certificate provenance: Vyper 0.2.4. Runtime identity: `eth_getCode`
agreement across five separately operated public providers at one finalized block; the creation
input fetched from two providers and equal byte for byte.

## Premise classes

| Class | Meaning | Acceptable in a headline? | INIT established by a deployment theorem? |
|---|---|---|---|
| INIT | Stated once, at the checkpoint | Yes, if shown inhabited, ideally by deployment | **Curve 3pool** `Checkpoint`, the pool's storage predicate at the constructor's model state: yes, no hash premise [`Blanc.Lift.Curve3Pool.Creation.pool_deploy_covered` (`Blanc/Lift/Curve3Pool/Creation/Deploy.lean:292`)]; the joint 3pool-and-3Crv `JointCheckpoint` is not established by deployment, and is checked by a kernel-evaluated checker on synthetic worlds only (Section 5.11) |

## Summary matrix

| | M1 | M2 | M3 | M4 | M5 | M6 | M7 | M8 |
|---|---|---|---|---|---|---|---|---|
| Curve 3pool | ✓ | ✓ | ✓ [ae] | ✓ HASH-T [af] | ✓ [ag] | ✓ [ah] | ~ [ai] | ✓ [aj] |

[ae] Per-frame premises are environmental: `PoolFrameEnv` for a frame, the per-execution keep
premise for a liveness row, and for a history the per-frame `callbacks` of `PoolTraceEnv` (every
direct child keeps the pool's storage, every coin child keeps 3Crv's storage) with trace-local
exclusions; fresh entry, calldata, gas and identity readiness are derived. At frame level the
target's code and the identity precompile's readiness are premises, discharged from the trace at
history level.

[af] No hash premise on the pool side (the pool's storage is at fixed slots); in the
composed statements freshness is 3Crv's `FreshKeys` (HASH-T, inherited); no HASH-U.

[ag] A modeled
deployment message under every covered fork, not chained into a configured history; the joint
checkpoint of the composed statements is a premise (checked on synthetic worlds), not derived from
the two deployments (§7 items 49 and 52).

[ah] All five entries (`exchange`, `add_liquidity` and the
three withdrawals) have history-level liveness at message entry with exact gas: for the residual
gas `R`, the message `msg.withGas (R + c)` executes and ends with exactly `R`, where the closed cost
`c` is fixed before `R` from the call profiles' debit and successor functions and the model words
pinned by the model's own checks; headroom and the no-wrap bound are separate premises. The coin
calls are per-call environment premises (exact profiles whose debit and successor functions are
parameters); 3Crv's calls are discharged under composition by 3Crv's own exact profiles. The
sufficient-gas forms remain, with a closed sufficient-gas cost and a named per-call allowance `U`;
each sufficient-gas frame theorem is instantiated end to end, with no hypotheses, at one synthetic
entry (`exchange` at a transaction's entry frame, the other four at remaining call depth 1). No
exact-gas theorem and no composed form is instantiated end to end; the exact premise bundles are
shown satisfiable (§7 items 48 and 53), and the composed headlines' coin-chain hypotheses are applied as stated, with their 3Crv and coin-ledger facts taken as world conditions (§7 item 53).

[ai] One fixed signed `exchange(0, 1, 100, 0)` on worlds that agree with a
fixed synthetic checkpoint, in one BPO2 block, with kernel recovery of the signer; no
transaction-level liveness for any other entry, calldata or world (§7 item 50).

[aj] Every frame,
history and deployment statement carries `CoveredFork`; the closed instance is BPO2 only.

## Disclosures and limits

42. **Curve 3pool: coin behaviour is a per-call premise, and only a synthetic coin is shown to
    satisfy it.** DAI, USDC and USDT are not model facts. Each liveness theorem takes, per call site,
    a premise of the shapes `CoinBalOkAt`, `CoinPullOkAt` and `CoinPushOkAt` (Section 5.11: from every
    world of a caller-chosen invariant, with at least the allowance `U` of gas, the exact call
    succeeds with a reply that passes Vyper's `raw_call` test, the pool's storage is kept, at most `U`
    gas is used, and the world moves to the next invariant). Each liveness theorem also takes the
    per-execution keep premise (every direct child of every execution of the frame keeps the pool's
    storage and the code at address 4), and the history statements take, per frame, that every
    direct child keeps the pool's storage and every coin child keeps 3Crv's storage. The callee
    premises are satisfied, with explicit world chains, by coins running `Token20`, a synthetic
    ERC-20, when the coin's ledger covers the moves (`removeLiquidity_premises_satisfiable` and
    siblings); those witnesses do not discharge the keep premise or the model step. The end-to-end
    instances (item 53) discharge every premise of each frame theorem at one synthetic entry. USDT's
    fee-on-transfer index is index 2: for it `exchange` and `add_liquidity` take two
    `balanceOf(self)` readings around the pull and the model credits their difference, not the
    requested amount; `Token20` charges no transfer fee, so that path is satisfied only by a fee-free
    coin. The exact-gas forms take, at the same call sites, the exact profiles of item 48, whose
    debit and successor functions are parameters; `Token20` coins satisfy those too
    (`exchange_exactPremises_satisfiable` and siblings). No statement claims that a real DAI, USDC
    or USDT satisfies a premise.

43. **Curve 3pool: 3Crv state preconditions in composed liveness.** The composed liveness rows,
    sufficient-gas and exact, state 3Crv's side once, on the entry: 3Crv's supply word is `T`, and 3Crv accepts the
    call the model makes, `MintFits` for `add_liquidity` (the pool is the minter, the recipient is
    nonzero, and neither the supply nor the recipient's balance overflows) or `BurnFits` for the
    withdrawals (the pool is the minter, the holder is nonzero, and the amount is covered by the
    supply and by the holder's balance). These are facts about 3Crv's storage at the frame's entry,
    not consequences of the history: a history that leaves 3Crv where the amount is not covered gives
    no liveness row for that call. The coin premises of those rows must in addition leave 3Crv's
    storage and code as they found them (the coin world chain does not read 3Crv's storage, and each
    coin world pins it). None of the eight composed theorems is instantiated end to end.

44. **Curve 3pool: the admin-fee bound.** Four of the six U3 bounds (`add_liquidity`,
    `remove_liquidity_imbalance`, `exchange`, `remove_liquidity_one_coin`) are stated under
    `admin_fee ≤ 10^10` at the pre-state of the step. The composed statement `pool_3crv_u3` shows this
    is kept by every replayed step when it holds at the checkpoint (the constructor does not assert
    it); `pool_3crv_u3_deployed` discharges it from the recorded deployment's storage. The composed U3
    uses 3Crv's supply words at the frame's entry and post, not an observed answer, so it takes no
    supply premise; the pool-only `pool_history_u3` takes the supply the frame observed.

45. **Curve 3pool: U3 is not an exact integer-output monotonicity.** The bounds of Section 5.11 are
    up to named error terms: `E = get_D − ⌊D*⌋` at the stated state and the `get_y` or `get_y_D` floor
    gap. No universal numeric cap is proved. The counterexamples are wei-scale: `D` falls by one wei
    to about fifteen thousand wei (values of 10^19 to 10^28) at a fixed `A`, and `D/T` falls with the
    supply unchanged (`exchange`, `donate_admin_fees`) or moved (the other four). A "deployed" name
    (`…_deployed`) means an amplification, fee and admin fee in the range of deployed pools; the
    histories deploy the model with chosen parameters (for example fee 10^6 or 5·10^9, admin fee
    50 % or 100 %), **not** the recorded constructor arguments (`A = 100`, fee 4,000,000, admin fee
    0), and are not claims about historical chain states.

46. **Curve 3pool: Newton loops, what is and is not stated.** `get_D ≥ ⌊D*⌋` holds for positive
    balances and `A ≥ 1` at every tolerance (`getDChk_lower`); `get_D` is not monotone
    (`getD_not_mono`, at tolerance 1 and 2). After 255 bodies without a stopping test firing,
    `get_D`, `get_y` and `get_y_D` return the last iterate and do not revert (the source has no
    `raise` after the loop); `getD_cap_cycle` is an explicit balance triple at `A = 2000` where
    `get_D` cycles and returns `⌊D*⌋ + 2`. For `get_y_D` and `get_y` the law is root-or-successor for
    every non-reverting call, including a call that runs all 255 bodies (`loopYChk_rootOrSucc`); the
    checked arithmetic's reverts (word overflow, division by zero) are outside the law. The bytecode
    frames are linked to the model laws only for the calls listed in Section 5.11 (the first and
    second `get_y_D` of `calc_withdraw_one_coin` and `remove_liquidity_one_coin`, the `get_y` of
    `exchange`, `get_dy` and `get_dy_underlying`).

47. **Curve 3pool: amplification.** The model's `_A()` is the stored interpolation at the header
    time of the block that retained the frame; taking the parent's timestamp gives a different `A`
    (`pool_invocation_time_ne_parent` for a settled frame of one configured block, and an explicit
    ramp state). The interpolation law needs `future_A` and the source's one product below 2^256.
    `dMonoInA` states the direction of `D` in `A` only up to the loop error, and the ramp control is
    an honest-world model example, not a bytecode history.

48. **Curve 3pool: sufficient-gas and exact-gas liveness.** Each entry has two liveness forms.
    The **sufficient-gas** rows are stated with a closed cost: the entry executes when the gas `G` it
    is given meets the cost expression, which is an explicit function of the model state and the
    call's arguments (`costExchange`, `costAddLiquidity`, `costImbalance`, `costOneCoin`, and the
    constant `167000` for `remove_liquidity`), plus `k·U` for the `k` callee calls, `U` being the
    named per-call allowance of the callee premises. The expression is `0` where the model reverts.
    These are not exact-gas equalities: the "Live" gloss of Section 1 (an exact gas) does not apply
    to them. 3Crv's costs enter through its bounds (`U ≥ 70000` covers `totalSupply()`, `mint` and
    `burnFrom`). These theorems are unchanged by the exact forms. The **exact-gas** rows meet that
    gloss in this sense: for the residual gas `R`, the entry is the message `msg.withGas (R + c)`
    (at frame level, the frame entered with `R + c`), and `post.gasLeft = R`. The cost `c`
    (`rlExactCost`, `exExactCost`, `alExactCost`, `rliExactCost`, `ocExactCost`) is fixed before
    `R`. It is a function of the entry, of the call profiles' debit and successor functions, and of
    the model's words, which the statements pin by the model's own checks before `R`; the pinned
    words are unique (`Blanc.Lift.Curve3Pool.xpWords_unique`, `Blanc.Lift.Curve3Pool.alExactCost_words_eq`, `Blanc.Lift.Curve3Pool.RliWordsPin.unique`, `Blanc.Lift.Curve3Pool.ocWords_unique`). It reads no residual gas and is not an existential cost. The headroom (such as
    `167000 + 5·U ≤ R`, plus, where a statement keeps it, the sufficient-gas bound at `R + c`) and the
    no-wrap bound on the entry gas are separate premises, not part of `c`. What remains premised:
    the coin calls' exact profiles, with their debit and successor functions as parameters
    (environment premises: a coin's gas use is the coin's, not a Blanc fact); the per-execution
    keep premise, stated for the executions from the entry gas `R + c`; and, in the pool-level
    rows, 3Crv's profiles, which the composed rows discharge with 3Crv's own. `Jaune.Msg.withGas`,
    which replaces a message's gas grant, is declared in Blanc, not by Jaune.

49. **Curve 3pool: the joint checkpoint and 3Crv's side.** The composed statements take a
    `JointCheckpoint`: the pool's storage is a `Checkpoint`, 3Crv's storage satisfies `VyInv` over
    the listed live keys, the pool's token is 3Crv and 3Crv's minter is the pool. Installed code is a
    separate premise. The composed statements do not derive the joint state from the two
    deployments, and no statement chains the deployments into one history. `pool_3crv_u3_deployed`
    takes a joint checkpoint whose pool state is the constructor's `poolInitState`; no such world is
    instantiated (the checked synthetic worlds are not at `poolInitState`). `FreshKeys` is 3Crv's
    HASH-T premise, inherited.

50. **Curve 3pool: the closed instance.** `curve3pool_closed_agreeing` is for worlds that agree with
    the synthetic world `P0` on the trader, the pool (at `0x1000`), 3Crv, three synthetic `Token20`
    coins, addresses 4 and 0 and the four system addresses; all other accounts are arbitrary subject
    to being canonical with representable total ether. The block is the configured BPO2 chain reused
    from the WETH9 closed instance. The pool, 3Crv and the coins are installed in `P0` by
    construction, not by deployment; the joint checkpoint is decided by the checker on the pool's and
    3Crv's storage. The transaction is a synthetic one signed with a published test key. The
    conclusion is one swap and `D` strictly up at an unchanged supply. It is the `exchange` entry
    only; the other entries have end-to-end frame instances (item 53), not a block.

51. **Curve 3pool: counterexamples and witnesses are model-level or synthetic.** The U3 refutations
    and the three `callee_not_floor` counterexamples are kernel evaluations in the honest-world model
    (the pool state, the coins' `balanceOf(pool)` and 3Crv's supply, with honest coins and 3Crv),
    reached from the model constructor by the listed calls. They are not configured bytecode
    histories and not statements about transactions. The model is refined by the bytecode (Section
    5.11 frame row), but no theorem states that a configured history reaches those states. The
    synthetic prestates of the closed instance, the witnesses and the end-to-end instances are not
    the chain's.

52. **Curve 3pool: deployment is modeled.** `pool_deploy_covered` runs the recorded creation input
    as a CREATE message from the recorded deployer into an empty world at the recorded block
    timestamp. The 3pool was created in block 10,809,473, before Prague. The result is not historical
    inclusion, and the creation transaction is not replayed as a validated transaction.

53. **Curve 3pool: what the end-to-end instances show.** Jaune counts call depth down: a child
    frame runs at its parent's depth minus one, and a transaction's entry frame has depth 1,024.
    `ex_frame_live` is at the transaction's entry frame (depth 1,024), conditional on the `ExFrame`
    facts, which the closed instance's prepared message meets (`ex_prepared_frame`).
    `rl_frame_live`, `oc_frame_live`, `al_frame_live` and `rli_frame_live` run at remaining depth 1:
    a frame nested 1,023 calls deep, whose children cannot call further. Their discharge of the
    per-execution keep premise depends on that depth (a depth-0 child enters no frame, so it keeps
    the pool's storage and the code at address 4 whatever code it runs). They witness that each
    liveness theorem's premises are jointly satisfiable at a concrete EVM state; only `exchange` is
    shown at a transaction's entry. The four run on one synthetic world (pool balances 1,000, 2,000
    and 3,000, 3Crv supply 6,000, `Token20` coins), not mainnet state, from a concrete message whose
    accessed-address set is patched to hold address 4 warm, as the identity-readiness premise needs.
    `add_liquidity`'s instance runs its frame with gas 1,110,000, while the concrete message,
    transaction and block of the setup say 878,400, 900,000 and 900,000; the other three run at
    878,400. The calldata pass zero minimum amounts to `remove_liquidity` (`[0, 0, 0]`) and
    `remove_liquidity_one_coin` (`0`). The environments are partly existential: `oc_frame_live`
    concludes for some supply reading `T'`, `al_frame_live` for some environment `e` with only its
    supply pinned, and `ex_frame_live` for some balance readings with only the credited pull pinned;
    `rli_frame_live` adds the instance's world-chain invariant at the post as a further conjunct.
    All five instances are of the sufficient-gas frame theorems. No exact-gas theorem is
    instantiated end to end. For the exact forms the premise bundles are shown satisfiable
    (`removeLiquidity_exactPremises_satisfiable` and siblings), at the worlds of the
    sufficient-gas witnesses (for `exchange`, of its own exact witness); and each composed
    headline, exact and sufficient-gas, is applied to a coin chain and `Token20` coin profiles
    meeting its coin-chain hypotheses as stated (`pool_3crv_removeLiquidity_live_exact_literal`
    and siblings), with its 3Crv, coin-ledger and frame facts taken as world conditions. Neither
    instantiates a composed headline end to end: the call data, the model step, `IdReady`, the
    keep premise and the gas bounds stay hypotheses there.

54. **Curve 3pool: the environment is an observation, with one escape.** In every frame and history
    statement the model's environment is what the frame observed from its children (`EnvOf`). Each
    coin and token answer in it is constrained only when its target enters a code frame; for a
    target that is an undelegated precompile, which is answered without a child frame, the answer is
    unconstrained (the `framed … = false` disjunct of each field). The history statements exclude
    coins and token that are precompiles under any pool frame's rules, and the frame statements take
    the same as a premise. `remove_liquidity_one_coin`'s liveness concludes the raw effect at some
    supply reading `T'`, not at the premised `T`, and `add_liquidity`'s at some environment whose
    supply is the premised `T`; the other entries conclude at the premised readings.

55. **Curve 3pool: axioms.** The statements of Section 5.11 are covered by the union walk at the
    commit the audit runs on, as every constant of the library is (Section 8). None of them is one
    of the stricter claims of Section 8.

## Named premises and definitions

| Name | Declaration | Role |
|---|---|---|
| `PoolFrameEnv` | `Blanc.Lift.Curve3Pool.PoolFrameEnv` (`Blanc/Lift/Curve3Pool/FrameEnv.lean:32`) | the per-frame environment of the 3pool's frame statements: every direct child keeps the pool's storage, every coin child keeps 3Crv's storage, every child keeps the code at 4, the identity precompile is ready, no coin and not the token is a precompile |
| `PoolTraceEnv` | `Blanc.Lift.Curve3Pool.PoolTraceEnv` (`Blanc/Lift/Curve3Pool/History.lean:202`) | the environment of the 3pool's history statements: the per-frame callback premise, and trace-local exclusions (coins and token not precompiles, the identity precompile empty at the checkpoint with no authority and no CREATE frame, no system frame at the pool) |
| `EnvOf` | `Blanc.Lift.Curve3Pool.EnvOf` (`Blanc/Lift/Curve3Pool/Observe.lean:153`) | the 3pool model's environment as what a frame observed from its own children |
| `PoolCallsKeep` | `Blanc.Lift.Curve3Pool.PoolCallsKeep` (`Blanc/Lift/Curve3Pool/Observe.lean:196`) | every direct child of a 3pool frame leaves the pool's storage as it found it |
| `Curve3Pool.Checkpoint` | `Blanc.Lift.Curve3Pool.Checkpoint` (`Blanc/Lift/Curve3Pool/Layout.lean:141`) | the 3pool's storage abstracts the model state, the lock is clear and the address fields are addresses |
| `PoolRun` | `Blanc.Lift.Curve3Pool.PoolRun` (`Blanc/Lift/Curve3Pool/CommittedReplay.lean:37`) | the committed 3pool invocations replay from a state to a state |
| `WClosed` | `Blanc.Lift.Curve3Pool.WClosed` (`Blanc/Lift/Curve3Pool/LivePremises.lean:48`) | a world invariant survives the 3pool's own steps |
| `CoinBalOkAt` | `Blanc.Lift.Curve3Pool.CoinBalOkAt` (`Blanc/Lift/Curve3Pool/LivePremises.lean:108`) | a coin's `balanceOf(self)` call site answers the named word |
| `CoinPullOkAt` | `Blanc.Lift.Curve3Pool.CoinPullOkAt` (`Blanc/Lift/Curve3Pool/LivePremises.lean:119`) | a coin's `transferFrom` call site succeeds |
| `CoinPushOkAt` | `Blanc.Lift.Curve3Pool.CoinPushOkAt` (`Blanc/Lift/Curve3Pool/LivePremises.lean:113`) | a coin's `transfer` call site succeeds |
| `SupplyOkAt` | `Blanc.Lift.Curve3Pool.SupplyOkAt` (`Blanc/Lift/Curve3Pool/LivePremises.lean:102`) | the token's `totalSupply()` call site answers the named word |
| `MintOkAt` | `Blanc.Lift.Curve3Pool.MintOkAt` (`Blanc/Lift/Curve3Pool/LivePremises.lean:133`) | the token's `mint` call site succeeds |
| `BurnOkAt` | `Blanc.Lift.Curve3Pool.BurnOkAt` (`Blanc/Lift/Curve3Pool/LivePremises.lean:126`) | the token's `burnFrom` call site succeeds |
| `U3Ledger` | `Blanc.Lift.Curve3Pool.U3Ledger` (`Blanc/Lift/Curve3Pool/U3Ledger.lean:21`) | the six U3 bounds at given pre- and post-supplies |
| `FeeBounded` | `Blanc.Lift.Curve3Pool.FeeBounded` (`Blanc/Lift/Curve3Pool/U3Ledger.lean:127`) | the admin fee and the committed future admin fee are at most `10^10` |
| `Curve3Pool3CrvJoint.JointCheckpoint` | `Blanc.Composition.Curve3Pool3CrvJoint.JointCheckpoint` (`Blanc/Composition/Curve3Pool3CrvCheckpoint.lean:327`) | the joint 3pool and 3Crv checkpoint: storage, minter and address facts (not installed code) |
| `C3Ready` | `Blanc.Composition.Curve3Pool3CrvHeadlines.C3Ready` (`Blanc/Composition/Curve3Pool3CrvHeadlines.lean:39`) | 3Crv as the 3pool's frame sees it: 3Crv's code, the pool its minter, the pool's token slot naming it (derived from the history) |
| `MintFits` | `Blanc.Composition.Curve3PoolCalleeLive.MintFits` (`Blanc/Composition/Curve3PoolCalleeLive.lean:342`) | 3Crv accepts `mint(d, v)` from the pool at the given storage |
| `BurnFits` | `Blanc.Composition.Curve3PoolCalleeLive.BurnFits` (`Blanc/Composition/Curve3PoolCalleeLive.lean:349`) | 3Crv accepts `burnFrom(f, v)` from the pool at the given storage |
| `AgreesP0` | `Blanc.Composition.Curve3Pool3CrvInstance.AgreesP0` (`Blanc/Composition/Curve3Pool3CrvWorldAgrees.lean:28`) | a world agrees with the 3pool closed instance's synthetic world on the touched accounts |
| `ExFrame` | `Blanc.Composition.Curve3Pool3CrvInstance.ExFrame` (`Blanc/Composition/Curve3Pool3CrvTxFrame.lean:58`) | what the 3pool closed instance's `exchange` frame sees at its entry |

## Checking this document

The Curve 3pool statement pins include its exact-gas rows and premise-bundle
witnesses.

## Uses of the shared API

### From `docs/COMMON_API.md`: E2. The walk crosses a child frame

The 3pool's
`remove_liquidity` walk (`Blanc/Lift/Curve3Pool/Walk/RemoveLiquidity*.lean`) is the worked
example.

### From `docs/COMMON_API.md`: E3. I must carry a predicate over all entered child roots

(used by Curve)

### From `docs/COMMON_API.md`: E6. I need the exact successful wrapper trace, not only its final result

The Curve
  signed-transaction witness uses this proof.

### From `docs/COMMON_API.md`: I1. One instruction/line/function preserves an observation

The Curve 3pool instances are
  `Blanc/Lift/Curve3Pool/ExactMessage.lean` (`*_msg_exact`), with the exchange/add_liquidity
  stage transports in `Blanc/Lift/Curve3Pool/ExactStaticGas.lean`.

- For the literal memory the 3pool's crossed callees leave (exact walks of `add_liquidity`,
  `remove_liquidity_imbalance`, `remove_liquidity_one_coin`): `_A()`'s is `aMemNext` (`a_exactL`
  in [`Blanc/Lift/Curve3Pool/Callee/A.lean`](../../Blanc/Lift/Curve3Pool/Callee/A.lean), the
  `0x1e0` variant `a_exact_1e0L` in
  [`Blanc/Lift/Curve3Pool/Callee/AGrow.lean`](../../Blanc/Lift/Curve3Pool/Callee/AGrow.lean));
  `get_D_mem`'s is `getDMemNext` up to bytes (`Mem.EqExcept … fun _ => False`: one logical
  size, every byte equal; `getDMem_exactL` in
  [`Blanc/Lift/Curve3Pool/Callee/GetDMemExact.lean`](../../Blanc/Lift/Curve3Pool/Callee/GetDMemExact.lean),
  `getDMem_exact_400L` in
  [`Blanc/Lift/Curve3Pool/Callee/GetDMemGrow.lean`](../../Blanc/Lift/Curve3Pool/Callee/GetDMemGrow.lean)),
  since the callee's scratch writes are not materialised alike; the caller's next growing
  store makes it literal (`eqB_write_word_grow` in
  [`Blanc/Lift/MemGlue.lean`](../../Blanc/Lift/MemGlue.lean), below). The pool's literal-memory
  forward steps are one kit: `rxe_mstoreL`, `rxe_calldatacopyL`, `rxe_identityL` (with the
  identity call's canonical successor) and `rxe_sstoreX` (exact `SSTORE` charge) in
  [`Blanc/Lift/Curve3Pool/Walk/LiveKit.lean`](../../Blanc/Lift/Curve3Pool/Walk/LiveKit.lean), whose
  bounded twins `rxe_mstore`, `rxe_calldatacopy`, `rxe_identity`, `rxe_sstore_le` are
  projections; `rxe_mloadXL`, `rxe_sloadVX`, `rxe_staticWordE` (and the projections
  `rxe_mloadX`, `rxe_sloadB`/`rxe_sloadV`, `rxe_sstoreB`/`rxe_sstoreV`/`rxe_sstoreVX`,
  `rxe_mstoreW`, `rxe_staticWord`) in
  [`Blanc/Lift/Curve3Pool/Walk/ExchangeLiveKit.lean`](../../Blanc/Lift/Curve3Pool/Walk/ExchangeLiveKit.lean);
  `add_liquidity`'s `rxe_mloadXE`/`rxe_staticWordAlE` are their projections. A fee iteration's
  words are functions of its inputs (`RliDif.unique`, `RliFeeIter.unique` in
  [`Blanc/Lift/Curve3Pool/Walk/RliExactKit.lean`](../../Blanc/Lift/Curve3Pool/Walk/RliExactKit.lean)). The frame save/restore loops around them are literal
  through `rx_svFromLM` / `rx_rsFromLM` (`saveMem`/`restoreMem`) in
  [`Blanc/Lift/Curve3Pool/Walk/LiveLoops.lean`](../../Blanc/Lift/Curve3Pool/Walk/LiveLoops.lean).
  The bounded statements (`a_exact`, `getDMem_exact`, `rx_svFromL`, …) are their projections.

- For the 3pool's exact-gas entry frames and their stage cores (an exact walk to reuse or extend):
  `removeLiquidity_live_exact`, `exchange_live_exact`, `addLiquidity_live_exact`,
  `removeLiquidityImbalance_live_exact`, `removeLiquidityOneCoin_live_exact` in
  `Blanc/Lift/Curve3Pool/{RemoveLiquidityExactFrame,ExchangeExactLive,AddLiquidityExactFrame,RemoveLiquidityImbalanceExactFrame,OneCoinExactFrame}.lean`,
  each over a schedule with call data, premise bundle, closed cost and static-gas transport
  (`Walk/{RemoveLiquidity,AddLiquidity,Rli,OneCoin}ExactSchedule.lean`,
  `ExchangeExactSchedule.lean`, `ExactStaticGas.lean`) and relation-parametric stage cores (the
  `*E`/`*_core` walks in `Walk/RemoveLiquidityLive.lean`, `Walk/ExchangeLive*.lean`,
  `Walk/AlLive*.lean`, `Walk/RliLive*.lean`, `Callee/CalcWithdrawLive*.lean` (`rx_cw_*E`) and
  `Walk/OneCoinLive*.lean` (`rx_oc_*E`)), whose bounded statements are projections; the
  message-entry, history and composed twins are `ExactMessage.lean`, `HistoryLiveExact.lean`
  and `Blanc/Composition/Curve3Pool3CrvHeadlinesExact.lean`.

### From `docs/COMMON_API.md`: T2a. I need a frame invariant under trace-local entry premises

Worked use: the Curve 3pool history
  (curve-3pool-stableswap-v1).

Worked use: `Lift.Curve3Pool.pool_trace_admitted`.

### From `docs/COMMON_API.md`: T2c. I need that ledger replay on every wrapper up to a whole configured history

Worked use: the 3Crv callee crossing in
`Blanc/Composition/Curve3PoolCalleeLive.lean` (`c3crv_msg_run`).

### From `docs/COMMON_API.md`: C9.1. I need the lifted language and a checked certificate

Worked use:
  `Blanc/Lift/Curve3Pool/Check.lean`.

### From `docs/COMMON_API.md`: C9.9. I need to walk a successful lifted run

Curve 3pool's `Walk/AutoStep.lean`

The 3pool's
  `remove_liquidity_imbalance` liveness (`RliLiveCut`, `LiveLink`) is the worked example.

such as
  `getDMem_spec`

### From `docs/COMMON_API.md`: C9.10. I need a Vyper 0.2 runtime's idioms

Worked use:
  `Blanc/Lift/Curve3Pool/Walk/Dispatch.lean` (`xa_dispatch`, `xa_dispatch_miss`).

Worked use:
  `Blanc/Lift/Curve3Pool/Walk/DispatchLive.lean` (`rxe_dispatch`, one line per `rx_dispatch_*`).

(Curve 3pool: `poolLinks`/`pool_chain`)

### From `docs/COMMON_API.md`: M4. I need a block's trie root, its header hash, or a finite hash-separation premise

`BlockRecord.Checked` and `BlockRecord.Slot` are the kernel's side, generated by
  `scripts/curve-3pool-block-generate.py`'s pattern.
