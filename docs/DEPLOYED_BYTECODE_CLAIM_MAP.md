# Deployed-bytecode claim map

What Blanc proves about bytecode that is already on Ethereum mainnet: WETH9, the
Beacon deposit contract, the Curve 3Crv LP token, Lido's CircuitBreaker, the
Vyper nonreentrancy pair (the fixed pool implementation "V+" and the vulnerable
one "V−"), the EIP-7002 withdrawal-request predeploy, and the Uniswap V2 Pair.
Every headline below names the theorem that carries it, the
premises it needs, and what it does not say. The companion page for Blanc's own
ports is [`PORTING.md`](../PORTING.md); this page is about the exogenous
bytes themselves.

**A Blanc theorem is a statement about Jaune's modeled semantics, not a
deployment audit** ([`SECURITY.md`](../SECURITY.md)). Nothing here says that a
contract is safe, that its Solidity or Vyper source is correct, or that a
proved property is the property a user cares about. Each statement is read in
Lean, in the file the map cites, before it is relied on.

## 1. How to read this map

- **Names and lines.** Every declaration is written fully qualified, followed
  by the file and line where it is declared, for example
  `Blanc.Lift.Weth9.weth9_history_footprint` (`Blanc/Lift/Weth9/FootHistory.lean:114`). Names and lines are checked against the
  repository (Section 10). A name in a premise column that is *not* fully
  qualified is defined in Section 9.
- **Statement kinds.** *Safety* is a refinement or an invariant. *Live* is
  constructive: a successful `Exec` exists and its gas is exact. *Witness* is
  an existence statement; a conditional witness lists its premises. *Deploy* is a modeled deployment (Section 7).
  Levels are *frame*, *message*, *transaction* and *history*.
- **Configured history.** `ConfiguredHistoryTrace cfg checkpoint future`
  [`Blanc.ExecutionTrace.ConfiguredHistoryTrace` (`Blanc/ExecutionHistory.lean:86`)] is a retained replay of validated
  blocks (system messages, transactions, withdrawals, requests) under a valid
  chain configuration, every block's fork in `CoveredFork`. "After any
  configured history" quantifies over all of them.
- **Covered forks.** `CoveredFork` [`Blanc.CoveredFork` (`Blanc/Semantics.lean:167`)] is Prague, Osaka, BPO1 and
  BPO2. **Amsterdam is not covered.**
- **This commit.** Every figure and line in this document describes the commit
  you have checked out. Bind a quotation to `git rev-parse HEAD`, not to a
  hash written here.

## 2. Artifacts

The runtime bytes are the lifted inputs in `scripts/lift/inputs/`; the codehash
column is recomputed from those files by the checker (Section 10), and each
creation transaction is recorded in the entry's `provenance` in
`scripts/lift/certificates.json`. Each proxy row is the 45-byte EIP-1167
forwarder to the implementation above it.

| Contract | Address | Runtime bytes | keccak256 codehash | Creation transaction | Block |
|---|---|---:|---|---|---:|
| WETH9 | 0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2 | 3,124 | 0xd0a06b12ac47863b5c7be4185c2deaad1c61557033f56c7d4ea74429cbb25e23 | 0xb95343413e459a0f97461812111254163ae53467855c0d73e0f1e7c5b8442fa3 (deployer 0x4f26ffbe5f04ed43630fdc30a87638d53d0b0876, nonce 446) | 4,719,568 |
| Beacon deposit | 0x00000000219ab540356cBB839Cbe05303d7705Fa | 6,358 | 0x6c029a231254fadb724d63be769f75eedd66362df034a3e663252b49d062a666 | 0xe75fb554e433e03763a1560646ee22dcb74e5274b34c5ad644e7c0f619a7e1d0 (deployer 0xb20a608c624ca5003905aa834de7156c68b2e1d0, nonce 0) | 11,052,984 |
| Curve 3Crv LP token | 0x6c3F90f043a72FA612cbac8115EE7e52BDe6E490 | 2,276 | 0xb731b7a9a74c6c60d715f0c791d663f1530743a48337e7fab9cf3481afdd9feb | 0xa7d90e460bed56181e41b74d143ec98fe097c8391700e4e0788f5282053694f8 (deployer 0xbabe61887f1de2713c6f97e567623453d3c79f67, nonce 42) | 10,809,467 |
| Lido CircuitBreaker | 0x6019CB557978296BA3C08a7B73225C0975DFB2F7 | 4,584 | 0x63d4da6a25804fabdc61ace21c19d1f2e1425ab9ade8d8a348a2591e801836ec | 0x9a1328c1f63fcdfd53d611cfe9c9a5f4c284c4c3e61af9066d90acaac2d5279f (deployer 0xaCf5f111399a7c613D2f5b96b70F2Ea464D3cdF3, nonce 0) | 24,993,190 |
| Vyper pool implementation, fixed (V+) | 0x847ee1227a9900b73aeeb3a47fac92c52fd54ed9 | 18,320 | 0x59469db6b75b045025abb5386ae6b7ef7e1698d13ee93f3d4ed32d5f72506e0e | 0xfaad66f8fa2b4883b9e5c91b69e31ac8c2cdbc6d383b8776d0eee94d3ee0a251 | 17,110,099 |
| ETH/stETH pool proxy to the V+ implementation | 0x21e27a5e5513d6e65c4f830167390997aa84843a | 45 | 0x9e28a09452d2354fc4e15e3244dde27cbc4d52f12a10b91f2ca755b672bfa9be | not recorded | not recorded |
| Vyper pool implementation, vulnerable (V−) | 0x6326debbaa15bcfe603d831e7d75f4fc10d9b43e | 17,535 | 0xba0284a6a8a86734c1c777e3c6b5b56f2c8ba95dc0f7eba481c6d09da7885ebc | 0xd27491757b3a4bc9287ed44ce5c43de9f32131264548ce139f0a702c3d5f389e | 12,904,329 |
| Pool proxy to the V− implementation | 0x9848482da3ee3076165ce6497eda906e66bb85c5 | 45 | 0xbed04db3507e08e5220f6eadf98d5df05bdbc74df129c73fcbab7c441e86b124 | not recorded | not recorded |
| Uniswap V2 Pair (exhibit: the USDC/WETH pair) | 0xB4e16d0168e52d35CaCD2c6185b44281Ec28C9Dc | 11,293 | 0x5b83bdbcc56b2e630f2807bbadd2b0c21619108066b92a58de081261089e9ce5 | not recorded (runtime read at a finalized block, below) | not recorded |

Compilers, from the certificate provenance: 3Crv Vyper 0.2.4; the
CircuitBreaker solc 0.8.34; V− Vyper 0.2.15; V+ Vyper 0.3.7; the Uniswap V2 Pair
solc 0.5.16.

**The Uniswap V2 Pair row.** One runtime serves every V2 pair, so the row is the
exhibit instance's code. It was read by `eth_getCode` at finalized block 26,098,569
(block hash 0x296870f7b828ab4cc996959e744f0a8178889f39cc5e497610420536ec5703cd)
and is equal across three separately operated providers; no creation transaction
of this instance is recorded, and the lifted input is
`scripts/lift/inputs/uniswap-v2-pair-runtime.hex`. The creation code behind the
deployment theorems is the 11,636-byte input `scripts/lift/inputs/uniswap-v2-pair-creation.hex`:
its Keccak-256 is the factory's init-code hash
0x96e8ac4277198ff8b6f785478aa9a39f403cb768dd02cbee326c3e7da348845f, and bytes
261 to 11,553 of it are the lifted runtime. Nothing was recompiled: the
refinement of Section 5.8 is what ties the bytes to the v1.0.1 source.

**Canonical system contracts.** The Beacon `_sys` headlines assume the four
canonical system contracts are installed at their protocol addresses. Their
bytes are the definitions in `Blanc.beaconRootsCode` (`Blanc/SystemContracts.lean:35`) and its neighbours; the SHA-256
column is the digest recorded in each definition's docstring.

| Contract | Address | Bytes | SHA-256 | Definition |
|---|---|---:|---|---|
| EIP-4788 beacon roots | 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02 | 97 | cb7bd3e115730f7d57c15cd892880ed517ff4421bf43dfc7591198868fffe31d | `Blanc.beaconRootsCode` (`Blanc/SystemContracts.lean:35`) |
| EIP-2935 history storage | 0x0000F90827F1C53a10cb7A02335B175320002935 | 83 | 41cd74981e0201f79ebca054c4e8102a7e6faa28ce015d0048ab2250c1222c67 | `Blanc.historyStorageCode` (`Blanc/SystemContracts.lean:46`) |
| EIP-7002 withdrawal requests | 0x00000961Ef480Eb55e80D19ad83579A64c007002 | 504 | 22ac79b68752353c9bfbc6213fee1ec168df0f5abd2336c9ec239fc324e370b7 | `Blanc.withdrawalRequestCode` (`Blanc/SystemContracts.lean:56`) |
| EIP-7251 consolidation requests | 0x0000BBdDc7CE488642fb579F8B00f3a590007251 | 414 | 99e3d84dc4a4440c78a64619a2b451c08654cc83b44441585cb6db159478d661 | `Blanc.consolidationRequestCode` (`Blanc/SystemContracts.lean:92`) |

That a real chain holds exactly these bytes at these addresses is **not**
proved or checked here. It is the premise `SystemCodeInstalled`
[`Blanc.SystemCodeInstalled` (`Blanc/SystemContracts.lean:165`)] that a consumer states. Only the EIP-7002 code
contains call-type bytes at all (offsets 67, 123, 128, 141, all PUSH data).

**Synthetic fixtures** (not deployed artifacts): for V−, an attacker (85
bytes), a dispatcher attacker (186 bytes) and a coin (30 bytes); for V+, a
reader (41 bytes) and a receiver (86 bytes).

## 3. Trust base

| Component | What is trusted | Evidence |
|---|---|---|
| Lean toolchain `v4.34.0` | Kernel soundness | For every constant of every Blanc module, and therefore for every theorem this map cites, the reachable axioms are within `propext`, `Classical.choice`, `Quot.sound`; one from-scratch union walk (Section 8), not `#print axioms` or `collectAxioms` |
| Jaune revision `2737c8eb` | That its EVM and transaction definitions match Ethereum | Not a theorem. Conformance, as reported by that Jaune revision's own README and not re-run here: **5,006/5,006** supported fixture files and **34,205/34,205** cases of the execution-specs mainnet corpus (`tests@v20.0.2`), Prague through BPO2 including configured fork transitions |
| Lift certificates | Nothing | The Python producers are untrusted. Each certificate is accepted only by its Lean `cert_check`, a kernel decision, against the literal bytes |
| Runtime identity | That the lifted bytes are the mainnet bytes | Recorded in each certificate's `provenance`: `eth_getCode` agreement across independent public providers (two for WETH9, five for 3Crv, three for the Uniswap V2 Pair, at one finalized block); the creation inputs of WETH9, the Beacon deposit contract and 3Crv fetched from two providers and equal byte for byte; the Lido creation input equal to the frozen reference template plus its constructor arguments; the two pool implementations taken from Sourcify v2 records; the Uniswap V2 Pair creation code taken from the publisher artifact of `@uniswap/v2-core` 1.0.1, its Keccak-256 equal to the factory's init-code hash and its embedded runtime equal to the lifted runtime. The codehashes in Section 2 are recomputed from the lifted files by the checker |
| Fork scope | — | `CoveredFork` is Prague, Osaka, BPO1, BPO2. Amsterdam is not covered |
| Chain arithmetic | Model bound | Configured traces carry total ETH plus withdrawals below 2^256 (`SumNof` at the checkpoint) |
| Signature recovery | Premise of the signature-generic transaction theorems | `recoverSender … = .ok E` is a premise of every theorem that quantifies over all signed transactions, since there is then no single signature to evaluate. For a concrete transaction the kernel evaluates recovery: `Blanc.Drip.concreteCreateRecoveredSender` (`Blanc/DripConcreteHistory/Deployment.lean:196`), `Blanc.Drip.concreteExitRecoveredSender` (`Blanc/DripConcreteHistory/AccrualExit.lean:1215`), `Blanc.Lift.WithdrawalRequest.FloodTx.txB_recoveredSender` (`Blanc/Lift/WithdrawalRequest/FloodTxRecover.lean:149`) and, for V−, `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.txC_recoveredSender` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/TxCRecover.lean:99`) |

## 4. Premise classes

Every theorem hypothesis below has one of these classes; these are not Lean
logical axioms, and a clean axiom audit does not discharge them. The table says
whether a class is acceptable and whether deployment establishes INIT.

| Class | Meaning | Acceptable in a headline? | INIT established by a deployment theorem? |
|---|---|---|---|
| CODE | Installed code and fork identity | Yes | — |
| INIT | Stated once, at the checkpoint | Yes, if shown inhabited, ideally by deployment | **WETH9** footprint `FootInv ∅`: yes, no hash premise [`Blanc.Lift.Weth9.Creation.weth9_deploy_init_covered` (`Blanc/Lift/Weth9/Creation/DeployInit.lean:22`)]. **Beacon** `SolInv []`: yes, no hash premise [`Blanc.Lift.BeaconDeposit.Creation.beacon_deploy_covered` (`Blanc/Lift/BeaconDeposit/Creation/Deploy.lean:144`)]. **Curve** `VyInv … ∅`: yes, no hash premise [`Blanc.Lift.Curve3Crv.Creation.curve_deploy_covered` (`Blanc/Lift/Curve3Crv/Creation/Deploy.lean:297`)]. **Lido** `RegistryZeroRaw` and `StateInv`: only under two hash premises `ForeignApart 0 0` and `ForeignApart 0 1` (bound zero still quantifies address mapping keys) [`Blanc.Lift.LidoCircuitBreakerDeployed.Creation.lido_deploy_init_covered` (`Blanc/Lift/LidoCircuitBreakerDeployed/Creation/Deploy.lean:203`)]. **Uniswap V2 Pair** `InitializedCheckpoint`: yes, no hash premise, by a `CREATE2` deployment followed by the factory's `initialize` [`Blanc.Lift.UniswapV2Pair.Creation.pair_create2_initialized` (`Blanc/Lift/UniswapV2Pair/Creation/DeployInit.lean:126`)]. **V±**: synthetic prestates, none |
| ENTRY | Required at every entered frame | Only if environmental, never invariant-shaped | — |
| HASH-T | Exact separation of the hashes and keys actually computed or touched in the trace, including avoidance of fixed slots where stated | Yes when stated; narrower and amenable to finite checking with a concrete initial footprint. Computational collision resistance does not entail this exact fact; fixed-slot avoidance also concerns target/preimage behavior. No cryptographic reduction is proved. The Lido finite tier (Section 5.4) states its instances as decidable checks on explicit key lists, so a concrete instance is closed by kernel evaluation | — |
| HASH-U | Exact separation quantified over all 2^160 addresses or indices | Needs justification; not established here. The finite domain does not make proof impossible. Under a random-function model of Keccak the estimated failure probability is about q·2^-94 per frame (q = written slots): **heuristic only, with no reduction or bound proved** | — |
| ENV | Gas, warmth, depth, static flag, callee behaviour, trace-local exclusions (no authorization or CREATE at given addresses) | Yes when stated; better derived | — |
| ARITH | Numeric bounds | Yes | — |

The per-frame calldata bound (below 2^256) is not a premise of any history
theorem: it holds for every raw frame of every configured history on all
covered forks [`Blanc.ExecutionTrace.ConfiguredHistoryTrace.calldata_bound` (`Blanc/ExecutionTraceCalldata.lean:780`);
`Blanc.ExecutionTrace.ConfiguredHistoryTrace.frameAdmitted_calldata` (`Blanc/ExecutionTraceCalldata.lean:797`)], because
`tx.gas ≤ blockGasLimit < 2^63`. Frame-level (non-history) theorems still take
it as a hypothesis about their own `sevm`.

## 5. Per contract

### 5.1 WETH9: booked-slot backing and exact ledger replay

The headline is **not** "solvency" of arbitrary holders. It is: after any
configured history, the contract's storage is the footprint of the tracked
keys, and the tracked balances are backed by its ETH.

**Safety and refinement**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| After any configured history: code intact, and there is a footprint `K ⊆ K₀ ∪ touched` such that every nonzero storage word is at a fixed slot (0, 1, 2) or a tracked key's slot, tracked slots are injective and apart from the fixed ones, and the sum of tracked balance words is at most the contract's ETH | `Blanc.Lift.Weth9.weth9_history_footprint` (`Blanc/Lift/Weth9/FootHistory.lean:114`); the universe form `Blanc.Lift.Weth9.weth9_history_footprint_universe` (`Blanc/Lift/Weth9/FootHistory.lean:86`) names `K` and adds `SumNof future`; a deployment-shaped checkpoint instantiates INIT by `Blanc.Lift.Weth9.FootInv.deployed` (`Blanc/Lift/Weth9/Footprint.lean:211`) | History / safety | CODE; ARITH `SumNof`; INIT `FootInv K₀`; **HASH-T** `KeysFresh K₀ (historyTouchedKeys ca trace)` (finite, trace-local, includes rolled-back frames) | The headline; no universal hash premise |
| Ledger reading: tracked holders' stored balances are backed in total and one by one; an address on no fixed or tracked slot books nothing | `Blanc.Lift.Weth9.weth9_history_backed` (`Blanc/Lift/Weth9/FootHistory.lean:130`) | History / safety | as above | |
| Frame form inside a root derivation | `Blanc.Lift.Weth9.foot_frame_post_in` (`Blanc/Lift/Weth9/FootFrame.lean:237`) | Frame / safety | CODE; `KeyInj U`; `frameKeys sevm ⊆ U` | Supporting |
| The premise is necessary: a written slot that coincides with a tracked balance slot breaks backing | `Blanc.Lift.Weth9.approve_collision_breaks_footprint` (`Blanc/Lift/Weth9/FootFrame.lean:212`), `Blanc.Lift.Weth9.trackedSum_collision_breaks_backing` (`Blanc/Lift/Weth9/FootFrame.lean:199`); a related control `Blanc.Lift.Weth9.approve_collision_control` (`Blanc/Lift/Weth9/Approve.lean:198`) | Frame / control | a hash collision is posited | |

**History (committed replay)**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| The footprint ledger at the future state equals the model `Ledger.run` over exactly the settlement-committed writer invocations at the contract, in trace order (rolled-back frames absent, views contribute nothing, re-entered calls after the withdraw that sent them); also code intact, `SumNof future`, `FootInv U future`, and the model run with ETH stays `Backed` | `Blanc.Lift.Weth9.weth9_history_committed` (`Blanc/Lift/Weth9/CommittedHistory.lean:62`) | History / safety, exact extraction | the same four as `weth9_history_footprint` | The list is definitional [`Blanc.Lift.Weth9.committedInvocations` (`Blanc/Lift/Weth9/CommittedReplay.lean:46`)]. Frames contribute iff target = contract, non-static, and a writer selector; **the non-static filter is a statement-level choice, not proved impossible for WETH9 writers** (it is proved for Curve and Beacon) |

**Liveness.** All explicit costs are sums of fixed parts and
`sloadCost`/`sstoreCost`/`callNet`; `G` is the gas left at the end. "Fresh
frame" means empty stack and memory, non-static, value 0, the contract's code,
a covered fork, and calldata of at least 4 bytes and below 2^256.

| Level | Claim | Theorem | Cost / gas formula | Premises beyond a fresh frame |
|---|---|---|---|---|
| Frame | `balanceOf` and `decimals` execute and return the stored word | `Blanc.Lift.Weth9.weth9_balanceOf_gas_exact` (`Blanc/Lift/Weth9/Live.lean:792`), `Blanc.Lift.Weth9.weth9_decimals_gas_exact` (`Blanc/Lift/Weth9/Live.lean:813`) | 2,534 / 534 (`balanceOf` cold / warm), 2,444 / 444 (`decimals`) [`Blanc.Lift.Weth9.balanceOfGas9_eq` (`Blanc/Lift/Weth9/Live.lean:603`)] | ENV: gas |
| Frame | `approve` writes `allowance[caller][guy] := wad` and returns `true` | `Blanc.Lift.Weth9.weth9_approve_live` (`Blanc/Lift/Weth9/LiveWriters.lean:50`) | `approveGas = 2320 + sstoreCost` [`Blanc.Lift.Weth9.approveGas` (`Blanc/Lift/Weth9/LiveApprove.lean:209`)]; worked case: cold, never-written slot, nonzero `wad` costs **24,420** [`Blanc.Lift.Weth9.approveGas_cold_set` (`Blanc/Lift/Weth9/LiveWriters.lean:653`)]; needs `380 ≤ G` | none |
| Frame | `deposit()` and the payable fallback | `Blanc.Lift.Weth9.weth9_deposit_live` (`Blanc/Lift/Weth9/LiveWriters.lean:84`), `Blanc.Lift.Weth9.weth9_fallback_short_live` (`Blanc/Lift/Weth9/LiveWriters.lean:109`), `Blanc.Lift.Weth9.weth9_fallback_live` (`Blanc/Lift/Weth9/LiveWriters.lean:132`) | `depositGas = 1874 + depositLoad + depositStore` [`Blanc.Lift.Weth9.depositGas` (`Blanc/Lift/Weth9/LiveDeposit.lean:195`)]; the fallback adds 1631 / 1896; needs `844 ≤ G` | none |
| Frame | `transfer` | `Blanc.Lift.Weth9.weth9_transfer_live` (`Blanc/Lift/Weth9/LiveWriters.lean:257`) | `transferGas = xferGasSelf + 470` [`Blanc.Lift.Weth9.transferGas` (`Blanc/Lift/Weth9/LiveTransfer.lean:649`)]; needs `353 ≤ G` | ENV: `wad ≤ balanceOf[caller]` |
| Frame | `transferFrom`, all three allowance cases | `Blanc.Lift.Weth9.weth9_transferFrom_live` (`Blanc/Lift/Weth9/LiveWriters.lean:434`) | `transferFromGas = xferGas{Self,Max,Allow} + 340` [`Blanc.Lift.Weth9.transferFromGas` (`Blanc/Lift/Weth9/LiveWriters.lean:425`)]; needs `377 ≤ G` | a storage effect exists (`xferStorStep`) |
| Frame | `withdraw(wad)` to an EOA, every `wad` (0 included) | `Blanc.Lift.Weth9.weth9_withdraw_any_live` (`Blanc/Lift/Weth9/LiveWriters.lean:535`); nonzero `wad`: `Blanc.Lift.Weth9.weth9_withdraw_live` (`Blanc/Lift/Weth9/LiveWriters.lean:329`) | `withdrawGas = 2040 + sload + sload + sstore + callNet` [`Blanc.Lift.Weth9.withdrawGas` (`Blanc/Lift/Weth9/LiveWithdraw.lean:441`)]; `wad = 0`: `Blanc.Lift.Weth9.withdrawZeroGas` (`Blanc/Lift/Weth9/LiveWithdraw.lean:562`); needs `811 ≤ G` | ENV: the caller has no code, is not a precompile, depth ≠ 0, and the contract holds the ETH |
| Frame | `withdraw` to a **contract** | `Blanc.Lift.Weth9.weth9_withdraw_send_live` (`Blanc/Lift/Weth9/LiveWriters.lean:592`) | `Blanc.Lift.Weth9.withdrawSendPre` (`Blanc/Lift/Weth9/LiveWriters.lean:583`); ends with `r − 1489` | **`SendOk` callee premise** [`Blanc.Lift.Weth9.SendOk` (`Blanc/Lift/Weth9/LiveWriters.lean:570`)]: the CALL succeeds, leaves at least 1489 gas, and changes no contract storage |
| Model | Any writer the model accepts at the extended footprint realises the model's next ledger, gas-exact | `Blanc.Lift.Weth9.weth9_approve_model_live` (`Blanc/Lift/Weth9/LiveModel.lean:52`), `Blanc.Lift.Weth9.weth9_deposit_model_live` (`Blanc/Lift/Weth9/LiveModel.lean:72`), `Blanc.Lift.Weth9.weth9_transfer_model_live` (`Blanc/Lift/Weth9/LiveModel.lean:90`), `Blanc.Lift.Weth9.weth9_transferFrom_model_live` (`Blanc/Lift/Weth9/LiveModel.lean:117`), `Blanc.Lift.Weth9.weth9_withdraw_model_live` (`Blanc/Lift/Weth9/LiveModel.lean:144`) | as the frame rows | INIT `FootInv K`; HASH-T `KeysFresh K (call keys)`; model acceptance |
| Reachable state | After any configured history, a tracked holder can `withdraw(wad)` to an EOA, `deposit()`, or `transfer` | `Blanc.Lift.Weth9.weth9_history_withdraw_live` (`Blanc/Lift/Weth9/LiveHistory.lean:75`), `Blanc.Lift.Weth9.weth9_history_deposit_live` (`Blanc/Lift/Weth9/LiveHistory.lean:130`), `Blanc.Lift.Weth9.weth9_history_transfer_live` (`Blanc/Lift/Weth9/LiveHistory.lean:158`) | `withdrawAnyGas` / `depositGas` / `transferGas` | the history premises (CODE, ARITH, INIT, HASH-T); a fresh frame at `pre.state = future.state`; the holder in the tracked universe. **No history-level `approve` or `transferFrom` liveness** |
| Transaction | A type-2 `withdraw(wad)` transaction is admitted by `processTransaction`, debits the holder's slot, moves `wad` ETH, and uses exact gas | `Blanc.Lift.Weth9.weth9_tx_withdraw` (`Blanc/Lift/Weth9/LiveTx.lean:359`); at any configured history's future state `Blanc.Lift.Weth9.weth9_history_tx_withdraw` (`Blanc/Lift/Weth9/LiveTx.lean:631`) | intrinsic `21000 + 4·calldataTokens` [`Blanc.Lift.Weth9.withdrawIntrinsicGas` (`Blanc/Lift/Weth9/LiveTx.lean:47`)]; frame **13,940** (`wad ≠ 0`) or **4,440** (`wad = 0`) [`Blanc.Lift.Weth9.withdrawFrameGas` (`Blanc/Lift/Weth9/LiveTx.lean:52`)]; refund 4,800 iff a nonzero `wad` empties the balance [`Blanc.Lift.Weth9.withdrawRefund` (`Blanc/Lift/Weth9/LiveTx.lean:57`)]; `gasUsed = intrinsic + frame − refund` [`Blanc.Lift.Weth9.withdrawGasUsed` (`Blanc/Lift/Weth9/LiveTx.lean:59`)] | the signature-recovery premise; a sender EOA with nonce and funds; `tx.gas ≥ intrinsic + frame + 811` and `≤ 2^24` (EIP-7825); block room; coinbase ∉ {E, ca}; `FootInv` at the block state; the holder tracked and `wad ≤` its balance |

**Deployment / INIT**

| Claim | Theorem | Kind | Premises |
|---|---|---|---|
| The recorded creation input (nonce 446 from the recorded deployer) succeeds, installs the certified runtime, and leaves exactly the constructor's `name`/`symbol`/`decimals` storage; the address is the CREATE address | `Blanc.Lift.Weth9.Creation.weth9_deploy_covered` (`Blanc/Lift/Weth9/Creation/Deploy.lean:148`); general `Blanc.Lift.Weth9.Creation.weth9_create` (`Blanc/Lift/Weth9/Creation/Deploy.lean:55`); the storage `Blanc.Lift.Weth9.Creation.deployedStor` (`Blanc/Lift/Weth9/Creation/Deploy.lean:35`) has every nonzero word in {0, 1, 2} [`Blanc.Lift.Weth9.Creation.deployedStor_metadata` (`Blanc/Lift/Weth9/Creation/Deploy.lean:38`)] | deploy | none (closed) |
| That storage satisfies the footprint INIT with the empty tracked set, for every ETH balance | `Blanc.Lift.Weth9.Creation.weth9_deploy_init_covered` (`Blanc/Lift/Weth9/Creation/DeployInit.lean:22`), by `weth9_deploy_covered` and `Blanc.Lift.Weth9.FootInv.deployed` (`Blanc/Lift/Weth9/Footprint.lean:211`) (metadata-only storage implies `FootInv ∅`) | deploy / INIT | none |
| Empty storage satisfies `StateInv` | `Blanc.Lift.Weth9.weth9_init_stateInv` (`Blanc/Lift/Weth9/Init.lean:42`) | satisfiability | none |

**Fork coverage.** The history and liveness theorems assume or derive
`CoveredFork`; deployment is stated for every covered fork by the `_covered`
forms; the transaction theorem assumes `CoveredFork benv.stat.fork`.

**Non-claims.** Holder-level `balanceOf` sums beyond tracked keys;
redeemability by third parties; authorization; that `decimals` returns the
constant 18 (it returns storage); static frames' writers; rolled-back frames'
effects (in the committed list); Beacon-style authenticated history. The
footprint freshness premise ranges over a **uniform five-key** set per raw
target frame (`frameKeys sevm = [bal caller, bal a0, bal a1, allow a0 caller,
allow caller a0]`, `a0 = dataWord 4`, `a1 = dataWord 36`), independent of the
selector, so it also constrains keys derived from the calldata of view calls.

**A second statement with a universal hash premise.** `Blanc.Lift.Weth9.weth9_history_preserves_solvent` (`Blanc/Lift/Weth9/Solvency.lean:80`)
proves a booked-ledger invariant under
the per-frame **HASH-U** premise `AllowAdmitted` [`Blanc.Lift.Weth9.AllowAdmitted` (`Blanc/Lift/Weth9/Premise.lean:24`)] and INIT
`StateInv`. `StateInv` is satisfiable (`weth9_init_stateInv`) but **no
deployment theorem establishes it**; the deployment result is the footprint
INIT above. Cite this form only with the HASH-U disclosure, and use
`weth9_history_footprint` for holder-level backing with trace-local premises.

### 5.2 Beacon deposit: exact committed deposit history

**Safety, refinement and history**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| After any configured history, storage is the accumulator of the initial history followed by exactly the deposits whose frames were committed (rollback-filtered by settlement), in order. **The mainnet-satisfiable form** | `Blanc.Lift.BeaconDeposit.configuredHistory_solInv_sys` (`Blanc/Lift/BeaconDeposit/BeaconEnv.lean:155`); base form `Blanc.Lift.BeaconDeposit.configuredHistory_solInv` (`Blanc/Lift/BeaconDeposit/CommittedHistory.lean:73`) | History / safety, exact extraction | CODE `installed`; INIT `SolInv … initialHistory`; ENV (trace-local, finite): `SystemCodeInstalled checkpoint` (canonical bytes at the four system addresses), `NoAuthorityAt` and no CREATE frame at those four addresses and at `0x02`, `getCode 2 = empty` at the checkpoint. **No hash premise.** The calldata bound, system exclusion [`Blanc.Lift.BeaconDeposit.system_of_installed` (`Blanc/Lift/BeaconDeposit/BeaconEnv.lean:137`), `Blanc.ExecutionTrace.ConfiguredHistoryTrace.systemFrames_of_installed` (`Blanc/ExecutionTraceSystemCode.lean:274`)], `0x02` warmth and no-delegation are derived | the `0x02` warmth is derived from EIP-2929 pre-warming, preserved across rollback |
| The count slot is the number of deposits; the root is the reference mixed Merkle root of that exact list | `Blanc.Lift.BeaconDeposit.configuredHistory_count_sys` (`Blanc/Lift/BeaconDeposit/BeaconEnv.lean:176`), `Blanc.Lift.BeaconDeposit.configuredHistory_root_sys` (`Blanc/Lift/BeaconDeposit/BeaconEnv.lean:196`); reference correctness `Blanc.BeaconDeposit.root_correct` (`Blanc/BeaconDepositCorrectness.lean:284`) | History / safety | as above | |
| `get_deposit_count` and `get_deposit_root` on the final state succeed with those outputs, at exact gas | `Blanc.Lift.BeaconDeposit.configuredHistory_count_view` (`Blanc/Lift/BeaconDeposit/CommittedHistory.lean:116`), `Blanc.Lift.BeaconDeposit.configuredHistory_root_view` (`Blanc/Lift/BeaconDeposit/CommittedHistory.lean:143`) | History and frame / live | **per-frame `beaconEntry`** (ENV: `0x02` warm, undelegated), depth, gas | there is no `_sys` form of the views |
| A successful frame is exactly the model step (decode, accumulator, event, storage shape); other selectors change no storage or logs | `Blanc.Lift.BeaconDeposit.deposit_frame_refines` (`Blanc/Lift/BeaconDeposit/Safe.lean:333`) | Frame / safety | CODE; ENV `ShaReady`; INIT-shaped `SolInv pre` | |

**Liveness.** Frame: `Blanc.Lift.BeaconDeposit.deposit_exec_solInv` (`Blanc/Lift/BeaconDeposit/DepositExec.lean:60`). A model-accepted deposit executes
at exactly `G + depositGas`, with `depositGas = 656 + bodyGas` and `bodyGas =
14551 + sloadCost(count) + countStoreCost + bodyInsertGas` [`Blanc.Lift.BeaconDeposit.depositGas` (`Blanc/Lift/BeaconDeposit/DepositExec.lean:25`),
`Blanc.Lift.BeaconDeposit.bodyGas` (`Blanc/Lift/BeaconDeposit/BodySpec.lean:155`)], appending the model node and event. `get_deposit_count` costs
1,514 warm / 3,514 cold; `get_deposit_root` costs `Blanc.Lift.BeaconDeposit.rootViewGas` (`Blanc/Lift/BeaconDeposit/RootView.lean:596`). Reachable
state: `Blanc.Lift.BeaconDeposit.configuredHistory_deposit_live` (`Blanc/Lift/BeaconDeposit/Liveness.lean:24`) says that after any configured history a
model-accepted deposit executes at exact gas and appends exactly the new node
(premises: per-frame `beaconEntry`, `DepositDecodable`, `ShaReady`, sentry and
bound side conditions). **There is no transaction-level Beacon liveness**: a
deposit carries value, which needs a value-carrying envelope.

**Deployment / INIT.** `Blanc.Lift.BeaconDeposit.Creation.beacon_deploy_covered` (`Blanc/Lift/BeaconDeposit/Creation/Deploy.lean:144`), for every covered fork
`f`: the address is the CREATE address of the recorded deployer at nonce 0, and
the deployment message `deployMsg.withFork f` installs the certified runtime
and leaves `SolInv (getStor post) []`. General form `Blanc.Lift.BeaconDeposit.Creation.beacon_create` (`Blanc/Lift/BeaconDeposit/Creation/Deploy.lean:53`). No
hash premise. Satisfiability: `Blanc.Lift.BeaconDeposit.beacon_zero_init` (`Blanc/Lift/BeaconDeposit/Init.lean:71`) (`SolInv beaconZeroStor []`).

**Fork coverage.** History and `_sys` theorems on all covered forks;
`beacon_deploy_covered` quantifies over covered forks.

**Non-claims.** Revert routes and payloads; BLS validity; authenticated
deposit history; historical inclusion of the constructor. The premises are the
honest form of the environment: trace-local and finite, but
`SystemCodeInstalled` posits the canonical bytes on the chain (Section 2).

### 5.3 Curve 3Crv: model refinement, exact committed replay, conservation

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| **History:** the final storage abstracts the model state reached by `Curve3Crv.step` over **exactly the settlement-committed writer invocations** at the contract, in trace order, and that model state is conserving (`totalSupply = Σ balances`) | `Blanc.Lift.Curve3Crv.c3crv_history_committed_derived` (`Blanc/Lift/Curve3Crv/CommittedHistory.lean:210`); base form `Blanc.Lift.Curve3Crv.c3crv_history_committed` (`Blanc/Lift/Curve3Crv/CommittedHistory.lean:171`) (takes the calldata bound as a hypothesis) | History / safety, exact extraction | CODE; INIT `VyInv … initialKeys`; **HASH-T** `FreshKeys initialKeys (historyTouchedKeys ca trace)` (rolled-back frames included); the calldata bound is derived | No static filter: `Blanc.Lift.Curve3Crv.c3crv_writer_nonstatic` (`Blanc/Lift/Curve3Crv/Safe.lean:202`) proves a writer cannot succeed in a static frame |
| A successful frame from a fresh entry is exactly the model step: writers (events, storage abstraction, owner answer for `set_name`, empty STOP output), **and views (storage and logs unchanged, return bytes equal the model output)** | `Blanc.Lift.Curve3Crv.c3crv_frame_refines` (`Blanc/Lift/Curve3Crv/Safe.lean:249`); raw form `Blanc.Lift.Curve3Crv.c3crv_frame_refines_raw` (`Blanc/Lift/Curve3Crv/Safe.lean:83`) (output stated relative to the entry output) | Frame / safety | CODE; covered fork; calldata bound below 2^256 (a frame-level hypothesis); **fresh entry as explicit premises** `pre.stack = []`, `pre.memory = Mem.empty`, `pre.output = []`; INIT-shaped `VyInv pre`; HASH-T `FreshKeys` (call keys); a successful `Exec 0 sevm pre (.ok post)` | Every successful selector is covered (misses and short calldata have no successful run). The fresh-entry facts are hypotheses here, not derived from a `Frame.enter` equation |
| Token-model properties: `step` preserves conservation; the initial state is conserving; supply and minter change only by the minter; non-minter `transferFrom` spends allowance even at the maximum value, while the minter retains allowances; zero-first approve; authorized allowance and balance changes | `Blanc.Curve3Crv.step_conserved` (`Blanc/Curve3Crv/Properties.lean:160`), `Blanc.Curve3Crv.init_conserved` (`Blanc/Curve3Crv/Properties.lean:165`), `Blanc.Curve3Crv.supply_change_by_minter` (`Blanc/Curve3Crv/Properties.lean:182`), `Blanc.Curve3Crv.minter_change_by_minter` (`Blanc/Curve3Crv/Properties.lean:201`), `Blanc.Curve3Crv.transferFrom_spends_allowance` (`Blanc/Curve3Crv/Properties.lean:223`), `Blanc.Curve3Crv.transferFrom_spends_max_allowance` (`Blanc/Curve3Crv/Properties.lean:233`), `Blanc.Curve3Crv.transferFrom_minter_keeps_allowances` (`Blanc/Curve3Crv/Properties.lean:249`), `Blanc.Curve3Crv.approve_zero_first` (`Blanc/Curve3Crv/Properties.lean:258`), `Blanc.Curve3Crv.allowance_change_authorized` (`Blanc/Curve3Crv/Properties.lean:267`), `Blanc.Curve3Crv.balance_debit_authorized` (`Blanc/Curve3Crv/Properties.lean:307`) | Model / safety | the model only | bridged to the bytes by the two rows above |

**Liveness.** Frame: `Blanc.Lift.Curve3Crv.c3crv_step_exec` (`Blanc/Lift/Curve3Crv/Exec.lean:53`). A model-accepted call (every selector
except `set_name`) executes with **an exact but existentially quantified
cost**: `∃ c, ∀ G > gCallStipend, … exec at G + c … gasLeft = G`, ending in the
model's step with exact logs and return bytes. **No closed cost formula is
claimed.** `Blanc.Lift.Curve3Crv.c3crv_setName_exec` (`Blanc/Lift/Curve3Crv/Exec.lean:86`): `∃ R P` such that any callee answering under
`OwnerCallOk` (the minter's `owner()` STATICCALL answers the caller and leaves
`R`) at `Gc` makes every frame with at least `Gc + P` gas succeed; this is a
**callee premise**. Reachable state: `Blanc.Lift.Curve3Crv.c3crv_history_live` (`Blanc/Lift/Curve3Crv/Liveness.lean:23`) and
`Blanc.Lift.Curve3Crv.c3crv_history_setName_live` (`Blanc/Lift/Curve3Crv/Liveness.lean:70`) say that after any configured history every
model-accepted call executes at the future storage (premises: the history
premises plus `FreshKeys` for the new call's own keys, and `pre.output = []`).
No transaction-level liveness.

**Deployment / INIT.** `Blanc.Lift.Curve3Crv.Creation.curve_deploy_covered` (`Blanc/Lift/Curve3Crv/Creation/Deploy.lean:297`), for every covered fork
`f`: a nonce-42 CREATE from the recorded deployer installs the runtime and
leaves `deployedStor deployer` with `VyInv … (curveDeployedState deployer) (fun _
=> False)`. The recorded deployment therefore satisfies the history theorem's
checkpoint predicate (name, symbol, decimals 18, supply 0, minter = deployer)
with no hash premise; the constructor's write of 0 at `keccak(3‖caller)` is
discharged by kernel evaluation. General form `Blanc.Lift.Curve3Crv.Creation.curve_create` (`Blanc/Lift/Curve3Crv/Creation/Deploy.lean:207`) (storage
`deployedStor`). `Blanc.Lift.Curve3Crv.curve_init_vyInv` (`Blanc/Lift/Curve3Crv/Init.lean:37`) is a satisfiability instance.

**Fork coverage.** History and liveness on covered forks;
`curve_deploy_covered` quantifies over covered forks.

**Non-claims.** Log and return bytes at the *history* level (only at frame
level); replay equal to the *raw* trace's writer sequence (rolled-back frames
are, by design, not in it); a closed cost formula; `set_name` without the
owner-call premise.

### 5.4 Lido CircuitBreaker: registry integrity (not "targets are paused")

The Lido results come in two tiers. The **finite tier** (frame and deployment
level) states registry agreement over an explicit, caller-supplied list of
address probes, and every hash-separation premise it takes is a decidable check
on concrete key lists, evaluable by the kernel; it claims nothing about an
address outside the probe list and proves nothing at history level. The
**history tier** keeps **universal (HASH-U) premises** with the explicit
random-function heuristic of Section 4 (about q·2^-94 per frame; no reduction
or probability bound is proved).

**Finite tier (frame and deployment).** The observation is `RegistryOn storage
entries probes` [`Blanc.Lift.LidoCircuitBreakerDeployed.RegistryOn` (`Blanc/Lift/LidoCircuitBreakerDeployed/FiniteRegistry.lean:24`)]: the entry list is valid
(below 2^252 entries, targets without repetition, nonzero canonical targets and
pausers, canonical probes), the length word and every live array cell agree
with the list, and for each probe the assignment, index and count words agree
with the list. `checkRegistryOn` [`Blanc.Lift.LidoCircuitBreakerDeployed.checkRegistryOn` (`Blanc/Lift/LidoCircuitBreakerDeployed/FiniteRegistry.lean:39`)] decides it
[`Blanc.Lift.LidoCircuitBreakerDeployed.checkRegistryOn_eq_true` (`Blanc/Lift/LidoCircuitBreakerDeployed/FiniteRegistry.lean:55`)]; `checkLiveCovered`
[`Blanc.Lift.LidoCircuitBreakerDeployed.checkLiveCovered` (`Blanc/Lift/LidoCircuitBreakerDeployed/FiniteRegistry.lean:74`)] decides that every listed target and
pauser is a probe. The separation checks are the shared `checkFaithfulOn`
[`Blanc.SlotFootprint.checkFaithfulOn` (`Blanc/SlotFootprint.lean:133`)] (each written key and
each observed key with the same slot are the same key) and `checkApartOn`
[`Blanc.SlotFootprint.checkApartOn` (`Blanc/SlotFootprint.lean:145`)] (no observed key sits on a
given raw slot), each with its exact soundness theorem
[`Blanc.SlotFootprint.checkFaithfulOn_eq_true` (`Blanc/SlotFootprint.lean:138`),
`Blanc.SlotFootprint.checkApartOn_eq_true` (`Blanc/SlotFootprint.lean:150`)], applied to the
finite query list `registryQueries probes length`
[`Blanc.Lift.LidoCircuitBreakerDeployed.registryQueries` (`Blanc/Lift/LidoCircuitBreakerDeployed/FiniteRegistry.lean:17`)]: the length key, the live array keys and
the three mapping keys of each probe.

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| A successful pc-0 `Exec` of the installed runtime at `registerPauser(target, p)`, for an existing `target` and a nonzero new pauser `p`, takes a storage on which `checkRegistryOn entries probes` holds to one on which it holds for `setEntryAt index (target, p) entries`, and live coverage is retained | `Blanc.Lift.LidoCircuitBreakerDeployed.registerPauser_nonzero_finite` (`Blanc/Lift/LidoCircuitBreakerDeployed/FiniteFrame.lean:97`); the body from the entry-32 subroutine `Blanc.Lift.LidoCircuitBreakerDeployed.registerPauser_body_finite` (`Blanc/Lift/LidoCircuitBreakerDeployed/FiniteFrame.lean:43`) | Frame / safety | CODE (installed code, covered fork); a fresh pc-0 entry and the selector; `checkRegistryOn` and `checkLiveCovered` true of the pre-storage; `target`, its old pauser and `p` in `probes`; `findEntry entries target`; two decidable checks: `checkFaithfulOn solKey (registryQueries probes entries.length)` over the keys of `nonzeroWrites`, and `checkApartOn` of the two heartbeat expiry slots `mapSlot oldPauser 2`, `mapSlot p 2` | **No universal premise**: neither `RegistryWitness`, `EntryAt`, `ForeignApart` nor `lidoEntry` occurs. Derived from the raw execution through the dispatcher, the ABI wrapper, the entry-32 update and both heartbeat continuations |
| The entry-32 update subroutine, entered from its exact caller stack, establishes `RegistryOn` for the updated entries and returns to that stack | `Blanc.Lift.LidoCircuitBreakerDeployed.setPauser_nonzero_finite` (`Blanc/Lift/LidoCircuitBreakerDeployed/FiniteUpdate.lean:209`) | Frame / safety | CODE; well-formed memory; `RegistryOn` of the pre-storage; the same membership, `findEntry` and `checkFaithfulOn` premises | Supporting; the synthetic logical completion it uses internally is a proof device, not a premise on EVM storage |
| Modeled deployment: the recorded creation input, run as a CREATE message, succeeds, installs the certified runtime, and leaves a storage satisfying `RegistryOn [] probes` for every list of canonical probes | `Blanc.Lift.LidoCircuitBreakerDeployed.lido_create_finite_init` (`Blanc/Lift/LidoCircuitBreakerDeployed/FiniteInit.lean:59`), through `Blanc.Lift.LidoCircuitBreakerDeployed.registryOn_deployedStor` (`Blanc/Lift/LidoCircuitBreakerDeployed/FiniteInit.lean:27`) | Deploy / INIT (finite) | the `lido_create` message premises (value 0, code address none, 1,000,000 gas, covered fork, non-static, code-size limit at least 4,584); `checkApartOn solKey (registryQueries probes 0) [0, 1] = true` (the constructor's two slots are off the probes' query keys) | No `ForeignApart`; still a modeled deployment (Section 7) |
| Premise satisfiability: a constructed five-write raw pre-state with entries `[(1, 2)]` and probes `[0, 1, 2, 3]` satisfies every premise of the nonzero update at once (state check, coverage, `findEntry`, membership, nonzero, both separation checks), each closed by kernel evaluation | `Blanc.Lift.LidoCircuitBreakerDeployed.exampleApplicable` (`Blanc/Lift/LidoCircuitBreakerDeployed/FiniteExample.lean:93`); the checker evaluations `Blanc.Lift.LidoCircuitBreakerDeployed.exampleInitialCheck` (`Blanc/Lift/LidoCircuitBreakerDeployed/FiniteExample.lean:77`), `Blanc.Lift.LidoCircuitBreakerDeployed.exampleSeparationChecks` (`Blanc/Lift/LidoCircuitBreakerDeployed/FiniteExample.lean:85`) | Witness (premises) | none (closed) | Not a successful call and not a history; the reserved address 0 is probed explicitly |

**What the finite tier does not say.** Nothing about an address outside
`probes`: no assignment, index or count word is constrained there, and address
0 is included only when probed. Nothing about inserting or removing a target.
Nothing at history level: there is no finite history theorem, and the
constructor state is not shown to precede the example's pre-state. Admitting
another address means extending the probe list and re-checking the actual raw
cells with `checkRegistryOn` for the extended list.

**History tier (universal premises).** `lidoEntry lidoA` [`Blanc.Lift.LidoCircuitBreakerDeployed.lidoEntry` (`Blanc/Lift/LidoCircuitBreakerDeployed/Frame.lean:63`)] states, at
every entered frame, `LocalApart` (`ForeignApart (2^160)` for the three
fixed and written slots) and `EntryAt lidoA` (for every witness of the
frame-entry storage, the registry keys the calldata addresses touch are
faithful at bound 2^160).

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| After any configured history there is a registry witness of the future storage: assignment and index agree with membership, counts equal assignments, pauser 0 has count 0, and live counts sum to the length word | `Blanc.Lift.LidoCircuitBreakerDeployed.lido_history_l1_l3` (`Blanc/Lift/LidoCircuitBreakerDeployed/History.lean:56`) | History / safety | CODE; INIT `RegistryZeroRaw`; ENTRY plus **HASH-U** `FrameAdmitted ca (lidoEntry lidoA)` | selector-insensitive |
| `registerPauser(t, 0)` from a real pc-0 entry removes `t` with the correct swap-and-pop repair (`L2Post`) | `Blanc.Lift.LidoCircuitBreakerDeployed.l2_registerPauser_zero` (`Blanc/Lift/LidoCircuitBreakerDeployed/L2Frame.lean:249`) | Frame / safety | CODE; fresh entry; **HASH-U** `EntryAt lidoA`; INIT-shaped `RegistryWitness` of the pre-storage | |
| **The pre-storage witness is derived:** every settlement-committed non-static `registerPauser(t, 0)` frame (including one re-entered from inside `pause`'s CALL) has a witness of its entry storage and `L2Post` | `Blanc.Lift.LidoCircuitBreakerDeployed.lido_history_l2_committed` (`Blanc/Lift/LidoCircuitBreakerDeployed/L2History.lean:62`) | History / safety | CODE via `StateInv` INIT; `FrameAdmitted ca (lidoEntry lidoA)` (HASH-U); per-frame call shape only. Uses the generic `Blanc.ExecutionTrace.ConfiguredHistoryTrace.entryGood_settled` (`Blanc/ExecutionEntryAccounting.lean:488`), `Blanc.Lift.LidoCircuitBreakerDeployed.lido_spawnEntry` (`Blanc/Lift/LidoCircuitBreakerDeployed/Reentry.lean:445`) and `Blanc.Lift.reach_of_parentPrefix` (`Blanc/Lift/Cursor.lean:718`) | static committed frames and frames under a rolled-back ancestor are **not claimed** |

**Liveness.** None. There is **no Lido liveness claim of any level**, at
either tier.

**Deployment / INIT.** `Blanc.Lift.LidoCircuitBreakerDeployed.Creation.lido_deploy_covered` (`Blanc/Lift/LidoCircuitBreakerDeployed/Creation/Deploy.lean:190`), for every covered fork
`f`: a nonce-0 CREATE from the recorded deployer with 1,000,000 gas installs
the certified runtime and leaves storage exactly `deployedStor`
(`pauseDuration = 1814400`, `heartbeatInterval = 31536000`).
`Blanc.Lift.LidoCircuitBreakerDeployed.Creation.lido_deploy_init_covered` (`Blanc/Lift/LidoCircuitBreakerDeployed/Creation/Deploy.lean:203`) adds `RegistryZeroRaw` and
`lidoSpec.StateInv` **under `ForeignApart 0 0` and `ForeignApart 0 1`** (two
bounded hash premises: the constructor's slots 0 and 1 are off the registry's
raw slots). The finite tier above replaces those two premises by one decidable
check per probe list, for the finite observation `RegistryOn [] probes` in place
of `RegistryZeroRaw`. General forms `Blanc.Lift.LidoCircuitBreakerDeployed.Creation.lido_create` (`Blanc/Lift/LidoCircuitBreakerDeployed/Creation/Deploy.lean:75`),
`Blanc.Lift.LidoCircuitBreakerDeployed.Creation.lido_create_registryZeroRaw` (`Blanc/Lift/LidoCircuitBreakerDeployed/Creation/Deploy.lean:115`), `Blanc.Lift.LidoCircuitBreakerDeployed.Creation.lido_create_stateInv` (`Blanc/Lift/LidoCircuitBreakerDeployed/Creation/Deploy.lean:129`).
Satisfiability: `Blanc.Lift.LidoCircuitBreakerDeployed.registryZeroRaw_empty` (`Blanc/Lift/LidoCircuitBreakerDeployed/Init.lean:37`), `Blanc.Lift.LidoCircuitBreakerDeployed.lido_init_stateInv` (`Blanc/Lift/LidoCircuitBreakerDeployed/Init.lean:50`). The gas of the
modeled constructor matches the mainnet receipt exactly; that comparison was
made outside Lean and is not a Lean fact.

**Fork coverage.** History on covered forks; `lido_deploy_covered` quantifies
over covered forks. See Section 7: this deployment is post-Prague.

**Non-claims.** Authorization completeness; setter effects and events;
pause-call liveness; that a target is actually paused; static committed
frames; frames under rolled-back ancestors; any liveness; at the finite tier,
any address outside the probe list, target insertion or removal, and any
history-level statement.

### 5.5 Vyper V+: guarded-body reentrancy exclusion

The fixed implementation 0x847e, called directly or through the ETH/stETH
proxy.

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| In any execution (any outcome, `Exec 0 …`), while an owner frame is inside one of the mutating guarded bodies and has not released, no descendant enters any guarded body for that owner | generic `Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_exclusion` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exclusion.lean:128`); instances `Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_exclusion_impl` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exclusion.lean:142`), `Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_exclusion_stethPool` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exclusion.lean:161`) | Message (all outcomes) / temporal exclusion | CODE (implementation or proxy bytes, `hP`, `hI`); ENV well-formed root `hroot`; **HASH-T** `HashAvoidIn` (executed Keccak digests differ from lock slot 0) | |
| The same for a transaction's retained top-level execution, with `hroot` **derived** (`prepareMessage` builds the root from the debited world) | `Blanc.ExecutionTrace.TransactionTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:248`); message carriers `Blanc.ExecutionTrace.ProcessMessageTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:70`), `Blanc.ExecutionTrace.ProcessCreateMessageTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:116`), `Blanc.ExecutionTrace.MessageCallTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:180`) | Transaction / temporal exclusion | `hfork`, `hP`, `hI` on the opening state; `tx.auths = []` (EIP-7702 excluded); `HashAvoidIn` of the retained execution | |
| The same for every raw frame root of a configured history; pc 0 and the covered fork are derived | `Blanc.ExecutionTrace.ConfiguredHistoryTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:281`) [roots by `Blanc.ExecutionTrace.MessageCallTrace.rootEntry` (`Blanc/ExecutionTraceEntry.lean:58`)] | History / temporal exclusion | per retained execution `R`: `hP`, `hI`, `hroot`, `HashAvoidIn` (not derivable from the trace) | statement form `VplusExcludes` [`Blanc.Lift.VyperNonreentrantDeployed.Fixed.VplusExcludes` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:44`); `Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_excludes` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:50`)] |
| **Nonvacuity (proxy-free):** an actual Jaune execution of the deployed 0x847e runtime in which a mutating guarded body (`remove_liquidity`, body start 0x1bae) is active and spawns a STATICCALL (pc 0x337a) to a coin, whose read-only reentry into the guarded view `get_virtual_price()` **reverts at the lock check** and never reaches a guarded body. It carries the full antecedent of `vplus_exclusion_impl` and its conclusion | `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness.vplus_witness_covered` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness/Top.lean:251`) (quantified over `g` with `CoveredFork g`, Prague included); every derivation of the entered machine, under any covered fork: `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness.vplus_run_at` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness/Top.lean:82`) | Message / closed witness | none (closed) | Kernel-checked; every walk boundary matches an EELS Prague trace (the printer is untrusted). No KECCAK executes, so `HashAvoidIn` holds by "no hash executed" |
| **Nonvacuity (proxy instance, mutating reentry):** an execution entered through the 45-byte forwarder 0x21e2… (DELEGATECALL to 0x847e). `remove_liquidity` holds the lock and CALLs a synthetic receiver with 100 wei; the receiver calls back through the forwarder with `add_liquidity`'s selector (mutating, guarded); the comparator frame reverts at the lock check (pc 0x53 → 0x477e, no guarded body start); the receiver stops; the outer call **succeeds** and the pool balance goes from 1000 to 900 wei. This is a witness of `vplus_exclusion_stethPool` (the covered form carries that theorem's premises and antecedent, and the reentry conclusion `¬ lockL.Enters`) | `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.vplus_witness2_covered` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness2/Top.lean:227`) (every covered fork); every derivation: `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.vplus_run2_at` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness2/Top.lean:104`) | Message / closed witness | none (closed) | `HashAvoidIn` by digests: the one KECCAK256 leaves a digest different from slot 0 (control `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.hashControl_bites` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness2/Run.lean:308`); engine control `Blanc.Lift.NodeWalk.hashPol_bites` (`Blanc/Lift/NodeWalk.lean:1075`)) |

**Fork coverage.** The exclusion assumes `CoveredFork`; both witnesses are
stated for every fork in Prague, Osaka, BPO1 and BPO2 (the Prague kernel facts
are transported by `Blanc/ForkUniform.lean`, `Blanc/Lift/NodeWalkFork.lean` and
`Blanc/Lift/WitnessFork.lean`; the runs execute no CLZ, read no blob price, and
enter no MODEXP or P256VERIFY).

**Non-claims.** Unguarded functions; reentry after release; mutation while
only a view is running; pricing, LP economics, liveness; EIP-7702-delegated
roots (excluded from the transaction and message carriers); a validated
transaction reaching the witness state; historical prestates (all witness
prestates, and the reader and receiver, are synthetic).

### 5.6 Vyper V−: cross-function reentrancy corrupts the LP ledger

The vulnerable implementation 0x6326, called through its proxy.

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| Message level: a successful message execution in which `remove_liquidity` holds lock slot 2, its ETH callback reenters `add_liquidity` (lock slot 0) through the proxy, and the final ledger has `totalSupply = 1800 < 1906 = balanceOf[attacker]`. The two guards are on different slots (bytes 6900-6911 versus 88-99) | `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top.vminus_witness` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Top.lean:155`); all covered forks `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top.vminus_witness_covered` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/ForkTop.lean:159`) | Message / closed witness | none (closed) | synthetic prestate (Section 7); stated for Prague, other covered forks by transport |
| **Transaction level, all covered forks:** conditional on block room, Jaune's `processTransaction` accepts a fixed signed type-2 transaction (zero fee and value, 16,043,200 gas, below 2^24, an access list of 19 addresses), and the returned world has `totalSupply = 1800 < 1906` in the pool | `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.vminus_txC_process` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/TxC/Envelope.lean:136`); closed message part `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.vminus_txC_message` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/TxC/Closed.lean:49`) (gas 15,822,837 left, refund 42,600, `accountsToDelete` empty) | Transaction / conditional witness | block room `hroom` | every other admission check, including signature recovery (`Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.txC_recoveredSender` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/TxCRecover.lean:99`)), is kernel-evaluated on the concrete transaction and block |

**Fork coverage.** `vminus_witness_covered`, `vminus_txC_message` and
`vminus_txC_process` quantify `g` with `CoveredFork g`. A Prague-only message
form, `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.vminus_tx_message` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Tx/Closed.lean:26`), carries 30,021,064 gas, which is above
the EIP-7825 cap from Osaka on and so is not a valid transaction there; cite
the `TxC` forms.

**Non-claims.** A reachable or historical prestate; a real historical
attack; a signature-generic transaction (the signature, transaction hash,
index 0 and coinbase are fixed); the attacker model is synthetic (Section 7).

### 5.7 EIP-7002 withdrawal requests: actual-fee FIFO from submissions to block requests

**Safety, refinement and history**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| For every block of a configured history, the type-1 request bytes are exactly the FIFO-first queued entries (at most 16), each the `(caller, pubkey, amount)` of exactly one committed submission that paid the fee the bytecode computed; nothing is dropped, duplicated, reordered or emitted early; the unemitted entries are the queue at the future state | `Blanc.Lift.WithdrawalRequest.block_word_fifo` (`Blanc/Lift/WithdrawalRequest/WordFifo.lean:345`); forms `Blanc.Lift.WithdrawalRequest.block_word_fifo_or_overflow` (`Blanc/Lift/WithdrawalRequest/WordFifo.lean:402`), `Blanc.Lift.WithdrawalRequest.block_word_fifo_of_blockCount` (`Blanc/Lift/WithdrawalRequest/WordFifo.lean:424`) | History / safety | CODE `SystemCodeInstalled checkpoint`; INIT `RepresentsStorage … initial`; ENV (trace-local): `NoSenderAt Jaune.systemAddress`, `NoAuthorityAt Jaune.systemAddress`, no code-less root frame targeting `Jaune.systemAddress`, empty code at `Jaune.systemAddress` at the checkpoint; **scope: at most 2^254 committed submission-payment occurrences since the checkpoint** (user-approved). **No hash premise, no per-frame ENTRY premise** | beyond the cap nothing is proved, neither safety nor failure; the block-count form is sufficient (≤ 2^190 blocks), not stronger |
| Delivery after acceptance: if an entry sits at index q of the queue at block B's request boundary, then in every configured extension of the history through B that ends at the block D exactly ⌊q/16⌋ blocks after B (B counted as 0), D's withdrawal system call returns `systemOutput` of its queue model with the entry as record q mod 16, and the records up to it are exactly B's queue entries 16·⌊q/16⌋ … q, so nothing submitted later overtakes it (the FIFO row places that output in D's requests as the type-1 entry) | `Blanc.Lift.WithdrawalRequest.block_word_delivery` (`Blanc/Lift/WithdrawalRequest/WordDelivery.lean:309`) | History / delivery bound | as the first row, stated for the history through the delivering block; the queue at B is the model B's request-boundary storage represents, which is unique | no claim that the chain produces those later blocks; distance is counted in configured blocks |
| The SYSTEM_ADDRESS exclusion is load-bearing: a configured history meeting every other hypothesis, with code at `Jaune.systemAddress` that drains the queue from inside a user transaction, violates the FIFO statement | `Blanc.Lift.WithdrawalRequest.DrainControl.systemEmpty_loadBearing_witness` (`Blanc/Composition/WithdrawalRequestDrainControl.lean:547`) | Negative control, closed | none | the witness lives only in the model: no key or CREATE reaches `Jaune.systemAddress` |
| Storage at the future state is the EIP model replayed over exactly the committed submissions and system calls, in trace order, at the actual word fee | `Blanc.Lift.WithdrawalRequest.history_word_storage_replay` (`Blanc/Lift/WithdrawalRequest/WordReplay.lean:321`), `Blanc.Lift.WithdrawalRequest.history_word_model` (`Blanc/Lift/WithdrawalRequest/WordFifo.lean:227`) | History / exact replay | as the first row | |
| Every successful fresh frame at this code is exactly one of a system dequeue, a word-fee submission or a fee read, with exact storage, logs and return bytes. No other fresh entry succeeds: a user call whose input is neither empty nor 56 bytes, a fee read carrying value, a static or underpaying submission, and any user call at the inhibitor have no successful execution | `Blanc.Lift.WithdrawalRequest.exec_frame_effect` (`Blanc/Lift/WithdrawalRequest/FrameEffects.lean:33`) | Frame / refinement | CODE; covered fork; fresh entry (empty stack, word-aligned well-formed memory, input shorter than 2^256 bytes) | model transcribed from the EIP text, not from the bytes; **success is classified, failure is not**: which failure occurs (REVERT, out-of-gas, a static-context fault), its gas and its return data are not stated |
| Fee: the executed word fee is at most fake_exponential(1, excess, 17), with equality exactly on `NatFeeDomain`; every committed submission paid its executed word fee | `Blanc.Lift.WithdrawalRequest.word_fee_le_nat` (`Blanc/Lift/WithdrawalRequest/ExactFeeDomain.lean:51`), `Blanc.Lift.WithdrawalRequest.word_fee_eq_iff_natFeeDomain` (`Blanc/Lift/WithdrawalRequest/ExactFeeDomain.lean:27`), `Blanc.Lift.WithdrawalRequest.history_word_fee_budget` (`Blanc/Lift/WithdrawalRequest/WordBudget.lean:78`) | Frame and history | CODE | see §7 item 16 |
| **The EIP's unbounded-integer fee guarantee is false for these bytes**: a three-block configured history under the original hypotheses has a committed submission that paid its executed word fee but less than fake_exponential(1, 2893, 17) | `Blanc.Lift.WithdrawalRequest.FeeCounterexample.not_natFeeGuarantee` (`Blanc/Composition/WithdrawalRequestFeeRefutation.lean:1200`), `Blanc.Lift.WithdrawalRequest.FeeCounterexample.nat_fee_guarantee_refuted` (`Blanc/Composition/WithdrawalRequestFeeRefutation.lean:1182`) | History / refutation, closed | none | §7 item 16 |
| System call: after any configured history the checked system call succeeds with no error and exact gas ≤ 210,000; its storage update is the raw 256-bit word computation, which sets the count to 0 and leaves the reset excess at least two below the word maximum | `Blanc.Lift.WithdrawalRequest.history_checked_system_totality` (`Blanc/Lift/WithdrawalRequest/SystemHistory.lean:14`), `Blanc.Lift.WithdrawalRequest.systemFrameGas_closed` (`Blanc/Lift/WithdrawalRequest/SystemGas.lean:96`), `Blanc.Lift.WithdrawalRequest.block_requests_reset_occurrence` (`Blanc/Lift/WithdrawalRequest/ResetOccurrence.lean:120`) | History / totality, exact gas | CODE; covered fork | no storage model: from CODE alone the excess update is word arithmetic, and excess + count can wrap modulo 2^256 |
| Within the first row's scope, the system call's word update is the EIP's natural-number bookkeeping: `excess' = max(0, e + count − 2)` where e is the effective excess (0 at the inhibitor), `count' = 0`, the first min(16, queue) entries leave and head/tail advance or reset; every bookkeeping value stays within 2^254 and no live queue slot reaches slots 0–3 | `Blanc.Lift.WithdrawalRequest.block_word_fifo` (`Blanc/Lift/WithdrawalRequest/WordFifo.lean:345`), `Blanc.Lift.WithdrawalRequest.systemNewExcess_represented` (`Blanc/Lift/WithdrawalRequest/SystemStorage.lean:119`), `Blanc.Lift.WithdrawalRequest.WordHistory.conservation` (`Blanc/Lift/WithdrawalRequest/WordHistory.lean:36`), `Blanc.Lift.WithdrawalRequest.WordMargin.slots_safe` (`Blanc/Lift/WithdrawalRequest/WordHistory.lean:139`) | History / refinement | as the first row: CODE, INIT, ENV and the 2^254 scope | the word-to-natural step assumes a storage representation and e + count < 2^256; the history derives both from INIT and the cap, so the natural recurrence is not a CODE-only fact; `Blanc.Lift.WithdrawalRequest.wordSystem_excess_wraps` (`Blanc/Lift/WithdrawalRequest/WordReplay.lean:42`) exhibits represented storage at excess 2^256 − 2 and count 10 whose word update stores 6 and does not represent that model's natural step, whose excess would be 2^256 + 6 |
| The contract's balance never decreases; committed submissions add exactly their value | `Blanc.Lift.WithdrawalRequest.history_balance_nondecreasing` (`Blanc/Lift/WithdrawalRequest/BalanceHistory.lean:158`), `Blanc.Lift.WithdrawalRequest.history_submission_payments` (`Blanc/Lift/WithdrawalRequest/BalanceHistory.lean:215`) | History | CODE | uses `SpawnFreeReach`, not the offset-blind `SpawnFree`; the balance is not a count of fees, since value that reaches the address without running its code also raises it |

**Liveness.** After any configured history that leaves the contract active (excess below the inhibitor), a fresh
non-static frame carrying a 56-byte submission from a non-system caller with `value ≥ fake_exponential(1, excess, 17)`
on a covered fork has a successful execution: started with 1258 + 87·k + reads + stores gas plus a residual G
greater than the 2,300-gas stipend, it consumes exactly that charge and ends with G left, where `k` is the fee loop's
iteration count. The charge is the gas consumed, not a proved minimum. At the inhibitor no user
call succeeds. The fee read likewise has a successful execution at an exact charge
[`Blanc.Lift.WithdrawalRequest.history_submission_nat_live` (`Blanc/Lift/WithdrawalRequest/NatLiveness.lean:59`), `Blanc.Lift.WithdrawalRequest.history_fee_getter_word_live` (`Blanc/Lift/WithdrawalRequest/NatLiveness.lean:96`)]. The only installation premise is checkpoint CODE, with no storage model; the frame shape, caller, input,
payment and fork above are hypotheses. At a large enough excess fake_exponential exceeds every 256-bit value, so the
payment hypothesis cannot hold there.
**No transaction-level liveness** (E13 not pursued): sender funding, intrinsic gas, block room and call forwarding are
not covered.

**Deployment / INIT.** `Blanc.Lift.WithdrawalRequest.Creation.deploy_initial` (`Blanc/Lift/WithdrawalRequest/Creation/Deploy.lean:88`): on every covered fork the recorded
keyless creation input installs the certified runtime and storage representing the inhibitor/empty-queue
initial state. No hash premise. Modeled, not historical inclusion; not chained into a history.

**Non-claims.** Consensus-layer processing, including validator authorization: the emitted source address is the
immediate caller, and whether a request may act on the named validator is decided there; economic soundness of the
parameters; EIP-7251; that the chain produces the later blocks the delivery bound speaks of; the failure outcome of a rejected call (REVERT,
out-of-gas or a static-context fault) and its gas; state growth (dequeued queue slots are not cleared, and the storage
representation ignores them); historical inclusion of the deployment; anything beyond the 2^254 occurrence scope.
Rolled-back frames are not ignored: the replay, FIFO and balance theorems range over settled frames, and a frame
rolled back by its own or an ancestor's failure is not among them.

### 5.8 Uniswap V2 Pair: exact committed replay, share-value monotonicity and gas-exact liveness

The lifted runtime is the one Uniswap V2 Pair runtime (solc 0.5.16, `Uniswap/v2-core`
v1.0.1, 11,293 bytes) that every V2 pair runs; the USDC/WETH pair of Section 2 is its
exhibit instance. The theorems quantify over the pair address, the two token
addresses and the factory, so they hold of every pair that runs these bytes. The
pair can observe only what `balanceOf` and the factory's `feeTo` answer: those
answers are **inputs** of the statements, never assumptions folded into a
definition. Results about the bytes and about replay, the LP ledger and the oracle
need no token or factory premise. The share-value statements take a named premise
about the callee answers of the history's own steps. The factory's bytecode is not
lifted. The functional model is transcribed from the v1.0.1 sources and carries a
line-by-line correspondence table with an independent source-versus-model review
([`docs/registers/UNISWAP_V2_MODEL_REVIEW.md`](registers/UNISWAP_V2_MODEL_REVIEW.md),
which reviewed an earlier snapshot of the model and states what has changed since).

**Safety, refinement and history**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| After any configured history: the certified runtime is still installed, and there is a list of steps, one per **outermost** settlement-committed non-static pair frame in trace order, such that the committed pair frames of the steps' subtrees are exactly the settlement-committed non-static pair frames of the trace (rolled-back frames absent, static frames observe nothing); every step is authenticated against its own run (its decoded entry and the token and factory answers its run actually observed, nested turns included); and replaying the steps' source invocations from the checkpoint model state with the source model's driver gives a model state that the future pair storage represents | `Blanc.Lift.UniswapV2Pair.pair_history_committed` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:344`); steps `Blanc.Lift.UniswapV2Pair.PairStep` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:148`) with `Blanc.Lift.UniswapV2Pair.PairStep.Authentic` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:162`); the observed list `Blanc.Lift.UniswapV2Pair.committedPairFrames` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:308`) over `Blanc.Lift.UniswapV2Pair.pairSubtreeFrames` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:173`) | History / safety, exact extraction | CODE (the certified runtime at the pair at the checkpoint); INIT `WriterRep K₀ (pair storage) st₀`; **HASH-T** `WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace)` (finite, trace-local, includes rolled-back frames). **No per-frame ENTRY premise, no universal hash premise, no token or factory premise** | The headline. The list is pinned by an equality, not a free witness: the observation equality places every step's frame among the trace's settled frames, and a committed non-static pair frame always observes itself, so a step cannot be a phantom. The replay is **nested, not flat**: a pair frame re-entered from inside a token call, the flash-swap callback or a factory call is consumed inside its parent step's transcript (Section 7 item 19). The calldata bound is derived [`Blanc.Lift.UniswapV2Pair.pair_trace_admitted` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:314`)]. The source driver `Blanc.Lift.UniswapV2Pair.runSourceInvocations` (`Blanc/Lift/UniswapV2Pair/SourceReplay.lean:25`) accepts only successful invocations |
| The same statement from the deployment checkpoint: with `st₀ = initializedState factory domain token0 token1` and no initially tracked row, every tracked row at the end is a row the trace touched | `Blanc.Lift.UniswapV2Pair.pair_history_initialized` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:384`) | History / safety | CODE; INIT `InitializedCheckpoint` (the checkpoint storage is the deploy-then-`initialize` storage); HASH-T with no initial row | The INIT premise is the conclusion of the deployment theorem below |
| **LP-token ledger (U7):** the replayed model state satisfies `Ledger`: the LP balances of **all** addresses sum to `totalSupply`, `MINIMUM_LIQUIDITY` at address 0 and every protocol-fee mint included | `Blanc.Lift.UniswapV2Pair.pair_history_ledger` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:414`); the invariant `Blanc.Lift.UniswapV2Pair.State.Ledger` (`Blanc/Lift/UniswapV2Pair/PropertiesLedger.lean:35`); model level `Blanc.Lift.UniswapV2Pair.runTyped_ledgerOn` (`Blanc/Lift/UniswapV2Pair/PropertiesLedger.lean:550`) | History / safety | as `pair_history_initialized`: CODE, INIT `InitializedCheckpoint`, HASH-T | Callbacks may re-enter the unlocked ERC-20 entry points; the replay admits that. The ledger at the checkpoint is proved, not assumed [`Blanc.Lift.UniswapV2Pair.State.initialized_ledgerOn` (`Blanc/Lift/UniswapV2Pair/PropertiesLedger.lean:70`)] |
| **Oracle (U5):** the two price accumulators after the history are the checkpoint's plus the sum of the increments of every committed update receipt of the replay (nested committed updates included), modulo 2^256 | `Blanc.Lift.UniswapV2Pair.pair_history_oracle` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:436`); the per-update law `Blanc.Lift.UniswapV2Pair.OracleUpdate.Lawful` (`Blanc/Lift/UniswapV2Pair/PropertiesOracleLaw.lean:8`): `Δt = (ts mod 2^32 − last) mod 2^32` and an increment of `⌊r1·2^112/r0⌋·Δt` (symmetrically for price 1) when `Δt` and both reserves are nonzero, established for every update `Blanc.Lift.UniswapV2Pair.State.update_oracle_lawful` (`Blanc/Lift/UniswapV2Pair/PropertiesOracleLaw.lean:20`) and carried through the typed driver by `runTyped_oracle_law` (`Blanc/Lift/UniswapV2Pair/PropertiesOracleLaw.lean`) | History (sum) and model (law) / safety | as `pair_history_committed` | Both wraparounds, of the `uint32` timestamp and of the accumulator, are part of the statements. **The history theorem states the modular sum of the recorded increments; that each recorded increment is the floor formula over the wrapped `Δt` is the model-level law, not restated at history level** (Section 7 item 22) |
| **Share value never decreases, protocol fee off (U3):** for every committed state change of the replay with positive incoming supply `T`, `r0·r1·T'² ≤ r0'·r1'·T²`, equivalently `√(r0·r1)/T` does not decrease, across mint (minimum of two floors), burn (floors), swap (fee-adjusted check), sync and skim | `Blanc.Lift.UniswapV2Pair.pair_history_feeOff_product` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:467`); consumed `Blanc.Lift.UniswapV2Pair.SourceReplay` (`Blanc/Lift/UniswapV2Pair/SourceReplay.lean:35`); frame-level `Blanc.Lift.UniswapV2Pair.runTyped_product` (`Blanc/Lift/UniswapV2Pair/Properties.lean:2680`) | History / safety | as `pair_history_committed`, and for the history's own steps `sourceReplayAnswers`: at each step `EntryFeeOff` (the factory's `feeTo` answer of a mint or burn is zero) and `EntryNoShrink` (the token-answer premise **NoShrink**, below) | **Token and factory premises, stated over the history's own steps only**, not over all tokens. Nonvacuous: any history whose tokens answer at least the stored reserves where the premise says so, and whose factory answers `feeTo = 0`, satisfies it. Mint and swap need no token premise: the bytecode's own checks (the checked balance subtractions, the fee-adjusted check) give the inequality |
| **Share value with the protocol fee on:** every committed state change with positive incoming supply keeps `r0·r1·T'² ≤ r0'·r1'·(T + F)²`, where `F = entryFeeAmount` is the exact fee mint of that step, `⌊T·(√k − √kLast)/(5·√k + √kLast)⌋` at the step's actual `feeTo` answer (floored roots, `feeTo ≠ 0`, `kLast ≠ 0`, `√kLast < √k`), else 0; dilution is bounded by the fee mint alone | `Blanc.Lift.UniswapV2Pair.pair_history_feeOn_product` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:496`) | History / safety | as `pair_history_committed`, and `sourceReplayNoShrink` over the history's own steps | As above without the fee-off condition |
| **NoShrink, exactly.** For `sync`: both answers of `balanceOf(pair)` are at least the stored reserves. For `burn`: both first answers are at least the stored reserves, and each first answer is at most its final answer plus that token's payout (a transfer debits at most its payout). For every other entry: none | `Blanc.Lift.UniswapV2Pair.EntryNoShrink` (`Blanc/Lift/UniswapV2Pair/Properties.lean:2643`) with `Blanc.Lift.UniswapV2Pair.SyncEntryNoShrink` (`Blanc/Lift/UniswapV2Pair/Properties.lean:1994`) and `Blanc.Lift.UniswapV2Pair.BurnEntryNoShrink` (`Blanc/Lift/UniswapV2Pair/Properties.lean:1490`); fee-off `Blanc.Lift.UniswapV2Pair.EntryFeeOff` (`Blanc/Lift/UniswapV2Pair/Properties.lean:2657`); over a replay `Blanc.Lift.UniswapV2Pair.sourceReplayAnswers` (`Blanc/Lift/UniswapV2Pair/SourceReplay.lean:105`), `Blanc.Lift.UniswapV2Pair.sourceReplayNoShrink` (`Blanc/Lift/UniswapV2Pair/SourceReplay.lean:150`) | Premise definitions (ENV: callee behaviour) | — | The burn form is weaker than "every answer is at least the stored reserve", which would exclude every ordinary burn (an honest token answers below the reserve after paying out). Tokens with transfer fees or rebasing fail NoShrink (Section 7 item 17) |
| Frame refinement of every selector: a successful pc-0 run of the certified runtime consumes the typed source entry exactly over the observations of its own derivation (the token and factory answers; nested turns derived from the run's actual children), with exact storage, logs and return bytes. Writers: sync, mint, swap (in all six successful shapes: each optimistic transfer present iff its amount is nonzero, the callback present iff `data` is nonempty), skim, burn, transfer, approve, transferFrom, initialize (the factory is the caller) and permit; **views**: every successful static frame is one of the views, with value zero | `Blanc.Lift.UniswapV2Pair.sync_bytecode_exact_consumes` (`Blanc/Lift/UniswapV2Pair/SyncGasCanonical.lean:749`), `Blanc.Lift.UniswapV2Pair.mint_bytecode_exact_consumes` (`Blanc/Lift/UniswapV2Pair/MintCanonical.lean:495`), `Blanc.Lift.UniswapV2Pair.swap_bytecode_exact_consumes` (`Blanc/Lift/UniswapV2Pair/SwapCanonical.lean:270`), `Blanc.Lift.UniswapV2Pair.skim_bytecode_exact_consumes` (`Blanc/Lift/UniswapV2Pair/SkimCanonical.lean:378`), `Blanc.Lift.UniswapV2Pair.burnRaw_source_authentic` (`Blanc/Lift/UniswapV2Pair/BurnFeeTransfers.lean:1076`), `Blanc.Lift.UniswapV2Pair.transfer_bytecode_exact_consumes` (`Blanc/Lift/UniswapV2Pair/TransferSource.lean:467`), `Blanc.Lift.UniswapV2Pair.approve_bytecode_exact_consumes` (`Blanc/Lift/UniswapV2Pair/ApproveSource.lean:254`), `Blanc.Lift.UniswapV2Pair.transferFrom_bytecode_exact_consumes` (`Blanc/Lift/UniswapV2Pair/TransferFromSource.lean:590`), `Blanc.Lift.UniswapV2Pair.initialize_bytecode_exact_consumes` (`Blanc/Lift/UniswapV2Pair/InitializeSource.lean:247`), `Blanc.Lift.UniswapV2Pair.permit_bytecode_refines_source` (`Blanc/Lift/UniswapV2Pair/PermitSource.lean:350`), `Blanc.Lift.UniswapV2Pair.staticView_bytecode_inv` (`Blanc/Lift/UniswapV2Pair/StaticViewClassify.lean:1256`) | Frame / refinement | CODE; covered fork; fresh pc-0 entry; INIT-shaped `WriterRep` of the entry storage; HASH-T over the run's own key universe (transfer, approve, transferFrom and permit: freshness of their own touched rows) | The frame theorems are the ground the history rows are built on. `permit` uses the **result** of the modeled ECRECOVER precompile as an input: value zero, at least 228 calldata bytes, non-static, before the deadline, and a successful recovery call whose copied word is the nonzero owner; unforgeability of signatures is not claimed |
| Model laws of the typed source model (the functional model the replay folds over): the first mint prices `⌊√(a0·a1)⌋ − 1000`, locks 1000 at address 0 and credits the recipient the rest, with the Babylonian loop equal to `Nat.sqrt` over the full domain; a later mint issues `min(⌊a0·T/r0⌋, ⌊a1·T/r1⌋)` (with `T` the supply after the fee mint); a burn pays and returns `⌊L·b_i/T⌋` of each token by exactly the two transfer requests; a swap succeeds only if (and, on the canonical transcript, whenever) some output is positive, the outputs are below the reserves, `to` is neither token, the post-callback balances fit `uint112`, some input is positive and the fee-adjusted check holds, and then stores exactly those balances as reserves; the callback request is present iff `data` is nonempty, with exact calldata | `Blanc.Lift.UniswapV2Pair.runTyped_mint_initial` (`Blanc/Lift/UniswapV2Pair/Properties.lean:3196`), `Blanc.Lift.UniswapV2Pair.runTyped_mint_initial_floor` (`Blanc/Lift/UniswapV2Pair/Properties.lean:3209`), `Blanc.Lift.UniswapV2Pair.mintAmount_initial_spec` (`Blanc/Lift/UniswapV2Pair/Properties.lean:2762`), `Blanc.BabylonianSqrt.sourceResult_eq_sqrt` (`Blanc/Lift/BabylonianSqrt.lean:106`), `Blanc.Lift.UniswapV2Pair.runTyped_mint_later` (`Blanc/Lift/UniswapV2Pair/PropertiesMintBurn.lean:310`), `Blanc.Lift.UniswapV2Pair.runTyped_burn_payout` (`Blanc/Lift/UniswapV2Pair/PropertiesMintBurn.lean:924`), `Blanc.Lift.UniswapV2Pair.runTyped_swap_success_reserves` (`Blanc/Lift/UniswapV2Pair/PropertiesSwap.lean:561`), `Blanc.Lift.UniswapV2Pair.runTyped_swap_canonical_success` (`Blanc/Lift/UniswapV2Pair/PropertiesSwap.lean:1042`), `Blanc.Lift.UniswapV2Pair.runTyped_swap_callback_request` (`Blanc/Lift/UniswapV2Pair/PropertiesSwap.lean:1664`) | Model / safety | the model only (the swap and burn statements are conditioned on the successful run's own answers) | Bridged to the bytes by the frame refinement and history rows above. The bytecode's own Babylonian loop is walked exactly [`Blanc.Lift.UniswapV2Pair.sqrt_of_run` (`Blanc/Lift/UniswapV2Pair/SqrtWalk.lean:589`)]. These are model facts: that real tokens give the answers a premise names is not proved |

**Statement controls.** Each is a single kernel fact or a mutation that must make
a statement fail; they say the statements above are not vacuous or insensitive.

| What it shows | Control | Altitude |
|---|---|---|
| NoShrink is needed: on a reachable sync, a token answer below the stored reserve is accepted by the model and the share-value inequality then fails | `Blanc.Lift.UniswapV2Pair.ModelControls.noShrink_required` (`Blanc/Lift/UniswapV2Pair/ModelControls.lean:115`) | typed model, kernel evaluation of the production driver |
| The model is sensitive to its arithmetic: a mint that rounds up breaks the fee-off share-value inequality on a state it reaches; a fee constant other than 997 and a burn that rounds toward the user each give a different accepted run | `Blanc.Lift.UniswapV2Pair.ModelControls.mintRoundUp_breaks_feeOff_product` (`Blanc/Lift/UniswapV2Pair/ModelControls.lean:216`), `Blanc.Lift.UniswapV2Pair.ModelControls.feeMutant_disagrees` (`Blanc/Lift/UniswapV2Pair/ModelControls.lean:269`), `Blanc.Lift.UniswapV2Pair.ModelControls.burnRoundUp_disagrees` (`Blanc/Lift/UniswapV2Pair/ModelControls.lean:291`) | typed model; mutated drivers compose the unchanged transitions with one changed arithmetic function |
| The burn-rounding mutant disagrees with production on a state reached from the deployment image; **the frame-level form `Blanc.Lift.UniswapV2Pair.RefinementControls.burn_refinement_control` (`Blanc/Lift/UniswapV2Pair/RefinementControls.lean:124`) is conditional on two named hypotheses** (a burn frame consumer and one successful raw burn run at that state) that this tree states but does not discharge | `Blanc.Lift.UniswapV2Pair.RefinementControls.burn_witness_disagrees` (`Blanc/Lift/UniswapV2Pair/RefinementControls.lean:59`) | typed model (closed); frame form EVM-conditional |
| The oracle law needs the `uint32` wrap: a reached update at a block timestamp past `2^32` satisfies the exact law and refutes the law with the wrap removed | `Blanc.Lift.UniswapV2Pair.OracleControls.oracle_law_requires_timestamp_wrap` (`Blanc/Lift/UniswapV2Pair/OracleControls.lean:50`); the bytecode's own wrap `Blanc.Lift.UniswapV2Pair.update_timestamp_wrap_control` (`Blanc/Lift/UniswapV2Pair/UpdateArithmetic.lean:166`) | typed model; the second is a raw walk |
| The `uint112` guard is load-bearing: a balance of `2^112` passes the fee-adjusted check and the typed swap still fails; every successful raw swap run observes balances below `2^112` | `Blanc.Lift.UniswapV2Pair.swap_uint112_control` (`Blanc/Lift/UniswapV2Pair/PropertiesSwap.lean:1151`), `Blanc.Lift.UniswapV2Pair.swap_bytecode_uint112_control` (`Blanc/Lift/UniswapV2Pair/SwapControls.lean:28`); the update walks `Blanc.Lift.UniswapV2Pair.update_uint112_overflow_control` (`Blanc/Lift/UniswapV2Pair/UpdateWalk.lean:108`), `Blanc.Lift.UniswapV2Pair.update_overflow_uint112_kernel_control` (`Blanc/Lift/UniswapV2Pair/UpdateOverflowWalk.lean:390`) | typed model, and universal over successful raw runs (no concrete reverting run is exhibited) |
| HASH-T is load-bearing for the ledger: a duplicated key breaks the footprint sum, and a successful raw `approve` whose allowance slot aliases a tracked balance slot (a hypothesis; no Keccak collision is asserted) ends outside raw ledger conservation | `Blanc.Lift.UniswapV2Pair.footprintSum_dup_breaks_ledger` (`Blanc/Lift/UniswapV2Pair/PropertiesLedger.lean:76`), `Blanc.Lift.UniswapV2Pair.LedgerKeyControl.approve_storage_alias_breaks_ledger` (`Blanc/Lift/UniswapV2Pair/LedgerKeyControl.lean:38`) | model; EVM-conditional on the alias |
| The callee premises are needed: if a token or the callback recipient holds code that reverts, no raw `sync`, `skim`, `mint` or `swap` run succeeds, whatever the gas; premise-free `sync` liveness is refuted on the family of worlds that deployment and `initialize` produce | `Blanc.Lift.UniswapV2Pair.sync_no_success_of_reverting_token0` (`Blanc/Lift/UniswapV2Pair/CalleeControls.lean:51`), `Blanc.Lift.UniswapV2Pair.skim_no_success_of_reverting_token0` (`Blanc/Lift/UniswapV2Pair/CalleeControls.lean:103`), `Blanc.Lift.UniswapV2Pair.mint_no_success_of_reverting_token0` (`Blanc/Lift/UniswapV2Pair/CalleeControls.lean:123`), `Blanc.Lift.UniswapV2Pair.swap_no_success_of_reverting_token0` (`Blanc/Lift/UniswapV2Pair/CalleeControlsSwap.lean:122`), `Blanc.Lift.UniswapV2Pair.swap_no_success_of_reverting_callback` (`Blanc/Lift/UniswapV2Pair/CalleeControlsSwap.lean:207`), `Blanc.Lift.UniswapV2Pair.sync_liveness_refuted` (`Blanc/Lift/UniswapV2Pair/CalleeControlsReach.lean:154`) | EVM, universal over raw runs for one concrete callee code |
| The deployment address is pinned: a salt or an init-code digest one bit off gives a different address | `Blanc.Lift.UniswapV2Pair.Creation.pairAddress_wrong_salt` (`Blanc/Lift/UniswapV2Pair/Creation/Facts.lean:108`), `Blanc.Lift.UniswapV2Pair.Creation.pairAddress_wrong_initHash` (`Blanc/Lift/UniswapV2Pair/Creation/Facts.lean:113`) | kernel evaluation |

**Liveness.** After any configured history, a call the model accepts at the
replayed state executes from pc 0 at a **closed** gas expression and ends at
exactly the residual gas `G`. The expression is a sum of fixed per-instruction
charges, `sloadCost`, `sstoreCost` and `temporalAccountAccessCost` of the actual
slots and accounts, and the gas forwarded to each callee; the callees' own
consumption enters only through their `returnedGas` equations, which are part of
the callee premise. It is not an existential cost. "Fresh frame" means the
history's future state as the frame's pre-state, the pair as target, the
certified code, a covered fork, empty output, calldata below 2^256, value 0 and
the selector. After the run, its post storage represents the model's next state
under HASH-T freshness of the call's own rows against the history's rows
(`PairStepOutcome`).

| Level | Claim | Theorem | Cost / gas formula | Premises beyond a fresh frame |
|---|---|---|---|---|
| Reachable state | `transfer`, `approve`, `transferFrom` | `Blanc.Lift.UniswapV2Pair.pair_history_writer_live` (`Blanc/Lift/UniswapV2Pair/PairHistoryLive.lean:125`) | `LedgerWriter.cost`: `approve` `sstoreCost + 2342`; `transfer` the source, debit, recipient and credit slot charges `+ 2740`; `transferFrom` `transferFromPublicGas` [`Blanc.Lift.UniswapV2Pair.LedgerWriter.cost` (`Blanc/Lift/UniswapV2Pair/ReplayWriterGas.lean:35`)] | the history's CODE, INIT, HASH-T; HASH-T freshness of the call's rows against the history's; model acceptance at the replayed state; a residual above the 2,300-gas stipend. **No callee** |
| Reachable state | `sync`, whenever the lock is open and the reserve update accepts the two actual `balanceOf(pair)` answers | `Blanc.Lift.UniswapV2Pair.pair_history_sync_live` (`Blanc/Lift/UniswapV2Pair/PairHistoryLive.lean:167`) | `syncCalleePrefixGas sevm pre callGas0 + 15 + 229` [`Blanc.Lift.UniswapV2Pair.syncCalleePrefixGas` (`Blanc/Lift/UniswapV2Pair/SyncWalk.lean:1150`)] | the two token `STATICCALL`s with their replies and returned gas (ENV); residual sentries |
| Reachable state | `mint`, on a transcript whose three answers (both `balanceOf(pair)` replies and the factory's `feeTo`) are the frame's actual answers | `Blanc.Lift.UniswapV2Pair.pair_history_mint_live` (`Blanc/Lift/UniswapV2Pair/PairHistoryLive.lean:289`) | `callee.gas + 228` [`Blanc.Lift.UniswapV2Pair.MintPrefixCallee.gas` (`Blanc/Lift/UniswapV2Pair/MintForwardAccept.lean:510`)]; returns the liquidity word | the three `STATICCALL`s (`Blanc.Lift.UniswapV2Pair.MintPrefixCallee` (`Blanc/Lift/UniswapV2Pair/MintForwardAccept.lean:471`)); HASH-T freshness of the LP rows of address 0, the recipient and the `feeTo` answer |
| Reachable state | `swap`, with or without the flash callback | `Blanc.Lift.UniswapV2Pair.pair_history_swap_live` (`Blanc/Lift/UniswapV2Pair/PairHistoryLive.lean:365`) | `swapFrontTransferGas … + swapPrefixGas … + 279 + 166` [`Blanc.Lift.UniswapV2Pair.swapFrontTransferGas` (`Blanc/Lift/UniswapV2Pair/SwapForwardFront.lean:43`), `Blanc.Lift.UniswapV2Pair.swapPrefixGas` (`Blanc/Lift/UniswapV2Pair/SwapForwardPrefix.lean:179`)] | the optional transfer `CALL`s and the callback `CALL` (present iff their amount or the data is nonzero) and the two post-callback `balanceOf(pair)` `STATICCALL`s (`Blanc.Lift.UniswapV2Pair.SwapFrontForwardEnv` (`Blanc/Lift/UniswapV2Pair/SwapForwardFront.lean:56`), `Blanc.Lift.UniswapV2Pair.SwapBackCalleeEnv` (`Blanc/Lift/UniswapV2Pair/SwapForwardAccept.lean:107`)); the decoded swap accepted by the model on those answers (`SwapContextConditions`, `SwapModelConditions`) |
| Reachable state | `burn` | `Blanc.Lift.UniswapV2Pair.pair_history_burn_live` (`Blanc/Lift/UniswapV2Pair/PairHistoryLive.lean:440`) | `BurnForwardEnv.gas` = the initial callees' charge `+ 249` [`Blanc.Lift.UniswapV2Pair.BurnForwardEnv.gas` (`Blanc/Lift/UniswapV2Pair/BurnForwardBody.lean:490`)]; returns both amounts | the two initial `balanceOf(pair)` `STATICCALL`s, the `feeTo` `STATICCALL`, both transfer `CALL`s and both final `balanceOf(pair)` `STATICCALL`s (`Blanc.Lift.UniswapV2Pair.BurnForwardEnv` (`Blanc/Lift/UniswapV2Pair/BurnForwardBody.lean:479`)); HASH-T freshness of the pair's own LP row and the `feeTo` answer's |
| Reachable state | `skim` | `Blanc.Lift.UniswapV2Pair.pair_history_skim_live` (`Blanc/Lift/UniswapV2Pair/PairHistoryLive.lean:525`) | `SkimForwardEnv.gas`, a closed sum of the lock, cache and request charges and the gas forwarded to the first token [`Blanc.Lift.UniswapV2Pair.SkimForwardEnv.gas` (`Blanc/Lift/UniswapV2Pair/SkimForwardAccept.lean:160`)] | both `balanceOf(pair)` `STATICCALL`s and both transfer `CALL`s (`Blanc.Lift.UniswapV2Pair.SkimForwardEnv` (`Blanc/Lift/UniswapV2Pair/SkimForwardAccept.lean:39`)); **the first transfer's `CALL` leaves the lock-guarded slots 0 and 8–12 unchanged** (`NoPairWriteOutsideLock`: the `SendOk`-shaped clause) |
| Frame | `permit` and `initialize`: a successful run exists at a closed charge | `Blanc.Lift.UniswapV2Pair.permit_bytecode_live_raw` (`Blanc/Lift/UniswapV2Pair/PermitEntries.lean:876`), `Blanc.Lift.UniswapV2Pair.initialize_bytecode_live_raw` (`Blanc/Lift/UniswapV2Pair/InitializeEntries.lean:321`) | `callGas + permitNonceStoreCharge + permitNonceCharge + 1137`; `G + initializeStorageCharge + 377` | for `permit`, the recovery call's reply and returned gas with a nonzero recovered owner; for `initialize`, the factory as caller. **No history-level liveness for these two** |

The views have frame-level exact and live theorems
(`Blanc.Lift.UniswapV2Pair.getterScalar_bytecode_live` (`Blanc/Lift/UniswapV2Pair/GetterScalarWalk.lean:59`),
`Blanc.Lift.UniswapV2Pair.getReserves_bytecode_live` (`Blanc/Lift/UniswapV2Pair/GetterStorageReservesWalk.lean:54`),
`Blanc.Lift.UniswapV2Pair.getterString_bytecode_live` (`Blanc/Lift/UniswapV2Pair/GetterStringWalk.lean:915`)).
**No transaction-level Uniswap liveness**: sender funding, intrinsic gas, block
room and call forwarding are not covered.

**Deployment / INIT.** `Blanc.Lift.UniswapV2Pair.Creation.pair_create2_initialized` (`Blanc/Lift/UniswapV2Pair/Creation/DeployInit.lean:126`),
for every covered fork: a `CREATE2` step of a non-static factory frame whose
memory window holds the pair creation code, with the creator's nonce below the
maximum, positive depth, an empty target and at least 2,400,000 gas forwarded,
pushes the `CREATE2` address of the creator, the salt and the creation code, and installs the certified runtime there with the
constructor storage (`unlocked = 1`, the creator as `factory`, the EIP-712 domain
separator over the creating frame's chain id and the new address
[`Blanc.Lift.UniswapV2Pair.Creation.domainSeparator_eip712` (`Blanc/Lift/UniswapV2Pair/Creation/Walk.lean:60`)]); and every successful `initialize` by the creator on that
storage leaves storage satisfying `InitializedCheckpoint`, which is the INIT
premise of `pair_history_initialized`. No hash premise. The exhibit instance
`Blanc.Lift.UniswapV2Pair.Creation.exhibit_create2` (`Blanc/Lift/UniswapV2Pair/Creation/DeployInit.lean:171`) deploys from the factory
with salt `keccak(USDC ‖ WETH)`, and the exhibit pair's address is the `CREATE2`
address of the factory, that salt and the creation code
[`Blanc.Lift.UniswapV2Pair.Creation.pairAddress_eq` (`Blanc/Lift/UniswapV2Pair/Creation/Facts.lean:104`)], by kernel evaluation. General form
`Blanc.Lift.UniswapV2Pair.Creation.pair_create2` (`Blanc/Lift/UniswapV2Pair/Creation/Deploy.lean:105`).

**Fork coverage.** The history, replay and liveness theorems assume or derive
`CoveredFork`; the deployment theorems quantify over covered forks.

**Non-claims.** That real tokens satisfy NoShrink or that a factory answers
`feeTo = 0`; that any price, the TWAP or the economics of the pool are fair or
safe; the factory's bytecode (it is a premise-level message source, and the
factory's `initialize` call is a hypothesis of the deployment theorem, not a
consequence of lifted factory code); historical inclusion of the deployment;
unforgeability of `permit` signatures; the composition of the pair with WETH9
(the WETH9 token of the exhibit pair is not discharged from Blanc's WETH9
results); transaction-level liveness; frames that were rolled back; the real
transaction history of the exhibit pair.

## 6. Summary matrix

Columns: **M1** pc-0 entry; **M2** history with the invariant carried from one
checkpoint; **M3** per-frame premises environmental only; **M4** hash
premises trace-local or none; **M5** INIT established by deployment; **M6**
liveness at a reachable state; **M7** transaction-level liveness; **M8** all
covered forks. ✓ met, ✗ not met, ~ partial (see the footnote), — not
applicable.

| | M1 | M2 | M3 | M4 | M5 | M6 | M7 | M8 |
|---|---|---|---|---|---|---|---|---|
| WETH9 (footprint) | ✓ | ✓ | ✓ | ✓ HASH-T [a] | ✓ [b] | ~ [c] | ~ [d] | ✓ |
| Beacon (`_sys`) | ✓ | ✓ | ~ [e] | ✓ none | ✓ [b] | ~ [f] | ✗ | ✓ |
| Curve | ✓ | ✓ | ✓ | ✓ HASH-T | ✓ [b] | ~ [g] | ✗ | ✓ |
| Lido | ✓ | ✓ (L1/L3) | ~ [h] | ~ [h] | ~ [i] | ✗ | ✗ | ✓ |
| V+ | ✓ | ~ [j] | ~ [j] | ✓ HASH-T (per execution) | — | ✓ nonvacuity (witnesses) | ~ [k] | ✓ |
| V− | ✓ | — | — | — | — synthetic | — | ✓ [l] | ✓ |
| EIP-7002 | ✓ | ✓ [m] | ✓ | ✓ none | ✓ [b] | ✓ | ✗ | ✓ |
| Uniswap V2 Pair | ✓ | ✓ | ✓ [n] | ✓ HASH-T | ✓ [b] [o] | ~ [p] | ✗ | ✓ |

[a] Freshness is over the uniform five-key set per raw target frame (Section
5.1). [b] A modeled deployment message under every covered fork (the
`_covered` forms); the deployment result is **not chained** into a configured
history (that a checkpoint equal to the deployed state starts a history is a
consumer's composition); and every historical deployment except Lido's
predates Prague (Section 7). [c] Withdraw, deposit and transfer at history
level; `approve` and `transferFrom` at frame and model level only. [d]
`withdraw` only. [e] Trace-local finite exclusions and `SystemCodeInstalled`
(chain-level bytes); the view and live theorems still take per-frame
`beaconEntry`. [f] Deposit at a reachable state; views need per-frame
`beaconEntry`. [g] `set_name` needs the `OwnerCallOk` callee premise; the cost
is existential. [h] History tier: `lidoEntry lidoA` at every frame (ENTRY and HASH-U). Finite
tier (frame and deployment, Section 5.4): decidable separation checks on
explicit probe lists, no universal premise, and no history theorem. [i]
`lido_deploy_init_covered` needs two hash premises; `lido_create_finite_init`
replaces them by one decidable check per probe list, for the finite observation
`RegistryOn [] probes` rather than `RegistryZeroRaw`. [j] Message, transaction
and history corollaries exist; per retained execution the world premises `hP`
and `hI`, the root code identity and `HashAvoidIn` are not derivable from the
trace (the transaction form derives `hroot`). [k] A transaction form exists
for the exclusion; no admitted transaction *witness* reaches an active guarded
body. [l] A fixed signed transaction; its signature recovery is a kernel theorem (`txC_recoveredSender`). [m] Up to 2^254 committed submission-payment occurrences since the checkpoint (user-approved scope); the fee is
the bytecode's executed word fee, and the EIP's unbounded-integer fee guarantee is refuted (§7 item 16).

[n] Callee premises only, and only where a statement needs them. The replay,
ledger and oracle history rows take none. The share-value rows take the
token-answer premises NoShrink and fee-off over the history's own steps. The
liveness rows take the token, factory and callback `STATICCALL` and `CALL`
environments (replies and returned gas), and `skim`'s first transfer carries the
`SendOk`-shaped clause `NoPairWriteOutsideLock` (§7 items 17 and 18). [o] The
deployment theorem's conclusion `InitializedCheckpoint` is literally the INIT
premise of `pair_history_initialized`, with the same factory, domain separator
and token arguments, so INIT is established by deployment followed by the
factory's `initialize`. As in [b] it is not chained into a configured history,
and the factory's `initialize` call is a hypothesis, since the factory's
bytecode is not lifted. [p] Every state-changing entry point except `permit` and
`initialize` has history-level liveness with a closed cost (`transfer`,
`approve`, `transferFrom`, `sync`, `mint`, `swap`, `burn`, `skim`); `permit` and
`initialize` have frame-level liveness only. Every cost is closed over the gas
forwarded to the callees, whose consumption enters through the callee premise
(§7 item 21).

## 7. Disclosures and limits

1. **Lido keeps universal (HASH-U) premises at the history level.** The
   per-frame premise quantifies over registry-observable keys below 2^160.
   The finite tier of Section 5.4 uses none of them and proves nothing at
   history level; its separation premises are decidable checks on explicit
   probe lists. Under a random-oracle
   model of Keccak the failure probability is about q·2^-94 per frame (four
   registry key families × 2^160 / 2^256 per written slot). This is a
   **heuristic bound estimate**, with no reduction or bound proved; the exact
   separation hypotheses remain unproved here.
2. **Two things are not claimed:** an explicit closed Curve cost formula
   (Curve's cost is exact but existential), and Lido liveness (there is none).
3. **Deployments are modeled, not historical inclusion.** WETH9 (block
   4,719,568), Beacon (11,052,984) and Curve 3Crv (10,809,467) predate Prague,
   and the Vyper pools and proxies are older. Their deployment theorems execute
   the recorded creation input as a CREATE message under current rules
   (`deployMsg`, an empty world, 1M–3M gas). **The Lido CircuitBreaker was
   created after Prague:** its creation transaction is in block 24,993,190 with
   timestamp 1,777,555,319 (2026-04-30T13:21:59Z), after the BPO2 activation
   at 1,767,747,671, the last fork in Jaune's mainnet schedule. The historical
   deployment ran under **BPO2 rules, a covered fork**, so `lido_deploy_covered`
   includes the historical fork. It is still a modeled deployment (empty world,
   `deployMsg`), not historical inclusion. The deployment results are messages,
   not validated transactions.
4. **The Beacon `_env` forms were vacuous on mainnet and have been removed.**
   The former configuredHistory_solInv_env, configuredHistory_count_env and
   configuredHistory_root_env required an offset-blind `SpawnFree`
   exclusion, which is false of the canonical EIP-7002 code
   [`Blanc.withdrawalRequestCode_not_spawnFree` (`Blanc/SystemContracts.lean:135`)]. The `_sys` headlines of Section 5.2 are
   the mainnet-satisfiable statements.
5. **Witness-engine guard.** The V− interpreter engine refuses synchronous
   MODEXP (0x05) and P256VERIFY (0x100) child frames
   [`Blanc.Lift.Witness.frameEntryForkFree` (`Blanc/Lift/WitnessArms.lean:950`), used by `Blanc.Lift.Witness.callStep` (`Blanc/Lift/WitnessArms.lean:960`)]. The `wrun … = .cont`
   run conjuncts of `vminus_witness` therefore also mean that the run enters no
   MODEXP or P-256 frame; that is what makes the runs fork-uniform. The V+ walks
   expose spawns as explicit nodes and execute no CLZ and no MODEXP or
   P256VERIFY.
6. **The following witness and deployment forms cover Prague, Osaka,
   BPO1 and BPO2:** the listed V± message witnesses are closed;
   `vminus_txC_message` is closed, while `vminus_txC_process` requires
   block room. The forms are
   `vplus_witness_covered`, `vplus_witness2_covered`, `vminus_witness_covered`,
   `vminus_txC_{message,process}`, `weth9_deploy_covered`,
   `weth9_deploy_init_covered`, `beacon_deploy_covered`,
   `curve_deploy_covered`, `lido_deploy_covered`, `lido_deploy_init_covered`.
7. **Synthetic prestates and fixtures (V±).** Pool storage (lock slots,
   balances, `totalSupply`), ETH balances, and the reader, receiver, attacker,
   dispatcher-attacker and coin contracts are synthetic. The coin-1 contract in
   V+ witness 2 is the receiver itself. The synthetic attacker and coin bytes
   are registered certificates, not deployed artifacts.
8. **Fixed signed transactions.** `vminus_txC_process` (and the Prague-only
   `Tx.vminus_tx_message`) is about one fixed signed transaction: signature
   `(r,s)`, transaction hash, index 0, **coinbase = the sender E** (warm, so
   address-shadow literals hold), chain id 0, base fee 0, block gas limit
   60,000,000. A signature-generic form is not built. The transaction's
   signature recovery is a kernel theorem (`txC_recoveredSender`). The
   signature of the Prague-only `Tx` transaction `tx0` is checked only by an
   interpreter `#guard`, not a kernel fact; no theorem cited here depends on it.
   `weth9_tx_withdraw` instead assumes coinbase ∉ {E, ca} and the signature
   premise.
9. **Callee premises.** `SendOk` (WETH9 `withdraw` to a contract) and
   `OwnerCallOk` (Curve `set_name`) assume the callee's behaviour; EOA withdraws
   and every other function need no callee premise.
10. **Static frames are not claimed** where the committed list filters them:
    WETH9 (the filter is a statement-level choice) and Lido (a `nonstatic`
    per-frame premise). An absent-target `registerPauser(t,0)` may leave the
    final registry unchanged, but its successful path has nine writes
    [`Blanc.Lift.LidoCircuitBreakerDeployed.absentZeroWrites` (`Blanc/Lift/LidoCircuitBreakerDeployed/RegistryLayout.lean:842`),
    `Blanc.Lift.LidoCircuitBreakerDeployed.setPauser_absentZero_inv` (`Blanc/Lift/LidoCircuitBreakerDeployed/SetPauserFresh.lean:440`)].
    An unchanged final registry does not make the path write-free. Beacon and
    Curve prove that statically-committed writers produce nothing.
11. **Rolled-back frames are not claimed.** History invariants hold of the
    final storage regardless; per-frame committed claims
    (`lido_history_l2_committed`, the committed invocation lists) say nothing of
    frames rolled back or under a rolled-back ancestor.
12. **Curve cost is exact but existential** (`∃ c`), with no closed formula.
    **WETH9 frame keys are a uniform five-key set** (Section 5.1).
13. **Liveness frames are fresh frames** (empty stack and memory) at a state,
    not transactions, except `weth9_tx_withdraw`.
14. **`SystemCodeInstalled`.** The canonical system bytes come from a Jaune test fixture
    (Section 2). For EIP-7002 the 504-byte runtime is provider-corroborated: three independent RPC operators
    returned bytes equal to `Blanc.withdrawalRequestCode` (recorded evidence, not re-fetched). For the other system
    contracts the mainnet identity per covered fork is not checked here. Theorems still take the code as a premise.
15. **Runtime identity is recorded, not re-fetched.** The provider agreement
    behind each lifted input is evidence in the certificate `provenance`; it is
    not reproduced by any gate.
16. **EIP-7002's unbounded-integer fee guarantee fails for the deployed bytes.** The bytecode
    computes fake_exponential with 256-bit intermediates; from excess ≈ 2893 the result is below the EIP's
    unbounded-integer value. A closed theorem exhibits a configured history (activation block; one block of 2,895
    fee-1 submissions through a looping contract, raising excess to 2893; one submission paying 2^245 wei) under
    the original hypotheses. The witness needs an account holding at least 2^245 wei, about 2^158 times the total
    ETH supply, so it is a divergence between the bytes and the EIP's pseudocode, not a practical attack. The
    configuration is synthetic as well: a Prague-only chain from a hand-built genesis, a block gas limit of 2^29
    and a flood transaction with a 2^28 gas limit; the witness shows that the modeled rules admit such a history,
    not that one fits mainnet's gas limits. Below the
    divergence the two fees agree exactly (`Blanc.Lift.WithdrawalRequest.word_fee_eq_iff_natFeeDomain` (`Blanc/Lift/WithdrawalRequest/ExactFeeDomain.lean:27`)). The FIFO headline is therefore stated
    for the executed word fee.
17. **Uniswap V2 Pair: token and factory behaviour is a premise.** The pair observes
    only what `balanceOf` and the factory's `feeTo` answer. The replay, ledger,
    oracle and refinement rows take no such premise. The share-value rows take, over
    the history's own steps only, `EntryNoShrink` (for `sync`, both answers at
    least the stored reserves; for `burn`, both first answers at least the stored
    reserves and each first answer at most its final answer plus its payout) and,
    for the fee-off row, `EntryFeeOff` (the `feeTo` answer of a mint or burn is
    zero). Tokens with transfer fees or rebasing fail NoShrink, and no theorem
    claims that a real token satisfies it. The burn form is deliberately weaker
    than "every answer is at least the stored reserve", which no ordinary burn
    satisfies.
18. **`skim` carries a `SendOk`-shaped callee clause.** The liveness theorem for
    `skim` assumes of its first transfer `CALL` that it leaves the lock-guarded
    slots 0 and 8 to 12 unchanged (`NoPairWriteOutsideLock`): a re-entry into the
    pair either meets the lock or is an unlocked entry that writes only its own
    rows. The other liveness rows state their callee environments (replies and
    returned gas) and no such clause.
19. **The Uniswap V2 Pair replay is nested, not a flat per-frame replay.** The
    steps are the **outermost** settlement-committed non-static pair frames. A pair
    frame re-entered from inside a token call, the flash-swap callback or a factory
    call is consumed inside its parent step's transcript, so the list of steps can
    be shorter than the list of committed pair frames; the observation equality of
    `pair_history_committed` places every committed pair frame in exactly one
    step's subtree. Rolled-back frames are not in the replay, and static frames
    observe nothing.
20. **Not claimed for the Uniswap V2 Pair:** composition with WETH9 is not claimed
    (the exhibit pair's WETH9 token is not discharged from Blanc's WETH9 results,
    and USDC is a premise-level callee); transaction-level liveness; permit
    signature unforgeability is not claimed (only the result of the modeled
    ECRECOVER precompile is an input); the factory's bytecode is not lifted (its
    `feeTo` answers and its `initialize` call are premise-level messages); the real
    transaction history of the exhibit pair; and any statement that a price, the
    TWAP or the economics of the pool are fair or safe.
21. **Uniswap liveness scope.** The history-level liveness rows cover `transfer`,
    `approve`, `transferFrom`, `sync`, `mint`, `swap`, `burn` and `skim`; `permit`
    and `initialize` have frame-level liveness only. Each cost is a closed
    expression, not an existential cost, but it is closed over the gas forwarded to
    each callee: the callees' consumption is fixed by the `returnedGas` equations of
    the callee premise. Premise-free liveness is false: a token or callback
    recipient whose code reverts defeats every raw run of `sync`, `skim`, `mint` and
    `swap` (the controls of Section 5.8).
22. **The Uniswap oracle history row states the modular sum of the recorded
    increments.** That each recorded increment equals the floor formula over the
    wrapped `Δt`, with the chained timestamps, is the model-level law
    (`OracleUpdate.Lawful`, `runTyped_oracle_law`); the history theorem does not
    restate it, so a reader composes the two.
23. **Altitude of the Uniswap controls.** The model controls run the typed
    functional model, not EVM execution. The bytecode controls are universal over
    successful raw runs and exhibit no concrete reverting run. The frame-level
    burn-rounding control is conditional on two named hypotheses (a burn frame
    consumer and one successful raw burn run at the witness state) that the tree
    states but does not discharge.
24. **The Uniswap deployment is modeled.** `pair_create2_initialized` is the
    `CREATE2` step of a non-static factory frame, with the constructor run inside
    the step, followed by a successful `initialize` from the creator. It is not
    historical inclusion, it is not chained into a history, and the creation
    transaction of the exhibit pair is not recorded. The exhibit address is the
    `CREATE2` address of the factory, the salt and the creation code by kernel
    evaluation, not a statement about the chain.

## 8. Axiom guarantee

**The guarantee.** `scripts/AxiomCheck.lean` imports the `Blanc` library, the two
authoring modules `Blanc/ProofRecipeTactic.lean` and
`Blanc/ProofRecipesGenerated.lean` (deliberately unreachable from the library's
root import), and Jaune's `AxiomAudit`, and runs exactly one
`#union_axioms_of_modules Blanc`. Every constant of every imported
module named `Blanc` or `Blanc.…` is a root of **one from-scratch walk** over
`Environment.find?` (types, definition, theorem and opaque values, inductive
constructors) with **one shared visited set**; the `UNION-AXIOMS 'Blanc': …`
report line prints the exact root, module and visited figures. Elaboration
fails unless the **union** of the axioms reached is within `propext`,
`Classical.choice` and `Quot.sound`; an empty population, or a reached
constant absent from the environment, also fails. That bounds `sorryAx`,
`Lean.ofReduceBool`, the `native_decide` and `bv_decide` auxiliary axioms, and
any bespoke `axiom`, for every declaration at once. Lean's own `#print axioms`
and `collectAxioms` are not verdict sources (lean4#15226).
`scripts/axiom_audit.py` refuses the audit unless every `Blanc/**/*.lean`
module is reachable from the imports, so a module nothing imports cannot
escape the walk. It runs as part of `scripts/check.sh --no-build`
(`scripts/GATES.md`).

**Consequence for citation.** There is no per-theorem list and no
per-theorem axiom row. Every theorem this map cites is covered by the union
guarantee at the commit the audit ran on, and carries exactly that bound: none
of them is one of the stricter claims below. The sentence available to a paper
is: *every constant of the library, hence each cited theorem, reaches only
`propext`, `Classical.choice` and `Quot.sound`, by one from-scratch union walk
at commit `git rev-parse HEAD`.* The guarantee concerns axioms only: the
statements are those read in Section 5, and the walk is tied to Jaune's
walker, it does not sandbox arbitrary Lean (`scripts/GATES.md`).

**The 9 stricter claims** (`#expect_axioms NAME [set]`, each checked in both
directions by the same walker; a claim exists only together with the register
row or gate constant that states it; none concerns a deployed-bytecode theorem
of this map). The checker requires this table to equal the rows of
`scripts/AxiomCheck.lean` exactly.

| # | Declaration | Exact set | Stated by |
|---|---|---|---|
| 1 | `Blanc.LidoCircuitBreaker.setPauser_sourceTrace_refines_model` | `propext, Quot.sound` | `docs/registers/LIDO_CIRCUIT_BREAKER_ASSURANCE.md` REG-2 |
| 2 | `Blanc.LidoCircuitBreaker.emptyWitness` | `propext, Quot.sound` | REG-12 |
| 3 | `Blanc.LidoCircuitBreaker.RuntimePersistentWrite.inventory_exact` | none | ACC-3 |
| 4 | `Blanc.LidoCircuitBreaker.RuntimePersistentWrite.all_length` | none | ACC-3 |
| 5 | `Blanc.LidoCircuitBreaker.constructor_inventory_cardinalities` | none | ACC-3 |
| 6 | `Blanc.LidoCircuitBreaker.officialConstructorEventScratch_eq` | none | `scripts/check-lido-circuit-breaker-deployment.py` |
| 7 | `Blanc.LidoCircuitBreaker.officialConstructorDecodedMemory_size` | `propext` | `scripts/check-lido-circuit-breaker-deployment.py` |
| 8 | `Blanc.LidoCircuitBreaker.officialConstructorDecodedMemory_read_memory` | `propext, Quot.sound` | `scripts/check-lido-circuit-breaker-deployment.py` |
| 9 | `Blanc.LidoCircuitBreaker.ConstructorPatchInvariant.read_memory` | `propext, Quot.sound` | `scripts/check-lido-circuit-breaker-deployment.py` |

**The count.** The published number of results is the leaf search's count of
leaf theorems: theorems of a `Blanc.*` module that no other Blanc declaration
uses (`scripts/leaf_audit.py`, `scripts/GATES.md` "Leaf audit"), the
independently valuable results, each covered by the union walk. It is generated
into `scripts/leaf-count.json` (never hand-edited) and quoted by the README and
the sites. At this commit it is 973 leaf results (970 public, 3 private).
The count is a property of the library at a commit, not of any cited theorem;
a cited theorem that another theorem uses is simply not a leaf. Bind any
quoted figure to `git rev-parse HEAD`, as the README does.

## 9. Named premises and definitions

Names that the tables above write unqualified.

| Name | Declaration | Role |
|---|---|---|
| `CoveredFork` | `Blanc.CoveredFork` (`Blanc/Semantics.lean:167`) | the covered forks: Prague, Osaka, BPO1, BPO2 |
| `ConfiguredHistoryTrace` | `Blanc.ExecutionTrace.ConfiguredHistoryTrace` (`Blanc/ExecutionHistory.lean:86`) | a retained replay of validated blocks under a valid chain configuration |
| `FrameAdmitted` | `Blanc.ExecutionTrace.ConfiguredHistoryTrace.FrameAdmitted` (`Blanc/ExecutionHistoryAdmission.lean:27`) | pointwise admission of every interpreter execution retained by a configured history, against a per-frame entry predicate |
| `SumNof` | `Blanc.SumNof` (`Blanc/LadderBase.lean:7`) | a total below 2^256 |
| `SystemCodeInstalled` | `Blanc.SystemCodeInstalled` (`Blanc/SystemContracts.lean:165`) | the canonical system-contract bytes are installed at their addresses |
| `NoAuthorityAt` | `Blanc.ExecutionTrace.ConfiguredHistoryTrace.NoAuthorityAt` (`Blanc/ExecutionTraceCodeAt.lean:462`) | no authorization of any transaction of a configured history recovers to the given address |
| `SpawnFree` | `Blanc.SpawnFree` (`Blanc/ExecutionTraceSystem.lean:24`) | the code has no instruction that could spawn a child frame, read at every offset (false of the canonical EIP-7002 code) |
| `FootInv` | `Blanc.Lift.Weth9.FootInv` (`Blanc/Lift/Weth9/Footprint.lean:79`) | WETH9's footprint invariant: support, injective and apart tracked slots, and the tracked ledger backed by the contract's ether |
| `KeysFresh` | `Blanc.Lift.Weth9.KeysFresh` (`Blanc/Lift/Weth9/Footprint.lean:59`) | each touched key is tracked or on an unused slot, and keys sharing a slot are one key (HASH-T) |
| `KeyInj` | `Blanc.Lift.Weth9.KeyInj` (`Blanc/Lift/Weth9/Footprint.lean:53`) | tracked slots are pairwise distinct |
| `frameKeys` | `Blanc.Lift.Weth9.frameKeys` (`Blanc/Lift/Weth9/FootFrame.lean:57`) | the decode-free five-key over-approximation of the keys a frame's call may touch |
| `Weth9.historyTouchedKeys` | `Blanc.Lift.Weth9.historyTouchedKeys` (`Blanc/Lift/Weth9/FootHistory.lean:61`) | the keys a WETH9 history touches, rolled-back frames included |
| `SendOk` | `Blanc.Lift.Weth9.SendOk` (`Blanc/Lift/Weth9/LiveWriters.lean:570`) | the callee premise of WETH9 `withdraw` to a contract: the CALL to the caller succeeds, leaves at least 1489 gas, and changes no storage of the contract |
| `AllowAdmitted` | `Blanc.Lift.Weth9.AllowAdmitted` (`Blanc/Lift/Weth9/Premise.lean:24`) | both allowance images written by the allowance entry points are off the balance image for this frame (a local HASH-U premise) |
| `SolInv` | `Blanc.Lift.BeaconDeposit.SolInv` (`Blanc/Lift/BeaconDeposit/Layout.lean:42`) | Beacon's storage abstraction: an intact zero-hash table and the model invariant for a deposit history |
| `beaconEntry` | `Blanc.Lift.BeaconDeposit.beaconEntry` (`Blanc/Lift/BeaconDeposit/Ladder.lean:130`) | Beacon's carried entry condition: calldata length below 2^256, the SHA-256 precompile account (`0x02`) not a delegation, and warm |
| `DepositDecodable` | `Blanc.Lift.BeaconDeposit.DepositDecodable` (`Blanc/Lift/BeaconDeposit/DepositArgs.lean:55`) | the deployed decoder accepts the deposit calldata |
| `ShaReady` | `Blanc.Lift.ShaReady` (`Blanc/Lift/ExactWalkCutOps.lean:77`) | the SHA-256 precompile premises of a frame's world: address 2 undelegated and warm, a precompile of the fork |
| `VyInv` | `Blanc.Lift.Curve3Crv.VyInv` (`Blanc/Lift/Curve3Crv/Layout.lean:95`) | Curve 3Crv's storage abstraction over the live keys |
| `FreshKeys` | `Blanc.Lift.Curve3Crv.FreshKeys` (`Blanc/Lift/Curve3Crv/Layout.lean:115`) | the frame-local premise for the keys a Curve frame touches: each is fresh and their slots are pairwise distinct (HASH-T) |
| `Curve3Crv.historyTouchedKeys` | `Blanc.Lift.Curve3Crv.historyTouchedKeys` (`Blanc/Lift/Curve3Crv/CarriedHistory.lean:27`) | the keys a Curve history touches |
| `OwnerCallOk` | `Blanc.Lift.Curve3Crv.OwnerCallOk` (`Blanc/Lift/Curve3Crv/LiveBodies.lean:1692`) | the callee premise of Curve `set_name`: its static `owner()` call answers whenever it is given enough gas, and leaves at least `R` gas |
| `RegistryZeroRaw` | `Blanc.Lift.LidoCircuitBreakerDeployed.RegistryZeroRaw` (`Blanc/Lift/LidoCircuitBreakerDeployed/L2.lean:46`) | the raw-slot form of an empty registry: the array length word is zero and every canonical address has zero assignment, index and count words |
| `StateInv` | `Blanc.ContractSpecSem.StateInv` (`Blanc/LadderSem.lean:86`) | the state invariant of a semantic contract spec (`lidoSpec.StateInv`) |
| `ForeignApart` | `Blanc.Lift.LidoCircuitBreakerDeployed.ForeignApart` (`Blanc/Lift/LidoCircuitBreakerDeployed/Foreign.lean:21`) | a raw slot is disjoint from the storage slots of every logical key the registry observes up to a bound (HASH-U) |
| `LocalApart` | `Blanc.Lift.LidoCircuitBreakerDeployed.LocalApart` (`Blanc/Lift/LidoCircuitBreakerDeployed/Frame.lean:52`) | the three non-registry slots a frame can write are off the registry layout |
| `EntryAt` | `Blanc.Lift.LidoCircuitBreakerDeployed.EntryAt` (`Blanc/Lift/LidoCircuitBreakerDeployed/Frame.lean:58`) | the registry-writer premise holds of every registry witness of the frame's entry storage (HASH-U at bound 2^160 for `lidoA`) |
| `L2Post` | `Blanc.Lift.LidoCircuitBreakerDeployed.L2Post` (`Blanc/Lift/LidoCircuitBreakerDeployed/L2Frame.lean:32`) | the removal effects of the L2 frame theorem, relative to the pre-call witness |
| `RegistryWitness` | `Blanc.LidoCircuitBreaker.RegistryWitness` (`Blanc/LidoCircuitBreakerRegistryModel.lean:254`) | a witness that a storage is a well-formed registry |
| `RegistryOn` | `Blanc.Lift.LidoCircuitBreakerDeployed.RegistryOn` (`Blanc/Lift/LidoCircuitBreakerDeployed/FiniteRegistry.lean:24`) | finite registry agreement: valid entry list, exact length word and live array cells, and assignment/index/count words for each supplied probe (finite tier) |
| `checkRegistryOn` | `Blanc.Lift.LidoCircuitBreakerDeployed.checkRegistryOn` (`Blanc/Lift/LidoCircuitBreakerDeployed/FiniteRegistry.lean:39`) | the executable decision of `RegistryOn` |
| `checkLiveCovered` | `Blanc.Lift.LidoCircuitBreakerDeployed.checkLiveCovered` (`Blanc/Lift/LidoCircuitBreakerDeployed/FiniteRegistry.lean:74`) | every listed target and pauser is a probe |
| `registryQueries` | `Blanc.Lift.LidoCircuitBreakerDeployed.registryQueries` (`Blanc/Lift/LidoCircuitBreakerDeployed/FiniteRegistry.lean:17`) | the finite logical keys a registry observation reads: the length key, the live array keys, and the three mapping keys of each probe |
| `checkFaithfulOn` | `Blanc.SlotFootprint.checkFaithfulOn` (`Blanc/SlotFootprint.lean:133`) | decidable: each written key and each observed key with the same slot are the same key (a HASH-T instance on explicit lists) |
| `checkApartOn` | `Blanc.SlotFootprint.checkApartOn` (`Blanc/SlotFootprint.lean:145`) | decidable: no observed key has a slot in the given raw-slot list |
| `solKey` | `Blanc.Lift.LidoCircuitBreakerDeployed.solKey` (`Blanc/Lift/LidoCircuitBreakerDeployed/RegistryLayout.lean:142`) | the raw storage slot of a logical registry key (Solidity mapping and array layout) |
| `nonzeroWrites` | `Blanc.Lift.LidoCircuitBreakerDeployed.nonzeroWrites` (`Blanc/Lift/LidoCircuitBreakerDeployed/RegistryLayout.lean:763`) | the logical writes of a nonzero `registerPauser` update of an existing target |
| `mapSlot` | `Blanc.Lift.mapSlot` (`Blanc/Lift/MapSlot.lean:19`) | the Solidity mapping slot `keccak(key ++ base)` |
| `findEntry` | `Blanc.LidoCircuitBreaker.findEntry` (`Blanc/LidoCircuitBreakerRegistryModel.lean:12`) | the index and pauser of a target in an entry list |
| `HashAvoidIn` | `Blanc.LockExclusion.LockSpec.HashAvoidIn` (`Blanc/LockExclusion.lean:316`) | every frame of the pool running the lock code avoids the lock slot with its executed hashes (HASH-T) |
| `VplusExcludes` | `Blanc.Lift.VyperNonreentrantDeployed.Fixed.VplusExcludes` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:44`) | the statement form of the V+ exclusion |
| `InitializedCheckpoint` | `Blanc.Lift.UniswapV2Pair.InitializedCheckpoint` (`Blanc/Lift/UniswapV2Pair/Creation/DeployInit.lean:34`) | the Pair's INIT after deployment and `initialize`: the pair storage represents `initializedState` over the empty tracked footprint |
| `initializedState` | `Blanc.Lift.UniswapV2Pair.initializedState` (`Blanc/Lift/UniswapV2Pair/Creation/DeployInit.lean:29`) | the model state after a factory deploys a pair with a given domain separator and initializes it with two tokens: zero supply, reserves, accumulators and `kLast`, `unlocked = 1`, no ledger row |
| `WriterRep` | `Blanc.Lift.UniswapV2Pair.WriterRep` (`Blanc/Lift/UniswapV2Pair/WriterStorage.lean:58`) | the Pair's storage abstraction over a finite tracked set of balance, allowance and nonce rows: slots 0 to 12 match the model, each tracked row matches, every other nonzero word is at a tracked row, and untracked rows are zero in the model |
| `WriterFreshKeys` | `Blanc.Lift.UniswapV2Pair.WriterFreshKeys` (`Blanc/Lift/UniswapV2Pair/WriterStorage.lean:36`) | HASH-T for the Pair: each touched row is tracked or on a slot that is neither fixed nor a tracked row's, and rows sharing a slot are one row |
| `pairHistoryTouchedKeys` | `Blanc.Lift.UniswapV2Pair.pairHistoryTouchedKeys` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:303`) | the rows the Pair's frames select, over every raw Pair frame root of a history, rolled-back frames included |
| `PairStep.Authentic` | `Blanc.Lift.UniswapV2Pair.PairStep.Authentic` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:162`) | a step's frame is a pc-0, committed, non-static frame at the pair, and its entry and transcript are the ones its own run decodes and observed |
| `EntryNoShrink` | `Blanc.Lift.UniswapV2Pair.EntryNoShrink` (`Blanc/Lift/UniswapV2Pair/Properties.lean:2643`) | the token-answer premise of the share-value rows, per entry (ENV: callee behaviour; exact forms in Section 7 item 17) |
| `EntryFeeOff` | `Blanc.Lift.UniswapV2Pair.EntryFeeOff` (`Blanc/Lift/UniswapV2Pair/Properties.lean:2657`) | the factory's `feeTo` answer of a mint or burn is zero (ENV: callee behaviour) |
| `sourceReplayAnswers` | `Blanc.Lift.UniswapV2Pair.sourceReplayAnswers` (`Blanc/Lift/UniswapV2Pair/SourceReplay.lean:105`) | at every step of a replay, `EntryFeeOff` and `EntryNoShrink` at the carried model state |
| `sourceReplayNoShrink` | `Blanc.Lift.UniswapV2Pair.sourceReplayNoShrink` (`Blanc/Lift/UniswapV2Pair/SourceReplay.lean:150`) | at every step of a replay, `EntryNoShrink` at the carried model state |
| `NoPairWriteOutsideLock` | `Blanc.Lift.UniswapV2Pair.NoPairWriteOutsideLock` (`Blanc/Lift/UniswapV2Pair/SkimForwardAccept.lean:30`) | the callee premise of `skim`'s first transfer: the `CALL` leaves the lock-guarded slots 0 and 8 to 12 unchanged |

## 10. Checking this document

`scripts/check-deployed-claim-map.sh` holds this page to the repository. It is
offline, elaborates no Lean, and runs in continuous integration before the
toolchain is installed. It requires that:

- every fully qualified `Blanc.…` name resolves, spelled in full, to a public
  declaration written in Blanc's sources (the lexical resolver of
  `scripts/axiom_audit.py`);
- every `path:line` reference is attached to such a name and points at a line
  of that file that declares it or belongs to its docstring;
- every repository file it cites exists;
- every other identifier-shaped code span that looks like a Lean name is still
  some declaration's name;
- the table of stricter axiom claims in Section 8 equals the `#expect_axioms`
  rows of `scripts/AxiomCheck.lean` exactly, in both directions, and the leaf
  count equals `scripts/leaf-count.json`;
- the Jaune revision, the Lean toolchain and the covered forks equal the
  repository's; the runtime sizes and codehashes of Section 2 equal the lifted
  input files, its creation transactions and blocks appear in the certificate
  provenance, the Lido creation timestamp equals the reference input and
  follows the BPO2 activation, and the system-contract sizes and SHA-256
  digests equal the bytes written in `Blanc/SystemContracts.lean`; the Uniswap V2 Pair
  row's code-read block and block hash appear in its certificate provenance, its
  creation code hashes to the factory's init-code hash, and the lifted runtime is
  embedded in that creation code at bytes 261 to 11,553;
- the page keeps its section structure, its required headline theorems and its
  load-bearing disclosures, and carries no process vocabulary.

The required headline theorems are also pinned by exact statement in
`scripts/ClaimCheck.lean` (gate `scripts/check-claims.sh`), together with the
definitions those statements are stated through, so a weakened headline fails
there although this checker elaborates no Lean.

Every run also executes in-memory falsifiers, each of which must be rejected: a
misspelled declaration, a stale line, a wrong file, an orphan line reference, a
missing cited file, a stale bare name, a wrong leaf count, an extra, a missing and a wrong stricter
axiom claim, a wrong codehash, size, creation transaction and system-contract
digest, a wrong Jaune revision and Lido timestamp, process vocabulary, a
deleted headline and a dropped disclosure.

What the check does **not** do: it does not elaborate Lean or re-derive any
axiom set (its authority over axioms is `scripts/AxiomCheck.lean`, verified by
`scripts/check.sh`); it does not judge whether a row's prose is a fair summary
of its theorem, whether a premise list is complete, or whether the bytes in
`scripts/lift/inputs/` are the bytes on the chain; and it does not re-run the
conformance figures of Section 3.
