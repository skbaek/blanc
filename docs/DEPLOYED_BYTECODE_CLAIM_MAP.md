# Deployed-bytecode claim map

What Blanc proves about bytecode that is already on Ethereum mainnet: WETH9, the
Beacon deposit contract, the Curve 3Crv LP token, the Curve 3pool StableSwap pool
(with 3Crv as its LP token, Section 5.11), Lido's CircuitBreaker, the
Vyper nonreentrancy pair (the fixed pool implementation "V+" and the vulnerable
one "V−"), the EIP-7002 withdrawal-request predeploy, the Uniswap V2 Pair and
the Uniswap V2 Factory, USDC (its proxy, implementation and signature library), and
two compositions over one configured history: the Uniswap V2 Pair with WETH9 as one
of its tokens (Section 5.9), and the Pair with USDC and WETH9 as its two tokens
(Section 5.10).
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
  [`Blanc.ExecutionTrace.ConfiguredHistoryTrace` (`Blanc/ExecutionHistory.lean:116`)] is a retained replay of validated
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
| Curve 3pool StableSwap | 0xbEbc44782C7dB0a1A60Cb6fe97d0b483032FF1C7 | 21,199 | 0x954a1e212c557c85043985931498ffa3e2fcbe7dfe9cd61513f36eb47d6f4dfc | 0x20793bbf260912aae189d5d261ff003c9b9166da8191d8f9d63ff1c7722f3ac6 (deployer 0xbabe61887f1de2713c6f97e567623453d3c79f67, nonce 43) | 10,809,473 |
| Lido CircuitBreaker | 0x6019CB557978296BA3C08a7B73225C0975DFB2F7 | 4,584 | 0x63d4da6a25804fabdc61ace21c19d1f2e1425ab9ade8d8a348a2591e801836ec | 0x9a1328c1f63fcdfd53d611cfe9c9a5f4c284c4c3e61af9066d90acaac2d5279f (deployer 0xaCf5f111399a7c613D2f5b96b70F2Ea464D3cdF3, nonce 0) | 24,993,190 |
| Vyper pool implementation, fixed (V+) | 0x847ee1227a9900b73aeeb3a47fac92c52fd54ed9 | 18,320 | 0x59469db6b75b045025abb5386ae6b7ef7e1698d13ee93f3d4ed32d5f72506e0e | 0xfaad66f8fa2b4883b9e5c91b69e31ac8c2cdbc6d383b8776d0eee94d3ee0a251 | 17,110,099 |
| ETH/stETH pool proxy to the V+ implementation | 0x21e27a5e5513d6e65c4f830167390997aa84843a | 45 | 0x9e28a09452d2354fc4e15e3244dde27cbc4d52f12a10b91f2ca755b672bfa9be | not recorded | not recorded |
| Vyper pool implementation, vulnerable (V−) | 0x6326debbaa15bcfe603d831e7d75f4fc10d9b43e | 17,535 | 0xba0284a6a8a86734c1c777e3c6b5b56f2c8ba95dc0f7eba481c6d09da7885ebc | 0xd27491757b3a4bc9287ed44ce5c43de9f32131264548ce139f0a702c3d5f389e | 12,904,329 |
| Pool proxy to the V− implementation | 0x9848482da3ee3076165ce6497eda906e66bb85c5 | 45 | 0xbed04db3507e08e5220f6eadf98d5df05bdbc74df129c73fcbab7c441e86b124 | not recorded | not recorded |
| Uniswap V2 Pair (exhibit: the USDC/WETH pair) | 0xB4e16d0168e52d35CaCD2c6185b44281Ec28C9Dc | 11,293 | 0x5b83bdbcc56b2e630f2807bbadd2b0c21619108066b92a58de081261089e9ce5 | not recorded (runtime read at a finalized block, below) | not recorded |
| Uniswap V2 Factory | 0x5C69bEe701ef814a2B6a3EDD4B1652CB9cc5aA6f | 13,859 | 0xbab145d02e7005f0d84c6c1639d39b799b0ea16df99ebbdaf5a14d9da820b4e0 | not recorded (runtime read at a finalized block, below) | not recorded |
| USDC FiatTokenProxy | 0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48 | 2,186 | 0xd80d4b7c890cb9d6a4893e6b52bc34b56b25335cb13716e0d1d31383e6b41505 | not recorded (runtime read at a finalized block, below) | not recorded |
| USDC FiatTokenV2_2 implementation | 0x43506849D7C04F9138D1A2050bbF3A0c054402dd | 23,464 | 0xcdfb7d322961af3acae7a8f7ee8b69c205b36f576cc5b077f170c7eb8ecbe3ea | not recorded (runtime read at a finalized block, below) | not recorded |
| USDC SignatureChecker library | 0x800C32EaA2a6c93cF4CB51794450ED77fBfbB172 | 1,741 | 0x76cfc2ce63b1f05cb58ae553090665c2aabf2e13cf8a0e6da755c096fc5295dd | not recorded (runtime read at a finalized block, below) | not recorded |

Compilers, from the certificate provenance: 3Crv Vyper 0.2.4; the Curve 3pool Vyper 0.2.4; the
CircuitBreaker solc 0.8.34; V− Vyper 0.2.15; V+ Vyper 0.3.7; the Uniswap V2 Pair
solc 0.5.16; USDC proxy solc 0.4.24; implementation solc 0.6.12; library solc 0.6.12.
The Uniswap V2 Factory's certificate provenance names no compiler; the compiler
metadata at the end of its lifted runtime encodes solc 0.5.16.

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

**The Uniswap V2 Factory row.** The factory's runtime was read by `eth_getCode` at
finalized block 26,209,011 (block hash 0x9df55d378356653a65256646c23abda202319a66be5b2d1699c9f05cf1a6dc92)
and is equal across three separately operated providers; its creation transaction is
not recorded, and the lifted input is `scripts/lift/inputs/uniswap-v2-factory-runtime.hex`.
Bytes 2,171 to 13,806 of it are the Pair creation code, byte for byte; bytes 0 to 2,170
are the factory's own logic and the last 52 bytes its compiler metadata. The certificate
covers the logic and the metadata, and the Pair creation code inside the runtime is data
to the factory: it is copied for `CREATE2`, and the certificate's walk of the factory's
code never enters it.

**The USDC rows.** The USDC proxy, implementation and library runtimes were read
by `eth_getCode` at finalized block 26,213,219 (block hash 0xa79841b4ef0d00bcd0b0c8dc6b405efd4ab1ac3182b1a9a4877f873673e24b6c)
and are equal byte for byte across six separately operated providers: Allnodes PublicNode,
dRPC, Bware BlastAPI, Tenderly, Nodies and bloXroute; no creation transaction of these
instances is recorded, and the lifted inputs are `scripts/lift/inputs/usdc-proxy-runtime.hex`,
`scripts/lift/inputs/usdc-impl-runtime.hex` and `scripts/lift/inputs/usdc-lib-runtime.hex`.
The proxy holds the implementation address in its implementation slot
0x7050c9e0f4ca769c69bd3a8ef740bc37934f8e2c036e5a723fd8ee048ed3f8c3
(`keccak256("org.zeppelinos.proxy.implementation")`), agreed across all six providers.
The library address is linked into the implementation runtime at two
PUSH20 sites (bytes 18,390 and 20,105), each reaching a DELEGATECALL. No Solidity recompilation.

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
reader (41 bytes) and a receiver (86 bytes). The reachable witnesses of Sections
5.5 and 5.6 use their own fixtures, each installed by an executed CREATE of its
registered creation input: a shared address-keyed token Token20 (299-byte
runtime, 315-byte creation input), the V− attacker AttackerR (186-byte runtime,
different code from the dispatcher attacker; 195-byte creation input), the V+
receiver ReceiverR (89-byte runtime; 98-byte creation input), and one 54-byte
synthetic EIP-1167 clone-creation input per side. The two implementations are
created there from their preserved creation inputs,
`scripts/lift/inputs/vyper-847e-creation.hex` (18,353 bytes) and
`scripts/lift/inputs/vyper-6326-creation.hex` (17,569 bytes), whose origin is
recorded in the certificate provenance; that is not historical inclusion.

## 3. Trust base

| Component | What is trusted | Evidence |
|---|---|---|
| Lean toolchain `v4.35.0` | Kernel soundness | For every constant of every Blanc module, and therefore for every theorem this map cites, the reachable axioms are within `propext`, `Classical.choice`, `Quot.sound`; one from-scratch union walk (Section 8), not `#print axioms` or `collectAxioms` |
| Jaune revision `e8db2742` | That its EVM and transaction definitions match Ethereum | Not a theorem. Conformance, as reported by that Jaune revision's own README and not re-run here: **4,968/4,968** supported fixture files and **34,449/34,449** cases of the execution-specs mainnet corpus (`tests@v21.0.1`), Prague through BPO2 including configured fork transitions |
| Lift certificates | Nothing | The Python producers are untrusted. Each certificate is accepted only by its Lean `cert_check`, a kernel decision, against the literal bytes |
| Runtime identity | That the lifted bytes are the mainnet bytes | Recorded in each certificate's `provenance`: `eth_getCode` agreement across separately operated public providers (two for WETH9, five for 3Crv, five for the Curve 3pool, three each for the Uniswap V2 Pair and the Uniswap V2 Factory, each at one finalized block); the creation inputs of WETH9, the Beacon deposit contract, 3Crv and the Curve 3pool fetched from two providers and equal byte for byte; the Lido creation input equal to the frozen reference template plus its constructor arguments; the two pool implementations taken from Sourcify v2 records; the Uniswap V2 Pair creation code taken from the publisher artifact of `@uniswap/v2-core` 1.0.1, its Keccak-256 equal to the factory's init-code hash and its embedded runtime equal to the lifted runtime; the lifted factory runtime embeds that creation code byte for byte. The codehashes in Section 2 are recomputed from the lifted files by the checker |
| Fork scope | — | `CoveredFork` is Prague, Osaka, BPO1, BPO2. Amsterdam is not covered. The 3Crv deployment-rooted rows use `HistFork` (Byzantium through BPO2), which includes the Muir Glacier rules the deployment block ran under; the Jaune conformance figures above begin at Prague and do not cover them |
| Chain arithmetic | Model bound | Configured traces carry total ETH plus withdrawals below 2^256 (`SumNof` at the checkpoint) |
| Signature recovery | Premise of the signature-generic transaction theorems | `recoverSender … = .ok E` is a premise of every theorem that quantifies over all signed transactions, since there is then no single signature to evaluate. For a concrete transaction the kernel evaluates recovery: `Blanc.Drip.concreteCreateRecoveredSender` (`Blanc/DripConcreteHistory/Deployment.lean:197`), `Blanc.Drip.concreteExitRecoveredSender` (`Blanc/DripConcreteHistory/AccrualExit.lean:1264`), `Blanc.Lift.WithdrawalRequest.FloodTx.txB_recoveredSender` (`Blanc/Lift/WithdrawalRequest/FloodTxRecover.lean:149`) and, for V−, `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.txC_recoveredSender` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/TxCRecover.lean:99`) |

## 4. Premise classes

Every theorem hypothesis below has one of these classes; these are not Lean
logical axioms, and a clean axiom audit does not discharge them. The table says
whether a class is acceptable and whether deployment establishes INIT.

| Class | Meaning | Acceptable in a headline? | INIT established by a deployment theorem? |
|---|---|---|---|
| CODE | Installed code and fork identity | Yes | — |
| INIT | Stated once, at the checkpoint | Yes, if shown inhabited, ideally by deployment | **WETH9** footprint `FootInv`: yes, no hash premise: the recorded creation transaction in its retained block leaves the constructor's storage [`Blanc.Composition.LiveUsdcWeth9B26213219.weth9_deployment` (`Blanc/Composition/LiveUsdcWeth9B26213219Headlines.lean:40`)], whose metadata-only words satisfy `FootInv ∅` [`Blanc.Lift.Weth9.FootInv.deployed` (`Blanc/Lift/Weth9/Footprint.lean:211`)], and the history from it carries `FootInv` over the touched keys [`Blanc.Composition.LiveUsdcWeth9B26213219.WethDeploymentTo.foot` (`Blanc/Composition/LiveUsdcWeth9B26213219History.lean:264`)]. **Beacon** `SolInv []`: yes, no hash premise [`Blanc.Lift.BeaconDeposit.Creation.beacon_deploy_covered` (`Blanc/Lift/BeaconDeposit/Creation/Deploy.lean:151`)], and from the actual deployment block, with no INIT premise [`Blanc.Lift.BeaconDeposit.beacon_deposits` (`Blanc/Lift/BeaconDeposit/HistDeployment.lean:166`)]. **Curve** `VyInv … ∅`: yes, no hash premise [`Blanc.Lift.Curve3Crv.Creation.curve_deploy_covered` (`Blanc/Lift/Curve3Crv/Creation/Deploy.lean:304`)], and from the recorded creation transaction in its retained Muir Glacier block [`Blanc.Lift.Curve3Crv.Creation.HistoricalTx.actual_block_cut` (`Blanc/Lift/Curve3Crv/Creation/HistoricalTxTrace.lean:229`), `Blanc.Lift.Curve3Crv.C3crvDeploymentTo.created` (`Blanc/Lift/Curve3Crv/HistDeployment.lean:78`)]. **Lido** `RegistryZeroRaw` and `StateInv`: only under two hash premises `ForeignApart 0 0` and `ForeignApart 0 1` (bound zero still quantifies address mapping keys) [`Blanc.Lift.LidoCircuitBreakerDeployed.Creation.lido_deploy_init_covered` (`Blanc/Lift/LidoCircuitBreakerDeployed/Creation/Deploy.lean:210`)]; from the actual creation transaction, under the one hash premise `LidoSlotsApart` [`Blanc.Lift.LidoCircuitBreakerDeployed.lido_registry_consistent` (`Blanc/Lift/LidoCircuitBreakerDeployed/DeploymentHistory.lean:113`)]. **Uniswap V2 Pair** `InitializedCheckpoint`: yes, no hash premise, by a `CREATE2` deployment followed by the factory's `initialize`, whose successful run is constructed [`Blanc.Lift.UniswapV2Pair.Creation.pair_create2_initialized` (`Blanc/Lift/UniswapV2Pair/Creation/DeployInit.lean:126`), `Blanc.Lift.UniswapV2Pair.Creation.pair_create2_initialize_live` (`Blanc/Lift/UniswapV2Pair/Creation/DeployInit.lean:246`)]. **V±**: the exclusion (V+) and violation (V−) statements take no INIT premise; the reachable witnesses execute deployment, initialization and liquidity as messages from a creator-only world [`Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit.vplus_exit` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exit/Capstone.lean:153`), `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol.vminus_attack` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Reach/ViolFinal.lean:78`); the detailed capstones `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit.vplus_reachable_capstone` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exit/Capstone.lean:48`), `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol.vminus_reachable_capstone` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Reach/ViolFinal.lean:39`)], message level only (Section 7 item 25); the older witnesses and the V− transaction row start from synthetic prestates. **Uniswap V2 Pair × WETH9** `JointCheckpoint`: by the Pair's `CREATE2` deployment and an `initialize` naming WETH9 as either token, from a world whose WETH9 satisfies its footprint INIT with the new address's balance row tracked and its allowance rows zero, no hash premise [`Blanc.Composition.UniswapV2PairWeth9Joint.pair_weth9_create2_jointCheckpoint_side` (`Blanc/Composition/UniswapV2PairWeth9Deploy.lean:56`)]; for one synthetic world, by a checker evaluated in the kernel (Section 5.9); **Uniswap V2 Pair × USDC × WETH9** `JointCheckpoint2`: by the Pair's `CREATE2` deployment and `initialize` naming USDC as `token0` and WETH9 as `token1`, from an initialize world carrying both tokens' checkpoint facts, no hash premise [`Blanc.Composition.UniswapV2PairUsdcWeth9.pair_usdc_weth9_create2_jointCheckpoint2` (`Blanc/Composition/UniswapV2PairUsdcWeth9Deploy.lean:31`)]; for one synthetic world `U0`, by a checker evaluated in the kernel (Section 5.10). **Curve 3pool** `Checkpoint`, the pool's storage predicate at the constructor's model state: yes, no hash premise [`Blanc.Lift.Curve3Pool.Creation.pool_deploy_covered` (`Blanc/Lift/Curve3Pool/Creation/Deploy.lean:292`)]; the joint 3pool-and-3Crv `JointCheckpoint` is not established by deployment, and is checked by a kernel-evaluated checker on synthetic worlds only (Section 5.11) |
| ENTRY | Required at every entered frame | Only if environmental, never invariant-shaped | — |
| HASH-T | Exact separation of the hashes and keys actually computed or touched in the trace, including avoidance of fixed slots where stated | Yes when stated; narrower and amenable to finite checking with a concrete initial footprint. Computational collision resistance does not entail this exact fact; fixed-slot avoidance also concerns target/preimage behavior. No cryptographic reduction is proved. The Lido finite tier (Section 5.4) states its instances as decidable checks on explicit key lists, so a concrete instance is closed by kernel evaluation | — |
| HASH-U | Exact separation quantified over all 2^160 addresses or indices | Needs justification; not established here. The finite domain does not make proof impossible. Under a random-function model of Keccak the estimated failure probability is about q·2^-94 per frame (q = written slots): **heuristic only, with no reduction or bound proved** | — |
| ENV | Gas, warmth, depth, static flag, callee behaviour, trace-local exclusions (no authorization or CREATE at given addresses) | Yes when stated; better derived | — |
| ARITH | Numeric bounds | Yes | — |

The per-frame calldata bound (below 2^256) is not a premise of any history
theorem: it holds for every raw frame of every configured history on all
covered forks [`Blanc.ExecutionTrace.ConfiguredHistoryTrace.calldata_bound` (`Blanc/ExecutionTraceCalldata.lean:927`);
`Blanc.ExecutionTrace.ConfiguredHistoryTrace.frameAdmitted_calldata` (`Blanc/ExecutionTraceCalldata.lean:944`)], because
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
| **From the actual deployment:** at any block after WETH9's recorded creation transaction, the stored balance words of every holder that the history from that transaction touched sum to at most WETH9's ether (the total only). Intermediate: `FootInv` over the touched keys at that block | `Blanc.Composition.LiveUsdcWeth9B26213219.weth9_backed` (`Blanc/Composition/LiveUsdcWeth9B26213219Headlines.lean:49`), with conclusion `Blanc.Lift.Weth9.EtherBacked` (`Blanc/Lift/Weth9/Holders.lean:32`); via `Blanc.Composition.LiveUsdcWeth9B26213219.WethDeploymentTo.foot` (`Blanc/Composition/LiveUsdcWeth9B26213219History.lean:264`) (from `Blanc.Lift.Weth9.weth9_history_committed_from_creation_block` (`Blanc/Lift/Weth9/DeployBlockHistory.lean:218`)) and `Blanc.Lift.Weth9.FootInv.etherBacked` (`Blanc/Lift/Weth9/Holders.lean:48`) | Deployment-rooted history / safety | DEPLOYMENT `Blanc.Composition.LiveUsdcWeth9B26213219.WethDeploymentTo` (`Blanc/Composition/LiveUsdcWeth9B26213219History.lean:28`): the retained configured `HistFork` mainnet block 4,719,568 whose transaction at the cut is the recorded creation (nonce 446 from the recorded deployer, the creation code, zero value, enough gas, an empty target), the configured history after it, and **HASH-T** freshness of the keys the raw WETH9 frames of the rest of that block and of that history touch, all fields of the record. No installed-code, INIT or `SumNof` premise | The total only; INIT is the constructor's storage, derived from the transaction |
| Frame form inside a root derivation | `Blanc.Lift.Weth9.foot_frame_post_in` (`Blanc/Lift/Weth9/FootFrame.lean:291`) | Frame / safety | CODE; `KeyInj U`; `frameKeys sevm ⊆ U` | Supporting |
| The premise is necessary: a written slot that coincides with a tracked balance slot breaks backing | `Blanc.Lift.Weth9.approve_collision_breaks_footprint` (`Blanc/Lift/Weth9/FootFrame.lean:213`), `Blanc.Lift.Weth9.trackedSum_collision_breaks_backing` (`Blanc/Lift/Weth9/FootFrame.lean:200`); a related control `Blanc.Lift.Weth9.approve_collision_control` (`Blanc/Lift/Weth9/Approve.lean:315`) | Frame / control | a hash collision is posited | |

**History (committed replay)**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| **From the actual deployment:** at any block after WETH9's recorded creation transaction, each holder the history from that transaction touched has, as its stored balance word, the credits minus the debits that the decoded committed writer calls of that history made to it, **modulo 2^256** (a congruence of integers, not an equality of naturals). Intermediate: the footprint ledger at the future state equals the model `Ledger.run` over exactly the settlement-committed writer invocations at the contract, in trace order (rolled-back frames absent, views contribute nothing, re-entered calls after the withdraw that sent them); also code intact, `SumNof future`, `FootInv U future`, and the model run with ETH stays `Backed` | `Blanc.Composition.LiveUsdcWeth9B26213219.weth9_net_flow` (`Blanc/Composition/LiveUsdcWeth9B26213219Headlines.lean:59`), with conclusion `Blanc.Lift.Weth9.NetFlow` (`Blanc/Lift/Weth9/Holders.lean:93`); via `Blanc.Composition.LiveUsdcWeth9B26213219.WethDeploymentTo.replay` (`Blanc/Composition/LiveUsdcWeth9B26213219History.lean:274`) (from `Blanc.Lift.Weth9.weth9_history_committed_from_creation_block` (`Blanc/Lift/Weth9/DeployBlockHistory.lean:218`), the mid-block form of `Blanc.Lift.Weth9.weth9_history_committed` (`Blanc/Lift/Weth9/CommittedHistory.lean:62`)) and `Blanc.Lift.Weth9.netFlow_of_replay` (`Blanc/Lift/Weth9/Holders.lean:221`) | Deployment-rooted history / safety, exact extraction | DEPLOYMENT `Blanc.Composition.LiveUsdcWeth9B26213219.WethDeploymentTo` (`Blanc/Composition/LiveUsdcWeth9B26213219History.lean:28`): the retained configured `HistFork` mainnet block 4,719,568 whose transaction at the cut is the recorded creation (nonce 446 from the recorded deployer, the creation code, zero value, enough gas, an empty target), the configured history after it, and **HASH-T** freshness of the keys the raw WETH9 frames of the rest of that block and of that history touch, all fields of the record. No installed-code, INIT or `SumNof` premise; the intermediate takes the same four as `weth9_history_footprint` | The congruence is modulo 2^256 because the model's credits wrap. The list is definitional [`Blanc.Lift.Weth9.committedInvocations` (`Blanc/Lift/Weth9/CommittedReplay.lean:46`)]. Frames contribute iff target = contract, non-static, and a writer selector; **the non-static filter is a statement-level choice, not proved impossible for WETH9 writers** (it is proved for Curve and Beacon) |

**Liveness.** All explicit costs are sums of fixed parts and
`sloadCost`/`sstoreCost`/`callNet`; `G` is the gas left at the end. "Fresh
frame" means empty stack and memory, non-static, value 0, the contract's code,
a covered fork, and calldata of at least 4 bytes and below 2^256.

| Level | Claim | Theorem | Cost / gas formula | Premises beyond a fresh frame |
|---|---|---|---|---|
| Frame | `balanceOf` and `decimals` execute and return the stored word | `Blanc.Lift.Weth9.weth9_balanceOf_gas_exact` (`Blanc/Lift/Weth9/Live.lean:789`), `Blanc.Lift.Weth9.weth9_decimals_gas_exact` (`Blanc/Lift/Weth9/Live.lean:811`) | 2,534 / 534 (`balanceOf` cold / warm), 2,444 / 444 (`decimals`) [`Blanc.Lift.Weth9.balanceOfGas9_eq` (`Blanc/Lift/Weth9/Live.lean:604`)] | ENV: gas |
| Frame | `approve` writes `allowance[caller][guy] := wad` and returns `true` | `Blanc.Lift.Weth9.weth9_approve_live` (`Blanc/Lift/Weth9/LiveWriters.lean:50`) | `approveGas = 2320 + sstoreCost` [`Blanc.Lift.Weth9.approveGas` (`Blanc/Lift/Weth9/LiveApprove.lean:209`)]; worked case: cold, never-written slot, nonzero `wad` costs **24,420** [`Blanc.Lift.Weth9.approveGas_cold_set` (`Blanc/Lift/Weth9/LiveWriters.lean:881`)]; needs `380 ≤ G` | none |
| Frame | `deposit()` and the payable fallback | `Blanc.Lift.Weth9.weth9_deposit_live` (`Blanc/Lift/Weth9/LiveWriters.lean:84`), `Blanc.Lift.Weth9.weth9_fallback_short_live` (`Blanc/Lift/Weth9/LiveWriters.lean:109`), `Blanc.Lift.Weth9.weth9_fallback_live` (`Blanc/Lift/Weth9/LiveWriters.lean:132`) | `depositGas = 1874 + depositLoad + depositStore` [`Blanc.Lift.Weth9.depositGas` (`Blanc/Lift/Weth9/LiveDeposit.lean:262`)]; the fallback adds 1631 / 1896; needs `844 ≤ G` | none |
| Frame | `transfer` | `Blanc.Lift.Weth9.weth9_transfer_live` (`Blanc/Lift/Weth9/LiveWriters.lean:257`) | `transferGas = xferGasSelf + 470` [`Blanc.Lift.Weth9.transferGas` (`Blanc/Lift/Weth9/LiveTransfer.lean:649`)]; needs `353 ≤ G` | ENV: `wad ≤ balanceOf[caller]` |
| Frame | `transferFrom`, all three allowance cases | `Blanc.Lift.Weth9.weth9_transferFrom_live` (`Blanc/Lift/Weth9/LiveWriters.lean:616`) | `transferFromGas = xferGas{Self,Max,Allow} + 340` [`Blanc.Lift.Weth9.transferFromGas` (`Blanc/Lift/Weth9/LiveWriters.lean:609`)]; needs `377 ≤ G` | a storage effect exists (`xferStorStep`) |
| Frame | `withdraw(wad)` to an EOA, every `wad` (0 included) | `Blanc.Lift.Weth9.weth9_withdraw_any_live` (`Blanc/Lift/Weth9/LiveWriters.lean:759`); nonzero `wad`: `Blanc.Lift.Weth9.weth9_withdraw_live` (`Blanc/Lift/Weth9/LiveWriters.lean:331`) | `withdrawGas = 2040 + sload + sload + sstore + callNet` [`Blanc.Lift.Weth9.withdrawGas` (`Blanc/Lift/Weth9/LiveWithdraw.lean:443`)]; `wad = 0`: `Blanc.Lift.Weth9.withdrawZeroGas` (`Blanc/Lift/Weth9/LiveWithdraw.lean:705`); needs `811 ≤ G` | ENV: the caller has no code, is not a precompile, depth ≠ 0, and the contract holds the ETH; the contract is `State.Protected` (nonzero nonce or code) and the caller is `State.Protected` or its credit does not wrap (`B256.Nof` of its balance and `wad`) |
| Frame | `withdraw` to a **contract** | `Blanc.Lift.Weth9.weth9_withdraw_send_live` (`Blanc/Lift/Weth9/LiveWriters.lean:818`) | `Blanc.Lift.Weth9.withdrawSendPre` (`Blanc/Lift/Weth9/LiveWriters.lean:811`); ends with `r − 1489` | **`SendOk` callee premise** [`Blanc.Lift.Weth9.SendOk` (`Blanc/Lift/Weth9/LiveWriters.lean:799`)]: the CALL succeeds, leaves at least 1489 gas, and changes no contract storage |
| Model | Any writer the model accepts at the extended footprint realises the model's next ledger, gas-exact | `Blanc.Lift.Weth9.weth9_approve_model_live` (`Blanc/Lift/Weth9/LiveModel.lean:52`), `Blanc.Lift.Weth9.weth9_deposit_model_live` (`Blanc/Lift/Weth9/LiveModel.lean:72`), `Blanc.Lift.Weth9.weth9_transfer_model_live` (`Blanc/Lift/Weth9/LiveModel.lean:90`), `Blanc.Lift.Weth9.weth9_transferFrom_model_live` (`Blanc/Lift/Weth9/LiveModel.lean:117`), `Blanc.Lift.Weth9.weth9_withdraw_model_live` (`Blanc/Lift/Weth9/LiveModel.lean:199`) | as the frame rows | INIT `FootInv K`; HASH-T `KeysFresh K (call keys)`; model acceptance; for `withdraw`, ENV: the contract is `State.Protected` |
| Reachable state | After any configured history, a tracked holder can `withdraw(wad)` to an EOA, `deposit()`, or `transfer` | `Blanc.Lift.Weth9.weth9_history_withdraw_live` (`Blanc/Lift/Weth9/LiveHistory.lean:75`), `Blanc.Lift.Weth9.weth9_history_deposit_live` (`Blanc/Lift/Weth9/LiveHistory.lean:154`), `Blanc.Lift.Weth9.weth9_history_transfer_live` (`Blanc/Lift/Weth9/LiveHistory.lean:182`) | `withdrawAnyGas` / `depositGas` / `transferGas` | the history premises (CODE, ARITH, INIT, HASH-T); a fresh frame at `pre.state = future.state`; the holder in the tracked universe. **No history-level `approve` or `transferFrom` liveness** |
| Transaction | A type-2 `withdraw(wad)` transaction is admitted by `processTransaction`, debits the holder's slot, moves `wad` ETH, and uses exact gas | `Blanc.Lift.Weth9.weth9_tx_withdraw` (`Blanc/Lift/Weth9/LiveTx.lean:710`); at the state after the last block of any configured history, a block boundary, `Blanc.Lift.Weth9.weth9_history_tx_withdraw` (`Blanc/Lift/Weth9/LiveTx.lean:835`); at any transaction position inside the next block, the mid-block row below | intrinsic `21000 + 4·calldataTokens` [`Blanc.Lift.Weth9.withdrawIntrinsicGas` (`Blanc/Lift/Weth9/LiveTx.lean:47`)]; frame **13,940** (`wad ≠ 0`) or **4,440** (`wad = 0`) [`Blanc.Lift.Weth9.withdrawFrameGas` (`Blanc/Lift/Weth9/LiveTx.lean:52`)]; refund 4,800 iff a nonzero `wad` empties the balance [`Blanc.Lift.Weth9.withdrawRefund` (`Blanc/Lift/Weth9/LiveTx.lean:57`)]; `gasUsed = intrinsic + frame − refund` [`Blanc.Lift.Weth9.withdrawGasUsed` (`Blanc/Lift/Weth9/LiveTx.lean:59`)] | the signature-recovery premise; a sender EOA with nonce and funds; `tx.gas ≥ intrinsic + frame + 811` and `≤ 2^24` (EIP-7825); block room; coinbase ∉ {E, ca}, and `State.Protected` or without storage; `ca` not among the block environment's created accounts; `FootInv` at the block state; the holder tracked and `wad ≤` its balance |
| Transaction, inside a block | The footprint invariant holds at every transaction position of a configured block, not only at its boundaries: given a configured history `history` ending at a block boundary and the next configured block `block`, after that block's two opening system calls and any prefix of its retained decoded transactions (a take/drop split `cut` of the retained transaction trace, of any length from 0 to the full list), the contract still has its code, `SumNof` holds at the cut's state, and `FootInv` holds there over the checkpoint's tracked keys extended by the uniform five-key sets (`frameKeys`) of the raw frames at the contract in the prior history, the opening calls and the prefix. The next transaction at that position, when it is a type-2 `withdraw(wad)` to an EOA holder, is processed exactly as in the row above (same `withdrawGasUsed` accounting, same storage, nonce and ether conclusions at the cut's state), is the very transaction the block's own retained trace processes next, and leaves the rest of that trace available from the world it returns | `Blanc.Lift.Weth9.weth9_prefix_footprint_universe` (`Blanc/Lift/Weth9/FootPrefix.lean:24`); `Blanc.Lift.Weth9.weth9_prefix_tx_withdraw` (`Blanc/Lift/Weth9/PrefixTx.lean:62`); the key universe `Blanc.Lift.Weth9.prefixTouchedKeys` (`Blanc/Lift/Weth9/FootPrefix.lean:13`) | as the row above, at the cut's state | CODE and `SumNof` of the checkpoint; INIT `FootInv K₀` of the checkpoint (no invariant, code fact or bound is assumed at the cut); **HASH-T** one trace-local premise `KeysFresh K₀ (prefixTouchedKeys …)` over the prior history's keys, the opening calls' raw keys and the raw keys of the prefix's frames (rolled-back frames included); `n ≤` the number of decoded transactions. `weth9_prefix_tx_withdraw` adds the next-head premise `block.bodyTrace.decodedTxs.putIndex.drop n = (index, tx) :: rest` (the genuine indexed head, so the index is the transaction's own) and the premises of the row above stated at the cut's state, except that the installed code, the covered fork, `FootInv` and `ca`'s absence from the created accounts at the cut are derived instead of assumed and the holder must lie in the extended key universe `Key.extend K₀ (prefixTouchedKeys …)`. WETH9 only; the footprint result covers any prefix, the next-transaction result only a type-2 `withdraw` |

**Deployment / INIT**

| Claim | Theorem | Kind | Premises |
|---|---|---|---|
| **The actual creation transaction:** in its retained block 4,719,568, the recorded creation transaction installs WETH9's runtime at its address and leaves exactly the constructor's `name`/`symbol`/`decimals` storage `Blanc.Lift.Weth9.Creation.deployedStor` (`Blanc/Lift/Weth9/Creation/Deploy.lean:30`), every nonzero word of which is in slots {0, 1, 2} [`Blanc.Lift.Weth9.Creation.deployedStor_metadata` (`Blanc/Lift/Weth9/Creation/Deploy.lean:33`)] | `Blanc.Composition.LiveUsdcWeth9B26213219.weth9_deployment` (`Blanc/Composition/LiveUsdcWeth9B26213219Headlines.lean:40`), with conclusion `Blanc.Composition.LiveUsdcWeth9B26213219.WethDeployed` (`Blanc/Composition/LiveUsdcWeth9B26213219Headlines.lean:34`) | deploy / transaction | DEPLOYMENT `Blanc.Composition.LiveUsdcWeth9B26213219.WethDeploymentTo` (`Blanc/Composition/LiveUsdcWeth9B26213219History.lean:28`) (its block, creation transaction and history fields) |
| That storage satisfies the footprint INIT with the empty tracked set, for every ETH balance | `Blanc.Lift.Weth9.FootInv.deployed` (`Blanc/Lift/Weth9/Footprint.lean:211`) (metadata-only storage implies `FootInv ∅`) | deploy / INIT | none |
| Empty storage satisfies `StateInv` | `Blanc.Lift.Weth9.weth9_init_stateInv` (`Blanc/Lift/Weth9/Init.lean:42`) | satisfiability | none |

**Closed instance of the transaction theorem**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| In a synthetic configured BPO2 world, one connected execution, proved by applying `weth9_history_tx_withdraw` with every premise discharged: the recorded creation input, run as a CREATE message from the recorded deployer at nonce 446, installs the certified 3,124-byte runtime at the CREATE address with the constructor's `name`/`symbol`/`decimals` storage; a valid configured block, the history's single step after the checkpoint, commits a signed type-2 `deposit` of 1 wei by a funded holder; and at the history's terminal state a concrete signed type-2 `withdraw(1)` by that holder is admitted by `processTransaction`. The holder's WETH9 balance slot goes from 1 to 0, no other account's storage changes, the contract's ether goes from 1 wei to 0, the holder's nonce becomes 2, and the transaction uses 30,344 gas (intrinsic 21,204 plus frame 13,940 minus the 4,800 clearing refund) | `Blanc.Lift.Weth9.ClosedInstance.weth9_closed_exit_instance` (`Blanc/Lift/Weth9/ClosedExit.lean:69`), whose conclusion `∃ st bout, ClosedExitWitness st bout` is packaged as `Blanc.Lift.Weth9.ClosedInstance.ClosedExitWitness` (`Blanc/Lift/Weth9/ClosedExit.lean:39`); the deployment facts are `Blanc.Lift.Weth9.ClosedInstance.DeploymentFacts` (`Blanc/Lift/Weth9/ClosedDeployment.lean:14`) and `Blanc.Lift.Weth9.ClosedInstance.deployment_facts` (`Blanc/Lift/Weth9/ClosedDeployment.lean:31`); the funded world and the system-contract code are `Blanc.Lift.Weth9.ClosedInstance.initialWorld` (`Blanc/Lift/Weth9/ClosedWorld.lean:28`) and `Blanc.Lift.Weth9.ClosedInstance.systemCode` (`Blanc/Lift/Weth9/ClosedWorld.lean:17`); the chain configuration is `Blanc.Lift.Weth9.ClosedInstance.config` (`Blanc/Lift/Weth9/ClosedBlockData.lean:14`) | History and transaction / closed witness | none (closed): no hypotheses; every premise of `weth9_history_tx_withdraw` is discharged inside the instance, including signature recovery of the withdrawal (and, for building the history, of the deposit), which is computed in the kernel | Satisfiability of the theorem's premises in the model, not a statement about the chain. The world is synthetic: finite funding (1,000,000 wei at the holder, 1 wei at the recorded deployer), chain id 1, BPO2 active from the checkpoint (time 0), and a STOP program at each of the four system-contract addresses instead of the canonical system-contract code. Not historical inclusion of the deployment or of the transactions; not live WETH9 storage; the withdrawal is evaluated at the history's terminal state and is not placed inside a valid successor block. The deployment is a message-level execution that leaves the deployer's nonce at 446 |

**Fork coverage.** The history and liveness theorems assume or derive
`CoveredFork`; deployment is stated for every covered fork by the `_covered`
forms; the transaction theorem assumes `CoveredFork benv.stat.fork`.

**Non-claims.** Holder-level `balanceOf` sums beyond tracked keys;
redeemability by third parties; authorization; that `decimals` returns the
constant 18 (it returns storage); static frames' writers; rolled-back frames'
effects (in the committed list); Beacon-style authenticated history. The mid-block footprint result covers WETH9 and any retained prefix of a
configured block's transactions; the next-transaction result covers only a type-2
`withdraw`. Neither covers another contract or a position after the block's
withdrawals or request calls (a cut of full length ends before them). The
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
| After any configured history, storage is the accumulator of the initial history followed by exactly the deposits whose frames were committed (rollback-filtered by settlement), in order. **The mainnet-satisfiable form** | `Blanc.Lift.BeaconDeposit.configuredHistory_solInv_sys` (`Blanc/Lift/BeaconDeposit/BeaconEnv.lean:139`); base form `Blanc.Lift.BeaconDeposit.configuredHistory_solInv` (`Blanc/Lift/BeaconDeposit/CommittedHistory.lean:73`) | History / safety, exact extraction | CODE `installed`; INIT `SolInv … initialHistory`; ENV (trace-local, finite): `SystemCodeInstalled checkpoint` (canonical bytes at the four system addresses), `NoAuthorityAt` and no CREATE frame at those four addresses and at `0x02`, `getCode 2 = empty` at the checkpoint. **No hash premise.** The calldata bound, system exclusion [`Blanc.Lift.BeaconDeposit.system_of_installed` (`Blanc/Lift/BeaconDeposit/BeaconEnv.lean:121`), `Blanc.ExecutionTrace.ConfiguredHistoryTrace.systemFrames_of_installed` (`Blanc/ExecutionTraceSystemCode.lean:274`)], `0x02` warmth and no-delegation are derived | the `0x02` warmth is derived from EIP-2929 pre-warming, preserved across rollback |
| **From the actual deployment block:** over the whole retained history from the deposit contract's deployment block 11,052,984 to a later modern block, the count word is the number of committed deposits, as a number, and the root computed from the stored branch and count words is the reference root of exactly those deposits, in order. Intermediate: at that block the storage satisfies `SolInv` for exactly the committed deposits of the whole span | `Blanc.Lift.BeaconDeposit.beacon_deposits` (`Blanc/Lift/BeaconDeposit/HistDeployment.lean:166`), with conclusion `Blanc.Lift.BeaconDeposit.DepositHistory` (`Blanc/Lift/BeaconDeposit/HistDeployment.lean:157`); via `Blanc.Lift.BeaconDeposit.BeaconDeploymentTo.solInv` (`Blanc/Lift/BeaconDeposit/HistDeployment.lean:122`), from the whole-span seam composition `Blanc.Lift.BeaconDeposit.historicalSeam_wholeSpan_solInv` (`Blanc/Lift/BeaconDeposit/HistoricalSeam.lean:256`); the count word by `Blanc.Lift.BeaconDeposit.solCount_eq_of_solInv` (`Blanc/Lift/BeaconDeposit/Views.lean:86`); reference correctness `Blanc.BeaconDeposit.root_correct` (`Blanc/BeaconDepositCorrectness.lean:284`) | Deployment-rooted history / safety | DEPLOYMENT `Blanc.Lift.BeaconDeposit.BeaconDeploymentTo` (`Blanc/Lift/BeaconDeposit/HistDeployment.lean:40`): the retained Muir Glacier deployment block whose body slot 2 decodes to the recorded creation transaction, with its successful receipt and no log at the deposit address; the configured histories through the adopted Shanghai, Cancun and Prague seam anchors to the modern block; empty `0x02` code after the deployment block; no frame without a code address targeting `0x02`, and over the modern span no authorization recovering to a system contract or `0x02`. No INIT, CODE or `SystemCodeInstalled` premise | INIT is the actual deployment (the empty deposit history at the deployment boundary is derived), not an arbitrary initial history |
| `get_deposit_count` and `get_deposit_root` on the final state succeed with those outputs, at exact gas | `Blanc.Lift.BeaconDeposit.configuredHistory_count_view` (`Blanc/Lift/BeaconDeposit/CommittedHistory.lean:92`), `Blanc.Lift.BeaconDeposit.configuredHistory_root_view` (`Blanc/Lift/BeaconDeposit/CommittedHistory.lean:119`) | History and frame / live | **per-frame `beaconEntry`** (ENV: `0x02` warm, undelegated), depth, gas | there is no `_sys` form of the views |
| A successful frame is exactly the model step (decode, accumulator, event, storage shape); other selectors change no storage or logs | `Blanc.Lift.BeaconDeposit.deposit_frame_refines` (`Blanc/Lift/BeaconDeposit/Safe.lean:333`) | Frame / safety | CODE; ENV `ShaReady`; INIT-shaped `SolInv pre` | |

**Liveness.** Frame: `Blanc.Lift.BeaconDeposit.deposit_exec_solInv` (`Blanc/Lift/BeaconDeposit/DepositExec.lean:73`). A model-accepted deposit executes
at exactly `G + depositGasOf origLive origCount`, with `depositGasOf = 656 + bodyGasOf` and `bodyGasOf =
14551 + sloadCost(count) + countStoreCostOf origCount + bodyInsertGasOf origLive`, where `origLive` and `origCount`
are the entry machine's original reads `base.getOrigStorVal` of the stored branch slot and of the count slot (the
price Jaune charges: `0` at an owner created in the same transaction; Option A, decision
blanc-repin-os-optionA-delegation-20261012) [`Blanc.Lift.BeaconDeposit.depositGasOf` (`Blanc/Lift/BeaconDeposit/DepositExec.lean:29`),
`Blanc.Lift.BeaconDeposit.bodyGasOf` (`Blanc/Lift/BeaconDeposit/BodySpec.lean:225`)], appending the model node and event. `get_deposit_count` costs
1,514 with its count slot warm [`Blanc.Lift.BeaconDeposit.get_deposit_count_warm_exec` (`Blanc/Lift/BeaconDeposit/Views.lean:20`)] (no cold-slot cost is stated); `supportsInterface(id)` succeeds at exact gas `erc165Gas` and returns true exactly when `id` is the ERC-165 or the deposit interface id [`Blanc.Lift.BeaconDeposit.supportsInterface_exec` (`Blanc/Lift/BeaconDeposit/Views.lean:38`)]; `get_deposit_root` costs `Blanc.Lift.BeaconDeposit.rootViewGas` (`Blanc/Lift/BeaconDeposit/RootView.lean:607`). Reachable
state: `Blanc.Lift.BeaconDeposit.configuredHistory_deposit_live` (`Blanc/Lift/BeaconDeposit/Liveness.lean:24`) says that after any configured history a
model-accepted deposit executes at exact gas and appends exactly the new node
(premises: per-frame `beaconEntry`, `DepositDecodable`, `ShaReady`, sentry and
bound side conditions, all priced from the same machine original reads). **There is no transaction-level Beacon liveness**: a
deposit carries value, which needs a value-carrying envelope.

**Deployment / INIT.** `Blanc.Lift.BeaconDeposit.Creation.beacon_deploy_covered` (`Blanc/Lift/BeaconDeposit/Creation/Deploy.lean:151`), for every covered fork
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
| **History:** the final storage abstracts the model state reached by `Curve3Crv.step` over **exactly the settlement-committed writer invocations** at the contract, in trace order, and that model state is conserving (`totalSupply = Σ balances`) | `Blanc.Lift.Curve3Crv.c3crv_history_committed_derived` (`Blanc/Lift/Curve3Crv/CommittedHistory.lean:230`); base form `Blanc.Lift.Curve3Crv.c3crv_history_committed` (`Blanc/Lift/Curve3Crv/CommittedHistory.lean:191`) (takes the calldata bound as a hypothesis) | History / safety, exact extraction | CODE; INIT `VyInv … initialKeys`; **HASH-T** `FreshKeys initialKeys (historyTouchedKeys ca trace)` (rolled-back frames included); the calldata bound is derived | No static filter: `Blanc.Lift.Curve3Crv.c3crv_writer_nonstatic` (`Blanc/Lift/Curve3Crv/Safe.lean:283`) proves a writer cannot succeed in a static frame |
| **Conservation from the actual deployment:** at any checkpoint after the 3Crv token's deployment, the supply word equals the sum of the balance words of every holder whose balance key the history's raw token frames touched. Intermediate: **Deployment-rooted history:** from the recorded creation transaction of the 3Crv token, in its retained mainnet block 10,809,467, to a later checkpoint: the runtime is still installed, and the final storage abstracts the model state reached by `Curve3Crv.step` from the constructor's state (minter the deployer, supply and balances zero) over **exactly the settlement-committed writer invocations** at the contract after the creation, in trace order, each accepted with the owner word that the frame's own `owner()` static call answered under the frame's actual delegation rules; and that model state is conserving | `Blanc.Lift.Curve3Crv.c3crv_conserved` (`Blanc/Lift/Curve3Crv/Headline.lean:118`), with conclusion `Blanc.Lift.Curve3Crv.SupplyConserved` (`Blanc/Lift/Curve3Crv/Headline.lean:48`); via the frame-by-frame replay `Blanc.Lift.Curve3Crv.C3crvDeploymentTo.frames` (`Blanc/Lift/Curve3Crv/HistDeployment.lean:105`), over the record `Blanc.Lift.Curve3Crv.C3crvDeploymentTo` (`Blanc/Lift/Curve3Crv/HistDeployment.lean:37`) | Deployment-rooted history / safety, exact extraction | DEPLOYMENT: a retained configured `HistFork` mainnet block with header number 10,809,467 and timestamp of 1,599,414,946, whose transaction at index 76 is the recorded signed creation transaction (hash 0xa7d90e46...053694f8) and whose receipt at that index reports success; HISTORY: the retained configured `HistFork` history from that block's end to the checkpoint; **HASH-T** `FreshKeys` over the keys the raw token frames of the rest of that block and of that history touch. No installed-code premise, no INIT premise, no gas premise | INIT is the actual deployment, not an arbitrary `VyInv` checkpoint (the checkpoint form is the row above). Funds, gas, nonce, sender code, target freshness, the installed runtime, the deployed storage and the initial `VyInv` are derived (`Blanc.Lift.Curve3Crv.C3crvDeploymentTo.created` (`Blanc/Lift/Curve3Crv/HistDeployment.lean:78`)). Owner evidence is `Blanc.Lift.Curve3Crv.OwnerAnswerH` (`Blanc/Lift/Curve3Crv/SafeBodies.lean:41`), which on a covered fork is `OwnerAnswer`. Rooted in the retained block, not in a header, block hash or state root |
| **The creation transaction in its block:** in a retained `HistFork` mainnet block at those coordinates, a transaction cut whose transaction is the recorded signed CREATE and whose receipt reports success leaves, right after it, the certified 3Crv runtime at the token address with storage `deployedStor deployer`; the block's log list gains exactly the creation log and its gas used grows by exactly 678,343 (intrinsic 97,992 + constructor 125,151 + code deposit 455,200) | `Blanc.Lift.Curve3Crv.Creation.HistoricalTx.actual_block_cut` (`Blanc/Lift/Curve3Crv/Creation/HistoricalTxTrace.lean:229`) | Block / transaction, deployment | DEPLOYMENT as in the row above (block, coordinates, transaction at the cut, receipt success); no hash, funds, gas or nonce premise | The recorded raw bytes hash to the observed transaction hash, decode strictly to the transaction used here, and recover the deployer [`Blanc.Lift.Curve3Crv.Creation.HistoricalTx.raw_binding` (`Blanc/Lift/Curve3Crv/Creation/HistoricalTxRecover.lean:44`), `Blanc.Lift.Curve3Crv.Creation.HistoricalTx.recoveredSender` (`Blanc/Lift/Curve3Crv/Creation/HistoricalTxRecover.lean:37`)]. The fork (Muir Glacier) and zero base fee are derived from the header; the pre-EIP-155 signature (v = 28) is recovered in the kernel; the receipt status is used only to exclude a CREATE collision. The gas figure is a theorem (`Blanc.Lift.Curve3Crv.Creation.HistoricalTx.muirGasUsed_eq_limit` (`Blanc/Lift/Curve3Crv/Creation/HistoricalTxSettle.lean:50`)), not an observation |
| A successful frame from a fresh entry is exactly the model step: writers (events, storage abstraction, owner answer for `set_name`, and the return bytes: the ABI word `true` for `transfer`, `transferFrom`, `approve`, `mint` and `burnFrom`, empty for `setMinter` and `setName`), **and views (storage and logs unchanged, return bytes equal the model output)** | `Blanc.Lift.Curve3Crv.c3crv_frame_refines` (`Blanc/Lift/Curve3Crv/Safe.lean:291`); raw form `Blanc.Lift.Curve3Crv.c3crv_frame_refines_raw` (`Blanc/Lift/Curve3Crv/Safe.lean:193`) (output stated relative to the entry output) | Frame / safety | CODE; covered fork; calldata bound below 2^256 (a frame-level hypothesis); **fresh entry as explicit premises** `pre.stack = []`, `pre.memory = Mem.empty`, `pre.output = []`; INIT-shaped `VyInv pre`; HASH-T `FreshKeys` (call keys); a successful `Exec 0 sevm pre (.ok post)` | Every successful selector is covered (misses and short calldata have no successful run). The fresh-entry facts are hypotheses here, not derived from a `Frame.enter` equation |
| Token-model properties: `step` preserves conservation; the initial state is conserving; supply and minter change only by the minter; non-minter `transferFrom` spends allowance even at the maximum value, while the minter retains allowances; zero-first approve; authorized allowance and balance changes | `Blanc.Curve3Crv.step_conserved` (`Blanc/Curve3Crv/Properties.lean:160`), `Blanc.Curve3Crv.init_conserved` (`Blanc/Curve3Crv/Properties.lean:165`), `Blanc.Curve3Crv.supply_change_by_minter` (`Blanc/Curve3Crv/Properties.lean:182`), `Blanc.Curve3Crv.minter_change_by_minter` (`Blanc/Curve3Crv/Properties.lean:201`), `Blanc.Curve3Crv.transferFrom_spends_allowance` (`Blanc/Curve3Crv/Properties.lean:223`), `Blanc.Curve3Crv.transferFrom_spends_max_allowance` (`Blanc/Curve3Crv/Properties.lean:233`), `Blanc.Curve3Crv.transferFrom_minter_keeps_allowances` (`Blanc/Curve3Crv/Properties.lean:249`), `Blanc.Curve3Crv.approve_zero_first` (`Blanc/Curve3Crv/Properties.lean:258`), `Blanc.Curve3Crv.allowance_change_authorized` (`Blanc/Curve3Crv/Properties.lean:267`), `Blanc.Curve3Crv.balance_debit_authorized` (`Blanc/Curve3Crv/Properties.lean:307`) | Model / safety | the model only | bridged to the bytes by the frame row above and the history rows, and four of them lifted to the bytes by the row below |
| **The policy at the bytes, from the actual deployment:** every settlement-committed writer frame at the token after the deployment obeys four facts over its own opening and closing storage words: only the address in the minter word moves the supply word, and only by `mint` or `burnFrom`; only that address moves the minter word; a `transferFrom` by any other caller spends exactly its value of the caller's allowance word, which covers it; and the allowance word of a tracked pair (one the history's raw token frames touched) moves only by its owner's `approve` of that spender or that spender's `transferFrom` from that owner | `Blanc.Lift.Curve3Crv.c3crv_policy` (`Blanc/Lift/Curve3Crv/Headline.lean:146`), with conclusion `Blanc.Lift.Curve3Crv.C3crvFramePolicy` (`Blanc/Lift/Curve3Crv/Headline.lean:89`) | Deployment-rooted history / safety, per frame | as the deployment-rooted row above (the record only) | Committed writer frames only: view and unknown-selector frames are not in the statement (the frame refinement shows they change no storage). The allowance fact covers tracked pairs only, since an untracked pair's slot may coincide with a live key's. Lifts `supply_change_by_minter`, `minter_change_by_minter`, `transferFrom_spends_allowance` and `allowance_change_authorized`; the other model properties stay at the model level |

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

**Deployment / INIT.** `Blanc.Lift.Curve3Crv.Creation.curve_deploy_covered` (`Blanc/Lift/Curve3Crv/Creation/Deploy.lean:304`), for every covered fork
`f`: a nonce-42 CREATE from the recorded deployer installs the runtime and
leaves `deployedStor deployer` with `VyInv … (curveDeployedState deployer) (fun _
=> False)`. The recorded deployment therefore satisfies the history theorem's
checkpoint predicate (name, symbol, decimals 18, supply 0, minter = deployer)
with no hash premise; the constructor's write of 0 at `keccak(3‖caller)` is
discharged by kernel evaluation. General form `Blanc.Lift.Curve3Crv.Creation.curve_create` (`Blanc/Lift/Curve3Crv/Creation/Deploy.lean:207`) (storage
`deployedStor`). `Blanc.Lift.Curve3Crv.curve_init_vyInv` (`Blanc/Lift/Curve3Crv/Init.lean:37`) is a satisfiability instance.
The recorded creation transaction is also shown inside its retained block:
`Blanc.Lift.Curve3Crv.Creation.HistoricalTx.actual_block_cut` (`Blanc/Lift/Curve3Crv/Creation/HistoricalTxTrace.lean:229`)
derives the installed runtime, the storage `deployedStor deployer`, the creation log and the exact gas used from the
recorded Muir Glacier transaction and the block's success receipt, with no hash premise, and
`Blanc.Lift.Curve3Crv.C3crvDeploymentTo.created` (`Blanc/Lift/Curve3Crv/HistDeployment.lean:78`) states the resulting
`VyInv` at `curveDeployedState deployer`. `Blanc.Lift.Curve3Crv.C3crvDeploymentTo.frames` (`Blanc/Lift/Curve3Crv/HistDeployment.lean:105`) carries it to a checkpoint.

**Fork coverage.** History and liveness on covered forks;
`curve_deploy_covered` quantifies over covered forks. The deployment-rooted row and the creation-transaction row range over `HistFork` (Byzantium through BPO2; Amsterdam is not covered).

**Non-claims.** Log and return bytes at the *history* level (only at frame
level); replay equal to the *raw* trace's writer sequence (rolled-back frames
are, by design, not in it); a closed cost formula; `set_name` without the
owner-call premise. That the retained block and history are the chain's own, or that the header coordinates bind to a block hash or state root.

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
| **From the actual creation transaction (finite):** right after the CircuitBreaker's actual creation transaction, its address holds the certified runtime and its storage satisfies `RegistryOn [] probes` for every list of canonical probes that passes the decidable apart check against the constructor's two written slots | `Blanc.Lift.LidoCircuitBreakerDeployed.lido_deployment_finite_init` (`Blanc/Lift/LidoCircuitBreakerDeployed/DeploymentHistory.lean:151`), through `Blanc.Lift.LidoCircuitBreakerDeployed.registryOn_deployedStor` (`Blanc/Lift/LidoCircuitBreakerDeployed/FiniteInit.lean:27`) | Deployment-rooted / INIT (finite) | DEPLOYMENT `Blanc.Lift.LidoCircuitBreakerDeployed.Creation.DeploymentCut` (`Blanc/Lift/LidoCircuitBreakerDeployed/Creation/Transaction.lean:41`): one-block observations of the creation transaction in block 24,993,190 at index 1,219 (a creation with the certified input, the recorded deployer, nonce 0, zero value, at least 1,000,000 message gas) and its successful receipt, inside a configured covered-fork block (the configured-history premise); canonical probes; `checkApartOn solKey (registryQueries probes 0) [0, 1] = true` (decidable) | **No hash premise** and no `ForeignApart`. The installed code and the constructor's storage are derived from the transaction. A deployment fact, not a history statement |
| **The live registry at block 26,141,229 (finite):** any raw CircuitBreaker storage that agrees with the 107 storage words observed at block 26,141,229 satisfies `RegistryOn` for the live entries (the whole stored target array, 19 entries) at the 29 recorded probes | `Blanc.Lift.LidoCircuitBreakerDeployed.Live.lido_live_registryOn` (`Blanc/Lift/LidoCircuitBreakerDeployed/LiveRegistry.lean:78`), over the observed words `Blanc.Lift.LidoCircuitBreakerDeployed.Live.words` (`Blanc/Lift/LidoCircuitBreakerDeployed/LiveObservation.lean:16`), entries `Blanc.Lift.LidoCircuitBreakerDeployed.Live.entries` (`Blanc/Lift/LidoCircuitBreakerDeployed/LiveObservation.lean:127`) and probes `Blanc.Lift.LidoCircuitBreakerDeployed.Live.probes` (`Blanc/Lift/LidoCircuitBreakerDeployed/LiveObservation.lean:150`) | Observation / finite | one premise: the storage agrees with the observed words (a one-block storage observation, generated by `scripts/lido-circuit-breaker-live-registry.py` from three public JSON-RPC operators' identical answers; an unadopted candidate) | `checkRegistryOn` is decided by kernel evaluation on the observed words, and every raw slot it reads is among them. Nothing about an address outside the probes, about another block, or about how the storage was reached |
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
| **From the actual deployment:** after the CircuitBreaker's actual creation transaction and any configured covered-fork history after it, the Registry read from storage is consistent: the stored targets are distinct, a target has a nonzero pauser and a nonzero index exactly when it is stored, each stored target's index is its position plus one, each pauser's guard count is the number of stored targets it guards, and address 0 guards nothing. Intermediate: after any configured history there is a registry witness of the future storage: assignment and index agree with membership, counts equal assignments, pauser 0 has count 0, and live counts sum to the length word | `Blanc.Lift.LidoCircuitBreakerDeployed.lido_registry_consistent` (`Blanc/Lift/LidoCircuitBreakerDeployed/DeploymentHistory.lean:113`), with conclusion `Blanc.Lift.LidoCircuitBreakerDeployed.ConsistentRegistry` (`Blanc/Lift/LidoCircuitBreakerDeployed/RegistryObservers.lean:43`); via the state invariant at the future block `Blanc.Lift.LidoCircuitBreakerDeployed.LidoDeploymentTo.stateInv_future` (`Blanc/Lift/LidoCircuitBreakerDeployed/DeploymentHistory.lean:95`) | Deployment-rooted history / safety | DEPLOYMENT `Blanc.Lift.LidoCircuitBreakerDeployed.LidoDeploymentTo` (`Blanc/Lift/LidoCircuitBreakerDeployed/DeploymentHistory.lean:58`): the CircuitBreaker's creation transaction cut in its configured block 24,993,190 at index 1,219 (a creation with the certified input, the recorded deployer, nonce 0, zero value, at least 1,000,000 message gas and a successful receipt) and any configured covered-fork history after it; one **HASH-U** premise `Blanc.Lift.LidoCircuitBreakerDeployed.LidoSlotsApart` (`Blanc/Lift/LidoCircuitBreakerDeployed/SlotsApart.lean:34`) (Keccak is injective on the mapping slots of canonical addresses over the four mapping bases, and those slots miss the first 2^160 array cells and the fixed slots 0, 1 and 5). CODE, INIT and frame admission are derived (intermediate: CODE; INIT `RegistryZeroRaw`; ENTRY plus **HASH-U** `FrameAdmitted ca (lidoEntry lidoA)`) | Distinctness is new; the sum of the counts follows from the rest and is not stated; selector-insensitive |
| `registerPauser(t, 0)` from a real pc-0 entry removes `t` with the correct swap-and-pop repair (`L2Post`) | `Blanc.Lift.LidoCircuitBreakerDeployed.l2_registerPauser_zero` (`Blanc/Lift/LidoCircuitBreakerDeployed/L2Frame.lean:281`) | Frame / safety | CODE; fresh entry; **HASH-U** `EntryAt lidoA`; INIT-shaped `RegistryWitness` of the pre-storage | |
| **From the actual deployment:** every settlement-committed non-static frame at the CircuitBreaker whose calldata is `registerPauser(t, 0)` (including one re-entered from inside `pause`'s CALL) clears `t`'s pauser and index words and leaves the stored target array equal to the one at the frame's entry with `t` swap-and-popped out (unchanged when `t` was not stored). Intermediate: **The pre-storage witness is derived:** every settlement-committed non-static `registerPauser(t, 0)` frame (including one re-entered from inside `pause`'s CALL) has a witness of its entry storage and `L2Post` | `Blanc.Lift.LidoCircuitBreakerDeployed.lido_remove_repairs` (`Blanc/Lift/LidoCircuitBreakerDeployed/DeploymentHistory.lean:128`), with conclusion `Blanc.Lift.LidoCircuitBreakerDeployed.RemovalRepaired` (`Blanc/Lift/LidoCircuitBreakerDeployed/RegistryObservers.lean:64`); via the mid-history entry accounting `Blanc.ExecutionTrace.MidHistoryTraceIn.entryGood_settled` (`Blanc/ExecutionEntryAccountingMidHistory.lean:27`) | Deployment-rooted history / safety | DEPLOYMENT `Blanc.Lift.LidoCircuitBreakerDeployed.LidoDeploymentTo` (`Blanc/Lift/LidoCircuitBreakerDeployed/DeploymentHistory.lean:58`): the CircuitBreaker's creation transaction cut in its configured block 24,993,190 at index 1,219 (a creation with the certified input, the recorded deployer, nonce 0, zero value, at least 1,000,000 message gas and a successful receipt) and any configured covered-fork history after it; one **HASH-U** premise `Blanc.Lift.LidoCircuitBreakerDeployed.LidoSlotsApart` (`Blanc/Lift/LidoCircuitBreakerDeployed/SlotsApart.lean:34`) (Keccak is injective on the mapping slots of canonical addresses over the four mapping bases, and those slots miss the first 2^160 array cells and the fixed slots 0, 1 and 5). CODE, INIT and frame admission are derived; per-frame call shape only (intermediate: CODE via `StateInv` INIT; `FrameAdmitted ca (lidoEntry lidoA)` (HASH-U); per-frame call shape only. Uses the generic `Blanc.ExecutionTrace.MidHistoryTraceIn.entryGood_settled` (`Blanc/ExecutionEntryAccountingMidHistory.lean:27`), `Blanc.Lift.LidoCircuitBreakerDeployed.lido_spawnEntry` (`Blanc/Lift/LidoCircuitBreakerDeployed/Reentry.lean:445`) and `Blanc.Lift.reach_of_parentPrefix` (`Blanc/Lift/Cursor.lean:955`)) | States the whole array, more than `L2Post`; static committed frames and frames under a rolled-back ancestor are **not claimed** |

**Liveness.** None. There is **no Lido liveness claim of any level**, at
either tier.

**Deployment / INIT.** `Blanc.Lift.LidoCircuitBreakerDeployed.Creation.lido_deploy_covered` (`Blanc/Lift/LidoCircuitBreakerDeployed/Creation/Deploy.lean:196`), for every covered fork
`f`: a nonce-0 CREATE from the recorded deployer with 1,000,000 gas installs
the certified runtime and leaves storage exactly `deployedStor`
(`pauseDuration = 1814400`, `heartbeatInterval = 31536000`).
`Blanc.Lift.LidoCircuitBreakerDeployed.Creation.lido_deploy_init_covered` (`Blanc/Lift/LidoCircuitBreakerDeployed/Creation/Deploy.lean:210`) adds `RegistryZeroRaw` and
`lidoSpec.StateInv` **under `ForeignApart 0 0` and `ForeignApart 0 1`** (two
bounded hash premises: the constructor's slots 0 and 1 are off the registry's
raw slots). The finite tier above replaces those two premises by one decidable
check per probe list, for the finite observation `RegistryOn [] probes` in place
of `RegistryZeroRaw`. General forms `Blanc.Lift.LidoCircuitBreakerDeployed.Creation.lido_create` (`Blanc/Lift/LidoCircuitBreakerDeployed/Creation/Deploy.lean:75`),
`Blanc.Lift.LidoCircuitBreakerDeployed.Creation.lido_create_registryZeroRaw` (`Blanc/Lift/LidoCircuitBreakerDeployed/Creation/Deploy.lean:120`), `Blanc.Lift.LidoCircuitBreakerDeployed.Creation.lido_create_stateInv` (`Blanc/Lift/LidoCircuitBreakerDeployed/Creation/Deploy.lean:134`).
Satisfiability: `Blanc.Lift.LidoCircuitBreakerDeployed.registryZeroRaw_empty` (`Blanc/Lift/LidoCircuitBreakerDeployed/Init.lean:36`), `Blanc.Lift.LidoCircuitBreakerDeployed.lido_init_stateInv` (`Blanc/Lift/LidoCircuitBreakerDeployed/Init.lean:49`). The gas of the
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
| In any execution (any outcome, `Exec 0 …`), while an owner frame is inside one of the mutating guarded bodies and has not released, no descendant enters any guarded body for that owner | generic `Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_exclusion` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exclusion.lean:128`); instances `Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_exclusion_impl` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exclusion.lean:142`), `Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_exclusion_stethPool` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exclusion.lean:161`) | Message (all outcomes) / temporal exclusion | CODE (implementation or proxy bytes, `hP`, `hI`); ENV well-formed root `hroot`; **HASH-T** `HashAvoidIn` (executed Keccak digests differ from lock slot 0) || In a pc-0 frame running the 0x847e code (covered fork, `HashAvoid 0`), every node executes only `CALL` or `STATICCALL` among external calls and never `DELEGATECALL`, `CALLCODE`, `CREATE`, `CREATE2` or `SELFDESTRUCT` [`Blanc.Lift.VyperNonreentrantDeployed.Fixed.lock_no_forbidden` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/LockDominance.lean:44`)] |
| The same for a transaction's retained top-level execution, with `hroot` **derived** (`prepareMessage` builds the root from the debited world) | `Blanc.ExecutionTrace.TransactionTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:251`); message carriers `Blanc.ExecutionTrace.ProcessMessageTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:70`), `Blanc.ExecutionTrace.ProcessCreateMessageTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:116`), `Blanc.ExecutionTrace.MessageCallTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:180`) | Transaction / temporal exclusion | `hfork`, `hP`, `hI` on the opening state; `tx.auths = []` (EIP-7702 excluded); `HashAvoidIn` of the retained execution | |
| The same for every raw frame root of a configured history; pc 0 and the covered fork are derived | `Blanc.ExecutionTrace.ConfiguredHistoryTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:283`) [roots by `Blanc.ExecutionTrace.MessageCallTrace.rootEntry` (`Blanc/ExecutionTraceEntry.lean:58`)] | History / temporal exclusion | per retained execution `R`: `hP`, `hI`, `hroot`, `HashAvoidIn` (not derivable from the trace) | statement form `VplusExcludes` [`Blanc.Lift.VyperNonreentrantDeployed.Fixed.VplusExcludes` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:44`); `Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_excludes` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:50`)] |
| **Nonvacuity (proxy-free):** an actual Jaune execution of the deployed 0x847e runtime in which a mutating guarded body (`remove_liquidity`, body start 0x1bae) is active and spawns a STATICCALL (pc 0x337a) to a coin, whose read-only reentry into the guarded view `get_virtual_price()` **reverts at the lock check** and never reaches a guarded body. It carries the full antecedent of `vplus_exclusion_impl` and its conclusion | `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness.vplus_witness_covered` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness/Top.lean:251`) (quantified over `g` with `CoveredFork g`, Prague included); every derivation of the entered machine, under any covered fork: `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness.vplus_run_at` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness/Top.lean:82`) | Message / closed witness | none (closed) | Kernel-checked; every walk boundary matches an EELS Prague trace (the printer is untrusted). No KECCAK executes, so `HashAvoidIn` holds by "no hash executed" |
| **Nonvacuity (proxy instance, mutating reentry):** an execution entered through the 45-byte forwarder 0x21e2… (DELEGATECALL to 0x847e). `remove_liquidity` holds the lock and CALLs a synthetic receiver with 100 wei; the receiver calls back through the forwarder with `add_liquidity`'s selector (mutating, guarded); the comparator frame reverts at the lock check (pc 0x53 → 0x477e, no guarded body start); the receiver stops; the outer call **succeeds** and the pool balance goes from 1000 to 900 wei. This is a witness of `vplus_exclusion_stethPool` (the covered form carries that theorem's premises and antecedent, and the reentry conclusion `¬ lockL.Enters`) | `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.vplus_witness2_covered` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness2/Top.lean:227`) (every covered fork); every derivation: `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.vplus_run2_at` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness2/Top.lean:104`) | Message / closed witness | none (closed) | `HashAvoidIn` by digests: the one KECCAK256 leaves a digest different from slot 0 (control `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.hashControl_bites` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness2/Run.lean:413`); engine control `Blanc.Lift.NodeWalk.hashPol_bites` (`Blanc/Lift/NodeWalk.lean:1090`)) |
| **The headline:** on every covered fork, the eight setup messages, folded from the creator-only world, reach a world whose LP ledger is sound at 2000, and the exit message `remove_liquidity(200, [0, 0], receiver)` then settles to a world whose ledger is sound at 1800, with the receiver paid 100 wei and its guarded reentry refused at the shared lock: while the pool frame holds the lock it pays the receiver, and the receiver's guarded call back into the pool reverts without entering a guarded body. Intermediate, the detailed capstone: **Nonvacuity reachable from deployment and initialization (message level):** on every covered fork, nine messages run in sequence from a world holding only a funded, code-free creator, each from the previous settled world and each settling without error: the preserved 0x847e implementation creation input (placed at its registered address by a supplied CREATE target), a labelled synthetic EIP-1167 clone creation, `initialize` and `set_oracle(0, 0)` through the clone, synthetic token and receiver creations, `approve`, `add_liquidity([1000, 1000], 0)` with 1000 wei, then `remove_liquidity(200, [0, 0], receiver)`. Before the last message the LP ledger is sound over its single holder (`totalSupply = balanceOf[creator] = 2000`). While the pool frame holds the shared lock it sends the receiver 100 wei; the receiver calls the guarded, mutating `add_liquidity` through the clone; that pool frame reads the held lock and reverts without reaching a guarded body, and the receiver returns normally. The outer call commits: the receiver holds 100 wei and 100 tokens; supply and the creator's LP balance are 1800 | `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit.vplus_exit` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exit/Capstone.lean:153`) over the message fold `Blanc.Lift.runMessages` (`Blanc/Lift/RootMessages.lean:41`), with `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit.ReentryRefused` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exit/Capstone.lean:135`); via `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit.vplus_reachable_capstone` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exit/Capstone.lean:48`); the instantiation, with the receiver and forwarder code facts, `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit.vplus_reach_exit` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exit/Main.lean:60`) | Message / closed witness | none (closed) | The headline states the ledger outcome and the refused reentry; the capstone keeps every frame fact. `vplus_exclusion` instantiated for this execution with its fork, code, root and trace-local `HashAvoidIn` premises proved. Synthetic token, receiver and clone code; supplied CREATE targets; calls use chain id 1 and block time 1,700,000,000; no historical inclusion; no transaction admission |

**Fork coverage.** The exclusion assumes `CoveredFork`; both witnesses are
stated for every fork in Prague, Osaka, BPO1 and BPO2 (the Prague kernel facts
are transported by `Blanc/ForkUniform.lean`, `Blanc/Lift/NodeWalkFork.lean` and
`Blanc/Lift/WitnessFork.lean`; the runs execute no CLZ, read no blob price, and
enter no MODEXP or P256VERIFY). The reachable witness
`vplus_reachable_capstone` is likewise stated for every covered fork.

**Non-claims.** Unguarded functions; reentry after release; mutation while
only a view is running; pricing, LP economics, liveness; EIP-7702-delegated
roots (excluded from the transaction and message carriers); a validated
transaction reaching the witness state; historical prestates (the closed
witnesses' prestates are synthetic; the reachable witness's prestate is reached
by executed messages from a synthetic creator-only world; the reader and
receiver are synthetic).

### 5.6 Vyper V−: cross-function reentrancy corrupts the LP ledger

The vulnerable implementation 0x6326, called through its proxy.

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| **The headline:** on every covered fork, the seven setup messages, folded from the creator-only world, reach a world whose LP ledger is sound (supply and the attacker's LP balance both 2000), and the attack message then settles to a world whose ledger is broken (supply 1800, the attacker's LP balance 1906). Intermediate, the detailed capstone: **Violation reachable from deployment and initialization (message level):** on every covered fork, eight messages run in sequence from a world holding only a funded, code-free creator, each from the previous settled world and each settling without error: the preserved 0x6326 implementation creation input (placed at its registered address by a supplied CREATE target), a labelled synthetic clone creation, `initialize` through the clone (`A = 100`, fee 0), synthetic token and attacker creations, `approve`, `add_liquidity([1000, 1000], 0, attacker)` with 1000 wei, then the violating call. After the seventh message the LP ledger is sound over its single holder (`totalSupply = balanceOf[attacker] = 2000`) and all nonzero pool storage lies in a listed slot set. In the eighth, the creator calls the attacker contract, which calls `remove_liquidity(200, [0, 0], attacker)`; holding lock slot 2, the pool sends the attacker 100 wei; the callback calls `add_liquidity([100, 0], 0, attacker)` through the same clone, which takes lock slot 0 and succeeds. The message settles with `totalSupply = 1800 < 1906 = balanceOf[attacker]`, compared as natural numbers. The universal form states the same message and conclusions for every world agreeing with the reached world on the 14 storage slots and 6 accounts the violation reads (`Checkpoint`) | `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol.vminus_attack` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Reach/ViolFinal.lean:78`) over the message fold `Blanc.Lift.runMessages` (`Blanc/Lift/RootMessages.lean:41`), with `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol.LedgerBroken` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Reach/ViolFinal.lean:68`); via `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol.vminus_reachable_capstone` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Reach/ViolFinal.lean:39`); universal form `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol.vminus_reach_violation` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Reach/ViolFinal.lean:35`) | Message / closed witness (capstone); message / universal over `Checkpoint` worlds | none for the capstone; `Checkpoint W` for the universal form | The headline states the ledger outcome; the reentry frame chain is in `vminus_reach_violation`. Synthetic token, attacker and clone code; supplied CREATE targets; default block environment. **This row and the transaction row below concern different worlds (different proxy, attacker, sender and token addresses); neither implies or extends the other. The equal figures come from the same scenario amounts, not a shared state** |
| Message level: a successful message execution in which `remove_liquidity` holds lock slot 2, its ETH callback reenters `add_liquidity` (lock slot 0) through the proxy, and the final ledger has `totalSupply = 1800 < 1906 = balanceOf[attacker]`. The two guards are on different slots (bytes 6900-6911 versus 88-99) | `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top.vminus_witness` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Top.lean:155`); all covered forks `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top.vminus_witness_covered` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/ForkTop.lean:159`) | Message / closed witness | none (closed) | synthetic prestate (Section 7); stated for Prague, other covered forks by transport |
| **Transaction level, all covered forks:** conditional on block room, Jaune's `processTransaction` accepts a fixed signed type-2 transaction (zero fee and value, 16,043,200 gas, below 2^24, an access list of 19 addresses), and the returned world has `totalSupply = 1800 < 1906` in the pool | `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.vminus_txC_process` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/TxC/Envelope.lean:136`); closed message part `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.vminus_txC_message` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/TxC/Closed.lean:49`) (gas 15,822,837 left, refund 42,600, `accountsToDelete` empty) | Transaction / conditional witness | block room `hroom` | every other admission check, including signature recovery (`Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.txC_recoveredSender` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/TxCRecover.lean:99`)), is kernel-evaluated on the concrete transaction and block. From the synthetic prestate of Section 7 (proxy 0x9848…85c5 with seeded storage, attacker 0xaaaa…a2a2); not the deployment-reached world of the first row, and `vminus_reach_violation` does not cover it |

**Fork coverage.** `vminus_witness_covered`, `vminus_txC_message` and
`vminus_txC_process` quantify `g` with `CoveredFork g`. A Prague-only message
form, `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.vminus_tx_message` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Tx/Closed.lean:26`), carries 30,021,064 gas, which is above
the EIP-7825 cap from Osaka on and so is not a valid transaction there; cite
the `TxC` forms. The reachable forms `vminus_reachable_capstone` and
`vminus_reach_violation` also quantify over every covered fork.

**Non-claims.** For the closed message witness and the transaction rows: a
reachable or historical prestate. For every row: a historical prestate, and a
transaction reaching the reachable row's checkpoint; a real historical
attack; a signature-generic transaction (the signature, transaction hash,
index 0 and coinbase are fixed); the attacker model is synthetic (Section 7).

### 5.7 EIP-7002 withdrawal requests: actual-fee FIFO from submissions to block requests

The headline states `submissions history = emissions history ++ remainingQueue history`.
All three lists are direct observations: committed submission calls (including nested
calls), records in the blocks' actual withdrawal requests, and the live queue read from
final storage. Each record contains the caller, public key and amount. Equality preserves
order and multiplicity, without an existential replay witness or a separate last block.

**Safety, refinement and history**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| After canonical Cancun deployment and the admitted preactivation prefix, every committed submission in a configured modern history is, in order, either an emitted withdrawal record or an entry still in the final concrete queue: `submissions history = emissions history ++ remainingQueue history` | `Blanc.Lift.WithdrawalRequest.history_fifo` (`Blanc/Lift/WithdrawalRequest/HistoryFifo.lean:285`), with conclusion `Blanc.Lift.WithdrawalRequest.HistoryFifo` (`Blanc/Lift/WithdrawalRequest/HistoryFifo.lean:71`) | Deployment-rooted history / FIFO | DEPLOYMENT: the actual retained canonical CREATE transaction at the canonical address, identified by creation code, zero value, sufficient gas and noncollision. PREFIX: the remainder of that same deployment block and every later preactivation block actually select Cancun; their checked senders exclude SYSTEM_ADDRESS, no entered CREATE targets SYSTEM_ADDRESS, its code is empty at the committed post-deployment boundary, and canonical beacon code is present at later whole-block openings. MODERN SUFFIX: `CoveredFork` (Prague, Osaka, BPO1 or BPO2), canonical beacon/history-storage/consolidation code at the shared checkpoint, checked sender/authority exclusions and no entered CREATE at SYSTEM_ADDRESS. **Scope: at most 2^254 committed submission-payment occurrences in the modern history**. No independent INIT, EIP-7002 installation or checkpoint SYSTEM-emptiness premise | INIT and EIP-7002 code are derived from construction and the same prefix; checkpoint SYSTEM emptiness is transported from the earlier environmental condition, not established by deployment alone. The prefix contributes no committed submissions, so it adds no submission occurrences. The empty history is included. No claim beyond the submission cap. No hash or per-frame ENTRY premise; historical inclusion is not authenticated |
| **FIFO from the actual mainnet deployment:** for the retained configured trace of the observed deployment block 21,881,389 (the deployment is its transaction at position 0), the following Cancun blocks to the observed last pre-Prague checkpoint 22,431,083, and any configured history after that checkpoint, every committed submission is, in order, either a withdrawal record the blocks published or an entry still in the final stored queue | `Blanc.Lift.WithdrawalRequest.history_fifo_mainnet` (`Blanc/Lift/WithdrawalRequest/MainnetDeployment.lean:323`), with conclusion `Blanc.Lift.WithdrawalRequest.HistoryFifo` (`Blanc/Lift/WithdrawalRequest/HistoryFifo.lean:71`); via `Blanc.Lift.WithdrawalRequest.history_fifo` (`Blanc/Lift/WithdrawalRequest/HistoryFifo.lean:285`) | Deployment-rooted history / FIFO, at the actual deployment | Configured history: the deployment block, the blocks from it to the checkpoint (`HistFork`) and the history after the checkpoint are configured mainnet traces. One-block observations `Blanc.Lift.WithdrawalRequest.WithdrawalDeploymentObservation` (`Blanc/Lift/WithdrawalRequest/MainnetDeployment.lean:77`): the deployment block's number, timestamp, hash and state root; the recorded signed transaction in its slot 0 with a successful receipt; empty SYSTEM_ADDRESS code and canonical beacon-roots code at the parent block; the checkpoint's last header; canonical beacon-roots, history-storage and consolidation code and SYSTEM_ADDRESS's zero nonce at the checkpoint. Undischarged ENV: no raw frame of the deployment block and the following blocks without a code address targets SYSTEM_ADDRESS; after the checkpoint, no checked sender or 7702 authority is SYSTEM_ADDRESS and no CREATE targets it. **Scope: at most 2^254 committed submission-payment occurrences after the checkpoint** | The recorded raw bytes hash to the observed transaction hash, decode strictly to the transaction used here, and recover the deployer [`Blanc.Lift.WithdrawalRequest.Creation.HistoricalTx.raw_binding` (`Blanc/Lift/WithdrawalRequest/Creation/HistoricalTxRecover.lean:34`), `Blanc.Lift.WithdrawalRequest.Creation.HistoricalTx.recoveredSender` (`Blanc/Lift/WithdrawalRequest/Creation/HistoricalTxRecover.lean:26`)]. The deployment input, the Cancun forks of the prefix, beacon code at its openings, SYSTEM_ADDRESS emptiness after the deployment, EIP-7002 code and INIT at the checkpoint, the other three system installations there and the prefix's SYSTEM_ADDRESS sender exclusion (from its zero nonce) are derived from the observations. The observed values come from public JSON-RPC operators; Lean does not authenticate them against consensus or a state trie |
| **Delivery over observed records:** after the actual deployment and its admitted prefix, if a record sits at position q of the stored queue at block B's request boundary, then block D, exactly ⌊q/16⌋ configured blocks after B, publishes it in its actual withdrawal requests as record q mod 16, preceded in order by exactly B's queue entries from position 16·⌊q/16⌋. Every stored record at B is covered, with no queue-model premise. Intermediate: delivery after acceptance: if an entry sits at index q of the queue at block B's request boundary, then in every configured extension of the history through B that ends at the block D exactly ⌊q/16⌋ blocks after B (B counted as 0), D's withdrawal system call returns `systemOutput` of its queue model with the entry as record q mod 16, and the records up to it are exactly B's queue entries 16·⌊q/16⌋ … q, so nothing submitted later overtakes it (the FIFO row places that output in D's requests as the type-1 entry) | `Blanc.Lift.WithdrawalRequest.history_delivery` (`Blanc/Lift/WithdrawalRequest/HeadlineHistory.lean:155`), with conclusion `Blanc.Lift.WithdrawalRequest.Delivered` (`Blanc/Lift/WithdrawalRequest/HeadlineHistory.lean:122`) over `Blanc.Lift.WithdrawalRequest.queueAtRequests` (`Blanc/Lift/WithdrawalRequest/HeadlineHistory.lean:111`) and `Blanc.Lift.WithdrawalRequest.blockWithdrawals` (`Blanc/Lift/WithdrawalRequest/HeadlineHistory.lean:117`); at the actual mainnet deployment `Blanc.Lift.WithdrawalRequest.history_delivery_mainnet` (`Blanc/Lift/WithdrawalRequest/HeadlineHistory.lean:242`); via `Blanc.Lift.WithdrawalRequest.block_word_delivery_from_deployment` (`Blanc/Lift/WithdrawalRequest/WordDelivery.lean:398`); independent checkpoint form `Blanc.Lift.WithdrawalRequest.block_word_delivery` (`Blanc/Lift/WithdrawalRequest/WordDelivery.lean:309`) | Deployment-rooted history / delivery bound | The first row's deployment, admitted Cancun prefix and modern environmental conditions, and the occurrence bound over the modern history through D; no representation, model or queued-entry premise (intermediate: The deployment form has the first row's deployment, admitted Cancun prefix and modern environmental conditions; the occurrence bound covers the modern history through D. The independent checkpoint form retains canonical system code, represented INIT and checkpoint SYSTEM emptiness. The queue at B is the model B's request-boundary storage represents, which is unique) | The headline states D's records up to position q mod 16, not D's whole withdrawal output; no claim that the chain produces those later blocks; distance is counted in configured blocks |
| **The control at the public FIFO law:** with no hypotheses, a configured history meeting every premise of the checkpoint FIFO form except SYSTEM_ADDRESS emptiness (a drainer runtime sits there) has `HistoryFifo` false: block D commits a submission, the drainer dequeues it before the block's system call, no block publishes it, and the final stored queue is empty. | `Blanc.Lift.WithdrawalRequest.DrainControl.historyFifo_of_checkpoint_needs_systemEmpty` (`Blanc/Composition/WithdrawalRequestDrainControl.lean:739`), stating `Blanc.Lift.WithdrawalRequest.HistoryFifoCheckpointLoadBearing` (`Blanc/Lift/WithdrawalRequest/FifoDrainControl.lean:92`) | Negative control of the checkpoint FIFO form, closed | none | It negates the checkpoint form `Blanc.Lift.WithdrawalRequest.history_fifo_of_checkpoint` (`Blanc/Lift/WithdrawalRequest/HistoryFifo.lean:241`), not `history_fifo`, which has no SYSTEM-emptiness premise: it shows that deriving emptiness from the deployment admission is load-bearing. The witness lives only in the model and concerns a history from an independently supplied checkpoint; it supplies no canonical deployment witness. The deployment-rooted theorem retains SYSTEM emptiness as an environmental condition at the committed post-deployment boundary and derives it at the modern checkpoint. That no real chain can put code there is not proved |
| Storage at the future state is the EIP model replayed over exactly the committed submissions and system calls, in trace order, at the actual word fee | `Blanc.Lift.WithdrawalRequest.history_word_storage_replay` (`Blanc/Lift/WithdrawalRequest/WordReplay.lean:323`), `Blanc.Lift.WithdrawalRequest.history_word_model` (`Blanc/Lift/WithdrawalRequest/WordFifo.lean:230`) | Modern checkpoint history / exact replay | Raw word-storage replay needs canonical EIP-7002 code at the checkpoint of the actual `CoveredFork` trace. Its INIT-rooted model refinement also requires represented INIT and the 2^254 submission-payment occurrence bound. The first row's deployment bridge produces the code and INIT facts; its modern capacity bound remains explicit | the lower-level replay theorem remains available for independent checkpoints; it does not itself assume or authenticate deployment |
| Every successful fresh frame at this code is exactly one of a system dequeue, a word-fee submission or a fee read, with exact storage, logs and return bytes. No other fresh entry succeeds: a user call whose input is neither empty nor 56 bytes, a fee read carrying value, a static or underpaying submission, and any user call at the inhibitor have no successful execution | `Blanc.Lift.WithdrawalRequest.exec_frame_effect` (`Blanc/Lift/WithdrawalRequest/FrameEffects.lean:33`) | Frame / refinement | CODE; covered fork; fresh entry (empty stack, word-aligned well-formed memory, input shorter than 2^256 bytes) | model transcribed from the EIP text, not from the bytes; **success is classified, failure is not**: which failure occurs (REVERT, out-of-gas, a static-context fault), its gas and its return data are not stated |
| Fee, against the EIP directly: the fee the bytecode computes from the excess is at most the EIP's fake_exponential(1, excess, 17), with equality exactly on `NatFeeDomain`, with no model state. Intermediate: Fee: the executed word fee is at most fake_exponential(1, excess, 17), with equality exactly on `NatFeeDomain`; every committed submission paid its executed word fee | `Blanc.Lift.WithdrawalRequest.fee_le_spec` (`Blanc/Lift/WithdrawalRequest/HeadlineFee.lean:41`), `Blanc.Lift.WithdrawalRequest.fee_eq_spec_iff` (`Blanc/Lift/WithdrawalRequest/HeadlineFee.lean:48`), over `Blanc.Lift.WithdrawalRequest.WordFee` (`Blanc/Lift/WithdrawalRequest/HeadlineFee.lean:20`) and `Blanc.Lift.WithdrawalRequest.SpecFee` (`Blanc/Lift/WithdrawalRequest/HeadlineFee.lean:17`); via `Blanc.Lift.WithdrawalRequest.word_fee_le_nat` (`Blanc/Lift/WithdrawalRequest/ExactFeeDomain.lean:51`), `Blanc.Lift.WithdrawalRequest.word_fee_eq_iff_natFeeDomain` (`Blanc/Lift/WithdrawalRequest/ExactFeeDomain.lean:27`); the intermediate's history clause (every committed submission paid its executed word fee) is `Blanc.Lift.WithdrawalRequest.history_word_fee_budget` (`Blanc/Lift/WithdrawalRequest/WordBudget.lean:78`) | Frame and history | the executed word fee loop only (intermediate: CODE) | see §7 item 16 |
| **The EIP's unbounded-integer fee guarantee is false for these bytes**: a three-block configured history from an initialized checkpoint (system contracts installed, empty SYSTEM_ADDRESS code, the four EIP-7002 storage words as deployed: inhibitor excess and zero count, head and tail), under the sender, authority and CREATE exclusions, has a committed submission that paid the bytecode's fee at its stored excess but less than fake_exponential(1, 2893, 17). The statement reads only storage words, the committed submission frames, their paid value and the word fee loop | `Blanc.Lift.WithdrawalRequest.FeeCounterexample.fee_guarantee_refuted` (`Blanc/Composition/WithdrawalRequestFeeHeadline.lean:59`), stating `Blanc.Lift.WithdrawalRequest.FeeCounterexample.FeeGuaranteeRefuted` (`Blanc/Composition/WithdrawalRequestFeeHeadline.lean:20`), equivalent to the model form by `Blanc.Lift.WithdrawalRequest.FeeCounterexample.feeGuaranteeRefuted_iff` (`Blanc/Composition/WithdrawalRequestFeeHeadline.lean:37`); via `Blanc.Lift.WithdrawalRequest.FeeCounterexample.nat_fee_guarantee_refuted` (`Blanc/Composition/WithdrawalRequestFeeRefutation.lean:1242`) | History / refutation, closed | none | Rooted in an initialized checkpoint, not in the deployment; §7 item 16 |
| System call: with canonical code installed, whatever storage holds, the checked system call succeeds with no error and uses at most 210,000 gas; the history form states the same after the actual deployment, its admitted prefix and any configured history. Intermediate: system call: with the code installed the checked system call succeeds with no error and exact gas `systemProtocolGas` ≤ 210,000; at a block's request boundary its storage update is the raw 256-bit word computation, which sets the count to 0 and leaves the reset excess at least two below the word maximum | `Blanc.Lift.WithdrawalRequest.system_call_succeeds` (`Blanc/Lift/WithdrawalRequest/HeadlineSystem.lean:28`), `Blanc.Lift.WithdrawalRequest.history_system_call_succeeds` (`Blanc/Lift/WithdrawalRequest/HeadlineSystem.lean:42`), with conclusion `Blanc.Lift.WithdrawalRequest.SystemCallOk` (`Blanc/Lift/WithdrawalRequest/HeadlineSystem.lean:23`); at the actual mainnet deployment `Blanc.Lift.WithdrawalRequest.history_system_call_succeeds_mainnet` (`Blanc/Lift/WithdrawalRequest/HeadlineSystem.lean:161`); via `Blanc.Lift.WithdrawalRequest.checked_system_totality` (`Blanc/Lift/WithdrawalRequest/SystemProtocol.lean:247`), `Blanc.Lift.WithdrawalRequest.systemFrameGas_closed` (`Blanc/Lift/WithdrawalRequest/SystemGas.lean:96`), `Blanc.Lift.WithdrawalRequest.block_requests_reset_occurrence` (`Blanc/Lift/WithdrawalRequest/ResetOccurrence.lean:121`); at each block's actual request boundary, `Blanc.Lift.WithdrawalRequest.block_checked_system_totality` (`Blanc/Lift/WithdrawalRequest/BlockRequests.lean:34`) | Frame and deployment-rooted history / totality; intermediate: frame and block / totality, exact gas | CODE; covered fork. The history form takes the first row's deployment and admitted prefix in place of checkpoint CODE (intermediate: CODE; covered fork). The mainnet form takes in their place the observed deployment block (its position-0 cut), the following Cancun blocks to the checkpoint and the recorded observations of the deployment [`Blanc.Lift.WithdrawalRequest.WithdrawalDeploymentObservation` (`Blanc/Lift/WithdrawalRequest/MainnetDeployment.lean:77`)], and the avoidance of `CREATE` at SYSTEM_ADDRESS by every raw frame of those blocks | The headline bounds the gas used by 210,000; the exact post state, output and gas are in the intermediate. no storage model: from CODE alone the excess update is word arithmetic, and excess + count can wrap modulo 2^256 |
| Within the first row's scope, the system call's word update is the EIP's natural-number bookkeeping: `excess' = max(0, e + count − 2)` where e is the effective excess (0 at the inhibitor), `count' = 0`, the first min(16, queue) entries leave and head/tail advance or reset; every bookkeeping value stays within 2^254 and no live queue slot reaches slots 0–3 | `Blanc.Lift.WithdrawalRequest.systemNewExcess_represented` (`Blanc/Lift/WithdrawalRequest/SystemStorage.lean:119`), `Blanc.Lift.WithdrawalRequest.WordHistory.conservation` (`Blanc/Lift/WithdrawalRequest/WordHistory.lean:36`), `Blanc.Lift.WithdrawalRequest.WordMargin.slots_safe` (`Blanc/Lift/WithdrawalRequest/WordHistory.lean:139`) | Deployment-rooted history / refinement | The first row's canonical Cancun deployment, all-Cancun admitted prefix, modern `CoveredFork` suffix, remaining environmental/installation conditions and 2^254 occurrence scope; INIT and EIP-7002 code are derived | the word-to-natural step requires a storage representation and e + count < 2^256; the deployment bridge and bounded model history derive them. The natural recurrence is not a CODE-only fact; `Blanc.Lift.WithdrawalRequest.wordSystem_excess_wraps` (`Blanc/Lift/WithdrawalRequest/WordReplay.lean:42`) exhibits represented storage at excess 2^256 − 2 and count 10 whose word update stores 6 and does not represent that model's natural step, whose excess would be 2^256 + 6 |
| Payments from the actual deployment: after the deployment and its admitted prefix, in any configured history the contract's final balance is at least its checkpoint balance plus the value of every committed submission. Intermediate: from the checkpoint the balance changes by an ordered list of signed credits whose submission payments are exactly the committed submissions' values | `Blanc.Lift.WithdrawalRequest.history_payments` (`Blanc/Lift/WithdrawalRequest/HeadlineHistory.lean:99`) over `Blanc.Lift.WithdrawalRequest.submissionPaid` (`Blanc/Lift/WithdrawalRequest/HeadlineHistory.lean:60`); at the actual mainnet deployment `Blanc.Lift.WithdrawalRequest.history_payments_mainnet` (`Blanc/Lift/WithdrawalRequest/HeadlineHistory.lean:226`); via `Blanc.Lift.WithdrawalRequest.history_submission_payments` (`Blanc/Lift/WithdrawalRequest/BalanceHistory.lean:206`) | Deployment-rooted history; intermediate: history | the first row's deployment and admitted prefix (intermediate: CODE) | uses `SpawnFreeReach`, not the offset-blind `SpawnFree`; the balance is not a count of fees, since value that reaches the address without running its code also raises it |

**Liveness.** After any configured history that leaves the contract active (excess below the inhibitor), a fresh
non-static frame carrying a 56-byte submission from a non-system caller with `value ≥ fake_exponential(1, excess, 17)`
on a covered fork has a successful execution: started with 1258 + 87·k + reads + stores gas plus a residual G
greater than the 2,300-gas stipend, it consumes exactly that charge and ends with G left, where `k` is the fee loop's
iteration count. The charge is the gas consumed, not a proved minimum. At the inhibitor no user
call succeeds. The fee read likewise has a successful execution at an exact charge
[`Blanc.Lift.WithdrawalRequest.history_submission_live` (`Blanc/Lift/WithdrawalRequest/HeadlineSystem.lean:80`), with conclusion `Blanc.Lift.WithdrawalRequest.SubmissionLive` (`Blanc/Lift/WithdrawalRequest/HeadlineSystem.lean:64`) and the charge `Blanc.Lift.WithdrawalRequest.submissionCost` (`Blanc/Lift/WithdrawalRequest/HeadlineSystem.lean:56`); at the actual mainnet deployment `Blanc.Lift.WithdrawalRequest.history_submission_live_mainnet` (`Blanc/Lift/WithdrawalRequest/HeadlineSystem.lean:177`); via `Blanc.Lift.WithdrawalRequest.history_submission_nat_live` (`Blanc/Lift/WithdrawalRequest/NatLiveness.lean:59`); the fee read is `Blanc.Lift.WithdrawalRequest.history_fee_getter_word_live` (`Blanc/Lift/WithdrawalRequest/NatLiveness.lean:96`)]. The submission headline takes the first row's deployment and admitted prefix in place of checkpoint CODE (the mainnet form, the observed deployment block, its following blocks and the `CREATE` avoidance of the system-call row above); the intermediates' only installation premise is checkpoint CODE, with no storage model; the frame shape, caller, input,
payment and fork above are hypotheses. At a large enough excess fake_exponential exceeds every 256-bit value, so the
payment hypothesis cannot hold there.
**Queue effect.** After the actual deployment, its admitted prefix and any configured history with at most `wordOccurrenceCap` (2^254) committed submissions, every
successful execution of a fresh 56-byte submission from a non-system caller on a covered fork leaves the stored queue as it was with one record appended: the caller's 20 bytes,
the 48 public-key bytes and the amount's 8 bytes in little-endian order
[`Blanc.Lift.WithdrawalRequest.history_submission_queued` (`Blanc/Lift/WithdrawalRequest/HeadlineSystem.lean:103`), with conclusion `Blanc.Lift.WithdrawalRequest.SubmissionQueued` (`Blanc/Lift/WithdrawalRequest/HeadlineSystem.lean:92`) over `Blanc.Lift.WithdrawalRequest.storedQueue` (`Blanc/Lift/WithdrawalRequest/HistoryFifo.lean:59`); at the actual mainnet deployment `Blanc.Lift.WithdrawalRequest.history_submission_queued_mainnet` (`Blanc/Lift/WithdrawalRequest/HeadlineSystem.lean:195`); via `Blanc.Lift.WithdrawalRequest.history_word_model` (`Blanc/Lift/WithdrawalRequest/WordFifo.lean:230`)]. The statement ranges over every successful execution, whatever fee the call paid, so it does not depend on the payment hypothesis of the liveness statement; it says nothing about whether a successful execution exists. Its premise beyond the liveness headline's is the cumulative cap on committed submissions (`(submissions history).length ≤ wordOccurrenceCap`), which keeps the stored count and tail inside the queue's window: without it the tail could wrap and the record could land outside `storedQueue`.
**No transaction-level liveness** (E13 not pursued): sender funding, intrinsic gas, block room and call forwarding are
not covered.

**Deployment / INIT.** The headline is rooted in one actual transaction of a retained configured
Cancun block. `Blanc.Lift.WithdrawalRequest.Creation.CanonicalDeploymentInput` (`Blanc/Lift/WithdrawalRequest/Creation/Transaction.lean:22`) identifies its prepared CREATE
message by canonical address and creation code, zero value, at least 123017 message gas and no creation
collision. It assumes neither installed runtime nor initialized storage nor constructor success.
`Blanc.Lift.WithdrawalRequest.Creation.transaction_initial_cancun` (`Blanc/Lift/WithdrawalRequest/Creation/Transaction.lean:95`) derives canonical runtime and inhibitor/empty-queue
storage in that transaction's actual committed final state. `Blanc.Lift.WithdrawalRequest.Creation.DeploymentCut.initial` (`Blanc/Lift/WithdrawalRequest/Creation/Block.lean:42`) places
that result at the exact boundary starting the remainder of its block. `Blanc.Lift.WithdrawalRequest.DeploymentHistory.initialized` (`Blanc/Lift/WithdrawalRequest/DeploymentHistory.lean:77`)
transports those facts through that same all-Cancun remainder and following history to the shared modern
checkpoint and proves the prefix has no committed nonstatic EIP-7002 target frames. Its admission keeps
checked sender exclusions, actual CREATE avoidance at SYSTEM_ADDRESS, empty SYSTEM_ADDRESS code at the
committed post-deployment boundary and canonical beacon code at later whole-block openings explicit.
The modern suffix uses `CoveredFork` and separately requires the other three canonical protocol contracts.
This is a conditional execution theorem; it does not authenticate a historical transaction, block inclusion
or state root. The public deployment statement `Blanc.Lift.WithdrawalRequest.deploy` (`Blanc/Lift/WithdrawalRequest/HeadlineHistory.lean:42`) reads both boundaries
directly: right after the deployment transaction and at the modern checkpoint, the canonical runtime is installed and the four
bookkeeping words hold the inhibitor excess and zero count, head and tail (`Blanc.Lift.WithdrawalRequest.InitialWords` (`Blanc/Lift/WithdrawalRequest/HeadlineHistory.lean:24`));
`Blanc.Lift.WithdrawalRequest.deploy_mainnet` (`Blanc/Lift/WithdrawalRequest/HeadlineHistory.lean:208`) states it at the actual mainnet deployment. The independent checkpoint
theorems remain available.

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
about the callee answers of the history's own steps. The theorems of this section do
not use the factory's bytecode: its `feeTo` answers and its `initialize` call stay
premise-level here. The factory runtime is lifted separately (Section 2), and Section
5.9 uses it only to show that the factory makes no non-static call into a pair
installed at the checkpoint. The functional model is transcribed from the v1.0.1 sources and carries a
line-by-line correspondence table with an independent source-versus-model review
([`docs/registers/UNISWAP_V2_MODEL_REVIEW.md`](registers/UNISWAP_V2_MODEL_REVIEW.md),
which reviewed an earlier snapshot of the model and states what has changed since).

**Safety, refinement and history**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| After any configured history: the certified runtime is still installed, and there is a list of steps, one per **outermost** settlement-committed non-static pair frame in trace order, such that the committed pair frames of the steps' subtrees are exactly the settlement-committed non-static pair frames of the trace (rolled-back frames absent, static frames observe nothing); every step's frame is a pc-0, committed, non-static frame at the pair whose entry is the one its own run decodes (`AuthenticWith PairEntryAuth`); the steps are consumed in order from the checkpoint model state by `PairObservedReplayWith PairAdmittedConsumes`, in which, for each step, the actual position of every external call of the frame's own derivation, its reply, the entered bit and the full nested queues below it feed one recursively admitted consumption, whose returned bytes are the step's actual output and whose carried model state starts the next step; and replaying the steps' source invocations from the checkpoint model state with the source model's driver gives a model state that the future pair storage represents | `Blanc.Lift.UniswapV2Pair.pair_history_committed` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:467`); steps `Blanc.Lift.UniswapV2Pair.PairStep` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:158`) with `Blanc.Lift.UniswapV2Pair.PairStep.AuthenticWith` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:218`) at `Blanc.Lift.UniswapV2Pair.PairEntryAuth` (`Blanc/Lift/UniswapV2Pair/PairPositionalEntry.lean:34`); the replay `Blanc.Lift.UniswapV2Pair.PairObservedReplayWith` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:168`) at `Blanc.Lift.UniswapV2Pair.PairAdmittedConsumes` (`Blanc/Lift/UniswapV2Pair/PairPositionalAdmission.lean:16`); the observed list `Blanc.Lift.UniswapV2Pair.committedPairFrames` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:384`) over `Blanc.Lift.UniswapV2Pair.pairSubtreeFrames` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:233`) | History / safety, exact extraction | CODE (the certified runtime at the pair at the checkpoint); INIT `WriterRep K₀ (pair storage) st₀`; **HASH-T** `WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace)` (finite, trace-local, includes rolled-back frames). **No per-frame ENTRY premise, no universal hash premise, no token or factory premise** | The headline. It instantiates the generic history construction at the concrete eleven-family admitted supplier `Blanc.Lift.UniswapV2Pair.pairAdmittedSupply` (`Blanc/Lift/UniswapV2Pair/PairPositionalSupply.lean:58`), assembled by `Blanc.Lift.UniswapV2Pair.pairAdmittedSupplyRules` (`Blanc/Lift/UniswapV2Pair/PairPositionalSupply.lean:12`) from the family suppliers, among them `pair_admitted_skim_supply`, `pair_admitted_burn_supply` and `pair_admitted_swap_supply`; a `burn`'s two reads of each token's balance are therefore consumed at their own positions. The replay, the history rows below and NoShrink all range over the same selected steps (`steps.map PairStep.source`). The list is pinned by an equality, not a free witness: the observation equality places every step's frame among the trace's settled frames, and a committed non-static pair frame always observes itself, so a step cannot be a phantom. The replay is **nested, not flat**: a pair frame re-entered from inside a token call, the flash-swap callback or a factory call is consumed inside its parent step's transcript (Section 7 item 19). The calldata bound is derived [`Blanc.Lift.UniswapV2Pair.pair_trace_admitted` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:389`)]. The source driver `Blanc.Lift.UniswapV2Pair.runSourceInvocations` (`Blanc/Lift/UniswapV2Pair/SourceReplay.lean:25`) accepts only successful invocations |
| The same statement from the deployment checkpoint: with `st₀ = initializedState factory domain token0 token1` and no initially tracked row, every tracked row at the end is a row the trace touched | `Blanc.Lift.UniswapV2Pair.pair_history_initialized` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:520`) | History / safety | CODE; INIT `InitializedCheckpoint` (the checkpoint storage is the deploy-then-`initialize` storage); HASH-T with no initial row | The INIT premise is the conclusion of the deployment theorem below |
| **From the actual deployment of the USDC/WETH9 Pair:** at any later block, its stored supply word (slot 0) is the sum of the stored LP balance words of every holder the history from the createPair transaction touched. Intermediate: **LP-token ledger (U7):** the replayed model state satisfies `Ledger`: the LP balances of **all** addresses sum to `totalSupply`, `MINIMUM_LIQUIDITY` at address 0 and every protocol-fee mint included | `Blanc.Composition.LiveUsdcWeth9B26213219.pair_ledger` (`Blanc/Composition/LiveUsdcWeth9B26213219Headlines.lean:84`), with conclusion `Blanc.Lift.UniswapV2Pair.LpLedgerBalanced` (`Blanc/Lift/UniswapV2Pair/StorageObservers.lean:38`); via the createPair replay `Blanc.Lift.UniswapV2Factory.pair_history_initialized_from_createPair_block_noCollision` (`Blanc/Lift/UniswapV2Factory/CreatePairHistory.lean:123`) and the replay law `Blanc.Lift.UniswapV2Pair.SourceReplay.ledger` (`Blanc/Lift/UniswapV2Pair/SourceReplay.lean:67`) from `Blanc.Lift.UniswapV2Pair.State.initialized_ledgerOn` (`Blanc/Lift/UniswapV2Pair/PropertiesLedger.lean:70`); the invariant `Blanc.Lift.UniswapV2Pair.State.Ledger` (`Blanc/Lift/UniswapV2Pair/PropertiesLedger.lean:35`); model level `Blanc.Lift.UniswapV2Pair.runTyped_ledgerOn` (`Blanc/Lift/UniswapV2Pair/PropertiesLedger.lean:550`) | Deployment-rooted history / safety (the exhibit pair); intermediate: history / safety | DEPLOYMENT `Blanc.Composition.LiveUsdcWeth9B26213219.PairDeploymentTo` (`Blanc/Composition/LiveUsdcWeth9B26213219History.lean:318`): the retained configured `HistFork` mainnet block 10,008,355 whose transaction at index 38 is the USDC/WETH9 createPair call to the factory (its call data, zero value, nonce 205, funds and gas; the factory's code, nonce and guard word and an empty Pair address at that point), the configured history after it, and **HASH-T** freshness of the rows the Pair frames of the rest of that block and of that history touch, all fields of the record | The exhibit pair only. Callbacks may re-enter the unlocked ERC-20 entry points; the replay admits that. The ledger at the initialized checkpoint is proved, not assumed |
| **Oracle (U5):** at every outer call of the Pair (a settled non-static Pair frame that no earlier one encloses), each stored cumulative price word at the call's committed exit is its entry word plus the TWAP increment of the entry reserve words over the advance `Δt` of the stored `uint32` timestamp, modulo 2^256 (`price0`: `⌊r1·2^112/r0⌋·Δt`; `price1`: `⌊r0·2^112/r1⌋·Δt`; zero when `Δt` or a reserve is zero), and the stored timestamp word stays or becomes the frame's block timestamp modulo 2^32. | `Blanc.Lift.UniswapV2Pair.pair_oracle` (`Blanc/Lift/UniswapV2Pair/HeadlineOracle.lean:54`), with conclusion `Blanc.Lift.UniswapV2Pair.OracleAdvance` (`Blanc/Lift/UniswapV2Pair/HeadlineOracle.lean:33`) over `Blanc.Lift.UniswapV2Pair.timestampAdvance` (`Blanc/Lift/UniswapV2Pair/HeadlineOracle.lean:26`), `Blanc.Lift.UniswapV2Pair.twapIncrement` (`Blanc/Lift/UniswapV2Pair/OracleCallReceipt.lean:31`), `Blanc.Lift.UniswapV2Pair.wrapElapsed` (`Blanc/Lift/UniswapV2Pair/OracleCallReceipt.lean:35`), the stored words `Blanc.Lift.UniswapV2Pair.price0Word` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:49`), `Blanc.Lift.UniswapV2Pair.price1Word` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:52`), `Blanc.Lift.UniswapV2Pair.reserve0Word` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:40`), `Blanc.Lift.UniswapV2Pair.reserve1Word` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:43`) and `Blanc.Lift.UniswapV2Pair.timestampWord` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:46`), and the call with its entry and exit storage `Blanc.Lift.UniswapV2Pair.OuterPairCall` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:120`), `Blanc.Lift.UniswapV2Pair.preS` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:127`), `Blanc.Lift.UniswapV2Pair.postS` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:130`); via each outer call's own consumed step `Blanc.Lift.UniswapV2Pair.pair_history_outer_call_at` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:225`) and the one-call model law `runTyped_oracle_call` (`Blanc/Lift/UniswapV2Pair/OracleCallReceipt.lean`); the per-update law `Blanc.Lift.UniswapV2Pair.OracleUpdate.Lawful` (`Blanc/Lift/UniswapV2Pair/PropertiesOracleLaw.lean:8`): `Δt = (ts mod 2^32 − last) mod 2^32` and an increment of `⌊r1·2^112/r0⌋·Δt` (symmetrically for price 1) when `Δt` and both reserves are nonzero, established for every update `Blanc.Lift.UniswapV2Pair.State.update_oracle_lawful` (`Blanc/Lift/UniswapV2Pair/PropertiesOracleLaw.lean:20`) and carried through the typed driver by `runTyped_oracle_law` (`Blanc/Lift/UniswapV2Pair/PropertiesOracleLaw.lean`) | History (per outer call) / safety; the per-update law: model / safety | as `pair_history_committed` | Both wraparounds, of the `uint32` timestamp and of the accumulator, are part of the statements. The headline states one TWAP increment per outer call, over the **stored** entry reserves and the stored-timestamp advance; a Pair frame re-entered inside the call adds no increment of its own. It states no sum over the whole history, and nothing about the Pair's storage between one outer call's exit and the next one's entry (Section 7 item 22) |
| **Share value never decreases, protocol fee off (U3):** at every outer call of the Pair whose own token answers back the stored reserves (`BalanceAnswersBacked`) and whose factory query entered a committed frame that answered `feeTo() = 0` (`FeeToOff`), with positive supply `T` at entry, `r0·r1·T'² ≤ r0'·r1'·T²` over the stored words at the call's entry and committed exit. Intermediate: **Share value, protocol fee off, over a consumed source replay (U3):** for every committed state change of the replay with positive incoming supply `T`, `r0·r1·T'² ≤ r0'·r1'·T²`; when the outgoing supply `T'` is positive too, this says `√(r0·r1)/T` does not decrease (`T'` can be 0, for example after a burn of the whole supply, and then no ratio is defined). The bound holds between consecutive committed steps of the replay, not at intermediate states inside a frame. It covers mint (minimum of two floors), burn (floors), swap (fee-adjusted check), sync and skim | `Blanc.Lift.UniswapV2Pair.pair_share_value_feeOff` (`Blanc/Lift/UniswapV2Pair/HeadlineShare.lean:93`), with conclusion `Blanc.Lift.UniswapV2Pair.ShareValueKept` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:162`) at fee 0 over `Blanc.Lift.UniswapV2Pair.OuterPairCall` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:120`) and the premise observers `Blanc.Lift.UniswapV2Pair.BalanceAnswersBacked` (`Blanc/Lift/UniswapV2Pair/BalanceAnswers.lean:268`) (read through `Blanc.Lift.UniswapV2Pair.answerWord` (`Blanc/Lift/UniswapV2Pair/BalanceAnswers.lean:256`), `Blanc.Lift.UniswapV2Pair.outputWord` (`Blanc/Lift/UniswapV2Pair/BalanceAnswers.lean:260`) and `Blanc.Lift.UniswapV2Pair.childAt` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:136`)) and `Blanc.Lift.UniswapV2Pair.FeeToOff` (`Blanc/Lift/UniswapV2Pair/HeadlineShare.lean:32`) (with `Blanc.Lift.UniswapV2Pair.feeToAnswer` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:143`), `Blanc.Lift.UniswapV2Pair.MintOrBurn` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:149`)); via the fee-on headline of the next row; intermediate (model replay): `Blanc.Lift.UniswapV2Pair.SourceReplay.feeOff_product` (`Blanc/Lift/UniswapV2Pair/SourceReplay.lean:94`) over the consumed replay `Blanc.Lift.UniswapV2Pair.SourceReplay` (`Blanc/Lift/UniswapV2Pair/SourceReplay.lean:35`); frame-level `Blanc.Lift.UniswapV2Pair.runTyped_product` (`Blanc/Lift/UniswapV2Pair/Properties.lean:2680`) | History (per outer call) / safety; intermediate: model replay / safety | as `pair_history_committed`, and for the call itself `BalanceAnswersBacked` and `FeeToOff` (intermediate: over the replay's own steps `sourceReplayAnswers`: at each step `EntryFeeOff` (the factory's `feeTo` answer of a mint or burn is zero) and `EntryNoShrink` (the token-answer premise **NoShrink**, below)) | **Token and factory premises, stated over the call itself**, not over all tokens and not over any other call. Nonvacuous: any call whose token frames answer at least the stored reserves where the premise says so, and whose factory frame answers `feeTo = 0`, satisfies it. The answers must come from committed frames: `BalanceAnswersBacked` and `FeeToOff` require the consulted calls to have entered one, so an answer from a precompile or from a call that entered no frame does not satisfy them. `BalanceAnswersBacked` is the transcript condition `EntryNoShrink` together with that requirement, exactly [`Blanc.Lift.UniswapV2Pair.balanceAnswersBacked_iff` (`Blanc/Lift/UniswapV2Pair/BalanceAnswers.lean:508`)]. The unit is the outer call, the frame together with every Pair frame re-entered inside it, not each model edge. Mint and swap need no token premise: the bytecode's own checks (the checked balance subtractions, the fee-adjusted check) give the inequality |
| **Share value with the protocol fee on:** at every outer call of the Pair whose own token answers back the stored reserves (`BalanceAnswersBacked`) and whose factory query entered a committed frame (`FeeAnswered`), with positive supply `T` at entry, `r0·r1·T'² ≤ r0'·r1'·(T + F)²` over the stored words at the call's entry and committed exit, where `F` is the fee that a `mint` or `burn` mints at the `feeTo()` answer read from the output of that factory frame (`⌊T·(√k − √kLast)/(5·√k + √kLast)⌋` over the stored entry words with floored roots, `feeTo ≠ 0`, `kLast ≠ 0`, `√kLast < √k`; else 0), and 0 for every other call. Intermediate: **Share value with the protocol fee on, over a consumed source replay:** every committed state change with positive incoming supply keeps `r0·r1·T'² ≤ r0'·r1'·(T + F)²`, where `F = entryFeeAmount` is the exact fee mint of that step, `⌊T·(√k − √kLast)/(5·√k + √kLast)⌋` at the step's actual `feeTo` answer (floored roots, `feeTo ≠ 0`, `kLast ≠ 0`, `√kLast < √k`), else 0; dilution is bounded by the fee mint alone | `Blanc.Lift.UniswapV2Pair.pair_share_value` (`Blanc/Lift/UniswapV2Pair/HeadlineShare.lean:48`), with conclusion `Blanc.Lift.UniswapV2Pair.ShareValueKept` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:162`) at `Blanc.Lift.UniswapV2Pair.callFeeWords` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:156`) over `Blanc.Lift.UniswapV2Pair.OuterPairCall` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:120`), the premise observers `Blanc.Lift.UniswapV2Pair.BalanceAnswersBacked` (`Blanc/Lift/UniswapV2Pair/BalanceAnswers.lean:268`) and `Blanc.Lift.UniswapV2Pair.FeeAnswered` (`Blanc/Lift/UniswapV2Pair/HeadlineShare.lean:29`), and `Blanc.Lift.UniswapV2Pair.feeMintWords` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:59`); `FeeAnswered` holds at every outer call when the stored factory is undelegated code and no precompile at the call's nodes [`Blanc.Composition.PairTwoToken.feeAnswered_of_factoryEntered` (`Blanc/Composition/PairTwoTokenCallShare.lean:174`)]; via `Blanc.Lift.UniswapV2Pair.entryNoShrink_of_backed` (`Blanc/Lift/UniswapV2Pair/BalanceAnswers.lean:360`) and the per-invocation law `Blanc.Lift.UniswapV2Pair.runTyped_product` (`Blanc/Lift/UniswapV2Pair/Properties.lean:2680`); intermediate (model replay): `Blanc.Lift.UniswapV2Pair.SourceReplay.feeOn_product` (`Blanc/Lift/UniswapV2Pair/SourceReplay.lean:140`) | History (per outer call) / safety; intermediate: model replay / safety | as `pair_history_committed`, and for the call itself `BalanceAnswersBacked` and `FeeAnswered` (intermediate: `sourceReplayNoShrink` over the replay's own steps) | As above without the fee-off condition; the fee is read from the actual factory frame, not from a transcript answer |
| **From the actual deployment of the USDC/WETH9 Pair:** at any later block, if no frame of the history from the createPair transaction entered at the Pair has caller 0, the stored supply is zero or address 0's stored LP balance is at least 1000. Intermediate: **`MINIMUM_LIQUIDITY` keeps the supply positive (U3 floor), over a consumed source replay:** from a model state satisfying `State.Ledger` and `State.SupplyFloor`, at the final state and at both ends of every step of the replay, the supply is zero or address 0 holds at least 1000 LP, and address 0 has granted no allowance; every step entered with positive supply leaves at least 1000 | `Blanc.Composition.LiveUsdcWeth9B26213219.pair_minimum_liquidity` (`Blanc/Composition/LiveUsdcWeth9B26213219Headlines.lean:104`), with conclusion `Blanc.Lift.UniswapV2Pair.MinLiquidity` (`Blanc/Lift/UniswapV2Pair/StorageObservers.lean:43`); via the createPair replay `Blanc.Lift.UniswapV2Factory.pair_history_initialized_from_createPair_block_noCollision` (`Blanc/Lift/UniswapV2Factory/CreatePairHistory.lean:123`) and the model replay law `Blanc.Lift.UniswapV2Pair.SourceReplay.supplyFloor` (`Blanc/Lift/UniswapV2Pair/PropertiesMinLiquidity.lean:699`); the invariant `Blanc.Lift.UniswapV2Pair.State.SupplyFloor` (`Blanc/Lift/UniswapV2Pair/PropertiesMinLiquidity.lean:40`) | Deployment-rooted history / safety (the exhibit pair); intermediate: model replay / safety | DEPLOYMENT `Blanc.Composition.LiveUsdcWeth9B26213219.PairDeploymentTo` (`Blanc/Composition/LiveUsdcWeth9B26213219History.lean:318`): the retained configured `HistFork` mainnet block 10,008,355 whose transaction at index 38 is the USDC/WETH9 createPair call to the factory (its call data, zero value, nonce 205, funds and gas; the factory's code, nonce and guard word and an empty Pair address at that point), the configured history after it, and **HASH-T** freshness of the rows the Pair frames of the rest of that block and of that history touch, all fields of the record; ENV: no raw frame of that history entered at the Pair has caller 0 (intermediate: `State.Ledger` and `State.SupplyFloor` at the replay's start; every step's pair nonzero, and `Blanc.Lift.UniswapV2Pair.SourceInvocation.CallersNonzero` (`Blanc/Lift/UniswapV2Pair/PropertiesMinLiquidity.lean:601`): no step and no re-entered pair child consumed inside a step has caller 0 (ENV: a caller-0 frame needs code or a signing key at address 0)) | The exhibit pair only; the caller premise ranges over raw frames, rolled-back ones included. The caller premise is load-bearing: a `transfer` or `approve` called by address 0 could move the locked LP. A `permit` cannot, since its recovered owner is nonzero. The floor concerns the model state the replay represents (Section 7 item 19) |
| **NoShrink, exactly.** For `sync`: both answers of `balanceOf(pair)` are at least the stored reserves. For `burn`: both first answers are at least the stored reserves, and each first answer is at most its final answer plus that token's payout (a transfer debits at most its payout). For every other entry: none | `Blanc.Lift.UniswapV2Pair.EntryNoShrink` (`Blanc/Lift/UniswapV2Pair/Properties.lean:2643`) with `Blanc.Lift.UniswapV2Pair.SyncEntryNoShrink` (`Blanc/Lift/UniswapV2Pair/Properties.lean:1994`) and `Blanc.Lift.UniswapV2Pair.BurnEntryNoShrink` (`Blanc/Lift/UniswapV2Pair/Properties.lean:1490`); fee-off `Blanc.Lift.UniswapV2Pair.EntryFeeOff` (`Blanc/Lift/UniswapV2Pair/Properties.lean:2657`); over a replay `Blanc.Lift.UniswapV2Pair.sourceReplayAnswers` (`Blanc/Lift/UniswapV2Pair/SourceReplay.lean:78`), `Blanc.Lift.UniswapV2Pair.sourceReplayNoShrink` (`Blanc/Lift/UniswapV2Pair/SourceReplay.lean:123`) | Premise definitions (ENV: callee behaviour) | — | The burn form is weaker than "every answer is at least the stored reserve", which would exclude every ordinary burn (an honest token answers below the reserve after paying out). NoShrink constrains only the pair's own balance answers, not what a recipient receives: a token that takes its transfer fee from the recipient's proceeds (the pair is debited exactly the payout), or whose balances only grow (positive rebases, donations), can satisfy it, while extra debits of the pair or downward rebases can violate it. No theorem claims that a recipient is credited, or that any token satisfies it outside Section 5.9, where the WETH9 half (`EntryNoShrinkSide` on WETH9's side) is a theorem from a joint checkpoint: the premise concerns the actual answers of the history's selected steps (Section 7 items 17 and 26) |
| Frame refinement of every selector: a successful pc-0 run of the certified runtime consumes the typed source entry exactly over the observations of its own derivation (the token and factory answers; nested turns derived from the run's actual children), with exact storage, logs and return bytes. For `mint`, `swap`, `skim` and `burn` the original-name statements return one admitted canonical result of the run: a positional consumption (the actual position of each external call, its reply, the entered bit and the full nested queues, mutable ones included) that is recursively admitted, with the actual output, the storage representation and the correspondence of the pending source logs with the raw logs; the `mint` direct and own forms carry that canonical result with the full pending and raw log image, and `swap_bytecode_exact_consumes` and its `_own` form return one `SwapPositionalCanonicalResult`. Writers: sync, mint, swap (in all six successful shapes: each optimistic transfer present iff its amount is nonzero, the callback present iff `data` is nonempty), skim, burn, transfer, approve, transferFrom, initialize (the factory is the caller) and permit; **views**: every successful static frame is one of the views, with value zero | `Blanc.Lift.UniswapV2Pair.sync_bytecode_exact_consumes` (`Blanc/Lift/UniswapV2Pair/SyncGasCanonical.lean:793`), `Blanc.Lift.UniswapV2Pair.mint_bytecode_exact_consumes` (`Blanc/Lift/UniswapV2Pair/MintPositionalRefinement.lean:19`), `Blanc.Lift.UniswapV2Pair.swap_bytecode_exact_consumes` (`Blanc/Lift/UniswapV2Pair/SwapPositionalRefinement.lean:8`), `Blanc.Lift.UniswapV2Pair.skim_bytecode_exact_consumes` (`Blanc/Lift/UniswapV2Pair/SkimPositionalRefinement.lean:8`), `Blanc.Lift.UniswapV2Pair.burnRaw_source_authentic` (`Blanc/Lift/UniswapV2Pair/BurnPositionalRefinement.lean:8`), `Blanc.Lift.UniswapV2Pair.transfer_bytecode_exact_consumes` (`Blanc/Lift/UniswapV2Pair/TransferSource.lean:719`), `Blanc.Lift.UniswapV2Pair.approve_bytecode_exact_consumes` (`Blanc/Lift/UniswapV2Pair/ApproveSource.lean:380`), `Blanc.Lift.UniswapV2Pair.transferFrom_bytecode_exact_consumes` (`Blanc/Lift/UniswapV2Pair/TransferFromSource.lean:961`), `Blanc.Lift.UniswapV2Pair.initialize_bytecode_exact_consumes` (`Blanc/Lift/UniswapV2Pair/InitializeSource.lean:292`), `Blanc.Lift.UniswapV2Pair.permit_bytecode_admitted_consumes` (`Blanc/Lift/UniswapV2Pair/PermitSourceOccurrence.lean:170`), `Blanc.Lift.UniswapV2Pair.staticView_bytecode_inv` (`Blanc/Lift/UniswapV2Pair/StaticViewClassify.lean:1268`) | Frame / refinement | CODE; covered fork; fresh pc-0 entry; INIT-shaped `WriterRep` of the entry storage; HASH-T over the run's own key universe (transfer, approve, transferFrom and permit: freshness of their own touched rows); `burnRaw_source_authentic` also takes the pair's own balance key as tracked and requires every nested frame at the pair to decode only keys of that universe (`LockedGood`, with the keys of its static views in `staticViewDecodedKeys`) | The frame theorems are the ground the history rows are built on. `permit` uses the **result** of the modeled ECRECOVER precompile as an input: value zero, at least 228 calldata bytes, non-static, before the deadline, and a successful recovery call whose copied word is the nonzero owner; unforgeability of signatures is not claimed. The admitted `permit` route additionally requires a separated universe, the installed runtime identity and descendant-view coverage; the admitted suppliers use it with `LockedAuth`. A successful `mint` frame also leaves every other account's storage unchanged [`Blanc.Lift.UniswapV2Pair.mint_bytecode_exact_consumes_own` (`Blanc/Lift/UniswapV2Pair/MintPositionalRefinement.lean:48`)] |
| Model laws of the typed source model (the functional model the replay folds over): the first mint prices `⌊√(a0·a1)⌋ − 1000`, locks 1000 at address 0 and credits the recipient the rest, with the Babylonian loop equal to `Nat.sqrt` over the full domain; a later mint issues `min(⌊a0·T/r0⌋, ⌊a1·T/r1⌋)` (with `T` the supply after the fee mint); a burn pays and returns `⌊L·b_i/T⌋` of each token by exactly the two transfer requests; a swap succeeds only if (and, on the canonical transcript, whenever) some output is positive, the outputs are below the reserves, `to` is neither token, the post-callback balances fit `uint112`, some input is positive and the fee-adjusted check holds, and then stores exactly those balances as reserves; the callback request is present iff `data` is nonempty, with exact calldata | `Blanc.Lift.UniswapV2Pair.runTyped_mint_initial` (`Blanc/Lift/UniswapV2Pair/Properties.lean:3196`), `Blanc.Lift.UniswapV2Pair.runTyped_mint_initial_floor` (`Blanc/Lift/UniswapV2Pair/Properties.lean:3209`), `Blanc.Lift.UniswapV2Pair.mintAmount_initial_spec` (`Blanc/Lift/UniswapV2Pair/Properties.lean:2762`), `Blanc.BabylonianSqrt.sourceResult_eq_sqrt` (`Blanc/Lift/BabylonianSqrt.lean:106`), `Blanc.Lift.UniswapV2Pair.runTyped_mint_later` (`Blanc/Lift/UniswapV2Pair/PropertiesMintBurn.lean:310`), `Blanc.Lift.UniswapV2Pair.runTyped_burn_payout` (`Blanc/Lift/UniswapV2Pair/PropertiesMintBurn.lean:924`), `Blanc.Lift.UniswapV2Pair.runTyped_swap_success_reserves` (`Blanc/Lift/UniswapV2Pair/PropertiesSwap.lean:561`), `Blanc.Lift.UniswapV2Pair.runTyped_swap_canonical_success` (`Blanc/Lift/UniswapV2Pair/PropertiesSwap.lean:1042`), `Blanc.Lift.UniswapV2Pair.runTyped_swap_callback_request` (`Blanc/Lift/UniswapV2Pair/PropertiesSwap.lean:1664`) | Model / safety | the model only (the swap and burn statements are conditioned on the successful run's own answers) | Bridged to the bytes by the frame refinement and history rows above. The bytecode's own Babylonian loop is walked exactly [`Blanc.Lift.UniswapV2Pair.sqrt_of_run` (`Blanc/Lift/UniswapV2Pair/SqrtWalk.lean:589`)]. These are model facts: that real tokens give the answers a premise names is not proved |

**Statement controls.** Each is a single kernel fact or a mutation that must make
a statement fail; they say the statements above are not vacuous or insensitive.

| What it shows | Control | Altitude |
|---|---|---|
| NoShrink is needed: on a reachable sync, a token answer below the stored reserve is accepted by the model and the share-value inequality then fails | `Blanc.Lift.UniswapV2Pair.ModelControls.noShrink_required` (`Blanc/Lift/UniswapV2Pair/ModelControls.lean:115`) | typed model, kernel evaluation of the production driver |
| The model is sensitive to its arithmetic: a mint that rounds up breaks the fee-off share-value inequality on a state it reaches; a fee constant other than 997 and a burn that rounds toward the user each give a different accepted run | `Blanc.Lift.UniswapV2Pair.ModelControls.mintRoundUp_breaks_feeOff_product` (`Blanc/Lift/UniswapV2Pair/ModelControls.lean:216`), `Blanc.Lift.UniswapV2Pair.ModelControls.feeMutant_disagrees` (`Blanc/Lift/UniswapV2Pair/ModelControls.lean:269`), `Blanc.Lift.UniswapV2Pair.ModelControls.burnRoundUp_disagrees` (`Blanc/Lift/UniswapV2Pair/ModelControls.lean:291`) | typed model; mutated drivers compose the unchanged transitions with one changed arithmetic function |
| The burn-rounding mutant disagrees with production on a state reached from the deployment image, in the typed model. No frame-level form of this control is claimed | `Blanc.Lift.UniswapV2Pair.RefinementControls.burn_witness_disagrees` (`Blanc/Lift/UniswapV2Pair/RefinementControls.lean:62`) | typed model (closed) |
| The oracle law needs the `uint32` wrap: a reached update at a block timestamp past `2^32` satisfies the exact law and refutes the law with the wrap removed | `Blanc.Lift.UniswapV2Pair.OracleControls.oracle_law_requires_timestamp_wrap` (`Blanc/Lift/UniswapV2Pair/OracleControls.lean:50`); the bytecode's own wrap `Blanc.Lift.UniswapV2Pair.update_timestamp_wrap_control` (`Blanc/Lift/UniswapV2Pair/UpdateArithmetic.lean:166`) | typed model; the second is a raw walk |
| The `uint112` guard is load-bearing: a balance of `2^112` passes the fee-adjusted check and the typed swap still fails; every successful raw swap run observes balances below `2^112` | `Blanc.Lift.UniswapV2Pair.swap_uint112_control` (`Blanc/Lift/UniswapV2Pair/PropertiesSwap.lean:1151`), `Blanc.Lift.UniswapV2Pair.swap_bytecode_uint112_control` (`Blanc/Lift/UniswapV2Pair/SwapControls.lean:28`); the update walks `Blanc.Lift.UniswapV2Pair.update_uint112_overflow_control` (`Blanc/Lift/UniswapV2Pair/UpdateWalk.lean:108`), `Blanc.Lift.UniswapV2Pair.update_overflow_uint112_kernel_control` (`Blanc/Lift/UniswapV2Pair/UpdateOverflowWalk.lean:392`) | typed model, and universal over successful raw runs (no concrete reverting run is exhibited) |
| HASH-T is load-bearing for the ledger: a duplicated key breaks the footprint sum, and a successful raw `approve` whose allowance slot aliases a tracked balance slot (a hypothesis; no Keccak collision is asserted) ends outside raw ledger conservation | `Blanc.Lift.UniswapV2Pair.footprintSum_dup_breaks_ledger` (`Blanc/Lift/UniswapV2Pair/PropertiesLedger.lean:76`), `Blanc.Lift.UniswapV2Pair.LedgerKeyControl.approve_storage_alias_breaks_ledger` (`Blanc/Lift/UniswapV2Pair/LedgerKeyControl.lean:38`) | model; EVM-conditional on the alias |
| The callee premises are needed: if a token or the callback recipient holds code that reverts, no raw `sync`, `skim`, `mint` or `swap` run succeeds, whatever the gas; premise-free `sync` liveness is refuted on the family of worlds that deployment and `initialize` produce | `Blanc.Lift.UniswapV2Pair.sync_no_success_of_reverting_token0` (`Blanc/Lift/UniswapV2Pair/CalleeControls.lean:51`), `Blanc.Lift.UniswapV2Pair.skim_no_success_of_reverting_token0` (`Blanc/Lift/UniswapV2Pair/CalleeControls.lean:103`), `Blanc.Lift.UniswapV2Pair.mint_no_success_of_reverting_token0` (`Blanc/Lift/UniswapV2Pair/CalleeControls.lean:123`), `Blanc.Lift.UniswapV2Pair.swap_no_success_of_reverting_token0` (`Blanc/Lift/UniswapV2Pair/CalleeControlsSwap.lean:122`), `Blanc.Lift.UniswapV2Pair.swap_no_success_of_reverting_callback` (`Blanc/Lift/UniswapV2Pair/CalleeControlsSwap.lean:207`), `Blanc.Lift.UniswapV2Pair.sync_liveness_refuted` (`Blanc/Lift/UniswapV2Pair/CalleeControlsReach.lean:162`) | EVM, universal over raw runs for one concrete callee code |
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
(for `sync`, `mint`, `swap`, `burn`, `skim`, `permit` and `initialize` the
conclusion is `PairAdmittedOutcome`: the new run is consumed by the same recursively
admitted positional consumption as the history's steps, from the history's replayed
model state, and the history's key universe is extended by the new run's own keys
without replaying the history; the common step is `pair_live_outcome`. The
`transfer`, `approve` and `transferFrom` row concludes the writer's own result
directly, with exact storage, logs and return word (`LedgerWriter.Result`), over the
same admitted history replay.)

| Level | Claim | Theorem | Cost / gas formula | Premises beyond a fresh frame |
|---|---|---|---|---|
| Reachable state | `transfer`, `approve`, `transferFrom` | `Blanc.Lift.UniswapV2Pair.pair_history_writer_live` (`Blanc/Lift/UniswapV2Pair/PairHistoryLive.lean:231`) | `LedgerWriter.cost`: `approve` `sstoreCost + 2342`; `transfer` the source, debit, recipient and credit slot charges `+ 2740`; `transferFrom` `transferFromPublicGas` [`Blanc.Lift.UniswapV2Pair.LedgerWriter.cost` (`Blanc/Lift/UniswapV2Pair/ReplayWriterGas.lean:35`)] | the history's CODE, INIT, HASH-T; HASH-T freshness of the call's rows against the history's; model acceptance at the replayed state; a residual above the 2,300-gas stipend. **No callee** |
| Reachable state | `sync`, whenever the lock is open and the reserve update accepts the two actual `balanceOf(pair)` answers | `Blanc.Lift.UniswapV2Pair.pair_history_sync_live` (`Blanc/Lift/UniswapV2Pair/PairHistoryLive.lean:386`) | `syncCalleePrefixGas sevm pre callGas0 + 15 + 229` [`Blanc.Lift.UniswapV2Pair.syncCalleePrefixGas` (`Blanc/Lift/UniswapV2Pair/SyncWalk.lean:1263`)] | the two token `STATICCALL`s with their replies and returned gas (ENV); residual sentries |
| Reachable state | `mint`, on a transcript whose three answers (both `balanceOf(pair)` replies and the factory's `feeTo`) are the frame's actual answers | `Blanc.Lift.UniswapV2Pair.pair_history_mint_live` (`Blanc/Lift/UniswapV2Pair/PairHistoryLive.lean:565`) | `callee.gas + 228` [`Blanc.Lift.UniswapV2Pair.MintPrefixCallee.gas` (`Blanc/Lift/UniswapV2Pair/MintForwardAccept.lean:496`)]; returns the liquidity word | the three `STATICCALL`s (`Blanc.Lift.UniswapV2Pair.MintPrefixCallee` (`Blanc/Lift/UniswapV2Pair/MintForwardAccept.lean:457`)); HASH-T freshness of the LP rows of address 0, the recipient and the `feeTo` answer |
| Reachable state | `swap`, with or without the flash callback | `Blanc.Lift.UniswapV2Pair.pair_history_swap_live` (`Blanc/Lift/UniswapV2Pair/PairHistoryLive.lean:692`) | `swapFrontTransferGas … + swapPrefixGas … + 279 + 166` [`Blanc.Lift.UniswapV2Pair.swapFrontTransferGas` (`Blanc/Lift/UniswapV2Pair/SwapForwardFront.lean:43`), `Blanc.Lift.UniswapV2Pair.swapPrefixGas` (`Blanc/Lift/UniswapV2Pair/SwapForwardPrefix.lean:179`)] | the optional transfer `CALL`s and the callback `CALL` (present iff their amount or the data is nonzero) and the two post-callback `balanceOf(pair)` `STATICCALL`s (`Blanc.Lift.UniswapV2Pair.SwapFrontForwardEnv` (`Blanc/Lift/UniswapV2Pair/SwapForwardFront.lean:56`), `Blanc.Lift.UniswapV2Pair.SwapBackCalleeEnv` (`Blanc/Lift/UniswapV2Pair/SwapForwardAccept.lean:107`)); the decoded swap accepted by the model on those answers (`SwapContextConditions`, `SwapModelConditions`); the proof builds the run with `Blanc.Lift.UniswapV2Pair.swap_bytecode_forward_consumes` (`Blanc/Lift/UniswapV2Pair/SwapForward.lean:194`), whose own conclusion, under its HASH-T premises, is one full `SwapPositionalCanonicalResult`; this row's statement exports the run and `PairAdmittedOutcome` only |
| Reachable state | `burn` | `Blanc.Lift.UniswapV2Pair.pair_history_burn_live` (`Blanc/Lift/UniswapV2Pair/PairHistoryLive.lean:832`) | `BurnForwardEnv.gas` = the initial callees' charge `+ 249` [`Blanc.Lift.UniswapV2Pair.BurnForwardEnv.gas` (`Blanc/Lift/UniswapV2Pair/BurnForwardBody.lean:490`)]; returns both amounts | the two initial `balanceOf(pair)` `STATICCALL`s, the `feeTo` `STATICCALL`, both transfer `CALL`s and both final `balanceOf(pair)` `STATICCALL`s (`Blanc.Lift.UniswapV2Pair.BurnForwardEnv` (`Blanc/Lift/UniswapV2Pair/BurnForwardBody.lean:479`)); HASH-T freshness of the pair's own LP row and the `feeTo` answer's |
| Reachable state | `skim` | `Blanc.Lift.UniswapV2Pair.pair_history_skim_live` (`Blanc/Lift/UniswapV2Pair/PairHistoryLive.lean:933`) | `SkimForwardEnv.gas`, a closed sum of the lock, cache and request charges and the gas forwarded to the first token [`Blanc.Lift.UniswapV2Pair.SkimForwardEnv.gas` (`Blanc/Lift/UniswapV2Pair/SkimForwardAccept.lean:146`)] | both `balanceOf(pair)` `STATICCALL`s and both transfer `CALL`s (`Blanc.Lift.UniswapV2Pair.SkimForwardEnv` (`Blanc/Lift/UniswapV2Pair/SkimForwardAccept.lean:25`)); HASH-T over the first transfer `CALL`: the mapping rows the pair's own frames decode inside it are fresh (`Blanc.Lift.UniswapV2Pair.SkimForwardEnv.FirstCallFresh` (`Blanc/Lift/UniswapV2Pair/SkimForwardKeep.lean:65`)). That this `CALL` leaves the lock-guarded fields unchanged is **derived, not assumed** (`Blanc.Lift.UniswapV2Pair.SkimForwardEnv.firstCall_keeps` (`Blanc/Lift/UniswapV2Pair/SkimForwardKeep.lean:89`)) |
| Reachable state | `permit`, on a transcript whose recovered address is the frame's actual `ECRECOVER` answer, whenever the model accepts it | `Blanc.Lift.UniswapV2Pair.pair_history_permit_live` (`Blanc/Lift/UniswapV2Pair/PairHistoryLiveAdmin.lean:292`), from the frame theorem `Blanc.Lift.UniswapV2Pair.permit_bytecode_live_raw` (`Blanc/Lift/UniswapV2Pair/PermitEntries.lean:932`) | `callGas + permitNonceStoreCharge + permitNonceCharge + 1137` | the recovery precompile `STATICCALL` with its reply and returned gas (ENV); residual sentries; HASH-T freshness of the call's rows |
| Reachable state | `initialize`, whenever the model accepts it (the caller is the stored factory) | `Blanc.Lift.UniswapV2Pair.pair_history_initialize_live` (`Blanc/Lift/UniswapV2Pair/PairHistoryLiveAdmin.lean:186`), from the frame theorem `Blanc.Lift.UniswapV2Pair.initialize_bytecode_live_raw` (`Blanc/Lift/UniswapV2Pair/InitializeEntries.lean:360`) | `G + initializeStorageCharge + 377` | residual sentries; HASH-T freshness of the call's rows. **No callee** |

The views have frame-level exact and live theorems
(`Blanc.Lift.UniswapV2Pair.getterScalar_bytecode_live` (`Blanc/Lift/UniswapV2Pair/GetterScalarWalk.lean:70`),
`Blanc.Lift.UniswapV2Pair.getReserves_bytecode_live` (`Blanc/Lift/UniswapV2Pair/GetterStorageReservesWalk.lean:55`),
`Blanc.Lift.UniswapV2Pair.getterString_bytecode_live` (`Blanc/Lift/UniswapV2Pair/GetterStringWalk.lean:915`),
for the `balanceOf` and `nonces` mappings `Blanc.Lift.UniswapV2Pair.singleMapping_bytecode_live` (`Blanc/Lift/UniswapV2Pair/GetterStorageMappingWalk.lean:89`),
and for `allowance` `Blanc.Lift.UniswapV2Pair.allowance_bytecode_live` (`Blanc/Lift/UniswapV2Pair/GetterStorageMappingWalk.lean:219`)).
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
premise of `pair_history_initialized`. `Blanc.Lift.UniswapV2Pair.Creation.pair_create2_initialize_live` (`Blanc/Lift/UniswapV2Pair/Creation/DeployInit.lean:246`)
also constructs that run: for an `initialize` frame called by the creator on that
storage (value 0, non-static, two calldata words, residual gas meeting the two
store sentries, which any 2,292 gas does), a successful run exists at its closed
gas, so the checkpoint is reached, not assumed. No hash premise. The exhibit instance
`Blanc.Lift.UniswapV2Pair.Creation.exhibit_create2` (`Blanc/Lift/UniswapV2Pair/Creation/DeployInit.lean:171`) deploys from the factory
with salt `keccak(USDC ‖ WETH)`, and the exhibit pair's address is the `CREATE2`
address of the factory, that salt and the creation code
[`Blanc.Lift.UniswapV2Pair.Creation.pairAddress_eq` (`Blanc/Lift/UniswapV2Pair/Creation/Facts.lean:104`)], by kernel evaluation. General form
`Blanc.Lift.UniswapV2Pair.Creation.pair_create2` (`Blanc/Lift/UniswapV2Pair/Creation/Deploy.lean:177`).

**Fork coverage.** The history, replay and liveness theorems assume or derive
`CoveredFork`; the deployment theorems quantify over covered forks.

**Non-claims.** That real tokens satisfy NoShrink (the WETH9 half is a theorem only
under the premises of Section 5.9) or that a factory answers `feeTo = 0`; that any
price, the TWAP or the economics of the pool are fair or safe; any use of the
factory's bytecode by the theorems of this section (the factory is a premise-level
message source here, and the fact that the factory issues the `initialize` call is a
premise of the deployment theorems, its frame environment, not a consequence of the
lifted factory code); historical inclusion of the deployment; unforgeability of
`permit` signatures; that the exhibit pair's current mainnet state satisfies the
joint checkpoint of Section 5.9, so its WETH9 side is not discharged for the live
pool; transaction-level liveness; frames that were rolled back; the real transaction
history of the exhibit pair.

### 5.9 Uniswap V2 Pair × WETH9: two deployed runtimes in one history

Sections 5.1 and 5.8 each describe one contract; in Section 5.8 a pair's token
answers enter as premises (NoShrink and the liveness callee records). This section
composes the two certified runtimes over **one** configured history. When one of a
pair's two tokens is WETH9 (an address holding the certified WETH9 runtime), WETH9's
half of those premises becomes a theorem, and the other token's half stays a named
premise (when that other token is USDC, Section 5.10 discharges it from USDC's certified runtimes, under the premises stated there). The statements cover every pair that runs the certified Pair runtime, with
WETH9 as `token0` or `token1` (`TokenSide`), whose stored `factory` address holds the
certified Uniswap V2 Factory runtime at the checkpoint, over any configured history
that starts from a world satisfying `JointCheckpoint`. The joint invariant is proved
once against a contract-neutral token interface, and WETH9 is its first instance; the
WETH9 statements are that proof instantiated.

**Token interface and WETH9 as its instance**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| The laws a token's pure book (an abstract ledger, its step on one entered frame's message, the decoded operation, balances, allowances, and a well-formedness predicate `Good`) must satisfy: a step from a good ledger lowers a holder's balance only if its caller is the holder or a spender to which the holder had granted a positive allowance; only the owner raises its own allowances; a holder's own `balanceOf`, `transfer` or credit-only call debits it at most by the declared amount and raises none of its allowances; a step decoded as `transfer` to someone else debits the caller exactly; a good ledger's balances are below 2^256 | `Blanc.Lift.Token.BookLaws` (`Blanc/Lift/Token/Core.lean:62`) over `Blanc.Lift.Token.Book` (`Blanc/Lift/Token/Core.lean:48`) | Interface / definition | — | No storage layout appears |
| The token core, what a token's **address** answers along a configured history: under a trace-local premise `Hist` the instance chooses, at the entry of every settled frame the booked ledger is the book run over exactly the non-static entry frames at the token before it, and at the end over all of them; the ledger is good at the checkpoint and at every settled frame's entry; a settled `balanceOf(h)` entry frame, static or not, answers the booked balance for every holder the instance vouches for; a settled `transfer` entry frame answers empty output or a nonzero first word; a settled frame at the token that is not an entry frame (`IsEntry`: storage owner and code address both the token) is a child only of settled frames at the token | `Blanc.Lift.Token.Core` (`Blanc/Lift/Token/Core.lean:98`); entry frames `Blanc.Lift.Token.IsEntry` (`Blanc/Lift/Token/Core.lean:85`) | History / interface | the instance's own `Hist` | Further facts are separate structures over the book or the core, added without editing it: `Blanc.Lift.Token.Erc20Abi` (`Blanc/Lift/Token/Abi.lean:17`) (the standard `transfer` and `balanceOf` selectors decode as those operations for every calldata of at least 68 and 36 bytes respectively and below 2^256), `SelfCaller` and `TransferLive` below. The non-entry clause admits a proxy's delegated implementation frames |
| Facet: every entry-frame child of a settled non-static frame at the token has the token itself as caller | `Blanc.Lift.Token.SelfCaller` (`Blanc/Lift/Token/SelfCaller.lean:18`) | History / interface | the core's `Hist` | No forwarded caller reaches a booked entry |
| Facet: at any world the instance accepts, a fresh entry frame (value 0, non-static, covered fork, the token's code) decoding a `transfer` of at most the caller's booked balance runs to success at an exact instance-given cost, answers the word 1, leaves an accepted world, and, when the recipient is not the caller, debits the caller exactly | `Blanc.Lift.Token.TransferLive` (`Blanc/Lift/Token/Core.lean:145`) | Frame / interface | the instance's world and frame conditions; ENV: gas at least the cost plus the 2,300-gas stipend | |
| WETH9's book (its pure ledger model read through the deployed dispatcher's own decoder, as natural numbers; good while the total fits a word) satisfies the laws | `Blanc.Composition.Weth9Token.weth9Book_laws` (`Blanc/Composition/Weth9Token.lean:337`), the book `Blanc.Composition.Weth9Token.weth9Book` (`Blanc/Composition/Weth9Token.lean:33`); the ABI facet `Blanc.Composition.UniswapV2PairWeth9Joint.weth9Book_erc20Abi` (`Blanc/Composition/UniswapV2PairWeth9Joint.lean:33`) | Model / safety | none | A zero-value `deposit` is read as credit-only, any other `deposit` as an unclassified operation |
| WETH9 at any address is an instance of the core: `Hist` is `Weth9Hist`, exactly the four premises of `weth9_history_committed`; the booked ledger is the footprint ledger over the history's key universe; the holders vouched for are its tracked balance rows | `Blanc.Composition.Weth9Token.weth9Core` (`Blanc/Composition/Weth9TokenCore.lean:253`) | History / instance | CODE; ARITH `SumNof`; INIT `FootInv K₀`; HASH-T `KeysFresh K₀ (historyTouchedKeys ca trace)` | Built from the WETH9 history theorems of Section 5.1 and the deployed code's `balanceOf` and `transfer` outputs, static frames included |
| WETH9 discharges the `SelfCaller` facet: its code spawns only by `CALL` and `STATICCALL`, so every child of a settled non-static WETH9 frame has WETH9 as caller | `Blanc.Composition.Weth9Token.weth9SelfCaller` (`Blanc/Composition/Weth9TokenCore.lean:269`) | History / instance | as `weth9Core` | |
| WETH9's transfer facet: the accepted worlds hold WETH9's code and `FootInv U`; the frame's five `frameKeys` lie in `U` and its calldata is below 2^256; the cost is `transferGas` | `Blanc.Composition.Weth9Token.weth9TransferLive` (`Blanc/Composition/Weth9Token.lean:453`) | Frame / instance | INIT `FootInv U` at the world; HASH-T `frameKeys sevm ⊆ U`; ENV gas | From the deployed code's frame-level `transfer` run |

**The factory lift**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| The certificate of the 13,859-byte factory runtime is accepted | `Blanc.Lift.UniswapV2Factory.cert_check` (`Blanc/Lift/UniswapV2Factory/Check.lean:121`), the runtime `Blanc.Lift.UniswapV2Factory.factoryCode` (`Blanc/Lift/UniswapV2Factory/Input.lean:163`) as the code image `Blanc.Lift.UniswapV2Factory.factorySem` (`Blanc/Lift/UniswapV2Factory/CallShape.lean:385`) | Bytes / certificate | none | Kernel decision against the literal bytes (Section 2) |
| Every direct child of a frame running the factory code from pc 0 on a covered fork is static, or targets address 0, or targets an address that had no code when the frame began; the target operand of each of its `CALL`s, after the 160-bit mask, is 0 or such an address | `Blanc.Lift.UniswapV2Factory.factory_children_fresh` (`Blanc/Lift/UniswapV2Factory/CallShape.lean:326`), `Blanc.Lift.UniswapV2Factory.factory_call_target` (`Blanc/Lift/UniswapV2Factory/CallShape.lean:291`) | Frame / safety | CODE; covered fork | The only `CALL` sites are the `initialize` calls of the factory's pair-creation entry point; the certificate's walk tracks their target operand to the result of the preceding `CREATE2` |
| Over any configured history whose checkpoint has the Pair runtime at `pair ≠ 0` and the factory runtime at the address a Pair model state names as `factory`, that address not being the system address: no settled non-static frame at `pair` has the factory as caller | `Blanc.Composition.UniswapV2FactoryQuiet.pair_history_factoryQuiet` (`Blanc/Composition/UniswapV2FactoryQuiet.lean:40`) | History / safety | CODE (both runtimes at the checkpoint); ENV: `pair ≠ 0`, the factory is not the system address | The Pair's `initialize` has no one-shot guard, so a factory call could replace its stored tokens; this theorem is why the composed statements need no premise about the factory's behaviour. The factory's `feeTo` answers are not discharged from the lift |

**The joint invariant**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| For any token core with `BookLaws`, the ABI facet and `SelfCaller`: over any configured history from a checkpoint where the Pair runtime is at `pair` and its storage represents an unlocked model state whose token on `side` is `T`, and where `JointAt` holds (the side's stored reserve is at most `T`'s booked balance of the pair, and the pair has granted no booked allowance): at the entry of every settled frame not enclosed by a settled non-static frame at the pair (the committed points at which the pair is unlocked), the pair's storage represents an unlocked model state with that token and `JointAt` holds there; at the history's end, over the pair's full replay, `JointAt` holds at the final state | `Blanc.Composition.PairTokenJoint.pair_token_joint` (`Blanc/Composition/PairTokenJoint.lean:126`), the relation `Blanc.Composition.PairTokenJoint.JointAt` (`Blanc/Composition/PairTokenJointAt.lean:20`) | History / safety | CODE (the Pair runtime); INIT `WriterRep`, unlocked, `JointAt`, `token0 ≠ token1`; ENV: `pair ≠ T`, the pair is not the system address and is a holder the core vouches for; HASH-T `WriterFreshKeys` over the pair's touched rows; the core's `Hist`; ENV (trace-local): no settled non-static pair frame has the factory as caller, and at every execution step of every settled non-static pair frame `T`'s code is no EIP-7702 designator and `T` is not a precompile | No token storage layout appears. Reentrant callbacks during `swap` lie inside the pair's frames and are consumed by its positional replay. The factory and token-entry premises are discharged in the WETH9 form below |
| Under the same premises, every outer pair step of the history satisfies the token's half of NoShrink, over the replay of `pair_history_committed` | `Blanc.Composition.PairTokenJoint.pair_token_noShrinkSide` (`Blanc/Composition/PairTokenJoint.lean:165`), the half `Blanc.Lift.UniswapV2Pair.sourceReplayNoShrinkSide` (`Blanc/Lift/UniswapV2Pair/PropertiesSides.lean:128`) | History / safety | as `pair_token_joint` | NoShrink is exactly the conjunction of its two halves [`Blanc.Lift.UniswapV2Pair.entryNoShrink_iff_sides` (`Blanc/Lift/UniswapV2Pair/PropertiesSides.lean:117`), `Blanc.Lift.UniswapV2Pair.sourceReplayNoShrink_iff_sides` (`Blanc/Lift/UniswapV2Pair/PropertiesSides.lean:142`)]; the Section 5.8 statements are unchanged |
| **The joint invariant for WETH9**, either side: from `JointCheckpoint` at the checkpoint, at every such committed point the pair is unlocked with WETH9 on `side`, its reserve on that side is at most WETH9's booked balance of the pair, and the pair has granted no booked WETH9 allowance; at the history's end the reserve is at most the pair's stored WETH9 balance word and every tracked WETH9 allowance row of the pair is zero | `Blanc.Composition.UniswapV2PairWeth9Joint.pair_weth9_joint` (`Blanc/Composition/UniswapV2PairWeth9Joint.lean:127`); the checkpoint `Blanc.Composition.UniswapV2PairWeth9Joint.JointCheckpoint` (`Blanc/Composition/UniswapV2PairWeth9Checkpoint.lean:29`) | History / safety | INIT `JointCheckpoint`; HASH-T `WriterFreshKeys` over the pair's touched rows and `KeysFresh` over WETH9's touched keys; CODE: the factory runtime at the checkpoint model state's `factory`; ENV: that address is not the system address | **No premise about WETH9's answers.** The generic form's factory premise comes from `pair_history_factoryQuiet`, its token-entry premise from WETH9's installed code and the checkpoint's no-precompile field |

**WETH9's half of NoShrink discharged: share value**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| For every pair with WETH9 on `side`: the replay of `pair_history_committed` exists, and if the fee-off condition and **the other token's** half of NoShrink hold along it (`sourceReplayAnswersSide side.other`), then every committed state change with positive incoming supply keeps `r0·r1·T'² ≤ r0'·r1'·T²` | `Blanc.Composition.UniswapV2PairWeth9ShareValue.pair_weth9_history_feeOff_product` (`Blanc/Composition/UniswapV2PairWeth9ShareValue.lean:27`); generic `Blanc.Composition.PairTokenShareValue.pair_token_feeOff_product` (`Blanc/Composition/PairTokenShareValue.lean:108`) | History / safety | as `pair_weth9_joint` | Compared with the single-pair replay law `Blanc.Lift.UniswapV2Pair.SourceReplay.feeOff_product` (`Blanc/Lift/UniswapV2Pair/SourceReplay.lean:94`), WETH9's half of the antecedent is gone; only the fee-off condition and the other token's half remain |
| The same with the protocol fee on: with the other token's half (`sourceReplayNoShrinkSide side.other`) as the only antecedent, every committed state change with positive incoming supply keeps `r0·r1·T'² ≤ r0'·r1'·(T + F)²`, `F` the step's exact fee mint | `Blanc.Composition.UniswapV2PairWeth9ShareValue.pair_weth9_history_feeOn_product` (`Blanc/Composition/UniswapV2PairWeth9ShareValue.lean:58`); generic `Blanc.Composition.PairTokenShareValue.pair_token_feeOn_product` (`Blanc/Composition/PairTokenShareValue.lean:145`) | History / safety | as `pair_weth9_joint` | |

**WETH9's callee records discharged: liveness.** Each row restates the Section 5.8
row named in its first column from the premises of `pair_weth9_joint`, for a fresh
frame at the history's future state, and concludes what that row concludes (a run at
a closed gas expression and `PairAdmittedOutcome`). WETH9's callee records are not
premises: each is fixed to the run that WETH9's certified code performs at that point
(its result and call gas are defined from values bound earlier in the statement), and
its own premises are discharged from the history: WETH9's code at the token address
the pair loads, WETH9 not a precompile, and, for a transfer, the pair's WETH9 balance
covering the amount, by the joint invariant. **No remaining premise mentions WETH9's
answers.** What remains is listed per row. Every `sync`, `mint`, `burn` and `skim` row
also takes the frame's call depth `≠ 0` and, for each WETH9 call, that its call gas is a
word and leaves the 63/64 room WETH9's run needs (ENV: gas); the `swap` rows derive the
depth and state their gas premises in their own rows.

| Section 5.8 row | WETH9 side | Theorem | Level / kind | What remains beyond the common premises |
|---|---|---|---|---|
| `sync` | token0 | `Blanc.Composition.UniswapV2PairWeth9Joint.pair_weth9_history_sync_live_zero` (`Blanc/Composition/UniswapV2PairWeth9SyncLive.lean:102`) | History / live | ENV: the other token's `balanceOf(pair)` record; the pair's residual sentry |
| `sync` | token1 | `Blanc.Composition.UniswapV2PairWeth9Joint.pair_weth9_history_sync_live_one` (`Blanc/Composition/UniswapV2PairWeth9SyncLive.lean:176`) | History / live | as above |
| `mint` | token0 | `Blanc.Composition.UniswapV2PairWeth9Joint.pair_weth9_history_mint_live_zero` (`Blanc/Composition/UniswapV2PairWeth9MintLive.lean:157`) | History / live | ENV: the other token's record, the factory's `feeTo` record and the pair's charges; HASH-T: the LP rows' freshness |
| `mint` | token1 | `Blanc.Composition.UniswapV2PairWeth9Joint.pair_weth9_history_mint_live_one` (`Blanc/Composition/UniswapV2PairWeth9MintLive.lean:253`) | History / live | as above |
| `burn` | token0 | `Blanc.Composition.UniswapV2PairWeth9Joint.pair_weth9_history_burn_live_zero` (`Blanc/Composition/UniswapV2PairWeth9BurnLive.lean:91`) | History / live | WETH9's initial query, transfer and final query discharged. ENV: the other token's three records, the factory record, the pair's charges and sentries; HASH-T: the LP rows' freshness |
| `burn` | token1 | `Blanc.Composition.UniswapV2PairWeth9Joint.pair_weth9_history_burn_live_one` (`Blanc/Composition/UniswapV2PairWeth9BurnLiveOne.lean:117`) | History / live | as the token0 row, and **HASH-T over child frames**: over WETH9's keys of the two `STATICCALL` children before the other token's transfer (its initial query and the factory query), and over the keys the other token's transfer child touches, against WETH9's key universe and against the pair's rows |
| `skim` | token0 | `Blanc.Composition.UniswapV2PairWeth9Joint.pair_weth9_history_skim_live_zero` (`Blanc/Composition/UniswapV2PairWeth9SkimLive.lean:222`) | History / live | ENV: the other token's query and transfer records, the lock sentries, the frame non-static; HASH-T: `FirstCallFresh` |
| `skim` | token1 | `Blanc.Composition.UniswapV2PairWeth9Joint.pair_weth9_history_skim_live_one` (`Blanc/Composition/UniswapV2PairWeth9SkimLiveOne.lean:83`) | History / live | as the token0 row, and **HASH-T over child frames**: over WETH9's keys of the other token's query child and transfer child, and over the pair's rows of that transfer child. That the other token's transfer leaves the locked pair's `reserve1` unchanged is derived, under `FirstCallFresh` |
| `swap` | token0 | `Blanc.Composition.UniswapV2PairWeth9Joint.pair_weth9_history_swap_live_zero` (`Blanc/Composition/UniswapV2PairWeth9SwapLiveZero.lean:159`) | History / live | Both outputs allowed; WETH9's `transfer` and post-callback `balanceOf` records discharged. ENV: the other token's `transfer` and `balanceOf` records, the callback, the pair's gas sentries; the frame's gas is a word, at least 3,200 gas remain after WETH9's transfer when it is taken, and the first query's `GAS` word is a word |
| `swap` | token1, only WETH9 paid out (`amount0Out = 0`) | `Blanc.Composition.UniswapV2PairWeth9Joint.pair_weth9_history_swap_live_one` (`Blanc/Composition/UniswapV2PairWeth9SwapLive.lean:431`) | History / live | ENV: the other token's `balanceOf` record, the callback, the pair's gas sentries; the frame's gas is a word, the callback branch has at least 3,200 gas, the second query's `GAS` word is a word |
| `swap` | token1, both outputs allowed | `Blanc.Composition.UniswapV2PairWeth9Joint.pair_weth9_history_swap_live_one_both` (`Blanc/Composition/UniswapV2PairWeth9SwapLive.lean:173`) | History / live | as the previous row, and the other token's `transfer` record when it is paid; HASH-T over the keys that transfer child touches, against WETH9's key universe and against the pair's rows; the WETH9 `CALL`'s gas word after it |

In every row each WETH9 record is fixed by equations whose right sides read only the
row's free values and records fixed before it. For the three `swap` rows, the token1
`burn` row and the token1 `skim` row, the four lemmas in the controls table below show
that these equations never constrain the free values; for the other rows (`sync`,
`mint`, and the token0 `burn` and `skim` rows) no such lemma is stated.

**Deployment**

| Claim | Theorem | Kind | Premises | Notes |
|---|---|---|---|---|
| For every covered fork: the Pair's `CREATE2` step (as `pair_create2_initialize_live`) runs and pushes the new address; and for every `initialize` frame the creator sends to that address naming WETH9 as one of its tokens and a different other token, at a world that keeps the deployment's WETH9 storage and holds WETH9's code, its footprint INIT with the new address's balance row tracked, and representable total ether, a successful run exists at its closed gas and ends in a world satisfying `JointCheckpoint` (WETH9 on the side `initialize` names it) with the initialized model state and no tracked pair row | `Blanc.Composition.UniswapV2PairWeth9Joint.pair_weth9_create2_jointCheckpoint_side` (`Blanc/Composition/UniswapV2PairWeth9Deploy.lean:56`); for WETH9 as `token1` `Blanc.Composition.UniswapV2PairWeth9Joint.pair_weth9_create2_jointCheckpoint` (`Blanc/Composition/UniswapV2PairWeth9Deploy.lean:163`), as `token0` `Blanc.Composition.UniswapV2PairWeth9Joint.pair_weth9_create2_jointCheckpoint_zero` (`Blanc/Composition/UniswapV2PairWeth9Deploy.lean:223`) | deploy / INIT | CODE and ENV as `pair_create2_initialize_live`; INIT at the `initialize` world: the pair's code as the `CREATE2` step left it, WETH9's code, `FootInv K₀`, `SumNof`; ENV (trace-local): the new address's tracked WETH9 allowance rows are zero in the deployment's world (it has not acted as a WETH9 sender); the new address is neither WETH9, nor 0, nor the system address; WETH9 is no precompile under any covered fork. No hash premise | Both token orderings. The predicate is about the resulting state, not how it was produced. Not chained into a history; the factory issuing the `initialize` call is a premise, and the factory CODE premise of the rows above is separate |

**Closed instance**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| A computable checker decides `JointCheckpoint` from a finite description (WETH9's tracked rows, the pair's tracked rows and a base model state): both codes byte for byte, the pair's storage representation with a complete-support check, the token and lock fields, WETH9's footprint invariant, the world's ether sum over its actual accounts, the pair's WETH9 balance row against the reserve and its allowance rows, `pair ≠ WETH9`, `token0 ≠ token1`, the pair neither 0 nor the system address, and WETH9 no precompile of any covered fork; a second check decides that an address holds the factory runtime. Both are sound | `Blanc.Composition.UniswapV2PairWeth9Joint.checkJoint_sound` (`Blanc/Composition/UniswapV2PairWeth9CheckJoint.lean:51`) of `Blanc.Composition.UniswapV2PairWeth9Joint.checkJoint` (`Blanc/Composition/UniswapV2PairWeth9CheckJoint.lean:39`); `Blanc.Composition.UniswapV2PairWeth9Joint.checkFactory_sound` (`Blanc/Composition/UniswapV2PairWeth9CheckJoint.lean:83`) | Checker / soundness | none | Linear in the rows, the storage entries and the world's accounts; rows must be listed in ascending slot order (unsorted input is rejected) |
| The synthetic world `W0` satisfies `JointCheckpoint` with WETH9 as `token1`, and its pair's `factory` holds the factory runtime, both by running the checkers in the kernel | `Blanc.Composition.UniswapV2PairWeth9Instance.w0_jointCheckpoint` (`Blanc/Composition/UniswapV2PairWeth9W0.lean:98`) from `Blanc.Composition.UniswapV2PairWeth9Instance.w0_checkJoint` (`Blanc/Composition/UniswapV2PairWeth9W0.lean:94`); `Blanc.Composition.UniswapV2PairWeth9Instance.w0_factoryInstalled` (`Blanc/Composition/UniswapV2PairWeth9W0.lean:108`); the world `Blanc.Composition.UniswapV2PairWeth9Instance.W0` (`Blanc/Composition/UniswapV2PairWeth9W0.lean:83`) | Satisfiability / kernel evaluation | none | `W0` is synthetic: the system-contract fixture of Section 5.1's closed instance, WETH9's runtime at 0x3333…3333 with the pair's balance row (10^6, backed by WETH9's ether) and a zero pair allowance row, the Pair runtime with reserves 10^6 and 10^6 and supply 10^6 (1,000 locked at address 0, the rest held by the trader), `token0` the synthetic 299-byte Token20 runtime (Section 2), `token1` WETH9, the factory runtime at 0x4444…4444 with empty storage, and a funded code-free trader |
| For every world that is canonical (Jaune's `State.Canonical`: it stores no empty account and no zero storage word), whose total ether is representable (`SumNof`), and that agrees with `W0` on the ten accounts the block touches (`AgreesW0`): the configured BPO2 block with two signed type-2 transactions, `X.transfer(pair, 1000)` then `pair.swap(0, 996, trader, "")`, is a valid state transition from the checkpoint at that world, and on a configured history of it the trader's WETH9 balance word rises by 996 and the pair's falls by 996 (to 996 and 999,004); the pair's stored reserves equal its new `X` and WETH9 balances (1,001,000 and 999,004); the conclusion of `pair_weth9_joint` holds; and the conclusion of `pair_weth9_history_feeOff_product` holds with its antecedent discharged, share value rising strictly from `W0`'s pair state to the history's end at equal supply (`10^6·10^6 < 1,001,000·999,004`) | `Blanc.Composition.UniswapV2PairWeth9Capstone.uniswap_weth9_closed_agreeing` (`Blanc/Composition/UniswapV2PairWeth9CapstoneUniversal.lean:97`); the outcome `Blanc.Composition.UniswapV2PairWeth9Capstone.ClosedSwapOutcome` (`Blanc/Composition/UniswapV2PairWeth9CapstoneUniversal.lean:45`); the agreement `Blanc.Composition.UniswapV2PairWeth9Capstone.AgreesW0` (`Blanc/Composition/UniswapV2PairWeth9CapstoneWorld.lean:27`) | History and transaction / closed witness, universal over agreeing worlds | `State.Canonical`; ARITH `SumNof`; `AgreesW0` | Inside, every premise of the two headlines is discharged for this history: signature recovery of both transactions by kernel evaluation, the joint checkpoint transported from `W0`, the factory premises, and both HASH-T premises. Agreement with `W0` takes the place of a `JointCheckpoint` premise (Section 7 item 30) |
| The same at `W0` itself, with **no hypothesis** | `Blanc.Composition.UniswapV2PairWeth9Capstone.uniswap_weth9_closed_instance` (`Blanc/Composition/UniswapV2PairWeth9Capstone.lean:22`) | History and transaction / closed witness | none (closed) | `b = 996 > 0` and WETH9 leaves the pair, so the discharged WETH9 side is exercised; the swap is run at frame level inside the block (Section 7 item 29). Satisfiability in the model, not a statement about the chain |

**Statement controls**

| What it shows | Control | Altitude |
|---|---|---|
| The interface rejects a WETH9 model whose `transferFrom` skips the allowance check: that book violates `BookLaws` | `Blanc.Composition.Weth9Token.control_mutant_not_laws` (`Blanc/Composition/Weth9Token.lean:589`) on `Blanc.Composition.Weth9Token.mutantBook` (`Blanc/Composition/Weth9Token.lean:546`) | pure model, kernel evaluation |
| The no-allowance half of the joint relation is needed: on WETH9's ledger model, from a ledger in which address 1 holds one unit against a reserve of one and has granted nothing, a spender's `transferFrom` of that unit fails; after one `approve` by address 1, the same `transferFrom` succeeds and leaves its booked balance below the reserve | `Blanc.Composition.PairTokenJoint.control_pair_approve_breaks_joint` (`Blanc/Composition/PairTokenJointControl.lean:22`) | WETH9's pure ledger model; no pair model or bytecode is mutated |
| A world where the pair already holds a nonzero tracked WETH9 allowance row fails `JointCheckpoint`; the checker rejects `W0` with a stray nonzero pair slot and with a nonzero pair WETH9 allowance | `Blanc.Composition.UniswapV2PairWeth9Joint.JointCheckpoint.allowance_control` (`Blanc/Composition/UniswapV2PairWeth9Checkpoint.lean:49`); `Blanc.Composition.UniswapV2PairWeth9Instance.w0StrayPair_rejected` (`Blanc/Composition/UniswapV2PairWeth9W0.lean:118`), `Blanc.Composition.UniswapV2PairWeth9Instance.w0PairAllowance_rejected` (`Blanc/Composition/UniswapV2PairWeth9W0.lean:128`) | definitional; kernel evaluation of the checker |
| Each half of NoShrink is load-bearing: on states the production driver reaches, a `sync` whose token1 answer shrinks, and a `burn` whose token1 final answer falls below its initial answer minus the payout, each succeed with the token0 half holding and the token1 half failing, and the share-value inequality then fails (the token0 `sync` half is `noShrink_required` of Section 5.8) | `Blanc.Lift.UniswapV2Pair.ModelControlsSides.noShrinkSide_one_required` (`Blanc/Lift/UniswapV2Pair/ModelControlsSides.lean:22`), `Blanc.Lift.UniswapV2Pair.ModelControlsSides.burnNoShrinkSide_one_required` (`Blanc/Lift/UniswapV2Pair/ModelControlsSides.lean:50`) | typed model, kernel evaluation of the production driver |
| The pinned WETH9 records of the swap rows, the token1 `burn` row and the token1 `skim` row never constrain the free values: each pin reads only free values and earlier pins, so every choice of the free values extends to values meeting every pin | `Blanc.Composition.UniswapV2PairWeth9Joint.swapW0_pins_nonvacuous` (`Blanc/Composition/UniswapV2PairWeth9SwapLiveZero.lean:124`), `Blanc.Composition.UniswapV2PairWeth9Joint.swapW1_pins_nonvacuous` (`Blanc/Composition/UniswapV2PairWeth9SwapLive.lean:135`), `Blanc.Composition.UniswapV2PairWeth9Joint.burnEnvW1_pins_solvable` (`Blanc/Composition/UniswapV2PairWeth9BurnLiveOne.lean:479`), `Blanc.Composition.UniswapV2PairWeth9Joint.skimCalleeW1_pins_solvable` (`Blanc/Composition/UniswapV2PairWeth9SkimLiveOne.lean:262`) | definitional |

**Fork coverage.** The history rows assume or derive `CoveredFork`; the deployment
theorem quantifies over covered forks; the closed instance runs one BPO2 block.

**Non-claims.** The other token's behaviour (its half of NoShrink and its callee
records stay premises here; Section 5.10 discharges them for USDC, under its own
premises); that
mainnet's current state of any pair or of WETH9 satisfies `JointCheckpoint`; any pair
whose stored factory does not hold the factory runtime, or that reaches WETH9 through a
wrapper or router; the factory's `feeTo` answers; deployment of WETH9, deposits, the
pair's deployment, `initialize`, liquidity and the swap as **one** execution; historical
inclusion of either deployment; that any price, fee or LP outcome is fair or safe
(Section 7 items 20 and 27 to 34).

### 5.10 Uniswap V2 Pair × USDC × WETH9: three deployed runtimes in one history

Section 5.9 composes the Pair with WETH9 and keeps the other token's half as a named
premise. This section composes the Pair with **both** of its exhibit tokens over **one**
configured history, USDC as `token0` and WETH9 as `token1` (the exhibit pair's
assignment), and discharges both tokens' halves from deployed bytecode. USDC is three
certified runtimes (Section 2): the FiatTokenProxy, which forwards every non-admin call
by `DELEGATECALL` to the implementation its implementation slot names; the
FiatTokenV2_2 implementation, which runs over the proxy's storage; and the
SignatureChecker library the implementation reaches by `DELEGATECALL` for
authorizer-signed messages (`permit`, transferWithAuthorization,
receiveWithAuthorization, cancelAuthorization). The statements cover every pair
that runs the certified Pair runtime with USDC's proxy address as `token0` and WETH9 as
`token1`, whose stored factory holds the certified factory runtime, over any configured
history that starts from a world satisfying `JointCheckpoint2`, under one trace-local
premise on USDC's own messages, the governance premise `UsdcGovernance` (Section 7
item 35). The pair never signs a USDC entry: that is proved from the pair's code, not
assumed (`usdc_neverSigner_pair`; Section 7 item 36).

**The proxy and the `DELEGATECALL` lift**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| A certificate node claiming `CALL` where the code holds `DELEGATECALL` (`0xf4`) is rejected by the checker | `Blanc.Lift.checkNode_call_at_delegatecall` (`Blanc/Lift/DelegatecallControl.lean:16`) | Control / certificate | the byte at the node is `0xf4` | `DELEGATECALL` keeps the caller and the storage owner, so a certificate cannot pass it off as `CALL` |
| The proxy certificate with `CALL` claimed at the proxy's `DELEGATECALL` site (byte 1,680) fails `Cert.check` | `Blanc.Lift.Usdc.Proxy.proxy_cert_call_mutant_rejected` (`Blanc/Lift/Usdc/Proxy/Control.lean:24`) | Control / certificate | none | Kernel evaluation on the lifted proxy bytes |
| A frame running the proxy code from pc 0 whose caller is not the admin word: every external instruction it executes is `DELEGATECALL`; every child runs at the proxy with the implementation address `I` the slot names as code address, the frame's caller, value, calldata and static flag, and `I`'s code; on success the frame's output and world are a child's | `Blanc.Lift.Usdc.proxy_forwards` (`Blanc/Lift/Usdc/ProxyOk.lean:275`) | Frame / safety | CODE; covered fork; the implementation slot holds `I`; caller not the admin word; `I` carries no EIP-7702 designator and is no precompile; calldata below 2^256 bytes | `CALLDATASIZE` pushes the length modulo 2^256, hence the calldata bound |
| With the slot naming `J ≠ I`, no child runs with code address `I` | `Blanc.Lift.Usdc.proxy_forwards_control` (`Blanc/Lift/Usdc/ProxyForward.lean:126`) | Control / frame | as `proxy_forwards`, for `J` | The slot premise is load-bearing |
| A frame running the proxy code whose caller is the admin word: every external instruction is `CALL`, every child runs at the proxy with the proxy as caller, and a selector other than `upgradeTo`, `upgradeToAndCall` and `changeAdmin` spawns no child and leaves the proxy's storage unchanged | `Blanc.Lift.Usdc.proxy_admin_rule` (`Blanc/Lift/Usdc/ProxyForward.lean:227`) | Frame / safety | CODE; covered fork; caller is the admin word | The admin branch never reaches the implementation |
| The implementation's children are either library frames (at the same storage owner, with the frame's caller, value and static flag, running the library code) or frames whose caller is the storage owner, with value 0 | `Blanc.Lift.Usdc.impl_children` (`Blanc/Lift/Usdc/ImplSpawns.lean:52`) | Frame / safety | CODE; covered fork; the library code installed at its address | The second kind is rescueERC20's token call |
| The library's children are static, with the storage owner as caller, and a successful library frame leaves its storage owner's storage unchanged | `Blanc.Lift.Usdc.lib_children` (`Blanc/Lift/Usdc/LibSpawns.lean:30`) | Frame / safety | CODE; covered fork | The ERC-1271 isValidSignature call and the `ecrecover` call |

**USDC's model, its history and the signature laws**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| USDC's pure book (its ledger model read through the implementation's own decoder) satisfies the signature variant of the token laws, `BookLawsS`: as `BookLaws` (Section 5.9), except that a step may also lower a holder's balance, or raise its allowances, by a message the holder signed | `Blanc.Lift.Usdc.usdcBook_lawsS` (`Blanc/Lift/Usdc/Book.lean:140`), the book `Blanc.Lift.Usdc.usdcBookS` (`Blanc/Lift/Usdc/Book.lean:48`) | Model / safety | none | The signer is the third authorizer |
| Under `NeverSigner T S tr p` (no settled non-static entry of `T` along the history has `p` as signer), `BookLawsS` gives the holder-indexed laws the composition consumes, for `p` | `Blanc.Lift.Token.BookLawsS.holderLaws` (`Blanc/Lift/Token/Signed.lean:59`) | Model / bridge | `NeverSigner` | WETH9's laws are the unsigned case, `Blanc.Composition.Weth9Token.weth9Book_lawsS` (`Blanc/Composition/Weth9TokenSigned.lean:15`) |
| Under `UsdcHist` (USDC's three runtimes and its implementation slot installed at the checkpoint, the governance premise, the footprint invariant at the checkpoint, HASH-T over the keys the history touches), at every settled position not `UsdcShadowed` the book run over the earlier entry frames at the proxy is the footprint ledger at that frame's entry | `Blanc.Lift.Usdc.usdc_history_replayAt` (`Blanc/Lift/Usdc/HistoryReplay.lean:320`) | History / replay | `UsdcHist` | Positional replay |
| Under `UsdcHist`, the implementation slot and the admin word are unchanged at every settled frame's entry and at the end | `Blanc.Lift.Usdc.usdc_history_slots` (`Blanc/Lift/Usdc/HistorySlots.lean:168`) | History / safety | `UsdcHist` | This is what the governance premise buys |
| Under `UsdcHist`, at the history's end USDC's three runtimes and its implementation slot are installed, the footprint invariant holds over the history's key universe, and the admin word is unchanged | `Blanc.Lift.Usdc.usdc_history_end` (`Blanc/Lift/Usdc/HistoryEndFoot.lean:21`) | History / invariant | `UsdcHist` | The USDC analogue of WETH9's footprint standard |
| USDC at any proxy address is an instance of the writer-shadowed token core `CoreW`: its `Hist` is `UsdcHist`, its booked ledger is the footprint ledger over the history's key universe, its shadowed positions are `UsdcShadowed`, its answerable holders are the history's tracked balance rows | `Blanc.Composition.UsdcToken.usdcCore` (`Blanc/Composition/UsdcToken.lean:225`) | History / instance | `UsdcHist` | `CoreW` is `Core` with shadowed positions excluded |
| USDC discharges the self-caller facet: no foreign caller is forwarded into USDC's own entry | `Blanc.Composition.UsdcToken.usdcSelfCaller` (`Blanc/Composition/UsdcToken.lean:243`) | History / instance | as `usdcCore` | From the three spawn theorems above |
| USDC's book decodes `transfer` and `balanceOf` calldata as the ERC-20 ABI does | `Blanc.Composition.UsdcToken.usdcBook_erc20Abi` (`Blanc/Composition/UsdcToken.lean:268`) | Model / ABI | none | |
| USDC's budgeted transfer facet: at a world holding USDC's runtimes with the footprint core over `U`, a fresh entry frame at the proxy whose keys lie in `U`, whose caller is not the admin word and whose `transfer` meets USDC's state conditions, runs to success through the proxy and the implementation at an exact cost, given a gas budget that covers the proxy's 63/64 cut | `Blanc.Composition.UsdcToken.usdcTransferLive` (`Blanc/Composition/UsdcTokenLive.lean:159`) | Frame / instance | INIT footprint core; HASH-T frame keys in `U`; ENV gas and state conditions | From the proxy-to-implementation exact walk of `transfer` |

**The two-token joint invariant and share value**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| For any two writer-shadowed token cores with the ABI and self-caller facets and the holder laws for the pair: at every settled position not enclosed by a settled non-static pair frame and unshadowed in both cores the pair is unlocked with both joint relations; both hold at the end; and every outer pair step satisfies the whole of NoShrink, with no token antecedent | `Blanc.Composition.PairTwoToken.pair_two_token_joint` (`Blanc/Composition/PairTwoToken.lean:35`) | History / safety | Pair CODE and INIT; both cores' `Hist` and answerable rows; HASH-T over the pair's touched rows; ENV (trace-local): the factory never calls the pair, and neither token's code is an EIP-7702 designator or a precompile at the pair's steps | As `pair_token_joint`, for both sides at once |
| The same: fee on, every committed state change with positive incoming supply keeps `r0·r1·T'² ≤ r0'·r1'·(T + F)²`, with no antecedent; fee off, under the fee-off condition alone, `r0·r1·T'² ≤ r0'·r1'·T²` | `Blanc.Composition.PairTwoToken.pair_two_token_feeOn_product` (`Blanc/Composition/PairTwoTokenShareValue.lean:28`), `Blanc.Composition.PairTwoToken.pair_two_token_feeOff_product` (`Blanc/Composition/PairTwoTokenShareValue.lean:77`) | History / safety | as `pair_two_token_joint` | |
| Along a `UsdcHist` history, when the pair holds the certified Pair runtime at the checkpoint, differs from USDC's proxy and is no precompile of any covered fork, no settled non-static USDC entry frame has the pair as its signer (`NeverSigner`) | `Blanc.Composition.UsdcToken.usdc_neverSigner_pair` (`Blanc/Composition/UsdcNeverSigner.lean:19`) | History / safety | `UsdcHist`; CODE: the Pair runtime at the pair; the pair no precompile | The pair answers no ERC-1271 isValidSignature call, and the library rejects a signature for a signer with code; proved through a certified solc free-memory-pointer checker at USDC's two library call sites |
| `JointCheckpoint2`, the governance premise and HASH-T over USDC's touched keys give USDC's `Hist`, the pair's answerable row, the joint relation at the checkpoint and USDC's holder laws for the pair | `Blanc.Composition.UniswapV2PairUsdcWeth9.JointCheckpoint2.toUsdcCore` (`Blanc/Composition/UniswapV2PairUsdcWeth9Checkpoint.lean:63`) | History / bridge | `JointCheckpoint2`, `UsdcGovernance`, HASH-T | `NeverSigner` for the pair from `usdc_neverSigner_pair` and the checkpoint's pair-not-precompile field |
| **The joint invariant for the exhibit tokens**: from `JointCheckpoint2`, at every settled position not enclosed by a settled non-static pair frame and not `UsdcShadowed`, the pair is unlocked with USDC as `token0` and WETH9 as `token1`, `reserve0` is at most USDC's booked balance of the pair and `reserve1` at most WETH9's, and the pair has granted no booked allowance in either token; at the end `reserve0` is at most the balance bits of the pair's USDC balance word, `reserve1` at most its WETH9 balance word, and every tracked allowance row of the pair is zero in both tokens | `Blanc.Composition.UniswapV2PairUsdcWeth9.pair_usdc_weth9_joint` (`Blanc/Composition/UniswapV2PairUsdcWeth9Joint.lean:27`); the checkpoint `Blanc.Composition.UniswapV2PairUsdcWeth9.JointCheckpoint2` (`Blanc/Composition/UniswapV2PairUsdcWeth9Checkpoint.lean:33`) | History / safety | INIT `JointCheckpoint2`; HASH-T over the pair's, USDC's and WETH9's touched keys; ENV (trace-local): `UsdcGovernance`; CODE: the factory runtime at the model state's `factory`, not the system address | **No premise about either token's answers**; no never-signer premise |
| Share value, fee on, for the exhibit tokens: with **no antecedent**, every committed state change with positive incoming supply keeps `r0·r1·T'² ≤ r0'·r1'·(T + F)²` | `Blanc.Composition.UniswapV2PairUsdcWeth9.pair_usdc_weth9_history_feeOn_product` (`Blanc/Composition/UniswapV2PairUsdcWeth9ShareValue.lean:23`) | History / safety | as `pair_usdc_weth9_joint` | Both halves of NoShrink discharged |
| Share value, fee off: under the fee-off condition alone, `r0·r1·T'² ≤ r0'·r1'·T²` | `Blanc.Composition.UniswapV2PairUsdcWeth9.pair_usdc_weth9_history_feeOff_product` (`Blanc/Composition/UniswapV2PairUsdcWeth9ShareValue.lean:52`) | History / safety | as `pair_usdc_weth9_joint` | Only the factory's fee-off answer remains, as an antecedent |

**Both tokens' callee records discharged: liveness.** Each row restates the Section
5.8 row from the premises of `pair_usdc_weth9_joint`, for a fresh pair frame at the history's end, with
both tokens' callee records pinned to the legs their codes determine. Every row also
takes the frame's call depth (at least 2, for USDC's `DELEGATECALL`), that the pair is
not USDC's admin word, and the legs' 63/64 gas sentries (ENV).

| Section 5.8 row | Theorem | Level / kind | What remains beyond the common premises |
|---|---|---|---|
| `sync` | `Blanc.Composition.UniswapV2PairUsdcWeth9.pair_usdc_weth9_history_sync_live` (`Blanc/Composition/UniswapV2PairUsdcWeth9SyncLive.lean:25`) | History / live | ENV: the pair's residual sentry |
| `mint` | `Blanc.Composition.UniswapV2PairUsdcWeth9.pair_usdc_weth9_history_mint_live` (`Blanc/Composition/UniswapV2PairUsdcWeth9MintLive.lean:27`) | History / live | ENV: the factory's `feeTo` record and the pair's charges; HASH-T: the LP rows' freshness |
| `burn` | `Blanc.Composition.UniswapV2PairUsdcWeth9.pair_usdc_weth9_history_burn_live` (`Blanc/Composition/UniswapV2PairUsdcWeth9BurnLive.lean:44`) | History / live | Both tokens' initial queries, transfers and final queries discharged. ENV: the factory record, the pair's charges, USDC's state conditions for the payout (not paused, pair and recipient unflagged, the credit within the packed word, both parties nonzero); HASH-T: the LP rows' and the recipient's USDC balance row's freshness |
| `skim` | `Blanc.Composition.UniswapV2PairUsdcWeth9.pair_usdc_weth9_history_skim_live` (`Blanc/Composition/UniswapV2PairUsdcWeth9SkimLive.lean:42`) | History / live | Both queries and transfers discharged; no `FirstCallFresh`: USDC's `transfer` is proved to keep the pair's storage. ENV: the lock sentries, the frame non-static, USDC's state conditions; HASH-T: the recipient's USDC balance row |
| `swap` | `Blanc.Composition.UniswapV2PairUsdcWeth9.pair_usdc_weth9_history_swap_live` (`Blanc/Composition/UniswapV2PairUsdcWeth9SwapLive.lean:40`) | History / live | Both outputs allowed; both tokens' transfer and post-callback query records discharged, with no HASH-T over USDC's child. ENV: the callback, and when the callback runs, that it leaves USDC's implementation slot and does not make the pair USDC's admin; when USDC is paid out, USDC's state conditions and HASH-T for the recipient's USDC row |

**Deployment and the checkpoint checker**

| Claim | Theorem | Kind | Premises | Notes |
|---|---|---|---|---|
| For every covered fork: the Pair's `CREATE2` step runs and pushes the new address, and every `initialize` frame the creator sends to it naming USDC as `token0` and WETH9 as `token1`, at a world holding both tokens' checkpoint facts (codes, footprint invariants, storage agreeing with the deployment world's, the new address's balance rows tracked, USDC's unflagged, no tracked allowance row, neither token nor the new address a precompile), runs to success and leaves `JointCheckpoint2` | `Blanc.Composition.UniswapV2PairUsdcWeth9.pair_usdc_weth9_create2_jointCheckpoint2` (`Blanc/Composition/UniswapV2PairUsdcWeth9Deploy.lean:31`) | Deployment / INIT | ENV: the creator's frame conditions and gas | Not chained into a configured history; the factory issuing `initialize` is a premise |
| A computable checker decides `JointCheckpoint2` from finite row lists (USDC's, WETH9's and the pair's tracked rows, a base model state) and is sound | `Blanc.Composition.UniswapV2PairUsdcWeth9.checkJoint2_sound` (`Blanc/Composition/UniswapV2PairUsdcWeth9CheckJoint.lean:102`), the checker `Blanc.Composition.UniswapV2PairUsdcWeth9.checkJoint2` (`Blanc/Composition/UniswapV2PairUsdcWeth9CheckJoint.lean:92`); USDC's part `Blanc.Lift.Usdc.checkUsdc_sound` (`Blanc/Lift/Usdc/FiniteFootprint.lean:47`) | Decidable / sound | `checkJoint2 … = true` | |
| The synthetic world `U0` satisfies `JointCheckpoint2`, by running the checker in the kernel | `Blanc.Composition.UniswapV2PairUsdcWeth9.u0_jointCheckpoint2` (`Blanc/Composition/UniswapV2PairUsdcWeth9CheckJoint.lean:224`) | Closed witness | none | The checkpoint is satisfiable; `U0` is synthetic, not mainnet |

**Statement controls**

| What it shows | Control | Altitude |
|---|---|---|
| The laws reject USDC models that debit without authority: a mutant whose `transferFrom` skips the allowance, and an implementation whose `transfer` debits a third party | `Blanc.Lift.Usdc.control_usdc_mutant_not_lawsS` (`Blanc/Lift/Usdc/ModelControls.lean:175`), `Blanc.Lift.Usdc.control_usdc_thirdParty_not_lawsS` (`Blanc/Lift/Usdc/ModelControls.lean:194`) | definitional |
| `NeverSigner` is needed: a toy book satisfies `BookLawsS`, and when the holder may sign, any other caller's message lowers the holder's balance with no allowance | `Blanc.Lift.Token.control_signer_breaks_holder` (`Blanc/Lift/Token/SignedControl.lean:28`) | definitional |
| A tracked nonzero USDC allowance row of the pair, or a flagged pair balance word, fails `JointCheckpoint2` and the checker; the checker rejects `U0` with the pair's USDC allowance set to 7 and with its balance word flagged, and rejects USDC's synthetic storage with one stray word | `Blanc.Composition.UniswapV2PairUsdcWeth9.checkJoint2_allowance_control` (`Blanc/Composition/UniswapV2PairUsdcWeth9CheckJoint.lean:128`), `Blanc.Composition.UniswapV2PairUsdcWeth9.checkJoint2_frozen_control` (`Blanc/Composition/UniswapV2PairUsdcWeth9CheckJoint.lean:138`), `Blanc.Composition.UniswapV2PairUsdcWeth9.u0_allowance_rejected` (`Blanc/Composition/UniswapV2PairUsdcWeth9CheckJoint.lean:230`), `Blanc.Composition.UniswapV2PairUsdcWeth9.u0_frozen_rejected` (`Blanc/Composition/UniswapV2PairUsdcWeth9CheckJoint.lean:237`), `Blanc.Lift.Usdc.checkUsdc_rejects_stray` (`Blanc/Lift/Usdc/FiniteFootprint.lean:87`) | definitional (kernel evaluation for the concrete rejections) |

**The support-free checkpoint.** The same exhibit rows proved from `JointCheckpoint2F`:
`JointCheckpoint2` with the storage-wide support half of the footprint replaced by the
trace-local premise `PairUsdcAllowQuiet` (every touched Pair allowance row reads zero at
the checkpoint), taken only by the joint invariant, the share rows and the `swap` row.
The support-free checker decides `JointCheckpoint2F` from finite row lists and is sound;
its stray-slot control accepts the world the support-checking checker rejects.

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| The support-free checkpoint: the WETH9 joint, USDC installed, the support-free footprint, `token0`, the tracked balance row, unflagged, no tracked allowance, the reserve bound, apartness, neither USDC nor the pair a precompile | `Blanc.Composition.UniswapV2PairUsdcWeth9.JointCheckpoint2F` (`Blanc/Composition/UniswapV2PairUsdcWeth9CheckpointF.lean:32`) | History / INIT | as `JointCheckpoint2`, with `FootCoreL` for the footprint invariant | Eleven fields; every full checkpoint is one |
| The trace-local quiet premise | `Blanc.Composition.UniswapV2PairUsdcWeth9.PairUsdcAllowQuiet` (`Blanc/Composition/UniswapV2PairUsdcWeth9CheckpointF.lean:25`) | History / premise | the history's touched keys | Replaces support, taken only where the rows take it |
| The joint invariant for the exhibit tokens, support-free | `Blanc.Composition.UniswapV2PairUsdcWeth9.pair_usdc_weth9_joint_finite` (`Blanc/Composition/UniswapV2PairUsdcWeth9JointF.lean:47`) | History / safety | INIT `JointCheckpoint2F`; HASH-T; ENV: `UsdcGovernance`, `PairUsdcAllowQuiet`; CODE: as `pair_usdc_weth9_joint` | The original is its corollary |
| Share value, fee on and fee off, support-free | `Blanc.Composition.UniswapV2PairUsdcWeth9.pair_usdc_weth9_history_feeOn_product_finite` (`Blanc/Composition/UniswapV2PairUsdcWeth9ShareValueF.lean:20`), `Blanc.Composition.UniswapV2PairUsdcWeth9.pair_usdc_weth9_history_feeOff_product_finite` (`Blanc/Composition/UniswapV2PairUsdcWeth9ShareValueF.lean:58`) | History / safety | as the support-free joint invariant | The originals are their corollaries |
| `sync`, support-free | `Blanc.Composition.UniswapV2PairUsdcWeth9.pair_usdc_weth9_history_sync_live_finite` (`Blanc/Composition/UniswapV2PairUsdcWeth9SyncLiveF.lean:90`) | History / live | as the `sync` row, from `JointCheckpoint2F`, no quiet premise | The proof never uses the joint relation |
| `mint`, support-free | `Blanc.Composition.UniswapV2PairUsdcWeth9.pair_usdc_weth9_history_mint_live_finite` (`Blanc/Composition/UniswapV2PairUsdcWeth9MintLiveF.lean:30`) | History / live | as the `mint` row, from `JointCheckpoint2F`, no quiet premise | The proof never uses the joint relation |
| `burn`, support-free | `Blanc.Composition.UniswapV2PairUsdcWeth9.pair_usdc_weth9_history_burn_live_finite` (`Blanc/Composition/UniswapV2PairUsdcWeth9BurnLiveF.lean:26`) | History / live | as the `burn` row, from `JointCheckpoint2F`, no quiet premise | USDC's transfer is covered by its own queried balance |
| `skim`, support-free | `Blanc.Composition.UniswapV2PairUsdcWeth9.pair_usdc_weth9_history_skim_live_finite` (`Blanc/Composition/UniswapV2PairUsdcWeth9SkimLiveF.lean:25`) | History / live | as the `skim` row, from `JointCheckpoint2F`, no quiet premise | The proof never uses the joint relation |
| `swap`, support-free | `Blanc.Composition.UniswapV2PairUsdcWeth9.pair_usdc_weth9_history_swap_live_finite` (`Blanc/Composition/UniswapV2PairUsdcWeth9SwapLiveF.lean:26`) | History / live | as the `swap` row, from `JointCheckpoint2F` with the quiet premise | |
| A computable checker decides `JointCheckpoint2F` from finite row lists and is sound; with one nonzero word at the unlisted slot the support-free checker still accepts | `Blanc.Composition.UniswapV2PairUsdcWeth9.checkJoint2F_sound` (`Blanc/Composition/UniswapV2PairUsdcWeth9CheckJointF.lean:42`), the stray-slot control `Blanc.Composition.UniswapV2PairUsdcWeth9.u0F_stray_accepted` (`Blanc/Composition/UniswapV2PairUsdcWeth9CheckJointF.lean:74`) | Decidable / sound; control | `checkJoint2F … = true` | Support no longer needed |

**The live exhibit pair after an observed block**

These rows start from the actual deployments of WETH9 and of the USDC/WETH9 Pair and from the
observed mainnet block 26,213,219; each history premise is listed and assumed, not checked
against the chain.

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| After any configured mainnet history from the observed block, the reserves stored in the Pair's slot 8 are at most the Pair's USDC and WETH9 balance words | `Blanc.Composition.LiveUsdcWeth9B26213219.live_pair_reserves_backed` (`Blanc/Composition/LiveUsdcWeth9B26213219Headlines.lean:152`), with conclusion `Blanc.Composition.LiveUsdcWeth9B26213219.ReservesBacked` (`Blanc/Composition/LiveUsdcWeth9B26213219Headlines.lean:145`) | Deployment-rooted history / safety | OBSERVED `Blanc.Composition.LiveUsdcWeth9B26213219.ObservedCheckpoint` (`Blanc/Composition/LiveUsdcWeth9B26213219Anchor.lean:22`): the number, timestamp, hash and state root of the checkpoint's tip, chain id 1, and a finite set of storage reads at that state; DEPLOYMENT: the WETH9 and Pair deployment records of Sections 5.1 and 5.8 and `Blanc.Composition.LiveUsdcWeth9B26213219.DeploymentHistoryLink` (`Blanc/Composition/LiveUsdcWeth9B26213219AllowanceHistory.lean:51`), which places the Pair's block in WETH9's history; ENV: the Pair's WETH9 balance row fresh at WETH9's deployment, no checked sender of WETH9's history recovering to the Pair, no code-address-free frame targeting the Pair before its deployment, and no code at the Pair's address after WETH9's creation; HISTORY: the configured `HistFork` continuation from the observed block, USDC's original history over it (`Blanc.Composition.LiveUsdcWeth9B26213219.OriginalUsdcHistory` (`Blanc/Composition/LiveUsdcWeth9B26213219P1.lean:60`)) and the governance premise `UsdcGovernance`; **HASH-T** freshness of the Pair's, USDC's and WETH9's touched keys over the continuation | The same premises as the joint invariant from the original history |
| In such a history, at every outer call of the Pair (a settled non-static Pair frame that no earlier one encloses) entered with positive supply, the stored reserves and supply at its entry and at its committed exit keep `r0·r1·T'² ≤ r0'·r1'·(T + F)²`, where F is the fee that a `mint` or `burn` mints at the factory's actual `feeTo()` answer, read from the output of the call's own factory query, and zero for other calls | `Blanc.Composition.LiveUsdcWeth9B26213219.live_pair_share_value` (`Blanc/Composition/LiveUsdcWeth9B26213219CallShare.lean:116`), with conclusion `Blanc.Composition.LiveUsdcWeth9B26213219.LiveShareValue` (`Blanc/Composition/LiveUsdcWeth9B26213219CallShare.lean:95`) over `Blanc.Lift.UniswapV2Pair.OuterPairCall` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:120`), `Blanc.Lift.UniswapV2Pair.ShareValueKept` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:162`), `Blanc.Lift.UniswapV2Pair.callFeeWords` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:156`) and `Blanc.Lift.UniswapV2Pair.feeToAnswer` (`Blanc/Lift/UniswapV2Pair/PairOuterCalls.lean:143`) | Deployment-rooted history / safety | as above | Stated over stored words at each outer call, with no existential step; the factory's answer is the output of the actual child frame |
| Fee off: if the factory answered `feeTo() = 0` at every outer call, every outer call keeps `r0·r1·T'² ≤ r0'·r1'·T²` | `Blanc.Composition.LiveUsdcWeth9B26213219.live_pair_share_value_feeOff` (`Blanc/Composition/LiveUsdcWeth9B26213219CallShare.lean:147`), with premise `Blanc.Composition.LiveUsdcWeth9B26213219.FeeOffAlong` (`Blanc/Composition/LiveUsdcWeth9B26213219CallShare.lean:101`) | Deployment-rooted history / safety | as above, and the fee-off premise | |

**Fork coverage.** The history rows assume or derive `CoveredFork`; the deployment
theorem quantifies over covered forks.

**Non-claims.** Anything about live USDC or pool state other than the three rows on the live exhibit pair above, whose history premises are assumed; the closed single-block USDC
instance; other USDC versions than FiatTokenV2_2 at the stated implementation address;
positions inside `UsdcShadowed` (Section 7 items 35 to 40).

### 5.11 Curve 3pool StableSwap: frame, history, liveness, arithmetic, and composition with 3Crv

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
| A successful pc-0 run of the installed 3pool runtime, entered fresh (empty stack and memory) at a pool storage that is a `Checkpoint` of a model state `s`, is accepted by the model's `step` on its decoded call at some environment `e` it observed, with the frame's raw effect: the post storage is a `Checkpoint` of the model's output state; the logs are the entry logs, then the children's logs, then the model's events; the return data is the model's; for a non-static frame the frame's state-changing children are the model's calls encoded at the stored coin and token addresses (for every target that enters a code frame); the coins and token are unchanged. All 38 selectors | `Blanc.Lift.Curve3Pool.pool_frame_refines_env` (`Blanc/Lift/Curve3Pool/Safe.lean:43`); the form the history consumes `Blanc.Lift.Curve3Pool.pool_frame_refines` (`Blanc/Lift/Curve3Pool/Safe.lean:120`); the pure relation `Blanc.Lift.Curve3Pool.rawEffect_refines` (`Blanc/Lift/Curve3Pool/Refine.lean:239`) | Frame / safety | CODE (the frame's code is the certified runtime); covered fork; calldata length and gas below 2^256; the target account holds code; INIT `Checkpoint`; ENV `PoolFrameEnv`: every direct child keeps the pool's storage, every child that runs at a coin (and is not 3Crv) keeps 3Crv's storage, every child keeps the code at address 4, the identity precompile at 4 is warm, undelegated and enabled (`IdReady`), and no coin and not the token is a precompile | The coin and 3Crv answers enter through `e`; the walks of the individual selectors are not restated here |
| Calldata shorter than four bytes, or a selector among none of the 38, has **no** successful run. A successful, committing static frame writes no storage at any address and emits no logs | `Blanc.Lift.Curve3Pool.pool_other_fails` (`Blanc/Lift/Curve3Pool/Walk/Fallback.lean:130`); `Blanc.Lift.Curve3Pool.pool_static_noEffect` (`Blanc/Lift/Curve3Pool/Walk/Fallback.lean:145`) | Frame / safety | CODE; a fresh entry with calldata and gas below 2^256 (fallback); a covered fork, code at the target and `post.error = none` (static) | A static frame's return bytes are the model's by the row above |
| After any configured history from a checkpoint at which the pool holds the certified runtime and its storage is a `Checkpoint` of `s₀`: the runtime is still installed; the outermost settlement-committed non-static pool frames, in trace order, are authentic invocations (committed, non-static, pc 0, at the pool, each with the environment it observed) whose subtrees flatten exactly to the settlement-committed non-static pool frames of the trace; they replay through the model's `step` from `s₀`, each accepted with its raw effect, to a state of which the end pool storage is a `Checkpoint`, with coins and token unchanged | `Blanc.Lift.Curve3Pool.pool_history_committed_derived` (`Blanc/Lift/Curve3Pool/History.lean:130`) in its bundled form `Blanc.Lift.Curve3Pool.pool_history_committed_env` (`Blanc/Lift/Curve3Pool/History.lean:217`); the replay form over any entry condition `Blanc.Lift.Curve3Pool.pool_history_committed_with` (`Blanc/Lift/Curve3Pool/Ladder.lean:401`) | History / safety, exact extraction | CODE (installed at the checkpoint); INIT `Checkpoint`; `PoolTraceEnv`: per frame, every direct child of an admitted pool frame keeps the pool's storage and every coin child keeps 3Crv's storage (`callbacks`, an ENV premise); trace-local: the checkpoint's coins and token are not precompiles under any pool frame's rules, the identity precompile has no code at the checkpoint, no authorization of any transaction recovers to it, no CREATE frame targets it, and no system frame targets the pool. No hash premise | Rolled-back frames are not in the replay; static frames contribute nothing. The fresh-entry, calldata, gas and identity-readiness conditions of the frame row are derived from the trace, not assumed |
| The same from the deployment: the checkpoint's pool code is the runtime and its storage is exactly what the recorded deployment leaves (`deployedStor`), replayed from the constructor's model state | `Blanc.Lift.Curve3Pool.pool_history_initialized` (`Blanc/Lift/Curve3Pool/History.lean:162`) | History / safety | as above, with `PoolTraceEnv` at the constructor's coins and token | The deployment row below |

**Liveness, sufficient gas** (sufficient-gas bounds with a closed cost, not exact-gas equalities; the exact-gas forms are the next table; Section 7 item 48)

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| After any configured history, at a pool frame of the future state (fresh machine holding gas `G`, non-static, depth not 0, selector `exchange`): if the model accepts the call at the replayed state under the frame's balance readings and `G ≥ costExchange … + 4·U`, then the frame executes successfully, its raw effect is the model's `exchange` step at an environment whose credited pull equals the model's `pullIn` under the premised readings, the post pool storage is a `Checkpoint` of the model's output, and the post world is in the last invariant | `Blanc.Lift.Curve3Pool.pool_history_exchange_live` (`Blanc/Lift/Curve3Pool/HistoryLive.lean:71`) over the frame theorem `Blanc.Lift.Curve3Pool.exchange_live` (`Blanc/Lift/Curve3Pool/ExchangeLive.lean:79`) | History and frame / live | the history premises of the history row; no coin is a precompile; identity readiness; the per-execution keep premise; `CoinPullOkAt` for the input coin and `CoinPushOkAt` for the output coin over a chain `W → W' → W''` (a `WClosed` triple); for the **fee-on-transfer index 2 only**, two `CoinBalOkAt` readings `B1`, `B2` around the pull; the gas premise with the per-call allowance `U`; `gasMeasure < 2^256` | `exchange` calls no 3Crv function, so this pool-level row is also its composed statement. `costExchange` is a function of the model state and arguments, `0` where the model reverts. The index-2 path is not instantiated (Section 7 item 53) |
| The same for `add_liquidity`, `remove_liquidity`, `remove_liquidity_imbalance` and `remove_liquidity_one_coin`, with the 3Crv calls taken as premises. The conclusions: `remove_liquidity` and `remove_liquidity_imbalance` give the raw effect at the premised supply; `remove_liquidity_imbalance` and `remove_liquidity_one_coin` also put the post world in the last invariant; `remove_liquidity_one_coin` gives the raw effect at **some** supply reading `T'`, not pinned to the premised `T`; `add_liquidity` gives **some** environment `e` whose supply is the premised `T` and at which the model accepts the call, and the raw effect at `e` | `Blanc.Lift.Curve3Pool.pool_history_addLiquidity_live` (`Blanc/Lift/Curve3Pool/HistoryLive.lean:119`), `Blanc.Lift.Curve3Pool.pool_history_removeLiquidity_live` (`Blanc/Lift/Curve3Pool/HistoryLive.lean:170`), `Blanc.Lift.Curve3Pool.pool_history_removeLiquidityImbalance_live` (`Blanc/Lift/Curve3Pool/HistoryLive.lean:209`), `Blanc.Lift.Curve3Pool.pool_history_removeLiquidityOneCoin_live` (`Blanc/Lift/Curve3Pool/HistoryLive.lean:252`); frame forms `Blanc.Lift.Curve3Pool.addLiquidity_live` (`Blanc/Lift/Curve3Pool/AddLiquidityLive.lean:161`), `Blanc.Lift.Curve3Pool.removeLiquidity_live` (`Blanc/Lift/Curve3Pool/RemoveLiquidityLiveness.lean:124`), `Blanc.Lift.Curve3Pool.removeLiquidityImbalance_live` (`Blanc/Lift/Curve3Pool/RemoveImbalanceLive.lean:70`), `Blanc.Lift.Curve3Pool.removeLiquidityOneCoin_live` (`Blanc/Lift/Curve3Pool/OneCoinLive.lean:72`) | History and frame / live | as the row above (including the per-execution keep premise), plus the 3Crv call premises `SupplyOkAt` / `SupplyOk`, `MintOkAt`, `BurnOkAt` / `BurnOkTo` over the same kind of chain; a coin premise per coin call (`CoinPullOkAt` for `add_liquidity`, `CoinPushOkAt` for the withdrawals; `add_liquidity` and `remove_liquidity_imbalance` skip a coin whose amount is zero; `add_liquidity`'s fee coin also takes the two `CoinBalOkAt` readings); gas `costAddLiquidity … + 7·U`, `167000 + 5·U` (`remove_liquidity`), `costImbalance … + 5·U`, `costOneCoin … + 3·U` | The 3Crv premises are discharged in the composed row below. Section 7 item 54 on the existential conclusions |
| **Composed with 3Crv.** At a pool frame of the future state of a configured history from a joint checkpoint, `remove_liquidity`, `add_liquidity`, `remove_liquidity_imbalance` and `remove_liquidity_one_coin` execute under the same gas bounds and with the same conclusions, with every 3Crv call premise discharged by the deployed 3Crv: 3Crv's state is stated **once, at the frame's entry** | `Blanc.Composition.Curve3Pool3CrvHeadlines.pool_3crv_removeLiquidity_live_entry` (`Blanc/Composition/Curve3Pool3CrvHeadlines.lean:163`), `Blanc.Composition.Curve3Pool3CrvHeadlines.pool_3crv_addLiquidity_live_entry` (`Blanc/Composition/Curve3Pool3CrvHeadlines.lean:237`), `Blanc.Composition.Curve3Pool3CrvHeadlines.pool_3crv_removeLiquidityImbalance_live_entry` (`Blanc/Composition/Curve3Pool3CrvHeadlines.lean:332`), `Blanc.Composition.Curve3Pool3CrvHeadlines.pool_3crv_removeLiquidityOneCoin_live_entry` (`Blanc/Composition/Curve3Pool3CrvHeadlines.lean:411`) | History and frame / live | the history premises (`JointCheckpoint`, both runtimes installed, `FreshKeys` over 3Crv's touched keys, `PoolTraceEnv`, `pool ≠ systemAddress`); at the frame: `C3Ready` (derived from the history: 3Crv's code at the token, the pool is 3Crv's minter, the pool's token slot names it); the per-execution keep premise; 3Crv's supply word at entry is `T`; `BurnFits` (withdrawals) or `MintFits` (`add_liquidity`) at 3Crv's entry storage; a **coin world chain** `V 0 → V 1 → …` of `WClosed` invariants that do not read 3Crv's storage (`C3Blind`), with `CoinPushOkAt` or `CoinPullOkAt` per coin over worlds that pin 3Crv's storage (`C3With`); `U ≥ 70000` | Section 7 items 42, 43 and 50. 3Crv's costs enter through `Blanc.Composition.Curve3PoolCalleeLive.c3crv_supplyOkAt` (`Blanc/Composition/Curve3PoolCalleeLive.lean:618`) and its siblings for `mint` and `burnFrom`, built on 3Crv's cost bounds such as `Blanc.Lift.Curve3Crv.live_totalSupply_le` (`Blanc/Lift/Curve3Crv/CostBounds.lean:72`) |
| **The callee premises are satisfiable.** With `Token20` coins and the deployed 3Crv, world chains exist that satisfy every **callee** premise (coin, supply, mint and burn calls) of the four frame theorems at `U = 80000` | `Blanc.Composition.Curve3Pool3CrvInstance.removeLiquidity_premises_satisfiable` (`Blanc/Composition/Curve3Pool3CrvLiveWitness.lean:126`), `Blanc.Composition.Curve3Pool3CrvInstance.addLiquidity_premises_satisfiable` (`Blanc/Composition/Curve3Pool3CrvLiveWitness.lean:196`), `Blanc.Composition.Curve3Pool3CrvInstance.removeLiquidityImbalance_premises_satisfiable` (`Blanc/Composition/Curve3Pool3CrvLiveWitness.lean:301`), `Blanc.Composition.Curve3Pool3CrvInstance.removeLiquidityOneCoin_premises_satisfiable` (`Blanc/Composition/Curve3Pool3CrvLiveWitness.lean:369`) | Witness / conditional | the coins hold `Token20`'s code and their ledgers cover the moves (`T20MoveFits`, `T20PullFits`), 3Crv holds its code with supply `T` and accepts the burn or mint, the accounts involved are distinct, not precompiles and not the pool | These witnesses discharge the callee premises only: not the per-execution keep premise, not the model step, and not agreement of the amounts with the model's outputs. The end-to-end instances below discharge all of them at one concrete entry each. None of the four `_live_entry` theorems is itself instantiated |

**Liveness, exact gas** (the sufficient-gas rows above remain, unchanged; Section 7 items 48 and 53)

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| At a pool frame whose storage is a `Checkpoint` of `s`, for each of the five entries: if the model accepts the call and every call of the frame is an exact call profile with the call data `P`, then a closed cost `c` is fixed before any residual gas, and for every residual `R` above the entry's headroom the frame entered with `R + c` has an actual successful execution with `post.gasLeft = R` exactly and the conclusion of the entry's sufficient-gas frame theorem (the same raw effect and `Checkpoint`, and where that theorem has them the post invariant and the existential environment). For `exchange`, `add_liquidity`, `remove_liquidity_imbalance` and `remove_liquidity_one_coin`, `c` also reads model words (`_A()`, the scaled balances, the checked `get_D`, `get_y` and `get_y_D` results, the fee-loop words), which the statement fixes, before `R`, by the model's own checks (`aChk`, `xpChk`, `getDChk`, `getYChk`, `getYDChk`, `RliFeeIter`, `CwStep`) | `Blanc.Lift.Curve3Pool.removeLiquidity_live_exact` (`Blanc/Lift/Curve3Pool/RemoveLiquidityExactFrame.lean:81`), `Blanc.Lift.Curve3Pool.exchange_live_exact` (`Blanc/Lift/Curve3Pool/ExchangeExactLive.lean:31`), `Blanc.Lift.Curve3Pool.addLiquidity_live_exact` (`Blanc/Lift/Curve3Pool/AddLiquidityExactFrame.lean:40`), `Blanc.Lift.Curve3Pool.removeLiquidityImbalance_live_exact` (`Blanc/Lift/Curve3Pool/RemoveLiquidityImbalanceExactFrame.lean:78`), `Blanc.Lift.Curve3Pool.removeLiquidityOneCoin_live_exact` (`Blanc/Lift/Curve3Pool/OneCoinExactFrame.lean:42`) | Frame / live, exact gas | the sufficient-gas frame row's premises, with each call premise replaced by its exact profile (`RLExactPremises`, `ALExactPremises`, `RLIExactPremises`, `OCExactPremises`; for `exchange` the input coin's `transferFrom`, the output coin's `transfer` and, at the fee-on-transfer index 2, the two `balanceOf(self)` profiles); the per-execution keep premise at the entry gas `R + c`; headroom `167000 + 5·U ≤ R` (`remove_liquidity`), `60000 + U ≤ R` (`exchange`), `100000 + 5·U ≤ R` (`add_liquidity`), `66000 + 3·U ≤ R` (`remove_liquidity_imbalance`), `131000 + 3·U ≤ R` (`remove_liquidity_one_coin`), and for `exchange`, `add_liquidity` and `remove_liquidity_imbalance` also the sufficient-gas row's bound at the entry gas (`costExchange … + 4·U ≤ R + c` and its siblings); the entry's gas measure below 2^256 (with 6000, 3000 and 2000 to spare for `add_liquidity`, `remove_liquidity_imbalance` and `remove_liquidity_one_coin`) | The closed costs are `Blanc.Lift.Curve3Pool.rlExactCost` (`Blanc/Lift/Curve3Pool/Walk/RemoveLiquidityExactSchedule.lean:235`), `Blanc.Lift.Curve3Pool.exExactCost` (`Blanc/Lift/Curve3Pool/Walk/ExchangeExactWalk.lean:735`), `Blanc.Lift.Curve3Pool.alExactCost` (`Blanc/Lift/Curve3Pool/AddLiquidityExactFrame.lean:34`), `Blanc.Lift.Curve3Pool.rliExactCost` (`Blanc/Lift/Curve3Pool/Walk/RliExactSchedule.lean:271`) and `Blanc.Lift.Curve3Pool.ocExactCost` (`Blanc/Lift/Curve3Pool/Walk/OneCoinExactSchedule.lean:198`): finite sums of stage charges at canonical intermediate states, functions of the entry, of `P` (the profiles' debit and successor functions) and of the pinned words. None reads the residual gas, and none is existential. Headroom and the no-wrap bound are separate premises, not part of `c`. The effect is the sufficient-gas theorem's at the same entry gas: an entry has one execution result |
| The same at a message `msg` to the pool: the premises, the model words and `c` are fixed at the base message's initial frame `(initSevm msg, initDevm msg)`; then for every `R` with the same headroom, the message with its gas grant replaced by `R + c`, `msg.withGas (R + c)`, executes (`exec (initEvm (msg.withGas (R + c))) = .ok post`) with `post.gasLeft = R` and the frame theorem's conclusion | `Blanc.Lift.Curve3Pool.removeLiquidity_msg_exact` (`Blanc/Lift/Curve3Pool/ExactMessage.lean:30`), `Blanc.Lift.Curve3Pool.exchange_msg_exact` (`Blanc/Lift/Curve3Pool/ExactMessage.lean:73`), `Blanc.Lift.Curve3Pool.addLiquidity_msg_exact` (`Blanc/Lift/Curve3Pool/ExactMessage.lean:164`), `Blanc.Lift.Curve3Pool.removeLiquidityImbalance_msg_exact` (`Blanc/Lift/Curve3Pool/ExactMessage.lean:259`), `Blanc.Lift.Curve3Pool.removeLiquidityOneCoin_msg_exact` (`Blanc/Lift/Curve3Pool/ExactMessage.lean:315`) | Message / live, exact gas | the frame row's premises at the base message's initial frame; the per-execution keep premise at the grant `R + c`; the same headroom; `R + c`, with the frame's margin, below 2^256 | `msg.withGas` replaces only the message's `gas` field. It is declared in Blanc, not by Jaune (`Blanc/Lift/StaticGasMessage.lean`). The premises and `c` are carried across the grant, so `c` is the same at every grant; no execution is carried across gas |
| After any configured history, for a message to the pool whose state is the future state: the replayed state `s` is chosen, separately in each theorem, before that entry's premises, and each entry's message-level exact form holds at `s` | `Blanc.Lift.Curve3Pool.pool_history_removeLiquidity_live_exact` (`Blanc/Lift/Curve3Pool/HistoryLiveExact.lean:32`), `Blanc.Lift.Curve3Pool.pool_history_exchange_live_exact` (`Blanc/Lift/Curve3Pool/HistoryLiveExact.lean:77`), `Blanc.Lift.Curve3Pool.pool_history_addLiquidity_live_exact` (`Blanc/Lift/Curve3Pool/HistoryLiveExact.lean:161`), `Blanc.Lift.Curve3Pool.pool_history_removeLiquidityImbalance_live_exact` (`Blanc/Lift/Curve3Pool/HistoryLiveExact.lean:248`), `Blanc.Lift.Curve3Pool.pool_history_removeLiquidityOneCoin_live_exact` (`Blanc/Lift/Curve3Pool/HistoryLiveExact.lean:302`) | History and message / live, exact gas | the history premises of the history row, then the message row's | `exchange` calls no 3Crv function, so `pool_history_exchange_live_exact` is also its composed statement. In the other four, 3Crv's calls are exact profiles taken as premises; the composed row below discharges them |
| **Composed with 3Crv.** At a message to the pool at the future state of a configured history from a joint checkpoint, `remove_liquidity`, `add_liquidity`, `remove_liquidity_imbalance` and `remove_liquidity_one_coin` execute with exact gas as in the history row, with 3Crv's `totalSupply()`, `mint` and `burnFrom` calls answered by the deployed 3Crv's own exact profiles, so no 3Crv call-profile premise remains (3Crv's supply word and `BurnFits`/`MintFits` are stated once, at the entry) | `Blanc.Composition.Curve3Pool3CrvHeadlinesExact.pool_3crv_removeLiquidity_live_exact` (`Blanc/Composition/Curve3Pool3CrvHeadlinesExact.lean:40`), `Blanc.Composition.Curve3Pool3CrvHeadlinesExact.pool_3crv_addLiquidity_live_exact` (`Blanc/Composition/Curve3Pool3CrvHeadlinesExact.lean:112`), `Blanc.Composition.Curve3Pool3CrvHeadlinesExact.pool_3crv_removeLiquidityImbalance_live_exact` (`Blanc/Composition/Curve3Pool3CrvHeadlinesExact.lean:239`), `Blanc.Composition.Curve3Pool3CrvHeadlinesExact.pool_3crv_removeLiquidityOneCoin_live_exact` (`Blanc/Composition/Curve3Pool3CrvHeadlinesExact.lean:323`) | History and message / live, exact gas | the sufficient-gas composed row's premises (the joint history premises; `C3Ready`, derived; 3Crv's supply word `T` and `BurnFits` or `MintFits` at the entry; the coin world chain `V` with `C3Blind` and `C3With`; `U ≥ 70000`), with each coin call an exact profile whose debit and successor functions are parameters; the per-execution keep premise at the grant; the message row's headroom and no-wrap bound | `c` is the entry's closed cost at 3Crv's named call data (`Blanc.Composition.Curve3Pool3CrvExactAssembly.rlC3Calls` (`Blanc/Composition/Curve3Pool3CrvExactAssembly.lean:38`) and its siblings), built from `Blanc.Composition.Curve3PoolCalleeExactProfiles.c3crv_supplyProfile` (`Blanc/Composition/Curve3PoolCalleeExactProfiles.lean:126`), `Blanc.Composition.Curve3PoolCalleeExactProfiles.c3crv_mintProfile` (`Blanc/Composition/Curve3PoolCalleeExactProfiles.lean:431`) and `Blanc.Composition.Curve3PoolCalleeExactProfiles.c3crv_burnProfile` (`Blanc/Composition/Curve3PoolCalleeExactProfiles.lean:488`). The coin profiles stay environment premises. None of the four is instantiated end to end |
| **The exact premise bundles are satisfiable.** With `Token20` coins and the deployed 3Crv's own exact profiles, each frame theorem's exact premise bundle (for `exchange`, its three profiles) holds at `U = 80000` for some call data `P`, for the four 3Crv-calling entries along the world chains of the sufficient-gas witnesses and for `exchange`, which has no sufficient-gas callee witness, along its own two coin worlds | `Blanc.Composition.Curve3Pool3CrvInstance.removeLiquidity_exactPremises_satisfiable` (`Blanc/Composition/Curve3Pool3CrvExactWitness.lean:30`), `Blanc.Composition.Curve3Pool3CrvInstance.addLiquidity_exactPremises_satisfiable` (`Blanc/Composition/Curve3Pool3CrvExactWitness.lean:89`), `Blanc.Composition.Curve3Pool3CrvInstance.removeLiquidityImbalance_exactPremises_satisfiable` (`Blanc/Composition/Curve3Pool3CrvExactWitness.lean:220`), `Blanc.Composition.Curve3Pool3CrvInstance.removeLiquidityOneCoin_exactPremises_satisfiable` (`Blanc/Composition/Curve3Pool3CrvExactWitness.lean:294`), `Blanc.Composition.Curve3Pool3CrvInstance.exchange_exactPremises_satisfiable` (`Blanc/Composition/Curve3Pool3CrvExactWitness.lean:361`) | Witness / conditional | as the sufficient-gas witnesses: the coins hold `Token20`'s code and their ledgers cover the moves, 3Crv holds its code with supply `T` and accepts the burn or mint, the accounts involved are distinct, not precompiles and not the pool; for `exchange`, coins `i ≠ j` | They witness the premise bundles of the frame theorems at the sufficient-gas witnesses' worlds (for `exchange`, at the exact witness's own worlds); the composed headlines' coin-chain hypotheses as stated are witnessed in the next row, their 3Crv and coin-ledger facts taken as world conditions. They do not discharge the per-execution keep premise or the model step, and the amounts are not tied to the model's outputs. No exact-gas theorem is instantiated end to end |
| **The composed headlines' coin-chain hypotheses hold as stated.** Over the composed headline's own history, a coin chain `V` that never reads 3Crv's storage (coins not yet called as at the entry; for `add_liquidity` also the fee coin's pulled ledger, so the world after the mint carries it), `U = 80000` and `Token20`'s own coin debit and successor functions meet, jointly and in the headline's text, each of the four composed exact headlines' coin-chain hypotheses `_hU`, `_hVc`, `_hVb`, `_hVs`, `_hskip` where present (`add_liquidity`, `remove_liquidity_imbalance`) and coin profiles (the 3Crv profiles are then 3Crv's own, through `*ExactPremises_c3crv`), and `_hpc` follows from the history; `_htok`, `_hcoin`, `_hT` and `_hburn`/`_hmint` are restated from the world conditions. Applied to the headline itself, its conclusion holds under its remaining hypotheses. The same holds for the four sufficient-gas composed rows | `Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_removeLiquidity_live_exact_literal` (`Blanc/Composition/Curve3Pool3CrvExactLiteralHeadlines.lean:66`), `Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_addLiquidity_live_exact_literal` (`Blanc/Composition/Curve3Pool3CrvExactLiteralHeadlines.lean:138`), `Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_removeLiquidityImbalance_live_exact_literal` (`Blanc/Composition/Curve3Pool3CrvExactLiteralHeadlines.lean:262`), `Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_removeLiquidityOneCoin_live_exact_literal` (`Blanc/Composition/Curve3Pool3CrvExactLiteralHeadlines.lean:345`), `Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_removeLiquidity_live_entry_literal` (`Blanc/Composition/Curve3Pool3CrvExactLiteralHeadlines.lean:454`), `Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_addLiquidity_live_entry_literal` (`Blanc/Composition/Curve3Pool3CrvExactLiteralHeadlines.lean:512`), `Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_removeLiquidityImbalance_live_entry_literal` (`Blanc/Composition/Curve3Pool3CrvExactLiteralHeadlines.lean:584`), `Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_removeLiquidityOneCoin_live_entry_literal` (`Blanc/Composition/Curve3Pool3CrvExactLiteralHeadlines.lean:652`) | Witness / conditional | the composed headline's history premises; taken as world conditions, not discharged: the frame is not static, not at depth `0`, at a covered fork; 3Crv holds its code with supply `T`, is not the pool and not a precompile (`C3Entry`); the coins hold `Token20`'s code, are distinct, not the pool, not 3Crv and not precompiles (`T20Coins`; for `remove_liquidity_one_coin`, coin `i` only, with `_hcoin` a hypothesis for all three coin words); their ledgers cover the calls (`T20MoveFits`, `T20PullFits`); 3Crv accepts the burn or mint (`_hburn`/`_hmint` as `BurnFits`, `MintFits`) | The call code and call data (`_hcode`, `_hlen`, `_hcd`, `_hsel`, and `_hi` for `remove_liquidity_one_coin`), the model step, `IdReady`, the per-execution keep premise, the headroom and the no-wrap bound stay hypotheses; no composed headline is instantiated end to end. The witnesses are `Blanc.Composition.Curve3Pool3CrvLiteralWitness.removeLiquidity_exact_literal_witness` (`Blanc/Composition/Curve3Pool3CrvExactLiteralWitness.lean:176`) and its siblings |

**End-to-end instances** (of the sufficient-gas frame theorems; no hypotheses; Section 7 item 53)

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| `remove_liquidity(600, [0, 0, 0])` runs: an actual successful execution of the pool's runtime from a concrete entry at gas 878,400 whose raw effect is the model's output (pushes 100, 200 and 300, burn 600) at supply 6,000, with the pool's checkpoint at the post | `Blanc.Composition.Curve3Pool3CrvInstance.rl_frame_live` (`Blanc/Composition/Curve3Pool3CrvLiveEndKeep.lean:121`) | Frame / live, instantiated | none | `removeLiquidity_live` with every premise discharged, the per-execution keep premise included. The entry is a frame at remaining call depth 1 (nested 1,023 calls deep) on a synthetic world |
| `remove_liquidity_one_coin(600, 1, 0)` runs at gas 878,400: burn 600, push 531 of coin 1, with the pool's checkpoint at the post | `Blanc.Composition.Curve3Pool3CrvInstance.oc_frame_live` (`Blanc/Composition/Curve3Pool3CrvLiveEndKeep.lean:132`) | Frame / live, instantiated | none | The raw effect is at **some** supply reading `T'`, as in the frame theorem |
| `remove_liquidity_imbalance([90, 180, 270], 600)` runs at gas 878,400: burn 541, pushes 90, 180 and 270, with the pool's checkpoint at the post and the post world in the theorem's last invariant | `Blanc.Composition.Curve3Pool3CrvInstance.rli_frame_live` (`Blanc/Composition/Curve3Pool3CrvLiveEndKeepRLI.lean:69`) | Frame / live, instantiated | none | The last conjunct is the world-chain invariant of the instance (3Crv at its burned storage, the coins as the pushes leave them) |
| `add_liquidity([100, 200, 300], 599)` runs at gas **1,110,000**: mint 599, with the pool's checkpoint at the post | `Blanc.Composition.Curve3Pool3CrvInstance.al_frame_live` (`Blanc/Composition/Curve3Pool3CrvLiveEndKeepAL.lean:76`) | Frame / live, instantiated | none | At **some** environment `e` whose supply is 6,000 and at which the model accepts the call. The frame's gas differs from the 878,400 of the concrete entry message |
| `exchange(0, 1, 100, 0)` runs from the transaction's entry frame: at any machine satisfying `ExFrame` (the closed instance's pool frame: remaining call depth 1,024, the transaction's entry frame, gas 878,400), an actual successful execution whose raw effect is the model's output (pull 100 of coin 0, push 132 of coin 1) | `Blanc.Composition.Curve3Pool3CrvInstance.ex_frame_live` (`Blanc/Composition/Curve3Pool3CrvCapstoneFrame.lean:107`) | Frame / live, instantiated | `ExFrame`, which the transaction's prepared message meets (`ex_prepared_frame`) | The coins' answers come from `Token20`'s code (`Blanc.Composition.Curve3Pool3CrvInstance.token20_coinPullOkAt` (`Blanc/Composition/Curve3Pool3CrvCoinAnswers.lean:16`), `Blanc.Composition.Curve3Pool3CrvInstance.token20_coinPushOkAt` (`Blanc/Composition/Curve3Pool3CrvCoinAnswers.lean:34`)), not from premises. The environment's balance readings are existential, with the credited pull equal to the model's |

**Closed instance**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| A finite synthetic world satisfies the joint pool-and-3Crv checkpoint, decided by a computable checker whose soundness is a theorem: the pool's storage is a `Checkpoint` of the model state, 3Crv's storage satisfies `VyInv` over the listed rows (conservation included), the pool's token is 3Crv and 3Crv's minter is the pool | `Blanc.Composition.Curve3Pool3CrvJoint.checkJoint_sound` (`Blanc/Composition/Curve3Pool3CrvCheckpoint.lean:345`); the first fixture `Blanc.Composition.Curve3Pool3CrvJoint.world_joint` (`Blanc/Composition/Curve3Pool3CrvCheckpoint.lean:459`); the closed-instance world `Blanc.Composition.Curve3Pool3CrvInstance.p0_joint` (`Blanc/Composition/Curve3Pool3CrvWorld.lean:81`) | Witness / closed | none for the fixtures (kernel evaluation of the checker) | The checkpoint predicate carries storage, minter and address facts, not installed code. The synthetic pool is at address `0x1000` (not a precompile under any covered fork) |
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
| **Composed bound at 3Crv's ledger supply.** The same bounds over one configured history of the pool and 3Crv together, with `T` 3Crv's supply word at the frame's entry and `T'` at its post, no supply premise, and `supplyAfter T (model calls) = T'` | `Blanc.Composition.Curve3PoolSupply.pool_3crv_u3` (`Blanc/Composition/Curve3Pool3CrvU3.lean:84`); from the recorded deployment `Blanc.Composition.Curve3Pool3CrvHeadlines.pool_3crv_u3_deployed` (`Blanc/Composition/Curve3Pool3CrvHeadlines.lean:480`) | History / safety | the joint-history premises of the composition row below; the deployed form takes the joint checkpoint with the pool's state `Creation.poolInitState t₀` | In `pool_3crv_u3` the admin-fee side condition is kept by every replayed step if it holds at the checkpoint (`FeeBounded ps₀ → FeeBounded sᵢ`); `pool_3crv_u3_deployed` states `adminFee ≤ 10^10` outright (`Blanc.Lift.Curve3Pool.feeBounded_of_poolRun_init` (`Blanc/Lift/Curve3Pool/U3Ledger.lean:164`)). No joint checkpoint at `poolInitState` is instantiated (Section 7 item 49). Section 7 item 44 |

**Amplification**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| In the committed replay, every invocation ran at its block's **header** timestamp, which is its recorded time. At that time the model's `_A()` is the stored linear interpolation between `initial_A` and `future_A` (truncating, separately for a rising and a falling ramp) from the ramp start on, and is the constant `future_A` once the ramp has ended (so outside a ramp, and where `future_A_time = 0`); an accepted `ramp_A` meets the source's guards (duration at least `MIN_RAMP_TIME`, `0 < A < MAX_A`, factor at most `MAX_A_CHANGE` either way). After `stop_ramp_A`, `A` is constant at its value then | `Blanc.Lift.Curve3Pool.pool_history_amp` (`Blanc/Lift/Curve3Pool/AmpHistory.lean:81`); `Blanc.Lift.Curve3Pool.aChk_eq_aInterp` (`Blanc/Lift/Curve3Pool/U5.lean:60`), `Blanc.Lift.Curve3Pool.aChk_of_le` (`Blanc/Lift/Curve3Pool/U5.lean:51`), `Blanc.Lift.Curve3Pool.rampA_guards` (`Blanc/Lift/Curve3Pool/U5.lean:147`), `Blanc.Lift.Curve3Pool.stopRampA_const` (`Blanc/Lift/Curve3Pool/U5.lean:160`) | Model and history / safety | the history premises; for the interpolation: `future_A` below 2^256 and the source's one product `|future_A − initial_A|·(t − initial_A_time)` below 2^256 | The guards are read off an accepted ramp in one direction. Control: the recorded time is never the parent block's timestamp, `Blanc.Lift.Curve3Pool.pool_invocation_time_ne_parent` (`Blanc/Lift/Curve3Pool/AmpHistory.lean:123`), for a settled frame of one configured block whose timestamp is a word; and an explicit accepted ramp state at which the header time gives `A = 550` and the parent's timestamp gives `549`, `Blanc.Lift.Curve3Pool.u5_parent_time_control` (`Blanc/Lift/Curve3Pool/U5.lean:233`) |
| The exact root `⌊D*⌋` is non-decreasing in `A` at fixed positive balances, and `get_D` follows it only up to its loop error: `get_D(A) ≤ get_D(A') + (get_D(A) − ⌊D*⌋(A))` for `A ≤ A'`. A ramp alone can lower `D/T`: with one deposit and then a ramp from `A = 2000` to `A = 200`, and no operation after it, `get_D` falls from 200044801219456106169 to 192793226260180884069 at an unchanged supply | `Blanc.Lift.Curve3Pool.dMonoInA` (`Blanc/Lift/Curve3Pool/U5.lean:213`); `Blanc.Lift.Curve3Pool.u5_ramp_control` (`Blanc/Lift/Curve3Pool/U5.lean:189`) | Model / safety and control | positive balances, `1 ≤ A ≤ A'` (`dMonoInA`); the explicit honest-world history (control) | `dMonoInA` is **not** a monotonicity of `get_D` in `A`: its statement carries the error term. The ramp control is the negative control for the fixed-amplification statements; the bare inequality is `Blanc.Lift.Curve3Pool.u5_ramp_control_falls` (`Blanc/Lift/Curve3Pool/U5.lean:196`) |

**Composition with 3Crv**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| Over one configured history from a joint checkpoint in which 3Crv's `minter` is the pool: the pool history of the history row; 3Crv's model replays exactly its committed invocations to a state its future storage abstracts; the minter is still the pool (**persistence**); 3Crv's final supply plus the pool's committed burns equals the checkpoint supply plus the pool's committed mints (amounts read off the replayed steps' model calls, as words); per invocation, 3Crv's supply word at the frame's post plus the step's burned amounts equals its supply word at entry plus its minted amounts; and the supply the frame observed is 3Crv's supply word at the entry of its `totalSupply()` child | `Blanc.Composition.Curve3PoolSupply.pool_3crv_history` (`Blanc/Composition/Curve3PoolSupply.lean:565`) | History / safety, exact extraction | `JointCheckpoint`; both runtimes installed at the checkpoint; `FreshKeys` over 3Crv's touched keys (3Crv's HASH-T, inherited); `PoolTraceEnv`; `pool ≠ systemAddress` | The pool side takes no hash premise. Section 7 items 43 and 49 |
| 3Crv's own history statements used above | `Blanc.Lift.Curve3Crv.c3crv_history_committed_derived` (`Blanc/Lift/Curve3Crv/CommittedHistory.lean:230`); `Blanc.Composition.Curve3CrvToken.c3crv_history_supply` (`Blanc/Composition/Curve3CrvTokenCore.lean:247`); `Blanc.Composition.Curve3CrvToken.c3crv_history_at` (`Blanc/Composition/Curve3CrvPositional.lean:219`) | History / safety | the 3Crv premises of Section 5.3 | `c3crv_history_supply` additionally takes that every committed writer invocation the initial minter sends keeps the minter |
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
| Curve | ✓ | ✓ | ✓ | ✓ HASH-T | ✓ [b] [ak] | ~ [g] | ✗ | ✓ |
| Lido | ✓ | ✓ (L1/L3) | ~ [h] | ~ [h] | ~ [i] | ✗ | ✗ | ✓ |
| V+ | ✓ | ~ [j] | ~ [j] | ✓ HASH-T (per execution) | ✓ [q] (message level; the exclusion itself takes no INIT premise) | ✓ nonvacuity (witnesses), and a reachable witness [q] | ~ [k] | ✓ |
| V− | ✓ | — | — | — | ✓ [q] (message level) | ✓ [q] violation at a reachable state | ✓ [l] | ✓ |
| EIP-7002 | ✓ | ✓ [m] | ✓ | ✓ none | ✓ [b] | ✓ | ✗ | ✓ |
| Uniswap V2 Pair | ✓ | ✓ | ✓ [n] | ✓ HASH-T | ✓ [b] [o] | ✓ [p] | ✗ | ✓ |
| Uniswap V2 Pair × WETH9 | ✓ | ✓ [r] | ✓ [s] | ✓ HASH-T [t] | ~ [u] | ✓ [v] | ~ [w] | ✓ [x] |
| Uniswap V2 Pair × USDC × WETH9 | ✓ | ✓ [y] | ✓ [z] | ✓ HASH-T [aa] | ~ [ab] | ✓ [ac] | ✗ | ✓ [ad] |
| Curve 3pool | ✓ | ✓ | ✓ [ae] | ✓ HASH-T [af] | ✓ [ag] | ✓ [ah] | ~ [ai] | ✓ [aj] |

[a] Freshness is over the uniform five-key set per raw target frame (Section
5.1). [b] A modeled deployment message under every covered fork (the
`_covered` forms); the deployment result is **not chained** into a configured
history (that a checkpoint equal to the deployed state starts a history is a
consumer's composition); and every historical deployment except Lido's
predates Prague (Section 7). [c] Withdraw, deposit and transfer at history
level; `approve` and `transferFrom` at frame and model level only. [d]
`withdraw` only, at a block boundary and, by the mid-block results (Section 5.1), at any transaction position of the next block. [e] Trace-local finite exclusions and `SystemCodeInstalled`
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
environments (replies and returned gas), and `skim`'s first transfer adds a
trace-local hash premise over the rows the pair's own frames decode inside that
`CALL` (§7 items 17 and 18). [o] The
deployment theorem's conclusion `InitializedCheckpoint` is literally the INIT
premise of `pair_history_initialized`, with the same factory, domain separator
and token arguments, so INIT is established by deployment followed by the
factory's `initialize`. As in [b] it is not chained into a configured history,
and that the factory issues the `initialize` call is a premise (the run is
then constructed), since the factory's bytecode is not lifted. [p] Every state-changing entry point has history-level liveness with a closed
cost (`transfer`, `approve`, `transferFrom`, `sync`, `mint`, `swap`, `burn`,
`skim`, `permit`, `initialize`). Every cost is closed over the gas
forwarded to the callees, whose consumption enters through the callee premise
(§7 item 21). [q] Deployment, initialization and liquidity are executed messages
from a creator-only world, not admitted transactions (§7 item 3 applies); the
V− transaction row (M7) starts from a different, synthetic prestate. For both V+ and V−, M5 records the executed setup of the reachable witness; the older witnesses keep their synthetic prestates.

[r] One configured history in which both certified runtimes are installed, from a
world satisfying `JointCheckpoint`; the joint invariant holds at every committed point
at which the pair is unlocked and at the end. [s] The remaining per-frame premises
are the other token's half of NoShrink and its callee records, the factory's `feeTo`
record, gas sentries and call depth; none concerns WETH9's answers. The factory's
behaviour is not a premise: the factory CODE premise replaces it (§7 item 31). [t]
Both contracts' HASH-T premises, over the keys the history touches; the token1
`burn` and `skim` liveness rows and the token1 both-outputs `swap` row add HASH-T over
the keys of child frames (§7 item 34). [u] `pair_weth9_create2_jointCheckpoint` establishes `JointCheckpoint` by the
pair's `CREATE2` deployment and `initialize`, for WETH9 as either token, from WETH9
world premises at the `initialize` world; it is not chained into a configured history,
the factory issuing `initialize` is a premise, and WETH9's own deployment is not part
of it (§7 item 28). [v] `sync`, `mint`, `burn`, `skim` and `swap`, for both sides, with
WETH9's callee records discharged; the other entry points have no token callee and keep
their Section 5.8 rows. [w] The universal rows are history level. The closed instance
runs one configured block with two signed type-2 transactions, transaction level but for
two fixed transactions from worlds agreeing with one synthetic world, and it runs the swap
at frame level inside that block (§7 item 29). [x] The history and liveness rows assume or
derive `CoveredFork`; the deployment theorem quantifies over covered forks; the closed
instance is BPO2 only. [y] One configured history in which the Pair, the factory, USDC's three runtimes and
WETH9 are installed, from a world satisfying `JointCheckpoint2`, under the governance
premise; the joint invariant holds at the committed positions outside
`UsdcShadowed` at which the pair is unlocked, and at the end (§7 items 35 to 37).
[z] Environmental premises only: the call depth, the pair not USDC's admin word, gas
sentries, the factory's `feeTo` record, USDC's state conditions for a payout, and on
`swap` the callback and its governance; both tokens' callee records are discharged
(§7 item 38). [aa] HASH-T over the touched keys of all three contracts, the LP rows of
`mint` and `burn`, and the recipient's USDC balance row of `burn`, `skim` and a `swap`
that pays USDC; no HASH-T over child frames (§7 items 38 and 39). [ab]
`pair_usdc_weth9_create2_jointCheckpoint2` establishes `JointCheckpoint2` by the
pair's `CREATE2` deployment and `initialize` from a world carrying both tokens'
checkpoint facts; it is not chained into a configured history, and the factory issuing
`initialize` is a premise. [ac] `sync`, `mint`, `burn`, `skim` and `swap` at a fresh
pair frame after the history, with both tokens' callee records discharged. [ad] The
history rows assume or derive `CoveredFork`; the deployment theorem quantifies over
covered forks.

[ae] Per-frame premises are environmental: `PoolFrameEnv` for a frame, the per-execution keep
premise for a liveness row, and for a history the per-frame `callbacks` of `PoolTraceEnv` (every
direct child keeps the pool's storage, every coin child keeps 3Crv's storage) with trace-local
exclusions; fresh entry, calldata, gas and identity readiness are derived. At frame level the
target's code and the identity precompile's readiness are premises, discharged from the trace at
history level. [af] No hash premise on the pool side (the pool's storage is at fixed slots); in the
composed statements freshness is 3Crv's `FreshKeys` (HASH-T, inherited); no HASH-U. [ag] A modeled
deployment message under every covered fork, not chained into a configured history; the joint
checkpoint of the composed statements is a premise (checked on synthetic worlds), not derived from
the two deployments (§7 items 49 and 52). [ah] All five entries (`exchange`, `add_liquidity` and the
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
shown satisfiable (§7 items 48 and 53), and the composed headlines' coin-chain hypotheses are applied as stated, with their 3Crv and coin-ledger facts taken as world conditions (§7 item 53). [ai] One fixed signed `exchange(0, 1, 100, 0)` on worlds that agree with a
fixed synthetic checkpoint, in one BPO2 block, with kernel recovery of the signer; no
transaction-level liveness for any other entry, calldata or world (§7 item 50). [aj] Every frame,
history and deployment statement carries `CoveredFork`; the closed instance is BPO2 only. [ak] For 3Crv the deployment is also chained: the recorded creation transaction in its retained Muir Glacier block is the root of a configured history (Section 5.3), so [b]'s "not chained" describes the modeled `_covered` message only.

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
3. **Deployments are modeled, not historical inclusion.** Beacon (block
   11,052,984) predates Prague, and the Vyper pools and proxies are older. WETH9
   (4,719,568) has no modeled deployment theorem: Section 5.1 states its recorded
   creation transaction inside its retained block, which is not an inclusion proof
   either (no header, block hash or state-root binding). Curve 3Crv (10,809,467) predates Prague too; its `curve_deploy_covered` is a modeled deployment like the others, and Section 5.3 in addition states its recorded creation transaction inside its retained Muir Glacier block, which is still not an inclusion proof (no header, block hash or state-root binding). The modeled deployment theorems execute
   the recorded creation input as a CREATE message under current rules
   (`deployMsg`, an empty world, 1M–3M gas). **The Lido CircuitBreaker was
   created after Prague:** its creation transaction is in block 24,993,190 with
   timestamp 1,777,555,319 (2026-04-30T13:21:59Z), after the BPO2 activation
   at 1,767,747,671, the last fork in Jaune's mainnet schedule. The historical
   deployment ran under **BPO2 rules, a covered fork**, so `lido_deploy_covered`
   includes the historical fork. It is still a modeled deployment (empty world,
   `deployMsg`), not historical inclusion. The deployment results are messages,
   not validated transactions. The reachable V± chains (Sections 5.5 and 5.6)
   are modeled messages too but have a different shape: they start from a world
   holding a funded, code-free creator, place each implementation at its
   registered address by a supplied CREATE target, and continue through
   initialization, funding and the experiment, each message from the previous
   settled world (item 25).
4. **The Beacon `_env` forms were vacuous on mainnet and have been removed.**
   The former configuredHistory_solInv_env, configuredHistory_count_env and
   configuredHistory_root_env required an offset-blind `SpawnFree`
   exclusion, which is false of the canonical EIP-7002 code
   [`Blanc.withdrawalRequestCode_not_spawnFree` (`Blanc/SystemContracts.lean:135`)]. The `_sys` form of Section 5.2
   (`configuredHistory_solInv_sys`) is the mainnet-satisfiable statement.
5. **Witness-engine guard.** The V− interpreter engine refuses synchronous
   MODEXP (0x05) and P256VERIFY (0x100) child frames
   [`Blanc.Lift.Witness.frameEntryForkFree` (`Blanc/Lift/WitnessArms.lean:1056`), used by `Blanc.Lift.Witness.callStep` (`Blanc/Lift/WitnessArms.lean:1065`)]. The `wrun … = .cont`
   run conjuncts of `vminus_witness` therefore also mean that the run enters no
   MODEXP or P-256 frame; that is what makes the runs fork-uniform. The V+ walks
   expose spawns as explicit nodes and execute no CLZ and no MODEXP or
   P256VERIFY.
6. **The following witness and deployment forms cover Prague, Osaka,
   BPO1 and BPO2:** the listed V± message witnesses are closed;
   `vminus_txC_message` is closed, while `vminus_txC_process` requires
   block room; the reachable capstones are closed, while
   `vminus_reach_violation` takes `Checkpoint W`. The forms are
   `vplus_witness_covered`, `vplus_witness2_covered`, `vminus_witness_covered`,
   `vminus_txC_{message,process}`, `vplus_exit`, `vminus_attack`, `vplus_reachable_capstone`,
   `vminus_reachable_capstone`, `vminus_reach_violation`, `beacon_deploy_covered`,
   `curve_deploy_covered`, `lido_deploy_covered`, `lido_deploy_init_covered`.
7. **Synthetic prestates and fixtures (V±).** For the closed witnesses: pool
   storage (lock slots, balances, `totalSupply`), ETH balances, and the reader,
   receiver, attacker, dispatcher-attacker and coin contracts are synthetic. The
   reachable V± witnesses instead reach their pool storage by executed messages
   from a creator-only world (§5.5, §5.6); their token and receiver/attacker
   code and their clone-creation inputs remain synthetic, although the 45-byte
   forwarder runtime each clone creation installs is byte-identical to the mainnet
   forwarders' code (the stETH-ng pool's for V+; the pETH/ETH, msETH/ETH and
   alETH/ETH pools' for V−). The coin-1 contract in
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
    (`lido_remove_repairs`, the committed invocation lists) say nothing of
    frames rolled back or under a rolled-back ancestor.
12. **Curve cost is exact but existential** (`∃ c`), with no closed formula.
    **WETH9 frame keys are a uniform five-key set** (Section 5.1).
13. **Liveness frames are fresh frames** (empty stack and memory) at a state,
    not transactions, except `weth9_tx_withdraw`, its history form and its
    mid-block form (Section 5.1), and the closed Pair × WETH9 instance (Section 5.9).
14. **`SystemCodeInstalled`.** The canonical system bytes come from a Jaune test fixture
    (Section 2). For EIP-7002 the 504-byte runtime is provider-corroborated: three separately operated RPC services
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
    divergence the two fees agree exactly (`Blanc.Lift.WithdrawalRequest.word_fee_eq_iff_natFeeDomain` (`Blanc/Lift/WithdrawalRequest/ExactFeeDomain.lean:27`); against the EIP's formula directly, `Blanc.Lift.WithdrawalRequest.fee_eq_spec_iff` (`Blanc/Lift/WithdrawalRequest/HeadlineFee.lean:48`)). The FIFO headline is therefore stated
    for the executed word fee.
17. **Uniswap V2 Pair: token and factory behaviour is a premise.** The pair observes
    only what `balanceOf` and the factory's `feeTo` answer. The replay, ledger,
    oracle and refinement rows take no such premise. The replay forms of the
    share-value rows take, over the replay's own steps only, `EntryNoShrink` (for `sync`, both answers at
    least the stored reserves; for `burn`, both first answers at least the stored
    reserves and each first answer at most its final answer plus its payout) and,
    for the fee-off row, `EntryFeeOff` (the `feeTo` answer of a mint or burn is
    zero). The per-call headlines `pair_share_value` and `pair_share_value_feeOff`
    take the same conditions over the outer call itself (`BalanceAnswersBacked`,
    `FeeAnswered`, `FeeToOff`), read from the frames the call's own calls entered:
    an answer that came from a precompile or from a call that entered no frame does
    not satisfy them, and nothing is assumed about any other call. NoShrink constrains only the pair's own balance answers, not what a
    recipient receives: a token that takes its transfer fee from the recipient's
    proceeds, or whose balances only grow (positive rebases, donations), can
    satisfy it, while extra debits of the pair or downward rebases can violate
    it. No theorem claims that a recipient is credited, or that a real token
    satisfies it, except WETH9's half under the premises of Section 5.9 (item 27); positional authentication of the answers of the history's selected
    steps (item 26) does not prove that any token meets the premise. The burn form is deliberately weaker
    than "every answer is at least the stored reserve", which no ordinary burn
    satisfies.
18. **`skim`'s first transfer carries a trace-local hash premise.** That the
    first transfer `CALL` leaves the pair's lock-guarded fields unchanged (the
    supply, the three packed reserve fields, both price accumulators, `kLast` and
    the lock) is derived, not assumed: the pair is locked during the `CALL`, so a
    re-entry either meets the lock or is an unlocked entry that writes only its
    own rows. The derivation needs exact freshness of the mapping rows that those
    re-entered pair frames decode, a HASH-T premise over that one `CALL`'s trace,
    and nothing about what the callee does. The other liveness rows state their
    callee environments (replies and returned gas) and no such premise.
19. **The Uniswap V2 Pair replay is nested, not a flat per-frame replay.** The
    steps are the **outermost** settlement-committed non-static pair frames. A pair
    frame re-entered from inside a token call, the flash-swap callback or a factory
    call is consumed inside its parent step's transcript, so the list of steps can
    be shorter than the list of committed pair frames; the observation equality of
    `pair_history_committed` places every committed pair frame in exactly one
    step's subtree. Rolled-back frames are not in the replay, and static frames
    observe nothing.
20. **Not claimed for the Uniswap V2 Pair.** Section 5.9 composes the pair with
    WETH9 over one configured history from a world satisfying `JointCheckpoint`, for
    pairs whose stored factory holds the factory runtime. Outside that scope,
    composition with WETH9 is not claimed: not for the live exhibit pool (item 28),
    not for a pair whose factory holds other code, not for a pair that reaches WETH9
    through a wrapper or router, and not for any other token than WETH9 and USDC
    (Section 5.10 composes the pair with both, USDC as `token0`). Also not claimed:
    transaction-level liveness beyond the closed instance of Section 5.9; permit
    signature unforgeability is not claimed (only the result of the modeled
    ECRECOVER precompile is an input); that the factory's code issues the `initialize`
    call of the deployment theorems, and the factory's feeTo answers are not
    discharged from the lift (both stay premise-level messages, although the factory's
    runtime is lifted and used in Section 5.9); the router, whose bytecode is not
    lifted; the real transaction history of the exhibit pair; and any statement that
    a price, the TWAP or the economics of the pool are fair or safe.
21. **Uniswap liveness scope.** The history-level liveness rows cover `transfer`,
    `approve`, `transferFrom`, `sync`, `mint`, `swap`, `burn`, `skim`, `permit`
    and `initialize`; for `permit` the `ECRECOVER` precompile's answer is a callee
    input, and signature unforgeability is not claimed. Each cost is a closed
    expression, not an existential cost, but it is closed over the gas forwarded to
    each callee: the callees' consumption is fixed by the `returnedGas` equations of
    the callee premise. Premise-free liveness is false: a token or callback
    recipient whose code reverts defeats every raw run of `sync`, `skim`, `mint` and
    `swap` (the controls of Section 5.8).
22. **The Uniswap oracle row is per outer call.** The headline `pair_oracle`
    states, for each outer call of the Pair, one increment over the stored entry
    reserves and the stored-timestamp advance (the floor formula over the wrapped
    `Δt` of `OracleUpdate.Lawful`), with the stored timestamp staying or becoming
    the call's block time modulo 2^32. It states no sum over the history, nothing
    about which block a call's frame belongs to beyond that frame's own block
    environment, and nothing about the Pair's storage between one outer call's
    exit and the next one's entry.
23. **Altitude of the Uniswap controls.** The model controls run the typed
    functional model, not EVM execution. The bytecode controls are universal over
    successful raw runs and exhibit no concrete reverting run. No frame-level
    burn-rounding control is claimed.
24. **The Uniswap deployment is modeled.** `pair_create2_initialized` is the
    `CREATE2` step of a non-static factory frame, with the constructor run inside
    the step, followed by a successful `initialize` from the creator;
    `pair_create2_initialize_live` constructs that `initialize` run for a frame
    the creator calls. It is not
    historical inclusion, it is not chained into a history, and the creation
    transaction of the exhibit pair is not recorded. The exhibit address is the
    `CREATE2` address of the factory, the salt and the creation code by kernel
    evaluation, not a statement about the chain.
25. **The reachable V± witnesses are message level.** They do not model the
    transaction and block effects around a message: sender nonce increments and
    nonce-derived creation addresses, intrinsic gas, fees and refunds, the
    coinbase payment, warm sets (an admitted transaction warms its sender, its
    target and the precompiles; these messages start from empty access sets),
    block-level system calls, withdrawals and EIP-7702 delegations. Some of these
    run code: a block's system calls execute messages that write their system
    contracts' storage (EIP-4788's beacon-roots contract, for example). None of
    them is addressed to the pool, token or attacker contracts of these
    witnesses, but no theorem proves that their slots are preserved, and changed
    balances, gas or warm sets could change later execution. The implementation
    addresses are supplied `CREATE` targets, not the nonce-derived addresses of
    the creator, whose nonce stays zero. That equivalent messages are producible
    by admitted transactions (sender keys, nonce-derived addresses, gas and warm
    sets) is argued, not proved.
26. **Scope of the positional Uniswap statements.** The two history headlines
    (`pair_history_committed` and `pair_history_initialized`), the common
    replay and outcome (`pair_history_replayed`, `pair_live_outcome`) and the six
    Live and two Admin routes of Section 5.8 instantiate the concrete eleven-family
    admitted supplier `pairAdmittedSupply` (built by `pairAdmittedSupplyRules`, with
    `pair_admitted_skim_supply`, `pair_admitted_burn_supply` and
    `pair_admitted_swap_supply` for the three families with mutable external
    calls). For each step the actual call position, reply, entered bit and full
    nested queues feed one recursively admitted consumption, so the two reads of a
    token's balance by `burn` are told apart by position; NoShrink and the bounds
    stated over the replay by the share-value and minimum-liquidity rows range over
    the same selected steps (`steps.map PairStep.source`). NoShrink remains a premise about
    the
    selected actual answers and is not proved for any token; the protocol fee,
    token behavior, the hash and initialization assumptions and the caller and
    deployment assumptions remain premises as stated in the rows; and no
    composition of the pair with token or factory economics is claimed.
27. **Pair × WETH9: the other token's half stays a named premise.** The composition
    removes WETH9's half of NoShrink and WETH9's callee records, and nothing else: the
    share-value rows keep the other token's half of NoShrink (and, fee off, the
    fee-off condition) as an antecedent, and the liveness rows keep the other token's
    callee records, the factory's `feeTo` record, the callback and the gas sentries
    (ENV). Outside Section 5.10, which discharges USDC's half under its own premises
    (items 35 to 39), no theorem says that another token meets its half.
28. **Pair × WETH9: what is not done.** The live state is not checked: no theorem or
    gate says that mainnet's WETH9 or any mainnet pair, the exhibit pair included,
    satisfies `JointCheckpoint` at any block, and no storage was fetched. USDC's
    runtimes were not lifted for this section (Section 5.10 lifts them). The full deployment sequence is not
    executed: deploying WETH9, depositing, deploying the pair, `initialize`, adding
    liquidity and swapping as one execution is not modeled; the deployment theorem
    starts from WETH9 world premises, and the closed instance starts from a synthetic
    world. The first and the last were deliberately left for later work, not overlooked.
29. **The closed instance exercises the discharged WETH9 side at frame level.** Its
    swap is the second transaction of its block, not a frame after a configured
    history, so the history-level liveness rows of Section 5.9 are not applied to it.
    The swap frame is instead run inside the block by the Pair's certified frame-level
    walk of `swap`, with WETH9's `transfer` and `balanceOf` runs taken from the same
    leg facts those rows use and `X`'s `balanceOf` from `X`'s code; it succeeds with
    exact gas and the `Transfer`, `Sync` and `Swap` logs. The joint invariant and the fee-off
    share-value row are applied to the configured history from the checkpoint to the
    end of the block.
30. **The universal closed-instance form takes `Canonical` and `SumNof`.**
    `uniswap_weth9_closed_agreeing` holds for every world that is canonical (no empty
    account and no zero storage word stored), whose total ether is below 2^256, and
    that agrees with `W0` on the ten touched accounts. It takes no `JointCheckpoint`
    premise: the checkpoint is transported from `W0` through the agreement. Its
    strict share-value increase is stated from `W0`'s pair state to the end at equal
    supply, not between arbitrary steps.
31. **The factory CODE premise.** The Section 5.9 headlines take that the pair's
    stored `factory` address holds the certified factory runtime at the checkpoint,
    and that it is not the system address. They therefore cover pairs whose factory is
    the canonical factory code; for those, the factory's behaviour is not a premise
    (`pair_history_factoryQuiet`). The pair's `initialize` has no one-shot guard, and
    without this premise a factory call could replace the stored tokens.
32. **The joint checkpoint's INIT facts.** Besides both codes, the pair's
    representation, WETH9's footprint and the reserve bound, `JointCheckpoint` requires
    `token0 ≠ token1`, the pair neither 0 nor the system address, the pair not WETH9,
    and WETH9 no precompile under any covered fork; for `W0` all of them, and the
    factory CODE premise, are checked by the kernel-evaluated checker. The deployment
    theorem takes the corresponding facts about the new address and the other token as
    premises, for either token ordering.
33. **For `swap`, NoShrink's WETH9 half is trivially true.** `EntryNoShrinkSide` is
    `True` for every entry other than `sync` and `burn`, so the share-value rows
    discharge real content only at `sync` and `burn` steps; for `swap`, the WETH9
    premises the composition removes are the liveness callee records. In the closed
    instance the other token's antecedent is discharged the same way: the history's
    only pair step is the swap. It is not derived from `X`'s code.
34. **Three token1 rows take HASH-T over child frames.** With WETH9 as
    `token1`, the other token is called first, so these rows take exact freshness of
    WETH9's keys touched inside the `STATICCALL` children that precede WETH9's
    transfer (`burn`: the other token's initial query and the factory query; `skim`:
    the other token's query), and of the keys the other token's transfer child
    touches, against WETH9's key universe and against the pair's rows. These are
    HASH-T premises of the same kind as the history's, trace-local and about keys
    only; none concerns WETH9's answers. A theorem that static calls preserve WETH9's
    balances would remove the static-child ones; it is not proved. The token1
    both-outputs `swap` row takes the same freshness over the keys of the other token's
    transfer child, when that token is paid out.
35. **Pair × USDC × WETH9: the governance premise.** `UsdcGovernance`: no settled
    entry frame at USDC's proxy whose caller is the checkpoint's admin word calls
    `upgradeTo`, `upgradeToAndCall` or `changeAdmin`. It names an actor and three entry
    points, not an outcome; from it the implementation slot and the admin word are
    proved unchanged along the history. Every Section 5.10 history row takes it.
36. **Pair × USDC × WETH9: the never-signer premise, removed.** No Section 5.10 row
    takes `NeverSigner usdc (usdcBookS usdc) trace pair` (no settled non-static USDC
    entry frame along the history, a `permit`, transferWithAuthorization,
    receiveWithAuthorization or cancelAuthorization, has the pair as its signer): it
    is proved, `usdc_neverSigner_pair`. A pair holding the Pair runtime has code, so
    USDC's library checks its signature only by an ERC-1271 isValidSignature static
    call, which the pair's code does not answer; reading the library's calldata word
    and returned flag uses a certified solc free-memory-pointer invariant at USDC's
    two library call sites. The proof needs the pair to be no precompile (a precompile
    at the pair's address could echo the call), so `JointCheckpoint2` and
    `JointCheckpoint2F` carry a pair-not-precompile field, which the kernel-evaluated checkers
    decide over the covered forks and which `pair_usdc_weth9_create2_jointCheckpoint2`
    takes for the new address, as it takes USDC's and WETH9's.
37. **Pair × USDC × WETH9: excluded positions.** The joint invariant is stated only at
    settled positions that are not `UsdcShadowed`: a frame at the proxy that is not an
    entry frame (an implementation or library frame running over the proxy's storage,
    static or not), and a position inside the block of an earlier library frame at the
    proxy (the ERC-1271 and `ecrecover` static calls a signed message makes, at which
    part of its effect, such as `permit`'s nonce increment, may already be written).
    Settled frame values need not be unique, so the exclusion is by position.
38. **Pair × USDC × WETH9: the liveness premises.** Beyond the history premises, every
    Section 5.10 liveness row takes: call depth at least 2 at the pair frame (USDC's
    `DELEGATECALL` adds a level); the pair is not USDC's admin word at the frame; and
    explicit 63/64 gas sentries for each token leg. The rows that pay USDC out (`burn`,
    `skim`, and `swap` when `amount0Out ≠ 0`) also take USDC's state conditions at the
    frame (not paused, the pair and the recipient unflagged, the credit within the
    packed word, both parties nonzero) and HASH-T for the recipient's USDC balance row.
    `swap` takes, when the callback runs, that it leaves
    USDC's implementation slot and does not make the pair USDC's admin (the governance
    premise at frame level). `skim` takes no `FirstCallFresh`: USDC's `transfer` is
    proved to keep the pair's storage. `mint` and `burn` keep the factory's `feeTo`
    record as in Section 5.9.
39. **Pair × USDC × WETH9: the key universe.** As for WETH9, USDC's history key
    universe is the checkpoint's tracked keys extended by the keys every frame at the
    proxy may touch, read from its calldata and caller, whether or not the frame
    commits; HASH-T is stated over that universe. In the general statements the
    checkpoint's tracked set is any predicate; a checkpoint the checker accepts tracks
    exactly its finite rows.
40. **Pair × USDC × WETH9: not claimed.** Anything about the live state of USDC or of
    any pool, the exhibit pair included (no storage was fetched); the closed
    single-block USDC instance, which is not built; USDC versions other than
    FiatTokenV2_2 at the stated implementation address; and anything at the positions
    item 37 excludes.
41. **Pair × USDC × WETH9: the support-free headlines.** The `JointCheckpoint2F`
    checkpoint keeps injectivity, apartness and ledger goodness over the tracked keys
    (`FootCoreL`) and drops the storage-wide support half. The joint invariant, both
    share-value rows and the `swap` row are proved from it with the trace-local premise
    `PairUsdcAllowQuiet` — every touched Pair allowance row reads zero at the
    checkpoint — in place of support; the `mint`, `burn`, `skim` and `sync` rows take
    neither. The support-free checker `checkJoint2F` is sound for `JointCheckpoint2F`,
    and the stray-slot control shows the difference: with one nonzero word at the
    unlisted slot the support-free checker still accepts while the support-checking
    checker rejects.
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
uses (`scripts/leaf_audit.py`, `scripts/GATES.md` "Leaf audit"), each covered
by the union walk. It is generated
into `scripts/leaf-count.json` (never hand-edited) and quoted by the README and
the sites. At this commit it is 2274 leaf results (2216 public, 58 private).
The review ledger separately records the last review; the audit reports new
or changed leaves. The count is a property of the library at a commit, not of any cited theorem;
a cited theorem that another theorem uses is simply not a leaf. Bind any
quoted figure to `git rev-parse HEAD`, as the README does.

## 9. Named premises and definitions

Names that the tables above write unqualified.

| Name | Declaration | Role |
|---|---|---|
| `CoveredFork` | `Blanc.CoveredFork` (`Blanc/Semantics.lean:167`) | the covered forks: Prague, Osaka, BPO1, BPO2 |
| `ConfiguredHistoryTrace` | `Blanc.ExecutionTrace.ConfiguredHistoryTrace` (`Blanc/ExecutionHistory.lean:116`) | a retained replay of validated blocks under a valid chain configuration |
| `FrameAdmitted` | `Blanc.ExecutionTrace.ConfiguredHistoryTrace.FrameAdmitted` (`Blanc/ExecutionHistoryAdmission.lean:27`) | pointwise admission of every interpreter execution retained by a configured history, against a per-frame entry predicate |
| `SumNof` | `Blanc.SumNof` (`Blanc/LadderBase.lean:8`) | a total below 2^256 |
| `SystemCodeInstalled` | `Blanc.SystemCodeInstalled` (`Blanc/SystemContracts.lean:165`) | the canonical system-contract bytes are installed at their addresses |
| `NoAuthorityAt` | `Blanc.ExecutionTrace.ConfiguredHistoryTrace.NoAuthorityAt` (`Blanc/ExecutionTraceCodeAt.lean:462`) | no authorization of any transaction of a configured history recovers to the given address |
| `SpawnFree` | `Blanc.SpawnFree` (`Blanc/ExecutionTraceSystem.lean:24`) | the code has no instruction that could spawn a child frame, read at every offset (false of the canonical EIP-7002 code) |
| `FootInv` | `Blanc.Lift.Weth9.FootInv` (`Blanc/Lift/Weth9/Footprint.lean:79`) | WETH9's footprint invariant: support, injective and apart tracked slots, and the tracked ledger backed by the contract's ether |
| `KeysFresh` | `Blanc.Lift.Weth9.KeysFresh` (`Blanc/Lift/Weth9/Footprint.lean:59`) | each touched key is tracked or on an unused slot, and keys sharing a slot are one key (HASH-T) |
| `KeyInj` | `Blanc.Lift.Weth9.KeyInj` (`Blanc/Lift/Weth9/Footprint.lean:53`) | tracked slots are pairwise distinct |
| `frameKeys` | `Blanc.Lift.Weth9.frameKeys` (`Blanc/Lift/Weth9/FootFrame.lean:57`) | the decode-free five-key over-approximation of the keys a frame's call may touch |
| `Weth9.historyTouchedKeys` | `Blanc.Lift.Weth9.historyTouchedKeys` (`Blanc/Lift/Weth9/FootHistory.lean:64`) | the keys a WETH9 history touches, rolled-back frames included |
| `SendOk` | `Blanc.Lift.Weth9.SendOk` (`Blanc/Lift/Weth9/LiveWriters.lean:799`) | the callee premise of WETH9 `withdraw` to a contract: the CALL to the caller succeeds, leaves at least 1489 gas, and changes no storage of the contract |
| `AllowAdmitted` | `Blanc.Lift.Weth9.AllowAdmitted` (`Blanc/Lift/Weth9/Premise.lean:24`) | both allowance images written by the allowance entry points are off the balance image for this frame (a local HASH-U premise) |
| `SolInv` | `Blanc.Lift.BeaconDeposit.SolInv` (`Blanc/Lift/BeaconDeposit/Layout.lean:42`) | Beacon's storage abstraction: an intact zero-hash table and the model invariant for a deposit history |
| `beaconEntry` | `Blanc.Lift.BeaconDeposit.beaconEntry` (`Blanc/Lift/BeaconDeposit/Ladder.lean:130`) | Beacon's carried entry condition: calldata length below 2^256, the SHA-256 precompile account (`0x02`) not a delegation, and warm |
| `DepositDecodable` | `Blanc.Lift.BeaconDeposit.DepositDecodable` (`Blanc/Lift/BeaconDeposit/DepositArgs.lean:55`) | the deployed decoder accepts the deposit calldata |
| `ShaReady` | `Blanc.Lift.ShaReady` (`Blanc/Lift/ExactWalkCutOps.lean:81`) | the SHA-256 precompile premises of a frame's world: address 2 undelegated and warm, a precompile of the fork |
| `VyInv` | `Blanc.Lift.Curve3Crv.VyInv` (`Blanc/Lift/Curve3Crv/Layout.lean:95`) | Curve 3Crv's storage abstraction over the live keys |
| `FreshKeys` | `Blanc.Lift.Curve3Crv.FreshKeys` (`Blanc/Lift/Curve3Crv/Layout.lean:115`) | the frame-local premise for the keys a Curve frame touches: each is fresh and their slots are pairwise distinct (HASH-T) |
| `Curve3Crv.historyTouchedKeys` | `Blanc.Lift.Curve3Crv.historyTouchedKeys` (`Blanc/Lift/Curve3Crv/CarriedHistory.lean:27`) | the keys a Curve history touches |
| `OwnerCallOk` | `Blanc.Lift.Curve3Crv.OwnerCallOk` (`Blanc/Lift/Curve3Crv/LiveBodies.lean:1840`) | the callee premise of Curve `set_name`: its static `owner()` call answers whenever it is given enough gas, and leaves at least `R` gas |
| `C3crvDeploymentTo` | `Blanc.Lift.Curve3Crv.C3crvDeploymentTo` (`Blanc/Lift/Curve3Crv/HistDeployment.lean:37`) | the 3Crv deployment record: the retained Muir Glacier block that created the token, its transaction at index 76 and successful receipt, the configured history to the checkpoint, and HASH-T freshness |
| `OwnerAnswerH` | `Blanc.Lift.Curve3Crv.OwnerAnswerH` (`Blanc/Lift/Curve3Crv/SafeBodies.lean:41`) | `OwnerAnswer` under the frame's actual delegation rules: the frame's static `owner()` call succeeded and returned a word starting with the recorded one |
| `HistFork` | `Blanc.HistFork` (`Blanc/HistoricalFork.lean:21`) | the historical extraction domain, Byzantium through BPO2, Amsterdam excluded |
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
| `HashAvoidIn` | `Blanc.LockExclusion.LockSpec.HashAvoidIn` (`Blanc/LockExclusion.lean:817`) | every frame of the pool running the lock code avoids the lock slot with its executed hashes (HASH-T) |
| `VplusExcludes` | `Blanc.Lift.VyperNonreentrantDeployed.Fixed.VplusExcludes` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:44`) | the statement form of the V+ exclusion |
| `InitializedCheckpoint` | `Blanc.Lift.UniswapV2Pair.InitializedCheckpoint` (`Blanc/Lift/UniswapV2Pair/Creation/DeployInit.lean:34`) | the Pair's INIT after deployment and `initialize`: the pair storage represents `initializedState` over the empty tracked footprint |
| `initializedState` | `Blanc.Lift.UniswapV2Pair.initializedState` (`Blanc/Lift/UniswapV2Pair/Creation/DeployInit.lean:29`) | the model state after a factory deploys a pair with a given domain separator and initializes it with two tokens: zero supply, reserves, accumulators and `kLast`, `unlocked = 1`, no ledger row |
| `WriterRep` | `Blanc.Lift.UniswapV2Pair.WriterRep` (`Blanc/Lift/UniswapV2Pair/WriterStorage.lean:72`) | the Pair's storage abstraction over a finite tracked set of balance, allowance and nonce rows: slots 0 to 12 match the model, each tracked row matches, every other nonzero word is at a tracked row, and untracked rows are zero in the model |
| `WriterFreshKeys` | `Blanc.Lift.UniswapV2Pair.WriterFreshKeys` (`Blanc/Lift/UniswapV2Pair/WriterStorage.lean:36`) | HASH-T for the Pair: each touched row is tracked or on a slot that is neither fixed nor a tracked row's, and rows sharing a slot are one row |
| `pairHistoryTouchedKeys` | `Blanc.Lift.UniswapV2Pair.pairHistoryTouchedKeys` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:378`) | the rows the Pair's frames select, over every raw Pair frame root of a history, rolled-back frames included |
| `PairStep.AuthenticWith` | `Blanc.Lift.UniswapV2Pair.PairStep.AuthenticWith` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:218`) | a step's frame is a pc-0, committed, non-static frame at the pair, and a given relation `Auth` holds of the frame's root derivation, entry and transcript; the headlines use `PairEntryAuth` |
| `PairEntryAuth` | `Blanc.Lift.UniswapV2Pair.PairEntryAuth` (`Blanc/Lift/UniswapV2Pair/PairPositionalEntry.lean:34`) | the step's entry is the one the root frame's own selector and calldata decode; it names no callee answer, which `PairAdmittedConsumes` consumes |
| `PairObservedReplayWith` | `Blanc.Lift.UniswapV2Pair.PairObservedReplayWith` (`Blanc/Lift/UniswapV2Pair/PairHistory.lean:168`) | the steps are consumed in order, each by a given consumption relation on its own root derivation, from the carried model state, with the step's actual returned bytes as the result's output |
| `PairAdmittedConsumes` | `Blanc.Lift.UniswapV2Pair.PairAdmittedConsumes` (`Blanc/Lift/UniswapV2Pair/PairPositionalAdmission.lean:16`) | one positional consumption of a root derivation (the actual position of every external call, its reply, the entered bit and the full nested queues) together with recursive admission of its mutable children on the same selection |
| `pairAdmittedSupply` | `Blanc.Lift.UniswapV2Pair.pairAdmittedSupply` (`Blanc/Lift/UniswapV2Pair/PairPositionalSupply.lean:58`) | the concrete eleven-family supplier of admitted outcomes for every successful pc-0 pair execution, dispatched by selector |
| `EntryNoShrink` | `Blanc.Lift.UniswapV2Pair.EntryNoShrink` (`Blanc/Lift/UniswapV2Pair/Properties.lean:2643`) | the token-answer premise of the share-value rows, per entry (ENV: callee behaviour; exact forms in Section 7 item 17) |
| `EntryFeeOff` | `Blanc.Lift.UniswapV2Pair.EntryFeeOff` (`Blanc/Lift/UniswapV2Pair/Properties.lean:2657`) | the factory's `feeTo` answer of a mint or burn is zero (ENV: callee behaviour) |
| `sourceReplayAnswers` | `Blanc.Lift.UniswapV2Pair.sourceReplayAnswers` (`Blanc/Lift/UniswapV2Pair/SourceReplay.lean:78`) | at every step of a replay, `EntryFeeOff` and `EntryNoShrink` at the carried model state |
| `sourceReplayNoShrink` | `Blanc.Lift.UniswapV2Pair.sourceReplayNoShrink` (`Blanc/Lift/UniswapV2Pair/SourceReplay.lean:123`) | at every step of a replay, `EntryNoShrink` at the carried model state |
| `prefixTouchedKeys` | `Blanc.Lift.Weth9.prefixTouchedKeys` (`Blanc/Lift/Weth9/FootPrefix.lean:13`) | the keys a WETH9 mid-block result ranges over: the prior history's touched keys followed by the uniform five-key `frameKeys` of every raw frame at the contract in both opening system calls and the transaction prefix, rolled-back frames included |
| `FirstCallFresh` | `Blanc.Lift.UniswapV2Pair.SkimForwardEnv.FirstCallFresh` (`Blanc/Lift/UniswapV2Pair/SkimForwardKeep.lean:65`) | the hash premise of `skim`'s first transfer: the mapping rows decoded by the pair's own frames inside that `CALL` are fresh against the history's universe (HASH-T, trace-local) |
| `Book` | `Blanc.Lift.Token.Book` (`Blanc/Lift/Token/Core.lean:48`) | a token's pure book: an abstract ledger, the step of one entered frame's message, the decoded operation, balances, allowances and a well-formedness predicate; no storage layout |
| `BookLaws` | `Blanc.Lift.Token.BookLaws` (`Blanc/Lift/Token/Core.lean:62`) | the laws of a book that the composition consumes (Section 5.9) |
| `Core` | `Blanc.Lift.Token.Core` (`Blanc/Lift/Token/Core.lean:98`) | what a token's address answers along a configured history, under an instance-chosen trace-local premise |
| `IsEntry` | `Blanc.Lift.Token.IsEntry` (`Blanc/Lift/Token/Core.lean:85`) | a frame entered at the token: storage owner and code address are both the token |
| `Erc20Abi` | `Blanc.Lift.Token.Erc20Abi` (`Blanc/Lift/Token/Abi.lean:17`) | the book reads the standard `transfer` and `balanceOf` selectors as those operations, for every calldata of at least 68 (`transfer`) or 36 (`balanceOf`) bytes and below 2^256 |
| `SelfCaller` | `Blanc.Lift.Token.SelfCaller` (`Blanc/Lift/Token/SelfCaller.lean:18`) | every entry-frame child of a settled non-static frame at the token has the token as caller |
| `TransferLive` | `Blanc.Lift.Token.TransferLive` (`Blanc/Lift/Token/Core.lean:145`) | frame-level `transfer` liveness at an exact cost, at the worlds an instance accepts |
| `Weth9Hist` | `Blanc.Composition.Weth9Token.Weth9Hist` (`Blanc/Composition/Weth9Token.lean:44`) | WETH9's trace-local premises as a token core: CODE, `SumNof`, `FootInv K₀` and `KeysFresh` over the history's touched keys |
| `TokenSide` | `Blanc.Lift.UniswapV2Pair.TokenSide` (`Blanc/Lift/UniswapV2Pair/PropertiesSides.lean:15`) | which of a pair's two tokens: `token0` or `token1` |
| `EntryNoShrinkSide` | `Blanc.Lift.UniswapV2Pair.EntryNoShrinkSide` (`Blanc/Lift/UniswapV2Pair/PropertiesSides.lean:74`) | one token's half of `EntryNoShrink`; `True` for every entry other than `sync` and `burn` |
| `sourceReplayNoShrinkSide` | `Blanc.Lift.UniswapV2Pair.sourceReplayNoShrinkSide` (`Blanc/Lift/UniswapV2Pair/PropertiesSides.lean:128`) | `EntryNoShrinkSide` for one side at every step of a replay |
| `sourceReplayAnswersSide` | `Blanc.Lift.UniswapV2Pair.sourceReplayAnswersSide` (`Blanc/Lift/UniswapV2Pair/PropertiesSides.lean:135`) | `EntryFeeOff` and one side's `EntryNoShrinkSide` at every step of a replay |
| `JointAt` | `Blanc.Composition.PairTokenJoint.JointAt` (`Blanc/Composition/PairTokenJointAt.lean:20`) | the joint relation at a world: the side's stored reserve is at most the token's booked balance of the pair, and the pair has granted no booked allowance |
| `JointCheckpoint` | `Blanc.Composition.UniswapV2PairWeth9Joint.JointCheckpoint` (`Blanc/Composition/UniswapV2PairWeth9Checkpoint.lean:29`) | the joint checkpoint of the Pair and WETH9 on one world state: both codes, the pair's representation of an unlocked state with WETH9 on the side, WETH9's footprint with the pair's balance row tracked and its allowance rows zero, `SumNof`, the reserve bound, and the INIT facts of Section 7 item 32 |
| `checkJoint` | `Blanc.Composition.UniswapV2PairWeth9Joint.checkJoint` (`Blanc/Composition/UniswapV2PairWeth9CheckJoint.lean:39`) | the computable decision of `JointCheckpoint` over a finite description |
| `W0` | `Blanc.Composition.UniswapV2PairWeth9Instance.W0` (`Blanc/Composition/UniswapV2PairWeth9W0.lean:83`) | the synthetic world of the closed Pair × WETH9 instance |
| `AgreesW0` | `Blanc.Composition.UniswapV2PairWeth9Capstone.AgreesW0` (`Blanc/Composition/UniswapV2PairWeth9CapstoneWorld.lean:27`) | a world holds the same account as `W0` at each of the ten accounts the closed block touches |
| `ClosedSwapOutcome` | `Blanc.Composition.UniswapV2PairWeth9Capstone.ClosedSwapOutcome` (`Blanc/Composition/UniswapV2PairWeth9CapstoneUniversal.lean:45`) | what the closed block does on a world: a valid transition, the WETH9 ledger move, the reserves, the joint invariant and the fee-off share-value row with its strict increase |
| `UsdcGovernance` | `Blanc.Lift.Usdc.UsdcGovernance` (`Blanc/Lift/Usdc/Governance.lean:21`) | USDC's governance premise: no settled entry frame at the proxy from the admin word calls upgradeTo, upgradeToAndCall or changeAdmin |
| `NeverSigner` | `Blanc.Lift.Token.NeverSigner` (`Blanc/Lift/Token/Signed.lean:41`) | no settled non-static entry of the token along a history has the given account as signer |
| `UsdcShadowed` | `Blanc.Lift.Usdc.UsdcShadowed` (`Blanc/Lift/Usdc/HistoryReplay.lean:39`) | a non-entry frame at the proxy (implementation or library), or a position inside the block of an earlier library frame |
| `JointCheckpoint2` | `Blanc.Composition.UniswapV2PairUsdcWeth9.JointCheckpoint2` (`Blanc/Composition/UniswapV2PairUsdcWeth9Checkpoint.lean:33`) | the two-token joint checkpoint of the Pair, USDC (`token0`) and WETH9 (`token1`) on one world state |
| `checkJoint2` | `Blanc.Composition.UniswapV2PairUsdcWeth9.checkJoint2` (`Blanc/Composition/UniswapV2PairUsdcWeth9CheckJoint.lean:92`) | the computable decision of `JointCheckpoint2` over finite row lists |
| `checkUsdc` | `Blanc.Lift.Usdc.checkUsdc` (`Blanc/Lift/Usdc/FiniteFootprint.lean:37`) | USDC's checkpoint checker on fetched rows: codes, implementation slot, layout and fixed words |
| `BookS` | `Blanc.Lift.Token.BookS` (`Blanc/Lift/Token/Signed.lean:20`) | a pure book with an authorizer function (`signer`) |
| `BookLawsS` | `Blanc.Lift.Token.BookLawsS` (`Blanc/Lift/Token/Signed.lean:25`) | the signature-variant laws of a book, admitting the holder's signature as a third authorizer |
| `usdcBookS` | `Blanc.Lift.Usdc.usdcBookS` (`Blanc/Lift/Usdc/Book.lean:48`) | the pure book of USDC at a given proxy address |
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
| `MintFits` | `Blanc.Composition.Curve3PoolCalleeLive.MintFits` (`Blanc/Composition/Curve3PoolCalleeLive.lean:364`) | 3Crv accepts `mint(d, v)` from the pool at the given storage |
| `BurnFits` | `Blanc.Composition.Curve3PoolCalleeLive.BurnFits` (`Blanc/Composition/Curve3PoolCalleeLive.lean:371`) | 3Crv accepts `burnFrom(f, v)` from the pool at the given storage |
| `StaticWordCallProfile` | `Blanc.Lift.StaticWordCallProfile` (`Blanc/Lift/ExactCallProfile.lean:93`) | a `STATICCALL` site answering the named word, with a debit and a successor fixed before the call's gas: the call's charge is exactly the debit |
| `MutableCallProfile` | `Blanc.Lift.MutableCallProfile` (`Blanc/Lift/ExactCallProfile.lean:104`) | a zero-value `CALL` site that succeeds and keeps the caller's storage, with a debit and a successor fixed before the call's gas |
| `AgreesP0` | `Blanc.Composition.Curve3Pool3CrvInstance.AgreesP0` (`Blanc/Composition/Curve3Pool3CrvWorldAgrees.lean:28`) | a world agrees with the 3pool closed instance's synthetic world on the touched accounts |
| `ExFrame` | `Blanc.Composition.Curve3Pool3CrvInstance.ExFrame` (`Blanc/Composition/Curve3Pool3CrvTxFrame.lean:58`) | what the 3pool closed instance's `exchange` frame sees at its entry |

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
  embedded in that creation code at bytes 261 to 11,553; the Uniswap V2 Factory row's
  code-read block and block hash appear in its certificate provenance, and its lifted
  runtime embeds that creation code at bytes 2,171 to 13,806;
- the page keeps its section structure, its required headline theorems and its
  load-bearing disclosures, and carries no process vocabulary.

The required headline theorems are also pinned by exact statement in
`scripts/ClaimCheck.lean` (gate `scripts/check-claims.sh`), together with the
definitions they are stated through whose bodies are themselves the claim (pinned
by unfolding) and the record types they use (pinned field by field), so a weakened
headline fails there although this checker elaborates no Lean. The repaired Uniswap headlines are pinned together with the definitions they are
stated through: by unfolding `PairStep.AuthenticWith`, `PairEntryAuth`,
`PairStepOutcomeWith`, `PairAdmittedOutcome`, `PairAdmittedConsumes`,
`PairSourceAdmission`, `AdmittedSourceConsumes` and `PairHistoryReplayedWith`; by
the types of their constructors, `PairEntryAt`, `PairObservedReplayWith`,
`SourceAdmission`, `MutableAdmission`, `PositionalConsumes`, `PositionalMutableTurns`
and `PositionalTurns.staticViews`; and by their record constructors,
`SourceCallAt.mk`, `BurnPositionalCanonicalResult.mk` and
`SwapPositionalCanonicalResult.mk`. Further rows are pinned there by name, among them
`weth9_history_tx_withdraw`, the WETH9 mid-block results `weth9_prefix_footprint_universe` and
`weth9_prefix_tx_withdraw`, the closed instance
`Blanc.Lift.Weth9.ClosedInstance.weth9_closed_exit_instance` with its record constructor
`ClosedExitWitness.mk`, the reachable V± witnesses (`vplus_reachable_capstone`,
`vminus_reachable_capstone`, `vminus_reach_violation`), the Lido finite tier
(`registerPauser_nonzero_finite`, `lido_create_finite_init`, `exampleApplicable`), the model laws
`runTyped_mint_initial`, `runTyped_mint_later`, `runTyped_burn_payout` and
`runTyped_swap_canonical_success`, `sqrt_of_run`, the `swap` frame theorem
`swap_bytecode_exact_consumes`, the exhibit address `pairAddress_eq` and most, not all,
of the statement controls of Section 5.8 (the burn-rounding control
`burn_witness_disagrees`, the update-walk controls and `footprintSum_dup_breaks_ledger`
are not pinned). The composition headlines of Section 5.9 are pinned there too, among
them the token interface and WETH9's instance, the factory certificate check, `pair_history_factoryQuiet`,
`pair_token_joint`, `pair_weth9_joint`, both WETH9 share-value rows, every WETH9
liveness row, `pair_weth9_create2_jointCheckpoint`, `uniswap_weth9_closed_agreeing`
and `uniswap_weth9_closed_instance`, with the statement controls of that section
other than the two checker rejections; `factory_children_fresh`, `w0_jointCheckpoint`,
the checker soundness theorems and the two checker rejections are not. Of Section 5.10,
the pins cover `pair_usdc_weth9_joint`, both share-value rows, the five liveness rows,
`JointCheckpoint2` field by field, `pair_usdc_weth9_create2_jointCheckpoint2`,
`checkJoint2_sound`, `proxy_forwards`, `usdcBook_lawsS`, `usdc_history_end`, the type
of `usdcCore`, and the definitions `UsdcGovernance`, `UsdcShadowed` and `NeverSigner`.
The finite-checkpoint pins also cover `pair_usdc_weth9_joint_finite`, both finite
share-value rows, the five finite liveness rows, `JointCheckpoint2F` field by field,
`checkJoint2F_sound`, the definition `PairUsdcAllowQuiet`, and the stray-slot
control `u0F_stray_accepted`; the remaining Section 5.10 rows and controls are not pinned. Of Section 5.11, every
theorem in a Theorem column is pinned by exact statement, the five end-to-end instances and
the exact-gas rows among them, with `Jaune.Msg.withGas` and `RliWordsPin` pinned by unfolding;
the other definitions written there (`U3Ledger`, `U3Step`, `ClosedExchangeOutcome`, the closed
exact costs) and the Curve 3pool names of Section 9 are not pinned. The trimmed public headlines (`fee_le_spec`, `fee_eq_spec_iff`, `fee_guarantee_refuted`,
`system_call_succeeds`, `history_system_call_succeeds`, `history_submission_live`,
`history_submission_queued`, `history_system_call_succeeds_mainnet`, `history_submission_live_mainnet`,
`history_submission_queued_mainnet`, `deploy`,
`deploy_mainnet`, `history_payments`, `history_payments_mainnet`, `history_delivery`,
`history_delivery_mainnet`, `history_fifo_mainnet`, `historyFifo_of_checkpoint_needs_systemEmpty`, `c3crv_conserved`,
`c3crv_policy`, `beacon_deposits`, `lido_registry_consistent`, `lido_remove_repairs`,
`lido_deployment_finite_init`, `lido_live_registryOn`, `vminus_attack`,
`vplus_exit`, `weth9_deployment`, `weth9_backed`, `weth9_net_flow`, `pair_ledger`,
`pair_minimum_liquidity`, `live_pair_reserves_backed`, `live_pair_share_value`,
`live_pair_share_value_feeOff`, `pair_oracle`, `pair_share_value` and `pair_share_value_feeOff`,
with `balanceAnswersBacked_iff` and `feeAnswered_of_factoryEntered`) are pinned by exact statement, every observer they are stated through
by unfolding, and `LidoSlotsApart` field by field. The remaining rows, among them the WETH9 liveness rows of Section 5.1, are held here
by name and line only.

Each of those pins is a definitional-equality check against the current
definitions it mentions, so on its own it does not see a definition below the
pinned layer change. `scripts/check-claim-hash.sh` covers that layer: in one run
it hashes with SHA-256 the full definitional closure of every pinned statement
and every unfolding pin in `scripts/ClaimCheck.lean` (a definition by its type
and body, a theorem by its statement only so that changing the proof of any theorem it reaches changes nothing, an inductive type by its whole mutual
block with the names of its types and constructors and its constructor types;
binder names and annotations are ignored, and a referenced constant contributes
its own hash, not its name) and compares each pin's root hash with the manifest
committed in `scripts/claim-pin-hash/`; a mismatch names the definitions whose
content changed and the pins they reach. Each pin is keyed by the constant its
proof applies or the definition it unfolds, with the statement's hash added when
several pins share that name, so adding a pin adds one entry, while re-proving a
pin through a different constant shows as one pin removed and one added. It
reads the built Lean artifacts and refuses to run unless they, Jaune's
included, are certified current for the sources.
Jaune's definitions are hashed in full like Blanc's, because its EVM semantics
are part of what every claim means: a change of the Jaune revision moves exactly
the pins whose meaning changed, and the check names the Jaune definitions that
moved; a Jaune revision change that moves no pin passes with a note only, and
the recorded Jaune revision is then refreshed in a reviewed update. The hash stops at the other pinned dependencies: a constant from the Lean
toolchain, Batteries or Mathlib counts as its name together with the toolchain
in `lean-toolchain` or the package revision in `lake-manifest.json`, so its body
is fixed by that pin rather than by the hash. A hash records change, not
weakening: a mismatch says that the meaning of those claims moved and must be
reviewed, not that they became weaker.

Every run also executes in-memory falsifiers, each of which must be rejected: a
misspelled declaration, a stale line, a wrong file, an orphan line reference, a
missing cited file, a stale bare name, a wrong leaf count, an extra, a missing and a wrong stricter
axiom claim, a wrong codehash, size, creation transaction and system-contract
digest, a wrong Jaune revision and Lido timestamp, process vocabulary, a
deleted headline and a dropped disclosure, and for the Uniswap rows a wrong codehash,
code-read block, init-code hash and embedded runtime window, a wrong factory code-read
block and embedded creation-code window, and a deleted headline and a dropped
disclosure of Sections 5.8 and 5.9; and for the USDC rows a wrong code-read block,
library link site and implementation slot, and a deleted headline and a dropped
disclosure of Section 5.10.

What the check does **not** do: it does not elaborate Lean or re-derive any
axiom set (its authority over axioms is `scripts/AxiomCheck.lean`, verified by
`scripts/check.sh`); it does not judge whether a row's prose is a fair summary
of its theorem, whether a premise list is complete, or whether the bytes in
`scripts/lift/inputs/` are the bytes on the chain; and it does not re-run the
conformance figures of Section 3.
