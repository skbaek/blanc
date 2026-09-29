# Deployed-bytecode claim map

What Blanc proves about bytecode that is already on Ethereum mainnet: WETH9, the
Beacon deposit contract, the Curve 3Crv LP token, Lido's CircuitBreaker, and the
Vyper nonreentrancy pair (the fixed pool implementation "V+" and the vulnerable
one "V−"). Every headline below names the theorem that carries it, the
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
  a closed existence statement. *Deploy* is a modeled deployment (Section 7).
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

Compilers, from the certificate provenance: 3Crv Vyper 0.2.4; the
CircuitBreaker solc 0.8.34; V− Vyper 0.2.15; V+ Vyper 0.3.7.

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
| Jaune revision `b019bbf` | That its EVM and transaction definitions match Ethereum | Not a theorem. Conformance, as reported by that Jaune revision's own README and not re-run here: **5,006/5,006** supported fixture files and **34,205/34,205** cases of the execution-specs mainnet corpus (`tests@v20.0.2`), Prague through BPO2 including configured fork transitions |
| Lift certificates | Nothing | The Python producers are untrusted. Each certificate is accepted only by its Lean `cert_check`, a kernel decision, against the literal bytes |
| Runtime identity | That the lifted bytes are the mainnet bytes | Recorded in each certificate's `provenance`: `eth_getCode` agreement across independent public providers (two for WETH9, five for 3Crv); the creation inputs of WETH9, the Beacon deposit contract and 3Crv fetched from two providers and equal byte for byte; the Lido creation input equal to the frozen reference template plus its constructor arguments; the two pool implementations taken from Sourcify v2 records. The codehashes in Section 2 are recomputed from the lifted files by the checker |
| Fork scope | — | `CoveredFork` is Prague, Osaka, BPO1, BPO2. Amsterdam is not covered |
| Chain arithmetic | Model bound | Configured traces carry total ETH plus withdrawals below 2^256 (`SumNof` at the checkpoint) |
| Signature recovery | Premise, not proved | `recoverSender … = .ok E` is the only cryptographic premise of the transaction-level theorems (secp256k1 is not kernel-reducible) |

## 4. Premise classes

Every premise below is one of these classes. The table also says whether the
class is acceptable in a headline and whether a deployment theorem establishes
the INIT premise.

| Class | Meaning | Acceptable in a headline? | INIT established by a deployment theorem? |
|---|---|---|---|
| CODE | Installed code and fork identity | Yes | — |
| INIT | Stated once, at the checkpoint | Yes, if shown inhabited, ideally by deployment | **WETH9** footprint `FootInv ∅`: yes, no hash premise [`Blanc.Lift.Weth9.Creation.weth9_deploy_init_covered` (`Blanc/Lift/Weth9/Creation/DeployInit.lean:22`)]. **Beacon** `SolInv []`: yes, no hash premise [`Blanc.Lift.BeaconDeposit.Creation.beacon_deploy_covered` (`Blanc/Lift/BeaconDeposit/Creation/Deploy.lean:144`)]. **Curve** `VyInv … ∅`: yes, no hash premise [`Blanc.Lift.Curve3Crv.Creation.curve_deploy_covered` (`Blanc/Lift/Curve3Crv/Creation/Deploy.lean:286`)]. **Lido** `RegistryZeroRaw` and `StateInv`: only under two hash premises `ForeignApart 0 0` and `ForeignApart 0 1` [`Blanc.Lift.LidoCircuitBreakerDeployed.Creation.lido_deploy_init_covered` (`Blanc/Lift/LidoCircuitBreakerDeployed/Creation/Deploy.lean:203`)]. **V±**: synthetic prestates, none |
| ENTRY | Required at every entered frame | Only if environmental, never invariant-shaped | — |
| HASH-T | Collision-freedom for the hashes and keys actually computed or touched in the trace | Yes: implied by collision resistance | — |
| HASH-U | Separation quantified over all 2^160 addresses or indices | Needs justification. Not implied by collision resistance; under a random-function model of Keccak it fails with probability about q·2^-94 per frame (q = written slots), a **heuristic bound, not a theorem**. It can never be inhabited by a proof | — |
| ENV | Gas, warmth, depth, static flag, callee behaviour, trace-local exclusions (no authorization or CREATE at given addresses) | Yes when stated; better derived | — |
| ARITH | Numeric bounds | Yes | — |

The per-frame calldata bound (below 2^256) is not a premise of any history
theorem: it holds for every raw frame of every configured history on all
covered forks [`Blanc.ExecutionTrace.ConfiguredHistoryTrace.calldata_bound` (`Blanc/ExecutionTraceCalldata.lean:768`);
`Blanc.ExecutionTrace.ConfiguredHistoryTrace.frameAdmitted_calldata` (`Blanc/ExecutionTraceCalldata.lean:785`)], because
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
| Frame | `balanceOf` and `decimals` execute and return the stored word | `Blanc.Lift.Weth9.weth9_balanceOf_gas_exact` (`Blanc/Lift/Weth9/Live.lean:746`), `Blanc.Lift.Weth9.weth9_decimals_gas_exact` (`Blanc/Lift/Weth9/Live.lean:767`) | 2,534 / 534 (`balanceOf` cold / warm), 2,444 / 444 (`decimals`) [`Blanc.Lift.Weth9.balanceOfGas9_eq` (`Blanc/Lift/Weth9/Live.lean:557`)] | ENV: gas |
| Frame | `approve` writes `allowance[caller][guy] := wad` and returns `true` | `Blanc.Lift.Weth9.weth9_approve_live` (`Blanc/Lift/Weth9/LiveWriters.lean:50`) | `approveGas = 2320 + sstoreCost` [`Blanc.Lift.Weth9.approveGas` (`Blanc/Lift/Weth9/LiveApprove.lean:209`)]; worked case: cold, never-written slot, nonzero `wad` costs **24,420** [`Blanc.Lift.Weth9.approveGas_cold_set` (`Blanc/Lift/Weth9/LiveWriters.lean:645`)]; needs `380 ≤ G` | none |
| Frame | `deposit()` and the payable fallback | `Blanc.Lift.Weth9.weth9_deposit_live` (`Blanc/Lift/Weth9/LiveWriters.lean:84`), `Blanc.Lift.Weth9.weth9_fallback_short_live` (`Blanc/Lift/Weth9/LiveWriters.lean:109`), `Blanc.Lift.Weth9.weth9_fallback_live` (`Blanc/Lift/Weth9/LiveWriters.lean:132`) | `depositGas = 1874 + depositLoad + depositStore` [`Blanc.Lift.Weth9.depositGas` (`Blanc/Lift/Weth9/LiveDeposit.lean:195`)]; the fallback adds 1631 / 1896; needs `844 ≤ G` | none |
| Frame | `transfer` | `Blanc.Lift.Weth9.weth9_transfer_live` (`Blanc/Lift/Weth9/LiveWriters.lean:257`) | `transferGas = xferGasSelf + 470` [`Blanc.Lift.Weth9.transferGas` (`Blanc/Lift/Weth9/LiveTransfer.lean:645`)]; needs `353 ≤ G` | ENV: `wad ≤ balanceOf[caller]` |
| Frame | `transferFrom`, all three allowance cases | `Blanc.Lift.Weth9.weth9_transferFrom_live` (`Blanc/Lift/Weth9/LiveWriters.lean:428`) | `transferFromGas = xferGas{Self,Max,Allow} + 340` [`Blanc.Lift.Weth9.transferFromGas` (`Blanc/Lift/Weth9/LiveWriters.lean:419`)]; needs `377 ≤ G` | a storage effect exists (`xferStorStep`) |
| Frame | `withdraw(wad)` to an EOA, every `wad` (0 included) | `Blanc.Lift.Weth9.weth9_withdraw_any_live` (`Blanc/Lift/Weth9/LiveWriters.lean:529`); nonzero `wad`: `Blanc.Lift.Weth9.weth9_withdraw_live` (`Blanc/Lift/Weth9/LiveWriters.lean:329`) | `withdrawGas = 2040 + sload + sload + sstore + callNet` [`Blanc.Lift.Weth9.withdrawGas` (`Blanc/Lift/Weth9/LiveWithdraw.lean:441`)]; `wad = 0`: `Blanc.Lift.Weth9.withdrawZeroGas` (`Blanc/Lift/Weth9/LiveWithdraw.lean:552`); needs `811 ≤ G` | ENV: the caller has no code, is not a precompile, depth ≠ 0, and the contract holds the ETH |
| Frame | `withdraw` to a **contract** | `Blanc.Lift.Weth9.weth9_withdraw_send_live` (`Blanc/Lift/Weth9/LiveWriters.lean:586`) | `Blanc.Lift.Weth9.withdrawSendPre` (`Blanc/Lift/Weth9/LiveWriters.lean:577`); ends with `r − 1489` | **`SendOk` callee premise** [`Blanc.Lift.Weth9.SendOk` (`Blanc/Lift/Weth9/LiveWriters.lean:564`)]: the CALL succeeds, leaves at least 1489 gas, and changes no contract storage |
| Model | Any writer the model accepts at the extended footprint realises the model's next ledger, gas-exact | `Blanc.Lift.Weth9.weth9_approve_model_live` (`Blanc/Lift/Weth9/LiveModel.lean:52`), `Blanc.Lift.Weth9.weth9_deposit_model_live` (`Blanc/Lift/Weth9/LiveModel.lean:72`), `Blanc.Lift.Weth9.weth9_transfer_model_live` (`Blanc/Lift/Weth9/LiveModel.lean:90`), `Blanc.Lift.Weth9.weth9_transferFrom_model_live` (`Blanc/Lift/Weth9/LiveModel.lean:117`), `Blanc.Lift.Weth9.weth9_withdraw_model_live` (`Blanc/Lift/Weth9/LiveModel.lean:144`) | as the frame rows | INIT `FootInv K`; HASH-T `KeysFresh K (call keys)`; model acceptance |
| Reachable state | After any configured history, a tracked holder can `withdraw(wad)` to an EOA, `deposit()`, or `transfer` | `Blanc.Lift.Weth9.weth9_history_withdraw_live` (`Blanc/Lift/Weth9/LiveHistory.lean:75`), `Blanc.Lift.Weth9.weth9_history_deposit_live` (`Blanc/Lift/Weth9/LiveHistory.lean:130`), `Blanc.Lift.Weth9.weth9_history_transfer_live` (`Blanc/Lift/Weth9/LiveHistory.lean:158`) | `withdrawAnyGas` / `depositGas` / `transferGas` | the history premises (CODE, ARITH, INIT, HASH-T); a fresh frame at `pre.state = future.state`; the holder in the tracked universe. **No history-level `approve` or `transferFrom` liveness** |
| Transaction | A type-2 `withdraw(wad)` transaction is admitted by `processTransaction`, debits the holder's slot, moves `wad` ETH, and uses exact gas | `Blanc.Lift.Weth9.weth9_tx_withdraw` (`Blanc/Lift/Weth9/LiveTx.lean:359`); at any configured history's future state `Blanc.Lift.Weth9.weth9_history_tx_withdraw` (`Blanc/Lift/Weth9/LiveTx.lean:621`) | intrinsic `21000 + 4·calldataTokens` [`Blanc.Lift.Weth9.withdrawIntrinsicGas` (`Blanc/Lift/Weth9/LiveTx.lean:45`)]; frame **13,940** (`wad ≠ 0`) or **4,440** (`wad = 0`) [`Blanc.Lift.Weth9.withdrawFrameGas` (`Blanc/Lift/Weth9/LiveTx.lean:52`)]; refund 4,800 iff a nonzero `wad` empties the balance [`Blanc.Lift.Weth9.withdrawRefund` (`Blanc/Lift/Weth9/LiveTx.lean:55`)]; `gasUsed = intrinsic + frame − refund` [`Blanc.Lift.Weth9.withdrawGasUsed` (`Blanc/Lift/Weth9/LiveTx.lean:59`)] | the signature-recovery premise; a sender EOA with nonce and funds; `tx.gas ≥ intrinsic + frame + 811` and `≤ 2^24` (EIP-7825); block room; coinbase ∉ {E, ca}; `FootInv` at the block state; the holder tracked and `wad ≤` its balance |

**Deployment / INIT**

| Claim | Theorem | Kind | Premises |
|---|---|---|---|
| The recorded creation input (nonce 446 from the recorded deployer) succeeds, installs the certified runtime, and leaves exactly the constructor's `name`/`symbol`/`decimals` storage; the address is the CREATE address | `Blanc.Lift.Weth9.Creation.weth9_deploy` (`Blanc/Lift/Weth9/Creation/Deploy.lean:145`), `Blanc.Lift.Weth9.Creation.weth9_deploy_covered` (`Blanc/Lift/Weth9/Creation/Deploy.lean:156`); general `Blanc.Lift.Weth9.Creation.weth9_create` (`Blanc/Lift/Weth9/Creation/Deploy.lean:55`); the storage `Blanc.Lift.Weth9.Creation.deployedStor` (`Blanc/Lift/Weth9/Creation/Deploy.lean:35`) has every nonzero word in {0, 1, 2} [`Blanc.Lift.Weth9.Creation.deployedStor_metadata` (`Blanc/Lift/Weth9/Creation/Deploy.lean:38`)] | deploy | none (closed) |
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

**A second statement with a universal hash premise.** `Blanc.Lift.Weth9.weth9_history_preserves_solvent` (`Blanc/Lift/Weth9/Solvency.lean:92`)
[frame rung `Blanc.Lift.Weth9.weth9_preserves_solvent` (`Blanc/Lift/Weth9/Solvency.lean:78`)] proves a booked-ledger invariant under
the per-frame **HASH-U** premise `AllowAdmitted` [`Blanc.Lift.Weth9.AllowAdmitted` (`Blanc/Lift/Weth9/Premise.lean:24`)] and INIT
`StateInv`. `StateInv` is satisfiable (`weth9_init_stateInv`) but **no
deployment theorem establishes it**; the deployment result is the footprint
INIT above. Cite this form only with the HASH-U disclosure, and use
`weth9_history_footprint` for holder-level backing with trace-local premises.

### 5.2 Beacon deposit: exact committed deposit history

**Safety, refinement and history**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| After any configured history, storage is the accumulator of the initial history followed by exactly the deposits whose frames were committed (rollback-filtered by settlement), in order. **The mainnet-satisfiable form** | `Blanc.Lift.BeaconDeposit.configuredHistory_solInv_sys` (`Blanc/Lift/BeaconDeposit/BeaconEnv.lean:222`); base form `Blanc.Lift.BeaconDeposit.configuredHistory_solInv` (`Blanc/Lift/BeaconDeposit/CommittedHistory.lean:73`) | History / safety, exact extraction | CODE `installed`; INIT `SolInv … initialHistory`; ENV (trace-local, finite): `SystemCodeInstalled checkpoint` (canonical bytes at the four system addresses), `NoAuthorityAt` and no CREATE frame at those four addresses and at `0x02`, `getCode 2 = empty` at the checkpoint. **No hash premise.** The calldata bound, system exclusion [`Blanc.Lift.BeaconDeposit.system_of_installed` (`Blanc/Lift/BeaconDeposit/BeaconEnv.lean:204`), `Blanc.ExecutionTrace.ConfiguredHistoryTrace.systemFrames_of_installed` (`Blanc/ExecutionTraceSystemCode.lean:269`)], `0x02` warmth and no-delegation are derived | the `0x02` warmth is derived from EIP-2929 pre-warming, preserved across rollback |
| The count slot is the number of deposits; the root is the reference mixed Merkle root of that exact list | `Blanc.Lift.BeaconDeposit.configuredHistory_count_sys` (`Blanc/Lift/BeaconDeposit/BeaconEnv.lean:243`), `Blanc.Lift.BeaconDeposit.configuredHistory_root_sys` (`Blanc/Lift/BeaconDeposit/BeaconEnv.lean:263`); reference correctness `Blanc.BeaconDeposit.root_correct` (`Blanc/BeaconDepositCorrectness.lean:284`) | History / safety | as above | |
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
| **History:** the final storage abstracts the model state reached by `Curve3Crv.step` over **exactly the settlement-committed writer invocations** at the contract, in trace order, and that model state is conserving (`totalSupply = Σ balances`) | `Blanc.Lift.Curve3Crv.c3crv_history_committed_derived` (`Blanc/Lift/Curve3Crv/CommittedHistory.lean:210`); base form `Blanc.Lift.Curve3Crv.c3crv_history_committed` (`Blanc/Lift/Curve3Crv/CommittedHistory.lean:171`) (takes the calldata bound as a hypothesis) | History / safety, exact extraction | CODE; INIT `VyInv … initialKeys`; **HASH-T** `FreshKeys initialKeys (historyTouchedKeys ca trace)` (rolled-back frames included); the calldata bound is derived | No static filter: `Blanc.Lift.Curve3Crv.c3crv_writer_nonstatic` (`Blanc/Lift/Curve3Crv/Safe.lean:195`) proves a writer cannot succeed in a static frame |
| A successful frame from a fresh entry is exactly the model step: writers (events, storage abstraction, owner answer for `set_name`, empty STOP output), **and views (storage and logs unchanged, return bytes equal the model output)** | `Blanc.Lift.Curve3Crv.c3crv_frame_refines` (`Blanc/Lift/Curve3Crv/Safe.lean:242`); raw form `Blanc.Lift.Curve3Crv.c3crv_frame_refines_raw` (`Blanc/Lift/Curve3Crv/Safe.lean:83`) (output stated relative to the entry output) | Frame / safety | CODE; covered fork; calldata bound below 2^256 (a frame-level hypothesis); **fresh entry as explicit premises** `pre.stack = []`, `pre.memory = Mem.empty`, `pre.output = []`; INIT-shaped `VyInv pre`; HASH-T `FreshKeys` (call keys); a successful `Exec 0 sevm pre (.ok post)` | Every successful selector is covered (misses and short calldata have no successful run). The fresh-entry facts are hypotheses here, not derived from a `Frame.enter` equation |
| Token-model properties: `step` preserves conservation; the initial state is conserving; supply and minter change only by the minter; `transferFrom` spends allowance (maximum allowance exempt); zero-first approve; authorized allowance and balance changes | `Blanc.Curve3Crv.step_conserved` (`Blanc/Curve3Crv/Properties.lean:160`), `Blanc.Curve3Crv.init_conserved` (`Blanc/Curve3Crv/Properties.lean:165`), `Blanc.Curve3Crv.supply_change_by_minter` (`Blanc/Curve3Crv/Properties.lean:182`), `Blanc.Curve3Crv.minter_change_by_minter` (`Blanc/Curve3Crv/Properties.lean:201`), `Blanc.Curve3Crv.transferFrom_spends_allowance` (`Blanc/Curve3Crv/Properties.lean:223`), `Blanc.Curve3Crv.approve_zero_first` (`Blanc/Curve3Crv/Properties.lean:258`), `Blanc.Curve3Crv.allowance_change_authorized` (`Blanc/Curve3Crv/Properties.lean:267`), `Blanc.Curve3Crv.balance_debit_authorized` (`Blanc/Curve3Crv/Properties.lean:304`) | Model / safety | the model only | bridged to the bytes by the two rows above |

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

**Deployment / INIT.** `Blanc.Lift.Curve3Crv.Creation.curve_deploy_covered` (`Blanc/Lift/Curve3Crv/Creation/Deploy.lean:286`), for every covered fork
`f`: a nonce-42 CREATE from the recorded deployer installs the runtime and
leaves `deployedStor deployer` with `VyInv … (curveDeployedState deployer) (fun _
=> False)`. The recorded deployment therefore satisfies the history theorem's
checkpoint predicate (name, symbol, decimals 18, supply 0, minter = deployer)
with no hash premise; the constructor's write of 0 at `keccak(3‖caller)` is
discharged by kernel evaluation. General form `Blanc.Lift.Curve3Crv.Creation.curve_create` (`Blanc/Lift/Curve3Crv/Creation/Deploy.lean:198`) (storage
`deployedStor`). `Blanc.Lift.Curve3Crv.curve_init_vyInv` (`Blanc/Lift/Curve3Crv/Init.lean:37`) is a satisfiability instance.

**Fork coverage.** History and liveness on covered forks;
`curve_deploy_covered` quantifies over covered forks.

**Non-claims.** Log and return bytes at the *history* level (only at frame
level); replay equal to the *raw* trace's writer sequence (rolled-back frames
are, by design, not in it); a closed cost formula; `set_name` without the
owner-call premise.

### 5.4 Lido CircuitBreaker: registry integrity (not "targets are paused")

The Lido headlines keep **universal (HASH-U) premises** with the explicit
random-oracle bound of Section 4 (about q·2^-94 per frame; a heuristic bound,
no theorem derives it). `lidoEntry lidoA` [`Blanc.Lift.LidoCircuitBreakerDeployed.lidoEntry` (`Blanc/Lift/LidoCircuitBreakerDeployed/Frame.lean:63`)] states, at
every entered frame, `LocalApart` (`ForeignApart (2^160)` for the three
fixed and written slots) and `EntryAt lidoA` (for every witness of the
frame-entry storage, the registry keys the calldata addresses touch are
faithful at bound 2^160).

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| After any configured history there is a registry witness of the future storage: assignment and index agree with membership, counts equal assignments, pauser 0 has count 0, and live counts sum to the length word | `Blanc.Lift.LidoCircuitBreakerDeployed.lido_history_l1_l3` (`Blanc/Lift/LidoCircuitBreakerDeployed/History.lean:56`) | History / safety | CODE; INIT `RegistryZeroRaw`; ENTRY plus **HASH-U** `FrameAdmitted ca (lidoEntry lidoA)` | selector-insensitive |
| `registerPauser(t, 0)` from a real pc-0 entry removes `t` with the correct swap-and-pop repair (`L2Post`) | `Blanc.Lift.LidoCircuitBreakerDeployed.l2_registerPauser_zero` (`Blanc/Lift/LidoCircuitBreakerDeployed/L2Frame.lean:249`) | Frame / safety | CODE; fresh entry; **HASH-U** `EntryAt lidoA`; INIT-shaped `RegistryWitness` of the pre-storage | |
| **The pre-storage witness is derived:** every settlement-committed non-static `registerPauser(t, 0)` frame (including one re-entered from inside `pause`'s CALL) has a witness of its entry storage and `L2Post` | `Blanc.Lift.LidoCircuitBreakerDeployed.lido_history_l2_committed` (`Blanc/Lift/LidoCircuitBreakerDeployed/L2History.lean:97`) | History / safety | CODE via `StateInv` INIT; `FrameAdmitted ca (lidoEntry lidoA)` (HASH-U); per-frame call shape only. Uses the generic `Blanc.ExecutionTrace.ConfiguredHistoryTrace.entryGood_settled` (`Blanc/ExecutionEntryAccounting.lean:488`), `Blanc.Lift.LidoCircuitBreakerDeployed.lido_spawnEntry` (`Blanc/Lift/LidoCircuitBreakerDeployed/Reentry.lean:440`) and `Blanc.Lift.reach_of_parentPrefix` (`Blanc/Lift/Cursor.lean:705`) | static committed frames and frames under a rolled-back ancestor are **not claimed** |

**Liveness.** None. There is **no Lido liveness claim of any level**.

**Deployment / INIT.** `Blanc.Lift.LidoCircuitBreakerDeployed.Creation.lido_deploy_covered` (`Blanc/Lift/LidoCircuitBreakerDeployed/Creation/Deploy.lean:190`), for every covered fork
`f`: a nonce-0 CREATE from the recorded deployer with 1,000,000 gas installs
the certified runtime and leaves storage exactly `deployedStor`
(`pauseDuration = 1814400`, `heartbeatInterval = 31536000`).
`Blanc.Lift.LidoCircuitBreakerDeployed.Creation.lido_deploy_init_covered` (`Blanc/Lift/LidoCircuitBreakerDeployed/Creation/Deploy.lean:203`) adds `RegistryZeroRaw` and
`lidoSpec.StateInv` **under `ForeignApart 0 0` and `ForeignApart 0 1`** (two
bounded hash premises: the constructor's slots 0 and 1 are off the registry's
raw slots). General forms `Blanc.Lift.LidoCircuitBreakerDeployed.Creation.lido_create` (`Blanc/Lift/LidoCircuitBreakerDeployed/Creation/Deploy.lean:75`),
`Blanc.Lift.LidoCircuitBreakerDeployed.Creation.lido_create_registryZeroRaw` (`Blanc/Lift/LidoCircuitBreakerDeployed/Creation/Deploy.lean:115`), `Blanc.Lift.LidoCircuitBreakerDeployed.Creation.lido_create_stateInv` (`Blanc/Lift/LidoCircuitBreakerDeployed/Creation/Deploy.lean:129`).
Satisfiability: `Blanc.Lift.LidoCircuitBreakerDeployed.registryZeroRaw_empty` (`Blanc/Lift/LidoCircuitBreakerDeployed/Init.lean:35`), `Blanc.Lift.LidoCircuitBreakerDeployed.lido_init_stateInv` (`Blanc/Lift/LidoCircuitBreakerDeployed/Init.lean:46`). The gas of the
modeled constructor matches the mainnet receipt exactly; that comparison was
made outside Lean and is not a Lean fact.

**Fork coverage.** History on covered forks; `lido_deploy_covered` quantifies
over covered forks. See Section 7: this deployment is post-Prague.

**Non-claims.** Authorization completeness; setter effects and events;
pause-call liveness; that a target is actually paused; static committed
frames; frames under rolled-back ancestors; any liveness.

### 5.5 Vyper V+: guarded-body reentrancy exclusion

The fixed implementation 0x847e, called directly or through the ETH/stETH
proxy.

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| In any execution (any outcome, `Exec 0 …`), while an owner frame is inside one of the mutating guarded bodies and has not released, no descendant enters any guarded body for that owner | generic `Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_exclusion` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exclusion.lean:128`); instances `Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_exclusion_impl` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exclusion.lean:142`), `Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_exclusion_stethPool` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exclusion.lean:161`) | Message (all outcomes) / temporal exclusion | CODE (implementation or proxy bytes, `hP`, `hI`); ENV well-formed root `hroot`; **HASH-T** `HashAvoidIn` (executed Keccak digests differ from lock slot 0) | |
| The same for a transaction's retained top-level execution, with `hroot` **derived** (`prepareMessage` builds the root from the debited world) | `Blanc.ExecutionTrace.TransactionTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:248`); message carriers `Blanc.ExecutionTrace.ProcessMessageTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:70`), `Blanc.ExecutionTrace.ProcessCreateMessageTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:116`), `Blanc.ExecutionTrace.MessageCallTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:180`) | Transaction / temporal exclusion | `hfork`, `hP`, `hI` on the opening state; `tx.auths = []` (EIP-7702 excluded); `HashAvoidIn` of the retained execution | |
| The same for every raw frame root of a configured history; pc 0 and the covered fork are derived | `Blanc.ExecutionTrace.ConfiguredHistoryTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:281`) [roots by `Blanc.ExecutionTrace.MessageCallTrace.rootEntry` (`Blanc/ExecutionTraceEntry.lean:58`)] | History / temporal exclusion | per retained execution `R`: `hP`, `hI`, `hroot`, `HashAvoidIn` (not derivable from the trace) | statement form `VplusExcludes` [`Blanc.Lift.VyperNonreentrantDeployed.Fixed.VplusExcludes` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:44`); `Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_excludes` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:50`)] |
| **Nonvacuity (proxy-free):** an actual Jaune execution of the deployed 0x847e runtime in which a mutating guarded body (`remove_liquidity`, body start 0x1bae) is active and spawns a STATICCALL (pc 0x337a) to a coin, whose read-only reentry into the guarded view `get_virtual_price()` **reverts at the lock check** and never reaches a guarded body. It carries the full antecedent of `vplus_exclusion_impl` and its conclusion | `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness.vplus_witness_covered` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness/Top.lean:254`) (quantified over `g` with `CoveredFork g`, Prague included); every derivation of the entered machine, under any covered fork: `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness.vplus_run_at` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness/Top.lean:87`) | Message / closed witness | none (closed) | Kernel-checked; every walk boundary matches an EELS Prague trace (the printer is untrusted). No KECCAK executes, so `HashAvoidIn` holds by "no hash executed" |
| **Nonvacuity (proxy instance, mutating reentry):** an execution entered through the 45-byte forwarder 0x21e2… (DELEGATECALL to 0x847e). `remove_liquidity` holds the lock and CALLs a synthetic receiver with 100 wei; the receiver calls back through the forwarder with `add_liquidity`'s selector (mutating, guarded); the comparator frame reverts at the lock check (pc 0x53 → 0x477e, no guarded body start); the receiver stops; the outer call **succeeds** and the pool balance goes from 1000 to 900 wei. This is a witness of `vplus_exclusion_stethPool` (the covered form carries that theorem's premises and antecedent, and the reentry conclusion `¬ lockL.Enters`) | `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.vplus_witness2_covered` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness2/Top.lean:229`) (every covered fork); every derivation: `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.vplus_run2_at` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness2/Top.lean:109`) | Message / closed witness | none (closed) | `HashAvoidIn` by digests: the one KECCAK256 leaves a digest different from slot 0 (control `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.hashControl_bites` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness2/Run.lean:308`); engine control `Blanc.Lift.NodeWalk.hashPol_bites` (`Blanc/Lift/NodeWalk.lean:1070`)) |

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
| **Transaction level, all covered forks:** Jaune's `processTransaction` accepts a fixed signed type-2 transaction (zero fee and value, 16,043,200 gas, below 2^24, an access list of 19 addresses), and the returned world has `totalSupply = 1800 < 1906` in the pool | `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.vminus_txC_process` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/TxC/Envelope.lean:137`); message part `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.vminus_txC_message` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/TxC/Closed.lean:49`) (gas 15,822,837 left, refund 42,600, `accountsToDelete` empty) | Transaction / closed witness | `hrecover : recoverSender … = .ok E` (**true by an interpreter `#guard` in `TxTopC.lean`, not a kernel fact**); block room `hroom` | every other admission check is kernel-evaluated on the concrete transaction and block |

**Fork coverage.** `vminus_witness_covered`, `vminus_txC_message` and
`vminus_txC_process` quantify `g` with `CoveredFork g`. A Prague-only message
form, `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.vminus_tx_message` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Tx/Closed.lean:26`), carries 30,021,064 gas, which is above
the EIP-7825 cap from Osaka on and so is not a valid transaction there; cite
the `TxC` forms.

**Non-claims.** A reachable or historical prestate; a real historical
attack; a signature-generic transaction (the signature, transaction hash,
index 0 and coinbase are fixed); the attacker model is synthetic (Section 7).

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
| Lido | ✓ | ✓ (L1/L3) | ✗ [h] | ✗ HASH-U | ~ [i] | ✗ | ✗ | ✓ |
| V+ | ✓ | ~ [j] | ~ [j] | ✓ HASH-T (per execution) | — | ✓ nonvacuity (witnesses) | ~ [k] | ✓ |
| V− | ✓ | — | — | — | — synthetic | — | ✓ [l] | ✓ |

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
is existential. [h] `lidoEntry lidoA` at every frame (ENTRY and HASH-U). [i]
`lido_deploy_init_covered` needs two hash premises. [j] Message, transaction
and history corollaries exist; per retained execution the world premises `hP`
and `hI`, the root code identity and `HashAvoidIn` are not derivable from the
trace (the transaction form derives `hroot`). [k] A transaction form exists
for the exclusion; no admitted transaction *witness* reaches an active guarded
body. [l] A fixed signed transaction; the recovery premise is true by `#guard`.

## 7. Disclosures and limits

1. **Lido keeps universal (HASH-U) premises.** The per-frame premise
   quantifies over registry-observable keys below 2^160. Under a random-oracle
   model of Keccak the failure probability is about q·2^-94 per frame (four
   registry key families × 2^160 / 2^256 per written slot). This is a
   **heuristic bound**, not a theorem, and it cannot be inhabited by a proof.
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
4. **The Beacon `_env` forms are vacuous on mainnet.**
   `Blanc.Lift.BeaconDeposit.configuredHistory_solInv_env` (`Blanc/Lift/BeaconDeposit/BeaconEnv.lean:96`), `Blanc.Lift.BeaconDeposit.configuredHistory_count_env` (`Blanc/Lift/BeaconDeposit/BeaconEnv.lean:115`) and
   `Blanc.Lift.BeaconDeposit.configuredHistory_root_env` (`Blanc/Lift/BeaconDeposit/BeaconEnv.lean:136`) require an offset-blind `SpawnFree`
   exclusion, which is false of the canonical EIP-7002 code
   [`Blanc.withdrawalRequestCode_not_spawnFree` (`Blanc/SystemContracts.lean:135`)]. The `_sys` headlines of Section 5.2 are
   the mainnet-satisfiable statements; do not cite the `_env` forms.
5. **Witness-engine guard.** The V− interpreter engine refuses synchronous
   MODEXP (0x05) and P256VERIFY (0x100) child frames
   [`Blanc.Lift.Witness.frameEntryForkFree` (`Blanc/Lift/WitnessArms.lean:931`), used by `Blanc.Lift.Witness.callStep` (`Blanc/Lift/WitnessArms.lean:941`)]. The `wrun … = .cont`
   run conjuncts of `vminus_witness` therefore also mean that the run enters no
   MODEXP or P-256 frame; that is what makes the runs fork-uniform. The V+ walks
   expose spawns as explicit nodes and execute no CLZ and no MODEXP or
   P256VERIFY.
6. **Every closed witness and deployment theorem cited is stated for all of
   Prague, Osaka, BPO1 and BPO2:** `vplus_witness_covered`,
   `vplus_witness2_covered`, `vminus_witness_covered`,
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
   60,000,000. A signature-generic form is not built. `hrecover` is true by
   interpreter evaluation (`#guard`), not by a kernel theorem.
   `weth9_tx_withdraw` instead assumes coinbase ∉ {E, ca} and the signature
   premise.
9. **Callee premises.** `SendOk` (WETH9 `withdraw` to a contract) and
   `OwnerCallOk` (Curve `set_name`) assume the callee's behaviour; EOA withdraws
   and every other function need no callee premise.
10. **Static frames are not claimed** where the committed list filters them:
    WETH9 (the filter is a statement-level choice) and Lido (a `nonstatic`
    per-frame premise; a static `registerPauser(t,0)` of an absent `t` can
    succeed since it writes nothing). Beacon and Curve prove that
    statically-committed writers produce nothing.
11. **Rolled-back frames are not claimed.** History invariants hold of the
    final storage regardless; per-frame committed claims
    (`lido_history_l2_committed`, the committed invocation lists) say nothing of
    frames rolled back or under a rolled-back ancestor.
12. **Curve cost is exact but existential** (`∃ c`), with no closed formula.
    **WETH9 frame keys are a uniform five-key set** (Section 5.1).
13. **Liveness frames are fresh frames** (empty stack and memory) at a state,
    not transactions, except `weth9_tx_withdraw`.
14. **`SystemCodeInstalled`.** The canonical system bytes come from a Jaune
    test fixture (Section 2); their mainnet identity per covered fork is not
    checked here.
15. **Runtime identity is recorded, not re-fetched.** The provider agreement
    behind each lifted input is evidence in the certificate `provenance`; it is
    not reproduced by any gate.

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
the sites. At this commit it is 1381 leaf results (1236 public, 145 private).
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
| `NoAuthorityAt` | `Blanc.ExecutionTrace.ConfiguredHistoryTrace.NoAuthorityAt` (`Blanc/ExecutionTraceCodeAt.lean:460`) | no authorization of any transaction of a configured history recovers to the given address |
| `SpawnFree` | `Blanc.SpawnFree` (`Blanc/ExecutionTraceSystem.lean:24`) | the code has no instruction that could spawn a child frame, read at every offset (false of the canonical EIP-7002 code) |
| `FootInv` | `Blanc.Lift.Weth9.FootInv` (`Blanc/Lift/Weth9/Footprint.lean:79`) | WETH9's footprint invariant: support, injective and apart tracked slots, and the tracked ledger backed by the contract's ether |
| `KeysFresh` | `Blanc.Lift.Weth9.KeysFresh` (`Blanc/Lift/Weth9/Footprint.lean:59`) | each touched key is tracked or on an unused slot, and keys sharing a slot are one key (HASH-T) |
| `KeyInj` | `Blanc.Lift.Weth9.KeyInj` (`Blanc/Lift/Weth9/Footprint.lean:53`) | tracked slots are pairwise distinct |
| `frameKeys` | `Blanc.Lift.Weth9.frameKeys` (`Blanc/Lift/Weth9/FootFrame.lean:57`) | the decode-free five-key over-approximation of the keys a frame's call may touch |
| `Weth9.historyTouchedKeys` | `Blanc.Lift.Weth9.historyTouchedKeys` (`Blanc/Lift/Weth9/FootHistory.lean:61`) | the keys a WETH9 history touches, rolled-back frames included |
| `SendOk` | `Blanc.Lift.Weth9.SendOk` (`Blanc/Lift/Weth9/LiveWriters.lean:564`) | the callee premise of WETH9 `withdraw` to a contract: the CALL to the caller succeeds, leaves at least 1489 gas, and changes no storage of the contract |
| `AllowAdmitted` | `Blanc.Lift.Weth9.AllowAdmitted` (`Blanc/Lift/Weth9/Premise.lean:24`) | both allowance images written by the allowance entry points are off the balance image for this frame (a local HASH-U premise) |
| `SolInv` | `Blanc.Lift.BeaconDeposit.SolInv` (`Blanc/Lift/BeaconDeposit/Layout.lean:42`) | Beacon's storage abstraction: an intact zero-hash table and the model invariant for a deposit history |
| `beaconEntry` | `Blanc.Lift.BeaconDeposit.beaconEntry` (`Blanc/Lift/BeaconDeposit/Ladder.lean:130`) | Beacon's carried entry condition: calldata length below 2^256, the SHA-256 precompile account (`0x02`) not a delegation, and warm |
| `DepositDecodable` | `Blanc.Lift.BeaconDeposit.DepositDecodable` (`Blanc/Lift/BeaconDeposit/DepositArgs.lean:55`) | the deployed decoder accepts the deposit calldata |
| `ShaReady` | `Blanc.Lift.ShaReady` (`Blanc/Lift/ExactWalkCutOps.lean:77`) | the SHA-256 precompile premises of a frame's world: address 2 undelegated and warm, a precompile of the fork |
| `VyInv` | `Blanc.Lift.Curve3Crv.VyInv` (`Blanc/Lift/Curve3Crv/Layout.lean:95`) | Curve 3Crv's storage abstraction over the live keys |
| `FreshKeys` | `Blanc.Lift.Curve3Crv.FreshKeys` (`Blanc/Lift/Curve3Crv/Layout.lean:115`) | the frame-local premise for the keys a Curve frame touches: each is fresh and their slots are pairwise distinct (HASH-T) |
| `Curve3Crv.historyTouchedKeys` | `Blanc.Lift.Curve3Crv.historyTouchedKeys` (`Blanc/Lift/Curve3Crv/CarriedHistory.lean:27`) | the keys a Curve history touches |
| `OwnerCallOk` | `Blanc.Lift.Curve3Crv.OwnerCallOk` (`Blanc/Lift/Curve3Crv/LiveBodies.lean:1570`) | the callee premise of Curve `set_name`: its static `owner()` call answers whenever it is given enough gas, and leaves at least `R` gas |
| `RegistryZeroRaw` | `Blanc.Lift.LidoCircuitBreakerDeployed.RegistryZeroRaw` (`Blanc/Lift/LidoCircuitBreakerDeployed/L2.lean:46`) | the raw-slot form of an empty registry: the array length word is zero and every canonical address has zero assignment, index and count words |
| `StateInv` | `Blanc.ContractSpecSem.StateInv` (`Blanc/LadderSem.lean:86`) | the state invariant of a semantic contract spec (`lidoSpec.StateInv`) |
| `ForeignApart` | `Blanc.Lift.LidoCircuitBreakerDeployed.ForeignApart` (`Blanc/Lift/LidoCircuitBreakerDeployed/Foreign.lean:21`) | a raw slot is disjoint from the storage slots of every logical key the registry observes up to a bound (HASH-U) |
| `LocalApart` | `Blanc.Lift.LidoCircuitBreakerDeployed.LocalApart` (`Blanc/Lift/LidoCircuitBreakerDeployed/Frame.lean:52`) | the three non-registry slots a frame can write are off the registry layout |
| `EntryAt` | `Blanc.Lift.LidoCircuitBreakerDeployed.EntryAt` (`Blanc/Lift/LidoCircuitBreakerDeployed/Frame.lean:58`) | the registry-writer premise holds of every registry witness of the frame's entry storage (HASH-U at bound 2^160 for `lidoA`) |
| `L2Post` | `Blanc.Lift.LidoCircuitBreakerDeployed.L2Post` (`Blanc/Lift/LidoCircuitBreakerDeployed/L2Frame.lean:32`) | the removal effects of the L2 frame theorem, relative to the pre-call witness |
| `RegistryWitness` | `Blanc.LidoCircuitBreaker.RegistryWitness` (`Blanc/LidoCircuitBreakerRegistryModel.lean:254`) | a witness that a storage is a well-formed registry |
| `HashAvoidIn` | `Blanc.LockExclusion.LockSpec.HashAvoidIn` (`Blanc/LockExclusion.lean:316`) | every frame of the pool running the lock code avoids the lock slot with its executed hashes (HASH-T) |
| `VplusExcludes` | `Blanc.Lift.VyperNonreentrantDeployed.Fixed.VplusExcludes` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:44`) | the statement form of the V+ exclusion |

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
  digests equal the bytes written in `Blanc/SystemContracts.lean`;
- the page keeps its section structure, its required headline theorems and its
  load-bearing disclosures, and carries no process vocabulary.

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
