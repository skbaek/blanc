# Deployed-bytecode claim map

What Blanc proves about bytecode that is already on Ethereum mainnet: the Curve
3Crv LP token, the Curve 3pool StableSwap pool (with 3Crv as its LP token, Section
5.11), the Vyper nonreentrancy pair (the fixed pool implementation "V+" and the
vulnerable one "V−"), the EIP-7002 withdrawal-request predeploy, and USDC (its
proxy, implementation and signature library, Section 5.10).
Every headline below names the theorem that carries it, the premises it needs,
and what it does not say. This page is about the exogenous bytes themselves.

Historical exhibits outside paper v2, including WETH9, Beacon deposit, Lido, Uniswap and Blanc-native programmes, are preserved in the [archived corpus](https://github.com/skbaek/blanc/blob/corpus-v1-20261105/docs/DEPLOYED_BYTECODE_CLAIM_MAP.md). The section and disclosure labels below retain their historical numbering. The archive is outside the live corpus and is not promised to build against later revisions.

**A Blanc theorem is a statement about Jaune's modeled semantics, not a
deployment audit** ([`SECURITY.md`](../SECURITY.md)). Nothing here says that a
contract is safe, that its Solidity or Vyper source is correct, or that a
proved property is the property a user cares about. Each statement is read in
Lean, in the file the map cites, before it is relied on.

## 1. How to read this map

- **Names and lines.** Every declaration is written fully qualified, followed
  by the file and line where it is declared, for example
  `Blanc.Lift.Curve3Crv.c3crv_frame_refines` (`Blanc/Lift/Curve3Crv/Safe.lean:291`). Names and lines are checked against the
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
`scripts/lift/certificates.json`. Each Vyper proxy row is the 45-byte EIP-1167
forwarder to the implementation above it.

| Contract | Address | Runtime bytes | keccak256 codehash | Creation transaction | Block |
|---|---|---:|---|---|---:|
| Curve 3Crv LP token | 0x6c3F90f043a72FA612cbac8115EE7e52BDe6E490 | 2,276 | 0xb731b7a9a74c6c60d715f0c791d663f1530743a48337e7fab9cf3481afdd9feb | 0xa7d90e460bed56181e41b74d143ec98fe097c8391700e4e0788f5282053694f8 (deployer 0xbabe61887f1de2713c6f97e567623453d3c79f67, nonce 42) | 10,809,467 |
| Curve 3pool StableSwap | 0xbEbc44782C7dB0a1A60Cb6fe97d0b483032FF1C7 | 21,199 | 0x954a1e212c557c85043985931498ffa3e2fcbe7dfe9cd61513f36eb47d6f4dfc | 0x20793bbf260912aae189d5d261ff003c9b9166da8191d8f9d63ff1c7722f3ac6 (deployer 0xbabe61887f1de2713c6f97e567623453d3c79f67, nonce 43) | 10,809,473 |
| Vyper pool implementation, fixed (V+) | 0x847ee1227a9900b73aeeb3a47fac92c52fd54ed9 | 18,320 | 0x59469db6b75b045025abb5386ae6b7ef7e1698d13ee93f3d4ed32d5f72506e0e | 0xfaad66f8fa2b4883b9e5c91b69e31ac8c2cdbc6d383b8776d0eee94d3ee0a251 | 17,110,099 |
| ETH/stETH pool proxy to the V+ implementation | 0x21e27a5e5513d6e65c4f830167390997aa84843a | 45 | 0x9e28a09452d2354fc4e15e3244dde27cbc4d52f12a10b91f2ca755b672bfa9be | not recorded | not recorded |
| Vyper pool implementation, vulnerable (V−) | 0x6326debbaa15bcfe603d831e7d75f4fc10d9b43e | 17,535 | 0xba0284a6a8a86734c1c777e3c6b5b56f2c8ba95dc0f7eba481c6d09da7885ebc | 0xd27491757b3a4bc9287ed44ce5c43de9f32131264548ce139f0a702c3d5f389e | 12,904,329 |
| Pool proxy to the V− implementation | 0x9848482da3ee3076165ce6497eda906e66bb85c5 | 45 | 0xbed04db3507e08e5220f6eadf98d5df05bdbc74df129c73fcbab7c441e86b124 | not recorded | not recorded |
| USDC FiatTokenProxy | 0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48 | 2,186 | 0xd80d4b7c890cb9d6a4893e6b52bc34b56b25335cb13716e0d1d31383e6b41505 | not recorded (runtime read at a finalized block, below) | not recorded |
| USDC FiatTokenV2_2 implementation | 0x43506849D7C04F9138D1A2050bbF3A0c054402dd | 23,464 | 0xcdfb7d322961af3acae7a8f7ee8b69c205b36f576cc5b077f170c7eb8ecbe3ea | not recorded (runtime read at a finalized block, below) | not recorded |
| USDC SignatureChecker library | 0x800C32EaA2a6c93cF4CB51794450ED77fBfbB172 | 1,741 | 0x76cfc2ce63b1f05cb58ae553090665c2aabf2e13cf8a0e6da755c096fc5295dd | not recorded (runtime read at a finalized block, below) | not recorded |

Compilers, from the certificate provenance: 3Crv Vyper 0.2.4; the Curve 3pool Vyper
0.2.4; V− Vyper 0.2.15; V+ Vyper 0.3.7; USDC proxy solc 0.4.24;
implementation solc 0.6.12; library solc 0.6.12.

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

**Canonical system contracts.** The shared configured-execution machinery names
the four canonical system contracts at their protocol addresses. Their bytes are the definitions in `Blanc.beaconRootsCode` (`Blanc/SystemContracts.lean:35`) and its neighbours; the SHA-256
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
| Runtime identity | That the lifted bytes are the mainnet bytes | Recorded in each certificate's `provenance`: `eth_getCode` agreement across separately operated public providers (five for 3Crv, five for the Curve 3pool, six for USDC, each at one finalized block); the creation inputs of 3Crv and the Curve 3pool fetched from two providers and equal byte for byte; the two pool implementations taken from Sourcify v2 records. The codehashes in Section 2 are recomputed from the lifted files by the checker |
| Fork scope | — | `CoveredFork` is Prague, Osaka, BPO1, BPO2. Amsterdam is not covered. The 3Crv deployment-rooted rows use `HistFork` (Byzantium through BPO2), which includes the Muir Glacier rules the deployment block ran under; the Jaune conformance figures above begin at Prague and do not cover them |
| Chain arithmetic | Model bound | Configured traces carry total ETH plus withdrawals below 2^256 (`SumNof` at the checkpoint) |
| Signature recovery | Premise of the signature-generic transaction theorems | `recoverSender … = .ok E` is a premise of every theorem that quantifies over all signed transactions, since there is then no single signature to evaluate. For a concrete transaction the kernel evaluates recovery: `Blanc.Lift.WithdrawalRequest.FloodTx.txB_recoveredSender` (`Blanc/Lift/WithdrawalRequest/FloodTxRecover.lean:149`) and, for V−, `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.txC_recoveredSender` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/TxCRecover.lean:99`) |

## 4. Premise classes

Every theorem hypothesis below has one of these classes; these are not Lean
logical axioms, and a clean axiom audit does not discharge them. The table says
whether a class is acceptable and whether deployment establishes INIT.

| Class | Meaning | Acceptable in a headline? | INIT established by a deployment theorem? |
|---|---|---|---|
| CODE | Installed code and fork identity | Yes | — |
| INIT | Stated once, at the checkpoint | Yes, if shown inhabited, ideally by deployment | **Curve 3pool** `Checkpoint`, the pool's storage predicate at the constructor's model state: yes, no hash premise [`Blanc.Lift.Curve3Pool.Creation.pool_deploy_covered` (`Blanc/Lift/Curve3Pool/Creation/Deploy.lean:292`)]; the joint 3pool-and-3Crv `JointCheckpoint` is not established by deployment, and is checked by a kernel-evaluated checker on synthetic worlds only (Section 5.11) |
| ENTRY | Required at every entered frame | Only if environmental, never invariant-shaped | — |
| HASH-T | Exact separation of the hashes and keys actually computed or touched in the trace, including avoidance of fixed slots where stated | Yes when stated; narrower and amenable to finite checking with a concrete initial footprint. Computational collision resistance does not entail this exact fact; fixed-slot avoidance also concerns target/preimage behavior. No cryptographic reduction is proved. | — |
| HASH-B | Binding instances: `Separated f [traceValue, recordedValue]` (`Blanc.Separated` (`Blanc/Separated.lean:23`)) for a hash or trie function `f`, a value the trace itself computes and a recorded value checked in the kernel against a public commitment | Yes when stated. Finite (two values), trace-local, satisfiable (`Blanc.Separated.pair_self` (`Blanc/Separated.lean:31`)) and not refutable; in context it is equivalent to the equation it delivers, `f traceValue = f recordedValue → traceValue = recordedValue` (`Blanc.Separated.pair_iff` (`Blanc/Separated.lean:42`)). Its gain is epistemic: it fails only under a collision of `f` on those two values, not under bad supplied data. The `trie` instances are structural: no Merkle–Patricia reduction of `trie` to Keccak is proved. HASH-T's key separation is the same shape (`Blanc.SlotFootprint.freshKeys_iff` (`Blanc/Separated.lean:61`)). No universal injectivity premise is used | — |
| HASH-U | Exact separation quantified over all 2^160 addresses or indices | Needs justification; not established here. The finite domain does not make proof impossible. Under a random-function model of Keccak the estimated failure probability is about q·2^-94 per frame (q = written slots): **heuristic bound estimate only, with no reduction or bound proved** | — |
| ENV | Gas, warmth, depth, static flag, callee behaviour, trace-local exclusions (no authorization or CREATE at given addresses) | Yes when stated; better derived | — |
| ARITH | Numeric bounds | Yes | — |

The per-frame calldata bound (below 2^256) is not a premise of any history
theorem: it holds for every raw frame of every configured history on all
covered forks [`Blanc.ExecutionTrace.ConfiguredHistoryTrace.calldata_bound` (`Blanc/ExecutionTraceCalldata.lean:927`);
`Blanc.ExecutionTrace.ConfiguredHistoryTrace.frameAdmitted_calldata` (`Blanc/ExecutionTraceCalldata.lean:944`)], because
`tx.gas ≤ blockGasLimit < 2^63`. Frame-level (non-history) theorems still take
it as a hypothesis about their own `sevm`.

Shared system-code support remains live: `Blanc.ExecutionTrace.ConfiguredHistoryTrace.systemFrames_of_installed` (`Blanc/ExecutionTraceSystemCode.lean:274`).
An offset-blind `SpawnFree` exclusion cannot be assumed for the canonical EIP-7002
bytes: `Blanc.withdrawalRequestCode_not_spawnFree` (`Blanc/SystemContracts.lean:135`).
The shared finite separation checks retain their characterizations:
`Blanc.SlotFootprint.checkFaithfulOn_eq_true` (`Blanc/SlotFootprint.lean:138`) and
`Blanc.SlotFootprint.checkApartOn_eq_true` (`Blanc/SlotFootprint.lean:150`).

## 5. Per contract

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

### 5.5 Vyper V+: guarded-body reentrancy exclusion

The fixed implementation 0x847e, called directly or through the ETH/stETH
proxy.

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| In any execution (any outcome, `Exec 0 …`), while an owner frame is inside one of the mutating guarded bodies and has not released, no descendant enters any guarded body for that owner | generic `Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_exclusion` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exclusion.lean:128`); instances `Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_exclusion_impl` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exclusion.lean:142`), `Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_exclusion_stethPool` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exclusion.lean:161`) | Message (all outcomes) / temporal exclusion | CODE (implementation or proxy bytes, `hP`, `hI`); ENV well-formed root `hroot`; **HASH-T** `HashAvoidIn` (executed Keccak digests differ from lock slot 0) || In a pc-0 frame running the 0x847e code (covered fork, `HashAvoid 0`), every node executes only `CALL` or `STATICCALL` among external calls and never `DELEGATECALL`, `CALLCODE`, `CREATE`, `CREATE2` or `SELFDESTRUCT` [`Blanc.Lift.VyperNonreentrantDeployed.Fixed.lock_no_forbidden` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/LockDominance.lean:44`)] |
| The same for a transaction's retained top-level execution, with `hroot` **derived** (`prepareMessage` builds the root from the debited world) | `Blanc.ExecutionTrace.TransactionTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:251`); message carriers `Blanc.ExecutionTrace.ProcessMessageTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:70`), `Blanc.ExecutionTrace.ProcessCreateMessageTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:116`), `Blanc.ExecutionTrace.MessageCallTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:180`) | Transaction / temporal exclusion | `hfork`, `hP`, `hI` on the opening state; `tx.auths = []` (EIP-7702 excluded); `HashAvoidIn` of the retained execution | |
| The same for every raw frame root of a configured history; pc 0 and the covered fork are derived | `Blanc.ExecutionTrace.ConfiguredHistoryTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:283`) [roots by `Blanc.ExecutionTrace.MessageCallTrace.rootEntry` (`Blanc/ExecutionTraceEntry.lean:58`)] | History / temporal exclusion | per retained execution `R`: `hP`, `hI`, `hroot`, `HashAvoidIn` (not derivable from the trace) | statement form `VplusExcludes` [`Blanc.Lift.VyperNonreentrantDeployed.Fixed.VplusExcludes` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:44`); `Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_excludes` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:50`)] |
| **Nonvacuity (proxy-free):** an actual Jaune execution of the deployed 0x847e runtime in which a mutating guarded body (`remove_liquidity`, body start 0x1bae) is active and spawns a STATICCALL (pc 0x337a) to a coin, whose read-only reentry into the guarded view `get_virtual_price()` **reverts at the lock check** and never reaches a guarded body. It carries the full antecedent of `vplus_exclusion_impl` and its conclusion | `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness.vplus_witness_covered` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness/Top.lean:251`) (quantified over `g` with `CoveredFork g`, Prague included); every derivation of the entered machine, under any covered fork: `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness.vplus_run_at` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness/Top.lean:82`) | Message / closed witness | none (closed) | Kernel-checked; every walk boundary matches an EELS Prague trace (the printer is untrusted). No KECCAK executes, so `HashAvoidIn` holds by "no hash executed" |
| **Nonvacuity (proxy instance, mutating reentry):** an execution entered through the 45-byte forwarder 0x21e2… (DELEGATECALL to 0x847e). `remove_liquidity` holds the lock and CALLs a synthetic receiver with 100 wei; the receiver calls back through the forwarder with `add_liquidity`'s selector (mutating, guarded); the comparator frame reverts at the lock check (pc 0x53 → 0x477e, no guarded body start); the receiver stops; the outer call **succeeds** and the pool balance goes from 1000 to 900 wei. This is a witness of `vplus_exclusion_stethPool` (the covered form carries that theorem's premises and antecedent, and the reentry conclusion `¬ lockL.Enters`) | `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.vplus_witness2_covered` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness2/Top.lean:227`) (every covered fork); every derivation: `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.vplus_run2_at` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness2/Top.lean:104`) | Message / closed witness | none (closed) | `HashAvoidIn` by digests: the one KECCAK256 leaves a digest different from slot 0 (control `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.hashControl_bites` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness2/Run.lean:413`); engine control `Blanc.Lift.NodeWalk.hashPol_bites` (`Blanc/Lift/NodeWalk.lean:1086`)) |
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
| Fee, against the EIP directly: the fee the bytecode computes from the excess is at most the EIP's fake_exponential(1, excess, 17), with equality exactly on `NatFeeDomain`, with no model state. Intermediate: Fee: the executed word fee is at most fake_exponential(1, excess, 17), with equality exactly on `NatFeeDomain`; every committed submission paid its executed word fee | `Blanc.Lift.WithdrawalRequest.fee_le_spec` (`Blanc/Lift/WithdrawalRequest/HeadlineFee.lean:41`), `Blanc.Lift.WithdrawalRequest.fee_eq_spec_iff` (`Blanc/Lift/WithdrawalRequest/HeadlineFee.lean:48`), over `Blanc.Lift.WithdrawalRequest.WordFee` (`Blanc/Lift/WithdrawalRequest/HeadlineFee.lean:20`) and `Blanc.Lift.WithdrawalRequest.SpecFee` (`Blanc/Lift/WithdrawalRequest/HeadlineFee.lean:17`); via `Blanc.Lift.WithdrawalRequest.word_fee_le_nat` (`Blanc/Lift/WithdrawalRequest/ExactFeeDomain.lean:23`), `Blanc.Lift.WithdrawalRequest.word_fee_eq_iff_natFeeDomain` (`Blanc/Lift/WithdrawalRequest/ExactFeeDomain.lean:12`); the intermediate's history clause (every committed submission paid its executed word fee) is `Blanc.Lift.WithdrawalRequest.history_word_fee_budget` (`Blanc/Lift/WithdrawalRequest/WordBudget.lean:78`) | Frame and history | the executed word fee loop only (intermediate: CODE) | see §7 item 16 |
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

### 5.10 USDC: proxy forwarding, signature laws and history replay

USDC is three certified runtimes (Section 2): the FiatTokenProxy, which forwards
every non-admin call by `DELEGATECALL` to the implementation its implementation
slot names; the FiatTokenV2_2 implementation, which runs over the proxy's storage;
and the SignatureChecker library the implementation reaches by `DELEGATECALL`
for authorizer-signed messages (`permit`, transferWithAuthorization,
receiveWithAuthorization, cancelAuthorization). The history rows take `UsdcHist`;
the governance, tracked-key and excluded-position premises remain stated below.
These rows do not establish the planned Curve composition with actual DAI, USDC
and USDT bytes.

**Shared token vocabulary**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| The laws a token's pure book (an abstract ledger, its step on one entered frame's message, the decoded operation, balances, allowances, and a well-formedness predicate `Good`) must satisfy: a step from a good ledger lowers a holder's balance only if its caller is the holder or a spender to which the holder had granted a positive allowance; only the owner raises its own allowances; a holder's own `balanceOf`, `transfer` or credit-only call debits it at most by the declared amount and raises none of its allowances; a step decoded as `transfer` to someone else debits the caller exactly; a good ledger's balances are below 2^256 | `Blanc.Lift.Token.BookLaws` (`Blanc/Lift/Token/Core.lean:62`) over `Blanc.Lift.Token.Book` (`Blanc/Lift/Token/Core.lean:48`) | Interface / definition | — | No storage layout appears |
| The token core, what a token's **address** answers along a configured history: under a trace-local premise `Hist` the instance chooses, at the entry of every settled frame the booked ledger is the book run over exactly the non-static entry frames at the token before it, and at the end over all of them; the ledger is good at the checkpoint and at every settled frame's entry; a settled `balanceOf(h)` entry frame, static or not, answers the booked balance for every holder the instance vouches for; a settled `transfer` entry frame answers empty output or a nonzero first word; a settled frame at the token that is not an entry frame (`IsEntry`: storage owner and code address both the token) is a child only of settled frames at the token | `Blanc.Lift.Token.Core` (`Blanc/Lift/Token/Core.lean:98`); entry frames `Blanc.Lift.Token.IsEntry` (`Blanc/Lift/Token/Core.lean:85`) | History / interface | the instance's own `Hist` | Further facts are separate structures over the book or the core, added without editing it: `Blanc.Lift.Token.Erc20Abi` (`Blanc/Lift/Token/Abi.lean:17`) (the standard `transfer` and `balanceOf` selectors decode as those operations for every calldata of at least 68 and 36 bytes respectively and below 2^256), `SelfCaller` and `TransferLive` below. The non-entry clause admits a proxy's delegated implementation frames |
| Facet: every entry-frame child of a settled non-static frame at the token has the token itself as caller | `Blanc.Lift.Token.SelfCaller` (`Blanc/Lift/Token/SelfCaller.lean:18`) | History / interface | the core's `Hist` | No forwarded caller reaches a booked entry |
| Facet: at any world the instance accepts, a fresh entry frame (value 0, non-static, covered fork, the token's code) decoding a `transfer` of at most the caller's booked balance runs to success at an exact instance-given cost, answers the word 1, leaves an accepted world, and, when the recipient is not the caller, debits the caller exactly | `Blanc.Lift.Token.TransferLive` (`Blanc/Lift/Token/Core.lean:145`) | Frame / interface | the instance's world and frame conditions; ENV: gas at least the cost plus the 2,300-gas stipend | |

**The proxy and the `DELEGATECALL` lift**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| A certificate node claiming `CALL` where the code holds `DELEGATECALL` (`0xf4`) is rejected by the checker | `Blanc.Lift.checkNode_call_at_delegatecall` (`Blanc/Lift/DelegatecallControl.lean:16`) | Control / certificate | the byte at the node is `0xf4` | `DELEGATECALL` keeps the caller and the storage owner, so a certificate cannot pass it off as `CALL` |
| The proxy certificate with `CALL` claimed at the proxy's `DELEGATECALL` site (byte 1,680) fails `Cert.check` | `Blanc.Lift.Usdc.Proxy.proxy_cert_call_mutant_rejected` (`Blanc/Lift/Usdc/Proxy/Control.lean:24`) | Control / certificate | none | Kernel evaluation on the lifted proxy bytes |
| A frame running the proxy code from pc 0 whose caller is not the admin word: every external instruction it executes is `DELEGATECALL`; every child runs at the proxy with the implementation address `I` the slot names as code address, the frame's caller, value, calldata and static flag, and `I`'s code; on success the frame's output and world are a child's | `Blanc.Lift.Usdc.proxy_forwards` (`Blanc/Lift/Usdc/ProxyOk.lean:275`) | Frame / safety | CODE; covered fork; the implementation slot holds `I`; caller not the admin word; `I` carries no EIP-7702 designator and is no precompile; calldata below 2^256 bytes | `CALLDATASIZE` pushes the length modulo 2^256, hence the calldata bound |
| With the slot naming `J ≠ I`, no child runs with code address `I` | `Blanc.Lift.Usdc.proxy_forwards_control` (`Blanc/Lift/Usdc/ProxyForward.lean:123`) | Control / frame | as `proxy_forwards`, for `J` | The slot premise is load-bearing |
| A frame running the proxy code whose caller is the admin word: every external instruction is `CALL`, every child runs at the proxy with the proxy as caller, and a selector other than upgradeTo, upgradeToAndCall and changeAdmin spawns no child and leaves the proxy's storage unchanged | `Blanc.Lift.Usdc.proxy_admin_rule` (`Blanc/Lift/Usdc/ProxyForward.lean:224`) | Frame / safety | CODE; covered fork; caller is the admin word | The admin branch never reaches the implementation |
| The implementation's children are either library frames (at the same storage owner, with the frame's caller, value and static flag, running the library code) or frames whose caller is the storage owner, with value 0 | `Blanc.Lift.Usdc.impl_children` (`Blanc/Lift/Usdc/ImplSpawns.lean:298`) | Frame / safety | CODE; covered fork; the library code installed at its address | The second kind is rescueERC20's token call |
| The library's children are static, with the storage owner as caller, and a successful library frame leaves its storage owner's storage unchanged | `Blanc.Lift.Usdc.lib_children` (`Blanc/Lift/Usdc/LibSpawns.lean:30`) | Frame / safety | CODE; covered fork | The ERC-1271 isValidSignature call and the `ecrecover` call |

**USDC's model, its history and the signature laws**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| USDC's pure book (its ledger model read through the implementation's own decoder) satisfies the signature variant of the token laws, `BookLawsS`: as `BookLaws` (the shared vocabulary above), except that a step may also lower a holder's balance, or raise its allowances, by a message the holder signed | `Blanc.Lift.Usdc.usdcBook_lawsS` (`Blanc/Lift/Usdc/Book.lean:140`), the book `Blanc.Lift.Usdc.usdcBookS` (`Blanc/Lift/Usdc/Book.lean:48`) | Model / safety | none | The signer is the third authorizer |
| Under `NeverSigner T S tr p` (no settled non-static entry of `T` along the history has `p` as signer), `BookLawsS` gives the holder-indexed laws the composition consumes, for `p` | `Blanc.Lift.Token.BookLawsS.holderLaws` (`Blanc/Lift/Token/Signed.lean:59`) | Model / bridge | `NeverSigner` | The never-signer premise is required for this holder-indexed bridge |
| Under `UsdcHist` (USDC's three runtimes and its implementation slot installed at the checkpoint, the governance premise, the footprint invariant at the checkpoint, HASH-T over the keys the history touches), at every settled position not `UsdcShadowed` the book run over the earlier entry frames at the proxy is the footprint ledger at that frame's entry | `Blanc.Lift.Usdc.usdc_history_replayAt` (`Blanc/Lift/Usdc/HistoryReplay.lean:320`) | History / replay | `UsdcHist` | Positional replay |
| Under `UsdcHist`, the implementation slot and the admin word are unchanged at every settled frame's entry and at the end | `Blanc.Lift.Usdc.usdc_history_slots` (`Blanc/Lift/Usdc/HistorySlots.lean:168`) | History / safety | `UsdcHist` | This is what the governance premise buys |
| Under `UsdcHist`, at the history's end USDC's three runtimes and its implementation slot are installed, the footprint invariant holds over the history's key universe, and the admin word is unchanged | `Blanc.Lift.Usdc.usdc_history_end` (`Blanc/Lift/Usdc/HistoryEndFoot.lean:21`) | History / invariant | `UsdcHist` | The footprint invariant is retained |
| USDC at any proxy address is an instance of the writer-shadowed token core `CoreW`: its `Hist` is `UsdcHist`, its booked ledger is the footprint ledger over the history's key universe, its shadowed positions are `UsdcShadowed`, its answerable holders are the history's tracked balance rows | `Blanc.Composition.UsdcToken.usdcCore` (`Blanc/Composition/UsdcToken.lean:225`) | History / instance | `UsdcHist` | `CoreW` is `Core` with shadowed positions excluded |
| USDC discharges the self-caller facet: no foreign caller is forwarded into USDC's own entry | `Blanc.Composition.UsdcToken.usdcSelfCaller` (`Blanc/Composition/UsdcToken.lean:243`) | History / instance | as `usdcCore` | From the three spawn theorems above |
| USDC's book decodes `transfer` and `balanceOf` calldata as the ERC-20 ABI does | `Blanc.Composition.UsdcToken.usdcBook_erc20Abi` (`Blanc/Composition/UsdcToken.lean:268`) | Model / ABI | none | |
| USDC's budgeted transfer facet: at a world holding USDC's runtimes with the footprint core over `U`, a fresh entry frame at the proxy whose keys lie in `U`, whose caller is not the admin word and whose `transfer` meets USDC's state conditions, runs to success through the proxy and the implementation at an exact cost, given a gas budget that covers the proxy's 63/64 cut | `Blanc.Composition.UsdcToken.usdcTransferLive` (`Blanc/Composition/UsdcTokenLive.lean:159`) | Frame / instance | INIT footprint core; HASH-T frame keys in `U`; ENV gas and state conditions | From the proxy-to-implementation exact walk of `transfer` |

**A retained trace-local premise**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| The trace-local quiet premise | `Blanc.Composition.UniswapV2PairUsdcWeth9.PairUsdcAllowQuiet` (`Blanc/Lift/Usdc/AllowanceQuiet.lean:14`) | History / premise | the history's touched keys | Every touched allowance row of the supplied holder reads zero at the checkpoint |

Its declaration is owned by USDC despite its historical namespace. It states a
premise, not a surviving Pair composition theorem.

**Statement controls**

| What it shows | Control | Altitude |
|---|---|---|
| The laws reject USDC models that debit without authority: a mutant whose `transferFrom` skips the allowance, and an implementation whose `transfer` debits a third party | `Blanc.Lift.Usdc.control_usdc_mutant_not_lawsS` (`Blanc/Lift/Usdc/ModelControls.lean:175`), `Blanc.Lift.Usdc.control_usdc_thirdParty_not_lawsS` (`Blanc/Lift/Usdc/ModelControls.lean:194`) | definitional |
| `NeverSigner` is needed: a toy book satisfies `BookLawsS`, and when the holder may sign, any other caller's message lowers the holder's balance with no allowance | `Blanc.Lift.Token.control_signer_breaks_holder` (`Blanc/Lift/Token/SignedControl.lean:28`) | definitional |

USDC's own finite checkpoint checker rejects a synthetic storage with a stray
word: `Blanc.Lift.Usdc.checkUsdc_rejects_stray` (`Blanc/Lift/Usdc/FiniteFootprint.lean:87`).
Its soundness theorem, `Blanc.Lift.Usdc.checkUsdc_sound` (`Blanc/Lift/Usdc/FiniteFootprint.lean:47`),
takes `checkUsdc P rows w = true` and yields the installed-code facts and footprint
invariant over the row keys. These are conditional checkpoint facts, not an
attestation of live state.

**Non-claims.** The closed single-block USDC instance; live USDC or pool-state
assurance; USDC versions other than FiatTokenV2_2 at the stated implementation
address; results at positions excluded by `UsdcShadowed`. No actual-coin Curve
flagship or full deployed DAI/USDC/USDT composition is established here.

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

## 6. Summary matrix

Columns: **M1** pc-0 entry; **M2** history with the invariant carried from one
checkpoint; **M3** per-frame premises environmental only; **M4** hash
premises trace-local or none; **M5** INIT established by deployment; **M6**
liveness at a reachable state; **M7** transaction-level liveness; **M8** all
covered forks. ✓ met, ✗ not met, ~ partial (see the footnote), — not
applicable.

| | M1 | M2 | M3 | M4 | M5 | M6 | M7 | M8 |
|---|---|---|---|---|---|---|---|---|
| Curve | ✓ | ✓ | ✓ | ✓ HASH-T | ✓ [b] [ak] | ~ [g] | ✗ | ✓ |
| V+ | ✓ | ~ [j] | ~ [j] | ✓ HASH-T (per execution) | ✓ [q] (message level; the exclusion itself takes no INIT premise) | ✓ nonvacuity (witnesses), and a reachable witness [q] | ~ [k] | ✓ |
| V− | ✓ | — | — | — | ✓ [q] (message level) | ✓ [q] violation at a reachable state | ✓ [l] | ✓ |
| EIP-7002 | ✓ | ✓ [m] | ✓ | ✓ none | ✓ [b] | ✓ | ✗ | ✓ |
| Curve 3pool | ✓ | ✓ | ✓ [ae] | ✓ HASH-T [af] | ✓ [ag] | ✓ [ah] | ~ [ai] | ✓ [aj] |

[b] it is not chained into a configured history,
and that the factory issues the `initialize` call is a premise (the run is
then constructed), since the factory's bytecode is not lifted.

[g] `set_name` needs the `OwnerCallOk` callee premise; the cost
is existential.

[j] Message, transaction
and history corollaries exist; per retained execution the world premises `hP`
and `hI`, the root code identity and `HashAvoidIn` are not derivable from the
trace (the transaction form derives `hroot`).

[k] A transaction form exists
for the exclusion; no admitted transaction *witness* reaches an active guarded
body.

[l] A fixed signed transaction; its signature recovery is a kernel theorem (`txC_recoveredSender`).

[m] Up to 2^254 committed submission-payment occurrences since the checkpoint (user-approved scope); the fee is
the bytecode's executed word fee, and the EIP's unbounded-integer fee guarantee is refuted (§7 item 16).

[q] Deployment, initialization and liquidity are executed messages
from a creator-only world, not admitted transactions (§7 item 3 applies); the
V− transaction row (M7) starts from a different, synthetic prestate. For both V+ and V−, M5 records the executed setup of the reachable witness; the older witnesses keep their synthetic prestates.

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

[ak] For 3Crv the deployment is also chained: the recorded creation transaction in its retained Muir Glacier block is the root of a configured history (Section 5.3), so [b]'s "not chained" describes the modeled `_covered` message only.

## 7. Disclosures and limits

2. **Curve cost.** No closed Curve cost formula is claimed for 3Crv: its cost is exact but existential.

3. **Deployments are modeled, not historical inclusion.** Curve 3Crv (10,809,467) predates Prague too; its `curve_deploy_covered` is a modeled deployment like the others, and Section 5.3 in addition states its recorded creation transaction inside its retained Muir Glacier block, which is still not an inclusion proof (no header, block hash or state-root binding). The modeled deployment theorems execute
   the recorded creation input as a CREATE message under current rules
   (`deployMsg`, an empty world, 1M–3M gas). The deployment results are messages,
   not validated transactions. The reachable V± chains (Sections 5.5 and 5.6)
   are modeled messages too but have a different shape: they start from a world
   holding a funded, code-free creator, place each implementation at its
   registered address by a supplied CREATE target, and continue through
   initialization, funding and the experiment, each message from the previous
   settled world (item 25).

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
   `vminus_reachable_capstone`, `vminus_reach_violation`,
   `curve_deploy_covered`.

7. **Synthetic prestates and fixtures (V±).** For the closed witnesses: pool
   storage (lock slots, balances, totalSupply), ETH balances, and the reader,
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

9. **Callee premises.** `OwnerCallOk` (Curve `set_name`) assumes the callee's behaviour.

11. **Rolled-back frames are not claimed.** History invariants hold of the
    final storage regardless; per-frame committed claims
    (the committed invocation lists) say nothing of
    frames rolled back or under a rolled-back ancestor.

12. **Curve cost is exact but existential** (`∃ c`), with no closed formula.

13. **Liveness frames are fresh frames** (empty stack and memory) at a state. Transaction-level witnesses are only those explicitly stated in Sections 5.6 and 5.11, under their premises.

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
    divergence the two fees agree exactly (`Blanc.Lift.WithdrawalRequest.word_fee_eq_iff_natFeeDomain` (`Blanc/Lift/WithdrawalRequest/ExactFeeDomain.lean:12`); against the EIP's formula directly, `Blanc.Lift.WithdrawalRequest.fee_eq_spec_iff` (`Blanc/Lift/WithdrawalRequest/HeadlineFee.lean:48`)). The FIFO headline is therefore stated
    for the executed word fee.

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

35. **USDC: the governance premise.** `UsdcGovernance`: no settled
    entry frame at USDC's proxy whose caller is the checkpoint's admin word calls
    upgradeTo, upgradeToAndCall or changeAdmin. It names an actor and three entry
    points, not an outcome; from it the implementation slot and the admin word are
    proved unchanged along the history. Every Section 5.10 history row takes it.

36. **USDC: the never-signer premise.** The holder-indexed bridge from
    `BookLawsS` takes `NeverSigner`; it is not established here for an arbitrary
    holder. The retained signer control shows why that premise is load-bearing.

37. **USDC: excluded positions.** The positional replay is stated only at
    settled positions that are not `UsdcShadowed`: a frame at the proxy that is not an
    entry frame (an implementation or library frame running over the proxy's storage,
    static or not), and a position inside the block of an earlier library frame at the
    proxy (the ERC-1271 and `ecrecover` static calls a signed message makes, at which
    part of its effect, such as `permit`'s nonce increment, may already be written).
    Settled frame values need not be unique, so the exclusion is by position.

38. **USDC: liveness premises.** The transfer facet takes the footprint core,
    HASH-T for the frame's keys, a caller distinct from the admin word, USDC's
    transfer state conditions and a budget covering the proxy's 63/64 cut. It is
    a frame-level statement under these premises, not a closed single-block instance.

39. **USDC: the key universe.** USDC's history key
    universe is the checkpoint's tracked keys extended by the keys every frame at the
    proxy may touch, read from its calldata and caller, whether or not the frame
    commits; HASH-T is stated over that universe. In the general statements the
    checkpoint's tracked set is any predicate; a checkpoint the checker accepts tracks
    exactly its finite rows.

40. **USDC: not claimed.** Anything about the live state of USDC or of any pool;
    the closed single-block USDC instance, which is not built; USDC versions other
    than FiatTokenV2_2 at the stated implementation address; and anything at the
    excluded positions item 37 describes.

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

**The 0 stricter claims** (`#expect_axioms NAME [set]`, each checked in both
directions by the same walker; a claim exists only together with the register
row or gate constant that states it; none concerns a deployed-bytecode theorem
of this map). The checker requires this table to equal the rows of
`scripts/AxiomCheck.lean` exactly.

| # | Declaration | Exact set | Stated by |
|---|---|---|---|

**The count.** The published number of results is the leaf search's count of
leaf theorems: theorems of a `Blanc.*` module that no other Blanc declaration
uses (`scripts/leaf_audit.py`, `scripts/GATES.md` "Leaf audit"), each covered
by the union walk. It is generated
into `scripts/leaf-count.json` (never hand-edited) and quoted by the README and
the sites. At this commit it is 2334 leaf results (2288 public, 46 private).
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
| `NoAuthorityAt` | `Blanc.ExecutionTrace.ConfiguredHistoryTrace.NoAuthorityAt` (`Blanc/ExecutionTraceCodeAt.lean:598`) | no authorization of any transaction of a configured history recovers to the given address |
| `SpawnFree` | `Blanc.SpawnFree` (`Blanc/ExecutionTraceSystem.lean:24`) | the code has no instruction that could spawn a child frame, read at every offset (false of the canonical EIP-7002 code) |
| `ShaReady` | `Blanc.Lift.ShaReady` (`Blanc/Lift/ExactWalkCutOps.lean:66`) | the SHA-256 precompile premises of a frame's world: address 2 undelegated and warm, a precompile of the fork |
| `VyInv` | `Blanc.Lift.Curve3Crv.VyInv` (`Blanc/Lift/Curve3Crv/Layout.lean:95`) | Curve 3Crv's storage abstraction over the live keys |
| `FreshKeys` | `Blanc.Lift.Curve3Crv.FreshKeys` (`Blanc/Lift/Curve3Crv/Layout.lean:115`) | the frame-local premise for the keys a Curve frame touches: each is fresh and their slots are pairwise distinct (HASH-T) |
| `Curve3Crv.historyTouchedKeys` | `Blanc.Lift.Curve3Crv.historyTouchedKeys` (`Blanc/Lift/Curve3Crv/CarriedHistory.lean:27`) | the keys a Curve history touches |
| `OwnerCallOk` | `Blanc.Lift.Curve3Crv.OwnerCallOk` (`Blanc/Lift/Curve3Crv/LiveBodies.lean:1866`) | the callee premise of Curve `set_name`: its static `owner()` call answers whenever it is given enough gas, and leaves at least `R` gas |
| `C3crvDeploymentTo` | `Blanc.Lift.Curve3Crv.C3crvDeploymentTo` (`Blanc/Lift/Curve3Crv/HistDeployment.lean:37`) | the 3Crv deployment record: the retained Muir Glacier block that created the token, its transaction at index 76 and successful receipt, the configured history to the checkpoint, and HASH-T freshness |
| `OwnerAnswerH` | `Blanc.Lift.Curve3Crv.OwnerAnswerH` (`Blanc/Lift/Curve3Crv/SafeBodies.lean:41`) | `OwnerAnswer` under the frame's actual delegation rules: the frame's static `owner()` call succeeded and returned a word starting with the recorded one |
| `HistFork` | `Blanc.HistFork` (`Blanc/HistoricalFork.lean:21`) | the historical extraction domain, Byzantium through BPO2, Amsterdam excluded |
| `StateInv` | `Blanc.ContractSpecSem.StateInv` (`Blanc/LadderSem.lean:86`) | the state invariant of a semantic contract spec (the semantic contract spec's state invariant) |
| `checkFaithfulOn` | `Blanc.SlotFootprint.checkFaithfulOn` (`Blanc/SlotFootprint.lean:133`) | decidable: each written key and each observed key with the same slot are the same key (a HASH-T instance on explicit lists) |
| `checkApartOn` | `Blanc.SlotFootprint.checkApartOn` (`Blanc/SlotFootprint.lean:145`) | decidable: no observed key has a slot in the given raw-slot list |
| `mapSlot` | `Blanc.Lift.mapSlot` (`Blanc/Lift/MapSlot.lean:19`) | the Solidity mapping slot `keccak(key ++ base)` |
| `HashAvoidIn` | `Blanc.LockExclusion.LockSpec.HashAvoidIn` (`Blanc/LockExclusion.lean:853`) | every frame of the pool running the lock code avoids the lock slot with its executed hashes (HASH-T) |
| `VplusExcludes` | `Blanc.Lift.VyperNonreentrantDeployed.Fixed.VplusExcludes` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:44`) | the statement form of the V+ exclusion |
| `Book` | `Blanc.Lift.Token.Book` (`Blanc/Lift/Token/Core.lean:48`) | a token's pure book: an abstract ledger, the step of one entered frame's message, the decoded operation, balances, allowances and a well-formedness predicate; no storage layout |
| `BookLaws` | `Blanc.Lift.Token.BookLaws` (`Blanc/Lift/Token/Core.lean:62`) | the laws of a book that the composition consumes (Section 5.10) |
| `Core` | `Blanc.Lift.Token.Core` (`Blanc/Lift/Token/Core.lean:98`) | what a token's address answers along a configured history, under an instance-chosen trace-local premise |
| `IsEntry` | `Blanc.Lift.Token.IsEntry` (`Blanc/Lift/Token/Core.lean:85`) | a frame entered at the token: storage owner and code address are both the token |
| `Erc20Abi` | `Blanc.Lift.Token.Erc20Abi` (`Blanc/Lift/Token/Abi.lean:17`) | the book reads the standard `transfer` and `balanceOf` selectors as those operations, for every calldata of at least 68 (`transfer`) or 36 (`balanceOf`) bytes and below 2^256 |
| `SelfCaller` | `Blanc.Lift.Token.SelfCaller` (`Blanc/Lift/Token/SelfCaller.lean:18`) | every entry-frame child of a settled non-static frame at the token has the token as caller |
| `TransferLive` | `Blanc.Lift.Token.TransferLive` (`Blanc/Lift/Token/Core.lean:145`) | frame-level `transfer` liveness at an exact cost, at the worlds an instance accepts |
| `UsdcGovernance` | `Blanc.Lift.Usdc.UsdcGovernance` (`Blanc/Lift/Usdc/Governance.lean:21`) | USDC's governance premise: no settled entry frame at the proxy from the admin word calls upgradeTo, upgradeToAndCall or changeAdmin |
| `NeverSigner` | `Blanc.Lift.Token.NeverSigner` (`Blanc/Lift/Token/Signed.lean:41`) | no settled non-static entry of the token along a history has the given account as signer |
| `UsdcShadowed` | `Blanc.Lift.Usdc.UsdcShadowed` (`Blanc/Lift/Usdc/HistoryReplay.lean:39`) | a non-entry frame at the proxy (implementation or library), or a position inside the block of an earlier library frame |
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
| `MintFits` | `Blanc.Composition.Curve3PoolCalleeLive.MintFits` (`Blanc/Composition/Curve3PoolCalleeLive.lean:342`) | 3Crv accepts `mint(d, v)` from the pool at the given storage |
| `BurnFits` | `Blanc.Composition.Curve3PoolCalleeLive.BurnFits` (`Blanc/Composition/Curve3PoolCalleeLive.lean:349`) | 3Crv accepts `burnFrom(f, v)` from the pool at the given storage |
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
  provenance, and the system-contract sizes and SHA-256 digests equal the bytes
  written in `Blanc/SystemContracts.lean`; the USDC code-read block and block hash,
  implementation slot and library link sites agree with the certificate provenance
  and lifted implementation bytes;
- the page keeps its section structure, its required headline theorems and its
  load-bearing disclosures, and carries no process vocabulary.

The required headline theorems are also pinned by exact statement in
`scripts/ClaimCheck.lean` (gate `scripts/check-claims.sh`), together with the
definitions they are stated through whose bodies are themselves the claim (pinned
by unfolding) and the record types they use (pinned field by field), so a weakened
headline fails there although this checker elaborates no Lean. The retained required names and their physical source owners are listed by this
checker; the exact statement-pin population is owned by `scripts/ClaimCheck.lean`.
The Curve 3pool statement pins include its exact-gas rows and premise-bundle
witnesses; the USDC pins retain `UsdcGovernance`, `UsdcShadowed`, `NeverSigner`
and the USDC-owned definition `PairUsdcAllowQuiet`. The reachable V± and EIP-7002
headlines retain their own pins. Pin counts are generated on the exact candidate.

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

Every run also executes in-memory falsifiers, each of which must be rejected:
a misspelled declaration, a stale line, a wrong file, an orphan line reference,
a missing cited file, a stale bare name, a wrong leaf count, extra, missing and
wrong stricter axiom claims, a wrong codehash, runtime size, creation transaction
and system-contract digest, a wrong Jaune revision, process vocabulary, a deleted
headline and a dropped disclosure; and for USDC a wrong code-read block, library
link site and implementation slot, a deleted headline and a dropped disclosure.
The stricter-row controls use a synthetic authority/table pair when the live
stricter-claim population is empty; equality with the real audit source remains
mandatory in both directions.

What the check does **not** do: it does not elaborate Lean or re-derive any
axiom set (its authority over axioms is `scripts/AxiomCheck.lean`, verified by
`scripts/check.sh`); it does not judge whether a row's prose is a fair summary
of its theorem, whether a premise list is complete, or whether the bytes in
`scripts/lift/inputs/` are the bytes on the chain; and it does not re-run the
conformance figures of Section 3.
