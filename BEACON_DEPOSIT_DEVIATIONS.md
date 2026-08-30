# Beacon deposit deviation and claim-boundary registry

This is the per-contract registry required by [`PORTING.md`](PORTING.md) for
the Blanc port of the pinned Ethereum beacon deposit contract. It records
known implementation differences, interface rulings, pending behavioral
questions, and explicit claim exclusions. A passing finite differential is
evidence on its stated rows only: it is neither a proof of universal
equivalence nor a liveness result. A known observable difference may not be
left out merely because this registry is non-exhaustive.

The comparison target is the vendored source
[`deposit_contract.sol`](scripts/reference/beacon-deposit/inputs/deposit_contract.sol)
(SHA-256
`2a8db249155e8502e1132f14410b8d7b2a924512723ed07a08167477d8f8c073`)
and the vendored deployed-runtime anchor under
[`scripts/reference/beacon-deposit/`](scripts/reference/beacon-deposit/).
The source algorithm is re-derived in the opening report's §B1.7. Raw source,
storage, instruction, and byte identity are not comparison targets.

## Closure status

This registry is fail-closed: a known observable difference may not be hidden
by an unfinished evidence marker.  The compiled proof families named below now
close the port's mandatory P1--P6 boundaries, and both committed differential
lanes close their stated finite matrices.  A row backed only by differential
evidence says so explicitly; finite agreement is never promoted to a universal
theorem.  Deployment-root and open-history claims remain explicit exclusions
owned by the nominated closure successor.

## Implementation differences and behavioral decisions

| ID | Surface | Pinned-reference semantics | Blanc semantics | Observable consequence | Project stance | Evidence / status |
|---|---|---|---|---|---|---|
| BD-1 | Raw storage layout | The source declares three regions in Solidity's layout: `branch[32]`, `deposit_count`, and `zero_hashes[32]`. The deployed artifact's raw slots follow its own compiler-produced scheme. | Blanc uses compact disjoint tagged bases on reachable indices: `branch[h] = 0x100 + h`, `deposit_count = 0x200`, and `zero_hashes[h] = 0x300 + h` for `h < 32`. | Logical deposits, roots, and counts can agree while raw slots, storage proofs, and storage roots differ. A reference storage image cannot be installed unchanged as Blanc state; differential seeded rows must seed each side through its own layout. | **Orthogonal to the contract's job.** A proof-oriented, structurally disjoint layout is an implementation freedom under `PORTING.md`; no raw-layout compatibility is claimed. | Source state declarations; frozen design in `docs/BEACON_DEPOSIT_PORT_DESIGN.md`; `Blanc/BeaconDepositCore.lean` declarations `branchSlot`, `depositCountSlot`, and `zeroHashSlot`; `Blanc/BeaconDepositBridge.lean` declarations `ArtifactInv`, `constructorFinalStorage_artifactInv`, `ArtifactInv.root_eq_mixedRootOf`, and `ArtifactInv.count_eq_history_length`; compiled establishment/preservation in `constructor_success_retainedStorageEffectTriples` and `deposit_success_artifactInv`; the pinned-EELS seeded cap-boundary row seeds and projects each side through its declared layout and is green. |
| BD-2 | Canonical dynamic calldata | Solidity's ABI decoder first interprets the three dynamic `bytes` arguments and the fixed `bytes32` root; the function body then checks lengths 48, 32, and 96 in that source order and returns the corresponding byte-exact `Error(string)` on the first failure. | Blanc's frozen `DepositAbiDecodable` boundary is a separate phase before every source guard. Phase one requires the 132-byte selector-plus-four-word head. Phase two checks each of the three tails independently: `offset < 2^32`, `36 + offset <= calldatasize`, `length := calldataload (4 + offset)`, `length < 2^32`, and `36 + offset + ceil32(length) <= calldatasize`. Reordered or overlapping tails are allowed; padding contents and trailing calldata are ignored. Structural failure empty-reverts. Only after all three tails pass does the body test lengths 48, 32, and 96 in source order. Compiled theorems separately require `data.length < 2^256` to relate Lean's unbounded length to `CALLDATASIZE`; this is a machine-representability premise, not an extra decoder guard, and canonical calls derive it from their `< 2^32` bound. | No difference is accepted on canonical decoded calls. The two-phase predicate also fixes the intended noncanonical machine boundary without defining decoding as merely whatever the implementation happens to read. It must not quietly exclude any canonical input accepted by the reference. | **Interface agreement required.** Dynamic argument decoding, guard precedence, and revert reasons are caller-visible contract behavior. | Frozen design in `docs/BEACON_DEPOSIT_PORT_DESIGN.md`; pinned source `deposit`; model `Reason` order; `Blanc/BeaconDepositCore.lean` declarations `DynamicTailDecodable`, `DepositAbiStructureDecodable`, `DepositAbiDecodable`, and `CanonicalDepositCalldata`; `Blanc/BeaconDepositEncoding.lean` theorem `canonicalDepositCalldata_decodable`; compiled malformed coverage in `deposit_malformed_noRawSstore`; total decoded-error coverage in `deposit_error_runCompiledTo`; compiled success in `deposit_success_runCompiled`; canonical, malformed, all-tail-precedence, and guard-precedence pinned-EELS rows are green. |
| BD-3 | Malformed or noncanonical dynamic calldata | Behavior is whatever the pinned solc decoder and deployed runtime do for the particular malformed shape, before or while the function body is reached. This includes truncated heads or tails, out-of-bounds or overlapping offsets, noncanonical offsets, inconsistent lengths, and trailing data. | Blanc first requires the 132-byte head, then independently requires every dynamic offset and length to fit below `2^32` and its padded tail to fit in calldata. It permits reordering/overlap, ignored padding bytes, and trailing calldata. Every structural failure empty-reverts before the source guards. | The chosen boundary reproduces the pinned decoder on the declared malformed/noncanonical matrix and accepts every canonical call, including calls whose source length guards fail. Agreement is finite evidence on those rows, not a universal decoder theorem; any later measured mismatch remains registry-bearing. | **Reference-shaped, measured finite agreement.** The algorithmic ruling is frozen and the mandatory reordered-tail, overlapping-tail, dirty-padding, trailing-data, truncation, out-of-bounds, and all-tail-precedence rows are green. | Frozen design in `docs/BEACON_DEPOSIT_PORT_DESIGN.md`; decoder predicates in `Blanc/BeaconDepositCore.lean`; canonical implication `BeaconDeposit.canonicalDepositCalldata_decodable`; compiled structural-failure theorem `deposit_malformed_noRawSstore` (including the exact selected `DepositAbiFailure`, raw-SSTORE freedom, and empty retained writes); execution-derived manifest rows and live comparison/manifest falsifiers. |
| BD-4 | Terminal insertion-loop `assert(false)` | After incrementing the count, the source's 32-step insertion loop returns at the first set bit. It retains a terminal `assert(false)` after the loop as a defensive unreachable arm. | The Blanc loop omits the terminal panic arm and exits by construction. This omission is licensed **only** by `BeaconDeposit.deposit_ne_assert_false`; no informal cap argument substitutes for that theorem. | On model-covered decoded inputs there is no observable difference because `.error .assert_false` is impossible. No equivalence is claimed for a state or execution that falls outside the theorem's premises or the compiled storage abstraction. | **Orthogonal low-level control flow.** Removing a proved-dead arm keeps the reachable interface while simplifying the structured program and its proof. | `Blanc/BeaconDepositCorrectness.lean`, theorem `BeaconDeposit.deposit_ne_assert_false`; `Blanc/BeaconDepositInsertCommit.lean`, theorem `commitDeposit_firstLive_exists_runCompiledTo`, which executes the complete concrete commit through the unique first-live slot; `Blanc/BeaconDepositSuccessPublic.lean`, theorem `deposit_success_runCompiled`, which instantiates that exit from model success; and `Blanc/BeaconDepositErrors.lean`, theorem `deposit_error_runCompiledTo`, whose total reachable-error elimination has no `assert_false` arm. |
| BD-5 | Internal program structure, runtime bytes, and creation bytes | The reference artifacts were produced by the pinned Solidity toolchain and have their own dispatcher, control flow, stack discipline, instruction selection, metadata, runtime, and initcode. The pinned deployed runtime is 6,358 bytes and its creation artifact is 6,633 bytes. | Blanc uses structured `Func` control flow, tail-recursive loops, a gas-shaped four-leaf dispatcher, and its own compiler output. The compiler-owned runtime is 2,891 bytes (SHA-256 `8f2474c60f85dce94e97403369d64d94d7cce4bbb44e620175bd43a5990f0c48`); the constructor uses fixed `PUSH2` coordinates with an exact full-width fallback, giving a 146-byte prefix and a complete 3,037-byte creation artifact with SHA-256 `3f3af51d0674c1afb7679dbcc60720bbd3f3d61adc9bd319da025064c0521c59`. | Runtime/creation bytes and code hashes differ; tooling or callers pinned to reference byte or code-hash identity will not recognize the Blanc artifact as the deployed artifact. Blanc's runtime is 3,467 bytes (54.53%) smaller and its creation artifact 3,596 bytes (54.21%) smaller. Endpoint behavior is compared separately. | **Orthogonal to the contract's job.** Byte identity is a permanent non-goal under `PORTING.md`; the obligation is to prove Blanc's own program-to-bytes connection and test the declared interface. | `Blanc/BeaconDeposit.lean`, `BeaconDepositCode.lean`, and `BeaconDepositDeploy.lean`; compiler/size/tail/source-site theorems there; artifact identities independently rechecked by `scripts/fixtures/beacon-deposit/manifest.json` (historical Prague) and `scripts/fixtures/beacon-deposit-current-mainnet/manifest.json` (BPO2); EIP-170 and EIP-3860 bounds. Never cite these as equality with the deployed artifact. |

## Interface agreements (not deviations)

These rulings are recorded because they constrain the implementation and stop
an agreement from being mislabeled as a low-level freedom.

| Surface | Reference semantics | Required Blanc semantics | Classification | Evidence / status |
|---|---|---|---|---|
| Nonpayable views and ERC-165 | `get_deposit_root` and `get_deposit_count` are `view`; `supportsInterface` is `pure`. The pinned Solidity artifact rejects nonzero-value calls to all three before performing their bodies. | The same three recognized selectors reject nonzero call value, with no state write or log. The exact status and returndata must match the reference rows. `deposit` remains payable. | **Interface agreement.** The ABI's mutability boundary protects callers from silently stranded value and is reproduced, not registered as an accident. | Source declarations; opening fidelity finding 2; exact selected empty-revert routes and same-execution raw-SSTORE certificates `getDepositRoot_nonzero_value_runCompiledTo_noRawSstore`, `getDepositCount_nonzero_value_runCompiledTo_noRawSstore`, and `supportsInterface_nonzero_value_runCompiledTo_noRawSstore`; global source-site classification in `beaconRuntime_sstore_pc_of_rawFrameRoot`; all three value-carrying pinned-EELS rows are green with exact status/returndata/state/log comparison. |
| Guard order, reason strings, and event timing | The three length guards precede the three value guards; the event is emitted after those six guards but before root and cap validation, and a later revert makes it unobservable. The event index is the pre-increment count. | Blanc uses the same source-shaped order, byte-exact `Error(string)` data, and old-count index. The successful compiled theorem proves the exact emitted event; the two late-error source walks pass event staging and seven childless SHA-256 calls before reverting. Enclosing-call invisibility for those late logs is supported by the ordinary revert-settlement semantics and the finite differential log/revert channels; this goal does not claim a separate universal raw-`LOG` occurrence theorem for those arms. | **Interface agreement.** No deviation is accepted. | Pinned source §`deposit`; model `Reason`, `DepositEvent`, and `deposit_ok_spec`; compiled success/settlement in `deposit_success_runCompiled` and `deposit_success_settled_effects`; the eight public error theorems and their model-error-indexed wrapper `deposit_error_runCompiledTo`, each now carrying same-execution raw-SSTORE freedom and empty retained forms; all eight guard rows, precedence row, successful exact-event rows, and live log/revert channel falsifiers are green. |
| SHA-256 STATICCALL response handling | At every source-shaped SHA-256 wrapper, a failed child call copies the complete returndata and reverts with those exact bytes; zero-length child returndata therefore produces the ordinary empty-data revert subcase. A successful child response shorter than 32 bytes empty-reverts, while a response of at least 32 bytes supplies its first word. The pinned creation bytecode contains twelve instances of `3d6000803e3d6000fd` (`RETURNDATASIZE; PUSH1 0; DUP1; RETURNDATACOPY; RETURNDATASIZE; PUSH1 0; REVERT`), one for each source-shaped SHA-256 site, followed at each wrapper by the 32-byte length guard. | Every failed `STATICCALL` to address `0x2` takes the shared `Func.revReturnData` auxiliary and bubbles complete child returndata; the success arm checks `RETURNDATASIZE >= 32`, empty-reverting when short and otherwise consuming the first output word. | **Interface agreement.** Failure status, returndata, and short-success rejection are caller-visible; normalizing every response edge to an empty revert or accepting a partial digest would be a deviation. | Pinned creation artifact and frozen design; compiled successful precompile crossings in `Ninst.runCompiled_statcall_sha256_64_warm_ext` and `sha64_success_prefix_runCompiledTo_ext`, consumed by the root, reconstruction, insertion, and constructor proofs; failed-empty/payload/long, successful-short/long-first-word, exact output-buffer, and three common-gas OOG rows are green with live channels. The hostile-response matrix is finite differential evidence, not a universal compiled failure theorem. |
| Selectors and ERC-165 answers | The callable selectors are `22895118`, `c5f2892f`, `621fd130`, and `01ffc9a7`; ERC-165 reports the pinned ERC-165 and deposit interface ids and rejects `ffffffff`. | Exactly the same four selectors plus the no-match path, and the same Boolean answers. | **Interface agreement.** | Pinned source/vectors; compiler witness `code_compile`; `beaconSelectors` and `tree_hasSelector_iff` give the complete four-selector census; compiled public theorems `supportsInterface_runCompiled`, `getDepositRoot_zero_runCompiled`, `getDepositCount_warm_runCompiled`, and `getDepositCount_cold_runCompiled`; `unmatched_selector_noRawSstore` covers every nonempty selector-dispatch input outside that census, while `empty_calldata_runCompiledTo` separately proves the top-level empty-calldata branch and the older `noMatchSelector_runCompiledTo` remains a fixed regression row; exact compiler-emitted selector inventory and all selector/no-match/ERC-165 pinned-EELS rows are green. |

## DepositEvent ABI-size correction

The B5 design memo described the five dynamic tails as “~416 bytes of log
data.” The number 416 is exactly the **tail-region** size, not the complete
event data size. The pinned source and ABI layout govern, so the Blanc LOG1
payload must be **576 bytes** (`0x240`) in total:

| Region | Bytes | Running offset |
|---|---:|---:|
| Five 32-byte offset heads | 160 | `0x00..0x9f` |
| `pubkey`: length word + 48 bytes padded to 64 | 96 | `0xa0..0xff` |
| `withdrawal_credentials`: length word + 32 bytes | 64 | `0x100..0x13f` |
| `amount`: length word + 8 bytes padded to 32 | 64 | `0x140..0x17f` |
| `signature`: length word + 96 bytes | 128 | `0x180..0x1ff` |
| `index`: length word + 8 bytes padded to 32 | 64 | `0x200..0x23f` |
| **Total tails** | **416** | |
| **Complete LOG data** | **576** | |

Accordingly the five head offsets are `0xa0`, `0x100`, `0x140`, `0x180`, and
`0x200`. This is a correction to planning prose, not a reference/Blanc
deviation. Event shape and byte-exact encoding are interface.
`Blanc/BeaconDepositCore.lean` defines `abiDepositEvent` and
`CanonicalDepositEventData`; `Blanc/BeaconDepositEncoding.lean` proves
`abiDepositEvent_mk` and `abiDepositEvent_length`.  The compiled success and
settlement witnesses are `deposit_success_runCompiled` and
`deposit_success_settled_effects`; the latter exposes the retained successful
effects in the settlement substrate.  The exact-event differential rows and
live log-channel falsifier are green.

## Gas and finite-resource rows

Exact gas identity is not claimed, but gas is observable. The committed
Prague direct-message matrix records 69 runtime transactions: 67 are strictly
cheaper in Blanc, two shared-gas OOG thresholds are equal, and none is more
expensive. The median delta is -1,131 gas and the largest saving is 18,090.
These are finite measurements on the manifest's exact worlds, not a universal
gas theorem. Because there is no positive public-path delta, the marker
protocol correctly requires no `BD-GAS-*` deviation row.

| Row family | Measured coordinates | Result / disposition |
|---|---|---|
| GAS-P1 deposit success | Canonical first deposit, four accepted noncanonical encodings, value edges, and chained counts 1..8 across insertion depths | Blanc saves 6,801 gas on the canonical first deposit (55,249 vs 62,050); chained savings range from 6,801 to 8,422. **No positive delta.** |
| GAS-P2 deposit rejection | All eight reachable guards in source order and the all-invalid precedence row | Early source guards save 56..108 gas; root mismatch saves 6,578 and cap rejection 6,676. **No positive delta.** |
| GAS-P3 read-only selectors | Empty-state and chained `get_deposit_root`/`get_deposit_count`; true/false/`ffffffff` and dirty-padding `supportsInterface` | A normal root read saves 18,063 gas (84,032 vs 102,095), count saves 1,131 (2,383 vs 3,514), and supports probes save 116 or 133. **No positive delta.** |
| GAS-P4 dispatch and ABI rejection | Empty/unknown no-match, deposit malformed shapes and all-tail precedence, short supports calldata, and each nonpayable value rejection | Empty fallback saves 26 gas (20 vs 46), unknown fallback 29, malformed paths 10..64, and nonpayable paths 10..33. **No positive delta.** |
| GAS-P5 precompile resource edges | Failed empty/payload/long returndata, short and long success, plus common-gas child/before-first/first-success OOG boundaries | Failure/short-success rows save 466..484 gas; long-success root saves 18,063; one child-OOG row saves 4; the two shared thresholds are equal. **No positive delta.** |
| GAS-P6 construction | Constructor completion and its 31 SHA-256 calls; reported separately from public runtime paths | In fresh direct creation messages with every Prague precompile prewarmed, the reference uses 1,993,844 gas and Blanc 1,274,272, a 719,572-gas saving. Runtime code deposit is 1,271,600 vs 578,200 (-693,400), while constructor execution itself is 722,244 vs 696,072 (-26,172). Exact returned/installed runtime, poststate, 31-call SHA chain, and zero refund counters agree with their side-qualified expectations. **No positive delta.** |
| GAS-P7 current-mainnet BPO2 | Two fresh top-level CREATE transactions plus the same ordered seven-transition runtime state chain per side under the contract-neutral BPO2 lane | Creation transaction gas is 2,146,896 reference vs 1,368,074 Blanc (-778,822). Regular intrinsic gas is 153,052 vs 93,802 and code deposit is 1,271,600 vs 578,200; the remaining receipt-charged constructor execution after any transaction refund is 722,244 vs 696,072 (-26,172). The target does not expose a refund counter, so this row makes no zero-refund claim. Runtime deltas are deposit -6,801, root -18,072, count -1,131, the three ERC-165 probes equal, and no-match -26. **No positive delta and therefore no `BD-BPO2-GAS-*` marker.** |

Measurement basis and every exact transaction-level value live in
`scripts/fixtures/beacon-deposit/manifest.json`: pinned EELS
`4198b9c5996713b268aed602739d5aa40e277694`, Prague, direct
`process_message_call`, fresh runtime transaction access sets, and the
manifest's fully committed logical seed per row. The separate creation section
uses two fresh direct prepared messages with caller, target, coinbase, and all
17 Prague precompiles prewarmed. Its `createMessageGas` includes constructor
execution and runtime code deposit; transaction intrinsic/calldata charges,
EIP-3860 initcode-word charging, refund application, and transaction settlement
are explicitly outside that comparison. Net savings elsewhere would not erase
a positive row; the empty positive-delta list is measured, not inferred from an
aggregate.

The independent current-mainnet evidence lives in
`scripts/fixtures/beacon-deposit-current-mainnet/manifest.json`. It pins the
contract-neutral target checkout `827a1cad9c9c8528512f90a06888c8bd9171d9ae`,
execution fork BPO2, chain id 1, reward -1, and logical compiler lineage Osaka
(EEST testing backend `cancun`, no external solc invocation). Creation uses one
fresh state-test transition per side. Runtime uses seven ordered state-test
transitions per side, carrying each exact prior poststate forward; this avoids
silently supplying unrelated mainnet system-contract code while retaining the
contract's causal deposit/read chain. Every transaction uses the EIP-7825 cap
of 16,777,216 gas, and both EIP-7623 calldata floors are checked nonbinding.
The manifest credits exact raw logs/storage/ETH only on the deposit row and
status/gas on every row; exact returndata and the broader malformed,
precompile-response, and OOG corpus remain exclusively in the preserved Prague
gate.

## Explicit equivalence and verification exclusions

| Exclusion | Boundary of the present claim | Future owner, if wanted |
|---|---|---|
| Verification of the deployed reference | Lean theorems concern Blanc's own named program and exact compiled artifacts under their stated premises. The deployed runtime is executed only as the finite differential oracle; this port does not prove that artifact correct. | A separate reference-bytecode verification project. |
| Universal reference/Blanc equivalence or liveness | Differential agreement applies only to the committed matrix and is not a proof, an exhaustive behavioral comparison, a gas-parity theorem, or evidence that a call or deployment will eventually succeed or be included. | A separately stated universal theorem or operational programme. |
| P7 deployment-root transition | This goal includes the constructor program, its exact creation artifact, write classification, and abstraction-establishing postcondition. It does **not** prove a transaction/block/state-transition deployment root, historical inclusion, propagation, signing, CREATE/CREATE2 variants, factory deployment, co-blocks, arbitrary forks, or endowment shapes. | The nominated beacon-deposit closure successor. |
| P8 history/open-frame family | No theorem in this goal carries the storage abstraction or monotone count through arbitrary future transactions, re-entry shapes, blocks, or configured-chain reachability. | The nominated beacon-deposit closure successor. |
| Raw implementation identity | No source, dispatcher, instruction, runtime-byte, creation-byte, code-hash, raw-slot, storage-root/proof, or exact-gas identity with the reference is claimed. | Permanently outside the Blanc port claim, except finite measurements as evidence. |

No exclusion authorizes a known in-scope observable mismatch. The completed
port's conformance claim is limited to its proved specifications, the stated
finite differential corpus, and the defended rows in this registry.
