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

## Status while the port is being completed

This registry is intentionally fail-closed. Bracketed `PENDING` entries are
unfinished evidence or a decision that the implementation and differential
campaign must settle before the port can close. They are not accepted
deviations and do not authorize a mismatch. In particular, the implementation
and abstraction evidence for the frozen storage layout, the noncanonical-ABI
differential disposition, artifact identities, and gas rows remain provisional
until their named evidence exists.

## Implementation differences and behavioral decisions

| ID | Surface | Pinned-reference semantics | Blanc semantics | Observable consequence | Project stance | Evidence / status |
|---|---|---|---|---|---|---|
| BD-1 | Raw storage layout | The source declares three regions in Solidity's layout: `branch[32]`, `deposit_count`, and `zero_hashes[32]`. The deployed artifact's raw slots follow its own compiler-produced scheme. | Blanc uses compact disjoint tagged bases on reachable indices: `branch[h] = 0x100 + h`, `deposit_count = 0x200`, and `zero_hashes[h] = 0x300 + h` for `h < 32`. | Logical deposits, roots, and counts can agree while raw slots, storage proofs, and storage roots differ. A reference storage image cannot be installed unchanged as Blanc state; differential seeded rows must seed each side through its own layout. | **Orthogonal to the contract's job.** A proof-oriented, structurally disjoint layout is an implementation freedom under `PORTING.md`; no raw-layout compatibility is claimed. | Source state declarations; frozen design in `docs/BEACON_DEPOSIT_PORT_DESIGN.md`; `[PENDING]` named Blanc slot definitions, storage-abstraction theorem, constructor postcondition, and seeded cap-boundary differential row. |
| BD-2 | Canonical dynamic calldata | Solidity's ABI decoder first interprets the three dynamic `bytes` arguments and the fixed `bytes32` root; the function body then checks lengths 48, 32, and 96 in that source order and returns the corresponding byte-exact `Error(string)` on the first failure. | Blanc's frozen `DepositAbiDecodable` boundary is a separate phase before every source guard. Phase one requires the 132-byte selector-plus-four-word head. Phase two checks each of the three tails independently: `offset < 2^32`, `36 + offset <= calldatasize`, `length := calldataload (4 + offset)`, `length < 2^32`, and `36 + offset + ceil32(length) <= calldatasize`. Reordered or overlapping tails are allowed; padding contents and trailing calldata are ignored. Structural failure empty-reverts. Only after all three tails pass does the body test lengths 48, 32, and 96 in source order. | No difference is accepted on canonical decoded calls. The two-phase predicate also fixes the intended noncanonical machine boundary without defining decoding as merely whatever the implementation happens to read. It must not quietly exclude any canonical input accepted by the reference. | **Interface agreement required.** Dynamic argument decoding, guard precedence, and revert reasons are caller-visible contract behavior. | Frozen design in `docs/BEACON_DEPOSIT_PORT_DESIGN.md`; pinned source `deposit`; model `Reason` order; `[PENDING]` predicate implementation, canonical-encoding implication, undecodable-call theorem, compiled decode lemmas, and guard-precedence differential rows. |
| BD-3 | Malformed or noncanonical dynamic calldata | Behavior is whatever the pinned solc decoder and deployed runtime do for the particular malformed shape, before or while the function body is reached. This includes truncated heads or tails, out-of-bounds or overlapping offsets, noncanonical offsets, inconsistent lengths, and trailing data. | Blanc first requires the 132-byte head, then independently requires every dynamic offset and length to fit below `2^32` and its padded tail to fit in calldata. It permits reordering/overlap, ignored padding bytes, and trailing calldata. Every structural failure empty-reverts before the source guards. | The chosen boundary is designed to reproduce the pinned decoder and accepts every canonical call, including calls whose source length guards fail. A measured noncanonical mismatch would still be observable and must become a defended row rather than being hidden outside P2/P3. | **Reference-shaped, pending differential disposition.** The algorithmic ruling is frozen; exact noncanonical agreement remains an evidence question until the mandatory malformed matrix is green. | Frozen design in `docs/BEACON_DEPOSIT_PORT_DESIGN.md`; `[PENDING]` named decoder predicate/lemmas, undecodable-calldata theorem, malformed-row manifest, channel falsifier, and pinned-EELS results. |
| BD-4 | Terminal insertion-loop `assert(false)` | After incrementing the count, the source's 32-step insertion loop returns at the first set bit. It retains a terminal `assert(false)` after the loop as a defensive unreachable arm. | The Blanc loop omits the terminal panic arm and exits by construction. This omission is licensed **only** by `BeaconDeposit.deposit_ne_assert_false`; no informal cap argument substitutes for that theorem. | On model-covered decoded inputs there is no observable difference because `.error .assert_false` is impossible. No equivalence is claimed for a state or execution that falls outside the theorem's premises or the compiled storage abstraction. | **Orthogonal low-level control flow.** Removing a proved-dead arm keeps the reachable interface while simplifying the structured program and its proof. | `Blanc/BeaconDepositCorrectness.lean`, theorem `BeaconDeposit.deposit_ne_assert_false`; `[PENDING]` compiled loop-exit/refinement theorem showing that this model result licenses the concrete omission. |
| BD-5 | Internal program structure, runtime bytes, and creation bytes | The reference artifacts were produced by the pinned Solidity toolchain and have their own dispatcher, control flow, stack discipline, instruction selection, metadata, runtime, and initcode. | Blanc uses structured `Func` control flow, its selected measured loop realization, its own dispatcher, and its own compiler output. Exact artifact identities and sizes are **`[PENDING]`** until the compile witnesses land. | Runtime/creation bytes and code hashes differ; tooling or callers pinned to reference byte or code-hash identity will not recognize the Blanc artifact as the deployed artifact. Endpoint behavior is compared separately. | **Orthogonal to the contract's job.** Byte identity is a permanent non-goal under `PORTING.md`; the obligation is to prove Blanc's own program-to-bytes connection and test the declared interface. | `[PENDING]` named program, compiled-runtime/constructor witnesses, byte lengths, digests, and EIP-170 bound. Never cite these as equality with the deployed artifact. |

## Interface agreements (not deviations)

These rulings are recorded because they constrain the implementation and stop
an agreement from being mislabeled as a low-level freedom.

| Surface | Reference semantics | Required Blanc semantics | Classification | Evidence / status |
|---|---|---|---|---|
| Nonpayable views and ERC-165 | `get_deposit_root` and `get_deposit_count` are `view`; `supportsInterface` is `pure`. The pinned Solidity artifact rejects nonzero-value calls to all three before performing their bodies. | The same three recognized selectors reject nonzero call value, with no state write or log. The exact status and returndata must match the reference rows. `deposit` remains payable. | **Interface agreement.** The ABI's mutability boundary protects callers from silently stranded value and is reproduced, not registered as an accident. | Source declarations; opening fidelity finding 2; `[PENDING]` compiled nonpayable/write-free theorems and one value-carrying differential row per selector. |
| Guard order, reason strings, and event timing | The three length guards precede the three value guards; the event is emitted after those six guards but before root and cap validation, and a later revert makes it unobservable. The event index is the pre-increment count. | Blanc must use the same order, byte-exact `Error(string)` data, rollback-visible timing, and old-count index. The late-root/cap proofs retain the raw `LOG` occurrence and reverted-frame log field while proving that it is not retained and that the enclosing call/top-level output exposes no log. | **Interface agreement.** No deviation is accepted. | Pinned source §`deposit`; model `Reason`, `DepositEvent`, and `deposit_ok_spec`; `[PENDING]` compiled P2/P3 theorems and differential rows. |
| SHA-256 STATICCALL response handling | At every source-shaped SHA-256 wrapper, a failed child call copies the complete returndata and reverts with those exact bytes; zero-length child returndata therefore produces the ordinary empty-data revert subcase. A successful child response shorter than 32 bytes empty-reverts, while a response of at least 32 bytes supplies its first word. The pinned creation bytecode contains twelve instances of `3d6000803e3d6000fd` (`RETURNDATASIZE; PUSH1 0; DUP1; RETURNDATACOPY; RETURNDATASIZE; PUSH1 0; REVERT`), one for each source-shaped SHA-256 site, followed at each wrapper by the 32-byte length guard. | Every failed `STATICCALL` to address `0x2` takes the shared `Func.revReturnData` auxiliary and bubbles complete child returndata; the success arm checks `RETURNDATASIZE >= 32`, empty-reverting when short and otherwise consuming the first output word. | **Interface agreement.** Failure status, returndata, and short-success rejection are caller-visible; normalizing every response edge to an empty revert or accepting a partial digest would be a deviation. | Pinned creation artifact in `scripts/reference/beacon-deposit/inputs/deposit_contract.json`; frozen design in `docs/BEACON_DEPOSIT_PORT_DESIGN.md`; `[PENDING]` compiled routing/bubbling/short-success theorems and returndata/OOG differential rows with live payload and length-channel falsifiers. |
| Selectors and ERC-165 answers | The callable selectors are `22895118`, `c5f2892f`, `621fd130`, and `01ffc9a7`; ERC-165 reports the pinned ERC-165 and deposit interface ids and rejects `ffffffff`. | Exactly the same four selectors plus the no-match path, and the same Boolean answers. | **Interface agreement.** | Pinned source/vectors; `[PENDING]` dispatcher witness, P4 theorems, and differential rows. |

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
deviation. Event shape and byte-exact encoding are interface; `[PENDING]` the
canonical-encoding declaration, compiled LOG theorem, differential byte
comparison, and event-channel falsifier.

## Gas and finite-resource rows — pending measurement

Exact gas identity is not claimed, but gas is observable. Every externally
callable path whose measured Blanc gas exceeds the deployed reference must
become a defended deviation row; savings may be reported only from named
measurements. No gas result or dominance claim is made by this draft.

| Pending row family | Coordinates that must be measured | Result / disposition |
|---|---|---|
| GAS-P1 deposit success | First deposit; chained counts covering different insertion depths; value boundaries; event and all SHA-256 calls present | **`[PENDING differential measurements]`** |
| GAS-P2 deposit rejection | Each reachable guard in source order and the precedence row | **`[PENDING differential measurements]`** |
| GAS-P3 read-only selectors | `get_deposit_root`, `get_deposit_count`, and true/false/`ffffffff` `supportsInterface` rows | **`[PENDING differential measurements]`** |
| GAS-P4 dispatch and ABI rejection | No-match, malformed-ABI representatives, and each nonpayable value-rejection row | **`[PENDING differential measurements]`** |
| GAS-P5 precompile resource edges | STATICCALL-to-`0x2` adequate, returndata, and OOG boundary rows used by the campaign | **`[PENDING differential measurements]`** |
| GAS-P6 construction | Constructor completion and its 31 SHA-256 calls; reported separately from public runtime paths | **`[PENDING differential measurements]`** |

The final registry must state the measurement basis, exact matrix coordinate,
reference gas, Blanc gas, delta, consequence, stance, and evidence for each
positive public-path delta. Net savings elsewhere do not erase a positive row.

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
