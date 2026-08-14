# Lido CircuitBreaker deviation registry

This is the registry required by `PORTING.md`. An observable difference from
the pinned v1.0.0 reference that is not entered and defended here is a defect.
This registry contains no mismatch allowlist. A finite passing differential
row is evidence only; it is not permission to omit a discovered difference.

<!-- LIDO-CIRCUIT-BREAKER-DEVIATION-POLICY {"status":"pending-user-adjudication","unknownMismatchAllowlist":false,"acceptedBehavioralRows":0,"pendingBehavioralRows":5,"measuredGasPaths":33} -->

## Accepted behavioral deviations

None. The runtime/status/state/log/call-trace matrix has no accepted semantic
mismatch, and the measured gas increases below have not been accepted by the
user. They are a conformance blocker until explicitly adjudicated.

## Pending user adjudication — conformance blocker

`PORTING.md` treats these five gas-increase classes as behavioral deviations
even though exact gas identity is not a compatibility target. The candidate
stances below are arguments for the required user decision, not acceptance.

| ID | Reference and Blanc behavior | Observable consequence | Candidate defense for user adjudication | Evidence |
|---|---|---|---|---|
| GAS-1 | Successful Solidity construction uses 967,777 gas in the named worlds; Blanc uses 1,029,868. | Blanc creation costs 62,091 more gas (62,085 with trailing accepted arguments). A factory or deployment envelope with a Solidity-calibrated fixed limit may fail. | Candidate defense: the cost buys the generated, parameterized Blanc constructor/runtime family and its compiler-checked artifact boundary. This is a conceded cost, not an improvement claim. | Exact candidate identities and six named paths below; pinned EELS Prague execution. |
| GAS-2 | The listed constructor rejection/dirty-address paths revert on both sides, with Blanc costing 681–871 more gas. | A tightly limited failing creation can exhaust gas before returning the same reference error. No contract is installed on either path. | Candidate defense: the cost buys the shared fail-closed constructor decoder/validation structure used by the verifiable artifact. It does not excuse changed error data or precedence. | Eight named paths below. |
| GAS-3 | Every selector rejects nonzero runtime value before endpoint effects; Blanc's named rejection paths cost 99–126 more gas. | A caller using an exact Solidity-calibrated failure stipend may observe OOG instead of the same empty revert. | Candidate defense: the small cost buys the uniform generated nonpayability/dispatch boundary. Cheapness matters, so the increase is declared; no semantic-success path is being reclassified as an optimization. | Seventeen named selector paths below. |
| GAS-4 | Empty calldata reverts on both sides; Blanc costs 94 more gas. | A fixed 68–161 gas execution envelope distinguishes the artifacts by OOG versus empty revert. | Candidate defense: the small cost buys Blanc's generated dispatcher. Empty calldata is not a CircuitBreaker feature, but the increased public-path cost is still declared under `PORTING.md`. | `runtime-empty-calldata` below. |
| GAS-5 | With a 32,768-byte successful `isPaused()` return, both sides allocate/copy the full returndata and complete pause; Blanc costs 945 more gas. | A tight Solidity-calibrated envelope can make only Blanc OOG. Exact OOG thresholds remain excluded, but the increase is observable. | Candidate defense: the cost buys source-compatible complete returndata handling in the Blanc runtime. The evidence also requires both sides' size slopes to remain close; this row does not permit the old 32-byte shortcut. | `pause-return-true-large-32768` plus the adequate-gas/OOG resource family. |

Any newly discovered observable mismatch or gas increase must be repaired or
added here before a conformance claim, with reference behavior, Blanc behavior,
consequence, informed-deployer stance, and named evidence.

## Measured named-path gas deltas

The measurement is EELS Prague `gasUsed` for the final transaction of each
named 172-row differential case. It compares Solidity runtime SHA-256
`7decb73763f1c184f5e1950c5e3449fbca507fdf40836769df2e67fccd0c8a1e`
with Blanc runtime SHA-256
`fa628a48ab7544301c5a4b287315ccff998fb43ec23fc16250f4a4309d9c100a`
at EELS commit `4198b9c5996713b268aed602739d5aa40e277694`.

<!-- LIDO-CIRCUIT-BREAKER-GAS-MEASUREMENT {"eelsCommit":"4198b9c5996713b268aed602739d5aa40e277694","solidityRuntimeSha256":"7decb73763f1c184f5e1950c5e3449fbca507fdf40836769df2e67fccd0c8a1e","blancRuntimeSha256":"fa628a48ab7544301c5a4b287315ccff998fb43ec23fc16250f4a4309d9c100a","gasModel":"EELS Prague gasUsed for final case transaction","pathCount":33} -->

Each machine-readable row is pinned by the compatibility checker. `delta` is
`blanc - solidity`; only positive rows are listed.

<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"constructor-dirty-admin","solidity":260,"blanc":1131,"delta":871} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"constructor-error-admin-zero","solidity":481,"blanc":1162,"delta":681} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"constructor-error-min-heartbeat-above-max","solidity":577,"blanc":1262,"delta":685} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"constructor-error-min-heartbeat-zero","solidity":551,"blanc":1234,"delta":683} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"constructor-error-min-pause-above-max","solidity":529,"blanc":1212,"delta":683} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"constructor-error-min-pause-zero","solidity":503,"blanc":1184,"delta":681} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"constructor-precedence-admin-zero-plus-min-pause-zero","solidity":481,"blanc":1162,"delta":681} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"constructor-precedence-both-bound-inversions","solidity":529,"blanc":1212,"delta":683} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"constructor-success-equal-bounds","solidity":967777,"blanc":1029868,"delta":62091} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"constructor-success-exact-lower-bounds","solidity":967777,"blanc":1029868,"delta":62091} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"constructor-success-exact-upper-bounds","solidity":967777,"blanc":1029868,"delta":62091} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"constructor-success-independent","solidity":967777,"blanc":1029868,"delta":62091} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"constructor-success-official","solidity":967777,"blanc":1029868,"delta":62091} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"constructor-trailing-arguments","solidity":967783,"blanc":1029868,"delta":62085} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"nonpayable-ADMIN","solidity":43,"blanc":145,"delta":102} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"nonpayable-MAX_HEARTBEAT_INTERVAL","solidity":43,"blanc":144,"delta":101} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"nonpayable-MAX_PAUSE_DURATION","solidity":43,"blanc":168,"delta":125} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"nonpayable-MIN_HEARTBEAT_INTERVAL","solidity":43,"blanc":144,"delta":101} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"nonpayable-MIN_PAUSE_DURATION","solidity":43,"blanc":144,"delta":101} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"nonpayable-getPausableCount","solidity":43,"blanc":143,"delta":100} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"nonpayable-getPausables","solidity":43,"blanc":144,"delta":101} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"nonpayable-getPauser","solidity":43,"blanc":145,"delta":102} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"nonpayable-heartbeat","solidity":43,"blanc":144,"delta":101} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"nonpayable-heartbeatExpiry","solidity":43,"blanc":143,"delta":100} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"nonpayable-heartbeatInterval","solidity":43,"blanc":144,"delta":101} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"nonpayable-isPauserLive","solidity":43,"blanc":142,"delta":99} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"nonpayable-pause","solidity":43,"blanc":145,"delta":102} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"nonpayable-pauseDuration","solidity":43,"blanc":169,"delta":126} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"nonpayable-registerPauser","solidity":43,"blanc":145,"delta":102} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"nonpayable-setHeartbeatInterval","solidity":43,"blanc":143,"delta":100} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"nonpayable-setPauseDuration","solidity":43,"blanc":143,"delta":100} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"pause-return-true-large-32768","solidity":57317,"blanc":58262,"delta":945} -->
<!-- LIDO-CIRCUIT-BREAKER-GAS {"path":"runtime-empty-calldata","solidity":68,"blanc":162,"delta":94} -->

## Low-level implementation freedoms (not behavioral deviations)

| Freedom | Boundary | Evidence obligation |
|---|---|---|
| Runtime/initcode bytes, code hash, dispatcher shape, and instruction sequence | Byte identity is a permanent non-goal under `PORTING.md`. | Generated Blanc artifact identity and lock provenance; never cite as Solidity-byte equality. |
| Raw persistent/transient storage keys and layout | The comparison projects both worlds to logical configuration, Registry, expiry, and pause state. | Projection is frozen and differential rows do not compare raw slots. |
| Exact gas and identical OOG threshold (not gas increases) | Exact equality is excluded, but every known increase on an externally callable named path is a behavioral deviation pending adjudication above. | Measured named-path deltas, scaling/OOG controls, and a stated adequate-gas envelope. |
| Internal helper/table decomposition | Private factoring is free only if it changes no declared status, returndata, projected state, ETH, logs, or call trace. | Artifact and differential channels. |

## Explicit exclusions and verification debts

| Exclusion | Not a deviation stance | Future owner |
|---|---|---|
| Universal Registry integrity and arbitrary-length enumeration | Not established; finite histories do not prove either property. | S2/S3 successor goals. |
| Arbitrary-descendant hostile reentry, access completeness, and actual-write classification | Not established; finite callback rows are not a theorem. | S4/S5 successor goals. |
| Jaune deployment correctness, arbitrary deployment shapes, sequence/history preservation, and monitoring theorems | Not established; constructor differential worlds are finite executable evidence. | S6/closure successor work. |
| Deployed Solidity bytecode verification or universal Solidity/Blanc equivalence | Not claimed by a Blanc port. | Separate verification project if desired. |

No exclusion authorizes a known in-scope observable mismatch. It limits only the
claim, consistently with `PORTING.md`.
