# Lido CircuitBreaker deviation registry

This is the registry required by `PORTING.md`. An observable difference from
the pinned v1.0.0 reference that is not entered and defended here is a defect.
This registry contains no mismatch allowlist. A finite passing differential is
evidence only; it is not permission to omit a discovered difference.

<!-- LIDO-CIRCUIT-BREAKER-DEVIATION-POLICY {"status":"optimized-no-known-deviations","unknownMismatchAllowlist":false,"acceptedBehavioralRows":0,"pendingBehavioralRows":0,"adequatePositiveDeltaRows":0,"intrinsicBranchDispatchRows":0,"completionThresholdRows":33,"dispatcherThresholdRows":18,"measuredResourceBoundaries":464} -->

## Accepted behavioral deviations

None. The optimized candidate has zero accepted behavioral deviations: status,
exact returndata, logical projected state, ETH, ordered logs, and retained call
traces agree on every manifest row.

## Pending behavioral deviations

None. The optimized candidate has zero pending behavioral deviations. The five
pre-optimization gas classes GAS-1 through GAS-5 were repaired rather than
accepted or relabeled.

## Optimized finite resource evidence

The committed optimized manifest contains 175 cases and every one of their 464
constructor, clone-constructor, clone-history, history, and action boundaries.
Under its declared 20,000,000-gas adequate envelope, every adequate boundary in
the finite manifest is cheaper: 462 are strictly cheaper, the two explicit OOG
controls are equal, and no adequate boundary is dearer. There are 362 strict
successful-boundary improvements. Direct EELS Prague message gas is compared
before refunds, without transaction intrinsic gas and with CREATE code-deposit
gas.

All 33 former GAS-family witnesses have Blanc completion thresholds no greater
than Solidity. Each threshold is the minimum direct-message gas that reproduces
the complete adequate outcome. Constructor thresholds also reproduce the owned
installed runtime, and runtime probes rebuild a fresh causal world while
retaining adequate gas for the seed and history. The 17 nonzero-selector rows
and empty calldata are cross-checked against the selected dispatcher's separate
direct-state threshold instrument. The two 25,000-gas equal-OOG controls remain
separate and are not relabeled as threshold witnesses.

<!-- LIDO-CIRCUIT-BREAKER-GAS-MEASUREMENT {"stage":"optimized","manifestSha256":"2b0716f7d666d69d2844e2c8a01b5cd3f59cc124ba571ef16a5a02ad55cf3693","eelsCommit":"4198b9c5996713b268aed602739d5aa40e277694","cases":175,"boundaries":464,"adequateBoundaries":462,"oogControls":2,"adequatePositiveDeltas":0,"intrinsicBranchDispatchRows":0,"completionThresholdRows":33,"completionThresholdRowsSha256":"49456665e2c6095cb1aa467231d78e45deef3d5dc9614248fcdcd756217c83fe","dispatcherThresholdRows":18,"dispatcherThresholdRowsSha256":"b7b8f0ad5ca7e96de4cff76f54b4c661fce7f3faefd8e6d15526d9317db78bee","successfulStrictImprovements":362,"blancCreationTemplateSha256":"e899d8f2d7406f7aa6bf6ac60e25779355c6f1e3063f5edd4aed694710ba2eaa","blancOfficialFullCreateSha256":"bbf5c2c548a4c56ae9079cdb63f20b607ea8c4dabf853771bd33228099e2fa64","blancOfficialRuntimeSha256":"ff8eb66d66f8e4668af9bf5b687dda082c3729f8cd5ffd24a4b14697389d1505","blancIndependentFullCreateSha256":"c33bbb06829ca1f66c536ace9d0a8a108a6f7c1a609f3aed68490afdfa50862f","blancIndependentRuntimeSha256":"ce955ede77a6343897f61bd5395731e404d9ca271fe86849359c6c9d50803796","fullResourceVectorSha256":"98392ffe11a9eeef6407e90cc42b55739f384c154ef090473882e5d60d69a335","orderedCoordinatesSha256":"07ca7475b4af537e4866de0a8f102f043ced22c4207ef8587d7570bd9151aef2"} -->

The official Blanc runtime is 4,282 bytes and its full CREATE input is 5,122
bytes; successful construction uses 906,729 gas, versus Solidity's 4,584
bytes, 5,638 bytes, and 967,777 gas. Former constructor rejection excesses are
now savings of 117–307 gas. Every selector's nonzero-value rejection is 11 gas
cheaper, empty calldata is 36 gas cheaper, and the former 32,768-byte successful
return excess is now a 7,444-gas saving.

Successful `isPaused()` handling requests a 32-byte `STATICCALL` output window,
requires at least 32 returndata bytes, decodes only the canonical first word,
and performs no successful-tail `RETURNDATACOPY`. Failed `CALL` and
`STATICCALL` paths still copy and bubble their complete revert data. The finite
return-size and OOG controls measure this resource shape; they do not turn it
into a universal theorem.

## Intrinsic `.branch` dispatch comparison rows

The exact `intrinsic-branch-dispatch` set is empty and contains zero rows. Blanc
still expresses all control flow, including selector dispatch, through
`Func.branch`; direct-jump dispatch is not an allowed implementation freedom.
The selected hybrid tree remains independently Pareto-checked against legal
balanced, linear, and hybrid trees.

If a future adequate row is positive, the architecture label is available only
when independent opcode traces place its entire excess before the selected
leaf, no later Blanc segment is costlier, the legal tree remains Pareto-
justified, and the exact coordinate and delta are independently pinned and
mutation-tested. A future positive adequate row is not silently netted against
savings: absent that full evidence it is a deviation or a defect.

## Low-level implementation freedoms (not behavioral deviations)

| Freedom | Boundary | Evidence obligation |
|---|---|---|
| Runtime/initcode bytes, code hash, dispatcher shape, and instruction sequence | Byte identity is a permanent non-goal under `PORTING.md`; structured control flow remains mandatory. | Generated Blanc artifact identity, compiler connection, and lock provenance; never cite this as Solidity-byte equality. |
| Raw persistent/transient storage keys and layout | The comparison projects both worlds to logical configuration, Registry, expiry, and pause state. | Projection is frozen and differential rows do not compare raw slots. |
| Exact gas and identical arbitrary-world OOG thresholds | The port does not claim universal gas dominance. In the committed finite vector, all adequate boundaries are cheaper, all 33 historical GAS-family completion thresholds are nonpositive, and the independently pinned intrinsic exception set is empty. | Complete ordered resource vector, exact completion-threshold searches, separate scaling/OOG controls, independent digests, and threshold/architecture falsifiers. |
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
