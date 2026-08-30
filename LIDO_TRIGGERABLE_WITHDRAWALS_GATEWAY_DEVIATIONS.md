# Lido TriggerableWithdrawalsGateway deviation registry

> **Draft status:** incomplete. Every `{{MACHINE:...}}` token must be filled
> from the validated B1 lock or generated B2 manifest, and every deviation
> marker with status `unresolved` must become either `accepted` with complete
> evidence and a reviewed stance or `repaired` with the former difference
> retained as historical evidence. The family gates must reject closure while
> either condition remains.

This is the per-contract registry required by [`PORTING.md`](PORTING.md) for
Blanc's port of Lido's `TriggerableWithdrawalsGateway`. A known observable
difference from the pinned reference that is neither repaired nor entered and
defended here is a defect. Passing a finite differential does not prove that no
other difference exists, and an opaque mismatch allowlist is prohibited: every
intentional mismatch must name one stable row below and its exact expected
channels.

The normative identities, public boundary, and finite coverage criterion are
in
[`LIDO_TRIGGERABLE_WITHDRAWALS_GATEWAY_COMPATIBILITY.md`](LIDO_TRIGGERABLE_WITHDRAWALS_GATEWAY_COMPATIBILITY.md).

<!-- LIDO-TWG-DEVIATION-POLICY {"schema":1,"closure":"incomplete","knownBehavioralRows":5,"acceptedBehavioralRows":0,"repairedBehavioralRows":0,"pendingBehavioralRows":5,"positiveGasRows":"{{MACHINE:B2_POSITIVE_GAS_ROW_COUNT}}","unknownMismatchAllowlist":false} -->

## Behavioral deviations and dispositions

The five IDs are stable even if a row is repaired. Repair changes its status
and moves its text to past tense; it does not recycle the ID for a different
difference.

<!-- LIDO-TWG-DEVIATION {"id":"TWG-D01","status":"unresolved","class":"returndata"} -->
### TWG-D01 — role-gate unauthorized payload

| Field | Record |
|---|---|
| Reference semantics | The pinned OpenZeppelin 4.4.1 `AccessControl` base rejects a missing role with dynamic `Error(string)` data containing the canonical account and role text. |
| Blanc semantics | The current Blanc runtime rejects with the four-byte selector of the no-argument signature `AccessControlUnauthorizedAccount()`. It does not encode the account or role and is not the later OpenZeppelin custom error `AccessControlUnauthorizedAccount(address,bytes32)`. |
| Observable consequence | Status and rollback agree, but returndata length and bytes differ for unauthorized `pauseFor`, `pauseUntil`, `resume`, `triggerFullWithdrawals`, `setExitRequestLimit`, `grantRole`, and `revokeRole`. Integrators that decode or display the reference reason observe different data. |
| Candidate stance | **Priced cost, not an improvement.** A fixed four-byte role failure keeps the proof-oriented runtime/error table compact, at the cost of worse diagnostics. Final acceptance requires exact size/gas evidence, corpus rows for all seven entries, and hostile-review agreement that an informed deployer could accept the trade. Otherwise repair it. |
| Required evidence | Reference payload derivation from B1; exact Blanc bytes; B2 row set `{{MACHINE:B2_D01_ROW_SET}}`; size attribution `{{MACHINE:B2_D01_SIZE_ATTRIBUTION}}`; hostile disposition pending independent review. |

<!-- LIDO-TWG-DEVIATION {"id":"TWG-D02","status":"unresolved","class":"returndata"} -->
### TWG-D02 — wrong-account `renounceRole` payload

| Field | Record |
|---|---|
| Reference semantics | `renounceRole(role, account)` with `account != msg.sender` reverts with dynamic `Error("AccessControl: can only renounce roles for self")` data. |
| Blanc semantics | The current Blanc runtime empty-reverts on that check. |
| Observable consequence | Status, rollback, and membership agree; returndata differs exactly on the wrong-account rejection. |
| Candidate stance | **Priced cost, not an improvement.** Empty revert is smaller and simpler to verify but removes a source diagnostic. Final acceptance requires named resource evidence and hostile review; otherwise repair it. |
| Required evidence | B1 exact reference payload; B2 row set `{{MACHINE:B2_D02_ROW_SET}}`; size/gas attribution `{{MACHINE:B2_D02_RESOURCE_ATTRIBUTION}}`; hostile disposition pending independent review. |

<!-- LIDO-TWG-DEVIATION {"id":"TWG-D03","status":"unresolved","class":"returndata"} -->
### TWG-D03 — `getRoleMember` out-of-bounds payload

| Field | Record |
|---|---|
| Reference semantics | The per-role `EnumerableSet` indexes its backing array. An ordinal at or beyond the role's member count reaches Solidity's array-index-out-of-bounds panic, `Panic(0x32)`. |
| Blanc semantics | The global filtered scan exhausts the role-record array and empty-reverts. |
| Observable consequence | Both calls fail without committed effects, but their returndata differs. This includes an empty role queried at index zero and a populated role queried at `count` or above. |
| Candidate stance | **Unresolved.** The candidate defense is the priced cost of one compact scan terminator; this row should be repaired unless measured size/proof benefit and hostile review justify losing the standard panic payload. |
| Required evidence | Reference and Blanc exact payload bytes; B2 boundary rows `{{MACHINE:B2_D03_ROW_SET}}`; resource attribution `{{MACHINE:B2_D03_RESOURCE_ATTRIBUTION}}`; hostile disposition pending independent review. |

<!-- LIDO-TWG-DEVIATION {"id":"TWG-D04","status":"unresolved","class":"enumeration-order"} -->
### TWG-D04 — role-member ordering after cross-role removal histories

| Field | Record |
|---|---|
| Reference semantics | Each role owns a separate `EnumerableSet`. Removing one member swap-pops the last member of that same role into the removed ordinal. |
| Blanc semantics | Blanc owns one global role/account array, filters it for `getRoleMember`, and swap-pops the last global record on removal. Membership and count are preserved, but the filtered per-role order can change differently when records of several roles are interleaved. |
| Observable consequence | After a suitable grant/revoke history, `hasRole` and `getRoleMemberCount` agree while `getRoleMember(role, i)` can return a different valid member at the same ordinal. A minimal discriminating family grants at least three members of the queried role with interleaved members of another role, then removes a non-last queried-role member. |
| Candidate stance | **Orthogonal to the gateway's job, if retained.** Enumeration membership and count are the intended interface; stable insertion order is not used by the gateway's pause/withdrawal job. The difference remains observable and therefore published rather than hidden as storage freedom. |
| Required evidence | A causal B2 history proving equal membership/count and different ordinal result, `{{MACHINE:B2_D04_ROW_SET}}`; exact expected orders `{{MACHINE:B2_D04_EXPECTED_ORDERS}}`; hostile disposition pending independent review. |

<!-- LIDO-TWG-DEVIATION {"id":"TWG-D05","status":"unresolved","class":"collision-refusal"} -->
### TWG-D05 — flat role-key collision refusal

| Field | Record |
|---|---|
| Reference semantics | OpenZeppelin stores role membership in mapping-/set-derived keccak storage. It has no branch that treats two distinct `(role, account)` pairs as the same key under Blanc's projection. |
| Blanc semantics | Blanc's lookup payload is the low 252 bits of `role XOR canonicalAccount`. Three tagged regions store the full role, canonical account, and one-based global index. A nonempty record whose full identity differs is refused rather than aliased; views return nonmembership instead of reading through it. |
| Observable consequence | In a colliding constructed state/history, an operation the reference admits can fail in Blanc, and `hasRole` can return false rather than attribute another pair's membership. No storage or role record is silently overwritten. |
| Candidate stance | **Priced design cost with fail-loud behavior.** The flat full-identity layout buys a compact, locally verifiable representation; refusing a collision is preferable to silently granting, revoking, or reading another pair's authority. This does not make the collision domain equivalent to Solidity's. |
| Required evidence | Explicit colliding pair construction and live refusal/nonalias control `{{MACHINE:B2_D05_ROW_SET}}`; projection identity `{{MACHINE:B2_D05_PROJECTION_SHA256}}`; resource attribution `{{MACHINE:B2_D05_RESOURCE_ATTRIBUTION}}`; hostile disposition pending independent review. |

## Pending behavioral deviations

At draft time, `TWG-D01` through `TWG-D05` are all pending final B2/B3
disposition. Closure requires this section to say exactly which rows remain
accepted and which were repaired, with no unresolved row and no unregistered
corpus mismatch.

Current draft result: zero accepted, zero repaired, five pending. The hostile
review must update this sentence and the policy marker together with the five
stable row markers.

## Accepted low-level implementation differences

These freedoms do not authorize a difference in status, returndata, logical
state, ETH, logs, external calls, or their ordering unless a behavioral row
above explicitly records it.

<!-- LIDO-TWG-IMPLEMENTATION-DIFFERENCE {"id":"TWG-I01","class":"storage-layout"} -->
### TWG-I01 — raw storage layout and immutable embedding

| Field | Record |
|---|---|
| Reference | A common keccak-named pause word, a packed exit-limit struct at `TWR_LIMIT_POSITION`, OpenZeppelin mapping/set storage for roles, and a Solidity immutable locator. |
| Blanc | One tagged configuration region holds the pause projection, five separate limit words, and global role-record length; full-identity flat lookup records and two global enumeration regions hold roles; generated runtime parameters hold the locator. |
| Boundary | Logical pause, limit, membership, count, enumeration, and locator behavior are compared. Raw slots, storage roots/proofs, source-layout offsets, upgrade-in-place storage compatibility, and direct interpretation of one implementation's storage as the other's are not claimed. |
| Stance | Raw layout is an implementation accident under `PORTING.md`. Blanc deliberately chooses the flat collision-refusing representation for proof locality and compactness; `TWG-D04` and `TWG-D05` separately publish the observable costs rather than laundering them into this freedom. |
| Evidence | B2 projection schema `{{MACHINE:B2_PROJECTION_SCHEMA_SHA256}}`; exact runtime identity `{{MACHINE:B2_BLANC_RUNTIME_SHA256}}`; reference lock `{{MACHINE:B1_REFERENCE_LOCK_SHA256}}`. |

Other accepted low-level freedoms, subject to the same behavioral boundary:

- runtime/initcode bytes, code hash, dispatcher shape, internal table layout,
  instruction selection, and source organization;
- exact raw persistent-memory/transient-memory coordinates internal to a call;
- compiler control-flow structure and private helper decomposition; and
- exact gas and access-list warming, except that every measured public-path
  increase is itself a behavioral deviation requiring a stable row.

## Code-size comparison

<!-- LIDO-TWG-CODE-SIZE {"referenceLock":"{{MACHINE:B1_REFERENCE_LOCK_SHA256}}","blancCommit":"{{MACHINE:B2_BLANC_COMMIT}}","manifest":"{{MACHINE:B2_MANIFEST_SHA256}}"} -->

All lengths are byte counts over the exact hex decoded by the named gates.
Negative delta means Blanc is smaller. The creation template has no direct
Solidity counterpart and is recorded without pretending otherwise.

| Artifact boundary | Reference bytes | Blanc bytes | Blanc − reference | Identity evidence |
|---|---:|---:|---:|---|
| Runtime | `{{MACHINE:B1_REFERENCE_RUNTIME_BYTES}}` | `{{MACHINE:B2_BLANC_RUNTIME_BYTES}}` | `{{MACHINE:B2_RUNTIME_BYTE_DELTA}}` | reference `{{MACHINE:B1_REFERENCE_RUNTIME_SHA256}}`; Blanc `{{MACHINE:B2_BLANC_RUNTIME_SHA256}}` |
| Complete CREATE input for the compared parameter world | `{{MACHINE:B1_REFERENCE_FULL_CREATE_BYTES}}` | `{{MACHINE:B2_BLANC_FULL_CREATE_BYTES}}` | `{{MACHINE:B2_FULL_CREATE_BYTE_DELTA}}` | reference `{{MACHINE:B1_REFERENCE_FULL_CREATE_SHA256}}`; Blanc `{{MACHINE:B2_BLANC_FULL_CREATE_SHA256}}` |
| Blanc parameterized creation template | not comparable | `{{MACHINE:B2_BLANC_CREATION_TEMPLATE_BYTES}}` | not applicable | `{{MACHINE:B2_BLANC_CREATION_TEMPLATE_SHA256}}` |

EIP-170/EIP-3860 headroom, where applicable:
`{{MACHINE:B2_CODE_SIZE_HEADROOM_SUMMARY}}`.

## Named-path gas comparison

<!-- LIDO-TWG-GAS-MEASUREMENT {"eelsCommit":"4198b9c5996713b268aed602739d5aa40e277694","manifest":"{{MACHINE:B2_MANIFEST_SHA256}}","boundaryDefinition":"{{MACHINE:B2_GAS_BOUNDARY_DEFINITION}}","rowCount":"{{MACHINE:B2_NAMED_GAS_ROW_COUNT}}","positiveDeltaRows":"{{MACHINE:B2_POSITIVE_GAS_ROW_COUNT}}"} -->

The gate must replace every cell below from the same ordered resource vector.
`Reference` and `Blanc` use one boundary definition, recorded verbatim as
`{{MACHINE:B2_GAS_BOUNDARY_DEFINITION}}`. Positive delta means Blanc is dearer
and requires repair or a separate stable `TWG-Gnn` deviation row; sums and
averages cannot hide it.

| Stable path | Compared world and outcome | Reference gas | Blanc gas | Delta | Manifest coordinate |
|---|---|---:|---:|---:|---|
| `constructor-success` | successful complete CREATE, official parameter world | `{{MACHINE:GAS_CONSTRUCTOR_SUCCESS_REF}}` | `{{MACHINE:GAS_CONSTRUCTOR_SUCCESS_BLANC}}` | `{{MACHINE:GAS_CONSTRUCTOR_SUCCESS_DELTA}}` | `{{MACHINE:GAS_CONSTRUCTOR_SUCCESS_COORD}}` |
| `pauseFor-finite` | authorized resumed → finite pause | `{{MACHINE:GAS_PAUSE_FOR_FINITE_REF}}` | `{{MACHINE:GAS_PAUSE_FOR_FINITE_BLANC}}` | `{{MACHINE:GAS_PAUSE_FOR_FINITE_DELTA}}` | `{{MACHINE:GAS_PAUSE_FOR_FINITE_COORD}}` |
| `pauseFor-sentinel` | authorized resumed → infinite sentinel | `{{MACHINE:GAS_PAUSE_FOR_SENTINEL_REF}}` | `{{MACHINE:GAS_PAUSE_FOR_SENTINEL_BLANC}}` | `{{MACHINE:GAS_PAUSE_FOR_SENTINEL_DELTA}}` | `{{MACHINE:GAS_PAUSE_FOR_SENTINEL_COORD}}` |
| `pauseUntil-finite` | authorized resumed → inclusive finite expiry | `{{MACHINE:GAS_PAUSE_UNTIL_FINITE_REF}}` | `{{MACHINE:GAS_PAUSE_UNTIL_FINITE_BLANC}}` | `{{MACHINE:GAS_PAUSE_UNTIL_FINITE_DELTA}}` | `{{MACHINE:GAS_PAUSE_UNTIL_FINITE_COORD}}` |
| `pauseUntil-sentinel` | authorized resumed → infinite sentinel | `{{MACHINE:GAS_PAUSE_UNTIL_SENTINEL_REF}}` | `{{MACHINE:GAS_PAUSE_UNTIL_SENTINEL_BLANC}}` | `{{MACHINE:GAS_PAUSE_UNTIL_SENTINEL_DELTA}}` | `{{MACHINE:GAS_PAUSE_UNTIL_SENTINEL_COORD}}` |
| `resume` | authorized paused → resumed | `{{MACHINE:GAS_RESUME_REF}}` | `{{MACHINE:GAS_RESUME_BLANC}}` | `{{MACHINE:GAS_RESUME_DELTA}}` | `{{MACHINE:GAS_RESUME_COORD}}` |
| `isPaused-resumed` | canonical false query | `{{MACHINE:GAS_IS_PAUSED_FALSE_REF}}` | `{{MACHINE:GAS_IS_PAUSED_FALSE_BLANC}}` | `{{MACHINE:GAS_IS_PAUSED_FALSE_DELTA}}` | `{{MACHINE:GAS_IS_PAUSED_FALSE_COORD}}` |
| `isPaused-paused` | canonical true query | `{{MACHINE:GAS_IS_PAUSED_TRUE_REF}}` | `{{MACHINE:GAS_IS_PAUSED_TRUE_BLANC}}` | `{{MACHINE:GAS_IS_PAUSED_TRUE_DELTA}}` | `{{MACHINE:GAS_IS_PAUSED_TRUE_COORD}}` |
| `grantRole-fresh` | authorized fresh membership | `{{MACHINE:GAS_GRANT_ROLE_REF}}` | `{{MACHINE:GAS_GRANT_ROLE_BLANC}}` | `{{MACHINE:GAS_GRANT_ROLE_DELTA}}` | `{{MACHINE:GAS_GRANT_ROLE_COORD}}` |
| `revokeRole-existing` | authorized existing membership | `{{MACHINE:GAS_REVOKE_ROLE_REF}}` | `{{MACHINE:GAS_REVOKE_ROLE_BLANC}}` | `{{MACHINE:GAS_REVOKE_ROLE_DELTA}}` | `{{MACHINE:GAS_REVOKE_ROLE_COORD}}` |
| `renounceRole-self` | self-renounce existing membership | `{{MACHINE:GAS_RENOUNCE_ROLE_REF}}` | `{{MACHINE:GAS_RENOUNCE_ROLE_BLANC}}` | `{{MACHINE:GAS_RENOUNCE_ROLE_DELTA}}` | `{{MACHINE:GAS_RENOUNCE_ROLE_COORD}}` |
| `getRoleMember` | successful populated-role ordinal | `{{MACHINE:GAS_GET_ROLE_MEMBER_REF}}` | `{{MACHINE:GAS_GET_ROLE_MEMBER_BLANC}}` | `{{MACHINE:GAS_GET_ROLE_MEMBER_DELTA}}` | `{{MACHINE:GAS_GET_ROLE_MEMBER_COORD}}` |
| `getRoleMemberCount` | populated role after history | `{{MACHINE:GAS_GET_ROLE_MEMBER_COUNT_REF}}` | `{{MACHINE:GAS_GET_ROLE_MEMBER_COUNT_BLANC}}` | `{{MACHINE:GAS_GET_ROLE_MEMBER_COUNT_DELTA}}` | `{{MACHINE:GAS_GET_ROLE_MEMBER_COUNT_COORD}}` |
| `setExitRequestLimit` | authorized configuration update | `{{MACHINE:GAS_SET_LIMIT_REF}}` | `{{MACHINE:GAS_SET_LIMIT_BLANC}}` | `{{MACHINE:GAS_SET_LIMIT_DELTA}}` | `{{MACHINE:GAS_SET_LIMIT_COORD}}` |
| `getExitRequestLimitFullInfo-same-frame` | no whole-frame refill | `{{MACHINE:GAS_GET_LIMIT_SAME_FRAME_REF}}` | `{{MACHINE:GAS_GET_LIMIT_SAME_FRAME_BLANC}}` | `{{MACHINE:GAS_GET_LIMIT_SAME_FRAME_DELTA}}` | `{{MACHINE:GAS_GET_LIMIT_SAME_FRAME_COORD}}` |
| `getExitRequestLimitFullInfo-refilled` | elapsed whole-frame refill/cap | `{{MACHINE:GAS_GET_LIMIT_REFILLED_REF}}` | `{{MACHINE:GAS_GET_LIMIT_REFILLED_BLANC}}` | `{{MACHINE:GAS_GET_LIMIT_REFILLED_DELTA}}` | `{{MACHINE:GAS_GET_LIMIT_REFILLED_COORD}}` |
| `trigger-empty` | successful empty validator array | `{{MACHINE:GAS_TRIGGER_EMPTY_REF}}` | `{{MACHINE:GAS_TRIGGER_EMPTY_BLANC}}` | `{{MACHINE:GAS_TRIGGER_EMPTY_DELTA}}` | `{{MACHINE:GAS_TRIGGER_EMPTY_COORD}}` |
| `trigger-single-no-refund` | one validator, exact fee | `{{MACHINE:GAS_TRIGGER_SINGLE_EXACT_REF}}` | `{{MACHINE:GAS_TRIGGER_SINGLE_EXACT_BLANC}}` | `{{MACHINE:GAS_TRIGGER_SINGLE_EXACT_DELTA}}` | `{{MACHINE:GAS_TRIGGER_SINGLE_EXACT_COORD}}` |
| `trigger-single-explicit-refund` | one validator, excess to named recipient | `{{MACHINE:GAS_TRIGGER_EXPLICIT_REFUND_REF}}` | `{{MACHINE:GAS_TRIGGER_EXPLICIT_REFUND_BLANC}}` | `{{MACHINE:GAS_TRIGGER_EXPLICIT_REFUND_DELTA}}` | `{{MACHINE:GAS_TRIGGER_EXPLICIT_REFUND_COORD}}` |
| `trigger-single-sender-refund` | one validator, zero recipient falls back to sender | `{{MACHINE:GAS_TRIGGER_SENDER_REFUND_REF}}` | `{{MACHINE:GAS_TRIGGER_SENDER_REFUND_BLANC}}` | `{{MACHINE:GAS_TRIGGER_SENDER_REFUND_DELTA}}` | `{{MACHINE:GAS_TRIGGER_SENDER_REFUND_COORD}}` |
| `trigger-multiple` | multi-validator fee/encoding/router path | `{{MACHINE:GAS_TRIGGER_MULTIPLE_REF}}` | `{{MACHINE:GAS_TRIGGER_MULTIPLE_BLANC}}` | `{{MACHINE:GAS_TRIGGER_MULTIPLE_DELTA}}` | `{{MACHINE:GAS_TRIGGER_MULTIPLE_COORD}}` |
| `trigger-limit-exceeded` | authorized resumed quota rejection | `{{MACHINE:GAS_TRIGGER_LIMIT_REF}}` | `{{MACHINE:GAS_TRIGGER_LIMIT_BLANC}}` | `{{MACHINE:GAS_TRIGGER_LIMIT_DELTA}}` | `{{MACHINE:GAS_TRIGGER_LIMIT_COORD}}` |
| `role-gate-unauthorized` | representative `TWG-D01` failure | `{{MACHINE:GAS_ROLE_UNAUTHORIZED_REF}}` | `{{MACHINE:GAS_ROLE_UNAUTHORIZED_BLANC}}` | `{{MACHINE:GAS_ROLE_UNAUTHORIZED_DELTA}}` | `{{MACHINE:GAS_ROLE_UNAUTHORIZED_COORD}}` |

Every remaining selector also has at least one measured adequate boundary in
the complete vector. Machine summary:
`{{MACHINE:B2_PER_SELECTOR_RESOURCE_COVERAGE_SUMMARY}}`.

### Positive-delta registry

`{{MACHINE:B2_POSITIVE_GAS_ROWS_TABLE}}`

At closure this placeholder is replaced either by `None — zero measured
positive public-path deltas` with the vector digest, or by one table row per
positive coordinate with stable IDs `TWG-G01`, `TWG-G02`, …, an exact delta,
defense, and evidence. Aggregate code-size or gas savings are never a stance
for an individual dearer path.

## Explicit equivalence exclusions and nonclaims

These are boundaries, not deviation defenses:

- deployed-Solidity or mainnet-byte verification;
- bytecode, codehash, source, compiler-layout, raw-storage, storage-root, or
  storage-proof identity;
- exhaustive semantic equivalence or completeness of this registry;
- exact behavior for malformed/noncanonical input shapes not named inside the
  compatibility corpus;
- exact arbitrary-world gas, access lists, callback-observed `gasleft()`, OOG
  thresholds, or universal gas dominance;
- proxy/delegatecall/library use;
- arbitrary deployment shapes, CREATE2/factory/proxy deployment, transaction
  signing, propagation, inclusion, finality, or persistence of the B1 mainnet
  snapshot;
- arbitrary dependency behavior, or a port/proof of the locator, withdrawal
  vault, or staking router;
- liveness of pause, resume, trigger, refund, or any external dependency;
- the future CircuitBreaker-plus-TWG entry-3 composition theorem; and
- verification of mainnet role ownership, pause state, quota state, or
  operational governance.

No exclusion authorizes a known in-scope mismatch. If B2 discovers one, it is
repaired or receives its own stable row before the port claim is made.

## Matched sentinel behavior is not a deviation

Both artifacts must agree that `pauseFor(2^256 - 1)` stores the infinite
sentinel rather than wrapping `timestamp + duration`, and that
`pauseUntil(2^256 - 1)` stores the same sentinel rather than adding one. The
shared `PinnedPauseTarget` amendment exists to state that family behavior
faithfully. The sentinel is part of the compatibility corpus and may not be
reclassified as an exclusion, a hypothesis exemption, or a deviation.
