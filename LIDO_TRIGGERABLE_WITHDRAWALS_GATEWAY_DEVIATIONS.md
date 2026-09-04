# Lido TriggerableWithdrawalsGateway deviation registry

> **Draft status:** every `machine-owned` token must be filled from the
> validated B1 lock or generated B2 manifest. The stable inventory has three
> accepted returndata differences and two repaired layout-era differences;
> the exact 51-cell gas ledger has no non-win. The family gate rejects marker
> drift, any unknown mismatch allowlist, or any future known difference that
> is not repaired or entered here.

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

<!-- LIDO-TWG-DEVIATION-POLICY {"schema":1,"closure":"complete","knownBehavioralRows":5,"acceptedBehavioralRows":3,"repairedBehavioralRows":2,"pendingBehavioralRows":0,"positiveGasRows":0,"unknownMismatchAllowlist":false} -->

## Behavioral deviations and dispositions

The five IDs are stable even if a row is repaired. Repair changes its status
and moves its text to past tense; it does not recycle the ID for a different
difference.

<!-- LIDO-TWG-DEVIATION {"id":"TWG-D01","status":"accepted","class":"returndata"} -->
### TWG-D01 — role-gate unauthorized payload

| Field | Record |
|---|---|
| Reference semantics | The pinned OpenZeppelin 4.4.1 `AccessControl` base rejects a missing role with dynamic `Error(string)` data containing the canonical account and role text. |
| Blanc semantics | The current Blanc runtime rejects with the four-byte selector of the no-argument signature `AccessControlUnauthorizedAccount()`. It does not encode the account or role and is not the later OpenZeppelin custom error `AccessControlUnauthorizedAccount(address,bytes32)`. |
| Observable consequence | Status and rollback agree, but returndata length and bytes differ for unauthorized `pauseFor`, `pauseUntil`, `resume`, `triggerFullWithdrawals`, `setExitRequestLimit`, `grantRole`, and `revokeRole`. Integrators that decode or display the reference reason observe different data. |
| Stance | **Accepted priced diagnostic cost.** The uniform four-byte failure keeps one compact, proof-oriented error-table convention at the cost of the reference's account/role diagnostics. The exact runtime and named gas ledger are strictly smaller/cheaper, but those wins do not erase this returndata difference. |
| Evidence | B1 derives the reference payloads and pins the exact Blanc four-byte payload. B2 rows `role-negative-grant, role-negative-revoke, role-negative-pause-for, role-negative-pause-until, role-negative-resume, role-negative-set-limit, role-negative-trigger` observe exactly the registered returndata mismatch; the machine summary is `seven exact unauthorized-role returndata rows; status, rollback, state, ETH, logs, and calls agree`. All seven action boundaries are present in the machine-owned resource vector, including the named `role-gate-unauthorized` row below. |

<!-- LIDO-TWG-DEVIATION {"id":"TWG-D02","status":"accepted","class":"returndata"} -->
### TWG-D02 — wrong-account `renounceRole` payload

| Field | Record |
|---|---|
| Reference semantics | `renounceRole(role, account)` with `account != msg.sender` reverts with dynamic `Error("AccessControl: can only renounce roles for self")` data. |
| Blanc semantics | The current Blanc runtime empty-reverts on that check. |
| Observable consequence | Status, rollback, and membership agree; returndata differs exactly on the wrong-account rejection. |
| Stance | **Accepted priced cost, not an improvement.** Empty revert follows the compact proof-oriented rejection convention but removes a useful source diagnostic. The choice is published as that local diagnostic cost, not as an aggregate code-size or gas improvement. |
| Evidence | B1 pins the exact reference `Error(string)` payload. B2 row `renounce-role-wrong-account` observes returndata as the only mismatch channel: both sides revert with identical rollback, membership projection, ETH, logs, and calls. The machine attribution is `wrong-account renounce action gas is pinned in the complete resource vector`; exact gas is in the ledger below. |

<!-- LIDO-TWG-DEVIATION {"id":"TWG-D03","status":"accepted","class":"returndata"} -->
### TWG-D03 — `getRoleMember` out-of-bounds payload

| Field | Record |
|---|---|
| Reference semantics | The per-role `EnumerableSet` indexes its backing array. An ordinal at or beyond the role's member count reaches Solidity's array-index-out-of-bounds panic, `Panic(0x32)`. |
| Blanc semantics | The direct per-role array checks its stored length and empty-reverts when the ordinal is out of range. |
| Observable consequence | Both calls fail without committed effects, but their returndata differs. This includes an empty role queried at index zero and a populated role queried at `count` or above. |
| Stance | **Accepted priced diagnostic cost, not an improvement.** Empty revert keeps the compact error-table convention but loses the standard Solidity panic payload. The row remains a strict gas win; the behavioral cost is returndata only. |
| Evidence | B2 row `get-role-member-oob` observes returndata as the only mismatch channel: reference `Panic(0x32)` digest `9bad752c2332f820f6c9ca0e71931cfb92d46fcc31990876e7df1b8735aa2e35`, Blanc empty-revert digest `cbf163e98f682a46701ff443b16283acbfcad88f59c6671f11b893dc1ee36aa1`; both sides revert with no committed effect. The machine attribution is `out-of-bounds getRoleMember action gas and exact two payload digests are pinned`. |

<!-- LIDO-TWG-DEVIATION {"id":"TWG-D04","status":"repaired","class":"enumeration-order"} -->
### TWG-D04 — role-member ordering after cross-role removal histories

| Field | Record |
|---|---|
| Reference semantics | Each role owns a separate `EnumerableSet`. Removing one member swap-pops the last member of that same role into the removed ordinal. |
| Blanc semantics | Blanc now owns direct per-role length, member, and one-based index storage and uses the same within-role swap-pop rule. |
| Observable consequence | **Repaired.** The former global-array implementation could return a different valid member at the same ordinal after cross-role removal. The current runtime returns the reference order. |
| Stance | The public ordinal was observable, so the earlier “orthogonal” disposition was not sufficient. The stable ID remains as historical evidence and a regression boundary. |
| Evidence | The causal B2 history `role-enumeration-cross-role-order` grants interleaved role records, removes a non-last role-A member, and observes `reference and Blanc role-A order [ACTOR_C, ACTOR_B] after the same cross-role removal history`; every compared channel now agrees. |

<!-- LIDO-TWG-DEVIATION {"id":"TWG-D05","status":"repaired","class":"collision-refusal"} -->
### TWG-D05 — flat role-key collision refusal

| Field | Record |
|---|---|
| Reference semantics | OpenZeppelin stores role membership in mapping-/set-derived keccak storage. It has no branch that treats two distinct `(role, account)` pairs as the same key under Blanc's projection. |
| Blanc semantics | Blanc now derives a nested-keccak membership slot from the complete role and canonical account. Distinct constructed pairs remain separated without a collision-refusal branch. |
| Observable consequence | **Repaired.** Both formerly colliding grants succeed independently; `hasRole`, per-role counts, ordering, and logs match the reference projection. |
| Stance | The earlier fail-loud collision policy still changed public status and authority observations, so it was replaced rather than waived. The stable ID remains as historical evidence and a regression boundary. |
| Evidence | The live causal row `role-flat-key-collision-refusal` and paired artifact mutant require `both formerly colliding grants succeed independently and subsequent hasRole observations remain separated`. Projection identity: `2cf7a3070c01f541165e2252ad1c5df14cd0f49fab27a73198a2f91e6b7fe0b5`. |

## Pending behavioral deviations

None. The stable inventory has three accepted rows, two repaired rows, and
zero rows awaiting disposition. The exact policy marker and all five row markers encode the
same counts. Any later discovered in-scope mismatch must be repaired or added
under a new stable ID; it may not enter an allowlist or be absorbed into a
nonclaim.

## Accepted low-level implementation differences

These freedoms do not authorize a difference in status, returndata, logical
state, ETH, logs, external calls, or their ordering unless a behavioral row
above explicitly records it.

<!-- LIDO-TWG-IMPLEMENTATION-DIFFERENCE {"id":"TWG-I01","class":"storage-layout"} -->
### TWG-I01 — raw storage layout and immutable embedding

| Field | Record |
|---|---|
| Reference | A common keccak-named pause word, a packed exit-limit struct at `TWR_LIMIT_POSITION`, OpenZeppelin mapping/set storage for roles, and a Solidity immutable locator. |
| Blanc | One tagged configuration region holds the pause projection and packed five-`uint32` limit word; nested-keccak membership plus direct per-role length/index/member slots hold roles; generated runtime parameters hold the locator. |
| Boundary | Logical pause, limit, membership, count, enumeration, and locator behavior are compared. Raw slots, storage roots/proofs, source-layout offsets, upgrade-in-place storage compatibility, and direct interpretation of one implementation's storage as the other's are not claimed. |
| Stance | Raw layout is an implementation freedom under `PORTING.md`; it does not excuse a public semantic difference. `TWG-D04` and `TWG-D05` record that the previous observable costs were repaired. |
| Evidence | B2 projection schema `2cf7a3070c01f541165e2252ad1c5df14cd0f49fab27a73198a2f91e6b7fe0b5`; exact runtime identity `6fdb5afdafc949df0677cea1e2f61f6363e21fd6348ff9843186fa8c68ca3c56`; reference lock `8e92a23746c47a9b065f6c042c98d9913785c40c0f27e0a1f82cfc37c0effc0f`. |

Other accepted low-level freedoms, subject to the same behavioral boundary:

- runtime/initcode bytes, code hash, dispatcher shape, internal table layout,
  instruction selection, and source organization;
- exact raw persistent-memory/transient-memory coordinates internal to a call;
- compiler control-flow structure and private helper decomposition; and
- exact arbitrary-world gas and access-list warming, while every cell in the
  exact named 51-cell ledger must remain a strict Blanc win.

## Code-size comparison

<!-- LIDO-TWG-CODE-SIZE {"referenceLock":"8e92a23746c47a9b065f6c042c98d9913785c40c0f27e0a1f82cfc37c0effc0f","artifactProgramCommit":"df9ce992b98b1eb784ab631be312cba4550ff61b","proofCertificateCommit":"35ba1e1b137529482180adccd44ae0da70417ac4","manifest":"30a62c2866e8a504aaece1b220622e16a774024b5aa6ab9f0d28bb38ba3de60c"} -->

All lengths are byte counts over the exact hex decoded by the named gates.
Negative delta means Blanc is smaller. The creation template has no direct
Solidity counterpart and is recorded without pretending otherwise.

| Artifact boundary | Reference bytes | Blanc bytes | Blanc − reference | Identity evidence |
|---|---:|---:|---:|---|
| Runtime | `8128` | `8094` | `-34` | reference `12c9d210f25202cf535622f93ba5237181512cc23970f2da08434f77e68d3a7b`; Blanc `6fdb5afdafc949df0677cea1e2f61f6363e21fd6348ff9843186fa8c68ca3c56` |
| Complete CREATE input for the compared parameter world | `10256` | `9966` | `-290` | reference `0e7dd55e589cf6bd38b2ebae7581ff169a354f9399087ecb6b8940f56bacc7e7`; Blanc `6342403216b7c9f9787d13a2f8ce1a98e4465b1d1955f0f1b1b72911c076b690` |
| Blanc parameterized creation template | not comparable | `9806` | not applicable | `0e1ee072fc51e1f93917004d7a0e67164bc7bc668087dd2f707f21f52e06f872` |

EIP-170/EIP-3860 headroom, where applicable:
`runtime 8094 bytes (16482 EIP-170 headroom); full CREATE 9966 bytes (39186 EIP-3860 headroom)`.

## Named-path gas comparison

<!-- LIDO-TWG-GAS-MEASUREMENT {"eelsCommit":"4198b9c5996713b268aed602739d5aa40e277694","manifest":"30a62c2866e8a504aaece1b220622e16a774024b5aa6ab9f0d28bb38ba3de60c","boundaryDefinition":"direct EELS Prague message gas used, computed as message gas minus output gas_left; constructor rows include code-deposit gas and exclude transaction intrinsic gas and refunds","rowCount":51,"positiveDeltaRows":0} -->

Every cell below comes from the same ordered machine-owned resource vector.
`Reference` and `Blanc` use one boundary definition, recorded verbatim as
`direct EELS Prague message gas used, computed as message gas minus output gas_left; constructor rows include code-deposit gas and exclude transaction intrinsic gas and refunds`. Every delta must be negative; sums,
averages, or an accepted disposition cannot hide a non-win.

| Stable path | Measured case boundary | Reference gas | Blanc gas | Delta | Manifest coordinate |
|---|---|---:|---:|---:|---|
| `constructor-success` | successful complete CREATE in `constructor-success` | `1744364` | `1735425` | `-8939` | `constructor-success#0:constructor` |
| `pauseFor-finite` | final `action` boundary in `pause-for-finite` | `26352` | `25598` | `-754` | `pause-for-finite#2:action` |
| `pauseFor-sentinel` | final `action` boundary in `pause-for-sentinel` | `26225` | `25567` | `-658` | `pause-for-sentinel#2:action` |
| `pauseUntil-finite` | final `action` boundary in `pause-until-finite` | `26392` | `25996` | `-396` | `pause-until-finite#2:action` |
| `pauseUntil-sentinel` | final `action` boundary in `pause-until-sentinel` | `26243` | `25943` | `-300` | `pause-until-sentinel#2:action` |
| `resume` | final `action` boundary in `resume-authorized` | `8538` | `8261` | `-277` | `resume-authorized#4:action` |
| `isPaused-resumed` | final `action` boundary in `view-is-paused-resumed` | `2385` | `2242` | `-143` | `view-is-paused-resumed#1:action` |
| `isPaused-paused` | final `action` boundary in `view-is-paused-paused` | `2385` | `2242` | `-143` | `view-is-paused-paused#3:action` |
| `grantRole-fresh` | final `action` boundary in `grant-role-fresh` | `96496` | `93807` | `-2689` | `grant-role-fresh#1:action` |
| `revokeRole-existing` | final `action` boundary in `revoke-role-existing` | `28381` | `25482` | `-2899` | `revoke-role-existing#2:action` |
| `renounceRole-self` | final `action` boundary in `renounce-role-self` | `23754` | `23009` | `-745` | `renounce-role-self#2:action` |
| `getRoleMember` | final `action` boundary in `get-role-member` | `4841` | `4614` | `-227` | `get-role-member#2:action` |
| `getRoleMemberCount` | final `action` boundary in `get-role-member-count` | `2614` | `2391` | `-223` | `get-role-member-count#2:action` |
| `setExitRequestLimit` | final `action` boundary in `set-limit-valid` | `11114` | `10091` | `-1023` | `set-limit-valid#2:action` |
| `getExitRequestLimitFullInfo-same-frame` | final `action` boundary in `get-limit-same-frame` | `3208` | `3044` | `-164` | `get-limit-same-frame#1:action` |
| `getExitRequestLimitFullInfo-refilled` | final `action` boundary in `get-limit-refilled` | `3567` | `3207` | `-360` | `get-limit-refilled#3:action` |
| `trigger-empty` | final `action` boundary in `trigger-empty` | `5398` | `5074` | `-324` | `trigger-empty#2:action` |
| `trigger-single-no-refund` | final `action` boundary in `trigger-single-exact-fee` | `233284` | `230117` | `-3167` | `trigger-single-exact-fee#2:action` |
| `trigger-single-explicit-refund` | final `action` boundary in `trigger-explicit-refund` | `267754` | `264488` | `-3266` | `trigger-explicit-refund#2:action` |
| `trigger-single-sender-refund` | final `action` boundary in `trigger-sender-refund` | `240258` | `236997` | `-3261` | `trigger-sender-refund#2:action` |
| `trigger-multiple` | final `action` boundary in `trigger-multiple` | `235133` | `231329` | `-3804` | `trigger-multiple#2:action` |
| `trigger-limit-exceeded` | final `action` boundary in `trigger-limit-exceeded` | `8215` | `7457` | `-758` | `trigger-limit-exceeded#2:action` |
| `role-gate-unauthorized` | final `action` boundary in `role-negative-pause-for` | `32304` | `2393` | `-29911` | `role-negative-pause-for#1:action` |
| `defaultAdminRole` | final `action` boundary in `view-default-admin-role` | `284` | `268` | `-16` | `view-default-admin-role#1:action` |
| `pauseInfinitely` | final `action` boundary in `view-pause-infinitely` | `309` | `291` | `-18` | `view-pause-infinitely#1:action` |
| `supportsInterface` | final `action` boundary in `view-supports-interface` | `412` | `303` | `-109` | `view-supports-interface#1:action` |
| `hasRole` | final `action` boundary in `view-has-role` | `2731` | `2450` | `-281` | `view-has-role#1:action` |
| `getResumeSinceTimestamp` | final `action` boundary in `view-resume-timestamp` | `2474` | `2413` | `-61` | `view-resume-timestamp#1:action` |
| `grantRole-duplicate` | final `action` boundary in `grant-role-duplicate` | `9810` | `5342` | `-4468` | `grant-role-duplicate#2:action` |
| `revokeRole-missing` | final `action` boundary in `revoke-role-missing` | `9889` | `5360` | `-4529` | `revoke-role-missing#1:action` |
| `renounceRole-wrong-account` | final `action` boundary in `renounce-role-wrong-account` | `543` | `401` | `-142` | `renounce-role-wrong-account#1:action` |
| `getRoleMember-oob` | final `action` boundary in `get-role-member-oob` | `2587` | `2385` | `-202` | `get-role-member-oob#1:action` |
| `role-enumeration-cross-role-order` | final `action` boundary in `role-enumeration-cross-role-order` | `4841` | `4614` | `-227` | `role-enumeration-cross-role-order#7:action` |
| `role-flat-key-collision-refusal` | final `action` boundary in `role-flat-key-collision-refusal` | `2731` | `2450` | `-281` | `role-flat-key-collision-refusal#3:action` |
| `pauseFor-when-paused` | final `action` boundary in `pause-for-when-paused` | `5000` | `4516` | `-484` | `pause-for-when-paused#3:action` |
| `pauseUntil-when-paused` | final `action` boundary in `pause-until-when-paused` | `5023` | `4890` | `-133` | `pause-until-when-paused#3:action` |
| `pauseFor-zero-duration` | final `action` boundary in `pause-zero-duration` | `5026` | `4540` | `-486` | `pause-zero-duration#2:action` |
| `pauseUntil-past` | final `action` boundary in `pause-until-past` | `5057` | `4916` | `-141` | `pause-until-past#2:action` |
| `resume-when-resumed` | final `action` boundary in `resume-when-resumed` | `4853` | `4624` | `-229` | `resume-when-resumed#2:action` |
| `setExitRequestLimit-max-too-large` | final `action` boundary in `set-limit-max-too-large` | `5503` | `2814` | `-2689` | `set-limit-max-too-large#2:action` |
| `setExitRequestLimit-frame-too-large` | final `action` boundary in `set-limit-frame-too-large` | `5529` | `2839` | `-2690` | `set-limit-frame-too-large#2:action` |
| `setExitRequestLimit-exits-above-max` | final `action` boundary in `set-limit-exits-above-max` | `5555` | `2867` | `-2688` | `set-limit-exits-above-max#2:action` |
| `setExitRequestLimit-zero-frame` | final `action` boundary in `set-limit-zero-frame` | `5572` | `2889` | `-2683` | `set-limit-zero-frame#2:action` |
| `trigger-insufficient-fee` | final `action` boundary in `trigger-insufficient-fee` | `18562` | `16440` | `-2122` | `trigger-insufficient-fee#2:action` |
| `trigger-paused` | final `action` boundary in `trigger-paused` | `5281` | `5009` | `-272` | `trigger-paused#4:action` |
| `trigger-zero-value` | final `action` boundary in `trigger-zero-value` | `5367` | `5052` | `-315` | `trigger-zero-value#2:action` |
| `trigger-locator-revert` | final `action` boundary in `trigger-locator-revert` | `15081` | `13391` | `-1690` | `trigger-locator-revert#2:action` |
| `trigger-fee-query-revert` | final `action` boundary in `trigger-fee-query-revert` | `18191` | `16290` | `-1901` | `trigger-fee-query-revert#2:action` |
| `trigger-vault-revert` | final `action` boundary in `trigger-vault-revert` | `27481` | `25353` | `-2128` | `trigger-vault-revert#2:action` |
| `trigger-router-revert` | final `action` boundary in `trigger-router-revert` | `142363` | `139284` | `-3079` | `trigger-router-revert#2:action` |
| `trigger-refund-revert` | final `action` boundary in `trigger-refund-revert` | `242729` | `239479` | `-3250` | `trigger-refund-revert#2:action` |

The full table is mechanically complete for all 47 positive final `action`
boundaries among the 63 public cases plus the positive successful constructor.
The two `isPaused` rows and representative unauthorized role-gate row remain as
three useful negative controls. Machine summary:
`24/24 census selectors each own at least one direct action boundary`.

### Positive-cost disposition registry

None — zero measured positive public-path deltas; ordered gas vector SHA-256 `4eaae83e6f0cb66241ded17661bf0f0114e1b2b775fabe2eb610ce1eaf12e8a9`.

There are no accepted positive-gas dispositions on this exact ledger. Every one of the 51 named constructor/public-path cells is a strict Blanc win; any nonnegative regeneration is a gate failure, not a row to waive.

## Explicit equivalence exclusions and nonclaims

These are boundaries, not deviation defenses:

- deployed-Solidity or mainnet-byte verification;
- bytecode, codehash, source, compiler-layout, raw-storage, storage-root, or
  storage-proof identity;
- exhaustive semantic equivalence or completeness of this registry;
- exact behavior for malformed/noncanonical input shapes not named inside the
  compatibility corpus;
- zero/unlimited exit-limit mode and partial-frame refill/consumption behavior;
- nested malformed dynamic ABI, empty/unknown/short dispatch, trailing
  calldata, and recognized-selector nonpayability;
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
