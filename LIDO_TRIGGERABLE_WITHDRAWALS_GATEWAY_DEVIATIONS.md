# Lido TriggerableWithdrawalsGateway deviation registry

> **Published evidence status:** the registry is synchronized to the validated
> B1 lock and generated B2 manifest. All five known behavioral differences are
> accepted and defended below; all 48 positive named-path gas deltas are
> published as measured priced costs. The family gate rejects marker drift,
> any unknown mismatch allowlist, or any future known difference that is not
> repaired or entered here.

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

<!-- LIDO-TWG-DEVIATION-POLICY {"schema":1,"closure":"complete","knownBehavioralRows":5,"acceptedBehavioralRows":5,"repairedBehavioralRows":0,"pendingBehavioralRows":0,"positiveGasRows":48,"unknownMismatchAllowlist":false} -->

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
| Stance | **Accepted priced cost, not an improvement.** The uniform four-byte failure keeps one compact, proof-oriented error-table convention at the cost of the reference's account/role diagnostics. The complete port is larger than the reference, so this is not defended as an aggregate size win; it is the declared local cost of the simpler verifiable error representation. |
| Evidence | B1 derives the reference payloads and pins the exact Blanc four-byte payload. B2 rows `role-negative-grant, role-negative-revoke, role-negative-pause-for, role-negative-pause-until, role-negative-resume, role-negative-set-limit, role-negative-trigger` observe exactly the registered returndata mismatch; the machine summary is `seven exact unauthorized-role returndata rows; status, rollback, state, ETH, logs, and calls agree`. All seven action boundaries are present in the 186-boundary resource vector; the named `role-gate-unauthorized` row records reference `32304`, Blanc `2270`, delta `-30034` at `role-negative-pause-for#1:action`. |

<!-- LIDO-TWG-DEVIATION {"id":"TWG-D02","status":"accepted","class":"returndata"} -->
### TWG-D02 — wrong-account `renounceRole` payload

| Field | Record |
|---|---|
| Reference semantics | `renounceRole(role, account)` with `account != msg.sender` reverts with dynamic `Error("AccessControl: can only renounce roles for self")` data. |
| Blanc semantics | The current Blanc runtime empty-reverts on that check. |
| Observable consequence | Status, rollback, and membership agree; returndata differs exactly on the wrong-account rejection. |
| Stance | **Accepted priced cost, not an improvement.** Empty revert follows the compact proof-oriented rejection convention but removes a useful source diagnostic. The choice is published as that local diagnostic cost, not as an aggregate code-size or gas improvement. |
| Evidence | B1 pins the exact reference `Error(string)` payload. B2 row `renounce-role-wrong-account` observes returndata as the only mismatch channel: both sides revert with identical rollback, membership projection, ETH, logs, and calls. The machine attribution is `wrong-account renounce action gas is pinned in the complete resource vector`: reference `543`, Blanc `621`. |

<!-- LIDO-TWG-DEVIATION {"id":"TWG-D03","status":"accepted","class":"returndata"} -->
### TWG-D03 — `getRoleMember` out-of-bounds payload

| Field | Record |
|---|---|
| Reference semantics | The per-role `EnumerableSet` indexes its backing array. An ordinal at or beyond the role's member count reaches Solidity's array-index-out-of-bounds panic, `Panic(0x32)`. |
| Blanc semantics | The global filtered scan exhausts the role-record array and empty-reverts. |
| Observable consequence | Both calls fail without committed effects, but their returndata differs. This includes an empty role queried at index zero and a populated role queried at `count` or above. |
| Stance | **Accepted priced cost, not an improvement.** Empty revert is the terminal result of the same compact filtered scan used for enumeration. It loses the standard Solidity panic diagnostic and costs more on the measured row; the defense is proof locality and one scan discipline, not size or gas superiority. |
| Evidence | B2 row `get-role-member-oob` observes returndata as the only mismatch channel: reference `Panic(0x32)` digest `9bad752c2332f820f6c9ca0e71931cfb92d46fcc31990876e7df1b8735aa2e35`, Blanc empty-revert digest `cbf163e98f682a46701ff443b16283acbfcad88f59c6671f11b893dc1ee36aa1`; both sides revert with no committed effect. The machine attribution is `out-of-bounds getRoleMember action gas and exact two payload digests are pinned`: reference `2587`, Blanc `5069`. |

<!-- LIDO-TWG-DEVIATION {"id":"TWG-D04","status":"accepted","class":"enumeration-order"} -->
### TWG-D04 — role-member ordering after cross-role removal histories

| Field | Record |
|---|---|
| Reference semantics | Each role owns a separate `EnumerableSet`. Removing one member swap-pops the last member of that same role into the removed ordinal. |
| Blanc semantics | Blanc owns one global role/account array, filters it for `getRoleMember`, and swap-pops the last global record on removal. Membership and count are preserved, but the filtered per-role order can change differently when records of several roles are interleaved. |
| Observable consequence | After a suitable grant/revoke history, `hasRole` and `getRoleMemberCount` agree while `getRoleMember(role, i)` can return a different valid member at the same ordinal. A minimal discriminating family grants at least three members of the queried role with interleaved members of another role, then removes a non-last queried-role member. |
| Stance | **Accepted as orthogonal to the gateway's job.** Membership, administration, and count remain the AccessControl interface used by the pause/withdrawal job; stable ordinal order after cross-role removal is not part of that job. Because ordinal results are nevertheless public and observable, the difference is registered rather than hidden as storage freedom. |
| Evidence | The causal B2 history `role-enumeration-cross-role-order` grants interleaved role records, removes a non-last role-A member, and observes equal membership/count with exact divergent orders: `reference role-A order [ACTOR_C, ACTOR_B]; Blanc filtered global order [ACTOR_B, ACTOR_C]`. The manifest limits expected mismatches to returndata and the ordered logical-state projection; status, ETH, logs, and calls agree. |

<!-- LIDO-TWG-DEVIATION {"id":"TWG-D05","status":"accepted","class":"collision-refusal"} -->
### TWG-D05 — flat role-key collision refusal

| Field | Record |
|---|---|
| Reference semantics | OpenZeppelin stores role membership in mapping-/set-derived keccak storage. It has no branch that treats two distinct `(role, account)` pairs as the same key under Blanc's projection. |
| Blanc semantics | Blanc's lookup payload is the low 252 bits of `role XOR canonicalAccount`. Three tagged regions store the full role, canonical account, and one-based global index. A nonempty record whose full identity differs is refused rather than aliased; views return nonmembership instead of reading through it. |
| Observable consequence | In a colliding constructed state/history, an operation the reference admits can fail in Blanc, and `hasRole` can return false rather than attribute another pair's membership. No storage or role record is silently overwritten. |
| Stance | **Accepted priced design cost with fail-loud behavior.** The flat full-identity layout buys proof locality and explicit identity checks; refusing a collision is preferable to silently granting, revoking, or reading another pair's authority. The collision-domain incompatibility is real and published, and is not defended as overall size or gas superiority. |
| Evidence | The live causal control `role-flat-key-collision-refusal` constructs the colliding identities, admits the first grant, rejects the second rather than aliasing it, and makes the subsequent `hasRole` return nonmembership. Its expected mismatch channels are exactly status, returndata, logical state, and logs. The projection identity is `d44df671ee050ddbf29add52fb66feecb374479da348819ac5f5cc58e5da4300`; machine attribution states `colliding second grant and subsequent hasRole boundaries are pinned`. |

## Pending behavioral deviations

None. The stable inventory has five accepted rows, zero repaired rows, and
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
| Blanc | One tagged configuration region holds the pause projection, five separate limit words, and global role-record length; full-identity flat lookup records and two global enumeration regions hold roles; generated runtime parameters hold the locator. |
| Boundary | Logical pause, limit, membership, count, enumeration, and locator behavior are compared. Raw slots, storage roots/proofs, source-layout offsets, upgrade-in-place storage compatibility, and direct interpretation of one implementation's storage as the other's are not claimed. |
| Stance | Raw layout is an implementation accident under `PORTING.md`. Blanc deliberately chooses the flat collision-refusing representation for proof locality and compactness; `TWG-D04` and `TWG-D05` separately publish the observable costs rather than laundering them into this freedom. |
| Evidence | B2 projection schema `d44df671ee050ddbf29add52fb66feecb374479da348819ac5f5cc58e5da4300`; exact runtime identity `2a4d45a407f79c896735072ba7f825927a857ec93f4c9c9abeff3e7905ebdb08`; reference lock `8e92a23746c47a9b065f6c042c98d9913785c40c0f27e0a1f82cfc37c0effc0f`. |

Other accepted low-level freedoms, subject to the same behavioral boundary:

- runtime/initcode bytes, code hash, dispatcher shape, internal table layout,
  instruction selection, and source organization;
- exact raw persistent-memory/transient-memory coordinates internal to a call;
- compiler control-flow structure and private helper decomposition; and
- exact gas and access-list warming, except that every measured positive
  public final-action cost requires its own accepted gas-cost disposition.

## Code-size comparison

<!-- LIDO-TWG-CODE-SIZE {"referenceLock":"8e92a23746c47a9b065f6c042c98d9913785c40c0f27e0a1f82cfc37c0effc0f","artifactProgramCommit":"35a196fd50192aa269d6cb07699ea0910ad3c468","proofCertificateCommit":"a0e04e7a69558b8744ced81ea4a3defdfc478d36","manifest":"4dea3481b12f12a751af1bdae602a8e5d6d7055f6359795fdd89950b3e0ae4d4"} -->

All lengths are byte counts over the exact hex decoded by the named gates.
Negative delta means Blanc is smaller. The creation template has no direct
Solidity counterpart and is recorded without pretending otherwise.

| Artifact boundary | Reference bytes | Blanc bytes | Blanc − reference | Identity evidence |
|---|---:|---:|---:|---|
| Runtime | `8128` | `15948` | `7820` | reference `12c9d210f25202cf535622f93ba5237181512cc23970f2da08434f77e68d3a7b`; Blanc `2a4d45a407f79c896735072ba7f825927a857ec93f4c9c9abeff3e7905ebdb08` |
| Complete CREATE input for the compared parameter world | `10256` | `18136` | `7880` | reference `0e7dd55e589cf6bd38b2ebae7581ff169a354f9399087ecb6b8940f56bacc7e7`; Blanc `8091507f8753791e74a3ba7704436dac4bc7db3fcbf973a97b5296934432347a` |
| Blanc parameterized creation template | not comparable | `17976` | not applicable | `1c7a59c47cb97dbd8da1ccd02ed2913d553d18e6f353c640b308ce47b638eeb1` |

EIP-170/EIP-3860 headroom, where applicable:
`runtime 15948 bytes (8628 EIP-170 headroom); full CREATE 18136 bytes (31016 EIP-3860 headroom)`.

## Named-path gas comparison

<!-- LIDO-TWG-GAS-MEASUREMENT {"eelsCommit":"4198b9c5996713b268aed602739d5aa40e277694","manifest":"4dea3481b12f12a751af1bdae602a8e5d6d7055f6359795fdd89950b3e0ae4d4","boundaryDefinition":"direct EELS Prague message gas used, computed as message gas minus output gas_left; constructor rows include code-deposit gas and exclude transaction intrinsic gas and refunds","rowCount":51,"positiveDeltaRows":48} -->

Every cell below comes from the same ordered 186-boundary resource vector.
`Reference` and `Blanc` use one boundary definition, recorded verbatim as
`direct EELS Prague message gas used, computed as message gas minus output gas_left; constructor rows include code-deposit gas and exclude transaction intrinsic gas and refunds`. Positive delta means Blanc is dearer and owns
an accepted, substantive gas-cost disposition below; sums and averages do not
hide any positive public final-action cost. These cost rows do not add
behavioral deviations beyond `TWG-D01` through `TWG-D05`.

| Stable path | Measured case boundary | Reference gas | Blanc gas | Delta | Manifest coordinate |
|---|---|---:|---:|---:|---|
| `constructor-success` | successful complete CREATE in `constructor-success` | `1744364` | `3400489` | `1656125` | `constructor-success#0:constructor` |
| `pauseFor-finite` | final `action` boundary in `pause-for-finite` | `26352` | `29772` | `3420` | `pause-for-finite#2:action` |
| `pauseFor-sentinel` | final `action` boundary in `pause-for-sentinel` | `26225` | `29741` | `3516` | `pause-for-sentinel#2:action` |
| `pauseUntil-finite` | final `action` boundary in `pause-until-finite` | `26392` | `30019` | `3627` | `pause-until-finite#2:action` |
| `pauseUntil-sentinel` | final `action` boundary in `pause-until-sentinel` | `26243` | `29963` | `3720` | `pause-until-sentinel#2:action` |
| `resume` | final `action` boundary in `resume-authorized` | `8538` | `12498` | `3960` | `resume-authorized#4:action` |
| `isPaused-resumed` | final `action` boundary in `view-is-paused-resumed` | `2385` | `2220` | `-165` | `view-is-paused-resumed#1:action` |
| `isPaused-paused` | final `action` boundary in `view-is-paused-paused` | `2385` | `2220` | `-165` | `view-is-paused-paused#3:action` |
| `grantRole-fresh` | final `action` boundary in `grant-role-fresh` | `96496` | `124650` | `28154` | `grant-role-fresh#1:action` |
| `revokeRole-existing` | final `action` boundary in `revoke-role-existing` | `28381` | `39316` | `10935` | `revoke-role-existing#2:action` |
| `renounceRole-self` | final `action` boundary in `renounce-role-self` | `23754` | `32928` | `9174` | `renounce-role-self#2:action` |
| `getRoleMember` | final `action` boundary in `get-role-member` | `4841` | `9363` | `4522` | `get-role-member#2:action` |
| `getRoleMemberCount` | final `action` boundary in `get-role-member-count` | `2614` | `7400` | `4786` | `get-role-member-count#2:action` |
| `setExitRequestLimit` | final `action` boundary in `set-limit-valid` | `11114` | `31141` | `20027` | `set-limit-valid#2:action` |
| `getExitRequestLimitFullInfo-same-frame` | final `action` boundary in `get-limit-same-frame` | `3208` | `11470` | `8262` | `get-limit-same-frame#1:action` |
| `getExitRequestLimitFullInfo-refilled` | final `action` boundary in `get-limit-refilled` | `3567` | `11633` | `8066` | `get-limit-refilled#3:action` |
| `trigger-empty` | final `action` boundary in `trigger-empty` | `5398` | `9164` | `3766` | `trigger-empty#2:action` |
| `trigger-single-no-refund` | final `action` boundary in `trigger-single-exact-fee` | `233284` | `242996` | `9712` | `trigger-single-exact-fee#2:action` |
| `trigger-single-explicit-refund` | final `action` boundary in `trigger-explicit-refund` | `267754` | `277367` | `9613` | `trigger-explicit-refund#2:action` |
| `trigger-single-sender-refund` | final `action` boundary in `trigger-sender-refund` | `240258` | `249876` | `9618` | `trigger-sender-refund#2:action` |
| `trigger-multiple` | final `action` boundary in `trigger-multiple` | `235133` | `244208` | `9075` | `trigger-multiple#2:action` |
| `trigger-limit-exceeded` | final `action` boundary in `trigger-limit-exceeded` | `8215` | `19907` | `11692` | `trigger-limit-exceeded#2:action` |
| `role-gate-unauthorized` | final `action` boundary in `role-negative-pause-for` | `32304` | `2270` | `-30034` | `role-negative-pause-for#1:action` |
| `defaultAdminRole` | final `action` boundary in `view-default-admin-role` | `284` | `422` | `138` | `view-default-admin-role#1:action` |
| `pauseInfinitely` | final `action` boundary in `view-pause-infinitely` | `309` | `379` | `70` | `view-pause-infinitely#1:action` |
| `supportsInterface` | final `action` boundary in `view-supports-interface` | `412` | `560` | `148` | `view-supports-interface#1:action` |
| `hasRole` | final `action` boundary in `view-has-role` | `2731` | `6953` | `4222` | `view-has-role#1:action` |
| `getResumeSinceTimestamp` | final `action` boundary in `view-resume-timestamp` | `2474` | `2501` | `27` | `view-resume-timestamp#1:action` |
| `grantRole-duplicate` | final `action` boundary in `grant-role-duplicate` | `9810` | `13465` | `3655` | `grant-role-duplicate#2:action` |
| `revokeRole-missing` | final `action` boundary in `revoke-role-missing` | `9889` | `11311` | `1422` | `revoke-role-missing#1:action` |
| `renounceRole-wrong-account` | final `action` boundary in `renounce-role-wrong-account` | `543` | `621` | `78` | `renounce-role-wrong-account#1:action` |
| `getRoleMember-oob` | final `action` boundary in `get-role-member-oob` | `2587` | `5069` | `2482` | `get-role-member-oob#1:action` |
| `role-enumeration-cross-role-order` | final `action` boundary in `role-enumeration-cross-role-order` | `4841` | `11658` | `6817` | `role-enumeration-cross-role-order#7:action` |
| `role-flat-key-collision-refusal` | final `action` boundary in `role-flat-key-collision-refusal` | `2731` | `6953` | `4222` | `role-flat-key-collision-refusal#3:action` |
| `pauseFor-when-paused` | final `action` boundary in `pause-for-when-paused` | `5000` | `8690` | `3690` | `pause-for-when-paused#3:action` |
| `pauseUntil-when-paused` | final `action` boundary in `pause-until-when-paused` | `5023` | `8910` | `3887` | `pause-until-when-paused#3:action` |
| `pauseFor-zero-duration` | final `action` boundary in `pause-zero-duration` | `5026` | `8714` | `3688` | `pause-zero-duration#2:action` |
| `pauseUntil-past` | final `action` boundary in `pause-until-past` | `5057` | `8936` | `3879` | `pause-until-past#2:action` |
| `resume-when-resumed` | final `action` boundary in `resume-when-resumed` | `4853` | `8864` | `4011` | `resume-when-resumed#2:action` |
| `setExitRequestLimit-max-too-large` | final `action` boundary in `set-limit-max-too-large` | `5503` | `6834` | `1331` | `set-limit-max-too-large#2:action` |
| `setExitRequestLimit-frame-too-large` | final `action` boundary in `set-limit-frame-too-large` | `5529` | `6859` | `1330` | `set-limit-frame-too-large#2:action` |
| `setExitRequestLimit-exits-above-max` | final `action` boundary in `set-limit-exits-above-max` | `5555` | `6887` | `1332` | `set-limit-exits-above-max#2:action` |
| `setExitRequestLimit-zero-frame` | final `action` boundary in `set-limit-zero-frame` | `5572` | `6909` | `1337` | `set-limit-zero-frame#2:action` |
| `trigger-insufficient-fee` | final `action` boundary in `trigger-insufficient-fee` | `18562` | `29239` | `10677` | `trigger-insufficient-fee#2:action` |
| `trigger-paused` | final `action` boundary in `trigger-paused` | `5281` | `9099` | `3818` | `trigger-paused#4:action` |
| `trigger-zero-value` | final `action` boundary in `trigger-zero-value` | `5367` | `9142` | `3775` | `trigger-zero-value#2:action` |
| `trigger-locator-revert` | final `action` boundary in `trigger-locator-revert` | `15081` | `26190` | `11109` | `trigger-locator-revert#2:action` |
| `trigger-fee-query-revert` | final `action` boundary in `trigger-fee-query-revert` | `18191` | `29089` | `10898` | `trigger-fee-query-revert#2:action` |
| `trigger-vault-revert` | final `action` boundary in `trigger-vault-revert` | `27481` | `38232` | `10751` | `trigger-vault-revert#2:action` |
| `trigger-router-revert` | final `action` boundary in `trigger-router-revert` | `142363` | `152163` | `9800` | `trigger-router-revert#2:action` |
| `trigger-refund-revert` | final `action` boundary in `trigger-refund-revert` | `242729` | `252358` | `9629` | `trigger-refund-revert#2:action` |

The full table is mechanically complete for all 47 positive final `action`
boundaries among the 63 public cases plus the positive successful constructor.
The two `isPaused` rows and representative unauthorized role-gate row remain as
three useful negative controls. Machine summary:
`24/24 census selectors each own at least one direct action boundary`.

### Positive-cost disposition registry

<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G01","gasKey":"CONSTRUCTOR_SUCCESS","path":"constructor-success","delta":1656125,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G02","gasKey":"PAUSE_FOR_FINITE","path":"pauseFor-finite","delta":3420,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G03","gasKey":"PAUSE_FOR_SENTINEL","path":"pauseFor-sentinel","delta":3516,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G04","gasKey":"PAUSE_UNTIL_FINITE","path":"pauseUntil-finite","delta":3627,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G05","gasKey":"PAUSE_UNTIL_SENTINEL","path":"pauseUntil-sentinel","delta":3720,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G06","gasKey":"RESUME","path":"resume","delta":3960,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G07","gasKey":"GRANT_ROLE","path":"grantRole-fresh","delta":28154,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G08","gasKey":"REVOKE_ROLE","path":"revokeRole-existing","delta":10935,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G09","gasKey":"RENOUNCE_ROLE","path":"renounceRole-self","delta":9174,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G10","gasKey":"GET_ROLE_MEMBER","path":"getRoleMember","delta":4522,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G11","gasKey":"GET_ROLE_MEMBER_COUNT","path":"getRoleMemberCount","delta":4786,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G12","gasKey":"SET_LIMIT","path":"setExitRequestLimit","delta":20027,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G13","gasKey":"GET_LIMIT_SAME_FRAME","path":"getExitRequestLimitFullInfo-same-frame","delta":8262,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G14","gasKey":"GET_LIMIT_REFILLED","path":"getExitRequestLimitFullInfo-refilled","delta":8066,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G15","gasKey":"TRIGGER_EMPTY","path":"trigger-empty","delta":3766,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G16","gasKey":"TRIGGER_SINGLE_EXACT","path":"trigger-single-no-refund","delta":9712,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G17","gasKey":"TRIGGER_EXPLICIT_REFUND","path":"trigger-single-explicit-refund","delta":9613,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G18","gasKey":"TRIGGER_SENDER_REFUND","path":"trigger-single-sender-refund","delta":9618,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G19","gasKey":"TRIGGER_MULTIPLE","path":"trigger-multiple","delta":9075,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G20","gasKey":"TRIGGER_LIMIT","path":"trigger-limit-exceeded","delta":11692,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G21","gasKey":"DEFAULT_ADMIN_ROLE_VIEW","path":"defaultAdminRole","delta":138,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G22","gasKey":"PAUSE_INFINITELY_VIEW","path":"pauseInfinitely","delta":70,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G23","gasKey":"SUPPORTS_INTERFACE","path":"supportsInterface","delta":148,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G24","gasKey":"HAS_ROLE","path":"hasRole","delta":4222,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G25","gasKey":"GET_RESUME_TIMESTAMP","path":"getResumeSinceTimestamp","delta":27,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G26","gasKey":"GRANT_ROLE_DUPLICATE","path":"grantRole-duplicate","delta":3655,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G27","gasKey":"REVOKE_ROLE_MISSING","path":"revokeRole-missing","delta":1422,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G28","gasKey":"RENOUNCE_ROLE_WRONG_ACCOUNT","path":"renounceRole-wrong-account","delta":78,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G29","gasKey":"GET_ROLE_MEMBER_OOB","path":"getRoleMember-oob","delta":2482,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G30","gasKey":"ROLE_ENUMERATION_CROSS_ROLE","path":"role-enumeration-cross-role-order","delta":6817,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G31","gasKey":"ROLE_COLLISION_REFUSAL","path":"role-flat-key-collision-refusal","delta":4222,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G32","gasKey":"PAUSE_FOR_WHEN_PAUSED","path":"pauseFor-when-paused","delta":3690,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G33","gasKey":"PAUSE_UNTIL_WHEN_PAUSED","path":"pauseUntil-when-paused","delta":3887,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G34","gasKey":"PAUSE_ZERO_DURATION","path":"pauseFor-zero-duration","delta":3688,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G35","gasKey":"PAUSE_UNTIL_PAST","path":"pauseUntil-past","delta":3879,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G36","gasKey":"RESUME_WHEN_RESUMED","path":"resume-when-resumed","delta":4011,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G37","gasKey":"SET_LIMIT_MAX_TOO_LARGE","path":"setExitRequestLimit-max-too-large","delta":1331,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G38","gasKey":"SET_LIMIT_FRAME_TOO_LARGE","path":"setExitRequestLimit-frame-too-large","delta":1330,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G39","gasKey":"SET_LIMIT_EXITS_ABOVE_MAX","path":"setExitRequestLimit-exits-above-max","delta":1332,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G40","gasKey":"SET_LIMIT_ZERO_FRAME","path":"setExitRequestLimit-zero-frame","delta":1337,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G41","gasKey":"TRIGGER_INSUFFICIENT_FEE","path":"trigger-insufficient-fee","delta":10677,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G42","gasKey":"TRIGGER_PAUSED","path":"trigger-paused","delta":3818,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G43","gasKey":"TRIGGER_ZERO_VALUE","path":"trigger-zero-value","delta":3775,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G44","gasKey":"TRIGGER_LOCATOR_REVERT","path":"trigger-locator-revert","delta":11109,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G45","gasKey":"TRIGGER_FEE_QUERY_REVERT","path":"trigger-fee-query-revert","delta":10898,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G46","gasKey":"TRIGGER_VAULT_REVERT","path":"trigger-vault-revert","delta":10751,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G47","gasKey":"TRIGGER_ROUTER_REVERT","path":"trigger-router-revert","delta":9800,"status":"accepted"} -->
<!-- LIDO-TWG-GAS-DEVIATION {"id":"TWG-G48","gasKey":"TRIGGER_REFUND_REVERT","path":"trigger-refund-revert","delta":9629,"status":"accepted"} -->

| Stable ID | Path | Delta | Defense | Evidence |
|---|---|---:|---|---|
| `TWG-G01` | `constructor-success` | `1656125` | Accepted deployment cost for explicit constructor validation, tagged role/limit initialization, and runtime code deposit; no deployment-gas improvement is claimed. | manifest resource coordinate constructor-success#0:constructor; deployment initialization and code-deposit boundary |
| `TWG-G02` | `pauseFor-finite` | `3420` | Accepted pause-control cost for explicit authorization, sentinel/error-polarity checks, and tagged-state update or rollback; no gas improvement is claimed. | manifest resource coordinate pause-for-finite#2:action; pause/resume authorization and tagged-state boundary |
| `TWG-G03` | `pauseFor-sentinel` | `3516` | Accepted pause-control cost for explicit authorization, sentinel/error-polarity checks, and tagged-state update or rollback; no gas improvement is claimed. | manifest resource coordinate pause-for-sentinel#2:action; pause/resume authorization and tagged-state boundary |
| `TWG-G04` | `pauseUntil-finite` | `3627` | Accepted pause-control cost for explicit authorization, sentinel/error-polarity checks, and tagged-state update or rollback; no gas improvement is claimed. | manifest resource coordinate pause-until-finite#2:action; pause/resume authorization and tagged-state boundary |
| `TWG-G05` | `pauseUntil-sentinel` | `3720` | Accepted pause-control cost for explicit authorization, sentinel/error-polarity checks, and tagged-state update or rollback; no gas improvement is claimed. | manifest resource coordinate pause-until-sentinel#2:action; pause/resume authorization and tagged-state boundary |
| `TWG-G06` | `resume` | `3960` | Accepted pause-control cost for explicit authorization, sentinel/error-polarity checks, and tagged-state update or rollback; no gas improvement is claimed. | manifest resource coordinate resume-authorized#4:action; pause/resume authorization and tagged-state boundary |
| `TWG-G07` | `grantRole-fresh` | `28154` | Accepted role-state cost for full-identity collision checks and global enumeration maintenance or scanning; TWG-D02–D05 separately delimit observable differences. | manifest resource coordinate grant-role-fresh#1:action; full-identity role lookup/enumeration boundary |
| `TWG-G08` | `revokeRole-existing` | `10935` | Accepted role-state cost for full-identity collision checks and global enumeration maintenance or scanning; TWG-D02–D05 separately delimit observable differences. | manifest resource coordinate revoke-role-existing#2:action; full-identity role lookup/enumeration boundary |
| `TWG-G09` | `renounceRole-self` | `9174` | Accepted role-state cost for full-identity collision checks and global enumeration maintenance or scanning; TWG-D02–D05 separately delimit observable differences. | manifest resource coordinate renounce-role-self#2:action; full-identity role lookup/enumeration boundary |
| `TWG-G10` | `getRoleMember` | `4522` | Accepted role-state cost for full-identity collision checks and global enumeration maintenance or scanning; TWG-D02–D05 separately delimit observable differences. | manifest resource coordinate get-role-member#2:action; full-identity role lookup/enumeration boundary |
| `TWG-G11` | `getRoleMemberCount` | `4786` | Accepted role-state cost for full-identity collision checks and global enumeration maintenance or scanning; TWG-D02–D05 separately delimit observable differences. | manifest resource coordinate get-role-member-count#2:action; full-identity role lookup/enumeration boundary |
| `TWG-G12` | `setExitRequestLimit` | `20027` | Accepted exit-limit cost for explicit five-field projection, validation, checked consumption, or whole-frame refill; the measured behavior is independently pinned. | manifest resource coordinate set-limit-valid#2:action; exit-limit projection and validation boundary |
| `TWG-G13` | `getExitRequestLimitFullInfo-same-frame` | `8262` | Accepted exit-limit cost for explicit five-field projection, validation, checked consumption, or whole-frame refill; the measured behavior is independently pinned. | manifest resource coordinate get-limit-same-frame#1:action; exit-limit projection and validation boundary |
| `TWG-G14` | `getExitRequestLimitFullInfo-refilled` | `8066` | Accepted exit-limit cost for explicit five-field projection, validation, checked consumption, or whole-frame refill; the measured behavior is independently pinned. | manifest resource coordinate get-limit-refilled#3:action; exit-limit projection and validation boundary |
| `TWG-G15` | `trigger-empty` | `3766` | Accepted trigger-path cost for explicit fee, vault, router, refund, and rollback choreography; the corpus pins effects and no aggregate gas advantage is claimed. | manifest resource coordinate trigger-empty#2:action; trigger dependency/value/rollback boundary |
| `TWG-G16` | `trigger-single-no-refund` | `9712` | Accepted trigger-path cost for explicit fee, vault, router, refund, and rollback choreography; the corpus pins effects and no aggregate gas advantage is claimed. | manifest resource coordinate trigger-single-exact-fee#2:action; trigger dependency/value/rollback boundary |
| `TWG-G17` | `trigger-single-explicit-refund` | `9613` | Accepted trigger-path cost for explicit fee, vault, router, refund, and rollback choreography; the corpus pins effects and no aggregate gas advantage is claimed. | manifest resource coordinate trigger-explicit-refund#2:action; trigger dependency/value/rollback boundary |
| `TWG-G18` | `trigger-single-sender-refund` | `9618` | Accepted trigger-path cost for explicit fee, vault, router, refund, and rollback choreography; the corpus pins effects and no aggregate gas advantage is claimed. | manifest resource coordinate trigger-sender-refund#2:action; trigger dependency/value/rollback boundary |
| `TWG-G19` | `trigger-multiple` | `9075` | Accepted trigger-path cost for explicit fee, vault, router, refund, and rollback choreography; the corpus pins effects and no aggregate gas advantage is claimed. | manifest resource coordinate trigger-multiple#2:action; trigger dependency/value/rollback boundary |
| `TWG-G20` | `trigger-limit-exceeded` | `11692` | Accepted trigger-path cost for explicit fee, vault, router, refund, and rollback choreography; the corpus pins effects and no aggregate gas advantage is claimed. | manifest resource coordinate trigger-limit-exceeded#2:action; trigger dependency/value/rollback boundary |
| `TWG-G21` | `defaultAdminRole` | `138` | Accepted read-path cost of Blanc's explicit dispatcher and proof-local tagged representation; exact output semantics are pinned and no gas improvement is claimed. | manifest resource coordinate view-default-admin-role#1:action; constant, interface, role, or pause-state read boundary |
| `TWG-G22` | `pauseInfinitely` | `70` | Accepted read-path cost of Blanc's explicit dispatcher and proof-local tagged representation; exact output semantics are pinned and no gas improvement is claimed. | manifest resource coordinate view-pause-infinitely#1:action; constant, interface, role, or pause-state read boundary |
| `TWG-G23` | `supportsInterface` | `148` | Accepted read-path cost of Blanc's explicit dispatcher and proof-local tagged representation; exact output semantics are pinned and no gas improvement is claimed. | manifest resource coordinate view-supports-interface#1:action; constant, interface, role, or pause-state read boundary |
| `TWG-G24` | `hasRole` | `4222` | Accepted read-path cost of Blanc's explicit dispatcher and proof-local tagged representation; exact output semantics are pinned and no gas improvement is claimed. | manifest resource coordinate view-has-role#1:action; constant, interface, role, or pause-state read boundary |
| `TWG-G25` | `getResumeSinceTimestamp` | `27` | Accepted read-path cost of Blanc's explicit dispatcher and proof-local tagged representation; exact output semantics are pinned and no gas improvement is claimed. | manifest resource coordinate view-resume-timestamp#1:action; constant, interface, role, or pause-state read boundary |
| `TWG-G26` | `grantRole-duplicate` | `3655` | Accepted role-state cost for full-identity collision checks and global enumeration maintenance or scanning; TWG-D02–D05 separately delimit observable differences. | manifest resource coordinate grant-role-duplicate#2:action; full-identity role lookup/enumeration boundary |
| `TWG-G27` | `revokeRole-missing` | `1422` | Accepted role-state cost for full-identity collision checks and global enumeration maintenance or scanning; TWG-D02–D05 separately delimit observable differences. | manifest resource coordinate revoke-role-missing#1:action; full-identity role lookup/enumeration boundary |
| `TWG-G28` | `renounceRole-wrong-account` | `78` | Accepted role-state cost for full-identity collision checks and global enumeration maintenance or scanning; TWG-D02–D05 separately delimit observable differences. | manifest resource coordinate renounce-role-wrong-account#1:action; full-identity role lookup/enumeration boundary |
| `TWG-G29` | `getRoleMember-oob` | `2482` | Accepted role-state cost for full-identity collision checks and global enumeration maintenance or scanning; TWG-D02–D05 separately delimit observable differences. | manifest resource coordinate get-role-member-oob#1:action; full-identity role lookup/enumeration boundary |
| `TWG-G30` | `role-enumeration-cross-role-order` | `6817` | Accepted role-state cost for full-identity collision checks and global enumeration maintenance or scanning; TWG-D02–D05 separately delimit observable differences. | manifest resource coordinate role-enumeration-cross-role-order#7:action; full-identity role lookup/enumeration boundary |
| `TWG-G31` | `role-flat-key-collision-refusal` | `4222` | Accepted role-state cost for full-identity collision checks and global enumeration maintenance or scanning; TWG-D02–D05 separately delimit observable differences. | manifest resource coordinate role-flat-key-collision-refusal#3:action; full-identity role lookup/enumeration boundary |
| `TWG-G32` | `pauseFor-when-paused` | `3690` | Accepted pause-control cost for explicit authorization, sentinel/error-polarity checks, and tagged-state update or rollback; no gas improvement is claimed. | manifest resource coordinate pause-for-when-paused#3:action; pause/resume authorization and tagged-state boundary |
| `TWG-G33` | `pauseUntil-when-paused` | `3887` | Accepted pause-control cost for explicit authorization, sentinel/error-polarity checks, and tagged-state update or rollback; no gas improvement is claimed. | manifest resource coordinate pause-until-when-paused#3:action; pause/resume authorization and tagged-state boundary |
| `TWG-G34` | `pauseFor-zero-duration` | `3688` | Accepted pause-control cost for explicit authorization, sentinel/error-polarity checks, and tagged-state update or rollback; no gas improvement is claimed. | manifest resource coordinate pause-zero-duration#2:action; pause/resume authorization and tagged-state boundary |
| `TWG-G35` | `pauseUntil-past` | `3879` | Accepted pause-control cost for explicit authorization, sentinel/error-polarity checks, and tagged-state update or rollback; no gas improvement is claimed. | manifest resource coordinate pause-until-past#2:action; pause/resume authorization and tagged-state boundary |
| `TWG-G36` | `resume-when-resumed` | `4011` | Accepted pause-control cost for explicit authorization, sentinel/error-polarity checks, and tagged-state update or rollback; no gas improvement is claimed. | manifest resource coordinate resume-when-resumed#2:action; pause/resume authorization and tagged-state boundary |
| `TWG-G37` | `setExitRequestLimit-max-too-large` | `1331` | Accepted exit-limit cost for explicit five-field projection, validation, checked consumption, or whole-frame refill; the measured behavior is independently pinned. | manifest resource coordinate set-limit-max-too-large#2:action; exit-limit projection and validation boundary |
| `TWG-G38` | `setExitRequestLimit-frame-too-large` | `1330` | Accepted exit-limit cost for explicit five-field projection, validation, checked consumption, or whole-frame refill; the measured behavior is independently pinned. | manifest resource coordinate set-limit-frame-too-large#2:action; exit-limit projection and validation boundary |
| `TWG-G39` | `setExitRequestLimit-exits-above-max` | `1332` | Accepted exit-limit cost for explicit five-field projection, validation, checked consumption, or whole-frame refill; the measured behavior is independently pinned. | manifest resource coordinate set-limit-exits-above-max#2:action; exit-limit projection and validation boundary |
| `TWG-G40` | `setExitRequestLimit-zero-frame` | `1337` | Accepted exit-limit cost for explicit five-field projection, validation, checked consumption, or whole-frame refill; the measured behavior is independently pinned. | manifest resource coordinate set-limit-zero-frame#2:action; exit-limit projection and validation boundary |
| `TWG-G41` | `trigger-insufficient-fee` | `10677` | Accepted trigger-path cost for explicit fee, vault, router, refund, and rollback choreography; the corpus pins effects and no aggregate gas advantage is claimed. | manifest resource coordinate trigger-insufficient-fee#2:action; trigger dependency/value/rollback boundary |
| `TWG-G42` | `trigger-paused` | `3818` | Accepted trigger-path cost for explicit fee, vault, router, refund, and rollback choreography; the corpus pins effects and no aggregate gas advantage is claimed. | manifest resource coordinate trigger-paused#4:action; trigger dependency/value/rollback boundary |
| `TWG-G43` | `trigger-zero-value` | `3775` | Accepted trigger-path cost for explicit fee, vault, router, refund, and rollback choreography; the corpus pins effects and no aggregate gas advantage is claimed. | manifest resource coordinate trigger-zero-value#2:action; trigger dependency/value/rollback boundary |
| `TWG-G44` | `trigger-locator-revert` | `11109` | Accepted trigger-path cost for explicit fee, vault, router, refund, and rollback choreography; the corpus pins effects and no aggregate gas advantage is claimed. | manifest resource coordinate trigger-locator-revert#2:action; trigger dependency/value/rollback boundary |
| `TWG-G45` | `trigger-fee-query-revert` | `10898` | Accepted trigger-path cost for explicit fee, vault, router, refund, and rollback choreography; the corpus pins effects and no aggregate gas advantage is claimed. | manifest resource coordinate trigger-fee-query-revert#2:action; trigger dependency/value/rollback boundary |
| `TWG-G46` | `trigger-vault-revert` | `10751` | Accepted trigger-path cost for explicit fee, vault, router, refund, and rollback choreography; the corpus pins effects and no aggregate gas advantage is claimed. | manifest resource coordinate trigger-vault-revert#2:action; trigger dependency/value/rollback boundary |
| `TWG-G47` | `trigger-router-revert` | `9800` | Accepted trigger-path cost for explicit fee, vault, router, refund, and rollback choreography; the corpus pins effects and no aggregate gas advantage is claimed. | manifest resource coordinate trigger-router-revert#2:action; trigger dependency/value/rollback boundary |
| `TWG-G48` | `trigger-refund-revert` | `9629` | Accepted trigger-path cost for explicit fee, vault, router, refund, and rollback choreography; the corpus pins effects and no aggregate gas advantage is claimed. | manifest resource coordinate trigger-refund-revert#2:action; trigger dependency/value/rollback boundary |

All 48 positive coordinates are accepted as measured priced costs of the
proof-oriented Blanc design. The exact path, delta, resource coordinate, and one
of six substantive review rationales are pinned row by row; no generic
“retained for review” defense remains. Their `TWG-Gnn` identifiers are gas-cost
dispositions, not behavioral mismatch IDs. `TWG-D01` through `TWG-D05` remain
the complete known behavioral-deviation inventory, and aggregate code-size or
gas savings are not a stance for any individual dearer path.

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
