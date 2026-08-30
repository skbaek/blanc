# Lido TriggerableWithdrawalsGateway deviation registry

> **Published evidence status:** the registry is synchronized to the validated
> B1 lock and generated B2 manifest. All five known behavioral differences are
> accepted and defended below; all 20 positive named-path gas deltas are
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

<!-- LIDO-TWG-DEVIATION-POLICY {"schema":1,"closure":"complete","knownBehavioralRows":5,"acceptedBehavioralRows":5,"repairedBehavioralRows":0,"pendingBehavioralRows":0,"positiveGasRows":20,"unknownMismatchAllowlist":false} -->

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
- exact gas and access-list warming, except that every measured public-path
  increase is itself a behavioral deviation requiring a stable row.

## Code-size comparison

<!-- LIDO-TWG-CODE-SIZE {"referenceLock":"8e92a23746c47a9b065f6c042c98d9913785c40c0f27e0a1f82cfc37c0effc0f","blancCommit":"35a196fd50192aa269d6cb07699ea0910ad3c468","manifest":"a4e7a9b553ceda869f97c30a85214ae599171960fd54db43244ebc7cb43ac4f8"} -->

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

<!-- LIDO-TWG-GAS-MEASUREMENT {"eelsCommit":"4198b9c5996713b268aed602739d5aa40e277694","manifest":"a4e7a9b553ceda869f97c30a85214ae599171960fd54db43244ebc7cb43ac4f8","boundaryDefinition":"direct EELS Prague message gas used, computed as message gas minus output gas_left; constructor rows include code-deposit gas and exclude transaction intrinsic gas and refunds","rowCount":23,"positiveDeltaRows":20} -->

Every cell below comes from the same ordered resource vector. `Reference` and
`Blanc` use one boundary definition, recorded verbatim as
`direct EELS Prague message gas used, computed as message gas minus output gas_left; constructor rows include code-deposit gas and exclude transaction intrinsic gas and refunds`. Positive delta means Blanc is dearer
and is entered under a stable `TWG-Gnn` deviation row; sums and averages do
not hide it.

| Stable path | Compared world and outcome | Reference gas | Blanc gas | Delta | Manifest coordinate |
|---|---|---:|---:|---:|---|
| `constructor-success` | successful complete CREATE, official parameter world | `1744364` | `3400489` | `1656125` | `constructor-success#0:constructor` |
| `pauseFor-finite` | authorized resumed → finite pause | `26352` | `29772` | `3420` | `pause-for-finite#2:action` |
| `pauseFor-sentinel` | authorized resumed → infinite sentinel | `26225` | `29741` | `3516` | `pause-for-sentinel#2:action` |
| `pauseUntil-finite` | authorized resumed → inclusive finite expiry | `26392` | `30019` | `3627` | `pause-until-finite#2:action` |
| `pauseUntil-sentinel` | authorized resumed → infinite sentinel | `26243` | `29963` | `3720` | `pause-until-sentinel#2:action` |
| `resume` | authorized paused → resumed | `8538` | `12498` | `3960` | `resume-authorized#4:action` |
| `isPaused-resumed` | canonical false query | `2385` | `2220` | `-165` | `view-is-paused-resumed#1:action` |
| `isPaused-paused` | canonical true query | `2385` | `2220` | `-165` | `view-is-paused-paused#3:action` |
| `grantRole-fresh` | authorized fresh membership | `96496` | `124650` | `28154` | `grant-role-fresh#1:action` |
| `revokeRole-existing` | authorized existing membership | `28381` | `39316` | `10935` | `revoke-role-existing#2:action` |
| `renounceRole-self` | self-renounce existing membership | `23754` | `32928` | `9174` | `renounce-role-self#2:action` |
| `getRoleMember` | successful populated-role ordinal | `4841` | `9363` | `4522` | `get-role-member#2:action` |
| `getRoleMemberCount` | populated role after history | `2614` | `7400` | `4786` | `get-role-member-count#2:action` |
| `setExitRequestLimit` | authorized configuration update | `11114` | `31141` | `20027` | `set-limit-valid#2:action` |
| `getExitRequestLimitFullInfo-same-frame` | no whole-frame refill | `3208` | `11470` | `8262` | `get-limit-same-frame#1:action` |
| `getExitRequestLimitFullInfo-refilled` | elapsed whole-frame refill/cap | `3567` | `11633` | `8066` | `get-limit-refilled#3:action` |
| `trigger-empty` | empty validator array rejection | `5398` | `9164` | `3766` | `trigger-empty#2:action` |
| `trigger-single-no-refund` | one validator, exact fee | `233284` | `242996` | `9712` | `trigger-single-exact-fee#2:action` |
| `trigger-single-explicit-refund` | one validator, excess to named recipient | `267754` | `277367` | `9613` | `trigger-explicit-refund#2:action` |
| `trigger-single-sender-refund` | one validator, zero recipient falls back to sender | `240258` | `249876` | `9618` | `trigger-sender-refund#2:action` |
| `trigger-multiple` | multi-validator fee/encoding/router path | `235133` | `244208` | `9075` | `trigger-multiple#2:action` |
| `trigger-limit-exceeded` | authorized resumed quota rejection | `8215` | `19907` | `11692` | `trigger-limit-exceeded#2:action` |
| `role-gate-unauthorized` | representative `TWG-D01` failure | `32304` | `2270` | `-30034` | `role-negative-pause-for#1:action` |

Every remaining selector also has at least one measured adequate boundary in
the complete vector. Machine summary:
`24/24 census selectors each own at least one direct action boundary`.

### Positive-delta registry

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

| Stable ID | Path | Delta | Defense | Evidence |
|---|---|---:|---|---|
| `TWG-G01` | `constructor-success` | `1656125` | Published finite-corpus increase retained for explicit review in the TWG gas registry. | manifest resource coordinate constructor-success#0:constructor |
| `TWG-G02` | `pauseFor-finite` | `3420` | Published finite-corpus increase retained for explicit review in the TWG gas registry. | manifest resource coordinate pause-for-finite#2:action |
| `TWG-G03` | `pauseFor-sentinel` | `3516` | Published finite-corpus increase retained for explicit review in the TWG gas registry. | manifest resource coordinate pause-for-sentinel#2:action |
| `TWG-G04` | `pauseUntil-finite` | `3627` | Published finite-corpus increase retained for explicit review in the TWG gas registry. | manifest resource coordinate pause-until-finite#2:action |
| `TWG-G05` | `pauseUntil-sentinel` | `3720` | Published finite-corpus increase retained for explicit review in the TWG gas registry. | manifest resource coordinate pause-until-sentinel#2:action |
| `TWG-G06` | `resume` | `3960` | Published finite-corpus increase retained for explicit review in the TWG gas registry. | manifest resource coordinate resume-authorized#4:action |
| `TWG-G07` | `grantRole-fresh` | `28154` | Published finite-corpus increase retained for explicit review in the TWG gas registry. | manifest resource coordinate grant-role-fresh#1:action |
| `TWG-G08` | `revokeRole-existing` | `10935` | Published finite-corpus increase retained for explicit review in the TWG gas registry. | manifest resource coordinate revoke-role-existing#2:action |
| `TWG-G09` | `renounceRole-self` | `9174` | Published finite-corpus increase retained for explicit review in the TWG gas registry. | manifest resource coordinate renounce-role-self#2:action |
| `TWG-G10` | `getRoleMember` | `4522` | Published finite-corpus increase retained for explicit review in the TWG gas registry. | manifest resource coordinate get-role-member#2:action |
| `TWG-G11` | `getRoleMemberCount` | `4786` | Published finite-corpus increase retained for explicit review in the TWG gas registry. | manifest resource coordinate get-role-member-count#2:action |
| `TWG-G12` | `setExitRequestLimit` | `20027` | Published finite-corpus increase retained for explicit review in the TWG gas registry. | manifest resource coordinate set-limit-valid#2:action |
| `TWG-G13` | `getExitRequestLimitFullInfo-same-frame` | `8262` | Published finite-corpus increase retained for explicit review in the TWG gas registry. | manifest resource coordinate get-limit-same-frame#1:action |
| `TWG-G14` | `getExitRequestLimitFullInfo-refilled` | `8066` | Published finite-corpus increase retained for explicit review in the TWG gas registry. | manifest resource coordinate get-limit-refilled#3:action |
| `TWG-G15` | `trigger-empty` | `3766` | Published finite-corpus increase retained for explicit review in the TWG gas registry. | manifest resource coordinate trigger-empty#2:action |
| `TWG-G16` | `trigger-single-no-refund` | `9712` | Published finite-corpus increase retained for explicit review in the TWG gas registry. | manifest resource coordinate trigger-single-exact-fee#2:action |
| `TWG-G17` | `trigger-single-explicit-refund` | `9613` | Published finite-corpus increase retained for explicit review in the TWG gas registry. | manifest resource coordinate trigger-explicit-refund#2:action |
| `TWG-G18` | `trigger-single-sender-refund` | `9618` | Published finite-corpus increase retained for explicit review in the TWG gas registry. | manifest resource coordinate trigger-sender-refund#2:action |
| `TWG-G19` | `trigger-multiple` | `9075` | Published finite-corpus increase retained for explicit review in the TWG gas registry. | manifest resource coordinate trigger-multiple#2:action |
| `TWG-G20` | `trigger-limit-exceeded` | `11692` | Published finite-corpus increase retained for explicit review in the TWG gas registry. | manifest resource coordinate trigger-limit-exceeded#2:action |

All 20 positive coordinates are accepted as measured priced costs of the
proof-oriented Blanc design. Their stable IDs, exact deltas, and manifest
coordinates make the cost reviewable path by path. The generated defense text
“retained for explicit review” means published for continuing public scrutiny,
not awaiting disposition: all 20 marker statuses are `accepted`. Aggregate code-size or
gas savings are not a stance for any individual dearer path.

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
