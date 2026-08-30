# Lido TriggerableWithdrawalsGateway compatibility contract

> **Published evidence status:** the identities, counts, comparisons, and
> finite observations below are filled from the validated B1 reference lock
> and generated B2 differential manifest. The synchronization gate rejects
> marker drift, non-dispositioned deviations, or a mismatch with either evidence
> source.

This document freezes the public conformance boundary for Blanc's port of
Lido's `TriggerableWithdrawalsGateway`. It is read with [`PORTING.md`](PORTING.md):
the port does not claim Solidity bytecode, code hash, raw storage layout, or
gas identity. It claims only the behavior stated here, the properties proved
of the exact compiled Blanc runtime, finite agreement on the published corpus,
and the known differences published in
[`LIDO_TRIGGERABLE_WITHDRAWALS_GATEWAY_DEVIATIONS.md`](LIDO_TRIGGERABLE_WITHDRAWALS_GATEWAY_DEVIATIONS.md).

The source authority is
`contracts/0.8.9/TriggerableWithdrawalsGateway.sol` and its inherited bases at
`lidofinance/core` commit
`17005714f151e5502c559932319a3f2f74ac2436`. The source-derived census in
[`scripts/lido-twg-census.json`](scripts/lido-twg-census.json) freezes 24
selectors, six event families, 14 custom-error families, six role/slot hashes,
and the exact `whenResumed` surface. The B1 lock and B2 manifest, not this
prose, own artifact identities and finite observations.

## Evidence identities

| Item | Locked identity |
|---|---|
| Reference-lock schema | `1` |
| Reference-lock SHA-256 | `8e92a23746c47a9b065f6c042c98d9913785c40c0f27e0a1f82cfc37c0effc0f` |
| Source commit | `17005714f151e5502c559932319a3f2f74ac2436` |
| Solidity compiler | `0.8.9`; artifact SHA-256 `5b25f987aae32a0275fdc6c1be36cc47cf126024a04dafd8e4be39a1d1d1422c` |
| Reference creation bytes | `10256` bytes; SHA-256 `0e7dd55e589cf6bd38b2ebae7581ff169a354f9399087ecb6b8940f56bacc7e7` |
| Reference runtime | `8128` bytes; SHA-256 `12c9d210f25202cf535622f93ba5237181512cc23970f2da08434f77e68d3a7b` |
| Selection-time mainnet snapshot | account `0xDC00116a0D3E064427dA2600449cfD2566B3037B`; block `25866991`; code hash `0xbf27dab01ae7fb4507657a02d975bd38aeea9eaba4498225da3a0ee5f815f123`; role/pause snapshot `b22333b245132e24f43328f46030b09f2ccf805ad3937382d1636a849626cc23` |
| Blanc artifact/runtime program commit | `35a196fd50192aa269d6cb07699ea0910ad3c468` |
| First compile-valid pinned-target proof certificate | `a0e04e7a69558b8744ced81ea4a3defdfc478d36` |
| Jaune pin | `949cf97ee1956828a3ac0eb12a62c438656ba76e` |
| Blanc creation template | `17976` bytes; SHA-256 `1c7a59c47cb97dbd8da1ccd02ed2913d553d18e6f353c640b308ce47b638eeb1` |
| Blanc complete CREATE input | `18136` bytes; SHA-256 `8091507f8753791e74a3ba7704436dac4bc7db3fcbf973a97b5296934432347a` |
| Blanc runtime | `15948` bytes; SHA-256 `2a4d45a407f79c896735072ba7f825927a857ec93f4c9c9abeff3e7905ebdb08` |
| EELS oracle | `ethereum/execution-specs` commit `4198b9c5996713b268aed602739d5aa40e277694`, Prague |
| Differential manifest | schema `1`; SHA-256 `4dea3481b12f12a751af1bdae602a8e5d6d7055f6359795fdd89950b3e0ae4d4` |
| Differential result | `PASS`; `71` cases, `186` measured resource boundaries |

The mainnet snapshot is provenance and selection-time context. It is not a
proof of the deployed Solidity account, a claim that its role state persists,
or a premise of the Blanc theorems.

## Coverage criterion

The published compatibility corpus is defined by the following finite
criterion, which the generated manifest and its gate establish:

1. every one of the 24 census selectors is exercised on both exact artifacts;
2. the constructor is executed through each artifact's complete CREATE input;
3. all five reachable emitted event families are checked for exact emitter,
   topics, data, order, and rollback, while `RoleAdminChanged` owns an exact
   non-emission row because this gateway never calls `_setRoleAdmin`;
4. pause/resume coverage contains resumed and paused worlds, finite
   `pauseFor`, `pauseFor(2^256 - 1)`, finite inclusive `pauseUntil`,
   `pauseUntil(2^256 - 1)`, truthful paused/resumed queries, and authorization
   negatives;
5. AccessControl coverage contains membership, admin lookup, grant, revoke,
   self-renounce, wrong-account renounce, enumeration, removal histories, and
   the five known difference classes `TWG-D01` through `TWG-D05`;
6. limit coverage contains initial configuration, valid reconfiguration,
   validation failures, consumption, exceeded quota, same-frame observation,
   whole-frame refill, capping, and the named checked arithmetic boundaries;
7. trigger coverage contains canonical empty, singleton, and multi-validator
   arrays; fee multiplication; exact vault value;
   locator, vault, and router observations; no-refund, explicit-recipient
   refund, zero-recipient-to-sender refund, refund failure, rollback, and ETH
   balance preservation;
8. dispatch/calldata coverage is limited to the recognized selectors and
   canonical ABI words used by the named endpoint rows, plus the named dirty
   constructor-address rejection; and
9. every compared status, returndata, logical-state, ETH, log, and external-call
   channel has a bounded falsifier that changes only that channel and is caught
   for the expected reason.

The deliberately untested dispatch/calldata boundary is exact: nested
malformed dynamic ABI, empty/unknown/short dispatch, trailing calldata, and
recognized-selector nonpayability are untested and excluded.

The exact generated coverage result is
`71 named rows cover 24/24 selectors, constructor, five reachable emitted event kinds plus RoleAdminChanged non-emission, pause sentinel/error-polarity arms, roles, configured-limit consumption/exceeded/whole-frame refill, and trigger mocks; zero/unlimited and partial-frame limit behavior plus the excluded dispatch/calldata arms are untested`. Agreement means agreement on those chosen
rows and observations only. It is not a proof, a liveness result, or an
exhaustive equivalence claim.

## Runtime endpoints

Unless an endpoint says otherwise, canonical ABI input and adequate execution
gas are required. Successful no-output calls return empty bytes. A reverted
top-level call commits no state, ETH movement, or log. Exact error payload
differences are governed by the deviation registry, never normalized away by
the comparison.

The marker inventory below is an exact ordered transcription of the locked
census. The adjacent endpoint sections state the claimed behavior.

| # | Signature | Selector |
|---:|---|---|
| 1 | `PAUSE_ROLE()` | `0x389ed267` |
| 2 | `RESUME_ROLE()` | `0x2de03aa1` |
| 3 | `ADD_FULL_WITHDRAWAL_REQUEST_ROLE()` | `0xa0cbdf14` |
| 4 | `TW_EXIT_LIMIT_MANAGER_ROLE()` | `0x2d44866b` |
| 5 | `TWR_LIMIT_POSITION()` | `0x76b0023e` |
| 6 | `VERSION()` | `0xffa1ad74` |
| 7 | `resume()` | `0x046f7da2` |
| 8 | `pauseFor(uint256)` | `0xf3f449c7` |
| 9 | `pauseUntil(uint256)` | `0xabe9cfc8` |
| 10 | `triggerFullWithdrawals((uint256,uint256,bytes)[],address,uint256)` | `0x138b1b15` |
| 11 | `setExitRequestLimit(uint256,uint256,uint256)` | `0x56254a97` |
| 12 | `getExitRequestLimitFullInfo()` | `0xb6b764b2` |
| 13 | `PAUSE_INFINITELY()` | `0xa302ee38` |
| 14 | `isPaused()` | `0xb187bd26` |
| 15 | `getResumeSinceTimestamp()` | `0x589ff76c` |
| 16 | `DEFAULT_ADMIN_ROLE()` | `0xa217fddf` |
| 17 | `supportsInterface(bytes4)` | `0x01ffc9a7` |
| 18 | `hasRole(bytes32,address)` | `0x91d14854` |
| 19 | `getRoleAdmin(bytes32)` | `0x248a9ca3` |
| 20 | `grantRole(bytes32,address)` | `0x2f2ff15d` |
| 21 | `revokeRole(bytes32,address)` | `0xd547741f` |
| 22 | `renounceRole(bytes32,address)` | `0x36568abe` |
| 23 | `getRoleMember(bytes32,uint256)` | `0x9010d07c` |
| 24 | `getRoleMemberCount(bytes32)` | `0xca15c873` |

<!-- LIDO-TWG-ENDPOINT {"signature":"PAUSE_ROLE()","selector":"0x389ed267"} -->
### `PAUSE_ROLE()`

The canonical zero-value corpus row returns
`0x139c2898040ef16910dc9f44dc697df79363da767d8bc92f2e310312b816e46d`.

<!-- LIDO-TWG-ENDPOINT {"signature":"RESUME_ROLE()","selector":"0x2de03aa1"} -->
### `RESUME_ROLE()`

The canonical zero-value corpus row returns
`0x2fc10cc8ae19568712f7a176fb4978616a610650813c9d05326c34abb62749c7`.

<!-- LIDO-TWG-ENDPOINT {"signature":"ADD_FULL_WITHDRAWAL_REQUEST_ROLE()","selector":"0xa0cbdf14"} -->
### `ADD_FULL_WITHDRAWAL_REQUEST_ROLE()`

The canonical zero-value corpus row returns
`0x15fac8ba7fe8dd5344b88c1915452ce66976f270d1cd793c3b0ab579cecd33c0`.

<!-- LIDO-TWG-ENDPOINT {"signature":"TW_EXIT_LIMIT_MANAGER_ROLE()","selector":"0x2d44866b"} -->
### `TW_EXIT_LIMIT_MANAGER_ROLE()`

The canonical zero-value corpus row returns
`0x03c30da9b9e4d4789ac88a294d39a63058ca4a498804c2aa823e381df59d0cf4`.

<!-- LIDO-TWG-ENDPOINT {"signature":"TWR_LIMIT_POSITION()","selector":"0x76b0023e"} -->
### `TWR_LIMIT_POSITION()`

The canonical zero-value corpus row returns the reference's public named-slot word
`0x3a69583d449251314fd68e4e68fe89ca455d27f2701d2fdee1b16c585fc4e2d6`.
This does not imply that Blanc stores its logical limit state at that raw slot.

<!-- LIDO-TWG-ENDPOINT {"signature":"VERSION()","selector":"0xffa1ad74"} -->
### `VERSION()`

The canonical zero-value corpus row returns `1`.

<!-- LIDO-TWG-ENDPOINT {"signature":"resume()","selector":"0x046f7da2"} -->
### `resume()`

Requires `RESUME_ROLE` and a currently paused state. On success it writes the
resume-since projection to the current timestamp and emits `Resumed()`. The
authorization-payload difference is `TWG-D01`.

<!-- LIDO-TWG-ENDPOINT {"signature":"pauseFor(uint256)","selector":"0xf3f449c7"} -->
### `pauseFor(uint256)`

Requires `PAUSE_ROLE`, a resumed state, and nonzero duration. For
`duration = 2^256 - 1`, success stores that sentinel. Otherwise checked
addition stores `block.timestamp + duration`. It emits `Paused(duration)`.
Authorization payloads are governed by `TWG-D01`; the sentinel arm is part of
compatibility, not a deviation or an exemption.

<!-- LIDO-TWG-ENDPOINT {"signature":"pauseUntil(uint256)","selector":"0xabe9cfc8"} -->
### `pauseUntil(uint256)`

Requires `PAUSE_ROLE`, a resumed state, and an inclusive timestamp not earlier
than the current block timestamp. For the infinite sentinel it stores the
sentinel and emits `Paused(2^256 - 1)`. Otherwise checked addition stores
`pauseUntilInclusive + 1` and emits the finite duration
`pauseUntilInclusive - block.timestamp`. Authorization payloads are governed
by `TWG-D01`.

<!-- LIDO-TWG-ENDPOINT {"signature":"triggerFullWithdrawals((uint256,uint256,bytes)[],address,uint256)","selector":"0x138b1b15"} -->
### `triggerFullWithdrawals((uint256,uint256,bytes)[],address,uint256)`

Payable. After ABI decoding and the source-declared modifier sequence, it
requires `ADD_FULL_WITHDRAWAL_REQUEST_ROLE`, requires the gateway to be
resumed, consumes the frame quota, resolves the withdrawal vault through the
immutable locator, computes `validatorCount * getWithdrawalRequestFee()`,
forwards the requests with exactly that fee, notifies the staking router, and
refunds excess ETH to the supplied recipient or to the sender when that
recipient is zero. The outer successful call preserves the gateway's entry ETH
balance. Dependency contracts are mocks in the corpus and arbitrary callees in
the theorem setting; they are not ported by this project. `TWG-D01` governs
the authorization payload.

<!-- LIDO-TWG-ENDPOINT {"signature":"setExitRequestLimit(uint256,uint256,uint256)","selector":"0x56254a97"} -->
### `setExitRequestLimit(uint256,uint256,uint256)`

Requires `TW_EXIT_LIMIT_MANAGER_ROLE`. It validates the maximum, exits per
frame, and frame duration in source order, accounts for the current refill,
writes the new five-word logical limit state, and emits
`ExitRequestsLimitSet(maxExitRequestsLimit, exitsPerFrame,
frameDurationInSec)`. `TWG-D01` governs the authorization payload.

<!-- LIDO-TWG-ENDPOINT {"signature":"getExitRequestLimitFullInfo()","selector":"0xb6b764b2"} -->
### `getExitRequestLimitFullInfo()`

The canonical zero-value corpus row returns five ABI words: maximum exit requests, exits per
frame, frame duration, stored previous limit, and the current calculated
limit. The current value uses the same checked frame-refill calculation as the
mutating paths without committing storage.

<!-- LIDO-TWG-ENDPOINT {"signature":"PAUSE_INFINITELY()","selector":"0xa302ee38"} -->
### `PAUSE_INFINITELY()`

The canonical zero-value corpus row returns `2^256 - 1`.

<!-- LIDO-TWG-ENDPOINT {"signature":"isPaused()","selector":"0xb187bd26"} -->
### `isPaused()`

The canonical zero-value corpus row returns ABI `true` exactly when
`block.timestamp < resumeSince`, otherwise canonical `false`, with no state,
ETH, log, or external-call effect.

<!-- LIDO-TWG-ENDPOINT {"signature":"getResumeSinceTimestamp()","selector":"0x589ff76c"} -->
### `getResumeSinceTimestamp()`

The canonical zero-value corpus row returns the logical resume-since projection unchanged.

<!-- LIDO-TWG-ENDPOINT {"signature":"DEFAULT_ADMIN_ROLE()","selector":"0xa217fddf"} -->
### `DEFAULT_ADMIN_ROLE()`

The canonical zero-value corpus row returns the zero `bytes32` word.

<!-- LIDO-TWG-ENDPOINT {"signature":"supportsInterface(bytes4)","selector":"0x01ffc9a7"} -->
### `supportsInterface(bytes4)`

The canonical zero-value corpus row exercises ERC-165, `IAccessControl`, and
`IAccessControlEnumerable`, and returns canonical false for other canonical
interface identifiers. Decoder-edge coverage is bounded by the calldata scope
below.

<!-- LIDO-TWG-ENDPOINT {"signature":"hasRole(bytes32,address)","selector":"0x91d14854"} -->
### `hasRole(bytes32,address)`

The canonical zero-value corpus row returns membership. Blanc verifies the full stored
role/account identity rather than aliasing a flat-key collision; see
`TWG-D05`.

<!-- LIDO-TWG-ENDPOINT {"signature":"getRoleAdmin(bytes32)","selector":"0x248a9ca3"} -->
### `getRoleAdmin(bytes32)`

The canonical zero-value corpus row returns `DEFAULT_ADMIN_ROLE` for the frozen source's role
configuration.

<!-- LIDO-TWG-ENDPOINT {"signature":"grantRole(bytes32,address)","selector":"0x2f2ff15d"} -->
### `grantRole(bytes32,address)`

Requires the role's admin role. A fresh grant adds membership and emits
`RoleGranted`; an existing identical membership is a successful no-op. Error
payloads and collision refusal are governed by `TWG-D01` and `TWG-D05`.

<!-- LIDO-TWG-ENDPOINT {"signature":"revokeRole(bytes32,address)","selector":"0xd547741f"} -->
### `revokeRole(bytes32,address)`

Requires the role's admin role. Existing membership is removed and
`RoleRevoked` is emitted; absent membership is a successful no-op. Error
payloads, enumeration order, and collision refusal are governed by `TWG-D01`,
`TWG-D04`, and `TWG-D05`.

<!-- LIDO-TWG-ENDPOINT {"signature":"renounceRole(bytes32,address)","selector":"0x36568abe"} -->
### `renounceRole(bytes32,address)`

The account must be the caller. Existing self-membership is removed and
`RoleRevoked` is emitted; absent self-membership is a successful no-op. The
wrong-account error payload is `TWG-D02`; enumeration and collision behavior
are `TWG-D04` and `TWG-D05`.

<!-- LIDO-TWG-ENDPOINT {"signature":"getRoleMember(bytes32,uint256)","selector":"0x9010d07c"} -->
### `getRoleMember(bytes32,uint256)`

The canonical zero-value corpus row returns the member at the requested zero-based ordinal in the
implementation's enumeration order. Out-of-bounds error data differs under
`TWG-D03`, and histories may expose the ordering difference `TWG-D04`.

<!-- LIDO-TWG-ENDPOINT {"signature":"getRoleMemberCount(bytes32)","selector":"0xca15c873"} -->
### `getRoleMemberCount(bytes32)`

The canonical zero-value corpus row returns the exact membership count for the role. The logical
count is compared even though the two implementations use different raw
storage and enumeration structures.

## Constructor

<!-- LIDO-TWG-CONSTRUCTOR {"arguments":["address","address","uint256","uint256","uint256"]} -->

The constructor arguments are `(admin, lidoLocator, maxExitRequestsLimit,
exitsPerFrame, frameDurationInSec)`. The locator becomes an immutable runtime
parameter. Constructor compatibility is finite B2 evidence over both complete
CREATE inputs. It must cover exact source-order rejection rows and a successful
world with `DEFAULT_ADMIN_ROLE` granted to `admin`, the initial five-word
logical limit projection, and the ordered `RoleGranted` then
`ExitRequestsLimitSet` logs. The installed-runtime and full constructor result
are owned by `complete CREATE success plus zero admin, dirty admin, value, and four exit-limit validation failures`.

There is no TWG deployment-root theorem in this goal. Constructor fixtures do
not establish transaction inclusion, arbitrary deployment shapes, CREATE2,
factory/proxy deployment, mainnet deployment history, or signing-key custody.

## Event census

The six events below are ABI/event-surface obligations. A B2 row receives
credit only for checking exact emitter, topic count/order, topic words, data,
and rollback rather than merely observing that some log occurred.

<!-- LIDO-TWG-EVENT {"signature":"ExitRequestsLimitSet(uint256,uint256,uint256)","topic0":"0x3119d910326e0f179e121df55f23f45b8a5022ff10c73c02aabf2b48ae36070a","indexed":[]} -->
- `ExitRequestsLimitSet(uint256,uint256,uint256)`: three data words, no indexed arguments.
  It is emitted by successful construction and successful limit
  reconfiguration.

<!-- LIDO-TWG-EVENT {"signature":"Paused(uint256)","topic0":"0x32fb7c9891bc4f963c7de9f1186d2a7755c7d6e9f4604dabe1d8bb3027c2f49e","indexed":[]} -->
- `Paused(uint256)`: one duration data word, no indexed arguments.
  It is emitted by successful `pauseFor` and `pauseUntil`.

<!-- LIDO-TWG-EVENT {"signature":"Resumed()","topic0":"0x62451d457bc659158be6e6247f56ec1df424a5c7597f71c20c2bc44e0965c8f9","indexed":[]} -->
- `Resumed()`: no indexed arguments and no data words.
  It is emitted by successful `resume`.

<!-- LIDO-TWG-EVENT {"signature":"RoleAdminChanged(bytes32,bytes32,bytes32)","topic0":"0xbd79b86ffe0ab8e8776151514217cd7cacd52c909f66475c3af44e129f0b00ff","indexed":["role","previousAdminRole","newAdminRole"]} -->
- `RoleAdminChanged(bytes32,bytes32,bytes32)`: all three arguments indexed.
  It is part of the inherited ABI/event census, but the frozen gateway exposes
  no route that changes a role admin. Corpus rows must therefore check its
  absence from reachable constructor and public-call observations rather than
  synthesize an impossible success event.

<!-- LIDO-TWG-EVENT {"signature":"RoleGranted(bytes32,address,address)","topic0":"0x2f8788117e7eff1d82e926ec794901d17c78024a50270940304540a733656f0d","indexed":["role","account","sender"]} -->
- `RoleGranted(bytes32,address,address)`: all three arguments indexed.
  It is emitted for the constructor's initial admin grant and every fresh
  successful public grant, but not an idempotent grant.

<!-- LIDO-TWG-EVENT {"signature":"RoleRevoked(bytes32,address,address)","topic0":"0xf6391f5c32d9c69d2a47ea670b442974b53935d1edc7fd64eb21e047a839171b","indexed":["role","account","sender"]} -->
- `RoleRevoked(bytes32,address,address)`: all three arguments indexed.
  It is emitted when public revoke or self-renounce removes existing
  membership, but not for an absent-membership no-op.

## Cross-cutting boundary

<!-- LIDO-TWG-CROSSCUT scope-oracles -->
### Scope and oracle independence

The Solidity side is reconstructed from the pinned source/compiler lock. The
Blanc side is emitted by evaluating the exact compiled program family. Neither
artifact supplies the other's expected status, returndata, projected state,
ETH, logs, or call observations.

<!-- LIDO-TWG-CROSSCUT dispatch-calldata -->
### Dispatch, nonpayability, and calldata

The finite corpus uses canonical ABI encodings for its named recognized-selector
rows and separately checks the dirty-address constructor rejection. Its exact
scope is `canonical ABI endpoint rows plus named dirty-address constructor rejection; nested malformed dynamic ABI, empty/unknown/short dispatch, trailing calldata, and recognized-selector nonpayability are untested and excluded`.
Those excluded dispatch/calldata arms have no B2 equivalence claim. Malformed
callback/dependency return data is a separate external-call obligation and is
not silently classified as input-calldata coverage.

<!-- LIDO-TWG-CROSSCUT pause-sentinel -->
### Pause projection and infinite sentinel

For `pauseFor`, the projection is
`duration = 2^256 - 1 ? 2^256 - 1 : block.timestamp + duration`. For
`pauseUntil`, it is
`pauseUntilInclusive = 2^256 - 1 ? 2^256 - 1 : pauseUntilInclusive + 1`.
The disjunct is unconditional on the sentinel input. It is not weakened into a
premise excluding that input.

<!-- LIDO-TWG-CROSSCUT access-control -->
### Access control and authorization failures

Membership, admin lookup, and role mutations are logical-state surfaces.
Unauthorized result status agrees, but the known returndata differences are
`TWG-D01` and `TWG-D02`. The differential compares exact bytes and may not use
a status-only allowlist.

<!-- LIDO-TWG-CROSSCUT role-enumeration -->
### Role enumeration and collision domain

Membership and count are compared through a logical projection. Enumeration
order and out-of-range returndata retain their observable differences
`TWG-D03` and `TWG-D04`. Blanc's collision-refusing lookup domain is `TWG-D05`;
no theorem or fixture may assume global injectivity of the low-252-bit key.

<!-- LIDO-TWG-CROSSCUT exit-limit -->
### Exit-limit frame arithmetic

The logical projection contains maximum, previous limit, previous timestamp,
frame duration, and exits per frame. Current limit is calculated from elapsed
whole frames, capped by the maximum, with the named checked-arithmetic rows.
The corpus observes configured same-frame and whole-frame worlds; zero/unlimited
mode and partial-frame behavior are untested and excluded. Raw
packed/reference slots and Blanc's five flat words are not compared.

<!-- LIDO-TWG-CROSSCUT trigger-choreography -->
### Trigger choreography and dependencies

Comparison observes the exact outbound call targets, calldata, value, order,
success/revert handling, refund recipient, and final gateway ETH balance.
Locator, vault, and router code are bounded mocks in B2, not verified ports or
honesty premises of the Phase A theorems.

<!-- LIDO-TWG-CROSSCUT events-errors-rollback -->
### Events, errors, and rollback

Error payloads are compared exactly and differences require registry rows.
An outer revert rolls back this gateway's storage, ETH movement, logs, and
descendant effects according to EVM settlement; retained call-trace evidence
does not reclassify rolled-back effects as committed ones.

<!-- LIDO-TWG-CROSSCUT logical-state-projection -->
### Logical-state projection

Comparison maps the reference's keccak-derived pause, packed exit-limit, and
AccessControl storage to Blanc's pause word, five limit words, full-identity
role records, and filtered enumeration. Raw slots, storage roots/proofs, and
layout are deliberately outside equivalence. See `TWG-I01`.

<!-- LIDO-TWG-CROSSCUT finite-evidence -->
### Finite evidence

The B2 corpus has `71` cases and
`186` resource boundaries. It establishes
only the manifest-listed observations in the manifest-listed worlds. Passing
every row is not proof of the reference, exhaustive equality, future
enabledness, or behavior outside the coverage criterion.

<!-- LIDO-TWG-CROSSCUT gas-boundary -->
### Code size and named-path gas

The machine-filled comparison tables live in the deviation registry. Exact gas
identity and universal dominance are not claimed. Every measured positive
public final-action delta and the successful constructor cost must be repaired
or receive its own accepted gas-cost disposition; aggregate savings cannot
hide it. These `TWG-Gnn` cost rows do not expand the behavioral-deviation
inventory beyond `TWG-D01` through `TWG-D05`.

<!-- LIDO-TWG-CROSSCUT formal-proof-boundary -->
### Formal Blanc boundary

The runtime/artifact program is frozen at
`35a196fd50192aa269d6cb07699ea0910ad3c468`. The first compile-valid
pinned-target certificate is commit
`a0e04e7a69558b8744ced81ea4a3defdfc478d36`, which certifies that exact
program's pause-face, authorization, protected-surface, and
`PinnedPauseTarget` properties within
`[propext, Classical.choice, Quot.sound]`. The bundle's CircuitBreaker-cell
noninterference is derived from selected-route childlessness, not assumed.
These are Blanc-only theorems and say nothing about the deployed Solidity
runtime.

<!-- LIDO-TWG-CROSSCUT deployment-boundary -->
### Direct installation, not deployment-root verification

The Phase A theorems quantify over an exact compiled runtime installed at the
gateway account. B2 separately creates both artifacts from complete CREATE
inputs in finite EELS worlds. Neither channel proves arbitrary deployment,
mainnet inclusion, signing, propagation, a proxy shape, or a deployed
Solidity account invariant.

## Strongest honest port claim

The published finite claim is:

> For the exact Blanc runtime/artifact program at
> `35a196fd50192aa269d6cb07699ea0910ad3c468`, certified by the first
> compile-valid pinned-target proof commit
> `a0e04e7a69558b8744ced81ea4a3defdfc478d36`, Jaune pin
> `949cf97ee1956828a3ac0eb12a62c438656ba76e`, reference lock
> `8e92a23746c47a9b065f6c042c98d9913785c40c0f27e0a1f82cfc37c0effc0f`, and EELS commit
> `4198b9c5996713b268aed602739d5aa40e277694`, the exact compiled Blanc
> TriggerableWithdrawalsGateway implements the frozen 24-selector and
> six-event surface. Lean proves its stated pause-face, authorization, and
> protected-surface properties within
> `[propext, Classical.choice, Quot.sound]`; successful authorized
> `pauseFor(d)` writes
> `d = 2^256 - 1 ? 2^256 - 1 : block.timestamp + d`, the corresponding
> inclusive `pauseUntil` sentinel disjunct holds, `isPaused()` is truthful,
> and the compiled program discharges `PinnedPauseTarget` with selected-route
> noninterference proved rather than assumed. The exact Blanc and pinned
> reference artifacts agree on the published finite differential corpus under
> the pinned EELS oracle, subject to its stated projection and adequate-gas
> boundary, with all known differences declared in the deviation registry.

This does **not** claim verification of the Solidity or mainnet artifact;
byte/codehash/raw-storage identity; exhaustive equivalence; liveness;
universal gas; arbitrary deployment; mainnet role state; a port of the
locator, vault, or router; or the later CircuitBreaker-plus-target composition
theorem. The last item belongs to the separately authorized entry-3 successor.
