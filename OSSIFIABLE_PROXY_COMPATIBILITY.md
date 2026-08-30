# OssifiableProxy compatibility contract

<!-- OSSIFIABLE-PROXY-LOCK 1c9f380f2475e5a54eb870e4f41ceeb09a0f9c227271ad14900fe82b0df1b688 -->

This contract freezes the Solidity reference boundary and names the Blanc
proof families plus finite differential rows that support each port claim.
The row references are evidence on the published inputs, not verification of
the Solidity artifact or a universal-equivalence claim. Exact completion
candidate and immutable-result identities live in the Plans completion report.

## Constructor

<!-- OSSIFIABLE-PROXY-CONSTRUCTOR {"argumentTypes":["address","address","bytes"],"payable":false,"signature":"constructor(address,address,bytes)"} -->

| Field | Frozen Solidity boundary | Blanc port evidence |
|---|---|---|
| Signature | `constructor(address,address,bytes)` | `ProxyPairOssifiableConstructor` strict decoder and `ProxyPairOssifiableDeploymentMessage`; K01–K18 |
| State mutability | `nonpayable` | `ossifiableConstructorProgram_value_rejected`; K06 |
| Nonzero creation value | rejected before constructor body behavior | `ossifiableConstructorProgram_value_rejected` and whole-CREATE rollback; K06 |
| Canonical empty-data suffix | 128 bytes after the 4,207-byte creation template | `ossifiableEmptyDataCreateInput` layout and direct-CREATE theorem; K01 |
| Classification | functional interface | empty/nonempty constructor and both-slot deployment families; K01–K18 |

## Runtime endpoints

<!-- OSSIFIABLE-PROXY-ENDPOINT {"acceptsValue":false,"selector":"0x916f1fd7","signature":"proxy__getAdmin()","stateMutability":"view"} -->
### `proxy__getAdmin()`

| Field | Frozen Solidity boundary | Blanc port evidence |
|---|---|---|
| Selector / dispatch key | `0x916f1fd7` | `getAdmin_body_of_program`; G01, G02, G07 |
| State mutability | `view` | `getAdmin_exact_of_program`; G01, G02, G07 |
| Nonzero call value | rejected before endpoint body behavior | `getAdmin_with_value_reverts`; V01 |
| Classification | functional interface | exact 32-byte canonical address result; G01, G02, G07 |

<!-- OSSIFIABLE-PROXY-ENDPOINT {"acceptsValue":false,"selector":"0xad729a71","signature":"proxy__getImplementation()","stateMutability":"view"} -->
### `proxy__getImplementation()`

| Field | Frozen Solidity boundary | Blanc port evidence |
|---|---|---|
| Selector / dispatch key | `0xad729a71` | `getImplementation_body_of_program`; G03, G04 |
| State mutability | `view` | `getImplementation_exact_of_program`; G03, G04 |
| Nonzero call value | rejected before endpoint body behavior | `getImplementation_with_value_reverts`; V02 |
| Classification | functional interface | exact 32-byte canonical address result, independent of code presence; G03, G04 |

<!-- OSSIFIABLE-PROXY-ENDPOINT {"acceptsValue":false,"selector":"0x13351258","signature":"proxy__getIsOssified()","stateMutability":"view"} -->
### `proxy__getIsOssified()`

| Field | Frozen Solidity boundary | Blanc port evidence |
|---|---|---|
| Selector / dispatch key | `0x13351258` | `getIsOssified_body_of_program`; G05, G06 |
| State mutability | `view` | `getIsOssified_exact_of_program` / `getIsOssified_true_of_program`; G05, G06 |
| Nonzero call value | rejected before endpoint body behavior | `getIsOssified_with_value_reverts`; V03 |
| Classification | functional interface | exact false/true word from the functional admin slot; G05, G06 |

<!-- OSSIFIABLE-PROXY-ENDPOINT {"acceptsValue":false,"selector":"0xadcbc237","signature":"proxy__ossify()","stateMutability":"nonpayable"} -->
### `proxy__ossify()`

| Field | Frozen Solidity boundary | Blanc port evidence |
|---|---|---|
| Selector / dispatch key | `0xadcbc237` | `ossify_body_of_program`; O01–O03 |
| State mutability | `nonpayable` | active-admin and exact ossification routes; O01–O03 |
| Nonzero call value | rejected before endpoint body behavior | `ossify_with_value_reverts`; V04 |
| Classification | functional interface | `ossifyMutation_success_irreversible`; O01–O03 |

<!-- OSSIFIABLE-PROXY-ENDPOINT {"acceptsValue":false,"selector":"0x773f5be8","signature":"proxy__changeAdmin(address)","stateMutability":"nonpayable"} -->
### `proxy__changeAdmin(address)`

| Field | Frozen Solidity boundary | Blanc port evidence |
|---|---|---|
| Selector / dispatch key | `0x773f5be8` | `changeAdmin_body_of_program`; D01–D06 |
| State mutability | `nonpayable` | exact authorized/unauthorized/ossified routes; D01–D06 |
| Nonzero call value | rejected before endpoint body behavior | `changeAdmin_with_value_reverts`; V05 |
| Classification | functional interface | exact packed slot update, log, same-value, and rollback behavior; D01–D06 |

<!-- OSSIFIABLE-PROXY-ENDPOINT {"acceptsValue":false,"selector":"0x3ebdd0eb","signature":"proxy__upgradeTo(address)","stateMutability":"nonpayable"} -->
### `proxy__upgradeTo(address)`

| Field | Frozen Solidity boundary | Blanc port evidence |
|---|---|---|
| Selector / dispatch key | `0x3ebdd0eb` | `upgradeTo_body_of_program`; U01–U07 |
| State mutability | `nonpayable` | exact authorization and code-present/no-code routes; U01–U07 |
| Nonzero call value | rejected before endpoint body behavior | `upgradeTo_with_value_reverts`; V06 |
| Classification | functional interface | exact packed implementation update, log, same-value, and rollback behavior; U01–U07 |

<!-- OSSIFIABLE-PROXY-ENDPOINT {"acceptsValue":false,"selector":"0xd2f6ed4d","signature":"proxy__upgradeToAndCall(address,bytes,bool)","stateMutability":"nonpayable"} -->
### `proxy__upgradeToAndCall(address,bytes,bool)`

| Field | Frozen Solidity boundary | Blanc port evidence |
|---|---|---|
| Selector / dispatch key | `0xd2f6ed4d` | `upgradeToAndCall_decoded_route_of_program`; X01–X20 |
| State mutability | `nonpayable` | exact authorized/unauthorized/ossified outcomes; X01–X20 |
| Nonzero call value | rejected before endpoint body behavior | `upgradeToAndCall_with_value_reverts`; V07 |
| Classification | functional interface | skip/force/setup/rollback and ABI-boundary families; X01–X20 |

<!-- OSSIFIABLE-PROXY-ENDPOINT {"acceptsValue":true,"selector":null,"signature":"fallback","stateMutability":"payable"} -->
### `fallback`

| Field | Frozen Solidity boundary | Blanc port evidence |
|---|---|---|
| Selector / dispatch key | `unmatched/short calldata` | selector-miss/short-data theorems; F01–F04 |
| State mutability | `payable` | `processMessage_forwardingEnvelope`; F00–F16 |
| Nonzero call value | accepted | delegated child preserves proxy-context value; F05 |
| Classification | functional interface | exact child status/output/log/storage settlement; F00–F16 |

<!-- OSSIFIABLE-PROXY-ENDPOINT {"acceptsValue":true,"selector":null,"signature":"receive","stateMutability":"payable"} -->
### `receive`

| Field | Frozen Solidity boundary | Blanc port evidence |
|---|---|---|
| Selector / dispatch key | `empty calldata` | `runtimeSelectors_miss_of_data_nil`; F00, F05 |
| State mutability | `payable` | `processMessage_forwardingEnvelope`; F00, F05 |
| Nonzero call value | accepted | delegated child preserves proxy-context value and ETH transfer; F05 |
| Classification | functional interface | the same complete forwarding settlement as fallback; F00, F05 |

## Cross-cutting behavior

<!-- OSSIFIABLE-PROXY-CROSSCUT named-entry-nonpayability -->
### named-entry-nonpayability

All seven named selectors reject nonzero call value in compiler dispatch before authorization or endpoint-body behavior. The three getters are `view`; the four administrative entries are `nonpayable`.

Blanc port evidence: `named_call_with_value_reverts_before_endpoint` and its
seven endpoint corollaries; V01–V07.

<!-- OSSIFIABLE-PROXY-CROSSCUT fallback-receive-payability -->
### fallback-receive-payability

Fallback and receive are payable and delegate to the implementation; value is observed in proxy storage context by the delegated child.

Blanc port evidence: `processMessage_forwardingEnvelope` and the exact
delegatecall child-context/settlement projections; F00–F16, especially F05.

<!-- OSSIFIABLE-PROXY-CROSSCUT selector-dispatch -->
### selector-dispatch

The seven locked selectors are pairwise distinct. Empty calldata selects receive; unmatched selectors and 0–3-byte nonempty calldata select fallback.

Blanc port evidence: compiled linear-dispatch route plus
`runtimeSelectors_miss_of_data_nil` / `_one` / `_two` / `_three`; G01–X20 and
F00–F04.

<!-- OSSIFIABLE-PROXY-CROSSCUT abi-decoding-boundaries -->
### abi-decoding-boundaries

The lock records the head width, canonical minimum length, address-word, bool-word, dynamic-offset/length, and trailing-calldata boundary for every decoded endpoint.

Blanc port evidence: address and upgrade-and-call decoder theorems in
`ProxyPairOssifiableControl`, constructor decoder theorems in
`ProxyPairOssifiableConstructor`, and D06/U06/U07/X14–X20/K13–K18.

<!-- OSSIFIABLE-PROXY-CROSSCUT authorization-and-ossification-precedence -->
### authorization-and-ossification-precedence

For every administrative body, admin zero raises `ProxyIsOssified()` before caller comparison; otherwise a caller different from admin raises `NotAdmin()`.

Blanc port evidence: `ActiveAdminRoute` and
`UpgradeToAndCallDecodedRoute` precedence theorems; O03, D05, U05, X13.

<!-- OSSIFIABLE-PROXY-CROSSCUT upgrade-and-setup-reverts -->
### upgrade-and-setup-reverts

A new implementation without code uses `ERC1967: new implementation is not a contract`; an empty failed setup uses `Address: low-level delegate call failed`; nonempty child revert data is bubbled exactly.

Blanc port evidence: exact no-code and delegatecall-error payloads in
`ProxyPairOssifiableControlEffects`, setup settlement/rollback in
`ProxyPairOssifiableUpgradeToAndCall`; U03 and X07–X11.

<!-- OSSIFIABLE-PROXY-CROSSCUT event-surface -->
### event-surface

The three reachable event families are: `Upgraded(address)` → `0xbc7cd75a20ee27fd9adebab32041f755214dbc6bffa90cc0225b39da2e5c2d3b`; `AdminChanged(address,address)` → `0x7e644d79422f17c01e4894b5f4f588d331ebfa28653d42ae832dc59e38c9798f`; `ProxyOssified()` → `0x158b204828f9326d9bb3c2be9336986c14911b4a72b93d1801f207aac3c68b9f`.

Blanc port evidence: exact raw log constructors and successful effect theorems
in the control and constructor families; K01–K05, O01, D01–D03, U01–U03,
X01–X11.

<!-- OSSIFIABLE-PROXY-CROSSCUT error-and-string-surface -->
### error-and-string-surface

The custom errors are `NotAdmin()` → `0x7bfa4b9f`; `ProxyIsOssified()` → `0xb83646a9`. The inherited `Error(string)` messages are `ERC1967: new admin is the zero address`; `ERC1967: new implementation is not a contract`; `Address: low-level delegate call failed`.

Blanc port evidence: exact custom/string payload calls in
`ProxyPairOssifiableControlEffects` and constructor settlement; all negative
K/O/D/U/X rows plus V01–V07.

<!-- OSSIFIABLE-PROXY-CROSSCUT erc1967-functional-slots -->
### erc1967-functional-slots

The ERC-1967 words are a functional interoperability surface, not discardable storage-layout accidents: implementation `0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc`; admin `0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103`.

Blanc port evidence: derived `ProxyPair.implementationSlot` / `adminSlot`,
exact packed-read/write theorems, both-slot constructor fixture, and
K03–K05/X04–X06/F12–F13.

<!-- OSSIFIABLE-PROXY-CROSSCUT constructor-source-order -->
### constructor-source-order

Construction validates/writes implementation and emits `Upgraded`, optionally delegatecalls setup, then reads the post-setup admin, emits `AdminChanged`, validates nonzero new admin, and writes admin.

Blanc port evidence: implementation initialization, retained setup child,
post-setup admin, exact empty/nonempty constructor, and whole-CREATE families;
K01–K12.

<!-- OSSIFIABLE-PROXY-CROSSCUT delegation-returndata -->
### delegation-returndata

Fallback and receive copy complete delegatecall returndata and return or revert with that data; execution uses the proxy account/storage context.

Blanc port evidence: arbitrary-child forwarding envelope, clean/failed tail
constructors, exact proxy storage ownership, and F00–F16.

<!-- OSSIFIABLE-PROXY-CROSSCUT inherited-abi-only-declarations -->
### inherited-abi-only-declarations

`BeaconUpgraded(address)` is preserved in the raw compiler ABI as an inherited ABI-only declaration. It is excluded from the three-event behavioral surface because no OssifiableProxy external or constructor path calls the inherited internal beacon-upgrade emitter.

Blanc port evidence: the compiled program exposes only the three owned event
constructors; the exact 85-row corpus observes no `BeaconUpgraded`; the raw ABI
declaration remains reference-lock evidence only.

<!-- OSSIFIABLE-PROXY-CROSSCUT interface-vs-source-accidents -->
### interface-vs-source-accidents

Selectors, mutability/value behavior, errors, reachable events, delegation observations, constructor behavior, and both ERC-1967 slots are functional. Source offsets, incidental bytecode layout, exact code hashes, and gas are reference or measurement facts rather than automatic semantic obligations.

Blanc port evidence: compiled-byte equations prove Blanc's own artifacts;
reference agreement is limited to the finite corpus, while artifact sizes and
gas remain the separate frozen 25-cell measurement campaign.
