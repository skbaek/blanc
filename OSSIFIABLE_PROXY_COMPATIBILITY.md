# OssifiableProxy compatibility contract

<!-- OSSIFIABLE-PROXY-LOCK 1c9f380f2475e5a54eb870e4f41ceeb09a0f9c227271ad14900fe82b0df1b688 -->

This generated skeleton freezes the Solidity reference boundary before the Blanc port
claim is filled in. `planned` means the reference side is locked while port evidence is
still required; it is not an equivalence claim.

## Constructor

<!-- OSSIFIABLE-PROXY-CONSTRUCTOR {"argumentTypes":["address","address","bytes"],"payable":false,"signature":"constructor(address,address,bytes)"} -->

| Field | Frozen Solidity boundary | Blanc port evidence |
|---|---|---|
| Signature | `constructor(address,address,bytes)` | planned |
| State mutability | `nonpayable` | planned |
| Nonzero creation value | rejected before constructor body behavior | planned |
| Canonical empty-data suffix | 128 bytes after the 4,207-byte creation template | planned |
| Classification | functional interface | planned |

## Runtime endpoints

<!-- OSSIFIABLE-PROXY-ENDPOINT {"acceptsValue":false,"selector":"0x916f1fd7","signature":"proxy__getAdmin()","stateMutability":"view"} -->
### `proxy__getAdmin()`

| Field | Frozen Solidity boundary | Blanc port evidence |
|---|---|---|
| Selector / dispatch key | `0x916f1fd7` | planned |
| State mutability | `view` | planned |
| Nonzero call value | rejected before endpoint body behavior | planned |
| Classification | functional interface | planned |

<!-- OSSIFIABLE-PROXY-ENDPOINT {"acceptsValue":false,"selector":"0xad729a71","signature":"proxy__getImplementation()","stateMutability":"view"} -->
### `proxy__getImplementation()`

| Field | Frozen Solidity boundary | Blanc port evidence |
|---|---|---|
| Selector / dispatch key | `0xad729a71` | planned |
| State mutability | `view` | planned |
| Nonzero call value | rejected before endpoint body behavior | planned |
| Classification | functional interface | planned |

<!-- OSSIFIABLE-PROXY-ENDPOINT {"acceptsValue":false,"selector":"0x13351258","signature":"proxy__getIsOssified()","stateMutability":"view"} -->
### `proxy__getIsOssified()`

| Field | Frozen Solidity boundary | Blanc port evidence |
|---|---|---|
| Selector / dispatch key | `0x13351258` | planned |
| State mutability | `view` | planned |
| Nonzero call value | rejected before endpoint body behavior | planned |
| Classification | functional interface | planned |

<!-- OSSIFIABLE-PROXY-ENDPOINT {"acceptsValue":false,"selector":"0xadcbc237","signature":"proxy__ossify()","stateMutability":"nonpayable"} -->
### `proxy__ossify()`

| Field | Frozen Solidity boundary | Blanc port evidence |
|---|---|---|
| Selector / dispatch key | `0xadcbc237` | planned |
| State mutability | `nonpayable` | planned |
| Nonzero call value | rejected before endpoint body behavior | planned |
| Classification | functional interface | planned |

<!-- OSSIFIABLE-PROXY-ENDPOINT {"acceptsValue":false,"selector":"0x773f5be8","signature":"proxy__changeAdmin(address)","stateMutability":"nonpayable"} -->
### `proxy__changeAdmin(address)`

| Field | Frozen Solidity boundary | Blanc port evidence |
|---|---|---|
| Selector / dispatch key | `0x773f5be8` | planned |
| State mutability | `nonpayable` | planned |
| Nonzero call value | rejected before endpoint body behavior | planned |
| Classification | functional interface | planned |

<!-- OSSIFIABLE-PROXY-ENDPOINT {"acceptsValue":false,"selector":"0x3ebdd0eb","signature":"proxy__upgradeTo(address)","stateMutability":"nonpayable"} -->
### `proxy__upgradeTo(address)`

| Field | Frozen Solidity boundary | Blanc port evidence |
|---|---|---|
| Selector / dispatch key | `0x3ebdd0eb` | planned |
| State mutability | `nonpayable` | planned |
| Nonzero call value | rejected before endpoint body behavior | planned |
| Classification | functional interface | planned |

<!-- OSSIFIABLE-PROXY-ENDPOINT {"acceptsValue":false,"selector":"0xd2f6ed4d","signature":"proxy__upgradeToAndCall(address,bytes,bool)","stateMutability":"nonpayable"} -->
### `proxy__upgradeToAndCall(address,bytes,bool)`

| Field | Frozen Solidity boundary | Blanc port evidence |
|---|---|---|
| Selector / dispatch key | `0xd2f6ed4d` | planned |
| State mutability | `nonpayable` | planned |
| Nonzero call value | rejected before endpoint body behavior | planned |
| Classification | functional interface | planned |

<!-- OSSIFIABLE-PROXY-ENDPOINT {"acceptsValue":true,"selector":null,"signature":"fallback","stateMutability":"payable"} -->
### `fallback`

| Field | Frozen Solidity boundary | Blanc port evidence |
|---|---|---|
| Selector / dispatch key | `unmatched/short calldata` | planned |
| State mutability | `payable` | planned |
| Nonzero call value | accepted | planned |
| Classification | functional interface | planned |

<!-- OSSIFIABLE-PROXY-ENDPOINT {"acceptsValue":true,"selector":null,"signature":"receive","stateMutability":"payable"} -->
### `receive`

| Field | Frozen Solidity boundary | Blanc port evidence |
|---|---|---|
| Selector / dispatch key | `empty calldata` | planned |
| State mutability | `payable` | planned |
| Nonzero call value | accepted | planned |
| Classification | functional interface | planned |

## Cross-cutting behavior

<!-- OSSIFIABLE-PROXY-CROSSCUT named-entry-nonpayability -->
### named-entry-nonpayability

All seven named selectors reject nonzero call value in compiler dispatch before authorization or endpoint-body behavior. The three getters are `view`; the four administrative entries are `nonpayable`.

Blanc port evidence: planned.

<!-- OSSIFIABLE-PROXY-CROSSCUT fallback-receive-payability -->
### fallback-receive-payability

Fallback and receive are payable and delegate to the implementation; value is observed in proxy storage context by the delegated child.

Blanc port evidence: planned.

<!-- OSSIFIABLE-PROXY-CROSSCUT selector-dispatch -->
### selector-dispatch

The seven locked selectors are pairwise distinct. Empty calldata selects receive; unmatched selectors and 0–3-byte nonempty calldata select fallback.

Blanc port evidence: planned.

<!-- OSSIFIABLE-PROXY-CROSSCUT abi-decoding-boundaries -->
### abi-decoding-boundaries

The lock records the head width, canonical minimum length, address-word, bool-word, dynamic-offset/length, and trailing-calldata boundary for every decoded endpoint.

Blanc port evidence: planned.

<!-- OSSIFIABLE-PROXY-CROSSCUT authorization-and-ossification-precedence -->
### authorization-and-ossification-precedence

For every administrative body, admin zero raises `ProxyIsOssified()` before caller comparison; otherwise a caller different from admin raises `NotAdmin()`.

Blanc port evidence: planned.

<!-- OSSIFIABLE-PROXY-CROSSCUT upgrade-and-setup-reverts -->
### upgrade-and-setup-reverts

A new implementation without code uses `ERC1967: new implementation is not a contract`; an empty failed setup uses `Address: low-level delegate call failed`; nonempty child revert data is bubbled exactly.

Blanc port evidence: planned.

<!-- OSSIFIABLE-PROXY-CROSSCUT event-surface -->
### event-surface

The three reachable event families are: `Upgraded(address)` → `0xbc7cd75a20ee27fd9adebab32041f755214dbc6bffa90cc0225b39da2e5c2d3b`; `AdminChanged(address,address)` → `0x7e644d79422f17c01e4894b5f4f588d331ebfa28653d42ae832dc59e38c9798f`; `ProxyOssified()` → `0x158b204828f9326d9bb3c2be9336986c14911b4a72b93d1801f207aac3c68b9f`.

Blanc port evidence: planned.

<!-- OSSIFIABLE-PROXY-CROSSCUT error-and-string-surface -->
### error-and-string-surface

The custom errors are `NotAdmin()` → `0x7bfa4b9f`; `ProxyIsOssified()` → `0xb83646a9`. The inherited `Error(string)` messages are `ERC1967: new admin is the zero address`; `ERC1967: new implementation is not a contract`; `Address: low-level delegate call failed`.

Blanc port evidence: planned.

<!-- OSSIFIABLE-PROXY-CROSSCUT erc1967-functional-slots -->
### erc1967-functional-slots

The ERC-1967 words are a functional interoperability surface, not discardable storage-layout accidents: implementation `0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc`; admin `0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103`.

Blanc port evidence: planned.

<!-- OSSIFIABLE-PROXY-CROSSCUT constructor-source-order -->
### constructor-source-order

Construction validates/writes implementation and emits `Upgraded`, optionally delegatecalls setup, then reads the post-setup admin, emits `AdminChanged`, validates nonzero new admin, and writes admin.

Blanc port evidence: planned.

<!-- OSSIFIABLE-PROXY-CROSSCUT delegation-returndata -->
### delegation-returndata

Fallback and receive copy complete delegatecall returndata and return or revert with that data; execution uses the proxy account/storage context.

Blanc port evidence: planned.

<!-- OSSIFIABLE-PROXY-CROSSCUT inherited-abi-only-declarations -->
### inherited-abi-only-declarations

`BeaconUpgraded(address)` is preserved in the raw compiler ABI as an inherited ABI-only declaration. It is excluded from the three-event behavioral surface because no OssifiableProxy external or constructor path calls the inherited internal beacon-upgrade emitter.

Blanc port evidence: planned.

<!-- OSSIFIABLE-PROXY-CROSSCUT interface-vs-source-accidents -->
### interface-vs-source-accidents

Selectors, mutability/value behavior, errors, reachable events, delegation observations, constructor behavior, and both ERC-1967 slots are functional. Source offsets, incidental bytecode layout, exact code hashes, and gas are reference or measurement facts rather than automatic semantic obligations.

Blanc port evidence: planned.
