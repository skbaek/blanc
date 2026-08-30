# Lido OssifiableProxy in Blanc

This page is the public evidence map for Blanc's port of Lido's
`OssifiableProxy`. It records properties of Blanc's compiled programs and
finite comparisons with the selected Solidity reference. It does not verify
the deployed Solidity contract or claim byte identity, universal equivalence,
universal gas dominance, or global optimality.

## Exact reference boundary

The offline authority is
[`scripts/lido-ossifiable-proxy-reference.json`](../scripts/lido-ossifiable-proxy-reference.json),
checked by
[`scripts/check-lido-ossifiable-proxy-reference.sh`](../scripts/check-lido-ossifiable-proxy-reference.sh).
It pins Lido core v4.0.0 at commit
`17005714f151e5502c559932319a3f2f74ac2436`, OpenZeppelin 4.4.1, solc
`0.8.9+commit.e5eed63a` with the locked settings, the complete source closure,
and the selected WithdrawalQueueERC721 proxy creation transaction. Independent
source/compiler and transaction/deployed-runtime routes reproduce the same
2,497-byte Solidity runtime.

[`OSSIFIABLE_PROXY_COMPATIBILITY.md`](../OSSIFIABLE_PROXY_COMPATIBILITY.md)
freezes the constructor, seven named selectors, fallback and receive paths,
events, errors, ABI boundaries, authorization precedence, delegation behavior,
and both functional ERC-1967 slots. The reference gate keeps that document
synchronized with the membership-sensitive lock and runs 36 live falsifier
cases.

## Blanc programs and artifacts

The runtime and creation programs are owned by
[`Blanc/ProxyPairOssifiableProgram.lean`](../Blanc/ProxyPairOssifiableProgram.lean)
and
[`Blanc/ProxyPairOssifiableDeploy.lean`](../Blanc/ProxyPairOssifiableDeploy.lean).
The generated-byte owner
[`Blanc/ProxyPairOssifiableArtifacts.lean`](../Blanc/ProxyPairOssifiableArtifacts.lean)
ties their compiler outputs to explicit byte lists, exact lengths, SHA-256,
and Ethereum Keccak-256 identities:

| Blanc artifact | Bytes | SHA-256 | Keccak-256 |
|---|---:|---|---|
| constructor prefix | 1,249 | `e07f2fbf0343cb5dfc3be9a83967e44eb3169374b507ed48ae3d45f942bde219` | `0x5ebc447c4900f540c52c27cff2887d2245d3fabe95b4ab490980f3d2cc066269` |
| returned runtime | 2,188 | `d818399e2c428c8be8aafb01e8b22d24c30a456955d004465dbae61778afa53c` | `0x20c1fdfe3ed4a0d85d42e4fff8d8b5613406c14f23281d6aae6c763a18c0b502` |
| creation template | 3,437 | `e466c9e5f98c9bee2062a4b5ddd8a06247fc922e883974289e2ae12777e2c8ff` | `0x3309623a7660d6a7947a5f3594c65aae15779ee5b5ec840f90c01923ffd63865` |

The network-free
[`scripts/check-lido-ossifiable-proxy-artifacts.sh`](../scripts/check-lido-ossifiable-proxy-artifacts.sh)
gate checks the generator-owned Lean/JSON surfaces and runs 20 independent
temporary-copy controls, including a coherent Lean+JSON laundering attempt.
These are Blanc artifact identities, not Solidity byte-identity claims.

## Formal proof surface

The main proof owners are:

- [`Blanc/ProxyPairOssifiableForwarding.lean`](../Blanc/ProxyPairOssifiableForwarding.lean),
  which proves the exact wrapper around an arbitrary certified delegated child
  and separately states the implementation-specific transport obligation for
  direct-to-delegated gas, depth, access-set, transfer, code-address, target,
  and storage-owner changes;
- [`Blanc/ProxyPairOssifiableControl.lean`](../Blanc/ProxyPairOssifiableControl.lean),
  [`Blanc/ProxyPairOssifiableControlEffects.lean`](../Blanc/ProxyPairOssifiableControlEffects.lean),
  and
  [`Blanc/ProxyPairOssifiableUpgradeToAndCall.lean`](../Blanc/ProxyPairOssifiableUpgradeToAndCall.lean),
  which cover all seven named entries, compiler nonpayability, authorization
  precedence, exact errors/logs, packed slot effects, setup settlement,
  rollback, and ossification irreversible through the administrative control
  entries; and
- the `ProxyPairOssifiableConstructor*`,
  [`Blanc/ProxyPairOssifiableBothSlotCreate.lean`](../Blanc/ProxyPairOssifiableBothSlotCreate.lean),
  and
  [`Blanc/ProxyPairOssifiableBothSlotDeployment.lean`](../Blanc/ProxyPairOssifiableBothSlotDeployment.lean)
  family, which proves strict `(address,address,bytes)` decoding, the source
  order `Upgraded` → optional setup → `AdminChanged`, setup ownership of proxy
  storage, both-slot mutation, exact runtime return, direct-CREATE settlement,
  and whole-CREATE rollback.

Public headline theorems are individually pinned by the repository claim and
axiom audits. Their admitted trust surface is limited to `propext`,
`Classical.choice`, and `Quot.sound`; fixed Keccak decisions use the existing
separate kernel route.

## Finite differential evidence

The 85-case corpus is frozen in
[`scripts/fixtures/lido-ossifiable-proxy/differential-manifest.json`](../scripts/fixtures/lido-ossifiable-proxy/differential-manifest.json)
and mapped in
[`scripts/fixtures/lido-ossifiable-proxy/DIFFERENTIAL.md`](../scripts/fixtures/lido-ossifiable-proxy/DIFFERENTIAL.md).
It covers construction, every getter and control entry, all
upgrade-and-call arms, payable fallback/receive, value rejection, malformed
ABI boundaries, missing code, revert/exception normalization, exact
logs/payloads, ordered child-call observations, and rollback.

The optimized candidate executes all 85 rows in fresh pinned EELS Prague
worlds with 85/85 semantic agreements and zero skipped rows. Seven independent
falsifier families exercise reference substitution, selector routing,
event/error bytes, state projection, rollback, child-call observation, and
corpus/result mutation. The ordered child-call projection freezes caller, code
address, input, storage owner, value, and outcome, but does not compare child
gas. This is finite agreement on the published inputs, not universal
equivalence, a same-budget claim for GAS-sensitive children, or verification of
the deployed Solidity artifact.

## Efficiency evidence

The immutable campaign contract is frozen in
[`scripts/fixtures/lido-ossifiable-proxy/performance-manifest.json`](../scripts/fixtures/lido-ossifiable-proxy/performance-manifest.json)
and described in
[`scripts/fixtures/lido-ossifiable-proxy/README.md`](../scripts/fixtures/lido-ossifiable-proxy/README.md).
It fixes two size cells, 23 direct Prague gas cells, a denominator of 25, and a
threshold of at least 13 strict Blanc wins. Every measured cell first requires
semantic agreement.

The planned semantic-preserving optimization replaces each product-private
address read schedule `PUSH0; NOT; PUSH1 0xa0; SHL; NOT; AND` with the equal
`PUSH0; NOT; PUSH1 0x60; SHR; AND`; strict ABI dirty-address guards and packed
write masks are unchanged. The resulting matrix is 25 strict Blanc wins, zero
ties, zero losses, and zero incomparables:

| Cell | Reference | Blanc | Cell | Reference | Blanc |
|---|---:|---:|---|---:|---:|
| A1 | 2,497 bytes | 2,188 bytes | A2 | 4,207 bytes | 3,437 bytes |
| A3 | 550,980 gas | 487,814 gas | A4 | 573,987 gas | 510,079 gas |
| F1 | 5,099 | 4,958 | F2 | 599 | 458 |
| F3 | 5,081 | 4,938 | F4 | 581 | 438 |
| F5 | 5,198 | 5,063 | F6 | 5,199 | 5,062 |
| F7 | 4,969 | 4,943 | C1 | 2,390 | 2,198 |
| C2 | 2,458 | 2,220 | C3 | 2,389 | 2,245 |
| C4 | 7,280 | 6,826 | C5 | 11,484 | 11,170 |
| C6 | 12,044 | 11,468 | C7 | 34,973 | 33,705 |
| C8 | 34,899 | 33,715 | C9 | 7,756 | 7,477 |
| N1 | 2,606 | 2,414 | N2 | 2,566 | 2,397 |
| N3 | 4,292 | 3,867 | N4 | 5,349 | 5,088 |
| N5 | 12,874 | 11,643 | — | — | — |

The report-only current-mainnet BPO2 replay in
[`scripts/reference/lido-ossifiable-proxy/current-mainnet-results.json`](../scripts/reference/lido-ossifiable-proxy/current-mainnet-results.json)
represents 21 transaction scenarios with 21/21 semantic agreements, 19 lower
Blanc receipt-gas rows, and two ties. A1/A2 are not transactions; F2/F4 require
pre-warmed message state not representable by the singleton transaction API.
The BPO2 replay does not alter or double-count the primary Prague score.

## Deviations and claim boundary

[`OSSIFIABLE_PROXY_DEVIATIONS.md`](../OSSIFIABLE_PROXY_DEVIATIONS.md) records
the constructor memory schedule, redundant Solidity implementation-code check,
discarded successful setup returndata, intrinsic direct/delegated context
delta, and the reference-versus-Blanc forwarded-child gas difference. That
last difference can change an arbitrary GAS-sensitive implementation or setup
child's behavior and is the one accepted known ordinary-behavior deviation;
the 85 fixed rows agree on their published gas-excluding projection. No other
ordinary-behavior deviation is accepted or known. Any later mismatch must be
repaired or dispositioned there before the claim can move.

The exact completion-candidate identity, immutable result digests,
independent-review verdicts, ordered gate verdicts, and downstream composition
boundary are recorded in the Plans completion report. Even on completion this
work does not claim byte identity, deployed-Solidity verification, universal
observational equivalence, universal gas dominance, current mainnet roles or
state, arbitrary-block deployment, or a downstream Lido target composition.
