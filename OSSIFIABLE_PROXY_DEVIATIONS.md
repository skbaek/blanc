# OssifiableProxy deviation and drift registry

This registry classifies known differences between Blanc's OssifiableProxy
port and the exact Lido v4.0.0 reference locked by
`scripts/lido-ossifiable-proxy-reference.json`. The selected deployed evidence
is the WithdrawalQueueERC721 proxy creation transaction named by that lock.
It is an oracle and provenance anchor, not a Solidity-verification claim.

The registry is intentionally non-exhaustive. Newly discovered observable
differences must be repaired or added here with a disposition; they may not be
silently excluded from the port claim.

## Known ordinary-behavior deviation

One observable deviation is accepted and declared. Blanc's cheaper wrapper and
setup schedules can leave a different amount of gas at the `GAS` immediately
before `DELEGATECALL`, so EIP-150 can give the delegated child a different gas
budget than the Solidity reference. A GAS-sensitive implementation or setup
child can therefore choose a different status, output, log, or storage effect
even when both outer calls have otherwise adequate gas. G-5 records the priced
project stance; it is distinct from G-4's direct-target-versus-delegated-child
transport boundary.

Apart from G-5, no ordinary-behavior deviation is accepted or currently known.
Blanc is intended to agree on the ordinary-call and direct-CREATE surface frozen
in `OSSIFIABLE_PROXY_COMPATIBILITY.md`, including malformed ABI boundaries,
functional ERC-1967 slot words, authorization precedence, setup rollback,
event and error bytes, fallback/receive routing, and complete delegated
returndata, subject to the exact evidence boundary below.

This is not a universal-equivalence claim. The committed 85-case corpus has
executed with 85/85 semantic agreements and zero skipped rows at the optimized
Blanc checkpoint. Those rows agree on their published projection; the ordered
child-call projection does not compare child gas. That finite agreement is
evidence on the published inputs, not proof or verification of the deployed
Solidity artifact and not evidence that an arbitrary GAS-sensitive child sees
the same budget.

## Accepted low-level implementation differences

The following are freedoms rather than ordinary-behavior deviations:

- Blanc source organization, program structure, dispatcher shape, stack and
  memory strategy, instruction selection, compiler route, and internal helper
  boundaries;
- runtime, creation-template, and complete-CREATE byte identity, length, code
  hash, and source offsets;
- exact gas consumption, gas-left observations, memory expansion schedule,
  warm-address and warm-storage bookkeeping, subject to the explicit
  adequate-gas and transport boundaries of the proved statements;
- the synthetic address and world used by a direct-CREATE proof fixture; and
- proof representation, trace certificates, and storage-projection machinery.

Blanc proves equations from its product programs to its own measured compiler
artifacts. It does not reproduce or verify the deployed Solidity bytecode.
Both ERC-1967 storage words are excluded from these freedoms: they are a
functional interoperability surface and are matched exactly.

## Known gas, exceptional-boundary, and child-budget differences

These rows are observable through gas, out-of-gas boundaries, warm-set state,
transaction receipts, or delegated-child behavior. G-1 through G-3 do not by
themselves authorize a different successful or ordinary reverting result for
the fixed compared child under adequate gas. G-5 is the explicit exception:
an arbitrary GAS-sensitive child may behave differently because its forwarded
budget may differ.

| ID | Reference behavior | Blanc behavior | Observable consequence | Stance | Evidence |
|---|---|---|---|---|---|
| G-1 | Solidity's constructor ABI decoder copies and expands its dynamic argument representation according to solc 0.8.9's generated decoder schedule. | Blanc validates the same accepted/rejected argument boundaries but copies the declared setup payload incrementally into its fixed scratch region. | Memory expansion charges and the exact gas point at which malformed or underfunded creation halts may differ. | Priced implementation difference: the public ABI boundary is retained; exact gas and inadequate-gas liveness are outside semantic equivalence and are measured separately. | `Blanc/ProxyPairOssifiableDeploy.lean`; K01–K18; A3/A4 and their completion-threshold diagnostics. |
| G-2 | OpenZeppelin's upgrade-with-call path checks that the new implementation has code when storing it and performs a second contract check in the inherited low-level delegatecall helper. | Blanc performs the semantically effective pre-write code check once and then delegates to the same resolved implementation without the redundant second check. | Successful and no-code branches use different gas and address-warming schedules; an OOG boundary can differ. No intervening external execution can remove code between the two reference checks. | Measured semantic-preserving implementation choice. All applicable differential rows agree; C5–C8, N4, and N5 are strict Blanc wins in the frozen matrix. | `Blanc/ProxyPairOssifiableProgram.lean`; U01–U07 and X01–X20; the frozen 25-cell matrix. |
| G-3 | The inherited Solidity helper materializes successful setup returndata before the constructor later discards it. | Blanc discards successful setup returndata directly after the child reports success. Revert data is still copied and either bubbled exactly or replaced by the inherited empty-data reason. | Successful nonempty setup has a different returndata-copy/memory cost and can cross a different OOG boundary; final installed state, logs, and runtime are unchanged with adequate gas. | Measured semantic-preserving implementation choice. Setup success/failure and rollback rows agree; A4, C7, C8, and N5 are strict Blanc wins. | `Blanc/ProxyPairOssifiableProgram.lean`; K02–K05 and X01–X11; the frozen 25-cell matrix. |
| G-4 | A direct call to the implementation and the proxy's delegated child enter with different gas, depth, access sets, transfer flag, code address, current target, and storage owner. | Blanc states those differences explicitly and does not assert whole-message direct/delegated equivalence for arbitrary code. | GAS-, depth-, access-, transfer-, code-address-, or storage-owner-sensitive implementation properties require a separate transport proof; some direct and proxied executions can intentionally differ. | Boundary clarification, not a port deviation: this is intrinsic to proxy delegation and is exposed rather than normalized away. | `Blanc/DelegatecallEnvelope.lean`; `Blanc/ProxyPairOssifiableForwarding.lean`. |
| G-5 | The Solidity proxy executes its own compiler-generated dispatch, checks, decoding, memory, and returndata schedule before reading `GAS` for fallback/receive or constructor/runtime setup `DELEGATECALL`. | Blanc executes its shorter compiled schedule before the corresponding `GAS`; in particular, it omits the redundant second implementation-code check and can discard successful setup returndata earlier. | The EIP-150 child budget can differ. A GAS-sensitive delegated implementation or setup child can branch differently and thereby change status, output, logs, or proxy-owned storage even when both outer calls have ample gas. The fixed 85 rows agree on their declared projection but do not compare child gas. | Accepted priced consequence of the measured smaller/cheaper implementation. Deployers whose implementation behavior depends on exact `gasleft()` must discharge a budget-sensitive compatibility argument or choose a fixed-gas wrapper; no cross-artifact universal equivalence is claimed. | `Blanc/ProxyPairProgram.lean`; `Blanc/ProxyPairOssifiableProgram.lean`; `Blanc/ProxyPairOssifiableForwarding.lean`; F00–F16, K02–K05, X01–X11; the frozen 25-cell matrix. |

The frozen 25-cell campaign reports 25 strict Blanc wins and no ties, losses,
or incomparables after the planned address-mask optimization. Every cell's
semantic projection agrees. A cheaper semantically wrong run remains
unscoreable, and any later mismatch must be repaired or registered before the
port claim can move.

## Explicit equivalence exclusions

The completed claim will not include:

- byte identity, code-hash identity, or verification of the selected deployed
  Solidity contract;
- universal observational equivalence, universal gas dominance, global
  optimality, or liveness below stated gas premises;
- equality of gas, access sets, depth, transfer context, or implementation
  `gasleft()` between a direct target call and the delegated child;
- an arbitrary-block deployment root, the historical CREATE address derivation,
  current mainnet admin/implementation state, or transaction propagation;
- delegatecall-as-library use of the proxy runtime, CREATE2/factory deployment,
  UUPS/beacon/transparent-proxy behavior, or additional named proxy/control
  selectors outside the frozen seven-entry surface; unmatched selectors and
  0–3-byte calldata remain covered by fallback; or
- a later Lido target composition, upgrade relation, migration theorem, or
  one-proxy-many-implementations arrangement.

These exclusions do not relax the exact ordinary-call payloads, event order,
rollback, functional slots, payable fallback/receive behavior, or constructor
source order recorded by the compatibility contract.

## Reference quirks intentionally matched

The following can look surprising but are target behavior, not deviations:

- all seven named calls reject nonzero value in the compiler wrapper before
  endpoint decoding, authorization, code checks, writes, or logs;
- admin zero yields `ProxyIsOssified()` before caller comparison;
- same-value admin and implementation changes still perform the source writes
  and emit their events;
- `_changeAdmin` emits its raw `AdminChanged` before rejecting a zero new
  admin, with ordinary settlement rolling the log and preceding effects back;
- ossification writes zero directly and emits `AdminChanged(previous,0)` then
  `ProxyOssified()`, after which every control entry remains irreversibly
  ossified;
- constructor setup runs after `Upgraded` and before `_changeAdmin`; it owns
  proxy storage and may alter either ERC-1967 slot. `AdminChanged` reads the
  post-setup admin, and the final admin write preserves that raw word's upper
  96 bits while replacing its low address bits;
- empty setup data skips delegatecall, while nonempty data or a true force flag
  invokes setup. Empty child revert data receives the inherited fallback
  string; nonempty data is bubbled verbatim;
- unaligned and noncanonical in-bounds dynamic offsets and trailing bytes are
  accepted where solc 0.8.9 accepts them, while dirty address/bool words,
  truncated data, and the uint64 allocation boundary follow the locked decoder
  outcomes;
- empty calldata selects receive; nonempty unmatched and 0–3-byte calldata
  select fallback; and
- fallback/receive preserve the proxy as storage owner and return or revert
  with the child's complete returndata, including the missing-code case.
