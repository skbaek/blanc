# OssifiableProxy frozen differential corpus

This directory freezes the semantic input corpus for G4-7. It contains definitions only: no runner, results, score data, schema, proof, gate, or implemented falsifier.

Current format version 2 supersedes result-free version 1 digest `6ddf76545a556a2e5d10f10b18ffa07fcf8dbadaa1d31d55b3a8d8b967ba5c1e`. The only authority change is the imported performance manifest's pre-result correction of its malformed `fallback-256` hex; all 85 rows, their order, projections, and local fixtures are unchanged.

The corpus imports `scripts/fixtures/lido-ossifiable-proxy/performance-manifest.json` at corrected campaign digest `d257394b6eb56b02072b68037896a863e96a42f405690423024bc6b432f34eaa`. Shared addresses, accounts, environment, access sets, constructor tuples, and common mocks resolve there. The local manifest adds only the malformed/boundary inputs, special proxy state, and exact mock bytecode needed by these rows. Solidity is bound to `scripts/lido-ossifiable-proxy-reference.json` (document SHA-256 `1c9f380f2475e5a54eb870e4f41ceeb09a0f9c227271ad14900fe82b0df1b688`) and its `/artifacts/creationTemplate` and `/artifacts/runtime` keys. Blanc is bound prospectively to `scripts/eval-lido-ossifiable-proxy-artifacts.lean`; a later result must pin the exact evaluated commit and emitted artifact digests.

Manifest canonical SHA-256: `538e9dd3c6f2e1c52a4dd559f6b48dd9f0d75eb478b11a7299170ecde904e7ab`. The digest covers the parsed document with `/campaign/digest/value` set to the empty string, canonicalized with sorted keys and compact separators. The denominator and order are fixed at 85 rows.

## Coverage map

| Family | Count | Ordered case IDs |
|---|---:|---|
| constructor | 18 | K01, K02, K03, K04, K05, K06, K07, K08, K09, K10, K11, K12, K13, K14, K15, K16, K17, K18 |
| getter | 7 | G01, G02, G03, G04, G05, G06, G07 |
| control | 16 | O01, O02, O03, D01, D02, D03, D04, D05, D06, U01, U02, U03, U04, U05, U06, U07 |
| upgrade-and-call | 20 | X01, X02, X03, X04, X05, X06, X07, X08, X09, X10, X11, X12, X13, X14, X15, X16, X17, X18, X19, X20 |
| fallback | 17 | F00, F01, F02, F03, F04, F05, F06, F07, F08, F09, F10, F11, F12, F13, F14, F15, F16 |
| value-rejection | 7 | V01, V02, V03, V04, V05, V06, V07 |

### constructor

| ID | Arm | Frozen world |
|---|---|---|
| K01 | success | canonical empty-data creation succeeds |
| K02 | success | nonempty constructor setup writes the fixture slot |
| K03 | success | constructor setup replaces the implementation slot |
| K04 | success | constructor setup replaces admin before post-setup AdminChanged ordering |
| K05 | success | constructor setup replaces both ERC-1967 slots before final admin write |
| K06 | negative | nonpayable constructor rejects value |
| K07 | negative | zero final admin reverts the whole create |
| K08 | negative | missing-code initial implementation is rejected |
| K09 | negative | empty setup revert becomes the inherited low-level string error |
| K10 | negative | nonempty setup revert bytes bubble exactly |
| K11 | negative | setup mutates both slots then reverts; the whole create rolls back |
| K12 | negative | InvalidOpcode setup child becomes the inherited low-level string error |
| K13 | negative | 127-byte constructor suffix is malformed |
| K14 | negative | dirty high bits in constructor address are rejected |
| K15 | negative | constructor dynamic offset outside input is rejected |
| K16 | negative | constructor dynamic length overrun is rejected |
| K17 | success | constructor trailing byte is accepted |
| K18 | negative | constructor bytes length 2^64 returns exact Panic(0x41) before implementation effects |

### getter

| ID | Arm | Frozen world |
|---|---|---|
| G01 | success | admin getter in unossified state |
| G02 | success | admin getter in ossified state returns zero |
| G03 | success | implementation getter returns a code-bearing address |
| G04 | success | implementation getter returns an address with no code |
| G05 | success | ossification getter is false |
| G06 | success | ossification getter is true |
| G07 | success | getter accepts trailing calldata |

### control

| ID | Arm | Frozen world |
|---|---|---|
| O01 | success | admin ossifies with two ordered logs |
| O02 | negative | outsider cannot ossify |
| O03 | negative | ossified error precedes caller mismatch |
| D01 | success | admin changes to a new admin |
| D02 | success | same-value admin change still emits AdminChanged |
| D03 | negative | zero admin change reverts atomically |
| D04 | negative | outsider cannot change admin |
| D05 | negative | ossified error precedes caller mismatch for changeAdmin |
| D06 | negative | short address argument is rejected |
| U01 | success | upgrade to valid new implementation |
| U02 | success | same-value implementation upgrade still emits Upgraded |
| U03 | negative | upgrade to missing-code implementation reverts atomically |
| U04 | negative | outsider cannot upgrade |
| U05 | negative | ossified error precedes caller mismatch for upgrade |
| U06 | negative | dirty address argument is rejected |
| U07 | success | upgrade accepts trailing calldata |

### upgrade-and-call

| ID | Arm | Frozen world |
|---|---|---|
| X01 | success | empty setup with force=false skips child call |
| X02 | success | empty setup with force=true executes child |
| X03 | success | nonempty setup succeeds |
| X04 | success | setup changes implementation slot after Upgraded |
| X05 | success | setup changes admin slot |
| X06 | success | setup changes both ERC-1967 slots |
| X07 | negative | empty setup revert maps to inherited string error and rolls back |
| X08 | negative | nonempty setup revert bubbles exactly and rolls back |
| X09 | negative | setup changes both slots then reverts and rolls back |
| X10 | negative | exceptional setup child maps to inherited string error and rolls back |
| X11 | negative | missing-code implementation fails before optional setup |
| X12 | negative | outsider cannot upgrade-and-call |
| X13 | negative | ossified error precedes caller mismatch for upgrade-and-call |
| X14 | success | shifted 0x80 dynamic offset with a gap is accepted |
| X15 | negative | out-of-bounds dynamic offset is rejected |
| X16 | negative | dynamic length overrun is rejected |
| X17 | negative | noncanonical bool word is rejected |
| X18 | negative | dirty implementation address is rejected |
| X19 | success | trailing byte after dynamic payload is accepted |
| X20 | negative | bytes length 2^64 returns exact Panic(0x41), distinct from the small length-overrun empty revert |

### fallback

| ID | Arm | Frozen world |
|---|---|---|
| F00 | success | empty zero-value fallback delegates and returns empty |
| F01 | success | one-byte fallback delegates while ossified |
| F02 | success | two-byte fallback delegates |
| F03 | success | three-byte fallback delegates |
| F04 | success | unknown four-byte selector delegates |
| F05 | success | empty value-bearing receive path preserves msg.value and transfers ETH |
| F06 | success | fallback to a missing-code implementation succeeds with empty return |
| F07 | success | 32-byte echo succeeds |
| F08 | success | 1024-byte echo succeeds |
| F09 | negative | 32-byte revert bubbles exactly |
| F10 | negative | 1024-byte revert bubbles exactly |
| F11 | negative | empty child revert bubbles empty |
| F12 | negative | child mutates both slots then reverts; storage rolls back |
| F13 | success | successful child writes proxy-owned storage |
| F14 | success | successful child emits a proxy-addressed LOG1 |
| F15 | negative | InvalidOpcode child becomes outer empty revert |
| F16 | negative | StackUnderflow child becomes outer empty revert |

### value-rejection

| ID | Arm | Frozen world |
|---|---|---|
| V01 | negative | value-bearing getAdmin is rejected |
| V02 | negative | value-bearing getImplementation is rejected |
| V03 | negative | value-bearing getIsOssified is rejected |
| V04 | negative | value-bearing ossify is rejected before body behavior |
| V05 | negative | value-bearing changeAdmin is rejected before body behavior |
| V06 | negative | value-bearing upgradeTo is rejected before body behavior |
| V07 | negative | value-bearing upgradeToAndCall is rejected before body behavior |

## Comparison and claim boundary

Each case runs in a fresh, identical Prague world at EELS commit `4198b9c5996713b268aed602739d5aa40e277694`. Only the side-specific creation/runtime artifact differs. A row accepts only if status, exact returndata, projected storage, ETH deltas, ordered exact logs, target-account disposition, and every ordered DELEGATECALL field match the frozen expectation. Missing or extra observations reject.

K05 and K11 exercise constructor setup mutation of both ERC-1967 slots; K04/K05 pin post-setup admin log ordering. K18 and X20 set the decoded bytes length to exactly `2^64`, one above solc's accepted `uint64.max`, and require the exact 36-byte `Panic(0x41)` payload before any implementation effect. K16 and X16 remain distinct small declared-length overruns that require an empty revert. X14 accepts the deliberately noncanonical but ABI-valid 0x80 dynamic offset, while X15-X18 reject malformed offset/length/bool/address encodings. K12, X10, F15, and F16 cover exceptional child outcomes. The manifest records all seven required future falsifier families—reference substitution, selector routing, event/error bytes, state projection, rollback, child-call observation, and corpus/result mutation—as obligations only; this packet does not claim they already bite.

Passing all 85 rows is finite differential evidence, not universal equivalence, Solidity verification, byte identity, or proof. No gas or scoring fields are present.
