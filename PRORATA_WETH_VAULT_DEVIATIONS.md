# Blanc PRORATA WETH vault deviations from OpenZeppelin `ERC4626`

Blanc's WETH-backed ERC-4626 vault is an independently authored EVM program,
not a recompilation of the reference. `PORTING.md` governs what that means: the
reference is a differential target and an interface contract, not a byte source.
This file records where the two differ on purpose.

## Pinned reference

| item | value |
|---|---|
| normative standard | ethereum/ERCs `bb48e3add1097f5a80df1d70947a823b1d506c01`, `ERCS/erc-4626.md` SHA-256 `698c05bff73bfb796f59cd7c4732edccdf7e40176f9bb027c19a0bbe7251e10a` (Final; CC0-1.0) |
| differential referent | OpenZeppelin Contracts `v5.7.0`, tag commit `cab19933c33c2ad1d4c7a84864a3601dddfd16f3` (MIT) |
| reference file | `contracts/token/ERC20/extensions/ERC4626.sol`, blob `498ef28ddf1dadaafd681467b09adc85bdd5f4f5`, SHA-256 `c3d57303bb40361934115b490514f3327ff88652cc2ac980bfd1b63a901ef7b4` |
| harness | `contracts/ProrataWethVaultReference.sol`, SHA-256 `db2d9df13d9c89b97a35f9e28b334a9dcee4565737779f6458a107494894d280` |
| transitive closure | 17 sources, manifest SHA-256 `a1b486f5b2bc52ff8d28377424e0fed2a23d9cd28afa9b9f934148fbe1f1e6c8` |

Recorded at G1 in `~/plans/reports/prorata-erc4626-port-sf.md` §10 and frozen
there with per-file blob and SHA-256 identities.

## Status of this file

Every row's *decision* was frozen at G1 and is final. Every row now carries
evidence, and the kind of evidence is stated per row:

- Rows whose behaviour the executed differential covers cite
  `scripts/check-prorata-weth-vault-differential.sh`, which runs the committed
  17481-byte runtime **and** the constructor-patched OpenZeppelin reference on
  Jaune's EVM, and compares both against an independent exact-integer oracle.
- Rows whose behaviour is arithmetic cite
  `scripts/check-prorata-weth-vault-oracle.sh`.
- Rows about the reference's identity and surface cite
  `scripts/check-prorata-weth-vault-reference.sh`, which verifies the vendored
  closure under `scripts/reference/prorata-weth-vault/` against the hashes
  above, the committed `solc 0.8.36+commit.8a079791` input and output against
  the frozen template identities, and the reference ABI against the vault's own
  25 selectors.
- Rows about size and gas cite the measurements the differential records in
  `scripts/prorata-weth-vault-reference-measurements.json`, which it regenerates
  on every run and fails on drift.

The closure was vendored on 2026-09-04 from a clean checkout of the pinned
commit after every file matched the frozen hashes; no network fetch was needed.

## Deviation matrix

The nine rows are the deviations pre-registered at G1 (SF §11). Anything not
listed here is *not* a permitted difference: an unexpected mismatch fails.

| # | Deviation | OpenZeppelin `v5.7.0` | Blanc vault | Consequence | Stance | Evidence |
|---|---|---|---|---|---|---|
| 1 | Asset configuration | `immutable` set by constructor | configured constant `assetAddress = 0x1000`, installed with the runtime | no constructor theorem; the asset is fixed at compile time | Blanc proves properties of an installed runtime, so a constructor-set immutable would move the claim rather than support it | differential: every case installs the runtime and reaches WETH at the configured address |
| 2 | Revert payload | custom errors (`ERC4626ExceededMaxDeposit`, …) | empty revert data in every class | a caller cannot distinguish classes from returndata | deliberate: the frozen policy is uniform empty reverts; error selectors are interface surface Blanc does not claim | differential: malformed dispatch, truncated arguments, zero receiver and value-bearing calls all revert and leave no state or events |
| 3 | Zero-receiver capacity | `maxDeposit`/`maxMint` ignore the receiver | both report `0` for the zero receiver | a zero receiver advertises no capacity, matching the call that would revert | honest maxima: advertising capacity the vault will refuse is the failure this avoids | oracle: `check_zero_receiver_capacity` over 63 boundary states |
| 4 | Allowance-key collision | Solidity mapping; collision impossible by construction | flat hashed key with an explicit guard refusing address-shaped or reserved keys | a colliding key reverts rather than aliasing a balance or the supply | the flat layout is what makes the ledger's conservation statable; the guard is what keeps it sound | proved: the guard's conclusion is a premise of the compiled `approve`/`transferFrom` effects |
| 5 | Supply cap | unbounded up to the word ceiling | capped at `U - O` | deposit/mint maxima differ near the ceiling | the cap is what keeps `D = S + O` a nonzero word | oracle: `check_max_mint_tight`, `check_max_deposit_tight` |
| 6 | `A = U` denominator | checked `A + 1` reverts on overflow | exact 257-bit `A + 1` | the vault still quotes at the word ceiling instead of reverting | the standard's converters are required not to revert; wrapping would be worse | oracle: `A = U` is one of the boundary states in every battery |
| 7 | Child return check | `SafeERC20` also accepts empty successful returndata | requires canonical `true`, exactly 32 bytes | a non-canonical WETH would be refused | the configured asset returns canonical true; accepting empty returndata would weaken the exact-child claim | proved: `requireCanonicalWethTrue` is on the success path of every flow |
| 8 | Permit and extra interfaces | not in `ERC4626.sol`; commonly added | absent | no EIP-2612, no ERC-165 | out of the frozen surface | reference gate: the reference's compiled method identifiers are exactly the 25 signatures of `vaultFuncs`, and its ABI carries no `permit`, `nonces`, `DOMAIN_SEPARATOR` or `supportsInterface`; neither side exposes them |
| 9 | Runtime and code size | solc output: 4347-byte constructor-patched runtime | 17481 bytes, independently authored | different bytecode; Blanc's runtime is 4.0× larger and every measured call is cheaper | the size is the priced cost of inlined full-width arithmetic and per-path guards; the gas is where that design wins, and `PORTING.md` counts bytes and gas rather than asserting them | measured on Jaune at BPO2 against the same WETH (`scripts/prorata-weth-vault-reference-measurements.json`): deposit into an empty vault 107986 vs 110152, deposit into a donated vault 56662 vs 58828, mint 56726 vs 58926, redeem 52276 vs 54942, withdraw 52337 vs 56969, share transfer 50797 vs 51587 (Blanc first, gas) |

## What this file does not claim

It does not claim the Blanc vault and the OpenZeppelin reference agree
everywhere else. It claims that the nine rows above are the *only* intended
differences, and that an unexpected mismatch is a failure rather than a new
row. The compiled-reference differential establishes agreement on its eleven
cases — the four flows, share transfer, event order and data, zero-receiver,
malformed and value-bearing calls — and nowhere it does not execute: finite
evidence on a stated corpus, never a proof.

It also does not claim ERC-4626 conformance as a certification. Blanc's
theorems stop at the Blanc program; the standard is the source of the frozen
statement, not a party to the proof.
