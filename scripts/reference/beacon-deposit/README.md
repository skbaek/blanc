# Beacon deposit contract — pinned reference inputs

This directory is the immutable fidelity target for the `BeaconDeposit*` pure
model family (goal `beacon-deposit-opening-v1`). It vendors the pinned
upstream artifacts the model mirrors, so the model-fidelity review and the
vector oracle are reproducible from this repository alone. It is deliberately
lighter than `../weth10/` and `../lido-circuit-breaker/`: no reference lock,
schema, or refresh machinery exists yet — that apparatus belongs to the
compiled-port successor goal, which will also decide whether to grow this
directory into a schema-v2 lock.

## Pins (fetched 2026-08-28, methods and full evidence in
`~/plans/reports/beacon-deposit-opening-completion.md`, section B1)

- `inputs/deposit_contract.sol` — the Solidity deposit contract, byte-exact
  from `ethereum/consensus-specs` at commit
  `5dac261c78eda16b383f7b6d832495880bdd015c` (the last revision containing
  `solidity_deposit_contract/`; the directory was removed by
  `af4a77680b216c7142e3c2dc2195b42b8aea04f2`, 2026-04-21, PR #5137, which
  moved the ossified contract to `ethereum/solidity-deposit-contract`).
  Byte-identical to `ethereum/solidity-deposit-contract` at its 2026-08-28
  default-branch tip `5bf2741b50c58b844225f89018041c5d54726f8e`.
  SHA-256 `2a8db249155e8502e1132f14410b8d7b2a924512723ed07a08167477d8f8c073`.
- `inputs/deposit_contract.json` — the upstream compiled artifact (ABI +
  creation bytecode) beside the source at the same pin. SHA-256
  `fbb573648e4fe96a6b731768cbf5165f5037d7bd29f43359c5316eeb9edc78e6`.
- `inputs/upstream-README.md` — the upstream folder README recording the
  compiler configuration (solc `v0.6.11+commit.5ef660b1`, `--optimize
  --optimize-runs 5000000 --metadata-literal`) and the rewrite history. SHA-256
  `a9d21d9ea4d428dc5adb1061677339dbf56425a7a22c9a6eac17d9b188e54de2`.
- `inputs/spec-deposit-contract.md` — `specs/phase0/deposit-contract.md` at
  consensus-specs master pin `cf65c29a2590b8f5d43b6a26aee9f2293ed560f1`
  (2026-08-26). SHA-256
  `e5218b6626b5a052c62224d6c2ceb09496263910766861067aecf22fb21d3d5f`.
- `inputs/deployed-runtime.norm.hex` — normalized (0x-stripped, lowercase)
  `eth_getCode` result for mainnet
  `0x00000000219ab540356cBB839Cbe05303d7705Fa` at `latest` on 2026-08-28,
  6,358 bytes of code; two independent RPC operators (publicnode, drpc)
  returned byte-identical code. Identity corroboration only — never a
  verification target. SHA-256 (of the hex text)
  `867e261f9811c5227ff0e2ec5d7803156f1af3428e49d6ffc041102da3050432`.
  The bytes equal the trailing 6,358 bytes of `deposit_contract.json`'s
  creation bytecode, metadata trailer included.

The model's normative target is `inputs/deposit_contract.sol` alone. The
other files are corroboration and compiler-configuration provenance.
