# PRORATA WETH vault reference inputs

This directory is the immutable, offline authority tree for the vault's
differential referent: OpenZeppelin Contracts `v5.7.0` at commit
`cab19933c33c2ad1d4c7a84864a3601dddfd16f3` (MIT), selected and frozen at G1 in
`~/plans/reports/prorata-erc4626-port-sf.md` §10.

- `inputs/source/openzeppelin-contracts/` holds the 16 upstream sources of the
  transitive closure at their upstream paths, plus the upstream `LICENSE`.
- `inputs/source/contracts/ProrataWethVaultReference.sol` is the goal-owned
  harness (MIT): OpenZeppelin `ERC4626` over `ERC20`, offset 3, the D2
  metadata, the asset passed to the constructor.
- `inputs/git-provenance.json` records the repository, commit, tag, and per
  file the Git blob, SHA-256 and byte count, together with how the bytes were
  acquired: copied from a clean local checkout of the pinned commit after every
  file matched the SHA-256 frozen in the SF, so no network fetch was needed.
- `inputs/standard-json-input.json` is the exact compiler input: the vendored
  bytes under the frozen settings (optimizer on, runs 1, legacy pipeline,
  `evmVersion = prague`, `bytecodeHash = none`, `appendCBOR = false`).
- `inputs/standard-json-output.json` is the output of `solc 0.8.36+commit.8a079791`
  on that input. It was produced with the native macOS build of that commit
  (SHA-256 `d4abcf0b…`, the build the SF records for dossier reconnaissance);
  the SF's selected platform-independent `emscripten-wasm32` artifact
  (SHA-256 `704877a5…`) is not vendored and has not been executed here. Both
  are the same compiler commit; the output's identities are the SF's own
  template identities, which is the check that matters.

The lock `scripts/prorata-weth-vault-reference.json` pins all of the above.
`scripts/check-prorata-weth-vault-reference.sh` verifies the tree against it
offline; `--recompile` with `$SOLC` pointing at the recorded native binary
reproduces the artifacts from source, and `--self-test` shows the gate bites.

The constructor-patched runtime — the creation input with the configured asset
word `0x…1000` executed against Blanc's WETH — is derived and identity-checked
by `scripts/check-prorata-weth-vault-differential.sh`, which then runs the same
cases on Blanc's runtime and on it.

The reference is evidence, never a theorem: Blanc's claims stop at the Blanc
program (`PORTING.md`).
