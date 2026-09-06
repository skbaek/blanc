# Recovering the current-mainnet reference environment

From the Blanc checkout, construct a **new** absolute target path:

```sh
python3 scripts/setup-current-mainnet.py \
  --root "$HOME/execution-specs-t8n-blanc-recovered" --install-python
export JAUNE_T8N_TARGET="$HOME/execution-specs-t8n-blanc-recovered"
scripts/check-current-mainnet.sh
```

The setup command refuses an existing destination. It leaves the previous
environment available for diagnosis, and prints `OK — current-mainnet setup`
only after the normal full native verifier accepts the constructed environment.
It does not write the runtime lock. `--install-python` bootstraps an absent
uv-managed Python base/alias; it never replaces an existing one.

## Exact construction inputs

`scripts/current-mainnet-runtime-recipe.json` records the downloadable artifact
URLs, archive and executable SHA-256 values, dependency export digest, build
backend wheels and source-file hashes. Its own digest is bound by the runtime
lock. The construction uses:

- The unchanged upstream `9d6e6f8352a0f76e7e8803722d1a2798fa4f0a96` and target
  `827a1cad9c9c8528512f90a06888c8bd9171d9ae`. The reviewable four-file overlay
  and original commit-object text in `scripts/reference/current-mainnet/`
  reconstruct the exact existing tree and commit, even if the local overlay
  commit is absent from the public origin. Both hashes are checked before use.
- CPython 3.11.9, python-build-standalone build **20240814**, for macOS arm64
  or Linux x86_64. The archive's interpreter bytes must equal the existing
  platform-specific executable pin; the native uv alias/base and entrypoint
  checks remain in force.
- The exact official **uv 0.11.3** platform archive and executable, rather
  than whichever installer happens to be on `PATH`.
- The unchanged target `uv.lock` and both workspace `pyproject.toml` files.
  `uv export --frozen --no-default-groups --group test --no-emit-workspace`
  produces the recorded dependency export. Hash-required, binary-only sync
  installs those third-party requirements. Missing compatible wheels fail
  instead of invoking an unpinned source build.
- **setuptools 78.0.2** and **wheel 0.45.1**, using the exact hashed wheels
  in the recipe. The two pinned workspace packages are then installed editable
  with `--offline --no-deps --no-build-isolation`; no isolated resolver can
  choose a different backend. These build backends remain installed and are
  included in the complete runtime fingerprint.

The macOS closure contains **3,824** files rather than the historical **3,269**:
the entire difference is the 516 setuptools and 39 wheel site-packages files.
Runtime dependency versions retain their source-lock pins; the previously
unbounded build inputs are now explicit. This is a documented population
change, not a claim that the old aggregate was reproduced.

Artifacts are verified and cached below `.lake/current-mainnet-artifacts` by
default. `--cache /absolute/path` selects another cache. After an online
construction has populated its artifact and uv caches, offline reconstruction
also needs a local Git object source containing the pinned upstream:

```sh
python3 scripts/setup-current-mainnet.py \
  --root /absolute/new-target --cache /absolute/populated-cache \
  --source-cache /absolute/existing-reference --offline
```

The local Git source supplies objects only; the reconstructed checkout still
has the pinned public origin, upstream parent, overlay, tree and commit.

## Failure recovery

| Failure | Action |
|---|---|
| Existing destination | Choose a new root; preserve the failed environment. |
| Missing Python | Use `--install-python` on a host with no existing base/alias. A partial or mismatching base is retained for diagnosis; compare it with the recipe's exact archive and executable identities before separately replacing it. |
| Missing offline artifact or dependency wheel | Populate the selected cache with an online construction using the same recipe, then retry at a new root. |
| Artifact, source, export, or installed-file mismatch | Preserve the reported path and digest. Verify the pinned inputs and reconstruct a new root; do not relax the check or select newer dependencies. |
| Dirty target, wrong interpreter, entrypoint or import origin | Select the newly reconstructed root with `JAUNE_T8N_TARGET`; the ordinary verifier explains the failed identity. |
| Historical platform representation | Native reconstruction evidence and a reviewed generator update are still required for that platform. The verifier refuses to reinterpret the historical digest. |
| Runtime lock mismatch after construction | Keep the construction receipt and report the mismatch. Do **not** run the lock writer merely to accept the current environment. |

`gen-current-mainnet-runtime-lock.py --write` remains a reviewed maintainer
operation after native construction evidence and controls. It refreshes only
the executing platform. A historical non-native row is retained explicitly as
representation 1 and cannot pass native verification until reconstructed there.

## Portable representation and controls

Representation 2 retains the complete file population and the existing
bytecode exclusions. Only the two known editable `.pth` paths and exact
`direct_url.json` objects substitute the validated target root. Known
`uv_cache.json` objects have their complete shape and timestamp types checked;
only installation timestamps are normalized. Other metadata and executable
`.pth` contents remain byte-exact.

Top-level installed distribution RECORD entries first validate real payload
bytes and sizes, confinement and required rows. Their portable hashes **and
sizes** then describe the validated canonical metadata or exact-Python-shebang
script bodies. Native executables remain byte-exact. Vendored RECORD files
are ordinary exact payload bytes, not reinterpreted installation manifests.
No installed file is edited to obtain the portable digest.

The existing runtime-lock self-check runs the focused relocation and corruption
controls. A maintainer can additionally run the actual payload/restoration
controls on an explicitly disposable temporary reconstruction:

```sh
python3 scripts/current_mainnet_runtime_controls.py \
  --disposable-root /tmp/blanc-runtime-reconstruction-example
```

Two fresh roots at different paths/times must produce identical portable
closures and pass the full native verifier. Wrong dependency code and editable
path escape must fail, then pass after restoring only the changed file.
