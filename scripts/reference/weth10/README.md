# WETH10 deployed-reference inputs

This directory is the immutable, reviewable input set for
[`../../weth10-reference.py`](../../weth10-reference.py).  The normal
generator and checker are offline; only `weth10-reference.py refresh` contacts
GitHub, solc-bin, and the two named RPC operators.

- `deployment-artifact.json`, `solc-input.json`, and `git-provenance.json`
  bind the official deployment record, its exact standard-json input, and the
  Git blob identities.
- `solc-emscripten-wasm32-list.json` and `solc-output.json` bind the compiler
  build and its complete output.  The compiler executable itself is not
  vendored; the release manifest's SHA-256 and Keccak-256 are checked during a
  refresh and carried into the generated lock.
- `rpc-*.json` are independent acquisition envelopes.  Each retains the raw
  JSON-RPC response, request, finalized observation block, and operator URL.
- `source/` contains the deployed source snapshot plus the current-main drift
  snapshot/diff.  The 34d2712 diff is provenance corroboration only: it is the
  exact two-comment change and never changes the normative target.

The generated [`../../weth10-reference.json`](../../weth10-reference.json)
is derived exclusively from the normative inputs, not from current-main drift.
