# WETH10 deployed-reference inputs

This directory is the immutable, reviewable input set for
[`../../weth10-reference.py`](../../weth10-reference.py).  The normal
generator and checker are offline; only `weth10-reference.py refresh` contacts
GitHub, solc-bin, and the two named RPC operators.  The lock's schema-v2
regeneration command is `python3 scripts/weth10-reference.py generate` from
the repository root.

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
  snapshot/diff.  `source/drift-provenance.json` pins that separate evidence's
  commit, source/blob digest, and diff digests.  The 34d2712 diff is provenance
  corroboration only: it is the exact two-comment change and never changes the
  normative target.

The generated [`../../weth10-reference.json`](../../weth10-reference.json)
is derived exclusively from the normative deployment/compiler/RPC inputs, not
from current-main drift.  It carries the installed runtime hex and Ethereum
codehash, full canonical function/event/receive ABI, the separate constructor
boundary, exact compiler settings and immutable references, all four derived
immutable values, and the source-side guard/callback/event/storage inventories.

The ordinary shell gate first applies the independent exact-schema contract in
`scripts/weth10_reference_schema.py`, then reconstructs the lock, checks the
separate drift evidence, and runs deletion, mutation, wrong-type, coherent,
deployment-derivation, and coordinated-input falsifiers. Runtime/compiler
binary and output digests, RPC
envelopes/block/operators, source/input Git blobs, the template digest, and the
exact immutable spans are pinned independently of the generated JSON so an
input-plus-lock coordinated edit cannot become self-affirming.

`refresh` acquires into a temporary staging tree, authenticates the selected
compiler entry and binary against independent SHA-256/Keccak pins before
execution, proves the fixed observation block is finalized at both operators,
validates the complete staged lock and drift evidence, and publishes only after
all those checks pass.
