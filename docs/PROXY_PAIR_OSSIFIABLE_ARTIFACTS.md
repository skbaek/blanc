# OssifiableProxy generated artifact chain

This packet gives Blanc's `ProxyPair` OssifiableProxy baseline one exact,
regenerable artifact owner without making a proof, differential, or performance
module own a second byte list.

## Owned outputs

After generation, the repository owns these two files:

- `Blanc/ProxyPairOssifiableArtifacts.lean` contains plain byte literals for
  `runtimeBaseline` and the executable `creationBaseline` prefix. It defines
  the measured creation template as their concatenation. The module contains
  direct compiler witnesses, exact numeral length theorems, and separate
  kernel-checked SHA-256 and Ethereum Keccak-256 theorems for the runtime,
  prefix, and aggregate creation template.
- `scripts/lido-ossifiable-proxy-artifacts.json` contains only canonical
  identity metadata: binding, Lean definition, byte length, SHA-256, and
  Ethereum Keccak-256. It deliberately does not duplicate the bytes as hex.

No artifact bytes or artifact digests are present in this staged packet. They
are rendered only from a successfully elaborated evaluator output.

## Authority chain

1. `Blanc.ProxyPair.runtimeBaseline_compile` and
   `Blanc.ProxyPair.creationBaseline_compile` are the production compiler
   witnesses in `ProxyPairOssifiableProgram` and
   `ProxyPairOssifiableDeploy`.
2. `scripts/eval-lido-ossifiable-proxy-artifacts.lean` imports only the
   production deployment module and emits exactly two byte rows, in this
   stable order:

       creation-template <byteLength> <lowercase hex>
       returned-runtime <byteLength> <lowercase hex>

3. The generator requires the returned runtime to be a nonempty exact suffix
   of the creation template. The remaining nonempty prefix is therefore the
   exact `creationBaselineBytes`; an unrelated or stale runtime is rejected.
4. The generated Lean module makes the prefix and runtime plain byte literals
   and proves each literal is the corresponding `Prog.compile` result with
   `decide +kernel`. Its aggregate equality theorem derives the production
   creation template from those two witnesses.
5. `Bytes.sha256` and `Bytes.keccak` compute each fixed identity in Lean; each
   digest theorem uses a separate `decide +kernel`. The Python generator
   independently computes SHA-256 with `hashlib` and reuses the same
   dependency-free Ethereum Keccak-256 implementation already owned by
   `scripts/lido_ossifiable_proxy_reference_schema.py`. Two fixed Keccak
   self-tests run before every mode.
6. Ordinary Python `check` mode parses the two committed Lean literals,
   reconstructs the aggregate, recomputes every identity, and demands exact
   canonical equality with both generated files. It invokes neither Lean nor
   the network. `check-evaluator` additionally compares a fresh externally
   captured evaluator result to both committed outputs.

The network-free check intentionally cannot prove that a coherently edited
Lean literal still comes from the compiler. That leg is supplied by elaborating
the generated Lean compiler witnesses and by `check-evaluator` against a fresh
production evaluator result; neither may be omitted from closure.

## Deliberate regeneration

From the repository root, after acquiring the repository's Lean semaphore:

```sh
artifact_output="$(mktemp)"
lake env lean scripts/eval-lido-ossifiable-proxy-artifacts.lean >"$artifact_output"
python3 scripts/lido-ossifiable-proxy-artifacts.py generate \
  --evaluator-output "$artifact_output"
python3 scripts/lido-ossifiable-proxy-artifacts.py check
python3 scripts/lido-ossifiable-proxy-artifacts.py check-evaluator \
  --evaluator-output "$artifact_output"
lake env lean Blanc/ProxyPairOssifiableArtifacts.lean
git diff --exit-code -- Blanc/ProxyPairOssifiableArtifacts.lean \
  scripts/lido-ossifiable-proxy-artifacts.json
```

The temporary evaluator file is disposable. The two generated repository files
are the durable outputs. A normal no-build/static lane may run only:

```sh
PYTHONDONTWRITEBYTECODE=1 \
  python3 scripts/lido-ossifiable-proxy-artifacts.py check
```

## Integration checklist owned by the lead

- Confirm the current `runtimeBaseline`, `creationBaseline`,
  `ossifiableCreationTemplate`, and existing compiler-witness names before the
  first generation.
- Elaborate the evaluator and generated target under the host semaphore; in
  particular, confirm the six fixed digest decisions fit normal repository
  recursion/heartbeat policy without raising limits.
- Add `Blanc.ProxyPairOssifiableArtifacts` to the existing `proxy-pair`
  layering/import surface, not as a new contract family.
- Register all public compiler, length, aggregate, SHA-256, and Keccak theorems
  with the repository's axiom audit. Expected axioms must remain within the
  ordinary kernel-decision trust surface.
- Catalogue the network-free checker and any wrapper in `scripts/GATES.md` and
  its input registry using the owning procedures. The closure includes
  `scripts/lido_ossifiable_proxy_reference_schema.py` because the checker
  imports its established Keccak implementation. Add a falsifier packet if
  the chosen gate tier requires one.
- Point differential/performance consumers at the exact evaluator labels above
  and at `scripts/lido-ossifiable-proxy-artifacts.json`; they must not maintain
  a second Blanc hex literal or digest table.

The packet introduces no generic/shared declaration and therefore has no
`docs/COMMON_API.md` or discoverability consequence beyond the existing
`proxy-pair` family integration.
