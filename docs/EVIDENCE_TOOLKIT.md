# Evidence toolkit

Blanc's Python evidence tools share a few format and transport primitives.
Contract semantics, expected observations, schema inventories, and independent
oracle/model comparisons remain in their owning scripts.

## Ethereum hashes and ABI selectors

Use `scripts/keccak.py` for a stdlib-only Ethereum hash in an evidence script.
Import `keccak256` for digest bytes, `keccak256_bare_hex` for lowercase text
without a prefix, `keccak256_hex` for `0x`-prefixed text, and `selector` for
signature-derived selector bytes. Scripts beside the owner import it directly:

```python
from keccak import keccak256, keccak256_bare_hex, keccak256_hex, selector

payload_digest = keccak256(payload)
reference_digest = keccak256_bare_hex(payload)
rpc_digest = keccak256_hex(payload)
error_selector = selector("Error(string)")
```

This primitive uses Ethereum Keccak padding; it does not implement NIST SHA3.
The selector helper rejects signatures containing spaces. Hashing mechanics
are shared; frozen expected digests must come from an independent external
source. Reusing this helper does not replace independent schema validation,
artifact provenance or semantic models. Existing consumer spellings may remain
as aliases to preserve their API, but new scripts should import the owner.

Run `scripts/check-keccak-rate-boundary.sh` after changing the primitive or its
adoption. That gate checks external digest vectors, consumer representations
and extra implementations detected by its structural census. Its documented
fully derived-parameter detection limit remains relevant.

## Strict JSON

Use `scripts/strict_json.py` when an evidence input must reject duplicate
object keys and `NaN`/`Infinity`.  The primitive reports structured
`DuplicateKeyError` and `NonFiniteNumberError` exceptions and otherwise lets
the standard library report syntax and encoding errors.  A caller translates
those exceptions into its established local error type and wording:

```python
from strict_json import DuplicateKeyError, NonFiniteNumberError, loads

try:
    value = loads(raw)
except DuplicateKeyError as exc:
    raise LocalError(f"{label}: duplicate JSON key {exc.key!r}") from exc
except NonFiniteNumberError as exc:
    raise LocalError(f"{label}: non-finite JSON value {exc.value}") from exc
```

Do not move exact-key sets, type rules, frozen constants, or semantic policy
into this module.  Those are independent checks, not parsing mechanics.

## Coverage RLP decoding

Use `scripts/strict_rlp.py` for dependency-free decoding of committed block
RLP in evidence gates.  `decode` rejects truncated declared lengths and bytes
after the top-level item; `decode_legacy_block_transactions` additionally
validates the legacy transaction list shape and returns normalized
`(to, calldata)` pairs.  It deliberately preserves the former local decoders'
acceptance of non-minimal encodings, so it is not a canonical-RLP validator.
A gate should translate `RLPDecodeError` into its own top-level diagnostic.

This helper is a decoder only.  Transaction encoding/signing remains owned by
the independent fixture generators and their pinned EELS dependency.

## Prague fixture mechanics

Use `scripts/prague_fixture.py` for the five generic BlockchainTest operations:
allocation normalization, allocation state roots, header construction, header
JSON rendering, and the pinned `t8n` subprocess transport.  Pass the resolved
EELS root explicitly to `run_t8n`:

```python
post, result, body = run_t8n(env, alloc, txs, eels_root=EELS_ROOT)
```

Generators keep their scenario accounts, transactions, semantic assertions,
manifests, output paths, and write policy local.  A generator that is imported
as support may retain a thin three-argument `run_t8n` adapter to preserve its
existing API.

## Clean EELS pins

`scripts/eels_differential_common.py::verify_eels_pin` is the clean-checkout
owner.  Callers pass their expected commit and failure function.  The optional
`failure_message` callback preserves local mismatch/dirty diagnostics; Git
process failures propagate for the caller's established handling.

## Adoption and gate ownership

When one of these helpers becomes a transitive input of a registered gate,
add it to that row's `files` in `scripts/gate-registry.json` and regenerate
`docs/GATE_INPUTS.md` with `scripts/check-gates.sh --inventory`.  Run
`scripts/check-gates.sh --audit` to prove the generated inventory and catalogue
remain aligned.  New semantic-model sharing needs separate review: these
helpers are intentionally limited to syntax, generic format mechanics, and
checkout identity.
