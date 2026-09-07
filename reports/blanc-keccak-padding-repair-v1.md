# Keccak pad10*1 correctness repair

Goal `blanc-keccak-padding-repair-v1`. Base `c26f60d`, branch
`claude/blanc-keccak-padding-repair-v1`, worktree
`/Users/agent/blanc/.worktrees/blanc-keccak-padding-repair-v1`.

## 1. Enumeration and classification

Enumeration method, run three ways and reconciled: a grep for the Keccak round
constants and `keccak_f`/`RHO` shapes; a grep for every `padded`/`% rate`/`0x80`
padding construct; and a static scan for `padded = bytearray(` over
`scripts/**/*.py`. The three agree on the same population, and the scan is now
carried in the control itself (`test-keccak-rate-boundary.py`), so a tenth
implementation cannot appear without failing the gate.

| implementation | entry point | classification |
|---|---|---|
| `scripts/gen-beacon-deposit-vectors.py:122` | `keccak256`/`keccak256_bytes` | **defective — repaired** |
| `scripts/check-lido-twg-census.py:50` | `keccak256` | **defective — repaired** (not listed in the brief; found by enumeration) |
| `scripts/lido_circuit_breaker_reference_schema.py:172` | `keccak_bytes`/`keccak256` | **defective — repaired** |
| `scripts/lido_twg_reference_schema.py:198` | `keccak_bytes`/`keccak256` | **defective — repaired** |
| `scripts/lido_ossifiable_proxy_reference_schema.py:243` | `keccak256` | **defective — repaired** |
| `scripts/lido_ossifiable_proxy_performance_schema.py:422` | `keccak256` | **defective — repaired** |
| `scripts/weth10_reference_schema.py:218` | `keccak256` | **defective — repaired** |
| `scripts/weth10-reference.py:214` | `keccak256` | **defective — repaired** |
| `scripts/gen-beacon-deposit-current-mainnet.py:299` | `keccak256` | already correct — pads with `extend(bytes((-len(padded)) % rate))` then `padded[-1] |= 0x80`, which merges the two pad bits. Left untouched and used as the control-on-the-control. |
| `scripts/gen-weth10-differential.py:287` | `keccak` | not an implementation — one-line delegation to EELS `ethereum.crypto.hash.keccak256` |
| `scripts/gen-lido-twg-differential.py:222` | `keccak` | not an implementation — EELS delegation |
| `scripts/gen-lido-circuit-breaker-differential.py:181` | `keccak` | not an implementation — EELS delegation |
| `scripts/gen-beacon-deposit-differential.py:303` | `keccak` | not an implementation — EELS delegation |
| `scripts/gen-fmint-fixtures.py`, `gen-weth-fixtures.py`, `gen-fmint-borrower-solc.py`, `gen-prorata-fixtures.py`, `gen-weth10-current-mainnet.py`, `gen-weth10-redemption-fixtures.py`, `gen-lido-ossifiable-proxy-current-mainnet.py`, `gen-beacon-deposit-deployment-fixture.py`, `gen-lido-circuit-breaker-deployment-fixture.py`, `check-weth10-deployment.py`, `check-lido-circuit-breaker-dispatchers.py` | — | not implementations — import EELS `keccak256` |
| `scripts/lido-ossifiable-proxy-reference.py`, `lido-circuit-breaker-reference.py`, `lido-twg-reference.py`, `lido-ossifiable-proxy-artifacts.py`, `run-lido-ossifiable-proxy-performance.py`, `test-weth10-reference-falsifiers.py`, `test-lido-twg-reference-falsifiers.py`, `test-lido-ossifiable-proxy-reference-falsifiers.py`, `test-lido-ossifiable-proxy-artifact-falsifiers.py` | — | not implementations — import a repaired schema module |
| `scripts/check-error-data.py`, `scripts/check-fmint-borrower-source.py` | — | not implementations — load `weth10-reference.py` by path for its `keccak256` |
| `Jaune/Hash.lean:873` `Bytes.keccak` (via `Blanc/CommonCore.lean:2162` `String.keccak`) | — | already correct, and **not owned by this unit**. Its finalisation XORs the `0x01` domain byte into lane `wc` and `0x80 <<< 60` into lane 16 of the *same* state before one `f1600`; when the message ends one byte short of the rate both land on the same byte and XOR to `0x81`. No separate-block path exists. |

No shared Keccak helper exists in a vault or anywhere else reachable from main;
there is no `~/vault`. Nine independent sponges, eight of them defective.

## 2. Repair

Identical smallest coherent edit in all eight, e.g. in
`scripts/weth10_reference_schema.py`:

```python
-    while len(padded) % rate != rate - 1:
-        padded.append(0)
-    padded.append(0x80)
+    # pad10*1: the two pad bits share one byte when the message ends
+    # one byte short of the rate, so merge 0x80 into the final byte.
+    while len(padded) % rate != 0:
+        padded.append(0)
+    padded[-1] ^= 0x80
```

(`check-lido-twg-census.py` uses `RATE` rather than `rate`; otherwise byte
identical.) Deliberately **not** centralised: the programme's point is that one
shared helper would have propagated this defect to every surface at once
instead of leaving eight chances to catch it. Centralisation candidates for the
later S7 packet are recorded in section 7.

## 3. Independent oracle and rate-boundary vectors

`scripts/keccak_rate_boundary_vectors.py` pins digests for message lengths
0, 1, 2, 134, **135**, 136, 137, 270, **271**, 272, 406, **407**, 408 and
**543** (message of length *n* is `bytes(i % 256 for i in range(n))`), plus two
signature preimages.

Oracle: `ethereum.crypto.hash.keccak256` from the pinned execution-specs
checkout at `4198b9c5996713b268aed602739d5aa40e277694` — the same pin the
differential gates already treat as their oracle — which delegates to
pycryptodome's `Crypto.Hash.keccak`. This is a compiled C implementation
outside this repository and outside the code under repair. Cross-checked: the
length-0 row equals the published Keccak-256 empty-string digest
`c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470` that several
Blanc surfaces already pin literally, and the whole vector set is also matched
by `gen-beacon-deposit-current-mainnet.py`'s independently-phrased in-repo
implementation. `hashlib.sha3_256` was **not** used and is documented in the
module as invalid here (domain byte `0x06` vs `0x01`).

`scripts/test-keccak-rate-boundary.py` loads all nine implementations by path
and checks each against every vector, and additionally reconciles its
`IMPLEMENTATIONS` list against a static sponge scan of `scripts/**/*.py` in
both directions.

```
$ python3 scripts/test-keccak-rate-boundary.py
OK keccak rate-boundary control: 9 implementations x 14 lengths + 2 selectors
   = 144 comparisons against ethereum.crypto.hash.keccak256 @ 4198b9c5...
```

## 4. The control bites

In a disposable copy of `scripts/` under the scratchpad, the padding fix alone
was reverted in all eight repaired files — nothing else changed — and the
control re-run:

```
FAIL keccak rate-boundary control: 32 failure(s)
```

32 = 8 implementations x 4 lengths, and the four lengths are exactly
**135, 271, 407, 543** (every `len % 136 == 135` row). Every other length, both
selector preimages, and the untouched already-correct
`gen-beacon-deposit-current-mainnet.py` all still pass. Failure lands at the
control, removing only the control's subject restores green, and no live
fixture was perturbed.

## 5. Consumer audit

Two independent methods, both negative.

**(a) Byte-compare of every re-derived artifact.** Every owning gate re-derives
its digests from vendored sources and byte-compares against the committed lock,
manifest or golden. All are green post-repair (section 6). In particular
`python3 scripts/gen-beacon-deposit-vectors.py --check` reports the committed
`scripts/reference/beacon-deposit/vectors.json` matching regeneration
byte-for-byte at 92,835 bytes.

**(b) Positive length census.** Each repaired `keccak` was temporarily
instrumented to append `len(input)` to a log (instrumentation reverted
afterwards; the worktree was verified clean) and the gates re-run:

| surface | keccak calls censused | inputs with `len % 136 == 135` |
|---|---|---|
| `weth10_reference_schema.py` | 4,629 | 0 |
| `weth10-reference.py` | 3,820 | 0 |
| `lido_circuit_breaker_reference_schema.py` | 3,028 | 0 |
| `lido_twg_reference_schema.py` | 1,007 | 0 |
| `lido_ossifiable_proxy_reference_schema.py` | 136 | 0 |
| `check-lido-twg-census.py` | 101 | 0 |
| `lido_ossifiable_proxy_performance_schema.py` | 20 | 0 |
| `gen-beacon-deposit-vectors.py` (full `--check` regeneration) | 102,114 | 0 |
| **total** | **114,855** | **0** |

Longest input hashed anywhere: 19,710 bytes.

**Finding: no committed artifact, fixture, manifest, lock or recorded hash in
Blanc was produced from an input of length ≡ 135 (mod 136).** Every digest the
repository records is unchanged by this repair, and no recorded value moved. In
consequence this unit asserts nothing about any deployed contract, published
claim or public count, and nothing here is a reference or claim movement. The
defect was live tooling risk, not a landed error.

## 6. Gates

Selected from `scripts/GATES.md` by the changed paths.

| command | verdict |
|---|---|
| `python3 scripts/test-keccak-rate-boundary.py` (new control) | OK, exit 0 |
| `python3 scripts/gen-beacon-deposit-vectors.py --check` | OK, exit 0 — 92,835 bytes byte-identical |
| `scripts/check-weth10-reference.sh` | OK, exit 0 |
| `scripts/check-lido-circuit-breaker-reference.sh` | OK, exit 0 |
| `scripts/check-lido-twg-reference.sh` | OK, exit 0 |
| `scripts/check-lido-twg-census.sh` | OK, exit 0 |
| `scripts/check-lido-ossifiable-proxy-reference.sh` | OK, exit 0 |
| `scripts/check-lido-ossifiable-proxy-performance.sh` | OK, exit 0 |
| `scripts/check-lido-ossifiable-proxy-artifacts.sh` | OK, exit 0 |
| `python3 scripts/check-fmint-borrower-source.py` | OK, exit 0 |
| `scripts/check-error-data.sh` | OK, exit 0 — 11 lock reason strings, Lean and independent ABI derivations byte-identical |
| `scripts/check-beacon-deposit-model.sh` | OK, exit 0 — 476 compared lines across both regimes |
| `scripts/check-fmint.sh` | OK, exit 0 — 11/11 PASS, manifest cross-check clean |
| `scripts/check-doc-counts.sh` | OK, exit 0 — 12/12 quotations agree at 1070 |
| `scripts/check-layering.sh` | OK, exit 0 |

The three Lean-touching gates needed built artifacts; the build ran through
`~/creme/scripts/creme lake-build blanc-keccak-padding-repair-v1 --wait 900 --
Blanc.RevertPayload Blanc.BeaconDepositCorrectness jaune/jaune` with no
`--memory-gib`/`--contention`, and the wrapper classified it
`NOT_REQUIRED_FRESH` (0 modules stale, 1 restored from cache, 1.53 s, no hold
taken). `check-beacon-deposit-model.sh` additionally confirms the Jaune
`Bytes.keccak` classification empirically: the Lean model's keccak-256 regime
and the repaired Python oracle generator agree on all 476 compared lines.

No gate was weakened, and no baseline, budget, allowlist, golden or timeout was
touched.

## 7. Notes for the later S7 packet

- Centralisation candidates, if and when the shared toolkit packet runs: the
  eight repaired bodies are now byte-identical apart from the `rate`/`RATE`
  spelling, and `keccak_f` is identical across all of them. The reason to keep
  them separate is the independence argument, so a shared toolkit should come
  with a rate-boundary control per surface (the one added here) rather than as
  a replacement for it.
- `scripts/keccak_rate_boundary_vectors.py` and
  `scripts/test-keccak-rate-boundary.py` are not yet registered in
  `scripts/gate-registry.json` or in the `scripts/GATES.md` catalogue. Both are
  manifests/catalogues this unit does not own; see the unresolved list.
