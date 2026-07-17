# Patch plan: EIP-4844 point evaluation and EIP-2537 BLS12-381 precompiles

This is a self-contained implementation plan for `/Users/bsk/elevm`, closing
`~/blanc/review.md` finding 3.3 (precompiles `0x0a`–`0x11` registered but
unimplemented), with `/Users/bsk/blanc` treated as the downstream proof client
that must remain green throughout. It follows the style and discipline of
`~/blanc/patch.md`: one sequential, agent-session-sized step at a time; one
commit per touched repository per step; explicit verification gates; no long
blind arcs.

**9 steps**, with sanctioned split points inside Steps 6 and 7 if a session
runs long (worst case 11 sessions). Steps 2–8 each flip a fixed set of
official test vectors from red to green; Step 1 builds the vector harness and
proves it against the already-green precompiles; Step 9 closes with
consensus-format blockchain fixtures and baselines.

## Starting point (verified at plan-writing time)

The stubs are much further along than review.md implies. Verified facts:

- Dispatch for all eight precompiles is complete
  (`precompileRun`, `Elevm/Execution.lean:3291`).
- Every stub already has the correct input-length check, and G1MSM / G2MSM /
  PAIRING / both MAPs / G2ADD already charge gas before erroring
  (`Elevm/Execution.lean:3123`–`3242`).
- Both MSM discount tables are complete with 128 entries and match the final
  Pectra EIP-2537 values, including `g1MaxDiscount = 519`,
  `g2MaxDiscount = 524` (`Elevm/Execution.lean:693`–`735`). The pairing gas
  formula `32600*k + 37700` is also final-EIP-correct.
- `Elevm/EC.lean` already contains the exact machinery BLS12-381 needs, built
  for the BN254 precompiles in py_ecc's style: generic `FinField p`,
  polynomial extension fields `GaloisField p m`, generic affine
  `EllipticCurve F a b` with `add`/`double`/binary `mulBy`/`isOnCurve`/`mk?`,
  plus a working Miller loop and final exponentiation for BN254. BLS12-381 is
  an instantiation of the same pattern with different constants and a
  *simpler* Miller loop.
- Two latent defects sit in the stubs and are fixed by this plan:
  1. `lengthPerPair = 160` (`Elevm/Execution.lean:693`) is used by **both**
     MSM stubs, but a G2 MSM pair is 288 bytes (256-byte point + 32-byte
     scalar). Today G2MSM's `k`, input validation, and gas are all wrong
     (masked only because the stub always errors). Fixed in Step 5.
  2. `executeBls12G1Add` charges no gas at all; the final EIP cost is 375.
     Fixed in Step 2.

## Reference implementations (all already on this machine)

The EVM-layer semantics come from EELS and the curve arithmetic from py_ecc —
the same two sources the existing elevm code already mirrors (EC.lean quotes
py_ecc functions in comments; the stubs quote EELS `def bls12_*` signatures).

- EELS precompile layer (byte parsing, gas, error semantics, subgroup-check
  placement):
  - `~/execution-specs/src/ethereum/prague/vm/precompiled_contracts/bls12_381/__init__.py`
    — codecs `bytes_to_fq/fq2/g1/g2`, `g1/g2_to_bytes`,
    `decode_g1/g2_scalar_pair`, discount tables.
  - `.../bls12_381/bls12_381_g1.py`, `bls12_381_g2.py`, `bls12_381_pairing.py`
    — the seven precompile bodies.
  - `~/execution-specs/src/ethereum/prague/vm/precompiled_contracts/point_evaluation.py`
    — the 0x0a body.
  - `~/execution-specs/src/ethereum/crypto/kzg.py` — `verify_kzg_proof`,
    `verify_kzg_proof_impl`, `pairing_check`, `validate_kzg_g1`,
    `bytes_to_bls_field`, and the trusted-setup constant
    `KZG_SETUP_G2_MONOMIAL_1` (line 71). Verification needs only this ONE
    G2 point — not the 4096-point ceremony data.
- py_ecc (curve/field reference; installed in the EELS venv):
  - `~/execution-specs/venv/lib/python3.11/site-packages/py_ecc/bls12_381/bls12_381_curve.py`
    and `bls12_381_pairing.py` — the **non-optimized affine** implementation,
    structurally closest to EC.lean's BN254 code. Constants: `field_modulus`,
    `curve_order`, `b = 4`, `b2 = FQ2([4,4])`,
    `ate_loop_count = 15132376222941642752`,
    `FQ2_MODULUS_COEFFS = (1, 0)` (u²+1),
    `FQ12_MODULUS_COEFFS = (2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0)` (w¹²−2w⁶+2).
  - `.../py_ecc/optimized_bls12_381/optimized_swu.py`,
    `optimized_clear_cofactor.py`, `constants.py` — SSWU maps, isogeny
    coefficients, cofactor-clearing scalars for the MAP precompiles.
  - `.../py_ecc/bls/hash_to_curve.py` — `map_to_curve_G1/G2`,
    `clear_cofactor_G1/G2`: exactly what EELS calls for the MAP precompiles.
  - `.../py_ecc/bls/point_compression.py` — the 48-byte compressed-G1 codec
    (ZCash flag bits) needed by point evaluation.
- Specs, for cross-checking only (implementation follows the code above):
  [EIP-2537](https://eips.ethereum.org/EIPS/eip-2537) with its assets
  `field_to_curve.md` and `fast_subgroup_checks.md`;
  [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844); RFC 9380 for
  SSWU/`sgn0`.

Constants stated anywhere in this plan are conveniences; agents must
re-derive every constant from the local py_ecc/EELS sources, never from
memory or from this document.

## Test vectors

- **Official EIP-2537 vectors** —
  `https://github.com/ethereum/EIPs/tree/master/assets/eip-2537`:
  `add_G1_bls.json`, `add_G2_bls.json`, `mul_G1_bls.json`, `mul_G2_bls.json`,
  `msm_G1_bls.json` (3.6 MB), `msm_G2_bls.json` (6.5 MB),
  `pairing_check_bls.json`, `map_fp_to_G1_bls.json`, `map_fp2_to_G2_bls.json`,
  and a `fail-*.json` negative file for each. Format is geth's:
  `{"Input": hex, "Expected": hex, "Name": str, "Gas": int}` for positive
  vectors, `{"Input", "ExpectedError", "Name"}` for negative ones.
  The `mul_*` files are single-pair MSM inputs (160/288 bytes) and, because
  `discount(1) = 1000`, their `Gas` fields (12000/22500) are already correct
  MSM gas — they are usable against the MSM precompiles verbatim.
- **go-ethereum vectors** —
  `https://github.com/ethereum/go-ethereum/tree/master/core/vm/testdata/precompiles`:
  `blsG1Add.json` (99 KB, more edge cases than the EIP file), `blsG2Add.json`,
  `blsG1Mul.json`, `blsG2Mul.json`, `blsG1MultiExp.json`, `blsG2MultiExp.json`,
  `blsPairing.json`, `blsMapG1.json`, `blsMapG2.json`, all with `fail-*`
  twins, **and `pointEvaluation.json`** — plus control files for precompiles
  elevm already implements (`bn256Add.json`, `bn256ScalarMul.json`,
  `bn256Pairing.json`, `blake2F.json`, `modexp_eip2565.json`), which Step 1
  uses to prove the harness itself.
- **EEST blockchain fixtures, point evaluation — already on disk**:
  `~/execution-specs/tests/fixtures/latest_fork_tests/fixtures/blockchain_tests/cancun/eip4844_blobs/point_evaluation_precompile/`
  (7 files; `external_vectors.json` wraps the official consensus-spec-tests
  KZG `verify_kzg_proof` suite). Same `BlockchainTests` JSON family that
  `scripts/check.sh` already runs, reachable via the `ELEVM_FIXTURES`
  environment override.
- **EEST blockchain fixtures, EIP-2537** — the local snapshot stops at
  Cancun, so these need one download in Step 9: a pinned fixture release
  tarball from `https://github.com/ethereum/execution-spec-tests/releases`
  (v5.4.0 or newer), which contains
  `fixtures/blockchain_tests/prague/eip2537_bls_12_381_precompiles/…` with a
  test module per precompile plus `test_bls12_variable_length_input_contracts`.

## Design decisions fixed by this plan

### Affine py_ecc style over the existing generic machinery

New arithmetic goes in a new file `Elevm/BLS.lean` (plus generated
`Elevm/BLSConst.lean`), imported by `Elevm.lean` and `Elevm/Execution.lean`.
It instantiates `FinField` / `GaloisField` / `EllipticCurve` exactly the way
the BN254 code does, mirroring the **non-optimized** py_ecc `bls12_381`
modules. No new dependencies, no Montgomery form, no projective coordinates —
except inside the SSWU port (Step 7), where following py_ecc's projective
formulas and normalizing at the end is acceptable. Existing BN254/secp256k1
definitions in `EC.lean` are not modified (blanc's proofs may depend on
them); prefer small duplication over generalizing a shared definition.

### Precompile-layer semantics are EELS's, in the codebase's own idiom

Follow the conventions already established by `executePairingCheck`,
`executeEcadd`, and `catchWithOOGPrecomp`: validation failures produce
`.error`, and the error paths/messages mirror EELS's `InvalidParameter` /
`OutOfGasError` / `KZGProofError` distinctions the same way the BN254 code
does. Semantics fixed by the final EIP-2537: G1ADD/G2ADD check on-curve but
**not** subgroup; MSM and PAIRING_CHECK require subgroup checks on every
input point; field elements are 64-byte big-endian with the top 16 bytes
zero and value < p; infinity is the all-zero encoding; scalars are raw
32-byte values, not reduced and not bounded; empty MSM/pairing input is an
error; every error consumes all supplied gas.

### Generated constants, never hand-typed

Step 7 and Step 8 need bulky constants (11- and 3-isogeny coefficient
tables, SSWU parameters, cofactor-clearing scalars, the decompressed
trusted-setup G2 point). A committed script `scripts/gen-bls-consts.py`
imports py_ecc from `~/execution-specs/venv` and *prints*
`Elevm/BLSConst.lean`; the generated file is committed alongside it and
guarded by cheap Lean `#guard`s (on-curve checks, membership checks).
Transcription by hand is forbidden.

### Vector-first verification; blockchain fixtures last

Every implementation step is gated on named official vector files running
through a dedicated harness (Step 1) that checks output bytes **and charged
gas** per vector. Blockchain-level fixtures come only at Steps 8–9, once the
unit story is airtight. This is deliberately tighter than the fixture-only
discipline of `patch.md`, because here the failure modes are silent wrong
curve points, not lifecycle bugs.

### Performance: correctness first, recorded honestly

The BN254 precedent (naive final exponentiation by a ~3000-bit exponent)
already passes fixtures within the 300 s/file budget; BLS12-381 is the same
shape with a ~4300-bit exponent. Single-pairing and small-MSM vectors must
pass comfortably. EEST stress fixtures (128-pair MSMs, many-pair pairings)
may land in the TIMEOUT tier exactly like `CALLBlake2f_MaxRounds.json`;
Step 9 records and justifies each one (perf, not correctness — demonstrated
by a green truncated variant), never hides it.

## Rules for every step

1. Read the applicable `AGENTS.md` and the `lean-inspector` / `lean-prover`
   skills before touching Lean source. Use `lean-lsp-mcp` diagnostics during
   edits. Do not run a build merely to discover a proof state; builds are
   end-of-step gates.
2. Inspect current definitions and references before editing. Line numbers
   and counts in this plan are plan-writing-time observations and may drift.
3. One step is one reviewable commit per touched repository, created by the
   user after review. Do *not* commit before user has reviewed all changes 
   manually. Do not include unrelated working-tree changes.
4. Never add `sorry`, axioms, `ofReduce*`, intentionally invalid syntax, or a
   permissive fallback that converts a wrong output into a pass.
5. Keep `/Users/bsk/blanc` building with unchanged statements for
   `weth_inv_solvent`, `stateTransition_inv_solvent`, `chain_inv_solvent`,
   and `addBlockToChain_inv_solvent`. If an elevm definition used by a proof
   must change, repair the proof in the same step.
6. Preserve `scripts/baseline-*.txt` byte-for-byte through Step 8; only
   Step 9 adds a new baseline file, and it touches no existing one.
7. Every constant is taken from the local py_ecc / EELS sources named above,
   at read time, in the session that uses it.

## Verification gates

- **V0** — `lake build` green in elevm; `lake build` green in `~/blanc` with
  the four theorem statements unchanged.
- **VEC(files…)** — the Step-1 vector harness reports every vector in the
  named files as PASS (output equality, gas equality, and for `fail-*` files
  the expected-error classification).
- **SMOKE / PATCH** — `scripts/check.sh --smoke` / `--patch` verdicts
  unchanged against their committed baselines.
- **FULL** — `scripts/check.sh --full` against `baseline-full.txt`; run at
  Steps 1 and 9 only.

Each step ends with a report in the `patch.md` style: what changed, gates
run with verdicts, timings for anything slow, and observations (including
any evidence that contradicts this plan).

## Model allocation per step

Token-efficiency guidance for which model tier to hand each step to.
Options available at plan-writing time (July 2026): Claude Code with
Fable 5 / Opus 4.8 / Sonnet 5; Codex with GPT-5.4 mini / 5.4 / 5.5 /
5.6 Luna / 5.6 Terra / 5.6 Sol (effort light–ultra); Antigravity with
Gemini 3.5 Flash (low–high) and Gemini 3.1 Pro (low–high). Substitute
current equivalents as these age.

Cross-vendor placement per published July-2026 comparisons (salt to taste
— none of them measure Lean 4):

- **Frontier**: Fable 5 and GPT-5.6 Sol. Sol leads the agentic-coding
  indexes (Artificial Analysis coding-agent 80 vs Fable's 77.2); Fable
  leads SWE-Bench Pro and FrontierMath Tier 4 (87.8 vs 83). For this plan
  the math edge is the one that matters — the frontier steps are
  diagnosis-of-algebra steps, not long-horizon engineering.
- **Near-frontier**: Opus 4.8; GPT-5.6 Terra (≈ Fable-class agentic coding
  at half Sol's price — the best price/strength point in the Codex lineup
  for this plan); GPT-5.5 at xhigh (last cycle's flagship, still solid,
  but Terra generally matches it cheaper).
- **Mid**: Sonnet 5; GPT-5.6 Luna; Gemini 3.5 Flash (strongest agentic
  model of the cheap tier — Terminal-Bench 76.2, beats 3.1 Pro on
  coding/agentic rows — but weak on deep reasoning). Gemini 3.1 Pro also
  lands here: its remaining edge over Flash (long-context, abstract
  reasoning) buys nothing for this plan and it is agentically weaker, so
  within Antigravity prefer Flash.
- **Below the floor**: GPT-5.4 mini — do not use on any step. GPT-5.4 is
  not below the floor but is dominated by Luna (newer, cheaper,
  equal-or-better); no step names it.

Three principles behind the assignments:

1. **Lean 4 competence is the floor, independent of step difficulty.**
   Every step except parts of 1 and 9 edits Lean under this repo's
   conventions (LSP-driven, no blind builds), and no public benchmark
   measures this. Mini/Haiku-class models thrash on elaboration errors
   even for "easy" edits, burning more tokens than a stronger model would.
   Before trusting a non-Anthropic mid-tier model (Luna, Flash) with a
   Lean-touching step, watch its first session on a cheap step (3 or 5);
   if it thrashes, permanently promote that vendor's Lean work one tier.
2. **The gates make under-provisioning cheap on shallow steps and expensive
   on deep ones.** For pattern-following steps (3, 4, 5), a failed session
   costs one session — the vector gate catches everything. For Steps 6 and
   7, a model that cannot *diagnose* a red vector (wrong twist, wrong sqrt
   branch, wrong `sgn0`) will grind indefinitely, because the vectors say
   only "wrong point", never why. Provision those for diagnosis, not
   transcription.
3. **Escalation rule: two focused repair attempts, then stop.** If a
   session's gate is still red after two distinct diagnosis-driven fixes
   (not retries), stop the session, write up the evidence, and re-run the
   step one tier up (or one effort setting up within the same model
   first, if not already at max). Do not let a mid-tier model iterate
   against a red pairing gate.

| Step | Difficulty | Suggested models | Rationale |
|---|---|---|---|
| 1 — vector harness | ★★★ | Sonnet 5 · 5.6 Terra/medium · 3.5 Flash/high (scripts half only) | Repo-convention plumbing, zero crypto. The one subtlety is synthesizing an honest `Evm` for `precompileRun`; escalate to Opus 4.8 or Terra/high only if that proves gnarly. |
| 2 — Fp, G1, G1ADD | ★★☆ | Sonnet 5 · 5.6 Luna/high | Direct mirror of the existing BN254 idiom with a tight gate; the plan names every pitfall (padding, infinity, no subgroup check). |
| 3 — G1 subgroup, G1MSM | ★★ | Sonnet 5 · 5.6 Luna/medium · 3.5 Flash/high | Pure horizontal scaling of Step 2; `mulBy` already exists. Cheapest Lean-competent tier — and the designated probe step for Luna/Flash Lean competence (principle 1). |
| 4 — Fp2, G2, G2ADD | ★★☆ | Sonnet 5 · 5.6 Luna/high | Instantiation work; the only trap (c0/c1 ordering) is caught immediately by the generator `#guard`s. |
| 5 — G2MSM + 288-byte fix | ★★ | Sonnet 5 · 5.6 Luna/medium · 3.5 Flash/high | The smallest step: replicate Steps 3–4's pattern plus a constant fix the plan spells out. |
| 6 — Fp12, twist, Miller loop, pairing | ★★★★★ | **Fable 5** · 5.6 Sol/xhigh (ultra on a red re-run) | The one genuinely deep step. Twist/tower/loop conventions fail silently until the vector gate, and debugging a wrong pairing requires actual algebra plus disciplined use of the bilinearity `#guard`s. Fable's FrontierMath edge makes it first choice; a failed cheap session here costs more than the premium. Not a Gemini step. |
| 7 — SSWU, isogenies, MAP precompiles | ★★★★ | Opus 4.8/high · 5.6 Terra/xhigh · 5.5/xhigh | Mechanically large, intellectually medium *given* the constant-generation script. The G2 half (Fp2 sqrt-candidate machinery, `sgn0` branches) is where diagnosis gets subtle. If splitting: G1 session can drop to Sonnet 5 or Luna/high; keep the G2 session at Opus/Terra tier. Escalate to Fable 5 or Sol/xhigh if map vectors resist two repair rounds. |
| 8 — compressed G1, KZG, point eval | ★★★☆ | Opus 4.8/medium · 5.6 Terra/high | Verbatim ports with the strongest oracle in the plan (`external_vectors.json`); the flag-bit codec and sign rule are fiddly but fully specified in local py_ecc source. Sonnet 5 is a defensible economy choice; the consensus-critical sign conventions argue one tier up. |
| 9 — EEST fixtures, baselines, closure | ★★★ | Sonnet 5 · 3.5 Flash/high · 5.6 Terra/medium | Ops and honest bookkeeping, not depth — Flash's terminal-agent strength fits the download/run/classify loop well. The TIMEOUT-justification judgment is the only part needing care, and the plan constrains it explicitly (green truncated-variant evidence required). |

A rough budget consequence: only one step strictly wants frontier strength
(Step 6), one wants near-frontier (Step 7, or just its G2 half if split),
and five of nine are comfortably mid-tier. Running everything on Fable 5
or Sol would roughly double the token cost of the arc for no change in
outcome on Steps 2–5 and 9.

---

## Step 1 — Precompile vector harness, proven on green precompiles

### Agent prompt

Work in `/Users/bsk/elevm` (`Main.lean` and `scripts/`); change no EVM
semantics. Add a vector-runner mode to the elevm executable:
`elevm --vectors <addr-hex> <file.json>`. It parses the geth-format vector
JSON described above, and for each entry synthesizes the minimal `Evm` state
needed to call `precompileRun` (inspect `executePrecomp` and the fixture
path in `Main.lean` to find the smallest honest construction) with calldata
= `Input` and gas well above `Gas`. A positive vector passes iff the result
is `.ok` with output = `Expected` and charged gas = `Gas`. A `fail-*` vector
passes iff the result is `.error`. Print one line per vector and end with
the unambiguous verdict-line contract used by `scripts/check.sh`.

Add `scripts/check-vectors.sh`: it maps committed vector files to precompile
addresses, runs each through `--vectors`, and writes
`scripts/report-vectors.txt` (gitignored). Vendor vectors under
`scripts/vectors/` as follows: commit every file under ~350 KB directly
(EIP-2537 assets: all `add`/`mul`/`map`/`pairing_check` positives and all
`fail-*`; geth: the `bls*` small files, `fail-bls*`, `pointEvaluation.json`,
and control files `bn256Add.json`, `bn256ScalarMul.json`,
`bn256Pairing.json`, `blake2F.json`, `modexp_eip2565.json`). For the two
multi-megabyte MSM files, commit `msm_G1_bls.head.json` /
`msm_G2_bls.head.json` containing the first ~32 vectors each (produced by a
committed `jq` one-liner documented in the script), and record pinned
source-commit URLs plus sha256s for the full files in
`scripts/vectors/SOURCES.md`.

Gate for this step: V0, and **VEC on the five control files** — the
already-implemented precompiles must go fully green, proving the harness
measures output and gas honestly. If a control vector disagrees with
elevm's Prague-correct behavior, investigate and report before blaming
either side; do not curate vectors to force green. All BLS/point-eval files
are expected red (stub errors) — report the full red/green matrix. Run
SMOKE and FULL once to prove the executable change did not disturb fixture
behavior. [V0 + VEC(controls) + SMOKE + FULL observation]

### Note for the reader

This is the progress meter for the whole arc, in the same sense as
`--patch` was for the lifecycle plan: intentionally red after Step 1, fixed
green end condition, no rebasing. The gas-equality check matters as much as
the output check — the discount tables and the 375/600 constants are
consensus, and blockchain fixtures would surface a gas error only as an
opaque state-root mismatch much later.

---

## Step 2 — BLS12-381 base field, G1 codec, G1ADD (0x0b)

### Agent prompt

Create `Elevm/BLS.lean`, import it from `Elevm.lean` and
`Elevm/Execution.lean`. From the local py_ecc `bls12_381_curve.py` take
`field_modulus` and `curve_order` and define `blsPrime`, `blsCurveOrder`,
`abbrev BLSF := FinField blsPrime`, `abbrev BLSP := EllipticCurve BLSF 0 4`.
Implement the EIP-2537 codecs, mirroring the EELS `bls12_381/__init__.py`
functions and elevm's own `B8L.toExStrBNP` idiom: 64-byte field-element
decode (exact length; top 16 bytes zero; value < p — reject otherwise),
128-byte G1 decode (all-zero ⇒ infinity `⟨0,0⟩`; else both coordinates
decoded and the point checked on-curve via `EllipticCurve.mk?`), and the
inverse encoders (infinity ⇒ 128 zero bytes). Before wiring the precompile,
confirm with `#guard` that the py_ecc G1 generator decodes, is on curve,
and re-encodes to itself, and verify `EllipticCurve.add` handles the
`p = q` doubling case (the BN254 ecadd path already relies on this;
confirm, don't assume).

Define `gasBlsG1Add := 375` next to the other BLS gas constants and rewrite
`executeBls12G1Add` to mirror EELS `bls12_g1_add`: length check (256),
charge 375 via `PrecompResult.chargeGas`, decode both points (**no**
subgroup check), add, encode. [V0 + VEC(add_G1_bls.json,
fail-add_G1_bls.json, blsG1Add.json, fail-blsG1Add.json) + SMOKE]

### Note for the reader

Smallest possible first arithmetic step, and it fixes the missing-gas
defect. The geth `blsG1Add.json` file is 99 KB of edge cases (infinity
arms, doubling, negations) — much stronger than the EIP file alone.

---

## Step 3 — G1 subgroup check and G1MSM (0x0c)

### Agent prompt

In `Elevm/BLS.lean` add the subgroup check: `p * blsCurveOrder = ⟨0,0⟩`
using the existing binary `EllipticCurve.mulBy` (verified double-and-add;
255-bit scalars are fine). Add the 160-byte pair decoder mirroring EELS
`decode_g1_scalar_pair`: G1 point decoded **with** subgroup check, then a
raw 32-byte big-endian scalar, unreduced. Rewrite `executeBls12G1Msm`'s
inner logic (keep the existing length/gas code, which is already correct
for G1): naive Σ scalarᵢ·pointᵢ over the pairs, encode the sum. Rename
`lengthPerPair` to `g1MsmLengthPerPair` and leave a `g2MsmLengthPerPair`
TODO comment only if Step 5 is not being done in the same session — do not
change the G2 stub here. [V0 + VEC(mul_G1_bls.json, fail-mul_G1_bls.json,
msm_G1_bls.head.json, fail-msm_G1_bls.json, blsG1Mul.json,
fail-blsG1Mul.json) + Step-2 files stay green]

### Note for the reader

The `mul` vectors exercise k=1 MSM including the subgroup-check rejections
that G1ADD is forbidden from making — the difference between Steps 2 and 3
is exactly the EIP's on-curve-vs-subgroup distinction. Scalars are *not*
reduced mod r; with the subgroup check in force this is mathematically
inert, but the byte-level validation differences are what the fail vectors
probe.

---

## Step 4 — Fp2, G2 codec, G2ADD (0x0d)

### Agent prompt

In `Elevm/BLS.lean` define the quadratic extension exactly the way the BN254
code defines `BNF2` over `GaloisField` (inspect the `BNF2` definition and
its modulus-polynomial representation first, then instantiate the same
shape for `blsPrime` with u² + 1, py_ecc `FQ2_MODULUS_COEFFS = (1, 0)`).
Define `BLSP2 := EllipticCurve BLSF2 0 b2` with `b2 = 4(1+u)` (py_ecc
`b2 = FQ2([4,4])`). Implement the 256-byte G2 codec per EELS
`bytes_to_fq2` / `bytes_to_g2`: x.c0 ‖ x.c1 ‖ y.c0 ‖ y.c1, each a 64-byte
padded field element; all-zero ⇒ infinity. `#guard` the py_ecc G2 generator
round-trips and is on curve. Rewrite `executeBls12G2Add` (gas 600 is
already charged by the stub): decode both points without subgroup check,
add, encode. [V0 + VEC(add_G2_bls.json, fail-add_G2_bls.json,
blsG2Add.json, fail-blsG2Add.json) + Steps 2–3 files stay green]

### Note for the reader

Pure instantiation work — the generic `GaloisField` arithmetic and the
generic curve group law do everything. The only new failure surface is the
c0/c1 byte ordering, which the fail vectors and generator round-trip pin
down immediately.

---

## Step 5 — G2 subgroup check, G2MSM (0x0e), and the 288-byte pair fix

### Agent prompt

Fix the latent defect first: introduce `g2MsmLengthPerPair := 288` and make
`executeBls12G2Msm` use it for the modulus check, `k`, and therefore gas
(`Elevm/Execution.lean:3163`–`3168` at plan-writing time); G1 keeps 160.
Then implement the G2 pair decoder (subgroup-checked point + raw scalar)
and the naive MSM sum, mirroring Step 3. [V0 + VEC(mul_G2_bls.json,
fail-mul_G2_bls.json, msm_G2_bls.head.json, fail-msm_G2_bls.json,
blsG2Mul.json, fail-blsG2Mul.json) + all previous vector files stay green +
SMOKE]

### Note for the reader

The 160-vs-288 bug is invisible today because the stub always errors, but
it is a consensus bug the moment G2MSM returns values: every valid G2MSM
input would be rejected as mis-sized, and gas would be computed from a
wrong k. The gas-equality check in the harness is what proves the fix.

---

## Step 6 — Fp12 tower, twist, BLS Miller loop, PAIRING_CHECK (0x0f)

### Agent prompt

Read py_ecc's `bls12_381_curve.py` and `bls12_381_pairing.py` (non-optimized)
and EC.lean's BN254 `twist` / `linefunc` / `millerLoop` before writing
anything. Define `BLSF12` over `GaloisField` with modulus w¹² − 2w⁶ + 2
(py_ecc `FQ12_MODULUS_COEFFS = (2,0,0,0,0,0,-2,0,0,0,0,0)`), and `BLSP12`.
Port the BLS twist exactly from py_ecc — it is **not** the BN254 twist;
copy the coefficient shuffle verbatim. Duplicate `linefunc` for the BLS
types rather than generalizing the BN one. The BLS Miller loop iterates the
bits of `ate_loop_count = 15132376222941642752` top-down with the same
double/add-line accumulation as BN254 but with **no** pseudo-binary
negative digits and **no** Frobenius tail lines — then the same naive final
exponentiation `f ^ ((blsPrime^12 − 1) / blsCurveOrder)`. Follow py_ecc's
convention exactly and do not "correct" it: PAIRING_CHECK only tests
whether a product of pairings is 1, so the convention must merely be
self-consistent. Define `blsPairing (q : BLSP2) (p : BLSP)` with the same
guard structure as the BN `pairing` (on-curve guards, infinity ⇒ 1).

Add `#guard` bilinearity sanity checks before touching the precompile:
e(2·G1gen, G2gen) = e(G1gen, 2·G2gen) and e(G1gen+G1gen, G2gen) likewise
(computed once; if these are slow, note the wall time in the report).
Then rewrite `executeBls12Pairing` mirroring EELS `bls12_pairing` and the
existing `executePairingCheckInner` shape: 384-byte units (128-byte G1 ‖
256-byte G2), both decoded **with** subgroup checks, product of pairings
compared to 1, 32-byte 0/1 output. Record the wall time of the pairing
vector file in the report. If the session budget runs out, the sanctioned
split is: 6a = tower + twist + Miller loop + `#guard`s, 6b = precompile
wiring + vectors. [V0 + VEC(pairing_check_bls.json,
fail-pairing_check_bls.json, blsPairing.json, fail-blsPairing.json) +
earlier files stay green]

### Note for the reader

The single genuinely deep step, and still smaller than it looks: the BN254
Miller loop in EC.lean is the *harder* variant (negative digits plus two
Frobenius line evaluations), so this is a simplifying port with new
constants. The dangerous parts are the twist and the tower modulus — both
are pure transcription from py_ecc, and a wrong choice fails the generator
`#guard`s and bilinearity checks immediately, long before vectors run.

---

## Step 7 — SSWU maps, isogenies, cofactor clearing, MAP precompiles (0x10, 0x11)

### Agent prompt

Write `scripts/gen-bls-consts.py` (run with
`~/execution-specs/venv/bin/python`): it imports
`py_ecc.optimized_bls12_381.optimized_swu`, `optimized_clear_cofactor`, and
`constants`, and prints `Elevm/BLSConst.lean` containing every constant the
maps need — SSWU parameters and Z values for both curves, the 11-isogeny
(G1) and 3-isogeny (G2) coefficient tables, the Fp2 square-root helper
constants (the eta / roots-of-unity tables py_ecc uses), and both effective
cofactor scalars from `optimized_clear_cofactor.py`. Commit the script and
its output; hand-transcribing any of these is forbidden. Guard the
generated file with `#guard`s where cheap.

Then port, following `py_ecc.bls.hash_to_curve.map_to_curve_G1/G2` and
`clear_cofactor_G1/G2` down through `optimized_swu.py`: SSWU onto the
isogenous curve, the isogeny map, and cofactor clearing by scalar
multiplication with the generated h_eff values, plus RFC 9380 `sgn0` and
the Fp sqrt (exponent (p+1)/4) / Fp2 sqrt-candidate machinery py_ecc uses.
py_ecc works in projective coordinates; porting projectively and
normalizing at the end is acceptable — field inversion exists. Rewrite
`executeBls12MapFpToG1` and `executeBls12MapFp2ToG2` (gas already charged
by the stubs): decode one 64-/128-byte field element (reject ≥ p; note
these precompiles take field elements, **not** curve points — no on-curve
or subgroup validation of inputs), map, clear cofactor, encode. The
sanctioned split is one session per map (G1 first; G2 adds the Fp2 sqrt
dance). [V0 + VEC(map_fp_to_G1_bls.json, fail-map_fp_to_G1_bls.json,
map_fp2_to_G2_bls.json, fail-map_fp2_to_G2_bls.json, blsMapG1.json,
blsMapG2.json + geth fails) + earlier files stay green]

### Note for the reader

Mechanically the largest step (the isogeny tables are ~80 field constants)
but intellectually shallow once the constants are generated rather than
typed. The output must match the *exact* RFC 9380 clear_cofactor scalars —
multiplying by the plain cofactor also lands in the subgroup but at a
different point, which the vectors catch instantly. This step needs Step 2
(and Step 4 for G2) but not the pairing; it can be reordered before Step 6
if desired.

---

## Step 8 — Compressed G1, KZG verification, POINT_EVALUATION (0x0a)

### Agent prompt

Port from the local `~/execution-specs/src/ethereum/crypto/kzg.py` and
`.../prague/vm/precompiled_contracts/point_evaluation.py`, with
`py_ecc/bls/point_compression.py` for the codec. Implement: 48-byte
compressed G1 decoding with the ZCash flag bits (compression flag must be
set; infinity flag; y-sign flag; y recovered via sqrt of x³+4 with the
(p+1)/4 exponent and selected by the sign rule — copy `decompress_G1` and
its validation exactly), `validate_kzg_g1` (decode + subgroup check),
`bytes_to_bls_field` (32-byte BE, must be < `blsCurveOrder`, which is
EIP-4844's `BLS_MODULUS`), and `verify_kzg_proof_impl` as a two-pair
pairing check copied verbatim from `kzg.py` (it reuses Step 6's Miller
loop; the convention is consistent by construction). Extend
`scripts/gen-bls-consts.py` to decompress `KZG_SETUP_G2_MONOMIAL_1`
(`kzg.py:71`) via py_ecc and emit the affine G2 point into
`Elevm/BLSConst.lean`, `#guard`ed on-curve and in-subgroup.

Rewrite `executePointEval` mirroring EELS `point_evaluation`: exact
192-byte layout versioned_hash(32) ‖ z(32) ‖ y(32) ‖ commitment(48) ‖
proof(48); charge 50000 gas (take the constant name/order of operations
from EELS, not from memory); check versioned_hash = 0x01 ‖
sha256(commitment)[1:] using the existing sha256; validate fields and both
compressed points; verify the KZG proof; on success output exactly 64
bytes: uint256(4096) ‖ uint256(BLS_MODULUS); every failure is the
`KZGProofError` path. Then run the on-disk EEST fixtures:
`ELEVM_FIXTURES=$HOME/execution-specs/tests/fixtures/latest_fork_tests/fixtures/blockchain_tests scripts/check.sh --dir cancun/eip4844_blobs/point_evaluation_precompile`
(and `…_gas`). These are EEST-generated Cancun-network fixtures; the first
run is evidence-gathering — if the runner rejects their format or network
tag, report exactly what and why, fix only trivially-safe runner gaps in
this step, and defer anything structural to Step 9 with a written note.
[V0 + VEC(pointEvaluation.json) + the EEST point-eval dir observation +
SMOKE]

### Note for the reader

Everything hard was finished in Step 6; this step is codecs plus a
two-pairing formula plus one trusted-setup constant. `pointEvaluation.json`
has a single vector, so the real weight sits in the EEST directory —
`external_vectors.json` embeds the official consensus-spec-tests KZG suite,
which is as strong a correctness oracle as exists for this precompile.

---

## Step 9 — Prague EEST fixtures, baselines, and closure

### Agent prompt

Download one pinned EEST fixture release (`fixtures_stable.tar.gz` from
`https://github.com/ethereum/execution-spec-tests/releases`, v5.4.0 or the
current latest; record tag and sha256 in `scripts/vectors/SOURCES.md`) and
unpack outside the repo (e.g. `~/eest-fixtures`). Run
`scripts/check.sh --dir` over
`blockchain_tests/prague/eip2537_bls_12_381_precompiles` (whole tree, per
precompile subdirectory) and re-run the Step-8 point-evaluation
directories, with `ELEVM_FIXTURES` pointed at each fixture root. Classify
every file. Commit `scripts/baseline-bls.txt` as a **target gate** in the
`--patch` sense: every listed file PASS, except an explicit TIMEOUT list in
which each entry carries a one-line perf justification backed by a green
unit-vector or truncated-variant equivalent (stress MSM/pairing files are
the expected members). Wire a `--bls` tier into `check.sh` following the
existing tier pattern. Re-run SMOKE, PATCH, and FULL against their
untouched baselines. Audit that
`rg -n "not implemented|UNIMP" Elevm/` reports nothing on any precompile
path, and that `git log` shows one commit per step. Close with a final
report: the full vector matrix, the fixture matrix with timings, the
TIMEOUT inventory with justifications, and an explicit statement of what
now remains of review.md finding 3.3 (expected: nothing). [V0 +
VEC(everything) + BLS target gate + SMOKE + PATCH + FULL]

### Note for the reader

The green end condition for the arc: official unit vectors, geth's
extended vectors, and EEST consensus fixtures all pass, with any TIMEOUT
individually justified as performance rather than correctness. After this
step the review.md sentence "ELeVM cannot presently be described as
feature-complete Prague semantics" has no remaining basis in section 3.3.
