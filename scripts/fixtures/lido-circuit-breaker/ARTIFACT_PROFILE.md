# Lido artifact profiles

`artifact-profile-baseline.json` is generated evidence for the exact
pre-optimization Blanc candidate `fc3edee6dbfb77eaf344afee43c921d48ff8a3af`.
It is an immutable launch fixture, pinned byte-for-byte at SHA-256
`b0a59c180afac1cb1b853b747696523334c774f269001492b9109012ce6f9e7f`.
The ordinary checker never reconstructs or rewrites it from the current
production program.

`artifact-profile-optimized.json` is separately generated from the current
production evaluator. It pins the final 4,282-byte runtime, 616-byte
constructor prefix, 4,898-byte creation template, and 5,122-byte full CREATE
input in both official and independent parameter worlds. Its SHA-256 is
`ba3a0d93118ff80453920d6f05801ab25d9c232f3bba7471e39936931b1a8920`.
The optimized profile derives a complete before/after partition subtraction
from the frozen ledger: runtime −615 bytes, constructor prefix −1,997 bytes,
and creation template/full CREATE −2,612 bytes.

Both ledgers contain no runtime or creation byte literal. Blanc identities and
layout come from `eval-lido-circuit-breaker-artifacts.lean`; Solidity identities
come from the schema-v2 reference lock and its locked compiler source maps.
The optimized ledger additionally pins the exact 23-entry runtime table,
17 instruction-aligned endpoint spans, 11-entry constructor table, 12 immutable
lanes, 21 source-selected constructor coordinate PUSH2 instructions, complete
partitions, disassembly summaries, ownership totals, and before/after role
attribution.

Check both committed ledgers and all live falsifiers with:

```sh
scripts/check-lido-circuit-breaker-artifact-profile.sh
```

The launch ledger has no regeneration mode. Deliberate regeneration of the
optimized ledger is explicit and still refuses any artifact identity or layout
outside the independent W5 pins:

```sh
scripts/check-lido-circuit-breaker-artifact-profile.sh --write-optimized
```

`--print-current` prints the canonical optimized reconstruction without writing
it. The independent schema pins artifact/table/endpoint/constructor/immutable/
coordinate identities, every region partition covers every byte exactly once,
and the falsifier pins both complete ledger digests. The evaluator walks
`Func.branch` in compiler byte order; the optimized profiler requires all 17
endpoint spans to be instruction-aligned, nonoverlapping, exactly 1,760 bytes
in total, and to contain every immutable payload interval.

The ownership label is the lowest code owner that can change the emitted byte
in this baseline. Jaune supplies EVM semantics and instruction types, but the
measured table, branch, dispatcher, and coordinate choices are emitted by
Blanc common code or selected by Lido-private helpers; consequently both
profiles assign zero bytes directly to Jaune. Solidity-compiler and
reference-interface-data are provenance-only comparison categories. The
frozen profile retains GAS-1…GAS-5 launch attribution; complete optimized gas
vectors remain owned by the differential manifest and are not duplicated here.
