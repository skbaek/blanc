# Lido artifact profile baseline

`artifact-profile-baseline.json` is generated evidence for the exact
pre-optimization Blanc candidate `fc3edee6dbfb77eaf344afee43c921d48ff8a3af`.
It contains no runtime or creation byte literal. Blanc identities and layout
come from `eval-lido-circuit-breaker-artifacts.lean`; Solidity identities come
from the schema-v2 reference lock and its locked compiler source maps.

Check the committed baseline and all live falsifiers with:

```sh
scripts/check-lido-circuit-breaker-artifact-profile.sh
```

Deliberate regeneration is explicit and recovers the frozen differential
manifest from the exact launch commit before writing:

```sh
scripts/check-lido-circuit-breaker-artifact-profile.sh --write-baseline
```

`--print-current` prints the canonical reconstruction without writing it. The
schema independently pins artifact/table/immutable/gas identities, region
partitions must cover every byte exactly once, and a separate falsifier pins
the complete generated ledger digest. The evaluator walks `Func.branch` in
compiler byte order; the profiler requires all 17 endpoint spans to be
instruction-aligned, nonoverlapping, exactly 1,930 bytes in total, and to
contain every immutable payload interval. Optimization work should retain
this baseline rather than regenerate it to follow a changed candidate.

The ownership label is the lowest code owner that can change the emitted byte
in this baseline. Jaune supplies EVM semantics and instruction types, but the
measured table, branch, dispatcher, and fixed-width choices are emitted by
Blanc common code or selected by Lido-private helpers; consequently the
baseline assigns zero bytes directly to Jaune. Solidity-compiler and
reference-interface-data are provenance-only comparison categories.
