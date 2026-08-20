# Forward discharge trace inventory

`Blanc.Forward` emits one `BLANC_DISCHARGE_V1` record for each profiled gas,
room, or value discharge when its trace class is enabled. The reader is
opt-in and is not part of a blocking gate.

## Capture and read

Use the weak option form below. The trace option is registered by the imported
library, so `-Dtrace.Blanc.Forward.discharge=true` is not sufficient:

```sh
lake env lean -Dweak.trace.Blanc.Forward.discharge=true Blanc/LidoCircuitBreakerPauseWalk.lean 2>&1 \
  | scripts/read-discharge-trace.py
```

The reader also accepts a saved trace path. Non-trace compiler output is
ignored, but every line containing `BLANC_DISCHARGE_` is parsed fail-closed.
An unknown schema, missing field, duplicate/unknown field, or malformed value
fails with a named diagnostic and exit status 2.

Output is deterministic TSV, one row per `(kind, outer, subject)`:

```text
kind  outer  subject  frequency  total_elapsed_ns  median_elapsed_ns  outcome_mix
```

The record fields are:

| Field | Values / meaning |
|---|---|
| `BLANC_DISCHARGE_V1` | Schema marker; unknown versions are rejected |
| `kind` | `gas`, `room`, or `value` |
| `outer` | Proposition-head class |
| `subject` | Equality left-hand-side head, or `outer` for non-equalities |
| `out` | `assigned`, `exactLocal`, `tactic`, or `residual` |
| `idx` | Tactic index as a decimal, or `na` |
| `attempts` | Non-negative decimal tactic-attempt count |
| `elapsed_ns` | Non-negative elapsed nanoseconds |

Run the lightweight parser controls with:

```sh
python3 scripts/test-read-discharge-trace.py
```
