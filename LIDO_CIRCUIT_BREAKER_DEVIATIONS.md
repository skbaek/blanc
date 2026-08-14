# Lido CircuitBreaker deviation registry

This is the registry required by `PORTING.md`. An observable difference from
the pinned v1.0.0 reference that is not entered and defended here is a defect.
This initial registry accepts **no behavioral deviation** and contains no
mismatch allowlist. A finite passing differential row is evidence only; it is
not permission to omit a discovered difference.

## Accepted behavioral deviations

None. Any discovered observable mismatch must be repaired or added here before
a conformance claim, with reference behavior, Blanc behavior, consequence,
informed-deployer stance, and named evidence.

## Low-level implementation freedoms (not behavioral deviations)

| Freedom | Boundary | Evidence obligation |
|---|---|---|
| Runtime/initcode bytes, code hash, dispatcher shape, and instruction sequence | Byte identity is a permanent non-goal under `PORTING.md`. | Generated Blanc artifact identity and lock provenance; never cite as Solidity-byte equality. |
| Raw persistent/transient storage keys and layout | The comparison projects both worlds to logical configuration, Registry, expiry, and pause state. | Projection is frozen and differential rows do not compare raw slots. |
| Exact gas and OOG threshold | Exact gas equality is excluded; adequate-gas behavior and returndata-size scaling remain observable evidence. | Measured scaling/OOG controls and a stated adequate-gas envelope. |
| Internal helper/table decomposition | Private factoring is free only if it changes no declared status, returndata, projected state, ETH, logs, or call trace. | Artifact and differential channels. |

## Explicit exclusions and verification debts

| Exclusion | Not a deviation stance | Future owner |
|---|---|---|
| Universal Registry integrity and arbitrary-length enumeration | Not established; finite histories do not prove either property. | S2/S3 successor goals. |
| Arbitrary-descendant hostile reentry, access completeness, and actual-write classification | Not established; finite callback rows are not a theorem. | S4/S5 successor goals. |
| Jaune deployment correctness, arbitrary deployment shapes, sequence/history preservation, and monitoring theorems | Not established; constructor differential worlds are finite executable evidence. | S6/closure successor work. |
| Deployed Solidity bytecode verification or universal Solidity/Blanc equivalence | Not claimed by a Blanc port. | Separate verification project if desired. |

No exclusion authorizes a known in-scope observable mismatch. It limits only the
claim, consistently with `PORTING.md`.
