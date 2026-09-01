# Proxy-pair upgrade relation and migration

This document is the public claim boundary for the goal-local v1/v2 witness
behind Blanc's exact compiled OssifiableProxy. It separates three facts that
must not be conflated: a state migration is sound for a relation, the proxy
actually executes that migration, and later calls refine one another through
the proxy.

## Exact product claim

An authorized execution of the exact compiled Blanc OssifiableProxy
`upgradeToAndCall` route atomically changes the implementation from the named
v1 code to the named v2 code and executes `initializeV2()` over proxy-owned
storage. The selected call has nonempty setup calldata and `forceCall = false`.
It copies the protected logical word from S1 (slot 7) to S2 (slot 8), writes
the initialization marker `1` to slot 9, and establishes the initialized v2
domain and the named R2 relation.

From related pre/post states, subsequent calls through that same proxy agree
on `value()` and every `setValue(uint256)` input. This conclusion uses exact
compiled implementation children and the existing arbitrary-child forwarding
envelope. It explicitly discharges `DirectTargetTransport` for the scalar
input word and retains the G-5 forwarded-child-budget premise; it is not a
claim about GAS-sensitive child code.

The exact execution package is demonstrably inhabited. Its v1 and v2 child
messages are the actual children selected by the two forwarding descriptors;
their output and proxy-owned storage effects are derived from compiled walks,
not accepted as certificate fields. Retained `processMessage` certificates
and exact clean-tail budgets then settle both children through the wrapper.

The exact compiled `upgradeTo` entry realizes the identity application-state
specialization, and skipped `upgradeToAndCall(v2, [], false)` has the same
application-storage effect. Either identity route preserves R2 only under the
explicit identity-admissibility premise. The ordinary witness is deliberately
not identity-admissible, so `upgradeTo` alone is a biting insufficient-
migration control rather than the product migration.

## Frozen witnesses

| Role | Exact value |
|---|---|
| Proxy | `0x00000000000000000000000000000000000a0001` |
| v1 implementation | `0x00000000000000000000000000000000000b0002` |
| v2 implementation | `0x00000000000000000000000000000000000b0003` |
| Admin and caller | `0x00000000000000000000000000000000000c0003` |
| Shared getter | `value()` / `0x3fa4f245` / `[0x3f, 0xa4, 0xf2, 0x45]` |
| Shared setter | `setValue(uint256)` / `0x55241077` |
| Initializer | `initializeV2()` / `0x5cd8a76b` / `[0x5c, 0xd8, 0xa7, 0x6b]` |
| New v2 getter | `migrationMarker()` / `0x8d8a346e` |
| Scalar layout | S1=`7`, S2=`8`, marker=`9`, marker value=`1` |
| Compiled artifacts | v1=`74` bytes, v2=`141` bytes; proved distinct |

V1's two shared entries load/store only S1. V2's corresponding entries
load/store only S2; they do not inspect the marker and do not branch between
layouts. V2 adds the initializer and marker getter. The three scalar slots are
pairwise distinct and separately proved unequal to the ERC-1967
implementation, admin, and beacon slots.

The ordinary prestate installs the exact 2,188-byte proxy runtime and both
exact implementation codes, with implementation=v1, admin=caller, S1=42,
S2=0, and marker=0. The primary result has implementation=v2, S1=42, S2=42,
and marker=1.

## Public theorem surface

The generic layer in `Blanc.Upgrade` owns:

- `Blanc.UpgradeArchitecture`, whose five explicit fields are `proxyProg`,
  `v1`, `v2`, `migration`, and `relation`;
- `Blanc.MigrationSound`, which says only that a named migration establishes
  the v2 domain and relation; and
- `Blanc.BehavioralRefinement`, which says only that shared logical steps
  agree and preserve the relation.

The product layer in `Blanc.ProxyPair.Upgrade` owns the ten audited headlines:

| Family | Declaration | What it establishes |
|---|---|---|
| Pure migration | `migration_establishes_initializedDomain` | The eager S1-to-S2 migration writes the marker. |
| Pure migration | `migration_sound` | The named migration establishes both the v2 domain and R2. |
| R2 | `shared_getter_refinement` | `value()` returns the same protected word. |
| R2 | `shared_setter_refinement` | Every word input updates the two representations coherently. |
| Primary execution | `upgradeToAndCall_primary_realizes_migration` | The exact authorized compiled proxy and compiled initializer derive the complete post-storage formula, initialized domain, and R2. |
| Identity execution | `upgradeTo_realizes_identity` | Exact `upgradeTo` changes only the implementation word in application storage. |
| Identity execution | `upgradeToAndCall_skipped_empty_realizes_identity` | Empty/non-forced setup takes the skip branch and has the same application-storage shape. |
| Identity soundness | `upgradeTo_identity_sound_of_admissible` | Preserved application words carry initialized-domain R2 only from an admissible prestate. |
| Proxy refinement | `throughProxy_primary_refinement` | Exact v1/v2 compiled children settle through exact forwarding envelopes after the primary migration. |
| Proxy refinement | `throughProxy_identity_refinement_of_admissible` | The same wrapper result follows after an identity route only with the explicit admissibility and preservation premises. |

Three additional assurance theorems close premise satisfiability and direct
composition:

| Declaration | What it establishes |
|---|---|
| `fixture_exactProxyPairSharedExecution_value` | A closed v1/v2 `value()` pair inhabits the complete exact forwarding package, including descriptor-selected children, compiled walks, retained settlements, and tail budgets. |
| `fixture_throughProxy_value_refinement` | That closed package produces a concrete settled through-proxy refinement result. |
| `upgradeToAndCall_primary_throughProxy_refinement` | One exact primary upgrade execution supplies its own initialized-domain and R2 facts to the later through-proxy theorem. |

Every headline and assurance theorem's kernel axiom set is pinned to exactly
`propext`, `Classical.choice`, and `Quot.sound` by
`scripts/ProxyPairUpgradeAxiomCheck.lean` and the goal gate.

## Execution premises retained by the statements

The primary theorem keeps the proxy program as an explicit argument and
requires equality to the exact `runtimeBaseline`; it does not hide the proxy
in a namespace constant. Its hypotheses include the actual compiled outer
walk, proxy storage owner, exact caller and authorization words, live admin,
installed v1 implementation, installed exact v2 code, implementation commit,
nonempty setup boundary, exact compiled v2 child, child settlement, and exact
initializer calldata.

The wrapper refinement statements retain both exact forwarding routes and
their valid-installation facts. `ExactForwardingContext` records current
target/storage owner, code address, exact code, gas word and EIP-150 split,
depth decrement, warm address and storage-key sets, access/extension/call
costs, no value transfer, and the child gas. `ForwardingTailBudget` retains
the parent's post-child G-5 tail budget. No universal gas dominance follows.
`V1SharedChildExecution` and `V2SharedChildExecution` retain the exact compiled
walk, actual settled-child certificate, clean polarity, and initial
proxy-storage equality. They do not store claimed output or post-storage
effects; `logical_effect` derives both from the walks.

Migration soundness and behavioral refinement are separate conclusions. A
proof of one is never evidence for the other, and neither contains an opaque
certificate that assumes the desired postcondition.

## Executable witnesses and controls

`scripts/ProxyPairUpgradeWitness.lean` executes the exact compiled artifacts
under Prague and emits twelve labelled rows. The goal gate pins their complete
output. The primary row succeeds with implementation=v2, S1=42, S2=42,
marker=1, one log, and empty output. The `upgradeTo` and skipped-empty rows
succeed with implementation=v2 while retaining S2=0 and marker=0. The
relation row confirms the primary poststate is initialized and R2-related,
the ordinary state is not identity-admissible, and a poststate with S2=41
violates R2.

Four rows start from the actual primary poststate and execute through the
exact proxy again. `POST_VALUE` returns word 42, `POST_SET` writes S2=73,
`POST_GET` returns that updated word 73, and `POST_MARKER` returns the exact
v2-only marker word 1. These rows keep implementation=v2 and marker=1, so the
behavioral witness is genuinely post-upgrade rather than a detached direct
implementation run.

Four failure rows execute as well:

- an unauthorized caller;
- an ossified proxy (zero admin);
- absent v2 code; and
- setup calldata that reaches the v2 fallback and reverts.

Each settles with an error and restores implementation=v1, S1=42, S2=0, and
marker=0. `upgradeToAndCall_message_atomicRollback` is the theorem-level
message-settlement boundary: persistent and transient state roll back, so
failed setup cannot leave the committed implementation or child storage
writes in the settled world. The `REVERTING_SETUP` row deliberately reports
`logs=1`: the returned error machine retains the raw setup log observation;
that is not a claim that the reverted log is committed to the settled world.

The fail-closed checker also exercises disposable source/evidence mutants for
wrong headline names, wrong axiom expectations, a hidden or wrong proxy
program, v1=v2, a removed satisfiability witness, an R2 mutation, a missing
owner/context/budget premise, a detached child run, a reintroduced stored
effect field, disabled post-upgrade value or marker rows, a disabled rollback
row, a missing root import, contract-local placement of generic vocabulary,
and stale/shortened public evidence. Reverting the one mutation restores the
baseline checker result.

## Deliberate non-claims

- This is R2 equality on the named shared-selector set and logical storage
  projection. It is not full-surface R1: the v2-only marker getter and retained
  stale S1 word are outside the protected projection. It is not invariant-only
  R3 either.
- It proves properties of Blanc programs under Jaune's modeled semantics. It
  does not verify deployed Solidity, historical mainnet state, deployed byte
  identity, or every Lido upgrade.
- It is not a theorem about arbitrary proxies, arbitrary programs, arbitrary
  migrations, or arbitrary relations.
- Forced-empty setup and redeploy-and-migrate are not product migration routes.
- Scalar slots are checked against the three named ERC-1967 slots only; no
  global collision theorem, mapping layout, or hash assumption is claimed.
- The implementation witnesses are goal-local members of the existing
  proxy-pair family. This does not select a one-proxy/many-independent-
  implementations architecture.
- The forwarding result excludes a GAS-sensitive compatibility claim and
  makes no universal liveness or gas-dominance claim.

## Evidence owner

Run `scripts/check-proxy-pair-upgrade.sh` from the Blanc checkout under test.
It checks the exact public surface, static claim boundary, forbidden trust
escapes, root/layer placement, kernel axiom pins, and executable witness rows.
Its `--self-test` mode runs the disposable enforcement mutants. The gate is
registered in `scripts/GATES.md`, the selective gate registry, and CI.
