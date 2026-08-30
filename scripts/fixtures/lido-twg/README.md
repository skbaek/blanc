# Lido TWG differential fixture

`manifest.json` is generated evidence for the pinned Lido
`TriggerableWithdrawalsGateway` differential. It is not a handwritten test
oracle and must be refreshed only by the generator's explicit
`--write-manifest` route.

Both sides start in a fresh Prague state and execute their own complete CREATE
input. Solidity bytes come only from the validated B1 lock. Blanc bytes come
only from `scripts/eval-lido-twg-artifacts.lean`. The engine is
`ethereum/execution-specs` at commit
`4198b9c5996713b268aed602739d5aa40e277694`.

## Coverage criterion

The manifest owns at least one direct action row for every one of the 24
census selectors and complete-constructor rows. Cross-cut rows cover:

- finite and infinite-sentinel arms of both `pauseFor` and `pauseUntil`, both
  pause polarities, exact already-paused `ResumedExpected` failures, and the
  exact resumed-state `PausedExpected` failure for `resume`;
- all seven role-gated negative entries, grant/revoke/renounce, membership,
  count, enumeration, and the two hostile role-layout histories;
- limit configuration validation, consumption, insufficient quota, same-frame
  behavior, whole-frame restoration, and capping;
- mock locator, withdrawal-vault, staking-router, and refund-recipient worlds,
  including fee multiplication, exact vault value, router notification,
  explicit and zero-recipient refunds, rollback, gateway ETH preservation,
  dependency failure bubbling, and relevant events; and
- the exact 23 named gas rows consumed by the claim-document synchronizer.

## Logical projection and channels

Solidity's packed/keccak storage and Blanc's tagged flat storage are projected
independently onto pause state, the five exit-limit fields, role admin and
membership, per-role ordered members, selected balances, and selected mock
storage. Raw slots and storage roots are outside the claim.

Rows name the channels they compare: outcome status, returndata, projected
state, ETH balances, logs, and full CALL/STATICCALL traces. Event rows assert
the exact source-census topic0 (and exact constructor event order); the
unreachable `RoleAdminChanged` identity owns an explicit non-emission row.
Trigger fee paths assert one fee query and one vault call with exact selector
and value, router paths assert one notification with the exact selector, and
refund rows assert target/value and zero retained gateway ETH. These checks
also cover the corresponding dependency-revert rows, so empty mocks cannot
make the choreography claims vacuous.

## Stable behavioral differences

Only these exact differences are admitted, each with a fixed field set and at
least one discriminating row:

- `TWG-D01`: the seven unauthorized role-gate returndata payloads;
- `TWG-D02`: wrong-account `renounceRole` returndata;
- `TWG-D03`: out-of-bounds `getRoleMember` returndata;
- `TWG-D04`: cross-role removal enumeration order and the returned ordinal;
- `TWG-D05`: the flat full-identity role-key collision refusal.

No unknown mismatch allowlist exists. Removing a deviation row, widening its
field set, or making a declared difference stop discriminating fails schema
validation.

## Regeneration and checking

From the repository root, with a clean pinned EELS checkout at
`$EELS_ROOT` (default `~/execution-specs`):

```sh
scripts/check-lido-twg-differential.sh
scripts/check-lido-twg-differential.sh --write-manifest
```

Ordinary checking is offline. The wrapper evaluates the production-owned Blanc
artifacts, executes the generator under pinned EELS, validates the independent
schema, runs manifest/channel/identity/semantic falsifiers, and checks both
machine-filled compatibility documents against the manifest. The B1 lock and
census gates remain independent prerequisites.
