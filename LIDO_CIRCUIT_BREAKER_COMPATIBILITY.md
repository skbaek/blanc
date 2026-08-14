# Lido CircuitBreaker compatibility contract

This document freezes the public conformance boundary for the Blanc port of
Lido CircuitBreaker v1.0.0.  It is read with `PORTING.md`: the port does not
claim Solidity-bytecode, code-hash, gas, or raw-storage-layout identity.
It claims only the declared interface behavior supported by named evidence.
The pinned reference lock and differential manifest, when landed, are the
authorities for exact selectors, source identities, and finite observations.

## Runtime endpoints

<!-- LIDO-CIRCUIT-BREAKER-ENDPOINT {"signature":"ADMIN()","selector":"0x2a0acc6a"} -->
### `ADMIN()`

Immutable admin getter; differential and artifact evidence owner: AC7/AC8.

<!-- LIDO-CIRCUIT-BREAKER-ENDPOINT {"signature":"MIN_PAUSE_DURATION()","selector":"0x76c810b5"} -->
### `MIN_PAUSE_DURATION()`

Immutable minimum-pause getter; evidence owner: AC7/AC8.

<!-- LIDO-CIRCUIT-BREAKER-ENDPOINT {"signature":"MAX_PAUSE_DURATION()","selector":"0x2799657d"} -->
### `MAX_PAUSE_DURATION()`

Immutable maximum-pause getter; evidence owner: AC7/AC8.

<!-- LIDO-CIRCUIT-BREAKER-ENDPOINT {"signature":"MIN_HEARTBEAT_INTERVAL()","selector":"0x8dd54ee7"} -->
### `MIN_HEARTBEAT_INTERVAL()`

Immutable minimum-heartbeat getter; evidence owner: AC7/AC8.

<!-- LIDO-CIRCUIT-BREAKER-ENDPOINT {"signature":"MAX_HEARTBEAT_INTERVAL()","selector":"0x879f32f6"} -->
### `MAX_HEARTBEAT_INTERVAL()`

Immutable maximum-heartbeat getter; evidence owner: AC7/AC8.

<!-- LIDO-CIRCUIT-BREAKER-ENDPOINT {"signature":"pauseDuration()","selector":"0x0526679c"} -->
### `pauseDuration()`

Returns the configured pause duration through the declared logical projection.

<!-- LIDO-CIRCUIT-BREAKER-ENDPOINT {"signature":"heartbeatInterval()","selector":"0x561a4fac"} -->
### `heartbeatInterval()`

Returns the configured heartbeat interval through the declared logical projection.

<!-- LIDO-CIRCUIT-BREAKER-ENDPOINT {"signature":"heartbeatExpiry(address)","selector":"0xc427909e"} -->
### `heartbeatExpiry(address)`

Returns the address's expiry; dirty-address and short-head behavior is evidence-owned.

<!-- LIDO-CIRCUIT-BREAKER-ENDPOINT {"signature":"getPauser(address)","selector":"0x5280237a"} -->
### `getPauser(address)`

Returns the Registry assignment relation, not Blanc's raw storage representation.

<!-- LIDO-CIRCUIT-BREAKER-ENDPOINT {"signature":"getPausableCount(address)","selector":"0x8cd80ba0"} -->
### `getPausableCount(address)`

Returns the projected per-pauser count.

<!-- LIDO-CIRCUIT-BREAKER-ENDPOINT {"signature":"getPausables()","selector":"0x54720ecd"} -->
### `getPausables()`

Returns the ordered projected Registry enumeration; arbitrary-length proof is excluded.

<!-- LIDO-CIRCUIT-BREAKER-ENDPOINT {"signature":"isPauserLive(address)","selector":"0xd10ea321"} -->
### `isPauserLive(address)`

Uses the source's strict temporal boundary: equality with expiry is not live.

<!-- LIDO-CIRCUIT-BREAKER-ENDPOINT {"signature":"setPauseDuration(uint256)","selector":"0xc9387332"} -->
### `setPauseDuration(uint256)`

Admin-only inclusive bound validation, exact error/event behavior, and state update.

<!-- LIDO-CIRCUIT-BREAKER-ENDPOINT {"signature":"setHeartbeatInterval(uint256)","selector":"0x71a99c22"} -->
### `setHeartbeatInterval(uint256)`

Admin-only inclusive bound validation, exact error/event behavior, and state update.

<!-- LIDO-CIRCUIT-BREAKER-ENDPOINT {"signature":"registerPauser(address,address)","selector":"0x338d93fc"} -->
### `registerPauser(address,address)`

Admin Registry mutation: register, replace, unregister, idempotence, and swap-and-pop histories.

<!-- LIDO-CIRCUIT-BREAKER-ENDPOINT {"signature":"heartbeat()","selector":"0x3defb962"} -->
### `heartbeat()`

Registered/live checks, checked expiry arithmetic, exact error precedence, event, and update.

<!-- LIDO-CIRCUIT-BREAKER-ENDPOINT {"signature":"pause(address)","selector":"0x76a67a51"} -->
### `pause(address)`

Transient lock, target-code guard, external `pauseFor(uint256)` call, result handling,
pause observation, event order, rollback, and lock release are compared as declared channels.

## Constructor

<!-- LIDO-CIRCUIT-BREAKER-CONSTRUCTOR {"arguments":["address","uint256","uint256","uint256","uint256","uint256","uint256"]} -->

The seven arguments are admin, minimum/maximum pause duration,
minimum/maximum heartbeat interval, initial pause duration, and initial heartbeat
interval.  It rejects malformed/noncanonical inputs, nonzero creation value, zero
admin, and invalid bounds in source order; it performs two configuration writes
and emits `CircuitBreakerInitialized`, `PauseDurationUpdated`, then
`HeartbeatIntervalUpdated`. Constructor evidence is finite execution evidence,
not a Jaune deployment theorem.

## Cross-cutting boundary

<!-- LIDO-CIRCUIT-BREAKER-CROSSCUT dispatch-nonpayability -->
### dispatch-nonpayability

Unknown/empty calldata, selector-matched short heads, trailing calldata, and
nonzero runtime value are explicit comparison cases; no fallback behavior is inferred.

<!-- LIDO-CIRCUIT-BREAKER-CROSSCUT registry-histories -->
### registry-histories

Registry agreement covers zero/fresh/same/distinct targets, first/middle/last/only
removal, moved-element follow-up, and one-pauser/many-target histories in finite rows.

<!-- LIDO-CIRCUIT-BREAKER-CROSSCUT temporal-arithmetic -->
### temporal-arithmetic

Expiry uses strict liveness and checked addition. Boundary `-1`, `=`, `+1`,
interval changes, and overflow/error precedence are evidence-owned.

<!-- LIDO-CIRCUIT-BREAKER-CROSSCUT errors-events-order -->
### errors-events-order

All 15 custom-error families, Solidity overflow panic where applicable, six event
families, indexed/data words, and ordering are lock and differential obligations.

<!-- LIDO-CIRCUIT-BREAKER-CROSSCUT external-return-allocation -->
### external-return-allocation

`pauseFor` and `isPaused` call shape, complete successful-returndata allocation/copy,
Boolean decoding, bubbling, and adequate-gas scaling are compared; first-word-only
shortcuts are outside the allowed implementation freedom.

<!-- LIDO-CIRCUIT-BREAKER-CROSSCUT reentry-interference -->
### reentry-interference

Finite hostile callback rows cover same/different target and caught/bubbled cases.
They are not an arbitrary-descendant reentry theorem.

<!-- LIDO-CIRCUIT-BREAKER-CROSSCUT rollback -->
### rollback

Status, post-state projection, logs, and retained call traces are compared across
outer rollback; a successful parent may catch a failed child.

<!-- LIDO-CIRCUIT-BREAKER-CROSSCUT logical-state-projection -->
### logical-state-projection

Comparison is over the frozen logical CircuitBreaker state, never equality of the
two implementations' raw storage slots.

<!-- LIDO-CIRCUIT-BREAKER-CROSSCUT oracle-independence -->
### oracle-independence

The Solidity side is the pinned source/compiler artifact and the Blanc side is an
evaluator-derived Blanc artifact. Neither supplies the other's expected values.

<!-- LIDO-CIRCUIT-BREAKER-CROSSCUT finite-evidence -->
### finite-evidence

Differential agreement is only for manifest-listed worlds/channels. It is not
universal functional correctness, deployed-bytecode verification, Registry proof,
enumeration proof, hostile-world theorem, or deployment/history theorem.
