# WETH10 deviation and drift registry

This registry classifies differences against the deployed WETH10 target locked
by `scripts/weth10-reference.json`. The normative source is the deployment
input at parent source revision `4e7ed4085c07be94452cf64390fee36bd4d4e46e`;
the installed 9,975-byte runtime is the oracle/provenance anchor. Repository
`main` at `87ec30256dab62459a2e6d2a1741b44d345881f1` is drift evidence, not a
replacement target.

## True behavioral deviations

None are accepted. No in-scope mismatch is currently known from the finite
differential suite; agreement on its chosen inputs is evidence, not a proof
that no mismatch exists. Blanc WETH10 must match every in-scope ordinary-call
behavior in `WETH10_COMPATIBILITY.md`. A future mismatch in that surface is a
defect or a new explicit conformance decision; it may not be silently moved
into this section.

## Accepted low-level implementation differences

These are freedoms, not behavioral deviations:

- Blanc program structure, control flow, instruction selection, source
  organization, optimizer route, runtime length, and runtime bytes;
- raw storage slots, storage proofs/roots, and the tagged-key implementation
  used to project logical state;
- code and codehash identity;
- exact gas consumption, access-list warming, and callback-observed
  `gasleft()`, subject to the adequate-gas boundary;
- initcode bytes, deployment gas, CREATE2 address, and the mechanism by which
  deployment parameters are embedded in the Blanc runtime; and
- cheaper or more proof-reliable internal implementation when endpoint
  outcomes, returndata, logical state/ETH, calls, logs, guard precedence, and
  reentrancy snapshots remain compatible.

Blanc proves its own program-to-compiled-runtime equality. It does not prove or
reproduce the deployed Solidity runtime bytes.

## Explicit equivalence exclusions

The compatibility claim deliberately excludes:

- exact behavior for malformed or noncanonical **input** calldata, including
  dirty address words, truncated dynamic tails, pathological offsets, and
  other Solidity decoder edge cases;
- delegatecall-as-library use;
- raw storage equality, storage roots/proofs, code/codehash identity, source
  shape, and bytecode identity;
- exact gas, access lists, or equality of callback-observed `gasleft()`;
- liveness under inadequate gas and deployed-vs-Blanc liveness/gas parity. The
  Blanc-only `TH-redeem` result instead uses a named conservative Prague bound;
- guarantees that arbitrary hostile callback code returns successfully,
  permits withdrawal, or establishes another useful postcondition. The
  Blanc-only constructive redemption theorem is deliberately narrower:
  canonical `withdraw`/`withdrawTo`, `Stable`, and a nonzero code-free
  Prague-nonprecompile recipient under an explicit fresh execution envelope.
  The present verification program also makes no no-borrower-premise gas-
  settlement theorem for arbitrary receiver code; no such theorem is claimed;
- source-initcode, CREATE2-address, and deployment-gas equality; and
- adversarial cryptographic-collision states for the projected Blanc allowance
  map, under the qualification below.

These exclusions do not permit an unknown nonempty selector to act as receive,
do not relax recognized-selector nonpayability, and do not exclude malformed
**callback return** decoding or child-revert behavior.

## Allowance-key collision qualification

Solidity stores allowances under a full mapping hash. Blanc uses the `10`
high-bit tag plus the low 254 bits of `keccak256(owner-word ∥ spender-word)`.
That structural tag makes allowance keys disjoint from balances, nonces, and
`flashMinted`, but two distinct allowance pairs can collide after projection.

Allowance equivalence is therefore stated for the finite ordered pairs touched
or queried by the compared trace, with the local premise that distinct
observed pairs have distinct Blanc allowance keys. No proof may assume global
keccak injectivity or total allowance-key injectivity. This is a scoped
collision qualification, not an ordinary-state behavioral deviation.

## Current-main drift

The vendored exact diff from deployed input to observed repository `main`
contains one material behavior change:

- deployed `transfer` and `transferFrom` take the transfer branch for every
  nonzero `to`, including `to == address(this)`;
- current `main` changes those two tests to
  `to != address(0) && to != address(this)`, so a self-contract recipient is
  sent down the withdrawal branch instead; and
- deployed behavior wins. Blanc must treat `address(this)` as an ordinary
  nonzero recipient for those endpoints. `transferAndCall` was not changed by
  this drift and likewise uses the deployed nonzero-recipient branch.

The remaining observed diff is nonbehavioral: a vendored import path change,
whitespace cleanup, comment punctuation, and comment trailing-space cleanup.
The often-cited revision `34d2712876138fb3d5f769a3965f4e330bc91169`
is a sibling of the deployment commit, not its parent; its exact vendored diff
changes only two comment periods. It is behavior-equivalent corroboration, not
the literal deployed-source revision.

## Deployed quirks intentionally matched

These are sometimes surprising, but they belong to the target and are **not**
deviations.

### Transfers, withdrawals, and reason spelling

- `transfer`, `transferFrom`, and `transferAndCall` interpret `to == 0` as a
  withdrawal. The nonzero branch uses `WETH: transfer amount exceeds balance`;
  the zero branch uses `WETH: burn amount exceeds balance`.
- `transfer(to = 0)` and `transferAndCall(to = 0)` send ETH to `msg.sender`.
  `transferFrom(from, to = 0, value)` also sends ETH to `msg.sender`, not
  `from` and not `to`.
- `withdraw` and `withdrawTo` replace a failed ETH call with exact
  `WETH: ETH transfer failed`. `withdrawFrom` uniquely uses exact
  `WETH: Ether transfer failed`. `transfer`, `transferFrom`, and
  `transferAndCall` zero-recipient branches use the `ETH` spelling.
- These low-level ETH-call sites replace child revert bytes with their own
  reason rather than bubbling them. Storage changes and preceding logs roll
  back if the call fails.
- `withdrawTo(to = 0, value)` can succeed because a value-bearing low-level
  call to the zero address is allowed. This differs from typed token callback
  calls to a zero/codeless target.
- A transfer to `address(this)` is an ordinary deployed transfer. A same-key
  debit/credit restores the balance but still emits `Transfer`.

### ERC-677-style callbacks and codeless targets

- `depositToAndCall`, `approveAndCall`, and `transferAndCall` use the deployed
  Solidity-0.7 truthiness decoder. A full zero word returns canonical `false`;
  every full nonzero word, including noncanonical ABI words such as `2`,
  returns canonical `true`. Both outcomes are successful outer calls.
- State writes and the WETH10 log occur before each callback, so the callback
  observes them. Child reverts bubble exactly. A zero/codeless target or return
  shorter than 32 bytes empty-reverts and rolls the preceding state/log/ETH
  effects back.
- `depositTo(to = 0)` succeeds and mints to the zero mapping key because it has
  no callback. `depositToAndCall(to = 0)` transiently mints and logs, then its
  typed call to zero empty-reverts everything.
- `approve(spender = 0)` succeeds. `approveAndCall(spender = 0)` transiently
  approves/logs, then empty-reverts on the typed callback.
- `transferAndCall(to = 0)` first follows the withdrawal path and sends ETH to
  the caller; only then does it attempt the typed callback to zero. That final
  empty revert rolls the withdrawal and any recipient callback effects back.

### Allowance short circuits

- `transferFrom` and `withdrawFrom` bypass allowance entirely when
  `from == msg.sender`.
- Otherwise, max-uint256 allowance is infinite: no decrement, storage write,
  or `Approval` log occurs. Finite allowance is checked/decremented and its
  `Approval` precedes the balance guard and transfer/burn log; a later failure
  rolls it back.
- Flash-loan repayment has no from-is-caller bypass. It reads
  `allowance[receiver][address(this)]` after the callback; max allowance is
  infinite, while a finite allowance is checked/decremented and logged.

### Permit deadline, nonce, and fork behavior

- Deadline equality succeeds: only `block.timestamp > deadline` yields exact
  `WETH: Expired permit` (capital `E`). This guard wins before nonce/digest work.
- The current nonce is included in the struct hash and post-incremented before
  `ecrecover`. An invalid signature then yields exact `WETH: invalid permit`,
  and transaction rollback restores the old nonce.
- The recovered signer must be nonzero and equal owner. On success the nonce
  advances once, the allowance is overwritten, and one `Approval` is emitted.
- On the deployment chain the cached separator is used. After a chain-ID
  change, both `DOMAIN_SEPARATOR` and `permit` recompute from the current chain
  ID and `address(this)`, so pre-fork signatures do not silently retain the old
  domain. Address-correspondence comparison follows the three valid worlds in
  the compatibility contract; transplanting literal mainnet runtime to a new
  address on chain ID 1 is invalid.

### Flash-loan trace and callback behavior

- Guard precedence is token identity, individual `uint112` cap, temporary
  unchecked `flashMinted` increment, total cap, mint/credit, callback result,
  post-callback allowance, post-callback balance, burn, then `flashMinted`
  decrement.
- The callback receives `(initiator = msg.sender, token = address(this),
  amount = value, fee = 0, data)` and observes the temporary unbacked state.
- A child revert bubbles. No-code or malformed bytes32 return decoding
  empty-reverts. A successfully decoded wrong magic word is instead replaced
  by exact `WETH: flash loan failed`.
- The outer WETH10-owned trace is mint `Transfer`, arbitrary callback logs,
  optional finite-allowance `Approval`, then burn `Transfer`: two or three
  direct outer-frame WETH10 logs, **not four**. Reentrant WETH10 calls may add
  their own actually interleaved logs; they are not counted as outer emissions.

### Arithmetic, ETH, and dispatch

- Balance credits, nonce increment, `flashMinted` updates, `totalSupply`, and
  the same-key balance operations use Solidity 0.7.6 unchecked arithmetic.
  The compatibility contract does not add no-overflow guards.
- `totalSupply` is contract ETH balance plus `flashMinted`, not booked-balance
  sum. Force-sent ETH creates backing surplus without minting.
- Only receive and the three deposit functions are payable. Empty calldata
  selects receive; a nonempty unknown selector empty-reverts rather than
  depositing.
- STATICCALL failures preserve actual guard precedence before the first
  forbidden write/log/value call; mutators do not share one normalized revert.
