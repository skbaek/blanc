# Patch plan: strict block import, trustworthy fixtures, and lifecycle fixes

This is a self-contained implementation plan for `/Users/bsk/elevm`, with
`/Users/bsk/blanc` treated as the downstream proof client that must remain
green throughout. It follows the style and discipline of `~/REFACTOR.md` and
`~/CLEANUP.md`: one sequential, agent-session-sized step at a time; one commit
per touched repository per step; explicit verification gates; no long blind
arcs.

The starting point assumed by this plan already contains the fixes for
`review.md` findings 3.1, 3.2, 3.4, 3.5, and 3.7. Finding 3.3 (point-evaluation
and BLS12-381 precompiles) is deliberately deferred. This plan closes 3.6,
3.8, and 3.9 and also fixes two additional defects exposed by the ten-file
failure cluster:

- the block-prestate is incorrectly reused as `SSTORE`'s original state for
  every transaction in a block;
- the fixture runner treats every block as extending one linear chain, so it
  cannot import competing branches.

Completing all **12 steps** should make the original ten `FAIL` files pass and
should make `CALLBlake2f_MaxRounds.json` substantially faster, ideally changing
it from `TIMEOUT` to `PASS`. Tightening expected-exception checking is allowed
to expose new genuine failures; those are evidence gained, not regressions to
hide.

## Scope and target files

The historical full baseline contains 2,970 `PASS`, 10 `FAIL`, and 3
`TIMEOUT` files. The ten original failures are:

1. `InvalidBlocks/bc4895-withdrawals/shanghaiWithoutWithdrawalsRLP.json`
2. `InvalidBlocks/bc4895-withdrawals/withdrawalsIndexBounds.json`
3. `InvalidBlocks/bc4895-withdrawals/withdrawalsValidatorIndexBounds.json`
4. `InvalidBlocks/bcInvalidHeaderTest/GasLimitHigherThan2p63m1.json`
5. `InvalidBlocks/bcMultiChainTest/UncleFromSideChain.json`
6. `ValidBlocks/bcStateTests/blockhashNonConstArg.json`
7. `ValidBlocks/bcStateTests/blockhashTests.json`
8. `ValidBlocks/bcStateTests/extcodehashEmptySuicide.json`
9. `ValidBlocks/bcStateTests/refundReset.json`
10. `ValidBlocks/bcValidBlockTest/eip2930.json`

The performance target is:

- `GeneralStateTests/stTimeConsuming/CALLBlake2f_MaxRounds.json`

The two BLOCKHASH files should already be green at the start because finding
3.5 has been fixed. They remain in the target set as regression protection.

## Design decisions fixed by this plan

### Strict decoding happens before conversion

RLP bytes are untrusted consensus input. Fixed-width fields must have exactly
the required length; bounded integers must be checked for width and canonical
integer encoding before conversion; optional contract-creation addresses must
be either empty or exactly 20 bytes. The encode-and-compare round trip remains
a final defense, but it must no longer be the first place that detects a value
which was already truncated.

### Fixture exceptions are exact and fail closed

The fixture's `expectException` is a `|`-separated set of allowed official
exception identities. The runner parses that set, classifies the actual error
as one canonical identity, and accepts only set membership. Unknown expected
identities, unknown actual errors, and broad categories such as merely
`InvalidBlock` are failures. Details may follow a canonical identity after a
fixed delimiter, but substring matching is forbidden.

At plan-writing time the Prague fixtures contain 296 expected-invalid blocks,
38 distinct expectation strings, and 35 individual exception identities.
Step 4 records that vocabulary in code and tests it exhaustively.

### Block import is parent-hash based, not list-order based

The runner keeps immutable `BlockChain` snapshots indexed by tip hash. A
decoded block is evaluated against the snapshot named by its `parentHash`.
Successful blocks add snapshots; rejected blocks do not. This models forks
without special cases for fixture `chainname`, fixes `UncleFromSideChain`, and
lets the final `lastblockhash` select the exact state whose root must be
checked.

### Original storage state is transaction-scoped

`BenvStat.origState` may remain in its current structure for proof stability,
but every normal or system transaction must reset it to that transaction's
input state before any execution or authorization processing. It must not be
initialized once per block and then silently carried through later
transactions.

## Rules for every step

1. Read the applicable `AGENTS.md` and the `lean-inspector` / `lean-prover`
   skills before touching Lean source. Use `lean-lsp-mcp` diagnostics during
   edits. Do not run a build merely to discover a proof state; builds are
   end-of-step gates.
2. Inspect current definitions and references before editing. Line numbers and
   counts below are plan-writing-time observations and may drift.
3. One step is one reviewable commit per touched repository, created by the
   user after review. Do not include unrelated working-tree changes. In
   particular, commit or otherwise isolate the already-completed 3.7 changes
   before Step 1.
4. Never add `sorry`, axioms, `ofReduce*`, intentionally invalid syntax, or a
   permissive fallback that converts an unknown fixture error into success.
5. Keep `/Users/bsk/blanc` building with unchanged statements for
   `weth_inv_solvent`, `stateTransition_inv_solvent`, `chain_inv_solvent`, and
   `addBlockToChain_inv_solvent`. If an elevm definition used by a proof must
   change, repair the proof in the same step.
6. Do not change the public type or success shape of `addBlockToChain` merely
   to simplify `Main.lean`; `Blanc/Solvent.lean` depends on it. The fixture
   runner must handle both the outer `Except.error` decoder channel and the
   inner `.ok (.inr err)` transition channel explicitly.
7. Preserve `scripts/baseline-full.txt` as the pre-strict historical baseline
   until Step 12. Never rebase away a classification change during Steps
   1–11.
8. A new failure under the strict oracle may be genuine. First rule out a bad
   exception mapping or runner bug. If it is a real implementation gap outside
   this plan, document it precisely; do not broaden the matcher to make it
   pass.
9. Every expected-invalid block must leave its parent snapshot unchanged and
   processing must continue to later blocks. Never return early and thereby
   skip the file's final hash and state-root checks.
10. Keep each step within its stated scope. If reality makes a step larger
    than one session, stop at a green boundary and propose a subdivision.

## Verification gates

- **V0** — `lake build elevm` in `/Users/bsk/elevm`, then `lake build` and the
  existing axiom audit in `/Users/bsk/blanc`.
- **PATCH** — the Step 1 target tier: the ten historical failures plus the
  Blake2F max-round fixture. Its final contract is all 11 files `PASS`.
  During early steps it is an intentionally red progress meter; a step report
  must list every classification.
- **RLP4** — the four directly relevant invalid-RLP/header files: the missing
  withdrawals list, both withdrawal-index overflows, and the `2^63` gas-limit
  case.
- **INVALID-AUDIT** — every Prague file under `InvalidBlocks`, with actual and
  expected canonical identities printed for any mismatch. After strict mode
  lands this is an audit, not an instruction to hide newly exposed defects.
- **SMOKE** — `elevm/scripts/check.sh --smoke`, compared with its historical
  baseline and accompanied by an explanation for every classification change.
- **PERF** — run `CALLBlake2f_MaxRounds.json` with the same 100-second limit
  used by the current harness, record elapsed wall time, and confirm that no
  per-round trace output is emitted.
- **FULL** — the overnight full run, scheduled only in Step 12. Compare with
  the preserved historical baseline before accepting a new strict baseline.

---

## Step 1 — Add a focused red-to-green patch gate

### Agent prompt

Work in `/Users/bsk/elevm/scripts`; do not change Lean semantics. Extend the
existing fixture harness with a `--patch` tier backed by a committed
`scripts/patch-tests.txt`. The list contains exactly the ten historical FAIL
paths and `GeneralStateTests/stTimeConsuming/CALLBlake2f_MaxRounds.json`.

Unlike the regression-baseline tiers, `--patch` is a target gate: it succeeds
only when every listed file is `PASS`. It writes
`scripts/report-patch.txt` (gitignored), prints per-file elapsed time as well
as `PASS`/`FAIL`/`TIMEOUT`, uses the existing one-process-per-file isolation,
and ends with one unambiguous verdict. Do not add `--rebase` behavior for this
tier; its desired result is fixed. Keep the existing depth, smoke, full, and
directory behavior unchanged.

Also add an `RLP4` convenience list or documented command containing the four
files named by the RLP4 gate. Do not duplicate runner logic in a second shell
script. Preserve `baseline-full.txt` byte-for-byte and record its checksum in
the Step 1 report so later work cannot silently rebase it.

Build the current executable once, run `--patch`, and capture the starting
matrix. The already-fixed BLOCKHASH pair should now pass; if either does not,
stop and report that the assumed starting point is false. The remaining red
entries are expected in this infrastructure step. Run the existing depth and
smoke gates once to prove the harness extension did not change them. Report
all 11 classifications and timings. [V0 infrastructure portion + PATCH
observation]

### Note for the reader

This is the progress meter for the whole arc. It is intentionally red after
Step 1, but it has a fixed green end condition and cannot be rebased to accept
failures. The historical full baseline remains the regression reference.

---

## Step 2 — Fix both executable-performance defects

### Agent prompt

Work in `/Users/bsk/elevm/Elevm/Execution.lean`. Fix only finding 3.9.

First, replace the `Hashable (Adr × B256)` implementation that hashes only the
address. Use Lean's standard hash-combination facility (inspect and verify the
actual available declaration; do not invent an API) and mix the address with
all four 64-bit limbs of the storage key. Keep equality unchanged. Add a small
deterministic regression check showing that several distinct keys at one
address do not all receive the same hash and that a `KeySet` containing many
same-address keys still finds each key.

Second, change Blake2F to use the existing non-tracing iterator rather than
`iterRangeTrace`. Search for all references to `traceId` and
`iterRangeTrace`; if they become unreferenced, delete them. There must be no
`dbg_trace` on the Blake2F round path. Do not alter the compression function,
round count, gas calculation, input validation, or output bytes.

Run diagnostics after the edit, then V0. Run PERF and the full PATCH tier.
The Blake2F file should pass within 100 seconds; record before/after elapsed
times and its classification. The other ten PATCH classifications must not
regress. Report the chosen hash formula and the deletion/reference audit for
the tracing helpers. [V0 + PERF + PATCH]

### Note for the reader

The Blake change should be a dramatic speedup because it removes one trace
event per compression round. The hash fix may not change a fixture
classification immediately; its success signs are key-sensitive hashes and
the disappearance of the same-address collision bucket.

---

## Step 3 — Reset `origState` at every transaction boundary

### Agent prompt

Work in `/Users/bsk/elevm/Elevm/Execution.lean` and repair downstream blanc
proofs only if required. The current `initBenvStat` stores `chain.state` in
`origState` once per block, while `applyTransactions` updates only
`benv.state`. As a result, later transactions calculate `SSTORE` gas and
refunds relative to the block prestate.

Introduce one clearly named helper such as `Benv.beginTransaction` whose
semantic effect is to preserve the current environment while setting
`stat.origState := benv.state`. Call it at the start of every normal
transaction, before validation, EIP-7702 authorization processing, or message
execution. Audit the system-transaction path as well: beacon roots, history
storage, withdrawal requests, and consolidation requests each need their own
input state as the original state. Apply the same helper at the common system
transaction boundary rather than at individual call sites.

Do not move `origState` to a different structure in this step; that would
create unnecessary proof churn. Add a focused regression that executes two
transactions changing the same nonzero slot and demonstrates that the second
transaction uses its own input value as the original value.

Run V0 and PATCH. The expected signatures are:

- `extcodehashEmptySuicide`: the prior 2,800-gas deficit disappears;
- `eip2930`: the prior 10,080-gas deficit disappears;
- `refundReset`: the prior large refund/gas-used deficit disappears.

All three must become `PASS`. If gas used matches but a later root check fails,
continue debugging within this step rather than declaring partial success.
Report the exact normal and system transaction boundaries audited. [V0 +
PATCH]

### Note for the reader

The strongest quick check is `extcodehashEmptySuicide`: 2,800 gas is exactly
the difference between a clean nonzero storage update and the incorrectly
assumed dirty update in this case. The other two fixtures exercise the same
lifetime error through larger sequences.

---

## Step 4 — Add a canonical fixture-exception vocabulary

### Agent prompt

Add a small fixture-specific module in `/Users/bsk/elevm` (for example
`Elevm/FixtureException.lean`) and import it from `Main.lean`. This step is
additive: do not change which fixtures pass yet.

Define a finite canonical type with one constructor for every individual
exception identity present in the selected Prague corpus. Generate the
inventory from the fixture JSON before coding and compare it with the
plan-writing-time count: 296 expected-invalid blocks, 38 distinct expectation
strings, 35 individual identities. The identities span the `BlockException`
and `TransactionException` namespaces, including the three RLP identities.
If the corpus has drifted, report the new inventory and include every observed
identity rather than hard-coding the old count.

The plan-writing-time identities are listed here so the task has a checkable
target (re-generate rather than trusting the list blindly):

```text
BlockException.EXTRA_DATA_TOO_BIG
BlockException.GASLIMIT_TOO_BIG
BlockException.GAS_USED_OVERFLOW
BlockException.IMPORT_IMPOSSIBLE_DIFFICULTY_OVER_PARIS
BlockException.IMPORT_IMPOSSIBLE_UNCLES_OVER_PARIS
BlockException.INVALID_BASEFEE_PER_GAS
BlockException.INVALID_BLOCK_NUMBER
BlockException.INVALID_BLOCK_TIMESTAMP_OLDER_THAN_PARENT
BlockException.INVALID_GASLIMIT
BlockException.INVALID_GAS_USED
BlockException.INVALID_LOG_BLOOM
BlockException.INVALID_RECEIPTS_ROOT
BlockException.INVALID_STATE_ROOT
BlockException.INVALID_TRANSACTIONS_ROOT
BlockException.INVALID_WITHDRAWALS_ROOT
BlockException.RLP_INVALID_FIELD_OVERFLOW_64
BlockException.RLP_STRUCTURES_ENCODING
BlockException.RLP_WITHDRAWALS_NOT_READ
BlockException.UNKNOWN_PARENT
BlockException.UNKNOWN_PARENT_ZERO
TransactionException.GASLIMIT_PRICE_PRODUCT_OVERFLOW
TransactionException.GAS_ALLOWANCE_EXCEEDED
TransactionException.INITCODE_SIZE_EXCEEDED
TransactionException.INSUFFICIENT_ACCOUNT_FUNDS
TransactionException.INSUFFICIENT_MAX_FEE_PER_GAS
TransactionException.INTRINSIC_GAS_TOO_LOW
TransactionException.NONCE_IS_MAX
TransactionException.NONCE_MISMATCH_TOO_HIGH
TransactionException.NONCE_MISMATCH_TOO_LOW
TransactionException.PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS
TransactionException.SENDER_NOT_EOA
TransactionException.TYPE_3_TX_BLOB_COUNT_EXCEEDED
TransactionException.TYPE_3_TX_CONTRACT_CREATION
TransactionException.TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH
TransactionException.TYPE_3_TX_ZERO_BLOBS
```

Provide and test:

1. canonical `toString` and exact `ofString` round trips;
2. parsing of a `|`-separated fixture expectation into a nonempty set;
3. rejection of empty tokens, unknown tokens, whitespace variants, and
   duplicate-delimiter accidents;
4. an actual-error classifier API which currently recognizes only explicitly
   registered exact messages or prefixes ending at the fixed `" : "`
   delimiter;
5. `matches expected actual`, which succeeds only when one parsed expected
   identity equals the one classified actual identity.

Do not implement `contains`, suffix matching, a generic `InvalidBlock`
fallback, or “any RLP error is good enough.” Add table-driven checks covering
all 35 `toString`/`ofString` cases, every composite expectation string in the
fixture inventory, and negative unknown-error cases. Keep the old oracle
wired for now. Run V0 and PATCH; classifications should be unchanged. Report
the generated vocabulary and test counts. [V0 + PATCH unchanged]

### Note for the reader

This creates the fail-closed language used by the later decoder and runner
steps. It is intentionally not yet authoritative; wiring an incomplete table
would turn diagnostic work into a large blind failure set.

---

## Step 5 — Introduce strict bounded-scalar and exact-width decoders

### Agent prompt

Work in `/Users/bsk/elevm/Elevm/Types.lean` and
`/Users/bsk/elevm/Elevm/Execution.lean`. Add small reusable helpers for
consensus-field decoding; do not yet rewrite every header and transaction
decoder.

The helpers must distinguish these shapes:

- fixed bytes: length must equal `n` exactly;
- unsigned scalar: length must be at most `n`, zero is encoded as the empty
  byte string, and a nonempty scalar must not begin with zero;
- 64-bit scalar: the unsigned-scalar rule with at most 8 bytes, converted
  without truncation;
- 256-bit scalar: the unsigned-scalar rule with at most 32 bytes, converted
  without truncation;
- address: exactly 20 bytes;
- optional creation receiver: either empty or exactly 20 bytes.

Fix `B8L.toAdr?` itself so that a 21-byte or longer list is rejected rather
than the first 20 bytes being accepted and the tail ignored. Audit every
call site in both repos before making the global change; confirm address
derivation and delegation call sites already provide exactly 20 bytes.

Decoder errors must carry a precise internal reason which Step 4 can map to a
canonical RLP identity. Do not use a generic error for both width overflow and
wrong list structure. Add boundary checks for 0, 1, `n`, and `n+1` bytes,
leading-zero rejection, exact 20-byte acceptance, and 19/21-byte address
rejection. Run V0 and PATCH; no target classification should regress. Report
all audited `toAdr?` callers. [V0 + PATCH]

### Note for the reader

`B8L.toB64?` currently requires exactly eight bytes and therefore is not the
right RLP scalar decoder; valid small integers use fewer bytes. The new helper
must check “at most eight, canonical, then convert,” not reuse an unsuitable
exact-width function.

---

## Step 6 — Make header decoding and validation strict

### Agent prompt

Work in the header decoder, `checkGasLimit`, `validateHeader`, and
`stateTransitionChecks` in `/Users/bsk/elevm/Elevm/Execution.lean`. Apply the
Step 5 helpers to every Prague header field and write down a field table in the
step report: field name, fixed/scalar shape, width, semantic validation, and
canonical exception identity.

At minimum enforce exact lengths for all 32-byte roots/hashes, the 20-byte
coinbase, 256-byte bloom, and 8-byte nonce; canonical bounded integers for
number, gas fields, timestamp, difficulty, base fee, and blob-gas fields; and
the existing 32-byte limit on extra data. Preserve the optional requests-hash
shape but require exactly 32 bytes when present.

Split gas-limit failure identities correctly:

- `gasLimit >= 2^63` is `BlockException.GASLIMIT_TOO_BIG`;
- failure of the parent-relative adjustment or minimum is
  `BlockException.INVALID_GASLIMIT`.

Give every header and post-transition check an unambiguous actual error which
Step 4 maps to its exact official identity: timestamp, block number, base fee,
difficulty after Paris, gas used, extra data, parent, state root, transaction
root, receipt root, bloom, and withdrawals root. Eliminate bare
`"InvalidBlock"` at these sites. Distinguish zero unknown parent from a
nonzero unknown parent where the fixture vocabulary does.

Run V0, PATCH, and the header-related portion of INVALID-AUDIT. The
`GasLimitHigherThan2p63m1` implementation must now reject for the absolute
bound, although the old runner may still report the file as FAIL until Step
11 routes and compares the exception. Report the observed actual identity,
not just that some rejection occurred. [V0 + PATCH observation +
INVALID-AUDIT]

### Note for the reader

This step separates consensus rejection from fixture plumbing. A successful
implementation can still look red under the old oracle; the important sign is
that the block is rejected at the header check with `GASLIMIT_TOO_BIG`, not by
a later unrelated mismatch.

---

## Step 7 — Make block, withdrawal, and legacy-transaction RLP strict

### Agent prompt

Work in `BLT.toExStrWithdrawal`, legacy `BLT.toExStrTx`,
`BLT.toExStrBlock`, `rlpToBlock`, and the RLP round-trip check.

For withdrawals, decode both indexes as canonical at-most-8-byte scalars,
require an exact 20-byte recipient, and decode amount as a canonical
at-most-32-byte scalar. The two 9-byte index cases must fail before
construction of `Withdrawal`; no `.toB64` call may see unchecked bytes.

For legacy transactions, enforce canonical bounded decoding for nonce, gas
price, gas, value, `v`, `r`, and `s`; accept receiver only as empty or exactly
20 bytes. Reject oversized signature fields before sender recovery. Preserve
valid legacy signing and encoding behavior.

For blocks, distinguish at least:

- an RLP item that is not the expected block list structure;
- a post-Shanghai/Prague block list which omits the withdrawals list;
- a field whose integer width exceeds 64 bits;
- a canonical decode which nevertheless fails the final byte-for-byte
  re-encoding check.

Map these to the exact Step 4 RLP identities. Keep the round-trip comparison as
a final invariant, but it must not be the mechanism which discovers a
truncated withdrawal or transaction field.

Run V0, PATCH, and RLP4. Inspect actual errors directly even though Step 11 has
not yet replaced the oracle. The missing-withdrawals file and both withdrawal
overflow files must reach the expected canonical identities. Report grep
evidence that unchecked `.toB64` conversion is gone from these decoder paths.
[V0 + PATCH observation + RLP4]

### Note for the reader

Before this step, the withdrawal overflow is truncated, reconstructed, and
only then rejected as a generic RLP mismatch. Afterward it is rejected at the
field boundary for the right reason.

---

## Step 8 — Make typed transactions, access lists, and authorizations strict

### Agent prompt

Work in `BLT.toAccessItem`, `BLT.toAccessList`, `BLT.toAuth`, and
`B8L.toExStrTx` for types `0x01` through `0x04`. Apply the Step 5 helpers to
every untrusted field before conversion.

Requirements:

- nonce and every modelled 64-bit field reject more than 8 bytes rather than
  truncating;
- `r` and `s` reject more than 32 bytes; delete the
  `reverse.takeD 32` truncation pattern;
- access-list addresses are exactly 20 bytes and storage keys exactly 32;
- blob versioned hashes are exactly 32 bytes;
- type-1/type-2 receivers are empty or exactly 20 bytes;
- type-3/type-4 receivers are exactly 20 bytes, with the existing semantic
  contract-creation rejection retained as defense in depth;
- authorization addresses are exactly 20 bytes, authorization nonce is
  bounded to 64 bits, and authorization `r`/`s` are bounded to 256 bits;
- list shapes and scalar overflows produce distinct canonical reasons.

Do not change transaction signing hashes, transaction trie bytes, or valid
type-4 behavior fixed under finding 3.1. Add one positive and at least one
oversized negative vector for each transaction type, plus access-list,
blob-hash, and authorization boundary vectors.

Run V0, PATCH, and relevant type-1/type-2/type-3 fixture directories. Search
the decoder region for `.toB64`, `.toB256`, `.toAdr?`, and `takeD`; every
remaining raw conversion must be immediately dominated by a visible successful
width check. Report that audit. [V0 + PATCH]

### Note for the reader

This completes finding 3.6 beyond the three currently failing withdrawal and
gas-limit files. Most of these malformed typed transactions were previously
invisible because the oracle accepted a later broad failure.

---

## Step 9 — Complete exact classification of block and transaction failures

### Agent prompt

Finish the actual-error side of `FixtureException` without wiring it into the
runner yet. Re-generate the 35-identity Prague inventory and map every identity
to its real producer or to an explicit runner-level condition.

Audit and make unambiguous the transaction validation paths around:

- intrinsic gas and calldata floor;
- block gas allowance;
- nonce max, too low, and too high;
- insufficient funds and gas-price-product overflow;
- sender-not-EOA;
- max fee and priority fee;
- initcode size;
- type-3 empty blobs, blob count, contract creation, and version byte.

Likewise finish any block mappings not completed in Steps 6–7: ommers after
Paris, unknown parent, roots, bloom, gas-used overflow, and RLP structure.
Where two official identities currently share one bare internal string, make
the producer more precise; do not guess identity from unrelated later
failures. It is acceptable to keep detailed internal text after the canonical
tag delimiter.

Add a coverage check which fails if any expected identity from the generated
fixture inventory lacks an actual-classification route. Also check the
opposite direction: every registered actual prefix maps to exactly one
canonical identity. Include negative tests for the old broad strings
`"InvalidBlock"`, `"InvalidTransaction"`, and arbitrary RLP errors; they must
not classify.

Run V0, PATCH, and INVALID-AUDIT in diagnostic mode. Produce a table of
expected identity, current producer/mapping, and fixture count. Do not weaken
the table to make an unexplained mismatch disappear. [V0 + PATCH +
INVALID-AUDIT diagnostic]

### Note for the reader

At plan-writing time, 122 expected alternatives mention insufficient funds,
79 intrinsic gas, and 66 post-Paris ommers, while many identities occur only
once. The coverage table is what prevents the rare one-off cases from being
silently accepted by a generic category.

---

## Step 10 — Add a parent-hash-indexed chain-snapshot store

### Agent prompt

Add a small fixture-runner data structure, preferably beside the Step 4
fixture module rather than in core EVM semantics. This step is additive; keep
the old `processBlockJsons` wired until Step 11.

The store contains immutable `BlockChain` snapshots indexed by the hash of
their tip. Use an existing ordered map or a simple association list; do not
introduce a new questionable `Hashable B256` instance merely for the harness.
Provide operations to:

1. initialize with the genesis snapshot and its verified hash;
2. find the parent snapshot for a decoded block's `header.parentHash`;
3. insert a successful child snapshot under its computed tip hash;
4. leave the store unchanged after a rejected block;
5. retrieve the final snapshot named by fixture `lastblockhash`.

Represent unknown-parent failure explicitly, distinguishing the all-zero
parent hash from any other missing hash so Step 9's exact identities can be
used. `chainname` may be retained in diagnostics, but it must not decide
parentage; the block header is authoritative.

Add a pure synthetic fork test: genesis has children A1 and B1; A2 extends A1;
B2 extends B1; rejecting a candidate B3 does not change B2; looking up A2 and
B2 yields different snapshots. Test final lookup by hash. Run V0 and PATCH;
classifications should be unchanged. Report the store invariants and synthetic
fork results. [V0 + PATCH unchanged]

### Note for the reader

Keeping full snapshots is cheap for these immutable Lean values and avoids the
need to reconstruct state at a fork point. It is also more faithful than a map
from the fixture's advisory `chainname` to one mutable current chain.

---

## Step 11 — Replace the fixture oracle and process every block strictly

### Agent prompt

Work primarily in `/Users/bsk/elevm/Main.lean`. Replace the old linear,
broadly classified `processBlockJsons` with the Step 10 snapshot store and the
Step 4 exact matcher. Preserve the public core `addBlockToChain` API.

For each block JSON, in fixture order:

1. require and print its index and `chainname` for diagnostics;
2. read the raw RLP and parse its optional expected-exception set;
3. if enough decoding succeeds to obtain `parentHash`, select that parent
   snapshot; otherwise treat the decoder error itself as the actual result;
4. evaluate `addBlockToChain`, handling both outer `.error err` and inner
   `.ok (.inr err)` as failures to classify;
5. for an expected-valid block, require success and insert its child snapshot;
6. for an expected-invalid block, require a failure whose one canonical
   identity belongs to the expected set, do not insert anything, and continue;
7. never stop the file merely because an expected-invalid block passed its
   check.

At the end, always retrieve the snapshot named by `lastblockhash`, verify its
tip hash, and verify the post-state root. This includes files containing only
expected-invalid blocks and files with valid blocks after an invalid candidate.

Make network selection explicit. Add a `--network` option whose default is
`Prague`, print selected and skipped case counts, and fail a file invocation if
zero cases match the combined network/name/index filters. Skipping a Cancun
case while explicitly running Prague is fine; silently running zero cases is
not. Ensure the shell harness passes or relies visibly on the explicit Prague
default.

Remove the oracle's use of `isEthereumException` and `isRlpException`; delete
them if a cross-repository reference search shows they are now dead. Unknown
actual errors and unknown expected identities must print both raw and canonical
diagnostics and fail.

Run V0, PATCH, RLP4, and INVALID-AUDIT. All ten historical FAIL files must now
be `PASS`; in particular `UncleFromSideChain` must process A and B from their
actual parents, accept the expected invalid ommer rejection without mutating
the branch, continue to the later valid B block, and perform final hash/state
checks. Blake2F must remain `PASS`. Record every new strict-oracle failure
outside PATCH without broadening the matcher. [V0 + PATCH green + RLP4 green +
INVALID-AUDIT]

### Note for the reader

The decisive success signs are not merely “the invalid block was rejected.”
They are: the rejection identity matches, the branch snapshot is unchanged,
later blocks still run, and the file's final state is checked.

---

## Step 12 — Full-suite closure, strict baseline, and final audit

### Agent prompt

This is the only overnight step. First run V0, PATCH, RLP4,
INVALID-AUDIT, SMOKE, and PERF. PATCH must be 11/11 `PASS` before starting the
full run. Preserve the pre-strict `baseline-full.txt` and run FULL without
rebasing.

Classify every full-suite difference into one of four buckets:

1. intended fix among the original ten;
2. intended performance change (`TIMEOUT` to `PASS` for Blake2F);
3. newly exposed strict-oracle mismatch;
4. unintended regression in a previously valid case.

Buckets 1 and 2 are expected. For bucket 3, determine whether the cause is a
bad mapping/runner implementation or a real ELeVM conformance defect. Repair
mapping/runner errors in this step. Genuine new semantic defects may remain
as documented FAILs because strict checking is the purpose of finding them;
list the fixture, expected identity, actual identity/raw error, and likely
implementation area. Bucket 4 must be fixed before closure.

After the user reviews the complete diff, preserve the old baseline under a
clearly named historical file or commit history and establish the new strict
`baseline-full.txt`. Do not call a baseline with unexplained failures green.
The final report must include file and case counts, all classifications,
before/after Blake2F time, and the list of any newly exposed genuine defects.

Finish with a source audit:

- no unchecked truncating conversion remains in the header, withdrawal,
  legacy, typed-transaction, access-list, blob-hash, or authorization decoders;
- `B8L.toAdr?` rejects trailing bytes;
- `checkGasLimit` enforces `< 2^63`;
- the fixture oracle performs exact identity matching and fails on zero
  selected cases;
- expected-invalid blocks do not stop later processing or skip final checks;
- parent snapshots, not list order, determine block ancestry;
- normal and system transactions refresh `origState`;
- `Hashable (Adr × B256)` includes the key;
- Blake2F has no per-round tracing;
- findings 3.6, 3.8, and 3.9 have no remaining source witness from
  `review.md`.

Run the blanc axiom audit one final time and report that the four top theorem
statements and axiom sets are unchanged. [V0 + PATCH + RLP4 + INVALID-AUDIT +
SMOKE + PERF + FULL]

### Note for the reader

The expected ideal total, if no new strict failures appear and only Blake2F
leaves the timeout set, is 2,981 `PASS`, 0 `FAIL`, and 2 `TIMEOUT` files out of
2,983. A different total is not automatically bad, but every difference must
be explained. The strict baseline is an assurance artifact, not a score to
optimize.

---

## Expected end state

After Step 12:

- all ten historical FAIL files are PASS;
- the two already-fixed BLOCKHASH files remain protected by the PATCH tier;
- multi-transaction storage gas/refunds use transaction-scoped original
  state;
- competing branches import from the correct parent snapshot;
- malformed headers, withdrawals, legacy transactions, typed transactions,
  access lists, blob hashes, and authorizations are rejected before any
  truncating conversion;
- fixture expected exceptions are matched by exact canonical identity;
- no selected fixture file can pass by running zero cases, stopping after an
  expected-invalid block, or skipping final state checks;
- same-address storage keys distribute across the key-set hash table;
- Blake2F runs without per-round trace overhead and the max-round fixture is
  expected to pass under the normal timeout;
- any newly exposed strict-oracle failures are explicit, reproducible, and
  documented rather than hidden by a permissive classifier.
