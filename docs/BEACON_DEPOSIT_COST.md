# Beacon deposit port — loop-realization cost record

This record owns the measured decision required by the compiled BeaconDeposit
port. It compares two implementations of the first fixed-depth slice before
the production family commits to either one. It is evidence about Blanc's own
artifact and proof workflow; it is not a comparison with the deployed
Solidity bytecode or its gas.

## Decision boundary

The source has three bounded walks:

- the 32-step `get_deposit_root` fold, followed by one count mix-in;
- the at-most-32-step deposit insertion walk (at most 31 pair hashes after the
  cap guard, then one branch write);
- the constructor's 31-step zero-hash materialization.

The first prototype is the root fold because it exercises every mechanism
that distinguishes the alternatives: a changing height and size, a per-step
branch, two storage reads, an exact 64-byte SHA-256 precompile window, a
32-byte result, and continuation to the next iteration.

Two disposable files under `/private/tmp` use the real Blanc compiler:

- `BeaconDepositLoopTail.lean`: one recursive loop slot plus one shared
  continuation slot, constant EVM stack height, and one copy of each distinct
  live/dead SHA wrapper;
- `BeaconDepositLoopUnrolled.lean`: 32 source-generated step slots plus a
  finish slot, with the storage height specialized in each step and distinct
  live/dead SHA wrappers in every copy.

Both stage exactly 64 input bytes and issue `STATICCALL` to address `0x2` with
a 32-byte output window. Both route call failure through
`Func.revertReturnData`, reject a successful response shorter than 32 bytes via
the shared empty reverter, and otherwise consume the first output word,
exactly as the pinned solc SHA wrapper does. The measured files have SHA-256
digests
`0588d1a4939317d1b06df5e34cf85b12913c39ad8882d1f89d4165eeadc9b9c5`
and `f1da9cb24a6fa1210fa8d9997970a63ed40ab3430c13643454f6a9904aa6fde6`,
respectively. They intentionally omit the final count mix-in,
which is identical straight-line code in either realization and therefore
cannot decide the comparison.

These are compiler-shape probes, not executable root fixtures: their entry
uses a zero placeholder size and their finish returns the intermediate word.
The production endpoint must instead load `deposit_count`, retain its original
value, and perform the count mix-in before returning. Keeping that common
straight-line prefix/suffix out of both probes isolates the realization cost
without licensing either placeholder in production.

## Measurement protocol

Measurements are serial and exclusive under the host hard semaphore. Each
file is evaluated from the same candidate and warm dependency state using
`lake env lean`; `/usr/bin/time -l` records wall time and peak resident set,
and the evaluator prints the compiled byte length. The tail prototype is run
again after the unrolled prototype to expose gross order/cache effects. No
language server or other elaboration-class job may be resident during this
measurement.

The exclusive measurement ran on candidate
`b19f13887621253ecb389d11acc0b06d12f95ed3` under hard semaphore label
`beacon-deposit-port-v1-loop-measure`. The valid readings were:

| Run | Command | Compiled bytes | Real | User | System | Maximum RSS |
|---|---|---:|---:|---:|---:|---:|
| tail, first | `/usr/bin/time -l lake env lean /private/tmp/BeaconDepositLoopTail.lean` | 179 | 1.24 s | 0.67 s | 0.66 s | 1,511,686,144 B |
| unrolled | `/usr/bin/time -l lake env lean /private/tmp/BeaconDepositLoopUnrolled.lean` | 4,195 | 1.21 s | 0.66 s | 0.64 s | 1,512,652,800 B |
| tail, repeat | `/usr/bin/time -l lake env lean /private/tmp/BeaconDepositLoopTail.lean` | 179 | 1.22 s | 0.66 s | 0.65 s | 1,513,799,680 B |

The first sandboxed timing attempt elaborated the tail prototype and printed
179 bytes, but macOS denied `time -l` its `kern.clockrate` query and therefore
did not produce the required memory record. It is excluded from the table; the
same command was rerun with permission to read process statistics. Pre- and
post-prototype telemetry both reported 75% system memory free, with no Lean
process left resident after each compiler invocation.

The unrolled prototype is 4,016 bytes larger, or about 23.4 times the tail
prototype's byte length. Its wall time and maximum RSS are indistinguishable
at this scale, including against the repeat tail control, so they provide no
countervailing reason to carry 32 copies of each source-shaped SHA wrapper
into the artifact and every downstream compiled walk.

## Proof-performance interpretation

The decisive quantities are artifact growth and proof-term shape, not a
single noisy wall-clock delta. An unrolled result would require a carrier
abstraction from the first production proof so concrete internals never ride
through a 31/32-copy `RunCompiled` walk. A tail-recursive result instead needs
one loop invariant and one reusable SHA call boundary, but keeps both bytecode
and elaborated source structurally bounded. No resource ceiling is introduced
by this decision.

## ABI accounting correction

The event payload is 576 bytes: five 32-byte head offsets (160 bytes), plus
tails of 96, 64, 64, 128, and 64 bytes (416 bytes). The architecture memo's
“~416 bytes of log data” is therefore the tails-only subtotal. The pinned ABI
and Solidity source control the implementation and the byte-exact event
predicate.

## Early artifact and runtime-gas checkpoint

Before compiled-effect proofs make the emitted program expensive to change,
the exact compiler-owned artifact was compared with the pinned deployed
referent. This checkpoint does not alter the loop-choice experiment above and
does not claim byte or gas identity:

| Artifact | Blanc | Referent | Blanc reduction |
|---|---:|---:|---:|
| runtime | 2,891 bytes | 6,358 bytes | 3,467 bytes (54.53%) |
| creation | 3,037 bytes | 6,633 bytes | 3,596 bytes (54.21%) |

The pinned Prague runtime matrix has 69 direct-message executions: 67 are
strictly cheaper in Blanc, two shared-gas OOG thresholds are equal, and none
is more expensive. The median Blanc-minus-reference delta is -1,131 gas and
the largest saving is 18,090. The exact per-row values, artifact digests, and
finite-evidence boundary are owned by the differential manifest and
`BEACON_DEPOSIT_DEVIATIONS.md`.

Constructor gas is deliberately measured separately as total direct creation-
message gas, runtime code-deposit gas, and constructor-execution gas. Closure
requires both the total and execution-only Blanc deltas to be non-positive, so
the smaller runtime cannot hide a worse constructor. The optimized constructor
uses 1,274,272 gas versus 1,993,844 for the referent (-719,572); after removing
runtime code deposit, its own execution uses 696,072 versus 722,244 (-26,172).
Thus the constructor wins independently of Blanc's smaller deposited runtime.

The current-mainnet BPO2 lane independently confirms that conclusion at the
top-level transaction boundary. In fresh creation state transitions, the
referent uses 2,146,896 gas and Blanc 1,368,074 (-778,822). The side-specific
regular intrinsic charges are 153,052 and 93,802, and code deposit is 1,271,600
and 578,200. Subtracting those components leaves 722,244 versus 696,072
(-26,172) of receipt-charged constructor execution after any transaction
refund. The pinned t8n result does not expose the refund counter, so the BPO2
evidence deliberately does not claim it is zero; the historical direct-message
campaign owns that stronger observation.

The BPO2 runtime state chain likewise has no regression: Blanc-minus-reference
gas is -6,801 for deposit, -18,072 for root, -1,131 for count, zero for each of
the three ERC-165 probes, and -26 for no-match. The exact target provenance,
receipts, state, raw event bytes, and decomposition are committed in
`scripts/fixtures/beacon-deposit-current-mainnet/manifest.json`; exact
returndata and the broad malformed/precompile/OOG matrix remain with the
historical Prague manifest.

## Final decision

Use tail-recursive auxiliary slots at constant EVM stack height for all three
production loops: the 32-step root fold, the at-most-32-step insertion walk,
and the 31-step constructor zero-hash materialization. Each loop gets one
shared continuation slot and one inductive invariant; the root loop retains
distinct live/dead SHA sites, while insertion and construction each retain
their one source-shaped site. No unrolled carrier abstraction and no resource
ceiling is introduced.

The measured decision is dominated by artifact and proof-shape cost: 179 bytes
versus 4,195 bytes for the isolated slice, with effectively equal compilation
time and memory. This freezes the executable realization; later proof work may
split invariants across modules but may not silently replace the loops with an
unroll.
