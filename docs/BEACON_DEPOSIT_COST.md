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

- `BeaconDepositLoopTail.lean`: one recursive auxiliary-table slot, constant
  EVM stack height, and one copy of the loop body;
- `BeaconDepositLoopUnrolled.lean`: 32 source-generated copies of that body,
  with the storage height specialized in each copy.

Both stage exactly 64 input bytes and issue `STATICCALL` to address `0x2` with
a 32-byte output window. Both route call failure through
`Func.revReturnData`, reject a successful response shorter than 32 bytes via
the shared empty reverter, and otherwise consume the first output word,
exactly as the pinned solc SHA wrapper does. They intentionally omit the final count mix-in,
which is identical straight-line code in either realization and therefore
cannot decide the comparison.

## Measurement protocol

Measurements are serial and exclusive under the host hard semaphore. Each
file is evaluated from the same candidate and warm dependency state using
`lake env lean`; `/usr/bin/time -l` records wall time and peak resident set,
and the evaluator prints the compiled byte length. The tail prototype is run
again after the unrolled prototype to expose gross order/cache effects. No
language server or other elaboration-class job may be resident during this
measurement.

Candidate, commands, raw readings, and verdict will be inserted at the first
exclusive measurement boundary. Until then no production loop realization is
frozen.

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

## Final decision

Pending exclusive measurement.
