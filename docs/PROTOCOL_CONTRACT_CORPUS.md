# Protocol-contract corpus

**UNADOPTED REVIEW DRAFT — bindings and wording are incomplete.**

This file supplies no accepted claim or provenance. Missing evidence stays red.

## Matrix

| Row | D | R | H | W | C | B |
|---|---|---|---|---|---|---|
| S1 | [PENDING](#d-s1) | [PENDING](#r-s1) | [PENDING](#h-s1) | [PENDING — Exact system storage writes still need a pinned headline.](#w-s1) | [PENDING](#c-s1) | [PENDING](#b-s1) |
| S2 | [PENDING](#d-s2) | [PENDING](#r-s2) | [PENDING](#h-s2) | [PENDING — Exact kept-frame classification still needs its public pin.](#w-s2) | [PENDING](#c-s2) | [PENDING](#b-s2) |
| S3 | [PENDING](#d-s3) | [PENDING](#r-s3) | [PENDING](#h-s3) | [Admitted deployment histories determine word bookkeeping, FIFO records and block publication.](#w-s3) | [PENDING](#c-s3) | [PENDING](#b-s3) |
| S4 | [PENDING](#d-s4) | [PENDING](#r-s4) | [PENDING](#h-s4) | [Conditional observed deployment traces establish canonical code and initial queue words.](#w-s4) | [PENDING](#c-s4) | [PENDING](#b-s4) |
| S5 | N/A (fee row) | N/A (fee row) | N/A (fee row) | [PENDING — The exact fee-equality domain is pinned; first divergence remains incomplete.](#w-s5) | [PENDING](#c-s5) | [PENDING](#b-s5) |
| S6 | [PENDING](#d-s6) | [PENDING](#r-s6) | [PENDING](#h-s6) | [Every configured suffix retains the checkpoint balance plus committed submission payments.](#w-s6) | [PENDING](#c-s6) | [PENDING](#b-s6) |
| S7 | [PENDING](#d-s7) | [PENDING](#r-s7) | [PENDING](#h-s7) | [PENDING — Actual word-fee guard liveness still needs a complete pinned binding.](#w-s7) | [PENDING](#c-s7) | [PENDING](#b-s7) |
| S8 | [PENDING](#d-s8) | [PENDING](#r-s8) | [PENDING](#h-s8) | [An admitted extension delivers queue position q in block q/16 at record q%16.](#w-s8) | [PENDING](#c-s8) | [PENDING](#b-s8) |
| S9 | [PENDING](#d-s9) | [PENDING](#r-s9) | [PENDING](#h-s9) | [PENDING — Joint authorization, fate and crediting proofs still need all nine component pins.](#w-s9) | [PENDING](#c-s9) | [PENDING](#b-s9) |
| S10 | [PENDING](#d-s10) | [PENDING](#r-s10) | [PENDING](#h-s10) | [PENDING — The Amsterdam system-call result still needs its exact pin and complete S1 mapping.](#w-s10) | [PENDING](#c-s10) | [PENDING](#b-s10) |

## D-S1

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## R-S1

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## H-S1

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## W-S1

### Premises

The existing `system_call_succeeds` assumes canonical installed code and a covered fork, with arbitrary storage. Its `SystemCallOk` conclusion supplies checked-call success and a 210,000 gas bound.

### Non-claims

This cell remains incomplete: `SystemCallOk` existentially quantifies the post-state and does not state the exact storage writes required by S1. No full-cell binding is proposed.

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## C-S1

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## B-S1

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## D-S2

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## R-S2

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## H-S2

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## W-S2

### Premises

The source-level `exec_frame_effect` classifies successful canonical frames into system, submission and fee-getter arms. It assumes a covered fork, empty stack, aligned well-formed memory and calldata length below 2^256, and exposes exact arm post-state constructors.

### Non-claims

This cell remains incomplete: no existing full theorem key and typed claim example were found for the complete kept-history frame clause. The local classifier alone is not a proposed binding for the history statement.

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## C-S2

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## B-S2

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## D-S3

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## R-S3

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## H-S3

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## W-S3

### Premises

`block_word_fifo` takes a canonical Cancun deployment with its environmental Admission, a configured modern history and next block, the other system contracts installed at the checkpoint, no SYSTEM transaction sender or authority, no CREATE target at SYSTEM, and at most 2^254 committed submission occurrences over the extended history. The modern trace uses CoveredFork (Prague, Osaka, BPO1 or BPO2). Admission derives initial storage, canonical withdrawal code and checkpoint SYSTEM emptiness. Its BlockWordFifo conclusion includes initialization, an empty preactivation submission prefix, the exact request-boundary word model, emission, post-reset representation, FIFO, provenance and bookkeeping safety.

### Non-claims

This draft binding is conditional on the supplied traces and admission; it does not authenticate observed chain data, prove future block production, cover arbitrary occurrence overflow or clear stale storage outside the represented live queue. Word-fee behavior is preserved without assuming equality with the natural-number EIP fee. The existing pinned drain control establishes that checkpoint SYSTEM emptiness is load-bearing; the structural matrix checker does not require that control.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Lift.WithdrawalRequest.block_word_fifo` (`Blanc/Lift/WithdrawalRequest/WordFifo.lean:641`) | `thm:Blanc.Lift.WithdrawalRequest.block_word_fifo` |

## C-S3

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## B-S3

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## D-S4

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## R-S4

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## H-S4

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## W-S4

### Premises

`deploy_mainnet` takes a mainnet-configured historical block trace, its position-0 transaction split, a following historical trace to the checkpoint, a WithdrawalDeploymentObservation and avoidance of CREATE targeting SYSTEM throughout the prefix. The observation records deployment block 21881389 and checkpoint 22431083, their hashes and roots, the keyless creation transaction and successful receipt, and the required account/code observations. The conclusion gives canonical runtime and InitialWords both immediately after the creation transaction and at the checkpoint; InitialWords means inhibitor excess and zero count, head and tail.

### Non-claims

This is a conditional modeled execution-history bridge. The observation values remain unadopted candidates; neither this theorem nor this draft authenticates headers, trie proofs, receipts, mainnet inclusion or the existence of the assumed traces. The binding does not itself adopt public provenance.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Lift.WithdrawalRequest.deploy_mainnet` (`Blanc/Lift/WithdrawalRequest/HeadlineHistory.lean:212`) | `thm:Blanc.Lift.WithdrawalRequest.deploy_mainnet` |

## C-S4

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## B-S4

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## W-S5

### Premises

Given an actual WordFakeExponential.Run from excess with denominator 17 and initial accumulator 17, `fee_eq_spec_iff` proves that WordFee(output) equals fake_exponential(1, excess, 17) exactly when NatFeeDomain(excess, iterations) holds. NatFeeDomain quantifies a natural-number loop trace with the specified prefixed no-wrap bounds.

### Non-claims

Only the fee-domain component is proposed. The existing pinned existential underpayment refutation does not state a least excess or prove agreement at every earlier excess. The first-divergence component remains missing. This draft makes no reachable-domain or public provenance claim.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| fee-domain | `Blanc.Lift.WithdrawalRequest.fee_eq_spec_iff` (`Blanc/Lift/WithdrawalRequest/HeadlineFee.lean:48`) | `thm:Blanc.Lift.WithdrawalRequest.fee_eq_spec_iff` |

## C-S5

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## B-S5

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## D-S6

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## R-S6

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## H-S6

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## W-S6

### Premises

`history_payments_mainnet` assumes the same mainnet historical deployment block, position-0 split, following prefix, observation and SYSTEM-target avoidance as W-S4, followed by a configured modern history. It proves checkpoint balance plus submissionPaid(history) is at most the final withdrawal-account balance. submissionPaid sums values of the settled submission-payment observations, including nested committed calls.

### Non-claims

The bound is an inequality and concerns committed submission payments, not reverted calls or an asserted accounting of unrelated transfers. It needs no FIFO occurrence bound. The deployment observation and trace-existence/authentication limitations in W-S4 remain.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Lift.WithdrawalRequest.history_payments_mainnet` (`Blanc/Lift/WithdrawalRequest/HeadlineHistory.lean:228`) | `thm:Blanc.Lift.WithdrawalRequest.history_payments_mainnet` |

## C-S6

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## B-S6

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## D-S7

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## R-S7

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## H-S7

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## W-S7

### Premises

The pinned `history_submission_live` and its mainnet instance prove exact fresh 56-byte submission cost and residual gas under sufficient SpecFee payment, with an inhibitor rejection arm. Separate source-level `exec_submission_word_live` and `exec_fee_getter_word_live` use the actual word-fee guards and closed submission/getter charges.

### Non-claims

This cell remains incomplete: paying the natural-number SpecFee is stronger than the bytecode's actual word-fee admission guard outside the equality domain. No existing full theorem keys and typed claim examples were found for both actual-guard branches. The narrower pinned sufficient-payment theorem is not substituted for the complete S7 clause.

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## C-S7

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## B-S7

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## D-S8

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## R-S8

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## H-S8

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## W-S8

### Premises

`history_delivery_mainnet` uses the W-S4 observed deployment bridge, configured histories through blocks B and D, and an ExtendsBy relation of depth q/16 between those extended histories. The latter history excludes SYSTEM senders, authorities and CREATE targets and contains at most 2^254 committed submissions; the observation supplies the other checkpoint system code. For each record actually at queueAtRequests(B)[q], Delivered states blockWithdrawals(D)[q%16] is that record, with the exact preceding prefix from B's queue after dropping 16*(q/16) entries.

### Non-claims

The theorem is conditional on the admitted extension and queue membership. It does not produce future blocks, assert wall-clock latency, promise consensus acceptance or prove withdrawal crediting. Existing request-seam rejection and one-entry late-seam controls have no full theorem keys in the inherited manifest; the latter is an abstract queue counterexample. The structural checker does not enforce either control.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Lift.WithdrawalRequest.history_delivery_mainnet` (`Blanc/Lift/WithdrawalRequest/HeadlineHistory.lean:244`) | `thm:Blanc.Lift.WithdrawalRequest.history_delivery_mainnet` |

## C-S8

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## B-S8

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## D-S9

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## R-S9

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## H-S9

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## W-S9

### Premises

The source ValidJoint package includes deployment and admission, the pre-anchor execution history, a JointRun, AnchorInv, preset balance/epoch bounds, other installed code, SYSTEM exclusions and the occurrence cap. Existing theorems separately address exact authorization position, occurrence fate, processing outcome, retained payments, crediting recipient, first-loop budget, floor, compounding and address preservation. Their joint scope is Electra/Prague or Fulu/Osaka/BPO; signature-checking mode is an explicit parameter.

### Non-claims

All nine bindings remain missing: no matching full stable theorem keys or typed ClaimCheck examples were found for these public joint declarations. Theorems assume the supplied joint run and anchor invariant; they do not establish an inhabited real-BLS run, Gloas coverage or eventual withdrawal. Bad-credential/source, ignored-reason, order, payload and anchor-invariant controls also lack inherited theorem keys. The structural checker requires the nine headline components but has no control-coverage requirement.

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## C-S9

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## B-S9

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## D-S10

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## R-S10

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## H-S10

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## W-S10

### Premises

The source-level `Amsterdam.system_call_ok` assumes Amsterdam and canonical installed code, with arbitrary storage. It concludes checked-call success at the explicit sysState post-state and RegularGasWithin 163000, excluding state gas.

### Non-claims

This cell remains incomplete: the existing manifest contains no full theorem key or typed ClaimCheck example for that declaration. Its sysState closure must be mapped to the complete S1 storage clause before a full-cell binding can be proposed. The regular-gas result does not bound Amsterdam state gas.

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## C-S10

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## B-S10

### Premises

PENDING

### Non-claims

PENDING

### Evidence

| Components | Theorem | Pin |
|---|---|---|

## Implementation notes

This unadopted draft has no production theorem/pin mappings. Exact typed examples,
certified closure roots, clause review and user wording/provenance adoption remain owed.
Standalone checker success would establish structure only; final acceptance also requires
the existing exact-candidate claims and closure-hash gates and their certified build.

Revision 4 keeps both builder contracts and every original obligation. Future focused
B references must cover P1 history-wide queue fee budgets and conditional Amsterdam
payload delivery; P2 precise legible statements with complete premises; P3 actual
debit-at-most-once with bid occurrence identity, quorum/settlement/old-parent paths
and the exact first-crossing-bid limitation if unresolved; P4 the explicit
no-Amsterdam prefix and resulting focused fate. No unwritten proof names are proposed.
P5 real-BLS nontrivial exact-ValidJointG applicability evidence needs its separate
measured route and exact checker/witness boundary; this matrix parser cannot supply it.
P6/P7 remain assessed/optional. No observation, public count, external comparison or
publication is adopted by this file.

R-S8 uses both time and slot statements and the adopted arithmetic control limitation.
R-S9 retains the exact skipped-slot guard; H-S9 requires its chain form.
D-S9 keeps real BLS and its conditional positive-witness disclosure. New S4 records
remain provenance decisions. Amsterdam for D/R/H/W/C is confined to S10.

Later real G3 control: on the fully certified complete candidate, delete one actual
required roots.tsv row in a disposable copy; the direct checker must identify its
cell/component/key. Restore identical bytes and show green. Synthetic self-tests
do not supply this full-candidate evidence. No root artifact is written here.
