# Deployed-bytecode claim map: EIP-7251 consolidation requests

## 5.12 EIP-7251 consolidation requests: system call, what succeeds, fee and FIFO

EIP-7251's predeploy at 0x0000BBdDc7CE488642fb579F8B00f3a590007251 queues consolidation requests.
A user pays a fee and submits 96 bytes: a source public key and a target public key. Once per
block the system call takes up to two records from the queue and returns them. Each record is
116 bytes: the caller's 20-byte address, then the 96 submitted bytes.

Every statement below is about the canonical runtime `Blanc.consolidationRequestCode` (`Blanc/SystemContracts.lean:92`),
414 bytes, on the covered forks (`CoveredFork`: Prague, Osaka, BPO1, BPO2). The headlines live in
`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean` and
`Blanc/Composition/ConsolidationRequestPublicHistory.lean`. They read the chain through short
observers: storage words, the queue as stored, the frames a history commits and the requests its
blocks publish. 9 statements are featured: C1, C2,
C3a to C3c, C4 in two forms, and C5 in two parts.

**System call, what succeeds and fee**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| **C1. System call.** With the canonical code installed, whatever storage holds, the checked system call succeeds with no error and uses at most 114,177 gas | `Blanc.Composition.ConsolidationRequestPublic.system_call_succeeds` (`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean:43`), with conclusion `Blanc.Composition.ConsolidationRequestPublic.SystemCallOk` (`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean:37`); via `Blanc.Lift.ConsolidationRequest.system_call_ok` (`Blanc/Lift/ConsolidationRequest/System.lean:116`) | Frame / totality | CODE; covered fork | No storage premise. The headline bounds the gas used; it does not state the post state. That is C1b |
| **C1b. Bookkeeping.** With head ≤ tail, the tail below 2^253 and no 256-bit wrap in excess + count, the system call does the EIP's bookkeeping: `excess' = max(0, e + count − 1)` where e is the stored excess read as 0 at the inhibitor, `count' = 0`, the first min(2, queue) entries leave, both pointers reset to 0 when the queue empties, no slot beyond the four words changes, and the call returns exactly the entries that left | `Blanc.Composition.ConsolidationRequestPublic.system_call_bookkept` (`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean:95`), with conclusion `Blanc.Composition.ConsolidationRequestPublic.Bookkept` (`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean:54`) over `Blanc.Composition.ConsolidationRequestPublic.excessAfter` (`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean:51`) | Frame / refinement | CODE; covered fork; ARITH: head ≤ tail, tail < 2^253, e + count < 2^256 | Not featured. The tail bound is needed: each record takes four slots from slot 4, so a tail at or above 2^253 lets a record key wrap onto slots 0 to 3. The no-wrap bound is needed because the bytes add excess and count as 256-bit words. On a kept history from the checkpoint, `Blanc.Composition.ConsolidationRequestPublic.history_pointers` (`Blanc/Composition/ConsolidationRequestPublicHistory.lean:181`) gives head at most tail and tail at most the submission count, so the room premise holds below 2^253 submissions |
| **C2. What succeeds.** Every successful fresh frame at the predeploy running this code is exactly one of three: a system dequeue, a submission or a fee read. A dequeue (caller SYSTEM_ADDRESS) leaves the state the system call defines and, when head ≤ tail, returns the first two stored entries. A submission (96 bytes from a user, non-static, slot 0 off the inhibitor, value at least the quoted fee) stores its record at the tail, emits one topicless log of its 116 record bytes, changes no other account's storage and leaves the output unchanged. A fee read (empty calldata, no value, from a user, slot 0 off the inhibitor) returns the quoted fee as one word and changes nothing. No other fresh entry succeeds | `Blanc.Composition.ConsolidationRequestPublic.exec_succeeded` (`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean:272`), with conclusion `Blanc.Composition.ConsolidationRequestPublic.Succeeded` (`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean:219`) over `Blanc.Composition.ConsolidationRequestPublic.submissionLog` (`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean:215`), `Blanc.Lift.ConsolidationRequest.submittedStorage` (`Blanc/Lift/ConsolidationRequest/Frames.lean:36`) and `Blanc.Lift.RequestSystem.sysState` (`Blanc/Lift/RequestSystem/Call.lean:267`); via `Blanc.Lift.ConsolidationRequest.exec_system_frame` (`Blanc/Lift/ConsolidationRequest/SystemFrame.lean:75`), `Blanc.Lift.ConsolidationRequest.exec_user_frame` (`Blanc/Lift/ConsolidationRequest/Frames.lean:195`) | Frame / refinement | CODE; covered fork; fresh entry (`FreshEntry`: empty stack, word-aligned well-formed memory, calldata shorter than 2^256 bytes) | **Success is classified, failure is not**: which failure occurs (REVERT, out-of-gas, a static-context fault), its gas and its return data are not stated. The dequeue arm's storage field holds with no premise; its output field is stated only when head ≤ tail (Section 7 item 56). At the inhibitor no user call succeeds, since both user arms require slot 0 off it |
| **C3a. Fee bound.** The fee the bytes quote at any excess is at most the EIP's fake_exponential(1, excess, 17) | `Blanc.Composition.ConsolidationRequestPublic.fee_le_spec` (`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean:162`), over `Blanc.Composition.ConsolidationRequestPublic.quotedFee` (`Blanc/Composition/ConsolidationRequestPublicObservers.lean:36`) and `Blanc.Composition.ConsolidationRequestPublic.SpecFee` (`Blanc/Composition/ConsolidationRequestPublicObservers.lean:33`); via `Blanc.Lift.ConsolidationRequest.fee_le_spec` (`Blanc/Lift/ConsolidationRequest/Fee.lean:60`) | Function / refinement | none | The quoted fee is the word the bytes' fee loop leaves, divided by 17. It is what a fee read returns and what a submission must pay (C2) |
| **C3b. Exact fee through excess 2892.** At every excess up to 2892 the quoted fee equals fake_exponential(1, excess, 17) | `Blanc.Composition.ConsolidationRequestPublic.fee_eq_spec_of_le` (`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean:168`); via `Blanc.Lift.ConsolidationRequest.fee_eq_spec_of_le` (`Blanc/Lift/ConsolidationRequest/Fee.lean:73`) | Function / refinement | ARITH: excess ≤ 2892 | Stated as a bound, not as an equivalence: nothing is claimed about excesses above 2893 |
| **C3c. The bytes depart from the EIP at excess 2893.** At excess 2893 the quoted fee is strictly less than fake_exponential(1, 2893, 17) | `Blanc.Composition.ConsolidationRequestPublic.fee_lt_spec_2893` (`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean:177`); via `Blanc.Lift.ConsolidationRequest.fee_ne_spec_2893` (`Blanc/Lift/ConsolidationRequest/Fee.lean:79`); the 87-byte fee windows differ exactly at index 41 (0x9a vs 0xf4, pc 0x43), `Blanc.Composition.ConsolidationRequestPublic.fee_window_bytes_eq` (`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean:186`) | Function / finding | ARITH: excess = 2893 | A function-level finding. No history reaching excess 2893 is proved for these bytes (Section 7 item 59) |

**FIFO from the checkpoint and at mainnet**

The FIFO law `Fifo blocks final` states `submissions blocks = emissions blocks ++ remainingQueue final`.
All three lists are direct observations. The submissions are the records of the committed 96-byte
calls at the predeploy from a caller other than SYSTEM_ADDRESS, nested calls included, in history
order. The emissions are the type-2 payloads of the blocks' actual request lists, cut into
116-byte records; a short tail is kept as a record, so equality detects it. The remaining queue is
read from the final storage. Equality keeps order and multiplicity.

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| **C4. FIFO from the checkpoint.** For every kept history at covered forks that starts with the predeploy at its deployed words, every committed submission is, in order, either a record the blocks published or an entry still in the final stored queue | `Blanc.Composition.ConsolidationRequestPublic.history_fifo` (`Blanc/Composition/ConsolidationRequestPublicHistory.lean:142`), with conclusion `Blanc.Composition.ConsolidationRequestPublic.Fifo` (`Blanc/Composition/ConsolidationRequestPublicObservers.lean:114`) over `Blanc.Composition.ConsolidationRequestPublic.submissions` (`Blanc/Composition/ConsolidationRequestPublicObservers.lean:61`), `Blanc.Composition.ConsolidationRequestPublic.emissions` (`Blanc/Composition/ConsolidationRequestPublicObservers.lean:74`) and `Blanc.Composition.ConsolidationRequestPublic.remainingQueue` (`Blanc/Composition/ConsolidationRequestPublicObservers.lean:55`); via `Blanc.Lift.ConsolidationRequest.history_delivered` (`Blanc/Lift/ConsolidationRequest/Chain.lean:112`) | Checkpoint-rooted history / FIFO | INIT: `CheckpointStart` at the first state (canonical code; slots 0 to 3 hold the inhibitor, 0, 0, 0; no code at SYSTEM_ADDRESS). CODE: every block at a covered fork. ENV: `HistoryClean` (no kept block recovers SYSTEM_ADDRESS as a sender or a 7702 authority, and none creates it). **Scope: at most 2^253 committed submissions** | The empty history is included. The covered-fork premise is stated because the user frames are proved at the covered forks only; a kept history may otherwise contain Amsterdam blocks (Section 7 item 57). No hash or per-frame premise; historical inclusion is not authenticated |
| **C4 at mainnet.** For every kept mainnet history after the observed pre-Prague checkpoint 22,431,083, every committed submission is, in order, either a record the blocks published or an entry still in the final stored queue | `Blanc.Composition.ConsolidationRequestPublic.history_fifo_mainnet` (`Blanc/Composition/ConsolidationRequestPublicHistory.lean:229`), with conclusion `Blanc.Composition.ConsolidationRequestPublic.Fifo` (`Blanc/Composition/ConsolidationRequestPublicObservers.lean:114`); via `Blanc.Composition.ConsolidationRequestPublic.history_fifo` (`Blanc/Composition/ConsolidationRequestPublicHistory.lean:142`) and `Blanc.Composition.ConsolidationRequestPublic.mainnet_covered` (`Blanc/Composition/ConsolidationRequestPublicHistory.lean:213`) | Observation-rooted history / FIFO, at mainnet | The observation `ConsolidationCheckpointObservation` at the checkpoint: its last header (number 22,431,083, hash 0x28fb2c1d988435955e569451c6ad772f7fb5e61cddd7463c7b60e933ed5ff237, state root 0xab350e0fe349aef68947ede26295f8946c34ce3af5e3ec76f4b26ddeef29c0e3); the canonical code at the predeploy; slots 0 to 3 holding the inhibitor, 0, 0, 0; empty code at SYSTEM_ADDRESS. ENV: `HistoryClean`. **Scope: at most 2^253 committed submissions** | The covered-fork premise is discharged: mainnet's schedule names no Amsterdam activation. The observed values come from public JSON-RPC operators; Lean does not authenticate them against consensus or a state trie (Section 7 item 60) |

**A submission works**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| **C5a. A submission is queued.** Every successful fresh 96-byte frame from a user leaves the stored queue as it was with one record appended: the caller's 20 bytes, then the 96 submitted bytes | `Blanc.Composition.ConsolidationRequestPublic.submission_queued` (`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean:477`), with conclusion `Blanc.Composition.ConsolidationRequestPublic.SubmissionQueued` (`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean:299`) over `Blanc.Composition.ConsolidationRequestPublic.storedQueue` (`Blanc/Composition/ConsolidationRequestPublicObservers.lean:51`) | Frame / refinement | CODE; covered fork; fresh entry; caller not SYSTEM_ADDRESS; 96-byte calldata; ARITH: head ≤ tail < 2^253 | The statement ranges over every successful execution, whatever fee the call paid. It says nothing about whether a successful execution exists; C5b does. On a kept history from the checkpoint, `Blanc.Composition.ConsolidationRequestPublic.history_pointers` (`Blanc/Composition/ConsolidationRequestPublicHistory.lean:181`) gives head at most tail and tail at most the submission count |
| **C5b. A paid submission succeeds at an exact charge.** A fresh non-static frame carrying 96 bytes from a user, with slot 0 off the inhibitor and value at least the quoted fee, started with `submissionCharge` plus a residual G greater than the 2,300-gas stipend, has a successful execution that ends with exactly G left | `Blanc.Composition.ConsolidationRequestPublic.submission_live` (`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean:532`), with conclusion `Blanc.Composition.ConsolidationRequestPublic.SubmissionLive` (`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean:527`) and the charge `Blanc.Composition.ConsolidationRequestPublic.submissionCharge` (`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean:511`): 269 + 87·k + the storage reads + the six stores (count, four record words, tail), where k is the fee loop's iteration count `Blanc.Composition.ConsolidationRequestPublic.quotedIterations` (`Blanc/Composition/ConsolidationRequestPublicObservers.lean:41`); via `Blanc.Lift.ConsolidationRequest.exec_submission_exact` (`Blanc/Lift/ConsolidationRequest/Frames.lean:299`) | Frame / live, exact gas | CODE; covered fork; caller not SYSTEM_ADDRESS; 96-byte calldata; non-static; slot 0 off the inhibitor; value at least the quoted fee | The charge is the gas consumed, not a proved minimum. The frame starts with an empty stack and empty memory. Frame level only: no history form is stated. At a large enough excess the quoted fee exceeds every value a call can carry, so the payment premise cannot hold there |

**No transaction-level liveness**: sender funding, intrinsic gas, block room and call forwarding are
not covered.

**Non-claims.** Consensus-layer processing, including validator authorization: the emitted source
address is the immediate caller, and whether a request may act on the named validators is decided
there; economic soundness of the parameters; the failure outcome of a rejected call and its gas;
a delivery bound (how many blocks a queued record waits); the contract's balance; state growth
(dequeued queue slots are not cleared, and the stored queue ignores them); deployment of the
contract; historical inclusion of the checkpoint; Amsterdam; anything beyond 2^253 committed
submissions. Rolled-back frames are not counted: the submissions are the frames a history commits,
and a frame rolled back by its own or an ancestor's failure is not among them.

## Artifacts

| Runtime | Address | Bytes | SHA-256 | Definition |
|---|---|---:|---|---|
| EIP-7251 consolidation requests | 0x0000BBdDc7CE488642fb579F8B00f3a590007251 | 414 | 99e3d84dc4a4440c78a64619a2b451c08654cc83b44441585cb6db159478d661 | `Blanc.consolidationRequestCode` (`Blanc/SystemContracts.lean:92`) |

The bytes are a canonical system contract of the shared configured-execution machinery (Section 2
of the shared map). They are not a lifted input: the frame statements walk the literal bytes of
the definition. The frame and system-call statements take the code at the predeploy as a CODE
premise. The mainnet FIFO statement takes it from the checkpoint observation, whose `eth_getCode`
read returned these bytes. That read is recorded, not re-fetched by any gate.

## Summary matrix

| | M1 | M2 | M3 | M4 | M5 | M6 | M7 | M8 |
|---|---|---|---|---|---|---|---|---|
| EIP-7251 | ✓ | ✓ [n] | ✓ | ✓ none | ✗ [o] | ✓ [p] | ✗ | ✓ |

[n] Up to 2^253 committed submissions after the checkpoint; the fee is the bytes' quoted fee, which
departs from the EIP's fake_exponential at excess 2893 (Section 7 item 59).

[o] The initial words are not derived from a deployment. The mainnet form takes them from an
observation at the pre-Prague checkpoint 22,431,083 (Section 7 item 60); the checkpoint form takes
them as `CheckpointStart`.

[p] Frame level, at every state with slot 0 off the inhibitor, so at every such reachable state; no
history form is stated.

## Disclosures and limits

56. **C2's dequeue output is stated only when head ≤ tail.** The bytes subtract the queue pointers
    as 256-bit words; the stored queue subtracts them as natural numbers, floored at 0. With head
    above tail the two disagree: with slot 2 holding 1 and slot 3 holding 0 the call drains two
    records (232 bytes) while the stored queue is empty. C2's dequeue arm therefore states the
    output under head ≤ tail, and its storage field with no premise. C2 ranges over every storage,
    including storage with head above tail.

57. **The checkpoint FIFO form takes covered forks for every block.** A kept history may contain
    Amsterdam blocks; the user frames of these bytes are proved at the covered forks only. The
    mainnet form discharges the premise, since mainnet's schedule names no Amsterdam activation.
    **Amsterdam is not covered by these statements.**

58. **C1b needs the tail below 2^253.** Records take four slots each from slot 4. With the tail at
    or above 2^253 a record key wraps onto slots 0 to 3, and the bookkeeping fails. The FIFO
    statements bound the committed submissions by 2^253 for the same reason. The bound is half of
    EIP-7002's 2^254, whose records take three slots.

59. **The fee departs from the EIP at excess 2893.** The bytes compute fake_exponential with 256-bit
    intermediates. The 87-byte fee windows differ exactly at index 41 (0x9a vs 0xf4, pc 0x43), so the departure
    sits at the same excess. C3c states it at the function level. For EIP-7002 a synthetic history
    that reaches the departure is proved (see the EIP-7002 file, Section 7 item 16); for these bytes
    no such history is proved, and a witness reaching excess 2893 within one block would need about 2,894 submissions.
    The divergence is between the bytes and the EIP's pseudocode, not a practical attack.

60. **The mainnet root is an observation, not a deployment.** C4 at mainnet is rooted at seven
    observed fields at block 22,431,083: the last header's number, hash and state root, the code at
    the predeploy, slots 0 to 3, and empty code at SYSTEM_ADDRESS. The observed values come from
    public JSON-RPC operators and are recorded, not re-fetched by any gate; Lean does not
    authenticate them against consensus or a state trie. The deployment transaction of the
    contract is not modelled.

61. **SYSTEM_ADDRESS emptiness is a premise, not shown load-bearing here.** `CheckpointStart` and the
    observation both require empty code at SYSTEM_ADDRESS, so only the block's own call can dequeue.
    No closed counterexample shows that the FIFO law fails without it for these bytes. EIP-7002's
    file proves that counterexample for its bytes.

62. **No transaction-level liveness.** C5b is a frame statement. Sender funding, intrinsic gas, block
    room and call forwarding are not covered.

## Named premises and definitions

| Name | Declaration | Role |
|---|---|---|
| `CheckpointStart` | `Blanc.Composition.ConsolidationRequestPublic.CheckpointStart` (`Blanc/Composition/ConsolidationRequestPublicObservers.lean:77`) | the predeploy at its start in a state: canonical code, slots 0 to 3 at the inhibitor, 0, 0, 0, no code at SYSTEM_ADDRESS |
| `ConsolidationCheckpointObservation` | `Blanc.Composition.ConsolidationRequestPublic.ConsolidationCheckpointObservation` (`Blanc/Composition/ConsolidationRequestPublicObservers.lean:95`) | the seven fields read at mainnet block 22,431,083 |
| `HistoryClean` | `Blanc.HistoryClean` (`Blanc/ExecutionKeptClean.lean:18`) | no kept block recovers SYSTEM_ADDRESS as a sender or a 7702 authority, and none creates it |
| `KeptHistory` | `Blanc.KeptHistory` (`Blanc/ExecutionKeptChain.lean:1814`) | the blocks from one chain to another, each a successful transition at a covered fork or Amsterdam, with the frames each block commits |
| `FreshEntry` | `Blanc.Composition.ConsolidationRequestPublic.FreshEntry` (`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean:199`) | a fresh frame: empty stack, word-aligned well-formed memory, calldata shorter than 2^256 bytes |
| `FreshEntry.of_exec` | `Blanc.Composition.ConsolidationRequestPublic.FreshEntry.of_exec` (`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean:210`) | every frame the model opens is a fresh entry given its calldata length |
| `storedQueue` | `Blanc.Composition.ConsolidationRequestPublic.storedQueue` (`Blanc/Composition/ConsolidationRequestPublicObservers.lean:51`) | the queue as stored: the entries from the head word (slot 2) up to the tail word (slot 3), each read from four slots |
| `quotedFee` | `Blanc.Composition.ConsolidationRequestPublic.quotedFee` (`Blanc/Composition/ConsolidationRequestPublicObservers.lean:36`) | the fee the bytes quote at an excess |
| `SpecFee` | `Blanc.Composition.ConsolidationRequestPublic.SpecFee` (`Blanc/Composition/ConsolidationRequestPublicObservers.lean:33`) | the EIP's fee, fake_exponential(1, excess, 17) |
| `records116` | `Blanc.Composition.ConsolidationRequestPublic.records116` (`Blanc/Composition/ConsolidationRequestPublicObservers.lean:66`) | request bytes cut into 116-byte records, a short tail kept |
| `blockConsolidations` | `Blanc.Composition.ConsolidationRequestPublic.blockConsolidations` (`Blanc/Composition/ConsolidationRequestPublicObservers.lean:70`) | the type-2 payloads of one block's actual request list, in order |
| `history_pointers` | `Blanc.Composition.ConsolidationRequestPublic.history_pointers` (`Blanc/Composition/ConsolidationRequestPublicHistory.lean:181`) | at a history end, head is at most tail and tail is at most the submission count |

## Checking this document

The 9 featured statements and C1b are pinned by
exact statement in `scripts/ClaimCheck.lean`, with 24 definitions they are stated through pinned by unfolding and 5 record types pinned field by field.

## See also

- [EIP-7002 withdrawal requests: Section 7 item 16](withdrawal-request.md#disclosures-and-limits)
