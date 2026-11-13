# Protocol-contract corpus

## Matrix

| Row | D | R | H | W | C | B |
|---|---|---|---|---|---|---|
| S1 | [Settled deposit-contract frames emit only valid 576-byte deposit logs, making block deposit parsing total.](#d-s1) | [The covered-fork beacon-roots system call succeeds from arbitrary storage within 44,251 regular gas with exact ring writes.](#r-s1) | [The covered-fork history-storage system call succeeds from arbitrary storage within 22,143 regular gas with exact slot writes.](#h-s1) | [The covered-fork withdrawal-request checked system call succeeds from arbitrary storage within 210,000 gas.](#w-s1) | [The covered-fork consolidation-request checked system call succeeds from arbitrary storage within 114,177 gas.](#c-s1) | [Both builder-request contracts complete their Amsterdam system calls with exact post-state within 888,000 and 161,000 regular gas.](#b-s1) |
| S2 | [Every settled frame at canonical deposit bytes in a kept history is deposit, root view, count view, or ERC-165.](#d-s2) | [Every settled beacon-roots frame on covered forks is either the system ring write or a 32-byte timestamp read.](#r-s2) | [Every settled history-storage frame on covered forks is either the system ring write or an in-window block-hash read.](#h-s2) | [Every successful fresh canonical withdrawal-request frame is a system dequeue, a 56-byte submission, or a fee-getter read.](#w-s2) | [Every settled consolidation-request frame in a kept history is a system dequeue, a 96-byte submission, or a fee read.](#c-s2) | [Every settled frame on both builder contracts is system empty, system inhibitor latch, submission, or fee read.](#b-s2) |
| S3 | [Configured deposit histories maintain exact deposit count, 32-level SHA-256 Merkle root, and leaf recurrence.](#d-s3) | [Clean covered-fork histories determine every beacon-roots ring slot as the exact fold of block-entry writes.](#r-s3) | [Clean covered-fork histories determine every history-storage slot as the exact fold of parent-hash writes.](#h-s3) | [Admitted deployment histories determine withdrawal word bookkeeping, FIFO queue records, and block publication.](#w-s3) | [Clean checkpoint histories satisfy the consolidation FIFO law equating submissions with published records plus remaining queue.](#c-s3) | [Clean Amsterdam histories determine exact queue storage and request-boundary publication for both builder contracts.](#b-s3) |
| S4 | [Modeled deployment at block 11,052,984 and historical seam anchors establish SolInv and empty initial history.](#d-s4) | [The observed block 22,431,083 checkpoint establishes canonical beacon-roots code and empty SYSTEM_ADDRESS code.](#r-s4) | [The observed block 22,431,083 checkpoint establishes canonical history-storage code and empty SYSTEM_ADDRESS code.](#h-s4) | [Conditional observed deployment traces from block 21,881,389 to 22,431,083 establish canonical code and initial words.](#w-s4) | [The observed block 22,431,083 checkpoint roots the conditional mainnet consolidation FIFO and storage history.](#c-s4) | [The adopted block 26,391,669 checkpoint establishes both builder bytecodes, whole initial storages, and clean SYSTEM.](#b-s4) |
| S5 | N/A (fee row) | N/A (fee row) | N/A (fee row) | [Withdrawal word fee equals fake_exponential iff NatFeeDomain holds, with first underpayment at excess 2,893.](#w-s5) | [Consolidation word fee equals fake_exponential iff NoWrapDomain holds, agreeing through 2,892 and diverging at 2,893.](#c-s5) | [Both builder contracts share the NoWrapDomain/2,893 word-fee boundary and expose a reversible SYSTEM inhibitor latch.](#b-s5) |
| S6 | [Deposit contract balance never decreases and retains every committed deposit payment at exact gwei-to-wei scaling.](#d-s6) | [Beacon-roots contract balance never falls and accumulates all value sent in kept frames across covered-fork histories.](#r-s6) | [History-storage contract balance never falls and accumulates all value sent in kept frames across covered-fork histories.](#h-s6) | [Every configured mainnet suffix retains the checkpoint balance plus all committed withdrawal submission payments.](#w-s6) | [Kept covered-fork histories retain starting balance plus committed consolidation submission and kept-frame values.](#c-s6) | [Both builder contracts retain starting balance plus all committed submission payments across Amsterdam histories.](#b-s6) |
| S7 | [Valid 416-byte deposit frames with at least 1 ETH at exact gwei multiples and count below 2^32-1 succeed at exact gas.](#d-s7) | [Fresh 32-byte beacon-roots reads of a matching nonzero timestamp succeed at exact 120 plus two-SLOAD gas.](#r-s7) | [Fresh 32-byte history-storage reads within the 8,191-block window succeed at exact 125 plus SLOAD gas.](#h-s7) | [Canonical withdrawal submission and fee-getter frames succeed with exact gas under their actual word-fee guards.](#w-s7) | [Canonical consolidation submission and fee-getter frames succeed with exact gas under their actual word-fee guards.](#c-s7) | [Both builder contracts accept valid submissions and serve fee reads at exact regular gas under actual word-fee guards.](#b-s7) |
| S8 | [Every committed deposit frame event becomes an exact same-block deposit request record in emission order.](#d-s8) | [Beacon-roots ring entries persist across timestamp-noncongruent suffixes and across fewer than 8,191 affine slots.](#r-s8) | [History-storage retains exact parent hashes for 8,191 blocks, rejects endpoints, and preserves unwritten slots.](#h-s8) | [An admitted mainnet extension delivers withdrawal queue position q in block q/16 at record index q%16.](#w-s8) | [A clean covered-fork history delivers consolidation queue position q in block j + q/2 at record index q%2.](#c-s8) | [History-wide multi-user fee budgets bound both builder queues at every boundary and yield conditional q/64 and q/16 delivery.](#b-s8) |
| S9 | [Valid joint chains deliver same-block deposits and classify post-cutover queued fate and conservation under real BLS.](#d-s9) | [Valid joint steps store the consensus parent_root in beacon-roots and match SSZ parent headers under the slot guard.](#r-s9) | [Contiguous kept histories return the exact ancestor execution block hash for every retained height in the 8,191-block window.](#h-s9) | [Valid joint runs preserve withdrawal authorization, occurrence fate, retained fee budget, and payout crediting laws.](#w-s9) | [Valid joint runs enforce consolidation caller/credential authorization, unique occurrence fate, and balance conservation.](#c-s9) | [Focused Gloas joint theorems prove builder fate, registration/exit authorization, unique resolution, and at-most-once debit.](#b-s9) |
| S10 | [Settled deposit frames at Amsterdam emit only valid 576-byte deposit logs, discharging request-pass parse premises.](#d-s10) | [The Amsterdam beacon-roots system call succeeds from arbitrary storage within 30,000 regular gas with exact ring writes.](#r-s10) | [The Amsterdam history-storage system call succeeds from arbitrary storage within 15,000 regular gas with exact writes.](#h-s10) | [The Amsterdam withdrawal system call succeeds within 163,000 regular gas and composes in the four-contract request phase.](#w-s10) | [The Amsterdam consolidation system call succeeds within 75,000 regular gas and composes in the four-contract request phase.](#c-s10) | [Both builder contracts succeed within 888,000 and 161,000 regular gas and compose in the Amsterdam request-phase pass.](#b-s10) |

## D-S1

### Premises

Assumes a covered fork (Prague, Osaka, BPO1, or BPO2), canonical deposit runtime bytes at 0x00000000219ab540356cBB839Cbe05303d7705Fa, a receipt-producing execution trace with complete transaction receipts, and attribution of every deposit-topic log at that address to settled frames of the canonical code.

### Non-claims

Does not claim parsing totality when foreign or unverified runtime bytes inhabit the deposit address; the paired short-log control proves parseDepositRequests fails if a 1-byte log with the deposit address and topic appears in receipts. Does not assert consensus validator crediting.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| log-shape, parse | `Blanc.Composition.DepositParse.d_s1` (`Blanc/Composition/DepositParse.lean:65`) | `thm:Blanc.Composition.DepositParse.d_s1` |

## R-S1

### Premises

Assumes a covered fork (Prague, Osaka, BPO1, or BPO2) and canonical EIP-4788 bytecode installed at 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02, with arbitrary initial contract storage.

### Non-claims

Applies to the protocol system call from SYSTEM_ADDRESS; zero parentBeaconBlockRoot performs no storage write. Does not classify user-originated calls or Amsterdam state gas.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Corpus.Proofs.R.r_s1` (`Blanc/Composition/Corpus/Proofs/RingTotality.lean:23`) | `thm:Blanc.Corpus.Proofs.R.r_s1` |

## H-S1

### Premises

Assumes a covered fork (Prague, Osaka, BPO1, or BPO2), canonical EIP-2935 bytecode installed at 0x0000F90827F1C53a10cb7A02335B175320002935, blockHashes.getLast? = some lastHash, and arbitrary initial contract storage.

### Non-claims

Applies to the protocol system call from SYSTEM_ADDRESS; at block number zero `blockNumber - 1` wraps modulo 2^256 in the bytecode, writing `lastHash` to slot `2^256 - 1 mod 8,191`. Does not classify user-originated reads or Amsterdam state gas.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Corpus.Proofs.H.h_s1` (`Blanc/Composition/Corpus/Proofs/RingTotality.lean:85`) | `thm:Blanc.Corpus.Proofs.H.h_s1` |

## W-S1

### Premises

Assumes a covered fork (Prague, Osaka, BPO1, or BPO2) and canonical EIP-7002 bytecode installed at 0x00000961Ef480Eb55e80D19ad83579A64c007002, with arbitrary initial contract storage.

### Non-claims

Bounds checked system-call gas without stating the post-state directly in the headline existential (`checked_system_totality` states the exact post-state in the unit layer).

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Lift.WithdrawalRequest.system_call_succeeds` (`Blanc/Lift/WithdrawalRequest/HeadlineSystem.lean:28`) | `thm:Blanc.Lift.WithdrawalRequest.system_call_succeeds` |

## C-S1

### Premises

Assumes a covered fork (Prague, Osaka, BPO1, or BPO2) and canonical EIP-7251 bytecode installed at 0x0000BBdDc7CE488642fb579F8B00f3a590007251, with arbitrary initial contract storage.

### Non-claims

Bounds checked system-call gas without stating the post-state in the headline existential (stated separately by `system_call_bookkept` / `ConsolidationRequest.system_call_ok`); does not assert consensus consolidation processing.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Composition.ConsolidationRequestPublic.system_call_succeeds` (`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean:41`) | `thm:Blanc.Composition.ConsolidationRequestPublic.system_call_succeeds` |

## B-S1

### Premises

Assumes the Amsterdam fork and canonical EIP-8282 deposit and exit bytecodes installed at their respective predeploys, with arbitrary initial storage on each contract.

### Non-claims

Bounds regular execution gas only and excludes Amsterdam state gas; does not assert consensus request processing or user-frame classification.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| deposit | `Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s1_deposit` (`Blanc/Composition/Corpus/Proofs/MatrixComponentPins.lean:126`) | `thm:Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s1_deposit` |
| exit | `Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s1_exit` (`Blanc/Composition/Corpus/Proofs/MatrixComponentPins.lean:150`) | `thm:Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s1_exit` |

## D-S2

### Premises

Assumes a kept covered-fork execution history from a state establishing the deposit Merkle accumulator invariant (discharged via D-S3 and D-S4 rather than assumed per frame) with canonical deposit bytecode retained at the deposit address.

### Non-claims

Classifies settled frames of the canonical deposit runtime only; reverted frames roll back their local effects, and non-matching selectors or malformed calldata revert.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| deposit, root-view, count-view, erc165 | `Blanc.Composition.DepositClassified.d_s2` (`Blanc/Composition/DepositClassified.lean:132`) | `thm:Blanc.Composition.DepositClassified.d_s2` |

## R-S2

### Premises

Assumes a covered fork, canonical EIP-4788 bytecode at the predeploy target, empty initial stack, word-aligned well-formed initial memory, and calldata length below 2^256.

### Non-claims

User-originated ring reads do not reject nonzero call value in the bytecode, so incoming ETH on a successful read is retained by the predeploy rather than reverted.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Corpus.Proofs.BeaconRoots.r_s2` (`Blanc/Corpus/Proofs/BeaconRootsClassification.lean:10`) | `thm:Blanc.Corpus.Proofs.BeaconRoots.r_s2` |

## H-S2

### Premises

Assumes a covered fork, canonical EIP-2935 bytecode at the predeploy target, empty initial stack, word-aligned well-formed initial memory, and calldata length below 2^256.

### Non-claims

User-originated reads do not reject nonzero call value in the bytecode, so incoming ETH on a successful read is retained by the predeploy rather than reverted.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Corpus.Proofs.HistoryStorage.h_s2` (`Blanc/Corpus/Proofs/HistoryStorage.lean:13`) | `thm:Blanc.Corpus.Proofs.HistoryStorage.h_s2` |

## W-S2

### Premises

Assumes a covered fork, canonical EIP-7002 bytecode, empty initial stack, word-aligned well-formed initial memory, and calldata length below 2^256.

### Non-claims

Stated at the established fresh-frame entry contract for EIP-7002; incoming call value is credited by EVM message entry prior to frame body execution.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Lift.WithdrawalRequest.exec_frame_effect` (`Blanc/Lift/WithdrawalRequest/FrameEffects.lean:32`) | `thm:Blanc.Lift.WithdrawalRequest.exec_frame_effect` |

## C-S2

### Premises

Assumes a kept history on covered forks (Prague, Osaka, BPO1, or BPO2) with canonical EIP-7251 bytecode at the predeploy address.

### Non-claims

System dequeue output uses unconditional word subtraction even if synthetic storage has head above tail; incoming call value is credited before frame body execution.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| all-success-arms, unconditional-output, exact-effects | `Blanc.Corpus.Proofs.Consolidation.c_s2` (`Blanc/Composition/Corpus/Proofs/ConsolidationExecution.lean:18`) | `thm:Blanc.Corpus.Proofs.Consolidation.c_s2` |

## B-S2

### Premises

Assumes an Amsterdam kept history with canonical EIP-8282 deposit and exit bytecodes at their predeploys, under unrestricted Form B without assuming HistoryClean or empty SYSTEM_ADDRESS code.

### Non-claims

Includes the nonzero-calldata SYSTEM_ADDRESS arm writing B256.max to slot 0 and user-originated SYSTEM_ADDRESS empty-calldata dequeues when SYSTEM_ADDRESS is unguarded; clean histories exclude those paths via B-S3.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| deposit-system-empty, deposit-system-latch, deposit-submission, deposit-fee-read | `Blanc.Composition.BuilderRequestClassification.b_s2_deposit` (`Blanc/Composition/BuilderRequestClassification.lean:139`) | `thm:Blanc.Composition.BuilderRequestClassification.b_s2_deposit` |
| exit-system-empty, exit-system-latch, exit-submission, exit-fee-read | `Blanc.Composition.BuilderRequestClassification.b_s2_exit` (`Blanc/Composition/BuilderRequestClassification.lean:147`) | `thm:Blanc.Composition.BuilderRequestClassification.b_s2_exit` |

## D-S3

### Premises

Assumes a configured execution history from canonical deposit deployment or a valid SolInv checkpoint, canonical SHA-256 precompile availability (empty code and no authority or CREATE at address 0x02), and no authority or CREATE collisions at system contract addresses.

### Non-claims

Tracks committed deposit leaves and stored Merkle branch words; does not authenticate external RPC responses or assert consensus deposit-queue consumption.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Lift.BeaconDeposit.beacon_deposits` (`Blanc/Lift/BeaconDeposit/HistDeployment.lean:164`) | `thm:Blanc.Lift.BeaconDeposit.beacon_deposits` |

## R-S3

### Premises

Assumes a kept covered-fork history with canonical EIP-4788 bytecode, empty code at SYSTEM_ADDRESS, and no transaction sender, EIP-7702 authority, or CREATE targeting SYSTEM_ADDRESS.

### Non-claims

Without SYSTEM_ADDRESS cleanliness, a coded SYSTEM_ADDRESS account can spoof the system caller and overwrite ring slots mid-block, as demonstrated by the paired negative control.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Corpus.Proofs.RingHistory.R.r_s3` (`Blanc/Composition/Corpus/Proofs/RingHistory.lean:150`) | `thm:Blanc.Corpus.Proofs.RingHistory.R.r_s3` |

## H-S3

### Premises

Assumes a kept covered-fork history with canonical EIP-2935 bytecode, empty code at SYSTEM_ADDRESS, and no transaction sender, EIP-7702 authority, or CREATE targeting SYSTEM_ADDRESS.

### Non-claims

Without SYSTEM_ADDRESS cleanliness, a coded SYSTEM_ADDRESS account can spoof the system caller and overwrite stored block hashes mid-block, as demonstrated by the paired negative control.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Corpus.Proofs.RingHistory.H.h_s3` (`Blanc/Composition/Corpus/Proofs/RingHistory.lean:246`) | `thm:Blanc.Corpus.Proofs.RingHistory.H.h_s3` |

## W-S3

### Premises

Assumes canonical Cancun deployment admission, configured covered-fork history, canonical sibling system code at checkpoint, SYSTEM_ADDRESS sender/authority/CREATE exclusions, and at most 2^254 committed submissions.

### Non-claims

Does not clear stale storage outside the active head-to-tail window or cover occurrence counts above 2^254; checkpoint SYSTEM_ADDRESS emptiness is load-bearing per the proved drain control.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Lift.WithdrawalRequest.block_word_fifo` (`Blanc/Lift/WithdrawalRequest/WordFifo.lean:635`) | `thm:Blanc.Lift.WithdrawalRequest.block_word_fifo` |

## C-S3

### Premises

Assumes a kept covered-fork history from CheckpointStart, HistoryClean exclusions on SYSTEM_ADDRESS, and at most 2^253 committed consolidation submissions.

### Non-claims

`Fifo` characterizes `submissions = emissions ++ remainingQueue` without asserting slots 0 to 3 or non-queue storage slots outside `remainingQueue`; the paired drain control shows a coded SYSTEM_ADDRESS caller drains queued requests before block publication.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Composition.ConsolidationRequestPublic.history_fifo` (`Blanc/Composition/ConsolidationRequestPublicHistory.lean:139`) | `thm:Blanc.Composition.ConsolidationRequestPublic.history_fifo` |

## B-S3

### Premises

Assumes an Amsterdam kept history from initial builder storage, canonical EIP-8282 deposit and exit bytecodes, SYSTEM_ADDRESS cleanliness, and bounded submission counts.

### Non-claims

Requires SYSTEM_ADDRESS cleanliness to exclude user-triggered dequeues and nonzero-calldata inhibitor writes; does not assert consensus execution of published requests.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| deposit | `Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s3_deposit` (`Blanc/Composition/Corpus/Proofs/MatrixComponentPins.lean:174`) | `thm:Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s3_deposit` |
| exit | `Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s3_exit` (`Blanc/Composition/Corpus/Proofs/MatrixComponentPins.lean:189`) | `thm:Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s3_exit` |

## D-S4

### Premises

Assumes a mainnet-configured block trace at block 11,052,984 with the canonical creation transaction at index 2 and successful receipt, empty deposit logs in the creation block, historical seam anchors, and address-0x02/system-address collision exclusions.

### Non-claims

Conditional modeled execution-history bridge: Lean does not authenticate external RPC headers or Merkle-Patricia receipt/state proofs against canonical mainnet finality.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Lift.BeaconDeposit.BeaconDeploymentTo.solInv` (`Blanc/Lift/BeaconDeposit/HistDeployment.lean:121`) | `thm:Blanc.Lift.BeaconDeposit.BeaconDeploymentTo.solInv` |

## R-S4

### Premises

Assumes a RingCheckpointObservation at mainnet block 22,431,083 recording header hash, state root, canonical EIP-4788 runtime bytes, and empty code at SYSTEM_ADDRESS, followed by a clean kept covered-fork history.

### Non-claims

Observed-checkpoint route rather than a deployment-transaction trace; RPC header and account fields are unauthenticated model inputs and assert no initial ring-slot zeroes.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Corpus.Proofs.RingRoots.r_s4` (`Blanc/Composition/Corpus/Proofs/RingRoots.lean:10`) | `thm:Blanc.Corpus.Proofs.RingRoots.r_s4` |

## H-S4

### Premises

Assumes a RingCheckpointObservation at mainnet block 22,431,083 recording header hash, state root, canonical EIP-2935 runtime bytes, and empty code at SYSTEM_ADDRESS, followed by a clean kept covered-fork history.

### Non-claims

Observed-checkpoint route rather than a deployment-transaction trace; RPC header and account fields are unauthenticated model inputs and assert no pre-checkpoint ring contents.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Corpus.Proofs.RingRoots.h_s4` (`Blanc/Composition/Corpus/Proofs/RingRoots.lean:15`) | `thm:Blanc.Corpus.Proofs.RingRoots.h_s4` |

## W-S4

### Premises

Assumes mainnet historical traces across deployment block 21,881,389 (transaction split 0) to checkpoint block 22,431,083 satisfying WithdrawalDeploymentObservation and excluding CREATE targeting SYSTEM_ADDRESS.

### Non-claims

Conditional modeled bridge: external header hashes, state roots, and receipt fields are not cryptographically authenticated inside Lean, and canonical chain inclusion is not proved.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Lift.WithdrawalRequest.deploy_mainnet` (`Blanc/Lift/WithdrawalRequest/HeadlineHistory.lean:208`) | `thm:Blanc.Lift.WithdrawalRequest.deploy_mainnet` |

## C-S4

### Premises

Assumes a mainnet kept history from ConsolidationCheckpointObservation at block 22,431,083 (hash 0x28fb2c1d988435955e569451c6ad772f7fb5e61cddd7463c7b60e933ed5ff237) with canonical EIP-7251 code, inhibitor excess, zero count/head/tail, HistoryClean, and 2^253 submission cap.

### Non-claims

Observed-checkpoint route rather than a creation-transaction proof; RPC account and header fields are unauthenticated model inputs and assert nothing outside slots 0 through 3 at start.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Composition.ConsolidationRequestPublic.history_fifo_mainnet` (`Blanc/Composition/ConsolidationRequestPublicHistory.lean:224`) | `thm:Blanc.Composition.ConsolidationRequestPublic.history_fifo_mainnet` |

## B-S4

### Premises

Assumes the adopted BuilderCheckpointObservation at block 26,391,669 (timestamp 1794399959, hash 0x2410154b2609d8811f1acde0d30fea3815da62d90648e262fae38d2b5e4bfb6f, stateRoot 0xc4eeecdcc9b8002f80699481d73abb807d3d3ce1286b0430ba6e2a4f3f15d60e), whole-storage hash matches for empty deposit storage and slot0=max exit storage, and empty SYSTEM_ADDRESS code.

### Non-claims

Coverage starts at block 26,391,669 and excludes creation block 26,211,406 and the intervening segment; RPC account storageHash and header fields are trusted observations under hash-collision assumptions without in-Lean MPT path verification.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| deposit, exit | `Blanc.Composition.Corpus.Proofs.BuilderCheckpoint.b_s4` (`Blanc/Composition/Corpus/Proofs/BuilderCheckpoint.lean:108`) | `thm:Blanc.Composition.Corpus.Proofs.BuilderCheckpoint.b_s4` |

## W-S5

### Premises

Assumes execution of the bytecode's 256-bit word Taylor loop with factor 1 and denominator 17 from stored excess below B256.max.

### Non-claims

For excess 2,893 and higher wrap points, 256-bit numerator multiplication wraps modulo 2^256 and strictly underquotes the natural-number EIP-7002 fake_exponential specification; per-word characterization makes no reachability claim.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| fee-domain | `Blanc.Lift.WithdrawalRequest.fee_eq_spec_iff` (`Blanc/Lift/WithdrawalRequest/HeadlineFee.lean:46`) | `thm:Blanc.Lift.WithdrawalRequest.fee_eq_spec_iff` |
| first-divergence | `Blanc.Composition.Corpus.Proofs.MatrixComponentPins.w_s5_first_divergence` (`Blanc/Composition/Corpus/Proofs/MatrixComponentPins.lean:45`) | `thm:Blanc.Composition.Corpus.Proofs.MatrixComponentPins.w_s5_first_divergence` |

## C-S5

### Premises

Assumes execution of the EIP-7251 bytecode's 256-bit word Taylor recurrence with factor 1 and denominator 17 from stored excess below B256.max.

### Non-claims

At excess 2,893 the word Taylor loop wraps modulo 2^256 and charges strictly less than the natural-number EIP-7251 fake_exponential formula; per-storage characterization makes no mainnet reachability claim.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| fee-domain | `Blanc.Composition.Corpus.Proofs.MatrixComponentPins.c_s5_fee_domain` (`Blanc/Composition/Corpus/Proofs/MatrixComponentPins.lean:77`) | `thm:Blanc.Composition.Corpus.Proofs.MatrixComponentPins.c_s5_fee_domain` |
| first-divergence | `Blanc.Composition.ConsolidationRequestPublic.fee_lt_spec_2893` (`Blanc/Composition/ConsolidationRequestPublicHeadlines.lean:174`) | `thm:Blanc.Composition.ConsolidationRequestPublic.fee_lt_spec_2893` |

## B-S5

### Premises

Assumes canonical EIP-8282 deposit and exit bytecodes at Amsterdam; fee-domain theorems cover active excess words, and latch theorems cover nonzero-calldata SYSTEM_ADDRESS calls followed by ordinary empty-calldata system calls.

### Non-claims

Word-fee arithmetic wraps first at excess 2,893; contrary to permanent kill-switch prose, writing B256.max to slot 0 via nonzero-calldata SYSTEM_ADDRESS call is cleared by the next empty-calldata system call.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| deposit-fee-domain | `Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s5_deposit_fee_domain` (`Blanc/Composition/Corpus/Proofs/MatrixComponentPins.lean:236`) | `thm:Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s5_deposit_fee_domain` |
| exit-fee-domain | `Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s5_exit_fee_domain` (`Blanc/Composition/Corpus/Proofs/MatrixComponentPins.lean:257`) | `thm:Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s5_exit_fee_domain` |
| reversible-latch | `Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s5_reversible_latch` (`Blanc/Composition/Corpus/Proofs/MatrixComponentPins.lean:278`) | `thm:Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s5_reversible_latch` |

## D-S6

### Premises

Assumes a kept covered-fork execution history with canonical deposit runtime bytes at the deposit address and standard EVM balance-fit bounds on incoming root/credit values.

### Non-claims

Bounds balance from below (unsolicited SELFDESTRUCT or coinbase credits may raise it further); each committed deposit pays at least 1 ETH as an exact gwei multiple within uint64.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| balance, paid-amount | `Blanc.Composition.DepositValue.d_s6` (`Blanc/Composition/DepositValue.lean:133`) | `thm:Blanc.Composition.DepositValue.d_s6` |

## R-S6

### Premises

Assumes a kept covered-fork history with canonical EIP-4788 bytecode, no transaction sender at the predeploy, and non-wrapping root/credit balance bounds.

### Non-claims

The bytecode has no value-transferring opcode and accepts nonzero msg.value on user ring reads, so any ETH sent on a settled read remains permanently in the predeploy balance.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Corpus.Proofs.R.r_s6` (`Blanc/Composition/Corpus/Proofs/RingValue.lean:24`) | `thm:Blanc.Corpus.Proofs.R.r_s6` |

## H-S6

### Premises

Assumes a kept covered-fork history with canonical EIP-2935 bytecode, no transaction sender at the predeploy, and non-wrapping root/credit balance bounds.

### Non-claims

The bytecode has no value-transferring opcode and accepts nonzero msg.value on user block-hash reads, so any ETH sent on a settled read remains permanently in the predeploy balance.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Corpus.Proofs.H.h_s6` (`Blanc/Composition/Corpus/Proofs/RingValue.lean:39`) | `thm:Blanc.Corpus.Proofs.H.h_s6` |

## W-S6

### Premises

Assumes the W-S4 deployment-to-checkpoint bridge followed by a configured modern covered-fork execution history.

### Non-claims

Lower-bound inequality over settled submission frames (including nested committed calls); reverted frames and unauthenticated RPC checkpoint caveats from W-S4 remain.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Lift.WithdrawalRequest.history_payments_mainnet` (`Blanc/Lift/WithdrawalRequest/HeadlineHistory.lean:226`) | `thm:Blanc.Lift.WithdrawalRequest.history_payments_mainnet` |

## C-S6

### Premises

Assumes a kept covered-fork history with canonical EIP-7251 bytecode, no transaction sender at the predeploy, HistoryRootsFit, and HistoryCreditsFit.

### Non-claims

Lower-bound inequality excluding reverted or ancestor-reverted frames; arithmetic fit premises rule out synthetic 256-bit account-balance wrap.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Corpus.Proofs.Consolidation.c_s6` (`Blanc/Composition/Corpus/Proofs/ConsolidationExecution.lean:54`) | `thm:Blanc.Corpus.Proofs.Consolidation.c_s6` |

## B-S6

### Premises

Assumes an Amsterdam kept history with canonical EIP-8282 deposit and exit bytecodes and standard non-wrapping account-balance bounds.

### Non-claims

Lower-bound inequality on contract ETH balances; consensus builder-balance crediting or payment debiting is governed separately by B-S9.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| deposit | `Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s6_deposit` (`Blanc/Composition/Corpus/Proofs/MatrixComponentPins.lean:284`) | `thm:Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s6_deposit` |
| exit | `Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s6_exit` (`Blanc/Composition/Corpus/Proofs/MatrixComponentPins.lean:298`) | `thm:Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s6_exit` |

## D-S7

### Premises

Assumes a configured covered-fork history establishing SolInv, canonical deposit code, non-static frame entry, properly encoded 416-byte deposit calldata, value >= 1 ETH with value % 10^9 = 0 and value / 10^9 < 2^64, deposit count < 2^32 - 1, and sufficient frame gas.

### Non-claims

Stated at frame level over configured histories rather than outer transaction wrapper gas; does not validate BLS proof-of-possession validity, which consensus checks in D-S9.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Lift.BeaconDeposit.configuredHistory_deposit_live` (`Blanc/Lift/BeaconDeposit/Liveness.lean:20`) | `thm:Blanc.Lift.BeaconDeposit.configuredHistory_deposit_live` |

## R-S7

### Premises

Assumes a covered fork, canonical EIP-4788 bytecode, fresh frame entry (empty stack, word-aligned memory), non-SYSTEM caller, 32-byte nonzero timestamp calldata matching the stored timestamp slot (`read = some w`), and residual gas plus `120 + sloadGas(timeKey t) + sloadGas(rootKey t)`.

### Non-claims

Frame-level liveness for accepted reads only (whatever call value is supplied); miss/non-32-byte non-acceptance is proved by `R-S2` (`r_s2_control`) rather than `r_s7`, and transaction-level liveness is not claimed.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Corpus.Proofs.BeaconRoots.r_s7` (`Blanc/Corpus/Proofs/BeaconRootsFrames.lean:44`) | `thm:Blanc.Corpus.Proofs.BeaconRoots.r_s7` |

## H-S7

### Premises

Assumes a covered fork, canonical EIP-2935 bytecode, fresh frame entry (empty stack, word-aligned memory), non-SYSTEM caller, 32-byte block-number query in `[max(number - 8191, 0), number - 1]` (`InWindow`), and residual gas plus `125 + sloadGas(q mod 8191)`.

### Non-claims

Frame-level liveness for in-window reads only (whatever call value is supplied); out-of-window and non-32-byte non-acceptance are proved by `H-S2` (`h_s2_control`) rather than `h_s7`, and transaction-level liveness is not claimed.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Corpus.Proofs.HistoryStorage.h_s7` (`Blanc/Corpus/Proofs/HistoryStorage.lean:52`) | `thm:Blanc.Corpus.Proofs.HistoryStorage.h_s7` |

## W-S7

### Premises

Assumes a covered fork, canonical EIP-7002 bytecode, non-SYSTEM caller, active slot 0 (excess != B256.max), 56-byte dynamic frame with value >= actual WordFee for submissions, or empty zero-value calldata for the fee getter.

### Non-claims

Uses the bytecode's actual 256-bit word-fee threshold rather than natural-number SpecFee; frames with slot 0 equal to B256.max revert.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Composition.Corpus.Proofs.MatrixComponentPins.w_s7_headline` (`Blanc/Composition/Corpus/Proofs/MatrixComponentPins.lean:382`) | `thm:Blanc.Composition.Corpus.Proofs.MatrixComponentPins.w_s7_headline` |

## C-S7

### Premises

Assumes a covered fork, canonical EIP-7251 bytecode, non-SYSTEM caller, active slot 0 (excess != B256.max), 96-byte dynamic frame with value >= quotedFee for submissions, or empty zero-value calldata for the fee getter.

### Non-claims

Uses the bytecode's actual quoted word fee rather than natural-number SpecFee; frames arriving while slot 0 holds B256.max revert.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Composition.Corpus.Proofs.MatrixComponentPins.c_s7_headline` (`Blanc/Composition/Corpus/Proofs/MatrixComponentPins.lean:413`) | `thm:Blanc.Composition.Corpus.Proofs.MatrixComponentPins.c_s7_headline` |

## B-S7

### Premises

Assumes the Amsterdam fork, canonical EIP-8282 deposit and exit bytecodes, non-SYSTEM caller, active slot 0 (excess != B256.max), exact submission calldata length with value >= quoted word fee, or empty zero-value calldata for fee reads.

### Non-claims

States frame-level regular gas and excludes outer transaction intrinsic/state gas; active inhibitor latch (slot 0 = B256.max) causes user submissions and fee reads to revert.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| deposit-acceptance-gas | `Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s7_deposit_acceptance_gas` (`Blanc/Composition/Corpus/Proofs/MatrixComponentPins.lean:309`) | `thm:Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s7_deposit_acceptance_gas` |
| exit-acceptance-gas | `Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s7_exit_acceptance_gas` (`Blanc/Composition/Corpus/Proofs/MatrixComponentPins.lean:315`) | `thm:Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s7_exit_acceptance_gas` |

## D-S8

### Premises

Assumes a kept covered-fork history from valid deposit storage with canonical deposit code, complete block receipts, and attribution of deposit-address logs to canonical deposit frames.

### Non-claims

Covers the execution half only (same-block request extraction, record layout, order, and request-phase preservation); consensus deposit-queue scheduling and crediting belong to D-S9.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| record-shape, same-block-list, request-order, frame-phase | `Blanc.Composition.DepositRequests.d_s8` (`Blanc/Composition/DepositRequests.lean:72`) | `thm:Blanc.Composition.DepositRequests.d_s8` |

## R-S8

### Premises

The time statement assumes a clean kept covered-fork history where no later block timestamp is congruent modulo 8,191. The slot statement additionally assumes an affine slot clock timestamp = t0 + SECONDS_PER_SLOT * slot with positive SECONDS_PER_SLOT and slot gap < 8,191.

### Non-claims

Wall-clock or variable-interval schedules violate the slot bound if timestamps collide modulo 8,191; per adopted decision, slot wrap at delta = 8,191 is witnessed by the arithmetic `writeAll` mechanism control (`r_s8_slot_control`) rather than an 8,191-block closed `RingJoint` EVM trace.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| time | `Blanc.Composition.BeaconRootsRetention.r_s8_time` (`Blanc/Composition/BeaconRootsRetention.lean:7`) | `thm:Blanc.Composition.BeaconRootsRetention.r_s8_time` |
| slot | `Blanc.Composition.Corpus.Proofs.RingJointRetention.r_s8_slot` (`Blanc/Composition/Corpus/Proofs/RingJointRetention.lean:935`) | `thm:Blanc.Composition.Corpus.Proofs.RingJointRetention.r_s8_slot` |

## H-S8

### Premises

Assumes a clean kept covered-fork history with canonical EIP-2935 bytecode and contiguous block numbers across the suffix.

### Non-claims

Queries at the current block number or at number - 8192 revert; slots never reached by the block-number range retain their pre-history storage values.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| retention, endpoint-rejection, unwritten-slot | `Blanc.Composition.Corpus.Proofs.RingJointRetention.h_s8` (`Blanc/Composition/Corpus/Proofs/RingJointRetention.lean:1096`) | `thm:Blanc.Composition.Corpus.Proofs.RingJointRetention.h_s8` |

## W-S8

### Premises

Assumes the W-S4 deployment bridge, configured covered-fork histories to block B and depth q / 16 extension to D, SYSTEM_ADDRESS exclusions, sibling system code, and <= 2^254 submissions.

### Non-claims

Conditional on the existence of the admitted extension of depth q / 16; does not prove future block production, wall-clock latency, or consensus balance crediting.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Lift.WithdrawalRequest.history_delivery_mainnet` (`Blanc/Lift/WithdrawalRequest/HeadlineHistory.lean:242`) | `thm:Blanc.Lift.WithdrawalRequest.history_delivery_mainnet` |

## C-S8

### Premises

Assumes a kept covered-fork history from CheckpointStart, HistoryClean exclusions, <= 2^253 submissions, and blocks B at index j and D at index j + q / 2 in the history.

### Non-claims

Conditional on block D existing in the history; proves no wall-clock latency or consensus consolidation application, and depends on the per-block cap of 2 per the proved control.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| occurrence, delivery-block, record-position | `Blanc.Corpus.Proofs.Consolidation.c_s8` (`Blanc/Composition/Corpus/Proofs/ConsolidationLatency.lean:34`) | `thm:Blanc.Corpus.Proofs.Consolidation.c_s8` |

## B-S8

### Premises

Assumes clean Amsterdam kept histories for both EIP-8282 contracts; budget theorems sum paid word fees across all users and blocks (excluding principal and gas), and delivery composes those queue bounds with built-upon Amsterdam payload extensions of depth `q / 64` (deposit, offset `q mod 64`) and `q / 16` (exit, offset `q mod 16`).

### Non-claims

Mathematical fee-budget instances make no live ETH-supply claim; delivery is conditional on built-upon Amsterdam payloads without inhibitor latching and promises no wall-clock latency.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| deposit-history-queue-budget | `Blanc.Lift.BuilderRequest.ActualFeeBounds.deposit_every_boundary` (`Blanc/Composition/BuilderRequestActualFeeBounds.lean:111`) | `thm:Blanc.Lift.BuilderRequest.ActualFeeBounds.deposit_every_boundary` |
| exit-history-queue-budget | `Blanc.Lift.BuilderRequest.ActualFeeBounds.exit_every_boundary` (`Blanc/Composition/BuilderRequestActualFeeBounds.lean:123`) | `thm:Blanc.Lift.BuilderRequest.ActualFeeBounds.exit_every_boundary` |
| deposit-conditional-delivery | `Blanc.Lift.BuilderRequest.ActualFeeBounds.deposit_delivery` (`Blanc/Composition/BuilderRequestActualFeeBounds.lean:189`) | `thm:Blanc.Lift.BuilderRequest.ActualFeeBounds.deposit_delivery` |
| exit-conditional-delivery | `Blanc.Lift.BuilderRequest.ActualFeeBounds.exit_delivery` (`Blanc/Composition/BuilderRequestActualFeeBounds.lean:239`) | `thm:Blanc.Lift.BuilderRequest.ActualFeeBounds.exit_delivery` |

## D-S9

### Premises

Assumes ValidJointD over Electra/Prague or Fulu/Osaka/BPO with real BLS verification enabled (bls = true), canonical deposit and sibling system code, complete attributed receipts, and post-cutover AnchorLedgerD bounding legacy Eth1-bridge deposits without a 2020 bridge-finished premise.

### Non-claims

`D9FateJoined` and `D9ConservationJoined` partition post-cutover request occurrences (`cutoverCount <= k < E_final`) and exclude the pre-cutover legacy Eth1 deposit prefix (`k < cutoverCount`) from request-occurrence fate tracking. A new pubkey with an invalid BLS proof of possession receives no validator credit while its paid ETH remains permanently in the deposit contract; positive new-validator registration witnesses are conditional on real-BLS signature acceptance, and consensus enforces request list equality independently of blockHash.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| joined-delivery | `Blanc.Composition.DepositJoint.d9_delivery` (`Blanc/Composition/DepositJoint.lean:542`) | `thm:Blanc.Composition.DepositJoint.d9_delivery` |
| joined-fate-credit | `Blanc.Composition.DepositJoint.d9_fate_joined` (`Blanc/Composition/DepositJoint.lean:763`) | `thm:Blanc.Composition.DepositJoint.d9_fate_joined` |
| joined-conservation | `Blanc.Composition.DepositJoint.d9_conservation_joined` (`Blanc/Composition/DepositJoint.lean:609`) | `thm:Blanc.Composition.DepositJoint.d9_conservation_joined` |

## R-S9

### Premises

Assumes a valid Electra/Prague or Fulu/Osaka/BPO joint step with canonical EIP-4788 code and nonzero payload timestamp; skipped-slot SSZ header equality additionally assumes either consecutive slots (prev.slot + 1 = curr.slot) or hash_tree_root prev != 0.

### Non-claims

Joint-step parent_beacon_block_root = block.message.parent_root holds unconditionally, whereas across skipped slots a hypothetical zero BeaconState tree root would trigger Phase 0 sentinel replacement in process_slot, as witnessed by the proved sentinel control.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Composition.Corpus.Proofs.RingJointRetention.r_s9` (`Blanc/Composition/Corpus/Proofs/RingJointRetention.lean:182`) | `thm:Blanc.Composition.Corpus.Proofs.RingJointRetention.r_s9` |

## H-S9

### Premises

Assumes a clean kept covered-fork history with canonical EIP-2935 bytecode and contiguous `parentHash`-linked execution headers (`H_S9` chain form).

### Non-claims

Binds the execution-chain form `h_s9` (`H_S9`) within the 8,191-block ring window (with joint corollary `h_s9_joint` proved alongside it in `RingJointRetention.lean`); does not prove fork-choice canonicality or retain hashes older than 8,191 blocks.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Composition.Corpus.Proofs.RingJointRetention.h_s9` (`Blanc/Composition/Corpus/Proofs/RingJointRetention.lean:1154`) | `thm:Blanc.Composition.Corpus.Proofs.RingJointRetention.h_s9` |

## W-S9

### Premises

Assumes ValidJoint over Electra/Prague or Fulu/Osaka/BPO with deployment/checkpoint admission, AnchorInv, preset balance/epoch bounds, sibling system code, SYSTEM_ADDRESS exclusions, and <= 2^254 submissions, parameterized explicitly by signature-verification mode bls.

### Non-claims

Covers Electra and Fulu (not Gloas); requests failing validator/credential/balance/exit checks take the proved ignored outcome leaving beacon state unchanged while retaining paid fees.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| authorization-position | `Blanc.Lift.WithdrawalRequest.ValidJoint.authorization` (`Blanc/Lift/WithdrawalRequest/JointAuthorization.lean:212`) | `thm:Blanc.Lift.WithdrawalRequest.ValidJoint.authorization` |
| occurrence-fate | `Blanc.Lift.WithdrawalRequest.ValidJoint.fate` (`Blanc/Lift/WithdrawalRequest/JointFate.lean:78`) | `thm:Blanc.Lift.WithdrawalRequest.ValidJoint.fate` |
| outcome | `Blanc.Lift.WithdrawalRequest.ValidJoint.fate_outcome` (`Blanc/Lift/WithdrawalRequest/JointFate.lean:159`) | `thm:Blanc.Lift.WithdrawalRequest.ValidJoint.fate_outcome` |
| retained-budget | `Blanc.Lift.WithdrawalRequest.ValidJoint.fee_budget_retained_aggregate` (`Blanc/Lift/WithdrawalRequest/JointFate.lean:201`) | `thm:Blanc.Lift.WithdrawalRequest.ValidJoint.fee_budget_retained_aggregate` |
| crediting-recipient | `Blanc.Lift.WithdrawalRequest.ValidJoint.crediting_recipient` (`Blanc/Lift/WithdrawalRequest/JointCrediting.lean:58`) | `thm:Blanc.Lift.WithdrawalRequest.ValidJoint.crediting_recipient` |
| crediting-loop1 | `Blanc.Lift.WithdrawalRequest.ValidJoint.crediting_loop1` (`Blanc/Lift/WithdrawalRequest/JointCrediting.lean:111`) | `thm:Blanc.Lift.WithdrawalRequest.ValidJoint.crediting_loop1` |
| crediting-floor | `Blanc.Lift.WithdrawalRequest.ValidJoint.crediting_floor` (`Blanc/Lift/WithdrawalRequest/JointCrediting.lean:195`) | `thm:Blanc.Lift.WithdrawalRequest.ValidJoint.crediting_floor` |
| crediting-compounding | `Blanc.Lift.WithdrawalRequest.ValidJoint.crediting_loop1_compounding` (`Blanc/Lift/WithdrawalRequest/JointCrediting.lean:177`) | `thm:Blanc.Lift.WithdrawalRequest.ValidJoint.crediting_loop1_compounding` |
| crediting-address | `Blanc.Lift.WithdrawalRequest.ValidJoint.crediting_address` (`Blanc/Lift/WithdrawalRequest/JointCrediting.lean:376`) | `thm:Blanc.Lift.WithdrawalRequest.ValidJoint.crediting_address` |

## C-S9

### Premises

Authorization and fate assume ValidJointC (CheckpointStart, pre-anchor history, JointRun, HistoryClean, <= 2^253 cap); balance conservation assumes ValidJointCBalance (adding PendingDistinct and ordered acceptance/consumption traces across Electra-to-Fulu crossings).

### Non-claims

Acceptance checks target active/compounding/non-exiting status without target signature or caller-to-target address match; queued epoch processing skips slashed sources and waits for withdrawability without re-checking target eligibility.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| authorization | `Blanc.Composition.ConsolidationRequestJoint.c_s9_authorization` (`Blanc/Composition/ConsolidationRequestJoint.lean:326`) | `thm:Blanc.Composition.ConsolidationRequestJoint.c_s9_authorization` |
| fate | `Blanc.Composition.ConsolidationRequestJoint.c_s9_fate` (`Blanc/Composition/ConsolidationRequestJoint.lean:339`) | `thm:Blanc.Composition.ConsolidationRequestJoint.c_s9_fate` |
| balance | `Blanc.Composition.ConsolidationRequestBalance.c_s9_balance` (`Blanc/Composition/ConsolidationRequestBalance.lean:976`) | `thm:Blanc.Composition.ConsolidationRequestBalance.c_s9_balance` |

## B-S9

### Premises

Assumes ValidJointG at Gloas/Amsterdam with explicit focused premises; focused no-preanchor fate corollaries additionally assume an explicit pre-anchor prefix containing no Amsterdam block, and computational checker/replay soundness targets exact ValidJointG fields with real BLS.

### Non-claims

Preserves modulo-2^256 / saturation arithmetic domains unless bounded; payment-debit-at-most-once covers quorum, settlement, and old-parent paths while stating the exact anchor-crossing first-bid boundary, and theorem/checker soundness does not supply an external multi-client replay trace.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| deposit-position-fate | `Blanc.Lift.BuilderRequest.ValidJointG.deposit_fate` (`Blanc/Composition/BuilderRequestJointGFate.lean:309`) | `thm:Blanc.Lift.BuilderRequest.ValidJointG.deposit_fate` |
| exit-position-fate | `Blanc.Lift.BuilderRequest.ValidJointG.exit_fate` (`Blanc/Composition/BuilderRequestJointGFate.lean:396`) | `thm:Blanc.Lift.BuilderRequest.ValidJointG.exit_fate` |
| registration-authorization-credit | `Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s9_registration_authorization_credit` (`Blanc/Composition/Corpus/Proofs/MatrixComponentPins.lean:321`) | `thm:Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s9_registration_authorization_credit` |
| exit-authorization-caller | `Blanc.Lift.BuilderRequest.ValidJointG.exit_authorization_caller` (`Blanc/Composition/BuilderRequestJointGExitUnique.lean:84`) | `thm:Blanc.Lift.BuilderRequest.ValidJointG.exit_authorization_caller` |
| exit-resolution | `Blanc.Lift.BuilderRequest.ValidJointG.exit_resolution_unique` (`Blanc/Composition/BuilderRequestJointGExitUnique.lean:62`) | `thm:Blanc.Lift.BuilderRequest.ValidJointG.exit_resolution_unique` |
| payment-debit-at-most-once | `Blanc.Lift.BuilderRequest.ValidJointG.payment_debit_at_most_once` (`Blanc/Composition/BuilderRequestJointGDebitOnce.lean:1003`) | `thm:Blanc.Lift.BuilderRequest.ValidJointG.payment_debit_at_most_once` |
| deposit-focused-fate-no-preanchor | `Blanc.Lift.BuilderRequest.ValidJointG.deposit_fate_no_pre_anchor_emissions` (`Blanc/Composition/BuilderRequestJointGFateFocused.lean:29`) | `thm:Blanc.Lift.BuilderRequest.ValidJointG.deposit_fate_no_pre_anchor_emissions` |
| exit-focused-fate-no-preanchor | `Blanc.Lift.BuilderRequest.ValidJointG.exit_fate_no_pre_anchor_emissions` (`Blanc/Composition/BuilderRequestJointGFateFocused.lean:59`) | `thm:Blanc.Lift.BuilderRequest.ValidJointG.exit_fate_no_pre_anchor_emissions` |

## D-S10

### Premises

Assumes the Amsterdam fork, canonical deposit runtime bytes at the deposit address, complete block receipts, and attribution of deposit-topic logs at the deposit address to settled canonical deposit frames via the step-capability soundness lift.

### Non-claims

Safety-only statement for Amsterdam row S10 (no Amsterdam deposit gas bound or post-S10 Amsterdam history/Gloas deposit claim); paired Amsterdam short-log control proves the canonical code premise remains load-bearing.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| log-shape, parse | `Blanc.Composition.DepositParse.d_s10` (`Blanc/Composition/DepositParse.lean:119`) | `thm:Blanc.Composition.DepositParse.d_s10` |

## R-S10

### Premises

Assumes the Amsterdam fork and canonical EIP-4788 bytecode installed at the beacon-roots predeploy address, with arbitrary initial contract storage.

### Non-claims

RegularGasWithin bounds regular execution gas only and excludes Amsterdam state gas; Amsterdam coverage for EIP-4788 is confined to row S10.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Corpus.Proofs.R.r_s10` (`Blanc/Composition/Corpus/Proofs/RingTotality.lean:60`) | `thm:Blanc.Corpus.Proofs.R.r_s10` |

## H-S10

### Premises

Assumes the Amsterdam fork, canonical EIP-2935 bytecode installed at the history-storage predeploy address, `blockHashes.getLast? = some lastHash`, and arbitrary initial contract storage.

### Non-claims

RegularGasWithin bounds regular execution gas only and excludes Amsterdam state gas; Amsterdam coverage for EIP-2935 is confined to row S10.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Corpus.Proofs.H.h_s10` (`Blanc/Composition/Corpus/Proofs/RingTotality.lean:121`) | `thm:Blanc.Corpus.Proofs.H.h_s10` |

## W-S10

### Premises

Assumes the Amsterdam fork and canonical EIP-7002 bytecode (plus canonical sibling request bytecodes for the composed four-contract request phase), with arbitrary initial storage.

### Non-claims

RegularGasWithin excludes Amsterdam state gas; Amsterdam coverage for EIP-7002 is confined to row S10 and the ordered four-contract system request pass.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Composition.Corpus.Proofs.MatrixComponentPins.w_s10_headline` (`Blanc/Composition/Corpus/Proofs/MatrixComponentPins.lean:443`) | `thm:Blanc.Composition.Corpus.Proofs.MatrixComponentPins.w_s10_headline` |

## C-S10

### Premises

Assumes the Amsterdam fork and canonical EIP-7251 bytecode (plus canonical sibling request bytecodes for the composed four-contract request phase), with arbitrary initial storage.

### Non-claims

RegularGasWithin excludes Amsterdam state gas; Amsterdam coverage for EIP-7251 is confined to row S10 and the ordered four-contract system request pass.

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| headline | `Blanc.Composition.Corpus.Proofs.MatrixComponentPins.c_s10_headline` (`Blanc/Composition/Corpus/Proofs/MatrixComponentPins.lean:492`) | `thm:Blanc.Composition.Corpus.Proofs.MatrixComponentPins.c_s10_headline` |

## B-S10

### Premises

Assumes the Amsterdam fork and canonical EIP-8282 deposit and exit bytecodes (together with canonical withdrawal and consolidation bytecodes in the full four-contract pass) from arbitrary storage.

### Non-claims

Covers the Amsterdam request-phase system-call pass and regular-gas bounds; excludes Amsterdam state gas and consensus request-outcome application (covered in B-S9).

### Evidence

| Components | Theorem | Pin |
|---|---|---|
| deposit | `Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s10_deposit` (`Blanc/Composition/Corpus/Proofs/MatrixComponentPins.lean:358`) | `thm:Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s10_deposit` |
| exit | `Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s10_exit` (`Blanc/Composition/Corpus/Proofs/MatrixComponentPins.lean:370`) | `thm:Blanc.Composition.Corpus.Proofs.MatrixComponentPins.b_s10_exit` |

## Implementation notes

Every applicable cell of the protocol-contract matrix (`D`, `R`, `H`, `W`, `C`, `B` across `S1`–`S10`, with `D-S5`, `R-S5`, and `H-S5` fixed `N/A (fee row)`) is bound above to a public Lean theorem whose exact statement and transitive definition closure are pinned in `scripts/ClaimCheck.lean` and hashed in `scripts/claim-pin-hash/roots.tsv`. Structural matrix verification (`scripts/check-protocol-contract-corpus.sh`) operates alongside `scripts/check-claims.sh`, `scripts/check-claim-hash.sh`, and the checked build certificate.

Cross-family scope boundaries and byte-versus-prose disclosures:

- **Bytecode departures from EIP prose:** EIP-7002 (`W-S5`), EIP-7251 (`C-S5`), and both EIP-8282 contracts (`B-S5`) wrap their 256-bit Taylor numerator multiplication first at stored excess `2,893`, strictly underquoting the natural-number `fake_exponential` specification. Both EIP-8282 contracts (`B-S2`, `B-S5`) clear a `B256.max` inhibitor word written to slot `0` by a nonzero-calldata `SYSTEM_ADDRESS` call on the next empty-calldata system call rather than latching permanently. EIP-4788 (`R-S2`, `R-S6`) and EIP-2935 (`H-S2`, `H-S6`) omit a zero-value check on user reads and retain any ETH sent on settled read frames.
- **Ring and joint boundaries (`R`, `H`, `D`):** `R-S8` pairs unconditional timestamp congruence (`r_s8_time`) with affine slot retention (`r_s8_slot`) and an arithmetic `writeAll` slot-grid wrap control (`r_s8_slot_control`). `R-S9` proves unconditional `jointBlockInput` root equality and guards skipped-slot SSZ header relationships by `prev.slot + 1 = curr.slot ∨ hash_tree_root prev ≠ 0` (`r_s9_control`). `H-S9` establishes contiguous chain-hash provenance without skipped-slot ambiguity. `D-S9` runs with real BLS enabled (`bls = true`), bounds legacy Eth1-bridge deposits via post-cutover `AnchorLedgerD` without imposing a finished-bridge premise at block `11,052,984`, discloses that invalid-signature new-pubkey deposits leave paid ETH in the deposit contract without validator credit, and pairs conditional real-BLS registration witnesses with closed invalid-signature, top-up, list-versus-hash seam, and replay controls.
- **Builder focused theorems and applicability (`B`):** `B-S2` uses unrestricted Form B without `HistoryClean` or `SystemCodeAbsent`. `B-S4` begins at observed checkpoint block `26,391,669` (whole-storage `storageHash` roots for empty deposit storage and `slot0 = max` exit storage, leaving creation block `26,211,406` and the intervening prefix outside checkpoint coverage). `B-S8` proves history-wide multi-user queue fee budgets at every request boundary composed with conditional `⌊q / 64⌋` (deposit, offset `q mod 64`) and `⌊q / 16⌋` (exit, offset `q mod 16`) delivery on built-upon Amsterdam payloads. `B-S9` provides focused premise-explicit headlines, explicit no-Amsterdam-prefix fate corollaries, payment-debit-at-most-once across quorum/settlement/old-parent paths with its exact anchor-crossing first-bid boundary, and computational checker/replay soundness tied to the exact `ValidJointG` premise bundle under real BLS without claiming an external multi-client trace.
- **Observation and fork boundaries:** Mainnet deployment and checkpoint records (`11,052,984`, `21,881,389`, `22,431,083`, `26,391,669`) are modeled provenance hypotheses whose external RPC header and trie responses are not authenticated inside Lean. Amsterdam execution for `D`, `R`, `H`, `W`, and `C` is confined to row `S10` (regular gas / settled deposit log safety), while `B` covers Amsterdam execution and Gloas joint transitions across `S1`–`S10`.
