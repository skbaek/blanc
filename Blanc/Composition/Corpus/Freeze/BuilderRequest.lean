import Blanc.Composition.BuilderRequestPublicGuarantees
import Blanc.Lift.BuilderRequest.Deposit.Fifo
import Blanc.Lift.BuilderRequest.Exit.Fifo
import Blanc.Lift.BuilderRequest.Latch

/-!
# Freeze record (G0, part cb): EIP-8282 cells B-S2 and B-S4

Statements only, against Blanc main `7f2a69ba` and Jaune `c30cf0a5`. Nothing here is proved, registered in the
layering classification, or imported by the root.

* `B_S2`: unrestricted Form B, selected by the user on 2026-11-11 (goal revision 3, section 13).
  Every frame a kept history keeps at either contract is a SYSTEM_ADDRESS empty-calldata dequeue, a SYSTEM_ADDRESS
  nonempty-calldata latch, a non-system submission or a non-system fee read, with exact storage, log, output and
  balance effects. No `HistoryClean` or `SystemCodeAbsent` premise is used. Both privileged arms apply on every kept
  fork: the caller dispatch does not test whether Amsterdam has activated. Thus a user-originated SYSTEM_ADDRESS
  call before Amsterdam can dequeue or latch, although the protocol schedules its own builder calls only at Amsterdam.
  The latch is reversible: the next empty-calldata system call resets slot 0 from the inhibitor to zero.
* `B_S4`: the delivery statement rooted at an observed mainnet checkpoint, block 26,391,669 (timestamp 1,794,399,959,
  hash `0x2410…fb6f`, `stateRoot = expectedStateRoot`), a recent observed checkpoint; the record
  holds the full tip schema together with the five whole-account/storage equalities `ValidJointG`'s checkpoint fields
  consume.
-/

namespace Blanc.Corpus.Freeze.Builder

open Jaune Blanc Blanc.Lift.BuilderRequest
open Blanc.Lift.RequestSystem (sysState drainCount)
open Blanc.Composition.BuilderRequestPublic

/-! ## Vocabulary -/

/-- The fee word the bytes quote at an excess: the word the fee loop leaves, divided by 17. (The word form of
`ConsolidationRequestPublic.quotedFee`; at landing the two share one definition.) -/
noncomputable def wordFee (excess : B256) : B256 :=
  (Classical.choose (Blanc.WordFakeExponential.run_exists_unique excess 17 1 17 0).exists).2 / (17 : B256)

/-- The excess a builder contract quotes at, read off its storage: slot 0 plus what the count in slot 1 exceeds the
per-block target by (word arithmetic). -/
def quotedExcess (target : B256) (pre : Devm) (a : Adr) : B256 :=
  targetExcess target (pre.getStorVal a 0) (pre.getStorVal a 1)

/-! ## B-S2: what succeeds, per contract -/

/-- **Unrestricted settled-frame classification at the builder deposit contract.** Exactly one of four disjoint
caller/calldata forms. No arm's code moves a balance: any value transfer occurs before the frame starts. The system
arms do not constrain value or fork and need not be protocol-scheduled calls. -/
inductive DepositSettled (b : KeptBlock) (f : Exec.Frame) : Prop
  /-- **Dequeue.** A non-static SYSTEM_ADDRESS call with empty calldata, at any kept fork. Its world is exactly
  `sysState`: the pointer updates, slot 0's word-arithmetic excess update (including inhibitor-to-zero reset), and
  cleared count, with every other account field unchanged. Output is the first `min(64, (tail − head) mod 2^256)`
  records, 184 bytes each with the amount little-endian; no log or balance change. -/
  | dequeue (caller : f.sevm.caller = systemAddress) (empty : f.sevm.data = [])
      (dynamic : f.sevm.isStatic = false)
      (state : f.post.state = sysState Deposit.sysShape f.pre.state depositAddr)
      (output : f.post.output = Deposit.sysOutput.drained (f.pre.getStorVal depositAddr)
        (f.pre.getStorVal depositAddr 2)
        (drainCount Deposit.sysShape.cap.word (f.pre.getStorVal depositAddr 2)
          (f.pre.getStorVal depositAddr 3)).toNat)
      (balance : ∀ a, f.post.getBal a = f.pre.getBal a)
      (logs : f.post.logs = f.pre.logs)
  /-- **Reversible latch.** A non-static SYSTEM_ADDRESS call with nonempty calldata, at any kept fork. It drains
  exactly as `dequeue`, sets slot 0 to `B256.max` and clears slot 1; exact world `latchState`, same output and no log
  or balance change. It reads neither CALLVALUE nor the calldata contents. A later empty-calldata dequeue resets the
  inhibitor to zero. -/
  | latch (caller : f.sevm.caller = systemAddress) (nonempty : f.sevm.data ≠ [])
      (dynamic : f.sevm.isStatic = false)
      (state : f.post.state = latchState Deposit.sysShape f.pre.state depositAddr)
      (output : f.post.output = Deposit.sysOutput.drained (f.pre.getStorVal depositAddr)
        (f.pre.getStorVal depositAddr 2)
        (drainCount Deposit.sysShape.cap.word (f.pre.getStorVal depositAddr 2)
          (f.pre.getStorVal depositAddr 3)).toNat)
      (balance : ∀ a, f.post.getBal a = f.pre.getBal a)
      (logs : f.post.logs = f.pre.logs)
  /-- **Submission.** 184 bytes from a caller other than SYSTEM_ADDRESS, non-static, slot 0 off the inhibitor, the
  credited amount at least 1 ETH and the value at least the credit plus the quoted fee. The record is stored at the
  tail; one topicless log of the 184 calldata bytes; nothing else. -/
  | submission (caller : f.sevm.caller ≠ systemAddress) (length : f.sevm.data.length = 184)
      (dynamic : f.sevm.isStatic = false) (active : f.pre.getStorVal depositAddr 0 ≠ B256.max)
      (admitted : Deposit.Admitted f.sevm (wordFee (quotedExcess 8 f.pre depositAddr)))
      (storage : f.post.getStor depositAddr = Deposit.submittedStorage f.sevm (f.pre.getStor depositAddr))
      (others : ∀ a, a ≠ depositAddr → f.post.getStor a = f.pre.getStor a)
      (balance : ∀ a, f.post.getBal a = f.pre.getBal a)
      (logs : f.post.logs = f.pre.logs ++ [⟨depositAddr, [], f.sevm.data⟩])
      (output : f.post.output = f.pre.output)
  /-- **Fee read.** Empty calldata and no value from a caller other than SYSTEM_ADDRESS, slot 0 off the inhibitor:
  returns the quoted fee as one word and changes no storage, balance or log. Static reads are allowed. -/
  | feeRead (caller : f.sevm.caller ≠ systemAddress) (empty : f.sevm.data = []) (value : f.sevm.value = 0)
      (active : f.pre.getStorVal depositAddr 0 ≠ B256.max)
      (output : f.post.output = (wordFee (quotedExcess 8 f.pre depositAddr)).toBytes)
      (storage : ∀ a, f.post.getStor a = f.pre.getStor a)
      (balance : ∀ a, f.post.getBal a = f.pre.getBal a)
      (logs : f.post.logs = f.pre.logs)

/-- **Unrestricted settled-frame classification at the builder exit contract.** Exactly one of the same four
disjoint forms, with 48-byte submissions and at most 16 dequeued 68-byte records. -/
inductive ExitSettled (b : KeptBlock) (f : Exec.Frame) : Prop
  /-- **Dequeue.** A non-static SYSTEM_ADDRESS empty-calldata call at any kept fork, including user-originated
  calls before Amsterdam. Exact pointer/excess/count update, output, balance and log effects. -/
  | dequeue (caller : f.sevm.caller = systemAddress) (empty : f.sevm.data = [])
      (dynamic : f.sevm.isStatic = false)
      (state : f.post.state = sysState Exit.sysShape f.pre.state exitAddr)
      (output : f.post.output = Exit.sysOutput.drained (f.pre.getStorVal exitAddr)
        (f.pre.getStorVal exitAddr 2)
        (drainCount Exit.sysShape.cap.word (f.pre.getStorVal exitAddr 2) (f.pre.getStorVal exitAddr 3)).toNat)
      (balance : ∀ a, f.post.getBal a = f.pre.getBal a)
      (logs : f.post.logs = f.pre.logs)
  /-- **Reversible latch.** The same drain on nonempty calldata, exact world `latchState` (slot 0 at the inhibitor,
  slot 1 cleared), at any kept fork; same output, no log or balance change. No zero-value guard. -/
  | latch (caller : f.sevm.caller = systemAddress) (nonempty : f.sevm.data ≠ [])
      (dynamic : f.sevm.isStatic = false)
      (state : f.post.state = latchState Exit.sysShape f.pre.state exitAddr)
      (output : f.post.output = Exit.sysOutput.drained (f.pre.getStorVal exitAddr)
        (f.pre.getStorVal exitAddr 2)
        (drainCount Exit.sysShape.cap.word (f.pre.getStorVal exitAddr 2) (f.pre.getStorVal exitAddr 3)).toNat)
      (balance : ∀ a, f.post.getBal a = f.pre.getBal a)
      (logs : f.post.logs = f.pre.logs)
  /-- **Submission.** 48 bytes from a caller other than SYSTEM_ADDRESS, non-static, slot 0 off the inhibitor, value
  at least the quoted fee. The record (caller, then the calldata) is stored at the tail; one topicless log of its 68
  bytes; nothing else. -/
  | submission (caller : f.sevm.caller ≠ systemAddress) (length : f.sevm.data.length = 48)
      (dynamic : f.sevm.isStatic = false) (active : f.pre.getStorVal exitAddr 0 ≠ B256.max)
      (covered : (wordFee (quotedExcess 2 f.pre exitAddr)).toNat ≤ f.sevm.value.toNat)
      (storage : f.post.getStor exitAddr = Exit.submittedStorage f.sevm (f.pre.getStor exitAddr))
      (others : ∀ a, a ≠ exitAddr → f.post.getStor a = f.pre.getStor a)
      (balance : ∀ a, f.post.getBal a = f.pre.getBal a)
      (logs : f.post.logs = f.pre.logs ++ [⟨exitAddr, [], f.sevm.caller.toBytes ++ f.sevm.data⟩])
      (output : f.post.output = f.pre.output)
  /-- **Fee read.** As for the deposit contract: empty calldata, zero value, active, static or dynamic. -/
  | feeRead (caller : f.sevm.caller ≠ systemAddress) (empty : f.sevm.data = []) (value : f.sevm.value = 0)
      (active : f.pre.getStorVal exitAddr 0 ≠ B256.max)
      (output : f.post.output = (wordFee (quotedExcess 2 f.pre exitAddr)).toBytes)
      (storage : ∀ a, f.post.getStor a = f.pre.getStor a)
      (balance : ∀ a, f.post.getBal a = f.pre.getBal a)
      (logs : f.post.logs = f.pre.logs)

/-- **B-S2 at the deposit contract, unrestricted Form B.** Every settled frame a kept history keeps there is a
dequeue, latch, submission or fee read with the exact effects above. SYSTEM_ADDRESS may send transactions, hold
code, be a 7702 authority or be created; no clean-history or system-code-absence premise is used. A dequeue need not
be the block's scheduled request call, and its fork need not be Amsterdam. -/
def B_S2_deposit : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    -- kept: a kept history (covered forks and Amsterdam) from a start holding both builder codes
    (_kept : CodesKept cfg start blocks stop),
    ∀ b ∈ blocks, ∀ f ∈ b.keptAt depositAddr, DepositSettled b f

/-- **B-S2 at the exit contract, unrestricted Form B.** The same four-arm exhaustive classification, with neither
SYSTEM_ADDRESS exclusions nor a protocol-scheduled-only restriction on its privileged calls. -/
def B_S2_exit : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    -- kept: a kept history (covered forks and Amsterdam) from a start holding both builder codes
    (_kept : CodesKept cfg start blocks stop),
    ∀ b ∈ blocks, ∀ f ∈ b.keptAt exitAddr, ExitSettled b f

/-- **B-S2.** One unrestricted statement for each builder contract, under `CodesKept` only. The four arms are
pairwise disjoint by caller and calldata: SYSTEM_ADDRESS empty/nonempty, non-system submission-length/empty. The
reversible latch and pre-Amsterdam user-originated SYSTEM_ADDRESS dequeues are included explicitly. -/
def B_S2 : Prop := B_S2_deposit ∧ B_S2_exit

/-! ### B-S2 negative controls

The guard-deletion and spurious-success witnesses below falsify the unrestricted four-arm relations: their caller
is explicitly non-system, so neither new privileged arm can classify the mutant. The old clean-history/empty-system
premise control is superseded: its latch behavior is now a required success arm, not a counterexample.
-/

/-- Replace `repl.length` bytes starting at `offset` in `code`. -/
def patchBytes (code : ByteArray) (offset : Nat) (repl : List UInt8) : ByteArray :=
  ⟨(code.toList.take offset ++ repl ++ code.toList.drop (offset + repl.length)).toArray⟩

/-- Mutant of `Deposit.code` with the 1-ETH floor guard (`PUSH2 0x0270; JUMPI` at bytes `187..190`, `0xbb..0xbe`)
replaced by `POP; JUMPDEST; JUMPDEST; JUMPDEST` (`0x50, 0x5b, 0x5b, 0x5b`), so `< 1 ETH` 184-byte submissions fall
through and commit. -/
def depositNoFloorCode : ByteArray :=
  patchBytes Deposit.code 187 [0x50, 0x5b, 0x5b, 0x5b]

/-- Mutant of `Deposit.code` with the shared guard-revert opcode (`REVERT` `0xfd` at byte `627`, `0x0273`) replaced by
`STOP` (`0x00`), adding a spurious success arm whenever an acceptance guard fails. -/
def depositSpuriousArmCode : ByteArray :=
  patchBytes Deposit.code 627 [0x00]

/-- Mutant of `Exit.code` with the fee guard (`PUSH2 0x01c6; JUMPI` at bytes `161..164`, `0xa1..0xa4`) replaced by
`POP; JUMPDEST; JUMPDEST; JUMPDEST` (`0x50, 0x5b, 0x5b, 0x5b`), so underpaid 48-byte exit submissions fall through and
commit. -/
def exitNoFeeGuardCode : ByteArray :=
  patchBytes Exit.code 161 [0x50, 0x5b, 0x5b, 0x5b]

/-- Mutant of `Exit.code` with the shared guard-revert opcode (`REVERT` `0xfd` at byte `457`, `0x01c9`) replaced by
`STOP` (`0x00`), adding a spurious success arm whenever an acceptance guard fails. -/
def exitSpuriousArmCode : ByteArray :=
  patchBytes Exit.code 457 [0x00]

/-- **B-S2 deposit negative control (`B_S2_deposit_control`).**
(1) Real guard rejection: on canonical `Deposit.code`, any fresh non-system frame at a kept fork (`KeptFork`) that
violates calldata length (`data ≠ [] ∧ data.length ≠ 184`), inhibition (`slot 0 = B256.max`), or submission admission
(`data.length = 184 ∧ ¬ Deposit.Admitted sevm (wordFee (quotedExcess 8 pre depositAddr))`) has no `.ok` execution.
(2) Guard-deletion mutant (`depositNoFloorCode`, 1-ETH floor deleted): there exist a kept block `b`, `sevm`, `pre`,
`post`, and a committed execution `run : Exec 0 { sevm with code := depositNoFloorCode } pre (.ok post)` (`hc`) on
inputs where canonical `Deposit.code` has no `.ok` execution, whose committed frame `Exec.Frame.ofRun run hc` falsifies
`DepositSettled b`.
(3) Spurious-success-arm mutant (`depositSpuriousArmCode`, `REVERT → STOP`): there exist `b`, `sevm`, `pre`, `post`,
and a committed execution `run : Exec 0 { sevm with code := depositSpuriousArmCode } pre (.ok post)` (`hc`, rejected by
canonical `Deposit.code`, e.g. wrong calldata length) whose committed frame `Exec.Frame.ofRun run hc` falsifies
`DepositSettled b`. -/
def B_S2_deposit_control : Prop :=
  (∀ {sevm : Sevm} {pre post : Devm},
    sevm.code = Deposit.code →
    sevm.currentTarget = depositAddr →
    KeptFork sevm.benvStat.fork →
    sevm.caller ≠ systemAddress →
    pre.stack = [] →
    pre.memory.size % 32 = 0 →
    Mem.Wf pre.memory →
    sevm.data.length < 2 ^ 256 →
    ((sevm.data ≠ [] ∧ sevm.data.length ≠ 184) ∨
      pre.getStorVal depositAddr 0 = B256.max ∨
      (sevm.data.length = 184 ∧ ¬ Deposit.Admitted sevm (wordFee (quotedExcess 8 pre depositAddr)))) →
    IsEmpty (Exec 0 sevm pre (.ok post))) ∧
  (∃ (b : KeptBlock) (sevm : Sevm) (pre post : Devm)
      (run : Exec 0 { sevm with code := depositNoFloorCode } pre (.ok post))
      (hc : Execution.commits (.ok post) = true),
    sevm.currentTarget = depositAddr ∧
    sevm.caller ≠ systemAddress ∧
    KeptFork sevm.benvStat.fork ∧
    b.fork = sevm.benvStat.fork ∧
    pre.stack = [] ∧ pre.memory = .empty ∧
    sevm.data.length = 184 ∧
    (∀ post', IsEmpty (Exec 0 { sevm with code := Deposit.code } pre (.ok post'))) ∧
    ¬ DepositSettled b (Exec.Frame.ofRun run hc)) ∧
  (∃ (b : KeptBlock) (sevm : Sevm) (pre post : Devm)
      (run : Exec 0 { sevm with code := depositSpuriousArmCode } pre (.ok post))
      (hc : Execution.commits (.ok post) = true),
    sevm.currentTarget = depositAddr ∧
    sevm.caller ≠ systemAddress ∧
    KeptFork sevm.benvStat.fork ∧
    b.fork = sevm.benvStat.fork ∧
    pre.stack = [] ∧ pre.memory = .empty ∧
    sevm.data ≠ [] ∧ sevm.data.length ≠ 184 ∧
    (∀ post', IsEmpty (Exec 0 { sevm with code := Deposit.code } pre (.ok post'))) ∧
    ¬ DepositSettled b (Exec.Frame.ofRun run hc))

/-- **B-S2 exit negative control (`B_S2_exit_control`).**
(1) Real guard rejection: on canonical `Exit.code`, any fresh non-system frame at a kept fork (`KeptFork`) that
violates calldata length (`data ≠ [] ∧ data.length ≠ 48`), inhibition (`slot 0 = B256.max`), or fee coverage
(`data.length = 48 ∧ sevm.value.toNat < (wordFee (quotedExcess 2 pre exitAddr)).toNat`) has no `.ok` execution.
(2) Guard-deletion mutant (`exitNoFeeGuardCode`, fee guard deleted): there exist `b`, `sevm`, `pre`, `post`, and a
committed execution `run : Exec 0 { sevm with code := exitNoFeeGuardCode } pre (.ok post)` (`hc`, on 48-byte underpaid
inputs rejected by canonical `Exit.code`) whose committed frame `Exec.Frame.ofRun run hc` falsifies `ExitSettled b`.
(3) Spurious-success-arm mutant (`exitSpuriousArmCode`, `REVERT → STOP`): there exist `b`, `sevm`, `pre`, `post`, and a
committed execution `run : Exec 0 { sevm with code := exitSpuriousArmCode } pre (.ok post)` (`hc`, on wrong-length
calldata rejected by canonical `Exit.code`) whose committed frame `Exec.Frame.ofRun run hc` falsifies `ExitSettled b`. -/
def B_S2_exit_control : Prop :=
  (∀ {sevm : Sevm} {pre post : Devm},
    sevm.code = Exit.code →
    sevm.currentTarget = exitAddr →
    KeptFork sevm.benvStat.fork →
    sevm.caller ≠ systemAddress →
    pre.stack = [] →
    pre.memory.size % 32 = 0 →
    Mem.Wf pre.memory →
    sevm.data.length < 2 ^ 256 →
    ((sevm.data ≠ [] ∧ sevm.data.length ≠ 48) ∨
      pre.getStorVal exitAddr 0 = B256.max ∨
      (sevm.data.length = 48 ∧ sevm.value.toNat < (wordFee (quotedExcess 2 pre exitAddr)).toNat)) →
    IsEmpty (Exec 0 sevm pre (.ok post))) ∧
  (∃ (b : KeptBlock) (sevm : Sevm) (pre post : Devm)
      (run : Exec 0 { sevm with code := exitNoFeeGuardCode } pre (.ok post))
      (hc : Execution.commits (.ok post) = true),
    sevm.currentTarget = exitAddr ∧
    sevm.caller ≠ systemAddress ∧
    KeptFork sevm.benvStat.fork ∧
    b.fork = sevm.benvStat.fork ∧
    pre.stack = [] ∧ pre.memory = .empty ∧
    sevm.data.length = 48 ∧
    (∀ post', IsEmpty (Exec 0 { sevm with code := Exit.code } pre (.ok post'))) ∧
    ¬ ExitSettled b (Exec.Frame.ofRun run hc)) ∧
  (∃ (b : KeptBlock) (sevm : Sevm) (pre post : Devm)
      (run : Exec 0 { sevm with code := exitSpuriousArmCode } pre (.ok post))
      (hc : Execution.commits (.ok post) = true),
    sevm.currentTarget = exitAddr ∧
    sevm.caller ≠ systemAddress ∧
    KeptFork sevm.benvStat.fork ∧
    b.fork = sevm.benvStat.fork ∧
    pre.stack = [] ∧ pre.memory = .empty ∧
    sevm.data ≠ [] ∧ sevm.data.length ≠ 48 ∧
    (∀ post', IsEmpty (Exec 0 { sevm with code := Exit.code } pre (.ok post'))) ∧
    ¬ ExitSettled b (Exec.Frame.ofRun run hc))

/-! ## B-S4: rooted in a recorded mainnet fact -/

/-- **The observation schema at mainnet block 26,391,669**, a recent observed checkpoint with the registered
runtime bytes and the same fresh-storage facts. The complete tip header (number, timestamp, hash, and
`expectedStateRoot` supplied when the observation record is taken and adopted under registered provenance) together with
the five whole-account and whole-storage reads (`eth_getCode` at both builder addresses and `SYSTEM_ADDRESS`, and
`eth_getProof` `storageHash` establishing empty storage at the deposit contract and `{slot 0 ↦ 2^256 − 1}` at the exit
contract). Lean does not authenticate the account reads against `expectedStateRoot`. -/
structure BuilderCheckpointObservation (expectedStateRoot : B256) (checkpoint : BlockChain) : Prop where
  /-- The checkpoint's last header: number 26,391,669, timestamp 1,794,399,959, hash `0x2410…fb6f`, and
  `stateRoot = expectedStateRoot`. -/
  tip : ∃ t, checkpoint.blocks.getLast? = some t ∧
    t.header.number = 26391669 ∧
    t.header.timestamp = 1794399959 ∧
    t.header.hash = 0x2410154b2609d8811f1acde0d30fea3815da62d90648e262fae38d2b5e4bfb6f ∧
    t.header.stateRoot = expectedStateRoot
  /-- `eth_getCode` at the deposit contract: the registered runtime. -/
  depositCode : checkpoint.state.getCode Deposit.Creation.address = Deposit.code
  /-- `eth_getProof` at the deposit contract: the empty storage root. -/
  depositStorage : checkpoint.state.getStor Deposit.Creation.address = Stor.empty
  /-- `eth_getCode` at the exit contract: the registered runtime. -/
  exitCode : checkpoint.state.getCode Exit.Creation.address = Exit.code
  /-- `eth_getProof` at the exit contract: slot 0 at the inhibitor, nothing else. -/
  exitStorage : checkpoint.state.getStor Exit.Creation.address = Exit.deployedStorage
  /-- `eth_getCode(0xff…fe)` is empty. -/
  systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty

/-- **B-S4 instantiated at a recorded tip `expectedStateRoot`.** (1) Exact delivery (`history_delivers_exactly`) for
every kept history from the observed checkpoint, under any chain configuration: what the blocks publish for each
builder contract is, in order, a prefix of what was submitted to it. (2) The record holds the exact five whole-account
and whole-storage equalities `ValidJointG`'s checkpoint fields consume: no code at `SYSTEM_ADDRESS`, both builder
codes, the deposit contract's `Stor.empty`, and the exit contract's `Exit.deployedStorage`. -/
def B_S4_at (expectedStateRoot : B256) : Prop :=
  (∀ {cfg : ChainConfig} {checkpoint stop : BlockChain} {blocks : List KeptBlock}
    -- obs: the recorded mainnet facts at block 26,391,669 with state root `expectedStateRoot`
    (_obs : BuilderCheckpointObservation expectedStateRoot checkpoint)
    -- kept: a kept history from the checkpoint
    (_kept : KeptHistory cfg checkpoint blocks stop)
    -- clean: no kept block has SYSTEM_ADDRESS as a sender or a 7702 authority, and none creates it
    (_clean : HistoryClean blocks)
    -- budget: the deposit contract's kept frames carried at most 2^256 wei
    (_budget : feesPaidAt blocks depositAddr ≤ 2 ^ 256)
    -- few: at most 2^64 exit submissions
    (_few : (exitSubmitted blocks).length ≤ 2 ^ 64),
    depositRequests blocks <+: (depositSubmitted blocks).flatMap Deposit.contract.out ∧
    exitRequests blocks <+: (exitSubmitted blocks).flatMap Exit.contract.out) ∧
  (∀ {checkpoint : BlockChain} (_obs : BuilderCheckpointObservation expectedStateRoot checkpoint),
    checkpoint.state.getCode systemAddress = ByteArray.empty ∧
    checkpoint.state.getCode Deposit.Creation.address = Deposit.code ∧
    checkpoint.state.getStor Deposit.Creation.address = Stor.empty ∧
    checkpoint.state.getCode Exit.Creation.address = Exit.code ∧
    checkpoint.state.getStor Exit.Creation.address = Exit.deployedStorage)

/-- **B-S4.** Uniform over the tip `expectedStateRoot` recorded and adopted at mainnet block 26,391,669. -/
def B_S4 : Prop := ∀ expectedStateRoot : B256, B_S4_at expectedStateRoot

end Blanc.Corpus.Freeze.Builder
