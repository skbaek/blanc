import Blanc.Composition.BuilderRequestPublicGuarantees
import Blanc.Lift.BuilderRequest.Deposit.Fifo
import Blanc.Lift.BuilderRequest.Exit.Fifo

/-!
# Freeze record (G0, part cb): EIP-8282 cells B-S2 and B-S4

Statements only, against Blanc main `7f2a69ba` and Jaune `c30cf0a5`. Nothing here is proved, registered in the
layering classification, or imported by the root.

* `B_S2`: one statement for each builder contract. Every frame a kept history keeps at the contract is the block's own
  dequeue, a submission or a fee read, with its storage, log, output and balance effect.
* `B_S4`: the delivery statement rooted at an observed mainnet checkpoint, block 26,211,406, the block of the recorded
  creation transaction; the record holds exactly the facts `ValidJointG`'s checkpoint fields consume.
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

/-- **What a settled frame at the builder deposit contract is.** Exactly one of three. No arm's code moves a balance:
the value a call carries is credited before the frame starts. -/
inductive DepositSettled (b : KeptBlock) (f : Exec.Frame) : Prop
  /-- **Dequeue: the block's own call.** The caller is SYSTEM_ADDRESS, the calldata is empty and the block is at
  Amsterdam. The world state after is `sysState` (the four bookkeeping words, nothing else); the output is the first
  `min(64, (tail − head) mod 2^256)` stored records, 184 bytes each; no log. -/
  | dequeue (caller : f.sevm.caller = systemAddress) (empty : f.sevm.data = []) (fork : b.fork = .amsterdam)
      (state : f.post.state = sysState Deposit.sysShape f.pre.state depositAddr)
      (output : f.post.output = Deposit.sysOutput.drained (f.pre.getStorVal depositAddr)
        (f.pre.getStorVal depositAddr 2)
        (drainCount Deposit.sysShape.cap.word (f.pre.getStorVal depositAddr 2)
          (f.pre.getStorVal depositAddr 3)).toNat)
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
  returns the quoted fee as one word and changes nothing. -/
  | feeRead (caller : f.sevm.caller ≠ systemAddress) (empty : f.sevm.data = []) (value : f.sevm.value = 0)
      (active : f.pre.getStorVal depositAddr 0 ≠ B256.max)
      (output : f.post.output = (wordFee (quotedExcess 8 f.pre depositAddr)).toBytes)
      (storage : ∀ a, f.post.getStor a = f.pre.getStor a)
      (balance : ∀ a, f.post.getBal a = f.pre.getBal a)
      (logs : f.post.logs = f.pre.logs)

/-- **What a settled frame at the builder exit contract is.** Exactly one of three. -/
inductive ExitSettled (b : KeptBlock) (f : Exec.Frame) : Prop
  /-- **Dequeue: the block's own call.** As for the deposit contract, with at most 16 records of 68 bytes. -/
  | dequeue (caller : f.sevm.caller = systemAddress) (empty : f.sevm.data = []) (fork : b.fork = .amsterdam)
      (state : f.post.state = sysState Exit.sysShape f.pre.state exitAddr)
      (output : f.post.output = Exit.sysOutput.drained (f.pre.getStorVal exitAddr)
        (f.pre.getStorVal exitAddr 2)
        (drainCount Exit.sysShape.cap.word (f.pre.getStorVal exitAddr 2) (f.pre.getStorVal exitAddr 3)).toNat)
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
  /-- **Fee read.** As for the deposit contract. -/
  | feeRead (caller : f.sevm.caller ≠ systemAddress) (empty : f.sevm.data = []) (value : f.sevm.value = 0)
      (active : f.pre.getStorVal exitAddr 0 ≠ B256.max)
      (output : f.post.output = (wordFee (quotedExcess 2 f.pre exitAddr)).toBytes)
      (storage : ∀ a, f.post.getStor a = f.pre.getStor a)
      (balance : ∀ a, f.post.getBal a = f.pre.getBal a)
      (logs : f.post.logs = f.pre.logs)

/-- **B-S2 at the deposit contract.** Every frame a kept history keeps at the builder deposit contract is the block's
own dequeue, a submission or a fee read. In particular no kept frame is a system call with calldata (the latch arm),
and no block before Amsterdam dequeues. -/
def B_S2_deposit : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    -- kept: a kept history (covered forks and Amsterdam) from a start holding both builder codes
    (_kept : CodesKept cfg start blocks stop)
    -- clean: no kept block has SYSTEM_ADDRESS as a sender or a 7702 authority, and none creates it
    (_clean : HistoryClean blocks)
    -- system: no code at SYSTEM_ADDRESS at the start
    (_system : SystemCodeAbsent start),
    ∀ b ∈ blocks, ∀ f ∈ b.keptAt depositAddr, DepositSettled b f

/-- **B-S2 at the exit contract.** Every frame a kept history keeps at the builder exit contract is the block's own
dequeue, a submission or a fee read. -/
def B_S2_exit : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    -- kept: a kept history (covered forks and Amsterdam) from a start holding both builder codes
    (_kept : CodesKept cfg start blocks stop)
    -- clean: no kept block has SYSTEM_ADDRESS as a sender or a 7702 authority, and none creates it
    (_clean : HistoryClean blocks)
    -- system: no code at SYSTEM_ADDRESS at the start
    (_system : SystemCodeAbsent start),
    ∀ b ∈ blocks, ∀ f ∈ b.keptAt exitAddr, ExitSettled b f

/-- **B-S2.** One statement for each builder contract. -/
def B_S2 : Prop := B_S2_deposit ∧ B_S2_exit

/-! ## B-S4: rooted in a recorded mainnet fact -/

/-- **The observation to record** at mainnet block 26,211,406, the block of the recorded creation transaction
`0xb2e7407f…2fe9` (`scripts/lift/certificates.json`): the tip header and the account reads. The storage fields are
whole-storage facts; JSON-RPC answers them through `eth_getProof`'s `storageHash` (the empty-trie root for the deposit
contract; the root of the one-entry trie `slot 0 ↦ 2^256 − 1` for the exit contract). Lean authenticates none of it
against a state root. The record is not taken yet: the state root joins `tip` when it is (registered provenance). -/
structure BuilderCheckpointObservation (checkpoint : BlockChain) : Prop where
  /-- The checkpoint's last header: number 26211406, hash 0x71b1…f661. -/
  tip : ∃ t, checkpoint.blocks.getLast? = some t ∧ t.header.number = 26211406 ∧
    t.header.hash = 0x71b1ba54e3d1c0d0f18381919861f75c04a6f3b2b860038da570b70240a3f661
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

/-- **B-S4.** (1) Exact delivery (the family's S3, `history_delivers_exactly`) for every kept history from the observed
checkpoint, under any chain configuration: what the blocks publish for each builder contract is, in order, a prefix of
what was submitted to it. (2) The record holds exactly what `ValidJointG` asks of its checkpoint: no code at
SYSTEM_ADDRESS, both codes, the deposit contract's empty storage and the exit contract's deployed storage. -/
def B_S4 : Prop :=
  (∀ {cfg : ChainConfig} {checkpoint stop : BlockChain} {blocks : List KeptBlock}
    -- obs: the recorded mainnet facts at block 26,211,406
    (_obs : BuilderCheckpointObservation checkpoint)
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
  (∀ {checkpoint : BlockChain} (_obs : BuilderCheckpointObservation checkpoint),
    checkpoint.state.getCode systemAddress = ByteArray.empty ∧
    checkpoint.state.getCode Deposit.Creation.address = Deposit.code ∧
    checkpoint.state.getStor Deposit.Creation.address = Stor.empty ∧
    checkpoint.state.getCode Exit.Creation.address = Exit.code ∧
    checkpoint.state.getStor Exit.Creation.address = Exit.deployedStorage)

end Blanc.Corpus.Freeze.Builder
