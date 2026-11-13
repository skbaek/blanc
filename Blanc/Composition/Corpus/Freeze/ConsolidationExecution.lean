import Blanc.Composition.ConsolidationRequestPublicHeadlines
import Blanc.Composition.ConsolidationRequestPublicHistory
import Blanc.ExecutionKeptValue

/-!
# Freeze record (G0, part cb): EIP-7251 execution cells C-S2, C-S6, C-S8

Frozen statement definitions (`def … : Prop`) from G0 against Blanc `7f2a69ba` and Jaune `c30cf0a5`,
classified in `scripts/check-layering.py`, imported by `Blanc.lean`, and proved in `Blanc/Composition/`.

Every statement ranges over kept histories (`Blanc.KeptHistory`) and the frames they keep at the predeploy
(`KeptBlock.keptAt`): a frame rolled back by its own or an ancestor's failure is not among them.
-/

namespace Blanc.Corpus.Freeze.Consolidation

open Jaune Blanc
open Blanc.Composition.ConsolidationRequestPublic

/-! ## C-S2: what succeeds -/

/-- **What a settled frame at the EIP-7251 predeploy is.** Exactly one of three, each with its storage, log, output and
balance effect. The frame's own code moves no balance in any arm: the value a call carries is credited to the predeploy
before the frame starts, so `f.pre` already holds it (C-S6 states the history-level consequence). -/
inductive Settled (f : Exec.Frame) : Prop
  /-- **Dequeue.** The caller is SYSTEM_ADDRESS, whatever the calldata and value. The world state after is
  `sysState`: the four bookkeeping words updated as the bytes define, no other slot, account, balance or code touched.
  The output is `drained`, with no ordering premise on the pointers: `min(2, (tail − head) mod 2^256)` records of 116
  bytes, record `i` read from the four slots from `4 + 4·(head + i)` (word arithmetic). No log is emitted. -/
  | dequeue (caller : f.sevm.caller = systemAddress)
      (dynamic : f.sevm.isStatic = false)
      (state : f.post.state = Lift.RequestSystem.sysState
        Lift.SystemExecution.ConsolidationRequest.Amsterdam.sysShape f.pre.state addr)
      (output : f.post.output = Lift.ConsolidationRequest.drained (f.pre.getStorVal addr))
      (logs : f.post.logs = f.pre.logs)
  /-- **Submission.** 96 bytes from a caller other than SYSTEM_ADDRESS, in a non-static frame, slot 0 off the
  inhibitor, value at least the quoted fee. The record is stored at the tail and the count and tail are bumped
  (`submittedStorage`); no other account's storage changes; no balance changes inside the frame; one topicless log of
  the 116 record bytes is appended; the output is the one the frame started with. -/
  | submission (caller : f.sevm.caller ≠ systemAddress) (length : f.sevm.data.length = 96)
      (dynamic : f.sevm.isStatic = false) (active : f.pre.getStorVal addr 0 ≠ B256.max)
      (paid : quotedFee (f.pre.getStorVal addr 0) ≤ f.sevm.value.toNat)
      (storage : f.post.getStor addr = Lift.ConsolidationRequest.submittedStorage f.sevm (f.pre.getStor addr))
      (others : ∀ a, a ≠ addr → f.post.getStor a = f.pre.getStor a)
      (balance : ∀ a, f.post.getBal a = f.pre.getBal a)
      (logs : f.post.logs = f.pre.logs ++ [submissionLog f.sevm])
      (output : f.post.output = f.pre.output)
  /-- **Fee read.** Empty calldata and no value from a caller other than SYSTEM_ADDRESS, slot 0 off the inhibitor.
  Returns the quoted fee as one word; no storage, balance or log changes. -/
  | feeRead (caller : f.sevm.caller ≠ systemAddress) (empty : f.sevm.data = []) (value : f.sevm.value = 0)
      (active : f.pre.getStorVal addr 0 ≠ B256.max)
      (output : f.post.output = (quotedFee (f.pre.getStorVal addr 0)).toB256.toBytes)
      (storage : ∀ a, f.post.getStor a = f.pre.getStor a)
      (balance : ∀ a, f.post.getBal a = f.pre.getBal a)
      (logs : f.post.logs = f.pre.logs)

/-- **C-S2. What succeeds at EIP-7251.** Every frame a kept history at covered forks keeps at the predeploy is a
dequeue, a submission or a fee read, with the stated effects. Nothing else is kept. -/
def C_S2 : Prop :=
  ∀ {cfg : ChainConfig} {start final : BlockChain} {blocks : List KeptBlock}
    -- kept: the blocks are a kept history from `start` to `final`
    (_kept : KeptHistory cfg start blocks final)
    -- code: the canonical 414 bytes sit at the predeploy at the start
    (_code : installed start.state)
    -- covered: every block is at Prague, Osaka, BPO1 or BPO2
    (_covered : ∀ b ∈ blocks, CoveredFork b.fork),
    ∀ b ∈ blocks, ∀ f ∈ b.keptAt addr, Settled f

/-! ## C-S6: value is kept -/

/-- The value every frame the history keeps at the predeploy carried in. -/
noncomputable def keptValue (blocks : List KeptBlock) : Nat :=
  ((blocks.flatMap (KeptBlock.keptAt addr)).map fun f => f.sevm.value.toNat).sum

/-- The value the history's committed submissions carried in: the kept 96-byte user calls, the frames `submissions`
reads. -/
noncomputable def submissionsValue (blocks : List KeptBlock) : Nat :=
  (((blocks.flatMap (KeptBlock.keptAt addr)).filter
    fun f => decide (f.sevm.caller ≠ systemAddress ∧ f.sevm.data.length = 96)).map fun f => f.sevm.value.toNat).sum

/-- **C-S6. Value is kept.** Over every kept history at covered forks from a state holding the canonical code, the
predeploy's final balance is at least its starting balance plus the value of every committed submission; indeed plus
the value of every kept frame there. (The internal balance-silence lemma stays fork-generic across kept histories; the
public statement scopes to covered forks `Prague..BPO2` per §2/§5 so Amsterdam creates no public maintenance
obligation.) -/
def C_S6 : Prop :=
  ∀ {cfg : ChainConfig} {start final : BlockChain} {blocks : List KeptBlock}
    -- kept: the blocks are a kept history from `start` to `final`
    (_kept : KeptHistory cfg start blocks final)
    -- code: the canonical 414 bytes sit at the predeploy at the start
    (_code : installed start.state)
    -- covered: every block is at Prague, Osaka, BPO1 or BPO2
    (_covered : ∀ b ∈ blocks, CoveredFork b.fork)
    -- noSender: no kept block's transaction is sent by the predeploy
    (_noSender : ∀ b ∈ blocks, NoSenderAt addr b.run.senders)
    -- roots: every root message opens on a world whose balances sum below 2^256
    (_roots : HistoryRootsFit blocks)
    -- credits: no tip and no withdrawal credit to the predeploy wraps its balance
    (_credits : HistoryCreditsFit addr blocks),
    (start.state.bal addr).toNat + submissionsValue blocks ≤ (final.state.bal addr).toNat ∧
    (start.state.bal addr).toNat + keptValue blocks ≤ (final.state.bal addr).toNat

/-! ## C-S8: delivery is bounded -/

/-- The frame a block's request step ran at the predeploy: its first kept frame there with the system caller. -/
def requestFrame (b : KeptBlock) : Option Exec.Frame :=
  (b.keptAt addr).find? fun f => decide (f.sevm.caller = systemAddress)

/-- The stored queue at a block's request boundary: the queue in the storage its request step read; empty if the block
kept no such frame. -/
def queueAtRequests (b : KeptBlock) : List Bytes :=
  match requestFrame b with
  | some f => storedQueue (Devm.getStor f.pre addr).get
  | none => []

/-- The consolidation records one block published: its type-2 request bytes cut into 116-byte records. -/
def blockRecords (b : KeptBlock) : List Bytes := records116 (blockConsolidations b)

/-- **C-S8. Delivery is bounded.** Take any kept history at covered forks from the predeploy's start, under the FIFO
statement's premises, that contains block `j` (B) and block `j + q / 2` (D). If record `r` sits at position `q` of the
stored queue at B's request boundary, then D publishes `r` as its record `q % 2`, preceded in order by exactly B's
queue entries from position `2 * (q / 2)`; and `r` is the history's committed submission number
`|records published before B| + q`. Nothing is claimed about a history too short to contain D. -/
def C_S8 : Prop :=
  ∀ {cfg : ChainConfig} {start final : BlockChain} {blocks : List KeptBlock}
    -- kept: the blocks are a kept history from `start` to `final`
    (_kept : KeptHistory cfg start blocks final)
    -- covered: every block is at Prague, Osaka, BPO1 or BPO2
    (_covered : ∀ b ∈ blocks, CoveredFork b.fork)
    -- root: canonical code, slots 0 to 3 at the inhibitor, 0, 0, 0, and no code at SYSTEM_ADDRESS, at the start
    (_root : CheckpointStart start.state)
    -- clean: no kept block has SYSTEM_ADDRESS as a sender or a 7702 authority, and none creates it
    (_clean : HistoryClean blocks)
    -- cap: at most 2^253 committed submissions, so no record slot wraps onto slots 0 to 3
    (_cap : (submissions blocks).length ≤ 2 ^ 253)
    {j q : Nat} {B D : KeptBlock} {r : Bytes}
    -- atB: B is block `j` of the history
    (_atB : blocks[j]? = some B)
    -- atD: the history contains the destination block, `q / 2` blocks after B
    (_atD : blocks[j + q / 2]? = some D)
    -- queued: `r` is at position `q` of the stored queue at B's request boundary
    (_queued : (queueAtRequests B)[q]? = some r),
    (blockRecords D)[q % 2]? = some r ∧
    (∀ i ≤ q % 2, (blockRecords D)[i]? = (queueAtRequests B)[2 * (q / 2) + i]?) ∧
    (submissions blocks)[(emissions (blocks.take j)).length + q]? = some r

/-! ## C-S8 negative control -/

/-- The `⌊q / 2⌋` queue-latency bound when drain capacity is `cap` (`cap = 2` for EIP-7251) and every step through
`j + q / 2` drains: if `r` sits at position `q` of the queue after `j` steps, step `j + q / 2` delivers `r` at record
slot `q % 2`. -/
def QueueLatencyAtCap (cap : Nat) : Prop :=
  ∀ (st : Lift.BuilderRequest.QueueState Bytes) (es : List (Lift.RequestQueue.Effect Bytes))
    (j q : Nat) (r : Bytes) (ds : List Bytes),
    (∀ k ≤ j + q / 2, ∃ next, es[k]? = some (.drain next)) →
    ((Lift.RequestQueue.run cap st (es.take j)).queue)[q]? = some r →
    (Lift.RequestQueue.deliveries cap st es)[j + q / 2]? = some ds →
    ds[q % 2]? = some r

/-- The bytes a mutated EIP-7251 system dequeue with per-block capacity `1` (instead of `2`) returns from storage
reader `rd`. -/
def drainedCap1 (rd : B256 → B256) : Bytes :=
  Lift.ConsolidationRequest.sysOutput.drained rd (rd 2)
    (Lift.RequestSystem.drainCount 1 (rd 2) (rd 3)).toNat

/-- **C-S8 negative control.**
(1) On the queue model, `QueueLatencyAtCap 2` holds, whereas mutating the per-block drain capacity to `1` falsifies
`QueueLatencyAtCap 1` on a 2-entry queue (`j = 0, q = 1`, destination `0 + 1 / 2 = 0`, slot `1 % 2 = 1`).
(2) Concretely on contract storage `s` holding a 2-entry stored queue `[r₀, r₁]` (`r₀ ≠ r₁`, each 116 bytes, so
`(storedQueue s.get)[1]? = some r₁` at `q = 1`), the real `cap = 2` dequeue output `drained` publishes `r₁` at record
`1 % 2 = 1` in block `B + ⌊1 / 2⌋ = B`, whereas the `cap = 1` mutant `drainedCap1` publishes only `[r₀]`
(`(records116 (drainedCap1 s.get))[1 % 2]? ≠ some r₁`), and a mutated publication fold that omits type-2 requests
publishes `[]` (`(records116 [])[1 % 2]? ≠ some r₁`). -/
def C_S8_control : Prop :=
  QueueLatencyAtCap 2 ∧
  ¬ QueueLatencyAtCap 1 ∧
  ∃ (s : Stor) (r₀ r₁ : Bytes),
    storedQueue s.get = [r₀, r₁] ∧ r₀.length = 116 ∧ r₁.length = 116 ∧ r₀ ≠ r₁ ∧
    (storedQueue s.get)[1]? = some r₁ ∧
    (records116 (Lift.ConsolidationRequest.drained s.get))[1 % 2]? = some r₁ ∧
    records116 (drainedCap1 s.get) = [r₀] ∧
    (records116 (drainedCap1 s.get))[1 % 2]? ≠ some r₁ ∧
    (records116 [])[1 % 2]? ≠ some r₁

end Blanc.Corpus.Freeze.Consolidation
