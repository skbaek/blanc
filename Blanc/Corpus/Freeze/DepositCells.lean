import Blanc.Corpus.Freeze.DepositLedger
import Blanc.ExecutionKeptConfigured
import Blanc.ExecutionKeptValue
-- The deployed-bytes vocabulary of `corpus-v1-20261105`, restored by `claude/pcc-d-restore`:
import Blanc.Lift.BeaconDeposit.HistDeployment
import Blanc.Lift.BeaconDeposit.Safe
import Blanc.Lift.BeaconDeposit.Views

/-!
# G0 freeze, part d: the deposit contract's execution cells and the joined D-S9 statements

**Elaboration waits for the revival.** This module imports the deployed-bytes family of
`corpus-v1-20261105` (`Blanc.Lift.BeaconDeposit.*`, `Blanc.BeaconDeposit*`), which is not on
Blanc main `7f2a69ba`; the revival branch `claude/pcc-d-restore` restores it. Every name below
from that family is read from the archive tag: `code` (`Lift/BeaconDeposit/Cert.lean:10`),
`Creation.depositAddress` (`Creation/Deploy.lean:112`), `SolInv`, `solAcc`, `solCountSlot`,
`solBranchSlot` (`Layout.lean`), `argBytes`, `argRoot`, `DepositDecodable`, `frameNode`
(`BodySpec.lean`, `DepositArgs.lean`, `Refines.lean`), `BeaconDeploymentTo` and its `trace`,
`deposits`, `modern` (`HistDeployment.lean:40`), `committedNodesIn`
(`HistCommittedHistory.lean:15`), and from the specification modules `BeaconDeposit.deposit`,
`DepositEvent`, `depositEventLog`, `abiDepositEvent`, `abiDynamicBytesReturn`, `abiBoolReturn`,
`le64`, `Acc.root`, `supportsInterface`, the four selectors and the two interface ids
(`BeaconDepositModel.lean`, `BeaconDepositCore.lean`). The consensus half
(`Blanc.Corpus.Freeze.DepositLedger`) elaborates on main.

New vocabulary, defined here minimally: `frameLogs`, `depositRecord`, `frameRecords`,
`DepositCodeAt`, `KeptAtForks`, `DepositOutcome`, `frameDepositData`, `committedDepositDataIn`,
`DepositJoint`, `AnchorLedgerD`.
-/

namespace Blanc.Corpus.Freeze.Deposit

open Jaune JauneConsensus Blanc Blanc.ExecutionTrace Blanc.Lift.BeaconDeposit

/-- The deposit contract's address (Jaune's `depositContractAddress`; the archive's
`Creation.depositAddress` is the same literal). -/
abbrev depositAddr : Adr := depositContractAddress

/-- The logs a frame appended (its own and its descendants'). -/
def frameLogs (fr : Exec.Frame) : List Log := fr.post.logs.drop fr.pre.logs.length

/-- The 192-byte request record of a deposit event: Jaune's `extractDepositData` output, and the
SSZ serialization of the consensus `DepositRequest` it stands for. -/
def depositRecord (ev : BeaconDeposit.DepositEvent) : Bytes :=
  ev.pubkey ++ ev.withdrawal_credentials ++ ev.amount ++ ev.signature ++ ev.index

/-- The deposit-topic logs at the deposit address among `logs`, as Jaune's parse selects them. -/
def depositLogs (logs : List Log) : List Log :=
  logs.filter fun log => decide (log.address = depositAddr ∧
    log.topics[0]? = some depositEventSignatureHash)

/-- Every kept block of a list ran at a fork satisfying `F`. -/
def KeptAtForks (F : Fork → Prop) (blocks : List KeptBlock) : Prop := ∀ b ∈ blocks, F b.fork

/-- The deposit code at the deposit address, the frame law the value fold needs. -/
def DepositCodeAt (σ : State) : Prop := σ.getCode depositAddr = code

/-! ## D-S1 and D-S10: the log shape and the parse -/

/-- **D-S1 / D-S10, frame half (log shape).** Over every kept history at forks `F` from a state
with the deposit code installed, every deposit-topic log a kept frame at the deposit address
appended is one Jaune's `extractDepositData` accepts, with a 192-byte record. A safety statement
about settled frames; no gas is stated. -/
def LogShape (F : Fork → Prop) : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock},
    -- the blocks are a kept history from `start`
    KeptHistory cfg start blocks stop →
    -- each block ran at a fork in `F`
    KeptAtForks F blocks →
    -- the deposit code is installed at the start
    DepositCodeAt start.state →
    ∀ b ∈ blocks, ∀ fr ∈ b.keptAt depositAddr, ∀ log ∈ depositLogs (frameLogs fr),
      ∃ ev, log = BeaconDeposit.depositEventLog depositAddr ev ∧
        extractDepositData log.data = .ok (depositRecord ev) ∧ (depositRecord ev).length = 192

/-- The request records a kept frame at the deposit address contributes: those of its
deposit-topic logs, in order. -/
def frameRecords (fr : Exec.Frame) : List Bytes :=
  (depositLogs (frameLogs fr)).filterMap fun log =>
    match extractDepositData log.data with
    | .ok r => some r
    | .error _ => none

/-- **D-S1 / D-S10, block half (the parse cannot fail).** For one block body at a fork in `F`,
whose transaction stage ran (`TransactionsRoots`, the receipt-producing trace) from the empty
block output, with the deposit code installed: the parse the request pass makes succeeds, and its
bytes are the records of the transactions' kept frames at the deposit address, in order. Receipt
completeness (one receipt per transaction, at its index key) and attribution (only frames at the
deposit address, running its code, write logs there) are derived, not assumed. With this,
`RequestPhaseAmsterdam.request_pass` drops its `parsed` premise (D-S10, `F = (· = .amsterdam)`). -/
def ParseSucceeds (F : Fork → Prop) : Prop :=
  ∀ (benv : Benv) (txis : List (Nat × Tx)) (bal : BalBuilder) (final : Benv) (out : BlockOutput)
    (senders : List (Adr × Tx)) (roots : List Root) (wds : List Withdrawal),
    -- the body's fork is in `F`
    F benv.stat.fork →
    -- the deposit code is installed when the transactions start
    DepositCodeAt benv.state →
    -- the transaction stage ran from the empty block output (the pre-calls' access list only)
    TransactionsRoots txis benv { BlockOutput.init with bal := bal } final out senders roots →
    parseDepositRequests (withdrawalsPass benv.stat.rules final out wds).2 =
      .ok ((roots.flatMap (Root.keptAt depositAddr)).flatMap frameRecords).flatten

/-- **D-S1** (Prague to BPO2): the log shape and the parse, at covered forks. -/
def D1 : Prop := LogShape CoveredFork ∧ ParseSucceeds CoveredFork

/-- **D-S10** (Amsterdam): the log-shape half only, so that `request_pass` drops its parsing
premise. -/
def D10 : Prop := LogShape (· = .amsterdam) ∧ ParseSucceeds (· = .amsterdam)

/-- **D-S1 / D-S10 control.** A closed runtime at the deposit address that emits one short
deposit-topic log, with every other premise of `ParseSucceeds` met (correct address, topic,
existing receipt), makes the parse fail: the CODE premise is needed. Stated at Prague (D-S1) and
at Amsterdam (D-S10). -/
def ShortLogControl (F : Fork → Prop) : Prop :=
  ∃ (shortCode : ByteArray) (benv : Benv) (txis : List (Nat × Tx)) (bal : BalBuilder) (final : Benv)
    (out : BlockOutput) (senders : List (Adr × Tx)) (roots : List Root) (wds : List Withdrawal),
    F benv.stat.fork ∧ benv.state.getCode depositAddr = shortCode ∧
    TransactionsRoots txis benv { BlockOutput.init with bal := bal } final out senders roots ∧
    (∃ log ∈ out.blockLogs, log.address = depositAddr ∧
      log.topics[0]? = some depositEventSignatureHash) ∧
    ∃ e, parseDepositRequests (withdrawalsPass benv.stat.rules final out wds).2 = .error e

/-! ## D-S2: what succeeds -/

/-- The four successful outcomes of a frame at the deposit bytes. -/
inductive DepositOutcome where
  | deposit | getDepositRoot | getDepositCount | supportsInterface

/-- **D-S2 classification of one frame**, given the history `history` its entry storage is the
accumulator of. Exactly one outcome holds, with its storage, log, output and balance effect;
nothing else succeeds. -/
def Classified (fr : Exec.Frame) (history : List B256) : DepositOutcome → Prop
  | .deposit =>
    Sevm.selector fr.sevm = BeaconDeposit.depositSelector ∧ DepositDecodable fr.sevm ∧
    ∃ s' ev, BeaconDeposit.deposit Bytes.sha256 (solAcc (fr.pre.getStor depositAddr))
        (argBytes fr.sevm 0) (argBytes fr.sevm 1) (argBytes fr.sevm 2) (argRoot fr.sevm)
        fr.sevm.value.toNat = .ok (s', ev) ∧
      solAcc (fr.post.getStor depositAddr) = s' ∧
      SolInv (fr.post.getStor depositAddr) (history ++ [frameNode fr.sevm]) ∧
      (∃ h v, h < 32 ∧ fr.post.getStor depositAddr =
        ((fr.pre.getStor depositAddr).set solCountSlot (history.length + 1)).set (solBranchSlot h) v) ∧
      (∀ a, a ≠ depositAddr → fr.post.getStor a = fr.pre.getStor a) ∧
      frameLogs fr = [BeaconDeposit.depositEventLog depositAddr ev] ∧
      fr.post.output = [] ∧ fr.post.getBal depositAddr = fr.pre.getBal depositAddr
  | .getDepositRoot =>
    Sevm.selector fr.sevm = BeaconDeposit.getDepositRootSelector ∧ fr.sevm.value = 0 ∧
    fr.post.output = (BeaconDeposit.Acc.root Bytes.sha256 (solAcc (fr.pre.getStor depositAddr))).toBytes ∧
    (∀ a, fr.post.getStor a = fr.pre.getStor a) ∧ frameLogs fr = [] ∧
    fr.post.getBal depositAddr = fr.pre.getBal depositAddr
  | .getDepositCount =>
    Sevm.selector fr.sevm = BeaconDeposit.getDepositCountSelector ∧ fr.sevm.value = 0 ∧
    fr.post.output = BeaconDeposit.abiDynamicBytesReturn (BeaconDeposit.le64 history.length) ∧
    (∀ a, fr.post.getStor a = fr.pre.getStor a) ∧ frameLogs fr = [] ∧
    fr.post.getBal depositAddr = fr.pre.getBal depositAddr
  | .supportsInterface =>
    Sevm.selector fr.sevm = BeaconDeposit.supportsInterfaceSelector ∧ fr.sevm.value = 0 ∧
    fr.post.output = BeaconDeposit.abiBoolReturn (BeaconDeposit.supportsInterface
      (BeaconDeposit.erc165InterfaceId.toBytes.take 4) (BeaconDeposit.depositInterfaceId.toBytes.take 4)
      ((Sevm.dataWord fr.sevm 4).toBytes.take 4)) ∧
    (∀ a, fr.post.getStor a = fr.pre.getStor a) ∧ frameLogs fr = [] ∧
    fr.post.getBal depositAddr = fr.pre.getBal depositAddr

/-- **D-S2.** Over the whole retained history from the actual deployment block to `B`, every
settled frame at the deposit address is exactly one of the named outcomes, with its entry storage
the accumulator of exactly the committed deposits before it (`SolInv` derived from the history,
not assumed). -/
def D2 : Prop :=
  ∀ {B : BlockChain} (d : BeaconDeploymentTo B), ∀ fr ∈ d.trace.settledFrames,
    fr.sevm.currentTarget = depositAddr →
    ∃ history, SolInv (fr.pre.getStor depositAddr) history ∧
      ∃! o : DepositOutcome, Classified fr history o

/-! ## D-S6: value is kept -/

/-- **D-S6.** Over every kept history from a state with the deposit code installed, in which the
deposit address sends no transaction, under the two virtual certainties of B's value row (root
worlds sum below `2 ^ 256`, no credit to the address wraps): the contract's balance at the end is
at least its start plus the value of every kept frame at it; every kept frame with the deposit
selector carried at least 1 ETH, an exact multiple of a gwei, at most `2^64 − 1` gwei, and the
amount its event records (little-endian gwei) times `10^9` is that value. -/
def D6 : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock},
    KeptHistory cfg start blocks stop → DepositCodeAt start.state →
    -- the deposit address sends no transaction
    (∀ b ∈ blocks, NoSenderAt depositAddr b.run.senders) →
    -- B's virtual certainties
    HistoryRootsFit blocks → HistoryCreditsFit depositAddr blocks →
    (start.state.bal depositAddr).toNat +
        ((blocks.flatMap (KeptBlock.keptAt depositAddr)).map fun f => f.sevm.value.toNat).sum ≤
      (stop.state.bal depositAddr).toNat ∧
    ∀ b ∈ blocks, ∀ fr ∈ b.keptAt depositAddr, Sevm.selector fr.sevm = BeaconDeposit.depositSelector →
      BeaconDeposit.oneEther ≤ fr.sevm.value.toNat ∧ fr.sevm.value.toNat % BeaconDeposit.oneGwei = 0 ∧
      fr.sevm.value.toNat / BeaconDeposit.oneGwei ≤ 2 ^ 64 - 1 ∧
      ∀ ev, frameLogs fr = [BeaconDeposit.depositEventLog depositAddr ev] →
        ev.amount = BeaconDeposit.le64 (fr.sevm.value.toNat / BeaconDeposit.oneGwei)

/-! ## The deposit joint chain -/

/-- A valid deposit joint chain: the deployment record to the anchor's execution chain, a joint
run from the anchor on mainnet's execution configuration, and the deployment record's modern
exclusions extended over the run. Every premise is a field. -/
structure DepositJoint {P : Preset} (ccfg : Config) (bls : Bool) (anchor final : JointState P) : Type where
  deployment : BeaconDeploymentTo anchor.exec
  run : JointRun mainnetChainConfig ccfg bls anchor final
  /-- No authorization over the run recovers to a system contract or `0x02`. -/
  systemNoAuthority : ∀ p ∈ systemContracts, (run.toExec deployment.modern).NoAuthorityAt p.1
  noAuthority : (run.toExec deployment.modern).NoAuthorityAt 2
  /-- No frame without a code address targets `0x02` over the run. -/
  noFrame : ∀ root ∈ (run.toExec deployment.modern).rawFrames, root.sevm.codeAddress = none →
    root.sevm.currentTarget ≠ (2 : Adr)

/-- The committed deposits before the anchor (the deployment record's span). -/
noncomputable def DepositJoint.E₀ {P : Preset} {ccfg : Config} {bls : Bool} {anchor final : JointState P}
    (v : DepositJoint ccfg bls anchor final) : Nat := v.deployment.deposits.length

/-- The data a kept deposit frame submitted: key, credentials, signature, and value in gwei. -/
def frameDepositData (fr : Exec.Frame) : Bytes × Bytes × Bytes × Nat :=
  (argBytes fr.sevm 0, argBytes fr.sevm 1, argBytes fr.sevm 2, fr.sevm.value.toNat / BeaconDeposit.oneGwei)

/-- The committed deposits' data over a historical trace, in the order of `committedNodesIn`. -/
noncomputable def committedDepositDataIn {cfg : ChainConfig} {D B : BlockChain}
    (trace : ConfiguredHistoryTraceIn HistFork cfg D B) : List (Bytes × Bytes × Bytes × Nat) :=
  (trace.settledFrames.filter fun fr => decide (fr.sevm.currentTarget = depositAddr ∧
    Sevm.selector fr.sevm = BeaconDeposit.depositSelector)).map frameDepositData

/-- **D's anchor ledger.** The consensus anchor ledger, and each tag `some n` names a committed
deposit `n < E₀` of the deployment span whose key, credentials, signature and gwei amount are the
entry's. With every tag `none` it is `AnchorLedger` alone. -/
def AnchorLedgerD {P : Preset} {ccfg : Config} {bls : Bool} {anchor final : JointState P}
    (v : DepositJoint ccfg bls anchor final) (tq₀ : TQueue) : Prop :=
  AnchorLedger anchor tq₀ ∧
  ∀ n e, (some n, e) ∈ tq₀ → n < v.E₀ ∧
    (committedDepositDataIn v.deployment.trace)[n]? =
      some (e.pubkey.toArray.toList, e.withdrawal_credentials.toArray.toList,
        e.signature.toArray.toList, e.amount.toNat)

/-! ## D-S9 delivery, and D-S8 -/

/-- **D-S9 delivery.** On a valid deposit joint chain, step `j`'s beacon block carries, as its
deposit requests serialized in order, exactly the request records of the kept frames at the
deposit address of step `j`'s own execution block; and the run's requests carry consecutive
indices from `E₀`, the contract's count at the anchor. -/
def D9Delivery : Prop :=
  ∀ {P : Preset} {ccfg : Config} {bls : Bool} {anchor final : JointState P}
    (v : DepositJoint (P := P) ccfg bls anchor final),
    (∀ j (D : JointRunStep (P := P) mainnetChainConfig ccfg bls), v.run.steps[j]? = some D →
      (stepDepositRequests D).map Ssz.serialize =
        (D.stepTrace.trace.kept.keptAt depositAddr).flatMap frameRecords) ∧
    (runDepositRequests v.run).map (fun dr => dr.index.toNat) =
      List.range' v.E₀ (runDepositRequests v.run).length

/-- **D-S8 (execution half).** The event of every kept deposit frame of a block becomes a deposit
request in that same block's requests: the block's type-0 request is the records of its kept
deposit frames (when there is one). Nothing about when consensus credits it. -/
def D8 : Prop :=
  ∀ {P : Preset} {ccfg : Config} {bls : Bool} {anchor final : JointState P}
    (v : DepositJoint (P := P) ccfg bls anchor final),
    ∀ j (D : JointRunStep (P := P) mainnetChainConfig ccfg bls), v.run.steps[j]? = some D →
      ∀ fr ∈ D.stepTrace.trace.kept.keptAt depositAddr, ∀ r ∈ frameRecords fr,
        ∃ dr ∈ stepDepositRequests D, Ssz.serialize dr = r

/-- **D-S9 delivery control.** A joint step whose beacon block's execution requests differ from
those its own execution block produces is refused (the engine's requests-hash comparison in the
transition, or, under a hash collision, the list comparison). W's `jointStep_rejects_of_requests_ne`
in D's statement form. -/
def D9DeliveryControl : Prop :=
  ∀ {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s : JointState P}
    {b : AnySignedBlock P} {req : NewPayloadRequest P} {f : Jaune.Fork} {post : BlockChain}
    {st : State} {bout : BlockOutput},
    NewPayloadRequest.ofBlock b.2.message = .ok req →
    cfg.forkAt (payloadToBlock req).header.number (payloadToBlock req).header.timestamp = .ok f →
    applyBody (initBenv f s.exec (payloadToBlock req).header) (payloadToBlock req).txs
      (payloadToBlock req).ommers (payloadToBlock req).wds = .ok (st, bout) →
    bout.requests ≠ req.executionRequests →
    ∀ s', jointStep cfg ccfg bls s b ≠ .ok s'

/-! ## D-S9 joined: fate, credit and conservation from the contract -/

/-- **D-S9 fate and credit, joined.** On a valid deposit joint chain with BLS on and D's anchor
ledger, the consensus half holds without its freshness premise (derived from delivery and the
anchor ledger), and each run request's amount is its kept deposit frame's value in gwei. Every
committed deposit `n` of the joint history from deployment then has exactly one fate: `n < E₀`
and untagged: before the anchor, no claim (the Eth1-bridge deposits and the pre-anchor requests
the anchor ledger does not attribute); tagged at the anchor or `n ≥ E₀` (request `k` of step `j`
at feed position `n − E₀`): applied with exactly one outcome or still pending, as `D9Fate`. -/
def D9FateJoined : Prop :=
  ∀ {P : Preset} {ccfg : Config} {anchor final : JointState P}
    (v : DepositJoint (P := P) ccfg true anchor final) (tq₀ : TQueue),
    AnchorLedgerD v tq₀ →
    RunIndicesFresh v.run tq₀ ∧
    ∀ j (D : JointRunStep (P := P) mainnetChainConfig ccfg true), v.run.steps[j]? = some D →
      ∀ k dr, (stepDepositRequests D)[k]? = some dr →
        ∃ fr ∈ D.stepTrace.trace.kept.keptAt depositAddr,
          Sevm.selector fr.sevm = BeaconDeposit.depositSelector ∧
          dr.amount.toNat * 10 ^ 9 = fr.sevm.value.toNat ∧
          dr.pubkey.toArray.toList = argBytes fr.sevm 0 ∧
          dr.withdrawal_credentials.toArray.toList = argBytes fr.sevm 1 ∧
          dr.signature.toArray.toList = argBytes fr.sevm 2

/-- **D-S9 conservation, joined.** On a valid deposit joint chain with BLS on and D's anchor
ledger, the Wei credited from deposit-request occurrences along the run is at most what the
contract was paid for them: the tagged anchor occurrences' payments plus every run deposit's. -/
def D9ConservationJoined : Prop :=
  ∀ {P : Preset} {ccfg : Config} {anchor final : JointState P}
    (v : DepositJoint (P := P) ccfg true anchor final) (tq₀ : TQueue),
    AnchorLedgerD v tq₀ →
    ∃ tqF ap, runLedger 0 v.run.steps tq₀ [] = .ok (tqF, ap) ∧
      creditedTotal (jointCtx ccfg true) ap * 10 ^ 9 ≤
        taggedTotal tq₀ * 10 ^ 9 +
          ((v.run.steps.flatMap fun D => D.stepTrace.trace.kept.keptAt depositAddr).filter
            (fun fr => decide (Sevm.selector fr.sevm = BeaconDeposit.depositSelector))).foldr
            (fun fr acc => fr.sevm.value.toNat + acc) 0

end Blanc.Corpus.Freeze.Deposit
