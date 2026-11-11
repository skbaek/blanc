import Blanc.Corpus.Freeze.DepositLedger
import Blanc.ExecutionKeptConfigured
import Blanc.ExecutionKeptValue
-- The deployed-bytes vocabulary of `corpus-v1-20261105`, restored by `claude/pcc-d-restore`:
import Blanc.Lift.BeaconDeposit.HistDeployment
import Blanc.Lift.BeaconDeposit.Safe
import Blanc.Lift.BeaconDeposit.Views

/-!
# G0 freeze, part d: the deposit contract's execution cells and the joined D-S9 statements

This module imports the revived deployed-bytes family (`Blanc.Lift.BeaconDeposit.*`,
`Blanc.BeaconDeposit*`, restored by `claude/pcc-d-restore`): `code` (`Lift/BeaconDeposit/Cert.lean`),
`Creation.depositAddress` (`Creation/Deploy.lean`), `SolInv`, `solAcc`, `solCountSlot`,
`solBranchSlot` (`Layout.lean`), `argBytes`, `argRoot`, `DepositDecodable`, `frameNode`,
`committedFrameNodes` (`BodySpec.lean`, `DepositArgs.lean`, `Refines.lean`, `CommittedReplay.lean`),
`BeaconDeploymentTo` and its `trace`, `deposits`, `modern` (`HistDeployment.lean`),
`committedNodesIn` (`HistCommittedHistory.lean`), and from the specification modules
`BeaconDeposit.deposit`, `DepositEvent`, `depositEventLog`, `abiDynamicBytesReturn`,
`abiBoolReturn`, `le64`, `Acc.root`, `supportsInterface`, the four selectors and the two interface
ids (`BeaconDepositModel.lean`, `BeaconDepositCore.lean`).

New vocabulary, defined here minimally: `frameLogs`, `depositRecord`, `frameRecords`,
`DepositCodeAt`, `KeptAtForks`, `DepositOutcome`, `Classified`, `depositWithoutFloor`,
`concatConfiguredHistory`, `DepositJoint`, `PreAnchorApplied`, `AnchorLedgerD`, `frameDepositData`,
`committedDepositDataIn`.
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
def KeptAtForks (F : Jaune.Fork → Prop) (blocks : List KeptBlock) : Prop := ∀ b ∈ blocks, F b.fork

/-- The deposit code at the deposit address, the frame law the value fold needs. -/
def DepositCodeAt (σ : State) : Prop := σ.getCode depositAddr = code

/-! ## D-S1 and D-S10: the log shape and the parse -/

/-- **D-S1 / D-S10, frame half (log shape).** Over every kept history at forks `F` from a state
with the deposit code installed, every deposit-topic log a kept frame at the deposit address
appended is one Jaune's `extractDepositData` accepts, with a 192-byte record. A safety statement
about settled frames; no gas is stated. -/
def LogShape (F : Jaune.Fork → Prop) : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock},
    KeptHistory cfg start blocks stop →
    KeptAtForks F blocks →
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
whose transaction stage ran (`TransactionsRoots` over `txs.putIndex`, matching `applyBody`'s
consecutive 0-based receipt keys) from the empty block output, with the deposit code installed:
the parse the request pass makes succeeds, and its bytes are the records of the transactions' kept
frames at the deposit address, in order. Receipt completeness (one receipt per transaction, at its
unique index key) and attribution (only frames at the deposit address, running its code, write logs
there) are derived, not assumed. With this, `RequestPhaseAmsterdam.request_pass` drops its `parsed`
premise (D-S10, `F = (· = .amsterdam)`). -/
def ParseSucceeds (F : Jaune.Fork → Prop) : Prop :=
  ∀ (benv : Benv) (txs : List Tx) (bal : BalBuilder) (final : Benv) (out : BlockOutput)
    (senders : List (Adr × Tx)) (roots : List Root) (wds : List Jaune.Withdrawal),
    F benv.stat.fork →
    DepositCodeAt benv.state →
    TransactionsRoots txs.putIndex benv { BlockOutput.init with bal := bal } final out
      senders roots →
    parseDepositRequests (withdrawalsPass benv.stat.rules final out wds).2 =
      .ok ((roots.flatMap (Root.keptAt depositAddr)).flatMap frameRecords).flatten

/-- **D-S1** (Prague to BPO2): the log shape and the parse, at covered forks. -/
def D1 : Prop := LogShape CoveredFork ∧ ParseSucceeds CoveredFork

/-- Alias matching the matrix cell identifier `D-S1`. -/
abbrev D_S1 : Prop := D1

/-- **D-S10** (Amsterdam): the log-shape half and the parse, at Amsterdam, so that `request_pass`
drops its parsing premise. -/
def D10 : Prop := LogShape (· = .amsterdam) ∧ ParseSucceeds (· = .amsterdam)

/-- Alias matching the matrix cell identifier `D-S10`. -/
abbrev D_S10 : Prop := D10

/-- **D-S1 / D-S10 control.** A closed runtime at the deposit address that emits one short /
malformed deposit-topic log (`log.data.length < depositEventLength`), with `txs.putIndex` indexing,
all receipt keys present in `receiptsTrie` (no unrelated missing-receipt failure), and every other
premise of `ParseSucceeds` met, makes `parseDepositRequests` fail specifically with
`.block (.depositEventLayout _)`: `DepositCodeAt` is necessary. -/
def ShortLogControl (F : Jaune.Fork → Prop) : Prop :=
  ∃ (shortCode : ByteArray) (benv : Benv) (txs : List Tx) (bal : BalBuilder) (final : Benv)
    (out : BlockOutput) (senders : List (Adr × Tx)) (roots : List Root)
    (wds : List Jaune.Withdrawal),
    let boutWds := (withdrawalsPass benv.stat.rules final out wds).2
    F benv.stat.fork ∧
    benv.state.getCode depositAddr = shortCode ∧
    TransactionsRoots txs.putIndex benv { BlockOutput.init with bal := bal } final out
      senders roots ∧
    (∀ key ∈ boutWds.receiptKeys, boutWds.receiptsTrie[key]?.isSome) ∧
    (∃ log ∈ out.blockLogs, log.address = depositAddr ∧
      log.topics[0]? = some depositEventSignatureHash ∧
      log.data.length < depositEventLength ∧
      ∃ msg, extractDepositData log.data = .error (.depositEventLayout msg)) ∧
    ∃ msg, parseDepositRequests boutWds = .error (.block (.depositEventLayout msg))

/-- **D-S1 control** instantiated at covered forks (e.g. Prague). -/
def D1Control : Prop := ShortLogControl CoveredFork

/-- **D-S10 control** instantiated at Amsterdam. -/
def D10Control : Prop := ShortLogControl (· = .amsterdam)

/-! ## D-S2: what succeeds -/

/-- The four successful outcomes of a frame at the deposit bytes. -/
inductive DepositOutcome where
  | deposit | getDepositRoot | getDepositCount | supportsInterface

/-- **D-S2 classification of one frame**, given the committed-deposit prefix `history` whose
accumulator its entry storage is. Note that `fr.pre` is the frame-entry state immediately after
the message call transferred `fr.sevm.value` from `fr.sevm.caller` to `fr.sevm.currentTarget`:
on `.deposit`, `BeaconDeposit.deposit` enforces `oneEther ≤ value`, `value % oneGwei = 0`, and
`value / oneGwei ≤ 2^64 − 1`; on the three view arms, `fr.sevm.value = 0`; and across all four
arms, frame execution preserves **every** account's balance (`∀ a : Adr, fr.post.getBal a =
fr.pre.getBal a` — deposit contract, caller, and all third parties alike). -/
def Classified (fr : Exec.Frame) (history : List B256) : DepositOutcome → Prop
  | .deposit =>
    Sevm.selector fr.sevm = BeaconDeposit.depositSelector ∧ DepositDecodable fr.sevm ∧
    ∃ s' ev, BeaconDeposit.deposit Bytes.sha256 (solAcc (fr.pre.getStor depositAddr))
        (argBytes fr.sevm 0) (argBytes fr.sevm 1) (argBytes fr.sevm 2) (argRoot fr.sevm)
        fr.sevm.value.toNat = .ok (s', ev) ∧
      solAcc (fr.post.getStor depositAddr) = s' ∧
      SolInv (fr.post.getStor depositAddr) (history ++ [frameNode fr.sevm]) ∧
      (∃ h v, h < 32 ∧ fr.post.getStor depositAddr =
        ((fr.pre.getStor depositAddr).set solCountSlot (Nat.toB256 (history.length + 1))).set (solBranchSlot h) v) ∧
      (∀ a, a ≠ depositAddr → fr.post.getStor a = fr.pre.getStor a) ∧
      frameLogs fr = [BeaconDeposit.depositEventLog depositAddr ev] ∧
      fr.post.output = fr.pre.output ∧
      (∀ a : Adr, fr.post.getBal a = fr.pre.getBal a)
  | .getDepositRoot =>
    Sevm.selector fr.sevm = BeaconDeposit.getDepositRootSelector ∧ fr.sevm.value = 0 ∧
    fr.post.output = (BeaconDeposit.Acc.root Bytes.sha256 (solAcc (fr.pre.getStor depositAddr))).toBytes ∧
    (∀ a, fr.post.getStor a = fr.pre.getStor a) ∧ frameLogs fr = [] ∧
    (∀ a : Adr, fr.post.getBal a = fr.pre.getBal a)
  | .getDepositCount =>
    Sevm.selector fr.sevm = BeaconDeposit.getDepositCountSelector ∧ fr.sevm.value = 0 ∧
    fr.post.output = BeaconDeposit.abiDynamicBytesReturn (BeaconDeposit.le64 history.length) ∧
    (∀ a, fr.post.getStor a = fr.pre.getStor a) ∧ frameLogs fr = [] ∧
    (∀ a : Adr, fr.post.getBal a = fr.pre.getBal a)
  | .supportsInterface =>
    Sevm.selector fr.sevm = BeaconDeposit.supportsInterfaceSelector ∧ fr.sevm.value = 0 ∧
    36 ≤ fr.sevm.data.length ∧
    fr.post.output = BeaconDeposit.abiBoolReturn (decide
      (Sevm.argWord fr.sevm 0 >>> 224 = BeaconDeposit.erc165InterfaceId ∨
        Sevm.argWord fr.sevm 0 >>> 224 = BeaconDeposit.depositInterfaceId)) ∧
    (∀ a, fr.post.getStor a = fr.pre.getStor a) ∧ frameLogs fr = [] ∧
    (∀ a : Adr, fr.post.getBal a = fr.pre.getBal a)

/-- **D-S2.** Over the whole retained history from the actual deployment block to `B`, for every
settled frame occurrence `idx` (`d.trace.settledFrames[idx]? = some fr`) targeting `depositAddr`,
the exact committed-deposit prefix `history := (d.trace.settledFrames.take idx).flatMap
(committedFrameNodes depositAddr)` before `idx` satisfies `SolInv (fr.pre.getStor depositAddr)
history`, and `fr` satisfies `Classified fr history o` for a unique `o : DepositOutcome`. -/
def D2 : Prop :=
  ∀ {B : BlockChain} (d : BeaconDeploymentTo B) (idx : Nat) (fr : Exec.Frame),
    d.trace.settledFrames[idx]? = some fr →
    fr.sevm.currentTarget = depositAddr →
    let history := (d.trace.settledFrames.take idx).flatMap (committedFrameNodes depositAddr)
    SolInv (fr.pre.getStor depositAddr) history ∧
      ∃! o : DepositOutcome, Classified fr history o

/-- Alias matching the matrix cell identifier `D-S2`. -/
abbrev D_S2 : Prop := D2

/-- Guard-deleted deposit model mutant dropping the `value < oneEther` floor guard from
`BeaconDeposit.deposit`. -/
def depositWithoutFloor (H : Bytes → B256) (s : BeaconDeposit.Acc)
    (pubkey withdrawal_credentials signature : Bytes)
    (deposit_data_root : B256) (value : Nat) :
    Except BeaconDeposit.Reason (BeaconDeposit.Acc × BeaconDeposit.DepositEvent) :=
  if pubkey.length ≠ 48 then .error .pubkey_length
  else if withdrawal_credentials.length ≠ 32 then .error .withdrawal_credentials_length
  else if signature.length ≠ 96 then .error .signature_length
  else if value % BeaconDeposit.oneGwei ≠ 0 then .error .value_not_gwei_multiple
  else if 2 ^ 64 - 1 < value / BeaconDeposit.oneGwei then .error .value_too_high
  else
    let amount := BeaconDeposit.le64 (value / BeaconDeposit.oneGwei)
    let event : BeaconDeposit.DepositEvent :=
      ⟨pubkey, withdrawal_credentials, amount, signature, BeaconDeposit.le64 s.count⟩
    let node := BeaconDeposit.depositDataNode H pubkey withdrawal_credentials signature amount
    if node ≠ deposit_data_root then .error .deposit_data_root_mismatch
    else if ¬ s.count < 2 ^ 32 - 1 then .error .merkle_tree_full
    else
      match BeaconDeposit.walk H s.branch 32 0 (s.count + 1) node with
      | some br => .ok (⟨br, s.count + 1⟩, event)
      | none => .error .assert_false

/-- **D-S2 control** (guard-deletion and spurious-arm mutant control):
1. deleting the 1 ETH minimum-value guard (`depositWithoutFloor`) accepts a positive sub-1-ETH
   deposit (`0 < value ∧ value < oneEther`) that `Classified` rejects on **every** frame and
   history; and
2. a permissive mutant runtime `mutantCode` at `depositAddr` admits a successful settled-shaped
   frame `fr` at a covered fork with valid `SolInv (fr.pre.getStor depositAddr) []` on an
   unrecognized selector, for which `¬ ∃ o, Classified fr [] o`. -/
def D2Control : Prop :=
  (∃ (pubkey wc sig : Bytes) (root : B256) (value : Nat)
      (s' : BeaconDeposit.Acc) (ev : BeaconDeposit.DepositEvent),
    0 < value ∧ value < BeaconDeposit.oneEther ∧
    depositWithoutFloor Bytes.sha256 BeaconDeposit.Acc.empty pubkey wc sig root value =
      .ok (s', ev) ∧
    ∀ (fr : Exec.Frame) (history : List B256),
      fr.sevm.value.toNat = value → ¬ ∃ o : DepositOutcome, Classified fr history o) ∧
  (∃ (mutantCode : ByteArray) (fr : Exec.Frame),
    fr.sevm.code = mutantCode ∧
    fr.sevm.currentTarget = depositAddr ∧
    CoveredFork fr.sevm.benvStat.fork ∧
    SolInv (fr.pre.getStor depositAddr) [] ∧
    ¬ ∃ o : DepositOutcome, Classified fr [] o)

/-- Alias matching the matrix control identifier `D-S2` control. -/
abbrev D_S2_control : Prop := D2Control

/-! ## D-S6: value is kept -/

/-- **D-S6.** Over every kept history at covered forks (`KeptAtForks CoveredFork blocks`) from a
state with the deposit code installed, in which the deposit address sends no transaction, under the
two virtual certainties of B's value row (root worlds sum below `2 ^ 256`, no credit to the address
wraps): the contract's balance at the end is at least its start plus the value of every kept frame
at it; every kept frame with the deposit selector carried at least 1 ETH, an exact multiple of a
gwei, at most `2^64 − 1` gwei, and the amount its event records (little-endian gwei) times `10^9`
is that value. -/
def D6 : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock},
    KeptHistory cfg start blocks stop →
    KeptAtForks CoveredFork blocks →
    DepositCodeAt start.state →
    (∀ b ∈ blocks, NoSenderAt depositAddr b.run.senders) →
    HistoryRootsFit blocks → HistoryCreditsFit depositAddr blocks →
    (start.state.bal depositAddr).toNat +
        ((blocks.flatMap (KeptBlock.keptAt depositAddr)).map fun f => f.sevm.value.toNat).sum ≤
      (stop.state.bal depositAddr).toNat ∧
    ∀ b ∈ blocks, ∀ fr ∈ b.keptAt depositAddr, Sevm.selector fr.sevm = BeaconDeposit.depositSelector →
      BeaconDeposit.oneEther ≤ fr.sevm.value.toNat ∧ fr.sevm.value.toNat % BeaconDeposit.oneGwei = 0 ∧
      fr.sevm.value.toNat / BeaconDeposit.oneGwei ≤ 2 ^ 64 - 1 ∧
      ∀ ev, frameLogs fr = [BeaconDeposit.depositEventLog depositAddr ev] →
        ev.amount = BeaconDeposit.le64 (fr.sevm.value.toNat / BeaconDeposit.oneGwei)

/-- Alias matching the matrix cell identifier `D-S6`. -/
abbrev D_S6 : Prop := D6

/-! ## D-S8: same-block request publication (execution side) -/

/-- **D-S8 (execution-side publication).** Over every kept history at covered forks from a state
with the deposit code installed, for every block `b ∈ blocks`, letting `txFrames :=
b.run.txRoots.flatMap (Root.keptAt depositAddr)` and `records := txFrames.flatMap frameRecords`:
* each record is 192 bytes (`∀ r ∈ records, r.length = 192`);
* `b.output.requests` equals `(if records.flatten.length > 0 then [Jaune.depositRequestType ++
  records.flatten] else []) ++ b.run.requests.flatMap RequestStep.bytes`, so every committed
  transaction-phase deposit event in `b` is published in `b`'s own `output.requests` under type
  `0x00` (`Jaune.depositRequestType`), concatenated in exact positional order;
* none of the post-execution system-contract request entries carries type byte `0x00`; and
* whenever the block's pre/post system calls keep no frame at `depositAddr` (as holds when the
  canonical EIP-4788/2935/7002/7251 system contracts are installed), `b.keptAt depositAddr =
  txFrames`. -/
def D8 : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock},
    KeptHistory cfg start blocks stop →
    KeptAtForks CoveredFork blocks →
    DepositCodeAt start.state →
    ∀ b ∈ blocks,
      let txFrames := b.run.txRoots.flatMap (Root.keptAt depositAddr)
      let records := txFrames.flatMap frameRecords
      (∀ r ∈ records, r.length = 192) ∧
      b.output.requests =
        (if records.flatten.length > 0 then [Jaune.depositRequestType ++ records.flatten] else []) ++
          b.run.requests.flatMap RequestStep.bytes ∧
      (∀ entry ∈ b.run.requests.flatMap RequestStep.bytes,
        entry.head? ≠ some JauneConsensus.depositRequestType) ∧
      ((b.run.preRoots ++ requestRootsOf b.run.requests).flatMap (Root.keptAt depositAddr) = [] →
        b.keptAt depositAddr = txFrames)

/-- Alias matching the matrix cell identifier `D-S8`. -/
abbrev D_S8 : Prop := D8

/-! ## The deposit joint chain (split at `cutover`, with Electra ingress) -/

/-- Concatenate two modern configured history traces sharing an intermediate chain. -/
def concatConfiguredHistory {cfg : ChainConfig} {A B C : BlockChain}
    (ab : ConfiguredHistoryTrace cfg A B) :
    ConfiguredHistoryTrace cfg B C → ConfiguredHistoryTrace cfg A C
  | .refl _ _ _ => ab
  | .step prior block => .step (concatConfiguredHistory ab prior) block

/-- A valid deposit joint chain, split at an explicit execution cutover `cutover` (e.g. mainnet
pre-Prague block `22,431,083` where `cutover = deployment.P`, or `cutover = anchor.exec`):
* `deployment : BeaconDeploymentTo cutover` spans deployment block `11,052,984` through `cutover`,
  defining `cutoverCount` (the pre-cutover legacy Eth1 deposit prefix);
* `pre : ConfiguredHistoryTrace mainnetChainConfig cutover anchor.exec` spans post-cutover
  pre-anchor modern blocks (`.refl` when `cutover = anchor.exec`, giving `cutoverCount = E₀`);
* `ingress : JointRunIngress mainnetChainConfig ccfg bls anchor final` advances from `anchor` to
  `final` (supporting both a standard `JointRun` and an Electra activation-slot first block);
* `stepsPostGenesis`: every beacon block along `ingress` is at a post-genesis slot; and
* the modern authority and `0x02` CREATE exclusions hold across `deployment.P → final.exec`. -/
structure DepositJoint {P : Preset} (ccfg : Config) (bls : Bool) (anchor final : JointState P) :
    Type where
  cutover : BlockChain
  deployment : BeaconDeploymentTo cutover
  pre : ConfiguredHistoryTrace mainnetChainConfig cutover anchor.exec
  ingress : JointRunIngress mainnetChainConfig ccfg bls anchor final
  stepsPostGenesis : ∀ D ∈ ingress.steps, D.block.2.message.slot ≠ GENESIS_SLOT
  /-- No authorization over the modern span `P → final.exec` recovers to a system contract or `0x02`. -/
  systemNoAuthority : ∀ p ∈ systemContracts,
    (ingress.toExec (concatConfiguredHistory deployment.modern pre)).NoAuthorityAt p.1
  noAuthority :
    (ingress.toExec (concatConfiguredHistory deployment.modern pre)).NoAuthorityAt 2
  /-- No frame without a code address targets `0x02` over `P → final.exec`. -/
  noFrame : ∀ root ∈ (ingress.toExec (concatConfiguredHistory deployment.modern pre)).rawFrames,
    root.sevm.codeAddress = none → root.sevm.currentTarget ≠ (2 : Adr)

/-- Retained historical+modern trace from deployment block `D` (`11,052,984`) to `anchor.exec`. -/
noncomputable def DepositJoint.anchorTrace {P : Preset} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} (v : DepositJoint ccfg bls anchor final) :
    ConfiguredHistoryTraceIn HistFork mainnetChainConfig v.deployment.D anchor.exec :=
  ((v.deployment.dc.step v.deployment.first).append v.deployment.tail).append
    (concatConfiguredHistory v.deployment.modern v.pre).toHistForkIn

/-- Retained historical+modern trace from deployment block `D` (`11,052,984`) to `final.exec`. -/
noncomputable def DepositJoint.fullTrace {P : Preset} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} (v : DepositJoint ccfg bls anchor final) :
    ConfiguredHistoryTraceIn HistFork mainnetChainConfig v.deployment.D final.exec :=
  ((v.deployment.dc.step v.deployment.first).append v.deployment.tail).append
    (v.ingress.toExec (concatConfiguredHistory v.deployment.modern v.pre)).toHistForkIn

/-- Pre-cutover legacy Eth1 deposit count (`k < v.cutoverCount`, before `v.cutover`). -/
noncomputable def DepositJoint.cutoverCount {P : Preset} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} (v : DepositJoint ccfg bls anchor final) : Nat :=
  v.deployment.deposits.length

/-- Total committed deposits from deployment through `anchor.exec` (definitionally equal to
`v.cutoverCount` when `v.pre = .refl _ _ _`). -/
noncomputable def DepositJoint.E₀ {P : Preset} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} (v : DepositJoint ccfg bls anchor final) : Nat :=
  (committedNodesIn Creation.depositAddress v.anchorTrace).length

/-- Total committed deposits from deployment through `final.exec`. -/
noncomputable def DepositJoint.E_final {P : Preset} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} (v : DepositJoint ccfg bls anchor final) : Nat :=
  (committedNodesIn Creation.depositAddress v.fullTrace).length

/-- The data a kept deposit frame submitted: key, credentials, signature, and value in gwei. -/
def frameDepositData (fr : Exec.Frame) : Bytes × Bytes × Bytes × Nat :=
  (argBytes fr.sevm 0, argBytes fr.sevm 1, argBytes fr.sevm 2,
    fr.sevm.value.toNat / BeaconDeposit.oneGwei)

/-- The committed deposits' data over a historical trace, in the order of `committedNodesIn`. -/
noncomputable def committedDepositDataIn {cfg : ChainConfig} {D B : BlockChain}
    (trace : ConfiguredHistoryTraceIn HistFork cfg D B) :
    List (Bytes × Bytes × Bytes × Nat) :=
  (trace.settledFrames.filter fun fr => decide (fr.sevm.currentTarget = depositAddr ∧
    Sevm.selector fr.sevm = BeaconDeposit.depositSelector)).map frameDepositData

/-- Attribution record for a post-cutover pre-anchor deposit (`cutoverCount ≤ index < E₀`) that
consensus already applied before `anchor`, recording its `ApplyOutcome`. Empty when
`cutover = anchor.exec` (`cutoverCount = E₀`). -/
structure PreAnchorApplied where
  index : Nat
  outcome : ApplyOutcome
  deriving DecidableEq

/-- **D's anchor ledger (complete post-cutover attribution).**
* `AnchorLedger anchor tq₀` aligns `tq₀` with `anchor.beacon.pending_deposits`;
* `preApplied` has distinct indices in `[v.cutoverCount, v.E₀)` (so `preApplied = []` automatically
  when `cutover = anchor.exec`);
* every tag `some n` in `tq₀` lies in `[v.cutoverCount, v.E₀)` (excluding the legacy Eth1 prefix
  `n < v.cutoverCount`) and matches the `n`-th committed deposit's `(pubkey, withdrawal_credentials,
  signature, amount)`; and
* **complete post-cutover attribution**: every post-cutover pre-anchor deposit index `k`
  (`v.cutoverCount ≤ k < v.E₀`) is **either** recorded at a unique position in `preApplied` (and
  absent from `tq₀`) **or** absent from `preApplied` and present at a unique position in `tq₀`
  with nonzero slot and matching `(pubkey, withdrawal_credentials, signature, amount)`.
When `cutover = anchor.exec` (`v.pre = .refl _ _ _`), `v.cutoverCount = v.E₀`, so tagging every
anchor entry `none` with `preApplied = []` satisfies `AnchorLedgerD` with zero extra observation. -/
def AnchorLedgerD {P : Preset} {ccfg : Config} {bls : Bool} {anchor final : JointState P}
    (v : DepositJoint ccfg bls anchor final) (tq₀ : TQueue)
    (preApplied : List PreAnchorApplied) : Prop :=
  AnchorLedger anchor tq₀ ∧
  (preApplied.map PreAnchorApplied.index).Nodup ∧
  (∀ rec ∈ preApplied, v.cutoverCount ≤ rec.index ∧ rec.index < v.E₀) ∧
  (∀ n e, (some n, e) ∈ tq₀ → v.cutoverCount ≤ n ∧ n < v.E₀ ∧
    (committedDepositDataIn v.anchorTrace)[n]? =
      some (e.pubkey.toArray.toList, e.withdrawal_credentials.toBytes,
        e.signature.toArray.toList, e.amount.toNat)) ∧
  (∀ k : Nat, v.cutoverCount ≤ k → k < v.E₀ →
    ((∃ idx : Nat, ∃ rec : PreAnchorApplied,
        preApplied[idx]? = some rec ∧ rec.index = k ∧
        (∀ idx' rec', preApplied[idx']? = some rec' → rec'.index = k → idx' = idx) ∧
        (∀ p : Nat, (tq₀[p]?.map Prod.fst) ≠ some (some k))) ∨
     ((∀ rec ∈ preApplied, rec.index ≠ k) ∧
      ∃ (p : Nat) (d : PendingDeposit),
        tq₀[p]? = some (some k, d) ∧
        d.slot ≠ GENESIS_SLOT ∧
        (committedDepositDataIn v.anchorTrace)[k]? =
          some (d.pubkey.toArray.toList, d.withdrawal_credentials.toBytes,
            d.signature.toArray.toList, d.amount.toNat) ∧
        ∀ p' : Nat, (tq₀[p']?.map Prod.fst) = some (some k) → p' = p)))

/-! ## D-S9 delivery, D-S8 joined corollary, and seam controls -/

/-- **D-S9 delivery.** On a valid deposit joint chain, step `j`'s beacon block carries, as its
deposit requests serialized in order, exactly the request records of the kept frames at the
deposit address of step `j`'s own execution block; and the run's requests carry consecutive
indices from `E₀`, ending at `E_final`. -/
def D9Delivery : Prop :=
  ∀ {P : Preset} {ccfg : Config} {bls : Bool} {anchor final : JointState P}
    (v : DepositJoint (P := P) ccfg bls anchor final),
    (∀ (j : Nat) (D : JointRunStep (P := P) mainnetChainConfig ccfg bls),
      v.ingress.steps[j]? = some D →
      (stepDepositRequests D).map Ssz.serialize =
        (D.stepTrace.trace.kept.keptAt depositAddr).flatMap frameRecords) ∧
    (ingressDepositRequests v.ingress).map (fun dr => dr.index.toNat) =
      List.range' v.E₀ (ingressDepositRequests v.ingress).length ∧
    v.E_final = v.E₀ + (ingressDepositRequests v.ingress).length

/-- **D-S8 joined corollary.** Along a `DepositJoint`, the records of every kept frame at
`depositAddr` in step `j`'s execution block are serialized in positional order as step `j`'s
beacon `DepositRequest`s. -/
def D8Joined : Prop :=
  ∀ {P : Preset} {ccfg : Config} {bls : Bool} {anchor final : JointState P}
    (v : DepositJoint (P := P) ccfg bls anchor final),
    ∀ (j : Nat) (D : JointRunStep (P := P) mainnetChainConfig ccfg bls),
      v.ingress.steps[j]? = some D →
      (stepDepositRequests D).map Ssz.serialize =
        (D.stepTrace.trace.kept.keptAt depositAddr).flatMap frameRecords

/-- **D-S9 delivery control (joint-step refusal).** Any joint step whose beacon block's execution
requests differ from those its own execution block produces is refused by `jointStep`. -/
def D9DeliveryControl : Prop :=
  ∀ {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s : JointState P}
    {b : AnySignedBlock P} {req : NewPayloadRequest P} {f : Jaune.Fork}
    {st : State} {bout : BlockOutput},
    NewPayloadRequest.ofBlock b.2.message = .ok req →
    cfg.forkAt (payloadToBlock req).header.number (payloadToBlock req).header.timestamp = .ok f →
    applyBody (initBenv f s.exec (payloadToBlock req).header) (payloadToBlock req).txs
      (payloadToBlock req).ommers (payloadToBlock req).wds = .ok (st, bout) →
    bout.requests ≠ req.executionRequests →
    ∀ s', jointStep cfg ccfg bls s b ≠ .ok s'

/-- **D-S9 delivery seam control (`engineVerdict` request-hash / request-list boundary).** When a
payload passes all pre-transition engine checks, header validation, body execution (`applyBody`),
and every non-`requestsHash` post-execution header check, but the execution body's `bout.requests`
(seeded from `parseDepositRequests`) differs from `req.executionRequests`, `engineVerdict` rejects
specifically at the request commitment seam:
* with `.error (.transition (.block (.requestsHash _)))` when `computeRequestsHash bout.requests ≠
  computeRequestsHash req.executionRequests`; and
* with `.error .requestsMismatch` on a hash collision (`computeRequestsHash bout.requests =
  computeRequestsHash req.executionRequests`). -/
def D9DeliverySeamControl : Prop :=
  ∀ {P : Preset} (cfg : ChainConfig) (cf : CFork) (exec : BlockChain) (req : NewPayloadRequest P)
    (f : Jaune.Fork) (st : State) (bout : BlockOutput),
    let blk := payloadToBlock req
    (cf = .electra ∨ cf = .fulu) →
    req.executionPayload.txBytes.any List.isEmpty = false →
    blk.header.hash = req.executionPayload.block_hash →
    blobVersionedHashesOf req.executionPayload.txBytes = .ok req.versionedHashes →
    cfg.checkChainId exec = .ok () →
    cfg.forkAt blk.header.number blk.header.timestamp = .ok f →
    f.consensusFork? = some cf →
    checkBlockRlpSize f.ruleSet.block blk.toBLT.toBytes.length = .ok () →
    validateHeader f.ruleSet exec blk.header = .ok () →
    applyBody (initBenv f exec blk.header) blk.txs blk.ommers blk.wds = .ok (st, bout) →
    stateTransitionChecks bout blk.header (getTransactionsRoot bout) st.root
      (getReceiptRoot bout) (logsBloom bout.blockLogs) (getWithdrawalsRoot bout)
      blk.header.requestsHash = .ok () →
    bout.requests ≠ req.executionRequests →
    (computeRequestsHash bout.requests ≠ computeRequestsHash req.executionRequests →
      ∃ msg, engineVerdict cfg cf exec req = .error (.transition (.block (.requestsHash msg)))) ∧
    (computeRequestsHash bout.requests = computeRequestsHash req.executionRequests →
      engineVerdict cfg cf exec req = .error .requestsMismatch)

/-! ## D-S9 joined: complete fate, credit and conservation from the contract -/

/-- **D-S9 fate and credit, joined (self-contained occurrence partition).** On a valid deposit
joint chain `v` with BLS on (`bls = true`) and `AnchorLedgerD v tq₀ preApplied`:
1. **Freshness & count progression:** `RunIndicesFreshIngress v.ingress tq₀` holds without
   assumption, `v.cutoverCount ≤ v.E₀ ≤ v.E_final`, and `(committedDepositDataIn v.fullTrace)` has
   length `v.E_final`.
2. **Explicit legacy prefix exclusion:** indices `k < v.cutoverCount` are the exact pre-cutover
   legacy Eth1 deposit prefix (`committedDepositDataIn v.deployment.trace`), outside `D-S9`
   request-occurrence tracking (absent from `preApplied`, `tq₀` tags, and `ingressDepositRequests`).
3. **Run-request frame correspondence:** every deposit request `dr` of step `j` came from a kept
   `deposit`-selector frame `fr` in step `j`'s execution block with matching key, credentials,
   signature, gwei value (`dr.amount.toNat * 10^9 = fr.sevm.value.toNat`), and committed index
   `dr.index.toNat ∈ [v.E₀, v.E_final)`.
4. **Complete 3-way occurrence-indexed fate partition:** the ledger runs to `(tqF, ap)` aligned
   with `pendingList final`, and **every** post-cutover committed deposit `k`
   (`v.cutoverCount ≤ k < v.E_final`, with committed payload `(pkBytes, wcBytes, sigBytes,
   amtGwei)`) meets **exact one** of three mutually exclusive fates:
   * **applied before `anchor`**: `k < v.E₀` and `k` appears at a unique index in `preApplied`
     (empty when `cutover = anchor.exec`), and nowhere in `ap` or `tqF`;
   * **applied during the joint run**: absent from `preApplied` and `tqF`, and applied at a
     **unique** `apIdx` (`ap[apIdx]? = some (stepIdx, a)`, with `emitStep < stepIdx` whenever `k`
     was emitted in step `emitStep`), matching `(pkBytes, wcBytes, sigBytes, amtGwei)` at a nonzero
     slot, and satisfying `ApplyOutcomeSpec ccfg true a.2.pre s' a.2.deposit o` (new validator
     registered only when `blsVerify true` holds, top-up of existing key, or invalid-signature
     new-key no-credit leaving ETH in `depositAddr` with `s' = a.2.pre`, with explicit
     `addValidatorToRegistry` / `increaseBalance` validator and balance equations); or
   * **still pending at `final`**: absent from `preApplied` and `ap`, and sitting at a **unique**
     position `p` in `tqF` with matching `(pkBytes, wcBytes, sigBytes, amtGwei)` and nonzero slot. -/
def D9FateJoined : Prop :=
  ∀ {P : Preset} {ccfg : Config} {anchor final : JointState P}
    (v : DepositJoint (P := P) ccfg true anchor final) (tq₀ : TQueue)
    (preApplied : List PreAnchorApplied),
    AnchorLedgerD v tq₀ preApplied →
    let deposits := committedDepositDataIn v.fullTrace
    RunIndicesFreshIngress v.ingress tq₀ ∧
    v.cutoverCount ≤ v.E₀ ∧ v.E₀ ≤ v.E_final ∧
    v.E_final = v.E₀ + (ingressDepositRequests v.ingress).length ∧
    deposits.length = v.E_final ∧
    deposits.take v.cutoverCount = committedDepositDataIn v.deployment.trace ∧
    (∀ k < v.cutoverCount,
      (∀ rec ∈ preApplied, rec.index ≠ k) ∧
      (∀ e ∈ tq₀, e.1 ≠ some k) ∧
      (∀ dr ∈ ingressDepositRequests v.ingress, dr.index.toNat ≠ k)) ∧
    (∀ (j : Nat) (D : JointRunStep (P := P) mainnetChainConfig ccfg true),
      v.ingress.steps[j]? = some D →
      ∀ (rIdx : Nat) (dr : DepositRequest), (stepDepositRequests D)[rIdx]? = some dr →
        v.E₀ ≤ dr.index.toNat ∧ dr.index.toNat < v.E_final ∧
        ∃ fr ∈ D.stepTrace.trace.kept.keptAt depositAddr,
          Sevm.selector fr.sevm = BeaconDeposit.depositSelector ∧
          dr.amount.toNat * 10 ^ 9 = fr.sevm.value.toNat ∧
          dr.pubkey.toArray.toList = argBytes fr.sevm 0 ∧
          dr.withdrawal_credentials.toBytes = argBytes fr.sevm 1 ∧
          dr.signature.toArray.toList = argBytes fr.sevm 2 ∧
          deposits[dr.index.toNat]? = some (frameDepositData fr)) ∧
    ∃ tqF ap, runLedger 0 v.ingress.steps tq₀ [] = .ok (tqF, ap) ∧
      pendingList final = .ok (tqF.map Prod.snd) ∧
      ∀ k : Nat, v.cutoverCount ≤ k → k < v.E_final →
        ∃ pkBytes wcBytes sigBytes amtGwei,
          deposits[k]? = some (pkBytes, wcBytes, sigBytes, amtGwei) ∧
          ((k < v.E₀ ∧
            (∃ idx : Nat, ∃ rec : PreAnchorApplied,
              preApplied[idx]? = some rec ∧ rec.index = k ∧
              ∀ idx' rec', preApplied[idx']? = some rec' → rec'.index = k → idx' = idx) ∧
            (∀ a ∈ ap, a.2.2.tag ≠ some k) ∧
            (∀ e ∈ tqF, e.1 ≠ some k)) ∨
           ((∀ rec ∈ preApplied, rec.index ≠ k) ∧
            (∀ e ∈ tqF, e.1 ≠ some k) ∧
            ∃ (apIdx stepIdx : Nat) (a : AppliedAt P),
              ap[apIdx]? = some (stepIdx, a) ∧
              stepIdx < v.ingress.steps.length ∧
              a.2.tag = some k ∧
              (∀ apIdx' stepIdx' a',
                ap[apIdx']? = some (stepIdx', a') → a'.2.tag = some k → apIdx' = apIdx) ∧
              a.2.deposit.pubkey.toArray.toList = pkBytes ∧
              a.2.deposit.withdrawal_credentials.toBytes = wcBytes ∧
              a.2.deposit.signature.toArray.toList = sigBytes ∧
              a.2.deposit.amount.toNat = amtGwei ∧
              a.2.deposit.slot ≠ GENESIS_SLOT ∧
              (∀ (emitStep : Nat) (D : JointRunStep (P := P) mainnetChainConfig ccfg true),
                v.ingress.steps[emitStep]? = some D →
                k ∈ (stepDepositRequests D).map (fun dr => dr.index.toNat) →
                emitStep < stepIdx) ∧
              ∃ (o : ApplyOutcome) (s' : BeaconState P a.1),
                ApplyOutcomeSpec ccfg true a.2.pre s' a.2.deposit o) ∨
           ((∀ rec ∈ preApplied, rec.index ≠ k) ∧
            (∀ a ∈ ap, a.2.2.tag ≠ some k) ∧
            ∃ (p : Nat) (d : PendingDeposit),
              tqF[p]? = some (some k, d) ∧
              (∀ p' : Nat, (tqF[p']?.map Prod.fst) = some (some k) → p' = p) ∧
              d.pubkey.toArray.toList = pkBytes ∧
              d.withdrawal_credentials.toBytes = wcBytes ∧
              d.signature.toArray.toList = sigBytes ∧
              d.amount.toNat = amtGwei ∧
              d.slot ≠ GENESIS_SLOT))

/-- **D-S9 conservation, joined.** On a valid deposit joint chain with BLS on and `AnchorLedgerD`,
the Wei of credited, uncredited-invalid-signature, and still-pending tagged occurrences equals the
Wei of the anchor's pending tagged occurrences plus the exact Wei paid to `depositAddr` across the
run's kept deposit frames; in particular, total Wei credited along the run never exceeds the Wei
paid for those occurrences. -/
def D9ConservationJoined : Prop :=
  ∀ {P : Preset} {ccfg : Config} {anchor final : JointState P}
    (v : DepositJoint (P := P) ccfg true anchor final) (tq₀ : TQueue)
    (preApplied : List PreAnchorApplied),
    AnchorLedgerD v tq₀ preApplied →
    let runPaidWei :=
      ((v.ingress.steps.flatMap fun D => D.stepTrace.trace.kept.keptAt depositAddr).filter
        (fun fr => decide (Sevm.selector fr.sevm = BeaconDeposit.depositSelector))).foldr
        (fun fr acc => fr.sevm.value.toNat + acc) 0
    ∃ tqF ap, runLedger 0 v.ingress.steps tq₀ [] = .ok (tqF, ap) ∧
      (creditedTotal (jointCtx ccfg true) ap +
        uncreditedTotal (jointCtx ccfg true) ap +
        taggedTotal tqF) * 10 ^ 9 =
        taggedTotal tq₀ * 10 ^ 9 + runPaidWei ∧
      creditedTotal (jointCtx ccfg true) ap * 10 ^ 9 ≤
        taggedTotal tq₀ * 10 ^ 9 + runPaidWei

end Blanc.Corpus.Freeze.Deposit
