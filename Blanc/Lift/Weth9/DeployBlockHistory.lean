import Blanc.Lift.Weth9.DeployTransaction
import Blanc.Lift.Weth9.CommittedHistoryIn
import Blanc.ExecutionAccountingMidHistoryIn
import Blanc.ExecutionMidHistoryInFacts
import Blanc.ExecutionIndexedReceipts
import Blanc.ExecutionTransactionDebitInverse

/-!
# WETH9 committed history from its creation transaction inside its block

A history that starts right after one transaction of a retained configured block
(`MidHistoryTraceIn`) and its WETH9 committed replay:

* `midTouchedKeysIn`, `midKeyUniverseIn`, `midCommittedInvocationsIn` — the touched keys, the
  tracked universe and the settlement-committed writer invocations of a mid history;
* `weth9_mid_history_committedIn` — the statement of `weth9_history_committed`
  (`CommittedHistory.lean`) over a mid history, with the start state in place of the checkpoint
  state (`midHistoryIn`, `MidHistoryTraceIn.stateInv_admitted_semIn`);
* `weth9_history_committed_from_creation_block` — the creation transaction at its position `i`
  of the deployment block (Byzantium, block 4719568), cut by `TxSplit`: the state right after
  it holds the runtime and the constructor's storage, and the rest of the block followed by any
  later `HistFork` history replays the committed writer invocations from the deployed ledger.
-/

namespace Blanc.Lift.Weth9

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- Length of the already registered WETH creation input, without evaluating
its individual calldata charges. -/
theorem Creation.code_toList_length : Creation.code.toList.length = 3504 := by
  rw [ByteArray.toList_eq_toList_data, Array.length_toList]
  decide +kernel

/-- Original Byzantium validation plus the recorded transaction gas limit
supplies the constructor margin. A byte-count upper bound is sufficient; no
evaluated intrinsic-gas observation is an input. -/
theorem weth9_creation_gas_of_limit {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    (hnumber : block.block.header.number = 4719568)
    (htime : block.block.header.timestamp = 1513077455)
    {i : Nat} (cut : block.bodyTrace.transactions.TxSplit i) {gasPrice : Nat}
    (htype : cut.tx.type = .zero gasPrice none)
    (hdata : cut.tx.data = Creation.code.toList) (hgas : cut.tx.gas = 1500000) :
    cut.head.intrinsicGas + 720000 ≤ cut.tx.gas := by
  have forkAt := block.forkAt
  rw [hnumber, htime] at forkAt
  have fork : block.fork = .byzantium :=
    Except.ok.inj (forkAt.symm.trans weth9_deployment_fork)
  have rules : cut.benv.stat.rules = byzantiumRules := by
    rw [cut.before.stat_eq]
    change block.fork.ruleSet = byzantiumRules
    rw [fork]
    rfl
  have bound := cut.head.intrinsicGas_legacy_create_le
    (by rw [rules]; rfl) (by rw [rules]; rfl) htype
  rw [rules, hdata, Creation.code_toList_length] at bound
  change cut.head.intrinsicGas ≤ 53000 + 68 * 3504 at bound
  omega

/-- The original successful WETH creation receipt and transaction admission
derive funding, the pre-debit collision check and the transaction gas bound.
Transaction identity and recovered sender remain explicit; no prestate balance
or target-account observation is supplied. -/
theorem weth9_creation_preconditions_of_receipt {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    {i : Nat} (cut : block.bodyTrace.transactions.TxSplit i) {gasPrice : Nat}
    (htype : cut.tx.type = .zero gasPrice none)
    (hnonce : cut.tx.nonce = 446)
    (hsender : cut.head.sender = Creation.deployer)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes cut.index.toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    (cut.tx.gas * cut.head.effectiveGasPrice).toB256 ≤
        cut.benv.state.bal Creation.deployer ∧
      accountHasCodeOrNonce cut.benv.state Creation.weth9Address = false ∧
      cut.tx.gas < 2 ^ 64 := by
  have hsg : cut.benv.stat.rules.stateGas = none := by
    rw [cut.before.stat_eq]
    exact BodyStageCapabilities.historical.stateGas_none block.forkIn
  have funds := cut.head.gas_funds_of_no_blob_fee (by
    simp only [transactionBlobGasFee, Tx.isTypeThree, htype, Bool.false_eq_true, ↓reduceIte])
  rw [hsender] at funds
  have senderNonce : (cut.benv.state.get cut.head.sender).nonce = 446 :=
    (checkTransaction_sender_nonce cut.head.checked).trans hnonce
  have debitNonce : (cut.head.debitState.get cut.head.sender).nonce = 447 := by
    rw [(State.of_subBal cut.head.debit).2, State.setBal_get_nonce]
    rw [State.incrNonce, State.setAccount_get_self, Acct.clearIfEmpty_nonce, senderNonce]
    rfl
  have prepared := cut.head.prepared
  simp only [prepareMessage, htype, TxType.receiver?] at prepared
  have messageEq := (Except.ok.inj prepared).symm
  have target : cut.head.msg.currentTarget = Creation.weth9Address := by
    rw [messageEq]
    change computeContractAddress cut.head.sender
      ((cut.head.debitState.get cut.head.sender).nonce - 1) = _
    rw [debitNonce, hsender, Creation.weth9Address_eq]
    rfl
  have clean := block.txSplit_error_eq_none_of_receipt cut block.forkIn.stateGas_none
    lookup succeeded
  have fresh := (cut.head.creation_entry_of_clean
    (by rw [messageEq]; rfl) hsg clean).2
  rw [target] at fresh
  have gasLe := tx_gas_le_blockGasLimit_of_checked
    (benv := cut.benv.beginTransaction) hsg cut.head.checked
  change cut.tx.gas ≤ cut.benv.stat.blockGasLimit at gasLe
  rw [cut.before.stat_eq] at gasLe
  have headerBound := header_gasLimit_lt_of_transition block.transition
  change cut.tx.gas ≤ block.block.header.gasLimit at gasLe
  exact ⟨funds, fresh, by omega⟩

/-- The keys the actual raw target entries of a mid history may touch, including entries whose
effects later roll back. -/
def midTouchedKeysIn {F : Fork → Prop} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} (ca : Adr) (trace : MidHistoryTraceIn F cfg start future) :
    List Key :=
  trace.rawFrames.flatMap fun root =>
    if root.sevm.currentTarget = ca then frameKeys root.sevm else []

/-- The tracked universe of a mid history: the initial keys together with every key a raw target
entry may touch. -/
def midKeyUniverseIn {F : Fork → Prop} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} (ca : Adr) (trace : MidHistoryTraceIn F cfg start future)
    (initialKeys : Key → Prop) : Key → Prop :=
  Key.extend initialKeys (midTouchedKeysIn ca trace)

/-- The settlement-committed WETH9 writer invocations at the contract of a mid history, in trace
order. -/
def midCommittedInvocationsIn {F : Fork → Prop} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} (ca : Adr) (trace : MidHistoryTraceIn F cfg start future) :
    List Invocation :=
  trace.settledFrames.flatMap (committedFrameInvocations ca)

/-- **The WETH9 model replays the committed chain of a mid history.** The statement of
`weth9_history_committed` for a history that starts right after one transaction of a retained
block: from one initial footprint `K₀` at the start state and the trace-local freshness of the
touched keys, the code stays installed, the ether does not overflow, the future storage carries
the footprint over `K₀ ∪ touched`, the future footprint ledger is the model run over exactly the
settlement-committed writer invocations at the contract in trace order, and the model run with the
contract's ether is backed. -/
theorem weth9_mid_history_committedIn {F : Fork → Prop} (capabilities : BodyStageCapabilities F)
    {ca : Adr} {cfg : ChainConfig} {start : Benv} {future : BlockChain} {K₀ : Key → Prop}
    (trace : MidHistoryTraceIn F cfg start future)
    (installed : some (start.state.getCode ca).toList = weth9Sem.image)
    (sumNof : SumNof start.state.bal)
    (initial : FootInv K₀ (start.state.getStor ca) (start.state.bal ca))
    (fresh : KeysFresh K₀ (midTouchedKeysIn ca trace)) :
    some (future.state.getCode ca).toList = weth9Sem.image ∧ SumNof future.state.bal ∧
      FootInv (midKeyUniverseIn ca trace K₀) (future.state.getStor ca)
        (future.state.bal ca) ∧
      (ledger K₀ (start.state.getStor ca)).run
          (replayCalls (midCommittedInvocationsIn ca trace)) =
        some (ledger (midKeyUniverseIn ca trace K₀) (future.state.getStor ca)) ∧
      ∃ s : State,
        (State.mk (ledger K₀ (start.state.getStor ca)) (start.state.bal ca).toNat).run
            (replayCalls (midCommittedInvocationsIn ca trace)) = some s ∧
          s.ledger = ledger (midKeyUniverseIn ca trace K₀) (future.state.getStor ca) ∧
          s.Backed := by
  let U := midKeyUniverseIn ca trace K₀
  have extended : FootInv U (start.state.getStor ca) (start.state.bal ca) :=
    initial.extend fresh
  have admitted : trace.FrameAdmitted ca (footEntry U) := by
    apply (trace.frameAdmitted_iff_rawFrames ca _).2
    intro root member target k hk
    exact Or.inr (List.mem_flatMap.mpr ⟨root, member, by simpa only [target, ite_true] using hk⟩)
  have startInv : (footSpec U).StateInv ca start.state :=
    footSpec_stateInv_iff.mpr ⟨installed, sumNof, extended.support, extended.backed⟩
  have rewards := trace.rewardCreditsFunded capabilities
  have finish := trace.stateInv_admitted_semIn
    (footSpec_preservesAdmittedIn F capabilities.stateGas_none ca extended.inj)
    capabilities admitted rewards startInv installedCert rfl
  obtain ⟨hcode, hside, hsup, hback⟩ := footSpec_stateInv_iff.mp finish
  obtain ⟨steps, replay, observed⟩ :=
    (weth9AccountingLadderIn F capabilities.stateGas_none ca extended.inj).midHistoryIn
      trace admitted capabilities rewards startInv installedCert rfl
  change LedgerReplay (ledger U (start.state.getStor ca)) steps
    (ledger U (future.state.getStor ca)) at replay
  change steps = trace.settledFrames.flatMap (committedFrameInvocations ca) at observed
  have hsteps : steps = midCommittedInvocationsIn ca trace := observed
  subst hsteps
  have hrun : (ledger K₀ (start.state.getStor ca)).run
      (replayCalls (midCommittedInvocationsIn ca trace)) =
        some (ledger U (future.state.getStor ca)) := by
    have := replay
    unfold LedgerReplay at this
    have hext : ledger U (start.state.getStor ca) = ledger K₀ (start.state.getStor ca) :=
      ledger_extend initial fresh
    rw [hext] at this
    exact this
  refine ⟨hcode, hside, ⟨hsup, extended.inj, extended.apart, hback⟩, hrun, ?_⟩
  have hmodel := State.run_ledger
    (State.mk (ledger K₀ (start.state.getStor ca)) (start.state.bal ca).toNat)
    (replayCalls (midCommittedInvocationsIn ca trace))
  simp only [hrun] at hmodel
  cases hs : (State.mk (ledger K₀ (start.state.getStor ca))
      (start.state.bal ca).toNat).run (replayCalls (midCommittedInvocationsIn ca trace)) with
  | none => rw [hs] at hmodel; cases hmodel
  | some s =>
    rw [hs] at hmodel
    simp only [Option.map_some, Option.some.injEq] at hmodel
    refine ⟨s, rfl, hmodel, ?_⟩
    exact State.run_backed (s := ⟨ledger K₀ (start.state.getStor ca),
      (start.state.bal ca).toNat⟩) initial.backed hs

/-- **WETH9 from its creation transaction inside the deployment block.** Let `block` be a retained
`HistFork` block of the mainnet configuration at the deployment coordinates (block 4719568,
timestamp 1513077455), and `cut` its transaction fold cut at position `i`, where the transaction
is the creation transaction: legacy type, the creation code as data, no value, nonce 446,
recovered sender the deployer, enough funds and gas, and an address with neither code nor nonce
before it. Then the state right after the transaction holds the runtime and the constructor's
storage at `weth9Address`, with the empty footprint and balances summing below the word bound;
and the rest of the block followed by any later `HistFork` history (`(MidHistoryTraceIn.tail
block cut).append history`), with trace-local freshness of its touched keys, keeps the runtime
installed and `SumNof`, carries the footprint over the touched keys, and its future footprint
ledger is the model run, from the deployed ledger, of exactly the settlement-committed writer
invocations at WETH9 from the transaction after the creation onwards, backed by the contract's
ether. -/
theorem weth9_history_committed_from_creation_block {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    (hnumber : block.block.header.number = 4719568)
    (htime : block.block.header.timestamp = 1513077455)
    {i : Nat} (cut : block.bodyTrace.transactions.TxSplit i) {gasPrice : Nat}
    (htype : cut.tx.type = .zero gasPrice none)
    (hdata : cut.tx.data = Creation.code.toList)
    (hvalue : cut.tx.value = 0) (hnonce : cut.tx.nonce = 446)
    (hsender : cut.head.sender = Creation.deployer)
    (hfunds : (cut.tx.gas * cut.head.effectiveGasPrice).toB256 ≤
      cut.benv.state.bal Creation.deployer)
    (hgas : cut.head.intrinsicGas + 720000 ≤ cut.tx.gas) (hgasb : cut.tx.gas < 2 ^ 64)
    (hfresh : accountHasCodeOrNonce cut.benv.state Creation.weth9Address = false) :
    (cut.afterBenv.state.getCode Creation.weth9Address).toList = code.toList ∧
      cut.afterBenv.state.getStor Creation.weth9Address = Creation.deployedStor ∧
      (∀ b : B256,
        FootInv (fun _ => False) (cut.afterBenv.state.getStor Creation.weth9Address) b) ∧
      SumNof cut.afterBenv.state.bal ∧
      ∀ {future : BlockChain}
        (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed future),
        KeysFresh (fun _ => False)
          (midTouchedKeysIn Creation.weth9Address
            ((MidHistoryTraceIn.tail block cut).append history)) →
        some (future.state.getCode Creation.weth9Address).toList = weth9Sem.image ∧
          SumNof future.state.bal ∧
          FootInv (midKeyUniverseIn Creation.weth9Address
              ((MidHistoryTraceIn.tail block cut).append history) (fun _ => False))
            (future.state.getStor Creation.weth9Address)
            (future.state.bal Creation.weth9Address) ∧
          (ledger (fun _ => False) Creation.deployedStor).run
              (replayCalls (midCommittedInvocationsIn Creation.weth9Address
                ((MidHistoryTraceIn.tail block cut).append history))) =
            some (ledger (midKeyUniverseIn Creation.weth9Address
                ((MidHistoryTraceIn.tail block cut).append history) (fun _ => False))
              (future.state.getStor Creation.weth9Address)) ∧
          ∃ s : State,
            (State.mk (ledger (fun _ => False) Creation.deployedStor)
                (cut.afterBenv.state.bal Creation.weth9Address).toNat).run
                (replayCalls (midCommittedInvocationsIn Creation.weth9Address
                  ((MidHistoryTraceIn.tail block cut).append history))) = some s ∧
              s.ledger = ledger (midKeyUniverseIn Creation.weth9Address
                  ((MidHistoryTraceIn.tail block cut).append history) (fun _ => False))
                (future.state.getStor Creation.weth9Address) ∧
              s.Backed := by
  have hstat : cut.benv.stat = (initBenv block.fork pre block.block.header).stat :=
    cut.before.stat_eq
  have hfork : mainnetChainConfig.forkAt 4719568 1513077455 = .ok cut.benv.stat.fork := by
    have h := block.forkAt
    rw [hnumber, htime] at h
    rw [hstat]
    exact h
  have hsg : cut.benv.stat.rules.stateGas = none := by
    rw [hstat]
    exact BodyStageCapabilities.historical.stateGas_none block.forkIn
  have hvalid : validateTransaction cut.benv.stat.rules cut.tx 0 =
      .ok (cut.head.intrinsicGas, cut.head.calldataFloorGasCost) :=
    (validateTransaction_sender_congr_none hsg).trans cut.head.validation
  have hchecked : checkTransaction cut.benv.beginTransaction
      (transactionPreludeBout cut.bout cut.tx cut.index) cut.tx =
        .ok (Creation.deployer, cut.head.effectiveGasPrice, cut.head.blobVersionedHashes,
          cut.head.txBlobGasUsed) := by
    rw [← hsender]
    exact cut.head.checked
  obtain ⟨post, bout', htx, hcode, hstor⟩ := Creation.weth9_creation_transaction_byzantium hfork
    htype hdata hvalue hnonce hvalid hchecked hfunds hgas hgasb hfresh
  have hpost : post = cut.txState :=
    (Prod.mk.inj (Except.ok.inj (htx.symm.trans cut.head.result))).1
  subst hpost
  have hfoot : ∀ b : B256,
      FootInv (fun _ => False) (cut.afterBenv.state.getStor Creation.weth9Address) b :=
    fun b => by
      change FootInv (fun _ => False) (cut.txState.getStor Creation.weth9Address) b
      rw [hstor]
      exact FootInv.deployed Creation.deployedStor_metadata
  have hsum : SumNof cut.afterBenv.state.bal :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _)
      (block.txSplit_bound cut BodyStageCapabilities.historical)
  refine ⟨hcode, hstor, hfoot, hsum, ?_⟩
  intro future history fresh
  have committed := weth9_mid_history_committedIn BodyStageCapabilities.historical
    ((MidHistoryTraceIn.tail block cut).append history) (K₀ := fun _ => False)
    (by show some _ = some code.toList; rw [← hcode]; rfl) hsum (hfoot _) fresh
  have hs : cut.afterBenv.state.getStor Creation.weth9Address = Creation.deployedStor := hstor
  rw [hs] at committed
  exact committed

end Blanc.Lift.Weth9
