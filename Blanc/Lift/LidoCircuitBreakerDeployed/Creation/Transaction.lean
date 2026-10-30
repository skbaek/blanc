import Blanc.Lift.LidoCircuitBreakerDeployed.Creation.Deploy
import Blanc.Lift.ConstructorTransaction
import Blanc.ExecutionIndexedReceipts
import Blanc.ExecutionMidHistoryIn

/-!
# The Lido CircuitBreaker deployment at its actual transaction cut

`DeploymentCut block` names one position of a retained configured block on the covered fork
domain whose transaction is the CircuitBreaker's creation: a contract creation (`to` empty)
whose input is the certified creation input, sent by the recorded deployer at nonce zero, with
at least 1,000,000 message gas, and whose indexed receipt in the block's own output reports
success. These are one-block observations of the creation transaction and its receipt. No
signature recovery is involved: the sender is the trace's own recovered sender, stated equal to
the recorded deployer.

`DeploymentCut.initial` derives, at the exact committed post-transaction boundary
`cut.afterBenv` (the start of `MidHistoryTraceIn.tail block cut`), that the CircuitBreaker's
address holds the certified runtime and the constructor's two-slot storage. Collision freedom is
a consequence of the success receipt (`MessageCallTrace.exists_clean_create_with_deletions`), and
the constructor schedules no deletion (`createTrace_deletions_of_balSilent`, its five lifted
functions execute no `CALL`/`CREATE` and no `SELFDESTRUCT`).
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed.Creation

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- The constructor's five lifted functions move no ether and schedule no deletion. -/
theorem cert_balSilentSet : BalSilentSet cert.prog [0, 1, 2, 3, 4] = true := by
  decide +kernel

theorem cert_entry_balSilent :
    ∃ entry, cert.prog[0]? = some entry ∧ entry.balSilent = true ∧
      entry.refs.all (· ∈ [0, 1, 2, 3, 4]) = true :=
  ⟨_, rfl, by decide +kernel, by decide +kernel⟩

/-- Input identification of the CircuitBreaker's creation inside one retained block on the
covered fork domain. Every field is an observation of the creation transaction or its receipt;
the installed code and storage are derived by `DeploymentCut.initial`. -/
structure DeploymentCut {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn CoveredFork cfg pre post) where
  /-- The transaction's position in the block's decoded transaction list. -/
  position : Nat
  cut : block.bodyTrace.transactions.TxSplit position
  /-- The recorded coordinates: block 24,993,190, transaction index 1,219. -/
  number : block.block.header.number = 24993190
  index : position = 1219
  /-- A contract creation: the transaction's `to` field is empty. -/
  creation : cut.tx.type.receiver? = none
  /-- Its input is the certified creation input (constructor, runtime template, arguments). -/
  input : cut.tx.data = code.toList
  /-- Its sender is the recorded deployer. -/
  sender : cut.head.sender = deployer
  /-- At nonce zero. -/
  nonce : cut.tx.nonce = 0
  /-- Transferring no ether. -/
  value : cut.tx.value = 0
  /-- The prepared message carries at least 1,000,000 gas (transaction gas limit less the
  intrinsic charge). -/
  gas : 1000000 ≤ cut.head.msg.gas
  /-- The receipt at this transaction's index in the block's own receipt trie. -/
  receipt : Fin 5 × Receipt
  receiptAt :
    block.blockOutput.receiptsTrie[BLT.toBytes (.bytes cut.index.toBytes)]? = some receipt
  /-- That receipt reports success. -/
  succeeded : receipt.2.succeeded = true

namespace DeploymentCut

variable {cfg : ChainConfig} {pre post : BlockChain}
  {block : ConfiguredBlockTraceIn CoveredFork cfg pre post}

/-- The creation message targets the CircuitBreaker's address. -/
theorem msg_currentTarget (deployment : DeploymentCut block) :
    deployment.cut.head.msg.currentTarget = breakerAddress := by
  rw [deployment.cut.head.creation_target_eq deployment.creation, deployment.sender,
    deployment.nonce, breakerAddress_eq]

/-- The selected transaction's environment runs the block's covered fork. -/
theorem fork (deployment : DeploymentCut block) :
    CoveredFork deployment.cut.benv.stat.fork := by
  have hselected := congrArg BenvStat.fork (block.txSplit_stat deployment.cut)
  change deployment.cut.benv.stat.fork = block.fork at hselected
  rw [hselected]
  exact block.forkIn

/-- **Deployment at the actual committed boundary.** Right after the creation transaction, the
CircuitBreaker's address holds the certified runtime and the constructor's storage
`deployedStor`. -/
theorem initial (deployment : DeploymentCut block) :
    (deployment.cut.afterBenv.state.getCode breakerAddress).toList =
        Blanc.Lift.LidoCircuitBreakerDeployed.code.toList ∧
      deployment.cut.afterBenv.state.getStor breakerAddress = deployedStor := by
  have hfork := deployment.fork
  have hsg : deployment.cut.benv.stat.rules.stateGas = none := hfork.rules_stateGas_none
  have clean : deployment.cut.head.messageOut.error = none :=
    block.txSplit_error_eq_none_of_receipt deployment.cut
      (BodyStageCapabilities.covered.stateGas_none block.forkIn) deployment.receiptAt
      deployment.succeeded
  have htarget := deployment.msg_currentTarget
  obtain ⟨-, codeEq, codeAddress, -, -, -⟩ :=
    deployment.cut.head.creation_message_fields deployment.creation deployment.input
  have hbenv := prepareMessage_benv deployment.cut.head.prepared
  have msgFork : CoveredFork deployment.cut.head.msg.benv.stat.fork := by
    rw [hbenv]; exact hfork
  have msgSg : deployment.cut.head.msg.benv.stat.rules.stateGas = none := by
    rw [hbenv]; exact hsg
  have hstatic : deployment.cut.head.msg.isStatic = false := by
    have prepared := deployment.cut.head.prepared
    unfold prepareMessage at prepared
    cases receiver : deployment.cut.tx.type.receiver? <;>
      simp only [receiver] at prepared <;>
      exact (congrArg Msg.isStatic (Except.ok.inj prepared)).symm
  have hvalue : deployment.cut.head.msg.value = 0 := by
    have prepared := deployment.cut.head.prepared
    have hmv : deployment.cut.head.msg.value = deployment.cut.tx.value.toB256 := by
      unfold prepareMessage at prepared
      cases receiver : deployment.cut.tx.type.receiver? <;>
        simp only [receiver] at prepared <;>
        exact (congrArg Msg.value (Except.ok.inj prepared)).symm
    rw [hmv, deployment.value]
    rfl
  have hmax : 4584 ≤ deployment.cut.head.msg.benv.stat.rules.code.maxCodeSize :=
    msgFork.cases (motive := fun f => 4584 ≤ (Fork.ruleSet f).code.maxCodeSize)
      (by decide) (by decide) (by decide) (by decide)
  obtain ⟨post, hcreate, hcodePost, hstorPost⟩ :=
    lido_create deployment.cut.head.msg hvalue codeAddress codeEq deployment.gas msgFork hstatic hmax
  obtain ⟨entry, first, silent, refs⟩ := cert_entry_balSilent
  have hstate := deployment.cut.head.getCode_getStor_of_create_effects
    (window := Blanc.Lift.LidoCircuitBreakerDeployed.code.toList) (storage := deployedStor)
    hsg deployment.creation deployment.input clean (by
      intro h
      have := Blanc.Lift.LidoCircuitBreakerDeployed.code_toList_length
      rw [h] at this
      cases this)
    (fun {installed} retained cleanInstalled => by
      have hsame : installed = post :=
        Except.ok.inj (retained.result.symm.trans hcreate)
      subst hsame
      exact ⟨createTrace_deletions_of_balSilent cert_check codeEq first cert_balSilentSet silent
        refs retained cleanInstalled codeAddress msgSg, hcodePost, hstorPost⟩)
  rw [htarget] at hstate
  exact hstate

end DeploymentCut

end Blanc.Lift.LidoCircuitBreakerDeployed.Creation
