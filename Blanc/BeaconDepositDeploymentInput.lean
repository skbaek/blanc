-- BeaconDepositDeploymentInput.lean : strict direct-deployment inputs.
--
-- Every public predicate in this owner is pre-execution. The prepared context
-- is proof-produced from those inputs and records the actual transaction-local
-- environment after the protocol-system prefix, nonce increment, and upfront
-- fee debit.

import Blanc.BeaconDepositDeploymentMessage

namespace Blanc

open Jaune

namespace BeaconDeposit

/-! ## Exact gas and transaction helpers -/

/-- Exact transaction gas selected by the strict deployment profile: ordinary
intrinsic gas plus the proved constructor-execution and code-deposit budget. -/
def deploymentTransactionGas (tx : Tx) : Nat :=
  deploymentIntrinsicGas tx + constructorCreateMessageGasAccounting

/-! ## Strict pre-execution inputs -/

/-- Strict singleton configured block and byte-retaining, round-tripping
type-2 direct creation transaction.  The schedule is the caller's `cfg`; every
fork-sensitive admission fact is stated against the block's selected `rules`.
`CanonicalBlock` retains the original block bytes and strict decode/re-encode
equations. -/
structure CanonicalBeaconDepositDeploymentBlock
    (cfg : ChainConfig) (rules : ForkRules)
    (base : BlockChain) (cb : CanonicalBlock)
    (txBytes : Bytes) (tx : Tx) (sender ca : Adr) : Prop where
  txs_eq : cb.block.txs = [.inl txBytes]
  decode_eq : decodeTx (.inl txBytes) = .ok tx
  ommers_eq : cb.block.ommers = []
  withdrawals_eq : cb.block.wds = []
  rulesAt : cfg.rulesAt cb.block.header.timestamp = .ok rules
  type_eq : ∃ maxPriorityFee maxFee,
    tx.type = .two cfg.chainId maxPriorityFee maxFee none []
  value_eq : tx.value = 0
  data_eq : tx.data = creationCode
  nonce_eq : tx.nonce = base.state.getNonce sender
  nonce_not_max : tx.nonce ≠ UInt64.max
  recoveredSender : recoverSender cfg.chainId tx = .ok sender
  validated : validateTransaction rules tx =
    .ok (calculateIntrinsicCost tx)
  checked :
    let benv := initBenv rules base cb.block.header
    checkTransaction benv.beginTransaction
      (deploymentTxPreludeBout .init tx 0) tx =
      .ok (sender, deploymentEffectiveGasPrice benv tx, [], 0)
  base_fee_le_effective :
    cb.block.header.baseFeePerGas ≤
      deploymentEffectiveGasPrice
        (initBenv rules base cb.block.header) tx
  upfront_funded :
    tx.gas * deploymentEffectiveGasPrice
        (initBenv rules base cb.block.header) tx ≤
      (base.state.bal sender).toNat
  gas_eq : tx.gas = deploymentTransactionGas tx
  calldata_floor_le : deploymentCalldataFloorGas tx ≤ tx.gas
  block_gas_room : tx.gas ≤ cb.block.header.gasLimit
  runtime_code_fits : 2891 ≤ rules.code.maxCodeSize
  sha_precompile : rules.isPrecomp 2
  target_eq : ca = computeContractAddress sender tx.nonce
  shaCode : getDelegatedCodeAddress (base.state.getCode 2) = none

/-- The actual transaction-local environments and prepared creation message.
Collision, original-storage, SHA-code, precompile, and warmth facts are all
derived at the message state. -/
structure PreparedDeploymentContext
    (cfg : ChainConfig) (rules : ForkRules)
    (base : BlockChain) (cb : CanonicalBlock)
    (tx : Tx) (sender ca : Adr) : Type where
  txInput : Benv
  begun : Benv
  debit : State
  tenv : Tenv
  msg : Msg
  systemPrefix : DeploymentSystemPrefix rules base cb.block txInput
  begun_eq : begun = txInput.beginTransaction
  debit_eq :
    (begun.state.incrNonce sender).subBal sender
      (tx.gas * deploymentEffectiveGasPrice txInput tx).toB256 = some debit
  tenv_eq : tenv = deploymentTenv txInput tx sender 0
  prepare_eq : prepareMessage {begun with state := debit} tenv tx = .ok msg
  msg_benv_eq : msg.benv = {begun with state := debit}
  msg_caller_eq : msg.caller = sender
  msg_target_eq : msg.target = none
  msg_gas_from_tx : msg.gas = tx.gas - deploymentIntrinsicGas tx
  msg_gas_eq : msg.gas = constructorCreateMessageGasAccounting
  msg_value_eq : msg.value = 0
  msg_data_eq : msg.data = []
  msg_code_eq : msg.code.toList = creationCode
  msg_codeAddress_eq : msg.codeAddress = none
  msg_shouldTransferValue_eq : msg.shouldTransferValue = true
  msg_auths_eq : msg.tenv.stat.auths = []
  msg_rules_eq : msg.benv.stat.rules = rules
  msg_chainId_eq : msg.benv.stat.chainId = cfg.chainId
  target_eq : msg.currentTarget = ca
  noCodeOrNonce : accountHasCodeOrNonce msg.benv.state ca = false
  noStorage : accountHasStorage msg.benv.state ca = false
  originalState_eq : msg.benv.stat.origState = base.state
  originalTargetStorage :
    (msg.benv.stat.origState.get ca).stor = Stor.empty
  shaCode : getDelegatedCodeAddress (msg.benv.state.getCode 2) = none
  shaWarm : (2 : Adr) ∈ msg.accessedAddresses
  codeSize_ok : 2891 ≤ msg.benv.stat.rules.code.maxCodeSize
  msg_static_eq : msg.isStatic = false
  msg_depth_eq : msg.depth = 1024
  shaPrecompile : decide (msg.benv.stat.rules.isPrecomp 2) = true

/-- Produce the real transaction input, original-state boundary, upfront
nonce/fee debit, and the direct-CREATE message returned by `prepareMessage`. -/
theorem prepareCanonicalDeploymentContext
    (cfg : ChainConfig) (rules : ForkRules)
    (base : BlockChain) (cb : CanonicalBlock)
    (tx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase cfg rules base sender ca)
    (henv : CanonicalBeaconDepositDeploymentBlock cfg rules base cb
      txBytes tx sender ca) :
    Nonempty (PreparedDeploymentContext cfg rules base cb tx sender ca) := by
  obtain ⟨⟨txInput, hprefix⟩⟩ :=
    canonicalDeploymentSystemPrefix cfg rules base cb sender ca hbase
  let begun := txInput.beginTransaction
  let fee := tx.gas * deploymentEffectiveGasPrice txInput tx
  have hbegunState : begun.state = base.state := by
    simpa [begun, Benv.beginTransaction] using hprefix.state_eq
  have hfeeLe : fee ≤ (begun.state.bal sender).toNat := by
    rw [hbegunState]
    have hprice : deploymentEffectiveGasPrice txInput tx =
        deploymentEffectiveGasPrice
          (initBenv rules base cb.block.header) tx := by
      rw [hprefix.txInput_eq]
      rfl
    simpa [fee, hprice] using henv.upfront_funded
  have hfeeLt : fee < 2 ^ 256 :=
    hfeeLe.trans_lt (B256.toNat_lt _)
  have hfeeEncoded : fee.toB256.toNat = fee :=
    B256.toNat_toB256_of_lt hfeeLt
  have hnotlt : ¬ (begun.state.incrNonce sender).bal sender <
      fee.toB256 := by
    rw [B256.lt_iff_toNat_lt_toNat, hfeeEncoded]
    change ¬ ((begun.state.incrNonce sender).get sender).bal.toNat < fee
    rw [State.incrNonce_get_bal]
    exact not_lt_of_ge hfeeLe
  let debit := (begun.state.incrNonce sender).setBal sender
    ((begun.state.incrNonce sender).bal sender - fee.toB256)
  have hdebit :
      (begun.state.incrNonce sender).subBal sender fee.toB256 =
        some debit := by
    unfold State.subBal
    rw [if_neg hnotlt]
  let tenv := deploymentTenv txInput tx sender 0
  let currentTarget :=
    computeContractAddress tenv.stat.origin
      (debit.getNonce tenv.stat.origin - 1)
  let msgBenv : Benv := {begun with state := debit}
  let msg : Msg :=
    { benv := msgBenv
      tenv := tenv
      caller := tenv.stat.origin
      target := tx.type.receiver?
      gas := tenv.stat.gas
      value := tx.value.toB256
      data := []
      code := .mk (.mk tx.data)
      depth := 1024
      currentTarget := currentTarget
      codeAddress := none
      shouldTransferValue := true
      isStatic := false
      accessedAddresses := tenv.stat.accessListAddresses.insertMany
        (msgBenv.stat.rules.precompiles ++ [tenv.stat.origin, currentTarget])
      accessedStorageKeys := tenv.stat.accessListStorageKeys
      disablePrecompiles := false }
  obtain ⟨maxPriorityFee, maxFee, htype⟩ := henv.type_eq
  have hreceiver : tx.type.receiver? = none := by
    rw [htype]
    rfl
  have hprepare : prepareMessage msgBenv tenv tx = .ok msg := by
    unfold prepareMessage
    rw [hreceiver]
    simp [msg, msgBenv, currentTarget, hreceiver]
  have hdebitNonce :
      debit.getNonce sender = base.state.getNonce sender + 1 := by
    dsimp only [debit]
    change (((begun.state.incrNonce sender).setBal sender _).get sender).nonce =
      base.state.getNonce sender + 1
    rw [State.setBal_get_self]
    change ((begun.state.incrNonce sender).get sender).nonce =
      base.state.getNonce sender + 1
    unfold State.incrNonce
    rw [State.get_set_self]
    change begun.state.getNonce sender + 1 = base.state.getNonce sender + 1
    rw [hbegunState]
  have htarget : msg.currentTarget = ca := by
    dsimp only [msg, currentTarget]
    change computeContractAddress sender (debit.getNonce sender - 1) = ca
    rw [hdebitNonce]
    simp
    exact hbase.target_eq.symm
  have htxChain : txInput.stat.chainId = base.chainId := by
    rw [hprefix.txInput_eq]
    rfl
  have htxRules : txInput.stat.rules = rules := by
    rw [hprefix.txInput_eq]
    rfl
  have hmsgChain : msg.benv.stat.chainId = cfg.chainId := by
    dsimp only [msg, msgBenv, begun]
    simpa [Benv.beginTransaction] using
      htxChain.trans hbase.chainId_eq.symm
  have hmsgRules : msg.benv.stat.rules = rules := by
    dsimp only [msg, msgBenv, begun]
    simpa [Benv.beginTransaction] using htxRules
  have hdebitTarget : debit.get ca = base.state.get ca := by
    dsimp only [debit]
    rw [State.setBal_get_ne hbase.sender_ne_target]
    unfold State.incrNonce
    rw [State.get_set_ne _ hbase.sender_ne_target]
    rw [hbegunState]
  have hnocode : accountHasCodeOrNonce msg.benv.state ca = false := by
    dsimp only [msg, msgBenv]
    have hpre := hbase.target_noCodeOrNonce
    unfold accountHasCodeOrNonce at hpre ⊢
    simpa [State.getNonce, State.getCode, hdebitTarget] using hpre
  have hnostor : accountHasStorage msg.benv.state ca = false := by
    dsimp only [msg, msgBenv]
    have hpre := hbase.target_noStorage
    unfold accountHasStorage at hpre ⊢
    simpa [State.getStor, hdebitTarget] using hpre
  have horiginal : msg.benv.stat.origState = base.state := by
    dsimp only [msg, msgBenv, begun]
    simpa [Benv.beginTransaction] using hprefix.state_eq
  have hbaseStorageEmpty : base.state.getStor ca = Stor.empty := by
    have hisEmpty : (base.state.getStor ca).isEmpty = true := by
      have hpre := hbase.target_noStorage
      unfold accountHasStorage at hpre
      simpa using hpre
    exact Std.TreeMap.eq_empty_of_isEmpty hisEmpty
  have horiginalTarget :
      (msg.benv.stat.origState.get ca).stor = Stor.empty := by
    rw [horiginal]
    exact hbaseStorageEmpty
  have hdebitShaCode : debit.getCode 2 = base.state.getCode 2 := by
    dsimp only [debit]
    rw [State.setBal_getCode]
    change ((begun.state.incrNonce sender).get 2).code =
      (base.state.get 2).code
    rw [State.incrNonce_get_code, hbegunState]
  have hshaCode :
      getDelegatedCodeAddress (msg.benv.state.getCode 2) = none := by
    dsimp only [msg, msgBenv]
    rw [hdebitShaCode]
    exact henv.shaCode
  have hmsgBenvRules : msgBenv.stat.rules = rules := by
    dsimp only [msgBenv, begun]
    simpa [Benv.beginTransaction] using htxRules
  have hshaWarm : (2 : Adr) ∈ msg.accessedAddresses := by
    have hmem : (2 : Adr) ∈ rules.precompiles := henv.sha_precompile
    dsimp only [msg]
    rw [hmsgBenvRules]
    simp [hmem]
  have hcodeSize : 2891 ≤ msg.benv.stat.rules.code.maxCodeSize := by
    rw [hmsgRules]
    exact henv.runtime_code_fits
  have hshaPre :
      decide (msg.benv.stat.rules.isPrecomp 2) = true := by
    rw [hmsgRules]
    exact decide_eq_true henv.sha_precompile
  have hmsgGas : msg.gas = constructorCreateMessageGasAccounting := by
    change tx.gas - deploymentIntrinsicGas tx = _
    rw [henv.gas_eq]
    unfold deploymentTransactionGas
    omega
  exact ⟨{
    txInput := txInput
    begun := begun
    debit := debit
    tenv := tenv
    msg := msg
    systemPrefix := hprefix
    begun_eq := rfl
    debit_eq := by simpa [fee] using hdebit
    tenv_eq := rfl
    prepare_eq := hprepare
    msg_benv_eq := rfl
    msg_caller_eq := rfl
    msg_target_eq := by simpa [msg] using hreceiver
    msg_gas_from_tx := rfl
    msg_gas_eq := hmsgGas
    msg_value_eq := by
      rw [show msg.value = tx.value.toB256 from rfl, henv.value_eq]
      decide
    msg_data_eq := rfl
    msg_code_eq := by
      rw [show msg.code = .mk (.mk tx.data) from rfl,
        henv.data_eq, ByteArray.toList_eq_toList_data]
    msg_codeAddress_eq := rfl
    msg_shouldTransferValue_eq := rfl
    msg_auths_eq := rfl
    msg_rules_eq := hmsgRules
    msg_chainId_eq := hmsgChain
    target_eq := htarget
    noCodeOrNonce := hnocode
    noStorage := hnostor
    originalState_eq := horiginal
    originalTargetStorage := horiginalTarget
    shaCode := hshaCode
    shaWarm := hshaWarm
    codeSize_ok := hcodeSize
    msg_static_eq := rfl
    msg_depth_eq := rfl
    shaPrecompile := hshaPre }⟩

end BeaconDeposit

end Blanc
