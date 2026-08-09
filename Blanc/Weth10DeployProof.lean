-- Proof-side facts for WETH10 fresh deployment.
--
-- This module keeps the initcode emitter usable without importing the backing
-- property layer.  It joins the emitted artifact, the parameterized compiler
-- witness, Jaune's generic creation-state preparation, and Jaune's gas
-- constants.  It proves both the gas-exact hand-emitted constructor walk and
-- the direct creation-message settlement that deposits the fresh parameterized
-- runtime.  Top-level transaction and intrinsic-gas accounting remain stated
-- separately from that creation-message semantic boundary.

import Blanc.Weth10Backed
import Blanc.Weth10DeployExec

namespace Blanc

open Jaune

namespace Weth10

/-! ## Parameterized runtime and creation-state preparation -/

/-- Every freshly derived parameter pair has the universal compiled runtime
family member promised by `weth10Code_compile`. -/
theorem freshDeployParams_runtime_compile
    (chainId : B256) (contractAddress : Adr) :
    Prog.compile (weth10 (freshDeployParams chainId contractAddress)) =
      some (weth10Code (freshDeployParams chainId contractAddress)) :=
  weth10Code_compile _

/-- Jaune's generic creation preparation clears the new account's storage
before incrementing its nonce.  This theorem is about that generic preparation
step, independently of which initcode the resulting frame executes. -/
theorem processCreateMessage_msg_getStor_currentTarget (msg : Msg) :
    (processCreateMessage.msg msg).benv.state.getStor msg.currentTarget =
      Stor.empty := by
  change (((msg.benv.state.setStor msg.currentTarget .empty).incrNonce
    msg.currentTarget).get msg.currentTarget).stor = .empty
  rw [State.incrNonce_get_stor]
  unfold State.setStor
  rw [State.get_set_self]

/-- The storage seeded by Jaune's generic creation preparation establishes
WETH10's exact backing invariant when its logical callvalue and ETH-balance
parameters are both instantiated with zero. -/
theorem processCreateMessage_msg_weth10Inv (msg : Msg) :
    Stor.Weth10Inv
      ((processCreateMessage.msg msg).benv.state.getStor msg.currentTarget)
      0 0 := by
  rw [processCreateMessage_msg_getStor_currentTarget]
  exact Stor.Weth10Inv.of_empty

/-! ## Closed deployment-gas accounting

The figures below use Jaune's global opcode schedule.  They keep three
accounting boundaries separate:

* a direct creation message pays initcode execution plus code deposit;
* an internal `CREATE` additionally pays `gasCreate`, EIP-3860 initcode-word
  metering, and caller-memory extension (the last term is caller-dependent and
  therefore excluded from the closed core below);
* a top-level creation transaction pays calldata, `txCreateCost`, and the same
  EIP-3860 word metering as intrinsic gas before the creation message.

The direct creation-message theorem below links the first boundary to the
hand-emitted constructor execution.  The transaction-level expressions remain
closed arithmetic facts rather than a transaction-interpreter theorem, so
`weth10TopLevelDeploymentGasBound` bounds the named accounting expression; it
must not be cited as a proved transaction-execution bound until that bytecode
execution crossing is supplied.
-/

private def calldataTokens : Bytes → Nat
  | [] => 0
  | byte :: rest =>
      (if byte = 0 then 1 else 4) + calldataTokens rest

private theorem calldataTokens_foldl (data : Bytes) (acc : Nat) :
    data.foldl (fun n byte => n + if byte = 0 then 1 else 4) acc =
      acc + calldataTokens data := by
  induction data generalizing acc with
  | nil => rfl
  | cons byte rest ih =>
      simp only [List.foldl_cons, calldataTokens]
      rw [ih]
      exact Nat.add_assoc acc (if byte = 0 then 1 else 4)
        (calldataTokens rest)

private theorem calldataTokens_le (data : Bytes) :
    calldataTokens data ≤ 4 * data.length := by
  induction data with
  | nil => simp [calldataTokens]
  | cons byte rest ih =>
      simp only [calldataTokens, List.length_cons]
      split
      · rw [Nat.mul_add, Nat.mul_one, Nat.add_comm (4 * rest.length) 4]
        exact Nat.add_le_add (by decide) ih
      · rw [Nat.mul_add, Nat.mul_one, Nat.add_comm (4 * rest.length) 4]
        exact Nat.add_le_add (Nat.le_refl 4) ih

private theorem calldataTokens_foldl_le (data : Bytes) :
    data.foldl (fun n byte => n + if byte = 0 then 1 else 4) 0 ≤
      4 * data.length := by
  rw [calldataTokens_foldl]
  simpa only [Nat.zero_add] using calldataTokens_le data

/-- The exact EIP-7623 token count used by Jaune's transaction intrinsic-gas
formula for this initcode. -/
def weth10InitCodeCalldataTokens : Nat :=
  weth10InitCode.foldl
    (fun acc byte => acc + if byte = 0 then 1 else 4) 0

/-- Every initcode byte contributes at most four calldata tokens. -/
theorem weth10InitCodeCalldataTokens_le :
    weth10InitCodeCalldataTokens ≤ 4 * weth10InitCode.length := by
  unfold weth10InitCodeCalldataTokens
  exact calldataTokens_foldl_le weth10InitCode

/-- Successful-prefix schedule: nonpayability branch, runtime `CODECOPY`,
three chain-word patches, five EIP-712 scratch words, `KECCAK256`, two domain
patches, and `RETURN`.  `RETURN` itself has zero base cost; its memory window
was already expanded by `CODECOPY`. -/
def weth10InitExecutionGasAccounting : Nat :=
  let runtimeLength := weth10RuntimeTemplate.length
  let scratch := 32 * ceilDiv runtimeLength 32
  -- CALLVALUE, ISZERO, PUSH2, JUMPI, JUMPDEST.
  (gBase + gVerylow + gVerylow + gHigh + gJumpdest) +
  -- CODECOPY arguments.
  (gVerylow + gVerylow + gBase) +
  -- CODECOPY, including copying and initial memory expansion.
  (gVerylow + gasCopy * ceilDiv runtimeLength 32 +
    calculateMemoryGasCost scratch) +
  -- CHAINID, PUSH2, MSTORE at each generated chain-word occurrence.
  deploymentChainIdWordOffsets.length * (gBase + gVerylow + gVerylow) +
  -- Three constant words, then CHAINID and ADDRESS scratch words.
  (3 * (gVerylow + gVerylow + gVerylow) +
    (gBase + gVerylow + gVerylow) +
    (gBase + gVerylow + gVerylow)) +
  -- Total telescoped memory expansion across the five scratch MSTOREs.
  (calculateMemoryGasCost (scratch + 160) -
    calculateMemoryGasCost scratch) +
  -- Two PUSH2s and a five-word KECCAK256.
  (gVerylow + gVerylow + gKeccak256 +
    gasKeccak256Word * ceilDiv 160 32) +
  -- DUP1, PUSH2, MSTORE at each generated domain-word occurrence.
  cachedDomainSeparatorWordOffsets.length *
    (gVerylow + gVerylow + gVerylow) +
  -- POP, then PUSH2/PUSH0 before zero-base-cost RETURN.
  gBase + (gVerylow + gBase)

private theorem deploymentChainIdWordOffsets_length :
    deploymentChainIdWordOffsets.length = 3 := by
  decide +kernel

private theorem cachedDomainSeparatorWordOffsets_length :
    cachedDomainSeparatorWordOffsets.length = 2 := by
  decide +kernel

private theorem initExecutionGasFormula_eq
    (runtimeLength chainWords domainWords : Nat)
    (hruntime : runtimeLength = 6313)
    (hchain : chainWords = 3)
    (hdomain : domainWords = 2) :
    let scratch := 32 * ceilDiv runtimeLength 32
    (gBase + gVerylow + gVerylow + gHigh + gJumpdest) +
    (gVerylow + gVerylow + gBase) +
    (gVerylow + gasCopy * ceilDiv runtimeLength 32 +
      calculateMemoryGasCost scratch) +
    chainWords * (gBase + gVerylow + gVerylow) +
    (3 * (gVerylow + gVerylow + gVerylow) +
      (gBase + gVerylow + gVerylow) +
      (gBase + gVerylow + gVerylow)) +
    (calculateMemoryGasCost (scratch + 160) -
      calculateMemoryGasCost scratch) +
    (gVerylow + gVerylow + gKeccak256 +
      gasKeccak256Word * ceilDiv 160 32) +
    domainWords * (gVerylow + gVerylow + gVerylow) +
    gBase + (gVerylow + gBase) = 1471 := by
  subst runtimeLength
  subst chainWords
  subst domainWords
  simp [gBase, gVerylow, gHigh, gJumpdest, gasCopy, gMemory,
    calculateMemoryGasCost, gKeccak256, gasKeccak256Word, ceilDiv]

theorem weth10InitExecutionGasAccounting_eq :
    weth10InitExecutionGasAccounting = 1471 := by
  unfold weth10InitExecutionGasAccounting
  exact initExecutionGasFormula_eq
    weth10RuntimeTemplate.length deploymentChainIdWordOffsets.length
    cachedDomainSeparatorWordOffsets.length weth10RuntimeTemplate_length
    deploymentChainIdWordOffsets_length
    cachedDomainSeparatorWordOffsets_length

/-- Code-deposit charge applied by `processCreateMessage.chargeCodeGas` to the
6,313-byte returned runtime. -/
def weth10CodeDepositGas : Nat :=
  weth10RuntimeTemplate.length * gasCodeDeposit

theorem weth10CodeDepositGas_eq : weth10CodeDepositGas = 1262600 := by
  calc
    weth10CodeDepositGas = 6313 * gasCodeDeposit := by
      unfold weth10CodeDepositGas
      rw [weth10RuntimeTemplate_length]
    _ = 1262600 := by rfl

/-- EIP-3860's two-gas-per-word charge for the 6,490-byte initcode. -/
def weth10Eip3860InitCodeGas : Nat :=
  initCodeCost weth10InitCode.length

theorem weth10Eip3860InitCodeGas_eq : weth10Eip3860InitCodeGas = 406 := by
  calc
    weth10Eip3860InitCodeGas = initCodeCost 6490 := by
      unfold weth10Eip3860InitCodeGas
      rw [weth10InitCode_length]
    _ = 406 := by rfl

/-- Closed successful-path accounting inside a direct creation message:
initcode execution plus runtime code deposit. -/
def weth10CreateMessageGasAccounting : Nat :=
  weth10InitExecutionGasAccounting + weth10CodeDepositGas

theorem weth10CreateMessageGasAccounting_eq :
    weth10CreateMessageGasAccounting = 1264071 := by
  calc
    weth10CreateMessageGasAccounting = 1471 + 1262600 := by
      unfold weth10CreateMessageGasAccounting
      rw [weth10InitExecutionGasAccounting_eq,
        weth10CodeDepositGas_eq]
    _ = 1264071 := by rfl

private theorem weth10CreateMessageGas_sub_certificate
    (g : Nat) (h : 1264071 ≤ g) :
    1262600 ≤ g - 1471 ∧
      (g - 1471) - 1262600 = g - 1264071 := by
  constructor
  · apply Nat.le_sub_of_add_le
    simpa using h
  · simpa using (Nat.sub_sub g 1471 1262600)

/-- Closed core charged by an internal `CREATE`, excluding the caller's
memory-extension term and the instructions used to place initcode in memory. -/
def weth10CreateOpcodeCoreGasAccounting : Nat :=
  gasCreate + weth10Eip3860InitCodeGas + weth10CreateMessageGasAccounting

theorem weth10CreateOpcodeCoreGasAccounting_eq :
    weth10CreateOpcodeCoreGasAccounting = 1296477 := by
  calc
    weth10CreateOpcodeCoreGasAccounting =
        gasCreate + 406 + 1264071 := by
      unfold weth10CreateOpcodeCoreGasAccounting
      rw [weth10Eip3860InitCodeGas_eq,
        weth10CreateMessageGasAccounting_eq]
    _ = 1296477 := by rfl

/-- Exact closed accounting expression for a zero-access-list top-level
creation transaction followed by the successful direct creation-message path. -/
def weth10TopLevelDeploymentGasAccounting : Nat :=
  txBaseCost +
    weth10InitCodeCalldataTokens * standardCallDataTokenCost +
    txCreateCost + weth10Eip3860InitCodeGas +
    weth10CreateMessageGasAccounting

/-- Closed worst-case-calldata ceiling for the preceding top-level accounting
expression.  This retains Jaune's base, CREATE, EIP-3860, init execution, and
code-deposit components exactly. -/
def weth10TopLevelDeploymentGasBound : Nat :=
  txBaseCost +
    (4 * weth10InitCode.length) * standardCallDataTokenCost +
    txCreateCost + weth10Eip3860InitCodeGas +
    weth10CreateMessageGasAccounting

theorem weth10TopLevelDeploymentGasAccounting_le_bound :
    weth10TopLevelDeploymentGasAccounting ≤
      weth10TopLevelDeploymentGasBound := by
  have htokens := weth10InitCodeCalldataTokens_le
  have hcost :
      weth10InitCodeCalldataTokens * standardCallDataTokenCost ≤
        (4 * weth10InitCode.length) * standardCallDataTokenCost :=
    Nat.mul_le_mul_right standardCallDataTokenCost htokens
  have hbase := Nat.add_le_add_left hcost txBaseCost
  have hcreate := Nat.add_le_add_right hbase txCreateCost
  have heip := Nat.add_le_add_right hcreate weth10Eip3860InitCodeGas
  have hmessage :=
    Nat.add_le_add_right heip weth10CreateMessageGasAccounting
  unfold weth10TopLevelDeploymentGasAccounting
    weth10TopLevelDeploymentGasBound
  exact hmessage

theorem weth10TopLevelDeploymentGasBound_eq :
    weth10TopLevelDeploymentGasBound = 1421317 := by
  calc
    weth10TopLevelDeploymentGasBound =
        txBaseCost + (4 * 6490) * standardCallDataTokenCost +
          txCreateCost + 406 + 1264071 := by
      unfold weth10TopLevelDeploymentGasBound
      rw [weth10InitCode_length, weth10Eip3860InitCodeGas_eq,
        weth10CreateMessageGasAccounting_eq]
    _ = 1421317 := by rfl

/-! ## Creation-message settlement -/

private theorem setMach_output_eq (d : Devm) (m : Mach) :
    (d.setMach m).output = d.output := rfl

private theorem setMach_state_eq (d : Devm) (m : Mach) :
    (d.setMach m).state = d.state := rfl

private theorem setMach_logs_eq (d : Devm) (m : Mach) :
    (d.setMach m).logs = d.logs := rfl

private theorem setMach_error_eq (d : Devm) (m : Mach) :
    (d.setMach m).error = d.error := rfl

private theorem setMach_refundCounter_eq (d : Devm) (m : Mach) :
    (d.setMach m).refundCounter = d.refundCounter := rfl

private theorem setMach_accountsToDelete_eq (d : Devm) (m : Mach) :
    (d.setMach m).accountsToDelete = d.accountsToDelete := rfl

private theorem setMach_gasLeft_eq (d : Devm) (m : Mach) :
    (d.setMach m).gasLeft = m.gasLeft := rfl

private theorem chargeCodeGas_exists_of_eq
    {rules : ForkRules} {d : Devm} {m : Mach}
    (h : processCreateMessage.chargeCodeGas rules d = .ok (d.setMach m)) :
    ∃ charged, processCreateMessage.chargeCodeGas rules d = .ok charged :=
  ⟨d.setMach m, h⟩

private theorem chargeCodeGas_ok_eq_setMach
    {rules : ForkRules} {d charged : Devm} {m : Mach}
    (hc : processCreateMessage.chargeCodeGas rules d = .ok charged)
    (hm : processCreateMessage.chargeCodeGas rules d = .ok (d.setMach m)) :
    charged = d.setMach m :=
  Except.ok.inj (hc.symm.trans hm)

private theorem chargeCodeGas_ok_output
    {rules : ForkRules} {d charged : Devm} {m : Mach}
    (hc : processCreateMessage.chargeCodeGas rules d = .ok charged)
    (hm : processCreateMessage.chargeCodeGas rules d = .ok (d.setMach m)) :
    charged.output = d.output := by
  rw [chargeCodeGas_ok_eq_setMach hc hm]
  exact setMach_output_eq d m

private theorem chargeCodeGas_ok_state
    {rules : ForkRules} {d charged : Devm} {m : Mach}
    (hc : processCreateMessage.chargeCodeGas rules d = .ok charged)
    (hm : processCreateMessage.chargeCodeGas rules d = .ok (d.setMach m)) :
    charged.state = d.state := by
  rw [chargeCodeGas_ok_eq_setMach hc hm]
  exact setMach_state_eq d m

private theorem chargeCodeGas_ok_logs
    {rules : ForkRules} {d charged : Devm} {m : Mach}
    (hc : processCreateMessage.chargeCodeGas rules d = .ok charged)
    (hm : processCreateMessage.chargeCodeGas rules d = .ok (d.setMach m)) :
    charged.logs = d.logs := by
  rw [chargeCodeGas_ok_eq_setMach hc hm]
  exact setMach_logs_eq d m

private theorem chargeCodeGas_ok_error
    {rules : ForkRules} {d charged : Devm} {m : Mach}
    (hc : processCreateMessage.chargeCodeGas rules d = .ok charged)
    (hm : processCreateMessage.chargeCodeGas rules d = .ok (d.setMach m)) :
    charged.error = d.error := by
  rw [chargeCodeGas_ok_eq_setMach hc hm]
  exact setMach_error_eq d m

private theorem chargeCodeGas_ok_refundCounter
    {rules : ForkRules} {d charged : Devm} {m : Mach}
    (hc : processCreateMessage.chargeCodeGas rules d = .ok charged)
    (hm : processCreateMessage.chargeCodeGas rules d = .ok (d.setMach m)) :
    charged.refundCounter = d.refundCounter := by
  rw [chargeCodeGas_ok_eq_setMach hc hm]
  exact setMach_refundCounter_eq d m

private theorem chargeCodeGas_ok_accountsToDelete
    {rules : ForkRules} {d charged : Devm} {m : Mach}
    (hc : processCreateMessage.chargeCodeGas rules d = .ok charged)
    (hm : processCreateMessage.chargeCodeGas rules d = .ok (d.setMach m)) :
    charged.accountsToDelete = d.accountsToDelete := by
  rw [chargeCodeGas_ok_eq_setMach hc hm]
  exact setMach_accountsToDelete_eq d m

private theorem chargeCodeGas_ok_gasLeft
    {rules : ForkRules} {d charged : Devm} {m : Mach}
    (hc : processCreateMessage.chargeCodeGas rules d = .ok charged)
    (hm : processCreateMessage.chargeCodeGas rules d = .ok (d.setMach m)) :
    charged.gasLeft = m.gasLeft := by
  rw [chargeCodeGas_ok_eq_setMach hc hm]
  exact setMach_gasLeft_eq d m

private theorem weth10Code_cons (dp : DeployParams) :
    ∃ tail, weth10Code dp = 0x5b :: tail := by
  have h := weth10Code_compile dp
  unfold Prog.compile at h
  rcases Table.compile_cons_eq_some h with ⟨cp, ct, hcp, hct, hbytes⟩
  refine ⟨cp ++ ct, ?_⟩
  change weth10Code dp = Jinst.jumpdest.toUInt8 :: (cp ++ ct)
  exact hbytes

private theorem benvAfterTransfer_exists_zero
    {msg : Msg} (h_value : msg.value = 0) :
    ∃ benv, msg.benvAfterTransfer = .ok benv := by
  have hnot : ¬ msg.benv.state.bal msg.caller < (0 : B256) := by
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_zero]
    omega
  unfold Msg.benvAfterTransfer
  rw [h_value]
  by_cases h_stv : msg.shouldTransferValue = true
  · rw [if_pos h_stv]
    unfold Benv.subBal State.subBal
    rw [if_neg hnot]
    exact ⟨_, rfl⟩
  · rw [if_neg h_stv]
    exact ⟨_, rfl⟩

private theorem benvAfterTransfer_getStor
    {msg : Msg} {benv' : Benv}
    (h : msg.benvAfterTransfer = .ok benv') (a : Adr) :
    benv'.state.getStor a = msg.benv.state.getStor a := by
  by_cases h_stv : msg.shouldTransferValue = true
  · obtain ⟨st_mid, h_sub, rfl⟩ := of_benvAfterTransfer h_stv h
    exact (of_state_transfer_fields h_sub).1 a
  · rw [of_benvAfterTransfer_no h_stv h]

private theorem benvAfterTransfer_stat
    {msg : Msg} {benv' : Benv}
    (h : msg.benvAfterTransfer = .ok benv') :
    benv'.stat = msg.benv.stat := by
  by_cases h_stv : msg.shouldTransferValue = true
  · obtain ⟨st_mid, h_sub, rfl⟩ := of_benvAfterTransfer h_stv h
    rfl
  · rw [of_benvAfterTransfer_no h_stv h]

private theorem initEvm_exec_weth10_zero
    {msg : Msg}
    (h_value : msg.value = 0)
    (h_gas : 1471 ≤ msg.gas)
    (h_code : msg.code.toList = weth10InitCode) :
    exec (initEvm msg) =
      .ok (weth10InitPost (initSevm msg) (initDevm msg) msg.gas) :=
  weth10Init_exec_zero (sevm := initSevm msg) (base := initDevm msg)
    (g := msg.gas) h_value h_gas h_code

private theorem processMessage_ok_of_exec
    {msg : Msg} {benv : Benv} {post : Devm}
    (h_transfer : msg.benvAfterTransfer = .ok benv)
    (h_codeAddress : msg.codeAddress = .none)
    (h_exec : exec (initEvm (msg.withBenv benv)) = .ok post)
    (h_error : post.error = .none) :
    processMessage msg = .ok post := by
  unfold processMessage runFrame Frame.enter Frame.ofCall
  rw [h_transfer]
  unfold executeCode.enter
  simp only [Msg.withBenv, h_codeAddress]
  unfold Frame.settle Frame.settleMsg
  simp only [Msg.withBenv, h_codeAddress] at h_exec
  rw [h_exec]
  simp [executeCode.handleError, processMessage.settle, h_error]

private theorem chargeCodeGas_weth10_output
    {rules : ForkRules} {d : Devm} (dp : DeployParams)
    (h_output : d.output = weth10Code dp)
    (h_gas : 1262600 ≤ d.gasLeft)
    (h_max : 6313 ≤ rules.code.maxCodeSize) :
    processCreateMessage.chargeCodeGas rules d =
      .ok (d.setMach
        ⟨d.stack, d.memory, d.gasLeft - 1262600⟩) := by
  obtain ⟨tail, hcons⟩ := weth10Code_cons dp
  have hlen : (weth10Code dp).length = 6313 :=
    weth10Code_length dp
  unfold processCreateMessage.chargeCodeGas
  rw [h_output, hcons]
  rw [hcons] at hlen
  simp only [List.length_cons] at hlen
  simp only [List.length_cons, hlen, gasCodeDeposit]
  rw [chargeGas_eq_ok h_gas]
  change
    ((if rules.code.maxCodeSize < 6313 then
      Except.error ⟨.halt (.outOfGas .none), _⟩
    else Except.ok _) : Execution) = Except.ok _
  rw [if_neg (by omega)]

private structure Weth10CodeGasCheckpoint
    (rules : ForkRules) (d : Devm) (dp : DeployParams)
    (charged : Devm) : Prop where
  charge : processCreateMessage.chargeCodeGas rules d = .ok charged
  output : charged.output = weth10Code dp
  state : charged.state = d.state
  logs : charged.logs = d.logs
  error : charged.error = d.error
  refundCounter : charged.refundCounter = d.refundCounter
  accountsToDelete : charged.accountsToDelete = d.accountsToDelete
  gas : charged.gasLeft = d.gasLeft - 1262600

private theorem chargeCodeGas_weth10_checkpoint
    {rules : ForkRules} {d : Devm} (dp : DeployParams)
    (h_output : d.output = weth10Code dp)
    (h_gas : 1262600 ≤ d.gasLeft)
    (h_max : 6313 ≤ rules.code.maxCodeSize) :
    ∃ charged, Weth10CodeGasCheckpoint rules d dp charged := by
  let m : Mach := ⟨d.stack, d.memory, d.gasLeft - 1262600⟩
  have hm :
      processCreateMessage.chargeCodeGas rules d = .ok (d.setMach m) := by
    simpa only [m] using
      chargeCodeGas_weth10_output dp h_output h_gas h_max
  obtain ⟨charged, hc⟩ := chargeCodeGas_exists_of_eq hm
  refine ⟨charged, {
    charge := hc
    output := ?_
    state := ?_
    logs := ?_
    error := ?_
    refundCounter := ?_
    accountsToDelete := ?_
    gas := ?_ }⟩
  · exact (chargeCodeGas_ok_output hc hm).trans h_output
  · exact chargeCodeGas_ok_state hc hm
  · exact chargeCodeGas_ok_logs hc hm
  · exact chargeCodeGas_ok_error hc hm
  · exact chargeCodeGas_ok_refundCounter hc hm
  · exact chargeCodeGas_ok_accountsToDelete hc hm
  · exact (chargeCodeGas_ok_gasLeft hc hm).trans (by rfl)

private structure Weth10InitCheckpoint
    (msg : Msg) (initPost : Devm) : Prop where
  process :
    processMessage (processCreateMessage.msg msg) = .ok initPost
  output :
    initPost.output =
      weth10Code (freshDeployParams
        msg.benv.stat.chainId.toB256 msg.currentTarget)
  stor : initPost.state.getStor msg.currentTarget = Stor.empty
  logs : initPost.logs = []
  error : initPost.error = .none
  refundCounter : initPost.refundCounter = 0
  accountsToDelete : initPost.accountsToDelete = .emptyWithCapacity
  gas : initPost.gasLeft = msg.gas - 1471

private theorem processMessage_weth10_checkpoint
    (msg : Msg)
    (h_value : msg.value = 0)
    (h_codeAddress : msg.codeAddress = .none)
    (h_code : msg.code.toList = weth10InitCode)
    (h_gas : 1471 ≤ msg.gas) :
    ∃ initPost, Weth10InitCheckpoint msg initPost := by
  let prepared := processCreateMessage.msg msg
  obtain ⟨benv, h_transfer⟩ :=
    benvAfterTransfer_exists_zero (msg := prepared) h_value
  let seeded := prepared.withBenv benv
  let initPost :=
    weth10InitPost (initSevm seeded) (initDevm seeded) msg.gas
  have h_stat : benv.stat = msg.benv.stat := by
    calc
      benv.stat = prepared.benv.stat :=
        benvAfterTransfer_stat h_transfer
      _ = msg.benv.stat := by rfl
  have h_seed_value : seeded.value = 0 := h_value
  have h_seed_code : seeded.code.toList = weth10InitCode := h_code
  have h_seed_ca : seeded.codeAddress = .none := h_codeAddress
  have h_seed_gas : seeded.gas = msg.gas := rfl
  have h_exec : exec (initEvm seeded) = .ok initPost := by
    apply initEvm_exec_weth10_zero h_seed_value
    · rw [h_seed_gas]
      exact h_gas
    · exact h_seed_code
  have h_frame :=
    weth10InitPost_preserves_frame
      (sevm := initSevm seeded) (base := initDevm seeded) (g := msg.gas)
  have h_init_error : initPost.error = .none := by
    exact h_frame.2.2.trans (by rfl)
  have h_meta := weth10InitPost_preserves_transaction_meta
    (sevm := initSevm seeded) (base := initDevm seeded) (g := msg.gas)
  have h_pm : processMessage prepared = .ok initPost := by
    apply processMessage_ok_of_exec h_transfer h_seed_ca h_exec
      h_init_error
  have h_output :
      initPost.output =
        weth10Code (freshDeployParams
          msg.benv.stat.chainId.toB256 msg.currentTarget) := by
    have h := weth10InitPost_output_code
      (sevm := initSevm seeded) (base := initDevm seeded)
      (g := msg.gas) h_seed_code
    rw [show (initSevm seeded).benvStat.chainId =
        msg.benv.stat.chainId from congrArg BenvStat.chainId h_stat] at h
    exact h
  have h_prepared_stor :
      prepared.benv.state.getStor msg.currentTarget = Stor.empty :=
    processCreateMessage_msg_getStor_currentTarget msg
  have h_benv_stor :
      benv.state.getStor msg.currentTarget = Stor.empty := by
    rw [benvAfterTransfer_getStor h_transfer, h_prepared_stor]
  refine ⟨initPost, {
    process := h_pm
    output := h_output
    stor := ?_
    logs := ?_
    error := h_init_error
    refundCounter := h_meta.1.trans (by rfl)
    accountsToDelete := h_meta.2.1.trans (by rfl)
    gas := ?_ }⟩
  · rw [show initPost.state = (initDevm seeded).state from h_frame.1]
    exact h_benv_stor
  · exact h_frame.2.1.trans (by rfl)
  · exact (weth10InitFunc_runCompiled_zero
      (sevm := initSevm seeded) (base := initDevm seeded) (g := msg.gas)
      h_seed_value h_gas).2

private theorem processCreateMessage_weth10_settle_checkpoint
    (msg : Msg) {initPost charged : Devm}
    (h_pm :
      processMessage (processCreateMessage.msg msg) = .ok initPost)
    (h_error : initPost.error = .none)
    (h_charge :
      processCreateMessage.chargeCodeGas msg.benv.stat.rules initPost =
        .ok charged) :
    processCreateMessage msg =
      .ok (charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩) := by
  rw [processCreateMessage_eq, h_pm]
  unfold processCreateMessage.settle
  simp [h_error, h_charge]

private structure Weth10ChargeCheckpoint
    (msg : Msg) (dp : DeployParams) (charged : Devm) : Prop where
  process :
    processCreateMessage msg =
      .ok (charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩)
  output : charged.output = weth10Code dp
  stor : charged.state.getStor msg.currentTarget = Stor.empty
  logs : charged.logs = []
  error : charged.error = .none
  refundCounter : charged.refundCounter = 0
  accountsToDelete : charged.accountsToDelete = .emptyWithCapacity
  gas : charged.gasLeft = msg.gas - 1264071

private theorem processCreateMessage_weth10_charge_checkpoint
    (msg : Msg) {initPost : Devm}
    (init : Weth10InitCheckpoint msg initPost)
    (h_gas : 1264071 ≤ msg.gas)
    (h_max : 6313 ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ charged, Weth10ChargeCheckpoint msg
      (freshDeployParams
        msg.benv.stat.chainId.toB256 msg.currentTarget) charged := by
  obtain ⟨h_deposit_after_init, h_gas_after_deposit⟩ :=
    weth10CreateMessageGas_sub_certificate msg.gas h_gas
  have h_deposit : 1262600 ≤ initPost.gasLeft := by
    rw [init.gas]
    exact h_deposit_after_init
  obtain ⟨charged, checkpoint⟩ :=
    chargeCodeGas_weth10_checkpoint
      (freshDeployParams
        msg.benv.stat.chainId.toB256 msg.currentTarget)
      init.output h_deposit h_max
  refine ⟨charged, {
    process := processCreateMessage_weth10_settle_checkpoint msg
      init.process init.error checkpoint.charge
    output := checkpoint.output
    stor := ?_
    logs := ?_
    error := ?_
    refundCounter := ?_
    accountsToDelete := ?_
    gas := ?_ }⟩
  · rw [checkpoint.state]
    exact init.stor
  · rw [checkpoint.logs]
    exact init.logs
  · rw [checkpoint.error]
    exact init.error
  · rw [checkpoint.refundCounter]
    exact init.refundCounter
  · rw [checkpoint.accountsToDelete]
    exact init.accountsToDelete
  · rw [checkpoint.gas, init.gas]
    exact h_gas_after_deposit

private theorem weth10InstalledPost_certificate
    (msg : Msg) (dp : DeployParams) {charged : Devm}
    (h_process :
      processCreateMessage msg =
        .ok (charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩))
    (h_output : charged.output = weth10Code dp)
    (h_stor : charged.state.getStor msg.currentTarget = Stor.empty)
    (h_logs : charged.logs = [])
    (h_error : charged.error = .none)
    (h_refund : charged.refundCounter = 0)
    (h_delete : charged.accountsToDelete = .emptyWithCapacity)
    (h_gas : charged.gasLeft = msg.gas - 1264071) :
    ∃ post,
      processCreateMessage msg = .ok post ∧
      post.getCode msg.currentTarget = ⟨⟨weth10Code dp⟩⟩ ∧
      post.state.getStor msg.currentTarget = Stor.empty ∧
      Stor.Weth10Inv (post.state.getStor msg.currentTarget) 0 0 ∧
      post.logs = [] ∧
      post.output = weth10Code dp ∧
      post.gasLeft = msg.gas - 1264071 ∧
      post.error = .none ∧
      post.refundCounter = 0 ∧
      post.accountsToDelete = .emptyWithCapacity := by
  refine ⟨charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩,
    h_process, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Devm.getCode Devm.getAcct
    rw [Devm.setCode_state]
    unfold State.setCode
    rw [State.get_set_self]
    simp only [h_output]
  · rw [Devm.setCode_state]
    change
      ((charged.state.setCode msg.currentTarget
        ⟨⟨charged.output⟩⟩).get msg.currentTarget).stor = Stor.empty
    rw [State.setCode_get_stor]
    exact h_stor
  · rw [Devm.setCode_state]
    change Stor.Weth10Inv
      ((charged.state.setCode msg.currentTarget
        ⟨⟨charged.output⟩⟩).get msg.currentTarget).stor 0 0
    rw [State.setCode_get_stor]
    change Stor.Weth10Inv
      (charged.state.getStor msg.currentTarget) 0 0
    rw [h_stor]
    exact Stor.Weth10Inv.of_empty
  · exact h_logs
  · exact h_output
  · exact h_gas
  · exact h_error
  · exact h_refund
  · exact h_delete

private theorem processCreateMessage_weth10_success_raw
    (msg : Msg)
    (h_value : msg.value = 0)
    (h_codeAddress : msg.codeAddress = .none)
    (h_code : msg.code.toList = weth10InitCode)
    (h_gas : 1264071 ≤ msg.gas)
    (h_max : 6313 ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ post,
      processCreateMessage msg = .ok post ∧
      post.getCode msg.currentTarget =
        ⟨⟨weth10Code (freshDeployParams
          msg.benv.stat.chainId.toB256 msg.currentTarget)⟩⟩ ∧
      post.state.getStor msg.currentTarget = Stor.empty ∧
      Stor.Weth10Inv (post.state.getStor msg.currentTarget) 0 0 ∧
      post.logs = [] ∧
      post.output =
        weth10Code (freshDeployParams
          msg.benv.stat.chainId.toB256 msg.currentTarget) ∧
      post.gasLeft = msg.gas - 1264071 ∧
      post.error = .none ∧
      post.refundCounter = 0 ∧
      post.accountsToDelete = .emptyWithCapacity := by
  let dp :=
    freshDeployParams msg.benv.stat.chainId.toB256 msg.currentTarget
  obtain ⟨initPost, init⟩ :=
    processMessage_weth10_checkpoint msg h_value h_codeAddress h_code
      (by omega)
  obtain ⟨chargedPost, charged⟩ :=
    processCreateMessage_weth10_charge_checkpoint msg init h_gas h_max
  exact weth10InstalledPost_certificate
    (charged := chargedPost) msg dp charged.process
    charged.output charged.stor charged.logs charged.error
    charged.refundCounter charged.accountsToDelete charged.gas



/-- A fresh zero-endowment creation message executes the actual emitted
constructor, pays the named execution-plus-deposit charge, and installs the
exact runtime family member derived from the creation chain id and target.
The constructor leaves the freshly cleared storage empty and emits no logs. -/
theorem processCreateMessage_weth10_success
    (msg : Msg)
    (h_value : msg.value = 0)
    (h_codeAddress : msg.codeAddress = .none)
    (h_code : msg.code.toList = weth10InitCode)
    (h_gas : weth10CreateMessageGasAccounting ≤ msg.gas)
    (h_max : 6313 ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ post,
      processCreateMessage msg = .ok post ∧
      post.getCode msg.currentTarget =
        ⟨⟨weth10Code (freshDeployParams
          msg.benv.stat.chainId.toB256 msg.currentTarget)⟩⟩ ∧
      post.state.getStor msg.currentTarget = Stor.empty ∧
      Stor.Weth10Inv (post.state.getStor msg.currentTarget) 0 0 ∧
      post.logs = [] ∧
      post.output =
        weth10Code (freshDeployParams
          msg.benv.stat.chainId.toB256 msg.currentTarget) ∧
      post.gasLeft = msg.gas - weth10CreateMessageGasAccounting := by
  have h_gas' : 1264071 ≤ msg.gas := by
    rw [← weth10CreateMessageGasAccounting_eq]
    exact h_gas
  obtain ⟨post, h_process, h_installed, h_stor, h_inv, h_logs,
      h_output, h_left, _, _, _⟩ :=
    processCreateMessage_weth10_success_raw msg h_value h_codeAddress
      h_code h_gas' h_max
  exact ⟨post, h_process, h_installed, h_stor, h_inv, h_logs, h_output,
    by simpa only [weth10CreateMessageGasAccounting_eq] using h_left⟩

/-- The successful constructor result with the transaction-settlement metadata
needed by the top-level creation bridge. -/
theorem processCreateMessage_weth10_success_full
    (msg : Msg)
    (h_value : msg.value = 0)
    (h_codeAddress : msg.codeAddress = .none)
    (h_code : msg.code.toList = weth10InitCode)
    (h_gas : weth10CreateMessageGasAccounting ≤ msg.gas)
    (h_max : 6313 ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ post,
      processCreateMessage msg = .ok post ∧
      post.getCode msg.currentTarget =
        ⟨⟨weth10Code (freshDeployParams
          msg.benv.stat.chainId.toB256 msg.currentTarget)⟩⟩ ∧
      post.state.getStor msg.currentTarget = Stor.empty ∧
      Stor.Weth10Inv (post.state.getStor msg.currentTarget) 0 0 ∧
      post.logs = [] ∧
      post.output =
        weth10Code (freshDeployParams
          msg.benv.stat.chainId.toB256 msg.currentTarget) ∧
      post.gasLeft = msg.gas - weth10CreateMessageGasAccounting ∧
      post.error = .none ∧
      post.refundCounter = 0 ∧
      post.accountsToDelete = .emptyWithCapacity := by
  have h_gas' : 1264071 ≤ msg.gas := by
    rw [← weth10CreateMessageGasAccounting_eq]
    exact h_gas
  simpa only [weth10CreateMessageGasAccounting_eq] using
    processCreateMessage_weth10_success_raw msg h_value h_codeAddress
      h_code h_gas' h_max


/-! ## Static deployment certificate -/

/-- Static companion to `processCreateMessage_weth10_success`.  It bundles
parameter derivation, universal runtime compilation, the exact initcode tail,
constructor call-freedom, empty-storage preparation and `Weth10Inv`, and the
closed gas-accounting ceiling.  The preceding semantic theorem supplies the
successful settlement, exact deposited code, empty persistent storage, and
no-log facts for every creation message satisfying its explicit premises. -/
theorem freshDeployment_staticCertificate
    (chainId : B256) (contractAddress : Adr) :
    (freshDeployParams chainId contractAddress).deploymentChainId = chainId ∧
    (freshDeployParams chainId contractAddress).cachedDomainSeparator =
      deploymentDomainSeparator chainId contractAddress ∧
    Prog.compile (weth10 (freshDeployParams chainId contractAddress)) =
      some (weth10Code (freshDeployParams chainId contractAddress)) ∧
    weth10InitCode.drop weth10InitPrefix.length = weth10RuntimeTemplate ∧
    weth10InitCode.length = 6490 ∧
    weth10InitFunc.NoCalls ∧
    Stor.Weth10Inv Stor.empty 0 0 ∧
    (∀ msg : Msg, msg.currentTarget = contractAddress →
      Stor.Weth10Inv
        ((processCreateMessage.msg msg).benv.state.getStor contractAddress)
        0 0) ∧
    weth10CodeDepositGas = 1262600 ∧
    weth10Eip3860InitCodeGas = 406 ∧
    weth10CreateMessageGasAccounting = 1264071 ∧
    weth10TopLevelDeploymentGasAccounting ≤
      weth10TopLevelDeploymentGasBound ∧
    weth10TopLevelDeploymentGasBound = 1421317 := by
  refine ⟨rfl, rfl, freshDeployParams_runtime_compile _ _,
    weth10InitCode_drop_prefix, weth10InitCode_length,
    weth10InitFunc_noCalls, Stor.Weth10Inv.of_empty, ?_, weth10CodeDepositGas_eq,
    weth10Eip3860InitCodeGas_eq, weth10CreateMessageGasAccounting_eq,
    weth10TopLevelDeploymentGasAccounting_le_bound,
    weth10TopLevelDeploymentGasBound_eq⟩
  intro msg h_target
  simpa [h_target] using processCreateMessage_msg_weth10Inv msg

end Weth10

end Blanc
