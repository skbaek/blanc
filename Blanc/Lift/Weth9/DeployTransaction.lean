import Blanc.Lift.Weth9.Creation.Deploy
import Blanc.Lift.Weth9.HistoricalCredits
import Blanc.Lift.Weth9.Contract
import Blanc.Lift.HistAccessMeta
import Blanc.TransactionForwardH
import Blanc.ExecDeterminism
import Blanc.ExecutionTransactionEffects
import Blanc.ExecutionAccountingAdmissionIn

/-!
# The WETH9 creation transaction under Byzantium

`Creation.weth9_deploy_byzantium` runs the recorded creation input as a CREATE message over
Jaune's default environment. This module runs it as the recorded creation *transaction*: a legacy
transaction with no receiver, the recorded creation input as data, zero value and sender nonce
446, processed by Jaune's `processTransaction` in a block whose fork the mainnet schedule selects
at the recorded deployment coordinates (block 4,719,568, timestamp 1,513,077,455: Byzantium,
`weth9_deployment_fork`).

The pre-state and block environment are abstract. The theorem reads only:

* the selected fork;
* the transaction's shape (legacy, no receiver, recorded input, zero value, nonce 446);
* Jaune's validation and admission results, with the recorded deployer as the admitted sender
  (sender recovery stays a premise);
* the deployer's funds for the up-front gas debit;
* gas: the intrinsic cost plus 720,000 within the transaction's gas, below `2^64`;
* the target address having neither code nor nonce (the CREATE collision check).

It concludes that `processTransaction` succeeds and that the settled post-transaction state holds
the certified WETH9 runtime and exactly the constructor's storage at `weth9Address`. The settled
state is Jaune's, including the Byzantium EIP-161 touched sweep, the self-destruct fold and the
refund/fee credits (`processTransaction_of_stagesH`).

`weth9_create_settledH` supplies the creation core's remaining outcome fields (no error, no
account scheduled for deletion beyond the inherited ones, zero refund under the legacy `SSTORE`
schedule) from the constructor's named final machine `ctorPostH`, identified with the run of
`ctor_run_framedH` by execution determinism.
-/

namespace Blanc.Lift.Weth9.Creation

open Jaune Blanc.Lift

/-- The constructor's final machine from the world `b` with `G` gas left: the `RETURN` of the
runtime window after the three storage writes. -/
def ctorPostH (sevm : Sevm) (b : Devm) (G : Nat) : Devm :=
  returnPost (St (afterSstoreH sevm (wDecimalsH sevm b) 2 18)
    [Nat.toB256 0, Nat.toB256 3124] m10w G) (Nat.toB256 0) (Nat.toB256 3124) []

/-- The constructor run of `ctor_run_framedH`, ending at the named machine `ctorPostH`. -/
theorem ctor_run_postH {sevm : Sevm} (fr : CtorFrameH sevm) (hcode : sevm.code = code)
    (hvalue : sevm.value = 0) {b : Devm}
    (hstor : ∀ x, (Devm.getStor b sevm.currentTarget).get x = 0) {G : Nat} (hG : 2300 ≤ G) :
    SProg.RunExact prog sevm (St b [] Mem.empty (G + ctorCostH sevm b)) (ctorPostH sevm b G) := by
  have hold0 : b.getStorVal sevm.currentTarget 0 = 0 := hstor 0
  have hold1 : (wNameH sevm b).getStorVal sevm.currentTarget 1 = 0 := by
    show (Devm.getStor (wNameH sevm b) sevm.currentTarget).get 1 = 0
    rw [wNameH, afterSstoreH_getStor_self, afterSloadH_getStor, Stor.get_set_ite,
      ite_eq_right (by decide)]
    exact hstor 1
  have hold2 : (wSymbolH sevm b).getStorVal sevm.currentTarget 2 = 0 := by
    show (Devm.getStor (wSymbolH sevm b) sevm.currentTarget).get 2 = 0
    rw [wSymbolH, afterSstoreH_getStor_self, afterSloadH_getStor, Stor.get_set_ite,
      ite_eq_right (by decide), wNameH, afterSstoreH_getStor_self, afterSloadH_getStor,
      Stor.get_set_ite, ite_eq_right (by decide)]
    exact hstor 2
  refine ⟨t_0000_c0, rfl, ?_⟩
  rw [show G + ctorCostH sevm b = G + 3 + copyCost + 45 +
      sstoreCostH sevm (wDecimalsH sevm b) 2 18 + 40 + sloadCostH sevm (wSymbolH sevm b) 2 + 28 +
      helperCostH sevm (wNameH sevm b) 1 symbolSlotWord + 8 + 101 +
      helperCostH sevm b 0 nameSlotWord + 8 + 116 by unfold ctorCostH; omega]
  exact segNameH fr hold0 (by omega) (segSymbolH fr hold1 (by omega)
    (segDecimalsH fr hcode hvalue hold2 hG))

theorem ctorPostH_accountsToDelete (sevm : Sevm) (b : Devm) (G : Nat) :
    (ctorPostH sevm b G).accountsToDelete = b.accountsToDelete := by
  show (afterSstoreH sevm (wDecimalsH sevm b) 2 18).accountsToDelete = _
  rw [afterSstoreH_accountsToDelete, wDecimalsH, afterSloadH_accountsToDelete, wSymbolH,
    afterSstoreH_accountsToDelete, afterSloadH_accountsToDelete, wNameH,
    afterSstoreH_accountsToDelete, afterSloadH_accountsToDelete]

/-- Under the legacy `SSTORE` schedule the constructor's three nonzero writes leave the refund
counter alone. -/
theorem ctorPostH_refundCounter {sevm : Sevm} (b : Devm) (G : Nat)
    (legacy : sevm.benvStat.rules.sstore.netMetering = false) :
    (ctorPostH sevm b G).refundCounter = b.refundCounter := by
  show (afterSstoreH sevm (wDecimalsH sevm b) 2 18).refundCounter = _
  rw [afterSstoreH_refundCounter_legacy _ _ legacy (by decide), wDecimalsH,
    afterSloadH_refundCounter, wSymbolH,
    afterSstoreH_refundCounter_legacy _ _ legacy (by decide +kernel), afterSloadH_refundCounter,
    wNameH, afterSstoreH_refundCounter_legacy _ _ legacy (by decide +kernel),
    afterSloadH_refundCounter]

/-- **The settled creation core's bookkeeping, from rule facts.**  Under the premises of
`weth9_create_framedH` and the legacy `SSTORE` refund schedule, the successful creation leaves no
error, schedules for deletion exactly the message's inherited deletions, and leaves a zero
refund counter. -/
theorem weth9_create_settledH (msg : Msg) (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = Blanc.Lift.Weth9.Creation.code)
    (hgas : 720000 ≤ msg.gas) (hgasb : msg.gas < 2 ^ 64)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (hflat : ∀ g, msg.benv.stat.rules.access = .flat g → g.sload ≤ 2100)
    (hlegacy : msg.benv.stat.rules.sstore.netMetering = false)
    (hstatic : msg.isStatic = false)
    (hmax : 3124 ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ post, processCreateMessage msg = .ok post ∧ post.error = none ∧
      post.accountsToDelete = msg.inheritedDeletions ∧ post.refundCounter = 0 := by
  obtain ⟨benv, htransfer⟩ :=
    benvAfterTransfer_exists_zero (msg := processCreateMessage.msg msg) hvalue
  set sevm := initSevm (createSeed msg benv) with hsevm
  set b := initDevm (createSeed msg benv) with hb
  have hstat : sevm.benvStat = msg.benv.stat := by
    show benv.stat = (processCreateMessage.msg msg).benv.stat
    exact benvAfterTransfer_stat htransfer
  have fr : CtorFrameH sevm := ⟨by rw [hstat]; exact hsg, hstatic⟩
  have hempty : Devm.getStor b sevm.currentTarget = Stor.empty := by
    show benv.state.getStor msg.currentTarget = _
    rw [benvAfterTransfer_ok_getStor htransfer _ (Or.inl (show (processCreateMessage.msg msg).value = 0
      from hvalue)), processCreateMessage_msg_getStor_currentTarget]
  have hstor : ∀ x, (Devm.getStor b sevm.currentTarget).get x = 0 := fun x => by
    rw [hempty]; simp only [Stor.get, Stor.empty, Std.TreeMap.empty_eq_emptyc,
      Std.TreeMap.getD_emptyc]
  have hle := ctorCostH_le sevm b (by rw [hstat]; exact hflat)
  obtain ⟨raw, hrun, hout, herr, -, hgasLeft, -⟩ :=
    ctor_run_framedH fr hcode hvalue hstor (G := msg.gas - ctorCostH sevm b) (by omega)
  have hnamed := ctor_run_postH fr hcode hvalue hstor (G := msg.gas - ctorCostH sevm b) (by omega)
  have hpre0 : St b [] Mem.empty (msg.gas - ctorCostH sevm b + ctorCostH sevm b) = b :=
    pre_eq_St rfl rfl (by show _ = msg.gas; omega)
  rw [hpre0] at hrun hnamed
  have hsgSevm : sevm.benvStat.rules.stateGas = none := by rw [hstat]; exact hsg
  obtain ⟨e₁⟩ := lift_exact_noStateGas Blanc.Lift.Weth9.Creation.cert_check
    Blanc.Lift.Weth9.Creation.jumps_ok hcode hsgSevm hrun
  obtain ⟨e₂⟩ := lift_exact_noStateGas Blanc.Lift.Weth9.Creation.cert_check
    Blanc.Lift.Weth9.Creation.jumps_ok hcode hsgSevm hnamed
  have hrawEq : raw = ctorPostH sevm b (msg.gas - ctorCostH sevm b) :=
    Except.ok.inj (Exec.result_unique e₁ e₂)
  have hwin : raw.output = Blanc.Lift.Weth9.code.toList := by
    rw [hout, runtimeWindow, ByteArray.sliceD_eq]
    exact runtime_window
  have hlen : raw.output.length = 3124 := by rw [hout]; exact runtimeWindow_length
  have hpost := liftCreate_postH Blanc.Lift.Weth9.Creation.cert_check
    Blanc.Lift.Weth9.Creation.jumps_ok msg
    hcodeAddress hcode hsg htransfer hrun (by rw [herr]; rfl)
    (by rw [hwin]; exact runtime_head)
    (by rw [hlen, hgasLeft]; unfold gasCodeDeposit; omega) (by rw [hlen]; exact hmax)
  refine ⟨_, hpost, ?_, ?_, ?_⟩
  · rw [(liftCreatePost_facts _ _).1, Devm.recordTouch_error, herr]
    rfl
  · show raw.accountsToDelete = _
    rw [hrawEq, ctorPostH_accountsToDelete]
    rfl
  · show raw.refundCounter = _
    rw [hrawEq, ctorPostH_refundCounter _ _ (by rw [hstat]; exact hlegacy)]
    rfl

/-- **The recorded WETH9 creation transaction under Byzantium.**  In a block whose fork the
mainnet schedule selects at WETH9's recorded deployment coordinates (block 4,719,568, timestamp
1,513,077,455), a legacy transaction with no receiver, the recorded creation input as data, zero
value and nonce 446, which Jaune validates and admits with the recorded deployer as sender, whose
sender can pay the up-front gas, whose gas covers the intrinsic cost plus 720,000 (below `2^64`),
and whose target address has neither code nor nonce, is processed by `processTransaction`; the
settled post-transaction state holds the certified WETH9 runtime and exactly the constructor's
storage at `weth9Address`. -/
theorem weth9_creation_transaction_byzantium
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {gasPrice intrinsicGas calldataFloorGas effectiveGasPrice : Nat}
    {blobVersionedHashes : List B256} {txBlobGasUsed : Nat}
    (hfork : mainnetChainConfig.forkAt 4719568 1513077455 = .ok benv.stat.fork)
    (htype : tx.type = .zero gasPrice none)
    (hdata : tx.data = Creation.code.toList)
    (hvalue : tx.value = 0) (hnonce : tx.nonce = 446)
    (hvalid : validateTransaction benv.stat.rules tx 0 = .ok (intrinsicGas, calldataFloorGas))
    (hchecked : checkTransaction benv.beginTransaction
      (ExecutionTrace.transactionPreludeBout bout tx index) tx =
        .ok (deployer, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed))
    (hfunds : (tx.gas * effectiveGasPrice).toB256 ≤ benv.state.bal deployer)
    (hgas : intrinsicGas + 720000 ≤ tx.gas) (hgasb : tx.gas < 2 ^ 64)
    (hfresh : accountHasCodeOrNonce benv.state weth9Address = false) :
    ∃ post bout', processTransaction benv bout tx index = .ok (post, bout') ∧
      (post.getCode weth9Address).toList = Blanc.Lift.Weth9.code.toList ∧
      post.getStor weth9Address = deployedStor := by
  have hbyz : benv.stat.fork = .byzantium := by
    have h := Blanc.Lift.Weth9.weth9_deployment_fork
    rw [hfork] at h
    exact Except.ok.inj h
  have hrules : benv.stat.rules = byzantiumRules := by rw [BenvStat.rules, hbyz]; rfl
  have hsg : benv.stat.rules.stateGas = none := by rw [hrules]; rfl
  have hbal : benv.stat.rules.bal = none := by rw [hrules]; rfl
  have hne : deployer ≠ weth9Address := by decide
  have hsenderNonce : (benv.state.get deployer).nonce = 446 := by
    rw [← hnonce]
    exact ExecutionTrace.checkTransaction_sender_nonce hchecked
  have hblob : ExecutionTrace.transactionBlobGasFee benv tx = 0 := by
    simp only [ExecutionTrace.transactionBlobGasFee, Tx.isTypeThree, htype, Bool.false_eq_true,
      ↓reduceIte]
  have hdebit : (benv.state.incrNonce deployer).subBal deployer
      (tx.gas * effectiveGasPrice + ExecutionTrace.transactionBlobGasFee benv tx).toB256 =
      some ((benv.state.incrNonce deployer).setBal deployer
        (benv.state.bal deployer - (tx.gas * effectiveGasPrice).toB256)) := by
    rw [hblob, Nat.add_zero]
    exact subBal_incrNonce_of_le hfunds
  set debit := (benv.state.incrNonce deployer).setBal deployer
    (benv.state.bal deployer - (tx.gas * effectiveGasPrice).toB256) with hdebitDef
  have hdebitSelf : (debit.get deployer).nonce = 447 := by
    rw [hdebitDef, debit_get_self (by rw [hsenderNonce]; decide)]
    simp only [hsenderNonce]
    rfl
  have hdebitW : debit.get weth9Address = benv.state.get weth9Address := debit_get_ne hne
  cases hprep : prepareMessage { benv.beginTransaction with state := debit }
      (ExecutionTrace.transactionTenv benv.beginTransaction tx index deployer effectiveGasPrice
        intrinsicGas blobVersionedHashes) tx with
  | error e =>
      simp only [prepareMessage, htype, TxType.receiver?] at hprep
      cases hprep
  | ok msg =>
  have hmsg := hprep
  simp only [prepareMessage, htype, TxType.receiver?] at hmsg
  have hmsgEq := (Except.ok.inj hmsg).symm
  have htarget : msg.currentTarget = weth9Address := by
    rw [hmsgEq]
    show computeContractAddress deployer ((debit.get deployer).nonce - 1) = _
    rw [hdebitSelf, weth9Address_eq]
    rfl
  have hmsgRules : msg.benv.stat.rules = byzantiumRules := by rw [hmsgEq]; exact hrules
  have hcodeEq : msg.code = Blanc.Lift.Weth9.Creation.code := by
    rw [hmsgEq]
    show ByteArray.mk (Array.mk tx.data) = _
    rw [hdata, ByteArray.toList_eq_toList_data]
  have hvalue' : msg.value = 0 := by rw [hmsgEq]; show tx.value.toB256 = 0; rw [hvalue]; rfl
  have hgas' : msg.gas = tx.gas - intrinsicGas := by rw [hmsgEq]; rfl
  have hsg' : msg.benv.stat.rules.stateGas = none := by rw [hmsgRules]; rfl
  have hflat : ∀ g, msg.benv.stat.rules.access = .flat g → g.sload ≤ 2100 := fun g h => by
    rw [hmsgRules, show byzantiumRules.access = .flat byzantiumAccessGas from rfl] at h
    cases h
    decide
  have hlegacy : msg.benv.stat.rules.sstore.netMetering = false := by rw [hmsgRules]; rfl
  have hstatic : msg.isStatic = false := by rw [hmsgEq]
  have hmax : 3124 ≤ msg.benv.stat.rules.code.maxCodeSize := by rw [hmsgRules]; decide
  have hcodeAddress : msg.codeAddress = .none := by rw [hmsgEq]
  have hinherited : msg.inheritedDeletions = .emptyWithCapacity := by rw [hmsgEq]
  have hmsgTarget : msg.target = none := by rw [hmsgEq]
  have hcollision : accountHasCodeOrNonce msg.benv.state msg.currentTarget = false := by
    rw [htarget, show msg.benv.state = debit by rw [hmsgEq]]
    unfold accountHasCodeOrNonce State.getNonce State.getCode
    rw [hdebitW]
    exact hfresh
  obtain ⟨post, hpost, herr, hatd, hrc⟩ := weth9_create_settledH msg hvalue' hcodeAddress hcodeEq
    (by omega) (by omega) hsg' hflat hlegacy hstatic hmax
  obtain ⟨post', hpost', hcodePost, hstorPost, -⟩ := weth9_create_framedH msg hvalue' hcodeAddress
    hcodeEq (by omega) (by omega) hsg' hflat hstatic hmax
  have hsame : post' = post := Except.ok.inj (hpost'.symm.trans hpost)
  subst hsame
  have hcall := processMessageCall_create_of_message (refund := 0) hsg' hmsgTarget hcollision hpost
    herr (by rw [hrc]; rfl)
  obtain ⟨bout', htx⟩ := processTransaction_of_stagesH hsg hbal hvalid hchecked hdebit hprep hcall
    (show Int.toNat? ((0 : Nat) : Int) = some 0 from rfl)
  refine ⟨_, bout', htx, ?_⟩
  rw [htarget] at hcodePost hstorPost
  have hcodeNe : (post'.state.getCode weth9Address).toList ≠ [] := by
    change (post'.getCode weth9Address).toList ≠ []
    rw [hcodePost]
    intro hnil
    have hlen := Blanc.Lift.Weth9.code_toList_length
    rw [hnil] at hlen
    exact absurd hlen (by decide)
  have hdel : ∀ a ∈ post'.accountsToDelete.toList, a ≠ weth9Address := fun a ha => by
    have hmem := Std.HashSet.mem_toList.mp ha
    rw [hatd, hinherited] at hmem
    exact absurd hmem AdrSet.not_mem_empty
  obtain ⟨hc, hs⟩ := settled_getCode_getStor_of_code_nonempty (rules := benv.stat.rules)
    (touched := post'.meta.touchedAccounts.toList) (s := deployer) (c := benv.stat.coinbase)
    (r := Nat.toB256 ((tx.gas - txGasUsedQ benv.stat.rules.settle.refundQuotient tx.gas
      calldataFloorGas post'.gasLeft 0) * effectiveGasPrice))
    (f := Nat.toB256 (txGasUsedQ benv.stat.rules.settle.refundQuotient tx.gas calldataFloorGas
      post'.gasLeft 0 * (effectiveGasPrice - benv.stat.baseFeePerGas))) hdel hcodeNe
  exact ⟨(congrArg ByteArray.toList hc).trans hcodePost, hs.trans hstorPost⟩

end Blanc.Lift.Weth9.Creation
