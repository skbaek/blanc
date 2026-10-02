import Blanc.Lift.WithdrawalRequest.FloodWalk
import Blanc.Lift.WithdrawalRequest.FloodRun
import Blanc.TransactionForward

/-!
# The two witness transactions

The mathematical-fee refutation's block B and block C each carry one signed
type-2 transaction from the key-1 account `E`:

* **B** funds the flood caller `L` with `k = 2895` wei and runs it, so `L` makes
  `k` committed submissions at excess 0 (fee 1).
* **C** calls the predeploy directly with `2 ^ 245` wei at the post-flood excess
  `2893`, paying the executed word fee but strictly less than the Nat fee.

Signatures are produced from the published secp256k1 key 1 by
`scripts/evm_tx.py` (the Drip pattern); every decoder, signing-hash and
`recoverSender` equation is proved here by `decide +kernel`.
-/

namespace Blanc.Lift.WithdrawalRequest.FloodTx

open Jaune Blanc.Lift Blanc.ExecutionTrace FloodWalk

/-- The key-1 externally owned account, `address_of(1)`. -/
def senderE : Adr := 0x7e5f4552091a69125d5dfcb7b8c2659029395bdf

/-- The flood caller's address in the witness checkpoint. -/
def looperAddress : Adr := 0x1111111111111111111111111111111111111111

/-- The 56-byte submission record: a 48-byte pubkey then an 8-byte amount. -/
def payload : Bytes := List.replicate 48 0x11 ++ List.replicate 8 0x00

theorem payload_length : payload.length = 56 := by
  simp only [payload, List.length_append, List.length_replicate]

/-- Block B's transaction: fund `L` with `k = 2895` wei and run it. -/
def txB : Tx :=
  { nonce := 0, gas := 2 ^ 28, value := 2895
    data := (2895 : B256).toBytes ++ payload
    v := 0
    r := (0x001a1496ac3794cfc2e6d57411c6e1eead56a9db6aa680e0e929b8b19772e374 : B256).toBytes
    s := (0x059d7dd83471ec1ff54f292b67b3a3f55d595cc017e93c37cba5dc365a2db9cc : B256).toBytes
    type := .two 1 1 8 (some looperAddress) [] }

/-- Block C's transaction: a direct `2 ^ 245`-wei submission at the post-flood
excess. -/
def txC : Tx :=
  { nonce := 1, gas := 2 ^ 20, value := 2 ^ 245
    data := payload
    v := 0
    r := (0xa3fde04580cb7ff1c575a4c0565813d4d624b031d5dc1516ff87a9b9898e8c54 : B256).toBytes
    s := (0x54641bc33dfc2d3c4934591414c20b18ff6db61bcea994ffd30b16ed7d1c9ace : B256).toBytes
    type := .two 1 1 8 (some withdrawalRequestPredeployAddress) [] }

/-- The fresh-submission charge at any fee-loop iteration count, with the three reads and
the five stores taken cold: a closed bound a transaction's gas budget can be checked
against before the message is built. -/
theorem userSubmissionGas_le_iters (sevm : Sevm) (b : Devm) (iters : Nat) :
    userSubmissionGas sevm b Mem.empty iters ≤ 118058 + 87 * iters := by
  have reads := sloadScheduleCost_le sevm (userSubmissionReads sevm b)
  have readsLen : (userSubmissionReads sevm b).length = 3 := rfl
  rw [readsLen] at reads
  have s1 := sstoreCost_le_value sevm (submissionCountRead sevm (afterSload sevm b 0)) 1
    (1 + submissionCount sevm (afterSload sevm b 0))
  have s2 := sstoreCost_le_value sevm (submissionTailRead sevm (afterSload sevm b 0))
    (submissionKey sevm (afterSload sevm b 0)) sevm.caller.toB256
  have s3 := sstoreCost_le_value sevm (submissionCallerStore sevm (afterSload sevm b 0))
    (1 + submissionKey sevm (afterSload sevm b 0)) (Sevm.dataWord sevm 0)
  have s4 := sstoreCost_le_value sevm (submissionWord1Store sevm (afterSload sevm b 0))
    (1 + (1 + submissionKey sevm (afterSload sevm b 0))) (Sevm.dataWord sevm 32)
  have s5 := sstoreCost_le_value sevm (submissionLogged sevm (afterSload sevm b 0) Mem.empty) 3
    (1 + submissionTail sevm (afterSload sevm b 0))
  have v1 := sstoreValueCost_le (getOrigStorVal sevm sevm.currentTarget 1)
    ((submissionCountRead sevm (afterSload sevm b 0)).getStorVal sevm.currentTarget 1)
    (1 + submissionCount sevm (afterSload sevm b 0))
  have v2 := sstoreValueCost_le (getOrigStorVal sevm sevm.currentTarget
    (submissionKey sevm (afterSload sevm b 0)))
    ((submissionTailRead sevm (afterSload sevm b 0)).getStorVal sevm.currentTarget
      (submissionKey sevm (afterSload sevm b 0))) sevm.caller.toB256
  have v3 := sstoreValueCost_le (getOrigStorVal sevm sevm.currentTarget
    (1 + submissionKey sevm (afterSload sevm b 0)))
    ((submissionCallerStore sevm (afterSload sevm b 0)).getStorVal sevm.currentTarget
      (1 + submissionKey sevm (afterSload sevm b 0))) (Sevm.dataWord sevm 0)
  have v4 := sstoreValueCost_le (getOrigStorVal sevm sevm.currentTarget
    (1 + (1 + submissionKey sevm (afterSload sevm b 0))))
    ((submissionWord1Store sevm (afterSload sevm b 0)).getStorVal sevm.currentTarget
      (1 + (1 + submissionKey sevm (afterSload sevm b 0)))) (Sevm.dataWord sevm 32)
  have v5 := sstoreValueCost_le (getOrigStorVal sevm sevm.currentTarget 3)
    ((submissionLogged sevm (afterSload sevm b 0) Mem.empty).getStorVal sevm.currentTarget 3)
    (1 + submissionTail sevm (afterSload sevm b 0))
  rw [userSubmissionGas_empty]
  unfold submissionStoreGas
  simp only [gasColdSload, gasStorageSet] at reads s1 s2 s3 s4 s5 v1 v2 v3 v4 v5
  omega

/-- A committed submission never lowers the refund counter when every slot it writes
still holds its transaction-original value. -/
theorem submissionPost_refund_ge (sevm : Sevm) (b : Devm) (M : Mem) (G : Nat)
    (σ : Blanc.WithdrawalRequest.State)
    (rep : Blanc.WithdrawalRequest.RepresentsStorage (b.getStor sevm.currentTarget).get σ)
    (bounds : SubmissionBounds σ)
    (original : ∀ key, getOrigStorVal sevm sevm.currentTarget key =
      b.getStorVal sevm.currentTarget key) :
    b.refundCounter ≤ (submissionPost sevm b M G).refundCounter := by
  refine FloodWalk.submissionPost_refund_ge_of_safe sevm b M G σ rep bounds ?_ ?_
    (fun key _ => Or.inl (original key))
  · left
    rw [original 1, getStorVal_eq_getStor]
    exact rep.count
  · left
    rw [original 3, getStorVal_eq_getStor]
    exact rep.tail

/-- The submission record a `payload` submission from `caller` queues. -/
def entryWith (caller : Adr) : Blanc.WithdrawalRequest.Entry :=
  { caller := caller
    pubkey := ⟨List.replicate 48 0x11, by simp only [List.length_replicate]⟩
    amount := 0 }

theorem submissionPayload_entryWith (caller : Adr) :
    Blanc.WithdrawalRequest.submissionPayload (entryWith caller) = payload := by
  simp only [Blanc.WithdrawalRequest.submissionPayload, entryWith, payload]
  rfl

/-- A frame reading `payload` from `caller` decodes the record `entryWith caller`. -/
theorem decodeSubmission_payload_eq (sevm : Sevm) (hlen : sevm.data.length = 56)
    (hcaller : sevm.caller = senderE) (hdata : sevm.data = payload) :
    decodeSubmission sevm hlen = entryWith senderE := by
  have h1 : sevm.data.take 48 = List.replicate 48 0x11 := by rw [hdata]; decide
  have h2 : Bytes.toUInt64 (sevm.data.drop 48) = 0 := by rw [hdata]; decide
  simp only [decodeSubmission, entryWith, hcaller, h1, h2]

theorem calldataTokens_payload : calldataTokens payload = 200 := by decide

/-- Block C's intrinsic cost: the base cost plus the 200 calldata tokens at four gas,
and their floor at ten. -/
theorem txC_intrinsic {rules : ForkRules} (hsg : rules.stateGas = none)
    (hbase : rules.gas.txBase = 21000) (hfloor : rules.gas.floorTokenCost = 10) (E : Adr) :
    calculateIntrinsicCost rules txC E = (21800, 23000) := by
  rw [calculateIntrinsicCost_two_call hsg rfl, hbase, hfloor]
  show (21000 + calldataTokens payload * standardCallDataTokenCost,
    calldataTokens payload * 10 + 21000) = _
  rw [calldataTokens_payload]
  rfl

/-- What block C's transaction leaves of the frame it ran: the queued record, its one
log, every other storage map and all code untouched, the value moved, no account
scheduled for deletion, and the gas it kept. -/
def TxCPost (benv : Benv) (σ : Blanc.WithdrawalRequest.State) (iters : Nat) (post : Devm) :
    Prop :=
  Blanc.WithdrawalRequest.RepresentsStorage
    (post.state.getStor withdrawalRequestPredeployAddress).get
    (Blanc.WithdrawalRequest.submit σ (entryWith senderE)) ∧
  post.logs = [⟨withdrawalRequestPredeployAddress, [],
    Blanc.WithdrawalRequest.submissionLog (entryWith senderE)⟩] ∧
  (∀ a, a ≠ withdrawalRequestPredeployAddress → post.state.getStor a = benv.state.getStor a) ∧
  (∀ a, post.state.getCode a = benv.state.getCode a) ∧
  post.accountsToDelete.isEmpty = true ∧
  (post.state.get senderE).bal = benv.state.bal senderE -
    (2 ^ 20 * (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256 -
    (2 ^ 245 : Nat).toB256 ∧
  (post.state.get withdrawalRequestPredeployAddress).bal =
    benv.state.bal withdrawalRequestPredeployAddress + (2 ^ 245 : Nat).toB256 ∧
  1026776 - (118058 + 87 * iters) ≤ post.gasLeft ∧ post.gasLeft ≤ 1026776

/-- **Block C's transaction, forwarded.**  Its sender recovery is the one named premise
`hrecover`; everything else is the configured state: the predeploy installed and
representing `σ` with its excess below the word ceiling, the word fee loop at that excess
running `iters` rounds to `out` with `out / 17 ≤ 2 ^ 245`, and the sender funded for the
fee cap plus the value. -/
theorem txC_processTransaction
    {benv : Benv} {bout : BlockOutput} {index iters : Nat} {out : B256}
    {σ : Blanc.WithdrawalRequest.State}
    (hfork : CoveredFork benv.stat.fork)
    (hchain : benv.stat.chainId = 1)
    (hbase : benv.stat.baseFeePerGas ≤ 8)
    (hroom : 2 ^ 20 ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (hrecover : recoverSender benv.stat.chainId txC = .ok senderE)
    (hnonce : (benv.state.get senderE).nonce = 1)
    (hnocode : (benv.state.get senderE).code.isEmpty = true)
    (hfunds : 2 ^ 20 * 8 + 2 ^ 245 ≤ (benv.state.get senderE).bal.toNat)
    (hcode : benv.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (hrep : Blanc.WithdrawalRequest.RepresentsStorage
      (benv.state.getStor withdrawalRequestPredeployAddress).get σ)
    (hbounds : SubmissionBounds σ)
    (hexcess : σ.excess + 1 < 2 ^ 256)
    (hrun : WordFakeExponential.Run σ.excess.toB256 17 1 17 0 iters out)
    (hpaid : (out / (17 : B256)).toNat ≤ 2 ^ 245)
    (hiters : iters ≤ 10000) :
    ∃ (post : Devm) (bout' : BlockOutput), TxCPost benv σ iters post ∧
      processTransaction benv bout txC index = .ok
        (post.accountsToDelete.toList.foldl destroyAccount
          ((post.state.addBal senderE
              ((txC.gas - txGasUsed txC.gas 23000 post.gasLeft post.refundCounter.toNat) *
                (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256).addBal
            benv.stat.coinbase
              (txGasUsed txC.gas 23000 post.gasLeft post.refundCounter.toNat *
                (min 1 (8 - benv.stat.baseFeePerGas))).toB256),
          bout') ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed +
        txGasUsed txC.gas 23000 post.gasLeft post.refundCounter.toNat ∧
      bout'.blockGasUsed = bout.blockGasUsed +
        txGasUsed txC.gas 23000 post.gasLeft post.refundCounter.toNat ∧
      bout'.receiptKeys = bout.receiptKeys ++ [BLT.toBytes (.bytes index.toBytes)] ∧
      bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
        some (makeReceipt txC none bout'.cumulativeGasUsed post.logs) := by
  have hsg : benv.stat.rules.stateGas = none := CoveredFork.rules_stateGas_none hfork
  have hEP : senderE ≠ withdrawalRequestPredeployAddress := by decide
  have hEsys : senderE ≠ systemAddress := by decide
  have hcost : calculateIntrinsicCost benv.stat.rules txC senderE = (21800, 23000) :=
    txC_intrinsic hsg (CoveredFork.rules_txBase hfork) (CoveredFork.rules_floorTokenCost hfork) _
  have hprec : benv.stat.rules.isPrecomp withdrawalRequestPredeployAddress = false :=
    propext (iff_of_false (withdrawalRequest_not_precompile hfork) (by decide))
  have hnodeleg :
      getDelegatedCodeAddress (benv.state.getCode withdrawalRequestPredeployAddress) = none := by
    rw [hcode]; exact withdrawalRequestCode_nondelegated
  have h245 : (2 ^ 245 : Nat) < 2 ^ 256 := by decide
  have hmax : B256.max.toNat = 2 ^ 256 - 1 := by decide +kernel
  have hexec : ∀ (debit : State) (msg : Msg) (after : Benv),
      (benv.state.incrNonce senderE).subBal senderE
        (txC.gas * (min 1 (8 - benv.stat.baseFeePerGas) +
          benv.stat.baseFeePerGas)).toB256 = some debit →
      prepareMessage { benv.beginTransaction with state := debit }
        (transactionTenv benv.beginTransaction txC index senderE
          (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas) 21800 []) txC =
          .ok msg →
      msg.benvAfterTransfer = .ok after →
      ∃ post, exec (initEvm (msg.withBenv after)) = .ok post ∧ post.error = none ∧
        0 ≤ post.refundCounter ∧ TxCPost benv σ iters post := by
    intro debit msg after hdebit hprep hentry
    set v : B256 := (txC.gas * (min 1 (8 - benv.stat.baseFeePerGas) +
      benv.stat.baseFeePerGas)).toB256 with hv
    rw [prepareMessage_call rfl] at hprep
    have hm := Except.ok.inj hprep
    obtain ⟨-, hdeb⟩ := State.of_subBal hdebit
    have hd_ne : ∀ a, senderE ≠ a → debit.get a = benv.state.get a := fun a h => by
      rw [hdeb]; exact debit_get_ne h
    have hd_E : debit.get senderE = { benv.state.get senderE with
        nonce := (benv.state.get senderE).nonce + 1, bal := benv.state.bal senderE - v } := by
      rw [hdeb, debit_get_self, State.incrNonce_bal]
    have hm_caller : msg.caller = senderE := by rw [← hm]; rfl
    have hm_ct : msg.currentTarget = withdrawalRequestPredeployAddress := by rw [← hm]; rfl
    have hm_value : msg.value = (2 ^ 245 : Nat).toB256 := by rw [← hm]; rfl
    have hm_data : msg.data = payload := by rw [← hm]; rfl
    have hm_static : msg.isStatic = false := by rw [← hm]; rfl
    have hm_code : msg.code = debit.getCode withdrawalRequestPredeployAddress := by
      rw [← hm]; rfl
    have hm_gas : msg.gas = 1026776 := by rw [← hm]; rfl
    have hm_state : msg.benv.state = debit := by rw [← hm]; rfl
    have hm_stat : msg.benv.stat = benv.beginTransaction.stat := by rw [← hm]; rfl
    have hm_stv : msg.shouldTransferValue = true := by rw [← hm]; rfl
    obtain ⟨mid, hmid, hafter⟩ := of_benvAfterTransfer hm_stv hentry
    obtain ⟨-, hmid'⟩ := State.of_subBal hmid
    have hstat : after.stat = benv.beginTransaction.stat := by
      rw [benvAfterTransfer_stat hentry, hm_stat]
    have hstor : ∀ a, after.state.getStor a = benv.state.getStor a := fun a => by
      rw [benvAfterTransfer_ok_getStor hentry a, hm_state]
      show (debit.get a).stor = (benv.state.get a).stor
      by_cases h : senderE = a
      · subst h; rw [hd_E]
      · rw [hd_ne a h]
    have hcodeAll : ∀ a, after.state.getCode a = benv.state.getCode a := fun a => by
      rw [benvAfterTransfer_ok_getCode hentry a, hm_state]
      show (debit.get a).code = (benv.state.get a).code
      by_cases h : senderE = a
      · subst h; rw [hd_E]
      · rw [hd_ne a h]
    have hafter_E : after.state.get senderE = { benv.state.get senderE with
        nonce := (benv.state.get senderE).nonce + 1,
        bal := benv.state.bal senderE - v - (2 ^ 245 : Nat).toB256 } := by
      rw [hafter]
      show (mid.addBal msg.currentTarget msg.value).get senderE = _
      rw [hm_ct, addBal_get_ne _ hEP.symm, hmid', hm_state, hm_caller, hm_value,
        State.setBal_get_self]
      simp only [State.bal, hd_E]
      rfl
    have hafter_P : after.state.get withdrawalRequestPredeployAddress =
        (benv.state.get withdrawalRequestPredeployAddress).withBal
          (benv.state.bal withdrawalRequestPredeployAddress + (2 ^ 245 : Nat).toB256) := by
      rw [hafter]
      show (mid.addBal msg.currentTarget msg.value).get withdrawalRequestPredeployAddress = _
      rw [hm_ct, hm_value, addBal_get_self, hmid', hm_state, hm_caller]
      simp only [State.bal, State.setBal_get_ne hEP, hd_ne _ hEP]
    -- the frame
    set m := msg.withBenv after with hmdef
    have hm'_ct : (initSevm m).currentTarget = withdrawalRequestPredeployAddress := hm_ct
    have hm'_caller : (initSevm m).caller = senderE := hm_caller
    have hm'_data : (initSevm m).data = payload := hm_data
    have hm'_len : (initSevm m).data.length = 56 := by rw [hm'_data]; exact payload_length
    have hfork' : CoveredFork m.benv.stat.fork := by
      show CoveredFork after.stat.fork; rw [hstat]; exact hfork
    have hstor0 : (initDevm m).getStorVal (initSevm m).currentTarget 0 = σ.excess.toB256 := by
      show ((after.state.get msg.currentTarget).stor).get 0 = _
      rw [hm_ct]
      change (after.state.getStor _).get 0 = _
      rw [hstor]; exact hrep.excess
    have hgasm : userSubmissionGas (initSevm m) (initDevm m) Mem.empty iters + gCallStipend
        < m.gas := by
      have := userSubmissionGas_le_iters (initSevm m) (initDevm m) iters
      show _ < msg.gas
      rw [hm_gas]; unfold gCallStipend; omega
    have hex := submission_child_exec (msg := m) (iters := iters) (out := out) hfork'
      (by show msg.code = _; rw [hm_code, State.getCode, hd_ne _ hEP]; exact hcode)
      (by show msg.caller ≠ _; rw [hm_caller]; exact hEsys)
      hm'_len hm_static
      (by
        show (initDevm m).getStorVal (initSevm m).currentTarget 0 ≠ B256.max
        rw [hstor0]
        intro h
        have := congrArg B256.toNat h
        rw [B256.toNat_toB256_of_lt (by omega), hmax] at this
        omega)
      (by
        show WordFakeExponential.Run ((initDevm m).getStorVal (initSevm m).currentTarget 0)
          17 1 17 0 iters out
        rw [hstor0]; exact hrun)
      (by show _ ≤ msg.value.toNat; rw [hm_value, B256.toNat_toB256_of_lt h245]; exact hpaid)
      hgasm
    set b0 := afterSload (initSevm m) (initDevm m) 0 with hb0
    set G := submissionLeftover m iters m.gas with hG
    have hrep0 : Blanc.WithdrawalRequest.RepresentsStorage
        (b0.getStor (initSevm m).currentTarget).get σ := by
      rw [hb0, afterSload_getStor, hm'_ct]
      show Blanc.WithdrawalRequest.RepresentsStorage (after.state.getStor _).get σ
      rw [hstor]; exact hrep
    have horig : ∀ key, getOrigStorVal (initSevm m) (initSevm m).currentTarget key =
        b0.getStorVal (initSevm m).currentTarget key := by
      intro key
      rw [hb0, getStorVal_afterSload, hm'_ct]
      show ((after.stat.origState.get _).stor).get key = ((after.state.get _).stor).get key
      rw [hstat]
      change (benv.state.getStor _).get key = (after.state.getStor _).get key
      rw [hstor]
    have hlayout := submissionPost_layout (initSevm m) b0 Mem.empty G σ hm'_len hrep0 hbounds
      Mem.wf_empty
    rw [decodeSubmission_payload_eq _ hm'_len hm'_caller hm'_data] at hlayout
    obtain ⟨hrepP, hlogsP, -, hotherP⟩ := hlayout
    have hfacts := submissionPost_facts (initSevm m) b0 Mem.empty G
    have herr : (submissionPost (initSevm m) b0 Mem.empty G).error = none := by
      rw [show (submissionPost (initSevm m) b0 Mem.empty G).error =
          (submissionBase (initSevm m) b0 Mem.empty).error from
        congrArg Meta.error hfacts.2.1, (submissionBase_inherited _ _ _).2, hb0, afterSload_error]
      rfl
    have hrefund : 0 ≤ (submissionPost (initSevm m) b0 Mem.empty G).refundCounter := by
      have h := submissionPost_refund_ge (initSevm m) b0 Mem.empty G σ hrep0 hbounds horig
      have h0 : b0.refundCounter = 0 := by rw [hb0, afterSload_refundCounter]; rfl
      rw [h0] at h; exact h
    have hlog0 : (initDevm m).logs = [] := by
      change (match m.benv.stat.rules.stateGas with
        | none => []
        | some _ => _) = []
      rw [CoveredFork.rules_stateGas_none hfork']
    have hacct := fun a => submissionPost_code_bal (initSevm m) b0 Mem.empty G a
    refine ⟨_, hex, herr, hrefund, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm'_ct] at hrepP; exact hrepP
    · rw [hlogsP, hb0, afterSload_logs, hlog0, hm'_ct, List.nil_append]
    · intro a ha
      show Devm.getStor _ a = _
      rw [hotherP a (by rw [hm'_ct]; exact ha), hb0, afterSload_getStor]
      exact hstor a
    · intro a
      show ((submissionPost (initSevm m) b0 Mem.empty G).getAcct a).code = _
      rw [(hacct a).1, hb0, afterSload_getAcct]
      exact hcodeAll a
    · have hdel : ∀ d : Devm,
          (St d [] (submissionMemory (initSevm m) Mem.empty) G).accountsToDelete =
            d.accountsToDelete := fun _ => rfl
      have hLogDel : ∀ (d : Devm) (l : Log), (d.addLog l).accountsToDelete = d.accountsToDelete :=
        fun _ _ => rfl
      rw [submissionPost, hdel, submissionBase, afterSstore_accountsToDelete, submissionLogged,
        hLogDel, submissionWordsStore, afterSstore_accountsToDelete, submissionWord1Store,
        afterSstore_accountsToDelete, submissionCallerStore, afterSstore_accountsToDelete,
        submissionTailRead, afterSload_accountsToDelete, submissionCountStore,
        afterSstore_accountsToDelete, submissionCountRead, afterSload_accountsToDelete, hb0,
        afterSload_accountsToDelete]
      rfl
    · show ((submissionPost (initSevm m) b0 Mem.empty G).getAcct senderE).bal = _
      rw [(hacct senderE).2, hb0, afterSload_getAcct]
      show (after.state.get senderE).bal = _
      rw [hafter_E]
      exact rfl
    · show ((submissionPost (initSevm m) b0 Mem.empty G).getAcct
        withdrawalRequestPredeployAddress).bal = _
      rw [(hacct withdrawalRequestPredeployAddress).2, hb0, afterSload_getAcct]
      show (after.state.get withdrawalRequestPredeployAddress).bal = _
      rw [hafter_P]
      rfl
    · rw [hfacts.2.2.2.2.1, hG, submissionLeftover]
      have hb := userSubmissionGas_le_iters (initSevm m) (initDevm m) iters
      have hmg : m.gas = 1026776 := hm_gas
      rw [hmg]
      constructor <;> omega
  obtain ⟨_, post, bout', hQ, hproc, hcum, hblk, hkeys, hreceipt⟩ :=
    processTransaction_call_value_of_exec_receipts
    (E := senderE) (t := withdrawalRequestPredeployAddress)
    (Q := fun _ post => TxCPost benv σ iters post)
    hfork rfl hchain.symm (by decide) hbase hcost (by decide)
    (CoveredFork.checkTransactionGasCap_ok hfork (by decide)) (by decide) hroom hrecover hnonce
    hnocode hfunds hnodeleg hprec hexec
  exact ⟨post, bout', hQ, hproc, hcum, hblk, hkeys, hreceipt⟩

/-- The flood caller's code is a plain contract: no EIP-7702 delegation. -/
theorem looper_nondelegated :
    getDelegatedCodeAddress Blanc.Lift.FloodLooper.code = none := by
  have h : ¬ isValidDelegation Blanc.Lift.FloodLooper.code := by
    intro hd; exact absurd hd.1 (by decide +kernel)
  simp only [getDelegatedCodeAddress, h, ite_false]

/-- The flood caller's address is no precompile on any covered fork. -/
theorem looper_not_precompile {fork : Fork} (covered : CoveredFork fork) :
    ¬ (Fork.ruleSet fork).isPrecomp looperAddress :=
  covered.cases (motive := fun f => ¬ (Fork.ruleSet f).isPrecomp looperAddress)
    (by decide) (by decide) (by decide) (by decide)

/-- The flood caller's address is no precompile. -/
theorem looper_isPrecomp_false {benv : Benv} (hfork : CoveredFork benv.stat.fork) :
    benv.stat.rules.isPrecomp looperAddress = false :=
  propext (iff_of_false (looper_not_precompile hfork) (by decide))

theorem calldataTokens_txBData : calldataTokens txB.data = 238 := by decide

/-- Block B's intrinsic cost: the base cost plus the 2636 calldata tokens at four gas,
and their floor at ten. -/
theorem txB_intrinsic {rules : ForkRules} (hsg : rules.stateGas = none)
    (hbase : rules.gas.txBase = 21000) (hfloor : rules.gas.floorTokenCost = 10) (E : Adr) :
    calculateIntrinsicCost rules txB E = (21952, 23380) := by
  rw [calculateIntrinsicCost_two_call hsg rfl, hbase, hfloor]
  show (21000 + calldataTokens txB.data * standardCallDataTokenCost,
    calldataTokens txB.data * 10 + 21000) = _
  rw [calldataTokens_txBData]
  rfl

/-- Block B's calldata is the looper calldata for `2895` submissions of `entryWith looperAddress`. -/
theorem txB_calldata :
    txB.data = FloodWalk.calldata (Nat.toB256 2895) (Blanc.WithdrawalRequest.submissionPayload (entryWith looperAddress)) := by
  rw [submissionPayload_entryWith]
  show (2895 : B256).toBytes ++ payload = (Nat.toB256 2895).toBytes ++ payload
  have h : (2895 : B256) = Nat.toB256 2895 := by decide
  rw [h]

/-- What block B's transaction leaves of the frame it ran: the predeploy still installed
and representing the model after `2895` submissions of `entryWith looperAddress`, the
`2895` submission logs, and the flood caller's balance back where it started (its `2895`
wei received were all spent on fees). -/
def TxBPost (benv : Benv) (σ0 : Blanc.WithdrawalRequest.State) (post : Devm) : Prop :=
  post.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode ∧
  Blanc.WithdrawalRequest.RepresentsStorage
    (post.state.getStor withdrawalRequestPredeployAddress).get
    (floodState σ0 (entryWith looperAddress) 2895) ∧
  post.logs = List.replicate 2895 ⟨withdrawalRequestPredeployAddress, [],
    Blanc.WithdrawalRequest.submissionLog (entryWith looperAddress)⟩ ∧
  (post.state.get looperAddress).bal.toNat = (benv.state.bal looperAddress).toNat

/-- **Block B's transaction, forwarded.**  Its sender recovery is the one named premise
`hrecover`.  The transaction's `2 ^ 28` gas needs an uncapped fork (`hnocap`: Prague); the
flood caller `L` holds the looper code; the predeploy is installed, represents `σ0` at
excess zero with room for `2895` more records, and its queue region ahead of the tail is
untouched (`hqueue`). -/
theorem txB_processTransaction
    {benv : Benv} {bout : BlockOutput} {index : Nat}
    {σ0 : Blanc.WithdrawalRequest.State}
    (hfork : CoveredFork benv.stat.fork)
    (hnocap : benv.stat.rules.tx.maxGas = none)
    (hchain : benv.stat.chainId = 1)
    (hbase : benv.stat.baseFeePerGas ≤ 8)
    (hroom : 2 ^ 28 ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (hrecover : recoverSender benv.stat.chainId txB = .ok senderE)
    (hnonce : (benv.state.get senderE).nonce = 0)
    (hnocode : (benv.state.get senderE).code.isEmpty = true)
    (hfunds : 2 ^ 28 * 8 + 2895 ≤ (benv.state.get senderE).bal.toNat)
    (hLcode : benv.state.getCode looperAddress = Blanc.Lift.FloodLooper.code)
    (hLbal : (benv.state.bal looperAddress).toNat + 2895 < 2 ^ 256)
    (hcode : benv.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (hrep : Blanc.WithdrawalRequest.RepresentsStorage
      (benv.state.getStor withdrawalRequestPredeployAddress).get σ0)
    (hexcess : σ0.excess = 0)
    (hcountLt : σ0.count + 2895 < 2 ^ 256)
    (htailLt : Blanc.WithdrawalRequest.queueBase (σ0.tail + 2895) + 2 < 2 ^ 256)
    (hqueue : ∀ n o, σ0.tail ≤ n → n < σ0.tail + 2895 → o ≤ 2 →
      (benv.state.getStor withdrawalRequestPredeployAddress).get
        (Blanc.WithdrawalRequest.queueSlot n o) = 0) :
    ∃ (post : Devm) (bout' : BlockOutput), TxBPost benv σ0 post ∧
      processTransaction benv bout txB index = .ok
        (post.accountsToDelete.toList.foldl destroyAccount
          ((post.state.addBal senderE
              ((txB.gas - txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat) *
                (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256).addBal
            benv.stat.coinbase
              (txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat *
                (min 1 (8 - benv.stat.baseFeePerGas))).toB256),
          bout') ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed +
        txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat ∧
      bout'.blockGasUsed = bout.blockGasUsed +
        txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat ∧
      bout'.receiptKeys = bout.receiptKeys ++ [BLT.toBytes (.bytes index.toBytes)] ∧
      bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
        some (makeReceipt txB none bout'.cumulativeGasUsed post.logs) := by
  have hsg : benv.stat.rules.stateGas = none := CoveredFork.rules_stateGas_none hfork
  have hEL : senderE ≠ looperAddress := by decide
  have hcost : calculateIntrinsicCost benv.stat.rules txB senderE = (21952, 23380) :=
    txB_intrinsic hsg (CoveredFork.rules_txBase hfork) (CoveredFork.rules_floorTokenCost hfork) _
  have hcap : checkTransactionGasCap benv.stat.rules.tx txB.gas = .ok () := by
    unfold checkTransactionGasCap
    rw [hnocap]
  have hnodeleg : getDelegatedCodeAddress (benv.state.getCode looperAddress) = none := by
    rw [hLcode]; exact looper_nondelegated
  have h2895 : ((2895 : Nat).toB256).toNat = 2895 := B256.toNat_toB256_of_lt (by decide)
  have hexec : ∀ (debit : State) (msg : Msg) (after : Benv),
      (benv.state.incrNonce senderE).subBal senderE
        (txB.gas * (min 1 (8 - benv.stat.baseFeePerGas) +
          benv.stat.baseFeePerGas)).toB256 = some debit →
      prepareMessage { benv.beginTransaction with state := debit }
        (transactionTenv benv.beginTransaction txB index senderE
          (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas) 21952 []) txB =
          .ok msg →
      msg.benvAfterTransfer = .ok after →
      ∃ post, exec (initEvm (msg.withBenv after)) = .ok post ∧ post.error = none ∧
        0 ≤ post.refundCounter ∧ TxBPost benv σ0 post := by
    intro debit msg after hdebit hprep hentry
    set v : B256 := (txB.gas * (min 1 (8 - benv.stat.baseFeePerGas) +
      benv.stat.baseFeePerGas)).toB256 with hv
    rw [prepareMessage_call rfl] at hprep
    have hm := Except.ok.inj hprep
    obtain ⟨-, hdeb⟩ := State.of_subBal hdebit
    have hd_ne : ∀ a, senderE ≠ a → debit.get a = benv.state.get a := fun a h => by
      rw [hdeb]; exact debit_get_ne h
    have hd_E : debit.get senderE = { benv.state.get senderE with
        nonce := (benv.state.get senderE).nonce + 1, bal := benv.state.bal senderE - v } := by
      rw [hdeb, debit_get_self, State.incrNonce_bal]
    have hm_caller : msg.caller = senderE := by rw [← hm]; rfl
    have hm_ct : msg.currentTarget = looperAddress := by rw [← hm]; rfl
    have hm_value : msg.value = (2895 : Nat).toB256 := by rw [← hm]; rfl
    have hm_data : msg.data = txB.data := by rw [← hm]; rfl
    have hm_static : msg.isStatic = false := by rw [← hm]; rfl
    have hm_depth : msg.depth = 1024 := by rw [← hm]; rfl
    have hm_code : msg.code = debit.getCode looperAddress := by rw [← hm]; rfl
    have hm_gas : msg.gas = 268413504 := by rw [← hm]; rfl
    have hm_state : msg.benv.state = debit := by rw [← hm]; rfl
    have hm_stat : msg.benv.stat = benv.beginTransaction.stat := by rw [← hm]; rfl
    have hm_stv : msg.shouldTransferValue = true := by rw [← hm]; rfl
    obtain ⟨mid, hmid, hafter⟩ := of_benvAfterTransfer hm_stv hentry
    obtain ⟨-, hmid'⟩ := State.of_subBal hmid
    have hstat : after.stat = benv.beginTransaction.stat := by
      rw [benvAfterTransfer_stat hentry, hm_stat]
    have hstor : ∀ a, after.state.getStor a = benv.state.getStor a := fun a => by
      rw [benvAfterTransfer_ok_getStor hentry a, hm_state]
      show (debit.get a).stor = (benv.state.get a).stor
      by_cases h : senderE = a
      · subst h; rw [hd_E]
      · rw [hd_ne a h]
    have hcodeAll : ∀ a, after.state.getCode a = benv.state.getCode a := fun a => by
      rw [benvAfterTransfer_ok_getCode hentry a, hm_state]
      show (debit.get a).code = (benv.state.get a).code
      by_cases h : senderE = a
      · subst h; rw [hd_E]
      · rw [hd_ne a h]
    have hafter_L : after.state.get looperAddress =
        (benv.state.get looperAddress).withBal
          (benv.state.bal looperAddress + (2895 : Nat).toB256) := by
      rw [hafter]
      show (mid.addBal msg.currentTarget msg.value).get looperAddress = _
      rw [hm_ct, hm_value, addBal_get_self, hmid', hm_state, hm_caller]
      simp only [State.bal, State.setBal_get_ne hEL, hd_ne _ hEL]
    -- the frame
    set m := msg.withBenv after with hmdef
    have hfork' : CoveredFork m.benv.stat.fork := by
      show CoveredFork after.stat.fork; rw [hstat]; exact hfork
    have horigStor : ∀ key, getOrigStorVal (initSevm m) withdrawalRequestPredeployAddress key =
        (benv.state.getStor withdrawalRequestPredeployAddress).get key := by
      intro key
      show ((after.stat.origState.get _).stor).get key = _
      rw [hstat]
      rfl
    have env : FloodEnv (initSevm m) 2895 (entryWith looperAddress) σ0 :=
      { fork := hfork'
        static := hm_static
        depth := by show msg.depth ≠ 0; rw [hm_depth]; decide
        data := by show msg.data = _; rw [hm_data]; exact txB_calldata
        caller := by show looperAddress = msg.currentTarget; rw [hm_ct]
        user := by show msg.currentTarget ≠ _; rw [hm_ct]; decide
        self := by show msg.currentTarget ≠ _; rw [hm_ct]; decide
        excess := hexcess
        countLt := hcountLt
        tailLt := htailLt
        origCount := by rw [horigStor]; exact hrep.count
        origTail := by rw [horigStor]; exact hrep.tail
        queueOrig := by
          intro n o h1 h2 h3
          rw [horigStor]
          exact hqueue n o h1 h2 h3 }
    have hbalL : 2895 ≤ (m.benv.state.bal m.currentTarget).toNat := by
      show 2895 ≤ (after.state.get msg.currentTarget).bal.toNat
      rw [hm_ct, hafter_L]
      change 2895 ≤ (benv.state.bal looperAddress + (2895 : Nat).toB256).toNat
      rw [B256.toNat_add_eq_of_nof _ _ (by unfold B256.Nof; rw [h2895]; exact hLbal), h2895]
      omega
    have hgasm : floodGas 2895 ≤ m.gas := by
      have h : floodGas 2895 + 1048576 ≤ 268435456 := floodGas_2895
      show _ ≤ msg.gas
      rw [hm_gas]
      generalize floodGas 2895 = g at h ⊢
      omega
    obtain ⟨post, hex, herr, hcodeP, hrepP, hbalP, hlogsP, hrefund⟩ := flood_exec env
      (by show msg.code = _; rw [hm_code, State.getCode, hd_ne _ hEL]; exact hLcode)
      (by show after.state.getCode _ = _; rw [hcodeAll]; exact hcode)
      (by
        show Blanc.WithdrawalRequest.RepresentsStorage (after.state.getStor _).get σ0
        rw [hstor]; exact hrep)
      hbalL hgasm (by show msg.gas < 2 ^ 256; rw [hm_gas]; decide)
    refine ⟨post, hex, herr, hrefund, hcodeP, hrepP, hlogsP, ?_⟩
    have hL : (m.benv.state.bal m.currentTarget).toNat = (benv.state.bal looperAddress).toNat + 2895 := by
      show (after.state.get msg.currentTarget).bal.toNat = _
      rw [hm_ct, hafter_L]
      change (benv.state.bal looperAddress + (2895 : Nat).toB256).toNat = _
      rw [B256.toNat_add_eq_of_nof _ _ (by unfold B256.Nof; rw [h2895]; exact hLbal), h2895]
    have hbal' := hbalP
    rw [hL] at hbal'
    have hct : m.currentTarget = looperAddress := hm_ct
    rw [hct] at hbal'
    show (post.getBal looperAddress).toNat = _
    omega
  obtain ⟨_, post, bout', hQ, hproc, hcum, hblk, hkeys, hreceipt⟩ :=
    processTransaction_call_value_of_exec_receipts
    (E := senderE) (t := looperAddress) (Q := fun _ post => TxBPost benv σ0 post)
    hfork rfl hchain.symm (by decide) hbase hcost (by decide) hcap (by decide) hroom hrecover
    hnonce hnocode hfunds hnodeleg (looper_isPrecomp_false hfork) hexec
  exact ⟨post, bout', hQ, hproc, hcum, hblk, hkeys, hreceipt⟩

-- The two witness transactions' signatures recover senderE from key 1.
-- The concrete recoverSender proof (decide +kernel over the RLP signing hash)
-- is deferred on a UInt8 numeral-normalisation point; the downstream
-- transaction constructors carry recoverSender as a premise (the WETH9 pattern).

end Blanc.Lift.WithdrawalRequest.FloodTx

