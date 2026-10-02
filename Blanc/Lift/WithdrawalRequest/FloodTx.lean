import Blanc.Lift.WithdrawalRequest.FloodWalk
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

/-- The queue slots a submission writes are pairwise distinct and avoid the metadata
slots, in the word arithmetic, under the submission bounds. -/
private theorem submissionKey_distinct (sevm : Sevm) (b : Devm)
    (σ : Blanc.WithdrawalRequest.State)
    (rep : Blanc.WithdrawalRequest.RepresentsStorage (b.getStor sevm.currentTarget).get σ)
    (bounds : SubmissionBounds σ) :
    submissionKey sevm b ≠ 1 ∧ 1 + submissionKey sevm b ≠ 1 ∧
    1 + (1 + submissionKey sevm b) ≠ 1 ∧
    1 + submissionKey sevm b ≠ submissionKey sevm b ∧
    1 + (1 + submissionKey sevm b) ≠ submissionKey sevm b ∧
    1 + (1 + submissionKey sevm b) ≠ 1 + submissionKey sevm b := by
  have tail := submissionTail_eq sevm b σ rep
  have key := submissionKey_queueSlot sevm b σ.tail tail
  have offsets := submissionKey_offsets sevm b σ.tail tail
  have inWord : ∀ off, off ≤ 2 → Blanc.WithdrawalRequest.queueBase σ.tail + off < 2 ^ 256 :=
    fun off hoff => Nat.lt_of_le_of_lt (Nat.add_le_add_left hoff _) bounds.tail_slot_lt
  have metaNe : ∀ off, off ≤ 2 →
      Blanc.WithdrawalRequest.queueSlot σ.tail off ≠ (1 : B256) := fun off hoff =>
    submission_queueSlot_ne_metadata σ.tail off 1 (inWord off hoff) (by decide)
  have slots : ∀ a c, a ≤ 2 → c ≤ 2 → a ≠ c →
      Blanc.WithdrawalRequest.queueSlot σ.tail a ≠ Blanc.WithdrawalRequest.queueSlot σ.tail c := by
    intro a c ha hc hac eq
    have values := congrArg B256.toNat eq
    rw [submission_queueSlot_toNat σ.tail a (inWord a ha),
      submission_queueSlot_toNat σ.tail c (inWord c hc)] at values
    exact hac (Nat.add_left_cancel values)
  rw [offsets.2, offsets.1, key]
  exact ⟨metaNe 0 (by decide), metaNe 1 (by decide), metaNe 2 (by decide),
    slots 1 0 (by decide) (by decide) (by decide), slots 2 0 (by decide) (by decide) (by decide),
    slots 2 1 (by decide) (by decide) (by decide)⟩

/-- A committed submission never lowers the refund counter when every slot it writes
still holds its transaction-original value: each of its five stores hits a slot the
earlier stores left alone. -/
theorem submissionPost_refund_ge (sevm : Sevm) (b : Devm) (M : Mem) (G : Nat)
    (σ : Blanc.WithdrawalRequest.State)
    (rep : Blanc.WithdrawalRequest.RepresentsStorage (b.getStor sevm.currentTarget).get σ)
    (bounds : SubmissionBounds σ)
    (original : ∀ key, getOrigStorVal sevm sevm.currentTarget key =
      b.getStorVal sevm.currentTarget key) :
    b.refundCounter ≤ (submissionPost sevm b M G).refundCounter := by
  obtain ⟨k1, k1', k1'', kk, kk2, kk3⟩ := submissionKey_distinct sevm b σ rep bounds
  -- the value of an untouched slot after a store at another key
  have keep : ∀ (d : Devm) (w x v : B256), w ≠ v →
      (afterSstore sevm d w x).getStorVal sevm.currentTarget v =
        d.getStorVal sevm.currentTarget v := by
    intro d w x v hne
    rw [getStorVal_eq_getStor, afterSstore_getStor_self, Stor.get_set_ne _ hne,
      ← getStorVal_eq_getStor]
  have hLog : ∀ (d : Devm) (l : Log), (d.addLog l).refundCounter = d.refundCounter :=
    fun _ _ => rfl
  have hSt : ∀ d : Devm, (St d [] (submissionMemory sevm M) G).refundCounter = d.refundCounter :=
    fun _ => rfl
  -- stage 1: the count store at slot 1
  have o1 : getOrigStorVal sevm sevm.currentTarget 1 =
      (submissionCountRead sevm b).getStorVal sevm.currentTarget 1 := by
    rw [submissionCountRead, getStorVal_afterSload]; exact original 1
  have r1 : (submissionCountRead sevm b).refundCounter ≤
      (submissionCountStore sevm b).refundCounter :=
    afterSstore_refundCounter_ge_of_original_eq_current sevm (submissionCountRead sevm b)
      1 (1 + submissionCount sevm b) o1
  -- stage 2: the caller word at `key`
  have o2 : getOrigStorVal sevm sevm.currentTarget (submissionKey sevm b) =
      (submissionTailRead sevm b).getStorVal sevm.currentTarget (submissionKey sevm b) := by
    rw [submissionTailRead, getStorVal_afterSload, submissionCountStore, keep _ _ _ _ k1.symm,
      submissionCountRead, getStorVal_afterSload]
    exact original _
  have r2 : (submissionTailRead sevm b).refundCounter ≤
      (submissionCallerStore sevm b).refundCounter :=
    afterSstore_refundCounter_ge_of_original_eq_current sevm (submissionTailRead sevm b)
      (submissionKey sevm b) sevm.caller.toB256 o2
  -- stage 3: the first payload word at `key + 1`
  have o3 : getOrigStorVal sevm sevm.currentTarget (1 + submissionKey sevm b) =
      (submissionCallerStore sevm b).getStorVal sevm.currentTarget (1 + submissionKey sevm b) := by
    rw [submissionCallerStore, keep _ _ _ _ kk.symm, submissionTailRead, getStorVal_afterSload,
      submissionCountStore, keep _ _ _ _ k1'.symm, submissionCountRead, getStorVal_afterSload]
    exact original _
  have r3 : (submissionCallerStore sevm b).refundCounter ≤
      (submissionWord1Store sevm b).refundCounter :=
    afterSstore_refundCounter_ge_of_original_eq_current sevm (submissionCallerStore sevm b)
      (1 + submissionKey sevm b) (Sevm.dataWord sevm 0) o3
  -- stage 4: the second payload word at `key + 2`
  have o4 : getOrigStorVal sevm sevm.currentTarget (1 + (1 + submissionKey sevm b)) =
      (submissionWord1Store sevm b).getStorVal sevm.currentTarget
        (1 + (1 + submissionKey sevm b)) := by
    rw [submissionWord1Store, keep _ _ _ _ kk3.symm, submissionCallerStore, keep _ _ _ _ kk2.symm,
      submissionTailRead, getStorVal_afterSload, submissionCountStore, keep _ _ _ _ k1''.symm,
      submissionCountRead, getStorVal_afterSload]
    exact original _
  have r4 : (submissionWord1Store sevm b).refundCounter ≤
      (submissionWordsStore sevm b).refundCounter :=
    afterSstore_refundCounter_ge_of_original_eq_current sevm (submissionWord1Store sevm b)
      (1 + (1 + submissionKey sevm b)) (Sevm.dataWord sevm 32) o4
  -- stage 5: the tail store at slot 3, whose current value is the represented tail
  have o5 : getOrigStorVal sevm sevm.currentTarget 3 =
      (submissionLogged sevm b M).getStorVal sevm.currentTarget 3 := by
    rw [FloodWalk.submissionLogged_tail sevm b M σ rep bounds, original 3, getStorVal_eq_getStor]
    exact rep.tail
  have r5 : (submissionLogged sevm b M).refundCounter ≤
      (submissionBase sevm b M).refundCounter :=
    afterSstore_refundCounter_ge_of_original_eq_current sevm (submissionLogged sevm b M)
      3 (1 + submissionTail sevm b) o5
  -- assemble: reads, the log, and `St` keep the counter
  have e1 : b.refundCounter = (submissionCountRead sevm b).refundCounter := by
    rw [submissionCountRead, afterSload_refundCounter]
  have e3 : (submissionCountStore sevm b).refundCounter =
      (submissionTailRead sevm b).refundCounter := by
    rw [submissionTailRead, afterSload_refundCounter]
  have e5 : (submissionWordsStore sevm b).refundCounter =
      (submissionLogged sevm b M).refundCounter := by
    rw [submissionLogged, hLog]
  have e6 : (submissionPost sevm b M G).refundCounter = (submissionBase sevm b M).refundCounter := by
    rw [submissionPost, hSt]
  rw [e6, e1]
  refine r1.trans ?_
  rw [e3]
  refine r2.trans (r3.trans (r4.trans ?_))
  rw [e5]
  exact r5

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
        txGasUsed txC.gas 23000 post.gasLeft post.refundCounter.toNat := by
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
  obtain ⟨_, post, bout', hQ, hproc, hcum, hblk⟩ := processTransaction_call_value_of_exec
    (E := senderE) (t := withdrawalRequestPredeployAddress)
    (Q := fun _ post => TxCPost benv σ iters post)
    hfork rfl hchain.symm (by decide) hbase hcost (by decide)
    (CoveredFork.checkTransactionGasCap_ok hfork (by decide)) (by decide) hroom hrecover hnonce
    hnocode hfunds hnodeleg hprec hexec
  exact ⟨post, bout', hQ, hproc, hcum, hblk⟩

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

-- The two witness transactions' signatures recover senderE from key 1.
-- The concrete recoverSender proof (decide +kernel over the RLP signing hash)
-- is deferred on a UInt8 numeral-normalisation point; the downstream
-- transaction constructors carry recoverSender as a premise (the WETH9 pattern).

end Blanc.Lift.WithdrawalRequest.FloodTx

