import Blanc.Lift.WithdrawalRequest.FloodTxRecover
import Blanc.Lift.WithdrawalRequest.SystemDrain

/-!
# The E5(ii) drain transaction

The E5(ii) negative control's drain transaction: key-1 sender `senderE`, nonce 2, a
zero-value call with empty calldata to SYSTEM_ADDRESS (`0xff…fe`), where the control
installs the SystemDrainer runtime.  `txD_exec` runs its frame (the drainer's `CALL` into the
predeploy's system path, `SystemDrain.drain_exec`) and `txD_processTransaction` forwards the
whole transaction.
-/

namespace Blanc.Lift.WithdrawalRequest.FloodTx

open Jaune Blanc.Lift Blanc.ExecutionTrace

/-- The drain transaction: a zero-value, empty-calldata call to `systemAddress`. -/
def txD : Tx :=
  { nonce := 2, gas := 2 ^ 20, value := 0
    data := []
    v := 0
    r := (0x2ba550518ad1955936234bb6ad552eeab937deecff98751c7f495a48a9594055 : B256).toBytes
    s := (0x09a1f8f3576b0e2ffd997b9d4aa4c200a5085b1a60d67f00eb7b3e21adf274ee : B256).toBytes
    type := .two 1 1 8 (some systemAddress) [] }

def txDSigningPayload : Bytes :=
  [0x02, 0xe0, 0x01, 0x02, 0x01, 0x08, 0x83, 0x10, 0x00, 0x00, 0x94,
   0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
   0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe,
   0x80, 0x80, 0xc0]

theorem txD_signingEncoded :
    txD.signingHash = some txDSigningPayload.keccak := by
  have hc : (UInt64.toBytes 1).sig = [1] := by decide +kernel
  have hn : (UInt64.toBytes 2).sig = [2] := by decide +kernel
  have h1 : Nat.toBytes 1 = [1] := by simp only [Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one,
    zero_add, Nat.one_mod, Nat.toUInt8_eq, UInt8.ofNat_one, Nat.reduceDiv]
  have h8 : Nat.toBytes 8 = [8] := by simp only [Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one,
    Nat.reduceAdd, Nat.reduceMod, Nat.toUInt8_eq, UInt8.reduceOfNat, Nat.reduceDiv]
  have hg : Nat.toBytes (2 ^ 20) = [0x10, 0, 0] := by simp only [Nat.toBytes, Nat.toBytes.aux,
    Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.toUInt8_eq, UInt8.reduceOfNat,
    Nat.reduceDiv, Nat.reducePow]
  have hv : Nat.toBytes 0 = [] := by decide +kernel
  have hto : ((some systemAddress <&> Adr.toBytes).getD []) =
      [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
       0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe] := by decide +kernel
  simp only [Tx.signingHash, txD, hc, hn, h1, h8, hg, hv, hto,
    AccessList.toBLT, List.map_nil]
  apply congrArg some
  apply congrArg Bytes.keccak
  change 2 :: (BLT.list
    [.bytes [1], .bytes [2], .bytes [1], .bytes [8], .bytes [0x10, 0, 0],
     .bytes [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
             0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe],
     .bytes [], .bytes [], .list []]).toBytes = _
  simp only [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin, UInt8.reduceLT, ↓reduceIte,
    List.length_nil, Nat.ofNat_pos, Nat.toUInt8_eq, UInt8.reduceOfNat, add_zero, List.length_cons,
    zero_add, Nat.reduceAdd, Nat.reduceLT, UInt8.reduceAdd,
    List.cons_append, List.nil_append, List.append_nil, txDSigningPayload]

theorem txD_signingHash :
    txD.signingHash =
      some (0x6af97fbfdb78e0c6c23d88d85bc88a663df4be87d10dd10fb4b8c16cdadc03a8 : B256) := by
  rw [txD_signingEncoded]
  decide +kernel

theorem txD_recoveredSender : recoverSender 1 txD = .ok senderE := by
  rw [recoverSender, txD_signingHash]
  decide +kernel

/-- The drain transaction's intrinsic cost: the bare base cost, empty calldata. -/
theorem txD_intrinsic {rules : ForkRules} (hsg : rules.stateGas = none)
    (hbase : rules.gas.txBase = 21000) (hfloor : rules.gas.floorTokenCost = 10) (E : Adr) :
    calculateIntrinsicCost rules txD E = (21000, 21000) := by
  rw [calculateIntrinsicCost_two_call hsg rfl, hbase, hfloor]
  rfl

theorem systemAddress_not_precompile {fork : Fork} (covered : CoveredFork fork) :
    ¬ (Fork.ruleSet fork).isPrecomp systemAddress :=
  covered.cases (motive := fun f => ¬ (Fork.ruleSet f).isPrecomp systemAddress)
    (by decide) (by decide) (by decide) (by decide)

/-- What the drain transaction's frame leaves: the predeploy storage advanced by one system
step, no log, every other storage map and all code untouched, no deletion. -/
def TxDPost (benv : Benv) (σ : Blanc.WithdrawalRequest.State) (post : Devm) : Prop :=
  Blanc.WithdrawalRequest.RepresentsStorage
    (post.state.getStor withdrawalRequestPredeployAddress).get
    (Blanc.WithdrawalRequest.system σ) ∧
  post.logs = [] ∧
  (∀ a, a ≠ withdrawalRequestPredeployAddress → post.state.getStor a = benv.state.getStor a) ∧
  (∀ a, post.state.getCode a = benv.state.getCode a) ∧
  post.accountsToDelete.isEmpty = true

/-- **The drain transaction's frame.**  The message `txD` prepares, entered after the up-front
debit, runs the drainer at SYSTEM_ADDRESS: the frame (depth `1024`, not static) calls the
predeploy, whose caller is SYSTEM_ADDRESS, so its system path dequeues. -/
theorem txD_exec {benv : Benv} {index : Nat} {σ : Blanc.WithdrawalRequest.State}
    (hfork : CoveredFork benv.stat.fork)
    (hdrainer : benv.state.getCode systemAddress = Blanc.Lift.SystemDrainer.code)
    (hcode : benv.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (hrep : Blanc.WithdrawalRequest.RepresentsStorage
      (benv.state.getStor withdrawalRequestPredeployAddress).get σ)
    (hsum : Blanc.WithdrawalRequest.effectiveExcess σ + σ.count < 2 ^ 256) :
    ∀ (debit : State) (msg : Msg) (after : Benv),
      (benv.state.incrNonce senderE).subBal senderE
        (txD.gas * (min 1 (8 - benv.stat.baseFeePerGas) +
          benv.stat.baseFeePerGas)).toB256 = some debit →
      prepareMessage { benv.beginTransaction with state := debit }
        (transactionTenv benv.beginTransaction txD index senderE
          (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas) 21000 []) txD =
          .ok msg →
      msg.benvAfterTransfer = .ok after →
      ∃ post, exec (initEvm (msg.withBenv after)) = .ok post ∧ post.error = none ∧
        0 ≤ post.refundCounter ∧ TxDPost benv σ post := by
  have hES : senderE ≠ systemAddress := by decide
  have hEP : senderE ≠ withdrawalRequestPredeployAddress := by decide
  intro debit msg after hdebit hprep hentry
  rw [prepareMessage_call rfl] at hprep
  have hm := Except.ok.inj hprep
  obtain ⟨-, hdeb⟩ := State.of_subBal hdebit
  have hd_ne : ∀ a, senderE ≠ a → debit.get a = benv.state.get a := fun a h => by
    rw [hdeb]; exact debit_get_ne h
  have hm_value : msg.value = 0 := by rw [← hm]; rfl
  have hm_depth : msg.depth = 1024 := by rw [← hm]; rfl
  have hm_gas : msg.gas = 1027576 := by rw [← hm]; rfl
  have hm_state : msg.benv.state = debit := by rw [← hm]; rfl
  have hm_stat : msg.benv.stat = benv.beginTransaction.stat := by rw [← hm]; rfl
  have hafter : ∀ a, after.state.get a = debit.get a := fun a => by
    rw [benvAfterTransfer_get_of_value_zero hm_value hentry a, hm_state]
  have hstat : after.stat = benv.beginTransaction.stat := by
    rw [benvAfterTransfer_stat hentry, hm_stat]
  have hstor : ∀ a, after.state.getStor a = benv.state.getStor a := fun a => by
    show (after.state.get a).stor = (benv.state.get a).stor
    rw [hafter]
    by_cases h : senderE = a
    · subst h; rw [hdeb, debit_get_self]
    · rw [hd_ne a h]
  have hcodeAll : ∀ a, after.state.getCode a = benv.state.getCode a := fun a => by
    show (after.state.get a).code = (benv.state.get a).code
    rw [hafter]
    by_cases h : senderE = a
    · subst h; rw [hdeb, debit_get_self]
    · rw [hd_ne a h]
  set m := msg.withBenv after with hmdef
  obtain ⟨post, hex, herr, hrepP, hcodeP, hstorP, hlogsP, hdelP, hrefP⟩ :=
    Blanc.Lift.WithdrawalRequest.SystemDrain.drain_exec (msg := m) (σ := σ)
      (by show CoveredFork after.stat.fork; rw [hstat]; exact hfork)
      (by
        show msg.code = _
        rw [← hm]
        show debit.getCode systemAddress = _
        show (debit.get systemAddress).code = _
        rw [hd_ne _ hES]
        exact hdrainer)
      (by show msg.currentTarget = _; rw [← hm]; rfl)
      (by show msg.isStatic = _; rw [← hm]; rfl)
      (by show msg.depth ≠ 0; rw [hm_depth]; decide)
      (by show after.state.getCode _ = _; rw [hcodeAll]; exact hcode)
      (by show Blanc.WithdrawalRequest.RepresentsStorage (after.state.getStor _).get σ
          rw [hstor]; exact hrep)
      hsum
      (by
        intro key
        show (after.stat.origState.getStor _).get key = (after.state.getStor _).get key
        rw [hstat, hstor]
        rfl)
      (by show 427217 ≤ msg.gas; rw [hm_gas]; decide)
      (by show msg.gas < 2 ^ 256; rw [hm_gas]; decide)
  refine ⟨post, hex, herr, hrefP, hrepP, hlogsP, ?_, ?_, hdelP⟩
  · intro a ha
    show post.getStor a = _
    rw [hstorP a ha]
    exact hstor a
  · intro a
    show post.getCode a = _
    rw [hcodeP a]
    exact hcodeAll a

/-- **The drain transaction, forwarded.**  From a world where `senderE` has nonce `2`, no code
and the fee cap in funds, the drainer sits at SYSTEM_ADDRESS and the predeploy is installed
representing `σ`, `txD` is processed: its frame leaves `TxDPost`, its receipt carries no log. -/
theorem txD_processTransaction
    {benv : Benv} {bout : BlockOutput} {index : Nat} {σ : Blanc.WithdrawalRequest.State}
    (hfork : CoveredFork benv.stat.fork)
    (hchain : benv.stat.chainId = 1)
    (hbase : benv.stat.baseFeePerGas ≤ 8)
    (hroom : 2 ^ 20 ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (hrecover : recoverSender benv.stat.chainId txD = .ok senderE)
    (hnonce : (benv.state.get senderE).nonce = 2)
    (hnocode : (benv.state.get senderE).code.isEmpty = true)
    (hfunds : 2 ^ 20 * 8 ≤ (benv.state.get senderE).bal.toNat)
    (hdrainer : benv.state.getCode systemAddress = Blanc.Lift.SystemDrainer.code)
    (hcode : benv.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (hrep : Blanc.WithdrawalRequest.RepresentsStorage
      (benv.state.getStor withdrawalRequestPredeployAddress).get σ)
    (hsum : Blanc.WithdrawalRequest.effectiveExcess σ + σ.count < 2 ^ 256) :
    ∃ (post : Devm) (bout' : BlockOutput), TxDPost benv σ post ∧
      processTransaction benv bout txD index = .ok
        (post.accountsToDelete.toList.foldl destroyAccount
          ((post.state.addBal senderE
              ((txD.gas - txGasUsed txD.gas 21000 post.gasLeft post.refundCounter.toNat) *
                (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256).addBal
            benv.stat.coinbase
              (txGasUsed txD.gas 21000 post.gasLeft post.refundCounter.toNat *
                (min 1 (8 - benv.stat.baseFeePerGas))).toB256),
          bout') ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed +
        txGasUsed txD.gas 21000 post.gasLeft post.refundCounter.toNat ∧
      bout'.blockGasUsed = bout.blockGasUsed +
        txGasUsed txD.gas 21000 post.gasLeft post.refundCounter.toNat ∧
      bout'.receiptKeys = bout.receiptKeys ++ [BLT.toBytes (.bytes index.toBytes)] ∧
      bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
        some (makeReceipt txD none bout'.cumulativeGasUsed post.logs) := by
  have hsg : benv.stat.rules.stateGas = none := CoveredFork.rules_stateGas_none hfork
  have hcost : calculateIntrinsicCost benv.stat.rules txD senderE = (21000, 21000) :=
    txD_intrinsic hsg (CoveredFork.rules_txBase hfork) (CoveredFork.rules_floorTokenCost hfork) _
  have hprec : benv.stat.rules.isPrecomp systemAddress = false :=
    propext (iff_of_false (systemAddress_not_precompile hfork) (by decide))
  have hnodeleg : getDelegatedCodeAddress (benv.state.getCode systemAddress) = none := by
    rw [hdrainer]; decide
  have hexec := txD_exec (benv := benv) (index := index) hfork hdrainer hcode hrep hsum
  obtain ⟨_, post, bout', hQ, hproc, hcum, hblk, hkeys, hreceipt⟩ :=
    processTransaction_call_value_of_exec_receipts
    (E := senderE) (t := systemAddress)
    (Q := fun _ post => TxDPost benv σ post)
    hfork rfl hchain.symm (by decide) hbase hcost (by decide)
    (CoveredFork.checkTransactionGasCap_ok hfork (by decide)) (by decide) hroom hrecover
    (by rw [hnonce]; rfl) hnocode (by show 2 ^ 20 * 8 + (0 : Nat) ≤ _; omega) hnodeleg hprec hexec
  exact ⟨post, bout', hQ, hproc, hcum, hblk, hkeys, hreceipt⟩

end Blanc.Lift.WithdrawalRequest.FloodTx
