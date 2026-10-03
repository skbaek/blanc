import Blanc.Composition.WithdrawalRequestFeeRefutation
import Blanc.Lift.WithdrawalRequest.DrainTx
import Blanc.Lift.WithdrawalRequest.FifoDrainControl
import Blanc.Lift.WithdrawalRequest.SubmissionCount

/-!
# E5(ii): the SYSTEM_ADDRESS exclusion is load-bearing, closed

`block_word_fifo` assumes no code at SYSTEM_ADDRESS (`systemEmpty`).  This module builds, with
no hypotheses, a two-block configured history that keeps every other hypothesis of
`block_word_fifo` but installs the SystemDrainer runtime at SYSTEM_ADDRESS, and whose second
block fails `BlockWordFifo` (`systemEmpty_loadBearing_witness`):

* the checkpoint is the fee refutation's (`checkpointState`) with the drainer at
  SYSTEM_ADDRESS and `senderE` at nonce `1`;
* block A has no transactions: the activation system call resets the inhibitor;
* block D carries `txC` (a direct submission at excess `0`, fee `1`) and `txD` (a call to
  SYSTEM_ADDRESS).  The drainer `CALL`s the predeploy with caller SYSTEM_ADDRESS, so the
  predeploy runs its system path and dequeues `txC`'s request before the block's own system
  call: at the request boundary the queue is empty although the block committed a submission.

Code at SYSTEM_ADDRESS cannot arise on mainnet (no key or CREATE reaches it); the witness
lives only in the formal model, where it shows the trace-local exclusion is necessary.
-/

namespace Blanc.Lift.WithdrawalRequest.DrainControl

open Jaune Blanc.Lift Blanc.ExecutionTrace Blanc.BlockForward FloodTx FeeCounterexample

/-! ## The drain checkpoint -/

/-- The drainer account at SYSTEM_ADDRESS. -/
def drainerAcct : Acct := { Acct.nil with code := Blanc.Lift.SystemDrainer.code }

/-- `senderE` after one transaction: nonce `1`, the refutation's funds. -/
def senderE1Acct : Acct := { Acct.nil with nonce := 1, bal := senderEFunds.toB256 }

/-- The checkpoint state: the refutation's, with `senderE` at nonce `1` and the drainer at
SYSTEM_ADDRESS. -/
def drainState : State := (checkpointState.set senderE senderE1Acct).set systemAddress drainerAcct

theorem drainState_get_other {a : Adr} (hS : systemAddress ≠ a) (hE : senderE ≠ a) :
    drainState.get a = checkpointState.get a := by
  unfold drainState
  rw [State.get_set_ne _ hS, State.get_set_ne _ hE]

theorem drainState_get_system : drainState.get systemAddress = drainerAcct := by
  unfold drainState
  rw [State.get_set_self]

theorem drainState_get_senderE : drainState.get senderE = senderE1Acct := by
  unfold drainState
  rw [State.get_set_ne _ (by decide), State.get_set_self]

theorem drainState_getCode_system :
    drainState.getCode systemAddress = Blanc.Lift.SystemDrainer.code := by
  change (drainState.get systemAddress).code = _
  rw [drainState_get_system]
  rfl

theorem drainState_getStor_other {a : Adr} (hS : systemAddress ≠ a) (hE : senderE ≠ a) :
    drainState.getStor a = checkpointState.getStor a :=
  congrArg (·.stor) (drainState_get_other hS hE)

theorem systemContracts_address_ne {p : Adr × ByteArray} (hp : p ∈ systemContracts) :
    systemAddress ≠ p.1 ∧ senderE ≠ p.1 := by
  simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

theorem drain_installed : SystemCodeInstalled drainState := by
  intro p hp
  obtain ⟨hS, hE⟩ := systemContracts_address_ne hp
  change (drainState.get p.1).code = p.2
  rw [drainState_get_other hS hE]
  exact checkpoint_installed p hp

theorem drain_canonical : drainState.Canonical :=
  (checkpoint_canonical.set senderE Stor.canonical_empty).set systemAddress Stor.canonical_empty

theorem drainState_bal : drainState.bal = checkpointState.bal := by
  funext a
  change (drainState.get a).bal = (checkpointState.get a).bal
  by_cases hS : systemAddress = a
  · subst hS
    rw [drainState_get_system, checkpoint_get_systemAddress]
    rfl
  by_cases hE : senderE = a
  · subst hE
    rw [drainState_get_senderE, checkpoint_get_senderE]
    rfl
  rw [drainState_get_other hS hE]

theorem drain_sum_bound : sum drainState.bal < 2 ^ 256 := by
  rw [drainState_bal]
  exact checkpoint_sum_bound

theorem drainer_callOnly : CallOnlyReach Blanc.Lift.SystemDrainer.code :=
  callOnlyReach_of_check (by decide +kernel)

theorem drainer_not_delegation : ¬ isValidDelegation Blanc.Lift.SystemDrainer.code :=
  fun hd => absurd hd.1 (by decide +kernel)

theorem drain_callOnly : CodesCallOnly drainState.getCode := by
  intro a
  by_cases hS : systemAddress = a
  · subst hS
    rw [drainState_getCode_system]
    exact ⟨drainer_callOnly, drainer_not_delegation⟩
  by_cases hE : senderE = a
  · subst hE
    have hcode : drainState.getCode senderE = ByteArray.empty := by
      change (drainState.get senderE).code = _
      rw [drainState_get_senderE]
      rfl
    rw [hcode]
    exact ⟨callOnlyReach_empty, not_isValidDelegation_empty⟩
  have hcode : drainState.getCode a = checkpointState.getCode a :=
    congrArg (·.code) (drainState_get_other hS hE)
  rw [hcode]
  exact checkpoint_callOnly a

/-- The drain checkpoint's genesis header: the refutation's, committed to `drainState`. -/
def drainGenesisHeader : Header := { genesisHeader with stateRoot := drainState.root }

def drainGenesisBlock : Block :=
  { header := drainGenesisHeader, txs := [], wds := [], ommers := [] }

def drainChain : BlockChain :=
  { blocks := [drainGenesisBlock], state := drainState, chainId := 1 }

theorem drain_validContext : drainChain.ValidContext := by
  refine ⟨by decide +kernel, drain_canonical, ?_, ?_⟩
  · decide +kernel
  · intro tip htip
    have ht : tip = drainGenesisBlock := by
      simpa only [drainChain, List.getLast?_singleton, Option.mem_def,
        Option.some.injEq] using htip.symm
    subst tip
    rfl

theorem drain_ready : ChainReady drainChain drainGenesisBlock :=
  ⟨rfl, List.cons_ne_nil _ _, rfl, rfl, rfl, by decide⟩

/-! ## Block A: activation -/

/-- What block D needs of the state block A leaves. -/
structure PreD (w : State) : Prop where
  zero : Slots7251Zero w
  sender : w.get senderE = senderE1Acct
  drainer : w.getCode systemAddress = Blanc.Lift.SystemDrainer.code
  rep : Blanc.WithdrawalRequest.RepresentsStorage
    (w.getStor withdrawalRequestPredeployAddress).get σA

theorem ApplyTransactionsTrace.settledFrames_nil {txs : List (Nat × Tx)}
    {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (t : ApplyTransactionsTrace txs benv bout finalBenv finalBout) (h : txs = []) :
    t.settledFrames = [] := by
  subst h
  cases t
  rfl

/-- **Stage A**: the activation block on the drain checkpoint; it settles no submission. -/
theorem drain_stageA : ∃ (post : BlockChain)
    (trace : ConfiguredBlockTrace witnessConfig drainChain post) (parent : Block),
    BlockOk trace ∧ PreD post.state ∧ ChainReady post parent ∧
    trace.settledFrames.flatMap submissionFramePayments = [] := by
  obtain ⟨lhA, hlA⟩ := blockHashes_getLast_of_ne drain_ready.nonempty
  obtain ⟨hbody, hz, hrep, -, hkeep⟩ := blockA_run (benv := benvAt drainChain drainGenesisBlock)
    prague_covered drain_installed hlA (drainState_getStor_other (by decide) (by decide))
    (drainState_getStor_other (by decide) (by decide))
  obtain ⟨trace⟩ := witnessBlockTrace drain_ready.last drain_sum_bound rfl rfl rfl
    drain_ready.gasUsed hbody (by decide)
  have blockEq := Blanc.BlockForward.ConfiguredBlockTrace.block_eq trace rfl
  have decoded : trace.bodyTrace.decodedTxs = [] :=
    AppliedBodyTrace.decodedTxs_nil trace.bodyTrace (by rw [blockEq]; rfl)
  have hpre : PreD (bodyPost (benvAt drainChain drainGenesisBlock)
      (stHistory (benvAt drainChain drainGenesisBlock))) := by
    refine ⟨hz, ?_, ?_, hrep⟩
    · rw [hkeep _ (by decide) (by decide) (by decide) (by decide)]
      exact drainState_get_senderE
    · change (Devm.state _).getCode _ = _
      exact (congrArg (·.code) (hkeep _ (by decide) (by decide) (by decide) (by decide))).trans
        drainState_getCode_system
  refine ⟨_, trace, _, blockOk_of trace drain_callOnly drain_installed drain_sum_bound
    (by rw [blockEq]; rfl) (calls_of_nil _ decoded)
    (ApplyTransactionsTrace.noSender_nil trace.bodyTrace.transactions (by rw [decoded]; rfl) _),
    hpre, chainReady_mk _ _ _ _ _ rfl (by decide), ?_⟩
  rw [block_submissions_eq_transactions (.refl witnessConfig_valid drain_validContext rfl) trace
    drain_installed, ApplyTransactionsTrace.settledFrames_nil trace.bodyTrace.transactions
      (by rw [decoded]; rfl)]
  rfl

/-! ## Transaction-fold helpers -/

theorem receiptKey_zero : BLT.toBytes (.bytes (0 : Nat).toBytes) = [0x80] := by
  have h0 : Nat.toBytes 0 = [] := by decide +kernel
  rw [h0]
  simp only [BLT.toBytes, List.length_nil, Nat.ofNat_pos, ↓reduceIte, Nat.toUInt8_eq,
    UInt8.reduceOfNat, add_zero]

theorem receiptKey_one : BLT.toBytes (.bytes (1 : Nat).toBytes) = [0x01] := by
  have h1 : Nat.toBytes 1 = [1] := by simp only [Nat.toBytes, Nat.toBytes.aux,
    Nat.succ_eq_add_one, zero_add, Nat.one_mod, Nat.toUInt8_eq, UInt8.ofNat_one, Nat.reduceDiv]
  rw [h1]
  simp only [BLT.toBytes, UInt8.reduceLT, ↓reduceIte]

theorem receiptKey_ne :
    BLT.toBytes (.bytes (1 : Nat).toBytes) ≠ BLT.toBytes (.bytes (0 : Nat).toBytes) := by
  rw [receiptKey_zero, receiptKey_one]
  decide

/-- The fold over two indexed transactions: each settles in the state the previous left. -/
theorem applyTransactions_two {benv : Benv} {bout bout1 bout2 : BlockOutput} {tx1 tx2 : Tx}
    {s1 s2 : State} (h1 : processTransaction benv bout tx1 0 = .ok (s1, bout1))
    (h2 : processTransaction (benv.withState s1) bout1 tx2 1 = .ok (s2, bout2)) :
    applyTransactions [tx1, tx2].putIndex benv bout = .ok (benv.withState s2, bout2) := by
  change applyTransactions [(0, tx1), (1, tx2)] benv bout = _
  simp only [applyTransactions, h1, h2, bind, Except.bind]
  rfl

/-- A successful transaction inserts exactly its own receipt: every other key of the receipts
trie keeps its entry. -/
theorem processTransaction_receiptsTrie {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {index : Nat} {p : State × BlockOutput} (hp : processTransaction benv bout tx index = .ok p) :
    ∃ r, p.2.receiptsTrie = bout.receiptsTrie.insert (BLT.toBytes (.bytes index.toBytes)) r := by
  unfold processTransaction at hp
  obtain ⟨b1, hb1, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨b2, hb2, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨b3, hb3, hp⟩ := Except.bind_eq_ok hp
  simp only [Except.ok.injEq] at hb1 hb2 hb3
  cases hp
  subst hb1 hb2 hb3
  exact ⟨_, rfl⟩

/-- The head transaction of a nonempty fold, with its frames among the fold's. -/
theorem ApplyTransactionsTrace.head_of_cons {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (t : ApplyTransactionsTrace txs benv bout finalBenv finalBout) {index : Nat} {tx : Tx}
    {rest : List (Nat × Tx)} (h : txs = (index, tx) :: rest) :
    ∃ (st : State) (bo : BlockOutput) (head : TransactionTrace benv bout tx index st bo),
      ∀ f ∈ head.settledFrames, f ∈ t.settledFrames := by
  subst h
  cases t with
  | cons head tail =>
      exact ⟨_, _, head, fun f hf => List.mem_append_left _ hf⟩

/-- A fold whose every transaction recovers to `senderE` has no sender at SYSTEM_ADDRESS. -/
theorem ApplyTransactionsTrace.noSenderAt_of_recover {txs : List (Nat × Tx)}
    {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (t : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (h : ∀ p ∈ txs, recoverSender benv.stat.chainId p.2 = .ok senderE) :
    t.NoSenderAt systemAddress := by
  induction t with
  | nil => trivial
  | cons head tail ih =>
    refine ⟨?_, ih (fun p hp => h p (List.mem_cons_of_mem _ hp))⟩
    intro hsender
    have hrecover' := checkTransaction_sender head.checked
    have hsender' : senderE = head.sender :=
      Except.ok.inj ((h _ List.mem_cons_self).symm.trans hrecover')
    exact (by decide : senderE ≠ systemAddress) (hsender'.trans hsender)

theorem AppliedBodyTrace.decodedTxs_of_mapM {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) {l : List Tx}
    (h : txs.mapM decodeTx = .ok l) : trace.decodedTxs = l :=
  Except.ok.inj (trace.decodeRun.symm.trans h)

theorem calls_of_two {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (hdecoded : trace.decodedTxs = [txC, txD]) :
    ∀ p ∈ trace.decodedTxs.putIndex, (∃ t, p.2.type.receiver? = some t) ∧ p.2.auths = [] := by
  intro p hp
  rw [hdecoded] at hp
  change p ∈ [(0, txC), (1, txD)] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨⟨_, rfl⟩, rfl⟩
  · exact ⟨⟨_, rfl⟩, rfl⟩

/-! ## The model states of block D -/

/-- The model after block D's submission. -/
def σ1 : Blanc.WithdrawalRequest.State :=
  Blanc.WithdrawalRequest.submit σA (entryWith senderE)

/-- One system step empties it: the queue holds one entry, at most `16` leave. -/
theorem system_σ1_queue : (Blanc.WithdrawalRequest.system σ1).queue = [] := rfl

theorem σ1_sum : Blanc.WithdrawalRequest.effectiveExcess σ1 + σ1.count < 2 ^ 256 := by
  rw [σ1, σA_eq]
  decide

theorem σA_bounds : SubmissionBounds σA := by
  rw [σA_eq]
  exact ⟨by decide, by decide⟩

theorem σA_excess_lt : σA.excess + 1 < 2 ^ 256 := by
  rw [σA_eq]
  decide

theorem σA_run : WordFakeExponential.Run σA.excess.toB256 17 1 17 0 1 17 := by
  have h0 : σA.excess.toB256 = 0 := by rw [σA_eq]; decide
  rw [h0]
  exact FloodWalk.wordRun_zero

theorem σA_paid : ((17 : B256) / (17 : B256)).toNat ≤ 2 ^ 245 := by decide

/-! ## Block D: submission, then drain -/

/-- **Block D**: `txC` submits at excess `0`, then `txD` calls the drainer at SYSTEM_ADDRESS.
The settled transaction state `s` represents `system σ1`, whose queue is empty. -/
theorem blockD_run {benv : Benv} {lastHash : B256}
    (hfork : CoveredFork benv.stat.fork) (installed : SystemCodeInstalled benv.state)
    (hlast : benv.stat.blockHashes.getLast? = some lastHash) (hpre : PreD benv.state)
    (hchain : benv.stat.chainId = 1) (hbase : benv.stat.baseFeePerGas = 1)
    (hroom : 2 ^ 21 ≤ benv.stat.blockGasLimit) (hcb : benv.stat.coinbase ≠ senderE) :
    ∃ (s : State) (bout : BlockOutput),
      applyTransactions [txC, txD].putIndex (benvH benv) BlockOutput.init =
        .ok ((benvH benv).withState s, bout) ∧
      applyBody benv [Sum.inr txC, Sum.inr txD] [] =
        .ok (bodyPost benv s, bodyOut benv s bout) ∧
      bout.blockGasUsed ≤ 2 ^ 28 ∧
      Blanc.WithdrawalRequest.RepresentsStorage
        (s.getStor withdrawalRequestPredeployAddress).get (Blanc.WithdrawalRequest.system σ1) := by
  have hsender : (stHistory benv).get senderE = senderE1Acct :=
    (stHistory_get_of_installed hfork installed hlast (by decide) (by decide)).trans hpre.sender
  have hcodeW : (stHistory benv).getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode :=
    (stHistory_getCode_inst hfork installed hlast _ (by decide) (by decide)).trans
      (systemCodeInstalled_withdrawal installed)
  have hcodeC : (stHistory benv).getCode consolidationRequestPredeployAddress =
      Blanc.consolidationRequestCode :=
    (stHistory_getCode_inst hfork installed hlast _ (by decide) (by decide)).trans
      (systemCodeInstalled_consolidation installed)
  have hcodeS : (stHistory benv).getCode systemAddress = Blanc.Lift.SystemDrainer.code :=
    (stHistory_getCode_inst hfork installed hlast _ (by decide) (by decide)).trans hpre.drainer
  have hrepA : Blanc.WithdrawalRequest.RepresentsStorage
      ((stHistory benv).getStor withdrawalRequestPredeployAddress).get σA := by
    rw [stHistory_getStor_inst hfork installed hlast _ (by decide) (by decide)]
    exact hpre.rep
  have hfundsE : senderE1Acct.bal.toNat = senderEFunds :=
    B256.toNat_toB256_of_lt senderEFunds_lt
  have hprice : min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas = 2 := by
    rw [hbase]
    rfl
  -- txC
  obtain ⟨postC, boutC, hQ, hprocC, -, hblkC, hkeysC, hreceiptC⟩ := txC_processTransaction
    (benv := benv.withState (stHistory benv)) (bout := BlockOutput.init) (index := 0)
    hfork hchain (by rw [show (benv.withState (stHistory benv)).stat.baseFeePerGas =
      benv.stat.baseFeePerGas from rfl, hbase]; decide)
    (by show 2 ^ 20 ≤ benv.stat.blockGasLimit - 0; omega)
    (by show recoverSender benv.stat.chainId txC = _; rw [hchain]; exact txC_recoveredSender)
    (by change ((stHistory benv).get senderE).nonce = 1; rw [hsender]; rfl)
    (by change ((stHistory benv).get senderE).code.isEmpty = true; rw [hsender]; rfl)
    (by
      change 2 ^ 20 * 8 + 2 ^ 245 ≤ ((stHistory benv).get senderE).bal.toNat
      rw [hsender, hfundsE]
      unfold senderEFunds
      omega)
    hcodeW hrepA σA_bounds σA_excess_lt σA_run σA_paid (by decide)
  set RC : B256 := ((txC.gas - txGasUsed txC.gas 23000 postC.gasLeft
    postC.refundCounter.toNat) * (min 1 (8 - benv.stat.baseFeePerGas) +
      benv.stat.baseFeePerGas)).toB256 with hRC
  set sC : State := settledState postC senderE benv.stat.coinbase RC
    (txGasUsed txC.gas 23000 postC.gasLeft postC.refundCounter.toNat *
      (min 1 (8 - benv.stat.baseFeePerGas))).toB256 with hsC
  have hprocC' : processTransaction (benvH benv) BlockOutput.init txC 0 = .ok (sC, boutC) := by
    rw [settled_of_no_deletions postC senderE _ _ _ hQ.2.2.2.2.1] at hprocC
    exact hprocC
  have hcodesC : ∀ a, sC.getCode a = (stHistory benv).getCode a := fun a =>
    TxCPost_settled_codes hQ _ _ a _ _
  have hstorC : sC.getStor consolidationRequestPredeployAddress =
      (stHistory benv).getStor consolidationRequestPredeployAddress :=
    TxCPost_settled_stor7251 hQ (by decide) _ _ _ _
  have hrep1 : Blanc.WithdrawalRequest.RepresentsStorage
      (sC.getStor withdrawalRequestPredeployAddress).get σ1 := by
    rw [hsC, settledState_getStor]
    exact hQ.1
  have hgetE : sC.get senderE = (postC.state.get senderE).withBal
      (postC.state.bal senderE + RC) := by
    rw [hsC, settledState, addBal_get_ne _ hcb, addBal_get_self]
  have husedC := txGasUsed_le (gas := txC.gas) (floor := 23000) (left := postC.gasLeft)
    (refund := postC.refundCounter.toNat) (by decide)
  have hgasC : txC.gas = 2 ^ 20 := rfl
  -- txD
  obtain ⟨postD, boutD, hQD, hprocD, -, hblkD, hkeysD, hreceiptD⟩ := txD_processTransaction
    (benv := benv.withState sC) (bout := boutC) (index := 1) (σ := σ1)
    hfork hchain (by rw [show (benv.withState sC).stat.baseFeePerGas =
      benv.stat.baseFeePerGas from rfl, hbase]; decide)
    (by
      show 2 ^ 20 ≤ benv.stat.blockGasLimit - boutC.blockGasUsed
      rw [hblkC]
      change 2 ^ 20 ≤ benv.stat.blockGasLimit - (0 + _)
      omega)
    (by show recoverSender benv.stat.chainId txD = _; rw [hchain]; exact txD_recoveredSender)
    (by
      change (sC.get senderE).nonce = 2
      rw [hgetE]
      change (postC.state.get senderE).nonce = 2
      rw [hQ.2.2.2.2.2.2.1]
      change ((stHistory benv).get senderE).nonce + 1 = 2
      rw [hsender]
      rfl)
    (by
      change (sC.get senderE).code.isEmpty = true
      have h := hcodesC senderE
      change (sC.get senderE).code = ((stHistory benv).get senderE).code at h
      rw [h, hsender]
      rfl)
    (by
      change 2 ^ 20 * 8 ≤ (sC.get senderE).bal.toNat
      rw [hgetE]
      change 2 ^ 20 * 8 ≤ (postC.state.bal senderE + RC).toNat
      have hbal : postC.state.bal senderE = senderEFunds.toB256 -
          (2 ^ 20 * (min 1 (8 - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas)).toB256 - (2 ^ 245 : Nat).toB256 := by
        show (postC.state.get senderE).bal = _
        rw [hQ.2.2.2.2.2.1]
        change ((stHistory benv).get senderE).bal - _ - _ = _
        rw [hsender]
        rfl
      rw [hbal, hRC, hprice, hgasC]
      rw [hgasC] at husedC
      have hF : senderEFunds.toB256.toNat = senderEFunds :=
        B256.toNat_toB256_of_lt senderEFunds_lt
      unfold senderEFunds at hF ⊢
      rw [toNat_sub_sub_add (by rw [hF]; omega) (by omega) (by rw [hF]; omega), hF]
      omega)
    (by change sC.getCode systemAddress = _; rw [hcodesC]; exact hcodeS)
    (by change sC.getCode _ = _; rw [hcodesC]; exact hcodeW)
    hrep1 σ1_sum
  set sD : State := settledState postD senderE benv.stat.coinbase
    ((txD.gas - txGasUsed txD.gas 21000 postD.gasLeft postD.refundCounter.toNat) *
      (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256
    (txGasUsed txD.gas 21000 postD.gasLeft postD.refundCounter.toNat *
      (min 1 (8 - benv.stat.baseFeePerGas))).toB256 with hsD
  have hprocD' : processTransaction ((benvH benv).withState sC) boutC txD 1 =
      .ok (sD, boutD) := by
    rw [settled_of_no_deletions postD senderE _ _ _ hQD.2.2.2.2] at hprocD
    exact hprocD
  have htxs : applyTransactions [txC, txD].putIndex (benvH benv) BlockOutput.init =
      .ok ((benvH benv).withState sD, boutD) := by
    exact applyTransactions_two hprocC' hprocD'
  have hdeposit : parseDepositRequests boutD = .ok [] := by
    apply parseDepositRequests_of_no_deposit_logs
    intro key hkey
    rw [hkeysD, hkeysC] at hkey
    change key ∈ ([] ++ [BLT.toBytes (.bytes (0 : Nat).toBytes)]) ++
      [BLT.toBytes (.bytes (1 : Nat).toBytes)] at hkey
    simp only [List.nil_append, List.mem_append, List.mem_singleton] at hkey
    rcases hkey with rfl | rfl
    · obtain ⟨r, hr⟩ := processTransaction_receiptsTrie hprocD'
      change boutD.receiptsTrie = _ at hr
      refine ⟨makeReceipt txC none boutC.cumulativeGasUsed postC.logs, ?_, ?_⟩
      · rw [hr, Std.TreeMap.getElem?_insert]
        split
        · rename_i h
          exact absurd (Std.LawfulEqCmp.eq_of_compare h) receiptKey_ne
        · exact hreceiptC
      · intro log hlog
        change log ∈ postC.logs at hlog
        rw [hQ.2.1, List.mem_singleton] at hlog
        rw [hlog]
        decide
    · refine ⟨_, hreceiptD, ?_⟩
      intro log hlog
      change log ∈ postD.logs at hlog
      rw [hQD.2.1] at hlog
      exact absurd hlog List.not_mem_nil
  have hWcode : sD.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode := by
    rw [hsD, settledState_getCode, hQD.2.2.2.1]
    change sC.getCode _ = _
    rw [hcodesC]
    exact hcodeW
  have hCcode : sD.getCode consolidationRequestPredeployAddress =
      Blanc.consolidationRequestCode := by
    rw [hsD, settledState_getCode, hQD.2.2.2.1]
    change sC.getCode _ = _
    rw [hcodesC]
    exact hcodeC
  have hz : Slots7251Zero sD := by
    apply slots7251Zero_of_getStor _ hpre.zero
    rw [hsD, settledState_getStor, hQD.2.2.1 _ (by decide)]
    change sC.getStor _ = _
    rw [hstorC]
    exact stHistory_getStor_inst hfork installed hlast _ (by decide) (by decide)
  have husedD := txGasUsed_le (gas := txD.gas) (floor := 21000) (left := postD.gasLeft)
    (refund := postD.refundCounter.toNat) (by decide)
  refine ⟨sD, boutD, htxs, body_of_txs hfork installed hlast rfl htxs hdeposit hWcode hCcode hz,
    ?_, ?_⟩
  · rw [hblkD, hblkC]
    change 0 + _ + _ ≤ 2 ^ 28
    have hgasD : txD.gas = 2 ^ 20 := rfl
    omega
  · rw [hsD, settledState_getStor]
    exact hQD.1

/-- **Stage D**: block D as a configured block trace.  It commits `txC`'s submission frame, and
at its request boundary the predeploy storage represents a model state with an empty queue. -/
theorem drain_stageD {pre : BlockChain} {parent : Block} (ready : ChainReady pre parent)
    (installed : SystemCodeInstalled pre.state) (hworld : CodesCallOnly pre.state.getCode)
    (hbound : sum pre.state.bal < 2 ^ 256) (hpre : PreD pre.state) :
    ∃ (post : BlockChain) (trace : ConfiguredBlockTrace witnessConfig pre post),
      BlockOk trace ∧
      trace.bodyTrace.transactions.settledFrames.flatMap submissionFramePayments ≠ [] ∧
      ∃ s : Blanc.WithdrawalRequest.State,
        Blanc.WithdrawalRequest.RepresentsStorage
          (trace.bodyTrace.requestBenv.state.getStor withdrawalRequestPredeployAddress).get s ∧
        s.queue = [] := by
  obtain ⟨lh, hl⟩ := blockHashes_getLast_of_ne ready.nonempty
  have hf := benvAt_facts pre parent
  obtain ⟨sD, boutD, -, hbody, hgas, -⟩ := blockD_run (benv := benvAt pre parent) hf.1
    installed hl hpre (hf.2.2.1.trans ready.chainId) hf.2.2.2.1
    (by rw [hf.2.2.2.2.1]; decide) hf.2.2.2.2.2.1
  obtain ⟨trace⟩ := witnessBlockTrace ready.last hbound ready.chainId ready.gasLimit
    ready.baseFee ready.gasUsed hbody (hgas.trans (by decide))
  have blockEq := Blanc.BlockForward.ConfiguredBlockTrace.block_eq trace rfl
  have decoded : trace.bodyTrace.decodedTxs = [txC, txD] :=
    AppliedBodyTrace.decodedTxs_of_mapM trace.bodyTrace (by rw [blockEq]; rfl)
  -- the transactions' environment is the functional one
  set benv0 := initBenv trace.fork pre trace.block.header with hbenv0
  have hfork0 : CoveredFork benv0.stat.fork := trace.covered
  have installed0 : SystemCodeInstalled benv0.state := installed
  have hl0 : benv0.stat.blockHashes.getLast? = some lh := hl
  have hpre0 : PreD benv0.state := hpre
  have hchain : benv0.stat.chainId = 1 := ready.chainId
  have hbase : benv0.stat.baseFeePerGas = 1 := by
    show trace.block.header.baseFeePerGas = 1
    rw [blockEq]; rfl
  have hlimit : benv0.stat.blockGasLimit = 2 ^ 29 := by
    show trace.block.header.gasLimit = 2 ^ 29
    rw [blockEq]; rfl
  have hcb : benv0.stat.coinbase ≠ senderE := by
    show trace.block.header.coinbase ≠ senderE
    rw [blockEq]
    show witnessCoinbase ≠ senderE
    decide
  obtain ⟨s0, bout0, htxs0, -, -, hrep0⟩ := blockD_run (benv := benv0) hfork0 installed0 hl0 hpre0
    hchain hbase (by rw [hlimit]; decide) hcb
  obtain ⟨hB, hH⟩ := AppliedBodyTrace.history_eq trace.bodyTrace hfork0 installed0
  have hrun := trace.bodyTrace.transactions.run
  rw [decoded, hB, hH] at hrun
  unfold benvH at htxs0
  have htb := (Prod.mk.inj (Except.ok.inj (hrun.symm.trans htxs0))).1
  -- txC's committed submission frame
  obtain ⟨st, bo, head, hsub⟩ := ApplyTransactionsTrace.head_of_cons
    trace.bodyTrace.transactions (by rw [decoded]; rfl)
  have hsenderH : trace.bodyTrace.historyState.get senderE = senderE1Acct := by
    rw [hH]
    exact (stHistory_get_of_installed hfork0 installed0 hl0 (by decide) (by decide)).trans
      hpre0.sender
  have hfundsE : senderE1Acct.bal.toNat = senderEFunds :=
    B256.toNat_toB256_of_lt senderEFunds_lt
  obtain ⟨frame, hmem, hpay, -, -⟩ := txC_submissionFrame
    (benv := (benv0.withState trace.bodyTrace.beaconState).withState
      trace.bodyTrace.historyState) head hfork0 hchain
    (by show benv0.stat.baseFeePerGas ≤ 8; rw [hbase]; decide)
    (by show 2 ^ 20 ≤ benv0.stat.blockGasLimit; rw [hlimit]; decide)
    (by change (trace.bodyTrace.historyState.get senderE).nonce = 1; rw [hsenderH]; rfl)
    (by change (trace.bodyTrace.historyState.get senderE).code.isEmpty = true
        rw [hsenderH]; rfl)
    (by
      change 2 ^ 20 * 8 + 2 ^ 245 ≤ (trace.bodyTrace.historyState.get senderE).bal.toNat
      rw [hsenderH, hfundsE]
      unfold senderEFunds
      omega)
    (by
      change trace.bodyTrace.historyState.getCode _ = _
      rw [hH]
      exact (stHistory_getCode_inst hfork0 installed0 hl0 _ (by decide) (by decide)).trans
        (systemCodeInstalled_withdrawal installed0))
    (by
      change Blanc.WithdrawalRequest.RepresentsStorage
        (trace.bodyTrace.historyState.getStor _).get σA
      rw [hH, stHistory_getStor_inst hfork0 installed0 hl0 _ (by decide) (by decide)]
      exact hpre0.rep)
    σA_bounds σA_excess_lt σA_run σA_paid (by decide)
  have hchainT : (((initBenv trace.fork pre trace.block.header).withState
      trace.bodyTrace.beaconState).withState trace.bodyTrace.historyState).stat.chainId = 1 :=
    ready.chainId
  refine ⟨_, trace, blockOk_of trace hworld installed hbound (by rw [blockEq]; rfl)
    (calls_of_two _ decoded)
    (ApplyTransactionsTrace.noSenderAt_of_recover trace.bodyTrace.transactions (by
      rw [decoded]
      intro p hp
      change p ∈ [(0, txC), (1, txD)] at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rw [hchainT]
      rcases hp with rfl | rfl
      · exact txC_recoveredSender
      · exact txD_recoveredSender)), ?_, Blanc.WithdrawalRequest.system σ1, ?_, system_σ1_queue⟩
  · apply List.ne_nil_of_mem (a := (frame, frame.sevm.value.toNat))
    apply List.mem_flatMap.mpr
    refine ⟨frame, hsub frame hmem, ?_⟩
    unfold submissionFramePayments
    rw [ite_eq_left hpay]
    exact List.mem_singleton_self _
  · change Blanc.WithdrawalRequest.RepresentsStorage
      ((processWithdrawalsState trace.bodyTrace.transactionBenv.state trace.block.wds).getStor
        _).get _
    rw [processWithdrawalsState_getStor_eq, htb]
    exact hrep0

/-! ## The negative control -/

/-- **E5(ii), closed: the SYSTEM_ADDRESS exclusion of the FIFO headline is load-bearing.**
With no hypotheses: the two-block history from the drain checkpoint (`drainChain`, the drainer
at SYSTEM_ADDRESS) keeps every other hypothesis of `block_word_fifo` (installed system code, no
sender or authority at SYSTEM_ADDRESS, no code-free root frame targeting it, INIT, the
occurrence cap), and block D fails `BlockWordFifo`. -/
theorem systemEmpty_loadBearing_witness : SystemEmptyLoadBearing := by
  obtain ⟨chainA, traceA, parentA, okA, preD, readyA, beforeA⟩ := drain_stageA
  obtain ⟨chainD, traceD, okD, committed, drained⟩ :=
    drain_stageD readyA okA.installed okA.world okA.bound preD
  refine systemEmpty_loadBearing
    (ConfiguredHistoryTrace.step (.refl witnessConfig_valid drain_validContext rfl) traceA) traceD
    drain_installed ⟨⟨trivial, okA.senders⟩, okD.senders⟩
    ⟨⟨trivial, okA.authorities⟩, okD.authorities⟩ ?_ ?_ ?_ ?_ ?_ committed drained
  · intro root member
    simp only [ConfiguredHistoryTrace.rawFrames, List.nil_append, List.mem_append] at member
    rcases member with hA | hD
    · exact okA.avoid root hA
    · exact okD.avoid root hD
  · change drainState.getCode systemAddress ≠ ByteArray.empty
    rw [drainState_getCode_system]
    decide
  · change Blanc.WithdrawalRequest.RepresentsStorage
      (drainState.getStor withdrawalRequestPredeployAddress).get Blanc.WithdrawalRequest.initial
    rw [drainState_getStor_other (by decide) (by decide)]
    exact checkpoint_7002_rep
  · have payments := submissionFramePayments_length_le
      (ConfiguredHistoryTrace.step (ConfiguredHistoryTrace.step
        (.refl witnessConfig_valid drain_validContext rfl) traceA) traceD).settledFrames
    have frames := (ConfiguredHistoryTrace.step (ConfiguredHistoryTrace.step
      (.refl witnessConfig_valid drain_validContext rfl) traceA) traceD).settledFrames_length_le
    have count : (ConfiguredHistoryTrace.step (ConfiguredHistoryTrace.step
      (.refl witnessConfig_valid drain_validContext rfl) traceA) traceD).blockCount = 2 := rfl
    have cap : (2 : Nat) * 2 ^ 64 ≤ wordOccurrenceCap := by
      unfold wordOccurrenceCap
      decide
    rw [count] at frames
    omega
  · change ([] ++ traceA.settledFrames).flatMap submissionFramePayments = []
    rw [List.nil_append]
    exact beforeA

end Blanc.Lift.WithdrawalRequest.DrainControl
