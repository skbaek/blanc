import Blanc.Lift.WithdrawalRequest.FloodTx
import Blanc.Lift.WithdrawalRequest.FloodTxRecover
import Blanc.Lift.WithdrawalRequest.ProtocolOccurrences
import Blanc.Lift.WithdrawalRequest.BalanceHistory
import Blanc.BlockForward
import Blanc.ExecutionTraceRootFrame
import Blanc.Lift.BeaconRoots.SystemWalk
import Blanc.Lift.HistoryStorage.SystemWalk
import Blanc.Lift.WithdrawalRequest.SystemProtocol
import Blanc.Lift.ConsolidationRequest.SystemWalk

/-!
# The mathematical-fee refutation: block assembly

The witness history is three configured blocks on a Prague chain:

* **A** activates the fork: no transactions, the four system calls.
* **B** carries `txB`, which runs the flood caller for `2895` fee-1 submissions.
* **C** carries `txC`, the direct `2 ^ 245`-wei submission at excess `2893`.

This module assembles each block's body from its transaction forward lemma
(`txB_processTransaction`, `txC_processTransaction`) and the block-forward
constructor, with the system-call results, the deposit parse, and the header
facts carried as hypotheses, and chains the three `ConfiguredBlockTrace`s into
a `ConfiguredHistoryTrace`.  The two `recoverSender` premises stay isolated,
one per transaction.
-/

namespace Blanc.Lift.WithdrawalRequest.FeeCounterexample

open Jaune Blanc.Lift Blanc.ExecutionTrace Blanc.BlockForward FloodTx



/-- The transaction fold over a single indexed transaction is that transaction's
settlement, its state installed. -/
theorem applyTransactions_single {benv : Benv} {bout bout' : BlockOutput} {tx : Tx}
    {index : Nat} {st : State}
    (h : processTransaction benv bout tx index = .ok (st, bout')) :
    applyTransactions [(index, tx)] benv bout = .ok (benv.withState st, bout') := by
  unfold applyTransactions
  rw [h]
  rfl

theorem putIndex_single (tx : Tx) : [tx].putIndex = [(0, tx)] := rfl

theorem decode_single (tx : Tx) : [Sum.inr tx].mapM decodeTx = .ok [tx] := rfl

/-- A one-transaction body retains exactly that decoded transaction. -/
theorem AppliedBodyTrace.decodedTxs_eq {benv : Benv} {tx : Tx} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv [Sum.inr tx] wds state bout) :
    trace.decodedTxs = [tx] := by
  exact Except.ok.inj (trace.decodeRun.symm.trans (decode_single tx))

theorem AppliedBodyTrace.decodedTxs_eq_of_txs_eq
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {tx : Tx} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (htxs : txs = [Sum.inr tx]) :
    trace.decodedTxs = [tx] := by
  have hdecode : txs.mapM decodeTx = .ok [tx] := by
    rw [htxs]
    exact decode_single tx
  exact Except.ok.inj (trace.decodeRun.symm.trans hdecode)

theorem noSenderAt_single {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    {tx : Tx} (trace : ApplyTransactionsTrace [(0, tx)] benv bout finalBenv finalBout)
    (hrecover : recoverSender benv.stat.chainId tx = .ok senderE) :
    trace.NoSenderAt systemAddress := by
  cases trace with
  | cons head tail =>
    cases tail with
    | nil =>
      refine ⟨?_, trivial⟩
      intro hsender
      have hrecover' := checkTransaction_sender head.checked
      have hrecover'' : recoverSender benv.stat.chainId tx = .ok head.sender := by
        simpa only [Benv.beginTransaction] using hrecover'
      have hsender' : senderE = head.sender :=
        Except.ok.inj (hrecover.symm.trans hrecover'')
      exact (by decide : senderE ≠ systemAddress) (hsender'.trans hsender)

theorem noAuthorityAt_decoded {benv : Benv} {txs : List (Bytes ⊕ Tx)} {tx : Tx}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (hdecoded : trace.decodedTxs = [tx]) (hauths : tx.auths = []) :
    ∀ p ∈ trace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
      recoverAuthority auth = .ok authority → authority ≠ systemAddress := by
  rw [hdecoded, putIndex_single]
  intro p hp
  rw [List.mem_singleton] at hp
  subst p
  rw [hauths]
  intro auth hauth
  exact False.elim (List.not_mem_nil hauth)

theorem noAuthorityAt_single {benv : Benv} {tx : Tx} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv [Sum.inr tx] wds state bout)
    (hauths : tx.auths = []) :
    ∀ p ∈ trace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
      recoverAuthority auth = .ok authority → authority ≠ systemAddress := by
  apply noAuthorityAt_decoded trace (AppliedBodyTrace.decodedTxs_eq trace)
  exact hauths

/-- A root frame supplied by `TransactionTrace.root_frame_of_call_value` is a
balance observation when its target is the withdrawal predeploy and it is
dynamic. -/
theorem member_of_root_frame
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} {frame : Exec.Frame}
    (trace : TransactionTrace benv bout tx index state bout')
    (hmem : frame ∈ trace.settledFrames)
    (htarget : frame.sevm.currentTarget = withdrawalRequestPredeployAddress)
    (hstatic : frame.sevm.isStatic = false) :
    frame ∈ trace.settledFrames.flatMap balanceFrameObservation := by
  apply List.mem_flatMap.mpr
  refine ⟨frame, hmem, ?_⟩
  unfold balanceFrameObservation
  rw [htarget, hstatic]
  exact List.mem_singleton_self _

/-- The settled state of a transaction whose frame scheduled no deletion and whose
sender and coinbase are credited, as `processTransaction` returns it. -/
def settledState (post : Devm) (E coinbase : Adr) (refund tip : B256) : State :=
  (post.state.addBal E refund).addBal coinbase tip

/-- The settled state once the frame's deletion set is known empty. -/
theorem settled_of_no_deletions (post : Devm) (E coinbase : Adr) (refund tip : B256)
    (hdel : post.accountsToDelete.isEmpty = true) :
    post.accountsToDelete.toList.foldl destroyAccount
      ((post.state.addBal E refund).addBal coinbase tip) =
      settledState post E coinbase refund tip := by
  have hlist : post.accountsToDelete.toList = [] := by
    apply List.isEmpty_iff.mp
    rw [Std.HashSet.isEmpty_toList]
    exact hdel
  rw [hlist]
  rfl

/-- The deposit parse of a block output holding one receipt whose logs all sit at the
withdrawal predeploy. -/
theorem parseDepositRequests_of_predeploy_logs {bout : BlockOutput} {tx : Tx} {cum : Nat}
    {logs : List Log} {index : Nat}
    (hkeys : bout.receiptKeys = [BLT.toBytes (.bytes index.toBytes)])
    (hreceipt : bout.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
      some (makeReceipt tx none cum logs))
    (hlogs : ∀ log ∈ logs, log.address = withdrawalRequestPredeployAddress) :
    parseDepositRequests bout = .ok [] := by
  apply parseDepositRequests_of_no_deposit_logs
  intro key hkey
  rw [hkeys, List.mem_singleton] at hkey
  subst hkey
  refine ⟨_, hreceipt, ?_⟩
  intro log hlog
  change log ∈ logs at hlog
  rw [hlogs log hlog]
  decide

/-- The state after the EIP-4788 beacon-roots system call. -/
def stBeacon (benv : Benv) : State :=
  (BeaconRoots.systemPost benv).state

/-- The state after the EIP-2935 history-storage system call. -/
def stHistory (benv : Benv) : State :=
  (HistoryStorage.systemPost (benv.withState (stBeacon benv))).state

/-- The call output of the EIP-4788 beacon-roots system call. -/
def outBeacon (benv : Benv) : MsgCallOutput :=
  systemCallOutput (BeaconRoots.systemPost benv)

/-- The call output of the EIP-2935 history-storage system call. -/
def outHistory (benv : Benv) : MsgCallOutput :=
  systemCallOutput (HistoryStorage.systemPost (benv.withState (stBeacon benv)))

theorem systemCodeInstalled_beaconRoots {w : State} (h : SystemCodeInstalled w) :
    w.getCode beaconRootsAddress = beaconRootsCode :=
  h (beaconRootsAddress, beaconRootsCode)
    (by simp only [systemContracts, List.mem_cons, true_or])

theorem systemCodeInstalled_historyStorage {w : State} (h : SystemCodeInstalled w) :
    w.getCode historyStorageAddress = historyStorageCode :=
  h (historyStorageAddress, historyStorageCode)
    (by simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true])

theorem stBeacon_step {benv : Benv} (hfork : CoveredFork benv.stat.fork)
    (hcode : benv.state.getCode beaconRootsAddress = beaconRootsCode) :
    processUncheckedSystemTransaction benv beaconRootsAddress
        benv.stat.parentBeaconBlockRoot.toBytes =
      .ok (stBeacon benv, outBeacon benv) ∧
    ∀ a, beaconRootsAddress ≠ a → (stBeacon benv).get a = benv.state.get a := by
  have h := BeaconRoots.processUncheckedSystemTransaction_beaconRoots hfork hcode
  exact ⟨h.1, h.2.2⟩

theorem stHistory_step {benv : Benv} {lastHash : B256}
    (hfork : CoveredFork benv.stat.fork)
    (hbeaconCode : benv.state.getCode beaconRootsAddress = beaconRootsCode)
    (hhistoryCode : benv.state.getCode historyStorageAddress = historyStorageCode)
    (hlast : benv.stat.blockHashes.getLast? = some lastHash) :
    processUncheckedSystemTransaction (benv.withState (stBeacon benv)) historyStorageAddress
        lastHash.toBytes = .ok (stHistory benv, outHistory benv) ∧
    ∀ a, historyStorageAddress ≠ a → (stHistory benv).get a = (stBeacon benv).get a := by
  have hB := stBeacon_step hfork hbeaconCode
  have hneBH : beaconRootsAddress ≠ historyStorageAddress := by decide
  have hgetH : (stBeacon benv).get historyStorageAddress = benv.state.get historyStorageAddress :=
    hB.2 historyStorageAddress hneBH
  have hcodeH : (stBeacon benv).getCode historyStorageAddress = historyStorageCode := by
    change ((stBeacon benv).get historyStorageAddress).code = historyStorageCode
    rw [hgetH]
    exact hhistoryCode
  have hlast' : (benv.withState (stBeacon benv)).stat.blockHashes.getLast? = some lastHash := hlast
  have h := HistoryStorage.processUncheckedSystemTransaction_historyStorage
    (benv := benv.withState (stBeacon benv)) hfork hcodeH hlast'
  exact ⟨h.1, h.2.2⟩

theorem stHistory_get {benv : Benv} {lastHash : B256} {a : Adr}
    (hfork : CoveredFork benv.stat.fork)
    (hbeaconCode : benv.state.getCode beaconRootsAddress = beaconRootsCode)
    (hhistoryCode : benv.state.getCode historyStorageAddress = historyStorageCode)
    (hlast : benv.stat.blockHashes.getLast? = some lastHash)
    (hneB : beaconRootsAddress ≠ a) (hneH : historyStorageAddress ≠ a) :
    (stHistory benv).get a = benv.state.get a := by
  have hB := stBeacon_step hfork hbeaconCode
  have hH := stHistory_step hfork hbeaconCode hhistoryCode hlast
  rw [hH.2 a hneH, hB.2 a hneB]

theorem stHistory_get_of_installed {benv : Benv} {lastHash : B256} {a : Adr}
    (hfork : CoveredFork benv.stat.fork)
    (installed : SystemCodeInstalled benv.state)
    (hlast : benv.stat.blockHashes.getLast? = some lastHash)
    (hneB : beaconRootsAddress ≠ a) (hneH : historyStorageAddress ≠ a) :
    (stHistory benv).get a = benv.state.get a :=
  stHistory_get hfork
    (systemCodeInstalled_beaconRoots installed)
    (systemCodeInstalled_historyStorage installed)
    hlast hneB hneH

/-- Empty-queue storage facts at a post-transaction state, in the exact shapes of
`Blanc.Lift.ConsolidationRequest.processCheckedSystemTransaction_consolidationRequest_empty`:
slots 3 and 2 read zero, slots 0 and 1 read zero after the pointer reset, and the
transaction-original values of slots 0-3 are zero. -/
def EmptyQueueAt (benvTxs : Benv) : Prop :=
  (Blanc.Lift.ConsolidationRequest.systemBase benvTxs).getStorVal
      (Blanc.Lift.ConsolidationRequest.systemSevm benvTxs).currentTarget 3 = 0 ∧
  (Blanc.afterSload (Blanc.Lift.ConsolidationRequest.systemSevm benvTxs)
      (Blanc.Lift.ConsolidationRequest.systemBase benvTxs) 3).getStorVal
      (Blanc.Lift.ConsolidationRequest.systemSevm benvTxs).currentTarget 2 = 0 ∧
  (Blanc.Lift.ConsolidationRequest.setupBase
      (Blanc.Lift.ConsolidationRequest.systemSevm benvTxs)
      (Blanc.Lift.ConsolidationRequest.systemBase benvTxs)).getStorVal
      (Blanc.Lift.ConsolidationRequest.systemSevm benvTxs).currentTarget 0 = 0 ∧
  (Blanc.Lift.ConsolidationRequest.setupBase
      (Blanc.Lift.ConsolidationRequest.systemSevm benvTxs)
      (Blanc.Lift.ConsolidationRequest.systemBase benvTxs)).getStorVal
      (Blanc.Lift.ConsolidationRequest.systemSevm benvTxs).currentTarget 1 = 0 ∧
  getOrigStorVal (Blanc.Lift.ConsolidationRequest.systemSevm benvTxs)
      (Blanc.Lift.ConsolidationRequest.systemSevm benvTxs).currentTarget 0 = 0 ∧
  getOrigStorVal (Blanc.Lift.ConsolidationRequest.systemSevm benvTxs)
      (Blanc.Lift.ConsolidationRequest.systemSevm benvTxs).currentTarget 1 = 0 ∧
  getOrigStorVal (Blanc.Lift.ConsolidationRequest.systemSevm benvTxs)
      (Blanc.Lift.ConsolidationRequest.systemSevm benvTxs).currentTarget 2 = 0 ∧
  getOrigStorVal (Blanc.Lift.ConsolidationRequest.systemSevm benvTxs)
      (Blanc.Lift.ConsolidationRequest.systemSevm benvTxs).currentTarget 3 = 0

/-- The 7002 checked system call from installed canonical code, via
`Blanc.Lift.WithdrawalRequest.checked_system_totality`. -/
theorem checkedW_of_installed (benvTxs : Benv) (fork : CoveredFork benvTxs.stat.fork)
    (installed : benvTxs.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode) :
    ∃ stW outW, processCheckedSystemTransaction benvTxs withdrawalRequestPredeployAddress [] =
      .ok (stW, outW) := by
  obtain ⟨h, -, -, -, -, -⟩ :=
    Blanc.Lift.WithdrawalRequest.checked_system_totality fork installed
  exact ⟨_, _, h⟩

/-- The 7251 checked system call from installed code and the empty-queue facts, via
`Blanc.Lift.ConsolidationRequest.processCheckedSystemTransaction_consolidationRequest_empty`. -/
theorem checkedC_of_emptyQueue (benvTxs : Benv) (fork : CoveredFork benvTxs.stat.fork)
    (installed : benvTxs.state.getCode consolidationRequestPredeployAddress =
      Blanc.consolidationRequestCode)
    (hempty : EmptyQueueAt benvTxs) :
    ∃ stC outC, processCheckedSystemTransaction benvTxs consolidationRequestPredeployAddress [] =
      .ok (stC, outC) := by
  obtain ⟨hs3, hs2, hs0b, hs1b, horig0, horig1, horig2, horig3⟩ := hempty
  obtain ⟨h, -, -, -⟩ :=
    Blanc.Lift.ConsolidationRequest.processCheckedSystemTransaction_consolidationRequest_empty
      fork installed hs3 hs2 hs0b hs1b horig0 horig1 horig2 horig3
  exact ⟨_, _, h⟩

/-! ## Preservation through settlement and the 7251 system call -/

/-- Settlement credits preserve every account's code, via shared
`State.addBal_getCode`. -/
theorem settledState_getCode (post : Devm) (E coinbase a : Adr) (refund tip : B256) :
    (settledState post E coinbase refund tip).getCode a = post.state.getCode a := by
  unfold settledState
  rw [State.addBal_getCode, State.addBal_getCode]

/-- Settlement credits preserve every account's storage map: `addBal` is a `setBal`,
whose storage projection is shared `State.setBal_get_stor`. -/
theorem settledState_getStor (post : Devm) (E coinbase a : Adr) (refund tip : B256) :
    (settledState post E coinbase refund tip).getStor a = post.state.getStor a := by
  simp only [settledState, State.getStor, State.addBal, State.setBal_get_stor]

/-- `setStorVal` preserves every account's code, via shared
`Blanc.State.setStorVal_balCodeEq` (same shape as the two existing private
copies; hoist candidate at the closure pass). -/
theorem setStorVal_getCode_local (w : State) (owner a : Adr) (key value : B256) :
    (w.setStorVal owner key value).getCode a = w.getCode a := by
  unfold State.getCode
  have h := congrFun (Blanc.State.setStorVal_balCodeEq w owner key value) a
  exact (congrArg Prod.snd h).symm

/-- Block C's settled state keeps every installed code: its frame already does
(`TxCPost`'s code leg). -/
theorem TxCPost_settled_codes {benv : Benv} {σ : Blanc.WithdrawalRequest.State}
    {iters : Nat} {post : Devm} (hQ : TxCPost benv σ iters post)
    (E coinbase a : Adr) (refund tip : B256) :
    (settledState post E coinbase refund tip).getCode a = benv.state.getCode a := by
  rw [settledState_getCode]
  exact hQ.2.2.2.1 a

/-- Block C's settled state keeps the 7251 storage map: its frame keeps every
non-predeploy map (`TxCPost`'s storage leg). -/
theorem TxCPost_settled_stor7251 {benv : Benv} {σ : Blanc.WithdrawalRequest.State}
    {iters : Nat} {post : Devm} (hQ : TxCPost benv σ iters post)
    (hne : consolidationRequestPredeployAddress ≠ withdrawalRequestPredeployAddress)
    (E coinbase : Adr) (refund tip : B256) :
    (settledState post E coinbase refund tip).getStor
      consolidationRequestPredeployAddress =
      benv.state.getStor consolidationRequestPredeployAddress := by
  rw [settledState_getStor]
  exact hQ.2.2.1 consolidationRequestPredeployAddress hne

/-- Block B's settled state keeps the 7002 code: its frame says so directly. -/
theorem TxBPost_settled_7002code {benv : Benv} {σ0 : Blanc.WithdrawalRequest.State}
    {post : Devm} (hQ : TxBPost benv σ0 post)
    (E coinbase : Adr) (refund tip : B256) :
    (settledState post E coinbase refund tip).getCode
      withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode := by
  rw [settledState_getCode]
  exact hQ.1

/-- Block B's settled state keeps any other account's code: its frame keeps the
whole account (`TxBPost`'s others leg). -/
theorem TxBPost_settled_otherCode {benv : Benv} {σ0 : Blanc.WithdrawalRequest.State}
    {post : Devm} (hQ : TxBPost benv σ0 post)
    (a : Adr) (hE : a ≠ senderE) (hL : a ≠ looperAddress)
    (hP : a ≠ withdrawalRequestPredeployAddress)
    (E coinbase : Adr) (refund tip : B256) :
    (settledState post E coinbase refund tip).getCode a = benv.state.getCode a := by
  have hget := hQ.2.2.2.2.2.2 a hE hL hP
  rw [settledState_getCode]
  exact congrArg (·.code) hget

/-- Block B's settled state keeps the 7251 storage map, by the same others leg. -/
theorem TxBPost_settled_stor7251 {benv : Benv} {σ0 : Blanc.WithdrawalRequest.State}
    {post : Devm} (hQ : TxBPost benv σ0 post)
    (hE : consolidationRequestPredeployAddress ≠ senderE)
    (hL : consolidationRequestPredeployAddress ≠ looperAddress)
    (hP : consolidationRequestPredeployAddress ≠ withdrawalRequestPredeployAddress)
    (E coinbase : Adr) (refund tip : B256) :
    (settledState post E coinbase refund tip).getStor
      consolidationRequestPredeployAddress =
      benv.state.getStor consolidationRequestPredeployAddress := by
  have hget := hQ.2.2.2.2.2.2 consolidationRequestPredeployAddress hE hL hP
  rw [settledState_getStor]
  exact congrArg (·.stor) hget

/-- The 7251 empty-queue system call preserves every account's code: its post
state writes only slots 0-3 of its own target (`systemPost_facts`). -/
theorem systemC_post_getCode (benvTxs : Benv) (hempty : EmptyQueueAt benvTxs) (a : Adr) :
    (Blanc.Lift.ConsolidationRequest.systemPost benvTxs).state.getCode a =
      benvTxs.state.getCode a := by
  obtain ⟨hs3, hs2, hs0b, hs1b, horig0, horig1, horig2, horig3⟩ := hempty
  have hfacts := Blanc.Lift.ConsolidationRequest.systemPost_facts benvTxs
    hs3 hs2 hs0b hs1b horig0 horig1 horig2 horig3
  rw [hfacts.2.2.2]
  rw [setStorVal_getCode_local, setStorVal_getCode_local,
    setStorVal_getCode_local, setStorVal_getCode_local]

/-- The 7251 empty-queue system call preserves every other account's storage map,
via shared `Blanc.State.get_setStorVal_ne`. -/
theorem systemC_post_getStor_other (benvTxs : Benv) (hempty : EmptyQueueAt benvTxs)
    (a : Adr) (hne : a ≠ consolidationRequestPredeployAddress) :
    (Blanc.Lift.ConsolidationRequest.systemPost benvTxs).state.getStor a =
      benvTxs.state.getStor a := by
  obtain ⟨hs3, hs2, hs0b, hs1b, horig0, horig1, horig2, horig3⟩ := hempty
  have hfacts := Blanc.Lift.ConsolidationRequest.systemPost_facts benvTxs
    hs3 hs2 hs0b hs1b horig0 horig1 horig2 horig3
  have htarg := (Blanc.Lift.ConsolidationRequest.system_seed benvTxs).2.1
  have h : (Blanc.Lift.ConsolidationRequest.systemSevm benvTxs).currentTarget ≠ a := by
    rw [htarg]
    exact Ne.symm hne
  rw [hfacts.2.2.2]
  simp only [State.getStor, Blanc.State.get_setStorVal_ne _ _ _ h]

/-! ## Preservation through the 7002 system call -/

/-- `St` preserves every account's code: it only replaces the machine. -/
theorem St_getCode_local (b : Devm) (S : List B256) (M : Mem) (G : Nat) (address : Adr) :
    (Blanc.Lift.St b S M G).getCode address = b.getCode address := by
  simp only [Blanc.Lift.St, Devm.getCode_state, Devm.setMach_state]

/-- `returnPost` preserves every account's code: it only replaces machine,
memory window and output. -/
theorem returnPost_getCode_local (d : Devm) (i sz : B256) (S : List B256) (address : Adr) :
    (Blanc.Lift.returnPost d i sz S).getCode address = d.getCode address := by
  have hstate : (Blanc.Lift.returnPost d i sz S).state = d.state := by
    simp only [Blanc.Lift.returnPost, Devm.withOutput_state, Devm.memRead_state,
      Devm.setMach_state]
  simp only [Devm.getCode_state, hstate]

/-- One queue-loop body preserves every account's code: three `SLOAD`s. -/
theorem systemBodyBase_getCode_local (sevm : Sevm) (base : Devm) (head index : B256)
    (address : Adr) :
    (Blanc.Lift.WithdrawalRequest.systemBodyBase sevm base head index).getCode address =
      base.getCode address := by
  simp only [Blanc.Lift.WithdrawalRequest.systemBodyBase,
    Blanc.Lift.WithdrawalRequest.systemBodyBase2,
    Blanc.Lift.WithdrawalRequest.systemBodyBase1, Blanc.afterSload_getCode]

/-- The queue loop preserves every account's code, mirroring `systemLoopFold_storage`. -/
theorem systemLoopFold_getCode_local (sevm : Sevm) (head : B256) (index remaining : Nat)
    (base : Devm) (memory : Mem) (address : Adr) :
    (Blanc.Lift.WithdrawalRequest.systemLoopFold sevm head index remaining base
      memory).base.getCode address = base.getCode address := by
  induction remaining generalizing index base memory with
  | zero => rfl
  | succ remaining ih =>
    simp only [Blanc.Lift.WithdrawalRequest.systemLoopFold]
    rw [ih, systemBodyBase_getCode_local]

/-- Queue setup preserves every account's code: two `SLOAD`s. -/
theorem systemSetupBase_getCode_local (sevm : Sevm) (base : Devm) (address : Adr) :
    (Blanc.Lift.WithdrawalRequest.systemSetupBase sevm base).getCode address =
      base.getCode address := by
  simp only [Blanc.Lift.WithdrawalRequest.systemSetupBase, Blanc.afterSload_getCode]

/-- The whole queue segment preserves every account's code, mirroring
`systemQueuePost_storage`. -/
theorem systemQueuePost_getCode_local (sevm : Sevm) (base : Devm) (memory : Mem)
    (address : Adr) :
    (Blanc.Lift.WithdrawalRequest.systemQueuePost sevm base memory).base.getCode address =
      base.getCode address := by
  rw [Blanc.Lift.WithdrawalRequest.systemQueuePost, systemLoopFold_getCode_local,
    systemSetupBase_getCode_local]

/-- The whole 7002 system frame preserves every account's code: every layer is
an `SLOAD`, an `SSTORE`, `RETURN` or a machine update. Mirrors
`systemFramePost_other_storage`, with no side condition since stores never touch
code. -/
theorem systemFramePost_getCode_local (sevm : Sevm) (base : Devm) (memory : Mem)
    (gas : Nat) (address : Adr) :
    (Blanc.Lift.WithdrawalRequest.systemFramePost sevm base memory gas).getCode address =
      base.getCode address := by
  rw [Blanc.Lift.WithdrawalRequest.systemFramePost,
    Blanc.Lift.WithdrawalRequest.systemBookkeepingPost,
    returnPost_getCode_local, St_getCode_local]
  simp only [Blanc.Lift.WithdrawalRequest.systemBookkeepingBase,
    Blanc.Lift.WithdrawalRequest.systemExcessStore,
    Blanc.Lift.WithdrawalRequest.systemCountRead,
    Blanc.Lift.WithdrawalRequest.systemExcessRead,
    Blanc.afterSstore_getCode, Blanc.afterSload_getCode]
  unfold Blanc.Lift.WithdrawalRequest.systemFramePointers
    Blanc.Lift.WithdrawalRequest.systemPointerBase
  split
  · simp only [Blanc.afterSstore_getCode, systemQueuePost_getCode_local]
  · simp only [Blanc.afterSstore_getCode, systemQueuePost_getCode_local]

/-- The 7002 checked system call preserves every account's code. -/
theorem systemW_post_getCode (benvTxs : Benv) (address : Adr) :
    (Blanc.Lift.WithdrawalRequest.systemProtocolPost benvTxs).state.getCode address =
      benvTxs.state.getCode address := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hstate, _, _, _, _, _⟩ :=
    Blanc.Lift.WithdrawalRequest.systemProtocol_seed benvTxs
  unfold Blanc.Lift.WithdrawalRequest.systemProtocolPost
  rw [← Devm.getCode_state, systemFramePost_getCode_local, Devm.getCode_state, hstate]

/-- The 7002 checked system call preserves every other account's storage map, via
shared `systemFramePost_other_storage`. -/
theorem systemW_post_getStor_other (benvTxs : Benv) (address : Adr)
    (hne : address ≠ withdrawalRequestPredeployAddress) :
    (Blanc.Lift.WithdrawalRequest.systemProtocolPost benvTxs).state.getStor address =
      benvTxs.state.getStor address := by
  obtain ⟨_, htarg, _, _, _, _, _, _, _, _, _, hstate, _, _, _, _, _⟩ :=
    Blanc.Lift.WithdrawalRequest.systemProtocol_seed benvTxs
  have hother : (Blanc.Lift.WithdrawalRequest.systemProtocolSevm benvTxs).currentTarget ≠
      address := by
    rw [htarg]
    exact Ne.symm hne
  have h := Blanc.Lift.WithdrawalRequest.systemFramePost_other_storage
    (Blanc.Lift.WithdrawalRequest.systemProtocolSevm benvTxs)
    (Blanc.Lift.WithdrawalRequest.systemProtocolBase benvTxs) .empty
    (systemTransactionGas - Blanc.Lift.WithdrawalRequest.systemProtocolGas benvTxs)
    address hother
  unfold Blanc.Lift.WithdrawalRequest.systemProtocolPost
  simp only [Devm.getStor, Devm.getAcct, State.getStor] at h ⊢
  rw [hstate] at h
  exact h

/-- The beacon-roots system call preserves an untouched account's code. -/
theorem stBeacon_getCode_of_ne {benv : Benv} (hfork : CoveredFork benv.stat.fork)
    (hcode : benv.state.getCode beaconRootsAddress = beaconRootsCode)
    (a : Adr) (hne : beaconRootsAddress ≠ a) :
    (stBeacon benv).getCode a = benv.state.getCode a := by
  have h := (stBeacon_step hfork hcode).2 a hne
  exact congrArg (·.code) h

/-- The beacon-roots system call preserves an untouched account's storage map. -/
theorem stBeacon_getStor_of_ne {benv : Benv} (hfork : CoveredFork benv.stat.fork)
    (hcode : benv.state.getCode beaconRootsAddress = beaconRootsCode)
    (a : Adr) (hne : beaconRootsAddress ≠ a) :
    (stBeacon benv).getStor a = benv.state.getStor a := by
  have h := (stBeacon_step hfork hcode).2 a hne
  exact congrArg (·.stor) h

/-- The history-storage system call preserves an untouched account's code, via
the chained `stHistory_get`. -/
theorem stHistory_getCode_of_ne {benv : Benv} {lastHash : B256}
    (hfork : CoveredFork benv.stat.fork)
    (hbeaconCode : benv.state.getCode beaconRootsAddress = beaconRootsCode)
    (hhistoryCode : benv.state.getCode historyStorageAddress = historyStorageCode)
    (hlast : benv.stat.blockHashes.getLast? = some lastHash)
    (a : Adr) (hneB : beaconRootsAddress ≠ a) (hneH : historyStorageAddress ≠ a) :
    (stHistory benv).getCode a = benv.state.getCode a := by
  have h := stHistory_get hfork hbeaconCode hhistoryCode hlast hneB hneH
  exact congrArg (·.code) h

/-- The history-storage system call preserves an untouched account's storage map. -/
theorem stHistory_getStor_of_ne {benv : Benv} {lastHash : B256}
    (hfork : CoveredFork benv.stat.fork)
    (hbeaconCode : benv.state.getCode beaconRootsAddress = beaconRootsCode)
    (hhistoryCode : benv.state.getCode historyStorageAddress = historyStorageCode)
    (hlast : benv.stat.blockHashes.getLast? = some lastHash)
    (a : Adr) (hneB : beaconRootsAddress ≠ a) (hneH : historyStorageAddress ≠ a) :
    (stHistory benv).getStor a = benv.state.getStor a := by
  have h := stHistory_get hfork hbeaconCode hhistoryCode hlast hneB hneH
  exact congrArg (·.stor) h

/-! ## Block C -/

/-- **Block C's body.** The two unchecked system calls are discharged via
`BeaconRoots.processUncheckedSystemTransaction_beaconRoots` and
`HistoryStorage.processUncheckedSystemTransaction_historyStorage`; the transaction
is `txC_processTransaction`. -/
theorem blockC_body {benv : Benv} {iters : Nat} {out : B256}
    {σ : Blanc.WithdrawalRequest.State} {lastHash : B256}
    (hfork : CoveredFork benv.stat.fork)
    (installed : SystemCodeInstalled benv.state)
    (hlast : benv.stat.blockHashes.getLast? = some lastHash)
    -- the transaction's premises, on the block's pre-state
    (hchain : benv.stat.chainId = 1)
    (hbase : benv.stat.baseFeePerGas ≤ 8)
    (hroom : 2 ^ 20 ≤ benv.stat.blockGasLimit)
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
    (hiters : iters ≤ 10000)
    -- the 7251 request call, on whatever the transaction leaves: installed
    -- canonical code plus the empty-queue facts (carried as state facts, not
    -- opaque existentials). The 7002 code is derived in the proof.
    (hCcode : ∀ benvTxs : Benv,
      benvTxs.state.getCode consolidationRequestPredeployAddress = Blanc.consolidationRequestCode)
    (hCempty : ∀ benvTxs : Benv, EmptyQueueAt benvTxs) :
    ∃ (post : Devm) (boutTxs : BlockOutput) (stW stC : State) (outW outC : MsgCallOutput),
      TxCPost (benv.withState (stHistory benv)) σ iters post ∧
      applyBody benv [Sum.inr txC] [] =
        .ok (stC, requestsOutput boutTxs outW.returnData outC.returnData) ∧
      processCheckedSystemTransaction
        (((benv.withState (stBeacon benv)).withState (stHistory benv)).withState
          (settledState post senderE benv.stat.coinbase
            ((txC.gas - txGasUsed txC.gas 23000 post.gasLeft post.refundCounter.toNat) *
              (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256
            (txGasUsed txC.gas 23000 post.gasLeft post.refundCounter.toNat *
              (min 1 (8 - benv.stat.baseFeePerGas))).toB256))
        withdrawalRequestPredeployAddress [] = .ok (stW, outW) ∧
      processCheckedSystemTransaction
        ((((benv.withState (stBeacon benv)).withState (stHistory benv)).withState
          (settledState post senderE benv.stat.coinbase
            ((txC.gas - txGasUsed txC.gas 23000 post.gasLeft post.refundCounter.toNat) *
              (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256
            (txGasUsed txC.gas 23000 post.gasLeft post.refundCounter.toNat *
              (min 1 (8 - benv.stat.baseFeePerGas))).toB256)).withState stW)
        consolidationRequestPredeployAddress [] = .ok (stC, outC) := by
  have hbeaconCode := systemCodeInstalled_beaconRoots installed
  have hhistoryCode := systemCodeInstalled_historyStorage installed
  obtain ⟨hbeacon, -⟩ := stBeacon_step hfork hbeaconCode
  obtain ⟨hhistory, -⟩ := stHistory_step hfork hbeaconCode hhistoryCode hlast
  have hsender : (stHistory benv).get senderE = benv.state.get senderE :=
    stHistory_get_of_installed hfork installed hlast (by decide) (by decide)
  have hpredeploy : (stHistory benv).get withdrawalRequestPredeployAddress =
      benv.state.get withdrawalRequestPredeployAddress :=
    stHistory_get_of_installed hfork installed hlast (by decide) (by decide)
  have hnonce' : ((stHistory benv).get senderE).nonce = 1 := by
    rw [hsender]; exact hnonce
  have hnocode' : ((stHistory benv).get senderE).code.isEmpty = true := by
    rw [hsender]; exact hnocode
  have hfunds' : 2 ^ 20 * 8 + 2 ^ 245 ≤ ((stHistory benv).get senderE).bal.toNat := by
    rw [hsender]; exact hfunds
  have hcode' : (stHistory benv).getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode := by
    change ((stHistory benv).get _).code = _
    rw [hpredeploy]
    exact hcode
  have hrep' : Blanc.WithdrawalRequest.RepresentsStorage
      ((stHistory benv).getStor withdrawalRequestPredeployAddress).get σ := by
    change Blanc.WithdrawalRequest.RepresentsStorage ((stHistory benv).get _).stor.get σ
    rw [hpredeploy]
    exact hrep
  set benvTx : Benv := (benv.withState (stBeacon benv)).withState (stHistory benv) with hbenvTx
  have hrecover : recoverSender benv.stat.chainId txC = .ok senderE := by
    rw [hchain]
    exact txC_recoveredSender
  obtain ⟨post, bout', hQ, hproc, -, -, hkeys, hreceipt⟩ := txC_processTransaction
    (benv := benv.withState (stHistory benv)) (bout := BlockOutput.init) (index := 0)
    hfork hchain hbase (by show 2 ^ 20 ≤ benv.stat.blockGasLimit - 0; exact hroom) hrecover
    hnonce' hnocode' hfunds' hcode' hrep' hbounds hexcess hrun hpaid hiters
  have hdeposit : parseDepositRequests bout' = .ok [] :=
    parseDepositRequests_of_predeploy_logs hkeys hreceipt (by
      rw [hQ.2.1]
      intro log hlog
      rw [List.mem_singleton] at hlog
      rw [hlog])
  have hproc' : processTransaction benvTx BlockOutput.init txC 0 = .ok
      (settledState post senderE benv.stat.coinbase
        ((txC.gas - txGasUsed txC.gas 23000 post.gasLeft post.refundCounter.toNat) *
          (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256
        (txGasUsed txC.gas 23000 post.gasLeft post.refundCounter.toNat *
          (min 1 (8 - benv.stat.baseFeePerGas))).toB256, bout') := by
    have hdel := hQ.2.2.2.2.1
    rw [settled_of_no_deletions post senderE _ _ _ hdel] at hproc
    exact hproc
  set settledTx : State := settledState post senderE benv.stat.coinbase
      ((txC.gas - txGasUsed txC.gas 23000 post.gasLeft post.refundCounter.toNat) *
        (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256
      (txGasUsed txC.gas 23000 post.gasLeft post.refundCounter.toNat *
        (min 1 (8 - benv.stat.baseFeePerGas))).toB256 with hsettledTx
  have hWcodeAt : (benvTx.withState settledTx).state.getCode
      withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode := by
    have h1 := hQ.2.2.2.1 withdrawalRequestPredeployAddress
    have h2 : (stHistory benv).getCode withdrawalRequestPredeployAddress =
        benv.state.getCode withdrawalRequestPredeployAddress :=
      stHistory_getCode_of_ne hfork hbeaconCode hhistoryCode hlast _
        (by decide) (by decide)
    have h3 : ((benv.withState (stHistory benv)).state).getCode
        withdrawalRequestPredeployAddress =
        (stHistory benv).getCode withdrawalRequestPredeployAddress := rfl
    have h4 : ((benvTx.withState settledTx).state).getCode
        withdrawalRequestPredeployAddress =
        settledTx.getCode withdrawalRequestPredeployAddress := rfl
    rw [h4, hsettledTx, settledState_getCode, h1, h3]
    exact h2.trans hcode
  obtain ⟨stW, outW, hWrun⟩ := checkedW_of_installed (benvTx.withState settledTx)
    hfork hWcodeAt
  obtain ⟨stC, outC, hCrun⟩ := checkedC_of_emptyQueue
    ((benvTx.withState settledTx).withState stW) hfork (hCcode _) (hCempty _)
  refine ⟨post, bout', stW, stC, outW, outC, hQ, ?_, hWrun, hCrun⟩
  exact applyBody_forward hfork hbeacon hlast hhistory (decode_single txC)
    (by rw [putIndex_single]; exact applyTransactions_single hproc') hdeposit hWrun hCrun

/-! ## Block B -/

/-- **Block B's body.** The two unchecked system calls are discharged via
`BeaconRoots.processUncheckedSystemTransaction_beaconRoots` and
`HistoryStorage.processUncheckedSystemTransaction_historyStorage`; the flood
frame schedules no deletions (`TxBPost.no_deletions`), settling to `settledState`. -/
theorem blockB_body {benv : Benv} {σ0 : Blanc.WithdrawalRequest.State} {lastHash : B256}
    (hfork : CoveredFork benv.stat.fork)
    (installed : SystemCodeInstalled benv.state)
    (hlast : benv.stat.blockHashes.getLast? = some lastHash)
    (hnocap : benv.stat.rules.tx.maxGas = none)
    (hchain : benv.stat.chainId = 1)
    (hbase : benv.stat.baseFeePerGas ≤ 8)
    (hroom : 2 ^ 28 ≤ benv.stat.blockGasLimit)
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
        (Blanc.WithdrawalRequest.queueSlot n o) = 0)
    (hCcode : ∀ benvTxs : Benv,
      benvTxs.state.getCode consolidationRequestPredeployAddress = Blanc.consolidationRequestCode)
    (hCempty : ∀ benvTxs : Benv, EmptyQueueAt benvTxs) :
    ∃ (post : Devm) (boutTxs : BlockOutput) (stW stC : State) (outW outC : MsgCallOutput),
      TxBPost (benv.withState (stHistory benv)) σ0 post ∧
      applyBody benv [Sum.inr txB] [] =
        .ok (stC, requestsOutput boutTxs outW.returnData outC.returnData) ∧
      processCheckedSystemTransaction
        (((benv.withState (stBeacon benv)).withState (stHistory benv)).withState
          (settledState post senderE benv.stat.coinbase
            ((txB.gas - txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat) *
              (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256
            (txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat *
              (min 1 (8 - benv.stat.baseFeePerGas))).toB256))
        withdrawalRequestPredeployAddress [] = .ok (stW, outW) ∧
      processCheckedSystemTransaction
        ((((benv.withState (stBeacon benv)).withState (stHistory benv)).withState
          (settledState post senderE benv.stat.coinbase
            ((txB.gas - txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat) *
              (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256
            (txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat *
              (min 1 (8 - benv.stat.baseFeePerGas))).toB256)).withState stW)
        consolidationRequestPredeployAddress [] = .ok (stC, outC) := by
  have hbeaconCode := systemCodeInstalled_beaconRoots installed
  have hhistoryCode := systemCodeInstalled_historyStorage installed
  obtain ⟨hbeacon, -⟩ := stBeacon_step hfork hbeaconCode
  obtain ⟨hhistory, -⟩ := stHistory_step hfork hbeaconCode hhistoryCode hlast
  have hsender : (stHistory benv).get senderE = benv.state.get senderE :=
    stHistory_get_of_installed hfork installed hlast (by decide) (by decide)
  have hlooper : (stHistory benv).get looperAddress = benv.state.get looperAddress :=
    stHistory_get_of_installed hfork installed hlast (by decide) (by decide)
  have hpredeploy : (stHistory benv).get withdrawalRequestPredeployAddress =
      benv.state.get withdrawalRequestPredeployAddress :=
    stHistory_get_of_installed hfork installed hlast (by decide) (by decide)
  have hnonce' : ((stHistory benv).get senderE).nonce = 0 := by
    rw [hsender]; exact hnonce
  have hnocode' : ((stHistory benv).get senderE).code.isEmpty = true := by
    rw [hsender]; exact hnocode
  have hfunds' : 2 ^ 28 * 8 + 2895 ≤ ((stHistory benv).get senderE).bal.toNat := by
    rw [hsender]; exact hfunds
  have hLcode' : (stHistory benv).getCode looperAddress = Blanc.Lift.FloodLooper.code := by
    change ((stHistory benv).get _).code = _
    rw [hlooper]
    exact hLcode
  have hLbal' : ((stHistory benv).bal looperAddress).toNat + 2895 < 2 ^ 256 := by
    change ((stHistory benv).get _).bal.toNat + 2895 < 2 ^ 256
    rw [hlooper]
    exact hLbal
  have hcode' : (stHistory benv).getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode := by
    change ((stHistory benv).get _).code = _
    rw [hpredeploy]
    exact hcode
  have hrep' : Blanc.WithdrawalRequest.RepresentsStorage
      ((stHistory benv).getStor withdrawalRequestPredeployAddress).get σ0 := by
    change Blanc.WithdrawalRequest.RepresentsStorage ((stHistory benv).get _).stor.get σ0
    rw [hpredeploy]
    exact hrep
  have hqueue' : ∀ n o, σ0.tail ≤ n → n < σ0.tail + 2895 → o ≤ 2 →
      ((stHistory benv).getStor withdrawalRequestPredeployAddress).get
        (Blanc.WithdrawalRequest.queueSlot n o) = 0 := by
    intro n o hn htail ho
    change ((stHistory benv).get _).stor.get _ = 0
    rw [hpredeploy]
    exact hqueue n o hn htail ho
  set benvTx : Benv := (benv.withState (stBeacon benv)).withState (stHistory benv) with hbenvTx
  have hrecover : recoverSender benv.stat.chainId txB = .ok senderE := by
    rw [hchain]
    exact txB_recoveredSender
  obtain ⟨post, bout', hQ, hproc, -, -, hkeys, hreceipt⟩ := txB_processTransaction
    (benv := benv.withState (stHistory benv)) (bout := BlockOutput.init) (index := 0)
    hfork hnocap hchain hbase (by show 2 ^ 28 ≤ benv.stat.blockGasLimit - 0; exact hroom)
    hrecover hnonce' hnocode' hfunds' hLcode' hLbal' hcode' hrep' hexcess hcountLt htailLt hqueue'
  have hdeposit : parseDepositRequests bout' = .ok [] :=
    parseDepositRequests_of_predeploy_logs hkeys hreceipt (by
      rw [hQ.2.2.1]
      intro log hlog
      rw [(List.mem_replicate.mp hlog).2])
  have hproc' : processTransaction benvTx BlockOutput.init txB 0 = .ok
      (settledState post senderE benv.stat.coinbase
        ((txB.gas - txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat) *
          (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256
        (txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat *
          (min 1 (8 - benv.stat.baseFeePerGas))).toB256, bout') := by
    rw [TxBPost.no_deletions hQ] at hproc
    exact hproc
  set settledTx : State := settledState post senderE benv.stat.coinbase
      ((txB.gas - txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat) *
        (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256
      (txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat *
        (min 1 (8 - benv.stat.baseFeePerGas))).toB256 with hsettledTx
  have hWcodeAt : (benvTx.withState settledTx).state.getCode
      withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode := by
    have h4 : ((benvTx.withState settledTx).state).getCode
        withdrawalRequestPredeployAddress =
        settledTx.getCode withdrawalRequestPredeployAddress := rfl
    rw [h4, hsettledTx, settledState_getCode]
    exact hQ.1
  obtain ⟨stW, outW, hWrun⟩ := checkedW_of_installed (benvTx.withState settledTx)
    hfork hWcodeAt
  obtain ⟨stC, outC, hCrun⟩ := checkedC_of_emptyQueue
    ((benvTx.withState settledTx).withState stW) hfork (hCcode _) (hCempty _)
  refine ⟨post, bout', stW, stC, outW, outC, hQ, ?_, hWrun, hCrun⟩
  exact applyBody_forward hfork hbeacon hlast hhistory (decode_single txB)
    (by rw [putIndex_single]; exact applyTransactions_single hproc') hdeposit hWrun hCrun

/-! ## From a body to a configured block trace -/

/-- A block without ommers or withdrawals whose header validates and commits to its
body's results is a configured block trace. -/
theorem blockTrace_of_body {cfg : ChainConfig} {pre : BlockChain} {block : Block}
    {fork : Fork} {st : State} {bout : BlockOutput}
    (hbound : sum pre.state.bal < 2 ^ 256) (hwds : block.wds = [])
    (hid : cfg.chainId = pre.chainId)
    (hforkAt : cfg.forkAt block.header.timestamp = .ok fork)
    (hcovered : CoveredFork fork)
    (hheader : validateHeader fork.ruleSet pre block.header = .ok ())
    (hommers : block.ommers = [])
    (hbody : applyBody (initBenv fork pre block.header) block.txs block.wds = .ok (st, bout))
    (hgasUsed : block.header.gasUsed = bout.blockGasUsed)
    (htxsRoot : block.header.txsRoot = getTransactionsRoot bout)
    (hstateRoot : block.header.stateRoot = st.root)
    (hreceiptRoot : block.header.receiptRoot = getReceiptRoot bout)
    (hbloom : block.header.bloom = logsBloom bout.blockLogs)
    (hwithdrawalsRoot : block.header.withdrawalsRoot = getWithdrawalsRoot bout)
    (hblobGasUsed : block.header.blobGasUsed = bout.blobGasUsed)
    (hrequestsHash : block.header.requestsHash = some (computeRequestsHash bout.requests)) :
    Nonempty (ConfiguredBlockTrace cfg pre ⟨appendBlock pre.blocks block, st, pre.chainId⟩) :=
  configuredBlockTrace_forward hbound hwds hforkAt hcovered
    (stateTransitionUsing_forward hid hforkAt hcovered hheader hommers hbody hgasUsed htxsRoot
      hstateRoot hreceiptRoot hbloom hwithdrawalsRoot hblobGasUsed hrequestsHash)

/-! ## The three-block history -/

/-- Three configured block traces from a valid checkpoint chain into a configured
history trace. -/
def history_of_three {cfg : ChainConfig} {checkpoint chainA chainB chainC : BlockChain}
    (hcfg : cfg.Valid) (hctx : checkpoint.ValidContext) (hid : cfg.chainId = checkpoint.chainId)
    (traceA : ConfiguredBlockTrace cfg checkpoint chainA)
    (traceB : ConfiguredBlockTrace cfg chainA chainB)
    (traceC : ConfiguredBlockTrace cfg chainB chainC) :
    ConfiguredHistoryTrace cfg checkpoint chainC :=
  .step (.step (.step (.refl hcfg hctx hid) traceA) traceB) traceC

/-! ## The statement -/

/-- **B, the mathematical-fee guarantee**, in the vocabulary of the retained word-fee
theorem: on every configured history under the original hypotheses, every committed
submission frame whose word fee loop ran to `output` and was paid at least `output / 17`
also paid at least the Nat reference fee `fakeExp 1 excess 17` of the model at its incoming
excess. -/
def NatFeeGuarantee : Prop :=
  ∀ (cfg : ChainConfig) (checkpoint future : BlockChain)
    (trace : ConfiguredHistoryTrace cfg checkpoint future),
    SystemCodeInstalled checkpoint.state →
    trace.NoSenderAt systemAddress → trace.NoAuthorityAt systemAddress →
    (∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ systemAddress) →
    checkpoint.state.getCode systemAddress = ByteArray.empty →
    Blanc.WithdrawalRequest.RepresentsStorage
      (checkpoint.state.getStor withdrawalRequestPredeployAddress).get
      Blanc.WithdrawalRequest.initial →
    ∀ frame ∈ trace.settledFrames.flatMap balanceFrameObservation,
      ∀ (model : Blanc.WithdrawalRequest.State) (iterations : Nat) (output : B256),
        submissionPaymentFrame frame →
        model.excess = ((frame.pre.getStor withdrawalRequestPredeployAddress).get 0).toNat →
        WordFakeExponential.Run ((frame.pre.getStor withdrawalRequestPredeployAddress).get 0)
          17 1 17 0 iterations output →
        (output / 17).toNat ≤ frame.sevm.value.toNat →
        Blanc.WithdrawalRequest.fee model ≤ frame.sevm.value.toNat

/-- **The refutation of B**: a configured history under the original hypotheses with a
committed submission frame that paid its executed word fee but less than the Nat fee. -/
def NatFeeGuaranteeRefuted : Prop :=
  ∃ (cfg : ChainConfig) (checkpoint future : BlockChain)
    (trace : ConfiguredHistoryTrace cfg checkpoint future),
    SystemCodeInstalled checkpoint.state ∧
    trace.NoSenderAt systemAddress ∧ trace.NoAuthorityAt systemAddress ∧
    (∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ systemAddress) ∧
    checkpoint.state.getCode systemAddress = ByteArray.empty ∧
    Blanc.WithdrawalRequest.RepresentsStorage
      (checkpoint.state.getStor withdrawalRequestPredeployAddress).get
      Blanc.WithdrawalRequest.initial ∧
    ∃ frame ∈ trace.settledFrames.flatMap balanceFrameObservation,
      ∃ (model : Blanc.WithdrawalRequest.State) (iterations : Nat) (output : B256),
        submissionPaymentFrame frame ∧
        model.excess = ((frame.pre.getStor withdrawalRequestPredeployAddress).get 0).toNat ∧
        WordFakeExponential.Run ((frame.pre.getStor withdrawalRequestPredeployAddress).get 0)
          17 1 17 0 iterations output ∧
        (output / 17).toNat ≤ frame.sevm.value.toNat ∧
        frame.sevm.value.toNat < Blanc.WithdrawalRequest.fee model

theorem not_natFeeGuarantee_of_refuted (h : NatFeeGuaranteeRefuted) : ¬ NatFeeGuarantee := by
  intro guarantee
  obtain ⟨cfg, checkpoint, future, trace, installed, senders, authorities, avoid, systemEmpty,
    init, frame, member, model, iterations, output, payment, excess, run, paid, below⟩ := h
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le below
    (guarantee cfg checkpoint future trace installed senders authorities avoid systemEmpty init
      frame member model iterations output payment excess run paid))

/-- The witness history's remaining inputs: the three-block configured history with the
original hypotheses, and block C's submission frame among its settled frames at excess
`2893` and value `2 ^ 245`. -/
structure RefutationWitness where
  cfg : ChainConfig
  checkpoint : BlockChain
  future : BlockChain
  trace : ConfiguredHistoryTrace cfg checkpoint future
  installed : SystemCodeInstalled checkpoint.state
  senders : trace.NoSenderAt systemAddress
  authorities : trace.NoAuthorityAt systemAddress
  avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
    root.sevm.currentTarget ≠ systemAddress
  systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty
  init : Blanc.WithdrawalRequest.RepresentsStorage
    (checkpoint.state.getStor withdrawalRequestPredeployAddress).get
    Blanc.WithdrawalRequest.initial
  frame : Exec.Frame
  member : frame ∈ trace.settledFrames.flatMap balanceFrameObservation
  payment : submissionPaymentFrame frame
  excess : (frame.pre.getStor withdrawalRequestPredeployAddress).get 0 = (2893 : Nat).toB256
  value : frame.sevm.value = (2 ^ 245 : Nat).toB256

/-- The Nat fee at excess `2893` (U2a's `fee_2893`). -/
def natFee2893 : Nat :=
  80668064690921409049190791237320678716946849613533250306370202067869504081

/-- The word fee loop's output at excess `2893` (U2a's `word_run_2893_existing`). -/
def wordOutput2893 : Nat :=
  545485220060489857066268109499810576327418688227975047986437738206577926843

/-- The executed word fee at excess `2893` (U2a's `word_run_2893_fee`). -/
def wordFee2893 : Nat :=
  32087365885911168062721653499988857431024628719292649881555161070975172167

/-- **B is refuted by the witness.**  The numeric inputs are stated in the shapes of
U2a's `NumericFacts` (`word_run_2893_existing`, `word_run_2893_fee`,
`word_fee_2893_le_two_pow_245`, `fee_2893`, `two_pow_245_lt_nat_fee_2893`) so they
discharge by citation once that module is merged. -/
theorem natFeeGuaranteeRefuted_of_witness (w : RefutationWitness)
    (word_run_2893_existing : WordFakeExponential.Run (2893 : Nat).toB256 (17 : Nat).toB256
      (1 : Nat).toB256 (17 : Nat).toB256 (0 : Nat).toB256 457 wordOutput2893.toB256)
    (word_run_2893_fee : (wordOutput2893.toB256 / (17 : Nat).toB256).toNat = wordFee2893)
    (word_fee_2893_le_two_pow_245 : wordFee2893 ≤ 2 ^ 245)
    (fee_2893 : ∀ {state : Blanc.WithdrawalRequest.State}, state.excess = 2893 →
      Blanc.WithdrawalRequest.fee state = natFee2893)
    (two_pow_245_lt_nat_fee_2893 : 2 ^ 245 < natFee2893) :
    NatFeeGuaranteeRefuted := by
  have h17 : (17 : Nat).toB256 = (17 : B256) := by decide
  have h1 : (1 : Nat).toB256 = (1 : B256) := by decide
  have h0 : (0 : Nat).toB256 = (0 : B256) := by decide
  have h2893 : ((2893 : Nat).toB256).toNat = 2893 := B256.toNat_toB256_of_lt (by decide)
  have h245 : ((2 ^ 245 : Nat).toB256).toNat = 2 ^ 245 := B256.toNat_toB256_of_lt (by decide)
  rw [h17, h1, h0] at word_run_2893_existing
  rw [h17] at word_run_2893_fee
  refine ⟨w.cfg, w.checkpoint, w.future, w.trace, w.installed, w.senders, w.authorities, w.avoid,
    w.systemEmpty, w.init, w.frame, w.member, ⟨2893, 0, 0, 0, []⟩, 457, wordOutput2893.toB256,
    w.payment, ?_, ?_, ?_, ?_⟩
  · rw [w.excess, h2893]
  · rw [w.excess]; exact word_run_2893_existing
  · rw [w.value, h245, word_run_2893_fee]; exact word_fee_2893_le_two_pow_245
  · rw [w.value, h245, fee_2893 rfl]; exact two_pow_245_lt_nat_fee_2893

/-- The witness from three configured block traces: per-block sender, authority and
creation-frame facts, and block C's submission frame. -/
def RefutationWitness.ofBlocks {cfg : ChainConfig} {checkpoint chainA chainB chainC : BlockChain}
    (hcfg : cfg.Valid) (hctx : checkpoint.ValidContext) (hid : cfg.chainId = checkpoint.chainId)
    (traceA : ConfiguredBlockTrace cfg checkpoint chainA)
    (traceB : ConfiguredBlockTrace cfg chainA chainB)
    (traceC : ConfiguredBlockTrace cfg chainB chainC)
    (installed : SystemCodeInstalled checkpoint.state)
    (sendersA : traceA.bodyTrace.transactions.NoSenderAt systemAddress)
    (sendersB : traceB.bodyTrace.transactions.NoSenderAt systemAddress)
    (sendersC : traceC.bodyTrace.transactions.NoSenderAt systemAddress)
    (authoritiesA : ∀ p ∈ traceA.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths,
      ∀ authority, recoverAuthority auth = .ok authority → authority ≠ systemAddress)
    (authoritiesB : ∀ p ∈ traceB.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths,
      ∀ authority, recoverAuthority auth = .ok authority → authority ≠ systemAddress)
    (authoritiesC : ∀ p ∈ traceC.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths,
      ∀ authority, recoverAuthority auth = .ok authority → authority ≠ systemAddress)
    (avoidA : ∀ root ∈ traceA.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ systemAddress)
    (avoidB : ∀ root ∈ traceB.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ systemAddress)
    (avoidC : ∀ root ∈ traceC.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ systemAddress)
    (systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty)
    (init : Blanc.WithdrawalRequest.RepresentsStorage
      (checkpoint.state.getStor withdrawalRequestPredeployAddress).get
      Blanc.WithdrawalRequest.initial)
    (frame : Exec.Frame)
    (memberC : frame ∈ traceC.settledFrames.flatMap balanceFrameObservation)
    (payment : submissionPaymentFrame frame)
    (excess : (frame.pre.getStor withdrawalRequestPredeployAddress).get 0 = (2893 : Nat).toB256)
    (value : frame.sevm.value = (2 ^ 245 : Nat).toB256) : RefutationWitness :=
  { cfg := cfg, checkpoint := checkpoint, future := chainC
    trace := history_of_three hcfg hctx hid traceA traceB traceC
    installed := installed
    senders := ⟨⟨⟨trivial, sendersA⟩, sendersB⟩, sendersC⟩
    authorities := ⟨⟨⟨trivial, authoritiesA⟩, authoritiesB⟩, authoritiesC⟩
    avoid := by
      intro root member
      simp only [history_of_three, ConfiguredHistoryTrace.rawFrames, List.nil_append,
        List.mem_append] at member
      rcases member with (hA | hB) | hC
      · exact avoidA root hA
      · exact avoidB root hB
      · exact avoidC root hC
    systemEmpty := systemEmpty
    init := init
    frame := frame
    member := by
      simp only [history_of_three, ConfiguredHistoryTrace.settledFrames, List.nil_append,
        List.flatMap_append]
      exact List.mem_append_right _ memberC
    payment := payment
    excess := excess
    value := value }

end Blanc.Lift.WithdrawalRequest.FeeCounterexample
