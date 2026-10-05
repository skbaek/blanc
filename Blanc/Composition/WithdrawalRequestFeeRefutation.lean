import Blanc.Composition.WithdrawalRequestFeeCounterexample
import Blanc.ExecutionTraceCallOnly
import Blanc.ExecutionTraceRootFrame
import Blanc.Lift.WithdrawalRequest.NumericFacts
import Blanc.Lift.WithdrawalRequest.SystemProtocol
import Blanc.Lift.ConsolidationRequest.SystemWalk
import Blanc.SystemCallForward
import Blanc.Lift.ExactWalkSolc
import Blanc.BlockForward

/-!
# The mathematical-fee refutation: the closed witness

Assembles the three-block witness history of
`Blanc/Composition/WithdrawalRequestFeeCounterexample.lean` with no hypotheses.
-/

namespace Blanc.Lift.WithdrawalRequest.FeeCounterexample

open Jaune Blanc.Lift Blanc.ExecutionTrace Blanc.BlockForward FloodTx FloodWalk

/-! ## Accounts other than the predeploy through the 7002 system frame -/

theorem systemBodyBase_getAcct_local (sevm : Sevm) (base : Devm) (head index : B256)
    (a : Adr) :
    (Blanc.Lift.WithdrawalRequest.systemBodyBase sevm base head index).getAcct a =
      base.getAcct a := by
  simp only [Blanc.Lift.WithdrawalRequest.systemBodyBase,
    Blanc.Lift.WithdrawalRequest.systemBodyBase2,
    Blanc.Lift.WithdrawalRequest.systemBodyBase1, afterSload_getAcct]

theorem systemLoopFold_getAcct_local (sevm : Sevm) (head : B256) (index remaining : Nat)
    (base : Devm) (memory : Mem) (a : Adr) :
    (Blanc.Lift.WithdrawalRequest.systemLoopFold sevm head index remaining base
      memory).base.getAcct a = base.getAcct a := by
  induction remaining generalizing index base memory with
  | zero => rfl
  | succ remaining ih =>
    simp only [Blanc.Lift.WithdrawalRequest.systemLoopFold]
    rw [ih, systemBodyBase_getAcct_local]

theorem systemQueuePost_getAcct_local (sevm : Sevm) (base : Devm) (memory : Mem) (a : Adr) :
    (Blanc.Lift.WithdrawalRequest.systemQueuePost sevm base memory).base.getAcct a =
      base.getAcct a := by
  rw [Blanc.Lift.WithdrawalRequest.systemQueuePost, systemLoopFold_getAcct_local]
  simp only [Blanc.Lift.WithdrawalRequest.systemSetupBase, afterSload_getAcct]

/-- The whole 7002 system frame keeps every account but its own. -/
theorem systemFramePost_getAcct_other (sevm : Sevm) (base : Devm) (memory : Mem)
    (gas : Nat) (a : Adr) (hne : sevm.currentTarget ≠ a) :
    (Blanc.Lift.WithdrawalRequest.systemFramePost sevm base memory gas).getAcct a =
      base.getAcct a := by
  have hret : ∀ (d : Devm) (i sz : B256) (S : List B256),
      (Blanc.Lift.returnPost d i sz S).getAcct a = d.getAcct a := by
    intro d i sz S
    simp only [Devm.getAcct, Blanc.Lift.returnPost, Devm.withOutput_state, Devm.memRead_state,
      Devm.setMach_state]
  have hSt : ∀ (d : Devm) (S : List B256) (M : Mem) (G : Nat),
      (Blanc.Lift.St d S M G).getAcct a = d.getAcct a := by
    intro d S M G
    simp only [Devm.getAcct, Blanc.Lift.St, Devm.setMach_state]
  rw [Blanc.Lift.WithdrawalRequest.systemFramePost,
    Blanc.Lift.WithdrawalRequest.systemBookkeepingPost, hret, hSt]
  simp only [Blanc.Lift.WithdrawalRequest.systemBookkeepingBase,
    Blanc.Lift.WithdrawalRequest.systemExcessStore,
    Blanc.Lift.WithdrawalRequest.systemCountRead,
    Blanc.Lift.WithdrawalRequest.systemExcessRead,
    afterSstore_getAcct_ne _ _ _ _ hne, afterSload_getAcct]
  unfold Blanc.Lift.WithdrawalRequest.systemFramePointers
    Blanc.Lift.WithdrawalRequest.systemPointerBase
  split
  · simp only [afterSstore_getAcct_ne _ _ _ _ hne, systemQueuePost_getAcct_local]
  · simp only [afterSstore_getAcct_ne _ _ _ _ hne, systemQueuePost_getAcct_local]

/-- The 7002 checked system call keeps every account but the predeploy. -/
theorem systemW_post_get_other (benv : Benv) (a : Adr)
    (hne : a ≠ withdrawalRequestPredeployAddress) :
    (Blanc.Lift.WithdrawalRequest.systemProtocolPost benv).state.get a = benv.state.get a := by
  have h := systemFramePost_getAcct_other
    (Blanc.Lift.WithdrawalRequest.systemProtocolSevm benv)
    (Blanc.Lift.WithdrawalRequest.systemProtocolBase benv) .empty
    (systemTransactionGas - Blanc.Lift.WithdrawalRequest.systemProtocolGas benv) a
    (Ne.symm hne)
  exact h

/-! ## The 7251 system call on an empty queue -/

/-- Slots 0-3 of the 7251 predeploy read zero. -/
def Slots7251Zero (w : State) : Prop :=
  (w.getStor consolidationRequestPredeployAddress).get 0 = 0 ∧
  (w.getStor consolidationRequestPredeployAddress).get 1 = 0 ∧
  (w.getStor consolidationRequestPredeployAddress).get 2 = 0 ∧
  (w.getStor consolidationRequestPredeployAddress).get 3 = 0

theorem slots7251Zero_of_getStor {w w' : State}
    (h : w'.getStor consolidationRequestPredeployAddress =
      w.getStor consolidationRequestPredeployAddress) (hz : Slots7251Zero w) :
    Slots7251Zero w' := by
  unfold Slots7251Zero
  rw [h]
  exact hz

/-- The 7251 system call's transaction-original storage is the storage it runs on: a system
call opens a fresh transaction context. -/
theorem systemC_original (b : Benv) (k : B256) :
    getOrigStorVal (Blanc.Lift.ConsolidationRequest.systemSevm b)
      (Blanc.Lift.ConsolidationRequest.systemSevm b).currentTarget k =
      (b.state.getStor consolidationRequestPredeployAddress).get k := rfl

/-- **The 7251 checked call on an empty queue**, from the four slot reads of the state it runs
on: it succeeds and writes zero into slots 0-3. -/
theorem checkedC_of_zero (b : Benv) (hfork : CoveredFork b.stat.fork)
    (hcode : b.state.getCode consolidationRequestPredeployAddress =
      Blanc.consolidationRequestCode)
    (hz : Slots7251Zero b.state) :
    processCheckedSystemTransaction b consolidationRequestPredeployAddress [] =
      .ok ((Blanc.Lift.ConsolidationRequest.systemPost b).state,
        systemCallOutput (Blanc.Lift.ConsolidationRequest.systemPost b)) ∧
    (Blanc.Lift.ConsolidationRequest.systemPost b).state =
      (((b.state.setStorVal consolidationRequestPredeployAddress 2 0).setStorVal
        consolidationRequestPredeployAddress 3 0).setStorVal
        consolidationRequestPredeployAddress 0 0).setStorVal
        consolidationRequestPredeployAddress 1 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := hz
  obtain ⟨_, htarg, _, _, _, _, _, _, _, _, _, hstate, _⟩ :=
    Blanc.Lift.ConsolidationRequest.system_seed b
  have hread : ∀ k : B256,
      (Blanc.Lift.ConsolidationRequest.systemBase b).getStorVal
        (Blanc.Lift.ConsolidationRequest.systemSevm b).currentTarget k =
        (b.state.getStor consolidationRequestPredeployAddress).get k := by
    intro k
    simp only [Devm.getStorVal, Devm.getAcct, State.getStor, htarg, hstate]
  have hs3 := (hread 3).trans h3
  have hs2 : (afterSload (Blanc.Lift.ConsolidationRequest.systemSevm b)
      (Blanc.Lift.ConsolidationRequest.systemBase b) 3).getStorVal
      (Blanc.Lift.ConsolidationRequest.systemSevm b).currentTarget 2 = 0 := by
    rw [getStorVal_afterSload]
    exact (hread 2).trans h2
  have hs0 : (Blanc.Lift.ConsolidationRequest.setupBase
      (Blanc.Lift.ConsolidationRequest.systemSevm b)
      (Blanc.Lift.ConsolidationRequest.systemBase b)).getStorVal
      (Blanc.Lift.ConsolidationRequest.systemSevm b).currentTarget 0 = 0 := by
    simp only [Blanc.Lift.ConsolidationRequest.setupBase, getStorVal_afterSload]
    exact (hread 0).trans h0
  have hs1 : (Blanc.Lift.ConsolidationRequest.setupBase
      (Blanc.Lift.ConsolidationRequest.systemSevm b)
      (Blanc.Lift.ConsolidationRequest.systemBase b)).getStorVal
      (Blanc.Lift.ConsolidationRequest.systemSevm b).currentTarget 1 = 0 := by
    simp only [Blanc.Lift.ConsolidationRequest.setupBase, getStorVal_afterSload]
    exact (hread 1).trans h1
  obtain ⟨hrun, -, -, hpost⟩ :=
    Blanc.Lift.ConsolidationRequest.processCheckedSystemTransaction_consolidationRequest_empty
      hfork hcode hs3 hs2 hs0 hs1
      ((systemC_original b 0).trans h0) ((systemC_original b 1).trans h1)
      ((systemC_original b 2).trans h2) ((systemC_original b 3).trans h3)
  refine ⟨hrun, ?_⟩
  rw [hpost, htarg]

theorem systemC_post_get_other (b : Benv) (hfork : CoveredFork b.stat.fork)
    (hcode : b.state.getCode consolidationRequestPredeployAddress =
      Blanc.consolidationRequestCode)
    (hz : Slots7251Zero b.state) (a : Adr) (hne : consolidationRequestPredeployAddress ≠ a) :
    (Blanc.Lift.ConsolidationRequest.systemPost b).state.get a = b.state.get a := by
  rw [(checkedC_of_zero b hfork hcode hz).2]
  simp only [Blanc.State.get_setStorVal_ne _ _ _ hne]

theorem systemC_post_zero (b : Benv) (hfork : CoveredFork b.stat.fork)
    (hcode : b.state.getCode consolidationRequestPredeployAddress =
      Blanc.consolidationRequestCode)
    (hz : Slots7251Zero b.state) :
    Slots7251Zero (Blanc.Lift.ConsolidationRequest.systemPost b).state := by
  rw [(checkedC_of_zero b hfork hcode hz).2]
  unfold Slots7251Zero
  simp only [State.getStor_setStorVal_self, Stor.get_set_self,
    Stor.get_set_ne _ (by decide : (1 : B256) ≠ 0),
    Stor.get_set_ne _ (by decide : (1 : B256) ≠ 2), Stor.get_set_ne _ (by decide : (0 : B256) ≠ 2),
    Stor.get_set_ne _ (by decide : (3 : B256) ≠ 2), Stor.get_set_ne _ (by decide : (1 : B256) ≠ 3),
    Stor.get_set_ne _ (by decide : (0 : B256) ≠ 3)]
  exact ⟨trivial, trivial, trivial, trivial⟩

/-! ## One body: system calls around a settled transaction state -/

/-- The environment a body's transactions run in: after the beacon-roots and history calls. -/
def benvH (benv : Benv) : Benv := (benv.withState (stBeacon benv)).withState (stHistory benv)

/-- The state after the 7002 system call. -/
def stW (b : Benv) : State := (Blanc.Lift.WithdrawalRequest.systemProtocolPost b).state

/-- The environment of the 7251 system call after the transactions settled at `s`. -/
def benvC (benv : Benv) (s : State) : Benv :=
  ((benvH benv).withState s).withState (stW ((benvH benv).withState s))

/-- The body's final state. -/
def bodyPost (benv : Benv) (s : State) : State :=
  (Blanc.Lift.ConsolidationRequest.systemPost (benvC benv s)).state

/-- The body's block output, from the transactions' output. -/
def bodyOut (benv : Benv) (s : State) (bout : BlockOutput) : BlockOutput :=
  requestsOutput bout
    (Blanc.Lift.WithdrawalRequest.systemProtocolOutput ((benvH benv).withState s)).returnData
    (systemCallOutput (Blanc.Lift.ConsolidationRequest.systemPost (benvC benv s))).returnData

theorem benvC_state_getStor7251 (benv : Benv) (s : State) :
    (benvC benv s).state.getStor consolidationRequestPredeployAddress =
      s.getStor consolidationRequestPredeployAddress :=
  systemW_post_getStor_other ((benvH benv).withState s) _ (by decide)

/-- **A body without withdrawals**: the two unchecked system calls, the given transaction fold
settling at `s`, and the two checked request calls on an empty 7251 queue. -/
theorem body_of_txs {benv : Benv} {txs : List (Bytes ⊕ Tx)} {decoded : List Tx}
    {s : State} {bout : BlockOutput} {lastHash : B256}
    (hfork : CoveredFork benv.stat.fork) (installed : SystemCodeInstalled benv.state)
    (hlast : benv.stat.blockHashes.getLast? = some lastHash)
    (hdecode : txs.mapM decodeTx = .ok decoded)
    (htxs : applyTransactions decoded.putIndex (benvH benv) BlockOutput.init =
      .ok ((benvH benv).withState s, bout))
    (hdeposit : parseDepositRequests bout = .ok [])
    (hWcode : s.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (hCcode : s.getCode consolidationRequestPredeployAddress = Blanc.consolidationRequestCode)
    (hz : Slots7251Zero s) :
    applyBody benv txs [] = .ok (bodyPost benv s, bodyOut benv s bout) := by
  have hbeaconCode := systemCodeInstalled_beaconRoots installed
  have hhistoryCode := systemCodeInstalled_historyStorage installed
  obtain ⟨hbeacon, -⟩ := stBeacon_step hfork hbeaconCode
  obtain ⟨hhistory, -⟩ := stHistory_step hfork hbeaconCode hhistoryCode hlast
  have hW := Blanc.Lift.WithdrawalRequest.processCheckedSystemTransaction_withdrawal
    (benv := (benvH benv).withState s) hfork hWcode
  have hCcode' : (benvC benv s).state.getCode consolidationRequestPredeployAddress =
      Blanc.consolidationRequestCode :=
    (systemW_post_getCode ((benvH benv).withState s) _).trans hCcode
  have hC := (checkedC_of_zero (benvC benv s) hfork hCcode'
    (slots7251Zero_of_getStor (benvC_state_getStor7251 benv s) hz)).1
  exact applyBody_forward hfork hbeacon hlast hhistory hdecode htxs hdeposit hW hC

/-- The body's final state agrees with the settled transaction state off the two request
predeploys. -/
theorem bodyPost_get_other {benv : Benv} {s : State} (hfork : CoveredFork benv.stat.fork)
    (hCcode : s.getCode consolidationRequestPredeployAddress = Blanc.consolidationRequestCode)
    (hz : Slots7251Zero s) (a : Adr) (hW : a ≠ withdrawalRequestPredeployAddress)
    (hC : a ≠ consolidationRequestPredeployAddress) :
    (bodyPost benv s).get a = s.get a := by
  have hCcode' : (benvC benv s).state.getCode consolidationRequestPredeployAddress =
      Blanc.consolidationRequestCode :=
    (systemW_post_getCode ((benvH benv).withState s) _).trans hCcode
  unfold bodyPost
  rw [systemC_post_get_other (benvC benv s) hfork hCcode'
    (slots7251Zero_of_getStor (benvC_state_getStor7251 benv s) hz) a (Ne.symm hC)]
  exact systemW_post_get_other ((benvH benv).withState s) a hW

/-- The body's final 7002 account is the one the 7002 system call leaves. -/
theorem bodyPost_get7002 {benv : Benv} {s : State} (hfork : CoveredFork benv.stat.fork)
    (hCcode : s.getCode consolidationRequestPredeployAddress = Blanc.consolidationRequestCode)
    (hz : Slots7251Zero s) :
    (bodyPost benv s).get withdrawalRequestPredeployAddress =
      (stW ((benvH benv).withState s)).get withdrawalRequestPredeployAddress := by
  have hCcode' : (benvC benv s).state.getCode consolidationRequestPredeployAddress =
      Blanc.consolidationRequestCode :=
    (systemW_post_getCode ((benvH benv).withState s) _).trans hCcode
  unfold bodyPost
  rw [systemC_post_get_other (benvC benv s) hfork hCcode'
    (slots7251Zero_of_getStor (benvC_state_getStor7251 benv s) hz) _ (by decide)]
  rfl

theorem bodyPost_zero {benv : Benv} {s : State} (hfork : CoveredFork benv.stat.fork)
    (hCcode : s.getCode consolidationRequestPredeployAddress = Blanc.consolidationRequestCode)
    (hz : Slots7251Zero s) : Slots7251Zero (bodyPost benv s) := by
  have hCcode' : (benvC benv s).state.getCode consolidationRequestPredeployAddress =
      Blanc.consolidationRequestCode :=
    (systemW_post_getCode ((benvH benv).withState s) _).trans hCcode
  exact systemC_post_zero (benvC benv s) hfork hCcode'
    (slots7251Zero_of_getStor (benvC_state_getStor7251 benv s) hz)

/-- **The 7002 system step on the model.**  If the settled state's 7002 storage represents `σ`,
the body's final 7002 storage represents `system σ`. -/
theorem bodyPost_represents {benv : Benv} {s : State} (hfork : CoveredFork benv.stat.fork)
    (hCcode : s.getCode consolidationRequestPredeployAddress = Blanc.consolidationRequestCode)
    (hz : Slots7251Zero s) {σ : Blanc.WithdrawalRequest.State}
    (hrep : Blanc.WithdrawalRequest.RepresentsStorage
      (s.getStor withdrawalRequestPredeployAddress).get σ)
    (hsum : Blanc.WithdrawalRequest.effectiveExcess σ + σ.count < 2 ^ 256) :
    Blanc.WithdrawalRequest.RepresentsStorage
      ((bodyPost benv s).getStor withdrawalRequestPredeployAddress).get
      (Blanc.WithdrawalRequest.system σ) := by
  have h := Blanc.Lift.WithdrawalRequest.systemFramePost_represents
    (Blanc.Lift.WithdrawalRequest.systemProtocolSevm ((benvH benv).withState s))
    (Blanc.Lift.WithdrawalRequest.systemProtocolBase ((benvH benv).withState s)) .empty
    (systemTransactionGas -
      Blanc.Lift.WithdrawalRequest.systemProtocolGas ((benvH benv).withState s)) σ hrep hsum
  have hget := congrArg (·.stor) (bodyPost_get7002 (benv := benv) hfork hCcode hz)
  change Blanc.WithdrawalRequest.RepresentsStorage ((bodyPost benv s).get _).stor.get _
  rw [hget]
  exact h

/-- The 7002 system call leaves every storage key but the four metadata slots. -/
theorem stW_getStor_high (b : Benv) (k : B256) (h0 : k ≠ 0) (h1 : k ≠ 1) (h2 : k ≠ 2)
    (h3 : k ≠ 3) :
    ((stW b).getStor withdrawalRequestPredeployAddress).get k =
      (b.state.getStor withdrawalRequestPredeployAddress).get k := by
  have hpost := Blanc.Lift.WithdrawalRequest.systemFramePost_storage
    (Blanc.Lift.WithdrawalRequest.systemProtocolSevm b)
    (Blanc.Lift.WithdrawalRequest.systemProtocolBase b) .empty
    (systemTransactionGas - Blanc.Lift.WithdrawalRequest.systemProtocolGas b)
  change (Devm.getStor (Blanc.Lift.WithdrawalRequest.systemProtocolPost b)
    withdrawalRequestPredeployAddress).get k = _
  unfold Blanc.Lift.WithdrawalRequest.systemProtocolPost
  rw [show withdrawalRequestPredeployAddress =
    (Blanc.Lift.WithdrawalRequest.systemProtocolSevm b).currentTarget from rfl, hpost,
    Stor.get_set_ne _ (Ne.symm h1), Stor.get_set_ne _ (Ne.symm h0)]
  unfold Blanc.Lift.WithdrawalRequest.systemFramePointers
    Blanc.Lift.WithdrawalRequest.systemPointerBase
  split
  · rw [afterSstore_getStor_self, afterSstore_getStor_self,
      Stor.get_set_ne _ (Ne.symm h3), Stor.get_set_ne _ (Ne.symm h2),
      Blanc.Lift.WithdrawalRequest.systemQueuePost_storage]
    rfl
  · rw [afterSstore_getStor_self, Stor.get_set_ne _ (Ne.symm h2),
      Blanc.Lift.WithdrawalRequest.systemQueuePost_storage]
    rfl

/-! ## Block C's submission frame -/

/-- **Block C's committed submission frame.**  A retained trace of `txC` on a state that
satisfies the transaction's premises holds a settled root frame at the predeploy that is a
submission payment frame, paid `2 ^ 245`, entered at the predeploy's storage. -/
theorem txC_submissionFrame {benv : Benv} {state : State} {bout' : BlockOutput}
    {iters : Nat} {out : B256} {σ : Blanc.WithdrawalRequest.State}
    (trace : TransactionTrace benv BlockOutput.init txC 0 state bout')
    (hfork : CoveredFork benv.stat.fork)
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
    (hiters : iters ≤ 10000) :
    ∃ frame ∈ trace.settledFrames, submissionPaymentFrame frame ∧
      frame.pre.getStor withdrawalRequestPredeployAddress =
        benv.state.getStor withdrawalRequestPredeployAddress ∧
      frame.sevm.value = (2 ^ 245 : Nat).toB256 := by
  have hsg : benv.stat.rules.stateGas = none := CoveredFork.rules_stateGas_none hfork
  have hEP : senderE ≠ withdrawalRequestPredeployAddress := by decide
  have hcost : calculateIntrinsicCost benv.stat.rules txC senderE = (21800, 23000) :=
    txC_intrinsic hsg (CoveredFork.rules_txBase hfork) (CoveredFork.rules_floorTokenCost hfork) _
  have hprec : benv.stat.rules.isPrecomp withdrawalRequestPredeployAddress = false :=
    propext (iff_of_false (Blanc.Lift.WithdrawalRequest.withdrawalRequest_not_precompile hfork)
      (by decide))
  have hnodeleg :
      getDelegatedCodeAddress (benv.state.getCode withdrawalRequestPredeployAddress) = none := by
    rw [hcode]; exact Blanc.Lift.WithdrawalRequest.withdrawalRequestCode_nondelegated
  have hrecover : recoverSender benv.stat.chainId txC = .ok senderE := by
    rw [hchain]
    exact txC_recoveredSender
  have hexecC := txC_exec (benv := benv) (index := 0) hfork hcode hrep hbounds hexcess
    hrun hpaid hiters
  obtain ⟨debit, msg, after, post, ⟨-, hct, hstatic, hcaller, hdata, hvalue, hstor⟩, frame,
      hmem, -, hsevm, hpre, -⟩ :=
    TransactionTrace.root_frame_of_call_value
      (R := fun _ msg after post =>
        TxCPost benv σ iters post ∧
        msg.currentTarget = withdrawalRequestPredeployAddress ∧ msg.isStatic = false ∧
        msg.caller = senderE ∧ msg.data = payload ∧ msg.value = (2 ^ 245 : Nat).toB256 ∧
        after.state.getStor withdrawalRequestPredeployAddress =
          benv.state.getStor withdrawalRequestPredeployAddress)
      trace hfork rfl hchain.symm (by decide) hbase hcost (by decide)
      (CoveredFork.checkTransactionGasCap_ok hfork (by decide)) (by decide)
      (by show 2 ^ 20 ≤ benv.stat.blockGasLimit - 0; exact hroom) hrecover hnonce
      hnocode hfunds hnodeleg hprec
      (by
        intro debit msg after hdebit hprep hentry
        obtain ⟨post, hex, herr, hrefund, hQ⟩ := hexecC debit msg after hdebit hprep hentry
        rw [prepareMessage_call rfl] at hprep
        have hm := Except.ok.inj hprep
        obtain ⟨-, hdeb⟩ := State.of_subBal hdebit
        have hstorAll : after.state.getStor withdrawalRequestPredeployAddress =
            benv.state.getStor withdrawalRequestPredeployAddress := by
          rw [benvAfterTransfer_ok_getStor hentry, ← hm]
          show (debit.get withdrawalRequestPredeployAddress).stor = _
          rw [hdeb, debit_get_ne hEP]
          rfl
        refine ⟨post, hex, herr, hrefund, hQ, ?_, ?_, ?_, ?_, ?_, hstorAll⟩
        all_goals rw [← hm]; rfl)
  refine ⟨frame, hmem, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · rw [hsevm]; exact hct
  · rw [hsevm]; exact hstatic
  · rw [hsevm]; show msg.caller ≠ systemAddress; rw [hcaller]; decide
  · rw [hsevm]; show msg.data.length = 56; rw [hdata]; exact payload_length
  · rw [hpre]; exact hstor
  · rw [hsevm]; exact hvalue

/-! ## The model states of the witness -/

/-- The model after block A's system call: the fork activated, nothing queued. -/
def σA : Blanc.WithdrawalRequest.State := Blanc.WithdrawalRequest.system Blanc.WithdrawalRequest.initial

theorem σA_eq : σA = ⟨0, 0, 0, 0, []⟩ := rfl

/-- The model after block B's flood. -/
def σF : Blanc.WithdrawalRequest.State := floodState σA (entryWith looperAddress) 2895

/-- The model block C's submission sees: after block B's system call. -/
def σC : Blanc.WithdrawalRequest.State := Blanc.WithdrawalRequest.system σF

theorem floodState_head (σ0 : Blanc.WithdrawalRequest.State)
    (entry : Blanc.WithdrawalRequest.Entry) (i : Nat) :
    (floodState σ0 entry i).head = σ0.head := by
  induction i with
  | zero => rfl
  | succ i ih => exact ih

theorem σF_fields : σF.excess = 0 ∧ σF.count = 2895 ∧ σF.head = 0 ∧ σF.tail = 2895 := by
  have f := floodState_fields σA (entryWith looperAddress) 2895
  rw [σA_eq] at f
  exact ⟨f.1, f.2.1, floodState_head _ _ _, f.2.2⟩

theorem σF_effectiveExcess : Blanc.WithdrawalRequest.effectiveExcess σF = 0 := by
  unfold Blanc.WithdrawalRequest.effectiveExcess
  rw [σF_fields.1]
  rfl

theorem σC_excess : σC.excess = 2893 := by
  unfold σC
  rw [Blanc.WithdrawalRequest.system_excess, σF_effectiveExcess, σF_fields.2.1]
  rfl

theorem σC_bounds (hcoh : Blanc.WithdrawalRequest.Coherent σF) : SubmissionBounds σC := by
  have hlen : σF.queue.length = 2895 := by
    have h : σF.head + σF.queue.length = σF.tail := hcoh
    rw [σF_fields.2.2.1, σF_fields.2.2.2] at h
    omega
  have hlive : ¬ σF.queue.length ≤ Blanc.WithdrawalRequest.maxPerBlock := by
    rw [hlen]; exact (by decide : ¬ 2895 ≤ 16)
  have htail : σC.tail = 2895 :=
    (Blanc.WithdrawalRequest.system_live_pointers σF hlive).2.trans σF_fields.2.2.2
  have hcount : σC.count = 0 := Blanc.WithdrawalRequest.system_count σF
  refine ⟨?_, ?_⟩
  · rw [hcount]
    exact (by decide : 0 + 1 < 2 ^ 256)
  · rw [htail]
    exact (by decide : Blanc.WithdrawalRequest.queueBase 2895 + 2 < 2 ^ 256)

/-! ## Block A -/

theorem stHistory_getStor_inst {benv : Benv} {lastHash : B256}
    (hfork : CoveredFork benv.stat.fork) (installed : SystemCodeInstalled benv.state)
    (hlast : benv.stat.blockHashes.getLast? = some lastHash)
    (a : Adr) (hneB : beaconRootsAddress ≠ a) (hneH : historyStorageAddress ≠ a) :
    (stHistory benv).getStor a = benv.state.getStor a :=
  stHistory_getStor_of_ne hfork (systemCodeInstalled_beaconRoots installed)
    (systemCodeInstalled_historyStorage installed) hlast a hneB hneH

theorem stHistory_getCode_inst {benv : Benv} {lastHash : B256}
    (hfork : CoveredFork benv.stat.fork) (installed : SystemCodeInstalled benv.state)
    (hlast : benv.stat.blockHashes.getLast? = some lastHash)
    (a : Adr) (hneB : beaconRootsAddress ≠ a) (hneH : historyStorageAddress ≠ a) :
    (stHistory benv).getCode a = benv.state.getCode a :=
  stHistory_getCode_of_ne hfork (systemCodeInstalled_beaconRoots installed)
    (systemCodeInstalled_historyStorage installed) hlast a hneB hneH

/-- A queue slot of the first `2895` records is above the four metadata slots. -/
theorem queueSlot_ne_meta {n o : Nat} (hn : n < 2895) (ho : o ≤ 2) (j : Nat) (hj : j < 4) :
    Blanc.WithdrawalRequest.queueSlot n o ≠ j.toB256 := by
  intro h
  have hk := congrArg B256.toNat h
  have hlt : Blanc.WithdrawalRequest.queueBase n + o < 2 ^ 256 := by
    unfold Blanc.WithdrawalRequest.queueBase; omega
  rw [show Blanc.WithdrawalRequest.queueSlot n o =
      (Blanc.WithdrawalRequest.queueBase n + o).toB256 from rfl,
    B256.toNat_toB256_of_lt hlt, B256.toNat_toB256_of_lt (by omega)] at hk
  unfold Blanc.WithdrawalRequest.queueBase at hk
  omega

theorem benvH_withState_stHistory (benv : Benv) :
    (benvH benv).withState (stHistory benv) = benvH benv := by
  unfold benvH Benv.withState
  rfl

/-- What block B needs of the state block A leaves. -/
structure PreB (w : State) : Prop where
  zero : Slots7251Zero w
  sender : w.get senderE = checkpointState.get senderE
  looper : w.get looperAddress = checkpointState.get looperAddress
  rep : Blanc.WithdrawalRequest.RepresentsStorage
    (w.getStor withdrawalRequestPredeployAddress).get σA
  queue : ∀ n o, n < 2895 → o ≤ 2 →
    (w.getStor withdrawalRequestPredeployAddress).get
      (Blanc.WithdrawalRequest.queueSlot n o) = 0

/-- **Block A**: no transactions; the fork-activation system call resets the inhibitor.  The
opening world needs only the checkpoint's two request-predeploy storage maps; every account but
the four system contracts' survives the block. -/
theorem blockA_run {benv : Benv} {lastHash : B256}
    (hfork : CoveredFork benv.stat.fork) (installed : SystemCodeInstalled benv.state)
    (hlast : benv.stat.blockHashes.getLast? = some lastHash)
    (h7002 : benv.state.getStor withdrawalRequestPredeployAddress =
      checkpointState.getStor withdrawalRequestPredeployAddress)
    (h7251 : benv.state.getStor consolidationRequestPredeployAddress =
      checkpointState.getStor consolidationRequestPredeployAddress) :
    applyBody benv [] [] =
      .ok (bodyPost benv (stHistory benv), bodyOut benv (stHistory benv) BlockOutput.init) ∧
    Slots7251Zero (bodyPost benv (stHistory benv)) ∧
    Blanc.WithdrawalRequest.RepresentsStorage
      ((bodyPost benv (stHistory benv)).getStor withdrawalRequestPredeployAddress).get σA ∧
    (∀ n o, n < 2895 → o ≤ 2 →
      ((bodyPost benv (stHistory benv)).getStor withdrawalRequestPredeployAddress).get
        (Blanc.WithdrawalRequest.queueSlot n o) = 0) ∧
    ∀ a, a ≠ withdrawalRequestPredeployAddress → a ≠ consolidationRequestPredeployAddress →
      beaconRootsAddress ≠ a → historyStorageAddress ≠ a →
      (bodyPost benv (stHistory benv)).get a = benv.state.get a := by
  have hWcode : (stHistory benv).getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode :=
    (stHistory_getCode_inst hfork installed hlast _ (by decide) (by decide)).trans
      (systemCodeInstalled_withdrawal installed)
  have hCcode : (stHistory benv).getCode consolidationRequestPredeployAddress =
      Blanc.consolidationRequestCode :=
    (stHistory_getCode_inst hfork installed hlast _ (by decide) (by decide)).trans
      (systemCodeInstalled_consolidation installed)
  have hstorW : (stHistory benv).getStor withdrawalRequestPredeployAddress =
      checkpointState.getStor withdrawalRequestPredeployAddress := by
    rw [stHistory_getStor_inst hfork installed hlast _ (by decide) (by decide), h7002]
  have hz : Slots7251Zero (stHistory benv) := by
    unfold Slots7251Zero
    rw [stHistory_getStor_inst hfork installed hlast _ (by decide) (by decide), h7251]
    exact ⟨checkpoint_7251_slots 0, checkpoint_7251_slots 1, checkpoint_7251_slots 2,
      checkpoint_7251_slots 3⟩
  have hkeep : ∀ a, a ≠ withdrawalRequestPredeployAddress →
      a ≠ consolidationRequestPredeployAddress → beaconRootsAddress ≠ a →
      historyStorageAddress ≠ a →
      (bodyPost benv (stHistory benv)).get a = benv.state.get a := by
    intro a hW hC hB hH
    rw [bodyPost_get_other hfork hCcode hz a hW hC,
      stHistory_get_of_installed hfork installed hlast hB hH]
  have htxs : applyTransactions ([] : List Tx).putIndex (benvH benv) BlockOutput.init =
      .ok ((benvH benv).withState (stHistory benv), BlockOutput.init) := by
    rw [benvH_withState_stHistory]
    rfl
  refine ⟨body_of_txs hfork installed hlast rfl htxs (parseDepositRequests_of_no_receipts rfl)
    hWcode hCcode hz, bodyPost_zero hfork hCcode hz, ?_, ?_, hkeep⟩
  · have hrep0 : Blanc.WithdrawalRequest.RepresentsStorage
        ((stHistory benv).getStor withdrawalRequestPredeployAddress).get
        Blanc.WithdrawalRequest.initial := by
      rw [hstorW]
      exact checkpoint_7002_rep
    exact bodyPost_represents hfork hCcode hz hrep0 (by decide)
  · intro n o hn ho
    have hst := congrArg (·.stor) (bodyPost_get7002 (benv := benv) hfork hCcode hz)
    change ((bodyPost benv (stHistory benv)).get _).stor.get _ = 0
    rw [hst]
    change ((stW ((benvH benv).withState (stHistory benv))).getStor _).get _ = 0
    rw [stW_getStor_high _ _ (queueSlot_ne_meta hn ho 0 (by decide))
      (queueSlot_ne_meta hn ho 1 (by decide)) (queueSlot_ne_meta hn ho 2 (by decide))
      (queueSlot_ne_meta hn ho 3 (by decide))]
    change ((stHistory benv).getStor _).get _ = 0
    rw [hstorW]
    exact checkpoint_7002_queue_zero n o (by unfold Blanc.WithdrawalRequest.queueBase; omega)

/-! ## Block B -/

/-- What block C needs of the state block B leaves. -/
structure PreC (w : State) : Prop where
  zero : Slots7251Zero w
  nonce : (w.get senderE).nonce = 1
  nocode : (w.get senderE).code.isEmpty = true
  funds : 2 ^ 20 * 8 + 2 ^ 245 ≤ (w.get senderE).bal.toNat
  rep : Blanc.WithdrawalRequest.RepresentsStorage
    (w.getStor withdrawalRequestPredeployAddress).get σC

/-- The sender's balance after a fee debit, a value debit and a refund, in naturals. -/
theorem toNat_sub_sub_add {b : B256} {x y r : Nat} (hxy : x + y ≤ b.toNat)
    (hr : r < 2 ^ 256) (hsum : b.toNat + r < 2 ^ 256) :
    ((b - x.toB256 - y.toB256) + r.toB256).toNat = b.toNat - x - y + r := by
  have hb := B256.toNat_lt b
  have hx : x.toB256.toNat = x := B256.toNat_toB256_of_lt (by omega)
  have hy : y.toB256.toNat = y := B256.toNat_toB256_of_lt (by omega)
  have hrr : r.toB256.toNat = r := B256.toNat_toB256_of_lt hr
  have h1 : (b - x.toB256).toNat = b.toNat - x := by
    rw [B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, hx]; omega), hx]
  have h2 : (b - x.toB256 - y.toB256).toNat = b.toNat - x - y := by
    rw [B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, hy, h1]; omega), hy, h1]
  rw [B256.toNat_add_eq_of_nof _ _ (by unfold B256.Nof; rw [h2, hrr]; omega), h2, hrr]

/-- **Block B**: the flood. -/
theorem blockB_run {benv : Benv} {lastHash : B256}
    (hfork : CoveredFork benv.stat.fork) (installed : SystemCodeInstalled benv.state)
    (hlast : benv.stat.blockHashes.getLast? = some lastHash) (hpre : PreB benv.state)
    (hnocap : benv.stat.rules.tx.maxGas = none) (hchain : benv.stat.chainId = 1)
    (hbase : benv.stat.baseFeePerGas = 1) (hroom : 2 ^ 28 ≤ benv.stat.blockGasLimit)
    (hcb : benv.stat.coinbase ≠ senderE) :
    ∃ (s : State) (bout : BlockOutput),
      applyBody benv [Sum.inr txB] [] = .ok (bodyPost benv s, bodyOut benv s bout) ∧
      bout.blockGasUsed ≤ 2 ^ 28 ∧ PreC (bodyPost benv s) := by
  have hsender : (stHistory benv).get senderE = checkpointState.get senderE :=
    (stHistory_get_of_installed hfork installed hlast (by decide) (by decide)).trans hpre.sender
  have hlooper : (stHistory benv).get looperAddress = checkpointState.get looperAddress :=
    (stHistory_get_of_installed hfork installed hlast (by decide) (by decide)).trans hpre.looper
  have hstor7002 : (stHistory benv).getStor withdrawalRequestPredeployAddress =
      benv.state.getStor withdrawalRequestPredeployAddress :=
    stHistory_getStor_inst hfork installed hlast _ (by decide) (by decide)
  have hnonce' : ((stHistory benv).get senderE).nonce = 0 := by
    rw [hsender, checkpoint_get_senderE]
  have hnocode' : ((stHistory benv).get senderE).code.isEmpty = true := by
    rw [hsender]; exact checkpoint_senderE_noCode
  have hfunds' : 2 ^ 28 * 8 + 2895 ≤ ((stHistory benv).get senderE).bal.toNat := by
    rw [hsender]; exact checkpoint_senderE_fundsB
  have hLcode' : (stHistory benv).getCode looperAddress = Blanc.Lift.FloodLooper.code := by
    change ((stHistory benv).get _).code = _
    rw [hlooper, checkpoint_get_looper]
  have hLbal' : ((stHistory benv).bal looperAddress).toNat + 2895 < 2 ^ 256 := by
    change ((stHistory benv).get _).bal.toNat + 2895 < 2 ^ 256
    rw [hlooper, checkpoint_get_looper]
    have h0 : (0 : B256).toNat = 0 := B256.toNat_toB256_of_lt (by decide)
    change (0 : B256).toNat + 2895 < 2 ^ 256
    rw [h0]
    decide
  have hcode' : (stHistory benv).getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode :=
    (stHistory_getCode_inst hfork installed hlast _ (by decide) (by decide)).trans
      (systemCodeInstalled_withdrawal installed)
  have hrep' : Blanc.WithdrawalRequest.RepresentsStorage
      ((stHistory benv).getStor withdrawalRequestPredeployAddress).get σA := by
    rw [hstor7002]; exact hpre.rep
  have hqueue' : ∀ n o, σA.tail ≤ n → n < σA.tail + 2895 → o ≤ 2 →
      ((stHistory benv).getStor withdrawalRequestPredeployAddress).get
        (Blanc.WithdrawalRequest.queueSlot n o) = 0 := by
    intro n o _ hn ho
    rw [hstor7002]
    exact hpre.queue n o (by rw [σA_eq] at hn; exact hn) ho
  have hrecover : recoverSender benv.stat.chainId txB = .ok senderE := by
    rw [hchain]; exact txB_recoveredSender
  obtain ⟨post, bout', hQ, hproc, -, hblk, hkeys, hreceipt⟩ := txB_processTransaction
    (benv := benv.withState (stHistory benv)) (bout := BlockOutput.init) (index := 0)
    hfork hnocap hchain (by rw [show (benv.withState (stHistory benv)).stat.baseFeePerGas =
      benv.stat.baseFeePerGas from rfl, hbase]; decide)
    (by show 2 ^ 28 ≤ benv.stat.blockGasLimit - 0; exact hroom)
    hrecover hnonce' hnocode' hfunds' hLcode' hLbal' hcode' hrep' (by rw [σA_eq])
    (by rw [σA_eq]; decide) (by rw [σA_eq]; decide) hqueue'
  have hdeposit : parseDepositRequests bout' = .ok [] :=
    parseDepositRequests_of_predeploy_logs hkeys hreceipt (by
      rw [hQ.2.2.1]
      intro log hlog
      rw [(List.mem_replicate.mp hlog).2])
  set R : B256 := ((txB.gas - txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat) *
    (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256 with hR
  set T : B256 := (txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat *
    (min 1 (8 - benv.stat.baseFeePerGas))).toB256 with hT
  set sB : State := settledState post senderE benv.stat.coinbase R T with hsB
  have hproc' : processTransaction (benvH benv) BlockOutput.init txB 0 = .ok (sB, bout') := by
    rw [TxBPost.no_deletions hQ] at hproc
    exact hproc
  have htxs : applyTransactions [txB].putIndex (benvH benv) BlockOutput.init =
      .ok ((benvH benv).withState sB, bout') := by
    rw [putIndex_single]
    exact applyTransactions_single hproc'
  have hWcode : sB.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode :=
    TxBPost_settled_7002code hQ _ _ _ _
  have hCcode : sB.getCode consolidationRequestPredeployAddress =
      Blanc.consolidationRequestCode :=
    (TxBPost_settled_otherCode hQ _ (by decide) (by decide) (by decide) _ _ _ _).trans
      ((stHistory_getCode_inst hfork installed hlast _ (by decide) (by decide)).trans
        (systemCodeInstalled_consolidation installed))
  have hz : Slots7251Zero sB :=
    slots7251Zero_of_getStor ((TxBPost_settled_stor7251 hQ (by decide) (by decide) (by decide)
      _ _ _ _).trans (stHistory_getStor_inst hfork installed hlast _ (by decide) (by decide)))
      hpre.zero
  refine ⟨sB, bout', body_of_txs hfork installed hlast (decode_single txB) htxs hdeposit
    hWcode hCcode hz, ?_, ?_⟩
  · rw [hblk]
    exact (Nat.zero_add _).le.trans (txGasUsed_le (by decide))
  -- the sender after the body
  have hget : (bodyPost benv sB).get senderE = (post.state.get senderE).withBal
      (post.state.bal senderE + R) := by
    rw [bodyPost_get_other hfork hCcode hz senderE (by decide) (by decide), hsB, settledState,
      addBal_get_ne _ hcb, addBal_get_self]
  have hpostE := hQ.2.2.2.2.2.1
  have hsE : (benv.withState (stHistory benv)).state.get senderE =
      { Acct.nil with nonce := 0, bal := senderEFunds.toB256 } :=
    hsender.trans checkpoint_get_senderE
  refine ⟨bodyPost_zero hfork hCcode hz, ?_, ?_, ?_, ?_⟩
  · rw [hget, hpostE, hsE]
    rfl
  · rw [hget, hpostE, hsE]
    rfl
  · rw [hget]
    change 2 ^ 20 * 8 + 2 ^ 245 ≤ (post.state.bal senderE + R).toNat
    have hbal : post.state.bal senderE = senderEFunds.toB256 -
        (txB.gas * (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256 -
        (2895 : Nat).toB256 := by
      show (post.state.get senderE).bal = _
      rw [hpostE]
      change ((benv.withState (stHistory benv)).state.get senderE).bal - _ - _ = _
      rw [hsE]
      rfl
    have hused := txGasUsed_le (gas := txB.gas) (floor := 23380) (left := post.gasLeft)
      (refund := post.refundCounter.toNat) (by decide)
    have hprice : min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas = 2 := by
      rw [hbase]
      rfl
    have hgas : txB.gas = 2 ^ 28 := rfl
    have hF : senderEFunds.toB256.toNat = senderEFunds := B256.toNat_toB256_of_lt senderEFunds_lt
    rw [hbal, hR, hprice, hgas]
    rw [hgas] at hused
    unfold senderEFunds at hF ⊢
    rw [toNat_sub_sub_add (by rw [hF]; omega) (by omega) (by rw [hF]; omega), hF]
    omega
  · have hrepF : Blanc.WithdrawalRequest.RepresentsStorage
        (sB.getStor withdrawalRequestPredeployAddress).get σF := by
      rw [hsB, settledState_getStor]
      exact hQ.2.1
    exact bodyPost_represents hfork hCcode hz hrepF
      (by rw [σF_effectiveExcess, σF_fields.2.1]; decide)

/-! ## Block C -/

theorem floodState_coherent {σ0 : Blanc.WithdrawalRequest.State}
    (h : Blanc.WithdrawalRequest.Coherent σ0) (entry : Blanc.WithdrawalRequest.Entry) (i : Nat) :
    Blanc.WithdrawalRequest.Coherent (floodState σ0 entry i) := by
  induction i with
  | zero => exact h
  | succ i ih => exact Blanc.WithdrawalRequest.submit_coherent ih entry

theorem σF_coherent : Blanc.WithdrawalRequest.Coherent σF :=
  floodState_coherent (by rw [σA_eq]; rfl) _ _

theorem σC_submissionBounds : SubmissionBounds σC := σC_bounds σF_coherent

/-- The word fee loop at block C's excess, in the shape `txC` takes. -/
theorem σC_run : WordFakeExponential.Run σC.excess.toB256 17 1 17 0 457
    wordOutput2893.toB256 := by
  have h17 : (17 : Nat).toB256 = (17 : B256) := by decide
  have h1 : (1 : Nat).toB256 = (1 : B256) := by decide
  have h0 : (0 : Nat).toB256 = (0 : B256) := by decide
  have h := Blanc.Lift.WithdrawalRequest.word_run_2893_existing
  rw [h17, h1, h0] at h
  rw [σC_excess]
  exact h

theorem σC_paid : (wordOutput2893.toB256 / (17 : B256)).toNat ≤ 2 ^ 245 := by
  have h17 : (17 : Nat).toB256 = (17 : B256) := by decide
  have h := Blanc.Lift.WithdrawalRequest.word_run_2893_fee
  rw [h17] at h
  change (wordOutput2893.toB256 / (17 : B256)).toNat ≤ 2 ^ 245 at *
  rw [show (wordOutput2893.toB256 / (17 : B256)).toNat = wordFee2893 from h]
  exact Blanc.Lift.WithdrawalRequest.word_fee_2893_le_two_pow_245

/-- What `txC` needs of the world it runs in. -/
structure TxCReady (w : State) : Prop where
  nonce : (w.get senderE).nonce = 1
  nocode : (w.get senderE).code.isEmpty = true
  funds : 2 ^ 20 * 8 + 2 ^ 245 ≤ (w.get senderE).bal.toNat
  code : w.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode
  rep : Blanc.WithdrawalRequest.RepresentsStorage
    (w.getStor withdrawalRequestPredeployAddress).get σC

theorem txCReady_stHistory {benv : Benv} {lastHash : B256}
    (hfork : CoveredFork benv.stat.fork) (installed : SystemCodeInstalled benv.state)
    (hlast : benv.stat.blockHashes.getLast? = some lastHash) (hpre : PreC benv.state) :
    TxCReady (stHistory benv) := by
  have hsender : (stHistory benv).get senderE = benv.state.get senderE :=
    stHistory_get_of_installed hfork installed hlast (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hsender]; exact hpre.nonce
  · rw [hsender]; exact hpre.nocode
  · rw [hsender]; exact hpre.funds
  · exact (stHistory_getCode_inst hfork installed hlast _ (by decide) (by decide)).trans
      (systemCodeInstalled_withdrawal installed)
  · rw [stHistory_getStor_inst hfork installed hlast _ (by decide) (by decide)]
    exact hpre.rep

/-- **Block C**: the direct `2 ^ 245`-wei submission at excess `2893`. -/
theorem blockC_run {benv : Benv} {lastHash : B256}
    (hfork : CoveredFork benv.stat.fork) (installed : SystemCodeInstalled benv.state)
    (hlast : benv.stat.blockHashes.getLast? = some lastHash) (hpre : PreC benv.state)
    (hchain : benv.stat.chainId = 1) (hbase : benv.stat.baseFeePerGas = 1)
    (hroom : 2 ^ 20 ≤ benv.stat.blockGasLimit) :
    ∃ (s : State) (bout : BlockOutput),
      applyBody benv [Sum.inr txC] [] = .ok (bodyPost benv s, bodyOut benv s bout) ∧
      bout.blockGasUsed ≤ 2 ^ 20 := by
  have hready := txCReady_stHistory hfork installed hlast hpre
  have hrecover : recoverSender benv.stat.chainId txC = .ok senderE := by
    rw [hchain]; exact txC_recoveredSender
  obtain ⟨post, bout', hQ, hproc, -, hblk, hkeys, hreceipt⟩ := txC_processTransaction
    (benv := benv.withState (stHistory benv)) (bout := BlockOutput.init) (index := 0)
    hfork hchain (by rw [show (benv.withState (stHistory benv)).stat.baseFeePerGas =
      benv.stat.baseFeePerGas from rfl, hbase]; decide)
    (by show 2 ^ 20 ≤ benv.stat.blockGasLimit - 0; exact hroom) hrecover
    hready.nonce hready.nocode hready.funds hready.code hready.rep σC_submissionBounds
    (by rw [σC_excess]; decide) σC_run σC_paid (by decide)
  have hdeposit : parseDepositRequests bout' = .ok [] :=
    parseDepositRequests_of_predeploy_logs hkeys hreceipt (by
      rw [hQ.2.1]
      intro log hlog
      rw [List.mem_singleton] at hlog
      rw [hlog])
  set sC : State := settledState post senderE benv.stat.coinbase
    ((txC.gas - txGasUsed txC.gas 23000 post.gasLeft post.refundCounter.toNat) *
      (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256
    (txGasUsed txC.gas 23000 post.gasLeft post.refundCounter.toNat *
      (min 1 (8 - benv.stat.baseFeePerGas))).toB256 with hsC
  have hproc' : processTransaction (benvH benv) BlockOutput.init txC 0 = .ok (sC, bout') := by
    rw [settled_of_no_deletions post senderE _ _ _ hQ.2.2.2.2.1] at hproc
    exact hproc
  have htxs : applyTransactions [txC].putIndex (benvH benv) BlockOutput.init =
      .ok ((benvH benv).withState sC, bout') := by
    rw [putIndex_single]
    exact applyTransactions_single hproc'
  have hcodes : ∀ a, sC.getCode a = (stHistory benv).getCode a := fun a =>
    TxCPost_settled_codes hQ _ _ a _ _
  have hWcode : sC.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode :=
    (hcodes _).trans hready.code
  have hCcode : sC.getCode consolidationRequestPredeployAddress =
      Blanc.consolidationRequestCode :=
    (hcodes _).trans ((stHistory_getCode_inst hfork installed hlast _ (by decide)
      (by decide)).trans (systemCodeInstalled_consolidation installed))
  have hz : Slots7251Zero sC :=
    slots7251Zero_of_getStor ((TxCPost_settled_stor7251 hQ (by decide) _ _ _ _).trans
      (stHistory_getStor_inst hfork installed hlast _ (by decide) (by decide))) hpre.zero
  refine ⟨sC, bout', body_of_txs hfork installed hlast (decode_single txC) htxs hdeposit
    hWcode hCcode hz, ?_⟩
  rw [hblk]
  exact (Nat.zero_add _).le.trans (txGasUsed_le (by decide))

/-! ## The witness blocks -/

/-- The witness blocks' fee recipient: no account the witness otherwise uses. -/
def witnessCoinbase : Adr := 0x2222222222222222222222222222222222222222

/-- The header fields every witness block shares; the rest are committed. -/
def witnessTemplate : Header := { genesisHeader with coinbase := witnessCoinbase }

/-- A witness block on `parent`, committed to the body result `st`, `bout`. -/
def mkBlock (parent : Block) (txs : List (Bytes ⊕ Tx)) (st : State) (bout : BlockOutput) :
    Block :=
  { header := commitHeader (Fork.ruleSet .prague) parent witnessTemplate st bout
    txs := txs, wds := [], ommers := [] }

/-- The chain after appending a block whose body left `st`. -/
def mkChain (pre : BlockChain) (block : Block) (st : State) : BlockChain :=
  ⟨appendBlock pre.blocks block, st, pre.chainId⟩

/-- The environment a witness block on `parent` opens with: it reads no committed field. -/
def benvAt (pre : BlockChain) (parent : Block) : Benv :=
  initBenv .prague pre (commitHeader (Fork.ruleSet .prague) parent witnessTemplate pre.state
    BlockOutput.init)

theorem prague_covered : CoveredFork .prague := by decide

theorem benvAt_facts (pre : BlockChain) (parent : Block) :
    CoveredFork (benvAt pre parent).stat.fork ∧
    (benvAt pre parent).state = pre.state ∧
    (benvAt pre parent).stat.chainId = pre.chainId ∧
    (benvAt pre parent).stat.baseFeePerGas = 1 ∧
    (benvAt pre parent).stat.blockGasLimit = 2 ^ 29 ∧
    (benvAt pre parent).stat.coinbase ≠ senderE ∧
    (benvAt pre parent).stat.rules.tx.maxGas = none ∧
    (benvAt pre parent).stat.blockHashes = getLast256BlockHashes pre :=
  ⟨prague_covered, rfl, rfl, rfl, rfl, by show witnessCoinbase ≠ senderE; decide, rfl, rfl⟩

/-- **A witness block is a configured block trace** once its body runs: the header is committed
and validates with base fee `1` whenever the parent used at most half the gas limit. -/
theorem witnessBlockTrace {pre : BlockChain} {parent : Block} {txs : List (Bytes ⊕ Tx)}
    {st : State} {bout : BlockOutput}
    (hlastBlock : pre.blocks.getLast? = some parent)
    (hbound : sum pre.state.bal < 2 ^ 256) (hid : pre.chainId = 1)
    (hparentLimit : parent.header.gasLimit = 2 ^ 29)
    (hparentBase : parent.header.baseFeePerGas = 1)
    (hparentUsed : parent.header.gasUsed ≤ 2 ^ 28)
    (hbody : applyBody (benvAt pre parent) txs [] = .ok (st, bout))
    (hgas : bout.blockGasUsed ≤ 2 ^ 29) :
    Nonempty (ConfiguredBlockTrace witnessConfig pre
      (mkChain pre (mkBlock parent txs st bout) st)) := by
  have hbase : calculateBaseFeePerGas
      (commitHeader (Fork.ruleSet .prague) parent witnessTemplate st bout).gasLimit
      parent.header.gasLimit parent.header.gasUsed parent.header.baseFeePerGas =
      .ok (commitHeader (Fork.ruleSet .prague) parent witnessTemplate st bout).baseFeePerGas := by
    rw [hparentLimit, hparentBase]
    exact calculateBaseFeePerGas_unit (gasLimit := 2 ^ 29) (by decide) (by decide) (by decide)
      (by show parent.header.gasUsed ≤ 2 ^ 29 / 2; omega)
  have hheader := commitHeader_ok (rules := Fork.ruleSet .prague) (chain := pre)
    (template := witnessTemplate) hlastBlock hbase hgas (by decide) rfl rfl
  exact blockTrace_of_body (block := mkBlock parent txs st bout) hbound rfl
    (by rw [witnessConfig_chainId, hid]) (witnessConfig_forkAt _) prague_covered hheader rfl
    hbody rfl rfl rfl rfl rfl rfl rfl rfl

/-! ## Creation-freedom of the witness world -/

theorem looper_callOnly : CallOnlyReach Blanc.Lift.FloodLooper.code :=
  callOnlyReach_of_check (by decide +kernel)

theorem looper_not_delegation : ¬ isValidDelegation Blanc.Lift.FloodLooper.code :=
  fun hd => absurd hd.1 (by decide +kernel)

theorem systemCode_callOnly {p : Adr × ByteArray} (hp : p ∈ systemContracts) :
    CallOnlyReach p.2 ∧ ¬ isValidDelegation p.2 := by
  obtain ⟨hreach, hnd, -⟩ := systemContracts_facts p hp
  exact ⟨callOnlyReach_of_spawnFreeReach hreach, hnd⟩

/-- Every checkpoint code is a system code, the looper's, or empty. -/
theorem checkpoint_getCode_cases (a : Adr) :
    checkpointState.getCode a = Blanc.beaconRootsCode ∨
    checkpointState.getCode a = Blanc.historyStorageCode ∨
    checkpointState.getCode a = Blanc.withdrawalRequestCode ∨
    checkpointState.getCode a = Blanc.consolidationRequestCode ∨
    checkpointState.getCode a = Blanc.Lift.FloodLooper.code ∨
    checkpointState.getCode a = ByteArray.empty := by
  change (checkpointState.get a).code = _ ∨ (checkpointState.get a).code = _ ∨
    (checkpointState.get a).code = _ ∨ (checkpointState.get a).code = _ ∨
    (checkpointState.get a).code = _ ∨ (checkpointState.get a).code = _
  unfold checkpointState State.ofList
  simp only [List.foldl_cons, List.foldl_nil]
  by_cases hE : senderE = a
  · rw [hE, State.get_set_self]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  rw [State.get_set_ne _ hE]
  by_cases hL : looperAddress = a
  · rw [hL, State.get_set_self]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rw [State.get_set_ne _ hL]
  by_cases hC : consolidationRequestPredeployAddress = a
  · rw [hC, State.get_set_self]
    exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rw [State.get_set_ne _ hC]
  by_cases hW : withdrawalRequestPredeployAddress = a
  · rw [hW, State.get_set_self]
    exact Or.inr (Or.inr (Or.inl rfl))
  rw [State.get_set_ne _ hW]
  by_cases hH : historyStorageAddress = a
  · rw [hH, State.get_set_self]
    exact Or.inr (Or.inl rfl)
  rw [State.get_set_ne _ hH]
  by_cases hB : beaconRootsAddress = a
  · rw [hB, State.get_set_self]
    exact Or.inl rfl
  rw [State.get_set_ne _ hB]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

theorem checkpoint_callOnly : CodesCallOnly checkpointState.getCode := by
  intro a
  have hmem := fun {p : Adr × ByteArray} (hp : p ∈ systemContracts) => systemCode_callOnly hp
  rcases checkpoint_getCode_cases a with h | h | h | h | h | h <;> rw [h]
  · exact hmem (p := (beaconRootsAddress, Blanc.beaconRootsCode))
      (by simp only [systemContracts, List.mem_cons, true_or])
  · exact hmem (p := (historyStorageAddress, Blanc.historyStorageCode))
      (by simp only [systemContracts, List.mem_cons, true_or, or_true])
  · exact hmem (p := (withdrawalRequestPredeployAddress, Blanc.withdrawalRequestCode))
      (by simp only [systemContracts, List.mem_cons, true_or, or_true])
  · exact hmem (p := (consolidationRequestPredeployAddress, Blanc.consolidationRequestCode))
      (by simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false, or_true])
  · exact ⟨looper_callOnly, looper_not_delegation⟩
  · exact ⟨callOnlyReach_empty, not_isValidDelegation_empty⟩

/-! ## Reading the retained traces -/

/-- A retained body's pre-transaction states are the functional ones. -/
theorem AppliedBodyTrace.history_eq {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {wds : List Withdrawal} {st : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds st bout) (hfork : CoveredFork benv.stat.fork)
    (installed : SystemCodeInstalled benv.state) :
    trace.beaconState = stBeacon benv ∧ trace.historyState = stHistory benv := by
  have hbeaconCode := systemCodeInstalled_beaconRoots installed
  have hhistoryCode := systemCodeInstalled_historyStorage installed
  have hB := (stBeacon_step hfork hbeaconCode).1
  have hBeq := Except.ok.inj (trace.beacon.run.symm.trans hB)
  have hbeacon : trace.beaconState = stBeacon benv := (Prod.mk.inj hBeq).1
  have hlast : benv.stat.blockHashes.getLast? = some trace.lastHash :=
    Option.toExcept_eq_ok trace.lastHashRun
  have hH := (stHistory_step hfork hbeaconCode hhistoryCode hlast).1
  have hrun := trace.history.run
  rw [hbeacon] at hrun
  have hHeq := Except.ok.inj (hrun.symm.trans hH)
  exact ⟨hbeacon, (Prod.mk.inj hHeq).1⟩

theorem ApplyTransactionsTrace.noSender_single {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (t : ApplyTransactionsTrace txs benv bout finalBenv finalBout) {tx : Tx}
    (h : txs = [(0, tx)]) (hrecover : recoverSender benv.stat.chainId tx = .ok senderE) :
    t.NoSenderAt systemAddress := by
  subst h
  exact noSenderAt_single t hrecover

/-- The one transaction of a witness block is a call without authorizations. -/
theorem calls_of_single {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) {tx : Tx}
    (hdecoded : trace.decodedTxs = [tx]) {t : Adr} (hreceiver : tx.type.receiver? = some t)
    (hauths : tx.auths = []) :
    ∀ p ∈ trace.decodedTxs.putIndex, (∃ t, p.2.type.receiver? = some t) ∧ p.2.auths = [] := by
  intro p hp
  rw [hdecoded, putIndex_single, List.mem_singleton] at hp
  subst hp
  exact ⟨⟨t, hreceiver⟩, hauths⟩

theorem calls_of_nil {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) (hdecoded : trace.decodedTxs = []) :
    ∀ p ∈ trace.decodedTxs.putIndex, (∃ t, p.2.type.receiver? = some t) ∧ p.2.auths = [] := by
  intro p hp
  rw [hdecoded] at hp
  exact absurd hp List.not_mem_nil

/-! ## The three-block history -/

/-- What one retained witness block gives the history: its frames have code addresses (so no
frame targets the system address without one), no sender or authorization is the system
address, and the next world is call-only, has the system code installed, and a bounded total
balance. -/
structure BlockOk {pre post : BlockChain} (trace : ConfiguredBlockTrace witnessConfig pre post) :
    Prop where
  avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
    root.sevm.currentTarget ≠ systemAddress
  senders : trace.bodyTrace.transactions.NoSenderAt systemAddress
  authorities : ∀ p ∈ trace.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
    recoverAuthority auth = .ok authority → authority ≠ systemAddress
  world : CodesCallOnly post.state.getCode
  installed : SystemCodeInstalled post.state
  bound : sum post.state.bal < 2 ^ 256

/-- The common part of `BlockOk`, from the call-only fact for the block's transactions. -/
theorem blockOk_of {pre post : BlockChain} (trace : ConfiguredBlockTrace witnessConfig pre post)
    (hworld : CodesCallOnly pre.state.getCode) (installed : SystemCodeInstalled pre.state)
    (hbound : sum pre.state.bal < 2 ^ 256) (hwds : trace.block.wds = [])
    (hcalls : ∀ p ∈ trace.bodyTrace.decodedTxs.putIndex,
      (∃ t, p.2.type.receiver? = some t) ∧ p.2.auths = [])
    (senders : trace.bodyTrace.transactions.NoSenderAt systemAddress) :
    BlockOk trace := by
  obtain ⟨hroots, hpostWorld⟩ := trace.callOnly hcalls hworld
  have hauth : ∀ (a : Adr), ∀ p ∈ trace.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths,
      ∀ authority, recoverAuthority auth = .ok authority → authority ≠ a := by
    intro a p hp auth hauth
    rw [(hcalls p hp).2] at hauth
    exact absurd hauth List.not_mem_nil
  have avoidAll : ∀ (a : Adr), ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a :=
    fun _ root member hnone => absurd hnone (hroots root member)
  exact ⟨avoidAll systemAddress, senders, hauth systemAddress, hpostWorld,
    (trace.systemFrames_of_installed installed (fun p _ => hauth p.1)
      (fun p _ => avoidAll p.1)).2,
    Nat.lt_of_le_of_lt (Blanc.BlockForward.ConfiguredBlockTrace.sum_post_le trace hwds) hbound⟩

theorem chain_blocks_ne (pre : BlockChain) (block : Block) (st : State) :
    (mkChain pre block st).blocks ≠ [] :=
  appendBlock_ne_nil _ _

theorem mkChain_getLast (pre : BlockChain) (block : Block) (st : State) :
    (mkChain pre block st).blocks.getLast? = some block :=
  appendBlock_getLast? _ _

/-- What the next witness block needs of a chain and its tip. -/
structure ChainReady (chain : BlockChain) (parent : Block) : Prop where
  last : chain.blocks.getLast? = some parent
  nonempty : chain.blocks ≠ []
  chainId : chain.chainId = 1
  gasLimit : parent.header.gasLimit = 2 ^ 29
  baseFee : parent.header.baseFeePerGas = 1
  gasUsed : parent.header.gasUsed ≤ 2 ^ 28

theorem chainReady_mk (pre : BlockChain) (parent : Block) (txs : List (Bytes ⊕ Tx))
    (st : State) (bout : BlockOutput) (hid : pre.chainId = 1)
    (hgas : bout.blockGasUsed ≤ 2 ^ 28) :
    ChainReady (mkChain pre (mkBlock parent txs st bout) st) (mkBlock parent txs st bout) :=
  ⟨mkChain_getLast _ _ _, chain_blocks_ne _ _ _, hid, rfl, rfl, hgas⟩

theorem checkpoint_ready : ChainReady checkpointChain genesisBlock :=
  ⟨rfl, List.cons_ne_nil _ _, rfl, rfl, rfl, by decide⟩

/-- **Stage A.** -/
theorem stageA : ∃ (post : BlockChain) (trace : ConfiguredBlockTrace witnessConfig checkpointChain post)
    (parent : Block), BlockOk trace ∧ PreB post.state ∧ ChainReady post parent := by
  obtain ⟨lhA, hlA⟩ := blockHashes_getLast_of_ne checkpoint_ready.nonempty
  obtain ⟨hbody, hz, hrep, hqueue, hkeep⟩ := blockA_run
    (benv := benvAt checkpointChain genesisBlock) prague_covered checkpoint_installed hlA rfl rfl
  have hpre : PreB (bodyPost (benvAt checkpointChain genesisBlock)
      (stHistory (benvAt checkpointChain genesisBlock))) :=
    ⟨hz, hkeep _ (by decide) (by decide) (by decide) (by decide),
      hkeep _ (by decide) (by decide) (by decide) (by decide), hrep, hqueue⟩
  obtain ⟨trace⟩ := witnessBlockTrace checkpoint_ready.last checkpoint_sum_bound rfl rfl rfl
    checkpoint_ready.gasUsed hbody (by decide)
  have blockEq := Blanc.BlockForward.ConfiguredBlockTrace.block_eq trace rfl
  have decoded : trace.bodyTrace.decodedTxs = [] :=
    AppliedBodyTrace.decodedTxs_nil trace.bodyTrace (by rw [blockEq]; rfl)
  exact ⟨_, trace, _, blockOk_of trace checkpoint_callOnly checkpoint_installed
    checkpoint_sum_bound (by rw [blockEq]; rfl) (calls_of_nil _ decoded)
    (ApplyTransactionsTrace.noSender_nil trace.bodyTrace.transactions (by rw [decoded]; rfl) _),
    hpre, chainReady_mk _ _ _ _ _ rfl (by decide)⟩

/-- **Stage B.** -/
theorem stageB {pre : BlockChain} {parent : Block} (ready : ChainReady pre parent)
    (installed : SystemCodeInstalled pre.state) (hworld : CodesCallOnly pre.state.getCode)
    (hbound : sum pre.state.bal < 2 ^ 256) (hpre : PreB pre.state) :
    ∃ (post : BlockChain) (trace : ConfiguredBlockTrace witnessConfig pre post)
      (parent' : Block), BlockOk trace ∧ PreC post.state ∧ ChainReady post parent' := by
  obtain ⟨lh, hl⟩ := blockHashes_getLast_of_ne ready.nonempty
  have hf := benvAt_facts pre parent
  obtain ⟨sB, boutB, hbody, hgas, hpreC⟩ := blockB_run (benv := benvAt pre parent) hf.1
    installed hl hpre hf.2.2.2.2.2.2.1 (hf.2.2.1.trans ready.chainId) hf.2.2.2.1
    (by rw [hf.2.2.2.2.1]; decide) hf.2.2.2.2.2.1
  obtain ⟨trace⟩ := witnessBlockTrace ready.last hbound ready.chainId ready.gasLimit
    ready.baseFee ready.gasUsed hbody (hgas.trans (by decide))
  have blockEq := Blanc.BlockForward.ConfiguredBlockTrace.block_eq trace rfl
  have decoded : trace.bodyTrace.decodedTxs = [txB] :=
    AppliedBodyTrace.decodedTxs_eq_of_txs_eq trace.bodyTrace (by rw [blockEq]; rfl)
  have hchain : (((initBenv trace.fork pre trace.block.header).withState
      trace.bodyTrace.beaconState).withState trace.bodyTrace.historyState).stat.chainId = 1 :=
    ready.chainId
  exact ⟨_, trace, _, blockOk_of trace hworld installed hbound (by rw [blockEq]; rfl)
    (calls_of_single _ decoded rfl rfl)
    (ApplyTransactionsTrace.noSender_single trace.bodyTrace.transactions
      (by rw [decoded]; rfl) (by rw [hchain]; exact txB_recoveredSender)),
    hpreC, chainReady_mk _ _ _ _ _ ready.chainId hgas⟩

/-- **Stage C**, with block C's committed submission frame. -/
theorem stageC {pre : BlockChain} {parent : Block} (ready : ChainReady pre parent)
    (installed : SystemCodeInstalled pre.state) (hworld : CodesCallOnly pre.state.getCode)
    (hbound : sum pre.state.bal < 2 ^ 256) (hpre : PreC pre.state) :
    ∃ (post : BlockChain) (trace : ConfiguredBlockTrace witnessConfig pre post),
      BlockOk trace ∧ ∃ frame ∈ trace.settledFrames.flatMap balanceFrameObservation,
        submissionPaymentFrame frame ∧
        (frame.pre.getStor withdrawalRequestPredeployAddress).get 0 = (2893 : Nat).toB256 ∧
        frame.sevm.value = (2 ^ 245 : Nat).toB256 := by
  obtain ⟨lh, hl⟩ := blockHashes_getLast_of_ne ready.nonempty
  have hf := benvAt_facts pre parent
  obtain ⟨sC, boutC, hbody, hgas⟩ := blockC_run (benv := benvAt pre parent) hf.1
    installed hl hpre (hf.2.2.1.trans ready.chainId) hf.2.2.2.1
    (by rw [hf.2.2.2.2.1]; decide)
  obtain ⟨trace⟩ := witnessBlockTrace ready.last hbound ready.chainId ready.gasLimit
    ready.baseFee ready.gasUsed hbody (hgas.trans (by decide))
  have blockEq := Blanc.BlockForward.ConfiguredBlockTrace.block_eq trace rfl
  have decoded : trace.bodyTrace.decodedTxs = [txC] :=
    AppliedBodyTrace.decodedTxs_eq_of_txs_eq trace.bodyTrace (by rw [blockEq]; rfl)
  -- the transaction's environment is the functional one
  set benv0 := initBenv trace.fork pre trace.block.header with hbenv0
  have hfork0 : CoveredFork benv0.stat.fork := trace.covered
  have hstate0 : benv0.state = pre.state := rfl
  have installed0 : SystemCodeInstalled benv0.state := installed
  have hl0 : benv0.stat.blockHashes.getLast? = some lh := hl
  obtain ⟨-, hH⟩ := AppliedBodyTrace.history_eq trace.bodyTrace hfork0 installed0
  have hready : TxCReady trace.bodyTrace.historyState := by
    rw [hH]
    exact txCReady_stHistory hfork0 installed0 hl0 hpre
  have hchain : benv0.stat.chainId = 1 := ready.chainId
  have hbase : benv0.stat.baseFeePerGas = 1 := by
    show trace.block.header.baseFeePerGas = 1
    rw [blockEq]; rfl
  have hlimit : benv0.stat.blockGasLimit = 2 ^ 29 := by
    show trace.block.header.gasLimit = 2 ^ 29
    rw [blockEq]; rfl
  obtain ⟨st, bo, head, hsub⟩ := ApplyTransactionsTrace.single_head trace.bodyTrace.transactions
    (by rw [decoded]; rfl)
  obtain ⟨frame, hmem, hpay, hpreStor, hvalue⟩ := txC_submissionFrame
    (benv := (benv0.withState trace.bodyTrace.beaconState).withState
      trace.bodyTrace.historyState) head hfork0 hchain
    (by show benv0.stat.baseFeePerGas ≤ 8; rw [hbase]; decide)
    (by show 2 ^ 20 ≤ benv0.stat.blockGasLimit; rw [hlimit]; decide) hready.nonce hready.nocode hready.funds hready.code hready.rep
    σC_submissionBounds (by rw [σC_excess]; decide) σC_run σC_paid (by decide)
  refine ⟨_, trace, blockOk_of trace hworld installed hbound (by rw [blockEq]; rfl)
    (calls_of_single _ decoded rfl rfl)
    (ApplyTransactionsTrace.noSender_single trace.bodyTrace.transactions
      (by rw [decoded]; rfl) (by rw [show ((benv0.withState trace.bodyTrace.beaconState).withState
        trace.bodyTrace.historyState).stat.chainId = 1 from hchain]; exact txC_recoveredSender)),
    frame, ?_, hpay, ?_, hvalue⟩
  · apply List.mem_flatMap.mpr
    refine ⟨frame, ?_, ?_⟩
    · simp only [ConfiguredBlockTrace.settledFrames, AppliedBodyTrace.settledFrames,
        List.mem_append]
      exact Or.inl (Or.inr (hsub frame hmem))
    · unfold balanceFrameObservation
      rw [ite_eq_left hpay.1]
      exact List.mem_singleton_self _
  · rw [hpreStor]
    change (trace.bodyTrace.historyState.getStor withdrawalRequestPredeployAddress).get 0 = _
    rw [hready.rep.excess, σC_excess]

/-- **The refutation of the mathematical-fee guarantee**, with no hypotheses: the three-block
history from the concrete checkpoint (`checkpointChain`) keeps every original hypothesis of
the guarantee and has a committed submission frame that paid its executed word fee with
`2 ^ 245` wei at excess `2893`, strictly less than the Nat fee there. -/
theorem nat_fee_guarantee_refuted : NatFeeGuaranteeRefuted := by
  obtain ⟨chainA, traceA, parentA, okA, preB, readyA⟩ := stageA
  obtain ⟨chainB, traceB, parentB, okB, preC, readyB⟩ :=
    stageB readyA okA.installed okA.world okA.bound preB
  obtain ⟨chainC, traceC, okC, frame, member, payment, excess, value⟩ :=
    stageC readyB okB.installed okB.world okB.bound preC
  exact natFeeGuaranteeRefuted_of_witness
    (RefutationWitness.ofBlocks witnessConfig_valid checkpoint_validContext rfl
      traceA traceB traceC checkpoint_installed okA.senders okB.senders okC.senders
      okA.authorities okB.authorities okC.authorities okA.avoid okB.avoid okC.avoid
      checkpoint_systemEmpty checkpoint_7002_rep frame member payment excess value)
    Blanc.Lift.WithdrawalRequest.word_run_2893_existing
    Blanc.Lift.WithdrawalRequest.word_run_2893_fee
    Blanc.Lift.WithdrawalRequest.word_fee_2893_le_two_pow_245
    Blanc.Lift.WithdrawalRequest.fee_2893
    Blanc.Lift.WithdrawalRequest.two_pow_245_lt_nat_fee_2893

/-- **B is false in the model.** -/
theorem not_natFeeGuarantee : ¬ NatFeeGuarantee :=
  not_natFeeGuarantee_of_refuted nat_fee_guarantee_refuted

end Blanc.Lift.WithdrawalRequest.FeeCounterexample
