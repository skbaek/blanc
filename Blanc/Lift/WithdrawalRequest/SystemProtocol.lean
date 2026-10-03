import Blanc.Lift.WithdrawalRequest.CodeFacts
import Blanc.Lift.WithdrawalRequest.SystemGas
import Blanc.Lift.WithdrawalRequest.SystemStorage
import Blanc.TransactionForward
import Blanc.StorageRefund

/-! Checked protocol execution from the actual system transaction seed. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

def systemProtocolMsg (benv : Benv) : Msg :=
  processSystemTransactionMsg benv.beginTransaction
    (processSystemTransactionTenv benv.beginTransaction)
    withdrawalRequestPredeployAddress [] Blanc.withdrawalRequestCode

def systemProtocolSevm (benv : Benv) : Sevm := initSevm (systemProtocolMsg benv)

def systemProtocolBase (benv : Benv) : Devm := initDevm (systemProtocolMsg benv)

def systemProtocolGas (benv : Benv) : Nat :=
  systemFrameClosedGas (systemProtocolSevm benv) (systemProtocolBase benv) .empty

def systemProtocolPost (benv : Benv) : Devm :=
  systemFramePost (systemProtocolSevm benv) (systemProtocolBase benv) .empty
    (systemTransactionGas - systemProtocolGas benv)

theorem systemProtocol_seed (benv : Benv) :
    (systemProtocolSevm benv).caller = systemAddress ∧
    (systemProtocolSevm benv).currentTarget = withdrawalRequestPredeployAddress ∧
    (systemProtocolSevm benv).isStatic = false ∧
    (systemProtocolSevm benv).code = Blanc.withdrawalRequestCode ∧
    (systemProtocolSevm benv).depth = 1024 ∧
    (systemProtocolBase benv).stack = [] ∧
    (systemProtocolBase benv).memory = .empty ∧
    (systemProtocolBase benv).gasLeft = systemTransactionGas ∧
    (systemProtocolBase benv).refundCounter = 0 ∧
    (systemProtocolBase benv).output = [] ∧
    (systemProtocolBase benv).error = none ∧
    (systemProtocolBase benv).state = benv.state ∧
    (systemProtocolSevm benv).codeAddress = some withdrawalRequestPredeployAddress ∧
    (systemProtocolSevm benv).value = 0 ∧
    (systemProtocolSevm benv).data = [] ∧
    (systemProtocolSevm benv).shouldTransferValue = false ∧
    (systemProtocolSevm benv).disablePrecompiles = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl⟩

theorem systemProtocol_original (benv : Benv) (address : Adr) (key : B256) :
    getOrigStorVal (systemProtocolSevm benv) address key =
      (systemProtocolBase benv).getStorVal address key := by
  rfl

theorem systemProtocol_fork {benv : Benv} (fork : CoveredFork benv.stat.fork) :
    CoveredFork (systemProtocolSevm benv).benvStat.fork := fork

theorem systemProtocol_exec {benv : Benv} (fork : CoveredFork benv.stat.fork) :
    exec (initEvm (systemProtocolMsg benv)) = .ok (systemProtocolPost benv) := by
  have seed := systemProtocol_seed benv
  have run := exec_system_frame_30M (systemProtocolBase benv) seed.2.2.2.1
    (systemProtocol_fork fork) seed.1 seed.2.2.1
  have entry : St (systemProtocolBase benv) [] .empty systemTransactionGas =
      systemProtocolBase benv := by
    rfl
  change Nonempty (Exec 0 (systemProtocolSevm benv)
    (St (systemProtocolBase benv) [] .empty systemTransactionGas)
    (.ok (systemProtocolPost benv))) at run
  rw [entry] at run
  exact (exec_iff_exec_eq _ _ _ _).mp run

theorem withdrawalRequest_not_precompile {fork : Fork} (covered : CoveredFork fork) :
    ¬ (Fork.ruleSet fork).isPrecomp withdrawalRequestPredeployAddress :=
  covered.cases (motive := fun f =>
    ¬ (Fork.ruleSet f).isPrecomp withdrawalRequestPredeployAddress)
    (by decide) (by decide) (by decide) (by decide)

theorem systemProtocol_message {benv : Benv} (fork : CoveredFork benv.stat.fork) :
    processMessage (systemProtocolMsg benv) = .ok (systemProtocolPost benv) := by
  have entry : (systemProtocolMsg benv).benvAfterTransfer = .ok benv.beginTransaction := rfl
  have codeEntry : executeCode.enter ((systemProtocolMsg benv).withBenv benv.beginTransaction) =
      .inl (initEvm ((systemProtocolMsg benv).withBenv benv.beginTransaction)) := by
    have notPrecompile : ¬ benv.stat.rules.isPrecomp withdrawalRequestPredeployAddress :=
      withdrawalRequest_not_precompile fork
    change (if (!false && (benv.stat.rules.isPrecomp withdrawalRequestPredeployAddress)) then _
      else _) = _
    simp only [Bool.not_false, Bool.true_and, notPrecompile, decide_false,
      Bool.false_eq_true, ite_false]
  have self : (systemProtocolMsg benv).withBenv benv.beginTransaction = systemProtocolMsg benv := rfl
  have clean : (systemProtocolPost benv).error = none := by
    rw [systemProtocolPost, systemFramePost_error]
    rfl
  exact MessageExecution.processMessage_clean_of_exec_afterTransfer_of_codeEntry
    _ _ _ entry codeEntry (by rw [self]; exact systemProtocol_exec fork) clean

private theorem systemLoopFold_refund (sevm : Sevm) (head : B256) (index remaining : Nat)
    (base : Devm) (memory : Mem) :
    (systemLoopFold sevm head index remaining base memory).base.refundCounter =
      base.refundCounter := by
  induction remaining generalizing index base memory with
  | zero => rfl
  | succ remaining ih =>
    simp only [systemLoopFold]
    rw [ih]
    simp only [systemBodyBase, systemBodyBase2, systemBodyBase1, afterSload_refundCounter]

private theorem systemQueuePost_refund (sevm : Sevm) (base : Devm) (memory : Mem) :
    (systemQueuePost sevm base memory).base.refundCounter = base.refundCounter := by
  rw [systemQueuePost, systemLoopFold_refund]
  simp only [systemSetupBase, afterSload_refundCounter]

private theorem systemBookkeepingPost_refund (sevm : Sevm) (base : Devm)
    (memory : Mem) (count : B256) (gas : Nat) :
    (systemBookkeepingPost sevm base memory count gas).refundCounter =
      (systemBookkeepingBase sevm base).refundCounter := by
  rw [systemBookkeepingPost]
  generalize systemBookkeepingBase sevm base = written
  rfl

/-- Queue reads can alias metadata, but write none of it. Each subsequent
metadata store is the first write to its own distinct key. -/
theorem systemFramePost_refund_ge (sevm : Sevm) (base : Devm) (memory : Mem) (gas : Nat)
    (original : ∀ key, getOrigStorVal sevm sevm.currentTarget key =
      base.getStorVal sevm.currentTarget key) :
    base.refundCounter ≤ (systemFramePost sevm base memory gas).refundCounter := by
  let queue := (systemQueuePost sevm base memory).base
  let pointers := systemFramePointers sevm base memory
  have queueOriginal (key : B256) : getOrigStorVal sevm sevm.currentTarget key =
      queue.getStorVal sevm.currentTarget key := by
    rw [getStorVal_eq_getStor, systemQueuePost_storage, ← getStorVal_eq_getStor]
    exact original key
  have pointersRefund : queue.refundCounter ≤ pointers.refundCounter := by
    unfold pointers systemFramePointers systemPointerBase
    split
    · have head := afterSstore_refundCounter_ge_of_original_eq_current sevm queue 2 0
        (queueOriginal 2)
      have tailOriginal : getOrigStorVal sevm sevm.currentTarget 3 =
          (afterSstore sevm queue 2 0).getStorVal sevm.currentTarget 3 := by
        rw [getStorVal_eq_getStor, afterSstore_getStor_self,
          Stor.get_set_ne _ (by decide : (2 : B256) ≠ 3), ← getStorVal_eq_getStor]
        exact queueOriginal 3
      exact head.trans (afterSstore_refundCounter_ge_of_original_eq_current
        sevm _ 3 0 tailOriginal)
    · exact afterSstore_refundCounter_ge_of_original_eq_current
        sevm queue 2 _ (queueOriginal 2)
  have pointersOriginal (key : B256) (key2 : (2 : B256) ≠ key) (key3 : (3 : B256) ≠ key) :
      getOrigStorVal sevm sevm.currentTarget key = pointers.getStorVal sevm.currentTarget key := by
    unfold pointers systemFramePointers systemPointerBase
    split
    · rw [getStorVal_eq_getStor, afterSstore_getStor_self, afterSstore_getStor_self,
        Stor.get_set_ne _ key3, Stor.get_set_ne _ key2, ← getStorVal_eq_getStor]
      exact queueOriginal key
    · rw [getStorVal_eq_getStor, afterSstore_getStor_self,
        Stor.get_set_ne _ key2, ← getStorVal_eq_getStor]
      exact queueOriginal key
  have excessOriginal : getOrigStorVal sevm sevm.currentTarget 0 =
      (systemCountRead sevm pointers).getStorVal sevm.currentTarget 0 := by
    simp only [systemCountRead, systemExcessRead, getStorVal_afterSload]
    exact pointersOriginal 0 (by decide) (by decide)
  have countOriginal : getOrigStorVal sevm sevm.currentTarget 1 =
      (systemExcessStore sevm pointers).getStorVal sevm.currentTarget 1 := by
    rw [systemExcessStore, getStorVal_eq_getStor, afterSstore_getStor_self,
      Stor.get_set_ne _ (by decide : (0 : B256) ≠ 1), ← getStorVal_eq_getStor]
    simp only [systemCountRead, systemExcessRead, getStorVal_afterSload]
    exact pointersOriginal 1 (by decide) (by decide)
  have excessRefund := afterSstore_refundCounter_ge_of_original_eq_current
    sevm (systemCountRead sevm pointers) 0 (systemNewExcess sevm pointers) excessOriginal
  have countRefund := afterSstore_refundCounter_ge_of_original_eq_current
    sevm (systemExcessStore sevm pointers) 1 0 countOriginal
  have readsRefund : (systemCountRead sevm pointers).refundCounter = pointers.refundCounter := by
    simp only [systemCountRead, systemExcessRead, afterSload_refundCounter]
  rw [systemFramePost, systemBookkeepingPost_refund]
  change base.refundCounter ≤ (systemBookkeepingBase sevm pointers).refundCounter
  rw [systemBookkeepingBase]
  have initialRefund : base.refundCounter = queue.refundCounter :=
    (systemQueuePost_refund sevm base memory).symm
  change (systemCountRead sevm pointers).refundCounter ≤
    (systemExcessStore sevm pointers).refundCounter at excessRefund
  rw [initialRefund]
  rw [readsRefund] at excessRefund
  exact pointersRefund.trans (excessRefund.trans countRefund)

theorem systemProtocol_refund_nonneg (benv : Benv) :
    0 ≤ (systemProtocolPost benv).refundCounter := by
  exact systemFramePost_refund_ge (systemProtocolSevm benv) (systemProtocolBase benv) .empty _
    (systemProtocol_original benv withdrawalRequestPredeployAddress)

def systemProtocolOutput (benv : Benv) : MsgCallOutput :=
  { gasLeft := (systemProtocolPost benv).gasLeft
    refundCounter := (systemProtocolPost benv).refundCounter
    logs := (systemProtocolPost benv).logs
    accountsToDelete := (systemProtocolPost benv).accountsToDelete
    error := none
    returnData := (systemProtocolPost benv).output }

theorem systemProtocol_call {benv : Benv} (fork : CoveredFork benv.stat.fork) :
    processMessageCall (systemProtocolMsg benv) =
      .ok ((systemProtocolPost benv).state, systemProtocolOutput benv) := by
  have clean : (systemProtocolPost benv).error = none := by
    rw [systemProtocolPost, systemFramePost_error]
    rfl
  have nonneg := systemProtocol_refund_nonneg benv
  have call := processMessageCall_call_of_message
    (msg := systemProtocolMsg benv) (post := systemProtocolPost benv)
    (fork.rules_stateGas_none (s := benv.beginTransaction.stat)) rfl rfl
    withdrawalRequestCode_nondelegated (systemProtocol_message fork) clean
    (Blanc.Int.toNat?_eq_some_of_nonneg nonneg)
  simpa only [systemProtocolOutput, Nat.zero_add, Int.toNat_of_nonneg nonneg] using call

/-- Actual checked protocol success on every covered fork, independently of
queue representation or reachability. Installed canonical code is sufficient. -/
theorem processCheckedSystemTransaction_withdrawal {benv : Benv}
    (fork : CoveredFork benv.stat.fork)
    (installed : benv.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode) :
    processCheckedSystemTransaction benv withdrawalRequestPredeployAddress [] =
      .ok ((systemProtocolPost benv).state, systemProtocolOutput benv) := by
  unfold processCheckedSystemTransaction
  simp only [installed, withdrawalRequestCode_nonempty, Bool.false_eq_true, ite_false]
  have system : processSystemTransaction benv withdrawalRequestPredeployAddress
      Blanc.withdrawalRequestCode [] =
        .ok ((systemProtocolPost benv).state, systemProtocolOutput benv) :=
    systemProtocol_call fork
  rw [system]
  rfl

theorem systemProtocolOutput_facts (benv : Benv) :
    (systemProtocolOutput benv).error = none ∧
    (systemProtocolOutput benv).gasLeft = systemTransactionGas - systemProtocolGas benv ∧
    (systemProtocolOutput benv).returnData = (systemProtocolPost benv).output ∧
    (systemProtocolOutput benv).refundCounter = (systemProtocolPost benv).refundCounter := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  change (systemProtocolPost benv).gasLeft = _
  rw [systemProtocolPost, systemFramePost, systemBookkeepingPost,
    (returnPost_facts _ _ _ _).2.2.2]
  rfl

theorem systemProtocolGas_le (benv : Benv) : systemProtocolGas benv ≤ 210000 := by
  have bound := systemFrameGas_le (systemProtocolSevm benv) (systemProtocolBase benv)
    (memory := Mem.empty) rfl
  rw [systemFrameGas_closed _ _ _ rfl] at bound
  exact bound

/-- The exact checked result includes the selected-cost formula, RETURN
bytes and the raw nonnegative refund; neither checked error arm is possible. -/
theorem checked_system_totality {benv : Benv} (fork : CoveredFork benv.stat.fork)
    (installed : benv.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode) :
    processCheckedSystemTransaction benv withdrawalRequestPredeployAddress [] =
      .ok ((systemProtocolPost benv).state, systemProtocolOutput benv) ∧
    (systemProtocolOutput benv).error = none ∧
    (systemProtocolOutput benv).gasLeft = systemTransactionGas - systemProtocolGas benv ∧
    systemProtocolGas benv ≤ 210000 ∧
    (systemProtocolOutput benv).returnData = (systemProtocolPost benv).output ∧
    (systemProtocolOutput benv).refundCounter = (systemProtocolPost benv).refundCounter := by
  have fields := systemProtocolOutput_facts benv
  exact ⟨processCheckedSystemTransaction_withdrawal fork installed, fields.1, fields.2.1,
    systemProtocolGas_le benv, fields.2.2⟩

/-- Conditional FIFO encoding reuses the already-built raw image theorem. -/
theorem systemProtocolOutput_represented (benv : Benv) (state : Blanc.WithdrawalRequest.State)
    (rep : Blanc.WithdrawalRequest.RepresentsStorage
      ((systemProtocolBase benv).getStorVal withdrawalRequestPredeployAddress) state) :
    (systemProtocolOutput benv).returnData = Blanc.WithdrawalRequest.systemOutput state := by
  change (systemProtocolPost benv).output = _
  exact systemFramePost_output_represented (systemProtocolSevm benv) (systemProtocolBase benv)
    .empty _ state rep (Nat.zero_le 0) (image := []) (by intro i; rfl)

end Blanc.Lift.WithdrawalRequest
