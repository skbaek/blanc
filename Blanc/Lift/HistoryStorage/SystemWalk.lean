import Blanc.Lift.HistoryStorage.Jumps
import Blanc.Lift.HistoryStorage.Prog
import Blanc.Lift.ExactWalkSolc
import Blanc.Lift.WalkSteps
import Blanc.Lift.Vyper
import Blanc.ExecutionTraceSystemCode
import Blanc.ExecutionNoninterference
import Blanc.SystemCallForward
import Blanc.StorageRefund

namespace Blanc.Lift.HistoryStorage

open Jaune
open ExecutionTrace
open Blanc.Lift

private theorem system_push :
    Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe] =
      systemAddress.toB256 := rfl

theorem body_run {fs : List SFunc} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hsentry : gCallStipend < G +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) :
    SFunc.RunExact fs sevm
      (St b [] M (G + 22 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
          (Sevm.dataWord sevm 0))) t_0046_c0
      (.halted (St (afterSstore sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) [] M G)) := by
  dsimp only [t_0046_c0]
  rw [show G + 22 +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 21 + sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) + 1 by omega]
  rdest
  rw [show G + 21 +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 19 + sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) + 2 by omega]
  refine rx_push0 (S := []) (by decide) ?_
  rw [show G + 19 +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 16 + sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_calldataload (S := []) (x := 0) (by decide) ?_
  rw [show G + 16 +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 13 + sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_push (S := [Sevm.dataWord sevm 0]) (x := 0x1f) (xs := [0xff])
    (w := (0x1fff : B256)) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  rw [show G + 13 +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 10 + sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_push (S := [(0x1fff : B256), Sevm.dataWord sevm 0])
    (x := 0x01) (xs := []) (w := 1) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  rw [show G + 10 +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 8 + sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) + 2 by omega]
  refine rx_number (S := [1, (0x1fff : B256), Sevm.dataWord sevm 0])
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  rw [show G + 8 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 5 + sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_sub (S := [(0x1fff : B256), Sevm.dataWord sevm 0])
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  rw [show G + 5 +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) + 5 by omega]
  refine rx_mod (S := [Sevm.dataWord sevm 0]) (by rfl)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_sstore hfork hsentry hstatic ?_
  exact Blanc.Lift.rx_stop

theorem root_run {fs : List SFunc} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hcaller : sevm.caller = systemAddress)
    (hsentry : gCallStipend < G +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) :
    SFunc.RunExact fs sevm
      (St b [] M (G + 21 + 22 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
          (Sevm.dataWord sevm 0))) t_0000_c0
      (.halted (St (afterSstore sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) [] M G)) := by
  have hbody := body_run (fs := fs) (sevm := sevm) (b := b) (M := M)
    (G := G) hfork hstatic hsentry
  dsimp only [t_0000_c0]
  rw [show G + 21 + 22 +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 19 + 22 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 2 by omega]
  refine rx_caller (S := []) (by decide) ?_
  rw [show G + 19 + 22 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 16 + 22 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_push (S := [sevm.caller.toB256]) system_push
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  rw [show G + 16 + 22 +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 13 + 22 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_eq (by rw [hcaller])
    (by decide) ?_
  rw [show G + 13 + 22 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 10 + 22 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_push rfl (by decide) ?_
  rw [show G + 10 + 22 +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 22 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 10 by omega]
  exact rx_branch_succ (by decide) hbody

def systemMsg (benv : Benv) : Msg :=
  systemCallMsg benv historyStorageAddress historyStorageCode
    (benv.stat.blockHashes.getLast?.getD 0).toBytes

def systemSevm (benv : Benv) : Sevm := initSevm (systemMsg benv)

def systemBase (benv : Benv) : Devm := initDevm (systemMsg benv)

/-- The ring-buffer slot the SYSTEM call writes: `(number - 1) mod 8191`. -/
def systemKey (benv : Benv) : B256 :=
  ((systemSevm benv).benvStat.number.toB256 - 1) % (0x1fff : B256)

/-- The parent hash the SYSTEM call stores. -/
def systemValue (benv : Benv) : B256 := Sevm.dataWord (systemSevm benv) 0

def systemCost (benv : Benv) : Nat :=
  sstoreCost (systemSevm benv) (systemBase benv) (systemKey benv) (systemValue benv)

/-- The exact halted frame of the SYSTEM call. -/
def systemPost (benv : Benv) : Devm :=
  St (afterSstore (systemSevm benv) (systemBase benv) (systemKey benv) (systemValue benv))
    [] .empty (systemTransactionGas - (43 + systemCost benv))

theorem system_seed (benv : Benv) :
    (systemSevm benv).caller = systemAddress ∧
    (systemSevm benv).currentTarget = historyStorageAddress ∧
    (systemSevm benv).isStatic = false ∧
    (systemSevm benv).code = historyStorageCode ∧
    (systemSevm benv).depth = 1024 ∧
    (systemBase benv).stack = [] ∧
    (systemBase benv).memory = .empty ∧
    (systemBase benv).gasLeft = systemTransactionGas ∧
    (systemBase benv).refundCounter = 0 ∧
    (systemBase benv).output = [] ∧
    (systemBase benv).error = none ∧
    (systemBase benv).state = benv.state ∧
    (systemSevm benv).codeAddress = some historyStorageAddress := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem system_exec {benv : Benv} (fork : CoveredFork benv.stat.fork) :
    exec (initEvm (systemMsg benv)) = .ok (systemPost benv) := by
  let sevm := systemSevm benv
  let base := systemBase benv
  let c := systemCost benv
  let G := systemTransactionGas - (43 + c)
  have hgas : systemTransactionGas = 30000000 := by rfl
  have hcost : c ≤ 22100 := by
    dsimp only [c, systemCost]
    have h := sstoreCost_le sevm base (systemKey benv) (systemValue benv)
    simp only [gasColdSload, gasStorageSet] at h
    exact h
  have hGbound : gCallStipend < G := by
    dsimp only [G]
    rw [hgas]
    norm_num only [gCallStipend]
    omega
  have hrun := root_run (fs := prog) (sevm := sevm) (b := base)
    (M := .empty) (G := G) fork (system_seed benv).2.2.1
    (system_seed benv).1 (by omega)
  have hG' : G + 21 + 22 +
      sstoreCost sevm base ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) = systemTransactionGas := by
    change G + 21 + 22 + c = systemTransactionGas
    dsimp only [G]
    rw [hgas]
    omega
  have hrun' : SFunc.RunExact prog sevm
      (St base [] .empty systemTransactionGas) t_0000_c0 (.halted (systemPost benv)) := by
    rw [hG'] at hrun
    exact hrun
  have hexec : Nonempty (Exec 0 sevm
      (St base [] .empty systemTransactionGas) (.ok (systemPost benv))) := by
    apply lift_exact cert_check jumps_ok (system_seed benv).2.2.2.1 fork
    exact ⟨t_0000_c0, prog_root, hrun'⟩
  change Nonempty (Exec 0 sevm
    (St base [] .empty systemTransactionGas) (.ok (systemPost benv))) at hexec
  have entry : St base [] .empty systemTransactionGas = base := by
    rfl
  rw [entry] at hexec
  exact (exec_iff_exec_eq _ _ _ _).mp hexec

theorem member : (historyStorageAddress, historyStorageCode) ∈ systemContracts := by
  simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
  exact Or.inr (Or.inl trivial)

/-- The SYSTEM frame halts cleanly, with a non-negative refund counter, having
written exactly one slot of its own storage. -/
theorem systemPost_facts (benv : Benv) :
    (systemPost benv).error = none ∧
    0 ≤ (systemPost benv).refundCounter ∧
    (systemPost benv).state =
      benv.state.setStorVal historyStorageAddress (systemKey benv) (systemValue benv) := by
  refine ⟨?_, ?_, ?_⟩
  · change (afterSstore (systemSevm benv) (systemBase benv) _ _).error = none
    rw [afterSstore_error]
    rfl
  · change 0 ≤ (afterSstore (systemSevm benv) (systemBase benv) _ _).refundCounter
    exact afterSstore_refundCounter_ge_of_original_eq_current _ _ _ _ rfl
  · change (afterSstore (systemSevm benv) (systemBase benv) _ _).state = _
    rw [afterSstore_state]
    rfl

/-- **The EIP-2935 unchecked system call** on the real installed code: it succeeds and
its state is the input state with one history slot written, so every other account is
untouched. -/
theorem processUncheckedSystemTransaction_historyStorage {benv : Benv} {lastHash : B256}
    (fork : CoveredFork benv.stat.fork)
    (installed : benv.state.getCode historyStorageAddress = historyStorageCode)
    (last : benv.stat.blockHashes.getLast? = some lastHash) :
    processUncheckedSystemTransaction benv historyStorageAddress lastHash.toBytes =
      .ok ((systemPost benv).state, systemCallOutput (systemPost benv)) ∧
    (systemPost benv).state =
      benv.state.setStorVal historyStorageAddress (systemKey benv) (systemValue benv) ∧
    ∀ a, historyStorageAddress ≠ a → (systemPost benv).state.get a = benv.state.get a := by
  have facts := systemPost_facts benv
  have data : lastHash.toBytes = (benv.stat.blockHashes.getLast?.getD 0).toBytes := by
    rw [last]
    rfl
  refine ⟨?_, facts.2.2, fun a different => ?_⟩
  · rw [data]
    exact processUncheckedSystemTransaction_of_exec member fork installed (system_exec fork)
      facts.1 facts.2.1
  · rw [facts.2.2, State.get_setStorVal_ne _ _ _ different]

theorem historyStorage_trace_target_of_installed
    {benv : Benv} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv historyStorageAddress
      (benv.stat.blockHashes.getLast?.getD 0).toBytes state out)
    (installed : SystemCodeInstalled benv.state) :
    ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = historyStorageAddress := by
  exact trace.rawFrames_target_of_installed (c := historyStorageCode)
    member installed

theorem historyStorage_no_foreign_write {benv : Benv} {pre : Devm} {out : Execution}
    {sevm : Sevm} (run : Exec 0 sevm pre out)
    (hsevm : sevm = systemSevm benv) (owner : Adr) (key : B256)
    (different : historyStorageAddress ≠ owner) :
    Exec.NoRetainedWriteTo run owner key := by
  subst sevm
  obtain ⟨hreach, _, _⟩ := systemContracts_facts _ member
  apply Exec.noRetainedWriteTo_of_frame_owners_ne run
  intro root member
  have hroot := Exec.rawFrameRoots_of_reach run
    (noPushBefore_zero _ _) hreach root member
  rw [hroot]
  exact different

end Blanc.Lift.HistoryStorage
