import Blanc.Lift.HistoryStorage.Jumps
import Blanc.Lift.HistoryStorage.Prog
import Blanc.Lift.ExactWalkSolc
import Blanc.Lift.WalkSteps
import Blanc.Lift.Vyper
import Blanc.ExecutionTraceSystemCode
import Blanc.ExecutionNoninterference

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
    ∃ post : Devm, SFunc.RunExact fs sevm
      (St b [] M (G + 22 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
          (Sevm.dataWord sevm 0))) t_0046_c0 (.halted post) := by
  refine ⟨St (afterSstore sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
      (Sevm.dataWord sevm 0)) [] M G, ?_⟩
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
    ∃ post : Devm, SFunc.RunExact fs sevm
      (St b [] M (G + 21 + 22 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
          (Sevm.dataWord sevm 0))) t_0000_c0 (.halted post) := by
  obtain ⟨post, hbody⟩ := body_run (fs := fs) (sevm := sevm) (b := b) (M := M)
    (G := G) hfork hstatic hsentry
  refine ⟨post, ?_⟩
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
  processSystemTransactionMsg benv.beginTransaction
    (processSystemTransactionTenv benv.beginTransaction)
    historyStorageAddress (benv.stat.blockHashes.getLast?.getD 0).toBytes historyStorageCode

def systemSevm (benv : Benv) : Sevm := initSevm (systemMsg benv)

def systemBase (benv : Benv) : Devm := initDevm (systemMsg benv)

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

theorem system_exec_exists {benv : Benv} (fork : CoveredFork benv.stat.fork) :
    ∃ post : Devm, exec (initEvm (systemMsg benv)) = .ok post := by
  let sevm := systemSevm benv
  let base := systemBase benv
  let key := (sevm.benvStat.number.toB256 - 1) % (0x1fff : B256)
  let c := sstoreCost sevm base key (Sevm.dataWord sevm 0)
  let G := systemTransactionGas - (43 + c)
  have hgas : systemTransactionGas = 30000000 := by rfl
  have hcost : c ≤ 22100 := by
    dsimp only [c]
    have h := sstoreCost_le sevm base key (Sevm.dataWord sevm 0)
    simp only [gasColdSload, gasStorageSet] at h
    exact h
  have hG : G + 43 + c = systemTransactionGas := by
    dsimp only [G]
    rw [hgas]
    omega
  have hGbound : gCallStipend < G := by
    dsimp only [G]
    rw [hgas]
    norm_num only [gCallStipend]
    omega
  obtain ⟨post, hrun⟩ := root_run (fs := prog) (sevm := sevm) (b := base)
    (M := .empty) (G := G) fork (system_seed benv).2.2.1
    (system_seed benv).1 (by omega)
  have hG' : G + 21 + 22 +
      sstoreCost sevm base ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) = systemTransactionGas := by
    dsimp only [sevm, key, c] at hG ⊢
    omega
  have hrun' : SFunc.RunExact prog sevm
      (St base [] .empty systemTransactionGas) t_0000_c0 (.halted post) := by
    rw [hG'] at hrun
    exact hrun
  have hexec : Nonempty (Exec 0 sevm
      (St base [] .empty systemTransactionGas) (.ok post)) := by
    apply lift_exact cert_check jumps_ok (system_seed benv).2.2.2.1 fork
    exact ⟨t_0000_c0, prog_root, hrun'⟩
  refine ⟨post, ?_⟩
  change exec (initEvm (systemMsg benv)) = .ok post
  change Nonempty (Exec 0 sevm
    (St base [] .empty systemTransactionGas) (.ok post)) at hexec
  have entry : St base [] .empty systemTransactionGas = base := by
    rfl
  rw [entry] at hexec
  exact (exec_iff_exec_eq _ _ _ _).mp hexec

theorem historyStorage_trace_target_of_installed
    {benv : Benv} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv historyStorageAddress
      (benv.stat.blockHashes.getLast?.getD 0).toBytes state out)
    (installed : SystemCodeInstalled benv.state) :
    ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = historyStorageAddress := by
  exact trace.rawFrames_target_of_installed (c := historyStorageCode)
    (by simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
        exact Or.inr (Or.inl trivial)) installed

theorem historyStorage_no_foreign_write {benv : Benv} {pre : Devm} {out : Execution}
    {sevm : Sevm} (run : Exec 0 sevm pre out)
    (hsevm : sevm = systemSevm benv) (owner : Adr) (key : B256)
    (different : historyStorageAddress ≠ owner) :
    Exec.NoRetainedWriteTo run owner key := by
  subst sevm
  obtain ⟨hreach, _, _⟩ := systemContracts_facts (historyStorageAddress, historyStorageCode)
    (by simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
        exact Or.inr (Or.inl trivial))
  apply Exec.noRetainedWriteTo_of_frame_owners_ne run
  intro root member
  have hroot := Exec.rawFrameRoots_of_reach run
    (noPushBefore_zero _ _) hreach root member
  rw [hroot]
  exact different

end Blanc.Lift.HistoryStorage
