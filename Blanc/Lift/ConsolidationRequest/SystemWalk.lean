import Blanc.Lift.ConsolidationRequest.Jumps
import Blanc.Lift.ConsolidationRequest.Prog
import Blanc.Lift.ExactWalkSolc
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.CreationOps
import Blanc.Lift.WalkSteps
import Blanc.Lift.Vyper
import Blanc.Lift.Deploy
import Blanc.ForwardStorageAccess
import Blanc.StorageAccessGas
import Blanc.ExecutionTraceSystemCode
import Blanc.ExecutionNoninterference
import Blanc.SystemCallForward
import Blanc.StorageRefund

/-! The EIP-7251 SYSTEM path with an empty queue.

With excess, count, head and tail all zero, and slot 0 below the inhibitor,
the frame reads slots 3 and 2, skips the loop, zeroes slots 2 and 3, reads
slots 0 and 1, takes the no-excess branch, zeroes slots 0 and 1, and returns
the empty window (`0x74` times the zero slot-0 excess). The walk mirrors
the 7002 kit's setup and
bookkeeping segments (`Blanc.Lift.WithdrawalRequest.SystemSetup`,
`Blanc.Lift.WithdrawalRequest.SystemBookkeeping`); only the entry indices,
branch constants and the return size differ. -/

namespace Blanc.Lift.ConsolidationRequest

open Jaune
open ExecutionTrace
open Blanc.Lift

private theorem system_push :
    Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe] =
      systemAddress.toB256 := rfl

/-- Exact meta-state after reading tail first, then head. -/
def setupBase (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm (afterSload sevm b 3) 2

/-- Exact meta-state after zeroing slots 2 then 3. -/
def ptrBase (sevm : Sevm) (b : Devm) : Devm :=
  afterSstore sevm (afterSstore sevm b 2 0) 3 0

/-- Exact meta-state after reading slot 0. -/
def excessBase (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm b 0

/-- Exact meta-state after reading slot 1. -/
def countBase (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm b 1

/-- Exact meta-state after zeroing slot 0. -/
def storeBase (sevm : Sevm) (b : Devm) : Devm :=
  afterSstore sevm b 0 0

/-- Exact meta-state after zeroing slot 1. -/
def bookBase (sevm : Sevm) (b : Devm) : Devm :=
  afterSstore sevm b 1 0

/-- Root prefix through the queue-diff branch: two JUMPDESTs, ten very-low
steps, one JUMPI and the pushes. -/
def setupGas (sevm : Sevm) (b : Devm) : Nat :=
  59 + sloadCost sevm b 3 + sloadCost sevm (afterSload sevm b 3) 2

/-- Loop-index check and exit branch. -/
def exitGas : Nat := 26

/-- Head-advance check and the two pointer stores. -/
def ptrGas (sevm : Sevm) (b : Devm) : Nat :=
  45 + sstoreCost sevm b 2 0 + sstoreCost sevm (afterSstore sevm b 2 0) 3 0

/-- Slot-0 read and the inhibitor branch. -/
def excessGas (sevm : Sevm) (b : Devm) : Nat :=
  28 + sloadCost sevm b 0

/-- Slot-1 read, the no-excess branch and the jump to the tail. -/
def countGas (sevm : Sevm) (b : Devm) : Nat :=
  49 + sloadCost sevm b 1

/-- The two final stores and the empty RETURN window (`RETURN` charges exactly
the expansion, which is zero here). -/
def finalGas (sevm : Sevm) (b : Devm) : Nat :=
  18 + sstoreCost sevm b 0 0 + sstoreCost sevm (afterSstore sevm b 0 0) 1 0

private theorem prog_1 : prog[1]? = some t_00e7_c1 := rfl

private theorem prog_3 : prog[3]? = some t_0173_c3 := rfl

private theorem prog_4 : prog[4]? = some t_018e_c4 := rfl

def systemMsg (benv : Benv) : Msg :=
  systemCallMsg benv consolidationRequestPredeployAddress consolidationRequestCode []

def systemSevm (benv : Benv) : Sevm := initSevm (systemMsg benv)

def systemBase (benv : Benv) : Devm := initDevm (systemMsg benv)

/-- The whole walk's storage and memory charge. -/
def systemCost (benv : Benv) : Nat :=
  setupGas (systemSevm benv) (systemBase benv) + exitGas +
    ptrGas (systemSevm benv) (setupBase (systemSevm benv) (systemBase benv)) +
    excessGas (systemSevm benv)
      (ptrBase (systemSevm benv) (setupBase (systemSevm benv) (systemBase benv))) +
    countGas (systemSevm benv)
      (excessBase (systemSevm benv)
        (ptrBase (systemSevm benv) (setupBase (systemSevm benv) (systemBase benv)))) +
    finalGas (systemSevm benv)
      (countBase (systemSevm benv)
        (excessBase (systemSevm benv)
          (ptrBase (systemSevm benv) (setupBase (systemSevm benv) (systemBase benv)))))

/-- The exact halted frame of the SYSTEM call: four slots zeroed, empty
return data. -/
def systemPost (benv : Benv) : Devm :=
  returnPost
    (St (bookBase (systemSevm benv)
      (storeBase (systemSevm benv)
        (countBase (systemSevm benv)
          (excessBase (systemSevm benv)
            (ptrBase (systemSevm benv) (setupBase (systemSevm benv) (systemBase benv)))))))
      [0, 0] .empty (systemTransactionGas - systemCost benv))
    0 0 []

theorem system_seed (benv : Benv) :
    (systemSevm benv).caller = systemAddress ∧
    (systemSevm benv).currentTarget = consolidationRequestPredeployAddress ∧
    (systemSevm benv).isStatic = false ∧
    (systemSevm benv).code = consolidationRequestCode ∧
    (systemSevm benv).depth = 1024 ∧
    (systemBase benv).stack = [] ∧
    (systemBase benv).memory = .empty ∧
    (systemBase benv).gasLeft = systemTransactionGas ∧
    (systemBase benv).refundCounter = 0 ∧
    (systemBase benv).output = [] ∧
    (systemBase benv).error = none ∧
    (systemBase benv).state = benv.state ∧
    (systemSevm benv).codeAddress = some consolidationRequestPredeployAddress := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem member :
    (consolidationRequestPredeployAddress, consolidationRequestCode) ∈ systemContracts := by
  simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
  exact Or.inr (Or.inr (Or.inr trivial))

/-- The tail: zero slots 0 and 1, then RETURN the empty window. The size
factor is a threaded zero, so the window is empty. -/
theorem tail_run {sevm : Sevm} {b : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hsentry : gCallStipend < G) :
    SFunc.RunExact prog sevm
      (St b [(0 : B256), 0] .empty (G + finalGas sevm b))
      t_018e_c4
      (.halted (returnPost
        (St (bookBase sevm (storeBase sevm b)) [0, 0] .empty G)
        0 0 [])) := by
  have hmul : (0x74 : B256) * 0 = 0 := by
    decide
  have hext : (St (bookBase sevm (storeBase sevm b)) [0, 0] .empty G).extCost
      [⟨(0 : B256).toNat, (0 : B256).toNat⟩] = 0 := by
    rw [St.extCost_eq rfl]
    decide
  have terminal : SFunc.RunExact prog sevm
      (St (bookBase sevm (storeBase sevm b)) [0, 0] .empty G)
      (.last .return_)
      (.halted (returnPost
        (St (bookBase sevm (storeBase sevm b)) [0, 0] .empty G)
        0 0 [])) :=
    rx_return hext rfl
  have gasEq : G + finalGas sevm b =
      G + 2 + 5 + 3 +
        sstoreCost sevm (afterSstore sevm b 0 0) 1 0 + 3 + 2 +
        sstoreCost sevm b 0 0 + 2 + 1 := by
    unfold finalGas
    omega
  rw [gasEq]
  unfold t_018e_c4
  apply rx_dest
  apply rx_push0 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_sstore hfork (by omega) hstatic
  apply rx_push0 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := (1 : B256)) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_sstore hfork (by omega) hstatic
  apply rx_push (w := (0x74 : B256)) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_mul hmul (by simp only [List.length_nil]; decide)
  apply rx_push0 (by simp only [List.length_cons, List.length_nil]; decide)
  exact terminal

/-- The no-excess branch: read slot 1, find nothing pending, jump to the tail. -/
theorem noexcess_run {sevm : Sevm} {b : Devm} {G : Nat} {s0 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hsentry : gCallStipend < G)
    (hs1 : b.getStorVal sevm.currentTarget 1 = 0)
    (hs0 : s0 = 0) :
    SFunc.RunExact prog sevm (St b [s0, (0 : B256)] .empty
        (G + (countGas sevm b + finalGas sevm (countBase sevm b))))
      t_0173_c3
      (.halted (returnPost
        (St (bookBase sevm (storeBase sevm (countBase sevm b))) [0, 0] .empty G)
        0 0 [])) := by
  have hsum : b.getStorVal sevm.currentTarget 1 + s0 = 0 := by
    rw [hs1, hs0]
    decide
  have hgt0 : B256.gtCheck (b.getStorVal sevm.currentTarget 1 + s0) 1 = 0 := by
    rw [hsum]
    decide
  have gasEq : G + (countGas sevm b + finalGas sevm (countBase sevm b)) =
      (G + finalGas sevm (countBase sevm b)) + 8 + 3 + 2 + 2 + 2 + 10 + 3 + 3 +
        3 + 3 + 3 + 3 + sloadCost sevm b 1 + 3 + 1 := by
    unfold countGas
    omega
  rw [gasEq]
  unfold t_0173_c3
  apply rx_dest
  apply rx_push (w := (1 : B256)) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_sload_sel hfork
    (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := (1 : B256)) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_dup3 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_dup3 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_add (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_gt hgt0 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := (0x188 : B256)) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_branch_zero
  unfold t_0181_c3
  apply rx_pop
  apply rx_pop
  apply rx_push0 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := (0x18e : B256)) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide)
  refine rx_jump prog_4 ?_
  simpa only [countBase] using
    tail_run (b := countBase sevm b) hfork hstatic hsentry

/-- The excess read: slot 0 is below the inhibitor, so jump to entry 3. -/
theorem excessread_run {sevm : Sevm} {b : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hsentry : gCallStipend < G)
    (hs0z : b.getStorVal sevm.currentTarget 0 = 0)
    (hs1e : (excessBase sevm b).getStorVal sevm.currentTarget 1 = 0) :
    SFunc.RunExact prog sevm (St b [(0 : B256)] .empty
        (G + (excessGas sevm b +
          (countGas sevm (excessBase sevm b) +
            finalGas sevm (countBase sevm (excessBase sevm b))))))
      t_0146_c2
      (.halted (returnPost
        (St (bookBase sevm (storeBase sevm (countBase sevm (excessBase sevm b))))
          [0, 0] .empty G)
        0 0 [])) := by
  have h0ne : B256.max ≠ b.getStorVal sevm.currentTarget 0 := by
    rw [hs0z]
    decide
  have he0 : B256.eqCheck B256.max (b.getStorVal sevm.currentTarget 0) = 0 := by
    simp only [B256.eqCheck, ite_eq_right h0ne]
  have hisz0 : B256.eqCheck 0 0 = 1 := by decide
  have gasEq : G + (excessGas sevm b +
      (countGas sevm (excessBase sevm b) +
        finalGas sevm (countBase sevm (excessBase sevm b)))) =
      (G + (countGas sevm (excessBase sevm b) +
        finalGas sevm (countBase sevm (excessBase sevm b)))) +
        10 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b 0 + 2 + 1 := by
    unfold excessGas
    omega
  rw [gasEq]
  unfold t_0146_c2
  apply rx_dest
  apply rx_push0 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_sload_sel hfork
    (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := B256.max) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_eq he0 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_iszero hisz0 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := (0x173 : B256)) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide)
  refine rx_branchTo_succ (by decide) prog_3 ?_
  simpa only [excessBase] using
    noexcess_run (b := excessBase sevm b) (s0 := b.getStorVal sevm.currentTarget 0)
      hfork hstatic hsentry hs1e hs0z

/-- The head-advance check and the two pointer stores. -/
theorem ptr_run {sevm : Sevm} {b : Devm} {G : Nat} {q s2 s3 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hsentry : gCallStipend < G)
    (hq : q = 0) (hs2 : s2 = 0) (hs3 : s3 = 0)
    (hs0b : b.getStorVal sevm.currentTarget 0 = 0)
    (hs1b : b.getStorVal sevm.currentTarget 1 = 0) :
    SFunc.RunExact prog sevm (St b [0, q, s2, s3] .empty
        (G + (ptrGas sevm b +
          (excessGas sevm (ptrBase sevm b) +
            (countGas sevm (excessBase sevm (ptrBase sevm b)) +
              finalGas sevm (countBase sevm (excessBase sevm (ptrBase sevm b))))))))
      t_0129_c1
      (.halted (returnPost
        (St (bookBase sevm (storeBase sevm (countBase sevm (excessBase sevm (ptrBase sevm b)))))
          [0, 0] .empty G)
        0 0 [])) := by
  have heq129 : B256.eqCheck s3 (s2 + q) = 1 := by
    rw [hs3, hs2, hq]
    decide
  have h30 : (3 : B256) ≠ 0 := by decide
  have h20 : (2 : B256) ≠ 0 := by decide
  have h31 : (3 : B256) ≠ 1 := by decide
  have h21 : (2 : B256) ≠ 1 := by decide
  have hs0z : (ptrBase sevm b).getStorVal sevm.currentTarget 0 = 0 := by
    rw [ptrBase, getStorVal_eq_getStor, afterSstore_getStor_self,
      afterSstore_getStor_self, Stor.get_set_ne _ h30, Stor.get_set_ne _ h20,
      ← getStorVal_eq_getStor]
    exact hs0b
  have hs1e : (excessBase sevm (ptrBase sevm b)).getStorVal sevm.currentTarget 1 = 0 := by
    rw [excessBase, getStorVal_afterSload, ptrBase, getStorVal_eq_getStor,
      afterSstore_getStor_self, afterSstore_getStor_self,
      Stor.get_set_ne _ h31, Stor.get_set_ne _ h21, ← getStorVal_eq_getStor]
    exact hs1b
  have gasEq : G + (ptrGas sevm b +
      (excessGas sevm (ptrBase sevm b) +
        (countGas sevm (excessBase sevm (ptrBase sevm b)) +
          finalGas sevm (countBase sevm (excessBase sevm (ptrBase sevm b)))))) =
      (G + (excessGas sevm (ptrBase sevm b) +
        (countGas sevm (excessBase sevm (ptrBase sevm b)) +
          finalGas sevm (countBase sevm (excessBase sevm (ptrBase sevm b)))))) +
        sstoreCost sevm (afterSstore sevm b 2 0) 3 0 + 3 + 2 +
        sstoreCost sevm b 2 0 + 3 + 2 + 2 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 +
        3 + 1 := by
    unfold ptrGas
    omega
  rw [gasEq]
  unfold t_0129_c1
  apply rx_dest
  apply rx_swap2
  apply rx_add (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_swap3
  apply rx_eq heq129 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := (0x13b : B256)) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_branch_succ (by decide)
  unfold t_013b_c1
  apply rx_dest
  apply rx_swap1
  apply rx_pop
  apply rx_push0 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := (2 : B256)) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_sstore hfork (by omega) hstatic
  apply rx_push0 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := (3 : B256)) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_sstore hfork (by omega) hstatic
  simpa only [ptrBase] using
    excessread_run (b := ptrBase sevm b)
      hfork hstatic hsentry hs0z hs1e

/-- The caller check passes for the system caller. -/
private theorem caller_eqCheck_sys {sevm : Sevm} (hcall : sevm.caller = systemAddress) :
    B256.eqCheck systemAddress.toB256 sevm.caller.toB256 = 1 := by
  simp only [hcall, B256.eqCheck, ite_true]

/-- The index check: the queue diff is zero, so jump to the head-advance check. -/
theorem exit_run {sevm : Sevm} {b : Devm} {G : Nat} {d s2 s3 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hsentry : gCallStipend < G)
    (hd : d = 0) (hs2 : s2 = 0) (hs3 : s3 = 0)
    (hs0b : b.getStorVal sevm.currentTarget 0 = 0)
    (hs1b : b.getStorVal sevm.currentTarget 1 = 0) :
    SFunc.RunExact prog sevm (St b [d, s2, s3] .empty
        (G + (exitGas +
          (ptrGas sevm b +
            (excessGas sevm (ptrBase sevm b) +
              (countGas sevm (excessBase sevm (ptrBase sevm b)) +
                finalGas sevm (countBase sevm (excessBase sevm (ptrBase sevm b)))))))))
      t_00e7_c1
      (.halted (returnPost
        (St (bookBase sevm (storeBase sevm (countBase sevm (excessBase sevm (ptrBase sevm b)))))
          [0, 0] .empty G)
        0 0 [])) := by
  have heq : B256.eqCheck 0 d = 1 := by
    rw [hd]
    decide
  have gasEq : G + (exitGas +
      (ptrGas sevm b +
        (excessGas sevm (ptrBase sevm b) +
          (countGas sevm (excessBase sevm (ptrBase sevm b)) +
            finalGas sevm (countBase sevm (excessBase sevm (ptrBase sevm b))))))) =
      (G + (ptrGas sevm b +
        (excessGas sevm (ptrBase sevm b) +
          (countGas sevm (excessBase sevm (ptrBase sevm b)) +
            finalGas sevm (countBase sevm (excessBase sevm (ptrBase sevm b))))))) +
        1 + 2 + 1 + 3 + 3 + 3 + 3 + 10 := by
    unfold exitGas
    omega
  rw [gasEq]
  unfold t_00e7_c1
  apply rx_dest
  apply rx_push0 (by simp only [List.length_cons, List.length_nil]; decide)
  unfold t_00e9_c1
  apply rx_dest
  apply rx_dup2 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_dup2 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_eq heq (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := (0x129 : B256)) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_branch_succ (by decide)
  exact ptr_run (b := b) (q := d) hfork hstatic hsentry hd hs2 hs3 hs0b hs1b

/-- The root prefix: system-caller check, queue-pointer reads and the jump
to the index check. -/
theorem setup_run {sevm : Sevm} {b : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hsentry : gCallStipend < G) (hcall : sevm.caller = systemAddress)
    (hs3 : b.getStorVal sevm.currentTarget 3 = 0)
    (hs2 : (afterSload sevm b 3).getStorVal sevm.currentTarget 2 = 0)
    (hs0b : (setupBase sevm b).getStorVal sevm.currentTarget 0 = 0)
    (hs1b : (setupBase sevm b).getStorVal sevm.currentTarget 1 = 0) :
    SFunc.RunExact prog sevm (St b [] .empty
        (G + (setupGas sevm b +
          (exitGas +
            (ptrGas sevm (setupBase sevm b) +
              (excessGas sevm (ptrBase sevm (setupBase sevm b)) +
                (countGas sevm (excessBase sevm (ptrBase sevm (setupBase sevm b))) +
                  finalGas sevm (countBase sevm
                    (excessBase sevm (ptrBase sevm (setupBase sevm b)))))))))))
      t_0000_c0
      (.halted (returnPost
        (St (bookBase sevm (storeBase sevm
          (countBase sevm (excessBase sevm (ptrBase sevm (setupBase sevm b))))))
          [0, 0] .empty G)
        0 0 [])) := by
  have hd : b.getStorVal sevm.currentTarget 3 -
      (afterSload sevm b 3).getStorVal sevm.currentTarget 2 = 0 := by
    rw [hs3, hs2]
    decide
  have hgt : B256.gtCheck 2 (b.getStorVal sevm.currentTarget 3 -
      (afterSload sevm b 3).getStorVal sevm.currentTarget 2) = 1 := by
    rw [hd]
    decide
  have gasEq : G + (setupGas sevm b +
      (exitGas +
        (ptrGas sevm (setupBase sevm b) +
          (excessGas sevm (ptrBase sevm (setupBase sevm b)) +
            (countGas sevm (excessBase sevm (ptrBase sevm (setupBase sevm b))) +
              finalGas sevm (countBase sevm
                (excessBase sevm (ptrBase sevm (setupBase sevm b))))))))) =
      (G + (exitGas +
        (ptrGas sevm (setupBase sevm b) +
          (excessGas sevm (ptrBase sevm (setupBase sevm b)) +
            (countGas sevm (excessBase sevm (ptrBase sevm (setupBase sevm b))) +
              finalGas sevm (countBase sevm
                (excessBase sevm (ptrBase sevm (setupBase sevm b))))))))) +
        10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 +
        sloadCost sevm (afterSload sevm b 3) 2 + 3 + sloadCost sevm b 3 + 3 + 1 +
        10 + 3 + 3 + 3 + 2 := by
    unfold setupGas
    omega
  rw [gasEq]
  unfold t_0000_c0
  apply rx_caller (by decide)
  refine rx_push system_push (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_eq (caller_eqCheck_sys hcall)
    (by simp only [List.length_nil]; decide) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_00d3_c0
  apply rx_dest
  apply rx_push (w := (3 : B256)) (by decide)
    (by simp only [List.length_nil]; decide)
  apply rx_sload_sel hfork
    (by simp only [List.length_nil]; decide)
  apply rx_push (w := (2 : B256)) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_sload_sel hfork
    (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_dup3 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_sub (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := (2 : B256)) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_gt hgt (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := (0xe7 : B256)) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide)
  refine rx_branchTo_succ (by decide) prog_1 ?_
  simpa only [setupBase] using
    exit_run (b := setupBase sevm b)
      (d := b.getStorVal sevm.currentTarget 3 -
        (afterSload sevm b 3).getStorVal sevm.currentTarget 2)
      (s2 := (afterSload sevm b 3).getStorVal sevm.currentTarget 2)
      (s3 := b.getStorVal sevm.currentTarget 3)
      hfork hstatic hsentry hd hs2 hs3 hs0b hs1b

/-- The whole walk fits in a system transaction's gas. -/
theorem systemCost_le (benv : Benv) : systemCost benv ≤ 97025 := by
  have e1 := Blanc.sloadCost_le (systemSevm benv) (systemBase benv) 3
  have e2 := Blanc.sloadCost_le (systemSevm benv)
    (afterSload (systemSevm benv) (systemBase benv) 3) 2
  have e3 := Blanc.sloadCost_le (systemSevm benv)
    (ptrBase (systemSevm benv) (setupBase (systemSevm benv) (systemBase benv))) 0
  have e4 := Blanc.sloadCost_le (systemSevm benv)
    (excessBase (systemSevm benv)
      (ptrBase (systemSevm benv) (setupBase (systemSevm benv) (systemBase benv)))) 1
  have f1 := sstoreCost_le (systemSevm benv)
    (setupBase (systemSevm benv) (systemBase benv)) 2 0
  have f2 := sstoreCost_le (systemSevm benv)
    (afterSstore (systemSevm benv)
      (setupBase (systemSevm benv) (systemBase benv)) 2 0) 3 0
  have f3 := sstoreCost_le (systemSevm benv)
    (countBase (systemSevm benv)
      (excessBase (systemSevm benv)
        (ptrBase (systemSevm benv) (setupBase (systemSevm benv) (systemBase benv))))) 0 0
  have f4 := sstoreCost_le (systemSevm benv)
    (afterSstore (systemSevm benv)
      (countBase (systemSevm benv)
        (excessBase (systemSevm benv)
          (ptrBase (systemSevm benv) (setupBase (systemSevm benv) (systemBase benv))))) 0 0) 1 0
  simp only [gasColdSload, gasStorageSet] at e1 e2 e3 e4 f1 f2 f3 f4
  unfold systemCost setupGas exitGas ptrGas excessGas countGas finalGas
  omega

/-- The whole empty-queue walk from the system base. -/
theorem root_run (benv : Benv) {G : Nat}
    (hfork : CoveredFork (systemSevm benv).benvStat.fork)
    (hsentry : gCallStipend < G)
    (hs3 : (systemBase benv).getStorVal (systemSevm benv).currentTarget 3 = 0)
    (hs2 : (afterSload (systemSevm benv) (systemBase benv) 3).getStorVal
      (systemSevm benv).currentTarget 2 = 0)
    (hs0b : (setupBase (systemSevm benv) (systemBase benv)).getStorVal
      (systemSevm benv).currentTarget 0 = 0)
    (hs1b : (setupBase (systemSevm benv) (systemBase benv)).getStorVal
      (systemSevm benv).currentTarget 1 = 0) :
    SFunc.RunExact prog (systemSevm benv)
      (St (systemBase benv) [] .empty (G + systemCost benv)) t_0000_c0
      (.halted (returnPost
        (St (bookBase (systemSevm benv)
          (storeBase (systemSevm benv)
            (countBase (systemSevm benv)
              (excessBase (systemSevm benv)
                (ptrBase (systemSevm benv)
                  (setupBase (systemSevm benv) (systemBase benv)))))))
          [0, 0] .empty G)
        0 0 [])) := by
  have hcall : (systemSevm benv).caller = systemAddress := (system_seed benv).1
  have hstatic : (systemSevm benv).isStatic = false := (system_seed benv).2.2.1
  have hcost : G + (setupGas (systemSevm benv) (systemBase benv) +
      (exitGas +
        (ptrGas (systemSevm benv) (setupBase (systemSevm benv) (systemBase benv)) +
          (excessGas (systemSevm benv)
            (ptrBase (systemSevm benv) (setupBase (systemSevm benv) (systemBase benv))) +
            (countGas (systemSevm benv)
              (excessBase (systemSevm benv)
                (ptrBase (systemSevm benv) (setupBase (systemSevm benv) (systemBase benv)))) +
              finalGas (systemSevm benv)
                (countBase (systemSevm benv)
                  (excessBase (systemSevm benv)
                    (ptrBase (systemSevm benv)
                      (setupBase (systemSevm benv) (systemBase benv)))))))))) =
      G + systemCost benv := by
    unfold systemCost
    omega
  rw [← hcost]
  exact setup_run (sevm := systemSevm benv) (b := systemBase benv) (G := G)
    hfork hstatic hsentry hcall hs3 hs2 hs0b hs1b

/-- The whole SYSTEM execution halts at the exact post-state. -/
theorem system_exec {benv : Benv} (fork : CoveredFork benv.stat.fork)
    (hs3 : (systemBase benv).getStorVal (systemSevm benv).currentTarget 3 = 0)
    (hs2 : (afterSload (systemSevm benv) (systemBase benv) 3).getStorVal
      (systemSevm benv).currentTarget 2 = 0)
    (hs0b : (setupBase (systemSevm benv) (systemBase benv)).getStorVal
      (systemSevm benv).currentTarget 0 = 0)
    (hs1b : (setupBase (systemSevm benv) (systemBase benv)).getStorVal
      (systemSevm benv).currentTarget 1 = 0) :
    exec (initEvm (systemMsg benv)) = .ok (systemPost benv) := by
  let G := systemTransactionGas - systemCost benv
  have hle300 : systemCost benv ≤ 30000000 :=
    (systemCost_le benv).trans (by decide)
  have hgas : systemTransactionGas = 30000000 := by rfl
  have hGbound : gCallStipend < G := by
    have htight := systemCost_le benv
    dsimp only [G]
    rw [hgas]
    norm_num only [gCallStipend]
    omega
  have hrun := root_run benv fork hGbound hs3 hs2 hs0b hs1b (G := G)
  have hG' : G + systemCost benv = systemTransactionGas := by
    dsimp only [G]
    omega
  rw [hG'] at hrun
  have hcode : (systemSevm benv).code = consolidationRequestCode :=
    (system_seed benv).2.2.2.1
  have hexec : Nonempty (Exec 0 (systemSevm benv)
      (St (systemBase benv) [] .empty systemTransactionGas)
      (.ok (systemPost benv))) := by
    apply lift_exact cert_check jumps_ok (hcode.trans code_eq.symm) fork
    exact ⟨t_0000_c0, prog_root, hrun⟩
  have entry : St (systemBase benv) [] .empty systemTransactionGas =
      systemBase benv := by
    rfl
  rw [entry] at hexec
  exact (exec_iff_exec_eq _ _ _ _).mp hexec

/-- An `SLOAD` leaves the world state untouched. -/
private theorem afterSload_state (sevm : Sevm) (b : Devm) (k : B256) :
    (afterSload sevm b k).state = b.state := by
  unfold afterSload
  split <;> rfl

/-- Setting the output leaves the world state untouched. -/
private theorem withOutput_state (d : Devm) (out : Bytes) :
    (d.withOutput out).state = d.state := rfl

/-- Setting the machine leaves the world state untouched. -/
private theorem setMach_state_eq (d : Devm) (m : Mach) :
    (d.setMach m).state = d.state := rfl

/-- The SYSTEM frame halts cleanly with empty return data, a non-negative
refund counter, and writes confined to slots 0–3. -/
theorem systemPost_facts (benv : Benv)
    (hs3 : (systemBase benv).getStorVal (systemSevm benv).currentTarget 3 = 0)
    (hs2 : (afterSload (systemSevm benv) (systemBase benv) 3).getStorVal
      (systemSevm benv).currentTarget 2 = 0)
    (hs0b : (setupBase (systemSevm benv) (systemBase benv)).getStorVal
      (systemSevm benv).currentTarget 0 = 0)
    (hs1b : (setupBase (systemSevm benv) (systemBase benv)).getStorVal
      (systemSevm benv).currentTarget 1 = 0)
    (horig0 : getOrigStorVal (systemSevm benv) (systemSevm benv).currentTarget 0 = 0)
    (horig1 : getOrigStorVal (systemSevm benv) (systemSevm benv).currentTarget 1 = 0)
    (horig2 : getOrigStorVal (systemSevm benv) (systemSevm benv).currentTarget 2 = 0)
    (horig3 : getOrigStorVal (systemSevm benv) (systemSevm benv).currentTarget 3 = 0) :
    (systemPost benv).error = none ∧
    0 ≤ (systemPost benv).refundCounter ∧
    (systemPost benv).output = [] ∧
    (systemPost benv).state =
      ((((benv.state.setStorVal (systemSevm benv).currentTarget 2 0).setStorVal
        (systemSevm benv).currentTarget 3 0).setStorVal
        (systemSevm benv).currentTarget 0 0).setStorVal
        (systemSevm benv).currentTarget 1 0) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, herror, hstate0, _⟩ := system_seed benv
  have herr : (systemPost benv).error = none := by
    obtain ⟨_, herror_eq, _, _⟩ := returnPost_facts _ _ _ _
    unfold systemPost
    rw [herror_eq, St_error, bookBase, afterSstore_error, storeBase,
      afterSstore_error, countBase, afterSload_error, excessBase, afterSload_error,
      ptrBase, afterSstore_error, afterSstore_error, setupBase, afterSload_error,
      afterSload_error]
    exact herror
  have c2 : (setupBase (systemSevm benv) (systemBase benv)).getStorVal
      (systemSevm benv).currentTarget 2 = 0 := by
    rw [setupBase, getStorVal_afterSload]
    exact hs2
  have r1 := afterSstore_refundCounter_ge_of_original_eq_current (systemSevm benv)
    (setupBase (systemSevm benv) (systemBase benv)) 2 0 (horig2.trans c2.symm)
  have c3 : (afterSstore (systemSevm benv)
      (setupBase (systemSevm benv) (systemBase benv)) 2 0).getStorVal
      (systemSevm benv).currentTarget 3 = 0 := by
    rw [getStorVal_eq_getStor, afterSstore_getStor_self,
      Stor.get_set_ne _ (by decide : (2 : B256) ≠ 3), ← getStorVal_eq_getStor,
      setupBase, getStorVal_afterSload, getStorVal_afterSload]
    exact hs3
  have r2 := afterSstore_refundCounter_ge_of_original_eq_current (systemSevm benv)
    (afterSstore (systemSevm benv)
      (setupBase (systemSevm benv) (systemBase benv)) 2 0) 3 0
    (horig3.trans c3.symm)
  have c0 : (countBase (systemSevm benv)
      (excessBase (systemSevm benv)
        (ptrBase (systemSevm benv)
          (setupBase (systemSevm benv) (systemBase benv))))).getStorVal
      (systemSevm benv).currentTarget 0 = 0 := by
    rw [countBase, excessBase, ptrBase, getStorVal_afterSload, getStorVal_afterSload,
      getStorVal_eq_getStor, afterSstore_getStor_self, afterSstore_getStor_self,
      Stor.get_set_ne _ (by decide : (3 : B256) ≠ 0),
      Stor.get_set_ne _ (by decide : (2 : B256) ≠ 0), ← getStorVal_eq_getStor]
    exact hs0b
  have r3 := afterSstore_refundCounter_ge_of_original_eq_current (systemSevm benv)
    (countBase (systemSevm benv)
      (excessBase (systemSevm benv)
        (ptrBase (systemSevm benv)
          (setupBase (systemSevm benv) (systemBase benv))))) 0 0
    (horig0.trans c0.symm)
  have c1 : (afterSstore (systemSevm benv)
      (countBase (systemSevm benv)
        (excessBase (systemSevm benv)
          (ptrBase (systemSevm benv)
            (setupBase (systemSevm benv) (systemBase benv))))) 0 0).getStorVal
      (systemSevm benv).currentTarget 1 = 0 := by
    rw [getStorVal_eq_getStor, afterSstore_getStor_self,
      Stor.get_set_ne _ (by decide : (0 : B256) ≠ 1), ← getStorVal_eq_getStor,
      countBase, excessBase, ptrBase, getStorVal_afterSload, getStorVal_afterSload,
      getStorVal_eq_getStor, afterSstore_getStor_self, afterSstore_getStor_self,
      Stor.get_set_ne _ (by decide : (3 : B256) ≠ 1),
      Stor.get_set_ne _ (by decide : (2 : B256) ≠ 1), ← getStorVal_eq_getStor]
    exact hs1b
  have r4 := afterSstore_refundCounter_ge_of_original_eq_current (systemSevm benv)
    (afterSstore (systemSevm benv)
      (countBase (systemSevm benv)
        (excessBase (systemSevm benv)
          (ptrBase (systemSevm benv)
            (setupBase (systemSevm benv) (systemBase benv))))) 0 0) 1 0
    (horig1.trans c1.symm)
  have href0 : (systemBase benv).refundCounter = 0 := rfl
  have hrefund : 0 ≤ (systemPost benv).refundCounter := by
    have hrr : (systemPost benv).refundCounter =
        (bookBase (systemSevm benv)
          (storeBase (systemSevm benv)
            (countBase (systemSevm benv)
              (excessBase (systemSevm benv)
                (ptrBase (systemSevm benv)
                  (setupBase (systemSevm benv) (systemBase benv))))))).refundCounter := by
      unfold systemPost returnPost
      simp only [show B256.toNat (0 : B256) = 0 by decide, Devm.memRead_zero,
        Devm.withOutput_refundCounter, St, Devm.setMach_refundCounter]
    rw [hrr, bookBase, storeBase]
    have hz : (0 : Int) ≤ (systemBase benv).refundCounter := by
      rw [href0]
    have s1 : (setupBase (systemSevm benv) (systemBase benv)).refundCounter =
        (systemBase benv).refundCounter := by
      rw [setupBase, afterSload_refundCounter, afterSload_refundCounter]
    have hz' : (0 : Int) ≤
        (setupBase (systemSevm benv) (systemBase benv)).refundCounter := by
      rw [s1]
      exact hz
    have s2 : (countBase (systemSevm benv)
        (excessBase (systemSevm benv)
          (ptrBase (systemSevm benv)
            (setupBase (systemSevm benv) (systemBase benv))))).refundCounter =
        (afterSstore (systemSevm benv)
          (afterSstore (systemSevm benv)
            (setupBase (systemSevm benv) (systemBase benv)) 2 0) 3 0).refundCounter := by
      rw [countBase, excessBase, ptrBase, afterSload_refundCounter,
        afterSload_refundCounter]
    have m23 : (afterSstore (systemSevm benv)
          (setupBase (systemSevm benv) (systemBase benv)) 2 0).refundCounter ≤
        (countBase (systemSevm benv)
          (excessBase (systemSevm benv)
            (ptrBase (systemSevm benv)
              (setupBase (systemSevm benv) (systemBase benv))))).refundCounter := by
      rw [s2]
      exact r2
    exact hz'.trans (r1.trans (m23.trans (r3.trans r4)))
  have hout : (systemPost benv).output = [] := by
    unfold systemPost
    rw [(returnPost_facts _ _ _ _).1]
    simp only [St, Devm.memory_setMach, show B256.toNat (0 : B256) = 0 by decide,
      Mem.read, Mem.extend, memExtSize]
    rfl
  have hstate : (systemPost benv).state =
      ((((benv.state.setStorVal (systemSevm benv).currentTarget 2 0).setStorVal
        (systemSevm benv).currentTarget 3 0).setStorVal
        (systemSevm benv).currentTarget 0 0).setStorVal
        (systemSevm benv).currentTarget 1 0) := by
    have hret : (systemPost benv).state =
        (bookBase (systemSevm benv)
          (storeBase (systemSevm benv)
            (countBase (systemSevm benv)
              (excessBase (systemSevm benv)
                (ptrBase (systemSevm benv)
                  (setupBase (systemSevm benv) (systemBase benv))))))).state := by
      unfold systemPost returnPost
      simp only [show B256.toNat (0 : B256) = 0 by decide, Devm.memRead_zero,
        withOutput_state, St, setMach_state_eq]
    rw [hret, bookBase, storeBase, countBase, excessBase, ptrBase, setupBase,
      afterSstore_state, afterSstore_state, afterSload_state, afterSload_state,
      afterSstore_state, afterSstore_state, afterSload_state, afterSload_state,
      hstate0]
  exact ⟨herr, hrefund, hout, hstate⟩

/-- **The EIP-7251 checked system call** on the real installed code with an
empty queue: it succeeds with empty return data, and its writes stay in
slots 0–3. -/
theorem processCheckedSystemTransaction_consolidationRequest_empty {benv : Benv}
    (fork : CoveredFork benv.stat.fork)
    (installed : benv.state.getCode consolidationRequestPredeployAddress =
      consolidationRequestCode)
    (hs3 : (systemBase benv).getStorVal (systemSevm benv).currentTarget 3 = 0)
    (hs2 : (afterSload (systemSevm benv) (systemBase benv) 3).getStorVal
      (systemSevm benv).currentTarget 2 = 0)
    (hs0b : (setupBase (systemSevm benv) (systemBase benv)).getStorVal
      (systemSevm benv).currentTarget 0 = 0)
    (hs1b : (setupBase (systemSevm benv) (systemBase benv)).getStorVal
      (systemSevm benv).currentTarget 1 = 0)
    (horig0 : getOrigStorVal (systemSevm benv) (systemSevm benv).currentTarget 0 = 0)
    (horig1 : getOrigStorVal (systemSevm benv) (systemSevm benv).currentTarget 1 = 0)
    (horig2 : getOrigStorVal (systemSevm benv) (systemSevm benv).currentTarget 2 = 0)
    (horig3 : getOrigStorVal (systemSevm benv) (systemSevm benv).currentTarget 3 = 0) :
    processCheckedSystemTransaction benv consolidationRequestPredeployAddress [] =
      .ok ((systemPost benv).state, systemCallOutput (systemPost benv)) ∧
    (systemCallOutput (systemPost benv)).error = none ∧
    (systemCallOutput (systemPost benv)).returnData = [] ∧
    (systemPost benv).state =
      ((((benv.state.setStorVal (systemSevm benv).currentTarget 2 0).setStorVal
        (systemSevm benv).currentTarget 3 0).setStorVal
        (systemSevm benv).currentTarget 0 0).setStorVal
        (systemSevm benv).currentTarget 1 0) := by
  have facts :=
    systemPost_facts benv hs3 hs2 hs0b hs1b horig0 horig1 horig2 horig3
  refine ⟨processCheckedSystemTransaction_of_exec member fork installed
    (system_exec fork hs3 hs2 hs0b hs1b) facts.1 facts.2.1, ?_, ?_, ?_⟩
  · rfl
  · exact facts.2.2.1
  · exact facts.2.2.2

end Blanc.Lift.ConsolidationRequest
