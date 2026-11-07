import Blanc.Lift.BuilderRequest.AmsterdamMsgProbeRevert
import Blanc.Lift.BuilderRequest.Deposit.SystemCall

/-!
# Probe: O7's control at the semantics

Disposable (goal `blanc-eip8282-builder-requests-v1`, O16). W7b showed no `SysPath` exists at a runtime
with `PUSH0 PUSH0 REVERT` over the first three bytes of the drain body. This shows the thing O7's row asks:
on a one-record queue that runtime's `processCheckedSystemTransaction` is not `.ok`, while the real
runtime's is, by `Deposit.system_call_ok`.
-/

namespace Blanc.Lift.BuilderRequest.AmsterdamMsgProbe

open Jaune
open RequestSystem (system_push)

/-- The real runtime with exactly three bytes changed, at 0x13b. W7b's mutation. -/
def mutantCode : ByteArray :=
  ⟨((Deposit.code.data.setIfInBounds 0x13b 0x5f).setIfInBounds 0x13c 0x5f).setIfInBounds 0x13d 0xfd⟩

theorem mutant_ne : mutantCode.data ≠ Deposit.code.data := by decide +kernel

def segA : SFunc :=
  (.next (.reg .caller) (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe] (by decide)) (.next (.reg .eq)
  (.next (.push [0x01, 0x1c] (by decide)) (.last .stop)))))

def segB : SFunc :=
  (.dest (.next (.push [0x03] (by decide)) (.next (.reg .sload) (.next (.push [0x02] (by decide))
  (.next (.reg .sload) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .sub)
  (.next (.reg (.dup 0)) (.next (.push [0x40] (by decide)) (.next (.reg .gt)
  (.next (.push [0x01, 0x31] (by decide)) (.last .stop)))))))))))))

def segC : SFunc :=
  (.dest (.next (.push [] (by decide)) (.dest (.next (.reg (.dup 1)) (.next (.reg (.dup 1))
  (.next (.reg .eq) (.next (.push [0x01, 0xd7] (by decide))
  (.branch (.next (.push [] (by decide)) (.next (.push [] (by decide)) (.last .stop)))
    .undefined))))))))

theorem segA_at : segEnd mutantCode 0 segA = some 26 := by decide +kernel
theorem segB_at : segEnd mutantCode 0x11c segB = some 0x12d := by decide +kernel
theorem segC_at : segEnd mutantCode 0x131 segC = some 0x13d := by decide +kernel
theorem jumpiA : Jinst.At mutantCode 26 .jumpi := by unfold Jinst.At; kernel_rfl
theorem jumpiB : Jinst.At mutantCode 0x12d .jumpi := by unfold Jinst.At; kernel_rfl
theorem jpA : jumpable mutantCode (0x11c : B256).toNat = true := by decide +kernel
theorem jpB : jumpable mutantCode (0x131 : B256).toNat = true := by decide +kernel
theorem revAt : Linst.At mutantCode 0x13d .revert := by unfold Linst.At; kernel_rfl

/-- The charge up to the mutant's `REVERT`, beside the two reads. -/
def mutantFixed : Nat := 2 + 3 + 3 + 3 + 10 + 1 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 10 +
  1 + 2 + 1 + 3 + 3 + 3 + 3 + 10 + 2 + 2

/-- The mutant's machine at its `REVERT`. -/
def mutantRaw (s : Sevm) (b : Devm) (G : Nat) : Devm :=
  (St (afterSloadA s (afterSloadA s b 3) 2) [0, (1 : B256) - 0, 0, 1] .empty G).withOutput []

/-- **The mutated frame executes `REVERT` on a one-record queue.** -/
theorem mutant_frame_reverts {s : Sevm} {b : Devm} {G : Nat} (hcode : s.code = mutantCode)
    (hacc : s.benvStat.rules.access = .eip2929) (hp0 : s.benvStat.rules.op.push0 = true)
    (caller : s.caller = systemAddress) (h2 : b.getStorVal s.currentTarget 2 = 0)
    (h3 : b.getStorVal s.currentTarget 3 = 1) :
    Nonempty (Exec 0 s (St b [] .empty (G + mutantFixed + sloadCost s b 3 +
        sloadCost s (afterSloadA s b 3) 2))
      (.error (.revert, mutantRaw s b G))) := by
  have segA_at' : segEnd s.code 0 segA = some 26 := by rw [hcode]; exact segA_at
  have segB_at' : segEnd s.code 0x11c segB = some 0x12d := by rw [hcode]; exact segB_at
  have segC_at' : segEnd s.code 0x131 segC = some 0x13d := by rw [hcode]; exact segC_at
  have jumpiA' : Jinst.At s.code 26 .jumpi := by rw [hcode]; exact jumpiA
  have jumpiB' : Jinst.At s.code 0x12d .jumpi := by rw [hcode]; exact jumpiB
  have jpA' : jumpable s.code (0x11c : B256).toNat = true := by rw [hcode]; exact jpA
  have jpB' : jumpable s.code (0x131 : B256).toNat = true := by rw [hcode]; exact jpB
  have revAt' : Linst.At s.code 0x13d .revert := by rw [hcode]; exact revAt
  let B := afterSloadA s (afterSloadA s b 3) 2
  have h2' : (afterSloadA s b 3).getStorVal s.currentTarget 2 = 0 := by
    rw [afterSloadA_getStorVal]
    exact h2
  have runC : SFunc.RunExact [] s (St B [(1 : B256) - 0, 0, 1] .empty (G + 2 + 2 + 10 + 3 + 3 + 3 + 3 + 1 + 2 + 1))
      segC (.halted (St B [0, 0, 0, (1 : B256) - 0, 0, 1] .empty G)) := by
    unfold segC
    refine rx_dest ?_
    refine rx_push0 (h_push0 := hp0) (by rroom) ?_
    refine rx_dest ?_
    refine rx_dup2 (by rroom) ?_
    refine rx_dup2 (by rroom) ?_
    refine rx_eq (v := 0) (by decide) (by rroom) ?_
    refine rx_push (w := (0x1d7 : B256)) (by decide) (by rroom) ?_
    refine rx_branch_zero ?_
    refine rx_push0 (h_push0 := hp0) (by rroom) ?_
    refine rx_push0 (h_push0 := hp0) (by rroom) ?_
    exact .last rfl
  have afterC := exec_of_seg _ segC_at' runC (exec_revert_empty (b := B) (M := .empty) (G := G)
    (S := [0, (1 : B256) - 0, 0, 1]) revAt')
  have takenB := exec_jumpi_taken (x := (0x131 : B256)) (w := 1) jumpiB' (by decide) jpB' afterC
  have runB : SFunc.RunExact [] s
      (St b [] .empty (G + 2 + 2 + 10 + 3 + 3 + 3 + 3 + 1 + 2 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 +
        sloadCost s (afterSloadA s b 3) 2 + 3 + sloadCost s b 3 + 3 + 1))
      segB (.halted (St B [0x131, 1, (1 : B256) - 0, 0, 1] .empty
        (G + 2 + 2 + 10 + 3 + 3 + 3 + 3 + 1 + 2 + 1 + 10))) := by
    unfold segB
    refine rx_dest ?_
    refine rx_push (w := (3 : B256)) (by decide) (by rroom) ?_
    refine rx_sloadV hacc (by rroom) h3 ?_
    refine rx_push (w := (2 : B256)) (by decide) (by rroom) ?_
    refine rx_sloadV hacc (by rroom) h2' ?_
    refine rx_dup1 (by rroom) ?_
    refine rx_dup3 (by rroom) ?_
    refine rx_sub' rfl (by rroom) ?_
    refine rx_dup1 (by rroom) ?_
    refine rx_push (w := (0x40 : B256)) (by decide) (by rroom) ?_
    refine rx_gt (v := 1) (by decide) (by rroom) ?_
    refine rx_push (w := (0x131 : B256)) (by decide) (by rroom) ?_
    exact .last rfl
  have afterB := exec_of_seg _ segB_at' runB takenB
  have takenA := exec_jumpi_taken (x := (0x11c : B256)) (w := 1) (S := []) (b := b) (M := .empty)
    jumpiA' (by decide) jpA' afterB
  have runA : SFunc.RunExact [] s
      (St b [] .empty (G + 2 + 2 + 10 + 3 + 3 + 3 + 3 + 1 + 2 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 +
        sloadCost s (afterSloadA s b 3) 2 + 3 + sloadCost s b 3 + 3 + 1 + 10 + 3 + 3 + 3 + 2))
      segA (.halted (St b [0x11c, 1] .empty (G + 2 + 2 + 10 + 3 + 3 + 3 + 3 + 1 + 2 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 +
        sloadCost s (afterSloadA s b 3) 2 + 3 + sloadCost s b 3 + 3 + 1 + 10))) := by
    unfold segA
    refine rx_caller (by decide) ?_
    refine rx_push system_push (by rroom) ?_
    refine rx_eq (v := 1) ((adr_eqCheck systemAddress s.caller).trans (ite_eq_left caller)) (by rroom) ?_
    refine rx_push (w := (0x11c : B256)) (by decide) (by rroom) ?_
    exact .last rfl
  have hg : G + mutantFixed + sloadCost s b 3 + sloadCost s (afterSloadA s b 3) 2 =
      G + 2 + 2 + 10 + 3 + 3 + 3 + 3 + 1 + 2 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 +
        sloadCost s (afterSloadA s b 3) 2 + 3 + sloadCost s b 3 + 3 + 1 + 10 + 3 + 3 + 3 + 2 := by
    simp only [mutantFixed]
    omega
  rw [hg]
  exact exec_of_seg _ segA_at' runA takenA

/-- **O7's control at the semantics.** Under Amsterdam, with the mutant installed and a one-record queue
in storage (head 0, tail 1), the checked system call is not `.ok`. -/
theorem mutant_call_not_ok {benv : Benv} {target : Adr} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode target = mutantCode)
    (hprecomp : ¬ amsterdamRules.isPrecomp target)
    (h2 : (benv.state.getStor target).get 2 = 0) (h3 : (benv.state.getStor target).get 3 = 1) :
    ∀ r, processCheckedSystemTransaction benv target [] ≠ .ok r := by
  let M := systemCallMsg benv target mutantCode []
  let s := userSevm M mutantCode M.benv
  let e := userEntry M M.benv
  have hfork' : M.benv.stat.fork = .amsterdam := hfork
  have hC : mutantFixed + sloadCost s e 3 + sloadCost s (afterSloadA s e 3) 2 ≤ systemTransactionGas := by
    have h1 := sloadCost_le s e 3
    have h2 := sloadCost_le s (afterSloadA s e 3) 2
    have hcold : gasColdSload = 2100 := rfl
    have hs : systemTransactionGas = 30000000 := rfl
    simp only [mutantFixed]
    omega
  let G := systemTransactionGas - (mutantFixed + sloadCost s e 3 + sloadCost s (afterSloadA s e 3) 2)
  have hsfork : s.benvStat.fork = .amsterdam := hfork
  have hrun := mutant_frame_reverts (s := s) (b := e) (G := G) rfl (Blanc.amsterdam_access hsfork)
    (Blanc.amsterdam_push0 hsfork) rfl h2 h3
  have hSt : St e [] .empty (G + mutantFixed + sloadCost s e 3 + sloadCost s (afterSloadA s e 3) 2) = e := by
    have hgas : G + mutantFixed + sloadCost s e 3 + sloadCost s (afterSloadA s e 3) 2 = e.gasLeft := by
      show _ = systemTransactionGas
      simp only [G]
      omega
    rw [hgas]
    exact St.self rfl rfl
  rw [hSt] at hrun
  have hexec := (exec_iff_exec_eq _ _ _ _).mp hrun
  have hnew : (M.value != 0 && decide (M.benv.state.get M.currentTarget).Empty) = false := by
    have hv : (M.value != 0) = false := by
      show ((0 : B256) != 0) = false
      simp only [bne_self_eq_false]
    rw [hv, Bool.false_and]
  have hcall := processMessageCall_revert (M := M) (code := mutantCode) (benv := M.benv) hfork' rfl rfl
    installed (by decide +kernel) hnew hprecomp (Msg.benvAfterTransfer_of_value_zero rfl) rfl hexec
  have hsys : processSystemTransaction benv target mutantCode [] = processMessageCall M := rfl
  have hne : mutantCode.isEmpty = false := by decide +kernel
  intro r h
  unfold processCheckedSystemTransaction at h
  simp only [installed, hne, Bool.false_eq_true, ite_false] at h
  rw [hsys, hcall] at h
  simp only [bind, Except.bind, Except.mapError, revertOutput] at h
  cases h

end Blanc.Lift.BuilderRequest.AmsterdamMsgProbe
