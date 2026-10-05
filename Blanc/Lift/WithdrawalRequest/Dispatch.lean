import Blanc.Lift.WithdrawalRequest.Prog
import Blanc.Lift.WithdrawalRequest.Jumps
import Blanc.Lift.WalkSteps

/-!
The certified caller-dispatch prefix, ending at the user or system tail.
No tail behavior or storage effect is assumed or proved here.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

/-- The branch selected by the protocol's system caller address. -/
def dispatchTail (sevm : Sevm) : SFunc :=
  if sevm.caller = systemAddress then t_00cb_c0 else t_001a_c0

/-- The pinned costs of `CALLER`, two nonempty `PUSH`es, `EQ` and `JUMPI`. -/
def dispatchGas : Nat := gBase + gVerylow + gVerylow + gVerylow + gHigh

theorem dispatchGas_eq : dispatchGas = 21 := rfl

private theorem system_push :
    Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe] =
      systemAddress.toB256 := rfl

private theorem caller_eqCheck (sevm : Sevm) :
    B256.eqCheck systemAddress.toB256 sevm.caller.toB256 =
      if sevm.caller = systemAddress then 1 else 0 := by
  by_cases h : sevm.caller = systemAddress
  · simp only [h, B256.eqCheck, ite_true]
  · have hw : systemAddress.toB256 ≠ sevm.caller.toB256 :=
      fun eq => h (Adr.toB256_inj eq.symm)
    simp only [B256.eqCheck, ite_eq_right hw, ite_eq_right h]

/-- A successful dispatch leaves its original base and memory at the selected tail. -/
theorem dispatch_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (run : SFunc.Run prog sevm (St b [] M G) t_0000_c0 o) :
    ∃ G', SFunc.Run prog sevm (St b [] M G') (dispatchTail sevm) o := by
  cases run with
  | next hc k =>
    obtain ⟨_, rfl⟩ := ri_caller hc
    cases k with
    | next hp k =>
      obtain ⟨_, rfl⟩ := ri_push hp
      rw [system_push] at k
      cases k with
      | next he k =>
        obtain ⟨_, rfl⟩ := ri_eq he
        cases k with
        | next hp k =>
          obtain ⟨_, rfl⟩ := ri_push hp
          rw [caller_eqCheck] at k
          by_cases h : sevm.caller = systemAddress
          · simp only [ite_eq_left h, dispatchTail] at k ⊢
            cases k with
            | zero _ pop _ =>
              exact False.elim ((by decide : (1 : B256) ≠ 0) (St.of_pop2 pop).2.1)
            | succ _ _ _ pop tail => exact ⟨_, (St.of_pop2 pop).2.2 ▸ tail⟩
          · simp only [ite_eq_right h, dispatchTail] at k ⊢
            cases k with
            | zero _ pop tail => exact ⟨_, (St.of_pop2 pop).2.2 ▸ tail⟩
            | succ _ _ hw pop _ => exact False.elim (hw (St.of_pop2 pop).2.1.symm)

/-- An exact continuation transports backwards through precisely the dispatch charge. -/
theorem dispatch_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (tail : SFunc.RunExact prog sevm (St b [] M G) (dispatchTail sevm) o) :
    SFunc.RunExact prog sevm (St b [] M (G + dispatchGas)) t_0000_c0 o := by
  have hgas : G + dispatchGas = G + 10 + 3 + 3 + 3 + 2 := by
    simp only [dispatchGas_eq, Nat.add_assoc]
  rw [hgas]
  unfold t_0000_c0
  refine rx_caller (by decide) ?_
  refine rx_push system_push (by change 1 < 1024; decide) ?_
  refine rx_eq (caller_eqCheck sevm) (by decide) ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  by_cases h : sevm.caller = systemAddress
  · simp only [ite_eq_left h, dispatchTail] at tail ⊢
    exact rx_branch_succ (by decide) tail
  · simp only [ite_eq_right h, dispatchTail] at tail ⊢
    exact rx_branch_zero tail

/-- Every successful canonical-code execution from an empty stack enters its selected tail. -/
theorem exec_dispatch {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = Blanc.withdrawalRequestCode)
    (hfork : CoveredFork sevm.benvStat.fork) (hstack : pre.stack = [])
    (exec : Exec 0 sevm pre (.ok post)) :
    ∃ G, SFunc.Run prog sevm (St pre [] pre.memory G) (dispatchTail sevm) (.halted post) := by
  obtain ⟨f, hf, run⟩ := lift_sound cert_check (hcode.trans code_eq.symm) hfork exec
  change prog[0]? = some f at hf
  rw [prog_root] at hf
  cases hf
  rw [St.self hstack rfl] at run
  exact dispatch_inv run

/-- A selected exact tail continuation constructs execution of the canonical bytes. -/
theorem exec_of_dispatch {sevm : Sevm} {b post : Devm} {M : Mem} {G : Nat}
    (hcode : sevm.code = Blanc.withdrawalRequestCode)
    (hfork : CoveredFork sevm.benvStat.fork)
    (tail : SFunc.RunExact prog sevm (St b [] M G) (dispatchTail sevm) (.halted post)) :
    Nonempty (Exec 0 sevm (St b [] M (G + dispatchGas)) (.ok post)) := by
  apply lift_exact cert_check jumps_ok (hcode.trans code_eq.symm) hfork
  exact ⟨t_0000_c0, prog_root, dispatch_exact tail⟩

end Blanc.Lift.WithdrawalRequest
