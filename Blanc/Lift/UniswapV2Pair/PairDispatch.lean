import Blanc.Lift.UniswapV2Pair.GetterMemory
import Blanc.Lift.UniswapV2Pair.Cert
import Blanc.Lift.ExactWalkSolc
import Blanc.Lift.SelectorRouteExact
import Blanc.Lift.InvWalkDispatch
import Blanc.ConcreteRun
import Blanc.Lift.WalkKit
import Blanc.Lift.WalkInvKit

/-!
# The pair's dispatcher, both ways

The runtime's entry `t_0000_c0` stores the free-memory pointer, rejects value and short calldata
(`getterString_guards_exact`, 63 gas), and `t_001a_c0` shifts the selector word down
(`PUSH1 0 CALLDATALOAD PUSH1 224 SHR`, 12 gas) before the solc comparison tree `pairRows`.  The
tree is walked by evaluation (`Blanc/Lift/SelectorRouteExact.lean`, `Blanc/Lift/SelectorRoute.lean`):

* `pair_dispatch_exact`: with the selector `σ`, a run of the entry `pairRows.selGoto cert.prog σ`
  (the selector word on the stack) is a run of the runtime, for `75 + pairRows.selCost σ` gas;
* `pair_dispatch_inv`: a run from `t_001a_c0` contains a run of that entry.

The goto and the cost are kernel facts (`kernel_rfl`, `decide +kernel`) at each named selector.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc.Lift

/-- **The guards**, forward: free-memory pointer, no value, at least four bytes of calldata. -/
theorem getterString_guards_exact {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (body : SFunc.RunExact cert.prog sevm (St b [] getterInitMemory G) t_001a_c0 o) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + 63)) t_0000_c0 o := by
  unfold t_0000_c0
  wrun! 2
  refine rx_mstore (c := 12) ?_ rfl ?_
  · rw [St.extCost_eq (n := 0) rfl]; decide
  refine rx_callvalue (by decide) ?_
  rw [value]
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_iszero (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 16) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0010_c0
  wrun! 4
  refine rx_lt (v := 0) (ltCheck_zero_of_le size) (by decide) ?_
  refine rx_push (w := 0x01b9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  exact rx_branch_zero body

/-- The solc comparison tree, after the selector shift. -/
def pairRows : SFunc :=
  .next (.reg (.dup 0)) (.next (.push [0x6a, 0x62, 0x78, 0x42] (by decide)) (.next (.reg .gt)
    (.next (.push [0x00, 0xf9] (by decide)) (.branch t_002b_c0 t_00f9_c0))))

theorem t_001a_eq : t_001a_c0 = .next (.push [0x00] (by decide)) (.next (.reg .calldataload)
    (.next (.push [0xe0] (by decide)) (.next (.reg .shr) pairRows))) := rfl

/-- **The selector shift and comparison tree, forward**, over any memory. -/
theorem pair_selector_exact {sevm : Sevm} {b : Devm} {M : Mem} {G N : Nat} {o : Outcome}
    {σ : B256} {tgt : SFunc}
    (selector : Blanc.Sevm.selector sevm = σ)
    (ht : pairRows.selGoto cert.prog σ = some tgt) (hN : 12 + pairRows.selCost σ = N)
    (body : SFunc.RunExact cert.prog sevm (St b [σ] M G) tgt o)
    (h_shifts : sevm.benvStat.rules.op.shifts = true) :
    SFunc.RunExact cert.prog sevm (St b [] M (G + N)) t_001a_c0 o := by
  subst hN
  rw [show G + (12 + pairRows.selCost σ) = G + pairRows.selCost σ + 3 + 3 + 3 + 3 by omega,
    t_001a_eq]
  wrun! 3
  refine rx_shr (h_shifts := h_shifts) (v := σ) selector (by decide) ?_
  exact SFunc.RunExact.selGoto (S := []) ht (by decide) body

/-- **The dispatcher, forward.** -/
theorem pair_dispatch_exact {sevm : Sevm} {b : Devm} {G N : Nat} {o : Outcome} {σ : B256}
    {tgt : SFunc}
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = σ)
    (ht : pairRows.selGoto cert.prog σ = some tgt) (hN : 75 + pairRows.selCost σ = N)
    (body : SFunc.RunExact cert.prog sevm (St b [σ] getterInitMemory G) tgt o)
    (h_shifts : sevm.benvStat.rules.op.shifts = true) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + N)) t_0000_c0 o := by
  rw [← hN, show G + (75 + pairRows.selCost σ) = G + (12 + pairRows.selCost σ) + 63 by omega]
  exact getterString_guards_exact value size (pair_selector_exact selector ht rfl body h_shifts)

/-- **The dispatcher, inverted**: a run from `t_001a_c0` with the selector `σ` contains a run of
the entry the walk of `σ` enters, with the selector word on the stack. -/
theorem pair_dispatch_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    {σ : B256} {tgt : SFunc}
    (selector : Blanc.Sevm.selector sevm = σ) (ht : pairRows.selGoto cert.prog σ = some tgt)
    (run : SFunc.Run cert.prog sevm (St b [] M G) t_001a_c0 o) :
    ∃ residual, SFunc.Run cert.prog sevm (St b [σ] M residual) tgt o := by
  have h := run.cut
  rw [t_001a_eq] at h
  winv 3
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_shr hd
  simp only [show Bytes.toB256 [0] = (0 : B256) from rfl,
    show Bytes.toB256 [0xe0] = (224 : B256) from rfl,
    show (224 : B256).toNat = 224 from rfl,
    show Sevm.dataWord sevm 0 >>> 224 = σ from selector] at hd
  subst d
  obtain ⟨_, _, hw, hj⟩ := SFunc.selGoto_spec ht
  obtain ⟨-, g, _, hg, h⟩ := SFunc.RunCut.selWalk_inl hw h
  rw [hj] at hg
  cases hg
  exact ⟨_, h.uncut⟩

/-- **The dispatcher, inverted, for a `P`-run** cut nowhere. -/
theorem pair_dispatch_invP {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {sevm : Sevm} {b : Devm} {M : Mem}
    {G : Nat} {r : Seg} {σ : B256} {tgt : SFunc}
    (selector : Blanc.Sevm.selector sevm = σ) (ht : pairRows.selGoto cert.prog σ = some tgt)
    (run : SFunc.RunCutP P cert.prog sevm [] (St b [] M G) t_001a_c0 r) :
    ∃ G', SFunc.RunCutP P cert.prog sevm [] (St b [σ] M G') tgt r := by
  rw [t_001a_eq] at run
  obtain ⟨d, hd, h⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_push (hP hd)
  winv 2 using hP
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, hd⟩ := ri_shr (hP hd)
  simp only [show Bytes.toB256 [0] = (0 : B256) from rfl,
    show Bytes.toB256 [0xe0] = (224 : B256) from rfl,
    show (224 : B256).toNat = 224 from rfl,
    show Sevm.dataWord sevm 0 >>> 224 = σ from selector] at hd
  subst d
  exact SFunc.RunCutP.selGoto (S := []) hP ht h

end Blanc.Lift.UniswapV2Pair
