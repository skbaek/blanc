import Blanc.Lift.Loop
namespace Blanc.Lift
open Jaune
def countedBody : SFunc := .dest (.next (Ninst.pushB256 1)
  (.next (.reg (.swap 0)) (.next (.reg .sub)
    (.next (.reg (.dup 0)) (.next (Ninst.pushB256 0) (.branchTo (.last .stop) 1))))))
def countedProgram : List SFunc :=
  [.next (Ninst.pushB256 3) (.next (Ninst.pushB256 0) (.jump 1)), countedBody]
private theorem stack_of_push {x : B256} {devm devm' : Devm} (h : Devm.PushBurn [x] devm devm') : devm'.stack = x :: devm.stack := by
  simpa [Devm.PushBurn, Stack.Push, Split] using h.stack
private theorem pop2_of_stack {d w a b : B256} {devm devm' : Devm} {xs : Stack}
    (h : Devm.PopBurn [d, w] devm devm') (hs : devm.stack = a :: b :: xs) :
    d = a ∧ w = b ∧ devm'.stack = xs := by
  have hp : a :: b :: xs = d :: w :: devm'.stack := by
    simpa [Devm.PopBurn, Stack.Pop, Split, hs] using h.stack
  have hd : a = d := (List.cons.inj hp).1
  have hrest : b :: xs = w :: devm'.stack := (List.cons.inj hp).2
  have hw : b = w := (List.cons.inj hrest).1
  have ht : xs = devm'.stack := (List.cons.inj hrest).2
  exact ⟨hd.symm, hw.symm, ht.symm⟩
private theorem stack_of_sub {sevm : Sevm} {x y : B256} {devm devm' : Devm} {xs : Stack}
    (h : Ninst.Run sevm devm (.reg .sub) devm') (hs : devm.stack = x :: y :: xs) :
    devm'.stack = (x - y) :: xs := by
  rcases of_run_reg h with ⟨_, hr⟩
  simp only [Rinst.run, Rinst.runCore] at hr
  rcases Devm.diffBurn_of_applyBinary hr with ⟨x', y', hdiff⟩
  rcases hdiff.stack with ⟨mid, hpop, hpush⟩
  simp only [Stack.Pop, Stack.Push, Split] at hpop hpush
  rw [hs] at hpop
  have hpre : x :: y :: xs = x' :: y' :: mid := by
    simpa [List.cons_append, List.nil_append] using hpop
  have hx' : x = x' := (List.cons.inj hpre).1
  have hy' : y = y' := (List.cons.inj (List.cons.inj hpre).2).1
  have htail : xs = mid := (List.cons.inj (List.cons.inj hpre).2).2
  subst x'
  subst y'
  subst mid
  simpa [List.cons_append, List.nil_append] using hpush
private theorem stack_of_dup {sevm : Sevm} {x : B256} {devm devm' : Devm} {xs : Stack}
    (h : Ninst.Run sevm devm (.reg (.dup 0)) devm') (hs : devm.stack = x :: xs) :
    devm'.stack = x :: x :: xs := by
  rcases of_run_dup h with ⟨y, hy, hpush⟩
  have hy' : y = x := by
    simpa [hs] using hy.symm
  subst y
  have hp := stack_of_push hpush
  simpa [hs] using hp
private theorem counted_step {sevm : Sevm} {devm : Devm} {r : Seg} (hstack : ∃ x, devm.stack = [x])
    (run : SFunc.RunCutP Ninst.Run countedProgram sevm [1] devm countedBody r) :
    Seg.LoopPost 1 (fun d => ∃ x, d.stack = [x]) (fun r => match r with
      | .at _ d => ∃ x, d.stack = [x]
      | .done o => ∃ d, o = .halted d ∧ d.stack = [0]) r := by
  rcases hstack with ⟨x, hx⟩
  change SFunc.RunCutP Ninst.Run countedProgram sevm [1] devm countedBody r at run
  cases run with
  | dest hburn hrun =>
    rename_i devm0
    have hx0 : devm0.stack = [x] := by simpa [hx] using hburn.stack.symm
    cases hrun with
    | next hpush hrun =>
      rename_i devm1
      have hx1 : devm1.stack = [1, x] := by simpa [hx0] using stack_of_push (of_run_pushB256 hpush)
      cases hrun with
      | next hswap hrun =>
        rename_i devm2
        have hx2 : devm2.stack = [x, 1] := by
          simpa [Jaune.List.swap, hx1] using (of_run_swap hswap).symm
        cases hrun with
        | next hsub hrun =>
          rename_i devm3
          have hx3 : devm3.stack = [x - 1] := stack_of_sub hsub hx2
          cases hrun with
          | next hdup hrun =>
            rename_i devm4
            have hx4 : devm4.stack = [x - 1, x - 1] := stack_of_dup hdup hx3
            cases hrun with
            | next hpushD hrun =>
              rename_i devm5
              have hx5 : devm5.stack = [0, x - 1, x - 1] := by simpa [hx4] using stack_of_push (of_run_pushB256 hpushD)
              cases hrun with
              | toZero d hpop hrun =>
                rename_i devm6
                rcases pop2_of_stack hpop hx5 with ⟨hd, hw, hx6⟩
                subst d
                have hzero : x - 1 = 0 := hw.symm
                cases hrun with
                | last hlast =>
                  rename_i devm7
                  have hstop : devm7 = devm6 := by simpa [Linst.Run, Linst.run] using hlast.symm
                  simp only [Seg.LoopPost]
                  refine ⟨devm7, rfl, ?_⟩
                  rw [hstop, hx6, hzero]
              | toSuccCut d w hne hk hpop =>
                rename_i devm6
                rcases pop2_of_stack hpop hx5 with ⟨hd, hw, hx6⟩
                subst d
                subst w
                simpa [Seg.LoopPost] using (show ∃ y, devm6.stack = [y] from ⟨x - 1, hx6⟩)
              | toSucc d w hne hnot hget hpop hrun =>
                simp at hnot
theorem counted_loop_halts_zero {sevm : Sevm} {devm : Devm} {o : Outcome} {x : B256}
    (hstack : devm.stack = [x]) (run : SFunc.Run countedProgram sevm devm countedBody o) :
    ∃ devm', o = .halted devm' ∧ devm'.stack = [0] := by
  have hrun := SFunc.RunP.loop (P := Ninst.Run) (fs := countedProgram)
    (sevm := sevm) (k := 1) (g := countedBody) (by simp [countedProgram])
    (fun d => ∃ y, d.stack = [y])
    (fun o => ∃ d, o = .halted d ∧ d.stack = [0])
    (by intro d hI r hrun; have h := counted_step hI hrun; cases r <;> simpa [Seg.LoopPost] using h)
    devm o (by exact ⟨x, hstack⟩) run
  exact hrun

theorem counted_program_halts_zero {sevm : Sevm} {devm devm' : Devm}
    (run : SProg.Run countedProgram sevm devm devm') (hstack : devm.stack = []) :
    devm'.stack = [0] := by
  obtain ⟨f, hf, hrun⟩ := run
  simp [countedProgram] at hf
  subst f
  change SFunc.Run countedProgram sevm devm (.next (Ninst.pushB256 3)
    (.next (Ninst.pushB256 0) (.jump 1))) (.halted devm') at hrun
  cases hrun with
  | next hpush3 hrun =>
    rename_i devm1
    have hs1 : devm1.stack = [3] := by simpa [hstack] using stack_of_push (of_run_pushB256 hpush3)
    cases hrun with
    | next hpush0 hrun =>
      rename_i devm2
      have hs2 : devm2.stack = [0, 3] := by simpa [hs1] using stack_of_push (of_run_pushB256 hpush0)
      cases hrun with
      | jump d hget hpop hbody =>
        rename_i devm3 f
        have hf1 : f = countedBody := by simpa [countedProgram] using hget.symm
        subst f
        have hstackPop : devm2.stack = d :: devm3.stack := by
          simpa [Devm.PopBurn, Stack.Pop, Split] using hpop.stack
        rw [hs2] at hstackPop
        have hd : d = 0 := by
          injection hstackPop with hd _
          exact hd.symm
        have hs3 : devm3.stack = [3] := by
          subst d
          injection hstackPop with _ hs3
          simpa using hs3.symm
        obtain ⟨d', ho, hs'⟩ := counted_loop_halts_zero hs3 hbody
        have hd' : d' = devm' := by
          injection ho with hEq
          exact hEq.symm
        simpa [hd'] using hs'
end Blanc.Lift
