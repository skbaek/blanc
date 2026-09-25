import Blanc.Lift.Weth9.Lift

namespace Jaune

/-- A nonterminal instruction which does not write the persistent world. -/
def Ninst.stateSilent : Ninst → Bool
  | .reg .sstore => false
  | .reg _ => true
  | .exec _ => false
  | .push _ _ => true
  | .dupn _ => true
  | .swapn _ => true
  | .exchange _ => true

end Jaune

namespace Blanc.Lift

open Jaune

/-- A synthetic tree whose instructions and terminal, if any, are state-silent. -/
def SFunc.silent : SFunc → Bool
  | .branch f g => f.silent && g.silent
  | .branchTo f _ => f.silent
  | .last l => if l = .selfdestruct then false else true
  | .next n f => n.stateSilent && f.silent
  | .dest f => f.silent
  | .jump _ => true
  | .callNext _ f => f.silent
  | .ret => true
  | .undefined => true

/-- Entry indices mentioned by a synthetic tree. -/
def SFunc.refs : SFunc → List Nat
  | .branch f g => f.refs ++ g.refs
  | .branchTo f k => k :: f.refs
  | .last _ => []
  | .next _ f => f.refs
  | .dest f => f.refs
  | .jump k => [k]
  | .callNext k f => k :: f.refs
  | .ret => []
  | .undefined => []

/-- `S` is closed under the entries referenced by its members. -/
def SilentSet (fs : List SFunc) (S : List Nat) : Bool :=
  S.all fun k => match fs[k]? with
    | some g => g.silent && g.refs.all (· ∈ S)
    | none => false

namespace Outcome

/-- Forget whether a synthetic run halted or returned. -/
def devm : Outcome → Devm
  | .halted d => d
  | .returned d => d

end Outcome

private theorem ninst_state_of_silent {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (hn : n.stateSilent = true) (run : Ninst.Run sevm pre n post) :
    post.state = pre.state := by
  cases n with
  | reg r =>
      rcases run with ⟨xl, -, pc, hrun⟩
      simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at hrun
      have hrun' : Rinst.run ⟨pc, sevm, pre⟩ r = .ok post := hrun.2.symm
      rcases eq_or_ne r .tstore with rfl | ht
      · have hframe := Rinst.tstore_run_transientWriteFrame pc pre sevm
        rw [hrun'] at hframe
        exact hframe.state.symm
      · have hsstore : r ≠ .sstore := by
          intro h
          subst r
          simp [Ninst.stateSilent] at hn
        have hframe := Rinst.preserves_state (pc := pc) (sevm := sevm)
          (pre := pre) (post := post) hsstore ht hrun'
        exact hframe.symm
  | exec x => simp [Ninst.stateSilent] at hn
  | push bs hbs =>
      rcases run with ⟨xl, -, pc, hrun⟩
      have hxl : xl = .none := by
        simp only [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at hrun
        exact hrun.1
      subst xl
      have hrel := Ninst.push_effectRec_of_instructionFrame
        (R := fun a b : Devm => a.state = b.state) (fun _ _ h => h.state)
        (pc := pc) (sevm := sevm) (pre := pre) (xl := .none) (out := .ok post)
        trivial hrun
      exact hrel.symm
  | dupn imm =>
      rcases run with ⟨xl, -, pc, hrun⟩
      have hxl : xl = .none := by
        simp only [Ninst.StepRun, Ninst.step_dupn, Step.run_ofExecution] at hrun
        exact hrun.1
      subst xl
      have hrel := Ninst.dupn_effectRec_of_instructionFrame
        (R := fun a b : Devm => a.state = b.state) (fun _ _ h => h.state)
        (pc := pc) (sevm := sevm) (pre := pre) (xl := .none) (out := .ok post)
        trivial hrun
      exact hrel.symm
  | swapn imm =>
      rcases run with ⟨xl, -, pc, hrun⟩
      have hxl : xl = .none := by
        simp only [Ninst.StepRun, Ninst.step_swapn, Step.run_ofExecution] at hrun
        exact hrun.1
      subst xl
      have hrel := Ninst.swapn_effectRec_of_instructionFrame
        (R := fun a b : Devm => a.state = b.state) (fun _ _ h => h.state)
        (pc := pc) (sevm := sevm) (pre := pre) (xl := .none) (out := .ok post)
        trivial hrun
      exact hrel.symm
  | exchange imm =>
      rcases run with ⟨xl, -, pc, hrun⟩
      have hxl : xl = .none := by
        simp only [Ninst.StepRun, Ninst.step_exchange, Step.run_ofExecution] at hrun
        exact hrun.1
      subst xl
      have hrel := Ninst.exchange_effectRec_of_instructionFrame
        (R := fun a b : Devm => a.state = b.state) (fun _ _ h => h.state)
        (pc := pc) (sevm := sevm) (pre := pre) (xl := .none) (out := .ok post)
        trivial hrun
      exact hrel.symm

private theorem linst_state_of_silent {sevm : Sevm} {pre post : Devm} {l : Linst}
    (hl : (l != .selfdestruct) = true) (run : Linst.Run sevm pre l (.ok post)) :
    post.state = pre.state := by
  have hnot : l ≠ .selfdestruct := by
    intro h
    subst l
    simp at hl
  have hframe := Linst.run_instructionFrame sevm pre l hnot
  rw [run] at hframe
  exact hframe.state.symm

theorem SFunc.Run.state_of_silent {fs : List SFunc} {S : List Nat}
    (hS : SilentSet fs S = true) {sevm : Sevm} {devm : Devm} {f : SFunc} {o : Outcome}
    (hf : f.silent = true) (hrefs : f.refs.all (· ∈ S) = true)
    (run : SFunc.Run fs sevm devm f o) :
    (Outcome.devm o).state = devm.state := by
  have closed : ∀ {k g}, k ∈ S → fs[k]? = some g →
      g.silent = true ∧ g.refs.all (· ∈ S) = true := by
    intro k g hk hget
    have h := (List.all_eq_true.mp hS) k hk
    rw [hget] at h
    simpa using h
  induction run with
  | zero d pop run ih =>
      have hff := hf
      have hfr := hrefs
      simp only [SFunc.silent, Bool.and_eq_true] at hff
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hfr
      simpa [Outcome.devm] using (ih hff.1 hfr.1).trans pop.state.symm
  | succ d w hnz pop run ih =>
      have hff := hf
      have hfr := hrefs
      simp only [SFunc.silent, Bool.and_eq_true] at hff
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hfr
      simpa [Outcome.devm] using (ih hff.2 hfr.2).trans pop.state.symm
  | toZero d pop run ih =>
      have hfr := hrefs
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hfr
      simpa [Outcome.devm] using (ih hf hfr.2).trans pop.state.symm
  | toSucc d w hnz lookup pop run ih =>
      have hfr := hrefs
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hfr
      have htarget := closed (of_decide_eq_true hfr.1) lookup
      simpa [SFunc.refs, SFunc.silent, Outcome.devm] using
        (ih htarget.1 htarget.2).trans pop.state.symm
  | last hrun =>
      simpa [Outcome.devm] using linst_state_of_silent (by simpa [SFunc.silent] using hf) hrun
  | next hrun run ih =>
      have hfn := hf
      simp only [SFunc.silent, Bool.and_eq_true] at hfn
      simpa [Outcome.devm] using
        (ih hfn.2 hrefs).trans (ninst_state_of_silent hfn.1 hrun)
  | dest burn run ih =>
      simpa [Outcome.devm] using (ih hf hrefs).trans burn.state.symm
  | jump d lookup pop run ih =>
      have hfr := hrefs
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hfr
      have htarget := closed (of_decide_eq_true hfr.1) lookup
      simpa [Outcome.devm] using (ih htarget.1 htarget.2).trans pop.state.symm
  | ret d pop =>
      simpa [Outcome.devm] using pop.state.symm
  | callHalt d lookup pop run ih =>
      have hfr := hrefs
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hfr
      have htarget := closed (of_decide_eq_true hfr.1) lookup
      simpa [Outcome.devm] using (ih htarget.1 htarget.2).trans pop.state.symm
  | callRet d lookup pop run tail ihRun ihTail =>
      have hfr := hrefs
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hfr
      have htarget := closed (of_decide_eq_true hfr.1) lookup
      have hfn := hf
      simp only [SFunc.silent] at hfn
      simpa [Outcome.devm] using
        (ihTail hfn hfr.2).trans ((ihRun htarget.1 htarget.2).trans pop.state.symm)

section Weth9

open Weth9

theorem Weth9.views_silent :
    SilentSet Weth9.prog [2, 4, 6, 7, 10, 12, 14, 15, 16, 17] = true := by
  decide +kernel

end Weth9

end Blanc.Lift
