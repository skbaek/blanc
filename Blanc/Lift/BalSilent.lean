import Blanc.Lift.Silent

/-!
# Balance-silent synthetic trees

A synthetic tree whose instructions never execute an `.exec` instruction
(`CALL`, `CREATE`, …) and whose terminal is not `SELFDESTRUCT` leaves every
account's ether balance unchanged: storage writes (`SSTORE`) are allowed.
This is the balance half of `SFunc.Run.state_of_silent`, for trees that write
storage.
-/

namespace Jaune

/-- A nonterminal instruction that cannot move ether. -/
def Ninst.balSilent : Ninst → Bool
  | .exec _ => false
  | _ => true

end Jaune

namespace Blanc.Lift

open Jaune

/-- A synthetic tree whose instructions and terminal cannot move ether. -/
def SFunc.balSilent : SFunc → Bool
  | .branch f g => f.balSilent && g.balSilent
  | .branchTo f _ => f.balSilent
  | .last l => if l = .selfdestruct then false else true
  | .next n f => n.balSilent && f.balSilent
  | .dest f => f.balSilent
  | .jump _ => true
  | .callNext _ f => f.balSilent
  | .ret => true
  | .undefined => true

/-- `S` is closed under the entries referenced by its members, all of which
are balance-silent. -/
def BalSilentSet (fs : List SFunc) (S : List Nat) : Bool :=
  S.all fun k => match fs[k]? with
    | some g => g.balSilent && g.refs.all (· ∈ S)
    | none => false

theorem Ninst.Run.getBal_of_balSilent {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (hn : n.balSilent = true) (run : Ninst.Run sevm pre n post) :
    post.getBal = pre.getBal := by
  cases n with
  | reg r =>
      rcases run with ⟨xl, -, pc, hrun⟩
      simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at hrun
      have hrun' : Rinst.run ⟨pc, sevm, pre⟩ r = .ok post := hrun.2.symm
      exact (Rinst.preserves_bal hrun').symm
  | exec x => simp [Ninst.balSilent] at hn
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
      exact funext (getBal_eq_of_state_eq hrel.symm)
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
      exact funext (getBal_eq_of_state_eq hrel.symm)
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
      exact funext (getBal_eq_of_state_eq hrel.symm)
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
      exact funext (getBal_eq_of_state_eq hrel.symm)

private theorem linst_getBal {sevm : Sevm} {pre post : Devm} {l : Linst}
    (hl : (if l = .selfdestruct then false else true) = true)
    (run : Linst.Run sevm pre l (.ok post)) :
    post.getBal = pre.getBal := by
  have hnot : l ≠ .selfdestruct := by
    intro h
    subst l
    simp at hl
  have hframe := Linst.run_instructionFrame sevm pre l hnot
  rw [run] at hframe
  exact funext (getBal_eq_of_state_eq hframe.state.symm)

/-- **A balance-silent run moves no ether.** -/
theorem SFunc.RunP.getBal_of_balSilent {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {fs : List SFunc} {S : List Nat}
    (hS : BalSilentSet fs S = true) {sevm : Sevm} {devm : Devm} {f : SFunc}
    {o : Outcome} (hf : f.balSilent = true) (hrefs : f.refs.all (· ∈ S) = true)
    (run : SFunc.RunP P fs sevm devm f o) :
    (Outcome.devm o).getBal = devm.getBal := by
  have closed : ∀ {k g}, k ∈ S → fs[k]? = some g →
      g.balSilent = true ∧ g.refs.all (· ∈ S) = true := by
    intro k g hk hget
    have h := (List.all_eq_true.mp hS) k hk
    rw [hget] at h
    simpa using h
  have popBal : ∀ {xs : List B256} {a b : Devm}, Devm.PopBurn xs a b →
      b.getBal = a.getBal := fun pop => funext (getBal_eq_of_state_eq pop.state.symm)
  induction run with
  | zero d pop run ih =>
      have hff := hf
      have hfr := hrefs
      simp only [SFunc.balSilent, Bool.and_eq_true] at hff
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hfr
      exact (ih hff.1 hfr.1).trans (popBal pop)
  | succ d w hnz pop run ih =>
      have hff := hf
      have hfr := hrefs
      simp only [SFunc.balSilent, Bool.and_eq_true] at hff
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hfr
      exact (ih hff.2 hfr.2).trans (popBal pop)
  | toZero d pop run ih =>
      have hfr := hrefs
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hfr
      exact (ih hf hfr.2).trans (popBal pop)
  | toSucc d w hnz lookup pop run ih =>
      have hfr := hrefs
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hfr
      have htarget := closed (of_decide_eq_true hfr.1) lookup
      exact (ih htarget.1 htarget.2).trans (popBal pop)
  | last hrun =>
      exact linst_getBal (by simpa [SFunc.balSilent] using hf) hrun
  | next hrun run ih =>
      have hfn := hf
      simp only [SFunc.balSilent, Bool.and_eq_true] at hfn
      exact (ih hfn.2 hrefs).trans (Ninst.Run.getBal_of_balSilent hfn.1 (hP hrun))
  | dest burn run ih =>
      exact (ih hf hrefs).trans (funext (getBal_eq_of_state_eq burn.state.symm))
  | jump d lookup pop run ih =>
      have hfr := hrefs
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hfr
      have htarget := closed (of_decide_eq_true hfr.1) lookup
      exact (ih htarget.1 htarget.2).trans (popBal pop)
  | ret d pop =>
      exact popBal pop
  | callHalt d lookup pop run ih =>
      have hfr := hrefs
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hfr
      have htarget := closed (of_decide_eq_true hfr.1) lookup
      exact (ih htarget.1 htarget.2).trans (popBal pop)
  | callRet d lookup pop run tail ihRun ihTail =>
      have hfr := hrefs
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hfr
      have htarget := closed (of_decide_eq_true hfr.1) lookup
      have hfn := hf
      simp only [SFunc.balSilent] at hfn
      exact (ihTail hfn hfr.2).trans ((ihRun htarget.1 htarget.2).trans (popBal pop))

/-- **A balance-silent run moves no ether** (over Jaune's steps). -/
theorem SFunc.Run.getBal_of_balSilent {fs : List SFunc} {S : List Nat}
    (hS : BalSilentSet fs S = true) {sevm : Sevm} {devm : Devm} {f : SFunc}
    {o : Outcome} (hf : f.balSilent = true) (hrefs : f.refs.all (· ∈ S) = true)
    (run : SFunc.Run fs sevm devm f o) :
    (Outcome.devm o).getBal = devm.getBal :=
  SFunc.RunP.getBal_of_balSilent id hS hf hrefs run

end Blanc.Lift
