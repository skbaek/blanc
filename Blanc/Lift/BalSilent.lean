import Blanc.Lift.Silent
import Blanc.Lift.Sound
import Blanc.Lift.Quiet
import Blanc.Lift.CallRestriction

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
  | .pcAt _ f => f.balSilent
  | .undefined => true

/-- `S` is closed under the entries referenced by its members, all of which
are balance-silent. -/
def BalSilentSet (fs : List SFunc) (S : List Nat) : Bool :=
  S.all fun k => match fs[k]? with
    | some g => g.balSilent && g.refs.all (· ∈ S)
    | none => false

theorem Ninst.Run.balance_deletion_frame_of_balSilent {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (hn : n.balSilent = true) (run : Ninst.Run sevm pre n post) :
    (post.getBal, Devm.delSets post) = (pre.getBal, Devm.delSets pre) := by
  cases n with
  | reg r =>
      rcases run with ⟨xl, -, pc, hrun⟩
      simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at hrun
      have hrun' : Rinst.run ⟨pc, sevm, pre⟩ r = .ok post := hrun.2.symm
      exact Prod.ext (Rinst.preserves_bal hrun').symm (Rinst.inv_delSets hrun').symm
  | exec x => simp only [Ninst.balSilent, Bool.false_eq_true] at hn
  | push bs hbs =>
      rcases run with ⟨xl, -, pc, hrun⟩
      have hxl : xl = .none := by
        simp only [Ninst.StepRun, Ninst.step_push] at hrun
        split at hrun <;> exact (Step.run_ofExecution.mp hrun).1
      subst xl
      have hrel := Ninst.push_effectRec_of_instructionFrame
        (R := fun a b : Devm => (a.getBal, Devm.delSets a) = (b.getBal, Devm.delSets b))
        (fun _ _ h => Prod.ext (funext (getBal_eq_of_state_eq h.state)) h.delSets)
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
        (R := fun a b : Devm => (a.getBal, Devm.delSets a) = (b.getBal, Devm.delSets b))
        (fun _ _ h => Prod.ext (funext (getBal_eq_of_state_eq h.state)) h.delSets)
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
        (R := fun a b : Devm => (a.getBal, Devm.delSets a) = (b.getBal, Devm.delSets b))
        (fun _ _ h => Prod.ext (funext (getBal_eq_of_state_eq h.state)) h.delSets)
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
        (R := fun a b : Devm => (a.getBal, Devm.delSets a) = (b.getBal, Devm.delSets b))
        (fun _ _ h => Prod.ext (funext (getBal_eq_of_state_eq h.state)) h.delSets)
        (pc := pc) (sevm := sevm) (pre := pre) (xl := .none) (out := .ok post)
        trivial hrun
      exact hrel.symm

/-- A balance-silent instruction preserves every ether balance. -/
theorem Ninst.Run.getBal_of_balSilent {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (hn : n.balSilent = true) (run : Ninst.Run sevm pre n post) :
    post.getBal = pre.getBal :=
  congrArg Prod.fst (Ninst.Run.balance_deletion_frame_of_balSilent hn run)

private theorem linst_balance_deletion_frame {sevm : Sevm} {pre post : Devm} {l : Linst}
    (hl : (if l = .selfdestruct then false else true) = true)
    (run : Linst.Run sevm pre l (.ok post)) :
    (post.getBal, Devm.delSets post) = (pre.getBal, Devm.delSets pre) := by
  have hnot : l ≠ .selfdestruct := by
    intro h
    subst l
    simp only [↓reduceIte, Bool.false_eq_true] at hl
  have hframe := Linst.run_instructionFrame sevm pre l hnot
  rw [run] at hframe
  exact Prod.ext (funext (getBal_eq_of_state_eq hframe.state.symm)) hframe.delSets.symm

/-- A balance-silent run preserves balances and both deletion-tracking sets. -/
theorem SFunc.RunP.balance_deletion_frame_of_balSilent {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {fs : List SFunc} {S : List Nat}
    (hS : BalSilentSet fs S = true) {sevm : Sevm} {devm : Devm} {f : SFunc}
    {o : Outcome} (hf : f.balSilent = true) (hrefs : f.refs.all (· ∈ S) = true)
    (run : SFunc.RunP P fs sevm devm f o) :
    ((Outcome.devm o).getBal, Devm.delSets (Outcome.devm o)) = (devm.getBal, Devm.delSets devm) := by
  have closed : ∀ {k g}, k ∈ S → fs[k]? = some g →
      g.balSilent = true ∧ g.refs.all (· ∈ S) = true := by
    intro k g hk hget
    have h := (List.all_eq_true.mp hS) k hk
    rw [hget] at h
    simpa only [List.all_eq_true, decide_eq_true_eq, Bool.and_eq_true] using h
  have popBal : ∀ {xs : List B256} {a b : Devm}, Devm.PopBurn xs a b →
      (b.getBal, Devm.delSets b) = (a.getBal, Devm.delSets a) := fun pop =>
        Prod.ext (funext (getBal_eq_of_state_eq pop.state.symm))
          (Prod.ext pop.accountsToDelete.symm pop.createdAccounts.symm)
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
      exact linst_balance_deletion_frame (by simpa only [Bool.ite_true_right, Bool.or_false, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not, balSilent] using hf) hrun
  | next hrun run ih =>
      have hfn := hf
      simp only [SFunc.balSilent, Bool.and_eq_true] at hfn
      exact (ih hfn.2 hrefs).trans (Ninst.Run.balance_deletion_frame_of_balSilent hfn.1 (hP hrun))
  | dest burn run ih =>
      exact (ih hf hrefs).trans (Prod.ext (funext (getBal_eq_of_state_eq burn.state.symm))
          (Prod.ext burn.accountsToDelete.symm burn.createdAccounts.symm))
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
  | pcAt hrun _ run ih =>
      exact (ih (by simpa only [balSilent] using hf) (by simpa only [List.all_eq_true,
        decide_eq_true_eq, refs] using hrefs)).trans
        (Ninst.Run.balance_deletion_frame_of_balSilent (n := .reg .pc) rfl (hP hrun))

/-- **A balance-silent run moves no ether.** -/
theorem SFunc.RunP.getBal_of_balSilent {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {fs : List SFunc} {S : List Nat}
    (hS : BalSilentSet fs S = true) {sevm : Sevm} {devm : Devm} {f : SFunc}
    {o : Outcome} (hf : f.balSilent = true) (hrefs : f.refs.all (· ∈ S) = true)
    (run : SFunc.RunP P fs sevm devm f o) :
    (Outcome.devm o).getBal = devm.getBal :=
  congrArg Prod.fst (SFunc.RunP.balance_deletion_frame_of_balSilent hP hS hf hrefs run)

/-- **No successful frame at certified code with no ether-moving node changes a balance**, for any
caller, depth and fork: the certificate's jump closure `S` holds only balance-silent trees. The
lift holds on any fork, since no node is call-family. -/
theorem frame_keeps_balances {code : ByteArray} {c : Cert} {S : List Nat} (hc : Cert.check code c = true)
    (hno : ProgNoExec c.prog) (closed : BalSilentSet c.prog S = true) (root : 0 ∈ S) {sevm : Sevm}
    {pre post : Devm} (hcode : sevm.code = code) (exec : Exec 0 sevm pre (.ok post)) :
    post.getBal = pre.getBal := by
  obtain ⟨f, hf, run⟩ := lift_sound_noExec hc hcode hno exec
  have hat := List.all_eq_true.mp closed 0 root
  rw [hf] at hat
  simp only [Bool.and_eq_true] at hat
  exact SFunc.RunP.getBal_of_balSilent (fun h => h) closed hat.1 hat.2 run

/-- **A `STATICCALL`-only run without `SELFDESTRUCT` moves no ether.** -/
theorem SFunc.RunP.getBal_of_staticcalls
    {P : Sevm → Devm → Ninst → Devm → Prop}
    (actual : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {fs : List SFunc} {sevm : Sevm} {pre : Devm} {f : SFunc} {o : Outcome}
    (closed : ∀ g ∈ fs,
      g.execsSatisfy Xinst.isStaticcall = true ∧ g.noSelfdestruct = true)
    (calls : f.execsSatisfy Xinst.isStaticcall = true)
    (terminal : f.noSelfdestruct = true)
    (run : SFunc.RunP P fs sevm pre f o) :
    (Outcome.devm o).getBal = pre.getBal := by
  have popBal : ∀ {xs : List B256} {a b : Devm}, Devm.PopBurn xs a b →
      b.getBal = a.getBal := fun pop => funext (getBal_eq_of_state_eq pop.state.symm)
  induction run with
  | zero d pop run ih =>
      simp only [SFunc.execsSatisfy, Bool.and_eq_true] at calls
      simp only [SFunc.noSelfdestruct, SFunc.lastsSatisfy, Bool.and_eq_true] at terminal
      exact (ih calls.1 terminal.1).trans (popBal pop)
  | succ d w hnz pop run ih =>
      simp only [SFunc.execsSatisfy, Bool.and_eq_true] at calls
      simp only [SFunc.noSelfdestruct, SFunc.lastsSatisfy, Bool.and_eq_true] at terminal
      exact (ih calls.2 terminal.2).trans (popBal pop)
  | toZero d pop run ih =>
      exact (ih calls terminal).trans (popBal pop)
  | toSucc d w hnz lookup pop run ih =>
      have htarget := closed _ (List.mem_of_getElem? lookup)
      exact (ih htarget.1 htarget.2).trans (popBal pop)
  | @last _ _ l hrun =>
      have hl : (if l = .selfdestruct then false else true) = true := by
        cases l
        · rfl
        · rfl
        · rfl
        · simp only [SFunc.noSelfdestruct, SFunc.lastsSatisfy, Linst.notSelfdestruct,
            Bool.false_eq_true] at terminal
      exact congrArg Prod.fst (linst_balance_deletion_frame hl hrun)
  | @next _ _ n _ _ hrun run ih =>
      have htail_calls := SFunc.execsSatisfy_next_tail calls
      have htail_term : SFunc.noSelfdestruct _ = true := terminal
      have hactual := actual hrun
      have hn_bal := by
        cases n with
        | exec x =>
            simp only [SFunc.execsSatisfy, Bool.and_eq_true] at calls
            cases x <;> simp only [Xinst.isStaticcall, Bool.false_eq_true, false_and] at calls
            exact congrArg Prod.snd (Ninst.staticcall_logs_balances_any hactual)
        | _ => exact Ninst.Run.getBal_of_balSilent rfl hactual
      exact (ih htail_calls htail_term).trans hn_bal
  | dest burn run ih =>
      exact (ih calls terminal).trans (funext (getBal_eq_of_state_eq burn.state.symm))
  | jump d lookup pop run ih =>
      have htarget := closed _ (List.mem_of_getElem? lookup)
      exact (ih htarget.1 htarget.2).trans (popBal pop)
  | ret d pop =>
      exact popBal pop
  | callHalt d lookup pop run ih =>
      have htarget := closed _ (List.mem_of_getElem? lookup)
      exact (ih htarget.1 htarget.2).trans (popBal pop)
  | callRet d lookup pop run tail ihRun ihTail =>
      have htarget := closed _ (List.mem_of_getElem? lookup)
      exact (ihTail calls terminal).trans ((ihRun htarget.1 htarget.2).trans (popBal pop))
  | pcAt hrun _ run ih =>
      exact (ih calls terminal).trans
        (Ninst.Run.getBal_of_balSilent (n := .reg .pc) rfl (actual hrun))

/-- **No successful frame at certified `STATICCALL`-only code without `SELFDESTRUCT` changes any
account balance**, for any caller, depth, and rule set. -/
theorem frame_keeps_balances_of_staticcalls {code : ByteArray} {c : Cert}
    (hc : Cert.check code c = true)
    (only : ∀ f ∈ c.prog, f.execsSatisfy Xinst.isStaticcall = true)
    (nosd : c.noSelfdestruct = true)
    {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = code)
    (exec : Exec 0 sevm pre (.ok post)) :
    post.getBal = pre.getBal := by
  have hstart : ∃ e f c', c = (e, f) :: c' ∧ e.pc = 0 ∧ e.frame = [] ∧
      ([] : List MemMap).getD 0 [] = [] := by
    cases c with
    | nil => simp only [Cert.check, List.all_nil, Bool.and_true, Bool.false_eq_true] at hc
    | cons p c' =>
        rcases p with ⟨e, f⟩
        simp only [Cert.check, List.beq_nil_eq, List.all_cons, Bool.and_eq_true, beq_iff_eq,
          List.isEmpty_iff, List.all_eq_true, Prod.forall] at hc
        exact ⟨e, f, c', rfl, hc.1.1, hc.1.2, rfl⟩
  obtain ⟨f, hf, run⟩ := lift_sound_inM_staticcall (Cert.checkedM_of_check hc) hstart hcode
    (fun x hx => by cases x <;> simp_all only [Xinst.isStaticcall, Bool.false_eq_true])
    only exec
  have hclosed : ∀ g ∈ c.prog,
      g.execsSatisfy Xinst.isStaticcall = true ∧ g.noSelfdestruct = true :=
    fun g hg => ⟨only g hg, Cert.noSelfdestruct_prog nosd g hg⟩
  have hf_mem : f ∈ c.prog := List.mem_of_getElem? hf
  exact SFunc.RunP.getBal_of_staticcalls StepIn.toRun hclosed
    (only f hf_mem) (Cert.noSelfdestruct_prog nosd f hf_mem) run

end Blanc.Lift
