import Blanc.Lift.Silent

namespace Blanc.Lift

open Jaune

/-- A tree with at most `budget` calls remaining.  Gotos are required to
belong to the state-silent entry set; a call consumes one unit and its
continuation has no calls left. -/
def SFunc.silentCalls (S : List Nat) : Nat → SFunc → Bool
  | b, .branch f g => f.silentCalls S b && g.silentCalls S b
  | b, .branchTo f k => (k ∈ S) && f.silentCalls S b
  | _, .last l => if l = .selfdestruct then false else true
  | b, .next n f => n.stateSilent && f.silentCalls S b
  | b, .dest f => f.silentCalls S b
  | _, .jump k => k ∈ S
  | 0, .callNext _ _ => false
  | b + 1, .callNext _ f => f.silentCalls S b
  | _, .ret => true
  | _, .undefined => true

/-- As `silentCalls`, but a jump to an entry in `W` is treated as the one
remaining call.  This is the shape of a selector wrapper: its dispatcher
goto consumes the budget, and the wrapper itself contains the callee call. -/
def SFunc.silentCallsWith (S W : List Nat) : Nat → SFunc → Bool
  | 0, f => f.silentCalls S 0
  | b + 1, .branch f g => f.silentCallsWith S W (b + 1) && g.silentCallsWith S W (b + 1)
  | b + 1, .branchTo f k =>
      (k ∈ S || k ∈ W) && f.silentCallsWith S W (b + 1)
  | b + 1, .last l => if l = .selfdestruct then false else true
  | b + 1, .next n f => n.stateSilent && f.silentCallsWith S W (b + 1)
  | b + 1, .dest f => f.silentCallsWith S W (b + 1)
  | b + 1, .jump k => k ∈ S || k ∈ W
  | b + 1, .callNext _ f => f.silentCallsWith S W b
  | b + 1, .ret => true
  | b + 1, .undefined => true

/-- The `callNext` entry indices occurring in a tree. -/
def SFunc.callRefs : SFunc → List Nat
  | .branch f g => f.callRefs ++ g.callRefs
  | .branchTo f _ => f.callRefs
  | .last _ => []
  | .next _ f => f.callRefs
  | .dest f => f.callRefs
  | .jump _ => []
  | .callNext k f => k :: f.callRefs
  | .ret => []
  | .undefined => []

private theorem silentCalls0_silent_refs {S : List Nat} {f : SFunc}
    (h : f.silentCalls S 0 = true) :
    f.silent = true ∧ f.refs.all (· ∈ S) = true := by
  induction f with
  | branch f g ihf ihg =>
      simp only [SFunc.silentCalls, SFunc.silent, SFunc.refs, List.all_append,
        Bool.and_eq_true] at h ⊢
      exact ⟨⟨(ihf h.1).1, (ihg h.2).1⟩, ⟨(ihf h.1).2, (ihg h.2).2⟩⟩
  | branchTo f k ih =>
      simp only [SFunc.silentCalls, SFunc.silent, SFunc.refs, List.all_cons,
        Bool.and_eq_true] at h ⊢
      exact ⟨(ih h.2).1, h.1, (ih h.2).2⟩
  | last l =>
      simp only [SFunc.silentCalls, SFunc.silent, SFunc.refs] at h ⊢
      exact ⟨h, rfl⟩
  | next n f ih =>
      simp only [SFunc.silentCalls, SFunc.silent, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1, (ih h.2).1⟩, (ih h.2).2⟩
  | dest f ih =>
      exact ih h
  | jump k =>
      simp only [SFunc.silentCalls, SFunc.silent, SFunc.refs] at h ⊢
      exact ⟨True.intro, by simpa using h⟩
  | callNext k f ih =>
      simp [SFunc.silentCalls] at h
  | ret => simp [SFunc.silentCalls, SFunc.silent, SFunc.refs]
  | undefined => simp [SFunc.silentCalls, SFunc.silent, SFunc.refs]

private theorem ninst_state_of_silent' {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (hn : n.stateSilent = true) (run : Ninst.Run sevm pre n post) :
    post.state = pre.state := by
  cases n with
  | reg r =>
      obtain ⟨xl, -, pc, hrun⟩ := run
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

private theorem linst_state_of_silent' {sevm : Sevm} {pre post : Devm} {l : Linst}
    (hl : (l != .selfdestruct) = true) (run : Linst.Run sevm pre l (.ok post)) :
    post.state = pre.state := by
  have hnot : l ≠ .selfdestruct := by
    intro h
    subst l
    simp at hl
  have hframe := Linst.run_instructionFrame sevm pre l hnot
  have hframe' := hframe
  rw [run] at hframe'
  exact hframe'.state.symm

theorem SFunc.RunP.hoare_single_call {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {fs : List SFunc} {S K : List Nat} {sevm : Sevm} {devm : Devm}
    {f : SFunc} {o : Outcome} {Φ₀ Φ₁ : Devm → Prop}
    (hS : SilentSet fs S = true)
    (hzero : ∀ {k g}, k ∈ S → fs[k]? = some g → g.silentCalls S 0 = true)
    (h01 : ∀ d, Φ₀ d → Φ₁ d)
    (hstable0 : ∀ {d d'}, d.state = d'.state → Φ₀ d → Φ₀ d')
    (hstable1 : ∀ {d d'}, d.state = d'.state → Φ₁ d → Φ₁ d')
    (hspec : ∀ {k g}, k ∈ K → fs[k]? = some g →
      ∀ {d o}, Φ₀ d → SFunc.RunP P fs sevm d g o → Φ₁ (Outcome.devm o))
    (hsc : f.silentCalls S 1 = true)
    (hcalls : f.callRefs.all (· ∈ K) = true)
    (run : SFunc.RunP P fs sevm devm f o) (h0 : Φ₀ devm) :
    Φ₁ (Outcome.devm o) := by
  have silent_preserve : ∀ {Ψ : Devm → Prop},
      (∀ {d d'}, d.state = d'.state → Ψ d → Ψ d') →
      ∀ {d : Devm} {g : SFunc} {q : Outcome},
        SFunc.RunP P fs sevm d g q → g.silentCalls S 0 = true →
          Ψ d → Ψ (Outcome.devm q) := by
    intro Ψ hstable d g q r
    intro hzero' hp
    obtain ⟨hg, hrefs⟩ := silentCalls0_silent_refs hzero'
    apply hstable (SFunc.RunP.state_of_silent hP hS hg hrefs r).symm hp
  have go : ∀ {d : Devm} {g : SFunc} {q : Outcome},
      SFunc.RunP P fs sevm d g q → g.silentCalls S 1 = true →
        g.callRefs.all (· ∈ K) = true → Φ₀ d → Φ₁ (Outcome.devm q) := by
    intro d g q r
    induction r with
    | zero d pop run ih =>
        intro hsc' hcalls' hp
        have hsc'' := hsc'
        have hcalls'' := hcalls'
        simp only [SFunc.silentCalls, Bool.and_eq_true] at hsc''
        simp only [SFunc.callRefs, List.all_append, Bool.and_eq_true] at hcalls''
        apply ih hsc''.1 hcalls''.1 (hstable0 pop.state hp)
    | succ d w hnz pop run ih =>
        intro hsc' hcalls' hp
        have hsc'' := hsc'
        have hcalls'' := hcalls'
        simp only [SFunc.silentCalls, Bool.and_eq_true] at hsc''
        simp only [SFunc.callRefs, List.all_append, Bool.and_eq_true] at hcalls''
        apply ih hsc''.2 hcalls''.2 (hstable0 pop.state hp)
    | toZero d pop run ih =>
        intro hsc' hcalls' hp
        have hsc'' := hsc'
        simp only [SFunc.silentCalls, Bool.and_eq_true] at hsc''
        apply ih hsc''.2 hcalls' (hstable0 pop.state hp)
    | toSucc d w hnz lookup pop run ih =>
        intro hsc' hcalls' hp
        have hsc'' := hsc'
        simp only [SFunc.silentCalls, Bool.and_eq_true] at hsc''
        have htarget := hzero (of_decide_eq_true hsc''.1) lookup
        have hp' := hstable0 pop.state hp
        exact h01 _ (silent_preserve hstable0 run htarget hp')
    | last hrun =>
        intro hsc' hcalls' hp
        have hstep := linst_state_of_silent' (by simpa [SFunc.silentCalls] using hsc') hrun
        exact h01 _ (hstable0 hstep.symm hp)
    | next hrun run ih =>
        intro hsc' hcalls' hp
        have hsc'' := hsc'
        simp only [SFunc.silentCalls, Bool.and_eq_true] at hsc''
        have hstep := ninst_state_of_silent' hsc''.1 (hP hrun)
        apply ih hsc''.2 hcalls' (hstable0 hstep.symm hp)
    | dest burn run ih =>
        intro hsc' hcalls' hp
        apply ih hsc' hcalls' (hstable0 burn.state hp)
    | jump d lookup pop run ih =>
        intro hsc' hcalls' hp
        have htarget := hzero (of_decide_eq_true hsc') lookup
        exact h01 _ (silent_preserve hstable0 run htarget (hstable0 pop.state hp))
    | ret d pop =>
        intro hsc' hcalls' hp
        exact h01 _ (hstable0 pop.state hp)
    | callHalt d lookup pop run ih =>
        intro hsc' hcalls' hp
        have hcalls'' := hcalls'
        simp only [SFunc.callRefs, List.all_cons, Bool.and_eq_true] at hcalls''
        have hk : _ := of_decide_eq_true hcalls''.1
        exact hspec hk lookup (hstable0 pop.state hp) run
    | callRet d lookup pop run tail ihRun ihTail =>
        intro hsc' hcalls' hp
        have hsc'' := hsc'
        have hcalls'' := hcalls'
        simp only [SFunc.silentCalls] at hsc''
        simp only [SFunc.callRefs, List.all_cons, Bool.and_eq_true] at hcalls''
        have hk : _ := of_decide_eq_true hcalls''.1
        have hcallee := hspec hk lookup (hstable0 pop.state hp) run
        exact silent_preserve hstable1 tail hsc'' hcallee
  exact go run hsc hcalls h0

theorem SFunc.RunP.hoare_single_call_with_gotos {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {fs : List SFunc} {S W K : List Nat} {sevm : Sevm} {devm : Devm}
    {f : SFunc} {o : Outcome} {Φ₀ Φ₁ : Devm → Prop}
    (hS : SilentSet fs S = true)
    (hzero : ∀ {k g}, k ∈ S → fs[k]? = some g → g.silentCalls S 0 = true)
    (h01 : ∀ d, Φ₀ d → Φ₁ d)
    (hstable0 : ∀ {d d'}, d.state = d'.state → Φ₀ d → Φ₀ d')
    (hstable1 : ∀ {d d'}, d.state = d'.state → Φ₁ d → Φ₁ d')
    (hspec : ∀ {k g}, k ∈ K → fs[k]? = some g →
      ∀ {d o}, Φ₀ d → SFunc.RunP P fs sevm d g o → Φ₁ (Outcome.devm o))
    (hwrap : ∀ {k g}, k ∈ W → fs[k]? = some g →
      ∀ {d o}, Φ₀ d → SFunc.RunP P fs sevm d g o → Φ₁ (Outcome.devm o))
    (hsc : f.silentCallsWith S W 1 = true)
    (hcalls : f.callRefs.all (· ∈ K) = true)
    (run : SFunc.RunP P fs sevm devm f o) (h0 : Φ₀ devm) :
    Φ₁ (Outcome.devm o) := by
  have silent_preserve : ∀ {Ψ : Devm → Prop},
      (∀ {d d'}, d.state = d'.state → Ψ d → Ψ d') →
      ∀ {d : Devm} {g : SFunc} {q : Outcome},
        SFunc.RunP P fs sevm d g q → g.silentCallsWith S W 0 = true →
          Ψ d → Ψ (Outcome.devm q) := by
    intro Ψ hstable d g q r
    intro hzero' hp
    obtain ⟨hg, hrefs⟩ := silentCalls0_silent_refs
      (by simpa [SFunc.silentCallsWith] using hzero')
    apply hstable (SFunc.RunP.state_of_silent hP hS hg hrefs r).symm hp
  have go : ∀ {d : Devm} {g : SFunc} {q : Outcome},
      SFunc.RunP P fs sevm d g q → g.silentCallsWith S W 1 = true →
        g.callRefs.all (· ∈ K) = true → Φ₀ d → Φ₁ (Outcome.devm q) := by
    intro d g q r
    induction r with
    | zero d pop run ih =>
        intro hsc' hcalls' hp
        have hsc'' := hsc'
        have hcalls'' := hcalls'
        simp only [SFunc.silentCallsWith, Bool.and_eq_true] at hsc''
        simp only [SFunc.callRefs, List.all_append, Bool.and_eq_true] at hcalls''
        apply ih hsc''.1 hcalls''.1 (hstable0 pop.state hp)
    | succ d w hnz pop run ih =>
        intro hsc' hcalls' hp
        have hsc'' := hsc'
        have hcalls'' := hcalls'
        simp only [SFunc.silentCallsWith, Bool.and_eq_true] at hsc''
        simp only [SFunc.callRefs, List.all_append, Bool.and_eq_true] at hcalls''
        apply ih hsc''.2 hcalls''.2 (hstable0 pop.state hp)
    | toZero d pop run ih =>
        intro hsc' hcalls' hp
        have hsc'' := hsc'
        simp only [SFunc.silentCallsWith, Bool.and_eq_true] at hsc''
        apply ih hsc''.2 hcalls' (hstable0 pop.state hp)
    | toSucc d w hnz lookup pop run ih =>
        intro hsc' hcalls' hp
        have hsc'' := hsc'
        simp only [SFunc.silentCallsWith, Bool.and_eq_true] at hsc''
        have hp' := hstable0 pop.state hp
        have hbranch := hsc''.1
        simp only [Bool.or_eq_true] at hbranch
        rcases hbranch with hs | hw
        · have htarget := hzero (of_decide_eq_true hs) lookup
          exact h01 _ (silent_preserve hstable0 run
            (by simpa [SFunc.silentCallsWith] using htarget) hp')
        · exact hwrap (of_decide_eq_true hw) lookup hp' run
    | last hrun =>
        intro hsc' hcalls' hp
        have hstep := linst_state_of_silent' (by simpa [SFunc.silentCallsWith] using hsc') hrun
        exact h01 _ (hstable0 hstep.symm hp)
    | next hrun run ih =>
        intro hsc' hcalls' hp
        have hsc'' := hsc'
        simp only [SFunc.silentCallsWith, Bool.and_eq_true] at hsc''
        have hstep := ninst_state_of_silent' hsc''.1 (hP hrun)
        apply ih hsc''.2 hcalls' (hstable0 hstep.symm hp)
    | dest burn run ih =>
        intro hsc' hcalls' hp
        apply ih hsc' hcalls' (hstable0 burn.state hp)
    | jump d lookup pop run ih =>
        intro hsc' hcalls' hp
        have hp' := hstable0 pop.state hp
        simp only [SFunc.silentCallsWith, Bool.or_eq_true] at hsc'
        rcases hsc' with hs | hw
        · have htarget := hzero (of_decide_eq_true hs) lookup
          exact h01 _ (silent_preserve hstable0 run
            (by simpa [SFunc.silentCallsWith] using htarget) hp')
        · exact hwrap (of_decide_eq_true hw) lookup hp' run
    | ret d pop =>
        intro hsc' hcalls' hp
        exact h01 _ (hstable0 pop.state hp)
    | callHalt d lookup pop run ih =>
        intro hsc' hcalls' hp
        have hcalls'' := hcalls'
        simp only [SFunc.callRefs, List.all_cons, Bool.and_eq_true] at hcalls''
        have hk : _ := of_decide_eq_true hcalls''.1
        exact hspec hk lookup (hstable0 pop.state hp) run
    | callRet d lookup pop run tail ihRun ihTail =>
        intro hsc' hcalls' hp
        have hsc'' := hsc'
        have hcalls'' := hcalls'
        simp only [SFunc.silentCallsWith] at hsc''
        simp only [SFunc.callRefs, List.all_cons, Bool.and_eq_true] at hcalls''
        have hk : _ := of_decide_eq_true hcalls''.1
        have hcallee := hspec hk lookup (hstable0 pop.state hp) run
        exact silent_preserve hstable1 tail
          (by simpa [SFunc.silentCallsWith] using hsc'') hcallee
  exact go run hsc hcalls h0

theorem SFunc.RunP.hoare_wrapper {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {fs : List SFunc} {S : List Nat} {k : Nat} {sevm : Sevm} {devm : Devm}
    {wrapper callee : SFunc} {o : Outcome} {Φ₀ Φ₁ : Devm → Prop}
    (hS : SilentSet fs S = true)
    (hzero : ∀ {j g}, j ∈ S → fs[j]? = some g → g.silentCalls S 0 = true)
    (h01 : ∀ d, Φ₀ d → Φ₁ d)
    (hstable0 : ∀ {d d'}, d.state = d'.state → Φ₀ d → Φ₀ d')
    (hstable1 : ∀ {d d'}, d.state = d'.state → Φ₁ d → Φ₁ d')
    (hlookup : fs[k]? = some callee)
    (hcallee : ∀ {d o}, Φ₀ d → SFunc.RunP P fs sevm d callee o → Φ₁ (Outcome.devm o))
    (hsc : wrapper.silentCalls S 1 = true)
    (hcalls : wrapper.callRefs.all (· ∈ [k]) = true)
    (run : SFunc.RunP P fs sevm devm wrapper o) (h0 : Φ₀ devm) :
    Φ₁ (Outcome.devm o) := by
  apply SFunc.RunP.hoare_single_call hP hS hzero h01 hstable0 hstable1
    (fun {j g} hj hjg => by
      have hjk : j = k := by simpa using hj
      subst j
      have hcg : callee = g := Option.some.inj (hlookup.symm.trans hjg)
      subst g
      intro d o hd hr
      exact hcallee hd hr) hsc hcalls run h0

theorem SFunc.Run.hoare_single_call
    {fs : List SFunc} {S K : List Nat} {sevm : Sevm} {devm : Devm}
    {f : SFunc} {o : Outcome} {Φ₀ Φ₁ : Devm → Prop}
    (hS : SilentSet fs S = true)
    (hzero : ∀ {k g}, k ∈ S → fs[k]? = some g → g.silentCalls S 0 = true)
    (h01 : ∀ d, Φ₀ d → Φ₁ d)
    (hstable0 : ∀ {d d'}, d.state = d'.state → Φ₀ d → Φ₀ d')
    (hstable1 : ∀ {d d'}, d.state = d'.state → Φ₁ d → Φ₁ d')
    (hspec : ∀ {k g}, k ∈ K → fs[k]? = some g →
      ∀ {d o}, Φ₀ d → SFunc.Run fs sevm d g o → Φ₁ (Outcome.devm o))
    (hsc : f.silentCalls S 1 = true)
    (hcalls : f.callRefs.all (· ∈ K) = true)
    (run : SFunc.Run fs sevm devm f o) (h0 : Φ₀ devm) :
    Φ₁ (Outcome.devm o) :=
  SFunc.RunP.hoare_single_call id hS hzero h01 hstable0 hstable1 hspec hsc hcalls run h0

theorem SFunc.Run.hoare_single_call_with_gotos
    {fs : List SFunc} {S W K : List Nat} {sevm : Sevm} {devm : Devm}
    {f : SFunc} {o : Outcome} {Φ₀ Φ₁ : Devm → Prop}
    (hS : SilentSet fs S = true)
    (hzero : ∀ {k g}, k ∈ S → fs[k]? = some g → g.silentCalls S 0 = true)
    (h01 : ∀ d, Φ₀ d → Φ₁ d)
    (hstable0 : ∀ {d d'}, d.state = d'.state → Φ₀ d → Φ₀ d')
    (hstable1 : ∀ {d d'}, d.state = d'.state → Φ₁ d → Φ₁ d')
    (hspec : ∀ {k g}, k ∈ K → fs[k]? = some g →
      ∀ {d o}, Φ₀ d → SFunc.Run fs sevm d g o → Φ₁ (Outcome.devm o))
    (hwrap : ∀ {k g}, k ∈ W → fs[k]? = some g →
      ∀ {d o}, Φ₀ d → SFunc.Run fs sevm d g o → Φ₁ (Outcome.devm o))
    (hsc : f.silentCallsWith S W 1 = true)
    (hcalls : f.callRefs.all (· ∈ K) = true)
    (run : SFunc.Run fs sevm devm f o) (h0 : Φ₀ devm) :
    Φ₁ (Outcome.devm o) :=
  SFunc.RunP.hoare_single_call_with_gotos id hS hzero h01 hstable0 hstable1 hspec hwrap hsc hcalls run h0

theorem SFunc.Run.hoare_wrapper
    {fs : List SFunc} {S : List Nat} {k : Nat} {sevm : Sevm} {devm : Devm}
    {wrapper callee : SFunc} {o : Outcome} {Φ₀ Φ₁ : Devm → Prop}
    (hS : SilentSet fs S = true)
    (hzero : ∀ {j g}, j ∈ S → fs[j]? = some g → g.silentCalls S 0 = true)
    (h01 : ∀ d, Φ₀ d → Φ₁ d)
    (hstable0 : ∀ {d d'}, d.state = d'.state → Φ₀ d → Φ₀ d')
    (hstable1 : ∀ {d d'}, d.state = d'.state → Φ₁ d → Φ₁ d')
    (hlookup : fs[k]? = some callee)
    (hcallee : ∀ {d o}, Φ₀ d → SFunc.Run fs sevm d callee o → Φ₁ (Outcome.devm o))
    (hsc : wrapper.silentCalls S 1 = true)
    (hcalls : wrapper.callRefs.all (· ∈ [k]) = true)
    (run : SFunc.Run fs sevm devm wrapper o) (h0 : Φ₀ devm) :
    Φ₁ (Outcome.devm o) :=
  SFunc.RunP.hoare_wrapper id hS hzero h01 hstable0 hstable1 hlookup hcallee hsc hcalls run h0

section Weth9

open Weth9

private instance : Inhabited SFunc := ⟨.undefined⟩

def Weth9.silentSet : List Nat := [2, 4, 5, 6, 7, 10, 12, 13, 14, 15, 16, 17]

def Weth9.wrapperSet : List Nat := [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

def Weth9.wrapperSpecs : List (Nat × Nat) :=
  [(18, 2), (19, 1), (20, 3), (21, 4), (22, 6), (23, 7),
   (24, 8), (25, 9), (26, 10), (27, 11), (28, 12)]

theorem Weth9.silentSet_closed :
    SilentSet Weth9.prog Weth9.silentSet = true := by
  decide +kernel

theorem Weth9.silentSet_no_calls :
    Weth9.silentSet.all (fun k => match Weth9.prog[k]? with
      | some g => g.silentCalls Weth9.silentSet 0
      | none => false) = true := by
  decide +kernel

theorem Weth9.entry0_silentCalls :
    (Weth9.prog[0]!).silentCallsWith Weth9.silentSet Weth9.wrapperSet 1 = true := by
  change t_0000_c0.silentCallsWith Weth9.silentSet Weth9.wrapperSet 1 = true
  decide +kernel

theorem Weth9.entry0_callRefs :
    t_0000_c0.callRefs.all (· ∈ [1]) = true := by
  decide +kernel

theorem Weth9.wrapper_entries_silentCalls :
    Weth9.wrapperSpecs.all (fun p =>
      match Weth9.prog[p.1]? with
      | some g => g.silentCallsWith Weth9.silentSet Weth9.wrapperSet 1 &&
          g.callRefs.all (· ∈ [p.2])
      | none => false) = true := by
  decide +kernel

end Weth9

end Blanc.Lift
