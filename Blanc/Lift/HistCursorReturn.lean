import Blanc.Lift.HistCursorCuts
import Blanc.Lift.CursorQuietReturn
import Blanc.Lift.ReachChain

/-!
# Historical source runs, returns and exec-free suffixes of an actual cursor

`CursorSourceRun`, `CursorSourceRunReturn`, `CursorNoExecSuffix`, `CursorQuietReturn` and
`ReachChain.noExec_after_of_cursor` read their `CoveredFork` premise only through
`node_soundM` and `cursor_stepS`, that is only through `rules.stateGas = none`. The `…H` forms
here take that fact alone, through `node_soundM_noStateGas`, `cursor_stepS_noStateGas` and the
cuts of `HistCursorCuts`. A modern statement is the `…H` form at `CoveredFork.rules_stateGas_none`.

The fork-free return-region invariant is hoisted here as the public
`SFunc.ReturnRegion`/`ConfStep.returnRegion`; `CursorQuietReturn` keeps a private copy.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-! ## Exec-free suffixes -/

/-- `cursor_reach_of_parentPrefix` from `rules.stateGas = none` alone. -/
theorem cursor_reach_of_parentPrefixH {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F N : Exec.Deriv}
    (path : Exec.Deriv.ParentPrefix F N) {κ : Cursor}
    (placed : CursorOK code c F κ) (hsg : F.sevm.benvStat.rules.stateGas = none) :
    ∃ κ', Reach Ninst.Run c.prog F.sevm (κ.conf F.devm) (κ'.conf N.devm) ∧
      CursorOK code c N κ' := by
  induction path generalizing κ with
  | refl root => exact ⟨κ, .refl, placed⟩
  | step edge _ ih =>
    obtain ⟨next, _, primitive, nextPlaced⟩ := cursor_stepS_noStateGas checked placed edge hsg
    have same := Cursor.parentStep_sevm edge
    obtain ⟨last, rest, lastPlaced⟩ := ih nextPlaced (same ▸ hsg)
    refine ⟨last, .head (primitive.mono fun run => run.toRun) ?_, lastPlaced⟩
    simpa only [same] using rest

/-- Exclusion of later external instructions from `rules.stateGas = none` alone. -/
theorem CursorOK.noExecSuffixH {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F : Exec.Deriv} {κ : Cursor}
    (placed : CursorOK code c F κ) (hsg : F.sevm.benvStat.rules.stateGas = none)
    {E : List Nat} (closed : ExecFreeSet c.prog E = true)
    (tree : κ.f.execFreeIn E = true)
    (continuations : ∀ f ∈ κ.K.map Cont.f, f.execFreeIn E = true) :
    ∀ N, Exec.Deriv.ParentPrefix F N → ∀ x,
      ¬ Ninst.At N.sevm.code N.pc (.exec x) := by
  intro N path x decoded
  obtain ⟨next, reach, nextPlaced⟩ := cursor_reach_of_parentPrefixH checked path placed hsg
  obtain ⟨tail, shape, _⟩ := nextPlaced.tree_of_exec decoded
  exact Reach.false_of_execFree closed reach ⟨x, tail, shape⟩ tree continuations

/-- Exclusion of a successful reverting suffix from `rules.stateGas = none` alone. -/
theorem CursorOK.revertLineNoOkH {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F : Exec.Deriv} {κ : Cursor}
    (placed : CursorOK code c F κ) (hsg : F.sevm.benvStat.rules.stateGas = none)
    (ns : List Ninst) (tree : κ.f = ns.foldr SFunc.next (.last .revert))
    {post : Devm} (success : F.exn = .ok post) : False := by
  obtain ⟨N, lastCursor, _, _, _, sameExn, lastPlaced, lastTree⟩ :=
    cursor_nexts_forwardH checked placed ns (.last .revert) tree success hsg
  have opcode : byteAt code lastCursor.pc = some (Linst.toUInt8 .revert) := by
    have check := lastPlaced.check
    rw [lastTree] at check
    simpa only [checkNode, beq_iff_eq] using check
  have instruction : Linst.At N.sevm.code N.pc .revert := by
    rw [lastPlaced.code_eq, lastPlaced.pc_eq]
    exact byteAt_linst_at opcode
  exact Linst.revert_not_ok ((N.exc.last_inv instruction).symm.trans (sameExn.trans success))

/-! ## Call-free internal returns -/

/-- A tree that makes no external call within the closed set `E` and cannot halt: the region
an internal body crosses before its first return. -/
def SFunc.ReturnRegion (E : List Nat) (f : SFunc) : Prop :=
  f.execFreeIn E = true ∧ f.noHalt = true

/-- One synthetic step keeps the current tree and every pending tree inside a return region,
when the referenced entries `E` are exec-free and cannot halt. Fork-free. -/
theorem ConfStep.returnRegion
    {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
    {E : List Nat} (free : ExecFreeSet fs E = true) (closed : NoHaltSet fs E = true)
    {a b : Conf} (step : ConfStep P fs sevm a b) (body : SFunc.ReturnRegion E a.f)
    (locals : ∀ f ∈ a.K, SFunc.ReturnRegion E f) :
    SFunc.ReturnRegion E b.f ∧ ∀ f ∈ b.K, SFunc.ReturnRegion E f := by
  have lookup {k : Nat} {g : SFunc} (member : k ∈ E) (entry : fs[k]? = some g) :
      SFunc.ReturnRegion E g := by
    have noHalt := (List.all_eq_true.mp closed) k member
    rw [entry] at noHalt
    simp only [Bool.and_eq_true] at noHalt
    exact ⟨ExecFreeSet.lookup free member entry, noHalt.1⟩
  cases step with
  | @next d d' n f K _ =>
    refine ⟨?_, locals⟩
    cases n <;> simp_all only [SFunc.ReturnRegion, SFunc.execFreeIn, SFunc.execsSatisfy,
      SFunc.refs, SFunc.noHalt, Bool.and_eq_true, Bool.true_and, Bool.false_and,
      Bool.false_eq_true, and_self, false_and]
  | dest _ => exact ⟨body, locals⟩
  | zero _ _ =>
    simp only [SFunc.ReturnRegion, SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.noHalt,
      SFunc.refs, List.all_append, Bool.and_eq_true] at body ⊢
    exact ⟨⟨⟨body.1.1.1, body.1.2.1⟩, body.2.1⟩,
      by simpa only [SFunc.ReturnRegion, SFunc.execFreeIn, Bool.and_eq_true] using locals⟩
  | succ _ _ _ _ =>
    simp only [SFunc.ReturnRegion, SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.noHalt,
      SFunc.refs, List.all_append, Bool.and_eq_true] at body ⊢
    exact ⟨⟨⟨body.1.1.2, body.1.2.2⟩, body.2.2⟩,
      by simpa only [SFunc.ReturnRegion, SFunc.execFreeIn, Bool.and_eq_true] using locals⟩
  | toZero _ _ =>
    simp only [SFunc.ReturnRegion, SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.noHalt,
      SFunc.refs, List.all_cons, Bool.and_eq_true] at body ⊢
    exact ⟨⟨⟨body.1.1, body.1.2.2⟩, body.2⟩,
      by simpa only [SFunc.ReturnRegion, SFunc.execFreeIn, Bool.and_eq_true] using locals⟩
  | @toSucc d d' f g k K _ _ _ entry _ =>
    simp only [SFunc.ReturnRegion, SFunc.execFreeIn, SFunc.refs, List.all_cons,
      Bool.and_eq_true, decide_eq_true_eq] at body
    exact ⟨lookup body.1.2.1 entry, locals⟩
  | @jump d d' g k K _ entry _ =>
    simp only [SFunc.ReturnRegion, SFunc.execFreeIn, SFunc.refs, List.all_cons,
      List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at body
    exact ⟨lookup body.1.2 entry, locals⟩
  | @call d d' f g k K _ entry _ =>
    simp only [SFunc.ReturnRegion, SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs,
      SFunc.noHalt, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at body
    refine ⟨lookup body.1.2.1 entry, fun s member => ?_⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨by simp only [SFunc.execFreeIn, Bool.and_eq_true]; exact ⟨body.1.1, body.1.2.2⟩,
        body.2⟩
    · exact locals s member
  | ret _ _ => exact ⟨locals _ List.mem_cons_self,
      fun s member => locals s (List.mem_cons_of_mem _ member)⟩
  | pcAt _ _ => exact ⟨body, locals⟩

private theorem cursor_step_of_return_regionH {code : ByteArray} {c : Cert}
    {F : Exec.Deriv} {κ : Cursor} {post : Devm} {E : List Nat}
    (checked : Cert.check code c = true) (placed : CursorOK code c F κ)
    (success : F.exn = .ok post) (hsg : F.sevm.benvStat.rules.stateGas = none)
    (closed : NoHaltSet c.prog E = true) (body : κ.f.noHalt = true)
    (refs : κ.f.refs.all (· ∈ E) = true) :
    ∃ N : Exec.Deriv, Exec.Deriv.ParentStep N F := by
  obtain halted | returned := placed.sourceRunReturnH checked success hsg
  · exact (SFunc.RunP.not_halted closed body refs halted rfl).elim
  · obtain ⟨continuation, tail, state, run, sameK, live, smaller, source, nextPlaced⟩ := returned
    rcases F with ⟨pc, sevm, pre, out, actual⟩
    dsimp only at success
    subst out
    cases actual with
    | halt step =>
      obtain ⟨middle, rest, edge⟩ := smaller
      cases edge
    | cont step next => exact ⟨_, .cont step next⟩
    | doneOk step entered resumed next => exact ⟨_, .doneOk step entered resumed next⟩
    | runOk step entered child resumed next => exact ⟨_, .runOk step entered child resumed next⟩

private theorem cursor_quietReturn_scopedH {code : ByteArray} {c : Cert} {E : List Nat}
    (checked : Cert.check code c = true) (free : ExecFreeSet c.prog E = true)
    (closed : NoHaltSet c.prog E = true) :
    ∀ (F : Exec.Deriv) (κ : Cursor) (locals : List SFunc) (caller : SFunc) (K : List SFunc)
      (post : Devm),
      CursorOK code c F κ → F.exn = .ok post → F.sevm.benvStat.rules.stateGas = none →
      SFunc.ReturnRegion E κ.f → (∀ f ∈ locals, SFunc.ReturnRegion E f) →
      κ.K.map Cont.f = locals ++ caller :: K →
      ∃ (N : Exec.Deriv) (next : Cursor),
        Exec.Deriv.ExecFreeUntil F N ∧ N.sevm = F.sevm ∧ N.exn = F.exn ∧
        CursorOK code c N next ∧ next.f = caller ∧ next.K.map Cont.f = K ∧
        RunPS Ninst.Run c.prog F.sevm κ.f locals F.devm N.devm := by
  apply Exec.Deriv.strongRec
  intro F ih κ locals caller K post placed success hsg body localRegions sameK
  have refs : κ.f.refs.all (· ∈ E) = true := by
    have h := body.1
    simp only [SFunc.execFreeIn, Bool.and_eq_true] at h
    exact h.2
  have headFree : ∀ x, ¬ Ninst.At F.sevm.code F.pc (.exec x) := by
    intro x instruction
    obtain ⟨tail, tree, _⟩ := placed.tree_of_exec instruction
    have h := body.1
    rw [tree] at h
    simp only [SFunc.execFreeIn, SFunc.execsSatisfy, Bool.false_and, Bool.false_eq_true] at h
  obtain ⟨N, edge⟩ := cursor_step_of_return_regionH checked placed success hsg closed body.2 refs
  obtain ⟨next, synthetic, stateful, nextPlaced⟩ := cursor_stepS_noStateGas checked placed edge hsg
  have step : ConfStep Ninst.Run c.prog F.sevm
      ⟨F.devm, κ.f, locals ++ caller :: K⟩ (next.conf N.devm) := by
    have step := stateful.mono (fun run => run.toRun)
    change ConfStep Ninst.Run c.prog F.sevm
      ⟨F.devm, κ.f, κ.K.map Cont.f⟩ (next.conf N.devm) at step
    rw [sameK] at step
    exact step
  have env : N.sevm = F.sevm := Cursor.parentStep_sevm edge
  have outcome : N.exn = F.exn := by cases edge <;> rfl
  rcases ConfStep.of_below step with ⟨truncated, inside, shape⟩ | boundary
  · have state : truncated.d = N.devm := (congrArg Conf.d shape).symm
    have tree : next.f = truncated.f := congrArg Conf.f shape
    have conts : next.K.map Cont.f = truncated.K ++ caller :: K := congrArg Conf.K shape
    obtain ⟨region, regions⟩ := ConfStep.returnRegion free closed inside body localRegions
    obtain ⟨last, lastCursor, span, sameEnv, sameOutcome, lastPlaced, lastTree, lastK, returned⟩ :=
      ih N edge.lt next truncated.K caller K post nextPlaced (outcome.trans success)
        (env ▸ hsg) (tree.symm ▸ region) regions conts
    have returned' : RunPS Ninst.Run c.prog F.sevm truncated.f truncated.K
        truncated.d last.devm := by
      rw [state, ← tree]
      simpa only [env] using returned
    exact ⟨last, lastCursor, (Exec.Deriv.ExecFreeUntil.ofStep edge headFree).trans span,
      sameEnv.trans env, sameOutcome.trans outcome, lastPlaced, lastTree, lastK,
      RunPS.back inside returned'⟩
  · obtain ⟨empty, ret, t, f, tail, same, pop, shape⟩ := boundary
    obtain ⟨rfl, rfl⟩ := List.cons.inj same
    subst locals
    refine ⟨N, next, Exec.Deriv.ExecFreeUntil.ofStep edge headFree, env, outcome,
      nextPlaced, congrArg Conf.f shape, congrArg Conf.K shape, ?_⟩
    change SFunc.RunP Ninst.Run c.prog F.sevm F.devm κ.f (.returned N.devm)
    rw [ret]
    exact .ret t pop

/-- A call-free internal return cut from `rules.stateGas = none` alone. -/
theorem CursorOK.quietReturnH {code : ByteArray} {c : Cert} {F : Exec.Deriv} {κ : Cursor}
    {E : List Nat} {post : Devm} {caller : SFunc} {K : List SFunc}
    (checked : Cert.check code c = true) (placed : CursorOK code c F κ)
    (success : F.exn = .ok post) (hsg : F.sevm.benvStat.rules.stateGas = none)
    (free : ExecFreeSet c.prog E = true) (closed : NoHaltSet c.prog E = true)
    (bodyFree : κ.f.execFreeIn E = true) (bodyNoHalt : κ.f.noHalt = true)
    (continuations : κ.K.map Cont.f = caller :: K) :
    ∃ (N : Exec.Deriv) (next : Cursor),
      Exec.Deriv.ExecFreeUntil F N ∧ N.sevm = F.sevm ∧ N.exn = F.exn ∧
      CursorOK code c N next ∧ next.f = caller ∧ next.K.map Cont.f = K ∧
      SFunc.Run c.prog F.sevm F.devm κ.f (.returned N.devm) :=
  cursor_quietReturn_scopedH checked free closed F κ [] caller K post placed success hsg
    ⟨bodyFree, bodyNoHalt⟩ (by intro f member; cases member) continuations

end Blanc.Lift
