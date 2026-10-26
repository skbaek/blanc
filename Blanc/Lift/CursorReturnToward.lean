import Blanc.Lift.CursorOccurrenceToward
import Blanc.Lift.ReachWalkSstore
import Blanc.Lift.CursorTreeNinst
import Blanc.Lift.RunPWalk

/-!
# Actual internal return before a later SSTORE

A helper with no SSTORE returns through its original caller continuation
before an actual later same-frame SSTORE. External calls inside the helper
are allowed; no successful final frame outcome is required.
-/

namespace Blanc.Lift

open Jaune

/-- A straight halting region cannot reach SSTORE, even with an arbitrary
saved caller stack below it. The source either stays inside or would have
to return through that caller, which the halting check excludes. -/
theorem Reach.false_of_sstoreFree_halting
    {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
    {d : Devm} {f : SFunc} {K : List SFunc} {target : Conf}
    (run : Reach P fs sevm ⟨d, f, K⟩ target) (store : AtSstore target)
    (free : f.sstoreFreeIn [] = true) (halts : f.haltsOnly = true) : False := by
  cases K with
  | nil =>
      exact Reach.false_of_sstoreFree (E := []) rfl run store free
        (fun _ member => (List.not_mem_nil member).elim)
  | cons caller K =>
      rcases Reach.split (S := []) run rfl with ⟨inside, route, shape⟩ | ⟨D, returned, _⟩
      · have atStore : AtSstore inside := by
          rw [shape] at store
          exact store
        exact Reach.false_of_sstoreFree (E := []) rfl route atStore free
          (fun _ member => (List.not_mem_nil member).elim)
      · exact returned.not_returned_of_haltsOnly halts

private theorem cursor_return_toward_scoped
    {code : ByteArray} {c : Cert} {E : List Nat}
    (checked : Cert.check code c = true) (closed : SstoreFreeSet c.prog E = true)
    {sevm : Sevm} {initial : Conf}
    (free : initial.f.sstoreFreeIn E = true)
    (freeLocals : ∀ f ∈ initial.K, f.sstoreFreeIn E = true)
    {F target : Exec.Deriv} (path : Exec.Deriv.ParentPrefix F target)
    (store : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
    ∀ (κ : Cursor) (locals : List SFunc) (caller : SFunc) (K : List SFunc),
      CursorOK code c F κ → F.sevm.benvStat.rules.stateGas = none → F.sevm = sevm →
      κ.K.map Cont.f = locals ++ caller :: K →
      Reach Ninst.Run c.prog sevm initial ⟨F.devm, κ.f, locals⟩ →
      (∀ D, RunPS Ninst.Run c.prog sevm κ.f locals F.devm D →
        RunPS Ninst.Run c.prog sevm initial.f initial.K initial.d D) →
      ∃ (N : Exec.Deriv) (next : Cursor),
        Exec.Deriv.ParentPrefix F N ∧ Exec.Deriv.ParentPrefix N target ∧
        CursorOK code c N next ∧ next.f = caller ∧ next.K.map Cont.f = K ∧
        RunPS Ninst.Run c.prog sevm initial.f initial.K initial.d N.devm := by
  induction path with
  | refl F =>
      intro κ locals caller K placed hsg env conts accumulated back
      obtain ⟨tail, tree, _⟩ := placed.tree_of_sstore store
      exact (Reach.false_of_sstoreFree closed accumulated ⟨tail, tree⟩ free freeLocals).elim
  | @step F middle target edge rest ih =>
      intro κ locals caller K placed hsg env conts accumulated back
      obtain ⟨next, _, stateful, nextPlaced⟩ :=
        cursor_stepS_noStateGas checked placed edge hsg
      have step : ConfStep Ninst.Run c.prog sevm
          ⟨F.devm, κ.f, locals ++ caller :: K⟩ (next.conf middle.devm) := by
        have actual := stateful.mono (fun run => run.toRun)
        rw [env] at actual
        change ConfStep Ninst.Run c.prog sevm
          ⟨F.devm, κ.f, κ.K.map Cont.f⟩ (next.conf middle.devm) at actual
        rw [conts] at actual
        exact actual
      have nextEnv : middle.sevm = sevm := (Cursor.parentStep_sevm edge).trans env
      have nextSg : middle.sevm.benvStat.rules.stateGas = none := by
        rw [Cursor.parentStep_sevm edge]
        exact hsg
      rcases ConfStep.of_below step with ⟨truncated, inside, shape⟩ | boundary
      · have state : truncated.d = middle.devm := (congrArg Conf.d shape).symm
        have tree : next.f = truncated.f := congrArg Conf.f shape
        have nextConts : next.K.map Cont.f = truncated.K ++ caller :: K :=
          congrArg Conf.K shape
        have nextAccumulated : Reach Ninst.Run c.prog sevm initial
            ⟨middle.devm, next.f, truncated.K⟩ := by
          rw [tree, ← state]
          exact accumulated.tail inside
        have nextBack : ∀ D, RunPS Ninst.Run c.prog sevm next.f truncated.K middle.devm D →
            RunPS Ninst.Run c.prog sevm initial.f initial.K initial.d D := by
          intro D run
          apply back D
          apply RunPS.back inside
          rw [state, ← tree]
          exact run
        obtain ⟨N, final, span, later, finalPlaced, finalTree, finalK, source⟩ :=
          ih store next truncated.K caller K nextPlaced nextSg nextEnv
            nextConts nextAccumulated nextBack
        exact ⟨N, final, .step edge span, later, finalPlaced, finalTree, finalK, source⟩
      · obtain ⟨empty, ret, t, f, tail, same, pop, shape⟩ := boundary
        obtain ⟨rfl, rfl⟩ := List.cons.inj same
        subst locals
        refine ⟨middle, next, .step edge (.refl _), rest, nextPlaced,
          congrArg Conf.f shape, congrArg Conf.K shape, ?_⟩
        apply back middle.devm
        change SFunc.Run c.prog sevm F.devm κ.f (.returned middle.devm)
        rw [ret]
        exact .ret t pop

/-- An SSTORE-free helper returns to its checked original continuation before
a later same-frame SSTORE. Its STATICCALLs and other external instructions
are retained in the completed source run; no final frame success is assumed. -/
theorem CursorOK.returnBeforeSstore_noStateGas
    {code : ByteArray} {c : Cert} {E : List Nat}
    (checked : Cert.check code c = true) (closed : SstoreFreeSet c.prog E = true)
    {F target : Exec.Deriv} {κ : Cursor} (placed : CursorOK code c F κ)
    (path : Exec.Deriv.ParentPrefix F target)
    (store : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (hsg : F.sevm.benvStat.rules.stateGas = none)
    (free : κ.f.sstoreFreeIn E = true)
    {caller : SFunc} {K : List SFunc} (continuations : κ.K.map Cont.f = caller :: K) :
    ∃ (N : Exec.Deriv) (next : Cursor),
      Exec.Deriv.ParentPrefix F N ∧ Exec.Deriv.ParentPrefix N target ∧
      CursorOK code c N next ∧ next.f = caller ∧ next.K.map Cont.f = K ∧
      SFunc.Run c.prog F.sevm F.devm κ.f (.returned N.devm) := by
  exact cursor_return_toward_scoped checked closed free
    (fun _ member => (List.not_mem_nil member).elim) path store κ [] caller K
    placed hsg rfl continuations .refl (fun _ run => run)

end Blanc.Lift
