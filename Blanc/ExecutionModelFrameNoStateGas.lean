import Blanc.ExecutionModelAccounting
import Blanc.ExecutionAccountingPositional
import Blanc.ExecutionEntryAccounting

/-!
# The model replay without state gas

`Exec.CoreAccounting.modelFrame` with `stateGas = none` in place of `CoveredFork`, its only use of the
fork. Hoist debt: `modelFrame` is this theorem's instance at `fork.rules_stateGas_none`.
-/

namespace Blanc

open Jaune
open ExecutionAccountingReplay

namespace Exec.CoreAccounting

variable {ca : Adr} {C : ReplayCarrier ca} {V : ReplayObservation C}

/-- **The model replay of a successful frame from its own steps and its children's replays.**  If
`own` takes the boundary `a` to the post boundary when the frame's chain decodes no external
instruction, and otherwise to the boundary of every node that decodes one, after which only silent
steps follow and no external instruction, then `own`, the settled child's replay and the silent steps
take `a` to the post boundary, observing `own` and then the frame's committed descendants. -/
theorem modelFrameNoStateGas
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (hsg : sevm.benvStat.rules.stateGas = none)
    (rootNonempty : (pre.getCode ca).toList ≠ []) (bound : sum pre.state.bal < 2 ^ 256)
    (children : ChildReplays C V run) {a : C.Snap} (own : List C.Step)
    (c3 : (∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
        ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)) →
      C.Replay a own (C.ofState post.state))
    (c12 : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) →
        C.Replay a own (C.ofState N.devm.state) ∧
        ∀ N', Exec.Deriv.ParentStep N' N →
          C.Replay (C.ofState N'.devm.state) [] (C.ofState post.state) ∧
          ∀ M, Exec.Deriv.ParentPrefix N' M →
            ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y)) :
    ∃ steps, C.Replay a steps (C.ofState post.state) ∧
      V.obs steps = V.obs own ++ (Exec.descendantFrames run).flatMap V.frameObs := by
  rcases Exec.Deriv.exists_firstExec_or_none run with none | ⟨Vn, hV⟩
  · rw [Exec.descendantFrames_eq_nil_of_noExec run none]
    exact ⟨own, c3 none, by rw [List.flatMap_nil, List.append_nil]⟩
  · have hpV := hV.parentPrefix
    have dEq := hV.descendantFrames_eq
    obtain ⟨x, hx⟩ := hV.exec_at
    have hexn := Exec.Deriv.ParentPrefix.exn_eq hpV
    obtain ⟨vpc, vsevm, vd, vout, vrun⟩ := Vn
    dsimp only at hexn hx dEq
    subst hexn
    have nodeNonempty : (vd.getCode ca).toList ≠ [] := by
      rw [Blanc.Exec.Deriv.ParentPrefix.codePreserve hpV ca rootNonempty]
      exact rootNonempty
    cases vrun with
    | halt step =>
        rw [Evm.step_next hx] at step
        exact (Ninst.step_ne_halt_ok step).elim
    | cont step next =>
        rename_i pc' post'
        have nstep : Ninst.step ⟨vpc, vsevm, vd⟩ (.exec x) = .cont pc' post' := by
          rw [← Evm.step_next hx]
          exact step
        have nrun : Ninst.StepRun vpc vsevm vd (.exec x) .none (.ok post') := by
          unfold Ninst.StepRun
          rw [nstep]
          exact ⟨rfl, rfl⟩
        have hstor : Devm.getStor post' ca = Devm.getStor vd ca :=
          Ninst.none_getStor_eq_of_ne_sstore nrun (by intro h; cases h) ca
            (State.Protected.of_code_ne_nil nodeNonempty)
        obtain ⟨hc1, hc2⟩ := c12 _ hpV x hx
        obtain ⟨hrep2, hnoexec⟩ := hc2 _ (Exec.Deriv.ParentStep.cont step next)
        have hdf : Exec.descendantFrames next = [] :=
          Exec.descendantFrames_eq_nil_of_noExec next fun M hM y => hnoexec M hM y
        have hE : C.ofState vd.state = C.ofState post'.state :=
          ofStateGet fun k => by
            exact (congrArg (fun t => Stor.get t k) hstor).symm
        rw [dEq]
        simp only [Exec.descendantFrames, hdf, List.flatMap_nil, List.append_nil]
        refine ⟨own ++ [], append (hE ▸ hc1) hrep2, ?_⟩
        rw [V.obs_append, V.obs_nil, List.append_nil]
    | doneOk step enter resume next =>
        rename_i settled pc' post'
        have hstor : Devm.getStor post' ca = Devm.getStor vd ca :=
          Evm.step_doneOk_getStor_eq step enter resume ca
            (State.Protected.of_code_ne_nil nodeNonempty)
        obtain ⟨hc1, hc2⟩ := c12 _ hpV x hx
        obtain ⟨hrep2, hnoexec⟩ := hc2 _ (Exec.Deriv.ParentStep.doneOk step enter resume next)
        have hdf : Exec.descendantFrames next = [] :=
          Exec.descendantFrames_eq_nil_of_noExec next fun M hM y => hnoexec M hM y
        have hE : C.ofState vd.state = C.ofState post'.state :=
          ofStateGet fun k => by
            exact (congrArg (fun t => Stor.get t k) hstor).symm
        rw [dEq]
        simp only [Exec.descendantFrames, hdf, List.flatMap_nil, List.append_nil]
        refine ⟨own ++ [], append (hE ▸ hc1) hrep2, ?_⟩
        rw [V.obs_append, V.obs_nil, List.append_nil]
    | runOk step enter child resume next =>
        rename_i frame rsm pc' cevm raw inter
        have nodeFork : vsevm.benvStat.rules.stateGas = none := by
          rw [show vsevm = sevm from Blanc.Exec.Deriv.ParentPrefix.sevm_eq hpV]
          exact hsg
        have nodeCodeNe : vd.getCode ca ≠ .empty := fun empty =>
          nodeNonempty (by rw [empty]; simp only [ByteArray.toList_empty])
        obtain ⟨hc1, hc2⟩ := c12 _ hpV x hx
        obtain ⟨hrep2, hnoexec⟩ := hc2 _ (Exec.Deriv.ParentStep.runOk step enter child resume next)
        have hdf : Exec.descendantFrames next = [] :=
          Exec.descendantFrames_eq_nil_of_noExec next fun M hM y => hnoexec M hM y
        obtain ⟨seamA, seamB⟩ := Exec.spawn_seam_noStateGas nodeFork step enter child resume
        have hentry : Devm.getStor cevm.dyna ca = Devm.getStor vd ca :=
          Evm.step_spawn_enter_getStor_protected_noStateGas nodeFork step enter ca
            (State.Protected.of_code_ne_nil nodeNonempty)
        rw [dEq, Exec.descendantFrames_flatMap_runOk, hdf, List.flatMap_nil, List.append_nil]
        by_cases settles : Frame.settlementCommits frame raw = true
        · have hcommit := Frame.raw_commits_of_settlementCommits settles
          have bound' : sum cevm.dyna.state.bal < 2 ^ 256 := by
            obtain ⟨-, childBal⟩ := Evm.step_spawn_child_world_noStateGas nodeFork step enter nodeCodeNe
            exact Nat.lt_of_le_of_lt
              (childBal.trans (Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode hpV).1) bound
          obtain ⟨csteps, creplay, cobs⟩ := children step enter child resume next hpV hcommit bound'
          have e1 : C.frameEntry cevm.sta cevm.dyna.state = C.ofState vd.state := by
            rw [entryOfState]
            exact ofStateGet fun k => by
              exact congrArg (fun t => Stor.get t k) hentry
          have e2 : C.ofState (Execution.committedPost raw hcommit).state =
              C.ofState inter.state := ofStateGet fun k => (seamA hcommit settles ca k).symm
          rw [e1, e2] at creplay
          refine ⟨own ++ csteps ++ [], append (append hc1 creplay) hrep2, ?_⟩
          rw [V.obs_append, V.obs_append, cobs, V.obs_nil]
          simp only [settles, ↓reduceIte, List.append_nil]
        · have e3 : C.ofState vd.state = C.ofState inter.state :=
            ofStateGet fun k => (seamB settles ca k).symm
          refine ⟨own ++ [], append (e3 ▸ hc1) hrep2, ?_⟩
          rw [V.obs_append, V.obs_nil]
          have hf : Frame.settlementCommits frame raw = false := by simpa only [Bool.not_eq_true] using
            settles
          simp only [hf, Bool.false_eq_true, ↓reduceIte, List.append_nil]

end Exec.CoreAccounting

end Blanc
