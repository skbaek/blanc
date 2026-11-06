import Blanc.Lift.Usdc.SignedSkip
import Blanc.Lift.Usdc.EntryLawProxy
import Blanc.Lift.HistAccessWalkFacts
import Blanc.HistoricalFork

/-!
# The library call without state gas

`libStep_qdKeep`: one step of `_requireValidSignature`'s closure keeps the proxy's storage and the library's code, from
`rules.stateGas = none` and `HistFork`, the form the signed walks of `HistFork` frames need. Nothing about a signature is read.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift

/-- **The library is quiet**, without state gas. -/
theorem lib_quietH : QuietCodeOn HistFork Lib.code := fun run codeEq fork => by
  obtain ⟨f, hf0, hrun⟩ := lift_sound_noStateGas Lib.cert_check codeEq fork.stateGas_none run
  have hmem : (0 : Nat) ∈ List.range Lib.cert.length := by decide
  have hq := (List.all_eq_true.mp lib_quietSet) 0 hmem
  rw [hf0] at hq
  simp only [Bool.and_eq_true] at hq
  exact congrFun (SFunc.Run.world_of_quietH lib_quietSet fork.stateGas_none hq.1 hq.2 hrun).1 _

/-- One `DELEGATECALL` into the library keeps the frame's storage owner's storage. -/
theorem delegatecall_lib_keep {sevm : Sevm} {pre post : Devm} (hsg : sevm.benvStat.rules.stateGas = none)
    (hfork : HistFork sevm.benvStat.fork) {g w : B256} {s : List B256} (hstack : pre.stack = g :: w :: s)
    (hcode : pre.getCode w.toAdr = Lib.code)
    (run : Ninst.Run sevm pre (.exec .delegatecall) post) :
    Devm.getStor post sevm.currentTarget = Devm.getStor pre sevm.currentTarget := by
  obtain ⟨xl, filled, pc, stepRun⟩ := run
  have xrun : XStep.Run (Xinst.step sevm pre .delegatecall) xl (.ok post) := by
    simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] using stepRun
  cases hs : Xinst.step sevm pre .delegatecall with
  | done e =>
      rw [hs] at xrun
      obtain ⟨-, rfl⟩ := xrun
      exact Xinst.step_done_getStor_noStateGas hsg hs _
  | spawn f rsm =>
      rw [hs] at xrun
      obtain ⟨r, frameRun, resumed⟩ := xrun
      obtain ⟨htarget, -, -, -, -, hfcode⟩ :=
        step_delegatecall_spawn_shapeH hsg hs hstack (by rw [hcode]; exact lib_undelegated)
      obtain ⟨hcreate, hnoTransfer, hstat, -⟩ := Xinst.step_delegatecall_spawn_meta_noStateGas hsg hs
      rcases Xinst.step_shapeNoStateGas sevm pre .delegatecall hsg with
        ⟨_, shape, -⟩ | ⟨_, _, _, _, _, _, shape⟩ |
        ⟨d, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hprefix, -, -, -, shape⟩ <;>
        rw [shape] at hs
      · cases hs
      · obtain ⟨rfl, -⟩ := genericCreate_step_spawn_exact hs
        cases hcreate
      · obtain ⟨rfl, rfl⟩ := genericCall_step_spawn_exact hs
        dsimp only [Frame.ofCall] at htarget hfcode hnoTransfer hstat
        cases r with
        | error e => exact (Resume.call_run_error resumed.symm).elim
        | ok child =>
            have childState : post.state = child.state := Resume.call_state resumed.symm
            have keep := ProcessMessage.getStor_of_quietCode lib_quietH filled frameRun hnoTransfer
              (hfcode.trans hcode) (hstat ▸ hfork)
            show post.state.getStor sevm.currentTarget = pre.state.getStor sevm.currentTarget
            rw [childState, ← htarget]
            refine keep.trans ?_
            rw [htarget]
            exact (hprefix.getStor sevm.currentTarget).symm

/-- **One step of a quiet-delegate tree of the implementation**, without state gas. -/
theorem libStep_qdKeep {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none) (hfork : HistFork sevm.benvStat.fork)
    {d d' : Devm} {n : Ninst} (hn : (n.quiet || n == .exec .delegatecall) = true)
    (step : FramedStep implP sevm d n d') (hcode : d.getCode usdcLib.toB256.toAdr = Lib.code) :
    QDKeep usdcLib.toB256 sevm d d' := by
  have codeKeep : d'.getCode usdcLib.toB256.toAdr = d.getCode usdcLib.toB256.toAdr :=
    Ninst.Run.getCode_eq step.1 (by rw [hcode]; exact lib_nonempty)
  rcases Bool.or_eq_true_iff.mp hn with hq' | hd
  · exact ⟨congrFun (Ninst.world_of_quietH hsg hq' step.1).1 _, codeKeep⟩
  · have hd : n = .exec .delegatecall := by simpa only [beq_iff_eq] using hd
    subst hd
    obtain ⟨ρ, a, X, R, hst, hfr, hPa⟩ := step.2 _ rfl
    have hX := FrameMatches.getElem?_const hfr (implP_delegatecall a hPa)
    have h1 : d.stack[1]? = some usdcLib.toB256 := by
      obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp hX
      rw [hst, List.getElem?_append_left hi]
      exact hX
    obtain ⟨g, s, hs⟩ : ∃ g s, d.stack = g :: usdcLib.toB256 :: s := by
      match hds : d.stack, h1 with
      | g :: w :: s, h1 =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h1
        exact ⟨g, s, by rw [h1]⟩
    exact ⟨delegatecall_lib_keep hsg hfork hs hcode step.1, codeKeep⟩

end Blanc.Lift.Usdc
