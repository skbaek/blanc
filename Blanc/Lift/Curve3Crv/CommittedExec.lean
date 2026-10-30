import Blanc.Lift.Curve3Crv.CommittedReplay
import Blanc.Lift.StaticOnlyFramesIn

/-!
# Curve's only spawned frame is a static owner query

The deployed 3Crv runtime executes no external instruction other than the single
`STATICCALL` of `set_name` (`owner()` on the minter). The certificate check below
turns that into a restriction at every actual same-frame location, and the generic
`Exec.staticOnly_descendantFrames_flatMap_eq_nil` removes every observed descendant.
The minter may be the contract itself: that child is a static, strictly deeper
target frame, and its observation is empty by the ladder's own inductive
hypothesis, exactly as for any foreign callee.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune Blanc.Lift Blanc.ExecutionTrace

/-- The checked deployed certificate executes no external instruction but `STATICCALL`. -/
private theorem cert_onlyStaticcall :
    ∀ f ∈ cert.prog, f.execsSatisfy Xinst.isStaticcall = true := by
  intro f member
  simp only [Cert.prog, cert, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

/-- A selected committed frame contributes exactly its own invocation, if any, over a fork domain
`F` (the frame itself without state gas). Every retained child is a static `owner()` query; the
lower-depth static-frame hypothesis removes its whole observation. -/
theorem target_committedFrameInvocationsIn {F : Fork → Prop} {ca : Adr}
    {entry : Sevm → Devm → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true)
    (hcode : sevm.code = code) (target : sevm.currentTarget = ca)
    (installed : c3crvSem.At ca 0 sevm pre)
    (fork : F sevm.benvStat.fork) (hsg : sevm.benvStat.rules.stateGas = none)
    (admitted : Exec.FrameAdmitted ca entry run)
    (deeper : ∀ {pc : Nat} {s : Sevm} {d : Devm} {out : Execution}
      (child : Exec pc s d out) (_committed : Execution.commits out = true),
      F s.benvStat.fork → s.depth < sevm.depth →
      c3crvSem.At ca pc s d → Exec.FrameAdmitted ca entry child →
      s.isStatic = true →
      (Exec.committedFrames child).flatMap (committedFrameInvocations ca) = []) :
    (Exec.committedFrames run).flatMap (committedFrameInvocations ca) =
      committedFrameInvocations ca (Exec.Frame.ofRun run committed) := by
  have descendants := Exec.staticOnly_descendantFrames_flatMap_eq_nilIn (F := F) ca c3crvSem entry
    (committedFrameInvocations ca) ⟨0, sevm, pre, .ok post, run⟩ target installed.1 fork
    (fun chain instruction =>
      parentPrefix_exec_staticcall_of_cert_noStateGas cert_check cert_onlyStaticcall
        (root := ⟨0, sevm, pre, .ok post, run⟩) rfl hcode hsg chain instruction)
    (fun child childCommitted childFork depth childAt childAdmitted static =>
      deeper child childCommitted childFork depth childAt childAdmitted static)
    run (.refl _) (by
      intro frameRoot member selected
      exact admitted frameRoot (List.mem_cons_of_mem _ member) selected)
  simp only [Exec.committedFrames, dite_eq_left committed, List.flatMap_cons,
    descendants, List.append_nil]

/-- `target_committedFrameInvocationsIn` on the covered domain. -/
theorem target_committedFrameInvocations {ca : Adr} {entry : Sevm → Devm → Prop}
    {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true)
    (hcode : sevm.code = code) (target : sevm.currentTarget = ca)
    (installed : c3crvSem.At ca 0 sevm pre)
    (fork : CoveredFork sevm.benvStat.fork)
    (admitted : Exec.FrameAdmitted ca entry run)
    (deeper : ∀ {pc : Nat} {s : Sevm} {d : Devm} {out : Execution}
      (child : Exec pc s d out) (_committed : Execution.commits out = true),
      CoveredFork s.benvStat.fork → s.depth < sevm.depth →
      c3crvSem.At ca pc s d → Exec.FrameAdmitted ca entry child →
      s.isStatic = true →
      (Exec.committedFrames child).flatMap (committedFrameInvocations ca) = []) :
    (Exec.committedFrames run).flatMap (committedFrameInvocations ca) =
      committedFrameInvocations ca (Exec.Frame.ofRun run committed) :=
  target_committedFrameInvocationsIn run committed hcode target installed fork
    fork.rules_stateGas_none admitted deeper

end Blanc.Lift.Curve3Crv
