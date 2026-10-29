import Blanc.Lift.BeaconDeposit.HistLadder
import Blanc.Lift.BeaconDeposit.CommittedExec
import Blanc.Lift.StaticOnlyFramesIn

/-! Exact observations of a historical Beacon frame and its retained descendants. -/

namespace Blanc.Lift.BeaconDeposit

open Jaune Blanc.ExecutionTrace

/-- A closed syntactic certificate fact, independent of any execution fork. -/
private theorem cert_staticcall_check :
    cert.prog.all (fun f => f.execsSatisfy Xinst.isStaticcall) = true := by
  decide +kernel

/-- Every actual same-frame spawn of the historical runtime is STATICCALL. -/
theorem parentPrefix_exec_staticcallH {root node : Exec.Deriv}
    (pc : root.pc = 0) (installed : root.sevm.code = code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    {x : Xinst} (instruction : Ninst.At node.sevm.code node.pc (.exec x)) :
    x = .staticcall :=
  parentPrefix_exec_staticcall_of_cert_noStateGas cert_check
    (List.all_eq_true.mp cert_staticcall_check) pc installed hsg chain instruction

/-- A committed target frame contributes exactly its own accepted node over HistFork.
Every retained child is static and its observation vanishes by the lower-depth hypothesis. -/
theorem target_committedFrameNodesH_of_entry {entry : Sevm → Devm → Prop} {ca : Adr} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true)
    (hcode : sevm.code = code) (target : sevm.currentTarget = ca)
    (installed : beaconSem.At ca 0 sevm pre)
    (fork : HistFork sevm.benvStat.fork)
    (admitted : Exec.FrameAdmitted ca entry run)
    (deeper : ∀ {pc : Nat} {s : Sevm} {d : Devm} {out : Execution}
      (child : Exec pc s d out) (_committed : Execution.commits out = true),
      HistFork s.benvStat.fork → s.depth < sevm.depth →
      beaconSem.At ca pc s d → Exec.FrameAdmitted ca entry child →
      s.isStatic = true →
      (Exec.committedFrames child).flatMap (committedFrameNodes ca) = []) :
    (Exec.committedFrames run).flatMap (committedFrameNodes ca) =
      frameAccepted sevm := by
  have descendants := Exec.staticOnly_descendantFrames_flatMap_eq_nilIn
    (F := HistFork) ca beaconSem entry (committedFrameNodes ca)
    ⟨0, sevm, pre, .ok post, run⟩ target installed.1 fork
    (fun chain instruction => parentPrefix_exec_staticcallH
      (root := ⟨0, sevm, pre, .ok post, run⟩) rfl hcode fork.stateGas_none chain instruction)
    (fun child childCommitted childFork depth childAt childAdmitted static =>
      deeper child childCommitted childFork depth childAt childAdmitted static)
    run (.refl _) (by
      intro frameRoot member selected
      exact admitted frameRoot (List.mem_cons_of_mem _ member) selected)
  simp only [Exec.committedFrames, dite_eq_left committed, List.flatMap_cons,
    descendants, List.append_nil, committedFrameNodes, Exec.Frame.ofRun]
  simp only [ite_eq_left target]

/-- Compatibility form for the original fresh Beacon entry. -/
theorem target_committedFrameNodesH {ca : Adr} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true)
    (hcode : sevm.code = code) (target : sevm.currentTarget = ca)
    (installed : beaconSem.At ca 0 sevm pre)
    (fork : HistFork sevm.benvStat.fork)
    (admitted : Exec.FrameAdmitted ca beaconFrameEntry run)
    (deeper : ∀ {pc : Nat} {s : Sevm} {d : Devm} {out : Execution}
      (child : Exec pc s d out) (_committed : Execution.commits out = true),
      HistFork s.benvStat.fork → s.depth < sevm.depth →
      beaconSem.At ca pc s d → Exec.FrameAdmitted ca beaconFrameEntry child →
      s.isStatic = true →
      (Exec.committedFrames child).flatMap (committedFrameNodes ca) = []) :
    (Exec.committedFrames run).flatMap (committedFrameNodes ca) =
      frameAccepted sevm :=
  target_committedFrameNodesH_of_entry run committed hcode target installed fork admitted deeper

end Blanc.Lift.BeaconDeposit

