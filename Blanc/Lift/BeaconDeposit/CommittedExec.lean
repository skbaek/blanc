import Blanc.Lift.BeaconDeposit.Refines
import Blanc.Lift.BeaconDeposit.Ladder
import Blanc.Lift.BeaconDeposit.CommittedReplay
import Blanc.ExecutionDirectCode
import Blanc.ExecutionNoninterference
import Blanc.Lift.StaticOnlyFrames
import Blanc.StaticStorage

namespace Blanc.Lift.BeaconDeposit

open Jaune Blanc.ExecutionTrace

private theorem cert_onlyStaticcall :
    ∀ f ∈ cert.prog, f.execsSatisfy Xinst.isStaticcall = true := by
  intro f member
  simp only [Cert.prog, cert, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

/-- The checked deployed certificate permits only STATICCALL at every actual
same-frame location, including internal jumps and returns. -/
theorem parentPrefix_exec_staticcall {root node : Exec.Deriv}
    (pc : root.pc = 0) (installed : root.sevm.code = code)
    (fork : CoveredFork root.sevm.benvStat.fork)
    (chain : Exec.Deriv.ParentPrefix root node)
    {x : Xinst} (instruction : Ninst.At node.sevm.code node.pc (.exec x)) :
    x = .staticcall :=
  parentPrefix_exec_staticcall_of_cert cert_check cert_onlyStaticcall pc installed fork chain
    instruction

private theorem event_suffix_not_static {sevm : Sevm} {pre : Devm} {out : Outcome}
    (static : sevm.isStatic = true)
    (run : SFunc.Run prog sevm pre t_071c_c4 out) : False := by
  unfold t_071c_c4 at run
  cases run with
  | dest burn run =>
    iterate 22 (cases run; rename_i _ step run)
    cases run with
    | next step run =>
      obtain ⟨pc, logRun⟩ := of_run_reg step
      exact Rinst.log_not_ok_of_static static logRun

/-- A successful deployed deposit cannot run in a static frame. This follows
from the mandatory event emission before the SHA and insertion segments. -/
theorem successful_deposit_not_static {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (hsel : Sevm.selector sevm = BeaconDeposit.depositSelector)
    (run : Exec 0 sevm pre (.ok post)) : sevm.isStatic = false := by
  cases hs : sevm.isStatic with
  | false => rfl
  | true =>
    obtain ⟨f, hf, lifted⟩ := lift_sound cert_check hcode hfork run
    have hf0 : prog[0]? = some t_0000_c0 := rfl
    rw [hf0] at hf
    cases hf
    rw [St.self hstack hmem] at lifted
    obtain ⟨k, G1, g, _, hk32, hg, lifted⟩ := safe_dispatch lifted
    have hk : k = 32 := hk32.mpr hsel
    subst k
    have hg32 : g = t_00a4_c32 := by
      have heq : prog[32]? = some t_00a4_c32 := rfl
      rw [heq] at hg
      exact (Option.some.inj hg).symm
    subst g
    obtain ⟨_, G2, d, body, _, _⟩ := safe_decoder hcd lifted
    obtain ⟨_, _, _, _, _, _, b1, M1, G3, _, memory, body⟩ :=
      safe_guards hcd hfork body
    obtain ⟨b2, M2, G4, _, _, body⟩ := safe_event memory body
    exact (event_suffix_not_static hs body).elim

/-- Static committed executions of the deployed deposit selector are impossible
even before imposing the storage invariant. -/
theorem frameAccepted_eq_nil_of_static {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (static : sevm.isStatic = true)
    (run : Exec 0 sevm pre (.ok post)) : frameAccepted sevm = [] := by
  unfold frameAccepted
  split
  next selected =>
    have impossible := successful_deposit_not_static hcode hfork hcd hstack hmem selected run
    rw [static] at impossible
    cases impossible
  next => rfl

/-- A selected committed frame contributes exactly its own accepted node.
The derived STATICCALL restriction makes every retained child static; the
lower-depth static-frame conclusion then removes its entire observation. -/
theorem target_committedFrameNodes {ca : Adr} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true)
    (hcode : sevm.code = code) (target : sevm.currentTarget = ca)
    (installed : beaconSem.At ca 0 sevm pre)
    (fork : CoveredFork sevm.benvStat.fork)
    (admitted : Exec.FrameAdmitted ca beaconFrameEntry run)
    (deeper : ∀ {pc : Nat} {s : Sevm} {d : Devm} {out : Execution}
      (child : Exec pc s d out) (_committed : Execution.commits out = true),
      CoveredFork s.benvStat.fork → s.depth < sevm.depth →
      beaconSem.At ca pc s d → Exec.FrameAdmitted ca beaconFrameEntry child →
      s.isStatic = true →
      (Exec.committedFrames child).flatMap (committedFrameNodes ca) = []) :
    (Exec.committedFrames run).flatMap (committedFrameNodes ca) =
      frameAccepted sevm := by
  have descendants := Exec.staticOnly_descendantFrames_flatMap_eq_nil ca beaconSem
    beaconFrameEntry (committedFrameNodes ca) ⟨0, sevm, pre, .ok post, run⟩ target installed.1 fork
    (fun chain instruction =>
      parentPrefix_exec_staticcall (root := ⟨0, sevm, pre, .ok post, run⟩) rfl hcode fork
        chain instruction)
    (fun child childCommitted childFork depth childAt childAdmitted static =>
      deeper child childCommitted childFork depth childAt childAdmitted static)
    run (.refl _) (by
      intro frameRoot member selected
      exact admitted frameRoot (List.mem_cons_of_mem _ member) selected)
  simp only [Exec.committedFrames, dite_eq_left committed, List.flatMap_cons,
    descendants, List.append_nil, committedFrameNodes, Exec.Frame.ofRun]
  simp only [ite_eq_left target]

end Blanc.Lift.BeaconDeposit
