import Blanc.Lift.Usdc.RefineDispatchCheck
import Blanc.Lift.Usdc.RefineShape
import Blanc.Lift.Usdc.Families
import Blanc.Lift.Cursor
import Blanc.Lift.ExactLeaf

/-!
# USDC refinement, dispatch family (U6g)

Certificate-driven walks over the implementation certificate (`Impl.cert`): the entry preamble
(nonpayable check, short-calldata check, selector extraction), then the dispatcher's comparison tree
evaluated at the selector (`SFunc.selWalk`, `Blanc/Lift/SelectorRoute.lean`), then the facts the
kernel decided about the wrapper entered (`RefineDispatchCheck.lean`).
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.Lift.Token

/-! ## The entry preamble -/

theorem shr_selector (sevm : Sevm) :
    Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Blanc.Sevm.selector sevm := rfl

/-- **The preamble of a cut run.**  The frame has no value, at least four calldata bytes, and the
dispatcher's comparison tree runs with the selector on top of the stack and the base unchanged. -/
theorem impl_preamble_cut {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg}
    (run : SFunc.RunCut implProg sevm [] (St b S M G) Impl.t_0000_c0 r) :
    sevm.value = 0 ∧ B256.ltCheck sevm.data.length.toB256 4 = 0 ∧
      ∃ M' G', SFunc.RunCut implProg sevm [] (St b (Blanc.Sevm.selector sevm :: S) M' G')
        dispTree r := by
  unfold Impl.t_0000_c0 at run
  obtain ⟨d, hd, h⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_mstore hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_callvalue hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_iszero hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branch h with ⟨-, _, h⟩ | ⟨nz, _, h⟩
  · exact (h.false_of_noOk (by decide)).elim
  have value : sevm.value = 0 := eq_of_eqCheck_ne nz
  unfold Impl.t_0010_c0 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_calldatasize hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_lt hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branch h with ⟨long, _, h⟩ | ⟨-, _, h⟩
  · rw [tree_001a] at h
    obtain ⟨d, hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_calldataload hd
    obtain ⟨d, hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_shr hd
    rw [shr_selector] at h
    exact ⟨value, long, _, _, h⟩
  · exact (h.false_of_noOk (by decide)).elim

/-- A reverting arm reaches no external instruction. -/
theorem reach_revert_false {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {d : Devm}
    {f : SFunc} {T : Conf} (hf : f.execFreeIn [] = true) (run : Reach P implProg sevm ⟨d, f, []⟩ T)
    (hT : AtExec T) : False :=
  Reach.false_of_execFree (E := []) rfl run hT hf (fun _ h => absurd h List.not_mem_nil)

/-- **The preamble of a reach** from the frame's start to an external instruction. -/
theorem impl_preamble_reach {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {sevm : Sevm} {b : Devm} {T : Conf}
    (run : Reach P implProg sevm ⟨b, Impl.t_0000_c0, []⟩ T) (hT : AtExec T) :
    ∃ M' G', Reach P implProg sevm ⟨St b (Blanc.Sevm.selector sevm :: b.stack) M' G', dispTree, []⟩ T := by
  rw [St.self (d := b) rfl rfl] at run
  unfold Impl.t_0000_c0 at run
  obtain ⟨d, hd, h⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_push (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_mstore (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_callvalue (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_iszero (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_push (hP hd)
  rcases rr_branch h hT with ⟨-, _, h⟩ | ⟨-, _, h⟩
  · exact (reach_revert_false (by decide) h hT).elim
  unfold Impl.t_0010_c0 at h
  obtain ⟨_, h⟩ := rr_dest h hT
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_pop (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_push (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_calldatasize (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_lt (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_push (hP hd)
  rcases rr_branch h hT with ⟨-, _, h⟩ | ⟨-, _, h⟩
  · rw [tree_001a] at h
    obtain ⟨d, hd, h⟩ := rr_next h hT
    obtain ⟨_, rfl⟩ := ri_push (hP hd)
    obtain ⟨d, hd, h⟩ := rr_next h hT
    obtain ⟨_, rfl⟩ := ri_calldataload (hP hd)
    obtain ⟨d, hd, h⟩ := rr_next h hT
    obtain ⟨_, rfl⟩ := ri_push (hP hd)
    obtain ⟨d, hd, h⟩ := rr_next h hT
    obtain ⟨_, rfl⟩ := ri_shr (hP hd)
    rw [shr_selector] at h
    exact ⟨_, _, h⟩
  · exact (reach_revert_false (by decide) h hT).elim

/-! ## What a decoded message's selector is -/

theorem decodeCall_some {e : Sevm} {c : Call} (h : decodeCall e = some c) :
    ∃ r ∈ rows, r.sel = Blanc.Sevm.selector e ∧ r.read e = c ∧
      4 + 32 * r.headWords ≤ e.data.length := by
  unfold decodeCall at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i r hr
      split at h
      · rename_i len
        cases h
        have hp := List.find?_some hr
        exact ⟨r, List.mem_of_find?_eq_some hr, of_decide_eq_true hp, rfl, len⟩
      · cases h

/-- The selectors of the calls of this unit. -/
theorem decodeCall_sel {e : Sevm} {c : Call} (h : decodeCall e = some c) :
    (c = .view → Blanc.Sevm.selector e ∈ viewSels) ∧
      (c = .«initialize» → Blanc.Sevm.selector e = 0x3357162b) ∧
      (c = .initializeV2 → Blanc.Sevm.selector e = 0xd608ea64) ∧
      (∀ a, c = .initializeV2_1 a → Blanc.Sevm.selector e = 0x2fc81e09) ∧
      (c = .initializeV2_2 → Blanc.Sevm.selector e = 0x430239b4) := by
  obtain ⟨r, hr, hsel, rfl, -⟩ := decodeCall_some h
  rw [← hsel]
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun a h => ?_, fun h => ?_⟩ <;>
      first | decide | cases h

/-! ## The views -/

/-- A successful implementation frame starts at entry `0` of the certificate, in the cut form. -/
theorem impl_run_cut {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (code : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork) :
    SFunc.RunCut implProg sevm [] (St pre pre.stack pre.memory pre.gasLeft) Impl.t_0000_c0
      (.done (.halted post)) := by
  obtain ⟨f, hf, frun⟩ := lift_sound Impl.cert_check code fork run
  rw [show Impl.cert.prog = implProg from rfl, prog_zero] at hf
  cases hf
  rw [← St.self rfl rfl]
  exact SFunc.Run.cut frun

/-- **A view writes nothing.**  A successful implementation frame whose message decodes to a view
leaves the persistent state as it found it. -/
theorem impl_view_state {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (code : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork)
    (dec : decodeCall sevm = some .view) : post.state = pre.state := by
  obtain ⟨-, -, M, G, drun⟩ := impl_preamble_cut (impl_run_cut run code fork)
  have routes := List.all_eq_true.mp view_routes _ ((decodeCall_sel dec).1 rfl)
  split at routes
  · rename_i p hw
    rcases p with ⟨c, j⟩
    obtain ⟨-, g, G', hg, grun⟩ := SFunc.RunCut.selWalk_inl hw drun
    have hj : j ∈ viewEntries := of_decide_eq_true routes
    have closed := List.all_eq_true.mp view_silent j hj
    rw [hg] at closed
    simp only [Bool.and_eq_true] at closed
    exact SFunc.Run.state_of_silent view_silent closed.1 closed.2 grun.uncut
  · cases routes

/-- **A view calls nothing.**  No node of a successful implementation frame whose message decodes
to a view decodes an external instruction. -/
theorem impl_view_noExec {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (code : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork)
    (dec : decodeCall sevm = some .view) :
    ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x) := by
  intro N hN x hx
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix Impl.cert_check
    (R := ⟨0, sevm, pre, .ok post, run⟩) rfl code fork hN
  obtain ⟨g, hf, -⟩ := ok.tree_of_exec hx
  have hT : AtExec (κ.conf N.devm) := ⟨x, g, hf⟩
  change Reach (StepIn ⟨0, sevm, pre, .ok post, run⟩) implProg sevm ⟨pre, Impl.t_0000_c0, []⟩
    (κ.conf N.devm) at reach
  obtain ⟨M, G, dreach⟩ := impl_preamble_reach StepIn.toRun reach hT
  have routes := List.all_eq_true.mp view_routes _ ((decodeCall_sel dec).1 rfl)
  split at routes
  · rename_i p hw
    rcases p with ⟨c, j⟩
    obtain ⟨-, g, G', hg, greach⟩ := Reach.selWalk_inl StepIn.toRun hw dreach hT
    have hj : j ∈ viewEntries := of_decide_eq_true routes
    exact Reach.false_of_execFree view_execFree greach hT (ExecFreeSet.lookup view_execFree hj hg)
      (fun _ h => absurd h List.not_mem_nil)
  · cases routes

open Classical in
/-- **The whole-frame law of the views** (U6g): a successful implementation frame whose message
decodes to a view commits the book's identity step, keeps the proxy's storage, and spawns nothing. -/
theorem impl_view_law : ImplStepLaw (· = Call.view) := by
  intro P U sevm pre post run code _ _ fork _ _ _ _ _ admin c dec hc
  subst hc
  have stor : post.state.getStor P = pre.state.getStor P := by
    rw [impl_view_state run code fork dec]
  refine ⟨?_, by rw [stor], by rw [stor],
    fun N hN x hx => (impl_view_noExec run code fork dec N hN x hx).elim⟩
  rw [stor]
  change (if sevm.caller = (ledger U (pre.state.getStor P)).admin then
      (if adminGetter sevm then some (ledger U (pre.state.getStor P)) else none)
    else match decodeCall sevm with
      | none => none
      | some c => (ledger U (pre.state.getStor P)).step P sevm.caller c) = _
  have admin' : sevm.caller ≠ (ledger U (pre.state.getStor P)).admin := admin
  rw [ite_eq_right_of_eq_false _ _ (eq_false admin'), dec]
  rfl

end Blanc.Lift.Usdc
