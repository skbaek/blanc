import Blanc.Lift.Usdc.HistorySlotsFrames
import Blanc.Lift.Usdc.RefineAdminRescue
import Blanc.Lift.RegionStor
import Blanc.Lift.CursorSourceRunReturn
import Blanc.Lift.InvWalkDispatch
import Blanc.Lift.InvWalkProvenance
import Blanc.Lift.InvWalkWorld

/-!
# `rescueERC20` without its call keeps the proxy's storage (U6b2)

`rescueQuietEnd : RescueQuietEnd`.  A successful frame of the implementation that decodes no
external instruction enters no child frame, so every step of its certified run inside the frame
(`StepIn`, from the cursor at the frame's start, `CursorOK.sourceRunReturn`) is childless; a
childless external step keeps a protected account's storage.  Under the `rescueERC20` selector
the run passes the dispatcher (walked) into the wrapper, a tree of the store-free region
`rescuePre` (U6f's `rescuePre_ok`, `rescueSilent_ok`, `rescueWrapper_pre`), whose whole run keeps the
proxy's storage (`SFunc.RunP.stor_of_preIn`).
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc.Impl

/-- A frame that enters no child frame takes only childless external steps, which keep every
protected account's storage. -/
theorem stepIn_exec_stor {R : Exec.Deriv} (noDesc : Exec.rawFrameDescendants R.exc = [])
    {ca : Adr} {d : Devm} {x : Xinst} {d' : Devm} (h : StepIn R R.sevm d (.exec x) d')
    (hp : State.Protected d.state ca) : d'.state.getStor ca = d.state.getStor ca := by
  obtain ⟨xl, filled, pc, run⟩ := h
  simp only [Ninst.StepRun, Ninst.step_exec] at run
  have xrun := XStep.run_toStep.mp run
  cases xl with
  | none => exact Xinst.none_getStor_eq xrun ca hp
  | some p =>
      obtain ⟨evm, exn⟩ := p
      obtain ⟨e, he⟩ := filled
      have mem := he ⟨evm.pc, evm.sta, evm.dyna, exn, e⟩ (Exec.mem_rawFrameRoots_self e)
      rw [Exec.rawFrameRoots, noDesc, List.mem_singleton] at mem
      have sevmEq : evm.sta = R.sevm := congrArg Exec.Deriv.sevm mem
      cases spawnEq : Xinst.step R.sevm d x with
      | done ex => simp only [XStep.Run, spawnEq, ExceptT.stM_eq, reduceCtorEq, false_and] at xrun
      | spawn f rsm =>
          simp only [spawnEq, XStep.Run] at xrun
          obtain ⟨_, frameRun, -⟩ := xrun
          have lt := Xinst.step_spawn_depth spawnEq
          rw [← Frame.enter_run_depth (RunFrame.some_inv frameRun).1, sevmEq] at lt
          exact (Nat.lt_irrefl _ lt).elim

/-- **`rescueERC20` without its call keeps the proxy's storage.** -/
theorem rescueQuietEnd : RescueQuietEnd := by
  intro P sevm pre post run codeEq target fork _ hsel prot none
  let R : Exec.Deriv := ⟨0, sevm, pre, .ok post, run⟩
  have noDesc : Exec.rawFrameDescendants R.exc = [] :=
    Exec.rawFrameDescendants_eq_nil_of_noExec run none
  have hX : ∀ {d : Devm} {x : Xinst} {d' : Devm}, StepIn R sevm d (.exec x) d' →
      State.Protected d.state P → d'.state.getStor P = d.state.getStor P :=
    fun h hp => stepIn_exec_stor noDesc h hp
  have hw : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0xb2, 0x11, 0x8a, 0x8d] := by
    rw [show Bytes.toB256 [0x00] = 0 from by decide,
      show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
    exact hsel.trans (by decide)
  have placed := cursor_start cert_check (F := R) rfl codeEq
  rcases placed.sourceRunReturn cert_check rfl fork with halted | ⟨c, tail, -, -, hK, -⟩
  swap
  · cases hK
  have sound : ∀ {s d n d'}, StepIn R s d n d' → Ninst.Run s d n d' := StepIn.toRun
  change SFunc.RunP (StepIn R) cert.prog sevm pre t_0000_c0 (.halted post) at halted
  rw [St.self' pre] at halted
  have run := SFunc.runP_iff_runCutP_nil.mp halted
  clear halted placed
  unfold t_0000_c0 at run
  obtain ⟨_, s, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (sound s)
  obtain ⟨_, s, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (sound s)
  obtain ⟨_, s, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_mstore (sound s)
  obtain ⟨_, s, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_callvalue (sound s)
  obtain ⟨_, s, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (sound s)
  obtain ⟨_, s, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (sound s)
  obtain ⟨_, s, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (sound s)
  rcases ric_branchP run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_0010_c0 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, s, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (sound s)
  obtain ⟨_, s, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (sound s)
  obtain ⟨_, s, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_calldatasize (sound s)
  obtain ⟨_, s, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_lt (sound s)
  obtain ⟨_, s, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (sound s)
  rcases ric_branchP run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_001a_c0 at run
  obtain ⟨_, s, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (sound s)
  obtain ⟨_, s, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_calldataload (sound s)
  obtain ⟨_, s, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (sound s)
  obtain ⟨_, s, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_shr (sound s)
  rw [hw] at run
  obtain ⟨_, run⟩ := ric_cmp_gtP sound run
  rw [ite_eq_left (by decide)] at run
  unfold t_002b_c0 at run
  obtain ⟨_, run⟩ := ric_cmp_gtP sound run
  rw [ite_eq_right (by decide)] at run
  unfold t_0104_c0 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, run⟩ := ric_cmp_gtP sound run
  rw [ite_eq_left (by decide)] at run
  unfold t_0110_c0 at run
  obtain ⟨_, run⟩ := ric_cmp_gtP sound run
  rw [ite_eq_left (by decide)] at run
  unfold t_011b_c0 at run
  obtain ⟨_, run⟩ := ric_cmp_eqP sound (List.not_mem_nil) rfl run
  rw [ite_eq_left (by decide)] at run
  unfold t_0126_c0 at run
  obtain ⟨_, run⟩ := ric_cmp_eqP sound (List.not_mem_nil) rfl run
  rw [ite_eq_left (by decide)] at run
  unfold t_0131_c0 at run
  obtain ⟨_, run⟩ := ric_cmp_eqP sound (List.not_mem_nil) rfl run
  rw [ite_eq_left (by decide)] at run
  unfold t_013c_c0 at run
  obtain ⟨_, run⟩ := ric_cmp_eqP sound (g := t_0d6d_c142) (List.not_mem_nil) rfl run
  rw [ite_eq_right (by decide)] at run
  have keep := SFunc.RunP.stor_of_preIn sound rescuePre_ok rescueSilent_ok hX
    (SFunc.runP_iff_runCutP_nil.mpr run) rescueWrapper_pre prot
  exact keep

end Blanc.Lift.Usdc
