import Blanc.Lift.StaticOnlyFrames
import Blanc.Lift.RetainedTargetCompleteness
import Blanc.LockExclusion
import Blanc.StaticStorage

/-!
# Storage along the chain of a frame that writes nothing and only `STATICCALL`s

The node-level companions of `Blanc/Lift/StaticOnlyFrames.lean`, for a frame whose same-frame
instructions are never `SSTORE` and whose spawning instructions are all `STATICCALL`:

* `Exec.Deriv.ParentStep.getStor_of_quiet`: one same-frame edge out of a node that decodes neither
  `SSTORE` nor an external instruction other than `STATICCALL` keeps every storage map (a regular
  instruction other than `SSTORE` keeps it, a jump keeps the instruction frame, and a `STATICCALL`
  keeps every map whatever its callee does);
* `Exec.Deriv.ParentPrefix.getStor_of_quiet`: hence every node of the chain carries the root's
  storage maps;
* `Exec.descendantFrames_isStatic_of_staticOnly`: every retained descendant of such a frame is
  static (the child of a `STATICCALL` is static, and below a static frame every frame is).

Nothing here mentions a contract.
-/

namespace Blanc

open Jaune

/-- The only byte that decodes as `SSTORE` is `0x55`. -/
theorem UInt8.toRinst_sstore {b : UInt8} (h : b.toRinst = some .sstore) : b = 0x55 := by
  have all : ∀ f : Fin 256,
      (match (UInt8.ofBitVec (BitVec.ofFin f)).toRinst with
        | some .sstore => decide (UInt8.ofBitVec (BitVec.ofFin f) = 0x55)
        | _ => true) = true := by
    decide +kernel
  have hb := all b.toBitVec.toFin
  rw [show UInt8.ofBitVec (BitVec.ofFin b.toBitVec.toFin) = b from rfl, h] at hb
  exact of_decide_eq_true hb

/-- A position that decodes `SSTORE` holds the byte `0x55`, so code without that byte decodes
`SSTORE` nowhere. -/
theorem ByteArray.sstore_mem_of_getInst {cd : ByteArray} {pc : Nat}
    (h : cd.getInst pc = some (.next (.reg .sstore))) : (0x55 : UInt8) ∈ cd.data.toList := by
  unfold ByteArray.getInst at h
  by_cases hpc : pc < cd.size
  · simp only [hpc, ↓reduceDIte] at h
    split at h
    · split at h
      · cases h
      · cases h
      · cases h
      · cases hr : UInt8.toRinst cd[pc] <;> simp only [Functor.mapRev, hr, Option.map_eq_map,
          Option.map_none, reduceCtorEq, Option.map_some, Function.comp_apply, Option.some.injEq,
          Inst.next.injEq, Ninst.reg.injEq] at h
        subst h
        rw [← UInt8.toRinst_sstore hr]
        exact Array.getElem_mem_toList hpc
    · cases hx : UInt8.toXinst cd[pc] <;> simp only [Functor.mapRev, hx, Option.map_eq_map,
        Option.map_none, reduceCtorEq, Option.map_some, Function.comp_apply, Option.some.injEq,
        Inst.next.injEq] at h
    · cases hj : UInt8.toJinst cd[pc] <;> simp only [Functor.mapRev, hj, Option.map_eq_map,
        Option.map_none, reduceCtorEq, Option.map_some, Option.some.injEq] at h
    · cases hl : UInt8.toLinst cd[pc] <;> simp only [Functor.mapRev, hl, Option.map_eq_map,
        Option.map_none, reduceCtorEq, Option.map_some, Option.some.injEq] at h
    · cases h
  · simp only [hpc, ↓reduceDIte, Option.some.injEq, reduceCtorEq] at h

/-- **One quiet same-frame edge keeps every storage map.** -/
theorem Exec.Deriv.ParentStep.getStor_of_quiet {next node : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep next node) (fork : CoveredFork node.sevm.benvStat.fork)
    (noStore : ¬ Ninst.At node.sevm.code node.pc (.reg .sstore))
    (onlyStatic : ∀ x, Ninst.At node.sevm.code node.pc (.exec x) → x = .staticcall) :
    Devm.getStor next.devm = Devm.getStor node.devm := by
  rcases decoded : node.sevm.code.getInst node.pc with _ | instruction
  · exact (Lift.Cursor.parentStep_false_of_none edge decoded).elim
  · cases instruction with
    | last l => exact (Lift.Cursor.parentStep_false_of_linst edge decoded).elim
    | jump j =>
        have run : Jinst.run ⟨node.pc, node.sevm, node.devm⟩ j = .ok ⟨next.pc, next.devm⟩ :=
          Lift.Cursor.parentStep_jinst edge decoded
        have frame := Jinst.run_instructionFrame ⟨node.pc, node.sevm, node.devm⟩ j
        rw [run] at frame
        funext owner
        exact (frame.getStor owner).symm
    | next i =>
        obtain ⟨-, run⟩ := Lift.Cursor.parentStep_ninst edge decoded
        obtain ⟨xl, filled, pc, stepRun⟩ := run
        cases i with
        | exec x =>
            have hx : x = .staticcall := onlyStatic x decoded
            subst hx
            exact (Ninst.staticcall_getStor_eq fork ⟨xl, filled, pc, stepRun⟩).symm
        | reg r =>
            have store : r ≠ .sstore := fun h => noStore (by rw [← h]; exact decoded)
            simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at stepRun
            exact (Rinst.preserves_stor store stepRun.2.symm).symm
        | push bytes bound =>
            have hxl := stepRun
            simp only [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at hxl
            obtain ⟨rfl, -⟩ := hxl
            funext owner
            exact ((Ninst.push_instructionFrame_effectRec (hxs := bound) (xl := .none) trivial
              stepRun).getStor owner).symm
        | dupn imm =>
            have hxl := stepRun
            simp only [Ninst.StepRun, Ninst.step_dupn, Step.run_ofExecution] at hxl
            obtain ⟨rfl, -⟩ := hxl
            funext owner
            exact ((Ninst.dupn_instructionFrame_effectRec (xl := .none) trivial
              stepRun).getStor owner).symm
        | swapn imm =>
            have hxl := stepRun
            simp only [Ninst.StepRun, Ninst.step_swapn, Step.run_ofExecution] at hxl
            obtain ⟨rfl, -⟩ := hxl
            funext owner
            exact ((Ninst.swapn_instructionFrame_effectRec (xl := .none) trivial
              stepRun).getStor owner).symm
        | exchange imm =>
            have hxl := stepRun
            simp only [Ninst.StepRun, Ninst.step_exchange, Step.run_ofExecution] at hxl
            obtain ⟨rfl, -⟩ := hxl
            funext owner
            exact ((Ninst.exchange_instructionFrame_effectRec (xl := .none) trivial
              stepRun).getStor owner).symm

/-- **A quiet chain keeps every storage map**: if no node of a frame's same-frame chain decodes
`SSTORE` and every external instruction it decodes is `STATICCALL`, every node of the chain carries
the root's storage maps. -/
theorem Exec.Deriv.ParentPrefix.getStor_of_quiet {root tail : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix root tail)
    (fork : CoveredFork root.sevm.benvStat.fork)
    (noStore : ∀ pc, ¬ Ninst.At root.sevm.code pc (.reg .sstore))
    (onlyStatic : ∀ {node : Exec.Deriv} {x : Xinst}, Exec.Deriv.ParentPrefix root node →
      Ninst.At node.sevm.code node.pc (.exec x) → x = .staticcall) :
    Devm.getStor tail.devm = Devm.getStor root.devm := by
  induction chain with
  | refl => rfl
  | @step root next tail head rest ih =>
      have sevmEq : next.sevm = root.sevm := Lift.Cursor.parentStep_sevm head
      have edge := Exec.Deriv.ParentStep.getStor_of_quiet head fork (noStore root.pc)
        (fun x hx => onlyStatic (.refl _) hx)
      refine (ih (by rw [sevmEq]; exact fork) (by rw [sevmEq]; exact noStore)
        (fun chain' hx => onlyStatic (.step head chain') hx)).trans edge

/-- **Only-`STATICCALL` frames have only static descendants.** -/
theorem Exec.descendantFrames_isStatic_of_staticOnly (root : Exec.Deriv)
    (onlyStatic : ∀ {node : Exec.Deriv} {x : Xinst}, Exec.Deriv.ParentPrefix root node →
      Ninst.At node.sevm.code node.pc (.exec x) → x = .staticcall) :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      Exec.Deriv.ParentPrefix root ⟨pc, sevm, pre, out, run⟩ →
      ∀ D ∈ Exec.descendantFrames run, D.sevm.isStatic = true := by
  intro pc sevm pre out run
  induction run with
  | halt _ => intro _ D member; simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | cont step next ih =>
      intro chain
      simpa only [Exec.descendantFrames] using ih (chain.snoc (.cont step next))
  | doneErr _ _ _ =>
      intro _ D member; simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | doneOk step enter resume next ih =>
      intro chain
      simpa only [Exec.descendantFrames] using ih (chain.snoc (.doneOk step enter resume next))
  | runErr _ _ _ _ =>
      intro _ D member; simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | runOk step enter child resume next _ nextIh =>
      intro chain D member
      obtain ⟨x, instruction, spawn, _⟩ := Evm.step_spawn_inv step
      have hx : x = .staticcall := onlyStatic chain instruction
      subst hx
      have childStatic :=
        (Frame.enter_run_isStatic enter).trans (Xinst.step_staticcall_spawn_isStatic spawn)
      simp only [Exec.descendantFrames, List.mem_append] at member
      rcases member with here | later
      · split at here
        · rw [List.mem_cons] at here
          rcases here with rfl | deeper
          · exact childStatic
          · exact Exec.descendantFrames_isStatic child childStatic D deeper
        · simp only [List.not_mem_nil] at here
      · exact nextIh (chain.snoc (.runOk step enter child resume next)) D later

end Blanc
