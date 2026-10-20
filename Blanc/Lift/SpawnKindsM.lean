import Blanc.ExecutionEntryAccounting
import Blanc.ExecutionReachable

/-!
# Spawn kinds from the bytes: `SpawnKinds` without a cursor

`SpawnKinds ca sem` (`Blanc/ExecutionEntryAccounting.lean`) asks that every external
instruction decoded along a successful target frame's own same-frame chain is `CALL` or
`STATICCALL`.  For a `Cert.check` certificate it is discharged through the certificate cursor
(`cursor_of_parentPrefix`, `CursorOK.exec_call_or_staticcall`, `Blanc/Lift/Cursor.lean`); a
`Cert.checkM` (memory-map) certificate has no cursor.

This module discharges it from the code bytes alone, for any certificate format:

* `Exec.Deriv.ParentPrefix.noPush`: every node of a frame's same-frame chain entered at a
  position no `PUSH` immediate covers sits at such a position (`Evm.step_cont_noPush` for a
  continued step; a spawn edge moves past its one-byte `X`-class opcode);
* `callKindsCheck code`: a linear walk over the instruction starts (stepping over `PUSH`
  immediates, as `spawnFreeCheck` does) refusing every `X`-class byte but `CALL` and
  `STATICCALL`, read off `code.data.toList` so a kernel decision over a large runtime is
  linear;
* `callKinds_of_check`: the walk is sound at every position no `PUSH` immediate covers
  (`PushReach.of_noPushBefore`);
* `spawnKinds_of_callKindsCheck`: hence `SpawnKinds ca sem` for any code semantics whose runs
  execute checked bytes.

The walk treats the immediate of `DUPN`/`SWAPN`/`EXCHANGE` as an instruction start (it
over-approximates the reached positions), so it can only refuse more, never less.
-/

namespace Blanc.Lift

open Jaune

/-! ### Reached positions along a same-frame chain -/

/-- One same-frame edge keeps the boundary invariant: the next node again sits at a position no
`PUSH` immediate covers. -/
theorem Exec.Deriv.ParentStep.noPush {n' n : Exec.Deriv} (edge : Exec.Deriv.ParentStep n' n)
    (hb : noPushBefore n.sevm.code n.pc 32 = true) :
    noPushBefore n'.sevm.code n'.pc 32 = true := by
  cases edge with
  | cont hstep _ => exact Evm.step_cont_noPush hstep hb
  | doneOk hstep _ _ _ =>
    obtain ⟨x, hx, -, rfl⟩ := Evm.step_spawn_inv hstep
    obtain ⟨hlt, hty⟩ := getInst_exec_inv hx
    exact noPushBefore_succ_of_ne_p hlt hb (by rw [hty]; exact nofun)
  | runOk hstep _ _ _ _ =>
    obtain ⟨x, hx, -, rfl⟩ := Evm.step_spawn_inv hstep
    obtain ⟨hlt, hty⟩ := getInst_exec_inv hx
    exact noPushBefore_succ_of_ne_p hlt hb (by rw [hty]; exact nofun)

/-- **Every node of a same-frame chain sits at a reached position.**  A frame entered at a
position no `PUSH` immediate covers (pc `0`, in particular) keeps every node of its own chain at
such a position. -/
theorem Exec.Deriv.ParentPrefix.noPush {F n : Exec.Deriv} (hp : Exec.Deriv.ParentPrefix F n)
    (hb : noPushBefore F.sevm.code F.pc 32 = true) :
    noPushBefore n.sevm.code n.pc 32 = true := by
  induction hp with
  | refl => exact hb
  | step head _ ih => exact ih (Exec.Deriv.ParentStep.noPush head hb)

/-! ### The decidable walk -/

/-- A byte admitted at an instruction start: it decodes no external instruction, or decodes
`CALL` or `STATICCALL`. -/
def callKindByte (b : UInt8) : Bool :=
  b.toXinst.all fun x => x == .call || x == .staticcall

/-- The linear instruction walk over a byte list, `skip` immediate bytes still to pass. -/
def callKindsWalk : List UInt8 → Nat → Bool
  | [], _ => true
  | b :: bs, 0 => callKindByte b && callKindsWalk bs (pushWidth b)
  | _ :: bs, skip + 1 => callKindsWalk bs skip

/-- The decidable check: every instruction start of the linear walk from `0` holds a byte
admitted by `callKindByte`.  It reads `code.data.toList` (a projection), so a kernel decision is
linear in the code size. -/
def callKindsCheck (code : ByteArray) : Bool := callKindsWalk code.data.toList 0

theorem callKindsWalk_drop : ∀ (skip : Nat) (xs : List UInt8),
    callKindsWalk xs skip = true → callKindsWalk (xs.drop skip) 0 = true
  | 0, _, h => h
  | _ + 1, [], _ => rfl
  | skip + 1, _ :: xs, h => callKindsWalk_drop skip xs h

/-- A decoded external instruction sits on its own `X`-class byte. -/
theorem getInst_exec_toXinst {cd : ByteArray} {pc : Nat} {x : Xinst}
    (h : Xinst.At cd pc x) : ∃ hpc : pc < cd.size, cd[pc].toXinst = some x := by
  obtain ⟨hpc, hty⟩ := getInst_exec_inv h
  refine ⟨hpc, ?_⟩
  unfold Xinst.At ByteArray.getInst at h
  simp only [hpc, ↓reduceDIte] at h
  split at h
  · rename_i hty'
    rw [hty] at hty'
    cases hty'
  · cases hx : UInt8.toXinst cd[pc] <;>
      simp only [Functor.mapRev, hx, Option.map_eq_map, Option.map_none, reduceCtorEq,
        Option.map_some, Function.comp_apply, Option.some.injEq, Inst.next.injEq,
        Ninst.exec.injEq] at h
    rw [h]
  all_goals
    rename_i hty'
    rw [hty] at hty'
    cases hty'

/-- **The walk is sound at every reached position.**  At a position no `PUSH` immediate covers,
checked bytes decode no external instruction but `CALL` and `STATICCALL`. -/
theorem callKinds_of_check {cd : ByteArray} (h : callKindsCheck cd = true) {pc : Nat}
    {x : Xinst} (hb : noPushBefore cd pc 32 = true) (hx : Xinst.At cd pc x) :
    x = .call ∨ x = .staticcall := by
  obtain ⟨hpc, hbyte⟩ := getInst_exec_toXinst hx
  have hreach := PushReach.of_noPushBefore cd pc hpc hb
  have hlen : cd.data.toList.length = cd.size := Array.length_toList
  have hget : ∀ j (hj : j < cd.size), cd.data.toList[j]'(hlen ▸ hj) = cd[j] := fun _ _ => rfl
  have key : ∀ j, PushReach cd j → callKindsWalk (cd.data.toList.drop j) 0 = true := by
    intro j hj
    induction hj with
    | zero => exact h
    | @step p hp _ ih =>
      rw [List.drop_eq_getElem_cons (hlen ▸ hp), hget p hp] at ih
      simp only [callKindsWalk, Bool.and_eq_true] at ih
      have hd := callKindsWalk_drop _ _ ih.2
      rwa [List.drop_drop] at hd
  have hk := key pc hreach
  rw [List.drop_eq_getElem_cons (hlen ▸ hpc), hget pc hpc] at hk
  simp only [callKindsWalk, Bool.and_eq_true] at hk
  have hc := hk.1
  simp only [callKindByte, hbyte, Option.all_some, Bool.or_eq_true, beq_iff_eq] at hc
  exact hc

/-- The walk steps over `PUSH` data (`0xF4` inside a `PUSH1`) and admits `CALL`. -/
example : callKindsCheck ⟨#[0x60, 0xf4, 0xf1, 0x00]⟩ = true := by decide +kernel

/-- The walk refuses a `DELEGATECALL` at an instruction start. -/
example : callKindsCheck ⟨#[0x60, 0x00, 0xf4]⟩ = false := by decide +kernel

/-! ### `SpawnKinds` -/

/-- **Spawn kinds from checked bytes.**  If every run of `sem` executes `code` and `code` passes
`callKindsCheck`, every external instruction decoded along a successful target frame's own chain
is `CALL` or `STATICCALL`.  No certificate is involved: the same statement serves `Cert.check`
and `Cert.checkM` certificates alike. -/
theorem spawnKinds_of_callKindsCheck {ca : Adr} {sem : CodeSem} {code : ByteArray}
    (hcode : ∀ {sevm pre post}, sem.Run sevm pre post → sevm.code = code)
    (h : callKindsCheck code = true) : SpawnKinds ca sem := by
  intro sevm pre post run hrun _ _ _ node chain x hat
  have hb : noPushBefore node.sevm.code node.pc 32 = true :=
    Exec.Deriv.ParentPrefix.noPush chain (noPushBefore_zero _ _)
  have hsevm : node.sevm = sevm := by
    clear hb hat
    suffices ∀ {F n : Exec.Deriv}, Exec.Deriv.ParentPrefix F n → n.sevm = F.sevm from this chain
    intro F n hp
    induction hp with
    | refl => rfl
    | step head _ ih => exact ih.trans (by cases head <;> rfl)
  rw [hsevm, hcode hrun] at hb hat
  exact callKinds_of_check h hb hat

end Blanc.Lift
