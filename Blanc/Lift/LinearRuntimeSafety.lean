import Blanc.ExecutionNoDelProducer
import Blanc.Lift.SpawnKindsM

/-!
# The runtime-safety bundle from a linear byte walk

`InstalledRuntimeSafety` is produced from a `Cert.check` certificate by `of_cert`. A runtime lifted
only under `Cert.checkM` has no such certificate; a linear walk over its bytes gives the same facts,
because every node of a frame entered at pc `0` sits at a position no `PUSH` immediate covers
(`Exec.Deriv.ParentPrefix.noPush`).

* `selfdestructFreeCheck` — the walk: no instruction start holds `SELFDESTRUCT`;
* `not_selfdestruct_of_check` — soundness at a reached position;
* `InstalledRuntimeSafety.of_linearCheck` — the bundle from this walk and `callKindsCheck`.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- The linear instruction walk refusing `SELFDESTRUCT` at an instruction start. -/
def selfdestructFreeWalk : List UInt8 → Nat → Bool
  | [], _ => true
  | b :: bs, 0 => b != 0xff && selfdestructFreeWalk bs (pushWidth b)
  | _ :: bs, skip + 1 => selfdestructFreeWalk bs skip

/-- No instruction start of `code` holds `SELFDESTRUCT`. -/
def selfdestructFreeCheck (code : ByteArray) : Bool := selfdestructFreeWalk code.data.toList 0

theorem selfdestructFreeWalk_drop : ∀ (skip : Nat) (xs : List UInt8),
    selfdestructFreeWalk xs skip = true → selfdestructFreeWalk (xs.drop skip) 0 = true
  | 0, _, h => h
  | _ + 1, [], _ => rfl
  | skip + 1, _ :: xs, h => selfdestructFreeWalk_drop skip xs h

/-- Only the byte `0xFF` decodes as `SELFDESTRUCT`. -/
theorem byte_of_selfdestruct_at {cd : ByteArray} {pc : Nat} (h : Linst.At cd pc .selfdestruct) :
    ∃ hpc : pc < cd.size, cd[pc] = 0xff := by
  have byte : ∀ b : UInt8, b.toLinst = some .selfdestruct → b = 0xff := by
    intro b h
    unfold UInt8.toLinst at h
    split at h <;> first | rfl | cases h
  unfold Linst.At ByteArray.getInst at h
  by_cases hpc : pc < cd.size
  · refine ⟨hpc, ?_⟩
    simp only [hpc, ↓reduceDIte] at h
    split at h
    · exfalso
      split at h
      · cases h
      · cases h
      · cases h
      · cases hx : UInt8.toRinst cd[pc] <;>
          simp only [Functor.mapRev, hx, Option.map_eq_map, Option.map_none, reduceCtorEq,
            Option.map_some, Function.comp_apply, Option.some.injEq] at h
        all_goals cases h
    · exfalso
      cases hx : UInt8.toXinst cd[pc] <;>
        simp only [Functor.mapRev, hx, Option.map_eq_map, Option.map_none, reduceCtorEq,
          Option.map_some, Function.comp_apply, Option.some.injEq] at h
      all_goals cases h
    · exfalso
      cases hx : UInt8.toJinst cd[pc] <;>
        simp only [Functor.mapRev, hx, Option.map_eq_map, Option.map_none, reduceCtorEq,
          Option.map_some, Option.some.injEq] at h
      all_goals cases h
    · apply byte
      cases hx : UInt8.toLinst cd[pc] <;>
        simp only [Functor.mapRev, hx, Option.map_eq_map, Option.map_none, reduceCtorEq,
          Option.map_some, Option.some.injEq, Inst.last.injEq] at h
      rw [h]
    · exfalso
      cases h
  · simp only [hpc, ↓reduceDIte] at h
    cases h

theorem not_selfdestruct_of_check {cd : ByteArray} (h : selfdestructFreeCheck cd = true) {pc : Nat}
    (hb : noPushBefore cd pc 32 = true) : ¬ Linst.At cd pc .selfdestruct := by
  intro hx
  obtain ⟨hpc, hbyte⟩ := byte_of_selfdestruct_at hx
  have hreach := PushReach.of_noPushBefore cd pc hpc hb
  have hlen : cd.data.toList.length = cd.size := Array.length_toList
  have hget : ∀ j (hj : j < cd.size), cd.data.toList[j]'(hlen ▸ hj) = cd[j] := fun _ _ => rfl
  have key : ∀ j, PushReach cd j → selfdestructFreeWalk (cd.data.toList.drop j) 0 = true := by
    intro j hj
    induction hj with
    | zero => exact h
    | @step p hp _ ih =>
      rw [List.drop_eq_getElem_cons (hlen ▸ hp), hget p hp] at ih
      simp only [selfdestructFreeWalk, Bool.and_eq_true] at ih
      have hd := selfdestructFreeWalk_drop _ _ ih.2
      rwa [List.drop_drop] at hd
  have hk := key pc hreach
  rw [List.drop_eq_getElem_cons (hlen ▸ hpc), hget pc hpc, hbyte] at hk
  simp only [selfdestructFreeWalk, Bool.and_eq_true] at hk
  exact absurd hk.1 (by decide)

/-- `SELFDESTRUCT` refused at an instruction start, stepped over in `PUSH` data. -/
example : selfdestructFreeCheck ⟨#[0x60, 0xff, 0x00]⟩ = true := by decide +kernel
example : selfdestructFreeCheck ⟨#[0x60, 0x00, 0xff]⟩ = false := by decide +kernel

end Blanc.Lift

namespace Blanc

open Jaune Blanc.Lift

/-- **The runtime-safety bundle from two linear walks of the bytes**, for a runtime with no
`Cert.check` certificate. -/
theorem InstalledRuntimeSafety.of_linearCheck {C : ByteArray}
    (kinds : callKindsCheck C = true) (terminal : selfdestructFreeCheck C = true)
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ []) : InstalledRuntimeSafety C where
  notDelegation := hCdel
  nonempty := hCne
  safe := fun run hsg installed root =>
    Exec.safe_of_spawnsTerminal
      (fun {R N x} hpc hcode _ chain hat => by
        have hb : noPushBefore N.sevm.code N.pc 32 = true :=
          Exec.Deriv.ParentPrefix.noPush chain (by rw [hpc]; exact noPushBefore_zero _ _)
        rw [Exec.Deriv.ParentPrefix.sevm_eq chain, hcode] at hb hat
        rcases callKinds_of_check kinds hb hat with h | h
        · exact .inl h
        · exact .inr (.inl h))
      (fun {R N} hpc hcode _ chain => by
        have hb : noPushBefore N.sevm.code N.pc 32 = true :=
          Exec.Deriv.ParentPrefix.noPush chain (by rw [hpc]; exact noPushBefore_zero _ _)
        rw [Exec.Deriv.ParentPrefix.sevm_eq chain, hcode] at hb ⊢
        exact not_selfdestruct_of_check terminal hb)
      hCdel run hsg installed hCne root

end Blanc
