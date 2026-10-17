import Blanc.Lift.Usdc.Impl.Check
import Blanc.Lift.Usdc.Constants
import Blanc.Lift.Usdc.CertRefine
import Blanc.Lift.Usdc.CursorFrames

/-!
# The implementation certificate with the library address as a frame constant

The generated implementation certificate (`Impl.cert`, U3) carries the linked library's address
`usdcLib` as a constant (`AVal.const`) from the two `PUSH20` sites (bytes 18390 and 20105) to the
`DELEGATECALL` nodes of `_permit` and `_requireValidSignature` only along their straight paths;
the ABI-encoding loop heads between them (entries 80, 9 at `0x4848`/`0x488d` and 117, 11 at
`0x4f0b`/`0x4f50`) declare that position unknown.  `certL` declares it `usdcLib` at those four
entries, and `rescueERC20`'s value word `0` at the copy-loop head of `functionCallWithValue`
(entry 121, `0x5388`); every tree is unchanged.  `certL_check` checks `certL` from scratch: the
nine entries that are refined or reference a refined entry are re-decided, every other entry
reuses U3's decision (`Cert.check_of_agree`).  Along every cursor of `certL`, each `DELEGATECALL`
node's address operand is the constant `usdcLib`, and each `CALL` node's value operand is `0`
(`certL_framesSat`).
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc.Lift

/-- The library address as an abstract frame word. -/
def libWord : AVal := .const usdcLib.toB256

/-- `Impl.cert` with the library address declared at the four loop-head entries and the
`rescueERC20` value word at the `functionCallWithValue` copy loop. -/
def certL : Cert :=
  ((((Impl.cert.refine 80 13 libWord).refine 9 8 libWord).refine 117 13 libWord).refine
    11 8 libWord).refine 121 8 (.const 0)

/-- The refined entries. -/
def refinedEntries : List Nat := [80, 9, 117, 11, 121]

/-- The entries re-decided: the refined ones and those referencing one. -/
def recheckedEntries : List Nat := [8, 9, 11, 80, 94, 111, 117, 118, 121]

theorem certL_getElem?_ne {i : Nat} (h : i ∉ refinedEntries) : certL[i]? = Impl.cert[i]? := by
  simp only [refinedEntries, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨h80, h9, h117, h11, h121⟩ := h
  unfold certL
  rw [Cert.refine_getElem?_ne h121, Cert.refine_getElem?_ne h11, Cert.refine_getElem?_ne h117,
    Cert.refine_getElem?_ne h9, Cert.refine_getElem?_ne h80]

theorem certL_entries_ne {i : Nat} (h : i ∉ refinedEntries) :
    certL.entries[i]? = Impl.cert.entries[i]? := by
  simp only [Cert.entries, List.getElem?_map, certL_getElem?_ne h]

theorem certL_prog : certL.prog = Impl.cert.prog := by
  unfold certL
  simp only [Cert.refine_prog]

theorem impl_refs_avoid : (List.range Impl.cert.length).all (fun i =>
    decide (i ∈ recheckedEntries) || match Impl.cert[i]? with
      | some p => p.2.refs.all fun k => decide (k ∉ refinedEntries)
      | none => true) = true := by
  decide +kernel

theorem certL_entry_8 : Cert.entryOk Impl.code certL.entries certL 8 = true := by
  rw [← Cert.entryOkT_eq Impl.codeTries]
  decide +kernel

theorem certL_entry_9 : Cert.entryOk Impl.code certL.entries certL 9 = true := by
  rw [← Cert.entryOkT_eq Impl.codeTries]
  decide +kernel

theorem certL_entry_11 : Cert.entryOk Impl.code certL.entries certL 11 = true := by
  rw [← Cert.entryOkT_eq Impl.codeTries]
  decide +kernel

theorem certL_entry_80 : Cert.entryOk Impl.code certL.entries certL 80 = true := by
  rw [← Cert.entryOkT_eq Impl.codeTries]
  decide +kernel

theorem certL_entry_94 : Cert.entryOk Impl.code certL.entries certL 94 = true := by
  rw [← Cert.entryOkT_eq Impl.codeTries]
  decide +kernel

theorem certL_entry_111 : Cert.entryOk Impl.code certL.entries certL 111 = true := by
  rw [← Cert.entryOkT_eq Impl.codeTries]
  decide +kernel

theorem certL_entry_117 : Cert.entryOk Impl.code certL.entries certL 117 = true := by
  rw [← Cert.entryOkT_eq Impl.codeTries]
  decide +kernel

theorem certL_entry_118 : Cert.entryOk Impl.code certL.entries certL 118 = true := by
  rw [← Cert.entryOkT_eq Impl.codeTries]
  decide +kernel

theorem certL_entry_121 : Cert.entryOk Impl.code certL.entries certL 121 = true := by
  rw [← Cert.entryOkT_eq Impl.codeTries]
  decide +kernel

/-- **The refined certificate checks.** -/
theorem certL_check : Cert.check Impl.code certL = true := by
  refine Cert.check_of_agree Impl.cert_check ?_ recheckedEntries ?_ ?_ ?_
  · rw [List.head?_eq_getElem?, List.head?_eq_getElem?,
      certL_getElem?_ne (by decide)]
  · intro i hi
    simp only [recheckedEntries, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact certL_entry_8
    · exact certL_entry_9
    · exact certL_entry_11
    · exact certL_entry_80
    · exact certL_entry_94
    · exact certL_entry_111
    · exact certL_entry_117
    · exact certL_entry_118
    · exact certL_entry_121
  · intro i hi
    exact certL_getElem?_ne fun h => hi (by
      simp only [refinedEntries, recheckedEntries, List.mem_cons, List.not_mem_nil,
        or_false] at h ⊢
      omega)
  · intro i hi p hp k hk
    have hlt : i < Impl.cert.length := (List.getElem?_eq_some_iff.mp hp).1
    have := List.all_eq_true.mp impl_refs_avoid i (List.mem_range.mpr hlt)
    simp only [hi, decide_false, Bool.false_or, hp, List.all_eq_true, decide_eq_true_eq] at this
    exact certL_entries_ne (this k hk)

/-- What the implementation's external-call nodes carry: a `DELEGATECALL`'s address operand is
the library, a `CALL`'s value operand is `0`. -/
def implP : Ninst → List AVal → Bool
  | .exec .delegatecall, a => a[1]? == some libWord
  | .exec .call, a => a[2]? == some (.const 0) && decide (7 ≤ a.length)
  | _, _ => true

theorem certL_framesSat : certL.framesSat implP = true := by
  decide +kernel

theorem certL_framesSat_head : ∀ p ∈ certL.head?, p.2.framesSat certL.entries implP [] = true := by
  decide +kernel

end Blanc.Lift.Usdc
