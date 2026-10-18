import Blanc.Lift.Usdc.FiniteFootprint
import Blanc.Lift.Usdc.HistFCore

/-!
# USDC's support-free checkpoint checker (F3)

`checkUsdcF P rows w` is the support-free twin of `checkUsdc`
(`FiniteFootprint.lean`): it decides `UsdcInstalled P w ∧ FootCoreL (rowKeys rows) (w.getStor P)`.
The installed half (the three runtimes byte for byte, the implementation slot, the proxy apart
from the implementation and the library) and the ledger's goodness on the fixed words
(`initialized`, version 3) are unchanged.  The footprint walk `checkRows` is replaced by its
row-local checks only — every row's word is its key's slot, the words strictly ascend, none is a
fixed slot — which give `Inj` and `Apart` on `rowKeys rows` through `FiniteCheckpoint`'s
`ascending_nodup`, `rows_words_eq` and `List.inj_on_of_nodup_map`, without `covered`.  There is
no support claim: a stray nonzero word at an unlisted slot is accepted here and rejected there.

Cost: linear in the rows (one keccak per row for its slot word) and linear in the three code
lengths (2,186 + 23,464 + 1,741 bytes); no walk over the storage entries.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift.FiniteCheckpoint

/-- **USDC's support-free checkpoint checker** on fetched rows: the three code identities, the
implementation slot, the row-local footprint checks (word, ascent, off the fixed slots), and the
ledger's goodness on the fixed words (version 3, initialized). -/
def checkUsdcF (P : Adr) (rows : List (Key × B256)) (w : State) : Bool :=
  decide ((w.getCode P).data.toList = Proxy.code.data.toList) &&
    decide ((w.getCode usdcImpl).data.toList = Impl.code.data.toList) &&
    decide ((w.getCode usdcLib).data.toList = Lib.code.data.toList) &&
    decide ((w.getStor P).get implSlot = usdcImpl.toB256) &&
    decide (P ≠ usdcImpl) && decide (P ≠ usdcLib) &&
    rows.all (fun r => decide (Key.slot r.1 = r.2)) &&
    ascending (rows.map Prod.snd) &&
    rows.all (fun r => decide (r.2 ∉ fixedSlots)) &&
    flag20 ((w.getStor P).get 8) && decide (((w.getStor P).get 18).toNat % 256 = 3)

/-- `checkUsdcF` establishes each listed word is its key's slot (the row fact the joint checker
reuses for its holder rows). -/
theorem checkUsdcF_word {P : Adr} {rows : List (Key × B256)} {w : State}
    (h : checkUsdcF P rows w = true) : ∀ r ∈ rows, Key.slot r.1 = r.2 := by
  simp only [checkUsdcF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hproxy, himpl⟩, hlib⟩, hslot⟩, hP⟩, hL⟩, hword⟩, hasc⟩, hoff⟩, hinit⟩,
    hver⟩ := h
  exact hword

/-- **Soundness of USDC's support-free checkpoint checker.** -/
theorem checkUsdcF_sound {P : Adr} {rows : List (Key × B256)} {w : State}
    (h : checkUsdcF P rows w = true) :
    UsdcInstalled P w ∧ FootCoreL (rowKeys rows) (w.getStor P) := by
  simp only [checkUsdcF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hproxy, himpl⟩, hlib⟩, hslot⟩, hP⟩, hL⟩, hword⟩, hasc⟩, hoff⟩, hinit⟩,
    hver⟩ := h
  have nodupWords := ascending_nodup hasc
  rw [rows_words_eq hword] at nodupWords
  refine ⟨⟨image_of_code_data hproxy, image_of_code_data himpl, image_of_code_data hlib, hslot,
    hP, hL⟩, ?_, ?_, ?_⟩
  · intro k k' hk hk' he
    exact List.inj_on_of_nodup_map nodupWords hk hk' he
  · intro k hk
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
    rw [hword r hr]
    exact hoff r hr
  · refine ⟨fun a => Nat.mod_lt _ (Nat.two_pow_pos 255), hinit, hver⟩

end Blanc.Lift.Usdc
