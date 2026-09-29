import Blanc.Lift.Weth9.Creation.Cert
import Blanc.Lift.Weth9.Cert
import Blanc.Lift.CheckFast
import Blanc.Lift.Exact

/-!
The lifted certificate of WETH9's creation input (3,504 bytes: the constructor, then the appended
runtime as unreachable data) checks against those bytes: one kernel decision per entry for
`Cert.check` and for `Cert.jumpsOk`, on the trie-reading copies (`Blanc/Lift/CheckFast.lean`).
What `lift_exact` consumes.
-/

namespace Blanc.Lift.Weth9.Creation

open Jaune

/-- The creation code's byte and instruction-start tries (depth 12: 4096 ≥ 3504 positions). -/
def codeTries : CodeTries code 12 :=
  CodeTries.ofCode code 12 (by decide +kernel) (by decide +kernel)

theorem entry_0 :
    checkNode code (Cert.entries cert) 0 0x0 [] t_0000_c0 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_1 :
    checkNode code (Cert.entries cert) 1 0x137 [.unk, .unk, .unk, .unk, .unk, .ret] t_0137_c1 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_2 :
    checkNode code (Cert.entries cert) 1 0xc8 [.unk, .unk, .unk, .ret] t_00c8_c2 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_3 :
    checkNode code (Cert.entries cert) 0 0x16d [] t_016d_c3 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_4 :
    checkNode code (Cert.entries cert) 1 0x148 [.unk, .unk, .ret] t_0148_c4 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_5 :
    checkNode code (Cert.entries cert) 1 0x11b [.unk, .unk, .unk, .unk, .unk, .ret] t_011b_c5 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_6 :
    checkNode code (Cert.entries cert) 1 0x14e [.unk, .unk, (.const (Nat.toB256 0x16a)), .ret] t_014e_c6 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_7 :
    checkNode code (Cert.entries cert) 1 0x16a [.unk, .ret] t_016a_c7 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem cert_check : Cert.check code cert = true := by
  unfold Cert.check
  rw [Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  rw [List.all_eq_true]
  intro p hp
  simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact entry_0
  · exact entry_1
  · exact entry_2
  · exact entry_3
  · exact entry_4
  · exact entry_5
  · exact entry_6
  · exact entry_7

theorem jumps_0 : jumpsOkNode code (Cert.entries cert) t_0000_c0 [] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_1 : jumpsOkNode code (Cert.entries cert) t_0137_c1 [.unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_2 : jumpsOkNode code (Cert.entries cert) t_00c8_c2 [.unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_3 : jumpsOkNode code (Cert.entries cert) t_016d_c3 [] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_4 : jumpsOkNode code (Cert.entries cert) t_0148_c4 [.unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_5 : jumpsOkNode code (Cert.entries cert) t_011b_c5 [.unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_6 : jumpsOkNode code (Cert.entries cert) t_014e_c6 [.unk, .unk, (.const (Nat.toB256 0x16a)), .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_7 : jumpsOkNode code (Cert.entries cert) t_016a_c7 [.unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_ok : Cert.jumpsOk code cert = true := by
  unfold Cert.jumpsOk
  rw [List.all_eq_true]
  intro p hp
  simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact jumps_0
  · exact jumps_1
  · exact jumps_2
  · exact jumps_3
  · exact jumps_4
  · exact jumps_5
  · exact jumps_6
  · exact jumps_7

/-- The creation input carries the certified deployed runtime (`Blanc.Lift.Weth9.code`,
3,124 bytes) at offset 380: the window the constructor copies out and returns. -/
theorem runtime_window :
    code.toList.sliceD 380 3124 0 = Blanc.Lift.Weth9.code.toList := by
  rw [ByteArray.toList_eq_toList_data, ByteArray.toList_eq_toList_data]
  apply eq_of_beq
  decide +kernel

/-- The certified runtime does not start with `0xEF` (the CREATE code-prefix rule). -/
theorem runtime_head : Blanc.Lift.Weth9.code.toList.head? ≠ some 0xEF := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

end Blanc.Lift.Weth9.Creation
