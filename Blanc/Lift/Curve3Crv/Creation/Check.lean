import Blanc.Lift.Curve3Crv.Creation.Cert
import Blanc.Lift.Curve3Crv.Cert
import Blanc.Lift.CheckFast
import Blanc.Lift.Exact

/-!
The lifted certificate of the 3Crv LP token's creation input (3,151 bytes: the Vyper constructor,
the runtime, the constructor's deploy tail and the ABI-encoded arguments) checks against those
bytes: one kernel decision per entry for `Cert.check` and for `Cert.jumpsOk`, on the trie-reading
copies (`Blanc/Lift/CheckFast.lean`).  What `lift_exact` consumes.
-/

namespace Blanc.Lift.Curve3Crv.Creation

open Jaune

/-- The creation code's byte and instruction-start tries (depth 12: 4096 ≥ 3151 positions). -/
def codeTries : CodeTries code 12 :=
  CodeTries.ofCode code 12 (by decide +kernel) (by decide +kernel)

theorem entry_0 :
    checkNode code (Cert.entries cert) 0 0x0 [] t_0000_c0 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_1 :
    checkNode code (Cert.entries cert) 0 0x197 [.unk, .unk, .unk, .unk, .unk, .unk] t_0197_c1 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_2 :
    checkNode code (Cert.entries cert) 0 0x1f1 [.unk, .unk, .unk, .unk, .unk, .unk] t_01f1_c2 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_3 :
    checkNode code (Cert.entries cert) 0 0x162 [.unk, .unk, .unk, .unk, .unk, .unk] t_0162_c3 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_4 :
    checkNode code (Cert.entries cert) 0 0x1bc [.unk, .unk, .unk, .unk, .unk, .unk] t_01bc_c4 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_5 :
    checkNode code (Cert.entries cert) 0 0xb37 [] t_0b37_c5 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem cert_check : Cert.check code cert = true := by
  unfold Cert.check
  rw [Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  rw [List.all_eq_true]
  intro p hp
  simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact entry_0
  · exact entry_1
  · exact entry_2
  · exact entry_3
  · exact entry_4
  · exact entry_5

theorem jumps_0 : jumpsOkNode code (Cert.entries cert) t_0000_c0 [] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_1 : jumpsOkNode code (Cert.entries cert) t_0197_c1 [.unk, .unk, .unk, .unk, .unk, .unk] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_2 : jumpsOkNode code (Cert.entries cert) t_01f1_c2 [.unk, .unk, .unk, .unk, .unk, .unk] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_3 : jumpsOkNode code (Cert.entries cert) t_0162_c3 [.unk, .unk, .unk, .unk, .unk, .unk] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_4 : jumpsOkNode code (Cert.entries cert) t_01bc_c4 [.unk, .unk, .unk, .unk, .unk, .unk] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_5 : jumpsOkNode code (Cert.entries cert) t_0b37_c5 [] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_ok : Cert.jumpsOk code cert = true := by
  unfold Cert.jumpsOk
  rw [List.all_eq_true]
  intro p hp
  simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact jumps_0
  · exact jumps_1
  · exact jumps_2
  · exact jumps_3
  · exact jumps_4
  · exact jumps_5

/-- The creation input carries the certified deployed runtime (`Blanc.Lift.Curve3Crv.code`,
2,276 bytes) at offset 595: the window the constructor's deploy tail copies out and returns. -/
theorem runtime_window :
    Blanc.Lift.Curve3Crv.Creation.code.toList.sliceD 595 2276 0 =
      Blanc.Lift.Curve3Crv.code.toList := by
  rw [ByteArray.toList_eq_toList_data, ByteArray.toList_eq_toList_data]
  apply eq_of_beq
  decide +kernel

/-- The certified runtime does not start with `0xEF` (the CREATE code-prefix rule). -/
theorem runtime_head : Blanc.Lift.Curve3Crv.code.toList.head? ≠ some 0xEF := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

end Blanc.Lift.Curve3Crv.Creation
