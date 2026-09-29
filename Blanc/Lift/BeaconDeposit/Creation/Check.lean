import Blanc.Lift.BeaconDeposit.Creation.Cert
import Blanc.Lift.BeaconDeposit.Cert
import Blanc.Lift.CheckFast
import Blanc.Lift.Exact

/-!
The lifted certificate of the Beacon deposit contract's creation input (6,633 bytes: the
constructor, then the appended runtime and metadata as unreachable data) checks against those
bytes: one kernel decision per entry for `Cert.check` and for `Cert.jumpsOk`, each on the
trie-reading copies (`Blanc/Lift/CheckFast.lean`).  What `lift_exact` consumes.
-/

namespace Blanc.Lift.BeaconDeposit.Creation

open Jaune

/-- The creation code's byte and instruction-start tries (depth 13: 8192 ≥ 6633 positions). -/
def codeTries : CodeTries code 13 :=
  CodeTries.ofCode code 13 (by decide +kernel) (by decide +kernel)

theorem entry_0 :
    checkNode code (Cert.entries cert) 0 0x0 [] t_0000_c0 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_1 :
    checkNode code (Cert.entries cert) 0 0x73
      [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk] t_0073_c1 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_2 :
    checkNode code (Cert.entries cert) 0 0x14 [.unk] t_0014_c2 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem cert_check : Cert.check code cert = true := by
  unfold Cert.check
  rw [Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  rw [List.all_eq_true]
  intro p hp
  simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact entry_0
  · exact entry_1
  · exact entry_2

theorem jumps_0 : jumpsOkNode code (Cert.entries cert) t_0000_c0 [] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_1 :
    jumpsOkNode code (Cert.entries cert) t_0073_c1
      [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_2 : jumpsOkNode code (Cert.entries cert) t_0014_c2 [.unk] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_ok : Cert.jumpsOk code cert = true := by
  unfold Cert.jumpsOk
  rw [List.all_eq_true]
  intro p hp
  simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact jumps_0
  · exact jumps_1
  · exact jumps_2

/-- The creation input carries the certified deployed runtime (`Blanc.Lift.BeaconDeposit.code`,
6,358 bytes) at offset 275: the window the constructor copies out and returns. -/
theorem runtime_window :
    code.toList.sliceD 275 6358 0 = Blanc.Lift.BeaconDeposit.code.toList := by
  rw [ByteArray.toList_eq_toList_data, ByteArray.toList_eq_toList_data]
  -- `List.beq` is tail-recursive in the kernel, where `List`'s `DecidableEq` recurses per byte
  apply eq_of_beq
  decide +kernel

end Blanc.Lift.BeaconDeposit.Creation
