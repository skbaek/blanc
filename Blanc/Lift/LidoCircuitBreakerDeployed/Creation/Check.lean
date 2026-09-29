import Blanc.Lift.LidoCircuitBreakerDeployed.Creation.Cert
import Blanc.Lift.LidoCircuitBreakerDeployed.Cert
import Blanc.Lift.CheckFast
import Blanc.Lift.Exact

/-!
The lifted certificate of the Lido CircuitBreaker's creation input (5,638 bytes: the solc 0.8.34
constructor, the 4,584-byte runtime template as unreachable data, and the 224 bytes of ABI-encoded
constructor arguments) checks against those bytes: one kernel decision per entry for
`Cert.check` and for `Cert.jumpsOk`, on the trie-reading copies (`Blanc/Lift/CheckFast.lean`).
What `lift_exact` consumes.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed.Creation

open Jaune

/-- The creation code's byte and instruction-start tries (depth 13: 8192 ≥ 5638 positions). -/
def codeTries : CodeTries code 13 :=
  CodeTries.ofCode code 13 (by decide +kernel) (by decide +kernel)

theorem entry_0 :
    checkNode code (Cert.entries cert) 0 0x0 [] t_0000_c0 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_1 :
    checkNode code (Cert.entries cert) 7 0x26d [.unk, .unk, .ret] t_026d_c1 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_2 :
    checkNode code (Cert.entries cert) 0 0x160 [.unk, .ret] t_0160_c2 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_3 :
    checkNode code (Cert.entries cert) 0 0x1e5 [.unk, .ret] t_01e5_c3 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_4 :
    checkNode code (Cert.entries cert) 0 0x2d0 [] t_02d0_c4 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem cert_check : Cert.check code cert = true := by
  unfold Cert.check
  rw [Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  rw [List.all_eq_true]
  intro p hp
  simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact entry_0
  · exact entry_1
  · exact entry_2
  · exact entry_3
  · exact entry_4

theorem jumps_0 : jumpsOkNode code (Cert.entries cert) t_0000_c0 [] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_1 : jumpsOkNode code (Cert.entries cert) t_026d_c1 [.unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_2 : jumpsOkNode code (Cert.entries cert) t_0160_c2 [.unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_3 : jumpsOkNode code (Cert.entries cert) t_01e5_c3 [.unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_4 : jumpsOkNode code (Cert.entries cert) t_02d0_c4 [] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_ok : Cert.jumpsOk code cert = true := by
  unfold Cert.jumpsOk
  rw [List.all_eq_true]
  intro p hp
  simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact jumps_0
  · exact jumps_1
  · exact jumps_2
  · exact jumps_3
  · exact jumps_4

/-- The certified deployed runtime does not start with `0xEF` (the CREATE code-prefix rule). -/
theorem runtime_head : Blanc.Lift.LidoCircuitBreakerDeployed.code.toList.head? ≠ some 0xEF := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

end Blanc.Lift.LidoCircuitBreakerDeployed.Creation
