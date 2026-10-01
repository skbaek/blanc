import Blanc.Lift.Exact
import Blanc.Lift.WithdrawalRequest.Check

/-!
# Canonical EIP-7002 bytes and valid jump destinations

The certificate uses the existing system-contract ByteArray. Each entry's
jumpability is a separate kernel decision, assembled over the seven entries.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

theorem code_eq : code = Blanc.withdrawalRequestCode := by
  rfl

theorem jumps_0 :
    jumpsOkNode code (Cert.entries cert) t_0000_c0 [] = true := by
  decide +kernel

theorem jumps_1 :
    jumpsOkNode code (Cert.entries cert) t_00df_c1 [.unk, .unk, .unk] = true := by
  decide +kernel

theorem jumps_2 :
    jumpsOkNode code (Cert.entries cert) t_01a0_c2 [.unk] = true := by
  decide +kernel

theorem jumps_3 :
    jumpsOkNode code (Cert.entries cert) t_01cd_c3 [.unk, .unk] = true := by
  decide +kernel

theorem jumps_4 :
    jumpsOkNode code (Cert.entries cert) t_01e8_c4 [.unk, .unk] = true := by
  decide +kernel

theorem jumps_5 :
    jumpsOkNode code (Cert.entries cert) t_004d_c5 [.unk, .unk, .unk, .unk, .unk] = true := by
  decide +kernel

theorem jumps_6 :
    jumpsOkNode code (Cert.entries cert) t_00e1_c6 [.unk, .unk, .unk, .unk] = true := by
  decide +kernel

theorem jumps_ok : Cert.jumpsOk code cert = true := by
  unfold Cert.jumpsOk
  rw [List.all_eq_true]
  intro p hp
  simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact jumps_0
  · exact jumps_1
  · exact jumps_2
  · exact jumps_3
  · exact jumps_4
  · exact jumps_5
  · exact jumps_6

end Blanc.Lift.WithdrawalRequest
