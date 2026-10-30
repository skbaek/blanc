import Blanc.Lift.BeaconDeposit.Cert
import Blanc.Lift.CheckFast
import Blanc.Lift.BeaconDeposit.CheckTries
import Blanc.Lift.KernelBatch

/-! The deployed beacon deposit certificate checks against the pinned runtime bytes: one
kernel decision per entry, assembled into `cert_check`.  Each decision runs on the trie-reading copy
`checkNodeT` (`Blanc/Lift/CheckFast.lean`), which `checkNodeT_eq` equates with `checkNode`.
`entry_jumps_k` decides entry `k`'s node check and its jump-destination check (`jumpsOkNodeT`,
used by `Blanc/Lift/BeaconDeposit/Jumps.lean`) in one kernel check: both walk the same
abstract stacks, which the kernel then evaluates once. -/

namespace Blanc.Lift.BeaconDeposit

/-- The code's byte and instruction-start tries (depth 13: 8192 ≥ 6358 positions). -/
def codeTries : CodeTries code 13 :=
  TrieData.codeTries

theorem entry_jumps_0 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0x0 [] t_0000_c0 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_0000_c0 [] = true := by
  kernel_rfl_and

theorem entry_0 :
    checkNode code (Cert.entries cert) 0 0x0 [] t_0000_c0 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_0.1

theorem entry_jumps_1 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0x236 [.unk, .unk, .unk, .unk, .unk, .unk] t_0236_c1 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_0236_c1 [.unk, .unk, .unk, .unk, .unk, .unk] = true := by
  kernel_rfl_and

theorem entry_1 :
    checkNode code (Cert.entries cert) 0 0x236 [.unk, .unk, .unk, .unk, .unk, .unk] t_0236_c1 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_1.1

theorem entry_jumps_2 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 1 0x2fe [.unk, .unk, .unk, .ret] t_02fe_c2 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_02fe_c2 [.unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_2 :
    checkNode code (Cert.entries cert) 1 0x2fe [.unk, .unk, .unk, .ret] t_02fe_c2 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_2.1

theorem entry_jumps_3 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0x675 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0675_c3 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_0675_c3 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_3 :
    checkNode code (Cert.entries cert) 0 0x675 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0675_c3 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_3.1

theorem entry_jumps_4 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0x71c [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_071c_c4 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_071c_c4 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_4 :
    checkNode code (Cert.entries cert) 0 0x71c [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_071c_c4 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_4.1

theorem entry_jumps_5 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 1 0x12e2 [.unk, .unk, .unk, .unk, .ret] t_12e2_c5 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_12e2_c5 [.unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_5 :
    checkNode code (Cert.entries cert) 1 0x12e2 [.unk, .unk, .unk, .unk, .ret] t_12e2_c5 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_5.1

theorem entry_jumps_6 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 1 0x26b [.unk, .ret] t_026b_c6 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_026b_c6 [.unk, .ret] = true := by
  kernel_rfl_and

theorem entry_6 :
    checkNode code (Cert.entries cert) 1 0x26b [.unk, .ret] t_026b_c6 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_6.1

theorem entry_jumps_7 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0x304 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0304_c7 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_0304_c7 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_7 :
    checkNode code (Cert.entries cert) 0 0x304 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0304_c7 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_7.1

theorem entry_jumps_8 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 1 0x10b5 [.ret] t_10b5_c8 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_10b5_c8 [.ret] = true := by
  kernel_rfl_and

theorem entry_8 :
    checkNode code (Cert.entries cert) 1 0x10b5 [.ret] t_10b5_c8 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_8.1

theorem entry_jumps_9 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0x1f1 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk] t_01f1_c9 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_01f1_c9 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk] = true := by
  kernel_rfl_and

theorem entry_9 :
    checkNode code (Cert.entries cert) 0 0x1f1 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk] t_01f1_c9 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_9.1

theorem entry_jumps_10 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 1 0x10c7 [.ret] t_10c7_c10 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_10c7_c10 [.ret] = true := by
  kernel_rfl_and

theorem entry_10 :
    checkNode code (Cert.entries cert) 1 0x10c7 [.ret] t_10c7_c10 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_10.1

theorem entry_jumps_11 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0x6d7 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_06d7_c11 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_06d7_c11 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_11 :
    checkNode code (Cert.entries cert) 0 0x6d7 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_06d7_c11 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_11.1

theorem entry_jumps_12 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0x7bf [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_07bf_c12 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_07bf_c12 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_12 :
    checkNode code (Cert.entries cert) 0 0x7bf [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_07bf_c12 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_12.1

theorem entry_jumps_13 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 2 0x16fe [.unk, .unk, .unk, .unk, .ret] t_16fe_c13 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_16fe_c13 [.unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_13 :
    checkNode code (Cert.entries cert) 2 0x16fe [.unk, .unk, .unk, .unk, .ret] t_16fe_c13 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_13.1

theorem entry_jumps_14 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0x8bb [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_08bb_c14 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_08bb_c14 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_14 :
    checkNode code (Cert.entries cert) 0 0x8bb [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_08bb_c14 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_14.1

theorem entry_jumps_15 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0x9b7 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_09b7_c15 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_09b7_c15 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_15 :
    checkNode code (Cert.entries cert) 0 0x9b7 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_09b7_c15 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_15.1

theorem entry_jumps_16 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0xa9d [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0a9d_c16 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_0a9d_c16 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_16 :
    checkNode code (Cert.entries cert) 0 0xa9d [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0a9d_c16 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_16.1

theorem entry_jumps_17 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0xb9c [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0b9c_c17 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_0b9c_c17 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_17 :
    checkNode code (Cert.entries cert) 0 0xb9c [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0b9c_c17 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_17.1

theorem entry_jumps_18 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0xc6c [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0c6c_c18 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_0c6c_c18 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_18 :
    checkNode code (Cert.entries cert) 0 0xc6c [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0c6c_c18 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_18.1

theorem entry_jumps_19 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0xd11 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0d11_c19 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_0d11_c19 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_19 :
    checkNode code (Cert.entries cert) 0 0xd11 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0d11_c19 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_19.1

theorem entry_jumps_20 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0xdf7 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0df7_c20 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_0df7_c20 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_20 :
    checkNode code (Cert.entries cert) 0 0xdf7 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0df7_c20 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_20.1

theorem entry_jumps_21 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0x10ac [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_10ac_c21 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_10ac_c21 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_21 :
    checkNode code (Cert.entries cert) 0 0x10ac [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_10ac_c21 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_21.1

theorem entry_jumps_22 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0xfe8 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0fe8_c22 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_0fe8_c22 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_22 :
    checkNode code (Cert.entries cert) 0 0xfe8 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0fe8_c22 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_22.1

theorem entry_jumps_23 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0xf6e [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0f6e_c23 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_0f6e_c23 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_23 :
    checkNode code (Cert.entries cert) 0 0xf6e [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0f6e_c23 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_23.1

theorem entry_jumps_24 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 1 0x10d1 [.unk, .unk, .unk, .unk, .ret] t_10d1_c24 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_10d1_c24 [.unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_24 :
    checkNode code (Cert.entries cert) 1 0x10d1 [.unk, .unk, .unk, .unk, .ret] t_10d1_c24 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_24.1

theorem entry_jumps_25 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 1 0x14ba [.unk, .ret] t_14ba_c25 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_14ba_c25 [.unk, .ret] = true := by
  kernel_rfl_and

theorem entry_25 :
    checkNode code (Cert.entries cert) 1 0x14ba [.unk, .ret] t_14ba_c25 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_25.1

theorem entry_jumps_26 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0x630 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0630_c26 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_0630_c26 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_26 :
    checkNode code (Cert.entries cert) 0 0x630 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0630_c26 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_26.1

theorem entry_jumps_27 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 1 0x112e [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_112e_c27 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_112e_c27 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_27 :
    checkNode code (Cert.entries cert) 1 0x112e [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_112e_c27 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_27.1

theorem entry_jumps_28 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 1 0x122e [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_122e_c28 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_122e_c28 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_28 :
    checkNode code (Cert.entries cert) 1 0x122e [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_122e_c28 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_28.1

theorem entry_jumps_29 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 1 0x131d [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_131d_c29 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_131d_c29 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_29 :
    checkNode code (Cert.entries cert) 1 0x131d [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_131d_c29 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_29.1

theorem entry_jumps_30 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 1 0x1402 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_1402_c30 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_1402_c30 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  kernel_rfl_and

theorem entry_30 :
    checkNode code (Cert.entries cert) 1 0x1402 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_1402_c30 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_30.1

theorem entry_jumps_31 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0x44 [.unk] t_0044_c31 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_0044_c31 [.unk] = true := by
  kernel_rfl_and

theorem entry_31 :
    checkNode code (Cert.entries cert) 0 0x44 [.unk] t_0044_c31 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_31.1

theorem entry_jumps_32 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0xa4 [.unk] t_00a4_c32 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_00a4_c32 [.unk] = true := by
  kernel_rfl_and

theorem entry_32 :
    checkNode code (Cert.entries cert) 0 0xa4 [.unk] t_00a4_c32 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_32.1

theorem entry_jumps_33 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0x1ba [.unk] t_01ba_c33 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_01ba_c33 [.unk] = true := by
  kernel_rfl_and

theorem entry_33 :
    checkNode code (Cert.entries cert) 0 0x1ba [.unk] t_01ba_c33 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_33.1

theorem entry_jumps_34 :
    checkNodeT code 13 codeTries.bytes (Cert.entries cert) 0 0x244 [.unk] t_0244_c34 = true ∧
      jumpsOkNodeT code 13 codeTries (Cert.entries cert) t_0244_c34 [.unk] = true := by
  kernel_rfl_and

theorem entry_34 :
    checkNode code (Cert.entries cert) 0 0x244 [.unk] t_0244_c34 = true := by
  rw [← checkNodeT_eq codeTries]
  exact entry_jumps_34.1

theorem cert_check : Cert.check code cert = true := by
  unfold Cert.check
  rw [Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  rw [List.all_eq_true]
  intro p hp
  simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact entry_0
  · exact entry_1
  · exact entry_2
  · exact entry_3
  · exact entry_4
  · exact entry_5
  · exact entry_6
  · exact entry_7
  · exact entry_8
  · exact entry_9
  · exact entry_10
  · exact entry_11
  · exact entry_12
  · exact entry_13
  · exact entry_14
  · exact entry_15
  · exact entry_16
  · exact entry_17
  · exact entry_18
  · exact entry_19
  · exact entry_20
  · exact entry_21
  · exact entry_22
  · exact entry_23
  · exact entry_24
  · exact entry_25
  · exact entry_26
  · exact entry_27
  · exact entry_28
  · exact entry_29
  · exact entry_30
  · exact entry_31
  · exact entry_32
  · exact entry_33
  · exact entry_34

end Blanc.Lift.BeaconDeposit
