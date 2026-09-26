import Blanc.Lift.BeaconDeposit.Cert
import Blanc.Lift.CheckFast

/-! The deployed beacon deposit certificate checks against the pinned runtime bytes: one
kernel decision per entry, assembled into `cert_check`.  Each decision runs on the trie-reading copy
`checkNodeT` (`Blanc/Lift/CheckFast.lean`), which `checkNodeT_eq` equates with `checkNode`. -/

namespace Blanc.Lift.BeaconDeposit

/-- The code's byte and instruction-start tries (depth 13: 8192 ≥ 6358 positions). -/
def codeTries : CodeTries code 13 :=
  CodeTries.ofCode code 13 (by decide +kernel) (by decide +kernel)

theorem entry_0 :
    checkNode code (Cert.entries cert) 0 0x0 [] t_0000_c0 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_1 :
    checkNode code (Cert.entries cert) 0 0x236 [.unk, .unk, .unk, .unk, .unk, .unk] t_0236_c1 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_2 :
    checkNode code (Cert.entries cert) 1 0x2fe [.unk, .unk, .unk, .ret] t_02fe_c2 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_3 :
    checkNode code (Cert.entries cert) 0 0x675 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0675_c3 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_4 :
    checkNode code (Cert.entries cert) 0 0x71c [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_071c_c4 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_5 :
    checkNode code (Cert.entries cert) 1 0x12e2 [.unk, .unk, .unk, .unk, .ret] t_12e2_c5 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_6 :
    checkNode code (Cert.entries cert) 1 0x26b [.unk, .ret] t_026b_c6 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_7 :
    checkNode code (Cert.entries cert) 0 0x304 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0304_c7 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_8 :
    checkNode code (Cert.entries cert) 1 0x10b5 [.ret] t_10b5_c8 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_9 :
    checkNode code (Cert.entries cert) 0 0x1f1 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk] t_01f1_c9 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_10 :
    checkNode code (Cert.entries cert) 1 0x10c7 [.ret] t_10c7_c10 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_11 :
    checkNode code (Cert.entries cert) 0 0x6d7 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_06d7_c11 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_12 :
    checkNode code (Cert.entries cert) 0 0x7bf [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_07bf_c12 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_13 :
    checkNode code (Cert.entries cert) 2 0x16fe [.unk, .unk, .unk, .unk, .ret] t_16fe_c13 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_14 :
    checkNode code (Cert.entries cert) 0 0x8bb [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_08bb_c14 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_15 :
    checkNode code (Cert.entries cert) 0 0x9b7 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_09b7_c15 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_16 :
    checkNode code (Cert.entries cert) 0 0xa9d [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0a9d_c16 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_17 :
    checkNode code (Cert.entries cert) 0 0xb9c [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0b9c_c17 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_18 :
    checkNode code (Cert.entries cert) 0 0xc6c [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0c6c_c18 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_19 :
    checkNode code (Cert.entries cert) 0 0xd11 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0d11_c19 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_20 :
    checkNode code (Cert.entries cert) 0 0xdf7 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0df7_c20 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_21 :
    checkNode code (Cert.entries cert) 0 0x10ac [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_10ac_c21 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_22 :
    checkNode code (Cert.entries cert) 0 0xfe8 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0fe8_c22 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_23 :
    checkNode code (Cert.entries cert) 0 0xf6e [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0f6e_c23 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_24 :
    checkNode code (Cert.entries cert) 1 0x10d1 [.unk, .unk, .unk, .unk, .ret] t_10d1_c24 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_25 :
    checkNode code (Cert.entries cert) 1 0x14ba [.unk, .ret] t_14ba_c25 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_26 :
    checkNode code (Cert.entries cert) 0 0x630 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0630_c26 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_27 :
    checkNode code (Cert.entries cert) 1 0x112e [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_112e_c27 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_28 :
    checkNode code (Cert.entries cert) 1 0x122e [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_122e_c28 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_29 :
    checkNode code (Cert.entries cert) 1 0x131d [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_131d_c29 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_30 :
    checkNode code (Cert.entries cert) 1 0x1402 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] t_1402_c30 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_31 :
    checkNode code (Cert.entries cert) 0 0x44 [.unk] t_0044_c31 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_32 :
    checkNode code (Cert.entries cert) 0 0xa4 [.unk] t_00a4_c32 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_33 :
    checkNode code (Cert.entries cert) 0 0x1ba [.unk] t_01ba_c33 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

theorem entry_34 :
    checkNode code (Cert.entries cert) 0 0x244 [.unk] t_0244_c34 = true := by
  rw [← checkNodeT_eq codeTries]
  decide +kernel

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
