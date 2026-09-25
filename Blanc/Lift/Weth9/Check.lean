import Blanc.Lift.Weth9.Cert

/-! The WETH9 lift certificate checks against the pinned runtime bytes: one
kernel decision per entry (a single decision over the whole certificate
exceeds the host's memory watchdog), assembled into `cert_check`. -/

namespace Blanc.Lift.Weth9

theorem entry_0 :
    checkNode code (Cert.entries cert) 0 0x0 [] t_0000_c0 = true := by
  decide +kernel

theorem entry_1 :
    checkNode code (Cert.entries cert) 0 0x440 [.ret] t_0440_c1 = true := by
  decide +kernel

theorem entry_2 :
    checkNode code (Cert.entries cert) 2 0xbe3 [.unk, .unk, .ret] t_0be3_c2 = true := by
  decide +kernel

theorem entry_3 :
    checkNode code (Cert.entries cert) 1 0xbce [.unk, .unk, .ret] t_0bce_c3 = true := by
  decide +kernel

theorem entry_4 :
    checkNode code (Cert.entries cert) 2 0xb30 [.ret] t_0b30_c4 = true := by
  decide +kernel

theorem entry_5 :
    checkNode code (Cert.entries cert) 0 0x31a [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk] t_031a_c5 = true := by
  decide +kernel

theorem entry_6 :
    checkNode code (Cert.entries cert) 2 0xb18 [.unk, .ret] t_0b18_c6 = true := by
  decide +kernel

theorem entry_7 :
    checkNode code (Cert.entries cert) 2 0xb05 [.ret] t_0b05_c7 = true := by
  decide +kernel

theorem entry_8 :
    checkNode code (Cert.entries cert) 0 0x9d9 [.unk, .ret] t_09d9_c8 = true := by
  decide +kernel

theorem entry_9 :
    checkNode code (Cert.entries cert) 1 0x68c [.unk, .unk, .unk, .ret] t_068c_c9 = true := by
  decide +kernel

theorem entry_10 :
    checkNode code (Cert.entries cert) 1 0x66d [.ret] t_066d_c10 = true := by
  decide +kernel

theorem entry_11 :
    checkNode code (Cert.entries cert) 1 0x57b [.unk, .unk, .ret] t_057b_c11 = true := by
  decide +kernel

theorem entry_12 :
    checkNode code (Cert.entries cert) 2 0x4dd [.ret] t_04dd_c12 = true := by
  decide +kernel

theorem entry_13 :
    checkNode code (Cert.entries cert) 0 0xf1 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk] t_00f1_c13 = true := by
  decide +kernel

theorem entry_14 :
    checkNode code (Cert.entries cert) 2 0xbc6 [.unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0bc6_c14 = true := by
  decide +kernel

theorem entry_15 :
    checkNode code (Cert.entries cert) 2 0xba9 [.unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0ba9_c15 = true := by
  decide +kernel

theorem entry_16 :
    checkNode code (Cert.entries cert) 2 0x573 [.unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0573_c16 = true := by
  decide +kernel

theorem entry_17 :
    checkNode code (Cert.entries cert) 2 0x556 [.unk, .unk, .unk, .unk, .unk, .unk, .ret] t_0556_c17 = true := by
  decide +kernel

theorem entry_18 :
    checkNode code (Cert.entries cert) 0 0x3d4 [.unk] t_03d4_c18 = true := by
  decide +kernel

theorem entry_19 :
    checkNode code (Cert.entries cert) 0 0x3ca [.unk] t_03ca_c19 = true := by
  decide +kernel

theorem entry_20 :
    checkNode code (Cert.entries cert) 0 0x370 [.unk] t_0370_c20 = true := by
  decide +kernel

theorem entry_21 :
    checkNode code (Cert.entries cert) 0 0x2e2 [.unk] t_02e2_c21 = true := by
  decide +kernel

theorem entry_22 :
    checkNode code (Cert.entries cert) 0 0x295 [.unk] t_0295_c22 = true := by
  decide +kernel

theorem entry_23 :
    checkNode code (Cert.entries cert) 0 0x266 [.unk] t_0266_c23 = true := by
  decide +kernel

theorem entry_24 :
    checkNode code (Cert.entries cert) 0 0x243 [.unk] t_0243_c24 = true := by
  decide +kernel

theorem entry_25 :
    checkNode code (Cert.entries cert) 0 0x1ca [.unk] t_01ca_c25 = true := by
  decide +kernel

theorem entry_26 :
    checkNode code (Cert.entries cert) 0 0x1a1 [.unk] t_01a1_c26 = true := by
  decide +kernel

theorem entry_27 :
    checkNode code (Cert.entries cert) 0 0x147 [.unk] t_0147_c27 = true := by
  decide +kernel

theorem entry_28 :
    checkNode code (Cert.entries cert) 0 0xb9 [.unk] t_00b9_c28 = true := by
  decide +kernel

theorem cert_check : Cert.check code cert = true := by
  unfold Cert.check
  rw [Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  rw [List.all_eq_true]
  intro p hp
  simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

end Blanc.Lift.Weth9
