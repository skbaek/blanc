import Blanc.Lift.Exact
import Blanc.Lift.Weth9.Lift

/-! The WETH9 certificate's jump destinations are valid: one kernel decision per
entry (a single decision over the whole certificate exceeds the host's memory watchdog). -/

namespace Blanc.Lift.Weth9

open Jaune

theorem jumps_0 :
    jumpsOkNode code (Cert.entries cert) t_0000_c0 [] = true := by
  decide +kernel

theorem jumps_1 :
    jumpsOkNode code (Cert.entries cert) t_0440_c1 [.ret] = true := by
  decide +kernel

theorem jumps_2 :
    jumpsOkNode code (Cert.entries cert) t_0be3_c2 [.unk, .unk, .ret] = true := by
  decide +kernel

theorem jumps_3 :
    jumpsOkNode code (Cert.entries cert) t_0bce_c3 [.unk, .unk, .ret] = true := by
  decide +kernel

theorem jumps_4 :
    jumpsOkNode code (Cert.entries cert) t_0b30_c4 [.ret] = true := by
  decide +kernel

theorem jumps_5 :
    jumpsOkNode code (Cert.entries cert) t_031a_c5 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk] = true := by
  decide +kernel

theorem jumps_6 :
    jumpsOkNode code (Cert.entries cert) t_0b18_c6 [.unk, .ret] = true := by
  decide +kernel

theorem jumps_7 :
    jumpsOkNode code (Cert.entries cert) t_0b05_c7 [.ret] = true := by
  decide +kernel

theorem jumps_8 :
    jumpsOkNode code (Cert.entries cert) t_09d9_c8 [.unk, .ret] = true := by
  decide +kernel

theorem jumps_9 :
    jumpsOkNode code (Cert.entries cert) t_068c_c9 [.unk, .unk, .unk, .ret] = true := by
  decide +kernel

theorem jumps_10 :
    jumpsOkNode code (Cert.entries cert) t_066d_c10 [.ret] = true := by
  decide +kernel

theorem jumps_11 :
    jumpsOkNode code (Cert.entries cert) t_057b_c11 [.unk, .unk, .ret] = true := by
  decide +kernel

theorem jumps_12 :
    jumpsOkNode code (Cert.entries cert) t_04dd_c12 [.ret] = true := by
  decide +kernel

theorem jumps_13 :
    jumpsOkNode code (Cert.entries cert) t_00f1_c13 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk] = true := by
  decide +kernel

theorem jumps_14 :
    jumpsOkNode code (Cert.entries cert) t_0bc6_c14 [.unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  decide +kernel

theorem jumps_15 :
    jumpsOkNode code (Cert.entries cert) t_0ba9_c15 [.unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  decide +kernel

theorem jumps_16 :
    jumpsOkNode code (Cert.entries cert) t_0573_c16 [.unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  decide +kernel

theorem jumps_17 :
    jumpsOkNode code (Cert.entries cert) t_0556_c17 [.unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  decide +kernel

theorem jumps_18 :
    jumpsOkNode code (Cert.entries cert) t_03d4_c18 [.unk] = true := by
  decide +kernel

theorem jumps_19 :
    jumpsOkNode code (Cert.entries cert) t_03ca_c19 [.unk] = true := by
  decide +kernel

theorem jumps_20 :
    jumpsOkNode code (Cert.entries cert) t_0370_c20 [.unk] = true := by
  decide +kernel

theorem jumps_21 :
    jumpsOkNode code (Cert.entries cert) t_02e2_c21 [.unk] = true := by
  decide +kernel

theorem jumps_22 :
    jumpsOkNode code (Cert.entries cert) t_0295_c22 [.unk] = true := by
  decide +kernel

theorem jumps_23 :
    jumpsOkNode code (Cert.entries cert) t_0266_c23 [.unk] = true := by
  decide +kernel

theorem jumps_24 :
    jumpsOkNode code (Cert.entries cert) t_0243_c24 [.unk] = true := by
  decide +kernel

theorem jumps_25 :
    jumpsOkNode code (Cert.entries cert) t_01ca_c25 [.unk] = true := by
  decide +kernel

theorem jumps_26 :
    jumpsOkNode code (Cert.entries cert) t_01a1_c26 [.unk] = true := by
  decide +kernel

theorem jumps_27 :
    jumpsOkNode code (Cert.entries cert) t_0147_c27 [.unk] = true := by
  decide +kernel

theorem jumps_28 :
    jumpsOkNode code (Cert.entries cert) t_00b9_c28 [.unk] = true := by
  decide +kernel

theorem jumps_ok : Cert.jumpsOk code cert = true := by
  unfold Cert.jumpsOk
  rw [List.all_eq_true]
  intro p hp
  simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact jumps_0
  · exact jumps_1
  · exact jumps_2
  · exact jumps_3
  · exact jumps_4
  · exact jumps_5
  · exact jumps_6
  · exact jumps_7
  · exact jumps_8
  · exact jumps_9
  · exact jumps_10
  · exact jumps_11
  · exact jumps_12
  · exact jumps_13
  · exact jumps_14
  · exact jumps_15
  · exact jumps_16
  · exact jumps_17
  · exact jumps_18
  · exact jumps_19
  · exact jumps_20
  · exact jumps_21
  · exact jumps_22
  · exact jumps_23
  · exact jumps_24
  · exact jumps_25
  · exact jumps_26
  · exact jumps_27
  · exact jumps_28

/-- The converse bridge at the pinned WETH9 bytes: a gas-exact synthetic run of the lifted
program is a real Jaune execution of the deployed code. -/
theorem exec_of_runExact {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (hrun : SProg.RunExact prog sevm pre post) :
    Nonempty (Exec 0 sevm pre (.ok post)) :=
  lift_exact cert_check jumps_ok hcode hfork hrun

end Blanc.Lift.Weth9
