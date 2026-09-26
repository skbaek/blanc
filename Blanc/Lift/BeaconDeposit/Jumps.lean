import Blanc.Lift.Exact
import Blanc.Lift.BeaconDeposit.Lift

/-! The deployed beacon deposit certificate's jump destinations are valid: one kernel decision per
entry (a single decision over the whole certificate exceeds the host's memory watchdog). -/

namespace Blanc.Lift.BeaconDeposit

open Jaune

theorem jumps_0 :
    jumpsOkNode code (Cert.entries cert) t_0000_c0 [] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_1 :
    jumpsOkNode code (Cert.entries cert) t_0236_c1 [.unk, .unk, .unk, .unk, .unk, .unk] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_2 :
    jumpsOkNode code (Cert.entries cert) t_02fe_c2 [.unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_3 :
    jumpsOkNode code (Cert.entries cert) t_0675_c3 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_4 :
    jumpsOkNode code (Cert.entries cert) t_071c_c4 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_5 :
    jumpsOkNode code (Cert.entries cert) t_12e2_c5 [.unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_6 :
    jumpsOkNode code (Cert.entries cert) t_026b_c6 [.unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_7 :
    jumpsOkNode code (Cert.entries cert) t_0304_c7 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_8 :
    jumpsOkNode code (Cert.entries cert) t_10b5_c8 [.ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_9 :
    jumpsOkNode code (Cert.entries cert) t_01f1_c9 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_10 :
    jumpsOkNode code (Cert.entries cert) t_10c7_c10 [.ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_11 :
    jumpsOkNode code (Cert.entries cert) t_06d7_c11 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_12 :
    jumpsOkNode code (Cert.entries cert) t_07bf_c12 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_13 :
    jumpsOkNode code (Cert.entries cert) t_16fe_c13 [.unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_14 :
    jumpsOkNode code (Cert.entries cert) t_08bb_c14 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_15 :
    jumpsOkNode code (Cert.entries cert) t_09b7_c15 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_16 :
    jumpsOkNode code (Cert.entries cert) t_0a9d_c16 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_17 :
    jumpsOkNode code (Cert.entries cert) t_0b9c_c17 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_18 :
    jumpsOkNode code (Cert.entries cert) t_0c6c_c18 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_19 :
    jumpsOkNode code (Cert.entries cert) t_0d11_c19 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_20 :
    jumpsOkNode code (Cert.entries cert) t_0df7_c20 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_21 :
    jumpsOkNode code (Cert.entries cert) t_10ac_c21 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_22 :
    jumpsOkNode code (Cert.entries cert) t_0fe8_c22 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_23 :
    jumpsOkNode code (Cert.entries cert) t_0f6e_c23 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_24 :
    jumpsOkNode code (Cert.entries cert) t_10d1_c24 [.unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_25 :
    jumpsOkNode code (Cert.entries cert) t_14ba_c25 [.unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_26 :
    jumpsOkNode code (Cert.entries cert) t_0630_c26 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_27 :
    jumpsOkNode code (Cert.entries cert) t_112e_c27 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_28 :
    jumpsOkNode code (Cert.entries cert) t_122e_c28 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_29 :
    jumpsOkNode code (Cert.entries cert) t_131d_c29 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_30 :
    jumpsOkNode code (Cert.entries cert) t_1402_c30 [.unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .unk, .ret] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_31 :
    jumpsOkNode code (Cert.entries cert) t_0044_c31 [.unk] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_32 :
    jumpsOkNode code (Cert.entries cert) t_00a4_c32 [.unk] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_33 :
    jumpsOkNode code (Cert.entries cert) t_01ba_c33 [.unk] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_34 :
    jumpsOkNode code (Cert.entries cert) t_0244_c34 [.unk] = true := by
  rw [← jumpsOkNodeT_eq codeTries]
  decide +kernel

theorem jumps_ok : Cert.jumpsOk code cert = true := by
  unfold Cert.jumpsOk
  rw [List.all_eq_true]
  intro p hp
  simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact jumps_29
  · exact jumps_30
  · exact jumps_31
  · exact jumps_32
  · exact jumps_33
  · exact jumps_34

/-- The converse bridge at the pinned deployed beacon deposit bytes: a gas-exact synthetic run of the lifted
program is a real Jaune execution of the deployed code. -/
theorem exec_of_runExact {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (hrun : SProg.RunExact prog sevm pre post) :
    Nonempty (Exec 0 sevm pre (.ok post)) :=
  lift_exact cert_check jumps_ok hcode hfork hrun

end Blanc.Lift.BeaconDeposit
