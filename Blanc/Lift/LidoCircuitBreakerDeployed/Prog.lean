import Blanc.Lift.LidoCircuitBreakerDeployed.Cert

/-! The lifted deployed program, separated from the kernel decision file so
small execution proofs need only import checked certificate data. -/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

/-- The exact deployed runtime's certified lifted program. -/
abbrev prog : List SFunc := Cert.prog cert

theorem entry32_lookup : prog[32]? = some t_0934_c32 := by
  rfl

theorem entry4_lookup : prog[4]? = some t_0a81_c4 := by
  rfl

theorem entry5_lookup : prog[5]? = some t_0c5e_c5 := by
  rfl

theorem entry24_lookup : prog[24]? = some t_110e_c24 := by
  rfl

theorem entry25_lookup : prog[25]? = some t_1145_c25 := by
  rfl

theorem entry3_lookup : prog[3]? = some t_051a_c3 := by
  rfl

theorem entry26_lookup : prog[26]? = some t_1158_c26 := by
  rfl

theorem entry27_lookup : prog[27]? = some t_1158_c27 := by
  rfl

theorem entry28_lookup : prog[28]? = some t_1185_c28 := by
  rfl

theorem entry38_lookup : prog[38]? = some t_107b_c38 := by
  rfl

theorem entry39_lookup : prog[39]? = some t_107b_c39 := by
  rfl

theorem entry40_lookup : prog[40]? = some t_10da_c40 := by
  rfl

theorem entry42_lookup : prog[42]? = some t_107b_c42 := by
  rfl

end Blanc.Lift.LidoCircuitBreakerDeployed
