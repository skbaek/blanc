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

end Blanc.Lift.LidoCircuitBreakerDeployed
