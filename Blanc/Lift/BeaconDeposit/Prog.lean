import Blanc.Lift.BeaconDeposit.Cert

/-! The lifted deployed beacon deposit program, apart from its kernel check, so that walks over
its trees do not import the certificate decisions. -/

namespace Blanc.Lift.BeaconDeposit

/-- The lifted deployed beacon deposit program. -/
abbrev prog : List SFunc := Cert.prog cert

end Blanc.Lift.BeaconDeposit
