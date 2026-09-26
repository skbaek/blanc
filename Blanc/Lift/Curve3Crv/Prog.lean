import Blanc.Lift.Curve3Crv.Cert

/-! The lifted deployed 3Crv program, apart from its kernel check, so that walks over its trees
do not import the certificate decisions. -/

namespace Blanc.Lift.Curve3Crv

/-- The lifted deployed 3Crv program. -/
abbrev prog : List SFunc := Cert.prog cert

end Blanc.Lift.Curve3Crv
