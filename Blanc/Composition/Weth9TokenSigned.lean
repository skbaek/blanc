import Blanc.Composition.Weth9Token
import Blanc.Lift.Token.Signed

/-!
# WETH9 under the signature variant (C4)

WETH9 has no signature path: its book read with no signer satisfies the signature-variant laws.
-/

namespace Blanc.Composition.Weth9Token

open Jaune Blanc Blanc.Lift.Token

/-- **WETH9 satisfies the signature variant** (`Blanc/Composition/Weth9TokenSigned.lean`). -/
theorem weth9Book_lawsS : BookLawsS weth9Book.unsigned :=
  weth9Book_laws.unsigned

end Blanc.Composition.Weth9Token
