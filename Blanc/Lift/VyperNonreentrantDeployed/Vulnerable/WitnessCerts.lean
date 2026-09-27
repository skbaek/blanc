import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Token.Cert
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Attacker.Cert
import Blanc.Lift.Exact

/-!
The V- witness's lifted fixture certificates (the token `T` and the attacker `A`), checked
against their runtimes (`Cert.check`, `Cert.jumpsOk`: each is one straight-line entry, a
direct kernel decision).  What `lift_exact` consumes.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable

open Jaune Blanc.Lift

theorem Token.cert_check : Cert.check Token.code Token.cert = true := by decide +kernel

theorem Token.cert_jumpsOk : Cert.jumpsOk Token.code Token.cert = true := by decide +kernel

theorem Attacker.cert_check : Cert.check Attacker.code Attacker.cert = true := by decide +kernel

theorem Attacker.cert_jumpsOk : Cert.jumpsOk Attacker.code Attacker.cert = true := by
  decide +kernel

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable
