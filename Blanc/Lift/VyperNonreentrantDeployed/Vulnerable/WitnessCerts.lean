import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Token.Cert
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Attacker.Cert
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Attacker2.Check
import Blanc.Lift.Exact

/-!
The V- witness's lifted fixture certificates (the token `T`, the old message-level attacker
`A`, and the tx-level dispatcher attacker `A'`), checked against their runtimes
(`Cert.check`, `Cert.jumpsOk`).  `A` and `T` are each one straight-line entry, a direct
kernel decision; `A'` (`Attacker2`, `vminus-attacker2` in the registry) is one entry with a
dispatcher branch (`cert_check` is `Attacker2.cert_check`, generated via `Check.lean`'s
trie-backed decision; `jumpsOk` is still a direct kernel decision here, since it inspects
only jump destinations).  What `lift_exact` consumes.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable

open Jaune Blanc.Lift

theorem Token.cert_check : Cert.check Token.code Token.cert = true := by decide +kernel

theorem Token.cert_jumpsOk : Cert.jumpsOk Token.code Token.cert = true := by decide +kernel

theorem Attacker.cert_check : Cert.check Attacker.code Attacker.cert = true := by decide +kernel

theorem Attacker.cert_jumpsOk : Cert.jumpsOk Attacker.code Attacker.cert = true := by
  decide +kernel

theorem Attacker2.cert_jumpsOk : Cert.jumpsOk Attacker2.code Attacker2.cert = true := by
  decide +kernel

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable
