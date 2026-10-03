import Blanc.Lift.VyperNonreentrantDeployed.ProxyEntry
import Blanc.ConcreteRun

/-!
Concrete machine states for the kernel-stepping pilot on the exact 0.2.15
implementation (`kernel-stepping-pilot-v1`). The storage values are
arbitrary but concrete; they are measurement fixtures, not a scenario claim.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Concrete

open Jaune Blanc.ConcreteRun


def attacker : Adr := 0xa11ce00000000000000000000000000000000a11


/-- Arbitrary concrete pool storage at the proxy (the storage owner). -/
def poolStorage : List (Nat × Nat) :=
  [(1, 0xfac7),
   (3, 0xae7ab96520de3a18e5e111b5eaab095312d7fe84),
   (4, 1000000), (5, 900000), (6, 4000000), (7, 20000), (8, 20000),
   (9, 0), (10, 0), (11, 1000000000000000000), (12, 1000000000000000000),
   (0x1d, 1800), (0x1a, 1800)]





end Blanc.Lift.VyperNonreentrantDeployed.Concrete
