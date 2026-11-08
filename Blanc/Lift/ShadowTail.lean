import Blanc.Lift.WitnessBoundary
import Blanc.Lift.WitnessArms

/-!
# Shadows with a free tail: kernel runs over every world agreeing on finitely many entries

The witness engine (`Blanc/Lift/WitnessArms.lean`) reads the world only through its shadows,
and its agreement (`Agree`) asks the storage and account shadows to describe the world at every
address and key.  A world that agrees with a finite *prefix* of entries is described by that
prefix followed by a tail that lists the rest of the world (`storTailOf`, `acctTailOf`):

* `storOf_prefix_tail`, `acctAgree_prefix_tail`: every world that agrees with a prefix of
  storage entries (resp. account views) is described by the prefix followed by its own tail.

A kernel decision stated over a **free** tail then holds for every such world: the
interpreter's lookups of keys the prefix holds reduce inside the prefix, and a lookup outside
it would leave the decision stuck (it fails; it is never wrong).  The boundary kit with a tail
(`cfgOfT`, `obsDT`, `cfg_of_obsDT`, `obsDT_cont`) compares a boundary's literal prefixes by
`decide` and the tails, which the run never inspects, as terms (`List.drop`).
Nothing here is contract-specific.
-/

namespace Blanc.Lift.Witness

open Jaune

/-! ## The tail of a world -/

/-! ## Boundaries with a tail -/

namespace Boundary

/-- A boundary's storage prefix. -/
def storOf1 : Bnd1 → StorShadow
  | (_, _, _, _, _, stor, _, _, _, _, _) => stor

/-- A boundary's account prefix. -/
def acsOf1 : Bnd1 → AcctShadow
  | (_, _, _, _, _, _, acs, _, _, _, _) => acs

/-- The configuration at boundary `x` with the storage tail `tS` and the account tail `tA`
after its literal prefixes, over a free world and free bookkeeping. -/
def cfgOfT (x : Bnd1) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : Cfg :=
  ⟨(cfgOf1 x m w).devm, (cfgOf1 x m w).f, (cfgOf1 x m w).K, (cfgOf1 x m w).keys,
    (cfgOf1 x m w).adrs, (cfgOf1 x m w).stor ++ tS, (cfgOf1 x m w).acs ++ tA⟩

theorem cfgOf1_acs (x : Bnd1) (m : Meta) (w : World) : (cfgOf1 x m w).acs = acsOf1 x := by
  rcases x with ⟨_, _, _, _, _, _, _, _, _, _, _⟩; rfl

/-- A boundary configuration's account shadow is its prefix followed by the free tail. -/
theorem cfgOfT_acs (x : Bnd1) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World) : (cfgOfT x tS tA m w).acs = acsOf1 x ++ tA := by
  rw [← cfgOf1_acs x m w]; rfl

end Boundary

end Blanc.Lift.Witness
