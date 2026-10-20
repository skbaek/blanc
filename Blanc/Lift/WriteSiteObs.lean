import Blanc.Lift.WriteSiteTerm

/-! ## W3/W4 observations (`Blanc/Lift/WriteSiteObs.lean`)

What an `SSTORE` step observes, and the step relation recording it.
The soundness unit W3 imports this file. -/

namespace Blanc.Lift.WriteSite

open Jaune

/-- What an `SSTORE` step observes: its slot and value meet a listed site, read in `ε`. -/
def WsObs (sites : List Site) (ε : Env) (sevm : Sevm) (d : Devm) (n : Ninst) : Prop :=
  n = .reg .sstore → ∀ x v rest, d.stack = x :: v :: rest →
    ∃ s ∈ sites, s.slot.Den ε x ∧ (∀ g ∈ s.guards, g.1.Den ε g.2) ∧
      (s.nonInc = true → v.toNat ≤ (d.getStorVal sevm.currentTarget x).toNat)

/-- A step relation that also records the write-site observation. -/
def WsStep (sites : List Site) (ε : Env) (P : Sevm → Devm → Ninst → Devm → Prop) :
    Sevm → Devm → Ninst → Devm → Prop :=
  fun s d n d' => P s d n d' ∧ WsObs sites ε s d n

end Blanc.Lift.WriteSite
