import Blanc.Lift.HistStaticCall

/-! Direct call-code resolution under the selected delegation rules. -/

namespace Blanc.Lift

open Jaune

/-- Under either delegation flag, a callee whose code carries no delegation designator is
called directly with its own code. -/
theorem CallCodeH.direct_of_nodeleg {deleg : Bool} {s : Devm} {t na : Adr} {code : ByteArray}
    {dp : Bool} (nodeleg : getDelegatedCodeAddress (s.getCode t) = none)
    (h : CallCodeH deleg s t na code dp) : na = t ∧ code = s.getCode t ∧ dp = false := by
  cases deleg with
  | false => exact h
  | true =>
    rw [CallCodeH_enabled] at h
    rcases h with ⟨_, same, sameCode, disabled⟩ | ⟨d, delegated, _⟩
    · exact ⟨same, sameCode, disabled⟩
    · rw [nodeleg] at delegated
      cases delegated

/-- A callee whose code carries no delegation designator is called directly with its own code,
under either delegation flag. -/
theorem CallCodeH.of_nodeleg {deleg : Bool} {s : Devm} {t : Adr}
    (nodeleg : getDelegatedCodeAddress (s.getCode t) = none) :
    CallCodeH deleg s t t (s.getCode t) false := by
  cases deleg with
  | false => exact ⟨rfl, rfl, rfl⟩
  | true =>
    rw [CallCodeH_enabled]
    exact .inl ⟨nodeleg, rfl, rfl, rfl⟩

/-- Effective lookup-none routes directly under the selected rules, including when
those rules disable delegation regardless of the target's code bytes. -/
theorem CallCodeH.direct_of_effective {rules : ForkRules} {s : Devm} {t na : Adr}
    {code : ByteArray} {dp : Bool}
    (ready : rules.delegatedCodeAddress (s.getCode t) = none)
    (h : CallCodeH rules.delegationEnabled s t na code dp) :
    na = t ∧ code = s.getCode t ∧ dp = false := by
  cases enabled : rules.delegationEnabled with
  | false =>
    rw [enabled] at h
    exact h
  | true =>
    have nodeleg : getDelegatedCodeAddress (s.getCode t) = none :=
      (rules.delegatedCodeAddress_enabled enabled _).symm.trans ready
    exact CallCodeH.direct_of_nodeleg nodeleg h

/-- Effective lookup-none supplies direct call-code resolution under the selected rules. -/
theorem CallCodeH.of_effective {rules : ForkRules} {s : Devm} {t : Adr}
    (ready : rules.delegatedCodeAddress (s.getCode t) = none) :
    CallCodeH rules.delegationEnabled s t t (s.getCode t) false := by
  cases enabled : rules.delegationEnabled with
  | false => exact ⟨rfl, rfl, rfl⟩
  | true =>
    have nodeleg : getDelegatedCodeAddress (s.getCode t) = none :=
      (rules.delegatedCodeAddress_enabled enabled _).symm.trans ready
    exact CallCodeH.of_nodeleg nodeleg


end Blanc.Lift
