import Blanc.Lift.Ecrecover
import Blanc.HistoricalFork
import Blanc.Lift.HistStaticCall

/-!
# The ECRECOVER precompile on historical forks

`ecrecover_activeH`: every fork of the semantics activates the address-1 precompile.
`ecrecover_output_of_processMessage_cleanH` is `ecrecover_output_of_processMessage_clean` from
`rules.stateGas = none` alone; `ecrecover_output_of_processMessage_cleanH_covered` recovers the
modern statement. `CallCodeH.direct_of_nodeleg` resolves a call's code under either delegation
flag when the callee's code carries no delegation designator (`CallCodeH.of_nodeleg` builds it).
Nothing here mentions a contract.
-/

namespace Blanc.Lift
open Jaune

/-- Every fork of the semantics activates the address-1 precompile. -/
theorem ecrecover_activeH (s : BenvStat) : decide (s.rules.isPrecomp 1) = true := by
  show decide ((Fork.ruleSet s.fork).isPrecomp 1) = true
  cases s.fork <;> decide

/-- A clean synchronous non-delegated address-1 child on an activating fork paid the fixed
charge and returned exactly the precompile's output on its calldata, from
`rules.stateGas = none` alone. -/
theorem ecrecover_output_of_processMessage_cleanH
    {sevm : Sevm} {parent child : Devm} {gas : Nat} {data : Bytes} {code : ByteArray}
    {xl : Xlot}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 1) = true)
    (hpm : ProcessMessage
      (callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true data code false) xl (.ok child))
    (hclean : child.error.isSome = false)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    gasEcrecover ≤ gas ∧ child.output = ecrecoverOutput data := by
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp hpm
  unfold FrameBody at hbody
  rcases hbt :
      (callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true data code false).benvAfterTransfer
    with e | benv <;> rw [hbt] at hbody
  · rw [hbody.2] at hset
    unfold processMessage.settle at hset
    cases hset
  · have hca : ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true data code
        false).withBenv benv).codeAddress = some 1 := rfl
    have hsgMsg : ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true data code
        false).withBenv benv).benv.stat.rules.stateGas = none := by
      change benv.stat.rules.stateGas = none
      rw [benvAfterTransfer_stat hbt, callMsg_stat]
      exact hsg
    rcases of_executeCode_someCode hca hbody with hpc | hinterp
    · have hexec := hpc.2.2
      rw [hsgMsg, show executePrecomp (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 1 1
          true true data code false).withBenv benv)) 1 =
          applyPrecompResult (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true
            true data code false).withBenv benv))
            (executeEcrecover (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true
              true data code false).withBenv benv))) from rfl] at hexec
      by_cases hgas : gasEcrecover ≤ gas
      · rw [executeEcrecover_eq (evm := (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true data code false).withBenv
          benv)))
          (by change gasEcrecover ≤ gas; exact hgas)] at hexec
        simp only [applyPrecompResult, executeCode.handleErrorWith] at hexec
        rw [← hexec] at hset
        unfold processMessage.settle at hset
        simp only [bind, Except.bind, Option.isSome] at hset
        injection hset with hchild
        subst child
        exact ⟨hgas, rfl⟩
      · unfold executeEcrecover PrecompResult.chargeGas at hexec
        rw [show (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true data code false).withBenv
          benv)).dyna.gasLeft = gas from rfl] at hexec
        simp only [hgas, ite_false, applyPrecompResult, executeCode.handleErrorWith] at hexec
        rw [← hexec] at hset
        unfold processMessage.settle at hset
        simp only [bind, Except.bind, Option.isSome] at hset
        injection hset with hchild
        subst child
        cases hclean
    · exact False.elim (hinterp.1 (by
        rw [Msg.benvAfterTransfer_of_value_zero (by rfl)] at hbt
        cases hbt
        exact hpre))

theorem ecrecover_output_of_processMessage_cleanH_covered
    {sevm : Sevm} {parent child : Devm} {gas : Nat} {data : Bytes} {code : ByteArray}
    {xl : Xlot}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 1) = true)
    (hpm : ProcessMessage
      (callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true data code false) xl (.ok child))
    (hclean : child.error.isSome = false)
    (hfork : CoveredFork sevm.benvStat.fork) :
    gasEcrecover ≤ gas ∧ child.output = ecrecoverOutput data :=
  ecrecover_output_of_processMessage_cleanH hpre hpm hclean hfork.rules_stateGas_none

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

end Blanc.Lift
