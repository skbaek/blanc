import Blanc.LadderBase
import Blanc.Lift.StaticCall

/-!
# The ECRECOVER precompile on arbitrary input

`ecrecoverSigner` is Jaune's own recovery on the four input words of any calldata; malformed
`v`, zero or out-of-range scalars and failed recovery give `none`. `ecrecoverOutput` is the
precompile's success output: empty, or the recovered address as one word. A clean synchronous
address-1 child on a fork where address 1 is a precompile returns exactly this output; this is
the executed precompile, not a claim that signatures are unforgeable. Every covered fork
activates address 1. Nothing here mentions a contract.
-/

namespace Blanc.Lift
open Jaune

/-- A machine reading `data` with exactly the precompile's fixed charge available. -/
def ecrecoverEvm (data : Bytes) : Evm :=
  let base : Evm := default
  ⟨base.pc, { base.sta with data := data }, base.dyna.withGasLeft gasEcrecover⟩

/-- The precompile's own output on `data`: empty for malformed `v`, zero or out-of-range
scalars and failed recovery, else the recovered address as one word. -/
def ecrecoverOutput (data : Bytes) : Bytes :=
  match executeEcrecover (ecrecoverEvm data) with
  | .ok _ output => output
  | .error _ _ => []

/-- With its fixed charge paid, the precompile returns the output of its own input. -/
theorem executeEcrecover_eq {evm : Evm} (hgas : gasEcrecover ≤ evm.dyna.gasLeft) :
    executeEcrecover evm = .ok gasEcrecover (ecrecoverOutput evm.sta.data) := by
  have paid : gasEcrecover ≤ (ecrecoverEvm evm.sta.data).dyna.gasLeft := Nat.le_refl _
  unfold ecrecoverOutput executeEcrecover PrecompResult.chargeGas
  simp only [hgas, paid, ite_true]
  rw [show (ecrecoverEvm evm.sta.data).sta.data = evm.sta.data from rfl]
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- Every covered fork activates the address-1 precompile. -/
theorem ecrecover_active {s : BenvStat} (h : CoveredFork s.fork) :
    decide (s.rules.isPrecomp 1) = true :=
  h.cases (motive := fun f => decide ((Fork.ruleSet f).isPrecomp 1) = true)
    (by decide) (by decide) (by decide) (by decide)

/-- A clean synchronous non-delegated address-1 child on an activating fork paid the fixed
charge and returned exactly the precompile's output on its calldata. -/
theorem ecrecover_output_of_processMessage_clean
    {sevm : Sevm} {parent child : Devm} {gas : Nat} {data : Bytes} {code : ByteArray}
    {xl : Xlot}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 1) = true)
    (hpm : ProcessMessage
      (callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true data code false) xl (.ok child))
    (hclean : child.error.isSome = false)
    (hfork : CoveredFork sevm.benvStat.fork) :
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
    have hsg : ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true data code
        false).withBenv benv).benv.stat.rules.stateGas = none := by
      change benv.stat.rules.stateGas = none
      rw [benvAfterTransfer_stat hbt]
      exact (show CoveredFork (callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true data
        code false).benv.stat.fork by rw [callMsg_stat]; exact hfork).rules_stateGas_none
    rcases of_executeCode_someCode hca hbody with hpc | hinterp
    · have hexec := hpc.2.2
      rw [hsg, show executePrecomp (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 1 1
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
        obtain ⟨st_mid, hsub, hbenv⟩ := of_benvAfterTransfer rfl hbt
        subst benv
        exact hpre))

end Blanc.Lift
