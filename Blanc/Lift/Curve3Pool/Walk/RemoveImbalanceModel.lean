import Blanc.Lift.Curve3Pool.Model
import Blanc.Lift.Curve3Pool.Decode

/-!
# `remove_liquidity_imbalance`: the model entry point (segment 0)

First segment of the `remove_liquidity_imbalance` walk (source lines 527–579, model
`removeLiquidityImbalance`): the environment shape a frame observes (`rliEnv`), the
dispatcher fact selecting the model's call (`rli_decode`), and the step unfolding
(`rli_step`).

Shared-library check: the model (`Model.removeLiquidityImbalance`), the decoder
(`Decode.decodeCall_at`, `Decode.callAt`) and the callee contracts
(`Callee/A.a_spec`, `Callee/GetDMem.getDMem_spec`) already exist and are reused, not
copied. Nothing below is generic, so nothing is hoisted.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune

/-- The environment a `remove_liquidity_imbalance` frame observes: the supply word `T`,
every coin's `transfer` and the `burnFrom` accepted, no balance read, no pull, no mint. -/
def rliEnv (sevm : Sevm) (T : B256) : Env :=
  ⟨sevm.benvStat.time.toNat, sevm.caller.toB256.toNat, sevm.value.toNat,
    fun _ => ⟨none, none, false, true⟩, some T.toNat, false, true⟩

/-- The dispatcher selects `removeLiquidityImbalance` on test `8`
(`selRemoveLiquidityImbalance`). -/
theorem rli_decode {sevm : Sevm}
    (hsel : Sevm.selector sevm = selRemoveLiquidityImbalance)
    (hlen : 4 ≤ sevm.data.length) :
    decodeCall sevm = .removeLiquidityImbalance (argV3 sevm 0) (arg sevm 3) :=
  decodeCall_at (k := 8) rfl hsel hlen

/-- The model's step on the decoded call is `removeLiquidityImbalance`, once the
non-payable guard is discharged. -/
theorem rli_step {s : State} {e : Env} {amounts : V3} {maxBurn : Nat}
    (hval : e.value = 0) :
    step s e (.removeLiquidityImbalance amounts maxBurn) =
      removeLiquidityImbalance s e amounts maxBurn := by
  show (if e.value = 0 then body s e (.removeLiquidityImbalance amounts maxBurn)
    else none) = _
  rw [hval, ite_eq_left rfl]
  simp only [body]

end Blanc.Lift.Curve3Pool
