import Blanc.Lift.Curve3Pool.Bridge
import Blanc.Lift.Curve3Pool.Walk.OneCoinRaw

/-!
# `remove_liquidity_one_coin`'s raw effect, with the certificate checked

The walk files take the certificate's checkedness `Cert.CheckedM code cert mems true` as a premise
(so that they need not import `Check.lean`); here it is discharged by `checkedM` (`Bridge.lean`,
from `cert_checkM`), giving `removeLiquidityOneCoin_raw`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **Safety of `remove_liquidity_one_coin`.** A successful frame of the pool's runtime on the
`remove_liquidity_one_coin` selector, entered at a `Checkpoint` with empty stack and memory,
under the frame premises (the coins and 3Crv are not precompiles; the pool's code is nonempty;
the identity precompile is ready; every child keeps the pool's storage, `PoolCallsKeep`, and
address 4's code), computed the model's step on the decoded call in the environment it
observed, with the raw effect Spec states. -/
theorem removeLiquidityOneCoin_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre)
    (hkeep : PoolCallsKeep ⟨0, sevm, pre, .ok post, exc⟩)
    (hidk : ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o :=
  removeLiquidityOneCoin_raw_of checkedM exc hcode hfork hlen hcd hsel hstack hmem hgas hck htok
    hcoin hpc hid hkeep hidk

end Blanc.Lift.Curve3Pool
