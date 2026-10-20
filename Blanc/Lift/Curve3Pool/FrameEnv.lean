import Blanc.Lift.Curve3Pool.Observe
import Blanc.Lift.IdentityCall

/-!
# The ENV premises of one pool frame

`PoolFrameEnv D` bundles what the frame `D`'s world and callees must do for the entry walks:
its coins and its token are not precompiles, the identity precompile at `4` is ready
(`IdReady`), every direct child keeps the pool's storage (`PoolCallsKeep`) and the code at `4`,
and (decision R1, option B) every coin child keeps the token's storage too
(`PoolCoinCallsKeepToken`), so that within the frame only the pool's own token calls move 3Crv.

The projections restate each field in the shape the `*_raw` theorems take for the frame
`⟨0, sevm, pre, .ok post, exc⟩`, where `coinAdr`/`tokenAdr` unfold to the entry storage's words
and `children` to `Exec.childFrames exc`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **Coin callbacks keep the token's storage** (R1): a direct child of `D` that runs at one of
the frame's coins (and not at its token) leaves the token's storage as it found it, slot by
slot. Real coins make no callback, so they discharge it trivially; the token's own children
are exempt. -/
def PoolCoinCallsKeepToken (D : Exec.Deriv) : Prop :=
  ∀ c ∈ children D, (∃ k, c.sevm.currentTarget = coinAdr D k) →
    c.sevm.currentTarget ≠ tokenAdr D → ∀ x,
      (c.post.getStor (tokenAdr D)).get x = (c.pre.getStor (tokenAdr D)).get x

/-- **The ENV premises of one pool frame** (design §1.1, §1.3; R1). -/
structure PoolFrameEnv (D : Exec.Deriv) : Prop where
  /-- Every direct child keeps the pool's storage. -/
  keep : PoolCallsKeep D
  /-- Every coin child keeps the token's storage (R1). -/
  keepToken : PoolCoinCallsKeepToken D
  /-- Every direct child keeps the identity precompile's code at `4`. -/
  code4 : ∀ c ∈ children D, c.post.getCode 4 = c.pre.getCode 4
  /-- The identity precompile is ready at the frame's entry. -/
  id : IdReady D.sevm D.devm
  /-- No coin is a precompile. -/
  coins : ∀ k : Fin 3, ¬ D.sevm.benvStat.rules.isPrecomp (coinAdr D k)
  /-- The token is not a precompile. -/
  token : ¬ D.sevm.benvStat.rules.isPrecomp (tokenAdr D)

namespace PoolFrameEnv

variable {D : Exec.Deriv}

/-- The coin premise in the walks' shape (`hcoin`). -/
theorem hcoin (h : PoolFrameEnv D) (k : Fin 3) :
    ¬ D.sevm.benvStat.rules.isPrecomp ((D.devm.getStor D.sevm.currentTarget).get (coinSlot k)).toAdr :=
  h.coins k

/-- The coin premise indexed by a bounded `Nat` (`add_liquidity`'s and `remove_liquidity`'s
segments). -/
theorem hcoinLt (h : PoolFrameEnv D) (i : Nat) (hi : i < 3) :
    ¬ D.sevm.benvStat.rules.isPrecomp
      ((D.devm.getStor D.sevm.currentTarget).get (coinSlot ⟨i, hi⟩)).toAdr :=
  h.coins ⟨i, hi⟩

/-- The token premise in the walks' shape (`htok`). -/
theorem htok (h : PoolFrameEnv D) :
    ¬ D.sevm.benvStat.rules.isPrecomp ((D.devm.getStor D.sevm.currentTarget).get tokenSlot).toAdr :=
  h.token

/-- The children-keep-code-at-`4` premise in the walks' shape (`hidk`). -/
theorem hidk (h : PoolFrameEnv D) :
    ∀ c ∈ Exec.childFrames D.exc, c.post.getCode 4 = c.pre.getCode 4 :=
  h.code4

/-- The per-child pool-storage premise of the segments: every child keeps the pool's storage
slot by slot. -/
theorem hkeep (h : PoolFrameEnv D) :
    ∀ c ∈ Exec.childFrames D.exc, ∀ x,
      (c.post.getStor D.sevm.currentTarget).get x = (c.pre.getStor D.sevm.currentTarget).get x :=
  h.keep

end PoolFrameEnv

end Blanc.Lift.Curve3Pool
