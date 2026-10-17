import Blanc.Lift.Curve3Pool.Walk.RemoveLiquiditySafe

/-!
# `remove_liquidity` under the per-child keep premises

`removeLiquidity_rawK` restates `removeLiquidity_raw` with the frame premises the other entries
take (`exchange_raw`, `addLiquidity_raw`): every direct child keeps the pool's storage
(`PoolCallsKeep`) and the code at `4`, in place of the target-level `CallKeeps`/`StaticKeeps`.
Both forms run through `removeLiquidity_rawT_of`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **Safety of `remove_liquidity`** under `PoolCallsKeep` and children keeping the code at `4`,
in the observed environment `rlEnv`. -/
theorem removeLiquidity_rawTK {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidity)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ k : Fin 3,
      ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre)
    (hkeep : PoolCallsKeep ⟨0, sevm, pre, .ok post, exc⟩)
    (hidk : ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) :
    ∃ T o, step s (rlEnv sevm T) (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post (rlEnv sevm T) o :=
  removeLiquidity_rawT_of exc hcode hfork hlen hcd hsel hstack hmem hgas hck htok hcoin hpc hid
    (.inr (RlKeep.of_pool hkeep hidk))

/-- **Safety of `remove_liquidity`** under `PoolCallsKeep` and children keeping the code at `4`,
with the observed environment left abstract. -/
theorem removeLiquidity_rawK {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidity)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ k : Fin 3,
      ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre)
    (hkeep : PoolCallsKeep ⟨0, sevm, pre, .ok post, exc⟩)
    (hidk : ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  obtain ⟨T, o, h1, h2⟩ := removeLiquidity_rawTK exc hcode hfork hlen hcd hsel hstack hmem hgas hck
    htok hcoin hpc hid hkeep hidk
  exact ⟨_, o, h1, h2⟩

end Blanc.Lift.Curve3Pool
