import Blanc.Composition.Curve3PoolVirtualPriceDeploy
import Blanc.Composition.Curve3PoolPublicEffects
import Blanc.Lift.Curve3Pool.HistoryWindow
import Blanc.Lift.Curve3Crv.HistWindow

/-!
# What a `Moment` of mainnet gives the next transaction

`Moment.facts`: right after a recorded transaction since the minter assignment, the pool's and 3Crv's runtimes are
installed, the pool's storage is at a `Checkpoint` of a model state with the constructor's coins and token, and DAI
and USDT are their bytes. The replay stops at the cut through `pool_window_history` and `c3crv_window_framesHist`.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Composition.Curve3PoolCoinKeep (daiInstalledCert usdtInstalledCert)

/-- What a moment gives the next transaction. -/
structure MomentFacts (w : State) : Prop where
  poolCode : w.getCode pool = Curve3Pool.code
  ck : ∃ s : Curve3Pool.State, Curve3Pool.Checkpoint (w.getStor pool) s ∧
    s.coins = Curve3Pool.Creation.coinsN ∧ s.token = Curve3Pool.Creation.tokenN
  c3Code : w.getCode c3 = Curve3Crv.code
  daiCode : w.getCode dai = Lift.Dai.code
  usdtCode : w.getCode usdt = Lift.Usdt.code

variable {d : Deployment} (m : Moment d)

/-- The history since the minter assignment through a moment's block is the history to its start, and the block. -/
theorem sinceMinter_through :
    d.sinceMinter m.through = (d.sinceMinter m.history).step m.block := rfl

/-- **What a moment gives.** -/
theorem Moment.facts (A : Assumes d m.through) : MomentFacts m.world := by
  obtain ⟨hpool, hc3, invs₀, ps, cs, -, -, -, run₀, -, -, joint⟩ :=
    Curve3PoolJointRoot.joint_root_replay (Deployment.toJoint d A.facts)
  obtain ⟨hcoins, htoken⟩ := run₀.coins_token
  have envAt : Curve3Pool.PoolMidEnv (d.sinceC3Block m.through) ((d.sinceMinter m.history).step m.block)
      pool ps.coins ps.token := by
    rw [hcoins, htoken]
    exact A.env
  obtain ⟨poolCode, -, -, -, -, s, -, -, hck, hsc, hst⟩ :=
    Curve3Pool.pool_window_history (d.sinceMinter m.history) m.block m.cut hpool joint.poolCk envAt
  obtain ⟨c3Code, -⟩ := Curve3Crv.c3crv_window_framesHist (d.sinceMinter m.history) m.block m.cut hc3 joint.c3
    A.fresh
  exact
    { poolCode := bytes_eq_of_image poolCode
      ck := ⟨s, hck, hsc.trans hcoins, hst.trans htoken⟩
      c3Code := Curve3Crv.code_of_image c3Code
      daiCode := cutCode_of_cert daiInstalledCert ((d.toPool.step d.pool.trace).append d.toMinter |>.step d.minter.trace |>.append m.history)
        m.block m.cut A.code.daiCode
      usdtCode := cutCode_of_cert usdtInstalledCert ((d.toPool.step d.pool.trace).append d.toMinter |>.step d.minter.trace |>.append m.history)
        m.block m.cut A.code.usdtCode }

end Blanc.Composition.Curve3PoolPublic
