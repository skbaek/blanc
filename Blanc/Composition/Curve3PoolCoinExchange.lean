import Blanc.Composition.Curve3PoolDaiCoin
import Blanc.Composition.Curve3PoolUsdc22Coin
import Blanc.Lift.Curve3Pool.ExchangeLive

/-!
# `exchange_live` with its coin calls discharged by real bytes

`exchange_dai_usdc22_live`: an `exchange` frame pulling DAI and pushing USDC over FiatTokenV2_2, with
`CoinPullOkAt` and `CoinPushOkAt` discharged by those coins' certified runtimes at the single gas
window `U = 95000`. The keep premise stays, because USDC's frames can `CALL` out in
`rescueERC20`, so no selector-free `ChildKeepsAt` holds for it.
-/

namespace Blanc.Composition.Curve3PoolCoinExchange

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Composition.Curve3Pool3CrvInstance (CoinLeaves)
open Blanc.Composition.UsdcLive (ProxyAt)

/-- **An `exchange` frame from DAI to USDC over FiatTokenV2_2 is live**, with both coin calls run from
their certified bytes. -/
theorem exchange_dai_usdc22_live {sevm : Sevm} {pre : Devm} {s : Curve3Pool.State} {o : Out} {i j : Fin 3}
    {B1 B2 : B256} {W W' W'' : Devm → Prop} {G : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : 2 ≤ sevm.depth)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange)
    (hi : i.val = (exI sevm).toNat) (hj : j.val = (exJ sevm).toNat)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (hstep : step s (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) (decodeCall sevm) = some o)
    (hcoin : ∀ k : Fin 3,
      ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre)
    (hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
      PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
        ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
    (hWc : WClosed sevm W) (hW'c : WClosed sevm W') (hWb : W pre) (hfee : i ≠ feeIndex)
    (hW''c : WClosed sevm W'')
    (hi1 : ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr ≠ sevm.currentTarget)
    (hj1 : ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr ≠ sevm.currentTarget)
    (hWdai : ∀ b, W b → b.getCode ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr = Dai.code ∧
      Dai.PullFits (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr) sevm.caller
        sevm.currentTarget sevm.currentTarget (exDx sevm))
    (hWdai' : ∀ b d, W b → CoinLeaves ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr
        (Dai.moveStor (Dai.spendStor (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr)
          sevm.caller sevm.currentTarget (exDx sevm)) sevm.caller sevm.currentTarget (exDx sevm))
      ((getOrigAcct sevm ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr).stor =
          b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr ∧
        ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr ∉ b.createdAccounts ∧
        Dai.allowSlot sevm.caller sevm.currentTarget ≠ Dai.balSlot sevm.caller ∧
        Dai.allowSlot sevm.caller sevm.currentTarget ≠ Dai.balSlot sevm.currentTarget ∧
        Dai.balSlot sevm.caller ≠ Dai.balSlot sevm.currentTarget) b d → W' d)
    (hWusdc : ∀ b, W' b → b.getCode ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr = Usdc.Proxy.code ∧
      ProxyAt sevm b ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr Usdc.Impl.code ∧
      Blanc.Composition.UsdcLive.MoveFits (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr)
        sevm.currentTarget sevm.caller (Nat.toB256 (exPushAmt o)))
    (hWusdc' : ∀ b d, W' b → CoinLeaves ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr
        (Usdc.creditStor (Usdc.debitStor (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr)
          sevm.currentTarget (Nat.toB256 (exPushAmt o)).toNat) sevm.caller (Nat.toB256 (exPushAmt o)).toNat)
      ((getOrigAcct sevm ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr).stor =
          b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr ∧
        ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr ∉ b.createdAccounts ∧
        Usdc.balSlot sevm.currentTarget ≠ Usdc.balSlot sevm.caller) b d → W'' d)
    (hG : costExchange sevm pre s (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i j
      (exDx sevm).toNat + 4 * 95000 ≤ G)
    (hGm : (St pre [] Mem.empty G).gasMeasure < 2 ^ 256) :
    ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ bp bq,
      pullIn (exEnv sevm i j bp bq) i (exDx sevm).toNat =
        pullIn (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i (exDx sevm).toNat ∧
      RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (exEnv sevm i j bp bq) o ∧
        Checkpoint (post.getStor sevm.currentTarget) o.state ∧ W'' post :=
  exchange_live (U := 95000) hcode hfork hstatic (by omega) hlen hcd hsel hi hj hck hstep hcoin hpc hid
    hkeep hWc hW'c hWb (fun h => absurd h hfee)
    (Blanc.Composition.Curve3PoolDai.dai_coinPullOkAt hfork hstatic (by omega) (hcoin i) hi1 (le_refl _)
      (by decide) (by decide) hWdai hWdai')
    hW''c
    (Blanc.Composition.Curve3PoolUsdc22.usdc22_coinPushOkAt hfork hstatic hdepth (hcoin j) hj1 (by decide)
      (by decide) (by decide) hWusdc hWusdc')
    hG hGm

end Blanc.Composition.Curve3PoolCoinExchange
