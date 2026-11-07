import Blanc.Composition.Curve3PoolDaiCoin
import Blanc.Composition.Curve3PoolUsdtCoin
import Blanc.Composition.Curve3PoolCoinKeep
import Blanc.Lift.Curve3Pool.ExchangeLive

/-!
# `exchange_live` with USDT on one side

`exchange_dai_usdt_live` pushes USDT, `exchange_usdt_dai_live` pulls it, both with DAI opposite and both
coin calls run from the certified runtimes, at the window `U = 104744` and `U = 129555`. The keep premise
is the three coins' bytes (`PoolCoinWorld`); what remains of USDT is the owner's gates and the ledger's fits
on the world invariants. `exchange_live`'s model credits the pull with what the fee coin's balance reads
say arrived (`exBalOpt`), so a nonzero USDT fee appears in the premises `B1`, `B2`, not in a mismatch.
-/

namespace Blanc.Composition.Curve3PoolUsdtExchange

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Composition.Curve3Pool3CrvInstance (CoinLeaves)

/-- **An `exchange` frame from DAI to USDT is live**, with both coin calls run from
their certified bytes. -/
theorem exchange_dai_usdt_live {sevm : Sevm} {pre : Devm} {s : Curve3Pool.State} {o : Out} {i j : Fin 3}
    {B1 B2 : B256} {W W' W'' : Devm → Prop} {G : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange)
    (hi : i.val = (exI sevm).toNat) (hj : j.val = (exJ sevm).toNat)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (hstep : step s (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) (decodeCall sevm) = some o)
    (hcoin : ∀ k : Fin 3,
      ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre)
    {dai usdc usdt : Adr} (hpool : pre.getCode sevm.currentTarget = code)
    (hworld : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
      Curve3PoolCoinKeep.PoolCoinWorld exc dai usdc usdt)
    (hparties : ∀ k : Fin 3,
      (((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr = dai ∨
        ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr = usdc ∨
        ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr = usdt) ∧
      ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr ≠ sevm.currentTarget ∧
      ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr ≠ 4)
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
    (hWusdt : ∀ b, W' b → b.getCode ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr = Usdt.code ∧
      Usdt.NotDeprecated (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr) ∧
      Usdt.XferFits (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr)
        sevm.currentTarget sevm.caller (Nat.toB256 (exPushAmt o)))
    (hWusdt' : ∀ b d, W' b → CoinLeaves ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr
        (Usdt.moveStor (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr)
          sevm.currentTarget sevm.caller (Nat.toB256 (exPushAmt o))
          (Usdt.feeOf (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr) (Nat.toB256 (exPushAmt o))))
      ((getOrigAcct sevm ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr).stor =
          b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr ∧
        ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr ∉ b.createdAccounts ∧
        Usdt.MoveApart (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr)
          sevm.currentTarget sevm.caller (Nat.toB256 (exPushAmt o))
          (Usdt.feeOf (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr) (Nat.toB256 (exPushAmt o)))) b d → W'' d)
    (hG : costExchange sevm pre s (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i j
      (exDx sevm).toNat + 4 * 104744 ≤ G)
    (hGm : (St pre [] Mem.empty G).gasMeasure < 2 ^ 256) :
    ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ bp bq,
      pullIn (exEnv sevm i j bp bq) i (exDx sevm).toNat =
        pullIn (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i (exDx sevm).toNat ∧
      RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (exEnv sevm i j bp bq) o ∧
        Checkpoint (post.getStor sevm.currentTarget) o.state ∧ W'' post :=
  exchange_live (U := 104744) hcode hfork hstatic hdepth hlen hcd hsel hi hj hck hstep hcoin hpc hid
    (fun post exc => (Curve3PoolCoinKeep.exchange_keeps_of_children exc hcode hfork.histFork hlen hcd hsel
      (St_getStor pre [] Mem.empty G sevm.currentTarget ▸ hck.abs) hcoin
      (by rw [St_getCode]; exact hpool)
      ⟨(St_getCode pre [] Mem.empty G 4) ▸ hid.toH.nodeleg, hid.toH.warm, hid.toH.pre, hid.toH.stateGas⟩
      rfl rfl hGm fun k => ⟨by
        have e : Curve3Pool3CrvInstance.exCoin sevm (St pre [] Mem.empty G) k =
            ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr := by
          simp only [Curve3Pool3CrvInstance.exCoin, St_getStor]
        obtain ⟨h | h | h, -⟩ := hparties k <;> rw [e, h]
        · exact (hworld post exc).dai_keeps hcode hfork.histFork
        · exact (hworld post exc).usdc_keeps hcode hfork.histFork
        · exact (hworld post exc).usdt_keeps hcode hfork.histFork, (hparties k).2.1, (hparties k).2.2⟩).2) hWc hW'c hWb (fun h => absurd h hfee)
    (Blanc.Composition.Curve3PoolDai.dai_coinPullOkAt hfork hstatic hdepth (hcoin i) hi1 (by decide)
      (by decide) (by decide) hWdai hWdai')
    hW''c
    (Blanc.Composition.Curve3PoolUsdt.usdt_coinPushOkAt hfork hstatic hdepth (hcoin j) hj1 (le_refl _)
      (by decide) (by decide) hWusdt hWusdt')
    hG hGm


/-- **An `exchange` frame from USDT to DAI is live**, whichever index USDT holds: for the fee coin the pool reads its balance around the pull, and `B1`, `B2` are USDT's answers, with both coin calls run from
their certified bytes. -/
theorem exchange_usdt_dai_live {sevm : Sevm} {pre : Devm} {s : Curve3Pool.State} {o : Out} {i j : Fin 3}
    {B1 B2 : B256} {W W' W'' : Devm → Prop} {G : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange)
    (hi : i.val = (exI sevm).toNat) (hj : j.val = (exJ sevm).toNat)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (hstep : step s (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) (decodeCall sevm) = some o)
    (hcoin : ∀ k : Fin 3,
      ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre)
    {dai usdc usdt : Adr} (hpool : pre.getCode sevm.currentTarget = code)
    (hworld : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
      Curve3PoolCoinKeep.PoolCoinWorld exc dai usdc usdt)
    (hparties : ∀ k : Fin 3,
      (((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr = dai ∨
        ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr = usdc ∨
        ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr = usdt) ∧
      ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr ≠ sevm.currentTarget ∧
      ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr ≠ 4)
    (hWc : WClosed sevm W) (hW'c : WClosed sevm W') (hWb : W pre)
    (hW''c : WClosed sevm W'')
    (hi1 : ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr ≠ sevm.currentTarget)
    (hj1 : ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr ≠ sevm.currentTarget)
    (hbal1 : i = feeIndex → ∀ b, W b →
      b.getCode ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr = Usdt.code ∧
      Usdt.NotDeprecated (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr) ∧
      (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr).get (Usdt.balSlot sevm.currentTarget) = B1)
    (hbal2 : i = feeIndex → ∀ b, W' b →
      b.getCode ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr = Usdt.code ∧
      Usdt.NotDeprecated (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr) ∧
      (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr).get (Usdt.balSlot sevm.currentTarget) = B2)
    (hstat : ∀ b d, W b → (∀ a, Devm.getStor d a = Devm.getStor b a) → (∀ a, d.getCode a = b.getCode a) → W d)
    (hstat' : ∀ b d, W' b → (∀ a, Devm.getStor d a = Devm.getStor b a) → (∀ a, d.getCode a = b.getCode a) → W' d)
    (hWusdt : ∀ b, W b → b.getCode ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr = Usdt.code ∧
      Usdt.NotDeprecated (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr) ∧
      Usdt.PullFits (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr) sevm.caller
        sevm.currentTarget sevm.currentTarget (exDx sevm))
    (hWusdt' : ∀ b d, W b → CoinLeaves ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr
        (Usdt.moveStor (Usdt.spendStor (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr)
            sevm.caller sevm.currentTarget (exDx sevm)) sevm.caller sevm.currentTarget (exDx sevm)
          (Usdt.feeOf (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr) (exDx sevm)))
      ((getOrigAcct sevm ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr).stor =
          b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr ∧
        ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr ∉ b.createdAccounts ∧
        Usdt.PullApart (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr) sevm.caller
          sevm.currentTarget sevm.currentTarget (exDx sevm)
          (Usdt.feeOf (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot i)).toAdr) (exDx sevm))) b d → W' d)
    (hWdai : ∀ b, W' b → b.getCode ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr = Dai.code ∧
      Dai.MoveFits (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr)
        sevm.currentTarget sevm.caller (Nat.toB256 (exPushAmt o)))
    (hWdai' : ∀ b d, W' b → CoinLeaves ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr
        (Dai.moveStor (b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr)
          sevm.currentTarget sevm.caller (Nat.toB256 (exPushAmt o)))
      ((getOrigAcct sevm ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr).stor =
          b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr ∧
        ((pre.getStor sevm.currentTarget).get (coinSlot j)).toAdr ∉ b.createdAccounts ∧
        Dai.balSlot sevm.currentTarget ≠ Dai.balSlot sevm.caller) b d → W'' d)
    (hG : costExchange sevm pre s (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i j
      (exDx sevm).toNat + 4 * 129555 ≤ G)
    (hGm : (St pre [] Mem.empty G).gasMeasure < 2 ^ 256) :
    ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ bp bq,
      pullIn (exEnv sevm i j bp bq) i (exDx sevm).toNat =
        pullIn (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i (exDx sevm).toNat ∧
      RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (exEnv sevm i j bp bq) o ∧
        Checkpoint (post.getStor sevm.currentTarget) o.state ∧ W'' post :=
  exchange_live (U := 129555) hcode hfork hstatic hdepth hlen hcd hsel hi hj hck hstep hcoin hpc hid
    (fun post exc => (Curve3PoolCoinKeep.exchange_keeps_of_children exc hcode hfork.histFork hlen hcd hsel
      (St_getStor pre [] Mem.empty G sevm.currentTarget ▸ hck.abs) hcoin
      (by rw [St_getCode]; exact hpool)
      ⟨(St_getCode pre [] Mem.empty G 4) ▸ hid.toH.nodeleg, hid.toH.warm, hid.toH.pre, hid.toH.stateGas⟩
      rfl rfl hGm fun k => ⟨by
        have e : Curve3Pool3CrvInstance.exCoin sevm (St pre [] Mem.empty G) k =
            ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr := by
          simp only [Curve3Pool3CrvInstance.exCoin, St_getStor]
        obtain ⟨h | h | h, -⟩ := hparties k <;> rw [e, h]
        · exact (hworld post exc).dai_keeps hcode hfork.histFork
        · exact (hworld post exc).usdc_keeps hcode hfork.histFork
        · exact (hworld post exc).usdt_keeps hcode hfork.histFork, (hparties k).2.1, (hparties k).2.2⟩).2) hWc hW'c hWb
    (fun h => ⟨Blanc.Composition.Curve3PoolUsdt.usdt_coinBalOkAt hfork hdepth (hcoin i) (by decide) (by decide) (by decide)
        (hbal1 h) hstat,
      Blanc.Composition.Curve3PoolUsdt.usdt_coinBalOkAt hfork hdepth (hcoin i) (by decide) (by decide) (by decide)
        (hbal2 h) hstat'⟩)
    (Blanc.Composition.Curve3PoolUsdt.usdt_coinPullOkAt hfork hstatic hdepth (hcoin i) hi1 (le_refl _)
      (by decide) (by decide) hWusdt hWusdt')
    hW''c
    (Blanc.Composition.Curve3PoolDai.dai_coinPushOkAt hfork hstatic hdepth (hcoin j) hj1 (by decide)
      (by decide) (by decide) hWdai hWdai')
    hG hGm


end Blanc.Composition.Curve3PoolUsdtExchange
