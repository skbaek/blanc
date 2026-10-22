import Blanc.Composition.Curve3Pool3CrvCoinAnswers
import Blanc.Composition.Curve3Pool3CrvCapstoneModel
import Blanc.Lift.Curve3Pool.ExchangeLive
import Blanc.Composition.Curve3Pool3CrvTxFrame

/-!
# U9(b): the `exchange` frame runs — `exchange_live` instantiated

At the transaction's entry machine (`ExFrame`), `exchange_live` applies with every premise
discharged: the model step is kernel-evaluated (`ex_step`), the coins' `transferFrom`/`transfer`
answers come from `Token20`'s code (`wPull_pullOkAt`, `wPush_pushOkAt`: `token20_coinPullOkAt`,
`token20_coinPushOkAt` over the invariants `WPull`, `WPush`, `WCore`), the children keep what the pool's walk needs (`exFrame_children`), and the gas
is within the frame's `878400` (`ex_cost`: `costExchange ≤ 218685`, plus four calls at `80000`).

`ex_frame_live` is the end-to-end non-vacuity witness of `exchange_live`: an actual successful
execution of the pool's runtime whose effect is the model's `exchange(0, 1, 100, 0)`.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.StableSwapNewton
open Blanc.Composition.Curve3Pool3CrvJoint

/-- The trader as the model reads `msg.sender`. -/
abbrev traderN : Nat := trader.toB256.toNat

/-- **The model's output of the swap**. -/
def exOut : Out :=
  ⟨poolState1, none, [.tokenExchange traderN 0 100 1 132], [.pull 0 traderN 100, .push 1 traderN 132]⟩

/-- `get_y`'s charge past `_A`. -/
def gyTail (amp i j x x0 x1 x2 : Nat) : Nat :=
  match getDChk (V3.mk x0 x1 x2).get amp 1, chkMul amp 3 with
  | some D, some ann => costGetD x0 x1 x2 amp + gyCostFrom0 i j x x0 x1 x2 D ann (D, 0)
  | _, _ => 0

theorem costGetY_split (sevm : Sevm) (b : Devm) (amp i j x x0 x1 x2 : Nat) :
    costGetY sevm b amp i j x x0 x1 x2 = 2100 + aGas sevm b + gyTail amp i j x x0 x1 x2 := rfl

theorem gyTail_ex : gyTail 100 0 1 1100 1000 2000000000000000 3000000000000000 = 44869 := by
  decide +kernel

section Frame

variable {sevm : Sevm} {b : Devm} (hf : Curve3Pool3CrvInstance.ExFrame sevm b)
include hf

theorem exFrame_exI : (exI sevm).toNat = 0 := by
  unfold exI Sevm.dataWord; rw [hf.data]; decide +kernel

theorem exFrame_exJ : (exJ sevm).toNat = 1 := by
  unfold exJ Sevm.dataWord; rw [hf.data]; decide +kernel

theorem exFrame_exDx : exDx sevm = Nat.toB256 exchangeDx := by
  unfold exDx Sevm.dataWord; rw [hf.data]; decide +kernel

theorem exFrame_decode : decodeCall sevm = .exchange 0 1 100 0 := by
  have hm : (exMinDy sevm).toNat = 0 := by
    unfold exMinDy Sevm.dataWord; rw [hf.data]; decide +kernel
  rw [ex_decode (exFrame_len hf).1 (exFrame_sel hf), exFrame_exI hf, exFrame_exJ hf,
    exFrame_exDx hf, hm]
  rfl

/-- **The model step at the frame's environment** (kernel evaluation). -/
theorem ex_step :
    step poolState (exEnv sevm 0 1 (exBalOpt 0 0) (exBalOpt 0 0)) (decodeCall sevm) =
      some exOut := by
  rw [exFrame_decode hf]
  unfold exEnv
  rw [hf.time, hf.caller, hf.value]
  decide +kernel

omit hf in
/-- **The frame's sufficient gas** is at most `218685`. -/
theorem ex_cost :
    costExchange sevm b poolState (exEnv sevm 0 1 (exBalOpt 0 0) (exBalOpt 0 0)) 0 1 100 ≤
      218685 := by
  have hxp : xpChk poolState.balances = some ⟨1000, 2000000000000000, 3000000000000000⟩ := by
    decide +kernel
  have hpi : pullIn (exEnv sevm 0 1 (exBalOpt 0 0) (exBalOpt 0 0)) 0 100 = some 100 := rfl
  have hA := poolState_aChk (exEnv sevm 0 1 (exBalOpt 0 0) (exBalOpt 0 0)).time
  unfold costExchange
  rw [hxp, hpi, hA]
  show costGetY sevm b 100 0 1 1100 1000 2000000000000000 3000000000000000 + 8858 + 154000 ≤ _
  rw [costGetY_split, gyTail_ex]
  have := aGas_le sevm b
  omega

/-- The core invariant at the frame's entry: no error, nothing created, refund `0`, and every pool
slot at its snapshot value (so none cleared). -/
theorem exFrame_core : WCore sevm b := by
  refine ⟨hf.error, hf.createdPool, hf.createdCoin0, hf.createdCoin1, ?_⟩
  have hz : clearedCount sevm b poolAddr poolKeys = 0 := clearedCount_eq_zero fun x _ => by
    unfold Devm.getOrigStorVal
    rw [ite_eq_right hf.createdPool]
    unfold Jaune.getOrigStorVal
    rw [hf.origPool]
    change poolStor.get x = (b.state.getStor poolAddr).get x
    rw [hf.poolStor]
  unfold refundPotential
  rw [hz, hf.refund, Nat.cast_zero, Int.mul_zero]
  exact Int.le_refl 0

/-- **`exchange_live` at the closed instance's frame**: an actual successful execution of the
pool's runtime from the transaction's entry machine, whose effect is the model's
`exchange(0, 1, 100, 0)` (`exOut`), with the pool's checkpoint at the post. -/
theorem ex_frame_live :
    ∃ post, ∃ exc : Exec 0 sevm b (.ok post), ∃ bp bq,
      pullIn (exEnv sevm 0 1 bp bq) 0 100 =
        pullIn (exEnv sevm 0 1 (exBalOpt 0 0) (exBalOpt 0 0)) 0 100 ∧
      RawEffect ⟨0, sevm, b, .ok post, exc⟩ post (exEnv sevm 0 1 bp bq) exOut ∧
        Checkpoint (post.getStor sevm.currentTarget) exOut.state ∧
        post.error = none ∧ 0 ≤ post.refundCounter := by
  have hb : St b [] Mem.empty 878400 = b := by
    rw [← hf.gas]; exact (St.self hf.stack hf.memory).symm
  have hdx : (exDx sevm).toNat = 100 := by rw [exFrame_exDx hf]; rfl
  have hpre0 : ¬ sevm.benvStat.rules.isPrecomp coin0Addr := by
    have := exFrame_coinPre hf 0; rw [exFrame_coin hf] at this; exact this
  have hpre1 : ¬ sevm.benvStat.rules.isPrecomp coin1Addr := by
    have := exFrame_coinPre hf 1; rw [exFrame_coin hf] at this; exact this
  have L := exchange_live (pre := b) (G := 878400) (s := poolState) (o := exOut) (i := 0) (j := 1)
    (B1 := 0) (B2 := 0) (W := WPull sevm) (W' := WPush sevm) (W'' := WCore sevm) (U := 80000)
    hf.code (exFrame_fork hf) hf.static (by rw [hf.depth]; decide) (exFrame_len hf).1
    (exFrame_len hf).2 (exFrame_sel hf) (exFrame_exI hf).symm (exFrame_exJ hf).symm
    (exFrame_checkpoint hf) (ex_step hf) (exFrame_coinPre hf)
    (by rw [exFrame_poolCode hf]; intro he; have := congrArg ByteArray.size he; revert this
        decide +kernel)
    (exFrame_id hf)
    (by rw [hb]; exact fun post exc => ⟨(exFrame_children hf exc).2.1, (exFrame_children hf exc).2.2⟩)
    (wPull_closed hf.target hf.origPool) (wPush_closed hf.target hf.origPool)
    ⟨hf.coin0Code, hf.coin1Code, hf.coin0Stor, hf.coin1Stor, exFrame_core hf⟩
    (fun h => absurd h (by decide))
    (by rw [exFrame_exDx hf]
        exact wPull_pullOkAt (exFrame_fork hf) hf.static (by rw [hf.depth]; decide) hf.caller
          hf.target hf.origCoin0 hpre0 (exFrame_coin hf 0))
    (wCore_closed hf.target hf.origPool)
    (wPush_pushOkAt (exFrame_fork hf) hf.static (by rw [hf.depth]; decide) hf.caller hf.target
      hf.origCoin1 hpre1 (exFrame_coin hf 1))
    (by rw [hdx]; have := ex_cost (sevm := sevm) (b := b); omega)
    (by rw [hb]; exact exFrame_gas hf)
  rw [hb, hdx] at L
  obtain ⟨post, exc, bp, bq, hp, hr, hc, hcore⟩ := L
  exact ⟨post, exc, bp, bq, hp, hr, hc, hcore.1, refundCounter_nonneg_of_potential hcore.2.2.2.2⟩

end Frame

end Blanc.Composition.Curve3Pool3CrvInstance
