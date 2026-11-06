import Blanc.Composition.Curve3Pool3CrvExRoot
import Blanc.Lift.CurveCoins.Keep
import Blanc.ExecutionDirectCode
import Blanc.Lift.TargetLogEvents
import Blanc.Lift.Curve3Pool.FrameEnv

/-!
# The pool's keep premises from the coins' bytes

What the deployed coins give a pool frame's keep premises, over the historical forks.

* `poolChild_facts`: what a committed child of a pool frame runs and sees;
* `ChildKeepsSel`: the frame's committed children at `t`, on the selectors the pool sends coins, keep the
  foreign world. `PoolCoinWorld` states how each coin enters: its deployed bytes at the frame's entry, and the
  named operator premises: USDC's implementation word names one of the three versions, USDT's `deprecated`
  flag is clear, each at the child's entry;
* `exchange_keeps_of_world`: every committed child of an `exchange` frame is at a coin on such a selector, and
  keeps the pool's storage, the code at `4` and, when it holds code, the token's storage. The walk exposes
  each child's target and calldata before it needs that child's keep (`ExCoinSel`).
-/

namespace Blanc.Composition.Curve3PoolCoinKeep

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.Lift.CurveCoins
open Blanc.Composition.Curve3Pool3CrvInstance

variable {sevm : Sevm} {b post : Devm}

/-- **What a committed child of a pool frame runs and sees.** No fork premise beyond no state gas. -/
theorem poolChild_facts (hcode : sevm.code = Curve3Pool.code)
    (hsg : sevm.benvStat.rules.stateGas = none) (exc : Exec 0 sevm b (.ok post)) :
    ∀ c ∈ Exec.childFrames exc, c.pc = 0 ∧ c.sevm.benvStat = sevm.benvStat ∧
      c.sevm.data.length < 2 ^ 256 ∧
      (∀ a, (b.getCode a).toList ≠ [] → c.pre.getCode a = b.getCode a) ∧
      ∀ a, (b.getCode a).toList ≠ [] → ¬ isValidDelegation (b.getCode a) →
        c.sevm.currentTarget = a → c.sevm.code = b.getCode a := by
  intro c hc
  obtain ⟨N, f, rsm, pc', cevm, pp, hstep, henter, hsevm, hpre⟩ :=
    Exec.childFrames_spawnedAt_entry exc (.refl _) c hc
  have hNs : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq pp
  have hNc : ∀ a, (b.getCode a).toList ≠ [] → N.devm.getCode a = b.getCode a :=
    fun a hne => Exec.Deriv.ParentPrefix.codePreserve pp a hne
  obtain ⟨x, hxat, hxs, -⟩ := Evm.step_spawn_inv hstep
  obtain ⟨-, pc0, -, stat, hdata⟩ :=
    Xinst.spawn_child_world_noStateGas (hNs ▸ hsg) hxs henter
  obtain ⟨benv, -, hcevm⟩ := Frame.enter_run_inv henter
  refine ⟨Exec.childFrames_pc exc c hc, by rw [hsevm, stat, hNs], by rw [hsevm]; exact hdata,
    fun a hne => ?_, fun a hne hnd ht => ?_⟩
  · rw [hpre, Frame.enter_run_getCode henter a, Xinst.step_spawn_getCode hxs a, hNc a hne]
  · have htf : f.inner.currentTarget = a := by
      rw [← ht, hsevm, hcevm]; rfl
    have hcf : c.sevm.code = f.inner.code := by
      rw [hsevm, hcevm]; rfl
    have hnd' : ¬ isValidDelegation (N.devm.getCode f.inner.currentTarget) := by
      rw [htf, hNc a hne]; exact hnd
    rw [hcf, Xinst.step_directCall_spawn_code
      (exRoot_callKinds hcode exc N pp x (by rw [hNs] at hxat ⊢; exact hxat)) hxs hnd', htf, hNc a hne]

/-- **The frame's committed children at `t` on the pool's selectors keep the foreign world.** -/
def ChildKeepsSel (exc : Exec 0 sevm b (.ok post)) (t : Adr) : Prop :=
  ∀ c ∈ Exec.childFrames exc, c.sevm.currentTarget = t → PoolCoinSel (Blanc.Sevm.selector c.sevm) →
    ∀ a, t ≠ a →
      ((b.getCode a).toList ≠ [] → ∀ x, (c.post.getStor a).get x = (c.pre.getStor a).get x) ∧
        c.post.getCode a = c.pre.getCode a

/-- How a frame's coins enter its keep premises: deployed bytes at the entry, and the named operator
premises at each child's entry. -/
structure PoolCoinWorld (exc : Exec 0 sevm b (.ok post)) (dai usdc usdt : Adr) : Prop where
  daiCode : b.getCode dai = Dai.code
  usdcCode : b.getCode usdc = Usdc.Proxy.code
  usdtCode : b.getCode usdt = Usdt.code
  /-- Circle's proxy admin: USDC's implementation word names one of the three versions. -/
  usdcImpl : ∀ c ∈ Exec.childFrames exc, c.sevm.currentTarget = usdc → UsdcImplAt c.pre usdc
  /-- Tether's owner: USDT is not deprecated. -/
  usdtLive : ∀ c ∈ Exec.childFrames exc, c.sevm.currentTarget = usdt →
    Usdt.flag20 ((Devm.getStor c.pre usdt).get 10) = 0

section World

variable {exc : Exec 0 sevm b (.ok post)} {dai usdc usdt : Adr}

private theorem keeps_of_frame (hcode : sevm.code = Curve3Pool.code)
    (hfork : HistFork sevm.benvStat.fork) {t : Adr} {c : Exec.Frame} (hc : c ∈ Exec.childFrames exc)
    (ht : c.sevm.currentTarget = t) (hk : FrameKeepsForeign c) (a : Adr) (hne : t ≠ a) :
    ((b.getCode a).toList ≠ [] → ∀ x, (c.post.getStor a).get x = (c.pre.getStor a).get x) ∧
      c.post.getCode a = c.pre.getCode a := by
  obtain ⟨-, -, -, cpre, -⟩ := poolChild_facts hcode hfork.stateGas_none exc c hc
  obtain ⟨hst, hcd⟩ := hk (a := a) (by rw [ht]; exact hne.symm)
  exact ⟨fun hna => hst (by rw [cpre a hna]; exact hna), hcd⟩

private theorem code_of_bytes {C : ByteArray} (hne : C.toList ≠ []) (hnd : ¬ isValidDelegation C)
    (hcode : sevm.code = Curve3Pool.code) (hfork : HistFork sevm.benvStat.fork) {t : Adr}
    (htc : b.getCode t = C) {c : Exec.Frame} (hc : c ∈ Exec.childFrames exc)
    (ht : c.sevm.currentTarget = t) : c.sevm.code = C := by
  obtain ⟨-, -, -, -, ccode⟩ := poolChild_facts hcode hfork.stateGas_none exc c hc
  rw [ccode t (by rw [htc]; exact hne) (by rw [htc]; exact hnd) ht, htc]

theorem PoolCoinWorld.dai_keeps (w : PoolCoinWorld exc dai usdc usdt)
    (hcode : sevm.code = Curve3Pool.code) (hfork : HistFork sevm.benvStat.fork) :
    ChildKeepsSel exc dai := by
  intro c hc ht sel a hne
  obtain ⟨pc0, stat, -, -, -⟩ := poolChild_facts hcode hfork.stateGas_none exc c hc
  refine keeps_of_frame hcode hfork hc ht
    (dai_frameKeeps c pc0 (code_of_bytes (by decide +kernel) (by decide +kernel) hcode hfork w.daiCode hc ht)
      (by rw [stat]; exact hfork.stateGas_none) sel) a hne

theorem PoolCoinWorld.usdt_keeps (w : PoolCoinWorld exc dai usdc usdt)
    (hcode : sevm.code = Curve3Pool.code) (hfork : HistFork sevm.benvStat.fork) :
    ChildKeepsSel exc usdt := by
  intro c hc ht sel a hne
  obtain ⟨pc0, stat, -, -, -⟩ := poolChild_facts hcode hfork.stateGas_none exc c hc
  refine keeps_of_frame hcode hfork hc ht
    (usdt_frameKeeps c pc0 (code_of_bytes (by decide +kernel) (by decide +kernel) hcode hfork w.usdtCode hc ht)
      (by rw [stat]; exact hfork.stateGas_none) (by rw [stat]; exact hfork.bal_none)
      (by rw [ht]; exact w.usdtLive c hc ht) sel) a hne

theorem PoolCoinWorld.usdc_keeps (w : PoolCoinWorld exc dai usdc usdt)
    (hcode : sevm.code = Curve3Pool.code) (hfork : HistFork sevm.benvStat.fork) :
    ChildKeepsSel exc usdc := by
  intro c hc ht sel a hne
  obtain ⟨pc0, stat, hsize, -, -⟩ := poolChild_facts hcode hfork.stateGas_none exc c hc
  refine keeps_of_frame hcode hfork hc ht
    (usdc_frameKeeps c pc0 (code_of_bytes (by decide +kernel) (by decide +kernel) hcode hfork w.usdcCode hc ht)
      (by rw [stat]; exact hfork.stateGas_none) (by rw [stat]; exact hfork.bal_none) hsize
      (by rw [ht]; exact w.usdcImpl c hc ht) sel) a hne

end World

/-- **Every direct committed child of an `exchange` frame is at a coin on the pool's selectors, and keeps the
pool's storage, the code at `4`, and the token's storage if the token holds code** (the coin world names the
keeps; the walk `xa_exchange` exposes each child). `exCoin k` are the coins at entry. -/
theorem exchange_keeps_of_children {s : Curve3Pool.State} (exc : Exec 0 sevm b (.ok post))
    (hcode : sevm.code = Curve3Pool.code) (hfork : HistFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (hcoinPre : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp (exCoin sevm b k))
    (hpool : b.getCode sevm.currentTarget = Curve3Pool.code) (hid : IdReadyH sevm b)
    (hstack : b.stack = []) (hmem : b.memory = Mem.empty) (hgas : b.gasMeasure < 2 ^ 256)
    (hcoins : ∀ k : Fin 3, ChildKeepsSel exc (exCoin sevm b k) ∧
      exCoin sevm b k ≠ sevm.currentTarget ∧ exCoin sevm b k ≠ 4) :
    (∀ c ∈ Exec.childFrames exc, ExCoinSel sevm b c) ∧
      PoolCallsKeep ⟨0, sevm, b, .ok post, exc⟩ ∧
      ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4 := by
  have hpne : (b.getCode sevm.currentTarget).toList ≠ [] := by rw [hpool]; exact pool_code_ne
  have keeps : ∀ c ∈ Exec.childFrames exc, ExCoinSel sevm b c →
      (∀ x, (c.post.getStor sevm.currentTarget).get x = (c.pre.getStor sevm.currentTarget).get x) ∧
        c.post.getCode 4 = c.pre.getCode 4 := by
    intro c hc ⟨⟨k, hk⟩, hs⟩
    obtain ⟨h1, h2, h3⟩ := hcoins k
    exact ⟨(h1 c hc hk hs _ h2).1 hpne, (h1 c hc hk hs _ h3).2⟩
  have hpc : b.getCode sevm.currentTarget ≠ .empty := by
    intro h
    rw [h, ByteArray.toList_eq_toList_data] at hpne
    exact hpne rfl
  have hci : (exI sevm).toNat < 3 → ¬ sevm.benvStat.rules.isPrecomp
      ((b.getStor sevm.currentTarget).get (coinsBase + exI sevm)).toAdr := fun hi => by
    simpa only [exCoin, coinSlot, toB256_toNat] using hcoinPre ⟨_, hi⟩
  have hcj : (exJ sevm).toNat < 3 → ¬ sevm.benvStat.rules.isPrecomp
      ((b.getStor sevm.currentTarget).get (coinsBase + exJ sevm)).toAdr := fun hj => by
    simpa only [exCoin, coinSlot, toB256_toNat] using hcoinPre ⟨_, hj⟩
  obtain ⟨-, -, -, hi3, hj3, x0, x1, x2, -, Lp, cp, cq, D, y, amp, hL, hcpm, hpt, hpd, -, -, -,
    hpull, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hqt, hqd, -⟩ :=
    xa_exchange hcode hfork hlen hcd hsel rfl ha hci hcj hpc hid
      (fun c hc hk => (keeps c hc hk).1) (fun c hc hk => (keeps c hc hk).2)
      (XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas))
  have coin : ∀ c ∈ Exec.childFrames exc, ExCoinSel sevm b c := by
    intro c hc
    rw [hL] at hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases hpull with ⟨-, rfl, -⟩ | ⟨-, c1, c2, rfl, hb1, hb2, -⟩
      · rw [List.mem_singleton] at hc
        subst hc
        exact ⟨exCoinChild_of hi3 hpt, poolCoinSel_transferFrom hpd⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl
        · exact ⟨exCoinChild_of hi3 hb1.target, poolCoinSel_balanceOf hb1.data⟩
        · exact ⟨exCoinChild_of hi3 hpt, poolCoinSel_transferFrom hpd⟩
        · exact ⟨exCoinChild_of hi3 hb2.target, poolCoinSel_balanceOf hb2.data⟩
    · rw [List.mem_singleton] at hc
      subst hc
      exact ⟨exCoinChild_of hj3 hqt, poolCoinSel_transfer hqd⟩
  exact ⟨coin, fun c hc => (keeps c hc (coin c hc)).1, fun c hc => (keeps c hc (coin c hc)).2⟩

/-- **Every coin child keeps the token**, for a frame all of whose children at coins are on the pool's
selectors, when the token holds code at the frame's entry. -/
theorem poolCoinCallsKeepToken_of_sel (exc : Exec 0 sevm b (.ok post))
    (hcoins : ∀ k, ChildKeepsSel exc (coinAdr ⟨0, sevm, b, .ok post, exc⟩ k))
    (hsel : ∀ c ∈ Exec.childFrames exc, (∃ k, c.sevm.currentTarget = coinAdr ⟨0, sevm, b, .ok post, exc⟩ k) →
      PoolCoinSel (Blanc.Sevm.selector c.sevm))
    (htok : (b.getCode (tokenAdr ⟨0, sevm, b, .ok post, exc⟩)).toList ≠ []) :
    PoolCoinCallsKeepToken ⟨0, sevm, b, .ok post, exc⟩ := by
  rintro c hc ⟨k, hk⟩ hct x
  exact (hcoins k c hc hk (hsel c hc ⟨k, hk⟩) _ (fun e => hct (hk.trans e))).1 htok x

end Blanc.Composition.Curve3PoolCoinKeep
