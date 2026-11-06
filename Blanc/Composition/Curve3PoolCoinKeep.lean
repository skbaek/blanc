import Blanc.Composition.Curve3Pool3CrvExRoot
import Blanc.Lift.StaticOnlyKeep
import Blanc.Lift.Curve3Pool.FrameEnv

/-!
# The pool's keep premises from what its coin children keep

`ChildKeepsAt`: a pool frame's direct committed children at one address keep the foreign world. Code
that keeps the foreign world (`KeepsForeign`) gives it at any address holding that code, and over the
three coins it gives the pool's keep premises:

* `poolCoinCallsKeepToken_of_children`: every coin child keeps the token (any entry);
* `exchange_keeps_of_children`: every child of an `exchange` frame is at a coin and keeps the pool's
  storage and the code at `4`, by the entry's walk (`xa_exchange`).

Nothing here names a coin; the coins are `ChildKeepsAt` premises, so one per coin can come from a
different route.
-/

namespace Blanc.Composition.Curve3PoolCoinKeep

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3Pool3CrvInstance

variable {sevm : Sevm} {b post : Devm}

/-- **The frame's direct committed children at `t` keep the foreign world**: the storage of every
other address holding code at the frame's entry, and the code of every other address. -/
def ChildKeepsAt (exc : Exec 0 sevm b (.ok post)) (t : Adr) : Prop :=
  ∀ c ∈ Exec.childFrames exc, c.sevm.currentTarget = t → ∀ a, t ≠ a →
    ((b.getCode a).toList ≠ [] → ∀ x, (c.post.getStor a).get x = (c.pre.getStor a).get x) ∧
      c.post.getCode a = c.pre.getCode a

/-- A pool frame's children at an address holding foreign-keeping undelegated code keep the foreign
world. -/
theorem childKeepsAt_of_keepsForeign (hcode : sevm.code = Curve3Pool.code)
    (hfork : CoveredFork sevm.benvStat.fork) (exc : Exec 0 sevm b (.ok post)) {C : ByteArray} {t : Adr}
    (hK : KeepsForeign C) (hne : C.toList ≠ []) (hnd : ¬ isValidDelegation C)
    (htc : b.getCode t = C) : ChildKeepsAt exc t := by
  intro c hc ht a hta
  obtain ⟨cfork, cpre, ccode⟩ := Exec.childFrames_code exc hfork (exRoot_callKinds hcode exc) c hc
  have hcc : c.sevm.code = C := by
    rw [ccode t (by rw [htc]; exact hne) (by rw [htc]; exact hnd) ht, htc]
  obtain ⟨hst, hcd⟩ := hK c (Exec.childFrames_pc exc c hc) hcc cfork (a := a) (by rw [ht]; exact hta.symm)
  exact ⟨fun hna => hst (by rw [cpre a hna]; exact hna), hcd⟩

/-- **Every coin child keeps the token**, when each coin's children keep the foreign world and the
token holds code at the frame's entry. -/
theorem poolCoinCallsKeepToken_of_children (exc : Exec 0 sevm b (.ok post))
    (hcoins : ∀ k, ChildKeepsAt exc (coinAdr ⟨0, sevm, b, .ok post, exc⟩ k))
    (htok : (b.getCode (tokenAdr ⟨0, sevm, b, .ok post, exc⟩)).toList ≠ []) :
    PoolCoinCallsKeepToken ⟨0, sevm, b, .ok post, exc⟩ := by
  rintro c hc ⟨k, hk⟩ hct x
  exact (hcoins k c hc hk _ (fun e => hct (hk.trans e))).1 htok x

/-- **Every direct committed child of an `exchange` frame is at a coin, and keeps the pool's storage
and the code at `4`**, when each coin's children keep the foreign world. -/
theorem exchange_keeps_of_children {s : Curve3Pool.State} (exc : Exec 0 sevm b (.ok post))
    (hcode : sevm.code = Curve3Pool.code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (hcoinPre : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp (exCoin sevm b k))
    (hpool : b.getCode sevm.currentTarget = Curve3Pool.code) (hid : IdReady sevm b)
    (hstack : b.stack = []) (hmem : b.memory = Mem.empty) (hgas : b.gasMeasure < 2 ^ 256)
    (hcoins : ∀ k : Fin 3, ChildKeepsAt exc (exCoin sevm b k) ∧
      exCoin sevm b k ≠ sevm.currentTarget ∧ exCoin sevm b k ≠ 4) :
    (∀ c ∈ Exec.childFrames exc, ExCoinChild sevm b c) ∧
      PoolCallsKeep ⟨0, sevm, b, .ok post, exc⟩ ∧
      ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4 := by
  have hpne : (b.getCode sevm.currentTarget).toList ≠ [] := by rw [hpool]; exact pool_code_ne
  have keeps : ∀ c ∈ Exec.childFrames exc, ExCoinChild sevm b c →
      (∀ x, (c.post.getStor sevm.currentTarget).get x = (c.pre.getStor sevm.currentTarget).get x) ∧
        c.post.getCode 4 = c.pre.getCode 4 := by
    intro c hc ⟨k, hk⟩
    obtain ⟨h1, h2, h3⟩ := hcoins k
    exact ⟨(h1 c hc hk _ h2).1 hpne, (h1 c hc hk _ h3).2⟩
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
  obtain ⟨-, -, -, hi3, hj3, x0, x1, x2, -, Lp, cp, cq, D, y, amp, hL, hcpm, hpt, -, -, -, -,
    hpull, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hqt, -⟩ :=
    xa_exchange hcode hfork hlen hcd hsel rfl ha hci hcj hpc hid
      (fun c hc hk => (keeps c hc hk).1) (fun c hc hk => (keeps c hc hk).2)
      (XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas))
  have coin : ∀ c ∈ Exec.childFrames exc, ExCoinChild sevm b c := by
    intro c hc
    rw [hL] at hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases hpull with ⟨-, rfl, -⟩ | ⟨-, c1, c2, rfl, hb1, hb2, -⟩
      · rw [List.mem_singleton] at hc
        subst hc
        exact exCoinChild_of hi3 hpt
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl
        · exact exCoinChild_of hi3 hb1.target
        · exact exCoinChild_of hi3 hpt
        · exact exCoinChild_of hi3 hb2.target
    · rw [List.mem_singleton] at hc
      subst hc
      exact exCoinChild_of hj3 hqt
  exact ⟨coin, fun c hc => (keeps c hc (coin c hc)).1, fun c hc => (keeps c hc (coin c hc)).2⟩

end Blanc.Composition.Curve3PoolCoinKeep
