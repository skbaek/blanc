import Blanc.Lift.PoolCoinSel
import Blanc.Lift.Curve3Pool.Walk.Kit

/-!
# The keep a pool walk asks of a child, once it has shown who the child is

A pool walk reaches each child knowing its target and calldata, and only then needs that child's keep. So its
premise can ask only of the children it can name: 3Crv on any selector, and a coin on a selector the pool sends
coins (`PoolChildSel`).

* `ChildKeepsPool`: a child keeps the pool's storage and the code at `4`;
* `KeepSel`: every remaining child that is one of those keeps the pool, at the pool's storage `σ` at entry;
* `KeepCoin`, `KeepTok`: what one call site reads of it.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc Blanc.Lift

/-- A child keeps the calling pool's storage, slot by slot, and the code at `4`. -/
abbrev ChildKeepsPool (sevm : Sevm) (c : Exec.Frame) : Prop :=
  (∀ x, (c.post.getStor sevm.currentTarget).get x = (c.pre.getStor sevm.currentTarget).get x) ∧
    c.post.getCode 4 = c.pre.getCode 4

/-- A child a pool walk names: at the token, or at a coin on a selector the pool sends coins. -/
def PoolChildSel (σ : Stor) (c : Exec.Frame) : Prop :=
  c.sevm.currentTarget = (σ.get tokenSlot).toAdr ∨
    (∃ i, i < 3 ∧ c.sevm.currentTarget = (σ.get (coinsBase + Nat.toB256 i)).toAdr) ∧
      CurveCoins.PoolCoinSel (Sevm.selector c.sevm)

/-- Every remaining child the walk can name keeps the pool. -/
def KeepSel (sevm : Sevm) (σ : Stor) (L : List Exec.Frame) : Prop :=
  ∀ c ∈ L, PoolChildSel σ c → ChildKeepsPool sevm c

/-- Every remaining child at the coin word `C`, on a coin selector, keeps the pool. -/
abbrev KeepCoin (sevm : Sevm) (C : B256) (L : List Exec.Frame) : Prop :=
  ∀ c ∈ L, c.sevm.currentTarget = C.toAdr → CurveCoins.PoolCoinSel (Sevm.selector c.sevm) →
    ChildKeepsPool sevm c

/-- Every remaining child at the token word `T` keeps the pool. -/
abbrev KeepTok (sevm : Sevm) (T : B256) (L : List Exec.Frame) : Prop :=
  ∀ c ∈ L, c.sevm.currentTarget = T.toAdr → ChildKeepsPool sevm c

namespace KeepSel

variable {sevm : Sevm} {σ : Stor} {L : List Exec.Frame}

theorem tok (h : KeepSel sevm σ L) : KeepTok sevm (σ.get tokenSlot) L :=
  fun c hc ht => h c hc (.inl ht)

theorem coin (h : KeepSel sevm σ L) {i : Nat} (hi : i < 3) :
    KeepCoin sevm (σ.get (coinsBase + Nat.toB256 i)) L :=
  fun c hc ht hs => h c hc (.inr ⟨⟨i, hi, ht⟩, hs⟩)

theorem suffix {L' : List Exec.Frame} (h : KeepSel sevm σ (L' ++ L)) : KeepSel sevm σ L :=
  fun c hc => h c (List.mem_append_right _ hc)

theorem tail {c : Exec.Frame} (h : KeepSel sevm σ (c :: L)) : KeepSel sevm σ L :=
  fun c' hc' => h c' (List.mem_cons_of_mem _ hc')

/-- Every child keeping the pool gives the conditional form. -/
theorem of_keep (h : RlKeep sevm L) : KeepSel sevm σ L := fun c hc _ => h c hc

/-- The form a frame at depth `1` has (`RlKeepC`), when its token and coins are neither the pool nor `4`. -/
theorem of_keepC (h : RlKeepC sevm L)
    (hc : ∀ i, i < 3 → (σ.get (coinsBase + Nat.toB256 i)).toAdr ≠ sevm.currentTarget ∧
      (σ.get (coinsBase + Nat.toB256 i)).toAdr ≠ 4)
    (ht : (σ.get tokenSlot).toAdr ≠ sevm.currentTarget ∧ (σ.get tokenSlot).toAdr ≠ 4) :
    KeepSel sevm σ L := by
  rintro c hm (e | ⟨⟨i, hi, e⟩, -⟩)
  · exact h c hm (by rw [e]; exact ht.1) (by rw [e]; exact ht.2)
  · exact h c hm (by rw [e]; exact (hc i hi).1) (by rw [e]; exact (hc i hi).2)

end KeepSel

theorem poolCoinSel_balanceOfData {e : Sevm} {a : Adr} (h : e.data = balanceOfData a) :
    CurveCoins.PoolCoinSel (Sevm.selector e) :=
  CurveCoins.poolCoinSel_balanceOf h

theorem poolCoinSel_transferFromData {e : Sevm} {a b c : Bytes}
    (h : e.data = transferFromSel ++ a ++ b ++ c) : CurveCoins.PoolCoinSel (Sevm.selector e) :=
  CurveCoins.poolCoinSel_transferFrom (tail := a ++ b ++ c)
    (by rw [h]; simp only [List.append_assoc]; rfl)

theorem poolCoinSel_transferData {e : Sevm} {a b : Bytes} (h : e.data = transferSel ++ a ++ b) :
    CurveCoins.PoolCoinSel (Sevm.selector e) :=
  CurveCoins.poolCoinSel_transfer (tail := a ++ b) (by rw [h]; simp only [List.append_assoc]; rfl)

end Blanc.Lift.Curve3Pool
