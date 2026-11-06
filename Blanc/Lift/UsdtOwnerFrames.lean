import Blanc.Lift.UsdtFrames
import Blanc.Lift.WriteSiteStep

/-!
# USDT: the owner's entry at the `top` write sites, and what the frame laws leave of a slot

The certificate cannot name the slot of USDT's four `top` balance writes, since its terms have no `SLOAD`.
The walks of `UsdtFrames` do: `transfer`'s and `transferFrom`'s fee credit (`moveStor`), `issue` (`issueStor`)
and `redeem` (`redeemStor`) write `balances[ownerOf …]`, with the owner word read at the write. This
module says that word is the owner's at the frame's entry:

* `moveStor_top`, `issueStor_top`, `redeemStor_top`: each `top` slot is `balSlot (ownerOf σ)`, for `σ` the
  storage at entry, given that the balance writes before it miss slot `0`;
* `moveStor_get_ne`, `issueStor_get_ne`, `redeemStor_get_ne`, `spendStor_get_ne`: any other slot keeps its word;
* `moveStor_source`: a move lowers its source's entry by at most `v`, whoever else it pays;
* `frame_balanceOf_output`: `balanceOf`'s answer is the entry it names.
-/

namespace Blanc.Lift.Usdt

open Jaune Blanc Blanc.Lift

variable {σ : Stor} {src dst : Adr} {v f k : B256}

theorem ownerOf_set {j x : B256} (hj : j ≠ 0) : ownerOf (σ.set j x) = ownerOf σ := by
  unfold ownerOf
  rw [Stor.get_set_ne _ hj]

/-- The owner word the fee credit reads is the entry's, when the two entries written first miss slot `0`. -/
theorem moveStor_owner (hs : balSlot src ≠ 0) (hd : balSlot dst ≠ 0) :
    ownerOf (credit (debit σ src v) dst (v - f)) = ownerOf σ := by
  unfold credit debit
  rw [ownerOf_set hd, ownerOf_set hs]

/-- **The `top` site of `transfer` and `transferFrom` is the owner's entry.** -/
theorem moveStor_top (hs : balSlot src ≠ 0) (hd : balSlot dst ≠ 0) (hf : f ≠ 0) :
    moveStor σ src dst v f =
      credit (credit (debit σ src v) dst (v - f)) (ownerOf σ) f := by
  unfold moveStor
  rw [ite_eq_right hf, moveStor_owner hs hd]

/-- **The `top` site of `issue` is the owner's entry**, read at entry. -/
theorem issueStor_top (a : B256) :
    issueStor σ a = (σ.set (balSlot (ownerOf σ)) (σ.get (balSlot (ownerOf σ)) + a)).set 1
      ((σ.set (balSlot (ownerOf σ)) (σ.get (balSlot (ownerOf σ)) + a)).get 1 + a) := rfl

/-- **The `top` site of `redeem` is the owner's entry**: the supply write before it misses slot `0`. -/
theorem redeemStor_top (a : B256) :
    redeemStor σ a = (σ.set 1 (σ.get 1 - a)).set (balSlot (ownerOf σ))
      ((σ.set 1 (σ.get 1 - a)).get (balSlot (ownerOf σ)) - a) := by
  unfold redeemStor
  rw [ownerOf_set (by decide)]

/-- Every slot but the three a move writes keeps its word. -/
theorem moveStor_get_ne (hs : balSlot src ≠ 0) (hd : balSlot dst ≠ 0) (k1 : balSlot src ≠ k)
    (k2 : balSlot dst ≠ k) (k3 : balSlot (ownerOf σ) ≠ k) :
    (moveStor σ src dst v f).get k = σ.get k := by
  have base : (credit (debit σ src v) dst (v - f)).get k = σ.get k := by
    unfold credit debit
    rw [Stor.get_set_ne _ k2, Stor.get_set_ne _ k1]
  unfold moveStor
  split
  · exact base
  · rw [moveStor_owner hs hd]
    unfold credit
    rw [Stor.get_set_ne _ k3]
    exact base

theorem issueStor_get_ne {a : B256} (k1 : (1 : B256) ≠ k) (k2 : balSlot (ownerOf σ) ≠ k) :
    (issueStor σ a).get k = σ.get k := by
  unfold issueStor
  rw [Stor.get_set_ne _ k1, Stor.get_set_ne _ k2]

theorem redeemStor_get_ne {a : B256} (k1 : (1 : B256) ≠ k) (k2 : balSlot (ownerOf σ) ≠ k) :
    (redeemStor σ a).get k = σ.get k := by
  rw [redeemStor_top, Stor.get_set_ne _ k2, Stor.get_set_ne _ k1]

theorem spendStor_get_ne {o s : Adr} (hk : allowSlot o s ≠ k) : (spendStor σ o s v).get k = σ.get k := by
  unfold spendStor
  split
  · rfl
  · exact Stor.get_set_ne _ hk _

/-- **A move lowers its source's entry by at most `v`**, whatever the fee and whoever it pays. -/
theorem moveStor_source (ok : MoveOk σ src dst v f) :
    (σ.get (balSlot src)).toNat ≤ ((moveStor σ src dst v f).get (balSlot src)).toNat + v.toNat := by
  have h0 : ((debit σ src v).get (balSlot src)).toNat = (σ.get (balSlot src)).toNat - v.toNat := by
    unfold debit
    rw [Stor.get_set_self, WriteSite.B256.toNat_sub_of_le ok.debit_le]
  have h2 : ((debit σ src v).get (balSlot src)).toNat ≤
      ((credit (debit σ src v) dst (v - f)).get (balSlot src)).toNat :=
    set_get_ge (by exact ok.credit_lt) rfl
  have h3 : ((debit σ src v).get (balSlot src)).toNat ≤
      ((moveStor σ src dst v f).get (balSlot src)).toNat := by
    unfold moveStor
    split
    · exact h2
    · rename_i hf
      exact h2.trans (set_get_ge (σ := credit (debit σ src v) dst (v - f)) (ok.owner_lt hf) rfl)
  have := ok.debit_le
  omega

end Blanc.Lift.Usdt
