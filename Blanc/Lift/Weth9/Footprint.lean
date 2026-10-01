import Blanc.SlotFootprint
import Blanc.BalanceAlgebra
import Blanc.LadderBase
import Blanc.Lift.Weth9.Spec

/-!
# The WETH9 storage footprint

WETH9's `balanceOf` (base slot 3) and nested `allowance` (base slot 4) live at hashed slots
(`Spec.lean`).  `Weth9.Booked` counts *every* balance slot once, and so has to say something about
every allowance slot; the footprint reading below says nothing about an address a history never
touches.

A **footprint** over a set `K` of tracked keys (`Key`: a balance row or an allowance row) is

* `Support K s`: every nonzero storage word sits at a fixed slot (`fixedSlots = [0, 1, 2]`: `name`,
  `symbol`, `decimals`, which no lifted walk writes) or at a tracked key's slot;
* `KeyInj K`, `KeyApart K`: the tracked slots are pairwise distinct and off the fixed slots;
* `trackedSum K s ≤ ETH`: the tracked balance words, summed as natural numbers, are backed.

`FootInv.extend` extends a footprint over keys that are fresh against it (`KeysFresh`, the
trace-local collision premise); `FootInv.deployed` says the empty footprint holds of deployment-shaped
storage (metadata in the fixed slots only) with no hash fact at all.  The frame-level reading is
`FootLadder.lean`; the history headline is `FootHistory.lean`.
-/

namespace Blanc.Lift.Weth9

open Jaune
open Blanc

/-! ## Keys and slots -/

/-- A mapping key of WETH9: `balanceOf[a]` or `allowance[o][p]`. -/
inductive Key
  | bal (a : Adr)
  | allow (o p : Adr)
  deriving DecidableEq

/-- The storage slot of a key. -/
def Key.slot : Key → B256
  | .bal a => balSlot a
  | .allow o p => allowSlot o p

/-- The slots of the non-mapping variables: `name` (0), `symbol` (1), `decimals` (2). -/
def fixedSlots : List B256 := [0, 1, 2]

/-- Every nonzero word sits at a fixed slot or a tracked key's slot. -/
abbrev Support (K : Key → Prop) (s : Stor) : Prop :=
  SlotFootprint.Support Key.slot fixedSlots K s

/-- Tracked slots are pairwise distinct. -/
abbrev KeyInj (K : Key → Prop) : Prop := SlotFootprint.Inj Key.slot K

/-- Tracked slots avoid the fixed slots. -/
abbrev KeyApart (K : Key → Prop) : Prop := SlotFootprint.Apart Key.slot fixedSlots K

/-- Each touched key is tracked or on a slot in no use; keys sharing a slot are one key. -/
abbrev KeysFresh (K : Key → Prop) (ks : List Key) : Prop :=
  SlotFootprint.FreshKeys Key.slot fixedSlots K ks

/-- The tracked keys after touching `ks`. -/
abbrev Key.extend (K : Key → Prop) (ks : List Key) : Key → Prop :=
  SlotFootprint.extendBy K ks

/-! ## The tracked ledger -/

open Classical in
/-- The word at each tracked holder's balance slot, `0` at an untracked holder. -/
noncomputable def tracked (K : Key → Prop) (s : Stor) : Adr → B256 :=
  fun a => if K (.bal a) then s.get (balSlot a) else 0

/-- The sum of the tracked balance words: the natural-number total the contract books at the tracked
holders. -/
noncomputable def trackedSum (K : Key → Prop) (s : Stor) : Nat := sum (tracked K s)

/-- **The footprint invariant**: support, injective and apart tracked slots, and the tracked ledger
backed by the contract's ether. -/
structure FootInv (K : Key → Prop) (s : Stor) (b : B256) : Prop where
  support : Support K s
  inj : KeyInj K
  apart : KeyApart K
  backed : trackedSum K s ≤ b.toNat

theorem Key.bal_injective {a b : Adr} (h : Key.bal a = Key.bal b) : a = b := Key.bal.inj h

/-! ## The tracked ledger across writes -/

section Ledger

variable {K : Key → Prop} {s : Stor}

theorem tracked_self {a : Adr} (ha : K (.bal a)) : tracked K s a = s.get (balSlot a) := by
  simp only [tracked, ha, ↓reduceIte]

theorem tracked_of_not {a : Adr} (ha : ¬ K (.bal a)) : tracked K s a = 0 := by
  simp only [tracked, ha, ↓reduceIte]

/-- A write at a tracked holder's balance slot changes exactly that holder's row. -/
theorem tracked_set_bal (hK : KeyInj K) {a : Adr} (ha : K (.bal a)) (w : B256) :
    Frel a (fun _ y => y = w) (tracked K s) (tracked K (s.set (balSlot a) w)) := by
  intro b
  constructor
  · intro h
    subst b
    rw [tracked_self ha, Stor.get_set_self]
  · intro hne
    by_cases hb : K (.bal b)
    · rw [tracked_self hb, tracked_self hb, Stor.get_set_ne]
      intro hslot
      exact hne (Key.bal_injective (hK _ _ ha hb hslot))
    · rw [tracked_of_not hb, tracked_of_not hb]

/-- A write off every tracked holder's balance slot leaves the tracked ledger alone. -/
theorem tracked_set_off {k w : B256} (hk : ∀ a, K (.bal a) → balSlot a ≠ k) :
    tracked K (s.set k w) = tracked K s := by
  funext a
  by_cases ha : K (.bal a)
  · rw [tracked_self ha, tracked_self ha, Stor.get_set_ne]
    exact fun h => hk a ha h.symm
  · rw [tracked_of_not ha, tracked_of_not ha]

theorem increase_tracked (hK : KeyInj K) {a : Adr} (ha : K (.bal a)) (v : B256) :
    Increase a v (tracked K s)
      (tracked K (s.set (balSlot a) (s.get (balSlot a) + v))) := by
  intro b
  constructor
  · intro h
    subst b
    rw [tracked_self ha, tracked_self ha, Stor.get_set_self]
  · intro hne
    exact (tracked_set_bal hK ha (s.get (balSlot a) + v) b).2 hne

theorem decrease_tracked (hK : KeyInj K) {a : Adr} (ha : K (.bal a)) (v : B256) :
    Decrease a v (tracked K s)
      (tracked K (s.set (balSlot a) (s.get (balSlot a) - v))) := by
  intro b
  constructor
  · intro h
    subst b
    rw [tracked_self ha, tracked_self ha, Stor.get_set_self]
  · intro hne
    exact (tracked_set_bal hK ha (s.get (balSlot a) - v) b).2 hne

theorem trackedSum_deposit (hK : KeyInj K) {a : Adr} (ha : K (.bal a)) {v : B256}
    (h : trackedSum K s + v.toNat < 2 ^ 256) :
    trackedSum K (s.set (balSlot a) (s.get (balSlot a) + v)) = trackedSum K s + v.toNat := by
  have hle : (tracked K s a).toNat ≤ trackedSum K s := le_sum
  have hnof : B256.Nof (tracked K s a) v := by
    unfold B256.Nof
    omega
  exact (sum_add_assoc (increase_tracked hK ha v) hnof).symm

theorem trackedSum_withdraw (hK : KeyInj K) {a : Adr} (ha : K (.bal a)) {v : B256}
    (h : v ≤ s.get (balSlot a)) :
    trackedSum K (s.set (balSlot a) (s.get (balSlot a) - v)) + v.toNat = trackedSum K s := by
  have hle : v ≤ tracked K s a := by
    rw [tracked_self ha]
    exact h
  have hs := sum_sub_assoc (decrease_tracked (s := s) hK ha v) hle
  have hsumle : v.toNat ≤ trackedSum K s :=
    (B256.toNat_le_toNat hle).trans le_sum
  have hs' : trackedSum K s - v.toNat =
      trackedSum K (s.set (balSlot a) (s.get (balSlot a) - v)) := by
    simpa only [trackedSum] using hs
  omega

/-- A balance transfer between two tracked holders (possibly the same) keeps the tracked ledger. -/
theorem trackedSum_transfer (hK : KeyInj K) {src dst : Adr} (hsrc : K (.bal src))
    (hdst : K (.bal dst)) {wad : B256} (hle : wad ≤ s.get (balSlot src))
    (hsum : trackedSum K s < 2 ^ 256) :
    let s₁ := s.set (balSlot src) (s.get (balSlot src) - wad)
    trackedSum K (s₁.set (balSlot dst) (s₁.get (balSlot dst) + wad)) = trackedSum K s := by
  dsimp only [Lean.Elab.WF.paramLet]
  have hle' : wad ≤ tracked K s src := by
    rw [tracked_self hsrc]
    exact hle
  have hdec := decrease_tracked (s := s) hK hsrc wad
  have hinc := increase_tracked
    (s := s.set (balSlot src) (s.get (balSlot src) - wad)) hK hdst wad
  have htr : Transfer (tracked K s) src wad dst
      (tracked K ((s.set (balSlot src) (s.get (balSlot src) - wad)).set (balSlot dst)
        ((s.set (balSlot src) (s.get (balSlot src) - wad)).get (balSlot dst) + wad))) :=
    ⟨hle', tracked K (s.set (balSlot src) (s.get (balSlot src) - wad)), hdec, hinc⟩
  exact (transfer_preserves_sum hsum htr).symm

end Ledger

/-! ## Extending a footprint over fresh keys -/

/-- Touching fresh keys extends the footprint: a fresh, untracked balance key reads zero, so the
tracked ledger is unchanged. -/
theorem FootInv.extend {K : Key → Prop} {s : Stor} {b : B256} {ks : List Key}
    (h : FootInv K s b) (hf : KeysFresh K ks) : FootInv (Key.extend K ks) s b := by
  refine ⟨h.support.mono (fun k hk => Or.inl hk), h.inj.extend hf, h.apart.extend hf, ?_⟩
  have htracked : tracked (Key.extend K ks) s = tracked K s := by
    funext a
    by_cases hK : K (.bal a)
    · rw [tracked_self hK, tracked_self (Or.inl hK)]
    · by_cases hks : Key.bal a ∈ ks
      · rw [tracked_self (Or.inr hks), tracked_of_not hK]
        exact h.support.get_eq_zero (hf.1 _ hks) hK
      · rw [tracked_of_not hK, tracked_of_not (fun hh => hh.elim hK hks)]
  unfold trackedSum
  rw [htracked]
  exact h.backed

/-- **The empty footprint holds of deployment-shaped storage.**  If the only nonzero words are the
metadata words at the fixed slots — no balance, no allowance — then `FootInv ∅` holds, with no hash
fact: the slots are the fixed ones, and there are no tracked keys whose slots could collide. -/
theorem FootInv.deployed {s : Stor} {b : B256}
    (metadata : ∀ x, s.get x ≠ 0 → x ∈ fixedSlots) :
    FootInv (fun _ => False) s b := by
  refine ⟨fun x hx => Or.inl (metadata x hx), ?_, ?_, ?_⟩
  · intro k k' hk
    exact hk.elim
  · intro k hk
    exact hk.elim
  · have : tracked (fun _ => False) s = fun _ => 0 := by
      funext a
      exact tracked_of_not id
    unfold trackedSum
    rw [this, sum, sumBelow_zero]
    exact Nat.zero_le _

/-! ## What the footprint says about the ledger -/

/-- A tracked holder's stored balance is backed by the contract's ether. -/
theorem FootInv.balance_le {K : Key → Prop} {s : Stor} {b : B256} (h : FootInv K s b)
    {a : Adr} (ha : K (.bal a)) : (s.get (balSlot a)).toNat ≤ b.toNat := by
  have : (tracked K s a).toNat ≤ trackedSum K s := le_sum
  rw [tracked_self ha] at this
  exact this.trans h.backed

/-- **The footprint is a complete ledger**: an address whose balance slot is neither fixed nor a
tracked key's slot books nothing. -/
theorem FootInv.balance_eq_zero {K : Key → Prop} {s : Stor} {b : B256} (h : FootInv K s b)
    {a : Adr} (hfix : balSlot a ∉ fixedSlots) (hK : ∀ k, K k → k.slot ≠ balSlot a) :
    s.get (balSlot a) = 0 := by
  by_contra hne
  rcases h.support _ hne with hx | ⟨k, hk, he⟩
  · exact hfix hx
  · exact hK k hk he

end Blanc.Lift.Weth9
