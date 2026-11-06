import Blanc.Composition.Curve3PoolExitWorks

/-!
# What a frame's step does to the columns its cost and effect read

`Same a b b'`: address `a` has the same warm keys, storage and warmth in both states. `Mv T r b b'`: every address
outside `T` keeps its view, the refund counter rises by `r`, and a frame that had created nothing, deleted nothing and
not failed still has not. The canonical schedule's states are related by these, step by step.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.Lift.AccumulatedWalk
open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.Curve3PoolCoinExactKit

/-- `a`'s view: the keys warm at it, its storage, its warmth. -/
structure Same (a : Adr) (b b' : Devm) : Prop where
  keys : ∀ k, (⟨a, k⟩ : Adr × B256) ∈ b'.accessedStorageKeys ↔ (⟨a, k⟩ : Adr × B256) ∈ b.accessedStorageKeys
  stor : b'.getStor a = b.getStor a
  warm : a ∈ b'.accessedAddresses ↔ a ∈ b.accessedAddresses

theorem Same.refl (a : Adr) (b : Devm) : Same a b b := ⟨fun _ => Iff.rfl, rfl, Iff.rfl⟩

theorem Same.trans {a : Adr} {b c d : Devm} (h : Same a b c) (h' : Same a c d) : Same a b d :=
  ⟨fun k => (h'.keys k).trans (h.keys k), h'.stor.trans h.stor, h'.warm.trans h.warm⟩

/-- Nothing created, nothing to delete, no failure. -/
structure Clean (b : Devm) : Prop where
  created : ∀ a, a ∉ b.createdAccounts
  del : ∀ a, a ∉ b.accountsToDelete
  error : b.error = none

/-- **A step changes the view of `T` only, adds `r` to the refund and stays clean.** -/
structure Mv (T : List Adr) (r : Int) (b b' : Devm) : Prop where
  same : ∀ a, a ∉ T → Same a b b'
  refund : b'.refundCounter = b.refundCounter + r
  clean : Clean b → Clean b'

theorem Mv.refl (b : Devm) : Mv [] 0 b b :=
  ⟨fun a _ => Same.refl a b, (Int.add_zero _).symm, id⟩

theorem Mv.trans {T T' : List Adr} {r r' : Int} {b c d : Devm} (h : Mv T r b c) (h' : Mv T' r' c d) :
    Mv (T ++ T') (r + r') b d :=
  ⟨fun a ha => by
      rw [List.mem_append, not_or] at ha
      exact (h.same a ha.1).trans (h'.same a ha.2),
    by rw [h'.refund, h.refund, Int.add_assoc], fun hc => h'.clean (h.clean hc)⟩

theorem Mv.mono {T T' : List Adr} {r : Int} {b b' : Devm} (h : Mv T r b b') (hT : ∀ a ∈ T, a ∈ T') : Mv T' r b b' :=
  ⟨fun a ha => h.same a (fun hm => ha (hT a hm)), h.refund, h.clean⟩

/-- Columns only the machine holds. -/
theorem Mv.of_machine {b b' : Devm} (hk : b'.accessedStorageKeys = b.accessedStorageKeys)
    (hs : b'.state = b.state) (hw : b'.accessedAddresses = b.accessedAddresses)
    (hr : b'.refundCounter = b.refundCounter) (hc : b'.createdAccounts = b.createdAccounts)
    (hd : b'.accountsToDelete = b.accountsToDelete) (he : b'.error = b.error) : Mv [] 0 b b' :=
  ⟨fun a _ => ⟨fun k => by rw [hk], by unfold Devm.getStor Devm.getAcct; rw [hs], by rw [hw]⟩,
    by rw [hr, Int.add_zero], fun h => ⟨fun a => by rw [hc]; exact h.created a, fun a => by rw [hd]; exact h.del a,
      by rw [he]; exact h.error⟩⟩

section Slots

variable (s : Sevm) (b : Devm) (k v : B256)

theorem mem_afterSload_iff (a : Adr) (k' : B256) :
    (⟨a, k'⟩ : Adr × B256) ∈ (afterSload s b k).accessedStorageKeys ↔
      (⟨a, k'⟩ : Adr × B256) ∈ b.accessedStorageKeys ∨ (a = s.currentTarget ∧ k' = k) := by
  unfold afterSload
  split
  · next h =>
    refine ⟨Or.inl, ?_⟩
    rintro (h' | ⟨rfl, rfl⟩)
    · exact h'
    · exact h
  · refine ⟨fun hm => ?_, ?_⟩
    · rcases Std.HashSet.mem_insert.mp hm with e | e
      · have : (⟨s.currentTarget, k⟩ : Adr × B256) = ⟨a, k'⟩ := by simpa only [beq_iff_eq] using e
        exact Or.inr ⟨(Prod.mk.inj this).1.symm, (Prod.mk.inj this).2.symm⟩
      · exact Or.inl e
    · rintro (h' | ⟨rfl, rfl⟩)
      · exact Std.HashSet.mem_insert.mpr (Or.inr h')
      · exact Std.HashSet.mem_insert_self

theorem mem_afterSstore_iff (a : Adr) (k' : B256) :
    (⟨a, k'⟩ : Adr × B256) ∈ (afterSstore s b k v).accessedStorageKeys ↔
      (⟨a, k'⟩ : Adr × B256) ∈ b.accessedStorageKeys ∨ (a = s.currentTarget ∧ k' = k) := by
  rw [afterSstore_accessedStorageKeys, ← mem_afterSload_iff s b k a k', afterSload_accessedStorageKeys]

theorem mv_afterSload : Mv [s.currentTarget] 0 b (afterSload s b k) := by
  refine ⟨fun a ha => ⟨fun k' => ?_, afterSload_getStor .., ?_⟩, ?_, fun h => ?_⟩
  · have hne : a ≠ s.currentTarget := fun e => ha (by rw [e]; exact List.mem_singleton.2 rfl)
    rw [mem_afterSload_iff]
    exact ⟨fun h => h.elim id (fun e => absurd e.1 hne), Or.inl⟩
  · unfold afterSload; split <;> exact Iff.rfl
  · unfold afterSload; rw [Int.add_zero]; split <;> rfl
  · unfold afterSload; split
    · exact h
    · exact ⟨h.created, h.del, h.error⟩

theorem mv_afterSstore {r : Int}
    (hr : sstoreNewRefundCounter s.benvStat.rules.gas v (b.getOrigStorVal s s.currentTarget k)
      (b.getStorVal s.currentTarget k) b.refundCounter = b.refundCounter + r) :
    Mv [s.currentTarget] r b (afterSstore s b k v) := by
  refine ⟨fun a ha => ?_, ?_, fun h => ⟨?_, ?_, ?_⟩⟩
  · have hne : a ≠ s.currentTarget := fun e => ha (by rw [e]; exact List.mem_singleton.2 rfl)
    refine ⟨fun k' => ?_, afterSstore_getStor_ne _ _ _ _ _ hne.symm, ?_⟩
    · rw [mem_afterSstore_iff]
      exact ⟨fun h => h.elim id (fun e => absurd e.1 hne), Or.inl⟩
    · rw [afterSstore_accessedAddresses]
  · rw [afterSstore_refundCounter, hr]
  · intro a; rw [afterSstore_createdAccounts]; exact h.created a
  · intro a; rw [afterSstore_accountsToDelete]; exact h.del a
  · rw [afterSstore_error]; exact h.error

theorem mv_addLog (l : Log) : Mv [] 0 b (b.addLog l) :=
  Mv.of_machine rfl rfl rfl rfl rfl rfl rfl

end Slots

/-! ## Warm keys and storage at the frame's own target -/

/-- At address `a`, the warm keys are `K` and the storage is `σ`. -/
structure At (a : Adr) (K : List B256) (σ : Stor) (b : Devm) : Prop where
  keys : ∀ k, (⟨a, k⟩ : Adr × B256) ∈ b.accessedStorageKeys ↔ k ∈ K
  stor : b.getStor a = σ

theorem At.ofSame {a : Adr} {K : List B256} {σ : Stor} {b b' : Devm} (h : At a K σ b) (hs : Same a b b') : At a K σ b' :=
  ⟨fun k => (hs.keys k).trans (h.keys k), hs.stor.trans h.stor⟩

theorem At.congr {a : Adr} {K K' : List B256} {σ : Stor} {b : Devm} (h : At a K σ b) (hK : ∀ k, k ∈ K ↔ k ∈ K') : At a K' σ b :=
  ⟨fun k => (h.keys k).trans (hK k), h.stor⟩

section Target

variable {s : Sevm} {b : Devm} {K : List B256} {σ : Stor} {k v : B256}

theorem At.val (h : At s.currentTarget K σ b) (x : B256) : b.getStorVal s.currentTarget x = σ.get x := by
  rw [getStorVal_eq_getStor, h.stor]

theorem At.sload (h : At s.currentTarget K σ b) (k : B256) : At s.currentTarget (k :: K) σ (afterSload s b k) :=
  ⟨fun x => by
      rw [mem_afterSload_iff, h.keys, List.mem_cons]
      exact ⟨fun h => h.elim Or.inr (fun e => Or.inl e.2), fun h => h.elim (fun e => Or.inr ⟨rfl, e⟩) Or.inl⟩,
    by rw [afterSload_getStor, h.stor]⟩

theorem At.sstore (h : At s.currentTarget K σ b) (k v : B256) :
    At s.currentTarget (k :: K) (σ.set k v) (afterSstore s b k v) :=
  ⟨fun x => by
      rw [mem_afterSstore_iff, h.keys, List.mem_cons]
      exact ⟨fun h => h.elim Or.inr (fun e => Or.inl e.2), fun h => h.elim (fun e => Or.inr ⟨rfl, e⟩) Or.inl⟩,
    by rw [afterSstore_getStor_self, h.stor]⟩

theorem At.sloadCost_cold (h : At s.currentTarget K σ b) (hk : k ∉ K) : sloadCost s b k = 2100 :=
  Blanc.Lift.AccumulatedWalk.sloadCost_cold (fun hm => hk ((h.keys k).1 hm))

theorem At.sloadCost_warm (h : At s.currentTarget K σ b) (hk : k ∈ K) : sloadCost s b k = 100 :=
  sloadCost_of_warm ((h.keys k).2 hk)

theorem At.sstoreCost_warm (h : At s.currentTarget K σ b) (hk : k ∈ K) :
    sstoreCost s b k v = sstoreValueCost (b.getOrigStorVal s s.currentTarget k) (σ.get k) v := by
  rw [sstoreCost_warm_eq ((h.keys k).2 hk), h.val]

end Target

/-- A slot's value at the transaction's start, in a frame that created nothing. -/
theorem Clean.orig {s : Sevm} {b : Devm} (h : Clean b) (a : Adr) (k : B256) :
    b.getOrigStorVal s a k = (getOrigAcct s a).stor.get k := by
  unfold Devm.getOrigStorVal
  rw [ite_eq_right (h.created a)]
  rfl

/-! ## The store's value classes -/

/-- A store over a word unchanged since the transaction began. -/
theorem first_value {x v : B256} :
    sstoreValueCost x x v = if x = v then 100 else if x = 0 then 20000 else 2900 := by
  unfold sstoreValueCost
  by_cases h : x = v
  · simp only [h, ne_eq, not_true_eq_false, and_false, ↓reduceIte]; rfl
  · simp only [ne_eq, h, not_false_eq_true, and_self, ↓reduceIte]; rfl

/-- The refund of a store over a word unchanged since the transaction began. -/
theorem first_refund (g : GasSchedule) {x v : B256} (rc : Int) :
    sstoreNewRefundCounter g v x x rc = rc + if x ≠ 0 ∧ v = 0 then (g.storageClearRefund : Int) else 0 := by
  unfold sstoreNewRefundCounter
  by_cases hxv : x = v
  · subst hxv
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    by_cases h0 : x = 0
    · simp only [h0, not_true_eq_false, false_and, ↓reduceIte, Int.add_zero]
    · simp only [h0, not_false_eq_true, true_and, ↓reduceIte, Int.add_zero]
  · by_cases h0 : x = 0
    · subst h0
      have hv : v ≠ 0 := fun e => hxv e.symm
      simp only [ne_eq, hxv, not_false_eq_true, hv, and_false, ↓reduceIte, not_true_eq_false, false_and, Int.add_zero]
    · by_cases hv : v = 0
      · subst hv
        simp only [ne_eq, h0, not_false_eq_true, and_self, ↓reduceIte, true_and]
      · simp only [ne_eq, hxv, not_false_eq_true, h0, hv, and_false, and_self, ↓reduceIte, false_and, Int.add_zero]

/-! ## The call sites -/

/-- A child that kept `a`'s view leaves its parent's. -/
theorem Same.callChild {a : Adr} {p c : Devm} (oi os : Nat) (h : Same a p c) : Same a p (callChildPost p c oi os) := by
  refine ⟨fun k => ?_, h.stor, ?_⟩
  · exact ⟨fun hm => (Std.HashSet.mem_union_iff.1 hm).elim id (h.keys k).1, fun hm => Std.HashSet.mem_union_iff.2 (Or.inl hm)⟩
  · exact ⟨fun hm => (Std.HashSet.mem_union_iff.1 hm).elim id h.warm.1, fun hm => Std.HashSet.mem_union_iff.2 (Or.inl hm)⟩

/-- The child's frame starts clean over a clean parent. -/
theorem clean_init {m : Msg} (hc : ∀ a, a ∉ m.benv.createdAccounts) (hd : ∀ a, a ∉ m.inheritedDeletions) :
    Clean (initDevm m) := ⟨hc, hd, rfl⟩

theorem mv_callChild {T : List Adr} {r : Int} {b p c : Devm} (oi os : Nat) (hS : ∀ a, a ∉ T → Same a b p)
    (hR : p.refundCounter = b.refundCounter) (hC : Clean b → Clean p)
    (hch : ∀ a, a ∉ T → Same a p c) (hrc : c.refundCounter = r) (hclean : Clean p → Clean c) :
    Mv T r b (callChildPost p c oi os) := by
  refine ⟨fun a ha => (hS a ha).trans ((hch a ha).callChild oi os), ?_, fun h => ?_⟩
  · show p.refundCounter + c.refundCounter = _
    rw [hR, hrc]
  · have hp := hC h
    have hc := hclean hp
    refine ⟨hc.created, fun a hm => ?_, hp.error⟩
    have hm' : a ∈ p.accountsToDelete.union c.accountsToDelete := hm
    rcases Std.HashSet.mem_union_iff.1 hm' with e | e
    · exact hp.del a e
    · exact hc.del a e

section Site

variable (s : Sevm) (b : Devm) (S : List B256) (M : Mem) (G : Nat) (t ii is oi os : B256)

theorem parent_clean (h : Clean b) : Clean (parent b S M G t ii is oi os) := ⟨h.created, h.del, h.error⟩

theorem parent_same {a : Adr} (hne : a ≠ t.toAdr) : Same a b (parent b S M G t ii is oi os) := by
  refine ⟨fun _ => Iff.rfl, rfl, ?_⟩
  show a ∈ b.accessedAddresses.insert t.toAdr ↔ _
  rw [Std.HashSet.mem_insert]
  exact ⟨fun h => h.elim (fun e => absurd (by simpa only [beq_iff_eq] using e : t.toAdr = a).symm hne) id, Or.inr⟩

theorem site_clean_of (h : Clean (parent b S M G t ii is oi os)) :
    Clean (initDevm (callMsg0 s b S M G t ii is oi os)) := by
  refine ⟨h.created, fun a hm => ?_, rfl⟩
  have hm' : a ∈ (if s.benvStat.rules.settle.selfdestructRefund = 0 then (.emptyWithCapacity : AdrSet)
      else (parent b S M G t ii is oi os).accountsToDelete) := hm
  split at hm'
  · exact Std.HashSet.not_mem_emptyWithCapacity hm'
  · exact h.del a hm'

end Site

theorem mv_identity (s : Sevm) (b : Devm) (S : List B256) (M : Mem) (ii is oi os : B256) :
    Mv [] 0 b (identityCallNext s b S M ii is oi os) := by
  refine ⟨fun a _ => ⟨fun k => ?_, rfl, ?_⟩, ?_, fun h => ⟨h.created, fun a hm => ?_, h.error⟩⟩
  · exact Std.HashSet.mem_union_iff.trans or_self_iff
  · exact Std.HashSet.mem_union_iff.trans or_self_iff
  · show b.refundCounter + 0 = _
    rfl
  · rcases Std.HashSet.mem_union_iff.1 hm with e | e
    · exact h.del a e
    · have hm' : a ∈ (if s.benvStat.rules.settle.selfdestructRefund = 0 then (.emptyWithCapacity : AdrSet)
          else b.accountsToDelete) := e
      split at hm'
      · exact Std.HashSet.not_mem_emptyWithCapacity hm'
      · exact h.del a hm'

theorem mv_rawTail (s : Sevm) (b : Devm) (S : List B256) (M : Mem) (p : VyRawSite) :
    Mv [] 0 b (rawTailBaseNext s b S M p) := mv_identity ..

/-- A call site's child message starts where its parent stands, at every address's keys and storage. -/
theorem site_at {a : Adr} {K : List B256} {σ : Stor} (s : Sevm) (b : Devm) (S : List B256) (M : Mem) (G : Nat)
    (t ii is oi os : B256) (h : At a K σ b) :
    At a K σ (initDevm (callMsg0 s b S M G t ii is oi os)) := ⟨h.keys, h.stor⟩

/-- **A value-`0` `CALL`'s canonical successor changes what its child changes.** -/
theorem mv_coinNext {T : List Adr} {r : Int} (canon : Sevm → Devm → Devm) (s : Sevm) (t ii is oi : B256) (b : Devm)
    (S : List B256) (M : Mem)
    (h : Mv T r (initDevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii is oi 0x20))
      (canon (initSevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii is oi 0x20))
        (initDevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii is oi 0x20))))
    (hr : (canon (initSevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii is oi 0x20))
        (initDevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii is oi 0x20))).refundCounter = r) :
    Mv (t.toAdr :: T) r b (coinNext canon s t ii is oi b S M) := by
  refine mv_callChild (T := t.toAdr :: T) _ _ (fun a ha => parent_same _ _ _ 0 t ii is oi 0x20 (fun e => ha (e ▸ List.mem_cons_self))) rfl
    (fun h => parent_clean _ _ _ 0 t ii is oi 0x20 ⟨h.created, h.del, h.error⟩) ?_ hr
    (fun hp => ?_)
  · intro a ha
    have e : Same a (parent (b.withGasLeft 0) S M 0 t ii is oi 0x20)
        (initDevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii is oi 0x20)) := ⟨fun _ => Iff.rfl, rfl, Iff.rfl⟩
    exact e.trans (h.same a (fun hm => ha (List.mem_cons_of_mem _ hm)))
  · exact h.clean (site_clean_of s (b.withGasLeft 0) S M 0 t ii is oi 0x20 hp)

/-- A frame's halting state keeps its base's columns. -/
theorem mv_halted (B : Devm) (S : List B256) (M : Mem) (G a n : Nat) (w : Bytes) :
    Mv [] 0 B (((St B S M G).memRead a n).2.withOutput w) :=
  Mv.of_machine rfl rfl rfl rfl rfl rfl rfl

theorem Mv.halted {T : List Adr} {r : Int} {b B : Devm} (h : Mv T r b B) (S : List B256) (M : Mem) (G a n : Nat) (w : Bytes) :
    Mv T r b (((St B S M G).memRead a n).2.withOutput w) :=
  ⟨fun x hx => ⟨(h.same x hx).keys, (h.same x hx).stor, (h.same x hx).warm⟩, h.refund,
    fun hc => ⟨(h.clean hc).created, (h.clean hc).del, (h.clean hc).error⟩⟩

/-- A list naming one address, repeated. -/
theorem Mv.one {t : Adr} {T : List Adr} {r r' : Int} {b b' : Devm} (h : Mv T r b b') (hT : ∀ a ∈ T, a = t) (hr : r = r') :
    Mv [t] r' b b' := hr ▸ h.mono (fun a ha => List.mem_singleton.2 (hT a ha))

theorem halted_at {x : Adr} {K : List B256} {σ : Stor} {B : Devm} (S : List B256) (M : Mem) (G a n : Nat) (w : Bytes)
    (h : At x K σ B) : At x K σ (((St B S M G).memRead a n).2.withOutput w) := ⟨h.keys, h.stor⟩

/-- `Mv` carries across agreement modulo gas. -/
theorem Mv.congr {T : List Adr} {r : Int} {b c c' : Devm} (h : Mv T r b c) (he : Devm.EqModGas c c') : Mv T r b c' :=
  ⟨fun a ha => ⟨fun k => by rw [← he.accessedStorageKeys]; exact (h.same a ha).keys k,
      (he.getStor_eq a).symm.trans (h.same a ha).stor, by rw [← he.accessedAddresses]; exact (h.same a ha).warm⟩,
    by rw [← he.refundCounter]; exact h.refund,
    fun hc => by
      have := h.clean hc
      exact ⟨fun a => by rw [← he.createdAccounts]; exact this.created a,
        fun a => by rw [← he.accountsToDelete]; exact this.del a, by rw [← he.error]; exact this.error⟩⟩

theorem At.congr_gas {a : Adr} {K : List B256} {σ : Stor} {c c' : Devm} (h : At a K σ c) (he : Devm.EqModGas c c') : At a K σ c' :=
  ⟨fun k => by rw [← he.accessedStorageKeys]; exact h.keys k, (he.getStor_eq a).symm.trans h.stor⟩

end Blanc.Composition.Curve3PoolPublic
