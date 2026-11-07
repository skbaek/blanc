import Jaune.Transaction
import Batteries.Tactic.OpenPrivate

/-!
# What incorporation does to a block access list's slots

`BalBuilder.incorporate` is EIP-7928's `update_builder_from_tx`. This module reads off its effect on the storage part of
one account's entry, for a transaction or system call whose slots are fresh at its index: a slot among the explicit writes
gains one change at that index if its value moved, and none otherwise; every other slot's changes stay; a slot read is
recorded. Balance, nonce and code changes are not stated here. `open private` on Jaune's builder is isolated in this
module. Contract-neutral.
-/

namespace Blanc.Lift

open Jaune

open private BalAccount.upsert BalBuilder.startAccount BalBuilder.startStorage from Jaune.Transaction

/-- A slot's changes in the builder. -/
def balChanges (b : BalBuilder) (a : Adr) (k : B256) : List (Nat × B256) :=
  (b.accounts.getD a {}).storageChanges.getD k []

/-- Whether the builder records a slot as read. -/
def balRead (b : BalBuilder) (a : Adr) (k : B256) : Prop :=
  k ∈ (b.accounts.getD a {}).storageReads

/-- The value the builder has captured for a slot at the start of an index. -/
def balStart (b : BalBuilder) (idx : Nat) (a : Adr) (k : B256) : Option B256 :=
  ((b.indexStartStorage.getD idx .empty).getD a .empty).get? k

/-- A step that leaves every account's storage entry and the captured storage alone. -/
def BalKeeps (b b' : BalBuilder) : Prop :=
  (∀ a, (b'.accounts.getD a {}).storageChanges = (b.accounts.getD a {}).storageChanges) ∧
    (∀ a, (b'.accounts.getD a {}).storageReads = (b.accounts.getD a {}).storageReads) ∧
    b'.indexStartStorage = b.indexStartStorage

theorem BalKeeps.refl (b : BalBuilder) : BalKeeps b b := ⟨fun _ => rfl, fun _ => rfl, rfl⟩

theorem BalKeeps.trans {b c d : BalBuilder} (h : BalKeeps b c) (k : BalKeeps c d) : BalKeeps b d :=
  ⟨fun a => (k.1 a).trans (h.1 a), fun a => (k.2.1 a).trans (h.2.1 a), k.2.2.trans h.2.2⟩

theorem BalKeeps.foldl {α : Type} {f : BalBuilder → α → BalBuilder} (hf : ∀ b x, BalKeeps b (f b x)) :
    ∀ (L : List α) (b : BalBuilder), BalKeeps b (L.foldl f b)
  | [], b => BalKeeps.refl b
  | x :: L, b => (hf b x).trans (BalKeeps.foldl hf L _)

theorem modify_getD (b : BalBuilder) (a a' : Adr) (f : BalAccount → BalAccount) :
    (b.modify a f).accounts.getD a' {} = if a = a' then f (b.accounts.getD a {}) else b.accounts.getD a' {} := by
  show (b.accounts.insert a _).getD a' {} = _
  rw [Std.TreeMap.getD_insert]
  by_cases h : a = a'
  · subst h
    simp only [Std.ReflCmp.compare_self, ↓reduceIte]
  · have hc : compare a a' ≠ .eq := fun hc => h (Std.LawfulEqCmp.eq_of_compare hc)
    simp only [hc, h, ↓reduceIte]

theorem modify_keeps (b : BalBuilder) (a : Adr) {f : BalAccount → BalAccount}
    (h1 : ∀ x, (f x).storageChanges = x.storageChanges) (h2 : ∀ x, (f x).storageReads = x.storageReads) :
    BalKeeps b (b.modify a f) := by
  refine ⟨fun a' => ?_, fun a' => ?_, rfl⟩
  · rw [modify_getD]
    split
    · rename_i h
      subst h
      exact h1 _
    · rfl
  · rw [modify_getD]
    split
    · rename_i h
      subst h
      exact h2 _
    · rfl

theorem ensure_keeps (b : BalBuilder) (a : Adr) : BalKeeps b (b.ensure a) := by
  unfold BalBuilder.ensure
  split
  · exact BalKeeps.refl b
  · rename_i hc
    have hget : ∀ a', (b.accounts.insert a {}).getD a' {} = b.accounts.getD a' {} := by
      intro a'
      rw [Std.TreeMap.getD_insert]
      split
      · rename_i he
        have he' : a = a' := Std.LawfulEqCmp.eq_of_compare he
        subst he'
        have hn : a ∉ b.accounts := by simpa only [Std.TreeMap.mem_iff_contains, Bool.not_eq_true] using hc
        rw [Std.TreeMap.getD_eq_fallback hn]
      · rfl
    exact ⟨fun a' => congrArg BalAccount.storageChanges (hget a'), fun a' => congrArg BalAccount.storageReads (hget a'), rfl⟩

theorem startAccount_keeps (b : BalBuilder) (idx : Nat) (a : Adr) (ac : Acct) :
    BalKeeps b (BalBuilder.startAccount b idx a ac).1 := by
  unfold BalBuilder.startAccount
  dsimp only
  split
  · exact BalKeeps.refl b
  · exact ⟨fun _ => rfl, fun _ => rfl, rfl⟩

theorem account_ite_keeps (B : BalBuilder) (a : Adr) (c1 c2 : Prop) [Decidable c1] [Decidable c2]
    {f g : BalAccount → BalAccount} (hf1 : ∀ x, (f x).storageChanges = x.storageChanges)
    (hf2 : ∀ x, (f x).storageReads = x.storageReads) (hg1 : ∀ x, (g x).storageChanges = x.storageChanges)
    (hg2 : ∀ x, (g x).storageReads = x.storageReads) :
    BalKeeps B (if c1 then B.modify a f else if c2 then B.modify a g else B) := by
  split
  · exact modify_keeps B a hf1 hf2
  · split
    · exact modify_keeps B a hg1 hg2
    · exact BalKeeps.refl B

theorem bal_ite_keeps (B : BalBuilder) (a : Adr) (idx : Nat) (v : B256) (c1 c2 : Prop) [Decidable c1] [Decidable c2] :
    BalKeeps B (if c1 then B.modify a (·.addBalanceChange idx v)
      else if c2 then B.modify a (·.removeBalanceChange idx) else B) :=
  account_ite_keeps B a c1 c2 (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem nonce_ite_keeps (B : BalBuilder) (a : Adr) (idx : Nat) (v : UInt64) (c1 c2 : Prop) [Decidable c1] [Decidable c2] :
    BalKeeps B (if c1 then B.modify a (·.addNonceChange idx v)
      else if c2 then B.modify a (·.removeNonceChange idx) else B) :=
  account_ite_keeps B a c1 c2 (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem code_ite_keeps (B : BalBuilder) (a : Adr) (idx : Nat) (v : ByteArray) (c1 c2 : Prop) [Decidable c1] [Decidable c2] :
    BalKeeps B (if c1 then B.modify a (·.addCodeChange idx v)
      else if c2 then B.modify a (·.removeCodeChange idx) else B) :=
  account_ite_keeps B a c1 c2 (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

/-- One explicit write, as `incorporate` folds it. -/
def balWriteStep (idx : Nat) (pre post : State) : BalBuilder → Adr × B256 → BalBuilder :=
  fun b ⟨a, k⟩ =>
    let ⟨b, startValue⟩ := BalBuilder.startStorage b idx a k ((pre.get a).stor.get k)
    let value := (post.get a).stor.get k
    if startValue ≠ value then b.modify a (·.addStorageWrite k idx value)
    else b.modify a (·.removeStorageWrite k idx)

/-- `incorporate`, split: the account half keeps the storage part. -/
theorem incorporate_eq (b : BalBuilder) (idx : Nat) (pre post : State) (ar : List Adr)
    (sr sw : List (Adr × B256)) :
    ∃ b1, BalKeeps b b1 ∧ b.incorporate idx pre post ar sr sw =
      ar.foldl (init := sr.foldl (init := sw.foldl (balWriteStep idx pre post) b1)
        fun b ⟨a, k⟩ => b.modify a (·.addStorageRead k)) fun b a => b.ensure a := by
  refine ⟨_, ?_, rfl⟩
  refine BalKeeps.foldl ?_ _ _
  intro B a
  dsimp only
  have step : ∀ {x y : BalBuilder} {f : BalAccount → BalAccount},
      (∀ z, (f z).storageChanges = z.storageChanges) → (∀ z, (f z).storageReads = z.storageReads) →
      BalKeeps x y → BalKeeps x (y.modify a f) := fun h1 h2 h => h.trans (modify_keeps _ a h1 h2)
  split
  · generalize hs : BalBuilder.startAccount B idx a (pre.get a) = pr
    have hB : BalKeeps B pr.1 := by
      rw [← hs]
      exact startAccount_keeps B idx a (pre.get a)
    obtain ⟨b0, st⟩ := pr
    replace hB : BalKeeps B b0 := hB
    dsimp only
    clear hs
    repeat' split
    all_goals
      repeat
        first
          | exact hB
          | refine step (fun _ => rfl) (fun _ => rfl) ?_
  · repeat' split
    all_goals
      repeat
        first
          | exact BalKeeps.refl B
          | refine step (fun _ => rfl) (fun _ => rfl) ?_

theorem startStorage_accounts (b : BalBuilder) (idx : Nat) (a : Adr) (k v : B256) :
    (BalBuilder.startStorage b idx a k v).1.accounts = b.accounts := by
  unfold BalBuilder.startStorage
  dsimp only
  split <;> rfl

theorem startStorage_value (b : BalBuilder) (idx : Nat) (a : Adr) (k v : B256) (h : balStart b idx a k = none) :
    (BalBuilder.startStorage b idx a k v).2 = v := by
  have hg : ((b.indexStartStorage.getD idx .empty).getD a .empty).get? k = none := h
  unfold BalBuilder.startStorage
  dsimp only
  rw [hg]

theorem startStorage_other (b : BalBuilder) (idx : Nat) (a : Adr) (k v : B256) (a' : Adr) (k' : B256)
    (hne : (a', k') ≠ (a, k)) :
    balStart (BalBuilder.startStorage b idx a k v).1 idx a' k' = balStart b idx a' k' := by
  unfold BalBuilder.startStorage
  dsimp only
  split
  · rfl
  show (((b.indexStartStorage.insert idx _).getD idx .empty).getD a' .empty).get? k' = _
  rw [Std.TreeMap.getD_insert_self, Std.TreeMap.getD_insert]
  by_cases ha : a = a'
  · subst ha
    have hk : k ≠ k' := fun e => hne (by rw [e])
    have hc : compare k k' ≠ .eq := fun hc => hk (Std.LawfulEqCmp.eq_of_compare hc)
    simp only [Std.ReflCmp.compare_self, ↓reduceIte, Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert, hc]
    rfl
  · have hc : compare a a' ≠ .eq := fun hc => ha (Std.LawfulEqCmp.eq_of_compare hc)
    simp only [hc, ↓reduceIte]
    rfl

theorem addWrite_changes (acc : BalAccount) (k : B256) (idx : Nat) (v : B256) (k' : B256)
    (clean : ∀ c ∈ acc.storageChanges.getD k [], c.1 ≠ idx) :
    (acc.addStorageWrite k idx v).storageChanges.getD k' [] =
      if k = k' then acc.storageChanges.getD k [] ++ [(idx, v)] else acc.storageChanges.getD k' [] := by
  show (acc.storageChanges.insert k _).getD k' [] = _
  rw [Std.TreeMap.getD_insert]
  by_cases h : k = k'
  · subst h
    have hany : (acc.storageChanges.getD k []).any (fun c => decide (c.1 = idx)) = false := by
      rw [List.any_eq_false]
      intro c hc
      simp only [decide_eq_true_eq]
      exact clean c hc
    simp only [Std.ReflCmp.compare_self, ↓reduceIte, BalAccount.upsert, hany, Bool.false_eq_true]
  · have hc : compare k k' ≠ .eq := fun hc => h (Std.LawfulEqCmp.eq_of_compare hc)
    simp only [hc, h, ↓reduceIte]

theorem removeWrite_changes (acc : BalAccount) (k : B256) (idx : Nat) (k' : B256)
    (clean : ∀ c ∈ acc.storageChanges.getD k [], c.1 ≠ idx) :
    (acc.removeStorageWrite k idx).storageChanges.getD k' [] = acc.storageChanges.getD k' [] := by
  have hfilter : (acc.storageChanges.getD k []).filter (fun c => c.1 != idx) = acc.storageChanges.getD k [] := by
    rw [List.filter_eq_self]
    intro c hc
    simp only [bne_iff_ne, ne_eq]
    exact clean c hc
  unfold BalAccount.removeStorageWrite
  dsimp only
  rw [hfilter]
  split
  · rename_i hempty
    rw [Std.TreeMap.getD_erase]
    split
    · rename_i he
      have he' : k = k' := Std.LawfulEqCmp.eq_of_compare he
      subst he'
      rw [List.isEmpty_iff.mp hempty]
    · rfl
  · rw [Std.TreeMap.getD_insert]
    split
    · rename_i he
      have he' : k = k' := Std.LawfulEqCmp.eq_of_compare he
      subst he'
      rfl
    · rfl

/-- One explicit write's effect at account `t`. -/
theorem writeStep_spec (idx : Nat) (pre post : State) (t : Adr) (b : BalBuilder) (a : Adr) (k : B256)
    (fresh : a = t → balStart b idx t k = none) (clean : a = t → ∀ c ∈ balChanges b t k, c.1 ≠ idx) :
    (∀ k', balChanges (balWriteStep idx pre post b (a, k)) t k' =
      if a = t ∧ k = k' ∧ (pre.get t).stor.get k ≠ (post.get t).stor.get k then
        balChanges b t k' ++ [(idx, (post.get t).stor.get k)]
      else balChanges b t k') ∧
    (∀ a', ((balWriteStep idx pre post b (a, k)).accounts.getD a' {}).storageReads =
      (b.accounts.getD a' {}).storageReads) ∧
    (∀ k', (a, k) ≠ (t, k') → balStart (balWriteStep idx pre post b (a, k)) idx t k' = balStart b idx t k') := by
  have haccs := startStorage_accounts b idx a k ((pre.get a).stor.get k)
  have hother := startStorage_other b idx a k ((pre.get a).stor.get k)
  have hvalue := startStorage_value b idx a k ((pre.get a).stor.get k)
  generalize hp : BalBuilder.startStorage b idx a k ((pre.get a).stor.get k) = pr at haccs hother hvalue
  obtain ⟨b0, sv⟩ := pr
  have hstep : balWriteStep idx pre post b (a, k) =
      if sv ≠ (post.get a).stor.get k then b0.modify a (·.addStorageWrite k idx ((post.get a).stor.get k))
      else b0.modify a (·.removeStorageWrite k idx) := by
    show (match BalBuilder.startStorage b idx a k ((pre.get a).stor.get k) with
      | (b, startValue) =>
        let value := (post.get a).stor.get k
        if startValue ≠ value then b.modify a (·.addStorageWrite k idx value)
        else b.modify a (·.removeStorageWrite k idx)) = _
    rw [hp]
  have hget : ∀ a', b0.accounts.getD a' {} = b.accounts.getD a' {} := fun a' => by
    have : b0.accounts = b.accounts := haccs
    rw [this]
  refine ⟨fun k' => ?_, fun a' => ?_, fun k' hne => ?_⟩
  · rw [hstep]
    by_cases ha : a = t
    · subst ha
      have hsv : sv = (pre.get a).stor.get k := hvalue (fresh rfl)
      have hc : ∀ c ∈ (b0.accounts.getD a {}).storageChanges.getD k [], c.1 ≠ idx := by
        rw [hget]
        exact clean rfl
      unfold balChanges
      by_cases hm : (pre.get a).stor.get k ≠ (post.get a).stor.get k
      · rw [hsv, ite_eq_left hm, modify_getD, ite_eq_left rfl, addWrite_changes _ _ _ _ _ hc, hget]
        by_cases hk : k = k'
        · subst hk
          simp only [true_and, hm, not_false_eq_true, ↓reduceIte, ne_eq]
        · simp only [hk, ↓reduceIte, false_and, and_false]
      · rw [hsv, ite_eq_right hm, modify_getD, ite_eq_left rfl, removeWrite_changes _ _ _ _ hc, hget]
        simp only [hm, and_false, ↓reduceIte]
    · unfold balChanges
      have hnot : ¬ (a = t ∧ k = k' ∧ (pre.get t).stor.get k ≠ (post.get t).stor.get k) := fun h => ha h.1
      rw [ite_eq_right hnot]
      split <;> rw [modify_getD, ite_eq_right ha, hget]
  · rw [hstep, ← hget a']
    split
    · rw [modify_getD]
      split
      · rename_i h
        subst h
        rfl
      · rfl
    · rw [modify_getD]
      split
      · rename_i h
        subst h
        unfold BalAccount.removeStorageWrite
        rfl
      · rfl
  · rw [hstep]
    split <;> exact hother t k' (Ne.symm hne)

/-- The writes' fold at one account: a slot among them gains one change at the index if its value moved; every other
slot stays. `fresh` and `clean` say nothing earlier at this index captured or changed these slots. -/
theorem writes_fold (idx : Nat) (pre post : State) (t : Adr) :
    ∀ (sw : List (Adr × B256)) (b : BalBuilder), sw.Nodup →
      (∀ k, (t, k) ∈ sw → balStart b idx t k = none) →
      (∀ k, (t, k) ∈ sw → ∀ c ∈ balChanges b t k, c.1 ≠ idx) →
      (∀ k, balChanges (sw.foldl (balWriteStep idx pre post) b) t k =
        if (t, k) ∈ sw ∧ (pre.get t).stor.get k ≠ (post.get t).stor.get k then
          balChanges b t k ++ [(idx, (post.get t).stor.get k)]
        else balChanges b t k) ∧
      (∀ a, ((sw.foldl (balWriteStep idx pre post) b).accounts.getD a {}).storageReads =
        (b.accounts.getD a {}).storageReads)
  | [], b, _, _, _ => by
    simp only [List.foldl_nil, List.not_mem_nil, false_and, ↓reduceIte, implies_true, and_self]
  | ⟨a, k⟩ :: sw, b, nd, fresh, clean => by
    have hndCons := List.nodup_cons.mp nd
    have hspec := writeStep_spec idx pre post t b a k
      (fun e => fresh k (by subst e; exact List.mem_cons_self))
      (fun e => clean k (by subst e; exact List.mem_cons_self))
    obtain ⟨h1, h2, h3⟩ := hspec
    have ih := writes_fold idx pre post t sw (balWriteStep idx pre post b (a, k)) hndCons.2
      (fun k' hk' => by
        rw [h3 k' (fun e => hndCons.1 (e ▸ hk'))]
        exact fresh k' (List.mem_cons_of_mem _ hk'))
      (fun k' hk' c hc => by
        rw [h1 k'] at hc
        have hne : ¬ (a = t ∧ k = k' ∧ (pre.get t).stor.get k ≠ (post.get t).stor.get k) := by
          rintro ⟨rfl, rfl, -⟩
          exact hndCons.1 hk'
        rw [ite_eq_right hne] at hc
        exact clean k' (List.mem_cons_of_mem _ hk') c hc)
    refine ⟨fun k' => ?_, fun a' => ?_⟩
    · simp only [List.foldl_cons]
      rw [ih.1 k', h1 k']
      by_cases heq : (a, k) = (t, k')
      · have ha : a = t := congrArg Prod.fst heq
        have hk : k = k' := congrArg Prod.snd heq
        subst ha hk
        have hnot : (a, k) ∉ sw := hndCons.1
        simp only [hnot, false_and, ↓reduceIte, List.mem_cons, true_or, true_and]
      · have hmem : (t, k') ∈ (a, k) :: sw ↔ (t, k') ∈ sw := by
          simp only [List.mem_cons, or_iff_right_iff_imp]
          exact fun e => absurd e.symm heq
        have hne : ¬ (a = t ∧ k = k' ∧ (pre.get t).stor.get k ≠ (post.get t).stor.get k) := by
          rintro ⟨rfl, rfl, -⟩
          exact heq rfl
        simp only [hmem, ite_eq_right hne]
    · simp only [List.foldl_cons]
      rw [ih.2 a', h2 a']

/-- The reads' fold. -/
theorem reads_fold (t : Adr) :
    ∀ (sr : List (Adr × B256)) (b : BalBuilder),
      (∀ k, balChanges (sr.foldl (init := b) fun b ⟨a, k⟩ => b.modify a (·.addStorageRead k)) t k = balChanges b t k) ∧
      (∀ k, balRead (sr.foldl (init := b) fun b ⟨a, k⟩ => b.modify a (·.addStorageRead k)) t k ↔
        balRead b t k ∨ (t, k) ∈ sr)
  | [], b => by
    simp only [List.foldl_nil, List.not_mem_nil, or_false, implies_true, and_self]
  | ⟨a, k⟩ :: sr, b => by
    obtain ⟨ih1, ih2⟩ := reads_fold t sr (b.modify a (·.addStorageRead k))
    refine ⟨fun k' => ?_, fun k' => ?_⟩
    · simp only [List.foldl_cons]
      refine (ih1 k').trans ?_
      unfold balChanges
      rw [modify_getD]
      split
      · rename_i h
        subst h
        rfl
      · rfl
    · simp only [List.foldl_cons]
      refine (ih2 k').trans ?_
      have hstep : balRead (b.modify a (·.addStorageRead k)) t k' ↔ balRead b t k' ∨ (a = t ∧ k = k') := by
        unfold balRead
        rw [modify_getD]
        by_cases ha : a = t
        · subst ha
          simp only [↓reduceIte, true_and]
          show k' ∈ ((b.accounts.getD a {}).storageReads.insert k ()) ↔ _
          rw [Std.TreeMap.mem_insert]
          constructor
          · rintro (h | h)
            · exact Or.inr (Std.LawfulEqCmp.eq_of_compare h)
            · exact Or.inl h
          · rintro (h | h)
            · exact Or.inr h
            · subst h
              exact Or.inl Std.ReflCmp.compare_self
        · simp only [ha, ↓reduceIte, false_and, or_false]
      rw [hstep]
      simp only [List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro ((h | ⟨h1, h2⟩) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨h1.symm, h2.symm⟩)
        · exact Or.inr (Or.inr h)
      · rintro (h | ⟨h1, h2⟩ | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr ⟨h1.symm, h2.symm⟩)
        · exact Or.inr h

/-- **What incorporation does to one account's slots.** The explicit writes are distinct; nothing earlier at the index
captured or changed the slots written at `t`. Then a written slot whose value moved from `pre` to `post` gains exactly one
change at the index, with its `post` value; every other slot's changes stay; and a slot is recorded as read exactly if it
already was or it is among the reads. Balance, nonce and code changes are not stated. -/
theorem incorporate_storage (b : BalBuilder) (idx : Nat) (pre post : State) (ar : List Adr)
    (sr sw : List (Adr × B256)) (t : Adr) (nd : sw.Nodup)
    (fresh : ∀ k, (t, k) ∈ sw → balStart b idx t k = none)
    (clean : ∀ k, (t, k) ∈ sw → ∀ c ∈ balChanges b t k, c.1 ≠ idx) :
    (∀ k, balChanges (b.incorporate idx pre post ar sr sw) t k =
      if (t, k) ∈ sw ∧ (pre.get t).stor.get k ≠ (post.get t).stor.get k then
        balChanges b t k ++ [(idx, (post.get t).stor.get k)]
      else balChanges b t k) ∧
    (∀ k, balRead (b.incorporate idx pre post ar sr sw) t k ↔ balRead b t k ∨ (t, k) ∈ sr) := by
  obtain ⟨b1, hkeep, heq⟩ := incorporate_eq b idx pre post ar sr sw
  have hch : ∀ k, balChanges b1 t k = balChanges b t k := fun k => by
    unfold balChanges
    rw [hkeep.1 t]
  have hst : ∀ k, balStart b1 idx t k = balStart b idx t k := fun k => by
    unfold balStart
    rw [hkeep.2.2]
  obtain ⟨w1, w2⟩ := writes_fold idx pre post t sw b1 nd
    (fun k hk => (hst k).trans (fresh k hk))
    (fun k hk c hc => clean k hk c (by rw [← hch k]; exact hc))
  obtain ⟨r1, r2⟩ := reads_fold t sr (sw.foldl (balWriteStep idx pre post) b1)
  have hens := BalKeeps.foldl ensure_keeps ar (sr.foldl (init := sw.foldl (balWriteStep idx pre post) b1)
    fun b ⟨a, k⟩ => b.modify a (·.addStorageRead k))
  rw [heq]
  refine ⟨fun k => ?_, fun k => ?_⟩
  · have h0 : balChanges (ar.foldl (init := sr.foldl (init := sw.foldl (balWriteStep idx pre post) b1)
        fun b ⟨a, k⟩ => b.modify a (·.addStorageRead k)) fun b a => b.ensure a) t k =
        balChanges (sr.foldl (init := sw.foldl (balWriteStep idx pre post) b1)
        fun b ⟨a, k⟩ => b.modify a (·.addStorageRead k)) t k := by
      unfold balChanges
      rw [hens.1 t]
    rw [h0, r1 k, w1 k, hch k]
  · have h0 : balRead (ar.foldl (init := sr.foldl (init := sw.foldl (balWriteStep idx pre post) b1)
        fun b ⟨a, k⟩ => b.modify a (·.addStorageRead k)) fun b a => b.ensure a) t k ↔
        balRead (sr.foldl (init := sw.foldl (balWriteStep idx pre post) b1)
        fun b ⟨a, k⟩ => b.modify a (·.addStorageRead k)) t k := by
      unfold balRead
      rw [hens.2.1 t]
    rw [h0, r2 k]
    have h1 : balRead (sw.foldl (balWriteStep idx pre post) b1) t k ↔ balRead b t k := by
      unfold balRead
      rw [w2 t, hkeep.2.1 t]
    rw [h1]

/-- `incorporate_storage` over key sets: their lists have no repeats and hold their members. -/
theorem incorporate_keysets (b : BalBuilder) (idx : Nat) (pre post : State) (ar : List Adr)
    (reads writes : KeySet) (t : Adr)
    (fresh : ∀ k, (t, k) ∈ writes → balStart b idx t k = none)
    (clean : ∀ k, (t, k) ∈ writes → ∀ c ∈ balChanges b t k, c.1 ≠ idx) :
    (∀ k, balChanges (b.incorporate idx pre post ar reads.toList writes.toList) t k =
      if (t, k) ∈ writes ∧ (pre.get t).stor.get k ≠ (post.get t).stor.get k then
        balChanges b t k ++ [(idx, (post.get t).stor.get k)]
      else balChanges b t k) ∧
    (∀ k, balRead (b.incorporate idx pre post ar reads.toList writes.toList) t k ↔
      balRead b t k ∨ (t, k) ∈ reads) := by
  have nd : writes.toList.Nodup := writes.distinct_toList.imp (fun h e => by
    subst e
    simp only [beq_self_eq_true, reduceCtorEq] at h)
  obtain ⟨h1, h2⟩ := incorporate_storage b idx pre post ar reads.toList writes.toList t nd
    (fun k hk => fresh k (Std.HashSet.mem_toList.mp hk))
    (fun k hk => clean k (Std.HashSet.mem_toList.mp hk))
  refine ⟨fun k => ?_, fun k => ?_⟩
  · rw [h1 k]
    simp only [Std.HashSet.mem_toList]
  · rw [h2 k]
    simp only [Std.HashSet.mem_toList]

end Blanc.Lift
