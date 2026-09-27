import Blanc.Lift.LockCheck
import Blanc.Lift.Cursor
import Blanc.LockExclusion

/-!
# Soundness of the reentrancy-lock checker

`LockCheck.dominance`: for any certificate `c` with `Cert.check code c` and
`lockCert sp c ann`, every frame running `code` from pc `0` on a covered fork
whose executed hashes avoid the slot meets the dominance obligation of
`Blanc/LockExclusion.lean` (every body start and every slot-addressed
`SSTORE` has an earlier node of the frame where the lock was not held; every
mutating body start holds it), plus its strong form (inside a guarded mutating
body only release pcs write the slot) and the absence of `DELEGATECALL`,
`CALLCODE`, `CREATE`, `CREATE2` and `SELFDESTRUCT`.

The proof is one induction along the frame's same-frame chain
(`Exec.Deriv.ParentPrefix`), whatever the frame's outcome: the invariant
`LockOK` pairs the certificate cursor (`CursorOK`, re-established here step by
step exactly as `cursor_step` does, so the synthetic branch taken is the
concrete one) with the lock walk (`lockNode … = true`), the meaning of the
abstract lock state (`LSt.Val`, `LSt.Flags`) and one saved lock state per
pending `callNext` continuation (`LConts`).
-/

namespace Blanc.Lift.LockCheck

open Jaune AbstractStackSafety Blanc.LockExclusion

local notation "PP" => Exec.Deriv.ParentPrefix

/-! ## Facts and their meaning -/

section Facts

variable (sp : Spec) (F n : Exec.Deriv) (ρ : Nat → B256)

/-- The meaning of one fact in the frame rooted at `F`, at its node `n`,
under the symbol valuation `ρ`. -/
def Fact.Holds : Fact → Prop
  | .bnd s lo hi => lo ≤ (ρ s).toNat ∧ (ρ s).toNat ≤ hi
  | .nsl s => ρ s ≠ sp.slot
  | .lt s t => (ρ s).toNat < (ρ t).toNat
  | .le s t => (ρ s).toNat ≤ (ρ t).toNat
  | .gt r s k => (ρ r = 0 → (ρ s).toNat ≤ k) ∧ (ρ r ≠ 0 → k < (ρ s).toNat)
  | .isz r s => (ρ r = 0 → ρ s ≠ 0) ∧ (ρ r ≠ 0 → ρ s = 0)
  | .xor r s t => ρ r ≠ 0 → ρ s ≠ ρ t
  | .lockv s => ∃ m, PP F m ∧ PP m n ∧
      ρ s = lockAt F.sevm.currentTarget sp.slot m.devm
  | .lockeq r => ρ r = 0 → ∃ m, PP F m ∧ PP m n ∧
      lockAt F.sevm.currentTarget sp.slot m.devm ≠ sp.locked

def AllHold (fs : List Fact) : Prop := ∀ f ∈ fs, Fact.Holds sp F n ρ f

end Facts

theorem Fact.holds_mono {sp : Spec} {F n n' : Exec.Deriv} {ρ : Nat → B256} {f : Fact}
    (h : PP n n') (hf : f.Holds sp F n ρ) : f.Holds sp F n' ρ := by
  cases f with
  | lockv s =>
    obtain ⟨m, h1, h2, h3⟩ := hf
    exact ⟨m, h1, h2.trans h, h3⟩
  | lockeq r =>
    intro h0
    obtain ⟨m, h1, h2, h3⟩ := hf h0
    exact ⟨m, h1, h2.trans h, h3⟩
  | _ => exact hf

theorem AllHold.mono {sp : Spec} {F n n' : Exec.Deriv} {ρ : Nat → B256} {fs : List Fact}
    (h : PP n n') (hf : AllHold sp F n ρ fs) : AllHold sp F n' ρ fs :=
  fun f hm => Fact.holds_mono h (hf f hm)

theorem Fact.holds_congr {sp : Spec} {F n : Exec.Deriv} {ρ ρ' : Nat → B256} {f : Fact}
    (h : ∀ s ∈ f.syms, ρ s = ρ' s) (hf : f.Holds sp F n ρ) : f.Holds sp F n ρ' := by
  cases f <;> simp only [Fact.syms, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at h <;> simp only [Fact.Holds] at hf ⊢
  all_goals first
    | (obtain ⟨h1, h2, h3⟩ := h; rw [← h1, ← h2, ← h3]; exact hf)
    | (obtain ⟨h1, h2⟩ := h; rw [← h1, ← h2]; exact hf)
    | (rw [← h]; exact hf)

theorem Fact.holds_rename {sp : Spec} {F n : Exec.Deriv} {ρ : Nat → B256} {m : Nat → Nat}
    {f : Fact} (hf : (f.rename m).Holds sp F n ρ) : f.Holds sp F n (ρ ∘ m) := by
  cases f <;> exact hf

/-! ## Entailment is sound -/

section Entails

variable {sp : Spec} {F n : Exec.Deriv} {ρ : Nat → B256} {fs : List Fact}

theorem bndOf_sound (hf : AllHold sp F n ρ fs) (s : Nat) :
    (bndOf fs s).1 ≤ (ρ s).toNat ∧ (ρ s).toNat ≤ (bndOf fs s).2 := by
  unfold bndOf
  have key : ∀ (gs : List Fact) (p : Nat × Nat), (∀ g ∈ gs, g ∈ fs) →
      p.1 ≤ (ρ s).toNat ∧ (ρ s).toNat ≤ p.2 →
      (gs.foldl (fun p f => match f with
        | .bnd s' lo hi => if s' = s then (max p.1 lo, min p.2 hi) else p
        | _ => p) p).1 ≤ (ρ s).toNat ∧
      (ρ s).toNat ≤ (gs.foldl (fun p f => match f with
        | .bnd s' lo hi => if s' = s then (max p.1 lo, min p.2 hi) else p
        | _ => p) p).2 := by
    intro gs
    induction gs with
    | nil => intro p _ hp; exact hp
    | cons g gs ih =>
      intro p hsub hp
      simp only [List.foldl_cons]
      apply ih _ (fun x hx => hsub x (List.mem_cons_of_mem _ hx))
      cases g with
      | bnd s' lo hi =>
        by_cases hs : s' = s
        · subst hs
          have hg := hf _ (hsub _ List.mem_cons_self)
          simp only [Fact.Holds] at hg
          simp only [ite_true]
          exact ⟨Nat.max_le.mpr ⟨hp.1, hg.1⟩, Nat.le_min.mpr ⟨hp.2, hg.2⟩⟩
        · simp only [hs, ite_false]; exact hp
      | _ => exact hp
  exact key fs _ (fun _ h => h) ⟨Nat.zero_le _, by
    have := B256.toNat_lt (ρ s); unfold maxW; omega⟩

theorem bnd2_sound (hf : AllHold sp F n ρ fs) (s : Nat) :
    (bnd2 fs s).1 ≤ (ρ s).toNat ∧ (ρ s).toNat ≤ (bnd2 fs s).2 := by
  unfold bnd2
  have key : ∀ (gs : List Fact) (p : Nat × Nat), (∀ g ∈ gs, g ∈ fs) →
      p.1 ≤ (ρ s).toNat ∧ (ρ s).toNat ≤ p.2 →
      (gs.foldl (fun p f => match f with
        | .lt a b =>
          if a = s then (p.1, min p.2 ((bndOf fs b).2 - 1))
          else if b = s then (max p.1 ((bndOf fs a).1 + 1), p.2) else p
        | .le a b =>
          if a = s then (p.1, min p.2 (bndOf fs b).2)
          else if b = s then (max p.1 (bndOf fs a).1, p.2) else p
        | _ => p) p).1 ≤ (ρ s).toNat ∧
      (ρ s).toNat ≤ (gs.foldl (fun p f => match f with
        | .lt a b =>
          if a = s then (p.1, min p.2 ((bndOf fs b).2 - 1))
          else if b = s then (max p.1 ((bndOf fs a).1 + 1), p.2) else p
        | .le a b =>
          if a = s then (p.1, min p.2 (bndOf fs b).2)
          else if b = s then (max p.1 (bndOf fs a).1, p.2) else p
        | _ => p) p).2 := by
    intro gs
    induction gs with
    | nil => intro p _ hp; exact hp
    | cons g gs ih =>
      intro p hsub hp
      simp only [List.foldl_cons]
      apply ih _ (fun x hx => hsub x (List.mem_cons_of_mem _ hx))
      have hg := hf _ (hsub _ List.mem_cons_self)
      cases g with
      | lt a b =>
        simp only [Fact.Holds] at hg
        by_cases ha : a = s
        · subst ha
          have hb := bndOf_sound hf b
          simp only [ite_true]
          exact ⟨hp.1, Nat.le_min.mpr ⟨hp.2, by omega⟩⟩
        · by_cases hb : b = s
          · subst hb
            have ha' := bndOf_sound hf a
            simp only [ha, ite_false, ite_true]
            exact ⟨Nat.max_le.mpr ⟨hp.1, by omega⟩, hp.2⟩
          · simp only [ha, hb, ite_false]; exact hp
      | le a b =>
        simp only [Fact.Holds] at hg
        by_cases ha : a = s
        · subst ha
          have hb := bndOf_sound hf b
          simp only [ite_true]
          exact ⟨hp.1, Nat.le_min.mpr ⟨hp.2, by omega⟩⟩
        · by_cases hb : b = s
          · subst hb
            have ha' := bndOf_sound hf a
            simp only [ha, ite_false, ite_true]
            exact ⟨Nat.max_le.mpr ⟨hp.1, by omega⟩, hp.2⟩
          · simp only [ha, hb, ite_false]; exact hp
      | _ => exact hp
  exact key fs _ (fun _ h => h) (bndOf_sound hf s)

theorem entails_sound (hf : AllHold sp F n ρ fs) {g : Fact} (he : entails fs g = true) :
    g.Holds sp F n ρ := by
  cases g with
  | bnd s lo hi =>
    simp only [entails, Bool.and_eq_true, decide_eq_true_eq] at he
    have := bnd2_sound hf s
    exact ⟨by omega, by omega⟩
  | lt s t =>
    simp only [entails, Bool.or_eq_true, List.contains_iff_mem, decide_eq_true_eq] at he
    rcases he with he | he
    · exact hf _ he
    · have := bnd2_sound hf s; have := bnd2_sound hf t
      show (ρ s).toNat < (ρ t).toNat
      omega
  | le s t =>
    simp only [entails, Bool.or_eq_true, List.contains_iff_mem, decide_eq_true_eq] at he
    rcases he with (he | he) | he
    · exact hf _ he
    · have := hf _ he; simp only [Fact.Holds] at this ⊢; omega
    · have := bnd2_sound hf s; have := bnd2_sound hf t
      show (ρ s).toNat ≤ (ρ t).toNat
      omega
  | _ =>
    simp only [entails, List.contains_iff_mem] at he
    exact hf _ he

theorem constOf_sound (hf : AllHold sp F n ρ fs) {s c : Nat} (h : constOf fs s = some c) :
    (ρ s).toNat = c := by
  unfold constOf at h
  split at h
  · cases h
    have := bnd2_sound hf s
    omega
  · cases h

theorem constOf_sound' (hf : AllHold sp F n ρ fs) {s : Nat} {c : B256}
    (h : constOf fs s = some c.toNat) : ρ s = c :=
  B256.toNat_inj _ _ (constOf_sound hf h)

theorem excluded_sound (hf : AllHold sp F n ρ fs) {s : Nat}
    (h : excluded sp fs s = true) : ρ s ≠ sp.slot := by
  intro heq
  simp only [excluded, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not, List.contains_iff_mem] at h
  rcases h with h | h
  · have := bnd2_sound hf s
    rw [heq] at this
    omega
  · exact hf _ h heq

end Entails

/-! ## Symbols and valuations -/

theorem le_foldr_max {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons y l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem lt_fresh_kv {kv : List Nat} {fs : List Fact} {s : Nat} (h : s ∈ kv) :
    s < freshSym kv fs :=
  Nat.lt_succ_of_le (le_foldr_max (List.mem_append_left _ h))

theorem lt_fresh_fact {kv : List Nat} {fs : List Fact} {f : Fact} {s : Nat}
    (hf : f ∈ fs) (hs : s ∈ f.syms) : s < freshSym kv fs :=
  Nat.lt_succ_of_le (le_foldr_max (List.mem_append_right _ (List.mem_flatMap.mpr ⟨f, hf, hs⟩)))

/-- The words `S` carry the symbols `kv` under a valuation satisfying `fs`. -/
def Val (sp : Spec) (F n : Exec.Deriv) (kv : List Nat) (fs : List Fact) (S : List B256) :
    Prop :=
  ∃ ρ : Nat → B256, List.Forall₂ (fun s w => ρ s = w) kv S ∧ AllHold sp F n ρ fs

theorem Val.mono {sp : Spec} {F n n' : Exec.Deriv} {kv : List Nat} {fs : List Fact}
    {S : List B256} (h : PP n n') (hv : Val sp F n kv fs S) : Val sp F n' kv fs S := by
  obtain ⟨ρ, h1, h2⟩ := hv
  exact ⟨ρ, h1, h2.mono h⟩

theorem Val.sub {sp : Spec} {F n : Exec.Deriv} {kv : List Nat} {fs gs : List Fact}
    {S : List B256} (hsub : ∀ g ∈ gs, g ∈ fs) (hv : Val sp F n kv fs S) :
    Val sp F n kv gs S := by
  obtain ⟨ρ, h1, h2⟩ := hv
  exact ⟨ρ, h1, fun g hg => h2 g (hsub g hg)⟩

theorem Val.filter {sp : Spec} {F n : Exec.Deriv} {kv : List Nat} {fs : List Fact}
    {S : List B256} (p : Fact → Bool) (hv : Val sp F n kv fs S) :
    Val sp F n kv (fs.filter p) S :=
  hv.sub fun _ hg => List.mem_of_mem_filter hg

theorem forall₂_getElem? {ρ : Nat → B256} :
    ∀ {kv : List Nat} {S : List B256}, List.Forall₂ (fun s w => ρ s = w) kv S →
      ∀ {j : Nat} {s : Nat}, kv[j]? = some s → S[j]? = some (ρ s)
  | [], [], _, j, s, h => by simp at h
  | _ :: _, _ :: _, .cons h0 hr, j, s, h => by
    cases j with
    | zero => simp at h ⊢; rw [← h, h0]
    | succ j => simpa using forall₂_getElem? hr (by simpa using h)

theorem forall₂_update_of_not_mem {ρ : Nat → B256} {r : Nat} {w : B256} :
    ∀ {kv : List Nat} {S : List B256}, r ∉ kv →
      List.Forall₂ (fun s x => ρ s = x) kv S →
      List.Forall₂ (fun s x => Function.update ρ r w s = x) kv S
  | [], [], _, _ => .nil
  | s :: kv, _ :: _, hr, .cons h0 hrest => by
    refine .cons ?_ (forall₂_update_of_not_mem (fun h => hr (List.mem_cons_of_mem _ h)) hrest)
    rw [Function.update_of_ne (by rintro rfl; exact hr List.mem_cons_self), h0]

theorem allHold_update {sp : Spec} {F n : Exec.Deriv} {ρ : Nat → B256} {r : Nat} {w : B256}
    {fs : List Fact} (hr : ∀ f ∈ fs, r ∉ f.syms) (hf : AllHold sp F n ρ fs) :
    AllHold sp F n (Function.update ρ r w) fs := fun f hm =>
  Fact.holds_congr (fun s hs => (Function.update_of_ne
    (by rintro rfl; exact hr f hm hs) _ _).symm) (hf f hm)

/-! ## Moving symbols through an instruction's stack transfer -/

section Transfer

variable {kv : List Nat} {S : List B256} {r : Nat} {ρ : Nat → B256}

/-- Index labels read back as the concrete words. -/
def wordOf (S : List B256) (l : Option B256) : Option B256 := l.bind fun j => S[j.toNat]?

theorem indexPattern_map_wordOf (hlen : S.length ≤ 1024) :
    (indexPattern S.length).map (wordOf S) = S.map some := by
  have hφ : wordOf S = label (S.map AVal.const) 0 := by
    funext l
    cases l with
    | none => rfl
    | some j =>
      simp only [wordOf, label, Option.bind_some, List.getElem?_map]
      cases S[j.toNat]? <;> rfl
  have h := indexPattern_map_label (a := S.map AVal.const) (ρ := 0) (by simpa using hlen)
  rw [List.length_map] at h
  rw [hφ, h, List.map_map]
  rfl

theorem transfer_combine_zero (hS : List.Forall₂ (fun s w => ρ s = w) kv S) (hr : r ∉ kv)
    (w : B256) :
    ∀ {out : Pattern} {kv' : List Nat} {S' : List B256},
      out.mapM (fun l => match l with | none => some r | some j => kv[j.toNat]?) = some kv' →
      AbstractStackSafety.Matches (out.map (wordOf S)) S' → out.count none = 0 →
      List.Forall₂ (fun s x => Function.update ρ r w s = x) kv' S'
  | [], kv', S', hm, hM, _ => by
    simp at hm; subst hm
    cases S' with
    | nil => exact .nil
    | cons _ _ => cases hM
  | l :: out, kv', S', hm, hM, hc => by
    cases S' with
    | nil => cases hM
    | cons x S' =>
      rw [List.mapM_cons] at hm
      cases l with
      | none => simp at hc
      | some j =>
        simp only [Option.bind_eq_bind] at hm
        cases hs : kv[j.toNat]? with
        | none => simp [hs] at hm
        | some s =>
          cases ht : out.mapM (fun l => match l with | none => some r | some j => kv[j.toNat]?) with
          | none => simp [hs, ht] at hm
          | some kt =>
            simp [hs, ht] at hm
            subst hm
            have hc' : out.count none = 0 := by simpa [List.count_cons] using hc
            refine .cons ?_ (transfer_combine_zero hS hr w ht hM.2 hc')
            have hw := hM.1
            simp only [List.map_cons, wordOf, Option.bind_some,
              forall₂_getElem? hS hs] at hw
            rw [Function.update_of_ne (by rintro rfl; exact hr (List.mem_of_getElem? hs))]
            exact (AbstractStackSafety.WordMatches.eq_of_some hw).symm

theorem transfer_combine (hS : List.Forall₂ (fun s w => ρ s = w) kv S) (hr : r ∉ kv) :
    ∀ {out : Pattern} {kv' : List Nat} {S' : List B256},
      out.mapM (fun l => match l with | none => some r | some j => kv[j.toNat]?) = some kv' →
      AbstractStackSafety.Matches (out.map (wordOf S)) S' → out.count none ≤ 1 →
      ∃ w, List.Forall₂ (fun s x => Function.update ρ r w s = x) kv' S'
  | [], kv', S', hm, hM, hc => ⟨0, transfer_combine_zero hS hr 0 hm hM (by simp)⟩
  | l :: out, kv', S', hm, hM, hc => by
    cases S' with
    | nil => cases hM
    | cons x S' =>
      have hm0 := hm
      rw [List.mapM_cons] at hm
      cases ht : out.mapM (fun l => match l with | none => some r | some j => kv[j.toNat]?) with
      | none => cases l <;> simp [ht] at hm <;> (split at hm <;> simp at hm)
      | some kt =>
        cases l with
        | none =>
          simp [ht] at hm
          subst hm
          have hc' : out.count none = 0 := by simp [List.count_cons] at hc; omega
          exact ⟨x, .cons (by simp) (transfer_combine_zero hS hr x ht hM.2 hc')⟩
        | some j =>
          cases hs : kv[j.toNat]? with
          | none => simp [hs] at hm
          | some s =>
            simp [hs, ht] at hm
            subst hm
            have hc' : out.count none ≤ 1 := by simp [List.count_cons] at hc; omega
            obtain ⟨w, hw⟩ := transfer_combine hS hr ht hM.2 hc'
            refine ⟨w, .cons ?_ hw⟩
            have hx := hM.1
            simp only [List.map_cons, wordOf, Option.bind_some,
              forall₂_getElem? hS hs] at hx
            rw [Function.update_of_ne (by rintro rfl; exact hr (List.mem_of_getElem? hs))]
            exact (AbstractStackSafety.WordMatches.eq_of_some hx).symm

/-- **Symbols through a transfer.**  A successful instruction whose transfer
the checker accepted leaves, above the untouched `rest`, words carrying the
transferred symbols — the one fresh result under a one-point update. -/
theorem transfer_val {sevm : Sevm} {d d' : Devm} {i : Ninst} {out : Pattern}
    {kv' : List Nat} {rest : List B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hout : ninstTransfer i (indexPattern kv.length) = some out)
    (hlen : kv.length ≤ 1024) (hcount : out.count none ≤ 1)
    (hkv' : out.mapM (fun l => match l with | none => some r | some j => kv[j.toNat]?) = some kv')
    (hr : r ∉ kv) (hS : List.Forall₂ (fun s w => ρ s = w) kv S)
    (hstack : d.stack = S ++ rest) (run : Ninst.Run sevm d i d') :
    ∃ S' w, d'.stack = S' ++ rest ∧
      List.Forall₂ (fun s x => Function.update ρ r w s = x) kv' S' := by
  have hSlen : kv.length = S.length := List.Forall₂.length_eq hS
  rw [hSlen] at hout hlen
  have h1 := ninstTransfer_map (wordOf S) rfl hout
  rw [indexPattern_map_wordOf hlen] at h1
  have h2 := ninstTransfer_append (rest.map some) h1
  have hin : AbstractStackSafety.Matches (S.map some ++ rest.map some) d.stack := by
    rw [hstack]; exact matches_append (matches_some_map S) (matches_some_map rest)
  have h3 := ninstTransfer_run hfork hin h2 run
  obtain ⟨S', s2, hsp, hM, hrest⟩ := matches_split h3
  rw [matches_some_map_eq hrest] at hsp
  obtain ⟨w, hw⟩ := transfer_combine hS hr hkv' hM hcount
  exact ⟨S', w, hsp, hw⟩

end Transfer

/-! ## Concrete results of the instructions with fact rules -/

section Ops

theorem binary_top {f : B256 → B256 → B256} {c : Nat} {d d' : Devm}
    (h : applyBinary f c d = .ok d') {x y : B256} {rest : List B256}
    (hs : d.stack = x :: y :: rest) : d'.stack = f x y :: rest := by
  obtain ⟨x', y', hd⟩ := Devm.diffBurn_of_applyBinary h
  obtain ⟨s1, hpop, hpush⟩ := hd.stack
  simp only [Stack.Pop, Stack.Push, Split] at hpop hpush
  rw [hs] at hpop
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hpop
  obtain ⟨rfl, rfl, rfl⟩ := hpop
  simpa using hpush

theorem unary_top {f : B256 → B256} {c : Nat} {d d' : Devm}
    (h : applyUnary f c d = .ok d') {x : B256} {rest : List B256}
    (hs : d.stack = x :: rest) : d'.stack = f x :: rest := by
  obtain ⟨x', hd⟩ := Devm.diffBurn_of_applyUnary h
  obtain ⟨s1, hpop, hpush⟩ := hd.stack
  simp only [Stack.Pop, Stack.Push, Split] at hpop hpush
  rw [hs] at hpop
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hpop
  obtain ⟨rfl, rfl⟩ := hpop
  simpa using hpush

variable {sevm : Sevm} {d d' : Devm} {x y : B256} {rest : List B256}

theorem run_add_top (run : Ninst.Run sevm d (.reg .add) d') (hs : d.stack = x :: y :: rest) :
    d'.stack = (x + y) :: rest := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact binary_top run hs

theorem run_gt_top (run : Ninst.Run sevm d (.reg .gt) d') (hs : d.stack = x :: y :: rest) :
    d'.stack = B256.gtCheck x y :: rest := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact binary_top run hs

theorem run_eq_top (run : Ninst.Run sevm d (.reg .eq) d') (hs : d.stack = x :: y :: rest) :
    d'.stack = B256.eqCheck x y :: rest := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact binary_top run hs

theorem run_xor_top (run : Ninst.Run sevm d (.reg .xor) d') (hs : d.stack = x :: y :: rest) :
    d'.stack = B256.xor x y :: rest := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact binary_top run hs

theorem run_iszero_top (run : Ninst.Run sevm d (.reg .iszero) d') (hs : d.stack = x :: rest) :
    d'.stack = B256.eqCheck x 0 :: rest := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact unary_top run hs

theorem run_sload_top (run : Ninst.Run sevm d (.reg .sload) d') (hs : d.stack = x :: rest) :
    d'.stack = lockAt sevm.currentTarget x d :: rest := by
  obtain ⟨x', s1, hpop, hpush⟩ := of_run_sload run
  simp only [Stack.Pop, Stack.Push, Split] at hpop hpush
  rw [hs] at hpop
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hpop
  obtain ⟨rfl, rfl⟩ := hpop
  rw [hpush]
  rfl

theorem B256.xor_self' (x : B256) : B256.xor x x = 0 := by
  rcases x with ⟨⟨a, b⟩, ⟨c, e⟩⟩
  show ((a ^^^ a, b ^^^ b), (c ^^^ c, e ^^^ e)) = 0
  simp only [UInt64.xor_self]
  rfl

theorem B256.one_ne_zero' : (1 : B256) ≠ 0 := by
  decide

end Ops

/-! ## The fact rules are sound -/

section OpFacts

variable {sp : Spec} {F n n' : Exec.Deriv} {ρ : Nat → B256} {fs : List Fact} {r : Nat}
  {w : B256}

theorem toNat_add_of_le {x y : B256} {a b : Nat} (hx : x.toNat ≤ a) (hy : y.toNat ≤ b)
    (hab : a + b ≤ maxW) : (x + y).toNat = x.toNat + y.toNat := by
  rw [B256.toNat_add, Nat.lo_eq_of_lt]
  unfold maxW at hab
  omega

/-- The facts a rule attaches to the fresh result hold once the result is its
concrete value. -/
theorem opFacts_sound {kv : List Nat} {S rest : List B256} {i : Ninst}
    (hf : AllHold sp F n ρ fs) (hr : r ∉ kv)
    (hS : List.Forall₂ (fun s w => ρ s = w) kv S) (hstack : n.devm.stack = S ++ rest)
    (run : Ninst.Run n.sevm n.devm i n'.devm) (reach : PP F n) (edge : Exec.Deriv.ParentStep n' n)
    (htop : n'.devm.stack.head? = some w)
    (hhash : i = .reg .keccak256 → n'.devm.stack.head? ≠ some sp.slot) :
    AllHold sp F n' (Function.update ρ r w) (opFacts sp fs kv i r) := by
  have hnn : PP n n' := .step edge (.refl _)
  have hsevm : n.sevm = F.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq reach
  have upd : ∀ s ∈ kv, Function.update ρ r w s = ρ s := fun s hs =>
    Function.update_of_ne (by rintro rfl; exact hr hs) _ _
  have hwr : Function.update ρ r w r = w := by simp
  -- the top two input words
  have two : ∀ {x y : Nat} {kt : List Nat}, kv = x :: y :: kt →
      ∃ St, n.devm.stack = ρ x :: ρ y :: St := by
    intro x y kt hk
    subst hk
    cases hS with
    | cons h0 h1 =>
      cases h1 with
      | cons h1 _ => exact ⟨_, by rw [hstack, ← h0, ← h1]; rfl⟩
  have one : ∀ {x : Nat} {kt : List Nat}, kv = x :: kt → ∃ St, n.devm.stack = ρ x :: St := by
    intro x kt hk
    subst hk
    cases hS with
    | cons h0 _ => exact ⟨_, by rw [hstack, ← h0]; rfl⟩
  have headOf : ∀ {v : B256} {St : List B256}, n'.devm.stack = v :: St → w = v := by
    intro v St h
    rw [h] at htop
    simp at htop
    exact htop.symm
  intro f hm
  cases i with
  | push _ _ => simp [opFacts] at hm
  | exec _ => simp [opFacts] at hm
  | dupn _ => simp [opFacts] at hm
  | swapn _ => simp [opFacts] at hm
  | exchange _ => simp [opFacts] at hm
  | reg rr =>
  cases rr
  all_goals first | (simp [opFacts] at hm; done) | skip
  case sload =>
    rcases kv with _ | ⟨x, kt⟩
    · simp [opFacts] at hm
    simp only [opFacts] at hm
    split at hm
    · rename_i hc
      simp only [List.mem_singleton] at hm
      subst hm
      obtain ⟨St, hst⟩ := one rfl
      have hv := headOf (run_sload_top run hst)
      refine ⟨n, reach, hnn, ?_⟩
      rw [hwr, hv, constOf_sound' hf hc, hsevm]
    · cases hm
  case eq =>
    rcases kv with _ | ⟨x, _ | ⟨y, kt⟩⟩
    · simp [opFacts] at hm
    · simp [opFacts] at hm
    simp only [opFacts] at hm
    split at hm
    · rename_i hc
      simp only [List.mem_singleton] at hm
      subst hm
      obtain ⟨St, hst⟩ := two rfl
      have hv := headOf (run_eq_top run hst)
      intro h0
      rw [hwr, hv] at h0
      have hne : ρ x ≠ ρ y := by
        intro he
        simp [B256.eqCheck, he] at h0
        exact B256.one_ne_zero' h0
      simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem,
        decide_eq_true_eq] at hc
      rcases hc with ⟨hl, hk⟩ | ⟨hl, hk⟩
      · obtain ⟨m, h1, h2, h3⟩ := hf _ hl
        refine ⟨m, h1, h2.trans hnn, ?_⟩
        rw [← h3, ← constOf_sound' hf hk]
        exact hne
      · obtain ⟨m, h1, h2, h3⟩ := hf _ hl
        refine ⟨m, h1, h2.trans hnn, ?_⟩
        rw [← h3, ← constOf_sound' hf hk]
        exact fun h => hne h.symm
    · cases hm
  case keccak256 =>
    simp only [opFacts, List.mem_singleton] at hm
    subst hm
    show Function.update ρ r w r ≠ sp.slot
    rw [hwr]
    intro h
    exact hhash rfl (by rw [htop, h])
  case add =>
    rcases kv with _ | ⟨x, _ | ⟨y, kt⟩⟩
    · simp [opFacts] at hm
    · simp [opFacts] at hm
    obtain ⟨St, hst⟩ := two rfl
    have hv := headOf (run_add_top run hst)
    have hx := bnd2_sound hf x
    have hy := bnd2_sound hf y
    simp only [opFacts, addFacts, List.mem_append] at hm
    rcases hm with (hm | hm) | hm
    · split at hm
      · rename_i hle
        simp only [List.mem_singleton] at hm
        subst hm
        show _ ≤ (Function.update ρ r w r).toNat ∧ (Function.update ρ r w r).toNat ≤ _
        rw [hwr, hv, toNat_add_of_le hx.2 hy.2 hle]
        omega
      · cases hm
    · split at hm
      · rename_i hc
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
        obtain ⟨htk, hlt⟩ := List.mem_filter.mp ht
        have hlt' := entails_sound hf hlt
        simp only [Fact.Holds] at hlt'
        have h1 := constOf_sound hf hc
        have := B256.toNat_lt (ρ t)
        show (Function.update ρ r w r).toNat ≤ (Function.update ρ r w t).toNat
        rw [hwr, upd t htk, hv, B256.toNat_add, Nat.lo_eq_of_lt (by omega)]
        omega
      · cases hm
    · split at hm
      · rename_i hc
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
        obtain ⟨htk, hlt⟩ := List.mem_filter.mp ht
        have hlt' := entails_sound hf hlt
        simp only [Fact.Holds] at hlt'
        have h1 := constOf_sound hf hc
        have := B256.toNat_lt (ρ t)
        show (Function.update ρ r w r).toNat ≤ (Function.update ρ r w t).toNat
        rw [hwr, upd t htk, hv, B256.toNat_add, Nat.lo_eq_of_lt (by omega)]
        omega
      · cases hm
  case gt =>
    rcases kv with _ | ⟨x, _ | ⟨y, kt⟩⟩
    · simp [opFacts] at hm
    · simp [opFacts] at hm
    simp only [opFacts] at hm
    split at hm
    · rename_i k hc
      simp only [List.mem_singleton] at hm
      subst hm
      obtain ⟨St, hst⟩ := two rfl
      have hv := headOf (run_gt_top run hst)
      have hk := constOf_sound hf hc
      show (_ = 0 → _) ∧ (_ ≠ 0 → _)
      rw [hwr, upd x (by simp), hv]
      unfold B256.gtCheck
      by_cases hlt : ρ x > ρ y
      · have := B256.lt_iff_toNat_lt_toNat.mp hlt
        simp only [hlt, ite_true]
        exact ⟨fun h => (B256.one_ne_zero' h).elim, fun _ => by omega⟩
      · have : ¬ (ρ y).toNat < (ρ x).toNat := fun h =>
          hlt (B256.lt_iff_toNat_lt_toNat.mpr h)
        simp only [hlt, ite_false]
        exact ⟨fun _ => by omega, fun h => (h rfl).elim⟩
    · cases hm
  case iszero =>
    rcases kv with _ | ⟨x, kt⟩
    · simp [opFacts] at hm
    simp only [opFacts, List.mem_singleton] at hm
    subst hm
    obtain ⟨St, hst⟩ := one rfl
    have hv := headOf (run_iszero_top run hst)
    show (_ = 0 → _) ∧ (_ ≠ 0 → _)
    rw [hwr, upd x (by simp), hv]
    unfold B256.eqCheck
    by_cases h0 : ρ x = 0
    · simp only [h0, ite_true]
      exact ⟨fun h => (B256.one_ne_zero' h).elim, fun _ => trivial⟩
    · simp only [h0, ite_false]
      exact ⟨fun _ => h0, fun h => (h rfl).elim⟩
  case xor =>
    rcases kv with _ | ⟨x, _ | ⟨y, kt⟩⟩
    · simp [opFacts] at hm
    · simp [opFacts] at hm
    simp only [opFacts, List.mem_singleton] at hm
    subst hm
    obtain ⟨St, hst⟩ := two rfl
    have hv := headOf (run_xor_top run hst)
    show _ ≠ 0 → _ ≠ _
    rw [hwr, upd x (by simp), upd y (by simp), hv]
    intro h he
    rw [he, B256.xor_self'] at h
    exact h rfl

end OpFacts

end Blanc.Lift.LockCheck
