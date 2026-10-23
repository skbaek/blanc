import Blanc.Lift.Sound

/-!
# Symbols through a stack transfer (shared by the symbolic checkers)

Checker-independent lemmas about symbol valuations `ρ : Nat → B256` carried by
concrete words (`List.Forall₂ (fun s w => ρ s = w) kv S`), moved through an
instruction's index-label transfer (`ninstTransfer` over `indexPattern`), and the
concrete top word of the instructions the checkers attach facts to.  Hoisted from
the reentrancy-lock checker's soundness (`Blanc/Lift/LockCheckSound.lean`) so that
the free-pointer and write-site checkers reuse them unchanged; nothing here
mentions a checker's fact or state type.
-/

namespace Blanc.Lift.SymTransfer

open Jaune AbstractStackSafety

/-! ## Fresh symbols -/

theorem le_foldr_max {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons y l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)


/-- A member of the leading list is below the fresh symbol `(kv ++ m).foldr max 0 + 1`. -/
theorem lt_fresh_kv {kv m : List Nat} {s : Nat} (h : s ∈ kv) :
    s < (kv ++ m).foldr max 0 + 1 :=
  Nat.lt_succ_of_le (le_foldr_max (List.mem_append_left _ h))

/-! ## Valuations along a word list -/

theorem forall₂_getElem? {ρ : Nat → B256} :
    ∀ {kv : List Nat} {S : List B256}, List.Forall₂ (fun s w => ρ s = w) kv S →
      ∀ {j : Nat} {s : Nat}, kv[j]? = some s → S[j]? = some (ρ s)
  | [], [], _, j, s, h => by simp only [List.length_nil, not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at h
  | _ :: _, _ :: _, .cons h0 hr, j, s, h => by
    cases j with
    | zero => simp only [List.length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, List.getElem_cons_zero, Option.some.injEq] at h ⊢; rw [← h, h0]
    | succ j => simpa only [List.getElem?_cons_succ] using forall₂_getElem? hr (by simpa only [List.getElem?_cons_succ] using h)

theorem forall₂_update_of_not_mem {ρ : Nat → B256} {r : Nat} {w : B256} :
    ∀ {kv : List Nat} {S : List B256}, r ∉ kv →
      List.Forall₂ (fun s x => ρ s = x) kv S →
      List.Forall₂ (fun s x => Function.update ρ r w s = x) kv S
  | [], [], _, _ => .nil
  | s :: kv, _ :: _, hr, .cons h0 hrest => by
    refine .cons ?_ (forall₂_update_of_not_mem (fun h => hr (List.mem_cons_of_mem _ h)) hrest)
    rw [Function.update_of_ne (by rintro rfl; exact hr List.mem_cons_self), h0]

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
  have h := indexPattern_map_label (a := S.map AVal.const) (ρ := 0) (by simpa only [List.length_map] using
    hlen)
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
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq, List.nil_eq] at hm; subst hm
    cases S' with
    | nil => exact .nil
    | cons _ _ => cases hM
  | l :: out, kv', S', hm, hM, hc => by
    cases S' with
    | nil => cases hM
    | cons x S' =>
      rw [List.mapM_cons] at hm
      cases l with
      | none => simp only [List.count_cons_self, Nat.add_eq_zero_iff, one_ne_zero, and_false] at hc
      | some j =>
        simp only [Option.bind_eq_bind] at hm
        cases hs : kv[j.toNat]? with
        | none => simp only [hs, Option.pure_def, Option.bind_none, reduceCtorEq] at hm
        | some s =>
          cases ht : out.mapM (fun l => match l with | none => some r | some j => kv[j.toNat]?) with
          | none => simp only [hs, ht, Option.pure_def, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hm
          | some kt =>
            simp only [hs, ht, Option.pure_def, Option.bind_some, Option.some.injEq] at hm
            subst hm
            have hc' : out.count none = 0 := by simpa only [ne_eq, reduceCtorEq, not_false_eq_true,
              List.count_cons_of_ne] using hc
            refine .cons ?_ (transfer_combine_zero hS hr w ht hM.2 hc')
            have hw := hM.1
            simp only [wordOf, Option.bind_some,
              forall₂_getElem? hS hs] at hw
            rw [Function.update_of_ne (by rintro rfl; exact hr (List.mem_of_getElem? hs))]
            exact (AbstractStackSafety.WordMatches.eq_of_some hw).symm

theorem transfer_combine (hS : List.Forall₂ (fun s w => ρ s = w) kv S) (hr : r ∉ kv) :
    ∀ {out : Pattern} {kv' : List Nat} {S' : List B256},
      out.mapM (fun l => match l with | none => some r | some j => kv[j.toNat]?) = some kv' →
      AbstractStackSafety.Matches (out.map (wordOf S)) S' → out.count none ≤ 1 →
      ∃ w, List.Forall₂ (fun s x => Function.update ρ r w s = x) kv' S'
  | [], kv', S', hm, hM, hc => ⟨0, transfer_combine_zero hS hr 0 hm hM (by simp only [List.count_nil])⟩
  | l :: out, kv', S', hm, hM, hc => by
    cases S' with
    | nil => cases hM
    | cons x S' =>
      have hm0 := hm
      rw [List.mapM_cons] at hm
      cases ht : out.mapM (fun l => match l with | none => some r | some j => kv[j.toNat]?) with
      | none => cases l <;> simp only [ht, Option.pure_def, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hm
      | some kt =>
        cases l with
        | none =>
          simp only [ht, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hm
          subst hm
          have hc' : out.count none = 0 := by simp only [List.count_cons_self, add_le_iff_nonpos_left, nonpos_iff_eq_zero] at hc; omega
          exact ⟨x, .cons (by simp only [Function.update_self]) (transfer_combine_zero hS hr x ht hM.2 hc')⟩
        | some j =>
          cases hs : kv[j.toNat]? with
          | none => simp only [hs, Option.pure_def, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hm
          | some s =>
            simp only [hs, ht, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hm
            subst hm
            have hc' : out.count none ≤ 1 := by simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.count_cons_of_ne] at hc; omega
            obtain ⟨w, hw⟩ := transfer_combine hS hr ht hM.2 hc'
            refine ⟨w, .cons ?_ hw⟩
            have hx := hM.1
            simp only [wordOf, Option.bind_some,
              forall₂_getElem? hS hs] at hx
            rw [Function.update_of_ne (by rintro rfl; exact hr (List.mem_of_getElem? hs))]
            exact (AbstractStackSafety.WordMatches.eq_of_some hx).symm

/-- **Symbols through a transfer.**  A successful instruction whose transfer
the checker accepted leaves, above the untouched `rest`, words carrying the
transferred symbols — the one fresh result under a one-point update. -/
theorem transfer_val_noStateGas {sevm : Sevm} {d d' : Devm} {i : Ninst} {out : Pattern}
    {kv' : List Nat} {rest : List B256} (hfork : sevm.benvStat.rules.stateGas = none)
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
  have h3 := ninstTransfer_run_noStateGas hfork hin h2 run
  obtain ⟨S', s2, hsp, hM, hrest⟩ := matches_split h3
  rw [matches_some_map_eq hrest] at hsp
  obtain ⟨w, hw⟩ := transfer_combine hS hr hkv' hM hcount
  exact ⟨S', w, hsp, hw⟩

theorem transfer_val {sevm : Sevm} {d d' : Devm} {i : Ninst} {out : Pattern}
    {kv' : List Nat} {rest : List B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hout : ninstTransfer i (indexPattern kv.length) = some out)
    (hlen : kv.length ≤ 1024) (hcount : out.count none ≤ 1)
    (hkv' : out.mapM (fun l => match l with | none => some r | some j => kv[j.toNat]?) = some kv')
    (hr : r ∉ kv) (hS : List.Forall₂ (fun s w => ρ s = w) kv S)
    (hstack : d.stack = S ++ rest) (run : Ninst.Run sevm d i d') :
    ∃ S' w, d'.stack = S' ++ rest ∧
      List.Forall₂ (fun s x => Function.update ρ r w s = x) kv' S' :=
  transfer_val_noStateGas hfork.rules_stateGas_none hout hlen hcount hkv' hr hS hstack run

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
  simpa only [List.cons_append, List.nil_append] using hpush

theorem unary_top {f : B256 → B256} {c : Nat} {d d' : Devm}
    (h : applyUnary f c d = .ok d') {x : B256} {rest : List B256}
    (hs : d.stack = x :: rest) : d'.stack = f x :: rest := by
  obtain ⟨x', hd⟩ := Devm.diffBurn_of_applyUnary h
  obtain ⟨s1, hpop, hpush⟩ := hd.stack
  simp only [Stack.Pop, Stack.Push, Split] at hpop hpush
  rw [hs] at hpop
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hpop
  obtain ⟨rfl, rfl⟩ := hpop
  simpa only [List.cons_append, List.nil_append] using hpush

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

theorem B256.one_ne_zero' : (1 : B256) ≠ 0 := by
  decide

theorem toNat_add_of_le {x y : B256} {a b : Nat} (hx : x.toNat ≤ a) (hy : y.toNat ≤ b)
    (hab : a + b ≤ 2 ^ 256 - 1) : (x + y).toNat = x.toNat + y.toNat := by
  rw [B256.toNat_add, Nat.lo_eq_of_lt]
  omega

theorem run_sub_top (run : Ninst.Run sevm d (.reg .sub) d') (hs : d.stack = x :: y :: rest) :
    d'.stack = (x - y) :: rest := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact binary_top run hs

theorem run_mul_top (run : Ninst.Run sevm d (.reg .mul) d') (hs : d.stack = x :: y :: rest) :
    d'.stack = (x * y) :: rest := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact binary_top run hs

theorem run_div_top (run : Ninst.Run sevm d (.reg .div) d') (hs : d.stack = x :: y :: rest) :
    d'.stack = (x / y) :: rest := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact binary_top run hs

theorem run_and_top (run : Ninst.Run sevm d (.reg .and) d') (hs : d.stack = x :: y :: rest) :
    d'.stack = (x &&& y) :: rest := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact binary_top run hs

theorem run_or_top (run : Ninst.Run sevm d (.reg .or) d') (hs : d.stack = x :: y :: rest) :
    d'.stack = (x ||| y) :: rest := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact binary_top run hs

theorem run_shr_top (run : Ninst.Run sevm d (.reg .shr) d') (hs : d.stack = x :: y :: rest) :
    d'.stack = (y >>> x.toNat) :: rest := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  split at run
  · exact binary_top run hs
  · cases run

theorem run_lt_top (run : Ninst.Run sevm d (.reg .lt) d') (hs : d.stack = x :: y :: rest) :
    d'.stack = B256.ltCheck x y :: rest := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact binary_top run hs

theorem run_msize_top (run : Ninst.Run sevm d (.reg .msize) d') :
    d'.stack = d.memory.size.toB256 :: d.stack := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  have h := (Devm.pushBurn_of_pushItem run).stack
  simpa only [Stack.Push, Split, List.singleton_append, List.cons_append, List.nil_append] using h

end Ops

end Blanc.Lift.SymTransfer
