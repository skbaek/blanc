import Blanc.Lift.WriteSiteStep

/-!
# W3: the joins of the write-site checker are sound

Companion of `Blanc/Lift/WriteSiteStep.lean` (one non-jump step): a `JUMPI` arm (`refine`), a
popped jump (`popped`), an annotation met at a goto, loop head or join (`compat`), a callee's
entry (`WSt.param`) and return (`retOk`), the call continuation (`resume`), and a callee's
instantiated sites (`instSite`).  Each is stated over `WSt.Holds`/`WSt.Sat` so that the tree-level
induction (W4) never unfolds the checker.  Contract-neutral.
-/

namespace Blanc.Lift.WriteSite

open Jaune AbstractStackSafety Blanc.Lift.SymTransfer
open Blanc.Lift.FreePtr (Fact AllHold)

variable {ε : Env} {sevm : Sevm} {ν : Nat → B256} {σ : WSt} {S rest : List B256} {d d' : Devm}

/-! ## Popping the top words -/

/-- A `PopBurn` keeps memory and storage, so a state's meaning survives it. -/
theorem WSt.Holds.popBurn {xs : List B256} (h : σ.Holds ε sevm ν S d)
    (hp : Devm.PopBurn xs d d') : σ.Holds ε sevm ν S d' :=
  h.of_keep (.of_eq hp.memory) (by
    show ((d'.state.get _).stor) = ((d.state.get _).stor)
    rw [hp.state])

theorem popBurn_stack {xs : List B256} (hp : Devm.PopBurn xs d d') : d.stack = xs ++ d'.stack := by
  have h := hp.stack
  simp only [Stack.Pop, Split] at h
  exact h

theorem forall₂_map_self (ν : Nat → B256) :
    ∀ l : List Nat, List.Forall₂ (fun s w => ν s = w) l (l.map ν)
  | [] => .nil
  | _ :: l => .cons rfl (forall₂_map_self ν l)

/-! ## Branches -/

theorem B256.eq_of_eqCheck_ne_zero {a b : B256} (h : B256.eqCheck a b ≠ 0) : a = b := by
  unfold B256.eqCheck at h
  split at h
  · assumption
  · exact absurd rfl h

/-- The guard a nonzero `EQ` result gives holds. -/
theorem eqGuard_sound {t u : Term} {a b : B256} {g : Term × B256} (hab : a = b)
    (ht : t.Den ε a) (hu : u.Den ε b) (hg : eqGuard t u = some g) : g.1.Den ε g.2 := by
  unfold eqGuard at hg
  split at hg
  · rename_i t' k
    split at hg
    · rename_i hk
      cases hg
      intro _
      show k = t.eval ε
      rw [← ht hk, hab]
      exact (hu rfl).symm
    · cases hg
  · rename_i k t'
    split at hg
    · rename_i hk
      cases hg
      intro _
      show k = _
      rw [← hu hk, ← hab]
      exact (ht rfl).symm
    · cases hg
  · cases hg

/-- **A `JUMPI` arm is sound**: on the arm taken (the condition word zero, or nonzero), the refined
state holds of the machine after the two pops. -/
theorem refine_sound {t c : Nat} {kv : List Nat} {dw cw : B256} {zero : Bool}
    (h : σ.Holds ε sevm ν S d) (hS : d.stack = S ++ rest) (hkv : σ.kv = t :: c :: kv)
    (hp : Devm.PopBurn [dw, cw] d d') (hz : zero = true → cw = 0) (hnz : zero = false → cw ≠ 0) :
    (refine σ c kv zero).Sat ε sevm d' rest := by
  have h1 := popBurn_stack hp
  rw [hS, forall₂_eq_map h.kv, hkv] at h1
  simp only [List.map_cons, List.cons_append, List.nil_append, List.cons.injEq] at h1
  obtain ⟨-, hc, hrest⟩ := h1
  have hp' := h.popBurn hp
  refine ⟨ν, kv.map ν, hrest.symm, WSt.Holds.prune ⟨forall₂_map_self ν kv, hp'.args, ?_, hp'.prov, hp'.mem, hp'.cur,
    hp'.ub, hp'.eqs, ?_⟩⟩
  · have hr := FreePtr.refineFacts_sound h.facts (fun hz' => by rw [hc]; exact hz hz')
      (fun hnz' => by rw [hc]; exact hnz hnz')
    exact (FreePtr.learn1_sound hr (FreePtr.zeros_sound hr) (FreePtr.ones_sound hr)).append hr
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · cases zero with
      | true => cases hg
      | false =>
        obtain ⟨e, he, hge⟩ := List.mem_filterMap.mp hg
        split at hge
        · rename_i hec
          obtain ⟨a, b, hν, ha, hb⟩ := h.eqs e he
          have hab : a = b := B256.eq_of_eqCheck_ne_zero (by
            rw [← hν, hec, hc]; exact hnz rfl)
          exact eqGuard_sound hab ha hb hge
        · cases hge
    · exact h.guards g hg

/-- **A popped jump is sound** (`JUMP` to a goto, the `.ret` pop): the state over the remaining
frame words holds after the pop. -/
theorem popped_sound {t : Nat} {kv : List Nat} {dw : B256}
    (h : σ.Holds ε sevm ν S d) (hS : d.stack = S ++ rest) (hkv : σ.kv = t :: kv)
    (hp : Devm.PopBurn [dw] d d') : (popped σ kv).Sat ε sevm d' rest := by
  have h1 := popBurn_stack hp
  rw [hS, forall₂_eq_map h.kv, hkv] at h1
  simp only [List.map_cons, List.cons_append, List.nil_append, List.cons.injEq] at h1
  have hp' := h.popBurn hp
  exact ⟨ν, kv.map ν, h1.2.symm, WSt.Holds.prune ⟨forall₂_map_self ν kv, hp'.args, hp'.facts, hp'.prov, hp'.mem,
    hp'.cur, hp'.ub, hp'.eqs, hp'.guards⟩⟩

/-! ## Annotations: gotos, loop heads, joins -/

theorem forall₂_of_zip' {m : Nat → Nat} :
    ∀ {as ss : List Nat} {S : List B256}, as.length = ss.length →
      (∀ p ∈ as.zip ss, m p.1 = p.2) → List.Forall₂ (fun s w => ν s = w) ss S →
      List.Forall₂ (fun a w => ν (m a) = w) as S
  | [], [], [], _, _, _ => .nil
  | a :: as, s :: ss, w :: S, hl, hz, .cons h0 hr => by
    refine .cons ?_ (forall₂_of_zip' (Nat.succ.inj hl)
      (fun p hp => hz p (List.mem_cons_of_mem _ hp)) hr)
    rw [hz (a, s) List.mem_cons_self]
    exact h0
  | [], _ :: _, _, hl, _, _ => by cases hl
  | _ :: _, [], _, hl, _, _ => by cases hl

/-- The prefix form of `map_of_zip`: a shorter annotation list names a prefix. -/
theorem map_of_zip_prefix {m : Nat → Nat} :
    ∀ {as ss : List Nat}, as.length ≤ ss.length → (∀ p ∈ as.zip ss, m p.1 = p.2) →
      as.map (ν ∘ m) <+: ss.map ν
  | [], _, _, _ => List.nil_prefix
  | a :: as, s :: ss, hl, hz => by
    rw [List.map_cons, List.map_cons, Function.comp_apply, hz (a, s) List.mem_cons_self]
    exact List.prefix_cons_inj _ |>.mpr (map_of_zip_prefix (Nat.le_of_succ_le_succ hl)
      (fun p hp => hz p (List.mem_cons_of_mem _ hp)))
  | _ :: _, [], hl, _ => by cases hl

theorem map_of_zip {m : Nat → Nat} :
    ∀ {as ss : List Nat}, as.length = ss.length → (∀ p ∈ as.zip ss, m p.1 = p.2) →
      as.map (ν ∘ m) = ss.map ν
  | [], [], _, _ => rfl
  | a :: as, s :: ss, hl, hz => by
    rw [List.map_cons, List.map_cons, map_of_zip (Nat.succ.inj hl)
      (fun p hp => hz p (List.mem_cons_of_mem _ hp))]
    rw [Function.comp_apply, hz (a, s) List.mem_cons_self]
  | [], _ :: _, hl, _ => by cases hl
  | _ :: _, [], hl, _ => by cases hl

/-- **An accepted join is sound**: an incoming state passing `compat σ A` makes the annotation
`A` hold of the same machine state under the renamed valuation `ν ∘ symMap A σ`. -/
theorem compat_sound {A : WSt} (hc : compat σ A = true) (h : σ.Holds ε sevm ν S d) :
    A.Holds ε sevm (ν ∘ symMap A σ) S d := by
  unfold compat at hc
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem,
    Bool.or_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl1, hl2⟩, hzip⟩, -⟩, hfacts⟩, hprov⟩, hmem⟩, hcur⟩, hub⟩, heqs⟩, hguards⟩ := hc
  rw [decide_eq_true_eq] at hl2
  rw [List.zip_append hl1.symm] at hzip
  have hz1 : ∀ p ∈ A.kv.zip σ.kv, symMap A σ p.1 = p.2 :=
    fun p hp => hzip p (List.mem_append_left _ hp)
  have hz2 : ∀ p ∈ A.args.zip σ.args, symMap A σ p.1 = p.2 :=
    fun p hp => hzip p (List.mem_append_right _ hp)
  refine ⟨forall₂_of_zip' (m := symMap A σ) hl1.symm hz1 h.kv,
    (map_of_zip_prefix (m := symMap A σ) hl2 hz2).trans h.args, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · exact fun f hf => FreePtr.Fact.holds_rename.mp (FreePtr.entails_sound h.facts (hfacts f hf))
  · intro p hp
    rcases hprov p hp with hk | hk
    · intro hk'; rw [hk] at hk'; cases hk'
    · have := h.provOf (symMap A σ p.1)
      rw [hk] at this
      exact this
  · intro p hp
    exact h.mem (p.1, symMap A σ p.2) (hmem p hp)
  · intro p hp
    exact h.cur (symMap A σ p.1, p.2) (hcur p hp)
  · intro p hp
    rcases hub p hp with hu | hu
    · exact h.ub (symMap A σ p.1, p.2) hu
    · show (ν (symMap A σ p.1)).toNat ≤ _
      rw [← h.cur (symMap A σ p.1, p.2) hu]
  · intro e he
    exact h.eqs (symMap A σ e.1, e.2.1, e.2.2) (heqs e he)
  · exact fun g hg => h.guards g (hguards g hg)

/-- The `Sat` form of `compat_sound`. -/
theorem compat_sat {A : WSt} (hc : compat σ A = true) (h : σ.Sat ε sevm d rest) :
    A.Sat ε sevm d rest := by
  obtain ⟨ν, S, hS, h⟩ := h
  exact ⟨_, S, hS, compat_sound hc h⟩

/-! ## Calls -/

/-- **What a callee's return establishes**, read in the callee's environment `ε` (its entry words):
the returned words `W` (top first) are as many as the summary's terms, each is what its term
says, and each order fact `(j, i)` puts returned word `j` below entry word `i`. -/
def WRet.Holds (ε : Env) (R : WRet) (W : List B256) : Prop :=
  W.length = R.prov.length ∧ (∀ (j : Nat) (t : Term) (w : B256), R.prov[j]? = some t → W[j]? = some w → t.Den ε w) ∧
    ∀ p ∈ R.les, ∃ w a, W[p.1]? = some w ∧ ε.args[p.2]? = some a ∧ w.toNat ≤ a.toNat

/-- The callee's environment at a call: the caller's frame constants and the words `W`. -/
def Env.callee (ε : Env) (W : List B256) : Env := ⟨ε.caller, ε.self, ε.data, W⟩

theorem Env.Frame.callee {W : List B256} (h : ε.Frame sevm) : (ε.callee W).Frame sevm := h

theorem Env.callee_glob (W : List B256) :
    (ε.callee W).caller = ε.caller ∧ (ε.callee W).self = ε.self ∧ (ε.callee W).data = ε.data :=
  ⟨rfl, rfl, rfl⟩

/-- The caller's terms for the callee's entry words describe them. -/
theorem WSt.Holds.pa (h : σ.Holds ε sevm ν S d) (cw : List Nat) :
    ∀ (i : Nat) (u : Term), (cw.map σ.provOf)[i]? = some u → u.known = true →
      (ε.callee (cw.map ν)).args[i]? = some (u.eval ε) := by
  intro i u hu hk
  show (cw.map ν)[i]? = _
  rw [List.getElem?_map] at hu ⊢
  cases hc : cw[i]? with
  | none => rw [hc] at hu; cases hu
  | some s =>
    rw [hc] at hu
    cases hu
    rw [Option.map_some, h.provOf s hk]

/-- **A callee's entry is sound**: the words `W` on top of the stack are the callee's parameters,
read in the callee's environment. -/
theorem param_sat {W : List B256} (hd : d.stack = W ++ rest) :
    (WSt.param W.length).Sat (ε.callee W) sevm d rest := by
  let ν0 : Nat → B256 := fun s => W.getD (s - 1) 0
  have hmap : ((List.range W.length).map (· + 1)).map ν0 = W := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, ν0, Nat.add_sub_cancel,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
  have hkv : List.Forall₂ (fun s w => ν0 s = w) ((List.range W.length).map (· + 1)) W := by
    have := forall₂_map_self ν0 ((List.range W.length).map (· + 1))
    rwa [hmap] at this
  refine ⟨ν0, W, hd, hkv, (show ((List.range W.length).map (· + 1)).map ν0 <+: W by
      rw [hmap]),
    (fun _ hf => by cases hf), ?_,
    (fun _ hp => by cases hp),
    (fun _ hp => by cases hp), (fun _ hp => by cases hp), (fun _ hp => by cases hp),
    (fun _ hp => by cases hp)⟩
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  intro _
  show W.getD (i + 1 - 1) 0 = W.getD i 0
  rw [Nat.add_sub_cancel]

/-- The frame's entry state holds of any machine state, in the frame's root environment. -/
theorem init_sat (sevm : Sevm) (d : Devm) : WSt.init.Sat (Env.root sevm) sevm d d.stack :=
  param_sat (ε := Env.root sevm) (W := []) (rest := d.stack) rfl

theorem zip_mem_of_getElem? {α β : Type} :
    ∀ {l : List α} {l' : List β} {j : Nat} {a : α} {b : β},
      l[j]? = some a → l'[j]? = some b → (a, b) ∈ l.zip l'
  | _ :: _, _ :: _, 0, _, _, ha, hb => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
    subst ha hb
    exact List.mem_cons_self
  | _ :: l, _ :: l', j + 1, _, _, ha, hb => by
    simp only [List.getElem?_cons_succ] at ha hb
    exact List.mem_cons_of_mem _ (zip_mem_of_getElem? ha hb)
  | [], _, _, _, _, ha, _ => by cases ha
  | _ :: _, [], _, _, _, _, hb => by cases hb

/-- **A return is sound**: after the `.ret` pop, the returned words (the frame words below the
return tag) meet the current function's summary, read in its environment. -/
theorem retOk_sound {t : Nat} {kv : List Nat} {dw : B256} {R : WRet}
    (h : σ.Holds ε sevm ν S d) (hS : d.stack = S ++ rest) (hkv : σ.kv = t :: kv)
    (hp : Devm.PopBurn [dw] d d') (hr : retOk σ kv R = true) :
    d'.stack = kv.map ν ++ rest ∧ R.Holds ε (kv.map ν) := by
  have h1 := popBurn_stack hp
  rw [hS, forall₂_eq_map h.kv, hkv] at h1
  simp only [List.map_cons, List.cons_append, List.nil_append, List.cons.injEq] at h1
  unfold retOk at hr
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at hr
  obtain ⟨⟨hl, hprov⟩, hles⟩ := hr
  refine ⟨h1.2.symm, by rw [List.length_map, hl], ?_, ?_⟩
  · intro j u w hu hw
    rw [List.getElem?_map] at hw
    cases hs : kv[j]? with
    | none => rw [hs] at hw; cases hw
    | some s =>
      rw [hs, Option.map_some, Option.some.injEq] at hw
      subst hw
      rcases hprov _ (zip_mem_of_getElem? hu hs) with hk | hk
      · intro hk'; rw [hk] at hk'; cases hk'
      · have := h.provOf s
        rw [hk] at this
        exact this
  · intro p hp
    have hle := hles p hp
    revert hle
    cases hs : kv[p.1]? with
    | none => intro hle; cases hle
    | some s =>
      cases ha : σ.args[p.2]? with
      | none => intro hle; cases hle
      | some a =>
        intro hle
        refine ⟨ν s, ν a, by rw [List.getElem?_map, hs]; rfl, ?_,
          FreePtr.entails_sound h.facts hle⟩
        obtain ⟨tl, htl⟩ := h.args
        rw [← htl, List.getElem?_append_left (by
          rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp ha).1), List.getElem?_map, ha]
        rfl

/-- **A callee's instantiated sites are covered**: a site of the callee's summary that holds in the
callee's environment gives a site of the caller's summary that holds in the caller's, when the
call passed `wsNode`'s coverage check. -/
theorem callNext_obs {A R : WRet} {cw : List Nat} {d₀ : Devm} {x v : B256}
    (h : σ.Holds ε sevm ν S d)
    (hall : A.sites.all (fun s => R.sites.any (·.covers (instSite (cw.map σ.provOf) σ.guards s))) =
      true)
    (hobs : ∃ s ∈ A.sites, s.Obs (ε.callee (cw.map ν)) sevm d₀ x v) :
    ∃ s ∈ R.sites, s.Obs ε sevm d₀ x v := by
  obtain ⟨s, hs, ho⟩ := hobs
  exact Site.Obs.of_any (List.all_eq_true.mp hall s hs)
    (instSite_obs (Env.callee_glob _) (h.pa cw) h.guards ho)

/-- **A call continuation resumes soundly.**  At the call the caller's state `σ` held of `d`
(its frame words `cw` the callee's entry words, `below` the words under them).  If the callee
returned the words `Wr` meeting its summary `R` in its environment, above the caller's `below`
words, and a keeping callee left the executing account's storage as it was at `d`, then the
continuation's state `resume σ cw below R rets` holds of the machine state after the return. -/
theorem resume_sound {cw below : List Nat} {R : WRet} {rets : Nat} {Wr : List B256}
    {d'' : Devm} (h : σ.Holds ε sevm ν S d) (hcw : ∀ s ∈ cw, s ∈ σ.kv)
    (hbelow : ∀ s ∈ below, s ∈ σ.kv) (hR : R.Holds (ε.callee (cw.map ν)) Wr)
    (hrets : Wr.length = rets) (hd : d''.stack = Wr ++ (below.map ν ++ rest))
    (hstor : R.keeps = true →
      Devm.getStor d'' sevm.currentTarget = Devm.getStor d sevm.currentTarget) :
    (resume σ cw below R rets).Sat ε sevm d'' rest := by
  let ν' : Nat → B256 := fun s => if σ.fresh ≤ s then Wr.getD (s - σ.fresh) 0 else ν s
  have hlow : ∀ s, s < σ.fresh → ν' s = ν s := fun s hs => by
    simp only [ν', show ¬ σ.fresh ≤ s from Nat.not_le.mpr hs, ↓reduceIte]
  have hhigh : ∀ j, ν' (σ.fresh + j) = Wr.getD j 0 := fun j => by
    simp only [ν', Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left]
  have hkvlt : ∀ s ∈ σ.kv, ν' s = ν s := fun s hs => hlow s (WSt.lt_fresh (by
    simp only [WSt.syms, List.mem_append]
    exact .inl (.inl (.inl (.inl (.inl (.inl (.inl hs))))))))
  have hA : σ.Holds ε sevm ν' S d := h.agree hlow
  have hcwv : ∀ {i : Nat} {s : Nat} {a : B256}, cw[i]? = some s →
      (ε.callee (cw.map ν)).args[i]? = some a → a = ν s := fun {i s a} hc ha => by
    change (cw.map ν)[i]? = some a at ha
    rw [List.getElem?_map, hc, Option.map_some, Option.some.injEq] at ha
    exact ha.symm
  refine ⟨ν', Wr ++ below.map ν, by rw [hd, List.append_assoc], ?_⟩
  unfold resume
  dsimp only
  refine WSt.Holds.prune ⟨?_, hA.args, ?_, ?_, (fun _ hp => by cases hp), ?_, ?_, hA.eqs,
    hA.guards⟩
  · -- the returned words above the caller's
    have e : ((List.range rets).map (σ.fresh + ·) ++ below).map ν' = Wr ++ below.map ν := by
      rw [List.map_append, List.map_map]
      congr 1
      · apply List.ext_getElem
        · simp only [List.length_map, List.length_range, hrets]
        · intro i h1 h2
          simp only [List.getElem_map, List.getElem_range, Function.comp_apply, hhigh,
            List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
      · exact List.map_congr_left fun s hs => hkvlt s (hbelow s hs)
    have := forall₂_map_self ν' ((List.range rets).map (σ.fresh + ·) ++ below)
    rwa [e] at this
  · -- order facts of the summary, and the caller's facts
    refine FreePtr.AllHold.append ?_ hA.facts
    intro f hf
    obtain ⟨p, hp, hfp⟩ := List.mem_filterMap.mp hf
    cases hc : cw[p.2]? with
    | none => rw [hc] at hfp; cases hfp
    | some s =>
      rw [hc, Option.map_some, Option.some.injEq] at hfp
      subst hfp
      obtain ⟨w, a, hw, ha, hle⟩ := hR.2.2 p hp
      show (ν' (σ.fresh + p.1)).toNat ≤ (ν' s).toNat
      rw [hhigh, hkvlt s (hcw s (List.mem_of_getElem? hc)), List.getD_eq_getElem?_getD, hw,
        Option.getD_some, ← hcwv hc ha]
      exact hle
  · -- the returned words' instantiated terms, and the caller's terms
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨j, hj, hq⟩ := List.mem_filterMap.mp hq
      split at hq
      · rename_i hk
        cases hq
        have hjr : j < R.prov.length := by
          rw [← hR.1, hrets]; exact List.mem_range.mp hj
        have hjw : j < Wr.length := by rw [hrets]; exact List.mem_range.mp hj
        show ((R.prov.getD j .top).subst (cw.map σ.provOf)).Den ε (ν' (σ.fresh + j))
        rw [hhigh, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjr, Option.getD_some,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjw, Option.getD_some]
        exact Term.den_subst_of_den (Env.callee_glob _) (h.pa cw)
          (hR.2.1 j _ _ (List.getElem?_eq_getElem hjr) (List.getElem?_eq_getElem hjw))
      · cases hq
    · exact hA.prov q hq
  · -- current slot values survive a keeping callee
    intro q hq
    split at hq
    · rename_i hk
      show (Devm.getStor d'' _).get _ = _
      rw [hstor hk]
      exact hA.cur q hq
    · cases hq
  · -- slot upper bounds
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · split at hq
      · rename_i hk
        obtain ⟨p, hp, hq⟩ := List.mem_flatMap.mp hq
        cases hc : cw[p.2]? with
        | none => rw [hc] at hq; cases hq
        | some s =>
          rw [hc] at hq
          obtain ⟨u, hu, hqu⟩ := List.mem_filterMap.mp hq
          split at hqu
          · rename_i hus
            cases hqu
            obtain ⟨w, a, hw, ha, hle⟩ := hR.2.2 p hp
            have has := hcwv hc ha
            have hsu : (ν s).toNat ≤ (d.getStorVal sevm.currentTarget (u.2.eval ε)).toNat := by
              rw [← hus]
              rcases List.mem_append.mp hu with hc' | hu'
              · rw [← h.cur u hc']
              · exact h.ub u hu'
            show (ν' (σ.fresh + p.1)).toNat ≤ ((Devm.getStor d'' _).get _).toNat
            rw [hhigh, hstor hk, List.getD_eq_getElem?_getD, hw, Option.getD_some]
            rw [has] at hle
            exact le_trans hle hsu
          · cases hqu
      · cases hq
    · split at hq
      · rename_i hk
        show _ ≤ ((Devm.getStor d'' _).get _).toNat
        rw [hstor hk]
        exact hA.ub q hq
      · cases hq

end Blanc.Lift.WriteSite
