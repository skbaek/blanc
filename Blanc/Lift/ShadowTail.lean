import Blanc.Lift.WitnessBoundary
import Blanc.Lift.WitnessShadow

/-!
# Shadows with a free tail: kernel runs over every world agreeing on finitely many entries

The witness engine (`Blanc/Lift/WitnessArms.lean`) reads the world only through its shadows,
and its agreement (`Agree`) asks the storage and account shadows to describe the world at every
address and key.  A world that agrees with a finite *prefix* of entries is described by that
prefix followed by a tail that lists the rest of the world (`storTailOf`, `acctTailOf`):

* `storOf_prefix_tail`, `acctAgree_prefix_tail`: every world that agrees with a prefix of
  storage entries (resp. account views) is described by the prefix followed by its own tail.

A kernel decision stated over a **free** tail then holds for every such world: the
interpreter's lookups of keys the prefix holds reduce inside the prefix, and a lookup outside
it would leave the decision stuck (it fails; it is never wrong).  The boundary kit with a tail
(`cfgOfT`, `obsDT`, `cfg_of_obsDT`, `obsDT_cont`) compares a boundary's literal prefixes by
`decide` and the tails, which the run never inspects, as terms (`List.drop`).
Nothing here is contract-specific.
-/

namespace Blanc.Lift.Witness

open Jaune

/-! ## The tail of a world -/

/-- A storage map, as the tree map it is. -/
abbrev storMap (s : Stor) : Std.TreeMap B256 B256 compare := s

/-- Every storage entry of a world, as a storage shadow. -/
def storTailOf (W : State) : StorShadow :=
  W.toList.flatMap fun p => (storMap p.2.stor).toList.map fun q => ((p.1, q.1), q.2)

/-- Every account of a world, storage dropped, as an account shadow. -/
def acctTailOf (W : State) : AcctShadow :=
  W.toList.map fun p => (p.1, acctView p.2)

theorem lookupS_eq_of {l : StorShadow} {a : Adr} {k v : B256}
    (h : ∀ e ∈ l, e.1 = (a, k) → e.2 = v) (h0 : (∀ e ∈ l, e.1 ≠ (a, k)) → v = 0) :
    lookupS l a k = v := by
  induction l with
  | nil => exact (h0 fun _ he => absurd he List.not_mem_nil).symm
  | cons e l ih =>
    obtain ⟨⟨b, j⟩, w⟩ := e
    simp only [lookupS]
    split
    · next hb =>
      obtain ⟨rfl, rfl⟩ := hb
      exact h _ List.mem_cons_self rfl
    · next hb =>
      refine ih (fun e he => h e (List.mem_cons_of_mem _ he)) (fun hn => h0 fun e he => ?_)
      rcases List.mem_cons.mp he with rfl | he
      · intro hx
        simp only [Prod.mk.injEq] at hx
        exact hb hx
      · exact hn e he

theorem lookupA_eq_of {l : AcctShadow} {a : Adr} {v : Acct}
    (h : ∀ e ∈ l, e.1 = a → e.2 = v) (h0 : (∀ e ∈ l, e.1 ≠ a) → v = .nil) :
    lookupA l a = v := by
  induction l with
  | nil => exact (h0 fun _ he => absurd he List.not_mem_nil).symm
  | cons e l ih =>
    obtain ⟨b, w⟩ := e
    simp only [lookupA]
    split
    · next hb => exact h _ List.mem_cons_self hb
    · next hb =>
      refine ih (fun e he => h e (List.mem_cons_of_mem _ he)) (fun hn => h0 fun e he => ?_)
      rcases List.mem_cons.mp he with rfl | he
      · exact hb
      · exact hn e he

theorem storOf_eq_getD (W : State) (a : Adr) (k : B256) :
    storOf W a k = (storMap (W.getD a .nil).stor).getD k 0 := rfl

theorem storOf_eq_of_get {W : State} {a : Adr} {ac : Acct} (h : W[a]? = some ac) (k : B256) :
    storOf W a k = (storMap ac.stor).getD k 0 := by
  rw [storOf_eq_getD, Std.TreeMap.getD_eq_getD_getElem? (t := W), h, Option.getD_some]

theorem storOf_eq_zero_of_get {W : State} {a : Adr} (h : W[a]? = none) (k : B256) :
    storOf W a k = 0 := by
  rw [storOf_eq_getD, Std.TreeMap.getD_eq_getD_getElem? (t := W), h, Option.getD_none]; rfl

/-- **The tail lists the world's storage.** -/
theorem lookupS_storTailOf (W : State) (a : Adr) (k : B256) :
    lookupS (storTailOf W) a k = storOf W a k := by
  refine lookupS_eq_of (fun e he hk => ?_) (fun hn => ?_)
  · obtain ⟨⟨b, j⟩, v⟩ := e
    simp only [Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    simp only [storTailOf, List.mem_flatMap, List.mem_map, Prod.mk.injEq] at he
    obtain ⟨⟨b', ac⟩, hp, ⟨k', v'⟩, hq, ⟨rfl, rfl⟩, rfl⟩ := he
    have hW : W[b']? = some ac := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp
    have hS : (storMap ac.stor)[k']? = some v' :=
      Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hq
    rw [storOf_eq_of_get hW, Std.TreeMap.getD_eq_getD_getElem?, hS, Option.getD_some]
  · rcases hW : W[a]? with _ | ac
    · exact storOf_eq_zero_of_get hW k
    · rw [storOf_eq_of_get hW, Std.TreeMap.getD_eq_getD_getElem?]
      rcases hS : (storMap ac.stor)[k]? with _ | v
      · rfl
      · exfalso
        refine hn ((a, k), v) ?_ rfl
        simp only [storTailOf, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
        exact ⟨(a, ac), Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hW, (k, v),
          Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hS, ⟨rfl, rfl⟩, rfl⟩

/-- **The tail lists the world's accounts.** -/
theorem lookupA_acctTailOf (W : State) (a : Adr) :
    lookupA (acctTailOf W) a = acctView (W.get a) := by
  refine lookupA_eq_of (fun e he hk => ?_) (fun hn => ?_)
  · obtain ⟨b, v⟩ := e
    simp only at hk
    subst hk
    simp only [acctTailOf, List.mem_map, Prod.mk.injEq] at he
    obtain ⟨⟨b', ac⟩, hp, rfl, rfl⟩ := he
    have hW : W[b']? = some ac := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp
    show acctView ac = acctView (W.getD b' .nil)
    rw [Std.TreeMap.getD_eq_getD_getElem?, hW, Option.getD_some]
  · show acctView (W.getD a .nil) = .nil
    rw [Std.TreeMap.getD_eq_getD_getElem?]
    rcases hW : W[a]? with _ | ac
    · rfl
    · exfalso
      refine hn (a, acctView ac) ?_ rfl
      simp only [acctTailOf, List.mem_map, Prod.mk.injEq]
      exact ⟨(a, ac), Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hW, rfl, rfl⟩

/-- **A world agreeing with a storage prefix is described by the prefix and its tail.** -/
theorem storOf_prefix_tail {W : State} {p : StorShadow}
    (h : ∀ e ∈ p, storOf W e.1.1 e.1.2 = e.2) :
    ∀ a k, storOf W a k = lookupS (p ++ storTailOf W) a k := by
  intro a k
  induction p with
  | nil => exact (lookupS_storTailOf W a k).symm
  | cons e p ih =>
    obtain ⟨⟨b, j⟩, v⟩ := e
    simp only [List.cons_append, lookupS]
    split
    · next hb =>
      obtain ⟨rfl, rfl⟩ := hb
      exact h _ List.mem_cons_self
    · exact ih fun e he => h e (List.mem_cons_of_mem _ he)

/-- **A world agreeing with an account prefix is described by the prefix and its tail.** -/
theorem acctAgree_prefix_tail {W : State} {p : AcctShadow}
    (h : ∀ e ∈ p, acctView (W.get e.1) = e.2) : AcctAgree W (p ++ acctTailOf W) := by
  intro a
  induction p with
  | nil => exact (lookupA_acctTailOf W a).symm
  | cons e p ih =>
    obtain ⟨b, v⟩ := e
    simp only [List.cons_append, lookupA]
    split
    · next hb =>
      subst hb
      exact h _ List.mem_cons_self
    · exact ih fun e he => h e (List.mem_cons_of_mem _ he)

/-! ## Boundaries with a tail -/

namespace Boundary

/-- A boundary's storage prefix. -/
def storOf1 : Bnd1 → StorShadow
  | (_, _, _, _, _, stor, _, _, _, _, _) => stor

/-- A boundary's account prefix. -/
def acsOf1 : Bnd1 → AcctShadow
  | (_, _, _, _, _, _, acs, _, _, _, _) => acs

/-- The configuration at boundary `x` with the storage tail `tS` and the account tail `tA`
after its literal prefixes, over a free world and free bookkeeping. -/
def cfgOfT (x : Bnd1) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : Cfg :=
  ⟨(cfgOf1 x m w).devm, (cfgOf1 x m w).f, (cfgOf1 x m w).K, (cfgOf1 x m w).keys,
    (cfgOf1 x m w).adrs, (cfgOf1 x m w).stor ++ tS, (cfgOf1 x m w).acs ++ tA⟩

/-- A configuration with its shadows cut to the lengths of boundary `x`'s prefixes. -/
def cutT (x : Bnd1) (c : Cfg) : Cfg :=
  ⟨c.devm, c.f, c.K, c.keys, c.adrs, c.stor.take (storOf1 x).length,
    c.acs.take (acsOf1 x).length⟩

/-- A chunk's end decided against boundary `x` with tails: the prefixes as `obsD1` decides them,
and what lies after them, compared as terms. -/
def obsDT (x : Bnd1) : Res →
    Option (Bool × SFunc × List SFunc × List (Stor × ByteArray) × AdrSet) × StorShadow ×
      AcctShadow
  | .cont c => (obsD1 x (.cont (cutT x c)), c.stor.drop (storOf1 x).length,
      c.acs.drop (acsOf1 x).length)
  | r => (obsD1 x r, [], [])

/-- What `obsDT` shows at boundary `x` with the tails `tS`, `tA`. -/
def obsDOkT (x : Bnd1) (tS : StorShadow) (tA : AcctShadow) :
    Option (Bool × SFunc × List SFunc × List (Stor × ByteArray) × AdrSet) × StorShadow ×
      AcctShadow :=
  (obsDOk1 x, tS, tA)

theorem cfgOf1_stor (x : Bnd1) (m : Meta) (w : World) : (cfgOf1 x m w).stor = storOf1 x := by
  rcases x with ⟨_, _, _, _, _, _, _, _, _, _, _⟩; rfl

theorem cfgOf1_acs (x : Bnd1) (m : Meta) (w : World) : (cfgOf1 x m w).acs = acsOf1 x := by
  rcases x with ⟨_, _, _, _, _, _, _, _, _, _, _⟩; rfl

/-- A boundary configuration's storage shadow is its prefix followed by the free tail. -/
theorem cfgOfT_stor (x : Bnd1) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World) : (cfgOfT x tS tA m w).stor = storOf1 x ++ tS := by
  rw [← cfgOf1_stor x m w]; rfl

/-- A boundary configuration's account shadow is its prefix followed by the free tail. -/
theorem cfgOfT_acs (x : Bnd1) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World) : (cfgOfT x tS tA m w).acs = acsOf1 x ++ tA := by
  rw [← cfgOf1_acs x m w]; rfl

/-- A configuration decided at boundary `x` with tails is `cfgOfT x` at its own world and
bookkeeping. -/
theorem cfg_of_obsDT {c : Cfg} {x : Bnd1} {tS : StorShadow} {tA : AcctShadow}
    (h : obsDT x (.cont c) = obsDOkT x tS tA) :
    c = cfgOfT x tS tA c.devm.meta c.devm.world := by
  simp only [obsDT, obsDOkT, Prod.mk.injEq] at h
  obtain ⟨h1, hs, ha⟩ := h
  have hc := cfg_of_obsD1 h1
  have hs' : c.stor = storOf1 x ++ tS := by
    rw [← List.take_append_drop (storOf1 x).length c.stor, hs]
    congr 1
    have := congrArg Cfg.stor hc
    simp only [cutT] at this
    rw [this, cfgOf1_stor]
  have ha' : c.acs = acsOf1 x ++ tA := by
    rw [← List.take_append_drop (acsOf1 x).length c.acs, ha]
    congr 1
    have := congrArg Cfg.acs hc
    simp only [cutT] at this
    rw [this, cfgOf1_acs]
  have hd := congrArg Cfg.devm hc
  have hf := congrArg Cfg.f hc
  have hK := congrArg Cfg.K hc
  have hk := congrArg Cfg.keys hc
  have hA := congrArg Cfg.adrs hc
  simp only [cutT] at hd hf hK hk hA
  rcases c with ⟨d, f, K, keys, adrs, stor, acs⟩
  simp only at hd hf hK hk hA hs' ha'
  unfold cfgOfT
  rw [cfgOf1_stor, cfgOf1_acs, ← hd, ← hf, ← hK, ← hk, ← hA, ← hs', ← ha']

/-- A result decided at boundary `x` with tails is `cfgOfT x` at some world and bookkeeping. -/
theorem obsDT_cont {x : Bnd1} {tS : StorShadow} {tA : AcctShadow} {r : Res}
    (h : obsDT x r = obsDOkT x tS tA) : ∃ m w, r = .cont (cfgOfT x tS tA m w) := by
  rcases r with c | _ | _
  · exact ⟨_, _, congrArg Res.cont (cfg_of_obsDT h)⟩
  · rcases x with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
    simp only [obsDT, obsDOkT, obsD1, obsDOk1, Prod.mk.injEq, reduceCtorEq, false_and] at h
  · rcases x with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
    simp only [obsDT, obsDOkT, obsD1, obsDOk1, Prod.mk.injEq, reduceCtorEq, false_and] at h

end Boundary

end Blanc.Lift.Witness
