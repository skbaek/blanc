import Blanc.Lift.Loop

/-!
# Fuel-bounded loops in lifted code

A compiled `for _i in range(cap)` loop whose body computes a new iterate, stops
early when a test passes, and otherwise falls out after `cap` bodies returning
the last iterate (Vyper's Newton loops, for example) is modelled by
`fuelLoop body close fuel D`: `none` when a body reverts, the stopped iterate
when `close new prev` holds, and the last iterate when the fuel runs out.

The bridges below connect a lifted loop head at entry `k` to that model.  The
loop is described abstractly, by what one pass of the head's tree does from a
state satisfying `At n D` (iteration counter `n < cap`, current iterate `D`;
typically the counter and value words in memory, the bound on the stack):

* safety, `RunCut_fuelLoop_sound`: from the per-pass inversion `FuelStep`
  (a reverting body leaves with `Out none`, a stopping body or the last
  permitted body leaves with `Out (some D')`, any other body re-enters `k` in
  `At (n + 1) D'`), every run from the head cut at `C` ends satisfying
  `Out (fuelLoop body close (cap - n) D)`;
* liveness, `RunExactCut_fuelLoop_exact`: from the per-pass forward runs, with
  a cost per branch (`cStep` for a pass that re-enters, `cStop` for a stopping
  pass, `cCap` for the last permitted pass), the head runs to its exit with the
  recursive charge `fuelCost`, which mirrors `fuelLoop`.

**Peeled heads.**  A certificate that duplicates a loop head (the first pass, or
the first few, as separate entries whose back edge targets the next copy) is
handled by `RunCut_fuelLoop_peel` and `RunExactCut_fuelLoop_peel`: from the
statement already proved for the continuation entry `k` and one pass of the
peeled tree `f` ending at `k`, the same statement holds for `f`.  A chain of
copies is discharged from the steady head backwards.  The per-pass hypotheses
quantify over the continuation entry `k`, so one body lemma stated over that
index serves every copy.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-! ## The model -/

/-- A fuel-bounded loop: with fuel left, run `body` on the iterate (`none`
reverts); stop with the new iterate when `close new prev`, otherwise continue;
with no fuel left, return the last iterate. -/
def fuelLoop (body : Nat → Option Nat) (close : Nat → Nat → Bool) : Nat → Nat → Option Nat
  | 0, D => some D
  | fuel + 1, D =>
    match body D with
    | none => none
    | some D' => if close D' D then some D' else fuelLoop body close fuel D'

/-- The gas a successful `fuelLoop` run charges, pass by pass: `cStop prev new`
for the stopping pass, `cCap prev new` for the last permitted pass, and
`cStep prev new` for every pass that re-enters the head. -/
def fuelCost (body : Nat → Option Nat) (close : Nat → Nat → Bool)
    (cStep cStop cCap : Nat → Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | 1, D =>
    match body D with
    | none => 0
    | some D' => if close D' D then cStop D D' else cCap D D'
  | fuel + 2, D =>
    match body D with
    | none => 0
    | some D' =>
      if close D' D then cStop D D'
      else cStep D D' + fuelCost body close cStep cStop cCap (fuel + 1) D'

/-! ## Safety -/

/-- What one pass of a fuel loop at head `k` must establish, from counter `n`
and iterate `D`, about the segment `r` it ends with: a reverting body leaves
with `Out none`; a stopping body, or the last permitted body (`n + 1 = cap`),
leaves with `Out (some D')`; any other body re-enters `k` in `At (n + 1) D'`.
Leaving means not re-entering `k`. -/
def FuelStep (k cap : Nat) (body : Nat → Option Nat) (close : Nat → Nat → Bool)
    (At : Nat → Nat → Devm → Prop) (Out : Option Nat → Seg → Prop)
    (n D : Nat) (r : Seg) : Prop :=
  match body D with
  | none => Seg.LoopPost k (fun _ => False) (Out none) r
  | some D' =>
    if close D' D = true ∨ n + 1 = cap then
      Seg.LoopPost k (fun _ => False) (Out (some D')) r
    else ∃ d', r = .at k d' ∧ At (n + 1) D' d'

theorem Seg.LoopPost.mono {k : Nat} {I I' : Devm → Prop} {Q Q' : Seg → Prop}
    (hI : ∀ d, I d → I' d) (hQ : ∀ r, Q r → Q' r) {r : Seg}
    (h : Seg.LoopPost k I Q r) : Seg.LoopPost k I' Q' r := by
  rcases r with ⟨j, d⟩ | o
  · by_cases hj : j = k
    · simp only [Seg.LoopPost, hj, ↓reduceIte] at h ⊢
      exact hI d h
    · simp only [Seg.LoopPost, hj, ↓reduceIte] at h ⊢
      exact hQ _ h
  · exact hQ _ h

/-- A pass that `FuelStep` describes keeps the loop invariant "at the head with
the same final value", or leaves with that value. -/
theorem FuelStep.loopPost {k cap : Nat} {body : Nat → Option Nat}
    {close : Nat → Nat → Bool} {At : Nat → Nat → Devm → Prop}
    {Out : Option Nat → Seg → Prop} {n D : Nat} {r : Seg} (hn : n < cap)
    (h : FuelStep k cap body close At Out n D r) :
    Seg.LoopPost k
      (fun d => ∃ n' D', n' < cap ∧ At n' D' d ∧
        fuelLoop body close (cap - n') D' = fuelLoop body close (cap - n) D)
      (Out (fuelLoop body close (cap - n) D)) r := by
  obtain ⟨m, hm⟩ : ∃ m, cap - n = m + 1 := ⟨cap - n - 1, by omega⟩
  rw [hm]
  unfold FuelStep at h
  cases hb : body D with
  | none =>
    rw [hb] at h
    simp only [fuelLoop, hb]
    exact Seg.LoopPost.mono (fun _ hf => hf.elim) (fun _ hq => hq) h
  | some D' =>
    rw [hb] at h
    by_cases hc : close D' D = true
    · simp only [hc, true_or, ↓reduceIte] at h
      simp only [fuelLoop, hb, hc, ↓reduceIte]
      exact Seg.LoopPost.mono (fun _ hf => hf.elim) (fun _ hq => hq) h
    · by_cases hcap : n + 1 = cap
      · have hm0 : m = 0 := by omega
        subst hm0
        simp only [hc, hcap, or_true, ↓reduceIte] at h
        simp only [fuelLoop, hb, hc, Bool.false_eq_true, ↓reduceIte]
        exact Seg.LoopPost.mono (fun _ hf => hf.elim) (fun _ hq => hq) h
      · simp only [hc, hcap] at h
        obtain ⟨d', rfl, hAt⟩ := h
        simp only [Seg.LoopPost, ↓reduceIte]
        refine ⟨n + 1, D', by omega, hAt, ?_⟩
        rw [show cap - (n + 1) = m by omega]
        simp only [fuelLoop, hb, hc, Bool.false_eq_true, ↓reduceIte]

/-- **Fuel-loop safety.**  If every pass of the head at entry `k` (its tree `g`
cut at `k` and the outer list `C`) from `At n D` with `n < cap` is described by
`FuelStep`, then every run of the loop cut at `C` from `At n D` ends satisfying
`Out (fuelLoop body close (cap - n) D)`. -/
theorem RunCut_fuelLoop_sound {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {C : List Nat} {k : Nat} {g : SFunc}
    (hk : fs[k]? = some g) (hkC : k ∉ C) {cap : Nat}
    {body : Nat → Option Nat} {close : Nat → Nat → Bool}
    (At : Nat → Nat → Devm → Prop) (Out : Option Nat → Seg → Prop)
    (step : ∀ n D d, n < cap → At n D d → ∀ r,
      SFunc.RunCutP P fs sevm (k :: C) d g r → FuelStep k cap body close At Out n D r) :
    ∀ n D d r, n < cap → At n D d → SFunc.RunCutP P fs sevm C d g r →
      Out (fuelLoop body close (cap - n) D) r := by
  intro n D d r hn hAt run
  exact SFunc.RunCutP.loop hk hkC
    (fun d => ∃ n' D', n' < cap ∧ At n' D' d ∧
      fuelLoop body close (cap - n') D' = fuelLoop body close (cap - n) D)
    (Out (fuelLoop body close (cap - n) D))
    (fun d ⟨n', D', hn', hAt', hv⟩ r hrun => by
      have hp := (step n' D' d hn' hAt' r hrun).loopPost hn'
      refine Seg.LoopPost.mono ?_ (fun _ hq => hv ▸ hq) hp
      intro d0 ⟨n0, D0, h0, hA0, hv0⟩
      exact ⟨n0, D0, h0, hA0, hv0.trans hv⟩)
    d r ⟨n, D, hn, hAt, rfl⟩ run

/-- A run cut at `C` either never enters `k ∉ C`, or splits at its first entry
into `k`. -/
theorem SFunc.RunCutP.split_at {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {C : List Nat} {k : Nat} {g : SFunc}
    (hk : fs[k]? = some g) (hkC : k ∉ C) {devm : Devm} {f : SFunc} {r : Seg}
    (run : SFunc.RunCutP P fs sevm C devm f r) :
    (SFunc.RunCutP P fs sevm (k :: C) devm f r ∧ ∀ d, r ≠ .at k d) ∨
      ∃ d, SFunc.RunCutP P fs sevm (k :: C) devm f (.at k d) ∧
        SFunc.RunCutP P fs sevm C d g r := by
  refine SFunc.RunCutP.rec (C := C)
    (motive := fun devm f r _ =>
      (SFunc.RunCutP P fs sevm (k :: C) devm f r ∧ ∀ d, r ≠ .at k d) ∨
        ∃ d, SFunc.RunCutP P fs sevm (k :: C) devm f (.at k d) ∧
          SFunc.RunCutP P fs sevm C d g r)
    (fun d pop _ ih => by
      rcases ih with ⟨h, hne⟩ | ⟨d', h, h2⟩
      · exact .inl ⟨.zero d pop h, hne⟩
      · exact .inr ⟨d', .zero d pop h, h2⟩)
    (fun d w hnz pop _ ih => by
      rcases ih with ⟨h, hne⟩ | ⟨d', h, h2⟩
      · exact .inl ⟨.succ d w hnz pop h, hne⟩
      · exact .inr ⟨d', .succ d w hnz pop h, h2⟩)
    (fun d pop _ ih => by
      rcases ih with ⟨h, hne⟩ | ⟨d', h, h2⟩
      · exact .inl ⟨.toZero d pop h, hne⟩
      · exact .inr ⟨d', .toZero d pop h, h2⟩)
    (fun {s0 s1 f0 t} d w hnz ht pop => by
      refine .inl ⟨.toSuccCut d w hnz (List.mem_cons_of_mem k ht) pop, ?_⟩
      intro d' h
      cases h
      exact hkC ht)
    (fun {s0 s1 f0 g0 t r0} d w hnz hnot hget pop hrun ih => by
      by_cases htk : t = k
      · subst t
        have hfg : g = g0 := Option.some.inj (hk.symm.trans hget)
        subst hfg
        exact .inr ⟨s1, .toSuccCut d w hnz List.mem_cons_self pop, hrun⟩
      · have hnot' : t ∉ k :: C := by
          intro hm
          rcases List.mem_cons.mp hm with h | h
          · exact htk h
          · exact hnot h
        rcases ih with ⟨h, hne⟩ | ⟨d', h, h2⟩
        · exact .inl ⟨.toSucc d w hnz hnot' hget pop h, hne⟩
        · exact .inr ⟨d', .toSucc d w hnz hnot' hget pop h, h2⟩)
    (fun h => .inl ⟨.last h, fun _ he => Seg.noConfusion he⟩)
    (fun h _ ih => by
      rcases ih with ⟨h', hne⟩ | ⟨d', h', h2⟩
      · exact .inl ⟨.next h h', hne⟩
      · exact .inr ⟨d', .next h h', h2⟩)
    (fun burn _ ih => by
      rcases ih with ⟨h', hne⟩ | ⟨d', h', h2⟩
      · exact .inl ⟨.dest burn h', hne⟩
      · exact .inr ⟨d', .dest burn h', h2⟩)
    (fun {s0 s1 t} d ht pop => by
      refine .inl ⟨.jumpCut d (List.mem_cons_of_mem k ht) pop, ?_⟩
      intro d' h
      cases h
      exact hkC ht)
    (fun {s0 s1 t f0 r0} d hnot hget pop hrun ih => by
      by_cases htk : t = k
      · subst t
        have hfg : g = f0 := Option.some.inj (hk.symm.trans hget)
        subst hfg
        exact .inr ⟨s1, .jumpCut d List.mem_cons_self pop, hrun⟩
      · have hnot' : t ∉ k :: C := by
          intro hm
          rcases List.mem_cons.mp hm with h | h
          · exact htk h
          · exact hnot h
        rcases ih with ⟨h, hne⟩ | ⟨d', h, h2⟩
        · exact .inl ⟨.jump d hnot' hget pop h, hne⟩
        · exact .inr ⟨d', .jump d hnot' hget pop h, h2⟩)
    (fun d pop => .inl ⟨.ret d pop, fun _ he => Seg.noConfusion he⟩)
    (fun d hget pop hrun => .inl ⟨.callHalt d hget pop hrun, fun _ he => Seg.noConfusion he⟩)
    (fun d hget pop hrun _ ih => by
      rcases ih with ⟨h', hne⟩ | ⟨d', h', h2⟩
      · exact .inl ⟨.callRet d hget pop hrun h', hne⟩
      · exact .inr ⟨d', .callRet d hget pop hrun h', h2⟩)
    (fun h hpc _ ih => by
      rcases ih with ⟨h', hne⟩ | ⟨d', h', h2⟩
      · exact .inl ⟨.pcAt h hpc h', hne⟩
      · exact .inr ⟨d', .pcAt h hpc h', h2⟩)
    run

/-- **Peeled head, safety.**  If the statement of `RunCut_fuelLoop_sound` holds
for the head at entry `k` (`next`), and every pass of another tree `f` (a
peeled copy whose back edge targets `k`) cut at `k :: C` is described by
`FuelStep`, then it holds for `f`. -/
theorem RunCut_fuelLoop_peel {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {C : List Nat} {k : Nat} {g f : SFunc}
    (hk : fs[k]? = some g) (hkC : k ∉ C) {cap : Nat}
    {body : Nat → Option Nat} {close : Nat → Nat → Bool}
    (At : Nat → Nat → Devm → Prop) (Out : Option Nat → Seg → Prop)
    (next : ∀ n D d r, n < cap → At n D d → SFunc.RunCutP P fs sevm C d g r →
      Out (fuelLoop body close (cap - n) D) r)
    (step : ∀ n D d, n < cap → At n D d → ∀ r,
      SFunc.RunCutP P fs sevm (k :: C) d f r → FuelStep k cap body close At Out n D r) :
    ∀ n D d r, n < cap → At n D d → SFunc.RunCutP P fs sevm C d f r →
      Out (fuelLoop body close (cap - n) D) r := by
  intro n D d r hn hAt run
  rcases run.split_at hk hkC with ⟨h, hne⟩ | ⟨d', h, rest⟩
  · have hp := (step n D d hn hAt r h).loopPost hn
    rcases r with ⟨j, d0⟩ | o
    · have hj : j ≠ k := fun hj => hne d0 (by rw [hj])
      simpa only [Seg.LoopPost, hj, ↓reduceIte] using hp
    · exact hp
  · have hp := (step n D d hn hAt _ h).loopPost hn
    simp only [Seg.LoopPost, ↓reduceIte] at hp
    obtain ⟨n', D', hn', hAt', hv⟩ := hp
    rw [← hv]
    exact next n' D' d' r hn' hAt' rest

/-! ## Liveness -/

/-- One pass of the exact loop, from counter `n`, given the statement for the
continuation at counter `n + 1`. -/
theorem RunExactCut_fuelLoop_pass {fs : List SFunc} {sevm : Sevm} {C : List Nat}
    {k : Nat} {g f : SFunc} (hk : fs[k]? = some g) (hkC : k ∉ C) {cap : Nat}
    {body : Nat → Option Nat} {close : Nat → Nat → Bool}
    {cStep cStop cCap : Nat → Nat → Nat}
    (At : Nat → Nat → Nat → Devm → Prop) (Exit : Nat → Nat → Seg → Prop)
    (hstep : ∀ n D D' G d, n + 1 < cap → body D = some D' → close D' D = false →
      At n D (G + cStep D D') d →
      ∃ d', SFunc.RunExactCut fs sevm (k :: C) d f (.at k d') ∧ At (n + 1) D' G d')
    (hstop : ∀ n D D' G d, n < cap → body D = some D' → close D' D = true →
      At n D (G + cStop D D') d →
      ∃ r, SFunc.RunExactCut fs sevm (k :: C) d f r ∧ (∀ d', r ≠ .at k d') ∧ Exit D' G r)
    (hcap : ∀ n D D' G d, n + 1 = cap → body D = some D' → close D' D = false →
      At n D (G + cCap D D') d →
      ∃ r, SFunc.RunExactCut fs sevm (k :: C) d f r ∧ (∀ d', r ≠ .at k d') ∧ Exit D' G r)
    {n : Nat} (hn : n < cap)
    (next : n + 1 < cap → ∀ D v G d, fuelLoop body close (cap - (n + 1)) D = some v →
      At (n + 1) D (G + fuelCost body close cStep cStop cCap (cap - (n + 1)) D) d →
      ∃ r, SFunc.RunExactCut fs sevm C d g r ∧ Exit v G r) :
    ∀ D v G d, fuelLoop body close (cap - n) D = some v →
      At n D (G + fuelCost body close cStep cStop cCap (cap - n) D) d →
      ∃ r, SFunc.RunExactCut fs sevm C d f r ∧ Exit v G r := by
  intro D v G d hv hAt
  obtain ⟨m, hm⟩ : ∃ m, cap - n = m + 1 := ⟨cap - n - 1, by omega⟩
  rw [hm] at hv hAt
  cases hb : body D with
  | none => simp only [fuelLoop, hb, reduceCtorEq] at hv
  | some D' =>
    by_cases hc : close D' D = true
    · have hvD : v = D' := by
        simp only [fuelLoop, hb, hc, ↓reduceIte, Option.some.injEq] at hv
        exact hv.symm
      subst hvD
      have hcost : fuelCost body close cStep cStop cCap (m + 1) D = cStop D v := by
        cases m <;> simp only [fuelCost, hb, hc, ↓reduceIte]
      rw [hcost] at hAt
      obtain ⟨r, hrun, hne, hex⟩ := hstop n D v G d hn hb hc hAt
      exact ⟨r, SFunc.RunExactCut.uncut hrun hne, hex⟩
    · have hc' : close D' D = false := by simpa only [Bool.not_eq_true] using hc
      cases m with
      | zero =>
        have hvD : v = D' := by
          simp only [fuelLoop, hb, hc', Bool.false_eq_true, ↓reduceIte,
            Option.some.injEq] at hv
          exact hv.symm
        subst hvD
        have hcost : fuelCost body close cStep cStop cCap (0 + 1) D = cCap D v := by
          simp only [fuelCost, hb, hc', Bool.false_eq_true, ↓reduceIte]
        rw [hcost] at hAt
        obtain ⟨r, hrun, hne, hex⟩ := hcap n D v G d (by omega) hb hc' hAt
        exact ⟨r, SFunc.RunExactCut.uncut hrun hne, hex⟩
      | succ m =>
        have hv' : fuelLoop body close (m + 1) D' = some v := by
          simpa only [fuelLoop, hb, hc', Bool.false_eq_true, ↓reduceIte] using hv
        have hcost : G + fuelCost body close cStep cStop cCap (m + 1 + 1) D =
            (G + fuelCost body close cStep cStop cCap (m + 1) D') + cStep D D' := by
          simp only [fuelCost, hb, hc', Bool.false_eq_true, ↓reduceIte]
          omega
        rw [hcost] at hAt
        obtain ⟨d', hseg, hAt'⟩ := hstep n D D' _ d (by omega) hb hc' hAt
        have hm' : cap - (n + 1) = m + 1 := by omega
        obtain ⟨r, hrun, hex⟩ := next (by omega) D' v G d' (by rw [hm']; exact hv')
          (by rw [hm']; exact hAt')
        exact ⟨r, SFunc.RunExactCut.resume hk hkC hseg hrun, hex⟩

/-- **Fuel-loop liveness.**  From exact passes of the head at entry `k` (its
tree `g` cut at `k` and `C`) on each branch, with constant costs `cStep`,
`cStop` and `cCap` per branch, a successful `fuelLoop` from `At n D` with
`n < cap` and gas `G + fuelCost … (cap - n) D` runs to its exit leaving `G`. -/
theorem RunExactCut_fuelLoop_exact {fs : List SFunc} {sevm : Sevm} {C : List Nat}
    {k : Nat} {g : SFunc} (hk : fs[k]? = some g) (hkC : k ∉ C) {cap : Nat}
    {body : Nat → Option Nat} {close : Nat → Nat → Bool}
    {cStep cStop cCap : Nat → Nat → Nat}
    (At : Nat → Nat → Nat → Devm → Prop) (Exit : Nat → Nat → Seg → Prop)
    (hstep : ∀ n D D' G d, n + 1 < cap → body D = some D' → close D' D = false →
      At n D (G + cStep D D') d →
      ∃ d', SFunc.RunExactCut fs sevm (k :: C) d g (.at k d') ∧ At (n + 1) D' G d')
    (hstop : ∀ n D D' G d, n < cap → body D = some D' → close D' D = true →
      At n D (G + cStop D D') d →
      ∃ r, SFunc.RunExactCut fs sevm (k :: C) d g r ∧ (∀ d', r ≠ .at k d') ∧ Exit D' G r)
    (hcap : ∀ n D D' G d, n + 1 = cap → body D = some D' → close D' D = false →
      At n D (G + cCap D D') d →
      ∃ r, SFunc.RunExactCut fs sevm (k :: C) d g r ∧ (∀ d', r ≠ .at k d') ∧ Exit D' G r) :
    ∀ n D v G d, n < cap → fuelLoop body close (cap - n) D = some v →
      At n D (G + fuelCost body close cStep cStop cCap (cap - n) D) d →
      ∃ r, SFunc.RunExactCut fs sevm C d g r ∧ Exit v G r := by
  have aux : ∀ m n, cap - n = m → n < cap → ∀ D v G d,
      fuelLoop body close (cap - n) D = some v →
      At n D (G + fuelCost body close cStep cStop cCap (cap - n) D) d →
      ∃ r, SFunc.RunExactCut fs sevm C d g r ∧ Exit v G r := by
    intro m
    induction m with
    | zero => intro n hm hn; omega
    | succ m ih =>
      intro n hm hn
      exact RunExactCut_fuelLoop_pass hk hkC At Exit hstep hstop hcap hn
        (fun h1 => ih (n + 1) (by omega) h1)
  intro n D v G d hn
  exact aux (cap - n) n rfl hn D v G d

/-- **Peeled head, liveness.**  If the statement of `RunExactCut_fuelLoop_exact`
holds for the head at entry `k` (`next`), and another tree `f` (a peeled copy
whose back edge targets `k`) has the exact passes, then it holds for `f`. -/
theorem RunExactCut_fuelLoop_peel {fs : List SFunc} {sevm : Sevm} {C : List Nat}
    {k : Nat} {g f : SFunc} (hk : fs[k]? = some g) (hkC : k ∉ C) {cap : Nat}
    {body : Nat → Option Nat} {close : Nat → Nat → Bool}
    {cStep cStop cCap : Nat → Nat → Nat}
    (At : Nat → Nat → Nat → Devm → Prop) (Exit : Nat → Nat → Seg → Prop)
    (next : ∀ n D v G d, n < cap → fuelLoop body close (cap - n) D = some v →
      At n D (G + fuelCost body close cStep cStop cCap (cap - n) D) d →
      ∃ r, SFunc.RunExactCut fs sevm C d g r ∧ Exit v G r)
    (hstep : ∀ n D D' G d, n + 1 < cap → body D = some D' → close D' D = false →
      At n D (G + cStep D D') d →
      ∃ d', SFunc.RunExactCut fs sevm (k :: C) d f (.at k d') ∧ At (n + 1) D' G d')
    (hstop : ∀ n D D' G d, n < cap → body D = some D' → close D' D = true →
      At n D (G + cStop D D') d →
      ∃ r, SFunc.RunExactCut fs sevm (k :: C) d f r ∧ (∀ d', r ≠ .at k d') ∧ Exit D' G r)
    (hcap : ∀ n D D' G d, n + 1 = cap → body D = some D' → close D' D = false →
      At n D (G + cCap D D') d →
      ∃ r, SFunc.RunExactCut fs sevm (k :: C) d f r ∧ (∀ d', r ≠ .at k d') ∧ Exit D' G r) :
    ∀ n D v G d, n < cap → fuelLoop body close (cap - n) D = some v →
      At n D (G + fuelCost body close cStep cStop cCap (cap - n) D) d →
      ∃ r, SFunc.RunExactCut fs sevm C d f r ∧ Exit v G r := by
  intro n D v G d hn
  exact RunExactCut_fuelLoop_pass hk hkC At Exit hstep hstop hcap hn
    (fun h1 D' v' G' d' => next (n + 1) D' v' G' d' h1) D v G d

/-- **One peeled pass, liveness, at one counter.**  The pass of a peeled copy `f` (whose back edge
targets `k`) at the single counter `n0` (`n0 + 1 < cap`), followed by the statement for the
continuation at `n0 + 1`.  Unlike `RunExactCut_fuelLoop_peel` it asks nothing of the copy at
other counters, so a copy whose last-pass fall-through is unreachable qualifies. -/
theorem RunExactCut_fuelLoop_peelAt {fs : List SFunc} {sevm : Sevm} {C : List Nat}
    {k : Nat} {g f : SFunc} (hk : fs[k]? = some g) (hkC : k ∉ C) {cap : Nat}
    {body : Nat → Option Nat} {close : Nat → Nat → Bool}
    {cStep cStop cCap : Nat → Nat → Nat}
    (At : Nat → Nat → Nat → Devm → Prop) (Exit : Nat → Nat → Seg → Prop) {n0 : Nat}
    (hn0 : n0 + 1 < cap)
    (next : ∀ D v G d, fuelLoop body close (cap - (n0 + 1)) D = some v →
      At (n0 + 1) D (G + fuelCost body close cStep cStop cCap (cap - (n0 + 1)) D) d →
      ∃ r, SFunc.RunExactCut fs sevm C d g r ∧ Exit v G r)
    (hstep : ∀ D D' G d, body D = some D' → close D' D = false →
      At n0 D (G + cStep D D') d →
      ∃ d', SFunc.RunExactCut fs sevm (k :: C) d f (.at k d') ∧ At (n0 + 1) D' G d')
    (hstop : ∀ D D' G d, body D = some D' → close D' D = true →
      At n0 D (G + cStop D D') d →
      ∃ r, SFunc.RunExactCut fs sevm (k :: C) d f r ∧ (∀ d', r ≠ .at k d') ∧ Exit D' G r) :
    ∀ D v G d, fuelLoop body close (cap - n0) D = some v →
      At n0 D (G + fuelCost body close cStep cStop cCap (cap - n0) D) d →
      ∃ r, SFunc.RunExactCut fs sevm C d f r ∧ Exit v G r := by
  intro D v G d hv hAt
  obtain ⟨m, hm⟩ : ∃ m, cap - n0 = m + 2 := ⟨cap - n0 - 2, by omega⟩
  rw [hm] at hv hAt
  cases hb : body D with
  | none => simp only [fuelLoop, hb, reduceCtorEq] at hv
  | some D' =>
    by_cases hc : close D' D = true
    · have hvD : v = D' := by
        simp only [fuelLoop, hb, hc, ↓reduceIte, Option.some.injEq] at hv
        exact hv.symm
      subst hvD
      have hcost : fuelCost body close cStep cStop cCap (m + 2) D = cStop D v := by
        simp only [fuelCost, hb, hc, ↓reduceIte]
      rw [hcost] at hAt
      obtain ⟨r, hrun, hne, hex⟩ := hstop D v G d hb hc hAt
      exact ⟨r, SFunc.RunExactCut.uncut hrun hne, hex⟩
    · have hc' : close D' D = false := by simpa only [Bool.not_eq_true] using hc
      have hv' : fuelLoop body close (m + 1) D' = some v := by
        simpa only [fuelLoop, hb, hc', Bool.false_eq_true, ↓reduceIte] using hv
      have hcost : G + fuelCost body close cStep cStop cCap (m + 2) D =
          (G + fuelCost body close cStep cStop cCap (m + 1) D') + cStep D D' := by
        simp only [fuelCost, hb, hc', Bool.false_eq_true, ↓reduceIte]
        omega
      rw [hcost] at hAt
      obtain ⟨d', hseg, hAt'⟩ := hstep D D' _ d hb hc' hAt
      have hm' : cap - (n0 + 1) = m + 1 := by omega
      obtain ⟨r, hrun, hex⟩ := next D' v G d' (by rw [hm']; exact hv') (by rw [hm']; exact hAt')
      exact ⟨r, SFunc.RunExactCut.resume hk hkC hseg hrun, hex⟩

end Blanc.Lift
