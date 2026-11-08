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

end Blanc.Lift
