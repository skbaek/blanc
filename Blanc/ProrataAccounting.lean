-- ProrataAccounting.lean : exact finite-trace accounting for PRORATA.

import Blanc.ProrataArithmetic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Blanc

namespace Prorata

open scoped BigOperators

/-- The Nat-level accounting state observed at a semantic PRORATA boundary. -/
structure AccountingSnapshot where
  supply : Nat
  balance : Nat
deriving DecidableEq

/-- The four SF-frozen accounting classes. -/
inductive ProrataAccountingKind where
  | deposit (amount minted : Nat)
  | withdraw (shares paid : Nat)
  | externalCredit (amount : Nat)
  | silent
deriving DecidableEq

/-- Stable chronology metadata retained by the EVM trace carrier. -/
structure ProrataAccountingProvenance where
  blockIndex : Nat
  transactionIndex : Option Nat
  framePath : List Nat
deriving DecidableEq

/-- The exact state equation and pricing fact for one accounting step. -/
inductive ProrataAccountingEffect (o : Nat) :
    AccountingSnapshot → ProrataAccountingKind → AccountingSnapshot → Prop where
  | deposit (supply balance amount minted : Nat)
      (hquote : minted = mintN o amount supply balance) :
      ProrataAccountingEffect o
        ⟨supply, balance⟩ (.deposit amount minted)
        ⟨supply + minted, balance + amount⟩
  | withdraw (supply balance shares paid : Nat)
      (hshares : shares ≤ supply)
      (hquote : paid = payN o shares supply balance) :
      ProrataAccountingEffect o
        ⟨supply, balance⟩ (.withdraw shares paid)
        ⟨supply - shares, balance - paid⟩
  | externalCredit (supply balance amount : Nat)
      (hpositive : 0 < amount) :
      ProrataAccountingEffect o
        ⟨supply, balance⟩ (.externalCredit amount)
        ⟨supply, balance + amount⟩
  | silent (snapshot : AccountingSnapshot) :
      ProrataAccountingEffect o snapshot .silent snapshot

/-- One classified step with its exact semantic boundary and chronology. -/
structure ProrataAccountingStep (o : Nat) where
  pre : AccountingSnapshot
  post : AccountingSnapshot
  kind : ProrataAccountingKind
  provenance : ProrataAccountingProvenance
  effect : ProrataAccountingEffect o pre kind post

namespace ProrataAccountingStep

/-- The virtual-share denominator at a snapshot. -/
def D (o : Nat) (snapshot : AccountingSnapshot) : Nat :=
  snapshot.supply + o

/-- The virtual-asset numerator at a snapshot. -/
def X (snapshot : AccountingSnapshot) : Nat :=
  snapshot.balance + 1

/-- The exact floor-division residue of a priced operation. -/
def rho {o : Nat} (step : ProrataAccountingStep o) : Nat :=
  match step.kind with
  | .deposit amount minted =>
      amount * D o step.pre - minted * X step.pre
  | .withdraw shares paid =>
      shares * X step.pre - paid * D o step.pre
  | .externalCredit _ | .silent => 0

/-- Non-rounding price motion caused by a positive external credit. -/
def kappa {o : Nat} (step : ProrataAccountingStep o) : Nat :=
  match step.kind with
  | .externalCredit amount => amount * D o step.pre
  | .deposit _ _ | .withdraw _ _ | .silent => 0

/-- Every classified operation satisfies the exact one-step dust equation. -/
theorem dust_exact {o : Nat} (ho : o ≠ 0) (step : ProrataAccountingStep o) :
    X step.post * D o step.pre =
      X step.pre * D o step.post + rho step + kappa step := by
  rcases step with ⟨pre, post, kind, provenance, effect⟩
  cases effect with
  | deposit supply balance amount minted hquote =>
      subst minted
      have hres := mintN_residue_eq o amount supply balance
      simp only [X, D, rho, kappa, Nat.add_zero]
      have hrho :
          amount * (supply + o) -
              mintN o amount supply balance * (balance + 1) =
            depositResidueN o amount supply balance := by
        omega
      rw [hrho, Nat.add_zero]
      calc
        (balance + amount + 1) * (supply + o) =
            (balance + 1) * (supply + o) + amount * (supply + o) := by
          rw [show balance + amount + 1 = (balance + 1) + amount by omega,
            Nat.add_mul]
        _ = (balance + 1) * (supply + o) +
              (mintN o amount supply balance * (balance + 1) +
                depositResidueN o amount supply balance) := by
          rw [hres]
        _ = (balance + 1) *
              (supply + mintN o amount supply balance + o) +
                depositResidueN o amount supply balance := by
          rw [show supply + mintN o amount supply balance + o =
              (supply + o) + mintN o amount supply balance by omega,
            Nat.mul_add,
            Nat.mul_comm (mintN o amount supply balance) (balance + 1)]
          simp only [Nat.mul_add, Nat.add_mul]
          ac_rfl
  | withdraw supply balance shares paid hshares hquote =>
      subst paid
      have hpaid := payN_le_balance (balance := balance) ho hshares
      have hres := payN_residue_eq o shares supply balance
      have hpayFloor :
          payN o shares supply balance * (supply + o) ≤
            shares * (balance + 1) := by
        omega
      have hsharesScaled :
          shares * (balance + 1) ≤ (balance + 1) * (supply + o) := by
        have hsD : shares ≤ supply + o :=
          hshares.trans (Nat.le_add_right supply o)
        simpa only [Nat.mul_comm] using
          Nat.mul_le_mul_right (balance + 1) hsD
      simp only [X, D, rho, kappa]
      rw [← Nat.sub_add_comm hpaid, ← Nat.sub_add_comm hshares]
      rw [Nat.sub_mul, Nat.mul_sub]
      rw [Nat.mul_comm (balance + 1) shares, Nat.add_zero]
      omega
  | externalCredit supply balance amount hpositive =>
      simp only [X, D, rho, kappa, Nat.add_zero]
      rw [show balance + amount + 1 = (balance + 1) + amount by omega,
        Nat.add_mul]
  | silent snapshot =>
      simp only [X, D, rho, kappa, Nat.add_zero]

/-- The syntactic residue carried by a step is its Euclidean pricing residue. -/
theorem rho_eq_residue {o : Nat} (step : ProrataAccountingStep o) :
    match step.kind with
    | .deposit amount _ =>
        rho step = depositResidueN o amount step.pre.supply step.pre.balance
    | .withdraw shares _ =>
        rho step = withdrawResidueN o shares step.pre.supply step.pre.balance
    | .externalCredit _ | .silent => rho step = 0 := by
  rcases step with ⟨pre, post, kind, provenance, effect⟩
  cases effect with
  | deposit supply balance amount minted hquote =>
      subst minted
      have hres := mintN_residue_eq o amount supply balance
      simp only [rho, D, X]
      omega
  | withdraw supply balance shares paid hshares hquote =>
      subst paid
      have hres := payN_residue_eq o shares supply balance
      simp only [rho, D, X]
      omega
  | externalCredit supply balance amount hpositive =>
      rfl
  | silent snapshot =>
      rfl

/-- Deposit and withdrawal rounding residues lie below their priced divisor. -/
theorem rho_lt_price_divisor {o : Nat} (ho : o ≠ 0)
    (step : ProrataAccountingStep o) :
    match step.kind with
    | .deposit _ _ => rho step < X step.pre
    | .withdraw _ _ => rho step < D o step.pre
    | .externalCredit _ | .silent => rho step = 0 := by
  rcases step with ⟨pre, post, kind, provenance, effect⟩
  cases effect with
  | deposit supply balance amount minted hquote =>
      subst minted
      have hres := mintN_residue_eq o amount supply balance
      have hlt := mintN_residue_lt o amount supply balance
      simp only [rho, D, X]
      omega
  | withdraw supply balance shares paid hshares hquote =>
      subst paid
      have hres := payN_residue_eq o shares supply balance
      have hlt := payN_residue_lt (shares := shares) (supply := supply)
        (balance := balance) ho
      simp only [rho, D, X]
      omega
  | externalCredit supply balance amount hpositive =>
      rfl
  | silent snapshot =>
      rfl

end ProrataAccountingStep

/-- A Nat-semiring telescope for the exact per-step dust recurrence. -/
theorem dust_telescope_of_step {n : Nat} {x d epsilon : Nat → Nat}
    (hstep : ∀ i < n,
      x (i + 1) * d i = x i * d (i + 1) + epsilon i) :
    x n * (∏ j ∈ Finset.range n, d j) =
      x 0 * (∏ j ∈ Finset.Icc 1 n, d j) +
        ∑ i ∈ Finset.range n,
          epsilon i * (∏ j ∈ Finset.range i, d j) *
            (∏ j ∈ Finset.Icc (i + 2) n, d j) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hprior : ∀ i < n,
          x (i + 1) * d i = x i * d (i + 1) + epsilon i := by
        intro i hi
        exact hstep i (by omega)
      have ih' := ih hprior
      have hlast := hstep n (Nat.lt_succ_self n)
      have hmain :
          (∏ j ∈ Finset.Icc 1 (n + 1), d j) =
            (∏ j ∈ Finset.Icc 1 n, d j) * d (n + 1) := by
        exact Finset.prod_Icc_succ_top (by omega) d
      have hsuffix (i : Nat) (hi : i < n) :
          (∏ j ∈ Finset.Icc (i + 2) (n + 1), d j) =
            (∏ j ∈ Finset.Icc (i + 2) n, d j) * d (n + 1) := by
        exact Finset.prod_Icc_succ_top (by omega) d
      have htail :
          (∑ i ∈ Finset.range n,
              epsilon i * (∏ j ∈ Finset.range i, d j) *
                (∏ j ∈ Finset.Icc (i + 2) (n + 1), d j)) =
            (∑ i ∈ Finset.range n,
                epsilon i * (∏ j ∈ Finset.range i, d j) *
                  (∏ j ∈ Finset.Icc (i + 2) n, d j)) * d (n + 1) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hsuffix i (Finset.mem_range.mp hi)]
        ac_rfl
      have hlastSuffix :
          (∏ j ∈ Finset.Icc (n + 2) (n + 1), d j) = 1 := by
        simp
      rw [Finset.prod_range_succ]
      calc
        x (n + 1) * ((∏ j ∈ Finset.range n, d j) * d n) =
            (x (n + 1) * d n) * (∏ j ∈ Finset.range n, d j) := by
          ac_rfl
        _ = (x n * d (n + 1) + epsilon n) *
              (∏ j ∈ Finset.range n, d j) := by
          rw [hlast]
        _ = (x n * (∏ j ∈ Finset.range n, d j)) * d (n + 1) +
              epsilon n * (∏ j ∈ Finset.range n, d j) := by
          rw [Nat.add_mul]
          ac_rfl
        _ = (x 0 * (∏ j ∈ Finset.Icc 1 n, d j) +
                ∑ i ∈ Finset.range n,
                  epsilon i * (∏ j ∈ Finset.range i, d j) *
                    (∏ j ∈ Finset.Icc (i + 2) n, d j)) * d (n + 1) +
              epsilon n * (∏ j ∈ Finset.range n, d j) := by
          rw [ih']
        _ = x 0 * ((∏ j ∈ Finset.Icc 1 n, d j) * d (n + 1)) +
              (∑ i ∈ Finset.range n,
                  epsilon i * (∏ j ∈ Finset.range i, d j) *
                    (∏ j ∈ Finset.Icc (i + 2) n, d j)) * d (n + 1) +
              epsilon n * (∏ j ∈ Finset.range n, d j) := by
          rw [Nat.add_mul]
          ac_rfl
        _ = x 0 * (∏ j ∈ Finset.Icc 1 (n + 1), d j) +
              ∑ i ∈ Finset.range (n + 1),
                epsilon i * (∏ j ∈ Finset.range i, d j) *
                  (∏ j ∈ Finset.Icc (i + 2) (n + 1), d j) := by
          rw [Finset.sum_range_succ, hmain, htail, hlastSuffix,
            Nat.mul_one]
          ac_rfl

/-- A connected finite accounting path with all `n+1` boundary snapshots. -/
structure ProrataAccountingPath (o : Nat) where
  steps : List (ProrataAccountingStep o)
  snapshot : Fin (steps.length + 1) → AccountingSnapshot
  pre_eq (i : Fin steps.length) :
    snapshot i.castSucc = (steps.get i).pre
  post_eq (i : Fin steps.length) :
    snapshot i.succ = (steps.get i).post

namespace ProrataAccountingPath

open ProrataAccountingStep

/-- The empty connected accounting path at one snapshot. -/
def nil (o : Nat) (snapshot : AccountingSnapshot) :
    ProrataAccountingPath o where
  steps := []
  snapshot := fun _ => snapshot
  pre_eq := by
    intro i
    exact Fin.elim0 i
  post_eq := by
    intro i
    exact Fin.elim0 i

/-- Prepend one exact effect to a connected accounting path. -/
def cons {o : Nat} (step : ProrataAccountingStep o)
    (tail : ProrataAccountingPath o)
    (connect : step.post = tail.snapshot ⟨0, Nat.zero_lt_succ _⟩) :
    ProrataAccountingPath o where
  steps := step :: tail.steps
  snapshot := Fin.cases step.pre tail.snapshot
  pre_eq := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact tail.pre_eq j
  post_eq := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact connect.symm
    · exact tail.post_eq j

/-- The initial snapshot of a connected accounting path. -/
def first {o : Nat} (path : ProrataAccountingPath o) : AccountingSnapshot :=
  path.snapshot ⟨0, Nat.zero_lt_succ _⟩

/-- The terminal snapshot of a connected accounting path. -/
def last {o : Nat} (path : ProrataAccountingPath o) : AccountingSnapshot :=
  path.snapshot ⟨path.steps.length, Nat.lt_succ_self _⟩

@[simp] theorem nil_first {o : Nat} (snapshot : AccountingSnapshot) :
    (nil o snapshot).first = snapshot := rfl

@[simp] theorem nil_last {o : Nat} (snapshot : AccountingSnapshot) :
    (nil o snapshot).last = snapshot := rfl

@[simp] theorem cons_first {o : Nat} (step : ProrataAccountingStep o)
    (tail : ProrataAccountingPath o)
    (connect : step.post = tail.first) :
    (cons step tail connect).first = step.pre := rfl

@[simp] theorem cons_last {o : Nat} (step : ProrataAccountingStep o)
    (tail : ProrataAccountingPath o)
    (connect : step.post = tail.first) :
    (cons step tail connect).last = tail.last := by
  rfl

/-- Total boundary lookup; telescope indices are always within the unclamped range. -/
def snapshotAt {o : Nat} (path : ProrataAccountingPath o) (i : Nat) :
    AccountingSnapshot :=
  path.snapshot ⟨min i path.steps.length,
    Nat.lt_succ_of_le (Nat.min_le_right i path.steps.length)⟩

/-- The numerator at boundary `i`. -/
def XAt {o : Nat} (path : ProrataAccountingPath o) (i : Nat) : Nat :=
  X (path.snapshotAt i)

/-- The denominator at boundary `i`. -/
def DAt {o : Nat} (path : ProrataAccountingPath o) (i : Nat) : Nat :=
  D o (path.snapshotAt i)

/-- The rounding residue of step `i`, zero outside the finite trace. -/
def rhoAt {o : Nat} (path : ProrataAccountingPath o) (i : Nat) : Nat :=
  if hi : i < path.steps.length then
    rho (path.steps.get ⟨i, hi⟩)
  else
    0

/-- The external-credit contribution of step `i`, zero outside the trace. -/
def kappaAt {o : Nat} (path : ProrataAccountingPath o) (i : Nat) : Nat :=
  if hi : i < path.steps.length then
    kappa (path.steps.get ⟨i, hi⟩)
  else
    0

/-- Every in-range accounting-path index exposes the one-step dust equation. -/
theorem dust_exact_at {o : Nat} (path : ProrataAccountingPath o)
    (ho : o ≠ 0) {i : Nat} (hi : i < path.steps.length) :
    path.XAt (i + 1) * path.DAt i =
      path.XAt i * path.DAt (i + 1) + path.rhoAt i + path.kappaAt i := by
  let index : Fin path.steps.length := ⟨i, hi⟩
  let step := path.steps.get index
  have hpre : path.snapshotAt i = step.pre := by
    calc
      path.snapshotAt i = path.snapshot index.castSucc := by
        apply congrArg path.snapshot
        apply Fin.ext
        simp [index, Nat.min_eq_left (Nat.le_of_lt hi)]
      _ = step.pre := by
        simpa only [step] using path.pre_eq index
  have hpost : path.snapshotAt (i + 1) = step.post := by
    calc
      path.snapshotAt (i + 1) = path.snapshot index.succ := by
        apply congrArg path.snapshot
        apply Fin.ext
        simp [index, Nat.min_eq_left (Nat.succ_le_iff.mpr hi)]
      _ = step.post := by
        simpa only [step] using path.post_eq index
  have hstep := ProrataAccountingStep.dust_exact ho step
  simpa only [XAt, DAt, rhoAt, kappaAt, hi, dite_true, hpre, hpost] using hstep

/-- The SF-frozen finite-range cumulative dust identity. -/
theorem prorata_dust_trace_exact {o : Nat} (ho : o ≠ 0)
    (path : ProrataAccountingPath o) :
    let n := path.steps.length
    path.XAt n * (∏ j ∈ Finset.range n, path.DAt j) =
      path.XAt 0 * (∏ j ∈ Finset.Icc 1 n, path.DAt j) +
        ∑ i ∈ Finset.range n,
          (path.rhoAt i + path.kappaAt i) *
            (∏ j ∈ Finset.range i, path.DAt j) *
              (∏ j ∈ Finset.Icc (i + 2) n, path.DAt j) := by
  dsimp only
  apply dust_telescope_of_step
  intro i hi
  simpa only [Nat.add_assoc] using path.dust_exact_at ho hi

end ProrataAccountingPath

end Prorata

end Blanc
