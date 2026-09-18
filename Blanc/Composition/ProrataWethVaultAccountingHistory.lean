-- ProrataWethVaultAccountingHistory.lean : the pair's realized four-quote path and the exact
-- cumulative-dust identity (vault P3) over every realized pair history.

import Blanc.Composition.ProrataWethVaultPairHistory

/-!
# P3 over real pair histories

G7's `FourQuote.FourQuotePath` joins consecutive actual effects at equal *worlds*.  A realized pair
history does not: its records meet at equal pair boundaries -- the vault's storage and WETH's --
while foreign frames, balance moves and transaction boundaries change the rest of the world between
two vault operations.  The telescope only ever reads the accounting snapshot, so this module states
the snapshot-connected path `FourQuote.RealizedPath` (every world-connected path is one,
`FourQuotePath.toRealizedPath`) and reads it off the realized trace.

The path's steps are exactly the trace's accepted operations, in order.  A silent WETH-frame record
keeps both coordinates; a runtime-authorized debit keeps them when it moves nothing, which D9
(`NoVaultAllowanceKeyCollision`) guarantees for every one of them (`PairTraceRealizes.debitAmount_eq_zero`).
Anchored at the pair root's genesis snapshot, the telescope is SF §9 P3: the exact cumulative-residue
identity with rounding, retained self-outbound and outside credit as three separately weighted sums.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune
open scoped BigOperators

namespace FourQuote

/-! ## 1. Snapshot-connected four-quote paths -/

/-- A connected finite trace of actual four-quote effects whose consecutive effects meet at equal
accounting snapshots (not at equal worlds). -/
structure RealizedPath (vault : Adr) : Type where
  steps : List (FourQuoteStep vault)
  snapshot : Fin (steps.length + 1) → Snapshot
  pre_eq (i : Fin steps.length) :
    snapshot i.castSucc = stateSnapshot vault (steps.get i).before
  post_eq (i : Fin steps.length) :
    snapshot i.succ = stateSnapshot vault (steps.get i).after
-- A:2209 with the joins projected through `stateSnapshot`; PA:321 is the snapshot-valued shape.

namespace RealizedPath

/-- The empty path at one snapshot. -/
def nil (vault : Adr) (q : Snapshot) : RealizedPath vault where
  steps := []
  snapshot := fun _ => q
  pre_eq := by
    intro i
    exact Fin.elim0 i
  post_eq := by
    intro i
    exact Fin.elim0 i
-- PA:334–344.

/-- Prepend one actual effect whose post-snapshot is the tail's first snapshot. -/
def cons {vault : Adr} (step : FourQuoteStep vault) (tail : RealizedPath vault)
    (connect : stateSnapshot vault step.after = tail.snapshot ⟨0, Nat.zero_lt_succ _⟩) :
    RealizedPath vault where
  steps := step :: tail.steps
  snapshot := Fin.cases (stateSnapshot vault step.before) tail.snapshot
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
-- PA:346–362.

/-- The first snapshot. -/
def first {vault : Adr} (path : RealizedPath vault) : Snapshot :=
  path.snapshot ⟨0, Nat.zero_lt_succ _⟩

/-- The last snapshot. -/
def last {vault : Adr} (path : RealizedPath vault) : Snapshot :=
  path.snapshot ⟨path.steps.length, Nat.lt_succ_self _⟩
-- PA:364–370.

@[simp] theorem nil_steps {vault : Adr} (q : Snapshot) : (nil vault q).steps = [] := rfl
@[simp] theorem nil_first {vault : Adr} (q : Snapshot) : (nil vault q).first = q := rfl
@[simp] theorem nil_last {vault : Adr} (q : Snapshot) : (nil vault q).last = q := rfl

@[simp] theorem cons_steps {vault : Adr} (step : FourQuoteStep vault) (tail : RealizedPath vault)
    (connect : stateSnapshot vault step.after = tail.first) :
    (cons step tail connect).steps = step :: tail.steps := rfl

@[simp] theorem cons_first {vault : Adr} (step : FourQuoteStep vault) (tail : RealizedPath vault)
    (connect : stateSnapshot vault step.after = tail.first) :
    (cons step tail connect).first = stateSnapshot vault step.before := rfl

@[simp] theorem cons_last {vault : Adr} (step : FourQuoteStep vault) (tail : RealizedPath vault)
    (connect : stateSnapshot vault step.after = tail.first) :
    (cons step tail connect).last = tail.last := by
  rfl
-- PA:372–385.

/-- Total snapshot lookup; the telescope only uses in-range indices. -/
def snapshotAt {vault : Adr} (path : RealizedPath vault) (i : Nat) : Snapshot :=
  path.snapshot ⟨min i path.steps.length,
    Nat.lt_succ_of_le (Nat.min_le_right i path.steps.length)⟩

def xAt {vault : Adr} (path : RealizedPath vault) (i : Nat) : Nat :=
  X (path.snapshotAt i)

def dAt {vault : Adr} (path : RealizedPath vault) (i : Nat) : Nat :=
  D (path.snapshotAt i)

def roundingAt {vault : Adr} (path : RealizedPath vault) (i : Nat) : Nat :=
  if hi : i < path.steps.length then
    roundingContribution (path.steps.get ⟨i, hi⟩).event.operation
  else 0

def retainedAt {vault : Adr} (path : RealizedPath vault) (i : Nat) : Nat :=
  if hi : i < path.steps.length then
    retainedContribution (path.steps.get ⟨i, hi⟩).event.operation
  else 0

def creditAt {vault : Adr} (path : RealizedPath vault) (i : Nat) : Nat :=
  if hi : i < path.steps.length then
    creditContribution (path.steps.get ⟨i, hi⟩).event.operation
  else 0
-- A:2224–2247 with `stateSnapshot vault (worldAt i)` replaced by the snapshot itself.

/-- Index zero is the first snapshot. -/
theorem snapshotAt_zero {vault : Adr} (path : RealizedPath vault) :
    path.snapshotAt 0 = path.first := by
  unfold snapshotAt first
  congr 1
-- PH:181–184.

/-- The last index is the last snapshot. -/
theorem snapshotAt_length {vault : Adr} (path : RealizedPath vault) :
    path.snapshotAt path.steps.length = path.last := by
  unfold snapshotAt last
  apply congrArg path.snapshot
  exact Fin.ext (Nat.min_self _)

/-- An in-range index is the pre-snapshot of its step. -/
theorem snapshotAt_pre {vault : Adr} (path : RealizedPath vault) {i : Nat}
    (hi : i < path.steps.length) :
    path.snapshotAt i = stateSnapshot vault (path.steps.get ⟨i, hi⟩).before := by
  rw [← path.pre_eq ⟨i, hi⟩]
  apply congrArg path.snapshot
  apply Fin.ext
  simp [Nat.min_eq_left (Nat.le_of_lt hi)]

/-- The successor of an in-range index is the post-snapshot of its step. -/
theorem snapshotAt_post {vault : Adr} (path : RealizedPath vault) {i : Nat}
    (hi : i < path.steps.length) :
    path.snapshotAt (i + 1) = stateSnapshot vault (path.steps.get ⟨i, hi⟩).after := by
  rw [← path.post_eq ⟨i, hi⟩]
  apply congrArg path.snapshot
  apply Fin.ext
  simp [Nat.min_eq_left (Nat.succ_le_iff.mpr hi)]
-- the two `calc` blocks of A:2253–2268, factored once.

/-- An in-range step exposes the exact three-contribution recurrence. -/
theorem step_exact_at {vault : Adr} (path : RealizedPath vault) {i : Nat}
    (hi : i < path.steps.length) :
    path.xAt (i + 1) * path.dAt i =
      path.xAt i * path.dAt (i + 1) +
        path.roundingAt i + path.retainedAt i + path.creditAt i := by
  have hstep := (path.steps.get ⟨i, hi⟩).trace_exact
  simpa only [xAt, dAt, roundingAt, retainedAt, creditAt,
    FourQuoteStep.stateTransition, FourQuoteTransition.stateTransition,
    hi, dite_true, path.snapshotAt_pre hi, path.snapshotAt_post hi] using hstep
-- A:2249–2276 (`FourQuotePath.step_exact_at`), closing `simpa only` verbatim.

/-- The Nat-semiring telescope over a snapshot-connected path. -/
theorem dust_telescope {vault : Adr} (path : RealizedPath vault) :
    path.xAt path.steps.length * (∏ j ∈ Finset.range path.steps.length, path.dAt j) =
      path.xAt 0 * (∏ j ∈ Finset.Icc 1 path.steps.length, path.dAt j) +
        ∑ i ∈ Finset.range path.steps.length,
          (path.roundingAt i + path.retainedAt i + path.creditAt i) *
              (∏ j ∈ Finset.range i, path.dAt j) *
                (∏ j ∈ Finset.Icc (i + 2) path.steps.length, path.dAt j) := by
  apply Blanc.Prorata.dust_telescope_of_step
  intro i hi
  simpa only [Nat.add_assoc] using path.step_exact_at hi
-- A:2339–2351 without the `let`.

/-- The same telescope with rounding, retained-asset and outside-credit terms as three separately
weighted sums. -/
theorem dust_telescope_separate {vault : Adr} (path : RealizedPath vault) :
    path.xAt path.steps.length * (∏ j ∈ Finset.range path.steps.length, path.dAt j) =
      path.xAt 0 * (∏ j ∈ Finset.Icc 1 path.steps.length, path.dAt j) +
        (∑ i ∈ Finset.range path.steps.length,
          path.roundingAt i * (∏ j ∈ Finset.range i, path.dAt j) *
            (∏ j ∈ Finset.Icc (i + 2) path.steps.length, path.dAt j)) +
        (∑ i ∈ Finset.range path.steps.length,
          path.retainedAt i * (∏ j ∈ Finset.range i, path.dAt j) *
            (∏ j ∈ Finset.Icc (i + 2) path.steps.length, path.dAt j)) +
        ∑ i ∈ Finset.range path.steps.length,
          path.creditAt i * (∏ j ∈ Finset.range i, path.dAt j) *
            (∏ j ∈ Finset.Icc (i + 2) path.steps.length, path.dAt j) := by
  rw [dust_telescope]
  simp only [Nat.add_mul, Finset.sum_add_distrib]
  ac_rfl
-- A:2354–2370 verbatim after the `let`.

end RealizedPath

/-- Every world-connected G7 path is snapshot-connected, with the same boundary snapshots. -/
def FourQuotePath.toRealizedPath {vault : Adr} (path : FourQuotePath vault) :
    RealizedPath vault where
  steps := path.steps
  snapshot := fun i => stateSnapshot vault (path.world i)
  pre_eq := fun i => congrArg (stateSnapshot vault) (path.pre_eq i)
  post_eq := fun i => congrArg (stateSnapshot vault) (path.post_eq i)

@[simp] theorem FourQuotePath.toRealizedPath_snapshotAt {vault : Adr}
    (path : FourQuotePath vault) (i : Nat) :
    path.toRealizedPath.snapshotAt i = path.snapshotAt i := rfl
-- new; A:2220–2225 (`worldAt`, `snapshotAt`) unfold to the same term.

end FourQuote

/-! ## 2. The realized operations of a pair history -/

/-- The accepted four-quote effect a step is, if it is one. -/
def PairStep.fourQuoteStep? {vault : Adr} {before after : State} :
    PairStep vault before after → Option (FourQuote.FourQuoteStep vault)
  | .operation t _ => some ⟨_, _, t⟩
  | _ => none

/-- A kept step has the step's own endpoints. -/
theorem PairStep.fourQuoteStep?_eq_some {vault : Adr} {before after : State}
    {step : PairStep vault before after} {q : FourQuote.FourQuoteStep vault}
    (h : step.fourQuoteStep? = some q) : q.before = before ∧ q.after = after := by
  cases step with
  | operation t evidence =>
      simp only [PairStep.fourQuoteStep?, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
  | authorizedDebit call foreign owner pair moved vaultKept =>
      simp [PairStep.fourQuoteStep?] at h
  | silent caller vaultKept rowKept =>
      simp [PairStep.fourQuoteStep?] at h

/-- **A dropped step keeps the accounting snapshot.**  A silent WETH-frame step keeps both
coordinates by its own fields; a runtime-authorized debit keeps them when it moves nothing. -/
theorem PairStep.snapshot_eq_of_fourQuoteStep?_eq_none {vault : Adr} {before after : State}
    {step : PairStep vault before after}
    (dropped : step.fourQuoteStep? = none) (zero : step.debitAmount = 0) :
    FourQuote.stateSnapshot vault after = FourQuote.stateSnapshot vault before := by
  cases step with
  | operation t evidence =>
      simp [PairStep.fourQuoteStep?] at dropped
  | authorizedDebit call foreign owner pair moved vaultKept =>
      have wad0 : Sevm.argWord call.sevm 2 = 0 :=
        B256.toNat_inj _ _ (by rw [B256.toNat_zero]; exact zero)
      rw [wad0] at moved
      unfold FourQuote.stateSnapshot
      rw [vaultKept, transfer_src_row_of_zero moved]
  | silent caller vaultKept rowKept =>
      unfold FourQuote.stateSnapshot
      rw [vaultKept, rowKept]
-- the two `same` blocks of U6 §5 (`PairStep.priceLe_of_debitAmount_eq_zero`), as one lemma (D-5).

/-- The accepted four-quote effect a record is, if it is one. -/
def PairStepRecord.fourQuoteStep? {vault : Adr} (r : PairStepRecord vault) :
    Option (FourQuote.FourQuoteStep vault) :=
  r.step.fourQuoteStep?

/-- The accepted operations of a history, in order. -/
def PairStepRecord.fourQuoteSteps {vault : Adr} (steps : List (PairStepRecord vault)) :
    List (FourQuote.FourQuoteStep vault) :=
  steps.filterMap PairStepRecord.fourQuoteStep?
-- shape of `PairStepRecord.ledger` (History.lean:65).

theorem PairStepRecord.fourQuoteSteps_length_le {vault : Adr}
    (steps : List (PairStepRecord vault)) :
    (PairStepRecord.fourQuoteSteps steps).length ≤ steps.length :=
  List.length_filterMap_le _ _

/-- Every kept operation is a record of the history, with that record's endpoints (U9's hook). -/
theorem PairStepRecord.mem_fourQuoteSteps {vault : Adr} {steps : List (PairStepRecord vault)}
    {q : FourQuote.FourQuoteStep vault} (member : q ∈ PairStepRecord.fourQuoteSteps steps) :
    ∃ r ∈ steps, r.step.fourQuoteStep? = some q ∧ q.before = r.before ∧ q.after = r.after := by
  obtain ⟨r, rMember, hq⟩ := List.mem_filterMap.mp member
  obtain ⟨hb, ha⟩ := PairStep.fourQuoteStep?_eq_some hq
  exact ⟨r, rMember, hq, hb, ha⟩

/-! ## 3. The path of a realized history -/

/-- **The list-to-path construction.**  A connected pair replay whose steps debit nothing carries a
snapshot-connected four-quote path whose steps are exactly its accepted operations and whose ends are
the replay's own boundary snapshots.  No connectivity is reconstructed: a kept record joins by its
boundary equations, a dropped one because it keeps the snapshot. -/
theorem PairReplay.exists_realizedPath {vault : Adr} {pre post : PairBoundary}
    {steps : List (PairStepRecord vault)} (replay : PairReplay vault pre steps post) :
    (∀ r ∈ steps, r.step.debitAmount = 0) →
      ∃ path : FourQuote.RealizedPath vault,
        path.steps = PairStepRecord.fourQuoteSteps steps ∧
          path.first = pre.snapshot vault ∧ path.last = post.snapshot vault := by
  induction replay with
  | nil boundary =>
      intro _
      exact ⟨FourQuote.RealizedPath.nil vault (boundary.snapshot vault), rfl, rfl, rfl⟩
  | @cons pre mid post record steps preEq postEq tail ih =>
      intro zero
      obtain ⟨path, hsteps, hfirst, hlast⟩ := ih fun r member => zero r (by simp [member])
      subst preEq
      subst postEq
      rw [PairBoundary.snapshot_ofState] at hfirst
      cases hq : record.step.fourQuoteStep? with
      | none =>
          have kept :=
            PairStep.snapshot_eq_of_fourQuoteStep?_eq_none hq (zero record (by simp))
          refine ⟨path, ?_, ?_, hlast⟩
          · rw [hsteps]
            simp [PairStepRecord.fourQuoteSteps, PairStepRecord.fourQuoteStep?, hq]
          · rw [hfirst, PairBoundary.snapshot_ofState, kept]
      | some q =>
          obtain ⟨hbefore, hafter⟩ := PairStep.fourQuoteStep?_eq_some hq
          have connect : FourQuote.stateSnapshot vault q.after = path.first := by
            rw [hfirst, hafter]
          refine ⟨FourQuote.RealizedPath.cons q path connect, ?_, ?_, hlast⟩
          · show q :: path.steps = _
            rw [hsteps]
            simp [PairStepRecord.fourQuoteSteps, PairStepRecord.fourQuoteStep?, hq]
          · show FourQuote.stateSnapshot vault q.before = _
            rw [hbefore, PairBoundary.snapshot_ofState]
-- PR:1148–1166 (`ProrataAccountingReplay.exists_path`); induction shape U6 §5 (`PairReplay.priceLe`).

/-- **Under D9 the realized trace is a four-quote path anchored at genesis** (design §3.4
`FourQuotePath.ofPairTrace`, snapshot-connected). -/
theorem FourQuote.RealizedPath.ofPairTrace {cfg : ChainConfig} {deployed future : BlockChain}
    {vault : Adr} (root : PairRoot cfg deployed vault) {steps : List (PairStepRecord vault)}
    (realizes : PairTraceRealizes root steps future)
    (collision : NoVaultAllowanceKeyCollision (PairStepRecord.ledger steps) vault) :
    ∃ path : FourQuote.RealizedPath vault,
      path.steps = PairStepRecord.fourQuoteSteps steps ∧
        path.first = ⟨0, 0⟩ ∧ path.last = FourQuote.stateSnapshot vault future.state := by
  obtain ⟨path, hsteps, hfirst, hlast⟩ :=
    realizes.toReplay.exists_realizedPath (realizes.debitAmount_eq_zero collision)
  rw [PairBoundary.snapshot_ofState, root.genesisSnapshot] at hfirst
  rw [PairBoundary.snapshot_ofState] at hlast
  exact ⟨path, hsteps, hfirst, hlast⟩
-- PH:231–232 (`exists_path` of `toAccountingReplay`) + U6 `backing`'s genesis rewrite.

/-! ## 4. P3 -/

/-- **P3 (SF §9): the exact cumulative-residue identity over every realized pair history.**  The
path's steps are exactly the trace's accepted operations in order, its ends are the genesis snapshot
and the continuation's own, and the telescope separates rounding, retained self-outbound and outside
credit.  Anchoring at the pair root gives `X₀ = 1` and `D₀ = O`, so the leading term is the bare
denominator product.  The only premise beyond the realized trace is D9. -/
theorem pair_realized_dust_trace_exact {cfg : ChainConfig} {deployed future : BlockChain}
    {vault : Adr} (root : PairRoot cfg deployed vault) {steps : List (PairStepRecord vault)}
    (realizes : PairTraceRealizes root steps future)
    (collision : NoVaultAllowanceKeyCollision (PairStepRecord.ledger steps) vault) :
    ∃ path : FourQuote.RealizedPath vault,
      path.steps = PairStepRecord.fourQuoteSteps steps ∧
      path.snapshotAt 0 = ⟨0, 0⟩ ∧
      path.snapshotAt path.steps.length = FourQuote.stateSnapshot vault future.state ∧
      path.xAt 0 = 1 ∧
      path.dAt 0 = Blanc.ProrataWethVault.offsetN ∧
      path.xAt path.steps.length * (∏ j ∈ Finset.range path.steps.length, path.dAt j) =
        (∏ j ∈ Finset.Icc 1 path.steps.length, path.dAt j) +
          (∑ i ∈ Finset.range path.steps.length,
            path.roundingAt i * (∏ j ∈ Finset.range i, path.dAt j) *
              (∏ j ∈ Finset.Icc (i + 2) path.steps.length, path.dAt j)) +
          (∑ i ∈ Finset.range path.steps.length,
            path.retainedAt i * (∏ j ∈ Finset.range i, path.dAt j) *
              (∏ j ∈ Finset.Icc (i + 2) path.steps.length, path.dAt j)) +
          ∑ i ∈ Finset.range path.steps.length,
            path.creditAt i * (∏ j ∈ Finset.range i, path.dAt j) *
              (∏ j ∈ Finset.Icc (i + 2) path.steps.length, path.dAt j) := by
  obtain ⟨path, hsteps, hfirst, hlast⟩ :=
    FourQuote.RealizedPath.ofPairTrace root realizes collision
  have hzero : path.snapshotAt 0 = ⟨0, 0⟩ := by
    rw [path.snapshotAt_zero, hfirst]
  have hend : path.snapshotAt path.steps.length = FourQuote.stateSnapshot vault future.state := by
    rw [path.snapshotAt_length, hlast]
  have hX : path.xAt 0 = 1 := by
    simp [FourQuote.RealizedPath.xAt, FourQuote.X, hzero]
  have hD : path.dAt 0 = Blanc.ProrataWethVault.offsetN := by
    simp [FourQuote.RealizedPath.dAt, FourQuote.D, hzero]
  refine ⟨path, hsteps, hzero, hend, hX, hD, ?_⟩
  have hexact := path.dust_telescope_separate
  rw [hX, Nat.one_mul] at hexact
  exact hexact
-- PH:216–257 (`prorata_realized_dust_trace_exact`), arm for arm.

end Blanc.Composition.ProrataWethVault
