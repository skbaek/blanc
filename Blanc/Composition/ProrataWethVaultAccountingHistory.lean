-- ProrataWethVaultAccountingHistory.lean : the pair's realized four-quote path and the exact
-- cumulative-dust identity (vault P3) over every realized pair history.

import Blanc.Composition.ProrataWethVaultPairHistory
import Blanc.Composition.ProrataWethVaultCoalition

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

/-! ## 5. The realized coalition overlay (vault U9)

PRORATA keys its realized coalition accounting on a step's actor, because a PRORATA caller is the share holder.  A
pair record's actor is only the emitting frame's caller, while the vault separates caller, owner and receiver and a
WETH credit is paid by its source.  This section reads each accepted operation once into its role-resolved
`PairFlow`, keys every realized sum and the victim schedule on it, and folds one `PairAttackStep` per record onto
U8's `PairAttackPath`.  The victim is the protected party: one exact deposit to itself, optionally one exact full
redeem to itself, no other cash of its own, and no share gift that takes its row below the open deposit's shares. -/

open Blanc.ProrataWethVault (offsetN offsetN_ne_zero two_le_offsetN supplySlot)

/-! ### 5.1 Role-resolved flows -/

/-- The economic content of one record, with every role an address and every amount a `Nat`. -/
inductive PairFlow where
  /-- `deposit` (`exact`) or `mint`: `payer` pays `assets` and `receiver` is minted `shares`. -/
  | inbound (payer receiver : Adr) (assets shares : Nat) (exact : Bool)
  /-- `redeem` (`exact`) or `withdraw`: `owner` burns `shares` and `receiver` is paid `assets`, or the vault keeps
  them (`retained`, receiver = vault). -/
  | outbound (owner receiver : Adr) (shares assets : Nat) (exact retained : Bool)
  /-- An outside WETH credit to the vault, paid by `source`. -/
  | credit (source : Adr) (amount : Nat)
  /-- `transfer` / `transferFrom`: `amount` shares from `source` to `receiver`. -/
  | shareMove (source receiver : Adr) (amount : Nat)
  /-- `approve`, a silent WETH frame, or a zero-amount authorized debit. -/
  | silent

/-- The flow of an accepted operation. -/
def FourQuote.FourQuoteOperation.flow {vault : Adr} {sevm : Sevm} {pre post : Devm} :
    FourQuote.FourQuoteOperation vault sevm pre post → PairFlow
  | .deposit words _ _ _ _ _ _ =>
      .inbound sevm.caller words.receiver.toAdr words.assets.toNat words.shares.toNat true
  | .mint words _ _ _ _ _ _ =>
      .inbound sevm.caller words.receiver.toAdr words.assets.toNat words.shares.toNat false
  | .withdrawNormal words _ _ _ _ _ =>
      .outbound words.owner.toAdr words.receiver.toAdr words.shares.toNat words.assets.toNat false false
  | .redeemNormal words _ _ _ _ _ =>
      .outbound words.owner.toAdr words.receiver.toAdr words.shares.toNat words.assets.toNat true false
  | .withdrawSelf words _ _ _ _ _ =>
      .outbound words.owner.toAdr words.receiver.toAdr words.shares.toNat words.assets.toNat false true
  | .redeemSelf words _ _ _ _ _ =>
      .outbound words.owner.toAdr words.receiver.toAdr words.shares.toNat words.assets.toNat true true
  | .credit words _ _ _ _ _ => .credit words.source words.amount.toNat
  | .transfer words _ _ _ _ _ _ _ _ => .shareMove words.owner words.receiver.toAdr words.amount.toNat
  | .transferFrom words _ _ _ _ _ _ _ _ _ =>
      .shareMove words.owner.toAdr words.receiver.toAdr words.amount.toNat
  | .approve _ _ _ _ _ _ _ _ _ => .silent
-- binder counts: A:1068–1107 (`FourQuoteShareRowsMove`), arm for arm; roles: A:741–779 and the A:782 guards
-- (`depositorNotVault` is the caller, `transfer.owner = sevm.caller`).

def PairStep.flow {vault : Adr} {before after : State} : PairStep vault before after → PairFlow
  | .operation t _ => t.operation.flow
  | _ => .silent

namespace PairStepRecord

variable {vault : Adr}

def flow (r : PairStepRecord vault) : PairFlow := r.step.flow
/-- The accounting snapshot a record starts from (PRORATA's `step.pre`). -/
def pre (r : PairStepRecord vault) : FourQuote.Snapshot := FourQuote.stateSnapshot vault r.before
def post (r : PairStepRecord vault) : FourQuote.Snapshot := FourQuote.stateSnapshot vault r.after
def victimRowBefore (victim : Adr) (r : PairStepRecord vault) : Nat :=
  (Stor.rest (r.before.getStor vault) victim).toNat
def victimRowAfter (victim : Adr) (r : PairStepRecord vault) : Nat :=
  (Stor.rest (r.after.getStor vault) victim).toNat

end PairStepRecord

/-- What a flow does to the accounting snapshot, with its quote read as a model quote. -/
def PairFlow.Accounts : PairFlow → FourQuote.Snapshot → FourQuote.Snapshot → Prop
  | .inbound _ _ assets shares exact, pre, post =>
      post = ⟨pre.supply + shares, pre.balance + assets⟩ ∧
        shares ≤ Blanc.Prorata.mintN offsetN assets pre.supply pre.balance ∧
        (exact = true → shares = Blanc.Prorata.mintN offsetN assets pre.supply pre.balance)
  | .outbound _ _ shares assets exact retained, pre, post =>
      shares ≤ pre.supply ∧ assets ≤ Blanc.Prorata.payN offsetN shares pre.supply pre.balance ∧
        (exact = true → assets = Blanc.Prorata.payN offsetN shares pre.supply pre.balance) ∧
        post = ⟨pre.supply - shares, if retained = true then pre.balance else pre.balance - assets⟩
  | .credit _ amount, pre, post => post = ⟨pre.supply, pre.balance + amount⟩
  | .shareMove _ _ _, pre, post => post = pre
  | .silent, pre, post => post = pre

/-- What a flow does to the victim's share row. -/
def PairFlow.VictimRow : PairFlow → Adr → Nat → Nat → Prop
  | .inbound _ receiver _ shares _, victim, row, row' =>
      row' = row + if receiver = victim then shares else 0
  | .outbound owner _ shares _ _ _, victim, row, row' =>
      row' + (if owner = victim then shares else 0) = row
  | .credit _ _, _, row, row' => row' = row
  | .shareMove source receiver amount, victim, row, row' =>
      row' + (if source = victim then amount else 0) = row + if receiver = victim then amount else 0
  | .silent, _, row, row' => row' = row

/-- The party whose share row a flow debits, and by how much. -/
def PairFlow.debited? : PairFlow → Option (Adr × Nat)
  | .outbound owner _ shares _ _ _ => some (owner, shares)
  | .shareMove source _ amount => some (source, amount)
  | _ => none

/-- The victim's own economic moves: cash it pays in or takes out to itself.  Share gifts it makes are not moves;
the lock bounds them. -/
def PairFlow.victimOwn (victim : Adr) : PairFlow → Bool
  | .inbound payer _ _ _ _ => decide (payer = victim)
  | .outbound owner receiver _ _ _ retained =>
      decide (owner = victim ∧ receiver = victim ∧ retained = false)
  | .credit source _ => decide (source = victim)
  | _ => false

/-! ### 5.2 The ten tags, once -/

/-- **Every accepted operation accounts exactly as its flow says.** -/
theorem FourQuote.FourQuoteOperation.flow_accounts {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (operation : FourQuote.FourQuoteOperation vault sevm pre post) :
    operation.flow.Accounts (vaultSnapshot vault pre) (vaultSnapshot vault post) := by
  cases operation with
  | deposit words target depositorNotVault supplyNof rowNof quote effect =>
      subst vault
      have hpost := FourQuote.inboundEffect_normal_snapshot depositorNotVault supplyNof rowNof effect
      simp only [snapshotAt_eq] at hpost quote
      simp only [FourQuote.FourQuoteOperation.flow, PairFlow.Accounts]
      exact ⟨by simpa only [FourQuote.normalInbound] using hpost,
        Nat.le_of_eq (quote.trans (mintN_offsetN_eq _ _ _).symm),
        fun _ => quote.trans (mintN_offsetN_eq _ _ _).symm⟩
  | mint words target depositorNotVault supplyNof rowNof quote effect =>
      subst vault
      have hpost := FourQuote.inboundEffect_normal_snapshot depositorNotVault supplyNof rowNof effect
      simp only [snapshotAt_eq] at hpost quote
      simp only [FourQuote.FourQuoteOperation.flow, PairFlow.Accounts]
      refine ⟨by simpa only [FourQuote.normalInbound] using hpost, ?_,
        fun h => (Bool.false_ne_true h).elim⟩
      rw [quote]
      exact minted_le_mintN_of_previewMintN _ _ _
  | withdrawNormal words target receiverNotVault burnable quote effect =>
      subst vault
      have hcovered := FourQuote.outboundEffect_covered effect
      have hpost := FourQuote.outboundEffect_normal_snapshot receiverNotVault burnable hcovered effect
      simp only [snapshotAt_eq] at hpost quote burnable
      simp only [FourQuote.FourQuoteOperation.flow, PairFlow.Accounts, Bool.false_eq_true, ↓reduceIte]
      refine ⟨burnable, ?_, fun h => h.elim,
        by simpa only [FourQuote.normalOutbound] using hpost⟩
      rw [quote]
      exact paid_le_payN_of_previewWithdrawN _ _ _
  | redeemNormal words target receiverNotVault burnable quote effect =>
      subst vault
      have hcovered := FourQuote.outboundEffect_covered effect
      have hpost := FourQuote.outboundEffect_normal_snapshot receiverNotVault burnable hcovered effect
      simp only [snapshotAt_eq] at hpost quote burnable
      simp only [FourQuote.FourQuoteOperation.flow, PairFlow.Accounts, Bool.false_eq_true, ↓reduceIte]
      exact ⟨burnable, Nat.le_of_eq (quote.trans (payN_offsetN_eq _ _ _).symm),
        fun _ => quote.trans (payN_offsetN_eq _ _ _).symm,
        by simpa only [FourQuote.normalOutbound] using hpost⟩
  | withdrawSelf words target receiverIsVault burnable quote effect =>
      subst vault
      have hpost := FourQuote.outboundEffect_retained_snapshot receiverIsVault burnable effect
      simp only [snapshotAt_eq] at hpost quote burnable
      simp only [FourQuote.FourQuoteOperation.flow, PairFlow.Accounts, ↓reduceIte]
      refine ⟨burnable, ?_, fun h => (Bool.false_ne_true h).elim,
        by simpa only [FourQuote.retainedOutbound] using hpost⟩
      rw [quote]
      exact paid_le_payN_of_previewWithdrawN _ _ _
  | redeemSelf words target receiverIsVault burnable quote effect =>
      subst vault
      have hpost := FourQuote.outboundEffect_retained_snapshot receiverIsVault burnable effect
      simp only [snapshotAt_eq] at hpost quote burnable
      simp only [FourQuote.FourQuoteOperation.flow, PairFlow.Accounts, ↓reduceIte]
      exact ⟨burnable, Nat.le_of_eq (quote.trans (payN_offsetN_eq _ _ _).symm),
        fun _ => quote.trans (payN_offsetN_eq _ _ _).symm,
        by simpa only [FourQuote.retainedOutbound] using hpost⟩
  | credit words wethTarget sourceNotVault supplyKept rowNof effect =>
      have hpost := FourQuote.externalCredit_snapshot sourceNotVault supplyKept rowNof effect
      simp only [FourQuote.FourQuoteOperation.flow, PairFlow.Accounts]
      simpa only [FourQuote.normalInbound, Nat.add_zero] using hpost
  | transfer words target owner receiver amount config memoryWf run selectorEq =>
      have hkeep := Blanc.Prorata.ProrataAccountingEffect.silent_inv
        (transferEffect_accountingStep config memoryWf run selectorEq)
      simp only [snapshotAt_eq, target] at hkeep
      exact hkeep
  | transferFrom words target spender owner receiver amount config memoryWf run selectorEq =>
      have hkeep := Blanc.Prorata.ProrataAccountingEffect.silent_inv
        (transferFromEffect_accountingStep config memoryWf run selectorEq)
      simp only [snapshotAt_eq, target] at hkeep
      exact hkeep
  | approve words target owner spender amount config memoryWf run selectorEq =>
      have hkeep := Blanc.Prorata.ProrataAccountingEffect.silent_inv
        (approveEffect_accountingStep config memoryWf run selectorEq)
      simp only [snapshotAt_eq, target] at hkeep
      exact hkeep
-- arm layout: A:2134–2172 (`FourQuoteOperation.step_exact`); snapshot bridges A:238/306/347/379/663; share-writer
-- arms: A:2070–2080 (`silent_step_exact`: `silent_inv`, `snapshotAt_eq`, `target`); quote bridges C:240–258.

/-- **The victim's share row moves exactly as the flow says**: G7's coalition equation at `{victim}`. -/
theorem FourQuote.FourQuoteShareEvidence.victimRow {vault : Adr} {sevm : Sevm} {pre post : Devm}
    {operation : FourQuote.FourQuoteOperation vault sevm pre post}
    (evidence : FourQuote.FourQuoteShareEvidence operation)
    (conserved : LedgerConserved supplySlot (Devm.getStor pre vault)) (victim : Adr) :
    operation.flow.VictimRow victim (Stor.rest (Devm.getStor pre vault) victim).toNat
      (Stor.rest (Devm.getStor post vault) victim).toNat := by
  have hcoal : FourQuote.FourQuoteShareCoalition {victim} operation := by
    by_cases vaultTarget : sevm.currentTarget = vault
    · exact evidence.coalition (by rw [vaultTarget]; exact conserved)
    · cases evidence with
      | credit words wethTarget sourceNotVault supplyKept rowNof effect vaultKept =>
          dsimp only [FourQuote.FourQuoteShareCoalition]
          rw [vaultKept]
      | deposit words target => exact absurd target vaultTarget
      | mint words target => exact absurd target vaultTarget
      | withdrawNormal words target => exact absurd target vaultTarget
      | redeemNormal words target => exact absurd target vaultTarget
      | withdrawSelf words target => exact absurd target vaultTarget
      | redeemSelf words target => exact absurd target vaultTarget
      | transfer words target => exact absurd target vaultTarget
      | transferFrom words target => exact absurd target vaultTarget
      | approve words target => exact absurd target vaultTarget
  cases evidence with
  | credit words wethTarget sourceNotVault supplyKept rowNof effect vaultKept =>
      simp only [FourQuote.FourQuoteShareCoalition, ledgerSumOn, Finset.sum_singleton] at hcoal
      exact hcoal
  | deposit words target =>
      subst vault
      simp only [FourQuote.FourQuoteShareCoalition, ledgerSumOn, Finset.sum_singleton,
        Finset.mem_singleton] at hcoal
      exact hcoal
  | mint words target =>
      subst vault
      simp only [FourQuote.FourQuoteShareCoalition, ledgerSumOn, Finset.sum_singleton,
        Finset.mem_singleton] at hcoal
      exact hcoal
  | withdrawNormal words target =>
      subst vault
      simp only [FourQuote.FourQuoteShareCoalition, ledgerSumOn, Finset.sum_singleton,
        Finset.mem_singleton] at hcoal
      exact hcoal
  | redeemNormal words target =>
      subst vault
      simp only [FourQuote.FourQuoteShareCoalition, ledgerSumOn, Finset.sum_singleton,
        Finset.mem_singleton] at hcoal
      exact hcoal
  | withdrawSelf words target =>
      subst vault
      simp only [FourQuote.FourQuoteShareCoalition, ledgerSumOn, Finset.sum_singleton,
        Finset.mem_singleton] at hcoal
      exact hcoal
  | redeemSelf words target =>
      subst vault
      simp only [FourQuote.FourQuoteShareCoalition, ledgerSumOn, Finset.sum_singleton,
        Finset.mem_singleton] at hcoal
      exact hcoal
  | transfer words target =>
      subst vault
      simp only [FourQuote.FourQuoteShareCoalition, ledgerSumOn, Finset.sum_singleton,
        Finset.mem_singleton] at hcoal
      exact hcoal
  | transferFrom words target =>
      subst vault
      simp only [FourQuote.FourQuoteShareCoalition, ledgerSumOn, Finset.sum_singleton,
        Finset.mem_singleton] at hcoal
      exact hcoal
  | approve words target =>
      subst vault
      simp only [FourQuote.FourQuoteShareCoalition, ledgerSumOn, Finset.sum_singleton] at hcoal
      exact hcoal
-- A:1393–1446 (`FourQuoteShareEvidence.coalition`) at the singleton coalition; the target split is
-- A:1309–1350's `rw [← target] at conserved` made total, since the credit arm's target is WETH.

/-- **The debited party's row covers the debit.** -/
theorem FourQuote.FourQuoteShareEvidence.debited_le_row {vault : Adr} {sevm : Sevm} {pre post : Devm}
    {operation : FourQuote.FourQuoteOperation vault sevm pre post}
    (evidence : FourQuote.FourQuoteShareEvidence operation) {party : Adr} {amount : Nat}
    (debited : operation.flow.debited? = some (party, amount)) :
    amount ≤ (Stor.rest (Devm.getStor pre vault) party).toNat := by
  have rows := evidence.actual_share_rows_move
  cases evidence with
  | withdrawNormal words target receiverNotVault burnable quote effect receiverArg ownerArg
      receiverValid ownerValid covered =>
      subst vault
      simp only [FourQuote.FourQuoteOperation.flow, PairFlow.debited?, Option.some.injEq,
        Prod.mk.injEq] at debited
      obtain ⟨rfl, rfl⟩ := debited
      change words.shares.toNat ≤
        ((Devm.getStor pre sevm.currentTarget).get words.owner.toAdr.toB256).toNat
      rw [toB256_toAdr ownerValid]
      exact covered
  | redeemNormal words target receiverNotVault burnable quote effect receiverArg ownerArg
      receiverValid ownerValid covered =>
      subst vault
      simp only [FourQuote.FourQuoteOperation.flow, PairFlow.debited?, Option.some.injEq,
        Prod.mk.injEq] at debited
      obtain ⟨rfl, rfl⟩ := debited
      change words.shares.toNat ≤
        ((Devm.getStor pre sevm.currentTarget).get words.owner.toAdr.toB256).toNat
      rw [toB256_toAdr ownerValid]
      exact covered
  | withdrawSelf words target receiverIsVault burnable quote effect receiverArg ownerArg
      receiverValid ownerValid covered =>
      subst vault
      simp only [FourQuote.FourQuoteOperation.flow, PairFlow.debited?, Option.some.injEq,
        Prod.mk.injEq] at debited
      obtain ⟨rfl, rfl⟩ := debited
      change words.shares.toNat ≤
        ((Devm.getStor pre sevm.currentTarget).get words.owner.toAdr.toB256).toNat
      rw [toB256_toAdr ownerValid]
      exact covered
  | redeemSelf words target receiverIsVault burnable quote effect receiverArg ownerArg
      receiverValid ownerValid covered =>
      subst vault
      simp only [FourQuote.FourQuoteOperation.flow, PairFlow.debited?, Option.some.injEq,
        Prod.mk.injEq] at debited
      obtain ⟨rfl, rfl⟩ := debited
      change words.shares.toNat ≤
        ((Devm.getStor pre sevm.currentTarget).get words.owner.toAdr.toB256).toNat
      rw [toB256_toAdr ownerValid]
      exact covered
  | transfer words target =>
      subst vault
      simp only [FourQuote.FourQuoteOperation.flow, PairFlow.debited?, Option.some.injEq,
        Prod.mk.injEq] at debited
      obtain ⟨rfl, rfl⟩ := debited
      simp only [FourQuote.FourQuoteShareRowsMove] at rows
      exact B256.toNat_le_toNat rows.1
  | transferFrom words target =>
      subst vault
      simp only [FourQuote.FourQuoteOperation.flow, PairFlow.debited?, Option.some.injEq,
        Prod.mk.injEq] at debited
      obtain ⟨rfl, rfl⟩ := debited
      simp only [FourQuote.FourQuoteShareRowsMove] at rows
      exact B256.toNat_le_toNat rows.1
  | deposit => simp [FourQuote.FourQuoteOperation.flow, PairFlow.debited?] at debited
  | mint => simp [FourQuote.FourQuoteOperation.flow, PairFlow.debited?] at debited
  | credit => simp [FourQuote.FourQuoteOperation.flow, PairFlow.debited?] at debited
  | approve => simp [FourQuote.FourQuoteOperation.flow, PairFlow.debited?] at debited
-- outbound arms: A:1170–1180 (private `share_covered_of_nat`, four lines transcribed); share-writer arms: the
-- `Transfer` relation's first conjunct (Ladder:46) through A:1352 (`actual_share_rows_move`).

/-! ### 5.3 Steps and records -/

theorem PairStep.accounts {vault : Adr} {before after : State} (step : PairStep vault before after)
    (zero : step.debitAmount = 0) :
    step.flow.Accounts (FourQuote.stateSnapshot vault before) (FourQuote.stateSnapshot vault after) := by
  match step, zero with
  | .operation t _, _ =>
      simpa only [PairStep.flow, FourQuote.vaultSnapshot_state, t.preState, t.postState] using
        t.operation.flow_accounts
  | .authorizedDebit call foreign owner pair moved vaultKept, zero =>
      show FourQuote.stateSnapshot vault after = FourQuote.stateSnapshot vault before
      exact PairStep.snapshot_eq_of_fourQuoteStep?_eq_none
        (step := .authorizedDebit call foreign owner pair moved vaultKept) rfl zero
  | .silent caller vaultKept rowKept, _ =>
      show FourQuote.stateSnapshot vault after = FourQuote.stateSnapshot vault before
      exact PairStep.snapshot_eq_of_fourQuoteStep?_eq_none
        (step := .silent caller vaultKept rowKept) rfl rfl
-- U6 §5 (`PairStep.priceLe_of_debitAmount_eq_zero`): same `match step, zero` and operation `simpa only`;
-- dropped arms: U7 §2 (`snapshot_eq_of_fourQuoteStep?_eq_none`).

theorem PairStep.victimRow {vault : Adr} {before after : State} (step : PairStep vault before after)
    (conserved : LedgerConserved supplySlot (before.getStor vault)) (victim : Adr) :
    step.flow.VictimRow victim (Stor.rest (before.getStor vault) victim).toNat
      (Stor.rest (after.getStor vault) victim).toNat := by
  match step with
  | .operation t evidence =>
      have entry : Devm.getStor t.entry vault = before.getStor vault :=
        congrArg (fun w : State => w.getStor vault) t.preState
      have exit : Devm.getStor t.exit vault = after.getStor vault :=
        congrArg (fun w : State => w.getStor vault) t.postState
      rw [← entry] at conserved
      rw [← entry, ← exit]
      exact evidence.victimRow conserved victim
  | .authorizedDebit _ _ _ _ _ vaultKept =>
      show (Stor.rest (after.getStor vault) victim).toNat = (Stor.rest (before.getStor vault) victim).toNat
      rw [vaultKept]
  | .silent _ vaultKept _ =>
      show (Stor.rest (after.getStor vault) victim).toNat = (Stor.rest (before.getStor vault) victim).toNat
      rw [vaultKept]
-- U5:88–111 (`PairStep.conserved`), same three arms and the same `entry`/`exit` equations.

theorem PairStep.debited_le_row {vault : Adr} {before after : State} (step : PairStep vault before after)
    {party : Adr} {amount : Nat} (debited : step.flow.debited? = some (party, amount)) :
    amount ≤ (Stor.rest (before.getStor vault) party).toNat := by
  match step, debited with
  | .operation t evidence, debited =>
      have entry : Devm.getStor t.entry vault = before.getStor vault :=
        congrArg (fun w : State => w.getStor vault) t.preState
      rw [← entry]
      exact evidence.debited_le_row debited
  | .authorizedDebit .., debited => simp [PairStep.flow, PairFlow.debited?] at debited
  | .silent .., debited => simp [PairStep.flow, PairFlow.debited?] at debited

namespace PairStepRecord

variable {vault : Adr}

theorem accounts (r : PairStepRecord vault) (zero : r.step.debitAmount = 0) :
    r.flow.Accounts r.pre r.post :=
  r.step.accounts zero

theorem victimRow (r : PairStepRecord vault)
    (conserved : LedgerConserved supplySlot (r.before.getStor vault)) (victim : Adr) :
    r.flow.VictimRow victim (r.victimRowBefore victim) (r.victimRowAfter victim) :=
  r.step.victimRow conserved victim

/-- A debit of a party other than the victim fits beside the victim's row under supply. -/
theorem debited_add_victimRow_le (r : PairStepRecord vault) {victim party : Adr} {amount : Nat}
    (conserved : LedgerConserved supplySlot (r.before.getStor vault))
    (debited : r.flow.debited? = some (party, amount)) (ne : party ≠ victim) :
    amount + r.victimRowBefore victim ≤ r.pre.supply := by
  have hle := r.step.debited_le_row debited
  have hsum := add_le_sum_of_ne (Stor.rest (r.before.getStor vault)) ne
  have hcons : ((r.before.getStor vault).get supplySlot).toNat = balSum (r.before.getStor vault) :=
    conserved
  unfold balSum at hcons
  show amount + (Stor.rest (r.before.getStor vault) victim).toNat ≤
    ((r.before.getStor vault).get supplySlot).toNat
  omega
-- T:557–564 (`add_le_sum_of_ne` against the ledger identity); `LedgerConserved` LC:27, `balSum` CommonCore:499.

end PairStepRecord

/-! ### 5.4 Realized coalition accounting -/

/-- Cash one record pays into the vault on the non-victim side (T:285). -/
def stepCredit {vault : Adr} (victim : Adr) (r : PairStepRecord vault) : Nat :=
  match r.flow with
  | .inbound payer _ assets _ _ => if payer = victim then 0 else assets
  | .credit _ amount => amount
  | _ => 0

/-- Cash one record pays out of the vault to the non-victim side, or on the non-victim side's burn (T:295). -/
def stepPayout {vault : Adr} (victim : Adr) (r : PairStepRecord vault) : Nat :=
  match r.flow with
  | .outbound owner receiver _ assets _ retained =>
      if retained = true then 0 else if owner = victim ∧ receiver = victim then 0 else assets
  | _ => 0

/-- D1(a) ceiling price, at the record's own pre-snapshot, of shares the non-victim side takes from the victim. -/
def stepSharesIn {vault : Adr} (victim : Adr) (r : PairStepRecord vault) : Nat :=
  match r.flow with
  | .outbound owner receiver shares _ _ retained =>
      if owner = victim ∧ (retained = true ∨ receiver ≠ victim) then
        ceilClaimN offsetN shares r.pre.supply r.pre.balance
      else 0
  | .shareMove source receiver amount =>
      if source = victim ∧ receiver ≠ victim then ceilClaimN offsetN amount r.pre.supply r.pre.balance
      else 0
  | _ => 0

/-- D1(a) floor price, at the record's own pre-snapshot, of shares the non-victim side sends the victim. -/
def stepSharesOut {vault : Adr} (victim : Adr) (r : PairStepRecord vault) : Nat :=
  match r.flow with
  | .inbound payer receiver _ shares _ =>
      if payer ≠ victim ∧ receiver = victim then
        Blanc.Prorata.claimN offsetN shares r.pre.supply r.pre.balance
      else 0
  | .shareMove source receiver amount =>
      if source ≠ victim ∧ receiver = victim then
        Blanc.Prorata.claimN offsetN amount r.pre.supply r.pre.balance
      else 0
  | _ => 0

def inA {vault : Adr} (victim : Adr) (charge : PairStepRecord vault → Blanc.Prorata.AttackAttribution)
    (steps : List (PairStepRecord vault)) : Nat :=
  (steps.map fun r => (charge r).coalitionAmount (stepCredit victim r)).sum

def outA {vault : Adr} (victim : Adr) (charge : PairStepRecord vault → Blanc.Prorata.AttackAttribution)
    (steps : List (PairStepRecord vault)) : Nat :=
  (steps.map fun r => (charge r).coalitionAmount (stepPayout victim r)).sum

def outsideSubsidy {vault : Adr} (victim : Adr)
    (charge : PairStepRecord vault → Blanc.Prorata.AttackAttribution)
    (steps : List (PairStepRecord vault)) : Nat :=
  (steps.map fun r => (charge r).outsideAmount (stepCredit victim r)).sum

def sharesIn {vault : Adr} (victim : Adr) (steps : List (PairStepRecord vault)) : Nat :=
  (steps.map (stepSharesIn victim)).sum

def sharesOut {vault : Adr} (victim : Adr) (steps : List (PairStepRecord vault)) : Nat :=
  (steps.map (stepSharesOut victim)).sum

def coalitionCharge {vault : Adr} : PairStepRecord vault → Blanc.Prorata.AttackAttribution :=
  fun _ => .coalition

theorem outsideSubsidy_coalitionCharge {vault : Adr} (victim : Adr)
    (steps : List (PairStepRecord vault)) : outsideSubsidy victim coalitionCharge steps = 0 := by
  induction steps with
  | nil => rfl
  | cons s ss ih => simp [outsideSubsidy, coalitionCharge, Blanc.Prorata.AttackAttribution.outsideAmount]
-- T:306–335 verbatim over `PairStepRecord`; the two `_coalitionCharge` `rfl` lemmas (T:339/345) transcribe too.

/-! ### 5.5 The victim schedule -/

def victimMove {vault : Adr} (victim : Adr) (r : PairStepRecord vault) : Bool := r.flow.victimOwn victim

def victimMoves {vault : Adr} (victim : Adr) (steps : List (PairStepRecord vault)) :
    List (PairStepRecord vault) :=
  steps.filter (victimMove victim)

theorem mem_of_mem_victimMoves {vault victim : Adr} {r : PairStepRecord vault}
    {steps : List (PairStepRecord vault)} (mem : r ∈ victimMoves victim steps) : r ∈ steps :=
  List.mem_of_mem_filter mem

/-- The schedule once the deposit minting `locked` is open: the next victim move, if any, is the exact full redeem
of `locked` to itself, after which nothing; until then no record takes the victim's row below `locked`. -/
def VictimOpenAdmits {vault : Adr} (victim : Adr) (locked : Nat) :
    List (PairStepRecord vault) → Prop
  | [] => True
  | r :: rest =>
      if victimMove victim r then
        (∃ paid, r.flow = .outbound victim victim locked paid true false) ∧ victimMoves victim rest = []
      else locked ≤ r.victimRowAfter victim ∧ VictimOpenAdmits victim locked rest

/-- **The SF-frozen victim schedule of the pair** (PRORATA's T:141 plus the lock): exactly one exact deposit the victim
pays for itself, then at most one exact full redeem of what it minted, to itself; no other victim cash; and while the
deposit is open, the victim's share row never falls below that deposit's shares.  What non-victims do to the
victim is unrestricted. -/
def VictimSchedule {vault : Adr} (victim : Adr) : List (PairStepRecord vault) → Prop
  | [] => False
  | r :: rest =>
      if victimMove victim r then
        ∃ amount minted, r.flow = .inbound victim victim amount minted true ∧
          VictimOpenAdmits victim minted rest
      else VictimSchedule victim rest

/-- What a reached phase still admits (T:153). -/
def victimAdmits {vault : Adr} {o : Nat} (victim : Adr) :
    Blanc.Prorata.VictimPhase o → List (PairStepRecord vault) → Prop
  | .before, steps => VictimSchedule victim steps
  | .open deposit, steps => VictimOpenAdmits victim deposit.minted steps
  | .exited _ _, steps => victimMoves victim steps = []

/-- One record under the schedule: not a victim move (and then the lock holds after it while a deposit is open), the
victim's deposit, or the victim's exit (T:176/216/254 in one lemma). -/
theorem victimAdmits_cons {vault victim : Adr} {o : Nat} {phase : Blanc.Prorata.VictimPhase o}
    {r : PairStepRecord vault} {rest : List (PairStepRecord vault)}
    (h : victimAdmits victim phase (r :: rest)) :
    (victimMove victim r = false ∧ victimAdmits victim phase rest ∧
        ∀ deposit, phase = .open deposit → deposit.minted ≤ r.victimRowAfter victim) ∨
      (phase = .before ∧ ∃ amount minted,
        r.flow = .inbound victim victim amount minted true ∧ VictimOpenAdmits victim minted rest) ∨
      (∃ deposit paid, phase = .open deposit ∧
        r.flow = .outbound victim victim deposit.minted paid true false ∧
          victimMoves victim rest = []) := by
  cases phase with
  | before =>
      cases hm : victimMove victim r
      · simp only [victimAdmits, VictimSchedule, hm, Bool.false_eq_true, ↓reduceIte] at h
        exact .inl ⟨rfl, h, fun _ hp => by cases hp⟩
      · simp only [victimAdmits, VictimSchedule, hm, ↓reduceIte] at h
        exact .inr (.inl ⟨rfl, h⟩)
  | «open» deposit =>
      cases hm : victimMove victim r
      · simp only [victimAdmits, VictimOpenAdmits, hm, Bool.false_eq_true, ↓reduceIte] at h
        exact .inl ⟨rfl, h.2, fun _ hp => by cases hp; exact h.1⟩
      · simp only [victimAdmits, VictimOpenAdmits, hm, ↓reduceIte] at h
        obtain ⟨⟨paid, hflow⟩, hnone⟩ := h
        exact .inr (.inr ⟨deposit, paid, rfl, hflow, hnone⟩)
  | exited deposit exit =>
      cases hm : victimMove victim r
      · simp only [victimAdmits, victimMoves, List.filter_cons, hm, Bool.false_eq_true,
          ↓reduceIte] at h
        exact .inl ⟨rfl, h, fun _ hp => by cases hp⟩
      · simp [victimAdmits, victimMoves, hm] at h

/-- **Parity with PRORATA's schedule.**  The pair schedule has PRORATA's move-list shape (T:141). -/
theorem VictimOpenAdmits.moves {vault victim : Adr} {locked : Nat} :
    ∀ {steps : List (PairStepRecord vault)}, VictimOpenAdmits victim locked steps →
      victimMoves victim steps = [] ∨
        ∃ exit paid, exit.flow = .outbound victim victim locked paid true false ∧
          victimMoves victim steps = [exit]
  | [], _ => .inl rfl
  | r :: rest, h => by
      cases hm : victimMove victim r
      · simp only [VictimOpenAdmits, hm, Bool.false_eq_true, ↓reduceIte] at h
        simpa only [victimMoves, List.filter_cons, hm, Bool.false_eq_true, ↓reduceIte] using
          VictimOpenAdmits.moves h.2
      · simp only [VictimOpenAdmits, hm, ↓reduceIte] at h
        obtain ⟨⟨paid, hflow⟩, hnone⟩ := h
        refine .inr ⟨r, paid, hflow, ?_⟩
        simp only [victimMoves] at hnone
        simp only [victimMoves, List.filter_cons, hm, ↓reduceIte, hnone]

theorem VictimSchedule.moves {vault victim : Adr} :
    ∀ {steps : List (PairStepRecord vault)}, VictimSchedule victim steps →
      ∃ (deposit : PairStepRecord vault) (amount minted : Nat),
        deposit.flow = .inbound victim victim amount minted true ∧
          (victimMoves victim steps = [deposit] ∨
            ∃ (exit : PairStepRecord vault) (paid : Nat),
              exit.flow = .outbound victim victim minted paid true false ∧
                victimMoves victim steps = [deposit, exit])
  | [], h => h.elim
  | r :: rest, h => by
      cases hm : victimMove victim r
      · simp only [VictimSchedule, hm, Bool.false_eq_true, ↓reduceIte] at h
        simpa only [victimMoves, List.filter_cons, hm, Bool.false_eq_true, ↓reduceIte] using
          VictimSchedule.moves h
      · simp only [VictimSchedule, hm, ↓reduceIte] at h
        obtain ⟨amount, minted, hflow, hopen⟩ := h
        refine ⟨r, amount, minted, hflow, ?_⟩
        rcases VictimOpenAdmits.moves hopen with hnone | ⟨exit, paid, hexit, hone⟩
        · left
          simp only [victimMoves] at hnone
          simp only [victimMoves, List.filter_cons, hm, ↓reduceIte, hnone]
        · right
          refine ⟨exit, paid, hexit, ?_⟩
          simp only [victimMoves] at hone
          simp only [victimMoves, List.filter_cons, hm, ↓reduceIte, hone]

/-! ### 5.6 Two model facts the adapter needs -/

/-- The genesis price anchor holds along every pair path. -/
theorem PairAttackPath.priceLe_genesis {o : Nat} (ho : 2 ≤ o) {state : PairAttackState o}
    (path : PairAttackPath o state) : Blanc.Prorata.PriceLe o ⟨0, 0⟩ state.accounting := by
  induction path with
  | genesis => exact Blanc.Prorata.PriceLe.refl o _
  | snoc step path ih =>
      have hinv := path.invariant ho
      exact Blanc.Prorata.PriceLe.trans (by omega) ih
        (step.effect.priceLe (by omega) hinv.1 hinv.2.2.1)
-- C:914–918 (`invariant`'s induction) with C:546 (`PairAttackEffect.priceLe`); T:639–642's `PriceLe.trans` step.

/-- A victim-row debit that respects the lock is a gift. -/
theorem PairAttackState.le_giftShares_of_lock {o : Nat} {state : PairAttackState o} {shares row : Nat}
    (hrow : row + shares = state.victimShares)
    (hlock : ∀ deposit, state.phase = .open deposit → deposit.minted ≤ row) :
    shares ≤ state.giftShares := by
  unfold PairAttackState.giftShares PairAttackState.lockedShares
  cases hp : state.phase with
  | before => dsimp only; omega
  | «open» deposit =>
      have := hlock deposit hp
      dsimp only
      omega
  | exited deposit exit => dsimp only; omega
-- C:472–481 (`lockedShares_le`'s phase split).


/-! ### 5.7 One realized record is one classified pair step -/

/-- **The adapter step.**  Every record is one `PairAttackEffect`, read off its flow, the schedule, the ledger
identity and the path's own invariant; no premise is added. -/
private theorem pairAttackStep_of_record {vault victim : Adr}
    (charge : PairStepRecord vault → Blanc.Prorata.AttackAttribution)
    {r : PairStepRecord vault} {rest : List (PairStepRecord vault)}
    {state : PairAttackState offsetN}
    (zero : r.step.debitAmount = 0)
    (conserved : LedgerConserved supplySlot (r.before.getStor vault))
    (hacc : state.accounting = r.pre)
    (hvictim : state.victimShares = r.victimRowBefore victim)
    (hinv : state.Invariant)
    (hprice : Blanc.Prorata.PriceLe offsetN ⟨0, 0⟩ state.accounting)
    (hadmits : victimAdmits victim state.phase (r :: rest)) :
    ∃ (kind : PairAttackKind) (next : PairAttackState offsetN),
      PairAttackEffect offsetN state kind next ∧
        next.accounting = r.post ∧
        next.victimShares = r.victimRowAfter victim ∧
        victimAdmits victim next.phase rest ∧
        next.inA = state.inA + (charge r).coalitionAmount (stepCredit victim r) ∧
        next.outA = state.outA + (charge r).coalitionAmount (stepPayout victim r) ∧
        next.outsideSubsidy = state.outsideSubsidy + (charge r).outsideAmount (stepCredit victim r) ∧
        next.sharesIn = state.sharesIn + stepSharesIn victim r ∧
        next.sharesOut = state.sharesOut + stepSharesOut victim r := by
  have accounts := r.accounts zero
  have rows := r.victimRow conserved victim
  have hpart : state.nonVictimShares + r.victimRowBefore victim = r.pre.supply := by
    have h := hinv.1
    unfold Blanc.Prorata.ProrataAttackState.SharesPartition at h
    rw [hacc, hvictim] at h
    exact h
  rcases victimAdmits_cons hadmits with
    ⟨hmove, hrest, hlock⟩ | ⟨hphase, amount, minted, hflow, hopen⟩ |
      ⟨deposit, paid, hphase, hflow, hnone⟩
  · -- Not a victim move: the phase is kept and the lock holds after the record.
    cases hf : r.flow with
    | inbound payer receiver assets shares exact =>
        have hpayer : payer ≠ victim := by
          intro h
          simp [victimMove, hf, PairFlow.victimOwn, h] at hmove
        rw [hf] at accounts rows
        simp [PairFlow.VictimRow] at rows
        obtain ⟨hpost, hminted, -⟩ := accounts
        by_cases hrecv : receiver = victim
        · rw [if_pos hrecv] at rows
          refine ⟨_, _, PairAttackEffect.depositToVictim state (charge r) assets shares
            (by rw [hacc]; exact hminted), ?_, ?_, hrest, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [PairAttackState.inboundCross, hacc, hpost]
          · simp only [PairAttackState.inboundCross, hvictim, rows]
          all_goals simp [PairAttackState.inboundCross, PairAttackState.outflowPrice, stepCredit,
            stepPayout, stepSharesIn, stepSharesOut, hf, hpayer, hrecv, hacc]
        · rw [if_neg hrecv] at rows
          refine ⟨_, _, PairAttackEffect.nonVictimDeposit state (charge r) assets shares
            (by rw [hacc]; exact hminted), ?_, ?_, hrest, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [PairAttackState.inbound, hacc, hpost]
          · simp only [PairAttackState.inbound, hvictim, rows, Nat.add_zero]
          all_goals simp [PairAttackState.inbound, stepCredit, stepPayout, stepSharesIn,
            stepSharesOut, hf, hpayer, hrecv]
    | outbound owner receiver shares assets exact retained =>
        rw [hf] at accounts rows
        simp [PairFlow.VictimRow] at rows
        obtain ⟨-, hpaid, -, hpost⟩ := accounts
        have hgift : owner = victim → shares ≤ state.giftShares := fun howner =>
          state.le_giftShares_of_lock (row := r.victimRowAfter victim)
            (by rw [if_pos howner] at rows; rw [hvictim]; exact rows) hlock
        have hnon : owner ≠ victim → shares ≤ state.nonVictimShares := fun howner => by
          have := r.debited_add_victimRow_le conserved (party := owner) (amount := shares)
            (by rw [hf]; rfl) howner
          omega
        cases retained with
        | true =>
            by_cases howner : owner = victim
            · rw [if_pos howner] at rows
              refine ⟨_, _, PairAttackEffect.delegatedWithdraw state (charge r) shares 0
                (hgift howner) (Nat.zero_le _), ?_, ?_, hrest, ?_, ?_, ?_, ?_, ?_⟩
              · simp [PairAttackState.outboundDelegated, hacc, hpost]
              · simp only [PairAttackState.outboundDelegated, hvictim]; omega
              all_goals simp [PairAttackState.outboundDelegated, PairAttackState.inflowPrice,
                stepCredit, stepPayout, stepSharesIn, stepSharesOut, hf, howner, hacc]
            · rw [if_neg howner] at rows
              refine ⟨_, _, PairAttackEffect.nonVictimWithdraw state (charge r) shares 0
                (hnon howner) (Nat.zero_le _), ?_, ?_, hrest, ?_, ?_, ?_, ?_, ?_⟩
              · simp [PairAttackState.outbound, hacc, hpost]
              · simp only [PairAttackState.outbound, hvictim]; omega
              all_goals simp [PairAttackState.outbound, stepCredit, stepPayout, stepSharesIn,
                stepSharesOut, hf, howner]
        | false =>
            by_cases howner : owner = victim
            · have hrecv : receiver ≠ victim := by
                intro h
                simp [victimMove, hf, PairFlow.victimOwn, howner, h] at hmove
              rw [if_pos howner] at rows
              refine ⟨_, _, PairAttackEffect.delegatedWithdraw state (charge r) shares assets
                (hgift howner) (by rw [hacc]; exact hpaid), ?_, ?_, hrest, ?_, ?_, ?_, ?_, ?_⟩
              · simp [PairAttackState.outboundDelegated, hacc, hpost]
              · simp only [PairAttackState.outboundDelegated, hvictim]; omega
              all_goals simp [PairAttackState.outboundDelegated, PairAttackState.inflowPrice,
                stepCredit, stepPayout, stepSharesIn, stepSharesOut, hf, howner, hrecv, hacc]
            · rw [if_neg howner] at rows
              refine ⟨_, _, PairAttackEffect.nonVictimWithdraw state (charge r) shares assets
                (hnon howner) (by rw [hacc]; exact hpaid), ?_, ?_, hrest, ?_, ?_, ?_, ?_, ?_⟩
              · simp [PairAttackState.outbound, hacc, hpost]
              · simp only [PairAttackState.outbound, hvictim]; omega
              all_goals simp [PairAttackState.outbound, stepCredit, stepPayout, stepSharesIn,
                stepSharesOut, hf, howner]
    | credit source amount =>
        rw [hf] at accounts rows
        simp [PairFlow.VictimRow] at rows
        refine ⟨_, _, PairAttackEffect.externalCredit state (charge r) amount,
          ?_, ?_, hrest, ?_, ?_, ?_, ?_, ?_⟩
        · simpa only [PairAttackState.credited, hacc] using accounts.symm
        · simp only [PairAttackState.credited, hvictim, rows]
        all_goals simp [PairAttackState.credited, stepCredit, stepPayout, stepSharesIn,
          stepSharesOut, hf]
    | shareMove source receiver amount =>
        rw [hf] at accounts rows
        simp [PairFlow.VictimRow] at rows
        by_cases hs : source = victim <;> by_cases hr : receiver = victim
        · -- victim to itself
          rw [if_pos hs, if_pos hr] at rows
          refine ⟨_, _, PairAttackEffect.shareMoveWithin state false amount,
            by rw [hacc, accounts], by rw [hvictim]; omega, hrest, ?_, ?_, ?_, ?_, ?_⟩
          all_goals simp [stepCredit, stepPayout, stepSharesIn, stepSharesOut, hf, hs, hr]
        · -- victim gift: priced in at the ceiling
          rw [if_pos hs, if_neg hr] at rows
          refine ⟨_, _, PairAttackEffect.shareMoveFromVictim state amount
            (state.le_giftShares_of_lock (by rw [hvictim]; exact rows) hlock),
            ?_, ?_, hrest, ?_, ?_, ?_, ?_, ?_⟩
          · simpa only [PairAttackState.sharesFromVictim, hacc] using accounts.symm
          · simp only [PairAttackState.sharesFromVictim, hvictim]; omega
          all_goals simp [PairAttackState.sharesFromVictim, PairAttackState.inflowPrice, stepCredit,
            stepPayout, stepSharesIn, stepSharesOut, hf, hs, hr, hacc]
        · -- non-victim gift to the victim: priced out at the floor
          rw [if_neg hs, if_pos hr] at rows
          refine ⟨_, _, PairAttackEffect.shareMoveToVictim state amount (by
              have := r.debited_add_victimRow_le conserved (party := source) (amount := amount)
                (by rw [hf]; rfl) hs
              omega),
            ?_, ?_, hrest, ?_, ?_, ?_, ?_, ?_⟩
          · simpa only [PairAttackState.sharesToVictim, hacc] using accounts.symm
          · simp only [PairAttackState.sharesToVictim, hvictim]; omega
          all_goals simp [PairAttackState.sharesToVictim, PairAttackState.outflowPrice, stepCredit,
            stepPayout, stepSharesIn, stepSharesOut, hf, hs, hr, hacc]
        · -- within the non-victim side
          rw [if_neg hs, if_neg hr] at rows
          refine ⟨_, _, PairAttackEffect.shareMoveWithin state true amount,
            by rw [hacc, accounts], by rw [hvictim]; omega, hrest, ?_, ?_, ?_, ?_, ?_⟩
          all_goals simp [stepCredit, stepPayout, stepSharesIn, stepSharesOut, hf, hs, hr]
    | silent =>
        rw [hf] at accounts rows
        simp [PairFlow.VictimRow] at rows
        refine ⟨_, _, PairAttackEffect.silent state, by rw [hacc, accounts], by rw [hvictim, rows],
          hrest, ?_, ?_, ?_, ?_, ?_⟩
        all_goals simp [stepCredit, stepPayout, stepSharesIn, stepSharesOut, hf]
  · -- The victim's deposit.
    rw [hflow] at accounts rows
    simp [PairFlow.VictimRow] at rows
    obtain ⟨hpost, -, hexact⟩ := accounts
    let deposit : Blanc.Prorata.VictimDeposit offsetN :=
      { pre := state.accounting, amount := amount, minted := minted
        minted_eq := by rw [hacc]; exact hexact rfl
        backed := Blanc.Prorata.backed_of_priceLe_genesis hprice }
    refine ⟨_, _, PairAttackEffect.victimDeposit state deposit hphase rfl,
      ?_, ?_, hopen, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [PairAttackState.victimDeposited, Blanc.Prorata.VictimDeposit.post, deposit, hacc, hpost]
    · simp only [PairAttackState.victimDeposited, deposit, hvictim, rows]
    all_goals simp [PairAttackState.victimDeposited, stepCredit, stepPayout, stepSharesIn,
      stepSharesOut, hflow]
  · -- The victim's exit.
    rw [hflow] at accounts rows
    simp [PairFlow.VictimRow] at rows
    obtain ⟨-, -, hexact, hpost⟩ := accounts
    let exit : Blanc.Prorata.VictimExit offsetN deposit :=
      { pre := state.accounting, payout := paid, payout_eq := by rw [hacc]; exact hexact rfl }
    refine ⟨_, _, PairAttackEffect.victimExit state deposit exit hphase rfl,
      ?_, ?_, hnone, ?_, ?_, ?_, ?_, ?_⟩
    · simp [PairAttackState.victimExited, exit, hacc, hpost]
    · simp only [PairAttackState.victimExited, hvictim]; omega
    all_goals simp [PairAttackState.victimExited, stepCredit, stepPayout, stepSharesIn,
      stepSharesOut, hflow]
-- T:440–598 (`attackStep_of_realized`): the same ∃-kind/post shape, the same `refine ⟨_, _, ctor, …⟩` per class and
-- `simp [stepCredit, …]` increment arms.  PRORATA's actor split (T:467) becomes the schedule's three-way split, and
-- its `LedgerMove` rows become the flow's `VictimRow`; the gift and share-sufficiency side conditions are U8 §4's.

/-! ### 5.8 The fold and the genesis adapter -/

private theorem exists_pairAttackPath_of_replay {vault victim : Adr}
    (charge : PairStepRecord vault → Blanc.Prorata.AttackAttribution)
    {first last : PairBoundary} {steps : List (PairStepRecord vault)}
    (replay : PairReplay vault first steps last) :
    (∀ r ∈ steps, r.step.debitAmount = 0) →
    ∀ state : PairAttackState offsetN,
      PairAttackPath offsetN state →
      state.accounting = first.snapshot vault →
      state.victimShares = (Stor.rest first.vault victim).toNat →
      LedgerConserved supplySlot first.vault →
      victimAdmits victim state.phase steps →
      ∃ final : PairAttackState offsetN,
        PairAttackPath offsetN final ∧
          final.inA = state.inA + inA victim charge steps ∧
          final.outA = state.outA + outA victim charge steps ∧
          final.outsideSubsidy = state.outsideSubsidy + outsideSubsidy victim charge steps ∧
          final.sharesIn = state.sharesIn + sharesIn victim steps ∧
          final.sharesOut = state.sharesOut + sharesOut victim steps := by
  induction replay with
  | nil boundary =>
      intro _ state path _ _ _ _
      exact ⟨state, path, by simp [inA], by simp [outA], by simp [outsideSubsidy],
        by simp [sharesIn], by simp [sharesOut]⟩
  | @cons pre mid last record tl preEq postEq tail ih =>
      intro zero state path hacc hvictim hconserved hadmits
      subst preEq
      subst postEq
      obtain ⟨kind, next, effect, hacc', hvictim', hadmits', hin, hout, hsub, hsin, hsout⟩ :=
        pairAttackStep_of_record charge (zero record (by simp)) hconserved hacc hvictim
          (path.invariant two_le_offsetN) (path.priceLe_genesis two_le_offsetN) hadmits
      have path' : PairAttackPath offsetN next :=
        .snoc ⟨state, next, kind, record.provenance, effect⟩ path
      obtain ⟨final, hfinal, h1, h2, h3, h4, h5⟩ :=
        ih (fun r member => zero r (by simp [member])) next path' hacc' hvictim'
          (record.step.conserved hconserved) hadmits'
      refine ⟨final, hfinal, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h1, hin]; simp [inA]; omega
      · rw [h2, hout]; simp [outA]; omega
      · rw [h3, hsub]; simp [outsideSubsidy]; omega
      · rw [h4, hsin]; simp [sharesIn]; omega
      · rw [h5, hsout]; simp [sharesOut]; omega
-- T:606–648 (`exists_attackPath_of_replay`): same ∀-state motive and increment arms.  PRORATA's ledger identity
-- and genesis price are replaced by U5's `PairStep.conserved` (U5:88) and `PairAttackPath.priceLe_genesis` (§5.6).


/-! ### 5.10 The replay split: price order between two records (U7 D-6) -/

/-- Every record of a zero-debit replay starts at or above the replay's first price. -/
theorem PairReplay.priceLe_of_mem {vault : Adr} {first last : PairBoundary}
    {steps : List (PairStepRecord vault)} (replay : PairReplay vault first steps last) :
    (∀ r ∈ steps, r.step.debitAmount = 0) → ∀ {r : PairStepRecord vault}, r ∈ steps →
      Blanc.Prorata.PriceLe offsetN (first.snapshot vault) r.pre := by
  induction replay with
  | nil boundary => intro _ r mem; cases mem
  | @cons pre mid last hd tl preEq postEq tail ih =>
      intro zero r mem
      subst preEq
      subst postEq
      have hstep : Blanc.Prorata.PriceLe offsetN hd.pre hd.post :=
        hd.step.priceLe_of_debitAmount_eq_zero (zero hd (by simp))
      rcases List.mem_cons.mp mem with rfl | hmem
      · exact Blanc.Prorata.PriceLe.refl offsetN _
      · exact Blanc.Prorata.PriceLe.trans offsetN_ne_zero hstep
          (ih (fun r member => zero r (by simp [member])) hmem)
-- T:48–63 over `PairReplay`; the step price is U6 §5 (`PairStep.priceLe_of_debitAmount_eq_zero`).

/-- **The replay split.**  Between the two members of a two-element filtered subsequence of a zero-debit replay the
price never falls: the earlier record's post-boundary is a boundary of the replay, so no list surgery is needed. -/
theorem PairReplay.priceLe_of_filter_pair {vault : Adr} {first last : PairBoundary}
    {steps : List (PairStepRecord vault)} (replay : PairReplay vault first steps last) :
    (∀ r ∈ steps, r.step.debitAmount = 0) → ∀ {p : PairStepRecord vault → Bool}
      {d w : PairStepRecord vault}, steps.filter p = [d, w] →
        Blanc.Prorata.PriceLe offsetN d.post w.pre := by
  induction replay with
  | nil boundary => intro _ _ _ _ h; simp at h
  | @cons pre mid last hd tl preEq postEq tail ih =>
      intro zero p d w h
      by_cases hp : p hd = true
      · rw [List.filter_cons_of_pos hp] at h
        simp only [List.cons.injEq] at h
        obtain ⟨rfl, htl⟩ := h
        have hw : w ∈ tl :=
          List.mem_of_mem_filter (p := p) (by rw [htl]; exact List.mem_singleton_self w)
        subst postEq
        exact tail.priceLe_of_mem (fun r member => zero r (by simp [member])) hw
      · rw [List.filter_cons_of_neg (by simpa using hp)] at h
        exact ih (fun r member => zero r (by simp [member])) h
-- T:68–86 verbatim over `PairReplay`.

/-! ### 5.9 The trace, the adapter headline, and P4 -/

/-- **The pair's open attack trace** (SF §9, T:368 shape).  The realized pair history from the pair root, the D9
premise that the SF names as the only limit, the designated victim outside a finite coalition, and the victim
schedule.  No callee-honesty, cooperation or no-donation premise. -/
structure PairOpenAttackTrace {cfg : ChainConfig} {deployed : BlockChain} {vault : Adr}
    (root : PairRoot cfg deployed vault) (coalition : Finset Adr) (victim : Adr)
    (charge : PairStepRecord vault → Blanc.Prorata.AttackAttribution)
    (steps : List (PairStepRecord vault)) (future : BlockChain) : Prop where
  realizes : PairTraceRealizes root steps future
  collision : NoVaultAllowanceKeyCollision (PairStepRecord.ledger steps) vault
  victim_not_mem : victim ∉ coalition
  coalition_covers : ∀ r ∈ steps, ∀ x : Adr,
    r.provenance.actor = some x → x ≠ victim → x ∈ coalition
  schedule : VictimSchedule victim steps

/-- The closed trace: every non-victim flow is the coalition's (T:383). -/
abbrev PairAttackTrace {cfg : ChainConfig} {deployed : BlockChain} {vault : Adr}
    (root : PairRoot cfg deployed vault) (coalition : Finset Adr) (victim : Adr)
    (steps : List (PairStepRecord vault)) (future : BlockChain) : Prop :=
  PairOpenAttackTrace root coalition victim coalitionCharge steps future

/-- **The adapter** (design `exists_pairAttackPath`): every pair attack trace is a pair actor path from genesis whose
coalition accounting, both priced share crossings included, is exactly the trace's own. -/
theorem exists_pairAttackPath {cfg : ChainConfig} {deployed future : BlockChain} {vault : Adr}
    {root : PairRoot cfg deployed vault} {coalition : Finset Adr} {victim : Adr}
    {charge : PairStepRecord vault → Blanc.Prorata.AttackAttribution}
    {steps : List (PairStepRecord vault)}
    (trace : PairOpenAttackTrace root coalition victim charge steps future) :
    ∃ final : PairAttackState offsetN,
      PairAttackPath offsetN final ∧
        final.inA = inA victim charge steps ∧
        final.outA = outA victim charge steps ∧
        final.outsideSubsidy = outsideSubsidy victim charge steps ∧
        final.sharesIn = sharesIn victim steps ∧
        final.sharesOut = sharesOut victim steps := by
  have hsnapshot : (PairBoundary.ofState vault deployed.state).snapshot vault = ⟨0, 0⟩ := by
    rw [PairBoundary.snapshot_ofState, root.genesisSnapshot]
  have hrow : (0 : Nat) =
      (Stor.rest (PairBoundary.ofState vault deployed.state).vault victim).toNat := by
    show (0 : Nat) = (Stor.rest (deployed.state.getStor vault) victim).toNat
    rw [root.vaultEmpty, show Stor.rest Stor.empty victim = (0 : B256) from rfl, B256.toNat_zero]
  have hconserved : LedgerConserved supplySlot (PairBoundary.ofState vault deployed.state).vault := by
    show LedgerConserved supplySlot (deployed.state.getStor vault)
    rw [root.vaultEmpty]
    exact LedgerConserved.of_empty
  obtain ⟨final, hfinal, h1, h2, h3, h4, h5⟩ :=
    exists_pairAttackPath_of_replay charge trace.realizes.toReplay
      (trace.realizes.debitAmount_eq_zero trace.collision)
      (PairAttackState.genesis offsetN) .genesis hsnapshot.symm hrow hconserved trace.schedule
  exact ⟨final, hfinal,
    by simpa [PairAttackState.genesis, Blanc.Prorata.ProrataAttackState.genesis] using h1,
    by simpa [PairAttackState.genesis, Blanc.Prorata.ProrataAttackState.genesis] using h2,
    by simpa [PairAttackState.genesis, Blanc.Prorata.ProrataAttackState.genesis] using h3,
    by simpa [PairAttackState.genesis] using h4,
    by simpa [PairAttackState.genesis] using h5⟩
-- T:657–687 (`exists_attackPath`): same three genesis facts, read off `PairRoot.vaultEmpty` and U6's
-- `genesisSnapshot`; the D9 zero-debit list is U6's `debitAmount_eq_zero`.

/-- **`pair_attacker_open_context`** (SF §9, P4).  The coalition's settled take plus the floor value of the shares it
sent the victim is bounded by its own settled input, the outside subsidy it was handed, and the ceiling value of the
shares it took from the victim.  `2 ≤ O` is discharged by the vault's offset. -/
theorem pair_attacker_open_context {cfg : ChainConfig} {deployed future : BlockChain} {vault : Adr}
    {root : PairRoot cfg deployed vault} {coalition : Finset Adr} {victim : Adr}
    {charge : PairStepRecord vault → Blanc.Prorata.AttackAttribution}
    {steps : List (PairStepRecord vault)}
    (trace : PairOpenAttackTrace root coalition victim charge steps future) :
    outA victim charge steps + sharesOut victim steps ≤
      inA victim charge steps + outsideSubsidy victim charge steps + sharesIn victim steps := by
  obtain ⟨final, path, h1, h2, h3, h4, h5⟩ := exists_pairAttackPath trace
  have h := path.attacker_open_context_of_pairAttackPath two_le_offsetN
  omega

/-- **`pair_attacker_no_profit`** (SF §9, P4).  No closed pair attack trace in which the victim gives the coalition
no shares is profitable.  The share gift is named, not assumed absent. -/
theorem pair_attacker_no_profit {cfg : ChainConfig} {deployed future : BlockChain} {vault : Adr}
    {root : PairRoot cfg deployed vault} {coalition : Finset Adr} {victim : Adr}
    {steps : List (PairStepRecord vault)}
    (trace : PairAttackTrace root coalition victim steps future)
    (noShareGifts : sharesIn victim steps = 0) :
    outA victim coalitionCharge steps + sharesOut victim steps ≤ inA victim coalitionCharge steps := by
  have h := pair_attacker_open_context trace
  rw [outsideSubsidy_coalitionCharge, noShareGifts] at h
  omega

/-- **`pair_victim_loss_bound`** (SF §9, P4).  If the victim's deposit saw pre-credit `(Sdep, Bdep)`, paid `v` and
minted `m`, and its later exit burns that `m` and pays `p`, the shortfall is at most one virtual-asset quantum above
the genesis-anchored price ratio, whatever non-victims did to the victim in between. -/
theorem pair_victim_loss_bound {cfg : ChainConfig} {deployed future : BlockChain} {vault : Adr}
    {root : PairRoot cfg deployed vault} {coalition : Finset Adr} {victim : Adr}
    {charge : PairStepRecord vault → Blanc.Prorata.AttackAttribution}
    {steps : List (PairStepRecord vault)}
    (trace : PairOpenAttackTrace root coalition victim charge steps future)
    {deposit exit : PairStepRecord vault} {v m p : Nat}
    (hmoves : victimMoves victim steps = [deposit, exit])
    (hdeposit : deposit.flow = .inbound victim victim v m true)
    (hexit : exit.flow = .outbound victim victim m p true false) :
    v - p ≤ Nat.div (deposit.pre.balance + 1) (deposit.pre.supply + offsetN) + 1 := by
  have replay := trace.realizes.toReplay
  have zero := trace.realizes.debitAmount_eq_zero trace.collision
  have hd := deposit.accounts (zero deposit (mem_of_mem_victimMoves (by rw [hmoves]; simp)))
  rw [hdeposit] at hd
  obtain ⟨hpost, -, hquote⟩ := hd
  have hw := exit.accounts (zero exit (mem_of_mem_victimMoves (by rw [hmoves]; simp)))
  rw [hexit] at hw
  obtain ⟨-, -, hpaid, -⟩ := hw
  have hprice : Blanc.Prorata.PriceLe offsetN deposit.post exit.pre :=
    replay.priceLe_of_filter_pair zero hmoves
  rw [hpost] at hprice
  exact Blanc.Prorata.victim_loss_le_div_add_one offsetN_ne_zero (hquote rfl) hprice (hpaid rfl)
-- T:736–757 (`victim_loss_bound`) line for line: `deposit_inv`/`withdraw_inv` → `accounts` at the two flows.


end Blanc.Composition.ProrataWethVault
