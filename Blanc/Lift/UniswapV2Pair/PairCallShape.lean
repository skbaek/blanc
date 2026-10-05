import Blanc.Lift.CallerProvenance
import Blanc.Lift.UniswapV2Pair.PairSelectors

/-!
# What the Pair runtime calls: the per-entry call shape

The Pair issues non-static CALLs only from `_safeTransfer` (selector `transfer`, `0xa9059cbb`; reached
from `skim`, `swap` and `burn`) and from `swap`'s flash callback (selector `uniswapV2Call`,
`0x10d1e85c`).  Every other child it spawns is a STATICCALL (`balanceOf`, `feeTo`, ECRECOVER), hence
static.  `CallsTransferOrCallback run` states this for the direct committed children of one run.

The per-entry facts are named hypotheses, keyed on the actual selector (`EntryCallShape`), so that each
is discharged by its own entry walk; `pair_callsTransferOrCallback` assembles them over the dispatcher's
selector partition (`pair_bytecode_selector_inv`).
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- Every non-static direct committed child of the run carries the `transfer` or the `uniswapV2Call`
selector. -/
def CallsTransferOrCallback {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : Prop :=
  ∀ c ∈ Exec.childFrames run, c.sevm.isStatic = false →
    Blanc.Sevm.selector c.sevm = 0xa9059cbb ∨ Blanc.Sevm.selector c.sevm = 0x10d1e85c

/-- The call shape of every successful Pair frame whose actual selector satisfies `sel`. -/
def EntryCallShape (sel : B256 → Prop) : Prop :=
  ∀ {sevm : Sevm} {b post : Devm} {G : Nat} (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)),
    sevm.code = code → CoveredFork sevm.benvStat.fork → sel (Blanc.Sevm.selector sevm) →
    CallsTransferOrCallback run

/-- The published selectors other than `skim`, `swap` and `burn`: the views, `sync`, `mint`, `permit`,
`transfer`, `approve`, `transferFrom` and `initialize`. -/
def QuietSelector (s : B256) : Prop :=
  s ∈ pairSelectors ∧ s ≠ 0xbc25cf77 ∧ s ≠ 0x022c0d9f ∧ s ≠ 0x89afcb44

/-- LANE-OPEN OBLIGATION (second host): discharged by this lane's entry walks,
one per quiet entry: every successful frame of a view, `sync`, `mint`, `permit`, `transfer`, `approve`,
`transferFrom` or `initialize` has no non-static committed child (each issues only STATICCALLs or no
call), which implies this shape.  Statement shape of the expected discharge, per entry `e`:
`∀ run, sevm.code = code → CoveredFork … → selector sevm = e → ∀ c ∈ Exec.childFrames run,
c.sevm.isStatic = true`.  Not derived here: the existing walks (`StaticViewTurns`, `SyncCanonical`,
`MintCanonical`, `PermitTurns`, the writer entries) expose the STATICCALL steps they take but do not
state that these are all of the frame's children. -/
def QuietEntriesCallShape : Prop := EntryCallShape QuietSelector

/-- LANE-OPEN OBLIGATION (second host): discharged by this lane's exhaustive
form of the skim walk (`skim_bytecode_exact_consumes`, SkimCanonical.lean): the only non-static
children of a successful `skim` frame are its two `_safeTransfer` CALLs, whose calldata starts with
`transfer`'s selector.  The current walk exposes both CALL steps (`SkimFirstSteps`/`SkimSecondSteps`)
but not that they are all of the frame's children. -/
def SkimCallShape : Prop := EntryCallShape (· = 0xbc25cf77)

/-- LANE-OPEN OBLIGATION (second host): discharged by this lane's exhaustive
form of the swap walk (`swap_bytecode_exact_consumes`, SwapCanonical.lean): the only non-static
children of a successful `swap` frame are its optimistic `transfer` CALLs (`SwapTransferOpt`) and the
`uniswapV2Call` callback (`SwapCallbackOpt`).  The current walk exposes these steps but not that they
are all of the frame's children. -/
def SwapCallShape : Prop := EntryCallShape (· = 0x022c0d9f)

/-- CROSS-HOST HYPOTHESIS (delete at consolidation): discharged by the original host's burn walk
(`Burn*`, its actual two-transfer execution, handoff "Original-host deliverables" 1): the only
non-static children of a successful `burn` frame are its two `_safeTransfer` CALLs, whose calldata
starts with `transfer`'s selector.  Expected statement: exactly this `EntryCallShape (· = 0x89afcb44)`,
or the stronger "children = the two transfer CALL frames plus static `balanceOf`/`feeTo` queries". -/
def BurnCallShape : Prop := EntryCallShape (· = 0x89afcb44)

/-- **Pair call shape.**  Every successful frame of the Pair code calls non-statically only with the
`transfer` or the `uniswapV2Call` selector, by the dispatcher's selector partition.
CROSS-HOST: conditional on BurnCallShape.
LANE-OPEN: conditional on QuietEntriesCallShape, SkimCallShape, SwapCallShape. -/
theorem pair_callsTransferOrCallback (quiet : QuietEntriesCallShape) (skim : SkimCallShape)
    (swap : SwapCallShape) (burn : BurnCallShape)
    {sevm : Sevm} {b post : Devm} {G : Nat} (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork) :
    CallsTransferOrCallback run := by
  by_cases hSkim : Blanc.Sevm.selector sevm = 0xbc25cf77
  · exact skim run codeEq fork hSkim
  by_cases hSwap : Blanc.Sevm.selector sevm = 0x022c0d9f
  · exact swap run codeEq fork hSwap
  by_cases hBurn : Blanc.Sevm.selector sevm = 0x89afcb44
  · exact burn run codeEq fork hBurn
  exact quiet run codeEq fork ⟨pair_bytecode_selector_inv codeEq fork run, hSkim, hSwap, hBurn⟩

end Blanc.Lift.UniswapV2Pair
