import Blanc.Lift.UniswapV2Pair.ModelControls
import Blanc.Lift.UniswapV2Pair.Creation.DeployInit
import Blanc.Lift.UniswapV2Pair.PairHistory

/-! U2 refinement control, burn-rounding route.

The goal's U2 control: the refinement fails against a model whose `burn` floor rounds toward
the user. `BurnReturnRefines A` is the returndata part of the burn frame refinement at the
arithmetic `A` (production `runTyped` at `ModelMutants.production`, the round-up mutant at
`ModelMutants.burnRoundUp`). The production statement holds:
`burnFrameRefinement_holds` proves `BurnFrameRefinement` at the universe representation
`UniverseRep U`, the trace-local admission `PairGood U` and the burn authentication `BurnAuth`
from the raw Burn consumer `burnRaw_source_authentic`. `burn_refinement_control` shows the mutant
statement is false, conditional on one named hypothesis, `BurnWitnessExists` (one successful raw
burn run at a concrete reached state, with a concrete callee environment), which this tree states
but does not discharge.

The witness state is new here, not `ModelControls.burnReady`: that state uses factory `16`
(`0x10`) and pair `17` (`0x11`), enabled precompile addresses on Prague and later forks, so no
actual EVM burn could observe a code-bearing factory there. This witness uses addresses off the
precompile range and a realistic timestamp, and starts from `initializedState`, the state that
`Creation.pair_create2_initialized` reaches by actual CREATE2 deployment plus `initialize`
(here with domain separator `0`; deployment yields the EIP-712 hash, which the burn never reads,
but that independence is not proved here). The later mint, donation sync and LP transfer are
typed-model steps.

Evidence altitude: production refinement EVM-level (closed); control EVM-conditional on
`BurnWitnessExists`. -/

namespace Blanc.Lift.UniswapV2Pair.RefinementControls

open Jaune
open Blanc.Lift.UniswapV2Pair.ModelMutants
open Blanc.Lift.UniswapV2Pair.ModelControls (mintTranscript donationTranscript burnTranscript)

/-- The witness factory, off the precompile address range. -/
def factory : Adr := 0x1000
/-- The witness pair address. -/
def pair : Adr := 0x2000
/-- The witness LP holder: first minter, LP returner and burn recipient. -/
def holder : Adr := 0x4000

/-- Every witness invocation: a non-static call from `holder` at one block timestamp. -/
def context : Context :=
  { pair := pair, sender := holder, value := 0, timestamp := 1700000000,
    isStatic := false, invocation := [] }

/-- The deployed and initialized pair over tokens `0x3000`, `0x3001`. -/
def initialized : State := initializedState factory 0 0x3000 0x3001

/-- After a first mint to `holder` at balances 1001/1001. -/
def minted : State :=
  (runTyped initialized context (.mint holder) mintTranscript).frame.current.state

/-- After a donation sync at balances 1002/1002. -/
def synced : State := (runTyped minted context .sync donationTranscript).frame.current.state

/-- After `holder` returns its one LP token to the pair, as a burn caller does. -/
def burnReady : State := (runTyped synced context (.transfer pair 1) .done).frame.current.state

/-- The witness is reached by accepted steps (first mint of one LP token, donation sync, LP
transfer to the pair), and at it production and the round-up mutant both accept the same
burn transcript, production returning `(1, 1)` and the mutant `(2, 2)`. Typed model. -/
theorem burn_witness_disagrees :
    (runTyped initialized context (.mint holder) mintTranscript).status =
      .success (encodeWords [1]) ∧
    (runTyped minted context .sync donationTranscript).status = .success [] ∧
    (runTyped synced context (.transfer pair 1) .done).status = .success (encodeWords [1]) ∧
    (runTyped burnReady context (.burn holder) burnTranscript).status =
      .success (encodeWords [1, 1]) ∧
    (runTypedWith burnRoundUp burnReady context (.burn holder) burnTranscript).status =
      .success (encodeWords [2, 2]) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

/-- The returndata part of the burn frame refinement at arithmetic `A`: every successful
pc-zero run of the certified runtime on the `burn` selector, from storage that `Rep`
relates to `current` and admitted by the trace-local `Good`, has an `Auth`-authenticated
source entry and observed transcript on which `runTypedWith A` succeeds with exactly the
run's output bytes. -/
def BurnReturnRefines (A : Arithmetic) (Rep : Stor → State → Prop) (Good : Exec.Deriv → Prop)
    (Auth : Exec.Deriv → Entry → Transcript → Prop) : Prop :=
  ∀ (current : State) (invocation : List Nat) {sevm : Sevm} {b post : Devm} {G : Nat}
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)),
    sevm.code = code → b.getCode sevm.currentTarget = code → CoveredFork sevm.benvStat.fork →
    Blanc.Sevm.selector sevm = 0x89afcb44 → b.output = [] → sevm.data.length < 2 ^ 256 →
    Good ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ →
    Rep (b.getStor sevm.currentTarget) current →
    ∃ (entry : Entry) (nested : Transcript),
      Auth ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ entry nested ∧
      (runTypedWith A current (writerContext sevm invocation) entry nested).status =
        .success post.output

/-- The production burn frame refinement (returndata consequence): every successful raw burn run
`ExactConsumes` the decoded `.burn` entry on its authenticated observed transcript with
`post.output` equal to the finished bytes. Proved by `burnFrameRefinement_holds`. -/
def BurnFrameRefinement (Rep : Stor → State → Prop) (Good : Exec.Deriv → Prop)
    (Auth : Exec.Deriv → Entry → Transcript → Prop) : Prop :=
  BurnReturnRefines production Rep Good Auth

/-- Named hypothesis, stated but not discharged in this tree (burn liveness at a concrete state):
a concrete successful raw burn run of the certified
runtime, on a covered fork, at pair `pair` called by `holder` at timestamp `1700000000`, from
storage that `Rep` relates to `burnReady`, admitted by `Good`, whose
every `Auth`-authenticated reading is the entry `.burn holder` with observed transcript
`ModelControls.burnTranscript` (token balances 1002/1002, zero `feeTo`, both payout transfers
accepted with empty returndata, final balances 1001/1001). -/
def BurnWitnessExists (Rep : Stor → State → Prop) (Good : Exec.Deriv → Prop)
    (Auth : Exec.Deriv → Entry → Transcript → Prop) : Prop :=
  ∃ (invocation : List Nat) (sevm : Sevm) (b post : Devm) (G : Nat)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)),
    sevm.code = code ∧ b.getCode sevm.currentTarget = code ∧ CoveredFork sevm.benvStat.fork ∧
    Blanc.Sevm.selector sevm = 0x89afcb44 ∧ b.output = [] ∧ sevm.data.length < 2 ^ 256 ∧
    Good ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ ∧
    Rep (b.getStor sevm.currentTarget) burnReady ∧
    writerContext sevm invocation = context ∧
    ∀ entry nested, Auth ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ entry nested →
      entry = .burn holder ∧ nested = burnTranscript

/-- Storage that is a finite representation over rows of the universe `U`. -/
def UniverseRep (U : WriterKey → Prop) (stor : Stor) (st : State) : Prop :=
  ∃ K : WriterKey → Prop, (∀ k, K k → U k) ∧ WriterRep K stor st

/-- **The production burn frame refinement holds** over a separated universe `U`, with the
trace-local admission `PairGood U` and the burn authentication `BurnAuth`: from the raw Burn
consumer `burnRaw_source_authentic`, `runTyped_of_exact` and `runTypedWith_production`. -/
theorem burnFrameRefinement_holds {U : WriterKey → Prop} (inj : WriterInj U)
    (apart : WriterApart U) : BurnFrameRefinement (UniverseRep U) (PairGood U) BurnAuth := by
  intro current invocation sevm b post G run codeEq installedCode fork selector _ _ good rep
  obtain ⟨K, sub, wrep⟩ := rep
  have row : ∀ k ∈ [WriterKey.balance sevm.currentTarget], U k := by
    intro k member
    rw [List.mem_singleton] at member
    rw [member]
    exact good.pairRow
  have fresh := Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub row
  have sub₁ := writerExtend_universe sub row
  have installed : some (b.getCode sevm.currentTarget).toList = pairSem.image := by
    rw [installedCode]
    exact pairSem_image.symm
  obtain ⟨a, amount0, amount1, provenance, K', final, rets, _, _, _, _, _, consumed, halted,
      output, _⟩ :=
    burnRaw_source_authentic (current := { state := current, logs := [], updates := [] })
      invocation codeEq fork selector (wrep.extend fresh)
      (Or.inr (List.mem_singleton_self _)) run inj apart sub₁ good.mint pairSem pairSem_image
      installed good.locked good.views
  cases halted
  refine ⟨_, a.transcript, ⟨selector, rfl, burnRaw_frameAuth provenance⟩, ?_⟩
  rw [runTypedWith_production, (runTyped_of_exact consumed).1, output]

/-- **U2 refinement control (burn rounding toward the user).** The production burn frame
refinement holds (`burnFrameRefinement_holds`); given one successful raw burn run at the reached
witness, the burn frame refinement against the round-up mutant `burnRoundUp` is false: the
witness run's output is production's `(1, 1)`, not the mutant's `(2, 2)`.
Conditional on the named hypothesis `BurnWitnessExists`. -/
theorem burn_refinement_control {U : WriterKey → Prop} (inj : WriterInj U)
    (apart : WriterApart U) (live : BurnWitnessExists (UniverseRep U) (PairGood U) BurnAuth) :
    ¬ BurnReturnRefines burnRoundUp (UniverseRep U) (PairGood U) BurnAuth := by
  have refines := burnFrameRefinement_holds inj apart
  intro mutant
  obtain ⟨invocation, sevm, b, post, G, run, codeEq, installed, fork, selector, fresh,
    representable, good, rep, ctx, unique⟩ := live
  obtain ⟨entry, nested, auth, prod⟩ :=
    refines _ invocation run codeEq installed fork selector fresh representable good rep
  obtain ⟨entry', nested', auth', mutRun⟩ :=
    mutant _ invocation run codeEq installed fork selector fresh representable good rep
  obtain ⟨rfl, rfl⟩ := unique _ _ auth
  obtain ⟨rfl, rfl⟩ := unique _ _ auth'
  rw [ctx, runTypedWith_production, burn_witness_disagrees.2.2.2.1] at prod
  rw [ctx, burn_witness_disagrees.2.2.2.2] at mutRun
  exact absurd ((RunStatus.success.inj prod).trans (RunStatus.success.inj mutRun).symm)
    (by decide)

end Blanc.Lift.UniswapV2Pair.RefinementControls
