import Blanc.Lift.UniswapV2Pair.ModelControls
import Blanc.Lift.UniswapV2Pair.Creation.DeployInit

/-! U2 refinement control, burn-rounding route (typed model).

The goal's U2 control: the model whose `burn` floor rounds toward the user
(`ModelMutants.burnRoundUp`) disagrees with production (`runTyped`). `burn_witness_disagrees`
reaches a witness state by accepted typed steps and shows both accept the same burn transcript
there, production returning `(1, 1)` and the mutant `(2, 2)`.

The witness state is new here, not `ModelControls.burnReady`: that state uses factory `16`
(`0x10`) and pair `17` (`0x11`), enabled precompile addresses on Prague and later forks, so no
actual EVM burn could observe a code-bearing factory there. This witness uses addresses off the
precompile range and a realistic timestamp, and starts from `initializedState`, the state that
`Creation.pair_create2_initialized` reaches by actual CREATE2 deployment plus `initialize`
(here with domain separator `0`; deployment yields the EIP-712 hash, which the burn never reads,
but that independence is not proved here). The later mint, donation sync and LP transfer are
typed-model steps.

A frame-level form of this control was removed: it was conditional on a hypothesis that every
authenticated reading of one concrete raw burn run is this witness's transcript, and the burn
authentication names an answer by call target and input, not by call position, so no run pins
"every authenticated reading" (the initial balance answer may equally be read from the final
balance call); the hypothesis was refutable.

Evidence altitude: typed model (closed). -/

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

end Blanc.Lift.UniswapV2Pair.RefinementControls
