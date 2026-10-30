import Blanc.Lift.WitnessArms

/-!
# Root-message scenarios: a fold of settled messages

A scenario of root messages, each built from the fork and the previous settled world, run in
sequence. `RootMsg.settle` runs one message (`processCreateMessage` for a creation,
`processMessage` for a call) and returns the settled world only when the message returns `.ok`
with no error; `runMessages` folds a list of them from a start world, failing (`none`) at the
first message that does not settle cleanly. Message level only: no transaction admission.

`runMessages_cons_of_ok` unfolds one step from an `.ok` result with no error, so a capstone that
already proves each message's settlement restates it as one fold.
-/

namespace Blanc.Lift

open Jaune

/-- One root message of a scenario: a creation or a call, with its input built from the fork and
the previous settled world. -/
inductive RootMsg where
  | create (input : Fork → State → Msg)
  | call (input : Fork → State → Msg)

/-- The settled world of a message result: `some` the world exactly when the result is `.ok`
with no error. -/
def settledState : Except (EvmError × State × AdrSet × Tra) Devm → Option State
  | .ok d => match d.error with
    | none => some d.state
    | some _ => none
  | .error _ => none

/-- The message's raw result over world `W` on `fork`. -/
def RootMsg.result : RootMsg → Fork → State → Except (EvmError × State × AdrSet × Tra) Devm
  | .create m, fork, W => processCreateMessage (m fork W)
  | .call m, fork, W => processMessage (m fork W)

/-- Run the messages in order from `W`, each from the previous settled world; `none` at the first
message that does not settle without error. -/
def runMessages (fork : Fork) : State → List RootMsg → Option State
  | W, [] => some W
  | W, m :: ms => (settledState (m.result fork W)).bind fun W' => runMessages fork W' ms

theorem runMessages_cons_of_ok {fork : Fork} {W : State} {m : RootMsg} {ms : List RootMsg}
    {d : Devm} (h : m.result fork W = .ok d) (he : d.error = none) :
    runMessages fork W (m :: ms) = runMessages fork d.state ms := by
  simp only [runMessages, h, settledState, he, Option.bind_some]

end Blanc.Lift
