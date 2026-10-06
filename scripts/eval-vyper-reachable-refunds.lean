import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolBoundary
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit.Capstone

/-! Native, finite refund observations for the exact reachable message chains.
No manufactured checkpoints, transaction refund caps, or replacement evaluator.
The companion Python driver validates the completed output and binds its provenance. -/

namespace Blanc.VyperReachableRefunds

open Jaune

private abbrev J := _root_.Lean.Json

private structure Step where
  label : String
  create : Bool
  message : Fork → State → Msg
  observe : Bool

private def minusSteps : List Step := [
  ⟨"implCreateMsg", true,
    Lift.VyperNonreentrantDeployed.Vulnerable.Reach.implCreateMsg, true⟩,
  ⟨"cloneCreateMsg", true,
    Lift.VyperNonreentrantDeployed.Vulnerable.Reach.cloneCreateMsg, true⟩,
  ⟨"initMsg", false, Lift.VyperNonreentrantDeployed.Vulnerable.Reach.initMsg, true⟩,
  ⟨"tokenCreateMsg", true,
    Lift.VyperNonreentrantDeployed.Vulnerable.Reach.tokenCreateMsg, true⟩,
  ⟨"attackerCreateMsg", true,
    Lift.VyperNonreentrantDeployed.Vulnerable.Reach.attackerCreateMsg, true⟩,
  ⟨"approveMsg", false, Lift.VyperNonreentrantDeployed.Vulnerable.Reach.approveMsg, true⟩,
  ⟨"addMsg", false, Lift.VyperNonreentrantDeployed.Vulnerable.Reach.addMsg, true⟩,
  ⟨"Viol.violMsg", false, Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol.violMsg, true⟩]

private def plusSteps : List Step := [
  ⟨"Reach.implCreateMsg", true,
    Lift.VyperNonreentrantDeployed.Fixed.Reach.implCreateMsg, true⟩,
  ⟨"Reach.cloneCreateMsg", true,
    Lift.VyperNonreentrantDeployed.Fixed.Reach.cloneCreateMsg, true⟩,
  ⟨"Init.initMsg", false, Lift.VyperNonreentrantDeployed.Fixed.Init.initMsg, false⟩,
  ⟨"Init.oracleMsg", false, Lift.VyperNonreentrantDeployed.Fixed.Init.oracleMsg, false⟩,
  ⟨"Fund.tokenCreateMsg", true,
    Lift.VyperNonreentrantDeployed.Fixed.Fund.tokenCreateMsg, true⟩,
  ⟨"Fund.receiverCreateMsg", true,
    Lift.VyperNonreentrantDeployed.Fixed.Fund.receiverCreateMsg, true⟩,
  ⟨"Fund.approveMsg", false, Lift.VyperNonreentrantDeployed.Fixed.Fund.approveMsg, false⟩,
  ⟨"Fund.addMsg", false, Lift.VyperNonreentrantDeployed.Fixed.Fund.addMsg, false⟩,
  ⟨"Fund.removeMsg", false, Lift.VyperNonreentrantDeployed.Fixed.Fund.removeMsg, false⟩]

private def runChain (fork : Fork) (side : String) (start : State) (steps : List Step) :
    IO (Array J) := do
  let stderr ← IO.getStderr
  let mut world := start
  let mut rows : Array J := #[]
  for step in steps do
    stderr.putStrLn s!"step {side} {step.label}: begin"
    let msg := step.message fork world
    let post ← match (if step.create then Jaune.processCreateMessage msg
                     else Jaune.processMessage msg) with
      | .error _ => throw (IO.userError s!"{side} {step.label}: process failed")
      | .ok post => pure post
    if post.error.isSome then
      throw (IO.userError s!"{side} {step.label}: settled error")
    if step.observe then
      rows := rows.push (.mkObj [
        ("message", .str step.label),
        ("refundCounter", .str (toString post.refundCounter))])
    world := post.state
    stderr.putStrLn s!"step {side} {step.label}: settled"
  return rows

def observe (name : String) (fork : Fork) : IO J := do
  let minus ← runChain fork "Vminus"
    Lift.VyperNonreentrantDeployed.Vulnerable.Reach.initialWorld minusSteps
  let plus ← runChain fork "Vplus"
    Lift.VyperNonreentrantDeployed.Fixed.Reach.initialWorld plusSteps
  return .mkObj [
    ("schema", .str "vyper-reachable-refunds-v1"),
    ("fork", .str name),
    ("completed", .bool true),
    ("prerequisiteMessages", .str "17"),
    ("Vminus", .arr minus),
    ("Vplus", .arr plus)]

end Blanc.VyperReachableRefunds

def main (args : List String) : IO UInt32 := do
  let [name] := args
    | throw (IO.userError "usage: eval-vyper-reachable-refunds.lean prague|osaka|bpo1|bpo2")
  let fork ← match name with
    | "prague" => pure Jaune.Fork.prague
    | "osaka" => pure Jaune.Fork.osaka
    | "bpo1" => pure Jaune.Fork.bpo1
    | "bpo2" => pure Jaune.Fork.bpo2
    | _ => throw (IO.userError "unknown covered fork")
  let result ← Blanc.VyperReachableRefunds.observe name fork
  IO.println result.compress
  return 0
