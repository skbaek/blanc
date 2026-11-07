import Blanc.Lift.SystemExecution.BeaconRoots.AmsterdamProbeExact
import Blanc.Lift.BuilderRequest.Deposit.Jumps
import Blanc.Lift.BuilderRequest.Exit.Jumps

/-!
# W1b probe, step 5: the lift's premise on the builder runtimes

Probe only; does not land. The byte-level `NoExecCode` is false for both builder runtimes, because
data of a `PUSH` can read as a call-family opcode. The certificate-level premise holds, and the
converse then needs no fork premise at all.
-/

namespace Blanc.Lift.BuilderRequest.AmsterdamProbe

open Jaune
open Blanc.Lift
open Blanc.Lift.SystemExecution.BeaconRoots.AmsterdamProbeExact

/-- Whether this decoded instruction is exactly `x`'s call-family node, by the opcode. -/
def isDelegatecall : Option Inst → Bool
  | some (.next (.exec .delegatecall)) => true
  | _ => false

def isCreate2 : Option Inst → Bool
  | some (.next (.exec .create2)) => true
  | _ => false

theorem of_isDelegatecall {i : Option Inst} (h : isDelegatecall i = true) :
    i = some (.next (.exec .delegatecall)) := by
  unfold isDelegatecall at h
  split at h
  · rfl
  · cases h

theorem of_isCreate2 {i : Option Inst} (h : isCreate2 i = true) :
    i = some (.next (.exec .create2)) := by
  unfold isCreate2 at h
  split at h
  · rfl
  · cases h

/-- Deposit position 487 decodes to `DELEGATECALL`: it is the data of `PUSH2 0x01f4` at 485. -/
theorem deposit_not_noExecCode : ¬ NoExecCode Deposit.code := by
  intro h
  refine h 487 .delegatecall ?_
  exact of_isDelegatecall (i := Deposit.code.getInst 487) (by decide +kernel)

/-- Exit position 240 decodes to `CREATE2`: it is the data of `PUSH1 0xf5` at 239. -/
theorem exit_not_noExecCode : ¬ NoExecCode Exit.code := by
  intro h
  refine h 240 .create2 ?_
  exact of_isCreate2 (i := Exit.code.getInst 240) (by decide +kernel)

theorem deposit_progNoExec : ProgNoExec Deposit.cert.prog :=
  progNoExec_of_all (by decide +kernel)

theorem exit_progNoExec : ProgNoExec Exit.cert.prog :=
  progNoExec_of_all (by decide +kernel)

/-- **The gas-exact converse on the deposit builder's runtime, under every fork**, Amsterdam
included. -/
theorem deposit_lift {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = Deposit.code)
    (hrun : SProg.RunExact Deposit.cert.prog sevm pre post) :
    Nonempty (Exec 0 sevm pre (.ok post)) :=
  lift_exact_lane Deposit.cert_check Deposit.jumps_ok hcode deposit_progNoExec hrun

/-- **The gas-exact converse on the exit builder's runtime, under every fork.** -/
theorem exit_lift {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = Exit.code)
    (hrun : SProg.RunExact Exit.cert.prog sevm pre post) :
    Nonempty (Exec 0 sevm pre (.ok post)) :=
  lift_exact_lane Exit.cert_check Exit.jumps_ok hcode exit_progNoExec hrun

end Blanc.Lift.BuilderRequest.AmsterdamProbe
