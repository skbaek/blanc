import Blanc.ExecutionSettlement

/-!
Concrete execution-level regression for CREATE code-deposit rollback.

The init code returns one byte beginning with `0xef`.  Its raw constructor
execution succeeds, but complete CREATE settlement rejects the deployed code.
The dependent fixture packages an actual `Exec.runOk` only along the concrete
machine branch where every required semantic observation holds.
-/

namespace Blanc.ExecutionSettlementRegression

open Jaune Blanc

noncomputable section

/-- The deliberately wrong retention rule used only by this regression. -/
private def rawCommittedDescendantFrames {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution} (run : Exec pc sevm pre out) :
    List Exec.Frame :=
  match run with
  | .halt _ => []
  | .cont _ next => rawCommittedDescendantFrames next
  | .doneErr _ _ _ => []
  | .doneOk _ _ _ next => rawCommittedDescendantFrames next
  | .runErr _ _ _ _ => []
  | .runOk _ _ child _ next =>
      let childFrames :=
        if h : Execution.commits child.outcome = true then
          Exec.Frame.ofRun child h :: rawCommittedDescendantFrames child
        else []
      childFrames ++ rawCommittedDescendantFrames next
termination_by sizeOf run

/-- Evidence carried by the inhabited branch of the concrete fixture. -/
private structure Fixture where
  pc : Nat
  nextPc : Nat
  sevm : Sevm
  pre : Devm
  resumed : Devm
  settled : Devm
  frame : Jaune.Frame
  resume : Resume
  childEvm : Evm
  raw : Execution
  out : Execution
  hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume nextPc
  henter : frame.enter = .run childEvm
  child : Exec childEvm.pc childEvm.sta childEvm.dyna raw
  hresume : resume.run (frame.settle raw) = .ok resumed
  next : Exec nextPc sevm resumed out
  rawCommits : Execution.commits raw = true
  isCreate : frame.isCreate = true
  settleResult : frame.settle raw = .ok settled
  settleError : settled.error.isSome = true
  settlementDoesNotCommit : Frame.settlementCommits frame raw ≠ true

private def Fixture.run (w : Fixture) : Exec w.pc w.sevm w.pre w.out :=
  Exec.runOk w.hstep w.henter w.child w.hresume w.next

private theorem Fixture.settlementTraversal_prunes (w : Fixture) :
    Exec.descendantFrames w.run = Exec.descendantFrames w.next :=
  Exec.descendantFrames_runOk_of_not_settlementCommits
    w.hstep w.henter w.child w.hresume w.next w.settlementDoesNotCommit

private theorem Fixture.rawTraversal_retains (w : Fixture) :
    rawCommittedDescendantFrames w.run =
      Exec.Frame.ofRun w.child w.rawCommits ::
        rawCommittedDescendantFrames w.child ++
          rawCommittedDescendantFrames w.next := by
  have hchild : Execution.commits w.child.outcome = true := w.rawCommits
  simp [Fixture.run, rawCommittedDescendantFrames, hchild]

private def initCode : Bytes :=
  [0x60, 0xef, 0x60, 0x00, 0x53, 0x60, 0x01, 0x60, 0x00, 0xf3]

private def parentSevm : Sevm :=
  { (default : Sevm) with code := ByteArray.mk #[0xf0, 0x00] }

private def parentDevm : Devm :=
  (((default : Devm).withGasLeft 100000).withStack [0, 0, 10]).withMemory
    (Mem.empty.write 0 initCode)

private def parentEvm : Evm := ⟨0, parentSevm, parentDevm⟩

/-- A computable mirror of the dependent fixture's branch conditions. -/
private def fixtureAvailable : Bool :=
  match parentEvm.step with
  | .spawn frame resume _ =>
      match frame.enter with
      | .run childEvm =>
          let raw := exec childEvm
          Execution.commits raw && frame.isCreate &&
            match frame.settle raw with
            | .ok settled =>
                settled.error.isSome &&
                  !Frame.settlementCommits frame raw &&
                    match resume.run (frame.settle raw) with
                    | .ok _ => true
                    | .error _ => false
            | .error _ => false
      | .done _ => false
  | _ => false

/-- The concrete `Exec.runOk` witness, present exactly on the checked branch. -/
private def fixture? : Option Fixture :=
  match hstep : parentEvm.step with
  | .spawn frame resume nextPc =>
      match henter : frame.enter with
      | .run childEvm =>
          let raw := exec childEvm
          if hraw : Execution.commits raw = true then
            if hcreate : frame.isCreate = true then
              match hsettled : frame.settle raw with
              | .ok settled =>
                  if herror : settled.error.isSome = true then
                    if hnot : Frame.settlementCommits frame raw ≠ true then
                      match hresume : resume.run (frame.settle raw) with
                      | .ok resumed =>
                          let out := exec ⟨nextPc, parentSevm, resumed⟩
                          let child := Classical.choice
                            ((exec_iff_exec_eq _ _ _ _).2 rfl)
                          let next := Classical.choice
                            ((exec_iff_exec_eq _ _ _ _).2 rfl)
                          some {
                            pc := 0
                            nextPc := nextPc
                            sevm := parentSevm
                            pre := parentDevm
                            resumed := resumed
                            settled := settled
                            frame := frame
                            resume := resume
                            childEvm := childEvm
                            raw := raw
                            out := out
                            hstep := hstep
                            henter := henter
                            child := child
                            hresume := hresume
                            next := next
                            rawCommits := hraw
                            isCreate := hcreate
                            settleResult := hsettled
                            settleError := herror
                            settlementDoesNotCommit := hnot
                          }
                      | .error _ => none
                    else none
                  else none
              | .error _ => none
            else none
          else none
      | .done _ => none
  | _ => none

-- The semantic gate requires this evaluator output to be exactly `true`.
#eval! fixtureAvailable

-- RAW-COMMIT-MUTANT-CONTROL

end

end Blanc.ExecutionSettlementRegression
