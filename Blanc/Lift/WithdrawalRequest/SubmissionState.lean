import Blanc.Lift.WithdrawalRequest.UserFeeDispatch
import Blanc.Lift.ExactWalkOps

/-! Sequential raw submission effects. No queue-key disjointness is assumed. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

def submissionCount (sevm : Sevm) (b : Devm) : B256 :=
  b.getStorVal sevm.currentTarget 1

def submissionCountRead (sevm : Sevm) (b : Devm) : Devm := afterSload sevm b 1

def submissionCountStore (sevm : Sevm) (b : Devm) : Devm :=
  afterSstore sevm (submissionCountRead sevm b) 1 (1 + submissionCount sevm b)

/-- This word is read before any queue write and retained on the operand stack. -/
def submissionTail (sevm : Sevm) (b : Devm) : B256 :=
  (submissionCountStore sevm b).getStorVal sevm.currentTarget 3

def submissionTailRead (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm (submissionCountStore sevm b) 3

def submissionKey (sevm : Sevm) (b : Devm) : B256 := 4 + 3 * submissionTail sevm b

def submissionCallerStore (sevm : Sevm) (b : Devm) : Devm :=
  afterSstore sevm (submissionTailRead sevm b) (submissionKey sevm b) sevm.caller.toB256

def submissionWord1Store (sevm : Sevm) (b : Devm) : Devm :=
  afterSstore sevm (submissionCallerStore sevm b) (1 + submissionKey sevm b)
    (Sevm.dataWord sevm 0)

def submissionWordsStore (sevm : Sevm) (b : Devm) : Devm :=
  afterSstore sevm (submissionWord1Store sevm b) (1 + (1 + submissionKey sevm b))
    (Sevm.dataWord sevm 32)

def submissionCallerMemory (sevm : Sevm) (M : Mem) : Mem :=
  M.write 0 (sevm.caller.toB256 <<< 96).toBytes

def submissionCopyMemory (sevm : Sevm) (M : Mem) : Mem :=
  (submissionCallerMemory sevm M).write 20 (sevm.data.sliceD 0 56 0)

def submissionLog (sevm : Sevm) (M : Mem) : Log :=
  ⟨sevm.currentTarget, [], ((submissionCopyMemory sevm M).read 0 76).1⟩

def submissionMemory (sevm : Sevm) (M : Mem) : Mem :=
  ((submissionCopyMemory sevm M).read 0 76).2

def submissionLogged (sevm : Sevm) (b : Devm) (M : Mem) : Devm :=
  (submissionWordsStore sevm b).addLog (submissionLog sevm M)

def submissionBase (sevm : Sevm) (b : Devm) (M : Mem) : Devm :=
  afterSstore sevm (submissionLogged sevm b M) 3 (1 + submissionTail sevm b)

/-- STOP preserves the inherited output and error fields. -/
def submissionPost (sevm : Sevm) (b : Devm) (M : Mem) (G : Nat) : Devm :=
  St (submissionBase sevm b M) [] (submissionMemory sevm M) G

def submissionCountGas (sevm : Sevm) (b : Devm) : Nat :=
  12 + sloadCost sevm b 1 +
    sstoreCost sevm (submissionCountRead sevm b) 1 (1 + submissionCount sevm b)

def submissionWordsGas (sevm : Sevm) (b : Devm) : Nat :=
  54 + sloadCost sevm (submissionCountStore sevm b) 3 +
    sstoreCost sevm (submissionTailRead sevm b) (submissionKey sevm b) sevm.caller.toB256 +
    sstoreCost sevm (submissionCallerStore sevm b) (1 + submissionKey sevm b)
      (Sevm.dataWord sevm 0) +
    sstoreCost sevm (submissionWord1Store sevm b) (1 + (1 + submissionKey sevm b))
      (Sevm.dataWord sevm 32)

def submissionMstoreGas (M : Mem) : Nat :=
  gVerylow + (calculateMemoryGasCost (memExtSize M.size 0 32) - calculateMemoryGasCost M.size)

def submissionCopyGas (sevm : Sevm) (M : Mem) : Nat :=
  gVerylow + gasCopy * ceilDiv 56 32 +
    (calculateMemoryGasCost (memExtSize (submissionCallerMemory sevm M).size 20 56) -
      calculateMemoryGasCost (submissionCallerMemory sevm M).size)

def submissionLogGas (sevm : Sevm) (M : Mem) : Nat :=
  gLog + gLogdata * 76 + gLogtopic * 0 +
    (calculateMemoryGasCost (memExtSize (submissionCopyMemory sevm M).size 0 76) -
      calculateMemoryGasCost (submissionCopyMemory sevm M).size)

def submissionSuffixGas (sevm : Sevm) (b : Devm) (M : Mem) : Nat :=
  32 + submissionMstoreGas M + submissionCopyGas sevm M + submissionLogGas sevm M +
    sstoreCost sevm (submissionLogged sevm b M) 3 (1 + submissionTail sevm b)

def submissionBodyGas (sevm : Sevm) (b : Devm) (M : Mem) : Nat :=
  submissionCountGas sevm b + submissionWordsGas sevm b + submissionSuffixGas sevm b M

/-- Ordered storage writes remain exact even when a queue key aliases any metadata key. -/
theorem submissionPost_storage (sevm : Sevm) (b : Devm) (M : Mem) (G : Nat) :
    Devm.getStor (submissionPost sevm b M G) sevm.currentTarget =
      (((((Devm.getStor b sevm.currentTarget).set 1 (1 + submissionCount sevm b)).set
        (submissionKey sevm b) sevm.caller.toB256).set
        (1 + submissionKey sevm b) (Sevm.dataWord sevm 0)).set
        (1 + (1 + submissionKey sevm b)) (Sevm.dataWord sevm 32)).set
        3 (1 + submissionTail sevm b) := by
  rw [submissionPost]
  rw [show Devm.getStor (St (submissionBase sevm b M) [] (submissionMemory sevm M) G)
      sevm.currentTarget = Devm.getStor (submissionBase sevm b M) sevm.currentTarget from by
    generalize submissionBase sevm b M = finalBase
    rfl]
  simp only [submissionBase, submissionLogged, submissionWordsStore, submissionWord1Store,
    submissionCallerStore, submissionTailRead, submissionCountStore, submissionCountRead,
    afterSstore_getStor_self, afterSload_getStor, Devm.addLog_getStor]

/-- The named complete base retains every world and metadata update of the sequential walk. -/
theorem submissionPost_facts (sevm : Sevm) (b : Devm) (M : Mem) (G : Nat) :
    (submissionPost sevm b M G).world = (submissionBase sevm b M).world ∧
    (submissionPost sevm b M G).meta = (submissionBase sevm b M).meta ∧
    (submissionPost sevm b M G).stack = [] ∧
    (submissionPost sevm b M G).memory = submissionMemory sevm M ∧
    (submissionPost sevm b M G).gasLeft = G ∧
    (submissionPost sevm b M G).stateGas = (submissionBase sevm b M).stateGas := by
  unfold submissionPost
  generalize submissionBase sevm b M = finalBase
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exactly one LOG0 is appended after the three queue-word writes. -/
theorem submissionBase_logs (sevm : Sevm) (b : Devm) (M : Mem) :
    (submissionBase sevm b M).logs = b.logs ++ [submissionLog sevm M] := by
  rw [submissionBase, afterSstore_logs, submissionLogged, logs_addLog,
    submissionWordsStore, afterSstore_logs, submissionWord1Store, afterSstore_logs,
    submissionCallerStore, afterSstore_logs, submissionTailRead, afterSload_logs,
    submissionCountStore, afterSstore_logs, submissionCountRead, afterSload_logs]

/-- STOP and the submission body leave the inherited output and error intact. -/
theorem submissionBase_inherited (sevm : Sevm) (b : Devm) (M : Mem) :
    (submissionBase sevm b M).output = b.output ∧ (submissionBase sevm b M).error = b.error := by
  constructor
  · rw [submissionBase, afterSstore_output, submissionLogged]
    rw [show ((submissionWordsStore sevm b).addLog (submissionLog sevm M)).output =
        (submissionWordsStore sevm b).output from by
      generalize submissionWordsStore sevm b = written
      rfl]
    rw [submissionWordsStore, afterSstore_output, submissionWord1Store, afterSstore_output,
      submissionCallerStore, afterSstore_output, submissionTailRead, afterSload_output,
      submissionCountStore, afterSstore_output, submissionCountRead, afterSload_output]
  · rw [submissionBase, afterSstore_error, submissionLogged, Devm.addLog_error,
      submissionWordsStore, afterSstore_error, submissionWord1Store, afterSstore_error,
      submissionCallerStore, afterSstore_error, submissionTailRead, afterSload_error,
      submissionCountStore, afterSstore_error, submissionCountRead, afterSload_error]

end Blanc.Lift.WithdrawalRequest
