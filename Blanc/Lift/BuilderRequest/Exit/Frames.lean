import Blanc.Lift.BuilderRequest.FeePath
import Blanc.Lift.BuilderRequest.Exit.Jumps

/-!
# The exit contract's user frames, under covered forks

While slot 0 holds the inhibitor, no user call at the exit code succeeds. The fee read is stated
with slot 0 off the inhibitor: that is a statement about any such storage, not a claim that it is
reachable. The submission path is not walked. Nothing here is stated for Amsterdam.
-/

namespace Blanc.Lift.BuilderRequest.Exit

open Jaune

/-- The exit runtime's user path. -/
def userPath : UserPath where
  code := code
  cert := cert
  check := cert_check
  jumps := jumps_ok
  shape :=
    { revert := ⟨0x01, [0xc6], by decide⟩
      target := ⟨0x02, [], by decide⟩
      over := ⟨0x51, [], by decide⟩
      under := ⟨0x57, [], by decide⟩
      window := 1
      post := ⟨0x7e, [], by decide⟩
      loop := ⟨0x63, [], by decide⟩
      loopEntry := 6
      len := ⟨0x30, [], by decide⟩
      submit := ⟨0x9e, [], by decide⟩ }
  systemDest := ⟨0xe1, [], by decide⟩
  system := t_00e1_c0
  revert := t_01c6_c0
  getterDest := ⟨0x01, [0xc6], by decide⟩
  getterRevert := t_01c6_c1
  submission := t_009e_c1
  root := rfl
  window := rfl
  loop := rfl
  revert_noOk := rfl
  getterRevert_noOk := rfl
  len_ne := by decide

variable {sevm : Sevm} {pre post : Devm}

/-- While slot 0 holds the inhibitor, no execution of the exit code at a non-system caller from an
empty stack succeeds. -/
theorem exec_user_inhibited_no_ok (hcode : sevm.code = code)
    (fork : CoveredFork sevm.benvStat.fork) (stack : pre.stack = [])
    (caller : sevm.caller ≠ systemAddress)
    (inhibited : pre.getStorVal sevm.currentTarget 0 = B256.max)
    (exec : Exec 0 sevm pre (.ok post)) : False :=
  UserPath.exec_inhibited_no_ok (k := userPath) hcode fork stack caller inhibited exec

/-- **Exit rejection.** While slot 0 holds the inhibitor, every execution of the exit code at a
non-system caller from an empty stack ends in failure, for any calldata, value and memory. Failure
rolls the frame back. With enough gas the failure is the code's `REVERT`; with too little it is
out-of-gas, so a gas-free statement cannot say `REVERT` specifically. -/
theorem exec_user_inhibited_fails {outcome : Execution} (hcode : sevm.code = code)
    (fork : CoveredFork sevm.benvStat.fork) (stack : pre.stack = [])
    (caller : sevm.caller ≠ systemAddress)
    (inhibited : pre.getStorVal sevm.currentTarget 0 = B256.max)
    (exec : Exec 0 sevm pre outcome) : ∃ failure, outcome = .error failure := by
  cases outcome with
  | ok post => exact (exec_user_inhibited_no_ok hcode fork stack caller inhibited exec).elim
  | error failure => exact ⟨failure, rfl⟩

/-- **Exit fee read.** With slot 0 off the inhibitor, a successful empty-calldata execution at a
non-system caller carries no value, changes no storage, balance or log, and returns the word
recurrence's quotient on `slot0 + max(0, count - 2)`. `aligned` and `wf` hold of the empty memory
every frame starts with. -/
theorem exec_fee_read (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (caller : sevm.caller ≠ systemAddress) (empty : sevm.data = [])
    (exec : Exec 0 sevm pre (.ok post)) :
    ∃ iterations finalOutput, UserPath.FeeRead 2 sevm pre post iterations finalOutput :=
  UserPath.exec_fee_read (k := userPath) hcode fork stack aligned wf caller empty exec

/-- The exit fee read, forward: such a read exists at the exact charge whenever slot 0 is off the
inhibitor, so `exec_fee_read`'s premises can be met. -/
theorem exec_fee_read_exact {b : Devm} {M : Mem} {G iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (aligned : M.size % 32 = 0) (caller : sevm.caller ≠ systemAddress)
    (empty : sevm.data = []) (zero : sevm.value = 0)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 sevm b) 17 1 17 0 iterations finalOutput) :
    Nonempty (Exec 0 sevm (St b [] M (G + UserPath.feeReadGas sevm b M iterations))
      (.ok (RequestFee.feeGetterPost (feeBase sevm b) M (finalOutput / (17 : B256)) G))) :=
  UserPath.exec_fee_read_exact (k := userPath) hcode fork aligned caller empty zero off wordRun

end Blanc.Lift.BuilderRequest.Exit
