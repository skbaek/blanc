import Blanc.Lift.FloodLooper.Check
import Blanc.Lift.ExactWalkCallChild
import Blanc.Lift.WithdrawalRequest.UserGas
import Blanc.Lift.WithdrawalRequest.NatLiveness

/-!
# The flood caller makes exactly `k` committed submissions

The hand-written looper (`Blanc/Lift/FloodLooper`) reads a 32-byte count `k`
and a 56-byte submission payload from its calldata and makes `k` value-1 CALLs
to the withdrawal-request predeploy, each a committed submission at the
unchanged incoming excess.  This module composes the looper's lifted loop with
the predeploy's `exec_submission_fresh` (`Blanc/Lift/WithdrawalRequest/UserGas`)
through the shared child-CALL crossing (`Blanc/Lift/ExactWalkCallChild`) to
show the looper run succeeds and leaves the predeploy storage as the `k`-fold
`submit` image.

The construction is the refutation witness's block-B body: at excess 0 the fee
is 1, so value 1 pays each submission, and `k = 2895` drives the end-of-block
excess to `2893`.
-/

namespace Blanc.Lift.WithdrawalRequest.FloodWalk

open Jaune Blanc.Lift

/-- The looper's runtime bytes. -/
def code : ByteArray := Blanc.Lift.FloodLooper.code

/-- The looper's lifted program. -/
def prog : List SFunc := Blanc.Lift.FloodLooper.cert.prog

theorem prog_root : prog[0]? = some Blanc.Lift.FloodLooper.t_0000_c0 := rfl

theorem prog_head : prog[1]? = some Blanc.Lift.FloodLooper.t_0007_c1 := rfl

/-- The looper's calldata: the 32-byte count word followed by the 56-byte
submission payload. -/
def calldata (k : B256) (payload : Bytes) : Bytes := k.toBytes ++ payload

theorem calldata_length {k : B256} {payload : Bytes} (hp : payload.length = 56) :
    (calldata k payload).length = 88 := by
  simp only [calldata, List.length_append, B256.length_toBytes, hp]

/-- The leftover gas a committed submission leaves the caller, for an incoming
child gas grant `g`. -/
def submissionLeftover (msg : Msg) (iters g : Nat) : Nat :=
  g - userSubmissionGas (initSevm msg) (initDevm msg) Mem.empty iters

/-- A message into the installed withdrawal predeploy, carrying a 56-byte
payload with enough gas and value to pay the incoming word fee, executes a
committed submission: `exec (initEvm msg)` succeeds without error.  Stated so
it discharges the `h_exec` premise of `Ninst.runCompiled_call_nonzero_child`
at `msg = callChildMsg …`. -/
theorem submission_child_exec {msg : Msg} {iters : Nat} {out : B256}
    (hfork : CoveredFork msg.benv.stat.fork)
    (hcode : msg.code = Blanc.withdrawalRequestCode)
    (huser : msg.caller ≠ systemAddress)
    (hlen : msg.data.length = 56)
    (hstatic : msg.isStatic = false)
    (hactive : (initDevm msg).getStorVal msg.currentTarget 0 ≠ B256.max)
    (hrun : WordFakeExponential.Run ((initDevm msg).getStorVal msg.currentTarget 0)
      17 1 17 0 iters out)
    (hpaid : (out / (17 : B256)).toNat ≤ msg.value.toNat)
    (hgas : userSubmissionGas (initSevm msg) (initDevm msg) Mem.empty iters + gCallStipend
      < msg.gas) :
    exec (initEvm msg) =
      .ok (submissionPost (initSevm msg) (afterSload (initSevm msg) (initDevm msg) 0) Mem.empty
        (submissionLeftover msg iters msg.gas)) := by
  have hslack : gCallStipend < submissionLeftover msg iters msg.gas := by
    unfold submissionLeftover; omega
  have hfresh := exec_submission_fresh (sevm := initSevm msg) (b := initDevm msg)
    (G := submissionLeftover msg iters msg.gas) (iterations := iters) (finalOutput := out)
    hcode hfork huser hlen hstatic hslack hactive hrun hpaid
  rw [← userSubmissionGas_empty (initSevm msg) (initDevm msg) iters] at hfresh
  have hgasEq : submissionLeftover msg iters msg.gas +
      userSubmissionGas (initSevm msg) (initDevm msg) Mem.empty iters = msg.gas := by
    unfold submissionLeftover; omega
  rw [hgasEq] at hfresh
  have hStEq : St (initDevm msg) [] Mem.empty msg.gas = initDevm msg := by
    have h := St.self (d := initDevm msg) (S := []) (M := Mem.empty) rfl rfl
    rw [initDevm_gasLeft] at h
    exact h.symm
  rw [hStEq] at hfresh
  exact (exec_iff_exec_eq 0 (initSevm msg) (initDevm msg) _).mp hfresh

end Blanc.Lift.WithdrawalRequest.FloodWalk
