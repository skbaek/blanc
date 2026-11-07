import Blanc.Lift.BuilderRequest.FeePath
import Blanc.Lift.BuilderRequest.Deposit.Jumps

/-!
# The deposit runtime's fee path and fee read

The deposit runtime as an instance of the builder contracts' `UserPath`, with its fee read at target
8. The statements hold for any storage; nothing here says which storage is reachable.
-/

namespace Blanc.Lift.BuilderRequest.Deposit

open Jaune

/-- The checked certificate's program. -/
def prog : List SFunc := cert.prog

/-- The deposit runtime's user path. -/
def userPath : UserPath where
  code := code
  cert := cert
  check := cert_check
  jumps := jumps_ok
  noExec := progNoExec_of_all (by decide +kernel)
  shape :=
    { revert := ⟨0x02, [0x70], by decide⟩
      target := ⟨0x08, [], by decide⟩
      over := ⟨0x52, [], by decide⟩
      under := ⟨0x58, [], by decide⟩
      window := 1
      post := ⟨0x7f, [], by decide⟩
      loop := ⟨0x64, [], by decide⟩
      loopEntry := 6
      len := ⟨0xb8, [], by decide⟩
      submit := ⟨0x9f, [], by decide⟩ }
  systemDest := ⟨0x01, [0x1c], by decide⟩
  system := t_011c_c0
  revert := t_0270_c0
  getterDest := ⟨0x02, [0x70], by decide⟩
  getterRevert := t_0270_c1
  submission := t_009f_c1
  root := rfl
  window := rfl
  loop := rfl
  revert_noOk := rfl
  getterRevert_noOk := rfl
  len_ne := by decide

end Blanc.Lift.BuilderRequest.Deposit
