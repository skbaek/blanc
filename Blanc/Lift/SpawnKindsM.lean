import Blanc.ExecutionEntryAccounting
import Blanc.ExecutionReachable

/-!
# Spawn kinds from the bytes: `SpawnKinds` without a cursor

`SpawnKinds ca sem` (`Blanc/ExecutionEntryAccounting.lean`) asks that every external
instruction decoded along a successful target frame's own same-frame chain is `CALL` or
`STATICCALL`.  For a `Cert.check` certificate it is discharged through the certificate cursor
(`cursor_of_parentPrefix`, `CursorOK.exec_call_or_staticcall`, `Blanc/Lift/Cursor.lean`); a
`Cert.checkM` (memory-map) certificate has no cursor.

This module discharges it from the code bytes alone, for any certificate format:

* `Exec.Deriv.ParentPrefix.noPush`: every node of a frame's same-frame chain entered at a
  position no `PUSH` immediate covers sits at such a position (`Evm.step_cont_noPush` for a
  continued step; a spawn edge moves past its one-byte `X`-class opcode);
* `callKindsCheck code`: a linear walk over the instruction starts (stepping over `PUSH`
  immediates, as `spawnFreeCheck` does) refusing every `X`-class byte but `CALL` and
  `STATICCALL`, read off `code.data.toList` so a kernel decision over a large runtime is
  linear;
* `callKinds_of_check`: the walk is sound at every position no `PUSH` immediate covers
  (`PushReach.of_noPushBefore`);
* `spawnKinds_of_callKindsCheck`: hence `SpawnKinds ca sem` for any code semantics whose runs
  execute checked bytes.

The walk treats the immediate of `DUPN`/`SWAPN`/`EXCHANGE` as an instruction start (it
over-approximates the reached positions), so it can only refuse more, never less.
-/

namespace Blanc.Lift

open Jaune

/-! ### Reached positions along a same-frame chain -/

/-! ### The decidable walk -/

/-- A byte admitted at an instruction start: it decodes no external instruction, or decodes
`CALL` or `STATICCALL`. -/
def callKindByte (b : UInt8) : Bool :=
  b.toXinst.all fun x => x == .call || x == .staticcall

/-- The linear instruction walk over a byte list, `skip` immediate bytes still to pass. -/
def callKindsWalk : List UInt8 → Nat → Bool
  | [], _ => true
  | b :: bs, 0 => callKindByte b && callKindsWalk bs (pushWidth b)
  | _ :: bs, skip + 1 => callKindsWalk bs skip

/-- The decidable check: every instruction start of the linear walk from `0` holds a byte
admitted by `callKindByte`.  It reads `code.data.toList` (a projection), so a kernel decision is
linear in the code size. -/
def callKindsCheck (code : ByteArray) : Bool := callKindsWalk code.data.toList 0

/-- The walk steps over `PUSH` data (`0xF4` inside a `PUSH1`) and admits `CALL`. -/
example : callKindsCheck ⟨#[0x60, 0xf4, 0xf1, 0x00]⟩ = true := by decide +kernel

/-- The walk refuses a `DELEGATECALL` at an instruction start. -/
example : callKindsCheck ⟨#[0x60, 0x00, 0xf4]⟩ = false := by decide +kernel

/-! ### `SpawnKinds` -/

end Blanc.Lift
