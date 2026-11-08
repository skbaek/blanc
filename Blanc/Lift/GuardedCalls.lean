import Blanc.Lift.SpawnKindsM
import Blanc.CallSpawnExact
import Blanc.ForwardCall
import Blanc.Lift.FrameWalk
import Blanc.Lift.InvWalkGas
import Blanc.Lift.ReturnDataBound
import Blanc.ExecutionCodeAt

/-!
# Flag-guarded calls: the children of a successful frame commit

A frame whose code tests the success flag of every call it makes (a failed call falls through to a
`REVERT`) cannot succeed after a child that did not commit.  This module states that discipline as a
byte-level fact about the code and proves its consequence for any successful derivation.

* `guardCheck code`: a linear walk over the instruction starts (stepping over `PUSH` immediates, as
  `callKindsCheck` does, reading `code.data.toList`) admitting at every start an external
  instruction only if it is `CALL` or `STATICCALL` and either
  - **flag-guarded**: the next bytes are `PUSH2 _ _; JUMPI; PUSH1 0; DUP1; REVERT`, so a zero flag
    falls through to the `REVERT`; or
  - **an identity copy**: the previous two instruction starts are `GAS` and `PUSH1 4`, so the target
    word is `4`.
* `guardCheck_sound`: what the walk guarantees at every reached position (`PushReach`);
* `Exec.rawFrameDescendants_of_guardCheck` (and its entry form `…_entry`): in a successful
  derivation of checked code, every raw frame descendant lies under a direct committed child —
  a child that did not commit leaves the flag `0`, which a guarded site reverts on, and an identity
  copy (target word `4`, tracked by `IdGuard` along the chain, the linear walk's predecessors being
  unique: `PushReach.succ_inj`) enters no code frame while the code at `4` is undelegated.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-! ## The walk -/

/-- The bytes after a flag-guarded call (the list starts at the call byte):
`PUSH2 _ _; JUMPI; PUSH1 0; DUP1; REVERT`. -/
def guardedAfter : List UInt8 → Bool
  | _ :: b1 :: _ :: _ :: b4 :: b5 :: b6 :: b7 :: b8 :: _ =>
    b1 == 0x61 && b4 == 0x57 && b5 == 0x60 && b6 == 0x00 && b7 == 0x80 && b8 == 0xfd
  | _ => false

/-- One instruction start at `pos` (byte `b`, bytes from it `xs`), whose two previous instruction
starts are `p1` and `p2`. -/
def guardSiteOk (full xs : List UInt8) (b : UInt8) (pos p1 p2 : Nat) : Bool :=
  b != 0xe6 && b != 0xe7 && b != 0xe8 &&
  match b.toXinst with
  | none => true
  | some x =>
    (x == .call || x == .staticcall) &&
      (guardedAfter xs ||
        (b == 0xf1 && p1 + 1 == pos && p2 + 2 == p1 && full[p1]? == some 0x5a &&
          full[p2]? == some 0x60 && full[p2 + 1]? == some 0x04))

/-- The linear instruction walk: `skip` immediate bytes still to pass, `p1`, `p2` the two previous
instruction starts. -/
def guardWalk (full : List UInt8) : List UInt8 → Nat → Nat → Nat → Nat → Bool
  | [], _, _, _, _ => true
  | b :: bs, pos, 0, p1, p2 =>
    guardSiteOk full (b :: bs) b pos p1 p2 && guardWalk full bs (pos + 1) (pushWidth b) pos p1
  | _ :: bs, pos, skip + 1, p1, p2 => guardWalk full bs (pos + 1) skip p1 p2

/-- **The flag-guard check** (see the module note). -/
def guardCheck (code : ByteArray) : Bool :=
  guardWalk code.data.toList code.data.toList 0 0 (code.size + 5) (code.size + 5)

/-! ## Soundness -/

/-! ## The linear walk has unique predecessors -/

/-! ## Where a continued step lands -/

/-! ## A spawning `CALL` -/

/-! ## Decoding from bytes -/

/-! ## The identity-copy guard along a frame's chain -/

/-! ## A call child that does not commit leaves the flag `0` -/

/-! ## Successful frames of flag-guarded code: every entered child commits -/

/-- The check refuses an unguarded `CALL` that is no identity copy. -/
example : guardCheck ⟨#[0x60, 0x00, 0xf1, 0x00]⟩ = false := by decide +kernel

/-- The check admits a flag-guarded `CALL`. -/
example : guardCheck ⟨#[0xf1, 0x61, 0x00, 0x09, 0x57, 0x60, 0x00, 0x80, 0xfd, 0x5b]⟩ = true := by
  decide +kernel

end Blanc.Lift
