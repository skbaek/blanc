import Blanc.Lift.BeaconDeposit.Prog

/-!
# The deployed `deposit` ABI decoder: arguments and acceptance

The deployed wrapper for `deposit(bytes,bytes,bytes,bytes32)` (pc `0x00a4`) decodes three dynamic
`bytes` tails and one word, then jumps to the internal function (pc `0x0304`, certificate entry 7) with
the stack, top first,

  `root, sigLen, sigPtr, wcLen, wcPtr, pkLen, pkPtr, 0x01b8, selector`

where for the `i`-th dynamic argument `off i = CALLDATALOAD (4 + 32 i)`, `len i = CALLDATALOAD (4 + off i)`
and `ptr i = 36 + off i` (calldata position of its first byte).  `0x01b8` is the return tag of the
wrapper's `STOP`.

`DepositDecodable` is the exact acceptance condition of the deployed decoder, read off its guards
(every comparison is on 256-bit words; `CDS` is `CALLDATASIZE`):

* head: `CDS - 4 ≥ 0x80`;
* for each tail: `off ≤ 2^32`; `(4 + off) + 32 ≤ CDS`; `len ≤ 2^32`; `(36 + off) + len ≤ CDS`.

This is the deployed code's own boundary, not the port's `DepositAbiDecodable` (which the port
compares with the deployed decoder only on a finite matrix, deviation BD-3).
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-- The offset word of dynamic argument `i` (`0`: pubkey, `1`: withdrawal credentials, `2`: signature). -/
def argOff (sevm : Sevm) (i : Nat) : B256 := Sevm.dataWord sevm (4 + 32 * Nat.toB256 i)

/-- The length word of dynamic argument `i`. -/
def argLen (sevm : Sevm) (i : Nat) : B256 := Sevm.dataWord sevm (4 + argOff sevm i)

/-- The calldata position of the first byte of dynamic argument `i`. -/
def argPtr (sevm : Sevm) (i : Nat) : B256 := 32 + (4 + argOff sevm i)

/-- The `deposit_data_root` word. -/
def argRoot (sevm : Sevm) : B256 := Sevm.dataWord sevm 100

/-- The stack the decoder hands to the internal `deposit` (entry 7), top first. -/
def depositArgStack (sevm : Sevm) (rest : List B256) : List B256 :=
  argRoot sevm :: argLen sevm 2 :: argPtr sevm 2 :: argLen sevm 1 :: argPtr sevm 1 ::
    argLen sevm 0 :: argPtr sevm 0 :: 0x01b8 :: rest

/-- One dynamic tail passes the deployed decoder's three guards. -/
def TailDecodable (sevm : Sevm) (i : Nat) : Prop :=
  (argOff sevm i).toNat ≤ 2 ^ 32 ∧
    (4 + argOff sevm i + 32).toNat ≤ sevm.data.length ∧
    (argLen sevm i).toNat ≤ 2 ^ 32 ∧
    (argPtr sevm i + argLen sevm i).toNat ≤ sevm.data.length

/-- The deployed decoder accepts the calldata. -/
def DepositDecodable (sevm : Sevm) : Prop :=
  132 ≤ sevm.data.length ∧ TailDecodable sevm 0 ∧ TailDecodable sevm 1 ∧ TailDecodable sevm 2

end Blanc.Lift.BeaconDeposit
