import Blanc.BeaconDepositCore
import Blanc.BeaconDepositCorrectness

/-!
# The deployed contract's storage layout and its storage abstraction

The deployed runtime stores the source's state in Solidity's layout (deviation BD-1 in
`BEACON_DEPOSIT_DEVIATIONS.md` describes Blanc's port, which uses a different one):

* `branch[h]` at slot `h` for `h < 32`;
* `deposit_count` at slot `32`;
* `zero_hashes[h]` at slot `33 + h` for `h < 32`.

`solAcc` reads the pure model's accumulator (`BeaconDeposit.Acc`) out of such a storage, and
`SolInv` is the storage abstraction the refinement theorems carry: the constructor's zero-hash
table is intact and the model invariant `BeaconDeposit.Inv` holds for the leaf history.  They
mirror the port's `accOfStor`, `ZeroHashesCorrect` and `ArtifactInv`
(`Blanc/BeaconDepositCore.lean`, `Blanc/BeaconDepositBridge.lean`) with this layout's slots.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune
open Blanc.BeaconDeposit

def solBranchSlot (height : Nat) : B256 := Nat.toB256 height

def solCountSlot : B256 := 32

def solZeroHashSlot (height : Nat) : B256 := Nat.toB256 (33 + height)

/-- The model accumulator stored in Solidity's layout. -/
def solAcc (stor : Stor) : Acc :=
  { branch := fun height => if height < 32 then stor.get (solBranchSlot height) else 0
    count := (stor.get solCountSlot).toNat }

/-- The constructor's zero-subtree table, as the deployed code reads it. -/
def SolZeroHashesCorrect (stor : Stor) : Prop :=
  ∀ height, height < 32 → stor.get (solZeroHashSlot height) = zeroHash Bytes.sha256 height

/-- The storage abstraction: intact zero-hash table and the model invariant for `history`. -/
def SolInv (stor : Stor) (history : List B256) : Prop :=
  SolZeroHashesCorrect stor ∧ Inv Bytes.sha256 (solAcc stor) history

end Blanc.Lift.BeaconDeposit
