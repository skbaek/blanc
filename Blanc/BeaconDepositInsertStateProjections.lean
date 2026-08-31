import Blanc.BeaconDepositInsertFold

/-!
# Beacon deposit insertion-state projections

One-layer projections over an abstract loop state.  These keep downstream
induction proofs from normalizing concrete state constructors in the kernel.
-/

namespace Blanc.BeaconDeposit

open Jaune

@[simp] theorem InsertionLoopState.step_height_eq
    (owner : Adr) (stor : Stor) (s : InsertionLoopState) :
    (s.step owner stor).height = s.height + 1 := rfl

@[simp] theorem InsertionLoopState.step_node_eq
    (owner : Adr) (stor : Stor) (s : InsertionLoopState) :
    (s.step owner stor).node =
      hashPair Bytes.sha256 (stor.get s.key) s.node := rfl

end Blanc.BeaconDeposit
