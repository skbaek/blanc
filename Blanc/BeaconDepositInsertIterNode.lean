import Blanc.BeaconDepositCorrectness
import Blanc.BeaconDepositInsertNat
import Blanc.BeaconDepositInsertStateProjections

/-! # Beacon deposit insertion-fold node projection -/

namespace Blanc.BeaconDeposit

open Jaune

private theorem insertionStep_height_of_nat
    {height : Nat} {s : InsertionLoopState}
    (owner : Adr) (stor : Stor)
    (hstate : s.height = Nat.toB256 height)
    (hheight : height < 32) :
    (s.step owner stor).height = Nat.toB256 (height + 1) := by
  rw [InsertionLoopState.step_height_eq, hstate]
  exact Blanc.toB256_add_one_of_lt height (by omega)

private theorem insertionStep_node_of_nat
    {height : Nat} {node : B256} {s : InsertionLoopState}
    (owner : Adr) (stor : Stor)
    (hstateHeight : s.height = Nat.toB256 height)
    (hstateNode : s.node = node) (hheight : height < 32) :
    (s.step owner stor).node =
      hashPair Bytes.sha256 ((accOfStor stor).branch height) node := by
  have hkey : s.key = branchSlot height := by
    calc
      s.key = (insertionNatState height 0 node s.keys).key := by
        unfold InsertionLoopState.key insertionNatState
        rw [hstateHeight]
      _ = branchSlot height :=
        insertionNatState_key height 0 node s.keys hheight
  rw [InsertionLoopState.step_node_eq, hstateNode, hkey,
    accOfStor_branch_of_lt stor height hheight]

private theorem insertionLoopIter_node_of_nat
    (owner : Adr) (stor : Stor) (k height : Nat) (node : B256)
    (s : InsertionLoopState)
    (hstateHeight : s.height = Nat.toB256 height)
    (hstateNode : s.node = node)
    (hheight : height + k ≤ 32) :
    (insertionLoopIter owner stor k s).node =
      accumulatedNode Bytes.sha256 (accOfStor stor).branch height k node := by
  induction k generalizing height node s with
  | zero =>
      simpa only [accumulatedNode, insertionLoopIter] using hstateNode
  | succ k ih =>
      rw [insertionLoopIter, accumulatedNode]
      exact ih (height := height + 1)
        (node := hashPair Bytes.sha256 ((accOfStor stor).branch height) node)
        (s := s.step owner stor)
        (insertionStep_height_of_nat owner stor hstateHeight (by omega))
        (insertionStep_node_of_nat owner stor hstateHeight hstateNode (by omega))
        (by omega)

theorem insertionLoopIter_node
    (owner : Adr) (stor : Stor) (k height size : Nat) (node : B256)
    (keys : KeySet) (hheight : height + k ≤ 32) :
    (insertionLoopIter owner stor k
      (insertionNatState height size node keys)).node =
        accumulatedNode Bytes.sha256 (accOfStor stor).branch
          height k node := by
  exact insertionLoopIter_node_of_nat owner stor k height node
    (insertionNatState height size node keys) rfl rfl hheight

end Blanc.BeaconDeposit
