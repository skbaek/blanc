import Blanc.BeaconDepositInsertFold
import Blanc.WordArithmetic

/-!
# Beacon deposit native insertion state

The small contract-specific bridge from natural heights/counts to the machine
words consumed by the compiled insertion fold.
-/

namespace Blanc.BeaconDeposit

open Jaune

def insertionNatState (height size : Nat) (node : B256)
    (keys : KeySet) : InsertionLoopState :=
  ⟨Nat.toB256 height, Nat.toB256 size, node, keys⟩

theorem insertionNatState_live_iff
    (height size : Nat) (node : B256) (keys : KeySet)
    (hsize : size < 2 ^ 256) :
    (insertionNatState height size node keys).live ↔ size % 2 = 1 := by
  unfold InsertionLoopState.live insertionNatState
  rw [one_and_toB256_eq_mod_two size hsize]
  constructor
  · intro hnz
    rcases Nat.mod_two_eq_zero_or_one size with hzero | hone
    · rw [hzero] at hnz
      exact (hnz rfl).elim
    · exact hone
  · intro hone hzero
    have hnat := congrArg B256.toNat hzero
    rw [B256.toNat_toB256_of_lt (by omega : size % 2 < 2 ^ 256)] at hnat
    simp only [hone] at hnat
    contradiction

private theorem branchBase_add_toB256_insert
    (height : Nat) (hheight : height < 32) :
    branchBase + Nat.toB256 height = branchSlot height := by
  apply B256.toNat_inj
  rw [B256.toNat_add_eq_of_nof]
  · rw [B256.toNat_toB256_of_lt (by omega : height < 2 ^ 256)]
    unfold branchSlot
    rw [B256.toNat_toB256_of_lt
      (by omega : 0x100 + height < 2 ^ 256)]
    rfl
  · unfold B256.Nof branchBase
    rw [B256.toNat_toB256_of_lt (by omega : height < 2 ^ 256)]
    change 256 + height < 2 ^ 256
    omega

theorem insertionNatState_key
    (height size : Nat) (node : B256) (keys : KeySet)
    (hheight : height < 32) :
    (insertionNatState height size node keys).key = branchSlot height := by
  unfold InsertionLoopState.key insertionNatState
  exact branchBase_add_toB256_insert height hheight

theorem insertionNatState_step
    (owner : Adr) (stor : Stor) (height size : Nat) (node : B256)
    (keys : KeySet) (hheight : height < 32) (hsize : size < 2 ^ 32) :
    (insertionNatState height size node keys).step owner stor =
      insertionNatState (height + 1) (size / 2)
        (hashPair Bytes.sha256 ((accOfStor stor).branch height) node)
        (insertionReadKeys owner keys (branchSlot height)) := by
  unfold InsertionLoopState.step
  rw [insertionNatState_key height size node keys hheight]
  unfold insertionNatState
  rw [toB256_add_one_of_lt height (by omega),
    toB256_shiftRight_one size (by omega),
    accOfStor_branch_of_lt stor height hheight]

def insertionNatKeys (owner : Adr) :
    Nat → Nat → KeySet → KeySet
  | 0, _, keys => keys
  | k + 1, height, keys =>
      insertionNatKeys owner k (height + 1)
        (insertionReadKeys owner keys (branchSlot height))

end Blanc.BeaconDeposit
