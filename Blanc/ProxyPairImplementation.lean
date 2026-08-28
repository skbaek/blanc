import Blanc.TransientSettlement
import Blanc.ProxyPairSlots

/-!
# The scalar witness implementation for the proxy-pair family

This module is the implementation half of the proxy-pair witness.  Its
storage key is deliberately a small scalar (`7`), while the three ERC-1967
keys remain the derived words owned by `ProxyPairSlots`.  The guarded program
has one dynamic path which writes `1` and returns the word `42`, and one empty
revert path; an empty calldata word is therefore a genuine revert case.
-/

namespace Blanc.ProxyPair

open Jaune
open Jaune.Ninst Blanc.Ninst

/-! ## Program and compiled artifact -/

def implSlot : B256 := 7

def implReturnWord : B256 := 42

def implSuccess : Func :=
  pushB256 1 ::: pushB256 implSlot ::: sstore :::
    pushB256 implReturnWord ::: mstoreAt 0 +++
      pushB256 32 ::: pushB256 0 ::: Func.last .ret

def implRevert : Func :=
  pushB256 0 ::: pushB256 0 ::: Func.last .rev

def implGuarded : Func :=
  cdl 0 +++ Ninst.iszero :::
    Func.branch implSuccess implRevert

def implGuardedProg : Prog := ⟨implGuarded, []⟩

def implGuardedBytes : Bytes := (Prog.compile implGuardedProg).getD []

def implGuardedCode : ByteArray := ByteArray.mk implGuardedBytes.toArray

theorem implGuardedProg_compiles : implGuardedProg.compiles = true := by
  decide

theorem implGuardedProg_compile :
    Prog.compile implGuardedProg = some implGuardedBytes :=
  Prog.compile_eq_some_getD_of_compiles _ implGuardedProg_compiles

theorem implGuardedBytes_length : implGuardedBytes.length = 25 := by
  decide +kernel

theorem implGuardedCode_notDelegation :
    getDelegatedCodeAddress implGuardedCode = none := by
  decide +kernel

/-! ## The scalar key is outside the ERC-1967 control slots -/

theorem implSlot_ne_implementationSlot : implSlot ≠ implementationSlot := by
  rw [implementationSlot_val]
  decide

theorem implSlot_ne_adminSlot : implSlot ≠ adminSlot := by
  rw [adminSlot_val]
  decide

theorem implSlot_ne_beaconSlot : implSlot ≠ beaconSlot := by
  rw [beaconSlot_val]
  decide

theorem implementationSlot_ne_implSlot : implementationSlot ≠ implSlot :=
  implSlot_ne_implementationSlot.symm

theorem adminSlot_ne_implSlot : adminSlot ≠ implSlot :=
  implSlot_ne_adminSlot.symm

theorem beaconSlot_ne_implSlot : beaconSlot ≠ implSlot :=
  implSlot_ne_beaconSlot.symm

/-! ## Exact body and entry charges -/

def implBodyGas : Nat :=
  (gVerylow + gVerylow + (gasColdSload + gasStorageSet))
    + (gVerylow + gBase + (gVerylow + gMemory))
    + (gVerylow + gBase)

theorem implBodyGas_eq : implBodyGas = 22122 := by
  decide

def implGuardedSuccessGas : Nat := 5 + 3 + (gVerylow + gHigh) + implBodyGas

theorem implGuardedSuccessGas_eq : implGuardedSuccessGas = 22143 := by
  decide

def implGuardedRevertGas : Nat := 5 + 3 + (gVerylow + gHigh + gJumpdest) + gBase + gBase

theorem implGuardedRevertGas_eq : implGuardedRevertGas = 26 := by
  decide

/-- Whole-program charge for the nonzero guarded path, including the compiled
entry `JUMPDEST`. -/
def implGuardedSuccessEntryGas : Nat := implGuardedSuccessGas + gJumpdest

theorem implGuardedSuccessEntryGas_eq : implGuardedSuccessEntryGas = 22144 := by
  decide

/-- Whole-program charge for the zero guarded path, including the compiled
entry `JUMPDEST`. -/
def implGuardedRevertEntryGas : Nat := implGuardedRevertGas + gJumpdest

theorem implGuardedRevertEntryGas_eq : implGuardedRevertEntryGas = 27 := by
  decide

private lemma retPost_world (d : Devm) (S : List B256) (G i sz : Nat)
    (out : Bytes) :
    ((((d.setMach ⟨S, d.memory, G⟩).memRead i sz).2).withOutput out).world
      = d.world := rfl

private lemma retPost_getStorVal (d : Devm) (S : List B256) (G i sz : Nat)
    (out : Bytes) (a : Adr) (k : B256) :
    Devm.getStorVal
        ((((d.setMach ⟨S, d.memory, G⟩).memRead i sz).2).withOutput out) a k =
      d.getStorVal a k := by
  unfold Devm.getStorVal Devm.getAcct
  rw [show ((((d.setMach ⟨S, d.memory, G⟩).memRead i sz).2).withOutput out).state =
      d.state from congrArg World.state (retPost_world d S G i sz out)]

private lemma retPost_transientStorage (d : Devm) (S : List B256) (G i sz : Nat)
    (out : Bytes) :
    ((((d.setMach ⟨S, d.memory, G⟩).memRead i sz).2).withOutput out).transientStorage =
      d.transientStorage :=
  congrArg World.transientStorage (retPost_world d S G i sz out)

private lemma getStorVal_setStorVal_self (d : Devm) (a : Adr) (k v : B256) :
    (d.setStorVal a k v).getStorVal a k = v := by
  show (Devm.getStor (d.setStorVal a k v) a).get k = v
  rw [setStorVal_getStor_self, Stor.get_set_self]

private lemma sstoreBase_state (d : Devm) (t : Adr) (key : B256)
    (rc : Int) (v : B256) :
    (((addAccessedStorageKey d t key).withRefundCounter rc).setStorVal t key
      v).state = d.state.setStorVal t key v := rfl

private lemma sstoreBase_error (d : Devm) (t : Adr) (key : B256)
    (rc : Int) (v : B256) :
    (((addAccessedStorageKey d t key).withRefundCounter rc).setStorVal t key
      v).error = d.error := rfl

private lemma sstoreBase_transientStorage (d : Devm) (t : Adr) (key : B256)
    (rc : Int) (v : B256) :
    (((addAccessedStorageKey d t key).withRefundCounter rc).setStorVal t key
      v).transientStorage = d.transientStorage := rfl

private lemma sstoreBase_logs (d : Devm) (t : Adr) (key : B256)
    (rc : Int) (v : B256) :
    (((addAccessedStorageKey d t key).withRefundCounter rc).setStorVal t key
      v).logs = d.logs := rfl

/-! ## The executed success arm

The storage premises are exactly those needed to select the cold, zero-to-one
`SSTORE` price.  The result names only the changed scalar cell and the output,
so callers can add the frame projections they need without importing a
contract-specific execution theorem.
-/

theorem implSuccess_runCompiledTo (fs : List Func) (sevm : Sevm) (base : Devm)
    (G : Nat) (h_static : sevm.isStatic = false)
    (h_cold : (⟨sevm.currentTarget, implSlot⟩ : Adr × B256) ∉
      base.accessedStorageKeys)
    (h_orig : getOrigStorVal sevm sevm.currentTarget implSlot = 0)
    (h_cur : Devm.getStorVal base sevm.currentTarget implSlot = 0) :
    ∃ post,
      Func.RunCompiledTo fs sevm
          (base.setMach ⟨[], Mem.empty, G + implBodyGas⟩)
          implSuccess (.ok post) ∧
      post.error = base.error ∧
      post.output = implReturnWord.toBytes ∧
      post.gasLeft = G ∧
      post.state = base.state.setStorVal sevm.currentTarget implSlot 1 ∧
      Devm.getStorVal post sevm.currentTarget implSlot = 1 ∧
      post.transientStorage = base.transientStorage ∧
      post.logs = base.logs := by
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold implSuccess mstoreAt
    rw [implBodyGas_eq]
    func_run [22100, 3]
    case h_cost =>
      rw [Devm.getStorVal_setMach, h_orig, h_cur]
      decide
    case h_ext =>
      rw [show ((0 : B256) * 32).toNat = 0 by decide]
      exact Devm.extCost_empty_word
    case a =>
      apply Func.runCompiledTo_ret_word (i := 0) (sz := 32) (s := [])
        (e := 0) (G := G) (out := implReturnWord.toBytes)
      · rfl
      · rw [show ((0 : B256)).toNat = 0 by decide,
          show ((32 : B256)).toNat = 32 by decide,
          show ((0 : B256) * 32).toNat = 0 by decide]
        exact Devm.extCost_word_word Mem.size_write_word
      · show G + 22122 - 22122 = G + 0
        omega
      · rw [show ((0 : B256)).toNat = 0 by decide,
          show ((32 : B256)).toNat = 32 by decide]
        exact Devm.memRead_word_fst
          (by rw [show ((0 : B256) * 32).toNat = 0 by decide]; rfl)
  · rw [Devm.withOutput_error, Devm.memRead_error, Devm.setMach_error,
      Devm.setMach_error, sstoreBase_error, Devm.setMach_error]
  · rfl
  · rfl
  · rw [Devm.withOutput_state, Devm.memRead_state, Devm.setMach_state,
      Devm.setMach_state, sstoreBase_state, Devm.setMach_state]
  · rw [retPost_getStorVal]
    rw [Devm.getStorVal_setMach, getStorVal_setStorVal_self]
  · rw [retPost_transientStorage, Devm.setMach_transientStorage,
      sstoreBase_transientStorage, Devm.setMach_transientStorage]
  · rw [Devm.withOutput_logs, Devm.memRead_logs, Devm.setMach_logs,
      Devm.setMach_logs, sstoreBase_logs, Devm.setMach_logs]

/-! ## Guard selection

The two public lemmas below expose the actual branch convention: a nonzero
calldata word makes `ISZERO` produce zero and takes the fall-through write arm;
zero (including an empty calldata window) makes it produce one and takes the
jumped empty-revert arm.
-/

theorem implGuarded_runCompiledTo_nonzero
    (fs : List Func) (sevm : Sevm) (base : Devm) (G : Nat)
    (h_static : sevm.isStatic = false)
    (h_cold : (⟨sevm.currentTarget, implSlot⟩ : Adr × B256) ∉
      base.accessedStorageKeys)
    (h_orig : getOrigStorVal sevm sevm.currentTarget implSlot = 0)
    (h_cur : Devm.getStorVal base sevm.currentTarget implSlot = 0)
    (h_data : Sevm.dataWord sevm 0 ≠ 0) :
    ∃ post,
      Func.RunCompiledTo fs sevm
          (base.setMach ⟨[], Mem.empty, G + implGuardedSuccessGas⟩)
          implGuarded (.ok post) ∧
      post.error = base.error ∧
      post.output = implReturnWord.toBytes ∧
      post.gasLeft = G ∧
      post.state = base.state.setStorVal sevm.currentTarget implSlot 1 ∧
      Devm.getStorVal post sevm.currentTarget implSlot = 1 ∧
      post.transientStorage = base.transientStorage ∧
      post.logs = base.logs := by
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold implGuarded cdl
    rw [implGuardedSuccessGas_eq]
    func_run [0, 22100, 3]
    all_goals try {simp [B256.eqCheck, h_data]}
    all_goals try {rw [Devm.getStorVal_setMach, h_orig, h_cur]; decide}
    case h_ext =>
      rw [show ((0 : B256) * 32).toNat = 0 by decide]
      exact Devm.extCost_empty_word
    case a =>
      apply Func.runCompiledTo_ret_word (i := 0) (sz := 32) (s := [])
        (e := 0) (G := G) (out := implReturnWord.toBytes)
      · rfl
      · rw [show ((0 : B256)).toNat = 0 by decide,
          show ((32 : B256)).toNat = 32 by decide,
          show ((0 : B256) * 32).toNat = 0 by decide]
        exact Devm.extCost_word_word Mem.size_write_word
      · simp only [Devm.gasLeft_setMach]
        omega
      · rw [show ((0 : B256)).toNat = 0 by decide,
          show ((32 : B256)).toNat = 32 by decide]
        exact Devm.memRead_word_fst
          (by rw [show ((0 : B256) * 32).toNat = 0 by decide]; rfl)
  · rw [Devm.withOutput_error, Devm.memRead_error, Devm.setMach_error,
      Devm.setMach_error, sstoreBase_error, Devm.setMach_error]
  · rfl
  · rfl
  · rw [Devm.withOutput_state, Devm.memRead_state, Devm.setMach_state,
      Devm.setMach_state, sstoreBase_state, Devm.setMach_state]
  · rw [retPost_getStorVal]
    rw [Devm.getStorVal_setMach, getStorVal_setStorVal_self]
  · rw [retPost_transientStorage, Devm.setMach_transientStorage,
      sstoreBase_transientStorage, Devm.setMach_transientStorage]
  · rw [Devm.withOutput_logs, Devm.memRead_logs, Devm.setMach_logs,
      Devm.setMach_logs, sstoreBase_logs, Devm.setMach_logs]

theorem implGuarded_runCompiledTo_zero
    (fs : List Func) (sevm : Sevm) (base : Devm) (G : Nat)
    (h_data : Sevm.dataWord sevm 0 = 0) :
    ∃ post,
      Func.RunCompiledTo fs sevm
          (base.setMach ⟨[], Mem.empty, G + implGuardedRevertGas⟩)
          implGuarded (.error (.revert, post)) ∧
      post.error = base.error ∧
      post.output = [] ∧
      post.gasLeft = G ∧
      post.state = base.state ∧
      post.transientStorage = base.transientStorage ∧
      post.logs = base.logs := by
  let post := (base.setMach ⟨[], Mem.empty, G⟩).withOutput []
  refine ⟨post, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · unfold implGuarded cdl implRevert post
    rw [implGuardedRevertGas_eq]
    func_run [1]
    all_goals try {simp [B256.eqCheck, h_data]}
    simp only [Nat.add_sub_cancel]
    apply Func.runCompiledTo_rev (G := G)
    · rfl
    · rw [show ((0 : B256)).toNat = 0 by decide,
        Devm.extCost_empty_window]
      simp only [Devm.gasLeft_setMach, Nat.add_zero]
    · exact Devm.memRead_zero
  · rw [Devm.withOutput_error, Devm.setMach_error]
  · rw [Devm.withOutput_gasLeft, Devm.gasLeft_setMach]
  · rw [Devm.withOutput_state, Devm.setMach_state]
  · rw [Devm.withOutput_transientStorage, Devm.setMach_transientStorage]
  · rw [Devm.withOutput_logs, Devm.setMach_logs]

end Blanc.ProxyPair
