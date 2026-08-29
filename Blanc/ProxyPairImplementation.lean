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
      Devm.setMach_error, Devm.sstoreBase_error, Devm.setMach_error]
  · rfl
  · rfl
  · rw [Devm.withOutput_state, Devm.memRead_state, Devm.setMach_state,
      Devm.setMach_state, Devm.sstoreBase_state, Devm.setMach_state]
  · rw [Devm.retPost_getStorVal]
    rw [Devm.getStorVal_setMach, Devm.getStorVal_setStorVal_self]
  · rw [Devm.retPost_transientStorage, Devm.setMach_transientStorage,
      Devm.sstoreBase_transientStorage, Devm.setMach_transientStorage]
  · rw [Devm.withOutput_logs, Devm.memRead_logs, Devm.setMach_logs,
      Devm.setMach_logs, Devm.sstoreBase_logs, Devm.setMach_logs]

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
      Devm.setMach_error, Devm.sstoreBase_error, Devm.setMach_error]
  · rfl
  · rfl
  · rw [Devm.withOutput_state, Devm.memRead_state, Devm.setMach_state,
      Devm.setMach_state, Devm.sstoreBase_state, Devm.setMach_state]
  · rw [Devm.retPost_getStorVal]
    rw [Devm.getStorVal_setMach, Devm.getStorVal_setStorVal_self]
  · rw [Devm.retPost_transientStorage, Devm.setMach_transientStorage,
      Devm.sstoreBase_transientStorage, Devm.setMach_transientStorage]
  · rw [Devm.withOutput_logs, Devm.memRead_logs, Devm.setMach_logs,
      Devm.setMach_logs, Devm.sstoreBase_logs, Devm.setMach_logs]

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

private lemma static_sstore_run
    (pc : Nat) (sevm : Sevm) (d : Devm)
    (h_static : sevm.isStatic = true)
    (h_stack : d.stack = implSlot :: 1 :: [])
    (h_stipend : gCallStipend < d.gasLeft)
    (h_cost : gasColdSload + gasStorageSet ≤ d.gasLeft)
    (h_cold : (⟨sevm.currentTarget, implSlot⟩ : Adr × B256) ∉
      d.accessedStorageKeys)
    (h_orig : getOrigStorVal sevm sevm.currentTarget implSlot = 0)
    (h_cur : Devm.getStorVal d sevm.currentTarget implSlot = 0) :
    ∃ post,
      Rinst.run ⟨pc, sevm, d⟩ .sstore =
        .error ⟨.halt (.writeInStaticContext .none), post⟩ ∧
      post.state = d.state ∧ post.transientStorage = d.transientStorage ∧
      post.logs = d.logs := by
  show ∃ post,
    (do
      let ⟨key, d⟩ ← d.pop
      let ⟨new_value, d⟩ ← d.pop
      .assert (gCallStipend < d.gasLeft) ⟨.halt (.outOfGas .none), d⟩
      let ct := sevm.currentTarget
      let original_value := getOrigStorVal sevm ct key
      let current_value := d.getStorVal ct key
      let ⟨d, gasCost2⟩ ← .ok <|
        if ((ct, key) : Adr × B256) ∉ d.accessedStorageKeys then
          (⟨addAccessedStorageKey d ct key, gasColdSload⟩ : Devm × Nat)
        else ⟨d, 0⟩
      let gasCost3 ← .ok <|
        if original_value = current_value ∧ current_value ≠ new_value then
          if original_value = 0 then gasCost2 + gasStorageSet
          else gasCost2 + (gasStorageUpdate - gasColdSload)
        else gasCost2 + gasWarmAccess
      let d ← .ok <| d.withRefundCounter
        (sstoreNewRefundCounter new_value original_value current_value d.refundCounter)
      let d ← chargeGas gasCost3 d
      assertDynamic sevm d
      .ok (d.setStorVal sevm.currentTarget key new_value)) =
      .error ⟨.halt (.writeInStaticContext .none), post⟩ ∧
      post.state = d.state ∧ post.transientStorage = d.transientStorage ∧
      post.logs = d.logs
  have h_pop : (d.setMach ⟨[1], d.memory, d.gasLeft⟩).pop =
      .ok ⟨1, d.setMach ⟨[], d.memory, d.gasLeft⟩⟩ := by rfl
  have h_if : (if (0 : B256) = 1 then gasColdSload + gasWarmAccess
      else gasColdSload + gasStorageSet) = gasColdSload + gasStorageSet := by
    decide
  let d0 := d.setMach ⟨[], d.memory, d.gasLeft⟩
  let d1 := addAccessedStorageKey d0 sevm.currentTarget implSlot
  let d2 := d1.withRefundCounter
    (sstoreNewRefundCounter 1 0 0 d1.refundCounter)
  have h_charge : chargeGas (gasColdSload + gasStorageSet) d2 =
      .ok (d2.setMach ⟨d2.stack, d2.memory,
        d.gasLeft - (gasColdSload + gasStorageSet)⟩) := by
    exact chargeGas_eq_ok h_cost
  have hd0 : Devm.WorldEq d d0 := Devm.worldEq_setMach d _
  have hd1 : Devm.WorldEq d0 d1 :=
    addAccessedStorageKey_worldEq d0 sevm.currentTarget implSlot
  have hd2 : Devm.WorldEq d1 d2 := by
    exact ⟨rfl, rfl⟩
  have hworld : Devm.WorldEq d d2 :=
    ⟨hd0.1.trans (hd1.1.trans hd2.1), hd0.2.trans (hd1.2.trans hd2.2)⟩
  have hlogs0 : d0.logs = d.logs := Devm.setMach_logs d _
  have hlogs1 : d1.logs = d0.logs := by rfl
  have hlogs2 : d2.logs = d1.logs := by rfl
  let post := d2.setMach ⟨d2.stack, d2.memory,
    d.gasLeft - (gasColdSload + gasStorageSet)⟩
  refine ⟨post, ?_, ?_, ?_, ?_⟩
  rw [Devm.pop_eq_ok h_stack]
  simp [h_pop, h_if, assertDynamic, Except.assert,
    Devm.setMach_accessedStorageKeys, Devm.getStorVal_setMach,
    h_static, h_stipend, h_cold, h_orig, h_cur, d0, d1, d2, h_charge, post]
  · rw [Devm.setMach_state]
    exact hworld.1.symm
  · rw [Devm.setMach_transientStorage]
    exact hworld.2.symm
  · rw [Devm.setMach_logs]
    exact hlogs2.trans (hlogs1.trans hlogs0)

private lemma static_sstore_step
    (pc : Nat) (sevm : Sevm) (d : Devm)
    (h_static : sevm.isStatic = true)
    (h_stack : d.stack = implSlot :: 1 :: [])
    (h_stipend : gCallStipend < d.gasLeft)
    (h_cost : gasColdSload + gasStorageSet ≤ d.gasLeft)
    (h_cold : (⟨sevm.currentTarget, implSlot⟩ : Adr × B256) ∉
      d.accessedStorageKeys)
    (h_orig : getOrigStorVal sevm sevm.currentTarget implSlot = 0)
    (h_cur : Devm.getStorVal d sevm.currentTarget implSlot = 0) :
    ∃ post,
      Ninst.StepRun pc sevm d (.reg .sstore) .none
        (.error ⟨.halt (.writeInStaticContext .none), post⟩) ∧
      post.state = d.state ∧ post.transientStorage = d.transientStorage ∧
      post.logs = d.logs := by
  obtain ⟨post, hrun, hstate, htrans, hlogs⟩ :=
    static_sstore_run pc sevm d h_static h_stack h_stipend h_cost h_cold h_orig h_cur
  refine ⟨post, ?_, hstate, htrans, hlogs⟩
  rw [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution]
  exact ⟨rfl, hrun.symm⟩

theorem implGuarded_static_sstore_halt
    (pc : Nat) (sevm : Sevm) (d : Devm)
    (h_at : Ninst.At sevm.code pc (.reg .sstore))
    (h_static : sevm.isStatic = true)
    (h_stack : d.stack = implSlot :: 1 :: [])
    (h_stipend : gCallStipend < d.gasLeft)
    (h_cost : gasColdSload + gasStorageSet ≤ d.gasLeft)
    (h_cold : (⟨sevm.currentTarget, implSlot⟩ : Adr × B256) ∉
      d.accessedStorageKeys)
    (h_orig : getOrigStorVal sevm sevm.currentTarget implSlot = 0)
    (h_cur : Devm.getStorVal d sevm.currentTarget implSlot = 0) :
    ∃ post,
      Nonempty (Exec pc sevm d
        (.error ⟨.halt (.writeInStaticContext .none), post⟩)) ∧
      exec ⟨pc, sevm, d⟩ =
        .error ⟨.halt (.writeInStaticContext .none), post⟩ ∧
      post.state = d.state ∧ post.transientStorage = d.transientStorage ∧
      post.logs = d.logs := by
  obtain ⟨post, hstep, hstate, htrans, hlogs⟩ :=
    static_sstore_step pc sevm d h_static h_stack h_stipend h_cost h_cold h_orig h_cur
  have hexec : Nonempty (Exec pc sevm d
      (.error ⟨.halt (.writeInStaticContext .none), post⟩)) :=
    Ninst.exec_of_stepRun_error h_at (show Xlot.Filled .none from trivial) hstep
  refine ⟨post, hexec, ?_, hstate, htrans, hlogs⟩
  exact (exec_iff_exec_eq pc sevm d
    (.error ⟨.halt (.writeInStaticContext .none), post⟩)).mp hexec

theorem implGuarded_static_halt_exec
    (sevm : Sevm) (base : Devm) (G : Nat)
    (h_code : sevm.code = implGuardedCode)
    (h_static : sevm.isStatic = true)
    (h_cold :
      (⟨sevm.currentTarget, implSlot⟩ : Adr × B256) ∉
        base.accessedStorageKeys)
    (h_orig :
      getOrigStorVal sevm sevm.currentTarget implSlot = 0)
    (h_cur :
      base.getStorVal sevm.currentTarget implSlot = 0)
    (h_data : Sevm.dataWord sevm 0 ≠ 0) :
    ∃ post,
      Nonempty (Exec 0 sevm
        (base.setMach ⟨[], Mem.empty,
          G + implGuardedSuccessEntryGas⟩)
        (.error ⟨.halt (.writeInStaticContext .none), post⟩)) ∧
      exec ⟨0, sevm,
        (base.setMach ⟨[], Mem.empty,
          G + implGuardedSuccessEntryGas⟩)⟩ =
        .error ⟨.halt (.writeInStaticContext .none), post⟩ ∧
      post.state = base.state ∧
      post.transientStorage = base.transientStorage ∧
      post.logs = base.logs := by
  let dEntry := base.setMach
    ⟨[], Mem.empty, G + implGuardedSuccessEntryGas⟩
  let d0 := dEntry.setMach
    {dEntry.mach with gasLeft := dEntry.gasLeft - gJumpdest}
  let d1 := d0.setMach
    ⟨[0], Mem.empty, G + 22141⟩
  let d2 := d1.setMach
    ⟨[Sevm.dataWord sevm 0], Mem.empty, G + 22138⟩
  let d3 := d2.setMach
    ⟨[0], Mem.empty, G + 22135⟩
  let d4 := d3
  let d8 := d4.setMach
    ⟨[], Mem.empty, G + implBodyGas⟩
  let d10 := d8.setMach
    ⟨[1], Mem.empty, G + 22119⟩
  let d12 := d10.setMach
    ⟨[implSlot, 1], Mem.empty, G + 22116⟩
  have hentry : Jinst.At sevm.code 0 .jumpdest := by
    rw [h_code]
    exact Jinst.at_of_slice (show List.Slice implGuardedCode.toList 0
      [Jinst.toUInt8 .jumpdest] from ⟨1, by decide +kernel⟩)
  have hpush0 : Ninst.At sevm.code 1 (Ninst.pushB256 0) := by
    rw [h_code]
    apply Ninst.at_of_slice
    show List.Slice implGuardedCode.toList 1
      (Ninst.toBytes (Ninst.pushB256 0))
    refine ⟨1, ?_⟩
    decide +kernel
  have hload : Ninst.At sevm.code 2 Ninst.calldataload := by
    rw [h_code]
    apply Ninst.at_of_slice
    show List.Slice implGuardedCode.toList 2
      (Ninst.toBytes Ninst.calldataload)
    refine ⟨1, ?_⟩
    decide +kernel
  have hiszero : Ninst.At sevm.code 3 Ninst.iszero := by
    rw [h_code]
    apply Ninst.at_of_slice
    show List.Slice implGuardedCode.toList 3
      (Ninst.toBytes Ninst.iszero)
    refine ⟨1, ?_⟩
    decide +kernel
  have hbranchPush :
      Ninst.At sevm.code 4
        (.push [((21 : Nat) >>> 8).toUInt8, (21 : Nat).toUInt8] two_le_32) := by
    rw [h_code]
    apply Ninst.at_of_slice
    show List.Slice implGuardedCode.toList 4
      (Ninst.toBytes (.push
        [((21 : Nat) >>> 8).toUInt8, (21 : Nat).toUInt8] two_le_32))
    refine ⟨3, ?_⟩
    decide +kernel
  have hjumpi : Jinst.At sevm.code 7 .jumpi := by
    rw [h_code]
    apply Jinst.at_of_slice
    exact show List.Slice implGuardedCode.toList 7
      [Jinst.toUInt8 .jumpi] from ⟨1, by decide +kernel⟩
  have hpush1 : Ninst.At sevm.code 8 (Ninst.pushB256 1) := by
    rw [h_code]
    apply Ninst.at_of_slice
    show List.Slice implGuardedCode.toList 8
      (Ninst.toBytes (Ninst.pushB256 1))
    refine ⟨2, ?_⟩
    decide +kernel
  have hpushSlot :
      Ninst.At sevm.code 10 (Ninst.pushB256 implSlot) := by
    rw [h_code]
    apply Ninst.at_of_slice
    show List.Slice implGuardedCode.toList 10
      (Ninst.toBytes (Ninst.pushB256 implSlot))
    refine ⟨2, ?_⟩
    decide +kernel
  have hsstore :
      Ninst.At sevm.code 12 (.reg .sstore) := by
    rw [h_code]
    apply Ninst.at_of_slice
    show List.Slice implGuardedCode.toList 12
      (Ninst.toBytes (.reg .sstore))
    refine ⟨1, ?_⟩
    decide +kernel
  have hEntryBurn : Devm.BurnBy gJumpdest dEntry d0 := by
    have hg : gJumpdest ≤ dEntry.gasLeft := by
      simp [dEntry, implGuardedSuccessEntryGas_eq, gJumpdest]
    have h := Devm.burnBy_setMach
      (devm := dEntry) (cost := gJumpdest) hg
    exact h
  have hEntryStep :
      Evm.step ⟨0, sevm, dEntry⟩ = .cont 1 d0 :=
    Evm.jumpdest_cont hentry hEntryBurn
  have rpush0 :=
    Ninst.runCompiled_pushB256
      (sevm := sevm) (devm := d0)
      (w := 0) (c := gBase) (G := G + 22141)
      pushCost_zero
      (by simp [d0, dEntry, implGuardedSuccessEntryGas_eq,
        gJumpdest, gBase])
      (by change ([] : List B256).length < 1024; decide)
  have rload :=
    Ninst.runCompiled_calldataload
      (sevm := sevm) (devm := d1)
      (x := 0) (v := Sevm.dataWord sevm 0) (s := [])
      (G := G + 22138)
      (by rfl) (by rfl)
      (by simp [d1, d0, dEntry, gVerylow, gJumpdest,
        implGuardedSuccessEntryGas_eq])
      (by decide)
  have riszero :=
    Ninst.runCompiled_unary
      (sevm := sevm) (devm := d2)
      (r := .iszero) (f := (B256.eqCheck · 0))
      (x := Sevm.dataWord sevm 0) (v := 0) (s := [])
      (cost := gVerylow) (G := G + 22135)
      (by rintro ⟨⟩) (by rfl) (by rfl)
      (by simp [B256.eqCheck, h_data])
      (by simp [d2, gVerylow]) (by decide)
  have rpush1 :=
    Ninst.runCompiled_pushB256
      (sevm := sevm) (devm := d8)
      (w := 1) (c := gVerylow) (G := G + 22119)
      (pushCost_of_ne_zero (by decide))
      (by simp [d8, implBodyGas_eq, gVerylow])
      (by change ([] : List B256).length < 1024; decide)
  have rpushSlot :=
    Ninst.runCompiled_pushB256
      (sevm := sevm) (devm := d10)
      (w := implSlot) (c := gVerylow) (G := G + 22116)
      (pushCost_of_ne_zero (by decide))
      (by simp [d10, gVerylow])
      (by change ([1] : List B256).length < 1024; decide)
  have hpop :=
    Devm.popBurnBy_setMach
      (devm := d4) (x := 0) (s := [])
      (cost := gVerylow + gHigh) (G := G + implBodyGas)
      (by rfl)
      (by simp [d4, d3, d2, d1, d0, dEntry,
        implBodyGas_eq, gVerylow, gHigh, gJumpdest,
        implGuardedSuccessEntryGas_eq])
  rcases Evm.branch_zero_steps
      (pc := 4) (loc := 21)
      hbranchPush hjumpi (by decide)
      (by change ([0] : List B256).length < 1024; decide) hpop with
    ⟨hBranchPushStep, hJumpiStep⟩
  rcases rpush0 with ⟨xl0, hfill0, hstep0⟩
  rcases rload with ⟨xl1, hfill1, hstep1⟩
  rcases riszero with ⟨xl2, hfill2, hstep2⟩
  rcases rpush1 with ⟨xl3, hfill3, hstep3⟩
  rcases rpushSlot with ⟨xl4, hfill4, hstep4⟩
  obtain ⟨post, h12, h12exec, hstate, htrans, hlogs⟩ :=
    implGuarded_static_sstore_halt
      12 sevm d12 hsstore h_static
      (by rfl)
      (by simp [d12, gCallStipend])
      (by simp [d12, gasColdSload, gasStorageSet])
      (by simpa [d12, d10, d8, d4, d3, d2, d1, d0, dEntry,
        Devm.setMach_accessedStorageKeys] using h_cold)
      (by simpa [d12, d10, d8, d4, d3, d2, d1, d0, dEntry] using h_orig)
      (by simpa [d12, d10, d8, d4, d3, d2, d1, d0, dEntry,
        Devm.getStorVal_setMach] using h_cur)
  obtain ⟨e12⟩ := h12
  obtain ⟨e10⟩ :=
    Ninst.exec_of_stepRun hpushSlot hfill4 (hstep4 10) ⟨e12⟩
  obtain ⟨e8⟩ :=
    Ninst.exec_of_stepRun hpush1 hfill3 (hstep3 8) ⟨e10⟩
  let finalEx : Execution :=
    .error ⟨.halt (.writeInStaticContext .none), post⟩
  have e4 : Exec 4 sevm d4 finalEx :=
    Exec.cont hBranchPushStep (Exec.cont hJumpiStep e8)
  obtain ⟨e3⟩ :=
    Ninst.exec_of_stepRun hiszero hfill2 (hstep2 3) ⟨e4⟩
  obtain ⟨e2⟩ :=
    Ninst.exec_of_stepRun hload hfill1 (hstep1 2) ⟨e3⟩
  obtain ⟨e1⟩ :=
    Ninst.exec_of_stepRun hpush0 hfill0 (hstep0 1) ⟨e2⟩
  have hexec : Nonempty (Exec 0 sevm dEntry finalEx) :=
    ⟨Exec.cont hEntryStep e1⟩
  refine ⟨post, hexec, ?_, ?_, ?_, ?_⟩
  · exact (exec_iff_exec_eq 0 sevm dEntry finalEx).mp hexec
  · simpa [d12, d10, d8, d4, d3, d2, d1, d0, dEntry,
      Devm.setMach_state] using hstate
  · simpa [d12, d10, d8, d4, d3, d2, d1, d0, dEntry,
      Devm.setMach_transientStorage] using htrans
  · simpa [d12, d10, d8, d4, d3, d2, d1, d0, dEntry,
      Devm.setMach_logs] using hlogs

end Blanc.ProxyPair
