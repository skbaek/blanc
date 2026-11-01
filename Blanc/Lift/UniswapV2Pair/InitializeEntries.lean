import Blanc.Lift.UniswapV2Pair.InitializeCore
import Blanc.Lift.UniswapV2Pair.PairDispatch
import Blanc.Lift.UniswapV2Pair.GetterStringWalk
import Blanc.Lift.InvWalkDispatch
import Blanc.Lift.WalkKit
import Blanc.Lift.WalkInvKit

/-! Actual initializer decoder, selector dispatch and pc-zero STOP endpoint. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def initializeToken0 (sevm : Sevm) : Adr := (Sevm.dataWord sevm 4).toAdr
def initializeToken1 (sevm : Sevm) : Adr := (Sevm.dataWord sevm 36).toAdr
def initializePublicBase (sevm : Sevm) (b : Devm) : Devm :=
  initializeCoreBase sevm b (initializeToken0 sevm) (initializeToken1 sevm)

def initializePublicBaseH (sevm : Sevm) (b : Devm) : Devm :=
  initializeCoreBaseH sevm b (initializeToken0 sevm) (initializeToken1 sevm)

theorem initializePublicBaseH_of_covered {sevm : Sevm} (fork : CoveredFork sevm.benvStat.fork)
    (b : Devm) :
    initializePublicBaseH sevm b = initializePublicBase sevm b := by
  unfold initializePublicBaseH initializePublicBase
  simp only [initializeCoreBaseH_of_covered fork]

def initializePublicPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem) (G : Nat) : Devm :=
  St (initializePublicBase sevm b) R M G

def initializePublicPostH (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem) (G : Nat) : Devm :=
  St (initializePublicBaseH sevm b) R M G

theorem initializePublicPostH_of_covered {sevm : Sevm} (fork : CoveredFork sevm.benvStat.fork)
    (b : Devm) (R : List B256) (M : Mem) (G : Nat) :
    initializePublicPostH sevm b R M G = initializePublicPost sevm b R M G := by
  unfold initializePublicPostH initializePublicPost
  simp only [initializePublicBaseH_of_covered fork]

def initializeFactoryCharge (sevm : Sevm) (b : Devm) : Nat := sloadCost sevm b 5
def initializeLoad0Charge (sevm : Sevm) (b : Devm) : Nat :=
  sloadCost sevm (initializeFactoryBase sevm b) 6
def initializeStore0Charge (sevm : Sevm) (b : Devm) : Nat :=
  sstoreCost sevm (initializeLoaded0 sevm (initializeFactoryBase sevm b)) 6
    (initializeWord0 sevm (initializeFactoryBase sevm b) (initializeToken0 sevm))
def initializeLoad1Charge (sevm : Sevm) (b : Devm) : Nat :=
  sloadCost sevm (initializeStored0 sevm (initializeFactoryBase sevm b) (initializeToken0 sevm)) 7
def initializeStore1Charge (sevm : Sevm) (b : Devm) : Nat :=
  sstoreCost sevm (initializeLoaded1 sevm (initializeFactoryBase sevm b) (initializeToken0 sevm)) 7
    (initializeWord1 sevm (initializeFactoryBase sevm b) (initializeToken0 sevm) (initializeToken1 sevm))
def initializeStorageCharge (sevm : Sevm) (b : Devm) : Nat :=
  initializeFactoryCharge sevm b + initializeLoad0Charge sevm b + initializeStore0Charge sevm b +
    initializeLoad1Charge sevm b + initializeStore1Charge sevm b

/-- The generic STOP continuation retains the incoming output along with the entire world. -/
theorem initializeStop_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} :
    SFunc.RunExact fs sevm (St b R M (G + 1)) t_0257_c90 (.halted (St b R M G)) := by
  unfold t_0257_c90
  exact rx_dest rx_stop

theorem initializeStop_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {o : Outcome}
    (run : SFunc.Run fs sevm (St b R M G) t_0257_c90 o) :
    ∃ residual, o = .halted (St b R M residual) := by
  have h := run.cut
  unfold t_0257_c90 at h
  obtain ⟨residual, h⟩ := ric_dest h
  cases h with
  | last hr => exact ⟨residual, congrArg Outcome.halted (Except.ok.inj hr).symm⟩

/-- Both calldata address words are masked; trailing bytes and dirty high bits are allowed. -/
theorem initialize_decoder_exact {sevm : Sevm} {b : Devm} {M : Mem}
    {G : Nat} {sel avail : B256}
    (fork : CoveredFork sevm.benvStat.fork)
    (authorized : sevm.caller = (b.getStorVal sevm.currentTarget 5).toAdr)
    (sentry0 : gCallStipend < G + initializeStore0Charge sevm b + initializeLoad1Charge sevm b +
      initializeStore1Charge sevm b + 39)
    (sentry1 : gCallStipend < G + initializeStore1Charge sevm b + 9)
    (nonstatic : sevm.isStatic = false) :
    SFunc.RunExact cert.prog sevm (St b [avail, 4, 0x0257, sel] M
      (G + initializeStorageCharge sevm b + 151)) t_0434_c90
      (.halted (initializePublicPost sevm b [sel] M G)) := by
  unfold t_0434_c90
  wrun! 2
  refine rx_push (w := ~~~ addressMask) ff20_eq (by simp only [List.length_cons, List.length_nil]; decide) ?_
  wrun! 3
  refine rx_and (v := (initializeToken0 sevm).toB256)
    (addressSlotReadWord_eq_toAdr_toB256 _) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  wrun! 2
  refine rx_add' (v := 36) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_and (v := (initializeToken1 sevm).toB256)
    (by rw [B256.and_comm]; exact addressSlotReadWord_eq_toAdr_toB256 _) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x0f2c) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  rw [show G + initializeStorageCharge sevm b + 115 =
    ((G + 1) + initializeFactoryCharge sevm b + initializeLoad0Charge sevm b +
      initializeStore0Charge sevm b + initializeLoad1Charge sevm b + initializeStore1Charge sevm b + 106) + 8
    from by unfold initializeStorageCharge; omega]
  refine rx_callRet (g := t_0f2c_c45) rfl
    (initialize45_exact fork authorized rfl rfl rfl rfl rfl (by omega) (by omega) nonstatic (by simp only [List.length_cons, List.length_nil]; decide)) ?_
  exact initializeStop_exact

theorem initialize_decoder_invH {sevm : Sevm} {b : Devm} {M : Mem}
    {G : Nat} {sel avail : B256} {o : Outcome}
    (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (run : SFunc.Run cert.prog sevm (St b [avail, 4, 0x0257, sel] M G) t_0434_c90 o) :
    sevm.caller = (b.getStorVal sevm.currentTarget 5).toAdr ∧ sevm.isStatic = false ∧
      ∃ residual, o = .halted (initializePublicPostH sevm b [sel] M residual) := by
  have h := run.cut
  unfold t_0434_c90 at h
  winv 6
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := (initializeToken0 sevm).toB256) (ff20_and_word _) (ri_and hd)
  winv 2
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 36) (by decide) (ri_add hd)
  winv 1
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := (initializeToken1 sevm).toB256)
    (by rw [B256.and_comm]; exact ff20_and_word _) (ri_and hd)
  winv 1
  obtain ⟨_, call⟩ := ric_call (g := t_0f2c_c45) rfl h
  rcases call with ⟨d, core, tail⟩ | ⟨d, core, _⟩
  · obtain ⟨authorized, nonstatic, _, result⟩ := initialize45_invH stateGas bal core
    cases result
    obtain ⟨residual, done⟩ := initializeStop_inv tail.uncut
    exact ⟨authorized, nonstatic, residual, done⟩
  · obtain ⟨_, _, _, result⟩ := initialize45_invH stateGas bal core
    cases result


theorem initialize_entry_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {sel : B256}
    (fork : CoveredFork sevm.benvStat.fork)
    (guard : (64 : B256) ≤ sevm.data.length.toB256 - 4)
    (authorized : sevm.caller = (b.getStorVal sevm.currentTarget 5).toAdr)
    (sentry0 : gCallStipend < G + initializeStore0Charge sevm b + initializeLoad1Charge sevm b +
      initializeStore1Charge sevm b + 39)
    (sentry1 : gCallStipend < G + initializeStore1Charge sevm b + 9)
    (nonstatic : sevm.isStatic = false) :
    SFunc.RunExact cert.prog sevm (St b [sel] M
      (G + initializeStorageCharge sevm b + 191)) t_041e_c90
      (.halted (initializePublicPost sevm b [sel] M G)) := by
  unfold t_041e_c90
  wrun! 5
  refine rx_sub' (v := sevm.data.length.toB256 - 4) rfl
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  wrun! 2
  refine rx_lt (v := 0) (ltCheck_zero_of_le guard)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_iszero (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x0434) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_succ (by decide) ?_
  exact initialize_decoder_exact fork authorized sentry0 sentry1 nonstatic

theorem initialize_entry_invH {sevm : Sevm} {b : Devm} {M : Mem}
    {G : Nat} {sel : B256} {o : Outcome}
    (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (run : SFunc.Run cert.prog sevm (St b [sel] M G) t_041e_c90 o) :
    (64 : B256) ≤ sevm.data.length.toB256 - 4 ∧
      sevm.caller = (b.getStorVal sevm.currentTarget 5).toAdr ∧ sevm.isStatic = false ∧
      ∃ residual, o = .halted (initializePublicPostH sevm b [sel] M residual) := by
  have h := run.cut
  unfold t_041e_c90 at h
  winv 11
  rcases ric_branch h with ⟨_, _, bad⟩ | ⟨nonzero, _, h⟩
  · unfold t_0430_c90 at bad
    wskip 2
    exact (ric_revert bad).elim
  · simp only [show Bytes.toB256 [4] = (4 : B256) from rfl,
      show Bytes.toB256 [0x40] = (64 : B256) from rfl] at nonzero
    have guard : (64 : B256) ≤ sevm.data.length.toB256 - 4 := by
      by_contra ne
      have flag : B256.ltCheck (sevm.data.length.toB256 - 4) 64 = 1 := by
        simp only [B256.ltCheck, lt_of_not_ge ne, ite_true]
      rw [flag] at nonzero
      exact nonzero (by decide)
    exact ⟨guard, initialize_decoder_invH stateGas bal h.uncut⟩



theorem initialize_dispatch_exact {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x485cc955)
    (body : SFunc.RunExact cert.prog sevm (St b [0x485cc955] getterInitMemory G) t_041e_c90 o)
    (h_shifts : sevm.benvStat.rules.op.shifts = true) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + 186)) t_0000_c0 o :=
  pair_dispatch_exact value size selector (by kernel_rfl) (by decide +kernel) body h_shifts

theorem initialize_selector_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (selector : Blanc.Sevm.selector sevm = 0x485cc955)
    (run : SFunc.Run cert.prog sevm (St b [] M G) t_001a_c0 o) :
    ∃ residual, SFunc.Run cert.prog sevm (St b [0x485cc955] M residual) t_041e_c90 o :=
  pair_dispatch_inv selector (by kernel_rfl) run

theorem initialize_pc0_exact {sevm : Sevm} {b : Devm} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (value : sevm.value = 0)
    (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x485cc955)
    (guard : (64 : B256) ≤ sevm.data.length.toB256 - 4)
    (authorized : sevm.caller = (b.getStorVal sevm.currentTarget 5).toAdr)
    (sentry0 : gCallStipend < G + initializeStore0Charge sevm b + initializeLoad1Charge sevm b +
      initializeStore1Charge sevm b + 39)
    (sentry1 : gCallStipend < G + initializeStore1Charge sevm b + 9)
    (nonstatic : sevm.isStatic = false) :
    SProg.RunExact cert.prog sevm (St b [] Mem.empty (G + initializeStorageCharge sevm b + 377))
      (initializePublicPost sevm b [0x485cc955] getterInitMemory G) := by
  refine ⟨t_0000_c0, rfl, ?_⟩
  rw [show G + initializeStorageCharge sevm b + 377 =
    (G + initializeStorageCharge sevm b + 191) + 186 from by omega]
  exact initialize_dispatch_exact (h_shifts := fork.rules_shifts) value size selector
    (initialize_entry_exact fork guard authorized sentry0 sentry1 nonstatic)

theorem initialize_pc0_invH {sevm : Sevm} {b post : Devm} {G : Nat}
    (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (selector : Blanc.Sevm.selector sevm = 0x485cc955)
    (run : SProg.Run cert.prog sevm (St b [] Mem.empty G) post) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (64 : B256) ≤ sevm.data.length.toB256 - 4 ∧
      sevm.caller = (b.getStorVal sevm.currentTarget 5).toAdr ∧ sevm.isStatic = false ∧
      ∃ residual, post = initializePublicPostH sevm b [0x485cc955] getterInitMemory residual := by
  obtain ⟨f, entry, run⟩ := run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨value, size, _, run⟩ := getter_guards_inv run
  obtain ⟨_, run⟩ := initialize_selector_inv selector run
  obtain ⟨guard, authorized, nonstatic, residual, result⟩ := initialize_entry_invH stateGas bal run
  exact ⟨value, size, guard, authorized, nonstatic, residual, Outcome.halted.inj result⟩


theorem initialize_bytecode_refines_rawH {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (selector : Blanc.Sevm.selector sevm = 0x485cc955)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (64 : B256) ≤ sevm.data.length.toB256 - 4 ∧
      sevm.caller = (b.getStorVal sevm.currentTarget 5).toAdr ∧ sevm.isStatic = false ∧
      ∃ residual, post = initializePublicPostH sevm b [0x485cc955] getterInitMemory residual :=
  initialize_pc0_invH stateGas bal selector (lift_sound_noStateGas cert_check codeEq stateGas run)

theorem initialize_bytecode_refines_raw {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x485cc955)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (64 : B256) ≤ sevm.data.length.toB256 - 4 ∧
      sevm.caller = (b.getStorVal sevm.currentTarget 5).toAdr ∧ sevm.isStatic = false ∧
      ∃ residual, post = initializePublicPost sevm b [0x485cc955] getterInitMemory residual := by
  simpa only [initializePublicPostH_of_covered fork] using
    initialize_bytecode_refines_rawH codeEq fork.rules_stateGas_none fork.rules_bal_none selector run


theorem initialize_bytecode_live_raw {sevm : Sevm} {b : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x485cc955)
    (guard : (64 : B256) ≤ sevm.data.length.toB256 - 4)
    (authorized : sevm.caller = (b.getStorVal sevm.currentTarget 5).toAdr)
    (sentry0 : gCallStipend < G + initializeStore0Charge sevm b + initializeLoad1Charge sevm b +
      initializeStore1Charge sevm b + 39)
    (sentry1 : gCallStipend < G + initializeStore1Charge sevm b + 9)
    (nonstatic : sevm.isStatic = false) :
    Nonempty (Exec 0 sevm (St b [] Mem.empty (G + initializeStorageCharge sevm b + 377))
      (.ok (initializePublicPost sevm b [0x485cc955] getterInitMemory G))) :=
  lift_exact cert_check jumps_ok codeEq fork
    (initialize_pc0_exact fork value size selector guard authorized sentry0 sentry1 nonstatic)

def initializePublicStorage (sevm : Sevm) (b : Devm) : Stor :=
  ((Devm.getStor b sevm.currentTarget).set 6
    (addressSlotWriteWord (b.getStorVal sevm.currentTarget 6) (initializeToken0 sevm).toB256)).set 7
    (addressSlotWriteWord (b.getStorVal sevm.currentTarget 7) (initializeToken1 sevm).toB256)

theorem initializePublicBase_storstepH {sevm : Sevm} {b : Devm} :
    StorStep sevm b (initializePublicBaseH sevm b) (initializePublicStorage sevm b) := by
  have word0 : initializeWord0 sevm (initializeFactoryBaseH sevm b) (initializeToken0 sevm) =
      addressSlotWriteWord (b.getStorVal sevm.currentTarget 6) (initializeToken0 sevm).toB256 := by
    unfold initializeWord0 initializeFactoryBaseH
    rw [getStorVal_afterSloadH]
  have word1 : initializeWord1H sevm (initializeFactoryBaseH sevm b)
      (initializeToken0 sevm) (initializeToken1 sevm) =
      addressSlotWriteWord (b.getStorVal sevm.currentTarget 7) (initializeToken1 sevm).toB256 := by
    unfold initializeWord1H initializeStored0H initializeLoaded0H
    rw [getStorVal_afterStoreH, Stor.get_set_ne _ (by decide : (6 : B256) ≠ 7)]
    change addressSlotWriteWord ((initializeFactoryBaseH sevm b).getStorVal sevm.currentTarget 7)
      (initializeToken1 sevm).toB256 = _
    unfold initializeFactoryBaseH
    rw [getStorVal_afterSloadH]
  have walk : StorStep sevm b (initializePublicBaseH sevm b)
      (((Devm.getStor b sevm.currentTarget).set 6
        (initializeWord0 sevm (initializeFactoryBaseH sevm b) (initializeToken0 sevm))).set 7
        (initializeWord1H sevm (initializeFactoryBaseH sevm b) (initializeToken0 sevm) (initializeToken1 sevm))) :=
    (((((StorStep.refl sevm b).sloadH 5).sloadH 6).sstoreH 6
      (initializeWord0 sevm (initializeFactoryBaseH sevm b) (initializeToken0 sevm))).sloadH 7).sstoreH 7
      (initializeWord1H sevm (initializeFactoryBaseH sevm b) (initializeToken0 sevm) (initializeToken1 sevm))
  simpa only [word0, word1, initializePublicStorage] using walk

theorem initializePublicPost_storstepH {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} :
    StorStep sevm b (initializePublicPostH sevm b R M G) (initializePublicStorage sevm b) := by
  have step : StorStep sevm b (initializePublicBaseH sevm b) (initializePublicStorage sevm b) :=
    initializePublicBase_storstepH
  constructor
  · simpa only [initializePublicPostH, St, Devm.getStor, Devm.getAcct, Devm.setMach_state] using step.self
  · intro a different
    simpa only [initializePublicPostH, St, Devm.getStor, Devm.getAcct, Devm.setMach_state] using step.other a different
  · simpa only [initializePublicPostH, St, Devm.setMach_logs] using step.logs

theorem initializePublicPost_outputH {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} :
    (initializePublicPostH sevm b R M G).output = b.output := by
  rw [initializePublicPostH, St, Devm.setMach_output]
  simp only [initializePublicBaseH, initializeCoreBaseH, initializeWritesBaseH,
    initializeLoaded1H, initializeStored0H, initializeLoaded0H, initializeFactoryBaseH,
    afterSstoreH_output, afterSloadH_output]

theorem initializePublicStorage_packed {sevm : Sevm} {b : Devm} :
    ((initializePublicStorage sevm b).get 6).toAdr = initializeToken0 sevm ∧
    ((initializePublicStorage sevm b).get 7).toAdr = initializeToken1 sevm ∧
    addressMask &&& (initializePublicStorage sevm b).get 6 =
      addressMask &&& b.getStorVal sevm.currentTarget 6 ∧
    addressMask &&& (initializePublicStorage sevm b).get 7 =
      addressMask &&& b.getStorVal sevm.currentTarget 7 := by
  have slot0 : (initializePublicStorage sevm b).get 6 =
      addressSlotWriteWord (b.getStorVal sevm.currentTarget 6) (initializeToken0 sevm).toB256 := by
    unfold initializePublicStorage
    rw [Stor.get_set_ne _ (by decide : (7 : B256) ≠ 6), Stor.get_set_self]
  have slot1 : (initializePublicStorage sevm b).get 7 =
      addressSlotWriteWord (b.getStorVal sevm.currentTarget 7) (initializeToken1 sevm).toB256 := by
    unfold initializePublicStorage
    rw [Stor.get_set_self]
  have low0 := addressSlotReadWord_write_of_clean (b.getStorVal sevm.currentTarget 6)
    (initializeToken0 sevm).toB256 (addressSlotReadWord_toB256 _)
  have low1 := addressSlotReadWord_write_of_clean (b.getStorVal sevm.currentTarget 7)
    (initializeToken1 sevm).toB256 (addressSlotReadWord_toB256 _)
  rw [addressSlotReadWord_eq_toAdr_toB256] at low0 low1
  rw [slot0, slot1]
  exact ⟨by simpa only [toAdr_toB256] using congrArg B256.toAdr low0,
    by simpa only [toAdr_toB256] using congrArg B256.toAdr low1,
    addressMask_and_write_of_clean _ _ (validAdr_iff.mp (validAdr_toB256 _)),
    addressMask_and_write_of_clean _ _ (validAdr_iff.mp (validAdr_toB256 _))⟩

end Blanc.Lift.UniswapV2Pair
