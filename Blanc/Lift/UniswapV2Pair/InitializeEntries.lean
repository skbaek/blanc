import Blanc.Lift.UniswapV2Pair.InitializeCore
import Blanc.Lift.UniswapV2Pair.GetterStringWalk
import Blanc.Lift.InvWalkDispatch

/-! Actual initializer decoder, selector dispatch and pc-zero STOP endpoint. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def initializeToken0 (sevm : Sevm) : Adr := (Sevm.dataWord sevm 4).toAdr
def initializeToken1 (sevm : Sevm) : Adr := (Sevm.dataWord sevm 36).toAdr
def initializePublicBase (sevm : Sevm) (b : Devm) : Devm :=
  initializeCoreBase sevm b (initializeToken0 sevm) (initializeToken1 sevm)
def initializePublicPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem) (G : Nat) : Devm :=
  St (initializePublicBase sevm b) R M G

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
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push (w := ~~~ addressMask) ff20_eq (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_dup2 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_dup2 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_and (v := (initializeToken0 sevm).toB256)
    (addressSlotReadWord_eq_toAdr_toB256 _) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_swap2 ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
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

theorem initialize_decoder_inv {sevm : Sevm} {b : Devm} {M : Mem}
    {G : Nat} {sel avail : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b [avail, 4, 0x0257, sel] M G) t_0434_c90 o) :
    sevm.caller = (b.getStorVal sevm.currentTarget 5).toAdr ∧ sevm.isStatic = false ∧
      ∃ residual, o = .halted (initializePublicPost sevm b [sel] M residual) := by
  have h := run.cut
  unfold t_0434_c90 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_calldataload hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := (initializeToken0 sevm).toB256) (ff20_and_word _) (ri_and hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 36) (by decide) (ri_add hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_calldataload hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := (initializeToken1 sevm).toB256)
    (by rw [B256.and_comm]; exact ff20_and_word _) (ri_and hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨_, call⟩ := ric_call (g := t_0f2c_c45) rfl h
  rcases call with ⟨d, core, tail⟩ | ⟨d, core, _⟩
  · obtain ⟨authorized, nonstatic, _, result⟩ := initialize45_inv fork core
    cases result
    obtain ⟨residual, done⟩ := initializeStop_inv tail.uncut
    exact ⟨authorized, nonstatic, residual, done⟩
  · obtain ⟨_, _, _, result⟩ := initialize45_inv fork core
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
  refine rx_dest ?_
  refine rx_push (w := 0x0257) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 4) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_calldatasize (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_sub' (v := sevm.data.length.toB256 - 4) rfl
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 64) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_dup2 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_lt (v := 0) (ltCheck_zero_of_le guard)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_iszero (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x0434) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_succ (by decide) ?_
  exact initialize_decoder_exact fork authorized sentry0 sentry1 nonstatic

theorem initialize_entry_inv {sevm : Sevm} {b : Devm} {M : Mem}
    {G : Nat} {sel : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b [sel] M G) t_041e_c90 o) :
    (64 : B256) ≤ sevm.data.length.toB256 - 4 ∧
      sevm.caller = (b.getStorVal sevm.currentTarget 5).toAdr ∧ sevm.isStatic = false ∧
      ∃ residual, o = .halted (initializePublicPost sevm b [sel] M residual) := by
  have h := run.cut
  unfold t_041e_c90 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_calldatasize hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_sub hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_lt hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_iszero hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branch h with ⟨_, _, bad⟩ | ⟨nonzero, _, h⟩
  · unfold t_0430_c90 at bad
    obtain ⟨_, _, bad⟩ := ric_next bad
    obtain ⟨_, _, bad⟩ := ric_next bad
    exact (ric_revert bad).elim
  · simp only [show Bytes.toB256 [4] = (4 : B256) from rfl,
      show Bytes.toB256 [0x40] = (64 : B256) from rfl] at nonzero
    have guard : (64 : B256) ≤ sevm.data.length.toB256 - 4 := by
      by_contra ne
      have flag : B256.ltCheck (sevm.data.length.toB256 - 4) 64 = 1 := by
        simp only [B256.ltCheck, lt_of_not_ge ne, ite_true]
      rw [flag] at nonzero
      exact nonzero (by decide)
    exact ⟨guard, initialize_decoder_inv fork h.uncut⟩


theorem initialize_dispatch_exact {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x485cc955)
    (body : SFunc.RunExact cert.prog sevm (St b [0x485cc955] getterInitMemory G) t_041e_c90 o) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + 186)) t_0000_c0 o := by
  refine getterString_guards_exact (G := G + 123) value size ?_
  unfold t_001a_c0
  refine rx_push (w := 0) rfl (by decide) ?_
  refine rx_calldataload (by decide) ?_
  refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_shr (v := 0x485cc955) selector (by decide) ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x00f9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_00f9_c0
  refine rx_dest ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x23b872dd) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x0166) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_zero ?_
  unfold t_0105_c0
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x3644e515) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x0140) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_zero ?_
  unfold t_0110_c0
  refine cmp_miss (by decide) ?_
  unfold t_011b_c0
  exact cmp_hit (tgt := t_041e_c90) rfl rfl body

theorem initialize_selector_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (selector : Blanc.Sevm.selector sevm = 0x485cc955)
    (run : SFunc.Run cert.prog sevm (St b [] M G) t_001a_c0 o) :
    ∃ residual, SFunc.Run cert.prog sevm (St b [0x485cc955] M residual) t_041e_c90 o := by
  have h := run.cut
  unfold t_001a_c0 at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_calldataload hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_shr hd
  simp only [show Bytes.toB256 [0] = (0 : B256) from rfl,
    show Bytes.toB256 [0xe0] = (224 : B256) from rfl,
    show (224 : B256).toNat = 224 from rfl,
    show Sevm.dataWord sevm 0 >>> 224 = (0x485cc955 : B256) from selector] at hd
  subst d
  obtain ⟨_, h⟩ := ric_cmp_gt h
  simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0x485cc955 : B256)
    = (1 : B256) from by decide, show (1 : B256) ≠ 0 from by decide, ite_false] at h
  unfold t_00f9_c0 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, h⟩ := ric_cmp_gt h
  simp only [show B256.gtCheck (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd]) (0x485cc955 : B256)
    = (0 : B256) from by decide, ite_true] at h
  unfold t_0105_c0 at h
  obtain ⟨_, h⟩ := ric_cmp_gt h
  simp only [show B256.gtCheck (Bytes.toB256 [0x36, 0x44, 0xe5, 0x15]) (0x485cc955 : B256)
    = (0 : B256) from by decide, ite_true] at h
  unfold t_0110_c0 at h
  obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0416_c89) (by intro bad; cases bad) rfl h
  simp only [show B256.eqCheck (Bytes.toB256 [0x36, 0x44, 0xe5, 0x15]) (0x485cc955 : B256)
    = (0 : B256) from by decide, ite_true] at h
  unfold t_011b_c0 at h
  obtain ⟨_, h⟩ := ric_cmp_eq (g := t_041e_c90) (by intro bad; cases bad) rfl h
  simp only [show B256.eqCheck (Bytes.toB256 [0x48, 0x5c, 0xc9, 0x55]) (0x485cc955 : B256)
    = (1 : B256) from by decide, show (1 : B256) ≠ 0 from by decide, ite_false] at h
  exact ⟨_, h.uncut⟩


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
  exact initialize_dispatch_exact value size selector
    (initialize_entry_exact fork guard authorized sentry0 sentry1 nonstatic)

theorem initialize_pc0_inv {sevm : Sevm} {b post : Devm} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x485cc955)
    (run : SProg.Run cert.prog sevm (St b [] Mem.empty G) post) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (64 : B256) ≤ sevm.data.length.toB256 - 4 ∧
      sevm.caller = (b.getStorVal sevm.currentTarget 5).toAdr ∧ sevm.isStatic = false ∧
      ∃ residual, post = initializePublicPost sevm b [0x485cc955] getterInitMemory residual := by
  obtain ⟨f, entry, run⟩ := run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨value, size, _, run⟩ := getter_guards_inv run
  obtain ⟨_, run⟩ := initialize_selector_inv selector run
  obtain ⟨guard, authorized, nonstatic, residual, result⟩ := initialize_entry_inv fork run
  exact ⟨value, size, guard, authorized, nonstatic, residual, Outcome.halted.inj result⟩

theorem initialize_bytecode_refines_raw {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x485cc955)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (64 : B256) ≤ sevm.data.length.toB256 - 4 ∧
      sevm.caller = (b.getStorVal sevm.currentTarget 5).toAdr ∧ sevm.isStatic = false ∧
      ∃ residual, post = initializePublicPost sevm b [0x485cc955] getterInitMemory residual :=
  initialize_pc0_inv fork selector (lift_sound cert_check codeEq fork run)

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

/-- The exact storage image is two distinct fixed-slot updates, with no hash premise. -/
theorem initializePublicBase_storstep {sevm : Sevm} {b : Devm} :
    StorStep sevm b (initializePublicBase sevm b) (initializePublicStorage sevm b) := by
  have word0 : initializeWord0 sevm (initializeFactoryBase sevm b) (initializeToken0 sevm) =
      addressSlotWriteWord (b.getStorVal sevm.currentTarget 6) (initializeToken0 sevm).toB256 := by
    unfold initializeWord0 initializeFactoryBase
    rw [getStorVal_afterSload]
  have word1 : initializeWord1 sevm (initializeFactoryBase sevm b)
      (initializeToken0 sevm) (initializeToken1 sevm) =
      addressSlotWriteWord (b.getStorVal sevm.currentTarget 7) (initializeToken1 sevm).toB256 := by
    unfold initializeWord1 initializeStored0 initializeLoaded0
    rw [getStorVal_afterStore, Stor.get_set_ne _ (by decide : (6 : B256) ≠ 7)]
    change addressSlotWriteWord ((initializeFactoryBase sevm b).getStorVal sevm.currentTarget 7)
      (initializeToken1 sevm).toB256 = _
    unfold initializeFactoryBase
    rw [getStorVal_afterSload]
  have walk : StorStep sevm b (initializePublicBase sevm b)
      (((Devm.getStor b sevm.currentTarget).set 6
        (initializeWord0 sevm (initializeFactoryBase sevm b) (initializeToken0 sevm))).set 7
        (initializeWord1 sevm (initializeFactoryBase sevm b) (initializeToken0 sevm) (initializeToken1 sevm))) :=
    (((((StorStep.refl sevm b).sload 5).sload 6).sstore 6
      (initializeWord0 sevm (initializeFactoryBase sevm b) (initializeToken0 sevm))).sload 7).sstore 7
      (initializeWord1 sevm (initializeFactoryBase sevm b) (initializeToken0 sevm) (initializeToken1 sevm))
  simpa only [word0, word1, initializePublicStorage] using walk

theorem initializePublicPost_storstep {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} :
    StorStep sevm b (initializePublicPost sevm b R M G) (initializePublicStorage sevm b) := by
  have step : StorStep sevm b (initializePublicBase sevm b) (initializePublicStorage sevm b) :=
    initializePublicBase_storstep
  constructor
  · simpa only [initializePublicPost, St, Devm.getStor, Devm.getAcct, Devm.setMach_state] using step.self
  · intro a different
    simpa only [initializePublicPost, St, Devm.getStor, Devm.getAcct, Devm.setMach_state] using step.other a different
  · simpa only [initializePublicPost, St, Devm.setMach_logs] using step.logs

/-- STOP retains any incoming output; emptiness needs the genuine incoming-output premise. -/
theorem initializePublicPost_output {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} :
    (initializePublicPost sevm b R M G).output = b.output := by
  rw [initializePublicPost, St, Devm.setMach_output]
  simp only [initializePublicBase, initializeCoreBase, initializeWritesBase,
    initializeLoaded1, initializeStored0, initializeLoaded0, initializeFactoryBase,
    afterSstore_output, afterSload_output]

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

/-- A successful fresh frame has empty output, unchanged logs and foreign storage,
    and both assigned addresses retain the old upper ninety-six bits. -/
theorem initialize_bytecode_effects_raw {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x485cc955) (freshOutput : b.output = [])
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    StorStep sevm b post (initializePublicStorage sevm b) ∧ post.output = [] ∧
    (post.getStorVal sevm.currentTarget 6).toAdr = initializeToken0 sevm ∧
    (post.getStorVal sevm.currentTarget 7).toAdr = initializeToken1 sevm ∧
    addressMask &&& post.getStorVal sevm.currentTarget 6 = addressMask &&& b.getStorVal sevm.currentTarget 6 ∧
    addressMask &&& post.getStorVal sevm.currentTarget 7 = addressMask &&& b.getStorVal sevm.currentTarget 7 := by
  obtain ⟨_, _, _, _, _, residual, result⟩ := initialize_bytecode_refines_raw codeEq fork selector run
  have step : StorStep sevm b post (initializePublicStorage sevm b) :=
    result.symm ▸ initializePublicPost_storstep
  have output : post.output = [] := by
    rw [result, initializePublicPost_output, freshOutput]
  refine ⟨step, output, ?_⟩
  rw [step.getStorVal 6, step.getStorVal 7]
  exact initializePublicStorage_packed

end Blanc.Lift.UniswapV2Pair
