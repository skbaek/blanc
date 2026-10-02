import Blanc.Lift.UniswapV2Pair.TransferCore
import Blanc.Lift.UniswapV2Pair.GetterStringWalk
import Blanc.Lift.InvWalkDispatch

/-! Literal transfer decoder, guarded pc-zero route and exact boolean ABI return. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def transferRecipient (sevm : Sevm) : Adr := (Sevm.dataWord sevm 4).toAdr
def transferAmount (sevm : Sevm) : B256 := Sevm.dataWord sevm 36

def transferLoadedBase (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm b (transferBalanceSlot sevm.caller)
def transferDebitedWord (sevm : Sevm) (b : Devm) : B256 :=
  transferSourceWord sevm b sevm.caller - transferAmount sevm
def transferDebitedBase (sevm : Sevm) (b : Devm) : Devm :=
  transferDebitBase sevm (transferLoadedBase sevm b) sevm.caller (transferDebitedWord sevm b)
def transferCreditWord (sevm : Sevm) (b : Devm) : B256 :=
  transferRecipientWord sevm (transferLoadedBase sevm b) sevm.caller (transferRecipient sevm)
    (transferDebitedWord sevm b)

def transferSourceCharge (sevm : Sevm) (b : Devm) : Nat :=
  sloadCost sevm b (transferBalanceSlot sevm.caller)
def transferDebitCharge (sevm : Sevm) (b : Devm) : Nat :=
  sstoreCost sevm (transferLoadedBase sevm b) (transferBalanceSlot sevm.caller)
    (transferDebitedWord sevm b)
def transferRecipientCharge (sevm : Sevm) (b : Devm) : Nat :=
  sloadCost sevm (transferDebitedBase sevm b) (transferBalanceSlot (transferRecipient sevm))
def transferCreditCharge (sevm : Sevm) (b : Devm) : Nat :=
  sstoreCost sevm (afterSload sevm (transferDebitedBase sevm b)
    (transferBalanceSlot (transferRecipient sevm))) (transferBalanceSlot (transferRecipient sevm))
    (transferCreditWord sevm b + transferAmount sevm)
def transferCreditSafe (sevm : Sevm) (b : Devm) : Prop :=
  (transferCreditWord sevm b).toNat + (transferAmount sevm).toNat < 2 ^ 256

def transferPublicPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem) (G : Nat) : Devm :=
  getterWordPost (transferCoreBase sevm b sevm.caller (transferRecipient sevm) (transferAmount sevm)) R
    (transferCoreMemory M sevm.caller (transferRecipient sevm) (transferAmount sevm)) 1 G

theorem transferCoreMemory_ptr {M : Mem} {owner recipient : Adr} {amount : B256}
    (mem : PtrMem 128 96 M) : PtrMem 128 160 (transferCoreMemory M owner recipient amount) := by
  have m0 := transferScratch_ptr mem owner.toB256
  have m1 := transferScratch_ptr m0 owner.toB256
  have m2 := m1.write 0 recipient.toB256 (Or.inl (by decide))
  rw [show memExtSize 96 0 32 = 96 from by decide] at m2
  exact getterWordMemory_ptr (transferScratch_ptr m2 recipient.toB256) amount

theorem transfer_decoder_exact {sevm : Sevm} {b : Devm} {M : Mem}
    {G : Nat} {sel avail : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (debitSentry : gCallStipend < G + transferDebitCharge sevm b +
      transferRecipientCharge sevm b + transferCreditCharge sevm b + 2153)
    (creditSentry : gCallStipend < G + transferCreditCharge sevm b + 1913)
    (nonstatic : sevm.isStatic = false)
    (cover : transferAmount sevm ≤ transferSourceWord sevm b sevm.caller)
    (nowrap : transferCreditSafe sevm b) :
    SFunc.RunExact cert.prog sevm (St b [avail, 4, 0x034e, sel] M
      (G + transferSourceCharge sevm b + transferDebitCharge sevm b +
        transferRecipientCharge sevm b + transferCreditCharge sevm b + 2470))
      t_0574_c85 (.halted (transferPublicPost sevm b [sel] M G)) := by
  have outmem := transferCoreMemory_ptr (owner := sevm.caller)
    (recipient := transferRecipient sevm) (amount := transferAmount sevm) mem
  unfold t_0574_c85
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push (w := ~~~ addressMask) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_dup2 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_and (v := (transferRecipient sevm).toB256)
    (by rw [B256.and_comm]; exact addressSlotReadWord_eq_toAdr_toB256 _)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_swap1 ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_add' (v := 36) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x18cb) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  have gas : G + transferSourceCharge sevm b + transferDebitCharge sevm b +
      transferRecipientCharge sevm b + transferCreditCharge sevm b + 2440 =
    ((G + 49) + transferSourceCharge sevm b + transferDebitCharge sevm b +
      transferRecipientCharge sevm b + transferCreditCharge sevm b + 2383) + 8 := by omega
  rw [gas]
  refine rx_callRet (g := t_18cb_c40) rfl
    (transfer40_exact fork mem rfl rfl rfl rfl (by omega) (by omega) nonstatic cover nowrap
      (by simp only [List.length_cons, List.length_nil]; decide)) ?_
  exact writerBool_tail_exact outmem (by simp only [List.length_cons, List.length_nil]; decide)

theorem transfer_entry_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {sel : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (guard : (64 : B256) ≤ sevm.data.length.toB256 - 4)
    (debitSentry : gCallStipend < G + transferDebitCharge sevm b +
      transferRecipientCharge sevm b + transferCreditCharge sevm b + 2153)
    (creditSentry : gCallStipend < G + transferCreditCharge sevm b + 1913)
    (nonstatic : sevm.isStatic = false)
    (cover : transferAmount sevm ≤ transferSourceWord sevm b sevm.caller)
    (nowrap : transferCreditSafe sevm b) :
    SFunc.RunExact cert.prog sevm (St b [sel] M
      (G + transferSourceCharge sevm b + transferDebitCharge sevm b +
        transferRecipientCharge sevm b + transferCreditCharge sevm b + 2510)) t_055e_c85
      (.halted (transferPublicPost sevm b [sel] M G)) := by
  unfold t_055e_c85
  refine rx_dest ?_
  refine rx_push (w := 0x034e) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
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
  refine rx_push (w := 0x0574) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_succ (by decide) ?_
  exact transfer_decoder_exact fork mem debitSentry creditSentry nonstatic cover nowrap

theorem transfer_decoder_inv {sevm : Sevm} {b : Devm} {M : Mem}
    {G : Nat} {sel avail : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm (St b [avail, 4, 0x034e, sel] M G) t_0574_c85 o) :
    transferAmount sevm ≤ transferSourceWord sevm b sevm.caller ∧ sevm.isStatic = false ∧
      transferCreditSafe sevm b ∧ ∃ residual, o = .halted (transferPublicPost sevm b [sel] M residual) := by
  have outmem := transferCoreMemory_ptr (owner := sevm.caller)
    (recipient := transferRecipient sevm) (amount := transferAmount sevm) mem
  have h := run.cut
  unfold t_0574_c85 at h
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
  obtain ⟨_, rfl⟩ := ri_val (w := (transferRecipient sevm).toB256)
    (by rw [B256.and_comm]; exact ff20_and_word _) (ri_and hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 36) (by decide) (ri_add hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_calldataload hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨_, call⟩ := ric_call (g := t_18cb_c40) rfl h
  rcases call with ⟨d, core, tail⟩ | ⟨d, core, _⟩
  · obtain ⟨cover, nonstatic, nowrap, _, eq⟩ := transfer40_inv fork mem core
    cases eq
    obtain ⟨residual, result⟩ := writerBool_tail_inv outmem tail.uncut
    exact ⟨cover, nonstatic, nowrap, residual, result⟩
  · obtain ⟨_, _, _, _, eq⟩ := transfer40_inv fork mem core
    cases eq

theorem transfer_entry_inv {sevm : Sevm} {b : Devm} {M : Mem}
    {G : Nat} {sel : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm (St b [sel] M G) t_055e_c85 o) :
    (64 : B256) ≤ sevm.data.length.toB256 - 4 ∧
      transferAmount sevm ≤ transferSourceWord sevm b sevm.caller ∧ sevm.isStatic = false ∧
      transferCreditSafe sevm b ∧ ∃ residual, o = .halted (transferPublicPost sevm b [sel] M residual) := by
  have h := run.cut
  unfold t_055e_c85 at h
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
  · unfold t_0570_c85 at bad
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
    exact ⟨guard, transfer_decoder_inv fork mem h.uncut⟩

theorem transfer_dispatch_exact {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xa9059cbb)
    (body : SFunc.RunExact cert.prog sevm (St b [0xa9059cbb] getterInitMemory G) t_055e_c85 o) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + 230)) t_0000_c0 o := by
  refine getterString_guards_exact (G := G + 167) value size ?_
  unfold t_001a_c0
  refine rx_push (w := 0) rfl (by decide) ?_
  refine rx_calldataload (by decide) ?_
  refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_shr (v := 0xa9059cbb) selector (by decide) ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x00f9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_zero ?_
  unfold t_002b_c0
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0xba9a7a56) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x0097) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0097_c0
  refine rx_dest ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x7ecebe00) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x00d3) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_zero ?_
  unfold t_00a3_c0
  refine cmp_miss (by decide) ?_
  unfold t_00ae_c0
  refine cmp_miss (by decide) ?_
  unfold t_00b9_c0
  refine cmp_miss (by decide) ?_
  unfold t_00c4_c0
  exact cmp_hit (tgt := t_055e_c85) rfl rfl body

theorem transfer_selector_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (selector : Blanc.Sevm.selector sevm = 0xa9059cbb)
    (run : SFunc.Run cert.prog sevm (St b [] M G) t_001a_c0 o) :
    ∃ residual, SFunc.Run cert.prog sevm (St b [0xa9059cbb] M residual) t_055e_c85 o := by
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
    show Sevm.dataWord sevm 0 >>> 224 = (0xa9059cbb : B256) from selector] at hd
  subst d
  obtain ⟨_, h⟩ := ric_cmp_gt h
  simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0xa9059cbb : B256)
    = (0 : B256) from by decide, ite_true] at h
  unfold t_002b_c0 at h
  obtain ⟨_, h⟩ := ric_cmp_gt h
  simp only [show B256.gtCheck (Bytes.toB256 [0xba, 0x9a, 0x7a, 0x56]) (0xa9059cbb : B256)
    = (1 : B256) from by decide, show (1 : B256) ≠ 0 from by decide, ite_false] at h
  unfold t_0097_c0 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, h⟩ := ric_cmp_gt h
  simp only [show B256.gtCheck (Bytes.toB256 [0x7e, 0xce, 0xbe, 0x00]) (0xa9059cbb : B256)
    = (0 : B256) from by decide, ite_true] at h
  unfold t_00a3_c0 at h
  obtain ⟨_, h⟩ := ric_cmp_eq (g := t_04d7_c82) (by intro bad; cases bad) rfl h
  simp only [show B256.eqCheck (Bytes.toB256 [0x7e, 0xce, 0xbe, 0x00]) (0xa9059cbb : B256)
    = (0 : B256) from by decide, ite_true] at h
  unfold t_00ae_c0 at h
  obtain ⟨_, h⟩ := ric_cmp_eq (g := t_050a_c83) (by intro bad; cases bad) rfl h
  simp only [show B256.eqCheck (Bytes.toB256 [0x89, 0xaf, 0xcb, 0x44]) (0xa9059cbb : B256)
    = (0 : B256) from by decide, ite_true] at h
  unfold t_00b9_c0 at h
  obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0556_c84) (by intro bad; cases bad) rfl h
  simp only [show B256.eqCheck (Bytes.toB256 [0x95, 0xd8, 0x9b, 0x41]) (0xa9059cbb : B256)
    = (0 : B256) from by decide, ite_true] at h
  unfold t_00c4_c0 at h
  obtain ⟨_, h⟩ := ric_cmp_eq (g := t_055e_c85) (by intro bad; cases bad) rfl h
  simp only [show B256.eqCheck (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb]) (0xa9059cbb : B256)
    = (1 : B256) from by decide, show (1 : B256) ≠ 0 from by decide, ite_false] at h
  exact ⟨_, h.uncut⟩

theorem transfer_pc0_exact {sevm : Sevm} {b : Devm} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (value : sevm.value = 0)
    (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xa9059cbb)
    (guard : (64 : B256) ≤ sevm.data.length.toB256 - 4)
    (debitSentry : gCallStipend < G + transferDebitCharge sevm b +
      transferRecipientCharge sevm b + transferCreditCharge sevm b + 2153)
    (creditSentry : gCallStipend < G + transferCreditCharge sevm b + 1913)
    (nonstatic : sevm.isStatic = false)
    (cover : transferAmount sevm ≤ transferSourceWord sevm b sevm.caller)
    (nowrap : transferCreditSafe sevm b) :
    SProg.RunExact cert.prog sevm (St b [] Mem.empty
      (G + transferSourceCharge sevm b + transferDebitCharge sevm b +
        transferRecipientCharge sevm b + transferCreditCharge sevm b + 2740))
      (transferPublicPost sevm b [0xa9059cbb] getterInitMemory G) := by
  refine ⟨t_0000_c0, rfl, ?_⟩
  have gas : G + transferSourceCharge sevm b + transferDebitCharge sevm b +
      transferRecipientCharge sevm b + transferCreditCharge sevm b + 2740 =
    (G + transferSourceCharge sevm b + transferDebitCharge sevm b +
      transferRecipientCharge sevm b + transferCreditCharge sevm b + 2510) + 230 := by omega
  rw [gas]
  exact transfer_dispatch_exact value size selector
    (transfer_entry_exact fork getterInitMemory_ptr guard debitSentry creditSentry nonstatic cover nowrap)

theorem transfer_pc0_inv {sevm : Sevm} {b post : Devm} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xa9059cbb)
    (run : SProg.Run cert.prog sevm (St b [] Mem.empty G) post) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (64 : B256) ≤ sevm.data.length.toB256 - 4 ∧
      transferAmount sevm ≤ transferSourceWord sevm b sevm.caller ∧ sevm.isStatic = false ∧
      transferCreditSafe sevm b ∧
      ∃ residual, post = transferPublicPost sevm b [0xa9059cbb] getterInitMemory residual := by
  obtain ⟨f, entry, run⟩ := run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨value, size, _, run⟩ := getter_guards_inv run
  obtain ⟨_, run⟩ := transfer_selector_inv selector run
  obtain ⟨guard, cover, nonstatic, nowrap, residual, result⟩ :=
    transfer_entry_inv fork getterInitMemory_ptr run
  exact ⟨value, size, guard, cover, nonstatic, nowrap, residual, Outcome.halted.inj result⟩

theorem transfer_bytecode_refines_raw {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xa9059cbb)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (64 : B256) ≤ sevm.data.length.toB256 - 4 ∧
      transferAmount sevm ≤ transferSourceWord sevm b sevm.caller ∧ sevm.isStatic = false ∧
      transferCreditSafe sevm b ∧
      ∃ residual, post = transferPublicPost sevm b [0xa9059cbb] getterInitMemory residual :=
  transfer_pc0_inv fork selector (lift_sound cert_check codeEq fork run)

theorem transfer_bytecode_live_raw {sevm : Sevm} {b : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xa9059cbb)
    (guard : (64 : B256) ≤ sevm.data.length.toB256 - 4)
    (debitSentry : gCallStipend < G + transferDebitCharge sevm b +
      transferRecipientCharge sevm b + transferCreditCharge sevm b + 2153)
    (creditSentry : gCallStipend < G + transferCreditCharge sevm b + 1913)
    (nonstatic : sevm.isStatic = false)
    (cover : transferAmount sevm ≤ transferSourceWord sevm b sevm.caller)
    (nowrap : transferCreditSafe sevm b) :
    Nonempty (Exec 0 sevm (St b [] Mem.empty
      (G + transferSourceCharge sevm b + transferDebitCharge sevm b +
        transferRecipientCharge sevm b + transferCreditCharge sevm b + 2740))
      (.ok (transferPublicPost sevm b [0xa9059cbb] getterInitMemory G))) :=
  lift_exact cert_check jumps_ok codeEq fork
    (transfer_pc0_exact fork value size selector guard debitSentry creditSentry nonstatic cover nowrap)

end Blanc.Lift.UniswapV2Pair
