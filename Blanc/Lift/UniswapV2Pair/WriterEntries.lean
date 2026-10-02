import Blanc.Lift.UniswapV2Pair.ApproveCore
import Blanc.Lift.UniswapV2Pair.GetterStringWalk
import Blanc.Lift.InvWalkDispatch

/-! Actual public writer argument decoders and guarded entry trees. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def approveSpender (sevm : Sevm) : Adr := (Sevm.dataWord sevm 4).toAdr

def approveAmount (sevm : Sevm) : B256 := Sevm.dataWord sevm 36

def approveSlot (sevm : Sevm) : B256 :=
  mapSlot (approveSpender sevm).toB256 (mapSlot sevm.caller.toB256 2)

def approvePublicPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem) (G : Nat) : Devm :=
  getterWordPost (approveCoreBase sevm b sevm.caller (approveSpender sevm) (approveAmount sevm)) R
    ((approveScratch M sevm.caller.toB256 (approveSpender sevm).toB256).write 128
      (approveAmount sevm).toBytes) 1 G

theorem approve_decoder_exact {sevm : Sevm} {b : Devm} {M : Mem}
    {G c : Nat} {sel avail : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (cost : c = sstoreCost sevm b (approveSlot sevm) (approveAmount sevm))
    (sentry : gCallStipend < G + c + 1898) (nonstatic : sevm.isStatic = false) :
    SFunc.RunExact cert.prog sevm (St b [avail, 4, 0x034e, sel] M (G + c + 2137))
      t_032b_c96 (.halted (approvePublicPost sevm b [sel] M G)) := by
  have outmem := getterWordMemory_ptr
    (approveScratch_ptr mem sevm.caller.toB256 (approveSpender sevm).toB256) (approveAmount sevm)
  unfold t_032b_c96
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push (w := ~~~ addressMask) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_dup2 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_and (v := (approveSpender sevm).toB256)
    (by rw [B256.and_comm]; exact addressSlotReadWord_eq_toAdr_toB256 _)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_swap1 ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_add' (v := 36) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x0de5) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  have gas : G + c + 2107 = ((G + 49) + c + 2050) + 8 := by omega
  rw [gas]
  refine rx_callRet (g := t_0de5_c51) (by rfl)
    (approve51_exact fork mem cost (by omega) nonstatic
      (by simp only [List.length_cons, List.length_nil]; decide)) ?_
  exact writerBool_tail_exact outmem (by simp only [List.length_cons, List.length_nil]; decide)

theorem approve_entry_exact {sevm : Sevm} {b : Devm} {M : Mem} {G c : Nat} {sel : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (guard : (64 : B256) ≤ sevm.data.length.toB256 - 4)
    (cost : c = sstoreCost sevm b (approveSlot sevm) (approveAmount sevm))
    (sentry : gCallStipend < G + c + 1898) (nonstatic : sevm.isStatic = false) :
    SFunc.RunExact cert.prog sevm (St b [sel] M (G + c + 2177)) t_0315_c96
      (.halted (approvePublicPost sevm b [sel] M G)) := by
  unfold t_0315_c96
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
  refine rx_push (w := 0x032b) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_succ (by decide) ?_
  exact approve_decoder_exact fork mem cost sentry nonstatic

theorem approve_decoder_inv {sevm : Sevm} {b : Devm} {M : Mem}
    {G : Nat} {sel avail : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm (St b [avail, 4, 0x034e, sel] M G) t_032b_c96 o) :
    sevm.isStatic = false ∧ ∃ G', o = .halted (approvePublicPost sevm b [sel] M G') := by
  have outmem := getterWordMemory_ptr
    (approveScratch_ptr mem sevm.caller.toB256 (approveSpender sevm).toB256) (approveAmount sevm)
  have h := run.cut
  unfold t_032b_c96 at h
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
  obtain ⟨_, rfl⟩ := ri_val (w := (approveSpender sevm).toB256)
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
  obtain ⟨_, h⟩ := ric_call (g := t_0de5_c51) (by rfl) h
  rcases h with ⟨d, hc, h⟩ | ⟨d, hc, _⟩
  · obtain ⟨nonstatic, _, eq⟩ := approve51_inv fork mem hc
    cases eq
    obtain ⟨G', eq⟩ := writerBool_tail_inv outmem h.uncut
    exact ⟨nonstatic, G', eq⟩
  · obtain ⟨_, _, eq⟩ := approve51_inv fork mem hc
    cases eq

theorem approve_entry_inv {sevm : Sevm} {b : Devm} {M : Mem}
    {G : Nat} {sel : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm (St b [sel] M G) t_0315_c96 o) :
    (64 : B256) ≤ sevm.data.length.toB256 - 4 ∧ sevm.isStatic = false ∧
      ∃ G', o = .halted (approvePublicPost sevm b [sel] M G') := by
  have h := run.cut
  unfold t_0315_c96 at h
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
  · unfold t_0327_c96 at bad
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
    exact ⟨guard, approve_decoder_inv fork mem h.uncut⟩


/-- The actual pc-zero selector route for approve consumes the guarded public entry. -/
theorem approve_dispatch_exact {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (body : SFunc.RunExact cert.prog sevm (St b [0x095ea7b3] getterInitMemory G) t_0315_c96 o) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + 165)) t_0000_c0 o := by
  refine getterString_guards_exact (G := G + 102) value size ?_
  unfold t_001a_c0
  refine rx_push (w := 0) rfl (by decide) ?_
  refine rx_calldataload (by decide) ?_
  refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_shr (v := 0x095ea7b3) selector (by decide) ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x00f9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_00f9_c0
  refine rx_dest ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x23b872dd) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x0166) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0166_c0
  refine rx_dest ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x095ea7b3) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x0197) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_zero ?_
  unfold t_0172_c0
  exact cmp_hit (tgt := t_0315_c96) rfl (by rfl) body

theorem approve_selector_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (selector : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (run : SFunc.Run cert.prog sevm (St b [] M G) t_001a_c0 o) :
    ∃ G', SFunc.Run cert.prog sevm (St b [0x095ea7b3] M G') t_0315_c96 o := by
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
    show Sevm.dataWord sevm 0 >>> 224 = (0x095ea7b3 : B256) from selector] at hd
  subst d
  obtain ⟨_, h⟩ := ric_cmp_gt h
  simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0x095ea7b3 : B256)
    = (1 : B256) from by decide, show (1 : B256) ≠ 0 from by decide, ite_false] at h
  unfold t_00f9_c0 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, h⟩ := ric_cmp_gt h
  simp only [show B256.gtCheck (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd]) (0x095ea7b3 : B256)
    = (1 : B256) from by decide, show (1 : B256) ≠ 0 from by decide, ite_false] at h
  unfold t_0166_c0 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, h⟩ := ric_cmp_gt h
  simp only [show B256.gtCheck (Bytes.toB256 [0x09, 0x5e, 0xa7, 0xb3]) (0x095ea7b3 : B256)
    = (0 : B256) from by decide, ite_true] at h
  unfold t_0172_c0 at h
  obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0315_c96) (by intro bad; cases bad) (by rfl) h
  simp only [show B256.eqCheck (Bytes.toB256 [0x09, 0x5e, 0xa7, 0xb3]) (0x095ea7b3 : B256)
    = (1 : B256) from by decide, show (1 : B256) ≠ 0 from by decide, ite_false] at h
  exact ⟨_, h.uncut⟩

/-- Pc-zero liveness, with the real storage charge and incoming store sentry. -/
theorem approve_pc0_exact {sevm : Sevm} {b : Devm} {G c : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (value : sevm.value = 0)
    (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (guard : (64 : B256) ≤ sevm.data.length.toB256 - 4)
    (cost : c = sstoreCost sevm b (approveSlot sevm) (approveAmount sevm))
    (sentry : gCallStipend < G + c + 1898) (nonstatic : sevm.isStatic = false) :
    SProg.RunExact cert.prog sevm (St b [] Mem.empty (G + c + 2342))
      (approvePublicPost sevm b [0x095ea7b3] getterInitMemory G) := by
  refine ⟨t_0000_c0, rfl, ?_⟩
  have gas : G + c + 2342 = (G + c + 2177) + 165 := by omega
  rw [gas]
  exact approve_dispatch_exact value size selector
    (approve_entry_exact fork getterInitMemory_ptr guard cost sentry nonstatic)

/-- The inverse retains the entire final state and derives the real acceptance guards. -/
theorem approve_pc0_inv {sevm : Sevm} {b post : Devm} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (run : SProg.Run cert.prog sevm (St b [] Mem.empty G) post) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (64 : B256) ≤ sevm.data.length.toB256 - 4 ∧ sevm.isStatic = false ∧
      ∃ G', post = approvePublicPost sevm b [0x095ea7b3] getterInitMemory G' := by
  obtain ⟨f, entry, run⟩ := run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨value, size, _, run⟩ := getter_guards_inv run
  obtain ⟨_, run⟩ := approve_selector_inv selector run
  obtain ⟨guard, nonstatic, G', eq⟩ := approve_entry_inv fork getterInitMemory_ptr run
  exact ⟨value, size, guard, nonstatic, G', Outcome.halted.inj eq⟩

theorem approve_bytecode_refines_raw {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (64 : B256) ≤ sevm.data.length.toB256 - 4 ∧ sevm.isStatic = false ∧
      ∃ G', post = approvePublicPost sevm b [0x095ea7b3] getterInitMemory G' :=
  approve_pc0_inv fork selector (lift_sound cert_check codeEq fork run)

theorem approve_bytecode_live_raw {sevm : Sevm} {b : Devm} {G c : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (guard : (64 : B256) ≤ sevm.data.length.toB256 - 4)
    (cost : c = sstoreCost sevm b (approveSlot sevm) (approveAmount sevm))
    (sentry : gCallStipend < G + c + 1898) (nonstatic : sevm.isStatic = false) :
    Nonempty (Exec 0 sevm (St b [] Mem.empty (G + c + 2342))
      (.ok (approvePublicPost sevm b [0x095ea7b3] getterInitMemory G))) :=
  lift_exact cert_check jumps_ok codeEq fork
    (approve_pc0_exact fork value size selector guard cost sentry nonstatic)

end Blanc.Lift.UniswapV2Pair
