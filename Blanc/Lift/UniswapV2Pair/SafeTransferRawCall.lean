import Blanc.Lift.ReachLine
import Blanc.Lift.RunPWalk
import Blanc.Lift.UniswapV2Pair.PairTransferRequestCursor

/-! The raw source prefix of the Pair's shared transfer helper, through its
unique CALL. No enclosing success or child-settlement premise is used. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

section Raw

variable {P : Sevm → Devm → Ninst → Devm → Prop}
  (project : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
  {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {T : Conf}

include project

private theorem transfer_raw_copy_guard {src dst len : B256}
    (run : Reach P cert.prog sevm ⟨St b (src :: dst :: len :: R) M G, t_20a4_c57, []⟩ T)
    (target : AtExec T) :
    ∃ residual, Reach P cert.prog sevm
      ⟨St b (0x20e1 :: B256.ltCheck len 32 :: src :: dst :: len :: R) M residual,
        .branch t_20ad_c57 t_20e1_c57, []⟩ T := by
  unfold t_20a4_c57 at run
  obtain ⟨_, run⟩ := rr_dest run target
  change Reach _ _ _ ⟨_, pairTransferCopyGuardLine.foldr SFunc.next
    (.branch t_20ad_c57 t_20e1_c57), []⟩ T at run
  obtain ⟨d, line, run⟩ := Reach.split_nexts project pairTransferCopyGuardLine
    (by intro n member x equal; subst n; simp only [pairTransferCopyGuardLine,
        List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member) run target
  dsimp only [pairTransferCopyGuardLine] at line
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup (w := len) rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_lt step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  cases line
  exact ⟨_, run⟩

private theorem transfer_raw_copy_pass {src dst len : B256}
    (run : Reach P cert.prog sevm ⟨St b (src :: dst :: len :: R) M G, t_20a4_c57, []⟩ T)
    (target : AtExec T) (enough : ¬ len < (32 : B256)) :
    ∃ residual, Reach P cert.prog sevm
      ⟨St b ((32 + src) :: (32 + dst) :: (len + ~~~(31 : B256)) :: R)
        ((M.read src.toNat 32).2.write dst.toNat
          (Bytes.toB256 (M.read src.toNat 32).1).toBytes) residual, t_20a4_c57, []⟩ T := by
  obtain ⟨_, run⟩ := transfer_raw_copy_guard project run target
  have zero : B256.ltCheck len 32 = 0 := by simp only [B256.ltCheck, ite_eq_right enough]
  rw [zero] at run
  rcases rr_branch run target with ⟨_, _, run⟩ | ⟨nonzero, _, _⟩
  swap
  · exact (nonzero rfl).elim
  change Reach _ _ _ ⟨_, pairTransferCopyLine.foldr SFunc.next (.jump 71), []⟩ T at run
  obtain ⟨d, line, run⟩ := Reach.split_nexts project pairTransferCopyLine
    (by intro n member x equal; subst n; simp only [pairTransferCopyLine,
        List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member) run target
  obtain ⟨_, rfl⟩ := pair_transfer_copy_line_inv line
  obtain ⟨f, _, lookup, run⟩ := rr_jump run target
  have same : f = t_20a4_c57 := Option.some.inj (lookup.symm.trans rfl)
  subst f
  exact ⟨_, run⟩

private theorem transfer_raw_copy_exit {src dst len : B256}
    (run : Reach P cert.prog sevm ⟨St b (src :: dst :: len :: R) M G, t_20a4_c57, []⟩ T)
    (target : AtExec T) (short : len < (32 : B256)) :
    ∃ residual, Reach P cert.prog sevm
      ⟨St b (src :: dst :: len :: R) M residual, t_20e1_c57, []⟩ T := by
  obtain ⟨_, run⟩ := transfer_raw_copy_guard project run target
  have one : B256.ltCheck len 32 = 1 := by simp only [B256.ltCheck, ite_eq_left short]
  rw [one] at run
  rcases rr_branch run target with ⟨impossible, _, _⟩ | ⟨_, _, run⟩
  · exact ((by decide : (1 : B256) ≠ 0) impossible).elim
  · exact ⟨_, run⟩

/-- A raw reach inside `_safeTransfer`, from its supplied local entry to any
external instruction, ends at its sole CALL with the canonical seven operands
and exact 68-byte ERC20 transfer input. The helper may later fail. -/
theorem safeTransfer_raw_reach_call {p amount toWord tokenWord rho : B256} {n : Nat}
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (run : Reach P cert.prog sevm
      ⟨St b (amount :: toWord :: tokenWord :: rho :: R) M G, t_1fdb_c57, []⟩ T)
    (target : AtExec T) :
    ∃ forwarded residual,
      T = ⟨St b
        (forwarded :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 0 ::
          (p + 164) :: 68 :: (p + 164) :: 0 :: (68 + (p + 164)) ::
          (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
          96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
        (safeTransfer_dynamicCallMemory M p amount toWord) residual,
        .next (.exec .call) safeTransfer_afterCall, []⟩ ∧
      ((safeTransfer_dynamicCallMemory M p amount toWord).read (p + 164).toNat 68).1 =
        abiSelectorBytes 0xa9059cbb ++
          ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes ++ amount.toBytes := by
  unfold t_1fdb_c57 at run
  obtain ⟨_, run⟩ := rr_dest run target
  change Reach _ _ _ ⟨_, pairTransferInitializeLine.foldr SFunc.next t_20a4_c57, []⟩ T at run
  obtain ⟨d, line, run⟩ := Reach.split_nexts project pairTransferInitializeLine
    (by intro inst member x equal; subst inst; simp only [pairTransferInitializeLine,
        List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member) run target
  obtain ⟨_, rfl⟩ := pair_transfer_initialize_line_state mem lower width line
  obtain ⟨_, first⟩ := transfer_raw_copy_pass project run target (by decide : ¬ (68 : B256) < 32)
  rw [show (68 : B256) + ~~~31 = 36 from rfl] at first
  obtain ⟨_, second⟩ := transfer_raw_copy_pass project first target (by decide : ¬ (36 : B256) < 32)
  rw [show (36 : B256) + ~~~31 = 4 from rfl] at second
  obtain ⟨_, remaining⟩ := transfer_raw_copy_exit project second target (by decide : (4 : B256) < 32)
  obtain ⟨adv96, adv128, adv164, adv196, _⟩ := safeTransfer_stageAdvance width
  have read96 := safeTransfer_copyRead96 (amount := amount) (toWord := toWord) mem lower width
  have read128 := safeTransfer_copyRead128 (amount := amount) (toWord := toWord) mem lower width
  rw [read96, adv96, adv128, adv164, adv196, read128] at remaining
  unfold t_20e1_c57 at remaining
  obtain ⟨_, remaining⟩ := rr_dest remaining target
  change Reach _ _ _ ⟨_, pairTransferPartialLine.foldr SFunc.next
    (.next (.reg .gas) (.next (.exec .call) safeTransfer_afterCall)), []⟩ T at remaining
  obtain ⟨d, line, remaining⟩ := Reach.split_nexts project pairTransferPartialLine
    (by intro inst member x equal; subst inst; simp only [pairTransferPartialLine,
        List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member) remaining target
  obtain ⟨_, rfl⟩ := pair_transfer_partial_line_state mem lower width line
  obtain ⟨_, step, remaining⟩ := rr_next remaining target
  obtain ⟨forwarded, residual, rfl⟩ := ri_gas (project step)
  rcases Reach.exec remaining with rfl | ⟨d, _, tail⟩
  · exact ⟨forwarded, residual, rfl,
      safeTransfer_dynamicCall_data mem.wf lower (by omega)⟩
  · exact (Reach.false_of_execFree (E := [16, 17]) (by decide) tail target
      (by decide) (fun _ member => by cases member)).elim

end Raw

end Blanc.Lift.UniswapV2Pair
