import Blanc.Lift.CursorExact
import Blanc.Lift.CursorExactLine
import Blanc.Lift.ExactWalkAddress
import Blanc.Lift.CursorOccurrence
import Blanc.Lift.UniswapV2Pair.BurnForward

/-! Exact original-bytecode cuts before Burn's first external call. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

local macro "burn_cut_nexts" : tactic =>
  `(tactic| repeat (apply SFunc.CutAt.next; focus (intro _ h; cases h; done)))

local macro "burn_stack_room" : term =>
  `(by simp only [List.length_cons, List.length_nil] <;> omega)

/-- The selected public Burn route reaches its actual internal ABI call.
The residual gas is a schedule parameter, not a premise about a reached node. -/
theorem burn_dispatch_positional_cut {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (abiSize : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : Exec 0 sevm (St b [] Mem.empty (G + 249)) (.ok post)) :
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ExecFreeUntil
        ⟨0, sevm, St b [] Mem.empty (G + 249), .ok post, run⟩ node ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ CursorOK code cert node cursor ∧
      cursor.f = .callNext 37 t_053d_c83 ∧
      node.devm = St b [0x13f5, (Sevm.dataWord sevm 4).toAdr.toB256,
        0x053d, 0x89afcb44] getterInitMemory (G + 8) := by
  have ok := cursor_start cert_check
    (F := ⟨0, sevm, St b [] Mem.empty (G + 249), .ok post, run⟩) rfl codeEq
  exact cursor_cut_exact (fs' := []) cert_check
    (f := t_0000_c0) (tgt := .callNext 37 t_053d_c83)
    (s := St b [0x13f5, (Sevm.dataWord sevm 4).toAdr.toB256,
      0x053d, 0x89afcb44] getterInitMemory (G + 8))
    (by
      unfold t_0000_c0
      burn_cut_nexts
      apply SFunc.CutAt.succ
      unfold t_0010_c0
      apply SFunc.CutAt.dest
      burn_cut_nexts
      apply SFunc.CutAt.zero
      unfold t_001a_c0
      burn_cut_nexts
      apply SFunc.CutAt.zero
      unfold t_002b_c0
      burn_cut_nexts
      apply SFunc.CutAt.succ
      unfold t_0097_c0
      apply SFunc.CutAt.dest
      burn_cut_nexts
      apply SFunc.CutAt.zero
      unfold t_00a3_c0
      burn_cut_nexts
      apply SFunc.CutAt.toZero
      unfold t_00ae_c0
      burn_cut_nexts
      apply SFunc.CutAt.toSucc rfl
      unfold t_050a_c83
      apply SFunc.CutAt.dest
      burn_cut_nexts
      apply SFunc.CutAt.succ
      unfold t_0520_c83
      apply SFunc.CutAt.dest
      burn_cut_nexts
      exact .here) ok (by rfl) rfl fork (by
      refine rx_push (w := 128) rfl burn_stack_room ?_
      refine rx_push (w := 64) rfl burn_stack_room ?_
      refine rx_mstore (c := 12) ?_ rfl ?_
      · rw [St.extCost_eq (n := 0) rfl]; decide
      refine rx_callvalue burn_stack_room ?_
      rw [value]
      refine rx_dup1 burn_stack_room ?_
      refine rx_iszero (v := 1) (by decide) burn_stack_room ?_
      refine rx_push (w := 16) rfl burn_stack_room ?_
      refine rx_branch_succ (by decide) ?_
      refine rx_dest ?_
      refine rx_pop ?_
      refine rx_push (w := 4) rfl burn_stack_room ?_
      refine rx_calldatasize burn_stack_room ?_
      refine rx_lt (v := 0) (ltCheck_zero_of_le size) burn_stack_room ?_
      refine rx_push (w := 0x01b9) rfl burn_stack_room ?_
      refine rx_branch_zero ?_
      refine rx_push (w := 0) rfl burn_stack_room ?_
      refine rx_calldataload burn_stack_room ?_
      refine rx_push (w := 224) rfl burn_stack_room ?_
      refine rx_shr (v := 0x89afcb44) selector burn_stack_room ?_
      refine rx_dup1 burn_stack_room ?_
      refine rx_push (w := 0x6a627842) rfl burn_stack_room ?_
      refine rx_gt (v := 0) (by decide) burn_stack_room ?_
      refine rx_push (w := 0xf9) rfl burn_stack_room ?_
      refine rx_branch_zero ?_
      refine rx_dup1 burn_stack_room ?_
      refine rx_push (w := 0xba9a7a56) rfl burn_stack_room ?_
      refine rx_gt (v := 1) (by decide) burn_stack_room ?_
      refine rx_push (w := 0x97) rfl burn_stack_room ?_
      refine rx_branch_succ (by decide) ?_
      refine rx_dest ?_
      refine rx_dup1 burn_stack_room ?_
      refine rx_push (w := 0x7ecebe00) rfl burn_stack_room ?_
      refine rx_gt (v := 0) (by decide) burn_stack_room ?_
      refine rx_push (w := 0xd3) rfl burn_stack_room ?_
      refine rx_branch_zero ?_
      refine rx_dup1 burn_stack_room ?_
      refine rx_push (w := 0x7ecebe00) rfl burn_stack_room ?_
      refine rx_eq (v := 0) (by decide) burn_stack_room ?_
      refine rx_push (w := 0x04d7) rfl burn_stack_room ?_
      refine rx_branch_zero ?_
      refine rx_dup1 burn_stack_room ?_
      refine rx_push (w := 0x89afcb44) rfl burn_stack_room ?_
      refine rx_eq (v := 1) (by decide) burn_stack_room ?_
      refine rx_push (w := 0x050a) rfl burn_stack_room ?_
      refine rx_branch_succ (by decide) ?_
      refine rx_dest ?_
      refine rx_push (w := 0x053d) rfl burn_stack_room ?_
      refine rx_push (w := 4) rfl burn_stack_room ?_
      refine rx_dup1 burn_stack_room ?_
      refine rx_calldatasize burn_stack_room ?_
      refine rx_sub' (v := sevm.data.length.toB256 - 4) rfl burn_stack_room ?_
      refine rx_push (w := 32) rfl burn_stack_room ?_
      refine rx_dup2 burn_stack_room ?_
      refine rx_lt (v := 0) (ltCheck_zero_of_le abiSize) burn_stack_room ?_
      refine rx_iszero (v := 1) (by decide) burn_stack_room ?_
      refine rx_push (w := 0x0520) rfl burn_stack_room ?_
      refine rx_branch_succ (by decide) ?_
      refine rx_dest ?_
      refine rx_pop ?_
      refine rx_calldataload burn_stack_room ?_
      refine rx_push (w := ~~~ addressMask) (by decide) burn_stack_room ?_
      refine rx_and (v := (Sevm.dataWord sevm 4).toAdr.toB256)
        (ff20_and_word _) burn_stack_room ?_
      refine rx_push (w := 0x13f5) rfl burn_stack_room ?_
      exact rx_stop)

/-- Burn's lock and reserve-helper staging are a real call-free prefix. -/
theorem burn_reserve_positional_cut {F : Exec.Deriv} {κ : Cursor}
    {b post : Devm} {R : List B256} {M : Mem} {G : Nat} {toWord extρ : B256}
    (ok : CursorOK code cert F κ) (tree : κ.f = t_13f5_c37)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork)
    (state : F.devm = St b (toWord :: extρ :: R) M
      (G + sstoreCost F.sevm (afterSload F.sevm b 12) 12 0 +
        sloadCost F.sevm b 12 + 51))
    (room : R.length ≤ 1008) (unlocked : b.getStorVal F.sevm.currentTarget 12 = 1)
    (nonstatic : F.sevm.isStatic = false)
    (sentry : gCallStipend < G + 9 +
      sstoreCost F.sevm (afterSload F.sevm b 12) 12 0) :
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ExecFreeUntil F node ∧ node.sevm = F.sevm ∧ node.exn = F.exn ∧
      CursorOK code cert node cursor ∧ cursor.f = .callNext 56 t_1479_c37 ∧
      node.devm = St (burnLockedWorld F.sevm b)
        (0x0d90 :: 0x1479 :: 0 :: 0 :: 0 :: 0 :: toWord :: extρ :: R) M G := by
  exact cursor_cut_exact (fs' := []) cert_check
    (f := t_13f5_c37) (tgt := .callNext 56 t_1479_c37)
    (s := St (burnLockedWorld F.sevm b)
      (0x0d90 :: 0x1479 :: 0 :: 0 :: 0 :: 0 :: toWord :: extρ :: R) M G)
    (by
      unfold t_13f5_c37
      apply SFunc.CutAt.dest
      burn_cut_nexts
      apply SFunc.CutAt.succ
      unfold t_1469_c37
      apply SFunc.CutAt.dest
      burn_cut_nexts
      exact .here) ok tree success fork (by
      rw [state]
      let load := sloadCost F.sevm b 12
      let lock := sstoreCost F.sevm (afterSload F.sevm b 12) 12 0
      rw [show G + lock + load + 51 = (G + lock + 22) + load + 29 by omega]
      refine rx_dest ?_
      refine rx_push (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
      refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
      refine rx_push (w := 12) rfl (by simp only [List.length_cons]; omega) ?_
      rw [show G + lock + 22 + load + 19 = (G + lock + 41) + load by omega]
      refine rx_sload_selC fork rfl (by simp only [List.length_cons]; omega) ?_
      refine rx_push (w := 1) rfl (by simp only [List.length_cons]; omega) ?_
      refine rx_eq (v := 1) (by rw [unlocked]; decide)
        (by simp only [List.length_cons]; omega) ?_
      refine rx_push (w := 0x1469) rfl (by simp only [List.length_cons]; omega) ?_
      refine rx_branch_succ (by decide) ?_
      refine rx_dest ?_
      refine rx_push (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
      refine rx_push (w := 12) rfl (by simp only [List.length_cons]; omega) ?_
      refine rx_dup (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
      refine rx_swap rfl ?_
      rw [show G + lock + 9 = (G + 9) + lock by omega]
      refine rx_sstoreC fork rfl sentry nonstatic ?_
      refine rx_dup (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
      refine rx_push (w := 0x1479) rfl (by simp only [List.length_cons]; omega) ?_
      refine rx_push (w := 0x0d90) rfl (by simp only [List.length_cons]; omega) ?_
      exact rx_stop)

/-- Literal original-bytecode reserve-helper line before its return. -/
def burnReserveLine : List Ninst := [
  .push [8] (by decide), .reg .sload,
  .push [255,255,255,255,255,255,255,255,255,255,255,255,255,255] (by decide),
  .reg (.dup 0), .reg (.dup 2), .reg .and, .reg (.swap 2),
  .push [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide),
  .reg (.dup 3), .reg .div, .reg (.swap 0), .reg (.swap 1), .reg .and,
  .reg (.swap 1),
  .push [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide),
  .reg (.swap 0), .reg .div, .push [255,255,255,255] (by decide),
  .reg .and, .reg (.swap 0)]

/-- The reserve helper stops at its actual return instruction, with all three
cache words and its real return tag still on the stack. -/
theorem burn_reserve_return_positional_cut {F : Exec.Deriv} {κ : Cursor}
    {b post : Devm} {R : List B256} {M : Mem} {G : Nat} {ρ : B256}
    (ok : CursorOK code cert F κ) (tree : κ.f = t_0d90_c56)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork)
    (state : F.devm = St b (ρ :: R) M (G + sloadCost F.sevm b 8 + 70))
    (room : R.length ≤ 1018) :
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ExecFreeUntil F node ∧ node.sevm = F.sevm ∧ node.exn = F.exn ∧
      CursorOK code cert node cursor ∧ cursor.f = .ret ∧
      node.devm = St (afterSload F.sevm b 8)
        (ρ :: reserveTimestampRead (b.getStorVal F.sevm.currentTarget 8) ::
          reserve1Read (b.getStorVal F.sevm.currentTarget 8) ::
          reserve0Read (b.getStorVal F.sevm.currentTarget 8) :: R) M (G + 8) ∧ cursor.K = κ.K := by
  exact cursor_dest_line_exact_cont (fs := []) cert_check ok burnReserveLine .ret
    (tree.trans (by rfl))
    (by
      intro n member x equal
      subst n
      simp only [burnReserveLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    success fork (by
      rw [state]
      let sevm := F.sevm
      let c := sloadCost sevm b 8
      refine rx_dest ?_
      refine rx_push (w := 8) rfl (by simp only [List.length_cons]; omega) ?_
      have gas : G + c + 66 = (G + 66) + c := by omega
      rw [gas]
      refine rx_sload_selC fork rfl (by simp only [List.length_cons]; omega) ?_
      refine rx_push (w := reserveMask112) rfl (by simp only [List.length_cons]; omega) ?_
      refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
      refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
      refine rx_and (v := reserve0Read _) rfl (by simp only [List.length_cons]; omega) ?_
      refine rx_swap3 ?_
      refine rx_push (w := reserveDiv112) rfl (by simp only [List.length_cons]; omega) ?_
      refine rx_dup4 (by simp only [List.length_cons]; omega) ?_
      refine rx_div rfl (by simp only [List.length_cons]; omega) ?_
      refine rx_swap1 ?_
      refine rx_swap2 ?_
      refine rx_and (v := reserve1Read _) (B256.and_comm _ _) (by simp only [List.length_cons]; omega) ?_
      refine rx_swap2 ?_
      refine rx_push (w := reserveDiv224) rfl (by simp only [List.length_cons]; omega) ?_
      refine rx_swap1 ?_
      refine rx_div rfl (by simp only [List.length_cons]; omega) ?_
      refine rx_push (w := reserveMask32) rfl (by simp only [List.length_cons]; omega) ?_
      refine rx_and (v := reserveTimestampRead (b.getStorVal sevm.currentTarget 8)) ?_ (by simp only [List.length_cons]; omega) ?_
      · exact B256.and_comm _ _
      refine rx_swap1 ?_
      exact rx_stop
    )

/-- The continuation immediately after the first initial STATICCALL. -/
def burnFirstAfterCallTree : SFunc :=
  match t_14fb_c37 with
  | .dest (.next _ (.next _ (.next _ f))) => f
  | _ => .undefined

/-- The initial request state, computed from cached storage and ABI input. -/
def burnFirstCallInput (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (G : Nat) (r1 r0 toWord extρ : B256) : Devm :=
  let mask : B256 := 0xffffffffffffffffffffffffffffffffffffffff
  let t0 := mask &&& b.getStorVal sevm.currentTarget 6
  let t1 := mask &&& (afterSload sevm b 6).getStorVal sevm.currentTarget 7
  St (temporalAccountAccessBase (burnTokensWorld sevm b) t0.toAdr)
    (G.toB256 :: t0 :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
      t0 :: 0 :: t1 :: t0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
    (balanceRequestMemory M sevm.currentTarget) G

/-- Cached reserves and token loads generate the first actual call request. -/
theorem burn_first_request_positional_cut {F : Exec.Deriv} {κ : Cursor}
    {b post : Devm} {R : List B256} {M : Mem} {G : Nat}
    {timestamp r1 r0 toWord extρ : B256}
    (ok : CursorOK code cert F κ) (tree : κ.f = t_1479_c37)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork)
    (state : F.devm = St b (timestamp :: r1 :: r0 :: 0 :: 0 :: 0 :: 0 :: toWord :: extρ :: R) M
      (G + 5 + sloadCost F.sevm b 6 + sloadCost F.sevm (afterSload F.sevm b 6) 7 +
        temporalAccountAccessCost (burnTokensWorld F.sevm b)
          ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
            b.getStorVal F.sevm.currentTarget 6).toAdr + 184))
    (mem : PtrMem 128 96 M) (room : R.length ≤ 990)
    (nonzero : ((burnTokensWorld F.sevm b).getCode
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
        b.getStorVal F.sevm.currentTarget 6).toAdr).size.toB256 ≠ 0) :
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ExecFreeUntil F node ∧ node.sevm = F.sevm ∧ node.exn = F.exn ∧
      CursorOK code cert node cursor ∧
      cursor.f = .next (.exec .staticcall) burnFirstAfterCallTree ∧
      node.devm = burnFirstCallInput F.sevm b R M G r1 r0 toWord extρ := by
  exact cursor_cut_exact (fs' := []) cert_check (f := t_1479_c37)
    (tgt := .next (.exec .staticcall) burnFirstAfterCallTree)
    (s := burnFirstCallInput F.sevm b R M G r1 r0 toWord extρ)
    (by
      unfold t_1479_c37
      apply SFunc.CutAt.dest
      burn_cut_nexts
      apply SFunc.CutAt.succ
      unfold t_14fb_c37
      apply SFunc.CutAt.dest
      burn_cut_nexts
      exact .here) ok tree success fork (by
      rw [state]
      dsimp only [burnFirstCallInput]
      let sevm := F.sevm
      let access := temporalAccountAccessCost (burnTokensWorld sevm b)
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& b.getStorVal sevm.currentTarget 6).toAdr
      have mem1 : PtrMem 128 160 (M.write 128 balanceOfSelectorWord.toBytes) :=
        mem.write 128 balanceOfSelectorWord (Or.inr (by decide))
      have mem2 : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
        balanceRequestMemory_ptr mem sevm.currentTarget
      rw [show (G + 5) + sloadCost sevm b 6 + sloadCost sevm (afterSload sevm b 6) 7 + access + 184 =
        ((((G + 5) + access + 175) + sloadCost sevm (afterSload sevm b 6) 7) + 3) + sloadCost sevm b 6 + 6
        by omega]
      apply rx_dest
      apply rx_pop
      apply rx_push (w := 6) rfl (by simp only [List.length_cons]; omega)
      apply rx_sload_selC fork rfl (by simp only [List.length_cons]; omega)
      apply rx_push (w := 7) rfl (by simp only [List.length_cons]; omega)
      apply rx_sload_selC fork rfl (by simp only [List.length_cons]; omega)
      apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
      apply rx_dup rfl (by simp only [List.length_cons]; omega)
      apply rx_mload (i := 64) (v := 128) (c := 3)
        (by rw [St.extCost_eq mem.size]; decide) mem.word (mem.read_self (by decide))
        (by simp only [List.length_cons]; omega)
      apply rx_push (w := balanceOfSelectorWord) rfl (by simp only [List.length_cons]; omega)
      apply rx_dup rfl (by simp only [List.length_cons]; omega)
      apply rx_mstore (i := 128) (v := balanceOfSelectorWord) (c := 9)
        (by rw [St.extCost_eq mem.size]; decide) rfl
      apply rx_address (by simp only [List.length_cons]; omega)
      change SFunc.RunExact [] sevm
        (St (burnTokensWorld sevm b)
          (sevm.currentTarget.toB256 :: 128 :: 64 ::
            (afterSload sevm b 6).getStorVal sevm.currentTarget 7 ::
            b.getStorVal sevm.currentTarget 6 ::
            r1 :: r0 :: 0 :: 0 :: 0 :: 0 :: toWord :: extρ :: R)
          (M.write 128 balanceOfSelectorWord.toBytes) ((G + 5) + access + 149)) _ _
      apply rx_push (w := 4) rfl (by simp only [List.length_cons]; omega)
      apply rx_dup rfl (by simp only [List.length_cons]; omega)
      apply rx_add' (v := 132) (by decide) (by simp only [List.length_cons]; omega)
      apply rx_mstore (i := 132) (v := sevm.currentTarget.toB256) (c := 6)
        (by rw [St.extCost_eq mem1.size]; decide) rfl
      apply rx_swap1
      apply rx_mload (i := 64) (v := 128) (c := 3)
        (by rw [St.extCost_eq mem2.size]; decide) mem2.word (mem2.read_self (by decide))
        (by simp only [List.length_cons]; omega)
      repeat sfw_rx
      apply rx_add' rfl (by simp only [List.length_cons]; omega)
      repeat sfw_rx
      apply rx_sub' rfl (by simp only [List.length_cons]; omega)
      apply rx_add' rfl (by simp only [List.length_cons]; omega)
      repeat sfw_rx
      rw [show (G + 5) + access + 22 = ((G + 5) + 22) + access by omega]
      rw [show Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
          255, 255, 255, 255, 255, 255, 255, 255, 255, 255] =
          (0xffffffffffffffffffffffffffffffffffffffff : B256) from rfl]
      apply rx_extcodesize fork (by simp only [List.length_cons]; omega)
      apply rx_iszero (v := 0)
        (by
          simp only [B256.eqCheck]
          exact ite_eq_right (show _ ≠ (0 : B256) from nonzero))
        (by simp only [List.length_cons]; omega)
      apply rx_dup rfl (by simp only [List.length_cons]; omega)
      apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
      apply rx_push rfl (by simp only [List.length_cons]; omega)
      apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
      simp only [show Bytes.toB256 [0] = (0 : B256) from rfl,
        show Bytes.toB256 [32] = (32 : B256) from rfl,
        show Bytes.toB256 [112, 160, 130, 49] = (0x70a08231 : B256) from rfl,
        show (128 : B256) - 128 + Bytes.toB256 [36] = 36 from by decide,
        show (128 : B256) + Bytes.toB256 [36] = 164 from by decide]
      apply rx_dest
      apply rx_pop
      apply rx_gas (by simp only [List.length_cons]; omega)
      exact rx_stop
    )

end Blanc.Lift.UniswapV2Pair
