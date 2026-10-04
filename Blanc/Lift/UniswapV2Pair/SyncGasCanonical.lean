import Blanc.Lift.UniswapV2Pair.SyncCanonical
import Blanc.Lift.UniswapV2Pair.Jumps
import Blanc.Lift.CursorExact

/-! Canonical Sync gas consumer of the accepted exact constructor. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- Cross a run of frame-free literal instructions of a cut path. -/
local macro "cut_nexts" : tactic =>
  `(tactic| repeat (apply SFunc.CutAt.next; focus (intro _ h; cases h; done)))

/-- A literal stack has room for one more word. -/
local macro "stack_room" : term =>
  `(by simp only [List.length_cons, List.length_nil] <;> omega)

/-- The actual public guards, sync selector and wrapper reach the internal
call of the callee with their complete exact state. -/
private theorem sync_dispatch_cut {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty (G + 15 + 229)) (.ok post)) :
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ExecFreeUntil ⟨0, sevm, St b [] Mem.empty (G + 15 + 229), .ok post, run⟩ node ∧
      node.sevm = sevm ∧ node.exn = .ok post ∧ CursorOK code cert node cursor ∧
      cursor.f = .callNext 31 t_0257_c78 ∧
      node.devm = St b [0x1df5, 0x0257, 0xfff6cae9] getterInitMemory (G + 8) := by
  have ok := cursor_start cert_check (F := ⟨0, sevm, St b [] Mem.empty (G + 15 + 229), .ok post, run⟩)
    rfl codeEq
  have tree : (Cursor.start cert).f = t_0000_c0 := rfl
  exact cursor_cut_exact (fs' := []) cert_check (tgt := .callNext 31 t_0257_c78)
    (s := St b [0x1df5, 0x0257, 0xfff6cae9] getterInitMemory (G + 8))
    (by
    unfold t_0000_c0
    cut_nexts
    apply SFunc.CutAt.succ
    unfold t_0010_c0
    apply SFunc.CutAt.dest
    cut_nexts
    apply SFunc.CutAt.zero
    unfold t_001a_c0
    cut_nexts
    apply SFunc.CutAt.zero
    unfold t_002b_c0
    cut_nexts
    apply SFunc.CutAt.zero
    unfold t_0036_c0
    cut_nexts
    apply SFunc.CutAt.zero
    unfold t_0041_c0
    cut_nexts
    apply SFunc.CutAt.toZero
    unfold t_004c_c0
    cut_nexts
    apply SFunc.CutAt.toZero
    unfold t_0057_c0
    cut_nexts
    apply SFunc.CutAt.toZero
    unfold t_0062_c0
    cut_nexts
    apply SFunc.CutAt.toSucc rfl
    unfold t_067b_c78
    apply SFunc.CutAt.dest
    cut_nexts
    exact .here) ok tree rfl fork (by
    refine rx_push (w := 128) rfl stack_room ?_
    refine rx_push (w := 64) rfl stack_room ?_
    refine rx_mstore (c := 12) ?_ rfl ?_
    · rw [St.extCost_eq (n := 0) rfl]; decide
    refine rx_callvalue stack_room ?_
    rw [value]
    refine rx_dup1 stack_room ?_
    refine rx_iszero (v := 1) (by decide) stack_room ?_
    refine rx_push (w := 16) rfl stack_room ?_
    refine rx_branch_succ (by decide) ?_
    refine rx_dest ?_
    refine rx_pop ?_
    refine rx_push (w := 4) rfl stack_room ?_
    refine rx_calldatasize stack_room ?_
    refine rx_lt (v := 0) (ltCheck_zero_of_le size) stack_room ?_
    refine rx_push (w := 0x01b9) rfl stack_room ?_
    refine rx_branch_zero ?_
    refine rx_push (w := 0) rfl stack_room ?_
    refine rx_calldataload stack_room ?_
    refine rx_push (w := 224) rfl stack_room ?_
    refine rx_shr (v := 0xfff6cae9) selector stack_room ?_
    refine rx_dup1 stack_room ?_
    refine rx_push (w := 0x6a627842) rfl stack_room ?_
    refine rx_gt (v := 0) (by decide) stack_room ?_
    refine rx_push (w := 0xf9) rfl stack_room ?_
    refine rx_branch_zero ?_
    refine rx_dup1 stack_room ?_
    refine rx_push (w := 0xba9a7a56) rfl stack_room ?_
    refine rx_gt (v := 0) (by decide) stack_room ?_
    refine rx_push (w := 0x97) rfl stack_room ?_
    refine rx_branch_zero ?_
    refine rx_dup1 stack_room ?_
    refine rx_push (w := 0xd21220a7) rfl stack_room ?_
    refine rx_gt (v := 0) (by decide) stack_room ?_
    refine rx_push (w := 0x71) rfl stack_room ?_
    refine rx_branch_zero ?_
    refine rx_dup1 stack_room ?_
    refine rx_push (w := 0xd21220a7) rfl stack_room ?_
    refine rx_eq (v := 0) (by decide) stack_room ?_
    refine rx_push (w := 0x05da) rfl stack_room ?_
    refine rx_branch_zero ?_
    refine rx_dup1 stack_room ?_
    refine rx_push (w := 0xd505accf) rfl stack_room ?_
    refine rx_eq (v := 0) (by decide) stack_room ?_
    refine rx_push (w := 0x05e2) rfl stack_room ?_
    refine rx_branch_zero ?_
    refine rx_dup1 stack_room ?_
    refine rx_push (w := 0xdd62ed3e) rfl stack_room ?_
    refine rx_eq (v := 0) (by decide) stack_room ?_
    refine rx_push (w := 0x0640) rfl stack_room ?_
    refine rx_branch_zero ?_
    refine rx_dup1 stack_room ?_
    refine rx_push (w := 0xfff6cae9) rfl stack_room ?_
    refine rx_eq (v := 1) (by decide) stack_room ?_
    refine rx_push (w := 0x067b) rfl stack_room ?_
    refine rx_branch_succ (by decide) ?_
    refine rx_dest ?_
    refine rx_push (w := 0x0257) rfl stack_room ?_
    refine rx_push (w := 0x1df5) rfl stack_room ?_
    exact rx_stop)

/-- The literal suffix after each balance call's STATICCALL. -/
def SyncBalanceSite.afterCallTree (site : SyncBalanceSite) : SFunc :=
  match site.callTree with
  | .dest (.next _ (.next _ (.next _ rest))) => rest
  | _ => .undefined

/-- The cut lock guard: its slot-12 read and the unlocked arm. -/
private theorem syncLockGuard_cut_rx {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G load : Nat} {tag : B256} {tail : SFunc} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (room : R.length ≤ 1010)
    (unlocked : b.getStorVal sevm.currentTarget 12 = 1)
    (charge : load = sloadCost sevm b 12)
    (body : SFunc.RunExact fs sevm (St (afterSload sevm b 12) (tag :: R) M G) tail o) :
    SFunc.RunExact fs sevm (St b (tag :: R) M (G + load + 23))
      (.dest (.next (.push [0x0c] (by decide)) (.next (.reg .sload)
        (.next (.push [0x01] (by decide)) (.next (.reg .eq)
          (.next (.push [0x1e, 0x66] (by decide)) (.branch .undefined tail))))))) o := by
  apply rx_dest
  apply rx_push (w := 12) rfl (by simp only [List.length_cons]; omega)
  rw [show G + load + 19 = (G + 19) + load by omega]
  apply rx_sload_selC fork charge (by simp only [List.length_cons]; omega)
  apply rx_push (w := 1) rfl (by simp only [List.length_cons]; omega)
  apply rx_eq (v := 1) (by rw [unlocked]; decide) (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x1e66) rfl (by simp only [List.length_cons]; omega)
  exact rx_branch_succ (by decide : (1 : B256) ≠ 0) body

/-- The cut first request: lock write, token0 read and overlapping request. -/
private theorem syncFirstRequest_cut_rx {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G load : Nat} {tag : B256} {tail : SFunc} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (room : R.length ≤ 1010) (static : sevm.isStatic = false)
    (charge : load = sloadCost sevm (afterSstore sevm b 12 0) 6)
    (sentry : gCallStipend < G + load + 119 + sstoreCost sevm b 12 0)
    (body : SFunc.RunExact fs sevm
      (St (afterSload sevm (afterSstore sevm b 12 0) 6)
        (((afterSstore sevm b 12 0).getStorVal sevm.currentTarget 6).toAdr.toB256 ::
         ((afterSstore sevm b 12 0).getStorVal sevm.currentTarget 6).toAdr.toB256 ::
         128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
         ((afterSstore sevm b 12 0).getStorVal sevm.currentTarget 6).toAdr.toB256 ::
         0x1fd4 :: tag :: R)
        (balanceRequestMemory M sevm.currentTarget) G) tail o) :
    SFunc.RunExact fs sevm (St b (tag :: R) M (G + sstoreCost sevm b 12 0 + load + 126))
      (.dest (syncFirstRequestLine.foldr SFunc.next tail)) o := by
  have mem1 : PtrMem 128 160 (M.write 128 balanceOfSelectorWord.toBytes) :=
    mem.write 128 balanceOfSelectorWord (Or.inr (by decide))
  have mem2 : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
    balanceRequestMemory_ptr mem sevm.currentTarget
  apply rx_dest
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 12) rfl (by simp only [List.length_cons]; omega)
  rw [show G + sstoreCost sevm b 12 0 + load + 119 =
    (G + load + 119) + sstoreCost sevm b 12 0 by omega]
  apply rx_sstore fork sentry static
  apply rx_push (w := 6) rfl (by simp only [List.length_cons]; omega)
  rw [show G + load + 116 = (G + 116) + load by omega]
  apply rx_sload_selC fork charge (by simp only [List.length_cons]; omega)
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mload (i := 64) (v := 128) (c := 3)
    (by rw [St.extCost_eq mem.size]; decide) mem.word
    (mem.read_self (by decide)) (by simp only [List.length_cons]; omega)
  apply rx_push (w := balanceOfSelectorWord) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mstore (i := 128) (v := balanceOfSelectorWord) (c := 9)
    (by rw [St.extCost_eq mem.size]; decide) rfl
  refine .next (Ninst.runCompiled_pushItem (G := G + 90) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl (by simp only [St.stack, List.length_cons]; omega)) ?_
  change SFunc.RunExact fs sevm
    (St (afterSload sevm (afterSstore sevm b 12 0) 6)
      (sevm.currentTarget.toB256 :: 128 :: 64 ::
       (afterSstore sevm b 12 0).getStorVal sevm.currentTarget 6 :: tag :: R)
      (M.write 128 balanceOfSelectorWord.toBytes) (G + 90)) _ o
  apply rx_push (w := 4) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 132) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_mstore (i := 132) (v := sevm.currentTarget.toB256) (c := 6)
    (by rw [St.extCost_eq mem1.size]; decide) rfl
  apply rx_swap1
  apply rx_mload (i := 64) (v := 128) (c := 3)
    (by rw [St.extCost_eq mem2.size]; decide) mem2.word
    (mem2.read_self (by decide)) (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x1fd4) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_push (w := ~~~ addressMask) ff20_eq (by simp only [List.length_cons]; omega)
  apply rx_and (addressSlotReadWord_eq_toAdr_toB256 _) (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_push (w := 0x70a08231) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_push (w := 36) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 164) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_swap2
  apply rx_swap1
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_sub' (v := 0) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 36) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  exact body

/-- The cut code guard and call prefix of either balance site stop at its
STATICCALL with the requested gas word on top. -/
private theorem syncCodeGuardCall_cut_rx {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {S : List B256} {M : Mem} {callGas : Nat} {token : B256}
    (site : SyncBalanceSite) (fork : CoveredFork sevm.benvStat.fork)
    (room : S.length ≤ 1021) (nonzero : (b.getCode token.toAdr).size.toB256 ≠ 0) :
    SFunc.RunExact fs sevm
      (St b (token :: S) M (callGas + 5 + 22 + temporalAccountAccessCost b token.toAdr))
      (syncCodeGuardLine.foldr SFunc.next
        (.next (.push site.codeDestination (by cases site <;> decide))
          (.branch .undefined (.dest (.next (.reg .pop) (.next (.reg .gas) (.last .stop)))))))
      (.halted (St (temporalAccountAccessBase b token.toAdr) (callGas.toB256 :: S) M callGas)) := by
  apply rx_extcodesize fork (by omega)
  have zero : B256.eqCheck (b.getCode token.toAdr).size.toB256 0 = 0 := by
    simp only [B256.eqCheck, nonzero, ite_false]
  apply rx_iszero zero (by omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
  cases site
  · apply rx_push (w := 0x1edd) rfl (by simp only [List.length_cons]; omega)
    apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
    apply rx_dest
    apply rx_pop
    apply rx_gas (by omega)
    exact rx_stop
  · apply rx_push (w := 0x1f7a) rfl (by simp only [List.length_cons]; omega)
    apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
    apply rx_dest
    apply rx_pop
    apply rx_gas (by omega)
    exact rx_stop

/-- The first actual request state before its STATICCALL. -/
def syncFirstCallInput (sevm : Sevm) (b : Devm) (callGas0 : Nat) : Devm :=
  St (temporalAccountAccessBase (syncFirstWorld sevm b) (syncFirstToken sevm b).toAdr)
    (callGas0.toB256 :: (syncFirstToken sevm b) :: 128 :: 36 :: 128 :: 32 :: 164 ::
      0x70a08231 :: (syncFirstToken sevm b) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
    (balanceRequestMemory getterInitMemory sevm.currentTarget) callGas0

/-- The callee's lock guard, lock write, token0 read, request and code guard
reach the first STATICCALL with its complete exact state. -/
private theorem sync_first_call_cut {sevm : Sevm} {b post : Devm} {callGas0 : Nat}
    {F : Exec.Deriv} {κ : Cursor} (ok : CursorOK code cert F κ) (tree : κ.f = t_1df5_c31)
    (success : F.exn = .ok post) (sameSevm : F.sevm = sevm)
    (state : F.devm = St b [0x0257, 0xfff6cae9] getterInitMemory
      (syncCalleePrefixGas sevm b callGas0))
    (fork : CoveredFork sevm.benvStat.fork)
    (static : sevm.isStatic = false) (unlocked : b.getStorVal sevm.currentTarget 12 = 1)
    (sentry : gCallStipend <
      (callGas0 + 5 + 22 + temporalAccountAccessCost (syncFirstWorld sevm b)
        (syncFirstToken sevm b).toAdr) + sloadCost sevm (syncLockedWorld sevm b) 6 + 119 +
      sstoreCost sevm (afterSload sevm b 12) 12 0)
    (nonzero0 : ((syncFirstWorld sevm b).getCode (syncFirstToken sevm b).toAdr).size.toB256 ≠ 0) :
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ExecFreeUntil F node ∧ node.sevm = sevm ∧ node.exn = .ok post ∧
      CursorOK code cert node cursor ∧
      cursor.f = .next (.exec .staticcall) SyncBalanceSite.first.afterCallTree ∧
      node.devm = syncFirstCallInput sevm b callGas0 := by
  subst sameSevm
  obtain ⟨node, cursor, span, nodeSevm, nodeExn, placed, nodeTree, nodeState⟩ :=
    cursor_cut_exact (fs' := []) cert_check
      (tgt := .next (.exec .staticcall) SyncBalanceSite.first.afterCallTree)
      (s := syncFirstCallInput F.sevm b callGas0)
      (by
      unfold t_1df5_c31
      apply SFunc.CutAt.dest
      cut_nexts
      apply SFunc.CutAt.succ
      unfold t_1e66_c31
      apply SFunc.CutAt.dest
      cut_nexts
      apply SFunc.CutAt.succ
      unfold t_1edd_c31
      apply SFunc.CutAt.dest
      cut_nexts
      exact .here) ok tree success fork (by
      rw [state]
      unfold syncCalleePrefixGas
      exact syncLockGuard_cut_rx fork stack_room unlocked rfl
        (syncFirstRequest_cut_rx fork getterInitMemory_ptr stack_room static rfl sentry
          (syncCodeGuardCall_cut_rx .first fork stack_room nonzero0)))
  exact ⟨node, cursor, span, nodeSevm, nodeExn.trans success, placed, nodeTree, nodeState⟩

/-- The cut first reply: success flag, full-width guard and decoder. -/
private theorem syncFirstReply_cut_rx {fs : List SFunc} {sevm : Sevm} {d : Devm}
    {R : List B256} {M : Mem} {G : Nat} {x y z : B256} {tail : SFunc} {o : Outcome}
    (mem : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget)) (wf : Mem.Wf M)
    (room : R.length ≤ 1015)
    (bound : d.returnData.length < 2 ^ 256) (long : 32 ≤ d.returnData.length)
    (body : SFunc.RunExact fs sevm
      (St d (Bytes.toB256 (d.returnData.take 32) :: R)
        (balanceReplyMemory M sevm.currentTarget d.returnData) G) tail o) :
    SFunc.RunExact fs sevm
      (St d (1 :: x :: y :: z :: R) (balanceReplyMemory M sevm.currentTarget d.returnData)
        (G + 70))
      (.next (.reg .iszero) (.next (.reg (.dup 0)) (.next (.reg .iszero)
        (.next (.push [0x1e, 0xf1] (by decide)) (.branch .undefined
          (.dest (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .pop)
            (.next (.push [0x40] (by decide)) (.next (.reg .mload) (.next (.reg .returndatasize)
              (.next (.push [0x20] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt)
                (.next (.reg .iszero) (.next (.push [0x1f, 0x07] (by decide))
                  (.branch .undefined
                    (.dest (.next (.reg .pop) (.next (.reg .mload) tail))))))))))))))))))))))
      o := by
  have reply := balanceReplyMemory_ptr d.returnData mem
  apply rx_iszero (v := 0) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
  refine returnWidthGuard_exact [0x1f, 0x07] (by decide) (by decide) rfl reply
    (by omega) bound long ?_
  apply rx_dest
  apply rx_pop
  apply rx_mload (i := 128) (v := Bytes.toB256 (d.returnData.take 32)) (c := 3)
    (by simp only [St.extCost_eq, reply.size]; rfl)
    (balanceReplyMemory_word wf sevm.currentTarget d.returnData long)
    (reply.read_self (by decide : 128 + 32 ≤ 192)) (by omega)
  exact body

/-- The cut second request: slot-7 read and the second overlapping request. -/
private theorem syncSecondRequest_cut_rx {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G load : Nat} {balance0 tag : B256} {tail : SFunc}
    {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (room : R.length ≤ 1010) (charge : load = sloadCost sevm b 7)
    (body : SFunc.RunExact fs sevm
      (St (afterSload sevm b 7)
        ((b.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
         (b.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
         128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
         (b.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
         balance0 :: 0x1fd4 :: tag :: R)
        (balanceRequestMemory M sevm.currentTarget) G) tail o) :
    SFunc.RunExact fs sevm
      (St b (balance0 :: 0x1fd4 :: tag :: R) M (G + load + 113))
      (syncSecondRequestLine.foldr SFunc.next tail) o := by
  have mem1 : PtrMem 128 192 (M.write 128 balanceOfSelectorWord.toBytes) :=
    mem.write 128 balanceOfSelectorWord (Or.inr (by decide))
  have mem2 : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
    balanceRequestMemory_ptr mem sevm.currentTarget
  apply rx_push (w := 7) rfl (by simp only [List.length_cons]; omega)
  rw [show G + load + 110 = (G + 110) + load by omega]
  apply rx_sload_selC fork charge (by simp only [List.length_cons]; omega)
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mload (i := 64) (v := 128) (c := 3)
    (by rw [St.extCost_eq mem.size]; decide) mem.word
    (mem.read_self (by decide)) (by simp only [List.length_cons]; omega)
  apply rx_push (w := balanceOfSelectorWord) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mstore (i := 128) (v := balanceOfSelectorWord) (c := 3)
    (by rw [St.extCost_eq mem.size]; decide) rfl
  refine .next (Ninst.runCompiled_pushItem (G := G + 90) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl (by simp only [St.stack, List.length_cons]; omega)) ?_
  change SFunc.RunExact fs sevm
    (St (afterSload sevm b 7)
      (sevm.currentTarget.toB256 :: 128 :: 64 :: b.getStorVal sevm.currentTarget 7 ::
       balance0 :: 0x1fd4 :: tag :: R) (M.write 128 balanceOfSelectorWord.toBytes) (G + 90)) _ o
  apply rx_push (w := 4) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 132) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_mstore (i := 132) (v := sevm.currentTarget.toB256) (c := 3)
    (by rw [St.extCost_eq mem1.size]; decide) rfl
  apply rx_swap1
  apply rx_mload (i := 64) (v := 128) (c := 3)
    (by rw [St.extCost_eq mem2.size]; decide) mem2.word
    (mem2.read_self (by decide)) (by simp only [List.length_cons]; omega)
  apply rx_push (w := ~~~ addressMask) ff20_eq (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_swap3
  apply rx_and (and_mask_word _) (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_push (w := 0x70a08231) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_push (w := 36) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 164) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_swap1
  apply rx_swap2
  apply rx_swap1
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_sub' (v := 0) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 36) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  exact body

/-- The second actual request state before its STATICCALL. -/
def syncSecondCallInput (sevm : Sevm) (d0 : Devm) (callGas1 : Nat) : Devm :=
  St (temporalAccountAccessBase (afterSload sevm d0 7)
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr)
    (callGas1.toB256 :: (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
      128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
      Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
    (balanceRequestMemory (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData)
      sevm.currentTarget) callGas1

/-- From the actual first return, the reply guards, decoder, slot-7 read,
second request and code guard reach the second STATICCALL exactly. -/
private theorem sync_second_call_cut {sevm : Sevm} {post d0 : Devm} {callGas1 : Nat}
    {token : B256} {F : Exec.Deriv} {κ : Cursor} (ok : CursorOK code cert F κ)
    (tree : κ.f = SyncBalanceSite.first.afterCallTree)
    (success : F.exn = .ok post) (sameSevm : F.sevm = sevm)
    (state : F.devm = St d0 (1 :: 164 :: 0x70a08231 :: token :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
      (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData)
      (callGas1 + 5 + 22 +
        temporalAccountAccessCost (afterSload sevm d0 7)
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr +
        sloadCost sevm d0 7 + 113 + 70))
    (fork : CoveredFork sevm.benvStat.fork)
    (bound : d0.returnData.length < 2 ^ 256) (long0 : 32 ≤ d0.returnData.length)
    (nonzero1 : ((afterSload sevm d0 7).getCode
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr).size.toB256 ≠ 0) :
    ∃ (node : Exec.Deriv) (cursor : Cursor),
      Exec.Deriv.ExecFreeUntil F node ∧ node.sevm = sevm ∧ node.exn = .ok post ∧
      CursorOK code cert node cursor ∧
      cursor.f = .next (.exec .staticcall) SyncBalanceSite.second.afterCallTree ∧
      node.devm = syncSecondCallInput sevm d0 callGas1 := by
  subst sameSevm
  have request0 := balanceRequestMemory_ptr getterInitMemory_ptr F.sevm.currentTarget
  obtain ⟨node, cursor, span, nodeSevm, nodeExn, placed, nodeTree, nodeState⟩ :=
    cursor_cut_exact (fs' := []) cert_check
      (tgt := .next (.exec .staticcall) SyncBalanceSite.second.afterCallTree)
      (s := syncSecondCallInput F.sevm d0 callGas1)
      (by
      unfold SyncBalanceSite.afterCallTree SyncBalanceSite.callTree t_1edd_c31
      cut_nexts
      apply SFunc.CutAt.succ
      unfold t_1ef1_c31
      apply SFunc.CutAt.dest
      cut_nexts
      apply SFunc.CutAt.succ
      unfold t_1f07_c31
      apply SFunc.CutAt.dest
      cut_nexts
      apply SFunc.CutAt.succ
      unfold t_1f7a_c31
      apply SFunc.CutAt.dest
      cut_nexts
      exact .here) ok tree success fork (by
      rw [state]
      exact syncFirstReply_cut_rx request0 getterInitMemory_ptr.wf stack_room bound long0
        (syncSecondRequest_cut_rx fork (balanceReplyMemory_ptr d0.returnData request0)
          stack_room rfl (syncCodeGuardCall_cut_rx .second fork stack_room nonzero1)))
  exact ⟨node, cursor, span, nodeSevm, nodeExn.trans success, placed, nodeTree, nodeState⟩

/-- The actual update/unlock schedule; no caller-selected primitive charges. -/
def syncUpdateUnlockClosedGas (sevm : Sevm) (b : Devm)
    (balance0 balance1 : B256) (n G : Nat) : Nat :=
  let u := afterSload sevm b 8
  let old0 := reserve0Read (b.getStorVal sevm.currentTarget 8)
  let old1 := reserve1Read (b.getStorVal sevm.currentTarget 8)
  let h := afterSload sevm u 8
  let delta := updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time
  let w9 := updateAccumulatorPost sevm h 9 (updatePriceWord old0 old1) delta
  let v := updateOracleWorld sevm u old0 old1
  syncUpdateUnlockGas sevm b balance0 balance1 n
    (sloadCost sevm u 8)
    (sloadCost sevm h 9)
    (sstoreCost sevm (afterSload sevm h 9) 9
      (updateAccumulatorWord (h.getStorVal sevm.currentTarget 9)
        (updatePriceWord old0 old1) delta))
    (sloadCost sevm w9 10)
    (sstoreCost sevm (afterSload sevm w9 10) 10
      (updateAccumulatorWord (w9.getStorVal sevm.currentTarget 10)
        (updatePriceWord old1 old0) delta))
    (sloadCost sevm v 8)
    (sstoreCost sevm (afterSload sevm v 8) 8
      (updateFinalPackedWord sevm u old0 old1 balance0 balance1)) G

/-- Exact liveness with the same actual canonical returned worlds and views. -/
theorem syncPc0_canonical_live {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b d0 d1 : Devm}
    {callGas0 callGas1 G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (codeEq : sevm.code = code)
    (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (static : sevm.isStatic = false) (unlocked : b.getStorVal sevm.currentTarget 12 = 1)
    (sentry : gCallStipend <
      (callGas0 + 5 + 22 + temporalAccountAccessCost (syncFirstWorld sevm b)
        (syncFirstToken sevm b).toAdr) + sloadCost sevm (syncLockedWorld sevm b) 6 + 119 +
      sstoreCost sevm (afterSload sevm b 12) 12 0)
    (nonzero0 : ((syncFirstWorld sevm b).getCode (syncFirstToken sevm b).toAdr).size.toB256 ≠ 0)
    (call0 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (syncFirstWorld sevm b) (syncFirstToken sevm b).toAdr)
        (callGas0.toB256 :: (syncFirstToken sevm b) :: 128 :: 36 :: 128 :: 32 :: 164 ::
          0x70a08231 :: (syncFirstToken sevm b) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
        (balanceRequestMemory getterInitMemory sevm.currentTarget) callGas0) (.exec .staticcall) d0)
    (success0 : d0.stack = 1 :: 164 :: 0x70a08231 :: (syncFirstToken sevm b) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
    (returnedGas0 : d0.gasLeft = callGas1 + 5 + 22 +
      temporalAccountAccessCost (afterSload sevm d0 7)
        (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr +
      sloadCost sevm d0 7 + 113 + 70)
    (long0 : 32 ≤ d0.returnData.length)
    (nonzero1 : ((afterSload sevm d0 7).getCode
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr).size.toB256 ≠ 0)
    (call1 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (afterSload sevm d0 7)
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr)
        (callGas1.toB256 :: (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
        (balanceRequestMemory (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData)
          sevm.currentTarget) callGas1) (.exec .staticcall) d1)
    (success1 : d1.stack = 1 :: 164 :: 0x70a08231 ::
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
      Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
    (returnedGas1 : d1.gasLeft = (syncUpdateUnlockClosedGas sevm d1 (Bytes.toB256 (d0.returnData.take 32)) (Bytes.toB256 (d1.returnData.take 32)) 192 (G + 1)) + 70)
    (long1 : 32 ≤ d1.returnData.length)
    (bound0 : (Bytes.toB256 (d0.returnData.take 32)).toNat < 2 ^ 112)
    (bound1 : (Bytes.toB256 (d1.returnData.take 32)).toNat < 2 ^ 112) :
    let balance0 := (Bytes.toB256 (d0.returnData.take 32))
    let balance1 := (Bytes.toB256 (d1.returnData.take 32))
    let u := afterSload sevm d1 8
    let old0 := reserve0Read (d1.getStorVal sevm.currentTarget 8)
    let old1 := reserve1Read (d1.getStorVal sevm.currentTarget 8)
    let finalGas := (G + 1) + 8 + sstoreCost sevm (syncUpdatedWorld sevm d1 balance0 balance1) 12 1 + 7
    let h := afterSload sevm u 8
    let delta := updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time
    let w9 := updateAccumulatorPost sevm h 9 (updatePriceWord old0 old1) delta
    let v := updateOracleWorld sevm u old0 old1
    let store9 := sstoreCost sevm (afterSload sevm h 9) 9
      (updateAccumulatorWord (h.getStorVal sevm.currentTarget 9)
        (updatePriceWord old0 old1) delta)
    let load10 := sloadCost sevm w9 10
    let store10 := sstoreCost sevm (afterSload sevm w9 10) 10
      (updateAccumulatorWord (w9.getStorVal sevm.currentTarget 10)
        (updatePriceWord old1 old0) delta)
    let load8 := sloadCost sevm v 8
    let store8 := sstoreCost sevm (afterSload sevm v 8) 8
      (updateFinalPackedWord sevm u old0 old1 balance0 balance1)
    gCallStipend < finalGas + updateSyncGas 192 + store8 →
    (updateOracleActive sevm u old0 old1 →
      gCallStipend < finalGas + updateSyncGas 192 + load8 + store8 + 110 + store10) →
    (updateOracleActive sevm u old0 old1 →
      gCallStipend < finalGas + updateSyncGas 192 + load8 + store8 + 110 +
        load10 + store10 + 42 + 149 + store9) →
    gCallStipend < (G + 1) + 8 + sstoreCost sevm (syncUpdatedWorld sevm d1 balance0 balance1) 12 1 →
    ∃ (post : Devm)
      (run : Exec 0 sevm
        (St b [] Mem.empty (syncCalleePrefixGas sevm b callGas0 + 15 + 229)) (.ok post)),
      post.gasLeft = G ∧
      (WriterInj (WriterExtend K (syncTraceKeys
          ⟨0, sevm, St b [] Mem.empty (syncCalleePrefixGas sevm b callGas0 + 15 + 229),
            .ok post, run⟩)) →
        WriterApart (WriterExtend K (syncTraceKeys
          ⟨0, sevm, St b [] Mem.empty (syncCalleePrefixGas sevm b callGas0 + 15 + 229),
            .ok post, run⟩)) →
        ∃ result : SyncCanonicalResult K current invocation
            ⟨0, sevm, St b [] Mem.empty (syncCalleePrefixGas sevm b callGas0 + 15 + 229),
              .ok post, run⟩ b post,
          result.returned0.devm = d0 ∧ result.returned1.devm = d1 ∧
          result.out0 = d0.returnData ∧ result.out1 = d1.returnData) := by
  dsimp only
  intro sentry8 sentry10 sentry9 unlockSentry
  let balance0 := Bytes.toB256 (d0.returnData.take 32)
  let balance1 := Bytes.toB256 (d1.returnData.take 32)
  let u := afterSload sevm d1 8
  let old0 := reserve0Read (d1.getStorVal sevm.currentTarget 8)
  let old1 := reserve1Read (d1.getStorVal sevm.currentTarget 8)
  let h := afterSload sevm u 8
  let delta := updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time
  let w9 := updateAccumulatorPost sevm h 9 (updatePriceWord old0 old1) delta
  let v := updateOracleWorld sevm u old0 old1
  have exactRun := syncPc0_exact
    (headerLoad := sloadCost sevm u 8)
    (load9 := sloadCost sevm h 9)
    (store9 := sstoreCost sevm (afterSload sevm h 9) 9
      (updateAccumulatorWord (h.getStorVal sevm.currentTarget 9)
        (updatePriceWord old0 old1) delta))
    (load10 := sloadCost sevm w9 10)
    (store10 := sstoreCost sevm (afterSload sevm w9 10) 10
      (updateAccumulatorWord (w9.getStorVal sevm.currentTarget 10)
        (updatePriceWord old1 old0) delta))
    (load8 := sloadCost sevm v 8)
    (store8 := sstoreCost sevm (afterSload sevm v 8) 8
      (updateFinalPackedWord sevm u old0 old1 balance0 balance1))
    fork value size selector static unlocked sentry nonzero0 call0 success0 returnedGas0 long0
    nonzero1 call1 success1
    (by simpa only [syncUpdateUnlockClosedGas] using returnedGas1)
    long1 bound0 bound1 rfl rfl rfl (fun _ => ⟨rfl, rfl, rfl, rfl⟩)
    sentry8 sentry10 sentry9 unlockSentry
  obtain ⟨run⟩ := lift_exact cert_check jumps_ok codeEq fork exactRun
  refine ⟨_, run, rfl, ?_⟩
  intro hashTInj hashTApart
  obtain ⟨result⟩ := sync_canonical_source_frame_result invocation rep sem image installed
    codeEq fork selector run hashTInj hashTApart
  obtain ⟨firstFree, _, _, firstInst, firstEdge, _, secondFree, _, _, _, _, secondInst,
    secondEdge, _, _⟩ := result.order
  -- The actual dispatcher, wrapper call and callee prefix reach the first STATICCALL.
  obtain ⟨entry, entryCursor, entryFree, entrySevm, entryExn, entryOk, entryTree, entryState⟩ :=
    sync_dispatch_cut (G := syncCalleePrefixGas sevm b callGas0) codeEq fork value size selector run
  obtain ⟨callee, calleeCursor, calleeFree, calleeSevm, calleeExn, calleeOk, calleeEntry,
    calleeState⟩ := cursor_callNext_exact cert_check entryOk entryTree entryExn
      (by rw [entrySevm]; exact fork) (d := 0x1df5)
      (s := St b [0x0257, 0xfff6cae9] getterInitMemory (syncCalleePrefixGas sevm b callGas0))
      (by rw [entryState]; exact popBurnBy_St1)
  have calleeTree : calleeCursor.f = t_1df5_c31 :=
    Option.some.inj (calleeEntry.symm.trans (rfl : cert.prog[31]? = some t_1df5_c31))
  obtain ⟨first, firstCursor, firstSpan, firstSevm, firstExn, firstOk, firstTree, firstState⟩ :=
    sync_first_call_cut calleeOk calleeTree (calleeExn.trans entryExn)
      (calleeSevm.trans entrySevm) calleeState fork static unlocked sentry nonzero0
  have firstSame : first = result.first.node :=
    Exec.Deriv.ExecFreeUntil.eq_of_execAt ((entryFree.trans calleeFree).trans firstSpan)
      firstFree (firstOk.ninstAt_of_next firstTree) (firstInst ▸ result.first.decoded)
  -- Its actual continuation is the canonical first return, with the compiled result.
  have firstFork : CoveredFork first.sevm.benvStat.fork := by rw [firstSevm]; exact fork
  obtain ⟨ret0, ret0Cursor, ret0Edge, _, ret0Primitive, ret0Synthetic, _, ret0Ok⟩ :=
    cursor_next_forward cert_check firstOk firstTree firstExn firstFork
  have ret0State : ret0.devm = d0 := ninstRun_eq_of_runCompiled ret0Primitive.toRun
    (by rw [firstSevm, firstState]; exact call0)
  have ret0Is : ret0 = result.returned0 :=
    Exec.Deriv.ParentStep.unique ret0Edge (by rw [firstSame]; exact firstEdge)
  have returned0Eq : result.returned0.devm = d0 := ret0Is ▸ ret0State
  have ret0Tree : ret0Cursor.f = SyncBalanceSite.first.afterCallTree := by
    rcases firstCursor with ⟨body, pc, a, m, K⟩
    dsimp only at firstTree
    subst body
    cases ret0Synthetic
    rfl
  obtain ⟨flag0, out0, post0, bound0', _⟩ := ri_staticcall_bounded fork (Ninst.Run.of_runCompiled call0)
  have flagOne : flag0 = 1 := (List.cons.inj (post0.stack.symm.trans success0)).1
  subst flagOne
  have outEq : d0.returnData = out0 := post0.returnData
  have memory0 : d0.memory =
      balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData := by
    rw [post0.memory, outEq]
    rfl
  have ret0Start : ret0.devm = St d0
      (1 :: 164 :: 0x70a08231 :: syncFirstToken sevm b :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
      (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData)
      (callGas1 + 5 + 22 +
        temporalAccountAccessCost (afterSload sevm d0 7)
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr +
        sloadCost sevm d0 7 + 113 + 70) := by
    rw [ret0State, ← returnedGas0]
    exact St.self success0 memory0
  have ret0Sevm : ret0.sevm = sevm := (Cursor.parentStep_sevm ret0Edge).trans firstSevm
  have ret0Exn : ret0.exn = first.exn := by cases ret0Edge <;> rfl
  obtain ⟨second, secondCursor, secondSpan, secondSevm, secondExn, secondOk, secondTree,
    secondState⟩ := sync_second_call_cut ret0Ok ret0Tree (ret0Exn.trans firstExn) ret0Sevm ret0Start fork
      (outEq ▸ bound0') long0 nonzero1
  have secondSame : second = result.second.node :=
    Exec.Deriv.ExecFreeUntil.eq_of_execAt (ret0Is ▸ secondSpan) secondFree
      (secondOk.ninstAt_of_next secondTree) (secondInst ▸ result.second.decoded)
  have secondFork : CoveredFork second.sevm.benvStat.fork := by rw [secondSevm]; exact fork
  obtain ⟨ret1, _, ret1Edge, _, ret1Primitive, _, _, _⟩ :=
    cursor_next_forward cert_check secondOk secondTree secondExn secondFork
  have ret1State : ret1.devm = d1 := ninstRun_eq_of_runCompiled ret1Primitive.toRun
    (by rw [secondSevm, secondState]; exact call1)
  have ret1Is : ret1 = result.returned1 :=
    Exec.Deriv.ParentStep.unique ret1Edge (by rw [secondSame]; exact secondEdge)
  have returned1Eq : result.returned1.devm = d1 := ret1Is ▸ ret1State
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, data0, _⟩ := result.firstCall
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, data1, _⟩ := result.secondCall
  refine ⟨result, returned0Eq, returned1Eq, ?_, ?_⟩
  · exact data0.symm.trans (congrArg Devm.returnData returned0Eq)
  · exact data1.symm.trans (congrArg Devm.returnData returned1Eq)

end Blanc.Lift.UniswapV2Pair
