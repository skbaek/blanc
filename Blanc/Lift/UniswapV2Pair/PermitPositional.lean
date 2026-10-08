import Blanc.Lift.UniswapV2Pair.PermitPositionalRequest
import Blanc.Lift.CursorNoExecSuffix

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The recovery instruction is an actual occurrence, including its original
complete operands, returned cursor, and bounded response. -/
structure PermitCallOccurrence (root : Exec.Deriv) (b : Devm) where
  call : CallOccurrenceStep root .staticcall
  gasWord : B256
  gas : Nat
  beforeSevm : call.occurrence.node.sevm = root.sevm
  beforeState : call.occurrence.node.devm =
    St (permitNonceWorld root.sevm b (permitOwner root.sevm))
      (gasWord :: 1 :: 482 :: 128 :: 450 :: 32 :: permitPublicCallStack root.sevm b 0xd505accf)
      (permitPublicCallMemory root.sevm b) gas
  beforeMemory : call.occurrence.node.devm.memory = permitPublicCallMemory root.sevm b
  gap : Exec.Deriv.ExecFreeUntil root call.occurrence.node
  returnedCursor : Cursor
  placed : CursorOK code cert call.returned returnedCursor
  tree : returnedCursor.f = permitRecoveryTail
  continuations : returnedCursor.K.map Cont.f = [t_0257_c76]
  returnedSevm : call.returned.sevm = root.sevm
  returnedExn : call.returned.exn = root.exn
  flag : B256
  out : Bytes
  post : StaticCallPost (permitNonceWorld root.sevm b (permitOwner root.sevm))
    call.returned.devm (permitPublicCallStack root.sevm b 0xd505accf)
    (permitPublicCallMemory root.sevm b) 482 128 450 32 flag out
  bound : out.length < 2^256
  answered : flag = 1 → StaticAnswered root.sevm
    (permitNonceWorld root.sevm b (permitOwner root.sevm)) (1 : B256).toAdr
    (ExternalOperation.encode (.recover (permitPublicDigest root.sevm b)
      (permitV root.sevm) (permitR root.sevm) (permitS root.sevm))) out

def permitReplyGuardLine : List Ninst :=
  [.reg .iszero, .reg (.dup 0), .reg .iszero, .push [0x1c, 0xdc] (by decide)]

/-- The actual successful parent cannot take the recovery failure/revert arm. -/
theorem PermitCallOccurrence.flag_one {root : Exec.Deriv} {b post : Devm}
    (actual : PermitCallOccurrence root b) (success : root.exn = .ok post)
    (fork : CoveredFork root.sevm.benvStat.fork) : actual.flag = 1 := by
  rcases actual.post.flag with zero | one
  · have returnedFork : CoveredFork actual.call.returned.sevm.benvStat.fork :=
      actual.returnedSevm ▸ fork
    have returnedSuccess := actual.returnedExn.trans success
    let begin : CursorStateAt code cert actual.call.returned permitRecoveryTail
        actual.call.returned.devm (0 :: permitPublicCallStack root.sevm b 0xd505accf)
        (permitReplyMemory (permitPublicCallMemory root.sevm b) actual.out)
        (actual.returnedCursor.K.map Cont.f) :=
      ⟨actual.call.returned, actual.returnedCursor, .refl _, rfl, rfl,
        actual.placed, actual.tree,
        ⟨actual.call.returned.devm.gasLeft, by simpa only [zero, permitReplyMemory,
          show (482 : B256).toNat = 482 from rfl, show (128 : B256).toNat = 128 from rfl,
          show (450 : B256).toNat = 450 from rfl, show (32 : B256).toNat = 32 from rfl]
          using actual.post.eq_St⟩, rfl⟩
    obtain ⟨guard⟩ := begin.line cert_check returnedSuccess returnedFork permitReplyGuardLine
      (by rfl)
      (by intro n member x equal; subst n; simp only [permitReplyGuardLine,
        List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
      (b' := actual.call.returned.devm)
      (S' := 0x1cdc :: 0 :: 1 :: permitPublicCallStack root.sevm b 0xd505accf)
      (M' := permitReplyMemory (permitPublicCallMemory root.sevm b) actual.out) (by
        intro gas d line
        dsimp only [permitReplyGuardLine] at line
        obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero step
        obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
        obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero step
        obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨gas', state⟩ := ri_push step
        cases line
        exact ⟨gas', by simpa only [show B256.eqCheck (0 : B256) 0 = 1 from by decide,
          show B256.eqCheck (1 : B256) 0 = 0 from by decide,
          show Bytes.toB256 [28, 220] = (0x1cdc : B256) from rfl] using state⟩)
    obtain ⟨failed⟩ := guard.branchZero cert_check returnedSuccess returnedFork
    exact (failed.placed.revertLineNoOk cert_check (failed.sevm_eq ▸ returnedFork)
      [.reg .returndatasize, .push [0] (by decide), .reg (.dup 0),
        .reg .returndatacopy, .reg .returndatasize, .push [0] (by decide)]
      (failed.tree.trans rfl) (failed.exn_eq.trans returnedSuccess)).elim
  · exact one

/-- Both the post-call tree and every actual suspended continuation are in the
checked closed region, so no later external instruction exists in this frame. -/
theorem PermitCallOccurrence.noExecSuffix {root : Exec.Deriv} {b : Devm}
    (actual : PermitCallOccurrence root b) (fork : CoveredFork root.sevm.benvStat.fork) :
    ∀ N, Exec.Deriv.ParentPrefix actual.call.returned N → ∀ x,
      ¬ Ninst.At N.sevm.code N.pc (.exec x) := by
  apply actual.placed.noExecSuffix cert_check (actual.returnedSevm ▸ fork)
    (E := [15, 64]) (by decide)
  · rw [actual.tree]
    decide
  · rw [actual.continuations]
    intro f member
    rcases List.mem_singleton.mp member with rfl
    decide

theorem permit_call_occurrence {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xd505accf)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (PermitCallOccurrence ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b) := by
  obtain ⟨gw, cut⟩ := permit_call_cursor_state codeEq fork selector run
  obtain ⟨cut⟩ := cut
  obtain ⟨call, κ', sameNode, _, primitive, synthetic, _, placed⟩ :=
    cursor_next_call_occurrence_forward cert_check cut.free.1 cut.placed cut.tree
      cut.exn_eq (cut.sevm_eq ▸ fork)
  obtain ⟨gas, state⟩ := cut.state
  have actual : Ninst.Run sevm
      (St (permitNonceWorld sevm b (permitOwner sevm))
        (gw :: 1 :: 482 :: 128 :: 450 :: 32 :: permitPublicCallStack sevm b 0xd505accf)
        (permitPublicCallMemory sevm b) gas) (.exec .staticcall) call.returned.devm := by
    simpa only [cut.sevm_eq, state] using primitive.toRun
  obtain ⟨flag, out, post, bound, answered⟩ := ri_staticcall_bounded fork actual
  have treeK : κ'.f = permitRecoveryTail ∧ κ'.K = cut.cursor.K := by
    have tree := cut.tree
    generalize original : cut.cursor = κ at synthetic tree ⊢
    rcases κ with ⟨f, pc, a, m, K⟩
    change f = .next (.exec .staticcall) permitRecoveryTail at tree
    subst f
    cases synthetic
    exact ⟨rfl, rfl⟩
  have sameExn : call.returned.exn = call.occurrence.node.exn := by
    have edge := call.edge
    generalize original : call.occurrence.node = F at edge ⊢
    generalize returned : call.returned = N at edge ⊢
    cases edge <;> rfl
  have beforeSevm := sameNode ▸ cut.sevm_eq
  refine ⟨⟨call, gw, gas, beforeSevm, ?_, ?_, ?_, κ', placed, treeK.1, ?_,
    (Cursor.parentStep_sevm call.edge).trans beforeSevm, ?_, flag, out, post, bound, ?_⟩⟩
  · rw [sameNode]
    exact state
  · rw [sameNode]
    exact cut.memory_eq
  · rw [sameNode]
    exact cut.free
  · rw [treeK.2]
    exact cut.continuations
  · rw [sameExn, sameNode]
    exact cut.exn_eq
  · intro one
    have answer := answered one
    have request := (permitCallMemory_facts (sevm := sevm) (b := b)
      getterInitMemory_ptr (Mem.reads_data getterInitMemory) (permitOwner sevm)
      (permitSpender sevm) (permitValue sevm) (permitDeadline sevm)
      (permitV sevm) (permitR sevm) (permitS sevm)).2.1
    change ((permitPublicCallMemory sevm b).read 482 128).1 =
      ExternalOperation.encode (.recover (permitPublicDigest sevm b)
        (permitV sevm) (permitR sevm) (permitS sevm)) at request
    change StaticAnswered sevm (permitNonceWorld sevm b (permitOwner sevm))
      (1 : B256).toAdr ((permitPublicCallMemory sevm b).read 482 128).1 out at answer
    rw [request] at answer
    exact answer

end Blanc.Lift.UniswapV2Pair
