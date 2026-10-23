import Blanc.Lift.HistCursorReturn
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

structure PermitCallOccurrenceH (root : Exec.Deriv) (b : Devm) where
  call : CallOccurrenceStep root .staticcall
  gasWord : B256
  gas : Nat
  beforeSevm : call.occurrence.node.sevm = root.sevm
  beforeState : call.occurrence.node.devm =
    St (permitNonceWorldH root.sevm b (permitOwner root.sevm))
      (gasWord :: 1 :: 482 :: 128 :: 450 :: 32 :: permitPublicCallStackH root.sevm b 0xd505accf)
      (permitPublicCallMemoryH root.sevm b) gas
  beforeMemory : call.occurrence.node.devm.memory = permitPublicCallMemoryH root.sevm b
  gap : Exec.Deriv.ExecFreeUntil root call.occurrence.node
  returnedCursor : Cursor
  placed : CursorOK code cert call.returned returnedCursor
  tree : returnedCursor.f = permitRecoveryTail
  continuations : returnedCursor.K.map Cont.f = [t_0257_c76]
  returnedSevm : call.returned.sevm = root.sevm
  returnedExn : call.returned.exn = root.exn
  flag : B256
  out : Bytes
  post : StaticCallPost (permitNonceWorldH root.sevm b (permitOwner root.sevm))
    call.returned.devm (permitPublicCallStackH root.sevm b 0xd505accf)
    (permitPublicCallMemoryH root.sevm b) 482 128 450 32 flag out
  bound : out.length < 2^256
  answered : flag = 1 → StaticAnsweredH root.sevm
    (permitNonceWorldH root.sevm b (permitOwner root.sevm)) (1 : B256).toAdr
    (ExternalOperation.encode (.recover (permitPublicDigestH root.sevm b)
      (permitV root.sevm) (permitR root.sevm) (permitS root.sevm))) out

/-- On a covered fork, `PermitCallOccurrenceH` gives the modern `PermitCallOccurrence` with the same fields. -/
def PermitCallOccurrenceH.toCovered {root : Exec.Deriv} {b : Devm}
    (fork : CoveredFork root.sevm.benvStat.fork) (h : PermitCallOccurrenceH root b) :
    PermitCallOccurrence root b where
  call := h.call
  gasWord := h.gasWord
  gas := h.gas
  beforeSevm := h.beforeSevm
  beforeState := by simpa only [permitNonceWorldH_of_covered fork, permitPublicCallMemoryH_of_covered fork, permitPublicCallStackH_of_covered fork] using h.beforeState
  beforeMemory := by simpa only [permitPublicCallMemoryH_of_covered fork] using h.beforeMemory
  gap := h.gap
  returnedCursor := h.returnedCursor
  placed := h.placed
  tree := h.tree
  continuations := h.continuations
  returnedSevm := h.returnedSevm
  returnedExn := h.returnedExn
  flag := h.flag
  out := h.out
  post := by simpa only [permitNonceWorldH_of_covered fork, permitPublicCallMemoryH_of_covered fork, permitPublicCallStackH_of_covered fork] using h.post
  bound := h.bound
  answered := by simpa only [permitNonceWorldH_of_covered fork, permitPublicDigestH_of_covered fork, StaticAnsweredH_iff_of_covered fork] using h.answered

/-- On a covered fork, the modern `PermitCallOccurrence` gives `PermitCallOccurrenceH` with the same fields. -/
def PermitCallOccurrence.toH {root : Exec.Deriv} {b : Devm}
    (fork : CoveredFork root.sevm.benvStat.fork) (h : PermitCallOccurrence root b) :
    PermitCallOccurrenceH root b where
  call := h.call
  gasWord := h.gasWord
  gas := h.gas
  beforeSevm := h.beforeSevm
  beforeState := by simpa only [permitNonceWorldH_of_covered fork, permitPublicCallMemoryH_of_covered fork, permitPublicCallStackH_of_covered fork] using h.beforeState
  beforeMemory := by simpa only [permitPublicCallMemoryH_of_covered fork] using h.beforeMemory
  gap := h.gap
  returnedCursor := h.returnedCursor
  placed := h.placed
  tree := h.tree
  continuations := h.continuations
  returnedSevm := h.returnedSevm
  returnedExn := h.returnedExn
  flag := h.flag
  out := h.out
  post := by simpa only [permitNonceWorldH_of_covered fork, permitPublicCallMemoryH_of_covered fork, permitPublicCallStackH_of_covered fork] using h.post
  bound := h.bound
  answered := by simpa only [permitNonceWorldH_of_covered fork, permitPublicDigestH_of_covered fork, StaticAnsweredH_iff_of_covered fork] using h.answered

def permitReplyGuardLine : List Ninst :=
  [.reg .iszero, .reg (.dup 0), .reg .iszero, .push [0x1c, 0xdc] (by decide)]

theorem PermitCallOccurrenceH.flag_one {root : Exec.Deriv} {b post : Devm}
    (actual : PermitCallOccurrenceH root b) (success : root.exn = .ok post)
    (stateGas : root.sevm.benvStat.rules.stateGas = none)
    (bal : root.sevm.benvStat.rules.bal = none) : actual.flag = 1 := by
  rcases actual.post.flag with zero | one
  · have returnedFork : actual.call.returned.sevm.benvStat.rules.stateGas = none ∧
        actual.call.returned.sevm.benvStat.rules.bal = none :=
      ⟨actual.returnedSevm ▸ stateGas, actual.returnedSevm ▸ bal⟩
    have returnedSuccess := actual.returnedExn.trans success
    let begin : CursorStateAt code cert actual.call.returned permitRecoveryTail
        actual.call.returned.devm (0 :: permitPublicCallStackH root.sevm b 0xd505accf)
        (permitReplyMemory (permitPublicCallMemoryH root.sevm b) actual.out)
        (actual.returnedCursor.K.map Cont.f) :=
      ⟨actual.call.returned, actual.returnedCursor, .refl _, rfl, rfl,
        actual.placed, actual.tree,
        ⟨actual.call.returned.devm.gasLeft, by simpa only [zero, permitReplyMemory,
          show (482 : B256).toNat = 482 from rfl, show (128 : B256).toNat = 128 from rfl,
          show (450 : B256).toNat = 450 from rfl, show (32 : B256).toNat = 32 from rfl]
          using actual.post.eq_St⟩, rfl⟩
    obtain ⟨guard⟩ := begin.lineH cert_check returnedSuccess returnedFork.1 permitReplyGuardLine
      (by rfl)
      (by intro n member x equal; subst n; simp only [permitReplyGuardLine,
        List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
      (b' := actual.call.returned.devm)
      (S' := 0x1cdc :: 0 :: 1 :: permitPublicCallStackH root.sevm b 0xd505accf)
      (M' := permitReplyMemory (permitPublicCallMemoryH root.sevm b) actual.out) (by
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
    obtain ⟨failed⟩ := guard.branchZeroH cert_check returnedSuccess returnedFork.1
    exact (failed.placed.revertLineNoOkH cert_check (failed.sevm_eq ▸ returnedFork.1)
      [.reg .returndatasize, .push [0] (by decide), .reg (.dup 0),
        .reg .returndatacopy, .reg .returndatasize, .push [0] (by decide)]
      (failed.tree.trans rfl) (failed.exn_eq.trans returnedSuccess)).elim
  · exact one

/-- The actual successful parent cannot take the recovery failure/revert arm. -/
theorem PermitCallOccurrence.flag_one {root : Exec.Deriv} {b post : Devm}
    (actual : PermitCallOccurrence root b) (success : root.exn = .ok post)
    (fork : CoveredFork root.sevm.benvStat.fork) : actual.flag = 1 :=
  PermitCallOccurrenceH.flag_one (actual.toH fork) success fork.rules_stateGas_none fork.rules_bal_none


theorem PermitCallOccurrenceH.noExecSuffix {root : Exec.Deriv} {b : Devm}
    (actual : PermitCallOccurrenceH root b) (stateGas : root.sevm.benvStat.rules.stateGas = none) :
    ∀ N, Exec.Deriv.ParentPrefix actual.call.returned N → ∀ x,
      ¬ Ninst.At N.sevm.code N.pc (.exec x) := by
  apply actual.placed.noExecSuffixH cert_check (actual.returnedSevm ▸ stateGas)
    (E := [15, 64]) (by decide)
  · rw [actual.tree]
    decide
  · rw [actual.continuations]
    intro f member
    rcases List.mem_singleton.mp member with rfl
    decide

/-- Both the post-call tree and every actual suspended continuation are in the
checked closed region, so no later external instruction exists in this frame. -/
theorem PermitCallOccurrence.noExecSuffix {root : Exec.Deriv} {b : Devm}
    (actual : PermitCallOccurrence root b) (fork : CoveredFork root.sevm.benvStat.fork) :
    ∀ N, Exec.Deriv.ParentPrefix actual.call.returned N → ∀ x,
      ¬ Ninst.At N.sevm.code N.pc (.exec x) :=
  PermitCallOccurrenceH.noExecSuffix (actual.toH fork) fork.rules_stateGas_none


theorem permit_call_occurrenceH {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (selector : Blanc.Sevm.selector sevm = 0xd505accf)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (PermitCallOccurrenceH ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b) := by
  obtain ⟨gw, cut⟩ := permit_call_cursor_stateH codeEq stateGas bal selector run
  obtain ⟨cut⟩ := cut
  obtain ⟨call, κ', sameNode, _, primitive, synthetic, _, placed⟩ :=
    cursor_next_call_occurrence_forwardH cert_check cut.free.1 cut.placed cut.tree
      cut.exn_eq (cut.sevm_eq ▸ stateGas)
  obtain ⟨gas, state⟩ := cut.state
  have actual : Ninst.Run sevm
      (St (permitNonceWorldH sevm b (permitOwner sevm))
        (gw :: 1 :: 482 :: 128 :: 450 :: 32 :: permitPublicCallStackH sevm b 0xd505accf)
        (permitPublicCallMemoryH sevm b) gas) (.exec .staticcall) call.returned.devm := by
    simpa only [cut.sevm_eq, state] using primitive.toRun
  obtain ⟨flag, out, post, bound, answered⟩ := ri_staticcall_boundedH stateGas actual
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
    have request := (permitCallMemory_factsH (sevm := sevm) (b := b)
      getterInitMemory_ptr (Mem.reads_data getterInitMemory) (permitOwner sevm)
      (permitSpender sevm) (permitValue sevm) (permitDeadline sevm)
      (permitV sevm) (permitR sevm) (permitS sevm)).2.1
    change ((permitPublicCallMemoryH sevm b).read 482 128).1 =
      ExternalOperation.encode (.recover (permitPublicDigestH sevm b)
        (permitV sevm) (permitR sevm) (permitS sevm)) at request
    change StaticAnsweredH sevm (permitNonceWorldH sevm b (permitOwner sevm))
      (1 : B256).toAdr ((permitPublicCallMemoryH sevm b).read 482 128).1 out at answer
    rw [request] at answer
    exact answer

theorem permit_call_occurrence {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xd505accf)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (PermitCallOccurrence ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b) := by
  obtain ⟨actual⟩ := permit_call_occurrenceH codeEq fork.rules_stateGas_none fork.rules_bal_none
    selector run
  exact ⟨actual.toCovered fork⟩


end Blanc.Lift.UniswapV2Pair
