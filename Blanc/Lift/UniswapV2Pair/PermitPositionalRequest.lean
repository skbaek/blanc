import Blanc.Lift.UniswapV2Pair.PermitPositionalCuts

namespace Blanc.Lift.UniswapV2Pair

open Jaune

def permitRequestPrefixLine : List Ninst :=
  permitNonceLine ++ (permitStructLine ++ (permitDigestLine ++ permitRequestLine))

def permitRecoveryTail : SFunc :=
  .next (.reg .iszero) (.next (.reg (.dup 0)) (.next (.reg .iszero)
    (.next (.push [0x1c, 0xdc] (by decide)) (.branch t_1cd3_c29 t_1cdc_c29))))

theorem permit_request_prefix_line_invH {sevm : Sevm} {b d : Devm} {G : Nat}
    (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (line : Line.Run sevm (St b
      [permitS sevm, permitR sevm, (permitV sevm).toB256, permitDeadline sevm,
        permitValue sevm, (permitSpender sevm).toB256, (permitOwner sevm).toB256,
        0x0257, 0xd505accf] getterInitMemory G) permitRequestPrefixLine d) :
    ∃ G', d = St (permitNonceWorldH sevm b (permitOwner sevm))
      (1 :: 482 :: 128 :: 450 :: 32 :: permitPublicCallStackH sevm b 0xd505accf)
      (permitPublicCallMemoryH sevm b) G' := by
  have mem := getterInitMemory_ptr
  have reads := Mem.reads_data getterInitMemory
  have mA := permitNonceMemory_ptr mem (permitOwner sevm)
  have wA := (mem.wf.write 0 (permitOwner sevm).toB256.toBytes).write 32 (4 : B256).toBytes
  have rA := (reads.write mem.wf 0 (permitOwner sevm).toB256.toBytes).write
    (mem.wf.write 0 (permitOwner sevm).toB256.toBytes) 32 (4 : B256).toBytes
  have mB := permitStructMemory_ptr mA (permitOwner sevm) (permitSpender sevm)
    (permitValue sevm) (permitNonceReadH sevm b (permitOwner sevm)) (permitDeadline sevm)
  have rB := permitStructMemory_reads wA rA (permitOwner sevm) (permitSpender sevm)
    (permitValue sevm) (permitNonceReadH sevm b (permitOwner sevm)) (permitDeadline sevm)
  have mC := permitDigestMemory_ptr mB (b.getStorVal sevm.currentTarget 3)
    (permitInner (permitOwner sevm) (permitSpender sevm) (permitValue sevm)
      (permitNonceReadH sevm b (permitOwner sevm)) (permitDeadline sevm))
  obtain ⟨a, nonce, rest⟩ := of_run_append permitNonceLine line
  obtain ⟨_, _, state⟩ := permitNonceLine_invH stateGas bal mem nonce
  rw [state] at rest
  obtain ⟨b', struct, rest⟩ := of_run_append permitStructLine rest
  obtain ⟨_, state⟩ := permitStructLine_inv mA rA struct
  rw [state] at rest
  obtain ⟨c', digest, request⟩ := of_run_append permitDigestLine rest
  obtain ⟨_, state⟩ := permitDigestLine_inv mB rB digest
  rw [state] at request
  obtain ⟨G', state⟩ := permitRequestLine_inv mC request
  exact ⟨G', state⟩


theorem permit_request_cursor_stateH {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (selector : Blanc.Sevm.selector sevm = 0xd505accf)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (CursorStateAt code cert
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
      (.next (.reg .gas) (.next (.exec .staticcall) permitRecoveryTail))
      (permitNonceWorldH sevm b (permitOwner sevm))
      (1 :: 482 :: 128 :: 450 :: 32 :: permitPublicCallStackH sevm b 0xd505accf)
      (permitPublicCallMemoryH sevm b) [t_0257_c76]) := by
  obtain ⟨body⟩ := permit_body_cursor_stateH codeEq stateGas bal selector run
  obtain ⟨body⟩ := body.destH cert_check rfl stateGas
  exact body.lineH cert_check rfl stateGas permitRequestPrefixLine (by rfl)
    (by
      intro n member x equal
      subst n
      simp only [permitRequestPrefixLine, permitNonceLine, permitStructLine,
        permitDigestLine, permitRequestLine, List.mem_append, List.mem_cons,
        List.not_mem_nil, reduceCtorEq, or_self] at member)
    (permit_request_prefix_line_invH stateGas bal)


theorem permit_call_cursor_stateH {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (selector : Blanc.Sevm.selector sevm = 0xd505accf)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    ∃ gw : B256, Nonempty (CursorStateAt code cert
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
      (.next (.exec .staticcall) permitRecoveryTail)
      (permitNonceWorldH sevm b (permitOwner sevm))
      (gw :: 1 :: 482 :: 128 :: 450 :: 32 :: permitPublicCallStackH sevm b 0xd505accf)
      (permitPublicCallMemoryH sevm b) [t_0257_c76]) := by
  obtain ⟨gas⟩ := permit_request_cursor_stateH codeEq stateGas bal selector run
  obtain ⟨N, κ', edge, _, primitive, synthetic, _, placed⟩ :=
    cursor_next_forwardH cert_check gas.placed gas.tree gas.exn_eq (gas.sevm_eq ▸ stateGas)
  have actual : Ninst.Run sevm gas.node.devm (.reg .gas) N.devm := by
    simpa only [gas.sevm_eq] using primitive.toRun
  obtain ⟨g, state⟩ := gas.state
  rw [state] at actual
  obtain ⟨gw, g', state⟩ := ri_gas actual
  have treeK : κ'.f = .next (.exec .staticcall) permitRecoveryTail ∧
      κ'.K = gas.cursor.K := by
    have tree := gas.tree
    generalize original : gas.cursor = κ at synthetic tree ⊢
    rcases κ with ⟨f, pc, a, m, K⟩
    change f = .next (.reg .gas) (.next (.exec .staticcall) permitRecoveryTail) at tree
    subst f
    cases synthetic
    exact ⟨rfl, rfl⟩
  have sameExn : N.exn = gas.node.exn := by
    generalize origin : gas.node = F at edge ⊢
    cases edge <;> rfl
  refine ⟨gw, ⟨⟨N, κ', gas.free.trans (.ofStep edge ?_),
    (Cursor.parentStep_sevm edge).trans gas.sevm_eq, sameExn.trans gas.exn_eq,
    placed, treeK.1, ⟨g', state⟩, ?_⟩⟩⟩
  · intro x decoded
    have impossible := (gas.placed.ninstAt_of_next gas.tree).symm.trans decoded
    cases impossible
  · rw [treeK.2]
    exact gas.continuations


end Blanc.Lift.UniswapV2Pair
