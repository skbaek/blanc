import Blanc.Lift.Usdc.RecoveryV2_1
import Blanc.Lift.Usdc.PermitQueryV2_1
import Blanc.Lift.CursorReturnToward

/-!
# V2_1 recovery consumption before a raw allowance write

The local cuts preserve the original prefix to a later SSTORE and allow
the enclosing frame to fail. Root-to-query coverage is a separate producer.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift

/-- The actual owner comparison before a later SSTORE accepts only the
canonical recovered address word. No final execution success is required. -/
theorem permitV2_1_owner_comparison_toward_sstore
    {F target : Exec.Deriv} {κ : Cursor} {adr : Adr} {owner : B256} {S : List B256}
    (placed : CursorOK ImplV2_1.code ImplV2_1.cert F κ)
    (tree : κ.f = ImplV2_1.t_421e_c71)
    (stack : F.devm.stack = adr.toB256 :: owner :: S)
    (path : Exec.Deriv.ParentPrefix F target)
    (store : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (hsg : F.sevm.benvStat.rules.stateGas = none) : owner = adr.toB256 := by
  obtain ⟨last, route, targetPlaced⟩ :=
    cursor_reach_of_parentPrefixH ImplV2_1.cert_check path placed hsg
  obtain ⟨tail, targetTree, _⟩ := targetPlaced.tree_of_sstore store
  have atStore : AtSstore (last.conf target.devm) := ⟨tail, targetTree⟩
  change Reach Ninst.Run ImplV2_1.cert.prog F.sevm
    ⟨F.devm, κ.f, κ.K.map Cont.f⟩ (last.conf target.devm) at route
  rw [tree, St.self stack rfl] at route
  unfold ImplV2_1.t_421e_c71 at route
  obtain ⟨_, route⟩ := rs_dest route atStore
  obtain ⟨_, step, route⟩ := rs_next route atStore
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, route⟩ := rs_next route atStore
  obtain ⟨_, state⟩ := ri_and step
  rw [ff20_and_word, toAdr_toB256] at state
  subst state
  obtain ⟨_, step, route⟩ := rs_next route atStore
  obtain ⟨_, rfl⟩ := ri_eq step
  obtain ⟨_, step, route⟩ := rs_next route atStore
  obtain ⟨_, rfl⟩ := ri_push step
  rcases rs_branch route atStore with ⟨_, _, rejected⟩ | ⟨compared, _, _⟩
  · exact (Reach.false_of_sstoreFree_halting rejected atStore rfl rfl).elim
  · have equal : adr.toB256 = owner := by
      unfold B256.eqCheck at compared
      by_contra different
      exact compared (ite_eq_right different)
    exact equal.symm

/-- The actual V2_1 recovery call and real owner comparison before a later
SSTORE consume the native answer for the saved owner. These are local query
registers, not a root-to-query coverage premise for a history theorem. -/
theorem permitV2_1_recovery_answer_toward_sstore
    {F target : Exec.Deriv} {κ : Cursor} {b : Devm} {M : Mem} {G n : Nat}
    {p placeholder s r v digest domain : B256} {owner : Adr} {S : List B256} {K : List SFunc}
    (placed : CursorOK ImplV2_1.code ImplV2_1.cert F κ)
    (tree : κ.f = ImplV2_1.t_4a2d_c7) (pc : F.pc = 0x4a2d)
    (state : F.devm = St b
      (placeholder :: s :: r :: v :: digest :: 0x471c :: digest :: 0 :: 128 ::
        s :: r :: v :: domain :: 0x421e :: owner.toB256 :: S) M G)
    (ptr : PtrMem p n M) (lower : 96 ≤ p.toNat) (space : p.toNat + 160 < 2 ^ 256)
    (nodeleg : getDelegatedCodeAddress (b.getCode 1) = none)
    (continuations : κ.K.map Cont.f = ImplV2_1.t_471c_c83 :: ImplV2_1.t_421e_c71 :: K)
    (path : Exec.Deriv.ParentPrefix F target)
    (store : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ (call : CallOccurrenceStep F .staticcall) (parent child : Devm) (gas : Nat)
      (Q : Exec.Deriv) (next : Cursor),
      let input := digest.toBytes ++ (255 &&& v).toBytes ++ r.toBytes ++ s.toBytes
      let msg := callMsg call.occurrence.node.sevm parent gas 0
        call.occurrence.node.sevm.currentTarget 1 1 true true input
        (call.occurrence.node.devm.getCode 1) false
      call.occurrence.node.pc = 0x4a78 ∧
      Exec.Deriv.ExecFreeUntil F call.occurrence.node ∧
      Exec.Deriv.ParentPrefix call.returned Q ∧ Exec.Deriv.ParentPrefix Q target ∧
      Ninst.step ⟨call.occurrence.node.pc, call.occurrence.node.sevm, call.occurrence.node.devm⟩
        (.exec .staticcall) = .spawn (Frame.ofCall msg)
          (Resume.call parent p.toNat 32) (call.occurrence.node.pc + 1) ∧
      ProcessMessage msg call.occurrence.slot (.ok child) ∧ call.occurrence.slot = .none ∧
      (Frame.ofCall msg).enter = .done
        ((Frame.ofCall msg).settle (executePrecomp (initEvm (msg.withBenv msg.benv)) 1)) ∧
      gasEcrecover ≤ gas ∧ child.error.isSome = false ∧ child.output = owner.toB256.toBytes ∧
      ecrecoverOutput input = owner.toB256.toBytes ∧ owner ≠ 0 ∧
      call.returned.devm.returnData = owner.toB256.toBytes ∧
      CursorOK ImplV2_1.code ImplV2_1.cert Q next ∧ next.f = ImplV2_1.t_421e_c71 ∧
      Q.devm.stack = owner.toB256 :: owner.toB256 :: S := by
  let layout : EcrecoverCall.ReturnLayout :=
    ⟨[0x4a, 0x89], by decide, [0x4b, 0x36], by decide,
      ImplV2_1.t_4a80_c7, ImplV2_1.t_4ad0_c7⟩
  have checks : EcrecoverCall.ReturnChecks layout := ⟨rfl, rfl, rfl, rfl⟩
  have helperTree : κ.f = EcrecoverCall.entry layout := tree.trans rfl
  obtain ⟨call, parent, child, gas, adr, N, cursor, callPc, span, returnSpan, later,
      spawned, process, emptySlot, native, paid, clean, childOutput, output,
      nonzero, returnData, finalPlaced, callerTree, callerK, callerStack⟩ :=
    EcrecoverCall.consumes_toward_sstore ImplV2_1.cert_check checks placed helperTree state
      ptr lower space nodeleg continuations rfl path store fork
  have env : N.sevm = F.sevm :=
    (Exec.Deriv.ParentPrefix.sevm_eq returnSpan).trans
      ((Cursor.parentStep_sevm call.edge).trans (Exec.Deriv.ParentPrefix.sevm_eq span.1))
  obtain ⟨Q, next, epilogue, targetSpan, comparisonPlaced, comparisonTree, _, returned⟩ :=
    finalPlaced.returnBeforeSstore_noStateGas ImplV2_1.cert_check (E := []) rfl later store
      (by rw [env]; exact fork.stateGas) (by rw [callerTree]; rfl) callerK
  rw [callerTree, St.self callerStack rfl] at returned
  obtain ⟨gas', returnedState⟩ := SolcSignedQuery.recovery_epilogue returned
  have comparisonStack : Q.devm.stack = adr.toB256 :: owner.toB256 :: S := by
    rw [returnedState, St.stack]
  have wordEq := permitV2_1_owner_comparison_toward_sstore comparisonPlaced comparisonTree
    comparisonStack targetSpan store (by
      rw [Exec.Deriv.ParentPrefix.sevm_eq epilogue, env]
      exact fork.stateGas)
  have ownerEq : owner = adr := Adr.toB256_inj wordEq
  subst adr
  exact ⟨call, parent, child, gas, Q, next, by rw [callPc, pc],
    span, returnSpan.trans epilogue, targetSpan, spawned, process, emptySlot,
    native, paid, clean, childOutput, output, nonzero, returnData,
    comparisonPlaced, comparisonTree, comparisonStack⟩

end Blanc.Lift.Usdc
