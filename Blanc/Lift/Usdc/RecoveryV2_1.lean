import Blanc.Lift.Usdc.ImplV2_1.Check
import Blanc.Lift.EcrecoverCall

/-! Actual V2_1 specialization of the common recovery engine. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift

private def recoveryLayout : EcrecoverCall.ReturnLayout :=
  ⟨[0x4a, 0x89], by decide, [0x4b, 0x36], by decide,
    ImplV2_1.t_4a80_c7, ImplV2_1.t_4ad0_c7⟩

private theorem recovery_layout_checked : EcrecoverCall.ReturnChecks recoveryLayout := by
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem recovery_source_shape :
    ImplV2_1.t_4a2d_c7 = EcrecoverCall.entry recoveryLayout := by
  rfl

/-- A successful actual V2_1 recovery return consumes the answer to its own
address-1 invocation. The concrete entry registers, free pointer, nondelegation
and checked caller are local producer obligations; they are not final history
or environmental hypotheses. This theorem does not enumerate flag-zero calls. -/
theorem recoveryV2_1_consumes
    {F : Exec.Deriv} {κ : Cursor} {post b : Devm} {M : Mem} {G n : Nat}
    {p placeholder s r v digest ret : B256} {S : List B256}
    {caller : SFunc} {K : List SFunc}
    (ok : CursorOK ImplV2_1.code ImplV2_1.cert F κ)
    (tree : κ.f = ImplV2_1.t_4a2d_c7) (pc : F.pc = 0x4a2d)
    (state : F.devm = St b (placeholder :: s :: r :: v :: digest :: ret :: S) M G)
    (ptr : PtrMem p n M) (lower : 96 ≤ p.toNat)
    (space : p.toNat + 160 < 2 ^ 256)
    (nodeleg : getDelegatedCodeAddress (b.getCode 1) = none)
    (continuations : κ.K.map Cont.f = caller :: K)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ (call : CallOccurrenceStep F .staticcall) (parent child : Devm)
      (gas : Nat) (adr : Adr) (N : Exec.Deriv) (next : Cursor),
      let input := digest.toBytes ++ (255 &&& v).toBytes ++ r.toBytes ++ s.toBytes
      let msg := callMsg call.occurrence.node.sevm parent gas 0
        call.occurrence.node.sevm.currentTarget 1 1 true true input
        (call.occurrence.node.devm.getCode 1) false
      call.occurrence.node.pc = 0x4a78 ∧
      Exec.Deriv.ExecFreeUntil F call.occurrence.node ∧
      Ninst.step ⟨call.occurrence.node.pc, call.occurrence.node.sevm, call.occurrence.node.devm⟩
        (.exec .staticcall) = .spawn (Frame.ofCall msg)
          (Resume.call parent p.toNat 32) (call.occurrence.node.pc + 1) ∧
      ProcessMessage msg call.occurrence.slot (.ok child) ∧
      call.occurrence.slot = .none ∧
      (Frame.ofCall msg).enter = .done
        ((Frame.ofCall msg).settle (executePrecomp (initEvm (msg.withBenv msg.benv)) 1)) ∧
      gasEcrecover ≤ gas ∧ child.error.isSome = false ∧
      child.output = adr.toB256.toBytes ∧
      ecrecoverOutput input = adr.toB256.toBytes ∧ adr ≠ 0 ∧
      call.returned.devm.returnData = adr.toB256.toBytes ∧
      Exec.Deriv.ExecFreeUntil call.returned N ∧
      N.exn = F.exn ∧ N.sevm = F.sevm ∧
      CursorOK ImplV2_1.code ImplV2_1.cert N next ∧
      next.f = caller ∧ next.K.map Cont.f = K ∧ N.devm.stack = adr.toB256 :: S := by
  have placedTree : κ.f = EcrecoverCall.entry recoveryLayout :=
    tree.trans recovery_source_shape
  have result := EcrecoverCall.consumes ImplV2_1.cert_check recoveryLayout
    recovery_layout_checked ok placedTree state ptr lower space nodeleg continuations success fork
  simpa only [pc] using result

/-- The checked V2_1 owner-comparison continuation accepts only the canonical
address word that it compares with the retained expected-owner register. -/
theorem recoveryV2_1_owner_comparison
    {F : Exec.Deriv} {κ : Cursor} {post : Devm} {adr : Adr}
    {owner : B256} {S : List B256}
    (ok : CursorOK ImplV2_1.code ImplV2_1.cert F κ)
    (tree : κ.f = ImplV2_1.t_421e_c71)
    (stack : F.devm.stack = adr.toB256 :: owner :: S)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    owner = adr.toB256 := by
  have source : ∃ outcome, SFunc.Run ImplV2_1.cert.prog F.sevm F.devm κ.f outcome := by
    rcases ok.sourceRunReturnH ImplV2_1.cert_check success fork.stateGas with halted | returned
    · exact ⟨_, halted.mono StepIn.toRun⟩
    · obtain ⟨continuation, tail, d, actual, sameK, live, smaller, run, placed⟩ := returned
      exact ⟨_, run.mono StepIn.toRun⟩
  obtain ⟨outcome, run⟩ := source
  rw [tree, St.self stack rfl] at run
  unfold ImplV2_1.t_421e_c71 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, state⟩ := ri_and step
  rw [ff20_and_word, toAdr_toB256] at state
  subst state
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_eq step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_push step
  rcases rpw_branch run with ⟨_, _, rejected⟩ | ⟨compared, _, _⟩
  · exact ((SFunc.runP_iff_runCutP_nil.mp rejected).false_of_noOk (by rfl)).elim
  · have equal : adr.toB256 = owner := by
      unfold B256.eqCheck at compared
      by_contra different
      exact compared (ite_eq_right different)
    exact equal.symm

/-- Specializing the actual consumer to its actual owner-comparison continuation
binds the precompile answer to that expected owner. It does not prove how the
permit prefix supplied the digest, owner or entry memory. -/
theorem recoveryV2_1_consumes_owner
    {F : Exec.Deriv} {κ : Cursor} {post b : Devm} {M : Mem} {G n : Nat}
    {p placeholder s r v digest ret owner : B256} {S : List B256} {K : List SFunc}
    (ok : CursorOK ImplV2_1.code ImplV2_1.cert F κ)
    (tree : κ.f = ImplV2_1.t_4a2d_c7) (pc : F.pc = 0x4a2d)
    (state : F.devm = St b
      (placeholder :: s :: r :: v :: digest :: ret :: owner :: S) M G)
    (ptr : PtrMem p n M) (lower : 96 ≤ p.toNat)
    (space : p.toNat + 160 < 2 ^ 256)
    (nodeleg : getDelegatedCodeAddress (b.getCode 1) = none)
    (continuations : κ.K.map Cont.f = ImplV2_1.t_421e_c71 :: K)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    ecrecoverOutput (digest.toBytes ++ (255 &&& v).toBytes ++ r.toBytes ++ s.toBytes) =
      owner.toBytes := by
  obtain ⟨call, parent, child, gas, adr, N, next, callPc, beforeSpan, spawned, process,
    emptySlot, native, paid, clean, childOutput, output, nonzero, returnData,
    suffix, sameExn, sameEnv, placed, callerTree, callerK, callerStack⟩ :=
    recoveryV2_1_consumes ok tree pc state ptr lower space nodeleg continuations success fork
  have ownerEq := recoveryV2_1_owner_comparison placed callerTree callerStack
    (sameExn.trans success) (by rw [sameEnv]; exact fork)
  rw [ownerEq]
  exact output

end Blanc.Lift.Usdc
