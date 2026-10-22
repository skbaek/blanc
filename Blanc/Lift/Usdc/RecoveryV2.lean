import Blanc.Lift.Usdc.ImplV2.Check
import Blanc.Lift.EcrecoverCall

/-! Actual V2 specialization; its real4d93 caller is a separate producer obligation. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift

private def recoveryLayout : EcrecoverCall.ReturnLayout :=
  ⟨[0x51, 0x00], by decide, [0x51, 0xad], by decide,
    ImplV2.t_50f7_c6, ImplV2.t_5147_c6⟩

private theorem recovery_layout_checked : EcrecoverCall.ReturnChecks recoveryLayout := by
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem recovery_source_shape :
    ImplV2.t_50a4_c6 = EcrecoverCall.entry recoveryLayout := by
  rfl

/-- A successful actual V2 recovery return consumes the answer to its own
address-1 invocation. The concrete entry registers, free pointer, nondelegation
and checked caller are local producer obligations; they are not final history
or environmental hypotheses. This theorem does not enumerate flag-zero calls. -/
theorem recoveryV2_consumes
    {F : Exec.Deriv} {κ : Cursor} {post b : Devm} {M : Mem} {G n : Nat}
    {p placeholder s r v digest ret : B256} {S : List B256}
    {caller : SFunc} {K : List SFunc}
    (ok : CursorOK ImplV2.code ImplV2.cert F κ)
    (tree : κ.f = ImplV2.t_50a4_c6) (pc : F.pc = 0x50a4)
    (state : F.devm = St b (placeholder :: s :: r :: v :: digest :: ret :: S) M G)
    (ptr : PtrMem p n M) (lower : 96 ≤ p.toNat)
    (space : p.toNat + 160 < 2 ^ 256)
    (nodeleg : getDelegatedCodeAddress (b.getCode 1) = none)
    (continuations : κ.K.map Cont.f = caller :: K)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ (call : CallOccurrenceStep F .staticcall) (parent child : Devm)
      (gas : Nat) (adr : Adr) (N : Exec.Deriv) (next : Cursor),
      let input := digest.toBytes ++ (255 &&& v).toBytes ++ r.toBytes ++ s.toBytes
      let msg := callMsg call.occurrence.node.sevm parent gas 0
        call.occurrence.node.sevm.currentTarget 1 1 true true input
        (call.occurrence.node.devm.getCode 1) false
      call.occurrence.node.pc = 0x50ef ∧
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
      CursorOK ImplV2.code ImplV2.cert N next ∧
      next.f = caller ∧ next.K.map Cont.f = K ∧ N.devm.stack = adr.toB256 :: S := by
  have placedTree : κ.f = EcrecoverCall.entry recoveryLayout :=
    tree.trans recovery_source_shape
  have result := EcrecoverCall.consumes ImplV2.cert_check recoveryLayout
    recovery_layout_checked ok placedTree state ptr lower space nodeleg continuations success fork
  simpa only [pc] using result

end Blanc.Lift.Usdc
