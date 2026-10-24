import Blanc.Lift.Usdc.AllowanceRawHistory
import Blanc.StaticcallObservation
import Blanc.Lift.Usdc.PermitRowPrefixV2_1

/-! The actual V2_1 native owner answer before a tracked allowance write. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift

/-- The listed pre-authentication nonce site is separated from every tracked
allowance row by the existing finite row-separation interface. -/
theorem permitV2_1_nonce_apart_tracked {sevm : Sevm} {pair g : Adr} {Tr : Adr → Prop}
    (selector : Sevm.selector sevm = 0xd505accf)
    (sep : WriteSite.RowSep 10 pair.toB256 (AllowKey Tr)
      (WriteSite.wsRoot ImplV2_1Ws.implWsAnn) (WriteSite.Env.root sevm))
    (tracked : Tr g) : nonceSlot (Sevm.dataWord sevm 4).toAdr ≠ allowSlot pair g := by
  let site : WriteSite.Site :=
    ⟨.kecc ownerWordT (.const 17), [(selV2T, 0xd505accf)], false⟩
  have member : site ∈ WriteSite.wsRoot ImplV2_1Ws.implWsAnn := by
    exact mem_of_getElem?_eq_some (i := 28) rfl
  have guards : site.GuardsHold (WriteSite.Env.root sevm) := by
    intro guard member known
    have equal : guard = (selV2T, 0xd505accf) := List.mem_singleton.mp member
    subst guard
    simpa only [selV2T, WriteSite.Term.eval, WriteSite.Op2.eval, WriteSite.Env.root,
      Sevm.selector, Sevm.dataWord, show (224 : B256).toNat = 224 from rfl] using selector.symm
  have apart := sep.other site member rfl guards rfl rfl g.toB256 ⟨g, tracked, rfl⟩
  have owner : ownerWordT.eval (WriteSite.Env.root sevm) = (Sevm.dataWord sevm 4).toAdr.toB256 := by
    rw [ownerWordT, addrMaskT_eval]
    rfl
  change mapSlot (ownerWordT.eval (WriteSite.Env.root sevm)) 17 ≠ allowSlot pair g at apart
  rw [owner] at apart
  exact apart

/-- A tracked raw permit write forces an actual native answer for the
calldata owner at the original execution root, even if that frame later
reverts. Finite row separation excludes the earlier nonce write. -/
theorem permitV2_1_tracked_sstore_native {F target : Exec.Deriv}
    {pair g : Adr} {Tr : Adr → Prop} {w : Exec.StorageWrite}
    (pc : F.pc = 0) (code : F.sevm.code = ImplV2_1.code)
    (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (selector : Sevm.selector F.sevm = 0xd505accf)
    (path : Exec.Deriv.ParentPrefix F target)
    (found : Exec.Deriv.successfulSstore? target = some w)
    (key : w.key = allowSlot pair g) (tracked : Tr g)
    (sep : WriteSite.RowSep 10 pair.toB256 (AllowKey Tr)
      (WriteSite.wsRoot ImplV2_1Ws.implWsAnn) (WriteSite.Env.root F.sevm))
    (owner : (Sevm.dataWord F.sevm 4).toAdr = pair)
    (nodeleg : getDelegatedCodeAddress (F.devm.getCode 1) = none)
    (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ (R : Exec.Deriv) (original : CallOccurrenceStep R .staticcall)
      (origin : Exec.Deriv.ExecFreeUntil F R) (call : CallOccurrenceStep F .staticcall)
      (parent child : Devm) (gas : Nat) (input : Bytes) (Q : Exec.Deriv) (next : Cursor),
      let msg := callMsg call.occurrence.node.sevm parent gas 0
        call.occurrence.node.sevm.currentTarget 1 1 true true input
        (call.occurrence.node.devm.getCode 1) false
      call = original.reRoot origin.1 ∧
      call.occurrence.node = original.occurrence.node ∧
      call.occurrence.instruction = original.occurrence.instruction ∧
      call.occurrence.slot = original.occurrence.slot ∧
      call.occurrence.stepResult = original.occurrence.stepResult ∧ call.returned = original.returned ∧
      R.pc = 0x4a2d ∧ call.occurrence.node.pc = 0x4a78 ∧ call.occurrence.node.sevm = F.sevm ∧
      Exec.Deriv.ExecFreeUntil F call.occurrence.node ∧
      Exec.Deriv.ParentPrefix call.returned Q ∧ Exec.Deriv.ParentPrefix Q target ∧
      Ninst.step ⟨call.occurrence.node.pc, call.occurrence.node.sevm, call.occurrence.node.devm⟩
        (.exec .staticcall) = .spawn (Frame.ofCall msg)
          (Resume.call parent 450 32) (call.occurrence.node.pc + 1) ∧
      ProcessMessage msg call.occurrence.slot (.ok child) ∧ call.occurrence.slot = .none ∧
      (Frame.ofCall msg).enter = .done ((Frame.ofCall msg).settle
        (executePrecomp (initEvm msg) 1)) ∧
      gasEcrecover ≤ gas ∧ child.error.isSome = false ∧ child.output = pair.toB256.toBytes ∧
      ecrecoverOutput input = pair.toB256.toBytes ∧ pair ≠ 0 ∧
      call.returned.devm.returnData = pair.toB256.toBytes ∧
      executeEcrecover (initEvm msg) = .ok gasEcrecover pair.toB256.toBytes ∧
      StaticcallObservation call.occurrence.node.pc call.occurrence.node.sevm
        call.occurrence.node.devm call.occurrence.slot call.occurrence.stepResult ∧
      CursorOK ImplV2_1.code ImplV2_1.cert Q next ∧ next.f = ImplV2_1.t_421e_c71 ∧
      ∃ S, Q.devm.stack = pair.toB256 :: pair.toB256 :: S := by
  obtain ⟨store, rest, targetStack⟩ := successfulSstore?_decoded found
  have targetHead : target.devm.stack.head? = some (allowSlot pair g) := by
    rw [targetStack, key]
    rfl
  have separated := permitV2_1_nonce_apart_tracked selector sep tracked
  obtain ⟨R, κ, b, M, G, digest, domain, S, entryPc, origin, later, env,
      placed, tree, continuations, state, ptr, codeEq⟩ :=
    permitV2_1_root_recovery_toward_sstore pc code stack memory selector path store
      targetHead separated fork
  have localNodeleg : getDelegatedCodeAddress (b.getCode 1) = none := by
    rw [codeEq]
    exact nodeleg
  obtain ⟨original, parent, child, gas, Q, next, callPc, span, returnSpan, targetSpan,
      spawned, process, emptySlot, native, paid, clean, childOutput, output, nonzero,
      returnData, comparisonPlaced, comparisonTree, comparisonStack⟩ :=
    permitV2_1_recovery_answer_toward_sstore placed tree entryPc state ptr
      (by decide) (by decide) localNodeleg continuations later store (env ▸ fork)
  rw [owner] at childOutput output nonzero returnData comparisonStack
  let call := original.reRoot origin.1
  let input := digest.toBytes ++ (255 &&& (Sevm.dataWord F.sevm 132 &&& 255)).toBytes ++
    (Sevm.dataWord F.sevm 164).toBytes ++ (Sevm.dataWord F.sevm 196).toBytes
  let msg := callMsg call.occurrence.node.sevm parent gas 0
    call.occurrence.node.sevm.currentTarget 1 1 true true input
    (call.occurrence.node.devm.getCode 1) false
  have answer : executeEcrecover (initEvm msg) = .ok gasEcrecover pair.toB256.toBytes := by
    rw [executeEcrecover_eq (evm := initEvm msg) paid]
    exact congrArg (PrecompResult.ok gasEcrecover) output
  exact ⟨R, original, origin, call, parent, child, gas, input, Q, next,
    rfl, rfl, rfl, rfl, rfl, rfl, entryPc, callPc,
    Exec.Deriv.ParentPrefix.sevm_eq call.sameFrame, origin.trans span,
    returnSpan, targetSpan, spawned, process, emptySlot, native, paid, clean,
    childOutput, output, nonzero, returnData, answer,
    call.occurrence.staticcall_observation call.instruction,
    comparisonPlaced, comparisonTree, S, comparisonStack⟩

end Blanc.Lift.Usdc
