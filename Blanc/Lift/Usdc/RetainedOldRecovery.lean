import Blanc.Lift.Usdc.OldRecoveryRelevance
import Blanc.ExecutionStagedRootFacts
import Blanc.ExecutionStagedFrames
import Blanc.ExecutionInCodeImage

/-! Actual old-owner native queries under globally retained parent frames. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- A globally retained old owner-route query at its actual parent position.
Native OOG, empty answers and arbitrary settled/resumed results are admitted.
Neither a write nor a desired answer defines membership. -/
structure RetainedOldOwnerNativeQuery {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) (P pair : Adr) where
  parent : Exec.Frame
  before : List Exec.Frame
  after : List Exec.Frame
  position : history.settledFrames = before ++ parent :: after
  target : parent.sevm.currentTarget = P
  version : (parent.sevm.code = ImplV2.code ∧ Sevm.selector parent.sevm ∈ selV2.owners) ∨
    (parent.sevm.code = ImplV2_1.code ∧ Sevm.selector parent.sevm ∈ selV2_1.owners)
  owner : (Sevm.dataWord parent.sevm 4).toAdr = pair
  occurrence : Exec.NinstOccurrence (Blanc.Exec.Frame.rootDeriv parent)
  sameFrame : Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv parent) occurrence.node
  instruction : occurrence.instruction = .exec .staticcall
  site : (parent.sevm.code = ImplV2.code ∧ occurrence.node.pc = 0x50ef) ∨
    (parent.sevm.code = ImplV2_1.code ∧ occurrence.node.pc = 0x4a78)
  message : Msg
  resume : Resume
  settled : Except (EvmError × State × AdrSet × Tra) Devm
  spawn : Ninst.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩
    (.exec .staticcall) = .spawn (Frame.ofCall message) resume (occurrence.node.pc + 1)
  process : ProcessMessage message occurrence.slot settled
  resumed : resume.run settled = occurrence.stepResult
  routing : StaticcallRouting message occurrence.slot settled
  address : message.codeAddress = some 1
  enabled : message.disablePrecompiles = false
  native : executeCode.enter message = .inr (executePrecomp (initEvm message) 1)

namespace RetainedOldOwnerNativeQuery

/-- The entered machine belongs to the original actual spawning message. -/
def actualEvm {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {history : ConfiguredHistoryTraceIn F cfg checkpoint future} {P pair : Adr}
    (query : RetainedOldOwnerNativeQuery history P pair) : Evm := initEvm query.message

/-- Membership retains the exact settled parent, including its list position. -/
theorem parent_mem {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {history : ConfiguredHistoryTraceIn F cfg checkpoint future} {P pair : Adr}
    (query : RetainedOldOwnerNativeQuery history P pair) : query.parent ∈ history.settledFrames := by
  rw [query.position]
  exact List.mem_append_right _ List.mem_cons_self

/-- The same original node is retained under an actual settled history root;
a locally successful raw parent is never used as a global-retention shortcut. -/
theorem global_retention {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {history : ConfiguredHistoryTraceIn F cfg checkpoint future} {P pair : Adr}
    (query : RetainedOldOwnerNativeQuery history P pair) :
    ∃ root ∈ history.settledRoots, query.parent ∈ Exec.committedFrames root.run ∧
      query.occurrence.node ∈ Exec.retainedNodes root.run := by
  have member := query.parent_mem
  rw [history.settledFrames_eq] at member
  obtain ⟨root, rootMember, parentMember⟩ := List.mem_flatMap.mp member
  exact ⟨root, rootMember, parentMember,
    (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix root.run _).mpr
      ⟨query.parent, parentMember, query.sameFrame⟩⟩

/-- The original occurrence gives the all-outcome observer without filtering. -/
theorem observation {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {history : ConfiguredHistoryTraceIn F cfg checkpoint future} {P pair : Adr}
    (query : RetainedOldOwnerNativeQuery history P pair) :
    StaticcallObservation query.occurrence.node.pc query.occurrence.node.sevm
      query.occurrence.node.devm query.occurrence.slot query.occurrence.stepResult :=
  query.occurrence.staticcall_observation query.instruction

end RetainedOldOwnerNativeQuery

/-- Every retained V2 or V2_1 owner-route parent produces its actual Pair query
at the supplied global position. Fresh entry is derived from the history;
no tracked write, final-answer or local-query premise is supplied. -/
theorem ConfiguredHistoryTraceIn.retained_old_owner_pair_query_at_effective
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ f, F f → f.ruleSet.bal = none)
    {P pair : Adr} {G : Exec.Frame} {before after : List Exec.Frame}
    (position : history.settledFrames = before ++ G :: after)
    (target : G.sevm.currentTarget = P)
    (version : (G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
      (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners))
    (owner : (Sevm.dataWord G.sevm 4).toAdr = pair)
    (ready : G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none) :
    ∃ query : RetainedOldOwnerNativeQuery history P pair,
      query.parent = G ∧ query.before = before ∧ query.after = after ∧
      executeEcrecover query.actualEvm = .ok gasEcrecover pair.toB256.toBytes := by
  have member : G ∈ history.settledFrames := by
    rw [position]
    exact List.mem_append_right _ List.mem_cons_self
  have rawMember := history.mem_rawFrames_of_mem_settledFrames G member
  obtain ⟨pc, selected, stateGas, fresh, _⟩ := history.rawFrame_entryFacts capabilities _ rawMember
  have success : (Blanc.Exec.Frame.rootDeriv G).exn = .ok G.post := by
    rcases G with ⟨pc, sevm, pre, out, run, committed⟩
    cases out with
    | ok post => rfl
    | error error => cases committed
  obtain ⟨call, parent, child, gas, input, pointer, Q, next,
      _, _, callEnv, spawned, process, emptySlot, address, enabled, paid, clean,
      childOutput, nonzero, returnData, observation, routing, execution, native,
      settlement, resumed, answer, retained, suffix, comparison, source⟩ :=
    old_owner_pair_native_effective pc fresh.1 fresh.2 version ready success
      ⟨stateGas, bal _ selected⟩ owner
  let message := callMsg call.occurrence.node.sevm parent gas 0
    call.occurrence.node.sevm.currentTarget 1 1 true true input
    (call.occurrence.node.devm.getCode 1) false
  have site : (G.sevm.code = ImplV2.code ∧ call.occurrence.node.pc = 0x50ef) ∨
      (G.sevm.code = ImplV2_1.code ∧ call.occurrence.node.pc = 0x4a78) := by
    rcases source with ⟨code, op, selector, data, ptr, pc, placed, tree⟩ |
      ⟨code, data, ptr, pc, placed, tree⟩
    · exact .inl ⟨code, pc⟩
    · exact .inr ⟨code, pc⟩
  let query : RetainedOldOwnerNativeQuery history P pair :=
    { parent := G, before := before, after := after, position := position,
      target := target, version := version, owner := owner,
      occurrence := call.occurrence, sameFrame := call.sameFrame,
      instruction := call.instruction, site := site, message := message,
      resume := .call parent pointer 32, settled := .ok child, spawn := spawned,
      process := process, resumed := resumed, routing := routing,
      address := address, enabled := enabled, native := execution }
  exact ⟨query, rfl, rfl, rfl, answer⟩

/-- Pure nondelegation retains the original retained-query interface. -/
theorem ConfiguredHistoryTraceIn.retained_old_owner_pair_query_at
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ f, F f → f.ruleSet.bal = none)
    {P pair : Adr} {G : Exec.Frame} {before after : List Exec.Frame}
    (position : history.settledFrames = before ++ G :: after)
    (target : G.sevm.currentTarget = P)
    (version : (G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
      (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners))
    (owner : (Sevm.dataWord G.sevm 4).toAdr = pair)
    (nodeleg : getDelegatedCodeAddress (G.pre.getCode 1) = none) :
    ∃ query : RetainedOldOwnerNativeQuery history P pair,
      query.parent = G ∧ query.before = before ∧ query.after = after ∧
      executeEcrecover query.actualEvm = .ok gasEcrecover pair.toB256.toBytes := by
  have ready : G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none := by
    simp only [ForkRules.delegatedCodeAddress, nodeleg, ite_self]
  exact ConfiguredHistoryTraceIn.retained_old_owner_pair_query_at_effective history capabilities bal position target version owner ready


/-- Membership-form projection, retaining an actual parent position in the
returned query. Coverage is both checked old owner tables. -/
theorem ConfiguredHistoryTraceIn.retained_old_owner_has_pair_query_effective
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ f, F f → f.ruleSet.bal = none)
    {P pair : Adr} {G : Exec.Frame} (member : G ∈ history.settledFrames)
    (target : G.sevm.currentTarget = P)
    (version : (G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
      (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners))
    (owner : (Sevm.dataWord G.sevm 4).toAdr = pair)
    (ready : G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none) :
    ∃ query : RetainedOldOwnerNativeQuery history P pair, query.parent = G ∧
      executeEcrecover query.actualEvm = .ok gasEcrecover pair.toB256.toBytes := by
  obtain ⟨before, after, position⟩ := List.append_of_mem member
  obtain ⟨query, parent, _, _, answer⟩ := ConfiguredHistoryTraceIn.retained_old_owner_pair_query_at_effective history capabilities bal
    position target version owner ready
  exact ⟨query, parent, answer⟩

/-- Pure nondelegation retains the original retained-query interface. -/
theorem ConfiguredHistoryTraceIn.retained_old_owner_has_pair_query
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ f, F f → f.ruleSet.bal = none)
    {P pair : Adr} {G : Exec.Frame} (member : G ∈ history.settledFrames)
    (target : G.sevm.currentTarget = P)
    (version : (G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
      (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners))
    (owner : (Sevm.dataWord G.sevm 4).toAdr = pair)
    (nodeleg : getDelegatedCodeAddress (G.pre.getCode 1) = none) :
    ∃ query : RetainedOldOwnerNativeQuery history P pair, query.parent = G ∧
      executeEcrecover query.actualEvm = .ok gasEcrecover pair.toB256.toBytes := by
  have ready : G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none := by
    simp only [ForkRules.delegatedCodeAddress, nodeleg, ite_self]
  exact ConfiguredHistoryTraceIn.retained_old_owner_has_pair_query_effective history capabilities bal member target version owner ready


/-- The approved retained-query exclusion rules out the Pair as calldata
owner on either old owner table. It is applied only to this exact universe. -/
theorem ConfiguredHistoryTraceIn.retained_old_owner_not_pair_effective
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ f, F f → f.ruleSet.bal = none)
    {P pair : Adr}
    (excluded : ∀ query : RetainedOldOwnerNativeQuery history P pair,
      executeEcrecover query.actualEvm ≠ .ok gasEcrecover pair.toB256.toBytes)
    {G : Exec.Frame} (member : G ∈ history.settledFrames)
    (target : G.sevm.currentTarget = P)
    (version : (G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
      (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners))
    (ready : G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none) :
    (Sevm.dataWord G.sevm 4).toAdr ≠ pair := by
  intro owner
  obtain ⟨query, _, answer⟩ := ConfiguredHistoryTraceIn.retained_old_owner_has_pair_query_effective
    history capabilities bal member target version owner ready
  exact excluded query answer

/-- Pure nondelegation retains the original retained-query interface. -/
theorem ConfiguredHistoryTraceIn.retained_old_owner_not_pair
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ f, F f → f.ruleSet.bal = none)
    {P pair : Adr}
    (excluded : ∀ query : RetainedOldOwnerNativeQuery history P pair,
      executeEcrecover query.actualEvm ≠ .ok gasEcrecover pair.toB256.toBytes)
    {G : Exec.Frame} (member : G ∈ history.settledFrames)
    (target : G.sevm.currentTarget = P)
    (version : (G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
      (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners))
    (nodeleg : getDelegatedCodeAddress (G.pre.getCode 1) = none) :
    (Sevm.dataWord G.sevm 4).toAdr ≠ pair := by
  have ready : G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none := by
    simp only [ForkRules.delegatedCodeAddress, nodeleg, ite_self]
  exact ConfiguredHistoryTraceIn.retained_old_owner_not_pair_effective history capabilities bal excluded member target version ready

end Blanc.Lift.Usdc
