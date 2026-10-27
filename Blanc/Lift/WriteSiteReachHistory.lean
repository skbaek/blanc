import Blanc.Lift.WriteSiteReach
import Blanc.Lift.CursorOccurrenceNoStateGas

/-!
# The write-site observation at an attributed history `SSTORE`

`ConfiguredHistoryTraceIn.exists_retainedSstore_frame_wsObs`: the last retained `SSTORE` that
`exists_retainedSstore_frame_sstoreCursor` attributes to a committed raw frame meets a root site
of every write-site certificate of the code that frame runs (`WsObs`, read in the frame's root
environment, at the write's node).  It composes the frame's gas-exact cursor reach with the
prefix soundness `ws_reach_start_noStateGas`; `stateGas = none` comes from
`rawFrame_entryFacts`.  Contract-neutral.
-/

namespace Blanc.Lift.WriteSite

open Jaune

/-- An actual successful store meets a certified root site. The site retains
its guards and its nonincrease guarantee at this same node, even if the frame
later reverts. No separation or eventual-retention premise is needed. -/
theorem successfulSstore_site {code : ByteArray} {c : Cert} {ann : List WAnn}
    (checked : Cert.check code c = true) (certified : wsCert c ann = true)
    {root node : Exec.Deriv} (pc : root.pc = 0) (hcode : root.sevm.code = code)
    (stateGas : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ∃ site ∈ wsRoot ann,
      site.slot.Den (Env.root root.sevm) write.key ∧
      (∀ guard ∈ site.guards, guard.1.Den (Env.root root.sevm) guard.2) ∧
      (site.nonInc = true →
        write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat) := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reached, placed⟩ :=
    reach_of_parentPrefix_noStateGas checked pc hcode stateGas chain
  obtain ⟨g, tree, -⟩ := placed.tree_of_sstore decoded
  have obs := ws_reach_start_noStateGas (fun h => StepIn.toRun h)
    certified stateGas reached tree
  obtain ⟨site, member, den, guards, nonInc⟩ :=
    obs rfl write.key write.value rest stack
  refine ⟨site, member, den, guards, ?_⟩
  rw [Exec.Deriv.ParentPrefix.sevm_eq chain]
  exact nonInc

end Blanc.Lift.WriteSite

namespace Blanc.ExecutionTrace

open Jaune Blanc.Lift Blanc.Lift.WriteSite

/-- Raw-frame membership supplies the entry facts for the actual-store site
producer. The returned inequality uses this node's storage context and
pre-state, not a root-entry cell. -/
theorem ConfiguredHistoryTraceIn.rawFrame_successfulSstore_site {F : Fork → Prop}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {code : ByteArray} {c : Cert} {ann : List WAnn}
    (checked : Cert.check code c = true) (certified : wsCert c ann = true)
    {root node : Exec.Deriv} (member : root ∈ history.rawFrames)
    (hcode : root.sevm.code = code) (chain : Exec.Deriv.ParentPrefix root node)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ∃ site ∈ wsRoot ann,
      site.slot.Den (Env.root root.sevm) write.key ∧
      (∀ guard ∈ site.guards, guard.1.Den (Env.root root.sevm) guard.2) ∧
      (site.nonInc = true →
        write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat) := by
  obtain ⟨pc, -, stateGas, -, -⟩ := history.rawFrame_entryFacts capabilities root member
  exact successfulSstore_site checked certified pc hcode stateGas chain found

/-- **The attributed write meets a root write site.**  The attribution of
`exists_retainedSstore_frame_sstoreCursor`, and, for every certified code of the attributing
frame with an accepted write-site annotation, the write-site observation at the write's node. -/
theorem ConfiguredHistoryTraceIn.exists_retainedSstore_frame_wsObs {F : Fork → Prop}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames)
    (committed : Execution.commits R.exn = true) {owner : Adr} {key : B256}
    (hcode : (R.devm.getCode owner).toList ≠ [])
    (changed : (Devm.getStor R.devm owner).get key ≠
      (Devm.getStor (Execution.committedPost R.exn committed) owner).get key) :
    ∃ (write : Exec.SuccessfulSstoreOccurrence R) (frame : Exec.Frame),
      write.Retained ∧ write.storageOwner = owner ∧ write.key = key ∧
      write.value = (Devm.getStor (Execution.committedPost R.exn committed) owner).get key ∧
      write.IsLastRetained ∧
      frame ∈ Exec.committedFrames R.exc ∧
      Blanc.Exec.Frame.rootDeriv frame ∈ history.rawFrames ∧
      Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv frame) write.occurrence.node ∧
      frame.sevm.currentTarget = owner ∧
      (∃ rest, write.occurrence.node.devm.stack = write.key :: write.value :: rest) ∧
      ∀ {code : ByteArray} {c : Cert} {ann : List WAnn}, Cert.check code c = true →
        wsCert c ann = true → frame.sevm.code = code →
        WsObs (wsRoot ann) (Env.root frame.sevm) frame.sevm write.occurrence.node.devm
          (.reg .sstore) := by
  obtain ⟨write, frame, retained, ownerEq, keyEq, valueEq, last, frameMem, frameRaw, chain,
    target, stack, cursor⟩ :=
    history.exists_retainedSstore_frame_sstoreCursor capabilities member committed hcode changed
  obtain ⟨-, -, hsg, -, -⟩ :=
    history.rawFrame_entryFacts capabilities (Blanc.Exec.Frame.rootDeriv frame) frameRaw
  refine ⟨write, frame, retained, ownerEq, keyEq, valueEq, last, frameMem, frameRaw, chain,
    target, stack, fun checked hw code => ?_⟩
  obtain ⟨κ, g, reached, -, tree⟩ := cursor checked code
  exact ws_reach_start_noStateGas (fun h => StepIn.toRun h) hw hsg reached tree

end Blanc.ExecutionTrace
