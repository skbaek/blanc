import Blanc.Lift.StaticOnlyRoots
import Blanc.Lift.ChildFrameCode
import Blanc.StaticStorage

/-!
# What a frame whose foreign frames are static keeps

A static frame makes no successful `SSTORE` and is no `CREATE` frame, so an execution retains a write
to, or replaces the code at, an address only through a non-static or creating frame there.

* `Exec.noRetainedWriteTo_of_owner_frames_static`: every entered frame at the owner is static, so no
  retained write reaches it;
* `Exec.staticOnly_rawFrameDescendants_static`: below a frame of certified code that executes only
  `STATICCALL`, every entered frame is static and has a code address;
* `KeepsForeign`, `keepsForeign_of_staticOnly`: a committed frame of such code keeps the storage of
  every other address with code and the code of every other address.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune Blanc

/-- If every entered frame at `owner` is static, no retained write targets `owner`. -/
theorem Exec.noRetainedWriteTo_of_owner_frames_static {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) (owner : Adr) (key : B256)
    (static : ∀ r ∈ Exec.rawFrameRoots run, r.sevm.currentTarget = owner → r.sevm.isStatic = true) :
    Exec.NoRetainedWriteTo run owner key := by
  intro event member matchEq
  rcases Exec.exists_successfulSstore_of_mem_retainedStorageWrites
      (root := (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv)) (event := event) member with
    ⟨write, -, writeEq⟩
  subst event
  rcases (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix run write.occurrence.node).mp
      write.occurrence.reached with ⟨r, hr, sameFrame⟩
  have hs := Blanc.Exec.Deriv.ParentPrefix.sevm_eq sameFrame
  have ownerEq := (Exec.StorageWrite.matches_eq_true.mp matchEq).1
  change write.occurrence.node.sevm.currentTarget = owner at ownerEq
  have nodeStatic : write.occurrence.node.sevm.isStatic = true := by
    rw [hs]
    exact static r hr (by rw [← hs]; exact ownerEq)
  have storeRun : Ninst.Run write.occurrence.node.sevm write.occurrence.node.devm (.reg .sstore)
      write.stepPost := by
    refine ⟨write.occurrence.slot, write.occurrence.filled, write.occurrence.node.pc, ?_⟩
    simpa only [write.instruction_eq, write.stepSuccess] using write.occurrence.stepRun
  have nonstatic := of_run_sstore_not_static storeRun
  rw [nodeStatic] at nonstatic
  exact Bool.noConfusion nonstatic

/-- A frame entered from a same-frame node of certified code that executes only `STATICCALL` is
static, has a code address, and enters only such frames. -/
private theorem staticOnly_child {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true)
    (only : ∀ f ∈ c.prog, f.execsSatisfy Xinst.isStaticcall = true)
    {root : Exec.Deriv} (pc0 : root.pc = 0) (installed : root.sevm.code = code)
    (rootFork : CoveredFork root.sevm.benvStat.fork)
    {nodePc nextPc : Nat} {nodeSevm : Sevm} {nodePre : Devm} {out raw : Execution} {frame : Frame}
    {rsm : Resume} {cevm : Evm} {run : Exec nodePc nodeSevm nodePre out}
    (chain : Exec.Deriv.ParentPrefix root ⟨nodePc, nodeSevm, nodePre, out, run⟩)
    (step : Evm.step ⟨nodePc, nodeSevm, nodePre⟩ = .spawn frame rsm nextPc)
    (enter : frame.enter = .run cevm) (child : Exec cevm.pc cevm.sta cevm.dyna raw) :
    cevm.sta.isStatic = true ∧ cevm.sta.codeAddress ≠ none ∧
      ∀ D ∈ Exec.rawFrameRoots child, D.sevm.isStatic = true ∧ D.sevm.codeAddress ≠ none := by
  have sevmEq : nodeSevm = root.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  have fork : CoveredFork nodeSevm.benvStat.fork := by rw [sevmEq]; exact rootFork
  obtain ⟨x, instruction, spawn, _⟩ := Evm.step_spawn_inv step
  have onlyStatic : x = .staticcall :=
    parentPrefix_exec_staticcall_of_cert checked only pc0 installed rootFork chain instruction
  subst x
  have fst := Xinst.step_staticcall_spawn_isStatic spawn
  have stc : cevm.sta.isStatic = true := (Frame.enter_run_isStatic enter).trans fst
  obtain ⟨_, _, hcev⟩ := Frame.enter_run_inv enter
  have cca : cevm.sta.codeAddress ≠ none := by
    rw [hcev]; exact Xinst.step_spawn_codeAddress_of_static fork spawn fst
  exact ⟨stc, cca, Exec.static_rawFrameRoots child (Evm.step_spawn_child_fork step enter fork) stc cca⟩

/-- **Below a frame of certified code that executes only `STATICCALL`, every entered frame is static
and has a code address.** -/
theorem Exec.staticOnly_rawFrameDescendants_static {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true)
    (only : ∀ f ∈ c.prog, f.execsSatisfy Xinst.isStaticcall = true)
    {root : Exec.Deriv} (pc0 : root.pc = 0) (installed : root.sevm.code = code)
    (rootFork : CoveredFork root.sevm.benvStat.fork) :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      Exec.Deriv.ParentPrefix root ⟨pc, sevm, pre, out, run⟩ →
      ∀ D ∈ Exec.rawFrameDescendants run, D.sevm.isStatic = true ∧ D.sevm.codeAddress ≠ none := by
  intro pc sevm pre out run
  induction run with
  | halt step => simp only [Exec.rawFrameDescendants, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true]
  | cont step next ih =>
    intro chain
    simpa only [Exec.rawFrameDescendants] using ih (chain.snoc (.cont step next))
  | doneErr step enter resume => simp only [Exec.rawFrameDescendants, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true]
  | doneOk step enter resume next ih =>
    intro chain
    simpa only [Exec.rawFrameDescendants] using ih (chain.snoc (.doneOk step enter resume next))
  | @runErr nodePc nodeSevm nodePre frame rsm nextPc cevm raw e step enter child resume ih =>
    intro chain D member
    obtain ⟨stc, cca, roots⟩ := staticOnly_child checked only pc0 installed rootFork chain step enter child
    simp only [Exec.rawFrameDescendants, List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨stc, cca⟩
    · exact roots D (List.mem_cons_of_mem _ member)
  | @runOk nodePc nodeSevm nodePre frame rsm nextPc cevm raw inter final step enter child resume
      next childIH nextIH =>
    intro chain D member
    obtain ⟨stc, cca, roots⟩ := staticOnly_child checked only pc0 installed rootFork chain step enter child
    have nextNodes := nextIH (chain.snoc (.runOk step enter child resume next))
    simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append] at member
    rcases member with rfl | member | member
    · exact ⟨stc, cca⟩
    · exact roots D (List.mem_cons_of_mem _ member)
    · exact nextNodes D member

/-- **A frame's code keeps the foreign world**: every committed frame running it from `pc 0` under a
covered fork keeps the storage of every other address with code and the code of every other
address. -/
def KeepsForeign (code : ByteArray) : Prop :=
  ∀ c : Exec.Frame, c.pc = 0 → c.sevm.code = code → CoveredFork c.sevm.benvStat.fork →
    ∀ {a : Adr}, a ≠ c.sevm.currentTarget →
      ((c.pre.getCode a).toList ≠ [] →
        ∀ key, (c.post.getStor a).get key = (c.pre.getStor a).get key) ∧
        c.post.getCode a = c.pre.getCode a

/-- **Code that executes only `STATICCALL` keeps the foreign world.** -/
theorem keepsForeign_of_staticOnly {code : ByteArray} {cert : Cert}
    (checked : Cert.check code cert = true)
    (only : ∀ f ∈ cert.prog, f.execsSatisfy Xinst.isStaticcall = true) : KeepsForeign code := by
  rintro ⟨cpc, sevm, pre, out, run, committed⟩ hpc hcode hfork a hne
  dsimp only at hpc hcode hfork hne ⊢
  subst hpc
  have hd := Exec.staticOnly_rawFrameDescendants_static checked only
    (root := ⟨0, sevm, pre, out, run⟩) rfl hcode hfork run (.refl _)
  have hroots : ∀ r ∈ Exec.rawFrameRoots run, r.sevm.currentTarget = a →
      r.sevm.isStatic = true ∧ r.sevm.codeAddress ≠ none := by
    intro r hr ht
    simp only [Exec.rawFrameRoots, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact absurd ht.symm hne
    · exact hd r hr
  refine ⟨fun hc key => ?_, ?_⟩
  · exact Exec.committedCell_eq_of_noRetainedWriteTo run committed hfork a key hc
      (Exec.noRetainedWriteTo_of_owner_frames_static run a key fun r hr ht => (hroots r hr ht).1)
  · have hrel := (Exec.codeAt_avoid (a := a) run hfork fun r hr hnone ht =>
      (hroots r hr ht).2 hnone).1
    cases out with
    | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
    | ok post => exact hrel

end Blanc.Lift
