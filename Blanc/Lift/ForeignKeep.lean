import Blanc.Lift.ReachChain
import Blanc.Lift.ReachDispatch
import Blanc.Lift.WalkCutKit
import Blanc.Lift.InvWalkLegacy
import Blanc.Lift.HistAccessWalk
import Blanc.ExecutionCodeAt
import Blanc.ExecutionNoninterference
import Blanc.Lift.StaticOnlyRoots
import Blanc.Lift.StaticOnlyFramesIn

/-!
# What a frame keeps when no frame it enters is elsewhere

`FrameKeepsForeign c`: a committed frame leaves alone the storage of every other address with
code at its entry, and the code of every other address.

* `frameKeepsForeign_of_roots`: it does, when every frame it enters runs at its own target;
* `frameKeepsForeign_of_noExec`: so when its chain decodes no external instruction;
* `frameKeeps_of_static`: a static frame keeps the world, and `frameKeepsForeign_of_staticOnly`: a frame of
  certified code executing only `STATICCALL` keeps the foreign world;
* the tactics `rstepN`, `rbranchE`, `rdispE` walk a reach from a certified frame's entry through a
  dispatcher with no storage access, closing as soon as the reach stands in a given exec-free set.
  They read the instruction relation's soundness from `StepIn.toRun` and no fork, so they hold wherever the
  frame's rules have no state gas.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune Blanc

/-- **A frame keeps the foreign world**: the storage of every other address with code at its entry,
and the code of every other address. -/
def FrameKeepsForeign (c : Exec.Frame) : Prop :=
  ∀ {a : Adr}, a ≠ c.sevm.currentTarget →
    ((c.pre.getCode a).toList ≠ [] → ∀ key, (c.post.getStor a).get key = (c.pre.getStor a).get key) ∧
      c.post.getCode a = c.pre.getCode a

/-- A committed frame all of whose entered frames run at its own target keeps the foreign world. -/
theorem frameKeepsForeign_of_roots (c : Exec.Frame)
    (hsg : c.sevm.benvStat.rules.stateGas = none)
    (h : ∀ r ∈ Exec.rawFrameRoots c.run, r.sevm.currentTarget = c.sevm.currentTarget) :
    FrameKeepsForeign c := by
  obtain ⟨cpc, sevm, pre, out, run, committed⟩ := c
  dsimp only at hsg h ⊢
  intro a hne
  have hroots : ∀ r ∈ Exec.rawFrameRoots run, r.sevm.currentTarget ≠ a := fun r hr e =>
    hne (e.symm.trans (h r hr))
  refine ⟨fun hcode key => ?_, ?_⟩
  · exact Exec.committedCell_eq_of_noRetainedWriteTo_noStateGas run committed hsg a key hcode
      (Exec.noRetainedWriteTo_of_frame_owners_ne run a key hroots)
  · have hrel := (ExecutionTrace.Exec.codeAt_avoid_noStateGas (a := a) run hsg fun r hr _ => hroots r hr).1
    cases out with
    | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
    | ok post => exact hrel

/-- A committed frame whose chain decodes no external instruction keeps the foreign world. -/
theorem frameKeepsForeign_of_noExec (c : Exec.Frame)
    (hsg : c.sevm.benvStat.rules.stateGas = none)
    (h : ∀ N, Exec.Deriv.ParentPrefix ⟨c.pc, c.sevm, c.pre, c.out, c.run⟩ N →
      ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)) :
    FrameKeepsForeign c := by
  refine frameKeepsForeign_of_roots c hsg fun r hr => ?_
  simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants_eq_nil_of_noExec c.run h,
    List.mem_singleton] at hr
  rw [hr]

/-- **Every frame below a chain satisfies `Q`**, when each frame a chain node enters does and so does
everything below that frame. -/
theorem Exec.rawFrameDescendants_of_chain {root : Exec.Deriv} {Q : Exec.Deriv → Prop}
    (hc : ∀ {nodePc nextPc : Nat} {nodeSevm : Sevm} {nodePre : Devm} {out raw : Execution} {frame : Frame}
      {rsm : Resume} {cevm : Evm} {run : Exec nodePc nodeSevm nodePre out},
      Exec.Deriv.ParentPrefix root ⟨nodePc, nodeSevm, nodePre, out, run⟩ →
      Evm.step ⟨nodePc, nodeSevm, nodePre⟩ = .spawn frame rsm nextPc → frame.enter = .run cevm →
      ∀ child : Exec cevm.pc cevm.sta cevm.dyna raw, ∀ D ∈ Exec.rawFrameRoots child, Q D) :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      Exec.Deriv.ParentPrefix root ⟨pc, sevm, pre, out, run⟩ →
      ∀ D ∈ Exec.rawFrameDescendants run, Q D := by
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
  | runErr step enter child resume ih =>
    intro chain D member
    exact hc chain step enter child D (by simpa only [Exec.rawFrameRoots, Exec.rawFrameDescendants] using member)
  | runOk step enter child resume next childIH nextIH =>
    intro chain D member
    simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append] at member
    rcases member with rfl | member | member
    · exact hc chain step enter child _ (List.mem_cons_self ..)
    · exact hc chain step enter child D (List.mem_cons_of_mem _ member)
    · exact nextIH (chain.snoc (.runOk step enter child resume next)) D member

/-- **No chain node of a certified frame decodes an external instruction**, when no reach from the
certificate's root tree `f0` stands at one. Any outcome. -/
theorem noExec_of_reach {code : ByteArray} {c : Cert} {f0 : SFunc} (checked : Cert.check code c = true)
    (hf0 : (Cursor.start c).f = f0) (hK : (Cursor.start c).K = [])
    {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (hcode : sevm.code = code) (hsg : sevm.benvStat.rules.stateGas = none)
    (hr : ∀ T, Reach (StepIn ⟨0, sevm, pre, out, run⟩) c.prog sevm
      ⟨St pre pre.stack pre.memory pre.gasLeft, f0, []⟩ T → AtExec T → False) :
    ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N →
      ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x) := by
  intro N hN x hat
  obtain ⟨κ, reach, okN⟩ := reach_of_parentPrefix_noStateGas checked rfl hcode hsg hN
  obtain ⟨g, hg, -⟩ := okN.tree_of_exec hat
  refine hr (κ.conf N.devm) ?_ ⟨x, g, hg⟩
  rw [← St.self rfl rfl]
  have e : (Cursor.start c).conf pre = ⟨pre, f0, []⟩ := by
    simp only [Cursor.conf, hf0, hK, List.map_nil]
  rw [← e]
  exact reach

/-! ## Static frames -/

/-- **A spawned static frame has a code address**: it is not a CREATE frame. -/
theorem Xinst.step_spawn_codeAddress_of_static_noStateGas {sevm : Sevm} {devm : Devm} {x : Xinst}
    (hsg : sevm.benvStat.rules.stateGas = none) {f : Frame} {rsm : Resume}
    (hs : Xinst.step sevm devm x = .spawn f rsm) (hst : f.inner.isStatic = true) :
    f.inner.codeAddress ≠ none := by
  rcases Xinst.step_shapeNoStateGas sevm devm x hsg with ⟨ex, hsh, -⟩ |
    ⟨d, e, na, mi, ms, hf, hsh⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, -, -, hsh⟩ <;> rw [hsh] at hs
  · cases hs
  · rw [genericCreate.step_spawn_inner_isStatic hs] at hst
    cases hst
  · rw [genericCall.step_spawn_codeAddress hs]
    exact Option.some_ne_none _

/-- **Every frame a static execution enters is static and has a code address.** -/
theorem Exec.static_rawFrameRoots_noStateGas {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hfork : sevm.benvStat.rules.stateGas = none)
    (hstatic : sevm.isStatic = true) (hca : sevm.codeAddress ≠ none) :
    ∀ root ∈ Exec.rawFrameRoots run, root.sevm.isStatic = true ∧ root.sevm.codeAddress ≠ none := by
  induction run with
  | halt hstep =>
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst member
      exact ⟨hstatic, hca⟩
  | cont hstep next ih =>
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨hstatic, hca⟩
      · exact ih hfork hstatic hca root (List.mem_cons_of_mem _ member)
  | doneErr hstep henter hresume =>
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst member
      exact ⟨hstatic, hca⟩
  | doneOk hstep henter hresume next ih =>
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨hstatic, hca⟩
      · exact ih hfork hstatic hca root (List.mem_cons_of_mem _ member)
  | @runErr p e d f rsm p' cevm raw er hstep henter child hresume ih =>
      obtain ⟨x, -, hxs, -⟩ := Evm.step_spawn_inv hstep
      have hfst := Xinst.step_spawn_isStatic hxs hstatic
      have hcst := Evm.step_run_isStatic hstep henter hstatic
      have hcac : f.inner.codeAddress ≠ none := Xinst.step_spawn_codeAddress_of_static_noStateGas hfork hxs hfst
      obtain ⟨_, _, hcev⟩ := Frame.enter_run_inv henter
      have hcac' : cevm.sta.codeAddress ≠ none := by rw [hcev]; exact hcac
      have hroots := ih (Evm.step_spawn_child_fork_noStateGas hstep henter hfork) hcst hcac'
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨hstatic, hca⟩
      · rcases member with rfl | member
        · exact hroots _ (List.mem_cons_self ..)
        · exact hroots root (List.mem_cons_of_mem _ member)
  | @runOk p e d f rsm p' cevm raw d' ex hstep henter child hresume next ihChild ihNext =>
      obtain ⟨x, -, hxs, -⟩ := Evm.step_spawn_inv hstep
      have hfst := Xinst.step_spawn_isStatic hxs hstatic
      have hcst := Evm.step_run_isStatic hstep henter hstatic
      have hcac : f.inner.codeAddress ≠ none := Xinst.step_spawn_codeAddress_of_static_noStateGas hfork hxs hfst
      obtain ⟨_, _, hcev⟩ := Frame.enter_run_inv henter
      have hcac' : cevm.sta.codeAddress ≠ none := by rw [hcev]; exact hcac
      have hrootsChild := ihChild (Evm.step_spawn_child_fork_noStateGas hstep henter hfork) hcst hcac'
      have hrootsNext := ihNext hfork hstatic hca
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.mem_append] at member
      rcases member with rfl | member | member | member
      · exact ⟨hstatic, hca⟩
      · exact hrootsChild root (by rw [member]; exact List.mem_cons_self ..)
      · exact hrootsChild root (List.mem_cons_of_mem _ member)
      · exact hrootsNext root (List.mem_cons_of_mem _ member)

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

/-- **A committed static frame with a code address keeps the world**: the storage of every address with
code at its entry and the code of every address. -/
theorem frameKeeps_of_static (c : Exec.Frame) (hsg : c.sevm.benvStat.rules.stateGas = none)
    (hs : c.sevm.isStatic = true) (hca : c.sevm.codeAddress ≠ none) (a : Adr) :
    ((c.pre.getCode a).toList ≠ [] → ∀ key, (c.post.getStor a).get key = (c.pre.getStor a).get key) ∧
      c.post.getCode a = c.pre.getCode a := by
  obtain ⟨cpc, sevm, pre, out, run, committed⟩ := c
  dsimp only at hsg hs hca ⊢
  have roots := Exec.static_rawFrameRoots_noStateGas run hsg hs hca
  refine ⟨fun hcode key => ?_, ?_⟩
  · exact Exec.committedCell_eq_of_noRetainedWriteTo_noStateGas run committed hsg a key hcode
      (Exec.noRetainedWriteTo_of_owner_frames_static run a key fun r hr _ => (roots r hr).1)
  · have hrel := (ExecutionTrace.Exec.codeAt_avoid_noStateGas (a := a) run hsg fun r hr hn =>
      absurd hn (roots r hr).2).1
    cases out with
    | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
    | ok post => exact hrel

/-- A frame entered from a chain node of certified code that executes only `STATICCALL` is static, has a code
address, and enters only such frames. -/
private theorem staticOnly_child {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true)
    (only : ∀ f ∈ c.prog, f.execsSatisfy Xinst.isStaticcall = true)
    {root : Exec.Deriv} (pc0 : root.pc = 0) (installed : root.sevm.code = code)
    (rootSg : root.sevm.benvStat.rules.stateGas = none)
    {nodePc nextPc : Nat} {nodeSevm : Sevm} {nodePre : Devm} {out raw : Execution} {frame : Frame}
    {rsm : Resume} {cevm : Evm} {run : Exec nodePc nodeSevm nodePre out}
    (chain : Exec.Deriv.ParentPrefix root ⟨nodePc, nodeSevm, nodePre, out, run⟩)
    (step : Evm.step ⟨nodePc, nodeSevm, nodePre⟩ = .spawn frame rsm nextPc)
    (enter : frame.enter = .run cevm) (child : Exec cevm.pc cevm.sta cevm.dyna raw) :
    ∀ D ∈ Exec.rawFrameRoots child, D.sevm.isStatic = true ∧ D.sevm.codeAddress ≠ none := by
  have sevmEq : nodeSevm = root.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  have sg : nodeSevm.benvStat.rules.stateGas = none := by rw [sevmEq]; exact rootSg
  obtain ⟨x, instruction, spawn, _⟩ := Evm.step_spawn_inv step
  have onlyStatic : x = .staticcall :=
    parentPrefix_exec_staticcall_of_cert_noStateGas checked only pc0 installed rootSg chain instruction
  subst x
  have fst := Xinst.step_staticcall_spawn_isStatic spawn
  have stc : cevm.sta.isStatic = true := (Frame.enter_run_isStatic enter).trans fst
  obtain ⟨_, _, hcev⟩ := Frame.enter_run_inv enter
  have cca : cevm.sta.codeAddress ≠ none := by
    rw [hcev]; exact Xinst.step_spawn_codeAddress_of_static_noStateGas sg spawn fst
  exact Exec.static_rawFrameRoots_noStateGas child (Evm.step_spawn_child_fork_noStateGas step enter sg) stc cca

/-- **A committed frame of certified code that executes only `STATICCALL` keeps the foreign world.** -/
theorem frameKeepsForeign_of_staticOnly {code : ByteArray} {cert : Cert}
    (checked : Cert.check code cert = true)
    (only : ∀ f ∈ cert.prog, f.execsSatisfy Xinst.isStaticcall = true)
    (c : Exec.Frame) (hpc : c.pc = 0) (hcode : c.sevm.code = code)
    (hsg : c.sevm.benvStat.rules.stateGas = none) : FrameKeepsForeign c := by
  obtain ⟨cpc, sevm, pre, out, run, committed⟩ := c
  dsimp only at hpc hcode hsg ⊢
  subst hpc
  intro a hne
  have hd : ∀ D ∈ Exec.rawFrameDescendants run, D.sevm.isStatic = true ∧ D.sevm.codeAddress ≠ none :=
    Exec.rawFrameDescendants_of_chain (root := ⟨0, sevm, pre, out, run⟩)
      (fun chain step enter child => staticOnly_child checked only rfl hcode hsg chain step enter child)
      run (.refl _)
  have hroots : ∀ r ∈ Exec.rawFrameRoots run, r.sevm.currentTarget = a →
      r.sevm.isStatic = true ∧ r.sevm.codeAddress ≠ none := by
    intro r hr ht
    simp only [Exec.rawFrameRoots, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact absurd ht.symm hne
    · exact hd r hr
  refine ⟨fun hc key => ?_, ?_⟩
  · exact Exec.committedCell_eq_of_noRetainedWriteTo_noStateGas run committed hsg a key hc
      (Exec.noRetainedWriteTo_of_owner_frames_static run a key fun r hr ht => (hroots r hr ht).1)
  · have hrel := (ExecutionTrace.Exec.codeAt_avoid_noStateGas (a := a) run hsg fun r hr hn ht =>
      (hroots r hr ht).2 hn).1
    cases out with
    | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
    | ok post => exact hrel

/-- Neither `SLOAD` nor `SSTORE`. -/
def Ninst.storageFree : Ninst → Bool
  | .reg .sload | .reg .sstore => false
  | _ => true

/-- `ri_stepX_nonstorage`, with its side conditions a kernel-checkable flag, so that a storage step
fails cleanly inside `first`. -/
theorem ri_stepX_free {sevm : Sevm} {b b' d : Devm} {S S' : List B256} {M M' : Mem} {G : Nat} {n : Ninst}
    (h : Ninst.Run sevm (St b S M G) n d) (hn : Ninst.storageFree n = true)
    (hs : stepX sevm n b S M = some (b', S', M')) : ∃ G', d = St b' S' M' G' :=
  ri_stepX_nonstorage (by rintro rfl; cases hn) (by rintro rfl; cases hn) h hs

/-- One straight-line, storage-free step of a reach `h` to the external instruction `t`. -/
macro "rstepN " h:ident t:ident : tactic => `(tactic| first
  | (have h' := rr_dest $h $t; clear $h; obtain ⟨_, $h:ident⟩ := h')
  | (have h' := rr_next $h $t; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
     obtain ⟨_, e⟩ := ri_stepX_free (StepIn.toRun hd) rfl rfl
     try dsimp only [List.set, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at e
     subst e; clear hd))

/-- One straight-line step of a reach that may read storage (`bal : rules.bal = none`) and use the
legacy `EXP`/`MUL` arithmetic; it stops at a store. -/
macro "rstepS " h:ident t:ident bal:ident : tactic => `(tactic| first
  | rstepN $h $t
  | (have h' := rr_next $h $t; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
     obtain ⟨_, e⟩ := ri_sloadH $bal (StepIn.toRun hd)
     subst e; clear hd)
  | (have h' := rr_next $h $t; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
     obtain ⟨_, e⟩ := ri_exp (StepIn.toRun hd)
     subst e; clear hd)
  | (have h' := rr_next $h $t; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
     obtain ⟨_, e⟩ := ri_mul (StepIn.toRun hd)
     subst e; clear hd))

/-- A conditional jump of the reach; an arm inside the exec-free set `hE` closes. -/
macro "rbranchE " h:ident t:ident hE:term : tactic => `(tactic|
  (have h' := rr_branch $h $t; clear $h; rcases h' with ⟨_, _, $h:ident⟩ | ⟨_, _, $h:ident⟩ <;>
    try (exact (Reach.false_of_execFree $hE $h $t (by decide)
      (fun _ hs => absurd hs List.not_mem_nil)).elim)))

/-- One dispatcher comparison of the reach on a known selector; the reach closes as soon as it
stands in the exec-free set `hE`. -/
macro "rdispE " h:ident t:ident hE:term : tactic => `(tactic| first
  | (exact (Reach.false_of_execFree $hE $h $t (by decide)
      (fun _ hs => absurd hs List.not_mem_nil)).elim)
  | (have h' := rr_cmp_gt StepIn.toRun $h $t; clear $h; obtain ⟨_, $h:ident⟩ := h'
     first
     | (rw [ite_eq_left (by decide)] at $h:ident)
     | (rw [ite_eq_right (by decide)] at $h:ident))
  | (have h' := rr_cmp_eq StepIn.toRun rfl $h $t; clear $h; obtain ⟨_, $h:ident⟩ := h'
     first
     | (rw [ite_eq_left (by decide)] at $h:ident)
     | (rw [ite_eq_right (by decide)] at $h:ident))
  | (have h' := rr_dest $h $t; clear $h; obtain ⟨_, $h:ident⟩ := h'))

end Blanc.Lift
