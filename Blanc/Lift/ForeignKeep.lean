import Blanc.Lift.ReachChain
import Blanc.Lift.ReachDispatch
import Blanc.Lift.WalkCutKit
import Blanc.Lift.InvWalkLegacy
import Blanc.Lift.HistAccessWalk
import Blanc.ExecutionCodeAt
import Blanc.ExecutionNoninterference

/-!
# What a frame keeps when no frame it enters is elsewhere

`FrameKeepsForeign c`: a committed frame leaves alone the storage of every other address with
code at its entry, and the code of every other address.

* `frameKeepsForeign_of_roots`: it does, when every frame it enters runs at its own target;
* `frameKeepsForeign_of_noExec`: so when its chain decodes no external instruction;
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

/-- **Every frame below a chain runs at `T`**, when each frame a chain node enters does and so does
everything below that frame. -/
theorem Exec.rawFrameDescendants_at {root : Exec.Deriv} {T : Adr}
    (hc : ∀ {nodePc nextPc : Nat} {nodeSevm : Sevm} {nodePre : Devm} {out raw : Execution} {frame : Frame}
      {rsm : Resume} {cevm : Evm} {run : Exec nodePc nodeSevm nodePre out},
      Exec.Deriv.ParentPrefix root ⟨nodePc, nodeSevm, nodePre, out, run⟩ →
      Evm.step ⟨nodePc, nodeSevm, nodePre⟩ = .spawn frame rsm nextPc → frame.enter = .run cevm →
      ∀ child : Exec cevm.pc cevm.sta cevm.dyna raw,
        ∀ D ∈ Exec.rawFrameRoots child, D.sevm.currentTarget = T) :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      Exec.Deriv.ParentPrefix root ⟨pc, sevm, pre, out, run⟩ →
      ∀ D ∈ Exec.rawFrameDescendants run, D.sevm.currentTarget = T := by
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
