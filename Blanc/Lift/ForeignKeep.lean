import Blanc.Lift.ReachChain
import Blanc.Lift.ReachDispatch
import Blanc.Lift.WalkCutKit
import Blanc.Lift.InvWalkLegacy
import Blanc.Lift.HistAccessWalk
import Blanc.ExecutionCodeAt
import Blanc.ExecutionNoninterference
import Blanc.Lift.StaticOnlyFrames
import Blanc.ExecutionTraceCallOnly
import Blanc.LockExclusion

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
