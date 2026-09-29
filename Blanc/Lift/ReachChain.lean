import Blanc.Lift.Cursor
import Blanc.Lift.ReachWalk
import Blanc.ExecutionModelAccounting

/-!
# From a cursor-placed node to later nodes of the same frame

`reach_of_parentPrefix` (`Cursor.lean`) reaches a chain node from entry `0`.  A fact about what a frame
does *after* one of its nodes — that it makes no further external call, that its storage does not change
until it halts — needs the reach *between* two chain nodes, which is the same induction started at any
cursor-placed node (`reach_between`).  Two consequences, both stated for a tree that is exec-free
(`SFunc.execFreeIn`) or state-silent (`SFunc.silentTree`) from the cursor on:

* `noExec_after_of_cursor`: no later node decodes an external instruction;
* `getStor_post_of_silent`: the frame's post storage is the node's storage.

`Reach.silentTo` is the reach lemma behind the second: a reach that runs only accepted instructions, pops
and burns, through `dest` and `branch` trees and returns into silent continuations, keeps a step-stable
predicate.
-/

namespace Blanc.Lift

open Jaune

/-- A tree every path of which runs instructions accepted by `ok`, jumpdests and conditional jumps to
subtrees of the same kind, and ends in a halt or a return. -/
def SFunc.silentTree (ok : Ninst → Bool) : SFunc → Bool
  | .next n f => ok n && f.silentTree ok
  | .dest f => f.silentTree ok
  | .branch f g => f.silentTree ok && g.silentTree ok
  | .last _ => true
  | .ret => true
  | _ => false

section Silent

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}

/-- **A silent reach.**  Whatever the accepted instructions, pops and burns preserve, holds all along a
reach that stays in `silentTree`s. -/
theorem Reach.silentTo {ok : Ninst → Bool} {Ψ : Devm → Prop}
    (hstep : ∀ {d n d'}, ok n = true → P sevm d n d' → Ψ d → Ψ d')
    (hpop : ∀ {xs d d'}, Devm.PopBurn xs d d' → Ψ d → Ψ d')
    (hburn : ∀ {d d'}, Devm.Burn d d' → Ψ d → Ψ d') :
    ∀ {a T : Conf}, Reach P fs sevm a T → a.f.silentTree ok = true →
      (∀ s ∈ a.K, s.silentTree ok = true) → Ψ a.d → Ψ T.d := by
  intro a T h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro _ _ hΨ; exact hΨ
  | @head a b step rest ih =>
    intro hf hK hΨ
    obtain ⟨d, f, K⟩ := a
    dsimp only at hf hK hΨ
    cases step with
    | next hp =>
        simp only [SFunc.silentTree, Bool.and_eq_true] at hf
        exact ih hf.2 hK (hstep hf.1 hp hΨ)
    | dest hb =>
        exact ih hf hK (hburn hb hΨ)
    | zero t hp =>
        simp only [SFunc.silentTree, Bool.and_eq_true] at hf
        exact ih hf.1 hK (hpop hp hΨ)
    | succ t w hw hp =>
        simp only [SFunc.silentTree, Bool.and_eq_true] at hf
        exact ih hf.2 hK (hpop hp hΨ)
    | toZero t hp => simp [SFunc.silentTree] at hf
    | toSucc t w hw hk hp => simp [SFunc.silentTree] at hf
    | jump t hk hp => simp [SFunc.silentTree] at hf
    | call t hk hp => simp [SFunc.silentTree] at hf
    | @ret d d' f₀ K₀ t hp =>
        exact ih (hK f₀ List.mem_cons_self) (fun s hs => hK s (List.mem_cons_of_mem _ hs))
          (hpop hp hΨ)
    | pcAt hp hr => simp [SFunc.silentTree] at hf

end Silent

/-- A frame none of whose chain nodes decodes an external instruction has no raw descendants. -/
theorem Exec.rawFrameDescendants_eq_nil_of_noExec {pc : Nat} {sevm : Sevm} {d : Devm}
    {out : Execution} (run : Exec pc sevm d out)
    (h : ∀ N, Exec.Deriv.ParentPrefix ⟨pc, sevm, d, out, run⟩ N →
      ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)) :
    Exec.rawFrameDescendants run = [] := by
  induction run with
  | halt step => simp [Exec.rawFrameDescendants]
  | cont step next ih =>
      have := ih (fun N hN x => h N (.step (.cont step next) hN) x)
      simpa [Exec.rawFrameDescendants] using this
  | doneErr step enter resume => simp [Exec.rawFrameDescendants]
  | doneOk step enter resume next ih =>
      obtain ⟨x, instruction, -, -⟩ := Evm.step_spawn_inv step
      exact (h _ (.refl _) x instruction).elim
  | runErr step enter child resume ih =>
      obtain ⟨x, instruction, -, -⟩ := Evm.step_spawn_inv step
      exact (h _ (.refl _) x instruction).elim
  | runOk step enter child resume next childIH nextIH =>
      obtain ⟨x, instruction, -, -⟩ := Evm.step_spawn_inv step
      exact (h _ (.refl _) x instruction).elim

/-! ## Between two chain nodes -/

/-- The raw descendants of a later node of a same-frame prefix are raw descendants of the earlier one. -/
theorem rawFrameDescendants_sub_of_prefix {A F : Exec.Deriv}
    (h : Exec.Deriv.ParentPrefix A F) :
    ∀ r ∈ Exec.rawFrameDescendants F.exc, r ∈ Exec.rawFrameDescendants A.exc := by
  induction h with
  | refl => exact fun r hr => hr
  | step head rest ih => exact fun r hr => desc_sub_of_prec head.prec r (ih r hr)

/-- **The reach between two chain nodes.**  `reach_of_parentPrefix` from any cursor-placed node `F` of a
frame `R`: a later node `N` of the same frame is reached from `F`'s stateful image, through steps whose
children lie among `R`'s raw frame roots. -/
theorem reach_between {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    {R F N : Exec.Deriv} (hF : Exec.Deriv.ParentPrefix R F) (hp : Exec.Deriv.ParentPrefix F N)
    (hfork : CoveredFork R.sevm.benvStat.fork) {κ₀ : Cursor} (ok : CursorOK code c F κ₀) :
    ∃ κ, Reach (StepIn R) c.prog R.sevm (κ₀.conf F.devm) (κ.conf N.devm) ∧
      CursorOK code c N κ := by
  have hsevm : F.sevm = R.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq hF
  have hdesc : ∀ r ∈ Exec.rawFrameDescendants F.exc, r ∈ Exec.rawFrameRoots R.exc :=
    fun r hr => List.mem_cons_of_mem _ (rawFrameDescendants_sub_of_prefix hF r hr)
  suffices h : ∀ {F n : Exec.Deriv}, Exec.Deriv.ParentPrefix F n →
      ∀ κ₀, CursorOK code c F κ₀ → CoveredFork F.sevm.benvStat.fork → F.sevm = R.sevm →
      (∀ r ∈ Exec.rawFrameDescendants F.exc, r ∈ Exec.rawFrameRoots R.exc) →
      ∃ κ, Reach (StepIn R) c.prog R.sevm (κ₀.conf F.devm) (κ.conf n.devm) ∧
        CursorOK code c n κ from
    h hp κ₀ ok (hsevm ▸ hfork) hsevm hdesc
  intro F n hp
  induction hp with
  | refl root => exact fun κ₀ ok _ _ _ => ⟨κ₀, .refl, ok⟩
  | step head _ ih =>
    intro κ₀ ok hfork hsevm hdesc
    obtain ⟨κ₁, -, hstep, ok₁⟩ := cursor_stepS hc ok head hfork
    have hsevm₁ := Cursor.parentStep_sevm head
    obtain ⟨κ, hreach, ok'⟩ := ih κ₁ ok₁ (by rw [hsevm₁]; exact hfork)
      (hsevm₁.trans hsevm)
      (fun r hr => hdesc r (by
        cases head with
        | cont => simpa only [Exec.rawFrameDescendants] using hr
        | doneOk => simpa only [Exec.rawFrameDescendants] using hr
        | runOk =>
          simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inr hr)))
    refine ⟨κ, .head ?_ hreach, ok'⟩
    rw [← hsevm]
    exact hstep.mono fun h => h.mono fun _ _ _ _ _ he r hr => hdesc r (he r hr)

/-- **No later external instruction.**  From a cursor-placed node of a certified frame whose remaining
tree, and the trees pending below it, make no external call within a closed exec-free set, no later
node of the frame decodes an external instruction. -/
theorem noExec_after_of_cursor {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    {R F N : Exec.Deriv} (hF : Exec.Deriv.ParentPrefix R F) (hp : Exec.Deriv.ParentPrefix F N)
    (hfork : CoveredFork R.sevm.benvStat.fork) {κ : Cursor} (ok : CursorOK code c F κ)
    {E : List Nat} (hE : ExecFreeSet c.prog E = true) (hf : κ.f.execFreeIn E = true)
    (hK : ∀ s ∈ κ.K.map Cont.f, s.execFreeIn E = true) :
    ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x) := by
  intro x hat
  obtain ⟨κ', reach, okN⟩ := reach_between hc hF hp hfork ok
  obtain ⟨g, hg, -⟩ := okN.tree_of_exec hat
  exact Reach.false_of_execFree hE reach ⟨x, g, hg⟩ hf hK

/-! ## The halt of a frame -/

private theorem exists_halt_aux {pc : Nat} {sevm : Sevm} {d : Devm} {out : Execution}
    (run : Exec pc sevm d out) :
    ∀ post, out = .ok post → ∃ H : Exec.Deriv,
      Exec.Deriv.ParentPrefix ⟨pc, sevm, d, out, run⟩ H ∧
        Evm.step ⟨H.pc, H.sevm, H.devm⟩ = .halt out := by
  induction run with
  | halt step => intro post h; exact ⟨_, .refl _, step⟩
  | cont step next ih =>
      intro post h
      obtain ⟨H, hp, hs⟩ := ih post h
      exact ⟨H, .step (.cont step next) hp, hs⟩
  | doneErr step enter resume => intro post h; cases h
  | doneOk step enter resume next ih =>
      intro post h
      obtain ⟨H, hp, hs⟩ := ih post h
      exact ⟨H, .step (.doneOk step enter resume next) hp, hs⟩
  | runErr step enter child resume ih => intro post h; cases h
  | runOk step enter child resume next childIH nextIH =>
      intro post h
      obtain ⟨H, hp, hs⟩ := nextIH post h
      exact ⟨H, .step (.runOk step enter child resume next) hp, hs⟩

/-- A successful frame's same-frame chain ends in the node that halts it. -/
theorem Exec.Deriv.exists_halt {pc : Nat} {sevm : Sevm} {d post : Devm}
    (run : Exec pc sevm d (.ok post)) :
    ∃ H : Exec.Deriv, Exec.Deriv.ParentPrefix ⟨pc, sevm, d, .ok post, run⟩ H ∧
      Evm.step ⟨H.pc, H.sevm, H.devm⟩ = .halt (.ok post) :=
  exists_halt_aux run post rfl

/-- A successful halting step keeps persistent storage. -/
theorem Evm.step_halt_getStor_eq {pc : Nat} {sevm : Sevm} {pre post : Devm}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .halt (.ok post)) : Devm.getStor post = Devm.getStor pre := by
  cases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with
  | none =>
      unfold Evm.step at step
      rw [decoded] at step
      cases step
  | some instruction =>
      cases instruction with
      | last last =>
          rw [Evm.step_last decoded] at step
          exact Linst.getStor_eq (Step.halt.inj step)
      | next next =>
          rw [Evm.step_next decoded] at step
          exact (Ninst.step_ne_halt_ok step).elim
      | jump jumpInst =>
          rw [Evm.step_jump decoded] at step
          cases jumpEq : Jinst.run ⟨pc, sevm, pre⟩ jumpInst with
          | error error =>
              rw [jumpEq] at step
              cases step
          | ok result =>
              rw [jumpEq] at step
              cases step

/-- **The post storage of a silent tail.**  If a cursor-placed node of a successful certified frame has a
remaining tree that is state-silent (`ok'`-accepted instructions, pops and burns keep the state) with
silent pending trees, the frame's post storage is that node's storage. -/
theorem getStor_post_of_silent {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    {R F : Exec.Deriv} {post : Devm} (hout : R.exn = .ok post)
    (hF : Exec.Deriv.ParentPrefix R F) (hfork : CoveredFork R.sevm.benvStat.fork) {κ : Cursor}
    (ok : CursorOK code c F κ) {ok' : Ninst → Bool}
    (hstep : ∀ {sevm d n d'}, ok' n = true → StepIn R sevm d n d' → d'.state = d.state)
    (hf : κ.f.silentTree ok' = true) (hK : ∀ s ∈ κ.K.map Cont.f, s.silentTree ok' = true) :
    Devm.getStor post = Devm.getStor F.devm := by
  have hFout : F.exn = .ok post := (Exec.Deriv.ParentPrefix.exn_eq hF).trans hout
  obtain ⟨fpc, fsevm, fd, fout, frun⟩ := F
  dsimp only at hFout
  subst hFout
  obtain ⟨H, hFH, hstepH⟩ := Exec.Deriv.exists_halt frun
  obtain ⟨κ', reach, -⟩ := reach_between hc hF hFH hfork ok
  have hstate := Reach.silentTo (P := StepIn R) (fs := c.prog) (sevm := R.sevm)
    (ok := ok') (Ψ := fun d : Devm => d.state = fd.state)
    (fun hn hs hΨ => (hstep hn hs).trans hΨ)
    (fun pop hΨ => pop.state.symm.trans hΨ) (fun burn hΨ => burn.state.symm.trans hΨ)
    reach hf hK rfl
  refine (Evm.step_halt_getStor_eq hstepH).trans ?_
  funext a
  exact getStor_eq_of_state_eq hstate a

end Blanc.Lift
