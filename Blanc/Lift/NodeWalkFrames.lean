import Blanc.Lift.NodeWalk

/-!
# Chains, halting frames and resumed parents over the node walks

The chain and frame layer of `Blanc/Lift/NodeWalk.lean`, for a proof that walks a whole tree
of frames (a parent, its call-family children, their children) on any derivation:

* `chain_trans`, `chain_step`, `interval_trans`, `interval_step`: a property of every node of
  a same-frame chain, or of an interval of it, assembled from its walk segments and the
  nodes between them;
* `noKeccakAt_of_exec`: a node at a frame-entering instruction executes no `KECCAK256`;
* `halt_ok_childAgree`, `halt1_childAgree`: a successful halting step hands its parent a machine
  the shadows of its start configuration describe;
* `spawn_resume_ok`, `spawn_resume_err`: a call-family node whose child has a known outcome
  spawns it, resumes into a same-frame successor at the resumed configuration (with the
  agreement of its shadows), and its raw descendants are the child's and the successor's;
* `leaf_frame`, `leaf_frame_ok`: a frame that walks and halts.

Nothing here is contract-specific.
-/

namespace Blanc.Lift.NodeWalk

open Jaune Blanc.Lift Blanc.Lift.Witness
open Jaune.Exec.Deriv (ParentStep ParentPrefix)

/-! ## Chains -/

/-- A same-frame chain from `a` satisfies `P` when the nodes of `[a, b)` do and every node
from `b` on does. -/
theorem chain_trans {P : Exec.Deriv → Prop} {a b : Exec.Deriv} (hab : ParentPrefix a b)
    (h1 : ∀ y, ParentPrefix a y → ParentPrefix y b → y ≠ b → P y)
    (h2 : ∀ y, ParentPrefix b y → P y) : ∀ y, ParentPrefix a y → P y := by
  intro y hy
  rcases parentPrefix_total hy hab with hyb | hby
  · by_cases hne : y = b
    · subst hne; exact h2 y (.refl _)
    · exact h1 y hy hyb hne
  · exact h2 y hby

/-- A same-frame chain from `x` satisfies `P` when `x` does and the chain from its
same-frame successor `x'` does. -/
theorem chain_step {P : Exec.Deriv → Prop} {x x' : Exec.Deriv} (hs : ParentStep x' x)
    (hx : P x) (h2 : ∀ y, ParentPrefix x' y → P y) : ∀ y, ParentPrefix x y → P y := by
  intro y hy
  cases hy with
  | refl => exact hx
  | step head rest =>
    have := Jaune.Exec.Deriv.ParentStep.unique head hs
    subst this
    exact h2 y rest

/-- The nodes of `[a, c)` satisfy `P` when those of `[a, b)`, `b` itself and those of `[b, c)`
do. -/
theorem interval_trans {P : Exec.Deriv → Prop} {a b c : Exec.Deriv} (hab : ParentPrefix a b)
    (h1 : ∀ y, ParentPrefix a y → ParentPrefix y b → y ≠ b → P y) (hb : P b)
    (h2 : ∀ y, ParentPrefix b y → ParentPrefix y c → y ≠ c → P y) :
    ∀ y, ParentPrefix a y → ParentPrefix y c → y ≠ c → P y := by
  intro y hay hyc hne
  rcases parentPrefix_total hay hab with hyb | hby
  · by_cases hyb' : y = b
    · subst hyb'; exact hb
    · exact h1 y hay hyb hyb'
  · exact h2 y hby hyc hne

/-- A node at a frame-entering instruction executes no `KECCAK256`. -/
theorem noKeccakAt_of_exec {code : ByteArray} {pc : Nat} {x : Xinst}
    (h : Ninst.At code pc (.exec x)) : NoKeccakAt code pc := by
  intro hk
  unfold Ninst.At at h hk
  rw [h] at hk
  cases hk

/-- Interval version of `chain_step`: the nodes of `[x, c)` satisfy `P` when `x` does and
those of `[x', c)` do, `x'` the same-frame successor of `x`. -/
theorem interval_step {P : Exec.Deriv → Prop} {x x' c : Exec.Deriv} (hs : ParentStep x' x)
    (hx : P x)
    (h2 : ∀ y, ParentPrefix x' y → ParentPrefix y c → y ≠ c → P y) :
    ∀ y, ParentPrefix x y → ParentPrefix y c → y ≠ c → P y := by
  intro y hy hyc hne
  cases hy with
  | refl => exact hx
  | step head rest =>
    have := Jaune.Exec.Deriv.ParentStep.unique head hs
    subst this
    exact h2 y rest hyc hne

/-! ## Halting frames and resumed parents -/

/-- A halting instruction that succeeds keeps the accessed sets and the world. -/
theorem linst_ok_accKeep {sevm : Sevm} {devm d' : Devm} {l : Linst}
    (h : l.run sevm devm = .ok d') (hl : l ≠ .selfdestruct) : AccKeep devm d' := by
  revert h hl
  cases l with
  | stop => intro h _; simp only [Linst.run] at h; cases h; exact ⟨rfl, rfl, rfl⟩
  | revert =>
    intro h _
    simp only [Linst.run] at h
    obtain ⟨⟨i, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
    obtain ⟨⟨n, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
    obtain ⟨d3, h3, e3⟩ := Except.bind_eq_ok e2
    cases e3
  | return_ =>
    intro h _
    simp only [Linst.run] at h
    obtain ⟨⟨i, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
    obtain ⟨⟨n, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
    obtain ⟨d3, h3, e3⟩ := Except.bind_eq_ok e2
    cases e3
    exact (accKeep_popToNat h1).trans ((accKeep_popToNat h2).trans
      ((accKeep_chargeGas h3).trans ⟨rfl, rfl, rfl⟩))
  | selfdestruct => intro _ hl; exact absurd rfl hl

/-- **A successful halting walk step hands its parent a machine the shadows describe.** -/
theorem halt_ok_childAgree {pol : HashPol} {code : ByteArray} {d : Nat} (T : CodeTries code d)
    {sevm : Sevm} {c : PCfg} {d' : Devm} (hag : PAgree c)
    (h : pstepH pol T sevm c = .halt (.ok d')) :
    ChildAgree d' c.keys c.adrs c.stor c.acs := by
  have key : ∀ l : Linst, l ≠ .selfdestruct → l.run sevm c.devm = .ok d' →
      ChildAgree d' c.keys c.adrs c.stor c.acs := fun l hl hr =>
    childAgree_of_pagree (agree_accKeep (c := c) hag (linst_ok_accKeep hr hl))
  unfold pstepH at h
  split at h
  · cases h
  · cases h
  · split at h <;> cases h
  · split at h <;> cases h
  · split at h
    · split at h <;> cases h
    · cases h
  · split at h
    · cases h
    · cases h
  · cases h
  · rename_i l hl _
    exact key l hl (PRes.halt.inj h)

/-- **A call-family node with a successful child, on any derivation.**  At a node sitting at an
agreeing configuration `c` whose step spawns the prepared frame `cp.f` (`spawn_node`), if every
node at the child's start configuration has the successful outcome `dch` (no error), described
by the shadows `cl`, then the node spawns such a child, resumes into a same-frame successor at
the resumed configuration (the child's shadows appended), and its raw descendants are the child,
the child's, and the successor's. -/
theorem spawn_resume_ok {sevm : Sevm} {c cl : PCfg} {cp : CallPrep} {cevm : Evm}
    {dch d' : Devm} {node : Exec.Deriv}
    (hn : NodeAt sevm c node) (hag : PAgree c) (hF : PrepFacts c cp)
    (hstep : Evm.step ⟨c.pc, sevm, c.devm⟩ = .spawn cp.f (.call cp.p cp.oi cp.os) (c.pc + 1))
    (hent : cp.f.enter = .run cevm)
    (hce : dch.error = none) (hr : resumeCallB cp.p cp.oi cp.os (.ok dch) = some d')
    (hchild : ∀ ch, NodeAt cevm.sta (childCfg cevm cp.f c.keys cp.adrs c.stor c.acs) ch →
      ch.exn = .ok dch ∧ ChildAgree dch cl.keys cl.adrs cl.stor cl.acs) :
    ∃ ch x', Blanc.LockExclusion.Spawns node ch ∧
      NodeAt cevm.sta (childCfg cevm cp.f c.keys cp.adrs c.stor c.acs) ch ∧ ParentStep x' node ∧
      NodeAt sevm ⟨c.pc + 1, d', c.keys ++ cl.keys, cp.adrs ++ cl.adrs, cl.stor, cl.acs⟩ x' ∧
      x'.exn = node.exn ∧
      Exec.rawFrameDescendants node.exc =
        ch :: (Exec.rawFrameDescendants ch.exc ++ Exec.rawFrameDescendants x'.exc) ∧
      PAgree ⟨c.pc + 1, d', c.keys ++ cl.keys, cp.adrs ++ cl.adrs, cl.stor, cl.acs⟩ := by
  have hstep' : Evm.step ⟨node.pc, node.sevm, node.devm⟩ =
      .spawn cp.f (.call cp.p cp.oi cp.os) (c.pc + 1) := by
    rw [step_eq_of_nodeAt hn]; exact hstep
  obtain ⟨ch, sp, hpc, hs', hd, okc, -⟩ := Exec.Deriv.step_spawn hstep' hent
  have hch : NodeAt cevm.sta (childCfg cevm cp.f c.keys cp.adrs c.stor c.acs) ch :=
    ⟨hpc, hs', hd⟩
  obtain ⟨hex, hcl⟩ := hchild ch hch
  obtain ⟨x', e, hpc', hs'', hd', hexn, hdesc⟩ := okc d' (by
    rw [hex, PrepFacts.settle_ok hF hce]; exact resumeCallB_sound hr)
  exact ⟨ch, x', sp, hch, e, ⟨hpc', hs''.trans hn.2.1, hd'⟩, hexn, hdesc,
    resume_agree_ok_of hag hF (by rw [hce]; rfl) hcl hr⟩

/-- **A call-family node with a failed child, on any derivation**: as `spawn_resume_ok`, for a
child every node at whose start configuration has the outcome `.error (e, dch)`, `e` a revert or
a halt; the child's world is rolled back, so the resumed configuration keeps the parent's
shadows.  `chd` is the machine the failed child settles to (`hs`), `hr` the parent's resume. -/
theorem spawn_resume_err {sevm : Sevm} {c : PCfg} {cp : CallPrep} {cevm : Evm}
    {e : EvmError} {dch chd d' : Devm} {node : Exec.Deriv}
    (hn : NodeAt sevm c node) (hag : PAgree c) (hF : PrepFacts c cp)
    (hstep : Evm.step ⟨c.pc, sevm, c.devm⟩ = .spawn cp.f (.call cp.p cp.oi cp.os) (c.pc + 1))
    (hent : cp.f.enter = .run cevm) (hk : e = .revert ∨ ∃ r, e = .halt r)
    (hs : cp.f.settle (.error (e, dch)) = .ok chd)
    (hr : resumeCallB cp.p cp.oi cp.os (.ok chd) = some d')
    (hchild : ∀ ch, NodeAt cevm.sta (childCfg cevm cp.f c.keys cp.adrs c.stor c.acs) ch →
      ch.exn = .error (e, dch)) :
    ∃ ch x', Blanc.LockExclusion.Spawns node ch ∧
      NodeAt cevm.sta (childCfg cevm cp.f c.keys cp.adrs c.stor c.acs) ch ∧ ParentStep x' node ∧
      NodeAt sevm ⟨c.pc + 1, d', c.keys, cp.adrs, c.stor, c.acs⟩ x' ∧
      x'.exn = node.exn ∧
      Exec.rawFrameDescendants node.exc =
        ch :: (Exec.rawFrameDescendants ch.exc ++ Exec.rawFrameDescendants x'.exc) ∧
      PAgree ⟨c.pc + 1, d', c.keys, cp.adrs, c.stor, c.acs⟩ := by
  have hstep' : Evm.step ⟨node.pc, node.sevm, node.devm⟩ =
      .spawn cp.f (.call cp.p cp.oi cp.os) (c.pc + 1) := by
    rw [step_eq_of_nodeAt hn]; exact hstep
  obtain ⟨ch, sp, hpc, hs', hd, okc, -⟩ := Exec.Deriv.step_spawn hstep' hent
  have hch : NodeAt cevm.sta (childCfg cevm cp.f c.keys cp.adrs c.stor c.acs) ch :=
    ⟨hpc, hs', hd⟩
  have hex := hchild ch hch
  obtain ⟨chd', hs2, hce, hst⟩ := PrepFacts.settle_error hF (d := dch) hk
  have hchd : chd' = chd := by
    have := hs2.symm.trans hs
    cases this; rfl
  subst hchd
  obtain ⟨x', e', hpc', hs'', hd', hexn, hdesc⟩ := okc d' (by
    rw [hex, hs]; exact resumeCallB_sound hr)
  exact ⟨ch, x', sp, hch, e', ⟨hpc', hs''.trans hn.2.1, hd'⟩, hexn, hdesc,
    resume_agree_error_of hag hF hce hst hr⟩

/-- **A frame that walks and halts, on any derivation** (`pwalkH_cont` then `pwalkH_halt`): every
node at its start configuration has the halting outcome, no raw frame descendant, and a chain
satisfying the hash policy. -/
theorem leaf_frame (pol : HashPol) {code : ByteArray} {d : Nat} (T : CodeTries code d)
    {sevm : Sevm} (hcode : sevm.code = code) (ok : Nat → Bool) {n k : Nat} {c c1 : PCfg}
    {ex : Execution} (hag : PAgree c) (hw : pwalkH pol T sevm ok n c = .cont c1)
    (hh : pwalkH pol T sevm ok k c1 = .halt ex) :
    ∀ x, NodeAt sevm c x → x.exn = ex ∧ Exec.rawFrameDescendants x.exc = [] ∧
      ∀ y, ParentPrefix x y → NodeOKH code ok pol y := by
  intro x hx
  obtain ⟨hag1, hc⟩ := pwalkH_cont pol T hcode ok n c c1 hag hw
  obtain ⟨x1, hx1, hpp, hex, hds, hbet⟩ := hc x hx
  obtain ⟨hex1, hds1, hall⟩ := pwalkH_halt pol T hcode ok k c1 ex hag1 hh x1 hx1
  exact ⟨hex ▸ hex1, hds ▸ hds1, chain_trans hpp hbet hall⟩

/-- A one-step halting walk that succeeds hands its parent a machine the shadows of its start
configuration describe (`halt_ok_childAgree`). -/
theorem halt1_childAgree {pol : HashPol} {code : ByteArray} {d : Nat} (T : CodeTries code d)
    {sevm : Sevm} {ok : Nat → Bool} {c : PCfg} {d' : Devm} (hag : PAgree c)
    (h : pwalkH pol T sevm ok 1 c = .halt (.ok d')) :
    ChildAgree d' c.keys c.adrs c.stor c.acs := by
  simp only [pwalkH] at h
  split at h
  · cases h1 : pstepH pol T sevm c with
    | stuck => rw [h1] at h; cases h
    | cont c' => rw [h1] at h; simp only at h; cases h
    | halt ex =>
      rw [h1] at h
      cases h
      exact halt_ok_childAgree T hag h1
  · cases h

/-- **A frame that walks and returns successfully, on any derivation** (`leaf_frame` with the
child's shadows): every node at its start configuration has the outcome `.ok d'` and no raw
frame descendant, and `d'` is described by the shadows of the configuration before the halt. -/
theorem leaf_frame_ok (pol : HashPol) {code : ByteArray} {d : Nat} (T : CodeTries code d)
    {sevm : Sevm} (hcode : sevm.code = code) (ok : Nat → Bool) {n : Nat} {c c1 : PCfg}
    {d' : Devm} (hag : PAgree c) (hw : pwalkH pol T sevm ok n c = .cont c1)
    (hh : pwalkH pol T sevm ok 1 c1 = .halt (.ok d')) :
    ChildAgree d' c1.keys c1.adrs c1.stor c1.acs ∧
    ∀ x, NodeAt sevm c x → x.exn = .ok d' ∧ Exec.rawFrameDescendants x.exc = [] ∧
      ∀ y, ParentPrefix x y → NodeOKH code ok pol y :=
  ⟨halt1_childAgree T (pwalkH_cont pol T hcode ok n c c1 hag hw).1 hh,
    leaf_frame pol T hcode ok hag hw hh⟩

end Blanc.Lift.NodeWalk
