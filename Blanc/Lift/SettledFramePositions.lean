import Blanc.ExecutionAccountingAdmission
import Blanc.ExecutionTraceSettledForest
import Blanc.ExecutionTraceSettledOrigin
import Blanc.ExecutionModelAccounting
import Blanc.Lift.RetainedTargetCompleteness
import Blanc.Lift.Token.FamilyReplay

/-!
# Positional facts about settled frames (contract-neutral)

* `ConfiguredHistoryTrace.settledFrames_parent_of_codeAddress`: every settled frame at `ca` whose
  code address is not `ca` (so no message root, since a root at `ca` runs at code address `ca`) has
  a positional parent: an earlier settled frame that spawned it and whose block of descendants
  covers its position.  A one-rung ladder (`parentLadder`) carries the order-local property.
* `Exec.Frame.not_mem_own_descendantFrames`: no frame is among its own descendants;
  `Exec.descendantFrames_eq_flatMap`: a run's descendants are its committed children's blocks, and
  `List.flatMap_committed_split`: a position among blocks lies in one block.
* `Exec.single_child_of_silentAfter`: a run that decodes no external instruction after its first
  one has at most one child, which heads its descendants.
* `ObserverChain.of_local`: an observer chain from its two local conditions.
* `ConfiguredHistoryTrace.settled_mem_rawFrames`: a settled frame's root derivation is a raw frame
  (the block and history steps of `ExecutionTraceSettledOrigin.lean`; a copy of the composition
  stratum's `mem_rawFrames_of_mem_settledFrames`, which Lift modules may not import).
-/

namespace Blanc

open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay Blanc.Lift.Token

/-! ## Positional parents -/

/-- Every frame of `fs` at `ca` off code address `ca` has a positional parent in `fs`. -/
def PositionalParents (ca : Adr) (fs : List Exec.Frame) : Prop :=
  ∀ b f a, fs = b ++ f :: a → f.sevm.currentTarget = ca → f.sevm.codeAddress ≠ some ca →
    ∃ b₁ G b₂, b = b₁ ++ G :: b₂ ∧ f ∈ Exec.childFrames G.run ∧
      b₂.length < (Exec.descendantFrames G.run).length

theorem PositionalParents.nil {ca : Adr} : PositionalParents ca [] := fun b f a split =>
  absurd split.symm (List.append_ne_nil_of_right_ne_nil b (List.cons_ne_nil f a))

theorem PositionalParents.append {ca : Adr} {xs ys : List Exec.Frame}
    (hx : PositionalParents ca xs) (hy : PositionalParents ca ys) :
    PositionalParents ca (xs ++ ys) := by
  intro b f a split target ne
  rcases Blanc.List.split_append_cons split with ⟨m, hxs, -⟩ | ⟨n, hb, hys⟩
  · exact hx b f m hxs target ne
  · obtain ⟨b₁, G, b₂, hn, child, len⟩ := hy n f a hys target ne
    exact ⟨xs ++ b₁, G, b₂, by rw [hb, hn, List.append_assoc], child, len⟩

/-- The carrier of positional parents: no boundary, the observed frames in order. -/
def parentCarrier (ca : Adr) : ReplayCarrier ca where
  Snap := Unit
  Step := Exec.Frame
  Tag := Unit
  Replay _ fs _ := PositionalParents ca fs
  ofState _ := ()
  frameEntry _ _ := ()
  nil _ := PositionalParents.nil
  readsStorage := false
  silent := fun _ _ => rfl
  credit := by
    intros
    exact ⟨[], PositionalParents.nil⟩
  entry_eq_ofState := by
    intros
    rfl

/-- Every frame is observed, as itself. -/
def parentObservation (ca : Adr) : ReplayObservation (parentCarrier ca) where
  O := Exec.Frame
  obs := id
  obs_nil := rfl
  obs_append := fun _ _ => rfl
  frameObs f := [f]
  credit := by
    intros
    exact ⟨[], PositionalParents.nil, rfl⟩

/-- **The positional-parent ladder**: a message root at `ca` runs at code address `ca`, and every
descendant has its positional parent in the root's committed frames. -/
noncomputable def parentLadder {c : ContractSpecSem} (ca : Adr)
    (preserves : c.PreservesAdmitted ca (fun _ _ => True)) :
    AccountingLadderAdmitted c ca (fun _ _ => True) where
  carrier := parentCarrier ca
  append := fun l r => PositionalParents.append l r
  tag _ _ := ()
  preserves := preserves
  view := parentObservation ca
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed admitted ready _ fork bound
    have sevmEq := congrArg Evm.sta evmEq
    dsimp only [initEvm] at sevmEq
    have rootCA : sevm.currentTarget = ca → sevm.codeAddress = some ca := by
      intro target
      rw [sevmEq] at target ⊢
      rcases ready.codeOrForeign with call | foreign
      · exact ready.ready.codeAddress call target
      · exact (foreign target).elim
    refine ⟨Exec.committedFrames run, ?_, by
      change Exec.committedFrames run = (Exec.committedFrames run).flatMap fun f => [f]
      rw [List.flatMap_singleton']⟩
    show PositionalParents ca (Exec.committedFrames run)
    rw [Exec.committedFrames, dite_eq_left committed]
    intro b f a split target ne
    cases b with
    | nil =>
        obtain ⟨rfl, -⟩ := List.cons.inj split
        exact (ne (rootCA target)).elim
    | cons g b =>
        obtain ⟨rfl, rest⟩ := List.cons.inj split
        rcases (Exec.descendantFrames_forest run rest).2 with ⟨child, -⟩ |
            ⟨b₁, G, b₂, hb, child, -, len⟩
        · refine ⟨[], _, b, rfl, child, ?_⟩
          show b.length < (Exec.descendantFrames run).length
          simp only [rest, List.append_eq, List.length_append, List.length_cons]
          omega
        · exact ⟨_ :: b₁, G, b₂, by rw [hb]; rfl, child, len⟩

/-- **Positional parents of the settled frames**: every settled frame at `ca` whose code address is
not `ca` was spawned by an earlier settled frame whose block of descendants covers its position. -/
theorem _root_.Blanc.ExecutionTrace.ConfiguredHistoryTrace.settledFrames_parent_of_codeAddress {c : ContractSpecSem} {ca : Adr}
    (preserves : c.PreservesAdmitted ca (fun _ _ => True)) {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (inv : c.StateInv ca checkpoint.state) :
    PositionalParents ca trace.settledFrames := by
  have admitted : trace.FrameAdmitted ca (fun _ _ => True) :=
    (trace.frameAdmitted_iff_rawFrames ca _).2 fun _ _ _ => trivial
  obtain ⟨steps, replay, observed⟩ :=
    (parentLadder ca preserves).configuredHistory trace admitted inv
  change steps = trace.settledFrames.flatMap (fun f => [f]) at observed
  rw [List.flatMap_singleton'] at observed
  subst observed
  exact replay

/-! ## Descendants -/

/-- **A run's descendants are its committed children's blocks**, in order. -/
theorem Exec.descendantFrames_eq_flatMap :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      Exec.descendantFrames run =
        (Exec.childFrames run).flatMap fun c => Exec.committedFrames c.run := by
  intro pc sevm pre out run
  induction run with
  | halt _ => simp only [Exec.descendantFrames, Exec.childFrames, List.flatMap_nil]
  | cont _ next ih =>
      simp only [Exec.descendantFrames, Exec.childFrames]
      exact ih
  | doneErr _ _ _ => simp only [Exec.descendantFrames, Exec.childFrames, List.flatMap_nil]
  | doneOk _ _ _ next ih =>
      simp only [Exec.descendantFrames, Exec.childFrames]
      exact ih
  | runErr _ _ _ _ => simp only [Exec.descendantFrames, Exec.childFrames, List.flatMap_nil]
  | runOk hstep henter child hresume next childIh nextIh =>
      rename_i nodePc nodeSevm nodePre frame rsm nextPc cevm raw inter final
      by_cases hs : Frame.settlementCommits frame raw = true
      · have hchildren : Exec.childFrames (Exec.runOk hstep henter child hresume next) =
            Exec.Frame.ofRun child (Frame.raw_commits_of_settlementCommits hs) ::
              Exec.childFrames next := by
          simp only [Exec.childFrames, dite_eq_left hs, List.singleton_append]
        rw [hchildren, Exec.descendantFrames_runOk_of_settlementCommits hstep henter child hresume
          next hs, List.flatMap_cons, ← nextIh, Exec.Frame.committedFrames_self]
        rfl
      · have hchildren : Exec.childFrames (Exec.runOk hstep henter child hresume next) =
            Exec.childFrames next := by
          simp only [Exec.childFrames, dite_eq_right hs, List.nil_append]
        rw [hchildren, Exec.descendantFrames_runOk_of_not_settlementCommits hstep henter child
          hresume next hs]
        exact nextIh

/-- A position in a list of committed blocks lies in one block. -/
theorem List.flatMap_committed_split {f : Exec.Frame} :
    ∀ {cs m n : List Exec.Frame},
      cs.flatMap (fun c => Exec.committedFrames c.run) = m ++ f :: n →
      ∃ (cs₁ : List Exec.Frame) (c : Exec.Frame) (cs₂ m' n' : List Exec.Frame),
        cs = cs₁ ++ c :: cs₂ ∧ m = cs₁.flatMap (fun c => Exec.committedFrames c.run) ++ m' ∧
          Exec.committedFrames c.run = m' ++ f :: n'
  | [], m, n, h => by
      rw [List.flatMap_nil] at h
      exact absurd h.symm (List.append_ne_nil_of_right_ne_nil m (List.cons_ne_nil f n))
  | c :: rest, m, n, h => by
      rw [List.flatMap_cons] at h
      rcases List.split_append_cons h with ⟨k, hc, -⟩ | ⟨k, hm, hrest⟩
      · exact ⟨[], c, rest, m, k, rfl, by rw [List.flatMap_nil, List.nil_append], hc⟩
      · obtain ⟨cs₁, c', cs₂, m', n', hcs, hk, hc'⟩ := List.flatMap_committed_split hrest
        exact ⟨c :: cs₁, c', cs₂, m', n', by rw [hcs, List.cons_append],
          by rw [hm, hk, List.flatMap_cons, List.append_assoc], hc'⟩


/-- No frame is among its own descendants. -/
theorem Exec.Frame.not_mem_own_descendantFrames (F : Exec.Frame) :
    F ∉ Exec.descendantFrames F.run := by
  intro member
  obtain ⟨x, y, split⟩ := List.append_of_mem member
  obtain ⟨r, hy⟩ := Exec.descendantFrames_contig F.run split
  have len := congrArg List.length split
  rw [hy] at len
  simp only [List.length_append, List.length_cons] at len
  omega

/-- **One child at most**: a run that decodes no external instruction after its first one has no
child, or one child heading its descendants. -/
theorem Exec.single_child_of_silentAfter :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      (∀ N, Exec.Deriv.ParentPrefix ⟨pc, sevm, pre, out, run⟩ N →
        ∀ x, Ninst.At N.sevm.code N.pc (.exec x) →
        ∀ N', Exec.Deriv.ParentStep N' N → ∀ M, Exec.Deriv.ParentPrefix N' M →
          ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y)) →
      Exec.childFrames run = [] ∨ ∃ c, Exec.childFrames run = [c] ∧
        Exec.descendantFrames run = c :: Exec.descendantFrames c.run := by
  intro pc sevm pre out run
  induction run with
  | halt _ => intro _; exact .inl rfl
  | cont step next ih =>
      intro after
      simpa only [Exec.childFrames, Exec.descendantFrames] using
        ih fun N chain => after N (.step (.cont step next) chain)
  | doneErr _ _ _ => intro _; exact .inl rfl
  | doneOk step enter resume next _ =>
      intro after
      obtain ⟨x, hat, -, -⟩ := Evm.step_spawn_inv step
      have quiet := after _ (.refl _) x hat _ (.doneOk step enter resume next)
      left
      simpa only [Exec.childFrames] using Exec.childFrames_eq_nil_of_free ⟨_, _, _, _, next⟩ quiet
  | runErr _ _ _ _ => intro _; exact .inl rfl
  | runOk step enter child resume next ihc ihn =>
      rename_i nodePc nodeSevm nodePre frame rsm nextPc cevm raw inter final
      intro after
      obtain ⟨x, hat, -, -⟩ := Evm.step_spawn_inv step
      have quiet := after _ (.refl _) x hat _ (.runOk step enter child resume next)
      have cnil := Exec.childFrames_eq_nil_of_free ⟨_, _, _, _, next⟩ quiet
      have dnil := Exec.descendantFrames_eq_nil_of_noExec next quiet
      change Exec.childFrames next = [] at cnil
      by_cases settles : Frame.settlementCommits frame raw = true
      · refine .inr ⟨Exec.Frame.ofRun child (Frame.raw_commits_of_settlementCommits settles), ?_, ?_⟩
        · simp only [Exec.childFrames, dite_eq_left settles, cnil, List.append_nil]
        · rw [Exec.descendantFrames_runOk_of_settlementCommits step enter child resume next settles,
            dnil, List.append_nil]
          rfl
      · left
        simp only [Exec.childFrames, dite_eq_right settles, cnil, List.append_nil]

/-! ## Observer chains from local conditions -/

/-- **An observer chain from its local conditions**: every non-static entry that does not observe
is followed by its observer, and every non-static non-entry observer at `T` follows a non-static
entry that does not observe. -/
theorem ObserverChain.of_local {T : Adr} {Obs : Exec.Frame → Prop} {R : Sevm → Sevm → Prop} :
    ∀ (l : List Exec.Frame),
      (∀ b f a, l = b ++ f :: a → IsEntry T f → f.sevm.isStatic = false → ¬ Obs f →
        ∃ o a', a = o :: a' ∧ o.sevm.currentTarget = T ∧ o.sevm.isStatic = false ∧ Obs o ∧
          ¬ IsEntry T o ∧ R f.sevm o.sevm) →
      (∀ b f a, l = b ++ f :: a → f.sevm.currentTarget = T → f.sevm.isStatic = false → Obs f →
        ¬ IsEntry T f → ∃ b' e, b = b' ++ [e] ∧ IsEntry T e ∧ e.sevm.isStatic = false ∧ ¬ Obs e) →
      ObserverChain T Obs R l := by
  intro l
  generalize hn : l.length = n
  induction n using Nat.strongRecOn generalizing l with
  | ind n ih =>
  intro hE hO
  cases l with
  | nil => exact .nil
  | cons f rest =>
  -- the conditions on a suffix `s` of `f :: rest` after `p`, given that the last frame of `p`
  -- leaves no observer at the head of `s`
  have tail : ∀ (p s : List Exec.Frame), f :: rest = p ++ s → p ≠ [] →
      (∀ e, (∃ p', p = p' ++ [e]) → ¬ (IsEntry T e ∧ e.sevm.isStatic = false ∧ ¬ Obs e)) →
      ObserverChain T Obs R s := by
    intro p s split pne last
    have shorter : s.length < n := by
      rw [← hn, split, List.length_append]
      have := List.length_pos_iff.mpr pne
      omega
    refine ih s.length shorter s rfl (fun b g a hs => hE (p ++ b) g a (by rw [split, hs, List.append_assoc]))
      (fun b g a hs target nonstatic obs notEntry => ?_)
    obtain ⟨b', e, hb, eEntry, eStatic, eObs⟩ :=
      hO (p ++ b) g a (by rw [split, hs, List.append_assoc]) target nonstatic obs notEntry
    cases b using List.reverseRecOn with
    | nil =>
        rw [List.append_nil] at hb
        exact (last e ⟨b', hb⟩ ⟨eEntry, eStatic, eObs⟩).elim
    | append_singleton b'' y _ =>
        rw [← List.append_assoc] at hb
        obtain ⟨-, hy⟩ := List.append_inj' hb rfl
        obtain ⟨rfl, -⟩ := List.cons.inj hy
        exact ⟨b'', y, rfl, eEntry, eStatic, eObs⟩
  by_cases hEntry : IsEntry T f ∧ f.sevm.isStatic = false
  · by_cases hObs : Obs f
    · exact .self hEntry.1 hEntry.2 hObs
        (tail [f] rest rfl (List.cons_ne_nil _ _) fun e ⟨p', hp⟩ h => by
          obtain ⟨-, he⟩ := List.append_inj' (hp.symm.trans (List.nil_append [f]).symm) rfl
          obtain ⟨rfl, -⟩ := List.cons.inj he
          exact h.2.2 hObs)
    · obtain ⟨o, a', rfl, oTarget, oStatic, oObs, oEntry, related⟩ :=
        hE [] f rest rfl hEntry.1 hEntry.2 hObs
      exact .pair hEntry.1 hEntry.2 hObs oTarget oStatic oObs oEntry related
        (tail [f, o] a' rfl (List.cons_ne_nil _ _) fun e ⟨p', hp⟩ h => by
          obtain ⟨-, he⟩ := List.append_inj' (hp.symm.trans (show [f, o] = [f] ++ [o] from rfl)) rfl
          obtain ⟨rfl, -⟩ := List.cons.inj he
          exact oEntry h.1)
  · refine .skip hEntry (fun ⟨target, nonstatic, obs⟩ => ?_)
      (tail [f] rest rfl (List.cons_ne_nil _ _) fun e ⟨p', hp⟩ h => by
        obtain ⟨-, he⟩ := List.append_inj' (hp.symm.trans (List.nil_append [f]).symm) rfl
        obtain ⟨rfl, -⟩ := List.cons.inj he
        exact hEntry ⟨h.1, h.2.1⟩)
    by_cases entry : IsEntry T f
    · exact hEntry ⟨entry, nonstatic⟩
    · obtain ⟨b', e, hb, -⟩ := hO [] f rest rfl target nonstatic obs entry
      exact List.append_ne_nil_of_right_ne_nil b' (List.cons_ne_nil e []) hb.symm

/-! ## Settled frames are raw frames -/

variable {cfg : ChainConfig}

private theorem _root_.Blanc.ExecutionTrace.ConfiguredBlockTrace.settled_mem_rawFrames {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) :
    (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ trace.rawFrames := by
  simp only [ConfiguredBlockTrace.settledFrames, AppliedBodyTrace.settledFrames,
    RequestsTrace.settledFrames, List.mem_append] at member
  simp only [ConfiguredBlockTrace.rawFrames, AppliedBodyTrace.rawFrames, RequestsTrace.rawFrames,
    List.mem_append]
  rcases member with ((beacon | history) | transactions) | (withdrawal | consolidation)
  · exact Or.inl (Or.inl (Or.inl (trace.bodyTrace.beacon.mem_rawFrames_of_mem_settledFrames _ beacon)))
  · exact Or.inl (Or.inl (Or.inr
      (trace.bodyTrace.history.mem_rawFrames_of_mem_settledFrames _ history)))
  · exact Or.inl (Or.inr
      (trace.bodyTrace.transactions.mem_rawFrames_of_mem_settledFrames _ transactions))
  · exact Or.inr (Or.inl
      (trace.bodyTrace.requests.withdrawal.mem_rawFrames_of_mem_settledFrames _ withdrawal))
  · exact Or.inr (Or.inr
      (trace.bodyTrace.requests.consolidation.mem_rawFrames_of_mem_settledFrames _ consolidation))

/-- A settled history frame's root derivation is a raw frame of the history. -/
theorem _root_.Blanc.ExecutionTrace.ConfiguredHistoryTrace.settled_mem_rawFrames {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) :
    (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ trace.rawFrames := by
  induction trace with
  | refl => simp only [ConfiguredHistoryTrace.settledFrames, List.not_mem_nil] at member
  | step prior block ih =>
      simp only [ConfiguredHistoryTrace.settledFrames, List.mem_append] at member
      simp only [ConfiguredHistoryTrace.rawFrames, List.mem_append]
      rcases member with member | member
      · exact Or.inl (ih member)
      · exact Or.inr (ConfiguredBlockTrace.settled_mem_rawFrames block frame member)

end Blanc
