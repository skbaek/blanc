import Blanc.ExecutionTraceSettledFrames
import Blanc.Lift.CallerProvenance

/-!
# Outermost committed frames at an address

The contract-neutral shape of a committed-replay history (hoisted from the
Uniswap V2 Pair's `pairFrameObs` / `pairSubtreeFrames` / `committedPairFrames`):
one replay step per *outermost* settled, non-static frame at an address, a
re-entered frame at the same address being consumed inside its outermost
ancestor's subtree.

* `Exec.Frame.obsAt ca f` — `[f]` when `f` is a non-static frame at `ca`, else `[]`;
* `Exec.Frame.subtreeAt ca f` — the committed non-static `ca` frames of `f`'s
  subtree, `f` first;
* `ConfiguredHistoryTrace.committedFramesAt ca trace` — every settled non-static
  `ca` frame of the history, in trace order;
* `Exec.outermostDescAt`, `Exec.Frame.outermostAt`,
  `ConfiguredHistoryTrace.outermostFramesAt` — the outermost such frames:
  the traversal never descends below a selected frame.

Facts for a committed-replay theorem:

* `mem_outermostFramesAt` — every outermost frame is settled, at `ca` and
  non-static (`Exec.Frame` itself carries its commit proof);
* `outermostFramesAt_sublist` — outermost frames occur in trace order among the
  committed `ca` frames;
* `outermostFramesAt_partition` — non-nesting: flattening each outermost
  frame's subtree gives exactly the committed `ca` frames, so each committed
  `ca` frame occurs in exactly one outermost frame's subtree and no outermost
  frame occurs inside another's;
* `eq_outermostFramesAt_of_partition` — any list of non-static `ca` frames with
  that partition property *is* the outermost list (so a ladder-produced step
  list, as in the Pair's history, coincides with it);
* `outermostFramesAt_step` — composition along the history.
-/

namespace Blanc

open Jaune

/-! ## Per-frame observation -/

/-- A frame's own observation at `ca`: itself when it is a non-static frame at `ca`. -/
def Exec.Frame.obsAt (ca : Adr) (frame : Exec.Frame) : List Exec.Frame :=
  if frame.sevm.currentTarget = ca ∧ frame.sevm.isStatic = false then [frame] else []

/-- The committed non-static `ca` frames of a frame's subtree, in execution order. -/
def Exec.Frame.subtreeAt (ca : Adr) (frame : Exec.Frame) : List Exec.Frame :=
  (Exec.committedFrames frame.run).flatMap (Exec.Frame.obsAt ca)

theorem Exec.Frame.obsAt_of_target {ca : Adr} {frame : Exec.Frame}
    (target : frame.sevm.currentTarget = ca) (nonstatic : frame.sevm.isStatic = false) :
    Exec.Frame.obsAt ca frame = [frame] := by
  simp only [Exec.Frame.obsAt, target, nonstatic, and_self, ↓reduceIte]

theorem Exec.Frame.obsAt_of_not {ca : Adr} {frame : Exec.Frame}
    (h : ¬ (frame.sevm.currentTarget = ca ∧ frame.sevm.isStatic = false)) :
    Exec.Frame.obsAt ca frame = [] := by
  simp only [Exec.Frame.obsAt, h, ↓reduceIte]

theorem Exec.Frame.obsAt_static {ca : Adr} {frame : Exec.Frame}
    (h : frame.sevm.isStatic = true) : Exec.Frame.obsAt ca frame = [] := by
  simp only [Exec.Frame.obsAt, h, Bool.true_eq_false, and_false, ↓reduceIte]

theorem Exec.Frame.obsAt_foreign {ca : Adr} {frame : Exec.Frame}
    (h : frame.sevm.currentTarget ≠ ca) : Exec.Frame.obsAt ca frame = [] := by
  simp only [Exec.Frame.obsAt, h, false_and, ↓reduceIte]

theorem Exec.Frame.mem_obsAt {ca : Adr} {frame other : Exec.Frame} :
    other ∈ Exec.Frame.obsAt ca frame ↔
      other = frame ∧ frame.sevm.currentTarget = ca ∧ frame.sevm.isStatic = false := by
  unfold Exec.Frame.obsAt
  split
  · rename_i h
    simp only [List.mem_singleton, h, and_self, and_true]
  · rename_i h
    simp only [List.not_mem_nil, false_iff, not_and]
    intro _ target nonstatic
    exact h ⟨target, nonstatic⟩

/-- A retained frame is the head of its own committed frames. -/
theorem Exec.Frame.committedFrames_run (frame : Exec.Frame) :
    Exec.committedFrames frame.run = frame :: Exec.descendantFrames frame.run := by
  simp only [Exec.committedFrames, frame.committed, ↓reduceDIte]
  rfl

/-- A non-static frame at `ca` heads its own subtree. -/
theorem Exec.Frame.subtreeAt_of_target {ca : Adr} {frame : Exec.Frame}
    (target : frame.sevm.currentTarget = ca) (nonstatic : frame.sevm.isStatic = false) :
    Exec.Frame.subtreeAt ca frame = frame :: (Exec.descendantFrames frame.run).flatMap (Exec.Frame.obsAt ca) := by
  simp only [Exec.Frame.subtreeAt, Exec.Frame.committedFrames_run frame, List.flatMap_cons,
    Exec.Frame.obsAt_of_target target nonstatic, List.singleton_append]

/-! ## Outermost frames of an execution -/

/-- The outermost committed non-static `ca` frames strictly below an execution:
a settled child at `ca` is selected and not descended into; any other settled
child is descended into. -/
def Exec.outermostDescAt (ca : Adr) {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) : List Exec.Frame :=
  match run with
  | .halt _ => []
  | .cont _ next => Exec.outermostDescAt ca next
  | .doneErr _ _ _ => []
  | .doneOk _ _ _ next => Exec.outermostDescAt ca next
  | .runErr _ _ _ _ => []
  | .runOk (f := frame) (raw := raw) _ _ child _ next =>
      let childFrames :=
        if h : Frame.settlementCommits frame raw = true then
          let c := Exec.Frame.ofRun child (Frame.raw_commits_of_settlementCommits h)
          if c.sevm.currentTarget = ca ∧ c.sevm.isStatic = false then [c]
          else Exec.outermostDescAt ca child
        else []
      childFrames ++ Exec.outermostDescAt ca next
termination_by sizeOf run

/-- The outermost committed non-static `ca` frames of a retained frame's subtree:
the frame itself when it is one, otherwise the outermost ones below it. -/
def Exec.Frame.outermostAt (ca : Adr) (frame : Exec.Frame) : List Exec.Frame :=
  if frame.sevm.currentTarget = ca ∧ frame.sevm.isStatic = false then [frame]
  else Exec.outermostDescAt ca frame.run

/-- Partition below an execution: the subtrees of the outermost `ca` frames
flatten to exactly the observed descendant frames. -/
theorem Exec.outermostDescAt_partition (ca : Adr) {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) :
    (Exec.outermostDescAt ca run).flatMap (Exec.Frame.subtreeAt ca) =
      (Exec.descendantFrames run).flatMap (Exec.Frame.obsAt ca) := by
  induction run with
  | halt hstep =>
      simp only [Exec.outermostDescAt, Exec.descendantFrames, List.flatMap_nil]
  | cont hstep next ih =>
      simp only [Exec.outermostDescAt, Exec.descendantFrames]
      exact ih
  | doneErr hstep henter hresume =>
      simp only [Exec.outermostDescAt, Exec.descendantFrames, List.flatMap_nil]
  | doneOk hstep henter hresume next ih =>
      simp only [Exec.outermostDescAt, Exec.descendantFrames]
      exact ih
  | runErr hstep henter child hresume ih =>
      simp only [Exec.outermostDescAt, Exec.descendantFrames, List.flatMap_nil]
  | runOk hstep henter child hresume next ihChild ihNext =>
      rename_i frame _ _ _ raw _
      simp only [Exec.outermostDescAt, Exec.descendantFrames, List.flatMap_append, ihNext]
      congr 1
      split
      · rename_i commits
        let c := Exec.Frame.ofRun child (Frame.raw_commits_of_settlementCommits commits)
        have hc : Exec.descendantFrames c.run = Exec.descendantFrames child := rfl
        split
        · rename_i sel
          rw [List.flatMap_cons, List.flatMap_nil, List.append_nil,
            Exec.Frame.subtreeAt_of_target sel.1 sel.2, List.flatMap_cons,
            Exec.Frame.obsAt_of_target sel.1 sel.2, hc, List.singleton_append]
        · rename_i sel
          rw [ihChild, List.flatMap_cons, Exec.Frame.obsAt_of_not sel, List.nil_append]
      · rfl

/-- Partition of one retained frame's subtree by its outermost `ca` frames. -/
theorem Exec.Frame.outermostAt_partition (ca : Adr) (frame : Exec.Frame) :
    (Exec.Frame.outermostAt ca frame).flatMap (Exec.Frame.subtreeAt ca) = Exec.Frame.subtreeAt ca frame := by
  unfold Exec.Frame.outermostAt
  split
  · rename_i sel
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  · rename_i sel
    rw [Exec.outermostDescAt_partition, Exec.Frame.subtreeAt, Exec.Frame.committedFrames_run frame,
      List.flatMap_cons, Exec.Frame.obsAt_of_not sel, List.nil_append]

theorem Exec.mem_outermostDescAt {ca : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) :
    ∀ frame ∈ Exec.outermostDescAt ca run,
      frame.sevm.currentTarget = ca ∧ frame.sevm.isStatic = false := by
  induction run with
  | halt hstep => simp only [Exec.outermostDescAt, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true]
  | cont hstep next ih => simpa only [Exec.outermostDescAt] using ih
  | doneErr hstep henter hresume => simp only [Exec.outermostDescAt, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true]
  | doneOk hstep henter hresume next ih => simpa only [Exec.outermostDescAt] using ih
  | runErr hstep henter child hresume ih => simp only [Exec.outermostDescAt, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true]
  | runOk hstep henter child hresume next ihChild ihNext =>
      intro frame member
      simp only [Exec.outermostDescAt, List.mem_append] at member
      rcases member with member | member
      · split at member
        · split at member
          · rename_i sel
            rw [List.mem_singleton] at member
            subst member
            exact sel
          · exact ihChild frame member
        · exact absurd member List.not_mem_nil
      · exact ihNext frame member

theorem Exec.Frame.mem_outermostAt {ca : Adr} {frame : Exec.Frame} :
    ∀ other ∈ Exec.Frame.outermostAt ca frame,
      other.sevm.currentTarget = ca ∧ other.sevm.isStatic = false := by
  intro other member
  unfold Exec.Frame.outermostAt at member
  split at member
  · rename_i sel
    rw [List.mem_singleton] at member
    subst member
    exact sel
  · exact Exec.mem_outermostDescAt frame.run other member

/-! ## Headed flattening -/

/-- A list whose images each begin with the element itself is a sublist of its
flattening. -/
theorem List.sublist_flatMap_of_headed {α : Type _} {g : α → List α} :
    ∀ {l : List α}, (∀ x ∈ l, ∃ rest, g x = x :: rest) → l.Sublist (l.flatMap g)
  | [], _ => List.Sublist.slnil
  | x :: l, headed => by
      obtain ⟨rest, hx⟩ := headed x List.mem_cons_self
      rw [List.flatMap_cons, hx, List.cons_append]
      exact List.Sublist.cons_cons x
        ((List.sublist_flatMap_of_headed (fun y hy => headed y (List.mem_cons_of_mem x hy))).trans
          (List.sublist_append_right rest _))

/-- A flattening by images that each begin with their element determines the
list. -/
theorem List.eq_of_flatMap_headed {α : Type _} {g : α → List α} {P : α → Prop}
    (headed : ∀ x, P x → ∃ rest, g x = x :: rest) :
    ∀ {l l' : List α}, (∀ x ∈ l, P x) → (∀ x ∈ l', P x) →
      l.flatMap g = l'.flatMap g → l = l'
  | [], [], _, _, _ => rfl
  | [], x :: _, _, hl', eq => by
      obtain ⟨rest, hx⟩ := headed x (hl' x List.mem_cons_self)
      rw [List.flatMap_nil, List.flatMap_cons, hx] at eq
      exact absurd eq (List.cons_ne_nil _ _).symm
  | x :: _, [], hl, _, eq => by
      obtain ⟨rest, hx⟩ := headed x (hl x List.mem_cons_self)
      rw [List.flatMap_nil, List.flatMap_cons, hx] at eq
      exact absurd eq (List.cons_ne_nil _ _)
  | x :: l, y :: l', hl, hl', eq => by
      obtain ⟨rx, hx⟩ := headed x (hl x List.mem_cons_self)
      obtain ⟨ry, hy⟩ := headed y (hl' y List.mem_cons_self)
      have eq' := eq
      rw [List.flatMap_cons, List.flatMap_cons, hx, hy, List.cons_append, List.cons_append,
        List.cons.injEq] at eq'
      obtain ⟨rfl, -⟩ := eq'
      rw [List.flatMap_cons, List.flatMap_cons] at eq
      have tail := List.append_cancel_left eq
      rw [List.eq_of_flatMap_headed headed (fun z hz => hl z (List.mem_cons_of_mem x hz))
        (fun z hz => hl' z (List.mem_cons_of_mem x hz)) tail]

theorem Exec.Frame.subtreeAt_headed {ca : Adr} (frame : Exec.Frame)
    (sel : frame.sevm.currentTarget = ca ∧ frame.sevm.isStatic = false) :
    ∃ rest, Exec.Frame.subtreeAt ca frame = frame :: rest :=
  ⟨_, Exec.Frame.subtreeAt_of_target sel.1 sel.2⟩

/-! ## Configured histories -/

namespace ExecutionTrace

variable {cfg : ChainConfig} {checkpoint future : BlockChain}

/-- Every settled non-static `ca` frame of a configured history, in trace order. -/
def ConfiguredHistoryTrace.committedFramesAt (ca : Adr)
    (trace : ConfiguredHistoryTrace cfg checkpoint future) : List Exec.Frame :=
  trace.settledFrames.flatMap (Exec.Frame.obsAt ca)

/-- The outermost settled non-static `ca` frames of a configured history, in
trace order: per settled message root, the root itself when it is one,
otherwise the outermost ones below it. -/
def ConfiguredHistoryTrace.outermostFramesAt (ca : Adr)
    (trace : ConfiguredHistoryTrace cfg checkpoint future) : List Exec.Frame :=
  trace.settledRoots.flatMap (Exec.Frame.outermostAt ca)

theorem ConfiguredHistoryTrace.mem_committedFramesAt {ca : Adr}
    {trace : ConfiguredHistoryTrace cfg checkpoint future} {frame : Exec.Frame} :
    frame ∈ trace.committedFramesAt ca ↔
      frame ∈ trace.settledFrames ∧ frame.sevm.currentTarget = ca ∧
        frame.sevm.isStatic = false := by
  simp only [committedFramesAt, List.mem_flatMap, Exec.Frame.mem_obsAt]
  constructor
  · rintro ⟨g, member, rfl, sel⟩
    exact ⟨member, sel⟩
  · rintro ⟨member, sel⟩
    exact ⟨frame, member, rfl, sel⟩

theorem ConfiguredHistoryTrace.committedFramesAt_sublist (ca : Adr)
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    (trace.committedFramesAt ca).Sublist trace.settledFrames := by
  unfold committedFramesAt
  induction trace.settledFrames with
  | nil => exact List.Sublist.slnil
  | cons f l ih =>
      rw [List.flatMap_cons]
      unfold Exec.Frame.obsAt
      split
      · exact List.Sublist.cons_cons f ih
      · exact List.Sublist.cons f ih

/-- **Non-nesting.**  The subtrees of the outermost `ca` frames flatten to
exactly the settled non-static `ca` frames of the history. -/
theorem ConfiguredHistoryTrace.outermostFramesAt_partition (ca : Adr)
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    (trace.outermostFramesAt ca).flatMap (Exec.Frame.subtreeAt ca) =
      trace.committedFramesAt ca := by
  rw [outermostFramesAt, committedFramesAt, trace.settledFrames_eq, rootFrames,
    List.flatMap_assoc, List.flatMap_assoc]
  congr 1
  funext root
  rw [Exec.Frame.outermostAt_partition]
  rfl

/-- Every outermost frame is a settled non-static frame at `ca`. -/
theorem ConfiguredHistoryTrace.mem_outermostFramesAt {ca : Adr}
    {trace : ConfiguredHistoryTrace cfg checkpoint future} {frame : Exec.Frame}
    (member : frame ∈ trace.outermostFramesAt ca) :
    frame ∈ trace.settledFrames ∧ frame.sevm.currentTarget = ca ∧
      frame.sevm.isStatic = false := by
  have sel : frame.sevm.currentTarget = ca ∧ frame.sevm.isStatic = false := by
    simp only [outermostFramesAt, List.mem_flatMap] at member
    obtain ⟨root, _, member⟩ := member
    exact Exec.Frame.mem_outermostAt frame member
  obtain ⟨rest, hrest⟩ := Exec.Frame.subtreeAt_headed frame sel
  have inSubtree : frame ∈ (trace.outermostFramesAt ca).flatMap (Exec.Frame.subtreeAt ca) :=
    List.mem_flatMap.mpr ⟨frame, member, by rw [hrest]; exact List.mem_cons_self⟩
  rw [trace.outermostFramesAt_partition ca] at inSubtree
  exact mem_committedFramesAt.mp inSubtree

/-- Outermost frames occur in trace order among the committed `ca` frames. -/
theorem ConfiguredHistoryTrace.outermostFramesAt_sublist (ca : Adr)
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    (trace.outermostFramesAt ca).Sublist (trace.committedFramesAt ca) := by
  rw [← trace.outermostFramesAt_partition ca]
  exact List.sublist_flatMap_of_headed fun frame member =>
    Exec.Frame.subtreeAt_headed frame (mem_outermostFramesAt member).2

/-- **Uniqueness.**  Any list of non-static `ca` frames whose subtrees flatten
to the committed `ca` frames is the outermost list. -/
theorem ConfiguredHistoryTrace.eq_outermostFramesAt_of_partition {ca : Adr}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) {frames : List Exec.Frame}
    (sel : ∀ frame ∈ frames, frame.sevm.currentTarget = ca ∧ frame.sevm.isStatic = false)
    (partition : frames.flatMap (Exec.Frame.subtreeAt ca) = trace.committedFramesAt ca) :
    frames = trace.outermostFramesAt ca :=
  List.eq_of_flatMap_headed (P := fun frame : Exec.Frame =>
      frame.sevm.currentTarget = ca ∧ frame.sevm.isStatic = false)
    (fun frame h => Exec.Frame.subtreeAt_headed frame h) sel
    (fun _ member => (mem_outermostFramesAt member).2)
    (partition.trans (trace.outermostFramesAt_partition ca).symm)

/-- Outermost frames compose along the history, block by block. -/
theorem ConfiguredHistoryTrace.outermostFramesAt_step (ca : Adr)
    {current : BlockChain}
    (prior : ConfiguredHistoryTrace cfg checkpoint current)
    (block : ConfiguredBlockTrace cfg current future) :
    (ConfiguredHistoryTrace.step prior block).outermostFramesAt ca =
      prior.outermostFramesAt ca ++ block.settledRoots.flatMap (Exec.Frame.outermostAt ca) := by
  simp only [outermostFramesAt, settledRoots, List.flatMap_append]

theorem ConfiguredHistoryTrace.committedFramesAt_step (ca : Adr)
    {current : BlockChain}
    (prior : ConfiguredHistoryTrace cfg checkpoint current)
    (block : ConfiguredBlockTrace cfg current future) :
    (ConfiguredHistoryTrace.step prior block).committedFramesAt ca =
      prior.committedFramesAt ca ++ block.settledFrames.flatMap (Exec.Frame.obsAt ca) := by
  simp only [committedFramesAt, settledFrames, List.flatMap_append]

end ExecutionTrace

end Blanc
