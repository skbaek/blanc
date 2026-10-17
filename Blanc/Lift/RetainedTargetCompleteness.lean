import Blanc.Lift.SegmentedHistory
import Blanc.Lift.CallChildren
import Blanc.PrefixTransport

/-!
# Direct children along a same-frame chain, and completeness of target selection

Contract-neutral facts about the frames a run retains:

* `Exec.mem_descendantFrames_of_mem_childFrames`, `Exec.Deriv.ExecFreeUntil.childFrames_eq` and
  `Exec.childFrames_eq_nil_of_free`: a span of the chain that decodes no `Xinst` has no direct child;
* `Exec.Deriv.ParentStep.childFrames_spawn` / `descendantFrames_spawn`: at a spawning node, the
  retained frames are the entered child's and those of the continuation;
* `Exec.descendantFrames_isStatic`: below a static run every retained frame is static;
* `Exec.retainedTargetFramesFromAt_complete`: every retained frame at `ca` lies inside one frame that
  `retainedTargetFramesFromAt ca` selects (the selection stops at the outermost target frames).
-/

namespace Blanc

open Jaune

/-- The committed frames of a retained frame's run: the frame itself, then its descendants. -/
theorem Exec.Frame.mem_committedFrames {F D : Exec.Frame} :
    D ∈ Exec.committedFrames F.run ↔ D = F ∨ D ∈ Exec.descendantFrames F.run := by
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := F
  simp only [Exec.committedFrames, committed, ↓reduceDIte, List.mem_cons]
  rfl

/-- A direct child is a retained descendant. -/
theorem Exec.mem_descendantFrames_of_mem_childFrames :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      ∀ c ∈ Exec.childFrames run, c ∈ Exec.descendantFrames run := by
  intro pc sevm pre out run
  induction run with
  | halt _ => intro c member; simp only [Exec.childFrames, List.not_mem_nil] at member
  | cont _ _ ih => simpa only [Exec.childFrames, Exec.descendantFrames] using ih
  | doneErr _ _ _ => intro c member; simp only [Exec.childFrames, List.not_mem_nil] at member
  | doneOk _ _ _ _ ih => simpa only [Exec.childFrames, Exec.descendantFrames] using ih
  | runErr _ _ _ _ => intro c member; simp only [Exec.childFrames, List.not_mem_nil] at member
  | runOk step enter child resume next _ nextIh =>
      intro c member
      simp only [Exec.childFrames, List.mem_append] at member
      simp only [Exec.descendantFrames, List.mem_append]
      rcases member with here | later
      · left
        split at here
        · rename_i settles
          rw [List.mem_singleton] at here
          rw [dite_eq_left_of_eq_true (eq_true settles), here]
          exact List.mem_cons_self
        · simp only [List.not_mem_nil] at here
      · exact Or.inr (nextIh c later)

/-- A chain whose every node decodes no `Xinst` has no direct child. -/
theorem Exec.childFrames_eq_nil_of_free (start : Exec.Deriv)
    (free : ∀ node, Exec.Deriv.ParentPrefix start node →
      ∀ x, ¬ Ninst.At node.sevm.code node.pc (.exec x)) :
    Exec.childFrames start.exc = [] := by
  have none := Exec.descendantFrames_eq_nil_of_no_sameFrame_xinstAt start.exc free
  cases frames : Exec.childFrames start.exc with
  | nil => rfl
  | cons c _ =>
      have member := Exec.mem_descendantFrames_of_mem_childFrames start.exc c
        (by rw [frames]; exact List.mem_cons_self)
      rw [none] at member
      cases member

/-- A frame-entry-free span has no direct child of its own. -/
theorem Exec.Deriv.ExecFreeUntil.childFrames_eq {start stop : Exec.Deriv}
    (free : Exec.Deriv.ExecFreeUntil start stop) :
    Exec.childFrames start.exc = Exec.childFrames stop.exc := by
  rcases free with ⟨reached, clean⟩
  induction reached with
  | refl => rfl
  | @step root next tail edge rest ih =>
      have rootClean : ∀ x : Xinst,
          ¬ Ninst.At root.sevm.code root.pc (.exec x) := by
        rcases clean root (.refl _) with back | rootClean
        · exact ((Blanc.Exec.Deriv.ParentStep.not_parentPrefix_back edge) rest back).elim
        · exact rootClean
      have nextClean : ∀ node, Exec.Deriv.ParentPrefix next node →
          Exec.Deriv.ParentPrefix tail node ∨
            ∀ x : Xinst, ¬ Ninst.At node.sevm.code node.pc (.exec x) :=
        fun node reached => clean node (.step edge reached)
      rw [← ih nextClean]
      cases edge with
      | cont hstep next => simp only [Exec.childFrames]
      | doneOk hstep henter hresume next =>
          rcases Evm.step_spawn_inv hstep with ⟨x, decoded, -, -⟩
          exact (rootClean x decoded).elim
      | runOk hstep henter child hresume next =>
          rcases Evm.step_spawn_inv hstep with ⟨x, decoded, -, -⟩
          exact (rootClean x decoded).elim

/-- At a spawning node, a direct child is the entered child or a child of the continuation. -/
theorem Exec.Deriv.ParentStep.childFrames_spawn {N returned : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep returned N) {frame : Jaune.Frame} {resume : Resume}
    {nextPc : Nat} (spawned : Evm.step ⟨N.pc, N.sevm, N.devm⟩ = .spawn frame resume nextPc) :
    ∀ c ∈ Exec.childFrames N.exc, c ∈ Exec.childFrames returned.exc ∨
      ∃ childEvm : Evm, frame.enter = .run childEvm ∧ c.sevm = childEvm.sta ∧
        c.pre = childEvm.dyna := by
  intro c member
  cases edge with
  | cont hstep next => cases hstep.symm.trans spawned
  | doneOk hstep henter hresume next =>
      exact Or.inl (by simpa only [Exec.childFrames] using member)
  | runOk hstep henter child hresume next =>
      rcases Step.spawn.inj (hstep.symm.trans spawned) with ⟨rfl, rfl, rfl⟩
      simp only [Exec.childFrames, List.mem_append] at member
      rcases member with here | later
      · split at here
        · rw [List.mem_singleton] at here
          subst here
          exact Or.inr ⟨_, henter, rfl, rfl⟩
        · simp only [List.not_mem_nil] at here
      · exact Or.inl later

/-- At a spawning node whose child slot is not entered, only the continuation retains frames. -/
theorem Exec.Deriv.ParentStep.descendantFrames_spawn_done {N returned : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep returned N) {frame : Jaune.Frame} {resume : Resume}
    {nextPc : Nat} (spawned : Evm.step ⟨N.pc, N.sevm, N.devm⟩ = .spawn frame resume nextPc)
    (notRun : ∀ childEvm, frame.enter ≠ .run childEvm) :
    Exec.descendantFrames N.exc = Exec.descendantFrames returned.exc := by
  cases edge with
  | cont hstep next => cases hstep.symm.trans spawned
  | doneOk hstep henter hresume next => simp only [Exec.descendantFrames]
  | runOk hstep henter child hresume next =>
      rcases Step.spawn.inj (hstep.symm.trans spawned) with ⟨rfl, rfl, rfl⟩
      exact (notRun _ henter).elim

/-- At a node that actually ran a child, the retained frames are that child's subtree (when its
settlement commits) followed by the continuation's. -/
theorem Exec.Deriv.ParentStep.descendantFrames_runOk {N returned : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep returned N) {frame : Jaune.Frame} {resume : Resume}
    {nextPc : Nat} {childEvm : Evm} {raw : Execution} {post : Devm}
    {spawn : Evm.step ⟨N.pc, N.sevm, N.devm⟩ = .spawn frame resume nextPc}
    {enter : frame.enter = .run childEvm}
    {childRun : Exec childEvm.pc childEvm.sta childEvm.dyna raw}
    {resumed : resume.run (frame.settle raw) = .ok post}
    {next : Exec nextPc N.sevm post N.exn}
    (nodeExc : N.exc = .runOk spawn enter childRun resumed next) :
    ∀ D ∈ Exec.descendantFrames N.exc, D ∈ Exec.descendantFrames returned.exc ∨
      ∃ settles : Jaune.Frame.settlementCommits frame raw = true,
        D = Exec.Frame.ofRun childRun (Jaune.Frame.raw_commits_of_settlementCommits settles) ∨
          D ∈ Exec.descendantFrames childRun := by
  have nextEdge : Exec.Deriv.ParentStep ⟨nextPc, N.sevm, post, N.exn, next⟩ N := by
    have shaped : Exec.Deriv.ParentStep ⟨nextPc, N.sevm, post, N.exn, next⟩
        ⟨N.pc, N.sevm, N.devm, N.exn, .runOk spawn enter childRun resumed next⟩ :=
      .runOk _ _ _ _ _
    have same : (⟨N.pc, N.sevm, N.devm, N.exn, .runOk spawn enter childRun resumed next⟩ :
        Exec.Deriv) = N := by
      rw [← nodeExc]
    rw [same] at shaped
    exact shaped
  cases nextEdge.unique edge
  intro D member
  rw [nodeExc] at member
  simp only [Exec.descendantFrames, List.mem_append] at member
  rcases member with here | later
  · split at here
    · rename_i settles
      rw [List.mem_cons] at here
      exact Or.inr ⟨settles, here⟩
    · simp only [List.not_mem_nil] at here
  · exact Or.inl later

/-- Below a static run every retained frame is static. -/
theorem Exec.descendantFrames_isStatic :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      sevm.isStatic = true → ∀ D ∈ Exec.descendantFrames run, D.sevm.isStatic = true := by
  intro pc sevm pre out run
  induction run with
  | halt _ => intro _ D member; simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | cont _ _ ih => simpa only [Exec.descendantFrames] using ih
  | doneErr _ _ _ =>
      intro _ D member; simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | doneOk _ _ _ _ ih => simpa only [Exec.descendantFrames] using ih
  | runErr _ _ _ _ =>
      intro _ D member; simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | runOk step enter _ _ _ childIh nextIh =>
      intro static D member
      obtain ⟨x, -, spawn, _⟩ := Evm.step_spawn_inv step
      have childStatic :=
        (Frame.enter_run_isStatic enter).trans (Xinst.step_spawn_isStatic spawn static)
      simp only [Exec.descendantFrames, List.mem_append] at member
      rcases member with here | later
      · split at here
        · rw [List.mem_cons] at here
          rcases here with rfl | deeper
          · exact childStatic
          · exact childIh childStatic D deeper
        · simp only [List.not_mem_nil] at here
      · exact nextIh static D later

/-- **Completeness of target selection.**  Every retained frame at `ca` of a run (the run's own
pseudo-frame or a descendant) lies inside one frame `retainedTargetFramesFromAt ca` selects. -/
theorem Exec.retainedTargetFramesFromAt_complete (ca : Adr) :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
      (path : List Nat) (counter : Nat) (committed : Execution.commits out = true) (D : Exec.Frame),
      (D = Exec.Frame.ofRun run committed ∨ D ∈ Exec.descendantFrames run) →
        D.sevm.currentTarget = ca →
        ∃ located ∈ Exec.retainedTargetFramesFromAt ca path counter run committed,
          located.frame.sevm.currentTarget = ca ∧ D ∈ Exec.committedFrames located.frame.run := by
  intro pc sevm pre out run
  by_cases target : sevm.currentTarget = ca
  · intro path counter committed D member _
    rw [Exec.retainedTargetFramesFromAt_target ca path counter run committed target]
    refine ⟨⟨path, Exec.Frame.ofRun run committed⟩, List.mem_singleton_self _, target, ?_⟩
    exact Exec.Frame.mem_committedFrames.mpr member
  induction run with
  | halt step =>
      intro path counter committed D member atCa
      rcases member with rfl | member
      · exact (target atCa).elim
      · simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | cont step next ih =>
      intro path counter committed D member atCa
      rcases member with rfl | member
      · exact (target atCa).elim
      rw [Exec.retainedTargetFramesFromAt_cont ca path counter step next committed target]
      exact ih target path counter committed D
        (Or.inr (by simpa only [Exec.descendantFrames] using member)) atCa
  | doneErr step entered resumed => intro _ _ committed; cases committed
  | doneOk step entered resumed next ih =>
      intro path counter committed D member atCa
      rcases member with rfl | member
      · exact (target atCa).elim
      rw [Exec.retainedTargetFramesFromAt_doneOk ca path counter step entered resumed next
        committed target]
      exact ih target path (counter + 1) committed D
        (Or.inr (by simpa only [Exec.descendantFrames] using member)) atCa
  | runErr step entered child resumed => intro _ _ committed; cases committed
  | @runOk _ _ _ frame _ _ childEvm raw _ _ step entered child resumed next childIh nextIh =>
      intro path counter committed D member atCa
      rcases member with rfl | member
      · exact (target atCa).elim
      rw [Exec.retainedTargetFramesFromAt_runOk ca path counter step entered child resumed next
        committed target]
      simp only [Exec.descendantFrames, List.mem_append] at member
      rcases member with here | later
      · split at here
        · rename_i settles
          rw [dite_eq_left_of_eq_true (eq_true settles)]
          have childCommitted := Frame.raw_commits_of_settlementCommits settles
          have inChild : D = Exec.Frame.ofRun child childCommitted ∨
              D ∈ Exec.descendantFrames child := List.mem_cons.mp here
          by_cases childTarget : childEvm.sta.currentTarget = ca
          · rw [Exec.retainedTargetFramesFromAt_target ca _ 0 child childCommitted childTarget]
            refine ⟨⟨path ++ [counter], Exec.Frame.ofRun child childCommitted⟩,
              List.mem_append_left _ (List.mem_singleton_self _), childTarget, ?_⟩
            exact Exec.Frame.mem_committedFrames.mpr inChild
          · obtain ⟨located, mem, located_at, inside⟩ :=
              childIh childTarget (path ++ [counter]) 0 childCommitted D inChild atCa
            exact ⟨located, List.mem_append_left _ mem, located_at, inside⟩
        · simp only [List.not_mem_nil] at here
      · obtain ⟨located, mem, located_at, inside⟩ :=
          nextIh target path (counter + 1) committed D (Or.inr later) atCa
        exact ⟨located, List.mem_append_right _ mem, located_at, inside⟩

private theorem GasSchedule.accessDelegation_codeAddress_of_none'
    {gas : GasSchedule} {d : Devm} {adr : Adr}
    (h : getDelegatedCodeAddress (d.getCode adr) = none) :
    (gas.accessDelegation d adr).2.1 = adr := by
  dsimp only [GasSchedule.accessDelegation]
  rw [show getDelegatedCodeAddress (d.state.getCode adr) = none from h]

private theorem GasSchedule.delegationCost_codeAddress_of_none'
    {gas : GasSchedule} {d : Devm} {adr : Adr}
    (h : getDelegatedCodeAddress (d.getCode adr) = none) :
    (gas.delegationCost d adr).2.1 = adr := by
  have hnone : getDelegatedCodeAddress (d.state.getCode adr) = none := h
  unfold GasSchedule.delegationCost
  simp only [hnone]

/-- A `CALL`/`STATICCALL` child message targets its current account. -/
theorem Xinst.step_callKind_spawn_target {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume} (kind : x = .call ∨ x = .staticcall)
    (hs : Xinst.step sevm devm x = .spawn f rsm) :
    f.inner.target = some f.inner.currentTarget := by
  rcases kind with rfl | rfl <;>
    simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hs
  all_goals repeat' split at hs
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
  all_goals first
    | cases hs
    | rw [(genericCall_step_spawn_exact hs).1]; rfl
    | rw [(genericCallAmsterdam_step_spawn_exact hs).1]; rfl

/-- A `CALL`/`STATICCALL` child runs at its callee's own code address unless the callee holds an
EIP-7702 delegation designator (which resolves the code address to the delegate). -/
theorem Xinst.step_callKind_spawn_codeAddress {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume} (kind : x = .call ∨ x = .staticcall)
    (hs : Xinst.step sevm devm x = .spawn f rsm)
    (hnodel : getDelegatedCodeAddress (devm.getCode f.inner.currentTarget) = none) :
    f.inner.codeAddress = some f.inner.currentTarget := by
  rcases kind with rfl | rfl
  · simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hs
    split at hs
    · -- Legacy: no state gas.
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vgas hgas
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vcallee hcallee
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vval hval
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vii hii
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vis his
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ voi hoi
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vos hos
      -- The delegation lookup runs on the popped-and-recorded machine, so the
      -- premise's code fact has to travel down the operand pops first.
      have hgc : ∀ a : Adr,
          (addAccessedAddress vos.2 vcallee.1).getCode a = devm.getCode a := by
        intro a
        rw [addAccessedAddress_getCode, Devm.popToNat_getCode hos,
          Devm.popToNat_getCode hoi, Devm.popToNat_getCode his,
          Devm.popToNat_getCode hii, Devm.pop_getCode hval,
          Devm.popToAdr_getCode hcallee, Devm.pop_getCode hgas]
      repeat' split at hs
      all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
      all_goals first
        | cases hs
        | simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
            Except.pure] at hs
          repeat' split at hs
          all_goals
            simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
          all_goals obtain ⟨rfl, rfl⟩ := hs
          all_goals
            refine congrArg some
              (GasSchedule.accessDelegation_codeAddress_of_none' ?_)
            rw [hgc]
            exact hnodel
    · -- Amsterdam: delegation priced without warming.
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vgas hgas
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vcallee hcallee
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vval hval
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vii hii
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vis his
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ voi hoi
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vos hos
      have hgc : ∀ a : Adr,
          (addAccessedAddress vos.2 vcallee.1).getCode a = devm.getCode a := by
        intro a
        rw [addAccessedAddress_getCode, Devm.popToNat_getCode hos,
          Devm.popToNat_getCode hoi, Devm.popToNat_getCode his,
          Devm.popToNat_getCode hii, Devm.pop_getCode hval,
          Devm.popToAdr_getCode hcallee, Devm.pop_getCode hgas]
      repeat' split at hs
      all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
      all_goals first
        | cases hs
        | simp only [genericCallAmsterdam.step, Bind.bind, Except.bind,
            Pure.pure, Except.pure] at hs
          repeat' split at hs
          all_goals
            simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
          all_goals obtain ⟨rfl, rfl⟩ := hs
          all_goals
            refine congrArg some
              (GasSchedule.delegationCost_codeAddress_of_none' ?_)
            rw [hgc]
            exact hnodel
  · simp only [Xinst.step, Bind.bind, Except.bind] at hs
    split at hs
    · -- Legacy: no state gas.
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vgas hgas
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vtgt htgt
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vii hii
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vis his
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ voi hoi
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vos hos
      have hgc : ∀ a : Adr,
          (addAccessedAddress vos.2 vtgt.1).getCode a = devm.getCode a := by
        intro a
        rw [addAccessedAddress_getCode, Devm.popToNat_getCode hos,
          Devm.popToNat_getCode hoi, Devm.popToNat_getCode his,
          Devm.popToNat_getCode hii, Devm.popToAdr_getCode htgt,
          Devm.pop_getCode hgas]
      repeat' split at hs
      all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
      all_goals first
        | cases hs
        | simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
            Except.pure] at hs
          repeat' split at hs
          all_goals
            simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
          all_goals obtain ⟨rfl, rfl⟩ := hs
          all_goals
            refine congrArg some
              (GasSchedule.accessDelegation_codeAddress_of_none' ?_)
            rw [hgc]
            exact hnodel
    · -- Amsterdam: delegation priced without warming.
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vgas hgas
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vtgt htgt
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vii hii
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vis his
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ voi hoi
      split at hs
      · simp only [XStep.ofExcept, reduceCtorEq] at hs
      rename_i _ vos hos
      have hgc : ∀ a : Adr,
          (addAccessedAddress vos.2 vtgt.1).getCode a = devm.getCode a := by
        intro a
        rw [addAccessedAddress_getCode, Devm.popToNat_getCode hos,
          Devm.popToNat_getCode hoi, Devm.popToNat_getCode his,
          Devm.popToNat_getCode hii, Devm.popToAdr_getCode htgt,
          Devm.pop_getCode hgas]
      repeat' split at hs
      all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
      all_goals first
        | cases hs
        | simp only [genericCallAmsterdam.step, Bind.bind, Except.bind,
            Pure.pure, Except.pure] at hs
          repeat' split at hs
          all_goals
            simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
          all_goals obtain ⟨rfl, rfl⟩ := hs
          all_goals
            refine congrArg some
              (GasSchedule.delegationCost_codeAddress_of_none' ?_)
            rw [hgc]
            exact hnodel

end Blanc
