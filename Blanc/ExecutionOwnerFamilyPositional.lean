import Blanc.ExecutionOwnerFamily
import Blanc.ExecutionAccountingPositionalHistory

/-!
# The positional law of a code family's ladder

`CodeFamily.ladder` replays every message root of a storage owner whose frames run a family of
codes.  This module adds the positional law (`PositionalLadder.rootAt`): at the entry of every
committed frame not enclosed by an earlier non-static whole frame at the owner
(`CodeFamily.Opaque`), the boundary is the replay of exactly the earlier frames' observations.

The descent is `Exec.positionalAccounting` with the family's target handler
(`CodeFamily.framePositional`): a static frame keeps the owner's storage and observes nothing; an
unguarded frame replays by the unguarded law; a guarded whole frame is opaque, so only its own entry
is selected; a guarded model frame composes its own steps with the positional replay of its single
settled child, located by the root's `CodeSem.At` or, for a `DELEGATECALL`, as a member frame
(`CodeFamily.childCases`).  Member frames descend by `CodeFamily.descend`.

`CodeFamily.positionalLadder` is the resulting `PositionalLadder` and
`CodeFamily.configuredHistory_at` its history law.
-/

namespace Blanc.CodeFamily

open Jaune Blanc.ExecutionAccountingReplay Blanc.ExecutionTrace

variable {ca : Adr}

/-- The positional accounting a pc-`0` frame owes: `Exec.PositionalAccounting`'s conclusion,
without the root code's location (a delegate frame is not located by it). -/
def MemberPositional (entry : Sevm → Devm → Prop) (C : ReplayCarrier ca)
    (V : ReplayObservation C) (Opaque : Exec.Frame → Prop) (sevm : Sevm) (pre : Devm)
    (out : Execution) : Prop :=
  ∀ (run : Exec 0 sevm pre out), Execution.commits out = true →
    CoveredFork sevm.benvStat.fork → Exec.FrameAdmitted ca entry run →
    sum pre.state.bal < 2 ^ 256 →
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      Exec.committedFrames run = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ Opaque A) →
      ∃ steps, C.Replay (C.ofState pre.state) steps (C.ofState f.pre.state) ∧
        V.obs steps = before.flatMap V.frameObs

section Handler

variable {root : CodeSem} {F : CodeFamily ca root} {Guard : Stor → Prop} {Whole : Sevm → Prop}
  {entry : Sevm → Devm → Prop} {C : ReplayCarrier ca} {V : ReplayObservation C}

/-- Member descent of the family's core accounting, from the root ladder's lower-depth
hypothesis. -/
theorem memberAccounting
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsStatic : ∀ f : Exec.Frame, f.sevm.isStatic = true → V.frameObs f = [])
    (unguarded : Unguarded C V Guard)
    (installed : ∀ (sevm : Sevm) (devm : Devm), sevm.currentTarget = ca → entry sevm devm →
      F.DelegatesInstalled devm.state)
    (kinds : F.SpawnKinds Guard) (spawn : F.SpawnReplay Guard Whole entry C V) {k : Nat}
    (deeper : ForallDeeperAtSem k ca root
      (fun pc s d e _ => Exec.CoreAccounting ca root entry C V pc s d e)) :
    F.ForallDeeperMember k (MemberAccounting entry C V) :=
  F.descend (fun _ {_ _ out} _ hm deeperRoot deeperMember => by
    intro run committed fork admitted
    cases out with
    | error error => simp only [Execution.commits, Bool.false_eq_true] at committed
    | ok post =>
        exact frameAccounting append entryOfState ofStateGet obsStatic unguarded installed kinds
          spawn run committed fork admitted hm.2.1 deeperRoot deeperMember) deeper

/-- **The family's core accounting** at every admitted derivation the root's `CodeSem.At`
locates: `Exec.coreAccounting` with the family frame handler. -/
theorem coreAccounting
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    (frameTag : Sevm → Devm → C.Tag)
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsStatic : ∀ f : Exec.Frame, f.sevm.isStatic = true → V.frameObs f = [])
    (obsForeign : ∀ f : Exec.Frame, f.sevm.currentTarget ≠ ca → V.frameObs f = [])
    (unguarded : Unguarded C V Guard)
    (installed : ∀ (sevm : Sevm) (devm : Devm), sevm.currentTarget = ca → entry sevm devm →
      F.DelegatesInstalled devm.state)
    (kinds : F.SpawnKinds Guard) (spawn : F.SpawnReplay Guard Whole entry C V) :
    Exec.Fa (Exec.WknSem ca root
      (fun pc s d e _ => Exec.CoreAccounting ca root entry C V pc s d e)) :=
  Exec.coreAccounting ca root entry C V append frameTag
    (fun sevm state _ => entryOfState sevm state) obsForeign
    (fun {sevm pre _} _ target deeper => by
      intro run committed fork installedAt admitted
      exact frameAccounting append entryOfState ofStateGet obsStatic unguarded installed kinds spawn
        run committed fork admitted
        ⟨target, installedAt.1, installed sevm pre target (admitted.root target),
          Or.inl (installedAt.2 target).1⟩
        deeper
        (memberAccounting append entryOfState ofStateGet obsStatic unguarded installed kinds spawn
          deeper))

/-- **The family child classification**, positionally: the child of a spawning node on a guarded
family frame's chain is entered deeper, on a covered fork, admitted, and is located by the root's
`CodeSem.At` (a `CALL`/`STATICCALL` child) or is a pc-`0` frame of a delegate (a `DELEGATECALL`
child). -/
theorem childCases
    (installed : ∀ (sevm : Sevm) (devm : Devm), sevm.currentTarget = ca → entry sevm devm →
      F.DelegatesInstalled devm.state)
    (kinds : F.SpawnKinds Guard)
    {sevm₀ : Sevm} {pre₀ post₀ : Devm} (run : Exec 0 sevm₀ pre₀ (.ok post₀))
    (runs : F.Runs sevm₀ pre₀) (fork : CoveredFork sevm₀.benvStat.fork)
    (guard : Guard (pre₀.state.getStor ca)) (admitted : Exec.FrameAdmitted ca entry run)
    {nodePc : Nat} {nodeSevm : Sevm} {nodePre : Devm} {out : Execution} {frame : Jaune.Frame}
    {rsm : Resume} {nextPc : Nat} {cevm : Evm} {raw : Execution} {inter : Devm}
    (step : Evm.step ⟨nodePc, nodeSevm, nodePre⟩ = .spawn frame rsm nextPc)
    (enter : frame.enter = .run cevm) (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (resume : rsm.run (frame.settle raw) = .ok inter) (next : Exec nextPc nodeSevm inter out)
    (chain : Exec.Deriv.ParentPrefix ⟨0, sevm₀, pre₀, .ok post₀, run⟩
      ⟨nodePc, nodeSevm, nodePre, out, .runOk step enter child resume next⟩) :
    cevm.sta.depth < sevm₀.depth ∧ CoveredFork cevm.sta.benvStat.fork ∧
      Exec.FrameAdmitted ca entry child ∧
      (root.At ca cevm.pc cevm.sta cevm.dyna ∨
        (cevm.pc = 0 ∧ ∃ m, F.MemberAt m cevm.sta cevm.dyna)) := by
  have sevmEq : nodeSevm = sevm₀ := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  obtain ⟨x, instruction, spawnStep, _⟩ := Evm.step_spawn_inv step
  have kind := kinds run runs fork guard _ chain x instruction
  obtain ⟨-, codeEq⟩ := Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain
  have codeNe : (pre₀.getCode ca).toList ≠ [] := fun empty =>
    root.ne_nil (runs.2.1.symm.trans (congrArg some empty)) rfl
  have nodeInstalled : some (nodePre.getCode ca).toList = root.image := by
    rw [show nodePre.getCode ca = pre₀.getCode ca from codeEq ca codeNe]
    exact runs.2.1
  have nodeFork : CoveredFork nodeSevm.benvStat.fork := by rw [sevmEq]; exact fork
  have childFork := Evm.step_spawn_child_fork step enter nodeFork
  have childDepth : cevm.sta.depth < sevm₀.depth := by
    rw [Frame.enter_run_depth enter, ← sevmEq]
    exact Step.spawn_depth_lt step
  have childAdmitted : Exec.FrameAdmitted ca entry child := by
    intro childRoot member selected
    apply admitted childRoot _ selected
    apply List.mem_cons_of_mem
    apply Exec.mem_rawFrameDescendants_of_parentPrefix chain
    simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append]
    simp only [Exec.rawFrameRoots, List.mem_cons] at member
    rcases member with rfl | member
    · exact Or.inl rfl
    · exact Or.inr (Or.inl member)
  refine ⟨childDepth, childFork, childAdmitted, ?_⟩
  obtain ⟨pcZero, getCode, _⟩ := Evm.step_spawn_child step enter
  rcases kind with hx | hx | ⟨hx, members⟩
  rotate_right
  · subst hx
    obtain ⟨g, a, rest, stack⟩ := Xinst.step_delegatecall_spawn_stack spawnStep
    obtain ⟨m, hm, addr⟩ := members g a rest stack
    have mNe : (pre₀.getCode m.addr).toList ≠ [] := fun empty =>
      m.sem.ne_nil ((runs.2.2.1 m hm).symm.trans (congrArg some empty)) rfl
    have nodeM : some (nodePre.getCode a.toAdr).toList = m.sem.image := by
      rw [addr, codeEq m.addr mNe]
      exact runs.2.2.1 m hm
    obtain ⟨tgt, caddr⟩ := Xinst.step_delegatecall_spawn_owner nodeFork spawnStep stack
      (m.sem.not_delegation nodeM)
    have code := Xinst.step_delegatecall_spawn_code spawnStep stack (m.sem.not_delegation nodeM)
    have childTarget : cevm.sta.currentTarget = ca := by
      rw [Frame.enter_run_currentTarget enter, tgt, sevmEq]
      exact runs.1
    have childCode : some cevm.sta.code.toList = m.sem.image := by
      rw [Frame.enter_run_code enter, code]
      exact nodeM
    have childAddr : cevm.sta.codeAddress = some m.addr := by
      rw [Frame.enter_run_codeAddress enter, caddr, addr]
    refine .inr ⟨pcZero, m, hm, ⟨childTarget, ?_, installed _ _ childTarget
      (childAdmitted.root childTarget), Or.inr ⟨m, hm, childAddr, childCode⟩⟩, childAddr,
      childCode⟩
    rw [getCode ca]
    exact nodeInstalled
  all_goals
    refine .inl ⟨?_, fun selected => ⟨?_, pcZero⟩⟩
    · rw [getCode ca]
      exact nodeInstalled
    · have sameTarget : frame.inner.currentTarget = nodeSevm.currentTarget := by
        rw [← Frame.enter_run_currentTarget enter, selected, sevmEq, runs.1]
      have notDel : ¬ isValidDelegation (nodePre.getCode frame.inner.currentTarget) := by
        rw [← Frame.enter_run_currentTarget enter, selected]
        exact root.not_delegation nodeInstalled
      have directCode : frame.inner.code = nodePre.getCode frame.inner.currentTarget := by
        subst hx
        first
          | exact Xinst.step_call_sameTarget_code spawnStep sameTarget notDel
          | exact Xinst.step_staticcall_sameTarget_code spawnStep sameTarget notDel
      rw [Frame.enter_run_code enter, directCode, ← Frame.enter_run_currentTarget enter,
        selected]
      exact nodeInstalled

/-- **The family positional frame handler.**  A pc-`0` family frame is positional, from the
lower-depth hypotheses of the root ladder and of the delegates (core and positional): a static
frame keeps the owner's storage and observes nothing; an unguarded frame replays by the unguarded
law; a guarded whole frame is opaque; a guarded model frame composes its own steps with its settled
child's positional replay. -/
theorem framePositional
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsStatic : ∀ f : Exec.Frame, f.sevm.isStatic = true → V.frameObs f = [])
    (unguarded : Unguarded C V Guard)
    (installed : ∀ (sevm : Sevm) (devm : Devm), sevm.currentTarget = ca → entry sevm devm →
      F.DelegatesInstalled devm.state)
    (kinds : F.SpawnKinds Guard) (spawn : F.SpawnReplay Guard Whole entry C V)
    {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true) (fork : CoveredFork sevm.benvStat.fork)
    (admitted : Exec.FrameAdmitted ca entry run) (runs : F.Runs sevm pre)
    (bound : sum pre.state.bal < 2 ^ 256)
    (deeperCore : ForallDeeperAtSem sevm.depth ca root
      (fun pc s d e _ => Exec.CoreAccounting ca root entry C V pc s d e))
    (deeperMemberCore : F.ForallDeeperMember sevm.depth (MemberAccounting entry C V))
    (deeper : ForallDeeperAtSem sevm.depth ca root
      (fun pc s d e _ => Exec.PositionalAccounting ca root entry C V (Opaque ca Whole) pc s d e))
    (deeperMember : F.ForallDeeperMember sevm.depth
      (MemberPositional entry C V (Opaque ca Whole))) :
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      Exec.committedFrames run = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ Opaque ca Whole A) →
      ∃ steps, C.Replay (C.ofState pre.state) steps (C.ofState f.pre.state) ∧
        V.obs steps = before.flatMap V.frameObs := by
  intro before f after split noOpaque
  have codeNe : (pre.getCode ca).toList ≠ [] := fun empty =>
    root.ne_nil (runs.2.1.symm.trans (congrArg some empty)) rfl
  by_cases hs : sevm.isStatic = true
  · have obsNil := (frameAccounting append entryOfState ofStateGet obsStatic unguarded installed
      kinds spawn run committed fork admitted runs deeperCore deeperMemberCore).1 hs
    rw [split, List.flatMap_append] at obsNil
    have member : f ∈ Exec.committedFrames run := by
      rw [split]; exact List.mem_append_right _ (List.mem_cons_self ..)
    rw [Exec.committedFrames, dite_eq_left committed] at member
    have stor : f.pre.state.getStor ca = pre.state.getStor ca := by
      rcases List.mem_cons.mp member with rfl | member
      · rfl
      · exact Exec.descendantFrames_getStor_of_static run hs committed fork codeNe f member
    refine ⟨[], C.nilOfEq (ofStateGet fun k => congrArg (fun t => Stor.get t k) stor), ?_⟩
    rw [V.obs_nil, (List.append_eq_nil_iff.mp obsNil).1]
  have hs' : sevm.isStatic = false := by simpa only [Bool.not_eq_true] using hs
  by_cases guard : Guard (pre.state.getStor ca)
  · obtain ⟨-, model⟩ := spawn run committed runs fork admitted bound hs' guard
    by_cases hw : Whole sevm
    · rw [Exec.committedFrames, dite_eq_left committed] at split
      cases before with
      | nil =>
          obtain ⟨rfl, -⟩ := List.cons.inj split
          exact ⟨[], C.nil _, by rw [V.obs_nil, List.flatMap_nil]⟩
      | cons P rest =>
          rw [List.cons_append] at split
          obtain ⟨hP, hdesc⟩ := List.cons.inj split
          subst hP
          refine (noOpaque _ (List.mem_cons_self ..) ?_ ⟨runs.1, hs', hw⟩).elim
          change f ∈ Exec.descendantFrames run
          rw [hdesc]
          exact List.mem_append_right _ (List.mem_cons_self ..)
    · obtain ⟨own, hown, -, c12⟩ := model hw
      refine Exec.PositionalAccounting.modelFrameAt ofStateGet append run committed fork codeNe
        bound ?_ own hown c12 before f after split noOpaque
      intro _ _ _ _ _ _ _ cevm raw _ step enter child resume next chain childCommitted
        childBound before' f' after' split' noOpaque'
      obtain ⟨childDepth, childFork, childAdmitted, located⟩ :=
        childCases installed kinds run runs fork guard admitted step enter child resume next chain
      rcases located with childAt | ⟨pcZero, m, hm⟩
      · exact deeper _ _ _ _ child childDepth childAt child childCommitted childFork childAt
          childAdmitted childBound before' f' after' split' noOpaque'
      · obtain ⟨cpc, csta, cdyna⟩ := cevm
        dsimp only at pcZero
        subst pcZero
        exact deeperMember m csta cdyna raw child childDepth hm child childCommitted childFork
          childAdmitted childBound before' f' after' split' noOpaque'
  · exact unguarded pre.state _ _ guard

end Handler

/-- **The family positional ladder** (`Opaque` = non-static whole frames at the owner). -/
noncomputable def positionalLadder {c : ContractSpecSem} {entry : Sevm → Devm → Prop}
    (F : CodeFamily ca c.sem) (Guard : Stor → Prop) (Whole : Sevm → Prop)
    (C : ReplayCarrier ca) (V : ReplayObservation C)
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    (tag : Nat → Option Nat → C.Tag) (frameTag : Sevm → Devm → C.Tag)
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsStatic : ∀ f : Exec.Frame, f.sevm.isStatic = true → V.frameObs f = [])
    (obsForeign : ∀ f : Exec.Frame, f.sevm.currentTarget ≠ ca → V.frameObs f = [])
    (unguarded : Unguarded C V Guard)
    (installed : ∀ (sevm : Sevm) (devm : Devm), sevm.currentTarget = ca → entry sevm devm →
      F.DelegatesInstalled devm.state)
    (kinds : F.SpawnKinds Guard) (spawn : F.SpawnReplay Guard Whole entry C V)
    (preserves : c.PreservesAdmitted ca entry) : PositionalLadder c ca entry :=
  { F.ladder Guard Whole C V append tag frameTag entryOfState ofStateGet obsStatic obsForeign
      unguarded installed kinds spawn preserves with
    Opaque := Opaque ca Whole
    rootAt := by
      intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed admitted ready _ fork
        bound before f after split noOpaque
      obtain ⟨installedAt, entryBound⟩ :=
        Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
      have core := coreAccounting append frameTag entryOfState ofStateGet obsStatic obsForeign
        unguarded installed kinds spawn
      have deeperCore : ∀ k, ForallDeeperAtSem k ca c.sem
          (fun pc s d e _ => Exec.CoreAccounting ca c.sem entry C V pc s d e) :=
        fun _ pc s d e ex _ hat => core pc s d e ex hat
      have pos := Exec.positionalAccounting (Opaque := Opaque ca Whole) entryOfState ofStateGet
        obsForeign append (fun _ op => op.1) core
        (fun {sevm pre _} _ target deeper => by
          intro run committed fork installedAt admitted bound
          exact framePositional append entryOfState ofStateGet obsStatic unguarded installed kinds
            spawn run committed fork admitted
            ⟨target, installedAt.1, installed sevm pre target (admitted.root target),
              Or.inl (installedAt.2 target).1⟩
            bound (deeperCore _)
            (memberAccounting append entryOfState ofStateGet obsStatic unguarded installed kinds
              spawn (deeperCore _))
            deeper
            (F.descend (fun _ {_ _ out} _ hm deeperRoot deeperMember => by
              intro run committed fork admitted bound
              cases out with
              | error error => simp only [Execution.commits, Bool.false_eq_true] at committed
              | ok post =>
                  exact framePositional append entryOfState ofStateGet obsStatic unguarded
                    installed kinds spawn run committed fork admitted hm.2.1 bound (deeperCore _)
                    (memberAccounting append entryOfState ofStateGet obsStatic unguarded installed
                      kinds spawn (deeperCore _))
                    deeperRoot deeperMember) deeper))
      obtain ⟨steps, replay, observed⟩ := pos pc sevm pre out run installedAt run committed fork
        installedAt admitted entryBound before f after split noOpaque
      refine ⟨steps, ?_, observed⟩
      show C.Replay (C.frameEntry sevm pre.state) steps (C.frameEntry f.sevm f.pre.state)
      rw [entryOfState, entryOfState]
      exact replay }

/-- **The family positional law over a configured history.**  At the entry of every settled frame
not enclosed by an earlier non-static whole frame at the owner, the boundary is the replay, from the
checkpoint, of exactly the earlier settled frames' observations.  (The end law is
`(F.ladder …).configuredHistory`.) -/
theorem configuredHistory_at {c : ContractSpecSem} {entry : Sevm → Devm → Prop}
    (F : CodeFamily ca c.sem) (Guard : Stor → Prop) (Whole : Sevm → Prop)
    (C : ReplayCarrier ca) (V : ReplayObservation C)
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    (tag : Nat → Option Nat → C.Tag) (frameTag : Sevm → Devm → C.Tag)
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsStatic : ∀ f : Exec.Frame, f.sevm.isStatic = true → V.frameObs f = [])
    (obsForeign : ∀ f : Exec.Frame, f.sevm.currentTarget ≠ ca → V.frameObs f = [])
    (unguarded : Unguarded C V Guard)
    (installed : ∀ (sevm : Sevm) (devm : Devm), sevm.currentTarget = ca → entry sevm devm →
      F.DelegatesInstalled devm.state)
    (kinds : F.SpawnKinds Guard) (spawn : F.SpawnReplay Guard Whole entry C V)
    (preserves : c.PreservesAdmitted ca entry) {cfg : ChainConfig}
    {checkpoint future : BlockChain} (history : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : history.FrameAdmitted ca entry) (inv : c.StateInv ca checkpoint.state) :
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      history.settledFrames = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ Opaque ca Whole A) →
      ∃ steps, C.Replay (C.ofState checkpoint.state) steps (C.ofState f.pre.state) ∧
        V.obs steps = before.flatMap V.frameObs := by
  intro before f after split noOpaque
  obtain ⟨steps, replay, observed⟩ :=
    (F.positionalLadder Guard Whole C V append tag frameTag entryOfState ofStateGet obsStatic
      obsForeign unguarded installed kinds spawn preserves).configuredHistory_at history admitted
      inv before f after split noOpaque
  refine ⟨steps, ?_, observed⟩
  change C.Replay (C.ofState checkpoint.state) steps (C.frameEntry f.sevm f.pre.state) at replay
  rw [entryOfState] at replay
  exact replay

end Blanc.CodeFamily
