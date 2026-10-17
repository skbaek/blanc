import Blanc.ExecutionWholeFrameAccounting
import Blanc.OwnerClosure
import Blanc.ExecutionTraceCallOnly
import Blanc.ExecutionCallerExclusion
import Blanc.Lift.RetainedTargetCompleteness
import Blanc.ExecutionAccountingPositional

/-!
# The accounting ladder of a storage owner whose frames run a family of codes

The single-code ladders (`modelLadder`, `wholeFrameLadder`) locate every frame at the owner `ca` with
the root code's `CodeSem.At`: a frame at `ca` runs `ca`'s installed code at pc `0`.  A proxy breaks
that in exactly one place.  A foreign frame enters `ca` only by `CALL` or `STATICCALL`, running the
installed (root) code, and a `DELEGATECALL` keeps its caller's storage owner, so the only frames at
`ca` that run another code are `DELEGATECALL` children of frames at `ca`.  Those children are inside
the target handler, so the family lives there: the eliminator (`Exec.coreAccounting`), the foreign
handlers and the history rungs are unchanged, with the root code as the location.

* `CodeFamily ca root` lists the delegates, tagged by code address; `CodeFamily.Runs` is a pc-`0`
  frame at `ca` running the root or a delegate, `CodeFamily.MemberAt` a delegate frame.
* `CodeFamily.descend` is a strong induction on depth: from the root ladder's lower-depth hypothesis
  and a handler for delegate frames, every delegate frame below a depth.
* The family target handler (`CodeFamily.frameAccounting`) handles a family frame: a static frame
  observes nothing; a frame entered unguarded replays by `CodeFamily.Unguarded`; a guarded frame
  replays as a whole or as a model frame (`CodeFamily.SpawnReplay`), whose children are classified by
  `CodeFamily.SpawnKinds` (`CodeFamily.childReplays`): a `CALL`/`STATICCALL` child is located by the
  root, a `DELEGATECALL` child is a member frame.
* `CodeFamily.ladder` is the resulting `AccountingLadderAdmitted`.

`Exec.descendant_getStor_spawnNode` is the storage fact positions inside a quiet frame need: every
committed descendant enters with the owner's storage at one of the frame's own spawning nodes.
-/

namespace Blanc

open Jaune
open ExecutionAccountingReplay

/-- A `DELEGATECALL` on a covered fork whose address operand holds no delegation designator keeps the
storage owner and carries the operand as its code address. -/
theorem Xinst.step_delegatecall_spawn_owner {sevm : Sevm} {devm : Devm}
    {f : Frame} {rsm : Resume} {g w : B256} {s : List B256}
    (hfork : CoveredFork sevm.benvStat.fork)
    (spawn : Xinst.step sevm devm .delegatecall = .spawn f rsm)
    (hstack : devm.stack = g :: w :: s)
    (notDelegation : ¬ isValidDelegation (devm.getCode w.toAdr)) :
    f.inner.currentTarget = sevm.currentTarget ∧ f.inner.codeAddress = some w.toAdr := by
  have hsg : sevm.benvStat.rules.stateGas = none := hfork.rules_stateGas_none
  have h1 := Devm.pop_eq_ok hstack
  have hs1 : (devm.setMach ⟨w :: s, devm.memory, devm.gasLeft,
      devm.stateGas⟩).stack = w :: s := rfl
  generalize devm.setMach ⟨w :: s, devm.memory, devm.gasLeft, devm.stateGas⟩ = d1
    at h1 hs1
  rcases h2 : d1.popToAdr with err | ⟨cadr, d2⟩
  · rw [Devm.popToAdr_def, Devm.pop_eq_ok hs1] at h2; cases h2
  have hcadr : cadr = w.toAdr := by
    rw [Devm.popToAdr_def, Devm.pop_eq_ok hs1] at h2
    cases h2; rfl
  subst hcadr
  rcases h3 : d2.popToNat with err | ⟨ii, d3⟩
  · simp only [Xinst.step, hsg, XStep.ofExcept, h1, bind_pure_comp, Except.bind_ok, h2, h3,
      Except.bind_error, reduceCtorEq] at spawn
  rcases h4 : d3.popToNat with err | ⟨isz, d4⟩
  · simp only [Xinst.step, hsg, XStep.ofExcept, h1, bind_pure_comp, Except.bind_ok, h2, h3, h4,
      Except.bind_error, reduceCtorEq] at spawn
  rcases h5 : d4.popToNat with err | ⟨oi, d5⟩
  · simp only [Xinst.step, hsg, XStep.ofExcept, h1, bind_pure_comp, Except.bind_ok, h2, h3, h4,
      h5, Except.bind_error, reduceCtorEq] at spawn
  rcases h6 : d5.popToNat with err | ⟨osz, d6⟩
  · simp only [Xinst.step, hsg, XStep.ofExcept, h1, bind_pure_comp, Except.bind_ok, h2, h3, h4,
      h5, h6, Except.bind_error, reduceCtorEq] at spawn
  have hcode : (addAccessedAddress d6 w.toAdr).getCode w.toAdr =
      devm.getCode w.toAdr := by
    rw [addAccessedAddress_getCode, Devm.popToNat_getCode h6,
      Devm.popToNat_getCode h5, Devm.popToNat_getCode h4,
      Devm.popToNat_getCode h3, Devm.popToAdr_getCode h2, Devm.pop_getCode h1]
  have hnd : ¬ isValidDelegation ((addAccessedAddress d6 w.toAdr).getCode w.toAdr) := by
    rw [hcode]; exact notDelegation
  simp only [Xinst.step, hsg, h1, h2, h3, h4, h5, h6, Bind.bind, Except.bind] at spawn
  repeat' split at spawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn
  all_goals first
    | cases spawn
    | refine ⟨(genericCall.step_spawn_frame spawn).2.1, ?_⟩
      rw [genericCall.step_spawn_codeAddress spawn, congrArg (fun t => t.2.1)
        (GasSchedule.accessDelegation_of_not_delegation (gas := sevm.benvStat.rules.gas) hnd)]

/-- A delegate member of a storage owner's code family: the code address its frames carry, and the
certified semantics of the code installed there. -/
structure FamilyMember where
  addr : Adr
  sem : CodeSem

/-- **A code family at the storage owner `ca`.**  `root` is the code installed at `ca`, which every
frame entered at `ca` by `CALL`/`STATICCALL` runs; `delegates` are the codes its frames reach by
`DELEGATECALL`, tagged by code address.  The single-code ladders are the case `delegates = []`. -/
structure CodeFamily (ca : Adr) (root : CodeSem) where
  delegates : List FamilyMember

namespace CodeFamily

variable {ca : Adr} {root : CodeSem}

/-- Every delegate's code is installed at its address. -/
def DelegatesInstalled (F : CodeFamily ca root) (w : State) : Prop :=
  ∀ m ∈ F.delegates, some (w.getCode m.addr).toList = m.sem.image

/-- A pc-0 frame at `ca` running a code of the family, with the family installed: the root's code,
or a delegate's code at that delegate's code address. -/
def Runs (F : CodeFamily ca root) (sevm : Sevm) (pre : Devm) : Prop :=
  sevm.currentTarget = ca ∧ some (pre.getCode ca).toList = root.image ∧
    F.DelegatesInstalled pre.state ∧
    (some sevm.code.toList = root.image ∨
      ∃ m ∈ F.delegates, sevm.codeAddress = some m.addr ∧ some sevm.code.toList = m.sem.image)

/-- A frame of the delegate `m` (a location the root's `CodeSem.At` does not cover). -/
def MemberAt (F : CodeFamily ca root) (m : FamilyMember) (sevm : Sevm) (pre : Devm) : Prop :=
  m ∈ F.delegates ∧ F.Runs sevm pre ∧ sevm.codeAddress = some m.addr ∧
    some sevm.code.toList = m.sem.image

/-- `εm` at every delegate frame of depth below `k`. -/
def ForallDeeperMember (F : CodeFamily ca root) (k : Nat)
    (εm : Sevm → Devm → Execution → Prop) : Prop :=
  ∀ (m : FamilyMember) (sevm : Sevm) (pre : Devm) (out : Execution), Exec 0 sevm pre out →
    sevm.depth < k → F.MemberAt m sevm pre → εm sevm pre out

/-- **Member descent.**  From the root ladder's lower-depth hypothesis (frames the root's
`CodeSem.At` locates: foreign frames, and frames at `ca` running the root's code) and a handler for
delegate frames that may use both lower-depth hypotheses, every delegate frame below `k` satisfies
`εm`.  Strong induction on depth; contract-neutral and predicate-generic. -/
theorem descend (F : CodeFamily ca root) {ε : Nat → Sevm → Devm → Execution → Prop}
    {εm : Sevm → Devm → Execution → Prop}
    (member : ∀ (m : FamilyMember) {sevm : Sevm} {pre : Devm} {out : Execution},
      Exec 0 sevm pre out → F.MemberAt m sevm pre →
      ForallDeeperAtSem sevm.depth ca root (fun pc s d e _ => ε pc s d e) →
      F.ForallDeeperMember sevm.depth εm → εm sevm pre out)
    {k : Nat} (deeper : ForallDeeperAtSem k ca root (fun pc s d e _ => ε pc s d e)) :
    F.ForallDeeperMember k εm := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m sevm pre out run depth hm
    have lower : ForallDeeperAtSem sevm.depth ca root (fun pc s d e _ => ε pc s d e) :=
      fun pc s d e ex hd hat => deeper pc s d e ex (hd.trans depth) hat
    exact member m run hm lower (ih sevm.depth depth lower)

/-- **The family's spawn kinds.**  At a guarded entry, every external instruction a successful
family frame decodes along its own chain is `CALL`, `STATICCALL`, or a `DELEGATECALL` naming a
delegate's address.  (`Guard` reads the owner's storage at the frame's entry: for a proxy, that its
implementation slot names the family's implementation.) -/
def SpawnKinds (F : CodeFamily ca root) (Guard : Stor → Prop) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post)), F.Runs sevm pre →
    CoveredFork sevm.benvStat.fork → Guard (pre.state.getStor ca) →
    ∀ node, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ node →
      ∀ x, Ninst.At node.sevm.code node.pc (.exec x) →
        x = .call ∨ x = .staticcall ∨
        (x = .delegatecall ∧ ∀ (g a : B256) (rest : List B256), node.devm.stack = g :: a :: rest →
          ∃ m ∈ F.delegates, a.toAdr = m.addr)

/-- **The family's replay obligation**, per frame shape.  A successful non-static family frame
entered guarded replays either as a **whole** (`Whole sevm`: one replay from its entry to its end
observing all of its committed frames; the shape of a frame whose own steps surround quiet
children, e.g. a signed writer around its library call), or as a **model** frame (`¬ Whole sevm`:
`Exec.CoreAccounting.SpawnReplay`'s shape — its own steps reach its single external node, after
which only silent steps follow). -/
def SpawnReplay (F : CodeFamily ca root) (Guard : Stor → Prop) (Whole : Sevm → Prop)
    (entry : Sevm → Devm → Prop) (C : ReplayCarrier ca) (V : ReplayObservation C) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true),
    F.Runs sevm pre → CoveredFork sevm.benvStat.fork → Exec.FrameAdmitted ca entry run →
    sum pre.state.bal < 2 ^ 256 → sevm.isStatic = false → Guard (pre.state.getStor ca) →
    (Whole sevm → ∃ steps : List C.Step,
      C.Replay (C.ofState pre.state) steps (C.ofState post.state) ∧
      V.obs steps = (Exec.committedFrames run).flatMap V.frameObs) ∧
    (¬ Whole sevm → ∃ own : List C.Step,
      V.obs own = V.frameObs (Exec.Frame.ofRun run committed) ∧
      ((∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
          ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)) →
        C.Replay (C.ofState pre.state) own (C.ofState post.state)) ∧
      (∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
        ∀ x, Ninst.At N.sevm.code N.pc (.exec x) →
          C.Replay (C.ofState pre.state) own (C.ofState N.devm.state) ∧
          ∀ N', Exec.Deriv.ParentStep N' N →
            C.Replay (C.ofState N'.devm.state) [] (C.ofState post.state) ∧
            ∀ M, Exec.Deriv.ParentPrefix N' M → ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y)))

/-- The positional exemption: a non-static whole frame at the owner (its boundary mid-frame is no
replay prefix). -/
def Opaque (ca : Adr) (Whole : Sevm → Prop) (A : Exec.Frame) : Prop :=
  A.sevm.currentTarget = ca ∧ A.sevm.isStatic = false ∧ Whole A.sevm

/-- **The unguarded law**: from a boundary whose storage fails the guard, any observation list is
the observation of some replay to any boundary (the carrier claims nothing there). -/
def Unguarded (C : ReplayCarrier ca) (V : ReplayObservation C) (Guard : Stor → Prop) : Prop :=
  ∀ (w : State) (b : C.Snap) (os : List V.O), ¬ Guard (w.getStor ca) →
    ∃ steps, C.Replay (C.ofState w) steps b ∧ V.obs steps = os

/-- The accounting a pc-`0` frame owes: `Exec.CoreAccounting`'s conclusion, without the root
code's location (a delegate frame is not located by it). -/
def MemberAccounting (entry : Sevm → Devm → Prop) (C : ReplayCarrier ca) (V : ReplayObservation C)
    (sevm : Sevm) (pre : Devm) (out : Execution) : Prop :=
  ∀ (run : Exec 0 sevm pre out) (committed : Execution.commits out = true),
    CoveredFork sevm.benvStat.fork → Exec.FrameAdmitted ca entry run →
    (sevm.isStatic = true → (Exec.committedFrames run).flatMap V.frameObs = []) ∧
    (sum pre.state.bal < 2 ^ 256 → ∃ steps,
      C.Replay (C.frameEntry sevm pre.state) steps
        (C.ofState (Execution.committedPost out committed).state) ∧
      V.obs steps = (Exec.committedFrames run).flatMap V.frameObs)

section Handler

variable {F : CodeFamily ca root} {Guard : Stor → Prop} {Whole : Sevm → Prop}
  {entry : Sevm → Devm → Prop} {C : ReplayCarrier ca} {V : ReplayObservation C}

/-- **The family child classification.**  The settled children of a guarded family frame's
spawning nodes replay: a `CALL`/`STATICCALL` child is located by the root's `CodeSem.At` (a
same-target child runs the installed root code), and a `DELEGATECALL` child naming a delegate is a
frame of that delegate; the lower-depth hypotheses give each child's accounting. -/
theorem childReplays
    (installed : ∀ (sevm : Sevm) (devm : Devm), sevm.currentTarget = ca → entry sevm devm →
      F.DelegatesInstalled devm.state)
    (kinds : F.SpawnKinds Guard)
    {sevm₀ : Sevm} {pre₀ post₀ : Devm} (run : Exec 0 sevm₀ pre₀ (.ok post₀))
    (runs : F.Runs sevm₀ pre₀) (fork : CoveredFork sevm₀.benvStat.fork)
    (guard : Guard (pre₀.state.getStor ca)) (admitted : Exec.FrameAdmitted ca entry run)
    (deeper : ForallDeeperAtSem sevm₀.depth ca root
      (fun pc s d e _ => Exec.CoreAccounting ca root entry C V pc s d e))
    (deeperMember : F.ForallDeeperMember sevm₀.depth (MemberAccounting entry C V)) :
    Exec.CoreAccounting.ChildReplays C V run := by
  intro nodePc nodeSevm nodePre out frame rsm nextPc cevm raw inter step enter child resume next
    chain committed bound
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
    have childMember : F.MemberAt m cevm.sta cevm.dyna := by
      have childCode : some cevm.sta.code.toList = m.sem.image := by
        rw [Frame.enter_run_code enter, code]
        exact nodeM
      have childAddr : cevm.sta.codeAddress = some m.addr := by
        rw [Frame.enter_run_codeAddress enter, caddr, addr]
      refine ⟨hm, ⟨childTarget, ?_, installed _ _ childTarget (childAdmitted.root childTarget),
        Or.inr ⟨m, hm, childAddr, childCode⟩⟩, childAddr, childCode⟩
      rw [getCode ca]
      exact nodeInstalled
    obtain ⟨cpc, csta, cdyna⟩ := cevm
    dsimp only at pcZero
    subst pcZero
    exact (deeperMember m csta cdyna raw child childDepth childMember child committed childFork
      childAdmitted).2 bound
  all_goals
    have childAt : root.At ca cevm.pc cevm.sta cevm.dyna := by
      refine ⟨?_, fun selected => ⟨?_, pcZero⟩⟩
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
    exact (deeper cevm.pc cevm.sta cevm.dyna raw child childDepth childAt child committed
      childFork childAt childAdmitted).2 bound

/-- **The family frame handler.**  A pc-`0` family frame owes its accounting, from the lower-depth
hypotheses of the root ladder and of the delegates: a static frame observes nothing below it and
keeps the owner's storage; a frame entered unguarded replays by the unguarded law; a guarded frame
replays as a whole, or as a model frame over its children's replays. -/
theorem frameAccounting
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
    (deeper : ForallDeeperAtSem sevm.depth ca root
      (fun pc s d e _ => Exec.CoreAccounting ca root entry C V pc s d e))
    (deeperMember : F.ForallDeeperMember sevm.depth (MemberAccounting entry C V)) :
    (sevm.isStatic = true → (Exec.committedFrames run).flatMap V.frameObs = []) ∧
    (sum pre.state.bal < 2 ^ 256 → ∃ steps,
      C.Replay (C.frameEntry sevm pre.state) steps
        (C.ofState (Execution.committedPost (.ok post) committed).state) ∧
      V.obs steps = (Exec.committedFrames run).flatMap V.frameObs) := by
  have codeNe : (pre.getCode ca).toList ≠ [] := fun empty =>
    root.ne_nil (runs.2.1.symm.trans (congrArg some empty)) rfl
  by_cases hs : sevm.isStatic = true
  · exact Exec.CoreAccounting.staticFrame entryOfState ofStateGet obsStatic run committed fork
      codeNe hs (List.flatMap_eq_nil_iff.mpr fun f hf =>
        obsStatic f (Exec.descendantFrames_isStatic run hs f hf))
  · have hs' : sevm.isStatic = false := by simpa only [Bool.not_eq_true] using hs
    refine ⟨fun h => absurd h hs, fun bound => ?_⟩
    rw [entryOfState]
    by_cases guard : Guard (pre.state.getStor ca)
    · obtain ⟨whole, model⟩ := spawn run committed runs fork admitted bound hs' guard
      by_cases hw : Whole sevm
      · exact whole hw
      · obtain ⟨own, hown, c3, c12⟩ := model hw
        obtain ⟨steps, replay, observed⟩ := Exec.CoreAccounting.modelFrame entryOfState
          ofStateGet append run fork codeNe bound
          (childReplays installed kinds run runs fork guard admitted deeper deeperMember)
          own c3 c12
        refine ⟨steps, replay, ?_⟩
        rw [observed, hown, Exec.committedFrames, dite_eq_left committed, List.flatMap_cons]
    · exact unguarded pre.state _ _ guard

end Handler

/-- **The family accounting ladder.**  The root ladder (`Exec.coreAccounting` over `c.sem`) with the
family target handler: member descent for delegate frames, the per-frame shape for guarded frames,
the unguarded law otherwise. -/
noncomputable def ladder {c : ContractSpecSem} {entry : Sevm → Devm → Prop}
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
    (preserves : c.PreservesAdmitted ca entry) : AccountingLadderAdmitted c ca entry where
  carrier := C
  append := append
  tag := tag
  preserves := preserves
  view := V
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed admitted ready _ fork
      bound
    obtain ⟨installedAt, entryBound⟩ :=
      Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    have core := Exec.coreAccounting ca c.sem entry C V append frameTag
      (fun sevm state _ => entryOfState sevm state) obsForeign
      (fun {sevm pre post} _ target deeper => by
        intro run committed fork installedAt admitted
        exact frameAccounting append entryOfState ofStateGet obsStatic unguarded installed kinds spawn
          run committed fork admitted
          ⟨target, installedAt.1, installed sevm pre target (admitted.root target),
            Or.inl (installedAt.2 target).1⟩
          deeper
          (F.descend (fun m {sevm pre out} _ hm deeperRoot deeperMember => by
            intro run committed fork admitted
            cases out with
            | error error => simp only [Execution.commits, Bool.false_eq_true] at committed
            | ok post =>
                exact frameAccounting append entryOfState ofStateGet obsStatic unguarded installed kinds spawn
                  run committed fork admitted hm.2.1 deeperRoot deeperMember)
            deeper))
    exact (core pc sevm pre out run installedAt run committed fork installedAt admitted).2
      entryBound

end CodeFamily

/-- The descendants of a run whose own chain keeps `ca`'s storage at `s`, every descendant of which
is static or a frame at `ca` keeping its entry storage along its own chain, all enter with `s`. -/
theorem Exec.descendantFrames_getStor_of_quiet {ca : Adr} :
    ∀ {pc : Nat} {sevm : Sevm} {d : Devm} {out : Execution} (run : Exec pc sevm d out)
      (s : Stor), CoveredFork sevm.benvStat.fork → (d.getCode ca).toList ≠ [] →
      (∀ N, Exec.Deriv.ParentPrefix ⟨pc, sevm, d, out, run⟩ N → N.devm.state.getStor ca = s) →
      (∀ f ∈ Exec.descendantFrames run, f.sevm.isStatic = true ∨
        (f.sevm.currentTarget = ca ∧ ∀ N, Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv f) N →
          N.devm.state.getStor ca = f.pre.state.getStor ca)) →
      ∀ f ∈ Exec.descendantFrames run, f.pre.state.getStor ca = s := by
  intro pc sevm d out run
  induction run with
  | halt _ => intro _ _ _ _ _ f hf; simp only [Exec.descendantFrames, List.not_mem_nil] at hf
  | cont step next ih =>
      rename_i nextPre _
      intro s fork codeNe keep quiet f hf
      have nextNe : (Devm.getCode nextPre ca).toList ≠ [] := by
        rw [Blanc.Exec.Deriv.ParentStep.codePreserve (.cont step next) ca codeNe]
        exact codeNe
      simp only [Exec.descendantFrames] at hf quiet
      exact ih s fork nextNe (fun N hN => keep N (.step (.cont step next) hN)) quiet f hf
  | doneErr _ _ _ => intro _ _ _ _ _ f hf; simp only [Exec.descendantFrames, List.not_mem_nil] at hf
  | doneOk step enter resume next ih =>
      rename_i nextPre _
      intro s fork codeNe keep quiet f hf
      have nextNe : (Devm.getCode nextPre ca).toList ≠ [] := by
        rw [Blanc.Exec.Deriv.ParentStep.codePreserve (.doneOk step enter resume next) ca codeNe]
        exact codeNe
      simp only [Exec.descendantFrames] at hf quiet
      exact ih s fork nextNe (fun N hN => keep N (.step (.doneOk step enter resume next) hN))
        quiet f hf
  | runErr _ _ _ _ => intro _ _ _ _ _ f hf; simp only [Exec.descendantFrames, List.not_mem_nil] at hf
  | runOk step enter child resume next childIh nextIh =>
      rename_i frame _ _ cevm raw nextPre _
      intro s fork codeNe keep quiet f hf
      have nextNe : (Devm.getCode nextPre ca).toList ≠ [] := by
        rw [Blanc.Exec.Deriv.ParentStep.codePreserve (.runOk step enter child resume next) ca
          codeNe]
        exact codeNe
      have nextKeep := fun N hN => keep N (.step (.runOk step enter child resume next) hN)
      by_cases settles : Frame.settlementCommits frame raw = true
      · rw [Exec.descendantFrames_runOk_of_settlementCommits step enter child resume next
          settles] at hf quiet
        have childEntry : cevm.dyna.state.getStor ca = s :=
          (Evm.step_spawn_enter_getStor fork step enter ca
            (State.Protected.of_code_ne_nil codeNe)).trans (keep _ (.refl _))
        have childFork := Evm.step_spawn_child_fork step enter fork
        have childNe : (cevm.dyna.getCode ca).toList ≠ [] := by
          rw [(Evm.step_spawn_child step enter).2.1 ca]
          exact codeNe
        rcases List.mem_cons.mp hf with rfl | hf
        · exact childEntry
        rcases List.mem_append.mp hf with hc | hn
        · rcases quiet _ (List.mem_cons_self ..) with static | ⟨_, ckeep⟩
          · rw [Blanc.Exec.descendantFrames_getStor_of_static child static
              (Frame.raw_commits_of_settlementCommits settles) childFork childNe f hc]
            exact childEntry
          · exact childIh s childFork childNe (fun N hN => (ckeep N hN).trans childEntry)
              (fun g hg => quiet g (List.mem_cons_of_mem _ (List.mem_append_left _ hg))) f hc
        · exact nextIh s fork nextNe nextKeep
            (fun g hg => quiet g (List.mem_cons_of_mem _ (List.mem_append_right _ hg))) f hn
      · rw [Exec.descendantFrames_runOk_of_not_settlementCommits step enter child resume next
          settles] at hf quiet
        exact nextIh s fork nextNe nextKeep quiet f hf

/-- **Inner positions of a quiet frame see a spawning node's storage.**  If every committed
descendant of a successful frame is static, or is a frame at `ca` whose own chain keeps `ca`'s
storage, then every committed descendant enters with `ca`'s storage at one of the frame's own nodes
that decodes an external instruction.  (U6h's `goodAt` at shadowed positions.) -/
theorem Exec.descendant_getStor_spawnNode {ca : Adr} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (fork : CoveredFork sevm.benvStat.fork)
    (codeNe : (pre.getCode ca).toList ≠ [])
    (quiet : ∀ f ∈ Exec.descendantFrames run, f.sevm.isStatic = true ∨
      (f.sevm.currentTarget = ca ∧ ∀ N, Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv f) N →
        N.devm.state.getStor ca = f.pre.state.getStor ca)) :
    ∀ f ∈ Exec.descendantFrames run, ∃ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N ∧
      (∃ x, Ninst.At N.sevm.code N.pc (.exec x)) ∧
      f.pre.state.getStor ca = N.devm.state.getStor ca := by
  suffices key : ∀ {pc : Nat} {sevm' : Sevm} {d : Devm} {out : Execution} (r : Exec pc sevm' d out),
      Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ ⟨pc, sevm', d, out, r⟩ →
      (∀ f ∈ Exec.descendantFrames r, f.sevm.isStatic = true ∨
        (f.sevm.currentTarget = ca ∧ ∀ N, Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv f) N →
          N.devm.state.getStor ca = f.pre.state.getStor ca)) →
      ∀ f ∈ Exec.descendantFrames r, ∃ N,
        Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N ∧
        (∃ x, Ninst.At N.sevm.code N.pc (.exec x)) ∧
        f.pre.state.getStor ca = N.devm.state.getStor ca from key run (.refl _) quiet
  intro pc sevm' d out r
  induction r with
  | halt _ => intro _ _ f hf; simp only [Exec.descendantFrames, List.not_mem_nil] at hf
  | cont step next ih =>
      intro chain quiet' f hf
      simp only [Exec.descendantFrames] at hf quiet'
      exact ih (chain.snoc (.cont step next)) quiet' f hf
  | doneErr _ _ _ => intro _ _ f hf; simp only [Exec.descendantFrames, List.not_mem_nil] at hf
  | doneOk step enter resume next ih =>
      intro chain quiet' f hf
      simp only [Exec.descendantFrames] at hf quiet'
      exact ih (chain.snoc (.doneOk step enter resume next)) quiet' f hf
  | runErr _ _ _ _ => intro _ _ f hf; simp only [Exec.descendantFrames, List.not_mem_nil] at hf
  | runOk step enter child resume next childIh nextIh =>
      rename_i nodePc nodeSevm nodePre frame _ _ cevm raw _ _
      intro chain quiet' f hf
      obtain ⟨x, instruction, -, -⟩ := Evm.step_spawn_inv step
      have nodeFork : CoveredFork nodeSevm.benvStat.fork := by
        rw [show nodeSevm = sevm from Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain]
        exact fork
      have nodeNe : (nodePre.getCode ca).toList ≠ [] := by
        rw [(Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain).2 ca codeNe]
        exact codeNe
      have spawned := fun (g : Exec.Frame) (eq : g.pre.state.getStor ca =
          nodePre.state.getStor ca) =>
        (⟨_, chain, ⟨x, instruction⟩, eq⟩ : ∃ N,
          Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N ∧
          (∃ x, Ninst.At N.sevm.code N.pc (.exec x)) ∧
          g.pre.state.getStor ca = N.devm.state.getStor ca)
      by_cases settles : Frame.settlementCommits frame raw = true
      · rw [Exec.descendantFrames_runOk_of_settlementCommits step enter child resume next
          settles] at hf quiet'
        have childEntry : cevm.dyna.state.getStor ca = nodePre.state.getStor ca :=
          Evm.step_spawn_enter_getStor nodeFork step enter ca
            (State.Protected.of_code_ne_nil nodeNe)
        have childFork := Evm.step_spawn_child_fork step enter nodeFork
        have childNe : (cevm.dyna.getCode ca).toList ≠ [] := by
          rw [(Evm.step_spawn_child step enter).2.1 ca]
          exact nodeNe
        rcases List.mem_cons.mp hf with rfl | hf
        · exact spawned _ childEntry
        rcases List.mem_append.mp hf with hc | hn
        · refine spawned f ?_
          rcases quiet' _ (List.mem_cons_self ..) with static | ⟨_, ckeep⟩
          · rw [Blanc.Exec.descendantFrames_getStor_of_static child static
              (Frame.raw_commits_of_settlementCommits settles) childFork childNe f hc]
            exact childEntry
          · exact Exec.descendantFrames_getStor_of_quiet child _ childFork childNe
              (fun N hN => (ckeep N hN).trans childEntry)
              (fun g hg => quiet' g (List.mem_cons_of_mem _ (List.mem_append_left _ hg))) f hc
        · exact nextIh (chain.snoc (.runOk step enter child resume next))
            (fun g hg => quiet' g (List.mem_cons_of_mem _ (List.mem_append_right _ hg))) f hn
      · rw [Exec.descendantFrames_runOk_of_not_settlementCommits step enter child resume next
          settles] at hf quiet'
        exact nextIh (chain.snoc (.runOk step enter child resume next)) quiet' f hf

end Blanc
