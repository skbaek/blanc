import Blanc.Composition.Curve3CrvPositional
import Blanc.ExecutionAccountingPositional
import Blanc.ExecutionEntryAccounting
import Blanc.ExecutionSettledOwnCode
import Blanc.ExecutionTraceSettledForest
import Blanc.Lift.StaticOnlyFrames

/-!
# 3Crv's replay at the frames of a history: entry, post and in-frame positions (U8c support)

`c3crv_history_at` (`Curve3CrvPositional.lean`) gives 3Crv's storage at the entry of a settled
frame as the model fold of the committed invocations before it.  The supply walk of the pool
(`Curve3PoolSupply.lean`) also needs 3Crv's storage at a frame's **post** state and at the entries of
the frames **inside** a pool frame.  Both come from the generic accounting descent applied at the
frame itself, once its side conditions are known:

* `Curve3PoolSupply.FrameReady` — a settled frame starts at pc `0` on a covered fork with 3Crv's code
  installed, is admitted by 3Crv's entry condition below it, and its world balance total is a word;
  `settled_ready` proves it of every settled frame (`settled_ownCode` for the code, and a frame-
  observing ladder over 3Crv's spec for the admission and the balance bound, whose root law descends
  through `descendantFrames_balSum_le`);
* `frame_core` / `frame_positional` — the core accounting (`Exec.coreAccounting` with the
  whole-frame target handler) and the positional descent (`Exec.positionalAccounting`) of 3Crv's
  word-view carrier, applied at a ready frame;
* `c3crv_descendants_static` — every descendant of a settled non-static 3Crv frame is static (3Crv
  spawns only by `STATICCALL`), so no settled non-static frame is enclosed by one;
* `descendantFrames_eq_children` and the depth facts — a frame's descendants are its children's
  committed frames in order, and each lies strictly deeper (`depth` counts down).
-/

namespace Blanc.Composition.Curve3PoolSupply

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Crv Blanc.ExecutionTrace
  Blanc.ExecutionAccountingReplay Blanc.Composition.Curve3CrvToken

/-! ## Spawn depth -/

theorem genericCall_spawn_depth_succ
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {f : Jaune.Frame} {rsm : Resume}
    (hs : genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles = .spawn f rsm) :
    f.inner.depth + 1 = sevm.depth := by
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals simp only [Jaune.Frame.ofCall, callMsg]
  all_goals omega

theorem genericCreate_spawn_depth_succ
    {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {memoryIndex memorySize : Nat} {f : Jaune.Frame} {rsm : Resume}
    (hs : genericCreate.step sevm devm endowment newAddress memoryIndex
      memorySize = .spawn f rsm) :
    f.inner.depth + 1 = sevm.depth := by
  simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
    assertDynamic, Pure.pure, Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals
    simp only [Jaune.Frame.ofCreate, processCreateMessage.msg, Msg.withBenv,
      createMsg, not_or] at *
  all_goals omega

theorem genericCallAmsterdam_spawn_depth_succ
    {sevm : Sevm} {state : StateGasRules} {devm : Devm}
    {gas reservoir : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray}
    {disablePrecompiles newAccountCharged insufficientBalance : Bool}
    {f : Jaune.Frame} {rsm : Resume}
    (hs : genericCallAmsterdam.step sevm state devm gas reservoir value
      caller target codeAddress shouldTransferValue isStaticcall inputIndex
      inputSize outputIndex outputSize code disablePrecompiles
      newAccountCharged insufficientBalance = .spawn f rsm) :
    f.inner.depth + 1 = sevm.depth := by
  simp only [genericCallAmsterdam.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals simp only [Jaune.Frame.ofCall, callMsg]
  all_goals omega

theorem genericCreateAmsterdam_spawn_depth_succ
    {sevm : Sevm} {state : StateGasRules} {devm : Devm} {endowment : B256}
    {newAddress : Adr} {memoryIndex memorySize : Nat} {f : Jaune.Frame} {rsm : Resume}
    (hs : genericCreateAmsterdam.step sevm state devm endowment newAddress
      memoryIndex memorySize = .spawn f rsm) :
    f.inner.depth + 1 = sevm.depth := by
  simp only [genericCreateAmsterdam.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals
    simp only [Jaune.Frame.ofCreate, processCreateMessage.msg, Msg.withBenv,
      createMsg, not_or] at *
  all_goals omega

/-- A spawned child frame sits exactly one level below its parent (`depth` counts down). -/
theorem Xinst_spawn_depth_succ {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Jaune.Frame} {rsm : Resume}
    (hs : Xinst.step sevm devm x = .spawn f rsm) :
    f.inner.depth + 1 = sevm.depth := by
  cases x <;>
    simp only [Xinst.step, Bind.bind, Except.bind, Except.assert,
      Pure.pure, Except.pure] at hs <;>
    repeat' split at hs
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
  all_goals
    first
      | exact genericCreate_spawn_depth_succ hs
      | exact genericCall_spawn_depth_succ hs
      | exact genericCreateAmsterdam_spawn_depth_succ hs
      | exact genericCallAmsterdam_spawn_depth_succ hs

/-! ## Frame structure -/

/-- A run's descendants are its committed children's committed frames, in order. -/
theorem descendantFrames_eq_children :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      Exec.descendantFrames run =
        (Exec.childFrames run).flatMap fun c => Exec.committedFrames c.run := by
  intro pc sevm pre out run
  induction run with
  | halt _ => simp only [Exec.descendantFrames, Exec.childFrames, List.flatMap_nil]
  | cont _ _ ih => simpa only [Exec.descendantFrames, Exec.childFrames] using ih
  | doneErr _ _ _ => simp only [Exec.descendantFrames, Exec.childFrames, List.flatMap_nil]
  | doneOk _ _ _ _ ih => simpa only [Exec.descendantFrames, Exec.childFrames] using ih
  | runErr _ _ _ _ => simp only [Exec.descendantFrames, Exec.childFrames, List.flatMap_nil]
  | runOk step enter child resume next _ nextIh =>
      simp only [Exec.descendantFrames, Exec.childFrames, List.flatMap_append, nextIh]
      congr 1
      split
      · rename_i settles
        rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, Exec.Frame.committedFrames_self]
        rfl
      · rfl

/-- Every descendant of a run lies strictly deeper (`depth` counts down). -/
theorem descendantFrames_depth_lt :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      ∀ D ∈ Exec.descendantFrames run, D.sevm.depth < sevm.depth := by
  intro pc sevm pre out run
  induction run with
  | halt _ => intro D member; simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | cont _ _ ih => simpa only [Exec.descendantFrames] using ih
  | doneErr _ _ _ =>
      intro D member; simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | doneOk _ _ _ _ ih => simpa only [Exec.descendantFrames] using ih
  | runErr _ _ _ _ =>
      intro D member; simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | runOk step enter _ _ _ childIh nextIh =>
      intro D member
      have childDepth := Frame.enter_run_depth enter ▸ Step.spawn_depth_lt step
      simp only [Exec.descendantFrames, List.mem_append] at member
      rcases member with here | later
      · split at here
        · rw [List.mem_cons] at here
          rcases here with rfl | deeper
          · exact childDepth
          · exact Nat.lt_trans (childIh D deeper) childDepth
        · simp only [List.not_mem_nil] at here
      · exact nextIh D later

/-- Every committed child of a run lies exactly one level deeper. -/
theorem childFrames_depth :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      ∀ c ∈ Exec.childFrames run, c.sevm.depth + 1 = sevm.depth := by
  intro pc sevm pre out run
  induction run with
  | halt _ => intro c member; simp only [Exec.childFrames, List.not_mem_nil] at member
  | cont _ _ ih => simpa only [Exec.childFrames] using ih
  | doneErr _ _ _ => intro c member; simp only [Exec.childFrames, List.not_mem_nil] at member
  | doneOk _ _ _ _ ih => simpa only [Exec.childFrames] using ih
  | runErr _ _ _ _ => intro c member; simp only [Exec.childFrames, List.not_mem_nil] at member
  | runOk step enter _ _ _ _ nextIh =>
      intro c member
      simp only [Exec.childFrames, List.mem_append] at member
      rcases member with here | later
      · split at here
        · rw [List.mem_singleton] at here
          subst here
          obtain ⟨x, -, spawn, -⟩ := Evm.step_spawn_inv step
          exact Frame.enter_run_depth enter ▸ Xinst_spawn_depth_succ spawn
        · simp only [List.not_mem_nil] at here
      · exact nextIh c later

/-! ## The world balance total below a frame -/

/-- **The balance total does not grow below a run**: every committed descendant starts with a
balance total at most the run's, while some account keeps nonempty code. -/
theorem descendantFrames_balSum_le {a : Adr} :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      CoveredFork sevm.benvStat.fork → (pre.getCode a).toList ≠ [] →
      ∀ D ∈ Exec.descendantFrames run, sum D.pre.state.bal ≤ sum pre.state.bal := by
  intro pc sevm pre out run
  induction run with
  | halt _ => intro _ _ D member; simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | cont hstep next ih =>
      intro fork code D member
      have edge := Jaune.Exec.Deriv.ParentStep.cont hstep next
      have keep := Blanc.Exec.Deriv.ParentStep.codePreserve edge a code
      have hb := Blanc.Exec.Deriv.ParentStep.balSum_le edge
      dsimp only at keep hb
      exact Nat.le_trans (ih fork (by rw [keep]; exact code) D
        (by simpa only [Exec.descendantFrames] using member)) hb
  | doneErr _ _ _ =>
      intro _ _ D member; simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | doneOk hstep henter hresume next ih =>
      intro fork code D member
      have edge := Jaune.Exec.Deriv.ParentStep.doneOk hstep henter hresume next
      have keep := Blanc.Exec.Deriv.ParentStep.codePreserve edge a code
      have hb := Blanc.Exec.Deriv.ParentStep.balSum_le edge
      dsimp only at keep hb
      exact Nat.le_trans (ih fork (by rw [keep]; exact code) D
        (by simpa only [Exec.descendantFrames] using member)) hb
  | runErr _ _ _ _ =>
      intro _ _ D member; simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | runOk hstep henter child hresume next childIh nextIh =>
      intro fork code D member
      have world := (Evm.step_spawn_child_world fork hstep henter (a := a) fun empty => code (by
        rw [empty]; simp only [ByteArray.toList_empty])).2
      have childFork := Evm.step_spawn_child_fork hstep henter fork
      have childCode := (Evm.step_spawn_child hstep henter).2.1 a
      have edge := Jaune.Exec.Deriv.ParentStep.runOk hstep henter child hresume next
      have keep := Blanc.Exec.Deriv.ParentStep.codePreserve edge a code
      have hb := Blanc.Exec.Deriv.ParentStep.balSum_le edge
      dsimp only at keep hb
      simp only [Exec.descendantFrames, List.mem_append] at member
      rcases member with here | later
      · split at here
        · rw [List.mem_cons] at here
          rcases here with rfl | deeper
          · exact world
          · exact Nat.le_trans (childIh childFork (by rw [childCode]; exact code) D deeper) world
        · simp only [List.not_mem_nil] at here
      · exact Nat.le_trans (nextIh fork (by rw [keep]; exact code) D later) hb

/-! ## Readiness of every settled frame -/

/-- A frame's side conditions for 3Crv's accounting descent at the frame. -/
def FrameReady (ca : Adr) (U : Key → Prop) (f : Exec.Frame) : Prop :=
  f.pc = 0 ∧ CoveredFork f.sevm.benvStat.fork ∧ c3crvSem.At ca 0 f.sevm f.pre ∧
    Exec.FrameAdmitted ca (carriedFrameEntry U) f.run ∧ sum f.pre.state.bal < 2 ^ 256

/-- The admission and balance part of readiness. -/
def FrameBound (ca : Adr) (U : Key → Prop) (f : Exec.Frame) : Prop :=
  Exec.FrameAdmitted ca (carriedFrameEntry U) f.run ∧ sum f.pre.state.bal < 2 ^ 256

/-- The ladder observing every settled frame with `FrameBound`. -/
def boundLadder (ca : Adr) (U : Key → Prop)
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) :
    AccountingLadderAdmitted (curveSpec U) ca (carriedFrameEntry U) where
  carrier :=
    { Snap := Unit
      Step := Exec.Frame
      Tag := Unit
      Replay := fun _ steps _ => ∀ f ∈ steps, FrameBound ca U f
      ofState := fun _ => ()
      frameEntry := fun _ _ => ()
      nil := fun _ f member => (List.not_mem_nil member).elim
      readsStorage := false
      silent := fun _ _ => rfl
      credit := by
        intros
        exact ⟨[], fun f member => (List.not_mem_nil member).elim⟩
      entry_eq_ofState := fun _ _ _ _ => rfl }
  append := fun left right f member => (List.mem_append.mp member).elim (left f) (right f)
  tag := fun _ _ => ()
  preserves := curveSpec_preservesAdmitted ca U injective apart
  view :=
    { O := Exec.Frame
      obs := id
      obs_nil := rfl
      obs_append := fun _ _ => rfl
      frameObs := fun f => [f]
      credit := by
        intros
        exact ⟨[], fun f member => (List.not_mem_nil member).elim, rfl⟩ }
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed admitted ready _ fork bound
    obtain ⟨installed, entryBound⟩ := Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    have code : (pre.getCode ca).toList ≠ [] := fun empty =>
      (curveSpec U).sem.ne_nil (installed.1.symm.trans (congrArg some empty)) rfl
    refine ⟨Exec.committedFrames run, ?_, by
      change Exec.committedFrames run = (Exec.committedFrames run).flatMap fun f => [f]
      rw [List.flatMap_singleton']⟩
    intro f member
    refine ⟨admitted.mono fun r hr =>
      Exec.rawFrameRoots_trans (Exec.mem_rawFrameRoots_of_mem_committedFrames run f member) hr, ?_⟩
    rw [Exec.committedFrames, dite_eq_left committed] at member
    rcases List.mem_cons.mp member with rfl | deeper
    · exact entryBound
    · exact Nat.lt_of_le_of_lt (descendantFrames_balSum_le run fork code f deeper) entryBound

/-- 3Crv's runtime spawns only by `STATICCALL`, in the shape `settled_ownCode` takes. -/
theorem c3crv_ownSpawns (ca : Adr) : OwnSpawns ca code := by
  intro R N x pcZero hcode _ fork chain instruction
  exact .inr (.inl (parentPrefix_exec_staticcall_of_cert cert_check c3crv_cert_staticOnly pcZero
    hcode fork chain instruction))

theorem c3crv_code_of_image {c : ByteArray} (h : some c.toList = c3crvSem.image) : c = code := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa only [ByteArray.toList_eq_toList_data] using Option.some.inj h

/-- **Every settled frame is ready** for 3Crv's accounting descent at it. -/
theorem settled_ready {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {initial : Blanc.Curve3Crv.State} {initialKeys : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = c3crvSem.image)
    (invariant : VyInv (checkpoint.state.getStor ca) initial initialKeys)
    (fresh : FreshKeys initialKeys (historyTouchedKeys ca trace)) :
    ∀ f ∈ trace.settledFrames, FrameReady ca (historyKeyUniverse ca trace initialKeys) f := by
  let U := historyKeyUniverse ca trace initialKeys
  have topology : VyInv (checkpoint.state.getStor ca) initial U := invariant.extend fresh
  have touched : trace.FrameAdmitted ca
      (fun sevm _ => ∀ k ∈ callKeys sevm.caller (decodeCall sevm), U k) := by
    apply (trace.frameAdmitted_iff_rawFrames ca _).2
    intro root member target k hk
    exact Or.inr (touchedKeys_mem member target hk)
  have admitted : trace.FrameAdmitted ca (carriedFrameEntry U) :=
    (trace.freshFrameAdmitted ca).and (trace.frameAdmitted_calldata.and touched)
  have start : (curveSpec U).StateInv ca checkpoint.state :=
    ⟨installed, trivial, ⟨initial, initialKeys, fun _ hk => Or.inl hk, invariant⟩⟩
  obtain ⟨steps, replay, observed⟩ :=
    (boundLadder ca U topology.inj topology.apart).configuredHistory trace admitted start
  change steps = trace.settledFrames.flatMap (fun f => [f]) at observed
  rw [List.flatMap_singleton'] at observed
  have nonempty : code.toList ≠ [] := fun empty =>
    c3crvSem.ne_nil (show c3crvSem.image = some code.toList from rfl) empty
  have nondelegating : ¬ isValidDelegation code :=
    c3crvSem.not_delegation (show some code.toList = c3crvSem.image from rfl)
  have own := trace.settled_ownCode nonempty nondelegating (c3crv_ownSpawns ca)
    (c3crv_code_of_image installed)
  intro f member
  obtain ⟨hcode, hpc, hfork, hown⟩ := own f member
  obtain ⟨hadm, hbound⟩ := replay f (observed ▸ member)
  refine ⟨hpc, hfork, ⟨by rw [hcode]; rfl, fun target => ⟨by rw [hown target]; rfl, rfl⟩⟩, hadm,
    hbound⟩

/-! ## The descent at a ready frame -/

/-- 3Crv's core accounting at every derivation. -/
theorem c3crv_coreFa (ca : Adr) (U : Key → Prop)
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) :
    Exec.Fa (Exec.WknSem ca c3crvSem (fun pc s d e _ =>
      Exec.CoreAccounting ca c3crvSem (carriedFrameEntry U) (viewCarrier ca U)
        (viewObservation ca U) pc s d e)) :=
  Exec.coreAccounting ca c3crvSem (carriedFrameEntry U) (viewCarrier ca U) (viewObservation ca U)
    viewReplay_append (fun _ _ => ()) (fun _ _ _ => rfl) (fun _ hf => viewFrameObs_foreign hf)
    (fun hrun target deeper =>
      Exec.CoreAccounting.wholeFrameTarget (fun _ _ => rfl) (fun h => Subtype.ext (funext h))
        (fun _ hf => viewFrameObs_static hf) (c3crv_spawnKinds ca)
        (c3crv_wholeFrame ca U injective apart) hrun target deeper)

/-- **3Crv across a ready frame**: from the frame's entry view to its post view, observing exactly
its committed frames. -/
theorem frame_core {ca : Adr} {U : Key → Prop}
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) {f : Exec.Frame} (ready : FrameReady ca U f) :
    ViewReplay U (viewOf (f.pre.state.getStor ca))
      ((Exec.committedFrames f.run).flatMap (viewFrameObs ca)) (viewOf (f.post.state.getStor ca)) := by
  obtain ⟨hpc, fork, at_, admitted, bound⟩ := ready
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := f
  dsimp only at hpc fork at_ admitted bound ⊢
  subst hpc
  obtain ⟨steps, replay, observed⟩ :=
    (c3crv_coreFa ca U injective apart 0 sevm pre out run at_ run committed fork at_ admitted).2
      bound
  change steps = _ at observed
  subst observed
  exact replay

/-- 3Crv's positional descent at every derivation. -/
theorem c3crv_positionalFa (ca : Adr) (U : Key → Prop)
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) :
    Exec.Fa (Exec.WknSem ca c3crvSem (fun pc s d e _ =>
      Exec.PositionalAccounting ca c3crvSem (carriedFrameEntry U) (viewCarrier ca U)
        (viewObservation ca U) (fun A => A.sevm.currentTarget = ca ∧ A.sevm.isStatic = false)
        pc s d e)) :=
  Exec.positionalAccounting (fun _ _ => rfl) (fun h => Subtype.ext (funext h))
    (fun _ hf => viewFrameObs_foreign hf) viewReplay_append (fun _ op => op.1)
    (c3crv_coreFa ca U injective apart)
    (fun _ target _ => Exec.PositionalAccounting.wholeFrameTarget (fun h => Subtype.ext (funext h))
      (c3crv_coreFa ca U injective apart) target)

/-- **3Crv at a position inside a ready frame**: from the frame's entry view to the entry view of
any of its committed frames that no earlier non-static 3Crv frame of it encloses, observing exactly
the committed frames before it. -/
theorem frame_positional {ca : Adr} {U : Key → Prop}
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) {f : Exec.Frame} (ready : FrameReady ca U f)
    {before : List Exec.Frame} {g : Exec.Frame} {after : List Exec.Frame}
    (split : Exec.committedFrames f.run = before ++ g :: after)
    (noOpaque : ∀ A ∈ before, A.Encloses g →
      ¬ (A.sevm.currentTarget = ca ∧ A.sevm.isStatic = false)) :
    ViewReplay U (viewOf (f.pre.state.getStor ca)) (before.flatMap (viewFrameObs ca))
      (viewOf (g.pre.state.getStor ca)) := by
  obtain ⟨hpc, fork, at_, admitted, bound⟩ := ready
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := f
  dsimp only at hpc fork at_ admitted bound split ⊢
  subst hpc
  obtain ⟨steps, replay, observed⟩ :=
    c3crv_positionalFa ca U injective apart 0 sevm pre out run at_ run committed fork at_ admitted
      bound before g after split noOpaque
  change steps = _ at observed
  subst observed
  exact replay

/-! ## Non-static 3Crv frames enclose only static frames -/

/-- **Every descendant of a settled non-static 3Crv frame is static.** -/
theorem c3crv_descendants_static {ca : Adr} {U : Key → Prop} {A : Exec.Frame}
    (ready : FrameReady ca U A) (target : A.sevm.currentTarget = ca) :
    ∀ D ∈ Exec.descendantFrames A.run, D.sevm.isStatic = true := by
  obtain ⟨hpc, fork, at_, -, -⟩ := ready
  have hcode : A.sevm.code = code := c3crv_code_of_image (at_.2 target).1
  have none := Exec.staticOnly_descendantFrames_flatMap_eq_nil ca c3crvSem (fun _ _ => True)
    (fun D : Exec.Frame => if D.sevm.isStatic = true then ([] : List Unit) else [()])
    (Blanc.Exec.Frame.rootDeriv A) target at_.1 fork
    (fun chain instruction =>
      parentPrefix_exec_staticcall_of_cert cert_check c3crv_cert_staticOnly hpc hcode fork chain
        instruction)
    (fun run _ _ _ _ _ static => List.flatMap_eq_nil_iff.mpr fun D member => by
      rw [if_pos (committedFrames_isStatic run static D member)])
    A.run (.refl _) (fun _ _ _ => trivial)
  intro D member
  have empty := List.flatMap_eq_nil_iff.mp none D member
  by_contra hs
  rw [if_neg hs] at empty
  cases empty

/-- **No settled non-static frame lies below a settled non-static 3Crv frame**, so the positional
replay applies at every settled non-static frame. -/
theorem noOpaque_of_nonstatic {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {U : Key → Prop} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (ready : ∀ f ∈ trace.settledFrames, FrameReady ca U f)
    {before : List Exec.Frame} {f : Exec.Frame} {after : List Exec.Frame}
    (split : trace.settledFrames = before ++ f :: after) (nonstatic : f.sevm.isStatic = false) :
    ∀ A ∈ before, A.Encloses f → ¬ (A.sevm.currentTarget = ca ∧ A.sevm.isStatic = false) := by
  intro A member encloses ⟨target, _⟩
  have settled : A ∈ trace.settledFrames := by
    rw [split]
    exact List.mem_append_left _ member
  have := c3crv_descendants_static (ready A settled) target f encloses
  rw [nonstatic] at this
  cases this

end Blanc.Composition.Curve3PoolSupply
