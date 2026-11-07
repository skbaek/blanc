import Blanc.Composition.Curve3CrvPositional
import Blanc.ExecutionAccountingPositional
import Blanc.ExecutionEntryAccounting
import Blanc.ExecutionSettledOwnCode
import Blanc.ExecutionTraceSettledForest

/-!
# 3Crv's replay at the frames of a history: entry, post and in-frame positions (U8c support)

The supply walk of the pool (`Curve3PoolSupply.lean`) needs 3Crv's storage at a frame's **post** state
and at the entries of the frames **inside** a pool frame, besides the one at a settled frame's entry.
Both come from the generic accounting descent applied at the frame itself, once its side conditions
are known:

* `FrameReady` (`Lift/Curve3Crv/HistFrameReady.lean`) — a settled frame starts at pc `0` without state
  gas with 3Crv's code installed, is admitted by 3Crv's entry condition below it, and its world balance
  total is a word; `settled_ready` proves it of every settled frame of a configured history
  (`settled_ownCode` for the code, and a frame-observing ladder over 3Crv's spec for the admission and
  the balance bound), `c3crv_mid_readyH` of a historical mid history;
* `frame_core` / `frame_positional` — the core accounting (`Exec.coreAccountingIn` with the
  whole-frame target handler) and the positional descent (`Exec.positionalAccountingIn`) of 3Crv's
  word-view carrier, applied at a ready frame. Both run on the fork domain "no state gas", so one proof
  serves both histories, with the owner evidence `OwnerAnswerH`;
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

/-! ## Readiness of every settled frame -/

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
    · exact Nat.lt_of_le_of_lt
        (descendantFrames_balSum_leH run (CoveredFork.rules_stateGas_none fork) code f deeper) entryBound

/-- 3Crv's runtime spawns only by `STATICCALL`, in the shape `settled_ownCode` takes. -/
theorem c3crv_ownSpawns (ca : Adr) : OwnSpawns ca code := by
  intro R N x pcZero hcode _ fork chain instruction
  exact .inr (.inl (parentPrefix_exec_staticcall_of_cert cert_check cert_onlyStaticcall pcZero
    hcode fork chain instruction))

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
    (code_of_image installed)
  intro f member
  obtain ⟨hcode, hpc, hfork, hown⟩ := own f member
  obtain ⟨hadm, hbound⟩ := replay f (observed ▸ member)
  refine ⟨hpc, CoveredFork.rules_stateGas_none hfork, ⟨by rw [hcode]; rfl, fun target => ⟨by rw [hown target]; rfl, rfl⟩⟩, hadm,
    hbound⟩

/-! ## The descent at a ready frame -/

/-- 3Crv's view replay with the historical owner evidence: the walk's replay, on every history. -/
abbrev ViewReplayH (U : Key → Prop) (a : View) (invs : List WriterInvocation) (b : View) : Prop :=
  ViewReplayBy OwnerAnswerH U a invs b

/-- The fork domain of the frame-level descent: no state gas. -/
abbrev NoStateGas (f : Fork) : Prop := (Fork.ruleSet f).stateGas = none

/-- 3Crv's core accounting at every derivation. -/
theorem c3crv_coreFa (ca : Adr) (U : Key → Prop)
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) :
    Exec.Fa (Exec.WknSem ca c3crvSem (fun pc s d e _ =>
      Exec.CoreAccountingIn NoStateGas ca c3crvSem (carriedFrameEntry U)
        (viewCarrierBy OwnerAnswerH ca U) (viewObservationBy OwnerAnswerH ca U) pc s d e)) :=
  Exec.coreAccountingIn NoStateGas ca c3crvSem (carriedFrameEntry U)
    (viewCarrierBy OwnerAnswerH ca U) (viewObservationBy OwnerAnswerH ca U)
    viewReplay_append (fun _ _ => ()) (fun _ _ _ => rfl) (fun _ hf => viewFrameObs_foreign hf) id
    (fun hrun target _ =>
      Exec.CoreAccounting.wholeFrameTargetIn id (fun _ _ => rfl) (fun h => Subtype.ext (funext h))
        (fun _ hf => viewFrameObs_static hf)
        (c3crv_wholeFrameBy id (frameRefines_noStateGas id) ca U injective apart) hrun target)

/-- **3Crv across a ready frame**: from the frame's entry view to its post view, observing exactly
its committed frames. -/
theorem frame_core {ca : Adr} {U : Key → Prop}
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) {f : Exec.Frame} (ready : FrameReady ca U f) :
    ViewReplayH U (viewOf (f.pre.state.getStor ca))
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
      Exec.PositionalAccountingIn NoStateGas ca c3crvSem (carriedFrameEntry U)
        (viewCarrierBy OwnerAnswerH ca U) (viewObservationBy OwnerAnswerH ca U)
        (fun A => A.sevm.currentTarget = ca ∧ A.sevm.isStatic = false) pc s d e)) :=
  Exec.positionalAccountingIn id (fun _ _ => rfl) (fun h => Subtype.ext (funext h))
    (fun _ hf => viewFrameObs_foreign hf) viewReplay_append (fun _ op => op.1)
    (c3crv_coreFa ca U injective apart)
    (fun _ target _ => Exec.PositionalAccounting.wholeFrameTarget id (fun h => Subtype.ext (funext h))
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
    ViewReplayH U (viewOf (f.pre.state.getStor ca)) (before.flatMap (viewFrameObs ca))
      (viewOf (g.pre.state.getStor ca)) := by
  obtain ⟨hpc, fork, at_, admitted, bound⟩ := ready
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := f
  dsimp only at hpc fork at_ admitted bound split ⊢
  subst hpc
  obtain ⟨steps, replay, observed⟩ :=
    c3crv_positionalFa ca U injective apart 0 sevm pre out run at_ run committed fork at_ admitted
      bound before g after split (Exec.NoOpaqueAbove.of_encloses noOpaque)
  change steps = _ at observed
  subst observed
  exact replay

/-! ## Non-static 3Crv frames enclose only static frames -/

/-- **No settled non-static frame lies below a settled non-static 3Crv frame**, so the positional
replay applies at every settled non-static frame. -/
theorem noOpaque_of_nonstatic {ca : Adr} {U : Key → Prop} {frames : List Exec.Frame}
    (ready : ∀ f ∈ frames, FrameReady ca U f)
    {before : List Exec.Frame} {f : Exec.Frame} {after : List Exec.Frame}
    (split : frames = before ++ f :: after) (nonstatic : f.sevm.isStatic = false) :
    ∀ A ∈ before, A.Encloses f → ¬ (A.sevm.currentTarget = ca ∧ A.sevm.isStatic = false) := by
  intro A member encloses ⟨target, _⟩
  have settled : A ∈ frames := by
    rw [split]
    exact List.mem_append_left _ member
  have := c3crv_descendants_staticH (ready A settled) target f encloses
  rw [nonstatic] at this
  cases this

end Blanc.Composition.Curve3PoolSupply
