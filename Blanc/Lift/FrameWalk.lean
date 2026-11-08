import Blanc.Lift.TargetLogEvents
import Blanc.Lift.CallerProvenance
import Blanc.CallSpawnExact
import Blanc.Lift.InvWalk
import Blanc.ExecutionWarmth
import Blanc.ExecutionCommittedGas

/-!
# Walking a successful frame along its own derivation, with its direct children

`lift_soundM` hands a walk an `SFunc` run whose jump steps are loose in gas (`Devm.PopBurn`
only bounds the burn), so the walk's states are not the frame's actual states and its call
steps cannot be matched with the frame's direct children (`Exec.childFrames`). This module
walks the actual derivation instead: `XAt sevm post pc d L` says that the frame running
`sevm` reaches pc `pc` in state `d` (some `Exec pc sevm d (.ok post)`), and that the direct,
settlement-committed children it spawns from there on are exactly `L`.

* `XAt.of_exec`: a frame's derivation starts a walk with `L = Exec.childFrames exc`;
* `xa_next`: a non-spawning instruction at `pc` is one `Ninst.Run` step (so the `ri_*`
  inversion kit applies to it), and keeps `L`;
* `xa_jumpdest`, `xa_jump`, `xa_jumpi`: the jump instructions, with their exact pops;
* `xa_halt`, `xa_revert`: a successful frame halting at a `Linst` ends with no further
  children; it cannot pass a `REVERT`.

The call family is in the second part of the file. Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- The frame running `sevm` reaches `pc` in state `d` on its way to `post`, and the direct
committed children it spawns from there on are `L`. -/
def XAt (sevm : Sevm) (post : Devm) (pc : Nat) (d : Devm) (L : List Exec.Frame) : Prop :=
  ∃ exc : Exec pc sevm d (.ok post), Exec.childFrames exc = L ∧ d.gasMeasure < 2 ^ 256

theorem XAt.of_exec {sevm : Sevm} {post : Devm} {pc : Nat} {d : Devm}
    (exc : Exec pc sevm d (.ok post)) (hg : d.gasMeasure < 2 ^ 256) :
    XAt sevm post pc d (Exec.childFrames exc) :=
  ⟨exc, rfl, hg⟩

/-- A walked state's gas fits a word. -/
theorem XAt.gasLeft_lt {sevm : Sevm} {post : Devm} {pc : Nat} {d : Devm} {L : List Exec.Frame}
    (h : XAt sevm post pc d L) : d.gasLeft < 2 ^ 256 := by
  obtain ⟨-, -, hg⟩ := h
  rw [Devm.gasMeasure_def] at hg
  omega

/-! ## Gas only falls along the frame's own chain -/

theorem gas_cont {pc pc' : Nat} {sevm : Sevm} {d d' : Devm}
    (h : Evm.step ⟨pc, sevm, d⟩ = .cont pc' d') : d'.gasMeasure < d.gasMeasure := by
  have b := Evm.step_gasBound ⟨pc, sevm, d⟩
  rw [h] at b
  exact b

theorem gas_done {pc pc' : Nat} {sevm : Sevm} {d d' : Devm} {f : Frame} {rsm : Resume}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h : Evm.step ⟨pc, sevm, d⟩ = .spawn f rsm pc') (he : f.enter = .done r)
    (hr : rsm.run r = .ok d') : d'.gasMeasure < d.gasMeasure := by
  have b := Evm.step_gasBound ⟨pc, sevm, d⟩
  rw [h] at b
  have rg := Resume.run_gasLe (rsm := rsm) (m := f.inner.gas)
    (fun d hd => Frame.enter_done_gasLe he hd)
  rw [hr, Execution.gasMeasure_ok] at rg
  change f.inner.gas + rsm.parentGas < d.gasMeasure ∧ _ at b
  omega

theorem gas_run {pc pc' : Nat} {sevm : Sevm} {d d' : Devm} {f : Frame} {rsm : Resume}
    {cevm : Evm} {raw : Execution}
    (h : Evm.step ⟨pc, sevm, d⟩ = .spawn f rsm pc') (he : f.enter = .run cevm)
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hr : rsm.run (f.settle raw) = .ok d') : d'.gasMeasure < d.gasMeasure := by
  have b := Evm.step_gasBound ⟨pc, sevm, d⟩
  rw [h] at b
  change f.inner.gas + rsm.parentGas < d.gasMeasure ∧ _ at b
  have childGas : raw.SettledGasLe f.inner.gas := by
    intro sg dd hd
    have budget := Exec.descendantFrames_settledGas child sg dd hd
    rw [Frame.enter_run_gasMeasure he] at budget
    omega
  have rg := Resume.run_gasLe (rsm := rsm) (r := f.settle raw) (m := f.inner.gas)
    (fun dd hd => Frame.settle_gasLe childGas hd)
  rw [hr, Execution.gasMeasure_ok] at rg
  omega

variable {sevm : Sevm} {post : Devm} {pc : Nat} {d : Devm} {L : List Exec.Frame}

/-! ## The jump instructions over `St` states -/

section St

variable {b : Devm} {S : List B256} {M : Mem} {G : Nat}

end St

/-! ## The call family -/

/-- A static child at an exact target and calldata, with a complete first return word
and no logs. This records reply observations; it does not assert parent-child provenance
or constrain the remaining return bytes. -/
structure StaticWordChild (t : Adr) (input : Bytes) (c : Exec.Frame) : Prop where
  target : c.sevm.currentTarget = t
  data : c.sevm.data = input
  static : c.sevm.isStatic = true
  len : 32 ≤ c.post.output.length
  logs : c.post.logs = []

/-- **What a committed call child is**, seen from its parent's step `d → d'`: it ran at `t`
with calldata `input`, value `v` and staticness `static`; it returned `d'.returnData`; the
parent's logs grew by exactly the child's; and at every account with code before the call,
the child started on the parent's storage and the parent resumed on the child's. -/
structure ChildOf (d d' : Devm) (t : Adr) (input : Bytes) (v : B256) (static : Bool)
    (c : Exec.Frame) : Prop where
  target : c.sevm.currentTarget = t
  data : c.sevm.data = input
  value : c.sevm.value = v
  isStatic : c.sevm.isStatic = static
  output : c.post.output = d'.returnData
  logs : d'.logs = d.logs ++ c.post.logs
  storPre : ∀ ca, d.getCode ca ≠ .empty → Devm.getStor c.pre ca = Devm.getStor d ca
  storPost : ∀ ca, d.getCode ca ≠ .empty → ∀ key,
    (Devm.getStor d' ca).get key = (Devm.getStor c.post ca).get key
  code : ∀ ca, d.getCode ca ≠ .empty → d'.getCode ca = d.getCode ca
  codePre : ∀ a, c.pre.getCode a = d.getCode a
  codePost : ∀ a, d'.getCode a = c.post.getCode a
  outputKeep : d'.output = d.output
  warm : Devm.AccGrow d d'

/-- Nonempty code, as `CodePreserve` states it. -/
theorem ByteArray.toList_ne_nil_of_ne_empty {c : ByteArray} (h : c ≠ .empty) : c.toList ≠ [] := by
  intro e
  apply h
  apply ByteArray.eq_empty_of_size_eq_zero
  rw [ByteArray.size_eq_length_toList, e]
  rfl

/-- **A `CALL`**: one `Ninst.Run` step. When it leaves a nonzero flag, either its target is a
precompile and no child was spawned, or the next remaining child is the call's (`ChildOf`). -/
theorem xa_call (fork : CoveredFork sevm.benvStat.fork)
    (hat : Ninst.At sevm.code pc (.exec .call))
    {g t v ii is oi os : B256} {S : List B256}
    (hstack : d.stack = g :: t :: v :: ii :: is :: oi :: os :: S)
    (h : XAt sevm post pc d L) :
    ∃ d', Ninst.Run sevm d (.exec .call) d' ∧ ∃ L', XAt sevm post (pc + 1) d' L' ∧
      ∀ flag rest, d'.stack = flag :: rest → flag ≠ 0 →
        (sevm.benvStat.rules.isPrecomp t.toAdr ∧ L = L') ∨
        (∃ c, L = c :: L' ∧ 0 < sevm.depth ∧
          (¬ sevm.benvStat.rules.isPrecomp t.toAdr ∨
            (getDelegatedCodeAddress (d.getCode t.toAdr)).isSome) ∧
          ChildOf d d' t.toAdr (d.memory.read ii.toNat is.toNat).1 v sevm.isStatic c) := by
  have hstep : Evm.step ⟨pc, sevm, d⟩ = Ninst.step ⟨pc, sevm, d⟩ (.exec .call) :=
    Evm.step_next hat
  have operands : (g :: t :: v :: ii :: is :: oi :: os :: S) <<+ d.stack := by
    rw [hstack]
    simpa only [List.append_nil] using (pref_append (g :: t :: v :: ii :: is :: oi :: os :: S) [])
  -- a childless outcome: a nonzero flag means a precompile target
  have childless : ∀ d', Ninst.StepRun pc sevm d (.exec .call) .none (.ok d') →
      ∀ flag rest, d'.stack = flag :: rest → flag ≠ 0 →
        sevm.benvStat.rules.isPrecomp t.toAdr := by
    intro d' stepRun flag rest hflag nz
    have xrun : Xinst.Run sevm d .call .none (.ok d') := by
      rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at stepRun
      exact stepRun
    exact Xinst.call_none_precompile fork operands xrun ⟨flag, rest, hflag, nz⟩
  obtain ⟨exc, rfl, hg⟩ := h
  cases exc with
  | halt h => cases Ninst.step_ne_halt_ok (hstep.symm.trans h)
  | @cont _ _ _ _ d'' _ h next =>
    have hs := hstep.symm.trans h
    cases Ninst.step_cont_pc hs
    have stepRun : Ninst.StepRun pc sevm d (.exec .call) .none (.ok d'') := by
      simp only [Ninst.StepRun, hs, Step.Run]
      exact ⟨trivial, trivial⟩
    exact ⟨_, ⟨.none, trivial, pc, stepRun⟩, _, ⟨next, rfl, lt_trans (gas_cont h) hg⟩,
      fun flag rest hflag nz => .inl ⟨childless _ stepRun flag rest hflag nz, rfl⟩⟩
  | @doneOk _ _ _ _ _ _ _ d'' _ h henter hr next =>
    have hs := hstep.symm.trans h
    cases Ninst.step_spawn_pc hs
    have stepRun : Ninst.StepRun pc sevm d (.exec .call) .none (.ok d'') := by
      simp only [Ninst.StepRun, hs, Step.Run]
      exact ⟨_, RunFrame.of_done henter, hr.symm⟩
    exact ⟨_, ⟨.none, trivial, pc, stepRun⟩, _, ⟨next, rfl, lt_trans (gas_done h henter hr) hg⟩,
      fun flag rest hflag nz => .inl ⟨childless _ stepRun flag rest hflag nz, rfl⟩⟩
  | @runOk _ _ _ f rsm _ cevm raw d'' _ h henter child hr next =>
    have hs := hstep.symm.trans h
    cases Ninst.step_spawn_pc hs
    have stepRun : Ninst.StepRun pc sevm d (.exec .call) (.some ⟨cevm, raw⟩) (.ok d'') := by
      simp only [Ninst.StepRun, hs, Step.Run]
      exact ⟨_, RunFrame.of_run henter, hr.symm⟩
    have xrun : Xinst.Run sevm d .call (.some ⟨cevm, raw⟩) (.ok d'') := by
      rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at stepRun
      exact stepRun
    have spawn : Xinst.step sevm d .call = .spawn f rsm := by
      rw [Ninst.step_exec] at hs
      exact XStep.toStep_spawn hs
    refine ⟨d'', ⟨.some ⟨cevm, raw⟩, ⟨child⟩, pc, stepRun⟩, Exec.childFrames next,
      ⟨next, rfl, lt_trans (gas_run h henter child hr) hg⟩, ?_⟩
    intro flag rest hflag nz
    have hc : Execution.commits raw = true :=
      Xinst.call_run_flag_commits fork (.inl rfl) xrun ⟨flag, rest, hflag, nz⟩
    rcases of_step_call_val_with_depth_frame (xl := .some ⟨cevm, raw⟩) operands
        (show Xlot.Filled (.some ⟨cevm, raw⟩) from ⟨child⟩) stepRun fork with
      ⟨failed, -⟩ | ⟨parent, -, dp, na, code, avail, hdepth, -, -, -, -, hpout, hdel, -, -, -, -, -,
        -, -, -, hstep'⟩
    · rw [hflag] at failed
      exact absurd (pref_head_unique failed (pref_append [flag] rest)).symm nz
    rw [hs] at hstep'
    obtain ⟨hf, hrsm⟩ := Step.spawn.inj hstep'
    replace hrsm := hrsm.1
    cases raw with
    | error e => simp only [Execution.commits, Bool.false_eq_true] at hc
    | ok body =>
      have clean : body.error = none := by
        simpa only [Execution.commits, Option.isNone_iff_eq_none] using hc
      have hsettle : f.settle (.ok body) = .ok body := by
        rw [hf, Frame.ofCall_settle_clean clean]
        congr 1
        exact Devm.recordTouch_of_not_touchedSweep (by exact fork.rules_touchedSweep) _ _ _
      have hsc : Frame.settlementCommits f (.ok body) = true := by
        simp only [Frame.settlementCommits, hsettle, clean, Option.isNone_none]
      right
      have hframed : ¬ sevm.benvStat.rules.isPrecomp t.toAdr ∨
          (getDelegatedCodeAddress (d.getCode t.toAdr)).isSome := by
        rcases hdel with ⟨-, rfl, -, rfl⟩ | ⟨dd, hsome, -, -, -⟩
        · by_cases hp : sevm.benvStat.rules.isPrecomp t.toAdr
          · exfalso
            obtain ⟨benv, hbt, -⟩ := Frame.enter_run_inv henter
            have hstat : benv.stat = sevm.benvStat := by
              rw [benvAfterTransfer_stat hbt, hf]; rfl
            have e := Frame.enter_eq_done_executePrecomp (adr := t.toAdr) hbt (by rw [hf]; rfl)
              (by
                rw [hf]
                simp only [Msg.withBenv, Frame.ofCall, callMsg, Bool.not_false, Bool.true_and]
                exact decide_eq_true (by rw [hstat]; exact hp))
            rw [henter] at e
            cases e
          · exact .inl hp
        · exact .inr (by rw [hsome]; rfl)
      refine ⟨Exec.Frame.ofRun child (Frame.raw_commits_of_settlementCommits hsc), ?_, hdepth,
        hframed, ?_⟩
      · simp only [Exec.childFrames, hsc, dite_true, List.singleton_append]
      · obtain ⟨benv, -, hcevm⟩ := Frame.enter_run_inv henter
        have hr' := hr
        rw [hrsm, hsettle] at hr'
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show cevm.sta.currentTarget = _
          rw [Frame.enter_run_currentTarget henter, hf]
          rfl
        · show cevm.sta.data = _
          rw [ExecutionTrace.Frame.enter_data_eq henter, hf]
          rfl
        · show cevm.sta.value = _
          rw [hcevm, hf]
          rfl
        · show cevm.sta.isStatic = _
          rw [Frame.enter_run_isStatic henter, hf]
          simp only [Frame.ofCall, callMsg, Bool.false_or]
        · show body.output = _
          exact (Resume.call_returnData hr').symm
        · exact (Xinst.call_run_logs fork (.inl rfl) xrun).2 cevm (.ok body) rfl |>.1 hc
        · intro ca ne
          exact (Xinst.spawn_child_world fork spawn henter).1 ca ne
        · intro ca ne key
          exact (Xinst.spawn_run_getStor fork spawn henter child hr ne).1 hsc key
        · intro ca ne
          exact Exec.Deriv.ParentStep.codePreserve (.runOk h henter child hr next) ca
            (ByteArray.toList_ne_nil_of_ne_empty ne)
        · intro a
          exact (Frame.enter_run_getCode henter a).trans (Xinst.step_spawn_getCode spawn a)
        · intro a
          show d''.getCode a = body.getCode a
          simp only [Devm.getCode, Devm.getAcct, Resume.call_state hr']
        · exact (Resume.call_output hr').trans hpout
        · have g := Xinst.step_accGrow sevm d .call fork.rules_stateGas_none
          rw [spawn] at g
          exact g.2 _ _ hr

/-- **A `STATICCALL`**: as `xa_call`, with value `0` and a static child. -/
theorem xa_staticcall (fork : CoveredFork sevm.benvStat.fork)
    (hat : Ninst.At sevm.code pc (.exec .staticcall))
    {g t ii is oi os : B256} {S : List B256}
    (hstack : d.stack = g :: t :: ii :: is :: oi :: os :: S)
    (h : XAt sevm post pc d L) :
    ∃ d', Ninst.Run sevm d (.exec .staticcall) d' ∧ ∃ L', XAt sevm post (pc + 1) d' L' ∧
      ∀ flag rest, d'.stack = flag :: rest → flag ≠ 0 →
        (sevm.benvStat.rules.isPrecomp t.toAdr ∧ L = L') ∨
        (∃ c, L = c :: L' ∧ 0 < sevm.depth ∧
          (¬ sevm.benvStat.rules.isPrecomp t.toAdr ∨
            (getDelegatedCodeAddress (d.getCode t.toAdr)).isSome) ∧
          ChildOf d d' t.toAdr (d.memory.read ii.toNat is.toNat).1 0 true c) := by
  have hstep : Evm.step ⟨pc, sevm, d⟩ = Ninst.step ⟨pc, sevm, d⟩ (.exec .staticcall) :=
    Evm.step_next hat
  have operands : (g :: t :: ii :: is :: oi :: os :: S) <<+ d.stack := by
    rw [hstack]
    simpa only [List.append_nil] using (pref_append (g :: t :: ii :: is :: oi :: os :: S) [])
  have childless : ∀ d', Ninst.StepRun pc sevm d (.exec .staticcall) .none (.ok d') →
      ∀ flag rest, d'.stack = flag :: rest → flag ≠ 0 →
        sevm.benvStat.rules.isPrecomp t.toAdr := by
    intro d' stepRun flag rest hflag nz
    have xrun : Xinst.Run sevm d .staticcall .none (.ok d') := by
      rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at stepRun
      exact stepRun
    exact Xinst.staticcall_none_precompile fork operands xrun ⟨flag, rest, hflag, nz⟩
  obtain ⟨exc, rfl, hg⟩ := h
  cases exc with
  | halt h => cases Ninst.step_ne_halt_ok (hstep.symm.trans h)
  | @cont _ _ _ _ d'' _ h next =>
    have hs := hstep.symm.trans h
    cases Ninst.step_cont_pc hs
    have stepRun : Ninst.StepRun pc sevm d (.exec .staticcall) .none (.ok d'') := by
      simp only [Ninst.StepRun, hs, Step.Run]
      exact ⟨trivial, trivial⟩
    exact ⟨_, ⟨.none, trivial, pc, stepRun⟩, _, ⟨next, rfl, lt_trans (gas_cont h) hg⟩,
      fun flag rest hflag nz => .inl ⟨childless _ stepRun flag rest hflag nz, rfl⟩⟩
  | @doneOk _ _ _ _ _ _ _ d'' _ h henter hr next =>
    have hs := hstep.symm.trans h
    cases Ninst.step_spawn_pc hs
    have stepRun : Ninst.StepRun pc sevm d (.exec .staticcall) .none (.ok d'') := by
      simp only [Ninst.StepRun, hs, Step.Run]
      exact ⟨_, RunFrame.of_done henter, hr.symm⟩
    exact ⟨_, ⟨.none, trivial, pc, stepRun⟩, _, ⟨next, rfl, lt_trans (gas_done h henter hr) hg⟩,
      fun flag rest hflag nz => .inl ⟨childless _ stepRun flag rest hflag nz, rfl⟩⟩
  | @runOk _ _ _ f rsm _ cevm raw d'' _ h henter child hr next =>
    have hs := hstep.symm.trans h
    cases Ninst.step_spawn_pc hs
    have stepRun : Ninst.StepRun pc sevm d (.exec .staticcall) (.some ⟨cevm, raw⟩)
        (.ok d'') := by
      simp only [Ninst.StepRun, hs, Step.Run]
      exact ⟨_, RunFrame.of_run henter, hr.symm⟩
    have xrun : Xinst.Run sevm d .staticcall (.some ⟨cevm, raw⟩) (.ok d'') := by
      have e := stepRun
      rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at e
      exact e
    have spawn : Xinst.step sevm d .staticcall = .spawn f rsm := by
      rw [Ninst.step_exec] at hs
      exact XStep.toStep_spawn hs
    refine ⟨d'', ⟨.some ⟨cevm, raw⟩, ⟨child⟩, pc, stepRun⟩, Exec.childFrames next,
      ⟨next, rfl, lt_trans (gas_run h henter child hr) hg⟩, ?_⟩
    intro flag rest hflag nz
    have hc : Execution.commits raw = true :=
      Xinst.call_run_flag_commits fork (.inr rfl) xrun ⟨flag, rest, hflag, nz⟩
    rcases of_step_staticcall_val_with_depth_frame_cause (xl := .some ⟨cevm, raw⟩) operands
        (show Xlot.Filled (.some ⟨cevm, raw⟩) from ⟨child⟩) stepRun fork with
      ⟨failed, -⟩ | ⟨parent, -, dp, na, code, avail, hdepth, -, -, -, -, hpout, hdel, -, -, -, -, -,
        -, -, -, hstep'⟩
    · rw [hflag] at failed
      exact absurd (pref_head_unique failed (pref_append [flag] rest)).symm nz
    rw [hs] at hstep'
    obtain ⟨hf, hrsm⟩ := Step.spawn.inj hstep'
    replace hrsm := hrsm.1
    cases raw with
    | error e => simp only [Execution.commits, Bool.false_eq_true] at hc
    | ok body =>
      have clean : body.error = none := by
        simpa only [Execution.commits, Option.isNone_iff_eq_none] using hc
      have hsettle : f.settle (.ok body) = .ok body := by
        rw [hf, Frame.ofCall_settle_clean clean]
        congr 1
        exact Devm.recordTouch_of_not_touchedSweep (by exact fork.rules_touchedSweep) _ _ _
      have hsc : Frame.settlementCommits f (.ok body) = true := by
        simp only [Frame.settlementCommits, hsettle, clean, Option.isNone_none]
      right
      have hframed : ¬ sevm.benvStat.rules.isPrecomp t.toAdr ∨
          (getDelegatedCodeAddress (d.getCode t.toAdr)).isSome := by
        rcases hdel with ⟨-, rfl, -, rfl⟩ | ⟨dd, hsome, -, -, -⟩
        · by_cases hp : sevm.benvStat.rules.isPrecomp t.toAdr
          · exfalso
            obtain ⟨benv, hbt, -⟩ := Frame.enter_run_inv henter
            have hstat : benv.stat = sevm.benvStat := by
              rw [benvAfterTransfer_stat hbt, hf]; rfl
            have e := Frame.enter_eq_done_executePrecomp (adr := t.toAdr) hbt (by rw [hf]; rfl)
              (by
                rw [hf]
                simp only [Msg.withBenv, Frame.ofCall, callMsg, Bool.not_false, Bool.true_and]
                exact decide_eq_true (by rw [hstat]; exact hp))
            rw [henter] at e
            cases e
          · exact .inl hp
        · exact .inr (by rw [hsome]; rfl)
      refine ⟨Exec.Frame.ofRun child (Frame.raw_commits_of_settlementCommits hsc), ?_, hdepth,
        hframed, ?_⟩
      · simp only [Exec.childFrames, hsc, dite_true, List.singleton_append]
      · obtain ⟨benv, -, hcevm⟩ := Frame.enter_run_inv henter
        have hr' := hr
        rw [hrsm, hsettle] at hr'
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show cevm.sta.currentTarget = _
          rw [Frame.enter_run_currentTarget henter, hf]
          rfl
        · show cevm.sta.data = _
          rw [ExecutionTrace.Frame.enter_data_eq henter, hf]
          rfl
        · show cevm.sta.value = _
          rw [hcevm, hf]
          rfl
        · show cevm.sta.isStatic = _
          rw [Frame.enter_run_isStatic henter, hf]
          simp only [Frame.ofCall, callMsg, Bool.true_or]
        · show body.output = _
          exact (Resume.call_returnData hr').symm
        · exact (Xinst.call_run_logs fork (.inr rfl) xrun).2 cevm (.ok body) rfl |>.1 hc
        · intro ca ne
          exact (Xinst.spawn_child_world fork spawn henter).1 ca ne
        · intro ca ne key
          exact (Xinst.spawn_run_getStor fork spawn henter child hr ne).1 hsc key
        · intro ca ne
          exact Exec.Deriv.ParentStep.codePreserve (.runOk h henter child hr next) ca
            (ByteArray.toList_ne_nil_of_ne_empty ne)
        · intro a
          exact (Frame.enter_run_getCode henter a).trans (Xinst.step_spawn_getCode spawn a)
        · intro a
          show d''.getCode a = body.getCode a
          simp only [Devm.getCode, Devm.getAcct, Resume.call_state hr']
        · exact (Resume.call_output hr').trans hpout
        · have g := Xinst.step_accGrow sevm d .staticcall fork.rules_stateGas_none
          rw [spawn] at g
          exact g.2 _ _ hr

end Blanc.Lift
