import Blanc.Lift.FrameWalkKit
import Blanc.Lift.FrameWalkAligned
import Blanc.Lift.HistIdentityCall

/-!
# Spawning walk steps under a frame's actual rules

`xa_call`, `xa_staticcall` and their image-carrier forms take `CoveredFork`. These twins take only
`rules.stateGas = none`, so they hold on every historical fork: a child's settlement before Paris
may record a touched account, which no field these steps state can see, and disabled delegation
resolves the target's own code.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

variable {sevm : Sevm} {post d : Devm} {pc : Nat} {L : List Exec.Frame}

/-- **A `CALL`**: one `Ninst.Run` step. When it leaves a nonzero flag, either its target is a
precompile and no child was spawned, or the next remaining child is the call's (`ChildOf`). -/
theorem xa_callH (fork : sevm.benvStat.rules.stateGas = none)
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
    exact Xinst.call_none_precompileH fork operands xrun ⟨flag, rest, hflag, nz⟩
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
      Xinst.call_run_flag_commits_noStateGas fork rfl rfl (.inl rfl) xrun ⟨flag, rest, hflag, nz⟩
    rcases of_step_call_val_with_depth_frameH (xl := .some ⟨cevm, raw⟩) operands
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
      obtain ⟨body', hsettle, hbodyE, hbodyO, hbodyS⟩ : ∃ body', f.settle (.ok body) = .ok body' ∧
          body'.error = body.error ∧ body'.output = body.output ∧ body'.state = body.state :=
        ⟨_, (congrArg (fun fr => Jaune.Frame.settle fr (.ok body)) hf).trans (Frame.ofCall_settle_clean clean), rfl, rfl, rfl⟩
      have hsc : Frame.settlementCommits f (.ok body) = true := by
        simp only [Frame.settlementCommits, hsettle, hbodyE, clean, Option.isNone_none]
      right
      have hframed : ¬ sevm.benvStat.rules.isPrecomp t.toAdr ∨
          (getDelegatedCodeAddress (d.getCode t.toAdr)).isSome := by
        have hdel' : (na = t.toAdr ∧ dp = false) ∨
            (getDelegatedCodeAddress (d.getCode t.toAdr)).isSome := by
          unfold CallCodeH at hdel
          split at hdel
          · rcases hdel with ⟨-, nameEq, -, dpEq⟩ | ⟨dd, hsome, -, -, -⟩
            · exact .inl ⟨nameEq, dpEq⟩
            · exact .inr (by rw [hsome]; rfl)
          · exact .inl ⟨hdel.1, hdel.2.2⟩
        rcases hdel' with ⟨rfl, rfl⟩ | hsome
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
        · exact .inr hsome
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
          exact ((Resume.call_returnData hr').trans hbodyO).symm
        · exact (Xinst.call_run_logs_noStateGas fork rfl rfl (.inl rfl) xrun).2 cevm (.ok body) rfl |>.1 hc
        · intro ca ne
          exact (Xinst.spawn_child_world_noStateGas fork spawn henter).1 ca ne
        · intro ca ne key
          exact (Xinst.spawn_run_getStor_noStateGas fork spawn henter child hr ne).1 hsc key
        · intro ca ne
          exact Exec.Deriv.ParentStep.codePreserve (.runOk h henter child hr next) ca
            (ByteArray.toList_ne_nil_of_ne_empty ne)
        · intro a
          exact (Frame.enter_run_getCode henter a).trans (Xinst.step_spawn_getCode spawn a)
        · intro a
          show d''.getCode a = body.getCode a
          simp only [Devm.getCode, Devm.getAcct, Resume.call_state hr', hbodyS]
        · exact (Resume.call_output hr').trans hpout
        · have g := Xinst.step_accGrow sevm d .call fork
          rw [spawn] at g
          exact g.2 _ _ hr

/-- **A `STATICCALL`**: as `xa_call`, with value `0` and a static child. -/
theorem xa_staticcallH (fork : sevm.benvStat.rules.stateGas = none)
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
    exact Xinst.staticcall_none_precompileH fork operands xrun ⟨flag, rest, hflag, nz⟩
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
      Xinst.call_run_flag_commits_noStateGas fork rfl rfl (.inr rfl) xrun ⟨flag, rest, hflag, nz⟩
    rcases of_step_staticcall_val_with_depth_frame_causeH (xl := .some ⟨cevm, raw⟩) operands
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
      obtain ⟨body', hsettle, hbodyE, hbodyO, hbodyS⟩ : ∃ body', f.settle (.ok body) = .ok body' ∧
          body'.error = body.error ∧ body'.output = body.output ∧ body'.state = body.state :=
        ⟨_, (congrArg (fun fr => Jaune.Frame.settle fr (.ok body)) hf).trans (Frame.ofCall_settle_clean clean), rfl, rfl, rfl⟩
      have hsc : Frame.settlementCommits f (.ok body) = true := by
        simp only [Frame.settlementCommits, hsettle, hbodyE, clean, Option.isNone_none]
      right
      have hframed : ¬ sevm.benvStat.rules.isPrecomp t.toAdr ∨
          (getDelegatedCodeAddress (d.getCode t.toAdr)).isSome := by
        have hdel' : (na = t.toAdr ∧ dp = false) ∨
            (getDelegatedCodeAddress (d.getCode t.toAdr)).isSome := by
          unfold CallCodeH at hdel
          split at hdel
          · rcases hdel with ⟨-, nameEq, -, dpEq⟩ | ⟨dd, hsome, -, -, -⟩
            · exact .inl ⟨nameEq, dpEq⟩
            · exact .inr (by rw [hsome]; rfl)
          · exact .inl ⟨hdel.1, hdel.2.2⟩
        rcases hdel' with ⟨rfl, rfl⟩ | hsome
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
        · exact .inr hsome
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
          exact ((Resume.call_returnData hr').trans hbodyO).symm
        · exact (Xinst.call_run_logs_noStateGas fork rfl rfl (.inr rfl) xrun).2 cevm (.ok body) rfl |>.1 hc
        · intro ca ne
          exact (Xinst.spawn_child_world_noStateGas fork spawn henter).1 ca ne
        · intro ca ne key
          exact (Xinst.spawn_run_getStor_noStateGas fork spawn henter child hr ne).1 hsc key
        · intro ca ne
          exact Exec.Deriv.ParentStep.codePreserve (.runOk h henter child hr next) ca
            (ByteArray.toList_ne_nil_of_ne_empty ne)
        · intro a
          exact (Frame.enter_run_getCode henter a).trans (Xinst.step_spawn_getCode spawn a)
        · intro a
          show d''.getCode a = body.getCode a
          simp only [Devm.getCode, Devm.getAcct, Resume.call_state hr', hbodyS]
        · exact (Resume.call_output hr').trans hpout
        · have g := Xinst.step_accGrow sevm d .staticcall fork
          rw [spawn] at g
          exact g.2 _ _ hr


section Img

variable {b : Devm} {S : List B256} {M : Mem} {G : Nat} {img : Bytes}

/-- **A `STATICCALL` step over the image carrier**: the flag and returned data `out`, the output
window written into the image, storage and logs kept; on a nonzero flag, either a precompile
target and no child, or the next remaining child is the call's (at `t`, with the input window as
calldata, static, returning `out`, logging nothing). -/
theorem xa_staticcall_imgH {pc' : Nat} {g t ii is oi os : B256} {i n o z : Nat}
    (hfork : sevm.benvStat.rules.stateGas = none) (hat : Ninst.At sevm.code pc (.exec .staticcall))
    (hpc : pc + 1 = pc') (hii : ii.toNat = i) (his : is.toNat = n) (hoi : oi.toNat = o)
    (hos : os.toNat = z) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post pc (St b (g :: t :: ii :: is :: oi :: os :: S) M G) L) :
    ∃ d flag out M' L', XAt sevm post pc' (St d (flag :: S) M' d.gasLeft) L' ∧
      (∃ d₀, Ninst.Run sevm (St b (g :: t :: ii :: is :: oi :: os :: S) M G) (.exec .staticcall)
        d₀ ∧ d₀.getCode = d.getCode) ∧
      Mem.Reads M' (Bytes.writeAt img o (out.take z)) ∧ Mem.Wf M' ∧
      d.returnData = out ∧ out.length < 2 ^ 256 ∧ (∀ a, d.getStor a = b.getStor a) ∧
      d.logs = b.logs ∧
      (flag ≠ 0 →
        (sevm.benvStat.rules.isPrecomp t.toAdr ∧ L = L') ∨
        (∃ c, L = c :: L' ∧ 0 < sevm.depth ∧ d.output = b.output ∧ Devm.AccGrow b d ∧
          (∀ a, b.getCode a ≠ .empty → d.getCode a = b.getCode a) ∧
          c.sevm.currentTarget = t.toAdr ∧ c.sevm.data = img.sliceD i n 0 ∧
          c.sevm.isStatic = true ∧ c.post.output = out ∧ c.post.logs = [] ∧
          (∀ a, c.pre.getCode a = b.getCode a) ∧ (∀ a, d.getCode a = c.post.getCode a))) := by
  subst hpc hii his hoi hos
  obtain ⟨d, s, L', h, hk⟩ := xa_staticcallH hfork hat rfl h
  obtain ⟨flag, out, hpost, hbound, -⟩ := ri_staticcall_boundedH hfork s
  refine ⟨d, flag, out, _, L', hpost.eq_St ▸ h, ⟨d, s, rfl⟩, Mem.Reads.write (Mem.Wf.extends _ hW)
    (Mem.Reads.extends _ hR) _ _, Mem.Wf.write (Mem.Wf.extends _ hW) _ _, hpost.returnData,
    hbound, hpost.stor, hpost.logs, fun nz => ?_⟩
  rcases hk flag S hpost.stack nz with hp | ⟨c, hL, hdep, -, hc⟩
  · exact .inl hp
  · refine .inr ⟨c, hL, hdep, hc.outputKeep, hc.warm, hc.code, hc.target, ?_, hc.isStatic,
      hc.output.trans hpost.returnData, ?_, hc.codePre, hc.codePost⟩
    · rw [hc.data]
      exact Mem.Reads.read hR _ _
    · have e := hc.logs
      rw [hpost.logs] at e
      have e2 : b.logs ++ c.post.logs = b.logs := e.symm
      exact List.append_right_eq_self.mp e2

/-- **An identity-precompile copy** (`CALL(gas, 4, 0, ii, is, oi, os)`) over the image carrier:
it pushed `0`, or it pushed `1`, spawned no child, kept the world (`ShaCallPost`) and laid the
input window (truncated to `os`) over the output window. -/
theorem xa_identity_imgH {pc' : Nat} {g ii is oi os : B256} {i n o z : Nat}
    (hid : IdReadyH sevm b) (hat : Ninst.At sevm.code pc (.exec .call))
    (hpc : pc + 1 = pc') (hii : ii.toNat = i) (his : is.toNat = n) (hoi : oi.toNat = o)
    (hos : os.toNat = z) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post pc (St b (g :: 4 :: 0 :: ii :: is :: oi :: os :: S) M G) L) :
    ∃ d L', XAt sevm post pc' d L' ∧
      ((d.stack = 0 :: S ∧ (g = Nat.toB256 G → 0 < sevm.depth → n ≤ 32 → d.gasLeft = 0)) ∨
        (L = L' ∧ ∃ b' G' M', ShaCallPost b b' (img.sliceD i n 0) ∧ d = St b' (1 :: S) M' G' ∧
          Mem.Reads M' (Bytes.writeAt img o ((img.sliceD i n 0).take z)) ∧ Mem.Wf M')) := by
  subst hpc hii his hoi hos
  have hG : G < 2 ^ 256 := h.gasLeft_lt
  obtain ⟨d, s, L', h, hk⟩ := xa_callH hid.stateGas hat rfl h
  refine ⟨d, L', h, ?_⟩
  rcases ri_call_identityH hid s with h0 | ⟨b', G', hpost, rfl⟩
  · refine .inl ⟨h0, fun hg hdep hn => ?_⟩
    subst hg
    exact ri_call_identity_gas_failH hid hdep hG hn s h0
  · refine .inr ⟨?_, b', G', _, ?_, rfl, ?_, ?_⟩
    · rcases hk 1 S rfl (by decide) with ⟨-, hL⟩ | ⟨c, -, -, hfr, -⟩
      · exact hL
      · exfalso
        rcases hfr with hp | hdel
        · exact hp (of_decide_eq_true hid.pre)
        · have e : getDelegatedCodeAddress
              ((St b (g :: 4 :: 0 :: ii :: is :: oi :: os :: S) M G).getCode (4 : B256).toAdr) =
              none := by
            rw [show (4 : B256).toAdr = (4 : Adr) by decide]
            exact hid.nodeleg
          rw [e] at hdel
          exact absurd hdel (by decide)
    · rw [← Mem.Reads.read hR]
      exact hpost
    · rw [← Mem.Reads.read hR]
      exact Mem.Reads.write (Mem.Wf.extends _ hW) (Mem.Reads.extends _ hR) _ _
    · exact Mem.Wf.write (Mem.Wf.extends _ hW) _ _

/-- **A `CALL` over the image carrier**: the flag on the stack over the resumed machine `d` (its
own base); on a nonzero flag, the output window holds (a prefix of) the returned data, and either
the target is a precompile and no child was spawned, or the next remaining child is the call's
(`ChildOf`, with the input window as calldata) and it ran a code frame. -/
theorem xa_call_imgH {pc' : Nat} {g t v ii is oi os : B256} {i n o z : Nat}
    (hfork : sevm.benvStat.rules.stateGas = none) (hat : Ninst.At sevm.code pc (.exec .call))
    (hpc : pc + 1 = pc') (hii : ii.toNat = i) (his : is.toNat = n) (hoi : oi.toNat = o)
    (hos : os.toNat = z) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post pc (St b (g :: t :: v :: ii :: is :: oi :: os :: S) M G) L) :
    ∃ d flag L', XAt sevm post pc' (St d (flag :: S) d.memory d.gasLeft) L' ∧
      Ninst.Run sevm (St b (g :: t :: v :: ii :: is :: oi :: os :: S) M G) (.exec .call) d ∧
      d.returnData.length < 2 ^ 256 ∧ (flag ≠ 0 →
        Mem.Reads d.memory (Bytes.writeAt img o (d.returnData.take z)) ∧ Mem.Wf d.memory ∧
        d.output = b.output ∧
        ((sevm.benvStat.rules.isPrecomp t.toAdr ∧ L = L') ∨
          (∃ c, L = c :: L' ∧ 0 < sevm.depth ∧
            (¬ sevm.benvStat.rules.isPrecomp t.toAdr ∨
              (getDelegatedCodeAddress (b.getCode t.toAdr)).isSome) ∧
            ChildOf (St b (g :: t :: v :: ii :: is :: oi :: os :: S) M G) d t.toAdr
              (img.sliceD i n 0) v sevm.isStatic c))) := by
  subst hpc hii his hoi hos
  obtain ⟨d, s, L', h, hk⟩ := xa_callH hfork hat rfl h
  obtain ⟨flag, hpost⟩ := ri_call_postH hfork s
  have hrd := ReturnDataBound.call_returnData_length_ltH s hfork
  rw [St.self hpost.stack rfl] at h
  refine ⟨d, flag, L', h, s, hrd, fun nz => ?_⟩
  obtain ⟨hmem, hout⟩ := hpost.settled nz
  refine ⟨?_, ?_, hout, ?_⟩
  · rw [hmem]
    exact Mem.Reads.write (Mem.Wf.extends _ hW) (Mem.Reads.extends _ hR) _ _
  · rw [hmem]
    exact Mem.Wf.write (Mem.Wf.extends _ hW) _ _
  · rcases hk flag S hpost.stack nz with hp | ⟨c, hL, hdep, hfr, hc⟩
    · exact .inl hp
    · refine .inr ⟨c, hL, hdep, hfr, ?_⟩
      rw [St.memory, Mem.Reads.read hR] at hc
      exact hc

/-- `xa_staticcall_img` with the memory kept aligned. -/
theorem xa_staticcall_imgAH {pc' : Nat} {g t ii is oi os : B256} {i n o z : Nat}
    (hfork : sevm.benvStat.rules.stateGas = none) (hat : Ninst.At sevm.code pc (.exec .staticcall))
    (hpc : pc + 1 = pc') (hii : ii.toNat = i) (his : is.toNat = n) (hoi : oi.toNat = o)
    (hos : os.toNat = z) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (h : XAt sevm post pc (St b (g :: t :: ii :: is :: oi :: os :: S) M G) L) :
    ∃ d flag out M' L', XAt sevm post pc' (St d (flag :: S) M' d.gasLeft) L' ∧
      (∃ d₀, Ninst.Run sevm (St b (g :: t :: ii :: is :: oi :: os :: S) M G) (.exec .staticcall)
        d₀ ∧ d₀.getCode = d.getCode) ∧
      Mem.Reads M' (Bytes.writeAt img o (out.take z)) ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      d.returnData = out ∧ out.length < 2 ^ 256 ∧ (∀ a, d.getStor a = b.getStor a) ∧
      d.logs = b.logs ∧
      (flag ≠ 0 →
        (sevm.benvStat.rules.isPrecomp t.toAdr ∧ L = L') ∨
        (∃ c, L = c :: L' ∧ 0 < sevm.depth ∧ d.output = b.output ∧ Devm.AccGrow b d ∧
          (∀ a, b.getCode a ≠ .empty → d.getCode a = b.getCode a) ∧
          c.sevm.currentTarget = t.toAdr ∧ c.sevm.data = img.sliceD i n 0 ∧
          c.sevm.isStatic = true ∧ c.post.output = out ∧ c.post.logs = [] ∧
          (∀ a, c.pre.getCode a = b.getCode a) ∧ (∀ a, d.getCode a = c.post.getCode a))) := by
  subst hpc hii his hoi hos
  obtain ⟨d, s, L', h, hk⟩ := xa_staticcallH hfork hat rfl h
  obtain ⟨flag, out, hpost, hbound, -⟩ := ri_staticcall_boundedH hfork s
  refine ⟨d, flag, out, _, L', hpost.eq_St ▸ h, ⟨d, s, rfl⟩, Mem.Reads.write (Mem.Wf.extends _ hW)
    (Mem.Reads.extends _ hR) _ _, Mem.Wf.write (Mem.Wf.extends _ hW) _ _,
    Mem.size_write_mod32 (Mem.size_extends_mod32 _ hA), hpost.returnData,
    hbound, hpost.stor, hpost.logs, fun nz => ?_⟩
  rcases hk flag S hpost.stack nz with hp | ⟨c, hL, hdep, -, hc⟩
  · exact .inl hp
  · refine .inr ⟨c, hL, hdep, hc.outputKeep, hc.warm, hc.code, hc.target, ?_, hc.isStatic,
      hc.output.trans hpost.returnData, ?_, hc.codePre, hc.codePost⟩
    · rw [hc.data]
      exact Mem.Reads.read hR _ _
    · have e := hc.logs
      rw [hpost.logs] at e
      have e2 : b.logs ++ c.post.logs = b.logs := e.symm
      exact List.append_right_eq_self.mp e2

/-- `xa_call_img` with the memory kept aligned on a nonzero flag. -/
theorem xa_call_imgAH {pc' : Nat} {g t v ii is oi os : B256} {i n o z : Nat}
    (hfork : sevm.benvStat.rules.stateGas = none) (hat : Ninst.At sevm.code pc (.exec .call))
    (hpc : pc + 1 = pc') (hii : ii.toNat = i) (his : is.toNat = n) (hoi : oi.toNat = o)
    (hos : os.toNat = z) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (h : XAt sevm post pc (St b (g :: t :: v :: ii :: is :: oi :: os :: S) M G) L) :
    ∃ d flag L', XAt sevm post pc' (St d (flag :: S) d.memory d.gasLeft) L' ∧
      Ninst.Run sevm (St b (g :: t :: v :: ii :: is :: oi :: os :: S) M G) (.exec .call) d ∧
      d.returnData.length < 2 ^ 256 ∧ (flag ≠ 0 →
        Mem.Reads d.memory (Bytes.writeAt img o (d.returnData.take z)) ∧ Mem.Wf d.memory ∧
        d.memory.size % 32 = 0 ∧ d.output = b.output ∧
        ((sevm.benvStat.rules.isPrecomp t.toAdr ∧ L = L') ∨
          (∃ c, L = c :: L' ∧ 0 < sevm.depth ∧
            (¬ sevm.benvStat.rules.isPrecomp t.toAdr ∨
              (getDelegatedCodeAddress (b.getCode t.toAdr)).isSome) ∧
            ChildOf (St b (g :: t :: v :: ii :: is :: oi :: os :: S) M G) d t.toAdr
              (img.sliceD i n 0) v sevm.isStatic c))) := by
  subst hpc hii his hoi hos
  obtain ⟨d, s, L', h, hk⟩ := xa_callH hfork hat rfl h
  obtain ⟨flag, hpost⟩ := ri_call_postH hfork s
  have hrd := ReturnDataBound.call_returnData_length_ltH s hfork
  rw [St.self hpost.stack rfl] at h
  refine ⟨d, flag, L', h, s, hrd, fun nz => ?_⟩
  obtain ⟨hmem, hout⟩ := hpost.settled nz
  refine ⟨?_, ?_, ?_, hout, ?_⟩
  · rw [hmem]
    exact Mem.Reads.write (Mem.Wf.extends _ hW) (Mem.Reads.extends _ hR) _ _
  · rw [hmem]
    exact Mem.Wf.write (Mem.Wf.extends _ hW) _ _
  · rw [hmem]
    exact Mem.size_write_mod32 (Mem.size_extends_mod32 _ hA)
  · rcases hk flag S hpost.stack nz with hp | ⟨c, hL, hdep, hfr, hc⟩
    · exact .inl hp
    · refine .inr ⟨c, hL, hdep, hfr, ?_⟩
      rw [St.memory, Mem.Reads.read hR] at hc
      exact hc

/-- `xa_identity_img` with the memory kept aligned. -/
theorem xa_identity_imgAH {pc' : Nat} {g ii is oi os : B256} {i n o z : Nat}
    (hid : IdReadyH sevm b) (hat : Ninst.At sevm.code pc (.exec .call))
    (hpc : pc + 1 = pc') (hii : ii.toNat = i) (his : is.toNat = n) (hoi : oi.toNat = o)
    (hos : os.toNat = z) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (h : XAt sevm post pc (St b (g :: 4 :: 0 :: ii :: is :: oi :: os :: S) M G) L) :
    ∃ d L', XAt sevm post pc' d L' ∧
      ((d.stack = 0 :: S ∧ (g = Nat.toB256 G → 0 < sevm.depth → n ≤ 32 → d.gasLeft = 0)) ∨
        (L = L' ∧ ∃ b' G' M', ShaCallPost b b' (img.sliceD i n 0) ∧ d = St b' (1 :: S) M' G' ∧
          Mem.Reads M' (Bytes.writeAt img o ((img.sliceD i n 0).take z)) ∧ Mem.Wf M' ∧
          M'.size % 32 = 0)) := by
  subst hpc hii his hoi hos
  have hG : G < 2 ^ 256 := h.gasLeft_lt
  obtain ⟨d, s, L', h, hk⟩ := xa_callH hid.stateGas hat rfl h
  refine ⟨d, L', h, ?_⟩
  rcases ri_call_identityH hid s with h0 | ⟨b', G', hpost, rfl⟩
  · refine .inl ⟨h0, fun hg hdep hn => ?_⟩
    subst hg
    exact ri_call_identity_gas_failH hid hdep hG hn s h0
  · refine .inr ⟨?_, b', G', _, ?_, rfl, ?_, ?_, ?_⟩
    · rcases hk 1 S rfl (by decide) with ⟨-, hL⟩ | ⟨c, -, -, hfr, -⟩
      · exact hL
      · exfalso
        rcases hfr with hp | hdel
        · exact hp (of_decide_eq_true hid.pre)
        · have e : getDelegatedCodeAddress
              ((St b (g :: 4 :: 0 :: ii :: is :: oi :: os :: S) M G).getCode (4 : B256).toAdr) =
              none := by
            rw [show (4 : B256).toAdr = (4 : Adr) by decide]
            exact hid.nodeleg
          rw [e] at hdel
          exact absurd hdel (by decide)
    · rw [← Mem.Reads.read hR]
      exact hpost
    · rw [← Mem.Reads.read hR]
      exact Mem.Reads.write (Mem.Wf.extends _ hW) (Mem.Reads.extends _ hR) _ _
    · exact Mem.Wf.write (Mem.Wf.extends _ hW) _ _
    · exact Mem.size_write_mod32 (Mem.size_extends_mod32 _ hA)

end Img

end Blanc.Lift
