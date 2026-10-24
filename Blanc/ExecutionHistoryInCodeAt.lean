import Blanc.ExecutionHistory
import Blanc.ExecutionCodeAt
import Blanc.ExecutionTraceCodeAt
import Blanc.ExecutionMessageEffects
import Blanc.ExecutionNoDelSafeHistory
import Blanc.ExecutionHistoryInForkFacts
import Blanc.ExecutionHistoryInWarmth
import Blanc.HistoricalFork

/-!
# Empty code at one address along selected-domain (`In`) histories

`In` forms of `ConfiguredHistoryTrace.codeAt_empty` and
`ConfiguredHistoryTrace.NoAuthorityAt`
(`Blanc/ExecutionTraceCodeAt.lean`): a retained `In`-history that starts
with empty code at `a` ends with empty code at `a`, and so does every
transaction frame it enters. The interpreter-level step case doubles as
the neutral twin of `Exec.codeAt_avoid`, proved through the
`stateGas = none` instruction shape (`Xinst.step_shapeNoStateGas`) instead
of the covered one; child environments travel by the exact spawn equality
(`Evm.step_spawn_child_benvStat`).

EIP-7702 authority is cased per fork, as ordered: the message-level fact
takes `rules.delegationEnabled = false` as a disjunct beside the usual
no-authority premise, so before Prague — where delegation is disabled —
the fact holds with no authority premise. At history level the disjunct
is supplied from an explicit per-fork disabled-delegation hypothesis
(discharged on `HistFork` by decision) on pre-Prague blocks and from an
`In` no-authority premise on later ones; fully pre-Prague histories get a
corollary with no authority premise at all.

Contract-neutral: no contract name in any statement.
-/

namespace Blanc

namespace ExecutionTrace

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat

/-- A CREATE-family child frame has no code address, under `stateGas = none`. -/
theorem Xinst.step_spawn_create_codeAddress_noStateGas {sevm : Sevm} {devm : Devm}
    {x : Xinst} (hsg : sevm.benvStat.rules.stateGas = none)
    {f : Frame} {rsm : Resume}
    (hs : Xinst.step sevm devm x = .spawn f rsm) (hc : f.isCreate = true) :
    f.inner.codeAddress = none := by
  rcases Xinst.step_shapeNoStateGas sevm devm x hsg with ⟨ex, hsh, -⟩ |
    ⟨d, e, na, mi, ms, hf, hsh⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, -, -, hsh⟩ <;> rw [hsh] at hs
  · cases hs
  · exact genericCreate.step_spawn_codeAddress hs
  · exact absurd hc (by rw [genericCall.step_spawn_isCreate_false hs]; simp only [Bool.false_eq_true,
    not_false_eq_true])

/-- **The code at `a` along one call-type instruction**, given that its
child keeps it and that the instruction enters no CREATE frame at `a`.
Neutral form: the covered step shape is replaced by the
`stateGas = none` one. -/
lemma Xinst.codeAt_effectRecAvoid_noStateGas {a : Adr} (x : Xinst) :
    ∀ {sevm : Sevm} {pre : Devm} {xl : Xlot} {out : Execution},
      sevm.benvStat.rules.stateGas = none → Xinst.AvoidsAt a sevm pre x →
      Xlot.Rel (Devm.CodeAt a) xl →
      Xinst.Run sevm pre x xl out → Execution.Rel (Devm.CodeAt a) pre out := by
  intro sevm devm xl exn hsg havoid hxl run
  have inv := Xlot.invAt_of_rel hxl
  unfold Xinst.Run at run
  have lift : ∀ {d : Devm}, Devm.InstructionFrame devm d →
      Execution.getCode exn a = d.getCode a → Execution.Rel (Devm.CodeAt a) devm exn := by
    intro d hf h
    cases exn with
    | error e => exact h.trans (hf.getCode a).symm
    | ok d' => exact h.trans (hf.getCode a).symm
  rcases Xinst.step_shapeNoStateGas sevm devm x hsg with ⟨ex, hs, hframe⟩ |
    ⟨d, e, na, mi, ms, hf, hs⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, -, -, hs⟩ <;> rw [hs] at run
  · obtain ⟨-, rfl⟩ := run
    cases exn with
    | error e => exact (hframe.getCode a).symm
    | ok d' => exact (hframe.getCode a).symm
  · refine lift hf (GenericCreate.codeAt ?_ inv run)
    intro f rsm cevm hsf henter
    have hc := genericCreate.step_spawn_frame hsf
    have hcreate := genericCreate.step_spawn_isCreate hsf
    intro h
    exact havoid f rsm cevm (hs.trans hsf) henter hcreate (hc.2.1.trans h.symm)
  · exact lift hf (GenericCall.codeAt inv run)

/-- **One interpreter step keeps the code at `a`**, given that its child
keeps it and that it enters no CREATE frame at `a`. Neutral form. -/
lemma Evm.step_codeAt_noStateGas {a : Adr} {pc : Nat} {sevm : Sevm} {devm : Devm}
    {xl : Xlot} {out : Execution} (hsg : sevm.benvStat.rules.stateGas = none)
    (hav : ∀ x, Xinst.At sevm.code pc x → Xinst.AvoidsAt a sevm devm x)
    (hxl : Xlot.Rel (Devm.CodeAt a) xl)
    (hrun : Step.Run (Evm.step ⟨pc, sevm, devm⟩) xl out) :
    Execution.Rel (Devm.CodeAt a) devm out := by
  have hIR : ∀ ⦃d d' : Devm⦄, Devm.InstructionFrame d d' → Devm.CodeAt a d d' :=
    fun _ _ hf => (hf.getCode a).symm
  rcases hgi : (Evm.getInst ⟨pc, sevm, devm⟩) with _ | i
  · rw [Evm.step_invOp hgi] at hrun
    obtain ⟨-, rfl⟩ := hrun
    exact Devm.codeAt_refl a _
  · cases i with
    | next n =>
      rw [Evm.step_next (n := n) hgi] at hrun
      cases n with
      | reg r => exact Ninst.effectRec_reg (Rinst.codeAt_effect a r) hxl hrun
      | exec x =>
        simp only [Ninst.step_exec] at hrun
        exact Xinst.codeAt_effectRecAvoid_noStateGas x hsg (hav x hgi) hxl
          (XStep.run_toStep.mp hrun)
      | push xs hxs => exact Ninst.push_effectRec_of_instructionFrame hIR hxl hrun
      | dupn imm => exact Ninst.dupn_effectRec_of_instructionFrame hIR hxl hrun
      | swapn imm => exact Ninst.swapn_effectRec_of_instructionFrame hIR hxl hrun
      | exchange imm => exact Ninst.exchange_effectRec_of_instructionFrame hIR hxl hrun
    | jump j =>
      rw [Evm.step_jump (j := j) hgi] at hrun
      obtain ⟨-, hcase⟩ := Step.run_ofJump hrun
      have hjr := Jinst.codeAt_effect a j (evm := ⟨pc, sevm, devm⟩)
        (out := j.run ⟨pc, sevm, devm⟩) rfl
      rcases hcase with ⟨e, hje, rfl⟩ | ⟨pc', d, hje, rfl⟩ <;> rw [hje] at hjr <;> exact hjr
    | last l =>
      rw [Evm.step_last (l := l) hgi] at hrun
      obtain ⟨-, rfl⟩ := hrun
      exact Linst.codeAt_effect a l rfl

/-- **An execution keeps the code at `a`, and so does every frame it
enters**, when it enters no CREATE frame targeting `a`. Neutral form of
`Exec.codeAt_avoid`: coverage is replaced by `stateGas = none`, carried
to spawned children by the exact spawn environment equality. -/
theorem Exec.codeAt_avoid_noStateGas {a : Adr} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hsg : sevm.benvStat.rules.stateGas = none)
    (avoid : ∀ root ∈ Exec.rawFrameRoots run,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a) :
    Execution.Rel (Devm.CodeAt a) pre out ∧
      ∀ root ∈ Exec.rawFrameRoots run, root.devm.getCode a = pre.getCode a := by
  revert hsg avoid
  induction run with
  | halt hstep =>
      intro hsg avoid
      have hc := Evm.step_codeAt_noStateGas (a := a) (xl := .none) hsg
        (Xinst.avoidsAt_of_step (fun f rsm pc' cevm h => by rw [hstep] at h; cases h))
        trivial (by rw [hstep]; exact ⟨rfl, rfl⟩)
      refine ⟨hc, ?_⟩
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst member
      rfl
  | @cont pc sevm devm pc' devm' ex hstep next ih =>
      intro hsg avoid
      have hself : sevm.codeAddress = none → sevm.currentTarget ≠ a :=
        avoid ⟨pc, sevm, devm, ex, Exec.cont hstep next⟩ (List.mem_cons_self ..)
      have hc : Devm.CodeAt a _ _ := Evm.step_codeAt_noStateGas (xl := .none) (out := .ok _)
        hsg
        (Xinst.avoidsAt_of_step (fun f rsm pc' cevm h => by rw [hstep] at h; cases h))
        trivial (by rw [hstep]; exact ⟨rfl, rfl⟩)
      obtain ⟨hrel, hroots⟩ := ih hsg (by
        intro root member
        simp only [Exec.rawFrameRoots, List.mem_cons] at member
        rcases member with rfl | member
        · exact hself
        · exact avoid root (by simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants,
          List.mem_cons, member, or_true]))
      refine ⟨Execution.Rel.trans_left (Devm.codeAt_trans a) hc hrel, ?_⟩
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact (hroots root (by simp only [Exec.rawFrameRoots, List.mem_cons, member,
          or_true])).trans hc
  | doneErr hstep henter hresume =>
      intro hsg avoid
      have hc := Evm.step_codeAt_noStateGas (a := a) (xl := .none) (out := .error _) hsg
        (Xinst.avoidsAt_of_step (fun f' rsm' pc' cevm h hen => by
          rw [hstep] at h; cases h; rw [henter] at hen; cases hen))
        trivial (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hresume.symm⟩)
      refine ⟨hc, ?_⟩
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst member
      rfl
  | @doneOk pc sevm devm f rsm pc' r devm' ex hstep henter hresume next ih =>
      intro hsg avoid
      have hself : sevm.codeAddress = none → sevm.currentTarget ≠ a :=
        avoid ⟨pc, sevm, devm, ex, Exec.doneOk hstep henter hresume next⟩
          (List.mem_cons_self ..)
      have hc : Devm.CodeAt a _ _ := Evm.step_codeAt_noStateGas (xl := .none) (out := .ok _) hsg
        (Xinst.avoidsAt_of_step (fun f' rsm' pc' cevm h hen => by
          rw [hstep] at h; cases h; rw [henter] at hen; cases hen))
        trivial (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hresume.symm⟩)
      obtain ⟨hrel, hroots⟩ := ih hsg (by
        intro root member
        simp only [Exec.rawFrameRoots, List.mem_cons] at member
        rcases member with rfl | member
        · exact hself
        · exact avoid root (by simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants,
          List.mem_cons, member, or_true]))
      refine ⟨Execution.Rel.trans_left (Devm.codeAt_trans a) hc hrel, ?_⟩
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact (hroots root (by simp only [Exec.rawFrameRoots, List.mem_cons, member,
          or_true])).trans hc
  | @runErr pc sevm devm f rsm pc' cevm raw e hstep henter child hresume ih =>
      intro hsg avoid
      have hsg_c : cevm.sta.benvStat.rules.stateGas = none := by
        rw [Evm.step_spawn_child_benvStat hstep henter]
        exact hsg
      have hstart := (Evm.step_spawn_child hstep henter).2.1 a
      have hcavoid : cevm.sta.codeAddress = none → cevm.sta.currentTarget ≠ a :=
        avoid ⟨cevm.pc, cevm.sta, cevm.dyna, raw, child⟩
          (by simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
            Exec.Deriv.mk.injEq, ExceptT.stM_eq, true_or, or_true])
      have hcode : cevm.sta.codeAddress = f.inner.codeAddress := by
        obtain ⟨benv, -, h⟩ := Frame.enter_run_inv henter
        rw [h]
        rfl
      obtain ⟨x, -, hxs, -⟩ := Evm.step_spawn_inv hstep
      obtain ⟨hrel, hroots⟩ := ih hsg_c (by
        intro root member
        exact avoid root (by
          simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member ⊢
          exact Or.inr member))
      have hc := Evm.step_codeAt_noStateGas (a := a) (xl := .some ⟨_, _⟩) (out := .error _) hsg
        (Xinst.avoidsAt_of_step (fun f' rsm' pc'' cevm' h hen hcr => by
          rw [hstep] at h; cases h; rw [henter] at hen; cases hen
          rw [← Frame.enter_run_currentTarget henter]
          exact hcavoid (hcode.trans (Xinst.step_spawn_create_codeAddress_noStateGas hsg hxs hcr))))
        hrel (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hresume.symm⟩)
      refine ⟨hc, ?_⟩
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | rfl | member
      · rfl
      · exact hstart
      · exact (hroots root (by simp only [Exec.rawFrameRoots, List.mem_cons, member,
          or_true])).trans hstart
  | @runOk pc sevm devm f rsm pc' cevm raw devm' ex hstep henter child hresume next
      ihChild ihNext =>
      intro hsg avoid
      have hself : sevm.codeAddress = none → sevm.currentTarget ≠ a :=
        avoid ⟨pc, sevm, devm, ex, Exec.runOk hstep henter child hresume next⟩
          (List.mem_cons_self ..)
      have hsg_c : cevm.sta.benvStat.rules.stateGas = none := by
        rw [Evm.step_spawn_child_benvStat hstep henter]
        exact hsg
      have hstart := (Evm.step_spawn_child hstep henter).2.1 a
      have hcavoid : cevm.sta.codeAddress = none → cevm.sta.currentTarget ≠ a :=
        avoid ⟨cevm.pc, cevm.sta, cevm.dyna, raw, child⟩
          (by simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
            Exec.Deriv.mk.injEq, ExceptT.stM_eq, List.mem_append, true_or, or_true])
      have hcode : cevm.sta.codeAddress = f.inner.codeAddress := by
        obtain ⟨benv, -, h⟩ := Frame.enter_run_inv henter
        rw [h]
        rfl
      obtain ⟨x, -, hxs, -⟩ := Evm.step_spawn_inv hstep
      obtain ⟨hrelChild, hrootsChild⟩ := ihChild hsg_c (by
        intro root member
        exact avoid root (by
          simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
            List.mem_append] at member ⊢
          rcases member with h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))))
      have hc : Devm.CodeAt a _ _ := Evm.step_codeAt_noStateGas (xl := .some ⟨_, _⟩)
        (out := .ok _) hsg
        (Xinst.avoidsAt_of_step (fun f' rsm' pc'' cevm' h hen hcr => by
          rw [hstep] at h; cases h; rw [henter] at hen; cases hen
          rw [← Frame.enter_run_currentTarget henter]
          exact hcavoid (hcode.trans (Xinst.step_spawn_create_codeAddress_noStateGas hsg hxs hcr))))
        hrelChild (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hresume.symm⟩)
      obtain ⟨hrel, hroots⟩ := ihNext hsg (by
        intro root member
        simp only [Exec.rawFrameRoots, List.mem_cons] at member
        rcases member with rfl | member
        · exact hself
        · exact avoid root (by
          simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
            List.mem_append]
          exact Or.inr (Or.inr (Or.inr member))))
      refine ⟨Execution.Rel.trans_left (Devm.codeAt_trans a) hc hrel, ?_⟩
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.mem_append] at member
      rcases member with rfl | rfl | member | member
      · rfl
      · exact hstart
      · exact (hrootsChild root (by simp only [Exec.rawFrameRoots, List.mem_cons, member,
          or_true])).trans hstart
      · exact (hroots root (by simp only [Exec.rawFrameRoots, List.mem_cons, member,
          or_true])).trans hc

/-- A retained slot keeps the code at `a`, and so do the frames it entered.
Neutral form. -/
theorem RetainedXlot.codeAt_of_runFrame_noStateGas
    {frame : Frame} {slot : Xlot}
    {out : Except (EvmError × State × AdrSet × Tra) Devm} {a : Adr}
    (retained : RetainedXlot slot) (hrun : RunFrame frame slot out)
    (hsg : frame.inner.benv.stat.rules.stateGas = Option.none)
    (avoid : ∀ root ∈ retained.rawFrames, root.sevm.codeAddress = Option.none →
      root.sevm.currentTarget ≠ a) :
    Xlot.InvAt a slot ∧
      ∀ root ∈ retained.rawFrames, root.devm.getCode a = frame.inner.benv.state.getCode a := by
  cases retained with
  | none => exact ⟨trivial, fun root member => by simp only [rawFrames,
    List.not_mem_nil] at member⟩
  | @some pc sevm pre execution run =>
      obtain ⟨henter, _⟩ := RunFrame.some_inv hrun
      have hstat := Frame.enter_run_benvStat henter
      have hcode := Frame.enter_run_getCode henter a
      obtain ⟨hrel, hroots⟩ := Exec.codeAt_avoid_noStateGas run
        (by rw [hstat]; exact hsg) avoid
      exact ⟨Xlot.invAt_of_rel hrel, fun root member => (hroots root member).trans hcode⟩

/-- A settled message keeps the code at `a`, and so does every frame it
enters. Neutral form. -/
theorem ProcessMessageTrace.codeAt_noStateGas
    {a : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessMessageTrace msg (.ok post))
    (hsg : msg.benv.stat.rules.stateGas = none)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    post.getCode a = msg.benv.state.getCode a ∧
      ∀ root ∈ trace.rawFrames, root.devm.getCode a = msg.benv.state.getCode a := by
  obtain ⟨inv, hroots⟩ := RetainedXlot.codeAt_of_runFrame_noStateGas trace.retained
    trace.run hsg avoid
  exact ⟨ProcessMessage.codeAt inv trace.run, hroots⟩

/-- A settled create message keeps the code at `a`, and so does every frame
it enters. Neutral form. -/
theorem ProcessCreateMessageTrace.codeAt_noStateGas
    {a : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessCreateMessageTrace msg (.ok post))
    (hsg : msg.benv.stat.rules.stateGas = none) (hca : msg.codeAddress = none)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    post.getCode a = msg.benv.state.getCode a ∧
      ∀ root ∈ trace.rawFrames, root.devm.getCode a = msg.benv.state.getCode a := by
  obtain ⟨inv, hroots⟩ := RetainedXlot.codeAt_of_runFrame_noStateGas trace.retained
    trace.run hsg avoid
  refine ⟨?_, fun root member =>
    (hroots root member).trans (processCreateMessage.msg_getCode msg a)⟩
  obtain ⟨slot, retained, hrun⟩ := trace
  cases retained with
  | none => exact ProcessCreateMessage.codeAt_none hca hrun
  | @some pc sevm pre execution run =>
      obtain ⟨henter, _⟩ := RunFrame.some_inv hrun
      have hne : a ≠ msg.currentTarget := by
        intro h
        have hself := avoid ⟨pc, sevm, pre, execution, run⟩
          (by simp only [rawFrames, RetainedXlot.rawFrames, Exec.rawFrameRoots, List.mem_cons,
            true_or])
        have hcode : sevm.codeAddress = none := by
          obtain ⟨benv, -, hevm⟩ := Frame.enter_run_inv henter
          have := congrArg (fun e : Evm => e.sta.codeAddress) hevm
          exact this.trans hca
        exact hself hcode ((Frame.enter_run_currentTarget henter).trans h.symm)
      exact ProcessCreateMessage.codeAt hne inv hrun

/-- **A settled message call keeps the code at `a`, and so does every frame
it enters**, when it enters no frame targeting `a`. Authority is cased per
fork: either delegation is disabled (the pre-Prague arm, needing no
authority premise) or no authorization of the transaction recovers to `a`. -/
theorem MessageCallTrace.codeAt_noStateGas
    {a : Adr} {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (hca : msg.target.isNone = true → msg.codeAddress = none)
    (hauth : msg.benv.stat.rules.delegationEnabled = false ∨
      ∀ auth ∈ msg.tenv.stat.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    state.getCode a = msg.benv.state.getCode a ∧
      ∀ root ∈ trace.rawFrames, root.devm.getCode a = msg.benv.state.getCode a := by
  cases trace with
  | createCollision target collision result =>
      refine ⟨?_, fun root member => by simp only [rawFrames, List.not_mem_nil] at member⟩
      rw [processMessageCall_createCollision_state_eq_noStateGas target collision result hsg]
  | createRun target collision evm core coreTrace result =>
      obtain ⟨hpost, hroots⟩ := coreTrace.codeAt_noStateGas hsg (hca target) avoid
      refine ⟨?_, hroots⟩
      rw [processMessageCall_createRun_state_eq_noStateGas target collision core result hsg]
      exact hpost
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
      have hsgExec : execMsg.benv.stat.rules.stateGas = none := by
        rw [execMsgEq, messageCallExecutionMessage_benv_stat,
          messageCallDelegation_benv_stat delegation]
        exact hsg
      have hcode : execMsg.benv.state.getCode a = msg.benv.state.getCode a := by
        rcases hauth with hdis | hauth
        · have hleg : messageCallDelegation msg = .ok ⟨msg, 0⟩ :=
            processMessageCall.legacyAuthorization_disabled msg hdis
          have hdel : delegated = msg :=
            (Prod.mk.inj (Except.ok.inj (hleg.symm.trans delegation))).1.symm
          rw [execMsgEq, hdel]
          exact messageCallExecutionMessage_getCode msg a
        · rw [execMsgEq, messageCallExecutionMessage_getCode]
          exact messageCallDelegation_getCode hauth delegation
      obtain ⟨hpost, hroots⟩ := coreTrace.codeAt_noStateGas hsgExec avoid
      refine ⟨?_, fun root member => (hroots root member).trans hcode⟩
      rw [processMessageCall_callRun_state_eq_noStateGas target delegation execMsgEq core
        result hsg]
      exact hpost.trans hcode

/-- Removing touched empty accounts from empty code leaves empty code. -/
theorem sweepTouchedAccounts_getCode_empty (rules : ForkRules) (addresses : List Adr)
    {state : State} {a : Adr} (h : state.getCode a = ByteArray.empty) :
    (sweepTouchedAccounts rules addresses state).getCode a = ByteArray.empty := by
  unfold sweepTouchedAccounts
  split
  · induction addresses generalizing state with
    | nil => exact h
    | cons x xs ih =>
        rw [List.foldl_cons]
        split
        · exact ih (destroyAccount_getCode_empty h)
        · exact ih h
  · exact h

/-- **A transaction keeps the code at `a`, and so does every frame it
enters**, when no frame it enters targets `a`. Either delegation is
disabled or none of its authorizations recovers to `a`. A transaction
that starts with empty code at `a` ends with empty code at `a`. -/
theorem TransactionTrace.codeAt_empty_noStateGas
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none) {a : Adr}
    (hauth : benv.stat.rules.delegationEnabled = false ∨
      ∀ auth ∈ tx.auths, ∀ authority, recoverAuthority auth = .ok authority →
        authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hempty : benv.state.getCode a = ByteArray.empty) :
    (∀ root ∈ trace.rawFrames, root.devm.getCode a = ByteArray.empty) ∧
      state.getCode a = ByteArray.empty := by
  have hbenv := prepareMessage_benv trace.prepared
  obtain ⟨htenv, hca⟩ := prepareMessage_fields trace.prepared
  have hdebit : trace.debitState.getCode a = benv.state.getCode a := by
    have h1 := State.subBal_getCode trace.debit (a := a)
    rw [h1]
    unfold State.getCode
    rw [State.incrNonce_get_code]
  have hmsgState : trace.msg.benv.state.getCode a = ByteArray.empty := by
    rw [hbenv]
    exact hdebit.trans hempty
  have hmsgSg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [hbenv]
    exact hsg
  have hmsgAuth : trace.msg.benv.stat.rules.delegationEnabled = false ∨
      ∀ auth ∈ trace.msg.tenv.stat.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ a := by
    rcases hauth with hdis | hauth
    · exact Or.inl (by rw [hbenv]; exact hdis)
    · exact Or.inr (by
        rw [htenv]
        simpa only [transactionTenv, Std.TreeMap.empty_eq_emptyc, ne_eq] using hauth)
  obtain ⟨hpost, hroots⟩ := trace.message.codeAt_noStateGas hmsgSg hca hmsgAuth avoid
  refine ⟨fun root member => (hroots root member).trans hmsgState, ?_⟩
  obtain ⟨refundCounter, -, hfinal⟩ := trace.exists_selectedFinalStateForm hsg
  have hcode : ∀ s : State, s.getCode a = ByteArray.empty →
      (sweepTouchedAccounts benv.stat.rules trace.messageOut.touchedAccounts.toList
        (trace.messageOut.accountsToDelete.toList.foldl destroyAccount s)).getCode a =
        ByteArray.empty := fun s hs => by
    rw [sweepTouchedAccounts_getCode_empty _ _ (foldl_destroyAccount_getCode_empty _ hs)]
  rw [hfinal]
  exact hcode _ (by
    rw [State.addBal_getCode, State.addBal_getCode]
    exact hpost.trans hmsgState)

/-- A selected transaction list keeps empty code at `a`, and so does every
frame it enters. -/
theorem ApplyTransactionsTrace.codeAt_empty_noStateGas
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none) {a : Adr}
    (hauth : benv.stat.rules.delegationEnabled = false ∨
      ∀ p ∈ txs, ∀ auth ∈ p.2.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hempty : benv.state.getCode a = ByteArray.empty) :
    (∀ root ∈ trace.rawFrames, root.devm.getCode a = ByteArray.empty) ∧
      finalBenv.state.getCode a = ByteArray.empty := by
  induction trace with
  | nil => exact ⟨fun root member => by simp only [rawFrames, List.not_mem_nil] at member,
      hempty⟩
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail ih =>
      have hhead : benv.stat.rules.delegationEnabled = false ∨
          ∀ auth ∈ tx.auths, ∀ authority,
            recoverAuthority auth = .ok authority → authority ≠ a := by
        rcases hauth with hdis | hauth
        · exact Or.inl hdis
        · exact Or.inr (hauth _ (List.mem_cons_self ..))
      have htail : benv.stat.rules.delegationEnabled = false ∨
          ∀ p ∈ txs, ∀ auth ∈ p.2.auths, ∀ authority,
            recoverAuthority auth = .ok authority → authority ≠ a := by
        rcases hauth with hdis | hauth
        · exact Or.inl hdis
        · exact Or.inr (fun p hp => hauth p (List.mem_cons_of_mem _ hp))
      obtain ⟨hroots, hstate⟩ := head.codeAt_empty_noStateGas hsg hhead
        (fun root member => avoid root (by
          simp only [ApplyTransactionsTrace.rawFrames, List.mem_append]
          exact Or.inl member)) hempty
      obtain ⟨hroots', hfinal⟩ := ih hsg htail
        (fun root member => avoid root (by
          simp only [ApplyTransactionsTrace.rawFrames, List.mem_append]
          exact Or.inr member)) hstate
      refine ⟨fun root member => ?_, hfinal⟩
      simp only [ApplyTransactionsTrace.rawFrames, List.mem_append] at member
      rcases member with member | member
      · exact hroots root member
      · exact hroots' root member

/-- A system message keeps empty code at `a`, and so does every frame it
enters: its authorization list is empty. -/
theorem SystemMessageTrace.codeAt_empty_noStateGas
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hsg : benv.stat.rules.stateGas = none) {a : Adr}
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    state.getCode a = benv.state.getCode a ∧
      ∀ root ∈ trace.rawFrames, root.devm.getCode a = benv.state.getCode a := by
  have hmsgSg : (systemTransactionMessage benv target data).benv.stat.rules.stateGas = none := by
    unfold systemTransactionMessage processSystemTransactionMsg Benv.beginTransaction
    exact hsg
  have hca : (systemTransactionMessage benv target data).target.isNone = true →
      (systemTransactionMessage benv target data).codeAddress = none := by
    intro h
    simp only [systemTransactionMessage, processSystemTransactionMsg, Option.isNone_some,
      Bool.false_eq_true] at h
  have hauth : ∀ auth ∈ (systemTransactionMessage benv target data).tenv.stat.auths,
      ∀ authority, recoverAuthority auth = .ok authority → authority ≠ a := by
    intro auth hauth
    simp only [systemTransactionMessage, processSystemTransactionMsg, processSystemTransactionTenv,
      Std.TreeMap.empty_eq_emptyc, List.not_mem_nil] at hauth
  have hdis : (systemTransactionMessage benv target data).benv.stat.rules.delegationEnabled =
      false ∨ ∀ auth ∈ (systemTransactionMessage benv target data).tenv.stat.auths,
        ∀ authority, recoverAuthority auth = .ok authority → authority ≠ a :=
    Or.inr hauth
  exact trace.message.codeAt_noStateGas hmsgSg hca hdis avoid

/-- A beacon stage that starts with empty code at `a` ends with it, and so
does every frame it enters. -/
theorem BeaconStageTrace.codeAt_empty_noStateGas
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (hsg : benv.stat.rules.stateGas = none) {a : Adr}
    (hempty : benv.state.getCode a = ByteArray.empty)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    state.getCode a = ByteArray.empty ∧
      ∀ root ∈ trace.rawFrames, root.devm.getCode a = benv.state.getCode a := by
  cases trace with
  | skipped => exact ⟨hempty, fun root member => by simp only [rawFrames,
    List.not_mem_nil] at member⟩
  | called _ _ message _ _ =>
      obtain ⟨hpost, hroots⟩ := message.codeAt_empty_noStateGas hsg avoid
      exact ⟨hpost.trans hempty, hroots⟩

/-- A history-storage stage that starts with empty code at `a` ends with
it, and so does every frame it enters. -/
theorem HistoryStageTrace.codeAt_empty_noStateGas
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (hsg : benv.stat.rules.stateGas = none) {a : Adr}
    (hempty : benv.state.getCode a = ByteArray.empty)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    state.getCode a = ByteArray.empty ∧
      ∀ root ∈ trace.rawFrames, root.devm.getCode a = benv.state.getCode a := by
  cases trace with
  | skipped => exact ⟨hempty, fun root member => by simp only [rawFrames,
    List.not_mem_nil] at member⟩
  | called _ _ _ _ message _ _ =>
      obtain ⟨hpost, hroots⟩ := message.codeAt_empty_noStateGas hsg avoid
      exact ⟨hpost.trans hempty, hroots⟩

/-- A request stage keeps the code at `a`. -/
theorem RequestStageTrace.codeAt_noStateGas
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (hsg : benv.stat.rules.stateGas = none) {a : Adr}
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    state.getCode a = benv.state.getCode a := by
  cases trace with
  | skipped => rfl
  | called _ requests _ =>
      obtain ⟨hw, -⟩ := requests.withdrawal.codeAt_empty_noStateGas hsg (fun root member =>
        avoid root (by
          simp only [RequestStageTrace.rawFrames, RequestsTrace.rawFrames, List.mem_append]
          exact Or.inl member))
      obtain ⟨hc, -⟩ := requests.consolidation.codeAt_empty_noStateGas
        (benv := benv.withState requests.withdrawalState) hsg (fun root member =>
          avoid root (by
            simp only [RequestStageTrace.rawFrames, RequestsTrace.rawFrames, List.mem_append]
            exact Or.inr member))
      rw [requests.state_eq_consolidationState]
      exact hc.trans hw

/-- **A staged body that starts with empty code at `a` ends with it, and so
does every transaction frame it enters**, when no frame it enters targets
`a`. Either delegation is disabled or no authorization of its transactions
recovers to `a`. -/
theorem StagedBodyTrace.codeAt_empty_noStateGas
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : benv.stat.rules.stateGas = none) {a : Adr}
    (hauth : benv.stat.rules.delegationEnabled = false ∨
      ∀ p ∈ trace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hempty : benv.state.getCode a = ByteArray.empty) :
    (∀ root ∈ trace.transactions.rawFrames, root.devm.getCode a = ByteArray.empty) ∧
      state.getCode a = ByteArray.empty := by
  have avoidBeacon : ∀ root ∈ trace.beacon.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a :=
    fun root member => avoid root (by
      simp only [StagedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inl (Or.inl member)))
  have avoidHistory : ∀ root ∈ trace.history.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a :=
    fun root member => avoid root (by
      simp only [StagedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inl (Or.inr member)))
  have avoidTx : ∀ root ∈ trace.transactions.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a :=
    fun root member => avoid root (by
      simp only [StagedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inr member))
  have avoidRequests : ∀ root ∈ trace.requests.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a :=
    fun root member => avoid root (by
      simp only [StagedBodyTrace.rawFrames, List.mem_append]
      exact Or.inr member)
  obtain ⟨hbeacon, -⟩ := trace.beacon.codeAt_empty_noStateGas hsg hempty avoidBeacon
  obtain ⟨hhistory, -⟩ := trace.history.codeAt_empty_noStateGas
    (benv := benv.withState trace.beaconState) hsg hbeacon avoidHistory
  have hstart : ((benv.withState trace.beaconState).withState trace.historyState).state.getCode a =
      ByteArray.empty := by
    simpa only [Benv.withState] using hhistory
  obtain ⟨hroots, hfinalTx⟩ := trace.transactions.codeAt_empty_noStateGas
    (benv := (benv.withState trace.beaconState).withState trace.historyState)
    hsg hauth avoidTx hstart
  have txStat : trace.transactionBenv.stat = benv.stat := trace.transactions.stat_eq
  have hwithdrawal : trace.withdrawalState.getCode a = ByteArray.empty := by
    have run := trace.withdrawalsRun
    cases enabled : benv.stat.rules.header.withdrawalsRoot with
    | false =>
        rw [(trace.withdrawals_disabled enabled).1]
        exact hfinalTx
    | true =>
        simp only [withdrawalsPass, processWithdrawals, enabled, ↓reduceIte] at run
        rw [← (Prod.mk.inj run).1, processWithdrawalsState_getCode]
        exact hfinalTx
  have hrequest := trace.requests.codeAt_noStateGas
    (benv := trace.transactionBenv.withState trace.withdrawalState)
    (by change trace.transactionBenv.stat.rules.stateGas = none; rw [txStat]; exact hsg)
    avoidRequests
  refine ⟨hroots, ?_⟩
  have hreqWithdraw : trace.requestState.getCode a = ByteArray.empty :=
    hrequest.trans hwithdrawal
  rw [trace.finalState_eq, trace.rewardState_eq]
  split
  · exact hreqWithdraw
  · rw [payRewards_getCode]
    exact hreqWithdraw

/-- No authorization of any transaction of a retained `In`-history recovers
to `a`. -/
def ConfiguredHistoryTraceIn.NoAuthorityAt {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint : BlockChain} (a : Adr) :
    {future : BlockChain} → ConfiguredHistoryTraceIn F cfg checkpoint future → Prop
  | _, .refl _ _ _ => True
  | _, .step prior block =>
      prior.NoAuthorityAt a ∧
        ∀ p ∈ block.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
          recoverAuthority auth = .ok authority → authority ≠ a

/-- Every block of a retained `In`-history selects a pre-Prague fork. -/
def ConfiguredHistoryTraceIn.AllPrePrague {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint : BlockChain} :
    {future : BlockChain} → ConfiguredHistoryTraceIn F cfg checkpoint future → Prop
  | _, .refl _ _ _ => True
  | _, .step prior block => prior.AllPrePrague ∧ PrePrague block.fork

/-- **A retained `In`-block that starts with empty code at `a` ends with
it**, and so does every transaction frame it enters. Delegation is either
disabled at the block's fork (the pre-Prague arm, needing no authority
premise) or no authorization of its transactions recovers to `a`. -/
theorem ConfiguredBlockTraceIn.codeAt_empty_noStateGas
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (capabilities : BodyStageCapabilities F) {a : Adr}
    (hdis : trace.fork.ruleSet.delegationEnabled = false ∨
      ∀ p ∈ trace.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hempty : pre.state.getCode a = ByteArray.empty) :
    (∀ root ∈ trace.bodyTrace.transactions.rawFrames, root.devm.getCode a = ByteArray.empty) ∧
      post.state.getCode a = ByteArray.empty := by
  obtain ⟨hroots, hstate⟩ := trace.bodyTrace.codeAt_empty_noStateGas
    (capabilities.stateGas_none trace.forkIn) hdis avoid hempty
  refine ⟨hroots, ?_⟩
  rw [trace.postEq]
  exact hstate

/-- **A retained `In`-history that starts with empty code at `a` ends with
empty code at `a`, and so does every transaction frame it enters**, when no
frame it enters targets `a`. Per-block delegation is either disabled on a
pre-Prague fork (from the explicit per-fork hypothesis, needing no
authority premise there) or covered by the history's no-authority premise. -/
theorem ConfiguredHistoryTraceIn.codeAt_empty_noStateGas
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (hdeleg : ∀ f, F f → PrePrague f → (Fork.ruleSet f).delegationEnabled = false)
    (hauth : history.NoAuthorityAt a)
    (avoid : ∀ root ∈ history.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hempty : checkpoint.state.getCode a = ByteArray.empty) :
    (∀ root ∈ history.txRawFrames, root.devm.getCode a = ByteArray.empty) ∧
      future.state.getCode a = ByteArray.empty := by
  induction history with
  | refl => exact ⟨fun root member => by simp only [txRawFrames, List.not_mem_nil] at member,
      hempty⟩
  | step prior block ih =>
      obtain ⟨hroots, hstate⟩ := ih hauth.1
        (fun root member => avoid root (by
          simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append]
          exact Or.inl member))
      have hdis : block.fork.ruleSet.delegationEnabled = false ∨
          ∀ p ∈ block.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
            recoverAuthority auth = .ok authority → authority ≠ a := by
        by_cases hpre : PrePrague block.fork
        · exact Or.inl (hdeleg _ block.forkIn hpre)
        · exact Or.inr hauth.2
      obtain ⟨hroots', hfinal⟩ := block.codeAt_empty_noStateGas capabilities hdis
        (fun root member => avoid root (by
          simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append]
          exact Or.inr member)) hstate
      refine ⟨fun root member => ?_, hfinal⟩
      simp only [ConfiguredHistoryTraceIn.txRawFrames, List.mem_append] at member
      rcases member with member | member
      · exact hroots root member
      · exact hroots' root member

/-- **A fully pre-Prague historical `In`-history keeps empty code at `a`
with no authority premise**: delegation is disabled on every block, so no
authorization can install a delegation designator anywhere. -/
theorem ConfiguredHistoryTraceIn.codeAt_empty_prePrague
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (capabilities : BodyStageCapabilities HistFork)
    (hpre : history.AllPrePrague)
    (avoid : ∀ root ∈ history.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hempty : checkpoint.state.getCode a = ByteArray.empty) :
    (∀ root ∈ history.txRawFrames, root.devm.getCode a = ByteArray.empty) ∧
      future.state.getCode a = ByteArray.empty := by
  induction history with
  | refl => exact ⟨fun root member => by simp only [txRawFrames, List.not_mem_nil] at member,
      hempty⟩
  | step prior block ih =>
      obtain ⟨hroots, hstate⟩ := ih hpre.1
        (fun root member => avoid root (by
          simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append]
          exact Or.inl member))
      have hdis : block.fork.ruleSet.delegationEnabled = false ∨
          ∀ p ∈ block.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
            recoverAuthority auth = .ok authority → authority ≠ a :=
        Or.inl (block.forkIn.delegationDisabled_of_prePrague hpre.2)
      obtain ⟨hroots', hfinal⟩ := block.codeAt_empty_noStateGas capabilities hdis
        (fun root member => avoid root (by
          simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append]
          exact Or.inr member)) hstate
      refine ⟨fun root member => ?_, hfinal⟩
      simp only [ConfiguredHistoryTraceIn.txRawFrames, List.mem_append] at member
      rcases member with member | member
      · exact hroots root member
      · exact hroots' root member

end ExecutionTrace

end Blanc
