import Blanc.Lift.Weth9.CommittedHistory
import Blanc.Lift.Weth9.DeployHistory
import Blanc.Lift.HistCursorReturn
import Blanc.ExecutionModelAccountingIn
import Blanc.ExecutionAccountingHistoryIn

/-!
# WETH9 committed history over a selected fork domain

The counterpart of `weth9_history_committed` (`CommittedHistory.lean`) for a configured history
`ConfiguredHistoryTraceIn F` whose forks have no state gas, with the body-stage capabilities:

* `depositCall_effectH`, `weth9_frame_effectH` — the frame effects with no fork argument (the
  modern bodies read the fork only through `Weth9.deposit_effect`, whose body never reads it);
* `weth9_exec_nodeIn`, `weth9_spawnKindsIn`, `weth9_spawnReplayIn` — the spawn obligations from
  `stateGas = none` (`reach_of_parentPrefix_noStateGas`, `cursor_stepS_noStateGas`,
  `CursorOK.sourceRunReturnH`, `noExec_after_of_cursorH`, `lift_sound_in_noStateGas`);
* `weth9AccountingLadderIn` (`modelLadderIn`) and `weth9_history_committedIn`, with its
  `HistFork` instance `weth9_history_committedHist`;
* `weth9_history_committed_from_byzantium_deployment` — from the Byzantium deployment output.
-/

namespace Blanc.Lift.Weth9

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- `depositCall_effect` with no fork argument. -/
theorem depositCall_effectH {sevm : Sevm} {d : Devm}
    {o : Outcome} {a b : Bytes} {ha : a.length ≤ 32} {hb : b.length ≤ 32} {f : SFunc}
    (hf : f.silent = true) (hrefs : f.refs.all (· ∈ ([] : List Nat)) = true)
    (run : SFunc.Run prog sevm d (.dest (chain [.push a ha, .push b hb] (.callNext 1 f))) o) :
    Devm.getStor (Outcome.devm o) sevm.currentTarget =
        (Devm.getStor d sevm.currentTarget).set (balSlot sevm.caller)
          ((Devm.getStor d sevm.currentTarget).get (balSlot sevm.caller) + sevm.value) ∧
      (Outcome.devm o).getBal = d.getBal := by
  cases run with
  | dest burn run1 =>
  obtain ⟨d1, hl, run2⟩ := run_chain_prefix [.push a ha, .push b hb] [] run1
  have s01 : Same d d1 := Same.trans (Same.of_state burn.state)
    ⟨Line.of_inv Devm.getStor (by line_inv) hl, Line.of_inv Devm.getBal (by line_inv) hl⟩
  change SFunc.Run prog sevm d1 (.callNext 1 f) o at run2
  cases run2 with
  | callHalt dd lookup pop crun =>
    have s02 := s01.trans (Same.of_state pop.state)
    obtain ⟨hs, hbal⟩ := Weth9.deposit_effectH lookup crun
    exact ⟨by rw [hs, ← s02.1], by rw [hbal, ← s02.2]⟩
  | callRet dd lookup pop crun tail =>
    have s02 := s01.trans (Same.of_state pop.state)
    obtain ⟨hs, hbal⟩ := Weth9.deposit_effectH lookup crun
    have hst := SFunc.Run.state_of_silent silentSet_nil hf hrefs tail
    have s2o := Same.of_state hst.symm
    simp only [Outcome.devm] at hs hbal
    exact ⟨by rw [← s2o.1, hs, ← s02.1], by rw [← s2o.2, hbal, ← s02.2]⟩

/-- `weth9_frame_effect` with no fork argument. -/
theorem weth9_frame_effectH {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {sevm : Sevm} {pre post : Devm}
    (hrun : SProg.RunP P prog sevm pre post) :
    (decodeCall sevm = none ∧
      Devm.getStor post sevm.currentTarget = Devm.getStor pre sevm.currentTarget) ∨
    (∃ c, decodeCall sevm = some c ∧ (∀ who w, c ≠ .withdraw who w) ∧
      c.stor (Devm.getStor pre sevm.currentTarget) = some (Devm.getStor post sevm.currentTarget)) ∨
    (∃ who w, decodeCall sevm = some (.withdraw who w) ∧ ∃ s sf : Devm, P sevm s (.exec .call) sf) := by
  rcases weth9_route hP hrun with ⟨hmiss, d', hs, run⟩ | ⟨l, hl, hshort, hsel, g, d', hg, hs, run⟩
  · right; left
    refine ⟨_, decode_miss hmiss, (fun _ _ h => by cases h), ?_⟩
    rw [tree_00af] at run
    obtain ⟨hst, -⟩ := depositCall_effectH (f := t_00b7_c0) (by decide) (by decide)
      (run.mono hP)
    simp only [Outcome.devm] at hst
    simp only [Call.stor]
    rw [hst, hs.stor]
  · rcases decode_hit hshort hl hsel with ⟨hk, hd⟩ | ⟨hk, hd⟩ | ⟨hk, hd⟩ | ⟨hk, hd⟩ | ⟨hk, hd⟩ |
        ⟨hk, hd⟩
    · left
      refine ⟨hd, ?_⟩
      have h := viewWrapper_state hP hk hg run
      simp only [Outcome.devm] at h
      exact (getStor_eq_of_state_eq h sevm.currentTarget).trans (congrFun hs.stor.symm _)
    · right; right
      refine ⟨_, _, hd, ?_⟩
      rw [hk] at hg
      have hg' : g = t_0243_c24 := Option.some.inj (hg.symm.trans wrapper24_lookup)
      subst hg'
      exact wrapper24_hasCall hP run
    · right; left
      refine ⟨_, hd, (fun _ _ h => by cases h), ?_⟩
      rw [hk] at hg
      have hok := (Weth9.transfer_wrapper_okX hg (run.mono hP)).of_same ⟨hs.stor, hs.bal⟩
      have := xferStorStep_of_okX hok
      simp only [Outcome.devm, toAdr_toB256] at this
      simpa only [Call.stor] using this
    · right; left
      refine ⟨_, hd, (fun _ _ h => by cases h), ?_⟩
      rw [hk] at hg
      have hok := (Weth9.transferFrom_wrapper_okX hg (run.mono hP)).of_same ⟨hs.stor, hs.bal⟩
      have := xferStorStep_of_okX hok
      simp only [Outcome.devm, toAdr_toB256] at this
      simpa only [Call.stor] using this
    · right; left
      refine ⟨_, hd, (fun _ _ h => by cases h), ?_⟩
      rw [hk] at hg
      obtain ⟨-, hst⟩ := approve_wrapper_ok hg (run.mono hP)
      simp only [Outcome.devm] at hst
      simp only [Call.stor]
      rw [hst, hs.stor]
    · right; left
      refine ⟨_, hd, (fun _ _ h => by cases h), ?_⟩
      rw [hk] at hg
      have hg' : g = t_03ca_c19 := by simpa only [prog, Cert.prog, cert, List.map_cons,
        List.map_nil, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT,
        getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Option.some.injEq] using
        hg.symm
      subst hg'
      rw [tree_03ca] at run
      obtain ⟨hst, -⟩ := depositCall_effectH (f := t_03d2_c19) (by decide) (by decide)
        (run.mono hP)
      simp only [Outcome.devm] at hst
      simp only [Call.stor]
      rw [hst, hs.stor]

/-- `weth9_exec_node` from `stateGas = none`: a chain node that decodes an external instruction is
the `withdraw` `CALL`, after the debit, followed only by the silent return. -/
theorem weth9_exec_nodeIn {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hsg : sevm.benvStat.rules.stateGas = none)
    {N : Exec.Deriv} (hN : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N)
    (hat : ∃ x, Ninst.At N.sevm.code N.pc (.exec x)) :
    decodeCall sevm = some (.withdraw sevm.caller (Sevm.dataWord sevm 4)) ∧
    Sevm.dataWord sevm 4 ≤ (Devm.getStor pre sevm.currentTarget).get (balSlot sevm.caller) ∧
    Devm.getStor N.devm sevm.currentTarget =
      (Devm.getStor pre sevm.currentTarget).set (balSlot sevm.caller)
        ((Devm.getStor pre sevm.currentTarget).get (balSlot sevm.caller) - Sevm.dataWord sevm 4) ∧
    ∀ N', Exec.Deriv.ParentStep N' N →
      Devm.getStor post = Devm.getStor N'.devm ∧
      ∀ M, Exec.Deriv.ParentPrefix N' M → ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y) := by
  obtain ⟨x, hx⟩ := hat
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix_noStateGas cert_check
    (R := ⟨0, sevm, pre, .ok post, run⟩) rfl hcode hsg hN
  obtain ⟨g, hf, -⟩ := ok.tree_of_exec hx
  have hT : AtExec (κ.conf N.devm) := ⟨x, g, hf⟩
  change Reach (StepIn ⟨0, sevm, pre, .ok post, run⟩) prog sevm ⟨pre, t_0000_c0, []⟩
    (κ.conf N.devm) at reach
  obtain ⟨hshort, hsel, d10, gw, cw, ys, hTeq, hle, hstor, -⟩ :=
    weth9_withdraw_reach StepIn.toRun reach hT
  have hdec := decode_of_withdraw_selector hshort hsel
  have hNd : N.devm = d10 := congrArg Conf.d hTeq
  have hκf : κ.f = .next (.exec .call) afterCall := congrArg Conf.f hTeq
  have hκK : κ.K.map Cont.f = [t_0264_c24] := congrArg Conf.K hTeq
  refine ⟨hdec, hle, by rw [hNd]; exact hstor, ?_⟩
  intro N' edge
  have hsevmN : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq hN
  have hforkN : N.sevm.benvStat.rules.stateGas = none := by rw [hsevmN]; exact hsg
  obtain ⟨κ₁, hs, -, ok₁⟩ := cursor_stepS_noStateGas cert_check ok edge hforkN
  obtain ⟨f, pc, a, m, K⟩ := κ
  dsimp only at hκf hκK
  subst hκf
  cases hs with
  | next habs =>
    have hchain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N' := hN.snoc edge
    refine ⟨?_, ?_⟩
    · -- The suffix after the `CALL` (`afterCall`, then its one continuation `t_0264_c24`) is
      -- state-silent with a non-`SELFDESTRUCT` terminal, so the frame's post world is `N'`'s.
      have hsevmN' : N'.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq hchain
      have hforkN' : N'.sevm.benvStat.rules.stateGas = none := by rw [hsevmN']; exact hsg
      have success : N'.exn = .ok post := Exec.Deriv.ParentPrefix.exn_eq hchain
      have hS : SilentSet prog [] = true := rfl
      have hstate : post.state = N'.devm.state := by
        rcases ok₁.sourceRunReturnH cert_check success hforkN' with halted |
            ⟨cont, tail, state, run', hK, -, -, returned, okC⟩
        · exact SFunc.RunP.state_of_silent StepIn.toRun hS (f := afterCall) (by decide)
            (by decide) halted
        · have h1 : state.state = N'.devm.state :=
            SFunc.RunP.state_of_silent StepIn.toRun hS (f := afterCall) (by decide) (by decide)
              returned
          have hK' : K = cont :: tail := hK
          rw [hK'] at hκK
          simp only [List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at hκK
          obtain ⟨hcf, rfl⟩ := hκK
          have hforkC : N'.sevm.benvStat.rules.stateGas = none := hforkN'
          rcases okC.sourceRunReturnH cert_check rfl hforkC with halted2 |
              ⟨cont2, tail2, -, -, hK2, -⟩
          · have h2 := SFunc.RunP.state_of_silent StepIn.toRun hS (f := t_0264_c24)
              (by decide) (by decide) (hcf ▸ halted2)
            exact h2.trans h1
          · exact absurd hK2 (by simp only [reduceCtorEq, not_false_eq_true])
      exact funext fun a => getStor_eq_of_state_eq hstate a
    · intro M hM y
      exact noExec_after_of_cursorH cert_check hchain hM hsg ok₁ (E := []) rfl
        (by exact afterCall_execFree)
        (by
          simp only [hκK, List.mem_singleton, forall_eq]
          decide) y

/-- **The replay of a successful non-static WETH9 target frame over a selected fork domain**
without state gas (`weth9_spawnReplay` with `SpawnReplayIn F`). -/
theorem weth9_spawnReplayIn (F : Fork → Prop)
    (hsgF : ∀ {f : Fork}, F f → (Fork.ruleSet f).stateGas = none) (ca : Adr) {U : Key → Prop}
    (hinj : KeyInj U) :
    Exec.CoreAccountingIn.SpawnReplayIn F ca (footSpec U).sem (footEntry U) (wethCarrier ca U)
      (wethObservation ca U) := by
  intro sevm pre post run committed hrun target fork installed admitted bound hstatic
  have hsg : sevm.benvStat.rules.stateGas = none := hsgF fork
  have hkeys : ∀ k ∈ frameKeys sevm, U k := admitted.root target
  have hin := lift_sound_in_noStateGas cert_check hrun.1 hsg run
  have self : committedFrameInvocations ca (Exec.Frame.ofRun run committed) =
      if (decodeCall sevm).isSome = true then [⟨sevm, pre, post⟩] else [] := by
    show (if sevm.currentTarget = ca ∧ sevm.isStatic = false ∧ (decodeCall sevm).isSome = true then
        [frameInvocation (Exec.Frame.ofRun run committed)] else []) = _
    by_cases h : (decodeCall sevm).isSome = true
    · simp only [target, hstatic, h, and_self, ↓reduceIte]
      rfl
    · have h' : (decodeCall sevm).isSome = false := by simpa only [Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none, Bool.not_eq_true] using h
      simp only [h', Bool.false_eq_true, and_false, ↓reduceIte]
  refine ⟨if (decodeCall sevm).isSome = true then [⟨sevm, pre, post⟩] else [], ?_, ?_, ?_⟩
  · show _ = committedFrameInvocations ca (Exec.Frame.ofRun run committed)
    rw [self]
    rfl
  · intro hnone
    subst target
    show LedgerReplay (ledger U (Devm.getStor pre sevm.currentTarget))
      (if (decodeCall sevm).isSome = true then [⟨sevm, pre, post⟩] else [])
      (ledger U (Devm.getStor post sevm.currentTarget))
    rcases weth9_frame_effectH StepIn.toRun hin with ⟨hd, hst⟩ | ⟨c, hd, hnw, hstor⟩ |
        ⟨who, w, hd, -⟩
    · simp only [hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      rw [hst]
      exact LedgerReplay.nil _
    · simp only [hd, Option.isSome_some, ↓reduceIte]
      exact replay_one hinj hkeys hd hstor
    · obtain ⟨d10, sf, hstorc, hcode10, hstep, hstate⟩ :=
        weth9_withdraw_frame StepIn.toRun hin ⟨who, w, hd⟩
      have hdesc : Exec.rawFrameDescendants run = [] :=
        Exec.rawFrameDescendants_eq_nil_of_noExec run hnone
      have hne : (pre.getCode sevm.currentTarget).toList ≠ [] :=
        (footSpec U).sem.ne_nil installed.1.symm
      have htol : (State.getCode d10.state sevm.currentTarget).toList ≠ [] := by
        show (d10.getCode sevm.currentTarget).toList ≠ []
        rw [hcode10]
        exact hne
      have hprot : State.Protected d10.state sevm.currentTarget :=
        State.Protected.of_code_ne_nil htol
      have hsf : Devm.getStor sf sevm.currentTarget = Devm.getStor d10 sevm.currentTarget :=
        StepIn.exec_getStor_eq_of_noDescendants (R := ⟨0, sevm, pre, .ok post, run⟩) hdesc hstep _ hprot
      have hpost : Devm.getStor post sevm.currentTarget = Devm.getStor d10 sevm.currentTarget :=
        (getStor_eq_of_state_eq hstate sevm.currentTarget).trans hsf
      obtain ⟨rfl, rfl⟩ := decodeCall_withdraw_inv hd
      simp only [hd, Option.isSome_some, ↓reduceIte]
      rw [hpost]
      exact replay_one hinj hkeys hd hstorc
  · subst target
    intro N hN x hx
    obtain ⟨hdec, hle, hstor, hafter⟩ := weth9_exec_nodeIn run hrun.1 hsg hN ⟨x, hx⟩
    refine ⟨?_, fun N' edge => ?_⟩
    · show LedgerReplay (ledger U (Devm.getStor pre sevm.currentTarget))
        (if (decodeCall sevm).isSome = true then [⟨sevm, pre, post⟩] else [])
        (ledger U (Devm.getStor N.devm sevm.currentTarget))
      simp only [hdec, Option.isSome_some, ↓reduceIte]
      exact replay_one hinj hkeys hdec (withdraw_stor_of_debit hle hstor)
    · obtain ⟨hpost, hnoexec⟩ := hafter N' edge
      refine ⟨?_, hnoexec⟩
      show LedgerReplay (ledger U (Devm.getStor N'.devm sevm.currentTarget)) []
        (ledger U (Devm.getStor post sevm.currentTarget))
      rw [hpost]
      exact LedgerReplay.nil _

/-- WETH9 frames spawn only by `CALL`/`STATICCALL` over a domain without state gas. -/
theorem weth9_spawnKindsIn (F : Fork → Prop)
    (hsgF : ∀ {f : Fork}, F f → (Fork.ruleSet f).stateGas = none) (ca : Adr) :
    SpawnKindsIn F ca weth9Sem := by
  intro sevm pre post run hrun _ fork _ node chain x hat
  obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix_noStateGas cert_check
    (F := ⟨0, sevm, pre, .ok post, run⟩) rfl hrun.1 (hsgF fork) chain
  exact ok.exec_call_or_staticcall (Cursor.callOnly_of_reach cert_callOnly reach) hat

/-- **The accounting ladder of the WETH9 ledger replay over a selected fork domain** without
state gas, over a tracked universe `U` with injective slots. -/
noncomputable def weth9AccountingLadderIn (F : Fork → Prop)
    (hsgF : ∀ {f : Fork}, F f → (Fork.ruleSet f).stateGas = none) (ca : Adr) {U : Key → Prop}
    (hinj : KeyInj U) : AccountingLadderAdmittedIn F (footSpec U) ca (footEntry U) :=
  modelLadderIn (c := footSpec U) (wethCarrier ca U) (wethObservation ca U) LedgerReplay.append
    (fun _ _ => ()) (fun _ _ => ()) (fun _ _ => rfl)
    (fun {_ _} h => ledger_congr_get h)
    (fun _ hf => committedFrameInvocations_static hf)
    (fun _ hf => committedFrameInvocations_foreign hf) hsgF
    (weth9_spawnKindsIn F hsgF ca) (weth9_spawnReplayIn F hsgF ca hinj)
    (footSpec_preservesAdmittedIn F hsgF ca hinj)

/-- The settlement-committed WETH9 writer invocations at the contract of a selected-domain
history, in trace order. -/
def committedInvocationsIn {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (ca : Adr) (trace : ConfiguredHistoryTraceIn F cfg checkpoint future) : List Invocation :=
  trace.settledFrames.flatMap (committedFrameInvocations ca)

/-- **The WETH9 model replays the committed chain over a selected fork domain.** The statement of
`weth9_history_committed` for a `ConfiguredHistoryTraceIn F` history whose forks have no state gas
(`BodyStageCapabilities F`): from one initial footprint `K₀` and the trace-local freshness of the
touched keys, the code stays installed, the ether does not overflow, the future storage carries
the footprint over `K₀ ∪ touched`, the future footprint ledger is the model run over exactly the
settlement-committed writer invocations at the contract in trace order, and the model run with the
contract's ether is backed. -/
theorem weth9_history_committedIn {F : Fork → Prop} (capabilities : BodyStageCapabilities F)
    {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {K₀ : Key → Prop}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = weth9Sem.image)
    (sumNof : SumNof checkpoint.state.bal)
    (initial : FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca))
    (fresh : KeysFresh K₀ (historyTouchedKeysIn ca trace)) :
    some (future.state.getCode ca).toList = weth9Sem.image ∧ SumNof future.state.bal ∧
      FootInv (historyKeyUniverseIn ca trace K₀) (future.state.getStor ca)
        (future.state.bal ca) ∧
      (ledger K₀ (checkpoint.state.getStor ca)).run
          (replayCalls (committedInvocationsIn ca trace)) =
        some (ledger (historyKeyUniverseIn ca trace K₀) (future.state.getStor ca)) ∧
      ∃ s : State,
        (State.mk (ledger K₀ (checkpoint.state.getStor ca)) (checkpoint.state.bal ca).toNat).run
            (replayCalls (committedInvocationsIn ca trace)) = some s ∧
          s.ledger = ledger (historyKeyUniverseIn ca trace K₀) (future.state.getStor ca) ∧
          s.Backed := by
  let U := historyKeyUniverseIn ca trace K₀
  have extended : FootInv U (checkpoint.state.getStor ca) (checkpoint.state.bal ca) :=
    initial.extend fresh
  have admitted : trace.FrameAdmitted ca (footEntry U) := by
    apply (trace.frameAdmitted_iff_rawFrames ca _).2
    intro root member target k hk
    exact Or.inr (List.mem_flatMap.mpr ⟨root, member, by simpa only [target, ite_true] using hk⟩)
  have start : (footSpec U).StateInv ca checkpoint.state :=
    footSpec_stateInv_iff.mpr ⟨installed, sumNof, extended.support, extended.backed⟩
  have rewards := trace.rewardCreditsFunded capabilities
  have finish := trace.stateInv_admitted_semIn
    (footSpec_preservesAdmittedIn F capabilities.stateGas_none ca extended.inj)
    capabilities admitted rewards start installedCert rfl
  obtain ⟨hcode, hside, hsup, hback⟩ := footSpec_stateInv_iff.mp finish
  obtain ⟨steps, replay, observed⟩ :=
    (weth9AccountingLadderIn F capabilities.stateGas_none ca extended.inj).configuredHistoryIn
      trace admitted capabilities rewards start installedCert rfl
  change LedgerReplay (ledger U (checkpoint.state.getStor ca)) steps
    (ledger U (future.state.getStor ca)) at replay
  change steps = trace.settledFrames.flatMap (committedFrameInvocations ca) at observed
  have hsteps : steps = committedInvocationsIn ca trace := observed
  subst hsteps
  have hrun : (ledger K₀ (checkpoint.state.getStor ca)).run
      (replayCalls (committedInvocationsIn ca trace)) =
        some (ledger U (future.state.getStor ca)) := by
    have := replay
    unfold LedgerReplay at this
    have hext : ledger U (checkpoint.state.getStor ca) = ledger K₀ (checkpoint.state.getStor ca) :=
      ledger_extend initial fresh
    rw [hext] at this
    exact this
  refine ⟨hcode, hside, ⟨hsup, extended.inj, extended.apart, hback⟩, hrun, ?_⟩
  have hmodel := State.run_ledger
    (State.mk (ledger K₀ (checkpoint.state.getStor ca)) (checkpoint.state.bal ca).toNat)
    (replayCalls (committedInvocationsIn ca trace))
  simp only [hrun] at hmodel
  cases hs : (State.mk (ledger K₀ (checkpoint.state.getStor ca))
      (checkpoint.state.bal ca).toNat).run (replayCalls (committedInvocationsIn ca trace)) with
  | none => rw [hs] at hmodel; cases hmodel
  | some s =>
    rw [hs] at hmodel
    simp only [Option.map_some, Option.some.injEq] at hmodel
    refine ⟨s, rfl, hmodel, ?_⟩
    exact State.run_backed (s := ⟨ledger K₀ (checkpoint.state.getStor ca),
      (checkpoint.state.bal ca).toNat⟩) initial.backed hs

/-- `weth9_history_committedIn` on the historical domain `HistFork`. -/
theorem weth9_history_committedHist {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : Key → Prop}
    (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = weth9Sem.image)
    (sumNof : SumNof checkpoint.state.bal)
    (initial : FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca))
    (fresh : KeysFresh K₀ (historyTouchedKeysIn ca trace)) :
    some (future.state.getCode ca).toList = weth9Sem.image ∧ SumNof future.state.bal ∧
      FootInv (historyKeyUniverseIn ca trace K₀) (future.state.getStor ca)
        (future.state.bal ca) ∧
      (ledger K₀ (checkpoint.state.getStor ca)).run
          (replayCalls (committedInvocationsIn ca trace)) =
        some (ledger (historyKeyUniverseIn ca trace K₀) (future.state.getStor ca)) ∧
      ∃ s : State,
        (State.mk (ledger K₀ (checkpoint.state.getStor ca)) (checkpoint.state.bal ca).toNat).run
            (replayCalls (committedInvocationsIn ca trace)) = some s ∧
          s.ledger = ledger (historyKeyUniverseIn ca trace K₀) (future.state.getStor ca) ∧
          s.Backed :=
  weth9_history_committedIn BodyStageCapabilities.historical trace installed sumNof initial fresh

/-- **WETH9 committed history from its Byzantium deployment.** The recorded creation input, run as
a CREATE message under Byzantium rules, succeeds with a post-state `post` whose WETH9 storage
carries the empty footprint; from any checkpoint whose WETH9 account carries `post`'s code and
storage and whose balances sum below the word bound, every `HistFork` history with trace-local
freshness of its touched keys keeps the runtime installed and `SumNof`, carries the footprint over
the touched keys, and its future footprint ledger is the model run, from the deployed ledger, of
exactly the settlement-committed writer invocations at WETH9, backed by the contract's ether. -/
theorem weth9_history_committed_from_byzantium_deployment :
    ∃ post, processCreateMessage (Creation.deployMsg.withFork .byzantium) = .ok post ∧
      (post.getCode Creation.weth9Address).toList = code.toList ∧
      ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
        (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future),
        checkpoint.state.getCode Creation.weth9Address = post.getCode Creation.weth9Address →
        checkpoint.state.getStor Creation.weth9Address =
          Devm.getStor post Creation.weth9Address →
        SumNof checkpoint.state.bal →
        KeysFresh (fun _ => False) (historyTouchedKeysIn Creation.weth9Address trace) →
        some (future.state.getCode Creation.weth9Address).toList = weth9Sem.image ∧
          SumNof future.state.bal ∧
          FootInv (historyKeyUniverseIn Creation.weth9Address trace (fun _ => False))
            (future.state.getStor Creation.weth9Address)
            (future.state.bal Creation.weth9Address) ∧
          (ledger (fun _ => False) (Devm.getStor post Creation.weth9Address)).run
              (replayCalls (committedInvocationsIn Creation.weth9Address trace)) =
            some (ledger (historyKeyUniverseIn Creation.weth9Address trace (fun _ => False))
              (future.state.getStor Creation.weth9Address)) ∧
          ∃ s : State,
            (State.mk (ledger (fun _ => False) (Devm.getStor post Creation.weth9Address))
                (checkpoint.state.bal Creation.weth9Address).toNat).run
                (replayCalls (committedInvocationsIn Creation.weth9Address trace)) = some s ∧
              s.ledger = ledger (historyKeyUniverseIn Creation.weth9Address trace (fun _ => False))
                (future.state.getStor Creation.weth9Address) ∧
              s.Backed := by
  obtain ⟨-, post, hpost, hcode, hfoot⟩ := Creation.weth9_deploy_init_byzantium
  refine ⟨post, hpost, hcode, ?_⟩
  intro cfg checkpoint future trace hc hs hsum fresh
  have committed := weth9_history_committedHist trace (K₀ := fun _ => False) ?_ hsum ?_ fresh
  · rw [hs] at committed
    exact committed
  · show some _ = some code.toList
    rw [hc, hcode]
  · rw [hs]
    exact hfoot _

end Blanc.Lift.Weth9
