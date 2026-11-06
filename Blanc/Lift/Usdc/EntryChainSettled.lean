import Blanc.Lift.Usdc.EntryChainRoots
import Blanc.Lift.Usdc.ProxySafeFrames
import Blanc.ExecutionRetainedDeletionSafety

/-!
# USDC's certification read at settled frames only

`CertifiedSettled`: the implementation word is certified at each settled proxy frame whose caller is not the
admin word. It speaks of committed frames, so it is what a scan of retained `Upgraded` logs can check.
A reverted upgrade to anything is not in it. From it, every committed frame at `T` runs one of USDC's codes
(`committed_context`), so no settled root schedules `T`'s deletion (`usdc_outputNotDeleted`), and the chain
holds with no premise about raw frames (`usdc_viewSettled_certified`).
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- **The proxy admin's power, read at the settled frames that consult the word.** -/
def CertifiedSettled (T : Adr) (settled : List Exec.Frame) : Prop :=
  ∀ G ∈ settled, G.sevm.currentTarget = T → G.sevm.code = Proxy.code →
    G.sevm.caller ≠ adminOf G.pre.state T → UsdcCertified G.pre T

/-- What a frame at `T` runs, with the library when it needs it. -/
def ContextAt (T : Adr) (sevm : Sevm) (pre : Devm) : Prop :=
  sevm.currentTarget = T →
    (sevm.code = Proxy.code ∨ CurveCoins.UsdcVersion sevm.code ∨ sevm.code = Lib.code) ∧
      (sevm.code = Impl.code → pre.state.getCode usdcLib = Lib.code)

theorem v2_kinds : ∀ f ∈ ImplV2.cert.prog, f.execsSatisfy (fun x => x == .call || x == .staticcall) = true := by
  decide +kernel

theorem v2_1_kinds : ∀ f ∈ ImplV2_1.cert.prog,
    f.execsSatisfy (fun x => x == .call || x == .staticcall) = true := by
  decide +kernel

theorem direct_of_kind {x : Xinst} (h : (x == .call || x == .staticcall) = true) :
    x = .call ∨ x = .staticcall := by
  cases x <;> first | exact .inl rfl | exact .inr rfl | cases h

variable {T : Adr}

/-- A spawn's child at `T` runs what `ContextAt` allows. -/
theorem child_context {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (fork : HistFork sevm.benvStat.fork) (proxyCode : pre.state.getCode T = Proxy.code)
    (context : ContextAt T sevm pre)
    (certified : sevm.currentTarget = T → sevm.code = Proxy.code →
      sevm.caller ≠ adminOf pre.state T → UsdcCertified pre T)
    {N : Exec.Deriv} (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N)
    {f : Frame} {rsm : Resume} {pc' : Nat} {cevm : Evm}
    (step : Evm.step ⟨N.pc, N.sevm, N.devm⟩ = .spawn f rsm pc') (enter : f.enter = .run cevm) :
    ContextAt T cevm.sta cevm.dyna := by
  intro childTarget
  have hsg := fork.stateGas_none
  have sevmEq : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  have proxyNe : (pre.getCode T).toList ≠ [] := by
    change (pre.state.getCode T).toList ≠ []
    rw [proxyCode]
    exact proxy_toList_ne_nil
  have nodeCode : N.devm.getCode T = Proxy.code :=
    ((Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain).2 T proxyNe).trans proxyCode
  obtain ⟨x, hat, spawn, -⟩ := Evm.step_spawn_inv step
  obtain ⟨pcZero, getCode, actual⟩ := Blanc.Evm.step_spawn_child step enter
  obtain ⟨benv, -, hcevm⟩ := Frame.enter_run_inv enter
  have frameTarget : f.inner.currentTarget = T := by rw [hcevm] at childTarget; exact childTarget
  have frameCode : cevm.sta.code = f.inner.code := Frame.enter_run_code enter
  have proxyResult : f.inner.code = Proxy.code →
      (cevm.sta.code = Proxy.code ∨ CurveCoins.UsdcVersion cevm.sta.code ∨ cevm.sta.code = Lib.code) ∧
        (cevm.sta.code = Impl.code → cevm.dyna.state.getCode usdcLib = Lib.code) := fun h =>
    ⟨.inl (frameCode.trans h), fun hi => (proxy_ne_impl (h.symm.trans (frameCode.symm.trans hi))).elim⟩
  have direct : x = .call ∨ x = .staticcall → f.inner.code = Proxy.code := fun d => by
    rw [Xinst.step_directCall_spawn_code d spawn (by rw [frameTarget, nodeCode]; exact proxy_not_delegation),
      frameTarget, nodeCode]
  by_cases parent : sevm.currentTarget = T
  · obtain ⟨codes, libClause⟩ := context parent
    rcases codes with hc | version | hc
    · -- the proxy
      obtain ⟨g, K, ⟨rfl, delegated⟩ | ⟨rfl, -⟩⟩ := Proxy.proxy_nodeH run hc hsg fork.bal_none chain hat
      · have notAdmin : sevm.caller ≠ adminOf pre.state T := by
          rw [← parent]
          exact delegated.1
        have cert := certified parent hc notAdmin
        obtain ⟨_, b, gas, S, M, G, tail, state, tree, input⟩ := delegated
        change N.devm = _ at input
        have nodeState : N.devm.state = pre.state := by rw [input]; exact state
        have nodeGetCode : ∀ a, N.devm.getCode a = pre.getCode a := fun a => by
          simp only [Devm.getCode, Devm.getAcct, nodeState]
        have version : CurveCoins.UsdcVersion (pre.getCode (pre.getStorVal T implSlot).toAdr) := cert.1
        have shape := step_delegatecall_spawn_shapeH (sevmEq ▸ hsg) spawn (by rw [input]; rfl)
          (by rw [nodeGetCode, parent]; exact version_undelegated version)
        have code : f.inner.code = pre.getCode (pre.getStorVal T implSlot).toAdr := by
          rw [shape.2.2.2.2.2, nodeGetCode, parent]
        refine ⟨.inr (.inl (by rw [frameCode, code]; exact version)), fun hi => ?_⟩
        have := cert.2 (code.symm.trans (frameCode.symm.trans hi))
        change cevm.dyna.getCode usdcLib = _
        rw [getCode, nodeGetCode]
        exact this
      · exact proxyResult (direct (.inl rfl))
    · rcases version with hc | hc | hc
      · obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix_noStateGas ImplV2.cert_check
          (F := ⟨0, sevm, pre, out, run⟩) rfl hc hsg chain
        exact proxyResult (direct (direct_of_kind
          (ok.execsSatisfy (Cursor.execsSatisfy_of_reachable v2_kinds reach) hat)))
      · obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix_noStateGas ImplV2_1.cert_check
          (F := ⟨0, sevm, pre, out, run⟩) rfl hc hsg chain
        exact proxyResult (direct (direct_of_kind
          (ok.execsSatisfy (Cursor.execsSatisfy_of_reachable v2_1_kinds reach) hat)))
      · obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix_noStateGas certL_check
          (F := ⟨0, sevm, pre, out, run⟩) rfl hc hsg chain
        have kind := ok.execsSatisfy (Cursor.execsSatisfy_of_reachable impl_kinds reach) hat
        cases x with
        | call => exact proxyResult (direct (.inl rfl))
        | delegatecall =>
            have lib := impl_delegate_lib run hc hsg (libClause hc) chain hat spawn
            exact ⟨.inr (.inr (frameCode.trans lib)), fun hi =>
              (lib_ne_impl (lib.symm.trans (frameCode.symm.trans hi))).elim⟩
        | _ => simp only [implKinds, reduceCtorEq, beq_iff_eq, Bool.or_eq_true, or_self] at kind
    · obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix_noStateGas Lib.cert_check
        (F := ⟨0, sevm, pre, out, run⟩) rfl hc hsg chain
      exact proxyResult (direct (.inr (isStaticcall_eq
        (ok.execsSatisfy (Cursor.execsSatisfy_of_reachable lib_staticOnly reach) hat))))
  · -- a foreign parent reaches `T` only by entering its code
    have away : N.sevm.currentTarget ≠ cevm.sta.currentTarget := by
      rw [sevmEq, childTarget]
      exact parent
    have code := actual away
      (by rw [childTarget, nodeCode]; exact fun e => proxy_toList_ne_nil (by rw [e]; exact ByteArray.toList_empty))
      (by rw [childTarget, nodeCode]; exact proxy_not_delegation)
    rw [childTarget, nodeCode] at code
    exact proxyResult (frameCode.symm.trans code)

/-- **Every committed frame at `T` runs one of USDC's codes.** -/
theorem committed_context (n : Nat) : ∀ {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out), sevm.depth < n → HistFork sevm.benvStat.fork →
    pre.state.getCode T = Proxy.code → ContextAt T sevm pre →
    CertifiedSettled T (Exec.committedFrames run) →
    ∀ G ∈ Exec.committedFrames run, G.pc = 0 ∧ G.sevm.benvStat.rules.stateGas = none ∧
      (G.sevm.currentTarget = T →
        G.sevm.code = Proxy.code ∨ CurveCoins.UsdcVersion G.sevm.code ∨ G.sevm.code = Lib.code) := by
  induction n with
  | zero => exact fun _ h => absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro sevm pre out run depth fork proxyCode context certified G member
    unfold Exec.committedFrames at member
    split at member
    · rename_i committed
      have rootFacts : (Exec.Frame.ofRun run committed).pc = 0 ∧
          (Exec.Frame.ofRun run committed).sevm.benvStat.rules.stateGas = none ∧
          ((Exec.Frame.ofRun run committed).sevm.currentTarget = T →
            (Exec.Frame.ofRun run committed).sevm.code = Proxy.code ∨
              CurveCoins.UsdcVersion (Exec.Frame.ofRun run committed).sevm.code ∨
                (Exec.Frame.ofRun run committed).sevm.code = Lib.code) :=
        ⟨rfl, fork.stateGas_none, fun t => (context t).1⟩
      have rootMember : Exec.Frame.ofRun run committed ∈ Exec.committedFrames run := by
        simp only [Exec.committedFrames, dite_eq_left committed]
        exact List.mem_cons_self
      have descMember : ∀ g ∈ Exec.descendantFrames run, g ∈ Exec.committedFrames run := fun g hg => by
        simp only [Exec.committedFrames, dite_eq_left committed]
        exact List.mem_cons_of_mem _ hg
      rcases List.mem_cons.mp member with rfl | below
      · exact rootFacts
      · refine Exec.descendantFrames_of_spawns (root := ⟨0, sevm, pre, out, run⟩)
          (Q := fun G => G.pc = 0 ∧ G.sevm.benvStat.rules.stateGas = none ∧
            (G.sevm.currentTarget = T →
              G.sevm.code = Proxy.code ∨ CurveCoins.UsdcVersion G.sevm.code ∨ G.sevm.code = Lib.code))
          ?_ run (.refl _) (fun _ h => h) (fun _ h => h) G below
        intro N f rsm pc' cevm raw child h chain step enter _ into
        have sevmEq : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
        have childDepth : cevm.sta.depth < n := by
          have : cevm.sta.depth < sevm.depth := by
            rw [Frame.enter_run_depth enter, ← sevmEq]
            exact Step.spawn_depth_lt step
          omega
        have childFork : HistFork cevm.sta.benvStat.fork :=
          Blanc.LockExclusion.Evm.step_spawn_child_forkIn step enter (by rw [sevmEq]; exact fork)
        have childContext := child_context run fork proxyCode context
          (fun t c a => certified _ rootMember t c a) chain step enter
        obtain ⟨pcZero, getCode, -⟩ := Blanc.Evm.step_spawn_child step enter
        have childProxy : cevm.dyna.state.getCode T = Proxy.code := by
          change cevm.dyna.getCode T = _
          rw [getCode]
          refine ((Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain).2 T ?_).trans proxyCode
          change (pre.state.getCode T).toList ≠ []
          rw [proxyCode]
          exact proxy_toList_ne_nil
        obtain ⟨cpc, csevm, cdyna⟩ := cevm
        dsimp only at pcZero child childDepth childFork childContext childProxy
        subst pcZero
        have childCert : CertifiedSettled T (Exec.committedFrames child) := fun g hg => by
          refine certified g (descMember g (into g ?_))
          simpa only [Exec.committedFrames, dite_eq_left h] using hg
        have all := ih child childDepth childFork childProxy childContext childCert
        have frames : Exec.committedFrames child = Exec.Frame.ofRun child h :: Exec.descendantFrames child := by
          simp only [Exec.committedFrames, dite_eq_left h]
        rw [frames] at all
        exact ⟨all _ List.mem_cons_self, fun g hg => all g (List.mem_cons_of_mem _ hg)⟩
    · exact absurd member List.not_mem_nil

/-- A settled root that finds the proxy keeps `T` out of the deletion set. -/
theorem root_noDel {R : Exec.Frame} (ready : RootReady HistFork T entrySem (fun _ _ => True) R)
    (certified : CertifiedSettled T (Exec.committedFrames R.run)) (initial : Devm.NoDel T R.pre) :
    Devm.NoDel T R.post := by
  obtain ⟨fork, at_, -, -, pcZero⟩ := ready
  rcases R with ⟨pc, sevm, pre, out, run, committed⟩
  dsimp only at fork at_ certified initial pcZero
  subst pcZero
  have proxyCode : pre.state.getCode T = Proxy.code := bytes_eq_of_image at_.1
  have context : ContextAt T sevm pre := fun t => by
    have hc : sevm.code = Proxy.code := bytes_eq_of_image (at_.2 t).1
    exact ⟨.inl hc, fun hi => (proxy_ne_impl (hc.symm.trans hi)).elim⟩
  have hsg := fork.stateGas_none
  have frames := committed_context (sevm.depth + 1) run (Nat.lt_succ_self _) fork proxyCode context certified
  have safe : ∀ N ∈ Exec.retainedNodes run, N.sevm.currentTarget = T →
      ¬ Linst.At N.sevm.code N.pc .selfdestruct := by
    intro N retained target
    obtain ⟨frame, member, chain⟩ := (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix run N).mp retained
    obtain ⟨framePc, frameSg, classify⟩ := frames frame member
    have same : N.sevm = frame.sevm := Exec.Deriv.ParentPrefix.sevm_eq chain
    have family : UsdcContextCode N.sevm.code := by
      rcases classify (by rw [← same]; exact target) with c | v | c
      · rw [same]; exact .inl c
      · rw [same]
        rcases v with c | c | c
        · exact .inr (.inr (.inl c))
        · exact .inr (.inr (.inr (.inl c)))
        · exact .inr (.inr (.inr (.inr (.inl c))))
      · rw [same]; exact .inr (.inr (.inr (.inr (.inr c))))
    obtain ⟨certificate, checked, noSelfdestruct⟩ := usdcContextCode_certified _ family
    exact not_selfdestruct_of_parentPrefix_noStateGas checked noSelfdestruct framePc
      (by change frame.sevm.code = N.sevm.code; rw [← same]) frameSg chain
  have result := Exec.inv_noDel_of_retained_terminal_safe run committed hsg safe initial
  cases out with
  | error error => cases committed
  | ok post => exact result

/-- **Certification at the settled frames excludes `T`'s deletion, and keeps its code.** -/
theorem usdc_outputNotDeleted {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (capabilities : BodyStageCapabilities HistFork)
    (installed : start.state.getCode T = Proxy.code)
    (certified : CertifiedSettled T trace.settledFrames) :
    trace.OutputNotDeleted T ∧ future.state.getCode T = Proxy.code := by
  refine Blanc.Lift.MidHistoryTraceIn.outputNotDeleted_of_ready trace capabilities (sem := entrySem)
    rfl installed proxy_toList_ne_nil proxy_not_delegation fun R member ready =>
      root_noDel ready fun G hG => certified G ?_
  rw [trace.settledFrames_eq]
  exact List.mem_flatMap.mpr ⟨R, member, hG⟩

/-- **USDC's chain, from certification at the settled frames alone.** -/
theorem usdc_viewSettled_certified {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (capabilities : BodyStageCapabilities HistFork)
    (installed : start.state.getCode T = Proxy.code)
    (certified : CertifiedSettled T trace.settledFrames) :
    ViewSettled T ledgerView (EntryObs T) (EntryGood T) (EntryAllowed T)
      (ledgerView (wordsAt T start.state)) (ledgerView (wordsAt T future.state))
      trace.settledFrames :=
  usdc_viewSettled trace capabilities installed
    (usdc_outputNotDeleted trace capabilities installed certified).1

end Blanc.Lift.Usdc
