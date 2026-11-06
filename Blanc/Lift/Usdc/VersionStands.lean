import Blanc.Lift.Usdc.EntryChainScan

/-!
# A listed version, once standing, stands: `ScanLive` from one read per version

Every certificate of the three versions and the library has no `SELFDESTRUCT` (kernel decided, `*.cert_noSelfdestruct`).
V2, V2_1 and the library spawn no `DELEGATECALL`, so nothing else runs in their storage context; V2_2's only one runs the
library (`impl_committed`). So no settled root deletes one of these accounts while it holds its code, and a read at the
start of a mid history reaches every later settled root (`entry_ready`).

`scanLive_of_suffixes`: `ScanLive` at every settled root from one cut per version, at which that version stands and
after which every root naming it lies. Nothing is read between interval ends.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-! ## At one root -/

theorem v2_undelegatedCert : ∀ f ∈ ImplV2.cert.prog, f.execsSatisfy Xinst.notDelegatecall = true := by
  decide +kernel

theorem v2_1_undelegatedCert : ∀ f ∈ ImplV2_1.cert.prog, f.execsSatisfy Xinst.notDelegatecall = true := by
  decide +kernel

theorem lib_undelegatedCert : ∀ f ∈ Lib.cert.prog, f.execsSatisfy Xinst.notDelegatecall = true := by
  decide +kernel

theorem v2_safety : InstalledRuntimeSafety ImplV2.code :=
  .of_undelegatedCert ImplV2.cert_check v2_undelegatedCert ImplV2.cert_noSelfdestruct
    ImplV2.code_not_delegation (UsdcContextCode.ne_nil (.inr (.inr (.inl rfl))))

theorem v2_1_safety : InstalledRuntimeSafety ImplV2_1.code :=
  .of_undelegatedCert ImplV2_1.cert_check v2_1_undelegatedCert ImplV2_1.cert_noSelfdestruct
    ImplV2_1.code_not_delegation (UsdcContextCode.ne_nil (.inr (.inr (.inr (.inl rfl)))))

theorem lib_safety : InstalledRuntimeSafety Lib.code :=
  .of_undelegatedCert Lib.cert_check lib_undelegatedCert Lib.cert_noSelfdestruct
    Lib.code_not_delegation (UsdcContextCode.ne_nil (.inr (.inr (.inr (.inr (.inr rfl))))))

variable {a : Adr}

/-- A root that finds code with the safety bundle keeps its account out of the deletion set. -/
theorem root_noDel_of_safety {C : ByteArray} (K : InstalledRuntimeSafety C) {s0 : C.size ≠ 0}
    {sd : C.size ≠ eoaDelegatedCodeLength} {R : Exec.Frame}
    (ready : RootReady HistFork a (CodeSem.ofBytes C s0 sd) (fun _ _ => True) R)
    (initial : Devm.NoDel a R.pre) : Devm.NoDel a R.post := by
  obtain ⟨fork, at_, -, -, pcZero⟩ := ready
  rcases R with ⟨pc, sevm, pre, out, run, committed⟩
  dsimp only at fork at_ initial pcZero
  subst pcZero
  have hsg := fork.stateGas_none
  have result := Exec.inv_noDel_of_retained_terminal_safe run committed hsg
    (fun N retained => K.safe run hsg (bytes_eq_of_image at_.1)
      (fun t => ⟨rfl, bytes_eq_of_image (at_.2 t).1⟩) N
      ((Exec.retainedNodes_sublist_rawNodes run).subset retained)) initial
  cases out with
  | error error => cases committed
  | ok post => exact result

/-- A spawn's child at `a`, which holds V2_2, runs V2_2 or the library. -/
theorem impl_child {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (fork : HistFork sevm.benvStat.fork) (code : pre.state.getCode a = Impl.code)
    (lib : pre.state.getCode usdcLib = Lib.code)
    (context : sevm.currentTarget = a → sevm.code = Impl.code ∨ sevm.code = Lib.code)
    {N : Exec.Deriv} (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N)
    {f : Frame} {rsm : Resume} {pc' : Nat} {cevm : Evm}
    (step : Evm.step ⟨N.pc, N.sevm, N.devm⟩ = .spawn f rsm pc') (enter : f.enter = .run cevm)
    (childTarget : cevm.sta.currentTarget = a) : cevm.sta.code = Impl.code ∨ cevm.sta.code = Lib.code := by
  have hsg := fork.stateGas_none
  have sevmEq : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  have implNe : Impl.code.toList ≠ [] := UsdcContextCode.ne_nil (.inr (.inr (.inr (.inr (.inl rfl)))))
  have nodeCode : N.devm.getCode a = Impl.code := by
    refine ((Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain).2 a ?_).trans code
    change (pre.state.getCode a).toList ≠ []
    rw [code]
    exact implNe
  obtain ⟨x, hat, spawn, -⟩ := Evm.step_spawn_inv step
  obtain ⟨-, -, actual⟩ := Blanc.Evm.step_spawn_child step enter
  obtain ⟨benv, -, hcevm⟩ := Frame.enter_run_inv enter
  have frameTarget : f.inner.currentTarget = a := by rw [hcevm] at childTarget; exact childTarget
  have frameCode : cevm.sta.code = f.inner.code := Frame.enter_run_code enter
  have direct : x = .call ∨ x = .staticcall → cevm.sta.code = Impl.code := fun d => by
    rw [frameCode, Xinst.step_directCall_spawn_code d spawn
      (by rw [frameTarget, nodeCode]; exact Impl.code_not_delegation), frameTarget, nodeCode]
  by_cases parent : sevm.currentTarget = a
  · rcases context parent with hc | hc
    · obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix_noStateGas certL_check
        (F := ⟨0, sevm, pre, out, run⟩) rfl hc hsg chain
      have kind := ok.execsSatisfy (Cursor.execsSatisfy_of_reachable impl_kinds reach) hat
      cases x with
      | call => exact .inl (direct (.inl rfl))
      | delegatecall => exact .inr (frameCode.trans (impl_delegate_lib run hc hsg lib chain hat spawn))
      | _ => simp only [implKinds, reduceCtorEq, beq_iff_eq, Bool.or_eq_true, or_self] at kind
    · obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix_noStateGas Lib.cert_check
        (F := ⟨0, sevm, pre, out, run⟩) rfl hc hsg chain
      exact .inl (direct (.inr (isStaticcall_eq
        (ok.execsSatisfy (Cursor.execsSatisfy_of_reachable lib_staticOnly reach) hat))))
  · have away : N.sevm.currentTarget ≠ cevm.sta.currentTarget := by
      rw [sevmEq, childTarget]
      exact parent
    have entered := actual away
      (by rw [childTarget, nodeCode]; exact fun e => implNe (by rw [e]; exact ByteArray.toList_empty))
      (by rw [childTarget, nodeCode]; exact Impl.code_not_delegation)
    rw [childTarget, nodeCode] at entered
    exact .inl entered

/-- **Every committed frame in the storage of an account holding V2_2 runs V2_2 or the library**, when the library
stands. -/
theorem impl_committed (n : Nat) : ∀ {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out), sevm.depth < n → HistFork sevm.benvStat.fork →
    pre.state.getCode a = Impl.code → pre.state.getCode usdcLib = Lib.code →
    (sevm.currentTarget = a → sevm.code = Impl.code ∨ sevm.code = Lib.code) →
    ∀ G ∈ Exec.committedFrames run, G.pc = 0 ∧ G.sevm.benvStat.rules.stateGas = none ∧
      (G.sevm.currentTarget = a → G.sevm.code = Impl.code ∨ G.sevm.code = Lib.code) := by
  induction n with
  | zero => exact fun _ h => absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro sevm pre out run depth fork code lib context G member
    unfold Exec.committedFrames at member
    split at member
    · rename_i committed
      rcases List.mem_cons.mp member with rfl | below
      · exact ⟨rfl, fork.stateGas_none, context⟩
      · refine Exec.descendantFrames_of_spawns (root := ⟨0, sevm, pre, out, run⟩)
          (Q := fun G => G.pc = 0 ∧ G.sevm.benvStat.rules.stateGas = none ∧
            (G.sevm.currentTarget = a → G.sevm.code = Impl.code ∨ G.sevm.code = Lib.code))
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
        have childContext := impl_child run fork code lib context chain step enter
        obtain ⟨pcZero, getCode, -⟩ := Blanc.Evm.step_spawn_child step enter
        have keep : ∀ {b : Adr} {C : ByteArray}, C.toList ≠ [] → pre.state.getCode b = C →
            cevm.dyna.state.getCode b = C := fun {b C} ne hb => by
          change cevm.dyna.getCode b = _
          rw [getCode]
          refine ((Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain).2 b ?_).trans hb
          change (pre.state.getCode b).toList ≠ []
          rw [hb]
          exact ne
        have childCode := keep (UsdcContextCode.ne_nil (.inr (.inr (.inr (.inr (.inl rfl)))))) code
        have childLib := keep (UsdcContextCode.ne_nil (.inr (.inr (.inr (.inr (.inr rfl)))))) lib
        obtain ⟨cpc, csevm, cdyna⟩ := cevm
        dsimp only at pcZero child childDepth childFork childContext childCode childLib
        subst pcZero
        have all := ih child childDepth childFork childCode childLib childContext
        have frames : Exec.committedFrames child = Exec.Frame.ofRun child h :: Exec.descendantFrames child := by
          simp only [Exec.committedFrames, dite_eq_left h]
        rw [frames] at all
        exact ⟨all _ List.mem_cons_self, fun g hg => all g (List.mem_cons_of_mem _ hg)⟩
    · exact absurd member List.not_mem_nil

/-- A root that finds V2_2 and the library keeps the account out of the deletion set. -/
theorem impl_root_noDel {s0 : Impl.code.size ≠ 0} {sd : Impl.code.size ≠ eoaDelegatedCodeLength} {R : Exec.Frame}
    (ready : RootReady HistFork a (CodeSem.ofBytes Impl.code s0 sd) (fun _ _ => True) R)
    (lib : R.pre.state.getCode usdcLib = Lib.code) (initial : Devm.NoDel a R.pre) : Devm.NoDel a R.post := by
  obtain ⟨fork, at_, -, -, pcZero⟩ := ready
  rcases R with ⟨pc, sevm, pre, out, run, committed⟩
  dsimp only at fork at_ lib initial pcZero
  subst pcZero
  have hsg := fork.stateGas_none
  have frames := impl_committed (a := a) (sevm.depth + 1) run (Nat.lt_succ_self _) fork
    (bytes_eq_of_image at_.1) lib (fun t => .inl (bytes_eq_of_image (at_.2 t).1))
  have safe : ∀ N ∈ Exec.retainedNodes run, N.sevm.currentTarget = a →
      ¬ Linst.At N.sevm.code N.pc .selfdestruct := by
    intro N retained target
    obtain ⟨frame, member, chain⟩ := (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix run N).mp retained
    obtain ⟨framePc, frameSg, classify⟩ := frames frame member
    have same : N.sevm = frame.sevm := Exec.Deriv.ParentPrefix.sevm_eq chain
    have family : UsdcContextCode N.sevm.code := by
      rcases classify (by rw [← same]; exact target) with c | c
      · rw [same]; exact .inr (.inr (.inr (.inr (.inl c))))
      · rw [same]; exact .inr (.inr (.inr (.inr (.inr c))))
    obtain ⟨certificate, checked, noSelfdestruct⟩ := usdcContextCode_certified _ family
    exact not_selfdestruct_of_parentPrefix_noStateGas checked noSelfdestruct framePc
      (by change frame.sevm.code = N.sevm.code; rw [← same]) frameSg chain
  have result := Exec.inv_noDel_of_retained_terminal_safe run committed hsg safe initial
  cases out with
  | error error => cases committed
  | ok post => exact result

/-! ## Along a mid history -/

section Mid

variable {cfg : ChainConfig} {start : Benv} {future : BlockChain}
  (trace : MidHistoryTraceIn HistFork cfg start future) (capabilities : BodyStageCapabilities HistFork)

include capabilities in
/-- Code standing at the start stands at every settled root, when no root that finds it deletes its account. -/
theorem stands_of_law {C : ByteArray} (s0 : C.size ≠ 0) (sd : C.size ≠ eoaDelegatedCodeLength)
    (ne : C.toList ≠ []) (del : ¬ isValidDelegation C) (installed : start.state.getCode a = C)
    (law : ∀ R ∈ trace.settledRoots, RootReady HistFork a (CodeSem.ofBytes C s0 sd) (fun _ _ => True) R →
      Devm.NoDel a R.pre → Devm.NoDel a R.post) :
    ∀ R ∈ trace.settledRoots, R.pre.state.getCode a = C := fun R member =>
  bytes_eq_of_image (Blanc.Lift.MidHistoryTraceIn.rootsReady trace capabilities (sem := CodeSem.ofBytes C s0 sd) rfl
    installed ne del (Blanc.Lift.MidHistoryTraceIn.outputNotDeleted_of_ready trace capabilities
      (sem := CodeSem.ofBytes C s0 sd) rfl installed ne del law).1 R member).2.1.1

include capabilities in
/-- Code with the safety bundle, standing at the start, stands at every settled root. -/
theorem stands_of_safety {C : ByteArray} (K : InstalledRuntimeSafety C) (s0 : C.size ≠ 0)
    (sd : C.size ≠ eoaDelegatedCodeLength) (installed : start.state.getCode a = C) :
    ∀ R ∈ trace.settledRoots, R.pre.state.getCode a = C :=
  stands_of_law trace capabilities s0 sd K.nonempty K.notDelegation installed
    fun _ _ ready => root_noDel_of_safety K ready

include capabilities in
/-- **A listed version, with the library under V2_2, standing at the start of a mid history stands at every settled
root.** One read at the start. -/
theorem entry_ready {e : UsdcDeployedEntry} (version : CurveCoins.UsdcVersion e.code)
    (code : start.state.getCode e.adr = e.code)
    (lib : e.code = Impl.code → start.state.getCode usdcLib = Lib.code) :
    ∀ R ∈ trace.settledRoots, e.RuntimeReady R.pre := by
  obtain ⟨adr, C, base, before⟩ := e
  dsimp only at version code lib
  intro R member
  refine ⟨?_, fun hi => ?_⟩
  · rcases version with rfl | rfl | rfl
    · exact stands_of_safety trace capabilities v2_safety (by decide +kernel) (by decide +kernel) code R member
    · exact stands_of_safety trace capabilities v2_1_safety (by decide +kernel) (by decide +kernel) code R member
    · have libStands := stands_of_safety trace capabilities lib_safety (by decide +kernel) (by decide +kernel)
        (lib rfl)
      exact stands_of_law trace capabilities (by decide +kernel) (by decide +kernel)
        (UsdcContextCode.ne_nil (.inr (.inr (.inr (.inr (.inl rfl)))))) Impl.code_not_delegation code
        (fun Q here ready => impl_root_noDel ready (libStands Q here)) R member
  · exact stands_of_safety trace capabilities lib_safety (by decide +kernel) (by decide +kernel) (lib hi) R member

variable {T : Adr} {Vs : List UsdcDeployedEntry} (list : VersionList Vs)

include capabilities list in
/-- `ScanLive` at every settled root, when every listed version stands at the start. -/
theorem scanLive_of_standing
    (standing : ∀ e ∈ Vs, start.state.getCode e.adr = e.code ∧
      (e.code = Impl.code → start.state.getCode usdcLib = Lib.code)) :
    ∀ R ∈ trace.settledRoots, ScanLive T Vs R := fun R member e he _ =>
  entry_ready trace capabilities (list.codes e he) (standing e he).1 (standing e he).2 R member

include capabilities list in
/-- **`ScanLive` at every settled root from one cut per version**: a mid history to the same end, at whose start the
version (and, under V2_2, the library) stands, holding every root that finds the word naming that version. -/
theorem scanLive_of_suffixes
    (cuts : ∀ e ∈ Vs, ∃ (c : Benv) (suffix : MidHistoryTraceIn HistFork cfg c future),
      (c.state.getCode e.adr = e.code ∧ (e.code = Impl.code → c.state.getCode usdcLib = Lib.code)) ∧
      ∀ R ∈ trace.settledRoots, ((R.pre.getStor T).get implSlot).toAdr = e.adr → R ∈ suffix.settledRoots) :
    ∀ R ∈ trace.settledRoots, ScanLive T Vs R := fun R member e he named => by
  obtain ⟨c, suffix, ⟨code, lib⟩, holds⟩ := cuts e he
  exact entry_ready suffix capabilities (list.codes e he) code lib R (holds R member named)

end Mid

end Blanc.Lift.Usdc
