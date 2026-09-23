import Blanc.DripExitPreCallbackLocator
import Blanc.DripRealizedExec
import Blanc.ExecutionTraceSettledFrames

/-!
DRIP frames spawn only their payout child.

Every committed non-exit route of the installed runtime is one gas-free source
prefix from the entry to a terminal instruction. Replayed onto the actual
execution with `Exec.Deriv.SourceCursor.ofRunPrefix_sameFrame_gasFree`, its
same-frame chain decodes no frame-entering instruction, so the frame retains no
descendant frame (`nonexit_descendantFrames_nil`).

A successful `exit` frame's same-frame chain enters exactly one frame, at its
payout `CALL`: `exit_exec_handoffAt` carries the actual child slot and proves
the frame's descendant frames are that slot's settled frames.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Drip

/-! ## Straight-line gas-free tails -/

theorem straightGasFree_afterDrip : Func.straightGasFree afterDrip = true := by
  decide

theorem straightGasFree_afterJoin : Func.straightGasFree afterJoin = true := by
  decide

theorem straightGasFree_afterConvertToAssets :
    Func.straightGasFree afterConvertToAssets = true := by
  decide

theorem straightGasFree_afterConvertToUnits :
    Func.straightGasFree afterConvertToUnits = true := by
  decide

/-! ## Route prefixes to a terminal instruction -/

/-- The shared route tail of every non-exit entry: staging a non-exit route
word, the fresh-index machine, and the selected straight-line tail, as one
gas-free prefix ending at a terminal instruction. -/
theorem of_run_freshTail_terminal_prefix {fs : List Func}
    (hlookup : AuxLookup fs) {e : Sevm} {entry s r : Devm} {image : Bytes}
    {route : B256} {path : Prog.SourcePath}
    (frame : Frame image entry s) (notExit : route ≠ routeExit)
    (run : Func.Run fs e s (stageRoute route +++ .call freshStartSlot) r) :
    ∃ target t l, Func.RunPrefix fs e path s
      (stageRoute route +++ .call freshStartSlot) target t (.last l) := by
  unfold stageRoute at run ⊢
  rcases run_prefix_prepend (l := [pushB256 route]) (path := path)
      (by simp only [Line.gasFree, Ninst.pushB256, Ninst.gasFree,
        Bool.true_and]) run with
    ⟨s1, mid1, hline1, run, hpre1⟩
  have frame1 := frame.line (by line_inv) (by line_inv) (by line_inv) hline1
  have hp1 : route :: [] <<+ s1.stack := by
    rcases Line.of_run_cons hline1 with ⟨u, hpush, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 hpush) nil_pref
  rcases run_prefix_prepend (l := mstoreAt routeWord) (path := mid1)
      (gasFree_mstoreAt routeWord) run with
    ⟨s2, mid2, hline2, run, hpre2⟩
  obtain ⟨hp2, frame2⟩ := frame1.mstoreAt hp1 hline2
  obtain ⟨t3, image3, target3, -, -, -, -, -, -, -, -, -, hmachine, frame3,
    hp3, hpre3, run⟩ := of_run_freshStart_prefix (path := mid2) hlookup
      frame2 hp2 run
  have htag : scratch image3 routeWord = route := by
    rw [hmachine.1, scratch_setScratch_self]
  obtain ⟨t4, target4, frame4, hp4, hroute⟩ :=
    of_run_freshRoute_prefix (path := target3) hlookup frame3 hp3 run
  have head := hpre1.trans (hpre2.trans hpre3)
  rcases hroute with ⟨-, hpre4, run⟩ | ⟨htagE, -, -⟩ | ⟨-, hpre4, run⟩ |
    ⟨-, hpre4, run⟩ | ⟨-, hpre4, run⟩
  · rcases Func.RunPrefix.toLast_of_run (path := target4)
        straightGasFree_afterConvertToAssets run with ⟨target, t, l, walk⟩
    exact ⟨target, t, l, head.trans (hpre4.trans walk)⟩
  · exact (notExit (htag.symm.trans htagE)).elim
  · rcases Func.RunPrefix.toLast_of_run (path := target4)
        straightGasFree_afterConvertToUnits run with ⟨target, t, l, walk⟩
    exact ⟨target, t, l, head.trans (hpre4.trans walk)⟩
  · rcases Func.RunPrefix.toLast_of_run (path := target4)
        straightGasFree_afterDrip run with ⟨target, t, l, walk⟩
    exact ⟨target, t, l, head.trans (hpre4.trans walk)⟩
  · rcases Func.RunPrefix.toLast_of_run (path := target4)
        straightGasFree_afterJoin run with ⟨target, t, l, walk⟩
    exact ⟨target, t, l, head.trans (hpre4.trans walk)⟩

/-- One staged surface guard: duplicate the value on top of the stack, stage
it in a scratch word, and pass `value ≤ cap`. The rejecting arm is the inline
revert, which has no successful run. -/
theorem of_run_stagedGuard_prefix {fs : List Func} {e : Sevm}
    {entry s r : Devm} {image : Bytes} {value word cap : B256} {cont : Func}
    {path : Prog.SourcePath}
    (frame : Frame image entry s) (hp : value :: [] <<+ s.stack)
    (run : Func.Run fs e s
      (dup 0 ::: mstoreAt word +++ pushB256 cap ::: lt ::: (.revert <?> cont))
      r) :
    ∃ t image' target, Frame image' entry t ∧
      Func.RunPrefix fs e path s
        (dup 0 ::: mstoreAt word +++ pushB256 cap ::: lt ::: (.revert <?> cont))
        target t cont ∧
      Func.Run fs e t cont r := by
  rcases run_prefix_prepend (l := [dup 0]) (path := path)
      (by decide : Line.gasFree [dup 0] = true) run with
    ⟨s1, mid1, hline1, run, hpre1⟩
  have frame1 := frame.line (by line_inv) (by line_inv) (by line_inv) hline1
  have hp1 : value :: value :: [] <<+ s1.stack :=
    prefix_of_dup_val (of_run_singleton hline1) (by show_nth) hp
  rcases run_prefix_prepend (l := mstoreAt word) (path := mid1)
      (gasFree_mstoreAt word) run with
    ⟨s2, mid2, hline2, run, hpre2⟩
  obtain ⟨-, frame2⟩ := frame1.mstoreAt hp1 hline2
  rcases run_prefix_prepend (l := [pushB256 cap, lt]) (path := mid2)
      (by simp only [Line.gasFree, Ninst.pushB256, Ninst.gasFree,
        Rinst.gasFree, Bool.true_and]) run with
    ⟨s3, mid3, hline3, run, hpre3⟩
  have frame3 := frame2.line (by line_inv) (by line_inv) (by line_inv) hline3
  rcases run_prefix_branch (path := mid3) run with
    ⟨t, mid4, hpop, run, hpre4⟩ | ⟨w, u, v, midV, hnz, hpopV, hburn, hrev, hpreV⟩
  · exact ⟨t, _, mid4, frame3.of_popBurn hpop,
      hpre1.trans (hpre2.trans (hpre3.trans hpre4)), run⟩
  · exact absurd hrev not_run_revert

/-- `drip()` as one gas-free prefix to a terminal instruction. -/
theorem of_run_drip_terminal_prefix {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {path : Prog.SourcePath}
    (frame : Frame image entry s) (run : Func.Run fs e s Drip.drip r) :
    ∃ target t l, Func.RunPrefix fs e path s Drip.drip target t (.last l) :=
  of_run_freshTail_terminal_prefix hlookup frame (by decide) run

/-- Either conversion view as one gas-free prefix to a terminal instruction. -/
theorem of_run_viewEntry_terminal_prefix {fs : List Func}
    (hlookup : AuxLookup fs) {e : Sevm} {entry s r : Devm} {image : Bytes}
    {cap route : B256} {path : Prog.SourcePath}
    (frame : Frame image entry s) (notExit : route ≠ routeExit)
    (run : Func.Run fs e s
      (arg 0 +++ dup 0 ::: mstoreAt argumentWord +++ pushB256 cap ::: lt :::
        (.revert <?> (stageRoute route +++ Func.call freshStartSlot))) r) :
    ∃ target t l, Func.RunPrefix fs e path s
      (arg 0 +++ dup 0 ::: mstoreAt argumentWord +++ pushB256 cap ::: lt :::
        (.revert <?> (stageRoute route +++ Func.call freshStartSlot)))
      target t (.last l) := by
  rcases run_prefix_prepend (l := arg 0) (path := path)
      (by simp only [arg, cdl, Line.gasFree, Ninst.pushB256, Ninst.gasFree,
        Rinst.gasFree, Bool.true_and]) run with
    ⟨s1, mid1, hline1, run, hpre1⟩
  have frame1 := frame.line (by line_inv) (by line_inv) (by line_inv) hline1
  obtain ⟨t2, image2, mid2, frame2, hpre2, run⟩ :=
    of_run_stagedGuard_prefix (path := mid1) frame1
      (prefix_of_cdl_val nil_pref hline1) run
  rcases of_run_freshTail_terminal_prefix (path := mid2) hlookup frame2
      notExit run with ⟨target, t, l, walk⟩
  exact ⟨target, t, l, hpre1.trans (hpre2.trans walk)⟩

/-- `join()` as one gas-free prefix to a terminal instruction. -/
theorem of_run_join_terminal_prefix {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {path : Prog.SourcePath}
    (frame : Frame image entry s) (run : Func.Run fs e s Drip.join r) :
    ∃ target t l, Func.RunPrefix fs e path s Drip.join target t (.last l) := by
  unfold Drip.join at run ⊢
  rcases run_prefix_prepend (l := [callvalue]) (path := path)
      (by decide : Line.gasFree [callvalue] = true) run with
    ⟨s1, mid1, hline1, run, hpre1⟩
  have frame1 := frame.line (by line_inv) (by line_inv) (by line_inv) hline1
  have hp1 : e.value :: [] <<+ s1.stack :=
    prefix_of_push (of_run_callvalue (of_run_singleton hline1)) nil_pref
  obtain ⟨t2, image2, mid2, frame2, hpre2, run⟩ :=
    of_run_stagedGuard_prefix (path := mid1) frame1 hp1 run
  rcases run_prefix_prepend (l := [caller, sload]) (path := mid2)
      (by decide : Line.gasFree [caller, sload] = true) run with
    ⟨s3, mid3, hline3, run, hpre3⟩
  have frame3 := frame2.line (by line_inv) (by line_inv) (by line_inv) hline3
  have hp3 : ∃ y, y :: [] <<+ s3.stack := by
    rcases Line.of_run_cons hline3 with ⟨u1, hcaller, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hsload, hnil⟩
    cases hnil
    obtain ⟨y, hy, -⟩ :=
      prefix_of_sload hsload (prefix_of_push (of_run_caller hcaller) nil_pref)
    exact ⟨y, hy⟩
  obtain ⟨y3, hp3⟩ := hp3
  obtain ⟨t4, image4, mid4, frame4, hpre4, run⟩ :=
    of_run_stagedGuard_prefix (path := mid3) frame3 hp3 run
  rcases run_prefix_prepend (l := [pushB256 totalUnitsSlot, sload])
      (path := mid4)
      (by simp only [Line.gasFree, Ninst.pushB256, Ninst.gasFree,
        Rinst.gasFree, Bool.true_and]) run with
    ⟨s5, mid5, hline5, run, hpre5⟩
  have frame5 := frame4.line (by line_inv) (by line_inv) (by line_inv) hline5
  have hp5 : ∃ y, y :: [] <<+ s5.stack := by
    rcases Line.of_run_cons hline5 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hsload, hnil⟩
    cases hnil
    obtain ⟨y, hy, -⟩ :=
      prefix_of_sload hsload (prefix_of_push (of_run_pushB256 hpush) nil_pref)
    exact ⟨y, hy⟩
  obtain ⟨y5, hp5⟩ := hp5
  obtain ⟨t6, image6, mid6, frame6, hpre6, run⟩ :=
    of_run_stagedGuard_prefix (path := mid5) frame5 hp5 run
  rcases of_run_freshTail_terminal_prefix (path := mid6) hlookup frame6
      (by decide) run with ⟨target, t, l, walk⟩
  exact ⟨target, t, l, hpre1.trans (hpre2.trans (hpre3.trans (hpre4.trans
    (hpre5.trans (hpre6.trans walk)))))⟩

/-- A dispatched nonpayable exact-calldata entry whose body walks to a
terminal instruction walks there from the dispatcher. -/
private theorem of_run_dispatch_nonpayable_terminal_prefix
    {fs : List Func} {sevm : Sevm} {s r : Devm} {path : Prog.SourcePath}
    {sig size : B256} {body : Func}
    (hmem : (sig, nonpayable (exactCalldata size body)) ∈ funcs)
    (hpfx : sig :: [] <<+ s.stack) (hmemory : s.memory = Mem.empty)
    (hdispatch : Func.Run fs sevm s (dispatch tree) r)
    (bodyWalk : ∀ {entry : Devm} {bodyPath : Prog.SourcePath},
      Frame [] entry entry → Func.Run fs sevm entry body r →
        ∃ target t l,
          Func.RunPrefix fs sevm bodyPath entry body target t (.last l)) :
    ∃ target t l,
      Func.RunPrefix fs sevm path s (dispatch tree) target t (.last l) := by
  rcases reach_of_dispatch_logs (path := path) funcs_sorted hmem hpfx
      hdispatch with
    ⟨s3, path3, -, -, hmm3, -, -, hpre3, hwrapped⟩
  rcases of_run_nonpayable_exactCalldata_prefix (path := path3) hwrapped with
    ⟨s4, path4, -, -, -, hmm4, -, -, hpre4, hbody⟩
  have hmem4 : s4.memory = Mem.empty := by rw [← hmm4, ← hmm3, hmemory]
  have hframe : Frame [] s4 s4 :=
    ⟨by rw [hmem4]; exact Mem.wf_empty,
      by rw [hmem4]; exact Mem.reads_empty, rfl, rfl⟩
  rcases bodyWalk (bodyPath := path4) hframe hbody with ⟨target, t, l, walk⟩
  exact ⟨target, t, l, hpre3.trans (hpre4.trans walk)⟩

/-- Every committed non-exit route of the installed runtime's source program
is one gas-free prefix from the entry to a terminal instruction. -/
theorem of_run_main_nonexit_terminal_prefix {sevm : Sevm} {entry post : Devm}
    (run : Func.Run (runtime.main :: runtime.aux) sevm entry main post)
    (hcanon : entry.memory = Mem.empty)
    (hnotExit :
      sevm.data.length.toB256 = 0 ∨ Sevm.selector sevm ≠ exitSelector) :
    ∃ target t l, Func.RunPrefix (runtime.main :: runtime.aux) sevm ⟨0, []⟩
      entry main target t (.last l) := by
  by_cases hempty : sevm.data.length.toB256 = 0
  · unfold main at run ⊢
    rcases run_prefix_prepend (l := [calldatasize]) (path := ⟨0, []⟩)
        (by decide : Line.gasFree [calldatasize] = true) run with
      ⟨s1, mid1, hline, hbranch, hpre1⟩
    have hp : sevm.data.length.toB256 :: [] <<+ s1.stack := by
      rcases Line.of_run_cons hline with ⟨a, hsize, hnil⟩
      cases hnil
      exact prefix_of_push (of_run_calldatasize hsize) nil_pref
    rcases run_prefix_branch (path := mid1) hbranch with
      ⟨u, midU, hpop, hstop, hpreB⟩
      | ⟨w, u, v, midV, hnz, hpop, hburn, hmain, hpreB⟩
    · exact ⟨midU, u, .stop, hpre1.trans hpreB⟩
    · exact absurd ((popBurn_pref hpop hp).1.trans hempty) hnz
  have hnonempty : sevm.data.length.toB256 ≠ 0 := hempty
  have hselector : Sevm.selector sevm ≠ exitSelector :=
    hnotExit.resolve_left hempty
  have hmemSel := main_selector_mem run hnonempty
  rcases dispatch_entry_of_run_main_prefix (path := ⟨0, []⟩) run hnonempty with
    ⟨s2, path2, -, hmm2, -, -, hpfx, hpre2, hdispatch⟩
  have hmem2 : s2.memory = Mem.empty := by rw [← hmm2, hcanon]
  have hlookup := auxLookup_runtime
  have finish : (∃ target t l, Func.RunPrefix (runtime.main :: runtime.aux)
      sevm path2 s2 (dispatch tree) target t (.last l)) →
      ∃ target t l, Func.RunPrefix (runtime.main :: runtime.aux) sevm
        ⟨0, []⟩ entry main target t (.last l) := by
    rintro ⟨target, t, l, walk⟩
    exact ⟨target, t, l, hpre2.trans walk⟩
  apply finish
  simp only [selectors, List.mem_cons, List.not_mem_nil, or_false] at hmemSel
  rcases hmemSel with hsel | hsel | hsel | hsel | hsel <;> rw [hsel] at hpfx
  · exact of_run_dispatch_nonpayable_terminal_prefix (size := 36)
      (body := Drip.convertToAssets) (by simp [funcs]) hpfx
      hmem2 hdispatch fun frame body => by
        unfold Drip.convertToAssets at body ⊢
        exact of_run_viewEntry_terminal_prefix hlookup frame (by decide) body
  · exact (hselector hsel).elim
  · exact of_run_dispatch_nonpayable_terminal_prefix (size := 36)
      (body := Drip.convertToUnits) (by simp [funcs]) hpfx
      hmem2 hdispatch fun frame body => by
        unfold Drip.convertToUnits at body ⊢
        exact of_run_viewEntry_terminal_prefix hlookup frame (by decide) body
  · exact of_run_dispatch_nonpayable_terminal_prefix (size := 4)
      (body := Drip.drip) (by simp [funcs]) hpfx
      hmem2 hdispatch fun frame body =>
        of_run_drip_terminal_prefix hlookup frame body
  · rcases reach_of_dispatch_logs (path := path2) funcs_sorted
        (by simp [funcs] : (joinSelector, exactCalldata 4 join) ∈ funcs) hpfx
        hdispatch with
      ⟨s3, path3, -, -, hmm3, -, -, hpre3, hwrapped⟩
    rcases of_run_exactCalldata_prefix (path := path3) hwrapped with
      ⟨s4, path4, -, -, hmm4, -, -, hpre4, hbody⟩
    have hmem4 : s4.memory = Mem.empty := by rw [← hmm4, ← hmm3, hmem2]
    have hframe : Frame [] s4 s4 :=
      ⟨by rw [hmem4]; exact Mem.wf_empty,
        by rw [hmem4]; exact Mem.reads_empty, rfl, rfl⟩
    rcases of_run_join_terminal_prefix (path := path4) hlookup hframe hbody with
      ⟨target, t, l, walk⟩
    exact ⟨target, t, l, hpre3.trans (hpre4.trans walk)⟩

-- The frozen statement carries `committed`; `.ok post` alone already fixes a
-- committed source route, so the proof does not read it.
set_option linter.unusedVariables false in
/-- **T4b.** Every committed non-exit route of a DRIP frame enters no frame. -/
theorem nonexit_descendantFrames_nil {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hcanon : pre.memory = Mem.empty)
    (committed : Execution.commits (.ok post) = true)
    (hnotExit : sevm.data.length.toB256 = 0 ∨ Sevm.selector sevm ≠ exitSelector)
    (hfork : CoveredFork sevm.benvStat.fork) :
    Exec.descendantFrames exc = [] := by
  have compiled : some sevm.code.toList = runtime.compile :=
    installed_compile hcode
  have hrun : Prog.Run sevm pre runtime post :=
    correct sevm pre runtime post exc compiled
  dsimp only [Prog.Run] at hrun
  cases hrun
  rename (_ = _) => heq
  rename (Func.Run _ _ _ _ _) => run
  rename (Devm.Burn _ _) => burn
  rename Devm => entry
  cases heq
  have hmemEntry : entry.memory = Mem.empty := by rw [← burn.memory, hcanon]
  rcases of_run_main_nonexit_terminal_prefix run hmemEntry hnotExit with
    ⟨target, t, l, walk⟩
  rcases Exec.Deriv.SourceCursor.mainForwardFree
      (root := ⟨0, sevm, pre, .ok post, exc⟩) (program := runtime)
      rfl compiled rfl with
    ⟨mainCursor, mainFree, actualBurn⟩
  have seed : Devm.EqModGas entry mainCursor.pre :=
    (Devm.EqModGas.refl pre).of_burn burn actualBurn
  rcases mainCursor.ofRunPrefix_sameFrame_gasFree compiled rfl walk seed
      hfork.rules_stateGas_none with
    ⟨endCursor, -, endFree⟩
  exact Exec.descendantFrames_eq_nil_of_no_sameFrame_xinstAt exc
    ((mainFree.trans endFree).noExec_of_linstAt
      (Linst.at_of_slice endCursor.codeSlice))

/-! ## T4a: the exit frame's descendants are its payout child's -/

/-- One same-frame step whose retained slot is `retained` contributes exactly
that slot's settled frames, provided a spawned child's settlement commits. -/
theorem Exec.Deriv.descendantFrames_eq_of_stepRun {node next : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep next node) {xl : Xlot}
    (stepRun : Step.Run (Evm.step ⟨node.pc, node.sevm, node.devm⟩) xl
      (.ok next.devm))
    (settles : ∀ (frame : Jaune.Frame) (resume : Resume) (nextPc : Nat)
      (evm : Evm) (raw : Execution),
      Evm.step ⟨node.pc, node.sevm, node.devm⟩ = .spawn frame resume nextPc →
      xl = .some ⟨evm, raw⟩ → Frame.settlementCommits frame raw = true)
    (retained : ExecutionTrace.RetainedXlot xl) :
    Exec.descendantFrames node.exc =
      retained.settledFrames ++ Exec.descendantFrames next.exc := by
  cases edge with
  | cont hstep next =>
      rw [hstep] at stepRun
      obtain ⟨hxl, -⟩ := stepRun
      subst hxl
      cases retained
      simp [Exec.descendantFrames]
  | doneOk hstep henter hresume next =>
      rw [hstep] at stepRun
      obtain ⟨r, frameRun, -⟩ := stepRun
      unfold RunFrame at frameRun
      rw [henter] at frameRun
      obtain ⟨hxl, -⟩ := frameRun
      subst hxl
      cases retained
      simp [Exec.descendantFrames]
  | runOk hstep henter child hresume next =>
      have stepRun' := stepRun
      rw [hstep] at stepRun'
      obtain ⟨r, frameRun, -⟩ := stepRun'
      unfold RunFrame at frameRun
      rw [henter] at frameRun
      obtain ⟨raw', hxl, -⟩ := frameRun
      have commits := settles _ _ _ _ raw' hstep hxl
      subst hxl
      cases retained with
      | some run =>
          have rawEq := Exec.result_unique run child
          subst rawEq
          have runEq : run = child := Exec.unique _ _
          subst runEq
          have hraw := Frame.raw_commits_of_settlementCommits commits
          simp [commits, Exec.committedFrames, hraw]

/-- The retained accepted callback of one successful `exit` frame, carried by
the frame's actual `CALL` child: the actual-child twin of `ExitHandoff`. -/
structure ExitHandoffAt (coalition : Finset Adr) {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post)) where
  childMsg : Msg
  entry : Benv
  child : Devm
  xl : Xlot
  retained : ExecutionTrace.RetainedXlot xl
  process : ProcessMessage childMsg xl (.ok child)
  childClean : child.error.isSome = false
  entryTransfer : childMsg.benvAfterTransfer = .ok entry
  benvStat : childMsg.benv.stat = sevm.benvStat
  targetNe : childMsg.currentTarget ≠ sevm.currentTarget
  depth : (initSevm (childMsg.withBenv entry)).depth < sevm.depth
  childPre : dripEntrySpec.Pre sevm.currentTarget
    (initSevm (childMsg.withBenv entry)) (initDevm (childMsg.withBenv entry))
  effect : Effect scale.toNat freshNat
    (snapshot coalition sevm.currentTarget pre.state)
    (.exit (decide (sevm.caller ∈ coalition)) sevm.caller
      (Sevm.dataWord sevm (32 * 0 + 4)).toNat
      (exitPayoutOf scale.toNat (Sevm.dataWord sevm (32 * 0 + 4)).toNat
        (freshNat (chiN (Devm.getStor pre sevm.currentTarget))
          (sevm.benvStat.time -
            Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat))
      (sevm.benvStat.time -
        Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat)
    (snapshot coalition sevm.currentTarget entry.state)
  postSnapshot : snapshot coalition sevm.currentTarget post.state =
    snapshot coalition sevm.currentTarget child.state
  frames : Exec.descendantFrames exc = retained.settledFrames

theorem exit_exec_handoffAt (coalition : Finset Adr) {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = exitSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty)
    (precondition : dripEntrySpec.Pre sevm.currentTarget sevm pre)
    (caller_ne : sevm.caller ≠ sevm.currentTarget)
    (hfork : CoveredFork sevm.benvStat.fork) :
    Nonempty (ExitHandoffAt coalition exc) := by
  have full := exit_exec_effect_full exc hcode hsel hnonempty hcanon hfork
  unfold ExitPaysExactlyFull at full
  dsimp only at full
  rcases full with
    ⟨hargCap, -, -, hown, hfund, -, -, hclock, -, hguards, hnofm, hcapChi, -⟩
  have spine := exit_callNode_spine_of_exec exc hcode hsel hnonempty hcanon hfork
  dsimp only at spine
  rcases spine with
    ⟨node, -, isCall, -, sameFrame, storEq, codeEq, -, -, nodeFree, balEq,
      callPost, guardPost, returnPre, stepEq, accepted, postStor, postBal,
      afterNode, afterDevm, afterEdge, afterClean⟩
  rcases accepted with
    ⟨gasWord, xs, parent, child, xl, delegated, nextAddress, childCode, avail,
      acceptedPc, -, -, -, -, acceptedStep, hdepth, acceptedStack, parentState,
      -, -, -, -, filled, process, clean, -, callPostState, -, -, -⟩
  obtain ⟨handoff, handoffXl, handoffChild, handoffMsg⟩ :=
    exit_handoff_of_components coalition precondition caller_ne hargCap hown
      hfund hclock hguards hnofm hcapChi storEq codeEq balEq postStor postBal
      hdepth parentState filled process clean callPostState
  obtain ⟨retained⟩ := ExecutionTrace.exists_retainedXlot_of_filled filled
  have sevmEq : node.node.sevm = sevm := sameFrame.sevm_eq
  have nodeStep : Step.Run
      (Evm.step ⟨node.node.pc, node.node.sevm, node.node.devm⟩) xl
      (.ok afterNode.devm) := by
    have evmStep := Evm.step_next (devm := node.node.devm) node.decoded
    rw [isCall] at evmStep
    rw [evmStep, afterDevm, sevmEq]
    exact Ninst.stepRun_pc_irrel (n := call) rfl (pc' := node.node.pc)
      acceptedStep
  have settles : ∀ (frame : Jaune.Frame) (resume : Resume) (nextPc : Nat)
      (evm : Evm) (raw : Execution),
      Evm.step ⟨node.node.pc, node.node.sevm, node.node.devm⟩ =
        .spawn frame resume nextPc →
      xl = .some ⟨evm, raw⟩ → Frame.settlementCommits frame raw = true := by
    intro frame resume nextPc evm raw spawn slotEq
    have evmStep := Evm.step_next (devm := node.node.devm) node.decoded
    rw [isCall, sevmEq] at evmStep
    rw [sevmEq, evmStep] at spawn
    rcases Ninst.step_call_spawn_exact spawn acceptedStack hfork with
      ⟨spawnParent, spawnDelegated, spawnAddress, spawnCode, spawnAvail,
        -, -, -, -, -, frameEq, -⟩
    subst frameEq
    subst slotEq
    obtain ⟨-, settled⟩ := RunFrame.some_inv process
    unfold Frame.settlementCommits
    have key : ∀ m : Msg, m.benv.stat = sevm.benvStat →
        (Frame.ofCall m).settle raw = .ok child := fun m hm =>
      ofCall_settle_of_clean _ m settled.symm clean (by rw [hm]; rfl)
    rw [key]
    · cases hError : child.error <;> simp_all
    · rfl
  have frames : Exec.descendantFrames exc = retained.settledFrames := by
    have head := nodeFree.descendantFrames_eq
    have step := Exec.Deriv.descendantFrames_eq_of_stepRun afterEdge nodeStep
      settles retained
    have tail : Exec.descendantFrames afterNode.exc = [] :=
      Exec.descendantFrames_eq_nil_of_no_sameFrame_xinstAt afterNode.exc
        afterClean
    change Exec.descendantFrames exc = Exec.descendantFrames node.node.exc at head
    rw [head, step, tail, List.append_nil]
  subst handoffXl
  subst handoffChild
  exact ⟨{
    childMsg := handoff.childMsg
    entry := handoff.entry
    child := handoff.child
    xl := handoff.xl
    retained := retained
    process := handoff.process
    childClean := handoff.childClean
    entryTransfer := handoff.entryTransfer
    benvStat := handoff.benvStat
    targetNe := handoff.targetNe
    depth := handoff.depth
    childPre := handoff.childPre
    effect := handoff.effect
    postSnapshot := handoff.postSnapshot
    frames := frames }⟩

end Drip

end Blanc
