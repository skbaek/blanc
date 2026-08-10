import Blanc.Weth10AllowanceArmsRedeem

/-!
The ERC-677-style callback arms of the allowance-region transport.

`depositToAndCall`, `transferAndCall` and `approveAndCall` all commit a
state prefix inside their own frame and only then spawn the recipient's
`onTokenTransfer`/`onTokenApproval` callback, decoding its Boolean result
in a childless tail.  The frame's own counted record therefore comes
*first*, and the retained callback child's attribution stream follows it,
matching the chronological order in which the writes happened.

The module walks the original retained execution at the counted-cursor
altitude down to the callback `CALL`, crosses that spawn edge while
identifying its counted label with the retained child's attribution
stream, closes the Boolean decoder as a childless suffix, and transports
the allowance region across the child through the `ForallDeeperAt`
recursion hypothesis.  Only `approveAndCall` carries an allowance event;
the other two write balance-region keys alone.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Weth10

/-! ## Key shape -/

/-- A tagged allowance key is never an address-shaped balance key. -/
private theorem allowanceRegion_ne_validAdr {key k : B256}
    (hkey : InRegion .allowance key) (hvalid : ValidAdr k) : key ≠ k := by
  intro h
  rcases hvalid with ⟨a, ha⟩
  apply regions_disjoint (x := .allowance) (y := .balance) (by decide)
    key hkey
  rw [h, ← ha]
  simpa only [balanceKey] using balanceKey_region a

/-! ## Local copies of private compiled-module helpers

`Weth10HolderFlowCompiled` and `Weth10AttributionChronology` keep several
step-level facts private, so this module re-declares the ones it needs. -/

/-- The first instruction of a compiled `.next` block is installed at the
block's starting program counter. -/
private theorem ninstAt_of_subcode_next_callback
    {code : ByteArray} {table : List (Nat × Func)} {pc : Nat}
    {n : Ninst} {tail : Func}
    (sub : subcode code.toList pc
      (Func.compile table pc (.next n tail))) :
    Ninst.At code pc n := by
  rcases of_subcode sub with ⟨cd, hcode, hslice⟩
  rcases of_bind_eq_some hcode with ⟨rest, hrest, hprefix⟩
  simp [pure] at hprefix
  rw [← hprefix] at hslice
  exact Ninst.at_of_slice (List.slice_prefix hslice)

private theorem not_run_call_revWith
    {fs : List Func} {e : Sevm} {k : Nat} {reason : String}
    {final : Devm}
    (hget : fs[k]? = some (Func.revWith reason)) :
    ∀ pre, ¬ Func.Run fs e pre (.call k) final := by
  intro pre run
  rcases of_run_call run with ⟨body, bodyPre, hbody, _hburn, hrun⟩
  rw [hget] at hbody
  have heq : body = Func.revWith reason := Option.some.inj hbody.symm
  subst body
  exact Func.not_run_revWith hrun

/-- Slot and outcome uniqueness for a pc-free external instruction, allowing
the two witnesses to name different program counters. -/
private theorem Ninst.StepRun.unique_exec_of_filled
    {pc₁ pc₂ : Nat} {sevm : Sevm} {pre : Devm} {x : Xinst}
    {left right : Xlot} {out₁ out₂ : Execution}
    (hleftFilled : Xlot.Filled left)
    (hrightFilled : Xlot.Filled right)
    (hleft : Ninst.StepRun pc₁ sevm pre (.exec x) left out₁)
    (hright : Ninst.StepRun pc₂ sevm pre (.exec x) right out₂) :
    left = right ∧ out₁ = out₂ := by
  have hright' : Ninst.StepRun pc₁ sevm pre (.exec x) right out₂ :=
    Ninst.stepRun_pc_irrel (by simp [Ninst.pcFree]) hright
  unfold Ninst.StepRun at hleft hright'
  exact Blanc.Step.Run.unique_of_filled
    hleftFilled hrightFilled hleft hright'

private theorem genericCall_step_spawn_exact_callback
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isStatic : Bool}
    {ii isz oi osz : Nat} {code : ByteArray} {disablePrecompiles : Bool}
    {frame : Frame} {resume : Resume}
    (hspawn : genericCall.step sevm devm gas value caller target codeAddress
      stv isStatic ii isz oi osz code disablePrecompiles =
        .spawn frame resume) :
    frame = Frame.ofCall
      (callMsg sevm (devm.withReturnData []) gas value caller target
        codeAddress stv isStatic ((devm.memory.read ii isz).1) code
        disablePrecompiles) ∧
    resume = .call (devm.withReturnData []) oi osz := by
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hspawn
  repeat' split at hspawn
  all_goals
    simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hspawn
  all_goals obtain ⟨rfl, rfl⟩ := hspawn
  all_goals exact ⟨rfl, rfl⟩

private theorem Xinst.step_call_spawn_ofCall
    {sevm : Sevm} {devm : Devm} {frame : Frame} {resume : Resume}
    (hspawn : Xinst.step sevm devm .call = .spawn frame resume) :
    ∃ msg, frame = Frame.ofCall msg := by
  simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hspawn
  repeat' split at hspawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hspawn
  all_goals first
    | cases hspawn
    | exact ⟨_, (genericCall_step_spawn_exact_callback hspawn).1⟩

private theorem Ninst.step_call_spawn_ofCall
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {frame : Frame} {resume : Resume}
    (hspawn : Ninst.step ⟨pc, sevm, pre⟩ Ninst.call =
      .spawn frame resume pc') :
    ∃ msg, frame = Frame.ofCall msg := by
  have hx : Xinst.step sevm pre .call = .spawn frame resume := by
    exact XStep.toStep_spawn (by
      simpa only [Ninst.call, Ninst.step_exec] using hspawn)
  exact Xinst.step_call_spawn_ofCall hx

private theorem Frame.settlementCommits_ofCall_of_raw_commits
    {msg : Msg} {raw : Execution}
    (hraw : Execution.commits raw = true) :
    Blanc.Weth10.Frame.settlementCommits (Frame.ofCall msg) raw = true := by
  cases raw with
  | error err =>
      simp [Execution.commits] at hraw
  | ok post =>
      cases herror : post.error with
      | none =>
          simp [Blanc.Weth10.Frame.settlementCommits, Frame.settle,
            Frame.settleMsg, Frame.ofCall, executeCode.handleError,
            processMessage.settle, herror]
      | some error =>
          simp [Execution.commits, herror] at hraw

/-! ## Entry-observation helpers

Local copies of the compiled module's private `Devm.DispatchSilent`
combinators, consumed by the counted silent walk below. -/

private theorem Devm.DispatchSilent.refl (pre : Devm) :
    Devm.DispatchSilent pre pre :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem Devm.DispatchSilent.trans
    {pre mid post : Devm}
    (h₁ : Devm.DispatchSilent pre mid)
    (h₂ : Devm.DispatchSilent mid post) :
    Devm.DispatchSilent pre post :=
  ⟨h₁.state.trans h₂.state, h₁.memory.trans h₂.memory,
    h₁.logs.trans h₂.logs, h₁.output.trans h₂.output⟩

private theorem Devm.DispatchSilent.of_popBurnBy
    {words : List B256} {cost : Nat} {pre post : Devm}
    (h : Devm.PopBurnBy words cost pre post) :
    Devm.DispatchSilent pre post :=
  ⟨h.state, h.memory, h.logs, h.output⟩

private theorem Devm.DispatchSilent.of_burnBy
    {cost : Nat} {pre post : Devm}
    (h : Devm.BurnBy cost pre post) : Devm.DispatchSilent pre post :=
  ⟨h.state, h.memory, h.logs, h.output⟩

private theorem Devm.DispatchSilent.of_pushEq
    {e : Sevm} {pre post : Devm} {word : B256}
    (run : Line.Run e pre [Ninst.pushB256 word, Ninst.eq] post) :
    Devm.DispatchSilent pre post := by
  rcases Line.of_run_cons run with ⟨mid, hpush, rest⟩
  rcases Line.of_run_cons rest with ⟨last, heq, hnil⟩
  cases hnil
  have hburn := of_run_pushB256 hpush
  rcases of_run_reg heq with ⟨pc, heqCore⟩
  simp only [Rinst.run, Rinst.runCore] at heqCore
  obtain ⟨left, right, heqBurn⟩ :=
    Devm.diffBurn_of_applyBinary heqCore
  exact ⟨Line.of_inv Devm.state (by line_inv) run,
    Line.of_inv Devm.memory (by line_inv) run,
    hburn.logs.trans heqBurn.logs,
    hburn.output.trans heqBurn.output⟩

private theorem Devm.DispatchSilent.of_dupPushGt
    {e : Sevm} {pre post : Devm} {word : B256}
    (run : Line.Run e pre
      [Ninst.dup 0, Ninst.pushB256 word, Ninst.gt] post) :
    Devm.DispatchSilent pre post := by
  rcases Line.of_run_cons run with ⟨afterDup, hdup, restDup⟩
  rcases Line.of_run_cons restDup with ⟨afterPush, hpush, restPush⟩
  rcases Line.of_run_cons restPush with ⟨last, hgt, hnil⟩
  cases hnil
  rcases of_run_dup hdup with ⟨value, _hvalue, hdupBurn⟩
  have hpushBurn := of_run_pushB256 hpush
  rcases of_run_reg hgt with ⟨pc, hgtCore⟩
  simp only [Rinst.run, Rinst.runCore] at hgtCore
  obtain ⟨left, right, hgtBurn⟩ :=
    Devm.diffBurn_of_applyBinary hgtCore
  exact ⟨Line.of_inv Devm.state (by line_inv) run,
    Line.of_inv Devm.memory (by line_inv) run,
    hdupBurn.logs.trans (hpushBurn.logs.trans hgtBurn.logs),
    hdupBurn.output.trans (hpushBurn.output.trans hgtBurn.output)⟩

private theorem Devm.DispatchSilent.of_entryFlag
    {e : Sevm} {pre post : Devm}
    (run : Line.Run e pre [Ninst.calldatasize, Ninst.iszero] post) :
    Devm.DispatchSilent pre post := by
  rcases Line.of_run_cons run with ⟨mid, hsize, rest⟩
  rcases Line.of_run_cons rest with ⟨last, hzero, hnil⟩
  cases hnil
  exact ⟨(of_run_calldatasize hsize).state.trans
      (Ninst.Hinv.inv (f := Devm.state) hzero),
    Line.of_inv Devm.memory (by line_inv) run,
    (of_run_calldatasize hsize).logs.trans
      (Ninst.Hinv.inv (f := Devm.logs) hzero),
    (of_run_calldatasize hsize).output.trans
      (Ninst.Hinv.inv (f := Devm.output) hzero)⟩

private theorem Devm.DispatchSilent.of_callvalueFlag
    {e : Sevm} {pre post : Devm}
    (run : Line.Run e pre [Ninst.callvalue, Ninst.iszero] post) :
    Devm.DispatchSilent pre post := by
  rcases Line.of_run_cons run with ⟨mid, hvalue, rest⟩
  rcases Line.of_run_cons rest with ⟨last, hzero, hnil⟩
  cases hnil
  exact ⟨(of_run_callvalue hvalue).state.trans
      (Ninst.Hinv.inv (f := Devm.state) hzero),
    Line.of_inv Devm.memory (by line_inv) run,
    (of_run_callvalue hvalue).logs.trans
      (Ninst.Hinv.inv (f := Devm.logs) hzero),
    (of_run_callvalue hvalue).output.trans
      (Ninst.Hinv.inv (f := Devm.output) hzero)⟩

private theorem Devm.DispatchSilent.of_fsig
    {e : Sevm} {pre post : Devm}
    (run : Line.Run e pre fsig post) : Devm.DispatchSilent pre post := by
  unfold fsig cdl shiftRight at run
  rcases Line.of_run_cons run with ⟨s₁, q₁, run⟩
  rcases Line.of_run_cons run with ⟨s₂, q₂, run⟩
  rcases Line.of_run_cons run with ⟨s₃, q₃, run⟩
  rcases Line.of_run_cons run with ⟨last, q₄, hnil⟩
  cases hnil
  rcases of_run_reg q₄ with ⟨pc, hshrCore⟩
  simp only [Rinst.run, Rinst.runCore] at hshrCore
  obtain ⟨left, right, hshrBurn⟩ :=
    Devm.diffBurn_of_applyBinary hshrCore
  have hloadState : s₁.state = s₂.state := by
    rcases of_run_reg q₂ with ⟨loadPc, hloadCore⟩
    simp only [Rinst.run, Rinst.runCore] at hloadCore
    rcases Except.bind_eq_ok hloadCore with
      ⟨⟨offset, popped⟩, hpop, loadTail⟩
    rcases Except.bind_eq_ok loadTail with
      ⟨burned, hburn, hpush⟩
    exact (Devm.pop_of_pop hpop).state.trans
      ((Devm.burn_of_chargeGas hburn).state.trans
        (Devm.push_of_push hpush).state)
  exact ⟨(of_run_pushB256 q₁).state.trans
      (hloadState.trans
        ((of_run_pushB256 q₃).state.trans hshrBurn.state)),
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons q₁ (Line.Run.cons q₂
        (Line.Run.cons q₃ (Line.Run.cons q₄ Line.Run.nil)))),
    (of_run_pushB256 q₁).logs.trans
      ((Ninst.Hinv.inv (f := Devm.logs) q₂).trans
        ((of_run_pushB256 q₃).logs.trans hshrBurn.logs)),
    (of_run_pushB256 q₁).output.trans
      ((Ninst.Hinv.inv (f := Devm.output) q₂).trans
        ((of_run_pushB256 q₃).output.trans hshrBurn.output))⟩

/-! ## Counted silent walk to the selector body

The counted cursor machinery of `Weth10AttributionChronology` discards
entry-state observations, but the redemption arms must relate the tagged
allowance keys of the frame entry to the counted walk's own body cursor.
These are the counted mirrors of the compiled module's private silent
dispatch walk. -/

/-- Zero-branch selection preserving the empty counted prefix and the
entry observations. -/
private theorem Exec.Frame.CountedCursor.selectBranchZeroSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm} {stack : Stack}
    (cursor : frame.CountedCursor dp ca fs table
      (.branch left right) final)
    (hstack : (0 : B256) :: stack <<+ cursor.pre.stack) :
    ∃ arm : frame.CountedCursor dp ca fs table left final,
      stack <<+ arm.pre.stack ∧
      Devm.DispatchSilent cursor.pre arm.pre := by
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, _hlocEq, hloc, hpush, hjumpi, hsubLeft, hboundLeft,
      _hjumpdest, _hjumpable, _hsubRight, _hboundRight⟩
  have compiled := cursor.run
  cases compiled with
  | zero hroom hpop hleft =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      rcases Evm.branch_zero_steps hpush hjumpi hloc hroom hpop with
        ⟨hstepPush, hstepJumpi⟩
      rcases frame.advance_cont_counted cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases frame.advance_cont_counted afterPush hpPush hcPush
          hstepJumpi with
        ⟨armExec, hpArm, hcArm⟩
      exact ⟨⟨cursor.pc + 4, _, armExec, hpArm, hcArm, hleft,
        hsubLeft, hboundLeft⟩, hw.2,
        Devm.DispatchSilent.of_popBurnBy hpop⟩
  | succ hne _hroom hpop _hright =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      exact (hne hw.1).elim

/-- Nonzero-branch selection preserving the empty counted prefix and the
entry observations. -/
private theorem Exec.Frame.CountedCursor.selectBranchSuccSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm} {flag : B256} {stack : Stack}
    (cursor : frame.CountedCursor dp ca fs table
      (.branch left right) final)
    (hflag : flag ≠ 0)
    (hstack : flag :: stack <<+ cursor.pre.stack) :
    ∃ arm : frame.CountedCursor dp ca fs table right final,
      stack <<+ arm.pre.stack ∧
      Devm.DispatchSilent cursor.pre arm.pre := by
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, _hlocEq, hloc, hpush, hjumpi, _hsubLeft, _hboundLeft,
      hjumpdest, hjumpable, hsubRight, hboundRight⟩
  have compiled := cursor.run
  cases compiled with
  | zero _hroom hpop _hleft =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      exact (hflag hw.1.symm).elim
  | succ hne hroom hpop hright =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      rcases Evm.branch_succ_steps hpush hjumpi hjumpdest hjumpable
          hloc hne hroom hpop with
        ⟨hstepPush, hstepJumpi, hstepJumpdest⟩
      rcases frame.advance_cont_counted cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases frame.advance_cont_counted afterPush hpPush hcPush
          hstepJumpi with
        ⟨afterJump, hpJump, hcJump⟩
      rcases frame.advance_cont_counted afterJump hpJump hcJump
          hstepJumpdest with
        ⟨armExec, hpArm, hcArm⟩
      exact ⟨⟨loc + 1, _, armExec, hpArm, hcArm, hright,
        hsubRight, hboundRight⟩, hw.2,
        Devm.DispatchSilent.of_popBurnBy hpop⟩

/-- Select the fall-through arm when successful execution of the jumped
arm is impossible, retaining the compiled branch pop/burn relation; the
counted mirror of `Exec.Frame.CompiledCursor.selectBranchLeftWithBurn`. -/
private theorem Exec.Frame.CountedCursor.selectBranchLeftWithBurn
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm}
    (cursor : frame.CountedCursor dp ca fs table
      (.branch left right) final)
    (hnoRight : ∀ pre, ¬ Func.Run fs frame.sevm pre right final) :
    ∃ arm : frame.CountedCursor dp ca fs table left final,
      Devm.PopBurnBy [0] (gVerylow + gHigh) cursor.pre arm.pre := by
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, _hlocEq, hloc, hpush, hjumpi, hsubLeft, hboundLeft,
      _hjumpdest, _hjumpable, _hsubRight, _hboundRight⟩
  have compiled := cursor.run
  cases compiled with
  | zero hroom hpop hleft =>
      rcases Evm.branch_zero_steps hpush hjumpi hloc hroom hpop with
        ⟨hstepPush, hstepJumpi⟩
      rcases frame.advance_cont_counted cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases frame.advance_cont_counted afterPush hpPush hcPush
          hstepJumpi with
        ⟨armExec, hpArm, hcArm⟩
      exact ⟨⟨cursor.pc + 4, _, armExec, hpArm, hcArm, hleft,
        hsubLeft, hboundLeft⟩, hpop⟩
  | succ _hne _hroom _hpop hright =>
      exact absurd (Func.Run.of_runCompiled hright) (hnoRight _)

/-- A matching compiled dispatch leaf advances to its stored body while
preserving the empty counted prefix and the entry observations. -/
private theorem Exec.Frame.CountedCursor.reachDispatchLeafSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)} {final : Devm}
    {sig w : B256} {f body : Func} {k : Nat} {stack : Stack}
    (hmem : (sig, f) ∈ [(w, body)])
    (cursor : frame.CountedCursor dp ca fs table
      (dispatchWith k (.leaf w body)) final)
    (hstack : sig :: stack <<+ cursor.pre.stack) :
    ∃ bodyCursor : frame.CountedCursor dp ca fs table f final,
      stack <<+ bodyCursor.pre.stack ∧
      Devm.DispatchSilent cursor.pre bodyCursor.pre := by
  have heq : (sig, f) = (w, body) := List.mem_singleton.mp hmem
  injection heq with hsig hfun
  subst w
  subst body
  change frame.CountedCursor dp ca fs table
    ([Ninst.pushB256 sig, Ninst.eq] +++ (f <?> .call k)) final at cursor
  rcases cursor.peelChildlessLine
      (by simp [NinstIsChildless, Ninst.pushB256]) with
    ⟨branchCursor, hline⟩
  have hflag : (sig =? sig) :: stack <<+ branchCursor.pre.stack := by
    rcases Line.of_run_cons hline with ⟨afterPush, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨afterEq, heqRun, hnil⟩
    cases hnil
    have hpushed : sig :: sig :: stack <<+ afterPush.stack := by
      simpa using prefix_of_push (of_run_pushB256 hpush) hstack
    exact prefix_of_eq heqRun hpushed
  rw [show (sig =? sig) = 1 from by simp [B256.eqCheck]] at hflag
  rcases branchCursor.selectBranchSuccSilent
      (left := .call k) (right := f) (flag := (1 : B256))
      (by decide) hflag with
    ⟨bodyCursor, hbodyStack, hbranchSilent⟩
  exact ⟨bodyCursor, hbodyStack,
    (Devm.DispatchSilent.of_pushEq hline).trans hbranchSilent⟩

/-- Reach the selected body of a generated sorted dispatch tree while
keeping the empty counted prefix and the entry observations. -/
private theorem Exec.Frame.CountedCursor.reachDispatchWithSilent_build :
    ∀ {n : Nat} {xs : List (B256 × Func)} {sig : B256} {f : Func}
      {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
      {fs : List Func} {table : List (Nat × Func)} {k : Nat}
      {final : Devm} {stack : Stack},
      DispatchTree.sorted xs = true →
      xs.length ≤ n + 1 →
      (sig, f) ∈ xs →
      (cursor : frame.CountedCursor dp ca fs table
        (dispatchWith k (DispatchTree.build n xs)) final) →
      (sig :: stack <<+ cursor.pre.stack) →
      ∃ bodyCursor : frame.CountedCursor dp ca fs table f final,
        stack <<+ bodyCursor.pre.stack ∧
        Devm.DispatchSilent cursor.pre bodyCursor.pre := by
  intro n
  induction n with
  | zero =>
      intro xs sig f dp ca frame fs table k final stack _hsorted hlen hmem
        cursor hstack
      rcases xs with _ | ⟨⟨w, body⟩, _ | ⟨y, ys⟩⟩
      · cases hmem
      · exact cursor.reachDispatchLeafSilent hmem hstack
      · exfalso
        simp only [List.length_cons] at hlen
        omega
  | succ n ih =>
      intro xs sig f dp ca frame fs table k final stack hsorted hlen hmem
        cursor hstack
      rcases xs with _ | ⟨⟨w, body⟩, _ | ⟨y, ys⟩⟩
      · cases hmem
      · exact cursor.reachDispatchLeafSilent hmem hstack
      · simp only [List.length_cons] at hlen
        have htakeLen :
            (((w, body) :: y :: ys).take
              ((((w, body) :: y :: ys).length + 1) / 2)).length ≤
              n + 1 := by
          simp only [List.length_take, List.length_cons]
          omega
        have hdropLen :
            (((w, body) :: y :: ys).drop
              ((((w, body) :: y :: ys).length + 1) / 2)).length ≤
              n + 1 := by
          simp only [List.length_drop, List.length_cons]
          omega
        obtain ⟨z, zs, hdrop⟩ :
            ∃ z zs, ((w, body) :: y :: ys).drop
              ((((w, body) :: y :: ys).length + 1) / 2) = z :: zs := by
          rcases hd : ((w, body) :: y :: ys).drop
              ((((w, body) :: y :: ys).length + 1) / 2) with _ | ⟨z, zs⟩
          · exfalso
            have hl := congrArg List.length hd
            simp only [List.length_drop, List.length_cons,
              List.length_nil] at hl
            omega
          · exact ⟨z, zs, rfl⟩
        have hsortedSplit : DispatchTree.sorted
            (((w, body) :: y :: ys).take
                ((((w, body) :: y :: ys).length + 1) / 2) ++
              ((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2)) = true := by
          rw [List.take_append_drop]
          exact hsorted
        have hsortedTake := DispatchTree.sorted_append_left hsortedSplit
        have hsortedDrop := DispatchTree.sorted_append_right hsortedSplit
        have hmemSplit :
            (sig, f) ∈ ((w, body) :: y :: ys).take
                ((((w, body) :: y :: ys).length + 1) / 2) ∨
              (sig, f) ∈ ((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2) := by
          apply List.mem_append.mp
          rw [List.take_append_drop]
          exact hmem
        change frame.CountedCursor dp ca fs table
          ([Ninst.dup 0,
              Ninst.pushB256 (leftmostFsig
                (DispatchTree.build n
                  (((w, body) :: y :: ys).drop
                    ((((w, body) :: y :: ys).length + 1) / 2)))),
              Ninst.gt] +++
            (dispatchWith k
                (DispatchTree.build n
                  (((w, body) :: y :: ys).take
                    ((((w, body) :: y :: ys).length + 1) / 2))) <?>
              dispatchWith k
                (DispatchTree.build n
                  (((w, body) :: y :: ys).drop
                    ((((w, body) :: y :: ys).length + 1) / 2))))) final
          at cursor
        rcases cursor.peelChildlessLine
            (by simp [NinstIsChildless, Ninst.pushB256]) with
          ⟨branchCursor, hline⟩
        have hlineSilent := Devm.DispatchSilent.of_dupPushGt hline
        have hflagPrefix :
            (leftmostFsig (DispatchTree.build n
                (((w, body) :: y :: ys).drop
                  ((((w, body) :: y :: ys).length + 1) / 2))) >? sig) ::
              sig :: stack <<+ branchCursor.pre.stack := by
          rcases Line.of_run_cons hline with
            ⟨afterDup, hdup, hrestDup⟩
          rcases Line.of_run_cons hrestDup with
            ⟨afterPush, hpush, hrestPush⟩
          rcases Line.of_run_cons hrestPush with
            ⟨afterGt, hgt, hnil⟩
          cases hnil
          have hdupStack : sig :: sig :: stack <<+ afterDup.stack :=
            prefix_of_dup_val hdup (by show_nth) hstack
          have hpushStack :
              leftmostFsig (DispatchTree.build n
                  (((w, body) :: y :: ys).drop
                    ((((w, body) :: y :: ys).length + 1) / 2))) ::
                sig :: sig :: stack <<+ afterPush.stack := by
            simpa using prefix_of_push (of_run_pushB256 hpush) hdupStack
          exact prefix_of_gt hgt hpushStack
        have hleftmost :
            leftmostFsig (DispatchTree.build n
              (((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2))) = z.fst := by
          rw [hdrop, DispatchTree.leftmostFsig_build]
        rw [hleftmost] at hflagPrefix
        rcases hmemSplit with hmemTake | hmemDrop
        · have hlt : sig < z.fst := by
            have hz : z ∈ ((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2) := by
              rw [hdrop]
              exact List.mem_cons_self ..
            exact DispatchTree.fst_lt_of_sorted_append
              hsortedSplit hmemTake hz
          have hcheck : (z.fst >? sig) = 1 := by
            simp [B256.gtCheck, hlt]
          rw [hcheck] at hflagPrefix
          rcases branchCursor.selectBranchSuccSilent (flag := (1 : B256))
              (by decide) hflagPrefix with
            ⟨leftCursor, hleftStack, hbranchSilent⟩
          rcases ih hsortedTake htakeLen hmemTake leftCursor hleftStack with
            ⟨bodyCursor, hbodyStack, hbodySilent⟩
          exact ⟨bodyCursor, hbodyStack,
            (hlineSilent.trans hbranchSilent).trans hbodySilent⟩
        · have hle : z.fst ≤ sig := by
            have hsortedZ : DispatchTree.sorted (z :: zs) = true := by
              rw [← hdrop]
              exact hsortedDrop
            rw [hdrop] at hmemDrop
            exact DispatchTree.fst_le_of_sorted_mem hsortedZ hmemDrop
          have hcheck : (z.fst >? sig) = 0 := by
            simp [B256.gtCheck, not_lt_of_ge hle]
          rw [hcheck] at hflagPrefix
          rcases branchCursor.selectBranchZeroSilent hflagPrefix with
            ⟨rightCursor, hrightStack, hbranchSilent⟩
          rcases ih hsortedDrop hdropLen hmemDrop rightCursor hrightStack with
            ⟨bodyCursor, hbodyStack, hbodySilent⟩
          exact ⟨bodyCursor, hbodyStack,
            (hlineSilent.trans hbranchSilent).trans hbodySilent⟩

/-- Local copy of the compiled module's private burn-determinism fact. -/
private theorem Devm.eq_of_burnBy_callback
    {cost : Nat} {pre left right : Devm}
    (hleft : Devm.BurnBy cost pre left)
    (hright : Devm.BurnBy cost pre right) : left = right := by
  apply Devm.eq_of_proj
  · exact hleft.stack.symm.trans hright.stack
  · exact hleft.memory.symm.trans hright.memory
  · have hl := hleft.gasLeft
    have hr := hright.gasLeft
    omega
  · exact hleft.logs.symm.trans hright.logs
  · exact hleft.refundCounter.symm.trans hright.refundCounter
  · exact hleft.output.symm.trans hright.output
  · exact hleft.accountsToDelete.symm.trans hright.accountsToDelete
  · exact hleft.returnData.symm.trans hright.returnData
  · exact hleft.error.symm.trans hright.error
  · exact hleft.accessedAddresses.symm.trans hright.accessedAddresses
  · exact hleft.accessedStorageKeys.symm.trans hright.accessedStorageKeys
  · exact hleft.state.symm.trans hright.state
  · exact hleft.createdAccounts.symm.trans hright.createdAccounts
  · exact hleft.transientStorage.symm.trans hright.transientStorage

/-- The actual retained root execution, advanced past the runtime's entry
`JUMPDEST`, is a counted cursor at the WETH10 main body whose state
retains the frame-entry observations. -/
private theorem Exec.Frame.compiledMainCursorCountedSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca) :
    ∃ cursor : frame.CountedCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (weth10 dp).main frame.post,
      Devm.DispatchSilent frame.pre cursor.pre := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have hcode := context.invocation.2.2.2
      have hcompiled := Prog.runCompiled_of_exec e pre (weth10 dp) post
        (weth10_pcFree dp) run hcode
      rcases hcompiled with ⟨compiledMid, hcompiledBurn, hmain⟩
      have hget :
          (table 0 (((weth10 dp).main) :: weth10Aux))[0]? =
            some (0, (weth10 dp).main) := rfl
      rcases subcode_of_get?_eq_some hcode hget with ⟨hjumpdest, hsub⟩
      have hboundary : noPushBefore e.code 1 32 = true :=
        (Prog.jumpable_of_get?_table hcode hget).2
      rcases jumpdest_at_exact run hjumpdest with
        ⟨actualMid, continuation, hburn, hgas, _hprec⟩
      have hmid : actualMid = compiledMid :=
        Devm.eq_of_burnBy_callback (Devm.BurnBy.of_burn hburn hgas)
          hcompiledBurn
      subst compiledMid
      have hstep : Evm.step ⟨0, e, pre⟩ = .cont 1 actualMid :=
        Evm.jumpdest_cont hjumpdest (Devm.BurnBy.of_burn hburn hgas)
      have hrootPrefix : Exec.Deriv.ParentPrefixActions dp ca
          ⟨0, e, pre, .ok post, run⟩
          ⟨0, e, pre, .ok post, run⟩ [] :=
        Exec.Deriv.ParentPrefixActions.refl _
      have hrootCounted : Exec.Deriv.ParentPrefixCounted dp ca
          ⟨0, e, pre, .ok post, run⟩
          ⟨0, e, pre, .ok post, run⟩ [] :=
        Exec.Deriv.ParentPrefixCounted.refl _
      rcases Exec.Frame.advance_cont_counted
          (frame := ⟨0, e, pre, .ok post, run, committed⟩)
          run ⟨[], hrootPrefix⟩ hrootCounted hstep with
        ⟨actualContinuation, hentryPrefix, hentryCounted⟩
      exact ⟨⟨1, actualMid, actualContinuation, hentryPrefix,
        hentryCounted, hmain, hsub, hboundary⟩,
        Devm.DispatchSilent.of_burnBy
          (Devm.BurnBy.of_burn hburn hgas)⟩

/-- A successful authentic non-receive invocation reaches the counted
cursor for its exact listed selector body while retaining the frame-entry
observations; the counted mirror of
`Exec.Frame.compiledSelectorBodyCursorSilent`. -/
private theorem Exec.Frame.compiledSelectorBodyCursorCountedSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {body : Func}
    (context : frame.AuthenticContext dp ca)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hmem : (Sevm.selector frame.sevm, body) ∈ weth10Funcs dp) :
    ∃ bodyCursor : frame.CountedCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) body frame.post,
      Devm.DispatchSilent frame.pre bodyCursor.pre := by
  rcases frame.compiledMainCursorCountedSilent context with
    ⟨mainCursor, hmainSilent⟩
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    ([Ninst.calldatasize, Ninst.iszero] +++
      (receiveEther <?>
        (fsig +++ dispatchWith fallbackSlot (weth10Tree dp))))
    frame.post at mainCursor
  rcases mainCursor.peelChildlessLine
      (by simp [NinstIsChildless]) with
    ⟨entryBranchCursor, hentryLine⟩
  have hentrySilent := Devm.DispatchSilent.of_entryFlag hentryLine
  have hflagPrefix :
      [frame.sevm.data.length.toB256 =? 0] <<+
        entryBranchCursor.pre.stack := by
    rcases Line.of_run_cons hentryLine with
      ⟨afterSize, hsize, hrestSize⟩
    rcases Line.of_run_cons hrestSize with
      ⟨afterZero, hzero, hnil⟩
    cases hnil
    have hsizePrefix : [frame.sevm.data.length.toB256] <<+
        afterSize.stack :=
      prefix_of_push (of_run_calldatasize hsize) nil_pref
    exact prefix_of_iszero hzero hsizePrefix
  have hflagZero : (frame.sevm.data.length.toB256 =? 0) = 0 := by
    simp [B256.eqCheck, hnonempty]
  rw [hflagZero] at hflagPrefix
  rcases entryBranchCursor.selectBranchZeroSilent hflagPrefix with
    ⟨dispatchPrefixCursor, _hdispatchStack, hentryBranchSilent⟩
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (fsig +++ dispatchWith fallbackSlot (weth10Tree dp))
    frame.post at dispatchPrefixCursor
  rcases dispatchPrefixCursor.peelChildlessLine
      (by simp [fsig, cdl, shiftRight, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨dispatchCursor, hfsig⟩
  have hfsigSilent := Devm.DispatchSilent.of_fsig hfsig
  have hselectorPrefix : Sevm.selector frame.sevm :: [] <<+
      dispatchCursor.pre.stack :=
    prefix_of_fsig nil_pref hfsig
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (dispatchWith fallbackSlot
      (DispatchTree.ofSorted (weth10Funcs dp))) frame.post at dispatchCursor
  rcases dispatchCursor.reachDispatchWithSilent_build (weth10Funcs_sorted dp)
      (Nat.le_succ _) hmem hselectorPrefix with
    ⟨bodyCursor, _hbodyStack, hdispatchSilent⟩
  exact ⟨bodyCursor,
    hmainSilent.trans (hentrySilent.trans
      (hentryBranchSilent.trans (hfsigSilent.trans hdispatchSilent)))⟩

/-- A successful counted cursor at a nonpayable wrapper reaches its
guarded body while retaining the entry observations; the counted mirror
of `Exec.Frame.CompiledCursor.enterNonpayableSilent`. -/
private theorem Exec.Frame.CountedCursor.enterNonpayableSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {body : Func} {final : Devm}
    (cursor : frame.CountedCursor dp ca fs table
      (nonpayable body) final) :
    ∃ bodyCursor : frame.CountedCursor dp ca fs table body final,
      Devm.DispatchSilent cursor.pre bodyCursor.pre := by
  have hvalue : frame.sevm.value = 0 :=
    value_eq_zero_of_run_nonpayable
      (Func.Run.of_runCompiled cursor.run)
  change frame.CountedCursor dp ca fs table
    ([Ninst.callvalue, Ninst.iszero] +++ (body <?> Func.rev)) final
    at cursor
  rcases cursor.peelChildlessLine
      (by simp [NinstIsChildless]) with
    ⟨branchCursor, hline⟩
  have hlineSilent := Devm.DispatchSilent.of_callvalueFlag hline
  have hflagPrefix : [frame.sevm.value =? 0] <<+
      branchCursor.pre.stack := by
    rcases Line.of_run_cons hline with
      ⟨afterValue, hcallvalue, hrestValue⟩
    rcases Line.of_run_cons hrestValue with
      ⟨afterZero, hzero, hnil⟩
    cases hnil
    have hvaluePrefix : [frame.sevm.value] <<+ afterValue.stack :=
      prefix_of_push (of_run_callvalue hcallvalue) nil_pref
    exact prefix_of_iszero hzero hvaluePrefix
  rw [hvalue] at hflagPrefix
  have hone : ((0 : B256) =? 0) = 1 := by simp [B256.eqCheck]
  rw [hone] at hflagPrefix
  rcases branchCursor.selectBranchSuccSilent (flag := (1 : B256))
      (by decide) hflagPrefix with
    ⟨bodyCursor, _hbodyStack, hbranchSilent⟩
  exact ⟨bodyCursor, hlineSilent.trans hbranchSilent⟩

/-! ## Counted branch and `.call` traversal

Two further counted mirrors of the compiled cursor API, copied from
`Weth10AllowanceArmsSpend`: arbitrary branch selection and entry into a
generated internal source call. -/

/-- Select whichever branch arm the committed run actually took while
preserving the empty counted prefix; the counted mirror of
`Exec.Frame.CompiledCursor.selectBranch`. -/
private theorem Exec.Frame.CountedCursor.selectBranchSplit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm}
    (cursor : frame.CountedCursor dp ca fs table
      (.branch left right) final) :
    Nonempty (frame.CountedCursor dp ca fs table left final) ∨
      Nonempty (frame.CountedCursor dp ca fs table right final) := by
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, _hlocEq, hloc, hpush, hjumpi, hsubLeft, hboundLeft,
      hjumpdest, hjumpable, hsubRight, hboundRight⟩
  have compiled := cursor.run
  cases compiled with
  | zero hroom hpop hleft =>
      rcases Evm.branch_zero_steps hpush hjumpi hloc hroom hpop with
        ⟨hstepPush, hstepJumpi⟩
      rcases frame.advance_cont_counted cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases frame.advance_cont_counted afterPush hpPush hcPush
          hstepJumpi with
        ⟨armExec, hpArm, hcArm⟩
      exact Or.inl ⟨⟨cursor.pc + 4, _, armExec, hpArm, hcArm, hleft,
        hsubLeft, hboundLeft⟩⟩
  | succ hne hroom hpop hright =>
      rcases Evm.branch_succ_steps hpush hjumpi hjumpdest hjumpable
          hloc hne hroom hpop with
        ⟨hstepPush, hstepJumpi, hstepJumpdest⟩
      rcases frame.advance_cont_counted cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases frame.advance_cont_counted afterPush hpPush hcPush
          hstepJumpi with
        ⟨afterJump, hpJump, hcJump⟩
      rcases frame.advance_cont_counted afterJump hpJump hcJump
          hstepJumpdest with
        ⟨armExec, hpArm, hcArm⟩
      exact Or.inr ⟨⟨loc + 1, _, armExec, hpArm, hcArm, hright,
        hsubRight, hboundRight⟩⟩

/-- Follow one generated internal source call while preserving the empty
counted prefix; the counted mirror of
`Exec.Frame.CompiledCursor.enterCall`. -/
private theorem Exec.Frame.CountedCursor.enterCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {k : Nat} {final : Devm}
    (cursor : frame.CountedCursor dp ca (f₀ :: aux)
      (table 0 (f₀ :: aux)) (.call k) final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩) :
    ∃ body,
      (f₀ :: aux)[k]? = some body ∧
      Nonempty (frame.CountedCursor dp ca (f₀ :: aux)
        (table 0 (f₀ :: aux)) body final) := by
  cases hrun : cursor.run with
  | call hget hroom hburn hbody =>
      rcases subcode_compile_call cursor.codeSlice with
        ⟨loc, p, hgetTable, hloc, hpushAt, hjump⟩
      have hpf := (Prog.get?_table (m := 0)).symm.trans
        (congrArg (Prod.snd <$> ·) hgetTable)
      rw [hget] at hpf
      simp only [Option.map_eq_map, Option.map_some,
        Option.some.injEq] at hpf
      subst p
      rcases subcode_of_get?_eq_some hcode hgetTable with
        ⟨hjumpdest, hsub⟩
      have hjumpable := Prog.jumpable_of_get?_table hcode hgetTable
      rcases hpushAt with ⟨le, hpush⟩
      rcases Evm.call_steps (le := le) hpush hjump hjumpdest
          hjumpable.1 hloc hroom hburn with
        ⟨hstepPush, hstepJump, hstepJumpdest⟩
      rcases frame.advance_cont_counted cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases frame.advance_cont_counted afterPush hpPush hcPush
          hstepJump with
        ⟨afterJump, hpJump, hcJump⟩
      rcases frame.advance_cont_counted afterJump hpJump hcJump
          hstepJumpdest with
        ⟨bodyExec, hpBody, hcBody⟩
      exact ⟨_, hget, ⟨⟨loc + 1, _, bodyExec, hpBody, hcBody, hbody,
        hsub, hjumpable.2⟩⟩⟩

/-! ## Crossing the retained callback `CALL`

The counted cursor API stops at childless instructions, so this section
adds the one labelled crossing the callback arms need: an exact source
`CALL` whose retained child commits contributes precisely that child's
attribution stream, and nothing else. -/

/-- The counted label of an exact source `CALL` edge is precisely the
retained raw child's attribution stream; the counted mirror of
`Exec.Deriv.ParentStepActions.selected_eq_retained_of_call`. -/
private theorem Exec.Deriv.ParentStepActions.counted_of_call
    {dp : DeployParams} {ca : Adr}
    {pc nextPc : Nat} {sevm : Sevm} {pre post : Devm} {out : Execution}
    {current : Exec pc sevm pre out}
    {continuation : Exec nextPc sevm post out}
    {xl : Xlot} {selected : List FlowAction}
    (hat : Ninst.At sevm.code pc Ninst.call)
    (filled : xl.Filled)
    (step : Ninst.StepRun pc sevm pre Ninst.call xl (.ok post))
    (retained : RetainedXlot xl)
    (commits : retained.RawCommits)
    (edge : Exec.Deriv.ParentStepActions dp ca
      ⟨nextPc, sevm, post, out, continuation⟩
      ⟨pc, sevm, pre, out, current⟩ selected) :
    Exec.Deriv.ParentStepCounted dp ca
      ⟨nextPc, sevm, post, out, continuation⟩
      ⟨pc, sevm, pre, out, current⟩
      (retained.attributionStream dp ca) := by
  cases edge with
  | cont hstep =>
      have hs := (Evm.step_next hat).symm.trans hstep
      have actual :
          Ninst.StepRun pc sevm pre Ninst.call .none (.ok post) := by
        simp only [Ninst.StepRun, hs, Step.Run]
        exact ⟨trivial, trivial⟩
      have hslot := (Ninst.StepRun.unique_exec_of_filled
        filled (show Xlot.Filled .none from trivial) step actual).1
      subst xl
      cases retained
      exact .cont hstep continuation
  | doneOk hstep henter hresume =>
      have hs := (Evm.step_next hat).symm.trans hstep
      have actual :
          Ninst.StepRun pc sevm pre Ninst.call .none (.ok post) := by
        simp only [Ninst.StepRun, hs, Step.Run]
        exact ⟨_, RunFrame.of_done henter, hresume.symm⟩
      have hslot := (Ninst.StepRun.unique_exec_of_filled
        filled (show Xlot.Filled .none from trivial) step actual).1
      subst xl
      cases retained
      exact .doneOk hstep henter hresume continuation
  | runOk hstep henter child hresume =>
      rename_i spawned resume childEvm raw
      have hs := (Evm.step_next hat).symm.trans hstep
      have actual :
          Ninst.StepRun pc sevm pre Ninst.call
            (.some ⟨childEvm, raw⟩) (.ok post) := by
        simp only [Ninst.StepRun, hs, Step.Run]
        exact ⟨_, RunFrame.of_run henter, hresume.symm⟩
      have actualFilled : Xlot.Filled (.some ⟨childEvm, raw⟩) := ⟨child⟩
      have hslot := (Ninst.StepRun.unique_exec_of_filled
        filled actualFilled step actual).1
      subst xl
      cases retained with
      | some retainedRun =>
          have hrun : retainedRun = child := Subsingleton.elim _ _
          subst retainedRun
          rcases Ninst.step_call_spawn_ofCall hs with ⟨msg, rfl⟩
          have hrawCommits : Execution.commits raw = true := commits
          have hcommit : Blanc.Weth10.Frame.settlementCommits
              (Frame.ofCall msg) raw = true :=
            Frame.settlementCommits_ofCall_of_raw_commits hrawCommits
          have hlabel : RetainedXlot.attributionStream dp ca
              (RetainedXlot.some child) =
              (if h : Blanc.Weth10.Frame.settlementCommits
                    (Frame.ofCall msg) raw = true then
                Exec.frameContribution dp ca
                  (Exec.Frame.ofRun child
                    (Blanc.Weth10.Frame.raw_commits_of_settlementCommits h))
                  (Exec.attributionInner dp ca child)
              else []) := by
            simp [RetainedXlot.attributionStream, Exec.attributionStream,
              hrawCommits, hcommit]
          rw [hlabel]
          exact .runOk hstep henter child hresume continuation

/-- Cross an exact source `CALL` whose retained child commits: the frame's
counted stream splits at precisely that child's attribution stream, and the
continuation carries the compiled tail. -/
private theorem Exec.Frame.CountedCursor.crossCommittedCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {tail : Func} {final rawPost : Devm}
    {rawSlot : Xlot} {rawPc : Nat}
    (cursor : frame.CountedCursor dp ca fs table
      (.next Ninst.call tail) final)
    (rawFilled : rawSlot.Filled)
    (rawStep : Ninst.StepRun rawPc frame.sevm cursor.pre
      Ninst.call rawSlot (.ok rawPost))
    (retained : RetainedXlot rawSlot)
    (commits : retained.RawCommits) :
    ∃ (tailPc : Nat) (next : Exec tailPc frame.sevm rawPost frame.out),
      Exec.attributionInner dp ca frame.run =
        retained.attributionStream dp ca ++
          Exec.attributionInner dp ca next ∧
      Func.RunCompiled fs frame.sevm rawPost tail final ∧
      subcode frame.sevm.code.toList tailPc
        (Func.compile table tailPc tail) ∧
      noPushBefore frame.sevm.code tailPc 32 = true := by
  have compiled := cursor.run
  cases compiled with
  | next hcompiled htail =>
      have hat : Ninst.At frame.sevm.code cursor.pc Ninst.call :=
        ninstAt_of_subcode_next_callback cursor.codeSlice
      rcases cursor.parentPrefix with ⟨before, hbefore⟩
      rcases frame.advance_runCompiled_next cursor.current hbefore hat
          hcompiled with
        ⟨_xl, continuation, _selected, _occurrence, hedge, _hnextPrefix⟩
      rcases hcompiled with ⟨actualSlot, actualFilled, hsteps⟩
      have halign := Ninst.StepRun.unique_exec_of_filled
        rawFilled actualFilled rawStep (hsteps cursor.pc)
      have hslot : rawSlot = actualSlot := halign.1
      subst rawSlot
      have hpost : rawPost = _ := Except.ok.inj halign.2
      subst rawPost
      have hcountedEdge := hedge.counted_of_call hat actualFilled
        (hsteps cursor.pc) retained commits
      obtain ⟨nextBoundary, nextSub⟩ :=
        Func.noPushBefore_next cursor.codeSlice cursor.codeBoundary
      refine ⟨cursor.pc + Ninst.call.size, continuation, ?_, htail,
        nextSub, nextBoundary⟩
      have hp := cursor.countedPrefix.descendantCounted_eq
      have hq := hcountedEdge.descendantCounted_eq
      simp only [Exec.Deriv.descendantCounted, List.nil_append] at hp hq
      rw [hp, hq]

/-! ## Reaching the callback `CALL` at the counted altitude -/

/-- Reach the ERC-677 `CALL` from a counted cursor at the generated
callback body, retaining the exact successful source prefix facts; the
counted mirror of
`Exec.Frame.CompiledCursor.reachCallBoolCallbackWithPrefix`. -/
private theorem Exec.Frame.CountedCursor.reachCallBoolCallbackCounted
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {table : List (Nat × Func)}
    {sel targetArg dataArg valueWord : B256} {value : Line}
    {final : Devm} {img : Bytes}
    (cursor : frame.CountedCursor dp ca (f₀ :: aux) table
      (callBoolCallback sel targetArg dataArg value) final)
    (hvalueChildless : ∀ n ∈ value, NinstIsChildless n)
    (h_value_stack : ∀ {a b : Devm} {xs : Stack},
      xs <<+ a.stack → Line.Run frame.sevm a value b →
        valueWord :: xs <<+ b.stack)
    (h_value_stor : Line.Inv Devm.getStor value)
    (h_value_bal : Line.Inv Devm.getBal value)
    (h_value_code : Line.Inv Devm.getCode value)
    (h_value_mem : Line.Inv Devm.memory value)
    (h_value_logs : Line.Inv Devm.logs value)
    (h_value_output : Line.Inv Devm.output value)
    (h_wf : Mem.Wf cursor.pre.memory)
    (h_reads : Mem.Reads cursor.pre.memory img) :
    ∃ callCursor : frame.CountedCursor dp ca (f₀ :: aux) table
        (.next Ninst.call (.call boolReturnSlot)) final,
      RawTokenCallbackCallPrefix frame.sevm sel targetArg dataArg valueWord
        img cursor.pre callCursor.pre := by
  unfold callBoolCallback at cursor
  rcases cursor.peelChildlessLine
      (line := arg targetArg ++
        [Ninst.dup 0, Ninst.extcodesize, Ninst.iszero])
      (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨branchCursor, hcheck⟩
  rcases branchCursor.selectBranchLeftWithBurn (fun _ => not_run_rev) with
    ⟨successCursor, hpopCheck⟩
  rcases successCursor.selectNextChildless (by simp [NinstIsChildless]) with
    ⟨valueCursor, hpop⟩
  rcases valueCursor.peelChildlessLine hvalueChildless with
    ⟨headCursor, hvalueRun⟩
  rcases headCursor.peelChildlessLine
      (line := storeTokenCallbackHead sel)
      (by simp [storeTokenCallbackHead, mstoreAt, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨zerosCursor, hhead⟩
  rcases zerosCursor.peelChildlessLine
      (line := pushList [0, 0])
      (by simp [pushList, NinstIsChildless, Ninst.pushB256]) with
    ⟨tailCursor, hzeros⟩
  rcases tailCursor.peelChildlessLine
      (line := forwardArgTail dataArg 4)
      (by simp [forwardArgTail, arg, cdl, mstoreAt, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨sizeCursor, htailRun⟩
  rcases sizeCursor.peelChildlessLine
      (line := tokenCallbackArgsSize)
      (by simp [tokenCallbackArgsSize, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨offsetCursor, hsize⟩
  rcases offsetCursor.peelChildlessLine
      (line := [Ninst.pushB256 callbackArgsOffset, Ninst.pushB256 0])
      (by simp [NinstIsChildless, Ninst.pushB256]) with
    ⟨targetCursor, hoffsets⟩
  rcases targetCursor.peelChildlessLine
      (line := arg targetArg)
      (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨gasCursor, htargetRun⟩
  rcases gasCursor.selectNextChildless (by simp [NinstIsChildless]) with
    ⟨callCursor, hgas⟩
  exact ⟨callCursor, rawTokenCallbackCallPrefix_of_runs
    sel targetArg dataArg valueWord value h_value_stack h_value_stor
    h_value_bal h_value_code h_value_mem h_value_logs h_value_output
    h_wf h_reads hcheck (Devm.PopBurn.of_popBurnBy hpopCheck) hpop
    hvalueRun hhead hzeros htailRun hsize hoffsets htargetRun hgas⟩

/-! ## The Boolean decoder tail

Packaged over the post-`CALL` continuation as its own retained frame, the
Boolean decoder contributes no counted records: its bubble and short
returndata arms cannot reach a committed final state, and its decode arm
is a childless line ending in `RETURN`. -/

private theorem Exec.attributionInner_eq_nil_of_boolReturnTail
    {dp : DeployParams} {ca : Adr}
    {fsevm : Sevm} {pcT : Nat} {midD final : Devm} {out : Execution}
    (next : Exec pcT fsevm midD out)
    (committed : Execution.commits out = true)
    (htail : Func.RunCompiled ((weth10 dp).main :: weth10Aux) fsevm midD
      (.call boolReturnSlot) final)
    (hsub : subcode fsevm.code.toList pcT
      (Func.compile (table 0 ((weth10 dp).main :: weth10Aux)) pcT
        (.call boolReturnSlot)))
    (hbound : noPushBefore fsevm.code pcT 32 = true)
    (hcode : some fsevm.code.toList = Prog.compile (weth10 dp)) :
    Exec.attributionInner dp ca next = [] := by
  let tailFrame : Exec.Frame := ⟨pcT, fsevm, midD, out, next, committed⟩
  let tailCursor : Exec.Frame.CountedCursor dp ca tailFrame
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (.call boolReturnSlot) final :=
    ⟨pcT, midD, next, ⟨[], Exec.Deriv.ParentPrefixActions.refl _⟩,
      Exec.Deriv.ParentPrefixCounted.refl _, htail, hsub, hbound⟩
  rcases tailCursor.enterCall hcode with ⟨body, hget, ⟨bodyCursor⟩⟩
  have hbody : body = boolReturn := by
    simpa [weth10, weth10Aux, boolReturnSlot] using hget.symm
  subst body
  unfold boolReturn at bodyCursor
  rcases bodyCursor.selectNextChildless (by simp [NinstIsChildless]) with
    ⟨firstBranchCursor, -⟩
  rcases firstBranchCursor.selectBranchSplit with hdecode | hbubble
  · rcases hdecode with ⟨decodePrefixCursor⟩
    rcases decodePrefixCursor.peelChildlessLine
        (line := retdataShorterThan 32)
        (by simp [retdataShorterThan, NinstIsChildless,
          Ninst.pushB256]) with
      ⟨secondBranchCursor, -⟩
    rcases secondBranchCursor.selectBranchSplit with hreturn | hrev
    · rcases hreturn with ⟨returnCursor⟩
      change Exec.Frame.CountedCursor dp ca tailFrame
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        ((pushList [32, 0, 0] ++
          [Ninst.retdatacopy, Ninst.pushB256 0, Ninst.mload,
            Ninst.iszero, Ninst.iszero] ++
          mstoreAt 0 ++ pushList [32, 0]) +++ Func.ret) final
        at returnCursor
      rcases returnCursor.peelChildlessLine
          (by simp [pushList, mstoreAt, NinstIsChildless,
            Ninst.pushB256]) with
        ⟨lastCursor, -⟩
      exact lastCursor.finishAttributionInner
    · rcases hrev with ⟨revCursor⟩
      exact absurd (Func.Run.of_runCompiled revCursor.run) not_run_rev
  · rcases hbubble with ⟨bubbleCursor⟩
    rcases bubbleCursor.enterCall hcode with
      ⟨bubbleBody, hbubbleGet, ⟨bubbleBodyCursor⟩⟩
    have hb : bubbleBody = bubbleRevert := by
      simpa [weth10, weth10Aux, bubbleRevertSlot] using hbubbleGet.symm
    subst bubbleBody
    exact (not_run_bubbleRevert
      (Func.Run.of_runCompiled bubbleBodyCursor.run)).elim

/-! ## The counted callback chronology -/

/-- Exact counted chronology for one generated ERC-677 callback: the raw
callback boundary and the retained child whose attribution stream is
precisely the frame's whole proper-descendant counted stream.  The counted
mirror of `Exec.Frame.CompiledCursor.compiledTokenCallbackChronology`. -/
private theorem Exec.Frame.CountedCursor.countedTokenCallbackChronology
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {sel targetArg dataArg valueWord : B256} {value : Line} {img : Bytes}
    (cursor : frame.CountedCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (callBoolCallback sel targetArg dataArg value) frame.post)
    (hvalueChildless : ∀ n ∈ value, NinstIsChildless n)
    (h_value_stack : ∀ {a b : Devm} {xs : Stack},
      xs <<+ a.stack → Line.Run frame.sevm a value b →
        valueWord :: xs <<+ b.stack)
    (h_value_stor : Line.Inv Devm.getStor value)
    (h_value_bal : Line.Inv Devm.getBal value)
    (h_value_code : Line.Inv Devm.getCode value)
    (h_value_mem : Line.Inv Devm.memory value)
    (h_value_logs : Line.Inv Devm.logs value)
    (h_value_output : Line.Inv Devm.output value)
    (h_wf : Mem.Wf cursor.pre.memory)
    (h_reads : Mem.Reads cursor.pre.memory img)
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp)) :
    ∃ (inputSize : B256) (input : Bytes)
        (callPre callPost parent child : Devm) (xl : Xlot) (pc : Nat)
        (retained : RetainedXlot xl),
      RawTokenCallbackIndexedStepBoundary dp frame.sevm
        frame.sevm.currentTarget (Sevm.argWord frame.sevm targetArg).toAdr
        (Sevm.argWord frame.sevm targetArg) sel valueWord
        (Sevm.tailLen frame.sevm dataArg) inputSize
        (Sevm.tailBytes frame.sevm dataArg) input cursor.pre frame.post
        callPre callPost parent child xl pc ∧
      Exec.attributionInner dp ca frame.run =
        retained.attributionStream dp ca := by
  rcases cursor.reachCallBoolCallbackCounted hvalueChildless h_value_stack
      h_value_stor h_value_bal h_value_code h_value_mem h_value_logs
      h_value_output h_wf h_reads with
    ⟨callCursor, hprefix⟩
  have compiled := callCursor.run
  cases compiled with
  | next hcallCompiled hboolCompiled =>
      have hcall := Ninst.Run.of_runCompiled hcallCompiled
      have hbool := Func.Run.of_runCompiled hboolCompiled
      rcases rawTokenCallbackIndexedStepBoundary_of_prefix dp sel
          targetArg dataArg valueWord hprefix hcall hbool with
        ⟨inputSize, input, parent, child, xl, pc, hraw⟩
      have hrawData := hraw
      rcases hrawData with
        ⟨_htargetEq, _hsize, _delegated, _code, _gasWord, _avail, hstep,
          _hdepth, _hstack, _hinput, _himage, _hstor, _hbal, _hcodePre,
          _hlogs, _houtput, _hparentState, _hparentMemory, _hparentLogs,
          _hparentOutput, _hdelegation, hfilled, hmessage, hclean,
          _hresume, _hcallPostState, _hreturnData, _hmemory,
          _hcallPostStack, _hcontinuation⟩
      obtain ⟨retained⟩ := exists_retainedXlot_of_filled hfilled
      have hcommits : retained.RawCommits := by
        cases retained with
        | none => trivial
        | some retainedRun =>
            exact Frame.raw_commits_of_settlementCommits
              (ProcessMessage.settlementCommits_of_some_ok_clean
                hmessage hclean)
      rcases callCursor.crossCommittedCall hfilled hstep retained
          hcommits with
        ⟨tailPc, tailExec, hsplit, htailRun, htailSub, htailBound⟩
      have htailNil : Exec.attributionInner dp ca tailExec = [] :=
        Exec.attributionInner_eq_nil_of_boolReturnTail tailExec
          frame.committed htailRun htailSub htailBound hcode
      exact ⟨inputSize, input, callCursor.pre, _, parent, child, xl, pc,
        retained, hraw, by rw [hsplit, htailNil, List.append_nil]⟩

/-! ## Allowance transport across the retained callback -/

/-- Exact allowance-region effect of a retained ERC-677 callback boundary;
the allowance mirror of
`RawTokenCallbackIndexedStepBoundary.storageSegmentEffect`.  The supplied
retained witness is the one selected by the enclosing counted execution, so
the resulting ledger is definitionally that exact slot's stream. -/
private theorem RawTokenCallbackIndexedStepBoundary.allowanceRegionEffect
    {dp : DeployParams} {ca : Adr} {e : Sevm}
    {self target : Adr}
    {rawTarget sel value tailLen inputSize : B256} {tail input : Bytes}
    {pre post callPre callPost parent child : Devm} {xl : Xlot}
    {pc : Nat}
    (callback : RawTokenCallbackIndexedStepBoundary dp e self target
      rawTarget sel value tailLen inputSize tail input pre post callPre
      callPost parent child xl pc)
    (retained : RetainedXlot xl)
    (hself : e.currentTarget = ca)
    (installed : some (pre.getCode ca).toList = Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt e.depth ca (weth10 dp)
      (fun pc sevm childPre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm childPre out)) :
    AllowanceRegionEffect ca pre post
      (retained.attributionStream dp ca) := by
  rcases callback with
    ⟨_targetEq, _inputSizeEq, delegated, code, gasWord, avail, _hstep,
      hdepth, _hstack, _hinput, _himage, hstorPre, _hbalPre, hcodePre,
      _hlogsPre, _houtputPre, hparentState, _hparentMemory, _hparentLogs,
      _hparentOutput, hdelegation, _hfilled, hprocess, _hclean, _hresume,
      hcallPostState, _hreturnData, _hcallPostMemory, _hcallPostStack,
      hcontinuation⟩
  let msg := callMsg e parent (min gasWord.toNat (except64th avail)) 0
    self target target true false input code delegated
  let trace : ProcessMessageTrace msg (.ok child) :=
    ⟨xl, retained, by simpa only [msg] using hprocess⟩
  have hcallPreCode : some (callPre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← congrFun hcodePre ca]
    exact installed
  have hparent : callPre.state = msg.benv.state := by
    simpa only [msg, callMsg] using hparentState.symm
  have hmsgDepth : msg.depth < e.depth := by
    dsimp only [msg, callMsg]
    omega
  have htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp) := by
    intro htarget
    have htargetCa : target = ca := by
      simpa only [msg, callMsg] using htarget
    exact callbackCode_eq_compiled_of_target_eq hcallPreCode htargetCa
      hdelegation
  have htargetDirect : msg.currentTarget = ca →
      msg.codeAddress = some ca := by
    intro htarget
    have htargetCa : target = ca := by
      simpa only [msg, callMsg] using htarget
    simp [msg, callMsg, htargetCa]
  have childEffect := trace.allowanceRegionDelta_of_forallDeeperAt hparent
    hmsgDepth hcallPreCode htargetCode htargetDirect hdeeper
  have hprefix := AllowanceRegionEffect.of_getStorCode_eq
    (congrFun hstorPre ca) (congrFun hcodePre ca)
  have hchildToCallPost := AllowanceRegionEffect.of_getStorCode_eq
    (congrArg (fun state : State => state.getStor ca) hcallPostState.symm)
    (congrArg (fun state : State => state.getCode ca) hcallPostState.symm)
  obtain ⟨htailStor, _, htailCode⟩ :=
    of_run_call_boolReturn_preserves_fields dp hcontinuation
  have hsuffix := AllowanceRegionEffect.of_getStorCode_eq
    (congrFun htailStor ca) (by simpa only [hself] using htailCode)
  have combined := hprefix.append
    (childEffect.append (hchildToCallPost.append hsuffix))
  simpa only [List.nil_append, List.append_nil, trace] using combined

/-! ## The `depositToAndCall` arm -/

/-- `depositToAndCall` transports the allowance region.  Its committed
prefix mints at one normalized address-shaped balance key and its own
record carries no allowance event, so that record replays transparently
ahead of the retained callback child's attribution stream. -/
theorem Exec.Frame.allowanceRegionEffect_of_depositToAndCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = depositToAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmem : (Sevm.selector frame.sevm, depositToAndCall) ∈
      weth10Funcs dp := by
    rw [hselector]
    simp [depositToAndCallSelector, weth10Funcs]
  rcases frame.compiledSelectorBodyCursorCountedSilent context hnonempty
      hmem with
    ⟨bodyCursor, hentrySilent⟩
  unfold depositToAndCall at bodyCursor
  rcases bodyCursor.peelChildlessLine
      (line := mintToPrefix)
      (by simp [mintToPrefix, addressArg, arg, cdl, normalizeAddress,
        pushAddressMask, mstoreAt, logWith, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨callbackCursor, hmint⟩
  have hwfBody : Mem.Wf bodyCursor.pre.memory := by
    rw [← hentrySilent.memory]
    exact context.memory_wf
  have hreadsBody : Mem.Reads bodyCursor.pre.memory [] := by
    rw [← hentrySilent.memory]
    exact context.memory_reads_empty
  rcases mintToPrefix_effect hwfBody hreadsBody hmint with
    ⟨hstor, _hlogs, _hbal, hcodeMint, _houtput⟩
  rcases mintToPrefix_callbackMemoryFrame hwfBody hreadsBody hmint with
    ⟨hwfCallback, hreadsCallback⟩
  rcases callbackCursor.countedTokenCallbackChronology
      (sel := onTokenTransferSelector) (targetArg := 0) (dataArg := 1)
      (valueWord := frame.sevm.value) (value := [Ninst.callvalue])
      (img := frame.sevm.value.toBytes)
      (by simp [NinstIsChildless])
      (by
        intro a b xs hp hline
        rcases Line.of_run_cons hline with ⟨c, hcv, hnil⟩
        cases hnil
        exact prefix_of_push (of_run_callvalue hcv) hp)
      (by line_inv) (by line_inv) (by line_inv) (by line_inv)
      (by
        intro e' a b hline
        rcases Line.of_run_cons hline with ⟨c, hcv, hnil⟩
        cases hnil
        exact (of_run_callvalue hcv).logs)
      (by
        intro e' a b hline
        rcases Line.of_run_cons hline with ⟨c, hcv, hnil⟩
        cases hnil
        exact (of_run_callvalue hcv).output)
      hwfCallback hreadsCallback context.invocation.2.2.2 with
    ⟨_inputSize, _input, _callPre, _callPost, _parent, _child, _xl, _pc,
      retained, callback, hinner⟩
  have htarget : frame.sevm.currentTarget = ca := context.invocation.2.1
  have hstorEntry : Devm.getStor frame.pre = Devm.getStor bodyCursor.pre :=
    funext (getStor_eq_of_state_eq hentrySilent.state)
  have hcodeEntry : Devm.getCode frame.pre = Devm.getCode bodyCursor.pre :=
    funext (getCode_eq_of_state_eq hentrySilent.state)
  have hcodeCallback : Devm.getCode frame.pre ca =
      Devm.getCode callbackCursor.pre ca :=
    (congrFun hcodeEntry ca).trans (congrFun hcodeMint ca).symm
  have installedCallback : some (callbackCursor.pre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← hcodeCallback]
    exact context.installed.1
  have childEffect := callback.allowanceRegionEffect retained htarget
    installedCallback hdeeper
  have hneFlash : depositToAndCallSelector ≠ flashLoanSelector := by
    decide +kernel
  have hsel : Sevm.selector frame.sevm = depositToAndCallSelector :=
    hselector
  have hnotflash : isFlashInvocation frame.sevm = false := by
    simp [isFlashInvocation, hsel, hneFlash]
  have hframeEq : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      CountedFrame.ofFrame dp ca frame ::
        retained.attributionStream dp ca := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframeEq, hinner,
      Exec.frameContribution_eq_cons dp ca frame _
        context.invocation hnotflash]
  rw [hstream]
  have hneApprove : depositToAndCallSelector ≠ approveSelector := by
    decide +kernel
  have hneApproveCall :
      depositToAndCallSelector ≠ approveAndCallSelector := by
    decide +kernel
  have hnePermit : depositToAndCallSelector ≠ permitSelector := by
    decide +kernel
  have hneTransferFrom :
      depositToAndCallSelector ≠ transferFromSelector := by
    decide +kernel
  have hneWithdrawFrom :
      depositToAndCallSelector ≠ withdrawFromSelector := by
    decide +kernel
  have hneAllowance : depositToAndCallSelector ≠ allowanceSelector := by
    decide +kernel
  have hown : (CountedFrame.ofFrame dp ca frame).allowance = none := by
    show frameAllowanceEvent frame.sevm frame.pre frame.post = none
    simp [frameAllowanceEvent, hnonempty, hsel, hneApprove, hneApproveCall,
      hnePermit, hneTransferFrom, hneWithdrawFrom, hneFlash, hneAllowance]
  have hvalid : ValidAdr (normalizedAddressArg frame.sevm 0) :=
    normalizedAddress_valid (Sevm.argWord frame.sevm 0)
  have hstorCa := hstor
  rw [htarget] at hstorCa
  have hprefixEffect : AllowanceRegionEffect ca frame.pre
      callbackCursor.pre [CountedFrame.ofFrame dp ca frame] := by
    refine ⟨fun key hkey => ?_, hcodeCallback⟩
    rw [applyAllowanceLedger_singleton, hown]
    show (Devm.getStor callbackCursor.pre ca).get key =
      (Devm.getStor frame.pre ca).get key
    rw [hstorCa,
      Stor.get_set_ne _ ((allowanceRegion_ne_validAdr hkey hvalid).symm) _,
      ← congrFun hstorEntry ca]
  exact hprefixEffect.append childEffect

/-! ## The `transferAndCall` arm -/

/-- The nonzero-recipient `transferAndCall` prefix writes exactly two
address-shaped balance keys — the caller's debit and the normalized
recipient's credit — so every tagged allowance key keeps its entry value,
and its `Transfer` emission leaves the callback's memory frame holding the
raw amount word. -/
private theorem transferAndCallPrefix_frame
    {e : Sevm} {s0 s1 s2 s3 s4 : Devm} {balance : B256}
    (hp : balance :: Sevm.argWord e 1 :: e.caller.toB256 :: [] <<+ s0.stack)
    (hwf : Mem.Wf s0.memory)
    (hreads : Mem.Reads s0.memory [])
    (hdebit : Line.Run e s0 debitLoadedBalance s1)
    (hcredit : Line.Run e s1 (addressArg 0 ++ [Ninst.dup 0, Ninst.sload] ++
      arg 1 ++ [Ninst.add, Ninst.swap 0, Ninst.sstore]) s2)
    (hevent : Line.Run e s2 ([Ninst.caller] ++ arg 1 ++ addressArg 0) s3)
    (hemit : Line.Run e s3 emitTransfer s4) :
    (∀ key, InRegion .allowance key →
      (Devm.getStor s4 e.currentTarget).get key =
        (Devm.getStor s0 e.currentTarget).get key) ∧
    Devm.getCode s4 = Devm.getCode s0 ∧
    Mem.Wf s4.memory ∧
    Mem.Reads s4.memory (Sevm.argWord e 1).toBytes := by
  unfold debitLoadedBalance at hdebit
  rcases Line.of_run_cons hdebit with ⟨d1, hsub, hdebit1⟩
  have hpD1 : (balance - Sevm.argWord e 1) :: e.caller.toB256 :: [] <<+
      d1.stack := prefix_of_sub hsub hp
  rcases Line.of_run_cons hdebit1 with ⟨d2, hswap, hdebit2⟩
  have hswapCoreD : Stack.Swap (0 : Fin 16).val
      [balance - Sevm.argWord e 1, e.caller.toB256]
      [e.caller.toB256, balance - Sevm.argWord e 1] :=
    Stack.swapCore_zero
  have hpD2 : e.caller.toB256 :: (balance - Sevm.argWord e 1) :: [] <<+
      d2.stack :=
    Stack.prefix_of_swap hswapCoreD (of_run_swap hswap) hpD1
  rcases Line.of_run_cons hdebit2 with ⟨d3, hstore, hnilD⟩
  cases hnilD
  have hsetDebit : Devm.getStor s1 e.currentTarget =
      (Devm.getStor d2 e.currentTarget).set e.caller.toB256
        (balance - Sevm.argWord e 1) :=
    sstore_getStor_set hstore hpD2
  rcases of_run_append (addressArg 0) hcredit with ⟨c1, haddr, hcredit1⟩
  have hpC1 : ((~~~ addressMask) &&& Sevm.argWord e 0) :: [] <<+ c1.stack :=
    prefix_of_addressArg nil_pref haddr
  rcases of_run_append [Ninst.dup 0] hcredit1 with ⟨c2, hdupLine, hcredit2⟩
  rcases Line.of_run_cons hdupLine with ⟨c2', hdup, hnil2⟩
  cases hnil2
  have hpC2 : ((~~~ addressMask) &&& Sevm.argWord e 0) ::
      ((~~~ addressMask) &&& Sevm.argWord e 0) :: [] <<+ c2.stack :=
    prefix_of_dup_val hdup (by show_nth) hpC1
  rcases of_run_append [Ninst.sload] hcredit2 with ⟨c3, hloadLine, hcredit3⟩
  rcases Line.of_run_cons hloadLine with ⟨c3', hloadN, hnil3⟩
  cases hnil3
  rcases prefix_of_sload hloadN hpC2 with ⟨toBal, hpC3, _⟩
  rcases of_run_append (arg 1) hcredit3 with ⟨c4, hamount, hcredit4⟩
  have hpC4 : Sevm.argWord e 1 :: toBal ::
      ((~~~ addressMask) &&& Sevm.argWord e 0) :: [] <<+ c4.stack :=
    prefix_of_arg hpC3 hamount
  rcases Line.of_run_cons hcredit4 with ⟨c5, haddN, hcredit5⟩
  have hpC5 : (Sevm.argWord e 1 + toBal) ::
      ((~~~ addressMask) &&& Sevm.argWord e 0) :: [] <<+ c5.stack :=
    prefix_of_add haddN hpC4
  rcases Line.of_run_cons hcredit5 with ⟨c6, hswapN, hcredit6⟩
  have hswapCoreC : Stack.Swap (0 : Fin 16).val
      [Sevm.argWord e 1 + toBal, (~~~ addressMask) &&& Sevm.argWord e 0]
      [(~~~ addressMask) &&& Sevm.argWord e 0, Sevm.argWord e 1 + toBal] :=
    Stack.swapCore_zero
  have hpC6 : ((~~~ addressMask) &&& Sevm.argWord e 0) ::
      (Sevm.argWord e 1 + toBal) :: [] <<+ c6.stack :=
    Stack.prefix_of_swap hswapCoreC (of_run_swap hswapN) hpC5
  rcases Line.of_run_cons hcredit6 with ⟨c7, hstoreN, hnil7⟩
  cases hnil7
  have hsetCredit : Devm.getStor s2 e.currentTarget =
      (Devm.getStor c6 e.currentTarget).set
        ((~~~ addressMask) &&& Sevm.argWord e 0)
        (Sevm.argWord e 1 + toBal) :=
    sstore_getStor_set hstoreN hpC6
  have heventRun := hevent
  rcases Line.of_run_cons hevent with ⟨afterCaller, hcaller, hevent1⟩
  have hpCaller : e.caller.toB256 :: [] <<+ afterCaller.stack :=
    prefix_of_push (of_run_caller hcaller) nil_pref
  rcases of_run_append (arg 1) hevent1 with ⟨afterAmount, hamountE, haddress⟩
  have hpAmount : Sevm.argWord e 1 :: e.caller.toB256 :: [] <<+
      afterAmount.stack := prefix_of_arg hpCaller hamountE
  have hpEvent : normalizedAddressArg e 0 :: Sevm.argWord e 1 ::
      e.caller.toB256 :: [] <<+ s3.stack := by
    simpa only [normalizedAddressArg] using
      prefix_of_addressArg hpAmount haddress
  have hmem03 : s0.memory = s3.memory := by
    calc
      s0.memory = d1.memory :=
        Line.of_inv Devm.memory (by line_inv)
          (Line.Run.cons hsub Line.Run.nil)
      _ = d2.memory :=
        Line.of_inv Devm.memory (by line_inv)
          (Line.Run.cons hswap Line.Run.nil)
      _ = s1.memory :=
        Line.of_inv Devm.memory (by line_inv)
          (Line.Run.cons hstore Line.Run.nil)
      _ = s2.memory := Line.of_inv Devm.memory (by line_inv) hcredit
      _ = s3.memory := Line.of_inv Devm.memory (by line_inv) heventRun
  have hwfEvent : Mem.Wf s3.memory := by
    rw [← hmem03]
    exact hwf
  have hreadsEvent : Mem.Reads s3.memory [] := by
    rw [← hmem03]
    exact hreads
  obtain ⟨_hpNext, _hemitLogs, hemitStor, _hemitBal, hemitCode,
      _hemitOutput, hwf4, hreads4⟩ :=
    emitTransfer_effect_frame hpEvent hwfEvent hreadsEvent hemit
  have hwrite : Bytes.writeAt [] 0 (Sevm.argWord e 1).toBytes =
      (Sevm.argWord e 1).toBytes :=
    Bytes.writeAt_zero_of_le (Nat.zero_le _)
  rw [hwrite] at hreads4
  have hsInv1 : Devm.getStor s0 = Devm.getStor d2 :=
    (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hsub Line.Run.nil)).trans
      (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hswap Line.Run.nil))
  have hsInv2 : Devm.getStor s1 = Devm.getStor c6 := by
    rw [Line.of_inv Devm.getStor (by line_inv) haddr,
      Line.of_inv Devm.getStor (by line_inv) hdupLine,
      Line.of_inv Devm.getStor (by line_inv) hloadLine,
      Line.of_inv Devm.getStor (by line_inv) hamount,
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons haddN Line.Run.nil),
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hswapN Line.Run.nil)]
  have hsInv3 : Devm.getStor s2 = Devm.getStor s3 :=
    Line.of_inv Devm.getStor (by line_inv) heventRun
  refine ⟨fun key hkey => ?_, ?_, hwf4, hreads4⟩
  · have hneCaller : e.caller.toB256 ≠ key :=
      (allowanceRegion_ne_validAdr hkey ⟨e.caller, rfl⟩).symm
    have hneNorm : ((~~~ addressMask) &&& Sevm.argWord e 0) ≠ key :=
      (allowanceRegion_ne_validAdr hkey
        (normalizedAddress_valid (Sevm.argWord e 0))).symm
    rw [congrFun hemitStor e.currentTarget,
      ← congrFun hsInv3 e.currentTarget, hsetCredit,
      Stor.get_set_ne _ hneNorm _, ← congrFun hsInv2 e.currentTarget,
      hsetDebit, Stor.get_set_ne _ hneCaller _,
      ← congrFun hsInv1 e.currentTarget]
  · calc
      Devm.getCode s4 = Devm.getCode s3 := hemitCode
      _ = Devm.getCode s2 :=
        (Line.of_inv Devm.getCode (by line_inv) heventRun).symm
      _ = Devm.getCode s1 :=
        (Line.of_inv Devm.getCode (by line_inv) hcredit).symm
      _ = Devm.getCode s0 :=
        (Line.of_inv Devm.getCode (by line_inv) hdebit).symm

/-- Nonzero-recipient `transferAndCall` transports the allowance region: the
frame's own record carries no allowance event and replays transparently,
and the retained callback child supplies the rest of the ledger. -/
theorem Exec.Frame.allowanceRegionEffect_of_transferAndCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = transferAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hto : Sevm.argWord frame.sevm 0 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmem : (Sevm.selector frame.sevm, nonpayable transferAndCall) ∈
      weth10Funcs dp := by
    rw [hselector]
    simp [transferAndCallSelector, weth10Funcs]
  rcases frame.compiledSelectorBodyCursorCountedSilent context hnonempty
      hmem with
    ⟨wrapperCursor, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨bodyCursor, hnonpayableSilent⟩
  have hbodySilent : Devm.DispatchSilent frame.pre bodyCursor.pre :=
    hentrySilent.trans hnonpayableSilent
  unfold transferAndCall transferThen at bodyCursor
  rcases bodyCursor.peelChildlessLine
      (line := arg 0 ++ [Ninst.iszero])
      (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨targetBranchCursor, htargetLine⟩
  have htargetPrefix :
      [Sevm.argWord frame.sevm 0 =? 0] <<+ targetBranchCursor.pre.stack := by
    rcases of_run_append (arg 0) htargetLine with
      ⟨afterArg, harg, hzeroLine⟩
    rcases Line.of_run_cons hzeroLine with ⟨afterZero, hzero, hnil⟩
    cases hnil
    exact prefix_of_iszero hzero (prefix_of_arg nil_pref harg)
  have htargetCheck : (Sevm.argWord frame.sevm 0 =? 0) = 0 := by
    simp [B256.eqCheck, hto]
  rw [htargetCheck] at htargetPrefix
  rcases targetBranchCursor.selectBranchZeroSilent htargetPrefix with
    ⟨nonzeroCursor, _hnonzeroStack, hselectSilent⟩
  rcases nonzeroCursor.peelChildlessLine
      (line := loadCallerBalanceAmount 1 ++ balanceTooSmall)
      (by simp [loadCallerBalanceAmount, balanceTooSmall, arg, cdl,
        NinstIsChildless, Ninst.pushB256]) with
    ⟨guardBranchCursor, hguardLine⟩
  rcases guardBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revWith (transferBalanceError_lookup dp)) with
    ⟨successCursor, hsuccessPop⟩
  rcases of_run_append (loadCallerBalanceAmount 1) hguardLine with
    ⟨afterLoad, hload, hsmall⟩
  rcases prefix_of_loadCallerBalanceAmount nil_pref hload with
    ⟨balance, _hbalance, hpLoad⟩
  have hpFlag := prefix_of_balanceTooSmall hpLoad hsmall
  have hsuccessStack := popBurn_pref
    (Devm.PopBurn.of_popBurnBy hsuccessPop) hpFlag
  rcases successCursor.peelChildlessLine
      (line := debitLoadedBalance)
      (by simp [debitLoadedBalance, NinstIsChildless]) with
    ⟨creditCursor, hdebit⟩
  rcases creditCursor.peelChildlessLine
      (line := addressArg 0 ++ [Ninst.dup 0, Ninst.sload] ++ arg 1 ++
        [Ninst.add, Ninst.swap 0, Ninst.sstore])
      (by simp [addressArg, normalizeAddress, pushAddressMask, arg, cdl,
        NinstIsChildless, Ninst.pushB256]) with
    ⟨eventCursor, hcredit⟩
  rcases eventCursor.peelChildlessLine
      (line := [Ninst.caller] ++ arg 1 ++ addressArg 0)
      (by simp [addressArg, normalizeAddress, pushAddressMask, arg, cdl,
        NinstIsChildless, Ninst.pushB256]) with
    ⟨emitCursor, hevent⟩
  rcases emitCursor.peelChildlessLine
      (line := emitTransfer)
      (by simp [emitTransfer, Blanc.transferFromLog, mstoreAt, logWith,
        NinstIsChildless, Ninst.pushB256]) with
    ⟨callbackCursor, hemit⟩
  have hmemSuccess : frame.pre.memory = successCursor.pre.memory := by
    calc
      frame.pre.memory = bodyCursor.pre.memory := hbodySilent.memory
      _ = targetBranchCursor.pre.memory :=
        Line.of_inv Devm.memory (by line_inv) htargetLine
      _ = nonzeroCursor.pre.memory := hselectSilent.memory
      _ = guardBranchCursor.pre.memory :=
        Line.of_inv Devm.memory (by line_inv) hguardLine
      _ = successCursor.pre.memory := hsuccessPop.memory
  have hwfSuccess : Mem.Wf successCursor.pre.memory := by
    rw [← hmemSuccess]
    exact context.memory_wf
  have hreadsSuccess : Mem.Reads successCursor.pre.memory [] := by
    rw [← hmemSuccess]
    exact context.memory_reads_empty
  obtain ⟨hprefixKey, hprefixCode, hwfCallback, hreadsCallback⟩ :=
    transferAndCallPrefix_frame hsuccessStack.2 hwfSuccess hreadsSuccess
      hdebit hcredit hevent hemit
  rcases callbackCursor.countedTokenCallbackChronology
      (sel := onTokenTransferSelector) (targetArg := 0) (dataArg := 2)
      (valueWord := Sevm.argWord frame.sevm 1) (value := arg 1)
      (img := (Sevm.argWord frame.sevm 1).toBytes)
      (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256])
      (by
        intro a b xs hp hline
        exact prefix_of_arg hp hline)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      hwfCallback hreadsCallback context.invocation.2.2.2 with
    ⟨_inputSize, _input, _callPre, _callPost, _parent, _child, _xl, _pc,
      retained, callback, hinner⟩
  have htarget : frame.sevm.currentTarget = ca := context.invocation.2.1
  have hstorSuccess : Devm.getStor frame.pre = Devm.getStor
      successCursor.pre := by
    calc
      Devm.getStor frame.pre = Devm.getStor bodyCursor.pre :=
        funext (getStor_eq_of_state_eq hbodySilent.state)
      _ = Devm.getStor targetBranchCursor.pre :=
        Line.of_inv Devm.getStor (by line_inv) htargetLine
      _ = Devm.getStor nonzeroCursor.pre :=
        funext (getStor_eq_of_state_eq hselectSilent.state)
      _ = Devm.getStor guardBranchCursor.pre :=
        Line.of_inv Devm.getStor (by line_inv) hguardLine
      _ = Devm.getStor successCursor.pre :=
        funext (getStor_eq_of_state_eq hsuccessPop.state)
  have hcodeSuccess : Devm.getCode frame.pre = Devm.getCode
      successCursor.pre := by
    calc
      Devm.getCode frame.pre = Devm.getCode bodyCursor.pre :=
        funext (getCode_eq_of_state_eq hbodySilent.state)
      _ = Devm.getCode targetBranchCursor.pre :=
        Line.of_inv Devm.getCode (by line_inv) htargetLine
      _ = Devm.getCode nonzeroCursor.pre :=
        funext (getCode_eq_of_state_eq hselectSilent.state)
      _ = Devm.getCode guardBranchCursor.pre :=
        Line.of_inv Devm.getCode (by line_inv) hguardLine
      _ = Devm.getCode successCursor.pre :=
        funext (getCode_eq_of_state_eq hsuccessPop.state)
  have hcodeCallback : Devm.getCode frame.pre ca =
      Devm.getCode callbackCursor.pre ca :=
    (congrFun hcodeSuccess ca).trans (congrFun hprefixCode ca).symm
  have installedCallback : some (callbackCursor.pre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← hcodeCallback]
    exact context.installed.1
  have childEffect := callback.allowanceRegionEffect retained htarget
    installedCallback hdeeper
  have hneFlash : transferAndCallSelector ≠ flashLoanSelector := by
    decide +kernel
  have hsel : Sevm.selector frame.sevm = transferAndCallSelector := hselector
  have hnotflash : isFlashInvocation frame.sevm = false := by
    simp [isFlashInvocation, hsel, hneFlash]
  have hframeEq : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      CountedFrame.ofFrame dp ca frame ::
        retained.attributionStream dp ca := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframeEq, hinner,
      Exec.frameContribution_eq_cons dp ca frame _
        context.invocation hnotflash]
  rw [hstream]
  have hneApprove : transferAndCallSelector ≠ approveSelector := by
    decide +kernel
  have hneApproveCall :
      transferAndCallSelector ≠ approveAndCallSelector := by
    decide +kernel
  have hnePermit : transferAndCallSelector ≠ permitSelector := by
    decide +kernel
  have hneTransferFrom :
      transferAndCallSelector ≠ transferFromSelector := by
    decide +kernel
  have hneWithdrawFrom :
      transferAndCallSelector ≠ withdrawFromSelector := by
    decide +kernel
  have hneAllowance : transferAndCallSelector ≠ allowanceSelector := by
    decide +kernel
  have hown : (CountedFrame.ofFrame dp ca frame).allowance = none := by
    show frameAllowanceEvent frame.sevm frame.pre frame.post = none
    simp [frameAllowanceEvent, hnonempty, hsel, hneApprove, hneApproveCall,
      hnePermit, hneTransferFrom, hneWithdrawFrom, hneFlash, hneAllowance]
  have hprefixKeyCa := hprefixKey
  rw [htarget] at hprefixKeyCa
  have hprefixEffect : AllowanceRegionEffect ca frame.pre
      callbackCursor.pre [CountedFrame.ofFrame dp ca frame] := by
    refine ⟨fun key hkey => ?_, hcodeCallback⟩
    rw [applyAllowanceLedger_singleton, hown]
    show (Devm.getStor callbackCursor.pre ca).get key =
      (Devm.getStor frame.pre ca).get key
    rw [hprefixKeyCa key hkey, ← congrFun hstorSuccess ca]
  exact hprefixEffect.append childEffect

/-! ## The `approveAndCall` arm -/

/-- `approveAndCall` transports the allowance region.  Unlike the other two
callback arms its own record does carry an allowance event — the same
`.approveStore` branch `approve` takes — and the committed prefix stores
exactly at that event's projected key before the callback child is
spawned, so the record replays ahead of the child's stream. -/
theorem Exec.Frame.allowanceRegionEffect_of_approveAndCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = approveAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmem : (Sevm.selector frame.sevm, nonpayable approveAndCall) ∈
      weth10Funcs dp := by
    rw [hselector]
    simp [approveAndCallSelector, weth10Funcs]
  rcases frame.compiledSelectorBodyCursorCountedSilent context hnonempty
      hmem with
    ⟨wrapperCursor, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨bodyCursor, hnonpayableSilent⟩
  have hbodySilent : Devm.DispatchSilent frame.pre bodyCursor.pre :=
    hentrySilent.trans hnonpayableSilent
  unfold approveAndCall at bodyCursor
  rcases bodyCursor.peelChildlessLine
      (line := approvePrefix)
      (by simp [approvePrefix, allowanceKeyFromMemory, Blanc.logApprove,
        argCopy, cdc, arg, cdl, mstoreAt, logWith, pushList,
        NinstIsChildless, Ninst.pushB256]) with
    ⟨callbackCursor, hprefix⟩
  have hwfBody : Mem.Wf bodyCursor.pre.memory := by
    rw [← hbodySilent.memory]
    exact context.memory_wf
  have hreadsBody : Mem.Reads bodyCursor.pre.memory [] := by
    rw [← hbodySilent.memory]
    exact context.memory_reads_empty
  rcases approvePrefix_callbackFrame nil_pref hwfBody hreadsBody
      hprefix with
    ⟨hstor, _hlogs, _hbal, hcodeApprove, _houtput, hwfCallback,
      callbackImg, hreadsCallback⟩
  rcases callbackCursor.countedTokenCallbackChronology
      (sel := onTokenApprovalSelector) (targetArg := 0) (dataArg := 2)
      (valueWord := Sevm.argWord frame.sevm 1) (value := arg 1)
      (img := callbackImg)
      (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256])
      (by
        intro a b xs hp hline
        exact prefix_of_arg hp hline)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      hwfCallback hreadsCallback context.invocation.2.2.2 with
    ⟨_inputSize, _input, _callPre, _callPost, _parent, _child, _xl, _pc,
      retained, callback, hinner⟩
  have htarget : frame.sevm.currentTarget = ca := context.invocation.2.1
  have hstorEntry : Devm.getStor frame.pre = Devm.getStor bodyCursor.pre :=
    funext (getStor_eq_of_state_eq hbodySilent.state)
  have hcodeEntry : Devm.getCode frame.pre = Devm.getCode bodyCursor.pre :=
    funext (getCode_eq_of_state_eq hbodySilent.state)
  have hcodeCallback : Devm.getCode frame.pre ca =
      Devm.getCode callbackCursor.pre ca :=
    (congrFun hcodeEntry ca).trans (congrFun hcodeApprove ca).symm
  have installedCallback : some (callbackCursor.pre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← hcodeCallback]
    exact context.installed.1
  have childEffect := callback.allowanceRegionEffect retained htarget
    installedCallback hdeeper
  have hneFlash : approveAndCallSelector ≠ flashLoanSelector := by
    decide +kernel
  have hsel : Sevm.selector frame.sevm = approveAndCallSelector := hselector
  have hnotflash : isFlashInvocation frame.sevm = false := by
    simp [isFlashInvocation, hsel, hneFlash]
  have hframeEq : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      CountedFrame.ofFrame dp ca frame ::
        retained.attributionStream dp ca := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframeEq, hinner,
      Exec.frameContribution_eq_cons dp ca frame _
        context.invocation hnotflash]
  rw [hstream]
  have hown : (CountedFrame.ofFrame dp ca frame).allowance =
      some { owner := frame.sevm.caller.toB256
             spender := Sevm.argWord frame.sevm 0
             caller := frame.sevm.caller
             depth := frame.sevm.depth
             visit := .approveStore (Sevm.argWord frame.sevm 1) } := by
    show frameAllowanceEvent frame.sevm frame.pre frame.post =
      some { owner := frame.sevm.caller.toB256
             spender := Sevm.argWord frame.sevm 0
             caller := frame.sevm.caller
             depth := frame.sevm.depth
             visit := .approveStore (Sevm.argWord frame.sevm 1) }
    simp [frameAllowanceEvent, hnonempty, hsel]
  have hstorCa := hstor
  rw [htarget] at hstorCa
  have hprefixEffect : AllowanceRegionEffect ca frame.pre
      callbackCursor.pre [CountedFrame.ofFrame dp ca frame] := by
    refine ⟨fun key hkey => ?_, hcodeCallback⟩
    rw [congrFun hstorEntry ca, applyAllowanceLedger_singleton, hown]
    simp only [AllowanceEvent.key, AllowanceVisit.written?]
    show (Devm.getStor callbackCursor.pre ca).get key = _
    rw [hstorCa]
    by_cases hkeyEq : projectedAllowanceKey frame.sevm.caller.toB256
        (Sevm.argWord frame.sevm 0) = key
    · rw [if_pos hkeyEq, ← hkeyEq, ← approveRuntimeKey_eq_projected]
      exact Stor.get_set_self _ _ _
    · rw [if_neg hkeyEq]
      apply Stor.get_set_ne
      rw [approveRuntimeKey_eq_projected]
      exact hkeyEq
  exact hprefixEffect.append childEffect

end Weth10

end Blanc
