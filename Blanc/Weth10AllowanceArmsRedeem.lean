import Blanc.Weth10AllowanceArmsSpend

/-!
The direct-redemption arms of the allowance-region transport.

`withdraw`, `withdrawTo`, and the zero-recipient `transfer` all debit the
caller's balance, emit, and then perform one external value `CALL` whose
recipient may reenter WETH10.  Unlike every earlier arm, the frame's
attribution stream is therefore *not* its own record alone: the committed
send child contributes its own counted stream between the frame's record
and the frame's end.  This module walks the original retained execution at
the counted-cursor altitude up to the `CALL`, crosses the spawn edge while
identifying its counted label with the retained child's attribution
stream, transports the allowance region across the child through the
`ForallDeeperAt` recursion hypothesis, and closes the trailing guard as a
childless suffix.  All three selectors miss every allowance branch of
`frameAllowanceEvent`, so the frame's own record replays transparently.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Weth10

/-! ## Key shape and ledger congruence -/

/-- A tagged allowance key is never an address-shaped balance key. -/
private theorem allowanceRegion_ne_validAdr {key k : B256}
    (hkey : InRegion .allowance key) (hvalid : ValidAdr k) : key ≠ k := by
  intro h
  rcases hvalid with ⟨a, ha⟩
  apply regions_disjoint (x := .allowance) (y := .balance) (by decide)
    key hkey
  rw [h, ← ha]
  simpa only [balanceKey] using balanceKey_region a

/-- The ledger replay reads its entry storage only at the replayed key. -/
private theorem applyAllowanceLedger_congr
    {pre pre' : Stor} {ledger : List CountedFrame} {key : B256}
    (h : pre.get key = pre'.get key) :
    applyAllowanceLedger pre ledger key =
      applyAllowanceLedger pre' ledger key := by
  unfold applyAllowanceLedger
  cases lastAllowanceWriteAt ledger.reverse key with
  | none => exact h
  | some value => rfl

/-- An uncommitted execution contributes no attribution stream. -/
private theorem Exec.attributionStream_eq_nil_of_not_commits
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hnot : Execution.commits out ≠ true) :
    Exec.attributionStream dp ca run = [] := by
  unfold Exec.attributionStream
  rw [dif_neg hnot]

/-! ## Local copies of private compiled-module helpers

`Weth10HolderFlowCompiled` and `Weth10AttributionChronology` keep several
step-level facts private, so this module re-declares the ones it needs. -/

/-- The first instruction of a compiled `.next` block is installed at the
block's starting program counter. -/
private theorem ninstAt_of_subcode_next_redeem
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

private theorem genericCall_step_spawn_exact_redeem
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
    | exact ⟨_, (genericCall_step_spawn_exact_redeem hspawn).1⟩

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
private theorem Devm.eq_of_burnBy_redeem
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
        Devm.eq_of_burnBy_redeem (Devm.BurnBy.of_burn hburn hgas)
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

/-! ## Allowance transport across one retained child message

The counted mirror of
`ProcessMessageTrace.storageSegmentDelta_of_forallDeeperAt`: a retained
call-message trace transports the allowance region by exactly its
retained child's attribution stream, consuming `lift_core`'s strong-depth
hypothesis at the `Exec.CoreAllowanceSound` instantiation. -/

theorem ProcessMessageTrace.allowanceRegionDelta_of_forallDeeperAt
    {dp : DeployParams} {ca : Adr} {depth : Nat}
    {msg : Msg} {post parent : Devm}
    (trace : ProcessMessageTrace msg (.ok post))
    (hparent : parent.state = msg.benv.state)
    (hdepth : msg.depth < depth)
    (hcode : some (parent.getCode ca).toList =
      Prog.compile (weth10 dp))
    (htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp))
    (htargetDirect : msg.currentTarget = ca →
      msg.codeAddress = some ca)
    (hdeeper : ForallDeeperAt depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    AllowanceRegionEffect ca parent post
      (trace.retained.attributionStream dp ca) := by
  rcases trace with ⟨slot, retained, hprocess⟩
  cases retained with
  | none =>
      have hstorage : Devm.getStor parent ca = Devm.getStor post ca := by
        rcases ProcessMessage.none_ok_state_cases hprocess with
          hrollback | ⟨benv, htransfer, hpost⟩
        · exact congrArg (fun state : State => state.getStor ca)
            (hparent.trans hrollback.symm)
        · change msg.benvAfterTransfer = .ok benv at htransfer
          exact (congrArg (fun state : State => state.getStor ca)
              hparent).trans <|
            (benvAfterTransfer_getStor_eq htransfer ca).symm.trans <|
              (congrArg (fun state : State => state.getStor ca) hpost).symm
      have hcodeEq : parent.getCode ca = post.getCode ca := by
        rcases ProcessMessage.none_ok_state_cases hprocess with
          hrollback | ⟨benv, htransfer, hpost⟩
        · exact congrArg (fun state : State => state.getCode ca)
            (hparent.trans hrollback.symm)
        · change msg.benvAfterTransfer = .ok benv at htransfer
          exact (congrArg (fun state : State => state.getCode ca)
              hparent).trans <|
            (benvAfterTransfer_ok_getCode htransfer ca).symm.trans <|
              (congrArg (fun state : State => state.getCode ca) hpost).symm
      exact AllowanceRegionEffect.of_getStorCode_eq hstorage hcodeEq
  | @some pc sevm pre out run =>
      have henter : (Frame.ofCall msg).enter =
          .run ⟨pc, sevm, pre⟩ :=
        (RunFrame.some_inv hprocess).1
      rcases Frame.enter_run_inv henter with ⟨benv, htransfer, hevm⟩
      simp only [Frame.ofCall] at htransfer hevm
      have hpreState : pre.state = benv.state := by
        have component := congrArg (fun evm : Evm => evm.dyna.state) hevm
        change pre.state = (initEvm (msg.withBenv benv)).dyna.state
        exact component
      have hsevm : sevm = initSevm (msg.withBenv benv) :=
        congrArg (fun evm : Evm => evm.sta) hevm
      have hpc : pc = 0 := by
        simpa [initEvm] using congrArg (fun evm : Evm => evm.pc) hevm
      have hmemory : pre.memory = Mem.empty := by
        have component := congrArg (fun evm : Evm => evm.dyna.memory) hevm
        change pre.memory = (initEvm (msg.withBenv benv)).dyna.memory
        simpa [initEvm, initDevm, Msg.withBenv] using component
      have hentryStorage : Devm.getStor parent ca =
          Devm.getStor pre ca := by
        exact (congrArg (fun state : State => state.getStor ca)
            hparent).trans <|
          (benvAfterTransfer_getStor_eq htransfer ca).symm.trans <|
            (congrArg (fun state : State => state.getStor ca)
              hpreState).symm
      have hentryCodeEq : parent.getCode ca = pre.getCode ca := by
        exact (congrArg (fun state : State => state.getCode ca)
            hparent).trans <|
          (benvAfterTransfer_ok_getCode htransfer ca).symm.trans <|
            (congrArg (fun state : State => state.getCode ca)
              hpreState).symm
      have hentryCode : some (pre.getCode ca).toList =
          Prog.compile (weth10 dp) := by
        calc
          some (pre.getCode ca).toList =
              some (benv.state.getCode ca).toList := by
            change some (pre.state.getCode ca).toList = _
            rw [hpreState]
          _ = some (msg.benv.state.getCode ca).toList := by
            rw [benvAfterTransfer_ok_getCode htransfer ca]
          _ = some (parent.getCode ca).toList := by
            change some (msg.benv.state.getCode ca).toList =
              some (parent.state.getCode ca).toList
            rw [hparent]
          _ = _ := hcode
      have hat : Prog.At (weth10 dp) ca pc sevm pre := by
        refine ⟨hentryCode, ?_⟩
        intro htarget
        have hmsgTarget : msg.currentTarget = ca := by
          rw [hsevm] at htarget
          simpa [initSevm, Msg.withBenv] using htarget
        refine ⟨?_, hpc⟩
        rw [hsevm]
        simpa [initSevm, Msg.withBenv] using htargetCode hmsgTarget
      have hdirect : sevm.currentTarget = ca →
          sevm.codeAddress = some ca := by
        intro htarget
        have hmsgTarget : msg.currentTarget = ca := by
          rw [hsevm] at htarget
          simpa [initSevm, Msg.withBenv] using htarget
        rw [hsevm]
        simpa [initSevm, Msg.withBenv] using htargetDirect hmsgTarget
      by_cases hcommit : Execution.commits out = true
      · cases out with
        | error error => simp [Execution.commits] at hcommit
        | ok raw =>
            have hchildDepth : sevm.depth < depth := by
              rw [hsevm]
              simpa [initSevm, Msg.withBenv] using hdepth
            have hcore := hdeeper pc sevm pre (.ok raw) run
              hchildDepth hat
            have childEffect := hcore run hcommit hat
              (fun htarget => ⟨⟨hpc, hmemory⟩, hdirect htarget⟩)
            have hpostState : post.state = raw.state :=
              ProcessMessage.ok_state_eq_committedPost hprocess hcommit
            have hpostStorage : Devm.getStor raw ca =
                Devm.getStor post ca :=
              congrArg (fun state : State => state.getStor ca)
                hpostState.symm
            have hpostCode : raw.getCode ca = post.getCode ca :=
              congrArg (fun state : State => state.getCode ca)
                hpostState.symm
            exact (by
              simpa only [List.nil_append, List.append_nil,
                RetainedXlot.attributionStream] using
                (AllowanceRegionEffect.of_getStorCode_eq
                    hentryStorage hentryCodeEq).append
                  (childEffect.append
                    (AllowanceRegionEffect.of_getStorCode_eq
                      hpostStorage hpostCode)))
      · have hactions : Exec.attributionStream dp ca run = [] :=
          Exec.attributionStream_eq_nil_of_not_commits run hcommit
        have hpostState : post.state = msg.benv.state :=
          ProcessMessage.ok_state_eq_of_not_commits hprocess hcommit
        have hstorage : Devm.getStor parent ca = Devm.getStor post ca :=
          congrArg (fun state : State => state.getStor ca)
            (hparent.trans hpostState.symm)
        have hcodeEq : parent.getCode ca = post.getCode ca :=
          congrArg (fun state : State => state.getCode ca)
            (hparent.trans hpostState.symm)
        have hstream : RetainedXlot.attributionStream dp ca
            (RetainedXlot.some run) = [] := by
          simpa only [RetainedXlot.attributionStream] using hactions
        rw [hstream]
        exact AllowanceRegionEffect.of_getStorCode_eq hstorage hcodeEq

/-! ## Closing the post-call guard suffix

After the external value `CALL` resumes with a success word, the
remaining body is the `ISZERO` test, the send-error reverter branch, and
a childless terminal continuation.  Packaged over the continuation
derivation as its own retained frame, the suffix contributes no counted
records and no storage writes. -/

private theorem Exec.tailGuard_attributionInner_storage
    {dp : DeployParams} {ca : Adr}
    {fsevm : Sevm} {pcT : Nat} {midD final : Devm}
    {table : List (Nat × Func)}
    {successLine : Line} {successLast : Linst}
    {errSlot : Nat} {_errReason : String} {rest : Stack}
    (next : Exec pcT fsevm midD (.ok final))
    (fcommitted : Execution.commits (.ok final) = true)
    (htail : Func.RunCompiled ((weth10 dp).main :: weth10Aux) fsevm midD
      (Ninst.iszero :::
        ((.call errSlot) <?> (successLine +++ Func.last successLast)))
      final)
    (hsub : subcode fsevm.code.toList pcT
      (Func.compile table pcT
        (Ninst.iszero :::
          ((.call errSlot) <?> (successLine +++ Func.last successLast)))))
    (hbound : noPushBefore fsevm.code pcT 32 = true)
    (hstackOne : midD.stack = (1 : B256) :: rest)
    (hsuccessChildless : ∀ n ∈ successLine, NinstIsChildless n)
    (hsuccessStor : Func.Inv Devm.getStor Devm.getStor
      (successLine +++ Func.last successLast)) :
    Exec.attributionInner dp ca next = [] ∧
    Devm.getStor midD = Devm.getStor final := by
  let tailCursor :
      Exec.Frame.CountedCursor dp ca
        (⟨pcT, fsevm, midD, .ok final, next, fcommitted⟩ : Exec.Frame)
        ((weth10 dp).main :: weth10Aux) table
        (Ninst.iszero :::
          ((.call errSlot) <?> (successLine +++ Func.last successLast)))
        final :=
    ⟨pcT, midD, next, ⟨[], Exec.Deriv.ParentPrefixActions.refl _⟩,
      Exec.Deriv.ParentPrefixCounted.refl _, htail, hsub, hbound⟩
  rcases tailCursor.selectNextChildless (by simp [NinstIsChildless]) with
    ⟨branchCursor, hiszeroRun⟩
  have hp0 : [(1 : B256)] <<+ midD.stack := by
    rw [hstackOne]
    exact pref_append [(1 : B256)] rest
  have hpIso : ((1 : B256) =? 0) :: [] <<+ branchCursor.pre.stack :=
    prefix_of_iszero hiszeroRun hp0
  have hne10 : (1 : B256) ≠ 0 := fun h => B256.zero_ne_one h.symm
  rw [show ((1 : B256) =? 0) = 0 from by simp [B256.eqCheck, hne10]]
    at hpIso
  rcases branchCursor.selectBranchZeroSilent hpIso with
    ⟨successCursor, _hsuccStack, hbranchSilent⟩
  rcases successCursor.peelChildlessLine hsuccessChildless with
    ⟨lastCursor, _hsuccessRun⟩
  have hinnerNil : Exec.attributionInner dp ca next = [] :=
    lastCursor.finishAttributionInner
  have hstorIso : midD.state = branchCursor.pre.state :=
    Ninst.Hinv.inv (f := Devm.state) hiszeroRun
  have hstorSuccess : Devm.getStor successCursor.pre =
      Devm.getStor final :=
    Func.of_inv Devm.getStor Devm.getStor hsuccessStor
      (Func.Run.of_runCompiled successCursor.run)
  refine ⟨hinnerNil, ?_⟩
  calc Devm.getStor midD
      = Devm.getStor branchCursor.pre :=
        funext (getStor_eq_of_state_eq hstorIso)
    _ = Devm.getStor successCursor.pre :=
        funext (getStor_eq_of_state_eq hbranchSilent.state)
    _ = Devm.getStor final := hstorSuccess

end Weth10

end Blanc
