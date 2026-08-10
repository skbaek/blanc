import Blanc.Weth10AllowanceArmsRedeem

/-!
The delegated redemption arms of the allowance-region transport.

`withdrawFrom` and the zero-recipient `transferFrom` are the two selectors
that compose both halves of the transport: the `spendCallerAllowanceThen`
wrapper, whose self/max/finite fork is the frame's own allowance record,
and a caller-owned redemption core, whose external value `CALL` may reenter
WETH10 and therefore contributes the committed child's counted stream.
The frame's ledger is `own :: inner`, and the storage side is the
chronological composition of the wrapper's singleton replay with the core's
child transport.
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

private def redeemSendToCallerPrefix : Line :=
  pushList [0, 0, 0, 0] ++ [swap 3, caller, gas]

private def redeemSendToArgPrefix (k : B256) : Line :=
  pushList [0, 0, 0, 0] ++ [swap 3] ++ arg k ++ [gas]

/-- Local copy of the compiled module's private caller-send operand walk. -/
private theorem redeemSendToCallerPrefix_effect
    {e : Sevm} {pre callPre : Devm} {value : B256} {tail : Stack}
    (hstack : value :: tail <<+ pre.stack)
    (run : Line.Run e pre redeemSendToCallerPrefix callPre) :
    ValueCallOperandPrefix e pre callPre value e.caller.toB256 tail := by
  unfold redeemSendToCallerPrefix pushList at run
  simp only [List.map] at run
  rcases Line.of_run_cons run with ⟨s₁, hpush₁, run₁⟩
  have hp₁ : (0 : B256) :: value :: tail <<+ s₁.stack :=
    prefix_of_push (of_run_pushB256 hpush₁) hstack
  rcases Line.of_run_cons run₁ with ⟨s₂, hpush₂, run₂⟩
  have hp₂ : (0 : B256) :: 0 :: value :: tail <<+ s₂.stack :=
    prefix_of_push (of_run_pushB256 hpush₂) hp₁
  rcases Line.of_run_cons run₂ with ⟨s₃, hpush₃, run₃⟩
  have hp₃ : (0 : B256) :: 0 :: 0 :: value :: tail <<+ s₃.stack :=
    prefix_of_push (of_run_pushB256 hpush₃) hp₂
  rcases Line.of_run_cons run₃ with ⟨s₄, hpush₄, run₄⟩
  have hp₄ : (0 : B256) :: 0 :: 0 :: 0 :: value :: tail <<+ s₄.stack :=
    prefix_of_push (of_run_pushB256 hpush₄) hp₃
  rcases Line.of_run_cons run₄ with ⟨s₅, hswap, run₅⟩
  have hswapCore : Stack.Swap (3 : Fin 16).val
      ((0 : B256) :: 0 :: 0 :: 0 :: value :: tail)
      (value :: 0 :: 0 :: 0 :: 0 :: tail) :=
    Stack.swapCore_succ (Stack.swapCore_succ
      (Stack.swapCore_succ Stack.swapCore_zero))
  have hp₅ : value :: 0 :: 0 :: 0 :: 0 :: tail <<+ s₅.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp₄
  rcases Line.of_run_cons run₅ with ⟨s₆, hcaller, run₆⟩
  have hp₆ : e.caller.toB256 :: value :: 0 :: 0 :: 0 :: 0 :: tail <<+
      s₆.stack := prefix_of_push (of_run_caller hcaller) hp₅
  rcases Line.of_run_cons run₆ with ⟨last, hgas, hnil⟩
  cases hnil
  rcases of_run_gas hgas with ⟨gasWord, hpushGas⟩
  exact ⟨⟨gasWord, prefix_of_push hpushGas hp₆⟩,
    Line.of_inv Devm.getStor (by line_inv) run,
    Line.of_inv Devm.getBal (by line_inv) run,
    Line.of_inv Devm.getCode (by line_inv) run,
    Line.of_inv Devm.memory (by line_inv) run,
    Line.of_inv Devm.logs (by line_inv) run,
    Line.of_inv Devm.output (by line_inv) run⟩

/-- Local copy of the compiled module's private argument-send operand walk. -/
private theorem redeemSendToArgPrefix_effect (k : B256)
    {e : Sevm} {pre callPre : Devm} {value : B256} {tail : Stack}
    (hstack : value :: tail <<+ pre.stack)
    (run : Line.Run e pre (redeemSendToArgPrefix k) callPre) :
    ValueCallOperandPrefix e pre callPre value (Sevm.argWord e k) tail := by
  unfold redeemSendToArgPrefix pushList at run
  simp only [List.map] at run
  rcases Line.of_run_cons run with ⟨s₁, hpush₁, run₁⟩
  have hp₁ : (0 : B256) :: value :: tail <<+ s₁.stack :=
    prefix_of_push (of_run_pushB256 hpush₁) hstack
  rcases Line.of_run_cons run₁ with ⟨s₂, hpush₂, run₂⟩
  have hp₂ : (0 : B256) :: 0 :: value :: tail <<+ s₂.stack :=
    prefix_of_push (of_run_pushB256 hpush₂) hp₁
  rcases Line.of_run_cons run₂ with ⟨s₃, hpush₃, run₃⟩
  have hp₃ : (0 : B256) :: 0 :: 0 :: value :: tail <<+ s₃.stack :=
    prefix_of_push (of_run_pushB256 hpush₃) hp₂
  rcases Line.of_run_cons run₃ with ⟨s₄, hpush₄, run₄⟩
  have hp₄ : (0 : B256) :: 0 :: 0 :: 0 :: value :: tail <<+ s₄.stack :=
    prefix_of_push (of_run_pushB256 hpush₄) hp₃
  rcases Line.of_run_cons run₄ with ⟨s₅, hswap, run₅⟩
  have hswapCore : Stack.Swap (3 : Fin 16).val
      ((0 : B256) :: 0 :: 0 :: 0 :: value :: tail)
      (value :: 0 :: 0 :: 0 :: 0 :: tail) :=
    Stack.swapCore_succ (Stack.swapCore_succ
      (Stack.swapCore_succ Stack.swapCore_zero))
  have hp₅ : value :: 0 :: 0 :: 0 :: 0 :: tail <<+ s₅.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp₄
  rcases of_run_append (arg k) run₅ with ⟨s₆, harg, run₆⟩
  have hp₆ : Sevm.argWord e k :: value :: 0 :: 0 :: 0 :: 0 :: tail <<+
      s₆.stack := prefix_of_arg hp₅ harg
  rcases Line.of_run_cons run₆ with ⟨last, hgas, hnil⟩
  cases hnil
  rcases of_run_gas hgas with ⟨gasWord, hpushGas⟩
  exact ⟨⟨gasWord, prefix_of_push hpushGas hp₆⟩,
    Line.of_inv Devm.getStor (by line_inv) run,
    Line.of_inv Devm.getBal (by line_inv) run,
    Line.of_inv Devm.getCode (by line_inv) run,
    Line.of_inv Devm.memory (by line_inv) run,
    Line.of_inv Devm.logs (by line_inv) run,
    Line.of_inv Devm.output (by line_inv) run⟩

/-! ## Identifying the counted label of a source `CALL` -/

/-- The counted label selected by an exact source `CALL` edge is precisely
the attribution stream of its retained raw child; the counted mirror of
`Exec.Deriv.ParentStepActions.selected_eq_retained_of_call`. -/
private theorem Exec.Deriv.ParentStepCounted.selected_eq_retained_of_call
    {dp : DeployParams} {ca : Adr}
    {pc nextPc : Nat} {sevm : Sevm} {pre post : Devm} {out : Execution}
    {current : Exec pc sevm pre out}
    {continuation : Exec nextPc sevm post out}
    {xl : Xlot} {selected : List CountedFrame}
    (hat : Ninst.At sevm.code pc Ninst.call)
    (filled : xl.Filled)
    (step : Ninst.StepRun pc sevm pre Ninst.call xl (.ok post))
    (retained : RetainedXlot xl)
    (commits : retained.RawCommits)
    (edge : Exec.Deriv.ParentStepCounted dp ca
      ⟨nextPc, sevm, post, out, continuation⟩
      ⟨pc, sevm, pre, out, current⟩ selected) :
    selected = retained.attributionStream dp ca := by
  cases edge with
  | cont hstep next =>
      have hs := (Evm.step_next hat).symm.trans hstep
      have actual :
          Ninst.StepRun pc sevm pre Ninst.call .none (.ok post) := by
        simp only [Ninst.StepRun, hs, Step.Run]
        exact ⟨trivial, trivial⟩
      have hslot := (Ninst.StepRun.unique_exec_of_filled
        filled (show Xlot.Filled .none from trivial) step actual).1
      subst xl
      cases retained
      rfl
  | doneOk hstep henter hresume next =>
      have hs := (Evm.step_next hat).symm.trans hstep
      have actual :
          Ninst.StepRun pc sevm pre Ninst.call .none (.ok post) := by
        simp only [Ninst.StepRun, hs, Step.Run]
        exact ⟨_, RunFrame.of_done henter, hresume.symm⟩
      have hslot := (Ninst.StepRun.unique_exec_of_filled
        filled (show Xlot.Filled .none from trivial) step actual).1
      subst xl
      cases retained
      rfl
  | runOk hstep henter child hresume next =>
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
          have hraw : Execution.commits raw = true := commits
          have hcommit : Blanc.Weth10.Frame.settlementCommits
              (Frame.ofCall msg) raw = true :=
            Frame.settlementCommits_ofCall_of_raw_commits hraw
          simp [hcommit, RetainedXlot.attributionStream,
            Exec.attributionStream, hraw]

/-- A leading eventless record is transparent to the ledger replay. -/
private theorem applyAllowanceLedger_cons_none
    {pre : Stor} {record : CountedFrame} {rest : List CountedFrame}
    {key : B256} (hnone : record.allowance = none) :
    applyAllowanceLedger pre (record :: rest) key =
      applyAllowanceLedger pre rest key := by
  have h := applyAllowanceLedger_append pre pre [record] rest key
    (by rw [applyAllowanceLedger_singleton, hnone])
  simpa using h

private def redeemReturnTrueLine : Line :=
  [pushB256 1] ++ mstoreAt 0 ++ pushList [32, 0]

private theorem returnTrue_eq_redeemReturnTrueLine :
    returnTrue = redeemReturnTrueLine +++ Func.last .ret := rfl

/-! ## Local copy of the exact caller-allowance key walk -/

private theorem of_callerAllowanceKeyPrefix
    {e : Sevm} {s r : Devm} {img : Bytes}
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Line.Run e s
      (arg 0 ++ mstoreAt 0 ++ [caller] ++ mstoreAt 1 ++
        allowanceKeyFromMemory) r) :
    callerAllowanceRuntimeKey e :: [] <<+ r.stack ∧
      Mem.Wf r.memory ∧ ∃ out, Mem.Reads r.memory out := by
  rcases of_run_append (arg 0) run with ⟨s1, howner, run1⟩
  have hp1 : Sevm.argWord e 0 :: [] <<+ s1.stack :=
    prefix_of_arg nil_pref howner
  rcases of_run_append (mstoreAt 0) run1 with
    ⟨s2, hstoreOwner, run2⟩
  rcases of_run_mstoreAt_val hstoreOwner hp1 with ⟨hp2, hm2⟩
  have hm2' : s2.memory =
      s1.memory.write 0 (Sevm.argWord e 0).toBytes := by
    simpa only [show (0 * 32 : B256).toNat = 0 by decide +kernel]
      using hm2
  have hmOwner : s.memory = s1.memory :=
    Line.of_inv Devm.memory (by unfold arg cdl; line_inv) howner
  rcases Line.of_run_cons run2 with ⟨s3, hcaller, run3⟩
  have hb3 := of_run_caller hcaller
  have hp3 : e.caller.toB256 :: [] <<+ s3.stack :=
    prefix_of_push hb3 hp2
  rcases of_run_append (mstoreAt 1) run3 with
    ⟨s4, hstoreCaller, hkey⟩
  rcases of_run_mstoreAt_val hstoreCaller hp3 with ⟨hp4, hm4⟩
  have hm4' : s4.memory =
      s3.memory.write 32 e.caller.toB256.toBytes := by
    simpa only [show (1 * 32 : B256).toNat = 32 by decide +kernel]
      using hm4
  let img1 := Bytes.writeAt img 0 (Sevm.argWord e 0).toBytes
  let img2 := Bytes.writeAt img1 32 e.caller.toB256.toBytes
  have hwf4 : Mem.Wf s4.memory := by
    rw [hm4', ← hb3.memory, hm2', ← hmOwner]
    exact (h_wf.write 0 (Sevm.argWord e 0).toBytes).write
      32 e.caller.toB256.toBytes
  have hr4 : Mem.Reads s4.memory img2 := by
    rw [hm4', ← hb3.memory, hm2', ← hmOwner]
    exact Mem.Reads.write
      (h_wf.write 0 (Sevm.argWord e 0).toBytes)
      (Mem.Reads.write h_wf h_reads 0 (Sevm.argWord e 0).toBytes)
      32 e.caller.toB256.toBytes
  rcases prefix_of_allowanceKeyFromMemory_image hp4 hwf4 hr4 hkey with
    ⟨hp5, hwf5, hr5⟩
  have himg : img2.sliceD 0 64 0 =
      (Sevm.argWord e 0).toBytes ++ e.caller.toB256.toBytes := by
    dsimp only [img2, img1]
    apply slice_two_words
    exact B256.length_toBytes _
  rw [himg] at hp5
  change callerAllowanceRuntimeKey e :: [] <<+ r.stack at hp5
  exact ⟨hp5, hwf5, ⟨img2, hr5⟩⟩

/-! ## Carried memory observations

The allowance wrapper writes the two key words and the approval payload, so
the redemption core it reaches is entered with a different memory image than
the frame.  Only well-formedness and readability survive, and only those are
needed. -/

/-- Memory well-formedness and readability carried across a segment. -/
private def MemCarried (pre post : Devm) : Prop :=
  ∀ {img : Bytes}, Mem.Wf pre.memory → Mem.Reads pre.memory img →
    Mem.Wf post.memory ∧ ∃ out, Mem.Reads post.memory out

private theorem MemCarried.of_eq {pre post : Devm}
    (h : pre.memory = post.memory) : MemCarried pre post := by
  intro img hwf hreads
  rw [← h]
  exact ⟨hwf, img, hreads⟩

private theorem MemCarried.trans {pre mid post : Devm}
    (h₁ : MemCarried pre mid) (h₂ : MemCarried mid post) :
    MemCarried pre post := by
  intro img hwf hreads
  rcases h₁ hwf hreads with ⟨hwfMid, out, hreadsMid⟩
  exact h₂ hwfMid hreadsMid

/-! ## Counted internal calls with observations

The counted mirror of `Exec.Frame.CompiledCursor.enterCallSilent`: a
generated internal source call is push/jump/jumpdest only, so reaching the
called body burns gas and changes nothing else. -/

private theorem Exec.Frame.CountedCursor.enterCallSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {k : Nat} {final : Devm}
    (cursor : frame.CountedCursor dp ca (f₀ :: aux)
      (table 0 (f₀ :: aux)) (.call k) final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩) :
    ∃ body,
      (f₀ :: aux)[k]? = some body ∧
      ∃ bodyCursor : frame.CountedCursor dp ca (f₀ :: aux)
          (table 0 (f₀ :: aux)) body final,
        Devm.DispatchSilent cursor.pre bodyCursor.pre := by
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
      exact ⟨_, hget, ⟨loc + 1, _, bodyExec, hpBody, hcBody, hbody,
        hsub, hjumpable.2⟩, Devm.DispatchSilent.of_burnBy hburn⟩

/-! ## The allowance wrapper's own lines -/

private def spendOwnerEqLine : Line := arg 0 ++ [Ninst.caller, Ninst.eq]

private def spendAllowanceLoadLine : Line :=
  arg 0 ++ mstoreAt 0 ++ [Ninst.caller] ++ mstoreAt 1 ++
    allowanceKeyFromMemory ++
    [Ninst.dup 0, Ninst.sload, Ninst.dup 0] ++ isMax

private def spendAllowanceCheckLine (amount : B256) : Line :=
  arg amount ++ [Ninst.swap 0] ++ balanceTooSmall

private def spendAllowanceStoreLine : Line :=
  [Ninst.sub, Ninst.dup 0, Ninst.swap 1, Ninst.sstore]

private def spendAllowanceAfterStoreLine : Line :=
  arg 0 ++ [Ninst.swap 0, Ninst.caller] ++ emitApproval ++
    [Ninst.pop, Ninst.pop]

/-- The allowance loader exposes the exact tagged runtime key, the loaded
allowance, and the max-allowance flag, and carries the memory image. -/
private theorem spendAllowanceLoadLine_effect
    {e : Sevm} {s r : Devm} {img : Bytes}
    (hwf : Mem.Wf s.memory)
    (hreads : Mem.Reads s.memory img)
    (run : Line.Run e s spendAllowanceLoadLine r) :
    ∃ allowance : B256,
      allowance = (Devm.getStor s e.currentTarget).get
        (callerAllowanceRuntimeKey e) ∧
      (((~~~ allowance) =? 0) :: allowance ::
        callerAllowanceRuntimeKey e :: []) <<+ r.stack ∧
      Mem.Wf r.memory ∧ ∃ out, Mem.Reads r.memory out := by
  let keyLine : Line :=
    arg 0 ++ mstoreAt 0 ++ [Ninst.caller] ++ mstoreAt 1 ++
      allowanceKeyFromMemory
  unfold spendAllowanceLoadLine at run
  rcases of_run_append keyLine run with ⟨sk, hkeyLine, runKey⟩
  have hmemTail : sk.memory = r.memory :=
    Line.of_inv Devm.memory (by line_inv) runKey
  have hkey : Line.Run e s
      (arg 0 ++ mstoreAt 0 ++ [Ninst.caller] ++ mstoreAt 1 ++
        allowanceKeyFromMemory) sk := by
    simpa only [keyLine] using hkeyLine
  obtain ⟨hpKey, hwfKey, out, hreadsKey⟩ :=
    of_callerAllowanceKeyPrefix hwf hreads hkey
  rcases Line.of_run_cons runKey with ⟨si1, hdupKey, runKey1⟩
  have hpI1 : callerAllowanceRuntimeKey e ::
      callerAllowanceRuntimeKey e :: [] <<+ si1.stack :=
    prefix_of_dup_val hdupKey (by show_nth) hpKey
  rcases Line.of_run_cons runKey1 with ⟨si2, hload, runKey2⟩
  rcases prefix_of_sload hload hpI1 with ⟨allowance, hpI2, hallowanceRead⟩
  rcases Line.of_run_cons runKey2 with ⟨si3, hdupAllowance, runKey3⟩
  have hpI3 : allowance :: allowance ::
      callerAllowanceRuntimeKey e :: [] <<+ si3.stack :=
    prefix_of_dup_val hdupAllowance (by show_nth) hpI2
  unfold isMax at runKey3
  rcases Line.of_run_cons runKey3 with ⟨si4, hnot, runKey4⟩
  have hpI4 : (~~~ allowance) :: allowance ::
      callerAllowanceRuntimeKey e :: [] <<+ si4.stack :=
    prefix_of_not hnot hpI3
  rcases Line.of_run_cons runKey4 with ⟨si5, hiszeroMax, hnilInspect⟩
  cases hnilInspect
  have hpLoad : ((~~~ allowance) =? 0) :: allowance ::
      callerAllowanceRuntimeKey e :: [] <<+ r.stack :=
    prefix_of_iszero hiszeroMax hpI4
  have hstorKey : Devm.getStor s = Devm.getStor si1 :=
    (Line.of_inv Devm.getStor (by line_inv) hkey).trans
      (Ninst.Hinv.inv (f := Devm.getStor) hdupKey)
  refine ⟨allowance, ?_, hpLoad, ?_, out, ?_⟩
  · rw [hallowanceRead]
    change (Devm.getStor si1 e.currentTarget).get
      (callerAllowanceRuntimeKey e) = _
    rw [← congrFun hstorKey e.currentTarget]
  · rw [← hmemTail]
    exact hwfKey
  · rw [← hmemTail]
    exact hreadsKey

/-- Local copy of the compiled module's private approval-tail memory walk. -/
private theorem spendAllowanceAfterStoreLine_memory
    {e : Sevm} {pre post : Devm} {reduced : B256} {img : Bytes}
    (hp : reduced :: [] <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory img)
    (run : Line.Run e pre spendAllowanceAfterStoreLine post) :
    Mem.Wf post.memory ∧ ∃ out, Mem.Reads post.memory out := by
  unfold spendAllowanceAfterStoreLine at run
  rcases of_run_append (arg 0) run with ⟨s₁, howner, run⟩
  have hp₁ : Sevm.argWord e 0 :: reduced :: [] <<+ s₁.stack :=
    prefix_of_arg hp howner
  rcases Line.of_run_cons run with ⟨s₂, hswap, run⟩
  have hswapCore : Stack.Swap (0 : Fin 16).val
      [Sevm.argWord e 0, reduced] [reduced, Sevm.argWord e 0] :=
    Stack.swapCore_zero
  have hp₂ : reduced :: Sevm.argWord e 0 :: [] <<+ s₂.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp₁
  rcases Line.of_run_cons run with ⟨s₃, hcaller, run⟩
  have hp₃ : e.caller.toB256 :: reduced :: Sevm.argWord e 0 :: [] <<+
      s₃.stack := prefix_of_push (of_run_caller hcaller) hp₂
  rcases of_run_append emitApproval run with ⟨s₄, hemit, run⟩
  have hmemory : pre.memory = s₃.memory :=
    (Line.of_inv Devm.memory (by line_inv) howner).trans
      ((Ninst.Hinv.inv (f := Devm.memory) hswap).trans
        (of_run_caller hcaller).memory)
  have hwf₃ : Mem.Wf s₃.memory := by
    rw [← hmemory]
    exact hwf
  have hreads₃ : Mem.Reads s₃.memory img := by
    rw [← hmemory]
    exact hreads
  obtain ⟨_hp, _hlogs, _hstor, _hbal, _hcode, _houtput,
      hwf₄, out, hreads₄⟩ :=
    emitApproval_effect hp₃ hwf₃ hreads₃ hemit
  rcases Line.of_run_cons run with ⟨s₅, hpop₁, run⟩
  rcases Line.of_run_cons run with ⟨s₆, hpop₂, hnil⟩
  cases hnil
  have hmemoryPost : s₄.memory = post.memory :=
    (Ninst.Hinv.inv (f := Devm.memory) hpop₁).trans
      (Ninst.Hinv.inv (f := Devm.memory) hpop₂)
  rw [← hmemoryPost]
  exact ⟨hwf₄, out, hreads₄⟩

/-! ## The wrapper's storage fork at the counted altitude

`CallerAllowanceOutcome` states the same fork at the `Func.Run` altitude,
but its witness state is not the counted cursor's, so the walk is redone
here.  Only the executing contract's storage is tracked: the logs and the
finite path's coverage bound play no part in allowance transport. -/

/-- The exact self/max/finite storage fork of the allowance wrapper. -/
private def SpendStorageFork (e : Sevm) (pre corePre : Devm)
    (amountArg : B256) : Prop :=
  (Sevm.argWord e 0 = e.caller.toB256 ∧
      Devm.getStor corePre e.currentTarget =
        Devm.getStor pre e.currentTarget) ∨
    (Sevm.argWord e 0 ≠ e.caller.toB256 ∧
      (((Devm.getStor pre e.currentTarget).get
            (callerAllowanceRuntimeKey e) = B256.max ∧
          Devm.getStor corePre e.currentTarget =
            Devm.getStor pre e.currentTarget) ∨
        (∃ allowance : B256,
          allowance ≠ B256.max ∧
          (Devm.getStor pre e.currentTarget).get
              (callerAllowanceRuntimeKey e) = allowance ∧
          Devm.getStor corePre e.currentTarget =
            (Devm.getStor pre e.currentTarget).set
              (callerAllowanceRuntimeKey e)
              (allowance - Sevm.argWord e amountArg))))

/-- Follow the actual successful allowance wrapper to its internal core
while retaining the storage fork, the installed code, and the memory
observations the core needs; the counted, allowance-tracking mirror of
`Exec.Frame.CompiledCursor.enterSpendCallerAllowanceThenWithObservations`. -/
private theorem Exec.Frame.CountedCursor.enterSpendCallerAllowanceThenFork
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {amount : B256} {nextSlot : Nat}
    {final : Devm} {img : Bytes}
    (cursor : frame.CountedCursor dp ca (f₀ :: aux)
      (table 0 (f₀ :: aux))
      (spendCallerAllowanceThen amount nextSlot) final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩)
    (hallowanceError :
      (f₀ :: aux)[allowanceErrorSlot]? =
        some (Func.revWith "WETH: request exceeds allowance"))
    (hwf : Mem.Wf cursor.pre.memory)
    (hreads : Mem.Reads cursor.pre.memory img) :
    ∃ body,
      (f₀ :: aux)[nextSlot]? = some body ∧
      ∃ bodyCursor : frame.CountedCursor dp ca (f₀ :: aux)
          (table 0 (f₀ :: aux)) body final,
        Mem.Wf bodyCursor.pre.memory ∧
        (∃ out, Mem.Reads bodyCursor.pre.memory out) ∧
        Devm.getCode cursor.pre = Devm.getCode bodyCursor.pre ∧
        SpendStorageFork frame.sevm cursor.pre bodyCursor.pre amount := by
  unfold spendCallerAllowanceThen at cursor
  rcases cursor.peelChildlessLine (line := spendOwnerEqLine)
      (by simp [spendOwnerEqLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨callerBranchCursor, hcallerLine⟩
  have hcallerPrefix :
      [frame.sevm.caller.toB256 =? Sevm.argWord frame.sevm 0] <<+
        callerBranchCursor.pre.stack := by
    unfold spendOwnerEqLine at hcallerLine
    rcases of_run_append (arg 0) hcallerLine with ⟨afterArg, harg, hrest⟩
    rcases Line.of_run_cons hrest with ⟨afterCaller, hcaller, heqLine⟩
    rcases Line.of_run_cons heqLine with ⟨afterEq, heq, hnil⟩
    cases hnil
    exact prefix_of_eq heq
      (prefix_of_push (of_run_caller hcaller) (prefix_of_arg nil_pref harg))
  have hcallerStor : Devm.getStor cursor.pre =
      Devm.getStor callerBranchCursor.pre :=
    Line.of_inv Devm.getStor (by unfold spendOwnerEqLine; line_inv)
      hcallerLine
  have hcallerCode : Devm.getCode cursor.pre =
      Devm.getCode callerBranchCursor.pre :=
    Line.of_inv Devm.getCode (by unfold spendOwnerEqLine; line_inv)
      hcallerLine
  have hcallerMem : MemCarried cursor.pre callerBranchCursor.pre :=
    MemCarried.of_eq
      (Line.of_inv Devm.memory (by unfold spendOwnerEqLine; line_inv)
        hcallerLine)
  by_cases hself : Sevm.argWord frame.sevm 0 = frame.sevm.caller.toB256
  · -- the self-owner path bypasses the allowance read entirely
    have hflag : (frame.sevm.caller.toB256 =? Sevm.argWord frame.sevm 0) = 1 := by
      simp [B256.eqCheck, hself]
    rw [hflag] at hcallerPrefix
    rcases callerBranchCursor.selectBranchSuccSilent (flag := (1 : B256))
        (by decide) hcallerPrefix with
      ⟨directCursor, _hdirectStack, hdirectSilent⟩
    rcases directCursor.enterCallSilent hcode with
      ⟨body, hget, bodyCursor, hbodySilent⟩
    obtain ⟨hwfBody, out, hreadsBody⟩ :=
      MemCarried.trans hcallerMem
        (MemCarried.trans (MemCarried.of_eq hdirectSilent.memory)
          (MemCarried.of_eq hbodySilent.memory)) hwf hreads
    refine ⟨body, hget, bodyCursor, hwfBody, ⟨out, hreadsBody⟩, ?_, ?_⟩
    · rw [hcallerCode, funext (getCode_eq_of_state_eq hdirectSilent.state),
        funext (getCode_eq_of_state_eq hbodySilent.state)]
    · refine Or.inl ⟨hself, ?_⟩
      rw [hcallerStor, funext (getStor_eq_of_state_eq hdirectSilent.state),
        funext (getStor_eq_of_state_eq hbodySilent.state)]
  · have hne : frame.sevm.caller.toB256 ≠ Sevm.argWord frame.sevm 0 :=
      fun h => hself h.symm
    have hflag : (frame.sevm.caller.toB256 =? Sevm.argWord frame.sevm 0) = 0 := by
      simp [B256.eqCheck, hne]
    rw [hflag] at hcallerPrefix
    rcases callerBranchCursor.selectBranchZeroSilent hcallerPrefix with
      ⟨allowanceCursor, _hallowanceStack, hallowanceSilent⟩
    have hentryStor : Devm.getStor cursor.pre =
        Devm.getStor allowanceCursor.pre := by
      rw [hcallerStor, funext (getStor_eq_of_state_eq hallowanceSilent.state)]
    have hentryCode : Devm.getCode cursor.pre =
        Devm.getCode allowanceCursor.pre := by
      rw [hcallerCode, funext (getCode_eq_of_state_eq hallowanceSilent.state)]
    obtain ⟨hwfLoad, imgLoad, hreadsLoad⟩ :=
      MemCarried.trans hcallerMem
        (MemCarried.of_eq hallowanceSilent.memory) hwf hreads
    rcases allowanceCursor.peelChildlessLine (line := spendAllowanceLoadLine)
        (by simp [spendAllowanceLoadLine, arg, cdl, mstoreAt,
          allowanceKeyFromMemory, pushList, isMax, NinstIsChildless,
          Ninst.pushB256]) with
      ⟨maxBranchCursor, hloadLine⟩
    obtain ⟨allowance, hallowanceVal, hloadPrefix, hwfMax, outMax, hreadsMax⟩ :=
      spendAllowanceLoadLine_effect hwfLoad hreadsLoad hloadLine
    have hloadStor : Devm.getStor allowanceCursor.pre =
        Devm.getStor maxBranchCursor.pre :=
      Line.of_inv Devm.getStor (by unfold spendAllowanceLoadLine; line_inv)
        hloadLine
    have hloadCode : Devm.getCode allowanceCursor.pre =
        Devm.getCode maxBranchCursor.pre :=
      Line.of_inv Devm.getCode (by unfold spendAllowanceLoadLine; line_inv)
        hloadLine
    by_cases hmax : allowance = B256.max
    · -- an infinite allowance is preserved
      have hmaxFlag : ((~~~ allowance) =? 0) = 1 := by
        rw [hmax, B256.not_max]
        simp [B256.eqCheck]
      rw [hmaxFlag] at hloadPrefix
      rcases maxBranchCursor.selectBranchSuccSilent (flag := (1 : B256))
          (by decide) hloadPrefix with
        ⟨maxCursor, _hmaxStack, hmaxSilent⟩
      rcases maxCursor.peelChildlessLine (line := [Ninst.pop, Ninst.pop])
          (by simp [NinstIsChildless]) with
        ⟨coreCallCursor, hpopLine⟩
      rcases coreCallCursor.enterCallSilent hcode with
        ⟨body, hget, bodyCursor, hbodySilent⟩
      obtain ⟨hwfBody, out, hreadsBody⟩ :=
        MemCarried.trans (MemCarried.of_eq hmaxSilent.memory)
          (MemCarried.trans
            (MemCarried.of_eq
              (Line.of_inv Devm.memory (by line_inv) hpopLine))
            (MemCarried.of_eq hbodySilent.memory)) hwfMax hreadsMax
      have hstor : Devm.getStor cursor.pre = Devm.getStor bodyCursor.pre := by
        rw [hentryStor, hloadStor,
          funext (getStor_eq_of_state_eq hmaxSilent.state),
          Line.of_inv Devm.getStor (by line_inv) hpopLine,
          funext (getStor_eq_of_state_eq hbodySilent.state)]
      refine ⟨body, hget, bodyCursor, hwfBody, ⟨out, hreadsBody⟩, ?_, ?_⟩
      · rw [hentryCode, hloadCode,
          funext (getCode_eq_of_state_eq hmaxSilent.state),
          Line.of_inv Devm.getCode (by line_inv) hpopLine,
          funext (getCode_eq_of_state_eq hbodySilent.state)]
      · refine Or.inr ⟨fun h => hne h.symm, Or.inl ⟨?_, ?_⟩⟩
        · rw [congrFun hentryStor frame.sevm.currentTarget, ← hallowanceVal]
          exact hmax
        · rw [hstor]
    · -- a finite allowance is decremented at the tagged runtime key
      have hmaxFlag : ((~~~ allowance) =? 0) = 0 := by
        rw [B256.eqCheck, if_neg]
        intro hzero
        exact hmax (B256.eq_max_of_not_eq_zero hzero)
      rw [hmaxFlag] at hloadPrefix
      rcases maxBranchCursor.selectBranchZeroSilent hloadPrefix with
        ⟨finiteCursor, hfiniteStack, hfiniteSilent⟩
      rcases finiteCursor.peelChildlessLine
          (line := spendAllowanceCheckLine amount)
          (by simp [spendAllowanceCheckLine, arg, cdl, balanceTooSmall,
            NinstIsChildless, Ninst.pushB256]) with
        ⟨spendBranchCursor, hcheckLine⟩
      have hcheckStack :
          (allowance <? Sevm.argWord frame.sevm amount) :: allowance ::
            Sevm.argWord frame.sevm amount ::
            callerAllowanceRuntimeKey frame.sevm :: [] <<+
              spendBranchCursor.pre.stack := by
        unfold spendAllowanceCheckLine at hcheckLine
        rcases of_run_append (arg amount) hcheckLine with
          ⟨afterArg, hargRun, hrest⟩
        have hpArg : Sevm.argWord frame.sevm amount :: allowance ::
            callerAllowanceRuntimeKey frame.sevm :: [] <<+ afterArg.stack :=
          prefix_of_arg hfiniteStack hargRun
        rcases of_run_append [Ninst.swap 0] hrest with
          ⟨afterSwap, hswapLine, hguard⟩
        rcases Line.of_run_cons hswapLine with ⟨afterSwap', hswap, hnil⟩
        cases hnil
        have hswapCore : Stack.Swap (0 : Fin 16).val
            [Sevm.argWord frame.sevm amount, allowance,
              callerAllowanceRuntimeKey frame.sevm]
            [allowance, Sevm.argWord frame.sevm amount,
              callerAllowanceRuntimeKey frame.sevm] :=
          Stack.swapCore_zero
        have hpSwap : allowance :: Sevm.argWord frame.sevm amount ::
            callerAllowanceRuntimeKey frame.sevm :: [] <<+ afterSwap.stack :=
          Stack.prefix_of_swap hswapCore (of_run_swap hswap) hpArg
        exact prefix_of_balanceTooSmall hpSwap hguard
      rcases spendBranchCursor.selectBranchLeftWithBurn
          (not_run_call_revWith hallowanceError) with
        ⟨successCursor, hcheckPopBy⟩
      have hcheckPop := Devm.PopBurn.of_popBurnBy hcheckPopBy
      have hpopStack := hcheckPop.stack
      simp only [Stack.Pop, Split, List.nil_append,
        List.cons_append] at hpopStack
      rw [hpopStack] at hcheckStack
      have hguardFlag : (allowance <? Sevm.argWord frame.sevm amount) = 0 :=
        pref_head_unique hcheckStack
          (pref_append [0] successCursor.pre.stack)
      rw [hguardFlag] at hcheckStack
      have hsuccessStack : allowance :: Sevm.argWord frame.sevm amount ::
          callerAllowanceRuntimeKey frame.sevm :: [] <<+
            successCursor.pre.stack := cons_pref_cons_inv hcheckStack
      rcases successCursor.peelChildlessLine
          (line := spendAllowanceStoreLine ++ spendAllowanceAfterStoreLine)
          (by simp [spendAllowanceStoreLine, spendAllowanceAfterStoreLine,
            arg, cdl, emitApproval, mstoreAt, logWith, NinstIsChildless,
            Ninst.pushB256]) with
        ⟨coreCallCursor, hspendLine⟩
      rcases of_run_append spendAllowanceStoreLine hspendLine with
        ⟨afterStore, hstoreLine, hafterLine⟩
      unfold spendAllowanceStoreLine at hstoreLine
      rcases Line.of_run_cons hstoreLine with ⟨d1, hsub, hstore1⟩
      have hpD1 : (allowance - Sevm.argWord frame.sevm amount) ::
          callerAllowanceRuntimeKey frame.sevm :: [] <<+ d1.stack :=
        prefix_of_sub hsub hsuccessStack
      rcases Line.of_run_cons hstore1 with ⟨d2, hdup, hstore2⟩
      have hpD2 : (allowance - Sevm.argWord frame.sevm amount) ::
          (allowance - Sevm.argWord frame.sevm amount) ::
          callerAllowanceRuntimeKey frame.sevm :: [] <<+ d2.stack :=
        prefix_of_dup_val hdup (by show_nth) hpD1
      rcases Line.of_run_cons hstore2 with ⟨d3, hswap1, hstore3⟩
      have hswapCore1 : Stack.Swap (1 : Fin 16).val
          [allowance - Sevm.argWord frame.sevm amount,
            allowance - Sevm.argWord frame.sevm amount,
            callerAllowanceRuntimeKey frame.sevm]
          [callerAllowanceRuntimeKey frame.sevm,
            allowance - Sevm.argWord frame.sevm amount,
            allowance - Sevm.argWord frame.sevm amount] :=
        Stack.swapCore_succ Stack.swapCore_zero
      have hpD3 : callerAllowanceRuntimeKey frame.sevm ::
          (allowance - Sevm.argWord frame.sevm amount) ::
          (allowance - Sevm.argWord frame.sevm amount) :: [] <<+ d3.stack :=
        Stack.prefix_of_swap hswapCore1 (of_run_swap hswap1) hpD2
      rcases Line.of_run_cons hstore3 with ⟨d4, hsstore, hnilStore⟩
      cases hnilStore
      have hsetStore : Devm.getStor afterStore frame.sevm.currentTarget =
          (Devm.getStor d3 frame.sevm.currentTarget).set
            (callerAllowanceRuntimeKey frame.sevm)
            (allowance - Sevm.argWord frame.sevm amount) :=
        sstore_getStor_set hsstore hpD3
      have hpAfter : (allowance - Sevm.argWord frame.sevm amount) :: [] <<+
          afterStore.stack := prefix_of_sstore hsstore hpD3
      have hstorePre : Devm.getStor successCursor.pre = Devm.getStor d3 :=
        (Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hsub Line.Run.nil)).trans
          ((Line.of_inv Devm.getStor (by line_inv)
            (Line.Run.cons hdup Line.Run.nil)).trans
            (Line.of_inv Devm.getStor (by line_inv)
              (Line.Run.cons hswap1 Line.Run.nil)))
      have hstoreMem : successCursor.pre.memory = afterStore.memory :=
        (Ninst.Hinv.inv (f := Devm.memory) hsub).trans
          ((Ninst.Hinv.inv (f := Devm.memory) hdup).trans
            ((Ninst.Hinv.inv (f := Devm.memory) hswap1).trans
              (Ninst.Hinv.inv (f := Devm.memory) hsstore)))
      have hstoreCode : Devm.getCode successCursor.pre =
          Devm.getCode afterStore :=
        Line.of_inv Devm.getCode (by line_inv)
          (show Line.Run frame.sevm successCursor.pre
            [Ninst.sub, Ninst.dup 0, Ninst.swap 1, Ninst.sstore] afterStore
            from hstoreLine)
      obtain ⟨hwfSuccess, imgSuccess, hreadsSuccess⟩ :=
        MemCarried.trans (MemCarried.of_eq hfiniteSilent.memory)
          (MemCarried.trans
            (MemCarried.of_eq
              (Line.of_inv Devm.memory (by line_inv) hcheckLine))
            (MemCarried.of_eq hcheckPop.memory)) hwfMax hreadsMax
      obtain ⟨hwfCall, outCall, hreadsCall⟩ :=
        spendAllowanceAfterStoreLine_memory hpAfter
          (by rw [← hstoreMem]; exact hwfSuccess)
          (show Mem.Reads afterStore.memory imgSuccess by
            rw [← hstoreMem]; exact hreadsSuccess)
          hafterLine
      rcases coreCallCursor.enterCallSilent hcode with
        ⟨body, hget, bodyCursor, hbodySilent⟩
      have hwfBody : Mem.Wf bodyCursor.pre.memory := by
        rw [← hbodySilent.memory]
        exact hwfCall
      have hreadsBody : Mem.Reads bodyCursor.pre.memory outCall := by
        rw [← hbodySilent.memory]
        exact hreadsCall
      have hpreStor : Devm.getStor cursor.pre = Devm.getStor d3 := by
        rw [hentryStor, hloadStor,
          funext (getStor_eq_of_state_eq hfiniteSilent.state),
          Line.of_inv Devm.getStor (by line_inv) hcheckLine,
          PopBurn.Inv.inv (f := Devm.getStor) hcheckPop, hstorePre]
      have hpostStor : Devm.getStor afterStore =
          Devm.getStor bodyCursor.pre := by
        rw [Line.of_inv Devm.getStor (by line_inv) hafterLine,
          funext (getStor_eq_of_state_eq hbodySilent.state)]
      refine ⟨body, hget, bodyCursor, hwfBody, ⟨outCall, hreadsBody⟩, ?_, ?_⟩
      · rw [hentryCode, hloadCode,
          funext (getCode_eq_of_state_eq hfiniteSilent.state),
          Line.of_inv Devm.getCode (by line_inv) hcheckLine,
          funext (fun a => getCode_eq_of_state_eq hcheckPop.state a),
          hstoreCode, Line.of_inv Devm.getCode (by line_inv) hafterLine,
          funext (getCode_eq_of_state_eq hbodySilent.state)]
      · refine Or.inr ⟨fun h => hne h.symm, Or.inr
          ⟨allowance, hmax, ?_, ?_⟩⟩
        · rw [congrFun hentryStor frame.sevm.currentTarget, ← hallowanceVal]
        · rw [← congrFun hpostStor frame.sevm.currentTarget, hsetStore,
            congrFun hpreStor frame.sevm.currentTarget]

/-! ## The delegated redemption core

The two delegated cores debit the *normalized owner argument* rather than
the caller, and burn-emit from that same word, so the shared caller-owned
walk of `Weth10AllowanceArmsRedeem` does not apply to them.  This is its
delegated counterpart, additionally parameterized over the send-failure
reverter slot, which the two cores do not share. -/

private def redeemFromCheckLine (ownerArg amountArg : B256) : Line :=
  loadArgBalanceAmount ownerArg amountArg ++ balanceTooSmall

private def redeemFromEventLine (ownerArg amountArg : B256) : Line :=
  addressArg ownerArg ++ arg amountArg ++ [Ninst.pushB256 0] ++
    emitTransfer ++ [Ninst.swap 0, Ninst.pop]

/-- The shared delegated redemption body: balance guard at the normalized
owner argument, debit, burn event, send-operand prefix, external value
`CALL`, success guard. -/
private def redeemFromBody (ownerArg amountArg : B256) (sendPrefix : Line)
    (errSlot : Nat) (success : Func) : Func :=
  redeemFromCheckLine ownerArg amountArg +++
  ((.call burnBalanceErrorSlot) <?>
    (debitLoadedBalance +++
      redeemFromEventLine ownerArg amountArg +++
      sendPrefix +++
      Ninst.call ::: Ninst.iszero :::
      ((.call errSlot) <?> success)))

private theorem withdrawFromCore_eq_redeemFromBody :
    withdrawFromCore =
      redeemFromBody 0 2 (redeemSendToArgPrefix 1) etherTransferErrorSlot
        (Func.last .stop) := rfl

private theorem transferFromZero_eq_redeemFromBody :
    transferFromZero =
      redeemFromBody 0 2 redeemSendToCallerPrefix ethTransferErrorSlot
        (redeemReturnTrueLine +++ Func.last .ret) := rfl

/-- The shared delegated redemption walk: the guarded debit writes a single
address-shaped balance key at the normalized owner argument, the external
value `CALL` is identified with a retained child message whose
allowance-region delta is supplied by the recursion hypothesis, and the
trailing success guard contributes neither counted records nor storage
writes. -/
private theorem Exec.Frame.CountedCursor.redeemFromAllowanceStorage
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {ownerArg amountArg target : B256} {sendPrefix successLine : Line}
    {successLast : Linst} {img : Bytes} {errSlot : Nat} {reason : String}
    (cursor : frame.CountedCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (redeemFromBody ownerArg amountArg sendPrefix errSlot
        (successLine +++ Func.last successLast)) frame.post)
    (herr : ((weth10 dp).main :: weth10Aux)[errSlot]? =
      some (Func.revWith reason))
    (htarget : frame.sevm.currentTarget = ca)
    (hstack : [] <<+ cursor.pre.stack)
    (hwf : Mem.Wf cursor.pre.memory)
    (hreads : Mem.Reads cursor.pre.memory img)
    (hcursorCode : some (cursor.pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hsendChildless : ∀ n ∈ sendPrefix, NinstIsChildless n)
    (hsend : ∀ {sendPre callPre : Devm} {value : B256} {tail : Stack},
      value :: tail <<+ sendPre.stack →
      Line.Run frame.sevm sendPre sendPrefix callPre →
      ValueCallOperandPrefix frame.sevm sendPre callPre value target tail)
    (hsuccessChildless : ∀ n ∈ successLine, NinstIsChildless n)
    (hsuccessStor : Func.Inv Devm.getStor Devm.getStor
      (successLine +++ Func.last successLast))
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    ∀ key, InRegion .allowance key →
      (Devm.getStor frame.post ca).get key =
        applyAllowanceLedger (Devm.getStor cursor.pre ca)
          (Exec.attributionInner dp ca frame.run) key := by
  rcases frame with ⟨fpc, e, fpre, fout, frun, fcommitted⟩
  cases fout with
  | error err => simp [Execution.commits] at fcommitted
  | ok fpost =>
      intro key hkey
      have htargetE : e.currentTarget = ca := htarget
      -- the guarded balance check
      unfold redeemFromBody at cursor
      rcases cursor.peelChildlessLine
          (line := redeemFromCheckLine ownerArg amountArg)
          (by simp [redeemFromCheckLine, loadArgBalanceAmount, addressArg,
            normalizeAddress, pushAddressMask, balanceTooSmall, arg, cdl,
            NinstIsChildless, Ninst.pushB256]) with
        ⟨branchCursor, hcheck⟩
      unfold redeemFromCheckLine at hcheck
      rcases of_run_append (loadArgBalanceAmount ownerArg amountArg)
          hcheck with
        ⟨afterLoad, hload, hguard⟩
      rcases prefix_of_loadArgBalanceAmount ownerArg amountArg hstack
          hload with
        ⟨balance, owner, howner, _hbalance, hloadStack⟩
      have hkeyNe : owner ≠ key := by
        refine (allowanceRegion_ne_validAdr hkey ?_).symm
        rw [howner]
        exact normalizedAddress_valid (Sevm.argWord e ownerArg)
      have hguardStack : (balance <? Sevm.argWord e amountArg) :: balance ::
          Sevm.argWord e amountArg :: owner :: [] <<+
            branchCursor.pre.stack :=
        prefix_of_balanceTooSmall hloadStack hguard
      rcases branchCursor.selectBranchLeftWithBurn
          (not_run_call_revWith (burnBalanceError_lookup dp)) with
        ⟨successCursor, hbalancePopBy⟩
      have hbalancePop := Devm.PopBurn.of_popBurnBy hbalancePopBy
      have hpopStack := hbalancePop.stack
      simp only [Stack.Pop, Split, List.nil_append,
        List.cons_append] at hpopStack
      rw [hpopStack] at hguardStack
      have hflag : (balance <? Sevm.argWord e amountArg) = 0 :=
        pref_head_unique hguardStack (pref_append [0] successCursor.pre.stack)
      rw [hflag] at hguardStack
      have hsuccessStack : balance :: Sevm.argWord e amountArg ::
          owner :: [] <<+ successCursor.pre.stack :=
        cons_pref_cons_inv hguardStack
      have hcheckStor : Devm.getStor cursor.pre =
          Devm.getStor successCursor.pre :=
        (Line.of_inv Devm.getStor (by line_inv) hload).trans
          ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
            (PopBurn.Inv.inv hbalancePop))
      have hcheckCode : Devm.getCode cursor.pre =
          Devm.getCode successCursor.pre :=
        (Line.of_inv Devm.getCode (by line_inv) hload).trans
          ((Line.of_inv Devm.getCode (by line_inv) hguard).trans
            (funext (getCode_eq_of_state_eq hbalancePop.state)))
      have hcheckMem : cursor.pre.memory = successCursor.pre.memory :=
        (Line.of_inv Devm.memory (by line_inv) hload).trans
          ((Line.of_inv Devm.memory (by line_inv) hguard).trans
            hbalancePop.memory)
      -- the owner-key debit
      rcases successCursor.peelChildlessLine (line := debitLoadedBalance)
          (by simp [debitLoadedBalance, NinstIsChildless]) with
        ⟨afterDebitCursor, hdebit⟩
      have hdebitCode : Devm.getCode successCursor.pre =
          Devm.getCode afterDebitCursor.pre :=
        Line.of_inv Devm.getCode (by line_inv) hdebit
      have hdebitMem : successCursor.pre.memory =
          afterDebitCursor.pre.memory :=
        Line.of_inv Devm.memory (by line_inv) hdebit
      unfold debitLoadedBalance at hdebit
      rcases Line.of_run_cons hdebit with ⟨d1, hsub, hdebit1⟩
      have hpD1 : (balance - Sevm.argWord e amountArg) ::
          owner :: [] <<+ d1.stack :=
        prefix_of_sub hsub hsuccessStack
      rcases Line.of_run_cons hdebit1 with ⟨d2, hswap, hdebit2⟩
      have hswapCoreD : Stack.Swap (0 : Fin 16).val
          [balance - Sevm.argWord e amountArg, owner]
          [owner, balance - Sevm.argWord e amountArg] :=
        Stack.swapCore_zero
      have hpD2 : owner ::
          (balance - Sevm.argWord e amountArg) :: [] <<+ d2.stack :=
        Stack.prefix_of_swap hswapCoreD (of_run_swap hswap) hpD1
      rcases Line.of_run_cons hdebit2 with ⟨d3, hstore, hnilD⟩
      cases hnilD
      have hsetDebit : Devm.getStor afterDebitCursor.pre e.currentTarget =
          (Devm.getStor d2 e.currentTarget).set owner
            (balance - Sevm.argWord e amountArg) :=
        sstore_getStor_set hstore hpD2
      have hdebitStorPre : Devm.getStor successCursor.pre =
          Devm.getStor d2 :=
        (Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hsub Line.Run.nil)).trans
          (Line.of_inv Devm.getStor (by line_inv)
            (Line.Run.cons hswap Line.Run.nil))
      -- the burn event and the send operands
      rcases afterDebitCursor.peelChildlessLine
          (line := redeemFromEventLine ownerArg amountArg)
          (by simp [redeemFromEventLine, addressArg, normalizeAddress,
            pushAddressMask, arg, cdl, emitTransfer, Blanc.transferFromLog,
            mstoreAt, logWith, NinstIsChildless, Ninst.pushB256]) with
        ⟨sendCursor, heventRun⟩
      unfold redeemFromEventLine at heventRun
      rcases of_run_append (addressArg ownerArg) heventRun with
        ⟨eventPre, hownerRun, htailRun⟩
      have hcallerStor : Devm.getStor afterDebitCursor.pre =
          Devm.getStor eventPre :=
        Line.of_inv Devm.getStor (by line_inv) hownerRun
      have hcallerCode : Devm.getCode afterDebitCursor.pre =
          Devm.getCode eventPre :=
        Line.of_inv Devm.getCode (by line_inv) hownerRun
      have hcallerMem : afterDebitCursor.pre.memory = eventPre.memory :=
        Line.of_inv Devm.memory (by line_inv) hownerRun
      have hownerStack : owner :: [] <<+ eventPre.stack := by
        rw [howner]
        exact prefix_of_addressArg nil_pref hownerRun
      have hwfEvent : Mem.Wf eventPre.memory := by
        rw [← hcallerMem, ← hdebitMem, ← hcheckMem]
        exact hwf
      have hreadsEvent : Mem.Reads eventPre.memory img := by
        rw [← hcallerMem, ← hdebitMem, ← hcheckMem]
        exact hreads
      obtain ⟨hsendStack, _heventLogs, heventStor, _heventBal, heventCode,
          _heventOutput, _hwfSend, _hreadsSend⟩ :=
        burnEventTail_effect_frame hownerStack hwfEvent hreadsEvent htailRun
      rcases sendCursor.peelChildlessLine (line := sendPrefix)
          hsendChildless with
        ⟨callCursor, hsendRun⟩
      have sendEvidence := hsend hsendStack hsendRun
      have hcallStor : Devm.getStor afterDebitCursor.pre =
          Devm.getStor callCursor.pre :=
        hcallerStor.trans (heventStor.symm.trans sendEvidence.storage)
      have hcallCode : Devm.getCode cursor.pre =
          Devm.getCode callCursor.pre :=
        hcheckCode.trans (hdebitCode.trans
          (hcallerCode.trans (heventCode.symm.trans sendEvidence.code)))
      have hpreCall : (Devm.getStor callCursor.pre e.currentTarget).get key =
          (Devm.getStor cursor.pre e.currentTarget).get key := by
        rw [← congrFun hcallStor e.currentTarget, hsetDebit,
          Stor.get_set_ne _ hkeyNe _,
          ← congrFun hdebitStorPre e.currentTarget,
          ← congrFun hcheckStor e.currentTarget]
      have hpreCallCa : (Devm.getStor callCursor.pre ca).get key =
          (Devm.getStor cursor.pre ca).get key := by
        rw [htargetE] at hpreCall
        exact hpreCall
      have hcallCodeAt : some (callCursor.pre.getCode ca).toList =
          Prog.compile (weth10 dp) := by
        rw [← congrFun hcallCode ca]
        exact hcursorCode
      -- cross the external value CALL
      have hcallRun := callCursor.run
      cases hcallRun with
      | next hcompiled htailCompiled =>
          rename_i midD
          have hat : Ninst.At e.code callCursor.pc Ninst.call :=
            ninstAt_of_subcode_next_redeem callCursor.codeSlice
          obtain ⟨nextBoundary, nextSub⟩ :=
            Func.noPushBefore_next callCursor.codeSlice
              callCursor.codeBoundary
          rcases callCursor.parentPrefix with ⟨actionsBefore, hbefore⟩
          rcases Exec.Frame.advance_runCompiled_next
              (frame := ⟨fpc, e, fpre, .ok fpost, frun, fcommitted⟩)
              callCursor.current hbefore hat hcompiled with
            ⟨xl, continuation, selected, occurrence, hedge, _hnextPrefix⟩
          rcases hedge.exists_counted with ⟨counted, hcountedEdge⟩
          rcases occurrence with
            ⟨_opc, _ocurrent, _ocont, _obefore, _oselected, _oprefix, _oat,
              ofilled, ostep, _oprec, _oedge⟩
          have hstepAt : Ninst.StepRun callCursor.pc e callCursor.pre
              Ninst.call xl (.ok midD) :=
            Ninst.stepRun_pc_irrel (pc' := callCursor.pc)
              (by simp [Ninst.pcFree]) ostep
          -- the trailing guard excludes the reverter arm
          have htailPlain : Func.Run ((weth10 dp).main :: weth10Aux) e midD
              (Ninst.iszero ::: ((.call errSlot) <?>
                (successLine +++ Func.last successLast))) fpost :=
            Func.Run.of_runCompiled htailCompiled
          rcases of_run_next htailPlain with
            ⟨afterIszero, hiszeroRun, hbranchPlain⟩
          rcases of_run_branch_call_revWith herr
              hbranchPlain with
            ⟨afterGuard, hguardPop, _hsuccessRun⟩
          rcases sendEvidence.stack with ⟨gasWord, hcallStack⟩
          have hcall : Ninst.Run e callCursor.pre Ninst.call midD :=
            Ninst.Run.of_runCompiled hcompiled
          rcases of_run_call_val_with_depth_frame hcallStack hcall with
              hfailed | hsuccess
          · exfalso
            have htest := prefix_of_iszero hiszeroRun hfailed.1
            have hguardStack' := hguardPop.stack
            simp only [Stack.Pop, Split, List.nil_append,
              List.cons_append] at hguardStack'
            rw [hguardStack'] at htest
            have hzero : ((0 : B256) =? 0) = 0 :=
              pref_head_unique htest (pref_append [(0 : B256)] afterGuard.stack)
            rw [show ((0 : B256) =? 0) = 1 from by
              simp [B256.eqCheck]] at hzero
            exact B256.zero_ne_one hzero.symm
          · rcases hsuccess with
              ⟨callParent, child, xlRaw, hasDelegation, code, availableGas,
                rawPc, hrawStep, hdepthPos, _hcallStackEq, hparentState,
                _hparentMemory, _hparentLogs, _hparentOutput, hdelegation,
                hrawFilled, hprocess, hclean, _hresume, hmidState,
                _hreturnData, _hmidMemory, hmidStack⟩
            have halign := Ninst.StepRun.unique_exec_of_filled ofilled
              hrawFilled hstepAt hrawStep
            cases halign.1
            obtain ⟨retained⟩ := exists_retainedXlot_of_filled ofilled
            have hcommits : retained.RawCommits := by
              cases retained with
              | none => trivial
              | some retainedRun =>
                  exact Frame.raw_commits_of_settlementCommits
                    (ProcessMessage.settlementCommits_of_some_ok_clean
                      hprocess hclean)
            have hparent : callCursor.pre.state =
                (callMsg e callParent
                  (min gasWord.toNat (except64th availableGas) +
                    (if (Sevm.argWord e amountArg).toNat = 0 then 0
                      else gCallStipend))
                  (Sevm.argWord e amountArg) e.currentTarget target.toAdr
                  target.toAdr true false
                  ((callCursor.pre.memory.read (0 : B256).toNat
                    (0 : B256).toNat).1) code hasDelegation).benv.state := by
              simpa only [callMsg] using hparentState.symm
            have hmsgDepth :
                (callMsg e callParent
                  (min gasWord.toNat (except64th availableGas) +
                    (if (Sevm.argWord e amountArg).toNat = 0 then 0
                      else gCallStipend))
                  (Sevm.argWord e amountArg) e.currentTarget target.toAdr
                  target.toAdr true false
                  ((callCursor.pre.memory.read (0 : B256).toNat
                    (0 : B256).toNat).1) code hasDelegation).depth <
                  e.depth := by
              dsimp only [callMsg]
              omega
            have htargetCode :
                (callMsg e callParent
                  (min gasWord.toNat (except64th availableGas) +
                    (if (Sevm.argWord e amountArg).toNat = 0 then 0
                      else gCallStipend))
                  (Sevm.argWord e amountArg) e.currentTarget target.toAdr
                  target.toAdr true false
                  ((callCursor.pre.memory.read (0 : B256).toNat
                    (0 : B256).toNat).1) code hasDelegation).currentTarget =
                  ca →
                some code.toList = Prog.compile (weth10 dp) := by
              intro hct
              have htargetCa : target.toAdr = ca := by
                simpa only [callMsg] using hct
              exact callbackCode_eq_compiled_of_target_eq hcallCodeAt
                htargetCa hdelegation
            have childEffect :=
              ProcessMessageTrace.allowanceRegionDelta_of_forallDeeperAt
                (dp := dp) (ca := ca) (depth := e.depth)
                (parent := callCursor.pre)
                ⟨_, retained, hprocess⟩ hparent hmsgDepth hcallCodeAt
                htargetCode
                (by
                  intro hct
                  have htargetCa : target.toAdr = ca := by
                    simpa only [callMsg] using hct
                  simp only [callMsg, htargetCa])
                hdeeper
            -- the trailing guard is childless and storage neutral
            obtain ⟨htailNil, htailStor⟩ :=
              Exec.tailGuard_attributionInner_storage
                (dp := dp) (ca := ca) (_errReason := "")
                (rest := callParent.stack)
                continuation fcommitted htailCompiled nextSub nextBoundary
                hmidStack hsuccessChildless hsuccessStor
            -- the counted stream of the frame is exactly the child's
            have hprefixSplit := callCursor.countedPrefix.descendantCounted_eq
            change Exec.attributionInner dp ca frun =
              [] ++ Exec.attributionInner dp ca callCursor.current
                at hprefixSplit
            have hedgeSplit := hcountedEdge.descendantCounted_eq
            change Exec.attributionInner dp ca callCursor.current =
              counted ++ Exec.attributionInner dp ca continuation
                at hedgeSplit
            have hcountedEq :=
              Exec.Deriv.ParentStepCounted.selected_eq_retained_of_call
                hat ofilled hstepAt retained hcommits hcountedEdge
            have hinnerEq : Exec.attributionInner dp ca frun =
                retained.attributionStream dp ca := by
              rw [hprefixSplit, List.nil_append, hedgeSplit, hcountedEq,
                htailNil, List.append_nil]
            calc (Devm.getStor fpost ca).get key
                = (Devm.getStor midD ca).get key := by
                  rw [congrFun htailStor ca]
              _ = (Devm.getStor child ca).get key :=
                  congrArg (fun state : State => (state.getStor ca).get key)
                    hmidState
              _ = applyAllowanceLedger (Devm.getStor callCursor.pre ca)
                    (retained.attributionStream dp ca) key :=
                  childEffect.storage key hkey
              _ = applyAllowanceLedger (Devm.getStor cursor.pre ca)
                    (retained.attributionStream dp ca) key :=
                  applyAllowanceLedger_congr hpreCallCa
              _ = applyAllowanceLedger (Devm.getStor cursor.pre ca)
                    (Exec.attributionInner dp ca frun) key := by
                  rw [hinnerEq]

/-! ## The two delegated redemption arms

Each arm composes the wrapper's singleton replay with the core's child
transport: the frame's own record carries the wrapper's exact
self/max/finite allowance fork, and the committed send child's counted
stream is the frame's proper-descendant stream. -/

/-- Delegated `withdrawFrom` transports the allowance region: its own record
is the wrapper's exact allowance fork, the core's debit is address-shaped at
the normalized owner argument, and the committed send child's counted stream
is transported by the recursion hypothesis. -/
theorem Exec.Frame.allowanceRegionEffect_of_withdrawFrom
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = withdrawFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmem : (Sevm.selector frame.sevm, nonpayable withdrawFrom) ∈
      weth10Funcs dp := by
    rw [hselector]
    simp [withdrawFromSelector, weth10Funcs]
  rcases frame.compiledSelectorBodyCursorCountedSilent context hnonempty
      hmem with
    ⟨wrapperCursor, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨spendCursor, hnonpayableSilent⟩
  have hspendSilent : Devm.DispatchSilent frame.pre spendCursor.pre :=
    hentrySilent.trans hnonpayableSilent
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (spendCallerAllowanceThen 2 withdrawFromCoreSlot) frame.post
    at spendCursor
  rcases spendCursor.enterSpendCallerAllowanceThenFork
      context.invocation.2.2.2 (allowanceError_lookup dp)
      (by rw [← hspendSilent.memory]; exact context.memory_wf)
      (by rw [← hspendSilent.memory]; exact context.memory_reads_empty) with
    ⟨body, hget, coreCursor, hwfCore, ⟨imgCore, hreadsCore⟩, hcodeCore,
      hfork⟩
  have hbody : body = withdrawFromCore := by
    simpa [weth10, weth10Aux, withdrawFromCoreSlot] using hget.symm
  subst body
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (redeemFromBody 0 2 (redeemSendToArgPrefix 1) etherTransferErrorSlot
      (Func.last .stop)) frame.post at coreCursor
  have htarget : frame.sevm.currentTarget = ca := context.invocation.2.1
  have hstorage := coreCursor.redeemFromAllowanceStorage
    (successLine := []) (target := Sevm.argWord frame.sevm 1)
    (etherTransferError_lookup dp) htarget nil_pref hwfCore hreadsCore
    (by
      rw [← congrFun hcodeCore ca,
        ← getCode_eq_of_state_eq hspendSilent.state ca]
      exact context.installed.1)
    (by simp [redeemSendToArgPrefix, pushList, arg, cdl, NinstIsChildless,
      Ninst.pushB256])
    (by
      intro sendPre callPre value tail hp hrun
      exact redeemSendToArgPrefix_effect 1 hp hrun)
    (by simp)
    (by func_inv)
    hdeeper
  have hneFlash : withdrawFromSelector ≠ flashLoanSelector := by
    decide +kernel
  have hneApprove : withdrawFromSelector ≠ approveSelector := by
    decide +kernel
  have hneApproveCall :
      withdrawFromSelector ≠ approveAndCallSelector := by decide +kernel
  have hnePermit : withdrawFromSelector ≠ permitSelector := by decide +kernel
  have hnotflash : isFlashInvocation frame.sevm = false := by
    simp [isFlashInvocation, hselector, hneFlash]
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      CountedFrame.ofFrame dp ca frame ::
        Exec.attributionInner dp ca frame.run := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframe,
      Exec.frameContribution_eq_cons dp ca frame
        (Exec.attributionInner dp ca frame.run) context.invocation hnotflash]
  have hpreStor : Devm.getStor frame.pre = Devm.getStor spendCursor.pre :=
    funext (getStor_eq_of_state_eq hspendSilent.state)
  rw [hstream]
  refine ⟨fun key hkey => ?_,
    Exec.installedCodeEq_committed frame.run frame.committed
      context.installed⟩
  have hmid : (Devm.getStor coreCursor.pre ca).get key =
      applyAllowanceLedger (Devm.getStor frame.pre ca)
        [CountedFrame.ofFrame dp ca frame] key := by
    rw [applyAllowanceLedger_singleton]
    rcases hfork with ⟨hself, hstorEq⟩ | ⟨hnself, hmaxOrFinite⟩
    · have hown : (CountedFrame.ofFrame dp ca frame).allowance = none := by
        show frameAllowanceEvent frame.sevm frame.pre frame.post = none
        simp [frameAllowanceEvent, hnonempty, hselector, hneApprove,
          hneApproveCall, hnePermit, hself]
      rw [htarget] at hstorEq
      rw [hown, hstorEq, ← congrFun hpreStor ca]
    · rcases hmaxOrFinite with
          ⟨hmaxGet, hstorEq⟩ |
          ⟨allowance, hneMax, hallowGet, hstorSet⟩
      · have hbefore :
            (Devm.getStor frame.pre frame.sevm.currentTarget).get
              (callerAllowanceRuntimeKey frame.sevm) = B256.max := by
          rw [congrFun hpreStor frame.sevm.currentTarget]
          exact hmaxGet
        have hown : (CountedFrame.ofFrame dp ca frame).allowance =
            some { owner := Sevm.argWord frame.sevm 0
                   spender := frame.sevm.caller.toB256
                   caller := frame.sevm.caller
                   depth := frame.sevm.depth
                   visit := .spendMax } := by
          show frameAllowanceEvent frame.sevm frame.pre frame.post = _
          simp [frameAllowanceEvent, hnonempty, hselector, hneApprove,
            hneApproveCall, hnePermit, hnself, hbefore]
        rw [htarget] at hstorEq
        rw [hown]
        simp only [AllowanceVisit.written?, ite_self]
        rw [hstorEq, ← congrFun hpreStor ca]
      · have hbefore :
            (Devm.getStor frame.pre frame.sevm.currentTarget).get
              (callerAllowanceRuntimeKey frame.sevm) = allowance := by
          rw [congrFun hpreStor frame.sevm.currentTarget]
          exact hallowGet
        have hown : (CountedFrame.ofFrame dp ca frame).allowance =
            some { owner := Sevm.argWord frame.sevm 0
                   spender := frame.sevm.caller.toB256
                   caller := frame.sevm.caller
                   depth := frame.sevm.depth
                   visit := .spendFinite allowance
                     (allowance - Sevm.argWord frame.sevm 2) } := by
          show frameAllowanceEvent frame.sevm frame.pre frame.post = _
          simp [frameAllowanceEvent, hnonempty, hselector, hneApprove,
            hneApproveCall, hnePermit, hnself, hbefore, hneMax]
        rw [htarget] at hstorSet
        rw [hown]
        simp only [AllowanceEvent.key, AllowanceVisit.written?]
        rw [hstorSet]
        by_cases hpk :
            projectedAllowanceKey (Sevm.argWord frame.sevm 0)
              frame.sevm.caller.toB256 = key
        · rw [if_pos hpk, ← hpk, ← callerAllowanceRuntimeKey_eq_projected]
          exact Stor.get_set_self _ _ _
        · have hne : callerAllowanceRuntimeKey frame.sevm ≠ key := by
            rw [callerAllowanceRuntimeKey_eq_projected]
            exact hpk
          rw [if_neg hpk, Stor.get_set_ne _ hne _, ← congrFun hpreStor ca]
  have hsplit := applyAllowanceLedger_append (Devm.getStor frame.pre ca)
    (Devm.getStor coreCursor.pre ca) [CountedFrame.ofFrame dp ca frame]
    (Exec.attributionInner dp ca frame.run) key hmid
  simp only [List.cons_append, List.nil_append] at hsplit
  rw [hsplit]
  exact hstorage key hkey

/-- Delegated `transferFrom` with a zero raw recipient word is a redemption
to the caller, and transports the allowance region exactly as delegated
`withdrawFrom` does. -/
theorem Exec.Frame.allowanceRegionEffect_of_transferFromZero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = transferFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hzero : Sevm.argWord frame.sevm 1 = 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmem : (Sevm.selector frame.sevm, nonpayable transferFrom) ∈
      weth10Funcs dp := by
    rw [hselector]
    simp [transferFromSelector, weth10Funcs]
  rcases frame.compiledSelectorBodyCursorCountedSilent context hnonempty
      hmem with
    ⟨wrapperCursor, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨spendCursor, hnonpayableSilent⟩
  have hspendSilent : Devm.DispatchSilent frame.pre spendCursor.pre :=
    hentrySilent.trans hnonpayableSilent
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (spendCallerAllowanceThen 2 transferFromCoreSlot) frame.post
    at spendCursor
  rcases spendCursor.enterSpendCallerAllowanceThenFork
      context.invocation.2.2.2 (allowanceError_lookup dp)
      (by rw [← hspendSilent.memory]; exact context.memory_wf)
      (by rw [← hspendSilent.memory]; exact context.memory_reads_empty) with
    ⟨body, hget, coreCursor, hwfCore, ⟨imgCore, hreadsCore⟩, hcodeCore,
      hfork⟩
  have hbody : body = transferFromCore := by
    simpa [weth10, weth10Aux, transferFromCoreSlot] using hget.symm
  subst body
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    ((arg 1 ++ [iszero]) +++ (transferFromZero <?> transferFromNonzero))
    frame.post at coreCursor
  rcases coreCursor.peelChildlessLine
      (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨targetBranchCursor, htargetLine⟩
  have htargetPrefix : [Sevm.argWord frame.sevm 1 =? 0] <<+
      targetBranchCursor.pre.stack := by
    rcases of_run_append (arg 1) htargetLine with
      ⟨afterArg, harg, hzeroLine⟩
    rcases Line.of_run_cons hzeroLine with ⟨afterZero, hzeroRun, hnil⟩
    cases hnil
    exact prefix_of_iszero hzeroRun (prefix_of_arg nil_pref harg)
  have htargetCheck : (Sevm.argWord frame.sevm 1 =? 0) = 1 := by
    simp [B256.eqCheck, hzero]
  rw [htargetCheck] at htargetPrefix
  rcases targetBranchCursor.selectBranchSuccSilent (flag := (1 : B256))
      (by decide) htargetPrefix with
    ⟨zeroCursor, _hzeroStack, hbranchSilent⟩
  have hlineStor : Devm.getStor coreCursor.pre =
      Devm.getStor targetBranchCursor.pre :=
    Line.of_inv Devm.getStor (by line_inv) htargetLine
  have hlineCode : Devm.getCode coreCursor.pre =
      Devm.getCode targetBranchCursor.pre :=
    Line.of_inv Devm.getCode (by line_inv) htargetLine
  have hlineMem : coreCursor.pre.memory = targetBranchCursor.pre.memory :=
    Line.of_inv Devm.memory (by line_inv) htargetLine
  have hcoreToZero : Devm.getStor coreCursor.pre =
      Devm.getStor zeroCursor.pre := by
    rw [hlineStor, funext (getStor_eq_of_state_eq hbranchSilent.state)]
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (redeemFromBody 0 2 redeemSendToCallerPrefix ethTransferErrorSlot
      (redeemReturnTrueLine +++ Func.last .ret)) frame.post at zeroCursor
  have htarget : frame.sevm.currentTarget = ca := context.invocation.2.1
  have hstorage := zeroCursor.redeemFromAllowanceStorage
    (target := frame.sevm.caller.toB256)
    (ethTransferError_lookup dp) htarget nil_pref
    (by rw [← hbranchSilent.memory, ← hlineMem]; exact hwfCore)
    (show Mem.Reads zeroCursor.pre.memory imgCore by
      rw [← hbranchSilent.memory, ← hlineMem]; exact hreadsCore)
    (by
      rw [← getCode_eq_of_state_eq hbranchSilent.state ca,
        ← congrFun hlineCode ca, ← congrFun hcodeCore ca,
        ← getCode_eq_of_state_eq hspendSilent.state ca]
      exact context.installed.1)
    (by simp [redeemSendToCallerPrefix, pushList, NinstIsChildless,
      Ninst.pushB256])
    (by
      intro sendPre callPre value tail hp hrun
      exact redeemSendToCallerPrefix_effect hp hrun)
    (by simp [redeemReturnTrueLine, mstoreAt, pushList, NinstIsChildless,
      Ninst.pushB256])
    (by func_inv)
    hdeeper
  have hneFlash : transferFromSelector ≠ flashLoanSelector := by
    decide +kernel
  have hneApprove : transferFromSelector ≠ approveSelector := by
    decide +kernel
  have hneApproveCall :
      transferFromSelector ≠ approveAndCallSelector := by decide +kernel
  have hnePermit : transferFromSelector ≠ permitSelector := by decide +kernel
  have hnotflash : isFlashInvocation frame.sevm = false := by
    simp [isFlashInvocation, hselector, hneFlash]
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      CountedFrame.ofFrame dp ca frame ::
        Exec.attributionInner dp ca frame.run := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframe,
      Exec.frameContribution_eq_cons dp ca frame
        (Exec.attributionInner dp ca frame.run) context.invocation hnotflash]
  have hpreStor : Devm.getStor frame.pre = Devm.getStor spendCursor.pre :=
    funext (getStor_eq_of_state_eq hspendSilent.state)
  rw [hstream]
  refine ⟨fun key hkey => ?_,
    Exec.installedCodeEq_committed frame.run frame.committed
      context.installed⟩
  have hmid : (Devm.getStor zeroCursor.pre ca).get key =
      applyAllowanceLedger (Devm.getStor frame.pre ca)
        [CountedFrame.ofFrame dp ca frame] key := by
    rw [applyAllowanceLedger_singleton, ← congrFun hcoreToZero ca]
    rcases hfork with ⟨hself, hstorEq⟩ | ⟨hnself, hmaxOrFinite⟩
    · have hown : (CountedFrame.ofFrame dp ca frame).allowance = none := by
        show frameAllowanceEvent frame.sevm frame.pre frame.post = none
        simp [frameAllowanceEvent, hnonempty, hselector, hneApprove,
          hneApproveCall, hnePermit, hself]
      rw [htarget] at hstorEq
      rw [hown, hstorEq, ← congrFun hpreStor ca]
    · rcases hmaxOrFinite with
          ⟨hmaxGet, hstorEq⟩ |
          ⟨allowance, hneMax, hallowGet, hstorSet⟩
      · have hbefore :
            (Devm.getStor frame.pre frame.sevm.currentTarget).get
              (callerAllowanceRuntimeKey frame.sevm) = B256.max := by
          rw [congrFun hpreStor frame.sevm.currentTarget]
          exact hmaxGet
        have hown : (CountedFrame.ofFrame dp ca frame).allowance =
            some { owner := Sevm.argWord frame.sevm 0
                   spender := frame.sevm.caller.toB256
                   caller := frame.sevm.caller
                   depth := frame.sevm.depth
                   visit := .spendMax } := by
          show frameAllowanceEvent frame.sevm frame.pre frame.post = _
          simp [frameAllowanceEvent, hnonempty, hselector, hneApprove,
            hneApproveCall, hnePermit, hnself, hbefore]
        rw [htarget] at hstorEq
        rw [hown]
        simp only [AllowanceVisit.written?, ite_self]
        rw [hstorEq, ← congrFun hpreStor ca]
      · have hbefore :
            (Devm.getStor frame.pre frame.sevm.currentTarget).get
              (callerAllowanceRuntimeKey frame.sevm) = allowance := by
          rw [congrFun hpreStor frame.sevm.currentTarget]
          exact hallowGet
        have hown : (CountedFrame.ofFrame dp ca frame).allowance =
            some { owner := Sevm.argWord frame.sevm 0
                   spender := frame.sevm.caller.toB256
                   caller := frame.sevm.caller
                   depth := frame.sevm.depth
                   visit := .spendFinite allowance
                     (allowance - Sevm.argWord frame.sevm 2) } := by
          show frameAllowanceEvent frame.sevm frame.pre frame.post = _
          simp [frameAllowanceEvent, hnonempty, hselector, hneApprove,
            hneApproveCall, hnePermit, hnself, hbefore, hneMax]
        rw [htarget] at hstorSet
        rw [hown]
        simp only [AllowanceEvent.key, AllowanceVisit.written?]
        rw [hstorSet]
        by_cases hpk :
            projectedAllowanceKey (Sevm.argWord frame.sevm 0)
              frame.sevm.caller.toB256 = key
        · rw [if_pos hpk, ← hpk, ← callerAllowanceRuntimeKey_eq_projected]
          exact Stor.get_set_self _ _ _
        · have hne : callerAllowanceRuntimeKey frame.sevm ≠ key := by
            rw [callerAllowanceRuntimeKey_eq_projected]
            exact hpk
          rw [if_neg hpk, Stor.get_set_ne _ hne _, ← congrFun hpreStor ca]
  have hsplit := applyAllowanceLedger_append (Devm.getStor frame.pre ca)
    (Devm.getStor zeroCursor.pre ca) [CountedFrame.ofFrame dp ca frame]
    (Exec.attributionInner dp ca frame.run) key hmid
  simp only [List.cons_append, List.nil_append] at hsplit
  rw [hsplit]
  exact hstorage key hkey

end Weth10

end Blanc
