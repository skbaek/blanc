import Blanc.Weth10AllowanceArmsRedeem

/-!
The flash-loan arm of the allowance-region transport.

`flashLoan` is the one dispatched selector whose own attribution record is
placed *after* its descendant stream: the runtime settles the repayment
allowance only once the borrower's callback has returned, and the canonical
repayment pattern grants that allowance inside the callback.  Its counted
contribution is therefore `inner ++ [own]` rather than `own :: inner`, and the
region transport splits at the post-callback settlement state — the
pre-callback prefix together with the borrower subtree carries `inner`, and
the settlement plus its shared burn continuation carries the single own
record.

The semantic heart of the arm is the post-state reconstruction: the committed
post state alone determines which settlement arm the runtime took, because the
burn continuation leaves the tagged repayment cell exactly as settlement wrote
it.  Reading `B256.max` there means the infinite-allowance arm ran and wrote
nothing; any other word `after` means the finite arm reduced an entry
allowance of exactly `after + amount`, the reconstruction `after + amount`
being exact precisely because the finite arm is guarded by
`amount ≤ allowance`.

Three pieces of that transport are established here.

* `flashSettlement_reconstruction` is the post-state reconstruction
  agreement, and `flashSettlement_allowanceLedger` /
  `flashSettlement_allowanceRegionEffect` are the settlement segment: from the
  post-callback settlement state to the committed post state, the region moves
  by exactly the frame's own single counted record.
* `Exec.Frame.attributionInner_eq_callback_of_flashLoan` is the bridge from
  the action-labelled flash chronology to the counted ledger: the whole
  proper-descendant counted stream of an authentic committed `flashLoan` frame
  is the attribution stream of its single retained borrower callback.  Every
  source instruction before that callback is childless and every alternate
  branch arm is a fixed nonreturning reverter, and the post-callback decoder,
  the settlement and the burn continuation likewise cross no recursive child.
* `Exec.Frame.flashCallbackAndSettlement` adds the settlement handoff: the
  settlement phase starts from exactly the storage the callback committed.

What is still open is the pre-callback prefix's own allowance-region
locality, the borrower message's `ProcessMessageTrace` data at the callback
boundary, and the memory image at the settlement entry that pins the hashed
repayment key.  All three need the callback boundary's stack and memory
witnesses, which currently live only inside
`Weth10HolderFlowFlashChronology`'s private compiled-cursor walk.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Weth10

/-! ## Key shape

`Weth10AllowanceArmsRedeem` and its siblings keep their key-shape helper
private, so this module re-declares it together with the two projections the
settlement segment needs. -/

/-- A tagged allowance key is never an address-shaped balance key. -/
private theorem allowanceRegion_ne_validAdr {key k : B256}
    (hkey : InRegion .allowance key) (hvalid : ValidAdr k) : key ≠ k := by
  intro h
  rcases hvalid with ⟨a, ha⟩
  apply regions_disjoint (x := .allowance) (y := .balance) (by decide)
    key hkey
  rw [h, ← ha]
  simpa only [balanceKey] using balanceKey_region a

/-- A tagged allowance key is never itself address-shaped. -/
private theorem allowanceRegion_not_valid {key : B256}
    (hkey : InRegion .allowance key) : ¬ ValidAdr key := fun hvalid =>
  allowanceRegion_ne_validAdr hkey hvalid rfl

/-- A tagged allowance key is never the flash counter slot. -/
private theorem allowanceRegion_ne_flashSlot {key : B256}
    (hkey : InRegion .allowance key) : key ≠ flashMintedSlot := by
  intro h
  refine regions_disjoint (x := .allowance) (y := .flash) (by decide)
    key hkey ?_
  rw [h]
  exact flashMintedSlot_region

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
private theorem Devm.eq_of_burnBy_flash
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
        Devm.eq_of_burnBy_flash (Devm.BurnBy.of_burn hburn hgas)
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

/-! ## Counted crossings

`Weth10AttributionChronology` exposes only the flag-directed branch
selections, and keeps no counted analogue of the compiled cursor's internal
source-call crossing.  The flash body needs one genuinely two-armed
selection and the internal jump into the shared settlement and burn bodies,
so this module rebuilds those two. -/

/-- Select whichever branch arm the committed run actually took, preserving
the empty counted prefix; the counted mirror of
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

/-- Follow one generated internal source call, preserving the empty counted
prefix; the counted mirror of `Exec.Frame.CompiledCursor.enterCall`. -/
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

/-! ## The post-callback settlement fork

`Weth10HolderFlowCompiled` keeps its reconstruction lemma private, so this
module re-proves it in the shape the counted ledger consumes. -/

/-- Post-state reconstruction of the flash repayment visit.  The burn
continuation never touches the tagged repayment cell, so the word the
committed post state holds there is exactly the word settlement wrote, and it
alone decides the fork: `B256.max` is the infinite-allowance arm, which wrote
nothing, and any other word `after` is the finite arm reducing an entry
allowance of exactly `after + amount`. -/
theorem flashSettlement_reconstruction
    {dp : DeployParams} {e : Sevm} {settlePre burnPre post : Devm}
    (houtcome : FlashAllowanceOutcome e settlePre burnPre)
    (hburn : Func.Run ((weth10 dp).main :: weth10Aux) e burnPre
      flashBurn post) :
    FlashAllowanceAccepted e settlePre burnPre
      (flashAllowanceBranchFromPost e post) := by
  have hkey := flashBurn_storage_at_allowanceKey dp hburn
  unfold flashAllowanceBranchFromPost
  rcases houtcome.1 with hmax | hfinite
  · have hpostmax : (Devm.getStor post e.currentTarget).get
        (flashAllowanceRuntimeKey e) = B256.max := by
      rw [hkey, hmax.2.1, hmax.1]
    rw [if_pos hpostmax]
    exact ⟨houtcome, rfl, hmax.1⟩
  · rcases hfinite with
      ⟨allowance, hnotmax, hle, hread, hwrite, _hlogs⟩
    have hpostafter : (Devm.getStor post e.currentTarget).get
        (flashAllowanceRuntimeKey e) =
          allowance - Sevm.argWord e 2 := by
      rw [hkey, hwrite, Stor.get_set_self]
    have hsuble : allowance - Sevm.argWord e 2 ≤ allowance := by
      apply B256.le_of_toNat_le_toNat
      rw [B256.toNat_sub_eq_of_le _ _ hle]
      omega
    have hallowlemax : allowance ≤ B256.max := B256.le_max allowance
    have hafternotmax :
        allowance - Sevm.argWord e 2 ≠ B256.max := by
      intro heq
      have hmaxle : B256.max ≤ allowance := by
        simpa only [heq] using hsuble
      exact hnotmax (le_antisymm hallowlemax hmaxle)
    have hpostnotmax : (Devm.getStor post e.currentTarget).get
        (flashAllowanceRuntimeKey e) ≠ B256.max := by
      rw [hpostafter]
      exact hafternotmax
    rw [if_neg hpostnotmax]
    have hbefore : (Devm.getStor post e.currentTarget).get
          (flashAllowanceRuntimeKey e) + Sevm.argWord e 2 = allowance := by
      rw [hpostafter]
      exact B256.sub_add_cancel
    refine ⟨houtcome, rfl, ?_, ?_, ?_, ?_⟩
    · rw [hbefore]
      exact hread
    · rw [hbefore]
      exact hnotmax
    · rw [hbefore]
      exact hle
    · rw [hbefore, hpostafter]

/-- Settlement and its burn continuation move no tagged allowance key other
than the runtime repayment cell: the settlement's only write is at that cell,
and the burn writes address-shaped balance keys and the flash counter. -/
private theorem flashSettlement_region_locality
    {dp : DeployParams} {e : Sevm} {settlePre burnPre post : Devm}
    (houtcome : FlashAllowanceOutcome e settlePre burnPre)
    (hburn : Func.Run ((weth10 dp).main :: weth10Aux) e burnPre
      flashBurn post)
    {key : B256} (hkey : InRegion .allowance key)
    (hne : flashAllowanceRuntimeKey e ≠ key) :
    (Devm.getStor post e.currentTarget).get key =
      (Devm.getStor settlePre e.currentTarget).get key := by
  rw [flashBurn_storage_get_of_not_valid dp key
    (allowanceRegion_not_valid hkey) (allowanceRegion_ne_flashSlot hkey)
    hburn]
  rcases houtcome.1 with hmax | hfinite
  · rw [hmax.2.1]
  · rcases hfinite with ⟨_allowance, _hnotmax, _hle, _hread, hwrite, _hlogs⟩
    rw [hwrite, Stor.get_set_ne _ hne]

/-! ## Local copies of the compiled flash body

`Weth10HolderFlowFlashChronology` publishes its decomposition of the flash
body, its post-callback decoder, the settlement and the burn continuation,
so this module consumes those directly.  Only the reverter-arm exclusion it
phrases in terms of `Func.revWith` is local. -/

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

/-! ## The childless prefix before the borrower callback

Every source instruction the flash body executes before the borrower `CALL`
is childless, and every alternate branch arm is a fixed nonreturning
reverter, so a counted cursor reaches the callback with an exactly empty
counted prefix. -/

/-- Reach the borrower callback from the public `flashLoan` body while
preserving the empty counted prefix; the counted mirror of
`Exec.Frame.CompiledCursor.reachFlashLoanSuccessTailCursor`. -/
private theorem Exec.Frame.CountedCursor.reachFlashCallback
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {final : Devm}
    (cursor : frame.CountedCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) flashLoan final) :
    Nonempty (frame.CountedCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      flashLoanSuccessTail final) := by
  rw [flashLoan_shape] at cursor
  unfold flashLoanBodyShape at cursor
  rcases cursor.peelChildlessLine (line := flashTokenLine) (by
      simp [flashTokenLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨tokenBranchCursor, _htoken⟩
  rcases tokenBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revWith (flashTokenError_lookup dp)) with
    ⟨amountCursor, -⟩
  unfold flashLoanPostAmount at amountCursor
  rcases amountCursor.peelChildlessLine (line := flashAmountLine) (by
      simp [flashAmountLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨amountBranchCursor, _hamount⟩
  rcases amountBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revWith (individualLimitError_lookup dp)) with
    ⟨counterCursor, -⟩
  unfold flashLoanPostCounter at counterCursor
  rcases counterCursor.peelChildlessLine (line := flashCounterLine) (by
      simp [flashCounterLine, pushFlashMintedSlot, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨totalCursor, _hcounter⟩
  rcases totalCursor.peelChildlessLine (line := flashTotalLine) (by
      simp [flashTotalLine, pushFlashMintedSlot, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨totalBranchCursor, _htotal⟩
  rcases totalBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revWith (totalLimitError_lookup dp)) with
    ⟨popCursor, -⟩
  unfold flashLoanPostTotal at popCursor
  rcases popCursor.peelChildlessLine (line := [Ninst.pop])
      (by simp [NinstIsChildless]) with
    ⟨mintCursor, _hpop⟩
  rcases mintCursor.peelChildlessLine (line := flashMintLine) (by
      simp [flashMintLine, addressArg, normalizeAddress, pushAddressMask,
        arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨eventCursor, _hmint⟩
  rcases eventCursor.peelChildlessLine (line := flashEventCheckLine) (by
      simp [flashEventCheckLine, mstoreAt, logWith, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨codeBranchCursor, _hevent⟩
  rcases codeBranchCursor.selectBranchLeftWithBurn
      (fun _ => not_run_rev) with
    ⟨setupCursor, -⟩
  unfold flashLoanPostCode at setupCursor
  rcases setupCursor.peelChildlessLine (line := flashCallbackSetupLine)
      (by
        simp [flashCallbackSetupLine, storeFlashCallbackHead, mstoreAt,
          pushList, forwardArgTail, arg, cdl, flashCallbackArgsSize,
          NinstIsChildless, Ninst.pushB256]) with
    ⟨callCursor, _hsetup⟩
  exact ⟨callCursor⟩

/-! ## The parent-only suffix after the borrower callback

Everything the frame executes after the callback returns is childless source
code, generated branch glue, internal table jumps, and fixed nonreturning
reverters, so it contributes no counted record. -/

/-- The shared burn continuation crosses no recursive child. -/
private theorem Exec.Frame.CountedCursor.finishFlashBurn
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {final : Devm}
    (cursor : frame.CountedCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) flashBurn final) :
    Exec.attributionInner dp ca frame.run = [] := by
  rw [flashBurn_shape] at cursor
  rcases cursor.peelChildlessLine (line := flashBurnGuardLine) (by
      simp [flashBurnGuardLine, loadArgBalanceAmount, balanceTooSmall,
        addressArg, normalizeAddress, arg, cdl, pushAddressMask,
        NinstIsChildless, Ninst.pushB256]) with
    ⟨branchCursor, _hguard⟩
  rcases branchCursor.selectBranchLeftWithBurn
      (not_run_call_revWith (burnBalanceError_lookup dp)) with
    ⟨successCursor, -⟩
  rcases successCursor.peelChildlessLine (line := flashBurnSuccessLine) (by
      simp [flashBurnSuccessLine, debitLoadedBalance, addressArg,
        normalizeAddress, pushAddressMask, arg, cdl, emitTransfer,
        Blanc.transferFromLog, mstoreAt, logWith, pushList,
        pushFlashMintedSlot, NinstIsChildless, Ninst.pushB256]) with
    ⟨lastCursor, _hsuccess⟩
  exact lastCursor.finishAttributionInner

/-- Settlement reaches the unique shared burn continuation through either
allowance arm, and neither arm crosses a recursive child. -/
private theorem Exec.Frame.CountedCursor.finishFlashSettle
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {final : Devm}
    (cursor : frame.CountedCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) flashSettle final)
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp)) :
    Exec.attributionInner dp ca frame.run = [] := by
  rw [flashSettle_shape] at cursor
  rcases cursor.peelChildlessLine (line := flashSettleKeyLine) (by
      simp [flashSettleKeyLine, addressArg, normalizeAddress,
        pushAddressMask, arg, cdl, mstoreAt, allowanceKeyFromMemory,
        pushList, isMax, NinstIsChildless, Ninst.pushB256]) with
    ⟨allowanceBranchCursor, _hkeyLine⟩
  rcases allowanceBranchCursor.selectBranchSplit with hfinite | hmax
  · rcases hfinite with ⟨finiteCursor⟩
    rcases finiteCursor.peelChildlessLine (line := flashSettleGuardLine) (by
        simp [flashSettleGuardLine, arg, cdl, balanceTooSmall,
          NinstIsChildless, Ninst.pushB256]) with
      ⟨guardBranchCursor, _hguard⟩
    rcases guardBranchCursor.selectBranchLeftWithBurn
        (not_run_call_revWith (allowanceError_lookup dp)) with
      ⟨successCursor, -⟩
    rcases successCursor.peelChildlessLine
        (line := flashSettleFiniteLine) (by
          simp [flashSettleFiniteLine, emitFlashApproval, arg, cdl,
            mstoreAt, logWith, NinstIsChildless, Ninst.pushB256]) with
      ⟨burnCallCursor, _hfiniteLine⟩
    obtain ⟨body, hget, ⟨burnCursor⟩⟩ := burnCallCursor.enterCall hcode
    have hbody : body = flashBurn := by
      simpa [weth10, weth10Aux, flashBurnSlot] using hget.symm
    subst body
    exact burnCursor.finishFlashBurn
  · rcases hmax with ⟨maxCursor⟩
    rcases maxCursor.peelChildlessLine (line := [Ninst.pop, Ninst.pop])
        (by simp [NinstIsChildless]) with
      ⟨burnCallCursor, _hpops⟩
    obtain ⟨body, hget, ⟨burnCursor⟩⟩ := burnCallCursor.enterCall hcode
    have hbody : body = flashBurn := by
      simpa [weth10, weth10Aux, flashBurnSlot] using hget.symm
    subst body
    exact burnCursor.finishFlashBurn

/-- The successful decoder and repayment suffix after the borrower callback
crosses no further recursive child. -/
private theorem Exec.Frame.CountedCursor.finishFlashLoanAfterCallback
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {final : Devm}
    (cursor : frame.CountedCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      flashLoanAfterCallback final)
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp)) :
    Exec.attributionInner dp ca frame.run = [] := by
  unfold flashLoanAfterCallback at cursor
  rcases cursor.selectNextChildless (by simp [NinstIsChildless]) with
    ⟨callbackBranchCursor, _hiszero⟩
  have hbubble : ∀ pre, ¬ Func.Run ((weth10 dp).main :: weth10Aux)
      frame.sevm pre (.call bubbleRevertSlot) final := by
    intro pre run
    rcases of_run_call run with ⟨body, bodyPre, hbody, _hburn, hrun⟩
    have hlookup : ((weth10 dp).main :: weth10Aux)[bubbleRevertSlot]? =
        some bubbleRevert := by
      simp [weth10, weth10Aux, bubbleRevertSlot]
    rw [hlookup] at hbody
    have heq : body = bubbleRevert := Option.some.inj hbody.symm
    subst body
    exact not_run_bubbleRevert hrun
  rcases callbackBranchCursor.selectBranchLeftWithBurn hbubble with
    ⟨decodeCursor, -⟩
  rcases decodeCursor.peelChildlessLine (line := retdataShorterThan 32)
      (by simp [retdataShorterThan, NinstIsChildless, Ninst.pushB256]) with
    ⟨lengthBranchCursor, _hlength⟩
  rcases lengthBranchCursor.selectBranchLeftWithBurn
      (fun _ => not_run_rev) with
    ⟨magicCursor, -⟩
  rcases magicCursor.peelChildlessLine
      (line := checkRetdataHead CALLBACK_SUCCESS 0 ++ [Ninst.iszero]) (by
        simp [checkRetdataHead, pushList, NinstIsChildless,
          Ninst.pushB256]) with
    ⟨magicBranchCursor, _hmagicLine⟩
  rcases magicBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revWith (flashFailedError_lookup dp)) with
    ⟨settlePrefixCursor, -⟩
  rcases settlePrefixCursor.peelChildlessLine
      (line := [Ninst.pop, Ninst.pop]) (by simp [NinstIsChildless]) with
    ⟨settleCallCursor, _hpops⟩
  obtain ⟨body, hget, ⟨settleCursor⟩⟩ := settleCallCursor.enterCall hcode
  have hbody : body = flashSettle := by
    simpa [weth10, weth10Aux, flashSettleSlot] using hget.symm
  subst body
  exact settleCursor.finishFlashSettle hcode

/-! ## Identifying the counted label of the callback `CALL`

`Weth10AllowanceArmsRedeem` keeps its step-level crossing facts private, so
this module re-declares the ones it needs.  Unlike the redemption arms, the
flash arm cannot assume up front that the callback settled: the label
identification is therefore proved for both settlement outcomes. -/

/-- The first instruction of a compiled `.next` block is installed at the
block's starting program counter. -/
private theorem ninstAt_of_subcode_next_flash
    {code : ByteArray} {sourceTable : List (Nat × Func)} {pc : Nat}
    {n : Ninst} {tail : Func}
    (sub : subcode code.toList pc
      (Func.compile sourceTable pc (.next n tail))) :
    Ninst.At code pc n := by
  rcases of_subcode sub with ⟨compiled, compiledEq, slice⟩
  rcases of_bind_eq_some compiledEq with ⟨rest, restEq, headEq⟩
  simp [pure] at headEq
  rw [← headEq] at slice
  exact Ninst.at_of_slice (List.slice_prefix slice)

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

private theorem genericCall_step_spawn_exact_flash
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
        disablePrecompiles) := by
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hspawn
  repeat' split at hspawn
  all_goals
    simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hspawn
  all_goals obtain ⟨rfl, rfl⟩ := hspawn
  all_goals exact rfl

private theorem Xinst.step_call_spawn_ofCall_flash
    {sevm : Sevm} {devm : Devm} {frame : Frame} {resume : Resume}
    (hspawn : Xinst.step sevm devm .call = .spawn frame resume) :
    ∃ msg, frame = Frame.ofCall msg := by
  simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hspawn
  repeat' split at hspawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hspawn
  all_goals first
    | cases hspawn
    | exact ⟨_, genericCall_step_spawn_exact_flash hspawn⟩

private theorem Ninst.step_call_spawn_ofCall_flash
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {frame : Frame} {resume : Resume}
    (hspawn : Ninst.step ⟨pc, sevm, pre⟩ Ninst.call =
      .spawn frame resume pc') :
    ∃ msg, frame = Frame.ofCall msg := by
  have hx : Xinst.step sevm pre .call = .spawn frame resume := by
    exact XStep.toStep_spawn (by
      simpa only [Ninst.call, Ninst.step_exec] using hspawn)
  exact Xinst.step_call_spawn_ofCall_flash hx

private theorem Frame.settlementCommits_ofCall_of_raw_commits_flash
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

/-- The counted label selected by an exact source `CALL` edge is precisely
the attribution stream of its retained raw child.  For a `CALL` frame raw
commitment and settlement commitment coincide, so no separate commitment
hypothesis is needed. -/
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
          rcases Ninst.step_call_spawn_ofCall_flash hs with ⟨msg, rfl⟩
          by_cases hraw : Execution.commits raw = true
          · have hcommit : Blanc.Weth10.Frame.settlementCommits
                (Frame.ofCall msg) raw = true :=
              Frame.settlementCommits_ofCall_of_raw_commits_flash hraw
            simp [hcommit, RetainedXlot.attributionStream,
              Exec.attributionStream, hraw]
          · have hnot : ¬ Blanc.Weth10.Frame.settlementCommits
                (Frame.ofCall msg) raw = true := fun h =>
              hraw (Blanc.Weth10.Frame.raw_commits_of_settlementCommits h)
            simp [RetainedXlot.attributionStream,
              Exec.attributionStream, hnot, hraw]

/-! ## The counted skeleton of a flash frame -/

/-- Cross the borrower callback `CALL` from a counted cursor at the
successful callback suffix.  The counted prefix reaching that cursor is
exactly empty and the post-callback decoder, settlement and burn
continuation cross no recursive child, so the frame's entire
proper-descendant counted stream is the retained callback child's
attribution stream. -/
private theorem Exec.Frame.CountedCursor.crossFlashCallback
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (callCursor : frame.CountedCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      flashLoanSuccessTail frame.post)
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp)) :
    ∃ (callPost : Devm) (pc : Nat) (xl : Xlot) (retained : RetainedXlot xl),
      Ninst.At frame.sevm.code pc Ninst.call ∧
      Xlot.Filled xl ∧
      Ninst.StepRun pc frame.sevm callCursor.pre Ninst.call xl
        (.ok callPost) ∧
      Exec.attributionInner dp ca frame.run =
        retained.attributionStream dp ca := by
  have hsub : subcode frame.sevm.code.toList callCursor.pc
      (Func.compile (table 0 ((weth10 dp).main :: weth10Aux)) callCursor.pc
        (Ninst.call ::: flashLoanAfterCallback)) := callCursor.codeSlice
  have hrunShape : Func.RunCompiled ((weth10 dp).main :: weth10Aux)
      frame.sevm callCursor.pre (Ninst.call ::: flashLoanAfterCallback)
      frame.post := callCursor.run
  rcases frame with ⟨fpc, e, fpre, fout, frun, fcommitted⟩
  cases fout with
  | error err => simp [Execution.commits] at fcommitted
  | ok fpost =>
      cases hrunShape with
      | next hcompiled htailCompiled =>
          rename_i midD
          have hat : Ninst.At e.code callCursor.pc Ninst.call :=
            ninstAt_of_subcode_next_flash hsub
          obtain ⟨nextBoundary, nextSub⟩ :=
            Func.noPushBefore_next hsub callCursor.codeBoundary
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
          obtain ⟨retained⟩ := exists_retainedXlot_of_filled ofilled
          have htailNil : Exec.attributionInner dp ca continuation = [] := by
            let tailFrame : Exec.Frame :=
              ⟨callCursor.pc + Ninst.call.size, e, midD, .ok fpost,
                continuation, fcommitted⟩
            let tailCursor :
                Exec.Frame.CountedCursor dp ca tailFrame
                  ((weth10 dp).main :: weth10Aux)
                  (table 0 ((weth10 dp).main :: weth10Aux))
                  flashLoanAfterCallback fpost :=
              ⟨callCursor.pc + Ninst.call.size, midD, continuation,
                ⟨[], Exec.Deriv.ParentPrefixActions.refl _⟩,
                Exec.Deriv.ParentPrefixCounted.refl _, htailCompiled,
                nextSub, nextBoundary⟩
            exact tailCursor.finishFlashLoanAfterCallback hcode
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
              hat ofilled hstepAt retained hcountedEdge
          refine ⟨midD, callCursor.pc, xl, retained, hat, ofilled,
            hstepAt, ?_⟩
          rw [hprefixSplit, List.nil_append, hedgeSplit, hcountedEq,
            htailNil, List.append_nil]

/-- An authentic committed `flashLoan` frame crosses exactly one recursive
child — the borrower callback — and its entire proper-descendant counted
stream is that child's attribution stream.  This is the bridge from the
action-labelled flash chronology to the counted ledger. -/
theorem Exec.Frame.attributionInner_eq_callback_of_flashLoan
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = flashLoanSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    ∃ (callPre callPost : Devm) (pc : Nat) (xl : Xlot)
        (retained : RetainedXlot xl),
      Ninst.At frame.sevm.code pc Ninst.call ∧
      Xlot.Filled xl ∧
      Ninst.StepRun pc frame.sevm callPre Ninst.call xl (.ok callPost) ∧
      Func.Run ((weth10 dp).main :: weth10Aux) frame.sevm callPre
        flashLoanSuccessTail frame.post ∧
      Exec.attributionInner dp ca frame.run =
        retained.attributionStream dp ca := by
  have hmember :
      (Sevm.selector frame.sevm, nonpayable flashLoan) ∈ weth10Funcs dp := by
    rw [hselector]
    simp [flashLoanSelector, weth10Funcs]
  have hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp) :=
    context.invocation.2.2.2
  rcases frame.compiledSelectorBodyCursorCounted context hnonempty hmember
    with ⟨wrapperCursor⟩
  rcases wrapperCursor.enterNonpayable with ⟨bodyCursor⟩
  rcases bodyCursor.reachFlashCallback with ⟨callCursor⟩
  obtain ⟨callPost, pc, xl, retained, hat, hfilled, hstep, hinner⟩ :=
    callCursor.crossFlashCallback hcode
  exact ⟨callCursor.pre, callPost, pc, xl, retained, hat, hfilled, hstep,
    Func.Run.of_runCompiled callCursor.run, hinner⟩

/-- The counted skeleton together with the settlement handoff: the borrower
callback is the frame's only recursive child, and the post-callback
settlement phase starts from exactly the storage the callback committed.
Neither the stack image at the callback boundary nor any memory invariant is
needed for this step. -/
theorem Exec.Frame.flashCallbackAndSettlement
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = flashLoanSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    ∃ (callPre callPost settlePre : Devm) (pc : Nat) (xl : Xlot)
        (retained : RetainedXlot xl),
      Ninst.At frame.sevm.code pc Ninst.call ∧
      Xlot.Filled xl ∧
      Ninst.StepRun pc frame.sevm callPre Ninst.call xl (.ok callPost) ∧
      Devm.getStor callPost = Devm.getStor settlePre ∧
      Func.Run ((weth10 dp).main :: weth10Aux) frame.sevm settlePre
        flashSettle frame.post ∧
      Exec.attributionInner dp ca frame.run =
        retained.attributionStream dp ca := by
  obtain ⟨callPre, callPost, pc, xl, retained, hat, hfilled, hstep,
      hcallFunc, hinner⟩ :=
    frame.attributionInner_eq_callback_of_flashLoan context hselector
      hnonempty
  obtain ⟨sf, settlePre, hcall, hsettle, hstor, _hbal⟩ :=
    of_run_flashLoanFromCall dp
      (show Func.Run ((weth10 dp).main :: weth10Aux) frame.sevm callPre
        flashLoanFromCall frame.post from hcallFunc)
  rcases hcall with ⟨xlCall, hfilledCall, pcCall, hstepCall⟩
  have halign := Ninst.StepRun.unique_exec_of_filled hfilled hfilledCall
    hstep hstepCall
  have hpost : callPost = sf := Except.ok.inj halign.2
  subst sf
  exact ⟨callPre, callPost, settlePre, pc, xl, retained, hat, hfilled,
    hstep, hstor, hsettle, hinner⟩

/-! ## The settlement segment

Replaying the frame's own counted record over the post-callback settlement
entry storage is exactly the settlement's effect on the tagged allowance
region. -/

/-- The settlement segment transports the tagged allowance region by exactly
the frame's own counted record: the record's projected key is the runtime
repayment cell, and its reconstructed visit writes precisely the word the
committed post state holds there. -/
theorem flashSettlement_allowanceLedger
    {dp : DeployParams} {e : Sevm} {pre settlePre burnPre post : Devm}
    (hne0 : e.data.length.toB256 ≠ 0)
    (hsel : Sevm.selector e = flashLoanSelector)
    (houtcome : FlashAllowanceOutcome e settlePre burnPre)
    (hburn : Func.Run ((weth10 dp).main :: weth10Aux) e burnPre
      flashBurn post)
    {record : CountedFrame}
    (hrecord : record.allowance = frameAllowanceEvent e pre post)
    {key : B256} (hkey : InRegion .allowance key) :
    (Devm.getStor post e.currentTarget).get key =
      applyAllowanceLedger (Devm.getStor settlePre e.currentTarget)
        [record] key := by
  have hneApprove : flashLoanSelector ≠ approveSelector := by decide +kernel
  have hneApproveCall : flashLoanSelector ≠ approveAndCallSelector := by
    decide +kernel
  have hnePermit : flashLoanSelector ≠ permitSelector := by decide +kernel
  have hneTransferFrom : flashLoanSelector ≠ transferFromSelector := by
    decide +kernel
  have hneWithdrawFrom : flashLoanSelector ≠ withdrawFromSelector := by
    decide +kernel
  have haccept := flashSettlement_reconstruction houtcome hburn
  rw [applyAllowanceLedger_singleton, hrecord]
  by_cases hafter : (Devm.getStor post e.currentTarget).get
      (flashAllowanceRuntimeKey e) = B256.max
  · have hbranch : flashAllowanceBranchFromPost e post =
        .maximum (flashAllowanceRuntimeKey e) := by
      simp [flashAllowanceBranchFromPost, hafter]
    rw [hbranch] at haccept
    obtain ⟨_hkeyEq, hsettleMax⟩ := haccept.2
    have hevent : frameAllowanceEvent e pre post =
        some { owner := normalizedAddressArg e 0
               spender := e.currentTarget.toB256
               caller := e.caller
               depth := e.depth
               visit := .flashMax } := by
      simp [frameAllowanceEvent, hne0, hsel, hneApprove, hneApproveCall,
        hnePermit, hneTransferFrom, hneWithdrawFrom, hafter]
    rw [hevent]
    simp only [AllowanceVisit.written?, ite_self]
    by_cases hkeyEq : flashAllowanceRuntimeKey e = key
    · rw [← hkeyEq, hafter, hsettleMax]
    · exact flashSettlement_region_locality houtcome hburn hkey hkeyEq
  · have hevent : frameAllowanceEvent e pre post =
        some { owner := normalizedAddressArg e 0
               spender := e.currentTarget.toB256
               caller := e.caller
               depth := e.depth
               visit := .flashFinite
                 ((Devm.getStor post e.currentTarget).get
                   (flashAllowanceRuntimeKey e) + Sevm.argWord e 2)
                 ((Devm.getStor post e.currentTarget).get
                   (flashAllowanceRuntimeKey e)) } := by
      simp [frameAllowanceEvent, hne0, hsel, hneApprove, hneApproveCall,
        hnePermit, hneTransferFrom, hneWithdrawFrom, hafter]
    rw [hevent]
    simp only [AllowanceEvent.key, AllowanceVisit.written?]
    by_cases hkeyEq :
        projectedAllowanceKey (normalizedAddressArg e 0)
          e.currentTarget.toB256 = key
    · rw [if_pos hkeyEq, ← hkeyEq, ← flashAllowanceRuntimeKey_eq_projected]
    · rw [if_neg hkeyEq]
      refine flashSettlement_region_locality houtcome hburn hkey ?_
      rw [flashAllowanceRuntimeKey_eq_projected]
      exact hkeyEq

/-- Carrier-level form of the settlement segment: the post-callback
settlement together with the shared burn continuation transports the tagged
allowance region by the single-record ledger of the frame's own counted
contribution.  The installed-code witness is the settlement chronology's own
`getCode` equality, which the burn continuation already carries. -/
theorem flashSettlement_allowanceRegionEffect
    {dp : DeployParams} {ca : Adr} {e : Sevm}
    {pre settlePre burnPre post : Devm}
    (htarget : e.currentTarget = ca)
    (hne0 : e.data.length.toB256 ≠ 0)
    (hsel : Sevm.selector e = flashLoanSelector)
    (houtcome : FlashAllowanceOutcome e settlePre burnPre)
    (hburn : Func.Run ((weth10 dp).main :: weth10Aux) e burnPre
      flashBurn post)
    (hcode : Devm.getCode settlePre = Devm.getCode post)
    {record : CountedFrame}
    (hrecord : record.allowance = frameAllowanceEvent e pre post) :
    AllowanceRegionEffect ca settlePre post [record] := by
  subst htarget
  exact ⟨fun key hkey =>
    flashSettlement_allowanceLedger hne0 hsel houtcome hburn hrecord hkey,
    congrFun hcode e.currentTarget⟩

/-! ## The borrower subtree segment -/

/-- The parent instruction step retained by a raw flash callback boundary. -/
private theorem RawFlashCallbackStepBoundary.exists_step
    {sevm : Sevm} {self receiver : Adr} {amount inputSize : B256}
    {callbackInput : Bytes} {pre mid : Devm}
    (h : RawFlashCallbackStepBoundary sevm self receiver amount inputSize
      callbackInput pre mid) :
    ∃ (xl : Xlot) (pc : Nat), Xlot.Filled xl ∧
      Ninst.StepRun pc sevm pre Ninst.call xl (.ok mid) := by
  rcases h with
    ⟨_parent, _child, xl, _delegated, _code, _gasWord, _avail, pc, hstep,
      _hdepth, _hstack, _hpref, _hparentState, _hparentMemory,
      _hparentLogs, _hparentOutput, _hdelegation, hfilled, _hprocess,
      _hclean, _hlength, _hmagic, _hresume, _hmidState, _hreturnData,
      _hmidStack, _hmidLogs, _hmidOutput⟩
  exact ⟨xl, pc, hfilled, hstep⟩

/-- The borrower callback transports the tagged allowance region by exactly
its own retained attribution stream, and its resume writes no storage. -/
private theorem RawFlashCallbackStepBoundary.allowanceRegionEffect
    {dp : DeployParams} {ca : Adr} {sevm : Sevm} {receiver : Adr}
    {amount inputSize : B256} {callbackInput : Bytes} {pre mid : Devm}
    {xl : Xlot} {pc : Nat}
    (boundary : RawFlashCallbackStepBoundary sevm sevm.currentTarget
      receiver amount inputSize callbackInput pre mid)
    (retained : RetainedXlot xl)
    (hfilled : Xlot.Filled xl)
    (hstep : Ninst.StepRun pc sevm pre Ninst.call xl (.ok mid))
    (installed : some (pre.getCode ca).toList = Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt sevm.depth ca (weth10 dp)
      (fun p s d out _ => Exec.CoreAllowanceSound dp ca p s d out)) :
    AllowanceRegionEffect ca pre mid
      (retained.attributionStream dp ca) := by
  rcases boundary with
    ⟨parent, child, xlRaw, delegated, code, gasWord, avail, pcRaw, hrawStep,
      hdepth, _hstack, _hpref, hparentState, _hparentMemory, _hparentLogs,
      _hparentOutput, hdelegation, hrawFilled, hprocess, _hclean, _hlength,
      _hmagic, _hresume, hmidState, _hreturnData, _hmidStack, _hmidLogs,
      _hmidOutput⟩
  have halign := Ninst.StepRun.unique_exec_of_filled hfilled hrawFilled
    hstep hrawStep
  cases halign.1
  let msg : Msg :=
    callMsg sevm parent (min gasWord.toNat (except64th avail)) 0
      sevm.currentTarget receiver receiver true false callbackInput code
      delegated
  have hparent : pre.state = msg.benv.state := by
    simpa only [msg, callMsg] using hparentState.symm
  have hmsgDepth : msg.depth < sevm.depth := by
    dsimp only [msg, callMsg]
    omega
  have htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp) := by
    intro hct
    have htargetCa : receiver = ca := by
      simpa only [msg, callMsg] using hct
    exact callbackCode_eq_compiled_of_target_eq installed htargetCa
      hdelegation
  have htargetDirect :
      msg.currentTarget = ca → msg.codeAddress = some ca := by
    intro hct
    have htargetCa : receiver = ca := by
      simpa only [msg, callMsg] using hct
    simp only [msg, callMsg, htargetCa]
  have hchild :=
    ProcessMessageTrace.allowanceRegionDelta_of_forallDeeperAt
      (dp := dp) (ca := ca) (depth := sevm.depth) (parent := pre)
      ⟨xl, retained, by simpa only [msg] using hprocess⟩
      hparent hmsgDepth installed htargetCode htargetDirect hdeeper
  have hresumeEffect : AllowanceRegionEffect ca child mid [] :=
    AllowanceRegionEffect.of_getStorCode_eq
      (congrArg (fun state : State => state.getStor ca) hmidState).symm
      (congrArg (fun state : State => state.getCode ca) hmidState).symm
  simpa only [List.append_nil] using hchild.append hresumeEffect

/-! ## The witnessed callback entry

`Weth10HolderFlowFlashChronology` states the effect of the flash body's
childless prefix over the machine states its source lines relate, so the
counted walk consumes exactly the same content the action-labelled walk
does: the callback `CALL` operand stack, the callback memory image, and the
prefix's storage locality away from the minted balance key and the flash
counter. -/

/-- Reach the borrower callback from the public `flashLoan` body with the
callback boundary's stack, memory and prefix-locality witnesses attached,
while preserving the empty counted prefix. -/
private theorem Exec.Frame.CountedCursor.reachFlashCallbackWitnessed
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (cursor : frame.CountedCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) flashLoan frame.post)
    (hwfEntry : Mem.Wf cursor.pre.memory)
    (hreadsEntry : Mem.Reads cursor.pre.memory []) :
    ∃ (gasWord : B256) (callCursor : frame.CountedCursor dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        flashLoanSuccessTail frame.post),
      gasWord :: (normalizedAddressArg frame.sevm 0).toAdr.toB256 ::
        (0 : B256) :: callbackArgsOffset ::
        flashCallbackRuntimeSize frame.sevm :: (0 : B256) ::
        (0 : B256) ::
        [Sevm.argWord frame.sevm 2,
          (normalizedAddressArg frame.sevm 0).toAdr.toB256] <<+
        callCursor.pre.stack ∧
      Mem.Wf callCursor.pre.memory ∧
      Mem.Reads callCursor.pre.memory
        (flashCallbackRuntimeImage frame.sevm []) ∧
      Devm.getCode cursor.pre = Devm.getCode callCursor.pre ∧
      ∀ k : B256, ¬ ValidAdr k → k ≠ flashMintedSlot →
        (Devm.getStor callCursor.pre frame.sevm.currentTarget).get k =
          (Devm.getStor cursor.pre frame.sevm.currentTarget).get k := by
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    flashLoanBodyShape frame.post at cursor
  unfold flashLoanBodyShape at cursor
  rcases cursor.peelChildlessLine (line := flashTokenLine) (by
      simp [flashTokenLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨tokenBranchCursor, htoken⟩
  rcases tokenBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revWith (flashTokenError_lookup dp)) with
    ⟨amountCursor, htokenPop⟩
  unfold flashLoanPostAmount at amountCursor
  rcases amountCursor.peelChildlessLine (line := flashAmountLine) (by
      simp [flashAmountLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨amountBranchCursor, hamount⟩
  rcases amountBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revWith (individualLimitError_lookup dp)) with
    ⟨counterCursor, hamountPop⟩
  unfold flashLoanPostCounter at counterCursor
  rcases counterCursor.peelChildlessLine (line := flashCounterLine) (by
      simp [flashCounterLine, pushFlashMintedSlot, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨totalCursor, hcounter⟩
  rcases totalCursor.peelChildlessLine (line := flashTotalLine) (by
      simp [flashTotalLine, pushFlashMintedSlot, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨totalBranchCursor, htotal⟩
  rcases totalBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revWith (totalLimitError_lookup dp)) with
    ⟨popCursor, htotalPop⟩
  unfold flashLoanPostTotal at popCursor
  rcases popCursor.peelChildlessLine (line := [Ninst.pop])
      (by simp [NinstIsChildless]) with
    ⟨mintCursor, hpop⟩
  rcases mintCursor.peelChildlessLine (line := flashMintLine) (by
      simp [flashMintLine, addressArg, normalizeAddress, pushAddressMask,
        arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨eventCursor, hmint⟩
  rcases eventCursor.peelChildlessLine (line := flashEventCheckLine) (by
      simp [flashEventCheckLine, mstoreAt, logWith, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨codeBranchCursor, hevent⟩
  rcases codeBranchCursor.selectBranchLeftWithBurn
      (fun _ => not_run_rev) with
    ⟨setupCursor, hcodePop⟩
  unfold flashLoanPostCode at setupCursor
  rcases setupCursor.peelChildlessLine (line := flashCallbackSetupLine)
      (by
        simp [flashCallbackSetupLine, storeFlashCallbackHead, mstoreAt,
          pushList, forwardArgTail, arg, cdl, flashCallbackArgsSize,
          NinstIsChildless, Ninst.pushB256]) with
    ⟨callCursor, hsetup⟩
  obtain ⟨gasWord, hstack, hwfCall, hreadsCall, _hcredit, _hbal, hcodeEq,
      hlocal⟩ :=
    flashLoanCallbackPrefix_effect hwfEntry hreadsEntry htoken htokenPop
      hamount hamountPop hcounter htotal htotalPop hpop hmint hevent
      hcodePop hsetup
  exact ⟨gasWord, callCursor, hstack, hwfCall, hreadsCall, hcodeEq, hlocal⟩

/-! ## The flash-loan arm

The pre-callback prefix moves no tagged allowance key, the borrower subtree
moves the region by exactly its own attribution stream, and the settlement
together with its shared burn continuation moves it by the frame's single
own record.  `flashLoan` is the one dispatched selector whose counted
contribution is `inner ++ [own]`, so those segments compose in that order. -/

/-- `flashLoan` transports the allowance region.  Its committed prefix mints
at one normalized address-shaped balance key and bumps the flash counter, so
every tagged allowance key still holds its entry value when the borrower
callback starts; the callback's subtree carries the whole descendant ledger;
and the post-callback settlement replays the frame's own record, which
follows that subtree precisely because the runtime settles the repayment
allowance only once the borrower has returned. -/
theorem Exec.Frame.allowanceRegionEffect_of_flashLoan
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = flashLoanSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ => Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmember :
      (Sevm.selector frame.sevm, nonpayable flashLoan) ∈ weth10Funcs dp := by
    rw [hselector]
    simp [flashLoanSelector, weth10Funcs]
  have hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp) :=
    context.invocation.2.2.2
  have htarget : frame.sevm.currentTarget = ca := context.invocation.2.1
  -- reach the borrower callback with all four witnesses
  rcases frame.compiledSelectorBodyCursorCountedSilent context hnonempty
      hmember with ⟨wrapperCursor, hwrapperSilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨bodyCursor, hbodySilent⟩
  have hentrySilent : Devm.DispatchSilent frame.pre bodyCursor.pre :=
    hwrapperSilent.trans hbodySilent
  have hwfBody : Mem.Wf bodyCursor.pre.memory := by
    rw [← hentrySilent.memory]
    exact context.memory_wf
  have hreadsBody : Mem.Reads bodyCursor.pre.memory [] := by
    rw [← hentrySilent.memory]
    exact context.memory_reads_empty
  obtain ⟨_gasWord, callCursor, hstack, hwfCall, hreadsCall, hcodePrefix,
      hlocalPrefix⟩ :=
    bodyCursor.reachFlashCallbackWitnessed hwfBody hreadsBody
  have hcallRun : Func.Run ((weth10 dp).main :: weth10Aux) frame.sevm
      callCursor.pre flashLoanSuccessTail frame.post :=
    Func.Run.of_runCompiled callCursor.run
  obtain ⟨callPost, settlePre, hboundary, hstorSettle, _hbalSettle,
      hcodeSettle, _hlogsSettle, _houtputSettle, hwfSettle,
      hreadsSettleEx, hsettle⟩ :=
    of_rawFlashLoanSuccessTail_step dp hstack hwfCall hreadsCall rfl
      hcallRun
  -- the counted crossing at the same callback cursor
  obtain ⟨callPost', pcCross, xl, retained, _hat, hfilled, hstep, hinner⟩ :=
    callCursor.crossFlashCallback hcode
  obtain ⟨xlRaw, pcRaw, hrawFilled, hrawStep⟩ := hboundary.exists_step
  have halign := Ninst.StepRun.unique_exec_of_filled hfilled hrawFilled
    hstep hrawStep
  have hpostEq : callPost = callPost' := (Except.ok.inj halign.2).symm
  subst hpostEq
  -- entry-observation transport of the dispatch prefix
  have hentryStor : Devm.getStor frame.pre = Devm.getStor bodyCursor.pre :=
    funext (getStor_eq_of_state_eq hentrySilent.state)
  have hentryCode : Devm.getCode frame.pre = Devm.getCode bodyCursor.pre :=
    funext (getCode_eq_of_state_eq hentrySilent.state)
  have hcodeCall : Devm.getCode frame.pre ca =
      Devm.getCode callCursor.pre ca :=
    (congrFun hentryCode ca).trans (congrFun hcodePrefix ca)
  have hcallCodeAt : some (callCursor.pre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← hcodeCall]
    exact context.installed.1
  have hprefixEffect :
      AllowanceRegionEffect ca frame.pre callCursor.pre [] := by
    refine ⟨fun key hkey => ?_, hcodeCall⟩
    rw [applyAllowanceLedger_nil]
    have hlocal := hlocalPrefix key (allowanceRegion_not_valid hkey)
      (allowanceRegion_ne_flashSlot hkey)
    rw [htarget] at hlocal
    rw [hlocal, ← congrFun hentryStor ca]
  -- the borrower subtree and the settlement handoff
  have hchildEffect :
      AllowanceRegionEffect ca callCursor.pre callPost
        (retained.attributionStream dp ca) :=
    hboundary.allowanceRegionEffect retained hfilled hstep hcallCodeAt
      hdeeper
  have hhandoff : AllowanceRegionEffect ca callPost settlePre [] :=
    AllowanceRegionEffect.of_getStorCode_eq (congrFun hstorSettle ca)
      (congrFun hcodeSettle ca)
  have hsegmentInner :
      AllowanceRegionEffect ca frame.pre settlePre
        (Exec.attributionInner dp ca frame.run) := by
    rw [hinner]
    simpa only [List.nil_append, List.append_nil] using
      hprefixEffect.append (hchildEffect.append hhandoff)
  -- the settlement segment carries the frame's own record
  obtain ⟨settleImg, hreadsSettle⟩ := hreadsSettleEx
  obtain ⟨burnPre, hburn, houtcome, hwfBurn, burnImg, hreadsBurn⟩ :=
    of_flashSettle_allowance dp hwfSettle hreadsSettle hsettle
  obtain ⟨_hdecrease, _hcover, _hflashSlot, _hburnLogs, _htrue, _hbalBurn,
      hcodeBurn⟩ :=
    flashBurn_effect dp hwfBurn hreadsBurn hburn
  have hcodeSettlePost : Devm.getCode settlePre = Devm.getCode frame.post :=
    houtcome.2.2.2.symm.trans hcodeBurn.symm
  have hown : (CountedFrame.ofFrame dp ca frame).allowance =
      frameAllowanceEvent frame.sevm frame.pre frame.post := rfl
  have hsegmentOwn :
      AllowanceRegionEffect ca settlePre frame.post
        [CountedFrame.ofFrame dp ca frame] :=
    flashSettlement_allowanceRegionEffect htarget hnonempty hselector
      houtcome hburn hcodeSettlePost hown
  -- the frame's own record follows its borrower subtree
  have hflash : isFlashInvocation frame.sevm = true := by
    simp [isFlashInvocation, hselector, hnonempty]
  have hframeEq : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      Exec.attributionInner dp ca frame.run ++
        [CountedFrame.ofFrame dp ca frame] := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframeEq,
      Exec.frameContribution_eq_append dp ca frame _ context.invocation
        hflash]
  rw [hstream]
  exact hsegmentInner.append hsegmentOwn

end Weth10

end Blanc
