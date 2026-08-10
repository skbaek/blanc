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

/-! ## Counted crossings

`Weth10AttributionChronology` exposes only the flag-directed branch
selections, and keeps no counted analogue of the compiled cursor's internal
source-call crossing.  The flash body needs one reverter-excluding arm
selection, one genuinely two-armed selection, and the internal jump into the
shared settlement and burn bodies, so this module rebuilds those three. -/

/-- A source-level internal jump cannot return when its selected auxiliary
body cannot return. -/
private theorem Func.not_run_call_of
    {fs : List Func} {sevm : Sevm} {slot : Nat} {body : Func}
    (hget : fs[slot]? = some body)
    (hbody : ∀ {pre post}, ¬ Func.Run fs sevm pre body post) :
    ∀ {pre post}, ¬ Func.Run fs sevm pre (.call slot) post := by
  intro pre post run
  cases run with
  | call selected _ bodyRun =>
      rw [hget] at selected
      cases Option.some.inj selected.symm
      exact hbody bodyRun

/-- Select the fall-through arm of a compiled branch when the jumped arm
cannot return, preserving the empty counted prefix. -/
private theorem Exec.Frame.CountedCursor.selectBranchLeftWithBurn
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm}
    (cursor : frame.CountedCursor dp ca fs table
      (.branch left right) final)
    (hnoRight : ∀ pre, ¬ Func.Run fs frame.sevm pre right final) :
    Nonempty (frame.CountedCursor dp ca fs table left final) := by
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
        hsubLeft, hboundLeft⟩⟩
  | succ _hne _hroom _hpop hright =>
      exact absurd (Func.Run.of_runCompiled hright) (hnoRight _)

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

`Weth10HolderFlowFlashChronology` keeps its decomposition of the flash body,
its post-callback decoder, the settlement and the burn continuation private,
so this module re-declares them byte for byte. -/

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

private def flashBurnGuardLine : Line :=
  loadArgBalanceAmount 0 2 ++ balanceTooSmall

private def flashBurnSuccessLine : Line :=
  debitLoadedBalance ++
    addressArg 0 ++ arg 2 ++ [Ninst.pushB256 0] ++ emitTransfer ++
    [Ninst.pop, Ninst.pop] ++
    pushFlashMintedSlot ++ [Ninst.sload] ++ arg 2 ++
    [Ninst.swap 0, Ninst.sub] ++ pushFlashMintedSlot ++ [Ninst.sstore] ++
    [Ninst.pushB256 1] ++ mstoreAt 0 ++ pushList [32, 0]

private theorem flashBurn_shape :
    flashBurn = flashBurnGuardLine +++
      ((.call burnBalanceErrorSlot) <?>
        (flashBurnSuccessLine +++ Func.ret)) := by
  rfl

private def flashSettleKeyLine : Line :=
  addressArg 0 ++ mstoreAt 0 ++ [Ninst.address] ++ mstoreAt 1 ++
    allowanceKeyFromMemory ++ [Ninst.dup 0, Ninst.sload, Ninst.dup 0] ++
    isMax

private def flashSettleGuardLine : Line :=
  arg 2 ++ [Ninst.swap 0] ++ balanceTooSmall

private def flashSettleFiniteLine : Line :=
  [Ninst.sub, Ninst.dup 0, Ninst.swap 1, Ninst.sstore] ++
    emitFlashApproval

private theorem flashSettle_shape :
    flashSettle = flashSettleKeyLine +++
      (([Ninst.pop, Ninst.pop] +++ .call flashBurnSlot) <?>
        (flashSettleGuardLine +++
          ((.call allowanceErrorSlot) <?>
            (flashSettleFiniteLine +++ .call flashBurnSlot)))) := by
  rfl

private def flashLoanAfterCallback : Func :=
  Ninst.iszero :::
    (.call bubbleRevertSlot) <?>
    (retdataShorterThan 32 +++
      Func.rev <?>
      (checkRetdataHead CALLBACK_SUCCESS 0 +++ Ninst.iszero :::
        (.call flashFailedErrorSlot) <?>
        ([Ninst.pop, Ninst.pop] +++ .call flashSettleSlot)))

private theorem flashLoanSuccessTail_shape :
    flashLoanSuccessTail = Ninst.call ::: flashLoanAfterCallback := by
  rfl

private def flashTokenLine : Line :=
  arg 1 ++ [Ninst.address, Ninst.eq, Ninst.iszero]

private def flashAmountLine : Line :=
  arg 2 ++ [Ninst.dup 0, Ninst.pushB256 maxUint112, Ninst.lt]

private def flashCounterLine : Line :=
  pushFlashMintedSlot ++ [Ninst.sload, Ninst.dup 1, Ninst.add] ++
    pushFlashMintedSlot ++ [Ninst.sstore]

private def flashTotalLine : Line :=
  pushFlashMintedSlot ++
    [Ninst.sload, Ninst.dup 0, Ninst.pushB256 maxUint112, Ninst.lt]

private def flashMintLine : Line :=
  addressArg 0 ++
    [Ninst.dup 0, Ninst.sload, Ninst.dup 2, Ninst.add,
      Ninst.dup 1, Ninst.sstore, Ninst.swap 0]

private def flashEventCheckLine : Line :=
  [Ninst.dup 0] ++ mstoreAt 0 ++
    [Ninst.dup 1, Ninst.pushB256 0, Ninst.pushB256 Blanc.transferEvent] ++
    logWith 2 0 1 ++ [Ninst.dup 1, Ninst.extcodesize, Ninst.iszero]

private def flashCallbackSetupLine : Line :=
  [Ninst.dup 0] ++ storeFlashCallbackHead ++ pushList [0, 0] ++
    forwardArgTail 3 6 ++ flashCallbackArgsSize ++
    [Ninst.pushB256 callbackArgsOffset, Ninst.pushB256 0,
      Ninst.dup 6, Ninst.gas]

private def flashLoanPostCode : Func :=
  flashCallbackSetupLine +++ flashLoanSuccessTail

private def flashLoanPostTotal : Func :=
  [Ninst.pop] +++ flashMintLine +++ flashEventCheckLine +++
    (Func.rev <?> flashLoanPostCode)

private def flashLoanPostCounter : Func :=
  flashCounterLine +++ flashTotalLine +++
    ((.call totalLimitErrorSlot) <?> flashLoanPostTotal)

private def flashLoanPostAmount : Func :=
  flashAmountLine +++
    ((.call individualLimitErrorSlot) <?> flashLoanPostCounter)

private def flashLoanBodyShape : Func :=
  flashTokenLine +++
    ((.call flashTokenErrorSlot) <?> flashLoanPostAmount)

private theorem flashLoan_shape : flashLoan = flashLoanBodyShape := by
  rfl

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
    ⟨amountCursor⟩
  unfold flashLoanPostAmount at amountCursor
  rcases amountCursor.peelChildlessLine (line := flashAmountLine) (by
      simp [flashAmountLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨amountBranchCursor, _hamount⟩
  rcases amountBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revWith (individualLimitError_lookup dp)) with
    ⟨counterCursor⟩
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
    ⟨popCursor⟩
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
    ⟨setupCursor⟩
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
    ⟨successCursor⟩
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
      ⟨successCursor⟩
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
    ⟨decodeCursor⟩
  rcases decodeCursor.peelChildlessLine (line := retdataShorterThan 32)
      (by simp [retdataShorterThan, NinstIsChildless, Ninst.pushB256]) with
    ⟨lengthBranchCursor, _hlength⟩
  rcases lengthBranchCursor.selectBranchLeftWithBurn
      (fun _ => not_run_rev) with
    ⟨magicCursor⟩
  rcases magicCursor.peelChildlessLine
      (line := checkRetdataHead CALLBACK_SUCCESS 0 ++ [Ninst.iszero]) (by
        simp [checkRetdataHead, pushList, NinstIsChildless,
          Ninst.pushB256]) with
    ⟨magicBranchCursor, _hmagicLine⟩
  rcases magicBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revWith (flashFailedError_lookup dp)) with
    ⟨settlePrefixCursor⟩
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
  rw [flashLoanSuccessTail_shape] at callCursor
  have hcallFunc : Func.Run ((weth10 dp).main :: weth10Aux) frame.sevm
      callCursor.pre flashLoanSuccessTail frame.post := by
    rw [flashLoanSuccessTail_shape]
    exact Func.Run.of_runCompiled callCursor.run
  rcases frame with ⟨fpc, e, fpre, fout, frun, fcommitted⟩
  cases fout with
  | error err => simp [Execution.commits] at fcommitted
  | ok fpost =>
      cases hcallRun : callCursor.run with
      | next hcompiled htailCompiled =>
          rename_i midD
          have hat : Ninst.At e.code callCursor.pc Ninst.call :=
            ninstAt_of_subcode_next_flash callCursor.codeSlice
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
          refine ⟨callCursor.pre, midD, callCursor.pc, xl, retained,
            hat, ofilled, hstepAt, hcallFunc, ?_⟩
          rw [hprefixSplit, List.nil_append, hedgeSplit, hcountedEq,
            htailNil, List.append_nil]

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

end Weth10

end Blanc
