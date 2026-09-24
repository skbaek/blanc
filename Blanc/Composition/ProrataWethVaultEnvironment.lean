import Blanc.Composition.ProrataWethVaultPair
import Blanc.Composition.ProrataWethVaultRely
import Blanc.MessageExecutionInversion

/-!
# The WETH environment of the PRORATA/WETH vault pair

This module is the pair rung's *environment* half: it says what an arbitrary
successful WETH frame can do to the vault's own WETH row and to the vault's
allowance cells, with no honesty assumption on any callee.

Three layers:

* **Per-selector compiled effects.**  The exported body walks of
  `ProrataWethVaultEffects` are lifted to `Prog.RunCompiled` at the general
  caller, one theorem per dispatched WETH selector, plus the fallback deposit
  path and the `withdraw` pre-call split.
* **`WethFrameClass`.**  A *total* classifier of exact committed WETH frames.
  Unlike `WethAllowanceEvent`, which deliberately retains only the two
  allowance selectors, every successful WETH frame lands in exactly one class.
* **`wethFrame_vaultRow_classified`.**  The unconditional vault-row statement:
  a successful WETH frame whose caller is not the vault either leaves the
  vault's WETH row alone, raises it as a donation from a source that is not the
  vault, performs a runtime-authorized debit that read the raw allowance cell,
  or is a `withdraw` whose value-bearing callback is retained and exposed.
  The fourth arm is what replaces a `reachableExecFree` blanket on WETH: WETH
  is *not* exec-free, and the callback is represented rather than assumed away.

The five former silence `def`s of `ProrataWethVaultRely` are proved here as
theorems and deleted there.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

/-! ## The dispatched WETH selectors -/

/-- The ten selectors inherited WETH dispatches on, read off the contract's own
table rather than restated. -/
def wethSelectors : List B256 := Blanc.wethFuncs.map Prod.fst

/-- The six read-only entries.  `totalSupply` reads the account balance and the
other five read storage or constants; none of them writes. -/
def wethViewSelectors : List B256 :=
  [selector "name" [], selector "totalSupply" [], selector "decimals" [],
    selector "balanceOf" [.address], selector "symbol" [],
    selector "allowance" [.address, .address]]

theorem wethViewSelectors_subset :
    ∀ sel ∈ wethViewSelectors, sel ∈ wethSelectors := by
  decide +kernel

/-! ## The total frame classifier -/

/-- Every successful exact WETH frame is exactly one of six kinds.  The
`withdraw` constructor is the only one whose frame can contain a retained
child; `deposit` is the payable fallback, reached by empty or unmatched
calldata rather than by a selector. -/
inductive WethFrameClass
  | view
  | approve (owner spender wad : B256)
  | deposit (caller : Adr) (value : B256)
  | withdraw (caller : Adr) (wad : B256)
  | transfer (caller : Adr) (dst wad : B256)
  | transferFrom (caller : Adr) (src dst wad : B256)
  deriving DecidableEq

/-- What one class asserts about the frame's own machine.  This is written
independently of `classify?` on purpose: the classifier is a decision
procedure, and a classifier that routed a selector to the wrong constructor
would have to disagree with this predicate. -/
def WethFrameClass.Matches (sevm : Sevm) : WethFrameClass → Prop
  | .view => Sevm.selector sevm ∈ wethViewSelectors
  | .approve owner spender wad =>
      Sevm.selector sevm = selector "approve" [.address, .uint256] ∧
        owner = sevm.caller.toB256 ∧ spender = Sevm.argWord sevm 0 ∧
        wad = Sevm.argWord sevm 1
  | .deposit caller value =>
      (∀ sel ∈ wethSelectors, Sevm.selector sevm ≠ sel) ∧
        caller = sevm.caller ∧ value = sevm.value
  | .withdraw caller wad =>
      Sevm.selector sevm = selector "withdraw" [.uint256] ∧
        caller = sevm.caller ∧ wad = Sevm.argWord sevm 0
  | .transfer caller dst wad =>
      Sevm.selector sevm = selector "transfer" [.address, .uint256] ∧
        caller = sevm.caller ∧ dst = Sevm.argWord sevm 0 ∧
        wad = Sevm.argWord sevm 1
  | .transferFrom caller src dst wad =>
      Sevm.selector sevm = selector "transferFrom" [.address, .address, .uint256] ∧
        caller = sevm.caller ∧ src = Sevm.argWord sevm 0 ∧
        dst = Sevm.argWord sevm 1 ∧ wad = Sevm.argWord sevm 2

/-- The exact frame-root identity plus the class's own machine facts. -/
def WethFrameClass.Classified (frame : Exec.Frame) (cls : WethFrameClass) : Prop :=
  (Blanc.Exec.Frame.exactInvocation Blanc.weth wethAccount wethAccount frame) ∧
    cls.Matches frame.sevm

/-- The total selector-driven classifier.  Only the exact compiled identity is
a precondition; once a frame has it, every selector — including none of the
ten — has a class. -/
def WethFrameClass.classify? (frame : Exec.Frame) : Option WethFrameClass :=
  if (Blanc.Exec.Frame.exactInvocation Blanc.weth wethAccount wethAccount frame) then
    if Sevm.selector frame.sevm = selector "approve" [.address, .uint256] then
      some (.approve frame.sevm.caller.toB256 (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 1))
    else if Sevm.selector frame.sevm =
        selector "transferFrom" [.address, .address, .uint256] then
      some (.transferFrom frame.sevm.caller (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 1) (Sevm.argWord frame.sevm 2))
    else if Sevm.selector frame.sevm = selector "transfer" [.address, .uint256] then
      some (.transfer frame.sevm.caller (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 1))
    else if Sevm.selector frame.sevm = selector "withdraw" [.uint256] then
      some (.withdraw frame.sevm.caller (Sevm.argWord frame.sevm 0))
    else if Sevm.selector frame.sevm ∈ wethViewSelectors then
      some .view
    else
      some (.deposit frame.sevm.caller frame.sevm.value)
  else none

/-! ### Selector bookkeeping

Three decidable facts about the ten dispatched selectors.  They are what make
the classifier exhaustive and mutually exclusive; every later case split cites
one of them rather than restating a selector. -/

theorem wethViewSelectors_not_writer :
    ∀ sel ∈ wethViewSelectors,
      sel ≠ selector "approve" [.address, .uint256] ∧
        sel ≠ selector "transferFrom" [.address, .address, .uint256] ∧
        sel ≠ selector "transfer" [.address, .uint256] ∧
        sel ≠ selector "withdraw" [.uint256] := by
  decide +kernel

theorem mem_wethSelectors_cases :
    ∀ sel ∈ wethSelectors,
      sel ∈ wethViewSelectors ∨
        sel = selector "approve" [.address, .uint256] ∨
        sel = selector "transferFrom" [.address, .address, .uint256] ∨
        sel = selector "transfer" [.address, .uint256] ∨
        sel = selector "withdraw" [.uint256] := by
  decide +kernel

theorem writer_mem_wethSelectors :
    selector "approve" [.address, .uint256] ∈ wethSelectors ∧
      selector "transferFrom" [.address, .address, .uint256] ∈ wethSelectors ∧
      selector "transfer" [.address, .uint256] ∈ wethSelectors ∧
      selector "withdraw" [.uint256] ∈ wethSelectors := by
  decide +kernel

/-- Every class the classifier returns really is the frame's class. -/
theorem WethFrameClass.classification_sound
    {frame : Exec.Frame} {cls : WethFrameClass}
    (classified : WethFrameClass.classify? frame = some cls) :
    WethFrameClass.Classified frame cls := by
  unfold WethFrameClass.classify? at classified
  split at classified
  · rename_i identity
    refine ⟨identity, ?_⟩
    split at classified
    · rename_i approve
      cases classified
      exact ⟨approve, rfl, rfl, rfl⟩
    · rename_i notApprove
      split at classified
      · rename_i transferFrom
        cases classified
        exact ⟨transferFrom, rfl, rfl, rfl, rfl⟩
      · rename_i notTransferFrom
        split at classified
        · rename_i transfer
          cases classified
          exact ⟨transfer, rfl, rfl, rfl⟩
        · rename_i notTransfer
          split at classified
          · rename_i withdraw
            cases classified
            exact ⟨withdraw, rfl, rfl⟩
          · rename_i notWithdraw
            split at classified
            · rename_i view
              cases classified
              exact view
            · rename_i notView
              cases classified
              refine ⟨?_, rfl, rfl⟩
              intro sel member equal
              rcases mem_wethSelectors_cases sel member with
                view | approve | transferFrom | transfer | withdraw
              · exact notView (equal ▸ view)
              · exact notApprove (equal.trans approve)
              · exact notTransferFrom (equal.trans transferFrom)
              · exact notTransfer (equal.trans transfer)
              · exact notWithdraw (equal.trans withdraw)
  · simp at classified

/-- Every classified frame is retained by the classifier at exactly its own
class.  This is where a classifier that routed one selector to another
constructor stops agreeing with `Matches`. -/
theorem WethFrameClass.classification_complete
    {frame : Exec.Frame} {cls : WethFrameClass}
    (classified : WethFrameClass.Classified frame cls) :
    WethFrameClass.classify? frame = some cls := by
  obtain ⟨identity, fit⟩ := classified
  unfold WethFrameClass.classify?
  rw [if_pos identity]
  obtain ⟨approveMem, transferFromMem, transferMem, withdrawMem⟩ :=
    writer_mem_wethSelectors
  cases cls with
  | view =>
      obtain ⟨notApprove, notTransferFrom, notTransfer, notWithdraw⟩ :=
        wethViewSelectors_not_writer _ fit
      rw [if_neg (fun h => notApprove h), if_neg (fun h => notTransferFrom h),
        if_neg (fun h => notTransfer h), if_neg (fun h => notWithdraw h)]
      exact if_pos fit
  | approve owner spender wad =>
      obtain ⟨selected, rfl, rfl, rfl⟩ := fit
      rw [if_pos selected]
  | deposit caller value =>
      obtain ⟨miss, rfl, rfl⟩ := fit
      have notView : Sevm.selector frame.sevm ∉ wethViewSelectors := by
        intro member
        exact miss _ (wethViewSelectors_subset _ member) rfl
      rw [if_neg (miss _ approveMem), if_neg (miss _ transferFromMem),
        if_neg (miss _ transferMem), if_neg (miss _ withdrawMem),
        if_neg notView]
  | withdraw caller wad =>
      obtain ⟨selected, rfl, rfl⟩ := fit
      have notApprove : Sevm.selector frame.sevm ≠
          selector "approve" [.address, .uint256] := by
        rw [selected]; decide +kernel
      have notTransferFrom : Sevm.selector frame.sevm ≠
          selector "transferFrom" [.address, .address, .uint256] := by
        rw [selected]; decide +kernel
      have notTransfer : Sevm.selector frame.sevm ≠
          selector "transfer" [.address, .uint256] := by
        rw [selected]; decide +kernel
      rw [if_neg notApprove, if_neg notTransferFrom, if_neg notTransfer,
        if_pos selected]
  | transfer caller dst wad =>
      obtain ⟨selected, rfl, rfl, rfl⟩ := fit
      have notApprove : Sevm.selector frame.sevm ≠
          selector "approve" [.address, .uint256] := by
        rw [selected]; decide +kernel
      have notTransferFrom : Sevm.selector frame.sevm ≠
          selector "transferFrom" [.address, .address, .uint256] := by
        rw [selected]; decide +kernel
      rw [if_neg notApprove, if_neg notTransferFrom, if_pos selected]
  | transferFrom caller src dst wad =>
      obtain ⟨selected, rfl, rfl, rfl, rfl⟩ := fit
      have notApprove : Sevm.selector frame.sevm ≠
          selector "approve" [.address, .uint256] := by
        rw [selected]; decide +kernel
      rw [if_neg notApprove, if_pos selected]

/-- **Totality.**  Exact compiled WETH identity is the classifier's only
precondition: no successful WETH frame is left unclassified.  This is the one
property `WethAllowanceEvent.classify?` deliberately does not have. -/
theorem WethFrameClass.classification_total
    {frame : Exec.Frame}
    (identity : (Blanc.Exec.Frame.exactInvocation Blanc.weth wethAccount wethAccount frame)) :
    ∃ cls, WethFrameClass.classify? frame = some cls ∧
      WethFrameClass.Classified frame cls := by
  have present : ∃ cls, WethFrameClass.classify? frame = some cls := by
    unfold WethFrameClass.classify?
    rw [if_pos identity]
    repeat' split
    all_goals exact ⟨_, rfl⟩
  obtain ⟨cls, classified⟩ := present
  exact ⟨cls, classified, WethFrameClass.classification_sound classified⟩

/-! ## Per-selector compiled effects at the general caller

`ProrataWethVaultEffects` proves each body's exact effect at `Func.Run`; these
lift them across the dispatcher to an arbitrary caller's `Prog.RunCompiled`,
which is the altitude a frame classifier can consume. -/

/-- The six read-only entries write no storage anywhere. -/
theorem weth_view_compiled_effect {sevm : Sevm} {pre post : Devm}
    (run : Prog.RunCompiled sevm pre Blanc.weth post)
    (selected : Sevm.selector sevm ∈ wethViewSelectors) :
    Devm.getStor pre = Devm.getStor post := by
  have entry : ∀ {body : Func},
      (Sevm.selector sevm, nonpayable body) ∈ Blanc.wethFuncs →
      Func.Inv Devm.getStor Devm.getStor body →
      Devm.getStor pre = Devm.getStor post := by
    intro body member inv
    obtain ⟨bodyPre, -, entryState, -, -, -, bodyRun⟩ :=
      runCompiled_enters_wethNonpayable run rfl member
    exact (funext (getStor_eq_of_state_eq entryState)).trans
      (Func.of_inv Devm.getStor Devm.getStor inv bodyRun)
  simp only [wethViewSelectors, List.mem_cons, List.not_mem_nil, or_false]
    at selected
  rcases selected with sel | sel | sel | sel | sel | sel
  · exact entry (body := Blanc.name) (by rw [sel]; simp [Blanc.wethFuncs])
      (by unfold Blanc.name; func_inv)
  · exact entry (body := Blanc.totalSupply) (by rw [sel]; simp [Blanc.wethFuncs])
      (by unfold Blanc.totalSupply; func_inv)
  · exact entry (body := Blanc.decimals) (by rw [sel]; simp [Blanc.wethFuncs])
      (by unfold Blanc.decimals; func_inv)
  · exact entry (body := Blanc.balanceOf) (by rw [sel]; simp [Blanc.wethFuncs])
      (by unfold Blanc.balanceOf; func_inv)
  · exact entry (body := Blanc.symbol) (by rw [sel]; simp [Blanc.wethFuncs])
      (by unfold Blanc.symbol; func_inv)
  · exact entry (body := Blanc.allowance) (by rw [sel]; simp [Blanc.wethFuncs])
      (by unfold Blanc.allowance; func_inv)

/-- The general-caller `transfer` effect: the debit is from the actual frame
caller, the credit to ABI word zero, nothing else in the target's storage
moves, and no other account's storage moves at all. -/
theorem weth_transfer_compiled_effect {sevm : Sevm} {pre post : Devm}
    (run : Prog.RunCompiled sevm pre Blanc.weth post)
    (selected : Sevm.selector sevm = selector "transfer" [.address, .uint256]) :
    Transfer (Stor.rest (Devm.getStor pre sevm.currentTarget)) sevm.caller
        (Sevm.argWord sevm 1) (Sevm.argWord sevm 0).toAdr
        (Stor.rest (Devm.getStor post sevm.currentTarget)) ∧
      Stor.AgreeOffAdr (Devm.getStor pre sevm.currentTarget)
        (Devm.getStor post sevm.currentTarget) ∧
      (∀ account, sevm.currentTarget ≠ account →
        Devm.getStor post account = Devm.getStor pre account) := by
  obtain ⟨bodyPre, -, entryState, -, -, -, bodyRun⟩ :=
    runCompiled_enters_wethNonpayable (body := Blanc.transfer) run selected
      (by simp [Blanc.wethFuncs])
  obtain ⟨move, off, foreign, -, -⟩ := transferBody_exactEffect bodyRun
  have storage : Devm.getStor pre = Devm.getStor bodyPre :=
    funext (getStor_eq_of_state_eq entryState)
  refine ⟨?_, ?_, ?_⟩
  · rw [congrFun storage sevm.currentTarget]; exact move
  · rw [congrFun storage sevm.currentTarget]; exact off
  · intro account different
    rw [foreign account different, ← congrFun storage account]

/-- The general-caller `transferFrom` balance-row effect.  The allowance half
is `weth_transferFrom_compiled_allowance_effect`; this is the row half, with
the source, destination, and amount the three actual ABI words. -/
theorem weth_transferFrom_compiled_row_effect {sevm : Sevm} {pre post : Devm}
    (run : Prog.RunCompiled sevm pre Blanc.weth post)
    (selected : Sevm.selector sevm =
      selector "transferFrom" [.address, .address, .uint256]) :
    Transfer (Stor.rest (Devm.getStor pre sevm.currentTarget))
        (Sevm.argWord sevm 0).toAdr (Sevm.argWord sevm 2)
        (Sevm.argWord sevm 1).toAdr
        (Stor.rest (Devm.getStor post sevm.currentTarget)) ∧
      (∀ account, sevm.currentTarget ≠ account →
        Devm.getStor post account = Devm.getStor pre account) := by
  obtain ⟨bodyPre, -, entryState, -, -, -, bodyRun⟩ :=
    runCompiled_enters_wethNonpayable (body := Blanc.transferFrom) run selected
      (by simp [Blanc.wethFuncs])
  obtain ⟨move, foreign, -, -, -⟩ := transferFromBody_exactEffect bodyRun
  have storage : Devm.getStor pre = Devm.getStor bodyPre :=
    funext (getStor_eq_of_state_eq entryState)
  refine ⟨?_, ?_⟩
  · rw [congrFun storage sevm.currentTarget]; exact move
  · intro account different
    rw [foreign account different, ← congrFun storage account]

/-! ## The fallback deposit path

WETH's selector miss is an indexed `Func.call 1` into `deposit`, not a revert,
so `sig_mem_of_dispatchWith_ok` (which needs the miss arm to be `Func.revert`)
does not apply.  The miss route is proved here directly, as the exact mirror of
the hit route `reach_of_dispatchWith_logs`. -/

/-- A selector absent from the dispatch tree reaches the indexed fallback, with
the same four frame transports the hit route reports. -/
private theorem run_dispatchWith_miss {fs : List Func} {k : Nat} {fallback : Func}
    (lookup : fs[k]? = some fallback) :
    ∀ (t : DispatchTree) {sevm : Sevm} {s r : Devm} {sig : B256} {tail : Stack},
      (∀ body : Func, (sig, body) ∉ t) →
      (sig :: tail <<+ s.stack) →
      Func.Run fs sevm s (dispatchWith k t) r →
      ∃ s', s.state = s'.state ∧ s.memory = s'.memory ∧ s.logs = s'.logs ∧
        s.output = s'.output ∧ Func.Run fs sevm s' fallback r := by
  intro t
  induction t with
  | leaf w p =>
      intro sevm s r sig tail miss hp
      have different : ¬ (w = sig) := by
        intro same
        exact miss p (by subst same; rfl)
      simp only [dispatchWith]
      func_execute 2
      intro branchRun
      rcases Line.of_run_cons h₁ with ⟨a, push, rest⟩
      rcases Line.of_run_cons rest with ⟨b, eqRun, nil⟩
      cases nil
      have hpa : w :: sig :: tail <<+ a.stack :=
        prefix_of_push (of_run_pushB256 push) hp
      have hpb : (0 : B256) :: tail <<+ s₁.stack := by
        simpa [B256.eqCheck, different] using prefix_of_eq eqRun hpa
      rcases of_run_branch branchRun with
        ⟨s₂, pop, callRun⟩ | ⟨v, s₂, s₃, vne, pop, burn, -⟩
      · cases callRun with
        | call lookupEq callBurn fallbackRun =>
            have same := lookup.symm.trans lookupEq
            injection same with fallbackEq
            subst fallbackEq
            refine ⟨_, ?_, ?_, ?_, ?_, fallbackRun⟩
            · exact ((Line.of_inv Devm.state (by line_inv) h₁).trans
                pop.state).trans callBurn.state
            · exact ((Line.of_inv Devm.memory (by line_inv) h₁).trans
                pop.memory).trans callBurn.memory
            · exact ((Line.of_inv Devm.logs (by line_inv) h₁).trans
                pop.logs).trans callBurn.logs
            · exact ((Line.of_inv Devm.output (by line_inv) h₁).trans
                pop.output).trans callBurn.output
      · exact absurd (popBurn_pref pop hpb).1 vne
  | fork tl tr ihl ihr =>
      intro sevm s r sig tail miss hp
      simp only [dispatchWith]
      func_execute 3
      intro branchRun
      rcases Line.of_run_cons h₁ with ⟨a, dupRun, rest⟩
      rcases Line.of_run_cons rest with ⟨b, push, rest⟩
      rcases Line.of_run_cons rest with ⟨c, gtRun, nil⟩
      cases nil
      have hpa : sig :: sig :: tail <<+ a.stack :=
        prefix_of_dup_val dupRun (Stack.Nth.head _ _) hp
      have hpb : leftmostFsig tr :: sig :: sig :: tail <<+ b.stack :=
        prefix_of_push (of_run_pushB256 push) hpa
      have hpc : (leftmostFsig tr >? sig) :: sig :: tail <<+ s₁.stack :=
        prefix_of_gt gtRun hpb
      rcases of_run_branch branchRun with
        ⟨s₂, pop, rightRun⟩ | ⟨v, s₂, s₃, vne, pop, burn, leftRun⟩
      · obtain ⟨-, hp₂⟩ := popBurn_pref pop hpc
        obtain ⟨s', state, memory, logs, output, fallbackRun⟩ :=
          ihr (fun body member => miss body (Or.inr member)) hp₂ rightRun
        refine ⟨s', ?_, ?_, ?_, ?_, fallbackRun⟩
        · exact ((Line.of_inv Devm.state (by line_inv) h₁).trans pop.state).trans state
        · exact ((Line.of_inv Devm.memory (by line_inv) h₁).trans pop.memory).trans memory
        · exact ((Line.of_inv Devm.logs (by line_inv) h₁).trans pop.logs).trans logs
        · exact ((Line.of_inv Devm.output (by line_inv) h₁).trans pop.output).trans output
      · obtain ⟨-, hp₂⟩ := popBurn_pref pop hpc
        have hp₃ : sig :: tail <<+ s₃.stack := by
          rw [← burn.stack]; exact hp₂
        obtain ⟨s', state, memory, logs, output, fallbackRun⟩ :=
          ihl (fun body member => miss body (Or.inl member)) hp₃ leftRun
        refine ⟨s', ?_, ?_, ?_, ?_, fallbackRun⟩
        · exact (((Line.of_inv Devm.state (by line_inv) h₁).trans pop.state).trans
            burn.state).trans state
        · exact (((Line.of_inv Devm.memory (by line_inv) h₁).trans pop.memory).trans
            burn.memory).trans memory
        · exact (((Line.of_inv Devm.logs (by line_inv) h₁).trans pop.logs).trans
            burn.logs).trans logs
        · exact (((Line.of_inv Devm.output (by line_inv) h₁).trans pop.output).trans
            burn.output).trans output

/-- A successful exact compiled WETH run whose selector is none of the ten
dispatched ones reaches the payable fallback `deposit` body.  Unlike the
recognized-selector route there is no `nonpayable` wrapper, so no `value = 0`
is available or claimed. -/
theorem runCompiled_enters_wethDeposit {sevm : Sevm} {pre post : Devm}
    (run : Prog.RunCompiled sevm pre Blanc.weth post)
    (miss : ∀ sel ∈ wethSelectors, Sevm.selector sevm ≠ sel) :
    ∃ mid,
      pre.state = mid.state ∧
      pre.memory = mid.memory ∧
      pre.logs = mid.logs ∧
      pre.output = mid.output ∧
      Func.Run (Blanc.weth.main :: Blanc.weth.aux) sevm mid Blanc.deposit post := by
  have sourceRun : Prog.Run sevm pre Blanc.weth post :=
    Prog.Run.of_runCompiled run
  dsimp only [Prog.Run] at sourceRun
  cases sourceRun
  rename (_ = _) => rootLookup
  rename (Func.Run _ _ _ _ _) => rootRun
  rename (Devm.Burn _ _) => rootBurn
  rename Devm => rootPre
  cases rootLookup
  have mainRun :
      Func.Run (Blanc.weth.main :: Blanc.weth.aux) sevm rootPre
        (fsig +++ dispatchWith 1 Blanc.wethTree) post := by
    simpa only [Blanc.weth, Func.mainWith] using rootRun
  refine run_prepend_elim _ fsig ?_ mainRun
  intro dispatchPre hfsig hdispatch
  have selectorPrefix : Sevm.selector sevm :: [] <<+ dispatchPre.stack :=
    prefix_of_fsig nil_pref hfsig
  have absent : ∀ body : Func, (Sevm.selector sevm, body) ∉ Blanc.wethTree := by
    intro body member
    have listMember : (Sevm.selector sevm, body) ∈ Blanc.wethFuncs :=
      DispatchTree.mem_of_mem_ofSorted (by decide +kernel) member
    exact miss (Sevm.selector sevm)
      (List.mem_map_of_mem (f := Prod.fst) listMember) rfl
  obtain ⟨depositPre, state, memory, logs, output, depositRun⟩ :=
    run_dispatchWith_miss (fallback := Blanc.deposit) rfl Blanc.wethTree absent
      selectorPrefix hdispatch
  refine ⟨depositPre, ?_, ?_, ?_, ?_, depositRun⟩
  · exact (rootBurn.state.trans
      (Line.of_inv Devm.state (by line_inv) hfsig)).trans state
  · exact (rootBurn.memory.trans
      (Line.of_inv Devm.memory (by line_inv) hfsig)).trans memory
  · exact (rootBurn.logs.trans (fsig_logs hfsig)).trans logs
  · exact (rootBurn.output.trans (fsig_output hfsig)).trans output

/-- Exact storage effect of the inherited WETH `deposit` fallback: the caller's
own balance row is credited by the frame's call value, nothing else in the
target's storage moves, and no other account's storage moves at all. -/
theorem depositBody_effect
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    (run : Func.Run fs sevm s Blanc.deposit r) :
    Devm.getStor r sevm.currentTarget =
        (Devm.getStor s sevm.currentTarget).set sevm.caller.toB256
          (sevm.value +
            Devm.getStorVal s sevm.currentTarget sevm.caller.toB256) ∧
      (∀ account, sevm.currentTarget ≠ account →
        Devm.getStor r account = Devm.getStor s account) := by
  simp only [Blanc.deposit] at run
  rcases of_run_next run with ⟨s1, callerRun, run⟩
  have hp1 : sevm.caller.toB256 :: [] <<+ s1.stack :=
    prefix_of_push (of_run_caller callerRun) nil_pref
  rcases of_run_next run with ⟨s2, sloadRun, run⟩
  obtain ⟨balance, hp2, balanceEq⟩ := prefix_of_sload sloadRun hp1
  rcases of_run_next run with ⟨s3, valueRun, run⟩
  have hp3 : sevm.value :: balance :: [] <<+ s3.stack :=
    prefix_of_push (of_run_callvalue valueRun) hp2
  rcases of_run_next run with ⟨s4, addRun, run⟩
  have hp4 : (sevm.value + balance) :: [] <<+ s4.stack :=
    prefix_of_add addRun hp3
  rcases of_run_next run with ⟨s5, caller2Run, run⟩
  have hp5 : [sevm.caller.toB256, sevm.value + balance] <<+ s5.stack :=
    prefix_of_push (of_run_caller caller2Run) hp4
  rcases of_run_next run with ⟨s6, storeRun, run⟩
  have stored := sstore_getStor_set storeRun hp5
  have prefixRun : Line.Run sevm s
      [Ninst.caller, Ninst.sload, Ninst.callvalue, Ninst.add, Ninst.caller] s5 :=
    Line.Run.cons callerRun (Line.Run.cons sloadRun (Line.Run.cons valueRun
      (Line.Run.cons addRun (Line.Run.cons caller2Run Line.Run.nil))))
  have prefixStorage : Devm.getStor s = Devm.getStor s5 :=
    Line.of_inv Devm.getStor (by line_inv) prefixRun
  have entryStorage : Devm.getStor s = Devm.getStor s1 :=
    Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons callerRun Line.Run.nil)
  have tailStorage : Devm.getStor s6 = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by unfold Blanc.logDeposit; func_inv) run
  have balanceValue :
      balance = Devm.getStorVal s sevm.currentTarget sevm.caller.toB256 := by
    rw [balanceEq]
    change (Devm.getStor s1 _).get _ = (Devm.getStor s _).get _
    rw [entryStorage]
  refine ⟨?_, ?_⟩
  · rw [← congrFun tailStorage sevm.currentTarget, stored,
      ← congrFun prefixStorage sevm.currentTarget, balanceValue]
  · intro account different
    obtain ⟨pc, registerRun⟩ := of_run_reg storeRun
    rw [← congrFun tailStorage account,
      sstore_preserves_getStor_ne registerRun different,
      ← congrFun prefixStorage account]

/-! ## The `withdraw` pre-call split

`withdraw` is the one WETH selector whose frame contains a retained child: the
caller's row is debited, a value-bearing `CALL` is made to the caller, and the
suffix only logs.  WETH is therefore *not* `reachableExecFree`, and no
certificate can exclude that child.  What this split does instead is expose it:
the crossing is handed back as an actual `Ninst.Run`, whose `Xlot.Filled`
carries the child's own derivation, so a consumer recurses into it rather than
assuming anything about the callee. -/

/-- The exact guard walk of `withdraw`, with the withdrawal amount kept as the
actual ABI word rather than an existential stack value. -/
private theorem withdrawLoadCheck_exact {sevm : Sevm} {s s' : Devm}
    (h : Line.Run sevm s Blanc.withdrawLoadCheck s') :
    Devm.getStor s = Devm.getStor s' ∧
      ∃ less,
        ([less, Devm.getStorVal s' sevm.currentTarget sevm.caller.toB256,
            Sevm.argWord sevm 0, Sevm.argWord sevm 0] <<+ s'.stack) ∧
          (less = 0 ↔
            Sevm.argWord sevm 0 ≤
              Devm.getStorVal s' sevm.currentTarget sevm.caller.toB256) := by
  refine ⟨by invariance, ?_⟩
  revert h
  simp only [Blanc.withdrawLoadCheck]
  line_execute_with (arg 0)
  have hp1 : Sevm.argWord sevm 0 :: [] <<+ s₁.stack := prefix_of_arg nil_pref h₁
  clear h₁
  line_execute 2
  have hp2 : [sevm.caller.toB256, Sevm.argWord sevm 0, Sevm.argWord sevm 0] <<+
      s₂.stack := by
    generalize_line_prefix
  clear hp1 h₂
  line_execute 1
  rcases prefix_of_sload (of_run_singleton h₃) hp2 with
    ⟨balance, hp3, hbalance⟩
  have storage23 : Devm.getStor s₂ = Devm.getStor s₃ :=
    Line.of_inv Devm.getStor (by line_inv) h₃
  clear h₃
  intro h₄
  have hp4 : [balance <? Sevm.argWord sevm 0, balance, Sevm.argWord sevm 0,
      Sevm.argWord sevm 0] <<+ s'.stack := by
    generalize_line_prefix
  have storage34 : Devm.getStor s₃ = Devm.getStor s' :=
    Line.of_inv Devm.getStor (by line_inv) h₄
  have balanceEq : balance =
      Devm.getStorVal s' sevm.currentTarget sevm.caller.toB256 := by
    rw [hbalance]
    show (Devm.getStor s₂ _).get _ = (Devm.getStor s' _).get _
    rw [storage23, storage34]
  refine ⟨balance <? Sevm.argWord sevm 0, ?_, ?_⟩
  · rw [← balanceEq]
    exact hp4
  · rw [← balanceEq, B256.ltCheck,
      Ne.ite_eq_right_iff B256.zero_ne_one.symm, B256.not_lt]

/-- `sendToCaller` up to its `CALL`: the seven payout operands are on the
stack, and the four pushes, the swap and the two address words moved no
storage, balance or code. -/
private theorem sendToCaller_callPre {sevm : Sevm} {s sf : Devm} {wad : B256}
    (hp : [wad] <<+ s.stack) :
    Line.Run sevm s Blanc.sendToCaller sf →
    ∃ c : Devm,
      [0, sevm.caller.toB256, wad, 0, 0, 0, 0] <<+ c.stack ∧
        Devm.getStor s = Devm.getStor c ∧ s.getBal = c.getBal ∧
        s.getCode = c.getCode ∧ Ninst.Run sevm c Ninst.call sf := by
  line_execute 7
  have stack : [0, sevm.caller.toB256, wad, 0, 0, 0, 0] <<+ s₁.stack := by
    generalize_line_prefix
  intro callRun
  exact ⟨s₁, stack, Line.of_inv Devm.getStor (by line_inv) h₁,
    Line.of_inv Devm.getBal (by line_inv) h₁,
    Line.of_inv Devm.getCode (by line_inv) h₁, of_run_singleton callRun⟩

/-- **WETH `withdraw` pre-call split, retained at the `CALL`.**  The caller's
row is debited before the value-bearing `CALL` to the caller, nothing else in
WETH's storage moves before it, and the suffix after it writes no storage at
all.  Beyond the storage split, it keeps what a consumer needs to open the
`CALL` itself: the seven payout operands on the stack, balance and code
unchanged since entry, the debited row's solvency against the balance less the
payout under WETH's precondition, and the nonzero success word the tail
consumed.  Mirrors PRORATA's `WithdrawPreCallEffect`; the crossing is returned
rather than assumed away. -/
theorem weth_withdraw_preCall_split {sevm : Sevm} {pre post : Devm}
    (run : Prog.RunCompiled sevm pre Blanc.weth post)
    (selected : Sevm.selector sevm = selector "withdraw" [.uint256]) :
    ∃ callPre callPost : Devm,
      Sevm.argWord sevm 0 ≤
          Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 ∧
        Devm.getStor callPre sevm.currentTarget =
          (Devm.getStor pre sevm.currentTarget).set sevm.caller.toB256
            (Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 -
              Sevm.argWord sevm 0) ∧
        (∀ account, sevm.currentTarget ≠ account →
          Devm.getStor callPre account = Devm.getStor pre account) ∧
        Ninst.Run sevm callPre Ninst.call callPost ∧
        Devm.getStor post = Devm.getStor callPost ∧
        [0, sevm.caller.toB256, Sevm.argWord sevm 0, 0, 0, 0, 0] <<+
          callPre.stack ∧
        Devm.getBal callPre = Devm.getBal pre ∧
        Devm.getCode callPre = Devm.getCode pre ∧
        (wethSpec.Pre sevm.currentTarget sevm pre →
          Stor.Solvent (Devm.getStor callPre sevm.currentTarget) 0
            (Devm.getBal callPre sevm.currentTarget - Sevm.argWord sevm 0)) ∧
        ∃ (success : B256) (guardPost : Devm),
          success ≠ 0 ∧ Devm.PopBurn [success] callPost guardPost := by
  obtain ⟨bodyPre, -, entryState, -, -, -, bodyRun⟩ :=
    runCompiled_enters_wethNonpayable (body := Blanc.withdraw) run selected
      (by simp [Blanc.wethFuncs])
  have entryStorage : Devm.getStor pre = Devm.getStor bodyPre :=
    funext (getStor_eq_of_state_eq entryState)
  simp only [Blanc.withdraw] at bodyRun
  rcases of_run_prepend Blanc.withdrawLoadCheck _ bodyRun with
    ⟨g1, guard, bodyRun⟩
  obtain ⟨guardStorage, less, hp1, lessIff⟩ := withdrawLoadCheck_exact guard
  rcases of_run_branch_revert bodyRun with ⟨g2, pop2, bodyRun⟩
  obtain ⟨lessZero, hp2⟩ := popBurn_pref pop2 hp1
  have covered : Sevm.argWord sevm 0 ≤
      Devm.getStorVal g1 sevm.currentTarget sevm.caller.toB256 :=
    lessIff.mp lessZero.symm
  have popStorage : Devm.getStor g1 = Devm.getStor g2 :=
    funext (fun a => (Devm.PopBurn.getStor pop2 a).symm)
  have guardBal : pre.getBal = g2.getBal :=
    (funext (getBal_eq_of_state_eq entryState)).trans
      ((Line.of_inv Devm.getBal (by line_inv) guard).trans
        (funext (getBal_eq_of_state_eq pop2.state)))
  have guardCode : pre.getCode = g2.getCode :=
    (funext (getCode_eq_of_state_eq entryState)).trans
      ((Line.of_inv Devm.getCode (by line_inv) guard).trans
        (funext (getCode_eq_of_state_eq pop2.state)))
  rcases of_run_next bodyRun with ⟨g3, subRun, bodyRun⟩
  have hp3 : (Devm.getStorVal g1 sevm.currentTarget sevm.caller.toB256 -
      Sevm.argWord sevm 0) :: Sevm.argWord sevm 0 :: [] <<+ g3.stack :=
    prefix_of_sub subRun hp2
  rcases of_run_next bodyRun with ⟨g4, callerRun, bodyRun⟩
  have hp4 : [sevm.caller.toB256,
      Devm.getStorVal g1 sevm.currentTarget sevm.caller.toB256 -
        Sevm.argWord sevm 0, Sevm.argWord sevm 0] <<+ g4.stack :=
    prefix_of_push (of_run_caller callerRun) hp3
  rcases of_run_next bodyRun with ⟨g5, storeRun, bodyRun⟩
  have stored := sstore_getStor_set storeRun hp4
  have debitRun : Line.Run sevm g2 [Blanc.Ninst.sub, Blanc.Ninst.caller,
      Blanc.Ninst.sstore] g5 :=
    Line.Run.cons subRun (Line.Run.cons callerRun
      (Line.Run.cons storeRun Line.Run.nil))
  have midStorage : Devm.getStor g2 = Devm.getStor g4 :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons subRun (Line.Run.cons callerRun Line.Run.nil))
  rcases of_run_prepend Blanc.sendToCaller _ bodyRun with ⟨g6, sendRun, bodyRun⟩
  obtain ⟨c4, callStack, crossingStorage, crossingBal, crossingCode, callRun⟩ :=
    sendToCaller_callPre (prefix_of_sstore storeRun hp4) sendRun
  have debitBal : g2.getBal = g5.getBal :=
    Line.of_inv Devm.getBal (by line_inv) debitRun
  have debitCode : g2.getCode = g5.getCode :=
    Line.of_inv Devm.getCode (by line_inv) debitRun
  obtain ⟨success, guardPost, nonzero, successPop, tailStorage⟩ :
      ∃ (success : B256) (guardPost : Devm), success ≠ 0 ∧
        Devm.PopBurn [success] g6 guardPost ∧
        Devm.getStor g6 = Devm.getStor post := by
    rcases of_run_branch bodyRun with
      ⟨t1, -, revertRun⟩ | ⟨w, t1, t2, nonzero, pop, burn, logRun⟩
    · exact absurd revertRun not_run_revert
    · refine ⟨w, t1, nonzero, pop, Eq.trans ?_ (Func.of_inv Devm.getStor Devm.getStor
        (by unfold Blanc.logWithdraw; func_inv) logRun)⟩
      exact (funext (fun a => (Devm.PopBurn.getStor pop a).symm)).trans
        (funext (fun a => (Devm.Burn.getStor burn a).symm))
  have solvent : wethSpec.Pre sevm.currentTarget sevm pre →
      Stor.Solvent (Devm.getStor c4 sevm.currentTarget) 0
        (Devm.getBal c4 sevm.currentTarget - Sevm.argWord sevm 0) := by
    intro precondition
    have atGuard : Precond sevm.currentTarget sevm g2 :=
      precond_of_precond (wethSpec_pre_iff.mp precondition) guardBal
        (entryStorage.trans (guardStorage.trans popStorage)) guardCode
    have rowAtGuard : Devm.getStorVal g1 sevm.currentTarget sevm.caller.toB256 =
        Devm.getStorVal g2 sevm.currentTarget sevm.caller.toB256 := by
      show (Devm.getStor g1 _).get _ = (Devm.getStor g2 _).get _
      rw [popStorage]
    obtain ⟨-, debited⟩ :=
      solvent_of_withdraw_update_bal atGuard hp2 rowAtGuard covered debitRun
    rw [← congrFun crossingStorage sevm.currentTarget,
      ← congrFun crossingBal sevm.currentTarget]
    exact debited
  have rowValue : Devm.getStorVal g1 sevm.currentTarget sevm.caller.toB256 =
      Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 := by
    show (Devm.getStor g1 _).get _ = (Devm.getStor pre _).get _
    rw [entryStorage, guardStorage]
  rw [rowValue] at covered stored
  refine ⟨c4, g6, covered, ?_, ?_, callRun, tailStorage.symm, callStack,
    (guardBal.trans (debitBal.trans crossingBal)).symm,
    (guardCode.trans (debitCode.trans crossingCode)).symm, solvent,
    success, guardPost, nonzero, successPop⟩
  · rw [← congrFun crossingStorage sevm.currentTarget, stored,
      ← congrFun midStorage sevm.currentTarget,
      ← congrFun popStorage sevm.currentTarget,
      ← congrFun guardStorage sevm.currentTarget,
      ← congrFun entryStorage sevm.currentTarget]
  · intro account different
    obtain ⟨pc, registerRun⟩ := of_run_reg storeRun
    rw [← congrFun crossingStorage account,
      sstore_preserves_getStor_ne registerRun different,
      ← congrFun midStorage account, ← congrFun popStorage account,
      ← congrFun guardStorage account, ← congrFun entryStorage account]

/-- **WETH `withdraw` pre-call split.**  The caller's row is debited before the
value-bearing `CALL` to the caller, nothing else in WETH's storage moves before
it, and the suffix after it writes no storage at all.  Mirrors PRORATA's
`WithdrawPreCallEffect`; the crossing is returned rather than assumed away. -/
theorem weth_withdraw_preCall_effect {sevm : Sevm} {pre post : Devm}
    (run : Prog.RunCompiled sevm pre Blanc.weth post)
    (selected : Sevm.selector sevm = selector "withdraw" [.uint256]) :
    ∃ callPre callPost : Devm,
      Sevm.argWord sevm 0 ≤
          Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 ∧
        Devm.getStor callPre sevm.currentTarget =
          (Devm.getStor pre sevm.currentTarget).set sevm.caller.toB256
            (Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 -
              Sevm.argWord sevm 0) ∧
        (∀ account, sevm.currentTarget ≠ account →
          Devm.getStor callPre account = Devm.getStor pre account) ∧
        Ninst.Run sevm callPre Ninst.call callPost ∧
        Devm.getStor post = Devm.getStor callPost := by
  obtain ⟨callPre, callPost, covered, written, foreignKept, callRun, after, -⟩ :=
    weth_withdraw_preCall_split run selected
  exact ⟨callPre, callPost, covered, written, foreignKept, callRun, after⟩

/-! ## The unconditional vault-row classification -/

/-- A committed exact WETH frame is a gas-exact compiled WETH run of its own
machine. -/
theorem wethFrame_runCompiled {frame : Exec.Frame}
    (identity : (Blanc.Exec.Frame.exactInvocation Blanc.weth wethAccount wethAccount frame)) :
    Prog.RunCompiled frame.sevm frame.pre Blanc.weth frame.post := by
  obtain ⟨pcZero, -, -, code⟩ := identity
  rcases frame with ⟨pc, sevm, pre, out, run, committed⟩
  cases pcZero
  cases out with
  | error error => simp [Execution.commits] at committed
  | ok post =>
      show Prog.RunCompiled sevm pre Blanc.weth post
      exact Prog.runCompiled_of_exec sevm pre Blanc.weth post weth_pcFree run code

/-- A successful compiled `transferFrom` really passed its source-address
guard.  `transferFromBody_exactEffect` derives this internally and then
projects only `.toAdr`; a classifier that must name the raw allowance cell
needs the ABI word itself. -/
private theorem transferFromBody_src_valid
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    (run : Func.Run fs sevm s Blanc.transferFrom r) :
    ValidAdr (Sevm.argWord sevm 0) := by
  simp only [Blanc.transferFrom] at run
  rcases of_run_prepend (arg 0) _ run with ⟨a1, h1, run⟩
  have hs1 : Sevm.argWord sevm 0 :: [] <<+ a1.stack := prefix_of_arg nil_pref h1
  rcases of_run_next run with ⟨a2, dupRun, run⟩
  have hs2 : [Sevm.argWord sevm 0, Sevm.argWord sevm 0] <<+ a2.stack :=
    prefix_of_dup_val dupRun (Stack.Nth.head _ _) hs1
  rcases of_run_prepend checkNonAddress _ run with ⟨a3, h3, run⟩
  rcases of_check_non_address hs2 h3 with ⟨invalid, hs3, validIff⟩
  rcases of_run_branch_revert run with ⟨a4, pop4, -⟩
  exact validIff.mp (popBurn_pref pop4 hs3).1.symm

/-- Source-address validity at the general caller. -/
theorem weth_transferFrom_compiled_src_valid {sevm : Sevm} {pre post : Devm}
    (run : Prog.RunCompiled sevm pre Blanc.weth post)
    (selected : Sevm.selector sevm =
      selector "transferFrom" [.address, .address, .uint256]) :
    ValidAdr (Sevm.argWord sevm 0) := by
  obtain ⟨bodyPre, -, -, -, -, -, bodyRun⟩ :=
    runCompiled_enters_wethNonpayable (body := Blanc.transferFrom) run selected
      (by simp [Blanc.wethFuncs])
  exact transferFromBody_src_valid bodyRun

/-- A balance transfer between two rows that are both distinct from the vault,
or whose credited row is the vault's with a zero amount, leaves the vault's row
exactly where it was. -/
private theorem transfer_vault_row_quiet {b d : Adr → B256}
    {source dest vault : Adr} {wad : B256}
    (move : Transfer b source wad dest d)
    (sourceNe : source ≠ vault) (quiet : dest ≠ vault ∨ wad.toNat = 0) :
    d vault = b vault := by
  obtain ⟨-, c, decrease, increase⟩ := move
  have first : b vault = c vault := (decrease vault).2 sourceNe
  rcases quiet with destNe | zero
  · rw [first]
    exact ((increase vault).2 destNe).symm
  · by_cases same : dest = vault
    · subst same
      have credited := (increase dest).1 rfl
      have wadZero : wad = 0 := B256.toNat_inj _ _ (by rw [zero]; rfl)
      rw [wadZero] at credited
      rw [first, ← credited]
      exact B256.toNat_inj _ _ (by
        rw [B256.toNat_add, B256.toNat_zero, Nat.add_zero, Nat.lo_eq,
          Nat.mod_eq_of_lt (B256.toNat_lt _)])
    · rw [first]
      exact ((increase vault).2 same).symm

/-- **The unconditional vault-row classification.**

A successful exact WETH frame whose caller is not the vault does exactly one of
four things to the vault's WETH row:

* leaves it alone;
* raises it by a positive amount from a source that is not the vault (a
  donation);
* is a `transferFrom` whose executed branch read the raw allowance cell
  `wethAllowanceKey vault.toB256 caller.toB256` (a runtime-authorized debit);
* is a `withdraw`, whose value-bearing callback to the caller is handed back
  as an actual retained crossing, with the vault's row untouched up to it and
  the whole storage frame after it equal to the crossing's post.

No honesty assumption is made about any callee.  The fourth arm is the one the
design's three-way statement omits, and it cannot be removed: `Blanc.weth` is
not `reachableExecFree`, so nothing at this rung excludes the callback's own
writes, and a consumer must recurse into it. -/
theorem wethFrame_vaultRow_classified (vault : Adr) (frame : Exec.Frame)
    (weth : (Blanc.Exec.Frame.exactInvocation Blanc.weth wethAccount wethAccount frame))
    (fresh : Exec.FreshEntry frame.sevm frame.pre)
    (callerNotVault : frame.sevm.caller ≠ vault) :
    (Stor.rest (Devm.getStor frame.post wethAccount) vault =
        Stor.rest (Devm.getStor frame.pre wethAccount) vault) ∨
      (∃ (source : Adr) (wad : B256), source ≠ vault ∧ 0 < wad.toNat ∧
        Transfer (Stor.rest (Devm.getStor frame.pre wethAccount)) source wad
          vault (Stor.rest (Devm.getStor frame.post wethAccount))) ∨
      (∃ call : WethAllowanceInvocation, call.approval = false ∧
        call.sevm = frame.sevm ∧ call.pre = frame.pre ∧
        call.post = frame.post ∧
        Sevm.argWord call.sevm 0 = vault.toB256 ∧
        call.pair? = some (vault.toB256, call.sevm.caller.toB256)) ∨
      (∃ callPre callPost : Devm,
        Stor.rest (Devm.getStor callPre wethAccount) vault =
            Stor.rest (Devm.getStor frame.pre wethAccount) vault ∧
          Ninst.Run frame.sevm callPre Ninst.call callPost ∧
          Devm.getStor frame.post = Devm.getStor callPost) := by
  have target : frame.sevm.currentTarget = wethAccount := weth.2.1
  have run : Prog.RunCompiled frame.sevm frame.pre Blanc.weth frame.post :=
    wethFrame_runCompiled weth
  have memoryWf : Mem.Wf frame.pre.memory := by
    rw [fresh.2]; exact Mem.wf_empty
  have vaultKeyNe : ∀ {a : Adr}, a ≠ vault → a.toB256 ≠ vault.toB256 := by
    intro a different equal
    exact different (by rw [← toAdr_toB256 a, equal, toAdr_toB256])
  obtain ⟨cls, -, -, fit⟩ := WethFrameClass.classification_total weth
  cases cls with
  | view =>
      left
      rw [← weth_view_compiled_effect run fit]
  | approve owner spender wad =>
      obtain ⟨selected, -, -, -⟩ := fit
      obtain ⟨keyInvalid, written⟩ :=
        weth_approve_compiled_raw_effect memoryWf run selected
      rw [target] at written
      left
      have keyNe : wethAllowanceKey frame.sevm.caller.toB256
          (Sevm.argWord frame.sevm 0) ≠ vault.toB256 := by
        intro equal
        exact keyInvalid (equal ▸ ⟨vault, rfl⟩)
      simp only [Stor.rest, Function.comp_apply, written,
        Stor.get_set_ne _ keyNe]
  | deposit caller value =>
      obtain ⟨miss, callerEq, -⟩ := fit
      obtain ⟨mid, entryState, -, -, -, depositRun⟩ :=
        runCompiled_enters_wethDeposit run miss
      obtain ⟨written, -⟩ := depositBody_effect depositRun
      have entryStorage : Devm.getStor frame.pre = Devm.getStor mid :=
        funext (getStor_eq_of_state_eq entryState)
      rw [target] at written
      left
      simp only [Stor.rest, Function.comp_apply, written,
        Stor.get_set_ne _ (vaultKeyNe callerNotVault), ← congrFun entryStorage]
  | withdraw caller wad =>
      obtain ⟨selected, -, -⟩ := fit
      obtain ⟨callPre, callPost, -, written, -, crossing, after⟩ :=
        weth_withdraw_preCall_effect run selected
      rw [target] at written
      exact Or.inr (Or.inr (Or.inr ⟨callPre, callPost, by
        simp only [Stor.rest, Function.comp_apply, written,
          Stor.get_set_ne _ (vaultKeyNe callerNotVault)], crossing, after⟩))
  | transfer caller dst wad =>
      obtain ⟨selected, -, -, -⟩ := fit
      obtain ⟨move, -, -⟩ := weth_transfer_compiled_effect run selected
      rw [target] at move
      by_cases credited : (Sevm.argWord frame.sevm 0).toAdr = vault
      · by_cases positive : 0 < (Sevm.argWord frame.sevm 1).toNat
        · exact Or.inr (Or.inl ⟨frame.sevm.caller, Sevm.argWord frame.sevm 1,
            callerNotVault, positive, credited ▸ move⟩)
        · left
          exact transfer_vault_row_quiet move callerNotVault (Or.inr (by omega))
      · left
        exact transfer_vault_row_quiet move callerNotVault (Or.inl credited)
  | transferFrom caller src dst wad =>
      obtain ⟨selected, -, -, -, -⟩ := fit
      obtain ⟨move, -⟩ := weth_transferFrom_compiled_row_effect run selected
      rw [target] at move
      by_cases debited : (Sevm.argWord frame.sevm 0).toAdr = vault
      · have srcValid : ValidAdr (Sevm.argWord frame.sevm 0) :=
          weth_transferFrom_compiled_src_valid run selected
        obtain ⟨sourceAdr, sourceEq⟩ := srcValid
        have owner : Sevm.argWord frame.sevm 0 = vault.toB256 := by
          rw [← sourceEq] at debited ⊢
          rw [toAdr_toB256] at debited
          rw [debited]
        refine Or.inr (Or.inr (Or.inl ⟨⟨frame.sevm, frame.pre, frame.post,
          false, target, memoryWf, run, by simpa using selected⟩,
          rfl, rfl, rfl, rfl, owner, ?_⟩))
        simp only [WethAllowanceInvocation.pair?, owner,
          if_neg (Ne.symm (vaultKeyNe callerNotVault)), Bool.false_eq_true,
          if_false]
      · by_cases credited : (Sevm.argWord frame.sevm 1).toAdr = vault
        · by_cases positive : 0 < (Sevm.argWord frame.sevm 2).toNat
          · exact Or.inr (Or.inl ⟨(Sevm.argWord frame.sevm 0).toAdr,
              Sevm.argWord frame.sevm 2, debited, positive, credited ▸ move⟩)
          · left
            exact transfer_vault_row_quiet move debited (Or.inr (by omega))
        · left
          exact transfer_vault_row_quiet move debited (Or.inl credited)

/-! ## The five former silence gaps, as theorems

`ProrataWethVaultRely` carried five `def … : Prop` gaps naming per-selector
message-level silence.  As written they were not merely unproved: a bare
`ProcessMessage msg slot (.ok post)` constrains the retained slot's raw
outcome only through `Frame.settle`, so an arbitrary `raw` satisfies it and the
gaps are false.  Each theorem below therefore also takes the slot's own
`Xlot.Filled` witness, which is what says the retained execution exists.

The `withdraw` gap is additionally *not* a silence statement: its frame
contains a value-bearing callback to an arbitrary callee, which can itself call
WETH.  It is replaced by the split that exposes that crossing. -/

/-- The calldata-only view of a frame's selector.  `Sevm.selector` reads
nothing but `data`, and this is that reading, so a message-level premise can be
stated before any frame exists. -/
def calldataSelector (data : Bytes) : B256 :=
  Bytes.toB256 (data.sliceD (0 : B256).toNat 32 0) >>> 224

theorem selector_eq_calldataSelector (sevm : Sevm) :
    Sevm.selector sevm = calldataSelector sevm.data := rfl

theorem calldataSelector_nil_not_mem :
    ∀ sel ∈ wethSelectors, calldataSelector [] ≠ sel := by
  decide +kernel

/-- **The settled WETH message reduction.**  A retained committing message to
`wethAccount` running the inherited WETH program either changed no cell at all
(no interpreted slot, or a rolled-back settlement) or exposes the actual
gas-exact compiled run whose WETH storage frame is the message's. -/
theorem weth_message_run_or_quiet {msg : Msg} {post : Devm} {slot : Xlot}
    (filled : Xlot.Filled slot)
    (process : ProcessMessage msg slot (.ok post))
    (target : msg.currentTarget = wethAccount)
    (uses : MessageUsesProgram msg Blanc.weth) :
    (∀ (owner : Adr) (key : B256),
        (post.state.getStor owner).get key =
          (msg.benv.state.getStor owner).get key) ∨
      (∃ (sevm : Sevm) (pre rawPost : Devm),
        sevm.currentTarget = wethAccount ∧ sevm.data = msg.data ∧
          Mem.Wf pre.memory ∧
          Prog.RunCompiled sevm pre Blanc.weth rawPost ∧
          Devm.getStor pre wethAccount =
            msg.benv.state.getStor wethAccount ∧
          post.state.getStor wethAccount =
            Devm.getStor rawPost wethAccount) := by
  cases slot with
  | none =>
      exact Or.inl (fun owner key =>
        processMessage_none_preserves_cell process owner key)
  | some entry =>
      obtain ⟨⟨pc, sevm, pre⟩, raw⟩ := entry
      by_cases clean : post.error.isSome = false
      · obtain ⟨rawPost, rawEq, -, stateEq, -⟩ :=
          MessageExecution.processMessage_clean_rawPost process clean
        subst rawEq
        obtain ⟨exc⟩ := filled
        obtain ⟨pcZero, codeEq, current, -, dataEq, -, entryStorage, memoryWf⟩ :=
          MessageExecution.processMessage_entry_facts wethAccount process
        subst pcZero
        have code : some sevm.code.toList = Prog.compile Blanc.weth := by
          rw [codeEq]; exact uses
        refine Or.inr ⟨sevm, pre, rawPost, current.trans target, dataEq,
          memoryWf,
          Prog.runCompiled_of_exec sevm pre Blanc.weth rawPost weth_pcFree
            exc code, entryStorage, ?_⟩
        rw [stateEq]
        rfl
      · refine Or.inl (fun owner key => ?_)
        have postError : post.error.isSome = true := by
          cases errorEq : post.error <;> simp_all
        rw [(ProcessMessage.rollback_of_error process postError).1]

/-- **Gap 1 (transfer), as a theorem.**  A non-static WETH `transfer` message
touches balance rows only, so every non-address cell — in particular every
vault-owned allowance cell the history touched — is silent. -/
theorem weth_transfer_message_silence {vault : Adr}
    {msg : Msg} {post : Devm} {slot : Xlot}
    {history : List WethAllowanceInvocation}
    (filled : Xlot.Filled slot)
    (process : ProcessMessage msg slot (.ok post))
    (target : msg.currentTarget = wethAccount)
    (uses : MessageUsesProgram msg Blanc.weth)
    (data : ∃ tail, msg.data =
      abiSelectorBytes (selector "transfer" [.address, .uint256]) ++ tail)
    (_collision : NoVaultAllowanceKeyCollision history vault)
    (p : B256 × B256) (touched : p ∈ touchedWethAllowancePairs history)
    (_owner : p.1 = vault.toB256) :
    (post.state.getStor wethAccount).get (wethAllowanceKey p.1 p.2) =
      (msg.benv.state.getStor wethAccount).get (wethAllowanceKey p.1 p.2) := by
  obtain ⟨tail, dataEq⟩ := data
  have invalid := touchedWethAllowancePairs_keys_nonaddress touched
  rcases weth_message_run_or_quiet filled process target uses with
    silent | ⟨sevm, pre, rawPost, current, sevmData, -, run, entry, exit⟩
  · exact silent _ _
  · have selected : Sevm.selector sevm =
        selector "transfer" [.address, .uint256] :=
      selector_eq_of_data_eq_abiSelectorBytes_append (by decide +kernel)
        (sevmData.trans dataEq)
    obtain ⟨-, off, -⟩ := weth_transfer_compiled_effect run selected
    rw [current] at off
    rw [exit, ← entry]
    exact (off _ invalid).symm

/-- **Gap 5 (non-static view call), as a theorem.**  The six read-only entries
write no storage at all, so every cell is silent — not only the allowance
cells the history touched. -/
theorem weth_view_message_silence
    {msg : Msg} {post : Devm} {slot : Xlot}
    (filled : Xlot.Filled slot)
    (process : ProcessMessage msg slot (.ok post))
    (target : msg.currentTarget = wethAccount)
    (uses : MessageUsesProgram msg Blanc.weth)
    (data : ∃ sel ∈ wethViewSelectors, ∃ tail,
      msg.data = abiSelectorBytes sel ++ tail ∧
        Bytes.toB256 (abiSelectorBytes sel) = sel)
    (key : B256) :
    (post.state.getStor wethAccount).get key =
      (msg.benv.state.getStor wethAccount).get key := by
  obtain ⟨sel, member, tail, dataEq, canonical⟩ := data
  rcases weth_message_run_or_quiet filled process target uses with
    silent | ⟨sevm, pre, rawPost, current, sevmData, -, run, entry, exit⟩
  · exact silent _ _
  · have selected : Sevm.selector sevm = sel :=
      selector_eq_of_data_eq_abiSelectorBytes_append canonical
        (sevmData.trans dataEq)
    have quiet := weth_view_compiled_effect run (selected ▸ member)
    rw [exit, ← entry, ← congrFun quiet wethAccount]

/-- **Gaps 2 and 3 (fallback deposit), as one theorem.**  Calldata matching
none of the ten dispatched selectors — empty calldata included — routes to the
payable fallback, which credits the caller's own balance row and writes nothing
else.  The premise is stated at the selector the dispatcher actually computes
rather than at a four-byte calldata prefix, because that is what WETH's
`fsig`/`dispatchWith` pair compares and it is total on short calldata. -/
theorem weth_fallback_message_silence
    {msg : Msg} {post : Devm} {slot : Xlot}
    (filled : Xlot.Filled slot)
    (process : ProcessMessage msg slot (.ok post))
    (target : msg.currentTarget = wethAccount)
    (uses : MessageUsesProgram msg Blanc.weth)
    (miss : ∀ sel ∈ wethSelectors, calldataSelector msg.data ≠ sel)
    (key : B256) (invalid : ¬ ValidAdr key) :
    (post.state.getStor wethAccount).get key =
      (msg.benv.state.getStor wethAccount).get key := by
  rcases weth_message_run_or_quiet filled process target uses with
    silent | ⟨sevm, pre, rawPost, current, sevmData, -, run, entry, exit⟩
  · exact silent _ _
  · have selectorMiss : ∀ sel ∈ wethSelectors, Sevm.selector sevm ≠ sel := by
      intro sel member
      rw [selector_eq_calldataSelector, sevmData]
      exact miss sel member
    obtain ⟨mid, entryState, -, -, -, depositRun⟩ :=
      runCompiled_enters_wethDeposit run selectorMiss
    obtain ⟨written, -⟩ := depositBody_effect depositRun
    rw [current] at written
    have midStorage : Devm.getStor pre = Devm.getStor mid :=
      funext (getStor_eq_of_state_eq entryState)
    have callerNe : sevm.caller.toB256 ≠ key := by
      intro equal
      exact invalid (by rw [← equal]; exact ⟨sevm.caller, rfl⟩)
    rw [exit, ← entry]
    change (Devm.getStor rawPost wethAccount).get key = _
    rw [written, Stor.get_set_ne _ callerNe, ← congrFun midStorage wethAccount]

/-- Empty calldata is a fallback deposit. -/
theorem weth_empty_message_silence
    {msg : Msg} {post : Devm} {slot : Xlot}
    (filled : Xlot.Filled slot)
    (process : ProcessMessage msg slot (.ok post))
    (target : msg.currentTarget = wethAccount)
    (uses : MessageUsesProgram msg Blanc.weth)
    (empty : msg.data = [])
    (key : B256) (invalid : ¬ ValidAdr key) :
    (post.state.getStor wethAccount).get key =
      (msg.benv.state.getStor wethAccount).get key :=
  weth_fallback_message_silence filled process target uses
    (by rw [empty]; exact calldataSelector_nil_not_mem) key invalid

/-- **Gap 4 (withdraw), as the split it has to be.**

`WethWithdrawSilence` is false as stated even with the retained execution
supplied: WETH `withdraw` sends value to its caller, and that callee may call
WETH again — including a `transferFrom` that debits a vault allowance the
vault really granted.  What is true, and what a history fold can consume, is
that the message's whole WETH storage movement at a non-address cell *is* the
callback's: the prefix writes one address-shaped row and the suffix writes
nothing. -/
theorem weth_withdraw_message_split
    {msg : Msg} {post : Devm} {slot : Xlot}
    (filled : Xlot.Filled slot)
    (process : ProcessMessage msg slot (.ok post))
    (target : msg.currentTarget = wethAccount)
    (uses : MessageUsesProgram msg Blanc.weth)
    (data : ∃ tail, msg.data =
      abiSelectorBytes (selector "withdraw" [.uint256]) ++ tail)
    (key : B256) (invalid : ¬ ValidAdr key) :
    ((post.state.getStor wethAccount).get key =
        (msg.benv.state.getStor wethAccount).get key) ∨
      (∃ (sevm : Sevm) (callPre callPost : Devm),
        sevm.currentTarget = wethAccount ∧ sevm.data = msg.data ∧
          (Devm.getStor callPre wethAccount).get key =
            (msg.benv.state.getStor wethAccount).get key ∧
          Ninst.Run sevm callPre Ninst.call callPost ∧
          (post.state.getStor wethAccount).get key =
            (Devm.getStor callPost wethAccount).get key) := by
  obtain ⟨tail, dataEq⟩ := data
  rcases weth_message_run_or_quiet filled process target uses with
    silent | ⟨sevm, pre, rawPost, current, sevmData, -, run, entry, exit⟩
  · exact Or.inl (silent _ _)
  · have selected : Sevm.selector sevm = selector "withdraw" [.uint256] :=
      selector_eq_of_data_eq_abiSelectorBytes_append (by decide +kernel)
        (sevmData.trans dataEq)
    obtain ⟨callPre, callPost, -, written, -, crossing, after⟩ :=
      weth_withdraw_preCall_effect run selected
    rw [current] at written
    have callerNe : sevm.caller.toB256 ≠ key := by
      intro equal
      exact invalid (by rw [← equal]; exact ⟨sevm.caller, rfl⟩)
    refine Or.inr ⟨sevm, callPre, callPost, current, sevmData, ?_, crossing, ?_⟩
    · rw [written, Stor.get_set_ne _ callerNe, ← entry]
    · rw [exit, ← congrFun after wethAccount]

end Blanc.Composition.ProrataWethVault
