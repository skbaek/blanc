import Blanc.LidoCircuitBreakerPinnedTarget
import Blanc.MessageExecutionInversion
import Blanc.ReachableExecFree

/-!
# Test-scoped controls for the pinned-target protocol

Nothing in this module is a contract, a port, or an entry-3 result.  The
compiled programs below exist only to show that the protocol is satisfiable
and that its noninterference and answer-shape clauses reject bad controls.
-/

namespace Blanc.LidoCircuitBreaker.PinnedTargetControl

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- The abstract projection is a real account storage word. -/
def pausedUntilSlot : B256 := 0

def pausedUntil (_target : Adr) (stor : Stor) : B256 :=
  stor.get pausedUntilSlot

/-- `pauseFor(uint256)`: preserve the infinite sentinel, otherwise store
`block.timestamp + duration`.  The compact straight-line selector avoids a
branch while keeping the public projection exact. -/
def stubPauseLine : Line :=
  arg 0 ++
    [Ninst.dup 0, Ninst.pushB256 0, Ninst.not, Ninst.eq, Ninst.iszero,
      Ninst.timestamp, Ninst.mul, Ninst.add,
      Ninst.pushB256 pausedUntilSlot, Ninst.sstore]

def stubPause : Func := stubPauseLine +++ Func.stop

/-- `isPaused()`: return the canonical word for `timestamp < pausedUntil`. -/
def stubQueryLine : Line :=
  [Ninst.pushB256 pausedUntilSlot, Ninst.sload, Ninst.timestamp, Ninst.lt]

def stubQuery : Func := stubQueryLine +++ returnWord

/-- One test-only protected selector.  Its guard precedes the length
dispatcher, so no calldata tail can alias the pause arm. -/
def stubProtectedSelector : B256 := selector "protectedAction" []

def stubProtectedLine : Line :=
  fsig ++ [Ninst.pushB256 stubProtectedSelector, Ninst.eq]

/-- The control uses the exact inbound calls' distinct ABI lengths: the
36-byte pause call enters the write arm; the four-byte static query enters the
read arm.  This is deliberately smaller than a production selector table. -/
def stubDispatchLine : Line :=
  [Ninst.calldatasize, Ninst.pushB256 36, Ninst.eq]

def stubBaseMain : Func := stubDispatchLine +++ (stubPause <?> stubQuery)

def stubMain : Func :=
  stubProtectedLine +++ (Func.rev <?> stubBaseMain)

def stubProgram : Prog := ⟨stubMain, []⟩

def stubBytes : Bytes := (Prog.compile stubProgram).getD []

def stubCode : ByteArray := ByteArray.mk stubBytes.toArray

theorem stubProgram_compiles : stubProgram.compiles = true := by
  decide +kernel

theorem stubProgram_compile : Prog.compile stubProgram = some stubBytes :=
  Prog.compile_eq_some_getD_of_compiles _ stubProgram_compiles

theorem stubProgram_pcFree : Prog.pcFree stubProgram = true := by
  decide

/-- The source map contains no frame-entering instruction. -/
theorem stubProgram_sourceSites_no_exec :
    ∀ site ∈ stubProgram.sourceSites, ∀ x : Xinst,
      site.instruction ≠ .exec x := by
  intro site member x
  have allClean : stubProgram.sourceSites.all
      (fun sourceSite =>
        match sourceSite.instruction with
        | .exec _ => false
        | _ => true) = true := by
    decide +kernel
  have clean := (List.all_eq_true.mp allClean) site member
  cases instructionEq : site.instruction <;>
    simp [instructionEq] at clean ⊢

/-- The selected stub main has no source `.exec` and no internal call edge.
This is the route-local certificate used by the generic noninterference
bridge; it does not require inspecting unrelated program entries. -/
theorem stubProgram_reachableExecFree :
    stubProgram.reachableExecFree stubProgram.main [] = true := by
  decide +kernel

private structure StubFrame (target : Adr) (calldata : Bytes)
    (sevm : Sevm) : Prop where
  currentTarget : sevm.currentTarget = target
  data : sevm.data = calldata

private lemma mem_reads_self (memory : Mem) :
    Mem.Reads memory memory.data.toList := by
  intro index
  simp

/-- Successful execution of the compiled stub exposes its source main body. -/
private theorem stubMain_run_of_exec
    {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post))
    (uses : some sevm.code.toList = Prog.compile stubProgram) :
    ∃ entry : Devm,
      Devm.BurnBy 1 pre entry ∧
      Func.Run [stubMain] sevm entry stubMain post := by
  have compiled := Prog.runCompiled_of_exec sevm pre stubProgram post
    stubProgram_pcFree run uses
  rcases compiled with ⟨entry, entryBurn, body⟩
  refine ⟨entry, entryBurn, ?_⟩
  simpa [stubProgram] using Func.Run.of_runCompiled body

private theorem stubBase_run_of_main
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (target : Adr)
    (run : Func.Run fs sevm pre stubMain post) :
    ∃ entry : Devm,
      Func.Run fs sevm entry stubBaseMain post ∧
      pre.memory = entry.memory ∧
      Devm.getStor pre target = Devm.getStor entry target := by
  unfold stubMain at run
  rcases of_run_prepend stubProtectedLine _ run with
    ⟨branchPre, guardRun, branchRun⟩
  have guardMemory : pre.memory = branchPre.memory :=
    Line.of_inv Devm.memory (by unfold stubProtectedLine; line_inv) guardRun
  have guardStorage : Devm.getStor pre target =
      Devm.getStor branchPre target :=
    congrFun (Line.of_inv Devm.getStor
      (by unfold stubProtectedLine; line_inv) guardRun) target
  unfold stubProtectedLine at guardRun
  rcases of_run_append fsig guardRun with
    ⟨afterSelector, fsigRun, guardRun⟩
  rcases Line.of_run_cons guardRun with
    ⟨afterPush, pushRun, guardRun⟩
  rcases Line.of_run_cons guardRun with
    ⟨afterEq, eqRun, guardNil⟩
  cases guardNil
  rcases of_run_branch branchRun with
      ⟨entry, zeroPop, baseRun⟩ |
      ⟨flag, popPost, bodyEntry, flagNonzero, flagPop, bodyBurn, revRun⟩
  · refine ⟨entry, baseRun, guardMemory.trans zeroPop.memory,
      guardStorage.trans (zeroPop.getStor target).symm⟩
  · exact absurd revRun not_run_rev

private theorem not_stubMain_run_of_protected
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (selectorEq : Sevm.selector sevm = stubProtectedSelector)
    (run : Func.Run fs sevm pre stubMain post) : False := by
  unfold stubMain at run
  rcases of_run_prepend stubProtectedLine _ run with
    ⟨branchPre, guardRun, branchRun⟩
  unfold stubProtectedLine at guardRun
  rcases of_run_append fsig guardRun with
    ⟨afterSelector, fsigRun, guardRun⟩
  rcases Line.of_run_cons guardRun with
    ⟨afterPush, pushRun, guardRun⟩
  rcases Line.of_run_cons guardRun with
    ⟨afterEq, eqRun, guardNil⟩
  cases guardNil
  have selectorPrefix : Sevm.selector sevm :: [] <<+
      afterSelector.stack := prefix_of_fsig nil_pref fsigRun
  have protectedPrefix : stubProtectedSelector ::
      Sevm.selector sevm :: [] <<+ afterPush.stack :=
    prefix_of_push (of_run_pushB256 pushRun) selectorPrefix
  have flagPrefix :
      (stubProtectedSelector =? Sevm.selector sevm) :: [] <<+
        branchPre.stack := prefix_of_eq eqRun protectedPrefix
  have flagOne :
      (stubProtectedSelector =? Sevm.selector sevm) = 1 := by
    rw [selectorEq, B256.eqCheck, if_pos rfl]
  rcases of_run_branch branchRun with
      ⟨entry, zeroPop, baseRun⟩ |
      ⟨flag, popPost, bodyEntry, flagNonzero, flagPop, bodyBurn, revRun⟩
  · have flagZero :
        (stubProtectedSelector =? Sevm.selector sevm) = 0 :=
      (popBurn_pref zeroPop flagPrefix).1.symm
    rw [flagOne] at flagZero
    exact (by cases flagZero)
  · exact absurd revRun not_run_rev

/-- The compiled control implements the bundle's exact pause effect. -/
theorem stub_pauseFor_effect
    {circuitBreaker target : Adr} {sevm : Sevm} {pre post : Devm}
    {duration : B256}
    (frame : StubFrame target (pauseForCalldata duration) sevm)
    (uses : some sevm.code.toList = Prog.compile stubProgram)
    (run : Exec 0 sevm pre (.ok post)) :
    pausedUntil target (post.state.getStor target) =
      pauseForProjection sevm.benvStat.time duration := by
  rcases stubMain_run_of_exec run uses with ⟨entry, -, mainRun⟩
  rcases stubBase_run_of_main target mainRun with
    ⟨entry, baseRun, -, -⟩
  unfold stubBaseMain at baseRun
  rcases of_run_prepend stubDispatchLine _ baseRun with
    ⟨branchPre, dispatchRun, branchRun⟩
  rcases Line.of_run_cons dispatchRun with ⟨afterSize, sizeRun, dispatchRun⟩
  rcases Line.of_run_cons dispatchRun with ⟨afterPush, pushRun, dispatchRun⟩
  rcases Line.of_run_cons dispatchRun with ⟨afterEq, eqRun, dispatchNil⟩
  cases dispatchNil
  have sizePrefix : sevm.data.length.toB256 :: [] <<+ afterSize.stack :=
    prefix_of_push (of_run_calldatasize sizeRun) nil_pref
  have pushPrefix : (36 : B256) :: sevm.data.length.toB256 :: [] <<+
      afterPush.stack :=
    prefix_of_push (of_run_pushB256 pushRun) sizePrefix
  have flagPrefix : ((36 : B256) =? sevm.data.length.toB256) :: [] <<+
      branchPre.stack :=
    prefix_of_eq eqRun pushPrefix
  rcases of_run_branch branchRun with
      ⟨zeroPre, zeroPop, queryRun⟩ |
      ⟨flag, popPost, bodyEntry, flagNonzero, flagPop, bodyBurn, pauseRun⟩
  · have flagZero : ((36 : B256) =? sevm.data.length.toB256) = 0 :=
      (popBurn_pref zeroPop flagPrefix).1.symm
    have flagOne : ((36 : B256) =? sevm.data.length.toB256) = 1 := by
      rw [frame.data]
      simp only [pauseForCalldata, List.length_append,
        abiSelectorBytes_length, B256.length_toBytes]
      change ((36 : B256) =? (36 : B256)) = 1
      rw [B256.eqCheck, if_pos rfl]
    rw [flagOne] at flagZero
    exact (by cases flagZero)
  · change Func.Run [stubMain] sevm bodyEntry stubPause post at pauseRun
    unfold stubPause at pauseRun
    rcases of_run_prepend stubPauseLine _ pauseRun with
      ⟨afterStore, pauseLineRun, stopRun⟩
    unfold stubPauseLine at pauseLineRun
    rcases of_run_append (arg 0) pauseLineRun with
      ⟨afterArg, argRun, pauseLineRun⟩
    rcases Line.of_run_cons pauseLineRun with
      ⟨afterDup, dupRun, pauseLineRun⟩
    rcases Line.of_run_cons pauseLineRun with
      ⟨afterZero, zeroRun, pauseLineRun⟩
    rcases Line.of_run_cons pauseLineRun with
      ⟨afterNot, notRun, pauseLineRun⟩
    rcases Line.of_run_cons pauseLineRun with
      ⟨afterEq, eqRun, pauseLineRun⟩
    rcases Line.of_run_cons pauseLineRun with
      ⟨afterIszero, iszeroRun, pauseLineRun⟩
    rcases Line.of_run_cons pauseLineRun with
      ⟨afterTime, timeRun, pauseLineRun⟩
    rcases Line.of_run_cons pauseLineRun with
      ⟨afterMul, mulRun, pauseLineRun⟩
    rcases Line.of_run_cons pauseLineRun with
      ⟨afterAdd, addRun, pauseLineRun⟩
    rcases Line.of_run_cons pauseLineRun with
      ⟨beforeStore, keyRun, pauseLineRun⟩
    rcases Line.of_run_cons pauseLineRun with
      ⟨stored, storeRun, pauseLineNil⟩
    cases pauseLineNil
    have argPrefix : Sevm.argWord sevm 0 :: [] <<+ afterArg.stack :=
      prefix_of_arg nil_pref argRun
    have argEq : Sevm.argWord sevm 0 = duration := by
      apply dataWord_of_append
        (pre := abiSelectorBytes pauseForSelector) (post := [])
      · rw [abiSelectorBytes_length]
        rfl
      · simpa [pauseForCalldata] using frame.data
    rw [argEq] at argPrefix
    have dupPrefix : duration :: duration :: [] <<+ afterDup.stack :=
      prefix_of_dup_val dupRun (by show_nth) argPrefix
    have zeroPrefix : (0 : B256) :: duration :: duration :: [] <<+
        afterZero.stack :=
      prefix_of_push (of_run_pushB256 zeroRun) dupPrefix
    have notPrefix : pauseInfiniteSentinel :: duration :: duration :: [] <<+
        afterNot.stack := by
      have zeroNot : ~~~ (0 : B256) = pauseInfiniteSentinel := rfl
      rw [← zeroNot]
      exact prefix_of_not notRun zeroPrefix
    have eqPrefix : (pauseInfiniteSentinel =? duration) :: duration :: [] <<+
        afterEq.stack :=
      prefix_of_eq eqRun notPrefix
    have iszeroPrefix :
        ((pauseInfiniteSentinel =? duration) =? 0) :: duration :: [] <<+
          afterIszero.stack :=
      prefix_of_iszero iszeroRun eqPrefix
    have timePrefix : sevm.benvStat.time ::
        ((pauseInfiniteSentinel =? duration) =? 0) :: duration :: [] <<+
        afterTime.stack :=
      prefix_of_timestamp iszeroPrefix timeRun
    have mulPrefix :
        (sevm.benvStat.time *
          ((pauseInfiniteSentinel =? duration) =? 0)) :: duration :: [] <<+
            afterMul.stack :=
      prefix_of_mul mulRun timePrefix
    have sumPrefix :
        (sevm.benvStat.time *
          ((pauseInfiniteSentinel =? duration) =? 0) + duration) :: [] <<+
        afterAdd.stack :=
      prefix_of_add addRun mulPrefix
    have keyPrefix : pausedUntilSlot ::
        (sevm.benvStat.time *
          ((pauseInfiniteSentinel =? duration) =? 0) + duration) :: [] <<+
            beforeStore.stack :=
      prefix_of_push (of_run_pushB256 keyRun) sumPrefix
    have effect := sstore_getStor_set storeRun keyPrefix
    rw [frame.currentTarget] at effect
    have stopStor := congrFun
      (Func.of_inv Devm.getStor Devm.getStor (by func_inv) stopRun) target
    unfold pausedUntil
    change (Devm.getStor post target).get pausedUntilSlot =
      pauseForProjection sevm.benvStat.time duration
    rw [← stopStor, effect, Stor.get_set_self,
      compact_pause_word_eq_projection]

/-- The Lido one-word return fragment returns the stack head and preserves the
entry error field.  Its full overwrite makes the initial memory image
irrelevant, while `Mem.Wf` rules out truncation in `Mem.write`. -/
private lemma error_eq_of_eq
    {sevm : Sevm} {pre post : Devm}
    (run : Ninst.Run sevm pre Ninst.eq post) :
    pre.error = post.error := by
  rcases of_run_reg run with ⟨pc, instructionRun⟩
  simp only [Rinst.run, Rinst.runCore] at instructionRun
  rcases Devm.diffBurn_of_applyBinary instructionRun with
    ⟨left, right, relation⟩
  exact relation.error

private lemma error_eq_of_lt
    {sevm : Sevm} {pre post : Devm}
    (run : Ninst.Run sevm pre Ninst.lt post) :
    pre.error = post.error := by
  rcases of_run_reg run with ⟨pc, instructionRun⟩
  simp only [Rinst.run, Rinst.runCore] at instructionRun
  rcases Devm.diffBurn_of_applyBinary instructionRun with
    ⟨left, right, relation⟩
  exact relation.error

private lemma error_eq_of_timestamp
    {sevm : Sevm} {pre post : Devm}
    (run : Ninst.Run sevm pre Ninst.timestamp post) :
    pre.error = post.error := by
  change Ninst.Run sevm pre (.reg .timestamp) post at run
  rcases of_run_reg run with ⟨pc, instructionRun⟩
  simp only [Rinst.run, Rinst.runCore] at instructionRun
  exact (Devm.pushBurn_of_pushItem instructionRun).error

private lemma error_eq_of_sload
    {sevm : Sevm} {pre post : Devm}
    (run : Ninst.Run sevm pre Ninst.sload post) :
    pre.error = post.error := by
  rcases of_run_reg run with ⟨pc, instructionRun⟩
  simp only [Rinst.run, Rinst.runCore] at instructionRun
  rcases Except.bind_eq_ok instructionRun with
    ⟨⟨key, afterKey⟩, popKey, instructionRun⟩
  have popError := (Devm.pop_of_pop popKey).error
  split at instructionRun
  · rcases Except.bind_eq_ok instructionRun with
      ⟨charged, charge, push⟩
    exact popError.trans
      ((Devm.burn_of_chargeGas charge).error.trans
        (Devm.push_of_push push).error)
  · rcases Except.bind_eq_ok instructionRun with
      ⟨charged, charge, push⟩
    have accessError : afterKey.error =
        (addAccessedStorageKey afterKey sevm.currentTarget key).error := rfl
    exact popError.trans (accessError.trans
      ((Devm.burn_of_chargeGas charge).error.trans
        (Devm.push_of_push push).error))

private lemma error_eq_of_mstore
    {sevm : Sevm} {pre post : Devm}
    (run : Ninst.Run sevm pre Ninst.mstore post) :
    pre.error = post.error := by
  rcases of_run_reg run with ⟨pc, instructionRun⟩
  simp only [Rinst.run, Rinst.runCore] at instructionRun
  rcases Except.bind_eq_ok instructionRun with
    ⟨⟨index, afterIndex⟩, popIndex, instructionRun⟩
  rcases Except.bind_eq_ok instructionRun with
    ⟨⟨word, afterWord⟩, popWord, instructionRun⟩
  rcases Except.bind_eq_ok instructionRun with
    ⟨charged, charge, finish⟩
  have indexError := (Devm.pop_of_popToNat popIndex).choose_spec.error
  have wordError := (Devm.pop_of_pop popWord).error
  have chargeError := (Devm.burn_of_chargeGas charge).error
  injection finish with stateEq
  rw [← stateEq]
  exact indexError.trans (wordError.trans chargeError)

private lemma error_eq_of_return
    {sevm : Sevm} {pre post : Devm}
    (run : Linst.Run sevm pre .ret (.ok post)) :
    pre.error = post.error := by
  simp only [Linst.Run, Linst.run] at run
  rcases Except.bind_eq_ok run with
    ⟨⟨index, afterIndex⟩, popIndex, run⟩
  rcases Except.bind_eq_ok run with
    ⟨⟨size, afterSize⟩, popSize, run⟩
  rcases Except.bind_eq_ok run with ⟨charged, charge, finish⟩
  have indexError := (Devm.pop_of_popToNat popIndex).choose_spec.error
  have sizeError := (Devm.pop_of_popToNat popSize).choose_spec.error
  have chargeError := (Devm.burn_of_chargeGas charge).error
  injection finish with stateEq
  rw [← stateEq]
  exact indexError.trans (sizeError.trans chargeError)

private lemma of_returnWord
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {word : B256} {xs : Stack}
    (stackPrefix : word :: xs <<+ pre.stack)
    (memoryWf : Mem.Wf pre.memory)
    (run : Func.Run fs sevm pre returnWord post) :
    post.output = word.toBytes ∧ post.error = pre.error := by
  have reads : Mem.Reads pre.memory pre.memory.data.toList :=
    mem_reads_self pre.memory
  simp only [returnWord] at run
  rcases of_run_prepend (mstoreAt 0) _ run with
    ⟨afterStore, storeRun, run⟩
  rcases of_run_mstoreAt_val storeRun stackPrefix with
    ⟨stackAfterStore, memoryAfterStore⟩
  have storeError : pre.error = afterStore.error := by
    have storeRun' := storeRun
    unfold mstoreAt at storeRun'
    rcases Line.of_run_cons storeRun' with
      ⟨afterOffset, offsetRun, storeRun'⟩
    rcases Line.of_run_cons storeRun' with
      ⟨afterWord, wordRun, storeNil⟩
    cases storeNil
    exact (of_run_pushB256 offsetRun).error.trans
      (error_eq_of_mstore wordRun)
  have storedReads : Mem.Reads afterStore.memory
      (Bytes.writeAt pre.memory.data.toList 0 word.toBytes) := by
    rw [memoryAfterStore]
    exact Mem.Reads.write memoryWf reads 0 _
  rcases of_run_prepend (pushList [32, 0]) _ run with
    ⟨beforeReturn, rangeRunFull, returnRun⟩
  rcases Line.of_run_cons rangeRunFull with
    ⟨afterSize, sizeRun, rangeRun⟩
  rcases Line.of_run_cons rangeRun with
    ⟨afterOffset, offsetRun, rangeNil⟩
  cases rangeNil
  have sizePrefix : (32 : B256) :: xs <<+ afterSize.stack :=
    prefix_of_push (of_run_pushB256 sizeRun) stackAfterStore
  have offsetPrefix : (0 : B256) :: (32 : B256) :: xs <<+
      beforeReturn.stack :=
    prefix_of_push (of_run_pushB256 offsetRun) sizePrefix
  have rangeMemory : afterStore.memory = beforeReturn.memory :=
    Line.of_inv Devm.memory (by line_inv) rangeRunFull
  have rangeError : afterStore.error = beforeReturn.error :=
    (of_run_pushB256 sizeRun).error.trans
      (of_run_pushB256 offsetRun).error
  have returnError : beforeReturn.error = post.error := by
    cases returnRun with
    | last terminalRun => exact error_eq_of_return terminalRun
  have errorEq : pre.error = post.error :=
    storeError.trans (rangeError.trans returnError)
  refine ⟨?_, errorEq.symm⟩
  rw [(of_run_ret_val offsetPrefix returnRun).1,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    Mem.Reads.read (rangeMemory ▸ storedReads) 0 32,
    show (32 : Nat) = word.toBytes.length from
      (B256.length_toBytes word).symm,
    Bytes.sliceD_writeAt]

private lemma acceptedBoolWord_iff
    {post : Devm} {word result : B256}
    (errorClean : post.error = none)
    (outputEq : post.output = word.toBytes) :
    AcceptedBoolWord post result ↔ word = result := by
  have sliceEq : word.toBytes.sliceD 0 word.toBytes.length 0 =
      word.toBytes := by
    simpa [Bytes.writeAt] using
      (Bytes.sliceD_writeAt ([] : Bytes) word.toBytes 0)
  have headEq : Bytes.toB256 (post.output.sliceD 0 32 0) = word := by
    rw [outputEq,
      show (32 : Nat) = word.toBytes.length from
        (B256.length_toBytes word).symm,
      sliceEq, B256.toB256_toBytes]
  constructor
  · intro accepted
    exact headEq.symm.trans accepted.2.2
  · intro wordEq
    refine ⟨?_, ?_, ?_⟩
    · rw [errorClean]
      rfl
    · rw [outputEq, B256.length_toBytes]
    · exact headEq.trans wordEq

/-- The compiled control's static query returns canonical true exactly for a
paused entry state and canonical false otherwise. -/
theorem stub_isPaused_truthful
    {circuitBreaker target : Adr} {sevm : Sevm} {pre post : Devm}
    (frame : StubFrame target isPausedCalldata sevm)
    (uses : some sevm.code.toList = Prog.compile stubProgram)
    (memoryWf : Mem.Wf pre.memory)
    (postClean : post.error = none)
    (run : Exec 0 sevm pre (.ok post)) :
    pausedUntil target (post.state.getStor target) =
        pausedUntil target (pre.state.getStor target) ∧
      (AcceptedBoolWord post 1 ↔
        PausedAt pausedUntil pre.state target sevm.benvStat.time) ∧
      (¬ PausedAt pausedUntil pre.state target sevm.benvStat.time →
        AcceptedBoolWord post 0 ∨ BoolQueryFailure post) := by
  rcases stubMain_run_of_exec run uses with
    ⟨guardEntry, entryBurnBy, mainRun⟩
  have entryBurn := Devm.Burn.of_burnBy entryBurnBy
  rcases stubBase_run_of_main target mainRun with
    ⟨entry, baseRun, outerMemory, outerStorage⟩
  unfold stubBaseMain at baseRun
  rcases of_run_prepend stubDispatchLine _ baseRun with
    ⟨branchPre, dispatchRun, branchRun⟩
  have dispatchMemory : entry.memory = branchPre.memory :=
    Line.of_inv Devm.memory (by unfold stubDispatchLine; line_inv) dispatchRun
  have dispatchStorage : Devm.getStor entry target =
      Devm.getStor branchPre target :=
    congrFun (Line.of_inv Devm.getStor
      (by unfold stubDispatchLine; line_inv) dispatchRun) target
  rcases Line.of_run_cons dispatchRun with
    ⟨afterSize, sizeRun, dispatchRun⟩
  rcases Line.of_run_cons dispatchRun with
    ⟨afterPush, pushRun, dispatchRun⟩
  rcases Line.of_run_cons dispatchRun with
    ⟨afterEq, eqRun, dispatchNil⟩
  cases dispatchNil
  have sizePrefix : sevm.data.length.toB256 :: [] <<+ afterSize.stack :=
    prefix_of_push (of_run_calldatasize sizeRun) nil_pref
  have pushPrefix : (36 : B256) :: sevm.data.length.toB256 :: [] <<+
      afterPush.stack :=
    prefix_of_push (of_run_pushB256 pushRun) sizePrefix
  have flagPrefix : ((36 : B256) =? sevm.data.length.toB256) :: [] <<+
      branchPre.stack :=
    prefix_of_eq eqRun pushPrefix
  have dispatchZero : ((36 : B256) =? sevm.data.length.toB256) = 0 := by
    rw [frame.data]
    simp only [isPausedCalldata, abiSelectorBytes_length]
    change ((36 : B256) =? (4 : B256)) = 0
    rw [B256.eqCheck, if_neg (by decide)]
  rcases of_run_branch branchRun with
      ⟨queryEntry, zeroPop, queryRun⟩ |
      ⟨flag, popPost, bodyEntry, flagNonzero, flagPop, bodyBurn, pauseRun⟩
  · have queryRunFull := queryRun
    have queryStorage : Devm.getStor queryEntry target =
        Devm.getStor post target :=
      congrFun (Func.of_inv Devm.getStor Devm.getStor
        (by func_inv) queryRunFull) target
    change Func.Run [stubMain] sevm queryEntry stubQuery post at queryRun
    unfold stubQuery at queryRun
    rcases of_run_prepend stubQueryLine _ queryRun with
      ⟨beforeReturn, queryLineRun, returnRun⟩
    have queryMemory : queryEntry.memory = beforeReturn.memory :=
      Line.of_inv Devm.memory (by unfold stubQueryLine; line_inv) queryLineRun
    unfold stubQueryLine at queryLineRun
    rcases Line.of_run_cons queryLineRun with
      ⟨afterKey, keyRun, queryLineRun⟩
    rcases Line.of_run_cons queryLineRun with
      ⟨afterLoad, loadRun, queryLineRun⟩
    rcases Line.of_run_cons queryLineRun with
      ⟨afterTime, timeRun, queryLineRun⟩
    rcases Line.of_run_cons queryLineRun with
      ⟨afterLt, ltRun, queryLineNil⟩
    cases queryLineNil
    have keyPrefix : pausedUntilSlot :: [] <<+ afterKey.stack :=
      prefix_of_push (of_run_pushB256 keyRun) nil_pref
    rcases prefix_of_sload loadRun keyPrefix with
      ⟨storedUntil, storedPrefix, storedEq⟩
    have timePrefix : sevm.benvStat.time :: storedUntil :: [] <<+
        afterTime.stack :=
      prefix_of_timestamp storedPrefix timeRun
    have pausedPrefix : (sevm.benvStat.time <? storedUntil) :: [] <<+
        beforeReturn.stack :=
      prefix_of_lt ltRun timePrefix
    have storageAtLoad : Devm.getStor afterKey target =
        Devm.getStor pre target := by
      have keyStorage := congrFun
        (Ninst.Hinv.inv (f := Devm.getStor) keyRun) target
      have branchStorage := zeroPop.getStor target
      exact keyStorage.symm.trans (branchStorage.trans
        (dispatchStorage.symm.trans (outerStorage.symm.trans
          (entryBurn.getStor target))))
    rw [frame.currentTarget] at storedEq
    change storedUntil = (Devm.getStor afterKey target).get pausedUntilSlot at storedEq
    rw [storageAtLoad] at storedEq
    change storedUntil =
      pausedUntil target (pre.state.getStor target) at storedEq
    rw [storedEq] at pausedPrefix
    have fullMemory : pre.memory = beforeReturn.memory :=
      entryBurn.memory.trans (outerMemory.trans (dispatchMemory.trans
        (zeroPop.memory.trans queryMemory)))
    have returnMemoryWf : Mem.Wf beforeReturn.memory := by
      rw [← fullMemory]
      exact memoryWf
    rcases of_returnWord pausedPrefix returnMemoryWf returnRun with
      ⟨outputEq, -⟩
    have projectionEq :
        pausedUntil target (post.state.getStor target) =
          pausedUntil target (pre.state.getStor target) := by
      unfold pausedUntil
      have storageEq : Devm.getStor post target =
          Devm.getStor pre target :=
        queryStorage.symm.trans ((zeroPop.getStor target).trans
          (dispatchStorage.symm.trans (outerStorage.symm.trans
            (entryBurn.getStor target))))
      change (Devm.getStor post target).get pausedUntilSlot =
        (Devm.getStor pre target).get pausedUntilSlot
      exact congrArg (fun stor : Stor => stor.get pausedUntilSlot) storageEq
    have acceptedIff (result : B256) :
        AcceptedBoolWord post result ↔
          (sevm.benvStat.time <?
            pausedUntil target (pre.state.getStor target)) = result :=
      acceptedBoolWord_iff (result := result) postClean outputEq
    have wordOneIff :
        (sevm.benvStat.time <?
          pausedUntil target (pre.state.getStor target)) = 1 ↔
          PausedAt pausedUntil pre.state target sevm.benvStat.time := by
      unfold PausedAt
      constructor
      · intro wordOne
        by_contra notPaused
        have wordZero :
            (sevm.benvStat.time <?
              pausedUntil target (pre.state.getStor target)) = 0 := by
          rw [B256.ltCheck, if_neg notPaused]
        rw [wordZero] at wordOne
        exact (by cases wordOne)
      · intro paused
        rw [B256.ltCheck, if_pos paused]
    refine ⟨projectionEq, (acceptedIff 1).trans wordOneIff, ?_⟩
    intro notPaused
    left
    apply (acceptedIff 0).mpr
    unfold PausedAt at notPaused
    simp [B256.ltCheck, notPaused]
  · have flagEq : flag = ((36 : B256) =? sevm.data.length.toB256) :=
      (popBurn_pref flagPop flagPrefix).1
    rw [dispatchZero] at flagEq
    exact (flagNonzero flagEq).elim

/-- The compiled stub discharges the complete Lido specialization, including
one nonempty protected selector whose clean paused execution must revert. -/
theorem stub_lidoPinnedPauseTarget
    (circuitBreaker pauser target : Adr)
    (different : target ≠ circuitBreaker) :
    LidoPinnedPauseTarget circuitBreaker pauser target stubProgram
      pausedUntil [stubProtectedSelector] := by
  refine {
    pauseFor_effect := ?_
    isPaused_truthful := ?_
    circuitBreaker_noninterference := ?_
    protectedSurface_reverts := ?_
  }
  · intro msg xl post duration exactCall executes process clean
    rcases executes with
      ⟨messageUses, ⟨pc, sevm, pre⟩, raw, xlEq, ⟨run⟩⟩
    subst xl
    rcases MessageExecution.processMessage_entry_facts target process with
      ⟨pcZero, codeEq, current, codeAddress, data, time,
        entryStorage, memoryWf⟩
    subst pc
    rcases MessageExecution.processMessage_clean_rawPost process clean with
      ⟨rawPost, rfl, rawClean, stateEq, outputEq⟩
    have frame : StubFrame target (pauseForCalldata duration) sevm :=
      ⟨current.trans exactCall.currentTarget, data.trans exactCall.data⟩
    have uses : some sevm.code.toList = Prog.compile stubProgram := by
      rw [codeEq]
      exact messageUses
    have effect := stub_pauseFor_effect
      (circuitBreaker := circuitBreaker) frame uses run
    rw [stateEq, effect, time]
  · intro msg xl ex exactCall executes process post exEq clean
    subst ex
    rcases executes with
      ⟨messageUses, ⟨pc, sevm, pre⟩, raw, xlEq, ⟨run⟩⟩
    subst xl
    rcases MessageExecution.processMessage_entry_facts target process with
      ⟨pcZero, codeEq, current, codeAddress, data, time,
        entryStorage, memoryWf⟩
    subst pc
    rcases MessageExecution.processMessage_clean_rawPost process clean with
      ⟨rawPost, rfl, rawClean, stateEq, outputEq⟩
    have frame : StubFrame target isPausedCalldata sevm :=
      ⟨current.trans exactCall.currentTarget, data.trans exactCall.data⟩
    have uses : some sevm.code.toList = Prog.compile stubProgram := by
      rw [codeEq]
      exact messageUses
    rcases stub_isPaused_truthful (circuitBreaker := circuitBreaker)
        frame uses memoryWf rawClean run with
      ⟨projection, truthful, falseOrFailure⟩
    have acceptedEq (word : B256) :
        AcceptedBoolWord post word ↔ AcceptedBoolWord rawPost word := by
      simp only [AcceptedBoolWord, clean, rawClean, outputEq,
        Option.isSome_none, Bool.false_eq_true, true_and]
    have acceptedExecutionEq (word : B256) :
        AcceptedBoolExecution (.ok post) word ↔
          AcceptedBoolWord rawPost word := by
      constructor
      · rintro ⟨child, childEq, accepted⟩
        cases childEq
        exact (acceptedEq word).mp accepted
      · intro accepted
        exact ⟨post, rfl, (acceptedEq word).mpr accepted⟩
    have failureExecutionEq :
        BoolQueryExecutionFailure (.ok post) ↔
          BoolQueryFailure rawPost := by
      unfold BoolQueryExecutionFailure BoolQueryFailure
      rw [acceptedExecutionEq 0, acceptedExecutionEq 1]
    have pausedEq :
        PausedAt pausedUntil pre.state target sevm.benvStat.time ↔
          PausedAt pausedUntil msg.benv.state target msg.benv.stat.time := by
      unfold PausedAt
      rw [entryStorage, time]
    refine ⟨?_, ?_, ?_⟩
    · rw [stateEq]
      exact projection.trans
        (congrArg (pausedUntil target) entryStorage)
    · exact acceptedExecutionEq 1 |>.trans (truthful.trans pausedEq)
    · intro notPaused
      have notPausedRaw :
          ¬ PausedAt pausedUntil pre.state target sevm.benvStat.time :=
        fun pausedRaw => notPaused (pausedEq.mp pausedRaw)
      rcases falseOrFailure notPausedRaw with accepted | failed
      · exact Or.inl ((acceptedExecutionEq 0).mpr accepted)
      · exact Or.inr (failureExecutionEq.mpr failed)
  · intro msg xl ex inbound executes process key member
    rcases executes with
      ⟨messageUses, ⟨pc, sevm, pre⟩, raw, xlEq, ⟨witnessRun⟩⟩
    subst xl
    intro actualRun
    rcases MessageExecution.processMessage_entry_facts target process with
      ⟨pcZero, codeEq, current, codeAddress, data, time,
        entryStorage, memoryWf⟩
    have msgCurrent : msg.currentTarget = target := by
      rcases inbound with ⟨duration, exactCall⟩ | exactCall
      · exact exactCall.currentTarget
      · exact exactCall.currentTarget
    have msgCodeAddress : msg.codeAddress = some target := by
      rcases inbound with ⟨duration, exactCall⟩ | exactCall
      · exact exactCall.codeAddress
      · exact exactCall.codeAddress
    have invocation :
        (⟨pc, sevm, pre, raw, actualRun⟩ : Exec.Deriv).exactInvocation
          stubProgram target target := by
      refine ⟨pcZero, current.trans msgCurrent,
        codeAddress.trans msgCodeAddress, ?_⟩
      rw [codeEq]
      exact messageUses
    exact Exec.noRetainedWriteTo_of_exactMain_reachableExecFree actualRun key
      invocation different [] stubProgram_reachableExecFree
  · intro msg xl child selected currentTarget targetAddress codeAddress
      executes hasSelector member paused process settled
    simp only [List.mem_singleton] at member
    subst selected
    rcases settled with childClean | childRevert
    · rcases executes with
        ⟨messageUses, ⟨pc, sevm, pre⟩, raw, xlEq, ⟨witnessRun⟩⟩
      subst xl
      rcases MessageExecution.processMessage_entry_facts target process with
        ⟨pcZero, codeEq, current, entryCodeAddress, data, time,
          entryStorage, memoryWf⟩
      subst pc
      have clean : child.error.isSome = false := by
        rw [childClean]
        rfl
      rcases MessageExecution.processMessage_clean_rawPost process clean with
        ⟨rawPost, rfl, rawClean, stateEq, outputEq⟩
      have uses : some sevm.code.toList = Prog.compile stubProgram := by
        rw [codeEq]
        exact messageUses
      rcases hasSelector with ⟨tail, messageData⟩
      have canonical :
          Bytes.toB256 (abiSelectorBytes stubProtectedSelector) =
            stubProtectedSelector := by
        have protectedEq : stubProtectedSelector = (0x3d7b369a : B256) := by
          decide +kernel
        rw [protectedEq]
        rfl
      have selectorEq : Sevm.selector sevm = stubProtectedSelector :=
        Blanc.selector_eq_of_data_eq_abiSelectorBytes_append canonical
          (data.trans messageData)
      rcases stubMain_run_of_exec witnessRun uses with
        ⟨entry, burnBy, mainRun⟩
      exact (not_stubMain_run_of_protected selectorEq mainRun).elim
    · exact childRevert

/-! ## Source-semantic successful composition -/

/-- An actual clean settled `pauseFor` message execution leaves the stub
paused and discharges both CircuitBreaker-cell noninterference obligations.
This is the account/message-level successor of the original toy composition
control: execution is an explicit semantic witness, never evaluator-provided
theorem evidence. -/
theorem stub_successful_pause_composition
    {circuitBreaker pauser target : Adr} {msg : Msg} {xl : Xlot}
    {post : Devm} {duration : B256}
    (different : target ≠ circuitBreaker)
    (exactCall : ExactTargetCall circuitBreaker target
      (pauseForCalldata duration) false msg)
    (executes : MessageExecutesProgram msg xl stubProgram)
    (process : ProcessMessage msg xl (.ok post))
    (clean : post.error.isSome = false)
    (strictGrowth :
      msg.benv.stat.time <
        pauseForProjection msg.benv.stat.time duration) :
    PausedAt pausedUntil post.state target msg.benv.stat.time ∧
      ∀ key ∈ [countSlot pauser.toB256, heartbeatIntervalSlot],
        TargetInvocationNoRetainedWriteTo xl circuitBreaker key := by
  have bundle := stub_lidoPinnedPauseTarget circuitBreaker pauser target
    different
  constructor
  · unfold PausedAt
    rw [bundle.pauseFor_effect exactCall executes process clean]
    exact strictGrowth
  · intro key member
    exact bundle.circuitBreaker_noninterference
      (Or.inl ⟨duration, exactCall⟩) executes process key member

/-! ## One benign outbound CALL

This closed-world control is deliberately not another universal bundle.  It
is one exact pause-shaped account message whose compiled parent stages and
performs an ordinary CALL to an inert STOP account before stopping.  The
theorem below presents the exact clause-(iii) antecedents and semantic
conclusion at the same retained message slot, while that slot's frame tree is
provably non-childless. -/

def benignCallTarget : Adr := 0x100

def benignCircuitBreaker : Adr := 0x200

def benignCallPauser : Adr := 0x201

def benignCallParentTarget : Adr := 0x300

def benignCallStaging : Line :=
  [Ninst.pushB256 0, Ninst.pushB256 0, Ninst.pushB256 0,
    Ninst.pushB256 0, Ninst.pushB256 0,
    Ninst.pushB256 benignCallTarget.toB256, Ninst.pushB256 10000]

def benignCallProgram : Prog :=
  ⟨benignCallStaging +++ (Ninst.call ::: Func.stop), []⟩

def benignCallBytes : Bytes := (Prog.compile benignCallProgram).getD []

def benignCallParentCode : ByteArray :=
  ByteArray.mk benignCallBytes.toArray

theorem benignCallProgram_compiles : benignCallProgram.compiles = true := by
  decide +kernel

theorem benignCallProgram_compile :
    Prog.compile benignCallProgram = some benignCallBytes :=
  Prog.compile_eq_some_getD_of_compiles _ benignCallProgram_compiles

def benignCallChildCode : ByteArray := ByteArray.mk #[0x00]

def benignCallState : State :=
  State.set
    (State.set .empty benignCallParentTarget
      { Acct.nil with code := benignCallParentCode })
    benignCallTarget
    { Acct.nil with code := benignCallChildCode }

/-- A concrete exact pause-shaped call into the compiled benign parent. -/
def benignCallMsg : Msg :=
  { (default : Msg) with
    benv :=
      { (default : Benv) with
        state := benignCallState
        stat :=
          { (default : BenvStat) with
            origState := benignCallState
            time := 10 } }
    caller := benignCircuitBreaker
    target := some benignCallParentTarget
    currentTarget := benignCallParentTarget
    gas := 200000
    value := 0
    data := pauseForCalldata 1
    codeAddress := some benignCallParentTarget
    code := benignCallParentCode
    shouldTransferValue := true
    isStatic := false
    disablePrecompiles := true }

/-- Same-frame continuation steps from message entry to the CALL opcode. -/
inductive BenignCallContPrefix : Evm → Evm → Type
  | refl (evm : Evm) : BenignCallContPrefix evm evm
  | step {source : Evm} {nextPc : Nat} {next : Devm} {target : Evm}
      (head : source.step = .cont nextPc next)
      (tail : BenignCallContPrefix ⟨nextPc, source.sta, next⟩ target) :
      BenignCallContPrefix source target

private def BenignCallContPrefix.run
    {source target : Evm} (trace : BenignCallContPrefix source target)
    {out : Execution} (tail : Exec target.pc target.sta target.dyna out) :
    Exec source.pc source.sta source.dyna out :=
  match trace with
  | .refl _ => tail
  | .step head rest => .cont head (rest.run tail)

private theorem BenignCallContPrefix.rawFrameDescendants_run
    {source target : Evm} (trace : BenignCallContPrefix source target)
    {out : Execution} (tail : Exec target.pc target.sta target.dyna out) :
    Exec.rawFrameDescendants (trace.run tail) =
      Exec.rawFrameDescendants tail := by
  induction trace with
  | refl => rfl
  | step head rest ih =>
      simpa [BenignCallContPrefix.run, Exec.rawFrameDescendants] using ih tail

/-- The first spawned frame reached from one concrete message entry. -/
structure BenignCallSpawn (entry : Evm) where
  callEvm : Evm
  trace : BenignCallContPrefix entry callEvm
  frame : Jaune.Frame
  resume : Resume
  nextPc : Nat
  hstep : callEvm.step = .spawn frame resume nextPc

private def benignCallSpawn? : (fuel : Nat) → (entry : Evm) →
    Option (BenignCallSpawn entry)
  | 0, _ => none
  | fuel + 1, entry =>
      match hstep : entry.step with
      | .halt _ => none
      | .spawn frame resume nextPc =>
          some {
            callEvm := entry
            trace := .refl entry
            frame := frame
            resume := resume
            nextPc := nextPc
            hstep := hstep }
      | .cont nextPc next =>
          match benignCallSpawn? fuel ⟨nextPc, entry.sta, next⟩ with
          | none => none
          | some found =>
              some {
                callEvm := found.callEvm
                trace := .step hstep found.trace
                frame := found.frame
                resume := found.resume
                nextPc := found.nextPc
                hstep := found.hstep }

structure BenignCallFixture where
  rootEvm : Evm
  spawn : BenignCallSpawn rootEvm
  resumed : Devm
  childEvm : Evm
  childOut : Execution
  out : Execution
  settled : Devm
  rootEnter : (Jaune.Frame.ofCall benignCallMsg).enter = .run rootEvm
  henter : spawn.frame.enter = .run childEvm
  childStep : childEvm.step = .halt childOut
  hresume : spawn.resume.run (spawn.frame.settle childOut) = .ok resumed
  nextStep :
    (⟨spawn.nextPc, spawn.callEvm.sta, resumed⟩ : Evm).step = .halt out
  rootSettle :
    (Jaune.Frame.ofCall benignCallMsg).settle out = .ok settled
  rootTarget : rootEvm.sta.currentTarget = benignCallParentTarget
  childTarget : childEvm.sta.currentTarget = benignCallTarget

private def BenignCallFixture.childRun (w : BenignCallFixture) :
    Exec w.childEvm.pc w.childEvm.sta w.childEvm.dyna w.childOut :=
  .halt w.childStep

private def BenignCallFixture.nextRun (w : BenignCallFixture) :
    Exec w.spawn.nextPc w.spawn.callEvm.sta w.resumed w.out :=
  .halt w.nextStep

private def BenignCallFixture.tailRun (w : BenignCallFixture) :
    Exec w.spawn.callEvm.pc w.spawn.callEvm.sta
      w.spawn.callEvm.dyna w.out :=
  .runOk w.spawn.hstep w.henter w.childRun w.hresume w.nextRun

private def BenignCallFixture.run (w : BenignCallFixture) :
    Exec w.rootEvm.pc w.rootEvm.sta w.rootEvm.dyna w.out :=
  w.spawn.trace.run w.tailRun

def BenignCallFixture.slot (w : BenignCallFixture) : Xlot :=
  .some ⟨w.rootEvm, w.out⟩

private def BenignCallFixture.root (w : BenignCallFixture) : Exec.Deriv :=
  ⟨w.rootEvm.pc, w.rootEvm.sta, w.rootEvm.dyna, w.out, w.run⟩

private def BenignCallFixture.childRoot
    (w : BenignCallFixture) : Exec.Deriv :=
  ⟨w.childEvm.pc, w.childEvm.sta, w.childEvm.dyna,
    w.childOut, w.childRun⟩

def benignCallFixture? : Option BenignCallFixture :=
  match rootEnter : (Jaune.Frame.ofCall benignCallMsg).enter with
  | .run rootEvm =>
      match benignCallSpawn? 16 rootEvm with
      | some spawn =>
          match henter : spawn.frame.enter with
          | .run childEvm =>
              match childStep : childEvm.step with
              | .halt childOut =>
                  match hresume :
                      spawn.resume.run (spawn.frame.settle childOut) with
                  | .ok resumed =>
                      match nextStep :
                          (⟨spawn.nextPc, spawn.callEvm.sta, resumed⟩ : Evm).step with
                      | .halt out =>
                          match rootSettle :
                              (Jaune.Frame.ofCall benignCallMsg).settle out with
                          | .ok settled =>
                              if rootTarget : rootEvm.sta.currentTarget =
                                  benignCallParentTarget then
                                if childTarget : childEvm.sta.currentTarget =
                                    benignCallTarget then
                                  some {
                                    rootEvm := rootEvm
                                    spawn := spawn
                                    resumed := resumed
                                    childEvm := childEvm
                                    childOut := childOut
                                    out := out
                                    settled := settled
                                    rootEnter := rootEnter
                                    henter := henter
                                    childStep := childStep
                                    hresume := hresume
                                    nextStep := nextStep
                                    rootSettle := rootSettle
                                    rootTarget := rootTarget
                                    childTarget := childTarget }
                                else none
                              else none
                          | .error _ => none
                      | _ => none
                  | .error _ => none
              | _ => none
          | .done _ => none
      | none => none
  | .done _ => none

/-! The kernel certificate below follows the same concrete execution as the
external evaluator, but names every semantic boundary directly.  In
particular, none of these declarations reflects `benignCallFixture?`. -/

private theorem benignCallCallerBalance :
    benignCallMsg.benv.state.bal benignCallMsg.caller = 0 := by
  change (State.get benignCallState benignCircuitBreaker).bal = 0
  let parentAcct : Acct :=
    { Acct.nil with code := benignCallParentCode }
  let childAcct : Acct :=
    { Acct.nil with code := benignCallChildCode }
  have htarget : State.get benignCallState benignCircuitBreaker =
      State.get (State.set (.empty : State) benignCallParentTarget parentAcct)
        benignCircuitBreaker := by
    unfold benignCallState
    exact State.get_set_ne
      (w := State.set (.empty : State) benignCallParentTarget parentAcct)
      (a := benignCallTarget) (b := benignCircuitBreaker)
      (by decide +kernel) childAcct
  rw [htarget]
  have hparent :
      State.get (State.set (.empty : State) benignCallParentTarget parentAcct)
          benignCircuitBreaker =
        State.get (.empty : State) benignCircuitBreaker := by
    exact State.get_set_ne (w := (.empty : State))
      (a := benignCallParentTarget) (b := benignCircuitBreaker)
      (by decide +kernel) parentAcct
  rw [hparent]
  rfl

private def benignCallEntryMid : State :=
  benignCallMsg.benv.state.setBal benignCallMsg.caller
    (benignCallMsg.benv.state.bal benignCallMsg.caller -
      benignCallMsg.value)

private def benignCallEntryBenv : Benv :=
  (benignCallMsg.benv.withState benignCallEntryMid).addBal
    benignCallMsg.currentTarget benignCallMsg.value

private def benignCallEntryEvm : Evm :=
  initEvm (benignCallMsg.withBenv benignCallEntryBenv)

private theorem benignCallRootEnter :
    (Jaune.Frame.ofCall benignCallMsg).enter = .run benignCallEntryEvm := by
  obtain ⟨stmid, hsub, hbt⟩ :=
    Msg.benvAfterTransfer_of_affordable benignCallMsg rfl (by
      rw [benignCallCallerBalance]
      decide +kernel)
  have expectedSub :
      benignCallMsg.benv.state.subBal benignCallMsg.caller
          benignCallMsg.value =
        some benignCallEntryMid := by
    unfold State.subBal benignCallEntryMid
    rw [benignCallCallerBalance]
    rw [show benignCallMsg.value = 0 by rfl]
    simp only [if_neg (by decide +kernel : ¬ (0 : B256) < 0)]
  rw [expectedSub] at hsub
  cases hsub
  unfold Jaune.Frame.enter Jaune.Frame.ofCall
  simp only
  rw [hbt]
  rfl

private def benignCallContSuccess (evm : Evm) : Bool :=
  match evm.step with
  | .cont _ _ => true
  | _ => false

private def benignCallTakeCont (evm : Evm) : Evm :=
  match evm.step with
  | .cont pc next => ⟨pc, evm.sta, next⟩
  | _ => default

private theorem benignCallStep_takeCont (evm : Evm)
    (success : benignCallContSuccess evm = true) :
    evm.step = .cont (benignCallTakeCont evm).pc
      (benignCallTakeCont evm).dyna := by
  cases h : evm.step with
  | halt _ => simp [benignCallContSuccess, h] at success
  | spawn _ _ _ => simp [benignCallContSuccess, h] at success
  | cont _ _ => simp [benignCallTakeCont, h]

private def benignCallEvm1 := benignCallTakeCont benignCallEntryEvm
private def benignCallEvm2 := benignCallTakeCont benignCallEvm1
private def benignCallEvm3 := benignCallTakeCont benignCallEvm2
private def benignCallEvm4 := benignCallTakeCont benignCallEvm3
private def benignCallEvm5 := benignCallTakeCont benignCallEvm4
private def benignCallEvm6 := benignCallTakeCont benignCallEvm5
private def benignCallEvm7 := benignCallTakeCont benignCallEvm6
private def benignCallEvm8 := benignCallTakeCont benignCallEvm7

private def benignCallEntryTrace :
    BenignCallContPrefix benignCallEntryEvm benignCallEvm8 := by
  exact .step (benignCallStep_takeCont benignCallEntryEvm (by decide +kernel))
    (.step (benignCallStep_takeCont benignCallEvm1 (by decide +kernel))
    (.step (benignCallStep_takeCont benignCallEvm2 (by decide +kernel))
    (.step (benignCallStep_takeCont benignCallEvm3 (by decide +kernel))
    (.step (benignCallStep_takeCont benignCallEvm4 (by decide +kernel))
    (.step (benignCallStep_takeCont benignCallEvm5 (by decide +kernel))
    (.step (benignCallStep_takeCont benignCallEvm6 (by decide +kernel))
    (.step (benignCallStep_takeCont benignCallEvm7 (by decide +kernel))
      (.refl benignCallEvm8))))))))

private theorem benignCallState_childCode :
    benignCallState.getCode benignCallTarget = benignCallChildCode := by
  change (State.get benignCallState benignCallTarget).code = _
  unfold benignCallState
  rw [State.get_set_self]

private theorem benignCallEntry_childCode :
    benignCallEntryEvm.dyna.getCode benignCallTarget =
      benignCallChildCode := by
  change benignCallEntryBenv.state.getCode benignCallTarget = _
  unfold benignCallEntryBenv Benv.addBal Benv.withState benignCallEntryMid
  rw [State.addBal_getCode, State.setBal_getCode]
  exact benignCallState_childCode

private theorem benignCallEvm8_childCode :
    benignCallEvm8.dyna.getCode benignCallTarget =
      benignCallChildCode := by
  change benignCallEntryEvm.dyna.getCode benignCallTarget = _
  exact benignCallEntry_childCode

private def benignCallBase : Devm :=
  benignCallEvm8.dyna.setMach
    ⟨[], benignCallEvm8.dyna.memory, benignCallEvm8.dyna.gasLeft⟩

private def benignCallDelegated : Devm :=
  addAccessedAddress benignCallBase benignCallTarget

private def benignCallExtCost : Nat :=
  benignCallBase.extCost [⟨0, 0⟩, ⟨0, 0⟩]

private def benignCallAccessCost : Nat :=
  accessCost benignCallTarget benignCallBase.accessedAddresses

private def benignCallGasSplit : Nat × Nat :=
  calculateMsgCallGas 0 10000 benignCallDelegated.gasLeft
    benignCallExtCost benignCallAccessCost

private def benignCallMsgCallCost : Nat := benignCallGasSplit.1
private def benignCallMsgCallStipend : Nat := benignCallGasSplit.2

private def benignCallSuspendedParent : Devm :=
  callSpawnParent benignCallDelegated
    (benignCallMsgCallCost + benignCallExtCost) 0 0 0 0

private def benignCallChildMsg : Msg :=
  callSpawnMsg benignCallEvm8.sta benignCallSuspendedParent
    benignCallMsgCallStipend benignCallTarget benignCallTarget 0 0
    benignCallChildCode false

private def benignCallChildFrame : Jaune.Frame :=
  Jaune.Frame.ofCall benignCallChildMsg

private def benignCallResume : Resume :=
  .call benignCallSuspendedParent 0 0

private theorem benignCallAccessCost_eq : benignCallAccessCost = 2600 := by
  unfold benignCallAccessCost accessCost
  rw [if_neg (show benignCallTarget ∉
      benignCallBase.accessedAddresses by
    rw [show benignCallBase.accessedAddresses =
        Std.HashSet.emptyWithCapacity by rfl]
    simp)]
  rfl

private theorem benignCallDelegated_gasLeft :
    benignCallDelegated.gasLeft = 199983 := by
  change benignCallEvm8.dyna.gasLeft = 199983
  rfl

private theorem benignCallExtCost_eq : benignCallExtCost = 0 := by rfl

private theorem benignCallMsgCallCost_eq :
    benignCallMsgCallCost = 12600 := by
  unfold benignCallMsgCallCost benignCallGasSplit
  rw [benignCallAccessCost_eq, benignCallExtCost_eq,
    benignCallDelegated_gasLeft]
  rfl

private theorem benignCallCharge_affordable :
    benignCallMsgCallCost + benignCallExtCost ≤
      benignCallDelegated.gasLeft := by
  rw [benignCallMsgCallCost_eq, benignCallExtCost_eq,
    benignCallDelegated_gasLeft]
  decide +kernel

private theorem benignCallDelegated_childCode :
    benignCallDelegated.getCode benignCallTarget =
      benignCallChildCode := by
  unfold benignCallDelegated benignCallBase
  rw [addAccessedAddress_getCode, Devm.getCode_setMach]
  exact benignCallEvm8_childCode

private theorem benignCallDelegation :
    accessDelegation benignCallDelegated benignCallTarget =
      ⟨false, benignCallTarget, benignCallChildCode, 0,
        benignCallDelegated⟩ := by
  have hnot :
      ¬ isValidDelegation
          (benignCallDelegated.getCode benignCallTarget) := by
    rw [benignCallDelegated_childCode]
    decide +kernel
  simpa [benignCallDelegated_childCode] using
    (accessDelegation_of_not_delegation
      (d := benignCallDelegated) (adr := benignCallTarget) hnot)

private theorem benignCallXstep :
    Xinst.step benignCallEvm8.sta benignCallEvm8.dyna .call =
      .spawn benignCallChildFrame benignCallResume := by
  apply Xinst.step_call_zero_value_spawn
      (gw := 10000) (cw := benignCallTarget.toB256)
      (iiw := 0) (isw := 0) (oiw := 0) (osw := 0) (s := [])
      (ext := benignCallExtCost) (acc := benignCallAccessCost)
      (mcc := benignCallMsgCallCost)
      (mcs := benignCallMsgCallStipend)
      (dp := false) (dadr := benignCallTarget)
      (code := benignCallChildCode) (dgc := 0)
      (d1 := benignCallDelegated)
  · rfl
  · rfl
  · exact benignCallDelegation
  · rfl
  · rfl
  · exact benignCallCharge_affordable
  · decide +kernel

private theorem benignCallSpawnStep :
    benignCallEvm8.step =
      .spawn benignCallChildFrame benignCallResume 13 := by
  unfold Evm.step
  rw [show benignCallEvm8.getInst =
      some (.next (.exec .call)) by rfl]
  simp only
  unfold Ninst.step
  change XStep.toStep
      (benignCallEvm8.pc + (Ninst.exec Xinst.call).size)
      (Xinst.step benignCallEvm8.sta benignCallEvm8.dyna .call) = _
  rw [benignCallXstep]
  rfl

private def benignCallSpawn : BenignCallSpawn benignCallEntryEvm :=
  { callEvm := benignCallEvm8
    trace := benignCallEntryTrace
    frame := benignCallChildFrame
    resume := benignCallResume
    nextPc := 13
    hstep := benignCallSpawnStep }

private def benignCallChildMid : State :=
  benignCallChildMsg.benv.state.setBal benignCallChildMsg.caller
    (benignCallChildMsg.benv.state.bal benignCallChildMsg.caller -
      benignCallChildMsg.value)

private def benignCallChildBenv : Benv :=
  (benignCallChildMsg.benv.withState benignCallChildMid).addBal
    benignCallChildMsg.currentTarget benignCallChildMsg.value

private def benignCallChildEvm : Evm :=
  initEvm (benignCallChildMsg.withBenv benignCallChildBenv)

private def benignCallChildOut : Execution :=
  .ok benignCallChildEvm.dyna

private theorem benignCallNot_lt_zero (x : B256) : ¬ x < 0 := by
  intro h
  have hn := B256.toNat_lt_toNat h
  rw [B256.toNat_zero] at hn
  exact Nat.not_lt_zero _ hn

private theorem benignCallChildEnter :
    benignCallChildFrame.enter = .run benignCallChildEvm := by
  obtain ⟨stmid, hsub, hbt⟩ :=
    Msg.benvAfterTransfer_of_affordable benignCallChildMsg rfl (by
      rw [show benignCallChildMsg.value = 0 by rfl]
      exact benignCallNot_lt_zero _)
  have expectedSub :
      benignCallChildMsg.benv.state.subBal benignCallChildMsg.caller
          benignCallChildMsg.value =
        some benignCallChildMid := by
    unfold State.subBal benignCallChildMid
    rw [show benignCallChildMsg.value = 0 by rfl]
    rw [if_neg (benignCallNot_lt_zero _)]
  rw [expectedSub] at hsub
  cases hsub
  unfold benignCallChildFrame Jaune.Frame.enter Jaune.Frame.ofCall
  simp only
  rw [hbt]
  rfl

private theorem benignCallChildStep :
    benignCallChildEvm.step = .halt benignCallChildOut := by
  rfl

private def benignCallResumed : Devm :=
  match benignCallResume.run
      (benignCallChildFrame.settle benignCallChildOut) with
  | .ok resumed => resumed
  | .error _ => default

private theorem benignCallResumeRun :
    benignCallResume.run
        (benignCallChildFrame.settle benignCallChildOut) =
      .ok benignCallResumed := by
  rfl

private def benignCallParentAfter : Evm :=
  ⟨13, benignCallEvm8.sta, benignCallResumed⟩

private def benignCallOut : Execution :=
  .ok benignCallParentAfter.dyna

private theorem benignCallParentStop :
    benignCallParentAfter.step = .halt benignCallOut := by
  rfl

private def benignCallSettled : Devm :=
  match (Jaune.Frame.ofCall benignCallMsg).settle benignCallOut with
  | .ok settled => settled
  | .error _ => default

private theorem benignCallRootSettle :
    (Jaune.Frame.ofCall benignCallMsg).settle benignCallOut =
      .ok benignCallSettled := by
  rfl

private def benignCallFixture : BenignCallFixture :=
  { rootEvm := benignCallEntryEvm
    spawn := benignCallSpawn
    resumed := benignCallResumed
    childEvm := benignCallChildEvm
    childOut := benignCallChildOut
    out := benignCallOut
    settled := benignCallSettled
    rootEnter := benignCallRootEnter
    henter := benignCallChildEnter
    childStep := benignCallChildStep
    hresume := benignCallResumeRun
    nextStep := benignCallParentStop
    rootSettle := benignCallRootSettle
    rootTarget := by rfl
    childTarget := by rfl }

/-- The closed-world benign outbound-CALL execution is inhabited by a
kernel-checked parent/child/resume certificate; no evaluator result is used. -/
theorem benignCallFixture_nonempty : Nonempty BenignCallFixture :=
  ⟨benignCallFixture⟩

private theorem BenignCallFixture.rawFrameRoots_eq
    (w : BenignCallFixture) :
    Exec.rawFrameRoots w.run = [w.root, w.childRoot] := by
  unfold Exec.rawFrameRoots BenignCallFixture.run
  rw [BenignCallContPrefix.rawFrameDescendants_run]
  simp [BenignCallFixture.root, BenignCallFixture.childRoot,
    BenignCallFixture.tailRun, BenignCallFixture.childRun,
    BenignCallFixture.nextRun, BenignCallFixture.run,
    Exec.rawFrameDescendants]

private theorem BenignCallFixture.has_descendant
    (w : BenignCallFixture) :
    Exec.rawFrameDescendants w.run ≠ [] := by
  unfold BenignCallFixture.run
  rw [BenignCallContPrefix.rawFrameDescendants_run]
  simp [BenignCallFixture.tailRun, BenignCallFixture.childRun,
    BenignCallFixture.nextRun, Exec.rawFrameDescendants]

private theorem benignCallExactCall :
    ExactTargetCall benignCircuitBreaker benignCallParentTarget
      (pauseForCalldata 1) false benignCallMsg := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem benignCallExactInbound :
    ExactPinnedInbound benignCircuitBreaker benignCallParentTarget
      pauseForCalldata isPausedCalldata benignCallMsg :=
  Or.inl ⟨1, benignCallExactCall⟩

private theorem benignCallMessageUsesProgram :
    MessageUsesProgram benignCallMsg benignCallProgram := by
  unfold MessageUsesProgram
  rw [benignCallProgram_compile]
  simp [benignCallMsg, benignCallParentCode, benignCallBytes,
    ByteArray.toList_eq_toList_data]

private theorem BenignCallFixture.executes (w : BenignCallFixture) :
    MessageExecutesProgram benignCallMsg w.slot benignCallProgram := by
  exact ⟨benignCallMessageUsesProgram, w.rootEvm, w.out, rfl, ⟨w.run⟩⟩

private theorem BenignCallFixture.process (w : BenignCallFixture) :
    ProcessMessage benignCallMsg w.slot (.ok w.settled) := by
  have runFrame := RunFrame.of_run
    (f := Jaune.Frame.ofCall benignCallMsg) (raw := w.out) w.rootEnter
  rw [w.rootSettle] at runFrame
  exact runFrame

/-- The retained slot contains at least one actually entered child frame. -/
def TargetInvocationHasDescendant (xl : Xlot) : Prop :=
  match xl with
  | .none => False
  | .some ⟨evm, raw⟩ =>
      ∃ run : Exec evm.pc evm.sta evm.dyna raw,
        Exec.rawFrameDescendants run ≠ []

private theorem BenignCallFixture.slot_has_descendant
    (w : BenignCallFixture) :
    TargetInvocationHasDescendant w.slot := by
  exact ⟨w.run, w.has_descendant⟩

private theorem BenignCallFixture.noRetainedWriteTo
    (w : BenignCallFixture) (key : B256) :
    TargetInvocationNoRetainedWriteTo
      w.slot benignCircuitBreaker key := by
  intro actualRun
  have runEq : actualRun = w.run := Exec.unique _ _
  subst actualRun
  apply Exec.noRetainedWriteTo_of_frame_owners_ne
  intro frameRoot member
  rw [w.rawFrameRoots_eq] at member
  simp at member
  rcases member with rfl | rfl
  · change w.rootEvm.sta.currentTarget ≠ benignCircuitBreaker
    rw [w.rootTarget]
    decide
  · change w.childEvm.sta.currentTarget ≠ benignCircuitBreaker
    rw [w.childTarget]
    decide

/-- One certified fixture yields the complete account/message-level
clause-(iii) control at one slot: exact inbound shape, compiled-program
identity, settlement, a nonempty descendant tree, and semantic protection of
both named CircuitBreaker cells.  This is a closed-world control, not a
universal bundle over arbitrary account states. -/
theorem benignCall_nonchildless_noninterference (w : BenignCallFixture) :
    ExactPinnedInbound benignCircuitBreaker benignCallParentTarget
        pauseForCalldata isPausedCalldata benignCallMsg ∧
      MessageExecutesProgram benignCallMsg w.slot benignCallProgram ∧
      ProcessMessage benignCallMsg w.slot (.ok w.settled) ∧
      TargetInvocationHasDescendant w.slot ∧
      ∀ key ∈
          [countSlot benignCallPauser.toB256, heartbeatIntervalSlot],
        TargetInvocationNoRetainedWriteTo
          w.slot benignCircuitBreaker key := by
  refine ⟨benignCallExactInbound, w.executes, w.process,
    w.slot_has_descendant, ?_⟩
  intro key _member
  exact w.noRetainedWriteTo key

/-- Closed standard-dependency evidence for the full non-childless clause-(iii)
control.  The witness is the concrete kernel certificate above, not the
external evaluator. -/
theorem benignCall_nonchildless_noninterference_closed :
    ∃ w : BenignCallFixture,
      ExactPinnedInbound benignCircuitBreaker benignCallParentTarget
          pauseForCalldata isPausedCalldata benignCallMsg ∧
        MessageExecutesProgram benignCallMsg w.slot benignCallProgram ∧
        ProcessMessage benignCallMsg w.slot (.ok w.settled) ∧
        TargetInvocationHasDescendant w.slot ∧
        ∀ key ∈
            [countSlot benignCallPauser.toB256, heartbeatIntervalSlot],
          TargetInvocationNoRetainedWriteTo
            w.slot benignCircuitBreaker key := by
  obtain ⟨w⟩ := benignCallFixture_nonempty
  exact ⟨w, benignCall_nonchildless_noninterference w⟩

/-! ## Falsifiers -/

/-- A deliberately bad query body returns the non-boolean word `2`. -/
def wrongBoolQuery : Func :=
  Ninst.pushB256 2 ::: returnWord

def wrongBoolProgram : Prog :=
  ⟨stubDispatchLine +++ (stubPause <?> wrongBoolQuery), []⟩

def wrongBoolBytes : Bytes := (Prog.compile wrongBoolProgram).getD []

def wrongBoolCode : ByteArray := ByteArray.mk wrongBoolBytes.toArray

theorem wrongBoolProgram_compiles : wrongBoolProgram.compiles = true := by
  decide +kernel

theorem wrongBoolProgram_compile :
    Prog.compile wrongBoolProgram = some wrongBoolBytes :=
  Prog.compile_eq_some_getD_of_compiles _ wrongBoolProgram_compiles

theorem wrongBoolProgram_pcFree : Prog.pcFree wrongBoolProgram = true := by
  decide

def wrongBoolCircuitBreaker : Adr := 0x300

def wrongBoolPauser : Adr := 0x301

def wrongBoolTarget : Adr := 0x400

def wrongBoolStor : Stor :=
  (Stor.empty : Stor).set pausedUntilSlot 20

def wrongBoolState : State :=
  State.set .empty wrongBoolTarget
    { Acct.nil with stor := wrongBoolStor, code := wrongBoolCode }

/-- An exact static query entered while the wrong-return target is paused. -/
def wrongBoolMsg : Msg :=
  { (default : Msg) with
    benv :=
      { (default : Benv) with
        state := wrongBoolState
        stat :=
          { (default : BenvStat) with
            origState := wrongBoolState
            time := 10 } }
    caller := wrongBoolCircuitBreaker
    target := some wrongBoolTarget
    currentTarget := wrongBoolTarget
    gas := 100000
    value := 0
    data := isPausedCalldata
    codeAddress := some wrongBoolTarget
    code := wrongBoolCode
    shouldTransferValue := true
    isStatic := true
    disablePrecompiles := true }

structure WrongBoolFixture where
  evm : Evm
  rawPost : Devm
  child : Devm
  enter : (Frame.ofCall wrongBoolMsg).enter = .run evm
  rawExec : exec evm = .ok rawPost
  settle : (Frame.ofCall wrongBoolMsg).settle (.ok rawPost) = .ok child
  clean : child.error = none
  output : child.output = (2 : B256).toBytes

def wrongBoolFixture? : Option WrongBoolFixture :=
  match enter : (Frame.ofCall wrongBoolMsg).enter with
  | .run evm =>
      match rawExec : exec evm with
      | .ok rawPost =>
          match settle : (Frame.ofCall wrongBoolMsg).settle (.ok rawPost) with
          | .ok child =>
              if clean : child.error = none then
                if output : child.output = (2 : B256).toBytes then
                  some {
                    evm := evm
                    rawPost := rawPost
                    child := child
                    enter := enter
                    rawExec := rawExec
                    settle := settle
                    clean := clean
                    output := output }
                else none
              else none
          | .error _ => none
      | .error _ => none
  | .done _ => none

private theorem wrongBoolCallerBalance :
    wrongBoolMsg.benv.state.bal wrongBoolMsg.caller = 0 := by
  change (State.get wrongBoolState wrongBoolCircuitBreaker).bal = 0
  have hget : State.get wrongBoolState wrongBoolCircuitBreaker =
      State.get (.empty : State) wrongBoolCircuitBreaker := by
    unfold wrongBoolState
    exact State.get_set_ne (w := (.empty : State))
      (a := wrongBoolTarget) (b := wrongBoolCircuitBreaker)
      (by decide +kernel) _
  rw [hget]
  rfl

private def wrongBoolEntryMid : State :=
  wrongBoolMsg.benv.state.setBal wrongBoolMsg.caller
    (wrongBoolMsg.benv.state.bal wrongBoolMsg.caller - wrongBoolMsg.value)

private def wrongBoolEntryBenv : Benv :=
  (wrongBoolMsg.benv.withState wrongBoolEntryMid).addBal
    wrongBoolMsg.currentTarget wrongBoolMsg.value

private def wrongBoolEntryEvm : Evm :=
  initEvm (wrongBoolMsg.withBenv wrongBoolEntryBenv)

private theorem wrongBoolEntry :
    (Frame.ofCall wrongBoolMsg).enter = .run wrongBoolEntryEvm := by
  obtain ⟨stmid, hsub, hbt⟩ :=
    Msg.benvAfterTransfer_of_affordable wrongBoolMsg rfl (by
      rw [wrongBoolCallerBalance]
      decide +kernel)
  have expectedSub :
      wrongBoolMsg.benv.state.subBal wrongBoolMsg.caller wrongBoolMsg.value =
        some wrongBoolEntryMid := by
    unfold State.subBal wrongBoolEntryMid
    rw [wrongBoolCallerBalance]
    rw [show wrongBoolMsg.value = 0 by rfl]
    simp only [if_neg (by decide +kernel : ¬ (0 : B256) < 0)]
  rw [expectedSub] at hsub
  cases hsub
  unfold Frame.enter Frame.ofCall
  simp only
  rw [hbt]
  rfl

private def wrongBoolRawPost : Devm :=
  match exec wrongBoolEntryEvm with
  | .ok post => post
  | .error _ => default

private theorem wrongBoolExec :
    exec wrongBoolEntryEvm = .ok wrongBoolRawPost := by
  have success : (match exec wrongBoolEntryEvm with
      | .ok _ => true | .error _ => false) = true := by
    decide +kernel
  cases h : exec wrongBoolEntryEvm with
  | error _ =>
      rw [h] at success
      contradiction
  | ok _ =>
      unfold wrongBoolRawPost
      rw [h]

private def wrongBoolChild : Devm :=
  match (Frame.ofCall wrongBoolMsg).settle (.ok wrongBoolRawPost) with
  | .ok child => child
  | .error _ => default

private theorem wrongBoolSettle :
    (Frame.ofCall wrongBoolMsg).settle (.ok wrongBoolRawPost) =
      .ok wrongBoolChild := by
  have success :
      (match (Frame.ofCall wrongBoolMsg).settle (.ok wrongBoolRawPost) with
        | .ok _ => true | .error _ => false) = true := by
    decide +kernel
  cases h : (Frame.ofCall wrongBoolMsg).settle (.ok wrongBoolRawPost) with
  | error _ =>
      rw [h] at success
      contradiction
  | ok _ =>
      unfold wrongBoolChild
      rw [h]

/-- The compiled wrong-return control has a closed standard-dependency witness.
The separate executable Option remains a regression check, not theorem
evidence. -/
theorem wrongBoolFixture_nonempty : Nonempty WrongBoolFixture := by
  exact ⟨{
    evm := wrongBoolEntryEvm
    rawPost := wrongBoolRawPost
    child := wrongBoolChild
    enter := wrongBoolEntry
    rawExec := wrongBoolExec
    settle := wrongBoolSettle
    clean := by decide +kernel
    output := by decide +kernel }⟩

private noncomputable def WrongBoolFixture.run (w : WrongBoolFixture) :
    Exec w.evm.pc w.evm.sta w.evm.dyna (.ok w.rawPost) :=
  Classical.choice ((exec_iff_exec_eq _ _ _ _).mpr w.rawExec)

private theorem wrongBoolExactCall :
    ExactTargetCall wrongBoolCircuitBreaker wrongBoolTarget
      isPausedCalldata true wrongBoolMsg := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem wrongBoolMessageUsesProgram :
    MessageUsesProgram wrongBoolMsg wrongBoolProgram := by
  unfold MessageUsesProgram
  rw [wrongBoolProgram_compile]
  simp [wrongBoolMsg, wrongBoolCode, wrongBoolBytes,
    ByteArray.toList_eq_toList_data]

private theorem wrongBoolMessagePaused :
    PausedAt pausedUntil wrongBoolMsg.benv.state wrongBoolTarget
      wrongBoolMsg.benv.stat.time := by
  simp [PausedAt, pausedUntil, wrongBoolMsg, wrongBoolState, wrongBoolStor,
    State.getStor, State.get_set_self, Stor.set]
  decide +kernel

/-- The compiled wrong-return program has a complete clean message execution
in a paused exact query world, but its settled word is not canonical true. -/
theorem wrongBool_paused_query_execution (w : WrongBoolFixture) :
    ∃ (xl : Xlot) (child : Devm),
      ExactTargetCall wrongBoolCircuitBreaker wrongBoolTarget
        isPausedCalldata true wrongBoolMsg ∧
      MessageExecutesProgram wrongBoolMsg xl wrongBoolProgram ∧
      ProcessMessage wrongBoolMsg xl (.ok child) ∧
      child.error.isSome = false ∧
      PausedAt pausedUntil wrongBoolMsg.benv.state wrongBoolTarget
        wrongBoolMsg.benv.stat.time ∧
      ¬ AcceptedBoolExecution (.ok child) 1 := by
  let xl : Xlot := .some ⟨w.evm, .ok w.rawPost⟩
  have process : ProcessMessage wrongBoolMsg xl (.ok w.child) := by
    have runFrame := RunFrame.of_run (f := Frame.ofCall wrongBoolMsg)
      (raw := (.ok w.rawPost : Execution)) w.enter
    rw [w.settle] at runFrame
    exact runFrame
  have notAccepted : ¬ AcceptedBoolWord w.child 1 := by
    rw [acceptedBoolWord_iff (word := (2 : B256))
      (result := (1 : B256)) w.clean w.output]
    decide
  have settledClean : w.child.error.isSome = false := by
    rw [w.clean]
    rfl
  refine ⟨xl, w.child, wrongBoolExactCall, ?_, process, settledClean,
    wrongBoolMessagePaused, ?_⟩
  · exact ⟨wrongBoolMessageUsesProgram, w.evm, .ok w.rawPost,
      rfl, ⟨w.run⟩⟩
  · rintro ⟨child, childEq, accepted⟩
    cases childEq
    exact notAccepted accepted

/-- Clause (ii) rejects the compiled wrong-return variant on its actual clean
paused query execution. -/
theorem wrongBoolProgram_truthfulness_falsifier (w : WrongBoolFixture) :
    ¬ LidoPinnedPauseTarget wrongBoolCircuitBreaker wrongBoolPauser
      wrongBoolTarget wrongBoolProgram pausedUntil [] := by
  intro bundle
  rcases wrongBool_paused_query_execution w with
    ⟨xl, child, exactCall, executes, process, clean, paused, notAccepted⟩
  have truthful := bundle.isPaused_truthful exactCall executes process
    child rfl clean
  exact notAccepted (truthful.2.1.mpr paused)

/-- The exact acceptance rule rejects the wrong-return variant's word.  This
control also pins that trailing-byte tolerance does not enlarge the accepted
first-word set beyond canonical zero and one. -/
theorem wrongBoolReturnShape_falsifier :
    BoolQueryFailure
      ((default : Devm).withOutput ((2 : B256).toBytes)) := by
  unfold BoolQueryFailure
  constructor
  · rw [acceptedBoolWord_iff (word := (2 : B256))
      (result := (0 : B256)) (by rfl) (by rfl)]
    decide
  · rw [acceptedBoolWord_iff (word := (2 : B256))
      (result := (1 : B256)) (by rfl) (by rfl)]
    decide

/-! ## Distinct-target retained-write falsifier -/

def retainedWriteCircuitBreaker : Adr := 0x600

def retainedWritePauser : Adr := 0x601

def retainedWriteTarget : Adr := 0x700

def retainedWriteKey : B256 := heartbeatIntervalSlot

def retainedWriteChildMain : Func :=
  Ninst.pushB256 1 :::
    Ninst.pushB256 retainedWriteKey :::
      Ninst.sstore ::: Func.stop

def retainedWriteChildProgram : Prog :=
  ⟨retainedWriteChildMain, []⟩

def retainedWriteCallLine : Line :=
  [Ninst.pushB256 0, Ninst.pushB256 0, Ninst.pushB256 0,
    Ninst.pushB256 0, Ninst.pushB256 0,
    Ninst.pushB256 retainedWriteCircuitBreaker.toB256,
    Ninst.pushB256 100000]

def retainedWriteMain : Func :=
  retainedWriteCallLine +++ (Ninst.call ::: Func.stop)

def retainedWriteProgram : Prog :=
  ⟨retainedWriteMain, []⟩

def retainedWriteChildBytes : Bytes :=
  (Prog.compile retainedWriteChildProgram).getD []

def retainedWriteBytes : Bytes :=
  (Prog.compile retainedWriteProgram).getD []

def retainedWriteChildCode : ByteArray :=
  ByteArray.mk retainedWriteChildBytes.toArray

def retainedWriteCode : ByteArray :=
  ByteArray.mk retainedWriteBytes.toArray

theorem retainedWriteChildProgram_compiles :
    retainedWriteChildProgram.compiles = true := by
  decide +kernel

theorem retainedWriteProgram_compiles :
    retainedWriteProgram.compiles = true := by
  decide +kernel

theorem retainedWriteChildProgram_compile :
    Prog.compile retainedWriteChildProgram = some retainedWriteChildBytes :=
  Prog.compile_eq_some_getD_of_compiles _
    retainedWriteChildProgram_compiles

theorem retainedWriteProgram_compile :
    Prog.compile retainedWriteProgram = some retainedWriteBytes :=
  Prog.compile_eq_some_getD_of_compiles _ retainedWriteProgram_compiles

def retainedWriteState : State :=
  State.set
    (State.set .empty retainedWriteTarget
      { Acct.nil with code := retainedWriteCode })
    retainedWriteCircuitBreaker
    { Acct.nil with code := retainedWriteChildCode }

/-- An exact pause-shaped message whose distinct target calls back into the
CircuitBreaker account, where a descendant frame writes the protected cell. -/
def retainedWriteMsg : Msg :=
  { (default : Msg) with
    benv :=
      { (default : Benv) with
        state := retainedWriteState
        stat :=
          { (default : BenvStat) with
            origState := retainedWriteState
            time := 10 } }
    caller := retainedWriteCircuitBreaker
    target := some retainedWriteTarget
    currentTarget := retainedWriteTarget
    gas := 200000
    value := 0
    data := pauseForCalldata 1
    codeAddress := some retainedWriteTarget
    code := retainedWriteCode
    shouldTransferValue := true
    isStatic := false
    disablePrecompiles := true }

structure RetainedWriteFixture where
  rootEvm : Evm
  rootPost : Devm
  settled : Devm
  enter : (Frame.ofCall retainedWriteMsg).enter = .run rootEvm
  rawExec : exec rootEvm = .ok rootPost
  rootClean : rootPost.error = none
  rootTarget : rootEvm.sta.currentTarget = retainedWriteTarget
  rootChanged :
    (Devm.getStor rootEvm.dyna retainedWriteCircuitBreaker).get
        retainedWriteKey ≠
      (Devm.getStor rootPost retainedWriteCircuitBreaker).get
        retainedWriteKey
  settle : (Frame.ofCall retainedWriteMsg).settle (.ok rootPost) = .ok settled
  settledClean : settled.error = none

def retainedWriteFixture? : Option RetainedWriteFixture :=
  match enter : (Frame.ofCall retainedWriteMsg).enter with
  | .run rootEvm =>
      match rawExec : exec rootEvm with
      | .ok rootPost =>
          if rootClean : rootPost.error = none then
            if rootTarget : rootEvm.sta.currentTarget =
                retainedWriteTarget then
              if rootChanged :
                  (Devm.getStor rootEvm.dyna
                      retainedWriteCircuitBreaker).get retainedWriteKey ≠
                    (Devm.getStor rootPost
                      retainedWriteCircuitBreaker).get retainedWriteKey then
                match settle : (Frame.ofCall retainedWriteMsg).settle
                    (.ok rootPost) with
                | .ok settled =>
                    if settledClean : settled.error = none then
                      some {
                        rootEvm := rootEvm
                        rootPost := rootPost
                        settled := settled
                        enter := enter
                        rawExec := rawExec
                        rootClean := rootClean
                        rootTarget := rootTarget
                        rootChanged := rootChanged
                        settle := settle
                        settledClean := settledClean }
                    else none
                | .error _ => none
              else none
            else none
          else none
      | .error _ => none
  | .done _ => none

private noncomputable def RetainedWriteFixture.run
    (w : RetainedWriteFixture) :
    Exec w.rootEvm.pc w.rootEvm.sta w.rootEvm.dyna (.ok w.rootPost) :=
  Classical.choice ((exec_iff_exec_eq _ _ _ _).mpr w.rawExec)

private theorem retainedWriteExactCall :
    ExactTargetCall retainedWriteCircuitBreaker retainedWriteTarget
      (pauseForCalldata 1) false retainedWriteMsg := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem retainedWriteMessageUsesProgram :
    MessageUsesProgram retainedWriteMsg retainedWriteProgram := by
  unfold MessageUsesProgram
  rw [retainedWriteProgram_compile]
  simp [retainedWriteMsg, retainedWriteCode, retainedWriteBytes,
    ByteArray.toList_eq_toList_data]

private theorem RetainedWriteFixture.process (w : RetainedWriteFixture) :
    ProcessMessage retainedWriteMsg
      (.some ⟨w.rootEvm, .ok w.rootPost⟩) (.ok w.settled) := by
  have runFrame := RunFrame.of_run (f := Frame.ofCall retainedWriteMsg)
    (raw := (.ok w.rootPost : Execution)) w.enter
  rw [w.settle] at runFrame
  exact runFrame

private theorem RetainedWriteFixture.notNoRetainedWrite (w :
    RetainedWriteFixture) :
    ¬ Exec.NoRetainedWriteTo w.run retainedWriteCircuitBreaker
      retainedWriteKey := by
  intro noWrite
  have committed : Execution.commits (.ok w.rootPost) = true := by
    simp [Execution.commits, w.rootClean]
  have preserved := Exec.committedCell_eq_of_noRetainedWriteTo w.run
    committed retainedWriteCircuitBreaker retainedWriteKey noWrite
  apply w.rootChanged
  simpa [Execution.committedPost] using preserved.symm

private theorem RetainedWriteFixture.hasDescendant
    (w : RetainedWriteFixture) :
    Exec.rawFrameDescendants w.run ≠ [] := by
  intro childless
  apply w.notNoRetainedWrite
  apply Exec.noRetainedWriteTo_of_frame_owners_ne
  intro frameRoot member
  have roots : Exec.rawFrameRoots w.run =
      [⟨w.rootEvm.pc, w.rootEvm.sta, w.rootEvm.dyna,
        .ok w.rootPost, w.run⟩] := by
    unfold Exec.rawFrameRoots
    rw [childless]
  rw [roots, List.mem_singleton] at member
  subst frameRoot
  change w.rootEvm.sta.currentTarget ≠ retainedWriteCircuitBreaker
  rw [w.rootTarget]
  decide

/-- The distinct target's compiled CALL enters a descendant CircuitBreaker
frame.  Its actual retained closure contains a last successful write to the
protected CircuitBreaker cell, so semantic noninterference is false. -/
theorem retainedWrite_distinctTarget_descendant_falsifier
    (w : RetainedWriteFixture) :
    ∃ (rootEvm : Evm) (rootPost settled : Devm)
        (run : Exec rootEvm.pc rootEvm.sta rootEvm.dyna (.ok rootPost)),
      retainedWriteTarget ≠ retainedWriteCircuitBreaker ∧
      rootEvm.sta.currentTarget = retainedWriteTarget ∧
      some rootEvm.sta.code.toList = Prog.compile retainedWriteProgram ∧
      ExactPinnedInbound retainedWriteCircuitBreaker retainedWriteTarget
        pauseForCalldata isPausedCalldata retainedWriteMsg ∧
      ProcessMessage retainedWriteMsg
        (.some ⟨rootEvm, .ok rootPost⟩) (.ok settled) ∧
      Exec.rawFrameDescendants run ≠ [] ∧
      ¬ Exec.NoRetainedWriteTo run retainedWriteCircuitBreaker
        retainedWriteKey ∧
      ∃ write : Exec.SuccessfulSstoreOccurrence
          (⟨rootEvm.pc, rootEvm.sta, rootEvm.dyna, .ok rootPost, run⟩ :
            Exec.Deriv),
        write.Retained ∧
        write.storageOwner = retainedWriteCircuitBreaker ∧
        write.key = retainedWriteKey ∧
        write.IsLastRetained := by
  have committed : Execution.commits (.ok w.rootPost) = true := by
    simp [Execution.commits, w.rootClean]
  have changed :
      (Devm.getStor w.rootEvm.dyna retainedWriteCircuitBreaker).get
          retainedWriteKey ≠
        (Devm.getStor
          (Execution.committedPost (.ok w.rootPost) committed)
          retainedWriteCircuitBreaker).get retainedWriteKey := by
    simpa [Execution.committedPost] using w.rootChanged
  rcases Exec.exists_lastRetainedSstore_of_getStor_ne w.run committed
      changed with
    ⟨write, retained, owner, key, value, last⟩
  have codeEq : w.rootEvm.sta.code = retainedWriteMsg.code :=
    Frame.enter_run_code w.enter
  have uses : some w.rootEvm.sta.code.toList =
      Prog.compile retainedWriteProgram := by
    rw [codeEq]
    exact retainedWriteMessageUsesProgram
  refine ⟨w.rootEvm, w.rootPost, w.settled, w.run, ?_, w.rootTarget,
    uses, ?_, w.process, w.hasDescendant, w.notNoRetainedWrite,
    write, retained,
    owner, key, last⟩
  · decide
  · exact Or.inl ⟨1, retainedWriteExactCall⟩

/-- Clause (iii) rejects the compiled distinct target because the exact
pause-shaped message's retained slot contains the descendant write above. -/
theorem retainedWriteProgram_noninterference_falsifier
    (w : RetainedWriteFixture) :
    ¬ LidoPinnedPauseTarget retainedWriteCircuitBreaker retainedWritePauser
      retainedWriteTarget retainedWriteProgram pausedUntil [] := by
  intro bundle
  let xl : Xlot := .some ⟨w.rootEvm, .ok w.rootPost⟩
  have executes : MessageExecutesProgram retainedWriteMsg xl
      retainedWriteProgram := by
    exact ⟨retainedWriteMessageUsesProgram, w.rootEvm, .ok w.rootPost,
      rfl, ⟨w.run⟩⟩
  have inbound : ExactPinnedInbound retainedWriteCircuitBreaker
      retainedWriteTarget pauseForCalldata isPausedCalldata
      retainedWriteMsg :=
    Or.inl ⟨1, retainedWriteExactCall⟩
  have claimed := bundle.circuitBreaker_noninterference inbound executes
    w.process retainedWriteKey (by simp [retainedWriteKey])
  unfold TargetInvocationNoRetainedWriteTo at claimed
  exact w.notNoRetainedWrite (claimed w.run)

end Blanc.LidoCircuitBreaker.PinnedTargetControl
