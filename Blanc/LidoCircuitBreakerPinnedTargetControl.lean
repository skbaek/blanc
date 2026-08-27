import Blanc.LidoCircuitBreakerPinnedTarget

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

def pausedUntil (state : Devm) (target : Adr) : B256 :=
  state.getStorVal target pausedUntilSlot

/-- `pauseFor(uint256)`: store `block.timestamp + duration`. -/
def stubPauseLine : Line :=
  arg 0 ++ [Ninst.timestamp, Ninst.add, Ninst.pushB256 pausedUntilSlot,
    Ninst.sstore]

def stubPause : Func := stubPauseLine +++ Func.stop

/-- `isPaused()`: return the canonical word for `timestamp < pausedUntil`. -/
def stubQueryLine : Line :=
  [Ninst.pushB256 pausedUntilSlot, Ninst.sload, Ninst.timestamp, Ninst.lt]

def stubQuery : Func := stubQueryLine +++ returnWord

/-- The control uses the exact inbound calls' distinct ABI lengths: the
36-byte pause call enters the write arm; the four-byte static query enters the
read arm.  This is deliberately smaller than a production selector table. -/
def stubDispatchLine : Line :=
  [Ninst.calldatasize, Ninst.pushB256 36, Ninst.eq]

def stubMain : Func := stubDispatchLine +++ (stubPause <?> stubQuery)

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

private lemma prefix_of_timestamp
    {sevm : Sevm} {pre post : Devm} {xs : Stack}
    (stackPrefix : xs <<+ pre.stack)
    (run : Ninst.Run sevm pre Ninst.timestamp post) :
    sevm.benvStat.time :: xs <<+ post.stack := by
  change Ninst.Run sevm pre (.reg .timestamp) post at run
  rcases of_run_reg run with ⟨pc, instructionRun⟩
  simp only [Rinst.run, Rinst.runCore] at instructionRun
  exact prefix_of_push (Devm.pushBurn_of_pushItem instructionRun) stackPrefix

private lemma mem_reads_self (memory : Mem) :
    Mem.Reads memory memory.data.toList := by
  intro index
  simp

/-- Successful execution of the compiled stub exposes its source main body. -/
private theorem stubMain_run_of_exec
    {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post))
    (uses : FrameUsesProgram sevm stubProgram) :
    ∃ entry : Devm,
      Devm.BurnBy 1 pre entry ∧
      Func.Run [stubMain] sevm entry stubMain post := by
  have compiled := Prog.runCompiled_of_exec sevm pre stubProgram post
    stubProgram_pcFree run uses
  rcases compiled with ⟨entry, entryBurn, body⟩
  refine ⟨entry, entryBurn, ?_⟩
  simpa [stubProgram] using Func.Run.of_runCompiled body

/-- The compiled control implements the bundle's exact pause effect. -/
theorem stub_pauseFor_effect
    {circuitBreaker target : Adr} {sevm : Sevm} {pre post : Devm}
    {duration : B256}
    (frame : ExactTargetFrame circuitBreaker target
      (pauseForCalldata duration) false sevm)
    (uses : FrameUsesProgram sevm stubProgram)
    (run : Exec 0 sevm pre (.ok post)) :
    pausedUntil post target = sevm.benvStat.time + duration := by
  rcases stubMain_run_of_exec run uses with ⟨entry, -, mainRun⟩
  change Func.Run [stubMain] sevm entry
    (stubDispatchLine +++ (stubPause <?> stubQuery)) post at mainRun
  rcases of_run_prepend stubDispatchLine _ mainRun with
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
    contradiction
  · change Func.Run [stubMain] sevm bodyEntry stubPause post at pauseRun
    unfold stubPause at pauseRun
    rcases of_run_prepend stubPauseLine _ pauseRun with
      ⟨afterStore, pauseLineRun, stopRun⟩
    unfold stubPauseLine at pauseLineRun
    rcases of_run_append (arg 0) pauseLineRun with
      ⟨afterArg, argRun, pauseLineRun⟩
    rcases Line.of_run_cons pauseLineRun with
      ⟨afterTime, timeRun, pauseLineRun⟩
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
    have timePrefix : sevm.benvStat.time :: duration :: [] <<+
        afterTime.stack :=
      prefix_of_timestamp argPrefix timeRun
    have sumPrefix : (sevm.benvStat.time + duration) :: [] <<+
        afterAdd.stack :=
      prefix_of_add addRun timePrefix
    have keyPrefix : pausedUntilSlot ::
        (sevm.benvStat.time + duration) :: [] <<+ beforeStore.stack :=
      prefix_of_push (of_run_pushB256 keyRun) sumPrefix
    have effect := sstore_getStor_set storeRun keyPrefix
    rw [frame.currentTarget] at effect
    have stopStor := congrFun
      (Func.of_inv Devm.getStor Devm.getStor (by func_inv) stopRun) target
    unfold pausedUntil Devm.getStorVal
    change (Devm.getStor post target).get pausedUntilSlot =
      sevm.benvStat.time + duration
    rw [← stopStor, effect, Stor.get_set_self]

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
    (frame : ExactTargetFrame circuitBreaker target isPausedCalldata true sevm)
    (uses : FrameUsesProgram sevm stubProgram)
    (memoryWf : Mem.Wf pre.memory)
    (errorClean : pre.error = none)
    (run : Exec 0 sevm pre (.ok post)) :
    (AcceptedBoolWord post 1 ↔
      PausedAt pausedUntil pre target sevm.benvStat.time) ∧
    (¬ PausedAt pausedUntil pre target sevm.benvStat.time →
      AcceptedBoolWord post 0 ∨ BoolQueryFailure post) := by
  rcases stubMain_run_of_exec run uses with
    ⟨entry, entryBurnBy, mainRun⟩
  have entryBurn := Devm.Burn.of_burnBy entryBurnBy
  change Func.Run [stubMain] sevm entry
    (stubDispatchLine +++ (stubPause <?> stubQuery)) post at mainRun
  rcases of_run_prepend stubDispatchLine _ mainRun with
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
  · change Func.Run [stubMain] sevm queryEntry stubQuery post at queryRun
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
        (dispatchStorage.symm.trans (entryBurn.getStor target)))
    rw [frame.currentTarget] at storedEq
    change storedUntil = (Devm.getStor afterKey target).get pausedUntilSlot at storedEq
    rw [storageAtLoad] at storedEq
    change storedUntil = pausedUntil pre target at storedEq
    rw [storedEq] at pausedPrefix
    have fullMemory : pre.memory = beforeReturn.memory :=
      entryBurn.memory.trans (dispatchMemory.trans
        (zeroPop.memory.trans queryMemory))
    have returnMemoryWf : Mem.Wf beforeReturn.memory := by
      rw [← fullMemory]
      exact memoryWf
    rcases of_returnWord pausedPrefix returnMemoryWf returnRun with
      ⟨outputEq, returnError⟩
    have dispatchError : entry.error = branchPre.error :=
      (of_run_calldatasize sizeRun).error.trans
        ((of_run_pushB256 pushRun).error.trans (error_eq_of_eq eqRun))
    have queryError : queryEntry.error = beforeReturn.error :=
      (of_run_pushB256 keyRun).error.trans
        ((error_eq_of_sload loadRun).trans
          ((error_eq_of_timestamp timeRun).trans (error_eq_of_lt ltRun)))
    have preToReturnError : pre.error = beforeReturn.error :=
      entryBurn.error.trans (dispatchError.trans
        (zeroPop.error.trans queryError))
    have postError : post.error = none :=
      returnError.trans (preToReturnError.symm.trans errorClean)
    have acceptedIff (result : B256) :
        AcceptedBoolWord post result ↔
          (sevm.benvStat.time <? pausedUntil pre target) = result :=
      acceptedBoolWord_iff (result := result) postError outputEq
    have wordOneIff :
        (sevm.benvStat.time <? pausedUntil pre target) = 1 ↔
          PausedAt pausedUntil pre target sevm.benvStat.time := by
      unfold PausedAt
      constructor
      · intro wordOne
        by_contra notPaused
        have wordZero :
            (sevm.benvStat.time <? pausedUntil pre target) = 0 := by
          rw [B256.ltCheck, if_neg notPaused]
        rw [wordZero] at wordOne
        contradiction
      · intro paused
        rw [B256.ltCheck, if_pos paused]
    refine ⟨(acceptedIff 1).trans wordOneIff, ?_⟩
    intro notPaused
    left
    apply (acceptedIff 0).mpr
    unfold PausedAt at notPaused
    simp [B256.ltCheck, notPaused]
  · have flagEq : flag = ((36 : B256) =? sevm.data.length.toB256) :=
      (popBurn_pref flagPop flagPrefix).1
    rw [dispatchZero] at flagEq
    exact (flagNonzero flagEq).elim

/-- The call-free compiled stub discharges the complete Lido specialization
of the target protocol.  The empty protected surface is intentional: future
real-target goals choose and prove their own protected selector inventory. -/
theorem stub_lidoPinnedPauseTarget
    (circuitBreaker pauser target : Adr)
    (different : target ≠ circuitBreaker) :
    LidoPinnedPauseTarget circuitBreaker pauser target stubProgram
      pausedUntil [] := by
  refine {
    pauseFor_effect := ?_
    isPaused_truthful := ?_
    circuitBreaker_noninterference := ?_
    protectedSurface_reverts := ?_
  }
  · intro sevm pre post duration frame uses run
    exact stub_pauseFor_effect frame uses run
  · intro sevm pre post frame uses memoryWf errorClean run
    exact stub_isPaused_truthful frame uses memoryWf errorClean run
  · intro sevm pre ex run inbound uses key member
    have currentTarget : sevm.currentTarget = target := by
      rcases inbound with ⟨duration, frame⟩ | frame
      · exact frame.currentTarget
      · exact frame.currentTarget
    have codeAddress : sevm.codeAddress = some target := by
      rcases inbound with ⟨duration, frame⟩ | frame
      · exact frame.codeAddress
      · exact frame.codeAddress
    have invocation :
        (⟨0, sevm, pre, ex, run⟩ : Exec.Deriv).exactInvocation
          stubProgram target target :=
      ⟨rfl, currentTarget, codeAddress, uses⟩
    exact Exec.noRetainedWriteTo_of_sourceSites_no_exec run key invocation
      different stubProgram_sourceSites_no_exec
  · intro sevm pre ex selected currentTarget targetAddress codeAddress
      uses selector member paused run
    simp at member

/-! ## One benign outbound CALL

This second control is deliberately below the source-program protocol.  It is
one concrete driver execution whose parent performs an ordinary CALL to an
inert STOP account and then stops.  It exists only to show that semantic
noninterference admits a genuinely non-childless frame tree. -/

def benignCallTarget : Adr := 0x100

def benignCircuitBreaker : Adr := 0x200

def benignCallParentCode : ByteArray := ByteArray.mk #[0xf1, 0x00]

def benignCallChildCode : ByteArray := ByteArray.mk #[0x00]

def benignCallSevm : Sevm :=
  { (default : Sevm) with code := benignCallParentCode }

def benignCallPre : Devm :=
  let pre := ((default : Devm).withGasLeft 100000).withStack
    [10000, benignCallTarget.toB256, 0, 0, 0, 0, 0]
  pre.withState (pre.state.setCode benignCallTarget benignCallChildCode)

private def benignCallEvm : Evm := ⟨0, benignCallSevm, benignCallPre⟩

private structure BenignCallFixture where
  nextPc : Nat
  resumed : Devm
  frame : Jaune.Frame
  resume : Resume
  childEvm : Evm
  childOut : Execution
  out : Execution
  hstep : benignCallEvm.step = .spawn frame resume nextPc
  henter : frame.enter = .run childEvm
  childStep : childEvm.step = .halt childOut
  hresume : resume.run (frame.settle childOut) = .ok resumed
  nextStep : (⟨nextPc, benignCallSevm, resumed⟩ : Evm).step = .halt out
  childTarget : childEvm.sta.currentTarget = benignCallTarget

private def BenignCallFixture.childRun (w : BenignCallFixture) :
    Exec w.childEvm.pc w.childEvm.sta w.childEvm.dyna w.childOut :=
  .halt w.childStep

private def BenignCallFixture.nextRun (w : BenignCallFixture) :
    Exec w.nextPc benignCallSevm w.resumed w.out :=
  .halt w.nextStep

private def BenignCallFixture.run (w : BenignCallFixture) :
    Exec 0 benignCallSevm benignCallPre w.out :=
  .runOk w.hstep w.henter w.childRun w.hresume w.nextRun

private def BenignCallFixture.root (w : BenignCallFixture) : Exec.Deriv :=
  ⟨0, benignCallSevm, benignCallPre, w.out, w.run⟩

private def BenignCallFixture.childRoot
    (w : BenignCallFixture) : Exec.Deriv :=
  ⟨w.childEvm.pc, w.childEvm.sta, w.childEvm.dyna,
    w.childOut, w.childRun⟩

private def benignCallFixture? : Option BenignCallFixture :=
  match hstep : benignCallEvm.step with
  | .spawn frame resume nextPc =>
      match henter : frame.enter with
      | .run childEvm =>
          match childStep : childEvm.step with
          | .halt childOut =>
              match hresume : resume.run (frame.settle childOut) with
              | .ok resumed =>
                  match nextStep :
                      (⟨nextPc, benignCallSevm, resumed⟩ : Evm).step with
                  | .halt out =>
                      if childTarget :
                          childEvm.sta.currentTarget = benignCallTarget then
                        some {
                          nextPc := nextPc
                          resumed := resumed
                          frame := frame
                          resume := resume
                          childEvm := childEvm
                          childOut := childOut
                          out := out
                          hstep := hstep
                          henter := henter
                          childStep := childStep
                          hresume := hresume
                          nextStep := nextStep
                          childTarget := childTarget }
                      else none
                  | _ => none
              | .error _ => none
          | _ => none
      | .done _ => none
  | _ => none

private theorem benignCallFixture_nonempty :
    Nonempty BenignCallFixture := by
  have available : benignCallFixture?.isSome = true := by
    native_decide
  cases fixture : benignCallFixture? with
  | none => simp [fixture] at available
  | some witness => exact ⟨witness⟩

private theorem BenignCallFixture.rawFrameRoots_eq
    (w : BenignCallFixture) :
    Exec.rawFrameRoots w.run = [w.root, w.childRoot] := by
  simp [BenignCallFixture.run, BenignCallFixture.root,
    BenignCallFixture.childRoot, BenignCallFixture.childRun,
    BenignCallFixture.nextRun, Exec.rawFrameRoots,
    Exec.rawFrameDescendants]

private theorem BenignCallFixture.has_descendant
    (w : BenignCallFixture) :
    Exec.rawFrameDescendants w.run ≠ [] := by
  simp [BenignCallFixture.run, BenignCallFixture.childRun,
    BenignCallFixture.nextRun, Exec.rawFrameDescendants]

/-- A concrete ordinary-CALL execution has a nonempty descendant-frame tree
and still cannot retain a write to any CircuitBreaker cell.  The proof uses
frame storage owners, not childlessness or delegatecall reasoning. -/
theorem benignCall_nonchildless_noninterference :
    ∃ (out : Execution)
        (run : Exec 0 benignCallSevm benignCallPre out),
      Exec.rawFrameDescendants run ≠ [] ∧
      ∀ key, Exec.NoRetainedWriteTo run benignCircuitBreaker key := by
  rcases benignCallFixture_nonempty with ⟨w⟩
  refine ⟨w.out, w.run, w.has_descendant, ?_⟩
  intro key
  apply Exec.noRetainedWriteTo_of_frame_owners_ne
  intro frameRoot member
  rw [w.rawFrameRoots_eq] at member
  simp at member
  rcases member with rfl | rfl
  · change benignCallSevm.currentTarget ≠ benignCircuitBreaker
    decide
  · change w.childEvm.sta.currentTarget ≠ benignCircuitBreaker
    rw [w.childTarget]
    decide

/-! ## Falsifiers -/

/-- A deliberately bad query body returns the non-boolean word `2`. -/
def wrongBoolQuery : Func :=
  Ninst.pushB256 2 ::: returnWord

def wrongBoolProgram : Prog :=
  ⟨stubDispatchLine +++ (stubPause <?> wrongBoolQuery), []⟩

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

/-- If the pause stub is installed at the CircuitBreaker storage owner, its
successful write changes the selected cell whenever the old word differs from
the computed expiry.  Semantic noninterference therefore measurably fails. -/
theorem sameOwner_pause_noninterference_falsifier
    {owner : Adr} {sevm : Sevm} {pre post : Devm} {duration : B256}
    (frame : ExactTargetFrame owner owner (pauseForCalldata duration)
      false sevm)
    (uses : FrameUsesProgram sevm stubProgram)
    (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true)
    (changed : pausedUntil pre owner ≠ sevm.benvStat.time + duration) :
    ¬ Exec.NoRetainedWriteTo run owner pausedUntilSlot := by
  intro noWrite
  have preserved : pausedUntil post owner = pausedUntil pre owner := by
    simpa [pausedUntil, Devm.getStorVal, Devm.getStor,
      Execution.committedPost] using
      (Exec.committedCell_eq_of_noRetainedWriteTo run committed owner
        pausedUntilSlot noWrite)
  have effect : pausedUntil post owner =
      sevm.benvStat.time + duration :=
    stub_pauseFor_effect frame uses run
  exact changed (preserved.symm.trans effect)

/-! ## Toy successful composition -/

/-- The successful exact pause leg of the toy choreography leaves the stub
paused at its committed target boundary and discharges the CircuitBreaker's
two-cell noninterference premise from the call-free compiled source.  The
strict-growth premise is the honest modular-arithmetic condition that excludes
timestamp-plus-duration wraparound; neither conclusion is assumed. -/
theorem stub_successful_pause_composition
    {circuitBreaker pauser target : Adr}
    {parentSevm targetSevm : Sevm} {pre post : Devm}
    {duration : B256}
    (different : target ≠ circuitBreaker)
    (parentOwner : parentSevm.currentTarget = circuitBreaker)
    (parentCaller : parentSevm.caller = pauser)
    (frame : ExactTargetFrame circuitBreaker target
      (pauseForCalldata duration) false targetSevm)
    (uses : FrameUsesProgram targetSevm stubProgram)
    (run : Exec 0 targetSevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true)
    (strictGrowth : targetSevm.benvStat.time <
      targetSevm.benvStat.time + duration) :
    PausedAt pausedUntil post target targetSevm.benvStat.time ∧
      PauseSuccessNoninterference parentSevm pre post := by
  have invocation :
      (⟨0, targetSevm, pre, .ok post, run⟩ : Exec.Deriv).exactInvocation
        stubProgram target target :=
    ⟨rfl, frame.currentTarget, frame.codeAddress, uses⟩
  have preserved (key : B256) :
      post.getStorVal circuitBreaker key =
        pre.getStorVal circuitBreaker key := by
    have noWrite := Exec.noRetainedWriteTo_of_sourceSites_no_exec run key
      invocation different stubProgram_sourceSites_no_exec
    simpa [Devm.getStorVal, Devm.getStor, Execution.committedPost] using
      (Exec.committedCell_eq_of_noRetainedWriteTo run committed
        circuitBreaker key noWrite)
  constructor
  · unfold PausedAt
    rw [stub_pauseFor_effect frame uses run]
    exact strictGrowth
  · unfold PauseSuccessNoninterference
    rw [parentOwner, parentCaller]
    exact ⟨preserved (countSlot pauser.toB256),
      preserved heartbeatIntervalSlot⟩

end Blanc.LidoCircuitBreaker.PinnedTargetControl
