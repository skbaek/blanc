import Blanc.LidoCircuitBreakerPinnedTargetComposition

/-!
# Source walks for the pinned-target control stub

This leaf constructs kernel-checked source executions for the compiled control
stub.  It is deliberately separate from the protocol and composition modules:
the latter state and consume the target interface, while this module supplies
one installed implementation of its external-call seams.
-/

namespace Blanc.LidoCircuitBreaker.PinnedTargetStubWalk

open Jaune
open Jaune.Ninst Blanc.Ninst
open PinnedTargetControl

private lemma withOutput_getStorVal (devm : Devm) (out : Bytes)
    (owner : Adr) (key : B256) :
    (devm.withOutput out).getStorVal owner key = devm.getStorVal owner key :=
  rfl

private lemma memRead_getStorVal (devm : Devm) (index size : Nat)
    (owner : Adr) (key : B256) :
    (devm.memRead index size).2.getStorVal owner key =
      devm.getStorVal owner key := rfl

private lemma withOutput_gasLeft (devm : Devm) (out : Bytes) :
    (devm.withOutput out).gasLeft = devm.gasLeft := rfl

private lemma memRead_gasLeft (devm : Devm) (index size : Nat) :
    (devm.memRead index size).2.gasLeft = devm.gasLeft := rfl

private theorem compact_pause_word_eq_projection (time duration : B256) :
    time * (((pauseInfiniteSentinel =? duration) =? 0)) + duration =
      pauseForProjection time duration := by
  by_cases infinite : duration = pauseInfiniteSentinel
  · subst duration
    have one_ne_zero : (1 : B256) ≠ 0 := by decide
    simp [pauseForProjection, B256.eqCheck, one_ne_zero]
    have mulZero : time * (0 : B256) = 0 := by
      change (time.toNat * 0).toB256 = 0
      rw [Nat.mul_zero]
      rfl
    rw [mulZero]
    rfl
  · have reverse : pauseInfiniteSentinel ≠ duration := Ne.symm infinite
    simp [pauseForProjection, B256.eqCheck, infinite, reverse]
    have mulOne : time * (1 : B256) = time := by
      change (time.toNat * 1).toB256 = time
      rw [Nat.mul_one]
      exact toB256_toNat time
    rw [mulOne]

def stubPausePost (sevm : Sevm) (base : Devm)
    (duration : B256) : Devm :=
  temporalSstorePost sevm
    (addAccessedStorageKey base sevm.currentTarget pausedUntilSlot)
    pausedUntilSlot (pauseForProjection sevm.benvStat.time duration)

lemma stubPausePost_logs (sevm : Sevm) (base : Devm)
    (duration : B256) :
    (stubPausePost sevm base duration).logs = base.logs := rfl

lemma stubPausePost_refundCounter (sevm : Sevm) (base : Devm)
    (duration : B256) :
    (stubPausePost sevm base duration).refundCounter =
      sstoreNewRefundCounter (pauseForProjection sevm.benvStat.time duration)
        (getOrigStorVal sevm sevm.currentTarget pausedUntilSlot)
        (base.getStorVal sevm.currentTarget pausedUntilSlot)
        base.refundCounter := rfl

lemma stubPausePost_accountsToDelete (sevm : Sevm) (base : Devm)
    (duration : B256) :
    (stubPausePost sevm base duration).accountsToDelete =
      base.accountsToDelete := rfl

lemma stubPausePost_accessedAddresses (sevm : Sevm) (base : Devm)
    (duration : B256) :
    (stubPausePost sevm base duration).accessedAddresses =
      base.accessedAddresses := rfl

lemma stubPausePost_accessedStorageKeys (sevm : Sevm) (base : Devm)
    (duration : B256) :
    (stubPausePost sevm base duration).accessedStorageKeys =
      base.accessedStorageKeys.insert
        (sevm.currentTarget, pausedUntilSlot) := rfl

lemma stubPausePost_transientStorage (sevm : Sevm) (base : Devm)
    (duration : B256) :
    (stubPausePost sevm base duration).transientStorage =
      base.transientStorage := rfl

lemma stubPausePost_state (sevm : Sevm) (base : Devm)
    (duration : B256) :
    (stubPausePost sevm base duration).state =
      base.state.setStorVal sevm.currentTarget pausedUntilSlot
        (pauseForProjection sevm.benvStat.time duration) := rfl

/-! ## The write arm -/

/-- The compiled `pauseFor(uint256)` arm executes from a cold paused-until
slot in the row-19 zero-to-nonzero price case.  The SSTORE costs `22100` and
the surrounding source instructions cost `32`. -/
theorem stubPause_cold_runCompiledTo
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (duration : B256) (G : Nat)
    (harg : Sevm.dataWord sevm 4 = duration)
    (hcold : (sevm.currentTarget, pausedUntilSlot) ∉
      base.accessedStorageKeys)
    (hdynamic : sevm.isStatic = false)
    (hcost : gasColdSload + sstoreValueCost
      (getOrigStorVal sevm sevm.currentTarget pausedUntilSlot)
      (base.getStorVal sevm.currentTarget pausedUntilSlot)
      (pauseForProjection sevm.benvStat.time duration) = 22100) :
    ∃ post,
      Func.RunCompiledTo fs sevm
        (base.setMach ⟨[], Mem.empty, G + 22132⟩)
        stubPause (.ok post) ∧
      post.getStorVal sevm.currentTarget pausedUntilSlot =
        pauseForProjection sevm.benvStat.time duration ∧
      post.gasLeft = G ∧
      post.error = base.error ∧
      post.output = base.output ∧
      post.meta = (stubPausePost sevm base duration).meta ∧
      post.world = (stubPausePost sevm base duration).world := by
  unfold stubPause stubPauseLine arg cdl
  apply Exists.intro
  constructor
  · func_run [~~~(0 : B256), pauseInfiniteSentinel =? duration,
      (pauseInfiniteSentinel =? duration) =? 0,
      sevm.benvStat.time * (((pauseInfiniteSentinel =? duration) =? 0)),
      sevm.benvStat.time * (((pauseInfiniteSentinel =? duration) =? 0)) + duration,
      22100]
    case h_val =>
      rw [show (32 * (0 : B256) + 4) = 4 by decide, harg]
      rfl
    all_goals try {
      simp [show (32 * (0 : B256) + 4) = 4 by decide, harg,
        pauseInfiniteSentinel, B256.eqCheck] }
    all_goals try {
      have hcost' := hcost
      rw [← compact_pause_word_eq_projection] at hcost'
      simpa only [Devm.getStorVal_setMach] using hcost' }
    all_goals try {
      simp only [Devm.gasLeft_setMach, gLow]
      omega }
    all_goals try { exact Func.RunCompiledTo.last rfl }
  · refine ⟨?_, ?_, rfl, rfl, ?_, ?_⟩
    · rw [Devm.getStorVal_setMach]
      show (Devm.getStor _ sevm.currentTarget).get pausedUntilSlot = _
      rw [setStorVal_getStor_self, Stor.get_set_self]
      rw [compact_pause_word_eq_projection]
    · simp only [Devm.gasLeft_setMach]
      omega
    · rw [compact_pause_word_eq_projection]
      rfl
    · rw [compact_pause_word_eq_projection]
      rfl

/-! ## The query arm -/

/-- After the successful write arm has warmed `pausedUntilSlot`, the compiled
`isPaused()` arm reads it for the warm charge, returns canonical true, and
preserves the stored word. -/
theorem stubQuery_true_warm_runCompiledTo
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (storedUntil : B256) (G : Nat)
    (hstored : base.getStorVal sevm.currentTarget pausedUntilSlot = storedUntil)
    (hwarm : (sevm.currentTarget, pausedUntilSlot) ∈
      base.accessedStorageKeys)
    (hpaused : sevm.benvStat.time < storedUntil) :
    ∃ post,
      Func.RunCompiledTo fs sevm
        (base.setMach ⟨[], Mem.empty, G + 120⟩)
        stubQuery (.ok post) ∧
      post.output = (1 : B256).toBytes ∧
      post.getStorVal sevm.currentTarget pausedUntilSlot = storedUntil ∧
      post.gasLeft = G ∧
      post.error = base.error ∧
      post.meta = (base.withOutput (1 : B256).toBytes).meta ∧
      post.world = base.world := by
  unfold stubQuery stubQueryLine returnWord mstoreAt returnMemoryRange pushList
  apply Exists.intro
  constructor
  · func_run [1, 3]
    case h_val =>
      rw [Devm.getStorVal_setMach, hstored]
      simp [B256.ltCheck, hpaused]
    case h_ext => exact Devm.extCost_empty_word
    case a =>
      apply Func.runCompiledTo_ret_word (i := 0) (sz := 32) (s := [])
        (e := 0) (G := G) (out := (1 : B256).toBytes)
      · rfl
      · rw [show ((0 : B256)).toNat = 0 by decide,
          show ((32 : B256)).toNat = 32 by decide,
          show ((0 : B256) * 32).toNat = 0 by decide]
        exact Devm.extCost_word_word Mem.size_write_word
      · simp only [Devm.gasLeft_setMach]
        omega
      · rw [show ((0 : B256)).toNat = 0 by decide,
          show ((32 : B256)).toNat = 32 by decide]
        exact Devm.memRead_word_fst
          (by rw [show ((0 : B256) * 32).toNat = 0 by decide]; rfl)
  · refine ⟨rfl, ?_, ?_, rfl, ?_, ?_⟩
    · rw [withOutput_getStorVal, memRead_getStorVal,
        Devm.getStorVal_setMach, Devm.getStorVal_setMach, hstored]
    · rw [withOutput_gasLeft, memRead_gasLeft,
        Devm.gasLeft_setMach]
    · rfl
    · rfl

/-! ## Dispatcher lifts -/

private theorem stubBaseMain_pause_cold_runCompiledTo
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (duration : B256) (G : Nat)
    (hsize : sevm.data.length.toB256 = 36)
    (harg : Sevm.dataWord sevm 4 = duration)
    (hcold : (sevm.currentTarget, pausedUntilSlot) ∉
      base.accessedStorageKeys)
    (hdynamic : sevm.isStatic = false)
    (hcost : gasColdSload + sstoreValueCost
      (getOrigStorVal sevm sevm.currentTarget pausedUntilSlot)
      (base.getStorVal sevm.currentTarget pausedUntilSlot)
      (pauseForProjection sevm.benvStat.time duration) = 22100) :
    ∃ post,
      Func.RunCompiledTo fs sevm
        (base.setMach ⟨[], Mem.empty, G + 22154⟩)
        stubBaseMain (.ok post) ∧
      post.getStorVal sevm.currentTarget pausedUntilSlot =
        pauseForProjection sevm.benvStat.time duration ∧
      post.gasLeft = G ∧
      post.error = base.error ∧
      post.output = base.output ∧
      post.meta = (stubPausePost sevm base duration).meta ∧
      post.world = (stubPausePost sevm base duration).world := by
  obtain ⟨post, body, effect, gas, error, output, hmeta, world⟩ :=
    stubPause_cold_runCompiledTo fs sevm base duration G harg hcold hdynamic
      hcost
  refine ⟨post, ?_, effect, gas, error, output, hmeta, world⟩
  unfold stubBaseMain stubDispatchLine
  func_run (4) [1]
  case h_val => simp [B256.eqCheck, hsize]
  case h_arm =>
    have hg : G + 22154 - 22 = G + 22132 := by omega
    rw [hg]
    exact body

private theorem protected_zero_tail_runCompiledTo
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (guardSelector selector : B256) (M : Mem) (G : Nat) (post : Devm)
    (hne : guardSelector ≠ selector)
    (guardNonzero : guardSelector ≠ 0)
    (body : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], M, G⟩) stubBaseMain (.ok post)) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[selector], M, G + 19⟩)
      (pushB256 guardSelector ::: Ninst.eq :::
        (Func.rev <?> stubBaseMain)) (.ok post) := by
  apply Func.RunCompiledTo.next
  · apply Ninst.runCompiled_pushB256 (c := 3) (G := G + 16)
      (pushCost_of_ne_zero guardNonzero)
    · simp only [Devm.gasLeft_setMach]
    · simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega
  · func_run (2) [0]
    case h_val => simp [B256.eqCheck, hne]
    case h_arm => exact body

private theorem fsig_prepend_runCompiledTo
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (selector : B256) (M : Mem) (G : Nat) (tail : Func) (post : Devm)
    (hselector : Sevm.selector sevm = selector)
    (body : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[selector], M, G⟩) tail (.ok post)) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], M, G + 11⟩) (fsig +++ tail) (.ok post) := by
  unfold fsig cdl shiftRight
  func_run (4) [selector]
  case a => exact body

/-- Lift the cold write-arm certificate through the control stub's two source
dispatchers.  The protected-selector guard takes its zero arm and the exact
36-byte length guard takes its pause arm. -/
theorem stubMain_pause_cold_runCompiledTo
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (duration : B256) (G : Nat)
    (hselector : Sevm.selector sevm = pauseForSelector)
    (hsize : sevm.data.length.toB256 = 36)
    (harg : Sevm.dataWord sevm 4 = duration)
    (hcold : (sevm.currentTarget, pausedUntilSlot) ∉
      base.accessedStorageKeys)
    (hdynamic : sevm.isStatic = false)
    (hcost : gasColdSload + sstoreValueCost
      (getOrigStorVal sevm sevm.currentTarget pausedUntilSlot)
      (base.getStorVal sevm.currentTarget pausedUntilSlot)
      (pauseForProjection sevm.benvStat.time duration) = 22100) :
    ∃ post,
      Func.RunCompiledTo fs sevm
        (base.setMach ⟨[], Mem.empty, G + 22184⟩)
        stubMain (.ok post) ∧
      post.getStorVal sevm.currentTarget pausedUntilSlot =
        pauseForProjection sevm.benvStat.time duration ∧
      post.gasLeft = G ∧
      post.error = base.error ∧
      post.output = base.output ∧
      post.meta = (stubPausePost sevm base duration).meta ∧
      post.world = (stubPausePost sevm base duration).world := by
  obtain ⟨post, body, effect, gas, error, output, hmeta, world⟩ :=
    stubBaseMain_pause_cold_runCompiledTo fs sevm base duration G hsize harg
      hcold hdynamic hcost
  refine ⟨post, ?_, effect, gas, error, output, hmeta, world⟩
  have protectedNe : stubProtectedSelector ≠ pauseForSelector := by
    decide +kernel
  have protectedNonzero : stubProtectedSelector ≠ 0 := by
    decide +kernel
  have tail := protected_zero_tail_runCompiledTo fs sevm base
    stubProtectedSelector pauseForSelector Mem.empty (G + 22154) post
    protectedNe protectedNonzero body
  have head := fsig_prepend_runCompiledTo fs sevm base pauseForSelector
    Mem.empty (G + 22173) _ post hselector tail
  have hg : G + 22173 + 11 = G + 22184 := by omega
  rw [hg] at head
  rw [stubMain, stubProtectedLine, prepend_append]
  exact head

private theorem stubBaseMain_query_true_warm_runCompiledTo
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (storedUntil : B256) (G : Nat)
    (hsize : sevm.data.length.toB256 = 4)
    (hstored : base.getStorVal sevm.currentTarget pausedUntilSlot = storedUntil)
    (hwarm : (sevm.currentTarget, pausedUntilSlot) ∈
      base.accessedStorageKeys)
    (hpaused : sevm.benvStat.time < storedUntil) :
    ∃ post,
      Func.RunCompiledTo fs sevm
        (base.setMach ⟨[], Mem.empty, G + 141⟩)
        stubBaseMain (.ok post) ∧
      post.output = (1 : B256).toBytes ∧
      post.getStorVal sevm.currentTarget pausedUntilSlot = storedUntil ∧
      post.gasLeft = G ∧
      post.error = base.error ∧
      post.meta = (base.withOutput (1 : B256).toBytes).meta ∧
      post.world = base.world := by
  obtain ⟨post, body, output, effect, gas, error, hmeta, world⟩ :=
    stubQuery_true_warm_runCompiledTo fs sevm base storedUntil G hstored hwarm
      hpaused
  refine ⟨post, ?_, output, effect, gas, error, hmeta, world⟩
  unfold stubBaseMain stubDispatchLine
  func_run (4) [0]
  case h_val =>
    rw [hsize]
    decide
  case h_arm =>
    have hg : G + 141 - 21 = G + 120 := by omega
    rw [hg]
    exact body

/-- Lift the warm canonical-true query through both source dispatchers. -/
theorem stubMain_query_true_warm_runCompiledTo
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (storedUntil : B256) (G : Nat)
    (hselector : Sevm.selector sevm = isPausedSelector)
    (hsize : sevm.data.length.toB256 = 4)
    (hstored : base.getStorVal sevm.currentTarget pausedUntilSlot = storedUntil)
    (hwarm : (sevm.currentTarget, pausedUntilSlot) ∈
      base.accessedStorageKeys)
    (hpaused : sevm.benvStat.time < storedUntil) :
    ∃ post,
      Func.RunCompiledTo fs sevm
        (base.setMach ⟨[], Mem.empty, G + 171⟩)
        stubMain (.ok post) ∧
      post.output = (1 : B256).toBytes ∧
      post.getStorVal sevm.currentTarget pausedUntilSlot = storedUntil ∧
      post.gasLeft = G ∧
      post.error = base.error ∧
      post.meta = (base.withOutput (1 : B256).toBytes).meta ∧
      post.world = base.world := by
  obtain ⟨post, body, output, effect, gas, error, hmeta, world⟩ :=
    stubBaseMain_query_true_warm_runCompiledTo fs sevm base storedUntil G hsize
      hstored hwarm hpaused
  refine ⟨post, ?_, output, effect, gas, error, hmeta, world⟩
  have protectedNe : stubProtectedSelector ≠ isPausedSelector := by
    decide +kernel
  have protectedNonzero : stubProtectedSelector ≠ 0 := by
    decide +kernel
  have tail := protected_zero_tail_runCompiledTo fs sevm base
    stubProtectedSelector isPausedSelector Mem.empty (G + 141) post
    protectedNe protectedNonzero body
  have head := fsig_prepend_runCompiledTo fs sevm base isPausedSelector
    Mem.empty (G + 160) _ post hselector tail
  have hg : G + 160 + 11 = G + 171 := by omega
  rw [hg] at head
  rw [stubMain, stubProtectedLine, prepend_append]
  exact head

/-! ## Program-entry lifts -/

/-- The complete compiled stub program on the cold pause calldata route. -/
theorem stubProgram_pause_cold_runCompiledTo
    (sevm : Sevm) (base : Devm) (duration : B256) (G : Nat)
    (hselector : Sevm.selector sevm = pauseForSelector)
    (hsize : sevm.data.length.toB256 = 36)
    (harg : Sevm.dataWord sevm 4 = duration)
    (hcold : (sevm.currentTarget, pausedUntilSlot) ∉
      base.accessedStorageKeys)
    (hdynamic : sevm.isStatic = false)
    (hcost : gasColdSload + sstoreValueCost
      (getOrigStorVal sevm sevm.currentTarget pausedUntilSlot)
      (base.getStorVal sevm.currentTarget pausedUntilSlot)
      (pauseForProjection sevm.benvStat.time duration) = 22100) :
    ∃ post,
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty, G + 22185⟩)
        stubProgram (.ok post) ∧
      post.getStorVal sevm.currentTarget pausedUntilSlot =
        pauseForProjection sevm.benvStat.time duration ∧
      post.gasLeft = G ∧
      post.error = base.error ∧
      post.output = base.output ∧
      post.meta = (stubPausePost sevm base duration).meta ∧
      post.world = (stubPausePost sevm base duration).world := by
  obtain ⟨post, body, effect, gas, error, output, hmeta, world⟩ :=
    stubMain_pause_cold_runCompiledTo [stubMain] sevm base duration G
      hselector hsize harg hcold hdynamic hcost
  refine ⟨post, ?_, effect, gas, error, output, hmeta, world⟩
  apply Prog.runCompiledTo_intro (G := G + 22184)
      (mid := base.setMach ⟨[], Mem.empty, G + 22184⟩)
  · simp only [Devm.gasLeft_setMach, gJumpdest]
  · rfl
  · simpa only [stubProgram] using body

/-- The complete compiled stub program on the warm canonical-true query
route. -/
theorem stubProgram_query_true_warm_runCompiledTo
    (sevm : Sevm) (base : Devm) (storedUntil : B256) (G : Nat)
    (hselector : Sevm.selector sevm = isPausedSelector)
    (hsize : sevm.data.length.toB256 = 4)
    (hstored : base.getStorVal sevm.currentTarget pausedUntilSlot = storedUntil)
    (hwarm : (sevm.currentTarget, pausedUntilSlot) ∈
      base.accessedStorageKeys)
    (hpaused : sevm.benvStat.time < storedUntil) :
    ∃ post,
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty, G + 172⟩)
        stubProgram (.ok post) ∧
      post.output = (1 : B256).toBytes ∧
      post.getStorVal sevm.currentTarget pausedUntilSlot = storedUntil ∧
      post.gasLeft = G ∧
      post.error = base.error ∧
      post.meta = (base.withOutput (1 : B256).toBytes).meta ∧
      post.world = base.world := by
  obtain ⟨post, body, output, effect, gas, error, hmeta, world⟩ :=
    stubMain_query_true_warm_runCompiledTo [stubMain] sevm base storedUntil G
      hselector hsize hstored hwarm hpaused
  refine ⟨post, ?_, output, effect, gas, error, hmeta, world⟩
  apply Prog.runCompiledTo_intro (G := G + 171)
      (mid := base.setMach ⟨[], Mem.empty, G + 171⟩)
  · simp only [Devm.gasLeft_setMach, gJumpdest]
  · rfl
  · simpa only [stubProgram] using body

/-! ## Exact stub calldata views -/

private lemma shiftRight224_of_take4_eq_pause (x : B256)
    (h : x.toBytes.take 4 = [0xf3, 0xf4, 0x49, 0xc7]) :
    x >>> 224 = (0xf3f449c7 : B256) := by
  rcases x with ⟨⟨x3, x2⟩, ⟨x1, x0⟩⟩
  simp [B256.toBytes, B128.toBytes, UInt64.toBytes, UInt32.toBytes,
    UInt16.toBytes, List.take] at h
  change B256.shiftRight (⟨⟨_, _⟩, ⟨_, _⟩⟩ : B256) 224 = _
  simp only [B256.shiftRight]
  change (⟨0, B128.shiftRight ⟨_, _⟩ 96⟩ : B256) = _
  simp only [B128.shiftRight]
  norm_num
  congr 3
  change x3 >>> (32 : UInt64) = (4092873159 : UInt64)
  rcases h with ⟨h0, h1, h2, h3⟩
  have h1' :
      ((x3 >>> 32).toUInt32 >>> 16).toUInt16.toUInt8 = 244 := by
    simpa using h1
  have h2' :
      ((x3 >>> 32).toUInt32.toUInt16 >>> 8).toUInt8 = 73 := by
    simpa using h2
  have h3' : (x3 >>> 32).toUInt32.toUInt16.toUInt8 = 199 := by
    simpa using h3
  have hbytes :
      (x3 >>> 32).toUInt32.toBytes = [243, 244, 73, 199] := by
    simp only [UInt32.toBytes, UInt16.toBytes]
    rw [h0, h1', h2', h3']
    rfl
  have hy32 : (x3 >>> 32).toUInt32 = (4092873159 : UInt32) := by
    have converted := congrArg Bytes.toUInt32 hbytes
    rw [toUInt32_toBytes] at converted
    exact converted
  have hlt : (x3 >>> 32).toNat < 4294967296 := by
    rw [UInt64.toNat_shiftRight]
    change x3.toNat >>> 32 < 4294967296
    rw [Nat.shiftRight_eq_div_pow]
    norm_num
    have hx := UInt64.toNat_lt x3
    omega
  rw [← UInt64.toNat_inj]
  have hyNat := congrArg UInt32.toNat hy32
  simp only [UInt64.toUInt32_toNat, Nat.mod_eq_of_lt hlt] at hyNat
  exact hyNat.trans rfl

private lemma shiftRight224_of_take4_eq_query (x : B256)
    (h : x.toBytes.take 4 = [0xb1, 0x87, 0xbd, 0x26]) :
    x >>> 224 = (0xb187bd26 : B256) := by
  rcases x with ⟨⟨x3, x2⟩, ⟨x1, x0⟩⟩
  simp [B256.toBytes, B128.toBytes, UInt64.toBytes, UInt32.toBytes,
    UInt16.toBytes, List.take] at h
  change B256.shiftRight (⟨⟨_, _⟩, ⟨_, _⟩⟩ : B256) 224 = _
  simp only [B256.shiftRight]
  change (⟨0, B128.shiftRight ⟨_, _⟩ 96⟩ : B256) = _
  simp only [B128.shiftRight]
  norm_num
  congr 3
  change x3 >>> (32 : UInt64) = (2978463014 : UInt64)
  rcases h with ⟨h0, h1, h2, h3⟩
  have h1' :
      ((x3 >>> 32).toUInt32 >>> 16).toUInt16.toUInt8 = 135 := by
    simpa using h1
  have h2' :
      ((x3 >>> 32).toUInt32.toUInt16 >>> 8).toUInt8 = 189 := by
    simpa using h2
  have h3' : (x3 >>> 32).toUInt32.toUInt16.toUInt8 = 38 := by
    simpa using h3
  have hbytes :
      (x3 >>> 32).toUInt32.toBytes = [177, 135, 189, 38] := by
    simp only [UInt32.toBytes, UInt16.toBytes]
    rw [h0, h1', h2', h3']
    rfl
  have hy32 : (x3 >>> 32).toUInt32 = (2978463014 : UInt32) := by
    have converted := congrArg Bytes.toUInt32 hbytes
    rw [toUInt32_toBytes] at converted
    exact converted
  have hlt : (x3 >>> 32).toNat < 4294967296 := by
    rw [UInt64.toNat_shiftRight]
    change x3.toNat >>> 32 < 4294967296
    rw [Nat.shiftRight_eq_div_pow]
    norm_num
    have hx := UInt64.toNat_lt x3
    omega
  rw [← UInt64.toNat_inj]
  have hyNat := congrArg UInt32.toNat hy32
  simp only [UInt64.toUInt32_toNat, Nat.mod_eq_of_lt hlt] at hyNat
  exact hyNat.trans rfl

private theorem pauseForCalldata_facts {sevm : Sevm} {duration : B256}
    (hdata : sevm.data = pauseForCalldata duration) :
    Sevm.selector sevm = pauseForSelector ∧
      sevm.data.length.toB256 = 36 ∧
      Sevm.dataWord sevm 4 = duration := by
  have pauseEq : pauseForSelector = (0xf3f449c7 : B256) := by
    decide +kernel
  have pauseBytes : abiSelectorBytes (0xf3f449c7 : B256) =
      [0xf3, 0xf4, 0x49, 0xc7] := rfl
  constructor
  · unfold Sevm.selector
    let word := sevm.data.sliceD 0 32 0
    have wordLength : word.length = 32 := List.takeD_length _ _ _
    have roundtrip : (Bytes.toB256 word).toBytes = word :=
      Bytes.toBytes_toB256_of_length wordLength
    apply pauseEq.symm ▸ shiftRight224_of_take4_eq_pause
    have firstFour :
        (Bytes.toB256 word).toBytes.take 4 =
          [0xf3, 0xf4, 0x49, 0xc7] := by
      rw [roundtrip]
      unfold word
      rw [hdata, pauseForCalldata, pauseEq, pauseBytes]
      rfl
    exact firstFour
  · constructor
    · rw [hdata]
      simp [pauseForCalldata, abiSelectorBytes_length, B256.length_toBytes]
      decide +kernel
    · apply dataWord_of_append
        (pre := abiSelectorBytes pauseForSelector) (post := [])
      · rw [abiSelectorBytes_length]
        rfl
      · rw [hdata]
        rfl

private theorem isPausedCalldata_facts {sevm : Sevm}
    (hdata : sevm.data = isPausedCalldata) :
    Sevm.selector sevm = isPausedSelector ∧
      sevm.data.length.toB256 = 4 := by
  have queryEq : isPausedSelector = (0xb187bd26 : B256) := by
    decide +kernel
  have queryBytes : abiSelectorBytes (0xb187bd26 : B256) =
      [0xb1, 0x87, 0xbd, 0x26] := rfl
  constructor
  · unfold Sevm.selector
    let word := sevm.data.sliceD 0 32 0
    have wordLength : word.length = 32 := List.takeD_length _ _ _
    have roundtrip : (Bytes.toB256 word).toBytes = word :=
      Bytes.toBytes_toB256_of_length wordLength
    apply queryEq.symm ▸ shiftRight224_of_take4_eq_query
    have firstFour :
        (Bytes.toB256 word).toBytes.take 4 =
          [0xb1, 0x87, 0xbd, 0x26] := by
      rw [roundtrip]
      unfold word
      rw [hdata, isPausedCalldata, queryEq, queryBytes]
      rfl
    exact firstFour
  · rw [hdata]
    simp [isPausedCalldata, abiSelectorBytes_length]
    decide +kernel

private lemma sliceD_split {ξ : Type} (xs : List ξ) (d : ξ) :
    ∀ (a m b : Nat),
      xs.sliceD m (a + b) d =
        xs.sliceD m a d ++ xs.sliceD (m + a) b d := by
  intro a
  induction a with
  | zero => intro m b; simp [List.sliceD, List.takeD]
  | succ a ih =>
    intro m b
    rw [show a + 1 + b = (a + b) + 1 from by omega, List.sliceD_succ,
      ih (m + 1) b, List.sliceD_succ xs m a d,
      show m + (a + 1) = m + 1 + a from by omega]
    rfl

private lemma drop_of_length_append {ξ : Type} (A B : List ξ) (n : Nat)
    (h : A.length = n) : (A ++ B).drop n = B := by
  subst h
  exact List.drop_left

lemma sliceD_stagedCalldata (img : Bytes) (sel dur : B256) :
    (Bytes.writeAt (Bytes.writeAt img 256 (B256.toBytes sel))
        288 (B256.toBytes dur)).sliceD 284 36 0 =
      abiSelectorBytes sel ++ B256.toBytes dur := by
  have hsel : (B256.toBytes sel).length = 32 := B256.length_toBytes sel
  have hdur : (B256.toBytes dur).length = 32 := B256.length_toBytes dur
  have hhigh :
      (Bytes.writeAt (Bytes.writeAt img 256 (B256.toBytes sel))
        288 (B256.toBytes dur)).sliceD 288 32 0 = B256.toBytes dur := by
    have h := Bytes.sliceD_writeAt
      (Bytes.writeAt img 256 (B256.toBytes sel)) (B256.toBytes dur) 288
    rwa [hdur] at h
  have hlow0 :
      (Bytes.writeAt (Bytes.writeAt img 256 (B256.toBytes sel))
        288 (B256.toBytes dur)).sliceD 284 4 0 =
      (Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 284 4 0 :=
    Bytes.sliceD_writeAt_before _ _ 284 4 288 (by omega)
  have hword :
      (Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 256 32 0 =
        B256.toBytes sel := by
    have h := Bytes.sliceD_writeAt img (B256.toBytes sel) 256
    rwa [hsel] at h
  have hinner := sliceD_split
    (Bytes.writeAt img 256 (B256.toBytes sel)) (0 : UInt8) 28 256 4
  simp only [show (28 : Nat) + 4 = 32 from rfl,
    show (256 : Nat) + 28 = 284 from rfl] at hinner
  have hA :
      ((Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 256 28 0).length =
        28 := List.takeD_length _ _ _
  have hlow :
      (Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 284 4 0 =
        abiSelectorBytes sel := by
    have hd : abiSelectorBytes sel =
        ((Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 256 28 0 ++
          (Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 284 4 0).drop
            28 := by
      rw [← hinner, hword]
      rfl
    rw [hd, drop_of_length_append _ _ 28 hA]
  have houter := sliceD_split
    (Bytes.writeAt (Bytes.writeAt img 256 (B256.toBytes sel))
      288 (B256.toBytes dur)) (0 : UInt8) 4 284 32
  simp only [show (4 : Nat) + 32 = 36 from rfl,
    show (284 : Nat) + 4 = 288 from rfl] at houter
  rw [houter, hlow0, hlow, hhigh]

lemma sliceD_stagedSelector (img : Bytes) (sel : B256) :
    (Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 284 4 0 =
      abiSelectorBytes sel := by
  have hsel : (B256.toBytes sel).length = 32 := B256.length_toBytes sel
  have hword :
      (Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 256 32 0 =
        B256.toBytes sel := by
    have h := Bytes.sliceD_writeAt img (B256.toBytes sel) 256
    rwa [hsel] at h
  have hinner := sliceD_split
    (Bytes.writeAt img 256 (B256.toBytes sel)) (0 : UInt8) 28 256 4
  simp only [show (28 : Nat) + 4 = 32 from rfl,
    show (256 : Nat) + 28 = 284 from rfl] at hinner
  have hA :
      ((Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 256 28 0).length =
        28 := List.takeD_length _ _ _
  have hd : abiSelectorBytes sel =
      ((Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 256 28 0 ++
        (Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 284 4 0).drop
          28 := by
    rw [← hinner, hword]
    rfl
  rw [hd, drop_of_length_append _ _ 28 hA]

/-! ## Total executions of the installed stub -/

/-- A message carrying the installed stub and exact `pauseFor(uint256)`
calldata executes the cold write route with the source-level charge exported
above. -/
theorem stubPause_exec (m : Msg) (duration : B256) (G : Nat)
    (hcode : m.code = stubCode)
    (hdata : m.data = pauseForCalldata duration)
    (hgas : m.gas = G + 22185)
    (hcold : ((initSevm m).currentTarget, pausedUntilSlot) ∉
      (initDevm m).accessedStorageKeys)
    (hdynamic : (initSevm m).isStatic = false)
    (hcost : gasColdSload + sstoreValueCost
      (getOrigStorVal (initSevm m) (initSevm m).currentTarget
        pausedUntilSlot)
      ((initDevm m).getStorVal (initSevm m).currentTarget pausedUntilSlot)
      (pauseForProjection (initSevm m).benvStat.time duration) = 22100) :
    ∃ post,
      exec (initEvm m) = .ok post ∧
      post.error = none ∧
      post.output = [] ∧
      post.gasLeft = G ∧
      post.meta =
        (stubPausePost (initSevm m) (initDevm m) duration).meta ∧
      post.world = (stubPausePost (initSevm m) (initDevm m) duration).world ∧
      post.getStorVal (initSevm m).currentTarget pausedUntilSlot =
        pauseForProjection (initSevm m).benvStat.time duration := by
  have hdata' : (initSevm m).data = pauseForCalldata duration := hdata
  obtain ⟨hselector, hsize, harg⟩ := pauseForCalldata_facts hdata'
  obtain ⟨post, walk, effect, gas, error, output, hmeta, world⟩ :=
    stubProgram_pause_cold_runCompiledTo (initSevm m) (initDevm m)
      duration G hselector hsize harg hcold hdynamic hcost
  have hrun : Prog.RunCompiledTo (initSevm m) (initDevm m) stubProgram
      (.ok post) := by
    have hbase : (initDevm m).setMach
        ⟨[], Mem.empty, G + 22185⟩ = initDevm m := by
      rw [← hgas]
      rfl
    rw [hbase] at walk
    exact walk
  have hcompile : some (initSevm m).code.toList =
      Prog.compile stubProgram := by
    show some m.code.toList = _
    rw [hcode, stubProgram_compile]
    simp [stubCode, stubBytes, ByteArray.toList_eq_toList_data]
  refine ⟨post, Prog.exec_of_runCompiledTo hrun hcompile, ?_, ?_, gas,
    hmeta, world, effect⟩
  · rw [error]
    rfl
  · rw [output]
    rfl

/-! ## Concrete sentinel execution -/

def stubPauseSentinelTarget : Adr := 0x123

def stubPauseSentinelState : State :=
  State.set (.empty : State) stubPauseSentinelTarget
    {Acct.nil with code := stubCode}

def stubPauseSentinelMsg : Msg :=
  { (default : Msg) with
    benv :=
      { (default : Benv) with
        state := stubPauseSentinelState
        stat :=
          { (default : BenvStat) with
            origState := stubPauseSentinelState
            time := 7 } }
    caller := 1
    target := some stubPauseSentinelTarget
    currentTarget := stubPauseSentinelTarget
    gas := 22185
    value := 0
    data := pauseForCalldata pauseInfiniteSentinel
    codeAddress := some stubPauseSentinelTarget
    code := stubCode
    isStatic := false
    disablePrecompiles := true }

/-- The actual compiled stub preserves the all-ones duration at a nonzero
timestamp, so the result differs from the wrapping timestamp-plus-duration
expression. -/
theorem stubPause_sentinel_execution :
    ∃ post,
      exec (initEvm stubPauseSentinelMsg) = .ok post ∧
      post.getStorVal stubPauseSentinelTarget pausedUntilSlot =
        pauseInfiniteSentinel ∧
      post.getStorVal stubPauseSentinelTarget pausedUntilSlot ≠
        (7 : B256) + pauseInfiniteSentinel := by
  obtain ⟨post, hexec, herr, hout, hgas, hmeta, hworld, hstored⟩ :=
    stubPause_exec stubPauseSentinelMsg pauseInfiniteSentinel 0
      rfl rfl rfl (by
        change (stubPauseSentinelTarget, pausedUntilSlot) ∉
          (Std.HashSet.emptyWithCapacity : KeySet)
        exact Std.HashSet.not_mem_emptyWithCapacity) rfl (by
        have h_orig :
            getOrigStorVal (initSevm stubPauseSentinelMsg)
              (initSevm stubPauseSentinelMsg).currentTarget
              pausedUntilSlot = 0 := by
          change (State.get stubPauseSentinelState stubPauseSentinelTarget).stor.get
            pausedUntilSlot = 0
          rw [stubPauseSentinelState, State.get_set_self]
          rfl
        have h_cur :
            (initDevm stubPauseSentinelMsg).getStorVal
              (initSevm stubPauseSentinelMsg).currentTarget
              pausedUntilSlot = 0 := by
          change (State.get stubPauseSentinelState stubPauseSentinelTarget).stor.get
            pausedUntilSlot = 0
          rw [stubPauseSentinelState, State.get_set_self]
          rfl
        rw [h_orig, h_cur, pauseForProjection]
        have hmax : (0 : B256) ≠ B256.max := by
          decide +kernel
        simp [pauseInfiniteSentinel, sstoreValueCost, gasStorageSet,
          gasColdSload, hmax])
  refine ⟨post, hexec, ?_, ?_⟩
  · simpa [stubPauseSentinelMsg, initSevm, pauseForProjection] using hstored
  · rw [show post.getStorVal stubPauseSentinelTarget pausedUntilSlot =
      pauseInfiniteSentinel by
        simpa [stubPauseSentinelMsg, initSevm, pauseForProjection] using hstored]
    decide +kernel

/-- A message carrying the installed stub and exact `isPaused()` calldata
executes the warm canonical-true query route. -/
theorem stubQuery_exec (m : Msg) (storedUntil : B256) (G : Nat)
    (hcode : m.code = stubCode)
    (hdata : m.data = isPausedCalldata)
    (hgas : m.gas = G + 172)
    (hstored : (initDevm m).getStorVal (initSevm m).currentTarget
      pausedUntilSlot = storedUntil)
    (hwarm : ((initSevm m).currentTarget, pausedUntilSlot) ∈
      (initDevm m).accessedStorageKeys)
    (hpaused : (initSevm m).benvStat.time < storedUntil) :
    ∃ post,
      exec (initEvm m) = .ok post ∧
      post.error = none ∧
      post.output = (1 : B256).toBytes ∧
      post.gasLeft = G ∧
      post.meta =
        ((initDevm m).withOutput (1 : B256).toBytes).meta ∧
      post.world = (initDevm m).world ∧
      post.getStorVal (initSevm m).currentTarget pausedUntilSlot =
        storedUntil := by
  have hdata' : (initSevm m).data = isPausedCalldata := hdata
  obtain ⟨hselector, hsize⟩ := isPausedCalldata_facts hdata'
  obtain ⟨post, walk, output, effect, gas, error, hmeta, world⟩ :=
    stubProgram_query_true_warm_runCompiledTo (initSevm m) (initDevm m)
      storedUntil G hselector hsize hstored hwarm hpaused
  have hrun : Prog.RunCompiledTo (initSevm m) (initDevm m) stubProgram
      (.ok post) := by
    have hbase : (initDevm m).setMach
        ⟨[], Mem.empty, G + 172⟩ = initDevm m := by
      rw [← hgas]
      rfl
    rw [hbase] at walk
    exact walk
  have hcompile : some (initSevm m).code.toList =
      Prog.compile stubProgram := by
    show some m.code.toList = _
    rw [hcode, stubProgram_compile]
    simp [stubCode, stubBytes, ByteArray.toList_eq_toList_data]
  refine ⟨post, Prog.exec_of_runCompiledTo hrun hcompile, ?_, output, gas,
    hmeta, world, effect⟩
  rw [error]
  rfl

end Blanc.LidoCircuitBreaker.PinnedTargetStubWalk
