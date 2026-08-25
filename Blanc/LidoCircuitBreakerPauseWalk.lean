import Blanc.LidoCircuitBreakerRegistrySubstrate

/-!
The `.ok`-flavour walk legs of a successful `pause(address)`.

`Blanc/LidoCircuitBreakerRegistry.lean` carries the same route in reverting
flavour, as a `Func.RunCompiledTo … (.error (.revert, raw))` ladder whose
purpose is a source-path predicate.  This leaf carries the successful
counterpart in the continuation-passing style the register-side substrate uses:
each leg reserves an exact charge, threads the world it changes, and takes the
next leg as a hypothesis.

The legs stop at two boundaries and cross neither.  The body ends at the
internal `.call setPauserSlot` burn, handing the shared Registry kernel a
generic continuation, and the `finishSetPauser` arm ends at the
`.call pauseAfterSetSlot` burn.  Everything between them — the kernel, the
append/remove arms — is the register-side substrate's, and nothing here
consumes it.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune
open Jaune.Ninst Blanc.Ninst

/-! ## The staged pause image -/

/-- The five scratch words `pause` stages before entering the Registry kernel,
in the order the source writes them: the pause duration first — the only write
that extends memory — then the target, the two zero words and the continuation
selector `1`. -/
def pauseMemory (target duration : B256) : Mem :=
  ((((Mem.empty.write (durationWord * 32).toNat duration.toBytes).write
      (targetWord * 32).toNat target.toBytes).write
      (newPauserWord * 32).toNat (0 : B256).toBytes).write
      (previousPauserWord * 32).toNat (0 : B256).toBytes).write
      (continuationWord * 32).toNat (1 : B256).toBytes

/-- The byte image of `pauseMemory`. -/
def pauseImage (target duration : B256) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt
          (Bytes.writeAt [] (durationWord * 32).toNat duration.toBytes)
          (targetWord * 32).toNat target.toBytes)
        (newPauserWord * 32).toNat (0 : B256).toBytes)
      (previousPauserWord * 32).toNat (0 : B256).toBytes)
    (continuationWord * 32).toNat (1 : B256).toBytes

/-- Everything a consumer of the staged pause image needs: well-formedness, the
image it reads, its exact size, and the five staged words.  The size is `768`
rather than the register side's `640` because `durationWord` sits two words
past `continuationWord`; `640 ≤ 768` and `768 % 32 = 0` are stated here so a
consumer written against the register-side window premises can use them
directly. -/
theorem pauseMemory_spec (target duration : B256) :
    let M := pauseMemory target duration
    let img := pauseImage target duration
    Mem.Wf M ∧ Mem.Reads M img ∧ M.size = 768 ∧
      640 ≤ M.size ∧ M.size % 32 = 0 ∧
      Bytes.toB256 (img.sliceD (targetWord * 32).toNat 32 0) = target ∧
      Bytes.toB256 (img.sliceD (newPauserWord * 32).toNat 32 0) = 0 ∧
      Bytes.toB256 (img.sliceD (previousPauserWord * 32).toNat 32 0) = 0 ∧
      Bytes.toB256 (img.sliceD (continuationWord * 32).toNat 32 0) = 1 ∧
      Bytes.toB256 (img.sliceD (durationWord * 32).toNat 32 0) = duration := by
  let M0 := Mem.empty
  let img0 : Bytes := []
  let M1 := M0.write (durationWord * 32).toNat duration.toBytes
  let img1 := Bytes.writeAt img0 (durationWord * 32).toNat duration.toBytes
  let M2 := M1.write (targetWord * 32).toNat target.toBytes
  let img2 := Bytes.writeAt img1 (targetWord * 32).toNat target.toBytes
  let M3 := M2.write (newPauserWord * 32).toNat (0 : B256).toBytes
  let img3 := Bytes.writeAt img2 (newPauserWord * 32).toNat (0 : B256).toBytes
  let M4 := M3.write (previousPauserWord * 32).toNat (0 : B256).toBytes
  let img4 := Bytes.writeAt img3 (previousPauserWord * 32).toNat
    (0 : B256).toBytes
  let M5 := M4.write (continuationWord * 32).toNat (1 : B256).toBytes
  let img5 := Bytes.writeAt img4 (continuationWord * 32).toNat
    (1 : B256).toBytes
  have hwf0 : Mem.Wf M0 := Mem.wf_empty
  have hreads0 : Mem.Reads M0 img0 := Mem.reads_empty
  have hwf1 : Mem.Wf M1 := hwf0.write _ _
  have hreads1 : Mem.Reads M1 img1 := Mem.Reads.write hwf0 hreads0 _ _
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hreads2 : Mem.Reads M2 img2 := Mem.Reads.write hwf1 hreads1 _ _
  have hwf3 : Mem.Wf M3 := hwf2.write _ _
  have hreads3 : Mem.Reads M3 img3 := Mem.Reads.write hwf2 hreads2 _ _
  have hwf4 : Mem.Wf M4 := hwf3.write _ _
  have hreads4 : Mem.Reads M4 img4 := Mem.Reads.write hwf3 hreads3 _ _
  have hwf5 : Mem.Wf M5 := hwf4.write _ _
  have hreads5 : Mem.Reads M5 img5 := Mem.Reads.write hwf4 hreads4 _ _
  have hsize1 : M1.size = 768 := by
    dsimp only [M1, M0]
    rw [Mem.size_write_word_at]
    decide +kernel
  have hsize2 : M2.size = 768 := by
    dsimp only [M2]
    rw [Mem.size_write_word_at, hsize1]
    decide +kernel
  have hsize3 : M3.size = 768 := by
    dsimp only [M3]
    rw [Mem.size_write_word_at, hsize2]
    decide +kernel
  have hsize4 : M4.size = 768 := by
    dsimp only [M4]
    rw [Mem.size_write_word_at, hsize3]
    decide +kernel
  have hsize5 : M5.size = 768 := by
    dsimp only [M5]
    rw [Mem.size_write_word_at, hsize4]
    decide +kernel
  have sliceAt (bs : Bytes) (word value : B256) :
      Bytes.toB256
          ((Bytes.writeAt bs (word * 32).toNat value.toBytes).sliceD
            (word * 32).toNat 32 0) = value := by
    rw [show 32 = value.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have htarget5 : Bytes.toB256
      (img5.sliceD (targetWord * 32).toNat 32 0) = target := by
    dsimp only [img5]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    dsimp only [img4]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    dsimp only [img3]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact sliceAt img1 targetWord target
  have hnew5 : Bytes.toB256
      (img5.sliceD (newPauserWord * 32).toNat 32 0) = 0 := by
    dsimp only [img5]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    dsimp only [img4]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact sliceAt img2 newPauserWord 0
  have hprevious5 : Bytes.toB256
      (img5.sliceD (previousPauserWord * 32).toNat 32 0) = 0 := by
    dsimp only [img5]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact sliceAt img3 previousPauserWord 0
  have hcontinuation5 : Bytes.toB256
      (img5.sliceD (continuationWord * 32).toNat 32 0) = 1 :=
    sliceAt img4 continuationWord 1
  have hduration5 : Bytes.toB256
      (img5.sliceD (durationWord * 32).toNat 32 0) = duration := by
    dsimp only [img5]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
    dsimp only [img4]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
    dsimp only [img3]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
    dsimp only [img2]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
    exact sliceAt img0 durationWord duration
  have hlow5 : 640 ≤ M5.size := by omega
  have halign5 : M5.size % 32 = 0 := by omega
  dsimp only [pauseMemory, pauseImage]
  exact ⟨hwf5, hreads5, hsize5, hlow5, halign5,
    htarget5, hnew5, hprevious5, hcontinuation5, hduration5⟩

/-- The staged pause image is wide enough that every register-side window
premise stated as a `max` against a smaller anchor collapses to `768`.  The
`removeTarget` walks anchor at `672` and `704`; `pauseAfterSet` at `736`. -/
theorem pauseMemory_size_max (target duration : B256) (n : Nat)
    (h : n ≤ 768) : max (pauseMemory target duration).size n = 768 := by
  rcases pauseMemory_spec target duration with ⟨-, -, hsize, -⟩
  omega

/-! ## Transient-storage steps

`Blanc/Forward.lean`'s walk has no rule for `TLOAD` or `TSTORE`, so the two
reentrancy-lock instructions are stepped by hand.  These are the `.ok`-flavour
transcriptions of the reverting ladder's phase-preserving prepends. -/

/-- The reentrancy lock, taken.  Only transient storage changes. -/
def pauseLockPost (sevm : Sevm) (base : Devm) : Devm :=
  base.setTransVal sevm.currentTarget lockKey 1

theorem setTransVal_setMach {devm : Devm} {adr : Adr} {key value : B256}
    {mach : Mach} :
    (devm.setMach mach).setTransVal adr key value =
      (devm.setTransVal adr key value).setMach mach := rfl

theorem transientStorage_setMach {devm : Devm} {mach : Mach} :
    (devm.setMach mach).transientStorage = devm.transientStorage := rfl

/-- Exact `TLOAD` step: the key is popped, the transient value pushed, and
`gasWarmAccess` burned.  Transient reads have no cold arm. -/
theorem runCompiled_tload_of
    {sevm : Sevm} {pre : Devm} {key value : B256}
    {stack : List B256} {G : Nat}
    (hstack : pre.stack = key :: stack)
    (hvalue : pre.getTransVal sevm.currentTarget key = value)
    (hgas : pre.gasLeft = G + gasWarmAccess)
    (hroom : stack.length < 1024) :
    Ninst.RunCompiled sevm pre Ninst.tload
      (pre.setMach ⟨value :: stack, pre.memory, G⟩) := by
  refine Ninst.runCompiled_reg (by rintro ⟨⟩) ?_
  show (do
    let ⟨k, d⟩ ← pre.pop
    pushItem (d.getTransVal sevm.currentTarget k) gasWarmAccess d) = _
  rw [Devm.pop_eq_ok hstack]
  simp only [bind, Except.bind]
  rw [show (pre.setMach
    ⟨stack, pre.memory, pre.gasLeft⟩).getTransVal
      sevm.currentTarget key = value by exact hvalue]
  rw [pushItem_eq_ok (by
    simp only [Devm.gasLeft_setMach]
    omega) (by
    simp only [Devm.stack_setMach]
    exact hroom)]
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [show pre.gasLeft - gasWarmAccess = G by omega]

/-- Exact `TSTORE` step: the machine pops the key first, then the value. -/
theorem runCompiled_tstore_of
    {sevm : Sevm} {pre : Devm} {key value : B256}
    {stack : List B256} {G : Nat}
    (hstack : pre.stack = key :: value :: stack)
    (hstatic : sevm.isStatic = false)
    (hgas : pre.gasLeft = G + gasWarmAccess) :
    Ninst.RunCompiled sevm pre Ninst.tstore
      ((pre.setMach ⟨stack, pre.memory, G⟩).setTransVal
        sevm.currentTarget key value) := by
  refine Ninst.runCompiled_reg (by rintro ⟨⟩) ?_
  show (do
    let ⟨k, d⟩ ← pre.pop
    let ⟨v, d⟩ ← d.pop
    let d ← chargeGas gasWarmAccess d
    assertDynamic sevm d
    .ok (d.setTransVal sevm.currentTarget k v)) = _
  rw [Devm.pop_eq_ok hstack]
  simp only [bind, Except.bind]
  rw [Devm.pop_eq_ok
    (devm := pre.setMach ⟨value :: stack, pre.memory, pre.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [chargeGas_eq_ok
    (devm := pre.setMach ⟨stack, pre.memory, pre.gasLeft⟩) (by
      simp only [Devm.gasLeft_setMach]
      omega)]
  have hremaining : pre.gasLeft - gasWarmAccess = G := by omega
  simp only [Devm.setMach_setMach,
    Devm.stack_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [hremaining]
  simp [assertDynamic, Except.assert, hstatic]

/-! ## Dispatcher reserve -/

/-- Exact generated-runtime dispatcher reserve for `pause(address)`.

`pause` is the first entry of the dispatcher's *third* linear group, so its
path is two hybrid pivots rather than the register side's one: the outer pivot
compares equal to the third group's own first selector and takes its right
half, and the inner fourth-group pivot is greater and takes the third group.

`26` for the entry guard, `11` for selector extraction, `45` for the two
pivots, `25` for the group's first — and matching — comparison and its `POP`,
plus the program's entry `JUMPDEST`. -/
def pauseDispatchGas : Nat := 108

set_option maxRecDepth 670 in
theorem pause_dispatch_runCompiledTo
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (bodyGas G : Nat) (out : Execution)
    (hdata : sevm.data.length = 36)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = selector "pause" [.address])
    (_hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hbody : Func.RunCompiledTo (runtimeMain dp :: aux) sevm
      (base.setMach ⟨[], Mem.empty, G + bodyGas⟩) pause out) :
    Prog.RunCompiledTo sevm
      (base.setMach ⟨[], Mem.empty, G + pauseDispatchGas + bodyGas⟩)
      (runtime dp) out ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  refine ⟨?_, ?_⟩
  · refine Prog.runCompiledTo_intro
      (mid := base.setMach ⟨[], Mem.empty, G + 107 + bodyGas⟩)
      (G := G + 107 + bodyGas) ?_ ?_ ?_
    · simp only [Devm.gasLeft_setMach, pauseDispatchGas, gJumpdest]
      omega
    · rfl
    · have hvalueZero : B256.eqCheck sevm.value 0 = 1 := by
        simp [B256.eqCheck, hvalue]
      have hlt : sevm.data.length.toB256 <? 4 = 0 := by
        rw [hdata]
        decide +kernel
      have hor : B256.or 0 sevm.value = 0 := by
        rw [hvalue]
        decide +kernel
      have hselector' :
          Sevm.dataWord sevm 0 >>> B256.toNat 224 =
            selector "pause" [.address] := hselector
      unfold runtime runtimeMain hybridDispatchWith splitDispatch
        linearDispatchWith firstSelector funcs
      simp only [List.take, List.drop, List.head?, Option.map, Option.getD]
      func_run (23) [0, 0, selector "pause" [.address], 0, 1, 1]
      case a =>
        have hboundary : G + 107 + bodyGas - 107 = G + bodyGas := by
          omega
        simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach, Devm.gasLeft_setMach, hboundary,
          runtimeMain, hybridDispatchWith, splitDispatch, firstSelector, funcs,
          List.take, List.drop, List.head?, Option.map, Option.getD,
          linearDispatchWith] using hbody
  · rw [hcode, lidoCircuitBreakerCode_compile]

/-! ## The staging line -/

private structure PauseStageMemory (memory : Mem) : Prop where
  size_eq : memory.size = 768

private theorem PauseStageMemory.duration (duration : B256) :
    PauseStageMemory
      (Mem.empty.write (durationWord * 32).toNat duration.toBytes) := by
  constructor
  rw [Mem.size_write_word_at]
  decide +kernel

private theorem PauseStageMemory.write
    {memory : Mem} (h : PauseStageMemory memory)
    (offset : B256) (value : B256)
    (hfit : (offset * 32).toNat + 32 ≤ 768) :
    PauseStageMemory
      (memory.write (offset * 32).toNat value.toBytes) := by
  constructor
  rw [Mem.size_write_of_le]
  · exact h.size_eq
  · rw [B256.length_toBytes, h.size_eq]
    exact hfit

private theorem pauseStageDuration_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {duration : B256} {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[],
        Mem.empty.write (durationWord * 32).toNat duration.toBytes, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[duration], Mem.empty, G + 79⟩)
      (mstoreAt durationWord +++ rest) post := by
  func_run (2) [73]
  case h_ext =>
    exact Devm.extCost_of_size (n := 0) rfl (by decide +kernel)
  case a =>
    have hgas : G + 79 - 79 = G := by omega
    simpa only [prepend, Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach, Devm.gasLeft_setMach, hgas] using hrest

private theorem PauseStageMemory.runCompiled_pushMstore
    {memory : Mem} (h : PauseStageMemory memory)
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {offset value : B256} {pushGas G : Nat} {rest : Func}
    (hoffset : pushCost (offset * 32).toBytes.sig = 3)
    (hvalue : pushCost value.toBytes.sig = pushGas)
    (hfit : (offset * 32).toNat + 32 ≤ 768)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[],
        memory.write (offset * 32).toNat value.toBytes, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, G + (pushGas + 6)⟩)
      (pushB256 value ::: mstoreAt offset +++ rest) post := by
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_pushB256 (c := pushGas) (G := G + 6) hvalue
    · simp only [Devm.gasLeft_setMach]
      omega
    · simp only [Devm.stack_setMach, List.length_nil]
      omega
  · apply Func.RunCompiled.next
    · apply Ninst.runCompiled_pushB256 (c := 3) (G := G + 3) hoffset
      · simp only [Devm.gasLeft_setMach]
      · simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega
    · func_run (1) [0]
      case h_ext =>
        simp only [Devm.memory_setMach]
        exact Devm.extCost_zero_of_le (by rw [h.size_eq]) (by
          rw [h.size_eq]
          exact hfit)
      case a =>
        have hgas : G + 3 - 3 = G := by omega
        simpa only [prepend, Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach, Devm.gasLeft_setMach, hgas] using hrest

private theorem PauseStageMemory.runCompiled_argTarget
    {memory : Mem} (h : PauseStageMemory memory)
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {target : B256} {G : Nat} {rest : Func}
    (hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hfit : (targetWord * 32).toNat + 32 ≤ 768)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[],
        memory.write (targetWord * 32).toNat target.toBytes, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, G + 12⟩)
      (arg 0 +++ mstoreAt targetWord +++ rest) post := by
  unfold arg cdl
  func_run (4) [0]
  case h_ext =>
    exact Devm.extCost_zero_of_le (by rw [h.size_eq]) (by
      rw [h.size_eq]
      exact hfit)
  case a =>
    rw [hargTarget]
    have hgas : G + 12 - 12 = G := by omega
    simpa only [prepend, Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach, Devm.gasLeft_setMach, hgas] using hrest

private theorem pauseStageCall_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (memory : Mem) (G : Nat) (post : Devm)
    (hkernel : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], memory, G⟩) setPauserKernel post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], memory, G + 12⟩)
      (.call setPauserSlot) post := by
  func_run (1)
  case h_body =>
    have hgas : G + 12 - 12 = G := by omega
    simpa only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach, Devm.gasLeft_setMach, hgas] using hkernel

/-- The five scratch writes `pause`'s body performs between its liveness guard
and the Registry kernel call, with the pause duration already on the stack.

Unlike the register side's staging, the first write is the *last* scratch word
— `durationWord` at offset `736` — so the whole memory extension, `73` gas for
twenty-four words, is paid there and the four writes that follow are free.
`128` gas in total, `12` of it the call burn. -/
theorem pause_stageArgs_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (target duration : B256) (kernelGas : Nat) (post : Devm)
    (hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hkernel : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], pauseMemory target duration, kernelGas⟩)
      setPauserKernel post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[duration], Mem.empty, kernelGas + 128⟩)
      (mstoreAt durationWord +++
        arg 0 +++ mstoreAt targetWord +++
        pushB256 0 ::: mstoreAt newPauserWord +++
        pushB256 0 ::: mstoreAt previousPauserWord +++
        pushB256 1 ::: mstoreAt continuationWord +++
        .call setPauserSlot) post := by
  let M1 := Mem.empty.write (durationWord * 32).toNat duration.toBytes
  let M2 := M1.write (targetWord * 32).toNat target.toBytes
  let M3 := M2.write (newPauserWord * 32).toNat (0 : B256).toBytes
  let M4 := M3.write (previousPauserWord * 32).toNat (0 : B256).toBytes
  let M5 := M4.write (continuationWord * 32).toNat (1 : B256).toBytes
  have htargetFit : (targetWord * 32).toNat + 32 ≤ 768 := by
    decide +kernel
  have hnewFit : (newPauserWord * 32).toNat + 32 ≤ 768 := by
    decide +kernel
  have hpreviousFit : (previousPauserWord * 32).toNat + 32 ≤ 768 := by
    decide +kernel
  have hcontinuationFit : (continuationWord * 32).toNat + 32 ≤ 768 := by
    decide +kernel
  have hnewOffset : pushCost (newPauserWord * 32).toBytes.sig = 3 := by
    decide +kernel
  have hpreviousOffset :
      pushCost (previousPauserWord * 32).toBytes.sig = 3 := by
    decide +kernel
  have hcontinuationOffset :
      pushCost (continuationWord * 32).toBytes.sig = 3 := by
    decide +kernel
  have hpushZero : pushCost (0 : B256).toBytes.sig = 2 := by
    decide +kernel
  have hpushOne : pushCost (1 : B256).toBytes.sig = 3 := by
    decide +kernel
  have hM1 : PauseStageMemory M1 := by
    simpa only [M1] using PauseStageMemory.duration duration
  have hM2 : PauseStageMemory M2 := by
    simpa only [M2] using hM1.write targetWord target htargetFit
  have hM3 : PauseStageMemory M3 := by
    simpa only [M3] using hM2.write newPauserWord 0 hnewFit
  have hM4 : PauseStageMemory M4 := by
    simpa only [M4] using hM3.write previousPauserWord 0 hpreviousFit
  have hcall : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], M5, kernelGas + 12⟩)
      (.call setPauserSlot) post := by
    apply pauseStageCall_runCompiled dp sevm base M5 kernelGas post
    simpa only [M5, M4, M3, M2, M1, pauseMemory] using hkernel
  have hcontinuation :
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[], M4, kernelGas + 21⟩)
        (pushB256 1 ::: mstoreAt continuationWord +++
          .call setPauserSlot) post := by
    simpa only [M5, show (kernelGas + 12) + (3 + 6) = kernelGas + 21 by omega]
      using hM4.runCompiled_pushMstore hcontinuationOffset hpushOne
        hcontinuationFit hcall
  have hprevious :
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[], M3, kernelGas + 29⟩)
        (pushB256 0 ::: mstoreAt previousPauserWord +++
          pushB256 1 ::: mstoreAt continuationWord +++
          .call setPauserSlot) post := by
    simpa only [M4, show (kernelGas + 21) + (2 + 6) = kernelGas + 29 by omega]
      using hM3.runCompiled_pushMstore hpreviousOffset hpushZero
        hpreviousFit hcontinuation
  have hnew : Func.RunCompiled
      ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], M2, kernelGas + 37⟩)
      (pushB256 0 ::: mstoreAt newPauserWord +++
        pushB256 0 ::: mstoreAt previousPauserWord +++
        pushB256 1 ::: mstoreAt continuationWord +++
        .call setPauserSlot) post := by
    simpa only [M3, show (kernelGas + 29) + (2 + 6) = kernelGas + 37 by omega]
      using hM2.runCompiled_pushMstore hnewOffset hpushZero hnewFit hprevious
  have htarget : Func.RunCompiled
      ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], M1, kernelGas + 49⟩)
      (arg 0 +++ mstoreAt targetWord +++
        pushB256 0 ::: mstoreAt newPauserWord +++
        pushB256 0 ::: mstoreAt previousPauserWord +++
        pushB256 1 ::: mstoreAt continuationWord +++
        .call setPauserSlot) post := by
    simpa only [M2, show (kernelGas + 37) + 12 = kernelGas + 49 by omega]
      using hM1.runCompiled_argTarget hargTarget htargetFit hnew
  simpa only [M1, show (kernelGas + 49) + 79 = kernelGas + 128 by omega]
    using pauseStageDuration_runCompiled htarget

/-! ## The guarded body -/

/-- The world after `pause`'s assignment `SLOAD`: the lock write, then the
warming that read may have done. -/
def pauseExpiryBase (sevm : Sevm) (base : Devm) (target : B256) : Devm :=
  temporalSloadBase sevm (pauseLockPost sevm base) (assignmentSlot target)

/-- The world after `pause`'s liveness `SLOAD`. -/
def pauseDurationBase (sevm : Sevm) (base : Devm) (target pauser : B256) :
    Devm :=
  temporalSloadBase sevm (pauseExpiryBase sevm base target) (expirySlot pauser)

/-- The world `pause` hands the Registry kernel: the lock is taken and the
three read keys are warm. -/
def pauseKernelBase (sevm : Sevm) (base : Devm) (target pauser : B256) :
    Devm :=
  temporalSloadBase sevm (pauseDurationBase sevm base target pauser)
    pauseDurationSlot

private theorem pausePushNotZero_prepend_runCompiled
    {dp : DeployParams} {sevm : Sevm} {base : Devm}
    {G : Nat} {tail : Func} {post : Devm} {target : B256}
    (htail : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨~~~(0 : B256) :: target :: [], Mem.empty, G⟩) tail post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨target :: [], Mem.empty, G + 5⟩)
      ([pushB256 0, not] +++ tail) post := by
  func_run (2) [~~~(0 : B256)]
  case a =>
    change Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨~~~(0 : B256) :: target :: [], Mem.empty, G⟩) tail post
    exact htail

private theorem pauseShiftAddressMask_prepend_runCompiled
    {dp : DeployParams} {sevm : Sevm} {base : Devm}
    {G : Nat} {tail : Func} {post : Devm} {target : B256}
    (htail : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach
        ⟨((~~~(0 : B256)) <<< (Nat.toB256 160).toNat) :: target :: [],
          Mem.empty, G⟩) tail post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨~~~(0 : B256) :: target :: [], Mem.empty, G + 6⟩)
      ([pushB256 (Nat.toB256 160), shl] +++ tail) post := by
  func_run (2)
    [((~~~(0 : B256)) <<< (Nat.toB256 160).toNat)]
  case a =>
    change Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach
        ⟨((~~~(0 : B256)) <<< (Nat.toB256 160).toNat) :: target :: [],
          Mem.empty, G⟩) tail post
    exact htail

private theorem pauseCanonicalBranch_success_runCompiled
    {dp : DeployParams} {sevm : Sevm} {base : Devm}
    {G : Nat} {body : Func} {post : Devm} {target : B256}
    (hmask : addressMask &&& target = 0)
    (hbody : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty, G⟩) body post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨addressMask :: target :: [], Mem.empty, G + 16⟩)
      ([Ninst.and] +++ ((.call emptyRevertSlot) <?> body)) post := by
  func_run (2) [0]
  case h_arm =>
    have hg : G + 16 - 16 = G := by omega
    simpa only [hg] using hbody

private theorem pauseCheckNonAddress_success_runCompiled
    {dp : DeployParams} {sevm : Sevm} {base : Devm}
    {G : Nat} {body : Func} {post : Devm} {target : B256}
    (hmask : addressMask &&& target = 0)
    (hbody : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty, G⟩) body post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨target :: [], Mem.empty, G + 27⟩)
      (checkNonAddress +++ ((.call emptyRevertSlot) <?> body)) post := by
  have hbranch := pauseCanonicalBranch_success_runCompiled hmask hbody
  have hshiftRaw :
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach
          ⟨((~~~(0 : B256)) <<< (Nat.toB256 160).toNat) :: target :: [],
            Mem.empty, G + 16⟩)
        ([Ninst.and] +++ ((.call emptyRevertSlot) <?> body)) post := by
    rw [← addressMask_eq_shl]
    exact hbranch
  have hshift := pauseShiftAddressMask_prepend_runCompiled hshiftRaw
  have hnot := pausePushNotZero_prepend_runCompiled hshift
  have hg : G + 16 + 6 + 5 = G + 27 := by omega
  have hsplit :
      checkNonAddress +++ ((.call emptyRevertSlot) <?> body) =
        [pushB256 0, not] +++
          ([pushB256 (Nat.toB256 160), shl] +++
            ([Ninst.and] +++ ((.call emptyRevertSlot) <?> body))) := by
    rfl
  rw [← hg, hsplit]
  exact hnot

private theorem pauseCanonicalAddressArg0_success_runCompiled
    {dp : DeployParams} {sevm : Sevm} {base : Devm}
    {G : Nat} {body : Func} {post : Devm} {target : B256}
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hmask : addressMask &&& target = 0)
    (hbody : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty, G⟩) body post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty, G + 33⟩)
      (canonicalAddressArg 0 body) post := by
  have hcheck := pauseCheckNonAddress_success_runCompiled hmask hbody
  have hargRun : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty, G + 27 + 6⟩)
      (arg 0 +++ checkNonAddress +++
        ((.call emptyRevertSlot) <?> body)) post := by
    unfold arg cdl
    func_run (2)
    case a => rw [harg]; exact hcheck
  have hg : G + 27 + 6 = G + 33 := by omega
  have hsplit :
      canonicalAddressArg 0 body =
        arg 0 +++ checkNonAddress +++
          ((.call emptyRevertSlot) <?> body) := by
    rfl
  rw [← hg, hsplit]
  exact hargRun

private theorem pauseRequireStaticArgs1_success_runCompiled
    {dp : DeployParams} {sevm : Sevm} {base : Devm}
    {G : Nat} {body : Func} {post : Devm}
    (hdata : sevm.data.length.toB256 <? 36 = 0)
    (hbody : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty, G⟩) body post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty, G + 21⟩)
      (requireStaticArgs 1 body) post := by
  unfold requireStaticArgs
  func_run (4) [0]
  case h_arm =>
    have hg : G + 21 - 21 = G := by omega
    rw [hg]
    exact hbody

private theorem pauseAssignmentSlotArg0_prepend_runCompiled
    {dp : DeployParams} {sevm : Sevm} {base : Devm}
    {G : Nat} {tail : Func} {post : Devm} {target : B256}
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (htail : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[assignmentSlot target], Mem.empty, G⟩) tail post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty, G + 12⟩)
      (arg 0 +++ tagTop assignmentRegion +++ tail) post := by
  unfold arg cdl
  func_run (4) [assignmentSlot target]
  case h_val => rw [harg]; rfl
  case a => exact htail

private theorem pauseExpirySlotCaller_prepend_runCompiled
    {dp : DeployParams} {sevm : Sevm} {base : Devm}
    {G : Nat} {tail : Func} {post : Devm} {pauser : B256}
    (hcaller : sevm.caller.toB256 = pauser)
    (htail : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[expirySlot pauser], Mem.empty, G⟩) tail post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty, G + 8⟩)
      (caller ::: tagTop expiryRegion +++ tail) post := by
  func_run (3) [expirySlot pauser]
  case h_val => rw [hcaller]; rfl
  case a => exact htail

set_option maxRecDepth 1150 in
/-- `pause`'s complete body, from the endpoint's entry to the internal
`.call setPauserSlot` burn.  The walk crosses all five guards on their taken
arms — the one-word calldata test, the canonical-address decoder, the
reentrancy lock, the caller's assignment and the caller's heartbeat liveness —
takes the lock, stages the five scratch words, and hands the shared Registry
kernel a generic continuation.  It does **not** enter the kernel.

Reserve `469` plus the three storage reads, whose charges are supplied as
`temporalSloadCost` equations because warmth is a fact about the frame:

* `21` for `requireStaticArgs 1` and `33` for `canonicalAddressArg 0`;
* `120` for the lock `TLOAD` and its branch, and `106` for the lock `TSTORE`;
* `31 + assignmentCost` for the authorization guard and
  `27 + expiryCost` for the liveness guard;
* `3 + durationCost` for the duration read, and `128` for the staging line
  and the call burn.

Every constant is the reverting ladder's own cost definition instantiated at
this image: `exactPauseCost`, `canonicalUnlockedPauseCost`,
`unlockedGuardPauseCost`, `lockWriteAuthorizedPauseCost`,
`authorizedLiveExpiryPauseCost`, `liveExpiryPauseCost` and
`pauseDurationSavePauseCost` in `Blanc/LidoCircuitBreakerRegistry.lean`, whose
three `gasColdSload` occurrences are the worst case of the three costs this
statement leaves open. -/
theorem pause_body_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (target pauser expiry duration : B256)
    (assignmentCost expiryCost durationCost kernelGas : Nat) (post : Devm)
    (hdataLength : sevm.data.length = 36)
    (hmask : addressMask &&& target = 0)
    (hlock : base.getTransVal sevm.currentTarget lockKey = 0)
    (hdataTarget : Sevm.dataWord sevm 4 = target)
    (hcaller : sevm.caller.toB256 = pauser)
    (hauthorizationStorage :
      (pauseLockPost sevm base).getStorVal sevm.currentTarget
        (assignmentSlot target) = pauser)
    (hassignmentCost : temporalSloadCost sevm (pauseLockPost sevm base)
      (assignmentSlot target) = assignmentCost)
    (hexpiryStorage :
      (pauseExpiryBase sevm base target).getStorVal sevm.currentTarget
        (expirySlot pauser) = expiry)
    (hexpiryCost : temporalSloadCost sevm (pauseExpiryBase sevm base target)
      (expirySlot pauser) = expiryCost)
    (hlive : sevm.benvStat.time < expiry)
    (hdurationStorage :
      (pauseDurationBase sevm base target pauser).getStorVal
        sevm.currentTarget pauseDurationSlot = duration)
    (hdurationCost : temporalSloadCost sevm
      (pauseDurationBase sevm base target pauser) pauseDurationSlot =
        durationCost)
    (hstatic : sevm.isStatic = false)
    (hkernel : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      ((pauseKernelBase sevm base target pauser).setMach
        ⟨[], pauseMemory target duration, kernelGas⟩) setPauserKernel post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty,
        kernelGas + (469 + assignmentCost + expiryCost + durationCost)⟩)
      pause post := by
  unfold pause
  set total :=
    kernelGas + (469 + assignmentCost + expiryCost + durationCost)
    with htotal
  have hdata : sevm.data.length.toB256 <? 36 = 0 := by
    rw [hdataLength]
    decide +kernel
  have hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target := by
    rw [show (32 * 0 + 4 : B256) = 4 by decide +kernel, hdataTarget]
  have hgas : (total - 54 + 33) + 21 = total := by
    dsimp only [total]
    omega
  rw [← hgas]
  refine pauseRequireStaticArgs1_success_runCompiled hdata ?_
  refine pauseCanonicalAddressArg0_success_runCompiled hargTarget hmask ?_
  func_run (1)
    -- The reentrancy lock reads zero.
  have htload : Ninst.RunCompiled sevm
        (base.setMach ⟨[lockKey], Mem.empty, total - 57⟩) Ninst.tload
        (base.setMach ⟨[0], Mem.empty, total - 57 - 100⟩) := by
      have h := runCompiled_tload_of (sevm := sevm)
        (pre := base.setMach ⟨[lockKey], Mem.empty, total - 57⟩)
        (key := lockKey) (value := 0) (stack := [])
        (G := total - 57 - 100) rfl hlock
        (by simp only [Devm.gasLeft_setMach, gasWarmAccess]; omega)
        (by simp)
      simpa only [Devm.memory_setMach, Devm.setMach_setMach] using h
  refine Func.RunCompiled.next htload ?_
  func_run (2) [1]
  func_run (2)
  -- The lock is taken; only transient storage changes.
  have htstore : Ninst.RunCompiled sevm
      (base.setMach ⟨[lockKey, 1], Mem.empty, total - 57 - 123⟩)
      Ninst.tstore
      ((pauseLockPost sevm base).setMach
        ⟨[], Mem.empty, total - 57 - 223⟩) := by
    have h := runCompiled_tstore_of (sevm := sevm)
      (pre := base.setMach ⟨[lockKey, 1], Mem.empty, total - 57 - 123⟩)
      (key := lockKey) (value := 1) (stack := [])
      (G := total - 57 - 223) rfl hstatic
      (by simp only [Devm.gasLeft_setMach, gasWarmAccess]; omega)
    simpa only [Devm.memory_setMach, Devm.setMach_setMach,
      setTransVal_setMach, pauseLockPost] using h
  refine Func.RunCompiled.next htstore ?_
  have hassignmentGas : total - 57 - 223 = total - 57 - 235 + 12 := by
    dsimp only [total]
    omega
  rw [hassignmentGas]
  refine pauseAssignmentSlotArg0_prepend_runCompiled hargTarget ?_
  -- The target's assignment names the caller.
  have hassignSload : Ninst.RunCompiled sevm
      ((pauseLockPost sevm base).setMach
        ⟨[assignmentSlot target], Mem.empty, total - 57 - 235⟩)
      Ninst.sload
      ((pauseExpiryBase sevm base target).setMach
        ⟨[pauser], Mem.empty, total - 57 - 235 - assignmentCost⟩) := by
    have h := temporal_sload_runCompiled (sevm := sevm)
      (base := pauseLockPost sevm base) (key := assignmentSlot target)
      (value := pauser) (stack := []) (M := Mem.empty)
      (G := total - 57 - 235 - assignmentCost)
      hauthorizationStorage (by simp)
    rw [hassignmentCost,
      show total - 57 - 235 - assignmentCost + assignmentCost =
        total - 57 - 235 by omega] at h
    exact h
  refine Func.RunCompiled.next hassignSload ?_
  func_run (3) [1]
  case h_val => simp [B256.eqCheck, hcaller]
  have hexpiryGas :
      total - 57 - 235 - assignmentCost - 19 =
        total - 57 - 235 - assignmentCost - 27 + 8 := by
    dsimp only [total]
    omega
  rw [hexpiryGas]
  refine pauseExpirySlotCaller_prepend_runCompiled hcaller ?_
  -- The caller's heartbeat has not expired.
  have hexpirySload : Ninst.RunCompiled sevm
      ((pauseExpiryBase sevm base target).setMach
        ⟨[expirySlot pauser], Mem.empty,
          total - 57 - 235 - assignmentCost - 27⟩)
      Ninst.sload
      ((pauseDurationBase sevm base target pauser).setMach
        ⟨[expiry], Mem.empty,
          total - 57 - 235 - assignmentCost - 27 - expiryCost⟩) := by
    have h := temporal_sload_runCompiled (sevm := sevm)
      (base := pauseExpiryBase sevm base target) (key := expirySlot pauser)
      (value := expiry) (stack := []) (M := Mem.empty)
      (G := total - 57 - 235 - assignmentCost - 27 - expiryCost)
      hexpiryStorage (by simp)
    rw [hexpiryCost,
      show total - 57 - 235 - assignmentCost - 27 - expiryCost +
        expiryCost = total - 57 - 235 - assignmentCost - 27 by omega] at h
    exact h
  refine Func.RunCompiled.next hexpirySload ?_
  func_run (3) [1]
  case h_val => simp [B256.ltCheck, hlive]
  func_run (1)
  -- The configured pause duration is staged with the rest of the image.
  have hdurationSload : Ninst.RunCompiled sevm
      ((pauseDurationBase sevm base target pauser).setMach
        ⟨[pauseDurationSlot], Mem.empty,
          total - 57 - 235 - assignmentCost - 27 - expiryCost - 22⟩)
      Ninst.sload
      ((pauseKernelBase sevm base target pauser).setMach
        ⟨[duration], Mem.empty, kernelGas + 128⟩) := by
    have h := temporal_sload_runCompiled (sevm := sevm)
      (base := pauseDurationBase sevm base target pauser)
      (key := pauseDurationSlot) (value := duration) (stack := [])
      (M := Mem.empty) (G := kernelGas + 128) hdurationStorage (by simp)
    rw [hdurationCost] at h
    rw [show total - 57 - 235 - assignmentCost - 27 - expiryCost - 22 =
      kernelGas + 128 + durationCost by omega]
    exact h
  refine Func.RunCompiled.next hdurationSload ?_
  exact pause_stageArgs_runCompiled dp sevm
      (pauseKernelBase sevm base target pauser) target duration kernelGas post
      hargTarget hkernel

/-! ## The `finishSetPauser` pause arm -/

set_option maxRecDepth 7629 in
/-- `finishSetPauser`'s pause arm: the sibling of
`finishSetPauser_registerAfterSet_runCompiled` in which the continuation word
is `1` rather than `0`, so `ISZERO` produces zero and the conditional takes its
zero branch into `pauseAfterSet`.

Glue cost 1934 gas: 1900 for the three scratch loads and the `LOG3`, 9 for the
continuation load and `ISZERO`, 13 for the branch pop — a zero arm pays no
`JUMPDEST` — and 12 for the call burn.  That is exactly one gas less than the
register arm, and the `JUMPDEST` is the whole difference. -/
theorem finishSetPauser_pauseAfterSet_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target previousPauser newPauser : B256)
    (stack : List B256) (G : Nat) (post : Devm)
    (hstack : stack.length ≤ 1)
    (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (hsize : 640 ≤ M.size) (halign : M.size % 32 = 0)
    (hstatic : sevm.isStatic = false)
    (hpause : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      ((base.addLog ⟨sevm.currentTarget,
          [pauserSetEvent, target, previousPauser, newPauser], []⟩).setMach
        ⟨stack, M, G⟩) pauseAfterSet post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M, G + 1934⟩) finishSetPauser post := by
  let eventLog : Log :=
    ⟨sevm.currentTarget,
      [pauserSetEvent, target, previousPauser, newPauser], []⟩
  let eventBase := base.addLog eventLog
  have htargetCovered : (targetWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (targetWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have hpreviousCovered :
      (previousPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (previousPauserWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have hnewCovered : (newPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (newPauserWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have hcontinuationCovered :
      (continuationWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (continuationWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have htargetMemory :
      (M.read (targetWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign htargetCovered)]
  have hpreviousMemory :
      (M.read (previousPauserWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hpreviousCovered)]
  have hnewMemory :
      (M.read (newPauserWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hnewCovered)]
  have hcontinuationMemory :
      (M.read (continuationWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self
      (memExtSize_of_le halign hcontinuationCovered)]
  have htargetValue :
      (M.read (targetWord * 32).toNat 32).1.toB256 = target := by
    rw [Mem.Reads.read hreads]
    exact htarget
  have hpreviousValue :
      (M.read (previousPauserWord * 32).toNat 32).1.toB256 =
        previousPauser := by
    rw [Mem.Reads.read hreads]
    exact hprevious
  have hnewValue :
      (M.read (newPauserWord * 32).toNat 32).1.toB256 = newPauser := by
    rw [Mem.Reads.read hreads]
    exact hnew
  have hcontinuationValue :
      (M.read (continuationWord * 32).toNat 32).1.toB256 = 1 := by
    rw [Mem.Reads.read hreads]
    exact hcontinuation
  have hreadZero : M.read 0 0 = ([], M) := by
    simp [Mem.read, Mem.extend, memExtSize]
    rfl
  let fs := (runtime dp).main :: (runtime dp).aux
  have hlookup : fs[pauseAfterSetSlot]? = some pauseAfterSet := by
    simp [fs, runtime, aux, pauseAfterSetSlot]
  have hcall : Func.RunCompiled fs sevm
      (eventBase.setMach ⟨stack, M, G + 12⟩)
      (.call pauseAfterSetSlot) post := by
    apply Func.RunCompiled.call hlookup
      (by simp only [Devm.stack_setMach]; omega)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.burnBy_setMach_gas
          (devm := eventBase.setMach ⟨stack, M, G + 12⟩)
          (cost := gVerylow + gMid + gJumpdest) (G := G)
          (by simp only [Devm.gasLeft_setMach]
              norm_num [gVerylow, gMid, gJumpdest]))
    · exact hpause
  have hbranch : Func.RunCompiled fs sevm
      (eventBase.setMach ⟨0 :: stack, M, G + 25⟩)
      ((.call registerAfterSetSlot) <?> (.call pauseAfterSetSlot)) post := by
    apply Func.RunCompiled.zero
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.popBurnBy_setMach
          (devm := eventBase.setMach ⟨0 :: stack, M, G + 25⟩)
          (x := (0 : B256)) (s := stack)
          (cost := gVerylow + gHigh) (G := G + 12)
          (h_stk := rfl) (h := by
            simp only [Devm.gasLeft_setMach]
            norm_num [gVerylow, gHigh]))
    · exact hcall
  have hcontinuationRun : Func.RunCompiled fs sevm
      (eventBase.setMach ⟨stack, M, G + 34⟩)
      (loadWord continuationWord +++ Ninst.iszero :::
        ((.call registerAfterSetSlot) <?> (.call pauseAfterSetSlot))) post := by
    func_run (3) [3]
    all_goals try ((try simp only [Devm.stack_setMach]); omega)
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign hcontinuationCovered]
      norm_num [gVerylow]
    case a =>
      rw [hcontinuationValue, hcontinuationMemory]
      norm_num
      exact hbranch
  simp only [finishSetPauser]
  func_run (10) [3, 3, 3, 1875]
  all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
  all_goals try simp_rw [hnewMemory]
  all_goals try simp_rw [hpreviousMemory]
  all_goals try simp_rw [htargetMemory]
  all_goals try {
    rw [Devm.extCost_zero_of_le halign (by omega)]
    norm_num [gVerylow, gLog, gLogdata, gLogtopic] }
  case h_cost =>
    simp only [show ((0 : B256) * 32).toNat = 0 by decide]
    rw [Devm.extCost_zero_of_le halign (by omega)]
    norm_num [gLog, gLogdata, gLogtopic]
  case a =>
    rw [hnewValue, hpreviousValue, htargetValue]
    rw [show ((0 : B256) * 32).toNat = 0 by decide, hreadZero]
    exact hcontinuationRun

end Blanc.LidoCircuitBreaker
