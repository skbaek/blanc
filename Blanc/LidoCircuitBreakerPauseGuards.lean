import Blanc.LidoCircuitBreakerPauseRoute

/-!
# The `pause` body route

Five guards stand between `pause`'s entry and its `.call setPauserSlot`, and
the kernel adds a sixth before the `setPauser.assignment` `SSTORE`.  Four of
the six are free on this route, and the split is exactly the one
`Blanc/LidoCircuitBreakerPauseRoute.lean` describes:

* the reentrancy-lock guard, the caller-assignment guard, the
  heartbeat-liveness guard and the kernel's target-zero test each have a
  *named* runtime error on the arm this walk does not take, so an empty raw
  payload refutes that arm outright;
* `requireStaticArgs` and `canonicalAddressArg` revert through a bare
  `Func.rev`, whose payload is also empty, so their words have to be computed.

Both surviving words are calldata-valued.  Nothing on this leg reads storage,
transient storage or memory, so nothing is threaded across it.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-- `requireStaticArgs 1`'s guard line, spelled literally. -/
def pauseStaticArgsTest : Line :=
  [Ninst.pushB256 (Nat.toB256 (4 + 32 * 1)), Ninst.calldatasize, Ninst.lt]

/-- The reentrancy-lock test, spelled literally. -/
def pauseLockTest : Line :=
  [Ninst.pushB256 lockKey, Ninst.tload, Ninst.iszero]

/-- The lock write followed by the assignment test. -/
def pauseAssignedTest : Line :=
  [Ninst.pushB256 1, Ninst.pushB256 lockKey, Ninst.tstore] ++
  arg 0 ++ tagTop assignmentRegion ++ [Ninst.sload, Ninst.caller, Ninst.eq]

/-- The heartbeat-liveness test. -/
def pauseLiveTest : Line :=
  [Ninst.caller] ++ tagTop expiryRegion ++
  [Ninst.sload, Ninst.timestamp, Ninst.lt]

/-- `pause`'s staging line, from the liveness guard to the kernel call: the
five memory words the shared Registry kernel reads, `continuationWord` among
them set to `1` so `finishSetPauser` tail-calls `pauseAfterSet`. -/
def pauseStagingLine : Line :=
  [Ninst.pushB256 pauseDurationSlot, Ninst.sload] ++ mstoreAt durationWord ++
  arg 0 ++ mstoreAt targetWord ++
  [Ninst.pushB256 0] ++ mstoreAt newPauserWord ++
  [Ninst.pushB256 0] ++ mstoreAt previousPauserWord ++
  [Ninst.pushB256 1] ++ mstoreAt continuationWord

set_option maxRecDepth 8192 in
/-- From `pause`'s entry to its `.call setPauserSlot`, on a walk whose raw
revert carries no payload.

Only the two calldata guards cost a branch word.  The three that read the
world — the reentrancy lock, the caller's assignment and the caller's
heartbeat liveness — are settled by the outcome, because each of them reverts
through a named error whose payload is four bytes long. -/
theorem pause_routeTo_setPauserCall (dp : DeployParams)
    {sevm : Sevm} {devm raw : Devm}
    {functionIndex : Nat} {steps : List Prog.SourceStep}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      pause (.error (.revert, raw)))
    (emptyOutput : raw.output = [])
    (argsPresent : ∀ start mid : Devm,
      Line.Run sevm start pauseStaticArgsTest mid →
      ∀ (w : B256) (rest : Stack), mid.stack = w :: rest → w = 0)
    (targetCanonical : ∀ start mid : Devm,
      Line.Run sevm start (arg 0 ++ checkNonAddress) mid →
      ∀ (w : B256) (rest : Stack), mid.stack = w :: rest → w = 0)
    (callRoute : ∀ (current : Prog.SourcePath) (stage devm' : Devm),
      Devm.getStor devm' = Devm.getStor devm →
      stage.memory = devm.memory →
      Line.Run sevm stage pauseStagingLine devm' →
      ∀ tail : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm devm' (Func.call setPauserSlot) (.error (.revert, raw)),
        Func.RunCompiledTo.RouteTo current tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h targetPath
      targetInstruction := by
  obtain ⟨_zero, notPauser, expired, reentrant⟩ := runtime_error_lookups dp
  refine routeTo_line pauseStaticArgsTest h (fun s0 r0 tail0 => ?_)
  have g0 : Devm.getStor s0 = Devm.getStor devm :=
    (Line.of_inv Devm.getStor (by unfold pauseStaticArgsTest; line_inv)
      r0).symm
  have m0 : s0.memory = devm.memory :=
    (Line.of_inv Devm.memory (by unfold pauseStaticArgsTest; line_inv) r0).symm
  refine routeTo_branchLeft_frame tail0 (argsPresent devm s0 r0)
    (fun s1 hpop1 tail1 => ?_)
  have g1 := (getStor_of_state hpop1.state).symm.trans g0
  have m1 := hpop1.memory.symm.trans m0
  refine routeTo_line (arg 0 ++ checkNonAddress) tail1
    (fun s2 r2 tail2 => ?_)
  have g2 := (Line.of_inv Devm.getStor (by line_inv) r2).symm.trans g1
  have m2 := (Line.of_inv Devm.memory (by line_inv) r2).symm.trans m1
  refine routeTo_branchLeft_frame tail2 (targetCanonical s1 s2 r2)
    (fun _s3 hpop3 tail3 => ?_)
  have g3 := (getStor_of_state hpop3.state).symm.trans g2
  have m3 := hpop3.memory.symm.trans m2
  refine routeTo_line pauseLockTest tail3 (fun _s4 r4 tail4 => ?_)
  have g4 := (Line.of_inv Devm.getStor (by unfold pauseLockTest; line_inv)
    r4).symm.trans g3
  have m4 := (Line.of_inv Devm.memory (by unfold pauseLockTest; line_inv)
    r4).symm.trans m3
  refine routeTo_branchRight_of_leftRefuted tail4
    (fun _start armRun =>
      call_namedError_refuted "ReentrantCall" reentrant emptyOutput armRun)
    (fun _s5 _w5 hpop5 tail5 => ?_)
  have g5 := (getStor_of_state hpop5.state).symm.trans g4
  have m5 := hpop5.memory.symm.trans m4
  refine routeTo_line pauseAssignedTest tail5 (fun _s6 r6 tail6 => ?_)
  have g6 := (Line.of_inv Devm.getStor
    (by unfold pauseAssignedTest; line_inv) r6).symm.trans g5
  have m6 := (Line.of_inv Devm.memory
    (by unfold pauseAssignedTest; line_inv) r6).symm.trans m5
  refine routeTo_branchRight_of_leftRefuted tail6
    (fun _start armRun =>
      call_namedError_refuted "SenderNotPauser" notPauser emptyOutput armRun)
    (fun _s7 _w7 hpop7 tail7 => ?_)
  have g7 := (getStor_of_state hpop7.state).symm.trans g6
  have m7 := hpop7.memory.symm.trans m6
  refine routeTo_line pauseLiveTest tail7 (fun _s8 r8 tail8 => ?_)
  have g8 := (Line.of_inv Devm.getStor
    (by unfold pauseLiveTest; line_inv) r8).symm.trans g7
  have m8 := (Line.of_inv Devm.memory
    (by unfold pauseLiveTest; line_inv) r8).symm.trans m7
  refine routeTo_branchRight_of_leftRefuted tail8
    (fun _start armRun =>
      call_namedError_refuted "HeartbeatExpired" expired emptyOutput armRun)
    (fun _s9 _w9 hpop9 tail9 => ?_)
  have g9 := (getStor_of_state hpop9.state).symm.trans g8
  have m9 := hpop9.memory.symm.trans m8
  refine routeTo_line pauseStagingLine tail9 (fun _s10 r10 tail10 => ?_)
  exact callRoute _ _ _
    ((Line.of_inv Devm.getStor (by unfold pauseStagingLine; line_inv)
      r10).symm.trans g9) m9 r10 tail10

/-! ## What the staging line puts in memory

Two of the kernel's own branch words are memory-valued, so the two windows they
read have to be built where the staging line writes them and carried across the
three later writes.  Byte offsets 512 (`targetWord`) and 544
(`newPauserWord`); the later writes land at 576, 608 and 736 and miss both. -/

set_option maxRecDepth 8192 in
/-- `pause`'s staging line leaves the call's target argument at `targetWord`
and a zero at `newPauserWord`.  The zero is what routes the shared kernel into
`removeTarget` rather than the count-increment arm. -/
theorem pauseStaging_windows {sevm : Sevm} {stage devm' : Devm} {img : Bytes}
    (image : MemImage stage img)
    (run : Line.Run sevm stage pauseStagingLine devm') :
    MemWordAt devm' (targetWord * 32).toNat (Sevm.argWord sevm 0) ∧
      MemWordAt devm' (newPauserWord * 32).toNat 0 := by
  unfold pauseStagingLine at run
  rcases of_run_append _ run with ⟨_u9, r9, rContinuation⟩
  rcases of_run_append _ r9 with ⟨_u8, r8, rPush1⟩
  rcases of_run_append _ r8 with ⟨_u7, r7, rPrevious⟩
  rcases of_run_append _ r7 with ⟨_u6, r6, rPush0b⟩
  rcases of_run_append _ r6 with ⟨_u5, r5, rNewPauser⟩
  rcases of_run_append _ r5 with ⟨_u4, r4, rPush0a⟩
  rcases of_run_append _ r4 with ⟨_u3, r3, rTarget⟩
  rcases of_run_append _ r3 with ⟨_u2, r2, rArg⟩
  rcases of_run_append _ r2 with ⟨_u1, r1, rDuration⟩
  have image1 : MemImage _u1 img :=
    MemImage.of_memory_eq (Line.of_inv Devm.memory (by line_inv) r1).symm image
  obtain ⟨_dv, hmemDuration⟩ := of_run_mstoreAt_mem rDuration
  have image2 := image1.write hmemDuration
  have image3 :=
    MemImage.of_memory_eq (Line.of_inv Devm.memory (by line_inv) rArg).symm
      image2
  have pArg : Sevm.argWord sevm 0 :: [] <<+ _u3.stack :=
    prefix_of_arg nil_pref rArg
  obtain ⟨pTarget, hmemTarget⟩ := of_run_mstoreAt_val rTarget pArg
  have windowT : MemWordAt _u4 (targetWord * 32).toNat (Sevm.argWord sevm 0) :=
    MemWordAt.of_write image3 hmemTarget
  have image4 := image3.write hmemTarget
  have image5 :=
    MemImage.of_memory_eq (Line.of_inv Devm.memory (by line_inv) rPush0a).symm
      image4
  have windowT5 := windowT.acrossLine (by line_inv) rPush0a
  have pZero : (0 : B256) :: [] <<+ _u5.stack :=
    prefix_of_push (of_run_pushB256 (by
      rcases Line.of_run_cons rPush0a with ⟨_, q, hnil⟩
      cases hnil
      exact q)) nil_pref
  obtain ⟨_pNew, hmemNew⟩ := of_run_mstoreAt_val rNewPauser pZero
  have windowN : MemWordAt _u6 (newPauserWord * 32).toNat 0 :=
    MemWordAt.of_write image5 hmemNew
  have windowT6 := MemWordAt.writeMiss hmemNew (by decide) windowT5
  refine ⟨?_, ?_⟩
  · exact ((((windowT6.acrossLine (by line_inv) rPush0b).acrossMstoreAt
      (by decide) rPrevious).acrossLine (by line_inv)
      rPush1).acrossMstoreAt (by decide) rContinuation)
  · exact ((((windowN.acrossLine (by line_inv) rPush0b).acrossMstoreAt
      (by decide) rPrevious).acrossLine (by line_inv)
      rPush1).acrossMstoreAt (by decide) rContinuation)


/-! ## Past the assignment write

The kernel's second branch reads the previous pauser it just `SLOAD`ed.  Under
`pause` that pauser is the caller, which `.pauseRegistry` authority requires to
be nonzero, so the walk takes the old-count arm rather than `appendTarget` --
and the arm it does not take is not an error endpoint, so this word has to be
computed.  It is the one storage-valued word on the whole route, and the one
place a memory window is read for its *value* rather than crossed. -/

/-- `setPauserKernelAssignmentPrefix` continued across the assignment `SSTORE`
and the previous-pauser zero test. -/
def pauseKernelAppendPrefix : Line :=
  setPauserKernelAssignmentPrefix ++ [Ninst.sstore, Ninst.iszero]

/-- The old-count arm's prefix, up to the `setPauser.oldCount` `SSTORE`. -/
def oldCountPrefix : Line :=
  previousCountKey ++
    [Ninst.sload, Ninst.pushB256 1, Ninst.swap 0, Ninst.sub] ++
    previousCountKey

/-- The source position the kernel reaches once its two branches are taken. -/
def kernelOldCountSteps : List Prog.SourceStep :=
  List.replicate setPauserKernelZeroCheck.length .rest ++
    [.branchLeft] ++
    List.replicate pauseKernelAppendPrefix.length .rest ++ [.branchLeft]

/-- Structural source position of the `setPauser.oldCount` `SSTORE`. -/
def setPauserOldCountPath : Prog.SourcePath :=
  ⟨setPauserSlot,
    kernelOldCountSteps ++ List.replicate oldCountPrefix.length .rest⟩

set_option maxRecDepth 8192 in
/-- The kernel's second branch word at a world whose target is already
assigned: the previous pauser is nonzero, so its `iszero` is zero and the
fall-through old-count arm is taken.  The `newPauserWord` window survives the
crossing -- the only memory the prefix writes is `previousPauserWord`. -/
theorem pauseKernel_previousPauserNonzero {sevm : Sevm} {devm devm' : Devm}
    {target : B256}
    (windowT : MemWordAt devm (targetWord * 32).toNat target)
    (windowN : MemWordAt devm (newPauserWord * 32).toNat 0)
    (assigned :
      Devm.getStorVal devm sevm.currentTarget (assignmentSlot target) ≠ 0)
    (run : Line.Run sevm devm pauseKernelAppendPrefix devm') :
    (∀ (w : B256) (rest : Stack), devm'.stack = w :: rest → w = 0) ∧
      MemWordAt devm' (newPauserWord * 32).toNat 0 := by
  unfold pauseKernelAppendPrefix setPauserKernelAssignmentPrefix at run
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  rcases Line.of_run_cons run with ⟨s2, q2, run⟩
  rcases Line.of_run_cons run with ⟨s3, q3, run⟩
  rcases Line.of_run_cons run with ⟨s4, q4, run⟩
  have p1 : (targetWord * 32) :: [] <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 q1) nil_pref
  have p2 : target :: [] <<+ s2.stack :=
    prefix_of_loadWord_window (k := targetWord) windowT nil_pref
      (Line.Run.cons q1 (Line.Run.cons q2 Line.Run.nil))
  have p3 : regionWord assignmentRegion :: target :: [] <<+ s3.stack :=
    prefix_of_push (of_run_pushB256 q3) p2
  have p4 : assignmentSlot target :: [] <<+ s4.stack := prefix_of_or q4 p3
  have hstor4 : Devm.getStor s4 = Devm.getStor devm :=
    (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons q1 (Line.Run.cons q2 (Line.Run.cons q3
        (Line.Run.cons q4 Line.Run.nil))))).symm
  rcases Line.of_run_cons run with ⟨s5, q5, run⟩
  obtain ⟨v, p5, hv⟩ := prefix_of_sload q5 p4
  have hnonzero : v ≠ 0 := by
    rw [hv,
      show Devm.getStorVal s4 sevm.currentTarget (assignmentSlot target)
          = Devm.getStorVal devm sevm.currentTarget (assignmentSlot target) from
        congrArg (fun f : Adr → Stor =>
          (f sevm.currentTarget).get (assignmentSlot target)) hstor4]
    exact assigned
  rcases Line.of_run_cons run with ⟨s6, q6, run⟩
  have p6 : v :: v :: [] <<+ s6.stack :=
    prefix_of_dup_val q6 (by show_nth) p5
  rcases Line.of_run_cons run with ⟨s7, q7, run⟩
  have p7 := prefix_of_push (of_run_pushB256 q7) p6
  rcases Line.of_run_cons run with ⟨s8, q8, run⟩
  obtain ⟨p8, hmem8⟩ := prefix_of_mstore_val q8 p7
  have windowN8 : MemWordAt s8 (newPauserWord * 32).toNat 0 :=
    MemWordAt.writeMiss hmem8 (by decide)
      (((((((windowN.acrossNinst q1).acrossMload q2).acrossNinst
        q3).acrossNinst q4).acrossNinst q5).acrossNinst q6).acrossNinst q7)
  rcases Line.of_run_cons run with ⟨s9, q9, run⟩
  have p9 := prefix_of_push (of_run_pushB256 q9) p8
  rcases Line.of_run_cons run with ⟨s10, q10, run⟩
  obtain ⟨_n, p10⟩ := prefix_of_mload q10 p9
  rcases Line.of_run_cons run with ⟨s11, q11, run⟩
  have p11 := prefix_of_push (of_run_pushB256 q11) p10
  rcases Line.of_run_cons run with ⟨s12, q12, run⟩
  obtain ⟨_m2, p12⟩ := prefix_of_mload q12 p11
  rcases Line.of_run_cons run with ⟨s13, q13, run⟩
  have p13 := prefix_of_push (of_run_pushB256 q13) p12
  rcases Line.of_run_cons run with ⟨s14, q14, run⟩
  have p14 := prefix_of_or q14 p13
  rcases Line.of_run_cons run with ⟨s15, q15, run⟩
  have p15 := prefix_of_sstore q15 p14
  rcases Line.of_run_cons run with ⟨s16, q16, hnil⟩
  cases hnil
  have p16 := prefix_of_iszero q16 p15
  refine ⟨?_, ?_⟩
  · intro w rest hstack
    rw [head_of_stack_prefix p16 hstack]
    simp [B256.eqCheck, hnonzero]
  · exact (((((((windowN8.acrossNinst q9).acrossMload q10).acrossNinst
      q11).acrossMload q12).acrossNinst q13).acrossNinst q14).acrossNinst
      q15).acrossNinst q16


set_option maxRecDepth 8192 in
/-- From `setPauserKernel`'s entry to the old-count arm: the target-zero test
(free, its other arm is `PausableZero`) and the previous-pauser test (paid for
with the one storage word on this route). -/
theorem setPauserKernel_routeTo_oldCountArm (dp : DeployParams)
    {sevm : Sevm} {devm raw : Devm} {target : B256}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      setPauserKernel (.error (.revert, raw)))
    (emptyOutput : raw.output = [])
    (windowT : MemWordAt devm (targetWord * 32).toNat target)
    (windowN : MemWordAt devm (newPauserWord * 32).toNat 0)
    (assigned :
      Devm.getStorVal devm sevm.currentTarget (assignmentSlot target) ≠ 0)
    (armRoute : ∀ devm' : Devm,
      MemWordAt devm' (newPauserWord * 32).toNat 0 →
      ∀ tail : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm
        devm' (oldCountPrefix +++ (Ninst.sstore ::: .call afterOldPauserSlot))
        (.error (.revert, raw)),
        Func.RunCompiledTo.RouteTo ⟨setPauserSlot, kernelOldCountSteps⟩ tail
          targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨setPauserSlot, []⟩ h targetPath
      targetInstruction := by
  refine routeTo_line setPauserKernelZeroCheck h (fun z zrun tail => ?_)
  have gz : Devm.getStor z = Devm.getStor devm :=
    (Line.of_inv Devm.getStor
      (by unfold setPauserKernelZeroCheck; line_inv) zrun).symm
  have wTz := windowT.acrossMemoryZeroCheck (k := targetWord) zrun
  have wNz := windowN.acrossMemoryZeroCheck (k := targetWord) zrun
  refine routeTo_branchLeft_of_rightRefuted tail
    (fun _start armRun =>
      call_namedError_refuted "PausableZero" (runtime_error_lookups dp).1
        emptyOutput armRun)
    (fun a hpop arm => ?_)
  have ga : Devm.getStor a = Devm.getStor devm :=
    (getStor_of_state hpop.state).symm.trans gz
  have wTa := MemWordAt.of_memory_eq hpop.memory.symm wTz
  have wNa := MemWordAt.of_memory_eq hpop.memory.symm wNz
  refine routeTo_line pauseKernelAppendPrefix arm (fun _b brun tail2 => ?_)
  obtain ⟨branchWord, wNb⟩ :=
    pauseKernel_previousPauserNonzero wTa wNa
      (by
        rw [show Devm.getStorVal a sevm.currentTarget (assignmentSlot target)
              = Devm.getStorVal devm sevm.currentTarget (assignmentSlot target)
            from congrArg (fun f : Adr → Stor =>
              (f sevm.currentTarget).get (assignmentSlot target)) ga]
        exact assigned)
      brun
  refine routeTo_branchLeft_frame tail2 branchWord (fun c hpopc tail3 => ?_)
  have wNc : MemWordAt c (newPauserWord * 32).toNat 0 :=
    MemWordAt.of_memory_eq hpopc.memory.symm wNb
  have pathEq :
      (([] ++ List.replicate setPauserKernelZeroCheck.length
            Prog.SourceStep.rest) ++ [Prog.SourceStep.branchLeft] ++
          List.replicate pauseKernelAppendPrefix.length Prog.SourceStep.rest) ++
            [Prog.SourceStep.branchLeft] = kernelOldCountSteps := by
    simp [kernelOldCountSteps]
  exact pathEq ▸ armRoute c wNc tail3

/-- The `setPauser.oldCount` row: the old-count arm's own straight line. -/
theorem setPauserKernel_routeTo_oldCount (dp : DeployParams)
    {sevm : Sevm} {devm raw : Devm} {target : B256}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      setPauserKernel (.error (.revert, raw)))
    (emptyOutput : raw.output = [])
    (windowT : MemWordAt devm (targetWord * 32).toNat target)
    (windowN : MemWordAt devm (newPauserWord * 32).toNat 0)
    (assigned :
      Devm.getStorVal devm sevm.currentTarget (assignmentSlot target) ≠ 0) :
    Func.RunCompiledTo.RouteTo ⟨setPauserSlot, []⟩ h setPauserOldCountPath
      (.reg .sstore) :=
  setPauserKernel_routeTo_oldCountArm dp h emptyOutput windowT windowN assigned
    (fun _devm' _wN tail =>
      routeTo_line oldCountPrefix tail
        (fun _writeState _writeRun write =>
          routeTo_head write setPauserOldCountPath))

/-! ## Into `removeTarget`

`pause` stages a zero new pauser, so `afterOldPauser`'s memory-valued test
sends the walk into `removeTarget`, which has no branch at all: its five
persistent writes are five split points of one straight line. -/

set_option maxRecDepth 8192 in
/-- Cross `oldCountPrefix` keeping the `newPauserWord` window.  The line
contains two `MLOAD`s, which only extend memory, so `line_inv` cannot cross it
in one step. -/
theorem MemWordAt.acrossOldCountPrefix {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256} (run : Line.Run e a oldCountPrefix b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold oldCountPrefix previousCountKey loadWord tagTop at run
  rcases Line.of_run_cons run with ⟨_s1, q1, run⟩
  rcases Line.of_run_cons run with ⟨_s2, q2, run⟩
  rcases Line.of_run_cons run with ⟨_s3, q3, run⟩
  rcases Line.of_run_cons run with ⟨_s4, q4, run⟩
  rcases Line.of_run_cons run with ⟨_s5, q5, run⟩
  rcases Line.of_run_cons run with ⟨_s6, q6, run⟩
  rcases Line.of_run_cons run with ⟨_s7, q7, run⟩
  rcases Line.of_run_cons run with ⟨_s8, q8, run⟩
  rcases Line.of_run_cons run with ⟨_s9, q9, run⟩
  rcases Line.of_run_cons run with ⟨_s10, q10, run⟩
  rcases Line.of_run_cons run with ⟨_s11, q11, run⟩
  rcases Line.of_run_cons run with ⟨_s12, q12, hnil⟩
  cases hnil
  exact (((((((((((window.acrossNinst q1).acrossMload q2).acrossNinst
    q3).acrossNinst q4).acrossNinst q5).acrossNinst q6).acrossNinst
    q7).acrossNinst q8).acrossNinst q9).acrossMload q10).acrossNinst
    q11).acrossNinst q12

set_option maxRecDepth 8192 in
/-- From `setPauserKernel`'s entry to `removeTarget`'s entry. -/
theorem setPauserKernel_routeTo_removeTarget (dp : DeployParams)
    {sevm : Sevm} {devm raw : Devm} {target : B256}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      setPauserKernel (.error (.revert, raw)))
    (emptyOutput : raw.output = [])
    (windowT : MemWordAt devm (targetWord * 32).toNat target)
    (windowN : MemWordAt devm (newPauserWord * 32).toNat 0)
    (assigned :
      Devm.getStorVal devm sevm.currentTarget (assignmentSlot target) ≠ 0)
    (bodyRoute : ∀ devm' : Devm,
      ∀ tail : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm
        devm' removeTarget (.error (.revert, raw)),
        Func.RunCompiledTo.RouteTo ⟨removeTargetSlot, []⟩ tail targetPath
          targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨setPauserSlot, []⟩ h targetPath
      targetInstruction := by
  refine setPauserKernel_routeTo_oldCountArm dp h emptyOutput windowT windowN
    assigned (fun _devm' wN tail => ?_)
  refine routeTo_line oldCountPrefix tail (fun d drun tail2 => ?_)
  have wNd := wN.acrossOldCountPrefix drun
  refine routeTo_next tail2 (fun e erun tail3 => ?_)
  have wNe := wNd.acrossNinst (Ninst.Run.of_runCompiled erun)
  refine routeTo_call (body := afterOldPauser) tail3
    (by simp [runtime, aux, afterOldPauserSlot]) (fun f fburn tail4 => ?_)
  have wNf := MemWordAt.of_memory_eq fburn.memory.symm wNe
  refine routeTo_line (memoryZeroCheck newPauserWord) tail4
    (fun g grun tail5 => ?_)
  refine routeTo_branchRight tail5
    (fun w rest hstack => by
      rw [memoryZeroCheck_word (k := newPauserWord) wNf grun w rest hstack]
      decide)
    (fun _armStart arm => ?_)
  exact routeTo_call (body := removeTarget) arm
    (by simp [runtime, aux, removeTargetSlot])
    (fun i _iburn tail6 => bodyRoute i tail6)

/-! ## `removeTarget`'s five writes -/

/-- Prefix up to the `remove.arrayHole` `SSTORE`. -/
def removeArrayHolePrefix : Line :=
  targetIndexKey ++ [Ninst.sload] ++ mstoreAt removedIndexWord ++
    [Ninst.pushB256 arrayLengthSlot, Ninst.sload] ++
    mstoreAt arrayLengthWord ++
    loadWord arrayLengthWord ++ tagTop arrayRegion ++ [Ninst.sload] ++
    mstoreAt lastTargetWord ++
    loadWord lastTargetWord ++ loadWord removedIndexWord ++
    tagTop arrayRegion

/-- Prefix up to the `remove.movedIndex` `SSTORE`. -/
def removeMovedIndexPrefix : Line :=
  removeArrayHolePrefix ++ [Ninst.sstore] ++
    loadWord removedIndexWord ++ lastTargetIndexKey

/-- Prefix up to the `remove.clearTail` `SSTORE`. -/
def removeClearTailPrefix : Line :=
  removeMovedIndexPrefix ++ [Ninst.sstore, Ninst.pushB256 0] ++
    loadWord arrayLengthWord ++ tagTop arrayRegion

/-- Prefix up to the `remove.arrayLength` `SSTORE`. -/
def removeArrayLengthPrefix : Line :=
  removeClearTailPrefix ++ [Ninst.sstore] ++ loadWord arrayLengthWord ++
    [Ninst.pushB256 1, Ninst.swap 0, Ninst.sub,
      Ninst.pushB256 arrayLengthSlot]

/-- Prefix up to the `remove.clearTargetIndex` `SSTORE`. -/
def removeClearTargetIndexPrefix : Line :=
  removeArrayLengthPrefix ++ [Ninst.sstore, Ninst.pushB256 0] ++
    targetIndexKey

def removeArrayHolePath : Prog.SourcePath :=
  ⟨removeTargetSlot, List.replicate removeArrayHolePrefix.length .rest⟩

def removeMovedIndexPath : Prog.SourcePath :=
  ⟨removeTargetSlot, List.replicate removeMovedIndexPrefix.length .rest⟩

def removeClearTailPath : Prog.SourcePath :=
  ⟨removeTargetSlot, List.replicate removeClearTailPrefix.length .rest⟩

def removeArrayLengthPath : Prog.SourcePath :=
  ⟨removeTargetSlot, List.replicate removeArrayLengthPrefix.length .rest⟩

def removeClearTargetIndexPath : Prog.SourcePath :=
  ⟨removeTargetSlot, List.replicate removeClearTargetIndexPrefix.length .rest⟩

set_option maxRecDepth 8192 in
theorem removeTarget_routeTo_arrayHole {fs : List Func} {sevm : Sevm}
    {devm : Devm} {out : Execution}
    (h : Func.RunCompiledTo fs sevm devm removeTarget out) :
    Func.RunCompiledTo.RouteTo ⟨removeTargetSlot, []⟩ h removeArrayHolePath
      (.reg .sstore) :=
  routeTo_line removeArrayHolePrefix h
    (fun _writeState _writeRun write => routeTo_head write removeArrayHolePath)

set_option maxRecDepth 8192 in
theorem removeTarget_routeTo_movedIndex {fs : List Func} {sevm : Sevm}
    {devm : Devm} {out : Execution}
    (h : Func.RunCompiledTo fs sevm devm removeTarget out) :
    Func.RunCompiledTo.RouteTo ⟨removeTargetSlot, []⟩ h removeMovedIndexPath
      (.reg .sstore) :=
  routeTo_line removeMovedIndexPrefix h
    (fun _writeState _writeRun write =>
      routeTo_head write removeMovedIndexPath)

set_option maxRecDepth 8192 in
theorem removeTarget_routeTo_clearTail {fs : List Func} {sevm : Sevm}
    {devm : Devm} {out : Execution}
    (h : Func.RunCompiledTo fs sevm devm removeTarget out) :
    Func.RunCompiledTo.RouteTo ⟨removeTargetSlot, []⟩ h removeClearTailPath
      (.reg .sstore) :=
  routeTo_line removeClearTailPrefix h
    (fun _writeState _writeRun write => routeTo_head write removeClearTailPath)

set_option maxRecDepth 8192 in
theorem removeTarget_routeTo_arrayLength {fs : List Func} {sevm : Sevm}
    {devm : Devm} {out : Execution}
    (h : Func.RunCompiledTo fs sevm devm removeTarget out) :
    Func.RunCompiledTo.RouteTo ⟨removeTargetSlot, []⟩ h removeArrayLengthPath
      (.reg .sstore) :=
  routeTo_line removeArrayLengthPrefix h
    (fun _writeState _writeRun write =>
      routeTo_head write removeArrayLengthPath)

set_option maxRecDepth 8192 in
theorem removeTarget_routeTo_clearTargetIndex {fs : List Func} {sevm : Sevm}
    {devm : Devm} {out : Execution}
    (h : Func.RunCompiledTo fs sevm devm removeTarget out) :
    Func.RunCompiledTo.RouteTo ⟨removeTargetSlot, []⟩ h
      removeClearTargetIndexPath (.reg .sstore) :=
  routeTo_line removeClearTargetIndexPrefix h
    (fun _writeState _writeRun write =>
      routeTo_head write removeClearTargetIndexPath)

/-! ## The kernel leg -/

/-- Inside `setPauserKernel`, a walk with an empty raw payload reaches the
assignment `SSTORE`: the target-is-zero arm calls `PausableZero`, whose payload
is not empty.  The `.ok` version of this leg
(`setPauserKernel_routeTo_assignment_ok`) settles the same branch from the
successful outcome; this is its raw-revert dual. -/
theorem setPauserKernel_routeTo_assignment_revert (dp : DeployParams)
    {sevm : Sevm} {devm raw : Devm}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      setPauserKernel (.error (.revert, raw)))
    (emptyOutput : raw.output = []) :
    Func.RunCompiledTo.RouteTo ⟨setPauserSlot, []⟩ h
      setPauserAssignmentPath (.reg .sstore) := by
  refine routeTo_line setPauserKernelZeroCheck h
    (fun _zeroCheck _lineRun tail => ?_)
  refine routeTo_branchLeft_of_rightRefuted tail
    (fun _start armRun =>
      call_namedError_refuted "PausableZero" (runtime_error_lookups dp).1
        emptyOutput armRun)
    (fun _armStart _pop arm => ?_)
  refine routeTo_line setPauserKernelAssignmentPrefix arm
    (fun _writeState _writeRun write => ?_)
  have pathEq :
      ((([] ++ List.replicate setPauserKernelZeroCheck.length
              Prog.SourceStep.rest) ++ [Prog.SourceStep.branchLeft]) ++
          List.replicate setPauserKernelAssignmentPrefix.length
            Prog.SourceStep.rest) =
        setPauserAssignmentPath.steps := by
    simp [setPauserAssignmentPath, setPauserKernelZeroCheck,
      setPauserKernelAssignmentPrefix]
  exact pathEq ▸ routeTo_head write setPauserAssignmentPath

/-- The `.call setPauserSlot` crossing on top of the kernel leg. -/
theorem call_setPauserSlot_routeTo_assignment_revert (dp : DeployParams)
    {sevm : Sevm} {devm raw : Devm} {current : Prog.SourcePath}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      (.call setPauserSlot) (.error (.revert, raw)))
    (emptyOutput : raw.output = []) :
    Func.RunCompiledTo.RouteTo current h setPauserAssignmentPath
      (.reg .sstore) :=
  routeTo_call h (by simp [runtime, aux, setPauserSlot])
    fun _kernelStart _burn tail =>
      setPauserKernel_routeTo_assignment_revert dp tail emptyOutput

end Blanc.LidoCircuitBreaker
