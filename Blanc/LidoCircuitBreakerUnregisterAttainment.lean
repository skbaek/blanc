import Blanc.LidoCircuitBreakerPauseAttainment
import Blanc.LidoCircuitBreakerUnregisterWorld

/-!
# Attaining the removal rows with `.adminRegistry` authority

`Blanc/LidoCircuitBreakerPauseAttainment.lean` closes the `.pauseRegistry` half
of the `setPauser.oldCount` row and the five `removeTarget` rows, at a walk
that reverts.  This module closes the `.adminRegistry` half of the same six
rows, at a walk that **succeeds**.

The flow is the admin unregistration `registerPauser(target, 0)` against a
target that is already recorded: the kernel's previous-pauser test finds a
nonzero assignment and takes the old-count arm, and `afterOldPauser`'s
memory-valued test finds the staged new pauser zero and enters `removeTarget`.
Every one of the six rows is therefore reached on one walk, exactly as the
pause route reaches them -- the two roles differ, the code path does not, which
is the same sharing the deployed Solidity has between `registerPauser` and
`pause`.

**What these six witnesses say beyond the pause six.**  The pause witnesses
reach their rows inside an execution that then reverts, so they establish
reachability of the *site* and nothing about persistence.  These are rooted at
a concrete `Msg` whose run ends `.ok`, so the same six sites are reached in a
transaction that succeeds.  That is still not a claim that the write survives
into the next block: `Attainable` is a raw-occurrence predicate and says
nothing about the poststate.  It is the correct dual of AT5, which quantifies
over raw same-frame writes without regard to outcome.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-! ## What `registerPauser`'s staging line puts in memory

`pauseStaging_windows` does this for `pause`'s staging line.  This is the same
statement for `registerPauser`'s, which stages the call's *second* argument at
`newPauserWord` rather than a literal zero -- so the zero the kernel branches
on is an antecedent here (`hnew`) rather than a fact about the line. -/

/-- `registerPauser`'s staging line leaves the call's target argument at
`targetWord` and its new-pauser argument at `newPauserWord`.  At an
unregistering call the latter is zero, which is what routes the shared kernel
into `removeTarget`. -/
theorem registerStaging_windows {sevm : Sevm} {stage devm' : Devm} {img : Bytes}
    (image : MemImage stage img)
    (hnew : Sevm.argWord sevm 1 = 0)
    (run : Line.Run sevm stage registerStagingLine devm') :
    MemWordAt devm' (targetWord * 32).toNat (Sevm.argWord sevm 0) ∧
      MemWordAt devm' (newPauserWord * 32).toNat 0 := by
  unfold registerStagingLine at run
  rcases of_run_append (arg 0) run with ⟨_s1, r1, run⟩
  have p1 : Sevm.argWord sevm 0 :: [] <<+ _s1.stack :=
    prefix_of_arg nil_pref r1
  have i1 : MemImage _s1 img :=
    MemImage.of_memory_eq (Line.of_inv Devm.memory (by line_inv) r1).symm image
  rcases of_run_append (mstoreAt targetWord) run with ⟨_s2, r2, run⟩
  obtain ⟨p2, hm2⟩ := of_run_mstoreAt_val r2 p1
  have wT2 : MemWordAt _s2 (targetWord * 32).toNat (Sevm.argWord sevm 0) :=
    MemWordAt.of_write i1 hm2
  have i2 := i1.write hm2
  rcases of_run_append (arg 1) run with ⟨_s3, r3, run⟩
  have p3 := prefix_of_arg p2 r3
  have i3 :=
    MemImage.of_memory_eq (Line.of_inv Devm.memory (by line_inv) r3).symm i2
  have wT3 := wT2.acrossLine (by line_inv) r3
  rcases of_run_append (mstoreAt newPauserWord) run with ⟨_s4, r4, run⟩
  obtain ⟨p4, hm4⟩ := of_run_mstoreAt_val r4 p3
  have wN4 : MemWordAt _s4 (newPauserWord * 32).toNat 0 := by
    rw [← hnew]
    exact MemWordAt.of_write i3 hm4
  have wT4 := MemWordAt.writeMiss hm4 (by decide) wT3
  rcases of_run_append [Ninst.pushB256 0] run with ⟨_s5, r5, run⟩
  have p5 : (0 : B256) :: [] <<+ _s5.stack := by
    rcases Line.of_run_cons r5 with ⟨_u, qu, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 qu) p4
  have wT5 := wT4.acrossLine (by line_inv) r5
  have wN5 := wN4.acrossLine (by line_inv) r5
  rcases of_run_append (mstoreAt previousPauserWord) run with ⟨_s6, r6, run⟩
  obtain ⟨p6, _hm6⟩ := of_run_mstoreAt_val r6 p5
  have wT6 := wT5.acrossMstoreAt (by decide) r6
  have wN6 := wN5.acrossMstoreAt (by decide) r6
  rcases of_run_append [Ninst.pushB256 0] run with ⟨_s7, r7, run⟩
  have p7 : (0 : B256) :: [] <<+ _s7.stack := by
    rcases Line.of_run_cons r7 with ⟨_u, qu, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 qu) p6
  have wT7 := wT6.acrossLine (by line_inv) r7
  have wN7 := wN6.acrossLine (by line_inv) r7
  exact ⟨wT7.acrossMstoreAt (by decide) run,
    wN7.acrossMstoreAt (by decide) run⟩

/-! ## The kernel legs, on a successful outcome

`Blanc/LidoCircuitBreakerPauseGuards.lean` states these three legs for a walk
that ends `.error (.revert, raw)` with an empty payload, which is what refutes
the kernel's `PausableZero` arm there.  These are the same legs with the
successful outcome doing that work instead -- `routeTo_branchLeft_of_rightRevertsOk`
in place of `call_namedError_refuted`.  Everything after the first branch is
shared: `pauseKernel_previousPauserNonzero` is outcome-generic, and so are all
five `removeTarget_routeTo_*` lemmas. -/

/-- From `setPauserKernel`'s entry to the old-count arm, on a successful walk:
the target-zero test (free, its other arm is `PausableZero`, which cannot end
`.ok`) and the previous-pauser test (paid for out of the entry storage). -/
theorem setPauserKernel_routeTo_oldCountArm_ok (dp : DeployParams)
    {sevm : Sevm} {devm post : Devm} {target : B256}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      setPauserKernel (.ok post))
    (windowT : MemWordAt devm (targetWord * 32).toNat target)
    (windowN : MemWordAt devm (newPauserWord * 32).toNat 0)
    (assigned :
      Devm.getStorVal devm sevm.currentTarget (assignmentSlot target) ≠ 0)
    (armRoute : ∀ devm' : Devm,
      MemWordAt devm' (newPauserWord * 32).toNat 0 →
      ∀ tail : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm
        devm' (oldCountPrefix +++ (Ninst.sstore ::: .call afterOldPauserSlot))
        (.ok post),
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
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail (fuel := 8) (by rfl)
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

/-- The `setPauser.oldCount` row on a successful walk. -/
theorem setPauserKernel_routeTo_oldCount_ok (dp : DeployParams)
    {sevm : Sevm} {devm post : Devm} {target : B256}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      setPauserKernel (.ok post))
    (windowT : MemWordAt devm (targetWord * 32).toNat target)
    (windowN : MemWordAt devm (newPauserWord * 32).toNat 0)
    (assigned :
      Devm.getStorVal devm sevm.currentTarget (assignmentSlot target) ≠ 0) :
    Func.RunCompiledTo.RouteTo ⟨setPauserSlot, []⟩ h setPauserOldCountPath
      (.reg .sstore) :=
  setPauserKernel_routeTo_oldCountArm_ok dp h windowT windowN assigned
    (fun _devm' _wN tail =>
      routeTo_line oldCountPrefix tail
        (fun _writeState _writeRun write =>
          routeTo_head write setPauserOldCountPath))

/-- From `setPauserKernel`'s entry to `removeTarget`'s entry, on a successful
walk.  `afterOldPauser`'s test is memory-valued, and the window it reads is the
staged zero the unregistering call put there. -/
theorem setPauserKernel_routeTo_removeTarget_ok (dp : DeployParams)
    {sevm : Sevm} {devm post : Devm} {target : B256}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      setPauserKernel (.ok post))
    (windowT : MemWordAt devm (targetWord * 32).toNat target)
    (windowN : MemWordAt devm (newPauserWord * 32).toNat 0)
    (assigned :
      Devm.getStorVal devm sevm.currentTarget (assignmentSlot target) ≠ 0)
    (bodyRoute : ∀ devm' : Devm,
      ∀ tail : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm
        devm' removeTarget (.ok post),
        Func.RunCompiledTo.RouteTo ⟨removeTargetSlot, []⟩ tail targetPath
          targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨setPauserSlot, []⟩ h targetPath
      targetInstruction := by
  refine setPauserKernel_routeTo_oldCountArm_ok dp h windowT windowN assigned
    (fun _devm' wN tail => ?_)
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

/-! ## The whole route, at the unregistration world -/

/-- Program entry to `setPauserKernel`'s own root at the unregistration world.
Twelve branches: six selector comparisons decided on the concrete calldata
selector, and six settled by certified-reverting siblings under the successful
outcome.  Not one branch word is computed before the kernel. -/
theorem runtimeMain_routeTo_unregisterKernel {devm post : Devm}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      unregWorldSevm devm (runtime officialParams).main (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor unregWorldPre)
    (hmem : devm.memory = unregWorldPre.memory)
    (kernelRoute : ∀ kernelStart : Devm,
      MemWordAt kernelStart (targetWord * 32).toNat unregWorldTarget →
      MemWordAt kernelStart (newPauserWord * 32).toNat 0 →
      Devm.getStor kernelStart = Devm.getStor unregWorldPre →
      ∀ tail : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        unregWorldSevm kernelStart setPauserKernel (.ok post),
        Func.RunCompiledTo.RouteTo ⟨setPauserSlot, []⟩ tail targetPath
          targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h targetPath targetInstruction := by
  refine routeTo_line runtimeMainEntryPrefix h (fun _entry erun tail => ?_)
  have g0 := (Line.of_inv Devm.getStor (by line_inv) erun).symm.trans hstor
  have n0 := (Line.of_inv Devm.memory (by line_inv) erun).symm.trans hmem
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail (fuel := 4) (by rfl)
    (fun _body hpop arm => ?_)
  have g1 := (getStor_of_state hpop.state).symm.trans g0
  have n1 := hpop.memory.symm.trans n0
  refine dispatch_routeTo_registerPauser officialParams arm unregWorld_selector
    (fun _current _devm' dstor dmem bodyTail => ?_)
  refine registerPauser_routeTo_setPauserCall officialParams bodyTail
    (fun _c _stage _d rstor rmem staging callTail => ?_)
  have hstage := (rmem.trans (dmem.trans n1)).trans unregWorld_memory
  obtain ⟨wT, wN⟩ :=
    registerStaging_windows
      (img := [])
      ⟨by rw [hstage]; exact Mem.wf_empty, by rw [hstage]; exact Mem.reads_empty⟩
      unregWorld_argNew staging
  refine routeTo_call callTail (by rfl) (fun kernelStart kburn ktail => ?_)
  exact kernelRoute kernelStart
    (by
      rw [← unregWorld_argTarget]
      exact MemWordAt.of_memory_eq kburn.memory.symm wT)
    (MemWordAt.of_memory_eq kburn.memory.symm wN)
    ((getStor_of_state kburn.state).symm.trans
      (rstor.trans (dstor.trans g1)))
    ktail

/-! ## The shared tail

`attainable_pauseRegistry_of_route` is this statement at the pause world; this
is the same tail at the unregistration world, with the roles exchanged.  There
the `.adminRegistry` disjunct is closed because a pause caller is not the
admin; here the `.pauseRegistry` disjunct is closed because the target's
recorded pauser is not the caller -- the admin is not pauser `9`. -/

/-- Any route from the runtime's entry to a persistent-write site attains, at
the admin unregistration world, the row that owns that site -- with the
`.adminRegistry` role. -/
theorem attainable_adminRegistry_of_route {row : RuntimePersistentWrite}
    {path : Prog.SourcePath}
    (roles : row.permittedRoles = [.adminRegistry, .pauseRegistry])
    (pin : ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some path) → index = row.index)
    (route : ∀ (devm post : Devm),
      Devm.getStor devm = Devm.getStor unregWorldPre →
      devm.memory = unregWorldPre.memory →
      ∀ h : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        unregWorldSevm devm (runtime officialParams).main (.ok post),
        Func.RunCompiledTo.RouteTo ⟨0, []⟩ h path (.reg .sstore)) :
    Attainable officialParams row .adminRegistry := by
  obtain ⟨post, hrun, hcompile⟩ := unregisterWorld_run
  obtain ⟨mid, hburn, hwalk⟩ := hrun
  have hroute := route mid post (getStor_of_state hburn.state).symm
    hburn.memory.symm hwalk
  obtain ⟨exc, occurrence, site, hpath, hmem, hpc, hinstr, hinstrTarget,
    sameFrame⟩ :=
    Prog.exec_of_runCompiledTo_routeTo hburn hroute hcompile
  have invocation :
      (⟨0, unregWorldSevm, unregWorldPre, .ok post, exc⟩ :
          Exec.Deriv).exactInvocation
        (runtime officialParams) unregWorldOwner unregWorldOwner :=
    ⟨rfl, unregWorld_currentTarget, unregWorld_codeAddress, hcompile⟩
  have instructionEq : occurrence.instruction = .reg .sstore :=
    hinstr.trans hinstrTarget
  obtain ⟨found, rowSite, _rowMem, foundSite, _classified, rowSitePc,
    _rowInstr, _unique, role, rolePermitted, authority⟩ :=
    Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot occurrence
      instructionEq (Exec.mem_rawFrameRoots_self exc) invocation sameFrame
  have routedMember : site ∈ runtimePersistentSourceSites officialParams := by
    unfold runtimePersistentSourceSites
    rw [List.mem_filter]
    exact ⟨hmem, by simp [hinstrTarget, isPersistentWriteInstruction]⟩
  have siteEq : rowSite = site :=
    runtimePersistentSourceSite_eq_of_pc
      (RuntimePersistentWrite.mem_runtimePersistentSourceSites foundSite)
      routedMember (rowSitePc.trans hpc)
  have rowEq : found = row := by
    have official := RuntimePersistentWrite.sourceSite?_official foundSite
    unfold RuntimePersistentWrite.sourceSite? at official
    have mapped :
        (runtimePersistentSourceSites officialParams)[found.index]?.map
          (fun s => s.path) = some path := by
      rw [official]
      exact congrArg some (siteEq ▸ hpath)
    exact RuntimePersistentWrite.index_injective
      (pin found.index (List.mem_range.mpr (by have := found.index_lt; omega))
        mapped)
  subst rowEq
  have roleEq : role = .adminRegistry := by
    have alternatives : role = .adminRegistry ∨ role = .pauseRegistry := by
      simpa [roles] using rolePermitted
    rcases alternatives with rfl | rfl
    · rfl
    · exfalso
      cases authority with
      | pauseRegistry _endpoint _assignedGuard _liveGuard assigned _live
          _writeSite =>
          rw [show (⟨0, unregWorldSevm, unregWorldPre, .ok post, exc⟩ :
                Exec.Deriv).sevm = unregWorldSevm from rfl,
            show (⟨0, unregWorldSevm, unregWorldPre, .ok post, exc⟩ :
                Exec.Deriv).devm = unregWorldPre from rfl,
            unregWorld_currentTarget, unregWorld_dataWord_target,
            unregWorld_assignment, unregWorld_admin] at assigned
          exact absurd assigned (by decide)
  subst roleEq
  exact ⟨unregWorldOwner,
    ⟨0, unregWorldSevm, unregWorldPre, .ok post, exc⟩,
    ⟨0, unregWorldSevm, unregWorldPre, .ok post, exc⟩, occurrence, rowSite,
    instructionEq, Exec.mem_rawFrameRoots_self exc, invocation, sameFrame,
    foundSite, rowSitePc, authority⟩

/-! ## The witnesses

The six index pins are the ones `Blanc/LidoCircuitBreakerPauseAttainment.lean`
already proved: an inventory pin says which row owns a path and is indifferent
to which world reaches it, so nothing is re-decided here. -/

/-- The world's kernel branch premise: the target is recorded, so the
previous-pauser test sends the walk down the old-count arm. -/
private theorem unregWorld_assigned {kernelStart : Devm}
    (hstor : Devm.getStor kernelStart = Devm.getStor unregWorldPre) :
    Devm.getStorVal kernelStart unregWorldSevm.currentTarget
      (assignmentSlot unregWorldTarget) ≠ 0 := by
  rw [unregWorld_currentTarget,
    show Devm.getStorVal kernelStart unregWorldOwner
        (assignmentSlot unregWorldTarget)
      = Devm.getStorVal unregWorldPre unregWorldOwner
        (assignmentSlot unregWorldTarget) from
      congrArg (fun f : Adr → Stor =>
        (f unregWorldOwner).get (assignmentSlot unregWorldTarget)) hstor,
    unregWorld_assignment]
  decide

/-- The `setPauser.oldCount` row, with the `.adminRegistry` role. -/
theorem attainable_setPauserOldCount_adminRegistry :
    Attainable officialParams .setPauserOldCount .adminRegistry :=
  attainable_adminRegistry_of_route rfl setPauserOldCount_pause_index_pin
    (fun _devm _post hstor hmem h =>
      runtimeMain_routeTo_unregisterKernel h hstor hmem
        (fun _kernelStart wT wN kstor ktail =>
          setPauserKernel_routeTo_oldCount_ok officialParams ktail wT wN
            (unregWorld_assigned kstor)))

/-- The `remove.arrayHole` row, with the `.adminRegistry` role. -/
theorem attainable_removeArrayHole_adminRegistry :
    Attainable officialParams .removeArrayHole .adminRegistry :=
  attainable_adminRegistry_of_route rfl removeArrayHole_pause_index_pin
    (fun _devm _post hstor hmem h =>
      runtimeMain_routeTo_unregisterKernel h hstor hmem
        (fun _kernelStart wT wN kstor ktail =>
          setPauserKernel_routeTo_removeTarget_ok officialParams ktail wT wN
            (unregWorld_assigned kstor)
            (fun _devm' tail => removeTarget_routeTo_arrayHole tail)))

/-- The `remove.movedIndex` row, with the `.adminRegistry` role. -/
theorem attainable_removeMovedIndex_adminRegistry :
    Attainable officialParams .removeMovedIndex .adminRegistry :=
  attainable_adminRegistry_of_route rfl removeMovedIndex_pause_index_pin
    (fun _devm _post hstor hmem h =>
      runtimeMain_routeTo_unregisterKernel h hstor hmem
        (fun _kernelStart wT wN kstor ktail =>
          setPauserKernel_routeTo_removeTarget_ok officialParams ktail wT wN
            (unregWorld_assigned kstor)
            (fun _devm' tail => removeTarget_routeTo_movedIndex tail)))

/-- The `remove.clearTail` row, with the `.adminRegistry` role. -/
theorem attainable_removeClearTail_adminRegistry :
    Attainable officialParams .removeClearTail .adminRegistry :=
  attainable_adminRegistry_of_route rfl removeClearTail_pause_index_pin
    (fun _devm _post hstor hmem h =>
      runtimeMain_routeTo_unregisterKernel h hstor hmem
        (fun _kernelStart wT wN kstor ktail =>
          setPauserKernel_routeTo_removeTarget_ok officialParams ktail wT wN
            (unregWorld_assigned kstor)
            (fun _devm' tail => removeTarget_routeTo_clearTail tail)))

/-- The `remove.arrayLength` row, with the `.adminRegistry` role. -/
theorem attainable_removeArrayLength_adminRegistry :
    Attainable officialParams .removeArrayLength .adminRegistry :=
  attainable_adminRegistry_of_route rfl removeArrayLength_pause_index_pin
    (fun _devm _post hstor hmem h =>
      runtimeMain_routeTo_unregisterKernel h hstor hmem
        (fun _kernelStart wT wN kstor ktail =>
          setPauserKernel_routeTo_removeTarget_ok officialParams ktail wT wN
            (unregWorld_assigned kstor)
            (fun _devm' tail => removeTarget_routeTo_arrayLength tail)))

/-- The `remove.clearTargetIndex` row, with the `.adminRegistry` role. -/
theorem attainable_removeClearTargetIndex_adminRegistry :
    Attainable officialParams .removeClearTargetIndex .adminRegistry :=
  attainable_adminRegistry_of_route rfl removeClearTargetIndex_pause_index_pin
    (fun _devm _post hstor hmem h =>
      runtimeMain_routeTo_unregisterKernel h hstor hmem
        (fun _kernelStart wT wN kstor ktail =>
          setPauserKernel_routeTo_removeTarget_ok officialParams ktail wT wN
            (unregWorld_assigned kstor)
            (fun _devm' tail => removeTarget_routeTo_clearTargetIndex tail)))

end Blanc.LidoCircuitBreaker
