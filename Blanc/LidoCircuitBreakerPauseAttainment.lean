import Blanc.LidoCircuitBreakerPauseGuards

/-!
# Attaining the Registry rows with `.pauseRegistry` authority

`Blanc/LidoCircuitBreakerAttainment.lean` closes the `.adminRegistry` half of
the `[.adminRegistry, .pauseRegistry]` rows.  This module closes the pause
half, at the world `directPause_zeroCode_postWrite_error_control` already
publishes: target `7` assigned to the live caller `9` in a singleton Registry
owned by address `100`, with the target account holding no code.

**What the witnesses below say, exactly.**  They say the row's frozen source
site is *reached*, in an exact runtime invocation, by a raw occurrence carrying
`.pauseRegistry` authority.  The enclosing execution then reverts, and the
control's own settlement conjunct says the entry Registry witness is restored.
That is the correct dual of AT5's raw-outcome soundness claim -- AT5
quantifies over raw same-frame writes without regard to the frame's outcome,
so a rolled-back write is precisely what its permitted-role table has to
account for.  It must not be paraphrased as "a pause can persist a Registry
change": no persistence is claimed, and the same control proves the opposite.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

set_option maxRecDepth 16384 in
/-- The complete pause route: `runtimeMain`'s entry guard, the three
`hybridDispatchWith` selector crossings, `pause`'s five guards, and the
`.call setPauserSlot` leg into the shared Registry kernel, ending at the
`setPauser.assignment` `SSTORE`.

Ten branch crossings, of which four are free: the reentrancy lock, the
caller-assignment guard, the heartbeat-liveness guard and the kernel's
target-zero test are all settled by `raw.output = []`.  The six that remain
are the calldata- and value-valued ones, so no world projection is threaded
anywhere on this route. -/
theorem runtimeMain_routeTo_pauseAssignment (dp : DeployParams)
    {sevm : Sevm} {devm raw : Devm}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      (runtime dp).main (.error (.revert, raw)))
    (emptyOutput : raw.output = [])
    (accepted : ∀ entry : Devm,
      Line.Run sevm devm runtimeMainEntryPrefix entry →
      ∀ (w : B256) (rest : Stack), entry.stack = w :: rest → w = 0)
    (selectorEq : Sevm.selector sevm = selector "pause" [.address])
    (argsPresent : ∀ start mid : Devm,
      Line.Run sevm start pauseStaticArgsTest mid →
      ∀ (w : B256) (rest : Stack), mid.stack = w :: rest → w = 0)
    (targetCanonical : ∀ start mid : Devm,
      Line.Run sevm start (arg 0 ++ checkNonAddress) mid →
      ∀ (w : B256) (rest : Stack), mid.stack = w :: rest → w = 0) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h setPauserAssignmentPath
      (.reg .sstore) := by
  refine runtimeMain_routeTo_dispatch dp h accepted (fun _entry arm => ?_)
  exact dispatch_routeTo_pause dp arm selectorEq
    (fun _current _devm' _stor _mem _code bodyTail =>
      pause_routeTo_setPauserCall dp bodyTail emptyOutput argsPresent
        targetCanonical
        (fun _c _stage _d _stor' _mem' _staging callTail =>
          call_setPauserSlot_routeTo_assignment_revert dp callTail emptyOutput))

/-! ## The pause world's calldata facts

`pause(address)` calldata is thirty-six bytes: a four-byte selector and one
head word.  All four branch words this route still has to compute are read off
those thirty-six bytes and the call's zero value, so they are settled here once
and for all, before any execution is looked at. -/

/-- What `pauseCalldata` says about the two target-independent calldata reads
on this route. -/
theorem pauseCalldata_facts {sevm : Sevm} {target : B256}
    (hd : sevm.data = pauseCalldata target) :
    sevm.data.length = 36 ∧ Sevm.argWord sevm 0 = target := by
  refine ⟨?_, ?_⟩
  · rw [hd]
    simp [pauseCalldata, abiSelectorBytes_length, B256.length_toBytes]
  · show Sevm.dataWord sevm ((32 * 0) + 4) = target
    apply dataWord_of_append
      (pre := abiSelectorBytes (selector "pause" [.address])) (post := [])
    · rw [abiSelectorBytes_length]
      rfl
    · rw [hd]
      rfl

set_option maxRecDepth 8192 in
/-- The dispatcher's selector, at the control world's own calldata.  Stated at
the concrete target because `Sevm.dataWord` reads a whole word: the selector
occupies the first four bytes and the argument the next twenty-eight of the
same word, and separating them takes an evaluation rather than a lemma. -/
theorem pauseCalldata_selector {sevm : Sevm}
    (hd : sevm.data = pauseCalldata (7 : B256)) :
    Sevm.selector sevm = selector "pause" [.address] := by
  show Sevm.dataWord sevm 0 >>> 224 = _
  unfold Sevm.dataWord
  rw [hd]
  decide

/-! ## The four surviving branch words

None of them reads the world.  `runtimeMain`'s entry guard reads the call's
value and the calldata length; `requireStaticArgs` reads the length alone; the
canonical-address guard reads the head word; and the dispatcher's three pivots
read the selector. -/

/-- `runtimeMain`'s entry guard falls through for a zero-value call whose
calldata carries at least a selector. -/
theorem entryGuard_word {sevm : Sevm} {devm : Devm}
    (hvalue : sevm.value = 0) (hlen : sevm.data.length = 36) :
    ∀ entry : Devm, Line.Run sevm devm runtimeMainEntryPrefix entry →
      ∀ (w : B256) (rest : Stack), entry.stack = w :: rest → w = 0 := by
  intro entry lineRun w rest hstack
  unfold runtimeMainEntryPrefix at lineRun
  rcases Line.of_run_cons lineRun with ⟨_u1, q1, r1⟩
  rcases Line.of_run_cons r1 with ⟨_u2, q2, r2⟩
  rcases Line.of_run_cons r2 with ⟨_u3, q3, r3⟩
  rcases Line.of_run_cons r3 with ⟨_u4, q4, r4⟩
  rcases Line.of_run_cons r4 with ⟨_u5, q5, r5⟩
  cases r5
  have p1 : sevm.value :: [] <<+ _u1.stack :=
    prefix_of_push (of_run_callvalue q1) nil_pref
  have p2 := prefix_of_push (of_run_pushB256 q2) p1
  have p3 := prefix_of_calldatasize q3 p2
  have p4 := prefix_of_lt q4 p3
  have p5 := prefix_of_or q5 p4
  rw [head_of_stack_prefix p5 hstack, hvalue, hlen]
  decide

/-- `requireStaticArgs 1` falls through for thirty-six bytes of calldata. -/
theorem staticArgs_word {sevm : Sevm} (hlen : sevm.data.length = 36) :
    ∀ start mid : Devm, Line.Run sevm start pauseStaticArgsTest mid →
      ∀ (w : B256) (rest : Stack), mid.stack = w :: rest → w = 0 := by
  intro start mid lineRun w rest hstack
  unfold pauseStaticArgsTest at lineRun
  rcases Line.of_run_cons lineRun with ⟨_u1, q1, r1⟩
  rcases Line.of_run_cons r1 with ⟨_u2, q2, r2⟩
  rcases Line.of_run_cons r2 with ⟨_u3, q3, r3⟩
  cases r3
  have p1 := prefix_of_push (of_run_pushB256 q1) nil_pref
  have p2 := prefix_of_calldatasize q2 p1
  have p3 := prefix_of_lt q3 p2
  rw [head_of_stack_prefix p3 hstack, hlen]
  decide

/-- `canonicalAddressArg 0` falls through for an address-shaped head word. -/
theorem canonicalArg_word {sevm : Sevm}
    (hvalid : ValidAdr (Sevm.argWord sevm 0)) :
    ∀ start mid : Devm, Line.Run sevm start (arg 0 ++ checkNonAddress) mid →
      ∀ (w : B256) (rest : Stack), mid.stack = w :: rest → w = 0 := by
  intro start mid lineRun w rest hstack
  obtain ⟨_y, hy, hiff⟩ := prefix_of_argCheckNonAddress nil_pref lineRun
  rw [head_of_stack_prefix hy hstack]
  exact hiff.mpr hvalid


set_option maxRecDepth 16384 in
/-- The whole pause route down to `setPauserKernel`'s entry, with the two
memory windows the kernel reads and the storage relation its second branch
needs.  Every row past the assignment write is reached through this. -/
theorem runtimeMain_routeTo_pauseKernel (dp : DeployParams)
    {sevm : Sevm} {devm raw : Devm} {img : Bytes}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      (runtime dp).main (.error (.revert, raw)))
    (emptyOutput : raw.output = [])
    (image : MemImage devm img)
    (accepted : ∀ entry : Devm,
      Line.Run sevm devm runtimeMainEntryPrefix entry →
      ∀ (w : B256) (rest : Stack), entry.stack = w :: rest → w = 0)
    (selectorEq : Sevm.selector sevm = selector "pause" [.address])
    (argsPresent : ∀ start mid : Devm,
      Line.Run sevm start pauseStaticArgsTest mid →
      ∀ (w : B256) (rest : Stack), mid.stack = w :: rest → w = 0)
    (targetCanonical : ∀ start mid : Devm,
      Line.Run sevm start (arg 0 ++ checkNonAddress) mid →
      ∀ (w : B256) (rest : Stack), mid.stack = w :: rest → w = 0)
    (kernelRoute : ∀ kernelStart : Devm,
      MemWordAt kernelStart (targetWord * 32).toNat (Sevm.argWord sevm 0) →
      MemWordAt kernelStart (newPauserWord * 32).toNat 0 →
      Devm.getStor kernelStart = Devm.getStor devm →
      ∀ tail : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm
        kernelStart setPauserKernel (.error (.revert, raw)),
        Func.RunCompiledTo.RouteTo ⟨setPauserSlot, []⟩ tail targetPath
          targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h targetPath targetInstruction := by
  refine routeTo_line runtimeMainEntryPrefix h (fun entry lineRun tail => ?_)
  have ge : Devm.getStor entry = Devm.getStor devm :=
    (Line.of_inv Devm.getStor (by unfold runtimeMainEntryPrefix; line_inv)
      lineRun).symm
  have me : entry.memory = devm.memory :=
    (Line.of_inv Devm.memory (by unfold runtimeMainEntryPrefix; line_inv)
      lineRun).symm
  refine routeTo_branchLeft_frame tail (accepted entry lineRun)
    (fun body hpop arm => ?_)
  have gb := (getStor_of_state hpop.state).symm.trans ge
  have mb := hpop.memory.symm.trans me
  refine dispatch_routeTo_pause dp arm selectorEq
    (fun _current pauseEntry hstor hmem _code bodyTail => ?_)
  refine pause_routeTo_setPauserCall dp bodyTail emptyOutput argsPresent
    targetCanonical
    (fun _c _stage callState hstor' hmem' staging callTail => ?_)
  obtain ⟨wT, wN⟩ := pauseStaging_windows
    (MemImage.of_memory_eq (hmem'.trans (hmem.trans mb)) image) staging
  refine routeTo_call (body := setPauserKernel) callTail
    (by simp [runtime, aux, setPauserSlot]) (fun kernelStart kburn ktail => ?_)
  exact kernelRoute kernelStart
    (MemWordAt.of_memory_eq kburn.memory.symm wT)
    (MemWordAt.of_memory_eq kburn.memory.symm wN)
    ((getStor_of_state kburn.state).symm.trans
      (hstor'.trans (hstor.trans gb))) ktail

/-! ## The shared pause-world tail

Everything after a route is the same for every row on it: the walk becomes an
`Exec`, its occurrence sits at the routed path, the frame is the exact runtime
invocation the control publishes, AT5 hands back the row that owns the reached
PC together with one of that row's permitted roles, and the role is
`.pauseRegistry` because the caller is not the admin.

The `roles` premise is what closes the `.adminRegistry` disjunct.  The fresh
registration tail closes the *other* disjunct at the same rows, and does it
with the world's storage (`assignment[target] ≠ caller`); here the natural
discriminator is the caller itself, since a `pause` invocation is by
construction not an admin one. -/

set_option maxRecDepth 16384 in
/-- Any route from the runtime's entry to a persistent-write site attains, at
the published codeless-target pause world, the row that owns that site -- with
the `.pauseRegistry` role. -/
theorem attainable_pauseRegistry_of_route {row : RuntimePersistentWrite}
    {path : Prog.SourcePath}
    (roles : row.permittedRoles = [.adminRegistry, .pauseRegistry])
    (pin : ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some path) → index = row.index)
    (route : ∀ (sevm : Sevm) (mid raw : Devm),
      sevm.value = 0 →
      sevm.data = pauseCalldata (7 : B256) →
      sevm.currentTarget = Nat.toAdr 100 →
      Devm.getStorVal mid (Nat.toAdr 100) (assignmentSlot (7 : B256)) = 9 →
      raw.output = [] →
      MemImage mid [] →
      ∀ h : Func.RunCompiledTo ((runtime officialParams).main ::
          (runtime officialParams).aux) sevm mid
          (runtime officialParams).main (.error (.revert, raw)),
        Func.RunCompiledTo.RouteTo ⟨0, []⟩ h path (.reg .sstore)) :
    Attainable officialParams row .pauseRegistry := by
  obtain ⟨msg, sevm, pre, raw, _htarget, howner, hcodeAddress, hcode, hvalue,
    hdata, hsevm, hpre, _hframe, _hwitness, hcaller, hassignment, _hexpiry,
    _hlive, _htargetNe, _hcanonical, _hzeroCode, hrun, _rootExec, houtput,
    _evidence, _post, _hprocess, _herror, _hrestored⟩ :=
    directPause_zeroCode_postWrite_error_control
  obtain ⟨mid, hburn, hwalk⟩ := hrun
  have hcompile :
      some sevm.code.toList = Prog.compile (runtime officialParams) := by
    rw [hsevm]
    show some msg.code.toList = _
    rw [hcode, lidoCircuitBreakerCode_compile]
  have hmidStor : Devm.getStorVal mid (Nat.toAdr 100)
      (assignmentSlot (7 : B256)) = 9 := by
    rw [show Devm.getStorVal mid (Nat.toAdr 100) (assignmentSlot (7 : B256))
          = pre.getStorVal (Nat.toAdr 100) (assignmentSlot (7 : B256)) from
        congrArg (fun w : State => (w.get (Nat.toAdr 100)).stor.get
          (assignmentSlot (7 : B256))) hburn.state.symm]
    exact hassignment
  have himage : MemImage mid [] :=
    MemImage.of_memory_eq hburn.memory.symm
      (by rw [hpre]; exact ⟨Mem.wf_empty, Mem.reads_empty⟩)
  have hroute := route sevm mid raw (by rw [hsevm]; exact hvalue)
    (by rw [hsevm]; exact hdata) (by rw [hsevm]; exact howner) hmidStor
    houtput himage hwalk
  obtain ⟨exc, occurrence, site, hpath, hmem, hpc, hinstr, hinstrTarget,
    sameFrame⟩ :=
    Prog.exec_of_runCompiledTo_routeTo hburn hroute hcompile
  have invocation :
      (⟨0, sevm, pre, .error (.revert, raw), exc⟩ : Exec.Deriv).exactInvocation
        (runtime officialParams) (Nat.toAdr 100) (Nat.toAdr 100) := by
    refine ⟨rfl, ?_, ?_, hcompile⟩
    · show sevm.currentTarget = Nat.toAdr 100
      rw [hsevm]
      exact howner
    · show sevm.codeAddress = some (Nat.toAdr 100)
      rw [hsevm]
      exact hcodeAddress
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
  have roleEq : role = .pauseRegistry := by
    have alternatives : role = .adminRegistry ∨ role = .pauseRegistry := by
      simpa [roles] using rolePermitted
    rcases alternatives with rfl | rfl
    · exfalso
      cases authority with
      | adminRegistry _endpoint _guard callerEq _writeSite =>
          rw [show (⟨0, sevm, pre, .error (.revert, raw), exc⟩ :
                Exec.Deriv).sevm = sevm from rfl, hcaller] at callerEq
          exact absurd callerEq (by decide)
    · rfl
  subst roleEq
  exact ⟨Nat.toAdr 100, ⟨0, sevm, pre, .error (.revert, raw), exc⟩,
    ⟨0, sevm, pre, .error (.revert, raw), exc⟩, occurrence, rowSite,
    instructionEq, Exec.mem_rawFrameRoots_self exc, invocation, sameFrame,
    foundSite, rowSitePc, authority⟩

/-! ## The witnesses -/

set_option maxRecDepth 20000 in
/-- Only inventory index `3` nominates the `setPauser.assignment` path. -/
theorem setPauserAssignment_pause_index_pin :
    ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some setPauserAssignmentPath) →
        index = RuntimePersistentWrite.setPauserAssignment.index := by
  decide +kernel

/-- The `.setPauserAssignment` row's frozen source site is reached with the
`.pauseRegistry` invocation role. -/
theorem attainable_setPauserAssignment_pauseRegistry :
    Attainable officialParams .setPauserAssignment .pauseRegistry :=
  attainable_pauseRegistry_of_route rfl setPauserAssignment_pause_index_pin
    (fun sevm mid raw hvalue hdata _howner _hassignment houtput _himage h => by
      obtain ⟨hlen, hargWord⟩ := pauseCalldata_facts hdata
      exact runtimeMain_routeTo_pauseAssignment officialParams h houtput
        (entryGuard_word hvalue hlen)
        (pauseCalldata_selector hdata)
        (staticArgs_word hlen)
        (canonicalArg_word (by rw [hargWord]; exact ⟨(7 : B256).toAdr, by decide⟩)))


/-- The canonical-address premise at the control world's target. -/
private theorem pauseWorld_validAdr {sevm : Sevm}
    (hargWord : Sevm.argWord sevm 0 = (7 : B256)) :
    ValidAdr (Sevm.argWord sevm 0) := by
  rw [hargWord]
  exact ⟨(7 : B256).toAdr, by decide⟩

/-- The kernel's storage-valued branch premise, at the control world. -/
private theorem pauseWorld_assigned {sevm : Sevm} {mid kernelStart : Devm}
    (howner : sevm.currentTarget = Nat.toAdr 100)
    (hargWord : Sevm.argWord sevm 0 = (7 : B256))
    (hassigned :
      Devm.getStorVal mid (Nat.toAdr 100) (assignmentSlot (7 : B256)) = 9)
    (hstor : Devm.getStor kernelStart = Devm.getStor mid) :
    Devm.getStorVal kernelStart sevm.currentTarget
      (assignmentSlot (Sevm.argWord sevm 0)) ≠ 0 := by
  rw [howner, hargWord,
    show Devm.getStorVal kernelStart (Nat.toAdr 100) (assignmentSlot (7 : B256))
        = Devm.getStorVal mid (Nat.toAdr 100) (assignmentSlot (7 : B256)) from
      congrArg (fun f : Adr → Stor =>
        (f (Nat.toAdr 100)).get (assignmentSlot (7 : B256))) hstor,
    hassigned]
  decide

set_option maxRecDepth 20000 in
theorem setPauserOldCount_pause_index_pin :
    ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some setPauserOldCountPath) →
        index = RuntimePersistentWrite.setPauserOldCount.index := by
  decide +kernel

set_option maxRecDepth 20000 in
theorem removeArrayHole_pause_index_pin :
    ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some removeArrayHolePath) →
        index = RuntimePersistentWrite.removeArrayHole.index := by
  decide +kernel

set_option maxRecDepth 20000 in
theorem removeMovedIndex_pause_index_pin :
    ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some removeMovedIndexPath) →
        index = RuntimePersistentWrite.removeMovedIndex.index := by
  decide +kernel

set_option maxRecDepth 20000 in
theorem removeClearTail_pause_index_pin :
    ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some removeClearTailPath) →
        index = RuntimePersistentWrite.removeClearTail.index := by
  decide +kernel

set_option maxRecDepth 20000 in
theorem removeArrayLength_pause_index_pin :
    ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some removeArrayLengthPath) →
        index = RuntimePersistentWrite.removeArrayLength.index := by
  decide +kernel

set_option maxRecDepth 20000 in
theorem removeClearTargetIndex_pause_index_pin :
    ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some removeClearTargetIndexPath) →
        index = RuntimePersistentWrite.removeClearTargetIndex.index := by
  decide +kernel

/-- The `setPauser.oldCount` row, with the `.pauseRegistry` role. -/
theorem attainable_setPauserOldCount_pauseRegistry :
    Attainable officialParams .setPauserOldCount .pauseRegistry :=
  attainable_pauseRegistry_of_route rfl setPauserOldCount_pause_index_pin
    (fun _sevm _mid _raw hvalue hdata howner hassigned houtput himage h => by
      obtain ⟨hlen, hargWord⟩ := pauseCalldata_facts hdata
      exact runtimeMain_routeTo_pauseKernel officialParams h houtput himage
        (entryGuard_word hvalue hlen) (pauseCalldata_selector hdata)
        (staticArgs_word hlen) (canonicalArg_word (pauseWorld_validAdr hargWord))
        (fun _kernelStart wT wN hstor ktail =>
          setPauserKernel_routeTo_oldCount officialParams ktail houtput wT wN
            (pauseWorld_assigned howner hargWord hassigned hstor)))

/-- The `remove.arrayHole` row, with the `.pauseRegistry` role. -/
theorem attainable_removeArrayHole_pauseRegistry :
    Attainable officialParams .removeArrayHole .pauseRegistry :=
  attainable_pauseRegistry_of_route rfl removeArrayHole_pause_index_pin
    (fun _sevm _mid _raw hvalue hdata howner hassigned houtput himage h => by
      obtain ⟨hlen, hargWord⟩ := pauseCalldata_facts hdata
      exact runtimeMain_routeTo_pauseKernel officialParams h houtput himage
        (entryGuard_word hvalue hlen) (pauseCalldata_selector hdata)
        (staticArgs_word hlen) (canonicalArg_word (pauseWorld_validAdr hargWord))
        (fun _kernelStart wT wN hstor ktail =>
          setPauserKernel_routeTo_removeTarget officialParams ktail houtput wT
            wN (pauseWorld_assigned howner hargWord hassigned hstor)
            (fun _devm' tail => removeTarget_routeTo_arrayHole tail)))

/-- The `remove.movedIndex` row, with the `.pauseRegistry` role. -/
theorem attainable_removeMovedIndex_pauseRegistry :
    Attainable officialParams .removeMovedIndex .pauseRegistry :=
  attainable_pauseRegistry_of_route rfl removeMovedIndex_pause_index_pin
    (fun _sevm _mid _raw hvalue hdata howner hassigned houtput himage h => by
      obtain ⟨hlen, hargWord⟩ := pauseCalldata_facts hdata
      exact runtimeMain_routeTo_pauseKernel officialParams h houtput himage
        (entryGuard_word hvalue hlen) (pauseCalldata_selector hdata)
        (staticArgs_word hlen) (canonicalArg_word (pauseWorld_validAdr hargWord))
        (fun _kernelStart wT wN hstor ktail =>
          setPauserKernel_routeTo_removeTarget officialParams ktail houtput wT
            wN (pauseWorld_assigned howner hargWord hassigned hstor)
            (fun _devm' tail => removeTarget_routeTo_movedIndex tail)))

/-- The `remove.clearTail` row, with the `.pauseRegistry` role. -/
theorem attainable_removeClearTail_pauseRegistry :
    Attainable officialParams .removeClearTail .pauseRegistry :=
  attainable_pauseRegistry_of_route rfl removeClearTail_pause_index_pin
    (fun _sevm _mid _raw hvalue hdata howner hassigned houtput himage h => by
      obtain ⟨hlen, hargWord⟩ := pauseCalldata_facts hdata
      exact runtimeMain_routeTo_pauseKernel officialParams h houtput himage
        (entryGuard_word hvalue hlen) (pauseCalldata_selector hdata)
        (staticArgs_word hlen) (canonicalArg_word (pauseWorld_validAdr hargWord))
        (fun _kernelStart wT wN hstor ktail =>
          setPauserKernel_routeTo_removeTarget officialParams ktail houtput wT
            wN (pauseWorld_assigned howner hargWord hassigned hstor)
            (fun _devm' tail => removeTarget_routeTo_clearTail tail)))

/-- The `remove.arrayLength` row, with the `.pauseRegistry` role. -/
theorem attainable_removeArrayLength_pauseRegistry :
    Attainable officialParams .removeArrayLength .pauseRegistry :=
  attainable_pauseRegistry_of_route rfl removeArrayLength_pause_index_pin
    (fun _sevm _mid _raw hvalue hdata howner hassigned houtput himage h => by
      obtain ⟨hlen, hargWord⟩ := pauseCalldata_facts hdata
      exact runtimeMain_routeTo_pauseKernel officialParams h houtput himage
        (entryGuard_word hvalue hlen) (pauseCalldata_selector hdata)
        (staticArgs_word hlen) (canonicalArg_word (pauseWorld_validAdr hargWord))
        (fun _kernelStart wT wN hstor ktail =>
          setPauserKernel_routeTo_removeTarget officialParams ktail houtput wT
            wN (pauseWorld_assigned howner hargWord hassigned hstor)
            (fun _devm' tail => removeTarget_routeTo_arrayLength tail)))

/-- The `remove.clearTargetIndex` row, with the `.pauseRegistry` role. -/
theorem attainable_removeClearTargetIndex_pauseRegistry :
    Attainable officialParams .removeClearTargetIndex .pauseRegistry :=
  attainable_pauseRegistry_of_route rfl removeClearTargetIndex_pause_index_pin
    (fun _sevm _mid _raw hvalue hdata howner hassigned houtput himage h => by
      obtain ⟨hlen, hargWord⟩ := pauseCalldata_facts hdata
      exact runtimeMain_routeTo_pauseKernel officialParams h houtput himage
        (entryGuard_word hvalue hlen) (pauseCalldata_selector hdata)
        (staticArgs_word hlen) (canonicalArg_word (pauseWorld_validAdr hargWord))
        (fun _kernelStart wT wN hstor ktail =>
          setPauserKernel_routeTo_removeTarget officialParams ktail houtput wT
            wN (pauseWorld_assigned howner hargWord hassigned hstor)
            (fun _devm' tail => removeTarget_routeTo_clearTargetIndex tail)))

end Blanc.LidoCircuitBreaker
