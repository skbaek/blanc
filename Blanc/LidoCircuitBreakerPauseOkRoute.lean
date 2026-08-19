import Blanc.LidoCircuitBreakerPauseAttainment

/-!
# The pause `.ok` routes to the expiry `SSTORE`

`Blanc/LidoCircuitBreakerPauseAttainment.lean` routes a `pause(address)` walk
that ends `.error (.revert, raw)` with an empty payload; that flavour reaches
the six Registry rows a codeless-target pause reaches, and no further.  The
two pause expiry rows — inventory indices 18 and 19 — sit past `pauseAfterSet`'s
two returning external calls, and a walk that reaches either of their `SSTORE`s
ends in `STOP`, so their routes need the `.ok` flavour throughout.

Everything before `pauseSuccess`'s count branch is cheaper in this flavour
than in the revert one: every untaken arm on the path is `Func.rev` or a
`.call` to a certified-reverting table body, so
`routeTo_branch*_of_*RevertsOk` settles fourteen of the fifteen branches
without a branch word.  The count branch (`B7`) is the one branch with two
live arms; its word, and the facts that survive the two external crossings,
are taken in continuation-passing style — quantified over the walk's own
states — so the witness side pins the crossing poststates against its
concrete responder crossings with `Ninst.RunCompiled.unique`
(`Blanc/ExecutionOccurrence.lean`) and discharges the storage guard from its
world.

The `attainable_of_entryRoute_frame` sibling at the foot passes the route the
**full** entry-burn fact rather than only its storage and memory projections:
`Devm.BurnBy` is `Rels.eq` outside the gas field, so the burn pins the walk's
entry transient storage — which the pause body's reentrancy-lock `TLOAD`
reads — and every other field the two-crossing route may need a witness-side
guard for.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-! ## Carrying the callee's code across the local route

The two external crossings read `EXTCODESIZE`, `CALL` and `STATICCALL` at
`target.toAdr`, and their outcome depends on the code installed there.  A
witness supplies that code at the message's entry state and needs it to hold
at each crossing's own prestate; the route threads it.  The address's code is
touched by no instruction on this route except the two external calls
themselves — `Rinst.Hinv Devm.getCode` holds for *every* register opcode,
`SSTORE` and the kernel's decrement included — so the crossings are the only
places a witness-side hypothesis is needed. -/

/-- `d.getCode adr = code` — the fact threaded to each crossing's prestate. -/
def CodeAt (d : Devm) (adr : Adr) (code : ByteArray) : Prop :=
  d.getCode adr = code

/-- Cross a whole line: no register opcode changes any account's code. -/
theorem CodeAt.acrossLine {e : Sevm} {a b : Devm} {adr : Adr}
    {code : ByteArray} {l : Line} (inv : Line.Inv Devm.getCode l)
    (run : Line.Run e a l b) (h : CodeAt a adr code) : CodeAt b adr code := by
  unfold CodeAt at *
  rw [← h]; exact (congrFun (Line.of_inv Devm.getCode inv run) adr).symm

/-- Cross any relation that preserves the state: `Devm.BurnBy`'s `.state`, a
`Devm.PopBurnBy`'s `.state`, a `.state`-equation between two Devms. -/
theorem CodeAt.ofState {a b : Devm} {adr : Adr} {code : ByteArray}
    (hstate : a.state = b.state) (h : CodeAt a adr code) :
    CodeAt b adr code := by
  unfold CodeAt Devm.getCode Devm.getAcct at *
  rw [← h, hstate]

/-- Cross one register-opcode instruction. -/
theorem CodeAt.acrossNinst {e : Sevm} {a b : Devm} {adr : Adr}
    {code : ByteArray} {i : Ninst} [inst : Ninst.Hinv Devm.getCode i]
    (run : Ninst.Run e a i b) (h : CodeAt a adr code) : CodeAt b adr code := by
  unfold CodeAt at *
  rw [← h]; exact (congrFun (inst.inv run) adr).symm


/-! ## The frame tail, with the whole entry burn

Identical to `attainable_of_entryRoute_frame` except in what the `route`
hypothesis receives about the walk's entry state: the full
`Devm.BurnBy gJumpdest pre devm` fact its proof already destructs, instead of
the two projections `Devm.getStor devm = Devm.getStor pre` and
`devm.memory = pre.memory`.  A route that reads `devm.transientStorage` — the
pause route's lock `TLOAD` does — cannot be stated over the two projections,
and a route whose external-crossing guards must pin the walk's states against
a concrete world needs every field the burn preserves. -/

theorem attainable_of_entryRoute_frame_burn {sevm : Sevm} {pre : Devm}
    {ca : Adr} {row : RuntimePersistentWrite} {expected : InvocationRole}
    {path : Prog.SourcePath}
    (owner : sevm.currentTarget = ca)
    (codeAddress : sevm.codeAddress = some ca)
    (pin : ∀ {r : RuntimePersistentWrite} {site : Prog.SourceSite},
      r.sourceSite? officialParams = some site → site.path = path → r = row)
    (roles : ∀ r ∈ row.permittedRoles, r = expected)
    (run : ∃ post,
      Prog.RunCompiledTo sevm pre (runtime officialParams) (.ok post) ∧
        some sevm.code.toList = Prog.compile (runtime officialParams))
    (route : ∀ (devm post : Devm),
      Devm.BurnBy gJumpdest pre devm →
      ∀ h : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        sevm devm (runtime officialParams).main (.ok post),
        Func.RunCompiledTo.RouteTo ⟨0, []⟩ h path (.reg .sstore)) :
    Attainable officialParams row expected := by
  obtain ⟨post, hrun, hcompile⟩ := run
  obtain ⟨mid, hburn, hwalk⟩ := hrun
  have hroute := route mid post hburn hwalk
  obtain ⟨exc, occurrence, site, hpath, hmem, hpc, hinstr, hinstrTarget,
    sameFrame⟩ :=
    Prog.exec_of_runCompiledTo_routeTo hburn hroute hcompile
  have invocation :
      (⟨0, sevm, pre, .ok post, exc⟩ : Exec.Deriv).exactInvocation
        (runtime officialParams) ca ca :=
    ⟨rfl, owner, codeAddress, hcompile⟩
  have instructionEq : occurrence.instruction = .reg .sstore :=
    hinstr.trans hinstrTarget
  obtain ⟨reached, rowSite, _rowMem, found, _classified, rowSitePc, _rowInstr,
    _unique, role, rolePermitted, authority⟩ :=
    Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot occurrence
      instructionEq (Exec.mem_rawFrameRoots_self exc) invocation sameFrame
  have routedMember : site ∈ runtimePersistentSourceSites officialParams := by
    unfold runtimePersistentSourceSites
    rw [List.mem_filter]
    exact ⟨hmem, by simp [hinstrTarget, isPersistentWriteInstruction]⟩
  have siteEq : rowSite = site :=
    runtimePersistentSourceSite_eq_of_pc
      (RuntimePersistentWrite.mem_runtimePersistentSourceSites found)
      routedMember (rowSitePc.trans hpc)
  have rowEq : reached = row := pin found (siteEq ▸ hpath)
  subst rowEq
  have roleEq : role = expected := roles role rolePermitted
  subst roleEq
  exact ⟨ca, ⟨0, sevm, pre, .ok post, exc⟩, ⟨0, sevm, pre, .ok post, exc⟩,
    occurrence, rowSite, instructionEq, Exec.mem_rawFrameRoots_self exc,
    invocation, sameFrame, found, rowSitePc, authority⟩

/-! ## The staging line's third window

`pauseStaging_windows` exports the two windows the shared kernel reads.  The
`.ok` route needs a third: the `1` staged at `continuationWord`, which is what
`finishSetPauser`'s continuation test reads to send the walk into
`pauseAfterSet` rather than back to `registerAfterSet`. -/

set_option maxRecDepth 8192 in
/-- `pause`'s staging line leaves the call's target argument at `targetWord`,
a zero at `newPauserWord`, and a one at `continuationWord`. -/
theorem pauseStaging_windows3 {sevm : Sevm} {stage devm' : Devm} {img : Bytes}
    (image : MemImage stage img)
    (run : Line.Run sevm stage pauseStagingLine devm') :
    MemWordAt devm' (targetWord * 32).toNat (Sevm.argWord sevm 0) ∧
      MemWordAt devm' (newPauserWord * 32).toNat 0 ∧
      MemWordAt devm' (continuationWord * 32).toNat 1 := by
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
  have image6 := image5.write hmemNew
  have image7 :=
    MemImage.of_memory_eq (Line.of_inv Devm.memory (by line_inv) rPush0b).symm
      image6
  have windowT7 := windowT6.acrossLine (by line_inv) rPush0b
  have windowN7 := windowN.acrossLine (by line_inv) rPush0b
  have pZero2 : (0 : B256) :: [] <<+ _u7.stack :=
    prefix_of_push (of_run_pushB256 (by
      rcases Line.of_run_cons rPush0b with ⟨_, q, hnil⟩
      cases hnil
      exact q)) nil_pref
  obtain ⟨_pPrev, hmemPrev⟩ := of_run_mstoreAt_val rPrevious pZero2
  have windowT8 := MemWordAt.writeMiss hmemPrev (by decide) windowT7
  have windowN8 := MemWordAt.writeMiss hmemPrev (by decide) windowN7
  have image8 := image7.write hmemPrev
  have image9 :=
    MemImage.of_memory_eq (Line.of_inv Devm.memory (by line_inv) rPush1).symm
      image8
  have windowT9 := windowT8.acrossLine (by line_inv) rPush1
  have windowN9 := windowN8.acrossLine (by line_inv) rPush1
  have pOne : (1 : B256) :: [] <<+ _u9.stack :=
    prefix_of_push (of_run_pushB256 (by
      rcases Line.of_run_cons rPush1 with ⟨_, q, hnil⟩
      cases hnil
      exact q)) nil_pref
  obtain ⟨_pCont, hmemCont⟩ := of_run_mstoreAt_val rContinuation pOne
  exact ⟨MemWordAt.writeMiss hmemCont (by decide) windowT9,
    MemWordAt.writeMiss hmemCont (by decide) windowN9,
    MemWordAt.of_write image9 hmemCont⟩

/-! ## The pause body, on a successful outcome

The revert flavour (`pause_routeTo_setPauserCall`) pays for the two calldata
guards and refutes the three world-valued ones with the walk's empty payload.
Here **all five** are free: `requireStaticArgs`' sibling is a bare `Func.rev`,
`canonicalAddressArg`'s is `.call emptyRevertSlot`, and the lock, assignment
and liveness guards call named runtime errors — every one certified reverting,
so a successful walk cannot have taken it.  No calldata hypothesis survives
into this statement, which is why the revert flavour's `argsPresent` and
`targetCanonical` premises have no `.ok` counterparts. -/

set_option maxRecDepth 8192 in
/-- From `pause`'s entry to its `.call setPauserSlot`, on a successful walk:
all five guards settled by certified-reverting siblings. -/
theorem pause_routeTo_setPauserCall_ok (dp : DeployParams)
    {sevm : Sevm} {devm post : Devm}
    {functionIndex : Nat} {steps : List Prog.SourceStep}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      pause (.ok post))
    (callRoute : ∀ (current : Prog.SourcePath) (stage devm' : Devm),
      Devm.getStor devm' = Devm.getStor devm →
      stage.memory = devm.memory →
      Devm.getCode devm' = Devm.getCode devm →
      Line.Run sevm stage pauseStagingLine devm' →
      ∀ tail : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm devm' (Func.call setPauserSlot) (.ok post),
        Func.RunCompiledTo.RouteTo current tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h targetPath
      targetInstruction := by
  refine routeTo_line pauseStaticArgsTest h (fun s0 r0 tail0 => ?_)
  have g0 : Devm.getStor s0 = Devm.getStor devm :=
    (Line.of_inv Devm.getStor (by unfold pauseStaticArgsTest; line_inv)
      r0).symm
  have m0 : s0.memory = devm.memory :=
    (Line.of_inv Devm.memory (by unfold pauseStaticArgsTest; line_inv) r0).symm
  have d0 : Devm.getCode s0 = Devm.getCode devm :=
    (Line.of_inv Devm.getCode (by unfold pauseStaticArgsTest; line_inv)
      r0).symm
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail0 (fuel := 4) (by rfl)
    (fun s1 hpop1 tail1 => ?_)
  have g1 := (getStor_of_state hpop1.state).symm.trans g0
  have m1 := hpop1.memory.symm.trans m0
  have d1 := (getCode_of_state hpop1.state).symm.trans d0
  refine routeTo_line (arg 0 ++ checkNonAddress) tail1
    (fun s2 r2 tail2 => ?_)
  have g2 := (Line.of_inv Devm.getStor (by line_inv) r2).symm.trans g1
  have m2 := (Line.of_inv Devm.memory (by line_inv) r2).symm.trans m1
  have d2 := (Line.of_inv Devm.getCode (by line_inv) r2).symm.trans d1
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail2 (fuel := 4) (by rfl)
    (fun _s3 hpop3 tail3 => ?_)
  have g3 := (getStor_of_state hpop3.state).symm.trans g2
  have m3 := hpop3.memory.symm.trans m2
  have d3 := (getCode_of_state hpop3.state).symm.trans d2
  refine routeTo_line pauseLockTest tail3 (fun _s4 r4 tail4 => ?_)
  have g4 := (Line.of_inv Devm.getStor (by unfold pauseLockTest; line_inv)
    r4).symm.trans g3
  have m4 := (Line.of_inv Devm.memory (by unfold pauseLockTest; line_inv)
    r4).symm.trans m3
  have d4 := (Line.of_inv Devm.getCode (by unfold pauseLockTest; line_inv)
    r4).symm.trans d3
  refine routeTo_branchRight_of_leftRevertsOk_frame tail4 (fuel := 8) (by rfl)
    (fun _s5 _w5 hpop5 tail5 => ?_)
  have g5 := (getStor_of_state hpop5.state).symm.trans g4
  have m5 := hpop5.memory.symm.trans m4
  have d5 := (getCode_of_state hpop5.state).symm.trans d4
  refine routeTo_line pauseAssignedTest tail5 (fun _s6 r6 tail6 => ?_)
  have g6 := (Line.of_inv Devm.getStor
    (by unfold pauseAssignedTest; line_inv) r6).symm.trans g5
  have m6 := (Line.of_inv Devm.memory
    (by unfold pauseAssignedTest; line_inv) r6).symm.trans m5
  have d6 := (Line.of_inv Devm.getCode
    (by unfold pauseAssignedTest; line_inv) r6).symm.trans d5
  refine routeTo_branchRight_of_leftRevertsOk_frame tail6 (fuel := 8) (by rfl)
    (fun _s7 _w7 hpop7 tail7 => ?_)
  have g7 := (getStor_of_state hpop7.state).symm.trans g6
  have m7 := hpop7.memory.symm.trans m6
  have d7 := (getCode_of_state hpop7.state).symm.trans d6
  refine routeTo_line pauseLiveTest tail7 (fun _s8 r8 tail8 => ?_)
  have g8 := (Line.of_inv Devm.getStor
    (by unfold pauseLiveTest; line_inv) r8).symm.trans g7
  have m8 := (Line.of_inv Devm.memory
    (by unfold pauseLiveTest; line_inv) r8).symm.trans m7
  have d8 := (Line.of_inv Devm.getCode
    (by unfold pauseLiveTest; line_inv) r8).symm.trans d7
  refine routeTo_branchRight_of_leftRevertsOk_frame tail8 (fuel := 8) (by rfl)
    (fun _s9 _w9 hpop9 tail9 => ?_)
  have g9 := (getStor_of_state hpop9.state).symm.trans g8
  have m9 := hpop9.memory.symm.trans m8
  have d9 := (getCode_of_state hpop9.state).symm.trans d8
  refine routeTo_line pauseStagingLine tail9 (fun _s10 r10 tail10 => ?_)
  exact callRoute _ _ _
    ((Line.of_inv Devm.getStor (by unfold pauseStagingLine; line_inv)
      r10).symm.trans g9) m9
    ((Line.of_inv Devm.getCode (by unfold pauseStagingLine; line_inv)
      r10).symm.trans d9) r10 tail10

set_option maxRecDepth 16384 in
/-- The whole pause route down to `setPauserKernel`'s entry on a successful
walk, with the three staged memory windows and the storage relation the
kernel's second branch needs.  The `.ok` sibling of
`runtimeMain_routeTo_pauseKernel`: the entry guard and the five body guards
are settled by the outcome, so only the calldata selector is a premise. -/
theorem runtimeMain_routeTo_pauseKernel_ok (dp : DeployParams)
    {sevm : Sevm} {devm post : Devm} {img : Bytes} {code : ByteArray}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      (runtime dp).main (.ok post))
    (image : MemImage devm img)
    (codeAt : CodeAt devm (Sevm.argWord sevm 0).toAdr code)
    (selectorEq : Sevm.selector sevm = selector "pause" [.address])
    (kernelRoute : ∀ kernelStart : Devm,
      MemWordAt kernelStart (targetWord * 32).toNat (Sevm.argWord sevm 0) →
      MemWordAt kernelStart (newPauserWord * 32).toNat 0 →
      MemWordAt kernelStart (continuationWord * 32).toNat 1 →
      Devm.getStor kernelStart = Devm.getStor devm →
      CodeAt kernelStart (Sevm.argWord sevm 0).toAdr code →
      ∀ tail : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm
        kernelStart setPauserKernel (.ok post),
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
  have de : Devm.getCode entry = Devm.getCode devm :=
    (Line.of_inv Devm.getCode (by unfold runtimeMainEntryPrefix; line_inv)
      lineRun).symm
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail (fuel := 4) (by rfl)
    (fun body hpop arm => ?_)
  have gb := (getStor_of_state hpop.state).symm.trans ge
  have mb := hpop.memory.symm.trans me
  have db := (getCode_of_state hpop.state).symm.trans de
  refine dispatch_routeTo_pause dp arm selectorEq
    (fun _current pauseEntry hstor hmem hcode bodyTail => ?_)
  refine pause_routeTo_setPauserCall_ok dp bodyTail
    (fun _c _stage callState hstor' hmem' hcode' staging callTail => ?_)
  obtain ⟨wT, wN, wC⟩ := pauseStaging_windows3
    (MemImage.of_memory_eq (hmem'.trans (hmem.trans mb)) image) staging
  refine routeTo_call (body := setPauserKernel) callTail
    (by simp [runtime, aux, setPauserSlot]) (fun kernelStart kburn ktail => ?_)
  exact kernelRoute kernelStart
    (MemWordAt.of_memory_eq kburn.memory.symm wT)
    (MemWordAt.of_memory_eq kburn.memory.symm wN)
    (MemWordAt.of_memory_eq kburn.memory.symm wC)
    ((getStor_of_state kburn.state).symm.trans
      (hstor'.trans (hstor.trans gb)))
    ((congrFun ((getCode_of_state kburn.state).symm.trans
      (hcode'.trans (hcode.trans db))) (Sevm.argWord sevm 0).toAdr).trans
      codeAt) ktail

/-! ## Window crossings the pause continuation needs

The kernel-and-removal leg is shared with the unregistration route, but the
pause continuation must carry two more windows across it: the staged target
survives to `pauseAfterSet`, whose two external calls read it back, and the
staged `1` at `continuationWord` survives to `finishSetPauser`'s test. -/

/-- Cross a `loadWord k ++ tagTop r` key-construction segment. -/
theorem MemWordAt.acrossLoadTag {e : Sevm} {a b : Devm} {offset : Nat}
    {w k : B256} {r : Nat} (run : Line.Run e a (loadWord k ++ tagTop r) b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  rcases of_run_append (loadWord k) run with ⟨_s1, r1, run⟩
  exact (window.acrossLoadWord r1).acrossLine (by line_inv) run

set_option maxRecDepth 8192 in
/-- Cross `removeTarget`'s whole straight line up to its last `SSTORE`.  The
line's three memory writes land at `removedIndexWord`, `arrayLengthWord` and
`lastTargetWord`; a window that misses all three survives. -/
theorem MemWordAt.acrossRemoveTargetPrefix {e : Sevm} {a b : Devm}
    {offset : Nat} {w : B256}
    (missRemoved : offset + 32 ≤ (removedIndexWord * 32).toNat ∨
      (removedIndexWord * 32).toNat + 32 ≤ offset)
    (missLength : offset + 32 ≤ (arrayLengthWord * 32).toNat ∨
      (arrayLengthWord * 32).toNat + 32 ≤ offset)
    (missLast : offset + 32 ≤ (lastTargetWord * 32).toNat ∨
      (lastTargetWord * 32).toNat + 32 ≤ offset)
    (run : Line.Run e a removeClearTargetIndexPrefix b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold removeClearTargetIndexPrefix at run
  rcases of_run_append removeArrayLengthPrefix run with ⟨sD, rD, run⟩
  unfold removeArrayLengthPrefix at rD
  rcases of_run_append removeClearTailPrefix rD with ⟨sC, rC, rD⟩
  unfold removeClearTailPrefix at rC
  rcases of_run_append removeMovedIndexPrefix rC with ⟨sB, rB, rC⟩
  unfold removeMovedIndexPrefix at rB
  rcases of_run_append removeArrayHolePrefix rB with ⟨sA, rA, rB⟩
  -- the hole prefix
  unfold removeArrayHolePrefix targetIndexKey at rA
  rcases of_run_append (loadWord targetWord ++ tagTop indexRegion) rA
    with ⟨_a1, q1, rA⟩
  rcases of_run_append [Ninst.sload] rA with ⟨_a2, q2, rA⟩
  rcases of_run_append (mstoreAt removedIndexWord) rA with ⟨_a3, q3, rA⟩
  rcases of_run_append [Ninst.pushB256 arrayLengthSlot, Ninst.sload] rA
    with ⟨_a4, q4, rA⟩
  rcases of_run_append (mstoreAt arrayLengthWord) rA with ⟨_a5, q5, rA⟩
  rcases of_run_append (loadWord arrayLengthWord) rA with ⟨_a6, q6, rA⟩
  rcases of_run_append (tagTop arrayRegion) rA with ⟨_a7, q7, rA⟩
  rcases of_run_append [Ninst.sload] rA with ⟨_a8, q8, rA⟩
  rcases of_run_append (mstoreAt lastTargetWord) rA with ⟨_a9, q9, rA⟩
  rcases of_run_append (loadWord lastTargetWord) rA with ⟨_a10, q10, rA⟩
  rcases of_run_append (loadWord removedIndexWord) rA with ⟨_a11, q11, rA⟩
  have windowA : MemWordAt sA offset w :=
    ((((((((((((window.acrossLoadTag q1).acrossLine (by line_inv)
      q2).acrossMstoreAt missRemoved q3).acrossLine (by line_inv)
      q4).acrossMstoreAt missLength q5).acrossLoadWord q6).acrossLine
      (by line_inv) q7).acrossLine (by line_inv) q8).acrossMstoreAt missLast
      q9).acrossLoadWord q10).acrossLoadWord q11).acrossLine (by line_inv) rA)
  -- the moved-index tail
  rcases of_run_append [Ninst.sstore] rB with ⟨_b1, p1, rB⟩
  rcases of_run_append (loadWord removedIndexWord) rB with ⟨_b2, p2, rB⟩
  unfold lastTargetIndexKey at rB
  have windowB : MemWordAt sB offset w :=
    ((windowA.acrossLine (by line_inv) p1).acrossLoadWord p2).acrossLoadTag rB
  -- the clear-tail tail
  rcases of_run_append [Ninst.sstore, Ninst.pushB256 0] rC with ⟨_c1, o1, rC⟩
  rcases of_run_append (loadWord arrayLengthWord) rC with ⟨_c2, o2, rC⟩
  have windowC : MemWordAt sC offset w :=
    ((windowB.acrossLine (by line_inv) o1).acrossLoadWord o2).acrossLine
      (by line_inv) rC
  -- the array-length tail
  rcases of_run_append [Ninst.sstore] rD with ⟨_d1, n1, rD⟩
  rcases of_run_append (loadWord arrayLengthWord) rD with ⟨_d2, n2, rD⟩
  have windowD : MemWordAt sD offset w :=
    ((windowC.acrossLine (by line_inv) n1).acrossLoadWord n2).acrossLine
      (by line_inv) rD
  -- the clear-target-index tail
  rcases of_run_append [Ninst.sstore, Ninst.pushB256 0] run with ⟨_e1, m1, run⟩
  unfold targetIndexKey at run
  exact (windowD.acrossLine (by line_inv) m1).acrossLoadTag run

set_option maxRecDepth 8192 in
/-- The kernel's second branch word at an assigned target, with all three
pause windows carried across the crossing.  The sibling of
`pauseKernel_previousPauserNonzero`, which carries only the `newPauserWord`
window the unregistration continuation needs. -/
theorem pauseKernel_previousPauserNonzero3 {sevm : Sevm} {devm devm' : Devm}
    {target : B256}
    (windowT : MemWordAt devm (targetWord * 32).toNat target)
    (windowN : MemWordAt devm (newPauserWord * 32).toNat 0)
    (windowC : MemWordAt devm (continuationWord * 32).toNat 1)
    (assigned :
      Devm.getStorVal devm sevm.currentTarget (assignmentSlot target) ≠ 0)
    (run : Line.Run sevm devm pauseKernelAppendPrefix devm') :
    (∀ (w : B256) (rest : Stack), devm'.stack = w :: rest → w = 0) ∧
      MemWordAt devm' (targetWord * 32).toNat target ∧
      MemWordAt devm' (newPauserWord * 32).toNat 0 ∧
      MemWordAt devm' (continuationWord * 32).toNat 1 := by
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
  have chain7 : ∀ {offset : Nat} {u : B256}, MemWordAt devm offset u →
      MemWordAt s7 offset u := fun window =>
    ((((((window.acrossNinst q1).acrossMload q2).acrossNinst
      q3).acrossNinst q4).acrossNinst q5).acrossNinst q6).acrossNinst q7
  have windowT8 : MemWordAt s8 (targetWord * 32).toNat target :=
    MemWordAt.writeMiss hmem8 (by decide) (chain7 windowT)
  have windowN8 : MemWordAt s8 (newPauserWord * 32).toNat 0 :=
    MemWordAt.writeMiss hmem8 (by decide) (chain7 windowN)
  have windowC8 : MemWordAt s8 (continuationWord * 32).toNat 1 :=
    MemWordAt.writeMiss hmem8 (by decide) (chain7 windowC)
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
  have chainEnd : ∀ {offset : Nat} {u : B256}, MemWordAt s8 offset u →
      MemWordAt devm' offset u := fun window =>
    (((((((window.acrossNinst q9).acrossMload q10).acrossNinst
      q11).acrossMload q12).acrossNinst q13).acrossNinst q14).acrossNinst
      q15).acrossNinst q16
  refine ⟨?_, chainEnd windowT8, chainEnd windowN8, chainEnd windowC8⟩
  intro w rest hstack
  rw [head_of_stack_prefix p16 hstack]
  simp [B256.eqCheck, hnonzero]

/-- `finishSetPauser`'s branch word on the pause side: the staging line wrote
a `1` continuation, so the test's `iszero` is zero and the walk falls through
into `.call pauseAfterSetSlot`.  The dual of
`freshWorld_continuationRegister`, stated at an arbitrary `Sevm`. -/
theorem pause_continuationWord {sevm : Sevm} {devm devm' : Devm}
    (window : MemWordAt devm (continuationWord * 32).toNat 1)
    (run : Line.Run sevm devm finishSetPauserPrefix devm') :
    ∀ (w : B256) (rest : Stack), devm'.stack = w :: rest → w = 0 := by
  unfold finishSetPauserPrefix at run
  rcases of_run_append (loadWord newPauserWord) run with ⟨_s1, r1, run⟩
  rcases of_run_append (loadWord previousPauserWord) run with ⟨_s2, r2, run⟩
  rcases of_run_append (loadWord targetWord) run with ⟨_s3, r3, run⟩
  rcases of_run_append [Ninst.pushB256 pauserSetEvent] run with ⟨_s4, r4, run⟩
  rcases of_run_append (logWith 3 0 0) run with ⟨_s5, r5, run⟩
  have window5 := ((((window.acrossLoadWord r1).acrossLoadWord
    r2).acrossLoadWord r3).acrossLine (by line_inv) r4).acrossLogWith r5
  intro w rest hstack
  rw [memoryZeroCheck_word window5 run w rest hstack]
  decide

set_option maxRecDepth 8192 in
/-- From `setPauserKernel`'s entry to `pauseAfterSet`'s entry, on a successful
walk at an assigned target with the pause staging in memory: the old-count
arm, the `removeTarget` leg, and `finishSetPauser`'s pause continuation.  The
continuation receives the staged target window, which `pauseAfterSet`'s two
external calls read back. -/
theorem setPauserKernel_routeTo_pauseAfterSetCall (dp : DeployParams)
    {sevm : Sevm} {devm post : Devm} {target : B256} {code : ByteArray}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      setPauserKernel (.ok post))
    (windowT : MemWordAt devm (targetWord * 32).toNat target)
    (windowN : MemWordAt devm (newPauserWord * 32).toNat 0)
    (windowC : MemWordAt devm (continuationWord * 32).toNat 1)
    (codeAt : CodeAt devm target.toAdr code)
    (assigned :
      Devm.getStorVal devm sevm.currentTarget (assignmentSlot target) ≠ 0)
    (bodyRoute : ∀ devm' : Devm,
      MemWordAt devm' (targetWord * 32).toNat target →
      CodeAt devm' target.toAdr code →
      ∀ tail : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm
        devm' pauseAfterSet (.ok post),
        Func.RunCompiledTo.RouteTo ⟨pauseAfterSetSlot, []⟩ tail targetPath
          targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨setPauserSlot, []⟩ h targetPath
      targetInstruction := by
  refine routeTo_line setPauserKernelZeroCheck h (fun z zrun tail => ?_)
  have gz : Devm.getStor z = Devm.getStor devm :=
    (Line.of_inv Devm.getStor
      (by unfold setPauserKernelZeroCheck; line_inv) zrun).symm
  have wTz := windowT.acrossMemoryZeroCheck (k := targetWord) zrun
  have wNz := windowN.acrossMemoryZeroCheck (k := targetWord) zrun
  have wCz := windowC.acrossMemoryZeroCheck (k := targetWord) zrun
  have cz := codeAt.acrossLine (by unfold setPauserKernelZeroCheck; line_inv)
    zrun
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail (fuel := 8) (by rfl)
    (fun a hpop arm => ?_)
  have ga : Devm.getStor a = Devm.getStor devm :=
    (getStor_of_state hpop.state).symm.trans gz
  have wTa := MemWordAt.of_memory_eq hpop.memory.symm wTz
  have wNa := MemWordAt.of_memory_eq hpop.memory.symm wNz
  have wCa := MemWordAt.of_memory_eq hpop.memory.symm wCz
  have ca := cz.ofState hpop.state
  refine routeTo_line pauseKernelAppendPrefix arm (fun _b brun tail2 => ?_)
  obtain ⟨branchWord, wTb, wNb, wCb⟩ :=
    pauseKernel_previousPauserNonzero3 wTa wNa wCa
      (by
        rw [show Devm.getStorVal a sevm.currentTarget (assignmentSlot target)
              = Devm.getStorVal devm sevm.currentTarget (assignmentSlot target)
            from congrArg (fun f : Adr → Stor =>
              (f sevm.currentTarget).get (assignmentSlot target)) ga]
        exact assigned)
      brun
  have cb := ca.acrossLine
    (by unfold pauseKernelAppendPrefix setPauserKernelAssignmentPrefix;
        line_inv) brun
  refine routeTo_branchLeft_frame tail2 branchWord (fun c hpopc tail3 => ?_)
  have wTc := MemWordAt.of_memory_eq hpopc.memory.symm wTb
  have wNc := MemWordAt.of_memory_eq hpopc.memory.symm wNb
  have wCc := MemWordAt.of_memory_eq hpopc.memory.symm wCb
  have cc := cb.ofState hpopc.state
  refine routeTo_line oldCountPrefix tail3 (fun d drun tail4 => ?_)
  have wTd := wTc.acrossOldCountPrefix drun
  have wNd := wNc.acrossOldCountPrefix drun
  have wCd := wCc.acrossOldCountPrefix drun
  have cd := cc.acrossLine
    (by unfold oldCountPrefix previousCountKey loadWord tagTop; line_inv) drun
  refine routeTo_next tail4 (fun e erun tail5 => ?_)
  have wTe := wTd.acrossNinst (Ninst.Run.of_runCompiled erun)
  have wNe := wNd.acrossNinst (Ninst.Run.of_runCompiled erun)
  have wCe := wCd.acrossNinst (Ninst.Run.of_runCompiled erun)
  have ce := cd.acrossNinst (Ninst.Run.of_runCompiled erun)
  refine routeTo_call (body := afterOldPauser) tail5
    (by simp [runtime, aux, afterOldPauserSlot]) (fun f fburn tail6 => ?_)
  have wTf := MemWordAt.of_memory_eq fburn.memory.symm wTe
  have wNf := MemWordAt.of_memory_eq fburn.memory.symm wNe
  have wCf := MemWordAt.of_memory_eq fburn.memory.symm wCe
  have cf := ce.ofState fburn.state
  refine routeTo_line (memoryZeroCheck newPauserWord) tail6
    (fun g grun tail7 => ?_)
  have wTg := wTf.acrossMemoryZeroCheck (k := newPauserWord) grun
  have wCg := wCf.acrossMemoryZeroCheck (k := newPauserWord) grun
  have cg := cf.acrossLine (by unfold memoryZeroCheck loadWord; line_inv) grun
  refine routeTo_branchRight_frame tail7
    (fun w rest hstack => by
      rw [memoryZeroCheck_word (k := newPauserWord) wNf grun w rest hstack]
      decide)
    (fun i _wi hpopi arm2 => ?_)
  have wTi := MemWordAt.of_memory_eq hpopi.memory.symm wTg
  have wCi := MemWordAt.of_memory_eq hpopi.memory.symm wCg
  have ci := cg.ofState hpopi.state
  refine routeTo_call (body := removeTarget) arm2
    (by simp [runtime, aux, removeTargetSlot]) (fun j jburn tail8 => ?_)
  have wTj := MemWordAt.of_memory_eq jburn.memory.symm wTi
  have wCj := MemWordAt.of_memory_eq jburn.memory.symm wCi
  have cj := ci.ofState jburn.state
  refine routeTo_line removeClearTargetIndexPrefix tail8
    (fun k krun tail9 => ?_)
  have wTk := wTj.acrossRemoveTargetPrefix (by decide) (by decide) (by decide)
    krun
  have wCk := wCj.acrossRemoveTargetPrefix (by decide) (by decide) (by decide)
    krun
  have ck := cj.acrossLine (by line_inv) krun
  refine routeTo_next tail9 (fun l lrun tail10 => ?_)
  have wTl := wTk.acrossNinst (Ninst.Run.of_runCompiled lrun)
  have wCl := wCk.acrossNinst (Ninst.Run.of_runCompiled lrun)
  have cl := ck.acrossNinst (Ninst.Run.of_runCompiled lrun)
  refine routeTo_call (body := finishSetPauser) tail10
    (by simp [runtime, aux, finishSetPauserSlot]) (fun m mburn tail11 => ?_)
  have wTm := MemWordAt.of_memory_eq mburn.memory.symm wTl
  have wCm := MemWordAt.of_memory_eq mburn.memory.symm wCl
  have cm := cl.ofState mburn.state
  refine routeTo_line finishSetPauserPrefix tail11 (fun n nrun tail12 => ?_)
  have wTn := wTm.acrossFinishPrefix nrun
  have cn := cm.acrossLine (by unfold finishSetPauserPrefix; line_inv) nrun
  refine routeTo_branchLeft_frame tail12 (pause_continuationWord wCm nrun)
    (fun o hpopo arm3 => ?_)
  have wTo := MemWordAt.of_memory_eq hpopo.memory.symm wTn
  have co := cn.ofState hpopo.state
  refine routeTo_call (body := pauseAfterSet) arm3
    (by simp [runtime, aux, pauseAfterSetSlot]) (fun p pburn tail13 => ?_)
  exact bodyRoute p (MemWordAt.of_memory_eq pburn.memory.symm wTo)
    (co.ofState pburn.state) tail13

/-! ## The two expiry paths -/

/-- Structural source position of the count-zero arm's expiry `SSTORE`:
inventory index `19`. -/
def pauseLastExpiryPath : Prog.SourcePath :=
  ⟨pauseAfterSetSlot,
    List.replicate 5 .rest ++ [.branchLeft] ++
      List.replicate 18 .rest ++ [.branchLeft] ++
      List.replicate 12 .rest ++ [.branchLeft] ++
      List.replicate 3 .rest ++ [.branchLeft] ++
      List.replicate 4 .rest ++ [.branchLeft] ++
      List.replicate 2 .rest ++ [.branchRight] ++
      List.replicate 16 .rest ++ [.branchRight] ++
      List.replicate 7 .rest⟩

/-- Structural source position of the checked arm's expiry `SSTORE`:
inventory index `18`. -/
def pauseRetainedExpiryPath : Prog.SourcePath :=
  ⟨pauseAfterSetSlot,
    List.replicate 5 .rest ++ [.branchLeft] ++
      List.replicate 18 .rest ++ [.branchLeft] ++
      List.replicate 12 .rest ++ [.branchLeft] ++
      List.replicate 3 .rest ++ [.branchLeft] ++
      List.replicate 4 .rest ++ [.branchLeft] ++
      List.replicate 2 .rest ++ [.branchRight] ++
      List.replicate 16 .rest ++ [.branchLeft] ++
      List.replicate 8 .rest ++ [.branchLeft] ++
      List.replicate 6 .rest⟩

/-!
Index pairing, verified by `#eval` against
`runtimePersistentSourceSites officialParams` on this tree (post-exchange
names):

* `(runtimePersistentSourceSites officialParams)[18]?` — path
  `= pauseRetainedExpiryPath`, pc `3912`, functionIndex `20` (checked arm);
* `(runtimePersistentSourceSites officialParams)[19]?` — path
  `= pauseLastExpiryPath`, pc `4032`, functionIndex `20` (count-zero arm).

The `decide +kernel` index pins themselves belong to the join module, beside
the witnesses that consume them.
-/

/-! ## The `pauseAfterSet` leg

Instruction-level pieces first.  `line_inv` lacks a memory instance for
`EXTCODESIZE` — no earlier route crossed one while carrying a window — so the
instance lives here, beside the three the revert-flavour route module added
for `TLOAD`, `TSTORE` and `TIMESTAMP`. -/

/-- `EXTCODESIZE` pops an address, charges an access cost, and pushes the code
size; memory is untouched on both the warm and the cold arm. -/
instance : Rinst.Hinv Devm.memory Rinst.extcodesize := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨adr, s₁⟩, h1, run₁⟩
  have hm1 : pre.memory = s₁.memory := by
    rw [Devm.popToAdr_def] at h1
    simp only [Functor.mapRev, Functor.map, Except.map] at h1
    rcases hp : Devm.pop pre with _ | ⟨x, s₂⟩ <;>
      simp [hp, Prod.mapFst] at h1
    rw [← h1.2]
    exact (Devm.pop_of_pop hp).memory
  refine hm1.trans ?_
  split at run₁ <;>
  · rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, run₂⟩
    exact Eq.trans (Devm.burn_of_chargeGas h2).memory
      (Devm.push_of_push run₂).memory⟩

/-- The target-code guard: the staged target is loaded back, duplicated, and
its code size tested for zero. -/
def pauseCodeGuard : Line :=
  loadWord targetWord ++ [Ninst.dup 0, Ninst.extcodesize, Ninst.iszero]

/-- From the code guard's live arm to the `pauseFor(uint256)` `CALL`: drop the
duplicate, stage selector and duration, and push the call's seven operands. -/
def pauseCallStaging : Line :=
  [Ninst.pop, Ninst.pushB256 pauseForSelector] ++ mstoreAt 8 ++
    loadWord durationWord ++ mstoreAt 9 ++
    pushList [0, 0, 36, 0x11c, 0] ++ loadWord targetWord ++ [Ninst.gas]

/-- From the `CALL`'s live arm to the `isPaused()` `STATICCALL`: restage the
selector and push the six operands. -/
def pauseStatStaging : Line :=
  [Ninst.pushB256 isPausedSelector] ++ mstoreAt 8 ++
    pushList [32, 0, 4, 0x11c] ++ loadWord targetWord ++ [Ninst.gas]

/-- `decodePausedResult`'s returndata-word load and zero test. -/
def pauseDecodeLoad : Line := loadWord 0 ++ [Ninst.dup 0, Ninst.iszero]

theorem pauseCallStaging_codeInv : Line.Inv Devm.getCode pauseCallStaging := by
  unfold pauseCallStaging mstoreAt loadWord pushList
  simp only [List.map, List.cons_append, List.nil_append]
  line_inv

theorem pauseStatStaging_codeInv : Line.Inv Devm.getCode pauseStatStaging := by
  unfold pauseStatStaging mstoreAt loadWord pushList
  simp only [List.map, List.cons_append, List.nil_append]
  line_inv

/-- `pauseSuccess`'s event prefix: the duration staged for the log data, the
caller and target as topics, and the `PauseTriggered` `LOG2`. -/
def pauseSuccessEventLine : Line :=
  loadWord durationWord ++ mstoreAt 0 ++ [Ninst.caller] ++
    loadWord targetWord ++ [Ninst.pushB256 pauseTriggeredEvent] ++
    logWith 2 0 1

/-- The source position of `pauseSuccess`'s count branch, from
`pauseAfterSet`'s root. -/
def pauseCountBranchSteps : List Prog.SourceStep :=
  List.replicate 5 .rest ++ [.branchLeft] ++
    List.replicate 18 .rest ++ [.branchLeft] ++
    List.replicate 12 .rest ++ [.branchLeft] ++
    List.replicate 3 .rest ++ [.branchLeft] ++
    List.replicate 4 .rest ++ [.branchLeft] ++
    List.replicate 2 .rest ++ [.branchRight] ++
    List.replicate 16 .rest

/-- The count branch's word from a storage fact about the state entering the
count test: `iszero` of the caller's count cell.  This is the lemma a witness
uses to discharge the two final theorems' count-word premises out of its
world's storage. -/
theorem pauseCount_word {sevm : Sevm} {s s' : Devm} {count : B256}
    (hcount : Devm.getStorVal s sevm.currentTarget
      (countSlot sevm.caller.toB256) = count)
    (run : Line.Run sevm s heartbeatCountTest s') :
    ∀ (w : B256) (rest : Stack), s'.stack = w :: rest → w = (count =? 0) := by
  unfold heartbeatCountTest tagTop at run
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  rcases Line.of_run_cons run with ⟨s2, q2, run⟩
  rcases Line.of_run_cons run with ⟨s3, q3, run⟩
  rcases Line.of_run_cons run with ⟨s4, q4, run⟩
  rcases Line.of_run_cons run with ⟨s5, q5, hnil⟩
  cases hnil
  have p1 : sevm.caller.toB256 :: [] <<+ s1.stack :=
    prefix_of_push (of_run_caller q1) nil_pref
  have p2 := prefix_of_push (of_run_pushB256 q2) p1
  have p3 : (regionWord countRegion ||| sevm.caller.toB256) :: [] <<+
      s3.stack := prefix_of_or q3 p2
  obtain ⟨v, p4, hv⟩ := prefix_of_sload q4 p3
  have hstor3 : Devm.getStor s3 = Devm.getStor s :=
    (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons q1 (Line.Run.cons q2
        (Line.Run.cons q3 Line.Run.nil)))).symm
  have hveq : v = count := by
    rw [hv, show (regionWord countRegion ||| sevm.caller.toB256)
        = countSlot sevm.caller.toB256 from rfl,
      show Devm.getStorVal s3 sevm.currentTarget
            (countSlot sevm.caller.toB256)
          = Devm.getStorVal s sevm.currentTarget
            (countSlot sevm.caller.toB256) from
        congrArg (fun f : Adr → Stor =>
          (f sevm.currentTarget).get (countSlot sevm.caller.toB256)) hstor3]
    exact hcount
  intro w rest hstack
  rw [head_of_stack_prefix (prefix_of_iszero q5 p4) hstack, hveq]

set_option maxRecDepth 16384 in
/-- From `pauseAfterSet`'s entry to `pauseSuccess`'s count branch, on a
successful walk.  Ten crossings: the code guard, the two `bubbleRevert`
flag tests, and the three decode tests are settled by certified-reverting
siblings; the two external calls are single `.next` crossings whose
poststates the caller pins — the `hcall`/`hstat` premises quantify over the
walk's own crossing states, handing the caller the crossing's
`Ninst.RunCompiled` step, the operand stack shape and the staged-target
window, and asking back only that the window survive.  A witness discharges
them against its concrete responder crossings with
`Ninst.RunCompiled.unique`.

The continuation is entered at the count branch — the one branch on the
route with two live arms — with the crossed count-test `Line.Run`, from
which the caller computes the branch word (`pauseCount_word` turns a storage
fact into it). -/
theorem pauseAfterSet_routeTo_countBranch (dp : DeployParams)
    {sevm : Sevm} {devm post : Devm} {target : B256} {code : ByteArray}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      pauseAfterSet (.ok post))
    (windowT : MemWordAt devm (targetWord * 32).toNat target)
    (codeAt : CodeAt devm target.toAdr code)
    (hcall : ∀ (preC postC : Devm) (gw : B256) (rest : Stack),
      preC.stack = gw :: target :: 0 :: 284 :: 36 :: 0 :: 0 :: rest →
      MemWordAt preC (targetWord * 32).toNat target →
      CodeAt preC target.toAdr code →
      Ninst.RunCompiled sevm preC Ninst.call postC →
      MemWordAt postC (targetWord * 32).toNat target ∧
        CodeAt postC target.toAdr code)
    (hstat : ∀ (preC postC : Devm) (gw : B256) (rest : Stack),
      preC.stack = gw :: target :: 284 :: 4 :: 0 :: 32 :: rest →
      MemWordAt preC (targetWord * 32).toNat target →
      CodeAt preC target.toAdr code →
      Ninst.RunCompiled sevm preC Ninst.statcall postC →
      MemWordAt postC (targetWord * 32).toNat target ∧
        CodeAt postC target.toAdr code)
    (branchRoute : ∀ s mid : Devm,
      MemWordAt s (targetWord * 32).toNat target →
      Line.Run sevm s heartbeatCountTest mid →
      ∀ tail : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm mid
        (Func.branch (checkedHeartbeatExpiry pauseExpiryFinish)
          (Ninst.pushB256 0 ::: pauseExpiryFinish)) (.ok post),
        Func.RunCompiledTo.RouteTo
          ⟨pauseAfterSetSlot, pauseCountBranchSteps⟩ tail targetPath
          targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨pauseAfterSetSlot, []⟩ h targetPath
      targetInstruction := by
  refine routeTo_line pauseCodeGuard h (fun s0 r0 tail0 => ?_)
  have w0 : MemWordAt s0 (targetWord * 32).toNat target := by
    unfold pauseCodeGuard at r0
    rcases of_run_append (loadWord targetWord) r0 with ⟨_t, u1, u2⟩
    exact (windowT.acrossLoadWord u1).acrossLine (by line_inv) u2
  have c0 := codeAt.acrossLine (by unfold pauseCodeGuard; line_inv) r0
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail0 (fuel := 4) (by rfl)
    (fun s1 hpop1 tail1 => ?_)
  have w1 := MemWordAt.of_memory_eq hpop1.memory.symm w0
  have c1 := c0.ofState hpop1.state
  refine routeTo_line pauseCallStaging tail1 (fun s2 r2 tail2 => ?_)
  have c2 := c1.acrossLine pauseCallStaging_codeInv r2
  unfold pauseCallStaging at r2
  rcases of_run_append [Ninst.pop, Ninst.pushB256 pauseForSelector] r2
    with ⟨_t1, u1, r2⟩
  rcases of_run_append (mstoreAt 8) r2 with ⟨_t2, u2, r2⟩
  rcases of_run_append (loadWord durationWord) r2 with ⟨_t3, u3, r2⟩
  rcases of_run_append (mstoreAt 9) r2 with ⟨_t4, u4, r2⟩
  rcases of_run_append (pushList [0, 0, 36, 0x11c, 0]) r2 with ⟨t5, u5, r2⟩
  rcases of_run_append (loadWord targetWord) r2 with ⟨t6, u6, r2⟩
  have wt5 : MemWordAt t5 (targetWord * 32).toNat target :=
    ((((w1.acrossLine (by line_inv) u1).acrossMstoreAt (by decide)
      u2).acrossLoadWord u3).acrossMstoreAt (by decide) u4).acrossLine
      (by line_inv) u5
  have p5 : (0 : B256) :: 284 :: 36 :: 0 :: 0 :: [] <<+ t5.stack := by
    simp only [pushList, List.map] at u5
    rcases Line.of_run_cons u5 with ⟨_v1, x1, u5⟩
    rcases Line.of_run_cons u5 with ⟨_v2, x2, u5⟩
    rcases Line.of_run_cons u5 with ⟨_v3, x3, u5⟩
    rcases Line.of_run_cons u5 with ⟨_v4, x4, u5⟩
    rcases Line.of_run_cons u5 with ⟨_v5, x5, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 x5)
      (prefix_of_push (of_run_pushB256 x4)
        (prefix_of_push (of_run_pushB256 x3)
          (prefix_of_push (of_run_pushB256 x2)
            (prefix_of_push (of_run_pushB256 x1) nil_pref))))
  have p6 : target :: 0 :: 284 :: 36 :: 0 :: 0 :: [] <<+ t6.stack :=
    prefix_of_loadWord_window wt5 p5 u6
  have wt6 := wt5.acrossLoadWord u6
  rcases Line.of_run_cons r2 with ⟨_t7, qg, hnil⟩
  cases hnil
  obtain ⟨gw, pbg⟩ := of_run_gas qg
  have p7 : gw :: target :: 0 :: 284 :: 36 :: 0 :: 0 :: [] <<+ s2.stack :=
    prefix_of_push pbg p6
  have w2 : MemWordAt s2 (targetWord * 32).toNat target := wt6.acrossNinst qg
  have c2' := c2
  refine routeTo_next tail2 (fun s3 crossRun tail3 => ?_)
  rcases p7 with ⟨rest2, hrest2⟩
  obtain ⟨w3, c3⟩ := hcall s2 s3 gw rest2 hrest2 w2 c2' crossRun
  refine routeTo_line [Ninst.iszero] tail3 (fun s4 r4 tail4 => ?_)
  have w4 := w3.acrossLine (by line_inv) r4
  have c4 := c3.acrossLine (by line_inv) r4
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail4 (fuel := 8) (by rfl)
    (fun s5 hpop5 tail5 => ?_)
  have w5 := MemWordAt.of_memory_eq hpop5.memory.symm w4
  have c5 := c4.ofState hpop5.state
  refine routeTo_line pauseStatStaging tail5 (fun s6 r6 tail6 => ?_)
  have c6 := c5.acrossLine pauseStatStaging_codeInv r6
  unfold pauseStatStaging at r6
  rcases of_run_append [Ninst.pushB256 isPausedSelector] r6 with ⟨_y1, v1, r6⟩
  rcases of_run_append (mstoreAt 8) r6 with ⟨_y2, v2, r6⟩
  rcases of_run_append (pushList [32, 0, 4, 0x11c]) r6 with ⟨y3, v3, r6⟩
  rcases of_run_append (loadWord targetWord) r6 with ⟨y4, v4, r6⟩
  have wy3 : MemWordAt y3 (targetWord * 32).toNat target :=
    ((w5.acrossLine (by line_inv) v1).acrossMstoreAt (by decide)
      v2).acrossLine (by line_inv) v3
  have q3 : (284 : B256) :: 4 :: 0 :: 32 :: [] <<+ y3.stack := by
    simp only [pushList, List.map] at v3
    rcases Line.of_run_cons v3 with ⟨_z1, c1, v3⟩
    rcases Line.of_run_cons v3 with ⟨_z2, c2, v3⟩
    rcases Line.of_run_cons v3 with ⟨_z3, c3, v3⟩
    rcases Line.of_run_cons v3 with ⟨_z4, c4, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 c4)
      (prefix_of_push (of_run_pushB256 c3)
        (prefix_of_push (of_run_pushB256 c2)
          (prefix_of_push (of_run_pushB256 c1) nil_pref)))
  have q4 : target :: 284 :: 4 :: 0 :: 32 :: [] <<+ y4.stack :=
    prefix_of_loadWord_window wy3 q3 v4
  have wy4 := wy3.acrossLoadWord v4
  rcases Line.of_run_cons r6 with ⟨_y5, qg2, hnil2⟩
  cases hnil2
  obtain ⟨gw2, pbg2⟩ := of_run_gas qg2
  have q6 : gw2 :: target :: 284 :: 4 :: 0 :: 32 :: [] <<+ s6.stack :=
    prefix_of_push pbg2 q4
  have w6 : MemWordAt s6 (targetWord * 32).toNat target := wy4.acrossNinst qg2
  refine routeTo_next tail6 (fun s7 crossRun2 tail7 => ?_)
  rcases q6 with ⟨rest3, hrest3⟩
  obtain ⟨w7, _c7⟩ := hstat s6 s7 gw2 rest3 hrest3 w6 c6 crossRun2
  refine routeTo_line [Ninst.iszero] tail7 (fun s8 r8 tail8 => ?_)
  have w8 := w7.acrossLine (by line_inv) r8
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail8 (fuel := 8) (by rfl)
    (fun s9 hpop9 tail9 => ?_)
  have w9 := MemWordAt.of_memory_eq hpop9.memory.symm w8
  refine routeTo_line (retdataShorterThan 32) tail9 (fun s10 r10 tail10 => ?_)
  have w10 := w9.acrossLine (by unfold retdataShorterThan; line_inv) r10
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail10 (fuel := 4) (by rfl)
    (fun s11 hpop11 tail11 => ?_)
  have w11 := MemWordAt.of_memory_eq hpop11.memory.symm w10
  refine routeTo_line pauseDecodeLoad tail11 (fun s12 r12 tail12 => ?_)
  have w12 : MemWordAt s12 (targetWord * 32).toNat target := by
    unfold pauseDecodeLoad at r12
    rcases of_run_append (loadWord 0) r12 with ⟨_z, d1, d2⟩
    exact (w11.acrossLoadWord d1).acrossLine (by line_inv) d2
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail12 (fuel := 8) (by rfl)
    (fun s13 hpop13 tail13 => ?_)
  have w13 := MemWordAt.of_memory_eq hpop13.memory.symm w12
  refine routeTo_line [Ninst.pushB256 1, Ninst.eq] tail13
    (fun s14 r14 tail14 => ?_)
  have w14 := w13.acrossLine (by line_inv) r14
  refine routeTo_branchRight_of_leftRevertsOk_frame tail14 (fuel := 4) (by rfl)
    (fun s15 _w15 hpop15 tail15 => ?_)
  have w15 := MemWordAt.of_memory_eq hpop15.memory.symm w14
  refine routeTo_line pauseSuccessEventLine tail15 (fun s16 r16 tail16 => ?_)
  have w16 : MemWordAt s16 (targetWord * 32).toNat target := by
    unfold pauseSuccessEventLine at r16
    rcases of_run_append (loadWord durationWord) r16 with ⟨_z1, e1, r16⟩
    rcases of_run_append (mstoreAt 0) r16 with ⟨_z2, e2, r16⟩
    rcases of_run_append [Ninst.caller] r16 with ⟨_z3, e3, r16⟩
    rcases of_run_append (loadWord targetWord) r16 with ⟨_z4, e4, r16⟩
    rcases of_run_append [Ninst.pushB256 pauseTriggeredEvent] r16
      with ⟨_z5, e5, r16⟩
    exact (((((w15.acrossLoadWord e1).acrossMstoreAt (by decide)
      e2).acrossLine (by line_inv) e3).acrossLoadWord e4).acrossLine
      (by line_inv) e5).acrossLogWith r16
  refine routeTo_line heartbeatCountTest tail16 (fun s17 r17 tail17 => ?_)
  exact branchRoute s16 s17 w16 r17 tail17

/-! ## The two final routes

Both stated at `officialParams`: the checked arm's overflow sibling is
`arithmeticPanic`, whose certificate needs `decide +kernel` (see
`arithmeticPanic_revertsWithin` in `Blanc/LidoCircuitBreakerAttainment.lean`,
private there and re-minted here) and `decide` refuses an expected type with
a free deployment parameter; the zero arm is pinned too so the pair share
their premises verbatim. -/

set_option maxRecDepth 100000 in
/-- `checkedHeartbeatExpiry`'s overflow arm certificate; see the module
docstring of the original for why this one certificate is `decide +kernel`
where every other reverting sibling certifies `by rfl`. -/
private theorem arithmeticPanic_revertsWithinOk :
    Func.alwaysRevertsWithin 16
      ((runtime officialParams).main :: (runtime officialParams).aux)
      (Func.call arithmeticPanicSlot) = true := by decide +kernel

set_option maxRecDepth 16384 in
/-- Program entry to the count-zero arm's expiry `SSTORE` — inventory index
19, `.pauseLastTargetExpiry` — on a successful pause walk.  Execution
premises: the calldata selector and target, the entry Registry assignment
that steers the kernel, the two crossing continuations, and the count word
(nonzero: the caller's count cell reads zero after the kernel's decrement,
so its `iszero` jumps). -/
theorem runtimeMain_routeTo_pauseLastExpiry
    {sevm : Sevm} {devm post : Devm} {img : Bytes} {target : B256}
    {code : ByteArray}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux) sevm
      devm (runtime officialParams).main (.ok post))
    (image : MemImage devm img)
    (selectorEq : Sevm.selector sevm = selector "pause" [.address])
    (targetEq : Sevm.argWord sevm 0 = target)
    (hcode : CodeAt devm target.toAdr code)
    (assigned : Devm.getStorVal devm sevm.currentTarget
      (assignmentSlot target) ≠ 0)
    (hcall : ∀ (preC postC : Devm) (gw : B256) (rest : Stack),
      preC.stack = gw :: target :: 0 :: 284 :: 36 :: 0 :: 0 :: rest →
      MemWordAt preC (targetWord * 32).toNat target →
      CodeAt preC target.toAdr code →
      Ninst.RunCompiled sevm preC Ninst.call postC →
      MemWordAt postC (targetWord * 32).toNat target ∧
        CodeAt postC target.toAdr code)
    (hstat : ∀ (preC postC : Devm) (gw : B256) (rest : Stack),
      preC.stack = gw :: target :: 284 :: 4 :: 0 :: 32 :: rest →
      MemWordAt preC (targetWord * 32).toNat target →
      CodeAt preC target.toAdr code →
      Ninst.RunCompiled sevm preC Ninst.statcall postC →
      MemWordAt postC (targetWord * 32).toNat target ∧
        CodeAt postC target.toAdr code)
    (countZero : ∀ s mid : Devm,
      MemWordAt s (targetWord * 32).toNat target →
      Line.Run sevm s heartbeatCountTest mid →
      ∀ (w : B256) (rest : Stack), mid.stack = w :: rest → w ≠ 0) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h pauseLastExpiryPath
      (.reg .sstore) := by
  refine runtimeMain_routeTo_pauseKernel_ok officialParams h image
    (targetEq ▸ hcode) selectorEq
    (fun kernelStart wT wN wC hstor kcode ktail => ?_)
  rw [targetEq] at wT kcode
  refine setPauserKernel_routeTo_pauseAfterSetCall officialParams ktail wT wN
    wC kcode
    (by
      rw [show Devm.getStorVal kernelStart sevm.currentTarget
            (assignmentSlot target)
          = Devm.getStorVal devm sevm.currentTarget (assignmentSlot target)
        from congrArg (fun f : Adr → Stor =>
          (f sevm.currentTarget).get (assignmentSlot target)) hstor]
      exact assigned)
    (fun entry wTe cTe tailPA => ?_)
  refine pauseAfterSet_routeTo_countBranch officialParams tailPA wTe cTe hcall
    hstat (fun s mid ws rline btail => ?_)
  refine routeTo_branchRight_frame btail (countZero s mid ws rline)
    (fun _s' _w' _hpop armTail => ?_)
  refine routeTo_line ([Ninst.pushB256 0] ++ heartbeatExpiryStorePrefix)
    armTail (fun _s'' _r write => ?_)
  exact routeTo_head write pauseLastExpiryPath

set_option maxRecDepth 16384 in
/-- Program entry to the checked arm's expiry `SSTORE` — inventory index 18,
`.pauseRetainedTargetExpiry` — on a successful pause walk.  Same premises as
the zero arm except the count word: the caller's count cell reads nonzero
after the decrement, so the `iszero` falls through into
`checkedHeartbeatExpiry`, whose overflow sibling is the certified
`arithmeticPanic`. -/
theorem runtimeMain_routeTo_pauseRetainedExpiry
    {sevm : Sevm} {devm post : Devm} {img : Bytes} {target : B256}
    {code : ByteArray}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux) sevm
      devm (runtime officialParams).main (.ok post))
    (image : MemImage devm img)
    (selectorEq : Sevm.selector sevm = selector "pause" [.address])
    (targetEq : Sevm.argWord sevm 0 = target)
    (hcode : CodeAt devm target.toAdr code)
    (assigned : Devm.getStorVal devm sevm.currentTarget
      (assignmentSlot target) ≠ 0)
    (hcall : ∀ (preC postC : Devm) (gw : B256) (rest : Stack),
      preC.stack = gw :: target :: 0 :: 284 :: 36 :: 0 :: 0 :: rest →
      MemWordAt preC (targetWord * 32).toNat target →
      CodeAt preC target.toAdr code →
      Ninst.RunCompiled sevm preC Ninst.call postC →
      MemWordAt postC (targetWord * 32).toNat target ∧
        CodeAt postC target.toAdr code)
    (hstat : ∀ (preC postC : Devm) (gw : B256) (rest : Stack),
      preC.stack = gw :: target :: 284 :: 4 :: 0 :: 32 :: rest →
      MemWordAt preC (targetWord * 32).toNat target →
      CodeAt preC target.toAdr code →
      Ninst.RunCompiled sevm preC Ninst.statcall postC →
      MemWordAt postC (targetWord * 32).toNat target ∧
        CodeAt postC target.toAdr code)
    (countNonzero : ∀ s mid : Devm,
      MemWordAt s (targetWord * 32).toNat target →
      Line.Run sevm s heartbeatCountTest mid →
      ∀ (w : B256) (rest : Stack), mid.stack = w :: rest → w = 0) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h pauseRetainedExpiryPath
      (.reg .sstore) := by
  refine runtimeMain_routeTo_pauseKernel_ok officialParams h image
    (targetEq ▸ hcode) selectorEq
    (fun kernelStart wT wN wC hstor kcode ktail => ?_)
  rw [targetEq] at wT kcode
  refine setPauserKernel_routeTo_pauseAfterSetCall officialParams ktail wT wN
    wC kcode
    (by
      rw [show Devm.getStorVal kernelStart sevm.currentTarget
            (assignmentSlot target)
          = Devm.getStorVal devm sevm.currentTarget (assignmentSlot target)
        from congrArg (fun f : Adr → Stor =>
          (f sevm.currentTarget).get (assignmentSlot target)) hstor]
      exact assigned)
    (fun entry wTe cTe tailPA => ?_)
  refine pauseAfterSet_routeTo_countBranch officialParams tailPA wTe cTe hcall
    hstat (fun s mid ws rline btail => ?_)
  refine routeTo_branchLeft_frame btail (countNonzero s mid ws rline)
    (fun _s' _hpop armTail => ?_)
  refine routeTo_line checkedHeartbeatExpiryTest armTail
    (fun _s'' _r'' tail'' => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail'' (fuel := 16)
    arithmeticPanic_revertsWithinOk (fun _s3 arm3 => ?_)
  refine routeTo_line heartbeatExpiryStorePrefix arm3
    (fun _s4 _r4 write => ?_)
  exact routeTo_head write pauseRetainedExpiryPath

end Blanc.LidoCircuitBreaker
