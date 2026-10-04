import Blanc.Lift.UniswapV2Pair.SkimHandler
import Blanc.Lift.UniswapV2Pair.LockedSupply
import Blanc.Lift.UniswapV2Pair.StaticViewTurns

/-!
# Canonical skim frame

Every successful raw skim run at the Pair code consumes the typed source skim over the
four external observations, with turn queues DERIVED from the actual child executions:
the two balance queries contribute their retained static Pair views, the two transfers
contribute their retained committed Pair frames (the lock-free entries, via
`lockedPairSupply`) and their actual foreign LOGs. The Pair storage after the run is the
final source state's finite representation; the trace-local key universe is HASH-T.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- Decoded rows of every actually entered Pair frame of the run (HASH-T universe rows). -/
def skimTraceKeys (root : Exec.Deriv) : List WriterKey :=
  (Exec.rawFrameRoots root.exc).flatMap fun F =>
    if F.sevm.currentTarget = root.sevm.currentTarget
    then pairDecodedKeys F.sevm ++ staticViewDecodedKeys F.sevm else []

theorem skimTraceKeys_contains {root : Exec.Deriv} {F : Exec.Deriv}
    (member : F ∈ Exec.rawFrameRoots root.exc)
    (target : F.sevm.currentTarget = root.sevm.currentTarget) :
    (∀ k ∈ pairDecodedKeys F.sevm, k ∈ skimTraceKeys root) ∧
      ∀ k ∈ staticViewDecodedKeys F.sevm, k ∈ skimTraceKeys root := by
  have inside : ∀ k ∈ pairDecodedKeys F.sevm ++ staticViewDecodedKeys F.sevm,
      k ∈ skimTraceKeys root := by
    intro k touched
    apply List.mem_flatMap.mpr
    refine ⟨F, member, ?_⟩
    rw [ite_eq_left target]
    exact touched
  exact ⟨fun k touched => inside k (List.mem_append_left _ touched),
    fun k touched => inside k (List.mem_append_right _ touched)⟩

/-- One lifted STATICCALL step of a Pair frame contributes the retained static Pair views of
its actual child, at the incoming frame, or nothing when no code frame is entered. -/
theorem skim_static_call_turns {U K : WriterKey → Prop} (inj : WriterInj U)
    (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    {D : Exec.Deriv} {frame : Frame} {request : Request} {sevm : Sevm} {pre d : Devm}
    (call : Blanc.Lift.StepIn D sevm pre (.exec .staticcall) d)
    (installed : some (pre.getCode frame.context.pair).toList = sem.image)
    (rep : WriterRep K (pre.getStor frame.context.pair) frame.current.state)
    (time : frame.context.timestamp = sevm.benvStat.time)
    (fork : CoveredFork sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots D.exc, F.sevm.currentTarget = frame.context.pair →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k) :
    ∃ views : List StaticViewTurn,
      ExactTurns frame request 0 (staticViewTranscript views .done)
        { complete := true, frame := frame,
          childReturns := staticViewChildReturns frame request 0 views } ∧
      (∀ picked ∈ views, picked.Authentic frame) ∧
      (views = [] ∨ ∃ (child : Evm) (raw : Execution)
        (childRun : Exec child.pc child.sta child.dyna raw),
        (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots D.exc) ∧
        views.map Prod.fst =
          (Exec.retainedTargetTurnsAt frame.context.pair [] childRun).filterMap
            Sum.getRight?) := by
  have nothing : ∃ views : List StaticViewTurn,
      ExactTurns frame request 0 (staticViewTranscript views .done)
        { complete := true, frame := frame,
          childReturns := staticViewChildReturns frame request 0 views } ∧
      (∀ picked ∈ views, picked.Authentic frame) ∧
      (views = [] ∨ ∃ (child : Evm) (raw : Execution)
        (childRun : Exec child.pc child.sta child.dyna raw),
        (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots D.exc) ∧
        views.map Prod.fst =
          (Exec.retainedTargetTurnsAt frame.context.pair [] childRun).filterMap
            Sum.getRight?) := by
    refine ⟨[], ExactTurns.done frame request 0, ?_, Or.inl rfl⟩
    intro picked member
    simp only [List.not_mem_nil] at member
  obtain ⟨xl, inRoots, pc, stepRun⟩ := call
  have xrun : Xinst.Run sevm pre .staticcall xl (.ok d) := by
    rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at stepRun
    exact stepRun
  cases xl with
  | none => exact nothing
  | some slot =>
    obtain ⟨child, raw⟩ := slot
    obtain ⟨childRun, childRoots⟩ := inRoots
    unfold Xinst.Run XStep.Run at xrun
    cases spawned : Xinst.step sevm pre .staticcall with
    | done result =>
      rw [spawned] at xrun
      cases xrun.1
    | spawn callee resume =>
      rw [spawned] at xrun
      obtain ⟨_, runFrame, _⟩ := xrun
      unfold RunFrame at runFrame
      cases entered : callee.enter with
      | done result =>
        rw [entered] at runFrame
        cases runFrame.1
      | run evm =>
        rw [entered] at runFrame
        obtain ⟨raw', slotEq, _⟩ := runFrame
        cases slotEq
        have nonempty : pre.getCode frame.context.pair ≠ .empty := by
          intro empty
          have imageEmpty : sem.image = some [] := by
            rw [← installed, empty, ByteArray.toList_empty]
          exact sem.ne_nil imageEmpty rfl
        obtain ⟨world, _, entry, stat, childFork, short⟩ :=
          Xinst.spawn_child_world fork spawned entered
        have childInstalled := CodeSem.At.callChild spawned entered (Or.inr rfl) installed
        have childRep : WriterRep K (child.dyna.getStor frame.context.pair)
            frame.current.state := by
          rw [world frame.context.pair nonempty]
          exact rep
        have childStatic : child.sta.isStatic = true :=
          (Blanc.Frame.enter_run_isStatic entered).trans
            (Xinst.step_staticcall_spawn_isStatic spawned)
        have fresh : ∀ located ∈ (Exec.retainedTargetTurnsAt frame.context.pair [] childRun).filterMap
            Sum.getRight?, WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm) := by
          intro located member
          by_cases committed : Execution.commits raw = true
          · rw [Exec.retainedTargetTurnsAt_filterMap_eq _ _ _ committed] at member
            obtain ⟨root, target⟩ :=
              Exec.retainedTargetFramesFromAt_rawFrameRoot _ childRun committed member
            have same : (Exec.Frame.rootDeriv located.frame).sevm = located.frame.sevm := rfl
            have keys := good (Exec.Frame.rootDeriv located.frame) (childRoots _ root)
              (same.symm ▸ target)
            rw [same] at keys
            exact Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub keys
          · have empty : Exec.retainedTargetTurnsAt frame.context.pair [] childRun = [] := by
              rw [Exec.retainedTargetTurnsAt, dite_eq_right committed]
            rw [empty, List.filterMap_nil] at member
            exact (List.not_mem_nil member).elim
        obtain ⟨views, mapped, authentic, consumed⟩ :=
          staticView_raw_retained_turns_inv (request := request) (turn := 0) (path := [])
            sem image childRun childInstalled childRep fresh (fun _ => ⟨entry.1, entry.2.1⟩)
            short (by rw [stat]; exact time) childStatic childFork
        exact ⟨views, consumed, authentic, Or.inr ⟨child, raw, childRun, childRoots, mapped⟩⟩

private theorem skim_St_getStor (x : Devm) (S : List B256) (M : Mem) (g : Nat) (a : Adr) :
    Devm.getStor (St x S M g) a = Devm.getStor x a := rfl

private theorem skim_St_getCode (x : Devm) (S : List B256) (M : Mem) (g : Nat) (a : Adr) :
    (St x S M g).getCode a = x.getCode a := rfl

private theorem skim_tAAB_getStor (base : Devm) (a x : Adr) :
    Devm.getStor (temporalAccountAccessBase base a) x = Devm.getStor base x := by
  unfold temporalAccountAccessBase
  split <;> rfl

private theorem skim_tAAB_getCode (base : Devm) (a x : Adr) :
    (temporalAccountAccessBase base a).getCode x = base.getCode x := by
  unfold temporalAccountAccessBase
  split <;> rfl

private theorem skim_cached_getStor (sevm : Sevm) (b : Devm) :
    Devm.getStor (skimCachedWorld sevm b) sevm.currentTarget =
      (Devm.getStor b sevm.currentTarget).set 12 0 := by
  unfold skimCachedWorld syncLockedWorld
  rw [afterSload_getStor, afterSload_getStor, afterSload_getStor, afterSstore_getStor_self,
    afterSload_getStor]

private theorem skim_cached_getCode (sevm : Sevm) (b : Devm) (a : Adr) :
    (skimCachedWorld sevm b).getCode a = b.getCode a := by
  unfold skimCachedWorld syncLockedWorld
  rw [afterSload_getCode, afterSload_getCode, afterSload_getCode, afterSstore_getCode,
    afterSload_getCode]

private theorem skim_cached_output (sevm : Sevm) (b : Devm) :
    (skimCachedWorld sevm b).output = b.output := by
  unfold skimCachedWorld syncLockedWorld
  rw [afterSload_output, afterSload_output, afterSload_output, afterSstore_output,
    afterSload_output]

/-- The actual first query and transfer0 steps of the run, up to their forwarded gas. -/
def SkimFirstSteps (D : Exec.Deriv) (sevm : Sevm) (b : Devm) (out0 : Bytes) (d : Devm) :
    Prop :=
  ∃ (S0 S1 : List B256) (M0 M1 : Mem) (g0 g1 : Nat) (d0 : Devm),
    Blanc.Lift.StepIn D sevm (St (temporalAccountAccessBase (skimCachedWorld sevm b)
      (skimToken0 sevm b).toAdr) S0 M0 g0) (.exec .staticcall) d0 ∧ d0.returnData = out0 ∧
    Blanc.Lift.StepIn D sevm (St d0 S1 M1 g1) (.exec .call) d

/-- The actual second query and transfer1 steps after transfer0's world `d`. -/
def SkimSecondSteps (D : Exec.Deriv) (sevm : Sevm) (d : Devm) (t1 : B256) (out1 : Bytes)
    (d2 : Devm) : Prop :=
  ∃ (S0 S1 : List B256) (M0 M1 : Mem) (g0 g1 : Nat) (d1 : Devm),
    Blanc.Lift.StepIn D sevm (St (temporalAccountAccessBase (afterSload sevm d 8)
      (t1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr) S0 M0 g0) (.exec .staticcall) d1 ∧
    d1.returnData = out1 ∧ Blanc.Lift.StepIn D sevm (St d1 S1 M1 g1) (.exec .call) d2

/-- Canonical skim frame: every successful raw skim run consumes the typed source skim
over turn queues derived from its actual children, under trace-local HASH-T. The second
half is stated for a fitting transfer0 reply pointer (`skimFirstPointer_fit`). -/
theorem skim_bytecode_exact_consumes {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (hashTInj : WriterInj (WriterExtend K
      (skimTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)))
    (hashTApart : WriterApart (WriterExtend K
      (skimTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩))) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    let ctx := writerContext sevm invocation
    let recipient := skimRecipient sevm
    sevm.value = 0 ∧ sevm.isStatic = false ∧
    ∃ (out0 : Bytes) (d : Devm), SkimFirstSteps root sevm b out0 d ∧
      (96 ≤ (skimFirstPointer d.returnData).toNat →
        (skimFirstPointer d.returnData).toNat + 1024 < 2 ^ 256 →
      ∃ (out1 : Bytes) (d2 : Devm) (views0 views1 : List StaticViewTurn)
        (turns1 turns3 : List MutableTurn) (final : Frame) (rets : List ChildReturn)
        (K' : WriterKey → Prop) (added : List PendingLog),
        SkimSecondSteps root sevm d (skimToken1 sevm b) out1 d2 ∧
        ExactConsumes (startTyped current ctx (.skim recipient))
          (.next (skimBalanceReply out0) (staticViewTranscript views0 .done)
            (.next (skimTransferReply d.returnData true) (mutableTranscript turns1 .done)
              (.next (skimBalanceReply out1) (staticViewTranscript views1 .done)
                (.next (skimTransferReply d2.returnData true) (mutableTranscript turns3 .done)
                  .done))))
          { status := .success [], frame := final, remaining := .done, childReturns := rets } ∧
        final.checkpoint = current ∧ final.context = ctx ∧
        (∀ k, K' k → WriterExtend K (skimTraceKeys root) k) ∧
        WriterRep K' (post.getStor sevm.currentTarget) final.current.state ∧
        final.current.state.unlocked = 1 ∧
        final.current.state.liquidityCore = current.state.liquidityCore ∧
        final.current.logs = current.logs ++ added ∧
        (∃ L : List Log, post.logs = b.logs ++ L ∧
          added.map (PendingLog.rawWith (lockedOwnedRaw sevm.currentTarget)) = L.map some) ∧
        (∀ picked ∈ views0 ++ views1, Blanc.Sevm.selector picked.1.frame.sevm = picked.2.selector ∧
          picked.1.frame.sevm.currentTarget = sevm.currentTarget) ∧
        (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns1 ++ turns3 →
          LockedAuth located.frame.sevm located.frame.post entry nested) ∧
        (views0 = [] ∨ ∃ (child : Evm) (raw : Execution)
          (childRun : Exec child.pc child.sta child.dyna raw),
          (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots root.exc) ∧
          views0.map Prod.fst =
            (Exec.retainedTargetTurnsAt sevm.currentTarget [] childRun).filterMap
              Sum.getRight?) ∧
        (views1 = [] ∨ ∃ (child : Evm) (raw : Execution)
          (childRun : Exec child.pc child.sta child.dyna raw),
          (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots root.exc) ∧
          views1.map Prod.fst =
            (Exec.retainedTargetTurnsAt sevm.currentTarget [] childRun).filterMap
              Sum.getRight?) ∧
        (turns1 = [] ∨ ∃ (child : Evm) (raw : Execution)
          (childRun : Exec child.pc child.sta child.dyna raw)
          (committed : Execution.commits raw = true),
          (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots root.exc) ∧
          turns1.map MutableTurn.event =
            Exec.targetLogEventsFrom sevm.currentTarget [] 0 childRun committed) ∧
        (turns3 = [] ∨ ∃ (child : Evm) (raw : Execution)
          (childRun : Exec child.pc child.sta child.dyna raw)
          (committed : Execution.commits raw = true),
          (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots root.exc) ∧
          turns3.map MutableTurn.event =
            Exec.targetLogEventsFrom sevm.currentTarget [] 0 childRun committed) ∧
        post.output = []) := by
  intro root ctx recipient
  let U := WriterExtend K (skimTraceKeys root)
  have sub : ∀ k, K k → U k := fun k tracked => Or.inl tracked
  have staticGood : ∀ F ∈ Exec.rawFrameRoots root.exc,
      F.sevm.currentTarget = sevm.currentTarget → ∀ k ∈ staticViewDecodedKeys F.sevm, U k :=
    fun F member target k touched => Or.inr ((skimTraceKeys_contains member target).2 k touched)
  have lockedGood : ∀ F ∈ Exec.rawFrameRoots root.exc,
      F.sevm.currentTarget = sevm.currentTarget → LockedGood U F.sevm :=
    fun F member target k touched => Or.inr ((skimTraceKeys_contains member target).1 k touched)
  have supply := lockedPairSupply hashTInj hashTApart sevm.currentTarget
  have repCongr : ∀ st (s s' : Stor), (∀ k, s'.get k = s.get k) →
      LockedRep U st s → LockedRep U st s' := fun _ _ _ same rep => LockedRep.congr same rep
  obtain ⟨value, _, _, unlockedRaw, first⟩ := skim_raw_inv codeEq fork selector run
  unfold SkimFirstFacts at first
  dsimp only at first
  obtain ⟨nonstatic, _, _, _, d0, out0, call0, post0, long0, _, _, cover0, _, _, _, d, _, _,
    call1, _, _, output1, _, accept1, second⟩ := first
  have nonempty : b.getCode sevm.currentTarget ≠ .empty := by
    intro empty
    have imageEmpty : sem.image = some [] := by
      rw [← installed, empty, ByteArray.toList_empty]
    exact sem.ne_nil imageEmpty rfl
  have nonemptyList : (b.getCode sevm.currentTarget).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (installed.symm.trans (congrArg some empty)) rfl
  refine ⟨value, nonstatic, out0, d, ⟨_, _, _, _, _, _, d0, call0, post0.returnData, call1⟩, ?_⟩
  intro low high
  have secondFacts := second low high
  unfold SkimSecondFacts at secondFacts
  dsimp only at secondFacts
  obtain ⟨_, _, _, d1, out1, call2, post2, long1, _, _, cover1, _, _, _, d2, call3, _, output3,
    _, accept3, _, _, postEq⟩ := secondFacts
  -- source frames and requests
  let frame0 := skimSourceLockedFrame current ctx recipient
  let request0 := skimRequest0 current ctx
  let amount0 := Bytes.toB256 (out0.take 32) - Nat.toB256 current.state.reserve0.val
  let frame1 := frame0.beginResume request0
  let request1 := skimRequest1 current recipient amount0
  -- raw worlds
  have cachedStor := skim_cached_getStor sevm b
  have world0 : Devm.getStor d0 sevm.currentTarget =
      (Devm.getStor b sevm.currentTarget).set 12 0 := by
    rw [post0.stor, skim_tAAB_getStor, cachedStor]
  have code0 : (temporalAccountAccessBase (skimCachedWorld sevm b)
      (skimToken0 sevm b).toAdr).getCode sevm.currentTarget = b.getCode sevm.currentTarget := by
    rw [skim_tAAB_getCode, skim_cached_getCode]
  have lockRep0 := rep.mint_lock_store
  have pair0 : frame0.context.pair = sevm.currentTarget := rfl
  -- query 0
  obtain ⟨views0, turns0Exact, authentic0, derived0⟩ :=
    skim_static_call_turns (frame := frame0) (request := request0) hashTInj hashTApart sub sem
      image call0 (by rw [pair0, skim_St_getCode, code0]; exact installed)
      (by rw [pair0, skim_St_getStor, skim_tAAB_getStor, cachedStor]; exact lockRep0)
      rfl fork staticGood
  -- transfer 0
  have codeD0 : d0.getCode sevm.currentTarget = b.getCode sevm.currentTarget := by
    rw [Blanc.Lift.StepIn.codePreserve call0 sevm.currentTarget
      (by rw [skim_St_getCode, code0]; exact nonemptyList), skim_St_getCode, code0]
  have mutable1 : externalStatic frame1 request1 = false := by
    unfold externalStatic
    rw [show frame1.context.isStatic = sevm.isStatic from rfl, nonstatic]
    rfl
  obtain ⟨turns1, c1, added1, rets1, turns1Exact, auth1, rep1, logs1, ⟨L1, raw1, images1⟩,
      derived1⟩ :=
    mutable_call_turns (frame := frame1) (request := request1) supply repCongr sem image call1
      (Or.inl rfl) rfl mutable1 (by rw [skim_St_getCode, codeD0]; exact installed)
      ⟨K, sub, by rw [skim_St_getStor, world0]; exact lockRep0, rfl⟩ rfl fork lockedGood
  obtain ⟨K1, sub1, wrep1, locked1⟩ := rep1
  have reserve1 := skim_transfer0_reserve1 turns1Exact
  have transport : reserve1Read (d.getStorVal sevm.currentTarget 8) =
      Nat.toB256 current.state.reserve1.val := by
    have fixed := wrep1.fixed.2.2.2.2.2.2.1
    change reserve1Read (d.getStorVal sevm.currentTarget 8) =
      Nat.toB256 c1.state.reserve1.val at fixed
    rw [fixed]
    exact congrArg (fun r : Fin (2 ^ 112) => Nat.toB256 r.val) reserve1
  -- query 1
  let frame2 : Frame := ({ frame1 with current := c1 } : Frame).beginResume request1
  let request2 := skimRequest2 current ctx
  have codeD : d.getCode sevm.currentTarget = b.getCode sevm.currentTarget := by
    rw [Blanc.Lift.StepIn.codePreserve call1 sevm.currentTarget
      (by rw [skim_St_getCode, codeD0]; exact nonemptyList), skim_St_getCode, codeD0]
  have pair2 : frame2.context.pair = sevm.currentTarget := rfl
  obtain ⟨views1, turns2Exact, authentic1, derived2⟩ :=
    skim_static_call_turns (frame := frame2) (request := request2) hashTInj hashTApart sub1 sem
      image call2
      (by rw [pair2, skim_St_getCode, skim_tAAB_getCode, afterSload_getCode, codeD]
          exact installed)
      (by rw [pair2, skim_St_getStor, skim_tAAB_getStor, afterSload_getStor]; exact wrep1)
      rfl fork staticGood
  -- transfer 1
  let amount1 := Bytes.toB256 (out1.take 32) - Nat.toB256 current.state.reserve1.val
  let frame3 := frame2.beginResume request2
  let request3 := skimRequest3 current recipient amount1
  have world1 : Devm.getStor d1 sevm.currentTarget = Devm.getStor d sevm.currentTarget := by
    rw [post2.stor, skim_tAAB_getStor, afterSload_getStor]
  have codeD1 : d1.getCode sevm.currentTarget = b.getCode sevm.currentTarget := by
    rw [Blanc.Lift.StepIn.codePreserve call2 sevm.currentTarget
      (by rw [skim_St_getCode, skim_tAAB_getCode, afterSload_getCode, codeD]
          exact nonemptyList),
      skim_St_getCode, skim_tAAB_getCode, afterSload_getCode, codeD]
  have mutable3 : externalStatic frame3 request3 = false := by
    unfold externalStatic
    rw [show frame3.context.isStatic = sevm.isStatic from rfl, nonstatic]
    rfl
  obtain ⟨turns3, c3, added3, rets3, turns3Exact, auth3, rep3, logs3, ⟨L3, raw3, images3⟩,
      derived3⟩ :=
    mutable_call_turns (frame := frame3) (request := request3) supply repCongr sem image call3
      (Or.inl rfl) rfl mutable3 (by rw [skim_St_getCode, codeD1]; exact installed)
      ⟨K1, sub1, by rw [skim_St_getStor, world1]; exact wrep1, locked1⟩ rfl fork lockedGood
  obtain ⟨K3, sub3, wrep3, _⟩ := rep3
  -- the source handler
  have slots : ReserveSlotMatches current.state sevm b :=
    ⟨rep.fixed.2.2.2.2.2.1, rep.fixed.2.2.2.2.2.2.1, rep.fixed.2.2.2.2.2.2.2.1⟩
  obtain ⟨_, consume⟩ := skim_raw_source_consumption (invocation := invocation)
    (codeT0 := true) (codeT1 := true) slots rep.fixed.2.2.2.1 rep.fixed.2.2.2.2.1
    rep.fixed.2.2.2.2.2.2.2.2.2.2.2 value nonstatic unlockedRaw long0 cover0 accept1 long1
    cover1 accept3 transport
  have consumed := consume _ _ _ _ _ _ _ _ turns0Exact (fun absent => by cases absent)
    turns1Exact turns2Exact (fun absent => by cases absent) turns3Exact
  refine ⟨out1, d2, views0, views1, turns1, turns3, _, _, K3, added1 ++ added3,
    ⟨_, _, _, _, _, _, d1, call2, post2.returnData, call3⟩, consumed, rfl, rfl,
    fun k tracked => sub3 k tracked, ?_, rfl, ?_, ?_, ⟨L1 ++ L3, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [postEq, skim_St_getStor, afterSstore_getStor_self]
    exact wrep3.mint_unlock_store
  · exact skim_source_liquidity consumed rfl
  · change c3.logs ++ List.map _ [] = _
    rw [List.map_nil, List.append_nil, logs3]
    change c1.logs ++ added3 = _
    rw [logs1, List.append_assoc]
    rfl
  · rw [postEq]
    change (afterSstore sevm d2 12 1).logs = _
    rw [afterSstore_logs, raw3]
    change d1.logs ++ L3 = _
    rw [post2.logs, temporalAccountAccessBase_logs, afterSload_logs, raw1]
    change d0.logs ++ L1 ++ L3 = _
    rw [post0.logs, temporalAccountAccessBase_logs, List.append_assoc]
    unfold skimCachedWorld syncLockedWorld
    rw [afterSload_logs, afterSload_logs, afterSload_logs, afterSstore_logs, afterSload_logs]
  · rw [List.map_append, List.map_append, images1, images3]
  · intro picked member
    rcases List.mem_append.mp member with left | right
    · exact ⟨(authentic0 picked left).2.2.2.2.2.1, (authentic0 picked left).1⟩
    · exact ⟨(authentic1 picked right).2.2.2.2.2.1, (authentic1 picked right).1⟩
  · intro located entry nested member
    rcases List.mem_append.mp member with left | right
    · exact auth1 located entry nested left
    · exact auth3 located entry nested right
  · exact derived0
  · exact derived2
  · rcases derived1 with ⟨empty, _, _⟩ | ⟨child, raw, childRun, committed, _, roots, events, _⟩
    · exact Or.inl empty
    · exact Or.inr ⟨child, raw, childRun, committed, roots, events⟩
  · rcases derived3 with ⟨empty, _, _⟩ | ⟨child, raw, childRun, committed, _, roots, events, _⟩
    · exact Or.inl empty
    · exact Or.inr ⟨child, raw, childRun, committed, roots, events⟩
  · rw [postEq]
    change (afterSstore sevm d2 12 1).output = []
    rw [afterSstore_output, output3, post2.output rfl]
    rw [temporalAccountAccessBase_output, afterSload_output, output1, post0.output rfl,
      temporalAccountAccessBase_output, skim_cached_output, freshOutput]

end Blanc.Lift.UniswapV2Pair
