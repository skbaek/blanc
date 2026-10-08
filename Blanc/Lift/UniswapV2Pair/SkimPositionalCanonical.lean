import Blanc.Lift.UniswapV2Pair.SkimSourceOccurrence
import Blanc.Lift.UniswapV2Pair.SkimPositionalFacts
import Blanc.Lift.UniswapV2Pair.SourceStaticSlotViews
import Blanc.Lift.UniswapV2Pair.SourceSlotQueueEquality
import Blanc.Lift.UniswapV2Pair.SourceSlotEventsEmpty
import Blanc.Lift.UniswapV2Pair.AdmittedMutableFold
import Blanc.Lift.UniswapV2Pair.SkimCanonical
import Blanc.Lift.UniswapV2Pair.MutablePositionalLockedSupply

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def skimPositionalFrame0 (current : Checkpoint) (invocation : List Nat) (root : Exec.Deriv) : Frame :=
  skimSourceLockedFrame current (writerContext root.sevm invocation) (skimRecipient root.sevm)

def skimPositionalFrame1 (current : Checkpoint) (invocation : List Nat) (root : Exec.Deriv) : Frame :=
  (skimPositionalFrame0 current invocation root).beginResume
    (skimRequest0 current (writerContext root.sevm invocation))

/-- The first source view queue belongs to the same original balance0 occurrence. -/
structure SkimFirstSource {root : Exec.Deriv} {b : Devm} {toWord : B256} {R : List B256}
    (r : SkimFirstObservation root b toWord R) (current : Checkpoint) (invocation : List Nat) where
  observed : SourceCallAt root (skimPositionalFrame0 current invocation root)
    (skimRequest0 current (writerContext root.sevm invocation)) (skimBalanceReply r.out) 0
  same : observed.call = r.call
  views : List StaticViewTurn
  mapped : views.map Prod.fst = observed.paths
  authentic : ∀ picked ∈ views, picked.Authentic (skimPositionalFrame0 current invocation root)
  during : ExactTurns (skimPositionalFrame0 current invocation root)
    (skimRequest0 current (writerContext root.sevm invocation)) 0 (staticViewTranscript views .done)
    {complete := true, frame := skimPositionalFrame0 current invocation root,
      childReturns := staticViewChildReturns (skimPositionalFrame0 current invocation root)
        (skimRequest0 current (writerContext root.sevm invocation)) 0 views}

theorem skim_first_source {root : Exec.Deriv} {b : Devm} {toWord : B256} {R : List B256}
    {K U : WriterKey → Prop} {current : Checkpoint}
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (r : SkimFirstObservation root b toWord R)
    (rep : WriterRep K (b.getStor root.sevm.currentTarget) current.state)
    (invocation : List Nat) (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode root.sevm.currentTarget).toList = sem.image)
    (fork : CoveredFork root.sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = root.sevm.currentTarget →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k) :
    Nonempty (SkimFirstSource r current invocation) := by
  let frame := skimPositionalFrame0 current invocation root
  let request := skimRequest0 current (writerContext root.sevm invocation)
  have slots : ReserveSlotMatches current.state root.sevm b :=
    ⟨rep.fixed.2.2.2.2.2.1, rep.fixed.2.2.2.2.2.2.1, rep.fixed.2.2.2.2.2.2.2.1⟩
  have token := (skimCache_source slots rep.fixed.2.2.2.1 rep.fixed.2.2.2.2.1).1
  have selected : ∃ observed : SourceCallAt root frame request (skimBalanceReply r.out) 0,
      observed.call = r.call := by
    have source := r.sourceCall frame rfl fork
    rw [token, toAdr_toB256] at source
    exact source
  obtain ⟨observed, same⟩ := selected
  have requestRep : WriterRep K (r.call.occurrence.node.devm.getStor frame.context.pair)
      frame.current.state := by
    change WriterRep K (r.call.occurrence.node.devm.getStor root.sevm.currentTarget)
      {current.state with unlocked := 0}
    rw [r.requestStor]
    exact rep.mint_lock_store
  obtain ⟨paths, views, queue, mapped, authentic, during⟩ :=
    CallOccurrenceStep.staticSlotViews r.call (frame := frame) (request := request) 0 sem image
      (by change some (r.call.occurrence.node.devm.getCode root.sevm.currentTarget).toList = _
          rw [r.requestCode]; exact installed) requestRep
      (by rw [r.sevm]; rfl) (by rw [r.sevm]; exact fork)
      (fun F member target => Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub
        (good F member target))
  have observedQueue := observed.queue
  rw [same] at observedQueue
  have pathsEq := queue.paths_unique observedQueue
  exact ⟨⟨observed, same, views, mapped.trans pathsEq, authentic, during⟩⟩

def skimPositionalAmount0 {root : Exec.Deriv} {b : Devm} {toWord : B256} {R : List B256}
    (r : SkimFirstObservation root b toWord R) (current : Checkpoint) : B256 :=
  Bytes.toB256 (r.out.take 32) - Nat.toB256 current.state.reserve0.val

/-- The first transfer's full original event queue and recursively admitted children
are tied to its same actual returned checkpoint and storage. -/
structure SkimFirstMutable {root : Exec.Deriv} {b : Devm}
    (r : SkimFourCalls root b (skimToWord root.sevm) [0x0257, 0xbc25cf77])
    (U : WriterKey → Prop) (current : Checkpoint) (invocation : List Nat) where
  observed : SourceCallAt root (skimPositionalFrame1 current invocation root)
    (skimRequest1 current (skimRecipient root.sevm) (skimPositionalAmount0 r.two.first current))
    (skimTransferReply r.two.transfer.call.returned.devm.returnData
      r.two.transfer.call.occurrence.slot.isSome) 1
  same : observed.call = r.two.transfer.call
  events : List (Log ⊕ Exec.LocatedFrame)
  turns : List MutableTurn
  checkpoint : Checkpoint
  added : List PendingLog
  rets : List ChildReturn
  queue : SourceSlotEvents observed.call root.sevm.currentTarget 1 events
  mappedPaths : events.filterMap Sum.getRight? = observed.paths
  mappedTurns : turns.map MutableTurn.event = events
  during : AdmittedMutableTurns LockedAuth (skimPositionalFrame1 current invocation root)
    (skimRequest1 current (skimRecipient root.sevm) (skimPositionalAmount0 r.two.first current))
    0 events (mutableTranscript turns .done)
    {complete := true, frame := {skimPositionalFrame1 current invocation root with current := checkpoint},
      childReturns := rets}
  authentic : ∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns →
    LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested
  rep : LockedRep U checkpoint.state (r.two.transfer.call.returned.devm.getStor root.sevm.currentTarget)
  sourceLogs : checkpoint.logs = current.logs ++ added
  rawLogs : ∃ L : List Log,
    r.two.transfer.call.returned.devm.logs = r.two.transfer.call.occurrence.node.devm.logs ++ L ∧
    added.map (PendingLog.rawWith (lockedOwnedRaw root.sevm.currentTarget)) = L.map some

theorem skim_first_mutable {root : Exec.Deriv} {b : Devm}
    {K U : WriterKey → Prop} {current : Checkpoint}
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (r : SkimFourCalls root b (skimToWord root.sevm) [0x0257, 0xbc25cf77])
    (rep : WriterRep K (b.getStor root.sevm.currentTarget) current.state)
    (invocation : List Nat) (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode root.sevm.currentTarget).toList = sem.image)
    (fork : CoveredFork root.sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = root.sevm.currentTarget →
      LockedGood U F) : Nonempty (SkimFirstMutable r U current invocation) := by
  let frame := skimPositionalFrame1 current invocation root
  let request := skimRequest1 current (skimRecipient root.sevm) (skimPositionalAmount0 r.two.first current)
  have slots : ReserveSlotMatches current.state root.sevm b :=
    ⟨rep.fixed.2.2.2.2.2.1, rep.fixed.2.2.2.2.2.2.1, rep.fixed.2.2.2.2.2.2.2.1⟩
  obtain ⟨token0, token1, reserve0⟩ :=
    skimCache_source slots rep.fixed.2.2.2.1 rep.fixed.2.2.2.2.1
  have env : r.two.first.call.returned.sevm = root.sevm :=
    Blanc.Exec.Deriv.ParentPrefix.sevm_eq (r.two.first.call.sameFrame.snoc r.two.first.call.edge)
  have selected : ∃ observed : SourceCallAt root frame request
      (skimTransferReply r.two.transfer.call.returned.devm.returnData
        r.two.transfer.call.occurrence.slot.isSome) 1, observed.call = r.two.transfer.call := by
    let actual := r.two.transfer.call
    have source : ∃ observed : SourceCallAt root frame
        (requestFor .skimTransfer0 (skimToken0 root.sevm b).toAdr
          (.transfer (skimToWord root.sevm).toAdr
            (Bytes.toB256 (r.two.first.out.take 32) - skimReserve0 root.sevm b)))
        (skimTransferReply actual.returned.devm.returnData actual.occurrence.slot.isSome) 1,
        observed.call = actual := r.two.transfer.sourceCall .skimTransfer0 frame
      (by change root.sevm.currentTarget = _; rw [env])
      (by change root.sevm.isStatic = _; rw [env]) 1 (by rw [env]; exact fork)
    rw [token0, toAdr_toB256, reserve0] at source
    dsimp only [skimToWord] at source
    rw [toAdr_toB256] at source
    exact source
  obtain ⟨observed, same⟩ := selected
  have present : (b.getCode root.sevm.currentTarget).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (installed.symm.trans (congrArg some empty)) rfl
  have inputCode : r.two.transfer.call.occurrence.node.devm.getCode root.sevm.currentTarget =
      b.getCode root.sevm.currentTarget :=
    (r.two.transfer.requestCode _).trans (r.two.first.returnCode present)
  have inputRep : LockedRep U frame.current.state
      (r.two.transfer.call.occurrence.node.devm.getStor root.sevm.currentTarget) := by
    rw [r.two.transfer.requestStor, r.two.first.returnStor]
    exact ⟨K, sub, rep.mint_lock_store, rfl⟩
  obtain ⟨events, turns, c, added, rets, queue, mappedPaths, mappedTurns, during,
    authentic, afterRep, sourceLogs, rawLogs⟩ :=
    locked_admitted_mutable_source_slot_turns inj apart sem image observed rfl
      (by change (root.sevm.isStatic || false) = false; rw [r.two.first.nonstatic]; rfl)
      (by change some (observed.call.occurrence.node.devm.getCode root.sevm.currentTarget).toList = _
          rw [same, inputCode]; exact installed)
      (by rw [same]; exact inputRep)
      (by rw [same, r.two.transfer.sevm, env]; rfl)
      (by rw [same, r.two.transfer.sevm, env]; exact fork) good
  rw [same] at afterRep rawLogs
  exact ⟨⟨observed, same, events, turns, c, added, rets, queue, mappedPaths, mappedTurns,
    during, authentic, afterRep, sourceLogs, rawLogs⟩⟩

def skimPositionalFrame2 {root : Exec.Deriv} {b : Devm}
    {r : SkimFourCalls root b (skimToWord root.sevm) [0x0257, 0xbc25cf77]}
    {U : WriterKey → Prop} {current : Checkpoint} {invocation : List Nat}
    (first : SkimFirstMutable r U current invocation) : Frame :=
  ({skimPositionalFrame1 current invocation root with current := first.checkpoint}).beginResume
    (skimRequest1 current (skimRecipient root.sevm) (skimPositionalAmount0 r.two.first current))

def skimPositionalFrame3 {root : Exec.Deriv} {b : Devm}
    {r : SkimFourCalls root b (skimToWord root.sevm) [0x0257, 0xbc25cf77]}
    {U : WriterKey → Prop} {current : Checkpoint} {invocation : List Nat}
    (first : SkimFirstMutable r U current invocation) : Frame :=
  (skimPositionalFrame2 first).beginResume (skimRequest2 current (writerContext root.sevm invocation))

def skimPositionalAmount1 {root : Exec.Deriv} {b : Devm}
    (r : SkimFourCalls root b (skimToWord root.sevm) [0x0257, 0xbc25cf77])
    (checkpoint : Checkpoint) : B256 :=
  Bytes.toB256 (r.reply.out.take 32) - Nat.toB256 checkpoint.state.reserve1.val

structure SkimSecondSource {root : Exec.Deriv} {b : Devm}
    {r : SkimFourCalls root b (skimToWord root.sevm) [0x0257, 0xbc25cf77]}
    {U : WriterKey → Prop} {current : Checkpoint} {invocation : List Nat}
    (first : SkimFirstMutable r U current invocation) where
  observed : SourceCallAt root (skimPositionalFrame2 first)
    (skimRequest2 current (writerContext root.sevm invocation)) (skimBalanceReply r.reply.out) 2
  same : observed.call = r.third.call
  views : List StaticViewTurn
  mapped : views.map Prod.fst = observed.paths
  authentic : ∀ picked ∈ views, picked.Authentic (skimPositionalFrame2 first)
  during : ExactTurns (skimPositionalFrame2 first)
    (skimRequest2 current (writerContext root.sevm invocation)) 0 (staticViewTranscript views .done)
    {complete := true, frame := skimPositionalFrame2 first,
      childReturns := staticViewChildReturns (skimPositionalFrame2 first)
        (skimRequest2 current (writerContext root.sevm invocation)) 0 views}

theorem skim_second_source {root : Exec.Deriv} {b : Devm}
    {K U : WriterKey → Prop} {current : Checkpoint} {invocation : List Nat}
    (inj : WriterInj U) (apart : WriterApart U)
    {r : SkimFourCalls root b (skimToWord root.sevm) [0x0257, 0xbc25cf77]}
    (rep : WriterRep K (b.getStor root.sevm.currentTarget) current.state)
    (first : SkimFirstMutable r U current invocation)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode root.sevm.currentTarget).toList = sem.image)
    (fork : CoveredFork root.sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = root.sevm.currentTarget →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k) : Nonempty (SkimSecondSource first) := by
  let frame := skimPositionalFrame2 first
  let request := skimRequest2 current (writerContext root.sevm invocation)
  have slots : ReserveSlotMatches current.state root.sevm b :=
    ⟨rep.fixed.2.2.2.2.2.1, rep.fixed.2.2.2.2.2.2.1, rep.fixed.2.2.2.2.2.2.2.1⟩
  have token := (skimCache_source slots rep.fixed.2.2.2.1 rep.fixed.2.2.2.2.1).2.1
  have selected : ∃ observed : SourceCallAt root frame request (skimBalanceReply r.reply.out) 2,
      observed.call = r.third.call := by
    have source := r.sourceCall2 frame rfl fork
    rw [token, toAdr_toB256] at source
    exact source
  obtain ⟨observed, same⟩ := selected
  obtain ⟨K1, sub1, wrep1, locked1⟩ := first.rep
  have requestRep : WriterRep K1 (r.third.call.occurrence.node.devm.getStor frame.context.pair)
      frame.current.state := by
    change WriterRep K1 (r.third.call.occurrence.node.devm.getStor root.sevm.currentTarget)
      first.checkpoint.state
    rw [r.requestStor2]
    exact wrep1
  have present : (b.getCode root.sevm.currentTarget).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (installed.symm.trans (congrArg some empty)) rfl
  have firstCode := r.two.first.returnCode present
  have secondCode : r.two.transfer.call.returned.devm.getCode root.sevm.currentTarget =
      b.getCode root.sevm.currentTarget :=
    (r.two.transfer.returnCode _ (by rw [firstCode]; exact present)).trans firstCode
  have env : r.third.call.occurrence.node.sevm = root.sevm :=
    Blanc.Exec.Deriv.ParentPrefix.sevm_eq r.third.call.sameFrame
  obtain ⟨paths, views, queue, mapped, authentic, during⟩ :=
    CallOccurrenceStep.staticSlotViews r.third.call (frame := frame) (request := request) 2 sem image
      (by change some (r.third.call.occurrence.node.devm.getCode root.sevm.currentTarget).toList = _
          rw [r.requestCode2, secondCode]; exact installed) requestRep
      (by rw [env]; rfl) (by rw [env]; exact fork)
      (fun F member target => Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub1
        (good F member target))
  have observedQueue := observed.queue
  rw [same] at observedQueue
  have pathsEq := queue.paths_unique observedQueue
  exact ⟨⟨observed, same, views, mapped.trans pathsEq, authentic, during⟩⟩

structure SkimSecondMutable {root : Exec.Deriv} {b : Devm}
    {r : SkimFourCalls root b (skimToWord root.sevm) [0x0257, 0xbc25cf77]}
    {U : WriterKey → Prop} {current : Checkpoint} {invocation : List Nat}
    (first : SkimFirstMutable r U current invocation) where
  observed : SourceCallAt root (skimPositionalFrame3 first)
    (skimRequest3 current (skimRecipient root.sevm) (skimPositionalAmount1 r first.checkpoint))
    (skimTransferReply r.transfer.call.returned.devm.returnData
      r.transfer.call.occurrence.slot.isSome) 3
  same : observed.call = r.transfer.call
  events : List (Log ⊕ Exec.LocatedFrame)
  turns : List MutableTurn
  checkpoint : Checkpoint
  added : List PendingLog
  rets : List ChildReturn
  queue : SourceSlotEvents observed.call root.sevm.currentTarget 3 events
  mappedPaths : events.filterMap Sum.getRight? = observed.paths
  mappedTurns : turns.map MutableTurn.event = events
  during : AdmittedMutableTurns LockedAuth (skimPositionalFrame3 first)
    (skimRequest3 current (skimRecipient root.sevm) (skimPositionalAmount1 r first.checkpoint))
    0 events (mutableTranscript turns .done)
    {complete := true, frame := {skimPositionalFrame3 first with current := checkpoint}, childReturns := rets}
  authentic : ∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns →
    LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested
  rep : LockedRep U checkpoint.state (r.transfer.call.returned.devm.getStor root.sevm.currentTarget)
  sourceLogs : checkpoint.logs = first.checkpoint.logs ++ added
  rawLogs : ∃ L : List Log,
    r.transfer.call.returned.devm.logs = r.transfer.call.occurrence.node.devm.logs ++ L ∧
    added.map (PendingLog.rawWith (lockedOwnedRaw root.sevm.currentTarget)) = L.map some

theorem skim_second_mutable {root : Exec.Deriv} {b : Devm}
    {K U : WriterKey → Prop} {current : Checkpoint} {invocation : List Nat}
    (inj : WriterInj U) (apart : WriterApart U)
    {r : SkimFourCalls root b (skimToWord root.sevm) [0x0257, 0xbc25cf77]}
    (rep : WriterRep K (b.getStor root.sevm.currentTarget) current.state)
    (first : SkimFirstMutable r U current invocation)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode root.sevm.currentTarget).toList = sem.image)
    (fork : CoveredFork root.sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = root.sevm.currentTarget →
      LockedGood U F) : Nonempty (SkimSecondMutable first) := by
  let frame := skimPositionalFrame3 first
  let request := skimRequest3 current (skimRecipient root.sevm) (skimPositionalAmount1 r first.checkpoint)
  obtain ⟨K1, sub1, wrep1, locked1⟩ := first.rep
  have slots : ReserveSlotMatches current.state root.sevm b :=
    ⟨rep.fixed.2.2.2.2.2.1, rep.fixed.2.2.2.2.2.2.1, rep.fixed.2.2.2.2.2.2.2.1⟩
  have token := (skimCache_source slots rep.fixed.2.2.2.1 rep.fixed.2.2.2.2.1).2.1
  have env0 : r.two.transfer.call.returned.sevm = root.sevm :=
    Blanc.Exec.Deriv.ParentPrefix.sevm_eq (r.two.transfer.call.sameFrame.snoc r.two.transfer.call.edge)
  have reserve1 : skimReserve1Word (r.two.transfer.call.returned.devm.getStorVal
      r.two.transfer.call.returned.sevm.currentTarget 8) = Nat.toB256 first.checkpoint.state.reserve1.val := by
    rw [env0, skimReserve1Word_eq]
    exact wrep1.fixed.2.2.2.2.2.2.1
  have env2 : r.third.call.returned.sevm = root.sevm :=
    Blanc.Exec.Deriv.ParentPrefix.sevm_eq (r.third.call.sameFrame.snoc r.third.call.edge)
  have selected : ∃ observed : SourceCallAt root frame request
      (skimTransferReply r.transfer.call.returned.devm.returnData
        r.transfer.call.occurrence.slot.isSome) 3, observed.call = r.transfer.call := by
    let actual := r.transfer.call
    let prior := r.two.transfer.call.returned
    have source : ∃ observed : SourceCallAt root frame
        (requestFor .skimTransfer1 (skimToken1 root.sevm b).toAdr
          (.transfer (skimToWord root.sevm).toAdr (Bytes.toB256 (r.reply.out.take 32) -
            skimReserve1Word (prior.devm.getStorVal prior.sevm.currentTarget 8))))
        (skimTransferReply actual.returned.devm.returnData actual.occurrence.slot.isSome) 3,
        observed.call = actual := r.transfer.sourceCall .skimTransfer1 frame
      (by change root.sevm.currentTarget = _; rw [env2])
      (by change root.sevm.isStatic = _; rw [env2]) 3 (by rw [env2]; exact fork)
    rw [token, toAdr_toB256, reserve1] at source
    dsimp only [skimToWord] at source
    rw [toAdr_toB256] at source
    exact source
  obtain ⟨observed, same⟩ := selected
  have present : (b.getCode root.sevm.currentTarget).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (installed.symm.trans (congrArg some empty)) rfl
  have firstCode := r.two.first.returnCode present
  have secondCode : r.two.transfer.call.returned.devm.getCode root.sevm.currentTarget =
      b.getCode root.sevm.currentTarget :=
    (r.two.transfer.returnCode _ (by rw [firstCode]; exact present)).trans firstCode
  have thirdCode : r.third.call.returned.devm.getCode root.sevm.currentTarget =
      b.getCode root.sevm.currentTarget :=
    (r.returnCode2 _ (by rw [secondCode]; exact present)).trans secondCode
  have inputCode := (r.transfer.requestCode root.sevm.currentTarget).trans thirdCode
  have inputRep : LockedRep U frame.current.state
      (r.transfer.call.occurrence.node.devm.getStor root.sevm.currentTarget) := by
    rw [r.transfer.requestStor, r.returnStor2]
    exact ⟨K1, sub1, wrep1, locked1⟩
  obtain ⟨events, turns, c, added, rets, queue, mappedPaths, mappedTurns, during,
    authentic, afterRep, sourceLogs, rawLogs⟩ :=
    locked_admitted_mutable_source_slot_turns inj apart sem image observed rfl
      (by change (root.sevm.isStatic || false) = false; rw [r.two.first.nonstatic]; rfl)
      (by change some (observed.call.occurrence.node.devm.getCode root.sevm.currentTarget).toList = _
          rw [same, inputCode]; exact installed)
      (by rw [same]; exact inputRep)
      (by rw [same, r.transfer.sevm, env2]; rfl)
      (by rw [same, r.transfer.sevm, env2]; exact fork) good
  rw [same] at afterRep rawLogs
  exact ⟨⟨observed, same, events, turns, c, added, rets, queue, mappedPaths, mappedTurns,
    during, authentic, afterRep, sourceLogs, rawLogs⟩⟩

def skimPositionalTranscript {root : Exec.Deriv} {b : Devm}
    {r : SkimFourCalls root b (skimToWord root.sevm) [0x0257, 0xbc25cf77]}
    {U : WriterKey → Prop} {current : Checkpoint} {invocation : List Nat}
    (balance0 : SkimFirstSource r.two.first current invocation)
    (transfer0 : SkimFirstMutable r U current invocation)
    (balance1 : SkimSecondSource transfer0) (transfer1 : SkimSecondMutable transfer0) : Transcript :=
  .next (skimBalanceReply r.two.first.out) (staticViewTranscript balance0.views .done)
    (.next (skimTransferReply r.two.transfer.call.returned.devm.returnData
        r.two.transfer.call.occurrence.slot.isSome) (mutableTranscript transfer0.turns .done)
      (.next (skimBalanceReply r.reply.out) (staticViewTranscript balance1.views .done)
        (.next (skimTransferReply r.transfer.call.returned.devm.returnData
            r.transfer.call.occurrence.slot.isSome) (mutableTranscript transfer1.turns .done) .done)))

def skimPositionalResult {root : Exec.Deriv} {b : Devm}
    {r : SkimFourCalls root b (skimToWord root.sevm) [0x0257, 0xbc25cf77]}
    {U : WriterKey → Prop} {current : Checkpoint} {invocation : List Nat}
    (balance0 : SkimFirstSource r.two.first current invocation)
    (transfer0 : SkimFirstMutable r U current invocation)
    (balance1 : SkimSecondSource transfer0) (transfer1 : SkimSecondMutable transfer0) : RunResult :=
  {status := .success [], remaining := .done,
    frame := skimSourceFinalFrame
      (({skimPositionalFrame3 transfer0 with current := transfer1.checkpoint}).beginResume
        (skimRequest3 current (skimRecipient root.sevm) (skimPositionalAmount1 r transfer0.checkpoint))),
    childReturns :=
      staticViewChildReturns (skimPositionalFrame0 current invocation root)
        (skimRequest0 current (writerContext root.sevm invocation)) 0 balance0.views ++
      (transfer0.rets ++ (staticViewChildReturns (skimPositionalFrame2 transfer0)
        (skimRequest2 current (writerContext root.sevm invocation)) 0 balance1.views ++ transfer1.rets))}

/-- Four same-slot source stages compose one recursively admitted result. The
terminal source frame is computed from the actual final return's closed suffix. -/
theorem SkimFourCalls.admittedConsumes {root : Exec.Deriv} {b : Devm}
    {K U : WriterKey → Prop} {current : Checkpoint} {invocation : List Nat}
    {r : SkimFourCalls root b (skimToWord root.sevm) [0x0257, 0xbc25cf77]}
    (rep : WriterRep K (b.getStor root.sevm.currentTarget) current.state)
    (balance0 : SkimFirstSource r.two.first current invocation)
    (transfer0 : SkimFirstMutable r U current invocation)
    (balance1 : SkimSecondSource transfer0) (transfer1 : SkimSecondMutable transfer0)
    (paid : root.sevm.value = 0) (unlocked : current.state.unlocked = 1)
    (fork : CoveredFork root.sevm.benvStat.fork) :
    AdmittedSourceConsumes LockedAuth root root 0
      (startTyped current (writerContext root.sevm invocation) (.skim (skimRecipient root.sevm)))
      (skimPositionalTranscript balance0 transfer0 balance1 transfer1)
      (skimPositionalResult balance0 transfer0 balance1 transfer1) := by
  let locals := skimSourceLocals current (skimRecipient root.sevm)
  let frame0 := skimPositionalFrame0 current invocation root
  let frame1 := skimPositionalFrame1 current invocation root
  let frame2 := skimPositionalFrame2 transfer0
  let frame3 := skimPositionalFrame3 transfer0
  let request0 := skimRequest0 current (writerContext root.sevm invocation)
  let request1 := skimRequest1 current (skimRecipient root.sevm) (skimPositionalAmount0 r.two.first current)
  let request2 := skimRequest2 current (writerContext root.sevm invocation)
  let request3 := skimRequest3 current (skimRecipient root.sevm) (skimPositionalAmount1 r transfer0.checkpoint)
  let result0 := skimBalanceReply r.two.first.out
  let result1 := skimTransferReply r.two.transfer.call.returned.devm.returnData r.two.transfer.call.occurrence.slot.isSome
  let result2 := skimBalanceReply r.reply.out
  let result3 := skimTransferReply r.transfer.call.returned.devm.returnData r.transfer.call.occurrence.slot.isSome
  have slots : ReserveSlotMatches current.state root.sevm b :=
    ⟨rep.fixed.2.2.2.2.2.1, rep.fixed.2.2.2.2.2.2.1, rep.fixed.2.2.2.2.2.2.2.1⟩
  have reserve0 := (skimCache_source slots rep.fixed.2.2.2.1 rep.fixed.2.2.2.2.1).2.2
  have cover0 := r.two.cover
  rw [reserve0, B256.le_iff_toNat_le_toNat,
    B256.toNat_toB256_of_lt (lt_trans current.state.reserve0.isLt (by decide))] at cover0
  obtain ⟨K1, sub1, wrep1, locked1⟩ := transfer0.rep
  have env0 : r.two.transfer.call.returned.sevm = root.sevm :=
    Blanc.Exec.Deriv.ParentPrefix.sevm_eq (r.two.transfer.call.sameFrame.snoc r.two.transfer.call.edge)
  have reserve1 : skimReserve1Word (r.two.transfer.call.returned.devm.getStorVal
      r.two.transfer.call.returned.sevm.currentTarget 8) = Nat.toB256 transfer0.checkpoint.state.reserve1.val := by
    rw [env0, skimReserve1Word_eq]
    exact wrep1.fixed.2.2.2.2.2.2.1
  have cover1 := r.cover
  rw [reserve1, B256.le_iff_toNat_le_toNat,
    B256.toNat_toB256_of_lt (lt_trans transfer0.checkpoint.state.reserve1.isLt (by decide))] at cover1
  have terminal := AdmittedSourceConsumes.finished (Auth := LockedAuth) (root := root)
    (start := r.transfer.call.returned) (index := 4)
    (skimSourceFinalFrame (({frame3 with current := transfer1.checkpoint}).beginResume request3)) []
    (r.noExecTail fork)
  have resumed3 := skim_resumeTransfer1 (frame := {frame3 with current := transfer1.checkpoint})
    (locals := locals) (amount := skimPositionalAmount1 r transfer0.checkpoint) (result := result3)
    rfl (skimAccepted_source r.transfer.accepted)
  change resumeSegment {frame3 with current := transfer1.checkpoint} request3
    (.skimTransfer1 locals) result3 =
      .finished (skimSourceFinalFrame
        (({frame3 with current := transfer1.checkpoint}).beginResume request3)) [] at resumed3
  rw [← resumed3] at terminal
  have last := AdmittedSourceConsumes.nextMutableCall
    (continuation := .skimTransfer1 locals) transfer1.observed
    (by rw [transfer1.same]; exact r.transfer.gap) transfer1.queue rfl
    (transfer1.observed.noCodeMutableTranscript rfl transfer1.queue transfer1.mappedTurns)
    transfer1.mappedTurns transfer1.authentic transfer1.during
    (by simpa only [transfer1.same, result3, frame3, request3, skimTransferReply, ite_true] using terminal)
  have resumed2 := skim_resumeBalance1 (frame := frame2) (locals := locals) (result := result2)
    rfl rfl r.reply.long cover1
  change resumeSegment frame2 request2 (.skimBalance1 locals) result2 =
    .suspended frame3 request3 (.skimTransfer1 locals) at resumed2
  rw [← resumed2] at last
  have query1 := AdmittedSourceConsumes.nextCall (continuation := .skimBalance1 locals)
    balance1.observed (by rw [balance1.same]; exact r.third.gap)
    (by simp only [externalStatic, skimRequest2, requestFor, BEq.rfl, Bool.or_true]) rfl
    (by intro impossible; cases impossible)
    (PositionalTurns.staticViews balance1.views balance1.mapped balance1.authentic balance1.during)
    (by simpa only [balance1.same, result2, frame2, request2, skimBalanceReply, ite_true] using last)
  have resumed1 := skim_resumeTransfer0 (frame := {frame1 with current := transfer0.checkpoint})
    (locals := locals) (amount := skimPositionalAmount0 r.two.first current) (result := result1)
    rfl (skimAccepted_source r.two.transfer.accepted)
  change resumeSegment {frame1 with current := transfer0.checkpoint} request1
    (.skimTransfer0 locals) result1 = .suspended frame2 request2 (.skimBalance1 locals) at resumed1
  rw [← resumed1] at query1
  have first := AdmittedSourceConsumes.nextMutableCall
    (continuation := .skimTransfer0 locals) transfer0.observed
    (by rw [transfer0.same]; exact r.two.transfer.gap) transfer0.queue rfl
    (transfer0.observed.noCodeMutableTranscript rfl transfer0.queue transfer0.mappedTurns)
    transfer0.mappedTurns transfer0.authentic transfer0.during
    (by simpa only [transfer0.same, result1, frame1, request1, skimTransferReply, ite_true] using query1)
  have resumed0 := skim_resumeBalance0 (frame := frame0) (locals := locals) (result := result0)
    rfl rfl r.two.first.long cover0
  change resumeSegment frame0 request0 (.skimBalance0 locals) result0 =
    .suspended frame1 request1 (.skimTransfer0 locals) at resumed0
  rw [← resumed0] at first
  have initial := AdmittedSourceConsumes.nextCall (start := root) (continuation := .skimBalance0 locals)
    balance0.observed (by rw [balance0.same]; exact r.two.first.gap)
    (by simp only [externalStatic, skimRequest0, requestFor, BEq.rfl, Bool.or_true]) rfl
    (by intro impossible; cases impossible)
    (PositionalTurns.staticViews balance0.views balance0.mapped balance0.authentic balance0.during)
    (by simpa only [balance0.same, result0, frame0, request0, skimBalanceReply, ite_true] using first)
  rw [skim_startTyped_suspended paid r.two.first.nonstatic unlocked]
  simpa only [skimPositionalTranscript, skimPositionalResult, List.append_nil,
    skimPositionalFrame0, frame3, request3, locals, skimBalanceReply, skimTransferReply] using initial

/-- One original raw Skim run, one incoming checkpoint, and the same four-call
source transcript/result with recursively admitted children and actual output. -/
structure SkimPositionalCanonicalResult (K : WriterKey → Prop) (current : Checkpoint)
    (invocation : List Nat) (root : Exec.Deriv) (b post : Devm) where
  positions : SkimFourCalls root b (skimToWord root.sevm) [0x0257, 0xbc25cf77]
  balance0 : SkimFirstSource positions.two.first current invocation
  transfer0 : SkimFirstMutable positions (WriterExtend K (skimTraceKeys root)) current invocation
  balance1 : SkimSecondSource transfer0
  transfer1 : SkimSecondMutable transfer0
  value : root.sevm.value = 0
  nonstatic : root.sevm.isStatic = false
  admitted : AdmittedSourceConsumes LockedAuth root root 0
    (startTyped current (writerContext root.sevm invocation) (.skim (skimRecipient root.sevm)))
    (skimPositionalTranscript balance0 transfer0 balance1 transfer1)
    (skimPositionalResult balance0 transfer0 balance1 transfer1)
  checkpoint : (skimPositionalResult balance0 transfer0 balance1 transfer1).frame.checkpoint = current
  context : (skimPositionalResult balance0 transfer0 balance1 transfer1).frame.context =
    writerContext root.sevm invocation
  unlocked : (skimPositionalResult balance0 transfer0 balance1 transfer1).frame.current.state.unlocked = 1
  keys : WriterKey → Prop
  grown : ∀ k, keys k → WriterExtend K (skimTraceKeys root) k
  storage : WriterRep keys (post.getStor root.sevm.currentTarget)
    (skimPositionalResult balance0 transfer0 balance1 transfer1).frame.current.state
  output : post.output = []
  sourceLogs : (skimPositionalResult balance0 transfer0 balance1 transfer1).frame.current.logs =
    current.logs ++ (transfer0.added ++ transfer1.added)
  rawLogs : ∃ L : List Log, post.logs = b.logs ++ L ∧
    (transfer0.added ++ transfer1.added).map
      (PendingLog.rawWith (lockedOwnedRaw root.sevm.currentTarget)) = L.map some

/-- The original successful-run assumptions produce the whole same-witness
canonical result. Actual transfer entry bits and original child paths are retained. -/
theorem skim_positional_canonical {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (inj : WriterInj (WriterExtend K (skimTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)))
    (apart : WriterApart (WriterExtend K (skimTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩))) :
    Nonempty (SkimPositionalCanonicalResult K current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b post) := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  let U := WriterExtend K (skimTraceKeys root)
  have sub : ∀ k, K k → U k := fun _ tracked => Or.inl tracked
  have staticGood : ∀ F ∈ Exec.rawFrameRoots root.exc,
      F.sevm.currentTarget = root.sevm.currentTarget → ∀ k ∈ staticViewDecodedKeys F.sevm, U k :=
    fun F member target k touched => Or.inr ((skimTraceKeys_contains member target).2 k touched)
  have lockedGood : ∀ F ∈ Exec.rawFrameRoots root.exc,
      F.sevm.currentTarget = root.sevm.currentTarget → LockedGood U F := by
    intro F member target child inner same k touched
    have deep := Exec.rawFrameRoots_trans member inner
    rcases List.mem_append.mp touched with pairKey | viewKey
    · exact Or.inr ((skimTraceKeys_contains deep (same.trans target)).1 k pairKey)
    · exact Or.inr ((skimTraceKeys_contains deep (same.trans target)).2 k viewKey)
  obtain ⟨positions⟩ := skim_four_calls_of_success codeEq fork selector run
  obtain ⟨balance0⟩ := skim_first_source inj apart sub positions.two.first rep invocation sem image
    installed fork staticGood
  obtain ⟨transfer0⟩ := skim_first_mutable inj apart sub positions rep invocation sem image
    installed fork lockedGood
  obtain ⟨balance1⟩ := skim_second_source inj apart rep transfer0 sem image installed fork staticGood
  obtain ⟨transfer1⟩ := skim_second_mutable inj apart rep transfer0 sem image installed fork lockedGood
  have guards := skim_raw_flag_inv codeEq fork selector run
  have paid := guards.1
  have unlocked : current.state.unlocked = 1 := rep.fixed.2.2.2.2.2.2.2.2.2.2.2.symm.trans guards.2.2.2.1
  have admitted := positions.admittedConsumes rep balance0 transfer0 balance1 transfer1 paid unlocked fork
  obtain ⟨K3, sub3, wrep3, locked3⟩ := transfer1.rep
  obtain ⟨M, gas, postEq⟩ := positions.post_image (post := post) rfl fork
  have storage : WriterRep K3 (post.getStor sevm.currentTarget)
      (skimPositionalResult balance0 transfer0 balance1 transfer1).frame.current.state := by
    have postStor : post.getStor sevm.currentTarget =
        (afterSstore sevm positions.transfer.call.returned.devm 12 1).getStor sevm.currentTarget := by
      have projected := congrArg (fun d : Devm => d.getStor sevm.currentTarget) postEq
      exact projected
    rw [afterSstore_getStor_self] at postStor
    rw [postStor]
    exact wrep3.mint_unlock_store
  have output : post.output = [] := (positions.output_eq rfl fork).trans freshOutput
  refine ⟨{
    positions := positions
    balance0 := balance0
    transfer0 := transfer0
    balance1 := balance1
    transfer1 := transfer1
    value := paid
    nonstatic := positions.two.first.nonstatic
    admitted := admitted
    checkpoint := rfl
    context := rfl
    unlocked := rfl
    keys := K3
    grown := sub3
    storage := storage
    output := output
    sourceLogs := ?_
    rawLogs := ?_
  }⟩
  · change transfer1.checkpoint.logs ++ [] = current.logs ++ (transfer0.added ++ transfer1.added)
    rw [List.append_nil, transfer1.sourceLogs, transfer0.sourceLogs, List.append_assoc]
  · obtain ⟨L1, raw1, images1⟩ := transfer0.rawLogs
    obtain ⟨L3, raw3, images3⟩ := transfer1.rawLogs
    refine ⟨L1 ++ L3, ?_, ?_⟩
    · rw [postEq, St, Devm.setMach_logs, afterSstore_logs, raw3,
        positions.transfer.input, St, Devm.setMach_logs, positions.reply.reply.logs,
        SkimTwoCalls.secondWorld, temporalAccountAccessBase_logs, afterSload_logs, raw1,
        positions.two.transfer.input, St, Devm.setMach_logs, positions.two.first.reply.logs,
        temporalAccountAccessBase_logs]
      unfold skimCachedWorld syncLockedWorld
      rw [afterSload_logs, afterSload_logs, afterSload_logs, afterSstore_logs, afterSload_logs,
        List.append_assoc]
    · rw [List.map_append, images1, images3, List.map_append]

end Blanc.Lift.UniswapV2Pair
