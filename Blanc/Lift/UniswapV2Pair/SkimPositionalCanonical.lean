import Blanc.Lift.UniswapV2Pair.SkimSourceOccurrence
import Blanc.Lift.UniswapV2Pair.SkimPositionalFacts
import Blanc.Lift.UniswapV2Pair.SourceStaticSlotViews
import Blanc.Lift.UniswapV2Pair.SourceSlotQueueEquality
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

end Blanc.Lift.UniswapV2Pair
