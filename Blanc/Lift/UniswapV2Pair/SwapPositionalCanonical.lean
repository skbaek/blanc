import Blanc.Lift.UniswapV2Pair.SwapPositionalSourceSuffix

/-! The original Swap execution has one complete admitted positional source result. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- One original root and checkpoint supply the physical calls, full admitted
queues, transcript, source result and actual output/storage/log images. -/
structure SwapPositionalCanonicalResult (K : WriterKey → Prop) (current : Checkpoint)
    (invocation : List Nat) (root : Exec.Deriv) (b post : Devm) where
  positions : SwapPhysicalResult root b post
  entryFacts : SwapSourcePrefix (WriterExtend K (swapTraceKeys root)) current invocation root.sevm b
  frontFrame : Frame
  frontIndex : Nat
  frontIndex_eq : frontIndex =
    (if swapAmount0Out root.sevm = 0 then 0 else 1) +
    (if swapAmount1Out root.sevm = 0 then 0 else 1) +
    (if swapDataLength root.sevm = 0 then 0 else 1)
  frontTranscript : Transcript → Transcript
  frontReturns : List ChildReturn
  queries : SwapBalancePairSource positions.balances (WriterExtend K (swapTraceKeys root))
    (writerContext root.sevm invocation) current b frontFrame frontIndex
  updated : SwapSourceUpdate positions.balances queries
  transcript : Transcript
  transcript_eq : transcript = frontTranscript queries.transcript
  result : RunResult
  result_eq : result =
    {status := .success [], frame := updated.finalFrame, remaining := .done,
      childReturns := frontReturns ++ queries.childReturns}
  admitted : AdmittedSourceConsumes LockedAuth root root 0
    (startTyped current (writerContext root.sevm invocation) (swapDecodedEntry root.sevm))
    transcript result
  checkpoint : result.frame.checkpoint = current
  context : result.frame.context = writerContext root.sevm invocation
  unlocked : result.frame.current.state.unlocked = 1
  grown : ∀ k, updated.keys k → WriterExtend K (swapTraceKeys root) k
  storage : WriterRep updated.keys (post.getStor root.sevm.currentTarget) result.frame.current.state
  bound0 : positions.balances.balance0.toNat < 2 ^ 112
  bound1 : positions.balances.balance1.toNat < 2 ^ 112
  added : List PendingLog
  raw : List Log
  sourceLogs : result.frame.current.logs = current.logs ++ added
  rawLogs : post.logs = b.logs ++ raw
  images : added.map (PendingLog.rawWith (swapOwnedRaw root.sevm.currentTarget)) = raw.map some
  output : post.output = []
  actualOutput : result.status = .success post.output
  remaining : result.remaining = .done
  prefixForeign : ∀ a, a ≠ root.sevm.currentTarget →
    (swapPrefixWorld root.sevm b).getStor a = b.getStor a
  foreign : ∀ a, a ≠ root.sevm.currentTarget →
    post.getStor a = positions.balances.optional.callback.world.getStor a

/-- The actual post-callback tail emits exactly the same observed Sync then Swap. -/
theorem SwapPositionalCanonicalResult.terminal_logs {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {root : Exec.Deriv} {b post : Devm}
    (r : SwapPositionalCanonicalResult K current invocation root b post) :
    post.logs = r.positions.balances.optional.callback.world.logs ++
      [swapSyncLog root.sevm.currentTarget r.positions.balances.balance0 r.positions.balances.balance1,
       swapEventLog root.sevm r.positions.balances.input0 r.positions.balances.input1
         (swapAmount0Out root.sevm) (swapAmount1Out root.sevm) (swapRecipientWord root.sevm)] := by
  obtain ⟨M, gas, image⟩ := r.positions.image
  have postLogs : post.logs = r.positions.balances.finalWorld.logs := by
    simpa only [St, Devm.setMach_logs] using congrArg (fun d : Devm => d.logs) image
  rw [postLogs, SwapBalances.finalWorld, afterSstore_logs]
  change (updateWorld root.sevm r.positions.balances.second.step.returned.devm
    (swapRawReserve0 root.sevm b) (swapRawReserve1 root.sevm b)
    r.positions.balances.balance0 r.positions.balances.balance1).logs ++ [_] = _
  rw [r.updated.updateLogs, r.positions.balances.second.reply.logs,
    temporalAccountAccessBase_logs, r.positions.balances.first.reply.logs,
    temporalAccountAccessBase_logs, List.append_assoc]
  rfl

/-- Positional consumption projects the SAME recursively admitted source proof. -/
theorem SwapPositionalCanonicalResult.positional {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {root : Exec.Deriv} {b post : Devm}
    (r : SwapPositionalCanonicalResult K current invocation root b post) :
    PositionalConsumes root root 0
      (startTyped current (writerContext root.sevm invocation) (swapDecodedEntry root.sevm))
      r.transcript r.result := r.admitted.positional

/-- Recursive admission applies to that SAME selected positional proof. -/
theorem SwapPositionalCanonicalResult.admission {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {root : Exec.Deriv} {b post : Devm}
    (r : SwapPositionalCanonicalResult K current invocation root b post) :
    SourceAdmission LockedAuth r.positional := r.admitted.choose_spec

/-- Erasure retains the SAME entry, transcript, result and actual output coupling. -/
theorem SwapPositionalCanonicalResult.forget {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {root : Exec.Deriv} {b post : Devm}
    (r : SwapPositionalCanonicalResult K current invocation root b post) :
    ExactConsumes
      (startTyped current (writerContext root.sevm invocation) (swapDecodedEntry root.sevm))
      r.transcript r.result := r.positional.forget

/-- The existing public successful-run premises produce one complete original-root
Swap result, with recursively admitted actual queues and same-witness projections. -/
theorem swap_positional_canonical {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (hashTInj : WriterInj (WriterExtend K
      (swapTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)))
    (hashTApart : WriterApart (WriterExtend K
      (swapTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩))) :
    Nonempty (SwapPositionalCanonicalResult K current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b post) := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  let U := WriterExtend K (swapTraceKeys root)
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
  obtain ⟨positions⟩ := swap_physical_result codeEq fork selector run
  obtain entryFacts := swap_source_prefix_of_success invocation rep sub codeEq fork selector run
  obtain ⟨frontFrame, frontT, frontReturns, inv, reach⟩ :=
    swap_source_callbacks positions.balances.optional entryFacts hashTInj hashTApart
      sem image installed fork lockedGood
  let index := (if swapAmount0Out sevm = 0 then 0 else 1) +
    (if swapAmount1Out sevm = 0 then 0 else 1) +
    (if swapDataLength sevm = 0 then 0 else 1)
  obtain ⟨queries⟩ := swap_balance_pair_source positions.balances index hashTInj hashTApart
    sem image installed inv rfl rfl fork staticGood
  obtain ⟨updated⟩ := swap_source_update positions.balances entryFacts queries positions.facts
  have suffix := swap_source_suffix_admitted positions.balances entryFacts queries updated fork
  have admitted := reach queries.transcript _ suffix
  obtain ⟨checkpoint, context, unlocked⟩ := updated.frame_facts
  obtain ⟨added, raw, sourceLogs, rawLogs, images⟩ := updated.logs entryFacts positions.facts
  obtain ⟨M, gas, postImage⟩ := positions.image
  have postLogs : post.logs = positions.balances.finalWorld.logs := by
    simpa only [St, Devm.setMach_logs] using congrArg (fun d : Devm => d.logs) postImage
  have output : post.output = [] := positions.output.trans freshOutput
  refine ⟨{
    positions := positions
    entryFacts := entryFacts
    frontFrame := frontFrame
    frontIndex := index
    frontIndex_eq := rfl
    frontTranscript := frontT
    frontReturns := frontReturns
    queries := queries
    updated := updated
    transcript := frontT queries.transcript
    transcript_eq := rfl
    result := {
      status := .success []
      frame := updated.finalFrame
      remaining := .done
      childReturns := frontReturns ++ queries.childReturns
    }
    result_eq := rfl
    admitted := admitted
    checkpoint := checkpoint
    context := context
    unlocked := unlocked
    grown := updated.grown
    storage := updated.post_storage
    bound0 := positions.facts.bound0
    bound1 := positions.facts.bound1
    added := added
    raw := raw
    sourceLogs := sourceLogs
    rawLogs := postLogs.trans rawLogs
    images := images
    output := output
    actualOutput := by rw [output]
    remaining := rfl
    prefixForeign := ?_
    foreign := positions.foreign_storage
  }⟩
  intro a foreign
  unfold swapPrefixWorld mintLockedWorld
  rw [afterSload_getStor, afterSload_getStor, afterSload_getStor,
    afterSstore_getStor_ne _ _ _ _ _ (Ne.symm foreign), afterSload_getStor]

end Blanc.Lift.UniswapV2Pair
