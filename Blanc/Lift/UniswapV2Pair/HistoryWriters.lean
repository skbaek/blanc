import Blanc.Lift.UniswapV2Pair.HistoryReplay
import Blanc.Lift.UniswapV2Pair.TransferSource
import Blanc.Lift.UniswapV2Pair.TransferFromSource
import Blanc.Lift.UniswapV2Pair.InitializeSource

/-! Literal noncalling public writer executions produce connected history steps.
The incoming model state is universally carried by the storage representation. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def HistoryStep.transfer (located : Exec.LocatedFrame) : HistoryStep :=
  { located := located, entry := transferDecodedEntry located.frame.sevm, transcript := .done }

def HistoryStep.transferFrom (located : Exec.LocatedFrame) : HistoryStep :=
  { located := located, entry := transferFromDecodedEntry located.frame.sevm, transcript := .done }

def HistoryStep.initialize (located : Exec.LocatedFrame) : HistoryStep :=
  { located := located, entry := initializeDecodedEntry located.frame.sevm, transcript := .done }

theorem transfer_history_replay {U : WriterKey → Prop} {sevm : Sevm}
    {b post : Devm} {G : Nat} (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (committed : Execution.commits (.ok post) = true) (located : Exec.LocatedFrame)
    (original : located.frame = Exec.Frame.ofRun run committed)
    (injective : WriterInj U) (apart : WriterApart U)
    (touched : ∀ k ∈ transferTouched sevm.caller (transferRecipient sevm), U k)
    (representable : sevm.data.length < 2 ^ 256)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xa9059cbb) :
    HistoryReplay U (b.getStor sevm.currentTarget)
      [HistoryStep.transfer located] (post.getStor sevm.currentTarget) := by
  intro st K included rep
  have fresh : WriterFreshKeys K (transferTouched sevm.caller (transferRecipient sevm)) :=
    Blanc.SlotFootprint.FreshKeys.of_universe injective apart included touched
  obtain ⟨_, _, _, residual, result, consumed⟩ :=
    transfer_bytecode_exact_consumes (current := {state := st, logs := [], updates := []})
      (invocation := located.path) rep fresh representable codeEq fork selector run
  refine ⟨transferSourceState st sevm.caller (transferRecipient sevm) (transferAmount sevm),
    WriterExtend K (transferTouched sevm.caller (transferRecipient sevm)), ?_,
    fun _ h => Or.inl h, ?_, result.representation⟩
  · change SourceReplay st [(HistoryStep.transfer located).source] _
    rw [HistoryStep.source, HistoryStep.transfer, original]
    exact .cons consumed rfl (.nil _)
  · intro k member
    rcases member with tracked | written
    · exact included k tracked
    · exact touched k written

theorem transferFrom_history_replay {U : WriterKey → Prop} {sevm : Sevm}
    {b post : Devm} {G : Nat} (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (committed : Execution.commits (.ok post) = true) (located : Exec.LocatedFrame)
    (original : located.frame = Exec.Frame.ofRun run committed)
    (injective : WriterInj U) (apart : WriterApart U)
    (touched : ∀ k ∈ transferFromTouched (transferFromOwner sevm) sevm.caller
      (transferFromRecipient sevm), U k)
    (representable : sevm.data.length < 2 ^ 256)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x23b872dd) :
    HistoryReplay U (b.getStor sevm.currentTarget)
      [HistoryStep.transferFrom located] (post.getStor sevm.currentTarget) := by
  intro st K included rep
  have fresh : WriterFreshKeys K (transferFromTouched (transferFromOwner sevm) sevm.caller
      (transferFromRecipient sevm)) :=
    Blanc.SlotFootprint.FreshKeys.of_universe injective apart included touched
  obtain ⟨_, _, _, residual, result, consumed⟩ :=
    transferFrom_bytecode_exact_consumes (current := {state := st, logs := [], updates := []})
      (invocation := located.path) rep fresh representable codeEq fork selector run
  refine ⟨transferFromSourceState st (transferFromOwner sevm) sevm.caller
      (transferFromRecipient sevm) (transferFromAmount sevm),
    WriterExtend K (transferFromTouched (transferFromOwner sevm) sevm.caller
      (transferFromRecipient sevm)), ?_, fun _ h => Or.inl h, ?_, result.representation⟩
  · change SourceReplay st [(HistoryStep.transferFrom located).source] _
    rw [HistoryStep.source, HistoryStep.transferFrom, original]
    exact .cons consumed rfl (.nil _)
  · intro k member
    rcases member with tracked | written
    · exact included k tracked
    · exact touched k written

theorem initialize_history_replay {U : WriterKey → Prop} {sevm : Sevm}
    {b post : Devm} {G : Nat} (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (committed : Execution.commits (.ok post) = true) (located : Exec.LocatedFrame)
    (original : located.frame = Exec.Frame.ofRun run committed)
    (representable : sevm.data.length < 2 ^ 256) (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x485cc955) :
    HistoryReplay U (b.getStor sevm.currentTarget)
      [HistoryStep.initialize located] (post.getStor sevm.currentTarget) := by
  intro st K included rep
  obtain ⟨_, _, _, _, residual, result, consumed⟩ :=
    initialize_bytecode_exact_consumes (current := {state := st, logs := [], updates := []})
      (invocation := located.path) rep representable freshOutput codeEq fork selector run
  refine ⟨initializeSourceState st (initializeToken0 sevm) (initializeToken1 sevm), K,
    ?_, fun _ h => h, included, result.representation⟩
  change SourceReplay st [(HistoryStep.initialize located).source] _
  rw [HistoryStep.source, HistoryStep.initialize, original]
  exact .cons consumed rfl (.nil _)

end Blanc.Lift.UniswapV2Pair
