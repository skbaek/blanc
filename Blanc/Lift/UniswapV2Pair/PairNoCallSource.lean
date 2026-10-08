import Blanc.Lift.UniswapV2Pair.PairNoCallEntries
import Blanc.Lift.UniswapV2Pair.SourceOccurrence
import Blanc.Lift.UniswapV2Pair.TransferSource
import Blanc.Lift.UniswapV2Pair.ApproveSource
import Blanc.Lift.UniswapV2Pair.TransferFromSource
import Blanc.Lift.UniswapV2Pair.InitializeSource
import Blanc.Lift.UniswapV2Pair.StaticViewSource

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Add an actual-root annotation to the supplied finished source witness.
The incoming segment, result frame and actual returned bytes are unchanged. -/
theorem PairNoCallEntry.positionalConsumes {sevm : Sevm} {b post : Devm} {G : Nat}
    (entry : PairNoCallEntry) (codeEq : sevm.code = code)
    (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = entry.selector)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    {segment : SegmentResult} {frame : Frame}
    (consumed : ExactConsumes segment .done
      {status := .success post.output, frame := frame, remaining := .done, childReturns := []}) :
    PositionalConsumes ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ 0 segment .done
      {status := .success post.output, frame := frame, remaining := .done, childReturns := []} := by
  cases consumed with
  | finished frame =>
    exact .finished frame post.output (entry.root_noExec codeEq fork selector run)

/-- Every existing view family maps to its actual no-call dispatcher entry. -/
def StaticView.noCallEntry : StaticView → PairNoCallEntry
  | .scalar (.constant .decimals) => .decimals
  | .scalar (.constant .minimumLiquidity) => .minimumLiquidity
  | .scalar (.constant .permitTypehash) => .permitTypehash
  | .scalar (.stored .domainSeparator) => .domainSeparator
  | .scalar (.stored .price0CumulativeLast) => .price0CumulativeLast
  | .scalar (.stored .price1CumulativeLast) => .price1CumulativeLast
  | .scalar (.stored .kLast) => .kLast
  | .scalar (.address .factory) => .factory
  | .scalar (.address .token0) => .token0
  | .scalar (.address .token1) => .token1
  | .string .name => .name
  | .string .symbol => .symbol
  | .totalSupply => .totalSupply
  | .singleMapping .balanceOf => .balanceOf
  | .singleMapping .nonces => .nonces
  | .allowance => .allowance
  | .getReserves => .getReserves

theorem StaticView.noCallEntry_selector (view : StaticView) :
    view.noCallEntry.selector = view.selector := by
  cases view with
  | scalar s =>
    cases s with
    | constant s => cases s <;> rfl
    | stored s => cases s <;> rfl
    | address s => cases s <;> rfl
  | string s => cases s <;> rfl
  | singleMapping s => cases s <;> rfl
  | totalSupply | allowance | getReserves => rfl

/-- Preserve the existing successful source result and exact consumption witness,
with an actual original-root call-free annotation of the same frame and bytes. -/
theorem transfer_bytecode_positional_consumes {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : WriterFreshKeys K (transferTouched sevm.caller (transferRecipient sevm)))
    (representable : sevm.data.length < 2 ^ 256)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xa9059cbb)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ 68 ≤ sevm.data.length ∧ sevm.isStatic = false ∧
      ∃ residual, TransferSourceResult K current invocation sevm b post residual ∧
        ExactConsumes (startTyped current (writerContext sevm invocation) (transferDecodedEntry sevm)) .done
          { status := .success post.output,
            frame := transferSourceFrame current (writerContext sevm invocation)
              (transferRecipient sevm) (transferAmount sevm),
            remaining := .done, childReturns := [] } ∧
        PositionalConsumes ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
          ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ 0 (startTyped current (writerContext sevm invocation) (transferDecodedEntry sevm)) .done
          { status := .success post.output,
            frame := transferSourceFrame current (writerContext sevm invocation)
              (transferRecipient sevm) (transferAmount sevm),
            remaining := .done, childReturns := [] } := by
  obtain ⟨value, size, nonstatic, residual, result, consumed⟩ := transfer_bytecode_exact_consumes rep fresh representable codeEq fork selector run
  exact ⟨value, size, nonstatic, residual, result, consumed,
    PairNoCallEntry.transfer.positionalConsumes codeEq fork selector run consumed⟩

/-- Preserve the existing successful source result and exact consumption witness,
with an actual original-root call-free annotation of the same frame and bytes. -/
theorem approve_bytecode_positional_consumes {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : WriterFreshKeys K (approveTouched sevm.caller (approveSpender sevm)))
    (representable : sevm.data.length < 2 ^ 256)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ 68 ≤ sevm.data.length ∧ sevm.isStatic = false ∧
      ∃ residual, ApproveSourceResult K current invocation sevm b post residual ∧
        ExactConsumes (startTyped current (writerContext sevm invocation) (approveDecodedEntry sevm)) .done
          { status := .success post.output,
            frame := approveSourceFrame current (writerContext sevm invocation)
              (approveSpender sevm) (approveAmount sevm),
            remaining := .done, childReturns := [] } ∧
        PositionalConsumes ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
          ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ 0 (startTyped current (writerContext sevm invocation) (approveDecodedEntry sevm)) .done
          { status := .success post.output,
            frame := approveSourceFrame current (writerContext sevm invocation)
              (approveSpender sevm) (approveAmount sevm),
            remaining := .done, childReturns := [] } := by
  obtain ⟨value, size, nonstatic, residual, result, consumed⟩ := approve_bytecode_exact_consumes rep fresh representable codeEq fork selector run
  exact ⟨value, size, nonstatic, residual, result, consumed,
    PairNoCallEntry.approve.positionalConsumes codeEq fork selector run consumed⟩

/-- Preserve the existing successful source result and exact consumption witness,
with an actual original-root call-free annotation of the same frame and bytes. -/
theorem transferFrom_bytecode_positional_consumes {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : WriterFreshKeys K (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm)))
    (representable : sevm.data.length < 2 ^ 256)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x23b872dd)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ 100 ≤ sevm.data.length ∧ sevm.isStatic = false ∧
      ∃ residual, TransferFromSourceResult K current invocation sevm b post residual ∧
        ExactConsumes (startTyped current (writerContext sevm invocation) (transferFromDecodedEntry sevm)) .done
          { status := .success post.output,
            frame := transferFromSourceFrame current (writerContext sevm invocation)
              (transferFromOwner sevm) (transferFromRecipient sevm) (transferFromAmount sevm),
            remaining := .done, childReturns := [] } ∧
        PositionalConsumes ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
          ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ 0 (startTyped current (writerContext sevm invocation) (transferFromDecodedEntry sevm)) .done
          { status := .success post.output,
            frame := transferFromSourceFrame current (writerContext sevm invocation)
              (transferFromOwner sevm) (transferFromRecipient sevm) (transferFromAmount sevm),
            remaining := .done, childReturns := [] } := by
  obtain ⟨value, size, nonstatic, residual, result, consumed⟩ := transferFrom_bytecode_exact_consumes rep fresh representable codeEq fork selector run
  exact ⟨value, size, nonstatic, residual, result, consumed,
    PairNoCallEntry.transferFrom.positionalConsumes codeEq fork selector run consumed⟩

/-- Preserve the existing successful source result and exact consumption witness,
with an actual original-root call-free annotation of the same frame and bytes. -/
theorem initialize_bytecode_positional_consumes {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (representable : sevm.data.length < 2 ^ 256) (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x485cc955)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ 68 ≤ sevm.data.length ∧ sevm.caller = current.state.factory ∧
      sevm.isStatic = false ∧ ∃ residual, InitializeSourceResult K current invocation sevm b post residual ∧
        ExactConsumes (startTyped current (writerContext sevm invocation) (initializeDecodedEntry sevm)) .done
          { status := .success post.output,
            frame := initializeSourceFrame current (writerContext sevm invocation)
              (initializeToken0 sevm) (initializeToken1 sevm),
            remaining := .done, childReturns := [] } ∧
        PositionalConsumes ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
          ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ 0 (startTyped current (writerContext sevm invocation) (initializeDecodedEntry sevm)) .done
          { status := .success post.output,
            frame := initializeSourceFrame current (writerContext sevm invocation)
              (initializeToken0 sevm) (initializeToken1 sevm),
            remaining := .done, childReturns := [] } := by
  obtain ⟨value, size, authorized, nonstatic, residual, result, consumed⟩ := initialize_bytecode_exact_consumes rep representable freshOutput codeEq fork selector run
  exact ⟨value, size, authorized, nonstatic, residual, result, consumed,
    PairNoCallEntry.«initialize».positionalConsumes codeEq fork selector run consumed⟩

/-- All seventeen views retain the donor's exact incoming checkpoint/context,
selected entry, actual output and finished source frame. -/
theorem staticView_source_positional_selected {K : WriterKey → Prop} {current : Checkpoint}
    {ctx : Context} {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : WriterFreshKeys K (staticViewDecodedKeys sevm))
    (representable : sevm.data.length < 2 ^ 256)
    (valueRep : ctx.value = sevm.value)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (view : StaticView) (selector : Blanc.Sevm.selector sevm = view.selector)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧
      view.argumentSize + 4 ≤ sevm.data.length ∧
      some post.output = getterResult current.state (view.entry sevm) ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs ∧
      let frame := Frame.enter current ctx (view.entry sevm)
      startImmediate current ctx (view.entry sevm) = some (.finished frame post.output) ∧
      startTyped current ctx (view.entry sevm) = .finished frame post.output ∧
      ExactConsumes (startTyped current ctx (view.entry sevm)) .done
        { status := .success post.output, frame := frame, remaining := .done, childReturns := [] } ∧
      PositionalConsumes ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
        ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ 0
        (startTyped current ctx (view.entry sevm)) .done
        { status := .success post.output, frame := frame, remaining := .done, childReturns := [] } ∧
      frame.current = current ∧ frame.checkpoint = current ∧ frame.context = ctx := by
  obtain ⟨value, length, output, storage, logs, immediate, typed, consumed,
      sameCurrent, sameCheckpoint, sameContext⟩ :=
    staticView_source_handler_selected rep fresh representable valueRep codeEq fork view selector run
  have selected : Blanc.Sevm.selector sevm = view.noCallEntry.selector :=
    selector.trans view.noCallEntry_selector.symm
  exact ⟨value, length, output, storage, logs, immediate, typed, consumed,
    view.noCallEntry.positionalConsumes codeEq fork selected run consumed,
    sameCurrent, sameCheckpoint, sameContext⟩

end Blanc.Lift.UniswapV2Pair
