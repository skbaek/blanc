import Blanc.Lift.CalldataGuards
import Blanc.Lift.UniswapV2Pair.StaticViewClassify
import Blanc.Lift.UniswapV2Pair.WriterStorage
import Blanc.Lift.UniswapV2Pair.Consumption

/-! Actual successful static views consume the existing finite current representation. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Only the mapping rows actually read by this decoded view. -/
def StaticView.keys (sevm : Sevm) : StaticView → List WriterKey
  | .singleMapping .balanceOf => [.balance (mappingOwner sevm)]
  | .singleMapping .nonces => [.nonce (mappingOwner sevm)]
  | .allowance => [.allowance (mappingOwner sevm) (mappingSpender sevm)]
  | _ => []

/-- The actual selector chooses at most one decoded mapping row. -/
def staticViewDecodedKeys (sevm : Sevm) : List WriterKey :=
  if Blanc.Sevm.selector sevm = 0x70a08231 then [.balance (mappingOwner sevm)]
  else if Blanc.Sevm.selector sevm = 0x7ecebe00 then [.nonce (mappingOwner sevm)]
  else if Blanc.Sevm.selector sevm = 0xdd62ed3e then
    [.allowance (mappingOwner sevm) (mappingSpender sevm)]
  else []

theorem StaticView.keys_eq_decoded (view : StaticView) {sevm : Sevm}
    (selector : Blanc.Sevm.selector sevm = view.selector) :
    staticViewDecodedKeys sevm = view.keys sevm := by
  unfold staticViewDecodedKeys
  rw [selector]
  cases view with
  | scalar s =>
    cases s with
    | constant s => cases s <;> rfl
    | stored s => cases s <;> rfl
    | address s => cases s <;> rfl
  | string s => cases s <;> rfl
  | totalSupply => rfl
  | singleMapping s => cases s <;> rfl
  | allowance => rfl
  | getReserves => rfl

def StaticView.argumentSize : StaticView → Nat
  | .singleMapping _ => 32
  | .allowance => 64
  | _ => 0

private theorem writerRep_scalarSlots {K : WriterKey → Prop} {st : State}
    {sevm : Sevm} {b : Devm} (s : ScalarGetter)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st) : s.SlotMatches st sevm b := by
  rcases rep.fixed with ⟨_, domain, factory, token0, token1, _, _, _, price0, price1, kLast, _⟩
  cases s with
  | constant _ => exact True.intro
  | stored s =>
    cases s with
    | domainSeparator => exact domain.symm
    | price0CumulativeLast => exact price0.symm
    | price1CumulativeLast => exact price1.symm
    | kLast => exact kLast.symm
  | address s =>
    cases s with
    | factory => exact factory.symm
    | token0 => exact token0.symm
    | token1 => exact token1.symm

private theorem writerRep_reserveSlots {K : WriterKey → Prop} {st : State}
    {sevm : Sevm} {b : Devm}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st) : ReserveSlotMatches st sevm b := by
  rcases rep.fixed with ⟨_, _, _, _, _, reserve0, reserve1, timestamp, _⟩
  exact ⟨reserve0, reserve1, timestamp⟩

private theorem writerRep_singleMappingSlots {K : WriterKey → Prop} {st : State}
    {sevm : Sevm} {b : Devm} (s : SingleMappingGetter)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K ((StaticView.singleMapping s).keys sevm)) :
    s.SlotMatches st sevm b := by
  cases s with
  | balanceOf =>
    exact (rep.get_fresh (fresh.1 (.balance (mappingOwner sevm))
      (List.mem_singleton.mpr rfl))).symm
  | nonces =>
    exact (rep.get_fresh (fresh.1 (.nonce (mappingOwner sevm))
      (List.mem_singleton.mpr rfl))).symm


/-- The selected getter consumes only fixed slots and its actual trace-local mapping row. -/
theorem StaticView.bytecode_refines {K : WriterKey → Prop} {sevm : Sevm}
    {b post : Devm} {G : Nat} {st : State} (view : StaticView)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (view.keys sevm))
    (representable : sevm.data.length < 2 ^ 256)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = view.selector)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ view.argumentSize + 4 ≤ sevm.data.length ∧
      some post.output = getterResult st (view.entry sevm) ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  cases view with
  | scalar s =>
    obtain ⟨value, size, result, storage, logs⟩ :=
      getterScalar_bytecode_refines s codeEq fork selector (writerRep_scalarSlots s rep) run
    exact ⟨value, (word_calldata_guards_iff (n := 0) representable (by decide)).mp
      ⟨size, B256.zero_le _⟩, result, storage, logs⟩
  | string s =>
    obtain ⟨value, size, result, storage, logs⟩ :=
      getterString_bytecode_refines st s codeEq fork selector run
    exact ⟨value, (word_calldata_guards_iff (n := 0) representable (by decide)).mp
      ⟨size, B256.zero_le _⟩, result, storage, logs⟩
  | totalSupply =>
    obtain ⟨value, size, result, storage, logs⟩ :=
      totalSupply_bytecode_refines codeEq fork selector rep.fixed.1.symm run
    exact ⟨value, (word_calldata_guards_iff (n := 0) representable (by decide)).mp
      ⟨size, B256.zero_le _⟩, result, storage, logs⟩
  | singleMapping s =>
    have selected : Blanc.Sevm.selector sevm = s.selector := by
      cases s <;> exact selector
    have decoded : (StaticView.singleMapping s).entry sevm = s.entry (mappingOwner sevm) := by
      cases s <;> rfl
    rw [decoded]
    obtain ⟨value, size, guard, result, storage, logs⟩ :=
      singleMapping_bytecode_refines s codeEq fork selected
        (writerRep_singleMappingSlots s rep fresh) run
    exact ⟨value, (word_calldata_guards_iff (n := 32) representable (by decide)).mp
      ⟨size, guard⟩, result, storage, logs⟩
  | allowance =>
    have slot := (rep.get_fresh
      (fresh.1 (.allowance (mappingOwner sevm) (mappingSpender sevm))
        (List.mem_singleton.mpr rfl))).symm
    obtain ⟨value, size, guard, result, storage, logs⟩ :=
      allowance_bytecode_refines codeEq fork selector slot run
    exact ⟨value, (word_calldata_guards_iff (n := 64) representable (by decide)).mp
      ⟨size, guard⟩, result, storage, logs⟩
  | getReserves =>
    obtain ⟨value, size, result, storage, logs⟩ :=
      getReserves_bytecode_refines codeEq fork selector (writerRep_reserveSlots rep) run
    exact ⟨value, (word_calldata_guards_iff (n := 0) representable (by decide)).mp
      ⟨size, B256.zero_le _⟩, result, storage, logs⟩


/-- Actual successful bytecode for a selected view constructs a finished source view at the current checkpoint. -/
theorem staticView_source_handler_selected {K : WriterKey → Prop} {current : Checkpoint}
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
      frame.current = current ∧ frame.checkpoint = current ∧ frame.context = ctx := by
  have selectedFresh : WriterFreshKeys K (view.keys sevm) := by
    rw [← view.keys_eq_decoded selector]
    exact fresh
  obtain ⟨value, length, result, storage, logs⟩ :=
    view.bytecode_refines rep selectedFresh representable codeEq fork selector run
  have contextValue : ctx.value = 0 := valueRep.trans value
  have immediate : startImmediate current ctx (view.entry sevm) =
      some (.finished (Frame.enter current ctx (view.entry sevm)) post.output) := by
    simp only [startImmediate, contextValue, ne_eq, not_true_eq_false, ite_false,
      ← result, Frame.finish]
  have typed : startTyped current ctx (view.entry sevm) =
      .finished (Frame.enter current ctx (view.entry sevm)) post.output := by
    unfold startTyped
    rw [immediate]
  refine ⟨value, length, result, storage, logs, immediate, typed, ?_, rfl, rfl, rfl⟩
  rw [typed]
  exact ExactConsumes.finished (Frame.enter current ctx (view.entry sevm)) post.output

/-- Actual successful static bytecode constructs a finished source view at the current checkpoint.
The incoming freshness condition concerns only the selector's actual decoded mapping row. -/
theorem staticView_source_handler_inv {K : WriterKey → Prop} {current : Checkpoint}
    {ctx : Context} {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : WriterFreshKeys K (staticViewDecodedKeys sevm))
    (representable : sevm.data.length < 2 ^ 256)
    (valueRep : ctx.value = sevm.value)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (static : sevm.isStatic = true)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ ∃ view : StaticView,
      Blanc.Sevm.selector sevm = view.selector ∧
      view.argumentSize + 4 ≤ sevm.data.length ∧
      some post.output = getterResult current.state (view.entry sevm) ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs ∧
      let frame := Frame.enter current ctx (view.entry sevm)
      startImmediate current ctx (view.entry sevm) = some (.finished frame post.output) ∧
      startTyped current ctx (view.entry sevm) = .finished frame post.output ∧
      ExactConsumes (startTyped current ctx (view.entry sevm)) .done
        { status := .success post.output, frame := frame, remaining := .done, childReturns := [] } ∧
      frame.current = current ∧ frame.checkpoint = current ∧ frame.context = ctx := by
  obtain ⟨_, _, view, selector⟩ := staticView_bytecode_inv codeEq fork static run
  obtain ⟨value, length, result, storage, logs, immediate, typed, exact, frameCurrent, frameCheckpoint,
      frameContext⟩ :=
    staticView_source_handler_selected rep fresh representable valueRep codeEq fork view selector run
  exact ⟨value, view, selector, length, result, storage, logs, immediate, typed, exact, frameCurrent,
    frameCheckpoint, frameContext⟩

end Blanc.Lift.UniswapV2Pair
