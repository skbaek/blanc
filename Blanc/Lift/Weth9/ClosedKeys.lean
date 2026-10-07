import Blanc.Lift.Weth9.ClosedKeysBalanceSender
import Blanc.Lift.Weth9.ClosedKeysBalanceZero
import Blanc.Lift.Weth9.ClosedKeysAllowZeroSender
import Blanc.Lift.Weth9.ClosedKeysAllowSenderZero
import Blanc.Lift.Weth9.ClosedKeysTrace

/-! Finite trace-local key freshness and holder tracking for the closed deposit history. -/

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- The four concrete deposit slots are pairwise distinct. -/
theorem depositKeyUniverse_inj : KeyInj depositKeyUniverse := by
  intro k k' hk hk' same
  simp only [depositKeyUniverse, depositKeys, List.mem_cons,
    List.mem_nil_iff, or_false] at hk hk'
  rcases hk with rfl | rfl | rfl | rfl <;>
    rcases hk' with rfl | rfl | rfl | rfl <;>
    simp only [Key.slot, deposit_bal_sender_slot, deposit_bal_zero_slot,
      deposit_allow_zero_sender_slot, deposit_allow_sender_zero_slot] at same
  all_goals first | rfl | (exfalso; revert same; decide +kernel)

/-- None of the concrete deposit mapping slots is a metadata slot. -/
theorem depositKeyUniverse_apart : KeyApart depositKeyUniverse := by
  intro k hk
  simp only [depositKeyUniverse, depositKeys, List.mem_cons,
    List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [Key.slot, deposit_bal_sender_slot, deposit_bal_zero_slot,
      deposit_allow_zero_sender_slot, deposit_allow_sender_zero_slot, fixedSlots] <;>
    decide +kernel

/-- The finite deposit universe is fresh against deployment's empty mapping footprint. -/
theorem deposit_keys_fresh : KeysFresh (fun _ => False) depositKeys :=
  SlotFootprint.FreshKeys.of_universe depositKeyUniverse_inj depositKeyUniverse_apart
    (fun _ h => h.elim) (fun _ h => h)

/-- Actual target entries with the deposit's calldata touch only the checked finite universe. -/
theorem deposit_history_keys_included {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (metadata : ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = contractAddress →
      root.sevm.caller = senderE ∧ root.sevm.data = depositTx.data) :
    ∀ k ∈ historyTouchedKeys contractAddress trace, depositKeyUniverse k := by
  intro k hk
  obtain ⟨root, member, touched⟩ := List.mem_flatMap.mp hk
  by_cases target : root.sevm.currentTarget = contractAddress
  · simp only [target, ↓reduceIte] at touched
    obtain ⟨caller, data⟩ := metadata root member target
    exact deposit_frameKeys_included caller data k touched
  · simp only [target, ↓reduceIte, List.mem_nil_iff] at touched

/-- Finite, trace-local freshness for the actual configured deposit history. -/
theorem deposit_history_fresh {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (metadata : ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = contractAddress →
      root.sevm.caller = senderE ∧ root.sevm.data = depositTx.data) :
    KeysFresh (fun _ => False) (historyTouchedKeys contractAddress trace) :=
  SlotFootprint.FreshKeys.of_universe depositKeyUniverse_inj depositKeyUniverse_apart
    (fun _ h => h.elim) (deposit_history_keys_included trace metadata)

/-- A genuine deposit root places its holder in the history-selected key universe. -/
theorem deposit_history_holder {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    {root : Exec.Deriv} (member : root ∈ trace.rawFrames)
    (target : root.sevm.currentTarget = contractAddress) (caller : root.sevm.caller = senderE) :
    historyKeyUniverse contractAddress trace (fun _ => False) (.bal senderE) :=
  Or.inr (touchedKeys_mem member target (deposit_holder_key caller))

end Blanc.Lift.Weth9.ClosedInstance
