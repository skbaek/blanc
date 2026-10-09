import Blanc.Lift.UniswapV2Pair.SkimSecondWalk
import Blanc.Lift.UniswapV2Pair.SkimSource

/-! Raw-to-source skim handler: the raw guards, cached slots and four observed replies
of `skim_raw_inv` drive the typed source handler to success, given the four exact turn
queues and the reserve1 transport across transfer0 as explicit producer obligations. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The decoded skim recipient (masked low 160 bits of calldata word 4). -/
def skimRecipient (sevm : Sevm) : Adr := (Sevm.dataWord sevm 4).toAdr

/-- A successful balance reply as the source driver observes it. -/
def skimBalanceReply (out : Bytes) : ExternalResult :=
  { success := true, returndata := out, codeExists := true, recoveryOutput := 0 }

/-- A successful transfer reply; code existence is the observed callee fact. -/
def skimTransferReply (out : Bytes) (codeExists : Bool) : ExternalResult :=
  { success := true, returndata := out, codeExists := codeExists, recoveryOutput := 0 }

/-- The raw cached tokens and reserve0 are the source checkpoint's fields. -/
theorem skimCache_source {current : Checkpoint} {sevm : Sevm} {b : Devm}
    (slots : ReserveSlotMatches current.state sevm b)
    (token0 : (b.getStorVal sevm.currentTarget 6).toAdr = current.state.token0)
    (token1 : (b.getStorVal sevm.currentTarget 7).toAdr = current.state.token1) :
    skimToken0 sevm b = current.state.token0.toB256 ∧
      skimToken1 sevm b = current.state.token1.toB256 ∧
      skimReserve0 sevm b = Nat.toB256 current.state.reserve0.val := by
  refine ⟨?_, ?_, ?_⟩
  · change ((Devm.getStor (afterSstore sevm (afterSload sevm b 12) 12 0)
      sevm.currentTarget).get 6).toAdr.toB256 = _
    rw [afterSstore_getStor_self, Stor.get_set_ne _ (by decide : (12 : B256) ≠ 6),
      afterSload_getStor]
    change (b.getStorVal sevm.currentTarget 6).toAdr.toB256 = _
    rw [token0]
  · change ((Devm.getStor (afterSload sevm (afterSstore sevm (afterSload sevm b 12) 12 0) 6)
      sevm.currentTarget).get 7).toAdr.toB256 = _
    rw [afterSload_getStor, afterSstore_getStor_self,
      Stor.get_set_ne _ (by decide : (12 : B256) ≠ 7), afterSload_getStor]
    change (b.getStorVal sevm.currentTarget 7).toAdr.toB256 = _
    rw [token1]
  · change skimReserveMask &&& (Devm.getStor (afterSload sevm (afterSload sevm
      (afterSstore sevm (afterSload sevm b 12) 12 0) 6) 7) sevm.currentTarget).get 8 = _
    rw [afterSload_getStor, afterSload_getStor, afterSstore_getStor_self,
      Stor.get_set_ne _ (by decide : (12 : B256) ≠ 8), afterSload_getStor, B256.and_comm]
    exact slots.1

/-- The literal reserve1 extraction is the layout's reserve1 read. -/
theorem skimReserve1Word_eq (word : B256) : skimReserve1Word word = reserve1Read word := by
  unfold skimReserve1Word reserve1Read
  rw [B256.and_comm]
  rfl

theorem skimSliceD_take {xs : Bytes} (long : 32 ≤ xs.length) : xs.sliceD 0 32 0 = xs.take 32 := by
  rw [List.sliceD_eq_map]
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, List.length_take]; omega
  · intro i hi hj
    rw [List.length_map, List.length_range] at hi
    rw [List.getElem_map, List.getElem_range, List.getElem_take, Nat.zero_add,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl

theorem skimAccepted_source {out : Bytes}
    (accepted : out = [] ∨ (32 ≤ out.length ∧ Bytes.toB256 (out.sliceD 0 32 0) ≠ 0)) :
    SkimTransferAccepted out := by
  rcases accepted with empty | ⟨long, nonzero⟩
  · exact Or.inl empty
  · rw [skimSliceD_take long] at nonzero
    exact Or.inr ⟨long, nonzero⟩

end Blanc.Lift.UniswapV2Pair
