import Blanc.Lift.UniswapV2Pair.TransferFromEntries
import Blanc.Lift.UniswapV2Pair.TransferSource

/-! Finite allowance and sequential balance representation for the existing transferFrom handler. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def transferFromTouched (owner spender recipient : Adr) : List WriterKey :=
  [.allowance owner spender, .balance owner, .balance recipient]

def transferFromAllowanceState (st : State) (owner spender : Adr) (amount : B256) : State :=
  if st.allowance owner spender = B256.max then st else
    approveSourceState st owner spender (st.allowance owner spender - amount)

def transferFromSourceState (st : State) (owner spender recipient : Adr) (amount : B256) : State :=
  transferSourceState (transferFromAllowanceState st owner spender amount) owner recipient amount

/-- The finite allowance write reuses the accepted selected-store theorem on the one extended universe. -/
theorem WriterRep.transferFrom_allowance_store {K : WriterKey → Prop} {s : Stor} {st : State}
    {owner spender recipient : Adr} {amount : B256} (rep : WriterRep K s st)
    (fresh : WriterFreshKeys K (transferFromTouched owner spender recipient)) :
    WriterRep (WriterExtend K (transferFromTouched owner spender recipient))
      (s.set (WriterKey.slot (.allowance owner spender)) (st.allowance owner spender - amount))
      (approveSourceState st owner spender (st.allowance owner spender - amount)) := by
  have extended := rep.extend fresh
  have touched : ∀ k ∈ approveTouched owner spender,
      WriterExtend K (transferFromTouched owner spender recipient) k := by
    intro k hk
    simp only [approveTouched, List.mem_singleton] at hk
    subst k
    exact .inr (List.mem_cons.mpr (.inl rfl))
  have selectedFresh : WriterFreshKeys (WriterExtend K (transferFromTouched owner spender recipient))
      (approveTouched owner spender) :=
    Blanc.SlotFootprint.FreshKeys.of_universe extended.inj extended.apart (fun _ h => h) touched
  have stored := extended.approve_store (amount := st.allowance owner spender - amount) selectedFresh
  have keys : WriterExtend (WriterExtend K (transferFromTouched owner spender recipient))
      (approveTouched owner spender) = WriterExtend K (transferFromTouched owner spender recipient) := by
    funext k
    apply propext
    constructor
    · rintro (old | new)
      · exact old
      · exact touched k new
    · intro old
      exact .inl old
  rw [keys] at stored
  exact stored

theorem transferFrom_allowance_reads {K : WriterKey → Prop} {st : State} {sevm : Sevm} {b : Devm}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm))) :
    transferFromAllowanceWord sevm b (transferFromOwner sevm) = st.allowance (transferFromOwner sevm) sevm.caller ∧
    transferFromAllowanceWord sevm (transferFromFirst sevm b) (transferFromOwner sevm) =
      st.allowance (transferFromOwner sevm) sevm.caller := by
  have extended := rep.extend fresh
  have member : WriterExtend K
      (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm))
      (.allowance (transferFromOwner sevm) sevm.caller) := .inr (List.mem_cons.mpr (.inl rfl))
  have read := extended.selected (.allowance (transferFromOwner sevm) sevm.caller) member
  refine ⟨read, ?_⟩
  unfold transferFromAllowanceWord transferFromFirst transferFromFirstBase
  change ((afterSload sevm b (transferFromAllowanceSlot (transferFromOwner sevm) sevm.caller)).getStor
    sevm.currentTarget).get (transferFromAllowanceSlot (transferFromOwner sevm) sevm.caller) = _
  rw [afterSload_getStor]
  exact read

theorem WriterRep.transferFrom_balance_base {K : WriterKey → Prop} {st : State} {sevm : Sevm} {b : Devm}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm))) :
    WriterRep (WriterExtend K (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm)))
      ((transferFromBalanceBase sevm b).getStor sevm.currentTarget)
      (transferFromAllowanceState st (transferFromOwner sevm) sevm.caller (transferFromAmount sevm)) := by
  have reads := transferFrom_allowance_reads rep fresh
  unfold transferFromBalanceBase transferFromAllowanceState
  by_cases maximal : transferFromMaximal sevm b
  · have same : st.allowance (transferFromOwner sevm) sevm.caller = B256.max := by
      rw [← reads.1]
      exact maximal
    rw [ite_eq_left maximal, ite_eq_left same]
    unfold transferFromFirst transferFromFirstBase
    rw [afterSload_getStor]
    exact rep.extend fresh
  · have different : st.allowance (transferFromOwner sevm) sevm.caller ≠ B256.max := by
      rw [← reads.1]
      exact maximal
    rw [ite_eq_right maximal, ite_eq_right different]
    unfold transferFromStored transferFromStoreBase transferFromSecond transferFromSecondBase transferFromFirst transferFromFirstBase
    rw [afterSstore_getStor_self, afterSload_getStor, afterSload_getStor]
    unfold transferFromReduced
    rw [reads.2]
    exact rep.transferFrom_allowance_store fresh

end Blanc.Lift.UniswapV2Pair
