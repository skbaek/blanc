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

/-- The raw word guards are the source guards: the checked subtractions cover the
source reserves, and the raw transfer amounts are the source request amounts. -/
theorem skim_raw_source_guards {current : Checkpoint} {sevm : Sevm} {b dT0 : Devm}
    {out0 out1 : Bytes}
    (slots : ReserveSlotMatches current.state sevm b)
    (token0 : (b.getStorVal sevm.currentTarget 6).toAdr = current.state.token0)
    (token1 : (b.getStorVal sevm.currentTarget 7).toAdr = current.state.token1)
    (cover0 : skimReserve0 sevm b ≤ Bytes.toB256 (out0.take 32))
    (transport : reserve1Read (dT0.getStorVal sevm.currentTarget 8) =
      Nat.toB256 current.state.reserve1.val)
    (cover1 : skimReserve1Word (dT0.getStorVal sevm.currentTarget 8) ≤
      Bytes.toB256 (out1.take 32)) :
    current.state.reserve0.val ≤ (Bytes.toB256 (out0.take 32)).toNat ∧
      current.state.reserve1.val ≤ (Bytes.toB256 (out1.take 32)).toNat ∧
      Bytes.toB256 (out0.take 32) - skimReserve0 sevm b =
        Bytes.toB256 (out0.take 32) - Nat.toB256 current.state.reserve0.val ∧
      Bytes.toB256 (out1.take 32) - skimReserve1Word (dT0.getStorVal sevm.currentTarget 8) =
        Bytes.toB256 (out1.take 32) - Nat.toB256 current.state.reserve1.val := by
  obtain ⟨_, _, reserve0⟩ := skimCache_source slots token0 token1
  rw [skimReserve1Word_eq, transport] at cover1 ⊢
  rw [reserve0] at cover0 ⊢
  have nat0 : (Nat.toB256 current.state.reserve0.val).toNat = current.state.reserve0.val :=
    B256.toNat_toB256_of_lt (lt_trans current.state.reserve0.isLt (by decide))
  have nat1 : (Nat.toB256 current.state.reserve1.val).toNat = current.state.reserve1.val :=
    B256.toNat_toB256_of_lt (lt_trans current.state.reserve1.isLt (by decide))
  rw [B256.le_iff_toNat_le_toNat, nat0] at cover0
  rw [B256.le_iff_toNat_le_toNat, nat1] at cover1
  exact ⟨cover0, cover1, rfl, rfl⟩

/-- The raw-to-source skim handler. The raw guard facts (as `skim_raw_inv` produces them),
the slot representation and the reserve1 transport across transfer0 make the source
handler accept; any four exact turn queues then consume the four observed replies to a
successful source run. The turn queues and the transport are producer obligations. -/
theorem skim_raw_source_consumption {current : Checkpoint} {sevm : Sevm} {b dT0 : Devm}
    {invocation : List Nat} {out0 outT0 out1 outT1 : Bytes} {codeT0 codeT1 : Bool}
    (slots : ReserveSlotMatches current.state sevm b)
    (token0 : (b.getStorVal sevm.currentTarget 6).toAdr = current.state.token0)
    (token1 : (b.getStorVal sevm.currentTarget 7).toAdr = current.state.token1)
    (lockRep : b.getStorVal sevm.currentTarget 12 = current.state.unlocked)
    (value : sevm.value = 0) (nonstatic : sevm.isStatic = false)
    (unlockedRaw : b.getStorVal sevm.currentTarget 12 = 1)
    (long0 : 32 ≤ out0.length) (cover0 : skimReserve0 sevm b ≤ Bytes.toB256 (out0.take 32))
    (acceptT0 : outT0 = [] ∨ (32 ≤ outT0.length ∧ Bytes.toB256 (outT0.sliceD 0 32 0) ≠ 0))
    (long1 : 32 ≤ out1.length)
    (cover1 : skimReserve1Word (dT0.getStorVal sevm.currentTarget 8) ≤
      Bytes.toB256 (out1.take 32))
    (acceptT1 : outT1 = [] ∨ (32 ≤ outT1.length ∧ Bytes.toB256 (outT1.sliceD 0 32 0) ≠ 0))
    (transport : reserve1Read (dT0.getStorVal sevm.currentTarget 8) =
      Nat.toB256 current.state.reserve1.val) :
    let ctx := writerContext sevm invocation
    let recipient := skimRecipient sevm
    let amount0 := Bytes.toB256 (out0.take 32) - Nat.toB256 current.state.reserve0.val
    let amount1 := Bytes.toB256 (out1.take 32) - Nat.toB256 current.state.reserve1.val
    current.state.unlocked = 1 ∧
    ∀ (turns0 turns1 turns2 turns3 : Transcript)
      (executed0 executed1 executed2 executed3 : TurnsResult),
      ExactTurns (skimSourceLockedFrame current ctx recipient) (skimRequest0 current ctx)
        0 turns0 executed0 →
      (codeT0 = false → turns1 = .done) →
      ExactTurns ((skimSourceLockedFrame current ctx recipient).beginResume
          (skimRequest0 current ctx)) (skimRequest1 current recipient amount0) 0 turns1 executed1 →
      ExactTurns (executed1.frame.beginResume (skimRequest1 current recipient amount0))
        (skimRequest2 current ctx) 0 turns2 executed2 →
      (codeT1 = false → turns3 = .done) →
      ExactTurns ((executed1.frame.beginResume (skimRequest1 current recipient amount0)).beginResume
          (skimRequest2 current ctx)) (skimRequest3 current recipient amount1) 0 turns3 executed3 →
      ExactConsumes (startTyped current ctx (.skim recipient))
        (.next (skimBalanceReply out0) turns0 (.next (skimTransferReply outT0 codeT0) turns1
          (.next (skimBalanceReply out1) turns2 (.next (skimTransferReply outT1 codeT1) turns3 .done))))
        { status := .success [],
          frame := skimSourceFinalFrame (executed3.frame.beginResume
            (skimRequest3 current recipient amount1)),
          remaining := .done,
          childReturns := executed0.childReturns ++ (executed1.childReturns ++
            (executed2.childReturns ++ executed3.childReturns)) } := by
  intro ctx recipient amount0 amount1
  have unlocked : current.state.unlocked = 1 := lockRep.symm.trans unlockedRaw
  refine ⟨unlocked, ?_⟩
  intro turns0 turns1 turns2 turns3 executed0 executed1 executed2 executed3
    during0 noCode1 during1 during2 noCode3 during3
  obtain ⟨source0, source1, _, _⟩ :=
    skim_raw_source_guards (dT0 := dT0) slots token0 token1 cover0 transport cover1
  have reserve1 := skim_transfer0_reserve1 during1
  have amountEq : amount1 = Bytes.toB256 (out1.take 32) -
      Nat.toB256 executed1.frame.current.state.reserve1.val := by
    rw [reserve1]
  rw [amountEq] at during3 ⊢
  exact skim_source_exact_consumption value nonstatic unlocked rfl rfl long0 source0 during0
    rfl (skimAccepted_source acceptT0) noCode1 during1 rfl rfl long1 (by rw [reserve1]; exact source1)
    during2 rfl (skimAccepted_source acceptT1) noCode3 during3

end Blanc.Lift.UniswapV2Pair
