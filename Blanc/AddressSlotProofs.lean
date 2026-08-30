import Blanc.AddressSlot
import Blanc.CommonProofs

/-!
# Functional facts for Solidity address slots

Contract-neutral, value-carrying inversions for the executable vocabulary in
`Blanc.AddressSlot`.  They expose the exact low-160-bit load and the exact
packed write, including preservation of the raw upper ninety-six bits.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

/-- The low-160-bit address-slot projection is exactly the ordinary `B256`
address conversion followed by re-encoding. -/
theorem addressSlotReadWord_eq_toAdr_toB256 (raw : B256) :
    addressSlotReadWord raw = raw.toAdr.toB256 := by
  have lowMask (x : UInt64) :
      (0x00000000ffffffff : UInt64) &&& x =
        x.toUInt32.toUInt64 := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_and, UInt64.toNat_toUInt32,
      UInt32.toNat_toUInt64]
    rw [Nat.and_comm]
    change x.toNat &&& 2 ^ 32 - 1 = x.toNat % 2 ^ 32
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have andMax (x : UInt64) : UInt64.max &&& x = x := by
    apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_and]
    have hmax : UInt64.max.toBitVec = BitVec.allOnes 64 := by rfl
    rw [hmax]
    exact BitVec.allOnes_and
  have b128AndMax (x : B128) : B128.max &&& x = x := by
    apply Prod.ext <;> apply andMax
  have hmask : (~~~ addressMask) =
      (⟨⟨0, 0x00000000ffffffff⟩, B128.max⟩ : B256) := by
    decide +kernel
  unfold addressSlotReadWord
  rw [hmask]
  rcases raw with ⟨⟨high, middle⟩, low⟩
  simp only [B256.toAdr, Adr.toB256, B256.and_eq_and_prod_and,
    B128.and_eq_and_prod_and, UInt64.zero_and]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · exact lowMask middle
  · exact b128AndMax low

@[simp] theorem addressSlotReadWord_toB256 (address : Adr) :
    addressSlotReadWord address.toB256 = address.toB256 := by
  rw [addressSlotReadWord_eq_toAdr_toB256, toAdr_toB256]

private theorem shr96_ones_eq_not_addressMask :
    (~~~ (0 : B256)) >>> (96 : Nat).toB256.toNat = ~~~ addressMask := by
  rw [B256.toNat_toB256, Nat.lo_eq_of_lt (by omega)]
  rfl

/-- Exact value and frame effect of `loadAddressWordAt`. -/
theorem of_loadAddressWordAt_val
    {sevm : Sevm} {pre post : Devm} {slot : B256} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (run : Line.Run sevm pre (loadAddressWordAt slot) post) :
    addressSlotReadWord
        (pre.getStorVal sevm.currentTarget slot) :: tail <<+ post.stack ∧
      post.memory = pre.memory ∧
      post.logs = pre.logs ∧
      Devm.getStor post = Devm.getStor pre := by
  unfold loadAddressWordAt at run
  obtain ⟨loadPost, loadLine, cleanLine⟩ :=
    of_run_append [pushB256 slot, sload] run
  rcases Line.of_run_cons loadLine with ⟨slotPost, qslot, loadLine⟩
  rcases Line.of_run_cons loadLine with ⟨_, qload, hnil⟩
  cases hnil
  rcases Line.of_run_cons cleanLine with ⟨zeroPost, qzero, cleanLine⟩
  rcases Line.of_run_cons cleanLine with ⟨notPost, qnot, cleanLine⟩
  rcases Line.of_run_cons cleanLine with ⟨shiftPost, qshift, cleanLine⟩
  rcases Line.of_run_cons cleanLine with ⟨andPost, qshr, cleanLine⟩
  rcases Line.of_run_cons cleanLine with ⟨_, qand, hnil⟩
  cases hnil
  have pSlot := prefix_of_push (of_run_pushB256 qslot) hp
  obtain ⟨raw, pRaw, hRaw⟩ := prefix_of_sload qload pSlot
  have pZero := prefix_of_push (of_run_pushB256 qzero) pRaw
  have pNot := prefix_of_not qnot pZero
  have pShift := prefix_of_push (of_run_pushB256 qshift) pNot
  have pShr := prefix_of_shr qshr pShift
  have pAddress := prefix_of_and qand pShr
  have slotStor : Devm.getStor pre = Devm.getStor slotPost :=
    Ninst.Hinv.inv (f := Devm.getStor) qslot
  have hraw : raw = pre.getStorVal sevm.currentTarget slot := by
    rw [hRaw]
    change (Devm.getStor slotPost sevm.currentTarget).get slot =
      (Devm.getStor pre sevm.currentTarget).get slot
    rw [← congrFun slotStor sevm.currentTarget]
  refine ⟨by simpa [addressSlotReadWord, hraw,
      shr96_ones_eq_not_addressMask] using pAddress, ?_, ?_, ?_⟩
  · exact (Line.of_inv Devm.memory (by line_inv) run).symm
  · exact (Line.of_inv Devm.logs (by line_inv) run).symm
  · exact (Line.of_inv Devm.getStor (by line_inv) run).symm

/-- Exact packed-field update performed by `storeAddressWordAt`.

Only the current target's storage map is stated because that is the object the
SSTORE instruction updates.  Memory and logs are unchanged, and the consumed
address word is removed from the known stack prefix. -/
theorem of_storeAddressWordAt_val
    {sevm : Sevm} {pre post : Devm} {slot newAddress : B256}
    {tail : Stack}
    (hp : newAddress :: tail <<+ pre.stack)
    (run : Line.Run sevm pre (storeAddressWordAt slot) post) :
    tail <<+ post.stack ∧
      Devm.getStor post sevm.currentTarget =
        (Devm.getStor pre sevm.currentTarget).set slot
          (addressSlotWriteWord
            (pre.getStorVal sevm.currentTarget slot) newAddress) ∧
      post.memory = pre.memory ∧
      post.logs = pre.logs := by
  unfold storeAddressWordAt at run
  let prefixLine : Line :=
    [pushB256 slot, sload] ++ pushAddressMask ++
      [Ninst.and, Ninst.or, pushB256 slot]
  obtain ⟨storePre, prefixRun, storeLine⟩ :=
    of_run_append prefixLine run
  rcases Line.of_run_cons storeLine with ⟨_, qstore, hnil⟩
  cases hnil
  unfold prefixLine at prefixRun
  obtain ⟨loadPost, loadLine, rest⟩ :=
    of_run_append [pushB256 slot, sload] prefixRun
  rcases Line.of_run_cons loadLine with ⟨slotPost, qslot, loadLine⟩
  rcases Line.of_run_cons loadLine with ⟨_, qload, hnil⟩
  cases hnil
  obtain ⟨maskPost, maskLine, rest⟩ :=
    of_run_append pushAddressMask rest
  rcases Line.of_run_cons rest with ⟨andPost, qand, rest⟩
  rcases Line.of_run_cons rest with ⟨orPost, qor, rest⟩
  rcases Line.of_run_cons rest with ⟨_, qslotStore, hnil⟩
  cases hnil
  have pSlot := prefix_of_push (of_run_pushB256 qslot) hp
  obtain ⟨raw, pRaw, hRaw⟩ := prefix_of_sload qload pSlot
  have pMask := of_push_addressMask pRaw maskLine
  have pAnd := prefix_of_and qand pMask
  have pOr := prefix_of_or qor pAnd
  have pStore := prefix_of_push (of_run_pushB256 qslotStore) pOr
  have pFinal := prefix_of_sstore qstore pStore
  have hstore := sstore_getStor_set qstore pStore
  have hprefixStor : Devm.getStor pre = Devm.getStor storePre :=
    Line.of_inv Devm.getStor (by line_inv) prefixRun
  have slotStor : Devm.getStor pre = Devm.getStor slotPost :=
    Ninst.Hinv.inv (f := Devm.getStor) qslot
  have hraw : raw = pre.getStorVal sevm.currentTarget slot := by
    rw [hRaw]
    change (Devm.getStor slotPost sevm.currentTarget).get slot =
      (Devm.getStor pre sevm.currentTarget).get slot
    rw [← congrFun slotStor sevm.currentTarget]
  refine ⟨pFinal, ?_, ?_, ?_⟩
  · rw [hstore, ← congrFun hprefixStor sevm.currentTarget, hraw]
    rfl
  · exact (Line.of_inv Devm.memory (by line_inv) run).symm
  · exact (Line.of_inv Devm.logs (by line_inv) run).symm

end Blanc
