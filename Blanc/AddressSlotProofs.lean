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

/-- Exact value and frame effect of `loadAddressWordAt`. -/
theorem of_loadAddressWordAt_val
    {sevm : Sevm} {pre post : Devm} {slot : B256} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (run : Line.Run sevm pre (loadAddressWordAt slot) post) :
    ((~~~ addressMask) &&&
        pre.getStorVal sevm.currentTarget slot) :: tail <<+ post.stack ∧
      post.memory = pre.memory ∧
      post.logs = pre.logs ∧
      Devm.getStor post = Devm.getStor pre := by
  unfold loadAddressWordAt at run
  obtain ⟨loadPost, loadLine, cleanLine⟩ :=
    of_run_append [pushB256 slot, sload] run
  rcases Line.of_run_cons loadLine with ⟨slotPost, qslot, loadLine⟩
  rcases Line.of_run_cons loadLine with ⟨_, qload, hnil⟩
  cases hnil
  obtain ⟨maskPost, maskLine, cleanTail⟩ :=
    of_run_append pushAddressMask cleanLine
  rcases Line.of_run_cons cleanTail with ⟨notPost, qnot, cleanTail⟩
  rcases Line.of_run_cons cleanTail with ⟨_, qand, hnil⟩
  cases hnil
  have pSlot := prefix_of_push (of_run_pushB256 qslot) hp
  obtain ⟨raw, pRaw, hRaw⟩ := prefix_of_sload qload pSlot
  have pMask := of_push_addressMask pRaw maskLine
  have pNot := prefix_of_not qnot pMask
  have pAddress := prefix_of_and qand pNot
  have slotStor : Devm.getStor pre = Devm.getStor slotPost :=
    Ninst.Hinv.inv (f := Devm.getStor) qslot
  have hraw : raw = pre.getStorVal sevm.currentTarget slot := by
    rw [hRaw]
    change (Devm.getStor slotPost sevm.currentTarget).get slot =
      (Devm.getStor pre sevm.currentTarget).get slot
    rw [← congrFun slotStor sevm.currentTarget]
  refine ⟨by simpa [hraw] using pAddress, ?_, ?_, ?_⟩
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
          ((addressMask &&& pre.getStorVal sevm.currentTarget slot) |||
            newAddress) ∧
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
  · exact (Line.of_inv Devm.memory (by line_inv) run).symm
  · exact (Line.of_inv Devm.logs (by line_inv) run).symm

end Blanc
