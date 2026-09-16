import Blanc.CommonProofs

/-!
Contract-neutral gas erasure: equality of EVM states modulo `gasLeft`, and
per-instruction congruence of successful source runs over a gas-free whitelist.

`Devm.EqModGas` relates states that agree on every `Devm.Rels` column except
`gasLeft`. `Ninst.gasFree` whitelists the instructions whose successful effect
never reads `gasLeft`; `Ninst.run_eqModGas` replays two successful runs of a
whitelisted instruction against each other, and `Line.run_eqModGas` lifts that
to gas-free lines. The DRIP prefix transport (U3) consumes the line theorem.
-/

namespace Blanc

open Jaune

/-- Equality on every `Devm.Rels` column except `gasLeft`. -/
def Devm.EqModGas : Devm → Devm → Prop :=
  Devm.Rel { Devm.Rels.eq with gasLeft := fun _ _ => True }

theorem Devm.EqModGas.refl (a : Devm) : EqModGas a a := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Devm.Rels.eq]

theorem Devm.EqModGas.symm {a b : Devm} (h : EqModGas a b) : EqModGas b a := by
  rcases h with ⟨hs, hm, -, hl, hr, ho, had, hrd, he, haa, has, hst, hca, hts⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [Devm.Rels.eq]

theorem Devm.EqModGas.trans {a b c : Devm}
    (h1 : EqModGas a b) (h2 : EqModGas b c) : EqModGas a c := by
  rcases h1 with ⟨hs1, hm1, -, hl1, hr1, ho1, had1, hrd1, he1, haa1, has1, hst1, hca1, hts1⟩
  rcases h2 with ⟨hs2, hm2, -, hl2, hr2, ho2, had2, hrd2, he2, haa2, has2, hst2, hca2, hts2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [Devm.Rels.eq]

/-- Two `Burn` steps from agreeing states land on agreeing states. -/
theorem Devm.EqModGas.of_burn {a a' b b' : Devm}
    (h1 : Devm.Burn a a') (h2 : Devm.Burn b b') (h : EqModGas a b) :
    EqModGas a' b' := by
  rcases h1 with ⟨hs1, hm1, -, hl1, hr1, ho1, had1, hrd1, he1, haa1, has1, hst1, hca1, hts1⟩
  rcases h2 with ⟨hs2, hm2, -, hl2, hr2, ho2, had2, hrd2, he2, haa2, has2, hst2, hca2, hts2⟩
  rcases h with ⟨hs, hm, -, hl, hr, ho, had, hrd, he, haa, has, hst, hca, hts⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [Devm.Rels.eq]

/-- Two `Pop` steps from agreeing states pop equal words onto agreeing states. -/
theorem Devm.EqModGas.of_pop {a a₁ b b₁ : Devm} {x y : B256}
    (h1 : Devm.Pop [x] a a₁) (h2 : Devm.Pop [y] b b₁) (h : EqModGas a b) :
    x = y ∧ EqModGas a₁ b₁ := by
  rcases h1 with ⟨hs1, hm1, hg1, hl1, hr1, ho1, had1, hrd1, he1, haa1, has1, hst1, hca1, hts1⟩
  rcases h2 with ⟨hs2, hm2, hg2, hl2, hr2, ho2, had2, hrd2, he2, haa2, has2, hst2, hca2, hts2⟩
  rcases h with ⟨hs, hm, -, hl, hr, ho, had, hrd, he, haa, has, hst, hca, hts⟩
  simp only [Stack.Pop, Split, Devm.Rels.eq] at *
  have hcons : x :: a₁.stack = y :: b₁.stack := by
    simpa using hs1.symm.trans (hs.trans hs2)
  rcases List.cons_eq_cons.mp hcons with ⟨hxy, hstk⟩
  refine ⟨hxy, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [Devm.Rels.eq]

/-- Two `Push` steps of the same word from agreeing states land agreeing. -/
theorem Devm.EqModGas.of_push {a a₁ b b₁ : Devm} {x : B256}
    (h1 : Devm.Push [x] a a₁) (h2 : Devm.Push [x] b b₁) (h : EqModGas a b) :
    EqModGas a₁ b₁ := by
  rcases h1 with ⟨hs1, hm1, hg1, hl1, hr1, ho1, had1, hrd1, he1, haa1, has1, hst1, hca1, hts1⟩
  rcases h2 with ⟨hs2, hm2, hg2, hl2, hr2, ho2, had2, hrd2, he2, haa2, has2, hst2, hca2, hts2⟩
  rcases h with ⟨hs, hm, -, hl, hr, ho, had, hrd, he, haa, has, hst, hca, hts⟩
  simp only [Stack.Push, Split, Devm.Rels.eq] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [Devm.Rels.eq]

/-- Two `PopBurn` steps from agreeing states pop equal words onto agreeing states. -/
theorem Devm.EqModGas.of_popBurn {a a' b b' : Devm} {x y : B256}
    (h1 : Devm.PopBurn [x] a a') (h2 : Devm.PopBurn [y] b b') (h : EqModGas a b) :
    x = y ∧ EqModGas a' b' := by
  rcases h1 with ⟨hs1, hm1, -, hl1, hr1, ho1, had1, hrd1, he1, haa1, has1, hst1, hca1, hts1⟩
  rcases h2 with ⟨hs2, hm2, -, hl2, hr2, ho2, had2, hrd2, he2, haa2, has2, hst2, hca2, hts2⟩
  rcases h with ⟨hs, hm, -, hl, hr, ho, had, hrd, he, haa, has, hst, hca, hts⟩
  simp only [Stack.Pop, Split, Devm.Rels.eq] at *
  have hcons : x :: a'.stack = y :: b'.stack := by
    simpa using hs1.symm.trans (hs.trans hs2)
  rcases List.cons_eq_cons.mp hcons with ⟨hxy, hstk⟩
  refine ⟨hxy, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [Devm.Rels.eq]

/-- Two `PushBurn` steps of the same word from agreeing states land agreeing. -/
theorem Devm.EqModGas.of_pushBurn {a a' b b' : Devm} {x : B256}
    (h1 : Devm.PushBurn [x] a a') (h2 : Devm.PushBurn [x] b b') (h : EqModGas a b) :
    EqModGas a' b' := by
  rcases h1 with ⟨hs1, hm1, -, hl1, hr1, ho1, had1, hrd1, he1, haa1, has1, hst1, hca1, hts1⟩
  rcases h2 with ⟨hs2, hm2, -, hl2, hr2, ho2, had2, hrd2, he2, haa2, has2, hst2, hca2, hts2⟩
  rcases h with ⟨hs, hm, -, hl, hr, ho, had, hrd, he, haa, has, hst, hca, hts⟩
  simp only [Stack.Push, Split, Devm.Rels.eq] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [Devm.Rels.eq]

/-- `memWrite` of equal indices/values from agreeing states lands agreeing. -/
theorem Devm.EqModGas.of_memWrite {a b : Devm} {i : Nat} {v : Bytes}
    (h : EqModGas a b) : EqModGas (a.memWrite i v) (b.memWrite i v) := by
  rcases h with ⟨hs, hm, -, hl, hr, ho, had, hrd, he, haa, has, hst, hca, hts⟩
  simp only [Devm.Rels.eq] at *
  have hms : (a.memWrite i v).stack = a.stack := Devm.memWrite_stack _ _ _
  have hms' : (b.memWrite i v).stack = b.stack := Devm.memWrite_stack _ _ _
  have hmm : (a.memWrite i v).memory = a.memory.write i v := Devm.memWrite_memory _ _ _
  have hmm' : (b.memWrite i v).memory = b.memory.write i v := Devm.memWrite_memory _ _ _
  have hml : (a.memWrite i v).logs = a.logs := rfl
  have hml' : (b.memWrite i v).logs = b.logs := rfl
  have hmr : (a.memWrite i v).refundCounter = a.refundCounter := rfl
  have hmr' : (b.memWrite i v).refundCounter = b.refundCounter := rfl
  have hmo : (a.memWrite i v).output = a.output := rfl
  have hmo' : (b.memWrite i v).output = b.output := rfl
  have hmad : (a.memWrite i v).accountsToDelete = a.accountsToDelete := rfl
  have hmad' : (b.memWrite i v).accountsToDelete = b.accountsToDelete := rfl
  have hmrd : (a.memWrite i v).returnData = a.returnData := rfl
  have hmrd' : (b.memWrite i v).returnData = b.returnData := rfl
  have hme : (a.memWrite i v).error = a.error := rfl
  have hme' : (b.memWrite i v).error = b.error := rfl
  have hmaa : (a.memWrite i v).accessedAddresses = a.accessedAddresses := rfl
  have hmaa' : (b.memWrite i v).accessedAddresses = b.accessedAddresses := rfl
  have hmas : (a.memWrite i v).accessedStorageKeys = a.accessedStorageKeys := rfl
  have hmas' : (b.memWrite i v).accessedStorageKeys = b.accessedStorageKeys := rfl
  have hmst : (a.memWrite i v).state = a.state := rfl
  have hmst' : (b.memWrite i v).state = b.state := rfl
  have hmca : (a.memWrite i v).createdAccounts = a.createdAccounts := rfl
  have hmca' : (b.memWrite i v).createdAccounts = b.createdAccounts := rfl
  have hmts : (a.memWrite i v).transientStorage = a.transientStorage := rfl
  have hmts' : (b.memWrite i v).transientStorage = b.transientStorage := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [Devm.Rels.eq]

/-- `addAccessedStorageKey` from agreeing states lands agreeing. -/
theorem Devm.EqModGas.of_addAccessedStorageKey {a b : Devm} {t : Adr} {k : B256}
    (h : EqModGas a b) :
    EqModGas (addAccessedStorageKey a t k) (addAccessedStorageKey b t k) := by
  rcases h with ⟨hs, hm, -, hl, hr, ho, had, hrd, he, haa, has, hst, hca, hts⟩
  simp only [Devm.Rels.eq] at *
  have hak : (addAccessedStorageKey a t k).accessedStorageKeys =
      a.accessedStorageKeys.insert ⟨t, k⟩ := rfl
  have hak' : (addAccessedStorageKey b t k).accessedStorageKeys =
      b.accessedStorageKeys.insert ⟨t, k⟩ := rfl
  have hs0 : (addAccessedStorageKey a t k).stack = a.stack := rfl
  have hs0' : (addAccessedStorageKey b t k).stack = b.stack := rfl
  have hm0 : (addAccessedStorageKey a t k).memory = a.memory := rfl
  have hm0' : (addAccessedStorageKey b t k).memory = b.memory := rfl
  have hl0 : (addAccessedStorageKey a t k).logs = a.logs := rfl
  have hl0' : (addAccessedStorageKey b t k).logs = b.logs := rfl
  have hr0 : (addAccessedStorageKey a t k).refundCounter = a.refundCounter := rfl
  have hr0' : (addAccessedStorageKey b t k).refundCounter = b.refundCounter := rfl
  have ho0 : (addAccessedStorageKey a t k).output = a.output := rfl
  have ho0' : (addAccessedStorageKey b t k).output = b.output := rfl
  have had0 : (addAccessedStorageKey a t k).accountsToDelete = a.accountsToDelete := rfl
  have had0' : (addAccessedStorageKey b t k).accountsToDelete = b.accountsToDelete := rfl
  have hrd0 : (addAccessedStorageKey a t k).returnData = a.returnData := rfl
  have hrd0' : (addAccessedStorageKey b t k).returnData = b.returnData := rfl
  have he0 : (addAccessedStorageKey a t k).error = a.error := rfl
  have he0' : (addAccessedStorageKey b t k).error = b.error := rfl
  have haa0 : (addAccessedStorageKey a t k).accessedAddresses = a.accessedAddresses := rfl
  have haa0' : (addAccessedStorageKey b t k).accessedAddresses = b.accessedAddresses := rfl
  have hst0 : (addAccessedStorageKey a t k).state = a.state := rfl
  have hst0' : (addAccessedStorageKey b t k).state = b.state := rfl
  have hca0 : (addAccessedStorageKey a t k).createdAccounts = a.createdAccounts := rfl
  have hca0' : (addAccessedStorageKey b t k).createdAccounts = b.createdAccounts := rfl
  have hts0 : (addAccessedStorageKey a t k).transientStorage = a.transientStorage := rfl
  have hts0' : (addAccessedStorageKey b t k).transientStorage = b.transientStorage := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [Devm.Rels.eq]

/-- `withRefundCounter` of equal refunds from agreeing states lands agreeing. -/
theorem Devm.EqModGas.of_withRefundCounter {a b : Devm} {r : Int}
    (h : EqModGas a b) :
    EqModGas (a.withRefundCounter r) (b.withRefundCounter r) := by
  rcases h with ⟨hs, hm, -, hl, hr, ho, had, hrd, he, haa, has, hst, hca, hts⟩
  simp only [Devm.Rels.eq] at *
  have hr0 : (a.withRefundCounter r).refundCounter = r := rfl
  have hr0' : (b.withRefundCounter r).refundCounter = r := rfl
  have hs0 : (a.withRefundCounter r).stack = a.stack := rfl
  have hs0' : (b.withRefundCounter r).stack = b.stack := rfl
  have hm0 : (a.withRefundCounter r).memory = a.memory := rfl
  have hm0' : (b.withRefundCounter r).memory = b.memory := rfl
  have hl0 : (a.withRefundCounter r).logs = a.logs := rfl
  have hl0' : (b.withRefundCounter r).logs = b.logs := rfl
  have ho0 : (a.withRefundCounter r).output = a.output := rfl
  have ho0' : (b.withRefundCounter r).output = b.output := rfl
  have had0 : (a.withRefundCounter r).accountsToDelete = a.accountsToDelete := rfl
  have had0' : (b.withRefundCounter r).accountsToDelete = b.accountsToDelete := rfl
  have hrd0 : (a.withRefundCounter r).returnData = a.returnData := rfl
  have hrd0' : (b.withRefundCounter r).returnData = b.returnData := rfl
  have he0 : (a.withRefundCounter r).error = a.error := rfl
  have he0' : (b.withRefundCounter r).error = b.error := rfl
  have haa0 : (a.withRefundCounter r).accessedAddresses = a.accessedAddresses := rfl
  have haa0' : (b.withRefundCounter r).accessedAddresses = b.accessedAddresses := rfl
  have has0 : (a.withRefundCounter r).accessedStorageKeys = a.accessedStorageKeys := rfl
  have has0' : (b.withRefundCounter r).accessedStorageKeys = b.accessedStorageKeys := rfl
  have hst0 : (a.withRefundCounter r).state = a.state := rfl
  have hst0' : (b.withRefundCounter r).state = b.state := rfl
  have hca0 : (a.withRefundCounter r).createdAccounts = a.createdAccounts := rfl
  have hca0' : (b.withRefundCounter r).createdAccounts = b.createdAccounts := rfl
  have hts0 : (a.withRefundCounter r).transientStorage = a.transientStorage := rfl
  have hts0' : (b.withRefundCounter r).transientStorage = b.transientStorage := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [Devm.Rels.eq]

/-- `setStorVal` of equal args from agreeing states lands agreeing. -/
theorem Devm.EqModGas.of_setStorVal {a b : Devm} {t : Adr} {k v : B256}
    (h : EqModGas a b) :
    EqModGas (a.setStorVal t k v) (b.setStorVal t k v) := by
  rcases h with ⟨hs, hm, -, hl, hr, ho, had, hrd, he, haa, has, hst, hca, hts⟩
  simp only [Devm.Rels.eq] at *
  have hst0 : (a.setStorVal t k v).state = a.state.setStorVal t k v := rfl
  have hst0' : (b.setStorVal t k v).state = b.state.setStorVal t k v := rfl
  have hs0 : (a.setStorVal t k v).stack = a.stack := rfl
  have hs0' : (b.setStorVal t k v).stack = b.stack := rfl
  have hm0 : (a.setStorVal t k v).memory = a.memory := rfl
  have hm0' : (b.setStorVal t k v).memory = b.memory := rfl
  have hl0 : (a.setStorVal t k v).logs = a.logs := rfl
  have hl0' : (b.setStorVal t k v).logs = b.logs := rfl
  have hr0 : (a.setStorVal t k v).refundCounter = a.refundCounter := rfl
  have hr0' : (b.setStorVal t k v).refundCounter = b.refundCounter := rfl
  have ho0 : (a.setStorVal t k v).output = a.output := rfl
  have ho0' : (b.setStorVal t k v).output = b.output := rfl
  have had0 : (a.setStorVal t k v).accountsToDelete = a.accountsToDelete := rfl
  have had0' : (b.setStorVal t k v).accountsToDelete = b.accountsToDelete := rfl
  have hrd0 : (a.setStorVal t k v).returnData = a.returnData := rfl
  have hrd0' : (b.setStorVal t k v).returnData = b.returnData := rfl
  have he0 : (a.setStorVal t k v).error = a.error := rfl
  have he0' : (b.setStorVal t k v).error = b.error := rfl
  have haa0 : (a.setStorVal t k v).accessedAddresses = a.accessedAddresses := rfl
  have haa0' : (b.setStorVal t k v).accessedAddresses = b.accessedAddresses := rfl
  have has0 : (a.setStorVal t k v).accessedStorageKeys = a.accessedStorageKeys := rfl
  have has0' : (b.setStorVal t k v).accessedStorageKeys = b.accessedStorageKeys := rfl
  have hca0 : (a.setStorVal t k v).createdAccounts = a.createdAccounts := rfl
  have hca0' : (b.setStorVal t k v).createdAccounts = b.createdAccounts := rfl
  have hts0 : (a.setStorVal t k v).transientStorage = a.transientStorage := rfl
  have hts0' : (b.setStorVal t k v).transientStorage = b.transientStorage := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [Devm.Rels.eq]

/-- `withMemory` of equal memories from agreeing states lands agreeing. -/
theorem Devm.EqModGas.of_withMemory {a b : Devm} {m : Mem}
    (h : EqModGas a b) : EqModGas (a.withMemory m) (b.withMemory m) := by
  rcases h with ⟨hs, hm, -, hl, hr, ho, had, hrd, he, haa, has, hst, hca, hts⟩
  simp only [Devm.Rels.eq] at *
  have hm0 : (a.withMemory m).memory = m := rfl
  have hm0' : (b.withMemory m).memory = m := rfl
  have hs0 : (a.withMemory m).stack = a.stack := rfl
  have hs0' : (b.withMemory m).stack = b.stack := rfl
  have hl0 : (a.withMemory m).logs = a.logs := rfl
  have hl0' : (b.withMemory m).logs = b.logs := rfl
  have hr0 : (a.withMemory m).refundCounter = a.refundCounter := rfl
  have hr0' : (b.withMemory m).refundCounter = b.refundCounter := rfl
  have ho0 : (a.withMemory m).output = a.output := rfl
  have ho0' : (b.withMemory m).output = b.output := rfl
  have had0 : (a.withMemory m).accountsToDelete = a.accountsToDelete := rfl
  have had0' : (b.withMemory m).accountsToDelete = b.accountsToDelete := rfl
  have hrd0 : (a.withMemory m).returnData = a.returnData := rfl
  have hrd0' : (b.withMemory m).returnData = b.returnData := rfl
  have he0 : (a.withMemory m).error = a.error := rfl
  have he0' : (b.withMemory m).error = b.error := rfl
  have haa0 : (a.withMemory m).accessedAddresses = a.accessedAddresses := rfl
  have haa0' : (b.withMemory m).accessedAddresses = b.accessedAddresses := rfl
  have has0 : (a.withMemory m).accessedStorageKeys = a.accessedStorageKeys := rfl
  have has0' : (b.withMemory m).accessedStorageKeys = b.accessedStorageKeys := rfl
  have hst0 : (a.withMemory m).state = a.state := rfl
  have hst0' : (b.withMemory m).state = b.state := rfl
  have hca0 : (a.withMemory m).createdAccounts = a.createdAccounts := rfl
  have hca0' : (b.withMemory m).createdAccounts = b.createdAccounts := rfl
  have hts0 : (a.withMemory m).transientStorage = a.transientStorage := rfl
  have hts0' : (b.withMemory m).transientStorage = b.transientStorage := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [Devm.Rels.eq]

/-- `withStack` of equal stacks from agreeing states lands agreeing. -/
theorem Devm.EqModGas.of_withStack {a b : Devm} {s : Stack}
    (h : EqModGas a b) : EqModGas (a.withStack s) (b.withStack s) := by
  rcases h with ⟨hs, hm, -, hl, hr, ho, had, hrd, he, haa, has, hst, hca, hts⟩
  simp only [Devm.Rels.eq] at *
  have hs0 : (a.withStack s).stack = s := rfl
  have hs0' : (b.withStack s).stack = s := rfl
  have hm0 : (a.withStack s).memory = a.memory := rfl
  have hm0' : (b.withStack s).memory = b.memory := rfl
  have hl0 : (a.withStack s).logs = a.logs := rfl
  have hl0' : (b.withStack s).logs = b.logs := rfl
  have hr0 : (a.withStack s).refundCounter = a.refundCounter := rfl
  have hr0' : (b.withStack s).refundCounter = b.refundCounter := rfl
  have ho0 : (a.withStack s).output = a.output := rfl
  have ho0' : (b.withStack s).output = b.output := rfl
  have had0 : (a.withStack s).accountsToDelete = a.accountsToDelete := rfl
  have had0' : (b.withStack s).accountsToDelete = b.accountsToDelete := rfl
  have hrd0 : (a.withStack s).returnData = a.returnData := rfl
  have hrd0' : (b.withStack s).returnData = b.returnData := rfl
  have he0 : (a.withStack s).error = a.error := rfl
  have he0' : (b.withStack s).error = b.error := rfl
  have haa0 : (a.withStack s).accessedAddresses = a.accessedAddresses := rfl
  have haa0' : (b.withStack s).accessedAddresses = b.accessedAddresses := rfl
  have has0 : (a.withStack s).accessedStorageKeys = a.accessedStorageKeys := rfl
  have has0' : (b.withStack s).accessedStorageKeys = b.accessedStorageKeys := rfl
  have hst0 : (a.withStack s).state = a.state := rfl
  have hst0' : (b.withStack s).state = b.state := rfl
  have hca0 : (a.withStack s).createdAccounts = a.createdAccounts := rfl
  have hca0' : (b.withStack s).createdAccounts = b.createdAccounts := rfl
  have hts0 : (a.withStack s).transientStorage = a.transientStorage := rfl
  have hts0' : (b.withStack s).transientStorage = b.transientStorage := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [Devm.Rels.eq]

/-- Memory expansion cost agrees on agreeing states. -/
theorem Devm.EqModGas.extCost_congr {a b : Devm} {l : List (Nat × Nat)}
    (h : EqModGas a b) : a.extCost l = b.extCost l := by
  have hm : a.memory = b.memory := by
    rcases h with ⟨_, hm, _, _, _, _, _, _, _, _, _, _, _, _⟩
    simpa [Devm.Rels.eq] using hm
  unfold Devm.extCost
  rw [hm]

/-- Storage reads agree on agreeing states. -/
theorem Devm.EqModGas.getStorVal_congr {a b : Devm} {t : Adr} {k : B256}
    (h : EqModGas a b) : a.getStorVal t k = b.getStorVal t k := by
  have hst : a.state = b.state := by
    rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hst, _, _⟩
    simpa [Devm.Rels.eq] using hst
  unfold Devm.getStorVal Devm.getAcct
  rw [hst]

/-- Memory reads agree on agreeing states, in value and in residual state. -/
theorem Devm.EqModGas.memRead_congr {a b : Devm} {i n : Nat}
    (h : EqModGas a b) :
    (a.memRead i n).1 = (b.memRead i n).1 ∧
      EqModGas (a.memRead i n).2 (b.memRead i n).2 := by
  have hm : a.memory = b.memory := by
    rcases h with ⟨_, hm, _, _, _, _, _, _, _, _, _, _, _, _⟩
    simpa [Devm.Rels.eq] using hm
  have hread : a.memory.read i n = b.memory.read i n := by rw [hm]
  simp only [Devm.memRead, hread]
  refine ⟨trivial, ?_⟩
  exact Devm.EqModGas.of_withMemory h

/-- Two `popToNat` steps from agreeing states pop equal indices onto agreeing states. -/
theorem Devm.EqModGas.of_popToNat {a a₁ b b₁ : Devm} {i j : Nat}
    (h1 : a.popToNat = .ok (i, a₁)) (h2 : b.popToNat = .ok (j, b₁))
    (h : EqModGas a b) : i = j ∧ EqModGas a₁ b₁ := by
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, hpop1, hii1⟩
  rcases Devm.pop_of_popToNat_val h2 with ⟨y, hpop2, hii2⟩
  obtain ⟨hxy, hag⟩ := Devm.EqModGas.of_pop hpop1 hpop2 h
  exact ⟨by rw [hii1, hii2, hxy], hag⟩

/-- Congruence for any binary stack op: pops, charge, and push all preserve agreement. -/
private theorem applyBinary_eqModGas {f : B256 → B256 → B256} {c : Nat}
    {a a' b b' : Devm}
    (h1 : applyBinary f c a = .ok a') (h2 : applyBinary f c b = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [applyBinary_def] at h1 h2
  rcases Except.bind_eq_ok h1 with ⟨⟨x1, a1⟩, hp1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨⟨x2, b1⟩, hp2, h2⟩
  rcases Except.bind_eq_ok h1 with ⟨⟨y1, a2⟩, hq1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨⟨y2, b2⟩, hq2, h2⟩
  obtain ⟨hxx, hag1⟩ := h.of_pop (Devm.pop_of_pop hp1) (Devm.pop_of_pop hp2)
  obtain ⟨hyy, hag2⟩ := hag1.of_pop (Devm.pop_of_pop hq1) (Devm.pop_of_pop hq2)
  simp only [pushItem_def] at h1 h2
  rcases Except.bind_eq_ok h1 with ⟨c1, hc1, hpush1⟩
  rcases Except.bind_eq_ok h2 with ⟨c2, hc2, hpush2⟩
  have hag3 := hag2.of_burn (Devm.burn_of_chargeGas hc1) (Devm.burn_of_chargeGas hc2)
  have hword : f x1 y1 = f x2 y2 := by rw [hxx, hyy]
  rw [hword] at hpush1
  exact hag3.of_push (Devm.push_of_push hpush1) (Devm.push_of_push hpush2)

/-- Congruence for any unary stack op. -/
private theorem applyUnary_eqModGas {f : B256 → B256} {c : Nat}
    {a a' b b' : Devm}
    (h1 : applyUnary f c a = .ok a') (h2 : applyUnary f c b = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [applyUnary_def] at h1 h2
  rcases Except.bind_eq_ok h1 with ⟨⟨x1, a1⟩, hp1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨⟨x2, b1⟩, hp2, h2⟩
  obtain ⟨hxx, hag1⟩ := h.of_pop (Devm.pop_of_pop hp1) (Devm.pop_of_pop hp2)
  simp only [pushItem_def] at h1 h2
  rcases Except.bind_eq_ok h1 with ⟨c1, hc1, hpush1⟩
  rcases Except.bind_eq_ok h2 with ⟨c2, hc2, hpush2⟩
  have hag2 := hag1.of_burn (Devm.burn_of_chargeGas hc1) (Devm.burn_of_chargeGas hc2)
  have hword : f x1 = f x2 := by rw [hxx]
  rw [hword] at hpush1
  exact hag2.of_push (Devm.push_of_push hpush1) (Devm.push_of_push hpush2)

/-- Congruence for a pushed immediate word: charge and push preserve agreement. -/
private theorem pushItem_eqModGas {x : B256} {c : Nat} {a a' b b' : Devm}
    (h1 : pushItem x c a = .ok a') (h2 : pushItem x c b = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' :=
  h.of_pushBurn (Devm.pushBurn_of_pushItem h1) (Devm.pushBurn_of_pushItem h2)

/-- Regular instructions whose successful effect never reads `gasLeft`: the
`regularTransfer` opcode list minus `gas`. Never `pc`, never `gas`. -/
def Rinst.gasFree : Rinst → Bool
  | .add | .mul | .sub | .div | .lt | .gt | .eq | .iszero | .and | .shr
  | .caller | .callvalue | .calldataload | .calldatasize | .timestamp
  | .pop | .mload | .mstore | .sload | .sstore | .dup _ | .swap _ => true
  | _ => false

/-- Instructions whose successful effect never reads `gasLeft`: the gas-free
regular instructions plus `push`. Never an `Xinst`, never `pc`. -/
def Ninst.gasFree : Ninst → Bool
  | .reg r => Rinst.gasFree r
  | .push _ _ => true
  | .exec _ => false

/-- A line is gas-free when every instruction is. -/
def Line.gasFree : Line → Bool
  | [] => true
  | i :: l => Ninst.gasFree i && Line.gasFree l

private theorem run_add {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ .add = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ .add = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  exact applyBinary_eqModGas h1 h2 h

private theorem run_mul {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ .mul = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ .mul = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  exact applyBinary_eqModGas h1 h2 h

private theorem run_sub {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ .sub = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ .sub = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  exact applyBinary_eqModGas h1 h2 h

private theorem run_div {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ .div = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ .div = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  exact applyBinary_eqModGas h1 h2 h

private theorem run_lt {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ .lt = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ .lt = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  exact applyBinary_eqModGas h1 h2 h

private theorem run_gt {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ .gt = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ .gt = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  exact applyBinary_eqModGas h1 h2 h

private theorem run_eq {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ .eq = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ .eq = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  exact applyBinary_eqModGas h1 h2 h

private theorem run_iszero {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ .iszero = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ .iszero = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  exact applyUnary_eqModGas h1 h2 h

private theorem run_and {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ .and = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ .and = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  exact applyBinary_eqModGas h1 h2 h

private theorem run_shr {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ .shr = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ .shr = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  exact applyBinary_eqModGas h1 h2 h

private theorem run_caller {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ .caller = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ .caller = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  exact pushItem_eqModGas h1 h2 h

private theorem run_callvalue {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ .callvalue = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ .callvalue = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  exact pushItem_eqModGas h1 h2 h

private theorem run_calldatasize {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ .calldatasize = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ .calldatasize = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  exact pushItem_eqModGas h1 h2 h

private theorem run_timestamp {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ .timestamp = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ .timestamp = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  exact pushItem_eqModGas h1 h2 h

/-- A successful `pop` run is a `PopBurn` step. -/
private theorem popBurn_of_run_pop {e : Sevm} {a a' : Devm} {pc : Nat}
    (h : Rinst.run ⟨pc, e, a⟩ .pop = .ok a') : ∃ x, Devm.PopBurn [x] a a' := by
  simp only [Rinst.run, Rinst.runCore] at h
  rcases Except.bind_eq_ok h with ⟨a1, hmap, hburn⟩
  simp only [Functor.mapRev, Functor.map, Except.map] at hmap
  rcases hp : Devm.pop a with _ | ⟨x, a2⟩ <;> simp [hp] at hmap
  subst hmap
  exact ⟨x, Devm.popBurn_of_pop_of_burn (Devm.pop_of_pop hp)
    (Devm.burn_of_chargeGas hburn)⟩

private theorem run_pop {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ .pop = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ .pop = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  rcases popBurn_of_run_pop h1 with ⟨x1, hpb1⟩
  rcases popBurn_of_run_pop h2 with ⟨x2, hpb2⟩
  exact (h.of_popBurn hpb1 hpb2).2

private theorem run_calldataload {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ .calldataload = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ .calldataload = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  rcases Except.bind_eq_ok h1 with ⟨⟨x1, a1⟩, hp1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨⟨x2, b1⟩, hp2, h2⟩
  rcases Except.bind_eq_ok h1 with ⟨c1, hc1, hpush1⟩
  rcases Except.bind_eq_ok h2 with ⟨c2, hc2, hpush2⟩
  obtain ⟨hxx, hag1⟩ := h.of_pop (Devm.pop_of_pop hp1) (Devm.pop_of_pop hp2)
  have hagc := hag1.of_burn (Devm.burn_of_chargeGas hc1) (Devm.burn_of_chargeGas hc2)
  have hword : Bytes.toB256 (e.data.sliceD x1.toNat 32 0) =
      Bytes.toB256 (e.data.sliceD x2.toNat 32 0) := by rw [hxx]
  rw [hword] at hpush1
  exact hagc.of_push (Devm.push_of_push hpush1) (Devm.push_of_push hpush2)

private theorem run_mload {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ .mload = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ .mload = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  rcases Except.bind_eq_ok h1 with ⟨⟨i1, a1⟩, hp1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨⟨i2, b1⟩, hp2, h2⟩
  rcases Except.bind_eq_ok h1 with ⟨a3, hc1, hpush1⟩
  rcases Except.bind_eq_ok h2 with ⟨b3, hc2, hpush2⟩
  obtain ⟨hii, hag1⟩ := Devm.EqModGas.of_popToNat hp1 hp2 h
  have hec := hag1.extCost_congr (l := [(i2, 32)])
  have hcost : gVerylow + a1.extCost [(i1, 32)] =
      gVerylow + b1.extCost [(i2, 32)] := by rw [hii, hec]
  rw [hcost] at hc1
  have hag3 := hag1.of_burn (Devm.burn_of_chargeGas hc1) (Devm.burn_of_chargeGas hc2)
  have hval : (a3.memRead i1 32).1 = (b3.memRead i2 32).1 := by
    rw [← hii]; exact (hag3.memRead_congr).1
  have hagm : Devm.EqModGas (a3.memRead i1 32).2 (b3.memRead i2 32).2 := by
    rw [← hii]; exact (hag3.memRead_congr).2
  generalize ha3m : a3.memRead i1 32 = m1 at hpush1 hval hagm
  generalize hb3m : b3.memRead i2 32 = m2 at hpush2 hval hagm
  rcases m1 with ⟨v1, d1⟩
  rcases m2 with ⟨v2, d2⟩
  dsimp only at hpush1 hpush2 hval hagm
  rw [hval] at hpush1
  exact hagm.of_push (Devm.push_of_push hpush1) (Devm.push_of_push hpush2)

private theorem run_mstore {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ .mstore = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ .mstore = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  rcases Except.bind_eq_ok h1 with ⟨⟨i1, a1⟩, hp1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨⟨i2, b1⟩, hp2, h2⟩
  rcases Except.bind_eq_ok h1 with ⟨⟨v1, a2⟩, hq1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨⟨v2, b2⟩, hq2, h2⟩
  rcases Except.bind_eq_ok h1 with ⟨a3, hc1, hmem1⟩
  rcases Except.bind_eq_ok h2 with ⟨b3, hc2, hmem2⟩
  obtain ⟨hii, hag1⟩ := Devm.EqModGas.of_popToNat hp1 hp2 h
  obtain ⟨hvv, hag2⟩ := hag1.of_pop (Devm.pop_of_pop hq1) (Devm.pop_of_pop hq2)
  have hec := hag2.extCost_congr (l := [(i2, 32)])
  have hcost : gVerylow + a2.extCost [(i1, 32)] =
      gVerylow + b2.extCost [(i2, 32)] := by rw [hii, hec]
  rw [hcost] at hc1
  have hag3 := hag2.of_burn (Devm.burn_of_chargeGas hc1) (Devm.burn_of_chargeGas hc2)
  injection hmem1 with hmem1
  injection hmem2 with hmem2
  rw [← hmem1, ← hmem2, hii, hvv]
  exact hag3.of_memWrite

private theorem run_sload {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ .sload = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ .sload = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  rcases Except.bind_eq_ok h1 with ⟨⟨k1, a1⟩, hp1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨⟨k2, b1⟩, hp2, h2⟩
  rcases Except.bind_eq_ok h1 with ⟨m1, hif1, hpush1⟩
  rcases Except.bind_eq_ok h2 with ⟨m2, hif2, hpush2⟩
  obtain ⟨hkey, hag1⟩ := h.of_pop (Devm.pop_of_pop hp1) (Devm.pop_of_pop hp2)
  have hasa1 : a1.accessedStorageKeys = b1.accessedStorageKeys := by
    rcases hag1 with ⟨_, _, _, _, _, _, _, _, _, _, has, _, _, _⟩
    simpa [Devm.Rels.eq] using has
  have hcond : (⟨e.currentTarget, k1⟩ ∈ a1.accessedStorageKeys) ↔
      (⟨e.currentTarget, k2⟩ ∈ b1.accessedStorageKeys) := by
    rw [hkey, hasa1]
  have hag2 : Devm.EqModGas m1 m2 := by
    by_cases hwarm : ⟨e.currentTarget, k1⟩ ∈ a1.accessedStorageKeys
    · have hwarm2 := hcond.mp hwarm
      rw [if_pos hwarm] at hif1
      rw [if_pos hwarm2] at hif2
      exact hag1.of_burn (Devm.burn_of_chargeGas hif1) (Devm.burn_of_chargeGas hif2)
    · have hcold2 : ¬ ⟨e.currentTarget, k2⟩ ∈ b1.accessedStorageKeys :=
        fun hc => hwarm (hcond.mpr hc)
      rw [if_neg hwarm] at hif1
      rw [if_neg hcold2] at hif2
      rw [← hkey] at hif2
      have hag1' := hag1.of_addAccessedStorageKey
      exact hag1'.of_burn (Devm.burn_of_chargeGas hif1) (Devm.burn_of_chargeGas hif2)
  have hword : m1.getStorVal e.currentTarget k1 =
      m2.getStorVal e.currentTarget k2 := by
    rw [hkey]; exact hag2.getStorVal_congr
  rw [hword] at hpush1
  exact hag2.of_push (Devm.push_of_push hpush1) (Devm.push_of_push hpush2)

private theorem run_sstore {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ .sstore = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ .sstore = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  rcases Except.bind_eq_ok h1 with ⟨⟨k1, a1⟩, hp1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨⟨k2, b1⟩, hp2, h2⟩
  rcases Except.bind_eq_ok h1 with ⟨⟨n1, a2⟩, hq1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨⟨n2, b2⟩, hq2, h2⟩
  rcases Except.bind_eq_ok h1 with ⟨_, _, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨_, _, h2⟩
  rcases Except.bind_eq_ok h1 with ⟨⟨a3, g21⟩, hacc1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨⟨b3, g22⟩, hacc2, h2⟩
  rcases Except.bind_eq_ok h1 with ⟨g31, hg1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨g32, hg2, h2⟩
  rcases Except.bind_eq_ok h1 with ⟨a4, hr1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨b4, hr2, h2⟩
  rcases Except.bind_eq_ok h1 with ⟨a5, hc1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨b5, hc2, h2⟩
  rcases Except.bind_eq_ok h1 with ⟨_, _, hset1⟩
  rcases Except.bind_eq_ok h2 with ⟨_, _, hset2⟩
  obtain ⟨hkey, hag1⟩ := h.of_pop (Devm.pop_of_pop hp1) (Devm.pop_of_pop hp2)
  obtain ⟨hnew, hag2⟩ := hag1.of_pop (Devm.pop_of_pop hq1) (Devm.pop_of_pop hq2)
  have hasa2 : a2.accessedStorageKeys = b2.accessedStorageKeys := by
    rcases hag2 with ⟨_, _, _, _, _, _, _, _, _, _, has, _, _, _⟩
    simpa [Devm.Rels.eq] using has
  have hsta2 : a2.state = b2.state := by
    rcases hag2 with ⟨_, _, _, _, _, _, _, _, _, _, _, hst, _, _⟩
    simpa [Devm.Rels.eq] using hst
  injection hacc1 with hacc1
  injection hacc2 with hacc2
  have hcond : (⟨e.currentTarget, k2⟩ ∉ b2.accessedStorageKeys) ↔
      (⟨e.currentTarget, k1⟩ ∉ a2.accessedStorageKeys) := by
    rw [← hkey, ← hasa2]
  obtain ⟨hag3, hg2eq⟩ : Devm.EqModGas a3 b3 ∧ g21 = g22 := by
    by_cases hcold : ⟨e.currentTarget, k1⟩ ∉ a2.accessedStorageKeys
    · have hcold2 : ⟨e.currentTarget, k2⟩ ∉ b2.accessedStorageKeys := hcond.mpr hcold
      rw [if_pos hcold] at hacc1
      rw [if_pos hcold2] at hacc2
      simp only [Prod.mk.injEq] at hacc1 hacc2
      rcases hacc1 with ⟨ha3, hg21⟩
      rcases hacc2 with ⟨hb3, hg22⟩
      rw [← hkey] at hb3
      refine ⟨?_, by rw [← hg21, ← hg22]⟩
      rw [← ha3, ← hb3]
      exact hag2.of_addAccessedStorageKey
    · have hwarm2 : ¬ ⟨e.currentTarget, k2⟩ ∉ b2.accessedStorageKeys :=
        fun hc => hcold (hcond.mp hc)
      rw [if_neg hcold] at hacc1
      rw [if_neg hwarm2] at hacc2
      simp only [Prod.mk.injEq] at hacc1 hacc2
      rcases hacc1 with ⟨ha3, hg21⟩
      rcases hacc2 with ⟨hb3, hg22⟩
      refine ⟨?_, by rw [← hg21, ← hg22]⟩
      rw [← ha3, ← hb3]
      exact hag2
  have horig : getOrigStorVal e e.currentTarget k1 =
      getOrigStorVal e e.currentTarget k2 := by rw [hkey]
  have hcurr : a2.getStorVal e.currentTarget k1 =
      b2.getStorVal e.currentTarget k2 := by
    unfold Devm.getStorVal Devm.getAcct
    rw [hkey, hsta2]
  injection hg1 with hg1
  injection hg2 with hg2
  have hg3eq : g31 = g32 := by
    rw [← hg1, ← hg2, horig, hcurr, hnew, hg2eq]
  have hrc : a3.refundCounter = b3.refundCounter := by
    rcases hag3 with ⟨_, _, _, _, hrc, _, _, _, _, _, _, _, _, _⟩
    simpa [Devm.Rels.eq] using hrc
  have hrf : sstoreNewRefundCounter n1 (getOrigStorVal e e.currentTarget k1)
        (a2.getStorVal e.currentTarget k1) a3.refundCounter =
        sstoreNewRefundCounter n2 (getOrigStorVal e e.currentTarget k2)
        (b2.getStorVal e.currentTarget k2) b3.refundCounter := by
    rw [hnew, horig, hcurr, hrc]
  injection hr1 with hr1
  injection hr2 with hr2
  rw [hrf] at hr1
  have hag4 : Devm.EqModGas a4 b4 := by
    rw [← hr1, ← hr2]
    exact hag3.of_withRefundCounter
  rw [hg3eq] at hc1
  have hag5 := hag4.of_burn (Devm.burn_of_chargeGas hc1)
    (Devm.burn_of_chargeGas hc2)
  injection hset1 with hset1
  injection hset2 with hset2
  rw [← hset1, ← hset2, hkey, hnew]
  exact hag5.of_setStorVal

private theorem run_dup {n : Fin 16} {e : Sevm} {a a' b b' : Devm}
    {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ (.dup n) = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ (.dup n) = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  rcases Except.bind_eq_ok h1 with ⟨c1, hc1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨c2, hc2, h2⟩
  have hagc := h.of_burn (Devm.burn_of_chargeGas hc1) (Devm.burn_of_chargeGas hc2)
  split at h1
  · cases h1
  · rename_i w1 hw1
    split at h2
    · cases h2
    · rename_i w2 hw2
      have hst : c1.stack = c2.stack := by
        rcases hagc with ⟨hst, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
        simpa [Devm.Rels.eq] using hst
      have hw : w1 = w2 := by
        rw [hst] at hw1
        exact Option.some.inj (hw1.symm.trans hw2)
      rw [hw] at h1
      exact hagc.of_push (Devm.push_of_push h1) (Devm.push_of_push h2)

private theorem run_swap {n : Fin 16} {e : Sevm} {a a' b b' : Devm}
    {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ (.swap n) = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ (.swap n) = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  rcases Except.bind_eq_ok h1 with ⟨c1, hc1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨c2, hc2, h2⟩
  have hagc := h.of_burn (Devm.burn_of_chargeGas hc1) (Devm.burn_of_chargeGas hc2)
  split at h1
  · cases h1
  · rename_i s1 hsw1
    split at h2
    · cases h2
    · rename_i s2 hsw2
      have hst : c1.stack = c2.stack := by
        rcases hagc with ⟨hst, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
        simpa [Devm.Rels.eq] using hst
      have hs12 : s1 = s2 := by
        rw [hst] at hsw1
        exact Option.some.inj (hsw1.symm.trans hsw2)
      injection h1 with h1
      injection h2 with h2
      rw [← h1, ← h2, hs12]
      exact hagc.of_withStack

/-- Per-op congruence: two successful runs of a gas-free regular instruction
from agreeing states land on agreeing states. -/
theorem Rinst.run_eqModGas {e : Sevm} {a a' b b' : Devm} {r : Rinst}
    {pc1 pc2 : Nat}
    (hfree : Rinst.gasFree r = true)
    (h1 : Rinst.run ⟨pc1, e, a⟩ r = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ r = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  cases r <;> simp [Rinst.gasFree] at hfree <;> first
    | exact run_add h1 h2 h
    | exact run_mul h1 h2 h
    | exact run_sub h1 h2 h
    | exact run_div h1 h2 h
    | exact run_lt h1 h2 h
    | exact run_gt h1 h2 h
    | exact run_eq h1 h2 h
    | exact run_iszero h1 h2 h
    | exact run_and h1 h2 h
    | exact run_shr h1 h2 h
    | exact run_caller h1 h2 h
    | exact run_callvalue h1 h2 h
    | exact run_calldataload h1 h2 h
    | exact run_calldatasize h1 h2 h
    | exact run_timestamp h1 h2 h
    | exact run_pop h1 h2 h
    | exact run_mload h1 h2 h
    | exact run_mstore h1 h2 h
    | exact run_sload h1 h2 h
    | exact run_sstore h1 h2 h
    | exact run_dup h1 h2 h
    | exact run_swap h1 h2 h

/-- Two successful runs of a gas-free instruction from agreeing states land on
agreeing states.

Caveat (design R6): this identity is modulo exactly the columns outside
`Devm.Rels` as pinned. A Jaune pin bump that adds `stateGas`/`accountReads`/
`storageReads` (or any other column) outside `Devm.Rels` would silently widen
this transport to be modulo those columns too. Revisit `Devm.Rels` and this
whitelist at any such bump. -/
theorem Ninst.run_eqModGas {e : Sevm} {a a' b b' : Devm} {i : Ninst}
    (hfree : Ninst.gasFree i = true)
    (h1 : Ninst.Run e a i a') (h2 : Ninst.Run e b i b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  cases i with
  | reg r =>
    simp only [Ninst.gasFree] at hfree
    rcases of_run_reg h1 with ⟨pc1, run1⟩
    rcases of_run_reg h2 with ⟨pc2, run2⟩
    exact Rinst.run_eqModGas hfree run1 run2 h
  | push xs le =>
    exact h.of_pushBurn (of_run_push h1) (of_run_push h2)
  | exec x =>
    simp [Ninst.gasFree] at hfree

/-- Two successful runs of a gas-free line from agreeing states land on
agreeing states. -/
theorem Line.run_eqModGas {e : Sevm} {a a' b b' : Devm} {l : Line}
    (hfree : Line.gasFree l = true)
    (h1 : Line.Run e a l a') (h2 : Line.Run e b l b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  revert b b' h2 h hfree
  induction h1 with
  | nil =>
    intro b b' h2 h _
    cases h2
    exact h
  | cons hstep htail ih =>
    intro b b' h2 h hfree
    cases h2 with
    | cons hstep2 htail2 =>
      simp only [Line.gasFree, Bool.and_eq_true] at hfree
      rcases hfree with ⟨hfi, hfl⟩
      exact ih htail2 (Ninst.run_eqModGas hfi hstep hstep2 h) hfl

end Blanc
