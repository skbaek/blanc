import Blanc.CommonProofs

/-!
R1 scratch probe (TEMPORARY — never committed, deleted before the B1 seal):
`EqModGas` congruence for `add`, `mstore`, `sstore` only.
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

/-- R1 probe, op 1: `add` congruence. -/
theorem probe_add {e : Sevm} {a a' b b' : Devm}
    (h1 : Ninst.Run e a (Ninst.reg .add) a')
    (h2 : Ninst.Run e b (Ninst.reg .add) b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  rcases of_run_reg h1 with ⟨pc1, run1⟩
  rcases of_run_reg h2 with ⟨pc2, run2⟩
  simp only [Rinst.run, Rinst.runCore, applyBinary_def] at run1 run2
  rcases Except.bind_eq_ok run1 with ⟨⟨x1, a1⟩, hp1, run1⟩
  rcases Except.bind_eq_ok run2 with ⟨⟨x2, b1⟩, hp2, run2⟩
  rcases Except.bind_eq_ok run1 with ⟨⟨y1, a2⟩, hq1, run1⟩
  rcases Except.bind_eq_ok run2 with ⟨⟨y2, b2⟩, hq2, run2⟩
  obtain ⟨hxx, hag1⟩ := Devm.EqModGas.of_pop (Devm.pop_of_pop hp1) (Devm.pop_of_pop hp2) h
  obtain ⟨hyy, hag2⟩ := Devm.EqModGas.of_pop (Devm.pop_of_pop hq1) (Devm.pop_of_pop hq2) hag1
  rw [pushItem_def] at run1 run2
  rcases Except.bind_eq_ok run1 with ⟨c1, hc1, hpush1⟩
  rcases Except.bind_eq_ok run2 with ⟨c2, hc2, hpush2⟩
  have hag3 := Devm.EqModGas.of_burn (Devm.burn_of_chargeGas hc1) (Devm.burn_of_chargeGas hc2) hag2
  have hword : x1 + y1 = x2 + y2 := by rw [hxx, hyy]
  rw [hword] at hpush1
  exact Devm.EqModGas.of_push (Devm.push_of_push hpush1) (Devm.push_of_push hpush2) hag3

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

/-- R1 probe, op 2: `mstore` congruence. -/
theorem probe_mstore {e : Sevm} {a a' b b' : Devm}
    (h1 : Ninst.Run e a (Ninst.reg .mstore) a')
    (h2 : Ninst.Run e b (Ninst.reg .mstore) b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  rcases of_run_reg h1 with ⟨pc1, run1⟩
  rcases of_run_reg h2 with ⟨pc2, run2⟩
  simp only [Rinst.run, Rinst.runCore] at run1 run2
  rcases Except.bind_eq_ok run1 with ⟨⟨i1, a1⟩, hp1, run1⟩
  rcases Except.bind_eq_ok run2 with ⟨⟨i2, b1⟩, hp2, run2⟩
  rcases Except.bind_eq_ok run1 with ⟨⟨v1, a2⟩, hq1, run1⟩
  rcases Except.bind_eq_ok run2 with ⟨⟨v2, b2⟩, hq2, run2⟩
  rcases Except.bind_eq_ok run1 with ⟨a3, hc1, hmem1⟩
  rcases Except.bind_eq_ok run2 with ⟨b3, hc2, hmem2⟩
  rcases Devm.pop_of_popToNat_val hp1 with ⟨x1, hpop1, hii1⟩
  rcases Devm.pop_of_popToNat_val hp2 with ⟨x2, hpop2, hii2⟩
  obtain ⟨hxx, hag1⟩ := Devm.EqModGas.of_pop hpop1 hpop2 h
  obtain ⟨hvv, hag2⟩ := Devm.EqModGas.of_pop (Devm.pop_of_pop hq1) (Devm.pop_of_pop hq2) hag1
  have hii : i1 = i2 := by rw [hii1, hii2, hxx]
  have hcost : gVerylow + a2.extCost [(i1, 32)] = gVerylow + b2.extCost [(i2, 32)] := by
    unfold Devm.extCost
    rcases hag2 with ⟨hsa, hma, -, -, -, -, -, -, -, -, -, -, -, -⟩
    simp only [Devm.Rels.eq] at hma
    rw [hii, hma]
  rw [hcost] at hc1
  have hag3 := Devm.EqModGas.of_burn (Devm.burn_of_chargeGas hc1) (Devm.burn_of_chargeGas hc2) hag2
  injection hmem1 with hmem1
  injection hmem2 with hmem2
  rw [← hmem1, ← hmem2, hii, hvv]
  exact Devm.EqModGas.of_memWrite hag3

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

/-- R1 probe, op 3: `sstore` congruence. -/
theorem probe_sstore {e : Sevm} {a a' b b' : Devm}
    (h1 : Ninst.Run e a (Ninst.reg .sstore) a')
    (h2 : Ninst.Run e b (Ninst.reg .sstore) b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  rcases of_run_reg h1 with ⟨pc1, run1⟩
  rcases of_run_reg h2 with ⟨pc2, run2⟩
  simp only [Rinst.run, Rinst.runCore] at run1 run2
  rcases Except.bind_eq_ok run1 with ⟨⟨k1, a1⟩, hp1, run1⟩
  rcases Except.bind_eq_ok run2 with ⟨⟨k2, b1⟩, hp2, run2⟩
  rcases Except.bind_eq_ok run1 with ⟨⟨n1, a2⟩, hq1, run1⟩
  rcases Except.bind_eq_ok run2 with ⟨⟨n2, b2⟩, hq2, run2⟩
  rcases Except.bind_eq_ok run1 with ⟨_, _, run1⟩
  rcases Except.bind_eq_ok run2 with ⟨_, _, run2⟩
  rcases Except.bind_eq_ok run1 with ⟨⟨a3, g21⟩, hacc1, run1⟩
  rcases Except.bind_eq_ok run2 with ⟨⟨b3, g22⟩, hacc2, run2⟩
  rcases Except.bind_eq_ok run1 with ⟨g31, hg1, run1⟩
  rcases Except.bind_eq_ok run2 with ⟨g32, hg2, run2⟩
  rcases Except.bind_eq_ok run1 with ⟨a4, hr1, run1⟩
  rcases Except.bind_eq_ok run2 with ⟨b4, hr2, run2⟩
  rcases Except.bind_eq_ok run1 with ⟨a5, hc1, run1⟩
  rcases Except.bind_eq_ok run2 with ⟨b5, hc2, run2⟩
  rcases Except.bind_eq_ok run1 with ⟨_, _, hset1⟩
  rcases Except.bind_eq_ok run2 with ⟨_, _, hset2⟩
  obtain ⟨hkey, hag1⟩ := Devm.EqModGas.of_pop (Devm.pop_of_pop hp1) (Devm.pop_of_pop hp2) h
  obtain ⟨hnew, hag2⟩ := Devm.EqModGas.of_pop (Devm.pop_of_pop hq1) (Devm.pop_of_pop hq2) hag1
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
      exact Devm.EqModGas.of_addAccessedStorageKey hag2
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
    exact Devm.EqModGas.of_withRefundCounter hag3
  rw [hg3eq] at hc1
  have hag5 := Devm.EqModGas.of_burn (Devm.burn_of_chargeGas hc1)
    (Devm.burn_of_chargeGas hc2) hag4
  injection hset1 with hset1
  injection hset2 with hset2
  rw [← hset1, ← hset2, hkey, hnew]
  exact Devm.EqModGas.of_setStorVal hag5

end Blanc
