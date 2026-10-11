import Blanc.ForwardCall

namespace Blanc

open Jaune

/-! Temporary nonce-preserving ExecSat donors, pending common-library hoisting. -/

lemma Func.execSat_sload_step_with_nonce {fs : List Func} {sevm : Sevm} {devm : Devm}
    {k v : B256} {s : List B256} {M : Mem} {rest : Func} {P : Execution → Prop}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_stk : devm.stack = k :: s) (h_room : s.length < 1024)
    (h_val : devm.getStorVal sevm.currentTarget k = v)
    (h_mem : devm.memory = M)
    (h_gas : gasColdSload ≤ devm.gasLeft)
    (h_next : ∀ (base : Devm) (c G : Nat),
      (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ base.accessedStorageKeys →
      (∀ p : Adr × B256, p ∈ devm.accessedStorageKeys →
        p ∈ base.accessedStorageKeys) →
      (∀ (a : Adr) (k' : B256), base.getStorVal a k' = devm.getStorVal a k') →
      (∀ a : Adr, base.getBal a = devm.getBal a) →
      (∀ a : Adr, base.getCode a = devm.getCode a) →
      (∀ a : Adr, base.state.getNonce a = devm.state.getNonce a) →
      base.refundCounter = devm.refundCounter →
      base.logs = devm.logs →
      base.output = devm.output →
      base.error = devm.error →
      base.accountsToDelete = devm.accountsToDelete →
      gasWarmAccess ≤ c → c ≤ gasColdSload →
      devm.gasLeft = G + c →
      Func.ExecSat fs sevm (base.setMach ⟨v :: s, M, G, base.stateGas⟩) rest P) :
    Func.ExecSat fs sevm devm (Func.next Ninst.sload rest) P := by
  subst h_val; subst h_mem
  set base : Devm :=
    if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
    then devm else addAccessedStorageKey devm sevm.currentTarget k with h_base
  set c : Nat :=
    if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
    then gasWarmAccess else gasColdSload with h_c
  have h_lo : gasWarmAccess ≤ c := (le_sload_cost_of h_c.symm).1
  have h_hi : c ≤ gasColdSload := (le_sload_cost_of h_c.symm).2
  rcases h_next base c (devm.gasLeft - c)
      (mem_accessedStorageKeys_sload_of h_base.symm)
      (fun _ hp => mem_accessedStorageKeys_sload_of_mem h_base.symm hp)
      (fun _ _ => getStorVal_sload_of h_base.symm)
      (fun _ => by rw [h_base]; split <;> rfl)
      (fun _ => by rw [h_base]; split <;> rfl)
      (fun _ => by rw [h_base]; split <;> rfl)
      (refundCounter_sload_of h_base.symm) (logs_sload_of h_base.symm)
      (by rw [h_base]; split <;> rfl)
      (by rw [h_base]; split <;> rfl)
      (by rw [h_base]; split <;> rfl)
      h_lo h_hi (by omega) with ⟨ex, hto, hp⟩
  exact ⟨ex, Func.ExecWitness.next
    (Ninst.runCompiled_sload_of (base := base) (c := c) (G := devm.gasLeft - c)
      h_stk hfork h_base.symm h_c.symm rfl (by omega) h_room) hto, hp⟩

lemma Func.execSat_sstore_warm_step_with_nonce {fs : List Func} {sevm : Sevm}
    {devm : Devm} {k v : B256} {s : List B256} {M : Mem} {rest : Func}
    {P : Execution → Prop}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_stk : devm.stack = k :: v :: s)
    (h_warm : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys)
    (h_static : sevm.isStatic = false)
    (h_mem : devm.memory = M)
    (h_gas : gasStorageSet ≤ devm.gasLeft)
    (h_next : ∀ (base : Devm) (c G : Nat),
      base.getStorVal sevm.currentTarget k = v →
      (∀ (a : Adr) (k' : B256), (a, k') ≠ (sevm.currentTarget, k) →
      base.getStorVal a k' = devm.getStorVal a k') →
      (∀ a : Adr, base.getBal a = devm.getBal a) →
      (∀ a : Adr, base.getCode a = devm.getCode a) →
      (∀ a : Adr, base.state.getNonce a = devm.state.getNonce a) →
      base.accessedStorageKeys = devm.accessedStorageKeys →
      base.logs = devm.logs →
      base.output = devm.output →
      base.error = devm.error →
      base.accountsToDelete = devm.accountsToDelete →
      base.refundCounter = sstoreNewRefundCounter sevm.benvStat.rules.gas v
        (devm.getOrigStorVal sevm sevm.currentTarget k)
        (devm.getStorVal sevm.currentTarget k) devm.refundCounter →
      c ≤ gasStorageSet →
      devm.gasLeft = G + c →
      Func.ExecSat fs sevm (base.setMach ⟨s, M, G, base.stateGas⟩) rest P) :
    Func.ExecSat fs sevm devm (Func.next Ninst.sstore rest) P := by
  subst h_mem
  have h_bound : sstoreValueCost (devm.getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k) v ≤ gasStorageSet := by
    rw [sstoreValueCost]; split_ifs <;> decide
  have h_key : ((devm.withRefundCounter (sstoreNewRefundCounter sevm.benvStat.rules.gas v
      (devm.getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k)
      devm.refundCounter)).setStorVal sevm.currentTarget k v).getStorVal
        sevm.currentTarget k = v := by
    show (Devm.getStor _ sevm.currentTarget).get k = v
    rw [setStorVal_getStor_self, Stor.get_set_self]
  have h_oth : ∀ (a : Adr) (k' : B256), (a, k') ≠ (sevm.currentTarget, k) →
      ((devm.withRefundCounter (sstoreNewRefundCounter sevm.benvStat.rules.gas v
        (devm.getOrigStorVal sevm sevm.currentTarget k)
        (devm.getStorVal sevm.currentTarget k)
        devm.refundCounter)).setStorVal sevm.currentTarget k v).getStorVal a k'
          = devm.getStorVal a k' := by
    intro a k' h_ne
    by_cases h_adr : sevm.currentTarget = a
    · subst h_adr
      have h_key' : k ≠ k' := fun h => h_ne (by rw [h])
      show (Devm.getStor _ sevm.currentTarget).get k' = _
      rw [setStorVal_getStor_self, Stor.get_set_ne _ h_key']
      rfl
    · show (Devm.getStor _ a).get k' = _
      have h_off : Devm.getStor
          ((devm.withRefundCounter (sstoreNewRefundCounter sevm.benvStat.rules.gas v
            (devm.getOrigStorVal sevm sevm.currentTarget k)
            (devm.getStorVal sevm.currentTarget k)
            devm.refundCounter)).setStorVal sevm.currentTarget k v) a
            = Devm.getStor devm a := by
        simp only [Devm.getStor, Devm.getAcct, Devm.setStorVal, Devm.withState,
          Devm.withStorageWrites, Devm.setWorld, State.setStorVal]
        simp only [Devm.state, State.get_set_ne _ h_adr]
        rfl
      rw [h_off]
      rfl
  rcases h_next _ _ (devm.gasLeft - sstoreValueCost
      (devm.getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k) v)
      h_key h_oth
      (fun a => by
        have hbc := State.setStorVal_balCodeEq devm.state sevm.currentTarget k v
        exact (congrArg Prod.fst (congrFun hbc a)).symm)
      (fun a => by
        have hbc := State.setStorVal_balCodeEq devm.state sevm.currentTarget k v
        exact (congrArg Prod.snd (congrFun hbc a)).symm)
      (fun a => by
        change ((devm.state.setStorVal sevm.currentTarget k v).get a).nonce =
          (devm.state.get a).nonce
        by_cases ha : sevm.currentTarget = a
        · subst a
          simp only [State.setStorVal, State.get_set_self]
        · simp only [State.setStorVal, State.get_set_ne _ ha])
      rfl rfl rfl rfl rfl rfl h_bound (by omega) with ⟨ex, hto, hp⟩
  exact ⟨ex, Func.ExecWitness.next
    (Ninst.runCompiled_sstore_warm (c := sstoreValueCost
        (devm.getOrigStorVal sevm sevm.currentTarget k)
        (devm.getStorVal sevm.currentTarget k) v)
      (G := devm.gasLeft - sstoreValueCost
        (devm.getOrigStorVal sevm sevm.currentTarget k)
        (devm.getStorVal sevm.currentTarget k) v)
      hfork.rules_stateGas_none h_stk h_warm
      (by simp only [gCallStipend, gasStorageSet] at *; omega)
      h_static rfl rfl (by omega)) hto, hp⟩

lemma Func.execSat_log_step_with_nonce {fs : List Func} {sevm : Sevm} {devm : Devm}
    {n : Fin 5} {i sz : B256} {topics s : List B256} {c : Nat} {M M' : Mem}
    {payload : Bytes} {rest : Func} {P : Execution → Prop}
    (h_stk : devm.stack = i :: sz :: (topics ++ s))
    (h_len : topics.length = n.val) (h_static : sevm.isStatic = false)
    (h_mem : devm.memory = M)
    (h_cost : gLog + gLogdata * sz.toNat + gLogtopic * n.val
      + devm.extCost [⟨i.toNat, sz.toNat⟩] = c)
    (h_data : (M.read i.toNat sz.toNat).1 = payload)
    (h_img : (M.read i.toNat sz.toNat).2 = M')
    (h_gas : c ≤ devm.gasLeft)
    (h_next : ∀ (base : Devm) (G : Nat),
      base.logs = devm.logs ++ [⟨sevm.currentTarget, topics, payload⟩] →
      (∀ (a : Adr) (k : B256), base.getStorVal a k = devm.getStorVal a k) →
      (∀ a : Adr, base.getBal a = devm.getBal a) →
      (∀ a : Adr, base.getCode a = devm.getCode a) →
      (∀ a : Adr, base.state.getNonce a = devm.state.getNonce a) →
      base.accessedStorageKeys = devm.accessedStorageKeys →
      base.refundCounter = devm.refundCounter →
      base.output = devm.output →
      base.error = devm.error →
      base.accountsToDelete = devm.accountsToDelete →
      devm.gasLeft = G + c →
      Func.ExecSat fs sevm (base.setMach ⟨s, M', G, base.stateGas⟩) rest P) :
    Func.ExecSat fs sevm devm (Func.next (.reg (.log n)) rest) P := by
  subst h_mem
  rcases h_next (devm.addLog ⟨sevm.currentTarget, topics, payload⟩)
      (devm.gasLeft - c) rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      rfl rfl rfl rfl rfl (by omega)
    with ⟨ex, hto, hp⟩
  exact ⟨ex, Func.ExecWitness.next
    (Ninst.runCompiled_log_of (G := devm.gasLeft - c) h_stk h_len h_static
      h_cost h_data h_img (by omega)) hto, hp⟩

end Blanc
