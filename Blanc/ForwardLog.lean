import Blanc.ForwardCall

/-!
# Selected `LOG` walk step

Contract-neutral `LOG` rule exposing every world projection the step preserves,
for walks that must carry storage, access-set and code facts across an emitted
event.
-/

namespace Blanc

open Jaune

/-- `LOG` as a walk step, exposing every world projection the step preserves.
`Func.runCompiledTo_log_step` is the same rule with the storage map and the
accessed-address set left implicit; both remain available. -/
lemma Func.runCompiledTo_log_step_ext {fs : List Func} {sevm : Sevm}
    {devm : Devm}
    {n : Fin 5} {i sz : B256} {topics s : List B256} {c : Nat} {M M' : Mem}
    {payload : Bytes} {rest : Func} {ex : Execution}
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
      (∀ a : Adr, Devm.getStor base a = Devm.getStor devm a) →
      (∀ a : Adr, base.getBal a = devm.getBal a) →
      (∀ a : Adr, base.getCode a = devm.getCode a) →
      base.accessedStorageKeys = devm.accessedStorageKeys →
      base.accessedAddresses = devm.accessedAddresses →
      base.output = devm.output →
      base.error = devm.error →
      devm.gasLeft = G + c →
      Func.RunCompiledTo fs sevm (base.setMach ⟨s, M', G⟩) rest ex) :
    Func.RunCompiledTo fs sevm devm (Func.next (.reg (.log n)) rest) ex := by
  subst h_mem
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_log_of (G := devm.gasLeft - c) h_stk h_len h_static
      h_cost h_data h_img (by omega)) ?_
  exact h_next _ _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) rfl rfl rfl rfl (by omega)

/-- Existential form of the same rule: the post-log state is exhibited, so a
walk that must produce a concrete outcome downstream can compose with it.  The
continuation form above is the same fact with the state left universally
quantified. -/
lemma Func.runCompiledTo_log_step_exists {fs : List Func} {sevm : Sevm}
    {devm : Devm}
    {n : Fin 5} {i sz : B256} {topics s : List B256} {c G : Nat} {M M' : Mem}
    {payload : Bytes} {rest : Func}
    (h_stk : devm.stack = i :: sz :: (topics ++ s))
    (h_len : topics.length = n.val) (h_static : sevm.isStatic = false)
    (h_mem : devm.memory = M)
    (h_cost : gLog + gLogdata * sz.toNat + gLogtopic * n.val
      + devm.extCost [⟨i.toNat, sz.toNat⟩] = c)
    (h_data : (M.read i.toNat sz.toNat).1 = payload)
    (h_img : (M.read i.toNat sz.toNat).2 = M')
    (h_gas : devm.gasLeft = G + c) :
    ∃ logged : Devm,
      logged.logs = devm.logs ++ [⟨sevm.currentTarget, topics, payload⟩] ∧
      (∀ (a : Adr) (k : B256), logged.getStorVal a k = devm.getStorVal a k) ∧
      (∀ a : Adr, Devm.getStor logged a = Devm.getStor devm a) ∧
      (∀ a : Adr, logged.getBal a = devm.getBal a) ∧
      (∀ a : Adr, logged.getCode a = devm.getCode a) ∧
      logged.accessedStorageKeys = devm.accessedStorageKeys ∧
      logged.accessedAddresses = devm.accessedAddresses ∧
      logged.output = devm.output ∧
      logged.error = devm.error ∧
      ∀ {ex : Execution},
        Func.RunCompiledTo fs sevm (logged.setMach ⟨s, M', G⟩) rest ex →
        Func.RunCompiledTo fs sevm devm (Func.next (.reg (.log n)) rest) ex := by
  refine ⟨devm.addLog ⟨sevm.currentTarget, topics, payload⟩, rfl,
    fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl,
    rfl, rfl, ?_⟩
  intro ex htail
  subst h_mem
  exact Func.RunCompiledTo.next
    (Ninst.runCompiled_log_of (G := G) h_stk h_len h_static h_cost h_data
      h_img (by omega)) htail

end Blanc
