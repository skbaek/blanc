import Blanc.ForkUniform
import Jaune.Transaction

/-!
# Transaction preparation under a covered fork

A message prepared under a covered fork `g` is the message prepared under any other covered fork
with its fork changed, **when the transaction's access list already warms every address the
preparation warms** (`prepareMessage` pre-warms the fork's precompiles, EIP-2929, and the fork
defines a different set: Osaka adds `P256VERIFY`, EIP-7951).  Re-inserting an address already in a
`Std.HashSet` returns the very same set (`hashSet_insert_of_mem`), so `prepareMessage`'s
`insertMany` is the identity on such an access list and the accessed set is the same term under
every fork.

`Std.HashSet` insertion does not evaluate in the kernel (the bucket index goes through the opaque
`System.Platform.numBits`), so this cannot be settled by a kernel `rfl`: these lemmas are the
proof.
-/

namespace Blanc.TransactionFork

open Jaune Blanc.ForkUniform

theorem raw_insertIfNew_of_contains {α : Type} {β : α → Type} [BEq α] [Hashable α]
    (m : Std.DHashMap.Internal.Raw₀ α β) (a : α) (b : β a) (h : m.contains a = true) :
    Std.DHashMap.Internal.Raw₀.insertIfNew m a b = m := by
  obtain ⟨⟨size, buckets⟩, hm⟩ := m
  unfold Std.DHashMap.Internal.Raw₀.contains at h
  unfold Std.DHashMap.Internal.Raw₀.insertIfNew
  simp only at h ⊢
  split
  · rfl
  · rename_i hn; exact absurd h hn

/-- **Inserting an element a hash set already contains returns the same set.** -/
theorem hashSet_insert_of_mem {α : Type} [BEq α] [Hashable α] (s : Std.HashSet α) (a : α)
    (h : s.contains a = true) : s.insert a = s := by
  obtain ⟨⟨⟨raw, wf⟩⟩⟩ := s
  have hc : Std.DHashMap.Internal.Raw₀.contains ⟨raw, wf.size_buckets_pos⟩ a = true := h
  have := raw_insertIfNew_of_contains ⟨raw, wf.size_buckets_pos⟩ a () hc
  show Std.HashSet.mk (Std.HashMap.mk (Std.DHashMap.insertIfNew ⟨raw, wf⟩ a ())) =
    Std.HashSet.mk (Std.HashMap.mk ⟨raw, wf⟩)
  congr 2
  unfold Std.DHashMap.insertIfNew
  simp only [this]

/-- Inserting elements a hash set already contains returns the same set. -/
theorem hashSet_insertMany_of_subset {α : Type} [BEq α] [Hashable α] (s : Std.HashSet α)
    (l : List α) (h : ∀ a ∈ l, s.contains a = true) : s.insertMany l = s := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [Std.HashSet.insertMany_cons, hashSet_insert_of_mem s x (h x (by simp))]
    exact ih (fun a ha => h a (by simp [ha]))

/-- **A message prepared under a covered fork is the message prepared under another with its fork
changed**, for a call transaction whose access list warms the origin, the target and the
precompiles of both forks. -/
theorem prepareMessage_withFork {benv : Benv} {tenv : Tenv} {tx : Tx} {target : Adr} {g : Fork}
    (hr : tx.type.receiver? = some target)
    (h1 : ∀ a ∈ benv.stat.rules.precompiles ++ [tenv.stat.origin, target],
      tenv.stat.accessListAddresses.contains a = true)
    (h2 : ∀ a ∈ (Fork.ruleSet g).precompiles ++ [tenv.stat.origin, target],
      tenv.stat.accessListAddresses.contains a = true) :
    prepareMessage (benv.withFork g) tenv tx = (prepareMessage benv tenv tx).map (·.withFork g) := by
  unfold prepareMessage
  simp only [hr]
  show (Except.ok _ : Except TransitionError Msg) = _
  simp only [Except.map]
  rw [show (benv.withFork g).stat.rules.precompiles = (Fork.ruleSet g).precompiles from rfl,
    hashSet_insertMany_of_subset _ _ h2, hashSet_insertMany_of_subset _ _ h1]
  rfl

end Blanc.TransactionFork
