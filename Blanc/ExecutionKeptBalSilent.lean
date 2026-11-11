import Blanc.ExecutionKeptValue
import Blanc.Lift.BalSilent
import Blanc.SystemCallForward

/-!
# Balance-silent contracts on kept histories

`Blanc.Lift.frame_keeps_balances` says a certified contract with no call-family, `CREATE` or
`SELFDESTRUCT` node leaves every account's balance unchanged across any successful frame, on any
fork. `Blanc.ExecutionKeptValue` folds that per-frame law into `KeptValueAt` and
`KeptHistory.bal_covers`. This module joins the two so any balance-silent contract (and in
particular any canonical system contract in `systemContracts`) obtains `KeptValueAt` and the
kept-history value cover without per-family boilerplate.
-/

namespace Blanc

open Jaune Lift

/-- A certified balance-silent contract satisfies `KeptValueAt` at any address holding its code. -/
theorem KeptValueAt.of_balSilent {a : Adr} {C : ByteArray} {c : Cert} {S : List Nat}
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (hc : Cert.check C c = true) (hno : Lift.ProgNoExec c.prog)
    (closed : Lift.BalSilentSet c.prog S = true) (root : 0 ∈ S) : KeptValueAt a C :=
  ⟨nonempty, nondelegating, fun _ hcode exec =>
    congrArg B256.toNat (congrFun (Lift.frame_keeps_balances hc hno closed root hcode exec) a)⟩

/-- No canonical system contract sits at a precompile address on any kept fork (covered or
Amsterdam). -/
theorem systemContracts_keptFork_not_precompile {p : Adr × ByteArray}
    (member : p ∈ systemContracts) (f : Fork) (kept : KeptFork f) :
    ¬ f.ruleSet.isPrecomp p.1 := by
  rcases kept with covered | rfl
  · exact systemContracts_not_precompile member covered
  · simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide +kernel

/-- A canonical system contract whose certificate is balance-silent satisfies `KeptValueAt`. -/
theorem KeptValueAt.of_systemContract {p : Adr × ByteArray} {c : Cert} {S : List Nat}
    (member : p ∈ systemContracts) (hc : Cert.check p.2 c = true) (hno : Lift.ProgNoExec c.prog)
    (closed : Lift.BalSilentSet c.prog S = true) (root : 0 ∈ S) : KeptValueAt p.1 p.2 :=
  let ⟨_, hd, hne⟩ := systemContracts_facts p member
  .of_balSilent hne hd hc hno closed root

/-- **Kept-history value cover for a balance-silent system contract.** Once the canonical code is
installed at the start, no block sends a transaction from the contract's address, and root/credit
no-wrap bounds hold, the final balance covers the starting balance plus every kept frame's carried
value. -/
theorem KeptHistory.systemContract_bal_covers {cfg : ChainConfig} {start post : BlockChain}
    {blocks : List KeptBlock} (h : KeptHistory cfg start blocks post)
    {p : Adr × ByteArray} {c : Cert} {S : List Nat} (member : p ∈ systemContracts)
    (hc : Cert.check p.2 c = true) (hno : Lift.ProgNoExec c.prog)
    (closed : Lift.BalSilentSet c.prog S = true) (root : 0 ∈ S)
    (code : start.state.getCode p.1 = p.2)
    (senders : ∀ b ∈ blocks, NoSenderAt p.1 b.run.senders)
    (fits : HistoryRootsFit blocks) (credits : HistoryCreditsFit p.1 blocks) :
    (start.state.bal p.1).toNat +
      ((blocks.flatMap (KeptBlock.keptAt p.1)).map fun f => f.sevm.value.toNat).sum ≤
      (post.state.bal p.1).toNat :=
  h.bal_covers (.of_systemContract member hc hno closed root) code
    (systemContracts_keptFork_not_precompile member) senders fits credits

/-- Filtering a list before summing a `Nat`-valued map never increases the sum. -/
theorem sum_map_filter_le {α : Type _} (xs : List α) (p : α → Bool) (f : α → Nat) :
    ((xs.filter p).map f).sum ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp only [List.filter_nil, List.map_nil, List.sum_nil, Nat.le_refl]
  | cons x xs ih =>
      rw [List.filter_cons, List.map_cons, List.sum_cons]
      split
      · rw [List.map_cons, List.sum_cons]
        exact Nat.add_le_add_left ih (f x)
      · exact Nat.le_trans ih (Nat.le_add_left _ (f x))

end Blanc
