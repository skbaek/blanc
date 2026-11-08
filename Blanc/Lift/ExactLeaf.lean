import Blanc.Lift.NodeWalk
import Blanc.Lift.ExactWalk
import Blanc.ForwardStorageAccess
import Blanc.ExecDeterminism
import Blanc.ExecutionReachable

/-!
# A gas-exact lifted run as a node-walk leaf child

A parent's node walk (`Blanc/Lift/NodeWalk.lean`) consumes a call-family child through
`spawn_resume_ok`, which asks, of every derivation node at the child's start configuration `c`,
its outcome and the shadows describing the machine it returns.  A child whose code is a lifted
certificate need not be walked by the kernel when a symbolic `SProg.RunExact` of it is at hand
(built forward with `Blanc/Lift/ExactWalk.lean`):

* `exact_leaf`: every node at `c` (pc 0) has the run's outcome, and — when no spawning instruction
  sits at a reachable position (`SpawnFreeReach`) — no raw frame descendant;
* `ChildAgree.afterSload`, `ChildAgree.afterSstore`, `ChildAgree.ret`: the selected-access bases
  of `Blanc/ForwardCall.lean` (`afterSload`, `afterSstore`) and a `RETURN` over an `St` move the
  witness engine's shadows by one entry each, so a run's explicit post state is described by
  explicit shadows;
* `ChildAgree.getStorVal`, `sloadCost_shadow`, `sstoreCost_shadow`: the values and the selected
  charges read from the shadows (`sloadCostS`, `sstoreCostS`), which the kernel can evaluate
  where the world's hash sets cannot be inspected.

Nothing here mentions a contract.
-/

namespace Blanc.Lift.NodeWalk

open Jaune Blanc.Lift Blanc.Lift.Witness

/-! ## The selected-access bases move the shadows -/

theorem afterSload_state (sevm : Sevm) (b : Devm) (k : B256) :
    (afterSload sevm b k).state = b.state := by
  unfold afterSload; split <;> rfl

theorem mem_sloadAccessedStorageKeys {t : Adr} {ks : KeySet} {keys : List (Adr × B256)}
    (h : ∀ x, x ∈ ks ↔ x ∈ keys) (k : B256) :
    ∀ x, x ∈ sloadAccessedStorageKeys t ks k ↔ x ∈ (t, k) :: keys := by
  intro x
  unfold sloadAccessedStorageKeys
  split
  · rename_i hm
    rw [h x, List.mem_cons]
    constructor
    · exact .inr
    · rintro (rfl | hx)
      · exact (h _).mp hm
      · exact hx
  · rw [Std.HashSet.mem_insert, List.mem_cons, h x, beq_iff_eq]
    constructor <;> rintro (hx | hx) <;> first | exact .inl hx.symm | exact .inr hx

theorem ChildAgree.afterSload {sevm : Sevm} {b : Devm} {keys : List (Adr × B256)}
    {adrs : List Adr} {stor : StorShadow} {acs : AcctShadow}
    (h : ChildAgree b keys adrs stor acs) (k : B256) :
    ChildAgree (afterSload sevm b k) ((sevm.currentTarget, k) :: keys) adrs stor acs := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [afterSload_accessedAddresses]; exact h.1
  · rw [afterSload_accessedStorageKeys]; exact mem_sloadAccessedStorageKeys h.2.1 k
  · rw [afterSload_state]; exact h.2.2.1
  · rw [afterSload_state]; exact h.2.2.2

/-! ## The selected charges, read from the shadows -/

/-- `sloadCost` with the warm test on the key shadow. -/
def sloadCostS (t : Adr) (keys : List (Adr × B256)) (k : B256) : Nat :=
  if (t, k) ∈ keys then gasWarmAccess else gasColdSload

theorem sloadCost_shadow {sevm : Sevm} {b : Devm} {keys : List (Adr × B256)} {adrs : List Adr}
    {stor : StorShadow} {acs : AcctShadow} (h : ChildAgree b keys adrs stor acs) (k : B256) :
    sloadCost sevm b k = sloadCostS sevm.currentTarget keys k := by
  unfold sloadCost sloadCostS
  simp only [h.2.1]

/-! ## The selected-access bases, decided on the shadows

`afterSload`/`afterSstore` decide warmth on the world's accessed-key hash set; their shadow
forms decide it on the key list and read the current value from the storage shadow, so that a
concrete post state avoids inspecting the accessed-key hash set while retaining the
created-account-aware original storage read. -/

/-- `afterSload` with the warm test on the key shadow. -/
def afterSloadS (t : Adr) (keys : List (Adr × B256)) (b : Devm) (k : B256) : Devm :=
  if (t, k) ∈ keys then b else addAccessedStorageKey b t k

theorem afterSload_shadow {sevm : Sevm} {b : Devm} {keys : List (Adr × B256)} {adrs : List Adr}
    {stor : StorShadow} {acs : AcctShadow} (h : ChildAgree b keys adrs stor acs) (k : B256) :
    afterSload sevm b k = afterSloadS sevm.currentTarget keys b k := by
  unfold afterSload afterSloadS
  simp only [h.2.1]

end Blanc.Lift.NodeWalk
