import Blanc.Lift.NodeWalkFrames
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

/-- **A lifted gas-exact run is the outcome of every node at the frame's entry.**  With the code
spawn-free at reachable positions, no such node has a raw frame descendant. -/
theorem exact_leaf {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    (hj : Cert.jumpsOk code c = true) (hsf : SpawnFreeReach code) {sevm : Sevm} {c0 : PCfg}
    {post : Devm} (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hpc : c0.pc = 0) (hrun : SProg.RunExact c.prog sevm c0.devm post) :
    ∀ x, NodeAt sevm c0 x → x.exn = .ok post ∧ Exec.rawFrameDescendants x.exc = [] := by
  intro x hx
  obtain ⟨e⟩ := lift_exact hc hj hcode hfork hrun
  obtain ⟨xpc, xs, xd, xexn, xexc⟩ := x
  obtain ⟨h1, h2, h3⟩ := hx
  simp only at h1 h2 h3
  subst h2 h3
  rw [hpc] at h1
  subst h1
  exact ⟨Blanc.Exec.result_unique xexc e,
    Blanc.Exec.rawFrameDescendants_eq_nil_of_reach xexc (noPushBefore_zero _ _)
      (by rw [hcode]; exact hsf)⟩

/-! ## The selected-access bases move the shadows -/

theorem afterSload_state (sevm : Sevm) (b : Devm) (k : B256) :
    (afterSload sevm b k).state = b.state := by
  unfold afterSload; split <;> rfl

theorem afterSstore_state (sevm : Sevm) (b : Devm) (k v : B256) :
    (afterSstore sevm b k v).state = b.state.setStorVal sevm.currentTarget k v := by
  unfold afterSstore; split <;> rfl

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

theorem ChildAgree.afterSstore {sevm : Sevm} {b : Devm} {keys : List (Adr × B256)}
    {adrs : List Adr} {stor : StorShadow} {acs : AcctShadow}
    (h : ChildAgree b keys adrs stor acs) (k v : B256) :
    ChildAgree (afterSstore sevm b k v) ((sevm.currentTarget, k) :: keys) adrs
      (((sevm.currentTarget, k), v) :: stor) acs := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [afterSstore_accessedAddresses]; exact h.1
  · rw [afterSstore_accessedStorageKeys]; exact mem_sloadAccessedStorageKeys h.2.1 k
  · rw [afterSstore_state]; exact storOf_setStorVal_cons h.2.2.1
  · rw [afterSstore_state]; exact acctAgree_setStorVal h.2.2.2 _ _ _

/-- A `RETURN` over an `St` keeps the base's world and accessed sets. -/
theorem ChildAgree.ret {b : Devm} {keys : List (Adr × B256)} {adrs : List Adr}
    {stor : StorShadow} {acs : AcctShadow} (h : ChildAgree b keys adrs stor acs)
    (S : List B256) (M : Mem) (G i n : Nat) (out : Bytes) :
    ChildAgree (((St b S M G).memRead i n).2.withOutput out) keys adrs stor acs := h

/-- The storage the shadow describes is the storage the machine reads. -/
theorem ChildAgree.getStorVal {b : Devm} {keys : List (Adr × B256)} {adrs : List Adr}
    {stor : StorShadow} {acs : AcctShadow} (h : ChildAgree b keys adrs stor acs) (a : Adr)
    (k : B256) : b.getStorVal a k = lookupS stor a k :=
  h.2.2.1 a k

/-! ## The selected charges, read from the shadows -/

/-- `sloadCost` with the warm test on the key shadow. -/
def sloadCostS (t : Adr) (keys : List (Adr × B256)) (k : B256) : Nat :=
  if (t, k) ∈ keys then gasWarmAccess else gasColdSload

/-- `sstoreCost` with the warm test on the key shadow and the current value on the storage
shadow. -/
def sstoreCostS (sevm : Sevm) (keys : List (Adr × B256)) (stor : StorShadow) (k v : B256) : Nat :=
  (if (sevm.currentTarget, k) ∈ keys then 0 else gasColdSload) +
    sstoreValueCost (getOrigStorVal sevm sevm.currentTarget k)
      (lookupS stor sevm.currentTarget k) v

theorem sloadCost_shadow {sevm : Sevm} {b : Devm} {keys : List (Adr × B256)} {adrs : List Adr}
    {stor : StorShadow} {acs : AcctShadow} (h : ChildAgree b keys adrs stor acs) (k : B256) :
    sloadCost sevm b k = sloadCostS sevm.currentTarget keys k := by
  unfold sloadCost sloadCostS
  simp only [h.2.1]

theorem sstoreCost_shadow {sevm : Sevm} {b : Devm} {keys : List (Adr × B256)} {adrs : List Adr}
    {stor : StorShadow} {acs : AcctShadow} (h : ChildAgree b keys adrs stor acs) (k v : B256) :
    sstoreCost sevm b k v = sstoreCostS sevm keys stor k v := by
  unfold sstoreCost sstoreCostS
  simp only [h.2.1, ChildAgree.getStorVal h]

/-! ## The selected-access bases, decided on the shadows

`afterSload`/`afterSstore` decide warmth on the world's accessed-key hash set; their shadow
forms decide it on the key list and read the current value from the storage shadow, so that a
concrete post state is evaluated without inspecting a hash set. -/

/-- `afterSload` with the warm test on the key shadow. -/
def afterSloadS (t : Adr) (keys : List (Adr × B256)) (b : Devm) (k : B256) : Devm :=
  if (t, k) ∈ keys then b else addAccessedStorageKey b t k

/-- `afterSstore` with the warm test on the key shadow and the current value on the storage
shadow. -/
def afterSstoreS (sevm : Sevm) (keys : List (Adr × B256)) (stor : StorShadow) (b : Devm)
    (k v : B256) : Devm :=
  ((if (sevm.currentTarget, k) ∈ keys then b else addAccessedStorageKey b sevm.currentTarget k).withRefundCounter
      (sstoreNewRefundCounter sevm.benvStat.rules.gas v
        (getOrigStorVal sevm sevm.currentTarget k)
        (lookupS stor sevm.currentTarget k) b.refundCounter)).setStorVal
    sevm.currentTarget k v

theorem afterSload_shadow {sevm : Sevm} {b : Devm} {keys : List (Adr × B256)} {adrs : List Adr}
    {stor : StorShadow} {acs : AcctShadow} (h : ChildAgree b keys adrs stor acs) (k : B256) :
    afterSload sevm b k = afterSloadS sevm.currentTarget keys b k := by
  unfold afterSload afterSloadS
  simp only [h.2.1]

theorem afterSstore_shadow {sevm : Sevm} {b : Devm} {keys : List (Adr × B256)} {adrs : List Adr}
    {stor : StorShadow} {acs : AcctShadow} (h : ChildAgree b keys adrs stor acs) (k v : B256) :
    afterSstore sevm b k v = afterSstoreS sevm keys stor b k v := by
  unfold afterSstore afterSstoreS
  simp only [h.2.1, ChildAgree.getStorVal h]

end Blanc.Lift.NodeWalk
