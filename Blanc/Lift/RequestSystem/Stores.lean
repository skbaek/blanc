import Blanc.Lift.AmsterdamWalk
import Blanc.Lift.WalkSteps
import Blanc.StorageRefund

/-!
# A fork's stores, as a request contract's system path takes them

The system path of a request contract (`Blanc/Lift/RequestSystem/Path.lean`) reads and writes storage, and
only its writes differ between the covered forks and Amsterdam: its reads are `rx_sloadA` on any fork with
EIP-2929 access. `SysStores` is a fork's `SSTORE` as the path sees it: the successor base, the charge taken
from `gasLeft`, a bound on that charge, and what a frame must carry to make its remaining stores (`Ready`).

This is a different shape from the builder user frames' `StorageSteps` (`Blanc/Lift/BuilderRequest/FeePath.lean`),
for a reason the bytes do not choose: a system call under Amsterdam draws its state gas from the system
reservoir, not from `gasLeft`, so its stores charge `sstoreCostA` against a `Ready` reservoir rather than
`StorageSteps`' charge-and-repay against `gasLeft`. The readiness predicate is therefore part of the record.

`amsterdamStores` is the Amsterdam instance (Ready is `Blanc.Lift.Ready`, the reservoir invariant);
`coveredStores` is the covered forks' (no state gas; Ready is `CoveredReady`: no error, a nonnegative
refund counter, slots still clean).
-/

namespace Blanc.Lift.RequestSystem

open Jaune

/-- A fork's `SSTORE` as a request contract's system path takes it. -/
structure SysStores (sevm : Sevm) where
  /-- The base after a write of a key. -/
  afterWrite : Devm → B256 → B256 → Devm
  /-- What a write takes from `gasLeft`. -/
  writeCost : Devm → B256 → B256 → Nat
  /-- A bound on `writeCost`, from the rule record. -/
  writeMax : Nat
  /-- What a frame carries to make its remaining stores at these keys. -/
  Ready : Devm → List B256 → Prop

namespace SysStores

variable {sevm : Sevm} (w : SysStores sevm)

/-- `SSTORE` runs as these stores say, from a base ready for it. -/
def Runs : Prop :=
  ∀ {fs : List SFunc} {f : SFunc} {o : Outcome} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {k v : B256} {ks : List B256},
    w.Ready b (k :: ks) → sevm.isStatic = false → gCallStipend < G + w.writeCost b k v →
    SFunc.RunExact fs sevm (St (w.afterWrite b k v) S M G) f o →
    SFunc.RunExact fs sevm (St b (k :: v :: S) M (G + w.writeCost b k v)) (.next (.reg .sstore) f) o

/-- What these stores keep, on any fork: readiness moves along the frame's reads and writes, a write
writes its slot, and a ready frame has no error and a nonnegative refund counter. -/
structure Laws : Prop where
  write : ∀ {b : Devm} {k : B256} {ks : List B256}, w.Ready b (k :: ks) → k ∉ ks → ∀ v,
    w.Ready (w.afterWrite b k v) ks
  skip : ∀ {b : Devm} {k k' : B256} {ks : List B256}, w.Ready b (k :: k' :: ks) → w.Ready b (k :: ks)
  read : ∀ {b : Devm} {ks : List B256}, w.Ready b ks → ∀ k, w.Ready (afterSloadA sevm b k) ks
  state : ∀ b k v, (w.afterWrite b k v).state = b.state.setStorVal sevm.currentTarget k v
  error : ∀ {b : Devm} {ks : List B256}, w.Ready b ks → b.error = none
  refund : ∀ {b : Devm} {ks : List B256}, w.Ready b ks → 0 ≤ b.refundCounter
  cost_le : ∀ b k v, w.writeCost b k v ≤ w.writeMax

variable {w}

theorem Laws.reads (l : w.Laws) {b : Devm} {ks : List B256} (r : w.Ready b ks) (keys : List B256) :
    w.Ready (readsBase sevm b keys) ks := by
  induction keys generalizing b with
  | nil => exact r
  | cons k rest ih => exact ih (l.read r k)

end SysStores

/-! ## Amsterdam -/

/-- Amsterdam's state-gas record. -/
local notation "A" => amsterdamStateGasRules

/-- Amsterdam's stores on a system frame: execution gas from `gasLeft`, state gas from the reservoir. -/
def amsterdamStores (sevm : Sevm) : SysStores sevm where
  afterWrite := afterSstoreA A sevm
  writeCost := sstoreCostA A sevm
  writeMax := gasColdSload + amsterdamStateGasRules.storageWrite
  Ready := Ready sevm

theorem amsterdamStores_runs {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = some A) :
    (amsterdamStores sevm).Runs :=
  fun r hstatic hG k => rx_sstoreR hsg hstatic r hG k

theorem amsterdamStores_laws (sevm : Sevm) : (amsterdamStores sevm).Laws where
  write := fun r fresh v => r.sstore fresh v
  skip := fun r => r.skip
  read := fun r k => r.sload k
  state := afterSstoreA_state A sevm
  error := fun r => r.error
  refund := fun r => r.refund
  cost_le := fun b k v => (sstoreCostA_le A sevm b k v :)

/-! ## The covered forks -/

/-- What a covered-fork frame carries to its remaining stores: no error, a nonnegative refund counter,
and every remaining slot unchanged in this transaction or originally zero. -/
structure CoveredReady (sevm : Sevm) (d : Devm) (keys : List B256) : Prop where
  error : d.error = none
  refund : 0 ≤ d.refundCounter
  clean : ∀ k ∈ keys, SlotClean sevm d k

/-- The covered forks' stores: no state gas, the selected `SSTORE` charge. -/
def coveredStores (sevm : Sevm) : SysStores sevm where
  afterWrite := afterSstore sevm
  writeCost := sstoreCost sevm
  writeMax := gasColdSload + gasStorageSet
  Ready := CoveredReady sevm

theorem coveredStores_runs {sevm : Sevm} (fork : CoveredFork sevm.benvStat.fork) :
    (coveredStores sevm).Runs :=
  fun _ hstatic hG k => rx_sstore fork hG hstatic k

theorem coveredStores_laws (sevm : Sevm) : (coveredStores sevm).Laws where
  write := fun {d k ks} r fresh v => {
    error := (afterSstore_error sevm d k v).trans r.error
    refund := by
      show 0 ≤ (afterSstore sevm d k v).refundCounter
      have hc := r.clean k List.mem_cons_self
      have safe : RefundSafe (d.getOrigStorVal sevm sevm.currentTarget k)
          (d.getStorVal sevm.currentTarget k) := by
        rcases hc with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      exact Int.le_trans r.refund (afterSstore_refundCounter_ge_of_safe sevm d k v safe)
    clean := fun k' hk' => by
      have hne : k ≠ k' := fun e => fresh (e ▸ hk')
      show SlotClean sevm (afterSstore sevm d k v) k'
      unfold SlotClean
      have hval : (afterSstore sevm d k v).getStorVal sevm.currentTarget k' =
          d.getStorVal sevm.currentTarget k' := by
        unfold Devm.getStorVal Devm.getAcct
        rw [afterSstore_state]
        show ((d.state.setStorVal sevm.currentTarget k v).getStor sevm.currentTarget).get k' =
          (d.state.getStor sevm.currentTarget).get k'
        rw [State.getStor_setStorVal_self, Stor.get_set_ne _ hne]
      rw [getOrigStorVal_congr_created (d2 := d) _ _ (afterSstore_createdAccounts sevm d k v), hval]
      exact r.clean k' (List.mem_cons_of_mem _ hk') }
  skip := fun r => {
    error := r.error
    refund := r.refund
    clean := fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact r.clean _ List.mem_cons_self
      · exact r.clean _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)) }
  read := fun {d _} r k => {
    error := (afterSloadA_error sevm d k).trans r.error
    refund := by rw [afterSloadA_refundCounter]; exact r.refund
    clean := fun k' hk' => by
      unfold SlotClean
      rw [afterSloadA_getOrig, afterSloadA_getStorVal]
      exact r.clean k' hk' }
  state := afterSstore_state sevm
  error := fun r => r.error
  refund := fun r => r.refund
  cost_le := fun d k v => by
    have h1 := sstoreCost_le_value sevm d k v
    have h2 := sstoreValueCost_le (d.getOrigStorVal sevm sevm.currentTarget k)
      (d.getStorVal sevm.currentTarget k) v
    show sstoreCost sevm d k v ≤ gasColdSload + gasStorageSet
    omega

end Blanc.Lift.RequestSystem
