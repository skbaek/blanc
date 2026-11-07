import Blanc.Lift.BuilderRequest.UserFrame
import Blanc.Lift.AmsterdamWalk

/-!
# What the builder contracts' submissions share, under Amsterdam

The forward steps of a submission when the fork carries a state-gas record: `SLOAD` with its read record,
`SSTORE` drawing on the reservoir, and the shared tail. `Room` is the premise a frame carries: no spill, and
room for its stores. Prices are read from the rule record.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune

/-- Amsterdam's state-gas record. -/
local notation "A" => amsterdamStateGasRules

variable {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}

/-- Amsterdam's `SLOAD`. -/
def amsterdamLane (hfork : sevm.benvStat.fork = .amsterdam) : SloadLane sevm where
  after := afterSloadA sevm
  push0 := amsterdam_push0 hfork
  read := afterSloadA_getStorVal sevm
  run := fun hroom k => rx_sloadA (amsterdam_access hfork) hroom k

/-- After the count bump. -/
def countStoreA (sevm : Sevm) (b : Devm) : Devm :=
  afterSstoreA A sevm (afterSloadA sevm b 1) 1 (1 + countWord sevm b)

/-- The tail word the path reads, after the count bump. -/
def tailWordA (sevm : Sevm) (b : Devm) : B256 := (countStoreA sevm b).getStorVal sevm.currentTarget 3

/-- After reading the tail. -/
def tailReadA (sevm : Sevm) (b : Devm) : Devm := afterSloadA sevm (countStoreA sevm b) 3

/-- A frame with no spill and room in the reservoir for `n` stores. -/
structure Room (d : Devm) (n : Nat) : Prop where
  spill : d.stateGas.spilled = 0
  left : n * amsterdamStateGasRules.storageSet ≤ d.stateGas.left

theorem Room.sload {d : Devm} {n : Nat} (r : Room d n) (k : B256) : Room (afterSloadA sevm d k) n :=
  ⟨by rw [afterSloadA_stateGas]; exact r.spill, by rw [afterSloadA_stateGas]; exact r.left⟩

theorem Room.sstore {d : Devm} {n : Nat} (r : Room d (n + 1)) (k v : B256) :
    Room (afterSstoreA A sevm d k v) n := by
  have hl := r.left
  rw [Nat.add_mul, Nat.one_mul] at hl
  have h := afterSstoreA_meter A (sevm := sevm) (k := k) (v := v) r.spill hl
  exact ⟨h.1, h.2⟩

theorem Room.log {d : Devm} {n : Nat} (r : Room d n) (l : Log) : Room (d.addLog l) n :=
  ⟨r.spill, r.left⟩

/-- `SSTORE` from a frame with room. -/
theorem rx_sstoreRoom {fs : List SFunc} {f : SFunc} {S : List B256} {k v : B256} {n : Nat}
    (hfork : sevm.benvStat.fork = .amsterdam) (dynamic : sevm.isStatic = false)
    (r : Room b (n + 1)) (hsentry : gCallStipend < G + sstoreCostA A sevm b k v)
    (next : SFunc.RunExact fs sevm (St (afterSstoreA A sevm b k v) S M G) f o) :
    SFunc.RunExact fs sevm (St b (k :: v :: S) M (G + sstoreCostA A sevm b k v))
      (.next (.reg .sstore) f) o := by
  refine rx_sstoreA (amsterdam_stateGas hfork) hsentry dynamic r.spill ?_ next
  have hc := sstoreChargeA_le A sevm b k v
  have hl := r.left
  rw [Nat.add_mul, Nat.one_mul] at hl
  omega

/-- `LOG0`, bump the tail, `STOP`, under Amsterdam. -/
theorem logTail_exactA {fs : List SFunc} {n tail : B256} (hfork : sevm.benvStat.fork = .amsterdam)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G) (r : Room b 1) :
    SFunc.RunExact fs sevm
      (St b [0, n, tail] M
        (G + sstoreCostA A sevm (b.addLog (windowLog sevm M n.toNat)) 3 (1 + tail) + 3 + 3 + 3 +
          log0Gas M n.toNat))
      logTail
      (.halted (St (afterSstoreA A sevm (b.addLog (windowLog sevm M n.toNat)) 3 (1 + tail)) []
        (M.read 0 n.toNat).2 G)) := by
  have emitted : Ninst.RunCompiled sevm
      (St b [0, n, tail] M
        (G + sstoreCostA A sevm (b.addLog (windowLog sevm M n.toNat)) 3 (1 + tail) + 3 + 3 + 3 +
          log0Gas M n.toNat)) (.reg (.log 0))
      (St (b.addLog (windowLog sevm M n.toNat)) [tail] (M.read 0 n.toNat).2
        (G + sstoreCostA A sevm (b.addLog (windowLog sevm M n.toNat)) 3 (1 + tail) + 3 + 3 + 3)) :=
    Ninst.runCompiled_log_of (n := 0) (i := 0) (sz := n) (topics := []) (s := [tail])
      rfl rfl dynamic (Devm.extCost_add_of_size rfl rfl) rfl rfl rfl
  unfold logTail
  refine .next emitted ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_add' rfl (by decide) ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_sstoreRoom (n := 0) hfork dynamic (r.log _) (by omega) ?_
  exact .last rfl

/-- `Room` can be met: from any machine, one whose reservoir holds `n` stores. -/
theorem Room.satisfiable (d : Devm) (n : Nat) : ∃ d' : Devm, Room d' n :=
  ⟨d.setMach { d.mach with stateGas := { d.stateGas with spilled := 0, left := n * amsterdamStateGasRules.storageSet } },
    ⟨rfl, Nat.le_refl _⟩⟩

end Blanc.Lift.BuilderRequest
