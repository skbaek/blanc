import Blanc.Lift.ExactWalkMemory
import Blanc.Lift.WalkSteps

/-!
# Free-pointer word without a tracked allocation size

`PtrWord p M` keeps only `Mem.Wf M` and the free-pointer word at offset64. It is the
size-free companion of `PtrMem p n M` for walks whose allocation grows by unbounded
replies (a moved free pointer after a full-returndata copy): writes at or above
offset96, read extensions and pointer replacement preserve it, without a size bound.
-/

namespace Blanc.Lift
open Jaune

/-- A well-formed memory whose free-pointer word reads `p`; no allocation size is tracked. -/
def PtrWord (p : B256) (M : Mem) : Prop :=
  Mem.Wf M ∧ Bytes.toB256 (M.read 64 32).1 = p

theorem PtrWord.of_ptrMem {p : B256} {n : Nat} {M : Mem} (h : PtrMem p n M) : PtrWord p M :=
  ⟨h.wf, h.word⟩

theorem PtrWord.set {p : B256} {M : Mem} (h : PtrWord p M) (q : B256) :
    PtrWord q (M.write 64 q.toBytes) := by
  refine ⟨h.1.write _ _, ?_⟩
  rw [(Mem.reads_data M |>.write h.1 64 q.toBytes).read, Bytes.readWord_writeAt_self]

theorem PtrWord.extends {p : B256} {M : Mem} (h : PtrWord p M) (pairs : List (Nat × Nat)) :
    PtrWord p (M.extends pairs) := by
  refine ⟨h.1.extends pairs, ?_⟩
  rw [((Mem.reads_data M).extends pairs).read, ← (Mem.reads_data M).read]
  exact h.2

end Blanc.Lift
