import Blanc.Lift.Curve3Pool.Walk.Kit
import Blanc.Lift.ExactWalk
import Blanc.Lift.ExactWalkOps
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.CreationOps

/-!
# Forward walks over a memory image, with exact gas

The forward twins of the image-carrier steps: the memory is an opaque `M` with
`Mem.Reads M img`, `Mem.Wf M` and its word-aligned size `M.size = s`; each memory step names its
cost, and a write hands its continuation the new memory with the written image and size.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- A stack-room side condition over a literal stack. -/
macro "hr" : tactic => `(tactic| (simp only [List.length_cons, List.length_nil]; omega))

section Fwd

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f : SFunc} {r : Outcome} {img : Bytes}

/-- `MSTORE` over the image carrier. -/
theorem rxm_mstore {i v : B256} {o s c : Nat} (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = s) (ho : i.toNat = o)
    (hc : gVerylow + (calculateMemoryGasCost (memExtSize s o 32) - calculateMemoryGasCost s) = c ∧
      s % 32 = 0)
    (k : ∀ M', Mem.Reads M' (Bytes.writeAt img o v.toBytes) → Mem.Wf M' →
      M'.size = memExtSize s o 32 → SFunc.RunExact fs sevm (St b S M' G) f r) :
    SFunc.RunExact fs sevm (St b (i :: v :: S) M (G + c)) (.next (.reg .mstore) f) r := by
  subst ho
  refine rx_mstore (M' := M.write i.toNat v.toBytes) ?_ rfl
    (k _ (hR.write hW _ _) (hW.write _ _) (Mem.size_write_of_size hsz hc.2 (B256.length_toBytes _)))
  rw [St.extCost_eq hsz]; exact hc.1

/-- `MLOAD` of a window the memory covers. -/
theorem rxm_mload {i : B256} {o s : Nat} (hR : Mem.Reads M img) (hsz : M.size = s)
    (ho : i.toNat = o) (hin : o + 32 ≤ s ∧ s % 32 = 0) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (Bytes.toB256 (img.sliceD o 32 0) :: S) M G) f r) :
    SFunc.RunExact fs sevm (St b (i :: S) M (G + 3)) (.next (.reg .mload) f) r := by
  subst ho
  refine rx_mload (c := 3) ?_ (by rw [hR.read]) (read_covered hsz hin.2 hin.1) hroom k
  rw [St.extCost_eq hsz, memExtSize_of_le hin.2 hin.1, Nat.sub_self]
  rfl

/-- `KECCAK256` of a window the memory covers. -/
theorem rxm_keccak {i sz : B256} {o z s : Nat} (hR : Mem.Reads M img) (hsz : M.size = s)
    (ho : i.toNat = o) (hz : sz.toNat = z) (hin : o + z ≤ s ∧ s % 32 = 0)
    (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (Bytes.keccak (img.sliceD o z 0) :: S) M G) f r) :
    SFunc.RunExact fs sevm (St b (i :: sz :: S) M (G + (30 + 6 * ceilDiv z 32)))
      (.next (.reg .keccak256) f) r := by
  subst ho hz
  refine rx_keccak ?_ (by rw [hR.read]) (read_covered_len hsz hin.2 hin.1) hroom k
  rw [St.extCost_eq hsz, memExtSize_of_le hin.2 hin.1, Nat.sub_self, Nat.add_zero]
  rfl

/-- `CALLDATACOPY` over the image carrier. -/
theorem rxm_calldatacopy {di si sz : B256} {o z s c : Nat} (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = s) (ho : di.toNat = o) (hz : sz.toNat = z)
    (hc : gVerylow + gasCopy * ceilDiv z 32 +
      (calculateMemoryGasCost (memExtSize s o z) - calculateMemoryGasCost s) = c ∧ s % 32 = 0)
    (k : ∀ M', Mem.Reads M' (Bytes.writeAt img o (sevm.data.sliceD si.toNat z 0)) → Mem.Wf M' →
      M'.size = memExtSize s o z → SFunc.RunExact fs sevm (St b S M' G) f r) :
    SFunc.RunExact fs sevm (St b (di :: si :: sz :: S) M (G + c))
      (.next (.reg .calldatacopy) f) r := by
  subst ho hz
  refine rx_calldatacopy (M' := M.write di.toNat (sevm.data.sliceD si.toNat sz.toNat 0)) ?_ rfl
    (k _ (hR.write hW _ _) (hW.write _ _)
      (Mem.size_write_of_size hsz hc.2 (List.length_sliceD _ _ _ _)))
  rw [St.extCost_eq hsz]; exact hc.1

end Fwd

end Blanc.Lift.Curve3Pool
