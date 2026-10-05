import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Clone.Cert
import Blanc.Lift.Deploy
import Blanc.Lift.CreationOps
import Blanc.Lift.ExactWalkCutOps
import Blanc.BytesWrite

/-! Gas-exact certified walk of the synthetic clone copier, stopping at its actual `RETURN`
of the 45-byte forwarder to `0x847e`. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Clone

open Jaune Blanc.Lift

/-- The forwarder runtime's bytes. -/
abbrev forwarder : List UInt8 := (Blanc.forwarderCode Blanc.curvePlainImpl847e).data.toList

theorem forwarder_length : forwarder.length = 45 := rfl

theorem forwarder_head : forwarder.head? = some 0x36 := rfl

/-- **The copy window is the forwarder to `0x847e`**: `clone[9, 54)`. -/
theorem forwarder_window : cloneCreationCode.sliceD 9 45 0 = forwarder := by
  rw [ByteArray.sliceD_eq, cloneCreationCode, ByteArray.toList_eq_toList_data,
    List.toList_toArray]
  have hp : copier.length = 9 := rfl
  rw [← hp, ← forwarder_length]
  simpa only [List.append_nil] using Bytes.sliceD_append_middle copier forwarder []

def cloneMemory : Mem := Mem.empty.write 0 forwarder

theorem cloneMemory_size : cloneMemory.size = 64 := by
  rw [cloneMemory, Mem.size_write_of_size rfl (by decide) forwarder_length]
  rfl

theorem cloneMemory_read : (cloneMemory.read 0 45).1 = forwarder := by
  rw [← forwarder_length]
  exact Mem.read_write_zero Mem.empty (List.ne_nil_of_length_pos (by rw [forwarder_length]; decide))

/-- The state the copier returns from. -/
def clonePost (b : Devm) (G : Nat) : Devm :=
  returnPost (St b [0, 45] cloneMemory G) 0 45 []

theorem clone_codecopy_charge (b : Devm) (G : Nat) :
    gVerylow + gasCopy * ceilDiv (45 : B256).toNat 32 +
      (St b [0, 9, 45, 0, 45] Mem.empty (G + 15)).extCost [⟨0, 45⟩] = 15 := by
  rw [St.extCost_eq rfl]
  rfl

theorem clone_return_charge (b : Devm) (G : Nat) :
    (St b [0, 45] cloneMemory G).extCost [⟨0, 45⟩] = 0 := by
  rw [St.extCost_eq cloneMemory_size]
  rfl

theorem clonePost_facts (b : Devm) (G : Nat) :
    (clonePost b G).output = forwarder ∧ (clonePost b G).error = b.error ∧
    (clonePost b G).state = b.state ∧ (clonePost b G).gasLeft = G := by
  have h := returnPost_facts (St b [0, 45] cloneMemory G) 0 45 []
  refine ⟨?_, h.2.1, rfl, h.2.2.2⟩
  unfold clonePost
  rw [h.1]
  have e0 : (0 : B256).toNat = 0 := rfl
  have e1 : (45 : B256).toNat = 45 := rfl
  rw [St.memory, e0, e1]
  exact cloneMemory_read

abbrev prog : List SFunc := cert.prog

theorem jumps_ok : Cert.jumpsOk code cert = true := by
  rfl

/-- The copier: `PUSH1 45`, `RETURNDATASIZE` (zero in a fresh frame), `DUP2`, `PUSH1 9`,
`RETURNDATASIZE`, `CODECOPY(0, 9, 45)`, `RETURN(0, 45)`; 28 gas. -/
theorem clone_run (sevm : Sevm) (b : Devm) (G : Nat) (hcode : sevm.code = cloneCreationCode)
    (hrd : b.returnData = []) :
    SProg.RunExact prog sevm (St b [] Mem.empty (G + 28)) (clonePost b G) := by
  refine ⟨t_0000_c0, rfl, ?_⟩
  have hgas : G + 28 = (((((G + 15) + 2) + 3) + 3) + 2) + 3 := by omega
  have hz : b.returnData.length.toB256 = 0 := by rw [hrd]; rfl
  rw [hgas]
  unfold t_0000_c0
  refine rx_push (w := (45 : B256)) rfl (by decide) ?_
  refine rx_returndatasize (by decide) ?_
  rw [hz]
  refine rx_dup (n := 1) (w := 45) rfl (by decide) ?_
  refine rx_push (w := (9 : B256)) rfl (by decide) ?_
  refine rx_returndatasize (by decide) ?_
  rw [hz]
  refine rx_codecopy (c := 15) (M' := cloneMemory) ?_ ?_ ?_
  · exact clone_codecopy_charge _ _
  · rw [hcode]
    change Mem.empty.write 0 (cloneCreationCode.sliceD 9 45 0) = cloneMemory
    rw [forwarder_window]
    rfl
  · exact rx_return_any rfl (clone_return_charge _ _)

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Clone
