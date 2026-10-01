import Blanc.Lift.ExactWalkMemory
import Blanc.Lift.WalkSteps
import Blanc.Lift.Deploy

/-! Actual memory and terminal images for the Pair's getter wrappers. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def getterInitMemory : Mem := Mem.empty.write 64 (128 : B256).toBytes

theorem getterInitMemory_ptr : PtrMem 128 96 getterInitMemory := PtrMem.init 128

def getterWordPost (b : Devm) (R : List B256) (M : Mem) (v : B256) (G : Nat) : Devm :=
  returnPost (St b (128 :: 32 :: R) (M.write 128 v.toBytes) G) 128 32 R

theorem getterWordMemory_ptr {M : Mem} (h : PtrMem 128 96 M) (v : B256) :
    PtrMem 128 160 (M.write 128 v.toBytes) := by
  have h' := h.write 128 v (Or.inr (by decide))
  have hs : memExtSize 96 128 32 = 160 := by decide
  rw [hs] at h'
  exact h'

theorem getterWordPost_facts {b : Devm} {R : List B256} {M : Mem} {v : B256} {G : Nat}
    (h : Mem.Wf M) :
    (getterWordPost b R M v G).output = v.toBytes ∧
      (∀ a, Devm.getStor (getterWordPost b R M v G) a = Devm.getStor b a) ∧
      (getterWordPost b R M v G).logs = b.logs ∧
      (getterWordPost b R M v G).gasLeft = G := by
  refine ⟨?_, fun _ => rfl, rfl, rfl⟩
  exact Mem.read_write_word_of_wf h 128 v

end Blanc.Lift.UniswapV2Pair
