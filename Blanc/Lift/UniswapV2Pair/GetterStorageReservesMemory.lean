import Blanc.Lift.UniswapV2Pair.GetterStorageDispatch

/-! The packed reserve wrapper's actual ordered return-memory stages. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def getterReservesMemory1 (M : Mem) (r0 : B256) : Mem := M.write 128 r0.toBytes
def getterReservesMemory2 (M : Mem) (r0 r1 : B256) : Mem :=
  (getterReservesMemory1 M r0).write 160 r1.toBytes
def getterReservesMemory (M : Mem) (r0 r1 ts : B256) : Mem :=
  (getterReservesMemory2 M r0 r1).write 192 ts.toBytes

theorem getterReservesMemory1_ptr {M : Mem} (mem : PtrMem 128 96 M) (r0 : B256) :
    PtrMem 128 160 (getterReservesMemory1 M r0) := by
  have h := mem.write 128 r0 (Or.inr (by decide))
  rw [show memExtSize 96 128 32 = 160 from by decide] at h
  exact h

theorem getterReservesMemory2_ptr {M : Mem} (mem : PtrMem 128 96 M) (r0 r1 : B256) :
    PtrMem 128 192 (getterReservesMemory2 M r0 r1) := by
  have h := (getterReservesMemory1_ptr mem r0).write 160 r1 (Or.inr (by decide))
  rw [show memExtSize 160 160 32 = 192 from by decide] at h
  exact h

theorem getterReservesMemory_ptr {M : Mem} (mem : PtrMem 128 96 M) (r0 r1 ts : B256) :
    PtrMem 128 224 (getterReservesMemory M r0 r1 ts) := by
  have h := (getterReservesMemory2_ptr mem r0 r1).write 192 ts (Or.inr (by decide))
  rw [show memExtSize 192 192 32 = 224 from by decide] at h
  exact h

def getterReservesImage (M : Mem) (r0 r1 ts : B256) : Bytes :=
  (MemoryStage.words [(128, r0), (160, r1), (192, ts)]).applyImage M.data.toList

theorem getterReservesImage_read (M : Mem) (r0 r1 ts : B256) :
    (getterReservesImage M r0 r1 ts).sliceD 128 96 0 = encodeWords [r0, r1, ts] := by
  unfold getterReservesImage
  have h0 := MemoryStage.read_written_word [] [(160, r1), (192, ts)] M.data.toList 128 r0 (by
    simp only [MemoryStage.words, List.map_cons, List.map_nil, MemoryStage.avoids,
      List.all_cons, List.all_nil, B256.length_toBytes]
    rfl)
  have h1 := MemoryStage.read_written_word [(128, r0)] [(192, ts)] M.data.toList 160 r1 (by
    simp only [MemoryStage.words, List.map_cons, List.map_nil, MemoryStage.avoids,
      List.all_cons, List.all_nil, B256.length_toBytes]
    rfl)
  have ht := MemoryStage.read_written_word [(128, r0), (160, r1)] [] M.data.toList 192 ts rfl
  simp only [List.cons_append, List.nil_append] at h0 h1 ht
  rw [show (96 : Nat) = 32 + (32 + 32) from rfl, List.sliceD_add, List.sliceD_add]
  rw [h0, h1, ht]
  simp only [encodeWords, List.flatMap_cons, List.flatMap_nil, List.append_nil]

def getterReservesPost (b : Devm) (R : List B256) (M : Mem) (r0 r1 ts : B256)
    (G : Nat) : Devm :=
  returnPost (St b (128 :: 96 :: R) (getterReservesMemory M r0 r1 ts) G) 128 96 R

theorem getterReservesPost_facts {b : Devm} {R : List B256} {M : Mem}
    {r0 r1 ts : B256} {G : Nat} (mem : PtrMem 128 96 M) :
    (getterReservesPost b R M r0 r1 ts G).output = encodeWords [r0, r1, ts] ∧
      (∀ a, Devm.getStor (getterReservesPost b R M r0 r1 ts G) a = Devm.getStor b a) ∧
      (getterReservesPost b R M r0 r1 ts G).logs = b.logs ∧
      (getterReservesPost b R M r0 r1 ts G).gasLeft = G := by
  refine ⟨?_, fun _ => rfl, rfl, rfl⟩
  have reads := (MemoryStage.wf_reads (MemoryStage.words [(128, r0), (160, r1), (192, ts)])
    mem.wf (Mem.reads_data M)).2
  change Mem.Reads (getterReservesMemory M r0 r1 ts) (getterReservesImage M r0 r1 ts) at reads
  rw [getterReservesPost, (returnPost_facts
    (St b (128 :: 96 :: R) (getterReservesMemory M r0 r1 ts) G) 128 96 R).1]
  simp only [St.memory, show (128 : B256).toNat = 128 from rfl,
    show (96 : B256).toNat = 96 from rfl]
  rw [reads.read]
  exact getterReservesImage_read M r0 r1 ts

end Blanc.Lift.UniswapV2Pair
