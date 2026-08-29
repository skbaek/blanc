import Blanc.BeaconDepositEventMemory

/-!
# Beacon deposit guard memory

The successful value guards retain the amount in gwei at byte offset 672.
This carrier transition isolates that expanding `MSTORE` from the compiled
guard walk.
-/

namespace Blanc.BeaconDeposit

open Jaune

/-- Writing the retained amount turns any decoded-memory carrier into the
event-staging input carrier. -/
def DepositDecodedMemoryCarrier.writeAmount
    {memory : Mem} {data : Bytes} (h : DepositDecodedMemoryCarrier memory data)
    (amount : B256) :
    DepositEventInputMemoryCarrier
      (memory.write 672 amount.toBytes) data amount := by
  let image := Bytes.writeAt h.image 672 amount.toBytes
  have hwf : Mem.Wf (memory.write 672 amount.toBytes) := h.wf.write _ _
  have hreads : Mem.Reads (memory.write 672 amount.toBytes) image := by
    exact Mem.Reads.write h.wf h.reads _ _
  have hsize : (memory.write 672 amount.toBytes).size = 704 := by
    rw [Mem.size_write_word_at, h.size_eq]
    decide +kernel
  have hlen : image.length = 704 := by
    dsimp only [image]
    rw [Bytes.length_writeAt, h.image_length, B256.length_toBytes]
    decide +kernel
  have hoffset0 : image.sliceD 0 32 0 =
      (depositOffsetWord data 0).toBytes := by
    dsimp only [image]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.offset0_read
  have hoffset1 : image.sliceD 32 32 0 =
      (depositOffsetWord data 1).toBytes := by
    dsimp only [image]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.offset1_read
  have hoffset2 : image.sliceD 64 32 0 =
      (depositOffsetWord data 2).toBytes := by
    dsimp only [image]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.offset2_read
  have hamount : image.sliceD 672 32 0 = amount.toBytes := by
    dsimp only [image]
    rw [show 32 = amount.toBytes.length by rw [B256.length_toBytes]]
    exact Bytes.sliceD_writeAt _ _ _
  exact ⟨image, hwf, hreads, hsize, by rw [hsize], hlen,
    hoffset0, hoffset1, hoffset2, hamount⟩

end Blanc.BeaconDeposit
