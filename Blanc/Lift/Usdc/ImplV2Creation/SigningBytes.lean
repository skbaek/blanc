import Blanc.Lift.Usdc.ImplV2Creation.SigningData0
import Blanc.Lift.Usdc.ImplV2Creation.SigningData1
import Blanc.Lift.Usdc.ImplV2Creation.SigningData2
import Blanc.Lift.Usdc.ImplV2Creation.SigningData3
import Blanc.Lift.Usdc.ImplV2Creation.SigningData4
import Blanc.Lift.Usdc.ImplV2Creation.SigningData5

/-! Bounded byte comparisons tie every literal block to the original code. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune

private def data : Bytes :=
  [0xf9, 0x5a, 0xe0, 0x1f, 0x85, 0x22, 0xec, 0xb2, 0x5c, 0x00, 0x83, 0x4f, 0x58, 0x80, 0x80, 0x80, 0xb9, 0x5a, 0xd0] ++ code.data.toList

private theorem payload_data : signingPayload = data := by
  unfold signingPayload data
  rw [ByteArray.toList_eq_toList_data]

private theorem part0 : (data.drop 0).take 4080 = segment0 := by
  have checked : ((data.drop 0).take 4080 == segment0) = true := by
    decide +kernel
  exact eq_of_beq checked

private theorem part1 : (data.drop 4080).take 4080 = segment1 := by
  have checked : ((data.drop 4080).take 4080 == segment1) = true := by
    decide +kernel
  exact eq_of_beq checked

private theorem part2 : (data.drop 8160).take 4080 = segment2 := by
  have checked : ((data.drop 8160).take 4080 == segment2) = true := by
    decide +kernel
  exact eq_of_beq checked

private theorem part3 : (data.drop 12240).take 4080 = segment3 := by
  have checked : ((data.drop 12240).take 4080 == segment3) = true := by
    decide +kernel
  exact eq_of_beq checked

private theorem part4 : (data.drop 16320).take 4080 = segment4 := by
  have checked : ((data.drop 16320).take 4080 == segment4) = true := by
    decide +kernel
  exact eq_of_beq checked

private theorem part5 : data.drop 20400 = segment5 := by
  have checked : (data.drop 20400 == segment5) = true := by
    decide +kernel
  exact eq_of_beq checked

theorem payload_split : signingPayload =
    segment0 ++ (segment1 ++ (segment2 ++ (segment3 ++ (segment4 ++ (segment5))))) := by
  rw [payload_data]
  have split (k : Nat) :
      (data.drop k).take 4080 ++ data.drop (k + 4080) = data.drop k := by
    simpa only [List.drop_drop] using List.take_append_drop 4080 (data.drop k)
  have assembled :
      (data.drop 0).take 4080 ++ ((data.drop 4080).take 4080 ++ ((data.drop 8160).take 4080 ++ ((data.drop 12240).take 4080 ++ ((data.drop 16320).take 4080 ++ (data.drop 20400))))) = data := by
    rw [split 16320, split 12240, split 8160, split 4080, split 0]
    rfl
  rw [← assembled, part0, part1, part2, part3, part4, part5]

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
