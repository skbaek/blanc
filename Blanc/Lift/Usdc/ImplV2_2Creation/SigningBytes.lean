import Blanc.Lift.Usdc.ImplV2_2Creation.SigningData0
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningData1
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningData2
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningData3
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningData4
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningData5

/-! Bounded byte comparisons tie every literal block to the original code. -/
namespace Blanc.Lift.Usdc.ImplV2_2Creation.SigningBlocks
open Jaune

private def data : Bytes :=
  [0xf9, 0x5c, 0x22, 0x01, 0x85, 0x05, 0x1f, 0x4d, 0x5c, 0x00, 0x83, 0xe4, 0xe1, 0xc0, 0x80, 0x80, 0xb9, 0x5c, 0x0f] ++ code.data.toList ++ [0x01, 0x80, 0x80]

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
  rw [payload_data, ← part0, ← part1, ← part2, ← part3, ← part4, ← part5]
  rw [List.drop_take_append_drop data 16320 4080, List.drop_take_append_drop data 12240 4080, List.drop_take_append_drop data 8160 4080, List.drop_take_append_drop data 4080 4080, List.drop_take_append_drop data 0 4080]
  rfl

end Blanc.Lift.Usdc.ImplV2_2Creation.SigningBlocks
