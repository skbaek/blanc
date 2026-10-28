import Blanc.Lift.Usdc.ImplV2_1Creation.SigningData0
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningData1
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningData2
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningData3
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningData4
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningData5

/-! Bounded byte comparisons tie every literal block to the original code. -/
namespace Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
open Jaune

private def data : Bytes :=
  [0xf9, 0x54, 0x62, 0x26, 0x85, 0x1e, 0x44, 0x9a, 0x94, 0x00, 0x83, 0x53, 0xec, 0x60, 0x80, 0x80, 0xb9, 0x54, 0x52] ++ code.data.toList

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
  simp only [List.drop_zero]
  conv_lhs => rw [← List.take_append_drop 4080 data]
  apply congrArg (fun rest => data.take 4080 ++ rest)
  conv_lhs => rw [← List.take_append_drop 4080 (data.drop 4080)]
  simp only [List.drop_drop, Nat.reduceAdd]
  apply congrArg (fun rest => (data.drop 4080).take 4080 ++ rest)
  conv_lhs => rw [← List.take_append_drop 4080 (data.drop 8160)]
  simp only [List.drop_drop, Nat.reduceAdd]
  apply congrArg (fun rest => (data.drop 8160).take 4080 ++ rest)
  conv_lhs => rw [← List.take_append_drop 4080 (data.drop 12240)]
  simp only [List.drop_drop, Nat.reduceAdd]
  apply congrArg (fun rest => (data.drop 12240).take 4080 ++ rest)
  conv_lhs => rw [← List.take_append_drop 4080 (data.drop 16320)]
  simp only [List.drop_drop, Nat.reduceAdd]

end Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
