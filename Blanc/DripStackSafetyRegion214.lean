import Blanc.DripStackSafety

/-!
Checked first 183-row region of the DRIP stack table. The first 91 rows are
imported from the prior checkpoint; every successor check uses the full table.
-/

namespace Blanc.Drip.StackSafety

open Jaune AbstractStackSafety

theorem subtree222_rows_checked :
    subtree222.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree222_layout_checked :
    subtree222.checkLayout code.toByteArray 217 231 = true := by
  decide +kernel

theorem subtree239_rows_checked :
    subtree239.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree239_layout_checked :
    subtree239.checkLayout code.toByteArray 232 250 = true := by
  decide +kernel

theorem subtree264_rows_checked :
    subtree264.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree264_layout_checked :
    subtree264.checkLayout code.toByteArray 251 270 = true := by
  decide +kernel

theorem subtree278_rows_checked :
    subtree278.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree278_layout_checked :
    subtree278.checkLayout code.toByteArray 271 286 = true := by
  decide +kernel

theorem subtree293_rows_checked :
    subtree293.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree293_layout_checked :
    subtree293.checkLayout code.toByteArray 287 316 = true := by
  decide +kernel

theorem subtree328_rows_checked :
    subtree328.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree328_layout_checked :
    subtree328.checkLayout code.toByteArray 319 333 = true := by
  decide +kernel

theorem subtree345_rows_checked :
    subtree345.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree345_layout_checked :
    subtree345.checkLayout code.toByteArray 334 357 = true := by
  decide +kernel

theorem subtree365_rows_checked :
    subtree365.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree365_layout_checked :
    subtree365.checkLayout code.toByteArray 358 371 = true := by
  decide +kernel

theorem subtree231_rows_checked :
    subtree231.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree222_rows_checked
  · exact subtree239_rows_checked

theorem subtree231_layout_checked :
    subtree231.checkLayout code.toByteArray 217 250 = true := by
  apply Table.checkLayout_node (next := 232)
  · decide +kernel
  · exact subtree222_layout_checked
  · exact subtree239_layout_checked
  · decide +kernel

theorem subtree270_rows_checked :
    subtree270.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree264_rows_checked
  · exact subtree278_rows_checked

theorem subtree270_layout_checked :
    subtree270.checkLayout code.toByteArray 251 286 = true := by
  apply Table.checkLayout_node (next := 271)
  · decide +kernel
  · exact subtree264_layout_checked
  · exact subtree278_layout_checked
  · decide +kernel

theorem subtree250_rows_checked :
    subtree250.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree231_rows_checked
  · exact subtree270_rows_checked

theorem subtree250_layout_checked :
    subtree250.checkLayout code.toByteArray 217 286 = true := by
  apply Table.checkLayout_node (next := 251)
  · decide +kernel
  · exact subtree231_layout_checked
  · exact subtree270_layout_checked
  · decide +kernel

theorem subtree316_rows_checked :
    subtree316.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree293_rows_checked
  · exact subtree328_rows_checked

theorem subtree316_layout_checked :
    subtree316.checkLayout code.toByteArray 287 333 = true := by
  apply Table.checkLayout_node (next := 319)
  · decide +kernel
  · exact subtree293_layout_checked
  · exact subtree328_layout_checked
  · decide +kernel

theorem subtree357_rows_checked :
    subtree357.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree345_rows_checked
  · exact subtree365_rows_checked

theorem subtree357_layout_checked :
    subtree357.checkLayout code.toByteArray 334 371 = true := by
  apply Table.checkLayout_node (next := 358)
  · decide +kernel
  · exact subtree345_layout_checked
  · exact subtree365_layout_checked
  · decide +kernel

theorem subtree333_rows_checked :
    subtree333.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree316_rows_checked
  · exact subtree357_rows_checked

theorem subtree333_layout_checked :
    subtree333.checkLayout code.toByteArray 287 371 = true := by
  apply Table.checkLayout_node (next := 334)
  · decide +kernel
  · exact subtree316_layout_checked
  · exact subtree357_layout_checked
  · decide +kernel

theorem subtree286_rows_checked :
    subtree286.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree250_rows_checked
  · exact subtree333_rows_checked

theorem subtree286_layout_checked :
    subtree286.checkLayout code.toByteArray 217 371 = true := by
  apply Table.checkLayout_node (next := 287)
  · decide +kernel
  · exact subtree250_layout_checked
  · exact subtree333_layout_checked
  · decide +kernel

theorem subtree214_rows_checked :
    subtree214.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree88_rows_checked
  · exact subtree286_rows_checked

theorem subtree214_layout_checked :
    subtree214.checkLayout code.toByteArray 0 371 = true := by
  apply Table.checkLayout_node (next := 217)
  · decide +kernel
  · exact subtree88_layout_checked
  · exact subtree286_layout_checked
  · decide +kernel

/-- Strict ordering and the exact region population are checked independently. -/
theorem subtree214_order_and_size_checked :
    subtree214.checkOrder = true ∧ subtree214.size = 183 := by
  decide +kernel

end Blanc.Drip.StackSafety
