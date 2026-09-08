import Blanc.DripCode
import Blanc.DripStackSafetyData

namespace Blanc.Drip.StackSafety

open Jaune AbstractStackSafety

theorem code_size : code.toByteArray.size = 1762 := by
  decide +kernel

theorem code_decode_one_checked :
    (match code.toByteArray.getInst 1 with
      | some (.next (.reg .calldatasize)) => true
      | _ => false) = true := by
  decide +kernel

theorem table_lookup_two : table.lookup 2 = some [none] := by
  decide +kernel

theorem row_one_checked : checkRow code.toByteArray table 8 1 [] = true := by
  decide +kernel

/-- Every row uses the complete table, including the edge from PC13 to PC14. -/
theorem subtree7_rows_checked :
    subtree7.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree7_layout_checked : subtree7.checkLayout code.toByteArray 0 14 = true := by
  decide +kernel

theorem subtree7_order_checked : subtree7.checkOrder = true := by
  decide +kernel

theorem subtree7_size : subtree7.size = 11 := by
  decide +kernel

theorem subtree30_rows_checked :
    subtree30.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree30_layout_checked : subtree30.checkLayout code.toByteArray 19 41 = true := by
  decide +kernel

/-- Named proofs join both children and the intervening row. -/
theorem subtree14_rows_checked :
    subtree14.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree7_rows_checked
  · exact subtree30_rows_checked

/-- The join consumes PC14's actual five-byte PUSH, leaving no byte gap. -/
theorem subtree14_layout_checked : subtree14.checkLayout code.toByteArray 0 41 = true := by
  apply Table.checkLayout_node (next := 19)
  · decide +kernel
  · exact subtree7_layout_checked
  · exact subtree30_layout_checked
  · decide +kernel

theorem subtree14_order_and_size_checked : subtree14.checkOrder = true ∧ subtree14.size = 22 := by
  decide +kernel

/-- This leaf includes the actual backedge at PC1140 to PC951 in another subtree. -/
theorem subtree1148_rows_checked :
    subtree1148.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree1148_layout_checked :
    subtree1148.checkLayout code.toByteArray 1140 1156 = true := by
  decide +kernel

/-- Includes the sole height-eight CALL at PC1720 and its actual continuation. -/
theorem subtree1717_rows_checked :
    subtree1717.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree1717_layout_checked :
    subtree1717.checkLayout code.toByteArray 1712 1724 = true := by
  decide +kernel

theorem subtree49_rows_checked :
    subtree49.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree49_layout_checked : subtree49.checkLayout code.toByteArray 44 58 = true := by
  decide +kernel

theorem subtree65_rows_checked :
    subtree65.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree65_layout_checked : subtree65.checkLayout code.toByteArray 59 88 = true := by
  decide +kernel

theorem subtree58_rows_checked :
    subtree58.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree49_rows_checked
  · exact subtree65_rows_checked

theorem subtree58_layout_checked : subtree58.checkLayout code.toByteArray 44 88 = true := by
  apply Table.checkLayout_node (next := 59)
  · decide +kernel
  · exact subtree49_layout_checked
  · exact subtree65_layout_checked
  · decide +kernel

theorem subtree41_rows_checked :
    subtree41.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree14_rows_checked
  · exact subtree58_rows_checked

theorem subtree41_layout_checked : subtree41.checkLayout code.toByteArray 0 88 = true := by
  apply Table.checkLayout_node (next := 44)
  · decide +kernel
  · exact subtree14_layout_checked
  · exact subtree58_layout_checked
  · decide +kernel

theorem subtree111_rows_checked :
    subtree111.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree111_layout_checked : subtree111.checkLayout code.toByteArray 89 151 = true := by
  decide +kernel

theorem subtree176_rows_checked :
    subtree176.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree176_layout_checked : subtree176.checkLayout code.toByteArray 153 185 = true := by
  decide +kernel

theorem subtree151_rows_checked :
    subtree151.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree111_rows_checked
  · exact subtree176_rows_checked

theorem subtree151_layout_checked : subtree151.checkLayout code.toByteArray 89 185 = true := by
  apply Table.checkLayout_node (next := 153)
  · decide +kernel
  · exact subtree111_layout_checked
  · exact subtree176_layout_checked
  · decide +kernel

theorem subtree191_rows_checked :
    subtree191.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree191_layout_checked : subtree191.checkLayout code.toByteArray 186 197 = true := by
  decide +kernel

theorem subtree209_rows_checked :
    subtree209.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree209_layout_checked : subtree209.checkLayout code.toByteArray 198 214 = true := by
  decide +kernel

theorem subtree197_rows_checked :
    subtree197.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree191_rows_checked
  · exact subtree209_rows_checked

theorem subtree197_layout_checked : subtree197.checkLayout code.toByteArray 186 214 = true := by
  apply Table.checkLayout_node (next := 198)
  · decide +kernel
  · exact subtree191_layout_checked
  · exact subtree209_layout_checked
  · decide +kernel

theorem subtree185_rows_checked :
    subtree185.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree151_rows_checked
  · exact subtree197_rows_checked

theorem subtree185_layout_checked : subtree185.checkLayout code.toByteArray 89 214 = true := by
  apply Table.checkLayout_node (next := 186)
  · decide +kernel
  · exact subtree151_layout_checked
  · exact subtree197_layout_checked
  · decide +kernel

/-- Complete initial 91-row region; successor lookup still uses all 735 rows. -/
theorem subtree88_rows_checked :
    subtree88.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree41_rows_checked
  · exact subtree185_rows_checked

theorem subtree88_layout_checked : subtree88.checkLayout code.toByteArray 0 214 = true := by
  apply Table.checkLayout_node (next := 89)
  · decide +kernel
  · exact subtree41_layout_checked
  · exact subtree185_layout_checked
  · decide +kernel

theorem subtree88_order_and_size_checked : subtree88.checkOrder = true ∧ subtree88.size = 91 := by
  decide +kernel

theorem subtree1148_order_and_size_checked : subtree1148.checkOrder = true ∧ subtree1148.size = 11 := by
  decide +kernel

theorem subtree1717_order_and_size_checked : subtree1717.checkOrder = true ∧ subtree1717.size = 10 := by
  decide +kernel

end Blanc.Drip.StackSafety
