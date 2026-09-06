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

end Blanc.Drip.StackSafety
