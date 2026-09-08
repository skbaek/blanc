import Blanc.DripStackSafetyRegion214
import Blanc.DripStackSafetyRegion576
import Blanc.DripStackSafetyRegion1022
import Blanc.DripStackSafetyRegion1459

/-!
Complete 735-row DRIP stack certificate and its actual same-frame entry theorem.
The conclusion follows only along an actual `Exec.Deriv.ParentPrefix`; entered child
frames require their own certificate before their parent continuation resumes.
-/

namespace Blanc.Drip.StackSafety

open Jaune AbstractStackSafety CompiledStackSafety

theorem subtree371_rows_checked :
    subtree371.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree214_rows_checked
  · exact subtree576_rows_checked

theorem subtree371_layout_checked :
    subtree371.checkLayout code.toByteArray 0 839 = true := by
  apply Table.checkLayout_node (next := 372)
  · decide +kernel
  · exact subtree214_layout_checked
  · exact subtree576_layout_checked
  · decide +kernel

theorem subtree1182_rows_checked :
    subtree1182.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree1022_rows_checked
  · exact subtree1459_rows_checked

theorem subtree1182_layout_checked :
    subtree1182.checkLayout code.toByteArray 840 1762 = true := by
  apply Table.checkLayout_node (next := 1199)
  · decide +kernel
  · exact subtree1022_layout_checked
  · exact subtree1459_layout_checked
  · decide +kernel

theorem subtree839_rows_checked :
    subtree839.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree371_rows_checked
  · exact subtree1182_rows_checked

theorem subtree839_layout_checked :
    subtree839.checkLayout code.toByteArray 0 1762 = true := by
  apply Table.checkLayout_node (next := 840)
  · decide +kernel
  · exact subtree371_layout_checked
  · exact subtree1182_layout_checked
  · decide +kernel

theorem table_rows_checked :
    table.all (checkRow code.toByteArray table 8) = true := by
  exact subtree839_rows_checked

theorem table_layout_checked :
    table.checkLayout code.toByteArray 0 1762 = true := by
  exact subtree839_layout_checked

/-- Strict ordering and the exact whole-table population are checked independently. -/
theorem table_order_and_size_checked :
    table.checkOrder = true ∧ table.size = 735 := by
  decide +kernel

/-- The actual runtime, complete ordered table, and all 735 transfer rows agree. -/
theorem table_checked : checkTable code.toByteArray table 8 = true := by
  unfold checkTable
  rw [show decide (8 ≤ 8) = true by decide]
  rw [table_order_and_size_checked.1, table_rows_checked]
  rfl

/-- The exact runtime entry row is PC zero with the complete empty operand stack. -/
theorem entry_invariant (pre : Devm) (entryStack : pre.stack = []) :
    table.Invariant 0 pre := by
  refine ⟨[], ?_, ?_⟩
  · decide +kernel
  · rw [entryStack]
    exact matches_nil

/-- Every node on an actual same-frame path from the concrete DRIP entry is locally
stack-safe and remains within the certified eight-word bound. -/
theorem actual_entry_safe {root node : Exec.Deriv}
    (hprefix : Exec.Deriv.ParentPrefix root node)
    (codeFrame : root.sevm.code = code.toByteArray)
    (entryPc : root.pc = 0)
    (entryStack : root.devm.stack = []) :
    node.devm.stack.length ≤ 8 ∧
      CompiledStackSafety.StepSafe table.Invariant
        (Evm.step ⟨node.pc, node.sevm, node.devm⟩) := by
  have checked : checkTable root.sevm.code table 8 = true := by
    rw [codeFrame]
    exact table_checked
  apply (checkTable_certificate checked).at_parentPrefix hprefix rfl
  rw [entryPc]
  exact entry_invariant root.devm entryStack

end Blanc.Drip.StackSafety
