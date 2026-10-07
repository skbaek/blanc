import Blanc.Lift.Weth9.ClosedSigningData

/-! Finite key universe of the configured selector-only deposit. -/

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc.Lift

/-- Distinct keys covering the conservative deposit-frame footprint. -/
def depositKeys : List Key :=
  [.bal senderE, .bal 0, .allow 0 senderE, .allow senderE 0]

/-- Membership in the finite deposit-key universe. -/
def depositKeyUniverse (k : Key) : Prop := k ∈ depositKeys

theorem deposit_decodeCall {sevm : Sevm} (data : sevm.data = depositTx.data) :
    decodeCall sevm = some (.deposit sevm.caller sevm.value) := by
  have sel : Sevm.selector sevm = 0xd0e30db0 := by
    simp only [Sevm.selector, Sevm.dataWord, data, depositTx, dpSel_eq]
    decide +kernel
  unfold decodeCall
  by_cases hs : shortCall sevm
  · simp only [hs, ↓reduceIte]
  · simp (config := { decide := true }) only [hs, sel, ↓reduceIte]

theorem deposit_frameKeys {sevm : Sevm}
    (caller : sevm.caller = senderE) (data : sevm.data = depositTx.data) :
    frameKeys sevm =
      [.bal senderE, .bal 0, .bal 0, .allow 0 senderE, .allow senderE 0] := by
  have word4 : Sevm.dataWord sevm 4 = 0 := by
    simp only [Sevm.dataWord, data, depositTx, dpSel_eq]
    decide +kernel
  have word36 : Sevm.dataWord sevm 36 = 0 := by
    simp only [Sevm.dataWord, data, depositTx, dpSel_eq]
    decide +kernel
  simp only [frameKeys, caller, word4, word36]
  rfl

theorem deposit_frameKeys_included {sevm : Sevm}
    (caller : sevm.caller = senderE) (data : sevm.data = depositTx.data) :
    ∀ k ∈ frameKeys sevm, depositKeyUniverse k := by
  rw [deposit_frameKeys caller data]
  intro k hk
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    simp only [depositKeyUniverse, depositKeys, List.mem_cons,
      List.mem_nil_iff, or_false, true_or, or_true]

theorem deposit_holder_key {sevm : Sevm}
    (caller : sevm.caller = senderE) : .bal senderE ∈ frameKeys sevm := by
  simp only [frameKeys, caller, List.mem_cons, true_or]

end Blanc.Lift.Weth9.ClosedInstance
