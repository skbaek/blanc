import Blanc.Lift.GasSuccessCut
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolReRun3
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame4Chunks

/-!
# Additional-gas success on the actual reentrant-add arithmetic cut

The reference is Reach's low-budget step3088→4048 cut, 960 witness steps.
Only its selected path is certified.  The existing checked endpoint is reused.
The larger gas instance uses the old deployment's actual step2625 gas budget,
while retaining the reference addresses, memory, metadata and world.  This is
gas-only transport, not an old/new state, address, hash, or root-frame adapter.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.GeneralizedGasCut

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.GasSuccess
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

/-- The genuine named entry, with the same free tails as the existing run. -/
def entry (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : Cfg :=
  Boundary.cfgOfT bRe3088 tS tA m w

/-- Reuse the checked endpoint, then derive success at every larger budget. -/
theorem transport_from_selected (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (hc : selected Reach.fsI sRe 960 (entry tS tA m w) = true) :
    ∃ m' w', wrun Reach.fsI sRe 960 (entry tS tA m w) =
        .cont (Boundary.cfgOfT bRe4048 tS tA m' w') ∧
      ∀ δ, wrun Reach.fsI sRe 960 (addCfgGas (entry tS tA m w) δ) =
        .cont (addCfgGas (Boundary.cfgOfT bRe4048 tS tA m' w') δ) := by
  obtain ⟨m', w', hr⟩ := Boundary.obsDT_cont (reChunk4048 tS tA m w)
  refine ⟨m', w', hr, ?_⟩
  intro δ
  exact wrun_addGas hc hr δ

/-- The higher budget is a real old-deployment frame boundary, at step2625. -/
def oldBoundaryBudget : Nat := Subtree.mach2625.gasLeft

/-- The low-budget reference's entry gas and the old boundary gas. -/
theorem budgets (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) :
    (entry tS tA m w).devm.gasLeft = 826652 ∧ oldBoundaryBudget = 28072686 := by
  constructor <;> rfl

/-- This kernel witness is checked by the owned build, outside the LSP loop. -/
theorem selected_reference : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    selected Reach.fsI sRe 960 (entry tS tA m w) = true := by
  kernel_forall_rfl

/-- The actual reference cut supplies success for every added gas budget. -/
theorem transport (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) :
    ∃ m' w', wrun Reach.fsI sRe 960 (entry tS tA m w) =
        .cont (Boundary.cfgOfT bRe4048 tS tA m' w') ∧
      ∀ δ, wrun Reach.fsI sRe 960 (addCfgGas (entry tS tA m w) δ) =
        .cont (addCfgGas (Boundary.cfgOfT bRe4048 tS tA m' w') δ) :=
  transport_from_selected tS tA m w (selected_reference tS tA m w)

/-- Low-budget success consumes the shared transport with offset zero. -/
theorem low_instance (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) :
    ∃ c', wrun Reach.fsI sRe 960 (addCfgGas (entry tS tA m w) 0) = .cont c' ∧
      c'.devm.gasLeft = 823493 := by
  obtain ⟨m', w', _, ha⟩ := transport tS tA m w
  exact ⟨_, ha 0, rfl⟩

/-- Higher-budget success at the old boundary's gas, retaining all reference columns. -/
theorem high_instance (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) :
    (addCfgGas (entry tS tA m w) 27246034).devm.gasLeft = oldBoundaryBudget ∧
    ∃ c', wrun Reach.fsI sRe 960 (addCfgGas (entry tS tA m w) 27246034) = .cont c' ∧
      c'.devm.gasLeft = 28069527 := by
  obtain ⟨m', w', _, ha⟩ := transport tS tA m w
  constructor
  · change (entry tS tA m w).devm.gasLeft + 27246034 = oldBoundaryBudget
    rw [(budgets tS tA m w).1, (budgets tS tA m w).2]
  · refine ⟨_, ha 27246034, ?_⟩
    change (Boundary.cfgOfT bRe4048 tS tA m' w').devm.gasLeft + 27246034 = 28069527
    have hg : (Boundary.cfgOfT bRe4048 tS tA m' w').devm.gasLeft = 823493 := rfl
    rw [hg]

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.GeneralizedGasCut
