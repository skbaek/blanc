import Blanc.BeaconDeposit
import Blanc.ExecutionOccurrence

/-!
# Beacon deposit compiled runtime artifact

Compiler-owned bytes, selector and size metadata, and fail-closed structural
source-site inventories for the BeaconDeposit runtime.
-/

namespace Blanc.BeaconDeposit

open Jaune

/-! ## Compiler artifact -/

def code : Bytes :=
  (Prog.compile runtime).getD []

def eip170RuntimeLimit : Nat :=
  pragueCodeLimits.maxCodeSize

def codeSize : Nat := code.length

theorem runtime_compiles : Prog.compiles runtime = true := by
  decide +kernel

theorem code_compile : Prog.compile runtime = some code := by
  unfold code
  exact Prog.compile_eq_some_getD_of_compiles _ runtime_compiles

theorem codeSize_exact : codeSize = 2891 := by
  decide +kernel

theorem eip170RuntimeLimit_exact : eip170RuntimeLimit = 24576 := by
  rfl

theorem code_eip170 : codeSize <= eip170RuntimeLimit := by
  rw [codeSize_exact, eip170RuntimeLimit_exact]
  decide

/-! ## Exact structural source-site inventories -/

private def isSstore : Ninst → Bool
  | .reg .sstore => true
  | _ => false

private def isStaticcall : Ninst → Bool
  | .exec .staticcall => true
  | _ => false

private def isLog1 : Ninst → Bool
  | .reg (.log 1) => true
  | _ => false

private def isExternalExecution : Ninst → Bool
  | .exec _ => true
  | _ => false

private def isMstore8 : Ninst → Bool
  | .reg .mstore8 => true
  | _ => false

private def sourceSitesMatching
    (predicate : Ninst → Bool) : List Prog.SourceSite :=
  runtime.sourceSites.filter fun site => predicate site.instruction

def runtimeSstoreSourceSites : List Prog.SourceSite :=
  sourceSitesMatching isSstore

def runtimeStaticcallSourceSites : List Prog.SourceSite :=
  sourceSitesMatching isStaticcall

/-- Membership in the runtime SSTORE inventory is exactly membership in the
compiler source map at a source-level SSTORE instruction. -/
theorem mem_runtimeSstoreSourceSites_iff
    {site : Prog.SourceSite} :
    site ∈ runtimeSstoreSourceSites ↔
      site ∈ runtime.sourceSites ∧ site.instruction = .reg .sstore := by
  rcases site with ⟨path, pc, instruction⟩
  cases instruction <;>
    simp only [runtimeSstoreSourceSites, sourceSitesMatching, isSstore, List.mem_filter, Ninst.reg.injEq, and_congr_right_iff, Bool.false_eq_true, and_false, reduceCtorEq]
  rename_i regular
  cases regular <;>
    simp only [Bool.false_eq_true, reduceCtorEq, implies_true]

theorem runtimeSstoreSourceSites_pcs :
    Prog.SourceSite.pcs runtimeSstoreSourceSites = [1070, 2869] := by
  decide +kernel

/-- Coupled function-table/PC identities for the two runtime write sites.
Keeping the coordinates paired prevents a consumer from mixing the main-body
count site with the insertion-loop branch site. -/
theorem runtimeSstoreSourceSites_coordinates :
    Prog.SourceSite.coordinates runtimeSstoreSourceSites =
      [(0, 1070), (13, 2869)] := by
  decide +kernel

/-- The complete runtime source-level SSTORE population is the count write in
the main deposit body or the branch write in the insertion-loop auxiliary. -/
theorem runtimeSstoreSourceSite_pc
    {site : Prog.SourceSite}
    (member : site ∈ runtimeSstoreSourceSites) :
    site.pc = 1070 ∨ site.pc = 2869 := by
  have pcMember : site.pc ∈ Prog.SourceSite.pcs runtimeSstoreSourceSites :=
    List.mem_map_of_mem member
  rw [runtimeSstoreSourceSites_pcs] at pcMember
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using pcMember

end Blanc.BeaconDeposit
