import Blanc.Composition.ProrataWethVaultEffects
import Blanc.ExecutionTraceFrames

/-!
# Raw allowance visits of the PRORATA/WETH execution trace

This module defines the finite visit projection used by the vault-local
allowance collision premise.  The frame classifier reads only raw committed
frame roots; it does not apply settlement filtering.
-/

namespace Blanc

open Jaune

namespace Composition.ProrataWethVault

/-- What D9 reads of one allowance invocation: selector class, WETH-frame
caller, first argument, and WETH's storage at entry. -/
structure AllowanceVisit where
  approval : Bool
  caller : Adr
  arg0 : B256
  wethPre : Stor

def AllowanceVisit.pair? (v : AllowanceVisit) : Option (B256 × B256) :=
  if v.approval then some (v.caller.toB256, v.arg0)
  else if v.arg0 = v.caller.toB256 then none
  else some (v.arg0, v.caller.toB256)

def AllowanceVisit.writtenPair? (v : AllowanceVisit) : Option (B256 × B256) :=
  if v.approval then v.pair?
  else v.pair?.filter fun p =>
    v.wethPre.get (wethAllowanceKey p.1 p.2) != B256.max

def WethAllowanceInvocation.visit
    (call : WethAllowanceInvocation) : AllowanceVisit :=
  ⟨call.approval, call.sevm.caller, Sevm.argWord call.sevm 0,
    Devm.getStor call.pre wethAccount⟩

theorem WethAllowanceInvocation.visit_pair?
    (call : WethAllowanceInvocation) :
    call.visit.pair? = call.pair? := by
  rfl

theorem WethAllowanceInvocation.visit_writtenPair?
    (call : WethAllowanceInvocation) :
    call.visit.writtenPair? = call.writtenPair? := by
  simp only [AllowanceVisit.writtenPair?, WethAllowanceInvocation.writtenPair?]
  rw [call.visit_pair?]
  rfl

/-- D9 over a list of visits, in the same shape as the allowance-history
collision premise. -/
def NoVaultVisitKeyCollision
    (visits : List AllowanceVisit) (vault : Adr) : Prop :=
  ∀ p ∈ visits.filterMap AllowanceVisit.pair?, p.1 = vault.toB256 →
    ∀ q ∈ visits.filterMap AllowanceVisit.writtenPair?, p ≠ q →
      wethAllowanceKey p.1 p.2 ≠ wethAllowanceKey q.1 q.2

instance (visits : List AllowanceVisit) (vault : Adr) :
    Decidable (NoVaultVisitKeyCollision visits vault) := by
  unfold NoVaultVisitKeyCollision
  infer_instance

/-- Antitonicity from the real-chain visit universe to the recorded ledger. -/
theorem noVaultAllowanceKeyCollision_of_visits
    {history : List WethAllowanceInvocation}
    {visits : List AllowanceVisit} {vault : Adr}
    (sub : ∀ call ∈ history, call.visit ∈ visits)
    (real : NoVaultVisitKeyCollision visits vault) :
    NoVaultAllowanceKeyCollision history vault := by
  intro p hp hpVault q hq hpq
  change p ∈ history.filterMap WethAllowanceInvocation.pair? at hp
  change q ∈ history.filterMap WethAllowanceInvocation.writtenPair? at hq
  rcases List.mem_filterMap.mp hp with ⟨call, callMember, pairEq⟩
  rcases List.mem_filterMap.mp hq with ⟨writer, writerMember, writtenEq⟩
  have visitMember : call.visit ∈ visits := sub call callMember
  have visitPair : call.visit.pair? = some p := by
    rw [call.visit_pair?]
    exact pairEq
  have visitWritten : writer.visit.writtenPair? = some q := by
    rw [writer.visit_writtenPair?]
    exact writtenEq
  exact real p
    (List.mem_filterMap.mpr ⟨call.visit, visitMember, visitPair⟩)
    hpVault q
    (List.mem_filterMap.mpr ⟨writer.visit, sub writer writerMember,
      visitWritten⟩)
    hpq

end Composition.ProrataWethVault

namespace Exec.Deriv

/-- The allowance visit an actual committed frame makes. -/
def pairVisit?
    (vault : Adr) (d : Exec.Deriv) :
    Option Composition.ProrataWethVault.AllowanceVisit :=
  if Execution.commits d.exn = true ∧ d.pc = 0 ∧
      d.sevm.currentTarget = Composition.ProrataWethVault.wethAccount ∧
      d.sevm.codeAddress = some Composition.ProrataWethVault.wethAccount ∧
      some d.sevm.code.toList = Blanc.weth.compile then
    if Sevm.selector d.sevm = selector "approve" [.address, .uint256] then
      some ⟨true, d.sevm.caller, Sevm.argWord d.sevm 0,
        Devm.getStor d.devm Composition.ProrataWethVault.wethAccount⟩
    else if Sevm.selector d.sevm =
        selector "transferFrom" [.address, .address, .uint256] then
      some ⟨false, d.sevm.caller, Sevm.argWord d.sevm 0,
        Devm.getStor d.devm Composition.ProrataWethVault.wethAccount⟩
    else none
  else if Execution.commits d.exn = true ∧ d.pc = 0 ∧
      d.sevm.currentTarget = vault ∧
      d.sevm.codeAddress = some vault ∧
      some d.sevm.code.toList = Blanc.ProrataWethVault.vault.compile ∧
      (Sevm.selector d.sevm = selector "deposit" [.uint256, .address] ∨
        Sevm.selector d.sevm = selector "mint" [.uint256, .address]) then
    some ⟨false, vault, d.sevm.caller.toB256,
      Devm.getStor d.devm Composition.ProrataWethVault.wethAccount⟩
  else none

theorem pairVisit?_eq_none_of_foreign {d : Exec.Deriv}
    (wethNe : d.sevm.currentTarget ≠ Composition.ProrataWethVault.wethAccount)
    (vaultNe : d.sevm.currentTarget ≠ vault) :
    d.pairVisit? vault = none := by
  simp [pairVisit?, wethNe, vaultNe]

end Exec.Deriv

namespace ExecutionTrace

open Composition.ProrataWethVault

/-- The real-chain allowance list of a retained configured history. -/
def ConfiguredHistoryTrace.pairVisits
    (vault : Adr) (h : ConfiguredHistoryTrace cfg c f) :
    List AllowanceVisit :=
  h.rawFrames.filterMap (Exec.Deriv.pairVisit? vault)

end ExecutionTrace

end Blanc
