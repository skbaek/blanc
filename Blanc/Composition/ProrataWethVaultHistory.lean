import Blanc.Composition.ProrataWethVaultEnvironment
import Blanc.Composition.ProrataWethVaultAccounting
import Blanc.ProrataRealizedAccounting
import Blanc.Composition.ProrataWethVaultRely

namespace Blanc.Composition.ProrataWethVault

open Jaune

structure PairBoundary where
  vault : Stor
  weth : Stor

def PairBoundary.ofState (vault : Adr) (w : State) : PairBoundary :=
  ⟨w.getStor vault, w.getStor wethAccount⟩

inductive PairStep (vault : Adr) : State → State → Type
  | operation {before after : State} (t : FourQuote.FourQuoteTransition vault before after)
      (evidence : FourQuote.FourQuoteShareEvidence t.operation) : PairStep vault before after
  | authorizedDebit {before after : State} (call : WethAllowanceInvocation)
      (foreign : call.sevm.caller ≠ vault)
      (owner : Sevm.argWord call.sevm 0 = vault.toB256)
      (pair : call.pair? = some (vault.toB256, call.sevm.caller.toB256))
      (moved : Transfer (Stor.rest (before.getStor wethAccount)) vault
        (Sevm.argWord call.sevm 2) (Sevm.argWord call.sevm 1).toAdr
        (Stor.rest (after.getStor wethAccount)))
      (vaultKept : after.getStor vault = before.getStor vault) : PairStep vault before after
  | silent {before after : State} (caller : Adr)
      (vaultKept : after.getStor vault = before.getStor vault)
      (rowKept : Stor.rest (after.getStor wethAccount) vault =
        Stor.rest (before.getStor wethAccount) vault) : PairStep vault before after

def PairStep.caller {vault : Adr} {before after : State} : PairStep vault before after → Adr
  | .operation t _ => t.sevm.caller
  | .authorizedDebit call _ _ _ _ _ => call.sevm.caller
  | .silent caller _ _ => caller

structure PairStepRecord (vault : Adr) where
  before : State
  after : State
  step : PairStep vault before after
  own : Option WethAllowanceInvocation
  linked : ∀ call, own = some call →
    call.pre.state.getStor wethAccount = before.getStor wethAccount ∧
    call.post.state.getStor wethAccount = after.getStor wethAccount ∧
    (call.sevm.caller = vault → VaultStagedCalldata call)
  quiet : own = none → ∀ key, ¬ ValidAdr key →
    (after.getStor wethAccount).get key = (before.getStor wethAccount).get key
  debitOwn : ∀ call f o p m k, step = .authorizedDebit call f o p m k → own = some call
  provenance : Blanc.Prorata.ProrataAccountingProvenance
  actor : provenance.actor = some step.caller

def PairStepRecord.ledger (steps : List (PairStepRecord vault)) : List WethAllowanceInvocation :=
  steps.filterMap (·.own)

inductive PairReplay (vault : Adr) : PairBoundary → List (PairStepRecord vault) → PairBoundary → Prop
  | nil (b : PairBoundary) : PairReplay vault b [] b
  | cons {pre mid post : PairBoundary} (record : PairStepRecord vault) {steps}
      (preEq : PairBoundary.ofState vault record.before = pre)
      (postEq : PairBoundary.ofState vault record.after = mid)
      (tail : PairReplay vault mid steps post) : PairReplay vault pre (record :: steps) post

namespace PairReplay

theorem nil_of_eq {vault : Adr} {pre post : PairBoundary}
    (eq : post = pre) : PairReplay vault pre [] post := by
  rw [eq]
  exact .nil pre

theorem singleton {vault : Adr} (record : PairStepRecord vault) :
    PairReplay vault (PairBoundary.ofState vault record.before) [record]
      (PairBoundary.ofState vault record.after) := by
  exact .cons record rfl rfl (.nil _)

theorem append {vault : Adr} {pre mid post : PairBoundary}
    {left right : List (PairStepRecord vault)}
    (before : PairReplay vault pre left mid)
    (after : PairReplay vault mid right post) :
    PairReplay vault pre (left ++ right) post := by
  induction before with
  | nil boundary =>
      simpa using after
  | @cons pre mid post record steps preEq postEq tail ih =>
      simpa using PairReplay.cons record preEq postEq (ih after)

theorem ledger_append {vault : Adr} {xs ys : List (PairStepRecord vault)} :
    PairStepRecord.ledger (xs ++ ys) =
      PairStepRecord.ledger xs ++ PairStepRecord.ledger ys := by
  simp [PairStepRecord.ledger]

end PairReplay
end Blanc.Composition.ProrataWethVault
