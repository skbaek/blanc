import Blanc.Lift.ViewChain
import Blanc.ExecutionAccountingMidHistoryIn
import Blanc.StorageOnlySpec
import Blanc.ExecutionSettledRootEntry
import Blanc.ExecutionRetainedDeletionSafety
import Blanc.ExecutionNoDelProducer

/-!
# A cell naming accounts that stand: a state-level invariant through a mid history

`MidHistoryTraceIn.outputNotDeleted_of_cell` carries a property of one cell, so a root law cannot read at a root's
entry that the account the cell names holds its code. `MidHistoryTraceIn.live_of_roots` carries that too: code at `wa`,
and a list of accounts witnessing the cell's word, each standing. A root may move the word to a list standing at its
entry; each account's own law keeps it out of the deletion set.

An account's code seen at a root's entry was there when its transaction began (`*.code_back`): authorizations write
only empty or delegation code.
-/

namespace Blanc.ExecutionTrace

open Jaune Blanc

/-! ## Code at a root's entry was there before it -/

end Blanc.ExecutionTrace

namespace Blanc.Lift

open Jaune Blanc Blanc.ExecutionTrace ContractSpecSem

/-! ## The invariant -/

/-- An account's code, with the certified semantics a root's entry reads it by. -/
structure StandingCode where
  adr : Adr
  code : ByteArray
  sem : CodeSem
  image : sem.image = some code.toList

/-- Every listed account holds its code. -/
def Stands (l : List StandingCode) (w : State) : Prop := ∀ p ∈ l, w.getCode p.adr = p.code

/-- `wa` holds `C`, and its cell's word has a witness list that stands. -/
def StateLive (wa : Adr) (C : ByteArray) (k : B256) (W : B256 → List StandingCode → Prop) (w : State) : Prop :=
  w.getCode wa = C ∧ ∃ l, W ((w.getStor wa).get k) l ∧ Stands l w

/-- A root's law: reading a standing witness at its entry, it keeps `wa` out of the deletion set and leaves a word whose
witness list stood at its entry. -/
def RootStep (F : Fork → Prop) (wa : Adr) (sem : CodeSem) (k : B256) (W : B256 → List StandingCode → Prop)
    (R : Exec.Frame) : Prop :=
  RootReady F wa sem (fun _ _ => True) R → ∀ l, W ((R.pre.getStor wa).get k) l → Stands l R.pre.state →
    (Devm.NoDel wa R.pre → Devm.NoDel wa R.post) ∧ ∃ l', W ((R.post.getStor wa).get k) l' ∧ Stands l' R.pre.state

section Levels

variable {F : Fork → Prop} {wa : Adr} {sem : CodeSem} {C : ByteArray} {k : B256}
  {W : B256 → List StandingCode → Prop}

local notation "Live" => StateLive wa C k W
local notation "Step" => RootStep F wa sem k W

end Levels

/-! ## One account standing -/

section Stands

variable {F : Fork → Prop} (capabilities : BodyStageCapabilities F) {a : Adr} {sem : CodeSem} {C : ByteArray}

variable {cfg : ChainConfig} {start : Benv} {future : BlockChain} (trace : MidHistoryTraceIn F cfg start future)

end Stands

end Blanc.Lift
