import Blanc.Lift.Token.Holder
import Blanc.Lift.Weth9.CommittedHistory
import Blanc.BalanceAlgebra

/-!
# WETH9 as the first instance of the token core (C2, composition stratum)

The WETH9 book reads the existing pure model (`Weth9.Ledger`, `Ledger.step`) through the dispatcher's
own decoder (`decodeCall`), as natural numbers; a ledger is good while its total fits a word.
`Weth9Hist` is exactly the trace-local premise set of `weth9_history_committed`.

The C2 control: a mutated model whose `transferFrom` skips the allowance check violates the core's
holder law (`control_mutant_not_laws`).
-/

namespace Blanc.Composition.Weth9Token

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.Token

/-- What a WETH9 entry frame asks, read through the dispatcher's own decoder. -/
def weth9Op (e : Sevm) : Op :=
  if ¬ shortCall e ∧ Sevm.selector e = 0x70a08231 then .balanceOf (Sevm.dataWord e 4).toAdr
  else match decodeCall e with
    | some (.deposit _ _) => .credit
    | some (.transfer _ dst wad) => .transfer dst wad.toNat
    | some (.transferFrom _ src dst wad) => .transferFrom src dst wad.toNat
    | some (.approve _ guy wad) => .approve guy wad.toNat
    | _ => .other

/-- The WETH9 book: the existing pure model, read as natural numbers; a ledger is good while its
total stays a word (what the history's ETH backing gives at every position). -/
def weth9Book : Book where
  Ledger := Weth9.Ledger
  step l e := match decodeCall e with
    | none => some l
    | some c => l.step c
  op := weth9Op
  bal l a := (l.bal a).toNat
  allow l o p := (l.allow o p).toNat
  Good l := l.total < 2 ^ 256

/-- The WETH9 trace-local premises: exactly those of `weth9_history_committed`. -/
def Weth9Hist (ca : Adr) (K₀ : Key → Prop) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future) : Prop :=
  some (checkpoint.state.getCode ca).toList = weth9Sem.image ∧ SumNof checkpoint.state.bal ∧
    FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca) ∧
    KeysFresh K₀ (historyTouchedKeys ca tr)

/-- The C2 control's mutant: `transferFrom` that skips the allowance check. -/
def mutantTransferFrom (l : Weth9.Ledger) (_who src dst : Adr) (wad : B256) : Option Weth9.Ledger :=
  if l.bal src < wad then none else some (l.xfer src dst wad)

def mutantBook : Book :=
  { weth9Book with
    step := fun l e => match decodeCall e with
      | some (.transferFrom who src dst wad) => mutantTransferFrom l who src dst wad
      | none => some l
      | some c => l.step c }

/-! ## The control witness -/

/-- The empty ledger. -/
def zeroLedger : Weth9.Ledger := ⟨fun _ => 0, fun _ _ => 0⟩

/-- A ledger in which only `a` holds one unit and nobody has granted an allowance. -/
def oneLedger (a : Adr) : Weth9.Ledger := zeroLedger.setBal a 1

theorem oneLedger_total (a : Adr) : (oneLedger a).total ≤ 1 := by
  have h := Ledger.sum_deposit_le zeroLedger a 1
  have hz : zeroLedger.total = 0 := sumBelow_zero _
  have hb : zeroLedger.bal a + 1 = 1 := by
    show (0 : B256) + 1 = 1
    decide
  rw [hb] at h
  change (oneLedger a).total ≤ zeroLedger.total + (1 : B256).toNat at h
  rw [hz] at h
  exact h

/-- The control's message: `transferFrom(1, 2, 1)` called by address `0`. -/
def mutantWitness : Sevm :=
  { (default : Sevm) with
    data := [0x23, 0xb8, 0x72, 0xdd] ++ List.replicate 31 0 ++ [1] ++ List.replicate 31 0 ++ [2] ++
      List.replicate 31 0 ++ [1] }

theorem mutantWitness_decode :
    decodeCall mutantWitness = some (.transferFrom 0 1 2 1) := by
  have short : ¬ shortCall mutantWitness := by decide +kernel
  have sel : Sevm.selector mutantWitness = 0x23b872dd := by decide +kernel
  have w4 : (Sevm.dataWord mutantWitness 4).toAdr = 1 := by decide +kernel
  have w36 : (Sevm.dataWord mutantWitness 36).toAdr = 2 := by decide +kernel
  have w68 : Sevm.dataWord mutantWitness 68 = 1 := by decide +kernel
  have caller : mutantWitness.caller = 0 := rfl
  unfold decodeCall
  rw [ite_eq_right short, sel, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl, w4, w36, w68, caller]

/-- **C2 control.**  The mutated model violates the core's holder law. -/
theorem control_mutant_not_laws : ¬ BookLaws mutantBook := by
  intro laws
  have good : mutantBook.Good (oneLedger 1) := by
    change (oneLedger 1).total < 2 ^ 256
    have := oneLedger_total 1
    omega
  have step : mutantBook.step (oneLedger 1) mutantWitness =
      some ((oneLedger 1).xfer 1 2 1) := by
    have h : mutantBook.step (oneLedger 1) mutantWitness =
        mutantTransferFrom (oneLedger 1) 0 1 2 1 := by
      unfold mutantBook
      dsimp only
      rw [mutantWitness_decode]
    rw [h]
    unfold mutantTransferFrom
    rw [ite_eq_right (by decide +kernel)]
  have lower : mutantBook.bal ((oneLedger 1).xfer 1 2 1) 1 < mutantBook.bal (oneLedger 1) 1 := by
    decide +kernel
  rcases laws.holder_only good step lower with h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide +kernel)

end Blanc.Composition.Weth9Token
