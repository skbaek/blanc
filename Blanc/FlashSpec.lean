-- FlashSpec.lean : fmint's `flashLoan` success specification (Arc C of the
-- flashmint program, `~/plans/fmint-flashloan.md`).
--
-- Step 2 lands the entry route here: the composition of `correct` with
-- dispatch reachability that takes a successful top-level `Exec` at fmint's
-- code to a run of `flashLoan`'s body.  Steps 3-6 add the forward walk, the
-- callback boundary, the repayment postcondition, and the headline
-- `fmint_flashLoan_spec`.
--
-- This module is fmint-owned (`scripts/check-layering.py`, `CONTRACTS`): it
-- may import `Blanc.Fmint` and `Blanc.Conserved`, and must not import any
-- WETH module.

import Blanc.Fmint
import Blanc.CommonProofs

namespace Blanc

namespace Fmint

open Jaune

/-- `flashLoan`'s selector, as `fmintFuncs` lists it: the top four bytes of
`keccak("flashLoan(address,address,uint256,bytes)")`, right-aligned in a word.
A definition, never evaluated: deciding it forces the `String.keccak` behind
it and blows `maxRecDepth` with an unreadable failure signature (see
`fmintFuncs_sorted`'s docstring).  Proofs treat it as an opaque word. -/
def flashLoanSelector : B256 :=
  selector "flashLoan" [.address, .address, .uint256, .dynBytes]

/-- `flashLoan` is entry 5 of `fmintFuncs`, by `List.Mem` constructors alone —
membership is positional, so nothing compares (and so nothing evaluates) any
selector word (fixed decision 3 of the arc). -/
lemma flashLoan_mem_fmintFuncs : (flashLoanSelector, flashLoan) ∈ fmintFuncs := by
  simp only [fmintFuncs, flashLoanSelector]
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.head _)))))

/-- **The entry route.**  A successful top-level `Exec` at fmint's code whose
calldata selector is `flashLoan`'s passed through `flashLoan`'s body: the run
factors as dispatcher entry to some state `s'` — with account storage,
balances and code images unchanged from `pre` — followed by a run of
`Fmint.flashLoan` from `s'` to the same `post`.

This is `correct` (`Exec` to `Prog.Run`), the `call 0` unwrap, Step 1's
`prefix_of_fsig` value fact, and `reach_of_dispatchWith` instantiated with
`fmintFuncs_sorted`, composed once so that Steps 3-6 can start every walk from
the `Func.Run` this delivers.

**Hypothesis-position throughout**: the `Exec` is given, and this factors it.
Nothing here says a `flashLoan` call ever succeeds — that would be a liveness
claim, and no such content exists in this repository
(`~/plans/liveness-prelude-proposal.md`). -/
theorem exec_enters_flashLoan {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector) :
    ∃ s',
      Devm.getStor s' = Devm.getStor pre ∧
      Devm.getBal s' = Devm.getBal pre ∧
      Devm.getCode s' = Devm.getCode pre ∧
      Func.Run (fmint.main :: fmintAux) sevm s' flashLoan post := by
  have h_run : Prog.Run sevm pre fmint post := correct sevm pre fmint post exc h_code
  dsimp only [Prog.Run] at h_run
  cases h_run
  rename (_ = _) => h_eq
  rename (Func.Run _ _ _ _ _) => run
  rename (Devm.Burn _ _) => burn
  rename Devm => s₀
  cases h_eq
  -- fmint's `main` is the dispatcher shape; run off its `fsig` prefix
  have run' : Func.Run (fmint.main :: fmint.aux) sevm s₀
      (fsig +++ dispatchWith fallbackSlot fmintTree) post := run
  clear run
  refine run_prepend_elim _ fsig ?_ run'
  intro s₁ h₁ run₁
  have h_pfx : Sevm.selector sevm :: [] <<+ s₁.stack := prefix_of_fsig nil_pref h₁
  rw [h_sel] at h_pfx
  rcases reach_of_dispatchWith fmintFuncs_sorted flashLoan_mem_fmintFuncs h_pfx run₁
    with ⟨s', _, h_state, h_runf⟩
  refine ⟨s', ?_, ?_, ?_, h_runf⟩
  · have h3 : Devm.getStor s₁ = Devm.getStor s' := by
      funext a; show (s₁.state.get a).stor = (s'.state.get a).stor; rw [h_state]
    have h2 : Devm.getStor s₀ = Devm.getStor s₁ :=
      Line.of_inv Devm.getStor (by line_inv) h₁
    have h1 : Devm.getStor pre = Devm.getStor s₀ := by
      funext a; show (pre.state.get a).stor = (s₀.state.get a).stor; rw [burn.state]
    rw [← h3, ← h2, ← h1]
  · have h3 : Devm.getBal s₁ = Devm.getBal s' := by
      funext a; show (s₁.state.get a).bal = (s'.state.get a).bal; rw [h_state]
    have h2 : Devm.getBal s₀ = Devm.getBal s₁ :=
      Line.of_inv Devm.getBal (by line_inv) h₁
    have h1 : Devm.getBal pre = Devm.getBal s₀ := by
      funext a; show (pre.state.get a).bal = (s₀.state.get a).bal; rw [burn.state]
    rw [← h3, ← h2, ← h1]
  · have h3 : Devm.getCode s₁ = Devm.getCode s' := by
      funext a; show (s₁.state.get a).code = (s'.state.get a).code; rw [h_state]
    have h2 : Devm.getCode s₀ = Devm.getCode s₁ :=
      Line.of_inv Devm.getCode (by line_inv) h₁
    have h1 : Devm.getCode pre = Devm.getCode s₀ := by
      funext a; show (pre.state.get a).code = (s₀.state.get a).code; rw [burn.state]
    rw [← h3, ← h2, ← h1]

end Fmint

end Blanc
