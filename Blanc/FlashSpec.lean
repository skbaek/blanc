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
import Blanc.Conserved
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

/-! ## The three guards, as facts

Arc B walked this same prefix while tracking `Devm.getStor`, and let every word
it met be anonymous (`Conserved.lean`, `flashLoan_preserves_conserved`).  Here
the words are *named*: Step 1's value-carrying calldata layer makes what the
guards constrain be `Sevm.argWord sevm k`, a function of the calldata alone, so
each `of_run_branch_rev` — "the revert arm was not taken" — becomes the fact the
guard states rather than a bookkeeping step.

**Hypothesis position throughout.**  The run is given and this reads facts off
it.  Nothing here says a `flashLoan` call ever succeeds. -/

/-- **`flashLoan`'s three guards, as facts about a run that got past them.**

If `flashLoan`'s body runs to a successful end, then

0. the `token` argument is this contract (`FMINT_DEVIATIONS.md` row 5: the
   ERC-3156 revert is reached through one explicit guard placed *before* the
   bound check, so the reason does not depend on `amount`);
1. the `receiver` argument is address-shaped.  Conservation-critical rather
   than hygiene (row 6), and it is also what makes the callback's callee equal
   to `receiver` on the nose, since `Devm.popToAdr` truncates to 160 bits and
   the guard makes that truncation the identity;
2. `supply + amount` does not overflow — the mint's whole overflow argument,
   bought by the `amount ≤ ~~~supply` bound check.

The supply named in (2) is the one in storage *on entry*, which is the right
one: nothing before this point writes storage. -/
theorem flashLoan_guards {sevm : Sevm} {s r : Devm}
    (h_run : Func.Run (fmint.main :: fmintAux) sevm s flashLoan r) :
    Sevm.argWord sevm 1 = sevm.currentTarget.toB256 ∧
    ValidAdr (Sevm.argWord sevm 0) ∧
    B256.Nof ((Devm.getStor s sevm.currentTarget).get supplySlot)
      (Sevm.argWord sevm 2) := by
  simp only [flashLoan] at h_run
  -- (0) `arg 1 +++ address ::: eq ::: iszero`: `token` must be this contract.
  rcases of_run_prepend (arg 1) _ h_run with ⟨s1, h1, h_run⟩
  have hs1 : Sevm.argWord sevm 1 :: [] <<+ s1.stack := prefix_of_arg nil_pref h1
  have hg : Devm.getStor s = Devm.getStor s1 := Line.of_inv Devm.getStor (by line_inv) h1
  clear h1
  rcases of_run_next h_run with ⟨s2, r2, h_run⟩
  have hs2 : sevm.currentTarget.toB256 :: Sevm.argWord sevm 1 :: [] <<+ s2.stack :=
    prefix_of_push (of_run_address r2) hs1
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r2 Line.Run.nil))
  clear r2 hs1
  rcases of_run_next h_run with ⟨s3, r3, h_run⟩
  have hs3 := prefix_of_eq r3 hs2
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r3 Line.Run.nil))
  clear r3 hs2
  rcases of_run_next h_run with ⟨s4, r4, h_run⟩
  have hs4 := prefix_of_iszero r4 hs3
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r4 Line.Run.nil))
  clear r4 hs3
  rcases of_run_branch_rev h_run with ⟨s5, hp5, h_run⟩
  have hp5s := hp5.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp5s
  rw [hp5s] at hs4
  have h_tokflag :
      ((sevm.currentTarget.toB256 =? Sevm.argWord sevm 1) =? 0) = 0 :=
    pref_head_unique hs4 (pref_append [0] s5.stack)
  have h_token : Sevm.argWord sevm 1 = sevm.currentTarget.toB256 := by
    by_contra hne
    have h0 : (sevm.currentTarget.toB256 =? Sevm.argWord sevm 1) = 0 := by
      simp only [B256.eqCheck]; exact if_neg (fun h => hne h.symm)
    rw [h0, show ((0 : B256) =? 0) = 1 from by simp [B256.eqCheck]] at h_tokflag
    exact B256.zero_ne_one h_tokflag.symm
  rw [h_tokflag] at hs4
  have hs5 : ([] : List B256) <<+ s5.stack := cons_pref_cons_inv hs4
  have hg := hg.trans (funext (fun x => (Devm.PopBurn.getStor hp5 x).symm))
  clear hp5 hs4 hp5s h_tokflag
  -- (1) `arg 0 +++ dup 0 ::: checkNonAddress`: the receiver word is address-shaped.
  rcases of_run_prepend (arg 0) _ h_run with ⟨s6, h6, h_run⟩
  have hs6 : Sevm.argWord sevm 0 :: [] <<+ s6.stack := prefix_of_arg hs5 h6
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h6)
  clear h6 hs5
  rcases of_run_next h_run with ⟨s7, r7, h_run⟩
  rcases of_run_dup r7 with ⟨y7, hy7, pb7⟩
  have hy7' : y7 = Sevm.argWord sevm 0 := by
    have hgt : s6.stack[(0 : Fin 16).val]? = some (Sevm.argWord sevm 0) :=
      Stack.nth_getElem (Stack.Nth.head _ []) hs6
    rw [hgt] at hy7; injection hy7 with hy7; exact hy7.symm
  subst y7
  have hs7 : [Sevm.argWord sevm 0, Sevm.argWord sevm 0] <<+ s7.stack :=
    prefix_of_push pb7 hs6
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r7 Line.Run.nil))
  clear r7 pb7 hs6
  rcases of_run_prepend checkNonAddress _ h_run with ⟨s8, h8, h_run⟩
  rcases of_check_non_address hs7 h8 with ⟨na, hs8, h_va_iff⟩
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h8)
  clear h8 hs7
  rcases of_run_branch_rev h_run with ⟨s9, hp9, h_run⟩
  have hp9s := hp9.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp9s
  rw [hp9s] at hs8
  have h_va : ValidAdr (Sevm.argWord sevm 0) :=
    h_va_iff.mp (pref_head_unique hs8 (pref_append [0] s9.stack))
  rw [pref_head_unique hs8 (pref_append [0] s9.stack)] at hs8
  have hs9 : [Sevm.argWord sevm 0] <<+ s9.stack := cons_pref_cons_inv hs8
  have hg := hg.trans (funext (fun x => (Devm.PopBurn.getStor hp9 x).symm))
  clear hs8 hp9s hp9 h_va_iff
  -- (2) `arg 2 +++ dup 0 ::: pushSupplySlot +++ sload ::: not ::: lt`: the bound.
  rcases of_run_prepend (arg 2) _ h_run with ⟨s10, h10, h_run⟩
  have hs10 : Sevm.argWord sevm 2 :: [Sevm.argWord sevm 0] <<+ s10.stack :=
    prefix_of_arg hs9 h10
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h10)
  clear h10 hs9
  rcases of_run_next h_run with ⟨s11, r11, h_run⟩
  rcases of_run_dup r11 with ⟨y11, hy11, pb11⟩
  have hy11' : y11 = Sevm.argWord sevm 2 := by
    have hgt : s10.stack[(0 : Fin 16).val]? = some (Sevm.argWord sevm 2) :=
      Stack.nth_getElem (Stack.Nth.head _ [Sevm.argWord sevm 0]) hs10
    rw [hgt] at hy11; injection hy11 with hy11; exact hy11.symm
  subst y11
  have hs11 : [Sevm.argWord sevm 2, Sevm.argWord sevm 2, Sevm.argWord sevm 0]
      <<+ s11.stack := prefix_of_push pb11 hs10
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r11 Line.Run.nil))
  clear r11 pb11 hs10
  rcases of_run_prepend pushSupplySlot _ h_run with ⟨s12, h12, h_run⟩
  have hs12 : supplySlot ::
      [Sevm.argWord sevm 2, Sevm.argWord sevm 2, Sevm.argWord sevm 0] <<+ s12.stack := by
    simp only [pushSupplySlot] at h12
    rcases Line.of_run_cons h12 with ⟨sa, ra, h12'⟩
    rcases Line.of_run_cons h12' with ⟨sb, rb, hnil⟩
    cases hnil
    have hpa : (0 : B256) ::
        [Sevm.argWord sevm 2, Sevm.argWord sevm 2, Sevm.argWord sevm 0] <<+ sa.stack :=
      prefix_of_push (of_run_pushB256 ra) hs11
    have hpb := prefix_of_not rb hpa
    rw [supplySlot_eq_not_zero] at hpb
    exact hpb
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h12)
  clear h12 hs11
  rcases of_run_next h_run with ⟨s13, r13, h_run⟩
  rcases prefix_of_sload r13 hs12 with ⟨supply, hs13, h_supply⟩
  have h_supply' : supply = (Devm.getStor s sevm.currentTarget).get supplySlot := by
    rw [h_supply]
    show (Devm.getStor s12 sevm.currentTarget).get supplySlot = _
    rw [← congr_fun hg sevm.currentTarget]
  clear h_supply
  rcases of_run_next h_run with ⟨s14, r14, h_run⟩
  have hs14 := prefix_of_not r14 hs13
  clear r14 hs13
  rcases of_run_next h_run with ⟨s15, r15, h_run⟩
  have hs15 := prefix_of_lt r15 hs14
  clear r15 hs14
  rcases of_run_branch_rev h_run with ⟨s16, hp16, h_run⟩
  have hp16s := hp16.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp16s
  rw [hp16s] at hs15
  have h_boundflag : ((~~~ supply) <? Sevm.argWord sevm 2) = 0 :=
    pref_head_unique hs15 (pref_append [0] s16.stack)
  have h_bound : Sevm.argWord sevm 2 ≤ ~~~ supply := by
    rw [← B256.not_lt]; intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_boundflag
    exact B256.zero_ne_one h_boundflag.symm
  exact ⟨h_token, h_va, h_supply' ▸ B256.nof_of_le_not h_bound⟩

end Fmint

end Blanc
