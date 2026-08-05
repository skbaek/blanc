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

/-! ## The callback's memory image

The layout `Blanc/Fmint.lean` tabulates, proved rather than assumed.  Two
fragment lemmas first: `storeCallbackHead` and `callbackArgsSize` are fmint's,
so their value-carrying forms live here rather than in the shared layer, and
they are the value-carrying companions of Arc B's stack-only
`of_storeCallbackHead` and `of_callbackArgsSize`. -/

/-- **`storeCallbackHead`, with its memory effect.**

The selector and the five head words land in memory words 0-5: selector at
`0x00` (right-aligned inside the word, which is what makes the `CALL`'s window
start four bytes short of word 1), `initiator = caller` at `0x20`,
`token = address(this)` at `0x40`, `amount` at `0x60`, `fee = 0` at `0x80`
(proposal D2), and the `data` offset `0xa0` at `0xa0`.

Checked against the table at `Blanc/Fmint.lean` instruction by instruction; the
byte offsets below are `(k * 32).toNat` evaluated, not restated. -/
lemma of_storeCallbackHead_val {e : Sevm} {s s' : Devm} {x xs}
    (hp : x :: xs <<+ s.stack) (h : Line.Run e s storeCallbackHead s') :
    (xs <<+ s'.stack) ∧
      s'.memory =
        ((((((s.memory.write 0 onFlashLoanSelector.toBytes).write
          32 e.caller.toB256.toBytes).write
          64 e.currentTarget.toB256.toBytes).write
          96 x.toBytes).write
          128 (0 : B256).toBytes).write
          160 (0xa0 : B256).toBytes) := by
  simp only [storeCallbackHead] at h
  rcases Line.of_run_cons h with ⟨t1, q1, h⟩
  have hb1 := of_run_pushB256 q1
  have hp1 : onFlashLoanSelector :: x :: xs <<+ t1.stack := prefix_of_push hb1 hp
  rcases of_run_append (mstoreAt 0) h with ⟨t2, q2, h⟩
  rcases of_run_mstoreAt_val q2 hp1 with ⟨hp2, hm2⟩
  have e2 : t2.memory = s.memory.write 0 onFlashLoanSelector.toBytes := by
    rw [hm2, ← hb1.memory]; rfl
  rcases Line.of_run_cons h with ⟨t3, q3, h⟩
  have hb3 := of_run_caller q3
  have hp3 : e.caller.toB256 :: x :: xs <<+ t3.stack := prefix_of_push hb3 hp2
  rcases of_run_append (mstoreAt 1) h with ⟨t4, q4, h⟩
  rcases of_run_mstoreAt_val q4 hp3 with ⟨hp4, hm4⟩
  have e4 : t4.memory =
      (s.memory.write 0 onFlashLoanSelector.toBytes).write 32 e.caller.toB256.toBytes := by
    rw [hm4, ← hb3.memory, e2]; rfl
  rcases Line.of_run_cons h with ⟨t5, q5, h⟩
  have hb5 := of_run_address q5
  have hp5 : e.currentTarget.toB256 :: x :: xs <<+ t5.stack := prefix_of_push hb5 hp4
  rcases of_run_append (mstoreAt 2) h with ⟨t6, q6, h⟩
  rcases of_run_mstoreAt_val q6 hp5 with ⟨hp6, hm6⟩
  have e6 : t6.memory =
      ((s.memory.write 0 onFlashLoanSelector.toBytes).write
        32 e.caller.toB256.toBytes).write 64 e.currentTarget.toB256.toBytes := by
    rw [hm6, ← hb5.memory, e4]; rfl
  rcases of_run_append (mstoreAt 3) h with ⟨t7, q7, h⟩
  rcases of_run_mstoreAt_val q7 hp6 with ⟨hp7, hm7⟩
  have e7 : t7.memory =
      (((s.memory.write 0 onFlashLoanSelector.toBytes).write
        32 e.caller.toB256.toBytes).write
        64 e.currentTarget.toB256.toBytes).write 96 x.toBytes := by
    rw [hm7, e6]; rfl
  rcases Line.of_run_cons h with ⟨t8, q8, h⟩
  have hb8 := of_run_pushB256 q8
  have hp8 : (0 : B256) :: xs <<+ t8.stack := prefix_of_push hb8 hp7
  rcases of_run_append (mstoreAt 4) h with ⟨t9, q9, h⟩
  rcases of_run_mstoreAt_val q9 hp8 with ⟨hp9, hm9⟩
  have e9 : t9.memory =
      ((((s.memory.write 0 onFlashLoanSelector.toBytes).write
        32 e.caller.toB256.toBytes).write
        64 e.currentTarget.toB256.toBytes).write
        96 x.toBytes).write 128 (0 : B256).toBytes := by
    rw [hm9, ← hb8.memory, e7]; rfl
  rcases Line.of_run_cons h with ⟨t10, q10, h⟩
  have hb10 := of_run_pushB256 q10
  have hp10 : (0xa0 : B256) :: xs <<+ t10.stack := prefix_of_push hb10 hp9
  rcases of_run_mstoreAt_val h hp10 with ⟨hp11, hm11⟩
  exact ⟨hp11, by rw [hm11, ← hb10.memory, e9]; rfl⟩

/-- **`callbackArgsSize`, with its value.**

`0xc4 + ceil32(len)` — four selector bytes plus six words plus the padded
payload, which is exactly the length `abiCallWithTail` emits for four head words
and one trailing `bytes`.  `~~~31` is pushed as `PUSH1 31; NOT`. -/
lemma of_callbackArgsSize_val {e : Sevm} {s s' : Devm} {x xs}
    (hp : x :: xs <<+ s.stack) (h : Line.Run e s callbackArgsSize s') :
    (0xc4 + ((~~~ (31 : B256)) &&& (31 + x))) :: xs <<+ s'.stack := by
  simp only [callbackArgsSize] at h
  rcases Line.of_run_cons h with ⟨u1, q1, h⟩
  have hp1 : (31 : B256) :: x :: xs <<+ u1.stack := prefix_of_push (of_run_pushB256 q1) hp
  rcases Line.of_run_cons h with ⟨u2, q2, h⟩
  have hp2 := prefix_of_add q2 hp1
  rcases Line.of_run_cons h with ⟨u3, q3, h⟩
  have hp3 : (31 : B256) :: (31 + x) :: xs <<+ u3.stack :=
    prefix_of_push (of_run_pushB256 q3) hp2
  rcases Line.of_run_cons h with ⟨u4, q4, h⟩
  have hp4 := prefix_of_not q4 hp3
  rcases Line.of_run_cons h with ⟨u5, q5, h⟩
  have hp5 := prefix_of_and q5 hp4
  rcases Line.of_run_cons h with ⟨u6, q6, h⟩
  have hp6 : (0xc4 : B256) :: ((~~~ (31 : B256)) &&& (31 + x)) :: xs <<+ u6.stack :=
    prefix_of_push (of_run_pushB256 q6) hp5
  rcases Line.of_run_cons h with ⟨u7, q7, hnil⟩
  cases hnil
  exact prefix_of_add q7 hp6

/-! ## The forward walk to the callback

Arc B walked this same route while tracking `Devm.getStor`, and let every word
it met be anonymous (`Conserved.lean`, `flashLoan_preserves_conserved`).  Here
the words are *named*: Step 1's value-carrying calldata layer makes what the
guards constrain be `Sevm.argWord sevm k`, a function of the calldata alone, so
each `of_run_branch_rev` — "the revert arm was not taken" — becomes the fact the
guard states, and the mint pair becomes an equation rather than a `Conserved`
step.

**Hypothesis position throughout.**  The run is given and this reads facts off
it.  Nothing here says a `flashLoan` call ever succeeds. -/

/-- `flashLoan`'s body from the `CALL` onward: the callback, the two returndata
checks, and the repayment.

A *definition*, not a restatement — it is literally the sub-term of `flashLoan`
at that point, so the walk below stops type-checking if the contract's tail ever
changes.  It exists so that `of_flashLoan_toCall` can hand the next step a run
that is still tied to the same `r`, rather than an unattached state. -/
def flashLoanFromCall : Func :=
  Ninst.call ::: Ninst.iszero :::
  .rev <?>
  retdataShorterThan 32 +++
  .rev <?>
  checkRetdataHead erc3156Magic 0 +++
  Ninst.iszero :::
  .rev <?>
  spendAllowanceThenBurn

/-- **The forward walk from `flashLoan`'s entry to its `CALL`.**

If `flashLoan`'s body runs to a successful end then, before the callback opens
a child frame:

* **guard (0)** the `token` argument is this contract (`FMINT_DEVIATIONS.md`
  row 5: the ERC-3156 revert is reached through one explicit guard placed
  *before* the bound check, so the reason does not depend on `amount`);
* **guard (2)** `supply + amount` does not overflow — the mint's whole overflow
  argument, bought by the `amount ≤ ~~~supply` bound check.  The supply named
  is the one in storage on entry, which is the right one: nothing before this
  point writes storage;
* **guard (1)** the `receiver` argument is address-shaped, delivered as the
  `Adr` it names.  Conservation-critical rather than hygiene (row 6), and it is
  also what makes the callback's callee equal to `receiver` on the nose, since
  `Devm.popToAdr` truncates to 160 bits and the guard makes that truncation the
  identity;
* **the mint pair, as an equation.**  Both `SSTORE`s complete before the `CALL`
  (proposal D5), so this is a fact about the state the callback is entered in,
  not merely about the state it is left in.  The supply side reads `amount +
  supply` and not `amount + (stor.set receiver _).get supplySlot` because the
  supply slot is not address-shaped (`Stor.get_supplySlot_set`), which is the
  same disjointness the conservation invariant rests on;
* **the `CALL`'s operand stack**, assembled deepest-first: gas, callee, value
  `0`, `argsOffset = 0x1c`, an `argsSize`, and the two empty-return-window
  zeros, over the retained `amount` and `receiver`.

Nothing here constrains the memory window the `CALL` will read; that is
`flashLoan_callback_image`. -/
theorem of_flashLoan_toCall {sevm : Sevm} {s r : Devm}
    (h_run : Func.Run (fmint.main :: fmintAux) sevm s flashLoan r) :
    Sevm.argWord sevm 1 = sevm.currentTarget.toB256 ∧
    B256.Nof ((Devm.getStor s sevm.currentTarget).get supplySlot)
      (Sevm.argWord sevm 2) ∧
    ∃ (a : Adr) (sc : Devm) (g : B256),
      Sevm.argWord sevm 0 = a.toB256 ∧
      Devm.getCode s = Devm.getCode sc ∧
      Devm.getStor sc sevm.currentTarget =
        ((Devm.getStor s sevm.currentTarget).set a.toB256
            (Sevm.argWord sevm 2 + (Devm.getStor s sevm.currentTarget).get a.toB256)).set
          supplySlot
          (Sevm.argWord sevm 2 + (Devm.getStor s sevm.currentTarget).get supplySlot) ∧
      (g :: a.toB256 :: (0 : B256) :: callbackArgsOffset ::
        (0xc4 + ((~~~ (31 : B256)) &&& (31 + Sevm.tailLen sevm 3))) ::
        (0 : B256) :: (0 : B256) :: [Sevm.argWord sevm 2, a.toB256] <<+ sc.stack) ∧
      (∀ bs, Mem.Wf s.memory → Mem.Reads s.memory bs →
        Mem.Wf sc.memory ∧
          Mem.Reads sc.memory
            (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
              (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
                (Bytes.writeAt bs 0 (Sevm.argWord sevm 2).toBytes)
                  0 onFlashLoanSelector.toBytes)
                  32 sevm.caller.toB256.toBytes)
                  64 sevm.currentTarget.toB256.toBytes)
                  96 (Sevm.argWord sevm 2).toBytes)
                  128 (0 : B256).toBytes)
                  160 (0xa0 : B256).toBytes)
                  192 (Sevm.tailLen sevm 3).toBytes)
                  224 (Sevm.tailBytes sevm 3))) ∧
      Func.Run (fmint.main :: fmintAux) sevm sc flashLoanFromCall r := by
  simp only [flashLoan] at h_run
  -- (0) `arg 1 +++ address ::: eq ::: iszero`: `token` must be this contract.
  rcases of_run_prepend (arg 1) _ h_run with ⟨s1, h1, h_run⟩
  have hs1 : Sevm.argWord sevm 1 :: [] <<+ s1.stack := prefix_of_arg nil_pref h1
  have hg : Devm.getStor s = Devm.getStor s1 := Line.of_inv Devm.getStor (by line_inv) h1
  have hgc : Devm.getCode s = Devm.getCode s1 := Line.of_inv Devm.getCode (by line_inv) h1
  have hm : s.memory = s1.memory := Line.of_inv Devm.memory (by line_inv) h1
  clear h1
  rcases of_run_next h_run with ⟨s2, r2, h_run⟩
  have hs2 : sevm.currentTarget.toB256 :: Sevm.argWord sevm 1 :: [] <<+ s2.stack :=
    prefix_of_push (of_run_address r2) hs1
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r2 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r2 Line.Run.nil))
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r2 Line.Run.nil))
  clear r2 hs1
  rcases of_run_next h_run with ⟨s3, r3, h_run⟩
  have hs3 := prefix_of_eq r3 hs2
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r3 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r3 Line.Run.nil))
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r3 Line.Run.nil))
  clear r3 hs2
  rcases of_run_next h_run with ⟨s4, r4, h_run⟩
  have hs4 := prefix_of_iszero r4 hs3
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r4 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r4 Line.Run.nil))
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r4 Line.Run.nil))
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
  have hgc := hgc.trans (funext (fun x => getCode_eq_of_state_eq hp5.state x))
  have hm := hm.trans hp5.memory
  clear hp5 hs4 hp5s h_tokflag
  -- (1) `arg 0 +++ dup 0 ::: checkNonAddress`: the receiver word is address-shaped.
  rcases of_run_prepend (arg 0) _ h_run with ⟨s6, h6, h_run⟩
  have hs6 : Sevm.argWord sevm 0 :: [] <<+ s6.stack := prefix_of_arg hs5 h6
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h6)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h6)
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) h6)
  clear h6 hs5
  rcases of_run_next h_run with ⟨s7, r7, h_run⟩
  have hs7 : [Sevm.argWord sevm 0, Sevm.argWord sevm 0] <<+ s7.stack :=
    prefix_of_dup_val r7 (by show_nth) hs6
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r7 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r7 Line.Run.nil))
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r7 Line.Run.nil))
  clear r7 hs6
  rcases of_run_prepend checkNonAddress _ h_run with ⟨s8, h8, h_run⟩
  rcases of_check_non_address hs7 h8 with ⟨na, hs8, h_va_iff⟩
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h8)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h8)
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) h8)
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
  have hgc := hgc.trans (funext (fun x => getCode_eq_of_state_eq hp9.state x))
  have hm := hm.trans hp9.memory
  clear hs8 hp9s hp9 h_va_iff
  rcases h_va with ⟨a, h_recv⟩
  rw [← h_recv] at hs9
  -- (2) `arg 2 +++ dup 0 ::: pushSupplySlot +++ sload ::: not ::: lt`: the bound.
  rcases of_run_prepend (arg 2) _ h_run with ⟨s10, h10, h_run⟩
  have hs10 : Sevm.argWord sevm 2 :: [a.toB256] <<+ s10.stack := prefix_of_arg hs9 h10
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h10)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h10)
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) h10)
  clear h10 hs9
  rcases of_run_next h_run with ⟨s11, r11, h_run⟩
  have hs11 : [Sevm.argWord sevm 2, Sevm.argWord sevm 2, a.toB256] <<+ s11.stack :=
    prefix_of_dup_val r11 (by show_nth) hs10
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r11 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r11 Line.Run.nil))
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r11 Line.Run.nil))
  clear r11 hs10
  rcases of_run_prepend pushSupplySlot _ h_run with ⟨s12, h12, h_run⟩
  have hs12 : supplySlot ::
      [Sevm.argWord sevm 2, Sevm.argWord sevm 2, a.toB256] <<+ s12.stack := by
    simp only [pushSupplySlot] at h12
    rcases Line.of_run_cons h12 with ⟨sa, ra, h12'⟩
    rcases Line.of_run_cons h12' with ⟨sb, rb, hnil⟩
    cases hnil
    have hpa : (0 : B256) ::
        [Sevm.argWord sevm 2, Sevm.argWord sevm 2, a.toB256] <<+ sa.stack :=
      prefix_of_push (of_run_pushB256 ra) hs11
    have hpb := prefix_of_not rb hpa
    rw [supplySlot_eq_not_zero] at hpb
    exact hpb
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h12)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h12)
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) h12)
  clear h12 hs11
  rcases of_run_next h_run with ⟨s13, r13, h_run⟩
  rcases prefix_of_sload r13 hs12 with ⟨supply, hs13, h_supply⟩
  have h_supply' : supply = (Devm.getStor s sevm.currentTarget).get supplySlot := by
    rw [h_supply]
    show (Devm.getStor s12 sevm.currentTarget).get supplySlot = _
    rw [← congr_fun hg sevm.currentTarget]
  clear h_supply
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r13 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r13 Line.Run.nil))
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r13 Line.Run.nil))
  clear r13 hs12
  rcases of_run_next h_run with ⟨s14, r14, h_run⟩
  have hs14 := prefix_of_not r14 hs13
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r14 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r14 Line.Run.nil))
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r14 Line.Run.nil))
  clear r14 hs13
  rcases of_run_next h_run with ⟨s15, r15, h_run⟩
  have hs15 := prefix_of_lt r15 hs14
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r15 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r15 Line.Run.nil))
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r15 Line.Run.nil))
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
  have h_nof : B256.Nof ((Devm.getStor s sevm.currentTarget).get supplySlot)
      (Sevm.argWord sevm 2) := h_supply' ▸ B256.nof_of_le_not h_bound
  rw [h_boundflag] at hs15
  have hs16 : [Sevm.argWord sevm 2, a.toB256] <<+ s16.stack := cons_pref_cons_inv hs15
  have hg := hg.trans (funext (fun x => (Devm.PopBurn.getStor hp16 x).symm))
  have hgc := hgc.trans (funext (fun x => getCode_eq_of_state_eq hp16.state x))
  have hm := hm.trans hp16.memory
  clear hs15 hp16s hp16 h_boundflag h_bound h_supply'
  -- (3) the mint pair.  Nothing between the two `SSTORE`s below transfers
  -- control out of this frame or halts successfully — D5's ordering discipline,
  -- read off the walk rather than assumed.
  rcases of_run_next h_run with ⟨s17, r17, h_run⟩
  have hs17 : a.toB256 :: [Sevm.argWord sevm 2, a.toB256] <<+ s17.stack :=
    prefix_of_dup_val r17 (by show_nth) hs16
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r17 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r17 Line.Run.nil))
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r17 Line.Run.nil))
  clear r17 hs16
  rcases of_run_next h_run with ⟨s18, r18, h_run⟩
  rcases prefix_of_sload r18 hs17 with ⟨rbal, hs18, h_rbal⟩
  have h_rbal' : rbal = (Devm.getStor s sevm.currentTarget).get a.toB256 := by
    rw [h_rbal]
    show (Devm.getStor s17 sevm.currentTarget).get a.toB256 = _
    rw [← congr_fun hg sevm.currentTarget]
  clear h_rbal
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r18 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r18 Line.Run.nil))
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r18 Line.Run.nil))
  clear r18 hs17
  rcases of_run_next h_run with ⟨s19, r19, h_run⟩
  have hs19 : Sevm.argWord sevm 2 :: rbal :: [Sevm.argWord sevm 2, a.toB256] <<+ s19.stack :=
    prefix_of_dup_val r19 (by show_nth) hs18
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r19 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r19 Line.Run.nil))
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r19 Line.Run.nil))
  clear r19 hs18
  rcases of_run_next h_run with ⟨s20, r20, h_run⟩
  have hs20 : (Sevm.argWord sevm 2 + rbal) :: [Sevm.argWord sevm 2, a.toB256] <<+ s20.stack :=
    prefix_of_add r20 hs19
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r20 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r20 Line.Run.nil))
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r20 Line.Run.nil))
  clear r20 hs19
  rcases of_run_next h_run with ⟨s21, r21, h_run⟩
  have hs21 : a.toB256 :: (Sevm.argWord sevm 2 + rbal) ::
      [Sevm.argWord sevm 2, a.toB256] <<+ s21.stack :=
    prefix_of_dup_val r21 (by show_nth) hs20
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r21 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r21 Line.Run.nil))
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r21 Line.Run.nil))
  clear r21 hs20
  -- the balance-side `SSTORE`
  rcases of_run_next h_run with ⟨s22, r22, h_run⟩
  have h_set1 : Devm.getStor s22 sevm.currentTarget
      = (Devm.getStor s21 sevm.currentTarget).set a.toB256 (Sevm.argWord sevm 2 + rbal) :=
    sstore_getStor_set r22 hs21
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r22 Line.Run.nil))
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r22 Line.Run.nil))
  have hs22 : [Sevm.argWord sevm 2, a.toB256] <<+ s22.stack := prefix_of_sstore r22 hs21
  clear r22 hs21
  rcases of_run_prepend pushSupplySlot _ h_run with ⟨s23, h23, h_run⟩
  have hs23 : supplySlot :: [Sevm.argWord sevm 2, a.toB256] <<+ s23.stack := by
    simp only [pushSupplySlot] at h23
    rcases Line.of_run_cons h23 with ⟨sa, ra, h23'⟩
    rcases Line.of_run_cons h23' with ⟨sb, rb, hnil⟩
    cases hnil
    have hpa : (0 : B256) :: [Sevm.argWord sevm 2, a.toB256] <<+ sa.stack :=
      prefix_of_push (of_run_pushB256 ra) hs22
    have hpb := prefix_of_not rb hpa
    rw [supplySlot_eq_not_zero] at hpb
    exact hpb
  have hg2 : Devm.getStor s22 = Devm.getStor s23 :=
    Line.of_inv Devm.getStor (by line_inv) h23
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h23)
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) h23)
  clear h23 hs22
  rcases of_run_next h_run with ⟨s24, r24, h_run⟩
  rcases prefix_of_sload r24 hs23 with ⟨supply2, hs24, h_supply2⟩
  have h_supply2' : supply2 = ((Devm.getStor s sevm.currentTarget).set a.toB256
      (Sevm.argWord sevm 2 + (Devm.getStor s sevm.currentTarget).get a.toB256)).get
        supplySlot := by
    rw [h_supply2]
    show (Devm.getStor s23 sevm.currentTarget).get supplySlot = _
    rw [← congr_fun hg2 sevm.currentTarget, h_set1, ← congr_fun hg sevm.currentTarget,
      h_rbal']
  clear h_supply2
  have hg2 := hg2.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r24 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r24 Line.Run.nil))
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r24 Line.Run.nil))
  clear r24 hs23
  rcases of_run_next h_run with ⟨s25, r25, h_run⟩
  have hs25 : Sevm.argWord sevm 2 :: supply2 :: [Sevm.argWord sevm 2, a.toB256]
      <<+ s25.stack := prefix_of_dup_val r25 (by show_nth) hs24
  have hg2 := hg2.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r25 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r25 Line.Run.nil))
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r25 Line.Run.nil))
  clear r25 hs24
  rcases of_run_next h_run with ⟨s26, r26, h_run⟩
  have hs26 : (Sevm.argWord sevm 2 + supply2) :: [Sevm.argWord sevm 2, a.toB256]
      <<+ s26.stack := prefix_of_add r26 hs25
  have hg2 := hg2.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r26 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r26 Line.Run.nil))
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r26 Line.Run.nil))
  clear r26 hs25
  rcases of_run_prepend pushSupplySlot _ h_run with ⟨s27, h27, h_run⟩
  have hs27 : supplySlot :: (Sevm.argWord sevm 2 + supply2) ::
      [Sevm.argWord sevm 2, a.toB256] <<+ s27.stack := by
    simp only [pushSupplySlot] at h27
    rcases Line.of_run_cons h27 with ⟨sa, ra, h27'⟩
    rcases Line.of_run_cons h27' with ⟨sb, rb, hnil⟩
    cases hnil
    have hpa : (0 : B256) :: (Sevm.argWord sevm 2 + supply2) ::
        [Sevm.argWord sevm 2, a.toB256] <<+ sa.stack :=
      prefix_of_push (of_run_pushB256 ra) hs26
    have hpb := prefix_of_not rb hpa
    rw [supplySlot_eq_not_zero] at hpb
    exact hpb
  have hg2 := hg2.trans (Line.of_inv Devm.getStor (by line_inv) h27)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h27)
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) h27)
  clear h27 hs26
  -- the supply-side `SSTORE`: the pair is complete, and it is complete *here*,
  -- before any external control transfer.
  rcases of_run_next h_run with ⟨s28, r28, h_run⟩
  have h_set2 : Devm.getStor s28 sevm.currentTarget
      = (Devm.getStor s27 sevm.currentTarget).set supplySlot
          (Sevm.argWord sevm 2 + supply2) :=
    sstore_getStor_set r28 hs27
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r28 Line.Run.nil))
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r28 Line.Run.nil))
  have hs28 : [Sevm.argWord sevm 2, a.toB256] <<+ s28.stack := prefix_of_sstore r28 hs27
  clear r28 hs27
  have h_mint : Devm.getStor s28 sevm.currentTarget =
      ((Devm.getStor s sevm.currentTarget).set a.toB256
          (Sevm.argWord sevm 2 + (Devm.getStor s sevm.currentTarget).get a.toB256)).set
        supplySlot
        (Sevm.argWord sevm 2 + (Devm.getStor s sevm.currentTarget).get supplySlot) := by
    rw [h_set2, ← congr_fun hg2 sevm.currentTarget, h_set1,
      ← congr_fun hg sevm.currentTarget, h_rbal', h_supply2',
      Stor.get_supplySlot_set ⟨a, rfl⟩]
  clear h_set1 h_set2 h_supply2' h_rbal' hg hg2
  -- (4) the mint `Transfer` event
  rcases of_run_next h_run with ⟨s29, r29, h_run⟩
  have hs29 : Sevm.argWord sevm 2 :: [Sevm.argWord sevm 2, a.toB256] <<+ s29.stack :=
    prefix_of_dup_val r29 (by show_nth) hs28
  have hg3 : Devm.getStor s28 = Devm.getStor s29 :=
    Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r29 Line.Run.nil)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r29 Line.Run.nil))
  have hm := hm.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r29 Line.Run.nil))
  clear r29 hs28
  rcases of_run_prepend (mstoreAt 0) _ h_run with ⟨s30, h30, h_run⟩
  rcases of_run_mstoreAt_val h30 hs29 with ⟨hs30, hmA⟩
  have hmA : s30.memory = s29.memory.write 0 (Sevm.argWord sevm 2).toBytes := by
    rw [hmA]; rfl
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) h30)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h30)
  clear h30 hs29
  rcases of_run_next h_run with ⟨s31, r31, h_run⟩
  have hs31 : a.toB256 :: [Sevm.argWord sevm 2, a.toB256] <<+ s31.stack :=
    prefix_of_dup_val r31 (by show_nth) hs30
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r31 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r31 Line.Run.nil))
  have hmB : s30.memory = s31.memory :=
    Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r31 Line.Run.nil)
  clear r31 hs30
  rcases of_run_next h_run with ⟨s32, r32, h_run⟩
  have hs32 : (0 : B256) :: a.toB256 :: [Sevm.argWord sevm 2, a.toB256] <<+ s32.stack :=
    prefix_of_push (of_run_pushB256 r32) hs31
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r32 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r32 Line.Run.nil))
  have hmB := hmB.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r32 Line.Run.nil))
  clear r32 hs31
  rcases of_run_next h_run with ⟨s33, r33, h_run⟩
  have hs33 : transferEvent :: (0 : B256) :: a.toB256 ::
      [Sevm.argWord sevm 2, a.toB256] <<+ s33.stack :=
    prefix_of_push (of_run_pushB256 r33) hs32
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r33 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r33 Line.Run.nil))
  have hmB := hmB.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r33 Line.Run.nil))
  clear r33 hs32
  rcases of_run_prepend (logWith 2 0 1) _ h_run with ⟨s34, h34, h_run⟩
  have hs34 : [Sevm.argWord sevm 2, a.toB256] <<+ s34.stack := of_logWith201 hs33 h34
  -- `LOG` only *extends* memory: it reads a window and records it, and the
  -- backing array is untouched, so both `Mem.Wf` and the image cross it.
  have hmC : ∃ mi sz, s34.memory = s33.memory.extend mi sz := by
    simp only [logWith] at h34
    rcases Line.of_run_cons h34 with ⟨v1, w1, h34'⟩
    rcases Line.of_run_cons h34' with ⟨v2, w2, h34''⟩
    rcases Line.of_run_cons h34'' with ⟨v3, w3, hnil⟩
    cases hnil
    rcases of_run_log_mem w3 with ⟨mi, sz, hlog⟩
    exact ⟨mi, sz, by
      rw [hlog, ← (of_run_pushB256 w2).memory, ← (of_run_pushB256 w1).memory]⟩
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) h34)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h34)
  clear h34 hs33
  -- (5) assemble the callback frame.  The seven `CALL` operands go on
  -- deepest-first, which is why the two return-window zeros are pushed before
  -- the argument window is even measured.
  rcases of_run_next h_run with ⟨s35, r35, h_run⟩
  have hs35 : Sevm.argWord sevm 2 :: [Sevm.argWord sevm 2, a.toB256] <<+ s35.stack :=
    prefix_of_dup_val r35 (by show_nth) hs34
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r35 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r35 Line.Run.nil))
  have hmD : s34.memory = s35.memory :=
    Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r35 Line.Run.nil)
  clear r35 hs34
  rcases of_run_prepend storeCallbackHead _ h_run with ⟨s36, h36, h_run⟩
  rcases of_storeCallbackHead_val hs35 h36 with ⟨hs36, hmE⟩
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) h36)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h36)
  clear h36 hs35
  rcases of_run_prepend (pushList [0, 0]) _ h_run with ⟨s37, h37, h_run⟩
  have hs37 : (0 : B256) :: (0 : B256) :: [Sevm.argWord sevm 2, a.toB256] <<+ s37.stack := by
    simp only [pushList, List.map] at h37
    rcases Line.of_run_cons h37 with ⟨u1, q1, h37'⟩
    rcases Line.of_run_cons h37' with ⟨u2, q2, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 q2)
      (prefix_of_push (of_run_pushB256 q1) hs36)
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) h37)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h37)
  have hmF : s36.memory = s37.memory := Line.of_inv Devm.memory (by line_inv) h37
  clear h37 hs36
  rcases of_run_prepend forwardCallbackData _ h_run with ⟨s38, h38, h_run⟩
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) h38)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h38)
  simp only [forwardCallbackData] at h38
  rcases of_forwardArgTail_val hs37 h38 with ⟨hs38, hmG⟩
  have hmG : s38.memory =
      (s37.memory.write 192 (Sevm.tailLen sevm 3).toBytes).write
        224 (Sevm.tailBytes sevm 3) := by rw [hmG]; rfl
  clear h38 hs37
  rcases of_run_prepend callbackArgsSize _ h_run with ⟨s39, h39, h_run⟩
  have hs39 := of_callbackArgsSize_val hs38 h39
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) h39)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h39)
  have hmH : s38.memory = s39.memory := Line.of_inv Devm.memory (by line_inv) h39
  clear h39 hs38
  rcases of_run_next h_run with ⟨s40, r40, h_run⟩
  have hs40 := prefix_of_push (of_run_pushB256 r40) hs39
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r40 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r40 Line.Run.nil))
  have hmH := hmH.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r40 Line.Run.nil))
  clear r40 hs39
  rcases of_run_next h_run with ⟨s41, r41, h_run⟩
  have hs41 := prefix_of_push (of_run_pushB256 r41) hs40
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r41 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r41 Line.Run.nil))
  have hmH := hmH.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r41 Line.Run.nil))
  clear r41 hs40
  rcases of_run_next h_run with ⟨s42, r42, h_run⟩
  have hs42 : a.toB256 :: (0 : B256) :: callbackArgsOffset ::
      (0xc4 + ((~~~ (31 : B256)) &&& (31 + Sevm.tailLen sevm 3))) ::
      (0 : B256) :: (0 : B256) :: [Sevm.argWord sevm 2, a.toB256] <<+ s42.stack :=
    prefix_of_dup_val r42 (by show_nth) hs41
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r42 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r42 Line.Run.nil))
  have hmH := hmH.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r42 Line.Run.nil))
  clear r42 hs41
  rcases of_run_next h_run with ⟨s43, r43, h_run⟩
  rcases of_run_gas r43 with ⟨g, pb43⟩
  have hs43 : g :: a.toB256 :: (0 : B256) :: callbackArgsOffset ::
      (0xc4 + ((~~~ (31 : B256)) &&& (31 + Sevm.tailLen sevm 3))) ::
      (0 : B256) :: (0 : B256) :: [Sevm.argWord sevm 2, a.toB256] <<+ s43.stack :=
    prefix_of_push pb43 hs42
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r43 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r43 Line.Run.nil))
  have hmH := hmH.trans (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r43 Line.Run.nil))
  clear r43 pb43 hs42
  refine ⟨h_token, h_nof, a, s43, g, h_recv.symm, hgc, ?_, hs43, ?_, h_run⟩
  · rw [← congr_fun hg3 sevm.currentTarget]
    exact h_mint
  · intro bs hwf hr
    obtain ⟨mi, sz, hmC⟩ := hmC
    rw [← hmH, hmG, ← hmF, hmE, ← hmD, hmC, ← hmB, hmA, ← hm]
    have w1 := hwf.write 0 (Sevm.argWord sevm 2).toBytes
    have r1 := hr.write hwf 0 (Sevm.argWord sevm 2).toBytes
    have w2 := w1.extend mi sz
    have r2 := r1.extend mi sz
    have w3 := w2.write 0 onFlashLoanSelector.toBytes
    have r3 := r2.write w2 0 onFlashLoanSelector.toBytes
    have w4 := w3.write 32 sevm.caller.toB256.toBytes
    have r4 := r3.write w3 32 sevm.caller.toB256.toBytes
    have w5 := w4.write 64 sevm.currentTarget.toB256.toBytes
    have r5 := r4.write w4 64 sevm.currentTarget.toB256.toBytes
    have w6 := w5.write 96 (Sevm.argWord sevm 2).toBytes
    have r6 := r5.write w5 96 (Sevm.argWord sevm 2).toBytes
    have w7 := w6.write 128 (0 : B256).toBytes
    have r7 := r6.write w6 128 (0 : B256).toBytes
    have w8 := w7.write 160 (0xa0 : B256).toBytes
    have r8 := r7.write w7 160 (0xa0 : B256).toBytes
    have w9 := w8.write 192 (Sevm.tailLen sevm 3).toBytes
    have r9 := r8.write w8 192 (Sevm.tailLen sevm 3).toBytes
    exact ⟨w9.write 224 (Sevm.tailBytes sevm 3),
      r9.write w9 224 (Sevm.tailBytes sevm 3)⟩

/-- **`flashLoan`'s three guards, on their own.**

The guard content of `of_flashLoan_toCall`, restated without the mint equation
or the callback's operand stack — the form the no-success corollaries want, and
the one that makes each guard readable as the property it enforces.

Guard (1) appears here as `ValidAdr`; `of_flashLoan_toCall` already delivers the
`Adr` it names, which is what the callee identity needs. -/
theorem flashLoan_guards {sevm : Sevm} {s r : Devm}
    (h_run : Func.Run (fmint.main :: fmintAux) sevm s flashLoan r) :
    Sevm.argWord sevm 1 = sevm.currentTarget.toB256 ∧
    ValidAdr (Sevm.argWord sevm 0) ∧
    B256.Nof ((Devm.getStor s sevm.currentTarget).get supplySlot)
      (Sevm.argWord sevm 2) := by
  rcases of_flashLoan_toCall h_run with ⟨h_token, h_nof, a, _, _, h_recv, -⟩
  exact ⟨h_token, ⟨a, h_recv.symm⟩, h_nof⟩

end Fmint

end Blanc
