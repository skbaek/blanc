-- FlashSpec.lean : fmint's `flashLoan` success specification (Arc C of the
-- flashmint program, `~/plans/fmint-flashloan.md`).
--
-- The entry route (`exec_enters_flashLoan`) composes `correct` with dispatch
-- reachability, taking a successful top-level `Exec` at fmint's code to a run
-- of `flashLoan`'s body.  On top of it: the forward walk to the `CALL`, the
-- callback's calldata image, `CallbackBoundary`, the repayment postcondition,
-- and then the headline `fmint_flashLoan_spec` with its seven `no_success_of_*`
-- corollaries.  A final section adds the frame-level restoration family
-- (`~/plans/fmint-restoration.md`): `rollback_of_callback_failure` at the
-- borrower's frame, and the shared `Blanc.rollback_of_no_success` with its
-- seven instantiations at fmint's own message frame.  Those name a FRAME and
-- never a transaction.
--
-- Everything here is PARTIAL CORRECTNESS and never liveness: every theorem
-- takes a successful run as a hypothesis and reads facts off it.  Nothing in
-- this module -- or anywhere in this repository -- says a `flashLoan` call ever
-- succeeds.
--
-- This module is fmint-owned (`scripts/check-layering.py`, `CONTRACTS`): it
-- may import `Blanc.Fmint` and `Blanc.Conserved`, and must not import any
-- WETH module.

import Blanc.Fmint
import Blanc.Conserved
import Blanc.CommonProofs
import Blanc.Ladder

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
balances, code images *and memory* unchanged from `pre` — followed by a run of
`Fmint.flashLoan` from `s'` to the same `post`.

The memory conjunct is what lets a caller state a frame-freshness premise at
`pre`, the frame's own initial state, instead of at an intermediate state it
cannot name: the entry burn, `fsig` and the dispatcher are all memory-silent.

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
      s'.memory = pre.memory ∧
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
    with ⟨s', _, h_state, h_smem, h_runf⟩
  refine ⟨s', ?_, ?_, ?_, ?_, h_runf⟩
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
  · have h2 : s₀.memory = s₁.memory := Line.of_inv Devm.memory (by line_inv) h₁
    rw [← h_smem, ← h2, ← burn.memory]

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

/-! ## The callback's calldata, as the ABI encoding

`of_flashLoan_toCall` says what the frame's memory *is*, as a chain of writes
over an arbitrary starting image.  This section instantiates that chain at the
empty image and shows the window the `CALL` hands the callback equals the
canonical encoding of `onFlashLoan(caller, this, amount, 0, data)` — the
equation the arc's fixed decision 2 demands, with `abiCallWithTail` written from
the five arguments in `Blanc/CommonCore.lean` and never from the contract's own
stores. -/

/-- The `argsSize` the code computes, as the length the encoding has. -/
lemma toNat_callbackArgsSize {len : Nat} (h : 196 + ceil32 len < 2 ^ 256) :
    ((0xc4 : B256) + ((~~~ (31 : B256)) &&& (31 + Nat.toB256 len))).toNat
      = 196 + ceil32 len := by
  have hlen : 31 + len < 2 ^ 256 := by
    have := Nat.le_ceil32 len
    omega
  rw [B256.toNat_add, B256.toNat_ceil32 hlen,
    show B256.toNat 0xc4 = 196 from rfl, Nat.lo_eq_of_lt h]

/-- The write chain of `of_flashLoan_toCall`, at the empty starting image.

The mint's `Transfer` word at `0x00` is overwritten by the selector, and every
later store lands exactly at the end of what is there — which is what the layout
table at `Blanc/Fmint.lean` asserts, now as an equation between byte lists. -/
lemma callbackImage_nil (sel cal slf amt lenw : B256) (payload : Bytes) :
    Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
        (Bytes.writeAt [] 0 amt.toBytes) 0 sel.toBytes) 32 cal.toBytes)
        64 slf.toBytes) 96 amt.toBytes) 128 (0 : B256).toBytes)
        160 (0xa0 : B256).toBytes) 192 lenw.toBytes) 224 payload
      = sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes ++
        (0 : B256).toBytes ++ (0xa0 : B256).toBytes ++ lenw.toBytes ++ payload := by
  have hlen : ∀ x : B256, (B256.toBytes x).length = 32 := B256.length_toBytes
  have e0 : Bytes.writeAt ([] : Bytes) 0 amt.toBytes = amt.toBytes :=
    Bytes.writeAt_zero_of_le (by simp)
  have e1 : Bytes.writeAt amt.toBytes 0 sel.toBytes = sel.toBytes :=
    Bytes.writeAt_zero_of_le (by rw [hlen, hlen])
  have e2 : Bytes.writeAt sel.toBytes 32 cal.toBytes = sel.toBytes ++ cal.toBytes :=
    Bytes.writeAt_of_length_eq (hlen sel)
  have e3 : Bytes.writeAt (sel.toBytes ++ cal.toBytes) 64 slf.toBytes
      = sel.toBytes ++ cal.toBytes ++ slf.toBytes :=
    Bytes.writeAt_of_length_eq (by simp [hlen])
  have e4 : Bytes.writeAt (sel.toBytes ++ cal.toBytes ++ slf.toBytes) 96 amt.toBytes
      = sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes :=
    Bytes.writeAt_of_length_eq (by simp [hlen])
  have e5 : Bytes.writeAt (sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes)
      128 (0 : B256).toBytes
      = sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes ++ (0 : B256).toBytes :=
    Bytes.writeAt_of_length_eq (by simp [hlen])
  have e6 : Bytes.writeAt (sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes ++
      (0 : B256).toBytes) 160 (0xa0 : B256).toBytes
      = sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes ++ (0 : B256).toBytes ++
        (0xa0 : B256).toBytes :=
    Bytes.writeAt_of_length_eq (by simp [hlen])
  have e7 : Bytes.writeAt (sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes ++
      (0 : B256).toBytes ++ (0xa0 : B256).toBytes) 192 lenw.toBytes
      = sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes ++ (0 : B256).toBytes ++
        (0xa0 : B256).toBytes ++ lenw.toBytes :=
    Bytes.writeAt_of_length_eq (by simp [hlen])
  have e8 : Bytes.writeAt (sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes ++
      (0 : B256).toBytes ++ (0xa0 : B256).toBytes ++ lenw.toBytes) 224 payload
      = sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes ++ (0 : B256).toBytes ++
        (0xa0 : B256).toBytes ++ lenw.toBytes ++ payload :=
    Bytes.writeAt_of_length_eq (by simp [hlen])
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8]

/-- **The window equals the encoding.**

Three of the table's claims are used here and nowhere else.  The selector is
right-aligned in word `0`, so the window starting at `0x1c` drops exactly the 28
leading zero bytes and `List.drop 28 (B256.toBytes sel)` is `abiSelectorBytes
sel` *by definition*.  The offset word is `0xa0` because offsets count from the
start of the argument area, which is `32 * (4 + 1)` for four heads.  And the
window runs `ceil32 len - len` bytes past the payload: those positions read as
`0` because `Mem.Reads` compares with `getD` on both sides, which is exactly
`abiBytesTail`'s padding — derived, not assumed. -/
lemma callbackWindow (sel cal slf amt : B256) (payload : Bytes) :
    (sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes ++ (0 : B256).toBytes ++
      (0xa0 : B256).toBytes ++ (Nat.toB256 payload.length).toBytes ++ payload).sliceD
        28 (196 + ceil32 payload.length) 0
      = abiCallWithTail sel [cal, slf, amt, 0] payload := by
  have hlen : ∀ x : B256, (B256.toBytes x).length = 32 := B256.length_toBytes
  have hce : payload.length ≤ ceil32 payload.length := Nat.le_ceil32 _
  have himg : (sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes ++
      (0 : B256).toBytes ++ (0xa0 : B256).toBytes ++
      (Nat.toB256 payload.length).toBytes ++ payload)
      = sel.toBytes ++ (cal.toBytes ++ slf.toBytes ++ amt.toBytes ++
        (0 : B256).toBytes ++ (0xa0 : B256).toBytes ++
        (Nat.toB256 payload.length).toBytes ++ payload) := by
    simp [List.append_assoc]
  unfold List.sliceD
  rw [himg, List.drop_append_of_le_length (by rw [hlen]; omega)]
  rw [List.takeD_of_length_le]
  · simp only [abiCallWithTail, abiBytesTail, abiSelectorBytes, List.map, List.flatten,
      List.length_cons, List.length_nil, List.append_assoc, List.length_append, hlen,
      List.length_drop]
    rw [show 196 + ceil32 payload.length -
        (32 - 28 + (32 + (32 + (32 + (32 + (32 + (32 + payload.length)))))))
          = ceil32 payload.length - payload.length from by omega]
    norm_num
    rfl
  · simp only [List.length_append, List.length_drop, hlen]
    omega

/-- **The callback's calldata image**, and this step's closing statement.

`of_flashLoan_toCall`'s conclusion with its universally quantified memory
conjunct discharged: the window `[0x1c, 0x1c + argsSize)` that the `CALL` hands
the callback *is* `onFlashLoan(caller, this, amount, 0, data)`, canonically
encoded.

**Three premises, each of them real.**

* `h_dec` — the calldata is a canonical encoding of
  `flashLoan(receiver, token, amount, data)`.  Fixed decision 1c: a
  non-canonical encoding is decodable by this contract, which validates no
  offset, but is out of scope here and this theorem says nothing about it.
* `h_size` — `196 + ceil32 data.length < 2 ^ 256`.  The same family as
  `tailBytes_three_of_decodes`'s bound: `List.length` is an unbounded `Nat`
  while the machine word is 256 bits, so a longer payload would not round-trip
  through any encoder and its `argsSize` would not be its length.
* `h_wf` and `h_fresh` — **frame freshness**, and it is a premise rather than a
  fact about the walk.  `Exec 0 sevm pre` quantifies `pre` freely and does not
  know it came from Jaune's `initDevm`, which is where `memory := .empty`
  actually comes from; `Mem.wf_empty` and `Mem.reads_empty` discharge both at
  the frame boundary.  Zero-*initialisation* is not assumed here — that is
  `Mem.Reads`'s `getD`-on-both-sides shape, and it is what makes the padding a
  theorem.  What is assumed is only that no earlier writer of *this frame* left
  bytes above the payload.

Note what is *not* premised: nothing here says a `flashLoan` call ever
succeeds.  The run is a hypothesis and this reads facts off it. -/
theorem flashLoan_callback_image {sevm : Sevm} {s r : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf s.memory) (h_fresh : Mem.Reads s.memory [])
    (h_run : Func.Run (fmint.main :: fmintAux) sevm s flashLoan r) :
    token = sevm.currentTarget.toB256 ∧
    B256.Nof ((Devm.getStor s sevm.currentTarget).get supplySlot) amount ∧
    ∃ (a : Adr) (sc : Devm) (g : B256),
      receiver = a.toB256 ∧
      Devm.getCode s = Devm.getCode sc ∧
      Devm.getStor sc sevm.currentTarget =
        ((Devm.getStor s sevm.currentTarget).set a.toB256
            (amount + (Devm.getStor s sevm.currentTarget).get a.toB256)).set
          supplySlot (amount + (Devm.getStor s sevm.currentTarget).get supplySlot) ∧
      (g :: a.toB256 :: (0 : B256) :: callbackArgsOffset ::
        Nat.toB256 (196 + ceil32 data.length) ::
        (0 : B256) :: (0 : B256) :: [amount, a.toB256] <<+ sc.stack) ∧
      (sc.memory.read callbackArgsOffset.toNat (196 + ceil32 data.length)).1
        = abiCallWithTail onFlashLoanSelector
            [sevm.caller.toB256, sevm.currentTarget.toB256, amount, 0] data ∧
      Func.Run (fmint.main :: fmintAux) sevm sc flashLoanFromCall r := by
  have hdlen : data.length < 2 ^ 256 := by
    have := Nat.le_ceil32 data.length
    omega
  have h0 : Sevm.argWord sevm 0 = receiver := argWord_zero_of_decodes h_dec
  have h1 : Sevm.argWord sevm 1 = token := argWord_one_of_decodes h_dec
  have h2 : Sevm.argWord sevm 2 = amount := argWord_two_of_decodes h_dec
  have htl : Sevm.tailLen sevm 3 = Nat.toB256 data.length := tailLen_three_of_decodes h_dec
  have htb : Sevm.tailBytes sevm 3 = data := tailBytes_three_of_decodes hdlen h_dec
  have hsize : (0xc4 : B256) + ((~~~ (31 : B256)) &&& (31 + Nat.toB256 data.length))
      = Nat.toB256 (196 + ceil32 data.length) := by
    rw [← toB256_toNat ((0xc4 : B256) + _), toNat_callbackArgsSize h_size]
  obtain ⟨h_token, h_nof, a, sc, g, h_recv, h_code, h_stor, h_stack, h_mem, h_res⟩ :=
    of_flashLoan_toCall h_run
  rw [h0] at h_recv
  rw [h1] at h_token
  rw [h2] at h_nof h_stor h_stack h_mem
  rw [htl, hsize] at h_stack
  refine ⟨h_token, h_nof, a, sc, g, h_recv, h_code, h_stor, h_stack, ?_, h_res⟩
  obtain ⟨-, h_reads⟩ := h_mem [] h_wf h_fresh
  rw [htl, htb, callbackImage_nil] at h_reads
  rw [show callbackArgsOffset.toNat = 28 from rfl, Mem.Reads.read h_reads,
    callbackWindow]

/-! ## The callback boundary

The relation the proposal names (`~/plans/flashmint-proposal.md`, headline 2):
a successful `flashLoan` actually opened a child frame against the named
receiver, handed it the canonically encoded `onFlashLoan` call, and resumed
from a clean child whose returndata leads with the ERC-3156 magic word. -/

/-- **`CallbackBoundary`**: between `pre`, `fa`'s frame at the `CALL`, and
`mid`, the same frame at resumption, a callback to `receiver` happened — and
`mid` is the resumption from *exactly that call*, which is what makes the
relation non-vacuous.  The witnesses are pinned by equations, not merely
asserted to exist: `parent` is `pre` minus the seven popped operands (the
stack equation) with `pre`'s world (the state equation); the child message is
the literal `callMsg` the `CALL` step builds, with its calldata pinned to the
independently defined encoder `abiCallWithTail` — never to "whatever the
window contained"; `child` is the settled result of running that message in
the filled slot `xl`; and `mid` is `(Resume.call parent 0 0).run (.ok child)`
— an equation that also pins `parent`'s memory through `mid`'s.

Clause by clause:

* **the operands** — the stack equation records gas `gw`, the callee word
  `receiver.toB256`, value `0`, fmint's fixed `[0x1c, 0x1c + argsSize)`
  argument window and the empty return window;
* **the callee** — `callMsg`'s `currentTarget` and `codeAddress` are
  `receiver`, entered from `caller = fa`.  The code the child ran is the
  receiver's own *unless* the receiver is an EIP-7702 delegation designator,
  in which case it is the designated account's — the delegation case is
  **covered as an explicit disjunct**, not excluded, because the callee is
  arbitrary borrower code and nothing rules a designator out;
* **the calldata** — the canonical ABI encoding of
  `onFlashLoan(sevm.caller, fa, amount, 0, data)`, and the value is `0`;
* **the gas** — EIP-150's grant, `min` of the request and the 63/64
  remainder: the relation does not claim "all gas" because the machine does
  not forward all gas;
* **success** — the frame actually ran (`Xlot.Filled`, `ProcessMessage` to
  `.ok child`) and settled with no error, which excludes the four no-frame
  failure modes and the in-frame rollback;
* **the returndata** — at least one word, and its head word is
  `erc3156Magic`.

A precompile receiver is *not* excluded: whether the answer came from a
precompile or from executing the resolved code is made explicit by
`CallbackBoundary.entry_modes` below.

**Hypothesis position.**  The relation is proved *from* a successful run; it
never asserts that any `flashLoan` succeeds. -/
def CallbackBoundary (sevm : Sevm) (fa receiver : Adr) (amount : B256)
    (data : Bytes) (pre mid : Devm) : Prop :=
  ∃ (parent child : Devm) (xl : Xlot) (dp : Bool) (code : ByteArray)
    (gw : B256) (avail : Nat),
    pre.stack = gw :: receiver.toB256 :: (0 : B256) :: callbackArgsOffset ::
      Nat.toB256 (196 + ceil32 data.length) :: (0 : B256) :: (0 : B256) ::
      parent.stack ∧
    parent.state = pre.state ∧
    ((getDelegatedCodeAddress (pre.getCode receiver) = none ∧
        code = pre.getCode receiver ∧ dp = false) ∨
      (∃ d, getDelegatedCodeAddress (pre.getCode receiver) = some d ∧
        code = pre.getCode d ∧ dp = true)) ∧
    Xlot.Filled xl ∧
    ProcessMessage
      (callMsg sevm parent (min gw.toNat (except64th avail)) 0 fa receiver
        receiver true false
        (abiCallWithTail onFlashLoanSelector
          [sevm.caller.toB256, fa.toB256, amount, 0] data)
        code dp)
      xl (.ok child) ∧
    child.error.isSome = false ∧
    32 ≤ child.output.length ∧
    Bytes.toB256 (child.output.sliceD 0 32 0) = erc3156Magic ∧
    (Resume.call parent 0 0).run (.ok child) = .ok mid ∧
    mid.state = child.state ∧
    mid.returnData = child.output ∧
    mid.stack = (1 : B256) :: parent.stack

/-- **The two entry modes, the precompile case explicit.**  The frame the
boundary names was answered either by a precompile — possible only when the
receiver is a precompile address and its code is not a delegation designator,
since a delegated callee runs with precompiles disabled — or by an actual
sub-execution of the resolved code on the encoded `onFlashLoan` calldata, in
the receiver's own storage context, from `fa`, with value `0`.

The plan requires this case split to be explicit rather than buried in
`ProcessMessage`: a precompile receiver *can* satisfy the magic-word check as
far as this relation knows (proving otherwise would force `String.keccak`,
which is barred), so it is carried, not excluded. -/
lemma CallbackBoundary.entry_modes {sevm : Sevm} {fa receiver : Adr}
    {amount : B256} {data : Bytes} {pre mid : Devm}
    (h : CallbackBoundary sevm fa receiver amount data pre mid) :
    (sevm.benvStat.rules.isPrecomp receiver ∧
      getDelegatedCodeAddress (pre.getCode receiver) = none) ∨
    (∃ (evm : Evm) (ex : Execution),
      Nonempty (Exec evm.pc evm.sta evm.dyna ex) ∧
      evm.sta.currentTarget = receiver ∧
      evm.sta.caller = fa ∧
      evm.sta.value = 0 ∧
      evm.sta.data = abiCallWithTail onFlashLoanSelector
        [sevm.caller.toB256, fa.toB256, amount, 0] data) := by
  obtain ⟨parent, child, xl, dp, code, gw, avail, -, -, h_del, h_fill,
    run_pm, -, -, -, -, -, -, -⟩ := h
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp run_pm
  unfold FrameBody at hbody
  rcases eq_bt : Msg.benvAfterTransfer
      (callMsg sevm parent (min gw.toNat (except64th avail)) 0 fa receiver
        receiver true false
        (abiCallWithTail onFlashLoanSelector
          [sevm.caller.toB256, fa.toB256, amount, 0] data)
        code dp) with e | benv' <;>
    rw [eq_bt] at hbody
  · rw [hbody.2, processMessage.settle_error] at hset
    cases hset
  have run_ec : ExecuteCode _ xl r0 := hbody
  rcases of_executeCode_someCode (adr := receiver) rfl run_ec with
    ⟨h_prec, h_xl_none, -⟩ | ⟨-, ex', h_xl_some, -⟩
  · -- answered by a precompile
    left
    rcases of_benvAfterTransfer rfl eq_bt with ⟨st_mid, -, hB⟩
    rcases Bool.and_eq_true_iff.mp h_prec with ⟨hdp, hpre⟩
    have hstat : benv'.stat = sevm.benvStat := by
      rw [hB]
      rfl
    constructor
    · have := of_decide_eq_true hpre
      rw [show ((callMsg sevm parent (min gw.toNat (except64th avail)) 0 fa
          receiver receiver true false
          (abiCallWithTail onFlashLoanSelector
            [sevm.caller.toB256, fa.toB256, amount, 0] data)
          code dp).withBenv benv').benv = benv' from rfl, hstat] at this
      exact this
    · rcases h_del with ⟨hnone, -, -⟩ | ⟨d, -, -, hdp_true⟩
      · exact hnone
      · rw [show ((callMsg sevm parent (min gw.toNat (except64th avail)) 0 fa
            receiver receiver true false
            (abiCallWithTail onFlashLoanSelector
              [sevm.caller.toB256, fa.toB256, amount, 0] data)
            code dp).withBenv benv').disablePrecompiles = dp from rfl,
          hdp_true] at hdp
        cases hdp
  · -- answered by an actual sub-execution of the resolved code
    right
    rw [h_xl_some] at h_fill
    refine ⟨_, ex', h_fill, rfl, rfl, rfl, rfl⟩

/-- **Restoration at the borrower's callback frame.**  The `CALL` at
`flashLoanFromCall`'s callback site pushed the failure flag `0`, so whatever
the borrower's `onFlashLoan` frame wrote is gone by the time fmint resumes:
the world at `mid` — state and transient storage alike — is the world at `sc`.

**Which frame this names, and which it does not.**  The frame whose writes are
rolled back is the **child** frame the `CALL` opened, the borrower's.  The
equation is stated between fmint's own machine states `sc` and `mid` because
those are where the child's effects would have been visible had they survived,
and it holds **at the resumption point `mid` and nowhere else**:

* it is not a claim about fmint's frame at the end of `flashLoan`.  At `sc` the
  flash mint has *already happened*, so `Devm.WorldEq sc mid` says the mint is
  still in place at `mid`, with only the borrower's writes gone.  The mint is
  undone by fmint's *own* subsequent revert, under its own premises — a
  different frame, and R3's subject, not this lemma's.  "The borrower's revert
  undoes the flash mint" is therefore **wrong**: it silently changes frames.
* it is not a transaction-level claim.  An outer caller may catch fmint's
  eventual failure and commit a perfectly successful transaction, and this
  statement is silent about that.

**No error kind is named.**  `h_flag` is the pushed word, which is all fmint's
own compiled guard (`call ::: iszero ::: .rev <?> _`) observes; the three ways
to reach it — the balance guard, the depth guard, and a child frame that
settled with *some* error — are deliberately not distinguished, and no claim is
made about which occurred.

**Hypothesis position.**  `h_call` and `h_flag` are hypotheses.  Nothing here
asserts that any `flashLoan` runs, that any callback reverts, or that this
branch is ever taken.

The premise set is `of_flashLoanFromCall`'s minus the run: the seven-operand
call-site stack, and the `CALL` *instruction*'s run.  It is deliberately **not**
`Func.Run … flashLoanFromCall …`, because `Func.Run` is success-only and on
this branch fmint's post-`CALL` guard reverts fmint's own frame — there is no
successful `Func.Run` to hang a hypothesis on.  The `CALL` instruction itself
still runs to `.ok`: it pushes `0`.  The memory-image premises
(`Mem.Wf`/`Mem.Reads`/`h_win`/`h_size`) are not carried, because identifying
the calldata window is exactly what a restoration claim does not need. -/
theorem rollback_of_callback_failure {sevm : Sevm} {sc mid : Devm}
    {amount : B256} {a : Adr} {data : Bytes} {g : B256}
    (h_stack : g :: a.toB256 :: (0 : B256) :: callbackArgsOffset ::
        Nat.toB256 (196 + ceil32 data.length) ::
        (0 : B256) :: (0 : B256) :: [amount, a.toB256] <<+ sc.stack)
    (h_call : Ninst.Run sevm sc Ninst.call mid)
    (h_flag : (0 : B256) :: [amount, a.toB256] <<+ mid.stack) :
    Devm.WorldEq sc mid := by
  rcases of_run_call_val h_stack h_call with h_fail | h_ok
  · exact h_fail.2
  · -- the clean-child branch pushes `1`, which `h_flag` refutes
    exfalso
    obtain ⟨parent, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      h_mid_stack⟩ := h_ok
    rw [h_mid_stack] at h_flag
    exact B256.zero_ne_one
      (pref_head_unique h_flag (pref_append [(1 : B256)] parent.stack))

/-- **The callback boundary, proved from the `CALL` step and the success
guard.**  From the state `sc` entering `flashLoanFromCall` — the operand
stack, a memory image whose window is the encoding, and the residual run —
either branch of the `CALL` that does *not* open a clean child frame pushes
`0`, and `call ::: iszero ::: .rev <?> _` turns reaching the next fragment
into the fact that the pushed word was nonzero; what survives is
`CallbackBoundary`, and the walk continues through the two returndata checks
to the state entering `spendAllowanceThenBurn`, handed to Step 5 with its
stack, storage, code and memory image intact. -/
theorem of_flashLoanFromCall {sevm : Sevm} {sc r : Devm} {amount : B256}
    {a : Adr} {data : Bytes} {g : B256} {bs : Bytes}
    (h_stack : g :: a.toB256 :: (0 : B256) :: callbackArgsOffset ::
        Nat.toB256 (196 + ceil32 data.length) ::
        (0 : B256) :: (0 : B256) :: [amount, a.toB256] <<+ sc.stack)
    (h_wf : Mem.Wf sc.memory) (h_reads : Mem.Reads sc.memory bs)
    (h_win : bs.sliceD callbackArgsOffset.toNat (196 + ceil32 data.length) 0
        = abiCallWithTail onFlashLoanSelector
            [sevm.caller.toB256, sevm.currentTarget.toB256, amount, 0] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_run : Func.Run (fmint.main :: fmintAux) sevm sc flashLoanFromCall r) :
    ∃ mid sfin : Devm,
      CallbackBoundary sevm sevm.currentTarget a amount data sc mid ∧
      Devm.getStor mid = Devm.getStor sfin ∧
      Devm.getCode mid = Devm.getCode sfin ∧
      ([amount, a.toB256] <<+ sfin.stack) ∧
      Mem.Wf sfin.memory ∧
      Mem.Reads sfin.memory
        (Bytes.writeAt bs 0 (mid.returnData.sliceD 0 32 0)) ∧
      Func.Run (fmint.main :: fmintAux) sevm sfin spendAllowanceThenBurn r := by
  simp only [flashLoanFromCall] at h_run
  rcases of_run_next h_run with ⟨mid, r_call, h_run⟩
  rcases of_run_call_val h_stack r_call with h_fail | h_ok
  · -- the call pushed `0` : the success guard refutes it
    exfalso
    rcases of_run_next h_run with ⟨s1, r_iz, h_run⟩
    have hp1 := prefix_of_iszero r_iz h_fail.1
    rcases of_run_branch_rev h_run with ⟨s2, hpb2, -⟩
    have hps2 := hpb2.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hps2
    rw [hps2] at hp1
    have h01 : ((0 : B256) =? 0) = 0 :=
      pref_head_unique hp1 (pref_append [(0 : B256)] s2.stack)
    rw [show ((0 : B256) =? 0) = 1 from by simp [B256.eqCheck]] at h01
    exact B256.zero_ne_one h01.symm
  · rcases h_ok with ⟨parent, child, xl, dp, code, avail, hstk_eq, hst_par,
      hmem_par, h_del, h_fill, run_pm, herr, h_resume, h_mid_state, h_mid_rd,
      h_mid_mem, h_mid_stack⟩
    rw [toAdr_toB256] at h_del run_pm
    -- the calldata window is the encoding
    have h_cd : (sc.memory.read callbackArgsOffset.toNat
        (Nat.toB256 (196 + ceil32 data.length)).toNat).1
        = abiCallWithTail onFlashLoanSelector
            [sevm.caller.toB256, sevm.currentTarget.toB256, amount, 0] data := by
      rw [B256.toNat_toB256_of_lt h_size, Mem.Reads.read h_reads, h_win]
    rw [h_cd] at run_pm
    -- the parent's residual stack carries the retained words
    have hp_par : [amount, a.toB256] <<+ parent.stack := by
      rw [hstk_eq] at h_stack
      exact cons_pref_cons_inv (cons_pref_cons_inv (cons_pref_cons_inv
        (cons_pref_cons_inv (cons_pref_cons_inv (cons_pref_cons_inv
          (cons_pref_cons_inv h_stack))))))
    -- the return window is empty, so `mid`'s memory is the parent's, and the
    -- image survives the `CALL`'s extensions untouched
    have h_mid_mem' : mid.memory = parent.memory := h_mid_mem
    have h_wf_mid : Mem.Wf mid.memory := by
      rw [h_mid_mem', hmem_par]
      exact Mem.Wf.extends _ h_wf
    have h_rd_mid : Mem.Reads mid.memory bs := by
      rw [h_mid_mem', hmem_par]
      exact Mem.Reads.extends _ h_reads
    -- `iszero` on the success flag, and the untaken revert arm
    rcases of_run_next h_run with ⟨s1, r_iz, h_run⟩
    have hp_mid : (1 : B256) :: [amount, a.toB256] <<+ mid.stack := by
      rw [h_mid_stack]
      exact pref_cons hp_par
    have hp1 := prefix_of_iszero r_iz hp_mid
    obtain ⟨w1, hdb1⟩ : ∃ w, Devm.DiffBurn [w] [w =? 0] mid s1 := by
      rcases of_run_reg r_iz with ⟨pc, run⟩
      simp only [Rinst.run, Rinst.runCore] at run
      exact Devm.diffBurn_of_applyUnary run
    rcases of_run_branch_rev h_run with ⟨s2, hpb2, h_run⟩
    have hps2 := hpb2.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hps2
    rw [hps2] at hp1
    rw [show ((1 : B256) =? 0) = 0 from by
      rw [B256.eqCheck, if_neg (fun h => B256.zero_ne_one h.symm)]] at hp1
    have hp2 : [amount, a.toB256] <<+ s2.stack := cons_pref_cons_inv hp1
    -- `retdataShorterThan 32`, and the untaken revert arm
    rcases of_run_prepend (retdataShorterThan 32) _ h_run with ⟨s3, h_rst, h_run⟩
    rcases of_retdataShorterThan_val hp2 h_rst with ⟨hp3, hm3, hrd3⟩
    rcases of_run_branch_rev h_run with ⟨s4, hpb4, h_run⟩
    have hps4 := hpb4.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hps4
    rw [hps4] at hp3
    rw [pref_head_unique hp3 (pref_append [(0 : B256)] s4.stack)] at hp3
    have hp4 : [amount, a.toB256] <<+ s4.stack := cons_pref_cons_inv hp3
    -- the image and the returndata, carried to the head check
    have h_mem_s4 : s4.memory = mid.memory :=
      (hpb4.memory.symm.trans hm3).trans
        (hpb2.memory.symm.trans hdb1.memory.symm)
    have h_rd_s4 : s4.returnData = mid.returnData :=
      (hpb4.returnData.symm.trans hrd3).trans
        (hpb2.returnData.symm.trans hdb1.returnData.symm)
    have h_wf4 : Mem.Wf s4.memory := by
      rw [h_mem_s4]
      exact h_wf_mid
    have h_rd4 : Mem.Reads s4.memory bs := by
      rw [h_mem_s4]
      exact h_rd_mid
    -- `checkRetdataHead erc3156Magic 0` : the head word, read back
    rcases of_run_prepend (checkRetdataHead erc3156Magic 0) _ h_run with
      ⟨s5, h_crh, h_run⟩
    rcases of_checkRetdataHead_val hp4 h_wf4 h_rd4 h_crh with
      ⟨hp5, hlen4, h_wf5, h_rd5, hrd5⟩
    -- `iszero`, and the untaken revert arm : the head word IS the magic
    rcases of_run_next h_run with ⟨s6, r_iz2, h_run⟩
    have hp6 := prefix_of_iszero r_iz2 hp5
    obtain ⟨w2, hdb6⟩ : ∃ w, Devm.DiffBurn [w] [w =? 0] s5 s6 := by
      rcases of_run_reg r_iz2 with ⟨pc, run⟩
      simp only [Rinst.run, Rinst.runCore] at run
      exact Devm.diffBurn_of_applyUnary run
    rcases of_run_branch_rev h_run with ⟨s7, hpb7, h_run⟩
    have hps7 := hpb7.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hps7
    rw [hps7] at hp6
    have h_flag2 : ((erc3156Magic
        =? Bytes.toB256 (s4.returnData.sliceD 0 32 0)) =? 0) = 0 :=
      pref_head_unique hp6 (pref_append [(0 : B256)] s7.stack)
    have h_magic : Bytes.toB256 (s4.returnData.sliceD 0 32 0)
        = erc3156Magic := by
      by_contra hne
      have h0 : (erc3156Magic =? Bytes.toB256 (s4.returnData.sliceD 0 32 0))
          = 0 := by
        simp only [B256.eqCheck]
        exact if_neg (fun h => hne h.symm)
      rw [h0, show ((0 : B256) =? 0) = 1 from by simp [B256.eqCheck]] at h_flag2
      exact B256.zero_ne_one h_flag2.symm
    rw [h_flag2] at hp6
    have hp7 : [amount, a.toB256] <<+ s7.stack := cons_pref_cons_inv hp6
    -- clause 5, in the child's terms
    have hlen : 32 ≤ child.output.length := by
      rw [← h_mid_rd, ← h_rd_s4]
      exact hlen4
    have h_magic' : Bytes.toB256 (child.output.sliceD 0 32 0)
        = erc3156Magic := by
      rw [← h_mid_rd, ← h_rd_s4]
      exact h_magic
    -- storage and code, silent from resumption to the repayment
    have hg : Devm.getStor mid = Devm.getStor s7 :=
      ((((((funext (fun x => getStor_eq_of_state_eq hdb1.state x)).trans
        (funext (fun x => getStor_eq_of_state_eq hpb2.state x))).trans
        (Line.of_inv Devm.getStor (by line_inv) h_rst)).trans
        (funext (fun x => getStor_eq_of_state_eq hpb4.state x))).trans
        (Line.of_inv Devm.getStor (by line_inv) h_crh)).trans
        (funext (fun x => getStor_eq_of_state_eq hdb6.state x))).trans
        (funext (fun x => getStor_eq_of_state_eq hpb7.state x))
    have hgc : Devm.getCode mid = Devm.getCode s7 :=
      ((((((funext (fun x => getCode_eq_of_state_eq hdb1.state x)).trans
        (funext (fun x => getCode_eq_of_state_eq hpb2.state x))).trans
        (Line.of_inv Devm.getCode (by line_inv) h_rst)).trans
        (funext (fun x => getCode_eq_of_state_eq hpb4.state x))).trans
        (Line.of_inv Devm.getCode (by line_inv) h_crh)).trans
        (funext (fun x => getCode_eq_of_state_eq hdb6.state x))).trans
        (funext (fun x => getCode_eq_of_state_eq hpb7.state x))
    -- the memory image at the repayment's entry
    have h_mem_s7 : s7.memory = s5.memory :=
      hpb7.memory.symm.trans hdb6.memory.symm
    have h_wf7 : Mem.Wf s7.memory := by
      rw [h_mem_s7]
      exact h_wf5
    have h_rd7 : Mem.Reads s7.memory
        (Bytes.writeAt bs 0 (mid.returnData.sliceD 0 32 0)) := by
      rw [h_mem_s7, ← h_rd_s4]
      rw [show (((0 : B256)) * 32).toNat = 0 from rfl] at h_rd5
      exact h_rd5
    exact ⟨mid, s7,
      ⟨parent, child, xl, dp, code, g, avail, hstk_eq, hst_par, h_del, h_fill,
        run_pm, herr, hlen, h_magic', h_resume, h_mid_state, h_mid_rd,
        h_mid_stack⟩,
      hg, hgc, hp7, h_wf7, h_rd7, h_run⟩

/-- **Step 4's headline: a successful `flashLoan` performed the callback.**
`flashLoan_callback_image` extended through the `CALL`: the guards, the mint
equation, the callback boundary between the state at the `CALL` and the state
at resumption, and the residual run into the repayment, all off one
hypothesis run.

Premises as in `flashLoan_callback_image`, and they travel to Step 6's claim
hygiene: `h_dec` (canonical encoding — the non-canonical case is out of
scope), `h_size` (the encoded call fits a machine word), `h_wf`/`h_fresh`
(frame freshness).

**This is partial correctness, not liveness**: the run is a hypothesis, and
nothing here says a `flashLoan` ever succeeds. -/
theorem flashLoan_performs_callback {sevm : Sevm} {s r : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf s.memory) (h_fresh : Mem.Reads s.memory [])
    (h_run : Func.Run (fmint.main :: fmintAux) sevm s flashLoan r) :
    token = sevm.currentTarget.toB256 ∧
    B256.Nof ((Devm.getStor s sevm.currentTarget).get supplySlot) amount ∧
    ∃ (a : Adr) (sc mid sfin : Devm),
      receiver = a.toB256 ∧
      Devm.getCode s = Devm.getCode sc ∧
      Devm.getStor sc sevm.currentTarget =
        ((Devm.getStor s sevm.currentTarget).set a.toB256
            (amount + (Devm.getStor s sevm.currentTarget).get a.toB256)).set
          supplySlot
          (amount + (Devm.getStor s sevm.currentTarget).get supplySlot) ∧
      CallbackBoundary sevm sevm.currentTarget a amount data sc mid ∧
      Devm.getStor mid = Devm.getStor sfin ∧
      Devm.getCode mid = Devm.getCode sfin ∧
      ([amount, a.toB256] <<+ sfin.stack) ∧
      Mem.Wf sfin.memory ∧
      (∃ img, Mem.Reads sfin.memory img) ∧
      Func.Run (fmint.main :: fmintAux) sevm sfin spendAllowanceThenBurn r := by
  have hdlen : data.length < 2 ^ 256 := by
    have := Nat.le_ceil32 data.length
    omega
  have h0 : Sevm.argWord sevm 0 = receiver := argWord_zero_of_decodes h_dec
  have h1 : Sevm.argWord sevm 1 = token := argWord_one_of_decodes h_dec
  have h2 : Sevm.argWord sevm 2 = amount := argWord_two_of_decodes h_dec
  have htl : Sevm.tailLen sevm 3 = Nat.toB256 data.length :=
    tailLen_three_of_decodes h_dec
  have htb : Sevm.tailBytes sevm 3 = data := tailBytes_three_of_decodes hdlen h_dec
  have hsize : (0xc4 : B256) + ((~~~ (31 : B256)) &&& (31 + Nat.toB256 data.length))
      = Nat.toB256 (196 + ceil32 data.length) := by
    rw [← toB256_toNat ((0xc4 : B256) + _), toNat_callbackArgsSize h_size]
  obtain ⟨h_token, h_nof, a, sc, g, h_recv, h_code, h_stor, h_stack, h_mem,
    h_res⟩ := of_flashLoan_toCall h_run
  rw [h0] at h_recv
  rw [h1] at h_token
  rw [h2] at h_nof h_stor h_stack h_mem
  rw [htl, hsize] at h_stack
  obtain ⟨h_wf_sc, h_reads_sc⟩ := h_mem [] h_wf h_fresh
  rw [htl, htb, callbackImage_nil] at h_reads_sc
  have h_win : (onFlashLoanSelector.toBytes ++ sevm.caller.toB256.toBytes ++
      sevm.currentTarget.toB256.toBytes ++ amount.toBytes ++
      (0 : B256).toBytes ++ (0xa0 : B256).toBytes ++
      (Nat.toB256 data.length).toBytes ++ data).sliceD
        callbackArgsOffset.toNat (196 + ceil32 data.length) 0
      = abiCallWithTail onFlashLoanSelector
          [sevm.caller.toB256, sevm.currentTarget.toB256, amount, 0] data := by
    rw [show callbackArgsOffset.toNat = 28 from rfl]
    exact callbackWindow onFlashLoanSelector sevm.caller.toB256
      sevm.currentTarget.toB256 amount data
  rcases of_flashLoanFromCall h_stack h_wf_sc h_reads_sc h_win h_size h_res with
    ⟨mid, sfin, h_cb, h_gs, h_gc2, h_pf, h_wf_fin, h_rd_fin, h_run5⟩
  exact ⟨h_token, h_nof, a, sc, mid, sfin, h_recv, h_code, h_stor, h_cb, h_gs,
    h_gc2, h_pf, h_wf_fin, ⟨_, h_rd_fin⟩, h_run5⟩

/-! ## The repayment

Arc B walked `spendAllowanceThenBurn` and `burnAndReturn` tracking
`Stor.Conserved`, and let every word it met be anonymous
(`Conserved.lean`, `of_spendAllowanceThenBurn`, `of_burnAndReturn`).  Here the
words are *named*: the allowance key is the keccak of a window this walk knows
the contents of, the allowance and the balance are the slots the walk read, and
the two writes of the burn pair are equations.

**Hypothesis position**, as everywhere in this module: the run is a hypothesis
and this reads facts off it. -/

/-- **The repayment's allowance key**, `keccak256(receiver ‖ address(this))`.

Two of the four departures from WETH's `updateAllowance` that
`Blanc/Fmint.lean`'s `spendAllowanceThenBurn` docstring lists are visible in
this definition alone: the spender is `address(this)` and **not** `caller`, and
there is no `src = caller` bypass — a borrower naming itself as `receiver` is
the *common* case and still spends allowance, as the pinned OpenZeppelin
reference does. -/
def repayKey (receiver self : Adr) : B256 :=
  Bytes.keccak (receiver.toB256.toBytes ++ self.toB256.toBytes)

/-- The hashed window, whatever memory held before it.  The two stores land at
`0x00` and `0x20` and the `KECCAK256` reads `[0, 64)`, so the hash input is
exactly the two words: nothing of the old image survives below `0x40`, and the
window does not reach above it.

fmint's own offsets, so this lives here rather than in the shared layer. -/
lemma repayKey_window (bs : Bytes) (x y : B256) :
    (Bytes.writeAt (Bytes.writeAt bs 0 x.toBytes) 32 y.toBytes).sliceD 0 64 0
      = x.toBytes ++ y.toBytes := by
  have hx : x.toBytes.length = 32 := B256.length_toBytes x
  have hy : y.toBytes.length = 32 := B256.length_toBytes y
  have e1 : Bytes.writeAt bs 0 x.toBytes = x.toBytes ++ bs.drop 32 := by
    rw [Bytes.writeAt, hx, show List.takeD 0 bs 0 = [] from rfl, List.nil_append,
      Nat.zero_add]
  have e2 : Bytes.writeAt (x.toBytes ++ bs.drop 32) 32 y.toBytes
      = x.toBytes ++ (y.toBytes ++ (bs.drop 32).drop 32) := by
    rw [Bytes.writeAt, hy, List.takeD_eq_take _ (by simp [hx]),
      List.take_left' hx, show (32 + 32) = x.toBytes.length + 32 from by rw [hx],
      List.drop_append, List.append_assoc]
    simp [hx]
  rw [e1, e2]
  unfold List.sliceD
  rw [List.drop_zero, List.takeD_eq_take _ (by simp [hx, hy]; omega),
    ← List.append_assoc, List.take_left' (by simp [hx, hy])]

/-- **The allowance spend, both arms.**

`spendAllowanceThenBurn` hashes `receiver ‖ address(this)` out of memory words
`0` and `1`, checks the resulting key against both storage regions the
invariant reads, loads the allowance, and converges on `Func.call burnSlot`
from two arms that this postcondition keeps apart:

* the **infinite** arm — the allowance is `type(uint256).max` — **writes
  nothing**.  That is a WETH9/OpenZeppelin convention rather than an EIP
  requirement (the pinned reference's `_spendAllowance` skips the write at
  `max`); collapsing it into the other arm would lose behaviour the fixture
  suite already tests;
* the **finite** arm writes `allowance - amount`, with `amount ≤ allowance`
  from its own `lt` guard — an honest bound, not a wrap.

The two guard conjuncts come out in front because they are facts about the key
alone: `checkSlotCollides` passing says the allowance slot is neither
address-shaped (so no balance aliases it) nor `supplySlot`. -/
lemma of_spendAllowanceThenBurn_val {sevm : Sevm} {s r : Devm} {wad : B256}
    {a : Adr} {bs : Bytes}
    (hs : [wad, a.toB256] <<+ s.stack)
    (h_wf : Mem.Wf s.memory) (h_reads : Mem.Reads s.memory bs)
    (h_run : Func.Run (fmint.main :: fmintAux) sevm s spendAllowanceThenBurn r) :
    ¬ ValidAdr (repayKey a sevm.currentTarget) ∧
    repayKey a sevm.currentTarget ≠ supplySlot ∧
    ∃ (sb : Devm) (allow : B256),
      allow = (Devm.getStor s sevm.currentTarget).get
        (repayKey a sevm.currentTarget) ∧
      ( (allow = B256.max ∧
          Devm.getStor sb sevm.currentTarget = Devm.getStor s sevm.currentTarget)
        ∨ (allow ≠ B256.max ∧ wad ≤ allow ∧
            Devm.getStor sb sevm.currentTarget
              = (Devm.getStor s sevm.currentTarget).set
                  (repayKey a sevm.currentTarget) (allow - wad)) ) ∧
      Devm.getCode s = Devm.getCode sb ∧
      ([wad, a.toB256] <<+ sb.stack) ∧
      Mem.Wf sb.memory ∧ (∃ img, Mem.Reads sb.memory img) ∧
      Func.Run (fmint.main :: fmintAux) sevm sb burnAndReturn r := by
  simp only [spendAllowanceThenBurn] at h_run
  -- dup 1 : [receiver, wad, receiver]
  rcases of_run_next h_run with ⟨s1, r1, h_run⟩
  rcases of_run_dup r1 with ⟨y, hy1, pb1⟩
  have hy1' : y = a.toB256 := by
    have h_get : s.stack[(1 : Fin 16).val]? = some a.toB256 :=
      Stack.nth_getElem (Stack.Nth.tail 0 a.toB256 wad [a.toB256]
        (Stack.Nth.head a.toB256 [])) hs
    rw [h_get] at hy1; injection hy1 with hy1; exact hy1.symm
  subst y
  have hs1 : [a.toB256, wad, a.toB256] <<+ s1.stack := prefix_of_push pb1 hs
  have hg : Devm.getStor s = Devm.getStor s1 :=
    Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r1 Line.Run.nil)
  have hgc : Devm.getCode s = Devm.getCode s1 :=
    Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r1 Line.Run.nil)
  have hm : s.memory = s1.memory := Ninst.Hinv.inv (f := Devm.memory) r1
  clear r1 pb1 hs
  -- mstoreAt 0 : the receiver word at 0x00
  rcases of_run_prepend (mstoreAt 0) _ h_run with ⟨s2, h2, h_run⟩
  rcases of_run_mstoreAt_val h2 hs1 with ⟨hs2, hm2⟩
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h2)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h2)
  have hwf2 : Mem.Wf s2.memory := by
    rw [hm2, ← hm]; exact h_wf.write _ _
  have hrd2 : Mem.Reads s2.memory (Bytes.writeAt bs 0 a.toB256.toBytes) := by
    rw [hm2, ← hm]; exact Mem.Reads.write h_wf h_reads 0 _
  clear h2 hs1 hm2
  -- address : [self, wad, receiver] — `address`, not `caller`
  rcases of_run_next h_run with ⟨s3, r3, h_run⟩
  have hs3 : sevm.currentTarget.toB256 :: [wad, a.toB256] <<+ s3.stack :=
    prefix_of_push (of_run_address r3) hs2
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r3 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r3 Line.Run.nil))
  have hm3 : s2.memory = s3.memory := Ninst.Hinv.inv (f := Devm.memory) r3
  clear r3 hs2
  -- mstoreAt 1 : the contract's own address at 0x20
  rcases of_run_prepend (mstoreAt 1) _ h_run with ⟨s4, h4, h_run⟩
  rcases of_run_mstoreAt_val h4 hs3 with ⟨hs4, hm4⟩
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h4)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h4)
  have hwf4 : Mem.Wf s4.memory := by
    rw [hm4, ← hm3]; exact hwf2.write _ _
  have hrd4 : Mem.Reads s4.memory (Bytes.writeAt (Bytes.writeAt bs 0 a.toB256.toBytes)
      32 sevm.currentTarget.toB256.toBytes) := by
    rw [hm4, ← hm3]; exact Mem.Reads.write hwf2 hrd2 32 _
  clear h4 hs3 hm4 hm3 hwf2 hrd2
  -- pushList [64, 0] : the hash window
  rcases of_run_prepend (pushList [64, 0]) _ h_run with ⟨s5, h5, h_run⟩
  have hs5 : [0, 64, wad, a.toB256] <<+ s5.stack := by generalize_line_prefix
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h5)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h5)
  have hm5 : s4.memory = s5.memory := Line.of_inv Devm.memory (by line_inv) h5
  clear h5 hs4
  -- kec : the allowance key, named
  rcases of_run_next h_run with ⟨s6, r6, h_run⟩
  have hs6 := (prefix_of_kec_val r6 hs5).1
  have hm6 := (prefix_of_kec_val r6 hs5).2
  have h_key : (s5.memory.read (0 : B256).toNat (64 : B256).toNat).1.keccak
      = repayKey a sevm.currentTarget := by
    rw [show (0 : B256).toNat = 0 from rfl, show (64 : B256).toNat = 64 from rfl,
      Mem.Reads.read (hm5 ▸ hrd4) 0 64, repayKey_window]
    rfl
  rw [h_key] at hs6
  have hwf6 : Mem.Wf s6.memory := by
    rw [hm6]; exact (hm5 ▸ hwf4).extend _ _
  have hrd6 : ∃ img, Mem.Reads s6.memory img :=
    ⟨_, by rw [hm6]; exact Mem.Reads.extend (hm5 ▸ hrd4) _ _⟩
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r6 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r6 Line.Run.nil))
  clear r6 hs5 hm6 hm5 hm hwf4 hrd4 h_key
  -- checkSlotCollides : the key aliases neither region
  rcases of_run_prepend checkSlotCollides _ h_run with ⟨s7, h7, h_run⟩
  rcases of_checkSlotCollides hs6 h7 with ⟨coll, hs7, h_guard⟩
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h7)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h7)
  have hmw : Mem.Wf s7.memory := (Line.of_inv Devm.memory (by line_inv) h7) ▸ hwf6
  have hmr : ∃ img, Mem.Reads s7.memory img := by
    rcases hrd6 with ⟨img, himg⟩
    exact ⟨img, (Line.of_inv Devm.memory (by line_inv) h7) ▸ himg⟩
  clear h7 hs6 hwf6 hrd6
  -- rev-branch : the guard passed
  rcases of_run_branch_rev h_run with ⟨s8, hp8, h_run⟩
  have hp8s := hp8.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp8s
  rw [hp8s] at hs7
  have h_coll : coll = 0 := pref_head_unique hs7 (pref_append [0] s8.stack)
  obtain ⟨h_nva, h_nsup⟩ := h_guard h_coll
  rw [h_coll] at hs7
  have hs8 : [repayKey a sevm.currentTarget, wad, a.toB256] <<+ s8.stack :=
    cons_pref_cons_inv hs7
  have hg := hg.trans (funext (fun x => getStor_eq_of_state_eq hp8.state x))
  have hgc := hgc.trans (funext (fun x => getCode_eq_of_state_eq hp8.state x))
  have hmw : Mem.Wf s8.memory := hp8.memory ▸ hmw
  have hmr : ∃ img, Mem.Reads s8.memory img := by
    rcases hmr with ⟨img, himg⟩; exact ⟨img, hp8.memory ▸ himg⟩
  clear hs7 hp8s hp8 h_guard h_coll
  refine ⟨h_nva, h_nsup, ?_⟩
  -- dup 0 : [key, key, wad, receiver]
  rcases of_run_next h_run with ⟨s9, r9, h_run⟩
  rcases of_run_dup r9 with ⟨y, hy9, pb9⟩
  have hy9' : y = repayKey a sevm.currentTarget := by
    have h_get : s8.stack[(0 : Fin 16).val]? = some (repayKey a sevm.currentTarget) :=
      Stack.nth_getElem (Stack.Nth.head _ [wad, a.toB256]) hs8
    rw [h_get] at hy9; injection hy9 with hy9; exact hy9.symm
  subst y
  have hs9 : [repayKey a sevm.currentTarget, repayKey a sevm.currentTarget,
      wad, a.toB256] <<+ s9.stack := prefix_of_push pb9 hs8
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r9 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r9 Line.Run.nil))
  have hmw : Mem.Wf s9.memory := (Ninst.Hinv.inv (f := Devm.memory) r9) ▸ hmw
  have hmr : ∃ img, Mem.Reads s9.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r9) ▸ himg⟩
  clear r9 pb9 hs8
  -- sload : the allowance, named
  rcases of_run_next h_run with ⟨s10, r10, h_run⟩
  rcases prefix_of_sload r10 hs9 with ⟨allow, hs10, h_allow⟩
  have h_allow' : allow
      = (Devm.getStor s sevm.currentTarget).get (repayKey a sevm.currentTarget) := by
    rw [h_allow]
    show (Devm.getStor s9 sevm.currentTarget).get _ = _
    rw [← congr_fun hg sevm.currentTarget]
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r10 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r10 Line.Run.nil))
  have hmw : Mem.Wf s10.memory := (Ninst.Hinv.inv (f := Devm.memory) r10) ▸ hmw
  have hmr : ∃ img, Mem.Reads s10.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r10) ▸ himg⟩
  clear r10 hs9 h_allow
  -- dup 0 : [allow, allow, key, wad, receiver]
  rcases of_run_next h_run with ⟨s11, r11, h_run⟩
  rcases of_run_dup r11 with ⟨y, hy11, pb11⟩
  have hy11' : y = allow := by
    have h_get : s10.stack[(0 : Fin 16).val]? = some allow :=
      Stack.nth_getElem (Stack.Nth.head allow
        [repayKey a sevm.currentTarget, wad, a.toB256]) hs10
    rw [h_get] at hy11; injection hy11 with hy11; exact hy11.symm
  subst y
  have hs11 : [allow, allow, repayKey a sevm.currentTarget, wad, a.toB256]
      <<+ s11.stack := prefix_of_push pb11 hs10
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r11 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r11 Line.Run.nil))
  have hmw : Mem.Wf s11.memory := (Ninst.Hinv.inv (f := Devm.memory) r11) ▸ hmw
  have hmr : ∃ img, Mem.Reads s11.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r11) ▸ himg⟩
  clear r11 pb11 hs10
  -- isMax = [not, iszero] : the infinite-allowance flag
  rcases of_run_prepend isMax _ h_run with ⟨s12, h12, h_run⟩
  rcases Line.of_run_cons h12 with ⟨sa, rNot, h12'⟩
  rcases Line.of_run_cons h12' with ⟨sb0, rIsz, hnil⟩
  cases hnil
  have hsa : (~~~ allow) :: [allow, repayKey a sevm.currentTarget, wad, a.toB256]
      <<+ sa.stack := prefix_of_not rNot hs11
  have hs12 : ((~~~ allow) =? 0) ::
      [allow, repayKey a sevm.currentTarget, wad, a.toB256] <<+ s12.stack :=
    prefix_of_iszero rIsz hsa
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h12)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h12)
  have hmw : Mem.Wf s12.memory := (Line.of_inv Devm.memory (by line_inv) h12) ▸ hmw
  have hmr : ∃ img, Mem.Reads s12.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨img, (Line.of_inv Devm.memory (by line_inv) h12) ▸ himg⟩
  clear h12 rNot rIsz hsa hs11
  -- the branch : the finite arm decrements, the infinite arm writes nothing
  rcases of_run_branch h_run with
    ⟨s13, hp13, h_run⟩ | ⟨w13, s13, s14, h_ne13, hp13, hb13, h_run⟩
  · -- FINITE ARM : the flag is 0, so the allowance is not `B256.max`
    have hp13s := hp13.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp13s
    rw [hp13s] at hs12
    have h_flag : ((~~~ allow) =? 0) = 0 :=
      pref_head_unique hs12 (pref_append [0] s13.stack)
    have h_ne_max : allow ≠ B256.max := by
      intro hmax
      rw [hmax, B256.not_max, show ((0 : B256) =? 0) = 1 from by simp [B256.eqCheck]]
        at h_flag
      exact B256.zero_ne_one h_flag.symm
    rw [h_flag] at hs12
    have hs13 : [allow, repayKey a sevm.currentTarget, wad, a.toB256] <<+ s13.stack :=
      cons_pref_cons_inv hs12
    have hg := hg.trans (funext (fun x => getStor_eq_of_state_eq hp13.state x))
    have hgc := hgc.trans (funext (fun x => getCode_eq_of_state_eq hp13.state x))
    have hmw : Mem.Wf s13.memory := hp13.memory ▸ hmw
    have hmr : ∃ img, Mem.Reads s13.memory img := by
      rcases hmr with ⟨img, himg⟩; exact ⟨img, hp13.memory ▸ himg⟩
    clear hs12 hp13s hp13 h_flag
    -- dup 2 : [wad, allow, key, wad, receiver]
    rcases of_run_next h_run with ⟨s14, r14, h_run⟩
    rcases of_run_dup r14 with ⟨y, hy14, pb14⟩
    have hy14' : y = wad := by
      have h_get : s13.stack[(2 : Fin 16).val]? = some wad :=
        Stack.nth_getElem
          (Stack.Nth.tail 1 wad allow [repayKey a sevm.currentTarget, wad, a.toB256]
            (Stack.Nth.tail 0 wad (repayKey a sevm.currentTarget) [wad, a.toB256]
              (Stack.Nth.head wad [a.toB256]))) hs13
      rw [h_get] at hy14; injection hy14 with hy14; exact hy14.symm
    subst y
    have hs14 : [wad, allow, repayKey a sevm.currentTarget, wad, a.toB256]
        <<+ s14.stack := prefix_of_push pb14 hs13
    have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r14 Line.Run.nil))
    have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r14 Line.Run.nil))
    have hmw : Mem.Wf s14.memory := (Ninst.Hinv.inv (f := Devm.memory) r14) ▸ hmw
    have hmr : ∃ img, Mem.Reads s14.memory img := by
      rcases hmr with ⟨img, himg⟩
      exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r14) ▸ himg⟩
    clear r14 pb14 hs13
    -- dup 1 : [allow, wad, allow, key, wad, receiver]
    rcases of_run_next h_run with ⟨s15, r15, h_run⟩
    rcases of_run_dup r15 with ⟨y, hy15, pb15⟩
    have hy15' : y = allow := by
      have h_get : s14.stack[(1 : Fin 16).val]? = some allow :=
        Stack.nth_getElem
          (Stack.Nth.tail 0 allow wad [allow, repayKey a sevm.currentTarget, wad, a.toB256]
            (Stack.Nth.head allow [repayKey a sevm.currentTarget, wad, a.toB256])) hs14
      rw [h_get] at hy15; injection hy15 with hy15; exact hy15.symm
    subst y
    have hs15 : [allow, wad, allow, repayKey a sevm.currentTarget, wad, a.toB256]
        <<+ s15.stack := prefix_of_push pb15 hs14
    have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r15 Line.Run.nil))
    have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r15 Line.Run.nil))
    have hmw : Mem.Wf s15.memory := (Ninst.Hinv.inv (f := Devm.memory) r15) ▸ hmw
    have hmr : ∃ img, Mem.Reads s15.memory img := by
      rcases hmr with ⟨img, himg⟩
      exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r15) ▸ himg⟩
    clear r15 pb15 hs14
    -- lt : the allowance covers the amount owed
    rcases of_run_next h_run with ⟨s16, r16, h_run⟩
    have hs16 : (allow <? wad) ::
        [allow, repayKey a sevm.currentTarget, wad, a.toB256] <<+ s16.stack :=
      prefix_of_lt r16 hs15
    have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r16 Line.Run.nil))
    have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r16 Line.Run.nil))
    have hmw : Mem.Wf s16.memory := (Ninst.Hinv.inv (f := Devm.memory) r16) ▸ hmw
    have hmr : ∃ img, Mem.Reads s16.memory img := by
      rcases hmr with ⟨img, himg⟩
      exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r16) ▸ himg⟩
    clear r16 hs15
    rcases of_run_branch_rev h_run with ⟨s17, hp17, h_run⟩
    have hp17s := hp17.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp17s
    rw [hp17s] at hs16
    have h_flag17 : (allow <? wad) = 0 :=
      pref_head_unique hs16 (pref_append [0] s17.stack)
    have h_le : wad ≤ allow := by
      rw [← B256.not_lt]; intro hlt
      rw [B256.ltCheck, if_pos hlt] at h_flag17
      exact B256.zero_ne_one h_flag17.symm
    rw [h_flag17] at hs16
    have hs17 : [allow, repayKey a sevm.currentTarget, wad, a.toB256] <<+ s17.stack :=
      cons_pref_cons_inv hs16
    have hg := hg.trans (funext (fun x => getStor_eq_of_state_eq hp17.state x))
    have hgc := hgc.trans (funext (fun x => getCode_eq_of_state_eq hp17.state x))
    have hmw : Mem.Wf s17.memory := hp17.memory ▸ hmw
    have hmr : ∃ img, Mem.Reads s17.memory img := by
      rcases hmr with ⟨img, himg⟩; exact ⟨img, hp17.memory ▸ himg⟩
    clear hs16 hp17s hp17 h_flag17
    -- dup 2 : [wad, allow, key, wad, receiver]
    rcases of_run_next h_run with ⟨s18, r18, h_run⟩
    rcases of_run_dup r18 with ⟨y, hy18, pb18⟩
    have hy18' : y = wad := by
      have h_get : s17.stack[(2 : Fin 16).val]? = some wad :=
        Stack.nth_getElem
          (Stack.Nth.tail 1 wad allow [repayKey a sevm.currentTarget, wad, a.toB256]
            (Stack.Nth.tail 0 wad (repayKey a sevm.currentTarget) [wad, a.toB256]
              (Stack.Nth.head wad [a.toB256]))) hs17
      rw [h_get] at hy18; injection hy18 with hy18; exact hy18.symm
    subst y
    have hs18 : [wad, allow, repayKey a sevm.currentTarget, wad, a.toB256]
        <<+ s18.stack := prefix_of_push pb18 hs17
    have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r18 Line.Run.nil))
    have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r18 Line.Run.nil))
    have hmw : Mem.Wf s18.memory := (Ninst.Hinv.inv (f := Devm.memory) r18) ▸ hmw
    have hmr : ∃ img, Mem.Reads s18.memory img := by
      rcases hmr with ⟨img, himg⟩
      exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r18) ▸ himg⟩
    clear r18 pb18 hs17
    -- swap 0 ; sub : the decremented allowance
    rcases of_run_next h_run with ⟨s19, r19, h_run⟩
    have hs19 : [allow, wad, repayKey a sevm.currentTarget, wad, a.toB256]
        <<+ s19.stack := by
      have h_swap : Stack.Swap (0 : Fin 16).val
          [wad, allow, repayKey a sevm.currentTarget, wad, a.toB256]
          [allow, wad, repayKey a sevm.currentTarget, wad, a.toB256] :=
        Stack.swapCore_zero
      exact Stack.prefix_of_swap h_swap (of_run_swap r19) hs18
    have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r19 Line.Run.nil))
    have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r19 Line.Run.nil))
    have hmw : Mem.Wf s19.memory := (Ninst.Hinv.inv (f := Devm.memory) r19) ▸ hmw
    have hmr : ∃ img, Mem.Reads s19.memory img := by
      rcases hmr with ⟨img, himg⟩
      exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r19) ▸ himg⟩
    clear r19 hs18
    rcases of_run_next h_run with ⟨s20, r20, h_run⟩
    have hs20 : (allow - wad) :: [repayKey a sevm.currentTarget, wad, a.toB256]
        <<+ s20.stack := prefix_of_sub r20 hs19
    have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r20 Line.Run.nil))
    have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r20 Line.Run.nil))
    have hmw : Mem.Wf s20.memory := (Ninst.Hinv.inv (f := Devm.memory) r20) ▸ hmw
    have hmr : ∃ img, Mem.Reads s20.memory img := by
      rcases hmr with ⟨img, himg⟩
      exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r20) ▸ himg⟩
    clear r20 hs19
    -- swap 0 : the key back on top
    rcases of_run_next h_run with ⟨s21, r21, h_run⟩
    have hs21 : [repayKey a sevm.currentTarget, allow - wad, wad, a.toB256]
        <<+ s21.stack := by
      have h_swap : Stack.Swap (0 : Fin 16).val
          [allow - wad, repayKey a sevm.currentTarget, wad, a.toB256]
          [repayKey a sevm.currentTarget, allow - wad, wad, a.toB256] :=
        Stack.swapCore_zero
      exact Stack.prefix_of_swap h_swap (of_run_swap r21) hs20
    have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r21 Line.Run.nil))
    have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r21 Line.Run.nil))
    have hmw : Mem.Wf s21.memory := (Ninst.Hinv.inv (f := Devm.memory) r21) ▸ hmw
    have hmr : ∃ img, Mem.Reads s21.memory img := by
      rcases hmr with ⟨img, himg⟩
      exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r21) ▸ himg⟩
    clear r21 hs20
    -- sstore : the one guarded allowance write
    rcases of_run_next h_run with ⟨s22, r22, h_run⟩
    have h_set : Devm.getStor s22 sevm.currentTarget
        = (Devm.getStor s21 sevm.currentTarget).set
            (repayKey a sevm.currentTarget) (allow - wad) :=
      sstore_getStor_set r22 hs21
    have hs22 : [wad, a.toB256] <<+ s22.stack := prefix_of_sstore r22 hs21
    have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r22 Line.Run.nil))
    have hmw : Mem.Wf s22.memory := (Ninst.Hinv.inv (f := Devm.memory) r22) ▸ hmw
    have hmr : ∃ img, Mem.Reads s22.memory img := by
      rcases hmr with ⟨img, himg⟩
      exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r22) ▸ himg⟩
    clear r22 hs21
    -- Func.call burnSlot : the shared epilogue
    rcases of_run_call h_run with ⟨f, s23, h_get, h_burn, h_run⟩
    rw [get_burnSlot] at h_get
    rw [← Option.some.inj h_get] at h_run
    refine ⟨s23, allow, h_allow', Or.inr ⟨h_ne_max, h_le, ?_⟩, ?_, ?_, ?_, ?_, h_run⟩
    · rw [← getStor_eq_of_state_eq h_burn.state sevm.currentTarget, h_set,
        ← congr_fun hg sevm.currentTarget]
    · exact hgc.trans (funext (fun x => getCode_eq_of_state_eq h_burn.state x))
    · rcases hs22 with ⟨t, hsplit⟩
      exact ⟨t, by rw [← h_burn.stack]; exact hsplit⟩
    · exact h_burn.memory ▸ hmw
    · rcases hmr with ⟨img, himg⟩; exact ⟨img, h_burn.memory ▸ himg⟩
  · -- INFINITE ARM : the flag is nonzero, so the allowance is `B256.max` and
    -- nothing is written
    have hp13s := hp13.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp13s
    rw [hp13s] at hs12
    have h_w13 : ((~~~ allow) =? 0) = w13 :=
      pref_head_unique hs12 (pref_append [w13] s13.stack)
    have h_max : allow = B256.max := by
      apply B256.eq_max_of_not_eq_zero
      by_contra hne
      rw [B256.eqCheck, if_neg hne] at h_w13
      exact h_ne13 h_w13.symm
    rw [h_w13] at hs12
    have hs13 : [allow, repayKey a sevm.currentTarget, wad, a.toB256] <<+ s13.stack :=
      cons_pref_cons_inv hs12
    have hg := hg.trans (funext (fun x => getStor_eq_of_state_eq hp13.state x))
    have hgc := hgc.trans (funext (fun x => getCode_eq_of_state_eq hp13.state x))
    have hmw : Mem.Wf s13.memory := hp13.memory ▸ hmw
    have hmr : ∃ img, Mem.Reads s13.memory img := by
      rcases hmr with ⟨img, himg⟩; exact ⟨img, hp13.memory ▸ himg⟩
    have hg := hg.trans (funext (fun x => getStor_eq_of_state_eq hb13.state x))
    have hgc := hgc.trans (funext (fun x => getCode_eq_of_state_eq hb13.state x))
    have hmw : Mem.Wf s14.memory := hb13.memory ▸ hmw
    have hmr : ∃ img, Mem.Reads s14.memory img := by
      rcases hmr with ⟨img, himg⟩; exact ⟨img, hb13.memory ▸ himg⟩
    have hs14 : [allow, repayKey a sevm.currentTarget, wad, a.toB256] <<+ s14.stack := by
      rcases hs13 with ⟨t, hsplit⟩
      exact ⟨t, by rw [← hb13.stack]; exact hsplit⟩
    clear hs12 hp13s hp13 hb13 h_w13 hs13
    -- pop ; pop : the arm that writes nothing
    rcases of_run_next h_run with ⟨s15, r15, h_run⟩
    have hs15 : [repayKey a sevm.currentTarget, wad, a.toB256] <<+ s15.stack :=
      prefix_of_pop (of_run_pop r15) hs14
    have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r15 Line.Run.nil))
    have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r15 Line.Run.nil))
    have hmw : Mem.Wf s15.memory := (Ninst.Hinv.inv (f := Devm.memory) r15) ▸ hmw
    have hmr : ∃ img, Mem.Reads s15.memory img := by
      rcases hmr with ⟨img, himg⟩
      exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r15) ▸ himg⟩
    clear r15 hs14
    rcases of_run_next h_run with ⟨s16, r16, h_run⟩
    have hs16 : [wad, a.toB256] <<+ s16.stack := prefix_of_pop (of_run_pop r16) hs15
    have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r16 Line.Run.nil))
    have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r16 Line.Run.nil))
    have hmw : Mem.Wf s16.memory := (Ninst.Hinv.inv (f := Devm.memory) r16) ▸ hmw
    have hmr : ∃ img, Mem.Reads s16.memory img := by
      rcases hmr with ⟨img, himg⟩
      exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r16) ▸ himg⟩
    clear r16 hs15
    -- Func.call burnSlot
    rcases of_run_call h_run with ⟨f, s17, h_get, h_burn, h_run⟩
    rw [get_burnSlot] at h_get
    rw [← Option.some.inj h_get] at h_run
    refine ⟨s17, allow, h_allow', Or.inl ⟨h_max, ?_⟩, ?_, ?_, ?_, ?_, h_run⟩
    · rw [← getStor_eq_of_state_eq h_burn.state sevm.currentTarget,
        ← congr_fun hg sevm.currentTarget]
    · exact hgc.trans (funext (fun x => getCode_eq_of_state_eq h_burn.state x))
    · rcases hs16 with ⟨t, hsplit⟩
      exact ⟨t, by rw [← h_burn.stack]; exact hsplit⟩
    · exact h_burn.memory ▸ hmw
    · rcases hmr with ⟨img, himg⟩; exact ⟨img, h_burn.memory ▸ himg⟩

/-! ### The burn pair, and what the frame returns -/

/-- Fmint's historical name for the shared canonical ABI-true result. -/
def ReturnsTrue (d : Devm) : Prop := Devm.output d = (1 : B256).toBytes

/-- Compatibility endpoint for fmint's existing proof family.  The generic
theorem is now shared upstream as `of_returnTrue_shared`; this statement and
its proof shape remain here so already-audited fmint declarations do not move. -/
lemma of_returnTrue {fs : List Func} {sevm : Sevm} {s r : Devm}
    {img : Bytes} {xs}
    (hp : xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (h : Func.Run fs sevm s returnTrue r) :
    ReturnsTrue r ∧ Devm.getCode s = Devm.getCode r := by
  simp only [returnTrue] at h
  rcases of_run_next h with ⟨s1, r1, h⟩
  have hp1 : (1 : B256) :: xs <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 r1) hp
  have hm1 : s.memory = s1.memory :=
    Ninst.Hinv.inv (f := Devm.memory) r1
  rcases of_run_prepend (mstoreAt 0) _ h with ⟨s2, h2, h⟩
  rcases of_run_mstoreAt_val h2 hp1 with ⟨hp2, hm2⟩
  have hwf2 : Mem.Wf s2.memory := by
    rw [hm2, ← hm1]
    exact h_wf.write _ _
  have hrd2 :
      Mem.Reads s2.memory (Bytes.writeAt img 0 (1 : B256).toBytes) := by
    rw [hm2, ← hm1]
    exact Mem.Reads.write h_wf h_reads 0 _
  rcases of_run_prepend (pushList [32, 0]) _ h with ⟨s3, h3, h⟩
  rcases Line.of_run_cons h3 with ⟨u1, q1, h3'⟩
  rcases Line.of_run_cons h3' with ⟨u2, q2, hnil⟩
  cases hnil
  have hu1 : (32 : B256) :: xs <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp2
  have hu2 : (0 : B256) :: (32 : B256) :: xs <<+ s3.stack :=
    prefix_of_push (of_run_pushB256 q2) hu1
  have hm3 : s2.memory = s3.memory :=
    Line.of_inv Devm.memory (by line_inv) h3
  have hgc : Devm.getCode s = Devm.getCode s3 :=
    ((Ninst.Hinv.inv (f := Devm.getCode) r1).trans
      (Line.of_inv Devm.getCode (by line_inv) h2)).trans
      (Line.of_inv Devm.getCode (by line_inv) h3)
  refine ⟨?_, hgc.trans (of_run_ret_val hu2 h).2⟩
  show Devm.output r = _
  rw [(of_run_ret_val hu2 h).1,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    Mem.Reads.read (hm3 ▸ hrd2) 0 32,
    show (32 : Nat) = (1 : B256).toBytes.length from
      (B256.length_toBytes 1).symm,
    Bytes.sliceD_writeAt]

/-- **The burn pair, as equations, and the frame's return value.**

`burnAndReturn` decreases the receiver's balance by `wad` and the supply by the
same `wad`, and returns ABI-`true`.  `wad ≤ rbal` is the contract's own
explicit balance check — the `lt` guard two instructions in — so the balance
side is an honest subtraction and not a wrap.

The supply side is stated in `B256` arithmetic and is *not* claimed
wrap-free here: the contract carries no supply-underflow guard, deliberately
(`Blanc/Fmint.lean`, `burnAndReturn`), and the bound that rules the wrap out
comes from the conservation invariant rather than from the code.  That is
`of_burnAndReturn_bound` below, which takes the invariant as an explicit
premise.

D5: the two `SSTORE`s are adjacent in the walk — nothing between them but the
`pushSupplySlot`/`SLOAD`/`DUP`/`SUB` that computes the second value, no
external control transfer and no halt. -/
lemma of_burnAndReturn_val {fs : List Func} {sevm : Sevm} {s r : Devm}
    {wad : B256} {a : Adr} {bs : Bytes}
    (hs : [wad, a.toB256] <<+ s.stack)
    (h_wf : Mem.Wf s.memory) (h_reads : Mem.Reads s.memory bs)
    (h_run : Func.Run fs sevm s burnAndReturn r) :
    wad ≤ (Devm.getStor s sevm.currentTarget).get a.toB256 ∧
    Devm.getStor r sevm.currentTarget
      = ((Devm.getStor s sevm.currentTarget).set a.toB256
            ((Devm.getStor s sevm.currentTarget).get a.toB256 - wad)).set supplySlot
          ((Devm.getStor s sevm.currentTarget).get supplySlot - wad) ∧
    Devm.getCode s = Devm.getCode r ∧
    ReturnsTrue r := by
  simp only [burnAndReturn] at h_run
  -- dup 1 : [receiver, wad, receiver]
  rcases of_run_next h_run with ⟨s1, r1, h_run⟩
  rcases of_run_dup r1 with ⟨y, hy1, pb1⟩
  have hy1' : y = a.toB256 := by
    have h_get : s.stack[(1 : Fin 16).val]? = some a.toB256 :=
      Stack.nth_getElem (Stack.Nth.tail 0 a.toB256 wad [a.toB256]
        (Stack.Nth.head a.toB256 [])) hs
    rw [h_get] at hy1; injection hy1 with hy1; exact hy1.symm
  subst y
  have hs1 : [a.toB256, wad, a.toB256] <<+ s1.stack := prefix_of_push pb1 hs
  have hg : Devm.getStor s = Devm.getStor s1 :=
    Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r1 Line.Run.nil)
  have hgc : Devm.getCode s = Devm.getCode s1 :=
    Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r1 Line.Run.nil)
  have hmw : Mem.Wf s1.memory := (Ninst.Hinv.inv (f := Devm.memory) r1) ▸ h_wf
  have hmr : ∃ img, Mem.Reads s1.memory img :=
    ⟨bs, (Ninst.Hinv.inv (f := Devm.memory) r1) ▸ h_reads⟩
  clear r1 pb1 hs h_wf h_reads
  -- sload : the receiver's balance, named
  rcases of_run_next h_run with ⟨s2, r2, h_run⟩
  rcases prefix_of_sload r2 hs1 with ⟨rbal, hs2, h_rbal⟩
  have h_rbal' : rbal = (Devm.getStor s sevm.currentTarget).get a.toB256 := by
    rw [h_rbal]
    show (Devm.getStor s1 sevm.currentTarget).get a.toB256 = _
    rw [← congr_fun hg sevm.currentTarget]
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r2 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r2 Line.Run.nil))
  have hmw : Mem.Wf s2.memory := (Ninst.Hinv.inv (f := Devm.memory) r2) ▸ hmw
  have hmr : ∃ img, Mem.Reads s2.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r2) ▸ himg⟩
  clear r2 hs1 h_rbal
  -- dup 1 ; dup 1 ; lt : the balance check
  rcases of_run_next h_run with ⟨s3, r3, h_run⟩
  rcases of_run_dup r3 with ⟨y, hy3, pb3⟩
  have hy3' : y = wad := by
    have h_get : s2.stack[(1 : Fin 16).val]? = some wad :=
      Stack.nth_getElem (Stack.Nth.tail 0 wad rbal [wad, a.toB256]
        (Stack.Nth.head wad [a.toB256])) hs2
    rw [h_get] at hy3; injection hy3 with hy3; exact hy3.symm
  subst y
  have hs3 : [wad, rbal, wad, a.toB256] <<+ s3.stack := prefix_of_push pb3 hs2
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r3 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r3 Line.Run.nil))
  have hmw : Mem.Wf s3.memory := (Ninst.Hinv.inv (f := Devm.memory) r3) ▸ hmw
  have hmr : ∃ img, Mem.Reads s3.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r3) ▸ himg⟩
  clear r3 pb3
  rcases of_run_next h_run with ⟨s4, r4, h_run⟩
  rcases of_run_dup r4 with ⟨y, hy4, pb4⟩
  have hy4' : y = rbal := by
    have h_get : s3.stack[(1 : Fin 16).val]? = some rbal :=
      Stack.nth_getElem (Stack.Nth.tail 0 rbal wad [rbal, wad, a.toB256]
        (Stack.Nth.head rbal [wad, a.toB256])) hs3
    rw [h_get] at hy4; injection hy4 with hy4; exact hy4.symm
  subst y
  have hs4 : [rbal, wad, rbal, wad, a.toB256] <<+ s4.stack := prefix_of_push pb4 hs3
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r4 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r4 Line.Run.nil))
  have hmw : Mem.Wf s4.memory := (Ninst.Hinv.inv (f := Devm.memory) r4) ▸ hmw
  have hmr : ∃ img, Mem.Reads s4.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r4) ▸ himg⟩
  clear r4 pb4 hs3
  rcases of_run_next h_run with ⟨s5, r5, h_run⟩
  have hs5 : (rbal <? wad) :: [rbal, wad, a.toB256] <<+ s5.stack := prefix_of_lt r5 hs4
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r5 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r5 Line.Run.nil))
  have hmw : Mem.Wf s5.memory := (Ninst.Hinv.inv (f := Devm.memory) r5) ▸ hmw
  have hmr : ∃ img, Mem.Reads s5.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r5) ▸ himg⟩
  clear r5 hs4
  rcases of_run_branch_rev h_run with ⟨s6, hp6, h_run⟩
  have hp6s := hp6.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp6s
  rw [hp6s] at hs5
  have h_ltflag : (rbal <? wad) = 0 := pref_head_unique hs5 (pref_append [0] s6.stack)
  have h_le : wad ≤ rbal := by
    rw [← B256.not_lt]; intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_ltflag
    exact B256.zero_ne_one h_ltflag.symm
  rw [h_ltflag] at hs5
  have hs6 : [rbal, wad, a.toB256] <<+ s6.stack := cons_pref_cons_inv hs5
  have hg := hg.trans (funext (fun x => getStor_eq_of_state_eq hp6.state x))
  have hgc := hgc.trans (funext (fun x => getCode_eq_of_state_eq hp6.state x))
  have hmw : Mem.Wf s6.memory := hp6.memory ▸ hmw
  have hmr : ∃ img, Mem.Reads s6.memory img := by
    rcases hmr with ⟨img, himg⟩; exact ⟨img, hp6.memory ▸ himg⟩
  clear hs5 hp6s hp6 h_ltflag
  -- dup 1 ; swap 0 ; sub : the debited balance
  rcases of_run_next h_run with ⟨s7, r7, h_run⟩
  rcases of_run_dup r7 with ⟨y, hy7, pb7⟩
  have hy7' : y = wad := by
    have h_get : s6.stack[(1 : Fin 16).val]? = some wad :=
      Stack.nth_getElem (Stack.Nth.tail 0 wad rbal [wad, a.toB256]
        (Stack.Nth.head wad [a.toB256])) hs6
    rw [h_get] at hy7; injection hy7 with hy7; exact hy7.symm
  subst y
  have hs7 : [wad, rbal, wad, a.toB256] <<+ s7.stack := prefix_of_push pb7 hs6
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r7 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r7 Line.Run.nil))
  have hmw : Mem.Wf s7.memory := (Ninst.Hinv.inv (f := Devm.memory) r7) ▸ hmw
  have hmr : ∃ img, Mem.Reads s7.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r7) ▸ himg⟩
  clear r7 pb7 hs6
  rcases of_run_next h_run with ⟨s8, r8, h_run⟩
  have hs8 : [rbal, wad, wad, a.toB256] <<+ s8.stack := by
    have h_swap8 : Stack.Swap (0 : Fin 16).val [wad, rbal, wad, a.toB256]
        [rbal, wad, wad, a.toB256] := Stack.swapCore_zero
    exact Stack.prefix_of_swap h_swap8 (of_run_swap r8) hs7
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r8 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r8 Line.Run.nil))
  have hmw : Mem.Wf s8.memory := (Ninst.Hinv.inv (f := Devm.memory) r8) ▸ hmw
  have hmr : ∃ img, Mem.Reads s8.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r8) ▸ himg⟩
  clear r8 hs7
  rcases of_run_next h_run with ⟨s9, r9, h_run⟩
  have hs9 : (rbal - wad) :: [wad, a.toB256] <<+ s9.stack := prefix_of_sub r9 hs8
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r9 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r9 Line.Run.nil))
  have hmw : Mem.Wf s9.memory := (Ninst.Hinv.inv (f := Devm.memory) r9) ▸ hmw
  have hmr : ∃ img, Mem.Reads s9.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r9) ▸ himg⟩
  clear r9 hs8
  -- dup 2 ; sstore : the balance write
  rcases of_run_next h_run with ⟨s10, r10, h_run⟩
  rcases of_run_dup r10 with ⟨y, hy10, pb10⟩
  have hy10' : y = a.toB256 := by
    have h_get : s9.stack[(2 : Fin 16).val]? = some a.toB256 :=
      Stack.nth_getElem
        (Stack.Nth.tail 1 a.toB256 (rbal - wad) [wad, a.toB256]
          (Stack.Nth.tail 0 a.toB256 wad [a.toB256] (Stack.Nth.head a.toB256 []))) hs9
    rw [h_get] at hy10; injection hy10 with hy10; exact hy10.symm
  subst y
  have hs10 : [a.toB256, rbal - wad, wad, a.toB256] <<+ s10.stack := prefix_of_push pb10 hs9
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r10 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r10 Line.Run.nil))
  have hmw : Mem.Wf s10.memory := (Ninst.Hinv.inv (f := Devm.memory) r10) ▸ hmw
  have hmr : ∃ img, Mem.Reads s10.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r10) ▸ himg⟩
  clear r10 pb10 hs9
  rcases of_run_next h_run with ⟨s11, r11, h_run⟩
  have h_set1 : Devm.getStor s11 sevm.currentTarget
      = (Devm.getStor s10 sevm.currentTarget).set a.toB256 (rbal - wad) :=
    sstore_getStor_set r11 hs10
  have hs11 : [wad, a.toB256] <<+ s11.stack := prefix_of_sstore r11 hs10
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r11 Line.Run.nil))
  have hmw : Mem.Wf s11.memory := (Ninst.Hinv.inv (f := Devm.memory) r11) ▸ hmw
  have hmr : ∃ img, Mem.Reads s11.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r11) ▸ himg⟩
  clear r11 hs10
  -- pushSupplySlot ; sload : the supply, named
  rcases of_run_prepend pushSupplySlot _ h_run with ⟨s12, h12, h_run⟩
  have hs12 : Fmint.supplySlot :: [wad, a.toB256] <<+ s12.stack := by
    simp only [pushSupplySlot] at h12
    rcases Line.of_run_cons h12 with ⟨sa, ra, h12'⟩
    rcases Line.of_run_cons h12' with ⟨sb, rb, hnil⟩
    cases hnil
    have hpa : (0 : B256) :: [wad, a.toB256] <<+ sa.stack :=
      prefix_of_push (of_run_pushB256 ra) hs11
    have hpb := prefix_of_not rb hpa
    rw [supplySlot_eq_not_zero] at hpb
    exact hpb
  have hg2 : Devm.getStor s11 = Devm.getStor s12 :=
    Line.of_inv Devm.getStor (by line_inv) h12
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h12)
  have hmw : Mem.Wf s12.memory := (Line.of_inv Devm.memory (by line_inv) h12) ▸ hmw
  have hmr : ∃ img, Mem.Reads s12.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨img, (Line.of_inv Devm.memory (by line_inv) h12) ▸ himg⟩
  clear h12 hs11
  rcases of_run_next h_run with ⟨s13, r13, h_run⟩
  rcases prefix_of_sload r13 hs12 with ⟨supply, hs13, h_supply⟩
  have h_supply' : supply
      = ((Devm.getStor s sevm.currentTarget).set a.toB256 (rbal - wad)).get
          Fmint.supplySlot := by
    rw [h_supply]
    show (Devm.getStor s12 sevm.currentTarget).get Fmint.supplySlot = _
    rw [← congr_fun hg2 sevm.currentTarget, h_set1, ← congr_fun hg sevm.currentTarget]
  have hg2 := hg2.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r13 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r13 Line.Run.nil))
  have hmw : Mem.Wf s13.memory := (Ninst.Hinv.inv (f := Devm.memory) r13) ▸ hmw
  have hmr : ∃ img, Mem.Reads s13.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r13) ▸ himg⟩
  clear r13 hs12 h_supply
  -- dup 1 ; swap 0 ; sub : the debited supply
  rcases of_run_next h_run with ⟨s14, r14, h_run⟩
  rcases of_run_dup r14 with ⟨y, hy14, pb14⟩
  have hy14' : y = wad := by
    have h_get : s13.stack[(1 : Fin 16).val]? = some wad :=
      Stack.nth_getElem (Stack.Nth.tail 0 wad supply [wad, a.toB256]
        (Stack.Nth.head wad [a.toB256])) hs13
    rw [h_get] at hy14; injection hy14 with hy14; exact hy14.symm
  subst y
  have hs14 : [wad, supply, wad, a.toB256] <<+ s14.stack := prefix_of_push pb14 hs13
  have hg2 := hg2.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r14 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r14 Line.Run.nil))
  have hmw : Mem.Wf s14.memory := (Ninst.Hinv.inv (f := Devm.memory) r14) ▸ hmw
  have hmr : ∃ img, Mem.Reads s14.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r14) ▸ himg⟩
  clear r14 pb14 hs13
  rcases of_run_next h_run with ⟨s15, r15, h_run⟩
  have hs15 : [supply, wad, wad, a.toB256] <<+ s15.stack := by
    have h_swap15 : Stack.Swap (0 : Fin 16).val [wad, supply, wad, a.toB256]
        [supply, wad, wad, a.toB256] := Stack.swapCore_zero
    exact Stack.prefix_of_swap h_swap15 (of_run_swap r15) hs14
  have hg2 := hg2.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r15 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r15 Line.Run.nil))
  have hmw : Mem.Wf s15.memory := (Ninst.Hinv.inv (f := Devm.memory) r15) ▸ hmw
  have hmr : ∃ img, Mem.Reads s15.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r15) ▸ himg⟩
  clear r15 hs14
  rcases of_run_next h_run with ⟨s16, r16, h_run⟩
  have hs16 : (supply - wad) :: [wad, a.toB256] <<+ s16.stack := prefix_of_sub r16 hs15
  have hg2 := hg2.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r16 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r16 Line.Run.nil))
  have hmw : Mem.Wf s16.memory := (Ninst.Hinv.inv (f := Devm.memory) r16) ▸ hmw
  have hmr : ∃ img, Mem.Reads s16.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r16) ▸ himg⟩
  clear r16 hs15
  -- pushSupplySlot ; sstore : the supply write, completing the pair
  rcases of_run_prepend pushSupplySlot _ h_run with ⟨s17, h17, h_run⟩
  have hs17 : Fmint.supplySlot :: (supply - wad) :: [wad, a.toB256] <<+ s17.stack := by
    simp only [pushSupplySlot] at h17
    rcases Line.of_run_cons h17 with ⟨sa, ra, h17'⟩
    rcases Line.of_run_cons h17' with ⟨sb, rb, hnil⟩
    cases hnil
    have hpa : (0 : B256) :: (supply - wad) :: [wad, a.toB256] <<+ sa.stack :=
      prefix_of_push (of_run_pushB256 ra) hs16
    have hpb := prefix_of_not rb hpa
    rw [supplySlot_eq_not_zero] at hpb
    exact hpb
  have hg2 := hg2.trans (Line.of_inv Devm.getStor (by line_inv) h17)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h17)
  have hmw : Mem.Wf s17.memory := (Line.of_inv Devm.memory (by line_inv) h17) ▸ hmw
  have hmr : ∃ img, Mem.Reads s17.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨img, (Line.of_inv Devm.memory (by line_inv) h17) ▸ himg⟩
  clear h17 hs16
  rcases of_run_next h_run with ⟨s18, r18, h_run⟩
  have h_set2 : Devm.getStor s18 sevm.currentTarget
      = (Devm.getStor s17 sevm.currentTarget).set Fmint.supplySlot (supply - wad) :=
    sstore_getStor_set r18 hs17
  have hs18 : [wad, a.toB256] <<+ s18.stack := prefix_of_sstore r18 hs17
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r18 Line.Run.nil))
  have hmw : Mem.Wf s18.memory := (Ninst.Hinv.inv (f := Devm.memory) r18) ▸ hmw
  have hmr : ∃ img, Mem.Reads s18.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r18) ▸ himg⟩
  clear r18 hs17
  -- the storage postcondition, assembled before the storage-silent tail
  have h_stor18 : Devm.getStor s18 sevm.currentTarget
      = ((Devm.getStor s sevm.currentTarget).set a.toB256
            ((Devm.getStor s sevm.currentTarget).get a.toB256 - wad)).set supplySlot
          ((Devm.getStor s sevm.currentTarget).get supplySlot - wad) := by
    rw [h_set2, ← congr_fun hg2 sevm.currentTarget, h_set1,
      ← congr_fun hg sevm.currentTarget, h_supply', h_rbal',
      Stor.get_supplySlot_set (⟨a, rfl⟩ : ValidAdr a.toB256)]
  -- dup 0 ; mstoreAt 0 : the event's data word
  rcases of_run_next h_run with ⟨s19, r19, h_run⟩
  rcases of_run_dup r19 with ⟨y, hy19, pb19⟩
  have hy19' : y = wad := by
    have h_get : s18.stack[(0 : Fin 16).val]? = some wad :=
      Stack.nth_getElem (Stack.Nth.head wad [a.toB256]) hs18
    rw [h_get] at hy19; injection hy19 with hy19; exact hy19.symm
  subst y
  have hs19 : [wad, wad, a.toB256] <<+ s19.stack := prefix_of_push pb19 hs18
  have hg3 : Devm.getStor s18 = Devm.getStor s19 :=
    Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r19 Line.Run.nil)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r19 Line.Run.nil))
  have hmw : Mem.Wf s19.memory := (Ninst.Hinv.inv (f := Devm.memory) r19) ▸ hmw
  have hmr : ∃ img, Mem.Reads s19.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r19) ▸ himg⟩
  clear r19 pb19 hs18
  rcases of_run_prepend (mstoreAt 0) _ h_run with ⟨s20, h20, h_run⟩
  rcases of_run_mstoreAt_val h20 hs19 with ⟨hs20, hm20⟩
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) h20)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h20)
  have hmw20 : Mem.Wf s20.memory := by rw [hm20]; exact hmw.write _ _
  have hmr20 : ∃ img, Mem.Reads s20.memory img := by
    rcases hmr with ⟨img, himg⟩
    exact ⟨_, by rw [hm20]; exact Mem.Reads.write hmw himg _ _⟩
  clear h20 hs19 hmw hmr hm20
  -- pushB256 0 ; dup 2 ; pushB256 transferEvent : the two topics
  rcases of_run_next h_run with ⟨s21, r21, h_run⟩
  have hs21 : (0 : B256) :: [wad, a.toB256] <<+ s21.stack :=
    prefix_of_push (of_run_pushB256 r21) hs20
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r21 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r21 Line.Run.nil))
  have hmw21 : Mem.Wf s21.memory := (Ninst.Hinv.inv (f := Devm.memory) r21) ▸ hmw20
  have hmr21 : ∃ img, Mem.Reads s21.memory img := by
    rcases hmr20 with ⟨img, himg⟩
    exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r21) ▸ himg⟩
  clear r21 hs20 hmw20 hmr20
  rcases of_run_next h_run with ⟨s22, r22, h_run⟩
  rcases of_run_dup r22 with ⟨y, hy22, pb22⟩
  have hy22' : y = a.toB256 := by
    have h_get : s21.stack[(2 : Fin 16).val]? = some a.toB256 :=
      Stack.nth_getElem
        (Stack.Nth.tail 1 a.toB256 (0 : B256) [wad, a.toB256]
          (Stack.Nth.tail 0 a.toB256 wad [a.toB256] (Stack.Nth.head a.toB256 []))) hs21
    rw [h_get] at hy22; injection hy22 with hy22; exact hy22.symm
  subst y
  have hs22 : a.toB256 :: (0 : B256) :: [wad, a.toB256] <<+ s22.stack :=
    prefix_of_push pb22 hs21
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r22 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r22 Line.Run.nil))
  have hmw22 : Mem.Wf s22.memory := (Ninst.Hinv.inv (f := Devm.memory) r22) ▸ hmw21
  have hmr22 : ∃ img, Mem.Reads s22.memory img := by
    rcases hmr21 with ⟨img, himg⟩
    exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r22) ▸ himg⟩
  clear r22 pb22 hs21 hmw21 hmr21
  rcases of_run_next h_run with ⟨s23, r23, h_run⟩
  have hs23 : transferEvent :: a.toB256 :: (0 : B256) :: [wad, a.toB256] <<+ s23.stack :=
    prefix_of_push (of_run_pushB256 r23) hs22
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r23 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r23 Line.Run.nil))
  have hmw23 : Mem.Wf s23.memory := (Ninst.Hinv.inv (f := Devm.memory) r23) ▸ hmw22
  have hmr23 : ∃ img, Mem.Reads s23.memory img := by
    rcases hmr22 with ⟨img, himg⟩
    exact ⟨img, (Ninst.Hinv.inv (f := Devm.memory) r23) ▸ himg⟩
  clear r23 hs22 hmw22 hmr22
  -- logWith 2 0 1 : the burn's Transfer event, which only extends memory
  rcases of_run_prepend (logWith 2 0 1) _ h_run with ⟨s24, h24, h_run⟩
  have hs24 : [wad, a.toB256] <<+ s24.stack := of_logWith201 hs23 h24
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) h24)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h24)
  have hmem24 : ∃ mi sz, s24.memory = s23.memory.extend mi sz := by
    simp only [logWith] at h24
    rcases Line.of_run_cons h24 with ⟨u1, q1, h24'⟩
    rcases Line.of_run_cons h24' with ⟨u2, q2, h24''⟩
    rcases Line.of_run_cons h24'' with ⟨u3, q3, hnil⟩
    cases hnil
    rcases of_run_log_mem q3 with ⟨mi, sz, hlog⟩
    exact ⟨mi, sz, by
      rw [hlog, ← Ninst.Hinv.inv (f := Devm.memory) q2,
        ← Ninst.Hinv.inv (f := Devm.memory) q1]⟩
  rcases hmem24 with ⟨mi, sz, hmem24⟩
  have hmw24 : Mem.Wf s24.memory := by rw [hmem24]; exact hmw23.extend _ _
  have hmr24 : ∃ img, Mem.Reads s24.memory img := by
    rcases hmr23 with ⟨img, himg⟩
    exact ⟨img, by rw [hmem24]; exact Mem.Reads.extend himg _ _⟩
  clear h24 hs23 hmw23 hmr23 hmem24
  -- returnTrue
  rcases hmr24 with ⟨img, himg⟩
  refine ⟨h_rbal' ▸ h_le, ?_, hgc.trans (of_returnTrue hs24 hmw24 himg h_run).2,
    (of_returnTrue hs24 hmw24 himg h_run).1⟩
  have h_tail : Devm.getStor s24 = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) h_run
  rw [← congr_fun h_tail sevm.currentTarget, ← congr_fun hg3 sevm.currentTarget]
  exact h_stor18

/-- **The invariant-dependent strengthening of the burn** — the arc's
predeclared decision gate, written out so the two options can be compared
rather than argued about.

`of_burnAndReturn_val` states the supply write in `B256` arithmetic and claims
nothing about wrap-around, because the contract carries no supply-underflow
guard.  With the conservation invariant *at the burn's entry state* as an
explicit premise the wrap is ruled out: `wad ≤ rbal` is the code's own balance
check, `rbal ≤ Σ balances = supply` is `Stor.Conserved.le_supply`, and the
supply side becomes an honest subtraction.  Arc B's `of_burnAndReturn` supplies
the third conjunct unchanged.

**Where the premise can and cannot be discharged.**  It is a genuine invariant
of every reachable state (`fmint_preserves_conserved`), so *assuming* it is
honest.  But it is a premise about the state entering the *repayment*, which
sits on the far side of an arbitrary borrower frame: `of_flashLoanFromCall`
relates that state to the state at the `CALL` through `CallbackBoundary`
alone, and carries no conservation fact across it.  So a headline premised on
conservation at `flashLoan`'s *entry* does not reach here without a further
theorem carrying the invariant across the callback — which is why the arc's
storage postcondition takes the wrap-tolerant form and this lemma stands
beside it rather than inside it.  Whatever consumes this lemma is a statement
about conserved states, and that qualification travels with it. -/
lemma of_burnAndReturn_bound {fs : List Func} {sevm : Sevm} {s r : Devm}
    {wad : B256} {a : Adr} {bs : Bytes}
    (hs : [wad, a.toB256] <<+ s.stack)
    (h_wf : Mem.Wf s.memory) (h_reads : Mem.Reads s.memory bs)
    (h_cons : Stor.Conserved (Devm.getStor s sevm.currentTarget))
    (h_run : Func.Run fs sevm s burnAndReturn r) :
    wad ≤ (Devm.getStor s sevm.currentTarget).get supplySlot ∧
    ((Devm.getStor s sevm.currentTarget).get supplySlot - wad).toNat
      = ((Devm.getStor s sevm.currentTarget).get supplySlot).toNat - wad.toNat ∧
    Stor.Conserved (Devm.getStor r sevm.currentTarget) := by
  obtain ⟨h_le, -, -, -⟩ := of_burnAndReturn_val hs h_wf h_reads h_run
  have h_bound : wad ≤ (Devm.getStor s sevm.currentTarget).get supplySlot := by
    rcases B256.le_or_gt wad ((Devm.getStor s sevm.currentTarget).get supplySlot)
      with h | h
    · exact h
    · exfalso
      have h1 := B256.toNat_lt_toNat h
      have h2 := B256.toNat_le_toNat h_le
      have h3 := h_cons.le_supply a
      simp only [Stor.rest, Function.comp_apply] at h3
      omega
  exact ⟨h_bound, B256.toNat_sub_eq_of_le _ _ h_bound,
    of_burnAndReturn ⟨a, rfl⟩ hs h_cons h_run⟩

/-- **The repayment, end to end** — the allowance spend and the burn composed,
which is the shape Step 6's headline consumes.

`st` is the contract's storage after the allowance spend, and the whole
repayment is then: `st` is `s`'s storage with at most the one guarded
allowance slot moved, the receiver's balance at `st` covers the amount, and
`r`'s storage is `st` with the burn pair applied.  The frame returns
ABI-`true`, and no code moves.

That the two halves compose is what makes this lemma worth its twenty lines:
`of_spendAllowanceThenBurn_val` hands out exactly the stack, `Mem.Wf` and
`Mem.Reads` that `of_burnAndReturn_val` asks for. -/
lemma of_repayment {sevm : Sevm} {s r : Devm} {wad : B256} {a : Adr} {bs : Bytes}
    (hs : [wad, a.toB256] <<+ s.stack)
    (h_wf : Mem.Wf s.memory) (h_reads : Mem.Reads s.memory bs)
    (h_run : Func.Run (fmint.main :: fmintAux) sevm s spendAllowanceThenBurn r) :
    ¬ ValidAdr (repayKey a sevm.currentTarget) ∧
    repayKey a sevm.currentTarget ≠ supplySlot ∧
    ∃ (st : Stor) (allow : B256),
      allow = (Devm.getStor s sevm.currentTarget).get (repayKey a sevm.currentTarget) ∧
      ( (allow = B256.max ∧ st = Devm.getStor s sevm.currentTarget)
        ∨ (allow ≠ B256.max ∧ wad ≤ allow ∧
            st = (Devm.getStor s sevm.currentTarget).set
                  (repayKey a sevm.currentTarget) (allow - wad)) ) ∧
      wad ≤ st.get a.toB256 ∧
      Devm.getStor r sevm.currentTarget
        = (st.set a.toB256 (st.get a.toB256 - wad)).set supplySlot
            (st.get supplySlot - wad) ∧
      Devm.getCode s = Devm.getCode r ∧
      ReturnsTrue r := by
  obtain ⟨h_nva, h_nsup, sb, allow, h_allow, h_arms, h_code, h_stack, h_wfb,
    ⟨img, h_img⟩, h_burn⟩ := of_spendAllowanceThenBurn_val hs h_wf h_reads h_run
  obtain ⟨h_le, h_stor, h_code2, h_ret⟩ :=
    of_burnAndReturn_val h_stack h_wfb h_img h_burn
  refine ⟨h_nva, h_nsup, Devm.getStor sb sevm.currentTarget, allow, h_allow, ?_,
    h_le, h_stor, h_code.trans h_code2, h_ret⟩
  rcases h_arms with ⟨hmax, heq⟩ | ⟨hne, hle, heq⟩
  · exact Or.inl ⟨hmax, heq⟩
  · exact Or.inr ⟨hne, hle, heq⟩

/-! ## The headline, and the no-success family

`fmint_flashLoan_spec` composes Steps 2-5 off a single successful top-level
`Exec` at fmint's code.  Everything below it is a consequence of that theorem
or of the walk it is built from.

**Read the headline as partial correctness, and never as liveness.**  Its
prose form — "a successful `flashLoan` performs the callback" — sounds like a
statement that flash loans work.  It is not.  The `Exec` is a *hypothesis*
throughout: nothing in this module, or anywhere in this repository, says that
any `flashLoan` call ever succeeds, and the machinery that would be needed to
say so is separate, unstarted work (`~/plans/liveness-prelude-proposal.md`).

Four premises restrict what the headline covers, and they travel with every
description of it:

* `h_dec` — the calldata is the *canonical* Solidity-shaped encoding of the
  call.  fmint validates no tail offset (`FMINT_DEVIATIONS.md` row 21), so a
  non-canonical encoding is decodable by the contract and is **out of scope**
  here: the headline says nothing about it (`Sevm.DecodesCallWithTail`'s own
  docstring records the restriction and why closing it would be vacuous);
* `h_size` — the encoded callback fits a machine word (`196 + ceil32
  data.length < 2 ^ 256`); it implies the `data.length < 2 ^ 256` bound the
  tail round-trip needs, since `List.length` is an unbounded `Nat` while the
  ABI length word is 256 bits;
* `h_wf`/`h_fresh` — **frame freshness**, stated as an explicit premise
  rather than smuggled in.  `Exec 0 sevm pre` quantifies `pre` freely and does
  not know it came from Jaune's `initDevm`, which is where `memory := .empty`
  actually comes from; the frame semantics discharge it at any real call site;
* `h_sel` — the calldata's selector word routes to `flashLoan`.

The storage postcondition is **wrap-tolerant `B256` arithmetic and carries no
`Stor.Conserved` premise**, so the headline is *not* a statement about states
satisfying the conservation invariant.  (That qualification attaches only to
consumers of `of_burnAndReturn_bound`, whose docstring carries it.)  The
reason is recorded there: conservation at `flashLoan`'s entry does not reach
the repayment's entry state, because `CallbackBoundary` deliberately carries no
storage relation across the borrower's frame.

**`h_sel` and `h_dec` are jointly satisfiable, and not by accident.**  The
canonical encoding *begins* with `flashLoanSelector`'s four bytes, so `h_sel` is
a fact `h_dec`'s own bytes carry; it is a separate premise only because
recovering it formally needs `>>>` arithmetic on `B256`, which is a nested pair
of `UInt64`s with no bitvector API (the arc's `3-b256-has-no-bitvector-api`
finding).  Witnesses exist concretely: `scripts/check-fmint.sh`'s `flashLoan`
fixtures are canonically encoded calls that route to this entry point. -/

/-- **The headline: a successful `flashLoan` performed the callback, and was
repaid.**

Given a successful top-level `Exec` at fmint's compiled code whose calldata is
a canonically encoded `flashLoan(receiver, token, amount, data)`:

* `token` is this contract — ERC-3156's `token = self` guard, reached before
  the bound check;
* `amount` does not overflow the supply — fmint's `amount ≤ maxFlashLoan`
  bound, with `maxFlashLoan = 2 ^ 256 - 1 - supply`;
* the frame returned ABI-`true`;
* `receiver` is address-shaped, and naming `a` for it is what makes the
  callback's callee equal to `receiver` on the nose;
* the **mint** landed in `sc`, the state the callback is entered in: both
  `SSTORE`s complete before the `CALL` (proposal D5), so this is a fact about
  the state the borrower sees, not only about the state it is left in;
* a **callback boundary** relates `sc` to `mid`, the same frame at resumption:
  the borrower's `onFlashLoan(initiator, token, amount, 0, data)` frame
  actually ran, on the canonical ABI encoding of those five arguments, and
  answered with the ERC-3156 magic word.  `CallbackBoundary`'s own docstring is
  the clause-by-clause reading;
* the **repayment** then spent an allowance — either the infinite arm, which
  writes nothing, or the finite arm, which requires `amount ≤ allow` and
  decrements — and burned the principal from the receiver and from the supply.
  The allowance key is `keccak256(receiver ‖ address(this))`: the spender is
  `address(this)`, not `caller`, and there is no `src = caller` bypass.

The allowance and the balance are read at `mid`, **after** the callback: a
borrower may set both from inside `onFlashLoan`, and a statement about them at
`pre` would be a different — and false — claim.

**Partial correctness, not liveness**; see this section's banner for that and
for the four premises' scope. -/
theorem fmint_flashLoan_spec {sevm : Sevm} {pre post : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf pre.memory) (h_fresh : Mem.Reads pre.memory [])
    (exc : Exec 0 sevm pre (.ok post)) :
    token = sevm.currentTarget.toB256 ∧
    B256.Nof ((Devm.getStor pre sevm.currentTarget).get supplySlot) amount ∧
    ReturnsTrue post ∧
    ∃ (a : Adr) (sc mid : Devm) (st : Stor) (allow : B256),
      receiver = a.toB256 ∧
      Devm.getCode pre = Devm.getCode sc ∧
      Devm.getStor sc sevm.currentTarget =
        ((Devm.getStor pre sevm.currentTarget).set a.toB256
            (amount + (Devm.getStor pre sevm.currentTarget).get a.toB256)).set
          supplySlot
          (amount + (Devm.getStor pre sevm.currentTarget).get supplySlot) ∧
      CallbackBoundary sevm sevm.currentTarget a amount data sc mid ∧
      ¬ ValidAdr (repayKey a sevm.currentTarget) ∧
      repayKey a sevm.currentTarget ≠ supplySlot ∧
      allow = (Devm.getStor mid sevm.currentTarget).get
        (repayKey a sevm.currentTarget) ∧
      ( (allow = B256.max ∧ st = Devm.getStor mid sevm.currentTarget)
        ∨ (allow ≠ B256.max ∧ amount ≤ allow ∧
            st = (Devm.getStor mid sevm.currentTarget).set
              (repayKey a sevm.currentTarget) (allow - amount)) ) ∧
      amount ≤ (Devm.getStor mid sevm.currentTarget).get a.toB256 ∧
      Devm.getStor post sevm.currentTarget =
        (st.set a.toB256 (st.get a.toB256 - amount)).set supplySlot
          (st.get supplySlot - amount) ∧
      Devm.getCode mid = Devm.getCode post := by
  obtain ⟨s, h_gs, h_gb, h_gc, h_mem, h_run⟩ := exec_enters_flashLoan exc h_code h_sel
  obtain ⟨h_token, h_nof, a, sc, mid, sfin, h_recv, h_code_sc, h_stor_sc, h_cb,
    h_gs_mid, h_gc_mid, h_stack, h_wf_fin, ⟨img, h_img⟩, h_run5⟩ :=
    flashLoan_performs_callback h_dec h_size (h_mem ▸ h_wf) (h_mem ▸ h_fresh) h_run
  obtain ⟨h_nva, h_nsup, st, allow, h_allow, h_arms, h_bal, h_post, h_code_post,
    h_ret⟩ := of_repayment h_stack h_wf_fin h_img h_run5
  -- restate the walk's facts at the states a reader can name: `pre`, the
  -- frame's own entry, and `mid`, the state the callback returns in
  rw [h_gs] at h_nof h_stor_sc
  rw [← h_gs_mid] at h_allow h_arms
  have h_key_ne : repayKey a sevm.currentTarget ≠ a.toB256 :=
    fun h => h_nva ⟨a, h.symm⟩
  have h_bal' : amount ≤ (Devm.getStor mid sevm.currentTarget).get a.toB256 := by
    rcases h_arms with ⟨-, heq⟩ | ⟨-, -, heq⟩
    · rw [heq] at h_bal; exact h_bal
    · rw [heq, Stor.get_set_ne _ h_key_ne] at h_bal; exact h_bal
  exact ⟨h_token, h_nof, h_ret, a, sc, mid, st, allow, h_recv,
    h_gc.symm.trans h_code_sc, h_stor_sc, h_cb, h_nva, h_nsup, h_allow, h_arms,
    h_bal', h_post, h_gc_mid.trans h_code_post⟩

/-! ### The no-success family

Seven statements of the form "… ⇒ this `Exec` did not succeed".  They are
**not all the same kind of theorem**, and the difference is the precision this
section exists to get right.

**Two are contrapositives of the headline** — `no_success_of_callback_never_magic`
and `no_success_of_callback_never_returns_word`.  Each negates a clause of
`CallbackBoundary`, so each is exactly as strong as the relation is.  Read the
quantifier: the premise is that **no** boundary the headline could produce
answers with the magic word (respectively, with a full word at all).  It is
*not* the stronger reading "if the receiver's code returns `X` then no success":
`CallbackBoundary` pins the callback frame by equations — the message from the
five arguments, `mid` from `child` — but it does not prove that frame *unique*.
The 2026-08-06 audit of this question (`~/plans/fmint-restoration.md`, decision
gate C) enumerated the seven existentials against `pre`.  Three *are* pinned:
`gw` is `pre.stack`'s head, `receiver` follows from the next word because
`Adr.toB256` is injective, and `dp`/`code` follow from
`getDelegatedCodeAddress (pre.getCode receiver)`.  The other four are not, and
one of them is decisive: **`parent` is constrained only by `parent.stack` and
`parent.state = pre.state`**, so its memory, gas, transient storage and access
sets are free — and `callMsg` and `Resume.call` both read them, so `child` and
`mid` are not functions of `pre` at all.  `avail` is likewise free
(`calculateMsgCallGas_stipend` is itself an existential over the *caller's*
charged machine), and the slot needs a `ProcessMessage` determinism lemma that
does not exist here.  So the honest form quantifies over every admissible
boundary, and that is the form stated here.

**Five are contrapositives of the guards**, not of the headline, and they never
were: `token ≠ self`, a dirty `receiver` word, `amount` past the mint headroom,
an allowance below `amount`, a balance below `amount`.  Each reads a fact off
the same walk `of_flashLoan_toCall` performs, and the first three need neither
the size premise nor frame freshness.  The guard facts themselves
(`flashLoan_guards`) hold with **no** encoding premise at all; `h_dec` appears
below only so the statements can name `token`, `receiver` and `amount` instead
of calldata head words.

**State restoration is not in this family**, and none of these may be read as
one.  They say a call did not succeed; they say nothing about the state coming
back.  A restoration claim is a separate frame-level theorem — a failed inner
call can be caught by its caller while the surrounding transaction succeeds, so
such a claim must name its frame.  Those theorems are the *next* section:
`rollback_of_no_success` and its seven instantiations take one of these seven
premises and add the frame's own message, returning `out.error.isSome` together
with the restored world.  They are strictly separate statements with strictly
more premises, and reading one of the seven below as though it already said
that is the confusion this paragraph exists to prevent.

As everywhere in this module, these are **partial correctness**: they rule
executions out, and nothing rules any execution in. -/

/-- What the boundary says about the answer, read off the frame's own
resumption state.  `mid.returnData` is `child.output` by the relation's own
equation, so a consumer never has to name the child frame. -/
lemma CallbackBoundary.answer {sevm : Sevm} {fa receiver : Adr} {amount : B256}
    {data : Bytes} {pre mid : Devm}
    (h : CallbackBoundary sevm fa receiver amount data pre mid) :
    32 ≤ mid.returnData.length ∧
      Bytes.toB256 (mid.returnData.sliceD 0 32 0) = erc3156Magic := by
  obtain ⟨_, child, _, _, _, _, _, -, -, -, -, -, -, hlen, hmagic, -, -, hrd, -⟩ := h
  rw [hrd]; exact ⟨hlen, hmagic⟩

/-- **Wrong magic word ⇒ no success.**  A contrapositive of the headline: if no
callback boundary this call could open answers with `erc3156Magic`, the
top-level `Exec` cannot have succeeded.  See the section banner for why the
premise quantifies over boundaries rather than over the receiver's code. -/
theorem no_success_of_callback_never_magic {sevm : Sevm} {pre post : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf pre.memory) (h_fresh : Mem.Reads pre.memory [])
    (h_never : ∀ (a : Adr) (sc mid : Devm),
      CallbackBoundary sevm sevm.currentTarget a amount data sc mid →
      Bytes.toB256 (mid.returnData.sliceD 0 32 0) ≠ erc3156Magic) :
    Exec 0 sevm pre (.ok post) → False := by
  intro exc
  obtain ⟨-, -, -, a, sc, mid, _, _, -, -, -, h_cb, -⟩ :=
    fmint_flashLoan_spec h_code h_sel h_dec h_size h_wf h_fresh exc
  exact h_never a sc mid h_cb (CallbackBoundary.answer h_cb).right

/-- **Returndata shorter than a word ⇒ no success.**  The other contrapositive
of the headline: the boundary requires at least one word of returndata before
the magic check even reads one, so a callback that returns less cannot have
been part of a successful call.  Same quantifier reading as its sibling. -/
theorem no_success_of_callback_never_returns_word {sevm : Sevm} {pre post : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf pre.memory) (h_fresh : Mem.Reads pre.memory [])
    (h_short : ∀ (a : Adr) (sc mid : Devm),
      CallbackBoundary sevm sevm.currentTarget a amount data sc mid →
      mid.returnData.length < 32) :
    Exec 0 sevm pre (.ok post) → False := by
  intro exc
  obtain ⟨-, -, -, a, sc, mid, _, _, -, -, -, h_cb, -⟩ :=
    fmint_flashLoan_spec h_code h_sel h_dec h_size h_wf h_fresh exc
  exact absurd (CallbackBoundary.answer h_cb).left
    (Nat.not_le_of_lt (h_short a sc mid h_cb))

/-- **`token ≠ self` ⇒ no success.**  A contrapositive of guard (0), not of the
headline: ERC-3156's `token` check is one explicit guard placed *before* the
bound check, so the revert reason does not depend on `amount`
(`FMINT_DEVIATIONS.md` row 5). -/
theorem no_success_of_token_ne_self {sevm : Sevm} {pre post : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_ne : token ≠ sevm.currentTarget.toB256) :
    Exec 0 sevm pre (.ok post) → False := by
  intro exc
  obtain ⟨s, -, -, -, -, h_run⟩ := exec_enters_flashLoan exc h_code h_sel
  exact h_ne ((argWord_one_of_decodes h_dec).symm.trans (flashLoan_guards h_run).left)

/-- **A `receiver` word that is not address-shaped ⇒ no success.**  A
contrapositive of guard (1).  The guard pays twice: Arc B proved it
conservation-critical, and it is also what makes the callback's callee equal to
`receiver` on the nose, since `Devm.popToAdr` truncates to 160 bits and the
guard makes that truncation the identity. -/
theorem no_success_of_receiver_not_address {sevm : Sevm} {pre post : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_dirty : ¬ ValidAdr receiver) :
    Exec 0 sevm pre (.ok post) → False := by
  intro exc
  obtain ⟨s, -, -, -, -, h_run⟩ := exec_enters_flashLoan exc h_code h_sel
  exact h_dirty ((argWord_zero_of_decodes h_dec) ▸ (flashLoan_guards h_run).right.left)

/-- **`amount` past `maxFlashLoan` ⇒ no success.**  A contrapositive of guard
(2).  The bound is `~~~ supply`, i.e. `2 ^ 256 - 1 - totalSupply`, which is the
value `Fmint.maxFlashLoan`'s body computes for `token = self` — visible in that
definition, though **no theorem in this arc walks that entry point**, so this
states the bound and not the view function's answer.  The supply named is the
one in storage at the frame's entry, which is the right one: nothing before the
guard writes storage. -/
theorem no_success_of_amount_over_maxFlashLoan {sevm : Sevm} {pre post : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_over : ~~~ ((Devm.getStor pre sevm.currentTarget).get supplySlot) < amount) :
    Exec 0 sevm pre (.ok post) → False := by
  intro exc
  obtain ⟨s, h_gs, -, -, -, h_run⟩ := exec_enters_flashLoan exc h_code h_sel
  have h_nof := (flashLoan_guards h_run).right.right
  rw [h_gs, argWord_two_of_decodes h_dec] at h_nof
  exact B256.not_lt.mpr (B256.le_not_of_nof h_nof) h_over

/-- **An allowance below `amount` ⇒ no success.**  A contrapositive of the
repayment's allowance arms, read at `mid` — **after** the callback, which is
where the contract reads it.  A borrower may approve from inside `onFlashLoan`,
so the same statement at the frame's entry would be a different and false claim.
The infinite arm is not an escape: `amount ≤ B256.max` always, so an allowance
strictly below `amount` is not `B256.max`. -/
theorem no_success_of_allowance_below_amount {sevm : Sevm} {pre post : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf pre.memory) (h_fresh : Mem.Reads pre.memory [])
    (h_low : ∀ (a : Adr) (sc mid : Devm),
      CallbackBoundary sevm sevm.currentTarget a amount data sc mid →
      (Devm.getStor mid sevm.currentTarget).get (repayKey a sevm.currentTarget)
        < amount) :
    Exec 0 sevm pre (.ok post) → False := by
  intro exc
  obtain ⟨-, -, -, a, sc, mid, st, allow, -, -, -, h_cb, -, -, h_allow, h_arms, -⟩ :=
    fmint_flashLoan_spec h_code h_sel h_dec h_size h_wf h_fresh exc
  have h_lt : allow < amount := h_allow ▸ h_low a sc mid h_cb
  rcases h_arms with ⟨hmax, -⟩ | ⟨-, hle, -⟩
  · exact B256.not_lt.mpr (B256.le_max amount) (hmax ▸ h_lt)
  · exact B256.not_lt.mpr hle h_lt

/-- **A receiver balance below `amount` ⇒ no success.**  A contrapositive of
the burn's balance check, read at `mid` for the same reason as the allowance:
the borrower holds the principal during the callback and the check happens
after it.  The allowance write cannot disturb the reading — its key is guarded
non-address-shaped, so it is a different slot from the receiver's balance. -/
theorem no_success_of_balance_below_amount {sevm : Sevm} {pre post : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf pre.memory) (h_fresh : Mem.Reads pre.memory [])
    (h_low : ∀ (a : Adr) (sc mid : Devm),
      CallbackBoundary sevm sevm.currentTarget a amount data sc mid →
      (Devm.getStor mid sevm.currentTarget).get a.toB256 < amount) :
    Exec 0 sevm pre (.ok post) → False := by
  intro exc
  obtain ⟨-, -, -, a, sc, mid, st, allow, -, -, -, h_cb, -, -, -, -, h_bal, -⟩ :=
    fmint_flashLoan_spec h_code h_sel h_dec h_size h_wf h_fresh exc
  exact B256.not_lt.mpr h_bal (h_low a sc mid h_cb)

/-! ### The error channel: the weak form of the no-success family

Jaune's `exec` is a **total function** into `Except (EvmError × Devm) Devm`, so
each `no_success_of_*` theorem above is one case away from a positive
statement: if no `.ok` outcome exists, the total function must have returned
`.error`.  `Blanc.exec_error_of_no_success` (`Blanc/CommonProofs.lean`) is that
one case, contract-agnostic; the seven corollaries below apply it to the seven
premises above, unchanged.  Named by the rule `no_success_of_X ↦
settles_with_error_of_X`.

**These name an error CHANNEL, not an error KIND.**  No `EvmError` constructor
is pinned by any of the seven — in particular, none of them says "reverts".
Each conclusion is exactly `∃ e post, exec ⟨0, sevm, pre⟩ = .error (e, post)`,
with `e` existentially bound: it is whichever error the total function
happens to return for an execution that was going to fail anyway, not a
constructor derived from walking the machine.  Pinning `e` — in this arc's
case, showing it is always `EvmError.revert` on these paths — is later work
(`~/plans/error-genre.md`'s Steps 2-3).

**These are still partial correctness, not liveness.**  Like their
`no_success_of_*` sources, they rule executions *out*; nothing here rules any
execution *in*, and nothing says any of these calls is ever made.

**These are at message-call altitude — one frame, not a transaction.**  `exec`
is Jaune's single-frame semantics; nothing here says what a caller observes,
or whether a surrounding transaction rolls back.  `~/plans/error-genre.md`'s
Step 4 lands the frame-level composition that connects this weak form to the
restoration family below. -/

/-- **Wrong magic word ⇒ settles with some error.**  The weak form of
`no_success_of_callback_never_magic`.  Read the quantifier as that theorem's
docstring and this file's no-success-family banner do: "the premise is that
**no** boundary the headline could produce answers with the magic word
(respectively, with a full word at all).  It is *not* the stronger reading
'if the receiver's code returns `X` then no success': `CallbackBoundary` pins
the callback frame by equations — the message from the five arguments, `mid`
from `child` — but it does not prove that frame *unique*." -/
theorem settles_with_error_of_callback_never_magic {sevm : Sevm} {pre : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf pre.memory) (h_fresh : Mem.Reads pre.memory [])
    (h_never : ∀ (a : Adr) (sc mid : Devm),
      CallbackBoundary sevm sevm.currentTarget a amount data sc mid →
      Bytes.toB256 (mid.returnData.sliceD 0 32 0) ≠ erc3156Magic) :
    ∃ e post, exec ⟨0, sevm, pre⟩ = .error (e, post) :=
  exec_error_of_no_success
    (fun _post exc => no_success_of_callback_never_magic h_code h_sel h_dec
      h_size h_wf h_fresh h_never exc)

/-- **Returndata shorter than a word ⇒ settles with some error.**  The weak
form of `no_success_of_callback_never_returns_word`.  Same quantifier reading
as its sibling above: "the premise is that **no** boundary the headline could
produce answers with the magic word (respectively, with a full word at all).
It is *not* the stronger reading 'if the receiver's code returns `X` then no
success': `CallbackBoundary` pins the callback frame by equations — the
message from the five arguments, `mid` from `child` — but it does not prove
that frame *unique*." -/
theorem settles_with_error_of_callback_never_returns_word {sevm : Sevm}
    {pre : Devm} {receiver token amount : B256} {data : Bytes}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf pre.memory) (h_fresh : Mem.Reads pre.memory [])
    (h_short : ∀ (a : Adr) (sc mid : Devm),
      CallbackBoundary sevm sevm.currentTarget a amount data sc mid →
      mid.returnData.length < 32) :
    ∃ e post, exec ⟨0, sevm, pre⟩ = .error (e, post) :=
  exec_error_of_no_success
    (fun _post exc => no_success_of_callback_never_returns_word h_code h_sel
      h_dec h_size h_wf h_fresh h_short exc)

/-- **`token ≠ self` ⇒ settles with some error.**  The weak form of
`no_success_of_token_ne_self`; see that theorem's docstring for why the
revert reason does not depend on `amount`. -/
theorem settles_with_error_of_token_ne_self {sevm : Sevm} {pre : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_ne : token ≠ sevm.currentTarget.toB256) :
    ∃ e post, exec ⟨0, sevm, pre⟩ = .error (e, post) :=
  exec_error_of_no_success
    (fun _post exc => no_success_of_token_ne_self h_code h_sel h_dec h_ne exc)

/-- **A `receiver` word that is not address-shaped ⇒ settles with some
error.**  The weak form of `no_success_of_receiver_not_address`. -/
theorem settles_with_error_of_receiver_not_address {sevm : Sevm} {pre : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_dirty : ¬ ValidAdr receiver) :
    ∃ e post, exec ⟨0, sevm, pre⟩ = .error (e, post) :=
  exec_error_of_no_success
    (fun _post exc =>
      no_success_of_receiver_not_address h_code h_sel h_dec h_dirty exc)

/-- **`amount` past `maxFlashLoan` ⇒ settles with some error.**  The weak form
of `no_success_of_amount_over_maxFlashLoan`. -/
theorem settles_with_error_of_amount_over_maxFlashLoan {sevm : Sevm}
    {pre : Devm} {receiver token amount : B256} {data : Bytes}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_over : ~~~ ((Devm.getStor pre sevm.currentTarget).get supplySlot) < amount) :
    ∃ e post, exec ⟨0, sevm, pre⟩ = .error (e, post) :=
  exec_error_of_no_success
    (fun _post exc =>
      no_success_of_amount_over_maxFlashLoan h_code h_sel h_dec h_over exc)

/-- **An allowance below `amount` ⇒ settles with some error.**  The weak form
of `no_success_of_allowance_below_amount`; the allowance is read at `mid`,
after the callback, for the reason that theorem's docstring gives. -/
theorem settles_with_error_of_allowance_below_amount {sevm : Sevm} {pre : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf pre.memory) (h_fresh : Mem.Reads pre.memory [])
    (h_low : ∀ (a : Adr) (sc mid : Devm),
      CallbackBoundary sevm sevm.currentTarget a amount data sc mid →
      (Devm.getStor mid sevm.currentTarget).get (repayKey a sevm.currentTarget)
        < amount) :
    ∃ e post, exec ⟨0, sevm, pre⟩ = .error (e, post) :=
  exec_error_of_no_success
    (fun _post exc => no_success_of_allowance_below_amount h_code h_sel h_dec
      h_size h_wf h_fresh h_low exc)

/-- **A receiver balance below `amount` ⇒ settles with some error.**  The weak
form of `no_success_of_balance_below_amount`; the balance is read at `mid`,
after the callback, for the reason that theorem's docstring gives. -/
theorem settles_with_error_of_balance_below_amount {sevm : Sevm} {pre : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf pre.memory) (h_fresh : Mem.Reads pre.memory [])
    (h_low : ∀ (a : Adr) (sc mid : Devm),
      CallbackBoundary sevm sevm.currentTarget a amount data sc mid →
      (Devm.getStor mid sevm.currentTarget).get a.toB256 < amount) :
    ∃ e post, exec ⟨0, sevm, pre⟩ = .error (e, post) :=
  exec_error_of_no_success
    (fun _post exc => no_success_of_balance_below_amount h_code h_sel h_dec
      h_size h_wf h_fresh h_low exc)

/-! ### Frame-level restoration under a no-success premise

The family above rules executions *out*.  This one says what the frame's own
caller is handed when one of those rulings applies: the frame settles with its
error flag set, and the state and transient storage it comes back with are the
ones the message entered with.  Together with
`ProcessMessage.rollback_of_error` (the generic mechanism, `CommonProofs.lean`)
and `rollback_of_callback_failure` (the borrower's frame, above), these are the
restoration family of `~/plans/fmint-restoration.md`.

**Every statement names its frame, and the frame is `msg`'s own** — the frame
`processMessage` opened for this message.  It is emphatically *not* the
transaction.  A failed inner call can be caught by its caller while the
surrounding transaction succeeds, so "the transaction was rolled back" is a
different claim and is frequently false; nothing here says it.  These
statements are also silent about fmint's caller, deliberately.

**No error kind is named.**  The conclusion is `out.error.isSome`, never
*which* error.  Two independent reasons: the relational layer this is phrased
in is `.ok`-level only, so nothing about an error *value* transfers; and
fmint's failure shapes are artefacts of compiled bytes that the hygiene arc
changed underneath this family, so a claim naming one would be coupled to bytes
a restoration statement has no business knowing.

**This is not liveness, and is not implied by the success spec.**  Every
premise is in hypothesis position.  Nothing here asserts that any `flashLoan`
call is ever made, ever fails, or ever runs at all.  As everywhere in this
module, these are partial correctness: they say what *would* be handed back,
not that anything happens. -/

/-- **A frame that cannot succeed settles with an error, and rolled back.**
Given a `processMessage` frame that settled `.ok out`, a filled slot, the
frame's post-transfer environment `benv`, the exclusion of the precompile entry
mode, and the fact that *no* successful `Exec` starts from this frame's entry
machine, the settled result carries an error flag and its world is exactly
`msg`'s entry world.

The shared core is stated **once**, over the abstract premise `h_none`; each of
the seven `no_success_of_*` corollaries below instantiates it in a single line.

**Why `h_fill` is a premise.**  `ProcessMessage msg xl (.ok out)` leaves the raw
execution result in the slot entirely unconstrained, so without
`Xlot.Filled xl` there is no derivation for `h_none` to contradict, the
clean-success branch cannot be refuted, and the statement would be false as
written.  The premise is idiomatic rather than a patch — `CallbackBoundary`
carries one too — and `rollback_of_no_success_total` below discharges it once
and for all for a caller who holds the total function's equation instead.

**Why `h_prec` is a premise.**  Frame entry splits into a precompile answer and
an interpreted-code execution.  In the precompile branch there is no `Exec` at
all for `h_none` to contradict, and the frame demonstrably *can* settle cleanly
there, so the conclusion `out.error.isSome` is simply **false** in that branch.
`CallbackBoundary.entry_modes` set this module's precedent of carrying the
precompile case explicitly rather than assuming it away; carrying it is
impossible here, so it is excluded by an honest, checkable premise instead.  A
precompile address holding fmint's code is not the situation this theorem is
about, and `h_prec` says so out loud.  Note its shape: it is
`of_executeCode_someCode`'s guard, and it is demanded only of a `codeAddress`
that is `some` — a frame with no code address has no precompile branch to
exclude, and is asked for nothing.

**Contract-agnostic.**  Nothing above `h_none` mentions fmint, so the proof
lives in the shared `Blanc/Ladder.lean` layer.  This declaration preserves the
original `Blanc.Fmint` API while the seven consumers below call the shared core
directly. -/
theorem rollback_of_no_success {msg : Msg} {benv : Benv} {xl : Xlot} {out : Devm}
    (h_pm : ProcessMessage msg xl (.ok out))
    (h_fill : Xlot.Filled xl)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles && decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_none : ∀ post, Exec 0 (initSevm (msg.withBenv benv))
        (initDevm (msg.withBenv benv)) (.ok post) → False) :
    out.error.isSome ∧
      out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage := by
  exact Blanc.rollback_of_no_success h_pm h_fill h_bt h_prec h_none

/-- **The same statement off the total function.**  `of_processMessage` produces
the slot *and* its `Filled` proof from `processMessage msg = .ok out`, so a
caller holding the equation supplies neither.  Same frame — `msg`'s own — same
absence of an error kind, and still not liveness: the equation is a hypothesis
about a run that is given, not a claim that one occurs. -/
theorem rollback_of_no_success_total {msg : Msg} {benv : Benv} {out : Devm}
    (h_run : processMessage msg = .ok out)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles && decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_none : ∀ post, Exec 0 (initSevm (msg.withBenv benv))
        (initDevm (msg.withBenv benv)) (.ok post) → False) :
    out.error.isSome ∧
      out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage := by
  exact Blanc.rollback_of_no_success_total h_run h_bt h_prec h_none

/-- **Wrong magic word ⇒ the frame settled with an error, rolled back.**  The
restoration form of `no_success_of_callback_never_magic`, at the frame
`processMessage` opened for `msg`.

Its premises are that corollary's, read at this frame's **entry machine** —
`initSevm (msg.withBenv benv)` and `initDevm (msg.withBenv benv)`, i.e. after
the value transfer `h_bt` names — plus the core's `h_fill` and `h_prec`.  The
restrictions travel with it unchanged:

* **canonical encoding** — `h_dec` is the canonical Solidity-shaped encoding.
  fmint validates no tail offset (`FMINT_DEVIATIONS.md` row 21), so a
  non-canonical encoding is decodable by the contract and is **out of scope**;
* **the size bound** `196 + ceil32 data.length < 2 ^ 256`;
* **frame freshness** — `h_wf`/`h_fresh` on the entry memory, stated rather
  than smuggled in;
* **the boundary-quantified reading of `h_never`** — the premise quantifies
  over *every* boundary this call could open, because `ProcessMessage` is a
  relation with no determinism lemma here and `gw`, `avail` and the slot stay
  existential.  It is **not** "if the receiver's code returns `X`".

Frame, error kind and liveness: see this section's banner. -/
theorem rollback_of_callback_never_magic {msg : Msg} {benv : Benv} {xl : Xlot}
    {out : Devm} {receiver token amount : B256} {data : Bytes}
    (h_pm : ProcessMessage msg xl (.ok out))
    (h_fill : Xlot.Filled xl)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles && decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_code : some (initSevm (msg.withBenv benv)).code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector (initSevm (msg.withBenv benv)) = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail (initSevm (msg.withBenv benv))
      flashLoanSelector [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf (initDevm (msg.withBenv benv)).memory)
    (h_fresh : Mem.Reads (initDevm (msg.withBenv benv)).memory [])
    (h_never : ∀ (a : Adr) (sc mid : Devm),
      CallbackBoundary (initSevm (msg.withBenv benv))
        (initSevm (msg.withBenv benv)).currentTarget a amount data sc mid →
      Bytes.toB256 (mid.returnData.sliceD 0 32 0) ≠ erc3156Magic) :
    out.error.isSome ∧
      out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage :=
  Blanc.rollback_of_no_success h_pm h_fill h_bt h_prec
    (fun _ exc => no_success_of_callback_never_magic h_code h_sel h_dec h_size
      h_wf h_fresh h_never exc)

/-- **Returndata shorter than a word ⇒ the frame settled with an error, rolled
back.**  The restoration form of `no_success_of_callback_never_returns_word`,
at `msg`'s own frame.

Same inherited restrictions as its sibling above: canonical encoding
(`FMINT_DEVIATIONS.md` row 21), the size bound, frame freshness on the entry
memory, and the **boundary-quantified** reading of `h_short` — no boundary this
call could open answers with a full word, not "the receiver's code returns
short".  Premises are read at the entry machine
`initSevm (msg.withBenv benv)` / `initDevm (msg.withBenv benv)`.

Frame, error kind and liveness: see this section's banner. -/
theorem rollback_of_callback_never_returns_word {msg : Msg} {benv : Benv}
    {xl : Xlot} {out : Devm} {receiver token amount : B256} {data : Bytes}
    (h_pm : ProcessMessage msg xl (.ok out))
    (h_fill : Xlot.Filled xl)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles && decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_code : some (initSevm (msg.withBenv benv)).code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector (initSevm (msg.withBenv benv)) = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail (initSevm (msg.withBenv benv))
      flashLoanSelector [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf (initDevm (msg.withBenv benv)).memory)
    (h_fresh : Mem.Reads (initDevm (msg.withBenv benv)).memory [])
    (h_short : ∀ (a : Adr) (sc mid : Devm),
      CallbackBoundary (initSevm (msg.withBenv benv))
        (initSevm (msg.withBenv benv)).currentTarget a amount data sc mid →
      mid.returnData.length < 32) :
    out.error.isSome ∧
      out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage :=
  Blanc.rollback_of_no_success h_pm h_fill h_bt h_prec
    (fun _ exc => no_success_of_callback_never_returns_word h_code h_sel h_dec
      h_size h_wf h_fresh h_short exc)

/-- **`token ≠ self` ⇒ the frame settled with an error, rolled back.**  The
restoration form of `no_success_of_token_ne_self`, at `msg`'s own frame.

A contrapositive of guard (0), so it needs **neither the size bound nor frame
freshness** and is not given them: a corollary must not acquire premises it
does not use.  The one restriction it inherits is **canonical encoding**
(`h_dec`; `FMINT_DEVIATIONS.md` row 21 — a non-canonical encoding is decodable
by the contract and out of scope).  Premises are read at the entry machine
`initSevm (msg.withBenv benv)`.

Frame, error kind and liveness: see this section's banner. -/
theorem rollback_of_token_ne_self {msg : Msg} {benv : Benv} {xl : Xlot}
    {out : Devm} {receiver token amount : B256} {data : Bytes}
    (h_pm : ProcessMessage msg xl (.ok out))
    (h_fill : Xlot.Filled xl)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles && decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_code : some (initSevm (msg.withBenv benv)).code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector (initSevm (msg.withBenv benv)) = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail (initSevm (msg.withBenv benv))
      flashLoanSelector [receiver, token, amount] data)
    (h_ne : token ≠ (initSevm (msg.withBenv benv)).currentTarget.toB256) :
    out.error.isSome ∧
      out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage :=
  Blanc.rollback_of_no_success h_pm h_fill h_bt h_prec
    (fun _ exc => no_success_of_token_ne_self h_code h_sel h_dec h_ne exc)

/-- **A `receiver` word that is not address-shaped ⇒ the frame settled with an
error, rolled back.**  The restoration form of
`no_success_of_receiver_not_address`, at `msg`'s own frame.

A contrapositive of guard (1): like its two neighbours it needs **neither the
size bound nor frame freshness**, and inherits only the **canonical-encoding**
restriction (`h_dec`; `FMINT_DEVIATIONS.md` row 21).  Premises are read at the
entry machine `initSevm (msg.withBenv benv)`.

Frame, error kind and liveness: see this section's banner. -/
theorem rollback_of_receiver_not_address {msg : Msg} {benv : Benv} {xl : Xlot}
    {out : Devm} {receiver token amount : B256} {data : Bytes}
    (h_pm : ProcessMessage msg xl (.ok out))
    (h_fill : Xlot.Filled xl)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles && decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_code : some (initSevm (msg.withBenv benv)).code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector (initSevm (msg.withBenv benv)) = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail (initSevm (msg.withBenv benv))
      flashLoanSelector [receiver, token, amount] data)
    (h_dirty : ¬ ValidAdr receiver) :
    out.error.isSome ∧
      out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage :=
  Blanc.rollback_of_no_success h_pm h_fill h_bt h_prec
    (fun _ exc => no_success_of_receiver_not_address h_code h_sel h_dec h_dirty exc)

/-- **`amount` past `maxFlashLoan` ⇒ the frame settled with an error, rolled
back.**  The restoration form of `no_success_of_amount_over_maxFlashLoan`, at
`msg`'s own frame.

A contrapositive of guard (2), so again **no size bound and no frame
freshness** — only the **canonical-encoding** restriction (`h_dec`;
`FMINT_DEVIATIONS.md` row 21).  The supply named is the one in storage at the
frame's entry, read off `initDevm (msg.withBenv benv)`, which is the right one:
nothing before the guard writes storage.  As in the underlying corollary this
states the bound `~~~ supply` and not `maxFlashLoan`'s answer — no theorem
walks that view function.

Frame, error kind and liveness: see this section's banner. -/
theorem rollback_of_amount_over_maxFlashLoan {msg : Msg} {benv : Benv} {xl : Xlot}
    {out : Devm} {receiver token amount : B256} {data : Bytes}
    (h_pm : ProcessMessage msg xl (.ok out))
    (h_fill : Xlot.Filled xl)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles && decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_code : some (initSevm (msg.withBenv benv)).code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector (initSevm (msg.withBenv benv)) = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail (initSevm (msg.withBenv benv))
      flashLoanSelector [receiver, token, amount] data)
    (h_over : ~~~ ((Devm.getStor (initDevm (msg.withBenv benv))
      (initSevm (msg.withBenv benv)).currentTarget).get supplySlot) < amount) :
    out.error.isSome ∧
      out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage :=
  Blanc.rollback_of_no_success h_pm h_fill h_bt h_prec
    (fun _ exc => no_success_of_amount_over_maxFlashLoan h_code h_sel h_dec h_over exc)

/-- **An allowance below `amount` ⇒ the frame settled with an error, rolled
back.**  The restoration form of `no_success_of_allowance_below_amount`, at
`msg`'s own frame.

Inherits the full premise set of its corollary, read at the entry machine:
**canonical encoding** (`FMINT_DEVIATIONS.md` row 21), the **size bound**, and
**frame freshness** on the entry memory.  `h_low` is **boundary-quantified**
for the same reason as the two headline contrapositives — every boundary the
call could open, not the receiver's code — and it is read at `mid`, *after* the
callback, because that is where the contract reads it: a borrower may approve
from inside `onFlashLoan`, so the same premise at the frame's entry would be a
different and false claim.

Frame, error kind and liveness: see this section's banner. -/
theorem rollback_of_allowance_below_amount {msg : Msg} {benv : Benv} {xl : Xlot}
    {out : Devm} {receiver token amount : B256} {data : Bytes}
    (h_pm : ProcessMessage msg xl (.ok out))
    (h_fill : Xlot.Filled xl)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles && decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_code : some (initSevm (msg.withBenv benv)).code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector (initSevm (msg.withBenv benv)) = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail (initSevm (msg.withBenv benv))
      flashLoanSelector [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf (initDevm (msg.withBenv benv)).memory)
    (h_fresh : Mem.Reads (initDevm (msg.withBenv benv)).memory [])
    (h_low : ∀ (a : Adr) (sc mid : Devm),
      CallbackBoundary (initSevm (msg.withBenv benv))
        (initSevm (msg.withBenv benv)).currentTarget a amount data sc mid →
      (Devm.getStor mid (initSevm (msg.withBenv benv)).currentTarget).get
        (repayKey a (initSevm (msg.withBenv benv)).currentTarget) < amount) :
    out.error.isSome ∧
      out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage :=
  Blanc.rollback_of_no_success h_pm h_fill h_bt h_prec
    (fun _ exc => no_success_of_allowance_below_amount h_code h_sel h_dec h_size
      h_wf h_fresh h_low exc)

/-- **A receiver balance below `amount` ⇒ the frame settled with an error,
rolled back.**  The restoration form of `no_success_of_balance_below_amount`, at
`msg`'s own frame.

Inherits the full premise set of its corollary, read at the entry machine:
**canonical encoding** (`FMINT_DEVIATIONS.md` row 21), the **size bound**, and
**frame freshness** on the entry memory.  `h_low` is **boundary-quantified**,
and is read at `mid` for the same reason as the allowance: the borrower holds
the principal during the callback and the check happens after it.

Frame, error kind and liveness: see this section's banner. -/
theorem rollback_of_balance_below_amount {msg : Msg} {benv : Benv} {xl : Xlot}
    {out : Devm} {receiver token amount : B256} {data : Bytes}
    (h_pm : ProcessMessage msg xl (.ok out))
    (h_fill : Xlot.Filled xl)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles && decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_code : some (initSevm (msg.withBenv benv)).code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector (initSevm (msg.withBenv benv)) = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail (initSevm (msg.withBenv benv))
      flashLoanSelector [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf (initDevm (msg.withBenv benv)).memory)
    (h_fresh : Mem.Reads (initDevm (msg.withBenv benv)).memory [])
    (h_low : ∀ (a : Adr) (sc mid : Devm),
      CallbackBoundary (initSevm (msg.withBenv benv))
        (initSevm (msg.withBenv benv)).currentTarget a amount data sc mid →
      (Devm.getStor mid (initSevm (msg.withBenv benv)).currentTarget).get a.toB256
        < amount) :
    out.error.isSome ∧
      out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage :=
  Blanc.rollback_of_no_success h_pm h_fill h_bt h_prec
    (fun _ exc => no_success_of_balance_below_amount h_code h_sel h_dec h_size
      h_wf h_fresh h_low exc)

end Fmint

end Blanc
