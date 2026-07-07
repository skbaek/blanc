import Blanc.Solvent

/-!
# NoDel : the "no self-destruction" invariant (scaffold)

GOAL: prove that WETH's account (`wa`, code-bearing) never enters
`accountsToDelete` during EVM execution, so `processMessageCall`'s output
satisfies `wa ∉ out.accountsToDelete` — the missing second conjunct of
`processMessageCall_inv_solvent` in Solvent.lean.

MATH (all confirmed against elevm/Elevm/Execution.lean):
- SELFDESTRUCT (`Linst .dest`, Execution.lean:1914-1939) inserts
  `donor = sevm.currentTarget` into `accountsToDelete` ONLY under the
  EIP-6780 guard `donor ∈ devm5.createdAccounts`.  So `wa ∉ createdAccounts`
  implies `donor ≠ wa`, preserving `wa ∉ accountsToDelete`.
- An address enters `createdAccounts` only via `addCreatedAccount`
  (Execution.lean:1184), reached only through `processCreateMessage.msg`
  (2617-2622) with `adr = msg.currentTarget`, and both create entry points
  guard against code-bearing targets: `genericCreate`'s emptiness check
  (2839-2843) and `processMessageCall.create`'s collision check (3676-3679).
  Since `wa` is code-bearing, `wa` never enters `createdAccounts` —
  PROVIDED wa's code stays nonempty, which is exactly the already-proved
  getCode ladder (`Exec.inv_getCode`, Common.lean:5757: code-bearing
  addresses keep their code, and its per-level `inv_getCode_gen` cousins).
- Call/create returns merge via `incorporateChildOnSuccess` (1963:
  atd := parent ∪ child, ca := child) / `incorporateChildOnError` (1953:
  ca := child, atd := parent's) — preserved when both sides are NoDel.
- `Devm.rollback` (2029) keeps atd/ca, resets state/tra.
- ERROR PAYLOADS MATTER: `executeCode.handleError` (2692) converts
  exceptional-halt/Revert errors into `.ok` results carrying the failed
  devm's atd/ca.  Hence every lemma below is stated over BOTH ok and error
  results (like the getCode ladder, UNLIKE the ok-only nof ladder).

ARCHITECTURE: mirror the `Xlot.InvNof` ladder (Solvent.lean:2562-3238)
lemma-for-lemma, with the result-shape of the `Xlot.InvGetCode` ladder
(Common.lean:4076-5785).  The code-nonempty conjunct inside `NoDel` is
never re-proved: each level cites the SAME-level `inv_getCode` lemma
(passed down via a separate `Xlot.InvGetCode` hypothesis).

FILL PROTOCOL (for future sessions, any model tier):
- Work ONLY in this file; never touch Solvent.lean/Common.lean/Semantics.lean.
- Verify each fill with:
    cd /Users/bsk/blanc && lake env lean --tstack=65536 Blanc/temp.lean > /tmp/t.log 2>&1; echo EXIT=$?
  EXIT=0 (sorry warnings ok) = good; EXIT=1 = ordinary errors, iterate;
  EXIT=134 = C++ stack blowup — STOP, shrink terms (see memory note
  scratch-file-cli-for-exec-proofs).  lean-lsp MCP `lean_goal` works here too.
- Each `sorry` has a `[FILL-nn]` tag, a difficulty tier, a one-line spec,
  and a CRIB pointing at the template proof to imitate.  Tiers:
  [MECH]       small mechanical fill, any model
  [MECH-LARGE] long but mechanical per-opcode/per-case bash, any model
  [ESCALATE]   inversion is genuinely tricky; use a strong model
- Fill order: FILL-01..05 (plumbing) → 06..08 (Rinst/Jinst) → 09 (Linst,
  the SELFDESTRUCT case) → 10..15 (relational ladder) → 16 (Exec) →
  17..21 (raw lift).  Later fills assume earlier statements only.
-/

/-! ## §1 AdrSet non-membership helpers (PROVED) -/

namespace AdrSet

theorem not_mem_insert {a b : Adr} {s : AdrSet} (hne : a ≠ b) (hs : a ∉ s) :
    a ∉ s.insert b := by
  simp only [Std.HashSet.mem_insert, not_or]
  exact ⟨by simpa using Ne.symm hne, hs⟩

theorem not_mem_foldl_insert {a : Adr} {l : List Adr} {m : AdrSet}
    (hm : a ∉ m) (hl : a ∉ l) :
    a ∉ l.foldl (fun acc x => acc.insert x) m := by
  induction l generalizing m with
  | nil => simpa using hm
  | cons x xs ih =>
    simp only [List.foldl_cons]
    refine ih (not_mem_insert ?_ hm) (fun h => hl (List.mem_cons_of_mem _ h))
    exact fun h => hl (h ▸ List.mem_cons_self ..)

theorem not_mem_union {a : Adr} {m₁ m₂ : AdrSet} (h₁ : a ∉ m₁) (h₂ : a ∉ m₂) :
    a ∉ m₁.union m₂ := by
  unfold Std.HashSet.union
  rw [Std.HashSet.fold_eq_foldl_toList]
  exact not_mem_foldl_insert h₁ (fun h => h₂ (Std.HashSet.mem_toList.mp h))

theorem not_mem_empty {a : Adr} {c : Nat} :
    a ∉ (Std.HashSet.emptyWithCapacity c : AdrSet) := by
  simp

end AdrSet

/-! ## §2 The NoDel invariant -/

-- Paired projection of the two deletion-relevant sets; `Rinst.Inv Devm.delSets r`
-- is the per-opcode preservation statement (mirrors `Rinst.Inv Devm.getBal`).
def Devm.delSets (d : Devm) : AdrSet × AdrSet :=
  (d.accountsToDelete, d.createdAccounts)

-- rfl-bridge between the Devm-level and State-level code projections.
lemma Devm.getCode_state (d : Devm) (a : Adr) :
    d.getCode a = d.state.getCode a := rfl

-- The frame-level invariant.  The `code` conjunct is the fuel for the
-- CREATE collision guards; it is transported by the PROVED getCode ladder,
-- never re-proved here.
structure Devm.NoDel (wa : Adr) (d : Devm) : Prop where
  (atd  : wa ∉ d.accountsToDelete)
  (ca   : wa ∉ d.createdAccounts)
  (code : (d.getCode wa).toList ≠ [])

-- The message-level invariant (a fresh frame starts with atd = ∅,
-- ca = msg.benv.createdAccounts, state = msg.benv.state; see initDevm,
-- elevm Execution.lean:2657).
structure Msg.NoDel (wa : Adr) (msg : Msg) : Prop where
  (ca   : wa ∉ msg.benv.createdAccounts)
  (code : (msg.benv.state.getCode wa).toList ≠ [])

-- Result-level invariants: error payloads carry live atd/ca (handleError
-- can resurrect them into ok results), so they must be covered.
def Execution.NoDel (wa : Adr) : Execution → Prop
  | .ok d => Devm.NoDel wa d
  | .error ⟨_, d⟩ => Devm.NoDel wa d

-- Msg-level results (`processMessage`-shaped): the error payload carries
-- only createdAccounts + state (no atd; consumers merge it via
-- liftToExecution, keeping the parent's atd).
def MsgResult.NoDel (wa : Adr) :
    Except (String × State × AdrSet × Tra) Devm → Prop
  | .ok d => Devm.NoDel wa d
  | .error ⟨_, st, ca, _⟩ => wa ∉ ca ∧ (st.getCode wa).toList ≠ []

-- The sub-execution oracle invariant threaded through the Exec induction
-- (mirrors Xlot.InvNof, Solvent.lean:2562, but result-shaped like
-- Xlot.InvGetCode, Common.lean:4076).
def Xlot.InvNoDel (wa : Adr) : Xlot → Prop
  | .none => True
  | .some ⟨_, devm_, exn_⟩ => Devm.NoDel wa devm_ → Execution.NoDel wa exn_

/-! ## §3 Proved transports -/

-- Transport NoDel across a step that moves neither set nor wa's code.
lemma Devm.NoDel.of_eqs {wa : Adr} {d d' : Devm}
    (hs : d.delSets = d'.delSets) (hc : d.getCode wa = d'.getCode wa)
    (h : Devm.NoDel wa d) : Devm.NoDel wa d' := by
  have h1 : d.accountsToDelete = d'.accountsToDelete := congrArg Prod.fst hs
  have h2 : d.createdAccounts = d'.createdAccounts := congrArg Prod.snd hs
  exact ⟨h1 ▸ h.atd, h2 ▸ h.ca, hc ▸ h.code⟩

-- A fresh frame satisfies NoDel (initDevm: atd := ∅, ca := benv.ca).
lemma Msg.NoDel.initDevm {wa : Adr} {msg : Msg}
    (h : Msg.NoDel wa msg) : Devm.NoDel wa (initDevm msg) :=
  ⟨AdrSet.not_mem_empty, h.ca, h.code⟩

-- Rollback keeps atd/ca and installs the given state.
lemma Devm.NoDel.rollback {wa : Adr} {d : Devm} {st : State} {tra : Tra}
    (h_atd : wa ∉ d.accountsToDelete) (h_ca : wa ∉ d.createdAccounts)
    (h_code : (st.getCode wa).toList ≠ []) :
    Devm.NoDel wa (d.rollback st tra) :=
  ⟨h_atd, h_ca, h_code⟩

-- handleError shuffles error payloads into ok results without touching
-- the sets (elevm Execution.lean:2692-2701).
lemma handleError_noDel {wa : Adr} {exn : Execution}
    (h : Execution.NoDel wa exn) :
    MsgResult.NoDel wa (executeCode.handleError exn) := by
  cases exn with
  | ok d => exact h
  | error p =>
    rcases p with ⟨err, d⟩
    have hd : Devm.NoDel wa d := h
    dsimp only [executeCode.handleError]
    split
    · exact ⟨hd.atd, hd.ca, hd.code⟩
    · split
      · exact ⟨hd.atd, hd.ca, hd.code⟩
      · exact ⟨hd.ca, hd.code⟩

-- Bridge from the blockchain-level invariant: WETH's compiled code is
-- nonempty, so `State.Inv` implies the Msg-level NoDel at any msg whose
-- benv carries the invariant state and a wa-free createdAccounts.
lemma Msg.NoDel.of_state_inv {wa : Adr} {msg : Msg}
    (h_ca : wa ∉ msg.benv.createdAccounts)
    (h_inv : State.Inv wa msg.benv.state) : Msg.NoDel wa msg := by
  refine ⟨h_ca, fun hc => ?_⟩
  have h := h_inv.code
  rw [hc] at h
  exact Prog.compile_ne_nil h.symm

/-! ## §4 Plumbing (sorried) -/

-- [FILL-01] [MECH] The create-guard bridge: an address whose account has
-- size-0 code cannot be the code-bearing wa.
-- HINT: intro h; subst h; the goal reduces `(st.get wa).code` vs
-- `st.getCode wa` (rfl); need `size = 0 → toList = []` for ByteArray —
-- search with lean_loogle for `ByteArray.size` + `toList` (e.g. a
-- `ByteArray.toList.length = size` lemma, then `List.length_eq_zero`).
lemma ne_wa_of_code_size_zero {st : State} {wa b : Adr}
    (hwa : (st.getCode wa).toList ≠ []) (hb : (st.get b).code.size = 0) :
    b ≠ wa := by
  intro h
  subst h
  have h_empty : (st.get b).code.toList = [] := by
    unfold ByteArray.toList
    unfold ByteArray.toList.loop
    simp [hb]
  unfold State.getCode at hwa
  rw [h_empty] at hwa
  exact hwa rfl

-- [FILL-02] [MECH] Same bridge via the collision predicate used by
-- `processMessageCall.create` (elevm Execution.lean:3475-3477): read
-- `accountHasCodeOrNonce`'s definition and extract "code empty at ct".
lemma ne_wa_of_not_hasCodeOrNonce {st : State} {wa ct : Adr}
    (hwa : (st.getCode wa).toList ≠ [])
    (h : accountHasCodeOrNonce st ct = false) : ct ≠ wa := by
  intro heq
  subst heq
  unfold accountHasCodeOrNonce at h
  rw [Bool.or_eq_false_iff] at h
  have h_empty_not := h.2
  have h_empty : (st.getCode ct).isEmpty = true := by
    simp at h_empty_not
    exact h_empty_not
  have hb : (st.getCode ct).size = 0 := by
    unfold ByteArray.isEmpty at h_empty
    simp at h_empty
    exact h_empty
  have h_empty_list : (st.getCode ct).toList = [] := by
    unfold ByteArray.toList
    unfold ByteArray.toList.loop
    simp [hb]
  rw [h_empty_list] at hwa
  exact hwa rfl

-- [FILL-03] [MECH] The pre-execution value transfer keeps ca and wa's code
-- (it only moves balances).  CRIB: `sum_bal_of_benvAfterTransfer`
-- (Solvent.lean:2600) for the inversion shape (`of_benvAfterTransfer`
-- gives `benv' = (msg.benv.withState (st_mid.addBal ..))`-form, so
-- `benv'.createdAccounts = msg.benv.createdAccounts` definitionally);
-- code via State-level subBal/addBal get-preservation lemmas (crib the
-- dest case of `Linst.inv_getCode`, Common.lean:5653).
lemma Msg.NoDel.benvAfterTransfer {wa : Adr} {msg : Msg} {benv : Benv}
    (h_run : msg.benvAfterTransfer = .ok benv)
    (h : Msg.NoDel wa msg) : Msg.NoDel wa (msg.withBenv benv) := by
  by_cases h_stv : msg.shouldTransferValue = true
  · rcases of_benvAfterTransfer h_stv h_run with ⟨st_mid, h_sub, hB⟩
    have hBc : benv.createdAccounts = msg.benv.createdAccounts := by
      rw [hB]; rfl
    have h_code_add : benv.state.getCode wa = st_mid.getCode wa := by
      have hBs : benv.state = st_mid.addBal msg.currentTarget msg.value := by
        rw [hB]; rfl
      rw [hBs]; exact State.addBal_getCode st_mid msg.currentTarget wa msg.value
    have h_code_sub : st_mid.getCode wa = msg.benv.state.getCode wa := by
      exact State.subBal_getCode h_sub
    have h_code : ((msg.withBenv benv).benv.state.getCode wa).toList ≠ [] := by
      change (benv.state.getCode wa).toList ≠ []
      rw [h_code_add, h_code_sub]
      exact h.code
    exact ⟨hBc ▸ h.ca, h_code⟩
  · unfold Msg.benvAfterTransfer at h_run
    rw [if_neg h_stv] at h_run
    have heq : benv = msg.benv := (Except.ok.inj h_run).symm
    subst heq
    exact h

-- [FILL-04] [MECH] The create-seeding step (elevm Execution.lean:2617-2622):
-- setStor ct ∅ (code untouched), addCreatedAccount ct (use
-- `AdrSet.not_mem_insert (Ne.symm h_ct)`), incrNonce ct (code untouched).
-- CRIB: the `h_inv_cm` step of `processCreateMessage_inv_solvent`
-- (Solvent.lean:5183-5186) for how `(processCreateMessage.msg msg).benv`
-- unfolds; code preservation via `State.get_set_ne`-style lemmas
-- (cf. `State.Inv.setStor_ne`, Solvent.lean:5140).
lemma Msg.NoDel.processCreateMessage_msg {wa : Adr} {msg : Msg}
    (h_ct : msg.currentTarget ≠ wa)
    (h : Msg.NoDel wa msg) : Msg.NoDel wa (processCreateMessage.msg msg) := by
  rcases h with ⟨hca, hcode⟩
  refine ⟨?_, ?_⟩
  · show wa ∉ msg.benv.createdAccounts.insert msg.currentTarget
    exact AdrSet.not_mem_insert (Ne.symm h_ct) hca
  · show (((msg.benv.state.setStor msg.currentTarget .empty).incrNonce msg.currentTarget).getCode wa).toList ≠ []
    have h_get : ((msg.benv.state.setStor msg.currentTarget .empty).incrNonce msg.currentTarget).get wa = msg.benv.state.get wa := by
      dsimp only [State.incrNonce, State.setStor]
      rw [State.get_set_ne h_ct, State.get_set_ne h_ct]
    show (((msg.benv.state.setStor msg.currentTarget .empty).incrNonce msg.currentTarget).get wa).code.toList ≠ []
    rw [h_get]
    exact hcode

-- [FILL-05] [MECH] Precompiles never touch the sets or code.
-- CRIB: `executePrecomp_inv_getCode` + `applyPrecompResult_getCode`
-- (Common.lean:4084-4093) — same two-step structure; conclude with
-- `Devm.NoDel.of_eqs`.
lemma executePrecomp_noDel {wa : Adr} {evm : Evm} {adr : Adr} {exn : Execution}
    (h_ex : executePrecomp evm adr = exn)
    (h : Devm.NoDel wa evm.dyna) : Execution.NoDel wa exn := by
  unfold executePrecomp at h_ex
  revert h_ex
  generalize h_res : precompileRun evm adr = res
  intro h_ex
  subst h_ex
  cases res
  · apply Devm.NoDel.of_eqs (d := evm.dyna)
    · rfl
    · rfl
    · exact h
  · apply Devm.NoDel.of_eqs (d := evm.dyna)
    · rfl
    · rfl
    · exact h

/-! ## §5 Instruction level (sorried) -/

-- [FILL-06] [MECH-LARGE] No register instruction touches either set
-- (ok results).  Per-opcode bash; each case is 1-6 lines given the
-- combinator helpers.  CRIB: `Rinst.inv_bal` (Common.lean:7122-7290ish)
-- — copy its case skeleton verbatim, replacing each `*_getBal_eq`
-- combinator citation with a `*_delSets_eq` analogue you prove alongside
-- (applyUnary/applyBinary/applyTernary, Devm.pop/popToNat/popToAdr,
-- Devm.push/pushItem, chargeGas, memRead/memWrite, sload/sstore/tload/
-- tstore/keccak/copy-family ops).  For chargeGas use `Devm.burn_of_chargeGas`:
-- `Devm.Burn` already contains accountsToDelete/createdAccounts equalities
-- as fields.  NOTE: a bare `cases r <;> simp_all` does NOT work (verified);
-- the combinator route is required.
lemma Rinst.inv_delSets {r : Rinst} : Rinst.Inv Devm.delSets r := by
  sorry

-- [FILL-07] [MECH-LARGE] Same for error results (error payloads are the
-- intermediate devms).  CRIB: `Rinst.inv_getCode_err` (Common.lean:4644)
-- — same skeleton, delSets instead of getCode.
lemma Rinst.inv_delSets_err {pc : Nat} {sevm : Sevm} {devm : Devm} {r : Rinst}
    {err : String} {devm' : Devm}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = .error ⟨err, devm'⟩) :
    devm'.delSets = devm.delSets := by
  sorry

-- [FILL-08] [MECH] Jumps touch only stack/gas/pc.  CRIB: `Jinst.inv_state`
-- (Solvent.lean:2452) — same case bash, reading off the sets instead of
-- state; and `Jinst.inv_getCode_gen` (Common.lean:5586) for the error case.
lemma Jinst.inv_delSets {pc : Nat} {sevm : Sevm} {devm : Devm} {j : Jinst}
    {pc' : Nat} {devm' : Devm}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j (.ok ⟨pc', devm'⟩)) :
    devm'.delSets = devm.delSets := by
  sorry

lemma Jinst.inv_delSets_err {pc : Nat} {sevm : Sevm} {devm : Devm} {j : Jinst}
    {err : String} {devm' : Devm}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j (.error ⟨err, devm'⟩)) :
    devm'.delSets = devm.delSets := by
  sorry

-- [FILL-09] [ESCALATE first time; the dest case is the mathematical heart]
-- Halting instructions preserve NoDel.  stop/ret/rev are plumbing
-- (CRIB: `Linst.inv_nof`, Solvent.lean:2374, for the inversion shape;
-- rev also lands in the error payload — cover it).  dest (SELFDESTRUCT,
-- elevm Execution.lean:1914-1939): invert exactly as in `Linst.inv_postcond`
-- (Solvent.lean:4562, dest case) down to the final
-- `if donor ∈ devm5.createdAccounts` split:
--   • then-branch: result `addAccountToDelete (devm5.setBal donor 0) donor`;
--     from the guard `donor ∈ devm5.createdAccounts` and NoDel.ca at devm5
--     conclude `donor ≠ wa`, then `AdrSet.not_mem_insert` closes atd;
--     ca untouched; code survives setBal (balance-only).
--   • else-branch: `.ok devm5` — direct.
-- The pop/chargeGas/assertDynamic/subBal/addBal plumbing between devm and
-- devm5 preserves delSets (record updates / balance-only state edits) and
-- wa's code — crib the corresponding steps of `Linst.inv_postcond` and of
-- `Linst.inv_getCode` (Common.lean:5653, dest case).  Error payloads along
-- the way are the intermediate devms; cover them like the ok paths.
lemma Linst.inv_noDel {wa : Adr} {sevm : Sevm} {devm : Devm} {l : Linst}
    {exn : Execution}
    (run : Linst.Run sevm devm l exn)
    (h : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  sorry

/-! ## §6 Relational call/create ladder (sorried)

Every lemma takes BOTH oracles for the sub-execution slot:
  `inv  : Xlot.InvNoDel wa xl`  — the new set-invariant (this ladder), and
  `invc : Xlot.InvGetCode xl`   — the PROVED code ladder's oracle, used to
                                  discharge each `.code` conjunct by citing
                                  the same-level `inv_getCode_gen` lemma.
At `Exec.inv_noDel` the two oracles are built from the sub-derivation:
  inv  from the induction hypothesis,
  invc as `⟨exec_x, fun a ha => (Exec.inv_getCode exec_x a ha).symm⟩`
  (exactly as in Exec.inv_getCode's own recursion, Common.lean:5767). -/

-- [FILL-10] [MECH] CRIB shape: `ExecuteCode.inv_getCode_gen`
-- (Common.lean:4100) for the three-way branch structure (precomp /
-- recorded sub-exec), `ProcessMessage.inv_nof`'s use of
-- `of_executeCode_cases` (Solvent.lean:2614/2663) for a cleaner split.
-- Ingredients: Msg.NoDel.initDevm, executePrecomp_noDel, handleError_noDel,
-- and the two oracles for the recorded slot.
lemma ExecuteCode.inv_noDel {wa : Adr} {msg : Msg} {xl : Xlot}
    {ex : Except (String × State × AdrSet × Tra) Devm}
    (inv : Xlot.InvNoDel wa xl) (invc : xl.InvGetCode)
    (run : ExecuteCode msg xl ex)
    (h : Msg.NoDel wa msg) : MsgResult.NoDel wa ex := by
  sorry

-- [FILL-11] [MECH] CRIB: `ProcessMessage.inv_nof` (Solvent.lean:2640) for
-- the SplitXl/Split inversion skeleton — but keep the error branches
-- (benvAfterTransfer error payload is ⟨_, msg.benv.state, msg.benv.ca, _⟩,
-- i.e. Msg.NoDel directly; executeCode error handled by FILL-10's result).
-- Rollback branch: `Devm.NoDel.rollback` with code from `h.code`.
lemma ProcessMessage.inv_noDel {wa : Adr} {msg : Msg} {xl : Xlot}
    {ex : Except (String × State × AdrSet × Tra) Devm}
    (inv : Xlot.InvNoDel wa xl) (invc : xl.InvGetCode)
    (run : ProcessMessage msg xl ex)
    (h : Msg.NoDel wa msg) : MsgResult.NoDel wa ex := by
  sorry

-- [FILL-12] [MECH] CRIB: `ProcessCreateMessage.inv_nof` (Solvent.lean:2729)
-- + the raw `processCreateMessage_inv_solvent` (Solvent.lean:5171) for the
-- chargeCodeGas/exceptionalHalt/setCode case analysis.  Seeding via
-- FILL-04; `setCode msg.currentTarget` keeps the sets (state-only) and
-- keeps wa's code because `h_ct : msg.currentTarget ≠ wa`;
-- `chargeCodeGas` via `Devm.burn_of_chargeGas`/`chargeCodeGas_state`
-- (Solvent.lean:2629); exceptionalHalt = rollback + record updates.
lemma ProcessCreateMessage.inv_noDel {wa : Adr} {msg : Msg} {xl : Xlot}
    {ex : Except (String × State × AdrSet × Tra) Devm}
    (inv : Xlot.InvNoDel wa xl) (invc : xl.InvGetCode)
    (run : ProcessCreateMessage msg xl ex)
    (h_ct : msg.currentTarget ≠ wa)
    (h : Msg.NoDel wa msg) : MsgResult.NoDel wa ex := by
  sorry

-- [FILL-13] [MECH] CRIB: `GenericCall.inv_nof` (Solvent.lean:2687) for the
-- rcases skeleton.  childMsg = callMsg …, whose benv is
-- ⟨evm1.state, evm1.createdAccounts, _⟩ (elevm Execution.lean:2729) — so
-- childMsg.NoDel follows from the parent's.  Merge:
-- incorporateChildOnError keeps parent atd + child ca/state;
-- incorporateChildOnSuccess needs `AdrSet.not_mem_union` for atd.
-- push/memWrite epilogues preserve delSets/code (record updates).
lemma GenericCall.inv_noDel {wa : Adr} {sevm : Sevm} {devm : Devm}
    {gas : Nat} {value : B256} {caller target codeAddress : Adr}
    {stv istat : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    {xl : Xlot} {exn : Execution}
    (inv : Xlot.InvNoDel wa xl) (invc : xl.InvGetCode)
    (h : GenericCall sevm devm gas value caller target codeAddress
      stv istat ii is oi os code dp xl exn)
    (hnd : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  sorry

-- [FILL-14] [ESCALATE first time; contains the CREATE collision argument]
-- CRIB: `GenericCreate.inv_nof` (Solvent.lean:2765) for the rcases
-- skeleton.  THE KEY STEP: in the branch where the emptiness guard
-- `¬(nonce ≠ 0 ∨ code.size ≠ 0 ∨ stor.size ≠ 0)` (at devm4.state.get
-- newAddress) passed, push_neg gives `(devm4.state.get newAddress).code.size
-- = 0`; NoDel.code transported to devm4 gives
-- `(devm4.getCode wa).toList ≠ []`; `ne_wa_of_code_size_zero` (FILL-01)
-- yields `newAddress ≠ wa` = the `h_ct` needed by FILL-12 for the child.
-- childMsg.benv = ⟨devm4.state, devm4.createdAccounts, _⟩ (in-file literal).
-- Merges as in FILL-13.
lemma GenericCreate.inv_noDel {wa : Adr} {sevm : Sevm} {devm : Devm}
    {endowment : B256} {newAddress : Adr} {mi ms : Nat}
    {xl : Xlot} {exn : Execution}
    (inv : Xlot.InvNoDel wa xl) (invc : xl.InvGetCode)
    (h : GenericCreate sevm devm endowment newAddress mi ms xl exn)
    (hnd : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  sorry

-- [FILL-15] [MECH-LARGE] Six-way dispatch (create/create2/call/callcode/
-- delegatecall/staticcall) onto FILL-13/14 after popping arguments.
-- CRIB: `Xinst.inv_nof_gen` (Solvent.lean:2826-3036) — copy the rcases
-- chains per case; each SplitXl error branch's payload is an intermediate
-- devm (cover with the plumbing equalities); each ok chain ends in a
-- GenericCall/GenericCreate application.
lemma Xinst.inv_noDel_gen {wa : Adr} {sevm : Sevm} {s : Devm} {x : Xinst}
    {xl : Xlot} {exn : Execution}
    (inv : Xlot.InvNoDel wa xl) (invc : xl.InvGetCode)
    (h : Xinst.Run sevm s x xl exn)
    (hnd : Devm.NoDel wa s) : Execution.NoDel wa exn := by
  sorry

-- [FILL-16] [MECH] Three-way dispatch on the Ninst shape.  CRIB:
-- `Ninst.inv_nof_gen` (Solvent.lean:3038): push = chargeGas + push
-- plumbing (both ok and error payloads); reg = FILL-06/07 via
-- `Devm.NoDel.of_eqs` + `Rinst.inv_getCode`/`Rinst.inv_getCode_err`
-- (Common.lean:3781/4644) for the code conjunct; exec = FILL-15.
-- Non-exec cases with xl = .some are `False` by definition of Ninst.Run'.
lemma Ninst.inv_noDel_gen {wa : Adr} {pc : Nat} {sevm : Sevm} {devm : Devm}
    {n : Ninst} {xl : Xlot} {exn : Execution}
    (inv : Xlot.InvNoDel wa xl) (invc : xl.InvGetCode)
    (run : Ninst.Run' pc sevm devm n xl exn)
    (h : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  sorry

-- [FILL-17] [ESCALATE-MAYBE: recursor mechanics over the Type-valued Exec]
-- The main induction.  CRIB: mirror `Exec.inv_getCode` (Common.lean:5757)
-- case-for-case (`revert exn devm sevm pc; apply Exec.rec` + 8 intro
-- blocks); nof twin `Exec.inv_nof` (Solvent.lean:3065) shows the same
-- pattern with an invariant-implication motive.  In the two `Some` cases
-- supply inv := the sub-ih and invc := ⟨exec_x, fun a ha =>
-- (Exec.inv_getCode exec_x a ha).symm⟩.  invOp's error payload is devm
-- itself; jump cases via FILL-08; last via FILL-09.
lemma Exec.inv_noDel {wa : Adr} {pc : Nat} {sevm : Sevm} {devm : Devm}
    {exn : Execution}
    (run : Exec pc sevm devm exn)
    (h : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  sorry

/-! ## §7 Raw executable lift (top three sorried; first one PROVED) -/

-- Raw exec preserves NoDel (both result shapes), recursion limit
-- quantified away.  PROVED given FILL-17 — mirrors `exec_inv_solvent`
-- (Solvent.lean:4704).
theorem exec_inv_noDel {wa : Adr} (lim : Nat) (sevm : Sevm) (pre : Devm)
    (exn : Execution)
    (h_run : exec ⟨0, sevm, pre⟩ lim = exn) (h_fit : exn.Fit)
    (h : Devm.NoDel wa pre) : Execution.NoDel wa exn := by
  obtain ⟨exc⟩ := (exec_iff_exec_eq 0 sevm pre exn).mpr ⟨h_fit, lim, h_run⟩
  exact Exec.inv_noDel exc h

-- [FILL-18] [MECH] A handleError-ok result cannot hide a recursion-limit
-- error: `.ok` arises only from `.ok` or exceptional-halt/"Revert" errors,
-- and "RecursionLimit" is neither (check `isExceptionalHalt`'s list,
-- elevm Execution.lean:807; `Except.Fit`/`Lim`/`toError?`,
-- Semantics.lean:732-739).  cases exn; dsimp [executeCode.handleError];
-- split; contradictions by `decide`/`simp` on the string tests.
lemma Fit_of_handleError_ok {exn : Execution} {evm : Devm}
    (h : executeCode.handleError exn = .ok evm) : exn.Fit := by
  sorry

-- [FILL-19] [MECH] Raw executeCode.  Invert (lim cases; `rw [executeCode]`;
-- codeAddress match; isPrecomp if) exactly as in
-- `processMessage_inv_solvent`'s inner block (Solvent.lean:5119-5136).
-- exec branches: `Fit_of_handleError_ok` + `exec_inv_noDel` +
-- `handleError_noDel`; precomp branch: `executePrecomp_noDel` +
-- `handleError_noDel`; initial NoDel from `Msg.NoDel.initDevm`.
-- (lim = 0 is impossible: the result is `.error`, not `.ok`.)
theorem executeCode_inv_noDel {wa : Adr} {msg : Msg} {lim : Nat} {evm : Devm}
    (h_run : executeCode msg lim = .ok evm)
    (h : Msg.NoDel wa msg) : Devm.NoDel wa evm := by
  sorry

-- [FILL-20] [MECH] Raw processMessage.  CRIB: `processMessage_inv_solvent`
-- (Solvent.lean:5095) — same lim/bind/if skeleton.  benvAfterTransfer via
-- FILL-03; executeCode via FILL-19; the error.isSome branch returns
-- `evm'.rollback msg.benv.state _` → `Devm.NoDel.rollback` with sets from
-- FILL-19's result and code from `h.code`.
theorem processMessage_inv_noDel {wa : Adr} {msg : Msg} {evm : Devm} {lim : Nat}
    (h_run : processMessage msg lim = .ok evm)
    (h : Msg.NoDel wa msg) : Devm.NoDel wa evm := by
  sorry

-- [FILL-21] [MECH] Raw processCreateMessage.  CRIB:
-- `processCreateMessage_inv_solvent` (Solvent.lean:5171) — same skeleton.
-- Seeding via FILL-04, sub-message via FILL-20, chargeCodeGas via
-- `Devm.burn_of_chargeGas` (Burn carries the set equalities) +
-- `chargeCodeGas_state` (Solvent.lean:2629), setCode at `h_ct`,
-- exceptionalHalt/rollback via `Devm.NoDel.rollback`.
theorem processCreateMessage_inv_noDel {wa : Adr} {msg : Msg} {evm : Devm}
    {lim : Nat}
    (h_run : processCreateMessage msg lim = .ok evm)
    (h_ct : msg.currentTarget ≠ wa)
    (h : Msg.NoDel wa msg) : Devm.NoDel wa evm := by
  sorry

-- [FILL-22] [ESCALATE: `for`-loop-with-`continue` inversion in the Except
-- monad] EIP-7702 delegation processing keeps Msg.NoDel: an authority only
-- receives setCode/incrNonce if its current code passes the emptiness test
-- (elevm Execution.lean:3648: nonempty code ⟹ `continue`), so the
-- code-bearing wa is never touched; benv.createdAccounts is never written.
-- The `for`/`mut` desugars to `List.forIn` — invert with a generalized
-- loop-invariant lemma over `forIn` (state the invariant as: msg.benv
-- differs from the input only by setCode/incrNonce at non-wa addresses,
-- hence Msg.NoDel is preserved).  The final `msg.code := …` step doesn't
-- touch benv.  NOTE: a future session will need the same loop lemma for
-- `State.Inv` preservation (processMessageCall_inv_solvent's first
-- conjunct) — factor the loop-invariant helper so both can use it.
theorem setDelegation_msg_noDel {wa : Adr} {msg msg' : Msg} {v : B256}
    (h_run : setDelegation msg = .ok ⟨msg', v⟩)
    (h : Msg.NoDel wa msg) : Msg.NoDel wa msg' := by
  sorry

-- [FILL-23] [MECH] The target theorem.  Dispatch `msg.target.isNone`
-- (raw def elevm Execution.lean:3740):
--  • create (3673): collision-true branch returns atd = ∅
--    (`AdrSet.not_mem_empty`); else `ne_wa_of_not_hasCodeOrNonce` (FILL-02)
--    gives h_ct, invert the `Except.bimap` (error side impossible at .ok),
--    FILL-21 gives evm.NoDel; out.accountsToDelete is
--    `if evm.error.isNone then evm.accountsToDelete else ∅` — both safe.
--  • call (3701): auths-empty test (msgDelegation = msg, refl) or FILL-22;
--    the msgPc match only rewrites code/codeAddress/accessedAddresses/
--    disablePrecompiles (benv untouched ⟹ Msg.NoDel carries over);
--    invert the bimap, FILL-20, same `if` epilogue.
theorem processMessageCall_inv_noDel {wa : Adr} {msg : Msg} {st' : State}
    {out : MsgCallOutput}
    (h_run : processMessageCall msg = .ok ⟨st', out⟩)
    (h : Msg.NoDel wa msg) : wa ∉ out.accountsToDelete := by
  sorry

-- The form consumed by `processMessageCall_inv_solvent`'s second conjunct
-- (PROVED given FILL-23).
theorem processMessageCall_accountsToDelete_ne {wa : Adr} {msg : Msg}
    {st' : State} {out : MsgCallOutput}
    (h_run : processMessageCall msg = .ok ⟨st', out⟩)
    (h : Msg.NoDel wa msg) :
    ∀ a ∈ out.accountsToDelete.toList, a ≠ wa := by
  intro a ha heq
  subst heq
  exact processMessageCall_inv_noDel h_run h (Std.HashSet.mem_toList.mp ha)
