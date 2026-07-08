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
    cd /Users/bsk/blanc && lake env lean --tstack=65536 Blanc/temp.lean > /Users/bsk/blanc/t.log 2>&1; echo EXIT=$?
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
-- delSets combinators (mirror the `*_getBal_eq` family, Common.lean:3407-3486,
-- 7090-7117).  Every building block below touches only stack/gas/memory/logs/
-- refund/accessed/state/transient fields, never accountsToDelete/createdAccounts,
-- so each equality is `rfl` after the definitional unfolds.
lemma delSets_eq_of_bind {α ε} {ma : Except ε α} {f : α → Except ε Devm}
    {devm devm' : Devm}
    (run : (ma >>= f) = .ok devm')
    (getDevm : α → Devm)
    (h_first : ∀ v, ma = .ok v → (getDevm v).delSets = devm.delSets)
    (h_rest : ∀ v, ma = .ok v → f v = .ok devm' → devm'.delSets = (getDevm v).delSets) :
    devm'.delSets = devm.delSets := by
  rcases of_bind_eq_ok run with ⟨v, hm, hf⟩
  rw [h_rest v hm hf, h_first v hm]

lemma Devm.pop_delSets_eq {x devm devm'} (h : Devm.pop devm = .ok ⟨x, devm'⟩) : devm'.delSets = devm.delSets := by
  simp only [Devm.pop] at h
  split at h <;> try contradiction
  cases h; rfl

lemma chargeGas_delSets_eq {cost devm devm'} (h : chargeGas cost devm = .ok devm') : devm'.delSets = devm.delSets := by
  simp only [chargeGas] at h
  split at h <;> try contradiction
  cases h; rfl

lemma Devm.push_delSets_eq {v devm devm'} (h : Devm.push v devm = .ok devm') : devm'.delSets = devm.delSets := by
  simp only [Devm.push, bind, Except.bind, Except.assert] at h
  split at h <;> try contradiction
  cases h; rfl

lemma Devm.popToAdr_delSets_eq {devm devm' adr} (h : Devm.popToAdr devm = .ok ⟨adr, devm'⟩) : devm'.delSets = devm.delSets := by
  dsimp [Devm.popToAdr, Functor.map, Except.map] at h
  rcases hp : devm.pop with _ | ⟨x, devm1⟩
  · simp [hp] at h
  · simp [hp] at h
    rcases h with ⟨_, rfl⟩
    exact Devm.pop_delSets_eq hp

lemma Devm.popToNat_delSets_eq {devm devm' n} (h : Devm.popToNat devm = .ok ⟨n, devm'⟩) : devm'.delSets = devm.delSets := by
  dsimp [Devm.popToNat, Functor.map, Except.map] at h
  rcases hp : devm.pop with _ | ⟨x, devm1⟩
  · simp [hp] at h
  · simp [hp] at h
    rcases h with ⟨_, rfl⟩
    exact Devm.pop_delSets_eq hp

lemma pushItem_delSets_eq {x c devm devm'} (h : pushItem x c devm = .ok devm') : devm'.delSets = devm.delSets := by
  simp only [pushItem] at h
  refine delSets_eq_of_bind h id ?_ ?_
  {intro devm1 hc; exact (chargeGas_delSets_eq hc).trans rfl}
  intro devm1 hc run; exact Devm.push_delSets_eq run

lemma applyBinary_delSets_eq {f : B256 → B256 → B256} {cost devm devm'}
    (h : applyBinary f cost devm = .ok devm') :
    devm.delSets = devm'.delSets := by
  simp only [applyBinary] at h
  apply Eq.symm
  refine delSets_eq_of_bind h Prod.snd ?_ ?_
  {intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp}
  intro ⟨x, devm1⟩ hp run; refine delSets_eq_of_bind run Prod.snd ?_ ?_
  {intro ⟨y, devm2⟩ hp2; exact Devm.pop_delSets_eq hp2}
  intro ⟨y, devm2⟩ hp2 run; exact pushItem_delSets_eq run

lemma applyUnary_delSets_eq {f : B256 → B256} {cost devm devm'}
    (h : applyUnary f cost devm = .ok devm') :
    devm.delSets = devm'.delSets := by
  simp only [applyUnary] at h
  apply Eq.symm
  refine delSets_eq_of_bind h Prod.snd ?_ ?_
  {intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp}
  intro ⟨x, devm1⟩ hp run; exact pushItem_delSets_eq run

lemma applyTernary_delSets_eq {f : B256 → B256 → B256 → B256} {cost devm devm'}
    (h : applyTernary f cost devm = .ok devm') :
    devm.delSets = devm'.delSets := by
  simp only [applyTernary] at h
  apply Eq.symm
  refine delSets_eq_of_bind h Prod.snd ?_ ?_
  {intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp}
  intro ⟨x, devm1⟩ hp run; refine delSets_eq_of_bind run Prod.snd ?_ ?_
  {intro ⟨y, devm2⟩ hp2; exact Devm.pop_delSets_eq hp2}
  intro ⟨y, devm2⟩ hp2 run; refine delSets_eq_of_bind run Prod.snd ?_ ?_
  {intro ⟨z, devm3⟩ hp3; exact Devm.pop_delSets_eq hp3}
  intro ⟨z, devm3⟩ hp3 run; exact pushItem_delSets_eq run

lemma memRead_delSets_eq {x n : Nat} {devm devm' : Devm} {value : B8L} (h : devm.memRead x n = ⟨value, devm'⟩) : devm'.delSets = devm.delSets := by
  simp only [Devm.memRead] at h
  rcases h_read : devm.memory.read x n with ⟨val, mem⟩
  rw [h_read] at h
  injection h with _ h_devm
  rw [← h_devm]
  rfl

lemma memWrite_delSets_eq {idx : Nat} {val : B8L} {devm : Devm} : (devm.memWrite idx val).delSets = devm.delSets := rfl

lemma Devm.popN_delSets_eq {n : Nat} {devm devm' : Devm} {l : List B256}
    (hp : devm.popN n = Except.ok (l, devm')) :
    devm'.delSets = devm.delSets := by
  induction n generalizing devm devm' l with
  | zero =>
    simp [Devm.popN] at hp
    rcases hp with ⟨_, eq⟩
    rw [eq]
  | succ n ih =>
    simp [Devm.popN] at hp
    rcases of_bind_eq_ok hp with ⟨⟨x, devm1⟩, hp1, hp2⟩
    rcases of_bind_eq_ok hp2 with ⟨⟨xs, devm2⟩, hp3, hp4⟩
    injection hp4 with eq
    injection eq with eq1 eq2
    subst eq2
    have h1 := Devm.pop_delSets_eq hp1
    have h2 := ih hp3
    rw [h2, h1]

lemma sstore_inv_delSets
    {pc sevm devm devm'}
    (run : Rinst.run ⟨pc, sevm, devm⟩ .sstore = .ok devm') :
    devm'.delSets = devm.delSets := by
  simp only [Rinst.run, Rinst.runCore] at run
  refine delSets_eq_of_bind run Prod.snd ?_ ?_
  {intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp}
  clear run
  intro ⟨x, devm1⟩ hp run;
  refine delSets_eq_of_bind run Prod.snd ?_ ?_
  {intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp}
  clear run
  intro ⟨y, devm2⟩ hp run;
  rcases of_bind_eq_ok run with ⟨⟨_⟩, _, run'⟩
  clear run
  refine delSets_eq_of_bind run' Prod.fst ?_ ?_
  · clear run';
    intro ⟨devm', _⟩
    simp only [ite_not, Except.ok.injEq]
    split
    · intro eq; injection eq with eq _; rw [eq]
    · simp [addAccessedStorageKey, Devm.withAccessedStorageKeys]
      intro rw _; rw [← rw]; clear rw
      simp [Devm.delSets]
  · clear run';
    intro ⟨devm3, _⟩ eq run; clear eq
    rcases of_bind_eq_ok run with ⟨_, bar, run'⟩;
    clear bar run
    simp only at run'
    refine delSets_eq_of_bind run' id ?_ ?_
    · clear run'
      intro devm4 eq
      injection eq with rw
      rw [← rw]
      simp [Devm.delSets]
    · clear run'
      intro devm4 temp run; clear temp
      refine delSets_eq_of_bind run id ?_ ?_
      {intro devm5 hc; exact (chargeGas_delSets_eq hc).trans rfl}
      clear run
      intro devm5 eq run
      rcases of_bind_eq_ok run with ⟨_, bar, run'⟩;
      clear bar run; injection run' with rw
      rw [← rw]
      rfl

lemma Rinst.inv_delSets {r : Rinst} : Rinst.Inv Devm.delSets r := by
  intros pc sevm pre post; cases r
  case add => exact applyBinary_delSets_eq
  case mul => exact applyBinary_delSets_eq
  case sub => exact applyBinary_delSets_eq
  case div => exact applyBinary_delSets_eq
  case sdiv => exact applyBinary_delSets_eq
  case mod => exact applyBinary_delSets_eq
  case smod => exact applyBinary_delSets_eq
  case signextend => exact applyBinary_delSets_eq
  case lt => exact applyBinary_delSets_eq
  case gt => exact applyBinary_delSets_eq
  case slt => exact applyBinary_delSets_eq
  case sgt => exact applyBinary_delSets_eq
  case eq => exact applyBinary_delSets_eq
  case and => exact applyBinary_delSets_eq
  case or => exact applyBinary_delSets_eq
  case xor => exact applyBinary_delSets_eq
  case byte => intro h; simp only [Rinst.run, Rinst.runCore] at h; exact applyBinary_delSets_eq h
  case shr => intro h; simp only [Rinst.run, Rinst.runCore] at h; exact applyBinary_delSets_eq h
  case shl => intro h; simp only [Rinst.run, Rinst.runCore] at h; exact applyBinary_delSets_eq h
  case sar => intro h; simp only [Rinst.run, Rinst.runCore] at h; exact applyBinary_delSets_eq h
  case addmod => intro h; simp only [Rinst.run, Rinst.runCore] at h; exact applyTernary_delSets_eq h
  case mulmod => intro h; simp only [Rinst.run, Rinst.runCore] at h; exact applyTernary_delSets_eq h
  case iszero => intro h; simp only [Rinst.run, Rinst.runCore] at h; exact applyUnary_delSets_eq h
  case not => intro h; simp only [Rinst.run, Rinst.runCore] at h; exact applyUnary_delSets_eq h
  case blobhash => intro h; change applyUnary (fun x => sevm.tenvStat.blobVersionedHashes.getD x.toNat 0) gHashopcode pre = Except.ok post at h; exact applyUnary_delSets_eq h
  case balance =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h Prod.snd ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp
    · intro ⟨x, devm1⟩ hp run; split at run
      · refine delSets_eq_of_bind run id ?_ ?_
        · intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl
        · intro devm2 hc run2; exact Devm.push_delSets_eq run2
      · refine delSets_eq_of_bind run id ?_ ?_
        · intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl
        · intro devm2 hc run2; exact Devm.push_delSets_eq run2
  case extcodesize =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h Prod.snd ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToAdr_delSets_eq hp
    · intro ⟨x, devm1⟩ hp run; split at run
      · refine delSets_eq_of_bind run id ?_ ?_
        · intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl
        · intro devm2 hc run2; exact Devm.push_delSets_eq run2
      · refine delSets_eq_of_bind run id ?_ ?_
        · intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl
        · intro devm2 hc run2; exact Devm.push_delSets_eq run2
  case mload =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h Prod.snd ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_delSets_eq hp
    · intro ⟨x, devm1⟩ hp run; refine delSets_eq_of_bind run id ?_ ?_
      · intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl
      · intro devm2 hc run2
        rcases h_read : devm2.memRead x 32 with ⟨value, devm3⟩
        rw [h_read] at run2
        change post.delSets = devm2.delSets
        rw [← memRead_delSets_eq h_read]
        exact Devm.push_delSets_eq run2
  case mstore =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h Prod.snd ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_delSets_eq hp
    · intro ⟨x, devm1⟩ hp run; refine delSets_eq_of_bind run Prod.snd ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.pop_delSets_eq hp2
      · intro ⟨y, devm2⟩ hp2 run2; refine delSets_eq_of_bind run2 id ?_ ?_
        · intro devm3 hc; exact (chargeGas_delSets_eq hc).trans rfl
        · intro devm3 hc run3
          injection run3 with h_post
          rw [← h_post]
          exact memWrite_delSets_eq
  case mstore8 =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h Prod.snd ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_delSets_eq hp
    · intro ⟨x, devm1⟩ hp run; refine delSets_eq_of_bind run Prod.snd ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.pop_delSets_eq hp2
      · intro ⟨y, devm2⟩ hp2 run2; refine delSets_eq_of_bind run2 id ?_ ?_
        · intro devm3 hc; exact (chargeGas_delSets_eq hc).trans rfl
        · intro devm3 hc run3
          injection run3 with h_post
          rw [← h_post]
          exact memWrite_delSets_eq
  case address | origin | caller | callvalue | calldatasize | codesize | gasprice | retdatasize | coinbase | timestamp | number | prevrandao | gaslimit | chainid | selfbalance | basefee | blobbasefee | pc | msize =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    exact pushItem_delSets_eq h
  case pop =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h id ?_ ?_
    · intro devm1 hp; rcases of_bind_eq_ok hp with ⟨⟨x, devm2⟩, hp1, hp2⟩; injection hp2 with h_eq; rw [← h_eq]; exact Devm.pop_delSets_eq hp1
    · intro devm1 hp run; exact chargeGas_delSets_eq run
  case tload =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h Prod.snd ?_ ?_
    · intro ⟨key, devm1⟩ hp; exact Devm.pop_delSets_eq hp
    · intro ⟨key, devm1⟩ hp run; exact pushItem_delSets_eq run
  case calldataload =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h Prod.snd ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp
    · intro ⟨x, devm1⟩ hp run; refine delSets_eq_of_bind run id ?_ ?_
      · intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl
      · intro devm2 hc run2; exact Devm.push_delSets_eq run2
  case gas =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h id ?_ ?_
    · intro devm1 hc; exact (chargeGas_delSets_eq hc).trans rfl
    · intro devm1 hc run; exact Devm.push_delSets_eq run
  case dup =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h id ?_ ?_
    · intro devm1 hc; exact (chargeGas_delSets_eq hc).trans rfl
    · intro devm1 hc run; split at run
      · contradiction
      · exact Devm.push_delSets_eq run
  case swap =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h id ?_ ?_
    · intro devm1 hc; exact (chargeGas_delSets_eq hc).trans rfl
    · intro devm1 hc run; split at run
      · contradiction
      · injection run with h_eq; rw [← h_eq]; rfl
  case exp =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h Prod.snd ?_ ?_
    · intro ⟨base, devm1⟩ hp; exact Devm.pop_delSets_eq hp
    · intro ⟨base, devm1⟩ hp run; refine delSets_eq_of_bind run Prod.snd ?_ ?_
      · intro ⟨exponent, devm2⟩ hp2; exact Devm.pop_delSets_eq hp2
      · intro ⟨exponent, devm2⟩ hp2 run2; refine delSets_eq_of_bind run2 id ?_ ?_
        · intro devm3 hc; exact (chargeGas_delSets_eq hc).trans rfl
        · intro devm3 hc run3; exact Devm.push_delSets_eq run3
  case tstore =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h Prod.snd ?_ ?_
    · intro ⟨key, devm1⟩ hp; exact Devm.pop_delSets_eq hp
    · intro ⟨key, devm1⟩ hp run; refine delSets_eq_of_bind run Prod.snd ?_ ?_
      · intro ⟨new_value, devm2⟩ hp2; exact Devm.pop_delSets_eq hp2
      · intro ⟨new_value, devm2⟩ hp2 run2; refine delSets_eq_of_bind run2 id ?_ ?_
        · intro devm3 hc; exact (chargeGas_delSets_eq hc).trans rfl
        · intro devm3 hc run3
          dsimp [assertDynamic, Except.assert] at run3
          split at run3 <;> try contradiction
          injection run3 with h_post
          rw [← h_post]
          rfl
  case kec =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.popToNat_delSets_eq hp}
    intro ⟨x, devm1⟩ hp run; refine delSets_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_delSets_eq hp2}
    intro ⟨y, devm2⟩ hp2 run;
    refine delSets_eq_of_bind run id ?_ ?_
    {intro devm3 hc; exact (chargeGas_delSets_eq hc).trans rfl}
    intro devm3 hc run; exact (Devm.push_delSets_eq run).trans rfl
  case calldatacopy =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.popToNat_delSets_eq hp}
    intro ⟨x, devm1⟩ hp run; refine delSets_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨y, devm2⟩ hp; exact Devm.popToNat_delSets_eq hp}
    intro ⟨y, devm2⟩ hp run; refine delSets_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨z, devm3⟩ hp; exact Devm.popToNat_delSets_eq hp}
    intro ⟨z, devm3⟩ hp run; refine delSets_eq_of_bind run id ?_ ?_
    {intro devm4 hc; exact (chargeGas_delSets_eq hc).trans rfl}
    intro devm4 hc run; injection run with eq; subst eq; rfl
  case codecopy =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.popToNat_delSets_eq hp}
    intro ⟨x, devm1⟩ hp run; refine delSets_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨y, devm2⟩ hp; exact Devm.popToNat_delSets_eq hp}
    intro ⟨y, devm2⟩ hp run; refine delSets_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨z, devm3⟩ hp; exact Devm.popToNat_delSets_eq hp}
    intro ⟨z, devm3⟩ hp run; refine delSets_eq_of_bind run id ?_ ?_
    {intro devm4 hc; exact (chargeGas_delSets_eq hc).trans rfl}
    intro devm4 hc run; injection run with eq; subst eq; rfl
  case extcodecopy =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.popToAdr_delSets_eq hp}
    intro ⟨x, devm1⟩ hp run; refine delSets_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨y, devm2⟩ hp; exact Devm.popToNat_delSets_eq hp}
    intro ⟨y, devm2⟩ hp run; refine delSets_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨z, devm3⟩ hp; exact Devm.popToNat_delSets_eq hp}
    intro ⟨z, devm3⟩ hp run; refine delSets_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨w, devm4⟩ hp; exact Devm.popToNat_delSets_eq hp}
    intro ⟨w, devm4⟩ hp run; split at run
    · refine delSets_eq_of_bind run id ?_ ?_
      {intro devm5 hc; exact (chargeGas_delSets_eq hc).trans rfl}
      intro devm5 hc run; injection run with eq; subst eq; rfl
    · refine delSets_eq_of_bind run id ?_ ?_
      {intro devm5 hc; exact (chargeGas_delSets_eq hc).trans rfl}
      intro devm5 hc run; injection run with eq; subst eq; rfl
  case retdatacopy =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.popToNat_delSets_eq hp}
    intro ⟨x, devm1⟩ hp run; refine delSets_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨y, devm2⟩ hp; exact Devm.popToNat_delSets_eq hp}
    intro ⟨y, devm2⟩ hp run; refine delSets_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨z, devm3⟩ hp; exact Devm.popToNat_delSets_eq hp}
    intro ⟨z, devm3⟩ hp run; refine delSets_eq_of_bind run id ?_ ?_
    {intro devm4 hc; exact (chargeGas_delSets_eq hc).trans rfl}
    intro devm4 hc run; split at run
    · cases run
    · injection run with eq; subst eq; rfl
  case extcodehash =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.popToAdr_delSets_eq hp}
    intro ⟨x, devm1⟩ hp run; split at run
    · refine delSets_eq_of_bind run id ?_ ?_
      {intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl}
      intro devm2 hc run; exact Devm.push_delSets_eq run
    · refine delSets_eq_of_bind run id ?_ ?_
      {intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl}
      intro devm2 hc run; exact Devm.push_delSets_eq run
  case blockhash =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp}
    intro ⟨x, devm1⟩ hp run; refine delSets_eq_of_bind run id ?_ ?_
    {intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl}
    intro devm2 hc run; exact Devm.push_delSets_eq run
  case sload =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp}
    intro ⟨x, devm1⟩ hp run; split at run
    · refine delSets_eq_of_bind run id ?_ ?_
      {intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl}
      intro devm2 hc run; exact Devm.push_delSets_eq run
    · refine delSets_eq_of_bind run id ?_ ?_
      {intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl}
      intro devm2 hc run; exact Devm.push_delSets_eq run
  case sstore =>
    intro h
    exact (sstore_inv_delSets h).symm
  case mcopy =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.popToNat_delSets_eq hp}
    intro ⟨x, devm1⟩ hp run; refine delSets_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨y, devm2⟩ hp; exact Devm.popToNat_delSets_eq hp}
    intro ⟨y, devm2⟩ hp run; refine delSets_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨z, devm3⟩ hp; exact Devm.popToNat_delSets_eq hp}
    intro ⟨z, devm3⟩ hp run; refine delSets_eq_of_bind run id ?_ ?_
    {intro devm4 hc; exact (chargeGas_delSets_eq hc).trans rfl}
    intro devm4 hc run; injection run with eq; subst eq; rfl
  case log =>
    intro h; simp only [Rinst.run, Rinst.runCore] at h
    apply Eq.symm
    refine delSets_eq_of_bind h Prod.snd ?_ ?_
    {intro ⟨x, devm1⟩ hp; exact Devm.popToNat_delSets_eq hp}
    intro ⟨x, devm1⟩ hp run; refine delSets_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨y, devm2⟩ hp; exact Devm.popToNat_delSets_eq hp}
    intro ⟨y, devm2⟩ hp run; refine delSets_eq_of_bind run Prod.snd ?_ ?_
    {intro ⟨z, devm3⟩ hp; exact Devm.popN_delSets_eq hp}
    intro ⟨z, devm3⟩ hp run; refine delSets_eq_of_bind run id ?_ ?_
    {intro devm4 hc; exact (chargeGas_delSets_eq hc).trans rfl}
    intro devm4 hc run
    rcases of_bind_eq_ok run with ⟨_, _, run'⟩
    injection run' with rw
    rw [← rw]
    rfl

-- delSets error combinators (mirror the `*_getCode_err` family,
-- Common.lean:4530-4642; error payload is `String × Devm`, so `err.2` is the
-- failed devm — every building block leaves its sets untouched).
lemma Devm.pop_delSets_err {err devm} (h : Devm.pop devm = .error err) : err.2.delSets = devm.delSets := by
  simp only [Devm.pop] at h
  split at h <;> try contradiction
  cases h; rfl

lemma chargeGas_delSets_err {cost devm err} (h : chargeGas cost devm = .error err) : err.2.delSets = devm.delSets := by
  simp only [chargeGas] at h
  split at h <;> try contradiction
  cases h; rfl

lemma Devm.push_delSets_err {v devm err} (h : Devm.push v devm = Except.error err) : err.2.delSets = devm.delSets := by
  unfold Devm.push Except.assert at h; dsimp [Bind.bind, Except.bind] at h
  split_ifs at h <;> try contradiction
  injection h with h1; rw [← h1]

lemma assert_delSets_err {cond : Prop} [Decidable cond] {msg : String} {devm : Devm} {err : String × Devm} (h : Except.assert cond (msg, devm) = Except.error err) : err.2.delSets = devm.delSets := by
  unfold Except.assert at h
  split_ifs at h <;> try contradiction
  injection h with h1; rw [← h1]

lemma Devm.popToNat_delSets_err {devm err} (h : Devm.popToNat devm = .error err) : err.2.delSets = devm.delSets := by
  dsimp [Devm.popToNat, Functor.map, Except.map] at h
  rcases hp : devm.pop with err_pop | ⟨x, devm1⟩
  · simp [hp] at h; cases h; exact Devm.pop_delSets_err hp
  · simp [hp] at h

lemma Devm.popToAdr_delSets_err {devm err} (h : Devm.popToAdr devm = .error err) : err.2.delSets = devm.delSets := by
  dsimp [Devm.popToAdr, Functor.map, Except.map] at h
  rcases hp : devm.pop with err_pop | ⟨x, devm1⟩
  · simp [hp] at h; cases h; exact Devm.pop_delSets_err hp
  · simp [hp] at h

lemma delSets_err_of_bind {α} {ma : Except (String × Devm) α} {f : α → Execution}
    {devm : Devm} {err : String × Devm}
    (run : (ma >>= f) = Except.error err)
    (getDevm : α → Devm)
    (h_first_ok : ∀ v, ma = Except.ok v → (getDevm v).delSets = devm.delSets)
    (h_first_err : ∀ e, ma = Except.error e → e.2.delSets = devm.delSets)
    (h_rest_err : ∀ v, ma = Except.ok v → f v = Except.error err → err.2.delSets = (getDevm v).delSets) :
    err.2.delSets = devm.delSets := by
  cases h_ma : ma
  case error e =>
    rw [h_ma, Except.bind_error] at run
    injection run with h_eq; subst h_eq
    exact h_first_err _ h_ma
  case ok v =>
    rw [h_ma, Except.bind_ok] at run
    have h1 := h_rest_err v h_ma run
    have h2 := h_first_ok v h_ma
    exact h1.trans h2

lemma Devm.popN_delSets_err {n : Nat} {devm : Devm} {err : String × Devm}
    (hp : devm.popN n = Except.error err) :
    err.2.delSets = devm.delSets := by
  induction n generalizing devm err with
  | zero => simp [Devm.popN] at hp
  | succ n ih =>
    simp [Devm.popN, bind, Except.bind] at hp
    split at hp
    · rename_i eq_err; injection hp with eq; subst eq
      exact Devm.pop_delSets_err eq_err
    · rename_i eq_ok; split at hp
      · rename_i eq_err; injection hp with eq; subst eq
        have h1 := ih eq_err
        have h2 := Devm.pop_delSets_eq eq_ok
        exact h1.trans h2
      · rename_i eq_ok2; injection hp

lemma Devm.pop_map_snd_delSets_eq {devm devm1 : Devm} (hp : (devm.pop <&> Prod.snd) = .ok devm1) : devm1.delSets = devm.delSets := by
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at hp
  rcases hp2 : devm.pop with _ | ⟨x, devm2⟩
  · simp [hp2] at hp
  · simp [hp2] at hp
    rcases hp with ⟨_, rfl⟩
    exact Devm.pop_delSets_eq hp2

lemma Devm.pop_map_snd_delSets_err {devm : Devm} {err : String × Devm} (hp : (devm.pop <&> Prod.snd) = .error err) : err.2.delSets = devm.delSets := by
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at hp
  rcases hp2 : devm.pop with e | ⟨x, devm2⟩
  · simp [hp2] at hp; cases hp
    simp only [Devm.pop] at hp2
    split at hp2 <;> try contradiction
    cases hp2; rfl
  · simp [hp2] at hp

lemma pushItem_delSets_err {x c devm err} (h : pushItem x c devm = Except.error err) : err.2.delSets = devm.delSets := by
  simp only [pushItem] at h
  refine delSets_err_of_bind h id ?_ ?_ ?_
  · intro devm1 hc; exact (chargeGas_delSets_eq hc).trans rfl
  · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
  · intro devm1 hc run; exact Devm.push_delSets_err run

lemma applyUnary_delSets_err {f : B256 → B256} {cost devm err}
    (h : applyUnary f cost devm = Except.error err) :
    err.2.delSets = devm.delSets := by
  simp only [applyUnary] at h
  refine delSets_err_of_bind h Prod.snd ?_ ?_ ?_
  · intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp
  · intro e hp; exact Devm.pop_delSets_err hp
  · intro ⟨x, devm1⟩ hp run; exact pushItem_delSets_err run

lemma applyBinary_delSets_err {f : B256 → B256 → B256} {cost devm err}
    (h : applyBinary f cost devm = Except.error err) :
    err.2.delSets = devm.delSets := by
  simp only [applyBinary] at h
  refine delSets_err_of_bind h Prod.snd ?_ ?_ ?_
  · intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp
  · intro e hp; exact Devm.pop_delSets_err hp
  · intro ⟨x, devm1⟩ hp run
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨y, devm2⟩ hp2; exact Devm.pop_delSets_eq hp2
    · intro e hp2; exact Devm.pop_delSets_err hp2
    · intro ⟨y, devm2⟩ hp2 run2; exact pushItem_delSets_err run2

lemma applyTernary_delSets_err {f : B256 → B256 → B256 → B256} {cost devm err}
    (h : applyTernary f cost devm = Except.error err) :
    err.2.delSets = devm.delSets := by
  simp only [applyTernary] at h
  refine delSets_err_of_bind h Prod.snd ?_ ?_ ?_
  · intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp
  · intro e hp; exact Devm.pop_delSets_err hp
  · intro ⟨x, devm1⟩ hp run
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨y, devm2⟩ hp2; exact Devm.pop_delSets_eq hp2
    · intro e hp2; exact Devm.pop_delSets_err hp2
    · intro ⟨y, devm2⟩ hp2 run2
      refine delSets_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨z, devm3⟩ hp3; exact Devm.pop_delSets_eq hp3
      · intro e hp3; exact Devm.pop_delSets_err hp3
      · intro ⟨z, devm3⟩ hp3 run3; exact pushItem_delSets_err run3

-- [FILL-07] [MECH-LARGE] Same for error results (error payloads are the
-- intermediate devms).  CRIB: `Rinst.inv_getCode_err` (Common.lean:4644)
-- — same skeleton, delSets instead of getCode.
lemma Rinst.inv_delSets_err {pc : Nat} {sevm : Sevm} {devm : Devm} {r : Rinst}
    {err : String} {devm' : Devm}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = .error ⟨err, devm'⟩) :
    devm'.delSets = devm.delSets := by
  cases r <;> dsimp [Rinst.run, Rinst.runCore] at run
  case add => apply applyBinary_delSets_err run
  case mul => apply applyBinary_delSets_err run
  case sub => apply applyBinary_delSets_err run
  case div => apply applyBinary_delSets_err run
  case sdiv => apply applyBinary_delSets_err run
  case mod => apply applyBinary_delSets_err run
  case smod => apply applyBinary_delSets_err run
  case addmod => apply applyTernary_delSets_err run
  case mulmod => apply applyTernary_delSets_err run
  case exp =>
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp
    · intro e hp; exact Devm.pop_delSets_err hp
    · intro ⟨x, devm1⟩ hp run2
      refine delSets_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.pop_delSets_eq hp2
      · intro e hp2; exact Devm.pop_delSets_err hp2
      · intro ⟨y, devm2⟩ hp2 run3; exact pushItem_delSets_err run3
  case signextend => apply applyBinary_delSets_err run
  case lt => apply applyBinary_delSets_err run
  case gt => apply applyBinary_delSets_err run
  case slt => apply applyBinary_delSets_err run
  case sgt => apply applyBinary_delSets_err run
  case eq => apply applyBinary_delSets_err run
  case iszero => apply applyUnary_delSets_err run
  case and => apply applyBinary_delSets_err run
  case or => apply applyBinary_delSets_err run
  case xor => apply applyBinary_delSets_err run
  case not => apply applyUnary_delSets_err run
  case byte => apply applyBinary_delSets_err run
  case shr => apply applyBinary_delSets_err run
  case shl => apply applyBinary_delSets_err run
  case sar => apply applyBinary_delSets_err run
  case kec =>
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_delSets_eq hp
    · intro e hp; exact Devm.popToNat_delSets_err hp
    · intro ⟨x, devm1⟩ hp run2
      refine delSets_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_delSets_eq hp2
      · intro e hp2; exact Devm.popToNat_delSets_err hp2
      · intro ⟨y, devm2⟩ hp2 run3
        refine delSets_err_of_bind run3 id ?_ ?_ ?_
        · intro devm3 hc; exact (chargeGas_delSets_eq hc).trans rfl
        · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
        · intro devm3 hc run4; exact (Devm.push_delSets_err run4).trans rfl
  case address => apply pushItem_delSets_err run
  case balance =>
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp
    · intro e hp; exact Devm.pop_delSets_err hp
    · intro ⟨x, devm1⟩ hp run2; split at run2
      · refine delSets_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl
        · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
        · intro devm2 hc run3; exact (Devm.push_delSets_err run3).trans rfl
      · refine delSets_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl
        · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
        · intro devm2 hc run3; exact (Devm.push_delSets_err run3).trans rfl
  case origin => apply pushItem_delSets_err run
  case caller => apply pushItem_delSets_err run
  case callvalue => apply pushItem_delSets_err run
  case calldataload =>
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp
    · intro e hp; exact Devm.pop_delSets_err hp
    · intro ⟨x, devm1⟩ hp run2
      refine delSets_err_of_bind run2 id ?_ ?_ ?_
      · intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl
      · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
      · intro devm2 hc run3; exact (Devm.push_delSets_err run3).trans rfl
  case calldatasize => apply pushItem_delSets_err run
  case calldatacopy =>
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_delSets_eq hp
    · intro e hp; exact Devm.popToNat_delSets_err hp
    · intro ⟨x, devm1⟩ hp run2
      refine delSets_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_delSets_eq hp2
      · intro e hp2; exact Devm.popToNat_delSets_err hp2
      · intro ⟨y, devm2⟩ hp2 run3
        refine delSets_err_of_bind run3 Prod.snd ?_ ?_ ?_
        · intro ⟨z, devm3⟩ hp3; exact Devm.popToNat_delSets_eq hp3
        · intro e hp3; exact Devm.popToNat_delSets_err hp3
        · intro ⟨z, devm3⟩ hp3 run4
          refine delSets_err_of_bind run4 id ?_ ?_ ?_
          · intro devm4 hc; exact (chargeGas_delSets_eq hc).trans rfl
          · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
          · intro devm4 hc run5; injection run5
  case codesize => apply pushItem_delSets_err run
  case codecopy =>
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_delSets_eq hp
    · intro e hp; exact Devm.popToNat_delSets_err hp
    · intro ⟨x, devm1⟩ hp run2
      refine delSets_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_delSets_eq hp2
      · intro e hp2; exact Devm.popToNat_delSets_err hp2
      · intro ⟨y, devm2⟩ hp2 run3
        refine delSets_err_of_bind run3 Prod.snd ?_ ?_ ?_
        · intro ⟨z, devm3⟩ hp3; exact Devm.popToNat_delSets_eq hp3
        · intro e hp3; exact Devm.popToNat_delSets_err hp3
        · intro ⟨z, devm3⟩ hp3 run4
          refine delSets_err_of_bind run4 id ?_ ?_ ?_
          · intro devm4 hc; exact (chargeGas_delSets_eq hc).trans rfl
          · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
          · intro devm4 hc run5; injection run5
  case gasprice => apply pushItem_delSets_err run
  case extcodesize =>
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToAdr_delSets_eq hp
    · intro e hp; exact Devm.popToAdr_delSets_err hp
    · intro ⟨x, devm1⟩ hp run2; split at run2
      · refine delSets_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl
        · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
        · intro devm2 hc run3; exact (Devm.push_delSets_err run3).trans rfl
      · refine delSets_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl
        · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
        · intro devm2 hc run3; exact (Devm.push_delSets_err run3).trans rfl
  case extcodecopy =>
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToAdr_delSets_eq hp
    · intro e hp; exact Devm.popToAdr_delSets_err hp
    · intro ⟨x, devm1⟩ hp run2
      refine delSets_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_delSets_eq hp2
      · intro e hp2; exact Devm.popToNat_delSets_err hp2
      · intro ⟨y, devm2⟩ hp2 run3
        refine delSets_err_of_bind run3 Prod.snd ?_ ?_ ?_
        · intro ⟨z, devm3⟩ hp3; exact Devm.popToNat_delSets_eq hp3
        · intro e hp3; exact Devm.popToNat_delSets_err hp3
        · intro ⟨z, devm3⟩ hp3 run4
          refine delSets_err_of_bind run4 Prod.snd ?_ ?_ ?_
          · intro ⟨w, devm4⟩ hp4; exact Devm.popToNat_delSets_eq hp4
          · intro e hp4; exact Devm.popToNat_delSets_err hp4
          · intro ⟨w, devm4⟩ hp4 run5
            split at run5
            · refine delSets_err_of_bind run5 id ?_ ?_ ?_
              · intro devm5 hc; exact (chargeGas_delSets_eq hc).trans rfl
              · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
              · intro devm5 hc run6; injection run6
            · refine delSets_err_of_bind run5 id ?_ ?_ ?_
              · intro devm5 hc; exact (chargeGas_delSets_eq hc).trans rfl
              · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
              · intro devm5 hc run6; injection run6
  case retdatasize => apply pushItem_delSets_err run
  case retdatacopy =>
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_delSets_eq hp
    · intro e hp; exact Devm.popToNat_delSets_err hp
    · intro ⟨x, devm1⟩ hp run2
      refine delSets_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_delSets_eq hp2
      · intro e hp2; exact Devm.popToNat_delSets_err hp2
      · intro ⟨y, devm2⟩ hp2 run3
        refine delSets_err_of_bind run3 Prod.snd ?_ ?_ ?_
        · intro ⟨z, devm3⟩ hp3; exact Devm.popToNat_delSets_eq hp3
        · intro e hp3; exact Devm.popToNat_delSets_err hp3
        · intro ⟨z, devm3⟩ hp3 run4
          refine delSets_err_of_bind run4 id ?_ ?_ ?_
          · intro devm4 hc; exact (chargeGas_delSets_eq hc).trans rfl
          · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
          · intro devm4 hc run5
            split_ifs at run5
            all_goals (try { cases run5; rfl })
            all_goals (try contradiction)
  case extcodehash =>
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToAdr_delSets_eq hp
    · intro e hp; exact Devm.popToAdr_delSets_err hp
    · intro ⟨x, devm1⟩ hp run2; split at run2
      · refine delSets_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl
        · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
        · intro devm2 hc run3; exact (Devm.push_delSets_err run3).trans rfl
      · refine delSets_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl
        · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
        · intro devm2 hc run3; exact (Devm.push_delSets_err run3).trans rfl
  case blockhash =>
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp
    · intro e hp; exact Devm.pop_delSets_err hp
    · intro ⟨x, devm1⟩ hp run2
      refine delSets_err_of_bind run2 id ?_ ?_ ?_
      · intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl
      · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
      · intro devm2 hc run3; exact (Devm.push_delSets_err run3).trans rfl
  case coinbase => apply pushItem_delSets_err run
  case timestamp => apply pushItem_delSets_err run
  case number => apply pushItem_delSets_err run
  case prevrandao => apply pushItem_delSets_err run
  case gaslimit => apply pushItem_delSets_err run
  case chainid => apply pushItem_delSets_err run
  case selfbalance => apply pushItem_delSets_err run
  case basefee => apply pushItem_delSets_err run
  case blobhash =>
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    exact fun ⟨x, devm1⟩ hp => Devm.pop_delSets_eq hp
    exact fun e hp => Devm.pop_delSets_err hp
    intro ⟨x, devm1⟩ hp run2
    refine delSets_err_of_bind run2 id ?_ ?_ ?_
    exact fun devm2 hc => (chargeGas_delSets_eq hc).trans rfl
    exact fun e hc => (chargeGas_delSets_err hc).trans rfl
    intro devm2 hc run3; exact (Devm.push_delSets_err run3).trans rfl
  case blobbasefee => apply pushItem_delSets_err run
  case pop =>
    refine delSets_err_of_bind run id ?_ ?_ ?_
    exact fun devm1 hc => Devm.pop_map_snd_delSets_eq hc
    exact fun e hc => Devm.pop_map_snd_delSets_err hc
    intro devm1 hc run2; exact chargeGas_delSets_err run2
  case mload =>
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    exact fun ⟨x, devm1⟩ hp => Devm.popToNat_delSets_eq hp
    exact fun e hp => Devm.popToNat_delSets_err hp
    intro ⟨x, devm1⟩ hp run2
    refine delSets_err_of_bind run2 id ?_ ?_ ?_
    exact fun devm2 hc => (chargeGas_delSets_eq hc).trans rfl
    exact fun e hc => (chargeGas_delSets_err hc).trans rfl
    intro devm2 hc run3; exact (Devm.push_delSets_err run3).trans rfl
  case mstore =>
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_delSets_eq hp
    · intro e hp; exact Devm.popToNat_delSets_err hp
    · intro ⟨x, devm1⟩ hp run2
      refine delSets_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.pop_delSets_eq hp2
      · intro e hp2; exact Devm.pop_delSets_err hp2
      · intro ⟨y, devm2⟩ hp2 run3
        refine delSets_err_of_bind run3 id ?_ ?_ ?_
        · intro devm3 hc; exact (chargeGas_delSets_eq hc).trans rfl
        · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
        · intro devm3 hc run4; cases run4
  case mstore8 =>
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_delSets_eq hp
    · intro e hp; exact Devm.popToNat_delSets_err hp
    · intro ⟨x, devm1⟩ hp run2
      refine delSets_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.pop_delSets_eq hp2
      · intro e hp2; exact Devm.pop_delSets_err hp2
      · intro ⟨y, devm2⟩ hp2 run3
        refine delSets_err_of_bind run3 id ?_ ?_ ?_
        · intro devm3 hc; exact (chargeGas_delSets_eq hc).trans rfl
        · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
        · intro devm3 hc run4; injection run4
  case sload =>
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp
    · intro e hp; exact Devm.pop_delSets_err hp
    · intro ⟨x, devm1⟩ hp run2; split at run2
      · refine delSets_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl
        · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
        · intro devm2 hc run3; exact (Devm.push_delSets_err run3).trans rfl
      · refine delSets_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl
        · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
        · intro devm2 hc run3; exact (Devm.push_delSets_err run3).trans rfl
  case sstore =>
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp
    · intro e hp; exact Devm.pop_delSets_err hp
    · intro ⟨x, devm1⟩ hp run2
      refine delSets_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.pop_delSets_eq hp2
      · intro e hp2; exact Devm.pop_delSets_err hp2
      · intro ⟨y, devm2⟩ hp2 run3
        refine delSets_err_of_bind run3 (fun _ => devm2) ?_ ?_ ?_
        · intro u h_assert; rfl
        · intro e h_assert; exact assert_delSets_err h_assert
        · intro u h_assert run4
          split_ifs at run4
          all_goals {
            refine delSets_err_of_bind run4 id ?_ ?_ ?_
            · intro devm3 hc; exact (chargeGas_delSets_eq hc).trans rfl
            · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
            · intro devm3 hc run5
              dsimp [assertDynamic, Except.assert] at run5
              split_ifs at run5
              all_goals (try { cases run5; rfl })
              all_goals (try injection run5)
          }
  case pc =>
    refine delSets_err_of_bind run id ?_ ?_ ?_
    · intro devm1 hc; exact (chargeGas_delSets_eq hc).trans rfl
    · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
    · intro devm1 hc run2; exact Devm.push_delSets_err run2
  case msize =>
    refine delSets_err_of_bind run id ?_ ?_ ?_
    · intro devm1 hc; exact (chargeGas_delSets_eq hc).trans rfl
    · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
    · intro devm1 hc run2; exact Devm.push_delSets_err run2
  case gas =>
    refine delSets_err_of_bind run id ?_ ?_ ?_
    · intro devm1 hc; exact (chargeGas_delSets_eq hc).trans rfl
    · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
    · intro devm1 hc run2; exact Devm.push_delSets_err run2
  case tload =>
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp
    · intro e hp; exact Devm.pop_delSets_err hp
    · intro ⟨x, devm1⟩ hp run2
      refine delSets_err_of_bind run2 id ?_ ?_ ?_
      · intro devm2 hc; exact (chargeGas_delSets_eq hc).trans rfl
      · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
      · intro devm2 hc run3; exact (Devm.push_delSets_err run3).trans rfl
  case tstore =>
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_delSets_eq hp
    · intro e hp; exact Devm.pop_delSets_err hp
    · intro ⟨x, devm1⟩ hp run2
      refine delSets_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.pop_delSets_eq hp2
      · intro e hp2; exact Devm.pop_delSets_err hp2
      · intro ⟨y, devm2⟩ hp2 run3
        refine delSets_err_of_bind run3 id ?_ ?_ ?_
        · intro devm3 hc; exact (chargeGas_delSets_eq hc).trans rfl
        · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
        · intro devm3 hc run4
          dsimp [assertDynamic, Except.assert] at run4
          simp only [bind, Except.bind] at run4
          try split_ifs at run4; simp at run4
          exact congrArg Devm.delSets run4.2.symm
  case mcopy =>
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_delSets_eq hp
    · intro e hp; exact Devm.popToNat_delSets_err hp
    · intro ⟨x, devm1⟩ hp run2
      refine delSets_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_delSets_eq hp2
      · intro e hp2; exact Devm.popToNat_delSets_err hp2
      · intro ⟨y, devm2⟩ hp2 run3
        refine delSets_err_of_bind run3 Prod.snd ?_ ?_ ?_
        · intro ⟨z, devm3⟩ hp3; exact Devm.popToNat_delSets_eq hp3
        · intro e hp3; exact Devm.popToNat_delSets_err hp3
        · intro ⟨z, devm3⟩ hp3 run4
          refine delSets_err_of_bind run4 id ?_ ?_ ?_
          · intro devm4 hc; exact (chargeGas_delSets_eq hc).trans rfl
          · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
          · intro devm4 hc run5; contradiction
  case dup =>
    refine delSets_err_of_bind run id ?_ ?_ ?_
    · intro devm1 hc; exact (chargeGas_delSets_eq hc).trans rfl
    · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
    · intro devm1 hc run2
      split at run2
      · injection run2 with h_eq; cases h_eq; rfl
      · exact Devm.push_delSets_err run2
  case swap =>
    refine delSets_err_of_bind run id ?_ ?_ ?_
    · intro devm1 hc; exact (chargeGas_delSets_eq hc).trans rfl
    · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
    · intro devm1 hc run2
      split at run2
      · injection run2 with h_eq; cases h_eq; rfl
      · contradiction
  case log =>
    refine delSets_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_delSets_eq hp
    · intro e hp; exact Devm.popToNat_delSets_err hp
    · intro ⟨x, devm1⟩ hp run2
      refine delSets_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_delSets_eq hp2
      · intro e hp2; exact Devm.popToNat_delSets_err hp2
      · intro ⟨y, devm2⟩ hp2 run3
        refine delSets_err_of_bind run3 Prod.snd ?_ ?_ ?_
        · intro ⟨z, devm3⟩ hp3; exact Devm.popN_delSets_eq hp3
        · intro e hp3; exact Devm.popN_delSets_err hp3
        · intro ⟨z, devm3⟩ hp3 run4
          refine delSets_err_of_bind run4 id ?_ ?_ ?_
          · intro devm4 hc; exact (chargeGas_delSets_eq hc).trans rfl
          · intro e hc; exact (chargeGas_delSets_err hc).trans rfl
          · intro devm4 hc run5
            dsimp [assertDynamic, Except.assert] at run5
            simp only [bind, Except.bind] at run5
            try split_ifs at run5; simp at run5
            exact congrArg Devm.delSets run5.2.symm

-- [FILL-08] [MECH] Jumps touch only stack/gas/pc.  CRIB: `Jinst.inv_state`
-- (Solvent.lean:2452) — same case bash, reading off the sets instead of
-- state; and `Jinst.inv_getCode_gen` (Common.lean:5586) for the error case.
lemma Jinst.inv_delSets {pc : Nat} {sevm : Sevm} {devm : Devm} {j : Jinst}
    {pc' : Nat} {devm' : Devm}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j (.ok ⟨pc', devm'⟩)) :
    devm'.delSets = devm.delSets := by
  cases h1 : devm.stack
  · cases j
    · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, safeSub, bind, Except.bind] at run
      rw [h1] at run; dsimp at run; contradiction
    · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, safeSub, bind, Except.bind] at run
      rw [h1] at run; dsimp at run; contradiction
    · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, bind, Except.bind, safeSub] at run
      rw [h1] at run
      by_cases h_gas : gJumpdest ≤ devm.gasLeft
      · simp only [h_gas, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
        cases run; subst_vars; rfl
      · have h_gas_not : ¬(gJumpdest ≤ devm.gasLeft) := by omega
        simp only [h_gas_not, if_neg] at run; contradiction
  · rename_i x xs
    cases h2 : xs
    · cases j
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, bind, Except.bind, safeSub] at run
        rw [h1] at run; dsimp at run
        by_cases h_gas : gMid ≤ devm.gasLeft
        · simp only [h_gas, if_pos] at run
          by_cases h_jump : jumpable sevm.code x.toNat = true
          · simp only [h_jump, if_pos, Except.ok.injEq, Prod.mk.injEq] at run; cases run; subst_vars; rfl
          · simp only [h_jump, if_neg] at run; contradiction
        · have h_gas_not : ¬(gMid ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg] at run; contradiction
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, bind, Except.bind, safeSub] at run
        rw [h1] at run; rw [h2] at run; dsimp at run; contradiction
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Except.assert, bind, Except.bind, safeSub] at run
        rw [h1] at run
        by_cases h_gas : gJumpdest ≤ devm.gasLeft
        · simp only [h_gas, if_pos, Except.ok.injEq, Prod.mk.injEq] at run; cases run; subst_vars; rfl
        · have h_gas_not : ¬(gJumpdest ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg] at run; contradiction
    · rename_i x2 xs2
      cases j
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, bind, Except.bind, safeSub] at run
        rw [h1] at run; dsimp at run
        by_cases h_gas : gMid ≤ devm.gasLeft
        · simp only [h_gas, if_pos] at run
          by_cases h_jump : jumpable sevm.code x.toNat = true
          · simp only [h_jump, if_pos, Except.ok.injEq, Prod.mk.injEq] at run; cases run; subst_vars; rfl
          · simp only [h_jump, if_neg] at run; contradiction
        · have h_gas_not : ¬(gMid ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg] at run; contradiction
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, bind, Except.bind, safeSub] at run
        rw [h1] at run; rw [h2] at run; dsimp at run
        by_cases h_gas : gHigh ≤ devm.gasLeft
        · simp only [h_gas, if_pos] at run
          by_cases h_cond : x2 = 0
          · simp only [h_cond, if_pos, Except.ok.injEq, Prod.mk.injEq] at run; cases run; subst_vars; rfl
          · simp only [h_cond, if_neg] at run
            by_cases h_jumpable : jumpable sevm.code x.toNat = true
            · simp only [h_jumpable, if_pos, Except.ok.injEq, Prod.mk.injEq] at run; cases run; subst_vars; rfl
            · simp only [h_jumpable, if_neg] at run; contradiction
        · have h_gas_not : ¬(gHigh ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg] at run; contradiction
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Except.assert, bind, Except.bind, safeSub] at run
        rw [h1] at run
        by_cases h_gas : gJumpdest ≤ devm.gasLeft
        · simp only [h_gas, if_pos, Except.ok.injEq, Prod.mk.injEq] at run; cases run; subst_vars; rfl
        · have h_gas_not : ¬(gJumpdest ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg] at run; contradiction

lemma Jinst.inv_delSets_err {pc : Nat} {sevm : Sevm} {devm : Devm} {j : Jinst}
    {err : String} {devm' : Devm}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j (.error ⟨err, devm'⟩)) :
    devm'.delSets = devm.delSets := by
  cases h1 : devm.stack
  · cases j
    · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, safeSub, bind, Except.bind] at run
      rw [h1] at run; dsimp at run; cases run; rfl
    · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, safeSub, bind, Except.bind] at run
      rw [h1] at run; dsimp at run; cases run; rfl
    · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, bind, Except.bind, safeSub] at run
      rw [h1] at run
      by_cases h_gas : gJumpdest ≤ devm.gasLeft
      · simp only [h_gas, if_pos] at run; contradiction
      · have h_gas_not : ¬(gJumpdest ≤ devm.gasLeft) := by omega
        simp only [h_gas_not, if_neg] at run; cases run; rfl
  · rename_i x xs
    cases h2 : xs
    · cases j
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, bind, Except.bind, safeSub] at run
        rw [h1] at run; dsimp at run
        by_cases h_gas : gMid ≤ devm.gasLeft
        · simp only [h_gas, if_pos] at run
          by_cases h_jump : jumpable sevm.code x.toNat = true
          · simp only [h_jump, if_pos] at run; contradiction
          · simp only [h_jump, if_neg] at run; cases run; rfl
        · have h_gas_not : ¬(gMid ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg] at run; cases run; rfl
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, bind, Except.bind, safeSub] at run
        rw [h1] at run; rw [h2] at run; dsimp at run; cases run; rfl
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Except.assert, bind, Except.bind, safeSub] at run
        rw [h1] at run
        by_cases h_gas : gJumpdest ≤ devm.gasLeft
        · simp only [h_gas, if_pos] at run; contradiction
        · have h_gas_not : ¬(gJumpdest ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg] at run; cases run; rfl
    · rename_i x2 xs2
      cases j
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, bind, Except.bind, safeSub] at run
        rw [h1] at run; dsimp at run
        by_cases h_gas : gMid ≤ devm.gasLeft
        · simp only [h_gas, if_pos] at run
          by_cases h_jump : jumpable sevm.code x.toNat = true
          · simp only [h_jump, if_pos] at run; contradiction
          · simp only [h_jump, if_neg] at run; cases run; rfl
        · have h_gas_not : ¬(gMid ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg] at run; cases run; rfl
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, bind, Except.bind, safeSub] at run
        rw [h1] at run; rw [h2] at run; dsimp at run
        by_cases h_gas : gHigh ≤ devm.gasLeft
        · simp only [h_gas, if_pos] at run
          by_cases h_cond : x2 = 0
          · simp only [h_cond, if_pos] at run; contradiction
          · simp only [h_cond, if_neg] at run
            by_cases h_jumpable : jumpable sevm.code x.toNat = true
            · simp only [h_jumpable, if_pos] at run; contradiction
            · simp only [h_jumpable, if_neg] at run; cases run; rfl
        · have h_gas_not : ¬(gHigh ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg] at run; cases run; rfl
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Except.assert, bind, Except.bind, safeSub] at run
        rw [h1] at run
        by_cases h_gas : gJumpdest ≤ devm.gasLeft
        · simp only [h_gas, if_pos] at run; contradiction
        · have h_gas_not : ¬(gJumpdest ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg] at run; cases run; rfl

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
  cases l <;> dsimp [Linst.Run, Linst.run] at run
  case stop => rw [← run]; exact h
  case ret =>
    revert run
    dsimp [bind, Except.bind]
    cases h1 : devm.popToNat <;> dsimp
    case error err => intro run; rw [← run]; exact Devm.NoDel.of_eqs (Devm.popToNat_delSets_err h1).symm (Devm.popToNat_getCode_err h1 wa).symm h
    case ok res1 =>
      cases h2 : res1.2.popToNat <;> dsimp
      case error err => intro run; rw [← run]; exact Devm.NoDel.of_eqs (Devm.popToNat_delSets_err h2).symm (Devm.popToNat_getCode_err h2 wa).symm (Devm.NoDel.of_eqs (Devm.popToNat_delSets_eq h1).symm (Devm.popToNat_getCode_eq h1 wa).symm h)
      case ok res2 =>
        cases h3 : chargeGas (res2.2.extCost [(res1.1, res2.1)]) res2.2 <;> dsimp
        case error err => intro run; rw [← run]; exact Devm.NoDel.of_eqs (chargeGas_delSets_err h3).symm (chargeGas_getCode_err h3 wa).symm (Devm.NoDel.of_eqs (Devm.popToNat_delSets_eq h2).symm (Devm.popToNat_getCode_eq h2 wa).symm (Devm.NoDel.of_eqs (Devm.popToNat_delSets_eq h1).symm (Devm.popToNat_getCode_eq h1 wa).symm h))
        case ok res3 => intro run; rw [← run]; exact Devm.NoDel.of_eqs (chargeGas_delSets_eq h3).symm (chargeGas_getCode_eq h3 wa).symm (Devm.NoDel.of_eqs (Devm.popToNat_delSets_eq h2).symm (Devm.popToNat_getCode_eq h2 wa).symm (Devm.NoDel.of_eqs (Devm.popToNat_delSets_eq h1).symm (Devm.popToNat_getCode_eq h1 wa).symm h))
  case rev =>
    revert run
    dsimp [bind, Except.bind]
    cases h1 : devm.popToNat <;> dsimp
    case error err => intro run; rw [← run]; exact Devm.NoDel.of_eqs (Devm.popToNat_delSets_err h1).symm (Devm.popToNat_getCode_err h1 wa).symm h
    case ok res1 =>
      cases h2 : res1.2.popToNat <;> dsimp
      case error err => intro run; rw [← run]; exact Devm.NoDel.of_eqs (Devm.popToNat_delSets_err h2).symm (Devm.popToNat_getCode_err h2 wa).symm (Devm.NoDel.of_eqs (Devm.popToNat_delSets_eq h1).symm (Devm.popToNat_getCode_eq h1 wa).symm h)
      case ok res2 =>
        cases h3 : chargeGas (res2.2.extCost [(res1.1, res2.1)]) res2.2 <;> dsimp
        case error err => intro run; rw [← run]; exact Devm.NoDel.of_eqs (chargeGas_delSets_err h3).symm (chargeGas_getCode_err h3 wa).symm (Devm.NoDel.of_eqs (Devm.popToNat_delSets_eq h2).symm (Devm.popToNat_getCode_eq h2 wa).symm (Devm.NoDel.of_eqs (Devm.popToNat_delSets_eq h1).symm (Devm.popToNat_getCode_eq h1 wa).symm h))
        case ok res3 => intro run; rw [← run]; exact Devm.NoDel.of_eqs rfl rfl (Devm.NoDel.of_eqs (chargeGas_delSets_eq h3).symm (chargeGas_getCode_eq h3 wa).symm (Devm.NoDel.of_eqs (Devm.popToNat_delSets_eq h2).symm (Devm.popToNat_getCode_eq h2 wa).symm (Devm.NoDel.of_eqs (Devm.popToNat_delSets_eq h1).symm (Devm.popToNat_getCode_eq h1 wa).symm h)))
  case dest =>
    revert run
    dsimp [bind, Except.bind]
    cases h1 : devm.popToAdr <;> dsimp
    case error err => intro run; rw [← run]; exact Devm.NoDel.of_eqs (Devm.popToAdr_delSets_err h1).symm (Devm.popToAdr_getCode_err h1 wa).symm h
    case ok res1 =>
      have h_acc : (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1.getCode wa = res1.2.getCode wa := by
        split
        · exact addAccessedAddress_getCode
        · rfl
      have h_acc_ds : (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1.delSets = res1.2.delSets := by
        split
        · rfl
        · rfl
      cases h2 : chargeGas (if ((if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1.getAcct res1.1).Empty ∧ ¬(res1.2.getAcct sevm.currentTarget).bal = 0 then (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).2 + gasSelfDestructNewAccount else (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).2) (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1 <;> dsimp
      case error err => intro run; rw [← run]; exact Devm.NoDel.of_eqs (chargeGas_delSets_err h2).symm (chargeGas_getCode_err h2 wa).symm (Devm.NoDel.of_eqs h_acc_ds.symm h_acc.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h))
      case ok res2 =>
        cases h3 : assertDynamic sevm res2
        case error err =>
          intro run; rw [← run]
          dsimp [assertDynamic, Except.assert] at h3
          split at h3
          · contradiction
          · simp only [Except.error.injEq] at h3; subst h3
            exact Devm.NoDel.of_eqs (chargeGas_delSets_eq h2).symm (chargeGas_getCode_eq h2 wa).symm (Devm.NoDel.of_eqs h_acc_ds.symm h_acc.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h))
        case ok _ =>
          cases h4 : res2.subBal sevm.currentTarget (res1.2.getAcct sevm.currentTarget).bal <;> dsimp [Option.toExcept]
          case none =>
            intro run; rw [← run]
            exact Devm.NoDel.of_eqs (chargeGas_delSets_eq h2).symm (chargeGas_getCode_eq h2 wa).symm (Devm.NoDel.of_eqs h_acc_ds.symm h_acc.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h))
          case some res3 =>
            have hd : Devm.NoDel wa res2 := Devm.NoDel.of_eqs (chargeGas_delSets_eq h2).symm (chargeGas_getCode_eq h2 wa).symm (Devm.NoDel.of_eqs h_acc_ds.symm h_acc.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h))
            have h_sub : res3.getCode wa = res2.getCode wa := by
              dsimp [Devm.subBal] at h4
              cases h_st : res2.state.subBal sevm.currentTarget (res1.2.getAcct sevm.currentTarget).bal
              case none =>
                rw [h_st] at h4; contradiction
              case some st =>
                rw [h_st] at h4; dsimp at h4
                simp only [Option.some.injEq] at h4; subst h4
                change st.getCode wa = res2.getCode wa
                exact State.subBal_getCode h_st
            have h_sub_ds : res3.delSets = res2.delSets := by
              dsimp [Devm.subBal] at h4
              cases h_st : res2.state.subBal sevm.currentTarget (res1.2.getAcct sevm.currentTarget).bal
              case none => rw [h_st] at h4; contradiction
              case some st =>
                rw [h_st] at h4; dsimp at h4
                simp only [Option.some.injEq] at h4; subst h4
                rfl
            have hd3 : Devm.NoDel wa res3 := Devm.NoDel.of_eqs h_sub_ds.symm h_sub.symm hd
            by_cases h_if : sevm.currentTarget ∈ (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).createdAccounts
            · simp only [h_if, if_pos]
              intro run; rw [← run]
              have h_ca_eq : (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).createdAccounts = res3.createdAccounts := rfl
              have h_ca : sevm.currentTarget ∈ res3.createdAccounts := h_ca_eq ▸ h_if
              have h_ne : sevm.currentTarget ≠ wa := by
                intro heq; rw [heq] at h_ca
                exact hd3.ca h_ca
              constructor
              · exact AdrSet.not_mem_insert (Ne.symm h_ne) hd3.atd
              · exact hd3.ca
              · have h_add : (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).getCode wa = res3.getCode wa := by
                  dsimp [Devm.addBal, Devm.getCode]; exact State.addBal_getCode res3.state _ _ _
                have h_set : ((res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).setBal sevm.currentTarget 0).getCode wa = (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).getCode wa := by
                  dsimp [Devm.setBal, Devm.getCode]; exact State.setBal_getCode _ _ _ _
                have h_code : (addAccountToDelete ((res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).setBal sevm.currentTarget 0) sevm.currentTarget).getCode wa = res3.getCode wa :=
                  h_set.trans h_add
                rw [h_code]; exact hd3.code
            · simp only [h_if, if_neg]
              intro run; rw [← run]
              constructor
              · exact hd3.atd
              · exact hd3.ca
              · have h_add : (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).getCode wa = res3.getCode wa := by
                  dsimp [Devm.addBal, Devm.getCode]; exact State.addBal_getCode res3.state _ _ _
                rw [h_add]; exact hd3.code

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
  rcases of_executeCode_cases run with ⟨adr, h_precomp⟩ | ⟨ex', h_xl, h_err⟩
  · have h_init : Devm.NoDel wa (initDevm msg) := Msg.NoDel.initDevm h
    have h_ex_noDel : Execution.NoDel wa (executePrecomp (initEvm msg) adr) := executePrecomp_noDel rfl h_init
    rw [← h_precomp]
    exact handleError_noDel h_ex_noDel
  · rw [h_xl] at inv
    dsimp [Xlot.InvNoDel] at inv
    have h_init : Devm.NoDel wa (initDevm msg) := Msg.NoDel.initDevm h
    have h_ex'_noDel : Execution.NoDel wa ex' := inv h_init
    rw [← h_err]
    exact handleError_noDel h_ex'_noDel

lemma Msg.NoDel.benvAfterTransfer_err {wa : Adr} {msg : Msg}
    {x : String × State × AdrSet × Tra}
    (h_run : msg.benvAfterTransfer = .error x)
    (h : Msg.NoDel wa msg) : wa ∉ x.2.2.1 ∧ (x.2.1.getCode wa).toList ≠ [] := by
  by_cases h_stv : msg.shouldTransferValue = true
  · unfold Msg.benvAfterTransfer at h_run
    rw [if_pos h_stv] at h_run
    cases h_sub : msg.benv.subBal msg.caller msg.value
    · rw [h_sub] at h_run
      simp only [Except.error.injEq, Option.toExcept, Except.bind, bind] at h_run
      subst h_run
      exact ⟨h.ca, h.code⟩
    · rw [h_sub] at h_run
      dsimp [Option.toExcept] at h_run
      contradiction
  · unfold Msg.benvAfterTransfer at h_run
    rw [if_neg h_stv] at h_run
    contradiction

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
  dsimp only [ProcessMessage] at run
  rcases run with ⟨x, eq_bt_err, eq_ex_err, _⟩ | ⟨benv', eq_bt, run⟩
  · rw [eq_ex_err]
    exact Msg.NoDel.benvAfterTransfer_err eq_bt_err h
  · have h_nof' : Msg.NoDel wa (msg.withBenv benv') := Msg.NoDel.benvAfterTransfer eq_bt h
    rcases run with ⟨ex'', run_ec, h_split⟩
    rcases h_split with ⟨x, eq_ec_err, eq_ex_err⟩ | ⟨evm2, h_ex'', h_if⟩
    · rw [eq_ex_err]
      have h_exec : MsgResult.NoDel wa ex'' := ExecuteCode.inv_noDel inv invc run_ec h_nof'
      rw [eq_ec_err] at h_exec
      exact h_exec
    · by_cases h_err : evm2.error.isSome = true
      · rw [if_pos h_err] at h_if
        rw [← h_if]
        have h_exec : MsgResult.NoDel wa ex'' := ExecuteCode.inv_noDel inv invc run_ec h_nof'
        rw [h_ex''] at h_exec
        exact Devm.NoDel.rollback h_exec.atd h_exec.ca h.code
      · rw [if_neg h_err] at h_if
        rw [← h_if]
        have h_exec : MsgResult.NoDel wa ex'' := ExecuteCode.inv_noDel inv invc run_ec h_nof'
        rw [h_ex''] at h_exec
        exact h_exec

-- chargeCodeGas preserves delSets on a clean (`.ok`) charge.
lemma chargeCodeGas_delSets_ok {d d' : Devm}
    (h : processCreateMessage.chargeCodeGas d = .ok d') : d'.delSets = d.delSets := by
  unfold processCreateMessage.chargeCodeGas at h
  dsimp only at h
  split at h
  · cases h
  · rcases of_bind_eq_ok h with ⟨d1, h_charge, h_rest⟩
    split_ifs at h_rest
    cases h_rest
    exact chargeGas_delSets_eq h_charge

-- chargeCodeGas preserves delSets on every error payload too (0xEF prefix,
-- OutOfGas from chargeGas, or maxCodeSize overflow).
lemma chargeCodeGas_delSets_err {d d' : Devm} {err : String}
    (h : processCreateMessage.chargeCodeGas d = .error ⟨err, d'⟩) :
    d'.delSets = d.delSets := by
  unfold processCreateMessage.chargeCodeGas at h
  dsimp only at h
  split at h
  · cases h; rfl
  · rcases hcg : chargeGas _ d with ⟨e, dd⟩ | dd
    · rw [hcg] at h
      dsimp only [Bind.bind, Except.bind] at h
      cases h
      exact chargeGas_delSets_err hcg
    · rw [hcg] at h
      dsimp only [Bind.bind, Except.bind] at h
      split_ifs at h
      cases h; exact chargeGas_delSets_eq hcg

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
  dsimp only [ProcessCreateMessage] at run
  rcases run with ⟨ex', run_pm, h_split⟩
  have h_seed : Msg.NoDel wa (processCreateMessage.msg msg) :=
    Msg.NoDel.processCreateMessage_msg h_ct h
  have h_pm : MsgResult.NoDel wa ex' :=
    ProcessMessage.inv_noDel inv invc run_pm h_seed
  rcases h_split with ⟨x, h_err_eq, h_ex_eq⟩ | ⟨evm, h_ex', h_if⟩
  · -- sub-message errored : ex = ex', payload carried through
    rw [h_err_eq] at h_pm
    rw [h_ex_eq]
    exact h_pm
  · -- sub-message ok : evm carries NoDel
    rw [h_ex'] at h_pm
    have h_evm : Devm.NoDel wa evm := h_pm
    by_cases h_err : evm.error.isNone = true
    · rw [if_pos h_err] at h_if
      rcases h_cg : processCreateMessage.chargeCodeGas evm with ⟨err, evm'⟩ | evm' <;>
        rw [h_cg] at h_if <;> dsimp only at h_if
      · -- code-gas charge errored
        have h_ds : evm'.delSets = evm.delSets := chargeCodeGas_delSets_err h_cg
        have h_atd_eq : evm'.accountsToDelete = evm.accountsToDelete := congrArg Prod.fst h_ds
        have h_ca_eq : evm'.createdAccounts = evm.createdAccounts := congrArg Prod.snd h_ds
        have h_atd : wa ∉ evm'.accountsToDelete := by rw [h_atd_eq]; exact h_evm.atd
        have h_ca : wa ∉ evm'.createdAccounts := by rw [h_ca_eq]; exact h_evm.ca
        have h_gc : evm'.getCode wa = evm.getCode wa := by
          have hh := processCreateMessage.chargeCodeGas_getCode_gen h_cg wa
          simpa only [Execution.getCode] using hh
        split_ifs at h_if with h_halt
        · -- exceptional halt : rolled back to msg.benv.state
          rw [← h_if]
          exact ⟨h_atd, h_ca, h.code⟩
        · -- non-halt error : payload = ⟨_, evm'.state, evm'.createdAccounts, _⟩
          rw [← h_if]
          refine ⟨h_ca, ?_⟩
          show (evm'.state.getCode wa).toList ≠ []
          rw [← Devm.getCode_state, h_gc]
          exact h_evm.code
      · -- clean code-gas charge : install code at currentTarget ≠ wa
        rw [← h_if]
        have h_ds : evm'.delSets = evm.delSets := chargeCodeGas_delSets_ok h_cg
        have h_atd_eq : evm'.accountsToDelete = evm.accountsToDelete := congrArg Prod.fst h_ds
        have h_ca_eq : evm'.createdAccounts = evm.createdAccounts := congrArg Prod.snd h_ds
        have h_atd : wa ∉ evm'.accountsToDelete := by rw [h_atd_eq]; exact h_evm.atd
        have h_ca : wa ∉ evm'.createdAccounts := by rw [h_ca_eq]; exact h_evm.ca
        have h_gc : evm'.getCode wa = evm.getCode wa := by
          have hh := processCreateMessage.chargeCodeGas_getCode_gen h_cg wa
          simpa only [Execution.getCode] using hh
        refine ⟨h_atd, h_ca, ?_⟩
        show ((evm'.setCode msg.currentTarget ⟨⟨evm'.output⟩⟩).getCode wa).toList ≠ []
        rw [setCode_getCode h_ct, h_gc]
        exact h_evm.code
    · -- sub-message flagged an error : rolled back to msg.benv.state
      rw [if_neg h_err] at h_if
      rw [← h_if]
      exact Devm.NoDel.rollback h_evm.atd h_evm.ca h.code

-- push transports NoDel to the Execution level: the ok payload changes only
-- the stack, and the overflow-error payload is the input devm itself.
lemma Devm.push_noDel {wa : Adr} {x : B256} {d : Devm} {exn : Execution}
    (heq : Devm.push x d = exn) (h : Devm.NoDel wa d) : Execution.NoDel wa exn := by
  unfold Devm.push Except.assert at heq
  by_cases hlt : d.stack.length < 1024
  · rw [if_pos hlt] at heq
    dsimp only [bind, Except.bind] at heq
    rw [← heq]; exact ⟨h.atd, h.ca, h.code⟩
  · rw [if_neg hlt] at heq
    dsimp only [bind, Except.bind] at heq
    rw [← heq]; exact ⟨h.atd, h.ca, h.code⟩

-- incorporateChildOnError (elevm Execution.lean:1953): keeps the parent's atd,
-- adopts the child's ca/state — so wa stays out of both and keeps its code.
lemma incorporateChildOnError_noDel {wa : Adr} {parent child : Devm} {rd : B8L}
    (hp_atd : wa ∉ parent.accountsToDelete) (hc : Devm.NoDel wa child) :
    Devm.NoDel wa (incorporateChildOnError parent child rd) :=
  ⟨hp_atd, hc.ca, hc.code⟩

-- incorporateChildOnSuccess (elevm Execution.lean:1963): atd := parent ∪ child
-- (both wa-free, via not_mem_union), ca/state := child's.
lemma incorporateChildOnSuccess_noDel {wa : Adr} {parent child : Devm} {rd : B8L}
    (hp_atd : wa ∉ parent.accountsToDelete) (hc : Devm.NoDel wa child) :
    Devm.NoDel wa (incorporateChildOnSuccess parent child rd) :=
  ⟨AdrSet.not_mem_union hp_atd hc.atd, hc.ca, hc.code⟩

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
  dsimp only [GenericCall] at h
  rcases h with ⟨evm1, eq_evm1, h⟩; subst eq_evm1
  split at h
  · -- depth limit reached : call fails, result is a push onto the parent
    rcases h with ⟨_, eq_ok⟩
    exact Devm.push_noDel eq_ok ⟨hnd.atd, hnd.ca, hnd.code⟩
  · rcases h with ⟨calldata, _, h⟩
    rcases h with ⟨childMsg, eq_childMsg, h⟩
    rcases h with ⟨ex', run_pm, h_split⟩
    have h_cm : Msg.NoDel wa childMsg := by
      rw [eq_childMsg]; exact ⟨hnd.ca, hnd.code⟩
    have h_pm : MsgResult.NoDel wa ex' :=
      ProcessMessage.inv_noDel inv invc run_pm h_cm
    rcases h_split with ⟨x, h_err, eq_err⟩ | ⟨child, h_ok, run⟩
    · -- sub-message lift errored : exn = the same error, payload carried through
      rw [eq_err]
      rcases ex' with err | c
      · rcases err with ⟨e_str, e_st, e_ca, e_tra⟩
        dsimp only [liftToExecution] at h_err
        injection h_err with h_eq
        subst h_eq
        rcases h_pm with ⟨h_ca, h_code⟩
        exact ⟨hnd.atd, h_ca, h_code⟩
      · dsimp only [liftToExecution] at h_err
        contradiction
    · -- sub-message lift ok : child carries NoDel
      have h_child : Devm.NoDel wa child := by
        rcases ex' with err | c
        · dsimp only [liftToExecution] at h_ok
          contradiction
        · dsimp only [liftToExecution] at h_ok
          injection h_ok with h_eq
          subst h_eq
          exact h_pm
      split at run
      · -- child errored : incorporateChildOnError, then push + memWrite
        rcases run with ⟨y, h_perr, eq_err⟩ | ⟨evm2, h_pok, eq_ok⟩
        · rw [eq_err]
          exact Devm.push_noDel h_perr (incorporateChildOnError_noDel hnd.atd h_child)
        · rw [← eq_ok]
          exact Devm.NoDel.of_eqs (Devm.push_delSets_eq h_pok).symm
            (Devm.push_getCode_gen h_pok wa).symm
            (incorporateChildOnError_noDel hnd.atd h_child)
      · -- child ok : incorporateChildOnSuccess, then push + memWrite
        rcases run with ⟨y, h_perr, eq_err⟩ | ⟨evm2, h_pok, eq_ok⟩
        · rw [eq_err]
          exact Devm.push_noDel h_perr (incorporateChildOnSuccess_noDel hnd.atd h_child)
        · rw [← eq_ok]
          exact Devm.NoDel.of_eqs (Devm.push_delSets_eq h_pok).symm
            (Devm.push_getCode_gen h_pok wa).symm
            (incorporateChildOnSuccess_noDel hnd.atd h_child)

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
  dsimp only [GenericCreate] at h
  rcases h with ⟨calldata, eq_calldata, h⟩; subst eq_calldata
  -- SplitXl 1 : OutOfGasError assert on the init-code size
  rcases h with ⟨x, h_err, eq_err, _⟩ | ⟨_, _, h⟩
  · rw [eq_err]
    dsimp only [Except.assert] at h_err
    split at h_err
    · contradiction
    · injection h_err with h_eq; subst h_eq; exact hnd
  · rcases h with ⟨devm1, eq_devm1, h⟩
    rcases h with ⟨createMsgGas, _, h⟩
    rcases h with ⟨devm2, eq_devm2, h⟩
    have hnd2 : Devm.NoDel wa devm2 := by
      refine Devm.NoDel.of_eqs (d := devm) ?_ ?_ hnd
      · rw [eq_devm2, eq_devm1]; rfl
      · rw [eq_devm2, eq_devm1]; rfl
    -- SplitXl 2 : WriteInStaticContext assert
    rcases h with ⟨x, h_err, eq_err, _⟩ | ⟨_, _, h⟩
    · rw [eq_err]
      dsimp only [assertDynamic, Except.assert] at h_err
      split at h_err
      · contradiction
      · injection h_err with h_eq; subst h_eq; exact hnd2
    · rcases h with ⟨devm3, eq_devm3, h⟩
      rcases h with ⟨sender, _, h⟩
      have hnd3 : Devm.NoDel wa devm3 := by
        refine Devm.NoDel.of_eqs (d := devm2) ?_ ?_ hnd2
        · rw [eq_devm3]; rfl
        · rw [eq_devm3]; rfl
      split at h
      · -- sender can't afford / nonce maxed / depth 0 : create fails, push 0
        rcases h with ⟨_, h_push⟩
        refine Devm.push_noDel h_push ?_
        exact Devm.NoDel.of_eqs (d := devm3) rfl rfl hnd3
      · rcases h with ⟨devm4, eq_devm4, h⟩
        have hnd4 : Devm.NoDel wa devm4 := by
          refine Devm.NoDel.of_eqs (d := devm3) ?_ ?_ hnd3
          · rw [eq_devm4]; rfl
          · rw [eq_devm4]; exact Devm.incrNonce_getCode.symm
        split at h
        · -- target account already exists : create fails, push 0
          rcases h with ⟨_, h_push⟩
          exact Devm.push_noDel h_push hnd4
        · -- emptiness guard passed : (devm4.state.get newAddress).code.size = 0
          rename_i h_c2
          rcases h with ⟨childMsg, eq_childMsg, h⟩; subst eq_childMsg
          rcases h with ⟨ex', run_pcm, h_split⟩
          have h_ct : newAddress ≠ wa := by
            push_neg at h_c2
            exact ne_wa_of_code_size_zero hnd4.code h_c2.2.1
          have h_pm : MsgResult.NoDel wa ex' :=
            ProcessCreateMessage.inv_noDel inv invc run_pcm h_ct ⟨hnd4.ca, hnd4.code⟩
          rcases h_split with ⟨y, h_lift_err, eq_exn⟩ | ⟨child, h_lift_ok, run⟩
          · -- child lift errored : exn carries the payload's ca/state on devm4
            rw [eq_exn]
            rcases ex' with err | c
            · rcases err with ⟨e_str, e_st, e_ca, e_tra⟩
              dsimp only [liftToExecution] at h_lift_err
              injection h_lift_err with h_eq; subst h_eq
              rcases h_pm with ⟨h_ca, h_code⟩
              exact ⟨hnd4.atd, h_ca, h_code⟩
            · dsimp only [liftToExecution] at h_lift_err; contradiction
          · -- child lift ok : merge via incorporateChild*, then push
            have h_child : Devm.NoDel wa child := by
              rcases ex' with err | c
              · dsimp only [liftToExecution] at h_lift_ok; contradiction
              · dsimp only [liftToExecution] at h_lift_ok
                injection h_lift_ok with h_eq; subst h_eq; exact h_pm
            split at run
            · exact Devm.push_noDel run (incorporateChildOnError_noDel hnd4.atd h_child)
            · exact Devm.push_noDel run (incorporateChildOnSuccess_noDel hnd4.atd h_child)

/-! Helpers for FILL-15: single-step NoDel transports for the argument-popping
    and bookkeeping ops used by `Xinst.Run`, plus error-payload transports.
    Every op preserves both `delSets` and wa's code, and every error payload
    carries the input devm unchanged. -/

lemma accessDelegation_delSets {d : Devm} {adr : Adr} :
    (accessDelegation d adr).2.2.2.2.delSets = d.delSets := by
  simp only [accessDelegation]; split <;> rfl

-- An error payload whose devm is NoDel yields a NoDel Execution result.
lemma Execution.NoDel.error_of {wa : Adr} {d : Devm} {x : String × Devm}
    (hd : Devm.NoDel wa d) (h : x.2 = d) : Execution.NoDel wa (.error x) := by
  obtain ⟨s, d'⟩ := x
  dsimp only at h
  subst h
  exact hd

-- Each op's error payload carries the input devm as its second component.
lemma Devm.pop_err_snd {d : Devm} {x : String × Devm}
    (h : Devm.pop d = .error x) : x.2 = d := by
  simp only [Devm.pop] at h
  split at h
  · injection h with h; exact (congrArg Prod.snd h).symm
  · exact absurd h (by simp)

lemma Devm.popToNat_err_snd {d : Devm} {x : String × Devm}
    (h : Devm.popToNat d = .error x) : x.2 = d := by
  dsimp only [Devm.popToNat, Functor.map, Except.map] at h
  rcases hp : d.pop with e | ⟨v, d0⟩
  · rw [hp] at h; injection h with h; rw [← h]; exact Devm.pop_err_snd hp
  · rw [hp] at h; exact absurd h (by simp)

lemma Devm.popToAdr_err_snd {d : Devm} {x : String × Devm}
    (h : Devm.popToAdr d = .error x) : x.2 = d := by
  dsimp only [Devm.popToAdr, Functor.map, Except.map] at h
  rcases hp : d.pop with e | ⟨v, d0⟩
  · rw [hp] at h; injection h with h; rw [← h]; exact Devm.pop_err_snd hp
  · rw [hp] at h; exact absurd h (by simp)

lemma chargeGas_err_snd {cost : Nat} {d : Devm} {x : String × Devm}
    (h : chargeGas cost d = .error x) : x.2 = d := by
  simp only [chargeGas] at h
  split at h
  · injection h with h; exact (congrArg Prod.snd h).symm
  · exact absurd h (by simp)

lemma Except.assert_err_snd {p : Prop} [Decidable p] {d : Devm} {s : String}
    {x : String × Devm} (h : Except.assert p (⟨s, d⟩ : String × Devm) = .error x) :
    x.2 = d := by
  simp only [Except.assert] at h
  split at h
  · exact absurd h (by simp)
  · injection h with h; exact (congrArg Prod.snd h).symm

-- ok-case transports.
lemma Devm.NoDel.pop {wa : Adr} {d d' : Devm} {v : B256}
    (hd : Devm.NoDel wa d) (h : Devm.pop d = .ok ⟨v, d'⟩) : Devm.NoDel wa d' :=
  hd.of_eqs (Devm.pop_delSets_eq h).symm (Devm.pop_getCode h).symm

lemma Devm.NoDel.popToNat {wa : Adr} {d d' : Devm} {n : Nat}
    (hd : Devm.NoDel wa d) (h : Devm.popToNat d = .ok ⟨n, d'⟩) : Devm.NoDel wa d' :=
  hd.of_eqs (Devm.popToNat_delSets_eq h).symm (Devm.popToNat_getCode h).symm

lemma Devm.NoDel.popToAdr {wa : Adr} {d d' : Devm} {a : Adr}
    (hd : Devm.NoDel wa d) (h : Devm.popToAdr d = .ok ⟨a, d'⟩) : Devm.NoDel wa d' :=
  hd.of_eqs (Devm.popToAdr_delSets_eq h).symm (Devm.popToAdr_getCode h).symm

lemma Devm.NoDel.chargeGas {wa : Adr} {d d' : Devm} {cost : Nat}
    (hd : Devm.NoDel wa d) (h : chargeGas cost d = .ok d') : Devm.NoDel wa d' :=
  hd.of_eqs (chargeGas_delSets_eq h).symm (chargeGas_getCode h).symm

lemma Devm.NoDel.memExtends {wa : Adr} {d : Devm} {ranges : List (Nat × Nat)}
    (hd : Devm.NoDel wa d) : Devm.NoDel wa (d.memExtends ranges) := by
  refine hd.of_eqs ?_ Devm.memExtends_getCode.symm
  rfl

lemma Devm.NoDel.addAccessedAddress {wa : Adr} {d : Devm} {a : Adr}
    (hd : Devm.NoDel wa d) : Devm.NoDel wa (_root_.addAccessedAddress d a) := by
  refine hd.of_eqs ?_ addAccessedAddress_getCode.symm
  rfl

lemma Devm.NoDel.incrNonce {wa : Adr} {d : Devm} {a : Adr}
    (hd : Devm.NoDel wa d) : Devm.NoDel wa (d.incrNonce a) := by
  refine hd.of_eqs ?_ Devm.incrNonce_getCode.symm
  rfl

lemma Devm.NoDel.of_accessDelegation {wa : Adr} {d d' : Devm} {adr na : Adr}
    {dp : Bool} {code : ByteArray} {dagc : Nat}
    (hd : Devm.NoDel wa d)
    (h : (dp, na, code, dagc, d') = _root_.accessDelegation d adr) : Devm.NoDel wa d' := by
  have hd' : d' = (_root_.accessDelegation d adr).2.2.2.2 := congrArg (fun q => q.2.2.2.2) h
  refine hd.of_eqs ?_ ?_
  · rw [hd']; exact accessDelegation_delSets.symm
  · rw [hd']; exact accessDelegation_getCode.symm

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
  cases x
  case create =>
    dsimp only [Xinst.Run] at h
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨endowment, d1⟩, e1, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd (Devm.pop_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨mi, d2⟩, e2, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of (hnd.pop e1) (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨ms, d3⟩, e3, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((hnd.pop e1).popToNat e2) (Devm.popToNat_err_snd h_e)
    rcases h with ⟨extendCost, _, h⟩
    rcases h with ⟨initCodeCost, _, h⟩
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨d4, e4, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of (((hnd.pop e1).popToNat e2).popToNat e3)
        (chargeGas_err_snd h_e)
    rcases h with ⟨d5, h_d5, h⟩
    rcases h with ⟨newAddress, _, h⟩
    have hnd4 : Devm.NoDel wa d4 := (((hnd.pop e1).popToNat e2).popToNat e3).chargeGas e4
    have hnd5 : Devm.NoDel wa d5 := by rw [h_d5]; exact hnd4.memExtends
    exact GenericCreate.inv_noDel inv invc h hnd5
  case create2 =>
    dsimp only [Xinst.Run] at h
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨endowment, d1⟩, e1, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd (Devm.pop_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨mi, d2⟩, e2, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of (hnd.pop e1) (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨ms, d3⟩, e3, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((hnd.pop e1).popToNat e2) (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨salt, d4⟩, e4, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of (((hnd.pop e1).popToNat e2).popToNat e3)
        (Devm.pop_err_snd h_e)
    rcases h with ⟨extendCost, _, h⟩
    rcases h with ⟨initCodeHashCost, _, h⟩
    rcases h with ⟨initCodeCost, _, h⟩
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨d5, e5, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((((hnd.pop e1).popToNat e2).popToNat e3).pop e4)
        (chargeGas_err_snd h_e)
    rcases h with ⟨d6, h_d6, h⟩
    rcases h with ⟨newAddress, _, h⟩
    have hnd5 : Devm.NoDel wa d5 :=
      ((((hnd.pop e1).popToNat e2).popToNat e3).pop e4).chargeGas e5
    have hnd6 : Devm.NoDel wa d6 := by rw [h_d6]; exact hnd5.memExtends
    exact GenericCreate.inv_noDel inv invc h hnd6
  case call =>
    dsimp only [Xinst.Run] at h
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨gas, d1⟩, e1, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd (Devm.pop_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨callee, d2⟩, e2, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of (hnd.pop e1) (Devm.popToAdr_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨value, d3⟩, e3, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((hnd.pop e1).popToAdr e2) (Devm.pop_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨ii, d4⟩, e4, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of (((hnd.pop e1).popToAdr e2).pop e3)
        (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨is, d5⟩, e5, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((((hnd.pop e1).popToAdr e2).pop e3).popToNat e4)
        (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨oi, d6⟩, e6, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of
        (((((hnd.pop e1).popToAdr e2).pop e3).popToNat e4).popToNat e5)
        (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨os, d7⟩, e7, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of
        ((((((hnd.pop e1).popToAdr e2).pop e3).popToNat e4).popToNat e5).popToNat e6)
        (Devm.popToNat_err_snd h_e)
    have hnd7 : Devm.NoDel wa d7 :=
      ((((((hnd.pop e1).popToAdr e2).pop e3).popToNat e4).popToNat e5).popToNat e6).popToNat e7
    rcases h with ⟨extendCost, _, h⟩
    rcases h with ⟨preAccessCost, _, h⟩
    rcases h with ⟨d8, h_d8, h⟩
    have hnd8 : Devm.NoDel wa d8 := by rw [h_d8]; exact hnd7.addAccessedAddress
    rcases h with ⟨⟨dp, na, code0, dagc, d9⟩, h_d9, h⟩
    have hnd9 : Devm.NoDel wa d9 := hnd8.of_accessDelegation h_d9
    rcases h with ⟨accessCost, _, h⟩
    rcases h with ⟨createCost, _, h⟩
    rcases h with ⟨transferCost, _, h⟩
    rcases h with ⟨⟨mcc, mcs⟩, _, h⟩
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨d10, e10, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd9 (chargeGas_err_snd h_e)
    have hnd10 : Devm.NoDel wa d10 := hnd9.chargeGas e10
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨_, _, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd10 (Except.assert_err_snd h_e)
    rcases h with ⟨d11, h_d11, h⟩
    have hnd11 : Devm.NoDel wa d11 := by rw [h_d11]; exact hnd10.memExtends
    rcases h with ⟨senderBal, _, h⟩
    split_ifs at h with h_lt
    · rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨d12, e12, h⟩
      · rw [h_ex]; exact Devm.push_noDel h_e hnd11
      · rcases h with ⟨_, h_ex⟩
        rw [← h_ex]
        exact Devm.NoDel.of_eqs (d := d12)
          (d' := (d12.withReturnData []).withGasLeft (d12.gasLeft + mcs))
          rfl rfl (Devm.push_noDel e12 hnd11)
    · exact GenericCall.inv_noDel inv invc h hnd11
  case callcode =>
    dsimp only [Xinst.Run] at h
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨gas, d1⟩, e1, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd (Devm.pop_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨codeAddress, d2⟩, e2, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of (hnd.pop e1) (Devm.popToAdr_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨value, d3⟩, e3, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((hnd.pop e1).popToAdr e2) (Devm.pop_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨ii, d4⟩, e4, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of (((hnd.pop e1).popToAdr e2).pop e3)
        (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨is, d5⟩, e5, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((((hnd.pop e1).popToAdr e2).pop e3).popToNat e4)
        (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨oi, d6⟩, e6, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of
        (((((hnd.pop e1).popToAdr e2).pop e3).popToNat e4).popToNat e5)
        (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨os, d7⟩, e7, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of
        ((((((hnd.pop e1).popToAdr e2).pop e3).popToNat e4).popToNat e5).popToNat e6)
        (Devm.popToNat_err_snd h_e)
    have hnd7 : Devm.NoDel wa d7 :=
      ((((((hnd.pop e1).popToAdr e2).pop e3).popToNat e4).popToNat e5).popToNat e6).popToNat e7
    rcases h with ⟨extendCost, _, h⟩
    rcases h with ⟨preAccessCost, _, h⟩
    rcases h with ⟨d8, h_d8, h⟩
    have hnd8 : Devm.NoDel wa d8 := by rw [h_d8]; exact hnd7.addAccessedAddress
    rcases h with ⟨⟨dp, newCodeAddress, code0, dagc, d9⟩, h_d9, h⟩
    have hnd9 : Devm.NoDel wa d9 := hnd8.of_accessDelegation h_d9
    rcases h with ⟨accessCost, _, h⟩
    rcases h with ⟨transferCost, _, h⟩
    rcases h with ⟨⟨mcc, mcs⟩, _, h⟩
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨d10, e10, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd9 (chargeGas_err_snd h_e)
    have hnd10 : Devm.NoDel wa d10 := hnd9.chargeGas e10
    rcases h with ⟨d11, h_d11, h⟩
    have hnd11 : Devm.NoDel wa d11 := by rw [h_d11]; exact hnd10.memExtends
    rcases h with ⟨senderBal, _, h⟩
    split_ifs at h with h_lt
    · rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨d12, e12, h⟩
      · rw [h_ex]; exact Devm.push_noDel h_e hnd11
      · rcases h with ⟨_, h_ex⟩
        rw [← h_ex]
        exact Devm.NoDel.of_eqs (d := d12)
          (d' := (d12.withReturnData []).withGasLeft (d12.gasLeft + mcs))
          rfl rfl (Devm.push_noDel e12 hnd11)
    · exact GenericCall.inv_noDel inv invc h hnd11
  case delcall =>
    dsimp only [Xinst.Run] at h
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨gas, d1⟩, e1, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd (Devm.pop_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨codeAddress, d2⟩, e2, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of (hnd.pop e1) (Devm.popToAdr_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨ii, d3⟩, e3, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((hnd.pop e1).popToAdr e2) (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨is, d4⟩, e4, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of (((hnd.pop e1).popToAdr e2).popToNat e3)
        (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨oi, d5⟩, e5, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((((hnd.pop e1).popToAdr e2).popToNat e3).popToNat e4)
        (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨os, d6⟩, e6, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of
        (((((hnd.pop e1).popToAdr e2).popToNat e3).popToNat e4).popToNat e5)
        (Devm.popToNat_err_snd h_e)
    have hnd6 : Devm.NoDel wa d6 :=
      (((((hnd.pop e1).popToAdr e2).popToNat e3).popToNat e4).popToNat e5).popToNat e6
    rcases h with ⟨extendCost, _, h⟩
    rcases h with ⟨preAccessCost, _, h⟩
    rcases h with ⟨d7, h_d7, h⟩
    have hnd7 : Devm.NoDel wa d7 := by rw [h_d7]; exact hnd6.addAccessedAddress
    rcases h with ⟨⟨dp, newCodeAddress, code0, dagc, d8⟩, h_d8, h⟩
    have hnd8 : Devm.NoDel wa d8 := hnd7.of_accessDelegation h_d8
    rcases h with ⟨accessCost, _, h⟩
    rcases h with ⟨⟨mcc, mcs⟩, _, h⟩
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨d9, e9, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd8 (chargeGas_err_snd h_e)
    have hnd9 : Devm.NoDel wa d9 := hnd8.chargeGas e9
    rcases h with ⟨d10, h_d10, h⟩
    have hnd10 : Devm.NoDel wa d10 := by rw [h_d10]; exact hnd9.memExtends
    exact GenericCall.inv_noDel inv invc h hnd10
  case statcall =>
    dsimp only [Xinst.Run] at h
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨gas, d1⟩, e1, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd (Devm.pop_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨target, d2⟩, e2, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of (hnd.pop e1) (Devm.popToAdr_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨ii, d3⟩, e3, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((hnd.pop e1).popToAdr e2) (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨is, d4⟩, e4, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of (((hnd.pop e1).popToAdr e2).popToNat e3)
        (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨oi, d5⟩, e5, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((((hnd.pop e1).popToAdr e2).popToNat e3).popToNat e4)
        (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨os, d6⟩, e6, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of
        (((((hnd.pop e1).popToAdr e2).popToNat e3).popToNat e4).popToNat e5)
        (Devm.popToNat_err_snd h_e)
    have hnd6 : Devm.NoDel wa d6 :=
      (((((hnd.pop e1).popToAdr e2).popToNat e3).popToNat e4).popToNat e5).popToNat e6
    rcases h with ⟨extendCost, _, h⟩
    rcases h with ⟨preAccessCost, _, h⟩
    rcases h with ⟨d7, h_d7, h⟩
    have hnd7 : Devm.NoDel wa d7 := by rw [h_d7]; exact hnd6.addAccessedAddress
    rcases h with ⟨⟨dp, newCodeAddress, code0, dagc, d8⟩, h_d8, h⟩
    have hnd8 : Devm.NoDel wa d8 := hnd7.of_accessDelegation h_d8
    rcases h with ⟨accessCost, _, h⟩
    rcases h with ⟨⟨mcc, mcs⟩, _, h⟩
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨d9, e9, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd8 (chargeGas_err_snd h_e)
    have hnd9 : Devm.NoDel wa d9 := hnd8.chargeGas e9
    rcases h with ⟨d10, h_d10, h⟩
    have hnd10 : Devm.NoDel wa d10 := by rw [h_d10]; exact hnd9.memExtends
    exact GenericCall.inv_noDel inv invc h hnd10

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
  cases n with
  | push xs le =>
    cases xl with
    | none =>
      dsimp only [Ninst.Run'] at run
      rw [← run]
      cases h_charge : chargeGas (if xs = [] then gBase else gVerylow) devm
      case error err =>
        exact Devm.NoDel.of_eqs (chargeGas_delSets_err h_charge).symm (chargeGas_getCode_err h_charge wa).symm h
      case ok d1 =>
        have h1 : Devm.NoDel wa d1 := Devm.NoDel.of_eqs (chargeGas_delSets_eq h_charge).symm (chargeGas_getCode_eq h_charge wa).symm h
        dsimp only [bind, Except.bind]
        cases h_push : Devm.push xs.toB256 d1
        case error err2 =>
          exact Devm.NoDel.of_eqs (Devm.push_delSets_err h_push).symm (Devm.push_getCode_err h_push wa).symm h1
        case ok d2 =>
          exact Devm.NoDel.of_eqs (Devm.push_delSets_eq h_push).symm (Devm.push_getCode_eq h_push wa).symm h1
    | some y => dsimp only [Ninst.Run'] at run
  | reg rg =>
    cases xl with
    | none =>
      dsimp only [Ninst.Run'] at run
      rw [← run]
      cases h_run : Rinst.run { pc := pc, sta := sevm, dyna := devm } rg
      case error err =>
        exact Devm.NoDel.of_eqs (Rinst.inv_delSets_err h_run).symm (Rinst.inv_getCode_err h_run wa).symm h
      case ok d1 =>
        exact Devm.NoDel.of_eqs (Rinst.inv_delSets h_run) (Rinst.inv_getCode h_run wa).symm h
    | some y => dsimp only [Ninst.Run'] at run
  | exec xinst =>
    dsimp only [Ninst.Run'] at run
    exact Xinst.inv_noDel_gen inv invc run h

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
  cases exn
  · dsimp [executeCode.handleError] at h
    split at h
    · next h_halt =>
      intro h_lim
      simp only [Except.Lim, Except.toError?, Option.some.injEq] at h_lim
      rw [h_lim] at h_halt
      revert h_halt
      decide
    · split at h
      · next h_rev =>
        intro h_lim
        simp only [Except.Lim, Except.toError?, Option.some.injEq] at h_lim
        rw [h_lim] at h_rev
        revert h_rev
        decide
      · contradiction
  · intro h_lim
    cases h_lim

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
