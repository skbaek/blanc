-- CommonProofs/NoDel.lean : no-deletion and account-set preservation laws.

import Blanc.CommonProofs.Frames

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat
open Jaune.Ninst Ninst
open DispatchTree

/-! ## §1 AdrSet non-membership helpers -/

namespace AdrSet


theorem not_mem_union {a : Adr} {m₁ m₂ : AdrSet} (h₁ : a ∉ m₁) (h₂ : a ∉ m₂) :
    a ∉ m₁.union m₂ := by
  intro h
  have hm : a ∈ m₁ ∨ a ∈ m₂ := Std.HashSet.mem_union_iff.mp h
  exact hm.elim h₁ h₂

theorem not_mem_empty {a : Adr} {c : Nat} :
    a ∉ (Std.HashSet.emptyWithCapacity c : AdrSet) := by
  simp only [Std.HashSet.not_mem_emptyWithCapacity, not_false_eq_true]

end AdrSet

/-! ## §2 The NoDel invariant -/

-- rfl-bridge between the Devm-level and State-level code projections.
-- The frame-level invariant. The `code` conjunct is the fuel for the
-- CREATE collision guards; it is transported by the PROVED getCode ladder,
-- never re-proved here.
structure Devm.NoDel (wa : Adr) (d : Devm) : Prop where
  (atd  : wa ∉ d.accountsToDelete)
  (ca   : wa ∉ d.createdAccounts)
  (code : (d.getCode wa).toList ≠ [])

-- The message-level invariant constrains the created-account set and code.
-- initDevm also inherits msg.inheritedDeletions; its precise exclusion is a
-- separate premise at the message-to-machine boundary.
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
    Except (EvmError × State × AdrSet × Tra) Devm → Prop
  | .ok d => Devm.NoDel wa d
  | .error ⟨_, st, ca, _⟩ => wa ∉ ca ∧ (st.getCode wa).toList ≠ []

-- The sub-execution oracle invariant threaded through the Exec induction
-- (result-shaped like Xlot.InvGetCode, Common.lean:4076; the former
-- Xlot.InvNof mirror in Solvent.lean was replaced by Exec.balance_effect).
def Xlot.InvNoDel (wa : Adr) : Xlot → Prop
  | .none => True
  | .some ⟨evm_, exn_⟩ => Devm.NoDel wa evm_.dyna → Execution.NoDel wa exn_

/-! ## §3 Proved transports -/

-- Transport NoDel across a step that moves neither set nor wa's code.
lemma Devm.NoDel.of_eqs {wa : Adr} {d d' : Devm}
    (hs : Devm.delSets d = Devm.delSets d') (hc : d.getCode wa = d'.getCode wa)
    (h : Devm.NoDel wa d) : Devm.NoDel wa d' := by
  have h1 : d.accountsToDelete = d'.accountsToDelete := congrArg Prod.fst hs
  have h2 : d.createdAccounts = d'.createdAccounts := congrArg Prod.snd hs
  exact ⟨h1 ▸ h.atd, h2 ▸ h.ca, hc ▸ h.code⟩

-- A fresh frame inherits its deletion set and the message state/created set.
lemma Msg.NoDel.initDevm {wa : Adr} {msg : Msg}
    (h : Msg.NoDel wa msg) (h_atd : wa ∉ msg.inheritedDeletions) :
    Devm.NoDel wa (initDevm msg) :=
  ⟨h_atd, h.ca, h.code⟩

-- Rollback keeps atd/ca and installs the given state.
lemma Devm.NoDel.rollback {wa : Adr} {d : Devm} {st : State} {tra : Tra}
    (h_atd : wa ∉ d.accountsToDelete) (h_ca : wa ∉ d.createdAccounts)
    (h_code : (st.getCode wa).toList ≠ []) :
    Devm.NoDel wa (d.rollback st tra) :=
  ⟨h_atd, h_ca, h_code⟩

-- handleError shuffles error payloads into ok results without touching
-- the sets (jaune Execution.lean:2692-2701).
lemma handleError_noDel {wa : Adr} {sg : Option StateGasRules} {exn : Execution}
    (h : Execution.NoDel wa exn) :
    MsgResult.NoDel wa (executeCode.handleErrorWith sg exn) := by
  cases sg <;> simp only [executeCode.handleErrorWith]
  · cases exn with
    | ok d => exact h
    | error p =>
      rcases p with ⟨err, d⟩
      have hd : Devm.NoDel wa d := h
      cases err <;>
        first
          | exact ⟨hd.atd, hd.ca, hd.code⟩
          | exact ⟨hd.ca, hd.code⟩
  · cases exn with
    | ok d => exact h
    | error p =>
      rcases p with ⟨err, d⟩
      have hd : Devm.NoDel wa d := h
      cases err <;>
        first
          | exact ⟨hd.atd, hd.ca, hd.code⟩
          | exact ⟨hd.ca, hd.code⟩

/-! ## §4 Plumbing -/

-- The create-guard bridge: an address whose account has size-0 code cannot be the code-bearing wa.
lemma ne_wa_of_code_size_zero {st : State} {wa b : Adr}
    (hwa : (st.getCode wa).toList ≠ []) (hb : (st.get b).code.size = 0) :
    b ≠ wa := by
  intro h
  subst h
  have h_empty : (st.get b).code.toList = [] := by
    unfold ByteArray.toList
    unfold ByteArray.toList.loop
    simp only [hb, lt_self_iff_false, ↓reduceIte, reverse_nil]
  unfold State.getCode at hwa
  rw [h_empty] at hwa
  exact hwa rfl

/-! ## Protected accounts (Jaune `setAccount` normalization)

An emptied account is deleted together with its storage; an account with a
nonzero nonce or nonempty code is never emptied by a balance, nonce or code
write. -/

/-- The successor of a nonce below `UInt64.max` is nonzero. -/
lemma UInt64.add_one_ne_zero_of_ne_max {n : UInt64} (h : n ≠ UInt64.max) : n + 1 ≠ 0 := by
  intro h1
  apply h
  calc n = n + 1 - 1 := (UInt64.add_sub_cancel n 1).symm
    _ = 0 - 1 := by rw [h1]
    _ = UInt64.max := by decide

/-- A balance write keeps every account's nonce. -/
lemma State.setBal_get_nonce {st : Jaune.State} {b a : Adr} {v : B256} :
    ((st.setBal b v).get a).nonce = (st.get a).nonce := by
  by_cases h : b = a
  · subst h; rw [State.setBal_get_self, Acct.clearIfEmpty_nonce]; rfl
  · rw [State.setBal_get_ne h]

/-- An account that is not empty survives `setAccount` normalization unchanged. -/
theorem Acct.clearIfEmpty_of_not_empty {ac : Acct} (h : ¬ ac.Empty) : ac.clearIfEmpty = ac := by
  unfold Acct.clearIfEmpty
  rw [ite_eq_right h]

/-- A balance write keeps the nonce. -/
theorem Acct.withBal_nonce (ac : Acct) (b : B256) : (ac.withBal b).nonce = ac.nonce := rfl

/-- A balance write keeps the code. -/
theorem Acct.withBal_code (ac : Acct) (b : B256) : (ac.withBal b).code = ac.code := rfl

/-- Normalization leaves a balance write alone at an account with code.

Stated on `ac.withBal b` so callers rewrite instead of closing the normalization branch
with `exact h hEmpty.1`: that asks the unifier for `(ac.withBal b).code = ac.code`, which
it first tries as `ac.withBal b =?= ac`. At a concrete credit such as
`bal + (2 ^ 245).toB256` that check unfolds literal word arithmetic and can exhaust a
16 GiB build scope. -/
theorem Acct.clearIfEmpty_withBal_of_code {ac : Acct} {b : B256} (h : ac.code.size ≠ 0) :
    (ac.withBal b).clearIfEmpty = ac.withBal b := by
  unfold Acct.clearIfEmpty
  split
  · rename_i hE
    have hc : (ac.withBal b).code.size = 0 := hE.1
    rw [Acct.withBal_code] at hc
    exact (h hc).elim
  · rfl

/-- Normalization leaves a balance write alone at an account with a nonzero nonce. -/
theorem Acct.clearIfEmpty_withBal_of_nonce {ac : Acct} {b : B256} (h : ac.nonce ≠ 0) :
    (ac.withBal b).clearIfEmpty = ac.withBal b := by
  unfold Acct.clearIfEmpty
  split
  · rename_i hE
    have hn : (ac.withBal b).nonce = 0 := hE.2.1
    rw [Acct.withBal_nonce] at hn
    exact (h hn).elim
  · rfl

/-- `setAccount` normalization is the identity on an account whose code is a
nonempty byte list. -/
theorem Acct.clearIfEmpty_of_code_toList_ne_nil (ac : Acct) (h : ac.code.toList ≠ []) :
    ac.clearIfEmpty = ac := by
  have hne : ¬ ac.Empty := by
    rintro ⟨hsize, _, _⟩
    apply h
    have hlen : ac.code.toList.length = 0 := by
      rw [ByteArray.toList_eq_toList_data, Array.length_toList]
      exact hsize
    exact List.length_eq_zero_iff.mp hlen
  unfold Acct.clearIfEmpty
  simp only [hne, ↓reduceIte]

/-- An account is *protected* when it has a nonzero nonce or nonempty code: no
balance write can empty it, so no balance write can wipe its storage. -/
def State.Protected (st : Jaune.State) (a : Adr) : Prop :=
  (st.get a).nonce ≠ 0 ∨ (st.get a).code.size ≠ 0

/-- An account whose code is a nonempty byte list is protected. -/
lemma State.Protected.of_code_ne_nil {st : Jaune.State} {a : Adr}
    (h : (st.getCode a).toList ≠ []) : State.Protected st a := by
  right
  intro hz
  exact (ne_wa_of_code_size_zero h hz) rfl

/-- An account carrying a code image is protected: an image is nonempty. -/
lemma State.Protected.of_image {st : Jaune.State} {a : Adr} {sem : CodeSem}
    (h : some (st.getCode a).toList = sem.image) : State.Protected st a :=
  State.Protected.of_code_ne_nil (sem.ne_nil h.symm)

/-- An account carrying a compiled program is protected: a compiled image is nonempty. -/
theorem State.Protected.of_compile {st : State} {a : Adr} {p : Prog}
    (h : some (st.getCode a).toList = Prog.compile p) : State.Protected st a :=
  State.Protected.of_code_ne_nil fun hnil => Prog.compile_ne_nil (by rw [← h, hnil])

/-- Protection survives a balance write. -/
lemma State.Protected.setBal {st : Jaune.State} {a : Adr} (hp : State.Protected st a)
    (b : Adr) (v : B256) : State.Protected (st.setBal b v) a := by
  unfold State.Protected at hp ⊢
  rw [State.setBal_get_nonce, State.setBal_get_code]
  exact hp

/-- A balance write leaves a protected account's storage alone. Unprotected
accounts are the storage-only ones a balance write may delete. -/
lemma State.setBal_get_stor_of_protected {st : Jaune.State} {b a : Adr} {v : B256}
    (hp : State.Protected st a) : ((st.setBal b v).get a).stor = (st.get a).stor := by
  rw [State.setBal_get_stor]
  split_ifs with h
  · obtain ⟨rfl, hE⟩ := h
    exfalso
    rcases hp with hn | hc
    · exact hn hE.2.1
    · exact hc hE.1
  · rfl

open Std.DTreeMap.Internal in
/-- Inserting a key at its current value returns the identical balanced raw
tree: an exact representation identity, not extensional tree equivalence. -/
theorem treeMapImpl_insert_same {α β : Type} [Ord α] [Std.LawfulEqOrd α]
    (tree : Impl α (fun _ => β)) (balanced : tree.Balanced) (key : α) (value : β)
    (found : Impl.Const.get? tree key = some value) :
    (Impl.insert key value tree balanced).impl = tree := by
  induction tree with
  | leaf => simp only [Impl.Const.get?] at found; cases found
  | inner size k v left right ihLeft ihRight =>
      cases compared : compare key k with
      | lt =>
          simp only [Impl.Const.get?, compared] at found
          simp only [Impl.insert, compared]
          simp only [ihLeft balanced.left found, Impl.balanceL_eq_balance,
            Impl.balance_eq_inner balanced]
      | gt =>
          simp only [Impl.Const.get?, compared] at found
          simp only [Impl.insert, compared]
          simp only [ihRight balanced.right found, Impl.balanceR_eq_balance,
            Impl.balance_eq_inner balanced]
      | eq =>
          have same : key = k := Std.LawfulEqOrd.eq_of_compare compared
          subst k
          simp only [Impl.Const.get?, compared, Option.some.injEq] at found
          subst value
          simp only [Impl.insert, compared]

/-- Inserting a key at its current value returns the identical `TreeMap`. -/
theorem treeMap_insert_same {α β : Type} [Ord α] [Std.LawfulEqOrd α]
    (tree : Std.TreeMap α β) (key : α) (value : β)
    (found : tree[key]? = some value) : tree.insert key value = tree := by
  cases tree with
  | mk inner =>
      cases inner with
      | mk raw wf =>
          change Std.DTreeMap.Internal.Impl.Const.get? raw key = some value at found
          simp only [Std.TreeMap.insert, Std.DTreeMap.insert,
            treeMapImpl_insert_same raw wf.balanced key value found]

/-- Rewriting a protected account's current balance is the identity on the raw
world tree: protection rules out the `clearIfEmpty` normalization. -/
theorem State.setBal_current_of_protected {state : State} {owner : Adr}
    (hp : State.Protected state owner) :
    state.setBal owner (state.bal owner) = state := by
  have notEmpty : ¬ (state.get owner).Empty := by
    intro empty
    rcases hp with nonce | code
    · exact nonce empty.2.1
    · exact code empty.1
  have notNil : state.get owner ≠ Acct.nil := by
    intro nil
    apply notEmpty
    rw [nil]
    exact ⟨rfl, rfl, rfl⟩
  have found : state[owner]? = some (state.get owner) := by
    cases lookup : state[owner]? with
    | none =>
        have nil : state.get owner = Acct.nil := by
          rw [State.get_eq_getD, lookup]
          rfl
        exact (notNil nil).elim
    | some account =>
        rw [State.get_eq_getD, lookup]
        rfl
  have unchanged : (state.get owner).withBal (state.bal owner) = state.get owner := by
    unfold State.bal
    cases state.get owner
    rfl
  unfold State.setBal
  rw [unchanged]
  unfold State.setAccount
  rw [Acct.clearIfEmpty, ite_eq_right notEmpty]
  unfold State.set
  rw [ite_eq_right notNil]
  exact treeMap_insert_same state owner (state.get owner) found

/-- A zero credit to a protected account is the identity on the world. -/
theorem State.addBal_zero_of_protected {state : State} {owner : Adr}
    (hp : State.Protected state owner) : state.addBal owner 0 = state := by
  unfold State.addBal
  rw [B256.add_zero]
  exact State.setBal_current_of_protected hp

/-- A zero debit from a protected account succeeds with the identical world. -/
theorem State.subBal_zero_of_protected {state : State} {owner : Adr}
    (hp : State.Protected state owner) : state.subBal owner 0 = some state := by
  unfold State.subBal
  simp only [B256.lt_iff_toNat_lt_toNat, B256.toNat_zero, Nat.not_lt_zero, ite_false, B256.sub_zero,
    State.setBal_current_of_protected hp]

/-- Beneficiary credit keeps protected storage in either account-presence regime. -/
lemma Devm.creditBeneficiary_getStor_of_protected (rules : ForkRules) (donee : Adr)
    (value : B256) (d : Devm) (a : Adr) (hp : State.Protected d.state a) :
    (d.creditBeneficiary rules donee value).getStor a = d.getStor a := by
  unfold Devm.creditBeneficiary
  split
  · exact State.setBal_get_stor_of_protected hp
  · change ((d.state.setPresent donee
      ((d.state.get donee).withBal (d.state.bal donee + value))).get a).stor = (d.state.get a).stor
    by_cases h : donee = a
    · subst a; rw [State.get_setPresent_self]; rfl
    · rw [State.get_setPresent_ne _ h]

lemma State.Protected.creditBeneficiary {d : Devm} {a : Adr}
    (hp : State.Protected d.state a) (rules : ForkRules) (donee : Adr) (value : B256) :
    State.Protected (d.creditBeneficiary rules donee value).state a := by
  unfold Devm.creditBeneficiary
  split
  · exact hp.setBal donee _
  · change State.Protected (d.state.setPresent donee _) a
    unfold State.Protected at hp ⊢
    by_cases h : donee = a
    · subst a; rw [State.get_setPresent_self]; exact hp
    · rw [State.get_setPresent_ne _ h]; exact hp

/-- Message entry that moves no value — no transfer flag, or a zero value —
leaves the block environment exactly as it was. -/
lemma benvAfterTransfer_eq_of_not_transfer {msg : Msg} {entry : Benv}
    (h : ¬ (msg.shouldTransferValue = true ∧ msg.value ≠ 0))
    (transfer : msg.benvAfterTransfer = .ok entry) : entry = msg.benv := by
  by_cases hs : msg.shouldTransferValue = true
  · have hz : msg.value = 0 := by
      by_contra hne
      exact h ⟨hs, hne⟩
    rw [Msg.benvAfterTransfer_of_value_zero hz] at transfer
    exact (Except.ok.inj transfer).symm
  · exact of_benvAfterTransfer_no hs transfer

/-- A full-balance self-payment empties a codeless, nonce-zero account, so
Jaune `ca9f27d` deletes it with its storage at message entry. This is why a
storage-preservation statement across message entry needs zero value or a
`State.Protected` owner. -/
theorem selfPayment_entry_clears_storage {msg : Msg} {entry : Benv}
    (transfers : msg.shouldTransferValue = true)
    (self : msg.caller = msg.currentTarget) (nonzero : msg.value ≠ 0)
    (hnonce : (msg.benv.state.get msg.caller).nonce = 0)
    (hcode : (msg.benv.state.get msg.caller).code.size = 0)
    (hbal : (msg.benv.state.get msg.caller).bal = msg.value)
    (transfer : msg.benvAfterTransfer = .ok entry) :
    entry.state.getStor msg.currentTarget = Stor.empty := by
  obtain ⟨debited, debit, entryEq⟩ := of_benvAfterTransfer transfers nonzero transfer
  have entryState : entry.state = debited.addBal msg.currentTarget msg.value := by
    rw [entryEq]
    rfl
  rw [entryState, ← self]
  unfold State.subBal at debit
  rw [ite_eq_right (by unfold State.bal; rw [hbal]; exact lt_irrefl _)] at debit
  cases debit
  unfold State.addBal State.getStor
  rw [State.setBal_get_stor]
  split
  · rfl
  · rw [State.setBal_get_stor, ite_eq_left]
    refine ⟨rfl, hcode, hnonce, ?_⟩
    unfold State.bal
    rw [hbal]
    exact B256.sub_self _

-- Same bridge via the collision predicate used by `processMessageCall.create`.
lemma ne_wa_of_not_hasCodeOrNonce {st : State} {wa ct : Adr}
    (hwa : (st.getCode wa).toList ≠ [])
    (h : accountHasCodeOrNonce st ct = false) : ct ≠ wa := by
  intro heq
  subst heq
  unfold accountHasCodeOrNonce at h
  rw [Bool.or_eq_false_iff] at h
  have h_empty_not := h.2
  have h_empty : (st.getCode ct).isEmpty = true := by
    simp only [Bool.not_eq_eq_eq_not, Bool.not_false] at h_empty_not
    exact h_empty_not
  have hb : (st.getCode ct).size = 0 := by
    unfold ByteArray.isEmpty at h_empty
    simp only [beq_iff_eq, ByteArray.size_eq_zero_iff] at h_empty
    simpa only [ByteArray.size_eq_zero_iff, ByteArray.size_empty] using
      congrArg ByteArray.size h_empty
  have h_empty_list : (st.getCode ct).toList = [] := by
    unfold ByteArray.toList
    unfold ByteArray.toList.loop
    simp only [hb, lt_self_iff_false, ↓reduceIte, reverse_nil]
  rw [h_empty_list] at hwa
  exact hwa rfl

-- The create-seeding step: wa ∉ msg.benv.createdAccounts and code is untouched.
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
      rw [State.setAccount_get_ne _ h_ct]
      split
      · exact State.get_setPresent_ne _ h_ct _
      · exact State.get_set_ne _ h_ct _
    show (((msg.benv.state.setStor msg.currentTarget .empty).incrNonce msg.currentTarget).get wa).code.toList ≠ []
    rw [h_get]
    exact hcode

-- Precompiles never touch the sets or code.
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

/-! ## §5 Instruction level -/

-- Helper lemmas for the EVM instructions delSets preservation.
lemma liftMach_delSets_of_ok {core : Mach → Footprint.Outcome Mach α}
    {d d' : Devm} {x : α} (h : liftMach core d = .ok (x, d')) :
    Devm.delSets d' = Devm.delSets d := by
  unfold liftMach Footprint.liftOutcome at h
  cases hc : core d.mach with
  | error err => simp only [hc, reduceCtorEq] at h
  | ok out =>
    simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    rfl

lemma liftMach_delSets_of_error {core : Mach → Footprint.Outcome Mach α}
    {d : Devm} {err : EvmError × Devm} (h : liftMach core d = .error err) :
    Devm.delSets err.2 = Devm.delSets d := by
  unfold liftMach Footprint.liftOutcome at h
  cases hc : core d.mach with
  | error out =>
    simp only [hc, Except.error.injEq] at h
    rcases h with ⟨_, rfl⟩
    rfl
  | ok out => simp only [hc, reduceCtorEq] at h

lemma liftMachExecution_delSets_of_ok {core : Mach → Footprint.Outcome Mach Unit}
    {d d' : Devm} (h : liftMachExecution core d = .ok d') :
    Devm.delSets d' = Devm.delSets d := by
  unfold liftMachExecution Footprint.toExecution at h
  split at h
  · cases h
  · rename_i out heq
    cases h
    exact liftMach_delSets_of_ok heq

lemma liftMachExecution_delSets_of_error {core : Mach → Footprint.Outcome Mach Unit}
    {d : Devm} {err : EvmError × Devm} (h : liftMachExecution core d = .error err) :
    Devm.delSets err.2 = Devm.delSets d := by
  unfold liftMachExecution Footprint.toExecution at h
  split at h
  · rename_i e heq
    cases h
    exact liftMach_delSets_of_error heq
  · cases h

lemma Devm.pop_delSets_eq {x devm devm'} (h : Devm.pop devm = .ok ⟨x, devm'⟩) : Devm.delSets devm' = Devm.delSets devm := by
  simp only [Devm.pop_def] at h
  split at h <;> try contradiction
  cases h; rfl

lemma chargeGas_delSets_eq {cost devm devm'} (h : chargeGas cost devm = .ok devm') : Devm.delSets devm' = Devm.delSets devm := by
  simp only [chargeGas_def] at h
  split at h <;> try contradiction
  cases h; rfl

lemma Devm.push_delSets_eq {v devm devm'} (h : Devm.push v devm = .ok devm') : Devm.delSets devm' = Devm.delSets devm := by
  exact liftMachExecution_delSets_of_ok (core := Mach.push v) h

lemma Devm.popToAdr_delSets_eq {devm devm' adr} (h : Devm.popToAdr devm = .ok ⟨adr, devm'⟩) : Devm.delSets devm' = Devm.delSets devm := by
  exact liftMach_delSets_of_ok (core := Mach.popToAdr) h

lemma Devm.popToNat_delSets_eq {devm devm' n} (h : Devm.popToNat devm = .ok ⟨n, devm'⟩) : Devm.delSets devm' = Devm.delSets devm := by
  exact liftMach_delSets_of_ok (core := Mach.popToNat) h

lemma Rinst.inv_delSets {r : Rinst} : Rinst.Inv Devm.delSets r := by
  intro pc sevm pre post hrun
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc pre sevm; rw [hrun] at hf
    exact Prod.ext hf.accountsToDelete hf.createdAccounts
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc pre sevm; rw [hrun] at hf
    exact Prod.ext hf.accountsToDelete hf.createdAccounts
  · have hf := Rinst.run_instructionFrame pc sevm pre r hs ht; rw [hrun] at hf; exact Devm.InstructionFrame.delSets hf

lemma chargeGas_delSets_err {cost devm err} (h : chargeGas cost devm = .error err) : Devm.delSets err.2 = Devm.delSets devm := by
  simp only [chargeGas_def] at h
  split at h <;> try contradiction
  cases h; rfl

lemma chargeStateGas_delSets_eq {amount devm devm'} (h : chargeStateGas amount devm = .ok devm') : Devm.delSets devm' = Devm.delSets devm := by
  exact liftMachExecution_delSets_of_ok (core := Mach.chargeStateGas amount) h

lemma chargeStateGas_delSets_err {amount devm err} (h : chargeStateGas amount devm = .error err) : Devm.delSets err.2 = Devm.delSets devm := by
  exact liftMachExecution_delSets_of_error (core := Mach.chargeStateGas amount) h

lemma Devm.push_delSets_err {v devm err} (h : Devm.push v devm = Except.error err) : Devm.delSets err.2 = Devm.delSets devm := by
  exact liftMachExecution_delSets_of_error (core := Mach.push v) h

lemma Devm.popToAdr_delSets_err {devm err} (h : Devm.popToAdr devm = .error err) : Devm.delSets err.2 = Devm.delSets devm := by
  exact liftMach_delSets_of_error (core := Mach.popToAdr) h

-- Rinst execution preserves delSets on error results.
lemma Rinst.inv_delSets_err {pc : Nat} {sevm : Sevm} {devm : Devm} {r : Rinst}
    {err : EvmError} {devm' : Devm}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = .error ⟨err, devm'⟩) :
    Devm.delSets devm' = Devm.delSets devm := by
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc devm sevm; rw [run] at hf
    exact (Prod.ext (by change devm.accountsToDelete = devm'.accountsToDelete; exact hf.accountsToDelete) (by change devm.createdAccounts = devm'.createdAccounts; exact hf.createdAccounts)).symm
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc devm sevm; rw [run] at hf
    exact (Prod.ext (by change devm.accountsToDelete = devm'.accountsToDelete; exact hf.accountsToDelete) (by change devm.createdAccounts = devm'.createdAccounts; exact hf.createdAccounts)).symm
  · have hf := Rinst.run_instructionFrame pc sevm devm r hs ht; rw [run] at hf
    exact (Devm.InstructionFrame.delSets hf).symm

lemma Jinst.inv_delSets {pc : Nat} {sevm : Sevm} {devm : Devm} {j : Jinst}
    {pc' : Nat} {devm' : Devm}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j (.ok ⟨pc', devm'⟩)) :
    Devm.delSets devm' = Devm.delSets devm := by
  have hf := Jinst.run_instructionFrame ⟨pc, sevm, devm⟩ j
  rw [run] at hf
  exact (Devm.InstructionFrame.delSets hf).symm

lemma Jinst.inv_delSets_err {pc : Nat} {sevm : Sevm} {devm : Devm} {j : Jinst}
    {err : EvmError} {devm' : Devm}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j (.error ⟨err, devm'⟩)) :
    Devm.delSets devm' = Devm.delSets devm := by
  have hf := Jinst.run_instructionFrame ⟨pc, sevm, devm⟩ j
  rw [run] at hf
  exact (Devm.InstructionFrame.delSets hf).symm

-- Halting/terminal instructions (Linst) preserve NoDel.
/-- SELFDESTRUCT preserves the protected account under the modern creation
restriction or when its actual executing storage target is foreign. -/
lemma Linst.selfdestruct_preserves_noDel_of_onlyCreated_or_foreign {wa : Adr} {sevm : Sevm} {devm : Devm}
    {exn : Execution} (run : Linst.Run sevm devm .selfdestruct exn)
    (h : Devm.NoDel wa devm)
    (safe : sevm.benvStat.rules.settle.selfdestructOnlyCreated = true ∨
      sevm.currentTarget ≠ wa) :
    Execution.NoDel wa exn := by
  dsimp only [Linst.Run, Linst.run, ne_eq, Except.bind_ok, ite_not, Lean.Elab.WF.paramLet,
    Devm.balReadAccount_accessedAddresses, Devm.balReadAccount_getAcct] at run
  revert run
  cases hsg : sevm.benvStat.rules.stateGas
  · -- Ordinary lane: pop, read both accounts, price, charge, sweep.
    intro run
    dsimp only [Devm.balReadAccount_accessedAddresses, ite_not, bind, Except.bind] at run
    revert run
    cases h1 : devm.popToAdr <;> dsimp only [Devm.balReadAccount_accessedAddresses, ite_not]
    case error err =>
      intro run; rw [← run]; exact Devm.NoDel.of_eqs (Devm.popToAdr_delSets_err h1).symm (Devm.popToAdr_getCode_err h1 wa).symm h
    case ok res1 =>
      have h_br2 : (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)).getCode wa = res1.2.getCode wa :=
        Devm.balReadAccount_getCode.trans Devm.balReadAccount_getCode
      have h_acc : (match sevm.benvStat.rules.access with | .eip2929 => (if res1.1 ∉ (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)).accessedAddresses then (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)) res1.1, gasSelfDestruct + sevm.benvStat.rules.gas.coldAccountAccess) else ((Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)), gasSelfDestruct)) | .flat _ => ((Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)), gasSelfDestruct)).1.getCode wa = res1.2.getCode wa := by
        cases haccess : sevm.benvStat.rules.access with
        | flat _ => exact h_br2
        | eip2929 =>
          dsimp only
          split
          · exact (addAccessedAddress_getCode ..).trans h_br2
          · exact h_br2
      have h_br2_ds : Devm.delSets res1.2 = Devm.delSets (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)) :=
        (Devm.balReadAccount_instructionFrame _ _ _).delSets.trans (Devm.balReadAccount_instructionFrame _ _ _).delSets
      have h_acc_ds0 : Devm.delSets (match sevm.benvStat.rules.access with | .eip2929 => (if res1.1 ∉ (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)).accessedAddresses then (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)) res1.1, gasSelfDestruct + sevm.benvStat.rules.gas.coldAccountAccess) else ((Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)), gasSelfDestruct)) | .flat _ => ((Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)), gasSelfDestruct)).1 = Devm.delSets (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)) := by
        cases haccess : sevm.benvStat.rules.access <;> dsimp only <;>
          (try split) <;> rfl
      have h_acc_ds : Devm.delSets res1.2 = Devm.delSets (match sevm.benvStat.rules.access with | .eip2929 => (if res1.1 ∉ (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)).accessedAddresses then (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)) res1.1, gasSelfDestruct + sevm.benvStat.rules.gas.coldAccountAccess) else ((Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)), gasSelfDestruct)) | .flat _ => ((Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)), gasSelfDestruct)).1 :=
        h_br2_ds.trans h_acc_ds0.symm
      cases h2 : chargeGas _ _ <;> dsimp only
      case error err =>
        intro run; rw [← run]
        exact Devm.NoDel.of_eqs (chargeGas_delSets_err h2).symm (chargeGas_getCode_err h2 wa).symm (Devm.NoDel.of_eqs h_acc_ds h_acc.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h))
      case ok res2 =>
        cases h3 : assertDynamic sevm res2
        case error err =>
          intro run; rw [← run]
          dsimp only [assertDynamic, assert, Bool.not_eq_eq_eq_not, Bool.not_true] at h3
          split at h3
          · contradiction
          · simp only [Except.error.injEq] at h3; subst h3
            exact Devm.NoDel.of_eqs (chargeGas_delSets_eq h2).symm (chargeGas_getCode_eq h2 wa).symm (Devm.NoDel.of_eqs h_acc_ds h_acc.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h))
        case ok _ =>
          cases h4 : res2.subBal _ _ <;> dsimp only [Option.toExcept]
          case none =>
            intro run; rw [← run]
            exact Devm.NoDel.of_eqs (chargeGas_delSets_eq h2).symm (chargeGas_getCode_eq h2 wa).symm (Devm.NoDel.of_eqs h_acc_ds h_acc.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h))
          case some res3 =>
            have hd : Devm.NoDel wa res2 := Devm.NoDel.of_eqs (chargeGas_delSets_eq h2).symm (chargeGas_getCode_eq h2 wa).symm (Devm.NoDel.of_eqs h_acc_ds h_acc.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h))
            have h_sub : res3.getCode wa = res2.getCode wa := by
              dsimp only [Devm.subBal, Option.bind_eq_bind] at h4
              cases h_st : res2.state.subBal _ _
              case none =>
                rw [h_st] at h4; contradiction
              case some st =>
                rw [h_st] at h4; dsimp only [Option.bind_some] at h4
                simp only [Option.some.injEq] at h4; subst h4
                change st.getCode wa = res2.getCode wa
                exact State.subBal_getCode h_st
            have h_sub_ds : Devm.delSets res3 = Devm.delSets res2 := by
              dsimp only [Devm.subBal, Option.bind_eq_bind] at h4
              cases h_st : res2.state.subBal _ _
              case none => rw [h_st] at h4; contradiction
              case some st =>
                rw [h_st] at h4; dsimp only [Option.bind_some] at h4
                simp only [Option.some.injEq] at h4; subst h4
                rfl
            have hd3 : Devm.NoDel wa res3 := Devm.NoDel.of_eqs h_sub_ds.symm h_sub.symm hd
            let credited := res3.creditBeneficiary sevm.benvStat.rules res1.1
              (res1.2.getAcct sevm.currentTarget).bal
            have hc : Devm.NoDel wa credited :=
              Devm.NoDel.of_eqs (Devm.creditBeneficiary_delSets _ _ _ _).symm
                (Devm.creditBeneficiary_getCode _ _ _ _ _).symm hd3
            change (if sevm.currentTarget ∈ credited.createdAccounts ∨
                sevm.benvStat.rules.settle.selfdestructOnlyCreated = false then
              .ok (creditSelfdestructRefund sevm.benvStat.rules
                (sevm.currentTarget ∈ credited.accountsToDelete)
                (addAccountToDelete (credited.setBal sevm.currentTarget 0)
                  sevm.currentTarget)) else .ok credited) = exn → _
            split
            · rename_i hmem
              have hne : sevm.currentTarget ≠ wa := by
                rcases safe with h_onlyCreated | hforeign
                · have hcreated : sevm.currentTarget ∈ credited.createdAccounts := by
                    simpa only [h_onlyCreated, Bool.true_eq_false, or_false] using hmem
                  intro heq
                  exact hc.ca (heq ▸ hcreated)
                · exact hforeign
              have hd : Devm.NoDel wa
                  (addAccountToDelete (credited.setBal sevm.currentTarget 0)
                    sevm.currentTarget) := by
                constructor
                · exact AdrSet.not_mem_insert (Ne.symm hne) hc.atd
                · exact hc.ca
                · change ((credited.setBal sevm.currentTarget 0).getCode wa).toList ≠ []
                  rw [show (credited.setBal sevm.currentTarget 0).getCode wa =
                    credited.getCode wa from State.setBal_getCode _ _ _ _]
                  exact hc.code
              intro run; rw [← run]
              exact Devm.NoDel.of_eqs (creditSelfdestructRefund_delSets _ _ _).symm
                (creditSelfdestructRefund_getCode _ _ _ _).symm hd
            · intro run; rw [← run]
              exact hc
  · -- Amsterdam lane: static check first, priced access, state charges, logging sweep.
    rename_i state
    intro run
    dsimp only [Devm.balReadAccount_accessedAddresses, ite_not, bind, Except.bind] at run
    revert run
    cases h0 : assertDynamic sevm devm <;> dsimp only [ite_not]
    case error err =>
      intro run; rw [← run]
      dsimp only [assertDynamic, assert, Bool.not_eq_eq_eq_not, Bool.not_true] at h0
      split at h0
      · contradiction
      · simp only [Except.error.injEq] at h0; subst h0
        exact h
    case ok _ =>
      cases h1 : devm.popToAdr <;> dsimp only [ite_not]
      case error err =>
        intro run; rw [← run]; exact Devm.NoDel.of_eqs (Devm.popToAdr_delSets_err h1).symm (Devm.popToAdr_getCode_err h1 wa).symm h
      case ok res1 =>
        cases hg : Except.assert (gasSelfDestruct + (if res1.1 ∉ res1.2.accessedAddresses then sevm.benvStat.rules.gas.coldAccountAccess else 0) ≤ res1.2.gasLeft) (⟨.halt (.outOfGas .none), res1.2⟩ : EvmError × Devm) <;> dsimp only [ite_not]
        case error err =>
          intro run; rw [← run]
          dsimp only [assert, ite_not] at hg
          by_cases hle : gasSelfDestruct + (if res1.1 ∉ res1.2.accessedAddresses then sevm.benvStat.rules.gas.coldAccountAccess else 0) ≤ res1.2.gasLeft
          · simp only [hle, ite_true] at hg
            contradiction
          · simp only [hle, ite_false] at hg
            simp only [Except.error.injEq] at hg; subst hg
            exact Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h
        case ok _ =>
          have h_warm : (if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2).getCode wa = res1.2.getCode wa := by
            split
            · exact addAccessedAddress_getCode ..
            · rfl
          have h_warm_ds : Devm.delSets res1.2 = Devm.delSets (if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2) := by
            split
            · rfl
            · rfl
          have h_wb : (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 (if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2))).getCode wa = res1.2.getCode wa :=
            Devm.balReadAccount_getCode.trans (Devm.balReadAccount_getCode.trans h_warm)
          have h_wb_ds : Devm.delSets res1.2 = Devm.delSets (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 (if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2))) :=
            h_warm_ds.trans ((Devm.balReadAccount_instructionFrame _ _ _).delSets.trans (Devm.balReadAccount_instructionFrame _ _ _).delSets)
          cases hchg : chargeGas _ _ <;> dsimp only [ite_not]
          case error err =>
            intro run; rw [← run]
            exact Devm.NoDel.of_eqs (chargeGas_delSets_err hchg).symm (chargeGas_getCode_err hchg wa).symm (Devm.NoDel.of_eqs h_wb_ds h_wb.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h))
          case ok res2 =>
            cases hstg : chargeStateGas _ _ <;> dsimp only [ite_not]
            case error err =>
              intro run; rw [← run]
              exact Devm.NoDel.of_eqs (chargeStateGas_delSets_err hstg).symm (chargeStateGas_getCode_err hstg wa).symm (Devm.NoDel.of_eqs (chargeGas_delSets_eq hchg).symm (chargeGas_getCode_eq hchg wa).symm (Devm.NoDel.of_eqs h_wb_ds h_wb.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h)))
            case ok res2b =>
              cases h4 : res2b.subBal _ _ <;> dsimp only [Option.toExcept, ite_not]
              case none =>
                intro run; rw [← run]
                exact Devm.NoDel.of_eqs (chargeStateGas_delSets_eq hstg).symm (chargeStateGas_getCode_eq hstg wa).symm (Devm.NoDel.of_eqs (chargeGas_delSets_eq hchg).symm (chargeGas_getCode_eq hchg wa).symm (Devm.NoDel.of_eqs h_wb_ds h_wb.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h)))
              case some res3 =>
                have hd : Devm.NoDel wa res2b := Devm.NoDel.of_eqs (chargeStateGas_delSets_eq hstg).symm (chargeStateGas_getCode_eq hstg wa).symm (Devm.NoDel.of_eqs (chargeGas_delSets_eq hchg).symm (chargeGas_getCode_eq hchg wa).symm (Devm.NoDel.of_eqs h_wb_ds h_wb.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h)))
                have h_sub : res3.getCode wa = res2b.getCode wa := by
                  dsimp only [Devm.subBal, Option.bind_eq_bind] at h4
                  cases h_st : res2b.state.subBal _ _
                  case none =>
                    rw [h_st] at h4; contradiction
                  case some st =>
                    rw [h_st] at h4; dsimp only [Option.bind_some] at h4
                    simp only [Option.some.injEq] at h4; subst h4
                    change st.getCode wa = res2b.getCode wa
                    exact State.subBal_getCode h_st
                have h_sub_ds : Devm.delSets res3 = Devm.delSets res2b := by
                  dsimp only [Devm.subBal, Option.bind_eq_bind] at h4
                  cases h_st : res2b.state.subBal _ _
                  case none => rw [h_st] at h4; contradiction
                  case some st =>
                    rw [h_st] at h4; dsimp only [Option.bind_some] at h4
                    simp only [Option.some.injEq] at h4; subst h4
                    rfl
                have hd3 : Devm.NoDel wa res3 := Devm.NoDel.of_eqs h_sub_ds.symm h_sub.symm hd
                have h_add : (res3.addBal res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal).getCode wa = res3.getCode wa := by
                  dsimp only [Devm.addBal, Devm.getCode]; exact State.addBal_getCode res3.state _ _ _
                have h_add_ds : Devm.delSets ((res3.addBal res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal)) = Devm.delSets res3 := by
                  rfl
                have hdA : Devm.NoDel wa ((res3.addBal res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal)) :=
                  Devm.NoDel.of_eqs h_add_ds.symm h_add.symm hd3
                have hdE : Devm.NoDel wa ((res3.addBal res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal).emitTransferLog sevm.currentTarget res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal) :=
                  Devm.NoDel.of_eqs (Devm.emitTransferLog_instructionFrame _ _ _ _).delSets ((Devm.emitTransferLog_instructionFrame _ _ _ _).getCode wa) hdA
                by_cases h_if : sevm.currentTarget ∈ ((res3.addBal res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal).emitTransferLog sevm.currentTarget res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal).createdAccounts
                · simp only [h_if, ite_eq_left]
                  intro run; rw [← run]
                  have h_ca_eq : ((res3.addBal res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal).emitTransferLog sevm.currentTarget res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal).createdAccounts = res3.createdAccounts := by
                    exact (Devm.emitTransferLog_instructionFrame _ _ _ _).createdAccounts.symm.trans rfl
                  have h_ca : sevm.currentTarget ∈ res3.createdAccounts := h_ca_eq ▸ h_if
                  have h_ne : sevm.currentTarget ≠ wa := by
                    intro heq; rw [heq] at h_ca
                    exact hd3.ca h_ca
                  have h_del : (addAccountToDelete ((res3.addBal res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal).emitTransferLog sevm.currentTarget res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal) sevm.currentTarget).getCode wa = ((res3.addBal res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal).emitTransferLog sevm.currentTarget res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal).getCode wa := by
                    rfl
                  constructor
                  · exact AdrSet.not_mem_insert (Ne.symm h_ne) hdE.atd
                  · exact hdE.ca
                  · rw [h_del]; exact hdE.code
                · simp only [h_if]
                  intro run; rw [← run]
                  constructor
                  · exact hdE.atd
                  · exact hdE.ca
                  · exact hdE.code

/-- Modern settlement specialization of the shared SELFDESTRUCT proof. -/
lemma Linst.selfdestruct_preserves_noDel {wa : Adr} {sevm : Sevm} {devm : Devm}
    {exn : Execution} (run : Linst.Run sevm devm .selfdestruct exn)
    (h : Devm.NoDel wa devm)
    (h_onlyCreated : sevm.benvStat.rules.settle.selfdestructOnlyCreated = true) :
    Execution.NoDel wa exn :=
  Linst.selfdestruct_preserves_noDel_of_onlyCreated_or_foreign run h (Or.inl h_onlyCreated)

/-- A terminal preserves the protected account when it executes in a foreign
storage context or is not SELFDESTRUCT. This covers both execution outcomes. -/
theorem Linst.run_noDel_of_safe {wa : Adr} {sevm : Sevm} {devm : Devm}
    {l : Linst} {exn : Execution} (run : Linst.Run sevm devm l exn)
    (h : Devm.NoDel wa devm)
    (safe : sevm.currentTarget ≠ wa ∨ l ≠ .selfdestruct) :
    Execution.NoDel wa exn := by
  rcases eq_or_ne l .selfdestruct with rfl | h_not_selfdestruct
  · rcases safe with hforeign | hnot
    · exact Linst.selfdestruct_preserves_noDel_of_onlyCreated_or_foreign run h
        (Or.inr hforeign)
    · exact (hnot rfl).elim
  · have hf := Linst.run_instructionFrame sevm devm l h_not_selfdestruct
    rw [run] at hf
    cases exn <;>
      exact Devm.NoDel.of_eqs (Devm.InstructionFrame.delSets hf) (hf.getCode wa) h


theorem Linst.run_noDel {wa : Adr} {sevm : Sevm} {devm : Devm}
    {l : Linst} {exn : Execution} (run : Linst.Run sevm devm l exn)
    (h : Devm.NoDel wa devm)
    (h_onlyCreated : sevm.benvStat.rules.settle.selfdestructOnlyCreated = true) :
    Execution.NoDel wa exn := by
  rcases eq_or_ne l .selfdestruct with rfl | h_not_selfdestruct
  · exact Linst.selfdestruct_preserves_noDel run h h_onlyCreated
  · have hf := Linst.run_instructionFrame sevm devm l h_not_selfdestruct
    rw [run] at hf
    cases exn <;>
      exact Devm.NoDel.of_eqs (Devm.InstructionFrame.delSets hf) (hf.getCode wa) h

lemma Linst.inv_noDel {wa : Adr} {sevm : Sevm} {devm : Devm} {l : Linst}
    {exn : Execution}
    (run : Linst.Run sevm devm l exn)
    (h : Devm.NoDel wa devm)
    (h_onlyCreated : sevm.benvStat.rules.settle.selfdestructOnlyCreated = true) :
    Execution.NoDel wa exn := by
  exact Linst.run_noDel run h h_onlyCreated

lemma Msg.NoDel.benvAfterTransfer_err {wa : Adr} {msg : Msg}
    {x : EvmError × State × AdrSet × Tra}
    (h_run : msg.benvAfterTransfer = .error x)
    (h : Msg.NoDel wa msg) : wa ∉ x.2.2.1 ∧ (x.2.1.getCode wa).toList ≠ [] := by
  by_cases h_stv : msg.shouldTransferValue = true ∧ msg.value ≠ 0
  · unfold Msg.benvAfterTransfer at h_run
    rw [ite_eq_left h_stv] at h_run
    cases h_sub : msg.benv.subBal msg.caller msg.value
    · rw [h_sub] at h_run
      simp only [Except.error.injEq, Option.toExcept, Except.bind, bind] at h_run
      subst h_run
      exact ⟨h.ca, h.code⟩
    · rw [h_sub] at h_run
      dsimp only [Option.toExcept, Except.bind_ok] at h_run
      contradiction
  · unfold Msg.benvAfterTransfer at h_run
    rw [ite_eq_right h_stv] at h_run
    contradiction

lemma chargeCodeGas_delSets_ok {rules : ForkRules} {d d' : Devm}
    (h : processCreateMessage.chargeCodeGas rules d = .ok d') :
    Devm.delSets d' = Devm.delSets d := by
  have hf := processCreateMessage.chargeCodeGas_instructionFrame rules d
  rw [h] at hf
  exact (Devm.InstructionFrame.delSets hf).symm

lemma chargeCodeGas_delSets_err {rules : ForkRules} {d d' : Devm} {err : EvmError}
    (h : processCreateMessage.chargeCodeGas rules d = .error ⟨err, d'⟩) :
    Devm.delSets d' = Devm.delSets d := by
  have hf := processCreateMessage.chargeCodeGas_instructionFrame rules d
  rw [h] at hf
  exact (Devm.InstructionFrame.delSets hf).symm

lemma Devm.push_noDel {wa : Adr} {x : B256} {d : Devm} {exn : Execution}
    (heq : Devm.push x d = exn) (h : Devm.NoDel wa d) : Execution.NoDel wa exn := by
  subst heq
  cases hp : Devm.push x d with
  | error err =>
    have hd := Devm.push_delSets_err hp
    refine ⟨?_, ?_, (Devm.push_getCode_err hp wa) ▸ h.code⟩
    · rw [show err.2.accountsToDelete = d.accountsToDelete from congrArg Prod.fst hd]
      exact h.atd
    · rw [show err.2.createdAccounts = d.createdAccounts from congrArg Prod.snd hd]
      exact h.ca
  | ok d' =>
    have hd := Devm.push_delSets_eq hp
    refine ⟨?_, ?_, (Devm.push_getCode_eq hp wa) ▸ h.code⟩
    · rw [show d'.accountsToDelete = d.accountsToDelete from congrArg Prod.fst hd]
      exact h.atd
    · rw [show d'.createdAccounts = d.createdAccounts from congrArg Prod.snd hd]
      exact h.ca

lemma incorporateChildOnError_noDel {wa : Adr} {parent child : Devm} {rd : Bytes}
    (hp_atd : wa ∉ parent.accountsToDelete) (hc : Devm.NoDel wa child) :
    Devm.NoDel wa (incorporateChildOnError parent child rd) :=
  ⟨hp_atd, hc.ca, hc.code⟩

lemma incorporateChildOnSuccess_noDel {wa : Adr} {parent child : Devm} {rd : Bytes}
    (hp_atd : wa ∉ parent.accountsToDelete) (hc : Devm.NoDel wa child) :
    Devm.NoDel wa (incorporateChildOnSuccess parent child rd) :=
  ⟨AdrSet.not_mem_union hp_atd hc.atd, hc.ca, hc.code⟩

lemma Devm.pop_err_snd {d : Devm} {x : EvmError × Devm}
    (h : Devm.pop d = .error x) : x.2 = d := by
  simp only [Devm.pop_def] at h
  split at h
  · injection h with h; exact (congrArg Prod.snd h).symm
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

lemma Devm.popToAdr_err_snd {d : Devm} {x : EvmError × Devm}
    (h : Devm.popToAdr d = .error x) : x.2 = d := by
  rw [Devm.popToAdr_def] at h
  rcases hp : d.pop with e | ⟨v, d0⟩
  · rw [hp] at h; injection h with h; rw [← h]; exact Devm.pop_err_snd hp
  · rw [hp] at h; exact absurd h (by simp only [Except.map_ok, reduceCtorEq, not_false_eq_true])

lemma chargeGas_err_snd {cost : Nat} {d : Devm} {x : EvmError × Devm}
    (h : chargeGas cost d = .error x) : x.2 = d := by
  simp only [chargeGas_def] at h
  split at h
  · injection h with h; exact (congrArg Prod.snd h).symm
  · exact absurd h (by simp only [ExceptT.stM_eq, reduceCtorEq, not_false_eq_true])

lemma Except.assert_err_snd {p : Prop} [Decidable p] {d : Devm} {s : EvmError}
    {x : EvmError × Devm} (h : Except.assert p (⟨s, d⟩ : EvmError × Devm) = .error x) :
    x.2 = d := by
  simp only [Except.assert] at h
  split at h
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  · injection h with h; exact (congrArg Prod.snd h).symm

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
  refine hd.of_eqs ?_ (Devm.memExtends_getCode ..).symm
  rfl

lemma Devm.NoDel.addAccessedAddress {wa : Adr} {d : Devm} {a : Adr}
    (hd : Devm.NoDel wa d) : Devm.NoDel wa (Jaune.addAccessedAddress d a) := by
  refine hd.of_eqs ?_ (addAccessedAddress_getCode ..).symm
  rfl

def Benv.EquivForDelegation (b1 b2 : Benv) : Prop :=
  b2.createdAccounts = b1.createdAccounts ∧
  ∀ a, (b1.state.getCode a).toList ≠ [] →
    ¬ isValidDelegation (b1.state.getCode a) →
    b2.state.getCode a = b1.state.getCode a

lemma Benv.EquivForDelegation_refl (b : Benv) : Benv.EquivForDelegation b b := by
  refine ⟨rfl, fun _ _ _ => rfl⟩

lemma Benv.EquivForDelegation_trans {b1 b2 b3 : Benv} (h12 : Benv.EquivForDelegation b1 b2) (h23 : Benv.EquivForDelegation b2 b3) :
    Benv.EquivForDelegation b1 b3 := by
  rcases h12 with ⟨h1c, h1code⟩
  rcases h23 with ⟨h2c, h2code⟩
  refine ⟨by rw [h2c, h1c], fun a ha hnd => ?_⟩
  have h1 := h1code a ha hnd
  have ha2' : (b2.state.getCode a).toList ≠ [] := by
    rw [h1]
    exact ha
  have hnd2 : ¬ isValidDelegation (b2.state.getCode a) := by
    rw [h1]
    exact hnd
  rw [h2code a ha2' hnd2, h1]

lemma Msg.NoDel.benvAfterTransfer {wa : Adr} {msg : Msg} {benv : Benv}
    (h_run : msg.benvAfterTransfer = .ok benv)
    (h : Msg.NoDel wa msg) : Msg.NoDel wa (msg.withBenv benv) := by
  by_cases h_stv : msg.shouldTransferValue = true ∧ msg.value ≠ 0
  · unfold Msg.benvAfterTransfer at h_run
    rw [ite_eq_left h_stv] at h_run
    unfold Benv.subBal at h_run
    rcases h_sub : msg.benv.state.subBal msg.caller msg.value with _ | st_mid
    · rw [h_sub] at h_run
      simp only [Option.toExcept, bind, Option.bind, Except.bind] at h_run
      contradiction
    · rw [h_sub] at h_run
      simp only [Option.toExcept, bind, Option.bind, Except.bind] at h_run
      injection h_run with hB
      have hBc : benv.createdAccounts = msg.benv.createdAccounts := by
        rw [← hB]; rfl
      have h_code_add : benv.state.getCode wa = st_mid.getCode wa := by
        have hBs : benv.state = st_mid.addBal msg.currentTarget msg.value := by
          rw [← hB]; rfl
        rw [hBs]; exact State.addBal_getCode st_mid msg.currentTarget wa msg.value
      have h_code_sub : st_mid.getCode wa = msg.benv.state.getCode wa := by
        exact State.subBal_getCode h_sub
      have h_code : ((msg.withBenv benv).benv.state.getCode wa).toList ≠ [] := by
        change (benv.state.getCode wa).toList ≠ []
        rw [h_code_add, h_code_sub]
        exact h.code
      exact ⟨hBc ▸ h.ca, h_code⟩
  · unfold Msg.benvAfterTransfer at h_run
    rw [ite_eq_right h_stv] at h_run
    have heq : benv = msg.benv := (Except.ok.inj h_run).symm
    subst heq
    exact h

end Blanc
