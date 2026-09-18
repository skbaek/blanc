-- ProrataWethVaultPairWethSegment.lean : the WETH-frame pair segment.

import Blanc.Composition.ProrataWethVaultHistory

/-!
# The WETH frame as a pair-history segment

`WethFramePairSegment vault` (History) asks every committed compiled WETH run
whose selector is not `withdraw(uint256)`, entered by a caller that is neither
the vault nor WETH, to be a provenance-tagged pair replay between its own
endpoints.  This module proves it by the selector split of
`WethFrameClass.classify?`, arm by arm as `wethFrame_vaultRow_classified`:

* a view keeps every `Stor` tree and replays with no record;
* `approve` is one `.silent` record owning its approval invocation: it writes
  one non-address allowance cell and never the vault's row;
* the fallback `deposit` is one `.silent` record owning nothing: it writes the
  caller's own address row only;
* `transfer` is a donation (`.operation` with the generalised
  `FourQuoteShareEvidence.credit`) when it credits the vault, and otherwise a
  `.silent` record owning nothing, since it moves address rows only;
* `transferFrom` owns its invocation.  From the vault it is an
  `.authorizedDebit`; crediting the vault it is a donation; otherwise it is
  `.silent`.

WETH writes no storage but its own, and `wethAccount ≠ vault` comes from the
vault's configuration, so the vault's storage is kept in every arm.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

/-- A successful exact compiled WETH `approve` writes no account's storage but
its own.  `weth_approve_compiled_raw_effect` pins the target's storage; this
is the foreign half, walked over the same fragments. -/
private theorem weth_approve_compiled_foreign {sevm : Sevm} {pre post : Devm}
    (run : Prog.RunCompiled sevm pre Blanc.weth post)
    (selected : Sevm.selector sevm = selector "approve" [.address, .uint256])
    {account : Adr} (foreign : sevm.currentTarget ≠ account) :
    Devm.getStor post account = Devm.getStor pre account := by
  obtain ⟨bodyPre, -, entryState, -, -, -, bodyRun⟩ :=
    runCompiled_enters_wethNonpayable (body := Blanc.approve) run selected
      (by simp [Blanc.wethFuncs])
  rcases of_run_prepend (arg 0 ++ checkNonAddress) _ bodyRun with
    ⟨a, ha, run⟩
  rcases of_run_branch_revert run with ⟨b, hb, run⟩
  rcases of_run_prepend prepApprove _ run with ⟨c, hc, run⟩
  rcases of_run_branch_revert run with ⟨d, hd, run⟩
  rcases of_run_next run with ⟨f, hs, run⟩
  have before : Devm.getStor pre = Devm.getStor d :=
    (funext (getStor_eq_of_state_eq entryState)).trans
      ((Line.of_inv Devm.getStor (by line_inv) ha).trans
        ((funext (fun account => (Devm.PopBurn.getStor hb account).symm)).trans
          ((Line.of_inv Devm.getStor (by line_inv) hc).trans
            (funext (fun account => (Devm.PopBurn.getStor hd account).symm)))))
  have after : Devm.getStor f = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) run
  obtain ⟨pc, registerRun⟩ := of_run_reg hs
  rw [← congrFun after account, sstore_preserves_getStor_ne registerRun foreign,
    ← congrFun before account]

/-- The one-record replay between a record's own endpoints, tagged with its
provenance. -/
private theorem wethRecord_segment {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (record : PairStepRecord vault)
    (before : record.before = pre.state) (after : record.after = post.state)
    {provenance : Blanc.Prorata.ProrataAccountingProvenance}
    (tag : record.provenance = provenance)
    (owned : ∀ call, record.own = some call →
      call.sevm = sevm ∧ call.pre = pre ∧ call.post = post) :
    ∃ steps : List (PairStepRecord vault),
      PairReplay vault (PairBoundary.ofState vault pre.state) steps
        (PairBoundary.ofState vault post.state) ∧
      ∀ r ∈ steps, r.provenance = provenance ∧
        ∀ call, r.own = some call → call.sevm = sevm ∧ call.pre = pre ∧ call.post = post := by
  have replay := PairReplay.singleton record
  rw [before, after] at replay
  refine ⟨_, replay, ?_⟩
  intro r member
  simp only [List.mem_singleton] at member
  subst member
  exact ⟨tag, owned⟩

/-- An invocation over the frame's own endpoints is linked at both, and staged
vacuously: its caller is not the vault. -/
private theorem linked_self {vault : Adr} {pre post : Devm}
    {call : WethAllowanceInvocation}
    (preEq : call.pre = pre) (postEq : call.post = post)
    (callerNe : call.sevm.caller ≠ vault) :
    ∀ c, some call = some c →
      c.pre.state.getStor wethAccount = pre.state.getStor wethAccount ∧
      c.post.state.getStor wethAccount = post.state.getStor wethAccount ∧
      (c.sevm.caller = vault → VaultStagedCalldata c) := by
  intro c same
  cases same
  refine ⟨by rw [preEq], by rw [postEq], fun equal => absurd equal callerNe⟩

/-- The donation record: an accepted `credit` operation to the vault from a
source that is not the vault, over a WETH frame that kept the vault's storage. -/
private def creditRecord {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (target : sevm.currentTarget = wethAccount)
    (source : Adr) (amount : B256) (sourceNe : source ≠ vault)
    (rowNof : B256.Nof (Stor.rest (Devm.getStor pre wethAccount) vault) amount)
    (effect : Transfer (Stor.rest (Devm.getStor pre wethAccount)) source amount
      vault (Stor.rest (Devm.getStor post wethAccount)))
    (vaultKept : Devm.getStor post vault = Devm.getStor pre vault)
    (own : Option WethAllowanceInvocation)
    (linked : ∀ call, own = some call →
      call.pre.state.getStor wethAccount = pre.state.getStor wethAccount ∧
      call.post.state.getStor wethAccount = post.state.getStor wethAccount ∧
      (call.sevm.caller = vault → VaultStagedCalldata call))
    (quiet : own = none → ∀ key, ¬ ValidAdr key →
      (post.state.getStor wethAccount).get key =
        (pre.state.getStor wethAccount).get key)
    (provenance : Blanc.Prorata.ProrataAccountingProvenance)
    (actor : provenance.actor = some sevm.caller) : PairStepRecord vault where
  before := pre.state
  after := post.state
  step := .operation ⟨sevm, pre, post, rfl, rfl,
      .credit ⟨source, amount⟩ target sourceNe
        (by
          change (Devm.getStor post vault).get _ = (Devm.getStor pre vault).get _
          rw [vaultKept]) rowNof effect⟩
    (.credit ⟨source, amount⟩ target sourceNe _ rowNof effect vaultKept)
  own := own
  linked := linked
  quiet := quiet
  debitOwn := by
    intro _ _ _ _ _ _ impossible
    cases impossible
  provenance := provenance
  actor := actor

/-- The silent record: the vault's storage and the vault's WETH row are kept. -/
private def silentRecord {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (vaultKept : Devm.getStor post vault = Devm.getStor pre vault)
    (rowKept : Stor.rest (Devm.getStor post wethAccount) vault =
      Stor.rest (Devm.getStor pre wethAccount) vault)
    (own : Option WethAllowanceInvocation)
    (linked : ∀ call, own = some call →
      call.pre.state.getStor wethAccount = pre.state.getStor wethAccount ∧
      call.post.state.getStor wethAccount = post.state.getStor wethAccount ∧
      (call.sevm.caller = vault → VaultStagedCalldata call))
    (quiet : own = none → ∀ key, ¬ ValidAdr key →
      (post.state.getStor wethAccount).get key =
        (pre.state.getStor wethAccount).get key)
    (provenance : Blanc.Prorata.ProrataAccountingProvenance)
    (actor : provenance.actor = some sevm.caller) : PairStepRecord vault where
  before := pre.state
  after := post.state
  step := .silent sevm.caller vaultKept rowKept
  own := own
  linked := linked
  quiet := quiet
  debitOwn := by
    intro _ _ _ _ _ _ impossible
    cases impossible
  provenance := provenance
  actor := actor

/-- The authorized-debit record: a `transferFrom` from the vault's row, owning
exactly its own invocation. -/
private def debitRecord {vault : Adr} {pre post : Devm}
    (call : WethAllowanceInvocation)
    (foreign : call.sevm.caller ≠ vault)
    (owner : Sevm.argWord call.sevm 0 = vault.toB256)
    (pair : call.pair? = some (vault.toB256, call.sevm.caller.toB256))
    (moved : Transfer (Stor.rest (Devm.getStor pre wethAccount)) vault
      (Sevm.argWord call.sevm 2) (Sevm.argWord call.sevm 1).toAdr
      (Stor.rest (Devm.getStor post wethAccount)))
    (vaultKept : Devm.getStor post vault = Devm.getStor pre vault)
    (linked : ∀ c, some call = some c →
      c.pre.state.getStor wethAccount = pre.state.getStor wethAccount ∧
      c.post.state.getStor wethAccount = post.state.getStor wethAccount ∧
      (c.sevm.caller = vault → VaultStagedCalldata c))
    (provenance : Blanc.Prorata.ProrataAccountingProvenance)
    (actor : provenance.actor = some call.sevm.caller) : PairStepRecord vault where
  before := pre.state
  after := post.state
  step := .authorizedDebit call foreign owner pair moved vaultKept
  own := some call
  linked := linked
  quiet := (fun impossible => nomatch impossible)
  debitOwn := by
    intro c _ _ _ _ _ same
    cases same
    rfl
  provenance := provenance
  actor := actor

/-- A balance transfer whose source is not the vault and whose destination is
not the vault leaves the vault's row alone. -/
private theorem transfer_row_kept {b d : Adr → B256} {source dest vault : Adr}
    {wad : B256} (move : Transfer b source wad dest d)
    (sourceNe : source ≠ vault) (destNe : dest ≠ vault) :
    d vault = b vault := by
  obtain ⟨-, c, decrease, increase⟩ := move
  rw [(decrease vault).2 sourceNe]
  exact ((increase vault).2 destNe).symm

/-- A donation to the vault from a row other than the vault's cannot overflow
the vault's row: both rows sit inside WETH's solvent booked sum. -/
private theorem credit_rowNof {vault source : Adr} {sevm : Sevm} {pre : Devm}
    {b d : Adr → B256} {amount : B256}
    (weth : wethSpec.Pre wethAccount sevm pre)
    (target : sevm.currentTarget = wethAccount)
    (bEq : b = Stor.rest (Devm.getStor pre wethAccount))
    (move : Transfer b source amount vault d) (sourceNe : source ≠ vault) :
    B256.Nof (Stor.rest (Devm.getStor pre wethAccount) vault) amount := by
  subst bEq
  have precond := wethSpec_pre_iff.mp weth
  have solvent := precond.solvent.1 target
  unfold Stor.Solvent at solvent
  have bound : (pre.getBal wethAccount).toNat < 2 ^ 256 :=
    B256.toNat_lt (pre.getBal wethAccount)
  have expand : balSum (Devm.getStor pre wethAccount) =
      sum (Stor.rest (Devm.getStor pre wethAccount)) := rfl
  have pairLe := add_le_sum_of_ne (Stor.rest (Devm.getStor pre wethAccount))
    sourceNe
  have movedLe := B256.toNat_le_toNat move.1
  unfold B256.Nof
  omega

/-- **The WETH-frame pair segment.**  Every committed compiled WETH run other
than `withdraw`, entered by a caller that is neither the vault nor WETH, is a
provenance-tagged pair replay between its own endpoints: no record for a view,
one classified record for each writer. -/
theorem wethFramePairSegment (vault : Adr) : WethFramePairSegment vault := by
  intro sevm pre post run target _direct callerNe _callerNotWeth notWithdraw inv
    provenance actor
  have memoryWf : Mem.Wf pre.memory := by
    rw [(inv.wethFresh target).2]; exact Mem.wf_empty
  have distinct : wethAccount ≠ vault := inv.vault.config.distinct
  have foreignVault : sevm.currentTarget ≠ vault := by rw [target]; exact distinct
  have vaultKeyNe : ∀ {a : Adr}, a ≠ vault → a.toB256 ≠ vault.toB256 := by
    intro a different equal
    exact different (by rw [← toAdr_toB256 a, equal, toAdr_toB256])
  by_cases isApprove : Sevm.selector sevm = selector "approve" [.address, .uint256]
  · obtain ⟨keyInvalid, written⟩ :=
      weth_approve_compiled_raw_effect memoryWf run isApprove
    rw [target] at written
    have vaultKept : Devm.getStor post vault = Devm.getStor pre vault :=
      weth_approve_compiled_foreign run isApprove foreignVault
    have keyNe : wethAllowanceKey sevm.caller.toB256 (Sevm.argWord sevm 0) ≠
        vault.toB256 := by
      intro equal
      exact keyInvalid (equal ▸ ⟨vault, rfl⟩)
    have rowKept : Stor.rest (Devm.getStor post wethAccount) vault =
        Stor.rest (Devm.getStor pre wethAccount) vault := by
      simp only [Stor.rest, Function.comp_apply, written, Stor.get_set_ne _ keyNe]
    let call : WethAllowanceInvocation :=
      ⟨sevm, pre, post, true, target, memoryWf, run, by simpa using isApprove⟩
    exact wethRecord_segment
      (silentRecord vaultKept rowKept (some call)
        (linked_self (call := call) rfl rfl callerNe) (fun impossible => nomatch impossible)
          provenance actor)
      rfl rfl rfl
            (by intro c h; cases h; exact ⟨rfl, rfl, rfl⟩)
  by_cases isTransferFrom : Sevm.selector sevm =
      selector "transferFrom" [.address, .address, .uint256]
  · obtain ⟨move, foreignAll⟩ := weth_transferFrom_compiled_row_effect run isTransferFrom
    rw [target] at move
    have vaultKept : Devm.getStor post vault = Devm.getStor pre vault :=
      foreignAll vault foreignVault
    let call : WethAllowanceInvocation :=
      ⟨sevm, pre, post, false, target, memoryWf, run, by simpa using isTransferFrom⟩
    have linked := linked_self (vault := vault) (call := call) rfl rfl callerNe
    by_cases debited : (Sevm.argWord sevm 0).toAdr = vault
    · obtain ⟨sourceAdr, sourceEq⟩ := weth_transferFrom_compiled_src_valid run isTransferFrom
      have owner : Sevm.argWord sevm 0 = vault.toB256 := by
        rw [← sourceEq] at debited ⊢
        rw [toAdr_toB256] at debited
        rw [debited]
      have pair : call.pair? = some (vault.toB256, call.sevm.caller.toB256) := by
        simp only [call, WethAllowanceInvocation.pair?, owner,
          if_neg (Ne.symm (vaultKeyNe callerNe)), Bool.false_eq_true, if_false]
      exact wethRecord_segment
        (debitRecord call callerNe owner pair (debited ▸ move) vaultKept linked
          provenance actor) rfl rfl rfl
            (by intro c h; cases h; exact ⟨rfl, rfl, rfl⟩)
    · by_cases credited : (Sevm.argWord sevm 1).toAdr = vault
      · have effect := credited ▸ move
        exact wethRecord_segment
          (creditRecord target _ _ debited
            (credit_rowNof inv.weth target rfl effect debited) effect vaultKept
            (some call) linked (fun impossible => nomatch impossible) provenance actor) rfl rfl rfl
            (by intro c h; cases h; exact ⟨rfl, rfl, rfl⟩)
      · exact wethRecord_segment
          (silentRecord vaultKept (transfer_row_kept move debited credited)
            (some call) linked (fun impossible => nomatch impossible) provenance actor) rfl rfl rfl
            (by intro c h; cases h; exact ⟨rfl, rfl, rfl⟩)
  by_cases isTransfer : Sevm.selector sevm = selector "transfer" [.address, .uint256]
  · obtain ⟨move, off, foreignAll⟩ := weth_transfer_compiled_effect run isTransfer
    rw [target] at move off
    have vaultKept : Devm.getStor post vault = Devm.getStor pre vault :=
      foreignAll vault foreignVault
    have quiet : (none : Option WethAllowanceInvocation) = none →
        ∀ key, ¬ ValidAdr key →
          (post.state.getStor wethAccount).get key =
            (pre.state.getStor wethAccount).get key := by
      intro _ key notAdr
      exact (off key notAdr).symm
    by_cases credited : (Sevm.argWord sevm 0).toAdr = vault
    · have effect := credited ▸ move
      exact wethRecord_segment
        (creditRecord target _ _ callerNe
          (credit_rowNof inv.weth target rfl effect callerNe) effect vaultKept
          none (fun _ impossible => nomatch impossible) quiet provenance actor) rfl rfl rfl
            (by intro c h; cases h)
    · exact wethRecord_segment
        (silentRecord vaultKept (transfer_row_kept move callerNe credited)
          none (fun _ impossible => nomatch impossible) quiet provenance actor) rfl rfl rfl
            (by intro c h; cases h)
  by_cases isView : Sevm.selector sevm ∈ wethViewSelectors
  · have kept := weth_view_compiled_effect run isView
    exact ⟨[], PairReplay.nil_of_eq
      (PairBoundary.ofState_eq (congrFun kept vault).symm
        (congrFun kept wethAccount).symm), by simp⟩
  have miss : ∀ sel ∈ wethSelectors, Sevm.selector sevm ≠ sel := by
    intro sel member equal
    rcases mem_wethSelectors_cases sel member with
      view | approve | transferFrom | transfer | withdraw
    · exact isView (equal ▸ view)
    · exact isApprove (equal.trans approve)
    · exact isTransferFrom (equal.trans transferFrom)
    · exact isTransfer (equal.trans transfer)
    · exact notWithdraw (equal.trans withdraw)
  obtain ⟨mid, entryState, -, -, -, depositRun⟩ :=
    runCompiled_enters_wethDeposit run miss
  obtain ⟨written, foreignAll⟩ := depositBody_effect depositRun
  have entryStorage : Devm.getStor pre = Devm.getStor mid :=
    funext (getStor_eq_of_state_eq entryState)
  rw [target] at written
  have vaultKept : Devm.getStor post vault = Devm.getStor pre vault := by
    rw [foreignAll vault foreignVault, ← congrFun entryStorage vault]
  have rowKept : Stor.rest (Devm.getStor post wethAccount) vault =
      Stor.rest (Devm.getStor pre wethAccount) vault := by
    simp only [Stor.rest, Function.comp_apply, written,
      Stor.get_set_ne _ (vaultKeyNe callerNe), ← congrFun entryStorage]
  have quiet : (none : Option WethAllowanceInvocation) = none →
      ∀ key, ¬ ValidAdr key →
        (post.state.getStor wethAccount).get key =
          (pre.state.getStor wethAccount).get key := by
    intro _ key notAdr
    have keyNe : sevm.caller.toB256 ≠ key := by
      intro equal
      exact notAdr (by rw [← equal]; exact ⟨sevm.caller, rfl⟩)
    change (Devm.getStor post wethAccount).get key =
      (Devm.getStor pre wethAccount).get key
    rw [written, Stor.get_set_ne _ keyNe, ← congrFun entryStorage wethAccount]
  exact wethRecord_segment
    (silentRecord vaultKept rowKept none (fun _ impossible => nomatch impossible)
      quiet provenance actor)
    rfl rfl rfl
            (by intro c h; cases h)

end Blanc.Composition.ProrataWethVault
