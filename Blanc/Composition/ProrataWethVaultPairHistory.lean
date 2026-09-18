-- ProrataWethVaultPairHistory.lean : the pair's realized history carrier (R10), its rooted allowance
-- ledger, and the backing corollary limited exactly by D9.

import Blanc.Composition.ProrataWethVaultPairLadder

/-!
# The realized pair history

`PairTraceRealizes root steps future` supplements configured reachability from the pair root with the
classified steps the chain actually produced: in chain order, one retained `ConfiguredBlockTrace` per
imported block together with that block's own connected `PairReplay` segment, every record of which carries
the block's header number.  It is the pair's rung R10, in the shape of `Prorata.ProrataTraceRealizes` and of
the generic `AccountingLadder.TraceRealizes`; it is not an instance of the latter because the pair is not an
`AccountingLadder` (two storages, a provenance-indexed replay, an invariant that is no single spec's).

Three things are read off a realized trace.

* **The raw allowance ledger** — the invocations the records own, `PairStepRecord.ledger steps` — is a rooted
  chronology (`rootedAllowanceHistory`): the records' own storage links and non-address silence are exactly
  the `invoked` and `silent` steps of `RootedAllowanceHistory`, and the pair root's empty WETH storage is its
  root.  This is SF §7 clause 8.
* **Under D9** (`NoVaultAllowanceKeyCollision` of that ledger) every runtime-authorized debit of the vault's
  WETH row moved nothing (`authorizedDebit_zero`): the rooted ledger makes the vault-owned cell read zero at
  the debit's own pre-state, and the executed finite branch then forces `wad = 0`
  (`WethAllowanceInvocation.vaultDebit_wad_eq_zero`).  With every step priced, the virtual price per share
  never falls from genesis, which is the backing bound `supply ≤ O · row`; with the supply cap — carried by
  every step unconditionally — this is `pair_reachable_stable`.
* **Without D9** the statement is the classification itself (`pair_reachable_backed_or_debit`): every
  reachable state is backed, or its realized trace retains a runtime-authorized debit of positive amount.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune
open _root_.Blanc.ExecutionTrace

/-! ## 1. Word algebra -/

/-- Subtracting zero is the identity on words. -/
private theorem b256_sub_zero (x : B256) : x - 0 = x := by
  apply B256.toNat_inj
  rw [B256.toNat_sub_eq_of_le x 0
      (B256.le_of_toNat_le_toNat (by rw [B256.toNat_zero]; exact Nat.zero_le _)),
    B256.toNat_zero, Nat.sub_zero]
-- Weth10Redeemable.lean:2271 states it; that module is contract-local and not importable (D-4).

/-- Adding zero is the identity on words. -/
private theorem b256_add_zero (x : B256) : x + 0 = x := by
  apply B256.toNat_inj
  rw [B256.toNat_add, B256.toNat_zero]
  norm_num [Nat.lo_eq]
  exact B256.toNat_lt x
-- Weth10Redeemable.lean:2283–2288 verbatim.

/-- A zero-amount `Transfer` leaves its source row where it was, whatever its destination — the source
itself included. -/
theorem transfer_src_row_of_zero {b d : Adr → B256} {kd ki : Adr}
    (h : Transfer b kd 0 ki d) : d kd = b kd := by
  obtain ⟨-, c, dec, inc⟩ := h
  have debited : b kd - 0 = c kd := (dec kd).1 rfl
  have credited : c kd = d kd := by
    by_cases same : ki = kd
    · have raised : c kd + 0 = d kd := (inc kd).1 same
      rwa [b256_add_zero] at raised
    · exact (inc kd).2 same
  rw [← credited, ← debited, b256_sub_zero]
-- new; the `Frel` unfolding is `credited_of_transfer`/`debitedSub_of_transfer` (B:186/:205), without their
-- `kd ≠ ki` premise.

/-! ## 2. The boundary's accounting coordinates -/

/-- The pair's accounting snapshot read off a boundary: the supply word and the vault's WETH row. -/
def PairBoundary.snapshot (vault : Adr) (b : PairBoundary) : FourQuote.Snapshot :=
  ⟨(b.vault.get Blanc.ProrataWethVault.supplySlot).toNat, (Stor.rest b.weth vault).toNat⟩

@[simp] theorem PairBoundary.snapshot_ofState (vault : Adr) (w : State) :
    (PairBoundary.ofState vault w).snapshot vault = FourQuote.stateSnapshot vault w := rfl
-- `stateSnapshot` A:684 reads exactly these two coordinates.

/-- The pair root is the genesis snapshot: no shares, no WETH row. -/
theorem PairRoot.genesisSnapshot {cfg : ChainConfig} {deployed : BlockChain} {vault : Adr}
    (root : PairRoot cfg deployed vault) :
    FourQuote.stateSnapshot vault deployed.state = ⟨0, 0⟩ := by
  unfold FourQuote.stateSnapshot
  rw [root.vaultEmpty, root.wethEmpty]
  congr
  change (Stor.empty.get vault.toB256).toNat = 0
  simp [Stor.empty, Stor.get, B256.toNat_zero]
-- PH:193–197 (`DeploymentRoot.accountingSnapshot`).

/-- The pair root is its own configured reach. -/
theorem PairRoot.reflReach {cfg : ChainConfig} {deployed : BlockChain} {vault : Adr}
    (root : PairRoot cfg deployed vault) : BlockChain.ReachUsing cfg deployed deployed :=
  .refl deployed root.configValid root.validContext root.chainId
-- `DeploymentRoot.reflReach` shape; Ladder.lean:6774.

/-! ## 3. The zero-debit fact, in the three currencies the carrier reads -/

/-- **The zero-debit fact in invocation currency.**  A successful WETH invocation, sent by a caller other
than the vault, that visits the vault-owned allowance pair `(vault, caller)` debits nothing when that raw
cell reads zero at the invocation's own pre-state.  The four branches are `allowance_debit_classification`'s:
an `approve` visits `(caller, spender)` and so would make the caller the vault; a self `transferFrom` visits no
pair; the maximum branch reads `B256.max`, not zero; the finite branch has `wad ≤ cell = 0`.  No collision
premise and no chronology: those only establish `quiet`. -/
theorem WethAllowanceInvocation.vaultDebit_wad_eq_zero {vault : Adr}
    (call : WethAllowanceInvocation)
    (foreign : call.sevm.caller ≠ vault)
    (pair : call.pair? = some (vault.toB256, call.sevm.caller.toB256))
    (quiet : call.pre.getStorVal wethAccount
      (wethAllowanceKey vault.toB256 call.sevm.caller.toB256) = 0) :
    Sevm.argWord call.sevm 2 = 0 := by
  rcases allowance_debit_classification call with
    ⟨approval, -, -⟩ | ⟨approval, same, -, -⟩ |
    ⟨approval, other, maximum, -, -⟩ | ⟨approval, other, -, covered, -⟩
  · -- `approve`: the visited pair's owner word is the caller's own
    simp only [WethAllowanceInvocation.pair?, approval, ↓reduceIte, Option.some.injEq,
      Prod.mk.injEq] at pair
    exact absurd (Adr.toB256_inj pair.1) foreign
  · -- self `transferFrom`: no pair is visited
    simp [WethAllowanceInvocation.pair?, approval, same] at pair
  · -- maximum allowance: the visited cell reads `B256.max`, never zero
    have ownerEq : Sevm.argWord call.sevm 0 = vault.toB256 := by
      simp only [WethAllowanceInvocation.pair?, approval, Bool.false_eq_true, ↓reduceIte,
        if_neg other, Option.some.injEq, Prod.mk.injEq] at pair
      exact pair.1
    rw [ownerEq, quiet] at maximum
    exact absurd maximum (by decide +kernel)
  · -- finite branch: `wad ≤ cell`, and the cell reads zero
    have ownerEq : Sevm.argWord call.sevm 0 = vault.toB256 := by
      simp only [WethAllowanceInvocation.pair?, approval, Bool.false_eq_true, ↓reduceIte,
        if_neg other, Option.some.injEq, Prod.mk.injEq] at pair
      exact pair.1
    rw [ownerEq, quiet] at covered
    have h := B256.toNat_le_toNat covered
    rw [B256.toNat_zero] at h
    have h0 := Nat.le_zero.mp h
    exact B256.toNat_inj _ _ (by rwa [B256.toNat_zero])
-- case split: R:467 (`allowance_debit_classification`, the four arms in its order); the finite arm is the
-- buried `wad0`, R:906–911 (and its twin R:604–609) verbatim; the `approve` arm is the caller argument of
-- `foreign_approve_preserves_vault_allowance` (Effects:922–927).

/-- The WETH amount a step debits from the vault's row under runtime authorization, in the currency the
backing bound reads; zero for every other step. -/
def PairStep.debitAmount {vault : Adr} {before after : State} :
    PairStep vault before after → Nat
  | .authorizedDebit call _ _ _ _ _ => (Sevm.argWord call.sevm 2).toNat
  | _ => 0

/-- A step of positive debit amount is a runtime-authorized debit of that amount (the design's
constructor-shaped disjunct, recovered from the `Nat` one). -/
theorem PairStep.eq_authorizedDebit_of_debitAmount_pos {vault : Adr} {before after : State}
    (step : PairStep vault before after) (positive : 0 < step.debitAmount) :
    ∃ (call : WethAllowanceInvocation) (foreign : call.sevm.caller ≠ vault)
      (owner : Sevm.argWord call.sevm 0 = vault.toB256)
      (pair : call.pair? = some (vault.toB256, call.sevm.caller.toB256))
      (moved : Transfer (Stor.rest (before.getStor wethAccount)) vault
        (Sevm.argWord call.sevm 2) (Sevm.argWord call.sevm 1).toAdr
        (Stor.rest (after.getStor wethAccount)))
      (vaultKept : after.getStor vault = before.getStor vault),
      step = .authorizedDebit call foreign owner pair moved vaultKept ∧
        0 < (Sevm.argWord call.sevm 2).toNat := by
  cases step with
  | operation t evidence => exact absurd positive (Nat.lt_irrefl 0)
  | silent caller vaultKept rowKept => exact absurd positive (Nat.lt_irrefl 0)
  | authorizedDebit call foreign owner pair moved vaultKept =>
      exact ⟨call, foreign, owner, pair, moved, vaultKept, rfl, positive⟩

/-! ## 4. Every step keeps the supply cap -/

/-- An inbound flow lands at or below the cap: it mints at most the room its own quote retained. -/
private theorem inboundEffect_capped {sevm : Sevm} {pre post : Devm}
    {receiver assets shares returned supply : B256}
    (supplyEq : supply = Devm.getStorVal pre sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot)
    (stable : supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN)
    (room : shares.toNat ≤ Blanc.ProrataWethVault.shareRoomN supply.toNat)
    (effect : InboundEffect sevm receiver assets shares returned pre post) :
    supplyN (Devm.getStor post sevm.currentTarget) ≤ Blanc.ProrataWethVault.maxSupplyN := by
  obtain ⟨-, -, vaultStorage, -, -⟩ := effect
  have roomNat : Blanc.ProrataWethVault.shareRoomN supply.toNat =
      Blanc.ProrataWethVault.maxSupplyN - supply.toNat := rfl
  have supplyNof : B256.Nof supply shares := FourQuote.supplyNof_of_capacity stable room
  have supplyAfter : supplyN (Devm.getStor post sevm.currentTarget) =
      supply.toNat + shares.toNat := by
    show (_ : B256).toNat = _
    rw [vaultStorage, Stor.get_set_self, ← supplyEq]
    exact B256.toNat_add_eq_of_nof _ _ supplyNof
  rw [supplyAfter]
  rw [roomNat] at room
  omega
-- B:255–275 (`inboundEffect_preserves_backed`'s `roomNat`, `supplyAfter` and cap arm) with `supplyNof` from
-- A:464 instead of the inline `omega`.

/-- An outbound flow burns, so it stays below the cap it started under. -/
private theorem outboundEffect_capped {sevm : Sevm} {pre post : Devm}
    {receiver owner assets shares returned : B256}
    (burnable : shares.toNat ≤ (snapshotAt sevm pre).supply)
    (effect : OutboundEffect sevm receiver owner assets shares returned pre post)
    (capped : supplyN (Devm.getStor pre sevm.currentTarget) ≤
      Blanc.ProrataWethVault.maxSupplyN) :
    supplyN (Devm.getStor post sevm.currentTarget) ≤ Blanc.ProrataWethVault.maxSupplyN := by
  obtain ⟨-, -, -, supplyRow, -, -, -, -⟩ := effect
  have burnable' : shares.toNat ≤ supplyN (Devm.getStor pre sevm.currentTarget) := burnable
  have supplyAfter : supplyN (Devm.getStor post sevm.currentTarget) =
      supplyN (Devm.getStor pre sevm.currentTarget) - shares.toNat := by
    show (Devm.getStorVal post sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot).toNat = _
    rw [supplyRow]
    exact B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat burnable')
  rw [supplyAfter]
  omega
-- B:382–390 (`outboundEffect_preserves_backed`'s `supplyAfter` and cap arm).

/-- **The supply cap across one accepted operation.**  The two inbound tags mint within the room their
evidence retains; the four outbound tags burn; the credit keeps the vault's storage; the three share writers
keep the supply slot by their own public compiled effects. -/
theorem FourQuote.FourQuoteShareEvidence.preserves_capped
    {vault : Adr} {sevm : Sevm} {pre post : Devm}
    {operation : FourQuote.FourQuoteOperation vault sevm pre post}
    (evidence : FourQuote.FourQuoteShareEvidence operation)
    (capped : supplyN (Devm.getStor pre vault) ≤ Blanc.ProrataWethVault.maxSupplyN) :
    supplyN (Devm.getStor post vault) ≤ Blanc.ProrataWethVault.maxSupplyN := by
  cases evidence with
  | deposit words target depositorNotVault supplyNof wethRowNof quote effect receiverArg
      receiverValid supply supplyEq stable room =>
      rw [← target]
      exact inboundEffect_capped supplyEq stable room effect
  | mint words target depositorNotVault supplyNof wethRowNof quote effect receiverArg
      receiverValid supply supplyEq stable room =>
      rw [← target]
      exact inboundEffect_capped supplyEq stable room effect
  | withdrawNormal words target receiverNotVault burnable quote effect receiverArg ownerArg
      receiverValid ownerValid covered =>
      rw [← target] at capped ⊢
      exact outboundEffect_capped burnable effect capped
  | redeemNormal words target receiverNotVault burnable quote effect receiverArg ownerArg
      receiverValid ownerValid covered =>
      rw [← target] at capped ⊢
      exact outboundEffect_capped burnable effect capped
  | withdrawSelf words target receiverIsVault burnable quote effect receiverArg ownerArg
      receiverValid ownerValid covered =>
      rw [← target] at capped ⊢
      exact outboundEffect_capped burnable effect capped
  | redeemSelf words target receiverIsVault burnable quote effect receiverArg ownerArg
      receiverValid ownerValid covered =>
      rw [← target] at capped ⊢
      exact outboundEffect_capped burnable effect capped
  | credit words wethTarget sourceNotVault supplyKept rowNof effect vaultKept =>
      rw [vaultKept]
      exact capped
  | transfer words target owner receiver amount config memoryWf run selectorEq =>
      rw [← target] at capped ⊢
      obtain ⟨-, -, -, -, -, supplyKept, -⟩ :=
        Blanc.ProrataWethVault.transfer_compiled_effect memoryWf run selectorEq
      show (Devm.getStorVal post sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot).toNat ≤ _
      rw [supplyKept]
      exact capped
  | transferFrom words target spender owner receiver amount config memoryWf run selectorEq =>
      rw [← target] at capped ⊢
      obtain ⟨-, -, -, -, -, -, -, -, -, supplyKept, -⟩ :=
        Blanc.ProrataWethVault.transferFrom_compiled_effect memoryWf run selectorEq
      show (Devm.getStorVal post sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot).toNat ≤ _
      rw [supplyKept]
      exact capped
  | approve words target owner spender amount config memoryWf run selectorEq =>
      rw [← target] at capped ⊢
      obtain ⟨-, -, -, -, -, keyNotSupply, -, storageEq, -, -⟩ :=
        Blanc.ProrataWethVault.approve_compiled_effect memoryWf run selectorEq
      show ((Devm.getStor post sevm.currentTarget).get
        Blanc.ProrataWethVault.supplySlot).toNat ≤ _
      rw [storageEq, Stor.get_set_ne _ keyNotSupply]
      exact capped
-- case layout and binder names: A:1309–1350 (`preserves_conserved`), arm for arm.  Share-writer supply
-- facts: Shares:1115 (6th conjunct), :1179 (10th), :1071 (6th = key ≠ supplySlot, 8th = storage).

/-- Every classified step keeps the supply cap. -/
theorem PairStep.preserves_capped {vault : Adr} {before after : State}
    (step : PairStep vault before after)
    (capped : supplyN (before.getStor vault) ≤ Blanc.ProrataWethVault.maxSupplyN) :
    supplyN (after.getStor vault) ≤ Blanc.ProrataWethVault.maxSupplyN := by
  match step with
  | .operation t evidence =>
      have entry : Devm.getStor t.entry vault = before.getStor vault :=
        congrArg (fun w : State => w.getStor vault) t.preState
      have exit : Devm.getStor t.exit vault = after.getStor vault :=
        congrArg (fun w : State => w.getStor vault) t.postState
      rw [← entry] at capped
      rw [← exit]
      exact evidence.preserves_capped capped
  | .authorizedDebit _ _ _ _ _ vaultKept =>
      rw [vaultKept]
      exact capped
  | .silent _ vaultKept _ =>
      rw [vaultKept]
      exact capped
-- L:88–111 (`PairStep.conserved`), same three arms.

/-- A connected replay carries the cap from its first boundary to its last. -/
theorem PairReplay.capped {vault : Adr} {pre post : PairBoundary}
    {steps : List (PairStepRecord vault)} (replay : PairReplay vault pre steps post) :
    supplyN pre.vault ≤ Blanc.ProrataWethVault.maxSupplyN →
      supplyN post.vault ≤ Blanc.ProrataWethVault.maxSupplyN := by
  induction replay with
  | nil boundary => exact id
  | @cons pre mid post record steps preEq postEq tail ih =>
      intro capped
      subst preEq
      subst postEq
      exact ih (record.step.preserves_capped capped)

/-! ## 5. Every step that debits nothing is priced -/

/-- A step of zero debit amount weakly raises the virtual price per share: an accepted operation by its
own four-quote recurrence; a silent step and a zero-amount authorized debit because both coordinates are
kept. -/
theorem PairStep.priceLe_of_debitAmount_eq_zero {vault : Adr} {before after : State}
    (step : PairStep vault before after) (zero : step.debitAmount = 0) :
    Blanc.Prorata.PriceLe Blanc.ProrataWethVault.offsetN
      (FourQuote.stateSnapshot vault before) (FourQuote.stateSnapshot vault after) := by
  match step, zero with
  | .operation t _, _ =>
      simpa only [FourQuote.vaultSnapshot_state, t.preState, t.postState] using
        t.operation.priceLe
  | .authorizedDebit call _ _ _ moved vaultKept, zero =>
      have wad0 : Sevm.argWord call.sevm 2 = 0 :=
        B256.toNat_inj _ _ (by rw [B256.toNat_zero]; exact zero)
      rw [wad0] at moved
      have same : FourQuote.stateSnapshot vault after =
          FourQuote.stateSnapshot vault before := by
        unfold FourQuote.stateSnapshot
        rw [vaultKept, transfer_src_row_of_zero moved]
      rw [same]
      exact Blanc.Prorata.PriceLe.refl _ _
  | .silent _ vaultKept rowKept, _ =>
      have same : FourQuote.stateSnapshot vault after =
          FourQuote.stateSnapshot vault before := by
        unfold FourQuote.stateSnapshot
        rw [vaultKept, rowKept]
      rw [same]
      exact Blanc.Prorata.PriceLe.refl _ _
-- operation arm: A:2295–2303 (`priceLe_step_at`'s closing `simpa only`); the other two are new.

/-- A connected replay whose steps debit nothing is priced end to end. -/
theorem PairReplay.priceLe {vault : Adr} {pre post : PairBoundary}
    {steps : List (PairStepRecord vault)} (replay : PairReplay vault pre steps post) :
    (∀ r ∈ steps, r.step.debitAmount = 0) →
      Blanc.Prorata.PriceLe Blanc.ProrataWethVault.offsetN
        (pre.snapshot vault) (post.snapshot vault) := by
  induction replay with
  | nil boundary => exact fun _ => Blanc.Prorata.PriceLe.refl _ _
  | @cons pre mid post record steps preEq postEq tail ih =>
      intro zero
      subst preEq
      subst postEq
      have head := record.step.priceLe_of_debitAmount_eq_zero (zero record (by simp))
      rw [← PairBoundary.snapshot_ofState, ← PairBoundary.snapshot_ofState] at head
      exact Blanc.Prorata.PriceLe.trans Blanc.ProrataWethVault.offsetN_ne_zero head
        (ih fun r member => zero r (by simp [member]))

/-- **Unconditional classification of a replay.**  A connected replay is priced end to end, or it retains a
runtime-authorized debit of positive amount. -/
theorem PairReplay.priceLe_or_debit {vault : Adr} {pre post : PairBoundary}
    {steps : List (PairStepRecord vault)} (replay : PairReplay vault pre steps post) :
    Blanc.Prorata.PriceLe Blanc.ProrataWethVault.offsetN
        (pre.snapshot vault) (post.snapshot vault) ∨
      ∃ r ∈ steps, 0 < r.step.debitAmount := by
  by_cases zero : ∀ r ∈ steps, r.step.debitAmount = 0
  · exact .inl (replay.priceLe zero)
  · push Not at zero
    obtain ⟨r, member, positive⟩ := zero
    exact .inr ⟨r, member, Nat.pos_of_ne_zero positive⟩

end Blanc.Composition.ProrataWethVault

namespace Blanc.Composition.ProrataWethVault

open Jaune
open _root_.Blanc.ExecutionTrace

/-! ## 6. The raw allowance ledger is a rooted chronology -/

/-- The machine the rooted chronology's root constructor is stated at, for a pair root: WETH is no
precompile because this rule set activates none.  Only its inhabitation is used; the chronology's own root
indices are `Stor.empty`, and `PairRoot.wethEmpty` supplies the continuity. -/
def pairRootSevm : Sevm :=
  { (default : Sevm) with
    benvStat := { (default : Sevm).benvStat with
      rules := { (default : ForkRules) with precompiles := [] } } }

/-- The machine state at a world: the world, and defaults elsewhere. -/
def pairRootDevm (w : State) : Devm :=
  { (default : Devm) with world := { (default : Devm).world with state := w } }

/-- A pair root is an allowance root: both runtimes installed, the vault untouched, WETH empty. -/
theorem AllowanceRoot.of_pairRoot {cfg : ChainConfig} {deployed : BlockChain} {vault : Adr}
    (root : PairRoot cfg deployed vault) :
    AllowanceRoot vault pairRootSevm (pairRootDevm deployed.state) where
  configured :=
    { configured :=
        { distinct := root.distinct
          nonprecompile := by simp [pairRootSevm, ForkRules.isPrecomp]
          code := by
            show (deployed.state.getCode wethAccount).toList = Blanc.wethCode
            exact root.wethInstalled }
      installed := by
        show some (deployed.state.getCode vault).toList = _
        exact root.vaultInstalled
      untouched := fun key => by
        show (deployed.state.getStor vault).get key = 0
        rw [root.vaultEmpty]
        rfl }
  wethEmpty := by
    show deployed.state.getStor wethAccount = Stor.empty
    exact root.wethEmpty
-- new; field shapes: R:647–653 (`AllowanceRoot`), Message.lean:526–535 (`ConfiguredRoot`),
-- Boundary.lean:40–44; the `show … getCode` pattern is Pair.lean:175 (`PairStable.configuration`).

/-- **A pair replay extends a rooted chronology by its own ledger.**  A record that owns an invocation is an
`invoked` step, by its `linked` field; a record that owns none is a `silent` step, by its `quiet` field and
the non-address shape of every touched allowance key. -/
theorem PairReplay.rootedAllowanceHistory {vault : Adr} {full : List WethAllowanceInvocation}
    {pre post : PairBoundary} {steps : List (PairStepRecord vault)}
    (replay : PairReplay vault pre steps post) :
    ∀ {done : List WethAllowanceInvocation} {s : Stor},
      RootedAllowanceHistory vault full done s pre.weth →
      (∀ call ∈ PairStepRecord.ledger steps, call ∈ full) →
      RootedAllowanceHistory vault full (done ++ PairStepRecord.ledger steps) s post.weth := by
  induction replay with
  | nil boundary =>
      intro done s chain _
      simpa [PairStepRecord.ledger] using chain
  | @cons pre mid post record steps preEq postEq tail ih =>
      intro done s chain sub
      subst preEq
      subst postEq
      cases hown : record.own with
      | none =>
          have ledgerEq : PairStepRecord.ledger (record :: steps) =
              PairStepRecord.ledger steps := by
            simp [PairStepRecord.ledger, hown]
          rw [ledgerEq] at sub ⊢
          refine ih (.silent done s _ _ chain ?_) sub
          intro p touched _
          exact record.quiet hown _ (touchedWethAllowancePairs_keys_nonaddress touched)
      | some call =>
          obtain ⟨preLink, postLink, staged⟩ := record.linked call hown
          have ledgerEq : PairStepRecord.ledger (record :: steps) =
              call :: PairStepRecord.ledger steps := by
            simp [PairStepRecord.ledger, hown]
          rw [ledgerEq] at sub ⊢
          have step : RootedAllowanceHistory vault full (done ++ [call]) s
              (record.after.getStor wethAccount) :=
            .invoked done s _ _ call chain (sub call (by simp)) preLink postLink.symm staged
          have tailChain := ih step (fun c member => sub c (by simp [member]))
          simpa only [List.append_assoc, List.singleton_append] using tailChain
-- constructors R:809–830; key shape R:435.  Induction shape L:113–124.

/-! ## 7. R10: the realized history carrier -/

/-- **R10.**  A realized pair history: in chain order, one retained configured block per imported block,
each with its own connected pair replay whose records carry that block's header number. -/
inductive PairTraceRealizes {cfg : ChainConfig} {deployed : BlockChain} {vault : Adr}
    (root : PairRoot cfg deployed vault) :
    List (PairStepRecord vault) → BlockChain → Prop where
  | refl : PairTraceRealizes root [] deployed
  | step {current future : BlockChain} {priorSteps blockSteps : List (PairStepRecord vault)}
      (prior : PairTraceRealizes root priorSteps current)
      (block : ConfiguredBlockTrace cfg current future)
      (replay : PairReplay vault (PairBoundary.ofState vault current.state) blockSteps
        (PairBoundary.ofState vault future.state))
      (tagged : ∀ r ∈ blockSteps, PairInBlock block.block.header.number r) :
      PairTraceRealizes root (priorSteps ++ blockSteps) future
-- PH:96–107 / G:625–634; `tagged` is new (§8 item 3).

namespace PairTraceRealizes

variable {cfg : ChainConfig} {deployed : BlockChain} {vault : Adr}
  {root : PairRoot cfg deployed vault}

/-- Every realized trace projects to the configured reach it replays. -/
theorem toReachUsing {steps : List (PairStepRecord vault)} {future : BlockChain}
    (realizes : PairTraceRealizes root steps future) :
    BlockChain.ReachUsing cfg deployed future := by
  induction realizes with
  | refl => exact root.reflReach
  | step prior block replay tagged ih => exact .step ih block.bound block.transition
-- PH:116–123 / G:640–648.

/-- The realized steps are one connected pair replay from the root to the continuation. -/
theorem toReplay {steps : List (PairStepRecord vault)} {future : BlockChain}
    (realizes : PairTraceRealizes root steps future) :
    PairReplay vault (PairBoundary.ofState vault deployed.state) steps
      (PairBoundary.ofState vault future.state) := by
  induction realizes with
  | refl => exact .nil _
  | step prior block replay tagged ih => exact ih.append replay
-- PH:128–137 / G:652–660.

/-- Every realized continuation carries the pair's unconditional invariant. -/
theorem worldInv {steps : List (PairStepRecord vault)} {future : BlockChain}
    (realizes : PairTraceRealizes root steps future) : PairWorldInv vault future.state := by
  rcases exists_configuredHistoryTrace_of_reachUsing realizes.toReachUsing with ⟨history⟩
  exact PairWorldInv.of_history root history

/-- The supply cap holds at every realized continuation, unconditionally. -/
theorem capped {steps : List (PairStepRecord vault)} {future : BlockChain}
    (realizes : PairTraceRealizes root steps future) :
    supplyN (future.state.getStor vault) ≤ Blanc.ProrataWethVault.maxSupplyN := by
  apply realizes.toReplay.capped
  show supplyN (deployed.state.getStor vault) ≤ _
  rw [root.vaultEmpty]
  have zero : supplyN Stor.empty = 0 := rfl
  rw [zero]
  exact Nat.zero_le _

/-- **SF §7 clause 8.**  The raw allowance ledger of a realized trace is a rooted chronology from the pair
root's empty WETH storage to the continuation's. -/
theorem rootedAllowanceHistory {steps : List (PairStepRecord vault)} {future : BlockChain}
    (realizes : PairTraceRealizes root steps future) :
    RootedAllowanceHistory vault (PairStepRecord.ledger steps) (PairStepRecord.ledger steps)
      Stor.empty (future.state.getStor wethAccount) := by
  have start : RootedAllowanceHistory vault (PairStepRecord.ledger steps) [] Stor.empty
      (PairBoundary.ofState vault deployed.state).weth := by
    show RootedAllowanceHistory vault _ [] Stor.empty (deployed.state.getStor wethAccount)
    rw [root.wethEmpty]
    exact .root (AllowanceRoot.of_pairRoot root)
  have chain := realizes.toReplay.rootedAllowanceHistory start (fun _ member => member)
  simpa only [List.nil_append, PairBoundary.ofState] using chain

/-- The rooted foreign-debit exclusion over a realized trace (cell altitude). -/
theorem foreign_debit_excluded {steps : List (PairStepRecord vault)} {future : BlockChain}
    (realizes : PairTraceRealizes root steps future)
    (collision : NoVaultAllowanceKeyCollision (PairStepRecord.ledger steps) vault)
    (call : WethAllowanceInvocation) (member : call ∈ PairStepRecord.ledger steps)
    (foreign : call.sevm.caller ≠ vault)
    (p : B256 × B256) (touched : p ∈ touchedWethAllowancePairs (PairStepRecord.ledger steps))
    (owner : p.1 = vault.toB256) :
    call.post.getStorVal wethAccount (wethAllowanceKey p.1 p.2) =
      call.pre.getStorVal wethAccount (wethAllowanceKey p.1 p.2) :=
  foreign_debit_excluded_rooted realizes.rootedAllowanceHistory collision call member foreign
    p touched owner
-- R:957–969 at the realized ledger.

/-- **Hardened no-foreign-debit at row altitude** (goal control 4; SF §6).  Under D9, every
runtime-authorized debit step of a realized trace has amount zero and leaves the vault's WETH row exactly
where it was. -/
theorem authorizedDebit_zero {steps : List (PairStepRecord vault)} {future : BlockChain}
    (realizes : PairTraceRealizes root steps future)
    (collision : NoVaultAllowanceKeyCollision (PairStepRecord.ledger steps) vault)
    {r : PairStepRecord vault} (member : r ∈ steps)
    {call : WethAllowanceInvocation} {foreign : call.sevm.caller ≠ vault}
    {owner : Sevm.argWord call.sevm 0 = vault.toB256}
    {pair : call.pair? = some (vault.toB256, call.sevm.caller.toB256)}
    {moved : Transfer (Stor.rest (r.before.getStor wethAccount)) vault
      (Sevm.argWord call.sevm 2) (Sevm.argWord call.sevm 1).toAdr
      (Stor.rest (r.after.getStor wethAccount))}
    {vaultKept : r.after.getStor vault = r.before.getStor vault}
    (debit : r.step = .authorizedDebit call foreign owner pair moved vaultKept) :
    Sevm.argWord call.sevm 2 = 0 ∧
      Stor.rest (r.after.getStor wethAccount) vault =
        Stor.rest (r.before.getStor wethAccount) vault := by
  have own : r.own = some call := r.debitOwn call foreign owner pair moved vaultKept debit
  have callMember : call ∈ PairStepRecord.ledger steps :=
    List.mem_filterMap.mpr ⟨r, member, own⟩
  have touched : (vault.toB256, call.sevm.caller.toB256) ∈
      touchedWethAllowancePairs (PairStepRecord.ledger steps) :=
    List.mem_filterMap.mpr ⟨call, callMember, pair⟩
  have quiet := (realizes.rootedAllowanceHistory.all_quiet collision).2 call callMember
    _ touched rfl
  have wad0 := call.vaultDebit_wad_eq_zero foreign pair quiet
  refine ⟨wad0, ?_⟩
  have zeroMoved := moved
  rw [wad0] at zeroMoved
  exact transfer_src_row_of_zero zeroMoved
-- `quiet` at the call's own pre-state: R:832 (`all_quiet`'s second conjunct); membership projections
-- Effects:865 / H:65; the rest is §3.

/-- Under D9 no step of a realized trace debits anything. -/
theorem debitAmount_eq_zero {steps : List (PairStepRecord vault)} {future : BlockChain}
    (realizes : PairTraceRealizes root steps future)
    (collision : NoVaultAllowanceKeyCollision (PairStepRecord.ledger steps) vault) :
    ∀ r ∈ steps, r.step.debitAmount = 0 := by
  rintro ⟨before, after, step, own, linked, quiet, debitOwn, provenance, actor⟩ member
  cases step with
  | operation t evidence => rfl
  | silent caller vaultKept rowKept => rfl
  | authorizedDebit call foreign owner pair moved vaultKept =>
      have zero := (realizes.authorizedDebit_zero collision member rfl).1
      show (Sevm.argWord call.sevm 2).toNat = 0
      rw [zero]
      rfl

/-- The backing number under D9: the price never falls from genesis. -/
theorem backing {steps : List (PairStepRecord vault)} {future : BlockChain}
    (realizes : PairTraceRealizes root steps future)
    (collision : NoVaultAllowanceKeyCollision (PairStepRecord.ledger steps) vault) :
    supplyN (future.state.getStor vault) ≤
      Blanc.ProrataWethVault.offsetN *
        (Stor.rest (future.state.getStor wethAccount) vault).toNat := by
  have price := realizes.toReplay.priceLe (realizes.debitAmount_eq_zero collision)
  rw [PairBoundary.snapshot_ofState, PairBoundary.snapshot_ofState,
    root.genesisSnapshot] at price
  exact Blanc.Prorata.backed_of_priceLe_genesis price
-- A:2329–2337 (`FourQuotePath.supply_le_offset_mul_balance`) over the replay.

end PairTraceRealizes

/-- Every retained configured history from the pair root is realized. -/
theorem pairTraceRealizes_of_configuredHistoryTrace {cfg : ChainConfig}
    {deployed future : BlockChain} {vault : Adr} (root : PairRoot cfg deployed vault)
    (history : ConfiguredHistoryTrace cfg deployed future) :
    ∃ steps, PairTraceRealizes root steps future := by
  induction history with
  | refl hcfg hctx hid => exact ⟨[], .refl⟩
  | step prior block ih =>
      obtain ⟨priorSteps, priorRealizes⟩ := ih
      obtain ⟨blockSteps, blockReplay, blockTagged⟩ :=
        retainedConfiguredBlockPairReplay block (PairWorldInv.of_history root prior)
          (root.notPrecompile block.rulesAt).2 block.block.header.number
      exact ⟨priorSteps ++ blockSteps, .step priorRealizes block blockReplay blockTagged⟩
-- PH:146–159 / G:664–677; `root.reachable_stateInv prior.toReachUsing` → `PairWorldInv.of_history root
-- prior` (L:750 at last read); the rules fact is R9's `schedule block.rulesAt` (L:720 at last read).

/-- **Non-vacuity.**  Configured reachability from the pair root is never more permissive than the
carrier; with `PairTraceRealizes.toReachUsing` the carrier is pinned exactly onto chain reachability. -/
theorem pairTraceRealizes_exists_of_reachUsing {cfg : ChainConfig}
    {deployed future : BlockChain} {vault : Adr} (root : PairRoot cfg deployed vault)
    (reach : BlockChain.ReachUsing cfg deployed future) :
    ∃ steps, PairTraceRealizes root steps future := by
  rcases exists_configuredHistoryTrace_of_reachUsing reach with ⟨history⟩
  exact pairTraceRealizes_of_configuredHistoryTrace root history
-- PH:167–173 / G:682–690.

/-! ## 8. The headlines -/

/-- **Unconditional classification headline (no D9).**  Every configured continuation of the pair root is
backed, or its realized trace retains a runtime-authorized debit of positive amount. -/
theorem pair_reachable_backed_or_debit {cfg : ChainConfig} {deployed future : BlockChain}
    {vault : Adr} (root : PairRoot cfg deployed vault)
    (reach : BlockChain.ReachUsing cfg deployed future) :
    ∃ steps, PairTraceRealizes root steps future ∧
      (PairBacked vault (future.state.getStor vault) (future.state.getStor wethAccount) ∨
        ∃ r ∈ steps, 0 < r.step.debitAmount) := by
  obtain ⟨steps, realizes⟩ := pairTraceRealizes_exists_of_reachUsing root reach
  refine ⟨steps, realizes, ?_⟩
  rcases realizes.toReplay.priceLe_or_debit with price | debit
  · rw [PairBoundary.snapshot_ofState, PairBoundary.snapshot_ofState,
      root.genesisSnapshot] at price
    exact .inl ⟨realizes.worldInv.conserved, realizes.capped,
      Blanc.Prorata.backed_of_priceLe_genesis price⟩
  · exact .inr debit

/-- **The final backing corollary** (goal G6 last clause; SF §7 last bullet), limited exactly by D9. -/
theorem pair_reachable_stable {cfg : ChainConfig} {deployed : BlockChain} {vault : Adr}
    (root : PairRoot cfg deployed vault)
    {steps : List (PairStepRecord vault)} {future : BlockChain}
    (realizes : PairTraceRealizes root steps future)
    (collision : NoVaultAllowanceKeyCollision (PairStepRecord.ledger steps) vault)
    {timestamp : Nat} {rules : ForkRules} (rulesAt : cfg.rulesAt timestamp = .ok rules) :
    PairStable vault rules future.state := by
  rcases exists_configuredHistoryTrace_of_reachUsing realizes.toReachUsing with ⟨history⟩
  exact PairStable.of_history root history rulesAt realizes.capped
    (realizes.backing collision)

/-- The backing corollary's two halves: the joint invariant and WETH's own state invariant. -/
theorem pair_reachable_backed {cfg : ChainConfig} {deployed : BlockChain} {vault : Adr}
    (root : PairRoot cfg deployed vault)
    {steps : List (PairStepRecord vault)} {future : BlockChain}
    (realizes : PairTraceRealizes root steps future)
    (collision : NoVaultAllowanceKeyCollision (PairStepRecord.ledger steps) vault) :
    PairBacked vault (future.state.getStor vault) (future.state.getStor wethAccount) ∧
      State.Inv wethAccount future.state := by
  obtain ⟨vaultInv, wethInv, -, -, -⟩ := realizes.worldInv
  exact ⟨⟨vaultInv.inv, realizes.capped, realizes.backing collision⟩,
    wethSpec_stateInv_iff.mp wethInv⟩
-- rules-free projection: no `rulesAt` is needed for these two conjuncts (PairStable.wethInv,
-- Pair.lean:122, would need one via `pair_reachable_stable`); `wethSpec_stateInv_iff` Solvent.lean:181.

end Blanc.Composition.ProrataWethVault
