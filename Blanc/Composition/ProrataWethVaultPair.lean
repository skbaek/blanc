-- ProrataWethVaultPair.lean : the joint vault/WETH root and stable boundary.

import Blanc.Composition.ProrataWethVaultMessage
import Blanc.Composition.ProrataWethVaultViews
import Blanc.Solvent

/-!
# The pair's root and its stable boundary

`PairBacked` (`Blanc/Composition/ProrataWethVaultBacking.lean`) is a statement
about two storage maps.  This module names the two *worlds* the ladder travels
between: the post-installation root a pair history starts from, and the settled
state a history rests at between messages.

Three things decide the shapes.

* A stable boundary is a `State`, as `Weth10.Stable` and
  `Prorata.DeploymentRoot` are.  A `State` has no live frame, so the clauses
  that mention one — the `totalAssets()` word, the absence of an in-flight
  vault→WETH child — are theorems *about* this state rather than fields of it.
* The root mirrors `Prorata.DeploymentRoot` field for field, with the second
  runtime added.  Both runtimes are installed directly: no CREATE theorem is
  claimed, and the deployment transaction is outside every history rooted here.
* WETH solvency across a vault message is not a new walk over WETH's program.
  The vault frame spawns WETH children, but `weth_preserves_solvent`
  (`Blanc/Solvent.lean`) is the generic frame-level ladder rung and is already
  quantified over *every* frame: its only premise about the running code is
  that a frame whose target is the asset runs the asset's program.  At a vault
  frame that premise is discharged by `wethAccount ≠ vault` and nothing else is
  needed — the children are inside the `Exec` the rung consumes.  See
  `vault_processMessage_preserves_stable` below.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune

/-! ## The post-installation root -/

/-- SF §7 clauses 1–2 at a configured chain checkpoint: the post-installation
root of every pair history.  Mirrors `Prorata.DeploymentRoot`
(`Blanc/ProrataDeploymentRoot.lean`); the two runtimes are installed directly,
so no CREATE theorem is claimed and the deployment transaction itself is
outside every continuation rooted here. -/
structure PairRoot (cfg : ChainConfig) (deployed : BlockChain) (vault : Adr) :
    Prop where
  /-- The schedule is a valid one. -/
  configValid : cfg.Valid
  /-- The checkpoint's own block context is valid. -/
  validContext : deployed.ValidContext
  /-- The schedule and the checkpoint agree on the chain. -/
  chainId : cfg.chainId = deployed.chainId
  /-- The asset is not the vault. -/
  distinct : wethAccount ≠ vault
  /-- The vault is not the zero account. -/
  vaultNonzero : vault ≠ 0
  /-- Neither account is the system sender, so the root envelope can exclude a
  system transaction's message at the pair. -/
  vaultNotSystem : vault ≠ systemAddress
  /-- The asset is not the system sender either. -/
  wethNotSystem : wethAccount ≠ systemAddress
  /-- Under any rules the schedule selects, neither account is a precompile. -/
  notPrecompile : ∀ {timestamp rules}, cfg.rulesAt timestamp = .ok rules →
    rules.isPrecomp vault = false ∧ rules.isPrecomp wethAccount = false
  /-- The vault runtime is installed at the vault. -/
  vaultInstalled : some (deployed.state.getCode vault).toList =
    Prog.compile Blanc.ProrataWethVault.vault
  /-- The inherited WETH runtime is installed at the asset. -/
  wethInstalled : (deployed.state.getCode wethAccount).toList = Blanc.wethCode
  /-- The vault has issued nothing. -/
  vaultEmpty : deployed.state.getStor vault = Stor.empty
  /-- The asset has booked nothing. -/
  wethEmpty : deployed.state.getStor wethAccount = Stor.empty
  /-- The world's balance sum cannot overflow a word. -/
  sumNof : SumNof deployed.state.bal

/-! ## The stable boundary -/

/-- SF §7 clauses 1–7 at a settled world under the rules in force.

Clause 4 (`A` is the successful `totalAssets()` word) and clause 7 (no active
vault→WETH child) are theorems about this state rather than fields: a `State`
has no live frame, and the returned word is read off the compiled program by
`PairStable.totalAssets`.  Clause 8 (the raw allowance ledger) belongs to the
history carrier, where D9 can be applied to it, and is deliberately absent
here. -/
structure PairStable (vault : Adr) (rules : ForkRules) (w : Jaune.State) :
    Prop where
  /-- The vault runtime is installed at the vault. -/
  vaultInstalled : some (w.getCode vault).toList =
    Prog.compile Blanc.ProrataWethVault.vault
  /-- The inherited WETH runtime is installed at the asset. -/
  wethInstalled : (w.getCode wethAccount).toList = Blanc.wethCode
  /-- The asset is not the vault. -/
  distinct : wethAccount ≠ vault
  /-- The vault is not the zero account. -/
  vaultNonzero : vault ≠ 0
  /-- The vault is not a precompile under the rules in force. -/
  vaultNonprecompile : rules.isPrecomp vault = false
  /-- The asset is not a precompile under the rules in force. -/
  wethNonprecompile : rules.isPrecomp wethAccount = false
  /-- SF §7 clauses 3 and 5: the joint two-contract backing invariant. -/
  backed : PairBacked vault (w.getStor vault) (w.getStor wethAccount)
  /-- The world's balance sum cannot overflow a word. -/
  sumNof : SumNof w.bal
  /-- SF §7 clause 6: the asset's own solvency. -/
  wethSolvent : State.Solvent w wethAccount

/-- An empty storage map books nothing at its address-shaped keys. -/
private theorem balSum_empty : balSum Stor.empty = 0 := by
  have step : ∀ n, sumBelow (Stor.rest Stor.empty) n = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [sumBelow_succ, ih,
          show Stor.rest Stor.empty (Nat.toAdr n) = (0 : B256) from rfl,
          B256.toNat_zero]
  exact step _

/-- The asset's clauses, in the shape the generic ladder consumes. -/
theorem PairStable.wethInv {vault : Adr} {rules : ForkRules} {w : Jaune.State}
    (h : PairStable vault rules w) : State.Inv wethAccount w := by
  refine ⟨?_, h.sumNof, h.wethSolvent⟩
  rw [h.wethInstalled, Blanc.wethCode_compile]

/-- The asset's booked-balance sum cannot overflow, because it is bounded by
the ETH the asset actually holds.  This is the `wethSumNof` that
`vault_message_preserves_backed` does *not* take as a premise. -/
theorem PairStable.wethRowSumNof {vault : Adr} {rules : ForkRules}
    {w : Jaune.State} (h : PairStable vault rules w) :
    SumNof (Stor.rest (w.getStor wethAccount)) := by
  have solvent : balSum (w.getStor wethAccount) + (0 : B256).toNat ≤
      (w.bal wethAccount).toNat := h.wethSolvent
  have bound : (w.bal wethAccount).toNat < 2 ^ 256 :=
    B256.toNat_lt (w.bal wethAccount)
  show sum (Stor.rest (w.getStor wethAccount)) < 2 ^ 256
  have expand : balSum (w.getStor wethAccount) =
      sum (Stor.rest (w.getStor wethAccount)) := rfl
  omega

/-- **The root is stable.**  Everything but the invariant is carried across
verbatim; the invariant itself holds for the reason genesis always does — an
empty ledger is conserved, issues nothing, and books nothing. -/
theorem PairStable.of_root {cfg : ChainConfig} {deployed : BlockChain}
    {vault : Adr} (root : PairRoot cfg deployed vault)
    {timestamp : Nat} {rules : ForkRules}
    (rulesAt : cfg.rulesAt timestamp = .ok rules) :
    PairStable vault rules deployed.state := by
  obtain ⟨vaultPrecomp, wethPrecomp⟩ := root.notPrecompile rulesAt
  refine ⟨root.vaultInstalled, root.wethInstalled, root.distinct,
    root.vaultNonzero, vaultPrecomp, wethPrecomp, ?_, root.sumNof, ?_⟩
  · refine PairBacked.of_vault_empty ?_
    intro key
    rw [root.vaultEmpty]
    rfl
  · show balSum (deployed.state.getStor wethAccount) + (0 : B256).toNat ≤
      (deployed.state.bal wethAccount).toNat
    rw [root.wethEmpty, balSum_empty]
    exact Nat.zero_le _

/-! ## What a frame opened on a stable world sees -/

/-- The frame-entry form every rung consumes: a frame opened on a stable world
carries the exact configuration, so no rung has to assume the asset's identity
out of the air. -/
theorem PairStable.configuration {vault : Adr} {rules : ForkRules}
    {w : Jaune.State} (h : PairStable vault rules w)
    {sevm : Sevm} {pre : Devm}
    (state : pre.state = w) (stat : sevm.benvStat.rules = rules) :
    DirectWethConfiguration vault sevm pre := by
  refine ⟨h.distinct, ?_, ?_⟩
  · rw [stat]
    exact h.wethNonprecompile
  · show (pre.state.getCode wethAccount).toList = Blanc.wethCode
    rw [state]
    exact h.wethInstalled

/-- **SF §7 clause 4.**  `A` is the word a successful `totalAssets()` returns.

The clause is a theorem rather than a field of `PairStable` because a settled
world has no live frame: the word is read off the compiled program, at whatever
frame a caller opens on this state. -/
theorem PairStable.totalAssets {vault : Adr} {rules : ForkRules}
    {w : Jaune.State} (h : PairStable vault rules w)
    {sevm : Sevm} {pre post : Devm}
    (state : pre.state = w) (stat : sevm.benvStat.rules = rules)
    (target : sevm.currentTarget = vault) (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (sel : Sevm.selector sevm = selector "totalAssets" []) :
    Blanc.ProrataWethVault.WordViewEffect
      ((w.getStor wethAccount).get vault.toB256) pre post := by
  have config : DirectWethConfiguration sevm.currentTarget sevm pre := by
    rw [target]
    exact h.configuration state stat
  obtain ⟨-, effect⟩ := totalAssets_compiled_effect config memoryWf run sel
  rwa [state, target] at effect

/-- **The final backing corollary**, in the clause-implied form and no
stronger: the whole supply is redeemable against the WETH row the vault holds,
and the asset's own booked balances are covered by the ETH it holds. -/
theorem PairStable.redeemable_and_solvent {vault : Adr} {rules : ForkRules}
    {w : Jaune.State} (h : PairStable vault rules w) :
    Blanc.ProrataWethVault.convertToAssetsN (supplyN (w.getStor vault))
        (Stor.rest (w.getStor wethAccount) vault).toNat
        (supplyN (w.getStor vault)) ≤
      (Stor.rest (w.getStor wethAccount) vault).toNat ∧
    balSum (w.getStor wethAccount) ≤ (w.bal wethAccount).toNat := by
  refine ⟨h.backed.redeemable, ?_⟩
  have solvent : balSum (w.getStor wethAccount) + (0 : B256).toNat ≤
      (w.bal wethAccount).toNat := h.wethSolvent
  rw [B256.toNat_zero] at solvent
  omega

/-! ## One vault message preserves the joint invariant

The 25-target split is not repeated here.  Twenty-one of the targets move
neither coordinate the invariant reads, and `nonflow_message_accountingStep`
already holds that case analysis once; the four ERC-4626 flows reach their
exact compiled effects.  So the split below is five-way, and each flow arm is
its effect theorem followed by the matching backing lemma with the matching
rounding bound. -/

/-- The outbound self-payout arm.

ERC-4626 does not forbid naming the vault itself as the receiver, and
`outboundEffect_preserves_backed` deliberately speaks only about distinct
accounts — the transfer projections it uses do.  The degenerate case is
discharged here rather than excluded by a premise the caller could not check:
the WETH movement nets to zero at the vault's own row while the burn still
lowers the supply, so the bound can only get slacker. -/
private theorem outboundEffect_preserves_backed_self
    {sevm : Sevm} {pre post : Devm}
    {receiver owner assets shares returned : B256}
    (receiverIsVault : sevm.currentTarget = receiver.toAdr)
    (ownerValid : ValidAdr owner)
    (covered : shares.toNat ≤
      (Devm.getStorVal pre sevm.currentTarget owner).toNat)
    (burnable : shares.toNat ≤ supplyN (Devm.getStor pre sevm.currentTarget))
    (effect :
      OutboundEffect sevm receiver owner assets shares returned pre post)
    (backed : PairBacked sevm.currentTarget
      (Devm.getStor pre sevm.currentTarget)
      (Devm.getStor pre wethAccount)) :
    PairBacked sevm.currentTarget
      (Devm.getStor post sevm.currentTarget)
      (Devm.getStor post wethAccount) := by
  obtain ⟨conserved, capped, bound⟩ := backed
  have effectWhole := effect
  obtain ⟨-, movement, -, supplyRow, -, -, -, -⟩ := effect
  rw [← receiverIsVault] at movement
  obtain ⟨-, mid, decrease, increase⟩ := movement
  have debited : Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget -
      assets = mid sevm.currentTarget :=
    (decrease sevm.currentTarget).1 rfl
  have credited : mid sevm.currentTarget + assets =
      Stor.rest (Devm.getStor post wethAccount) sevm.currentTarget :=
    (increase sevm.currentTarget).1 rfl
  have rowKept : Stor.rest (Devm.getStor post wethAccount) sevm.currentTarget =
      Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget := by
    rw [← credited, ← debited]
    exact B256.sub_add_cancel
  have supplyAfter : supplyN (Devm.getStor post sevm.currentTarget) =
      supplyN (Devm.getStor pre sevm.currentTarget) - shares.toNat := by
    show (Devm.getStorVal post sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot).toNat = _
    rw [supplyRow]
    exact B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat burnable)
  refine ⟨outboundEffect_preserves_conserved ownerValid covered effectWhole
    conserved, ?_, ?_⟩
  · rw [supplyAfter]
    omega
  · rw [supplyAfter, rowKept]
    omega

/-- **One vault message preserves `PairBacked`** (SF ladder bullet 2,
stable→stable) at `RunCompiled` altitude.

`wethSumNof` is a premise here and a consequence of the stable world one rung
up (`PairStable.wethRowSumNof`); `callerNotVault` is a premise here and is
derived from the root envelope by the history carrier. -/
theorem vault_message_preserves_backed
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (callerNotVault : sevm.caller ≠ sevm.currentTarget)
    (wethSumNof : SumNof (Stor.rest (Devm.getStor pre wethAccount)))
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (backed : PairBacked sevm.currentTarget
      (Devm.getStor pre sevm.currentTarget)
      (Devm.getStor pre wethAccount)) :
    PairBacked sevm.currentTarget
      (Devm.getStor post sevm.currentTarget)
      (Devm.getStor post wethAccount) := by
  by_cases isDeposit :
      Sevm.selector sevm = selector "deposit" [.uint256, .address]
  · obtain ⟨-, supply, supplyEq, stable, fits, -, receiverValid, -, roomFits,
        effect⟩ := deposit_compiled_effect config memoryWf run isDeposit
    refine inboundEffect_preserves_backed callerNotVault receiverValid
      wethSumNof supplyEq stable roomFits ?_ effect backed
    rw [B256.toNat_toB256_of_lt fits, Nat.mul_comm]
    exact Blanc.ProrataWethVault.convertToSharesN_floor_le _ _ _
  by_cases isMint : Sevm.selector sevm = selector "mint" [.uint256, .address]
  · obtain ⟨-, supply, supplyEq, stable, fits, -, receiverValid, -, roomFits,
        effect⟩ := mint_compiled_effect config memoryWf run isMint
    refine inboundEffect_preserves_backed callerNotVault receiverValid
      wethSumNof supplyEq stable roomFits ?_ effect backed
    rw [B256.toNat_toB256_of_lt fits]
    exact Blanc.ProrataWethVault.previewMintN_covers _ _ _
  by_cases isWithdraw : Sevm.selector sevm =
      selector "withdraw" [.uint256, .address, .address]
  · obtain ⟨-, supply, supplyEq, -, fits, -, -, -, ownerValid, -, covered,
        burnable, effect⟩ :=
      withdraw_compiled_effect config memoryWf run isWithdraw
    have supplyNat : supply.toNat =
        supplyN (Devm.getStor pre sevm.currentTarget) :=
      congrArg B256.toNat supplyEq
    have burnableN := Nat.le_trans burnable (Nat.le_of_eq supplyNat)
    by_cases self : sevm.currentTarget = (Sevm.argWord sevm 1).toAdr
    · exact outboundEffect_preserves_backed_self self ownerValid covered
        burnableN effect backed
    · refine outboundEffect_preserves_backed self ownerValid covered burnableN
        ?_ effect backed
      rw [B256.toNat_toB256_of_lt fits, ← supplyNat]
      exact Blanc.ProrataWethVault.previewWithdrawN_covers _ _ _
  by_cases isRedeem : Sevm.selector sevm =
      selector "redeem" [.uint256, .address, .address]
  · obtain ⟨-, supply, supplyEq, -, fits, -, -, -, ownerValid, -, covered,
        burnable, effect⟩ :=
      redeem_compiled_effect config memoryWf run isRedeem
    have supplyNat : supply.toNat =
        supplyN (Devm.getStor pre sevm.currentTarget) :=
      congrArg B256.toNat supplyEq
    have burnableN := Nat.le_trans burnable (Nat.le_of_eq supplyNat)
    by_cases self : sevm.currentTarget = (Sevm.argWord sevm 1).toAdr
    · exact outboundEffect_preserves_backed_self self ownerValid covered
        burnableN effect backed
    · refine outboundEffect_preserves_backed self ownerValid covered burnableN
        ?_ effect backed
      rw [B256.toNat_toB256_of_lt fits, ← supplyNat, Nat.mul_comm]
      exact Blanc.ProrataWethVault.convertToAssetsN_floor_le _ _ _
  · have silent := nonflow_message_accountingStep config memoryWf run isDeposit
      isMint isWithdraw isRedeem
    have snapshot : snapshotAt sevm post = snapshotAt sevm pre :=
      Blanc.Prorata.ProrataAccountingEffect.silent_inv silent
    have supplyKept : supplyN (Devm.getStor post sevm.currentTarget) =
        supplyN (Devm.getStor pre sevm.currentTarget) :=
      congrArg Blanc.Prorata.AccountingSnapshot.supply snapshot
    have rowKept :
        (Stor.rest (Devm.getStor post wethAccount) sevm.currentTarget).toNat =
        (Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget).toNat :=
      congrArg Blanc.Prorata.AccountingSnapshot.balance snapshot
    obtain ⟨conserved, capped, bound⟩ := backed
    refine ⟨vault_nonflow_message_preserves_conserved memoryWf run isDeposit
      isMint isWithdraw isRedeem conserved, ?_, ?_⟩
    · rw [supplyKept]
      exact capped
    · rw [supplyKept, rowKept]
      exact bound

/-! ## One vault message preserves the stable boundary

The wrapper strip is exactly the one
`vault_processMessage_some_preserves_conserved` performs.  What is new is the
asset's two clauses, and the route for them is the design's: **not** a walk over
WETH's program, and not a descent to the exact WETH children either.
`weth_preserves_solvent` is the generic frame-level ladder rung; it is already
quantified over every frame, and its only hypothesis about the running code is
that a frame whose target is the asset runs the asset's program.  At a vault
frame that hypothesis is vacuous — `wethAccount ≠ vault` — so the whole vault
message, children included, is one instance of it.

The entry value transfer is the one genuine obligation.  The generic message
rung asks the sender not to be the asset (`ContractSpec.MsgInv.ne`), because an
asset-sent transfer lowers the asset's ETH without lowering its books.  A
committing vault message cannot be that message: every vault target is
`nonpayable`, so the value is zero and the entry transfer moves nothing. -/

/-- Every entry of the vault's dispatch table is `routed`. -/
private theorem vaultFuncs_mem_routed {sig : B256} {body : Func}
    (member : (sig, body) ∈ Blanc.ProrataWethVault.vaultFuncs) :
    ∃ words target, body = Blanc.ProrataWethVault.routed words target := by
  simp only [Blanc.ProrataWethVault.vaultFuncs, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ |
    ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ |
    ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ |
    ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  all_goals exact ⟨_, _, rfl⟩

/-- **A successful vault message carries no value.**  Every dispatch target is
wrapped in `nonpayable`, so the guard has run whichever selector matched. -/
private theorem vault_message_value_zero
    {sevm : Sevm} {pre post : Devm}
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post) :
    sevm.value = 0 := by
  obtain ⟨body, member⟩ :=
    Blanc.ProrataWethVault.selector_mem_vaultFuncs_of_ok run
  obtain ⟨words, target, rfl⟩ := vaultFuncs_mem_routed member
  obtain ⟨-, valueZero, -, -, -, -, -, -⟩ :=
    Blanc.ProrataWethVault.runCompiled_enters_body_compiled_logs run rfl member
  exact valueZero

/-- **A zero-value message entry cannot lower a third account's ETH.**

`Msg.benvAfterTransfer` is a `subBal` at the caller followed by an `addBal` at
the target.  The `addBal` is at the target, which is the vault and not the
asset.  The `subBal` is at the caller, and that is where the generic message
rung asks for `caller ≠ wa` (`ContractSpec.MsgInv.ne`): a debit really can
break the asset's solvency.  At `value = 0` the debit is inert, so no premise
about the sender is needed. -/
private theorem benvAfterTransfer_bal_le_of_value_zero
    {msg : Msg} {entry : Benv} {account : Adr}
    (zero : msg.value = 0) (notTarget : msg.currentTarget ≠ account)
    (transfer : msg.benvAfterTransfer = .ok entry) :
    (msg.benv.state.bal account).toNat ≤ (entry.state.bal account).toNat := by
  cases stv : msg.shouldTransferValue with
  | false =>
      rw [of_benvAfterTransfer_no (by simp [stv]) transfer]
  | true =>
      have inert : ∀ x : B256, (x - msg.value).toNat = x.toNat := by
        intro x
        have zeroLe : msg.value ≤ x := by
          rw [B256.le_iff_toNat_le_toNat, zero, B256.toNat_zero]
          exact Nat.zero_le _
        rw [B256.toNat_sub_eq_of_le _ _ zeroLe, zero, B256.toNat_zero,
          Nat.sub_zero]
      obtain ⟨mid, sub, rfl⟩ := of_benvAfterTransfer stv transfer
      obtain ⟨-, rfl⟩ := State.of_subBal sub
      show _ ≤ (Jaune.State.bal ((msg.benv.state.setBal msg.caller
        (msg.benv.state.bal msg.caller - msg.value)).addBal
          msg.currentTarget msg.value) account).toNat
      rw [show Jaune.State.bal ((msg.benv.state.setBal msg.caller
          (msg.benv.state.bal msg.caller - msg.value)).addBal
            msg.currentTarget msg.value) account =
          Jaune.State.bal (msg.benv.state.setBal msg.caller
            (msg.benv.state.bal msg.caller - msg.value)) account from
        congrArg Acct.bal (State.setBal_get_ne notTarget)]
      by_cases caller : msg.caller = account
      · subst caller
        rw [show Jaune.State.bal (msg.benv.state.setBal msg.caller
            (msg.benv.state.bal msg.caller - msg.value)) msg.caller =
            msg.benv.state.bal msg.caller - msg.value from
          congrArg Acct.bal State.setBal_get_self, inert]
      · rw [show Jaune.State.bal (msg.benv.state.setBal msg.caller
            (msg.benv.state.bal msg.caller - msg.value)) account =
            msg.benv.state.bal account from
          congrArg Acct.bal (State.setBal_get_ne caller)]

/-- The vault program contains no `PC`, so a raw execution of its compiled code
is a gas-exact `Prog.RunCompiled`.  Restated rather than imported: the sibling
copies in `…Message.lean` and `…Rely.lean` are both `private`, and `…Rely.lean`
sits above this module. -/
private theorem pair_vault_pcFree :
    Prog.pcFree Blanc.ProrataWethVault.vault = true := by
  decide +kernel

/-- **One vault message preserves the stable boundary.**

The `.some` slot is the interpreted case: a committing settlement exposes its
gas-exact run to the two frame-level rungs, and a non-committing one rolls the
world back to the entry state, where the boundary already held. -/
theorem vault_processMessage_preserves_stable
    {vault : Adr} {rules : ForkRules} {msg : Msg} {post : Devm} {pc : Nat}
    {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (process : ProcessMessage msg (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (target : msg.currentTarget = vault)
    (code : some msg.code.toList = Prog.compile Blanc.ProrataWethVault.vault)
    (callerNotVault : msg.caller ≠ vault)
    (stat : msg.benv.stat.rules = rules)
    (stable : PairStable vault rules msg.benv.state) :
    PairStable vault rules post.state := by
  obtain ⟨pcEq, sevmCode, sevmTarget, -, -, -, -, memoryWf⟩ :=
    MessageExecution.processMessage_entry_facts vault process
  by_cases settles : Frame.settlementCommits (Frame.ofCall msg) out = true
  · have committed := Frame.raw_commits_of_settlementCommits settles
    cases out with
    | error err => simp [Execution.commits] at committed
    | ok execPost =>
        subst pcEq
        have postEq : post.state = execPost.state :=
          ProcessMessage.ok_state_eq_committedPost process committed
        have ct : sevm.currentTarget = vault := sevmTarget.trans target
        have enter := (RunFrame.some_inv process).1
        rcases Frame.enter_run_inv enter with ⟨entry, transfer, evmEq⟩
        change msg.benvAfterTransfer = .ok entry at transfer
        have sevmEq : sevm = initSevm (msg.withBenv entry) :=
          congrArg Evm.sta evmEq
        have preEq : pre = initDevm (msg.withBenv entry) :=
          congrArg Evm.dyna evmEq
        have entryState : pre.state = entry.state := by
          rw [preEq]
          exact rfl
        have entryStat : entry.stat = msg.benv.stat :=
          benvAfterTransfer_stat transfer
        have entryCode : ∀ a, entry.state.getCode a = msg.benv.state.getCode a :=
          benvAfterTransfer_ok_getCode transfer
        -- The frame's configuration, from the stable world it opened on.
        have frameVault : some (pre.state.getCode vault).toList =
            Prog.compile Blanc.ProrataWethVault.vault := by
          rw [entryState, entryCode]
          exact stable.vaultInstalled
        have frameWeth :
            (pre.state.getCode wethAccount).toList = Blanc.wethCode := by
          rw [entryState, entryCode]
          exact stable.wethInstalled
        have frameConfig :
            DirectWethConfiguration sevm.currentTarget sevm pre := by
          rw [ct]
          refine ⟨stable.distinct, ?_, frameWeth⟩
          rw [sevmEq]
          show (msg.withBenv entry).benv.stat.rules.isPrecomp wethAccount = false
          rw [show (msg.withBenv entry).benv = entry from rfl, entryStat, stat]
          exact stable.wethNonprecompile
        have codeEq : some sevm.code.toList =
            Prog.compile Blanc.ProrataWethVault.vault := by
          rw [sevmCode]
          exact code
        have compiled : Prog.RunCompiled sevm pre
            Blanc.ProrataWethVault.vault execPost :=
          Prog.runCompiled_of_exec sevm pre _ execPost pair_vault_pcFree run
            codeEq
        -- Nonpayability, and with it the entry transfer's inertness.
        have msgZero : msg.value = 0 := by
          have frameZero := vault_message_value_zero compiled
          rw [sevmEq] at frameZero
          exact frameZero
        have balSumLe : sum entry.state.bal ≤ sum msg.benv.state.bal :=
          Msg.benvAfterTransfer_balance_effect (out := .ok entry) transfer
        have wethBalLe : (msg.benv.state.bal wethAccount).toNat ≤
            (entry.state.bal wethAccount).toNat :=
          benvAfterTransfer_bal_le_of_value_zero msgZero
            (target.symm ▸ (Ne.symm stable.distinct)) transfer
        -- The joint invariant across the message.
        have backedPre : PairBacked sevm.currentTarget
            (Devm.getStor pre sevm.currentTarget)
            (Devm.getStor pre wethAccount) := by
          rw [ct]
          show PairBacked vault (pre.state.getStor vault)
            (pre.state.getStor wethAccount)
          rw [entryState, benvAfterTransfer_preserves_getStor transfer vault,
            benvAfterTransfer_preserves_getStor transfer wethAccount]
          exact stable.backed
        have wethSumNof : SumNof (Stor.rest (Devm.getStor pre wethAccount)) := by
          show SumNof (Stor.rest (pre.state.getStor wethAccount))
          rw [entryState, benvAfterTransfer_preserves_getStor transfer
            wethAccount]
          exact stable.wethRowSumNof
        have callerNe : sevm.caller ≠ sevm.currentTarget := by
          rw [ct, sevmEq]
          exact callerNotVault
        have backedPost := vault_message_preserves_backed frameConfig memoryWf
          callerNe wethSumNof compiled backedPre
        rw [ct] at backedPost
        -- The asset's own clauses, from the generic frame ladder at this very
        -- frame: no WETH walk, and no descent to the children.
        have precond : Precond wethAccount sevm pre := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · show some (pre.state.getCode wethAccount).toList = _
            rw [frameWeth, Blanc.wethCode_compile]
          · show sum pre.state.bal < 2 ^ 256
            rw [entryState]
            have bound : sum msg.benv.state.bal < 2 ^ 256 := stable.sumNof
            omega
          · intro hit
            exact absurd (ct.symm.trans hit).symm stable.distinct
          · intro _
            show balSum (pre.state.getStor wethAccount) + (0 : B256).toNat ≤
              (pre.state.bal wethAccount).toNat
            rw [entryState, benvAfterTransfer_preserves_getStor transfer
              wethAccount]
            have solvent : balSum (msg.benv.state.getStor wethAccount) +
                (0 : B256).toNat ≤ (msg.benv.state.bal wethAccount).toNat :=
              stable.wethSolvent
            omega
        have postcond : Postcond wethAccount sevm execPost :=
          weth_preserves_solvent wethAccount sevm pre execPost run
            (fun hit => absurd (ct.symm.trans hit).symm stable.distinct) precond
        -- Neither runtime can move: both accounts hold compiled code.
        have vaultKept : execPost.getCode vault = pre.getCode vault :=
          code_eq_of_exec run frameVault
        have wethKept : execPost.getCode wethAccount = pre.getCode wethAccount :=
          code_eq_of_exec run (by
            show some (pre.state.getCode wethAccount).toList = _
            rw [frameWeth, Blanc.wethCode_compile])
        rw [postEq]
        refine ⟨?_, ?_, stable.distinct, stable.vaultNonzero,
          stable.vaultNonprecompile, stable.wethNonprecompile, backedPost,
          postcond.nof, postcond.solvent⟩
        · show some (execPost.getCode vault).toList = _
          rw [vaultKept]
          exact frameVault
        · show (execPost.getCode wethAccount).toList = _
          rw [wethKept]
          exact frameWeth
  · have settledEq := (RunFrame.some_inv process).2
    have postError : post.error.isSome = true := by
      have notNone : post.error.isNone ≠ true := by
        intro clean
        apply settles
        unfold Frame.settlementCommits
        rw [← settledEq]
        exact clean
      cases errorEq : post.error <;> simp_all
    rw [(ProcessMessage.rollback_of_error process postError).1]
    exact stable

end Blanc.Composition.ProrataWethVault
