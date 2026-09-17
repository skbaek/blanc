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


/-! ## The five in-flight stages

Between two stable boundaries a vault flow passes through machine states that
are *not* stable: the WETH row has moved and the share ledger has not, or the
other way round.  SF §7 freezes five such stages, and this section names them
and proves the two that exit a flow do so at a `PairBacked` post.

Two shape decisions are worth stating.

* The stage is an **index**, not an existential inside one predicate.  A stage
  carries the operation words it is about, so `PairInFlight … (.inboundSettled
  assets shares) cur` pins both the stage and its amounts.  That is what lets
  the exit theorems below consume a named stage's own fields: `cases` on the
  hypothesis leaves exactly one arm.  Without the index every exit theorem
  would have to take its stage's fields as separate premises, and deleting a
  field from a constructor would then break nothing.
* The stages are stated **at the split points the flow theorems already
  expose** — the WETH child's `callPre`/`callPost` and the burn's exit — and
  nothing walks the vault program again.  `PairInFlight` is about storage,
  logs and the world, so a state that differs from the flow entry only in
  memory and stack is the flow entry as far as any stage is concerned; that is
  `PairInFlight.of_quiet_entry`, and it is how a stage taken at a body entry
  travels back to the message entry the history carrier holds. -/

/-- Which of SF §7's five frozen stages an in-flight state is at, together with
the operation words that stage is about.  `reverting` carries none: a rolled
back child settles no operation. -/
inductive PairStage where
  /-- Inbound, quoted, before the WETH child. -/
  | inboundQuoted (assets shares : B256)
  /-- Inbound, the WETH child settled, before the share mint. -/
  | inboundSettled (assets shares : B256)
  /-- Outbound, the allowance spent and the shares burned, before the child. -/
  | outboundBurned (owner assets shares : B256)
  /-- Outbound, the WETH child settled, before the final vault event. -/
  | outboundSettled (receiver : Adr) (assets shares : B256)
  /-- A reverting child or outer frame. -/
  | reverting

/-- **The exact in-flight record of one vault flow at one of the five frozen
stages**, relative to the flow's entry state.

Every field is about the world — storage, logs, the balance rows — so a stage
says nothing about memory or the stack and survives any prefix that moves only
those. -/
inductive PairInFlight (vault : Adr) (sevm : Sevm) (entry : Devm) :
    PairStage → Devm → Prop where
  /-- **Inbound quoted.**  Nothing has moved yet: the quote was priced from the
  WETH balance booked *before* the transfer, and the price is no better than
  the backing bound already allows. -/
  | inboundQuoted {cur : Devm} {assets shares : B256}
      (stable : supplyN (Devm.getStor entry vault) ≤
        Blanc.ProrataWethVault.maxSupplyN)
      (quote : shares.toNat * ((vaultSnapshot vault entry).balance + 1) ≤
        assets.toNat * ((vaultSnapshot vault entry).supply +
          Blanc.ProrataWethVault.offsetN))
      (storage : Devm.getStor cur = Devm.getStor entry)
      (logs : cur.logs = entry.logs) :
      PairInFlight vault sevm entry (.inboundQuoted assets shares) cur
  /-- **Inbound settled.**  The WETH child credited the vault's row and the
  share ledger has not moved, so the bound is strictly slacker than it needs to
  be: `strengthened` says the risen row already backs the shares the mint is
  about to issue, and `capped` that they fit the supply cap.  These two are
  what the mint consumes; the row rose by exactly the assets the quote was
  priced against, which is why they are available at all. -/
  | inboundSettled {cur : Devm} {assets shares : B256}
      (credited : Transfer (Stor.rest (Devm.getStor entry wethAccount))
        sevm.caller assets vault (Stor.rest (Devm.getStor cur wethAccount)))
      (vaultUntouched : Devm.getStor cur vault = Devm.getStor entry vault)
      (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
        (Devm.getStor cur vault))
      (strengthened : supplyN (Devm.getStor entry vault) + shares.toNat ≤
        Blanc.ProrataWethVault.offsetN *
          (Stor.rest (Devm.getStor cur wethAccount) vault).toNat)
      (capped : supplyN (Devm.getStor entry vault) + shares.toNat ≤
        Blanc.ProrataWethVault.maxSupplyN) :
      PairInFlight vault sevm entry (.inboundSettled assets shares) cur
  /-- **Outbound burned.**  The owner's row and the supply have fallen by the
  quoted share amount and no WETH has moved yet, so the bound is slacker than
  it needs to be in the other direction: `strengthened` says the remaining
  supply is still backed once the pending payout leaves the row. -/
  | outboundBurned {cur : Devm} {owner assets shares : B256}
      (burned : Devm.getStorVal cur vault owner =
        Devm.getStorVal entry vault owner - shares)
      (supplyDown : supplyN (Devm.getStor cur vault) + shares.toNat =
        supplyN (Devm.getStor entry vault))
      (wethUntouched : Devm.getStor cur wethAccount =
        Devm.getStor entry wethAccount)
      (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
        (Devm.getStor cur vault))
      (capped : supplyN (Devm.getStor cur vault) ≤
        Blanc.ProrataWethVault.maxSupplyN)
      (strengthened : supplyN (Devm.getStor cur vault) +
          Blanc.ProrataWethVault.offsetN * assets.toNat ≤
        Blanc.ProrataWethVault.offsetN *
          (Stor.rest (Devm.getStor entry wethAccount) vault).toNat) :
      PairInFlight vault sevm entry (.outboundBurned owner assets shares) cur
  /-- **Outbound settled.**  The child paid the receiver out of the vault's
  row, and the joint invariant already holds again: only the `Withdraw` event
  and the returned word are still owed, and neither touches storage. -/
  | outboundSettled {cur : Devm} {receiver : Adr} {assets shares : B256}
      (debited : Transfer (Stor.rest (Devm.getStor entry wethAccount))
        vault assets receiver (Stor.rest (Devm.getStor cur wethAccount)))
      (backedAfter : PairBacked vault (Devm.getStor cur vault)
        (Devm.getStor cur wethAccount)) :
      PairInFlight vault sevm entry
        (.outboundSettled receiver assets shares) cur
  /-- **Reverting.**  A failed child or a reverting outer frame exposes the
  entry world again, so the prior stable boundary is the projection. -/
  | reverting {cur : Devm} (rollback : cur.state = entry.state) :
      PairInFlight vault sevm entry .reverting cur

/-- The four stages that settle an operation.  `reverting` is deliberately
excluded below: it is the one stage that reads the whole world rather than the
two ledgers, and a prefix that leaves storage alone need not leave the world
alone — the quote snapshot's `STATICCALL` warms an address.  `reverting` is
produced at its own crossing and consumed by the settlement rollback, never
transported. -/
def PairStage.settles : PairStage → Prop
  | .reverting => False
  | _ => True

/-- A settling stage reads only the two storage maps and the log frame, so it
travels across any prefix that leaves those alone.  This is what moves a stage
taken at a flow's `finishInbound`/`finishOutbound` boundary back to the message
entry the history carrier holds: the argument staging, the quote snapshot, each
flow's own arithmetic, and every guard in front of the stage are quiet in
exactly this sense — and the quote snapshot is quiet in exactly this sense and
no stronger. -/
theorem PairInFlight.of_quiet_entry {vault : Adr} {sevm : Sevm}
    {entry entry' cur : Devm} {stage : PairStage}
    (settles : stage.settles)
    (storage : Devm.getStor entry' = Devm.getStor entry)
    (logs : entry'.logs = entry.logs)
    (h : PairInFlight vault sevm entry stage cur) :
    PairInFlight vault sevm entry' stage cur := by
  have vaultStor : Devm.getStor entry' vault = Devm.getStor entry vault :=
    congrFun storage vault
  have wethStor : Devm.getStor entry' wethAccount =
      Devm.getStor entry wethAccount :=
    congrFun storage wethAccount
  have vaultVal : ∀ k, Devm.getStorVal entry' vault k =
      Devm.getStorVal entry vault k := by
    intro k
    show (Devm.getStor entry' vault).get k = (Devm.getStor entry vault).get k
    rw [vaultStor]
  have snap : vaultSnapshot vault entry' = vaultSnapshot vault entry := by
    unfold vaultSnapshot
    rw [vaultVal, wethStor]
  cases h with
  | inboundQuoted stable quote storageEq logsEq =>
      refine .inboundQuoted ?_ ?_ ?_ ?_
      · rw [vaultStor]
        exact stable
      · rw [snap]
        exact quote
      · rw [storageEq, storage]
      · rw [logsEq, logs]
  | inboundSettled credited vaultUntouched conserved strengthened capped =>
      refine .inboundSettled ?_ ?_ conserved ?_ ?_
      · rw [wethStor]
        exact credited
      · rw [vaultStor]
        exact vaultUntouched
      · rw [vaultStor]
        exact strengthened
      · rw [vaultStor]
        exact capped
  | outboundBurned burned supplyDown wethUntouched conserved capped
      strengthened =>
      refine .outboundBurned ?_ ?_ ?_ conserved capped ?_
      · rw [vaultVal]
        exact burned
      · rw [vaultStor]
        exact supplyDown
      · rw [wethStor]
        exact wethUntouched
      · rw [wethStor]
        exact strengthened
  | outboundSettled debited backedAfter =>
      refine .outboundSettled ?_ backedAfter
      rw [wethStor]
      exact debited
  | reverting rollback => exact settles.elim

/-! ### Exiting a stage -/

/-- **The inbound stage exits to a backed post.**

The share mint is the last write of an inbound flow.  Its effect on the two
coordinates the invariant reads is a credit at the receiver's row and the same
credit at the supply; the WETH row does not move again.  So the post is backed
exactly when the settled stage's `strengthened` field holds — the risen WETH
row already covers the shares about to be issued — and that field is where the
mint bound (`mint_bound`, `Blanc/Composition/ProrataWethVaultBacking.lean`)
was cashed in, one stage earlier, against the pre-transfer quote.

`vaultAfter` is written against the flow entry rather than against `cur`
because that is the shape `InboundEffect` states it in; the settled stage's own
`vaultUntouched` is what makes the two the same map. -/
theorem PairInFlight.stable_of_mint {vault : Adr} {sevm : Sevm}
    {entry cur post : Devm} {receiver assets shares : B256}
    (stage : PairInFlight vault sevm entry (.inboundSettled assets shares) cur)
    (receiverValid : ValidAdr receiver)
    (vaultAfter : Devm.getStor post vault =
      ((Devm.getStor entry vault).set receiver
          (Devm.getStorVal entry vault receiver + shares)).set
        Blanc.ProrataWethVault.supplySlot
        (Devm.getStorVal entry vault Blanc.ProrataWethVault.supplySlot +
          shares))
    (wethAfter : Devm.getStor post wethAccount = Devm.getStor cur wethAccount) :
    PairBacked vault (Devm.getStor post vault)
      (Devm.getStor post wethAccount) := by
  cases stage with
  | inboundSettled credited vaultUntouched conserved strengthened capped =>
      obtain ⟨receiverAdr, receiverAdrEq⟩ := receiverValid
      subst receiverAdrEq
      have conservedEntry : LedgerConserved Blanc.ProrataWethVault.supplySlot
          (Devm.getStor entry vault) := by
        rw [← vaultUntouched]
        exact conserved
      have maxLt : Blanc.ProrataWethVault.maxSupplyN < 2 ^ 256 := by
        unfold Blanc.ProrataWethVault.maxSupplyN maxWordN wordModulusN
        omega
      have nof : B256.Nof
          ((Devm.getStor entry vault).get Blanc.ProrataWethVault.supplySlot)
          shares := by
        unfold B256.Nof
        have expand : supplyN (Devm.getStor entry vault) =
            ((Devm.getStor entry vault).get
              Blanc.ProrataWethVault.supplySlot).toNat := rfl
        omega
      have supplyAfter : supplyN (Devm.getStor post vault) =
          supplyN (Devm.getStor entry vault) + shares.toNat := by
        show ((Devm.getStor post vault).get _).toNat = _
        rw [vaultAfter, Stor.get_set_self]
        exact B256.toNat_add_eq_of_nof _ _ nof
      refine ⟨?_, ?_, ?_⟩
      · rw [vaultAfter]
        exact LedgerConserved.mint_set
          Blanc.ProrataWethVault.supplySlot_not_validAdr conservedEntry nof
      · rw [supplyAfter]
        exact capped
      · rw [supplyAfter, wethAfter]
        exact strengthened

/-- **The outbound stage exits to a backed post.**

Everything an outbound flow still owes after its WETH child — the `Withdraw`
entry and the returned word — is invisible to both coordinates, so the settled
stage's own `backedAfter` is the post's invariant. -/
theorem PairInFlight.stable_of_outboundSettled {vault : Adr} {sevm : Sevm}
    {entry cur post : Devm} {receiver : Adr} {assets shares : B256}
    (stage : PairInFlight vault sevm entry
      (.outboundSettled receiver assets shares) cur)
    (vaultAfter : Devm.getStor post vault = Devm.getStor cur vault)
    (wethAfter : Devm.getStor post wethAccount = Devm.getStor cur wethAccount) :
    PairBacked vault (Devm.getStor post vault)
      (Devm.getStor post wethAccount) := by
  cases stage with
  | outboundSettled debited backedAfter =>
      rw [vaultAfter, wethAfter]
      exact backedAfter


/-! ### Reverting

A failed WETH child is frame-relative rollback, not partial settlement: the
child's world is the call-entry world again.  That is the `reverting` stage,
and it is the reason a flow that reverts needs no separate invariant argument —
the prior stable boundary is literally the post. -/

open Jaune.Ninst Ninst
open scoped LogOutputHinv
open Source

/-- **A failed exact WETH child is the reverting stage**, at whatever crossing
it happened.  This is `ExactWethChildOccurrence.rollback_of_post`
(`Blanc/Composition/ProrataWethVaultBoundary.lean`) in the pair's currency. -/
theorem PairInFlight.reverting_of_failed_child {vault : Adr} {sevm : Sevm}
    {pre post : Devm} {instruction : Ninst} {calldata : Bytes} {static : Bool}
    (occurrence : ExactWethChildOccurrence sevm pre post instruction calldata
      static)
    (failureFlag : ∃ tail, post.stack = (0 : B256) :: tail) :
    PairInFlight vault sevm pre .reverting post :=
  .reverting (ExactWethChildOccurrence.rollback_of_post occurrence failureFlag)

/-- The inbound instance: a failed staged `transferFrom` settles nothing. -/
theorem PairInFlight.reverting_of_failed_inbound_child {vault : Adr}
    {sevm : Sevm} {entry callPre callPost : Devm} {image : Bytes}
    {assetsWord assets : B256}
    (config : DirectWethConfiguration sevm.currentTarget sevm callPre)
    (memory : MemoryImage entry image)
    (assetsAt : ImageWordAt image assetsWord assets)
    (assetsAboveCalldata : 96 ≤ (assetsWord * 32).toNat)
    (staging : Line.Run sevm entry (transferFromStaging assetsWord) callPre)
    (depth : sevm.depth ≠ 0)
    (dynamic : sevm.isStatic = false)
    (gasAvailable : CallGasAvailable callPre 100)
    (crossing : Ninst.RunCompiled sevm callPre call callPost)
    (failureFlag : ∃ tail, callPost.stack = (0 : B256) :: tail) :
    PairInFlight vault sevm callPre .reverting callPost :=
  .reverting (transferFromStaging_rollback config memory assetsAt
    assetsAboveCalldata staging depth dynamic gasAvailable crossing
    failureFlag)

/-- The outbound instance: a failed staged `transfer` pays nothing. -/
theorem PairInFlight.reverting_of_failed_outbound_child {vault : Adr}
    {sevm : Sevm} {entry callPre callPost : Devm} {image : Bytes}
    {receiverWord assetsWord assets : B256} {receiver : Adr}
    (config : DirectWethConfiguration sevm.currentTarget sevm callPre)
    (memory : MemoryImage entry image)
    (receiverAt : ImageWordAt image receiverWord receiver.toB256)
    (assetsAt : ImageWordAt image assetsWord assets)
    (receiverAboveSelector : 32 ≤ (receiverWord * 32).toNat)
    (assetsAboveReceiver : 64 ≤ (assetsWord * 32).toNat)
    (staging : Line.Run sevm entry
      (transferStaging receiverWord assetsWord) callPre)
    (depth : sevm.depth ≠ 0)
    (dynamic : sevm.isStatic = false)
    (gasAvailable : CallGasAvailable callPre 68)
    (crossing : Ninst.RunCompiled sevm callPre call callPost)
    (failureFlag : ∃ tail, callPost.stack = (0 : B256) :: tail) :
    PairInFlight vault sevm callPre .reverting callPost :=
  .reverting (transferStaging_rollback config memory receiverAt assetsAt
    receiverAboveSelector assetsAboveReceiver staging depth dynamic
    gasAvailable crossing failureFlag)

/-! ### The staging lines are quiet

Both calldata staging lines write memory and the stack and nothing else, which
is what puts the `inboundQuoted` stage exactly at the crossing rather than
somewhere inside the staging. -/

/-- The delegated-transfer staging moves no storage and logs nothing. -/
private theorem transferFromStaging_quiet {sevm : Sevm} {entry callPre : Devm}
    {assetsWord : B256}
    (staging : Line.Run sevm entry (transferFromStaging assetsWord) callPre) :
    Devm.getStor entry = Devm.getStor callPre ∧
      Devm.getCode entry = Devm.getCode callPre ∧
      entry.logs = callPre.logs := by
  refine ⟨Line.of_inv Devm.getStor ?_ staging,
    Line.of_inv Devm.getCode ?_ staging, Line.of_inv Devm.logs ?_ staging⟩
  · unfold transferFromStaging Blanc.ProrataWethVault.loadWord mstoreAt
      pushList
    simp only [List.map, List.cons_append, List.nil_append]
    line_inv
  · unfold transferFromStaging Blanc.ProrataWethVault.loadWord mstoreAt
      pushList
    simp only [List.map, List.cons_append, List.nil_append]
    line_inv
  · unfold transferFromStaging Blanc.ProrataWethVault.loadWord mstoreAt
      pushList
    simp only [List.map, List.cons_append, List.nil_append]
    line_inv

/-- The outbound-transfer staging moves no storage and logs nothing. -/
private theorem transferStaging_quiet {sevm : Sevm} {entry callPre : Devm}
    {receiverWord assetsWord : B256}
    (staging : Line.Run sevm entry
      (transferStaging receiverWord assetsWord) callPre) :
    Devm.getStor entry = Devm.getStor callPre ∧
      Devm.getCode entry = Devm.getCode callPre ∧
      entry.logs = callPre.logs := by
  refine ⟨Line.of_inv Devm.getStor ?_ staging,
    Line.of_inv Devm.getCode ?_ staging, Line.of_inv Devm.logs ?_ staging⟩
  · unfold transferStaging Blanc.ProrataWethVault.loadWord mstoreAt pushList
    simp only [List.map, List.cons_append, List.nil_append]
    line_inv
  · unfold transferStaging Blanc.ProrataWethVault.loadWord mstoreAt pushList
    simp only [List.map, List.cons_append, List.nil_append]
    line_inv
  · unfold transferStaging Blanc.ProrataWethVault.loadWord mstoreAt pushList
    simp only [List.map, List.cons_append, List.nil_append]
    line_inv


/-! ### The inbound stage witnesses

The inbound flow reaches its WETH child through the supply-room guard, and
`shareRoomGuard_trace` already walks that guard once.  This theorem starts
where that guard ends, takes the flow's own crossing apart with
`callWethTransferFrom_trace`, and reads the two stages off
`callWethTransferFrom_worldEffect` — the world-strength form of
`callWethTransferFrom_exactEffect`, which is what gives the vault's own ledger
back across the child.  Nothing walks the vault program again.

The premises are the ones the flow already establishes at this boundary:
`quote` is the exact pre-transfer inequality `deposit`/`mint` prove of their
own quotes, and `backed` is the entry invariant.  The single arithmetic step
is `mint_bound`, cashed in here rather than one rung later, which is what makes
the settled stage's `strengthened` field available to `stable_of_mint`. -/
theorem inbound_stage_witnesses
    {fs : List Func} {sevm : Sevm} {entry post : Devm} {image : Bytes}
    {sharesWord assetsSourceWord shares assets supply : B256}
    {tailBody : Func} {frame : Stack}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (memoryReads : Mem.Reads entry.memory image)
    (sharesAt : Bytes.toB256
      (image.sliceD (sharesWord * 32).toNat 32 0) = shares)
    (assetsAt : Bytes.toB256
      (image.sliceD (assetsSourceWord * 32).toNat 32 0) = assets)
    (supplyAt : Bytes.toB256
      (image.sliceD
        (Blanc.ProrataWethVault.supplyWord * 32).toNat 32 0) = supply)
    (assetsAboveCalldata : 96 ≤ (assetsSourceWord * 32).toNat)
    (supplyStorage : supply = Devm.getStorVal entry sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot)
    (stable : supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN)
    (stack : frame <<+ entry.stack)
    (dynamic : sevm.isStatic = false)
    (callerNotVault : sevm.caller ≠ sevm.currentTarget)
    (wethSumNof : SumNof (Stor.rest (Devm.getStor entry wethAccount)))
    (quote : shares.toNat *
        ((Stor.rest (Devm.getStor entry wethAccount)
          sevm.currentTarget).toNat + 1) ≤
      assets.toNat * (supply.toNat + Blanc.ProrataWethVault.offsetN))
    (backed : PairBacked sevm.currentTarget
      (Devm.getStor entry sevm.currentTarget)
      (Devm.getStor entry wethAccount))
    (run : Func.RunCompiledTo fs sevm entry
      (Blanc.ProrataWethVault.loadWord sharesWord +++
        Blanc.ProrataWethVault.shareRoom +++ lt :::
        (Func.revert <?>
          Blanc.ProrataWethVault.callWethTransferFrom
            (Blanc.ProrataWethVault.loadWord assetsSourceWord) tailBody))
      (.ok post)) :
    ∃ quoted settled : Devm,
      PairInFlight sevm.currentTarget sevm entry
        (.inboundQuoted assets shares) quoted ∧
      Devm.getStor quoted = Devm.getStor entry ∧
      PairInFlight sevm.currentTarget sevm entry
        (.inboundSettled assets shares) settled ∧
      Devm.getStor settled sevm.currentTarget =
        Devm.getStor entry sevm.currentTarget ∧
      Transfer (Stor.rest (Devm.getStor entry wethAccount)) sevm.caller assets
        sevm.currentTarget (Stor.rest (Devm.getStor settled wethAccount)) ∧
      Func.RunCompiledTo fs sevm settled tailBody (.ok post) := by
  obtain ⟨childEntry, roomFits, childStack, childWf, childReads, childState,
      childLogs, childRun⟩ :=
    Blanc.ProrataWethVault.shareRoomGuard_trace (R := Func.RunOk) memoryWf
      memoryReads sharesAt supplyAt stable stack run
  obtain ⟨callPre, callPost, staging, crossing, suffix⟩ :=
    callWethTransferFrom_trace childRun
  obtain ⟨stagingStorage, stagingCode, stagingLogs⟩ :=
    transferFromStaging_quiet staging
  have guardStorage : Devm.getStor entry = Devm.getStor childEntry :=
    funext (getStor_eq_of_state_eq childState)
  have guardCode : Devm.getCode entry = Devm.getCode childEntry :=
    funext (getCode_eq_of_state_eq childState)
  have entryToCall : Devm.getStor entry = Devm.getStor callPre :=
    guardStorage.trans stagingStorage
  have callConfig :
      DirectWethConfiguration sevm.currentTarget sevm callPre := by
    refine ⟨config.distinct, config.nonprecompile, ?_⟩
    rw [← congrFun (guardCode.trans stagingCode) wethAccount]
    exact config.code
  obtain ⟨settled, movement, childForeign, -, -, -, -, tailRun⟩ :=
    callWethTransferFrom_worldEffect callConfig ⟨childWf, childReads⟩
      (sliceBytes_of_toB256 assetsAt) assetsAboveCalldata staging dynamic
      crossing suffix
  -- Every world coordinate the stages read, relative to the flow entry.
  have vaultUntouched : Devm.getStor settled sevm.currentTarget =
      Devm.getStor entry sevm.currentTarget := by
    rw [childForeign sevm.currentTarget config.distinct,
      ← congrFun entryToCall sevm.currentTarget]
  have credited : Transfer (Stor.rest (Devm.getStor entry wethAccount))
      sevm.caller assets sevm.currentTarget
      (Stor.rest (Devm.getStor settled wethAccount)) := by
    rw [congrFun entryToCall wethAccount]
    exact movement
  have supplyNat : supplyN (Devm.getStor entry sevm.currentTarget) =
      supply.toNat := congrArg B256.toNat supplyStorage.symm
  obtain ⟨conserved, -, bound⟩ := backed
  -- The credited row cannot wrap, because the asset's own sum does not.
  have covered : assets ≤ Stor.rest (Devm.getStor entry wethAccount)
      sevm.caller := credited.1
  have pairBound :
      (Stor.rest (Devm.getStor entry wethAccount) sevm.caller).toNat +
        (Stor.rest (Devm.getStor entry wethAccount)
          sevm.currentTarget).toNat ≤
        sum (Stor.rest (Devm.getStor entry wethAccount)) :=
    add_le_sum_of_ne _ callerNotVault
  have rowNof : B256.Nof (Stor.rest (Devm.getStor entry wethAccount)
      sevm.currentTarget) assets := by
    unfold B256.Nof
    have coveredNat := B256.toNat_le_toNat covered
    have sumLt : sum (Stor.rest (Devm.getStor entry wethAccount)) < 2 ^ 256 :=
      wethSumNof
    omega
  have rowAfter : (Stor.rest (Devm.getStor settled wethAccount)
      sevm.currentTarget).toNat =
      (Stor.rest (Devm.getStor entry wethAccount)
        sevm.currentTarget).toNat + assets.toNat := by
    rw [credited_of_transfer credited callerNotVault]
    exact B256.toNat_add_eq_of_nof _ _ rowNof
  -- The mint bound: the quote cannot be better than the invariant allows.
  have mintable : shares.toNat ≤
      Blanc.ProrataWethVault.offsetN * assets.toNat := by
    refine mint_bound (supply := supply.toNat) ?_ quote
    rw [← supplyNat]
    exact bound
  have roomNat : Blanc.ProrataWethVault.shareRoomN supply.toNat =
      Blanc.ProrataWethVault.maxSupplyN - supply.toNat := rfl
  refine ⟨callPre, settled, ?_, entryToCall.symm, ?_, vaultUntouched,
    credited, tailRun⟩
  · refine .inboundQuoted ?_ ?_ entryToCall.symm
      (childLogs.trans stagingLogs).symm
    · rw [supplyNat]
      exact stable
    · show shares.toNat * ((Stor.rest (Devm.getStor entry wethAccount)
        sevm.currentTarget).toNat + 1) ≤
        assets.toNat * ((Devm.getStorVal entry sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot).toNat +
          Blanc.ProrataWethVault.offsetN)
      rw [← supplyStorage]
      exact quote
  · refine .inboundSettled credited vaultUntouched ?_ ?_ ?_
    · rw [vaultUntouched]
      exact conserved
    · rw [rowAfter, supplyNat]
      have expand : Blanc.ProrataWethVault.offsetN *
          ((Stor.rest (Devm.getStor entry wethAccount)
            sevm.currentTarget).toNat + assets.toNat) =
          Blanc.ProrataWethVault.offsetN *
            (Stor.rest (Devm.getStor entry wethAccount)
              sevm.currentTarget).toNat +
            Blanc.ProrataWethVault.offsetN * assets.toNat := by ring
      rw [supplyNat] at bound
      omega
    · rw [roomNat] at roomFits
      rw [supplyNat]
      omega


/-! ### The outbound stage witnesses

The mirror of the inbound witnesses, one split point later in each direction:
the outbound flow burns before it pays, so its first stage is the burn's own
exit — `outboundBurn_trace`, already walked once by the flow — and its second
is the same crossing the inbound flow uses, with the roles reversed.

`burn_bound` is cashed in here, against the pre-burn quote, and it is what puts
`strengthened` on the burned stage: the supply that survives the burn is still
backed once the pending payout has left the row.  By the time the child
returns, the joint invariant already holds again, which is why the settled
stage carries it outright.

`receiverNotVault` is a genuine premise, not an oversight: the transfer
projections speak only about distinct accounts, and a vault that names itself
as the receiver nets to zero in WETH's ledger.  That degenerate flow is already
closed one rung up, by `outboundEffect_preserves_backed_self`, and it has no
in-flight content — the row it would move is its own. -/
theorem outbound_stage_witnesses
    {fs : List Func} {sevm : Sevm} {entry post : Devm} {image : Bytes}
    {sharesSel assetsSel receiverWord : B256}
    {owner balance supply shares assets : B256} {receiver : Adr}
    {tailBody : Func} {frame : Stack}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (memoryReads : Mem.Reads entry.memory image)
    (sharesAt : Bytes.toB256
      (image.sliceD (sharesSel * 32).toNat 32 0) = shares)
    (ownerAt : Bytes.toB256
      (image.sliceD (Blanc.ProrataWethVault.ownerWord * 32).toNat 32 0) = owner)
    (balanceAt : Bytes.toB256
      (image.sliceD
        (Blanc.ProrataWethVault.balanceWord * 32).toNat 32 0) = balance)
    (supplyAt : Bytes.toB256
      (image.sliceD
        (Blanc.ProrataWethVault.supplyWord * 32).toNat 32 0) = supply)
    (receiverAt : Bytes.toB256
      (image.sliceD (receiverWord * 32).toNat 32 0) = receiver.toB256)
    (assetsAt : Bytes.toB256
      (image.sliceD (assetsSel * 32).toNat 32 0) = assets)
    (receiverAboveSelector : 32 ≤ (receiverWord * 32).toNat)
    (assetsAboveReceiver : 64 ≤ (assetsSel * 32).toNat)
    (ownerValid : ValidAdr owner)
    (balanceEq : balance = Devm.getStorVal entry sevm.currentTarget owner)
    (supplyEq : supply = Devm.getStorVal entry sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot)
    (covered : shares.toNat ≤ balance.toNat)
    (stable : supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN)
    (stack : frame <<+ entry.stack)
    (dynamic : sevm.isStatic = false)
    (receiverNotVault : sevm.currentTarget ≠ receiver)
    (quote : assets.toNat * (supply.toNat + Blanc.ProrataWethVault.offsetN) ≤
      shares.toNat *
        ((Stor.rest (Devm.getStor entry wethAccount)
          sevm.currentTarget).toNat + 1))
    (backed : PairBacked sevm.currentTarget
      (Devm.getStor entry sevm.currentTarget)
      (Devm.getStor entry wethAccount))
    (run : Func.RunCompiledTo fs sevm entry
      (Blanc.ProrataWethVault.loadWord sharesSel +++
        Blanc.ProrataWethVault.loadWord Blanc.ProrataWethVault.balanceWord +++
        sub ::: Blanc.ProrataWethVault.loadWord
          Blanc.ProrataWethVault.ownerWord +++ sstore :::
        Blanc.ProrataWethVault.loadWord sharesSel +++
        Blanc.ProrataWethVault.loadWord Blanc.ProrataWethVault.supplyWord +++
        lt :::
        (Func.revert <?>
          (Blanc.ProrataWethVault.loadWord sharesSel +++
            Blanc.ProrataWethVault.loadWord
              Blanc.ProrataWethVault.supplyWord +++ sub :::
            Blanc.ProrataWethVault.pushSupplySlot +++ sstore :::
            Blanc.ProrataWethVault.logBurnTransfer
              (Blanc.ProrataWethVault.loadWord sharesSel) +++
            Blanc.ProrataWethVault.callWethTransfer
              (Blanc.ProrataWethVault.loadWord receiverWord)
              (Blanc.ProrataWethVault.loadWord assetsSel) tailBody)))
      (.ok post)) :
    ∃ burnedState settled : Devm,
      PairInFlight sevm.currentTarget sevm entry
        (.outboundBurned owner assets shares) burnedState ∧
      Devm.getStor burnedState wethAccount =
        Devm.getStor entry wethAccount ∧
      PairInFlight sevm.currentTarget sevm entry
        (.outboundSettled receiver assets shares) settled ∧
      Devm.getStor settled sevm.currentTarget =
        Devm.getStor burnedState sevm.currentTarget ∧
      Transfer (Stor.rest (Devm.getStor entry wethAccount))
        sevm.currentTarget assets receiver
        (Stor.rest (Devm.getStor settled wethAccount)) ∧
      Func.RunCompiledTo fs sevm settled tailBody (.ok post) := by
  obtain ⟨ownerAdr, ownerAdrEq⟩ := ownerValid
  obtain ⟨conserved, -, bound⟩ := backed
  obtain ⟨burnedState, burnable, burnSet, burnForeign, -, burnCode, -, burnWf,
      burnReads, childRun⟩ :=
    Blanc.ProrataWethVault.outboundBurn_trace (R := Func.RunOk) memoryWf
      memoryReads sharesAt ownerAt balanceAt supplyAt stack run
  obtain ⟨callPre, callPost, staging, crossing, suffix⟩ :=
    callWethTransfer_trace childRun
  obtain ⟨stagingStorage, stagingCode, -⟩ := transferStaging_quiet staging
  have callConfig :
      DirectWethConfiguration sevm.currentTarget sevm callPre := by
    refine ⟨config.distinct, config.nonprecompile, ?_⟩
    rw [← congrFun (burnCode.trans stagingCode) wethAccount]
    exact config.code
  have receiverAtChild : ImageWordAt (Bytes.writeAt image 0 shares.toBytes)
      receiverWord receiver.toB256 := by
    unfold ImageWordAt
    rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (Or.inr (by omega))]
    exact sliceBytes_of_toB256 receiverAt
  have assetsAtChild : ImageWordAt (Bytes.writeAt image 0 shares.toBytes)
      assetsSel assets := by
    unfold ImageWordAt
    rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (Or.inr (by omega))]
    exact sliceBytes_of_toB256 assetsAt
  obtain ⟨settled, movement, childForeign, -, -, -, -, tailRun⟩ :=
    callWethTransfer_worldEffect callConfig ⟨burnWf, burnReads⟩ receiverAtChild
      assetsAtChild receiverAboveSelector assetsAboveReceiver staging dynamic
      crossing suffix
  -- The burned stage's own coordinates.
  have vaultNe : sevm.currentTarget ≠ wethAccount := Ne.symm config.distinct
  have wethUntouched : Devm.getStor burnedState wethAccount =
      Devm.getStor entry wethAccount := burnForeign wethAccount vaultNe
  have ownerNotSupply : owner ≠ Blanc.ProrataWethVault.supplySlot := by
    intro slotEq
    exact Blanc.ProrataWethVault.supplySlot_not_validAdr
      (slotEq ▸ ⟨ownerAdr, ownerAdrEq⟩)
  have supplyNat : supplyN (Devm.getStor entry sevm.currentTarget) =
      supply.toNat := congrArg B256.toNat supplyEq.symm
  have coveredB256 : shares ≤ balance := B256.le_of_toNat_le_toNat covered
  have burnableB256 : shares ≤ supply := B256.le_of_toNat_le_toNat burnable
  have burnedRow : Devm.getStorVal burnedState sevm.currentTarget owner =
      Devm.getStorVal entry sevm.currentTarget owner - shares := by
    show (Devm.getStor burnedState sevm.currentTarget).get owner = _
    rw [burnSet, Stor.get_set_ne _ (Ne.symm ownerNotSupply),
      Stor.get_set_self, balanceEq]
  have supplyBurned : supplyN (Devm.getStor burnedState sevm.currentTarget) +
      shares.toNat = supplyN (Devm.getStor entry sevm.currentTarget) := by
    have value : supplyN (Devm.getStor burnedState sevm.currentTarget) =
        (supply - shares).toNat := by
      show ((Devm.getStor burnedState sevm.currentTarget).get _).toNat = _
      rw [burnSet, Stor.get_set_self]
    rw [value, B256.toNat_sub_eq_of_le _ _ burnableB256, supplyNat]
    omega
  have conservedBurned : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor burnedState sevm.currentTarget) := by
    rw [burnSet, balanceEq, supplyEq, ← ownerAdrEq]
    exact LedgerConserved.burn_set
      Blanc.ProrataWethVault.supplySlot_not_validAdr conserved
      (by
        show shares ≤ (Devm.getStor entry sevm.currentTarget).get
          ownerAdr.toB256
        rw [ownerAdrEq]
        show shares ≤ Devm.getStorVal entry sevm.currentTarget owner
        rw [← balanceEq]
        exact coveredB256)
  -- `burn_bound`: the remaining supply is still backed once the payout leaves.
  have payable : supply.toNat + Blanc.ProrataWethVault.offsetN * assets.toNat ≤
      Blanc.ProrataWethVault.offsetN *
        (Stor.rest (Devm.getStor entry wethAccount)
          sevm.currentTarget).toNat + shares.toNat := by
    refine burn_bound (supply := supply.toNat) ?_ burnable quote
    rw [← supplyNat]
    exact bound
  have strengthened :
      supplyN (Devm.getStor burnedState sevm.currentTarget) +
          Blanc.ProrataWethVault.offsetN * assets.toNat ≤
        Blanc.ProrataWethVault.offsetN *
          (Stor.rest (Devm.getStor entry wethAccount)
            sevm.currentTarget).toNat := by
    rw [supplyNat] at supplyBurned
    omega
  -- The settled stage: the child debited the vault's row and nothing else.
  have callStorage : Devm.getStor burnedState = Devm.getStor callPre :=
    stagingStorage
  have debited : Transfer (Stor.rest (Devm.getStor entry wethAccount))
      sevm.currentTarget assets receiver
      (Stor.rest (Devm.getStor settled wethAccount)) := by
    rw [← wethUntouched, congrFun callStorage wethAccount]
    exact movement
  have vaultAtSettled : Devm.getStor settled sevm.currentTarget =
      Devm.getStor burnedState sevm.currentTarget := by
    rw [childForeign sevm.currentTarget config.distinct,
      ← congrFun callStorage sevm.currentTarget]
  have rowAfter : (Stor.rest (Devm.getStor settled wethAccount)
      sevm.currentTarget).toNat =
      (Stor.rest (Devm.getStor entry wethAccount)
        sevm.currentTarget).toNat - assets.toNat := by
    rw [debitedSub_of_transfer debited receiverNotVault]
    exact B256.toNat_sub_eq_of_le _ _ debited.1
  refine ⟨burnedState, settled, ?_, wethUntouched, ?_, vaultAtSettled, debited,
    tailRun⟩
  · exact .outboundBurned burnedRow supplyBurned wethUntouched conservedBurned
      (by rw [supplyNat] at supplyBurned; omega) strengthened
  · refine .outboundSettled debited ⟨?_, ?_, ?_⟩
    · rw [vaultAtSettled]
      exact conservedBurned
    · rw [vaultAtSettled, supplyNat] at *
      omega
    · rw [vaultAtSettled, rowAfter]
      have assetsLe : assets.toNat ≤
          (Stor.rest (Devm.getStor entry wethAccount)
            sevm.currentTarget).toNat := B256.toNat_le_toNat debited.1
      have expand : Blanc.ProrataWethVault.offsetN *
            ((Stor.rest (Devm.getStor entry wethAccount)
              sevm.currentTarget).toNat - assets.toNat) +
          Blanc.ProrataWethVault.offsetN * assets.toNat =
          Blanc.ProrataWethVault.offsetN *
            (Stor.rest (Devm.getStor entry wethAccount)
              sevm.currentTarget).toNat := by
        rw [← Nat.mul_add]
        congr 1
        omega
      omega

end Blanc.Composition.ProrataWethVault
