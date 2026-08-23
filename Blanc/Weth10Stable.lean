import Blanc.Weth10StateSound
import Blanc.Weth10DeployProof

/-!
Public packaging of WETH10's existing backing and exact-counter results.

The proofs in this module compose the `ContractSpec` results established for
the Blanc WETH10 program.  They do not make a claim about the deployed oracle;
the repository's standing porting boundary is documented in `PORTING.md`.
-/

namespace Blanc

open Jaune

namespace Weth10

/-- A reader-facing stable state for the compiled Blanc WETH10 program: the
named program is installed, the world's balance sum cannot overflow, booked
balances are backed by the contract's real ETH balance, and no flash mint is
in flight. -/
structure Stable (dp : DeployParams) (ca : Adr) (w : Jaune.State) : Prop where
  code : some (w.getCode ca).toList = Prog.compile (weth10 dp)
  sumNof : SumNof w.bal
  backed : Stor.Weth10Inv (w.getStor ca) 0 (w.bal ca)
  flashZero : (w.getStor ca).get flashMintedSlot = 0

private theorem Stable.backedStateInv
    {dp : DeployParams} {ca : Adr} {w : Jaune.State}
    (h : Stable dp ca w) :
    (backedSpec weth10 dp).StateInv ca w :=
  ⟨h.code, h.sumNof, h.backed⟩

private theorem Stable.flashStateInv
    {dp : DeployParams} {ca : Adr} {w : Jaune.State}
    (h : Stable dp ca w) :
    (flashExactSpec dp 0).StateInv ca w :=
  ⟨h.code, trivial, h.flashZero⟩

private theorem Stable.ofStateInvs
    {dp : DeployParams} {ca : Adr} {w : Jaune.State}
    (h_backed : (backedSpec weth10 dp).StateInv ca w)
    (h_flash : (flashExactSpec dp 0).StateInv ca w) :
    Stable dp ca w :=
  ⟨h_backed.code, h_backed.side, h_backed.inv, h_flash.inv⟩

/-- Exact flash-counter preservation at frame altitude, obtained by feeding
the already-proved receive-aware program relation and global depth theorem to
the generic `ContractSpec.preserves_inv` rung. -/
theorem flashExactSpec_preserves
    (dp : DeployParams) (ca : Adr) (flash : B256) :
    (flashExactSpec dp flash).Preserves ca :=
  ContractSpec.preserves_inv _ _ (by
    intro sevm pre post run h_target _ _ h_pre
    exact (flashExactSpecsRel_of_prog_run dp ca
      (weth10Funcs_exactRelFuncSound dp ca)
      (receiveEther_exactRelFuncSound dp ca)
      run h_target (flashExactDepth dp ca sevm.depth)) flash h_pre)

/-- One successful transaction preserves WETH10 stability.  The total-balance
bound and the fact that the already-installed contract is not freshly created
by this transaction are explicit premises of the generic transaction rung. -/
theorem processTransaction_preserves_stable
    (dp : DeployParams) (ca : Adr)
    (benv : Benv) (bout bout' : BlockOutput) (tx : Tx) (i : Nat)
    (st : Jaune.State)
    (h_run : processTransaction benv bout tx i = .ok ⟨st, bout'⟩)
    (h_sum : sum benv.state.bal < 2 ^ 256)
    (h_not_created : ca ∉ benv.createdAccounts)
    (h_inv : Stable dp ca benv.state) :
    Stable dp ca st :=
  Stable.ofStateInvs
    (ContractSpec.processTransaction_preserves_inv ca
      (backedSpec_preserves dp ca) benv bout bout' tx i st h_run h_sum
      ⟨h_inv.backedStateInv, h_not_created⟩).state
    (ContractSpec.processTransaction_preserves_inv ca
      (flashExactSpec_preserves dp ca 0) benv bout bout' tx i st h_run h_sum
      ⟨h_inv.flashStateInv, h_not_created⟩).state

/-- The rules-explicit block transition preserves WETH10 stability. -/
theorem stateTransitionWith_preserves_stable
    (dp : DeployParams) (ca : Adr) (rules : ForkRules)
    (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransitionWith rules ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : Stable dp ca ch.state) :
    Stable dp ca ch'.state :=
  Stable.ofStateInvs
    (ContractSpec.stateTransitionWith_preserves_inv ca
      (backedSpec_preserves dp ca) rules ch ch' block h_run h_wds
      h_inv.backedStateInv)
    (ContractSpec.stateTransitionWith_preserves_inv ca
      (flashExactSpec_preserves dp ca 0) rules ch ch' block h_run h_wds
      h_inv.flashStateInv)

/-- A configured-chain block transition preserves WETH10 stability. -/
theorem stateTransitionUsing_preserves_stable
    (dp : DeployParams) (ca : Adr) (cfg : ChainConfig)
    (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransitionUsing cfg ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : Stable dp ca ch.state) :
    Stable dp ca ch'.state :=
  Stable.ofStateInvs
    (ContractSpec.stateTransitionUsing_preserves_inv ca
      (backedSpec_preserves dp ca) cfg ch ch' block h_run h_wds
      h_inv.backedStateInv)
    (ContractSpec.stateTransitionUsing_preserves_inv ca
      (flashExactSpec_preserves dp ca 0) cfg ch ch' block h_run h_wds
      h_inv.flashStateInv)

/-- The pinned Prague transition preserves WETH10 stability. -/
theorem stateTransition_preserves_stable
    (dp : DeployParams) (ca : Adr)
    (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransition ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : Stable dp ca ch.state) :
    Stable dp ca ch'.state :=
  Stable.ofStateInvs
    (ContractSpec.stateTransition_preserves_inv ca
      (backedSpec_preserves dp ca) ch ch' block h_run h_wds
      h_inv.backedStateInv)
    (ContractSpec.stateTransition_preserves_inv ca
      (flashExactSpec_preserves dp ca 0) ch ch' block h_run h_wds
      h_inv.flashStateInv)

/-- Reachability on a configured chain preserves WETH10 stability across its
fork schedule. -/
theorem chainUsing_preserves_stable
    (dp : DeployParams) (ca : Adr) (cfg : ChainConfig)
    (ch ch' : BlockChain) (h_reach : BlockChain.ReachUsing cfg ch ch')
    (h_inv : Stable dp ca ch.state) :
    Stable dp ca ch'.state :=
  Stable.ofStateInvs
    (ContractSpec.chainUsing_preserves_inv ca
      (backedSpec_preserves dp ca) cfg ch ch' h_reach
      h_inv.backedStateInv)
    (ContractSpec.chainUsing_preserves_inv ca
      (flashExactSpec_preserves dp ca 0) cfg ch ch' h_reach
      h_inv.flashStateInv)

/-- Reachability under the pinned Prague transition preserves WETH10
stability. -/
theorem chain_preserves_stable
    (dp : DeployParams) (ca : Adr) (ch ch' : BlockChain)
    (h_reach : BlockChain.Reach ch ch')
    (h_inv : Stable dp ca ch.state) :
    Stable dp ca ch'.state :=
  Stable.ofStateInvs
    (ContractSpec.chain_preserves_inv ca
      (backedSpec_preserves dp ca) ch ch' h_reach h_inv.backedStateInv)
    (ContractSpec.chain_preserves_inv ca
      (flashExactSpec_preserves dp ca 0) ch ch' h_reach h_inv.flashStateInv)

/-- Rules-explicit block import preserves WETH10 stability. -/
theorem addBlockToChainWith_preserves_stable
    (dp : DeployParams) (ca : Adr) (rules : ForkRules)
    (ch ch' : BlockChain) (rlp : Bytes)
    (h_run : addBlockToChainWith rules ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : Stable dp ca ch.state) :
    Stable dp ca ch'.state :=
  Stable.ofStateInvs
    (ContractSpec.addBlockToChainWith_preserves_inv ca
      (backedSpec_preserves dp ca) rules ch ch' rlp h_run h_wds
      h_inv.backedStateInv)
    (ContractSpec.addBlockToChainWith_preserves_inv ca
      (flashExactSpec_preserves dp ca 0) rules ch ch' rlp h_run h_wds
      h_inv.flashStateInv)

/-- Configured-chain block import preserves WETH10 stability. -/
theorem addBlockToChainUsing_preserves_stable
    (dp : DeployParams) (ca : Adr) (cfg : ChainConfig)
    (ch ch' : BlockChain) (rlp : Bytes)
    (h_run : addBlockToChainUsing cfg ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : Stable dp ca ch.state) :
    Stable dp ca ch'.state :=
  Stable.ofStateInvs
    (ContractSpec.addBlockToChainUsing_preserves_inv ca
      (backedSpec_preserves dp ca) cfg ch ch' rlp h_run h_wds
      h_inv.backedStateInv)
    (ContractSpec.addBlockToChainUsing_preserves_inv ca
      (flashExactSpec_preserves dp ca 0) cfg ch ch' rlp h_run h_wds
      h_inv.flashStateInv)

/-- Block import under the pinned Prague rules preserves WETH10 stability. -/
theorem addBlockToChain_preserves_stable
    (dp : DeployParams) (ca : Adr)
    (ch ch' : BlockChain) (rlp : Bytes)
    (h_run : addBlockToChain ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : Stable dp ca ch.state) :
    Stable dp ca ch'.state :=
  Stable.ofStateInvs
    (ContractSpec.addBlockToChain_preserves_inv ca
      (backedSpec_preserves dp ca) ch ch' rlp h_run h_wds
      h_inv.backedStateInv)
    (ContractSpec.addBlockToChain_preserves_inv ca
      (flashExactSpec_preserves dp ca 0) ch ch' rlp h_run h_wds
      h_inv.flashStateInv)

/-- The literal solvency consequence of a stable WETH10 state. -/
theorem Stable.solvent
    {dp : DeployParams} {ca : Adr} {w : Jaune.State}
    (h : Stable dp ca w) :
    balSum (w.getStor ca) ≤ (w.bal ca).toNat := by
  have h_backed := h.backed.1
  rw [h.flashZero, B256.toNat_zero, Nat.add_zero] at h_backed
  simpa only [B256.toNat_zero, Nat.add_zero] using h_backed

/-- Headline Prague-chain theorem: readers get the exact zero flash counter
and backing inequality directly, without unpacking either `ContractSpec`. -/
theorem chain_reachable_backed_and_flash_zero
    (dp : DeployParams) (ca : Adr) (ch ch' : BlockChain)
    (h_reach : BlockChain.Reach ch ch')
    (h_inv : Stable dp ca ch.state) :
    (ch'.state.getStor ca).get flashMintedSlot = 0 ∧
      balSum (ch'.state.getStor ca) ≤ (ch'.state.bal ca).toNat := by
  have h := chain_preserves_stable dp ca ch ch' h_reach h_inv
  exact ⟨h.flashZero, h.solvent⟩

/-- A successful direct creation message establishes the stable predicate on
its actual post-state, for the runtime parameters derived from the message's
chain ID and target.  The pre-state balance-sum premise is transported through
the proved non-increase of total balances; the constructor's empty storage
establishes backing against the real post-state ETH balance. -/
theorem processCreateMessage_establishes_stable
    (msg : Msg)
    (h_value : msg.value = 0)
    (h_codeAddress : msg.codeAddress = .none)
    (h_code : msg.code.toList = weth10InitCode)
    (h_gas : weth10CreateMessageGasAccounting ≤ msg.gas)
    (h_max : 6313 ≤ msg.benv.stat.rules.code.maxCodeSize)
    (h_sum : SumNof msg.benv.state.bal) :
    ∃ post,
      processCreateMessage msg = .ok post ∧
      Stable
        (freshDeployParams msg.benv.stat.chainId.toB256 msg.currentTarget)
        msg.currentTarget post.state := by
  obtain ⟨post, h_process, h_installed, h_stor, _, _, _, _⟩ :=
    processCreateMessage_weth10_success msg h_value h_codeAddress h_code h_gas h_max
  have h_compiled :
      some (post.getCode msg.currentTarget).toList =
        Prog.compile (weth10
          (freshDeployParams msg.benv.stat.chainId.toB256 msg.currentTarget)) := by
    rw [h_installed, ByteArray.toList_eq_toList_data]
    exact (freshDeployParams_runtime_compile
      msg.benv.stat.chainId.toB256 msg.currentTarget).symm
  refine ⟨post, h_process, ⟨h_compiled, ?_, ?_, ?_⟩⟩
  · exact lt_of_le_of_lt (processCreateMessage_balance_noninc h_process) h_sum
  · rw [h_stor]
    exact (backedSpec weth10
      (freshDeployParams msg.benv.stat.chainId.toB256 msg.currentTarget)).inv_mono
        Stor.Weth10Inv.of_empty (Nat.zero_le _)
  · rw [h_stor]
    rfl

end Weth10

end Blanc
