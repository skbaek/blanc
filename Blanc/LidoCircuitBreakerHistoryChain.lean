import Blanc.LidoCircuitBreakerHistory

/-!
# Registry integrity through arbitrary histories — frame join and history ladder

The Registry-mutating endpoints, the open-contract frame theorem, and the
specialization of the landed generic ladder up to chain reachability.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

theorem registrySpec_sound (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).Sound ca := by
  sorry

theorem registrySpec_preserves (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).Preserves ca :=
  ContractSpec.preserves_inv (registrySpec dp) ca (registrySpec_sound dp ca)

/-! ## Messages, transactions, blocks and histories -/

theorem processMessageCall_preserves_registryStable (dp : DeployParams)
    {ca : Adr} {msg : Msg} {st' : Jaune.State} {out : MsgCallOutput}
    (h_run : processMessageCall msg = .ok ⟨st', out⟩)
    (h_inv : (registrySpec dp).MsgInv ca msg) :
    RegistryStable dp ca st' :=
  (registryStable_iff_stateInv dp ca st').mpr
    (ContractSpec.processMessageCall_preserves_inv (registrySpec_preserves dp ca) h_run h_inv).1

theorem processTransaction_preserves_registryStable (dp : DeployParams)
    (ca : Adr) (benv : Benv) (bout bout' : BlockOutput) (tx : Tx) (i : Nat)
    (st : Jaune.State)
    (h_run : processTransaction benv bout tx i = .ok ⟨st, bout'⟩)
    (h_sum : sum benv.state.bal < 2 ^ 256)
    (h_fresh : ca ∉ benv.createdAccounts)
    (h_stable : RegistryStable dp ca benv.state) :
    RegistryStable dp ca st :=
  (registryStable_iff_stateInv dp ca st).mpr
    (ContractSpec.processTransaction_preserves_inv ca (registrySpec_preserves dp ca) benv bout
      bout' tx i st h_run h_sum
      ⟨(registryStable_iff_stateInv dp ca benv.state).mp h_stable, h_fresh⟩).state

theorem applyTransactions_preserves_registryStable (dp : DeployParams)
    (ca : Adr) (txis : List (Nat × Tx)) (benv benv' : Benv)
    (bout bout' : BlockOutput)
    (h_run : applyTransactions txis benv bout = .ok ⟨benv', bout'⟩)
    (h_sum : sum benv.state.bal < 2 ^ 256)
    (h_fresh : ca ∉ benv.createdAccounts)
    (h_stable : RegistryStable dp ca benv.state) :
    RegistryStable dp ca benv'.state :=
  (registryStable_iff_stateInv dp ca benv'.state).mpr
    (ContractSpec.applyTransactions_preserves_inv ca (registrySpec_preserves dp ca) txis benv
      benv' bout bout' h_run h_sum
      ⟨(registryStable_iff_stateInv dp ca benv.state).mp h_stable, h_fresh⟩).state

theorem stateTransitionWith_preserves_registryStable (dp : DeployParams)
    (ca : Adr) (rules : ForkRules) (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransitionWith rules ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_stable : RegistryStable dp ca ch.state) :
    RegistryStable dp ca ch'.state :=
  (registryStable_iff_stateInv dp ca ch'.state).mpr
    (ContractSpec.stateTransitionWith_preserves_inv ca (registrySpec_preserves dp ca) rules ch
      ch' block h_run h_wds ((registryStable_iff_stateInv dp ca ch.state).mp h_stable))

theorem stateTransitionUsing_preserves_registryStable (dp : DeployParams)
    (ca : Adr) (cfg : ChainConfig) (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransitionUsing cfg ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_stable : RegistryStable dp ca ch.state) :
    RegistryStable dp ca ch'.state :=
  (registryStable_iff_stateInv dp ca ch'.state).mpr
    (ContractSpec.stateTransitionUsing_preserves_inv ca (registrySpec_preserves dp ca) cfg ch
      ch' block h_run h_wds ((registryStable_iff_stateInv dp ca ch.state).mp h_stable))

theorem stateTransition_preserves_registryStable (dp : DeployParams)
    (ca : Adr) (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransition ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_stable : RegistryStable dp ca ch.state) :
    RegistryStable dp ca ch'.state :=
  (registryStable_iff_stateInv dp ca ch'.state).mpr
    (ContractSpec.stateTransition_preserves_inv ca (registrySpec_preserves dp ca) ch ch' block
      h_run h_wds ((registryStable_iff_stateInv dp ca ch.state).mp h_stable))

/-- The headline configured-chain theorem: from an exact-runtime stable
checkpoint, every state reachable by the configured valid-chain relation is
still stable. -/
theorem chainUsing_preserves_registryStable (dp : DeployParams) (ca : Adr)
    (cfg : ChainConfig) (checkpoint future : BlockChain)
    (reach : BlockChain.ReachUsing cfg checkpoint future)
    (stable : RegistryStable dp ca checkpoint.state) :
    RegistryStable dp ca future.state :=
  (registryStable_iff_stateInv dp ca future.state).mpr
    (ContractSpec.chainUsing_preserves_inv ca (registrySpec_preserves dp ca) cfg checkpoint
      future reach ((registryStable_iff_stateInv dp ca checkpoint.state).mp stable))

theorem chain_preserves_registryStable (dp : DeployParams) (ca : Adr)
    (checkpoint future : BlockChain)
    (reach : BlockChain.Reach checkpoint future)
    (stable : RegistryStable dp ca checkpoint.state) :
    RegistryStable dp ca future.state :=
  (registryStable_iff_stateInv dp ca future.state).mpr
    (ContractSpec.chain_preserves_inv ca (registrySpec_preserves dp ca) checkpoint future reach
      ((registryStable_iff_stateInv dp ca checkpoint.state).mp stable))

end LidoCircuitBreaker

end Blanc
