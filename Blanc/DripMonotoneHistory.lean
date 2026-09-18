-- DRIP R4: the monotone invariant through the retained execution ladder.

import Blanc.DripDeploy
import Blanc.DripHistory
import Blanc.DripMonotone
import Blanc.ExecutionBodyEffects
import Blanc.ExecutionHistoryEffects
import Blanc.ExecutionTransactionEffects

namespace Blanc

open Jaune

namespace Drip

open ExecutionTrace

/-! The named R4 rungs are deliberately thin adapters: the execution facts
    live in the contract-neutral ladder modules, while `MonoInv` supplies the
    two scalar projections. -/

/-- Rung 0: the deployment state is rooted at its own index and clock. -/
theorem DeploymentRoot.monoStateInv
    (root : DeploymentRoot cfg base deployed ca) :
    (dripMonoSpec (chiN (deployed.state.getStor ca))
      (rhoN (deployed.state.getStor ca))).StateInv ca deployed.state := by
  have hroot := root.stateInv
  refine ⟨hroot.code, hroot.side, ?_⟩
  exact ⟨hroot.inv, le_rfl, le_rfl⟩

/-- The deployment execution witness exposes the rho write at the canonical
    deployment boundary.  The structure keeps this witness existential so no
    additional field is needed on `DeploymentRoot`. -/
theorem DeploymentRoot.rho
    (root : DeploymentRoot cfg base deployed ca) :
    ∃ (rules : ForkRules) (cb : CanonicalBlock)
        (deploymentTx : Tx) (sender : Adr)
        (ctx : PreparedDeploymentContext cfg rules base cb deploymentTx sender ca)
        (post : State) (bout : BlockOutput),
      CanonicalDeploymentTransactionResult cfg rules ca ctx post bout ∧
        post = deployed.state ∧
        (post.getStor ca).get rhoSlot = cb.block.header.timestamp.toB256 := by
  rcases root.execution with
    ⟨rules, cb, _, deploymentTx, sender, ctx, post, bout,
      _, _, htx, _, _, _, hpost, _⟩
  refine ⟨rules, cb, deploymentTx, sender, ctx, post, bout,
    htx, hpost, ?_⟩
  exact htx.rho.trans ctx.msg_time_eq

private theorem monoStateInv_of_stateInv
    {chi0 rho0 : Nat} {ca : Adr} {state : State}
    (h : dripSpec.StateInv ca state)
    (hchi : chi0 ≤ chiN (state.getStor ca))
    (hrho : rho0 ≤ rhoN (state.getStor ca)) :
    (dripMonoSpec chi0 rho0).StateInv ca state := by
  exact ⟨h.code, h.side, ⟨h.inv, hchi, hrho⟩⟩

/-- The index is monotone along every configured continuation from deployment. -/
theorem DeploymentRoot.reachable_chi_mono
    (root : DeploymentRoot cfg base deployed ca)
    (reach : BlockChain.ReachUsing cfg deployed future) :
    chiN (deployed.state.getStor ca) ≤ chiN (future.state.getStor ca) := by
  have hpost := ContractSpec.chainUsing_preserves_inv
    (c := dripMonoSpec (chiN (deployed.state.getStor ca))
      (rhoN (deployed.state.getStor ca))) ca
    (dripMonoSpec_preserves (chiN (deployed.state.getStor ca))
      (rhoN (deployed.state.getStor ca)) ca)
    cfg deployed future reach root.monoStateInv
  exact hpost.inv.2.1

/-- The accrual clock is monotone along every configured continuation from deployment. -/
theorem DeploymentRoot.reachable_rho_mono
    (root : DeploymentRoot cfg base deployed ca)
    (reach : BlockChain.ReachUsing cfg deployed future) :
    rhoN (deployed.state.getStor ca) ≤ rhoN (future.state.getStor ca) := by
  have hpost := ContractSpec.chainUsing_preserves_inv
    (c := dripMonoSpec (chiN (deployed.state.getStor ca))
      (rhoN (deployed.state.getStor ca))) ca
    (dripMonoSpec_preserves (chiN (deployed.state.getStor ca))
      (rhoN (deployed.state.getStor ca)) ca)
    cfg deployed future reach root.monoStateInv
  exact hpost.inv.2.2

/-- Two adjacent configured reaches compose to both scalar monotonicity facts. -/
theorem reach_chi_rho_mono
    (root : DeploymentRoot cfg base deployed ca)
    (r₁ : BlockChain.ReachUsing cfg deployed ch)
    (r₂ : BlockChain.ReachUsing cfg ch ch') :
    chiN (ch.state.getStor ca) ≤ chiN (ch'.state.getStor ca) ∧
      rhoN (ch.state.getStor ca) ≤ rhoN (ch'.state.getStor ca) := by
  have hch := root.reachable_stateInv r₁
  have hchMono := monoStateInv_of_stateInv hch le_rfl le_rfl
  have hpost := ContractSpec.chainUsing_preserves_inv
    (c := dripMonoSpec (chiN (ch.state.getStor ca))
      (rhoN (ch.state.getStor ca))) ca
    (dripMonoSpec_preserves (chiN (ch.state.getStor ca))
      (rhoN (ch.state.getStor ca)) ca)
    cfg ch ch' r₂ hchMono
  exact ⟨hpost.inv.2.1, hpost.inv.2.2⟩

/-- At a successful compiled DRIP endpoint boundary, the rho write is exactly
    the execution timestamp, hence the post rho is bounded by that timestamp.
    A configured-block wrapper can transport the timestamp equality separately. -/
theorem rho_le_timestamp_at_boundary
    {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = dripSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty) :
    rhoN (post.state.getStor sevm.currentTarget) ≤ sevm.benvStat.time.toNat := by
  rcases drip_exec_effect exc hcode hsel hnonempty hcanon with
    ⟨_, _, _, _, _, _, _, hstor, _⟩
  change ((Devm.getStor post sevm.currentTarget).get rhoSlot).toNat ≤
    sevm.benvStat.time.toNat
  rw [hstor, Stor.get_set_self]


/-- Rung 1: a DRIP body occurrence uses the source-level soundness rung. -/
theorem bodyOccurrence_mono (chi0 rho0 : Nat) (ca : Adr) :
    (dripMonoSpec chi0 rho0).Sound ca :=
  dripMonoSpec_sound chi0 rho0 ca

/-- Rung 2: a compiled execution preserves both scalar lower bounds. -/
theorem exec_monoInv
    {ca : Adr} {sevm : Sevm} {pre post : Devm}
    (h_run : exec ⟨0, sevm, pre⟩ = .ok post)
    (h_code : sevm.currentTarget = ca →
      some sevm.code.toList = Prog.compile runtime)
    (h_wf : sevm.currentTarget = ca → Mem.Wf pre.memory)
    (h_pc : (dripMonoSpec (chiN (pre.state.getStor ca))
      (rhoN (pre.state.getStor ca))).Pre ca sevm pre) :
    chiN (pre.state.getStor ca) ≤ chiN (post.state.getStor ca) ∧
      rhoN (pre.state.getStor ca) ≤ rhoN (post.state.getStor ca) := by
  obtain ⟨exc⟩ := (exec_iff_exec_eq 0 sevm pre (.ok post)).mpr h_run
  have hpost := ContractSpec.StateInv.of_exec_precond
    (c := dripMonoSpec (chiN (pre.state.getStor ca))
      (rhoN (pre.state.getStor ca)))
    (wa := ca)
    (dripMonoSpec_preserves (chiN (pre.state.getStor ca))
      (rhoN (pre.state.getStor ca)) ca)
    h_pc h_code h_wf exc
  exact ⟨hpost.inv.2.1, hpost.inv.2.2⟩

/-- Rung 3: a successful message preserves both scalar lower bounds. -/
theorem processMessage_mono
    {chi0 rho0 : Nat} {ca : Adr} {msg : Msg} {evm : Devm}
    (h_run : processMessage msg = .ok evm)
    (h_code : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile runtime)
    (h_ne : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (h_val0 : msg.shouldTransferValue = false → msg.currentTarget = ca →
      msg.value = 0)
    (h_inv : (dripMonoSpec chi0 rho0).StateInv ca msg.benv.state) :
    chi0 ≤ chiN (evm.state.getStor ca) ∧
      rho0 ≤ rhoN (evm.state.getStor ca) := by
  have hpost := ContractSpec.processMessage_preserves_inv
    (c := dripMonoSpec chi0 rho0) (wa := ca)
    (dripMonoSpec_preserves chi0 rho0 ca)
    h_run h_code h_ne h_val0 h_inv
  exact ⟨hpost.inv.2.1, hpost.inv.2.2⟩

/-- Rung 3': an errored message restores the entry storage literally. -/
theorem message_error_mono
    {chi0 rho0 : Nat} {ca : Adr} {msg : Msg} {xl : Xlot} {out : Devm}
    (h_run : ProcessMessage msg xl (.ok out))
    (h_error : out.error.isSome)
    (h_code : msg.code.toList = code)
    (h_inv : MonoInv chi0 rho0 (msg.benv.state.getStor ca)) :
    MonoInv chi0 rho0 (out.state.getStor ca) := by
  have hstor := drip_message_error_getStor h_run h_error h_code ca
  change MonoInv chi0 rho0 (Devm.getStor out ca)
  rw [hstor]
  exact h_inv

/-- Rung 4: one retained transaction preserves both scalar lower bounds. -/
theorem transaction_mono
    {chi0 rho0 : Nat} {ca : Adr} {benv : Benv} {bout bout' : BlockOutput}
    {tx : Tx} {index : Nat} {state : State}
    (trace : TransactionTrace benv bout tx index state bout')
    (h_sum : sum benv.state.bal < 2 ^ 256)
    (h_inv : (dripMonoSpec chi0 rho0).BenvInv ca benv) :
    chi0 ≤ chiN (state.getStor ca) ∧ rho0 ≤ rhoN (state.getStor ca) := by
  have hpost := trace.benvInv (dripMonoSpec_preserves chi0 rho0 ca)
    h_sum h_inv
  exact ⟨hpost.state.inv.2.1, hpost.state.inv.2.2⟩

/-- Rung 5: a retained transaction list preserves both scalar lower bounds. -/
theorem transactionList_mono
    {chi0 rho0 : Nat} {ca : Adr} {txs : List (Nat × Tx)}
    {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (h_sum : sum benv.state.bal < 2 ^ 256)
    (h_inv : (dripMonoSpec chi0 rho0).BenvInv ca benv) :
    chi0 ≤ chiN (finalBenv.state.getStor ca) ∧
      rho0 ≤ rhoN (finalBenv.state.getStor ca) := by
  have hpost := trace.benvInv (dripMonoSpec_preserves chi0 rho0 ca)
    h_sum h_inv
  exact ⟨hpost.state.inv.2.1, hpost.state.inv.2.2⟩

/-- Rung 6: a retained system message preserves both scalar lower bounds. -/
theorem systemMessage_mono
    {chi0 rho0 : Nat} {ca : Adr} {benv : Benv} {target : Adr}
    {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (h_inv : (dripMonoSpec chi0 rho0).BenvInv ca benv) :
    chi0 ≤ chiN (state.getStor ca) ∧ rho0 ≤ rhoN (state.getStor ca) := by
  have hpost := trace.benvInv (dripMonoSpec_preserves chi0 rho0 ca) h_inv
  exact ⟨hpost.state.inv.2.1, hpost.state.inv.2.2⟩

/-- Rung 7: request processing preserves both scalar lower bounds. -/
theorem requests_mono
    {chi0 rho0 : Nat} {ca : Adr} {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (h_inv : (dripMonoSpec chi0 rho0).BenvInv ca benv) :
    chi0 ≤ chiN (state.getStor ca) ∧ rho0 ≤ rhoN (state.getStor ca) := by
  have hpost := trace.stateInv_and_sum_le
    (dripMonoSpec_preserves chi0 rho0 ca) h_inv
  exact ⟨hpost.1.inv.2.1, hpost.1.inv.2.2⟩

/-- Rung 8: direct withdrawals preserve both scalar lower bounds. -/
theorem withdrawals_mono
    {chi0 rho0 : Nat} {ca : Adr} {benv : Benv} {wds : List Withdrawal}
    (h_bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (h_inv : (dripMonoSpec chi0 rho0).BenvInv ca benv) :
    chi0 ≤ chiN ((processWithdrawalsState benv.state wds).getStor ca) ∧
      rho0 ≤ rhoN ((processWithdrawalsState benv.state wds).getStor ca) := by
  have hpost := benvInv_processWithdrawalsState
    (c := dripMonoSpec chi0 rho0) (ca := ca) h_inv h_bound
  exact ⟨hpost.state.inv.2.1, hpost.state.inv.2.2⟩

/-- Rung 9: a block body preserves both scalar lower bounds. -/
theorem body_mono
    {chi0 rho0 : Nat} {ca : Adr} {benv : Benv}
    {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (h_run : applyBody benv txs wds = .ok (state, bout))
    (h_wds : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (h_inv : (dripMonoSpec chi0 rho0).BenvInv ca benv) :
    chi0 ≤ chiN (state.getStor ca) ∧ rho0 ≤ rhoN (state.getStor ca) := by
  have hpost := ContractSpec.applyBody_preserves_inv
    (c := dripMonoSpec chi0 rho0) ca
    (dripMonoSpec_preserves chi0 rho0 ca)
    benv txs wds state bout h_run h_wds h_inv
  exact ⟨hpost.inv.2.1, hpost.inv.2.2⟩

/-- Rung 10: a configured block preserves both scalar lower bounds. -/
theorem configuredBlock_mono
    {chi0 rho0 : Nat} {ca : Adr} {cfg : ChainConfig}
    {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post)
    (h_inv : (dripMonoSpec chi0 rho0).StateInv ca pre.state) :
    chi0 ≤ chiN (post.state.getStor ca) ∧
      rho0 ≤ rhoN (post.state.getStor ca) := by
  have hpost := ContractSpec.stateTransitionUsing_preserves_inv
    (c := dripMonoSpec chi0 rho0) ca
    (dripMonoSpec_preserves chi0 rho0 ca) cfg pre post trace.block
    trace.transition trace.bound h_inv
  exact ⟨hpost.inv.2.1, hpost.inv.2.2⟩

/-- Rung 11: a configured history preserves both scalar lower bounds. -/
theorem configuredHistory_mono
    {chi0 rho0 : Nat} {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (h_inv : (dripMonoSpec chi0 rho0).StateInv ca checkpoint.state) :
    chi0 ≤ chiN (future.state.getStor ca) ∧
      rho0 ≤ rhoN (future.state.getStor ca) := by
  have hpost := history.stateInv
    (dripMonoSpec_preserves chi0 rho0 ca) h_inv
  exact ⟨hpost.inv.2.1, hpost.inv.2.2⟩

end Drip

end Blanc
