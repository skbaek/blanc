import Blanc.DripClock
import Blanc.ExecutionFrameTime
import Blanc.ExecutionHistoryAdmission
import Blanc.DripMonotoneHistory

namespace Blanc

open Jaune

namespace Drip

open ExecutionTrace

private theorem exec_clock_admitted
    {T : Nat} {ca : Adr} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
    (htime : sevm.benvStat.time.toNat ≤ T) :
    Exec.FrameAdmitted ca (ClockEntry T) run := by
  intro root member target
  have hstat := Exec.frameAdmitted_benvStat run ca root member target
  dsimp [ClockEntry]
  rw [hstat]
  exact htime

private theorem processMessage_clock_admitted
    {T : Nat} {ca : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessMessageTrace msg (.ok post))
    (htime : msg.benv.stat.time.toNat ≤ T) :
    trace.FrameAdmitted ca (ClockEntry T) := by
  rcases trace with ⟨slot, retained, run⟩
  exact RetainedXlot.frameAdmitted_benvStat_of_runFrame (Q := fun stat =>
    stat.time.toNat ≤ T) retained run (by
      simpa [Jaune.Frame.ofCall, Msg.withBenv] using htime) ca

private theorem processCreateMessage_clock_admitted
    {T : Nat} {ca : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessCreateMessageTrace msg (.ok post))
    (htime : msg.benv.stat.time.toNat ≤ T) :
  trace.FrameAdmitted ca (ClockEntry T) := by
  change trace.retained.FrameAdmitted ca (ClockEntry T)
  exact RetainedXlot.frameAdmitted_benvStat_of_runFrame (Q := fun stat =>
    stat.time.toNat ≤ T) trace.retained trace.run (by
      simpa [Jaune.Frame.ofCreate, processCreateMessage.msg, Msg.withBenv,
        addCreatedAccount, Benv.setStor, Benv.incrNonce]
        using htime) ca

private theorem messageCall_clock_admitted
    {T : Nat} {ca : Adr} {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (htime : msg.benv.stat.time.toNat ≤ T) :
    trace.FrameAdmitted ca (ClockEntry T) := by
  cases trace with
  | createCollision => trivial
  | createRun target collision evm core coreTrace result =>
      exact RetainedXlot.frameAdmitted_benvStat_of_runFrame (Q := fun stat =>
        stat.time.toNat ≤ T) coreTrace.retained coreTrace.run (by
          simpa [Jaune.Frame.ofCreate, processCreateMessage.msg, Msg.withBenv,
            addCreatedAccount, Benv.setStor, Benv.incrNonce]
            using htime) ca
  | callRun target delegated refund delegation execMsg execMsgEq evm core
      coreTrace result =>
      subst execMsgEq
      exact processMessage_clock_admitted coreTrace (by
        have hstat := messageCallExecutionMessage_benv_stat delegated
        have hdelegation := messageCallDelegation_benv_stat delegation
        rw [hstat, hdelegation]
        exact htime)

private theorem transaction_clock_admitted
    {T : Nat} {ca : Adr} {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (htime : benv.stat.time.toNat ≤ T) :
    trace.FrameAdmitted ca (ClockEntry T) := by
  change trace.message.FrameAdmitted ca (ClockEntry T)
  have hmsg : trace.msg.benv.stat.time.toNat ≤ T := by
    rw [prepareMessage_benv trace.prepared]
    exact htime
  exact messageCall_clock_admitted trace.message hmsg

private theorem transactionList_clock_admitted
    {T : Nat} {ca : Adr} {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (htime : benv.stat.time.toNat ≤ T) :
    trace.FrameAdmitted ca (ClockEntry T) := by
  induction trace with
  | nil => trivial
  | cons head tail ih =>
      refine ⟨transaction_clock_admitted head ?_, ih ?_⟩
      · simpa [prepareMessage_benv] using htime
      · exact htime

private theorem systemMessage_clock_admitted
    {T : Nat} {ca : Adr} {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (htime : benv.stat.time.toNat ≤ T) :
    trace.FrameAdmitted ca (ClockEntry T) := by
  change trace.message.FrameAdmitted ca (ClockEntry T)
  exact messageCall_clock_admitted trace.message htime

private theorem requests_clock_admitted
    {T : Nat} {ca : Adr} {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (htime : benv.stat.time.toNat ≤ T) :
    trace.FrameAdmitted ca (ClockEntry T) := by
  refine ⟨?_, ?_⟩
  · exact systemMessage_clock_admitted trace.withdrawal htime
  · exact systemMessage_clock_admitted trace.consolidation htime

private theorem body_clock_admitted
    {T : Nat} {ca : Adr} {benv : Benv}
    {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (htime : benv.stat.time.toNat ≤ T) :
    trace.FrameAdmitted ca (ClockEntry T) := by
  have htransactionTime : trace.transactionBenv.stat.time.toNat ≤ T := by
    rw [trace.transactions.stat_eq]
    exact htime
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact systemMessage_clock_admitted trace.beacon htime
  · exact systemMessage_clock_admitted trace.history htime
  · exact transactionList_clock_admitted trace.transactions htime
  · exact requests_clock_admitted trace.requests htransactionTime

theorem bodyOccurrence_clock (chi0 rho0 T : Nat) (ca : Adr) :
    (dripClockSpec chi0 rho0 T).SoundAdmitted ca (ClockEntry T) :=
  dripClockSpec_soundAdmitted chi0 rho0 T ca

theorem exec_clockInv
    {chi0 rho0 T : Nat} {ca : Adr} {sevm : Sevm} {pre post : Devm}
    (h_run : exec ⟨0, sevm, pre⟩ = .ok post)
    (h_code : sevm.currentTarget = ca →
      some sevm.code.toList = Prog.compile runtime)
    (h_wf : sevm.currentTarget = ca → Mem.Wf pre.memory)
    (h_pc : (dripClockSpec chi0 rho0 T).Pre ca sevm pre)
    (htime : sevm.benvStat.time.toNat ≤ T)
    (hfork : CoveredFork sevm.benvStat.fork) :
    (dripClockSpec chi0 rho0 T).StateInv ca post.state := by
  obtain ⟨exc⟩ := (exec_iff_exec_eq 0 sevm pre (.ok post)).mpr h_run
  exact ContractSpec.StateInv.of_exec_precond_admitted
    (dripClockSpec_preservesAdmitted chi0 rho0 T ca)
    hfork h_pc h_code h_wf exc (exec_clock_admitted (ca := ca) exc htime)

theorem processMessage_clock
    {chi0 rho0 T : Nat} {ca : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessMessageTrace msg (.ok post))
    (ready : (dripClockSpec chi0 rho0 T).MessageRunReady ca msg)
    (htime : msg.benv.stat.time.toNat ≤ T)
    (hfork : CoveredFork msg.benv.stat.fork) :
    (dripClockSpec chi0 rho0 T).StateInv ca post.state :=
  trace.stateInv_admitted
    (dripClockSpec_preservesAdmitted chi0 rho0 T ca)
    hfork (processMessage_clock_admitted trace htime) ready

theorem processCreateMessage_clock
    {chi0 rho0 T : Nat} {ca : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessCreateMessageTrace msg (.ok post))
    (targetNone : msg.target.isNone = true)
    (targetNe : msg.currentTarget ≠ ca)
    (ready : (dripClockSpec chi0 rho0 T).MsgInv ca msg)
    (htime : msg.benv.stat.time.toNat ≤ T)
    (hfork : CoveredFork msg.benv.stat.fork) :
    (dripClockSpec chi0 rho0 T).StateInv ca post.state :=
  trace.stateInv_admitted
    (dripClockSpec_preservesAdmitted chi0 rho0 T ca)
    hfork (processCreateMessage_clock_admitted trace htime)
    targetNone targetNe ready

theorem messageCall_clock
    {chi0 rho0 T : Nat} {ca : Adr} {msg : Msg} {state : State}
    {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (inv : (dripClockSpec chi0 rho0 T).MsgInv ca msg)
    (htime : msg.benv.stat.time.toNat ≤ T)
    (hfork : CoveredFork msg.benv.stat.fork) :
    (dripClockSpec chi0 rho0 T).StateInv ca state :=
  (trace.stateInv_admitted
    (dripClockSpec_preservesAdmitted chi0 rho0 T ca)
    hfork (messageCall_clock_admitted trace htime) inv).1

theorem transaction_clock
    {chi0 rho0 T : Nat} {ca : Adr} {benv : Benv} {bout bout' : BlockOutput}
    {tx : Tx} {index : Nat} {state : State}
    (trace : TransactionTrace benv bout tx index state bout')
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (inv : (dripClockSpec chi0 rho0 T).BenvInv ca benv)
    (htime : benv.stat.time.toNat ≤ T)
    (hfork : CoveredFork benv.stat.fork) :
    (dripClockSpec chi0 rho0 T).BenvInv ca (benv.withState state) :=
  trace.benvInv_admitted
    (dripClockSpec_preservesAdmitted chi0 rho0 T ca)
    hfork (transaction_clock_admitted trace htime) sumNof inv

theorem transactionList_clock
    {chi0 rho0 T : Nat} {ca : Adr} {txs : List (Nat × Tx)}
    {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (inv : (dripClockSpec chi0 rho0 T).BenvInv ca benv)
    (htime : benv.stat.time.toNat ≤ T)
    (hfork : CoveredFork benv.stat.fork) :
    (dripClockSpec chi0 rho0 T).BenvInv ca finalBenv :=
  trace.benvInv_admitted
    (dripClockSpec_preservesAdmitted chi0 rho0 T ca)
    hfork (transactionList_clock_admitted trace htime) sumNof inv

theorem systemMessage_clock
    {chi0 rho0 T : Nat} {ca : Adr} {benv : Benv} {target : Adr}
    {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (inv : (dripClockSpec chi0 rho0 T).BenvInv ca benv)
    (htime : benv.stat.time.toNat ≤ T)
    (hfork : CoveredFork benv.stat.fork) :
    (dripClockSpec chi0 rho0 T).BenvInv ca (benv.withState state) :=
  trace.benvInv_admitted
    (dripClockSpec_preservesAdmitted chi0 rho0 T ca)
    hfork (systemMessage_clock_admitted trace htime) inv

theorem requests_clock
    {chi0 rho0 T : Nat} {ca : Adr} {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (inv : (dripClockSpec chi0 rho0 T).BenvInv ca benv)
    (htime : benv.stat.time.toNat ≤ T)
    (hfork : CoveredFork benv.stat.fork) :
    (dripClockSpec chi0 rho0 T).StateInv ca state :=
  (trace.stateInv_and_sum_le_admitted
    (dripClockSpec_preservesAdmitted chi0 rho0 T ca)
    hfork (requests_clock_admitted trace htime) inv).1

theorem directWithdrawal_clock
    {chi0 rho0 T : Nat} {ca : Adr} {benv : Benv} {wds : List Withdrawal}
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (inv : (dripClockSpec chi0 rho0 T).BenvInv ca benv)
    (htime : benv.stat.time.toNat ≤ T) :
    (dripClockSpec chi0 rho0 T).StateInv ca
      (processWithdrawalsState benv.state wds) := by
  have post := benvInv_processWithdrawalsState
    (c := dripClockSpec chi0 rho0 T) inv bound
  have _htime : benv.stat.time.toNat ≤ T := htime
  exact post.1

theorem body_clock
    {chi0 rho0 T : Nat} {ca : Adr} {benv : Benv}
    {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (inv : (dripClockSpec chi0 rho0 T).BenvInv ca benv)
    (htime : benv.stat.time.toNat ≤ T)
    (hfork : CoveredFork benv.stat.fork) :
    (dripClockSpec chi0 rho0 T).StateInv ca state :=
  trace.stateInv_admitted
    (dripClockSpec_preservesAdmitted chi0 rho0 T ca)
    hfork (body_clock_admitted trace htime) bound inv

theorem configuredBlock_clock
    {chi0 rho0 T : Nat} {ca : Adr} {cfg : ChainConfig}
    {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post)
    (inv : (dripClockSpec chi0 rho0 T).StateInv ca pre.state)
    (htime : trace.block.header.timestamp.toB256.toNat ≤ T) :
    (dripClockSpec chi0 rho0 T).StateInv ca post.state := by
  have admitted : trace.FrameAdmitted ca (ClockEntry T) := by
    change trace.bodyTrace.FrameAdmitted ca (ClockEntry T)
    exact body_clock_admitted trace.bodyTrace (by
      simpa [initBenv, initBenvStat] using htime)
  exact trace.stateInv_admitted
    (dripClockSpec_preservesAdmitted chi0 rho0 T ca) admitted inv

private theorem deployed_blocks_getLast_of_transition
    {fork : Fork} {base deployed : BlockChain} {block : Block}
    (core : stateTransitionAt fork base block = .ok deployed) :
    deployed.blocks.getLast? = some block := by
  rw [stateTransitionAt_eq_ok_iff, stateTransitionE] at core
  obtain ⟨_, _, core⟩ := Except.bind_eq_ok core
  obtain ⟨_, _, core⟩ := Except.bind_eq_ok core
  dsimp only at core
  obtain ⟨⟨bodyState, blockOutput⟩, _, core⟩ := Except.bind_eq_ok core
  dsimp only at core
  obtain ⟨_, _, core⟩ := Except.bind_eq_ok core
  obtain ⟨_, _, final⟩ := Except.bind_eq_ok core
  have blocks := congrArg (fun chain : BlockChain => chain.blocks.getLast?)
    (Except.ok.inj final)
  simpa only [appendBlock_getLast?] using blocks.symm

theorem DeploymentRoot.rho_le_head_timestamp
    {cfg : ChainConfig} {base deployed : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca) :
    ∀ t, deployed.blocks.getLast?.map (·.header.timestamp) = some t →
      rhoN (deployed.state.getStor ca) ≤ t := by
  intro t hlast
  rcases root.execution with
    ⟨rules, cb, deploymentTxBytes, deploymentTx, sender, ctx, post, bout,
      hbase, hblock, hcovered, htx, hsuffix, htransition, hbody, hpost, hreceipt⟩
  have hcb := deployed_blocks_getLast_of_transition htransition
  rw [hcb] at hlast
  have htime : cb.block.header.timestamp = t := Option.some.inj hlast
  have hrho : (post.getStor ca).get rhoSlot =
      cb.block.header.timestamp.toB256 := htx.rho.trans ctx.msg_time_eq
  change ((deployed.state.getStor ca).get rhoSlot).toNat ≤ t
  rw [← hpost, hrho, htime]
  rw [B256.toNat_toB256]
  simp only [Nat.lo]
  exact Nat.mod_le _ _

/-- Anti-vacuity of `history_clockInv`: every configured history from a
deployment root has a head block, so that theorem's antecedent
`future.blocks.getLast?.map (·.header.timestamp) = some t` is satisfiable. -/
theorem configuredHistory_has_head_timestamp
    {cfg : ChainConfig} {base deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca)
    (history : ConfiguredHistoryTrace cfg deployed future) :
    ∃ t, future.blocks.getLast?.map (·.header.timestamp) = some t := by
  induction history with
  | refl hcfg hctx hid =>
      rcases root.execution with
        ⟨rules, cb, deploymentTxBytes, deploymentTx, sender, ctx, post, bout,
          hbase, hblock, hcovered, htx, hsuffix, htransition, hbody, hpost, hreceipt⟩
      have hcb := deployed_blocks_getLast_of_transition htransition
      exact ⟨cb.block.header.timestamp, by simp [hcb]⟩
  | @step current future prior block ih =>
      exact ⟨block.block.header.timestamp, by
        rw [block.post_blocks_getLast]
        rfl⟩

theorem history_clockInv
    {cfg : ChainConfig} {base deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca)
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg deployed future)
    (hcov : ∀ timestamp fork,
      cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    ∀ t, future.blocks.getLast?.map (·.header.timestamp) = some t →
      ClockInv (chiN (deployed.state.getStor ca)) (rhoN (deployed.state.getStor ca))
        t (future.state.getStor ca) := by
  induction history with
  | refl hcfg hctx hid =>
      intro t hlast
      have hmono := root.monoStateInv
      exact ⟨hmono.inv, root.rho_le_head_timestamp t hlast⟩
  | @step current future prior block ih =>
      intro t hlast
      obtain ⟨tprev, hprev⟩ := configuredHistory_has_head_timestamp root prior
      have hprevInv := ih tprev hprev
      have hparentExists : ∃ parent, current.blocks.getLast? = some parent := by
        cases h : current.blocks.getLast? with
        | none => simp [h] at hprev
        | some parent => exact ⟨parent, rfl⟩
      obtain ⟨parent, hparent⟩ := hparentExists
      have hprevTime : parent.header.timestamp = tprev := by
        rw [hparent] at hprev
        exact Option.some.inj hprev
      have hlt := block.parent_timestamp_lt hparent
      have hle : tprev ≤ block.block.header.timestamp := by
        rw [← hprevTime]
        exact Nat.le_of_lt hlt
      have htime : block.block.header.timestamp = t := by
        rw [block.post_blocks_getLast] at hlast
        exact Option.some.inj hlast
      have hbaseInv := root.reachable_stateInv prior.toReachUsing hcov
      have hmonoBounds := configuredHistory_mono
        (chi0 := chiN (deployed.state.getStor ca))
        (rho0 := rhoN (deployed.state.getStor ca))
        prior root.monoStateInv hcov
      have hprevAtT :
          (dripClockSpec (chiN (deployed.state.getStor ca))
            (rhoN (deployed.state.getStor ca)) t).StateInv
            ca current.state := by
        refine ⟨hbaseInv.code, hbaseInv.side, ?_⟩
        exact ⟨⟨hbaseInv.inv, hmonoBounds.1, hmonoBounds.2⟩,
          le_trans hprevInv.2 (le_trans hle (Nat.le_of_eq htime))⟩
      have hblockInv := configuredBlock_clock
        (chi0 := chiN (deployed.state.getStor ca))
        (rho0 := rhoN (deployed.state.getStor ca))
        (T := t) (ca := ca) block hprevAtT (by
          rw [htime]
          rw [B256.toNat_toB256]
          simp only [Nat.lo]
          exact Nat.mod_le _ _)
      exact hblockInv.inv

end Drip

end Blanc
