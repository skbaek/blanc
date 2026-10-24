import Blanc.LadderBase
import Blanc.ExecutionTrace
import Blanc.ExecutionTraceCodeKeep
import Blanc.ExecutionTransactionEffects
import Blanc.ExecutionHistoryInCodeAt
import Blanc.ExecutionHistoryInForkFacts
import Blanc.HistoricalFork

/-!
# Neutral (`In`) non-deletion along executions and transactions

`In` forms of the non-deletion (`NoDel`) chain
(`Blanc/LadderBase.lean`, `Blanc/ExecutionTraceCodeKeep.lean`): a settled
message, create, or message call keeps `wa` out of every deletion set, and a
transaction keeps a nonempty, non-delegating code at `wa`, without any
`CoveredFork` premise. Coverage is replaced by two explicit schedule
hypotheses — `stateGas = none` and `selfdestructOnlyCreated = true` — carried
to spawned children by the exact spawn environment equality
(`Evm.step_spawn_child_benvStat`) and discharged on `HistFork` by decision
(`HistFork.stateGas_none`,
`HistFork.selfdestructOnlyCreated_of_cancunOnwards`).

The interpreter-level step case doubles as the neutral twin of
`Evm.step_effectForkTerminal`/`Exec.effectForkTerminal`; the per-instruction
twins reuse the fork-free `Jinst.noDelCode_effect` and the existing neutral
`Ninst.inv_noDel_noStateGas` as-is.

Contract-neutral: no contract name in any statement.
-/

namespace Blanc

open Jaune

/-- A nonterminal instruction preserves `NoDelCode`, under `stateGas = none`.
Neutral twin of `Ninst.noDelCode_effectRec`. -/
lemma Ninst.noDelCode_effectRec_noStateGas (wa : Adr) (n : Ninst) :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {xl : Xlot} {out : Execution},
    sevm.benvStat.rules.stateGas = none → Xlot.Rel (Devm.NoDelCode wa) xl →
    Ninst.StepRun pc sevm pre n xl out →
    Execution.Rel (Devm.NoDelCode wa) pre out := by
  intro pc sevm pre xl out hsg hxl hrun
  have hnd := fun h =>
    Ninst.inv_noDel_noStateGas hsg (Xlot.invNoDel_of_rel hxl) hrun h
  cases out with
  | error e => exact hnd
  | ok d => exact hnd

/-- A terminal instruction preserves `NoDelCode`, under the EIP-6780 flag.
Neutral twin of `Linst.noDelCode_effectFork`. -/
lemma Linst.noDelCode_effect_of_onlyCreated (wa : Adr) (l : Linst) :
    ∀ {sevm : Sevm} {pre : Devm} {out : Execution},
    sevm.benvStat.rules.settle.selfdestructOnlyCreated = true →
    Linst.Run sevm pre l out → Execution.Rel (Devm.NoDelCode wa) pre out := by
  intro sevm pre out hflag hrun
  have hnd := fun h => Linst.inv_noDel (wa := wa) hrun h hflag
  cases out with
  | error e => exact hnd
  | ok d => exact hnd

/-- One interpreter step preserves any reflexive relation with neutral
per-instruction effects. Neutral twin of `Evm.step_effectForkTerminal`. -/
lemma Evm.step_effect_noStateGas {R : Devm → Devm → Prop}
    (hrefl : ReflexiveRel R)
    (hn : ∀ (n : Ninst) {pc : Nat} {sevm : Sevm} {pre : Devm} {xl : Xlot}
      {out : Execution},
      sevm.benvStat.rules.stateGas = none → Xlot.Rel R xl →
      Ninst.StepRun pc sevm pre n xl out → Execution.Rel R pre out)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ (l : Linst) {sevm : Sevm} {pre : Devm} {out : Execution},
      sevm.benvStat.rules.settle.selfdestructOnlyCreated = true →
      Linst.Run sevm pre l out → Execution.Rel R pre out)
    {pc : Nat} {sevm : Sevm} {devm : Devm} {xl : Xlot} {out : Execution}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hflag : sevm.benvStat.rules.settle.selfdestructOnlyCreated = true)
    (hxl : Xlot.Rel R xl)
    (hrun : Step.Run (Evm.step ⟨pc, sevm, devm⟩) xl out) :
    Execution.Rel R devm out := by
  rcases hgi : (Evm.getInst ⟨pc, sevm, devm⟩) with _ | i
  · rw [Evm.step_invOp hgi] at hrun
    obtain ⟨-, rfl⟩ := hrun
    exact hrefl _
  · cases i with
    | next n =>
      rw [Evm.step_next (n := n) hgi] at hrun
      exact hn n hsg hxl hrun
    | jump j =>
      rw [Evm.step_jump (j := j) hgi] at hrun
      obtain ⟨-, hcase⟩ := Step.run_ofJump hrun
      have hjr := hj j (evm := ⟨pc, sevm, devm⟩) (out := j.run ⟨pc, sevm, devm⟩) rfl
      rcases hcase with ⟨e, hje, rfl⟩ | ⟨pc', d, hje, rfl⟩ <;> rw [hje] at hjr <;>
        exact hjr
    | last l =>
      rw [Evm.step_last (l := l) hgi] at hrun
      obtain ⟨-, rfl⟩ := hrun
      exact hl l hflag rfl

/-- Per-instruction neutral effects compose into `Execution.Rel` for a
complete `Exec` derivation. Neutral twin of `Exec.effectForkTerminal`: tails
keep the same frame, children transport the schedule by the exact spawn
environment equality. -/
theorem Exec.effect_neutralSchedule {R : Devm → Devm → Prop}
    (hrefl : ReflexiveRel R) (htrans : TransitiveRel R)
    (hn : ∀ (n : Ninst) {pc : Nat} {sevm : Sevm} {pre : Devm} {xl : Xlot}
      {out : Execution},
      sevm.benvStat.rules.stateGas = none → Xlot.Rel R xl →
      Ninst.StepRun pc sevm pre n xl out → Execution.Rel R pre out)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ (l : Linst) {sevm : Sevm} {pre : Devm} {out : Execution},
      sevm.benvStat.rules.settle.selfdestructOnlyCreated = true →
      Linst.Run sevm pre l out → Execution.Rel R pre out)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hflag : sevm.benvStat.rules.settle.selfdestructOnlyCreated = true) :
    Execution.Rel R pre out := by
  have hcomp : ∀ {a b : Devm} {o : Execution},
      R a b → Execution.Rel R b o → Execution.Rel R a o := by
    intro a b o hab hbo
    cases o <;> exact htrans hab hbo
  have aux : ∀ {pc sevm pre out}, Exec pc sevm pre out →
      sevm.benvStat.rules.stateGas = none →
      sevm.benvStat.rules.settle.selfdestructOnlyCreated = true →
      Execution.Rel R pre out := by
    intro pc sevm pre out run hsg hflag
    revert hsg hflag
    induction run with
    | halt hstep =>
      intro hsg hflag
      exact Evm.step_effect_noStateGas hrefl hn hj hl hsg hflag (xl := .none)
        trivial (by rw [hstep]; exact ⟨rfl, rfl⟩)
    | cont hstep _ ih =>
      intro hsg hflag
      refine hcomp (?_ : R _ _) (ih hsg hflag)
      exact Evm.step_effect_noStateGas hrefl hn hj hl hsg hflag (xl := .none)
        (out := .ok _) trivial (by rw [hstep]; exact ⟨rfl, rfl⟩)
    | doneErr hstep henter hr =>
      intro hsg hflag
      exact Evm.step_effect_noStateGas hrefl hn hj hl hsg hflag (xl := .none)
        trivial (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hr.symm⟩)
    | doneOk hstep henter hr _ ih =>
      intro hsg hflag
      refine hcomp (?_ : R _ _) (ih hsg hflag)
      exact Evm.step_effect_noStateGas hrefl hn hj hl hsg hflag (xl := .none)
        (out := .ok _) trivial
        (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hr.symm⟩)
    | runErr hstep henter _ hr ihc =>
      intro hsg hflag
      exact Evm.step_effect_noStateGas hrefl hn hj hl hsg hflag
        (xl := .some ⟨_, _⟩)
        (ihc (by rw [Evm.step_spawn_child_benvStat hstep henter]; exact hsg)
          (by rw [Evm.step_spawn_child_benvStat hstep henter]; exact hflag))
        (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hr.symm⟩)
    | runOk hstep henter _ hr _ ihc ih =>
      intro hsg hflag
      refine hcomp (?_ : R _ _) (ih hsg hflag)
      exact Evm.step_effect_noStateGas hrefl hn hj hl hsg hflag
        (xl := .some ⟨_, _⟩) (out := .ok _)
        (ihc (by rw [Evm.step_spawn_child_benvStat hstep henter]; exact hsg)
          (by rw [Evm.step_spawn_child_benvStat hstep henter]; exact hflag))
        (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hr.symm⟩)
  exact aux run hsg hflag

/-- A complete execution preserves `NoDel`. Neutral twin of
`Exec.inv_noDel`. -/
lemma Exec.inv_noDel_noStateGas {wa : Adr} {pc : Nat} {sevm : Sevm}
    {devm : Devm} {exn : Execution}
    (run : Exec pc sevm devm exn)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hflag : sevm.benvStat.rules.settle.selfdestructOnlyCreated = true)
    (h : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  have heff := Exec.effect_neutralSchedule (noDelCode_refl_trans wa).1
    (noDelCode_refl_trans wa).2 (Ninst.noDelCode_effectRec_noStateGas wa)
    (Jinst.noDelCode_effect wa) (Linst.noDelCode_effect_of_onlyCreated wa)
    run hsg hflag
  cases exn with
  | error e => exact heff h
  | ok d => exact heff h

/-- A settled message preserves `NoDel`. Neutral twin of
`processMessage_preserves_noDel`. -/
theorem processMessage_preserves_noDel_noStateGas {wa : Adr} {msg : Msg}
    {evm : Devm}
    (hsg : msg.benv.stat.rules.stateGas = none)
    (hflag : msg.benv.stat.rules.settle.selfdestructOnlyCreated = true)
    (h_run : processMessage msg = .ok evm)
    (h : Msg.NoDel wa msg)
    (h_inherited : wa ∉ msg.inheritedDeletions) : Devm.NoDel wa evm := by
  obtain ⟨xl, hfill, hrel⟩ := of_processMessage msg (.ok evm) h_run
  have hinv : Xlot.InvNoDel wa xl := by
    rcases xl with _ | ⟨cevm, cexn⟩
    · trivial
    · intro hnd
      obtain ⟨exc⟩ := hfill
      have hbenv : cevm.sta.benvStat = msg.benv.stat := RunFrame.benvStat_eq hrel
      have hsg_c : cevm.sta.benvStat.rules.stateGas = none := by
        rw [hbenv]; exact hsg
      have hflag_c :
          cevm.sta.benvStat.rules.settle.selfdestructOnlyCreated = true := by
        rw [hbenv]; exact hflag
      exact Exec.inv_noDel_noStateGas exc hsg_c hflag_c hnd
  exact ProcessMessage.inv_noDel hinv hrel h h_inherited

/-- A settled create message preserves `NoDel`. Neutral twin of
`processCreateMessage_preserves_noDel`. -/
theorem processCreateMessage_preserves_noDel_noStateGas {wa : Adr} {msg : Msg}
    {evm : Devm}
    (hsg : msg.benv.stat.rules.stateGas = none)
    (hflag : msg.benv.stat.rules.settle.selfdestructOnlyCreated = true)
    (h_run : processCreateMessage msg = .ok evm)
    (h_ct : msg.currentTarget ≠ wa)
    (h : Msg.NoDel wa msg)
    (h_inherited : wa ∉ msg.inheritedDeletions) : Devm.NoDel wa evm := by
  rw [processCreateMessage_eq] at h_run
  have h_inv_cm : Msg.NoDel wa (processCreateMessage.msg msg) :=
    Msg.NoDel.processCreateMessage_msg h_ct h
  rcases hpm0 : processMessage (processCreateMessage.msg msg) with x | evm2
  · rw [hpm0, processCreateMessage.settle_error] at h_run
    cases h_run
  rw [hpm0] at h_run
  have h_rest := h_run
  have hsg' : (processCreateMessage.msg msg).benv.stat.rules.stateGas = none := by
    rw [processCreateMessage.msg_benvStat]; exact hsg
  have hflag' :
      (processCreateMessage.msg msg).benv.stat.rules.settle.selfdestructOnlyCreated
        = true := by
    rw [processCreateMessage.msg_benvStat]; exact hflag
  have h_pm : Devm.NoDel wa evm2 :=
    processMessage_preserves_noDel_noStateGas hsg' hflag' hpm0 h_inv_cm
      h_inherited
  unfold processCreateMessage.settle at h_rest
  dsimp only [bind, Except.bind] at h_rest
  · by_cases herr : evm2.error.isNone = true
    · rw [ite_eq_left herr] at h_rest
      rcases hcg : processCreateMessage.chargeCodeGas msg.benv.stat.rules evm2
        with ⟨err, evm3⟩ | evm3
      · rw [hcg] at h_rest
        cases err
        case halt reason =>
          rw [← Except.ok.inj h_rest]
          have h_ds : Devm.delSets evm3 = Devm.delSets evm2 :=
            chargeCodeGas_delSets_err hcg
          have h_atd_eq : evm3.accountsToDelete = evm2.accountsToDelete :=
            congrArg Prod.fst h_ds
          have h_ca_eq : evm3.createdAccounts = evm2.createdAccounts :=
            congrArg Prod.snd h_ds
          have h_atd : wa ∉ evm3.accountsToDelete := by
            rw [h_atd_eq]; exact h_pm.atd
          have h_ca : wa ∉ evm3.createdAccounts := by
            rw [h_ca_eq]; exact h_pm.ca
          unfold processCreateMessage.exceptionalHalt
          cases hsg_eq : msg.benv.stat.rules.stateGas <;>
            exact Devm.NoDel.of_eqs (d := evm3.rollback msg.benv.state
              msg.tenv.transientStorage) rfl rfl
              (Devm.NoDel.rollback h_atd h_ca h.code)
        all_goals cases h_rest
      · rw [hcg] at h_rest; dsimp only at h_rest
        rw [← Except.ok.inj h_rest]
        have h_ds : Devm.delSets evm3 = Devm.delSets evm2 :=
          chargeCodeGas_delSets_ok hcg
        have h_atd_eq : evm3.accountsToDelete = evm2.accountsToDelete :=
          congrArg Prod.fst h_ds
        have h_ca_eq : evm3.createdAccounts = evm2.createdAccounts :=
          congrArg Prod.snd h_ds
        have h_atd : wa ∉ evm3.accountsToDelete := by
          rw [h_atd_eq]; exact h_pm.atd
        have h_ca : wa ∉ evm3.createdAccounts := by
          rw [h_ca_eq]; exact h_pm.ca
        have h_gc : evm3.getCode wa = evm2.getCode wa := by
          have hh := processCreateMessage.chargeCodeGas_getCode_gen hcg wa
          simpa only [Execution.getCode] using hh
        refine ⟨h_atd, h_ca, ?_⟩
        show ((evm3.setCode msg.currentTarget ⟨⟨evm3.output⟩⟩).getCode wa).toList
          ≠ []
        rw [setCode_getCode h_ct, h_gc]
        exact h_pm.code
    · rw [ite_eq_right herr] at h_rest
      rw [← Except.ok.inj h_rest]
      exact (⟨h_pm.atd, h_pm.ca, h.code⟩ : Devm.NoDel wa ((evm2.rollback
        msg.benv.state msg.tenv.transientStorage).withStorageWrites
        msg.benv.storageWrites))

/-- A settled message call keeps `wa` out of the deletion set. Neutral twin
of `processMessageCall_preserves_noDel`. -/
theorem processMessageCall_preserves_noDel_noStateGas {wa : Adr} {msg : Msg}
    {st' : Jaune.State} {out : MsgCallOutput}
    (hsg : msg.benv.stat.rules.stateGas = none)
    (hflag : msg.benv.stat.rules.settle.selfdestructOnlyCreated = true)
    (h_run : processMessageCall msg = .ok ⟨st', out⟩)
    (h : Msg.NoDel wa msg)
    (h_not_del : ¬ isValidDelegation (msg.benv.state.getCode wa))
    (h_inherited : wa ∉ msg.inheritedDeletions) :
    wa ∉ out.accountsToDelete := by
  unfold processMessageCall at h_run
  split at h_run
  · unfold processMessageCall.create at h_run
    dsimp only at h_run
    rw [hsg] at h_run
    dsimp only at h_run
    split at h_run
    · injection h_run with h_eq
      injection h_eq with _ h_out
      subst h_out
      exact AdrSet.not_mem_empty
    · rename_i h_col
      simp only [Bool.not_eq_true] at h_col
      have h_ct := ne_wa_of_not_hasCodeOrNonce h.code h_col
      revert h_run
      rcases h_evm : processCreateMessage msg with ⟨err⟩ | ⟨evm⟩
      · simp only [Except.bimap, bind, Except.bind]
        intro h_run
        injection h_run
      · simp only [Except.bimap, bind, Except.bind]
        intro h_run
        have h_nodel := processCreateMessage_preserves_noDel_noStateGas hsg
          hflag h_evm h_ct h h_inherited
        change (if evm.error.isNone = true then _ else _) = _ at h_run
        split at h_run
        · split at h_run
          · injection h_run
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h_run
            rcases h_run with ⟨_, rfl⟩
            simp_all only [id_eq, ite_eq_left]
            exact h_nodel.atd
        · simp only [id_eq, Except.ok.injEq, Prod.mk.injEq] at h_run
          rcases h_run with ⟨_, rfl⟩
          simp_all only [Option.isNone_iff_eq_none, ne_eq, ↓reduceIte,
            Std.HashSet.not_mem_emptyWithCapacity, not_false_eq_true]
  · unfold processMessageCall.call at h_run
    simp only [hsg] at h_run
    rcases Except.bind_eq_ok h_run with ⟨⟨delegated, refund⟩, hauth, h_run⟩
    have hd_msg : Msg.NoDel wa delegated := by
      unfold processMessageCall.legacyAuthorization at hauth
      split at hauth
      · cases hauth; exact h
      · rcases Except.bind_eq_ok hauth with ⟨⟨msg', v⟩, hdel, hauth⟩
        cases hauth
        exact setDelegation_msg_noDel hdel h h_not_del
    have hd_sg : delegated.benv.stat.rules.stateGas = none := by
      unfold processMessageCall.legacyAuthorization at hauth
      split at hauth
      · cases hauth; exact hsg
      · rcases Except.bind_eq_ok hauth with ⟨⟨msg', v⟩, hdel, hauth⟩
        cases hauth
        rw [setDelegation_benvStat hdel]; exact hsg
    have hd_flag :
        delegated.benv.stat.rules.settle.selfdestructOnlyCreated = true := by
      unfold processMessageCall.legacyAuthorization at hauth
      split at hauth
      · cases hauth; exact hflag
      · rcases Except.bind_eq_ok hauth with ⟨⟨msg', v⟩, hdel, hauth⟩
        cases hauth
        rw [setDelegation_benvStat hdel]; exact hflag
    have hd_inh : wa ∉ delegated.inheritedDeletions := by
      unfold processMessageCall.legacyAuthorization at hauth
      split at hauth
      · cases hauth; exact h_inherited
      · rcases Except.bind_eq_ok hauth with ⟨⟨msg', v⟩, hdel, hauth⟩
        cases hauth
        rw [setDelegation_inheritedDeletions hdel]; exact h_inherited
    rcases Except.bind_eq_ok h_run with ⟨evm, hpm, h_run⟩
    have hpm' : processMessage delegated.resolveCodeDelegation = .ok evm := by
      cases hp : processMessage delegated.resolveCodeDelegation with
      | error e => simp only [hp, Except.bimap, bind, Except.bind, reduceCtorEq] at hpm
      | ok d => simpa only [hp, Except.bimap, bind, Except.bind, id_eq, Except.ok.injEq] using hpm
    clear hpm
    have hpc : Msg.NoDel wa delegated.resolveCodeDelegation := by
      unfold Msg.resolveCodeDelegation
      split <;> exact ⟨hd_msg.ca, hd_msg.code⟩
    have hsg_pc :
        delegated.resolveCodeDelegation.benv.stat.rules.stateGas = none := by
      unfold Msg.resolveCodeDelegation
      split <;> exact hd_sg
    have hflag_pc :
        delegated.resolveCodeDelegation.benv.stat.rules.settle.selfdestructOnlyCreated
          = true := by
      unfold Msg.resolveCodeDelegation
      split <;> exact hd_flag
    have hipc : wa ∉ delegated.resolveCodeDelegation.inheritedDeletions := by
      unfold Msg.resolveCodeDelegation
      split <;> exact hd_inh
    have hn := processMessage_preserves_noDel_noStateGas hsg_pc hflag_pc hpm'
      hpc hipc
    split at h_run
    · rename_i herr
      rcases Except.bind_eq_ok h_run with ⟨r, hr, h_run⟩
      have hh := Except.ok.inj h_run
      cases hh
      simpa only [herr, ↓reduceIte] using hn.atd
    · rename_i herr
      simp only [Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at h_run
      obtain ⟨_, rfl⟩ := h_run
      simp only [herr, ↓reduceIte]
      exact AdrSet.not_mem_empty

/-- Every deleted account of a settled message call differs from `wa`.
Neutral twin of `processMessageCall_accountsToDelete_ne`. -/
theorem processMessageCall_accountsToDelete_ne_noStateGas {wa : Adr}
    {msg : Msg} {st' : Jaune.State} {out : MsgCallOutput}
    (hsg : msg.benv.stat.rules.stateGas = none)
    (hflag : msg.benv.stat.rules.settle.selfdestructOnlyCreated = true)
    (h_run : processMessageCall msg = .ok ⟨st', out⟩)
    (h : Msg.NoDel wa msg)
    (h_not_del : ¬ isValidDelegation (msg.benv.state.getCode wa))
    (h_inherited : wa ∉ msg.inheritedDeletions) :
    ∀ a ∈ out.accountsToDelete.toList, a ≠ wa := by
  intro a ha heq
  subst heq
  exact processMessageCall_preserves_noDel_noStateGas hsg hflag h_run h
    h_not_del h_inherited (Std.HashSet.mem_toList.mp ha)

namespace ExecutionTrace

/-- Exact post-message transaction settlement form, without coverage: the
schedule facts enter as explicit hypotheses. Neutral twin of
`TransactionTrace.exists_finalStateForm`. -/
theorem TransactionTrace.exists_finalStateForm_noStateGas
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (hrefund : benv.stat.fork.ruleSet.settle.refundQuotient = 5)
    (hsweep : benv.stat.fork.ruleSet.settle.touchedSweep = false) :
    ∃ refundCounter : Nat,
      Int.toNat? trace.messageOut.refundCounter = some refundCounter ∧
      state =
        trace.messageOut.accountsToDelete.toList.foldl destroyAccount
          ((trace.messageState.addBal trace.sender
              ((tx.gas -
                  max (tx.gas - trace.messageOut.gasLeft -
                    min ((tx.gas - trace.messageOut.gasLeft) / 5)
                      refundCounter)
                    trace.calldataFloorGasCost) *
                trace.effectiveGasPrice).toB256).addBal
            benv.stat.coinbase
              (max (tx.gas - trace.messageOut.gasLeft -
                  min ((tx.gas - trace.messageOut.gasLeft) / 5)
                    refundCounter)
                  trace.calldataFloorGasCost *
                (trace.effectiveGasPrice -
                  benv.stat.baseFeePerGas)).toB256) := by
  rcases trace.exists_selectedFinalStateForm hsg with
    ⟨refundCounter, hrc, hfinal⟩
  have hrefund' : benv.stat.rules.settle.refundQuotient = 5 := by
    simpa only [BenvStat.rules] using hrefund
  have hsweep' : benv.stat.rules.settle.touchedSweep = false := by
    simpa only [BenvStat.rules] using hsweep
  refine ⟨refundCounter, hrc, ?_⟩
  simpa only [settleTransactionGas, sweepTouchedAccounts, hsg,
    hrefund', hsweep', Bool.false_eq_true, ↓reduceIte] using hfinal

/-- **A transaction keeps nonempty, non-delegating code at `a`, and so does
every frame it enters**, when no frame it enters targets `a`, `a` was not
created in the block, and either delegation is disabled or none of its
authorizations recovers to `a`. Neutral twin of
`TransactionTrace.codeAt_keep`. -/
theorem TransactionTrace.codeAt_keep_noStateGas
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (hflag : benv.stat.rules.settle.selfdestructOnlyCreated = true)
    (hrefund : benv.stat.fork.ruleSet.settle.refundQuotient = 5)
    (hsweep : benv.stat.fork.ruleSet.settle.touchedSweep = false) {a : Adr}
    (hdis : benv.stat.rules.delegationEnabled = false ∨
      ∀ auth ∈ tx.auths, ∀ authority, recoverAuthority auth = .ok authority →
        authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hne : (benv.state.getCode a).toList ≠ [])
    (hnd : ¬ isValidDelegation (benv.state.getCode a))
    (notCreated : a ∉ benv.createdAccounts) :
    (∀ root ∈ trace.rawFrames, root.devm.getCode a = benv.state.getCode a) ∧
      state.getCode a = benv.state.getCode a := by
  have hbenv := prepareMessage_benv trace.prepared
  obtain ⟨htenv, hca⟩ := prepareMessage_fields trace.prepared
  have hdebit : trace.debitState.getCode a = benv.state.getCode a := by
    have h1 := State.subBal_getCode trace.debit (a := a)
    rw [h1]
    unfold State.getCode
    rw [State.incrNonce_get_code]
  have hmsgState : trace.msg.benv.state.getCode a = benv.state.getCode a := by
    rw [hbenv]
    exact hdebit
  have hmsgSg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [hbenv]
    exact hsg
  have hmsgFlag :
      trace.msg.benv.stat.rules.settle.selfdestructOnlyCreated = true := by
    rw [hbenv]
    exact hflag
  have hdis_msg : trace.msg.benv.stat.rules.delegationEnabled = false ∨
      ∀ auth ∈ trace.msg.tenv.stat.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ a := by
    rcases hdis with hdis | hauth
    · exact Or.inl (by rw [hbenv]; exact hdis)
    · exact Or.inr (by
        rw [htenv]
        simpa only [transactionTenv, Std.TreeMap.empty_eq_emptyc, ne_eq] using
          hauth)
  obtain ⟨hpost, hroots⟩ := trace.message.codeAt_noStateGas hmsgSg hca hdis_msg
    avoid
  refine ⟨fun root member => (hroots root member).trans hmsgState, ?_⟩
  obtain ⟨refundCounter, -, hfinal⟩ :=
    trace.exists_finalStateForm_noStateGas hsg hrefund hsweep
  have hnodel : Msg.NoDel a trace.msg := by
    refine ⟨?_, ?_⟩
    · rw [hbenv]
      simpa only [Benv.beginTransaction] using notCreated
    · rw [hmsgState]
      exact hne
  have hndMsg : ¬ isValidDelegation (trace.msg.benv.state.getCode a) := by
    rw [hmsgState]
    exact hnd
  have inherited : a ∉ trace.msg.inheritedDeletions :=
    trace.not_mem_msg_inheritedDeletions a
  have hnotDel := processMessageCall_accountsToDelete_ne_noStateGas hmsgSg
    hmsgFlag trace.message.result hnodel hndMsg inherited
  rw [hfinal]
  rw [foldl_destroyAccount_getCode_ne _ hnotDel]
  rw [State.addBal_getCode, State.addBal_getCode]
  exact hpost.trans hmsgState

/-- **A transaction list keeps nonempty, non-delegating code at `a`.**
Neutral twin of `ApplyTransactionsTrace.codeAt_keep`. -/
theorem ApplyTransactionsTrace.codeAt_keep_noStateGas
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none)
    (hflag : benv.stat.rules.settle.selfdestructOnlyCreated = true)
    (hrefund : benv.stat.fork.ruleSet.settle.refundQuotient = 5)
    (hsweep : benv.stat.fork.ruleSet.settle.touchedSweep = false) {a : Adr}
    (hdis : benv.stat.rules.delegationEnabled = false ∨
      ∀ p ∈ txs, ∀ auth ∈ p.2.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hne : (benv.state.getCode a).toList ≠ [])
    (hnd : ¬ isValidDelegation (benv.state.getCode a))
    (notCreated : a ∉ benv.createdAccounts) :
    finalBenv.state.getCode a = benv.state.getCode a := by
  induction trace with
  | nil => rfl
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail ih =>
      have hdis_head : benv.stat.rules.delegationEnabled = false ∨
          ∀ auth ∈ tx.auths, ∀ authority, recoverAuthority auth = .ok authority →
            authority ≠ a := by
        rcases hdis with hdis | hdis
        · exact Or.inl hdis
        · exact Or.inr (hdis _ (List.mem_cons_self ..))
      obtain ⟨-, hstate⟩ := head.codeAt_keep_noStateGas hsg hflag hrefund hsweep
        hdis_head
        (fun root member => avoid root (by
          simp only [ApplyTransactionsTrace.rawFrames, List.mem_append]
          exact Or.inl member)) hne hnd notCreated
      have hcode : (benv.withState txState).state.getCode a = benv.state.getCode a :=
        hstate
      have hdis_tail :
          (benv.withState txState).stat.rules.delegationEnabled = false ∨
            ∀ p ∈ txs, ∀ auth ∈ p.2.auths, ∀ authority,
              recoverAuthority auth = .ok authority → authority ≠ a := by
        rcases hdis with hdis | hdis
        · exact Or.inl hdis
        · exact Or.inr (fun p hp => hdis p (List.mem_cons_of_mem _ hp))
      have := ih hsg hflag hrefund hsweep hdis_tail
        (fun root member => avoid root (by
          simp only [ApplyTransactionsTrace.rawFrames, List.mem_append]
          exact Or.inr member))
        (by rw [hcode]; exact hne) (by rw [hcode]; exact hnd) notCreated
      exact this.trans hcode

end ExecutionTrace

end Blanc
