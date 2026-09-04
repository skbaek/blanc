-- ProrataWethVaultRely.lean : the rely rung — any execution with the vault installed preserves its ledger.

import Blanc.Composition.ProrataWethVaultMessage
import Blanc.ExecutionAdmission

/-!
# The rely rung

`Blanc/Composition/ProrataWethVaultMessage.lean` proves that one message *to
the vault* preserves the share ledger, and that any chain of such messages
does.  It says nothing about a message to some **other** account, during which
the vault's frame may be entered any number of times, at any depth, by any
caller.  This module supplies that: an arbitrary successful execution — at any
target, from any program counter — with the vault program installed at `vault`
and the configuration in force preserves `LedgerConserved` at the vault.

## The route

`Blanc/ExecutionAdmission.lean`'s `lift_inv_admitted`, and not
`ContractSpec.preserves_lift`: the frame invariant `σ` here carries
`DirectWethConfiguration`, which `preserves_lift`'s `σ_of_ne` cannot rebuild
from `Pre` alone (`Blanc/ProrataWethVaultLedgerSpec.lean` records why).
`lift_inv_admitted` takes preservation obligations instead, and they are
discharged here for every instruction class at a foreign frame:

- the `PreWf` half by `Xinst.some_preserves_precond` and its companions,
  exactly as `ContractSpec.preserves_lift_admitted` discharges them;
- the configuration's `code` field by the generic code-preservation relation
  `Devm.CodePreserve`, which every instruction class carries at an address
  whose code is nonempty — and `Blanc.wethCode` is;
- the configuration's `nonprecompile` field by `sevm.benvStat`, which a
  same-frame step leaves alone and a spawned child inherits verbatim
  (`callMsg` and `createMsg` both set `benv.stat := sevm.benvStat`);
- the frame's own code, `some sevm.code.toList = Prog.compile vault` whenever
  `sevm.currentTarget = vault`, which rides in `σ` because the target-frame
  obligation receives no `Prog.At`, and which a spawned child at the vault
  inherits from the installed code (`Xinst.step_spawn_source`).

The target-frame obligation `with_depth_ind` is `vault_message_preserves_conserved`
applied to the gas-exact run that `Prog.runCompiled_of_exec` recovers from the
raw execution — the vault program is `pcFree`, checked by the kernel — with the
four resource bundles read off the trace-local admission at that frame.  The
deeper-frame hypothesis is not consumed: a vault message's only child is the
configured WETH program, whose effect the flow theorems already carry.

## What is assumed at each vault frame, and why

`VaultFrameEntry` is the resource bundle the flows' effect theorems take —
`depth ≠ 0`, `isStatic = false` and the call-gas bounds at the two staging
lines — asserted at every actually entered vault frame through
`Exec.FrameAdmitted`.  It is threaded rather than derived: a frame at depth
zero or without gas for its WETH child *reverts* (the CALL pushes `0` and the
`iszero` guard takes the `REVERT` arm), so the bundle is a consequence of
success rather than an extra premise, but that derivation is not yet made
inside the effect theorems.  Until it is, the rung is stated with the
admission premise explicit, and `Exec.FrameAdmitted` makes it trace-local:
it constrains the frames the execution actually entered, not every frame the
adversary might have entered.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune

/-- The vault program has no `PC` instruction, so a raw execution of its
compiled code is a gas-exact `Prog.RunCompiled`. -/
private theorem vault_pcFree : Prog.pcFree Blanc.ProrataWethVault.vault = true := by
  decide +kernel

/-- The resources every actually entered vault frame carries: the four flow
bundles, exactly as `vault_message_preserves_conserved` takes them. -/
def VaultFrameEntry (sevm : Sevm) (_pre : Devm) : Prop :=
  InboundCompiledResources sevm Blanc.ProrataWethVault.amountWord ∧
    InboundCompiledResources sevm Blanc.ProrataWethVault.quoteWord ∧
    OutboundCompiledResources sevm Blanc.ProrataWethVault.amountWord ∧
    OutboundCompiledResources sevm Blanc.ProrataWethVault.quoteWord

/-- The frame invariant carried across every frame of the execution. -/
structure VaultFrameInv (vault : Adr) (sevm : Sevm) (pre : Devm) : Prop where
  /-- The storage-only spec's own precondition: the vault code installed, the
  ledger conserved, and the machine memory well-formed at the vault's frame. -/
  preWf : Blanc.ProrataWethVault.vaultSpec.PreWf vault sevm pre
  /-- The asset pinned to the exact WETH runtime at a distinct, non-precompile
  account. -/
  config : DirectWethConfiguration vault sevm pre
  /-- A frame at the vault runs the vault's code. -/
  code : sevm.currentTarget = vault →
    some sevm.code.toList = Prog.compile Blanc.ProrataWethVault.vault

/-! ## Transport of the configuration -/

/-- The asset's installed code is nonempty. -/
private theorem wethCode_toList_ne_nil {vault : Adr} {sevm : Sevm} {pre : Devm}
    (config : DirectWethConfiguration vault sevm pre) :
    (pre.getCode wethAccount).toList ≠ [] := by
  rw [config.code]
  exact wethCode_nonempty

/-- The configuration survives any step that preserves nonempty code and the
frame's block statics. -/
private theorem DirectWethConfiguration.of_codePreserve
    {vault : Adr} {sevm sevm' : Sevm} {pre inter : Devm}
    (config : DirectWethConfiguration vault sevm pre)
    (stat : sevm'.benvStat = sevm.benvStat)
    (preserve : Devm.CodePreserve pre inter) :
    DirectWethConfiguration vault sevm' inter := by
  refine ⟨config.distinct, ?_, ?_⟩
  · rw [stat]
    exact config.nonprecompile
  · rw [preserve wethAccount (wethCode_toList_ne_nil config)]
    exact config.code

/-- A same-frame `Ninst` step at any outcome preserves nonempty code. -/
private theorem Ninst.stepRun_codePreserve
    {pc : Nat} {sevm : Sevm} {pre inter : Devm} {n : Ninst} {xl : Xlot}
    (child : Xlot.Rel Devm.CodePreserve xl)
    (run : Ninst.StepRun pc sevm pre n xl (.ok inter)) :
    Devm.CodePreserve pre inter :=
  Ninst.codePreserve_effectRec n child run

/-! ## The rung -/

/-- **The rely rung.**  Any successful execution — at any target, from any
program counter — that starts with the vault program installed at `vault`, the
configuration in force and the ledger conserved, and whose actually entered
vault frames carry the flow resources, ends with the ledger conserved at the
vault.  A message to some *other* account is the case `sevm.currentTarget ≠
vault`; the execution's vault frames, however deep and however re-entered, are
covered by the same induction. -/
theorem vault_rely_preserves_conserved (vault : Adr) :
    ∀ pc sevm pre post (run : Exec pc sevm pre (.ok post)),
      Prog.At Blanc.ProrataWethVault.vault vault pc sevm pre →
      Exec.FrameAdmitted vault VaultFrameEntry run →
      VaultFrameInv vault sevm pre →
      Blanc.ProrataWethVault.vaultSpec.Post vault sevm post := by
  refine lift_inv_admitted VaultFrameEntry vault Blanc.ProrataWethVault.vault
    (VaultFrameInv vault) (Blanc.ProrataWethVault.vaultSpec.Post vault)
    ?_ ?_ ?_ ?_ ?_
  -- the vault's own frame
  · intro sevm pre post run _ target admitted _ inv
    subst target
    have compiled : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post :=
      Prog.runCompiled_of_exec sevm pre _ post vault_pcFree run (inv.code rfl)
    obtain ⟨depositR, mintR, withdrawR, redeemR⟩ := admitted.root rfl
    have conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
        (Devm.getStor pre sevm.currentTarget) :=
      (ContractSpec.ofStorageOnly_preInv_iff).mp inv.preWf.pre.inv
    refine ⟨trivial, ?_⟩
    exact (ContractSpec.ofStorageOnly_postInv_iff).mpr
      (vault_message_preserves_conserved inv.config (inv.preWf.wf rfl)
        depositR mintR withdrawR redeemR compiled conserved)
  -- a childless step at a foreign frame
  · intro pc sevm pre n inter h_at h_run h_ne inv
    refine ⟨⟨?_, fun h => absurd h h_ne⟩,
      inv.config.of_codePreserve rfl
        (Ninst.stepRun_codePreserve (xl := .none) trivial h_run),
      inv.code⟩
    have hσ' := inv.preWf.pre
    cases n with
    | push xs le =>
      simp only [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at h_run
      rcases Except.bind_eq_ok h_run.2.symm with ⟨devm1, h_charge, h_push⟩
      exact hσ'.state_eq
        (((Devm.burn_of_chargeGas h_charge).state).trans
          ((Devm.push_of_push h_push).state)).symm
    | reg r =>
      have h_reg : Rinst.run ⟨pc, sevm, pre⟩ r = .ok inter := by
        simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at h_run
        exact h_run.2.symm
      by_cases h_ss : r = Rinst.sstore
      · subst h_ss
        have h_frame := Rinst.sstore_run_stateWriteFrame pc pre sevm
        rw [h_reg] at h_frame
        refine ContractSpec.Pre.of_eqs hσ' (h_frame.getCode_eq vault).symm ?_
          (sstore_preserves_getStor_ne h_reg h_ne)
        funext b
        exact (h_frame.getBal_eq b).symm
      · exact ContractSpec.Pre.of_eqs hσ' (Rinst.preserves_getCode h_reg vault)
          (Rinst.preserves_bal h_reg).symm
          (congr_fun (Rinst.preserves_stor h_ss h_reg) vault).symm
    | exec x =>
      refine ContractSpec.Xinst.none_preserves_precond (x := x) ?_ h_ne hσ'
      simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.Run]
        using h_run
  -- a spawning step at a foreign frame
  · intro pc sevm pre n evm' out' inter h_at h_run child h_ne inv
    cases n with
    | push xs le =>
      simp only [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at h_run
      cases h_run.1
    | reg r =>
      simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at h_run
      cases h_run.1
    | exec x =>
      have hx : Xinst.Run sevm pre x (.some ⟨evm', out'⟩) (.ok inter) := by
        simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.Run]
          using h_run
      obtain ⟨h_child, h_back⟩ :=
        ContractSpec.Xinst.some_preserves_precond (x := x) hx child h_ne inv.preWf.pre
      obtain ⟨f, rsm, hstep, henter, -⟩ := XStep.Run.some_inv hx
      -- the child inherits the world's code and the block statics
      have childCode : Devm.CodePreserve pre evm'.dyna := by
        intro a _
        rw [Frame.enter_run_getCode henter a]
        exact Xinst.step_spawn_getCode hstep a
      have childStat : evm'.sta.benvStat = sevm.benvStat := by
        rw [Frame.enter_run_benvStat henter]
        exact _root_.Blanc.Xinst.step_spawn_benvStat hstep
      -- a child at the vault runs the vault's installed code
      have childOwnCode : evm'.sta.currentTarget = vault →
          some evm'.sta.code.toList = Prog.compile Blanc.ProrataWethVault.vault := by
        intro childTarget
        have targetEq := Frame.enter_run_currentTarget henter
        rw [Frame.enter_run_code henter]
        rw [childTarget] at targetEq
        rcases Xinst.step_spawn_source hstep with hempty | hsame | hsrc
        · rw [← targetEq] at hempty
          exact absurd hempty (not_empty_of_compile inv.preWf.pre.code)
        · rw [← targetEq] at hsame
          exact absurd hsame.symm h_ne
        · rw [← targetEq] at hsrc
          rw [hsrc (not_delegation_of_compile inv.preWf.pre.code)]
          exact inv.preWf.pre.code
      refine ⟨⟨⟨h_child, fun _ => Xinst.some_child_wf hx⟩,
        inv.config.of_codePreserve childStat childCode, childOwnCode⟩, ?_⟩
      intro h_if
      have wholeStep : Devm.CodePreserve pre inter :=
        Ninst.stepRun_codePreserve (xl := .some ⟨evm', out'⟩)
          (Exec.effect codePreserve_refl_trans.1 codePreserve_refl_trans.2
            Ninst.codePreserve_effectRec Jinst.codePreserve_effect
            Linst.codePreserve_effect child) h_run
      exact ⟨⟨h_back h_if, fun h => absurd h h_ne⟩,
        inv.config.of_codePreserve rfl wholeStep, inv.code⟩
  -- a jump at a foreign frame
  · intro pc sevm pre j pc' inter h_at h_run h_ne inv
    have state := Jinst.preserves_state h_run
    refine ⟨⟨inv.preWf.pre.state_eq state, fun h => absurd h h_ne⟩,
      inv.config.of_codePreserve rfl ?_, inv.code⟩
    intro a _
    exact getCode_eq_of_state_eq state a
  -- a terminal instruction at a foreign frame
  · intro pc sevm pre l post h_at h_run h_ne inv
    exact ContractSpec.Linst.inv_postcond h_run h_ne inv.preWf.pre

/-- The rung at a message boundary, in the form `Blanc/Ladder.lean`'s
`ContractSpec.Preserves` states it: the execution starts at pc `0` in a frame
whose code is the vault's whenever the frame is the vault's, the vault's own
frame has well-formed memory, and the storage-only precondition and the
configuration hold. -/
theorem vault_rely_preserves {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post))
    (admitted : Exec.FrameAdmitted vault VaultFrameEntry run)
    (code : sevm.currentTarget = vault →
      some sevm.code.toList = Prog.compile Blanc.ProrataWethVault.vault)
    (memoryWf : sevm.currentTarget = vault → Mem.Wf pre.memory)
    (pre_ : Blanc.ProrataWethVault.vaultSpec.Pre vault sevm pre)
    (config : DirectWethConfiguration vault sevm pre) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot (Devm.getStor post vault) :=
  (ContractSpec.ofStorageOnly_postInv_iff).mp
    (vault_rely_preserves_conserved vault 0 sevm pre post run
      ⟨pre_.code, fun target => ⟨code target, rfl⟩⟩ admitted
      ⟨⟨pre_, memoryWf⟩, config, code⟩).inv

end Blanc.Composition.ProrataWethVault
