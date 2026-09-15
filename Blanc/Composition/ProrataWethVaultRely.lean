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
raw execution — the vault program is `pcFree`, checked by the kernel.  The flow
theorems now derive CALL depth and gas from each successful crossing and derive
dynamic mode from the actual parent `SSTORE`, so this rung needs no separate
frame-entry resource premise.  The deeper-frame hypothesis is not consumed: a
vault message's only child is the configured WETH program, whose effect the
flow theorems already carry.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune

/-- The vault program has no `PC` instruction, so a raw execution of its
compiled code is a gas-exact `Prog.RunCompiled`. -/
private theorem vault_pcFree : Prog.pcFree Blanc.ProrataWethVault.vault = true := by
  decide +kernel

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
configuration in force and the ledger conserved ends with the ledger conserved
at the vault.  A message to some *other* account is the case `sevm.currentTarget ≠
vault`; the execution's vault frames, however deep and however re-entered, are
covered by the same induction. -/
theorem vault_rely_preserves_conserved (vault : Adr) :
    ∀ pc sevm pre post (_run : Exec pc sevm pre (.ok post)),
      Prog.At Blanc.ProrataWethVault.vault vault pc sevm pre →
      VaultFrameInv vault sevm pre →
      Blanc.ProrataWethVault.vaultSpec.Post vault sevm post := by
  intro pc sevm pre post run programAt inv
  have admitted : Exec.FrameAdmitted vault (fun _ _ => True) run := by
    intro _ _ _
    trivial
  refine lift_inv_admitted (fun _ _ => True) vault Blanc.ProrataWethVault.vault
    (VaultFrameInv vault) (Blanc.ProrataWethVault.vaultSpec.Post vault)
    ?_ ?_ ?_ ?_ ?_ pc sevm pre post run programAt admitted inv
  -- the vault's own frame
  · intro sevm pre post run _ target admitted _ inv
    subst target
    have compiled : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post :=
      Prog.runCompiled_of_exec sevm pre _ post vault_pcFree run (inv.code rfl)
    have conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
        (Devm.getStor pre sevm.currentTarget) :=
      (ContractSpec.ofStorageOnly_preInv_iff).mp inv.preWf.pre.inv
    refine ⟨trivial, ?_⟩
    exact (ContractSpec.ofStorageOnly_postInv_iff).mpr
      (vault_message_preserves_conserved inv.config (inv.preWf.wf rfl)
        compiled conserved)
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
    (code : sevm.currentTarget = vault →
      some sevm.code.toList = Prog.compile Blanc.ProrataWethVault.vault)
    (memoryWf : sevm.currentTarget = vault → Mem.Wf pre.memory)
    (pre_ : Blanc.ProrataWethVault.vaultSpec.Pre vault sevm pre)
    (config : DirectWethConfiguration vault sevm pre) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot (Devm.getStor post vault) :=
  (ContractSpec.ofStorageOnly_postInv_iff).mp
    (vault_rely_preserves_conserved vault 0 sevm pre post run
      ⟨pre_.code, fun target => ⟨code target, rfl⟩⟩
      ⟨⟨pre_, memoryWf⟩, config, code⟩).inv

/-! ## Allowance-debit authorization

The 09-08 transferFrom seam classifies each retained invocation's allowance
effect from its successful compiled run. This section closes the two G6
allowance-debit items over the retained history: the unconditional
authorization classification (every allowance write or omission is exactly one
runtime branch, and every touched pair's raw key is non-address-shaped), and
the `NoVaultAllowanceKeyCollision`-premised exclusion of foreign debits of the
vault's allowance cells (modulo the explicit quiescence hypothesis the rooted
chronology unit will discharge).
-/

/-- Every retained allowance pair visits a non-address-shaped raw key. The
executed hash guard of the originating successful invocation derives the shape
of its own pair's key; a self-bypass visits no pair. Unconditional: no
collision premise and no chronology. This is what lets the omission frames
apply at vault-owned keys in the exclusion below. -/
theorem touchedWethAllowancePairs_keys_nonaddress
    {history : List WethAllowanceInvocation} {p : B256 × B256}
    (touched : p ∈ touchedWethAllowancePairs history) :
    ¬ ValidAdr (wethAllowanceKey p.1 p.2) := by
  obtain ⟨call, _, pairEq⟩ := List.mem_filterMap.mp touched
  cases approval : call.approval with
  | true =>
    have selected := call.selected
    simp only [approval, ↓reduceIte] at selected
    simp only [WethAllowanceInvocation.pair?, approval, ↓reduceIte] at pairEq
    cases pairEq
    exact (weth_approve_compiled_raw_effect call.memoryWf call.run selected).1
  | false =>
    have selected := call.selected
    simp only [approval, Bool.false_eq_true, ↓reduceIte] at selected
    have effect := weth_transferFrom_compiled_allowance_effect
      call.memoryWf call.run selected
    dsimp only at effect
    by_cases same : Sevm.argWord call.sevm 0 = call.sevm.caller.toB256
    · simp [WethAllowanceInvocation.pair?, approval, same] at pairEq
    · simp only [if_neg same] at effect
      obtain ⟨valid, _⟩ := effect
      simp [WethAllowanceInvocation.pair?, approval, same] at pairEq
      cases pairEq
      exact valid

/-- **Unconditional debit-authorization classification.** Every retained
invocation's allowance effect is exactly one runtime-authorized branch: a
caller-owned exact approve write, a self-bypass omission, a maximum read-only
omission, or a covered finite decrement with its executed SSTORE witness. No
collision premise: this is raw-key/runtime-authorization altitude, proved from
the invocation's successful compiled run. -/
theorem allowance_debit_classification (call : WethAllowanceInvocation) :
    (call.approval = true ∧
      ¬ ValidAdr (wethAllowanceKey call.sevm.caller.toB256 (Sevm.argWord call.sevm 0)) ∧
      Devm.getStor call.post wethAccount =
        (Devm.getStor call.pre wethAccount).set
          (wethAllowanceKey call.sevm.caller.toB256 (Sevm.argWord call.sevm 0))
          (Sevm.argWord call.sevm 1)) ∨
    (call.approval = false ∧ Sevm.argWord call.sevm 0 = call.sevm.caller.toB256 ∧
      call.writtenPair? = none ∧
      Stor.AgreeOffAdr (Devm.getStor call.pre wethAccount)
        (Devm.getStor call.post wethAccount)) ∨
    (call.approval = false ∧ Sevm.argWord call.sevm 0 ≠ call.sevm.caller.toB256 ∧
      call.pre.getStorVal wethAccount
        (wethAllowanceKey (Sevm.argWord call.sevm 0) call.sevm.caller.toB256) =
        B256.max ∧
      call.writtenPair? = none ∧
      Stor.AgreeOffAdr (Devm.getStor call.pre wethAccount)
        (Devm.getStor call.post wethAccount)) ∨
    (call.approval = false ∧ Sevm.argWord call.sevm 0 ≠ call.sevm.caller.toB256 ∧
      call.pre.getStorVal wethAccount
        (wethAllowanceKey (Sevm.argWord call.sevm 0) call.sevm.caller.toB256) ≠
        B256.max ∧
      Sevm.argWord call.sevm 2 ≤ call.pre.getStorVal wethAccount
        (wethAllowanceKey (Sevm.argWord call.sevm 0) call.sevm.caller.toB256) ∧
      call.writtenPair? =
        some (Sevm.argWord call.sevm 0, call.sevm.caller.toB256) ∧
      ¬ ValidAdr
        (wethAllowanceKey (Sevm.argWord call.sevm 0) call.sevm.caller.toB256) ∧
      Stor.AgreeOffAdr
        ((Devm.getStor call.pre wethAccount).set
          (wethAllowanceKey (Sevm.argWord call.sevm 0) call.sevm.caller.toB256)
          (call.pre.getStorVal wethAccount
            (wethAllowanceKey (Sevm.argWord call.sevm 0)
              call.sevm.caller.toB256) - Sevm.argWord call.sevm 2))
        (Devm.getStor call.post wethAccount) ∧
      ∃ writePre writePost,
        Ninst.Run call.sevm writePre Ninst.sstore writePost ∧
        [wethAllowanceKey (Sevm.argWord call.sevm 0) call.sevm.caller.toB256,
          call.pre.getStorVal wethAccount
            (wethAllowanceKey (Sevm.argWord call.sevm 0)
              call.sevm.caller.toB256) - Sevm.argWord call.sevm 2] <<+
          writePre.stack ∧
        Stor.AgreeOffAdr (Devm.getStor call.pre wethAccount)
          (Devm.getStor writePre wethAccount) ∧
        Devm.getStor call.post = Devm.getStor writePost) := by
  cases approval : call.approval with
  | true =>
    have selected := call.selected
    simp only [approval, ↓reduceIte] at selected
    obtain ⟨valid, effect⟩ :=
      weth_approve_compiled_raw_effect call.memoryWf call.run selected
    rw [call.target] at effect
    exact Or.inl ⟨rfl, valid, effect⟩
  | false =>
    have selected := call.selected
    simp only [approval, Bool.false_eq_true, ↓reduceIte] at selected
    have effect := weth_transferFrom_compiled_allowance_effect
      call.memoryWf call.run selected
    dsimp only at effect
    rw [call.target] at effect
    by_cases same : Sevm.argWord call.sevm 0 = call.sevm.caller.toB256
    · simp only [if_pos same] at effect
      refine Or.inr (Or.inl ⟨rfl, same, ?_, effect⟩)
      simp [WethAllowanceInvocation.writtenPair?,
        WethAllowanceInvocation.pair?, approval, same]
    · simp only [if_neg same] at effect
      obtain ⟨valid, result⟩ := effect
      rcases result with ⟨maximum, silent⟩ | ⟨finite, covered, stored, witness⟩
      · refine Or.inr (Or.inr (Or.inl ⟨rfl, same, maximum, ?_, silent⟩))
        simp [WethAllowanceInvocation.writtenPair?,
          WethAllowanceInvocation.pair?, approval, same, Option.filter, maximum]
      · refine Or.inr (Or.inr
          (Or.inr ⟨rfl, same, finite, covered, ?_, valid, stored, witness⟩))
        simp [WethAllowanceInvocation.writtenPair?,
          WethAllowanceInvocation.pair?, approval, same, Option.filter, finite]

/-- An approval invocation debits no balance row: its exact raw write lands at
a non-address-shaped key, which the balance view cannot see. Unconditional. -/
theorem approve_invocation_preserves_balance_rows
    (call : WethAllowanceInvocation) (approval : call.approval = true) :
    Stor.rest (Devm.getStor call.post wethAccount) =
      Stor.rest (Devm.getStor call.pre wethAccount) := by
  have selected := call.selected
  simp only [approval, ↓reduceIte] at selected
  obtain ⟨valid, effect⟩ :=
    weth_approve_compiled_raw_effect call.memoryWf call.run selected
  rw [call.target] at effect
  rw [effect]
  exact rest_set_of_not_validAdr valid

/-- **Foreign-debit exclusion.** Under D9's finite collision premise, a foreign
invocation preserves every vault-owned touched allowance cell — given the
explicit quiescence hypothesis that the cell reads zero at the invocation's
pre-state. Foreign approvals and foreign spends of other pairs cannot alias
the vault key; a finite spend of the vault's own pair is then ruled out by
coverage against the zero cell; self and maximum branches are read-only. The
quiescence hypothesis is the precise premise the rooted chronology unit roots
from the empty root, vault-never-approves, and settled rollback. -/
theorem foreign_debit_excluded
    {history : List WethAllowanceInvocation} {vault : Adr}
    (collision : NoVaultAllowanceKeyCollision history vault)
    (call : WethAllowanceInvocation) (member : call ∈ history)
    (foreign : call.sevm.caller ≠ vault)
    (p : B256 × B256) (touched : p ∈ touchedWethAllowancePairs history)
    (owner : p.1 = vault.toB256)
    (quiet : call.pre.getStorVal wethAccount (wethAllowanceKey p.1 p.2) = 0) :
    Devm.getStorVal call.post wethAccount (wethAllowanceKey p.1 p.2) =
      Devm.getStorVal call.pre wethAccount (wethAllowanceKey p.1 p.2) := by
  have keyShape : ¬ ValidAdr (wethAllowanceKey p.1 p.2) :=
    touchedWethAllowancePairs_keys_nonaddress touched
  cases approval : call.approval with
  | true =>
    exact foreign_approve_preserves_vault_allowance collision call member
      approval foreign p touched owner
  | false =>
    have selected := call.selected
    simp only [approval, Bool.false_eq_true, ↓reduceIte] at selected
    have effect := weth_transferFrom_compiled_allowance_effect
      call.memoryWf call.run selected
    dsimp only at effect
    rw [call.target] at effect
    by_cases same : Sevm.argWord call.sevm 0 = call.sevm.caller.toB256
    · simp only [if_pos same] at effect
      exact (effect _ keyShape).symm
    · simp only [if_neg same] at effect
      obtain ⟨valid, result⟩ := effect
      rcases result with ⟨maximum, silent⟩ | ⟨finite, covered, stored, witness⟩
      · exact (silent _ keyShape).symm
      · by_cases pairEq : (Sevm.argWord call.sevm 0, call.sevm.caller.toB256) = p
        · subst pairEq
          have keyEq : wethAllowanceKey
                (Sevm.argWord call.sevm 0, call.sevm.caller.toB256).1
                (Sevm.argWord call.sevm 0, call.sevm.caller.toB256).2 =
              wethAllowanceKey (Sevm.argWord call.sevm 0)
                call.sevm.caller.toB256 := rfl
          rw [keyEq] at quiet keyShape ⊢
          have frame := stored _ keyShape
          rw [Stor.get_set_self] at frame
          rw [quiet] at covered
          have wad0 : Sevm.argWord call.sevm 2 = 0 := by
            have h := B256.toNat_le_toNat covered
            rw [B256.toNat_zero] at h
            have h0 := Nat.le_zero.mp h
            exact B256.toNat_inj _ _ (by rwa [B256.toNat_zero])
          rw [quiet, wad0] at frame
          have zeroSub : (0 : B256) - 0 = 0 := by decide +kernel
          rw [zeroSub] at frame
          have post0 : call.post.getStorVal wethAccount
              (wethAllowanceKey (Sevm.argWord call.sevm 0)
                call.sevm.caller.toB256) = 0 := frame.symm
          rw [post0, quiet]
        · have writer : (Sevm.argWord call.sevm 0, call.sevm.caller.toB256) ∈
              writtenWethAllowancePairs history := by
            apply List.mem_filterMap.mpr
            refine ⟨call, member, ?_⟩
            simp [WethAllowanceInvocation.writtenPair?,
              WethAllowanceInvocation.pair?, approval, same, Option.filter,
              finite]
          have keys := collision p touched owner _ writer (Ne.symm pairEq)
          have frame := stored _ keyShape
          rw [Stor.get_set_ne _ (Ne.symm keys)] at frame
          exact frame.symm

/-! ## Rooted allowance chronology

The retained-history adapter the invocation projection was built for: the
list of `WethAllowanceInvocation` is chronological only once it is chained
from a root with settled-state continuity. `RootedAllowanceHistory` is that
chain, threaded at WETH-storage granularity — the exact altitude the quiet
argument reads. Each `invoked` step links one listed invocation's pre/post
WETH storage to the chain; each `silent` step preserves every vault-owned
touched cell. Linkage, provenance, and preservation are carrier fields that
the configured-history inhabitation discharges; they are never assumed world
facts. In particular this adapter takes no `DirectWethConfiguration`: every
invocation already carries its target and its genuine successful WETH run.
-/

/-- The configured root plus WETH-side emptiness: both runtimes installed and
both storages empty. `ConfiguredRoot` states the vault half; this adds the
WETH half the allowance replay roots at. -/
structure AllowanceRoot (vault : Adr) (sevm : Sevm) (pre : Devm) : Prop where
  /-- The configured two-runtime root: asset pinned, vault installed, vault
  storage empty. -/
  configured : ConfiguredRoot vault sevm pre
  /-- The WETH account's storage is empty at the root. -/
  wethEmpty : Devm.getStor pre wethAccount = Stor.empty

/-- Root quiescence: every vault-owned touched cell reads zero at the root.
Holds for every cell, so the touched/owner witnesses are unused. -/
theorem AllowanceRoot.quiet {vault : Adr} {sevm : Sevm} {pre : Devm}
    {history : List WethAllowanceInvocation}
    (root : AllowanceRoot vault sevm pre)
    (p : B256 × B256) (_touched : p ∈ touchedWethAllowancePairs history)
    (_owner : p.1 = vault.toB256) :
    pre.getStorVal wethAccount (wethAllowanceKey p.1 p.2) = 0 := by
  show (Devm.getStor pre wethAccount).get (wethAllowanceKey p.1 p.2) = 0
  rw [root.wethEmpty]
  rfl

/-- Vault-staged calldata: the invocation's calldata is exactly one of the
three WETH call shapes the vault stages. Occurrence and parent threading are
inhabitation obligations; the bridge below needs only the data shape. -/
def VaultStagedCalldata (call : WethAllowanceInvocation) : Prop :=
  (∃ v, call.sevm.data = balanceOfCalldata v) ∨
    (∃ owner dst assets, call.sevm.data = transferFromCalldata owner dst assets) ∨
    (∃ receiver assets, call.sevm.data = transferCalldata receiver assets)

/-- A vault-staged child is never an approval: its staged selector is one of
the three allowlisted forms, and `approve` is not among them. -/
theorem VaultStagedCalldata.not_approve {call : WethAllowanceInvocation}
    (staged : VaultStagedCalldata call) : call.approval = false := by
  have selNe : Sevm.selector call.sevm ≠
      selector "approve" [.address, .uint256] := by
    rcases staged with ⟨v, hdata⟩ | ⟨owner, dst, assets, hdata⟩ | ⟨receiver, assets, hdata⟩
    · have sel := (balanceOfCalldata_facts hdata).1
      have mem : selector "balanceOf" [.address] ∈ allowedWethSelectors := by
        simp [allowedWethSelectors]
      rw [sel]
      intro hEq
      rw [hEq] at mem
      exact approveSelector_not_allowed mem
    · have sel := (transferFromCalldata_facts hdata).1
      have mem : selector "transferFrom" [.address, .address, .uint256] ∈
          allowedWethSelectors := by
        simp [allowedWethSelectors]
      rw [sel]
      intro hEq
      rw [hEq] at mem
      exact approveSelector_not_allowed mem
    · have sel := (transferCalldata_facts hdata).1
      have mem : selector "transfer" [.address, .uint256] ∈ allowedWethSelectors := by
        simp [allowedWethSelectors]
      rw [sel]
      intro hEq
      rw [hEq] at mem
      exact approveSelector_not_allowed mem
  cases approval : call.approval with
  | true =>
    have selected := call.selected
    simp only [approval, ↓reduceIte] at selected
    exact absurd selected selNe
  | false => rfl

/-- A rooted allowance history over the full invocation list, processing `done`
from WETH storage `s` to WETH storage `t`. The root starts from empty WETH
storage; `invoked` links one listed call; `silent` covers every other settled
step by its cell preservation. -/
inductive RootedAllowanceHistory (vault : Adr)
    (full : List WethAllowanceInvocation) :
    List WethAllowanceInvocation → Stor → Stor → Prop
  | root {sevm : Sevm} {pre : Devm} (r : AllowanceRoot vault sevm pre) :
      RootedAllowanceHistory vault full [] Stor.empty Stor.empty
  | invoked (done : List WethAllowanceInvocation) (s t u : Stor)
      (call : WethAllowanceInvocation) :
      RootedAllowanceHistory vault full done s t →
      call ∈ full →
      call.pre.state.getStor wethAccount = t →
      u = call.post.state.getStor wethAccount →
      (call.sevm.caller = vault → VaultStagedCalldata call) →
      RootedAllowanceHistory vault full (done ++ [call]) s u
  | silent (done : List WethAllowanceInvocation) (s t u : Stor) :
      RootedAllowanceHistory vault full done s t →
      (∀ p ∈ touchedWethAllowancePairs full, p.1 = vault.toB256 →
        u.get (wethAllowanceKey p.1 p.2) = t.get (wethAllowanceKey p.1 p.2)) →
      RootedAllowanceHistory vault full done s u

/-- Rooted quiet: over a rooted history, every vault-owned touched cell reads
zero at the current chain state, and every processed call was quiet at its
pre. The induction invariant is over the full list's pairs, so silent steps
and invocation order are both harmless. -/
theorem RootedAllowanceHistory.all_quiet
    {vault : Adr} {full done : List WethAllowanceInvocation} {s t : Stor}
    (collision : NoVaultAllowanceKeyCollision full vault)
    (chain : RootedAllowanceHistory vault full done s t) :
    (∀ p ∈ touchedWethAllowancePairs full, p.1 = vault.toB256 →
      t.get (wethAllowanceKey p.1 p.2) = 0) ∧
    (∀ call ∈ done, ∀ p ∈ touchedWethAllowancePairs full, p.1 = vault.toB256 →
      call.pre.getStorVal wethAccount (wethAllowanceKey p.1 p.2) = 0) := by
  induction chain with
  | root r =>
    refine ⟨?_, ?_⟩
    · intro p touched owner
      have h := r.quiet (history := full) p touched owner
      rw [← r.wethEmpty]
      exact h
    · intro call hmem
      simp at hmem
  | invoked _done _s mid fin call _prev member entry exit staged ih =>
    obtain ⟨zeroT, quietDone⟩ := ih
    have quietPre : ∀ p ∈ touchedWethAllowancePairs full, p.1 = vault.toB256 →
        call.pre.getStorVal wethAccount (wethAllowanceKey p.1 p.2) = 0 := by
      intro p touched owner
      have h0 := zeroT p touched owner
      have link : call.pre.getStorVal wethAccount (wethAllowanceKey p.1 p.2) =
          mid.get (wethAllowanceKey p.1 p.2) := by
        show (call.pre.state.getStor wethAccount).get (wethAllowanceKey p.1 p.2) =
          mid.get (wethAllowanceKey p.1 p.2)
        rw [entry]
      rw [link, h0]
    refine ⟨?_, ?_⟩
    · intro p touched owner
      have keyShape : ¬ ValidAdr (wethAllowanceKey p.1 p.2) :=
        touchedWethAllowancePairs_keys_nonaddress touched
      have finish : call.post.getStorVal wethAccount (wethAllowanceKey p.1 p.2) = 0 →
          fin.get (wethAllowanceKey p.1 p.2) = 0 := by
        intro post0
        subst exit
        exact post0
      by_cases vaultCaller : call.sevm.caller = vault
      · have approvalFalse := (staged vaultCaller).not_approve
        have classif := allowance_debit_classification call
        rcases classif with ⟨hAppr, _, _⟩ | ⟨_, _, _, frameSelf⟩
          | ⟨_, _, _, _, frameMax⟩
          | ⟨_, _, _, covered, writtenEq, _, stored, _⟩
        · rw [approvalFalse] at hAppr
          simp at hAppr
        · apply finish
          have quiet := quietPre p touched owner
          have preEq : (Devm.getStor call.pre wethAccount).get
              (wethAllowanceKey p.1 p.2) = 0 := quiet
          have postEq : (Devm.getStor call.post wethAccount).get
              (wethAllowanceKey p.1 p.2) = 0 :=
            (frameSelf _ keyShape).symm.trans preEq
          exact postEq
        · apply finish
          have quiet := quietPre p touched owner
          have preEq : (Devm.getStor call.pre wethAccount).get
              (wethAllowanceKey p.1 p.2) = 0 := quiet
          have postEq : (Devm.getStor call.post wethAccount).get
              (wethAllowanceKey p.1 p.2) = 0 :=
            (frameMax _ keyShape).symm.trans preEq
          exact postEq
        · apply finish
          by_cases pairEq :
            (Sevm.argWord call.sevm 0, call.sevm.caller.toB256) = p
          · have keyEq : wethAllowanceKey p.1 p.2 =
                wethAllowanceKey (Sevm.argWord call.sevm 0)
                  call.sevm.caller.toB256 := by
              rw [← pairEq]
            have quiet := quietPre p touched owner
            have quietArg : call.pre.getStorVal wethAccount
                (wethAllowanceKey (Sevm.argWord call.sevm 0)
                  call.sevm.caller.toB256) = 0 := by
              rwa [keyEq] at quiet
            have coveredArg := covered
            rw [quietArg] at coveredArg
            have wad0 : Sevm.argWord call.sevm 2 = 0 := by
              have h := B256.toNat_le_toNat coveredArg
              rw [B256.toNat_zero] at h
              have h0 := Nat.le_zero.mp h
              exact B256.toNat_inj _ _ (by rwa [B256.toNat_zero])
            have frame := stored _ keyShape
            rw [keyEq, Stor.get_set_self, quietArg, wad0] at frame
            have zeroSub : (0 : B256) - 0 = 0 := by decide +kernel
            rw [zeroSub] at frame
            have postEq : call.post.getStorVal wethAccount
                (wethAllowanceKey p.1 p.2) = 0 := by
              have postEqStor : (Devm.getStor call.post wethAccount).get
                  (wethAllowanceKey (Sevm.argWord call.sevm 0)
                    call.sevm.caller.toB256) = 0 := frame.symm
              rw [keyEq]
              exact postEqStor
            exact postEq
          · have writer : (Sevm.argWord call.sevm 0, call.sevm.caller.toB256) ∈
                writtenWethAllowancePairs full :=
              List.mem_filterMap.mpr ⟨call, member, writtenEq⟩
            have keys := collision p touched owner _ writer (Ne.symm pairEq)
            have frame := stored _ keyShape
            rw [Stor.get_set_ne _ (Ne.symm keys)] at frame
            have quiet := quietPre p touched owner
            have preEq : (Devm.getStor call.pre wethAccount).get
                (wethAllowanceKey p.1 p.2) = 0 := quiet
            have postEq : (Devm.getStor call.post wethAccount).get
                (wethAllowanceKey p.1 p.2) = 0 :=
              frame.symm.trans preEq
            exact postEq
      · apply finish
        have quiet := quietPre p touched owner
        have pres := foreign_debit_excluded collision call member vaultCaller p
          touched owner quiet
        rw [pres, quiet]
    · intro call' hmem p touched owner
      rw [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hDone | rfl
      · exact quietDone call' hDone p touched owner
      · exact quietPre p touched owner
  | silent _done _s _t _u _prev preserve ih =>
    obtain ⟨zeroT, quietDone⟩ := ih
    refine ⟨?_, quietDone⟩
    intro p touched owner
    exact (preserve p touched owner).trans (zeroT p touched owner)

/-- Rooted foreign-debit exclusion: V1's exclusion with `quiet` discharged
from the rooted history. The only premises are the chain and the finite
trace-local collision hypothesis. -/
theorem foreign_debit_excluded_rooted
    {history : List WethAllowanceInvocation} {vault : Adr} {s0 sn : Stor}
    (chain : RootedAllowanceHistory vault history history s0 sn)
    (collision : NoVaultAllowanceKeyCollision history vault)
    (call : WethAllowanceInvocation) (member : call ∈ history)
    (foreign : call.sevm.caller ≠ vault)
    (p : B256 × B256) (touched : p ∈ touchedWethAllowancePairs history)
    (owner : p.1 = vault.toB256) :
    call.post.getStorVal wethAccount (wethAllowanceKey p.1 p.2) =
      call.pre.getStorVal wethAccount (wethAllowanceKey p.1 p.2) := by
  have quiet := (chain.all_quiet collision).2 call member p touched owner
  exact foreign_debit_excluded collision call member foreign p touched owner quiet

/-! ## Settled rollback in chain currency

Each rollback substrate fact restated as WETH-storage preservation, the form
in which `silent` chain steps consume it. -/

/-- A failed WETH child settles its parent's WETH storage to the call-time
value: the occurrence-level rollback in chain currency. -/
theorem weth_child_failure_preserves_weth_storage
    {sevm : Sevm} {pre post : Devm} {instruction : Ninst} {calldata : Bytes}
    {static : Bool}
    (occurrence : ExactWethChildOccurrence sevm pre post instruction calldata
      static)
    (failureFlag : ∃ tail, post.stack = (0 : B256) :: tail) :
    (Devm.getStor post wethAccount) = (Devm.getStor pre wethAccount) := by
  have h := occurrence.rollback_of_post failureFlag
  show (post.state.getStor wethAccount) = (pre.state.getStor wethAccount)
  rw [h]

/-- A failed top-level message restores its entry world's WETH storage. -/
theorem failed_message_preserves_weth_storage
    {msg : Msg} {xl : Xlot} {out : Devm}
    (run : ProcessMessage msg xl (.ok out)) (failed : out.error.isSome) :
    (Devm.getStor out wethAccount) = (msg.benv.state.getStor wethAccount) := by
  have h := (ProcessMessage.rollback_of_error run failed).1
  show (out.state.getStor wethAccount) = (msg.benv.state.getStor wethAccount)
  rw [h]

/-- A message with no successful interpreted execution settles to its entry
world's WETH storage: the Ladder generic in chain currency. -/
theorem no_success_message_preserves_weth_storage
    {msg : Msg} {benv : Benv} {xl : Xlot} {out : Devm}
    (h_pm : ProcessMessage msg xl (.ok out))
    (h_fill : Xlot.Filled xl)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles && decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_none : ∀ post, Exec 0 (initSevm (msg.withBenv benv))
        (initDevm (msg.withBenv benv)) (.ok post) → False) :
    (Devm.getStor out wethAccount) = (msg.benv.state.getStor wethAccount) := by
  have h := (Blanc.rollback_of_no_success h_pm h_fill h_bt h_prec h_none).2.1
  show (out.state.getStor wethAccount) = (msg.benv.state.getStor wethAccount)
  rw [h]


/-! ## WETH environment rungs

Per-message WETH-environment facts for history projection: invocation
packaging from projected runs, static-call silence, foreign-approve
silence, and the named per-selector silence gap interface.  Committing
non-static vault-cell preservation goes through the source exec-free
route, which needs `Blanc.ReachableExecFree` — outside the current
import closure, so it is the precise next unit once the master decides
the Rely import delta. -/

/-- The inherited WETH program has no `PC` instruction, so a raw
execution of its compiled code is a gas-exact `Prog.RunCompiled`. -/
theorem weth_pcFree : Prog.pcFree Blanc.weth = true := by
  decide +kernel

/-- **WETH run packages an approve invocation.**  From a projected WETH
run with the approve selector equation. -/
theorem weth_run_mkApproveInvocation
    {childSevm : Sevm} {childPre rawPost : Devm}
    (target : childSevm.currentTarget = wethAccount)
    (memEmpty : childPre.memory = Mem.empty)
    (run : Prog.RunCompiled childSevm childPre Blanc.weth rawPost)
    (selected : Sevm.selector childSevm =
      selector "approve" [.address, .uint256]) :
    ∃ call : WethAllowanceInvocation,
      call.approval = true ∧ call.sevm = childSevm ∧
        call.pre = childPre ∧ call.post = rawPost := by
  refine ⟨⟨childSevm, childPre, rawPost, true, target, ?_, run, ?_⟩,
    rfl, rfl, rfl, rfl⟩
  · rw [memEmpty]
    exact Mem.wf_empty
  · simpa using selected

/-- **WETH run packages a transferFrom invocation.**  From a projected
WETH run with the transferFrom selector equation. -/
theorem weth_run_mkTransferFromInvocation
    {childSevm : Sevm} {childPre rawPost : Devm}
    (target : childSevm.currentTarget = wethAccount)
    (memEmpty : childPre.memory = Mem.empty)
    (run : Prog.RunCompiled childSevm childPre Blanc.weth rawPost)
    (selected : Sevm.selector childSevm =
      selector "transferFrom" [.address, .address, .uint256]) :
    ∃ call : WethAllowanceInvocation,
      call.approval = false ∧ call.sevm = childSevm ∧
        call.pre = childPre ∧ call.post = rawPost := by
  refine ⟨⟨childSevm, childPre, rawPost, false, target, ?_, run, ?_⟩,
    rfl, rfl, rfl, rfl⟩
  · rw [memEmpty]
    exact Mem.wf_empty
  · simpa using selected

/-- **Slotless message preserves every cell.**  With no interpreted
slot the message settles to its entry world or its post-transfer
world; value transfer moves balances only. -/
theorem processMessage_none_preserves_cell
    {msg : Msg} {post : Devm}
    (process : ProcessMessage msg .none (.ok post))
    (owner : Adr) (key : B256) :
    (post.state.getStor owner).get key =
      (msg.benv.state.getStor owner).get key := by
  rcases ProcessMessage.none_ok_state_cases process with
    rollback | ⟨benv, transfer, postEq⟩
  · rw [rollback]
  · rw [postEq]
    rw [benvAfterTransfer_preserves_getStor transfer owner]

/-- **Static message preserves every cell (interpreted slot).**  A
static interpreted slot retains no storage write; a noncommitting slot
rolls back. -/
theorem weth_static_processMessage_some_preserves_cell
    {msg : Msg} {post : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (process : ProcessMessage msg (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (static : msg.isStatic = true)
    (owner : Adr) (key : B256) :
    (post.state.getStor owner).get key =
      (msg.benv.state.getStor owner).get key := by
  by_cases settles : Frame.settlementCommits (Frame.ofCall msg) out = true
  · have committed := Frame.raw_commits_of_settlementCommits settles
    have postEq : post.state = (Execution.committedPost out committed).state :=
      ProcessMessage.ok_state_eq_committedPost process committed
    rw [postEq]
    have enter := (RunFrame.some_inv process).1
    rcases Frame.enter_run_inv enter with ⟨entry, transfer, evmEq⟩
    have sevmEq : sevm = initSevm (msg.withBenv entry) :=
      congrArg Evm.sta evmEq
    have childStatic : sevm.isStatic = true := by
      rw [sevmEq]
      show msg.isStatic = true
      exact static
    have viewEq :=
      Exec.storageView_committedPost_eq_of_static run childStatic committed
    have cellEq : ((Execution.committedPost out committed).state.getStor owner).get key
        = (pre.state.getStor owner).get key := by
      have h := congrFun (congrFun viewEq owner) key
      simp only [Devm.storageView] at h
      exact h
    rw [cellEq]
    obtain ⟨_, _, _, _, _, _, storEq, _⟩ :=
      MessageExecution.processMessage_entry_facts owner process
    rw [storEq]
  · have settledEq := (RunFrame.some_inv process).2
    have postError : post.error.isSome = true := by
      have notNone : post.error.isNone ≠ true := by
        intro clean
        apply settles
        unfold Frame.settlementCommits
        rw [← settledEq]
        exact clean
      cases errorEq : post.error <;> simp_all
    have rollback := (ProcessMessage.rollback_of_error process postError).1
    rw [rollback]

/-- **Foreign approve invocation preserves vault-owned cells.**  The
approve writes exactly its caller/spender cell; under the D9
no-collision hypothesis every other vault-owned touched cell is
silent.  State linkage is by premise; history projection discharges it
from the run package. -/
theorem weth_approve_call_silent
    {history : List WethAllowanceInvocation} {vault : Adr}
    {parentPre parentPost : Devm}
    (collision : NoVaultAllowanceKeyCollision history vault)
    (call : WethAllowanceInvocation) (member : call ∈ history)
    (approval : call.approval = true)
    (foreign : call.sevm.caller ≠ vault)
    (p : B256 × B256) (touched : p ∈ touchedWethAllowancePairs history)
    (owner : p.1 = vault.toB256)
    (preLink : call.pre.state.getStor wethAccount
      = parentPre.state.getStor wethAccount)
    (postLink : call.post.state.getStor wethAccount
      = parentPost.state.getStor wethAccount) :
    (parentPost.state.getStor wethAccount).get (wethAllowanceKey p.1 p.2) =
      (parentPre.state.getStor wethAccount).get (wethAllowanceKey p.1 p.2) := by
  rw [← preLink, ← postLink]
  have h := foreign_approve_preserves_vault_allowance collision call member
    approval foreign p touched owner
  simp only [Devm.getStorVal] at h
  exact h

/-- Calldata that matches none of the ten dispatched WETH selectors
routes to the fallback deposit path. -/
def WethFallbackCalldata (data : Bytes) : Prop :=
  ∀ sel ∈ [selector "name" [], selector "approve" [.address, .uint256],
      selector "totalSupply" [], selector "transferFrom" [.address, .address, .uint256],
      selector "withdraw" [.uint256], selector "decimals" [],
      selector "balanceOf" [.address], selector "symbol" [],
      selector "transfer" [.address, .uint256],
      selector "allowance" [.address, .address]],
    data.take 4 ≠ abiSelectorBytes sel

/-- **Gap: transfer-message silence.**  A non-static WETH transfer
touches balance rows only, so every vault-owned touched allowance
cell is silent.  Stated for history projection; the proof (per-selector
effect + key-space separation) is the next unit after the exec-free
import. -/
def WethTransferSilence (vault : Adr) : Prop :=
  ∀ {msg : Msg} {post : Devm} {slot : Xlot}
    {history : List WethAllowanceInvocation},
    ProcessMessage msg slot (.ok post) →
    msg.currentTarget = wethAccount →
    MessageUsesProgram msg Blanc.weth →
    (∃ tail, msg.data =
      abiSelectorBytes (selector "transfer" [.address, .uint256]) ++ tail) →
    msg.isStatic = false →
    NoVaultAllowanceKeyCollision history vault →
    ∀ (p : B256 × B256), p ∈ touchedWethAllowancePairs history →
      p.1 = vault.toB256 →
      (post.state.getStor wethAccount).get (wethAllowanceKey p.1 p.2) =
        (msg.benv.state.getStor wethAccount).get (wethAllowanceKey p.1 p.2)

/-- **Gap: empty-data deposit silence.**  Same shape as transfer, for
the empty-calldata fallback deposit path. -/
def WethDepositSilence (vault : Adr) : Prop :=
  ∀ {msg : Msg} {post : Devm} {slot : Xlot}
    {history : List WethAllowanceInvocation},
    ProcessMessage msg slot (.ok post) →
    msg.currentTarget = wethAccount →
    MessageUsesProgram msg Blanc.weth →
    msg.data = [] →
    msg.isStatic = false →
    NoVaultAllowanceKeyCollision history vault →
    ∀ (p : B256 × B256), p ∈ touchedWethAllowancePairs history →
      p.1 = vault.toB256 →
      (post.state.getStor wethAccount).get (wethAllowanceKey p.1 p.2) =
        (msg.benv.state.getStor wethAccount).get (wethAllowanceKey p.1 p.2)

/-- **Gap: non-matching-data fallback deposit silence.**  Same shape,
for fallback deposits with non-empty non-matching calldata. -/
def WethFallbackDepositSilence (vault : Adr) : Prop :=
  ∀ {msg : Msg} {post : Devm} {slot : Xlot}
    {history : List WethAllowanceInvocation},
    ProcessMessage msg slot (.ok post) →
    msg.currentTarget = wethAccount →
    MessageUsesProgram msg Blanc.weth →
    WethFallbackCalldata msg.data →
    msg.isStatic = false →
    NoVaultAllowanceKeyCollision history vault →
    ∀ (p : B256 × B256), p ∈ touchedWethAllowancePairs history →
      p.1 = vault.toB256 →
      (post.state.getStor wethAccount).get (wethAllowanceKey p.1 p.2) =
        (msg.benv.state.getStor wethAccount).get (wethAllowanceKey p.1 p.2)

/-- **Gap: withdraw-message silence.**  Same shape, for withdraw. -/
def WethWithdrawSilence (vault : Adr) : Prop :=
  ∀ {msg : Msg} {post : Devm} {slot : Xlot}
    {history : List WethAllowanceInvocation},
    ProcessMessage msg slot (.ok post) →
    msg.currentTarget = wethAccount →
    MessageUsesProgram msg Blanc.weth →
    (∃ tail, msg.data =
      abiSelectorBytes (selector "withdraw" [.uint256]) ++ tail) →
    msg.isStatic = false →
    NoVaultAllowanceKeyCollision history vault →
    ∀ (p : B256 × B256), p ∈ touchedWethAllowancePairs history →
      p.1 = vault.toB256 →
      (post.state.getStor wethAccount).get (wethAllowanceKey p.1 p.2) =
        (msg.benv.state.getStor wethAccount).get (wethAllowanceKey p.1 p.2)

/-- **Gap: non-static view-call silence.**  Same shape, for the six
read-only entries invoked through a non-static `CALL`. -/
def WethCallViewSilence (vault : Adr) : Prop :=
  ∀ {msg : Msg} {post : Devm} {slot : Xlot}
    {history : List WethAllowanceInvocation},
    ProcessMessage msg slot (.ok post) →
    msg.currentTarget = wethAccount →
    MessageUsesProgram msg Blanc.weth →
    (∃ tail, msg.data = abiSelectorBytes (selector "name" []) ++ tail) ∨
      (∃ tail, msg.data =
        abiSelectorBytes (selector "totalSupply" []) ++ tail) ∨
      (∃ tail, msg.data =
        abiSelectorBytes (selector "decimals" []) ++ tail) ∨
      (∃ tail, msg.data =
        abiSelectorBytes (selector "balanceOf" [.address]) ++ tail) ∨
      (∃ tail, msg.data = abiSelectorBytes (selector "symbol" []) ++ tail) ∨
      (∃ tail, msg.data =
        abiSelectorBytes (selector "allowance" [.address, .address]) ++ tail) →
    msg.isStatic = false →
    NoVaultAllowanceKeyCollision history vault →
    ∀ (p : B256 × B256), p ∈ touchedWethAllowancePairs history →
      p.1 = vault.toB256 →
      (post.state.getStor wethAccount).get (wethAllowanceKey p.1 p.2) =
        (msg.benv.state.getStor wethAccount).get (wethAllowanceKey p.1 p.2)


end Blanc.Composition.ProrataWethVault
