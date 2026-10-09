import Blanc.Lift.UniswapV2Pair.PairPositionalAdmission
import Blanc.Lift.UniswapV2Pair.PairNoCallSource
import Blanc.Lift.UniswapV2Pair.PermitSourceOccurrence
import Blanc.Lift.UniswapV2Pair.MintPositionalCanonical
import Blanc.Lift.UniswapV2Pair.SyncSourceOccurrence

namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem pair_admitted_transfer_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) :
    PairAdmittedSupply U (fun sevm => Blanc.Sevm.selector sevm = 0xa9059cbb) := by
  intro current invocation sevm b post G run K codeEq installed fork freshOutput
    representable selector good sub rep
  have touched := good.transferOwn selector
  obtain ⟨_, _, _, _, result, consumed, _⟩ := transfer_bytecode_positional_consumes
    (invocation := invocation) rep
    (Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub touched)
    representable codeEq fork selector run
  refine pairStepOutcome_with (Consumes := PairAdmittedConsumes) inj apart sub rep touched
    (PairEntryAt.transfer selector) (AdmittedSourceConsumes.of_done consumed (PairNoCallEntry.transfer.root_noExec codeEq fork selector run)) rfl rfl (fun _ h => h) ?_
  rw [result.sourceState]
  exact result.representation


/-- Compatibility projects the same admitted entry/result/output. -/
theorem pair_positional_transfer_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) :
    PairPositionalSupply U (fun sevm => Blanc.Sevm.selector sevm = 0xa9059cbb) := by
  exact PairAdmittedSupply.positional (pair_admitted_transfer_supply inj apart)

theorem pair_admitted_approve_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) :
    PairAdmittedSupply U (fun sevm => Blanc.Sevm.selector sevm = 0x095ea7b3) := by
  intro current invocation sevm b post G run K codeEq installed fork freshOutput
    representable selector good sub rep
  have touched := good.approveOwn selector
  obtain ⟨_, _, _, _, ⟨_, representation, _⟩, consumed, _⟩ :=
    approve_bytecode_positional_consumes (invocation := invocation) rep
      (Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub touched)
      representable codeEq fork selector run
  exact pairStepOutcome_with (Consumes := PairAdmittedConsumes) inj apart sub rep touched
    (PairEntryAt.approve selector) (AdmittedSourceConsumes.of_done consumed (PairNoCallEntry.approve.root_noExec codeEq fork selector run)) rfl rfl (fun _ h => h) representation


/-- Compatibility projects the same admitted entry/result/output. -/
theorem pair_positional_approve_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) :
    PairPositionalSupply U (fun sevm => Blanc.Sevm.selector sevm = 0x095ea7b3) := by
  exact PairAdmittedSupply.positional (pair_admitted_approve_supply inj apart)

theorem pair_admitted_transferFrom_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) :
    PairAdmittedSupply U (fun sevm => Blanc.Sevm.selector sevm = 0x23b872dd) := by
  intro current invocation sevm b post G run K codeEq installed fork freshOutput
    representable selector good sub rep
  have touched := good.transferFromOwn selector
  obtain ⟨_, _, _, _, result, consumed, _⟩ := transferFrom_bytecode_positional_consumes
    (invocation := invocation) rep
    (Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub touched)
    representable codeEq fork selector run
  refine pairStepOutcome_with (Consumes := PairAdmittedConsumes) inj apart sub rep touched
    (PairEntryAt.transferFrom selector) (AdmittedSourceConsumes.of_done consumed (PairNoCallEntry.transferFrom.root_noExec codeEq fork selector run)) rfl rfl (fun _ h => h) ?_
  rw [result.sourceState]
  exact result.representation


/-- Compatibility projects the same admitted entry/result/output. -/
theorem pair_positional_transferFrom_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) :
    PairPositionalSupply U (fun sevm => Blanc.Sevm.selector sevm = 0x23b872dd) := by
  exact PairAdmittedSupply.positional (pair_admitted_transferFrom_supply inj apart)

theorem pair_admitted_initialize_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) :
    PairAdmittedSupply U (fun sevm => Blanc.Sevm.selector sevm = 0x485cc955) := by
  intro current invocation sevm b post G run K codeEq installed fork freshOutput
    representable selector good sub rep
  obtain ⟨_, _, _, _, _, result, consumed, _⟩ := initialize_bytecode_positional_consumes
    (invocation := invocation) rep representable freshOutput codeEq fork selector run
  refine pairStepOutcome_with (Consumes := PairAdmittedConsumes) (keys := []) inj apart sub rep
    (fun _ h => absurd h List.not_mem_nil) (PairEntryAt.initializeEntry selector)
    (AdmittedSourceConsumes.of_done consumed (PairNoCallEntry.«initialize».root_noExec codeEq fork selector run)) rfl rfl (fun _ h => Or.inl h) ?_
  rw [result.sourceCurrent]
  exact result.representation


/-- Compatibility projects the same admitted entry/result/output. -/
theorem pair_positional_initialize_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) :
    PairPositionalSupply U (fun sevm => Blanc.Sevm.selector sevm = 0x485cc955) := by
  exact PairAdmittedSupply.positional (pair_admitted_initialize_supply inj apart)

theorem pair_admitted_permit_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (sem : CodeSem)
    (image : sem.image = some code.toList) :
    PairAdmittedSupply U (fun sevm => Blanc.Sevm.selector sevm = 0xd505accf) := by
  intro current invocation sevm b post G run K codeEq installed fork freshOutput
    representable selector good sub rep
  have touched := good.permitOwn selector
  obtain ⟨_, _, _, _, actual, settled, views, result, _, positional, _, _, _⟩ :=
    permit_bytecode_admitted_consumes (Auth := LockedAuth) (invocation := invocation) inj apart sub sem image rep touched
      (by rw [installed]; exact image.symm) representable codeEq fork selector freshOutput run good.views
  obtain ⟨_, representation, _, _, _, _, _, _, _, _, output, _⟩ := result
  exact pairStepOutcome_with (Consumes := PairAdmittedConsumes) inj apart sub rep touched
    (PairEntryAt.permit selector) positional rfl output.symm (fun _ h => h) representation


/-- Compatibility projects the same admitted entry/result/output. -/
theorem pair_positional_permit_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (sem : CodeSem)
    (image : sem.image = some code.toList) :
    PairPositionalSupply U (fun sevm => Blanc.Sevm.selector sevm = 0xd505accf) := by
  exact PairAdmittedSupply.positional (pair_admitted_permit_supply inj apart sem image)

theorem pair_admitted_view_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (view : StaticView) :
    PairAdmittedSupply U (fun sevm => Blanc.Sevm.selector sevm = view.selector) := by
  intro current invocation sevm b post G run K codeEq installed fork freshOutput
    representable selector good sub rep
  have fresh := Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub good.viewsOwn
  obtain ⟨_, _, _, storage, _, _, _, consumed, _, frameCurrent, _, _⟩ :=
    staticView_source_positional_selected (ctx := writerContext sevm invocation) rep fresh
      representable rfl codeEq fork view selector run
  refine pairStepOutcome_with (Consumes := PairAdmittedConsumes) inj apart sub rep good.viewsOwn
    (PairEntryAt.view view selector) (AdmittedSourceConsumes.of_done consumed (view.noCallEntry.root_noExec codeEq fork (by rw [StaticView.noCallEntry_selector]; exact selector) run)) rfl rfl (fun _ h => h) ?_
  rw [frameCurrent, storage sevm.currentTarget]
  exact rep.extend fresh


/-- Compatibility projects the same admitted entry/result/output. -/
theorem pair_positional_view_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (view : StaticView) :
    PairPositionalSupply U (fun sevm => Blanc.Sevm.selector sevm = view.selector) := by
  exact PairAdmittedSupply.positional (pair_admitted_view_supply inj apart view)

theorem pair_admitted_mint_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (sem : CodeSem)
    (image : sem.image = some code.toList) :
    PairAdmittedSupply U (fun sevm => Blanc.Sevm.selector sevm = 0x6a627842) := by
  intro current invocation sevm b post G run K codeEq installed fork freshOutput
    representable selector good sub rep
  have inside := writerExtend_universe sub good.mint
  obtain ⟨result⟩ := mint_positional_canonical invocation rep sem image
    (by rw [installed]; exact image.symm) codeEq fork selector run
    (writerInj_restrict inj inside) (writerApart_restrict apart inside)
  exact pairStepOutcome_with (Consumes := PairAdmittedConsumes) inj apart sub rep good.mint
    (PairEntryAt.mint selector) ⟨result.positional, result.admission LockedAuth⟩
    rfl result.output.symm result.grown result.storage


/-- Compatibility projects the same admitted entry/result/output. -/
theorem pair_positional_mint_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (sem : CodeSem)
    (image : sem.image = some code.toList) :
    PairPositionalSupply U (fun sevm => Blanc.Sevm.selector sevm = 0x6a627842) := by
  exact PairAdmittedSupply.positional (pair_admitted_mint_supply inj apart sem image)

theorem pair_admitted_sync_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (sem : CodeSem)
    (image : sem.image = some code.toList) :
    PairAdmittedSupply U (fun sevm => Blanc.Sevm.selector sevm = 0xfff6cae9) := by
  intro current invocation sevm b post G run K codeEq installed fork freshOutput
    representable selector good sub rep
  have inside := writerExtend_universe sub good.sync
  obtain ⟨_, _, result, _, representation, _, _, output⟩ := sync_bytecode_exact_consumes
    invocation rep sem image (by rw [installed]; exact image.symm) freshOutput codeEq fork
    selector run (writerInj_restrict inj inside) (writerApart_restrict apart inside)
  exact pairStepOutcome_with (Consumes := PairAdmittedConsumes) (keys := []) inj apart sub rep
    (fun _ h => absurd h List.not_mem_nil) (PairEntryAt.sync selector)
    (result.admittedConsumes (Auth := LockedAuth)) rfl output.symm (fun _ h => Or.inl h) representation


/-- Compatibility projects the same admitted entry/result/output. -/
theorem pair_positional_sync_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (sem : CodeSem)
    (image : sem.image = some code.toList) :
    PairPositionalSupply U (fun sevm => Blanc.Sevm.selector sevm = 0xfff6cae9) := by
  exact PairAdmittedSupply.positional (pair_admitted_sync_supply inj apart sem image)

/-- Concrete ready producers. The three mutable guarded families are absent;
this is not an all-selector supply or a completed strong history instance. -/
structure PairPositionalReadySupply (U : WriterKey → Prop) : Prop where
  transfer : PairPositionalSupply U (fun sevm => Blanc.Sevm.selector sevm = 0xa9059cbb)
  approve : PairPositionalSupply U (fun sevm => Blanc.Sevm.selector sevm = 0x095ea7b3)
  transferFrom : PairPositionalSupply U (fun sevm => Blanc.Sevm.selector sevm = 0x23b872dd)
  initializeEntry : PairPositionalSupply U (fun sevm => Blanc.Sevm.selector sevm = 0x485cc955)
  permit : PairPositionalSupply U (fun sevm => Blanc.Sevm.selector sevm = 0xd505accf)
  mint : PairPositionalSupply U (fun sevm => Blanc.Sevm.selector sevm = 0x6a627842)
  sync : PairPositionalSupply U (fun sevm => Blanc.Sevm.selector sevm = 0xfff6cae9)
  views : ∀ view : StaticView, PairPositionalSupply U
    (fun sevm => Blanc.Sevm.selector sevm = view.selector)

theorem pair_positional_ready_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (sem : CodeSem)
    (image : sem.image = some code.toList) : PairPositionalReadySupply U where
  transfer := pair_positional_transfer_supply inj apart
  approve := pair_positional_approve_supply inj apart
  transferFrom := pair_positional_transferFrom_supply inj apart
  initializeEntry := pair_positional_initialize_supply inj apart
  permit := pair_positional_permit_supply inj apart sem image
  mint := pair_positional_mint_supply inj apart sem image
  sync := pair_positional_sync_supply inj apart sem image
  views := pair_positional_view_supply inj apart


/-- Ready rules retain recursive admission on the same selected source result. -/
structure PairAdmittedReadySupply (U : WriterKey → Prop) : Prop where
  transfer : PairAdmittedSupply U (fun sevm => Blanc.Sevm.selector sevm = 0xa9059cbb)
  approve : PairAdmittedSupply U (fun sevm => Blanc.Sevm.selector sevm = 0x095ea7b3)
  transferFrom : PairAdmittedSupply U (fun sevm => Blanc.Sevm.selector sevm = 0x23b872dd)
  initializeEntry : PairAdmittedSupply U (fun sevm => Blanc.Sevm.selector sevm = 0x485cc955)
  permit : PairAdmittedSupply U (fun sevm => Blanc.Sevm.selector sevm = 0xd505accf)
  mint : PairAdmittedSupply U (fun sevm => Blanc.Sevm.selector sevm = 0x6a627842)
  sync : PairAdmittedSupply U (fun sevm => Blanc.Sevm.selector sevm = 0xfff6cae9)
  views : ∀ view : StaticView, PairAdmittedSupply U
    (fun sevm => Blanc.Sevm.selector sevm = view.selector)

theorem pair_admitted_ready_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (sem : CodeSem)
    (image : sem.image = some code.toList) : PairAdmittedReadySupply U where
  transfer := pair_admitted_transfer_supply inj apart
  approve := pair_admitted_approve_supply inj apart
  transferFrom := pair_admitted_transferFrom_supply inj apart
  initializeEntry := pair_admitted_initialize_supply inj apart
  permit := pair_admitted_permit_supply inj apart sem image
  mint := pair_admitted_mint_supply inj apart sem image
  sync := pair_admitted_sync_supply inj apart sem image
  views := pair_admitted_view_supply inj apart

end Blanc.Lift.UniswapV2Pair
