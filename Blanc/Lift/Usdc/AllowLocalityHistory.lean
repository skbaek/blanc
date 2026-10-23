import Blanc.Lift.Usdc.AllowLocalityV2_2
import Blanc.Lift.Usdc.OldRecoveryRelevance
import Blanc.ExecutionStagedRootFacts

/-!
# Allowance locality without a covered fork, and at raw history frames

`implV*Run_ws_noStateGas` instantiate `lift_sound_ws_noStateGas` with each
version's certificate and write-site check; the premise is
`stateGas = none` in place of `CoveredFork`. The allowance-locality laws of
`AllowLocality`/`AllowLocalityV2_2` and V1's selector-observed form follow
with the same premise change and the same conclusions.

For V2 and V2_1 the `_selectorObserved_noStateGas` forms replace the
owner-word exception by the native owner answer (`OldUsdcNativePairAnswer`, as
in `implV2_allowLocality_observed`), produced by `old_owner_pair_native` on a
`NeutralFork` from a fresh entry and a non-delegated address 1. V2_2's owner
selectors (both permit overloads) keep the selector table and calldata word 4.

The `_rawFrame` forms take the frame from a `ConfiguredHistoryTraceIn`:
`stateGas = none` and the fresh entry come from `rawFrame_entryFacts`; the V2
and V2_1 forms also take `rules.bal = none` on the history's forks (every
`HistFork`, `HistFork.bal_none`) and address 1's code at the frame without a
delegation designator. The remaining frame facts are success, the running
implementation code and the frame-local row separation `RowSep`.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

/-! ## Write-site runs on `stateGas = none` -/

theorem implV1Run_ws_noStateGas {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV1.code)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    SProg.RunP (WsStep (wsRoot ImplV1Ws.implWsAnn) (WriteSite.Env.root sevm)
      (StepIn ⟨0, sevm, pre, .ok post, run⟩)) ImplV1.cert.prog sevm pre post :=
  lift_sound_ws_noStateGas ImplV1.cert_check implV1_wsCert code hsg run

theorem implV2Run_ws_noStateGas {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV2.code)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    SProg.RunP (WsStep (wsRoot ImplV2Ws.implWsAnn) (WriteSite.Env.root sevm)
      (StepIn ⟨0, sevm, pre, .ok post, run⟩)) ImplV2.cert.prog sevm pre post :=
  lift_sound_ws_noStateGas ImplV2.cert_check implV2_wsCert code hsg run

theorem implV2_1Run_ws_noStateGas {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV2_1.code)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    SProg.RunP (WsStep (wsRoot ImplV2_1Ws.implWsAnn) (WriteSite.Env.root sevm)
      (StepIn ⟨0, sevm, pre, .ok post, run⟩)) ImplV2_1.cert.prog sevm pre post :=
  lift_sound_ws_noStateGas ImplV2_1.cert_check implV2_1_wsCert code hsg run

theorem implRun_ws_noStateGas {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = Impl.code)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    SProg.RunP (WsStep (wsRoot ImplWs.implWsAnn) (WriteSite.Env.root sevm)
      (StepIn ⟨0, sevm, pre, .ok post, run⟩)) Impl.cert.prog sevm pre post :=
  lift_sound_ws_noStateGas Impl.cert_check impl_wsCert code hsg run

/-! ## Allowance locality on `stateGas = none` -/

/-- `implV1_allowLocality` with `stateGas = none` in place of `CoveredFork`. -/
theorem implV1_allowLocality_noStateGas {pair : Adr} {Tr : Adr → Prop} {sevm : Sevm}
    {pre post : Devm} (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV1.code)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV1Ws.implWsAnn)
      (WriteSite.Env.root sevm)) :
    SProg.RunP (fun s d n d' => StepIn ⟨0, sevm, pre, .ok post, run⟩ s d n d' ∧
        GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
          (AllowedFrame selV1 pair (WriteSite.Env.root sevm)) s d n)
      ImplV1.cert.prog sevm pre post :=
  allow_locality (by decide) implV1_allowSitesOk sep (implV1Run_ws_noStateGas run code hsg)

/-- `implV2_allowLocality` with `stateGas = none` in place of `CoveredFork`. -/
theorem implV2_allowLocality_noStateGas {pair : Adr} {Tr : Adr → Prop} {sevm : Sevm}
    {pre post : Devm} (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV2.code)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV2Ws.implWsAnn)
      (WriteSite.Env.root sevm)) :
    SProg.RunP (fun s d n d' => StepIn ⟨0, sevm, pre, .ok post, run⟩ s d n d' ∧
        GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
          (AllowedFrame selV2 pair (WriteSite.Env.root sevm)) s d n)
      ImplV2.cert.prog sevm pre post :=
  allow_locality (by decide) implV2_allowSitesOk sep (implV2Run_ws_noStateGas run code hsg)

/-- `implV2_1_allowLocality` with `stateGas = none` in place of `CoveredFork`. -/
theorem implV2_1_allowLocality_noStateGas {pair : Adr} {Tr : Adr → Prop} {sevm : Sevm}
    {pre post : Devm} (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV2_1.code)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV2_1Ws.implWsAnn)
      (WriteSite.Env.root sevm)) :
    SProg.RunP (fun s d n d' => StepIn ⟨0, sevm, pre, .ok post, run⟩ s d n d' ∧
        GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
          (AllowedFrame selV2_1 pair (WriteSite.Env.root sevm)) s d n)
      ImplV2_1.cert.prog sevm pre post :=
  allow_locality (by decide) implV2_1_allowSitesOk sep (implV2_1Run_ws_noStateGas run code hsg)

/-- `implV2_2_allowLocality` with `stateGas = none` in place of `CoveredFork`. -/
theorem implV2_2_allowLocality_noStateGas {pair : Adr} {Tr : Adr → Prop} {sevm : Sevm}
    {pre post : Devm} (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = Impl.code)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplWs.implWsAnn)
      (WriteSite.Env.root sevm)) :
    SProg.RunP (fun s d n d' => StepIn ⟨0, sevm, pre, .ok post, run⟩ s d n d' ∧
        GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
          (AllowedFrame selV2_2 pair (WriteSite.Env.root sevm)) s d n)
      Impl.cert.prog sevm pre post :=
  allow_locality (by decide) implV2_2_allowSitesOk sep (implRun_ws_noStateGas run code hsg)

/-! ## Selector-observed forms -/

/-- `implV1_allowLocality_observed` with `stateGas = none` in place of
`CoveredFork`: only caller and initializer exceptions. -/
theorem implV1_allowLocality_observed_noStateGas
    {pair : Adr} {Tr : Adr → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV1.code)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV1Ws.implWsAnn)
      (WriteSite.Env.root sevm)) :
    SProg.RunP (fun s d n d' => StepIn ⟨0,sevm,pre,.ok post,run⟩ s d n d' ∧
      GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
        ((selV1T.eval (WriteSite.Env.root sevm) ∈ selV1.callers ∧ sevm.caller = pair) ∨
          selV1T.eval (WriteSite.Env.root sevm) ∈ selV1.inits) s d n)
      ImplV1.cert.prog sevm pre post := by
  refine SProg.RunP.mono ?_ (implV1_allowLocality_noStateGas run code hsg sep)
  intro s d n d' h
  refine ⟨h.1,?_⟩
  intro store x v rest registers tracked
  rcases h.2 store x v rest registers tracked with allowed | nonInc
  · rcases allowed with ⟨caller,callerEq⟩ | ⟨owner,ownerEq⟩ | initializer
    · exact Or.inl (Or.inl ⟨caller,by simpa only [WriteSite.Env.root,toAdr_toB256] using callerEq⟩)
    · exact (List.not_mem_nil owner).elim
    · exact Or.inl (Or.inr initializer)
  · exact Or.inr nonInc

private theorem selV2T_root_hist (sevm : Sevm) :
    selV2T.eval (WriteSite.Env.root sevm) = Sevm.selector sevm := by
  simp only [selV2T,Term.eval,Op2.eval,WriteSite.Env.root,Sevm.selector,Sevm.dataWord]
  rfl

/-- The V2-family selector table read at the frame root: caller exceptions
with the Pair as caller, owner-word exceptions with calldata word 4 the Pair,
or initializers. -/
private theorem allowedFrame_selV2T {t : SelTable} (hsel : t.selT = selV2T) {pair : Adr}
    {sevm : Sevm} (allowed : AllowedFrame t pair (WriteSite.Env.root sevm)) :
    (Sevm.selector sevm ∈ t.callers ∧ sevm.caller = pair) ∨
      Sevm.selector sevm ∈ t.inits ∨
      (Sevm.selector sevm ∈ t.owners ∧ (Sevm.dataWord sevm 4).toAdr = pair) := by
  simp only [AllowedFrame, hsel, selV2T_root_hist] at allowed
  rcases allowed with ⟨caller,callerEq⟩ | ⟨owner,ownerEq⟩ | initializer
  · exact Or.inl ⟨caller,by simpa only [WriteSite.Env.root,toAdr_toB256] using callerEq⟩
  · exact Or.inr (Or.inr ⟨owner, ownerEq⟩)
  · exact Or.inr (Or.inl initializer)

/-- V2 allowance locality on a `NeutralFork`, read at the frame's selector:
every protected write is non-increasing, or its frame is a caller-keyed
writer called by the Pair, an initializer, or an owner-keyed writer whose
actual native owner answer is the Pair. -/
theorem implV2_allowLocality_selectorObserved_noStateGas
    {pair : Adr} {Tr : Adr → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV2.code)
    (stack : pre.stack = []) (memory : pre.memory = Mem.empty)
    (nodeleg : getDelegatedCodeAddress (pre.getCode 1) = none)
    (neutral : NeutralFork sevm.benvStat.fork)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV2Ws.implWsAnn)
      (WriteSite.Env.root sevm)) :
    SProg.RunP (fun s d n d' => StepIn ⟨0,sevm,pre,.ok post,run⟩ s d n d' ∧
      GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
        ((Sevm.selector sevm ∈ selV2.callers ∧ sevm.caller = pair) ∨
          Sevm.selector sevm ∈ selV2.inits ∨
          OldUsdcNativePairAnswer ⟨0,sevm,pre,.ok post,run⟩ pair) s d n)
      ImplV2.cert.prog sevm pre post := by
  refine SProg.RunP.mono ?_ (implV2_allowLocality_noStateGas run code neutral.stateGas sep)
  intro s d n d' h
  refine ⟨h.1,?_⟩
  intro store x v rest registers tracked
  rcases h.2 store x v rest registers tracked with exception | nonInc
  · rcases allowedFrame_selV2T rfl exception with caller | initializer | ⟨owner, ownerEq⟩
    · exact Or.inl (Or.inl caller)
    · exact Or.inl (Or.inr (Or.inl initializer))
    · exact Or.inl (Or.inr (Or.inr (old_owner_pair_native (F := ⟨0,sevm,pre,.ok post,run⟩)
        rfl stack memory (Or.inl ⟨code,owner⟩) nodeleg rfl neutral ownerEq)))
  · exact Or.inr nonInc

/-- V2_1 allowance locality on a `NeutralFork`, read at the frame's
selector, as `implV2_allowLocality_selectorObserved_noStateGas`. -/
theorem implV2_1_allowLocality_selectorObserved_noStateGas
    {pair : Adr} {Tr : Adr → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV2_1.code)
    (stack : pre.stack = []) (memory : pre.memory = Mem.empty)
    (nodeleg : getDelegatedCodeAddress (pre.getCode 1) = none)
    (neutral : NeutralFork sevm.benvStat.fork)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV2_1Ws.implWsAnn)
      (WriteSite.Env.root sevm)) :
    SProg.RunP (fun s d n d' => StepIn ⟨0,sevm,pre,.ok post,run⟩ s d n d' ∧
      GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
        ((Sevm.selector sevm ∈ selV2_1.callers ∧ sevm.caller = pair) ∨
          Sevm.selector sevm ∈ selV2_1.inits ∨
          OldUsdcNativePairAnswer ⟨0,sevm,pre,.ok post,run⟩ pair) s d n)
      ImplV2_1.cert.prog sevm pre post := by
  refine SProg.RunP.mono ?_ (implV2_1_allowLocality_noStateGas run code neutral.stateGas sep)
  intro s d n d' h
  refine ⟨h.1,?_⟩
  intro store x v rest registers tracked
  rcases h.2 store x v rest registers tracked with exception | nonInc
  · rcases allowedFrame_selV2T rfl exception with caller | initializer | ⟨owner, ownerEq⟩
    · exact Or.inl (Or.inl caller)
    · exact Or.inl (Or.inr (Or.inl initializer))
    · exact Or.inl (Or.inr (Or.inr (old_owner_pair_native (F := ⟨0,sevm,pre,.ok post,run⟩)
        rfl stack memory (Or.inr ⟨code,owner⟩) nodeleg rfl neutral ownerEq)))
  · exact Or.inr nonInc

/-- V2_2 allowance locality on `stateGas = none`, read at the frame's
selector, as `implV2_allowLocality_selectorObserved_noStateGas`. -/
theorem implV2_2_allowLocality_selectorObserved_noStateGas
    {pair : Adr} {Tr : Adr → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = Impl.code)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplWs.implWsAnn)
      (WriteSite.Env.root sevm)) :
    SProg.RunP (fun s d n d' => StepIn ⟨0,sevm,pre,.ok post,run⟩ s d n d' ∧
      GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
        ((Sevm.selector sevm ∈ selV2_2.callers ∧ sevm.caller = pair) ∨
          Sevm.selector sevm ∈ selV2_2.inits ∨
          (Sevm.selector sevm ∈ selV2_2.owners ∧ (Sevm.dataWord sevm 4).toAdr = pair)) s d n)
      Impl.cert.prog sevm pre post := by
  refine SProg.RunP.mono ?_ (implV2_2_allowLocality_noStateGas run code hsg sep)
  intro s d n d' h
  refine ⟨h.1,?_⟩
  intro store x v rest registers tracked
  rcases h.2 store x v rest registers tracked with exception | nonInc
  · exact Or.inl (allowedFrame_selV2T rfl exception)
  · exact Or.inr nonInc

/-! ## At raw history frames -/

section RawFrame

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {pair : Adr} {Tr : Adr → Prop}

/-- **V1 allowance locality at a raw history frame.** -/
theorem implV1_allowLocality_rawFrame
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames) {post : Devm}
    (ok : R.exn = .ok post) (code : R.sevm.code = ImplV1.code)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV1Ws.implWsAnn)
      (WriteSite.Env.root R.sevm)) :
    SProg.RunP (fun s d n d' => StepIn R s d n d' ∧
        GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
          ((selV1T.eval (WriteSite.Env.root R.sevm) ∈ selV1.callers ∧ R.sevm.caller = pair) ∨
            selV1T.eval (WriteSite.Env.root R.sevm) ∈ selV1.inits) s d n)
      ImplV1.cert.prog R.sevm R.devm post := by
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities R member
  rcases R with ⟨pc', sevm, pre, out, run⟩
  dsimp only at pc hsg ok code sep ⊢
  subst pc ok
  exact implV1_allowLocality_observed_noStateGas run code hsg sep

/-- **V2 allowance locality at a raw history frame**, read at the selector. -/
theorem implV2_allowLocality_rawFrame
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames) {post : Devm}
    (ok : R.exn = .ok post) (code : R.sevm.code = ImplV2.code)
    (nodeleg : getDelegatedCodeAddress (R.devm.getCode 1) = none)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV2Ws.implWsAnn)
      (WriteSite.Env.root R.sevm)) :
    SProg.RunP (fun s d n d' => StepIn R s d n d' ∧
      GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
        ((Sevm.selector R.sevm ∈ selV2.callers ∧ R.sevm.caller = pair) ∨
          Sevm.selector R.sevm ∈ selV2.inits ∨
          OldUsdcNativePairAnswer R pair) s d n)
      ImplV2.cert.prog R.sevm R.devm post := by
  obtain ⟨pc, inF, hsg, ⟨stack, memory⟩, -⟩ := history.rawFrame_entryFacts capabilities R member
  rcases R with ⟨pc', sevm, pre, out, run⟩
  dsimp only at pc inF hsg stack memory ok code nodeleg sep ⊢
  subst pc ok
  exact implV2_allowLocality_selectorObserved_noStateGas run code stack memory nodeleg
    ⟨hsg, bal inF⟩ sep

/-- **V2_1 allowance locality at a raw history frame**, read at the selector. -/
theorem implV2_1_allowLocality_rawFrame
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames) {post : Devm}
    (ok : R.exn = .ok post) (code : R.sevm.code = ImplV2_1.code)
    (nodeleg : getDelegatedCodeAddress (R.devm.getCode 1) = none)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV2_1Ws.implWsAnn)
      (WriteSite.Env.root R.sevm)) :
    SProg.RunP (fun s d n d' => StepIn R s d n d' ∧
      GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
        ((Sevm.selector R.sevm ∈ selV2_1.callers ∧ R.sevm.caller = pair) ∨
          Sevm.selector R.sevm ∈ selV2_1.inits ∨
          OldUsdcNativePairAnswer R pair) s d n)
      ImplV2_1.cert.prog R.sevm R.devm post := by
  obtain ⟨pc, inF, hsg, ⟨stack, memory⟩, -⟩ := history.rawFrame_entryFacts capabilities R member
  rcases R with ⟨pc', sevm, pre, out, run⟩
  dsimp only at pc inF hsg stack memory ok code nodeleg sep ⊢
  subst pc ok
  exact implV2_1_allowLocality_selectorObserved_noStateGas run code stack memory nodeleg
    ⟨hsg, bal inF⟩ sep

/-- **V2_2 allowance locality at a raw history frame**, read at the selector. -/
theorem implV2_2_allowLocality_rawFrame
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames) {post : Devm}
    (ok : R.exn = .ok post) (code : R.sevm.code = Impl.code)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplWs.implWsAnn)
      (WriteSite.Env.root R.sevm)) :
    SProg.RunP (fun s d n d' => StepIn R s d n d' ∧
      GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
        ((Sevm.selector R.sevm ∈ selV2_2.callers ∧ R.sevm.caller = pair) ∨
          Sevm.selector R.sevm ∈ selV2_2.inits ∨
          (Sevm.selector R.sevm ∈ selV2_2.owners ∧ (Sevm.dataWord R.sevm 4).toAdr = pair)) s d n)
      Impl.cert.prog R.sevm R.devm post := by
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities R member
  rcases R with ⟨pc', sevm, pre, out, run⟩
  dsimp only at pc hsg ok code sep ⊢
  subst pc ok
  exact implV2_2_allowLocality_selectorObserved_noStateGas run code hsg sep

end RawFrame

end Blanc.Lift.Usdc
