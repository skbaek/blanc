import Blanc.Lift.Usdc.HistorySlotsFrames
import Blanc.Lift.Usdc.Hist
import Blanc.ExecutionSettledCodeImage
import Blanc.ExecutionAccountingAdmission
import Blanc.ExecutionTraceCalldata

/-!
# "Implementation and admin slots unchanged" and the owner discipline, at history level (U6b2)

The slot induction (`usdc_slotsOk`, `HistorySlotsFrames.lean`) runs below every message root of a
configured history through a ladder (`slotLadder`) whose carrier is the proxy's storage and whose
replay is conditional: from a boundary in `SlotInv`, given `Avail` at every observed (settled)
frame, the replay ends in `SlotInv` and every observed frame satisfies `FrameQ`.  At history level
`Avail` is discharged at every settled frame: the three codes stay installed
(`ConfiguredHistoryTrace.settled_codeImage`) and F2 is `UsdcGovernance`.

* `usdc_history_frames_of`: `FrameQ` at every settled frame and `SlotInv` at the end;
* `usdc_history_slots_of`, `usdc_history_settled_owner_of`: the frozen conclusions of
  `usdc_history_slots` and `usdc_history_settled_owner`, with the signed family's law
  (`ImplStepLaw famSigned`, U6e3/U6e4) and `RescueQuietEnd` as hypotheses.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.Lift.Token
  Blanc.ExecutionAccountingReplay

/-- The slot carrier: the proxy's storage; a replay of frames, from a boundary in the invariant and
with the history's facts at each frame, ends in the invariant and delivers `FrameQ` at each frame. -/
def slotCarrier (P : Adr) (U : Key → Prop) (a₀ : Adr) : ReplayCarrier P where
  Snap := Stor
  Step := Exec.Frame
  Tag := Unit
  Replay s fs s' := (∀ f ∈ fs, Avail P a₀ f) → SlotInv U a₀ s →
    SlotInv U a₀ s' ∧ ∀ f ∈ fs, FrameQ P U a₀ f
  ofState w := w.getStor P
  frameEntry _ w := w.getStor P
  nil _ := fun _ inv => ⟨inv, fun _ h => (List.not_mem_nil h).elim⟩
  readsStorage := true
  silent := fun storage _ => storage rfl
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], fun _ inv => ⟨?_, fun _ h => (List.not_mem_nil h).elim⟩⟩
    rw [storage]; exact inv
  entry_eq_ofState := by
    intro _ _ caller_ne _ transfer sum_nof
    exact benvAfterTransfer_getStor_eq_of_safe transfer sum_nof
      (fun transfers _ => Or.inl (caller_ne transfers))

/-- Every settled frame is observed, as itself. -/
def slotObservation (P : Adr) (U : Key → Prop) (a₀ : Adr) :
    ReplayObservation (slotCarrier P U a₀) where
  O := Exec.Frame
  obs := id
  obs_nil := rfl
  obs_append := fun _ _ => rfl
  frameObs f := [f]
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], fun _ inv => ⟨?_, fun _ h => (List.not_mem_nil h).elim⟩, rfl⟩
    change SlotInv U a₀ (post.getStor P)
    rw [storage]; exact inv

/-- **The slot ladder**: its root law is the slot induction below a message root. -/
noncomputable def slotLadder (P : Adr) {U : Key → Prop} (a₀ : Adr)
    (inj : SlotFootprint.Inj Key.slot U) (apart : SlotFootprint.Apart Key.slot fixedSlots U)
    (signed : ImplStepLaw famSigned) (rescueEnd : RescueQuietEnd) :
    AccountingLadderAdmitted (ContractSpecSem.ofStorageOnly proxySem (fun _ => True)) P
      (slotEntry U) where
  carrier := slotCarrier P U a₀
  append := fun left right avail inv =>
    let ⟨mid, q₁⟩ := left (fun f hf => avail f (List.mem_append_left _ hf)) inv
    let ⟨fin, q₂⟩ := right (fun f hf => avail f (List.mem_append_right _ hf)) mid
    ⟨fin, fun f hf => (List.mem_append.mp hf).elim (q₁ f) (q₂ f)⟩
  tag _ _ := ()
  preserves := by
    intro sevm pre post fork run admitted image wf inv
    exact ⟨trivial, trivial⟩
  view := slotObservation P U a₀
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed admitted ready _ fork bound
    obtain ⟨installed, -⟩ := Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    have pcEq := congrArg Evm.pc evmEq
    have sevmEq := congrArg Evm.sta evmEq
    dsimp only [initEvm] at pcEq sevmEq
    have rootCA : sevm.currentTarget = P → sevm.codeAddress = some P := by
      intro target
      rw [sevmEq] at target ⊢
      rcases ready.codeOrForeign with call | foreign
      · exact ready.ready.codeAddress call target
      · exact (foreign target).elim
    refine ⟨Exec.committedFrames run, fun avail inv => ?_, by
      change Exec.committedFrames run = (Exec.committedFrames run).flatMap fun f => [f]
      rw [List.flatMap_singleton']⟩
    have frames : Exec.committedFrames run = Exec.Frame.ofRun run committed ::
        Exec.descendantFrames run := by
      rw [Exec.committedFrames, dite_eq_left committed]
    rw [frames] at avail ⊢
    obtain ⟨codes, gov⟩ := avail _ List.mem_cons_self
    have here : Here P a₀ sevm pre := fun target =>
      ⟨rootCA target, codes, gov ⟨target, rootCA target⟩⟩
    obtain ⟨post, desc⟩ := usdc_slotsOk inj apart signed rescueEnd _ _ _ _ run installed run
      committed fork installed admitted here (fun f hf => avail f (List.mem_cons_of_mem _ hf)) inv
    have hpost := post_of_commits committed post
    refine ⟨hpost, fun f hf => ?_⟩
    rcases List.mem_cons.mp hf with rfl | hf
    · refine ⟨inv, hpost, fun target => .inl ⟨rootCA target, ?_⟩⟩
      exact bytes_eq_of_image (installed.2 target).1
    · exact desc f hf

/-- **The slot facts at every settled frame and at the end** of a configured history from a
`UsdcHist` checkpoint, over the history's key universe, given the signed family's law. -/
theorem usdc_history_frames_of (signed : ImplStepLaw famSigned) (rescueEnd : RescueQuietEnd)
    {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future) (hist : UsdcHist P K₀ tr) :
    (∀ G ∈ tr.settledFrames,
      FrameQ P (historyKeyUniverse P tr K₀) (adminOf checkpoint.state P) G) ∧
      SlotInv (historyKeyUniverse P tr K₀) (adminOf checkpoint.state P)
        (future.state.getStor P) := by
  obtain ⟨installed, gov, foot, fresh⟩ := hist
  have ext := foot.extend fresh
  have admitted : tr.FrameAdmitted P (slotEntry (historyKeyUniverse P tr K₀)) := by
    apply (tr.frameAdmitted_iff_rawFrames P _).2
    intro root member target
    refine ⟨fun k hk => Or.inr (List.mem_flatMap.mpr ⟨root, member, ?_⟩),
      tr.calldata_bound root member⟩
    simpa only [target, ite_true] using hk
  obtain ⟨steps, replay, observed⟩ :=
    (slotLadder P (adminOf checkpoint.state P) ext.inj ext.apart signed rescueEnd).configuredHistory
      tr admitted ⟨installed.proxy, trivial, trivial⟩
  change steps = tr.settledFrames.flatMap (fun f => [f]) at observed
  rw [List.flatMap_singleton'] at observed
  subst observed
  have codeP := tr.settled_codeImage proxySem P installed.proxy
  have codeI := tr.settled_codeImage implSem usdcImpl installed.impl
  have codeL := tr.settled_codeImage libSem usdcLib installed.lib
  have avail : ∀ f ∈ tr.settledFrames, Avail P (adminOf checkpoint.state P) f := fun f hf =>
    ⟨⟨bytes_eq_of_image (codeP f hf), bytes_eq_of_image (codeI f hf),
      bytes_eq_of_image (codeL f hf)⟩, gov f hf⟩
  obtain ⟨fin, frames⟩ := replay avail ⟨installed.slot, rfl, ext.good⟩
  exact ⟨frames, fin⟩

/-- **`usdc_history_slots`, given the signed family's law.** -/
theorem usdc_history_slots_of (signed : ImplStepLaw famSigned) (rescueEnd : RescueQuietEnd)
    {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) :
    (∀ G ∈ tr.settledFrames, (G.pre.state.getStor P).get implSlot = usdcImpl.toB256 ∧
      adminOf G.pre.state P = adminOf checkpoint.state P) ∧
    (future.state.getStor P).get implSlot = usdcImpl.toB256 ∧
      adminOf future.state P = adminOf checkpoint.state P := by
  obtain ⟨frames, fin⟩ := usdc_history_frames_of signed rescueEnd tr hist
  exact ⟨fun G hG => ⟨(frames G hG).1.1, (frames G hG).1.2.1⟩, fin.1, fin.2.1⟩

/-- **`usdc_history_settled_owner`, given the signed family's law.** -/
theorem usdc_history_settled_owner_of (signed : ImplStepLaw famSigned)
    (rescueEnd : RescueQuietEnd) {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) :
    ∀ G ∈ tr.settledFrames, G.sevm.currentTarget = P →
      (G.sevm.codeAddress = some P ∧ G.sevm.code = Proxy.code) ∨
      (G.sevm.codeAddress = some usdcImpl ∧ G.sevm.code = Impl.code) ∨
      (G.sevm.codeAddress = some usdcLib ∧ G.sevm.code = Lib.code) :=
  fun G hG => ((usdc_history_frames_of signed rescueEnd tr hist).1 G hG).2.2

end Blanc.Lift.Usdc
