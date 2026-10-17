import Blanc.Composition.Weth9TokenFramesExec
import Blanc.Composition.Weth9Token
import Blanc.ExecutionAccountingAdmission

/-!
# WETH9's per-frame history facts for the token core

Over a configured history whose checkpoint satisfies `Weth9Hist` (WETH9 installed at `ca`, one
initial footprint `K₀`, the trace-local key freshness), every settled frame `f`

* targeting `ca` runs WETH9's code from pc `0` on a covered fork, **static frames included**
  (`weth9_history_settled_code`);
* targeting `ca` has code address `some ca`, so it is the token's entry frame
  (`weth9_history_settled_codeAddress`, `weth9_history_decodes`);
* is entered with the booked footprint ledger good: its total fits a word
  (`weth9_history_goodAt`; at the checkpoint, `weth9_history_goodStart`).

All three read one fact, `FrameOk`, at every settled frame (`weth9_history_framesOk`).  It comes from a
ladder (`frameLadder`) whose carrier holds no snapshot and whose observation is every settled frame:
the generic history rungs (`AccountingLadderAdmitted.configuredHistory`) thread the message roots
(their entry precondition and code address from `MessageRunReady`), and the root law is the
derivation-level `weth9_framesOk`.
-/

namespace Blanc.Composition.Weth9TokenFrames

open Jaune Blanc Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.Token Blanc.ExecutionTrace
  Blanc.ExecutionAccountingReplay Blanc.Composition.Weth9Token

/-- The frame-fact carrier: no snapshot; a step is a settled frame, and a replay says each of its
steps carries `FrameOk`. -/
def frameCarrier (ca : Adr) (U : Key → Prop) : ReplayCarrier ca where
  Snap := Unit
  Step := Exec.Frame
  Tag := Unit
  Replay _ steps _ := ∀ f ∈ steps, FrameOk ca U f
  ofState _ := ()
  frameEntry _ _ := ()
  nil _ := fun _ h => (List.not_mem_nil h).elim
  readsStorage := false
  silent := fun _ _ => rfl
  credit := fun _ _ _ _ _ _ _ => ⟨[], fun _ h => (List.not_mem_nil h).elim⟩
  entry_eq_ofState := fun _ _ _ _ => rfl

/-- Every settled frame is observed, as itself. -/
def frameObservation (ca : Adr) (U : Key → Prop) : ReplayObservation (frameCarrier ca U) where
  O := Exec.Frame
  obs := id
  obs_nil := rfl
  obs_append := fun _ _ => rfl
  frameObs f := [f]
  credit := fun _ _ _ _ _ _ _ => ⟨[], fun _ h => (List.not_mem_nil h).elim, rfl⟩

/-- **The frame-fact ladder** over a tracked universe with injective slots: its root law is
`weth9_framesOk` below a message root entered in the footprint precondition. -/
noncomputable def frameLadder (ca : Adr) {U : Key → Prop} (hinj : KeyInj U) :
    AccountingLadderAdmitted (footSpec U) ca (footEntry U) where
  carrier := frameCarrier ca U
  append := fun h₁ h₂ f hf => (List.mem_append.mp hf).elim (h₁ f) (h₂ f)
  tag _ _ := ()
  preserves := footSpec_preservesAdmitted ca hinj
  view := frameObservation ca U
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed admitted ready _ fork bound
    refine ⟨Exec.committedFrames run, ?_, ?_⟩
    · obtain ⟨installed, -⟩ := Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
      have precondition := ContractSpecSem.Pre.of_inv_benvAfterTransfer
        ready.ready.ne ready.ready.val0 transfer ready.ready.state
      have pcEq := congrArg Evm.pc evmEq
      have sevmEq := congrArg Evm.sta evmEq
      have preEq := congrArg Evm.dyna evmEq
      dsimp only [initEvm] at pcEq sevmEq preEq
      subst pc sevm pre
      have rootCA : (initSevm (msg.withBenv entryBenv)).currentTarget = ca →
          (initSevm (msg.withBenv entryBenv)).codeAddress = some ca := by
        intro target
        rcases ready.codeOrForeign with call | foreign
        · exact ready.ready.codeAddress call target
        · exact (foreign target).elim
      intro f hf
      rw [Exec.committedFrames, dite_eq_left committed] at hf
      rcases List.mem_cons.mp hf with rfl | hd
      · exact ⟨⟨precondition, fun _ => Mem.wf_empty⟩, installed, rootCA, fork⟩
      · exact weth9_framesOk ca hinj _ _ _ _ run installed run committed fork installed admitted
          ⟨precondition, fun _ => Mem.wf_empty⟩ rootCA f hd
    · show Exec.committedFrames run = (Exec.committedFrames run).flatMap fun f => [f]
      rw [List.flatMap_singleton']

/-- **`FrameOk` at every settled frame** of a configured history from a `Weth9Hist` checkpoint, over
the history's key universe. -/
theorem weth9_history_framesOk {ca : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : Weth9Hist ca K₀ trace) :
    ∀ f ∈ trace.settledFrames, FrameOk ca (historyKeyUniverse ca trace K₀) f := by
  obtain ⟨installed, sumNof, initial, fresh⟩ := hist
  let U := historyKeyUniverse ca trace K₀
  have extended : FootInv U (checkpoint.state.getStor ca) (checkpoint.state.bal ca) :=
    initial.extend fresh
  have admitted : trace.FrameAdmitted ca (footEntry U) := by
    apply (trace.frameAdmitted_iff_rawFrames ca _).2
    intro root member target k hk
    exact Or.inr (touchedKeys_mem member target hk)
  have start : (footSpec U).StateInv ca checkpoint.state :=
    footSpec_stateInv_iff.mpr ⟨installed, sumNof, extended.support, extended.backed⟩
  obtain ⟨steps, replay, observed⟩ :=
    (frameLadder ca extended.inj).configuredHistory trace admitted start
  change ∀ f ∈ steps, FrameOk ca U f at replay
  change steps = trace.settledFrames.flatMap (fun f => [f]) at observed
  intro f hf
  apply replay
  rw [observed, List.flatMap_singleton']
  exact hf

/-- **Code identity, static frames included.**  Every settled frame at `ca` runs WETH9's code from
pc `0` on a covered fork, with the code installed at `ca`. -/
theorem weth9_history_settled_code {ca : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : Weth9Hist ca K₀ trace) :
    ∀ f ∈ trace.settledFrames, f.sevm.currentTarget = ca →
      f.pc = 0 ∧ f.sevm.code = code ∧ CoveredFork f.sevm.benvStat.fork ∧
        weth9Sem.At ca 0 f.sevm f.pre := by
  intro f member target
  have ok := weth9_history_framesOk trace hist f member
  obtain ⟨image, pcZero⟩ := ok.at_.2 target
  refine ⟨pcZero, code_eq_of_image image, ok.fork, ?_⟩
  rw [← pcZero]
  exact ok.at_

/-- **Code address.**  Every settled frame at `ca` runs at code address `ca`. -/
theorem weth9_history_settled_codeAddress {ca : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : Weth9Hist ca K₀ trace) :
    ∀ f ∈ trace.settledFrames, f.sevm.currentTarget = ca → f.sevm.codeAddress = some ca :=
  fun f member => (weth9_history_framesOk trace hist f member).codeAddress

/-- **`decodes`, in its strongest form**: every settled frame at `ca` is the token's entry frame. -/
theorem weth9_history_decodes {ca : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : Weth9Hist ca K₀ trace) :
    ∀ g ∈ trace.settledFrames, g.sevm.currentTarget = ca → IsEntry ca g :=
  fun g member target => ⟨target, weth9_history_settled_codeAddress trace hist g member target⟩

/-- The footprint ledger is good wherever the footprint precondition holds. -/
theorem good_of_pre {ca : Adr} {U : Key → Prop} {sevm : Sevm} {d : Devm}
    (h : (footSpec U).Pre ca sevm d) : weth9Book.Good (ledger U (d.state.getStor ca)) := by
  have hle : trackedSum U (Devm.getStor d ca) ≤ (d.getBal ca).toNat := by
    by_cases target : sevm.currentTarget = ca
    · have := (footSpec_inv.mp (h.inv.1 target)).2
      omega
    · have := (footSpec_inv.mp (h.inv.2 target)).2
      omega
  have hlt := B256.toNat_lt (d.getBal ca)
  change trackedSum U (Devm.getStor d ca) < 2 ^ 256
  omega

/-- **`goodAt`**: every settled frame is entered with the booked footprint ledger good. -/
theorem weth9_history_goodAt {ca : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : Weth9Hist ca K₀ trace) :
    ∀ f ∈ trace.settledFrames,
      weth9Book.Good (ledger (historyKeyUniverse ca trace K₀) (f.pre.state.getStor ca)) :=
  fun f member => good_of_pre (weth9_history_framesOk trace hist f member).pre.pre

/-- **`goodStart`**: the booked footprint ledger is good at the checkpoint. -/
theorem weth9_history_goodStart {ca : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : Weth9Hist ca K₀ trace) :
    weth9Book.Good
      (ledger (historyKeyUniverse ca trace K₀) (checkpoint.state.getStor ca)) := by
  obtain ⟨-, -, initial, fresh⟩ := hist
  have backed : trackedSum (historyKeyUniverse ca trace K₀) (checkpoint.state.getStor ca) ≤
      (checkpoint.state.bal ca).toNat := (initial.extend fresh).backed
  have hlt := B256.toNat_lt (checkpoint.state.bal ca)
  change trackedSum (historyKeyUniverse ca trace K₀) (checkpoint.state.getStor ca) < 2 ^ 256
  omega

end Blanc.Composition.Weth9TokenFrames
