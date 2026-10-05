import Blanc.Lift.UniswapV2Pair.PairSupply
import Blanc.Lift.UniswapV2Pair.SourceReplay
import Blanc.Lift.UniswapV2Pair.Creation.DeployInit
import Blanc.ExecutionWholeFrameAccounting
import Blanc.ExecutionTraceEntered
import Blanc.ExecutionTraceEntry
import Blanc.ExecutionTraceCalldata
import Blanc.StorageOnlySpec
import Blanc.Lift.Cursor

/-!
# The Uniswap V2 Pair's configured history

The pair's storage after any configured history is the model state obtained by replaying, from the
checkpoint's model state, one authenticated source invocation per *outermost* committed non-static
Pair frame, in trace order; a re-entered Pair frame is consumed inside its parent's transcript.

* `pairSem`, `pair_spawnKinds` — the certified runtime as a code semantics; its frames spawn only by
  `CALL`/`STATICCALL`;
* `pairSpec U` — the storage-only frame contract "the storage is a finite representation over rows
  of `U`"; `pairEntry U` — its trace-local entry condition (fresh frame, empty output, short calldata,
  every entered Pair frame's rows in `U`);
* `PairStep` — one committed Pair frame with the invocation consuming it; `PairStep.Authentic`;
* `pairCarrier`, `pairObservation` — the replay carrier over the storage view, whose steps are frames
  and whose replay produces authenticated invocations from every incoming representation;
* `pair_wholeFrameReplay`, `pairSpec_preservesAdmitted` — the ladder's two contract obligations, from
  `pairSupply`;
* `pair_history_committed` — the headline; `pair_history_initialized` — from the deployment
  checkpoint.

The burn arm of the supply is the explicit premise `BurnFrameSupply burnAuth` until the Burn transcript
provenance is merged.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-! ## The code semantics -/

theorem code_toList_length : code.toList.length = 11293 := by
  rw [ByteArray.toList_eq_toList_data, Array.length_toList]
  decide +kernel

theorem code_eq_of_toList {c : ByteArray} (h : some c.toList = some code.toList) : c = code := by
  have dataList : c.data.toList = code.data.toList := by
    simpa only [ByteArray.toList_eq_toList_data] using Option.some.inj h
  exact congrArg ByteArray.mk (Array.toList_inj.mp dataList)

/-- The certified Pair runtime as a code semantics. -/
def pairSem : CodeSem where
  image := some code.toList
  Run sevm _ _ := sevm.code = code
  correct := fun _ hcode => code_eq_of_toList hcode
  ne_nil := by
    intro l hl h
    have hlen := code_toList_length
    rw [Option.some.inj hl, h] at hlen
    exact absurd hlen (by decide)
  not_delegation := by
    intro c hc hdel
    have hlen : c.toList.length = 11293 := (Option.some.inj hc) ▸ code_toList_length
    rw [ByteArray.toList_eq_toList_data, Array.length_toList] at hlen
    have hsize : c.size = eoaDelegatedCodeLength := hdel.1
    have hsz : c.size = c.data.size := rfl
    rw [hsz, hlen] at hsize
    exact absurd hsize (by decide)

theorem pairSem_image : pairSem.image = some code.toList := rfl

/-- Pair frames spawn only by `CALL`/`STATICCALL` (the certificate cursor). -/
theorem pair_spawnKinds (pair : Adr) : SpawnKinds pair pairSem := by
  intro sevm pre post run hrun _ fork _ node chain x hat
  obtain ⟨κ, -, ok⟩ := Blanc.Lift.cursor_of_parentPrefix cert_check
    (F := ⟨0, sevm, pre, .ok post, run⟩) rfl hrun fork chain
  exact ok.exec_call_or_staticcall hat

/-! ## The frame contract and its entry condition -/

/-- The storage is a finite representation, over rows of the universe `U`, of some model state. -/
def PairRep (U : WriterKey → Prop) (s : Stor) : Prop :=
  ∃ (st : State) (K : WriterKey → Prop), (∀ k, K k → U k) ∧ WriterRep K s st

/-- The storage-only Pair frame contract over a trace-local universe `U`. -/
def pairSpec (U : WriterKey → Prop) : ContractSpecSem :=
  ContractSpecSem.ofStorageOnly pairSem (PairRep U)

/-- The Pair's trace-local entry condition: a freshly entered frame (empty stack, memory and
output), short calldata, and the rows of every Pair frame its derivation enters in `U`. -/
def pairEntry (U : WriterKey → Prop) : Sevm → Devm → Prop := fun sevm pre =>
  Exec.FreshEntry sevm pre ∧ pre.output = [] ∧ sevm.data.length < 2 ^ 256 ∧
    Exec.derivEntry (PairGood U) sevm pre

/-- A successful Pair frame admitted by `pairEntry`, restated at its raw `St` form. -/
theorem pair_frame_raw {U : WriterKey → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (entry : pairEntry U sevm pre) :
    ∃ raw : Exec 0 sevm (St pre [] Mem.empty pre.gasLeft) (.ok post),
      (⟨0, sevm, St pre [] Mem.empty pre.gasLeft, .ok post, raw⟩ : Exec.Deriv) =
        ⟨0, sevm, pre, .ok post, run⟩ ∧
      PairGood U ⟨0, sevm, St pre [] Mem.empty pre.gasLeft, .ok post, raw⟩ := by
  obtain ⟨⟨stack, memory⟩, _, _, deriv⟩ := entry
  obtain ⟨raw, rawEq⟩ : ∃ raw : Exec 0 sevm (St pre [] Mem.empty pre.gasLeft) (.ok post),
      (⟨0, sevm, St pre [] Mem.empty pre.gasLeft, .ok post, raw⟩ : Exec.Deriv) =
        ⟨0, sevm, pre, .ok post, run⟩ := by
    rw [← Blanc.Lift.St.self stack memory]
    exact ⟨run, rfl⟩
  refine ⟨raw, rawEq, ?_⟩
  rw [rawEq]
  exact deriv _ run

/-- A representation is a property of the storage view. -/
theorem WriterRep.congr {K : WriterKey → Prop} {s s' : Stor} {st : State}
    (same : ∀ k, s'.get k = s.get k) (wrep : WriterRep K s st) : WriterRep K s' st := by
  refine ⟨wrep.finite, ?_, ?_, wrep.inj, wrep.apart, ?_, wrep.logicalZero⟩
  · have fixed := wrep.fixed
    simp only [WriterFixedMatches, same] at fixed ⊢
    exact fixed
  · intro x nonzero
    rw [same] at nonzero
    exact wrep.support x nonzero
  · intro k tracked
    rw [same]
    exact wrep.selected k tracked

/-- **Pair frame soundness, trace-admitted**: a successful Pair frame keeps the storage a finite
representation over rows of a separated universe. -/
theorem pairSpec_soundAdmitted (pair : Adr) {burnAuth : Exec.Deriv → Entry → Transcript → Prop}
    (burn : BurnFrameSupply burnAuth) {U : WriterKey → Prop} (inj : WriterInj U)
    (apart : WriterApart U) : (pairSpec U).SoundAdmitted pair (pairEntry U) := by
  intro sevm pre post fork run codeEq target admitted _ _ hpre
  subst target
  have entry := admitted.root rfl
  obtain ⟨raw, _, good⟩ := pair_frame_raw run entry
  obtain ⟨_, output, representable, _⟩ := entry
  obtain ⟨st, K, sub, wrep⟩ :=
    (ContractSpecSem.ofStorageOnly_preInv_iff (sem := pairSem)).mp hpre.inv
  obtain ⟨_, _, _, _, K', _, _, _, _, inside, rep⟩ :=
    pairSupply burn inj apart pairSem pairSem_image { state := st, logs := [], updates := [] } []
      raw codeEq (code_eq_of_toList hpre.code) fork output representable trivial good sub wrep
  exact ⟨trivial, ⟨_, K', inside, rep⟩⟩

/-- **Pair frame preservation, trace-admitted**: the form the trace rungs consume. -/
theorem pairSpec_preservesAdmitted (pair : Adr) {burnAuth : Exec.Deriv → Entry → Transcript → Prop}
    (burn : BurnFrameSupply burnAuth) {U : WriterKey → Prop} (inj : WriterInj U)
    (apart : WriterApart U) : (pairSpec U).PreservesAdmitted pair (pairEntry U) :=
  (pairSpec U).preserves_inv_admitted pair (pairEntry U)
    (pairSpec_soundAdmitted pair burn inj apart)

/-! ## Steps, carrier and observation -/

/-- One committed Pair frame with the source invocation that consumes it, re-entered Pair frames
included in its transcript. -/
structure PairStep where
  frame : Exec.Frame
  entry : Entry
  transcript : Transcript

/-- The source invocation of a step, at the frame's own writer context. -/
def PairStep.source (s : PairStep) : SourceInvocation :=
  { context := writerContext s.frame.sevm [], entry := s.entry, transcript := s.transcript }

/-- **An authenticated step.**  The step's frame is a pc-zero, *committed* (`Exec.Frame` carries its
commit proof; it is restated here), non-static frame at the Pair, and its entry and transcript are the
ones its actual run decodes and answered (`PairFrameAuth`).  A committed non-static Pair frame always
observes itself (`pairSubtreeFrames`), so a step can never be a phantom: the observation equality of
the headline places every step's frame among the trace's settled frames. -/
def PairStep.Authentic (burnAuth : Exec.Deriv → Entry → Transcript → Prop) (pair : Adr)
    (s : PairStep) : Prop :=
  s.frame.pc = 0 ∧ Execution.commits s.frame.out = true ∧ s.frame.sevm.currentTarget = pair ∧
    s.frame.sevm.isStatic = false ∧
    PairFrameAuth burnAuth (Blanc.Exec.Frame.rootDeriv s.frame) s.entry s.transcript

/-- A frame's own observation: itself when it is a non-static Pair frame. -/
def pairFrameObservation (pair : Adr) (frame : Exec.Frame) : List Exec.Frame :=
  if frame.sevm.currentTarget = pair ∧ frame.sevm.isStatic = false then [frame] else []

/-- The committed non-static Pair frames of a frame's subtree, in execution order. -/
def pairSubtreeFrames (pair : Adr) (f : Exec.Frame) : List Exec.Frame :=
  (Exec.committedFrames f.run).flatMap (pairFrameObservation pair)

/-- A model state represented by a storage view. -/
def PairViewRep (K : WriterKey → Prop) (view : B256 → B256) (st : State) : Prop :=
  ∃ s : Stor, s.get = view ∧ WriterRep K s st

/-- The replay of a list of frames between two storage views: from every incoming representation
inside `U`, authenticated steps over exactly these frames whose source invocations replay to a model
state represented by the outgoing view. -/
def PairReplay (burnAuth : Exec.Deriv → Entry → Transcript → Prop) (pair : Adr)
    (U : WriterKey → Prop) (a : B256 → B256) (frames : List Exec.Frame) (b : B256 → B256) : Prop :=
  ∀ (st : State) (K : WriterKey → Prop), (∀ k, K k → U k) → PairViewRep K a st →
    ∃ steps : List PairStep, steps.map PairStep.frame = frames ∧
      (∀ s ∈ steps, s.Authentic burnAuth pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop), SourceReplay st (steps.map PairStep.source) finish ∧
        (∀ k, K k → K' k) ∧ (∀ k, K' k → U k) ∧ PairViewRep K' b finish

section Replay

variable {burnAuth : Exec.Deriv → Entry → Transcript → Prop} {pair : Adr} {U : WriterKey → Prop}

theorem PairReplay.nil (view : B256 → B256) : PairReplay burnAuth pair U view [] view := by
  intro st K sub rep
  exact ⟨[], rfl, fun _ h => absurd h List.not_mem_nil, st, K, .nil st, fun _ h => h, sub, rep⟩

theorem PairReplay.append {a b c : B256 → B256} {left right : List Exec.Frame}
    (first : PairReplay burnAuth pair U a left b) (second : PairReplay burnAuth pair U b right c) :
    PairReplay burnAuth pair U a (left ++ right) c := by
  intro st K sub rep
  obtain ⟨steps₁, frames₁, auth₁, middle, K₁, replay₁, grows₁, sub₁, rep₁⟩ := first st K sub rep
  obtain ⟨steps₂, frames₂, auth₂, finish, K₂, replay₂, grows₂, sub₂, rep₂⟩ :=
    second middle K₁ sub₁ rep₁
  refine ⟨steps₁ ++ steps₂, ?_, ?_, finish, K₂, ?_, fun k h => grows₂ k (grows₁ k h), sub₂, rep₂⟩
  · rw [List.map_append, frames₁, frames₂]
  · intro s member
    rcases List.mem_append.mp member with h | h
    · exact auth₁ s h
    · exact auth₂ s h
  · rw [List.map_append]
    exact replay₁.append replay₂

end Replay

/-- The Pair's replay carrier over its storage view. -/
def pairCarrier (burnAuth : Exec.Deriv → Entry → Transcript → Prop) (pair : Adr)
    (U : WriterKey → Prop) : ReplayCarrier pair where
  Snap := B256 → B256
  Step := Exec.Frame
  Tag := Unit
  Replay := PairReplay burnAuth pair U
  ofState world := (world.getStor pair).get
  frameEntry _ world := (world.getStor pair).get
  nil := PairReplay.nil
  silent := fun storage _ => by rw [storage]
  credit := by
    intro _ pre post _ storage _ _
    exact ⟨[], by rw [storage]; exact PairReplay.nil _⟩
  entry_eq_ofState := by
    intro _ _ _ _ transfer _
    exact congrArg Stor.get (congrFun (benvAfterTransfer_getStor_eq transfer) pair)

/-- The Pair's observation: every committed non-static Pair frame of each step's subtree. -/
def pairObservation (burnAuth : Exec.Deriv → Entry → Transcript → Prop) (pair : Adr)
    (U : WriterKey → Prop) : ReplayObservation (pairCarrier burnAuth pair U) where
  O := Exec.Frame
  obs frames := frames.flatMap (pairSubtreeFrames pair)
  obs_nil := rfl
  obs_append := fun _ _ => List.flatMap_append
  frameObs := pairFrameObservation pair
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], ?_, rfl⟩
    change PairReplay burnAuth pair U (pre.getStor pair).get [] (post.getStor pair).get
    rw [storage]
    exact PairReplay.nil _

/-- **The whole-frame obligation of the Pair**: a committed non-static Pair frame replays as one
authenticated step whose observation is its committed subtree. -/
theorem pair_wholeFrameReplay (pair : Adr) {burnAuth : Exec.Deriv → Entry → Transcript → Prop}
    (burn : BurnFrameSupply burnAuth) {U : WriterKey → Prop} (inj : WriterInj U)
    (apart : WriterApart U) :
    Exec.CoreAccounting.WholeFrameReplay pair pairSem (pairEntry U) (pairCarrier burnAuth pair U)
      (pairObservation burnAuth pair U) := by
  intro sevm pre post run committed codeEq target fork installed admitted _ nonstatic
  subst target
  have entry := admitted.root rfl
  obtain ⟨raw, rawEq, good⟩ := pair_frame_raw run entry
  obtain ⟨_, output, representable, _⟩ := entry
  refine ⟨[Exec.Frame.ofRun run committed], ?_, ?_⟩
  · intro st K sub incoming
    obtain ⟨s, view, wrep⟩ := incoming
    have wrep' : WriterRep K (pre.getStor sevm.currentTarget) st :=
      WriterRep.congr (fun k => (congrFun view k).symm) wrep
    obtain ⟨entryE, nested, child, bytes, K', auth, consumed, success, grows, inside, rep⟩ :=
      pairSupply burn inj apart pairSem pairSem_image { state := st, logs := [], updates := [] } []
        raw codeEq (code_eq_of_toList installed.1) fork output representable trivial good sub wrep'
    rw [rawEq] at auth
    refine ⟨[⟨Exec.Frame.ofRun run committed, entryE, nested⟩], rfl, ?_, child.frame.current.state,
      K', .cons consumed success (.nil _), grows, inside, ⟨_, rfl, rep⟩⟩
    intro s member
    rw [List.mem_singleton] at member
    subst member
    exact ⟨rfl, committed, rfl, nonstatic, auth⟩
  · change [Exec.Frame.ofRun run committed].flatMap (pairSubtreeFrames sevm.currentTarget) = _
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl

theorem pairFrameObservation_static {pair : Adr} {f : Exec.Frame} (h : f.sevm.isStatic = true) :
    pairFrameObservation pair f = [] := by
  unfold pairFrameObservation
  simp only [h, Bool.true_eq_false, and_false, ↓reduceIte]

theorem pairFrameObservation_foreign {pair : Adr} {f : Exec.Frame}
    (h : f.sevm.currentTarget ≠ pair) : pairFrameObservation pair f = [] := by
  unfold pairFrameObservation
  simp only [h, false_and, ↓reduceIte]

/-- **The accounting ladder of the Pair** over a separated universe `U`. -/
def pairLadder (pair : Adr) {burnAuth : Exec.Deriv → Entry → Transcript → Prop}
    (burn : BurnFrameSupply burnAuth) {U : WriterKey → Prop} (inj : WriterInj U)
    (apart : WriterApart U) : AccountingLadderAdmitted (pairSpec U) pair (pairEntry U) :=
  wholeFrameLadder (c := pairSpec U) (pairCarrier burnAuth pair U) (pairObservation burnAuth pair U)
    PairReplay.append (fun _ _ => ()) (fun _ _ => ()) (fun _ _ => rfl)
    (fun h => funext h) (fun _ h => pairFrameObservation_static h)
    (fun _ h => pairFrameObservation_foreign h) (pair_spawnKinds pair)
    (pair_wholeFrameReplay pair burn inj apart) (pairSpec_preservesAdmitted pair burn inj apart)

/-! ## The configured history -/

/-- HASH-T rows of a history: the rows of every Pair frame entered below every raw Pair frame root of
the trace, rolled-back frames included. -/
noncomputable def pairHistoryTouchedKeys {cfg : ChainConfig} {checkpoint future : BlockChain}
    (pair : Adr) (trace : ConfiguredHistoryTrace cfg checkpoint future) : List WriterKey :=
  trace.rawFrames.flatMap fun D => if D.sevm.currentTarget = pair then pairDerivKeys D else []

/-- The settlement-committed non-static Pair frames of a history, in trace order. -/
def committedPairFrames {cfg : ChainConfig} {checkpoint future : BlockChain} (pair : Adr)
    (trace : ConfiguredHistoryTrace cfg checkpoint future) : List Exec.Frame :=
  trace.settledFrames.flatMap (pairFrameObservation pair)

/-- Every Pair frame root of a configured history is admitted by `pairEntry` over a universe holding
the history's touched rows. -/
theorem pair_trace_admitted {cfg : ChainConfig} {checkpoint future : BlockChain} {pair : Adr}
    {U : WriterKey → Prop} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (touched : ∀ k ∈ pairHistoryTouchedKeys pair trace, U k) :
    trace.FrameAdmitted pair (pairEntry U) := by
  apply (trace.frameAdmitted_iff_rawFrames pair _).2
  intro root member target
  refine ⟨trace.rawFrames_entered (E := Exec.FreshEntry) enteredCondition_fresh root member,
    trace.rawFrames_entered (E := fun _ pre => pre.output = []) enteredCondition_output root member,
    trace.calldata_bound root member,
    Exec.derivEntry_of_deriv (trace.rootEntry root member).1 (pairGood_of_keys ?_)⟩
  intro k row
  apply touched k
  apply List.mem_flatMap.mpr
  refine ⟨root, member, ?_⟩
  rw [ite_eq_left target]
  exact row

/-- **The Pair model replays the committed history (U2(b)).**  In a configured history from a
checkpoint whose Pair storage represents the model state `st₀` over tracked rows `K₀` (the certified
runtime installed), whose touched rows are fresh against `K₀` (the trace-local hash premise), the
runtime is still installed, and there is a list of steps such that

* flattening each step's committed subtree gives *exactly* the settlement-committed non-static Pair
  frames of the trace, in trace order (rolled-back frames are absent, static frames observe nothing):
  each step is an outermost committed Pair frame, and every re-entered Pair frame lies in exactly one
  step's subtree, consumed inside that step's transcript;
* every step is authenticated against its frame's actual run (`PairStep.Authentic`; the burn arm
  through `burnAuth`);
* the step's source invocations replay from `st₀` (`SourceReplay`, hence the deterministic fold
  `runSourceInvocations`) to a model state that the future Pair storage represents, over tracked rows
  growing from `K₀` within `K₀ ∪ touched`.

The burn arm is the explicit premise `burn : BurnFrameSupply burnAuth` (open). -/
theorem pair_history_committed {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State} {burnAuth : Exec.Deriv → Entry → Transcript → Prop}
    (burn : BurnFrameSupply burnAuth)
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace)) :
    some (future.state.getCode pair).toList = pairSem.image ∧
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.Authentic burnAuth pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        SourceReplay st₀ (steps.map PairStep.source) finish ∧
        runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
        (∀ k, K₀ k → K' k) ∧
        (∀ k, K' k → WriterExtend K₀ (pairHistoryTouchedKeys pair trace) k) ∧
        WriterRep K' (future.state.getStor pair) finish := by
  let U := WriterExtend K₀ (pairHistoryTouchedKeys pair trace)
  have extended : WriterRep U (checkpoint.state.getStor pair) st₀ := initial.extend fresh
  have admitted : trace.FrameAdmitted pair (pairEntry U) :=
    pair_trace_admitted trace (fun k row => Or.inr row)
  have start : (pairSpec U).StateInv pair checkpoint.state :=
    ⟨installed, trivial, ⟨st₀, K₀, fun _ h => Or.inl h, initial⟩⟩
  have finishInv := trace.stateInv_admitted_sem
    (pairSpec_preservesAdmitted pair burn extended.inj extended.apart) admitted start
  obtain ⟨frames, replay, observed⟩ :=
    (pairLadder pair burn extended.inj extended.apart).configuredHistory trace admitted start
  change PairReplay burnAuth pair U (checkpoint.state.getStor pair).get frames
    (future.state.getStor pair).get at replay
  change frames.flatMap (pairSubtreeFrames pair) =
    trace.settledFrames.flatMap (pairFrameObservation pair) at observed
  obtain ⟨steps, framesEq, auth, finish, K', source, grows, inside, s, view, rep⟩ :=
    replay st₀ K₀ (fun _ h => Or.inl h) ⟨_, rfl, initial⟩
  refine ⟨finishInv.code, steps, ?_, auth, finish, K', source, source.realizes, grows, inside,
    WriterRep.congr (fun k => (congrFun view k).symm) rep⟩
  rw [← framesEq, List.flatMap_map] at observed
  exact observed

/-- **The Pair history from its deployment checkpoint.**  From the storage `pair_create2_initialized`
establishes (deployment by `factory`, then `initialize`), the same conclusion with
`st₀ = initializedState factory domain token0 token1` and no initially tracked row. -/
theorem pair_history_initialized {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {factory token0 token1 : Adr} {domain : B256}
    {burnAuth : Exec.Deriv → Entry → Transcript → Prop} (burn : BurnFrameSupply burnAuth)
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : InitializedCheckpoint (checkpoint.state.getStor pair) factory domain token0 token1)
    (fresh : WriterFreshKeys (fun _ => False) (pairHistoryTouchedKeys pair trace)) :
    some (future.state.getCode pair).toList = pairSem.image ∧
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.Authentic burnAuth pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        SourceReplay (initializedState factory domain token0 token1)
          (steps.map PairStep.source) finish ∧
        runSourceInvocations (initializedState factory domain token0 token1)
          (steps.map PairStep.source) = some finish ∧
        (∀ k, K' k → k ∈ pairHistoryTouchedKeys pair trace) ∧
        WriterRep K' (future.state.getStor pair) finish := by
  obtain ⟨code, steps, observed, auth, finish, K', source, realized, _, inside, rep⟩ :=
    pair_history_committed burn trace installed initial fresh
  refine ⟨code, steps, observed, auth, finish, K', source, realized, ?_, rep⟩
  intro k tracked
  rcases inside k tracked with none | row
  · exact none.elim
  · exact row

end Blanc.Lift.UniswapV2Pair
