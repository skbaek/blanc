import Blanc.Lift.UniswapV2Pair.PairStepShape
import Blanc.Lift.UniswapV2Pair.PairPositionalState
import Blanc.Lift.UniswapV2Pair.PairHistoryLive

/-!
# The Pair's fixed tokens, lock and call shape over a configured history

Under H1 (no settled non-static Pair frame of the history is called by the stored factory; amendment
A3, reserved for the user and carried as an explicit hypothesis), from a checkpoint whose Pair model
state is unlocked:

* `PairObservedReplayWith.fixed`: every step of an observed Pair replay keeps the token addresses,
  the factory and the open lock, and each step is consumed from an incoming state that has them;
* `pair_history_stateAt_fixed`: at every settled frame outside the Pair's own non-static frames, the
  Pair storage represents an unlocked model state with the checkpoint's tokens and factory;
* `PairHistoryReplayed.fixed`: the same at the history's end;
* `pair_history_mutable_children`: every mutable direct child of every settled non-static Pair frame
  is a `transfer` request to one of the two tokens or a callback to a non-token address
  (`ShapedChild`); re-entered Pair frames have no mutable child.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- Every non-static Pair frame of a step's subtree is one of the given frames. -/
theorem factoryQuiet_of_subtree {f pair : Adr} {frames : List Exec.Frame} {s : PairStep}
    (inFrames : ∀ D ∈ pairSubtreeFrames pair s.frame, D ∈ frames)
    (quiet : FactoryQuiet f pair frames) : FactoryQuiet f pair (Exec.committedFrames s.frame.run) := by
  intro D member atPair mutable
  apply quiet D _ atPair mutable
  apply inFrames
  refine List.mem_flatMap.mpr ⟨D, member, ?_⟩
  rw [pairFrameObs, ite_eq_left_of_eq_true _ _ (eq_true ⟨atPair, mutable⟩)]
  exact List.mem_singleton_self D

/-- **One consumed outer step from an unlocked state with the tokens and factory fixed.** -/
theorem PairStep.consumedFix {t0 t1 f pair : Adr} {s : PairStep} {current : Checkpoint}
    {out : RunResult}
    (consumed : PairAdmittedConsumes (Blanc.Exec.Frame.rootDeriv s.frame)
      (startTyped current s.source.context s.source.entry) s.transcript out)
    (target : s.frame.sevm.currentTarget = pair)
    (quiet : FactoryQuiet f pair (Exec.committedFrames s.frame.run))
    (tokens : TokensFix t0 t1 f current.state) (opened : current.state.unlocked = 1) :
    ConsumedFix false t0 t1 f (Blanc.Exec.Frame.rootDeriv s.frame)
      (Blanc.Exec.Frame.rootDeriv s.frame) out := by
  have inv := startTyped_segInv_outer (current := current) (ctx := s.source.context)
    (entry := s.source.entry) tokens opened (fun static =>
      quiet s.frame (Exec.Frame.mem_committedFrames.mpr (Or.inl rfl)) target static)
  apply consumed.positional.segInv inv
  intro D member atRoot mutable
  exact quiet D (Exec.Frame.mem_committedFrames.mpr (Or.inr member)) (atRoot.trans target) mutable

/-- **An observed Pair replay keeps the tokens, the factory and the open lock**, and consumes each
step from an incoming state that has them. -/
theorem PairObservedReplayWith.fixed {t0 t1 f pair : Adr} {st st' : State} {steps : List PairStep}
    (replay : PairObservedReplayWith PairAdmittedConsumes st steps st')
    (auth : ∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair)
    (quiet : ∀ s ∈ steps, FactoryQuiet f pair (Exec.committedFrames s.frame.run))
    (tokens : TokensFix t0 t1 f st) (opened : st.unlocked = 1) :
    TokensFix t0 t1 f st' ∧ st'.unlocked = 1 ∧
      ∀ s ∈ steps, ∃ (current : Checkpoint) (out : RunResult),
        PairAdmittedConsumes (Blanc.Exec.Frame.rootDeriv s.frame)
          (startTyped current s.source.context s.source.entry) s.transcript out ∧
        TokensFix t0 t1 f current.state ∧ current.state.unlocked = 1 := by
  induction replay with
  | nil st => exact ⟨tokens, opened, fun _ member => by cases member⟩
  | @cons st finish s rest out consumed successful tail ih =>
    obtain ⟨outFix, outOpen, -, -⟩ := PairStep.consumedFix consumed
      (auth s List.mem_cons_self).2.2.1 (quiet s List.mem_cons_self) tokens opened
    obtain ⟨tailTokens, tailOpen, tailSteps⟩ :=
      ih (fun s' member => auth s' (List.mem_cons_of_mem _ member))
        (fun s' member => quiet s' (List.mem_cons_of_mem _ member)) outFix.1
        (outOpen rfl _ successful)
    refine ⟨tailTokens, tailOpen, fun s' member => ?_⟩
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨_, _, consumed, tokens, opened⟩
    · exact tailSteps s' later

/-- A non-static Pair frame of a step's subtree is a settled frame when the observation is. -/
theorem mem_of_pairSubtree {pair : Adr} {steps : List PairStep} {frames settled : List Exec.Frame}
    (observed : steps.flatMap (fun s => pairSubtreeFrames pair s.frame) =
      frames.flatMap (pairFrameObs pair))
    (sub : ∀ F ∈ frames, F ∈ settled) :
    ∀ s ∈ steps, ∀ D ∈ pairSubtreeFrames pair s.frame, D ∈ settled := by
  intro s member D inSubtree
  have inObserved : D ∈ frames.flatMap (pairFrameObs pair) := by
    rw [← observed]
    exact List.mem_flatMap.mpr ⟨s, member, inSubtree⟩
  obtain ⟨F, inFrames, obs⟩ := List.mem_flatMap.mp inObserved
  unfold pairFrameObs at obs
  split at obs
  · rw [List.mem_singleton.mp obs]
    exact sub F inFrames
  · cases obs

/-- `pair_history_stateAt`, keeping the authentication of the prefix steps. -/
theorem pair_history_stateAt_auth {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace)) :
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      trace.settledFrames = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ (A.sevm.currentTarget = pair ∧ A.sevm.isStatic = false)) →
      ∃ (steps : List PairStep) (st : State) (K : WriterKey → Prop),
        steps.flatMap (fun s => pairSubtreeFrames pair s.frame) =
          before.flatMap (pairFrameObs pair) ∧
        (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
        PairObservedReplayWith PairAdmittedConsumes st₀ steps st ∧
        WriterRep K (f.pre.state.getStor pair) st := by
  intro before f after split noOpaque
  let U := WriterExtend K₀ (pairHistoryTouchedKeys pair trace)
  have extended : WriterRep U (checkpoint.state.getStor pair) st₀ := initial.extend fresh
  have admitted : trace.FrameAdmitted pair (pairEntry U) :=
    pair_trace_admitted trace (fun k row => Or.inr row)
  have start : (pairSpec U).StateInv pair checkpoint.state :=
    ⟨installed, trivial, ⟨st₀, K₀, fun _ h => Or.inl h, initial⟩⟩
  obtain ⟨frames, replay, observed⟩ :=
    (pairPositionalLadderWith pair
      (pairAdmittedSupply extended.inj extended.apart pairSem pairSem_image)).configuredHistory_at
      trace admitted start before f after split noOpaque
  change PairReplayWith PairAdmittedConsumes PairEntryAuth pair U
    (checkpoint.state.getStor pair).get frames (f.pre.state.getStor pair).get at replay
  change frames.flatMap (pairSubtreeFrames pair) = before.flatMap (pairFrameObs pair) at observed
  obtain ⟨steps, framesEq, auth, st, K, source, _, _, s, view, rep⟩ :=
    replay st₀ K₀ (fun _ h => Or.inl h) ⟨_, rfl, initial⟩
  refine ⟨steps, st, K, ?_, auth, source, WriterRep.congr (fun k => (congrFun view k).symm) rep⟩
  rw [← framesEq, List.flatMap_map] at observed
  exact observed

/-- **The Pair is unlocked with its checkpoint tokens and factory at every unlocked position**
(under H1). -/
theorem pair_history_stateAt_fixed {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (unlocked : st₀.unlocked = 1)
    (factoryQuiet : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → G.sevm.caller ≠ st₀.factory) :
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      trace.settledFrames = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ (A.sevm.currentTarget = pair ∧ A.sevm.isStatic = false)) →
      ∃ (st : State) (K : WriterKey → Prop), WriterRep K (f.pre.state.getStor pair) st ∧
        st.unlocked = 1 ∧ TokensFix st₀.token0 st₀.token1 st₀.factory st := by
  intro before f after split noOpaque
  obtain ⟨steps, st, K, observed, auth, replay, rep⟩ :=
    pair_history_stateAt_auth trace installed initial fresh before f after split noOpaque
  have inSettled := mem_of_pairSubtree observed (settled := trace.settledFrames) (fun F member => by
    rw [split]
    exact List.mem_append_left _ member)
  obtain ⟨tokens, opened, -⟩ := replay.fixed auth
    (fun s member => factoryQuiet_of_subtree (inSettled s member) factoryQuiet)
    ⟨rfl, rfl, rfl⟩ unlocked
  exact ⟨st, K, rep, opened, tokens⟩

/-- **At the history's end the Pair is unlocked with its checkpoint tokens and factory** (under
H1). -/
theorem PairHistoryReplayed.fixed {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ K' : WriterKey → Prop} {st₀ finish : State}
    {trace : ConfiguredHistoryTrace cfg checkpoint future}
    (replayed : PairHistoryReplayed pair trace K₀ st₀ finish K')
    (unlocked : st₀.unlocked = 1)
    (factoryQuiet : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → G.sevm.caller ≠ st₀.factory) :
    finish.unlocked = 1 ∧ TokensFix st₀.token0 st₀.token1 st₀.factory finish := by
  obtain ⟨steps, observed, auth, replay, -⟩ := replayed
  have inSettled := mem_of_pairSubtree observed (settled := trace.settledFrames) (fun F member => member)
  obtain ⟨tokens, opened, -⟩ := replay.fixed auth
    (fun s member => factoryQuiet_of_subtree (inSettled s member) factoryQuiet)
    ⟨rfl, rfl, rfl⟩ unlocked
  exact ⟨opened, tokens⟩

/-- **Every mutable child of a settled non-static Pair frame has the outer shape** (under H1):
a `transfer` request to one of the checkpoint's two tokens, or a callback to a non-token address.
Re-entered Pair frames have no mutable child at all. -/
theorem pair_history_mutable_children {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (unlocked : st₀.unlocked = 1)
    (factoryQuiet : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → G.sevm.caller ≠ st₀.factory) :
    ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair → G.sevm.isStatic = false →
      ∀ c ∈ Exec.childFrames G.run, c.sevm.isStatic = false →
        ShapedChild st₀.token0 st₀.token1 pair c := by
  intro G settled atPair mutableG c child mutable
  obtain ⟨-, steps, observedEq, auth, finish, K', replay, -⟩ :=
    pair_history_committed trace installed initial fresh
  have inSettled := mem_of_pairSubtree observedEq (settled := trace.settledFrames)
    (fun F member => member)
  have quiet : ∀ s ∈ steps, FactoryQuiet st₀.factory pair (Exec.committedFrames s.frame.run) :=
    fun s member => factoryQuiet_of_subtree (inSettled s member) factoryQuiet
  obtain ⟨-, -, consumedSteps⟩ := replay.fixed auth quiet ⟨rfl, rfl, rfl⟩ unlocked
  have inPair : G ∈ committedPairFrames pair trace := by
    refine List.mem_flatMap.mpr ⟨G, settled, ?_⟩
    rw [pairFrameObs, ite_eq_left_of_eq_true _ _ (eq_true ⟨atPair, mutableG⟩)]
    exact List.mem_singleton_self G
  rw [← observedEq] at inPair
  obtain ⟨s, stepMem, inSubtree⟩ := List.mem_flatMap.mp inPair
  obtain ⟨F, frameMem, obs⟩ := List.mem_flatMap.mp inSubtree
  have sameF : G = F := by
    unfold pairFrameObs at obs
    split at obs
    · exact List.mem_singleton.mp obs
    · cases obs
  subst sameF
  have target : s.frame.sevm.currentTarget = pair := (auth s stepMem).2.2.1
  obtain ⟨current, out, consumed, tokens, opened⟩ := consumedSteps s stepMem
  obtain ⟨-, -, children, locked⟩ :=
    PairStep.consumedFix consumed target (quiet s stepMem) tokens opened
  rcases Exec.Frame.mem_committedFrames.mp frameMem with rfl | deeper
  · obtain ⟨-, shaped⟩ := children c child mutable
    rw [← target]
    exact shaped
  · rw [locked G deeper (atPair.trans target.symm) mutableG c child] at mutable
    cases mutable

/-! ## Reading a shaped child -/

theorem transfer_encode_eq (recipient : Adr) (value : B256) :
    (ExternalOperation.transfer recipient value).encode =
      [0xa9, 0x05, 0x9c, 0xbb] ++ (recipient.toB256.toBytes ++ value.toBytes) := by
  simp only [ExternalOperation.encode, encodeWords, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- A `transfer` request's calldata is 68 bytes. -/
theorem transfer_encode_length (recipient : Adr) (value : B256) :
    (ExternalOperation.transfer recipient value).encode.length = 68 := by
  rw [transfer_encode_eq]
  simp only [List.length_append, B256.length_toBytes, List.length_cons, List.length_nil]

/-- A `transfer` request's calldata names its recipient and amount at words 4 and 36. -/
theorem transfer_encode_words {sevm : Sevm} {recipient : Adr} {value : B256}
    (data : sevm.data = (ExternalOperation.transfer recipient value).encode) :
    Sevm.dataWord sevm 4 = recipient.toB256 ∧ Sevm.dataWord sevm 36 = value := by
  have rLen : recipient.toB256.toBytes.length = 32 := B256.length_toBytes _
  have vLen : value.toBytes.length = 32 := B256.length_toBytes _
  rw [transfer_encode_eq] at data
  have restLen : (recipient.toB256.toBytes ++ value.toBytes).length = 64 := by
    rw [List.length_append, rLen, vLen]
  have dropFour : List.drop 4 sevm.data = recipient.toB256.toBytes ++ value.toBytes := by
    rw [data]
    rfl
  have dropMore : List.drop 36 sevm.data = value.toBytes := by
    rw [show (36 : Nat) = 4 + 32 from rfl, ← List.drop_drop, dropFour,
      List.drop_left' rLen]
  constructor
  · unfold Sevm.dataWord List.sliceD
    rw [show (4 : B256).toNat = 4 from rfl, dropFour,
      List.takeD_eq_take 0 (by rw [restLen]; omega), List.take_left' rLen,
      B256.toB256_toBytes]
  · unfold Sevm.dataWord List.sliceD
    rw [show (36 : B256).toNat = 36 from rfl, dropMore, List.takeD_eq_self 0 vLen.symm,
      B256.toB256_toBytes]

/-- **What a shaped child is.**  Either a `transfer` to one of the two tokens, with 68-byte
calldata naming its recipient and amount, or a callback to a non-token address. -/
theorem ShapedChild.cases {t0 t1 pair : Adr} {c : Exec.Frame} (shaped : ShapedChild t0 t1 pair c) :
    c.sevm.caller = pair ∧
      (((c.sevm.currentTarget = t0 ∨ c.sevm.currentTarget = t1) ∧
          ∃ recipient value, c.sevm.data = (ExternalOperation.transfer recipient value).encode) ∨
        (Blanc.Sevm.selector c.sevm = 0x10d1e85c ∧ c.sevm.currentTarget ≠ t0 ∧
          c.sevm.currentTarget ≠ t1)) := by
  obtain ⟨request, reqShape, target, caller, data⟩ := shaped
  refine ⟨caller, ?_⟩
  rcases reqShape with ⟨site, recipient, value, rfl | rfl⟩ |
    ⟨site, callee, sender, amount0, amount1, bytes, rfl, apart0, apart1⟩
  · exact Or.inl ⟨Or.inl target, recipient, value, data⟩
  · exact Or.inl ⟨Or.inr target, recipient, value, data⟩
  · refine Or.inr ⟨?_, target ▸ apart0, target ▸ apart1⟩
    rw [Blanc.Sevm.selector_eq_toB256_takeD_four, data]
    simp only [requestFor, ExternalOperation.encode, List.cons_append, List.takeD, List.headD_cons,
      List.tail_cons]
    rfl

end Blanc.Lift.UniswapV2Pair
