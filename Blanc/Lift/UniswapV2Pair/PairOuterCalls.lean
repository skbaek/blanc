import Blanc.Lift.UniswapV2Pair.PairPositionalState
import Blanc.ExecutionSettledOwnCode
import Blanc.ExecutionHistoryFrameTime

/-!
# The Pair's outer calls and their stored words

An *outer Pair call* of a configured history (`OuterPairCall`) is a settled (hence committed),
non-static frame at the Pair that no earlier settled non-static Pair frame encloses: the Pair is
unlocked when it starts.  `pair_history_outer_call` gives, for every outer call `f`:

* model states `st` and `st'` represented by the Pair storage at `f`'s entry and at its committed
  exit (`WriterRep`);
* an authenticated step `s` with `s.frame = f` whose source invocation is consumed from `st` to
  `st'`, returning `f`'s actual output;
* steps observing exactly the settled frames before `f` that replay from the checkpoint's model
  state to `st`, so the outer call's step extends that replay.

No alignment of prefix replays with the whole-history replay is needed: the step of `f` is the
supply's own outcome at `f`, applied to the positional representation at `f`'s entry.

The word observers (`supplyWord`, `reserve0Word`, `reserve1Word`, `timestampWord`, `price0Word`,
`price1Word`, `kLastWord`) read the Pair storage directly; `WriterRep` identifies each with its
model field (`WriterFixedMatches`).
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-! ## Word observers -/

/-- The Pair's total LP supply word (slot `0`). -/
def supplyWord (s : Stor) : B256 := s.get 0

/-- The Pair's stored reserve of token0 (low 112 bits of slot `8`). -/
def reserve0Word (s : Stor) : B256 := reserve0Read (s.get 8)

/-- The Pair's stored reserve of token1 (middle 112 bits of slot `8`). -/
def reserve1Word (s : Stor) : B256 := reserve1Read (s.get 8)

/-- The Pair's stored last-update timestamp (high 32 bits of slot `8`). -/
def timestampWord (s : Stor) : B256 := reserveTimestampRead (s.get 8)

/-- The Pair's cumulative price of token0 (slot `9`). -/
def price0Word (s : Stor) : B256 := s.get 9

/-- The Pair's cumulative price of token1 (slot `10`). -/
def price1Word (s : Stor) : B256 := s.get 10

/-- The Pair's `kLast` (slot `11`). -/
def kLastWord (s : Stor) : B256 := s.get 11

theorem reserve_lt (r : Fin (2 ^ 112)) : r.val < 2 ^ 256 :=
  Nat.lt_trans r.isLt (Nat.pow_lt_pow_right (by decide) (by decide))

namespace WriterRep

variable {K : WriterKey → Prop} {s : Stor} {st : State}

theorem supplyWord_eq (rep : WriterRep K s st) : supplyWord s = st.totalSupply := rep.fixed.1

theorem reserve0Word_toNat (rep : WriterRep K s st) :
    (reserve0Word s).toNat = st.reserve0.val := by
  rw [reserve0Word, rep.fixed.2.2.2.2.2.1, B256.toNat_toB256_of_lt (reserve_lt st.reserve0)]

theorem reserve1Word_toNat (rep : WriterRep K s st) :
    (reserve1Word s).toNat = st.reserve1.val := by
  rw [reserve1Word, rep.fixed.2.2.2.2.2.2.1, B256.toNat_toB256_of_lt (reserve_lt st.reserve1)]

theorem timestampWord_eq (rep : WriterRep K s st) :
    timestampWord s = st.blockTimestampLast.toB256 := rep.fixed.2.2.2.2.2.2.2.1

theorem price0Word_eq (rep : WriterRep K s st) : price0Word s = st.price0CumulativeLast :=
  rep.fixed.2.2.2.2.2.2.2.2.1

theorem price1Word_eq (rep : WriterRep K s st) : price1Word s = st.price1CumulativeLast :=
  rep.fixed.2.2.2.2.2.2.2.2.2.1

theorem kLastWord_eq (rep : WriterRep K s st) : kLastWord s = st.kLast :=
  rep.fixed.2.2.2.2.2.2.2.2.2.2.1

end WriterRep

/-! ## Outer Pair calls -/

/-- **An outer Pair call** of a history: a settled non-static frame at the Pair that no earlier
settled non-static Pair frame encloses (the position condition of `pair_history_stateAt`). -/
def OuterPairCall {cfg : ChainConfig} {checkpoint future : BlockChain} (pair : Adr)
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (f : Exec.Frame) : Prop :=
  f.sevm.currentTarget = pair ∧ f.sevm.isStatic = false ∧
    ∃ before after : List Exec.Frame, trace.settledFrames = before ++ f :: after ∧
      ∀ A ∈ before, A.Encloses f → ¬ (A.sevm.currentTarget = pair ∧ A.sevm.isStatic = false)

/-- The Pair storage at a frame's entry. -/
def preS (pair : Adr) (f : Exec.Frame) : Stor := f.pre.state.getStor pair

/-- The Pair storage at a frame's committed exit. -/
def postS (pair : Adr) (f : Exec.Frame) : Stor := f.post.state.getStor pair

/-- The Pair runtime spawns only by `CALL`/`STATICCALL`, in the shape `settled_ownCode` takes. -/
theorem pair_ownSpawns (ca : Adr) : OwnSpawns ca code := fun hpc hcode _ fork chain hat => by
  obtain ⟨_, reach, ok⟩ := Blanc.Lift.cursor_of_parentPrefix cert_check hpc hcode fork chain
  rcases ok.exec_call_or_staticcall (Cursor.callOnly_of_reach (by decide +kernel) reach) hat with
    h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- A settled frame of a configured history is an actually entered raw frame root. -/
theorem settled_mem_rawFrames {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) :
    Blanc.Exec.Frame.rootDeriv frame ∈ trace.rawFrames := by
  induction trace with
  | refl => cases member
  | step prior block ih =>
    rcases List.mem_append.mp member with h | h
    · exact List.mem_append_left _ (ih h)
    · exact List.mem_append_right _ (block.mem_rawFrames_of_settled frame h)

/-- **Every outer Pair call is one consumed source step between the represented model states of its
entry and exit storage, extending the replay of the settled frames before it** (by position). -/
theorem pair_history_outer_call_at {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace)) :
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      trace.settledFrames = before ++ f :: after →
      f.sevm.currentTarget = pair → f.sevm.isStatic = false →
      (∀ A ∈ before, A.Encloses f → ¬ (A.sevm.currentTarget = pair ∧ A.sevm.isStatic = false)) →
      ∃ (steps : List PairStep) (s : PairStep) (st st' : State) (out : RunResult)
        (K K' : WriterKey → Prop),
        steps.flatMap (fun s => pairSubtreeFrames pair s.frame) =
          before.flatMap (pairFrameObs pair) ∧
        (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
        PairObservedReplayWith PairAdmittedConsumes st₀ steps st ∧
        s.frame = f ∧ s.AuthenticWith PairEntryAuth pair ∧
        PairAdmittedConsumes (Blanc.Exec.Frame.rootDeriv s.frame)
          (startTyped { state := st, logs := [], updates := [] } s.source.context s.source.entry)
          s.transcript out ∧
        out.status = .success f.post.output ∧ out.frame.current.state = st' ∧
        PairObservedReplayWith PairAdmittedConsumes st₀ (steps ++ [s]) st' ∧
        WriterRep K (preS pair f) st ∧ WriterRep K' (postS pair f) st' := by
  intro before f after split target nonstatic noOpaque
  let U := WriterExtend K₀ (pairHistoryTouchedKeys pair trace)
  have extended : WriterRep U (checkpoint.state.getStor pair) st₀ := initial.extend fresh
  have admitted : trace.FrameAdmitted pair (pairEntry U) :=
    pair_trace_admitted trace (fun k row => Or.inr row)
  have start : (pairSpec U).StateInv pair checkpoint.state :=
    ⟨installed, trivial, ⟨st₀, K₀, fun _ h => Or.inl h, initial⟩⟩
  have supply := pairAdmittedSupply extended.inj extended.apart pairSem pairSem_image
  obtain ⟨frames, replay, observed⟩ :=
    (pairPositionalLadderWith pair supply).configuredHistory_at
      trace admitted start before f after split noOpaque
  change PairReplayWith PairAdmittedConsumes PairEntryAuth pair U
    (checkpoint.state.getStor pair).get frames (f.pre.state.getStor pair).get at replay
  change frames.flatMap (pairSubtreeFrames pair) = before.flatMap (pairFrameObs pair) at observed
  obtain ⟨steps, framesEq, auth, st, K, source, _, inside, s, view, rep⟩ :=
    replay st₀ K₀ (fun _ h => Or.inl h) ⟨_, rfl, initial⟩
  have preRep : WriterRep K (f.pre.state.getStor pair) st :=
    WriterRep.congr (fun k => (congrFun view k).symm) rep
  have member : f ∈ trace.settledFrames := by
    rw [split]
    exact List.mem_append_right _ List.mem_cons_self
  have pairCode : checkpoint.state.getCode pair = code := bytes_eq_of_image installed
  obtain ⟨pairAt, pcZero, fork, runsPair⟩ :=
    trace.settled_ownCode (pairSem.ne_nil rfl) (pairSem.not_delegation rfl) (pair_ownSpawns pair)
      pairCode f member
  have entry : pairEntry U f.sevm f.pre :=
    (trace.frameAdmitted_iff_rawFrames pair _).1 admitted _
      (settled_mem_rawFrames trace f member) target
  rw [← framesEq, List.flatMap_map] at observed
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := f
  dsimp only at pairAt pcZero fork runsPair entry target nonstatic preRep ⊢
  subst pcZero
  cases out with
  | error e => cases committed
  | ok post =>
    obtain ⟨raw, rawEq, good⟩ := pair_frame_raw run entry
    obtain ⟨_, output, representable, _⟩ := entry
    subst target
    obtain ⟨entryE, nested, child, bytes, K', authE, consumed, success, outputEq, _, _, postRep⟩ :=
      supply { state := st, logs := [], updates := [] } [] raw (runsPair rfl) pairAt fork output
        representable trivial good inside preRep
    rw [rawEq] at authE consumed
    have successful : child.status = .success post.output := by rw [success, outputEq]
    let s' : PairStep := ⟨⟨0, sevm, pre, .ok post, run, committed⟩, entryE, nested⟩
    refine ⟨steps, s', st, child.frame.current.state, child, K, K', observed, auth, source, rfl,
      ⟨rfl, committed, rfl, nonstatic, authE⟩, consumed, successful, rfl,
      source.append (.cons consumed successful (.nil _)), preRep, postRep⟩

/-- **Every outer Pair call is one authenticated, consumed source step between model states its entry
and exit storage represent.** -/
theorem pair_history_outer_call {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace)) :
    ∀ f, OuterPairCall pair trace f →
      ∃ (s : PairStep) (st st' : State) (out : RunResult) (K K' : WriterKey → Prop),
        s.frame = f ∧ s.AuthenticWith PairEntryAuth pair ∧
        PairAdmittedConsumes (Blanc.Exec.Frame.rootDeriv s.frame)
          (startTyped { state := st, logs := [], updates := [] } s.source.context s.source.entry)
          s.transcript out ∧
        out.status = .success f.post.output ∧ out.frame.current.state = st' ∧
        WriterRep K (preS pair f) st ∧ WriterRep K' (postS pair f) st' := by
  intro f ⟨target, nonstatic, before, after, split, noOpaque⟩
  obtain ⟨-, s, st, st', out, K, K', -, -, -, frameEq, auth, consumed, success, outEq, -, pre, post⟩ :=
    pair_history_outer_call_at trace installed initial fresh before f after split target nonstatic
      noOpaque
  exact ⟨s, st, st', out, K, K', frameEq, auth, consumed, success, outEq, pre, post⟩

end Blanc.Lift.UniswapV2Pair
