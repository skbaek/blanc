import Blanc.Lift.UniswapV2Pair.PairStepShape
import Blanc.ExecutionPathLocator

/-!
# Walking to the factory query of a `mint` or `burn`

The source program of `mint` and `burn` asks two `balanceOf` reads and then the factory's `feeTo()`.
Along a positional consumption (`PositionalConsumes`) of such an entry:

* `FeeLead` is the model shape before each of the first three answers; the first two requests are
  static (so their turns keep the frame, `ExactTurns.static_frame`), the third goes to the
  checkpoint's factory;
* `PositionalConsumes.suspended_inv` advances one answer, splitting the frame's located descendants
  into those entered by that call (paths below its spawn index) and those after it.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc

/-! ## Call-tree paths -/

/-- Every located descendant lies below the parent path it is collected under. -/
theorem descendantFramePaths_prefix (p : List Nat) (k : Nat) {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) :
    ∀ c ∈ Exec.descendantFramePaths p k run, p <+: c.path := by
  induction run generalizing p k with
  | halt => intro c member; simp only [Exec.descendantFramePaths, List.not_mem_nil] at member
  | cont _ _ ih =>
    intro c member
    simp only [Exec.descendantFramePaths] at member
    exact ih p k c member
  | doneErr => intro c member; simp only [Exec.descendantFramePaths, List.not_mem_nil] at member
  | doneOk _ _ _ _ ih =>
    intro c member
    simp only [Exec.descendantFramePaths] at member
    exact ih p (k + 1) c member
  | runErr => intro c member; simp only [Exec.descendantFramePaths, List.not_mem_nil] at member
  | runOk _ _ _ _ _ childIh nextIh =>
    intro c member
    simp only [Exec.descendantFramePaths, List.mem_append] at member
    rcases member with inChild | inNext
    · split at inChild
      · rcases List.mem_cons.mp inChild with rfl | deeper
        · exact List.prefix_append p [k]
        · exact (List.prefix_append p [k]).trans (childIh (p ++ [k]) 0 c deeper)
      · cases inChild
    · exact nextIh p (k + 1) c inNext

/-- A spawning parent edge contributes, at its index, only frames below that index. -/
theorem ParentStep.descendantFramePaths_spawn_head {F N : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep N F) {frame : Jaune.Frame} {resume : Resume} {pc : Nat}
    (spawned : Evm.step ⟨F.pc, F.sevm, F.devm⟩ = .spawn frame resume pc) (index : Nat) :
    ∃ C : List Exec.LocatedFrame,
      Exec.descendantFramePaths [] index F.exc =
        C ++ Exec.descendantFramePaths [] (index + 1) N.exc ∧ ∀ c ∈ C, [index] <+: c.path := by
  cases edge with
  | cont hstep next =>
    have impossible := hstep.symm.trans spawned
    cases impossible
  | doneOk hstep henter hresume next =>
    exact ⟨[], by simp only [Exec.descendantFramePaths, List.nil_append],
      fun c member => by cases member⟩
  | runOk hstep henter child hresume next =>
    refine ⟨_, by rw [Exec.descendantFramePaths], fun c member => ?_⟩
    split at member
    · rcases List.mem_cons.mp member with rfl | deeper
      · exact List.prefix_refl _
      · exact descendantFramePaths_prefix ([] ++ [index]) 0 child c deeper
    · cases member

/-! ## One answer along a positional consumption -/

/-- A failed segment is consumed to a failed status. -/
theorem PositionalConsumes.failed_status {root start : Exec.Deriv} {index : Nat} {fr : Frame}
    {failure : Failure} {transcript : Transcript} {out : RunResult}
    (consumed : PositionalConsumes root start index (.failed fr failure) transcript out) :
    out.status = .failed failure := by
  cases consumed
  rfl

/-- **One answer of a suspended segment**: the transcript's next reply is observed at the actual
call `observed` of index `index`, whose entered frames are the located descendants below `index`;
the rest is consumed from the resumed segment, with a static request resuming the same frame. -/
theorem PositionalConsumes.suspended_inv {root start : Exec.Deriv} {index : Nat} {frame : Frame}
    {request : Request} {continuation : Continuation} {transcript : Transcript} {out : RunResult}
    (consumed : PositionalConsumes root start index (.suspended frame request continuation)
      transcript out) :
    ∃ (reply : ExternalResult) (turns tail : Transcript)
      (observed : SourceCallAt root frame request reply index) (prior : Frame) (out' : RunResult)
      (C : List Exec.LocatedFrame),
      transcript = .next reply turns tail ∧
      Exec.Deriv.ExecFreeUntil start observed.call.occurrence.node ∧
      Exec.descendantFramePaths [] index start.exc =
        C ++ Exec.descendantFramePaths [] (index + 1) observed.call.returned.exc ∧
      (∀ c ∈ C, [index] <+: c.path) ∧
      (externalStatic frame request = true → prior = frame) ∧
      PositionalConsumes root observed.call.returned (index + 1)
        (resumeSegment prior request continuation reply) tail out' ∧
      out.status = out'.status := by
  have split {reply : ExternalResult} (observed : SourceCallAt root frame request reply index)
      (gap : Exec.Deriv.ExecFreeUntil start observed.call.occurrence.node) :
      ∃ C : List Exec.LocatedFrame,
        Exec.descendantFramePaths [] index start.exc =
          C ++ Exec.descendantFramePaths [] (index + 1) observed.call.returned.exc ∧
        ∀ c ∈ C, [index] <+: c.path := by
    rw [gap.descendantFramePaths_eq]
    exact ParentStep.descendantFramePaths_spawn_head observed.call.edge observed.spawned index
  cases consumed with
  | nextCall observed gap present noCodeTurns during rest =>
    obtain ⟨C, eq, below⟩ := split observed gap
    refine ⟨_, _, _, observed, _, _, C, rfl, gap, eq, below, fun static => ?_, rest, rfl⟩
    have kept := during.forget.static_frame (Or.inl static)
    split <;> rw [kept]
  | nextMutableCall observed gap queue present noCodeTurns during rest =>
    obtain ⟨C, eq, below⟩ := split observed gap
    refine ⟨_, _, _, observed, _, _, C, rfl, gap, eq, below, fun static => ?_, rest, rfl⟩
    have kept := during.forget.static_frame (Or.inl static)
    split <;> rw [kept]

/-! ## The model's way to the factory query -/

/-- The shape of a `mint`/`burn` segment before its answer number `0`, `1`, `2`: failed, or
suspended at the two static balance reads (frame state keeping the factory) and then at the
factory's `feeTo()`. -/
def FeeLead (factory : Adr) : Nat → SegmentResult → Prop
  | _, .finished _ _ => False
  | _, .failed _ _ => True
  | 0, .suspended fr request c =>
    fr.current.state.factory = factory ∧ request.kind = .staticCall ∧
      ((∃ recipient reserves, c = .mintBalance0 recipient reserves) ∨
        ∃ locals, c = .burnInitialBalance0 locals)
  | 1, .suspended fr request c =>
    fr.current.state.factory = factory ∧ request.kind = .staticCall ∧
      ((∃ recipient reserves balance0, c = .mintBalance1 recipient reserves balance0) ∨
        ∃ locals balance0, c = .burnInitialBalance1 locals balance0)
  | _ + 2, .suspended _ request c =>
    request.target = factory ∧ request.operation = .feeTo ∧
      ((∃ observed, c = .mintFee observed) ∨ ∃ observed, c = .burnFee observed)

theorem startTyped_feeLead (current : Checkpoint) (ctx : Context) {entry : Entry}
    (fee : (∃ recipient, entry = .mint recipient) ∨ ∃ recipient, entry = .burn recipient) :
    FeeLead current.state.factory 0 (startTyped current ctx entry) := by
  rcases fee with ⟨recipient, rfl⟩ | ⟨recipient, rfl⟩ <;>
  · unfold startTyped startImmediate
    by_cases value : ctx.value ≠ 0
    · simp only [FeeLead, ne_eq, value, not_false_eq_true, ↓reduceIte, Frame.fail]
    · simp only [value, ↓reduceIte, getterResult]
      unfold Frame.lock
      split_ifs <;>
        simp only [FeeLead, Frame.fail, Frame.suspend, Frame.enter, requestFor,
          Continuation.mintBalance0.injEq, Continuation.burnInitialBalance0.injEq, exists_and_left,
          ↓existsAndEq, and_true, exists_eq', reduceCtorEq, exists_false, or_false, or_true,
          and_self]

theorem resumeSegment_feeLead_zero {factory : Adr} {fr : Frame} {request : Request}
    {c : Continuation} (lead : FeeLead factory 0 (.suspended fr request c))
    (reply : ExternalResult) : FeeLead factory 1 (resumeSegment fr request c reply) := by
  obtain ⟨factoryEq, -, shape⟩ := lead
  unfold resumeSegment
  split
  · simp only [Frame.fail, FeeLead]
  · rename_i decoded _
    rcases shape with ⟨recipient, reserves, rfl⟩ | ⟨locals, rfl⟩ <;> cases decoded <;>
      simp only [FeeLead, Frame.fail, Frame.suspend, Frame.beginResume, requestFor, factoryEq,
        Continuation.mintBalance1.injEq, Continuation.burnInitialBalance1.injEq, exists_and_left,
        ↓existsAndEq, and_true, exists_eq', reduceCtorEq, exists_const, exists_false, or_false,
        or_true, and_self]

theorem resumeSegment_feeLead_one {factory : Adr} {fr : Frame} {request : Request}
    {c : Continuation} (lead : FeeLead factory 1 (.suspended fr request c))
    (reply : ExternalResult) : FeeLead factory 2 (resumeSegment fr request c reply) := by
  obtain ⟨factoryEq, -, shape⟩ := lead
  unfold resumeSegment
  split
  · simp only [Frame.fail, FeeLead]
  · rename_i decoded _
    rcases shape with ⟨recipient, reserves, balance0, rfl⟩ | ⟨locals, balance0, rfl⟩ <;>
      cases decoded <;>
      simp only [Frame.fail, Frame.suspend, Frame.beginResume, requestFor, FeeLead, factoryEq]
    all_goals (try split_ifs) <;> simp only [Nat.reducePow, Continuation.mintFee.injEq,
      Continuation.burnFee.injEq, exists_eq', reduceCtorEq, exists_false, or_false, or_true, and_self]

/-- An unsuccessful factory answer fails the segment. -/
theorem resumeSegment_feeLead_two_failed {factory : Adr} {fr : Frame} {request : Request}
    {c : Continuation} (lead : FeeLead factory 2 (.suspended fr request c))
    {reply : ExternalResult} (unsuccessful : reply.success = false) :
    ∃ fr' failure, resumeSegment fr request c reply = .failed fr' failure := by
  obtain ⟨-, operation, -⟩ := lead
  have decoded : ∃ failure, decodeExternal request reply = .error failure := by
    unfold decodeExternal
    split
    · exact ⟨_, rfl⟩
    · simp only [operation, unsuccessful, Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, rfl⟩
  obtain ⟨failure, decodedEq⟩ := decoded
  unfold resumeSegment
  simp only [decodedEq, Frame.fail]
  exact ⟨_, _, rfl⟩

end Blanc.Lift.UniswapV2Pair
