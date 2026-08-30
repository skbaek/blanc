import Blanc.ExecutionNoninterference

/-!
# Account-level protocol for a pinned pause target

This shared module describes observable account behaviour, not a particular
contract family.  The `program` parameter is deliberately only an index of the
bundle.  `ProgramInstalledAt` records direct installation, while
`MessageExecutesProgram` records code identity on one actual retained message
invocation.  The Lido specialization supplies a detachable boundary-scoped
hook connecting those two levels; a later proxy composition can establish the
same hook through proxy/implementation correspondence.

The storage-safety field is semantic.  It excludes retained successful writes
to selected owner/key pairs throughout the invocation frame closure; it does
not require the target to be childless.  `Exec.noRetainedWriteTo_of_no_execOccurrence`
is merely one sufficient route for direct call-free programs.
-/

namespace Blanc

open Jaune

/-- The result type settled by one message call frame. -/
abbrev TargetMessageResult : Type :=
  Except (EvmError × State × AdrSet × Tra) Devm

/-- One exact zero-value account call.  These are the account-level fields
fixed by the CircuitBreaker's CALL and STATICCALL boundaries. -/
structure ExactTargetCall (caller target : Adr) (calldata : Bytes)
    (static : Bool) (msg : Msg) : Prop where
  currentTarget : msg.currentTarget = target
  targetAddress : msg.target = some target
  codeAddress : msg.codeAddress = some target
  callerAddress : msg.caller = caller
  valueZero : msg.value = 0
  transfer : msg.shouldTransferValue = true
  staticFlag : msg.isStatic = static
  data : msg.data = calldata

/-- A single detachable direct-installation fact.  By itself it does not say
that a later message actually executed the installed code. -/
def ProgramInstalledAt (state : State) (target : Adr) (program : Prog) : Prop :=
  some (state.getCode target).toList = Prog.compile program

/-- The message carries the bundle's indexed code. -/
def MessageUsesProgram (msg : Msg) (program : Prog) : Prop :=
  some msg.code.toList = Prog.compile program

/-- The settled message really entered a retained code frame carrying the
indexed program.  The explicit nonempty slot excludes the precompile/no-frame
path, on which `Xlot.Filled .none` alone would be vacuous. -/
def MessageExecutesProgram
    (msg : Msg) (xl : Xlot) (program : Prog) : Prop :=
  MessageUsesProgram msg program ∧
    ∃ (evm : Evm) (raw : Execution),
      xl = .some ⟨evm, raw⟩ ∧
      Nonempty (Exec evm.pc evm.sta evm.dyna raw)

/-- The ABI acceptance rule used by the CircuitBreaker: at least one full
word, with trailing bytes ignored. -/
def AcceptedBoolWord (child : Devm) (word : B256) : Prop :=
  child.error.isSome = false ∧
    32 ≤ child.output.length ∧
    Bytes.toB256 (child.output.sliceD 0 32 0) = word

/-- Every settled answer that is neither accepted canonical false nor
accepted canonical true.  This includes a callee error, a short return, and a
non-boolean first word. -/
def BoolQueryFailure (child : Devm) : Prop :=
  ¬ AcceptedBoolWord child 0 ∧ ¬ AcceptedBoolWord child 1

/-- A whole settled account invocation returned an accepted boolean word. -/
def AcceptedBoolExecution (ex : TargetMessageResult) (word : B256) : Prop :=
  ∃ child, ex = .ok child ∧ AcceptedBoolWord child word

/-- A whole settled account invocation returned neither accepted boolean word. -/
def BoolQueryExecutionFailure (ex : TargetMessageResult) : Prop :=
  ¬ AcceptedBoolExecution ex 0 ∧ ¬ AcceptedBoolExecution ex 1

/-- A clean full-word output is accepted exactly at the word it encodes.
This is the shared account-boundary adapter from raw output equality to the
`AcceptedBoolWord` protocol; contract families should not repeat its byte
slice normalization. -/
theorem acceptedBoolWord_iff_of_output
    {post : Devm} {word result : B256}
    (errorClean : post.error = none)
    (outputEq : post.output = word.toBytes) :
    AcceptedBoolWord post result ↔ word = result := by
  have sliceEq : word.toBytes.sliceD 0 word.toBytes.length 0 =
      word.toBytes := by
    simpa [Bytes.writeAt] using
      (Bytes.sliceD_writeAt ([] : Bytes) word.toBytes 0)
  have headEq : Bytes.toB256 (post.output.sliceD 0 32 0) = word := by
    rw [outputEq,
      show (32 : Nat) = word.toBytes.length from
        (B256.length_toBytes word).symm,
      sliceEq, B256.toB256_toBytes]
  constructor
  · intro accepted
    exact headEq.symm.trans accepted.2.2
  · intro wordEq
    refine ⟨?_, ?_, ?_⟩
    · rw [errorClean]
      rfl
    · rw [outputEq, B256.length_toBytes]
    · exact headEq.trans wordEq

/-- At a successful settled result, whole-execution boolean acceptance is
exactly acceptance of the returned child. -/
theorem acceptedBoolExecution_ok_iff (post : Devm) (word : B256) :
    AcceptedBoolExecution (.ok post) word ↔ AcceptedBoolWord post word := by
  constructor
  · rintro ⟨child, childEq, accepted⟩
    cases childEq
    exact accepted
  · intro accepted
    exact ⟨post, rfl, accepted⟩

/-- The execution-level rejected-boolean predicate specializes to the
underlying successful child's rejected-boolean predicate. -/
theorem boolQueryExecutionFailure_ok_iff (post : Devm) :
    BoolQueryExecutionFailure (.ok post) ↔ BoolQueryFailure post := by
  unfold BoolQueryExecutionFailure BoolQueryFailure
  rw [acceptedBoolExecution_ok_iff, acceptedBoolExecution_ok_iff]

/-- A settled code result that was not cut short by an exceptional halt.  The
two cases deliberately leave ordinary clean completion open; a protected-
surface safety law may then rule that case out without promising enough gas to
reach `REVERT`. -/
def SettledNormallyOrReverted (child : Devm) : Prop :=
  child.error = none ∨ child.error = some .revert

/-- The account is paused exactly when the entry timestamp precedes its
storage-local paused-until projection. -/
def PausedAt (pausedUntil : Adr → Stor → B256)
    (state : State) (target : Adr) (timestamp : B256) : Prop :=
  timestamp < pausedUntil target (state.getStor target)

/-- The all-ones duration requests an unbounded pause.  Every other duration
is measured from the current block timestamp, matching Lido's public pause
protocol without making the shared target bundle Lido-specific. -/
def pauseInfiniteSentinel : B256 := B256.max

def pauseForProjection (time duration : B256) : B256 :=
  if duration = pauseInfiniteSentinel then pauseInfiniteSentinel
  else time + duration

/-- The branch-free encoding of `pauseForProjection`: multiplying the timestamp
by the negated sentinel test selects the sentinel arm without a jump.  This
identity supports branch-free implementations and executable test stubs; a
faithful port may instead branch explicitly between the two projection arms. -/
theorem compact_pause_word_eq_projection (time duration : B256) :
    time * (((pauseInfiniteSentinel =? duration) =? 0)) + duration =
      pauseForProjection time duration := by
  by_cases infinite : duration = pauseInfiniteSentinel
  · subst duration
    have one_ne_zero : (1 : B256) ≠ 0 := by decide
    simp [pauseForProjection, B256.eqCheck, one_ne_zero]
    have mulZero : time * (0 : B256) = 0 := by
      change (time.toNat * 0).toB256 = 0
      rw [Nat.mul_zero]
      rfl
    rw [mulZero]
    rfl
  · have reverse : pauseInfiniteSentinel ≠ duration := Ne.symm infinite
    simp [pauseForProjection, B256.eqCheck, infinite, reverse]
    have mulOne : time * (1 : B256) = time := by
      change (time.toNat * 1).toB256 = time
      rw [Nat.mul_one]
      exact toB256_toNat time
    rw [mulOne]

/-- Calldata has the selected ABI function selector and an arbitrary tail. -/
def HasSelector (msg : Msg) (selected : B256) : Prop :=
  ∃ tail, msg.data = abiSelectorBytes selected ++ tail

/-- The two exact inbound calls in a pause choreography. -/
def ExactPinnedInbound (circuitBreaker target : Adr)
    (pauseCalldata : B256 → Bytes) (queryCalldata : Bytes)
    (msg : Msg) : Prop :=
  (∃ duration,
      ExactTargetCall circuitBreaker target (pauseCalldata duration) false msg) ∨
    ExactTargetCall circuitBreaker target queryCalldata true msg

/-- No retained successful write in an actual message slot targets one
selected account cell.  A no-frame slot contributes no code-frame write. -/
def TargetInvocationNoRetainedWriteTo
    (xl : Xlot) (owner : Adr) (key : B256) : Prop :=
  match xl with
  | .none => True
  | .some ⟨evm, raw⟩ =>
      ∀ run : Exec evm.pc evm.sta evm.dyna raw,
        Exec.NoRetainedWriteTo run owner key

/-- A target-agnostic account protocol for pause composition.

The fields say only what the account at `target` does on exact settled inbound
messages.  They do not expose or unfold `program`.  The paused projection is
intrinsically local to one account's `Stor`, so unrelated account changes
cannot alter its observation. -/
structure PinnedPauseTarget
    (circuitBreaker target : Adr) (program : Prog)
    (pauseCalldata : B256 → Bytes) (queryCalldata : Bytes)
    (pausedUntil : Adr → Stor → B256)
    (circuitBreakerCells : List B256)
    (protectedSurface : List B256) : Prop where
  /-- A successful exact `pauseFor(duration)` call stores the shared pause
  projection: the all-ones sentinel is preserved and finite durations are
  measured from the entry timestamp. -/
  pauseFor_effect : ∀ {msg : Msg} {xl : Xlot} {post : Devm}
      {duration : B256},
    ExactTargetCall circuitBreaker target (pauseCalldata duration) false msg →
    MessageExecutesProgram msg xl program →
    ProcessMessage msg xl (.ok post) →
    post.error.isSome = false →
    pausedUntil target (post.state.getStor target) =
      pauseForProjection msg.benv.stat.time duration

  /-- Partial correctness for an exact static query.  Every clean settled
  result preserves the projection and accepts canonical true iff the account
  was paused at query entry.  When it was not paused, canonical false or a
  rejected answer are the only clean observations.  Exceptional/OOG outcomes
  carry no liveness obligation. -/
  isPaused_truthful : ∀ {msg : Msg} {xl : Xlot}
      {ex : TargetMessageResult},
    ExactTargetCall circuitBreaker target queryCalldata true msg →
    MessageExecutesProgram msg xl program →
    ProcessMessage msg xl ex →
    ∀ post, ex = .ok post → post.error.isSome = false →
      pausedUntil target (post.state.getStor target) =
        pausedUntil target (msg.benv.state.getStor target) ∧
      (AcceptedBoolExecution ex 1 ↔
        PausedAt pausedUntil msg.benv.state target msg.benv.stat.time) ∧
      (¬ PausedAt pausedUntil msg.benv.state target msg.benv.stat.time →
        AcceptedBoolExecution ex 0 ∨ BoolQueryExecutionFailure ex)

  /-- No retained successful SSTORE anywhere in either exact target
  invocation's frame closure targets a named CircuitBreaker cell. -/
  circuitBreaker_noninterference : ∀ {msg : Msg} {xl : Xlot}
      {ex : TargetMessageResult},
    ExactPinnedInbound circuitBreaker target pauseCalldata queryCalldata msg →
    MessageExecutesProgram msg xl program →
    ProcessMessage msg xl ex →
    ∀ key ∈ circuitBreakerCells,
      TargetInvocationNoRetainedWriteTo xl circuitBreaker key

  /-- Future target goals choose a protected selector surface and prove the
  safety claim that every nonexceptional settled call reverts while the entry
  projection is paused.  An exceptional/OOG halt remains admitted; this field
  does not assert resource sufficiency or handler reachability. -/
  protectedSurface_reverts : ∀ {msg : Msg} {xl : Xlot}
      {child : Devm} {selected : B256},
    msg.currentTarget = target →
    msg.target = some target →
    msg.codeAddress = some target →
    MessageExecutesProgram msg xl program →
    HasSelector msg selected →
    selected ∈ protectedSurface →
    PausedAt pausedUntil msg.benv.state target msg.benv.stat.time →
    ProcessMessage msg xl (.ok child) →
    SettledNormallyOrReverted child →
    child.error = some .revert

end Blanc
