import Blanc.ExecutionOccurrence

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
  /-- A successful exact `pauseFor(duration)` call stores precisely the
  entry timestamp plus the requested duration in the abstract projection. -/
  pauseFor_effect : ∀ {msg : Msg} {xl : Xlot} {post : Devm}
      {duration : B256},
    ExactTargetCall circuitBreaker target (pauseCalldata duration) false msg →
    MessageExecutesProgram msg xl program →
    ProcessMessage msg xl (.ok post) →
    post.error.isSome = false →
    pausedUntil target (post.state.getStor target) =
      msg.benv.stat.time + duration

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
