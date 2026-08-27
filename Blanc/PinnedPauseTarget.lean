import Blanc.ExecutionOccurrence

/-!
# Account-level protocol for a pinned pause target

This shared module describes observable account behaviour, not a particular
contract family.  The `program` parameter is deliberately only an index of the
bundle: `ProgramInstalledAt` is the single detachable code-identity premise.
A direct account can discharge it from installed bytecode; a later proxy
composition can instead establish the same indexed behaviour through its
proxy/implementation correspondence.

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

/-- A single detachable direct-installation fact.  It is intentionally not a
field of `PinnedPauseTarget`. -/
def ProgramInstalledAt (pre : Devm) (target : Adr) (program : Prog) : Prop :=
  some (pre.getCode target).toList = Prog.compile program

/-- The invocation frame is executing the indexed program.  Composition
derives this named fact from `ProgramInstalledAt` (or from a proxy pair); it is
kept separate from every observable call-shape predicate. -/
def MessageUsesProgram (msg : Msg) (program : Prog) : Prop :=
  some msg.code.toList = Prog.compile program

/-- The exact account-level code frame opened by one zero-value inbound call. -/
structure ExactTargetFrame (caller target : Adr) (calldata : Bytes)
    (static : Bool) (sevm : Sevm) : Prop where
  currentTarget : sevm.currentTarget = target
  targetAddress : sevm.target = some target
  codeAddress : sevm.codeAddress = some target
  callerAddress : sevm.caller = caller
  valueZero : sevm.value = 0
  staticFlag : sevm.isStatic = static
  data : sevm.data = calldata

/-- The account code frame is executing the bundle's indexed program. -/
def FrameUsesProgram (sevm : Sevm) (program : Prog) : Prop :=
  some sevm.code.toList = Prog.compile program

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

/-- A whole code-frame execution returned an accepted boolean word. -/
def AcceptedBoolExecution (ex : Execution) (word : B256) : Prop :=
  ∃ child, ex = .ok child ∧ AcceptedBoolWord child word

/-- A whole code-frame execution returned neither accepted boolean word. -/
def BoolQueryExecutionFailure (ex : Execution) : Prop :=
  ¬ AcceptedBoolExecution ex 0 ∧ ¬ AcceptedBoolExecution ex 1

/-- The account is paused exactly when the entry timestamp precedes its
abstract paused-until projection. -/
def PausedAt (pausedUntil : Devm → Adr → B256)
    (entry : Devm) (target : Adr) (timestamp : B256) : Prop :=
  timestamp < pausedUntil entry target

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

/-- Code-frame counterpart of `ExactPinnedInbound`. -/
def ExactPinnedFrameInbound (circuitBreaker target : Adr)
    (pauseCalldata : B256 → Bytes) (queryCalldata : Bytes)
    (sevm : Sevm) : Prop :=
  (∃ duration,
      ExactTargetFrame circuitBreaker target (pauseCalldata duration) false
        sevm) ∨
    ExactTargetFrame circuitBreaker target queryCalldata true sevm

/-- A code frame's calldata has the selected ABI function selector. -/
def FrameHasSelector (sevm : Sevm) (selected : B256) : Prop :=
  ∃ tail, sevm.data = abiSelectorBytes selected ++ tail

/-- A target-agnostic account protocol for pause composition.

The fields say only what the account at `target` does on exact inbound
messages.  They do not expose or unfold `program`, and code identity remains
the separate `ProgramInstalledAt` premise above. -/
structure PinnedPauseTarget
    (circuitBreaker target : Adr) (program : Prog)
    (pauseCalldata : B256 → Bytes) (queryCalldata : Bytes)
    (pausedUntil : Devm → Adr → B256)
    (circuitBreakerCells : List B256)
    (protectedSurface : List B256) : Prop where
  /-- A successful exact `pauseFor(duration)` call stores precisely the
  entry timestamp plus the requested duration in the abstract projection. -/
  pauseFor_effect : ∀ {sevm : Sevm} {pre post : Devm}
      {duration : B256},
    ExactTargetFrame circuitBreaker target (pauseCalldata duration) false
      sevm →
    FrameUsesProgram sevm program →
    Exec 0 sevm pre (.ok post) →
    pausedUntil post target = sevm.benvStat.time + duration

  /-- An exact static query accepts canonical true iff the account was paused
  at query entry.  When it was not paused, canonical false or a rejected
  answer/error are the only admitted observations. -/
  isPaused_truthful : ∀ {sevm : Sevm} {pre : Devm} {ex : Execution},
    ExactTargetFrame circuitBreaker target queryCalldata true sevm →
    FrameUsesProgram sevm program →
    Exec 0 sevm pre ex →
    (AcceptedBoolExecution ex 1 ↔
      PausedAt pausedUntil pre target sevm.benvStat.time) ∧
    (¬ PausedAt pausedUntil pre target sevm.benvStat.time →
      AcceptedBoolExecution ex 0 ∨ BoolQueryExecutionFailure ex)

  /-- No retained successful SSTORE anywhere in either exact target
  invocation's frame closure targets a named CircuitBreaker cell. -/
  circuitBreaker_noninterference : ∀ {sevm : Sevm} {pre : Devm}
      {ex : Execution} (run : Exec 0 sevm pre ex),
    ExactPinnedFrameInbound circuitBreaker target pauseCalldata queryCalldata
      sevm →
    FrameUsesProgram sevm program →
    ∀ key ∈ circuitBreakerCells,
      Exec.NoRetainedWriteTo run circuitBreaker key

  /-- Future target goals choose a protected selector surface and prove that
  every such account call reverts while the entry projection is paused. -/
  protectedSurface_reverts : ∀ {sevm : Sevm} {pre : Devm}
      {ex : Execution} {selected : B256},
    sevm.currentTarget = target →
    sevm.target = some target →
    sevm.codeAddress = some target →
    FrameUsesProgram sevm program →
    FrameHasSelector sevm selected →
    selected ∈ protectedSurface →
    PausedAt pausedUntil pre target sevm.benvStat.time →
    Exec 0 sevm pre ex →
    ∃ child, ex = .error (.revert, child)

end Blanc
