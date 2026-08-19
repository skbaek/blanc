import Blanc.LidoCircuitBreakerPauseWorldRun

/-!
# What a cooperative pause leaves behind

`Blanc/LidoCircuitBreakerPauseWorldRun.lean` runs each pause witness world end
to end and states what its **raw** poststate contains.  That is one altitude
below the message: a raw poststate is what the code frame produced, not what
the message left behind, and nothing there says the frame settles to it rather
than erasing it through error handling.

This module lifts both worlds to the message altitude on the
`unregisterWorld_settles` template: the frame really enters the code frame the
world is about, the settle of its clean raw poststate is that same state, and
so every surviving effect the run established is an effect of the **message**.

## What these theorems do not say

* **Two concrete worlds.**  Each statement is about one message in one
  two-account world with the frozen cooperative responder as the paused
  target.  Nothing is quantified over callees, gas, entry lists or worlds.
* **Cooperation is witness content.**  A codeless target routes to
  `emptyRevert`, a failing `pauseFor` to `bubbleRevert`, a non-canonical
  `isPaused` answer to `PauseFailed`; no `.ok` pause exists without a callee
  that answers as the pausable interface requires.  The complementary fact —
  that a *hostile* callee can prevent the pause outright — is the published
  callback-visible liveness counterexample, and it stands.
* **No genesis reachability.**  Neither world's entry state is exhibited as
  reachable from a genesis-consistent history.
* **The Registry projection is model-side.**  As in
  `Blanc/LidoCircuitBreakerAbsentRegistration.lean` and the unregistration
  world, the entry-list projection is stated over the model's applied writes,
  not over the settled storage: the walk exports no universal storage frame,
  so a `RegistryWitness` *about the poststate* is not available and is not
  claimed.  What is claimed about the poststate is the named cells.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-! ## The settle computation, shared by both worlds

For a clean raw poststate the call frame's settle is the identity on `.ok`.
Both worlds prove `post.error = none` unconditionally in their own effects
theorem, so neither settlement carries a cleanliness premise. -/

private theorem pauseWorld_settle_ok {stor : Stor} {gas : Nat} {post : Devm}
    (herr : post.error = none) :
    (Frame.ofCall (pauseWorldMsg stor gas)).settle (.ok post) = .ok post := by
  have hnot : post.error.isSome ≠ true := by rw [herr]; simp
  simp only [Frame.settle, Frame.settleMsg, Frame.ofCall,
    executeCode.handleError, processMessage.settle, bind, Except.bind,
    if_neg hnot]
  rfl

/-- The message frame settles to the raw poststate: `ProcessMessage` at the
world's own message, with the raw execution the run produced. -/
private theorem pauseWorld_processMessage {stor : Stor} {gas : Nat}
    {post : Devm} (herr : post.error = none) :
    ProcessMessage (pauseWorldMsg stor gas)
      (.some ⟨⟨0, pauseWorldSevm stor gas, pauseWorldPre stor gas⟩,
        (.ok post : Execution)⟩) (.ok post) := by
  have hframe := RunFrame.of_run (f := Frame.ofCall (pauseWorldMsg stor gas))
    (raw := (.ok post : Execution)) (pauseWorld_frameEntry stor gas)
  rwa [pauseWorld_settle_ok herr] at hframe

/-! ## Row 19: the last-assignment pause

The world's single registered target is the paused callee, so the pause
retires the pauser: the assignment, its one-based index, the array slot, the
array length and the pauser's assignment count all go to zero, and the expiry
cell is stored at the zero arm.  The configured interval and duration are
code-configured cells the pause does not touch. -/

/-- **Message-altitude settlement of the row-19 pause world.**  The frame
enters this world's code frame, its clean raw poststate survives settlement
unchanged, and the effects below are therefore effects of the message.  This
is a statement about one message in one world with a cooperative callee; see
the module header for what it does not claim. -/
theorem pauseLastWorld_settles :
    ∃ post : Devm,
      exec ⟨0, pauseLastSevm, pauseLastPre⟩ = .ok post ∧
      ProcessMessage (pauseWorldMsg pauseLastWorldStor pauseLastWorldGas)
        (.some ⟨⟨0, pauseLastSevm, pauseLastPre⟩, (.ok post : Execution)⟩)
        (.ok post) ∧
      post.error = none ∧
      post.output = [] ∧
      post.gasLeft = 0 ∧
      post.getTransVal configWorldOwner lockKey = 0 ∧
      post.getStorVal configWorldOwner (expirySlot pauseWorldPauser) = 0 ∧
      post.getStorVal configWorldOwner
        (assignmentSlot pauseWorldCallee.toB256) = 0 ∧
      post.getStorVal configWorldOwner (countSlot pauseWorldPauser) = 0 ∧
      post.getStorVal configWorldOwner arrayLengthSlot = 0 ∧
      post.getStorVal configWorldOwner (arrayEntrySlot 1) = 0 ∧
      post.getStorVal configWorldOwner
        (indexSlot pauseWorldCallee.toB256) = 0 ∧
      post.getStorVal configWorldOwner heartbeatIntervalSlot =
        pauseWorldInterval ∧
      post.getStorVal configWorldOwner pauseDurationSlot =
        pauseWorldDuration ∧
      (∀ pauser, canonicalAddress pauser → pauser ≠ pauseWorldPauser →
        post.getStorVal configWorldOwner (expirySlot pauser) =
          pauseLastPre.getStorVal configWorldOwner (expirySlot pauser)) ∧
      post.logs =
        [⟨configWorldOwner,
            [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0],
            []⟩,
          ⟨configWorldOwner,
            [pauseTriggeredEvent, pauseWorldCallee.toB256, pauseWorldPauser],
            pauseWorldDuration.toBytes⟩,
          ⟨configWorldOwner, [heartbeatUpdatedEvent, pauseWorldPauser],
            (0 : B256).toBytes⟩] := by
  obtain ⟨post, _hprog, hexec, _hne, hgas, herr, hout, hlock, hexp, hassign,
    hcount, hlen, harr, hidx, hint, hdur, hother, hlogs, _hcompile⟩ :=
    pauseLastWorld_effects
  exact ⟨post, hexec, pauseWorld_processMessage herr, herr, hout, hgas, hlock,
    hexp, hassign, hcount, hlen, harr, hidx, hint, hdur, hother, hlogs⟩

/-! ## Row 18: the retained-assignment pause

The paused callee is the first of the pauser's two registered targets, so the
removal is a swap-pop: the second target moves into array slot `1` and takes
one-based index `1`, the vacated slot `2` is cleared, the length drops to `1`
and the pauser's count to `1`.  The pauser survives, so the expiry cell is
stored at the *checked* arm — `timestamp + interval`, not zero — and the
heartbeat log carries that same word. -/

/-- **Message-altitude settlement of the row-18 pause world.**  Same shape and
same disclaimers as `pauseLastWorld_settles`; the difference is entirely in
the surviving content, where a retained second target and a live expiry
replace the row-19 zeros. -/
theorem pauseRetainedWorld_settles :
    ∃ post : Devm,
      exec ⟨0, pauseRetainedSevm, pauseRetainedPre⟩ = .ok post ∧
      ProcessMessage
        (pauseWorldMsg pauseRetainedWorldStor pauseRetainedWorldGas)
        (.some ⟨⟨0, pauseRetainedSevm, pauseRetainedPre⟩,
          (.ok post : Execution)⟩) (.ok post) ∧
      post.error = none ∧
      post.output = [] ∧
      post.gasLeft = 0 ∧
      post.getTransVal configWorldOwner lockKey = 0 ∧
      post.getStorVal configWorldOwner (expirySlot pauseWorldPauser) =
        pauseWorldInterval + pauseWorldTime ∧
      post.getStorVal configWorldOwner
        (assignmentSlot pauseWorldCallee.toB256) = 0 ∧
      post.getStorVal configWorldOwner (countSlot pauseWorldPauser) = 1 ∧
      post.getStorVal configWorldOwner arrayLengthSlot = 1 ∧
      post.getStorVal configWorldOwner (arrayEntrySlot 1) = pauseWorldT2 ∧
      post.getStorVal configWorldOwner (arrayEntrySlot 2) = 0 ∧
      post.getStorVal configWorldOwner
        (indexSlot pauseWorldCallee.toB256) = 0 ∧
      post.getStorVal configWorldOwner (indexSlot pauseWorldT2) = 1 ∧
      post.getStorVal configWorldOwner heartbeatIntervalSlot =
        pauseWorldInterval ∧
      post.getStorVal configWorldOwner pauseDurationSlot =
        pauseWorldDuration ∧
      (∀ pauser, canonicalAddress pauser → pauser ≠ pauseWorldPauser →
        post.getStorVal configWorldOwner (expirySlot pauser) =
          pauseRetainedPre.getStorVal configWorldOwner (expirySlot pauser)) ∧
      post.logs =
        [⟨configWorldOwner,
            [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0],
            []⟩,
          ⟨configWorldOwner,
            [pauseTriggeredEvent, pauseWorldCallee.toB256, pauseWorldPauser],
            pauseWorldDuration.toBytes⟩,
          ⟨configWorldOwner, [heartbeatUpdatedEvent, pauseWorldPauser],
            (pauseWorldInterval + pauseWorldTime).toBytes⟩] := by
  obtain ⟨post, _hprog, hexec, _hne, hgas, herr, hout, hlock, hexp, hassign,
    hcount, hlen, hh, htl, hidx, hmv, hint, hdur, hother, hlogs, _hcompile⟩ :=
    pauseRetainedWorld_effects
  exact ⟨post, hexec, pauseWorld_processMessage herr, herr, hout, hgas, hlock,
    hexp, hassign, hcount, hlen, hh, htl, hidx, hmv, hint, hdur, hother,
    hlogs⟩

/-! ## The Registry projection, model-side

Both removals go through the shared `setPauser` kernel, so the model's own
source trace applies at each world's entry list.  Following
`Blanc/LidoCircuitBreakerAbsentRegistration.lean` and the unregistration
world, the projection is stated over the model's **applied writes**, not over
the settled storage: a `RegistryWitness` quantifies over every canonical
address, and the walk exports no universal storage frame that could discharge
those quantifiers at the poststate.  These two theorems are therefore about
the model alone: they say what the Registry's own `setPauser` chronology does
to each world's entry storage, and they are proved from the general transport
`RegistryWitness.applySetPauserSourceTrace`, not from either run.  What the
*run* leaves behind is the named cells in the settlement theorems above, and
nothing here asserts that the two sides agree slot by slot -- see
`pauseWorld_projectionAgrees` below for the part of that agreement which is
actually proved. -/

theorem pauseLastWorld_registryProjection :
    ∃ trace,
      setPauserSourceTrace [(pauseWorldCallee.toB256, pauseWorldPauser)]
        pauseWorldCallee.toB256 0 = some trace ∧
      trace.postEntries = [] ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor pauseLastPre configWorldOwner) trace.writes))
        trace.postEntries := by
  refine ⟨_, rfl, by decide, ?_⟩
  exact RegistryWitness.applySetPauserSourceTrace
    (pauseWorld_lastPreWitness pauseLastWorldGas)
    (newPauser := 0) pauseWorld_calleeValid.2
    (show (0 : B256).toNat < 2 ^ 160 by decide) rfl

theorem pauseRetainedWorld_registryProjection :
    ∃ trace,
      setPauserSourceTrace
        [(pauseWorldCallee.toB256, pauseWorldPauser),
          (pauseWorldT2, pauseWorldPauser)]
        pauseWorldCallee.toB256 0 = some trace ∧
      trace.postEntries = [(pauseWorldT2, pauseWorldPauser)] ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor pauseRetainedPre configWorldOwner) trace.writes))
        trace.postEntries := by
  refine ⟨_, rfl, by decide, ?_⟩
  exact RegistryWitness.applySetPauserSourceTrace
    (pauseWorld_retainedPreWitness pauseRetainedWorldGas)
    (newPauser := 0) pauseWorld_calleeValid.2
    (show (0 : B256).toNat < 2 ^ 160 by decide) rfl

/-! ## Where the model and the run do meet

The projections above are model-side and the settlements are run-side; this
theorem is the part of their agreement that is actually provable here.  At
each world it takes the settled poststate's own Registry cells and the storage
the model's trace writes produce, and states that they agree **at the slots
the trace touches**.  It is deliberately not more: agreement at every slot is
the universal storage frame the walk does not export. -/

theorem pauseWorld_projectionAgrees :
    (∃ post : Devm, exec ⟨0, pauseLastSevm, pauseLastPre⟩ = .ok post ∧
      ∃ trace,
        setPauserSourceTrace [(pauseWorldCallee.toB256, pauseWorldPauser)]
          pauseWorldCallee.toB256 0 = some trace ∧
        (let applied :=
          applyRegistryWrites (Devm.getStor pauseLastPre configWorldOwner)
            trace.writes
        applied.get (assignmentSlot pauseWorldCallee.toB256) =
            post.getStorVal configWorldOwner
              (assignmentSlot pauseWorldCallee.toB256) ∧
          applied.get (indexSlot pauseWorldCallee.toB256) =
            post.getStorVal configWorldOwner
              (indexSlot pauseWorldCallee.toB256) ∧
          applied.get (countSlot pauseWorldPauser) =
            post.getStorVal configWorldOwner (countSlot pauseWorldPauser) ∧
          applied.get arrayLengthSlot =
            post.getStorVal configWorldOwner arrayLengthSlot ∧
          applied.get (arrayEntrySlot 1) =
            post.getStorVal configWorldOwner (arrayEntrySlot 1))) ∧
    (∃ post : Devm, exec ⟨0, pauseRetainedSevm, pauseRetainedPre⟩ = .ok post ∧
      ∃ trace,
        setPauserSourceTrace
          [(pauseWorldCallee.toB256, pauseWorldPauser),
            (pauseWorldT2, pauseWorldPauser)]
          pauseWorldCallee.toB256 0 = some trace ∧
        (let applied :=
          applyRegistryWrites (Devm.getStor pauseRetainedPre configWorldOwner)
            trace.writes
        applied.get (assignmentSlot pauseWorldCallee.toB256) =
            post.getStorVal configWorldOwner
              (assignmentSlot pauseWorldCallee.toB256) ∧
          applied.get (indexSlot pauseWorldCallee.toB256) =
            post.getStorVal configWorldOwner
              (indexSlot pauseWorldCallee.toB256) ∧
          applied.get (countSlot pauseWorldPauser) =
            post.getStorVal configWorldOwner (countSlot pauseWorldPauser) ∧
          applied.get arrayLengthSlot =
            post.getStorVal configWorldOwner arrayLengthSlot ∧
          applied.get (arrayEntrySlot 1) =
            post.getStorVal configWorldOwner (arrayEntrySlot 1) ∧
          applied.get (arrayEntrySlot 2) =
            post.getStorVal configWorldOwner (arrayEntrySlot 2) ∧
          applied.get (indexSlot pauseWorldT2) =
            post.getStorVal configWorldOwner (indexSlot pauseWorldT2))) := by
  constructor
  · obtain ⟨post, _hprog, hexec, _hne, _hgas, _herr, _hout, _hlock, _hexp,
      hassign, hcount, hlen, harr, hidx, _hint, _hdur, _hother, _hlogs,
      _hcompile⟩ := pauseLastWorld_effects
    refine ⟨post, hexec, _, rfl, ?_⟩
    simp only [pauseLastPre, pauseWorld_getStor]
    rw [hassign, hcount, hlen, harr, hidx]
    exact ⟨by decide, by decide, by decide, by decide, by decide⟩
  · obtain ⟨post, _hprog, hexec, _hne, _hgas, _herr, _hout, _hlock, _hexp,
      hassign, hcount, hlen, hh, htl, hidx, hmv, _hint, _hdur, _hother,
      _hlogs, _hcompile⟩ := pauseRetainedWorld_effects
    refine ⟨post, hexec, _, rfl, ?_⟩
    simp only [pauseRetainedPre, pauseWorld_getStor]
    rw [hassign, hcount, hlen, hh, htl, hidx, hmv]
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide,
      by decide⟩

end Blanc.LidoCircuitBreaker
