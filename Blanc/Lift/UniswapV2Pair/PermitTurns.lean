import Blanc.Lift.UniswapV2Pair.PermitRawFacts
import Blanc.Lift.UniswapV2Pair.StaticViewTurns
import Blanc.Lift.UniswapV2Pair.SyncWalk
import Blanc.Lift.UniswapV2Pair.PermitRecoveryPost
import Blanc.Lift.UniswapV2Pair.StaticSlotTurns
import Blanc.Lift.CursorOccurrenceRoots
import Blanc.Lift.UniswapV2Pair.SourceStaticSlotViews
import Blanc.Lift.UniswapV2Pair.SourceSlotQueueEquality

/-!
# Authentic permit recovery turns

The permit frame's recovery STATICCALL is recovered as a step of the SAME pc-zero
derivation (`lift_sound_in`, with the permit walk restated over any instruction relation),
and the static-call turn adapter is applied to that very occurrence at the
nonce-incremented world. The source transcript's recovery turns are the retained static
Pair views of the actual child (address `1` running Pair code, for example a delegated or
precompile-disabled frame), or empty when an enabled precompile answers without entering a
code frame. The carried code bit is the occurrence's frame-entry bit.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The successful public permit frame of `sevm` after its first segment. -/
def permitPublicSuspended (current : Checkpoint) (invocation : List Nat) (sevm : Sevm) : Frame :=
  permitSuspendedFrame current (writerContext sevm invocation) (permitOwner sevm)
    (permitSpender sevm) (permitValue sevm) (permitDeadline sevm) (permitV sevm) (permitR sevm)
    (permitS sevm)

/-- The public permit recovery request over the checkpoint state. -/
def permitPublicRequest (current : Checkpoint) (sevm : Sevm) : Request :=
  permitRequest current.state (permitOwner sevm) (permitSpender sevm) (permitValue sevm)
    (permitDeadline sevm) (permitV sevm) (permitR sevm) (permitS sevm)

/-- The successful public permit run result with the recovery turns' child returns. -/
def permitPublicDone (current : Checkpoint) (invocation : List Nat) (sevm : Sevm)
    (rets : List ChildReturn) : RunResult :=
  { permitSourceDone current (writerContext sevm invocation) (permitOwner sevm)
      (permitSpender sevm) (permitValue sevm) (permitDeadline sevm) (permitV sevm) (permitR sevm)
      (permitS sevm) with childReturns := rets }

/-- The recovery observation of the derivation `D`, authenticated against `D` itself: the
actual recovery STATICCALL is a step of `D`'s own pc-zero run at the nonce-incremented
world, with its reply `out`; the queue `views` and frame-entry bit `entered` are the
occurrence's: an enabled precompile answers without a code frame and contributes nothing,
or the entered committed child is a sub-derivation of `D` whose retained Pair frames are
exactly the views. -/
def PermitRecoveryAuth (D : Exec.Deriv) (out : Bytes) (entered : Bool)
    (views : List StaticViewTurn) : Prop :=
  ∃ (b : Devm) (G : Nat) (actual : PermitCallOccurrence D b)
    (settled : PermitRecoverySettlement actual),
    D.pc = 0 ∧ D.devm = St b [] Mem.empty G ∧
    out = actual.out ∧ entered = settled.entered ∧ views.map Prod.fst = settled.paths

private theorem permit_St_getCode (x : Devm) (S : List B256) (M : Mem) (g : Nat) (a : Adr) :
    (St x S M g).getCode a = x.getCode a := rfl

private theorem permit_St_getStor (x : Devm) (S : List B256) (M : Mem) (g : Nat) (a : Adr) :
    Devm.getStor (St x S M g) a = Devm.getStor x a := rfl

theorem permitNonceWorld_getCode (sevm : Sevm) (b : Devm) (owner : Adr) (a : Adr) :
    (permitNonceWorld sevm b owner).getCode a = b.getCode a := by
  unfold permitNonceWorld
  rw [afterSstore_getCode, afterSload_getCode, afterSload_getCode]

theorem permitNonceWorld_getStor (sevm : Sevm) (b : Devm) (owner : Adr) :
    (permitNonceWorld sevm b owner).getStor sevm.currentTarget =
      (b.getStor sevm.currentTarget).set (permitNonceSlot owner)
        (permitNonceRead sevm b owner + 1) := by
  unfold permitNonceWorld
  rw [afterSstore_getStor_self, afterSload_getStor, afterSload_getStor]

/-- The nonce-incremented world represents the suspended permit frame's state over the
footprint extended by the permit's decoded rows. -/
theorem permit_suspended_rep {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b : Devm}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : WriterFreshKeys K (permitTouched (permitOwner sevm) (permitSpender sevm))) :
    WriterRep (WriterExtend K (permitTouched (permitOwner sevm) (permitSpender sevm)))
      ((permitNonceWorld sevm b (permitOwner sevm)).getStor sevm.currentTarget)
      (permitPublicSuspended current invocation sevm).current.state := by
  have nonceKey : WriterExtend K (permitTouched (permitOwner sevm) (permitSpender sevm))
      (.nonce (permitOwner sevm)) := .inr (List.mem_cons.mpr (.inl rfl))
  have stored := (rep.extend fresh).nonce_store
    (value := current.state.nonces (permitOwner sevm) + 1) nonceKey
  obtain ⟨nonce, _⟩ := permit_reads (spender := permitSpender sevm) rep fresh
  rw [permitNonceWorld_getStor, nonce]
  exact stored

/-- The recovery views use the exact queue of the successful original occurrence. -/
theorem PermitCallOccurrence.recovery_turns {U K : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    {current : Checkpoint} {invocation : List Nat} {root : Exec.Deriv} {b : Devm}
    (actual : PermitCallOccurrence root b) (settled : PermitRecoverySettlement actual)
    (rep : WriterRep K (b.getStor root.sevm.currentTarget) current.state)
    (touched : ∀ k ∈ permitTouched (permitOwner root.sevm) (permitSpender root.sevm), U k)
    (installed : some (b.getCode root.sevm.currentTarget).toList = sem.image)
    (fork : CoveredFork root.sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = root.sevm.currentTarget →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k) :
    ∃ views : List StaticViewTurn,
      views.map Prod.fst = settled.paths ∧
      (∀ picked ∈ views, picked.Authentic (permitPublicSuspended current invocation root.sevm)) ∧
      ExactTurns (permitPublicSuspended current invocation root.sevm)
        (permitPublicRequest current root.sevm) 0 (staticViewTranscript views .done)
        {complete := true, frame := permitPublicSuspended current invocation root.sevm,
          childReturns := staticViewChildReturns
            (permitPublicSuspended current invocation root.sevm)
            (permitPublicRequest current root.sevm) 0 views} := by
  have fresh := Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub touched
  have extended : ∀ k,
      WriterExtend K (permitTouched (permitOwner root.sevm) (permitSpender root.sevm)) k → U k := by
    intro k tracked
    rcases tracked with old | new
    · exact sub k old
    · exact touched k new
  obtain ⟨paths, views, queue, mapped, authentic, during⟩ := CallOccurrenceStep.staticSlotViews actual.call
    (K := WriterExtend K (permitTouched (permitOwner root.sevm) (permitSpender root.sevm)))
    (frame := permitPublicSuspended current invocation root.sevm)
    (request := permitPublicRequest current root.sevm) 0 sem image
    (by rw [actual.beforeState, permit_St_getCode, permitNonceWorld_getCode]; exact installed)
    (by rw [actual.beforeState, permit_St_getStor]; exact permit_suspended_rep rep fresh)
    (by rw [actual.beforeSevm]; rfl) (actual.beforeSevm ▸ fork)
    (by
      intro F member target
      exact Blanc.SlotFootprint.FreshKeys.of_universe inj apart extended (good F member target))
  exact ⟨views, mapped.trans (queue.paths_unique settled.queue), authentic, during⟩

/-- Typed consumption of the public permit with its recovery turns: the turns run at the
suspended frame, which they leave unchanged, and the resume is the existing one. -/
theorem permit_exact_consumes_turns {current : Checkpoint} {invocation : List Nat}
    {sevm : Sevm} {out : Bytes} {entered : Bool} {views : List StaticViewTurn}
    (paid : sevm.value = 0) (timely : sevm.benvStat.time ≤ permitDeadline sevm)
    (nonstatic : sevm.isStatic = false)
    (recovered : (permitRecoveredWord out).toAdr ≠ 0)
    (signer : (permitRecoveredWord out).toAdr = permitOwner sevm)
    (during : ExactTurns (permitPublicSuspended current invocation sevm)
      (permitPublicRequest current sevm) 0 (staticViewTranscript views .done)
      { complete := true, frame := permitPublicSuspended current invocation sevm,
        childReturns := staticViewChildReturns (permitPublicSuspended current invocation sevm)
          (permitPublicRequest current sevm) 0 views })
    (noCode : entered = false → views = []) :
    ExactConsumes (startTyped current (writerContext sevm invocation) (permitDecodedEntry sevm))
      (.next (permitExternalResult out entered) (staticViewTranscript views .done) .done)
      (permitPublicDone current invocation sevm
        (staticViewChildReturns (permitPublicSuspended current invocation sevm)
          (permitPublicRequest current sevm) 0 views)) := by
  have started := permit_startTyped_suspended (current := current)
    (ctx := writerContext sevm invocation) (owner := permitOwner sevm)
    (spender := permitSpender sevm) (value := permitValue sevm) (v := permitV sevm)
    (r := permitR sevm) (s := permitS sevm) paid timely nonstatic
  have rest := permit_resume_finished (current := current) (ctx := writerContext sevm invocation)
    (deadline := permitDeadline sevm) (v := permitV sevm) (r := permitR sevm) (s := permitS sevm)
    (value := permitValue sevm) (spender := permitSpender sevm) (codeExists := entered)
    nonstatic recovered signer
  unfold permitDecodedEntry
  rw [started]
  have consumed := ExactConsumes.nextCall
    (frame := permitPublicSuspended current invocation sevm)
    (request := permitPublicRequest current sevm)
    (continuation := .permitRecovery (permitOwner sevm) (permitSpender sevm) (permitValue sevm))
    (result := permitExternalResult out entered) (tail := .done)
    (out := permitSourceDone current (writerContext sevm invocation) (permitOwner sevm)
      (permitSpender sevm) (permitValue sevm) (permitDeadline sevm) (permitV sevm)
      (permitR sevm) (permitS sevm)) rfl
    (fun missing => by rw [noCode missing]; rfl) during (by
      change ExactConsumes (resumeSegment (permitPublicSuspended current invocation sevm)
        (permitPublicRequest current sevm)
        (.permitRecovery (permitOwner sevm) (permitSpender sevm) (permitValue sevm))
        (permitExternalResult out entered)) .done _
      unfold permitPublicSuspended permitPublicRequest
      rw [rest]
      exact ExactConsumes.finished _ [])
  have rets : staticViewChildReturns (permitPublicSuspended current invocation sevm)
      (permitPublicRequest current sevm) 0 views ++
      (permitSourceDone current (writerContext sevm invocation) (permitOwner sevm)
        (permitSpender sevm) (permitValue sevm) (permitDeadline sevm) (permitV sevm)
        (permitR sevm) (permitS sevm)).childReturns =
      staticViewChildReturns (permitPublicSuspended current invocation sevm)
        (permitPublicRequest current sevm) 0 views := List.append_nil _
  rw [rets] at consumed
  exact consumed

/-- The public source result and recovery turns share the same actual call,
settlement, returned state, and full located queue. -/
theorem permit_bytecode_actual_turns {U K : WriterKey → Prop} (inj : WriterInj U)
    (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    {current : Checkpoint} {invocation : List Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (touched : ∀ k ∈ permitTouched (permitOwner sevm) (permitSpender sevm), U k)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (representable : sevm.data.length < 2 ^ 256)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xd505accf) (freshOutput : b.output = [])
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (good : ∀ F ∈ Exec.rawFrameRoots run, F.sevm.currentTarget = sevm.currentTarget →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k) :
    sevm.value = 0 ∧ 228 ≤ sevm.data.length ∧ sevm.isStatic = false ∧
      sevm.benvStat.time ≤ permitDeadline sevm ∧
      ∃ (actual : PermitCallOccurrence ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b)
        (settled : PermitRecoverySettlement actual) (views : List StaticViewTurn),
        PermitSourceResult K current invocation sevm b post actual.call.returned.devm
          actual.out settled.entered post.gasLeft ∧
        views.map Prod.fst = settled.paths ∧
        (∀ picked ∈ views, picked.Authentic (permitPublicSuspended current invocation sevm)) ∧
        ExactTurns (permitPublicSuspended current invocation sevm)
          (permitPublicRequest current sevm) 0 (staticViewTranscript views .done)
          {complete := true, frame := permitPublicSuspended current invocation sevm,
            childReturns := staticViewChildReturns (permitPublicSuspended current invocation sevm)
              (permitPublicRequest current sevm) 0 views} := by
  obtain ⟨paid, size, guard, _, timely, _⟩ := permit_raw_in codeEq fork selector run
  have length := (word_calldata_guards_iff (n := 224) representable (by decide)).mp ⟨size, guard⟩
  obtain ⟨actual⟩ := permit_call_occurrence codeEq fork selector run
  obtain ⟨settled⟩ := actual.settlement rfl fork
  obtain ⟨recovered, signer, nonstatic, postImage⟩ := actual.post_image rfl fork
  obtain ⟨views, mapped, authentic, during⟩ := actual.recovery_turns (invocation := invocation)
    inj apart sub sem image settled rep touched installed fork good
  have fresh := Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub touched
  have source := permit_public_source_result (codeExists := settled.entered)
    (G := post.gasLeft) (invocation := invocation) rep fresh freshOutput paid nonstatic timely
    (actual.flag_one rfl fork ▸ actual.post) recovered signer
  have samePost : PermitSourceResult K current invocation sevm b post actual.call.returned.devm
      actual.out settled.entered post.gasLeft := by
    simpa only [← postImage] using source
  exact ⟨paid, length, nonstatic, timely, actual, settled, views, samePost, mapped, authentic, during⟩

/-- **Authentic permit refinement.** Every successful literal permit run at the Pair code
derives, besides the existing source facts, the source transcript whose recovery turns are
derived from the SAME pc-zero execution: the recovery STATICCALL is a step of this
derivation at the nonce-incremented world, its reply is the observation, and its turn queue
is the actual child's retained static Pair views (the frame-entry bit is `true`), or empty
when an enabled precompile answers (the bit is `false`). Original raw paths are retained:
every Pair frame of the queue is a retained frame of a committed sub-derivation. -/
theorem permit_bytecode_exact_turns {U K : WriterKey → Prop} (inj : WriterInj U)
    (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    {current : Checkpoint} {invocation : List Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (touched : ∀ k ∈ permitTouched (permitOwner sevm) (permitSpender sevm), U k)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (representable : sevm.data.length < 2 ^ 256)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xd505accf) (freshOutput : b.output = [])
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (good : ∀ F ∈ Exec.rawFrameRoots run, F.sevm.currentTarget = sevm.currentTarget →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k) :
    sevm.value = 0 ∧ 228 ≤ sevm.data.length ∧ sevm.isStatic = false ∧
      sevm.benvStat.time ≤ permitDeadline sevm ∧
      ∃ (d : Devm) (out : Bytes) (residual : Nat) (entered : Bool)
        (views : List StaticViewTurn),
        PermitRecoveryAuth ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ out entered views ∧
        PermitSourceResult K current invocation sevm b post d out entered residual ∧
        ExactConsumes (startTyped current (writerContext sevm invocation)
            (permitDecodedEntry sevm))
          (.next (permitExternalResult out entered) (staticViewTranscript views .done) .done)
          (permitPublicDone current invocation sevm
            (staticViewChildReturns (permitPublicSuspended current invocation sevm)
              (permitPublicRequest current sevm) 0 views)) ∧
        (∀ picked ∈ views, picked.Authentic (permitPublicSuspended current invocation sevm)) := by
  obtain ⟨paid, length, nonstatic, timely, actual, settled, views, source, mapped,
    authentic, during⟩ := permit_bytecode_actual_turns (invocation := invocation)
      inj apart sub sem image rep touched installed representable codeEq fork selector
        freshOutput run good
  obtain ⟨recovered, signer, _, _⟩ := actual.post_image rfl fork
  have noCode : settled.entered = false → views = [] := by
    intro missing
    have slot : actual.call.occurrence.slot = .none := by
      cases eq : actual.call.occurrence.slot with
      | none => rfl
      | some pair =>
        have entered := settled.enteredEq
        rw [eq] at entered
        exact Bool.noConfusion (missing.symm.trans entered)
    have empty := settled.queue.paths_unique (Or.inl ⟨slot, rfl⟩)
    exact List.eq_nil_of_map_eq_nil (mapped.trans empty)
  exact ⟨paid, length, nonstatic, timely, actual.call.returned.devm, actual.out,
    post.gasLeft, settled.entered, views,
    ⟨b, G, actual, settled, rfl, rfl, rfl, rfl, mapped⟩, source,
    permit_exact_consumes_turns paid timely nonstatic recovered signer during noCode, authentic⟩

end Blanc.Lift.UniswapV2Pair
