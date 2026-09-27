import Blanc.Lift.Hoare
import Blanc.Lift.LidoCircuitBreakerDeployed.Wrappers
import Blanc.ContractAdmissionSem
import Blanc.ExecutionHistoryAdmission
import Blanc.ExecutionTraceFresh

/-!
# The deployed Lido CircuitBreaker frame, and its history rung

Ladder unit (f).  The whole frame is assembled from the selector wrappers by the
dispatcher Hoare lemma `SFunc.RunP.hoare_single_call_with_gotos`, at
`Φ₀ := lidoSpec.Pre ∧ EntryAt A` and `Φ₁ := lidoSpec.Post`, with the silent set
`S := []` and every selector wrapper (43–59) in the goto set `W`:

* the view wrappers 43, 45–47, 50, 51, 53–58 are in `silentEntries`
  (`silent_entries`, `Silent.lean`) and keep the whole persistent state;
* the three non-registry writers 52, 44, 48 are `Wrappers.lean`'s specs, each
  under its one `ForeignApart (2 ^ 160)` premise, collected in `LocalApart`;
* the two Registry writers, `registerPauser` (59) and `pause` (49, the entry
  with the external `CALL`), are the fields of `LidoWriterSpecs A`, taken here
  as hypotheses: they are exactly what the `setPauser` (entries 32/4) and
  `pause` (entry 13) walks must supply.

**The premise `A`.**  `LidoWriterSpecs` is parameterised by the per-frame
collision premise `A entries sevm` those two walks need (design §3: the
`RegistryKeysFaithful` keys of the `setPauser` branch the call's arguments
select, and the `ForeignApart` expiry slots of the old and new pauser).  The
entry condition carries it in implication form (design D3): for *every* witness
`entries` of the frame-entry storage, `A entries sevm`.  It asserts no
invariant; the ladder supplies the witness, and the witness is determined by
storage.  The instance `A` and the proof of `LidoWriterSpecs A` belong to the
next units; a trivial `A := fun _ _ => False` would make the entry condition
unsatisfiable at every entered frame, so the history theorem is only as strong
as the `A` it is instantiated with.

`LocalApart` is required at every entered frame, not only for the selector
that uses it: the dispatcher Hoare lemma does not track which selector reached
which wrapper, and the three facts (the caller's `heartbeatExpiry` slot and the
constant slots `0`, `1` are off the Registry layout) are collision-freedom facts
about one frame's own three slots.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc
open Blanc.Lift
open Blanc.LidoCircuitBreaker
open Blanc.ExecutionTrace

/-- The three non-registry slots a frame can write are off the Registry layout. -/
def LocalApart (sevm : Sevm) : Prop :=
  ForeignApart (2 ^ 160) (mapSlot sevm.caller.toB256 2) ∧
    ForeignApart (2 ^ 160) 0 ∧ ForeignApart (2 ^ 160) 1

/-- The Registry-writer premise `A`, in implication form over every witness of
the storage `d` holds for the frame's own contract. -/
def EntryAt (A : List LidoCircuitBreaker.Entry → Sevm → Prop) (sevm : Sevm) (d : Devm) : Prop :=
  ∀ entries, RegistryWitness (solRegistryStorage (Devm.getStor d sevm.currentTarget)) entries →
    A entries sevm

/-- The carried entry condition at every entered CircuitBreaker frame. -/
def lidoEntry (A : List LidoCircuitBreaker.Entry → Sevm → Prop) : Sevm → Devm → Prop := fun sevm pre =>
  LocalApart sevm ∧ EntryAt A sevm pre

/-- The full frame entry: fresh entry (discharged at the history rung) and `lidoEntry`. -/
def lidoFrameEntry (A : List LidoCircuitBreaker.Entry → Sevm → Prop) : Sevm → Devm → Prop := fun sevm pre =>
  Exec.FreshEntry sevm pre ∧ lidoEntry A sevm pre

/-- The deeper-frame hypothesis of `ContractSpecSem.SoundAdmitted` for `lidoSpec`
at the frame `sevm`, for the entry condition `entry`. -/
def LidoDeeper (entry : Sevm → Devm → Prop) (sevm : Sevm) : Prop :=
  ∀ pc' sevm' pre' post' (child : Exec pc' sevm' pre' (.ok post')),
    sevm'.depth < sevm.depth →
    lidoSpec.sem.At sevm.currentTarget pc' sevm' pre' →
    CoveredFork sevm'.benvStat.fork →
    Exec.FrameAdmitted sevm.currentTarget entry child →
    lidoSpec.PreWf sevm.currentTarget sevm' pre' →
    lidoSpec.Post sevm.currentTarget sevm' post'

/-- **The two Registry writers' wrapper specifications**, as the frame consumes
them.  Each is the statement the corresponding walk must prove:

* `registerPauser`: selector wrapper 59 (decoder 20, body 21: `onlyAdmin`,
  `setPauser` entry 32 → 4, the heartbeat tail entry 2) takes the frame
  precondition to the frame postcondition, given `LocalApart` and `A` at its
  entry storage;
* `pause`: selector wrapper 49 (decoder 7, body 13: lock, pauser check,
  `setPauser(t, 0)`, the `pauseFor` `CALL`, the `isPaused` `STATICCALL`,
  `_setHeartbeatExpiry`) does the same inside a root derivation `R` whose frame
  admission and deeper-frame hypothesis are given, as `Weth9.withdraw_post_in`
  does for WETH9's one `CALL`. -/
structure LidoWriterSpecs (A : List LidoCircuitBreaker.Entry → Sevm → Prop) : Prop where
  registerPauser : ∀ {sevm : Sevm} {d : Devm} {o : Outcome} {w : SFunc},
    CoveredFork sevm.benvStat.fork → prog[59]? = some w →
    LocalApart sevm → EntryAt A sevm d →
    lidoSpec.Pre sevm.currentTarget sevm d → SFunc.Run prog sevm d w o →
    lidoSpec.Post sevm.currentTarget sevm (Outcome.devm o)
  pause : ∀ {R : Exec.Deriv} {sevm : Sevm} {d : Devm} {o : Outcome} {w : SFunc},
    CoveredFork sevm.benvStat.fork → sevm.code = code →
    Exec.FrameAdmitted sevm.currentTarget (lidoFrameEntry A) R.exc →
    LidoDeeper (lidoFrameEntry A) sevm →
    prog[49]? = some w →
    LocalApart sevm → EntryAt A sevm d →
    lidoSpec.Pre sevm.currentTarget sevm d → SFunc.RunP (StepIn R) prog sevm d w o →
    lidoSpec.Post sevm.currentTarget sevm (Outcome.devm o)

/-- Every selector wrapper, the goto targets of the dispatcher. -/
def wrapperEntries : List Nat :=
  [43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59]

theorem entry0_lookup : prog[0]? = some t_0000_c0 := rfl

theorem entry0_gotos :
    t_0000_c0.silentCallsWith [] wrapperEntries 1 = true := by
  decide +kernel

theorem entry0_noCalls : t_0000_c0.callRefs.all (· ∈ ([] : List Nat)) = true := by
  decide +kernel

private instance : Inhabited SFunc := ⟨.undefined⟩

section Frame

variable {A : List LidoCircuitBreaker.Entry → Sevm → Prop} {sevm : Sevm}

private theorem stable0 {d d' : Devm} (hs : d.state = d'.state)
    (h : lidoSpec.Pre sevm.currentTarget sevm d ∧ EntryAt A sevm d) :
    lidoSpec.Pre sevm.currentTarget sevm d' ∧ EntryAt A sevm d' := by
  refine ⟨h.1.state_eq hs.symm, ?_⟩
  unfold EntryAt
  rw [getStor_eq_of_state_eq hs.symm]
  exact h.2

private theorem stable1 {d d' : Devm} (hs : d.state = d'.state)
    (h : lidoSpec.Post sevm.currentTarget sevm d) :
    lidoSpec.Post sevm.currentTarget sevm d' :=
  ContractSpecSem.Post.of_state_eq h hs.symm

private theorem post_of_regInv {d : Devm}
    (h : RegInv (Devm.getStor d sevm.currentTarget)) :
    lidoSpec.Post sevm.currentTarget sevm d :=
  ⟨trivial, h⟩

/-- **The Lido CircuitBreaker frame postcondition inside a root derivation.**
Every lifted run of the deployed runtime from the frame precondition ends in the
frame postcondition, given the two Registry writers' specs, the frame's own
`LocalApart` and `A` premises, `R`'s frame admission, and the admitted
deeper-frame hypothesis. -/
theorem lido_frame_post_in {R : Exec.Deriv} (W : LidoWriterSpecs A) {pre post : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hcode : sevm.code = code)
    (hrun : SProg.RunP (StepIn R) prog sevm pre post)
    (hloc : LocalApart sevm) (hA : EntryAt A sevm pre)
    (hadmR : Exec.FrameAdmitted sevm.currentTarget (lidoFrameEntry A) R.exc)
    (ih : LidoDeeper (lidoFrameEntry A) sevm)
    (hpre : lidoSpec.Pre sevm.currentTarget sevm pre) :
    lidoSpec.Post sevm.currentTarget sevm post := by
  obtain ⟨f, hf, run⟩ := hrun
  rw [entry0_lookup] at hf
  cases hf
  refine SFunc.RunP.hoare_single_call_with_gotos StepIn.toRun (S := []) (K := [])
    (W := wrapperEntries)
    (Φ₀ := fun d => lidoSpec.Pre sevm.currentTarget sevm d ∧ EntryAt A sevm d)
    (Φ₁ := lidoSpec.Post sevm.currentTarget sevm)
    rfl (fun hk _ => absurd hk (List.not_mem_nil))
    (fun _ h => ContractSpecSem.post_of_pre h.1)
    stable0 stable1 (fun hk _ => absurd hk (List.not_mem_nil)) ?_ entry0_gotos entry0_noCalls
    run ⟨hpre, hA⟩
  intro k g hk hg d o hd r
  have hinv : RegInv (Devm.getStor d sevm.currentTarget) := hd.1.inv.left rfl
  have silentCase : k ∈ silentEntries → lidoSpec.Post sevm.currentTarget sevm (Outcome.devm o) :=
    fun hs => post_of_regInv (silentCallee_regInv hs hg hinv (r.mono StepIn.toRun))
  simp only [wrapperEntries, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact silentCase (by decide)
  · exact post_of_regInv
      (setPauseDuration_wrapper_regInv hg hloc.2.1 hinv (r.mono StepIn.toRun))
  · exact silentCase (by decide)
  · exact silentCase (by decide)
  · exact silentCase (by decide)
  · exact post_of_regInv
      (setHeartbeatInterval_wrapper_regInv hg hloc.2.2 hinv (r.mono StepIn.toRun))
  · exact W.pause hfork hcode hadmR ih hg hloc hd.2 hd.1 r
  · exact silentCase (by decide)
  · exact silentCase (by decide)
  · exact post_of_regInv (heartbeat_wrapper_regInv hg hloc.1 hinv (r.mono StepIn.toRun))
  · exact silentCase (by decide)
  · exact silentCase (by decide)
  · exact silentCase (by decide)
  · exact silentCase (by decide)
  · exact silentCase (by decide)
  · exact silentCase (by decide)
  · exact W.registerPauser hfork hg hloc hd.2 hd.1 (r.mono StepIn.toRun)

end Frame

/-- **Lido CircuitBreaker frame soundness, trace-admitted**, given the two
Registry writers' specs. -/
theorem lidoSpec_soundAdmitted {A : List LidoCircuitBreaker.Entry → Sevm → Prop} (W : LidoWriterSpecs A)
    (ca : Adr) : lidoSpec.SoundAdmitted ca (lidoFrameEntry A) := by
  intro sevm pre post hfork execution hrun hca admitted ih _ hpre
  subst hca
  have hin := lift_sound_in cert_check hrun.1 hfork execution
  obtain ⟨_, hloc, hA⟩ := admitted.root rfl
  exact lido_frame_post_in (R := ⟨0, sevm, pre, .ok post, execution⟩) W hfork hrun.1 hin
    hloc hA admitted ih hpre

/-- **Lido CircuitBreaker frame preservation, trace-admitted**: the form the
trace rungs consume. -/
theorem lidoSpec_preservesAdmitted {A : List LidoCircuitBreaker.Entry → Sevm → Prop} (W : LidoWriterSpecs A)
    (ca : Adr) : lidoSpec.PreservesAdmitted ca (lidoFrameEntry A) :=
  lidoSpec.preserves_inv_admitted ca (lidoFrameEntry A) (lidoSpec_soundAdmitted W ca)


end Blanc.Lift.LidoCircuitBreakerDeployed
