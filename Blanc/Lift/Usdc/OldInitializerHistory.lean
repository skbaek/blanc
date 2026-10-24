import Blanc.Lift.Usdc.OldInitializerV1Root
import Blanc.Lift.Usdc.OldInitializerEffects
import Blanc.ExecutionStagedRootFacts

/-!
# Old USDC initializers at the raw frames of a selected-domain history

The V1 `initialize` and V2 `initializeV2` classifiers take a fresh PC0
successful run with `stateGas = none`, empty stack and memory and (for V1)
a word-bounded initial gas. At a raw frame of a `ConfiguredHistoryTraceIn`
all of these come from the history (`rawFrame_entryFacts`), so the only
frame facts left are the ones that select the case: the frame succeeded,
runs the registered implementation code, and carries that selector. Raw
frames include delegated child frames, so the proxy-forwarded initializer
frame is covered. Short-name zero preservation keeps its actual short-length,
fixed-slot separation and entry-seed inputs.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace
open OldInitializerV1Callee (V1InitializerWriteClass fixedSlots)

/-- **V1 `initialize` at a raw history frame.** A successful raw frame of a
selected-domain history running the registered V1 code with selector
`0x3357162b` is, on its own `StepIn` derivation, a run whose every store is
classified by `V1InitializerWriteClass` and which executes no external
instruction. -/
theorem implV1_initialize_observed_rawFrame
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames) {post : Devm}
    (ok : R.exn = .ok post) (code : R.sevm.code = ImplV1.code)
    (selector : Blanc.Sevm.selector R.sevm = 0x3357162b) :
    SProg.RunP (fun s d n d' => StepIn R s d n d' ∧
      V1InitializerWriteClass R.sevm d n ∧ ∀ x, n ≠ .exec x)
      ImplV1.cert.prog R.sevm R.devm post := by
  obtain ⟨pc, -, hsg, ⟨stack, memory⟩, gas⟩ :=
    history.rawFrame_entryFacts capabilities R member
  rcases R with ⟨pc', sevm, pre, out, run⟩
  dsimp only at pc hsg stack memory gas ok code selector ⊢
  subst pc ok
  exact implV1_initialize_observed run code hsg stack memory gas selector

/-- Short-string V1 `initialize` at a raw history frame preserves an
explicitly supplied zero-row seed at the frame's execution target. -/
theorem implV1_initialize_short_zero_rawFrame
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K : B256 → Prop}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames) {post : Devm}
    (ok : R.exn = .ok post) (code : R.sevm.code = ImplV1.code)
    (selector : Blanc.Sevm.selector R.sevm = 0x3357162b)
    (short : V1InitializerShort R.sevm)
    (separate : ∀ key, K key → key ∉ fixedSlots)
    (zero : ZeroSlots K R.sevm.currentTarget R.devm) :
    ZeroSlots K R.sevm.currentTarget post := by
  obtain ⟨pc, -, hsg, ⟨stack, memory⟩, gas⟩ :=
    history.rawFrame_entryFacts capabilities R member
  rcases R with ⟨pc', sevm, pre, out, run⟩
  dsimp only at pc hsg stack memory gas ok code selector short zero ⊢
  subst pc ok
  exact implV1_initialize_short_zero run code hsg stack memory gas selector short separate
    zero

/-- Short-name V2 `initializeV2` at a raw history frame preserves an
explicitly supplied zero-row seed at the frame's execution target. -/
theorem implV2_initializeV2_short_zero_rawFrame
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K : B256 → Prop}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames) {post : Devm}
    (ok : R.exn = .ok post) (code : R.sevm.code = ImplV2.code)
    (selector : Blanc.Sevm.selector R.sevm = 0xd608ea64)
    (short : v2InitializerNameLength R.sevm ≤ 31)
    (separate : ∀ key, K key → key ∉ ([4, 15, 18] : List B256))
    (zero : ZeroSlots K R.sevm.currentTarget R.devm) :
    ZeroSlots K R.sevm.currentTarget post := by
  obtain ⟨pc, -, hsg, ⟨stack, memory⟩, -⟩ :=
    history.rawFrame_entryFacts capabilities R member
  rcases R with ⟨pc', sevm, pre, out, run⟩
  dsimp only at pc hsg stack memory ok code selector short zero ⊢
  subst pc ok
  exact implV2_initializeV2_short_zero run code hsg stack memory selector short separate zero

/-- **V1 `initialize` leaves tracked rows non-increasing, step by step.** With the tracked keys
`K` apart from the initializer's fixed slots and from the payload keys of its decoded strings
(frame-local key separation), every store of a successful raw V1 `initialize` frame at a key of
`K` does not raise it. Any string length is allowed. -/
theorem implV1_initialize_rowNonInc_rawFrame
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K : B256 → Prop}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames) {post : Devm}
    (ok : R.exn = .ok post) (code : R.sevm.code = ImplV1.code)
    (selector : Blanc.Sevm.selector R.sevm = 0x3357162b)
    (fixedApart : ∀ key, K key → key ∉ fixedSlots)
    (payloadApart : ∀ key, K key → ¬ OldInitializerV1Callee.PayloadKey R.sevm key) :
    SProg.RunP (fun s d n d' => StepIn R s d n d' ∧ GuardObs K False s d n ∧ ∀ x, n ≠ .exec x)
      ImplV1.cert.prog R.sevm R.devm post := by
  refine SProg.RunP.mono ?_
    (implV1_initialize_observed_rawFrame history capabilities member ok code selector)
  intro s d n d' ⟨step, observed, noExec⟩
  refine ⟨step, ?_, noExec⟩
  intro store key value rest shape tracked
  rcases observed store key value rest shape with fixed | zero | payload
  · exact (fixedApart key tracked fixed).elim
  · rw [zero]
    exact Or.inr (Nat.zero_le _)
  · exact (payloadApart key tracked payload).elim

end Blanc.Lift.Usdc
