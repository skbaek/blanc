import Blanc.ExecutionInCodeImageSafe
import Blanc.ExecutionStagedRootFacts
import Blanc.ExecutionStagedSstoreAttribution
import Blanc.Lift.CallRestriction

/-!
# Raw-frame safety from the codes run in a protected storage context

`ExecutionTrace.SafeRawFrames wa roots` (`Blanc/ExecutionNoDelSafeHistory.lean`)
excludes decoded `SELFDESTRUCT` at every node of every listed frame whose
executing storage context is `wa`. Every such node lies in the same-frame
prefix of a raw frame root with the same `Sevm`
(`Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix`), so the premise follows
from the code each raw frame root in context `wa` runs: when that code
belongs to a family whose members each have a checked certificate without
SELFDESTRUCT terminals, the certificate cursor excludes it
(`Lift.not_selfdestruct_of_parentPrefix_noStateGas`).

* `SafeRawFrames.of_entryCodes`: any descent-closed list of raw roots;
* `ConfiguredHistoryTraceIn.safeRawFrames_of_codes`: a selected-domain
  history, whose raw frames are closed under descent and start at pc `0`
  without state gas (`rawFrames_closed`, `rawFrame_entryFacts`);
* `ConfiguredHistoryTraceIn.rawFrames_codeImage_of_codes` and
  `settled_codeImage_of_codes`: the per-frame code image of
  `Blanc/ExecutionInCodeImageSafe.lean` with this safety premise produced.

The family premise (which code runs in `wa`'s storage context at each raw
frame) is the caller's obligation; nothing here bounds the codes a
`DELEGATECALL` may run.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- **Raw safety from the codes run in context `wa`.** For a list of raw roots
closed under descent, if every listed root executing in `wa`'s storage context
starts at pc `0` without state gas and runs a code of a certified
SELFDESTRUCT-free family, every listed frame is safe at `wa`. -/
theorem SafeRawFrames.of_entryCodes {wa : Adr} {Fam : ByteArray → Prop}
    (certified : ∀ C, Fam C →
      ∃ c : Lift.Cert, Lift.Cert.check C c = true ∧ c.noSelfdestruct = true)
    {roots : List Exec.Deriv} (closed : RawFramesClosed roots)
    (entry : ∀ R ∈ roots, R.sevm.currentTarget = wa →
      R.pc = 0 ∧ R.sevm.benvStat.rules.stateGas = none ∧ Fam R.sevm.code) :
    SafeRawFrames wa roots := by
  intro R member node hnode target
  obtain ⟨G, hG, chain⟩ :=
    (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix R.exc node).mp hnode
  have hsevm := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [hsevm] at target
  obtain ⟨pc, hsg, fam⟩ := entry G (closed R member G hG) target
  obtain ⟨c, hc, noSelfdestruct⟩ := certified _ fam
  exact Lift.not_selfdestruct_of_parentPrefix_noStateGas hc noSelfdestruct pc rfl hsg chain

/-- **Raw safety of a selected-domain history** from the codes its raw frames
run in `wa`'s storage context. -/
theorem ConfiguredHistoryTraceIn.safeRawFrames_of_codes {wa : Adr}
    {Fam : ByteArray → Prop}
    (certified : ∀ C, Fam C →
      ∃ c : Lift.Cert, Lift.Cert.check C c = true ∧ c.noSelfdestruct = true)
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (codes : ∀ R ∈ history.rawFrames, R.sevm.currentTarget = wa → Fam R.sevm.code) :
    SafeRawFrames wa history.rawFrames :=
  SafeRawFrames.of_entryCodes certified history.rawFrames_closed fun R member target =>
    have facts := history.rawFrame_entryFacts capabilities R member
    ⟨facts.1, facts.2.2.1, codes R member target⟩

/-- **A protected code at every raw frame**, from the codes run in its storage
context: the code image of `rawFrames_codeImage_of_safe` with its safety
premise produced by `safeRawFrames_of_codes`. -/
theorem ConfiguredHistoryTraceIn.rawFrames_codeImage_of_codes {wa : Adr} {C : ByteArray}
    {Fam : ByteArray → Prop}
    (certified : ∀ C, Fam C →
      ∃ c : Lift.Cert, Lift.Cert.check C c = true ∧ c.noSelfdestruct = true)
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (installed : checkpoint.state.getCode wa = C)
    (codes : ∀ R ∈ history.rawFrames, R.sevm.currentTarget = wa → Fam R.sevm.code) :
    ∀ R ∈ history.rawFrames, R.devm.getCode wa = C :=
  history.rawFrames_codeImage_of_safe hCdel hCne capabilities installed
    (history.safeRawFrames_of_codes certified capabilities codes)

/-- **A protected code at every settled frame**, from the codes run in its
storage context. -/
theorem ConfiguredHistoryTraceIn.settled_codeImage_of_codes {wa : Adr} {C : ByteArray}
    {Fam : ByteArray → Prop}
    (certified : ∀ C, Fam C →
      ∃ c : Lift.Cert, Lift.Cert.check C c = true ∧ c.noSelfdestruct = true)
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (installed : checkpoint.state.getCode wa = C)
    (codes : ∀ R ∈ history.rawFrames, R.sevm.currentTarget = wa → Fam R.sevm.code) :
    ∀ f ∈ history.settledFrames, f.pre.getCode wa = C :=
  history.settled_codeImage_of_safe hCdel hCne capabilities installed
    (history.safeRawFrames_of_codes certified capabilities codes)

end ExecutionTrace

end Blanc
