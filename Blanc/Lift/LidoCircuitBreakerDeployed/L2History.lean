import Blanc.Lift.LidoCircuitBreakerDeployed.History
import Blanc.ExecutionTraceEntry
import Blanc.ExecutionTraceAdmission
import Blanc.Lift.LidoCircuitBreakerDeployed.Reentry

/-!
# L2 for the `registerPauser(t, 0)` frames of a configured history

`l2_registerPauser_zero` (`L2Frame.lean`) is a statement about one frame: it takes fresh
entry, the selector and calldata word, `EntryAt lidoA` at the frame's entry, the installed
code, and a `RegistryWitness` of the frame's entry storage.  Here the frame is a raw root
retained by an admitted configured history, and what the history determines is derived:

* pc zero and the covered fork (`ConfiguredHistoryTrace.rootEntry`);
* fresh entry (`ConfiguredHistoryTrace.freshFrameAdmitted`);
* `EntryAt lidoA` (from the history's admission `trace.FrameAdmitted ca (lidoEntry lidoA)` at
  the raw root, `frameAdmitted_iff_rawFrames`).

The raw-root wrapper `lido_history_l2_frame` still takes a witness of that frame's entry
registry; `lido_history_l2_frame_of_inv` takes its entry invariant as a premise.  The committed
history result below closes this gap for settlement-committed non-static frames:
`lido_history_l2_committed` derives the entry witness from the checkpoint's `StateInv` and the
actual execution, including reentry from `pause`.  It uses the configured-history entry
accounting and the Lido spawn obligation, while retaining the history-wide `lidoEntry lidoA`
admission premise.  Frames rolled back by an ancestor and static frames remain outside the
committed theorem's stated scope.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc
open Blanc.Lift
open Blanc.LidoCircuitBreaker
open Blanc.ExecutionTrace

/-- A byte array whose list is the deployed image is the deployed code. -/
theorem eq_code_of_image {b : ByteArray} (h : some b.toList = lidoSpec.sem.image) :
    b = code := by
  have h' : b.toList = code.toList := Option.some.inj h
  cases hb : b with
  | mk d =>
    cases hk : code with
    | mk d' =>
      rw [hb, hk, ByteArray.toList_eq_toList_data, ByteArray.toList_eq_toList_data] at h'
      exact congrArg ByteArray.mk (Array.toList_inj.mp h')

/-- **L2 at every committed `registerPauser(t, 0)` frame of a configured history,
with the entry witness derived.**  For an admitted history from a checkpoint
satisfying the Lido state invariant, every settlement-committed non-static frame
at the contract whose calldata is `registerPauser(t, 0)` — including frames
re-entered from inside `pause`'s `CALL` — has a Registry witness `entries` of its
entry storage, and its final storage satisfies `L2Post` relative to it.  The
per-frame premises are only the call shape: membership among the settled frames,
the target, non-static entry, the selector word and the zero pauser word.  Code
identity, pc `0`, the covered fork, fresh entry and the entry witness come from
the history (`ConfiguredHistoryTrace.entryGood_settled`, with the Lido spawn
obligation `lido_spawnEntry`); `EntryAt lidoA` comes from the admission hypothesis
`admitted`, which states it at every raw frame at the contract (re-entered ones
included), as for `lido_history_l2_frame`.  Frames rolled back by an ancestor
are not claimed; static frames are not observed by the accounting ladder. -/
theorem lido_history_l2_committed
    {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : trace.FrameAdmitted ca (lidoEntry lidoA))
    (inv : lidoSpec.StateInv ca checkpoint.state)
    (frame : Exec.Frame) (member : frame ∈ trace.settledFrames)
    (target : frame.sevm.currentTarget = ca) (nonstatic : frame.sevm.isStatic = false)
    (hsig : Sevm.dataWord frame.sevm 0 >>> 224 = selector "registerPauser" [.address, .address])
    (hnp0 : Sevm.dataWord frame.sevm 36 = 0) :
    ∃ entries, RegistryWitness (solRegistryStorage (Devm.getStor frame.pre ca)) entries ∧
      L2Post entries (Sevm.dataWord frame.sevm 4) (Devm.getStor frame.post ca) := by
  obtain ⟨-, good⟩ := ConfiguredHistoryTrace.entryGood_settled (c := lidoSpec)
    (I := fun s => RegInv s) trace ((trace.freshFrameAdmitted ca).and admitted) inv inv.inv
    (lidoSpec_preservesAdmitted_mem lidoWriterSpecsM ca) (lido_framePreserves ca)
    (lido_spawnKinds ca) (lido_spawnEntry ca)
  obtain ⟨hpc, fork, installed, ⟨hfresh, -, hA⟩, ⟨entries, hwit⟩⟩ :=
    good frame member target nonstatic
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := frame
  dsimp only at hpc fork installed hfresh hA hwit target hsig hnp0 ⊢
  subst hpc
  subst target
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    have hinstalled : Devm.getCode pre sevm.currentTarget = code := eq_code_of_image installed.1
    have hcode : sevm.code = Devm.getCode pre sevm.currentTarget := by
      rw [hinstalled]
      exact eq_code_of_image (installed.2 rfl).1
    exact ⟨entries, hwit,
      l2_registerPauser_zero fork hinstalled hcode hfresh hsig hA hwit hnp0 run⟩

end Blanc.Lift.LidoCircuitBreakerDeployed
