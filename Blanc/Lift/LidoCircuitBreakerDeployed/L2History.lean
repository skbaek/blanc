import Blanc.Lift.LidoCircuitBreakerDeployed.History
import Blanc.ExecutionTraceEntry
import Blanc.ExecutionTraceAdmission

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

What the history does **not** hand over is the incoming Registry invariant at the frame's own
entry.  The configured-history ladder (`ConfiguredHistoryTrace.stateInv_admitted`) transports
`lidoSpec.StateInv` between block boundaries; inside a transaction, the invariant at a nested
frame's entry is the parent's state at its `CALL`, and neither the frame-level ladder nor the
accounting ladder (`Exec.coreAccounting`, whose target handler sees only `sem.At`) exports it
for a frame entered below another Lido frame or below a frame that later fails.  So the
statement is relative to every witness of the entry storage (`lido_history_l2_frame`), and the
existential form takes the entry invariant as its one open premise
(`lido_history_l2_frame_of_inv`).
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc
open Blanc.Lift
open Blanc.LidoCircuitBreaker
open Blanc.ExecutionTrace

/-- **L2 at every successful `registerPauser(t, 0)` frame a configured history retains, for
every witness of the frame's entry storage.**  The frame is any raw root `root` at the
contract (a top-level message frame or a frame entered below one, whatever it does later);
the history supplies pc zero, the covered fork, fresh entry and `EntryAt lidoA`
(`hadmitted`), and the frame's own code identity and calldata are stated per frame. -/
theorem lido_history_l2_frame
    {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : trace.FrameAdmitted ca (lidoEntry lidoA))
    (root : Exec.Deriv) (member : root ∈ trace.rawFrames)
    (target : root.sevm.currentTarget = ca)
    (hinstalled : Devm.getCode root.devm ca = code)
    (hcode : root.sevm.code = Devm.getCode root.devm ca)
    (hsig : Sevm.dataWord root.sevm 0 >>> 224 = selector "registerPauser" [.address, .address])
    (hnp0 : Sevm.dataWord root.sevm 36 = 0)
    {post : Devm} (ok : root.exn = .ok post) :
    ∀ entries, RegistryWitness (solRegistryStorage (Devm.getStor root.devm ca)) entries →
      L2Post entries (Sevm.dataWord root.sevm 4) (Devm.getStor post ca) := by
  obtain ⟨pcZero, fork⟩ := trace.rootEntry root member
  have fresh : trace.FrameAdmitted ca Exec.FreshEntry := trace.freshFrameAdmitted ca
  have entry := (trace.frameAdmitted_iff_rawFrames ca (lidoEntry lidoA)).1 admitted root member
    target
  have freshEntry := (trace.frameAdmitted_iff_rawFrames ca Exec.FreshEntry).1 fresh root member
    target
  obtain ⟨pc, sevm, pre, exn, run⟩ := root
  dsimp only at pcZero fork target hinstalled hcode hsig hnp0 ok freshEntry entry ⊢
  subst pcZero
  subst ok
  subst target
  intro entries hwit
  exact l2_registerPauser_zero fork hinstalled hcode freshEntry hsig entry.2 hwit hnp0 run

/-- The existential form: given the Registry invariant at the frame's entry storage, a
witness `entries` of it exists and the frame's final storage satisfies `L2Post` relative to
it.  `hinv` is the one premise the history does not derive (see the module docstring). -/
theorem lido_history_l2_frame_of_inv
    {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : trace.FrameAdmitted ca (lidoEntry lidoA))
    (root : Exec.Deriv) (member : root ∈ trace.rawFrames)
    (target : root.sevm.currentTarget = ca)
    (hinstalled : Devm.getCode root.devm ca = code)
    (hcode : root.sevm.code = Devm.getCode root.devm ca)
    (hsig : Sevm.dataWord root.sevm 0 >>> 224 = selector "registerPauser" [.address, .address])
    (hnp0 : Sevm.dataWord root.sevm 36 = 0)
    {post : Devm} (ok : root.exn = .ok post)
    (hinv : RegInv (Devm.getStor root.devm ca)) :
    ∃ entries, RegistryWitness (solRegistryStorage (Devm.getStor root.devm ca)) entries ∧
      L2Post entries (Sevm.dataWord root.sevm 4) (Devm.getStor post ca) := by
  obtain ⟨entries, hwit⟩ := hinv
  exact ⟨entries, hwit, lido_history_l2_frame trace admitted root member target hinstalled
    hcode hsig hnp0 ok entries hwit⟩

end Blanc.Lift.LidoCircuitBreakerDeployed
