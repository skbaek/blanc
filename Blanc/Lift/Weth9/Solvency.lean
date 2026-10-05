import Blanc.Lift.Weth9.Frame
import Blanc.ContractAdmissionSem
import Blanc.ExecutionHistoryAdmission

/-!
# WETH9 solvency at frame, message, transaction, block and history altitude

The P1 parity rows for the pinned solc 0.4.19 WETH9 runtime, over the lifted
code semantics `weth9Sem` and the booked-sum frame contract `weth9Spec`
(`Inv = Solvent`, `Side = SumNof`), against Blanc-WETH's `Blanc/Solvent.lean`:

| Blanc-WETH (`Blanc/Solvent.lean`)       | WETH9 (this file)                              |
|-----------------------------------------|------------------------------------------------|
| `wethSpec_sound`                        | `weth9Spec_soundAdmitted`                      |
| `wethSpec_preserves`                    | `weth9Spec_preservesAdmitted`                  |
| `weth_preserves_solvent`                | `weth9_preserves_solvent`                      |
| `exec_preserves_solvent`                | `weth9_exec_preserves_solvent`                 |
| (message call, via the ladder)          | `weth9_messageCall_preserves_solvent`          |
| (transaction list, via the ladder)      | `weth9_applyTransactions_preserves_solvent`    |
| (block body, via the ladder)            | `weth9_appliedBody_preserves_solvent`          |
| `stateTransition_preserves_solvent`     | `weth9_block_preserves_solvent`                |
| `chain_preserves_solvent`               | `weth9_history_preserves_solvent`              |
| `addBlockToChain_preserves_solvent`     | not reached (see below)                        |

**The one qualification.**  Every row carries the trace-local admission
`Exec.FrameAdmitted ca weth9Entry …` (or its trace form): every WETH9 frame the
execution actually enters satisfies `AllowAdmitted`, i.e. the two allowance
slots that frame's `approve`/`transferFrom` could write are off the balance
image.  No global keccak assumption appears anywhere.  Its necessity is the O4
control `approve_collision_control` (`Approve.lean`): with an admitted
collision an approve run ends insolvent.  (`TransferFrom.lean` has no control
lemma of its own.)

`AllowAdmitted` is *universal* over addresses (the allowance slots avoid every address's balance
slot, even at frames that write no allowance), which no collision resistance implies.  The history
headline `weth9_history_footprint` (`FootHistory.lean`) replaces it by a footprint over the finitely
many keys the trace touches, with only trace-local hash premises; this module's rows are kept as they
are (`weth9_history_preserves_solvent` states backing of the deduplicated booked ledger).

**Block and chain rows.**  The admission chain's block and history rungs are
stated over retained traces (`ConfiguredBlockTrace`, `ConfiguredHistoryTrace`),
which carry the frame roots the admission talks about; Blanc-WETH's
`stateTransition`/`BlockChain.Reach` rows are over the executable functions,
where no derivation — hence no admitted root — is available.  The trace rows
are the counterparts.  `addBlockToChain_preserves_solvent` (RLP decoding and
hash checks in front of `stateTransition`) has no admission-chain rung at all,
so it is not reached.
-/

namespace Blanc.Lift.Weth9

open Jaune
open Blanc
open Blanc.Lift
open Blanc.ExecutionTrace

/-- The WETH9 entry condition: the frame's local collision premise. -/
def weth9Entry : Sevm → Devm → Prop := fun sevm _ => AllowAdmitted sevm

/-- **WETH9 frame soundness, trace-admitted.**  Counterpart of `wethSpec_sound`. -/
theorem weth9Spec_soundAdmitted (ca : Adr) : weth9Spec.SoundAdmitted ca weth9Entry := by
  intro sevm pre post hfork execution hrun hca admitted ih _ hpre
  subst hca
  have hin := lift_sound_in cert_check hrun.1 hfork execution
  exact frame_post_in (R := ⟨0, sevm, pre, .ok post, execution⟩) hfork hin
    (admitted.root rfl) admitted ih hpre

/-- **WETH9 frame preservation, trace-admitted.**  Counterpart of
`wethSpec_preserves`; the form the message, transaction and block rungs
consume. -/
theorem weth9Spec_preservesAdmitted (ca : Adr) :
    weth9Spec.PreservesAdmitted ca weth9Entry :=
  weth9Spec.preserves_inv_admitted ca weth9Entry (weth9Spec_soundAdmitted ca)

/-- History rung, counterpart of `chain_preserves_solvent`: a configured
history of blocks whose entered WETH9 frames are admitted preserves the WETH9
state invariant.

For holder-level backing with only trace-local hash premises see `weth9_history_footprint`; this theorem concerns the deduplicated booked-slot ledger under the universal `AllowAdmitted` premise. -/
theorem weth9_history_preserves_solvent {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : trace.FrameAdmitted ca weth9Entry)
    (inv : weth9Spec.StateInv ca checkpoint.state) :
    weth9Spec.StateInv ca future.state :=
  trace.stateInv_admitted_sem (weth9Spec_preservesAdmitted ca) admitted inv

/-- The state invariant is WETH9 solvency, the side condition, and the pinned
code. -/
theorem weth9Spec_stateInv_iff {ca : Adr} {w : State} :
    weth9Spec.StateInv ca w ↔
      (some (w.getCode ca).toList = some code.toList ∧ SumNof w.bal ∧
        Solvent (w.getStor ca) 0 (w.bal ca)) :=
  ⟨fun h => ⟨h.code, h.side, h.inv⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

end Blanc.Lift.Weth9
