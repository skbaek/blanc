import Blanc.Lift.BeaconDeposit.Safe
import Blanc.Lift.BeaconDeposit.DepositExec
import Blanc.Lift.BeaconDeposit.Views

/-!
# Headline corollaries for the deployed runtime (B3): frame histories

Corollaries of the per-frame refinement `deposit_frame_refines` (`Safe.lean`) and the view
theorems (`Views.lean`), over real Jaune executions of the deployed bytes:

* `FrameHistory` / `frameHistory_solInv`: a chain of successful frames, each starting from the
  previous one's post-storage of the contract, extends the storage abstraction by exactly the
  model nodes of the `deposit`-selector frames in order; `frameHistory_root_view` and
  `frameHistory_count_view` read the resulting mixed root and count through the deployed views.

## Register rows (`BEACON_DEPOSIT_ASSURANCE.md`) and their deployed-runtime counterparts

* OPEN-1: `SolInv stor history` (`Layout.lean`) contains the model invariant
  `Inv Bytes.sha256 (solAcc stor) history` as its second conjunct by definition, so
  `root_correct` and `deposit_inv` apply to the deployed contract's storage; the model theorems
  themselves are unchanged.
* P1: not covered here: the deployed bytes are fixed by the B1 certificate (`Check.lean`), not
  compiled by Blanc.
* P2: `deposit_exec_solInv` (`DepositExec.lean`), liveness of a model-accepted deposit.
* P3: the first conjunct of `deposit_frame_refines`, success-only: a successful `deposit`-selector
  frame has `DepositDecodable` calldata on which the model's `deposit` returns `.ok`, so a
  rejected deposit has no successful frame.  No revert data, route, or retained-effect statement
  (the lift bridges only relate successful executions).
* P4: `get_deposit_count_warm_exec`, `get_deposit_count_cold_exec`, `supportsInterface_exec`,
  `get_deposit_root_exec` (`Views.lean`).
* P5: `deposit_frame_refines`, the storage-shape conjunct (writes exactly the count slot and one
  branch slot; other accounts unchanged); no raw instruction-occurrence census and no
  constructor counterpart.
* P6: `deposit_frame_refines` / `deposit_exec_solInv` (preservation) and
  `get_deposit_root_exec_mixedRoot`, `get_deposit_count_warm_exec_history` (projection); no
  construction counterpart (the deployed constructor is not lifted).
* P7: not covered: no deployment transition for the deployed bytes.
* P8-FRAME: `deposit_frame_refines`.
* P8-HISTORY: `frameHistory_solInv`, over an explicit frame chain (`FrameHistory`) rather than
  a configured chain reach witness; the chain premise that each frame starts from the previous
  frame's contract storage is assumed, not derived from block execution.
* P8-READ: `frameHistory_root_view`, `frameHistory_count_view` (warm count read).
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-! ## P8: histories of frames -/

/-- The model node a `deposit` frame appends: the deposit-data node of the decoded arguments
and the call value in gwei. -/
def frameNode (sevm : Sevm) : B256 :=
  BeaconDeposit.depositDataNode Bytes.sha256 (argBytes sevm 0) (argBytes sevm 1)
    (argBytes sevm 2) (BeaconDeposit.le64 (sevm.value.toNat / BeaconDeposit.oneGwei))

/-- The nodes a frame contributes to the history: its node if its selector is `deposit`'s, and
none otherwise. -/
def frameAccepted (sevm : Sevm) : List B256 :=
  if Sevm.selector sevm = BeaconDeposit.depositSelector then [frameNode sevm] else []

/-- `FrameHistory ca stor₀ accepted stor` : a chain of successful frames of the deployed code at
the contract address `ca`, each meeting `deposit_frame_refines`'s per-frame premises and starting
from the previous frame's post-storage of `ca` (the first from `stor₀`), ends with `ca`'s storage
`stor`; `accepted` is the concatenation of the frames' `frameAccepted` in order. -/
inductive FrameHistory (ca : Adr) : Stor → List B256 → Stor → Prop
  | nil (stor : Stor) : FrameHistory ca stor [] stor
  | cons {sevm : Sevm} {pre post : Devm} {stor stor' : Stor} {rest : List B256}
      (hca : sevm.currentTarget = ca)
      (hpre : Devm.getStor pre ca = stor)
      (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
      (hcd : sevm.data.length < 2 ^ 256)
      (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
      (hsha : ShaReady sevm pre)
      (exc : Exec 0 sevm pre (.ok post))
      (tail : FrameHistory ca (Devm.getStor post ca) rest stor') :
      FrameHistory ca stor (frameAccepted sevm ++ rest) stor'

/-- One frame extends the storage abstraction by its accepted nodes. -/
theorem frame_solInv {sevm : Sevm} {pre post : Devm} {history : List B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (hsha : ShaReady sevm pre)
    (hinv : SolInv (Devm.getStor pre sevm.currentTarget) history)
    (exc : Exec 0 sevm pre (.ok post)) :
    SolInv (Devm.getStor post sevm.currentTarget) (history ++ frameAccepted sevm) := by
  have hr := deposit_frame_refines hcode hfork hcd hstack hmem hsha hinv exc
  unfold frameAccepted
  by_cases hsel : Sevm.selector sevm = BeaconDeposit.depositSelector
  · rw [ite_eq_left hsel]
    obtain ⟨-, s', ev, hOk, hacc, hinv', -⟩ := hr.1 hsel
    refine ⟨hinv'.1, ?_⟩
    show BeaconDeposit.Inv Bytes.sha256 _ _
    rw [hacc]
    exact BeaconDeposit.deposit_inv Bytes.sha256 _ _ _ _ _ _ _ _ _ hinv.2 hOk
  · rw [ite_eq_right hsel, List.append_nil, (hr.2 hsel).1]
    exact hinv

end Blanc.Lift.BeaconDeposit
