import Blanc.Lift.BeaconDeposit.Safe
import Blanc.Lift.BeaconDeposit.DepositExec
import Blanc.Lift.BeaconDeposit.Views

/-!
# Headline corollaries for the deployed runtime (B3): rejection, frame histories, OPEN-1

Corollaries of the per-frame refinement `deposit_frame_refines` (`Safe.lean`) and the view
theorems (`Views.lean`), over real Jaune executions of the deployed bytes:

* `deposit_reject_no_success`: a `deposit` call whose calldata is not `DepositDecodable`, or on
  which the model's `deposit` returns an error, has no successful frame execution;
* `FrameHistory` / `frameHistory_solInv`: a chain of successful frames, each starting from the
  previous one's post-storage of the contract, extends the storage abstraction by exactly the
  model nodes of the `deposit`-selector frames in order; `frameHistory_root_view` and
  `frameHistory_count_view` read the resulting mixed root and count through the deployed views;
* `solInv_inv`, `solInv_root`, `solInv_count`: the OPEN-1 transfer. `SolInv stor history`
  (`Layout.lean`) contains the model invariant `Inv Bytes.sha256 (solAcc stor) history` as its
  second conjunct by definition, so `root_correct` and `deposit_inv` apply to the deployed
  contract's storage.

## Register rows (`BEACON_DEPOSIT_ASSURANCE.md`) and their deployed-runtime counterparts

* OPEN-1: `solInv_inv` (with `solInv_root`, `solInv_count`); the model theorems themselves are
  unchanged.
* P1: not covered here: the deployed bytes are fixed by the B1 certificate (`Check.lean`), not
  compiled by Blanc.
* P2: `deposit_exec_solInv` (`DepositExec.lean`), liveness of a model-accepted deposit.
* P3: `deposit_reject_no_success`, success-only: no revert data, route, or retained-effect
  statement (the lift bridges only relate successful executions).
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

/-! ## OPEN-1 transfer -/

/-- **OPEN-1 transfer.**  The storage abstraction carries the model invariant for its history,
so the model theorems (`root_correct`, `deposit_inv`) apply to the deployed contract's storage. -/
theorem solInv_inv {stor : Stor} {history : List B256} (h : SolInv stor history) :
    BeaconDeposit.Inv Bytes.sha256 (solAcc stor) history :=
  h.2

theorem solInv_root {stor : Stor} {history : List B256} (h : SolInv stor history) :
    BeaconDeposit.Acc.root Bytes.sha256 (solAcc stor) =
      BeaconDeposit.mixedRootOf Bytes.sha256 history :=
  BeaconDeposit.root_correct _ _ _ (solInv_inv h)

theorem solInv_count {stor : Stor} {history : List B256} (h : SolInv stor history) :
    (solAcc stor).count = history.length :=
  (solInv_inv h).1

/-! ## P3: rejected deposits have no successful frame -/

/-- **P3 counterpart (success-only).**  Under `deposit_frame_refines`'s premises, a frame whose
selector is `deposit`'s and whose calldata is not `DepositDecodable`, or on whose decoded
arguments the model's `deposit` returns an error, has no successful execution.  Revert data,
the reverting route, and the identity of the model error with the deployed code's revert are not
covered: the lift bridges relate successful executions only. -/
theorem deposit_reject_no_success {sevm : Sevm} {pre post : Devm} {history : List B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (hsha : ShaReady sevm pre)
    (hinv : SolInv (Devm.getStor pre sevm.currentTarget) history)
    (hsel : Sevm.selector sevm = BeaconDeposit.depositSelector)
    (hrej : ¬ DepositDecodable sevm ∨
      ∃ r, BeaconDeposit.deposit Bytes.sha256 (solAcc (Devm.getStor pre sevm.currentTarget))
        (argBytes sevm 0) (argBytes sevm 1) (argBytes sevm 2) (argRoot sevm)
        sevm.value.toNat = .error r) :
    IsEmpty (Exec 0 sevm pre (.ok post)) := by
  refine ⟨fun exc => ?_⟩
  obtain ⟨hdec, s', ev, hOk, -⟩ :=
    (deposit_frame_refines hcode hfork hcd hstack hmem hsha hinv exc).1 hsel
  rcases hrej with hnd | ⟨r, herr⟩
  · exact hnd hdec
  · rw [hOk] at herr; cases herr

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

/-- **P8 counterpart: an admitted history of frames.**  From the storage abstraction for `h₀`,
a chain of successful frames ends in the abstraction for `h₀` extended by exactly the nodes of
its `deposit`-selector frames, in order. -/
theorem frameHistory_solInv {ca : Adr} {stor₀ stor : Stor} {accepted h₀ : List B256}
    (hh : FrameHistory ca stor₀ accepted stor) (hinv : SolInv stor₀ h₀) :
    SolInv stor (h₀ ++ accepted) := by
  induction hh generalizing h₀ with
  | nil => rw [List.append_nil]; exact hinv
  | cons hca hpre hcode hfork hcd hstack hmem hsha exc _ ih =>
    subst hca hpre
    rw [← List.append_assoc]
    exact ih (frame_solInv hcode hfork hcd hstack hmem hsha hinv exc)

/-- **P8-READ counterpart (root).**  After a frame history from the abstraction for `h₀`, the
deployed `get_deposit_root()` returns the mixed root of `h₀` extended by the accepted nodes. -/
theorem frameHistory_root_view {stor₀ stor : Stor} {accepted h₀ : List B256}
    (sevm : Sevm) (base : Devm) (G : Nat)
    (hh : FrameHistory sevm.currentTarget stor₀ accepted stor) (hinv : SolInv stor₀ h₀)
    (hcode : sevm.code = code)
    (hdataLength : 4 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = Blanc.BeaconDeposit.getDepositRootSelector)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hstor : Devm.getStor base sevm.currentTarget = stor)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : G + rootViewGas sevm base (h₀ ++ accepted).length + 6000 < 2 ^ 256) :
    ∃ post, Nonempty (Exec 0 sevm
        (base.setMach ⟨[], Mem.empty, G + rootViewGas sevm base (h₀ ++ accepted).length,
          base.stateGas⟩) (.ok post)) ∧
      post.gasLeft = G ∧
      post.output = (Blanc.BeaconDeposit.mixedRootOf Bytes.sha256 (h₀ ++ accepted)).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor base a) ∧
      post.logs = base.logs :=
  get_deposit_root_exec_mixedRoot sevm base stor (h₀ ++ accepted) G hcode hdataLength hdataBound
    hvalue hselector hfork hstor (frameHistory_solInv hh hinv) hnodeleg hwarm hpre hdepth hbound

/-- **P8-READ counterpart (count).**  After a frame history from the abstraction for `h₀`, the
deployed warm `get_deposit_count()` returns the little-endian length of `h₀` extended by the
accepted nodes. -/
theorem frameHistory_count_view {stor₀ stor : Stor} {accepted h₀ : List B256}
    (sevm : Sevm) (base : Devm) (G : Nat)
    (hh : FrameHistory sevm.currentTarget stor₀ accepted stor) (hinv : SolInv stor₀ h₀)
    (hcode : sevm.code = code)
    (hdataLength : 4 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = Blanc.BeaconDeposit.getDepositCountSelector)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hwarm : (⟨sevm.currentTarget, countSlot⟩ : Adr × B256) ∈ base.accessedStorageKeys)
    (hstor : Devm.getStor base sevm.currentTarget = stor) :
    ∃ Mf, Nonempty (Exec 0 sevm
        (base.setMach ⟨[], Mem.empty, G + countGasWarm, base.stateGas⟩)
        (.ok ((base.setMach ⟨[Sevm.selector sevm], Mf, G, base.stateGas⟩).withOutput
          (Blanc.BeaconDeposit.abiDynamicBytesReturn
            (Blanc.BeaconDeposit.le64 (h₀ ++ accepted).length))))) :=
  get_deposit_count_warm_exec_history sevm base stor (h₀ ++ accepted) G hcode hdataLength
    hdataBound hvalue hselector hfork hwarm hstor (frameHistory_solInv hh hinv)

end Blanc.Lift.BeaconDeposit
