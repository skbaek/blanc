import Blanc.Lift.BeaconDeposit.Safe
import Blanc.StorageOnlySpec
import Blanc.ContractAdmissionSem
import Blanc.ExecutionHistoryAdmission
import Blanc.ExecutionTraceFresh

/-!
# The beacon deposit invariant at frame and history altitude

The beacon counterpart of `Blanc/Lift/Weth9/Solvency.lean`.  `beaconSem` is the certified code
semantics of the deployed runtime (`code`); `beaconSpec` is the storage-only frame contract whose
invariant is `∃ h, SolInv (getStor ca) h`: the contract's storage abstracts, through the
constructor's zero-hash table and the incremental branch, the model state of *some* deposit
history.  The side condition is `True` (the invariant reads storage only; the balance
obligations are the `StorageOnlySpec` rewrites).

Frame soundness (`beaconSpec_soundAdmitted`) is `deposit_frame_refines` (`Safe.lean`): a
`deposit` frame extends the history by the model's node, every other successful frame keeps
every storage map.  The contract makes no call other than the SHA-256 precompile, so the
deeper-frame hypothesis is not consumed.

## The frame premises of `deposit_frame_refines`

* `CoveredFork`, the code (`sevm.code = code`): given by the ladder (`hfork`, `beaconSem.Run`).
* `isPrecomp 2` (part of `ShaReady`): discharged from `CoveredFork` (`isPrecomp_two`).
* empty stack and memory at frame start (`Exec.FreshEntry`): **discharged** at the history rung
  by the existing `*.freshFrameAdmitted` theorems, since every retained interpreter root is a
  freshly entered frame.  At frame altitude (`beaconSpec_soundAdmitted`), which starts from an
  arbitrary machine, it is part of the admitted entry `beaconFrameEntry`.

Carried in `beaconEntry` (the only entry condition the history rung asks for), each because frame
semantics does not supply it:

* `sevm.data.length < 2 ^ 256`: a transaction's calldata is an unbounded `Bytes` in the model;
  the bound is a fact about real transactions, not about the frame relation.
* `getDelegatedCodeAddress (pre.getCode 2) = none`: a fact about the code stored at account `2`
  in the world state, which the frame relation leaves arbitrary.
* `(2 : Adr) ∈ pre.accessedAddresses`: EIP-2929 pre-warms precompiles at transaction start and
  the accessed set only grows within a transaction, but no rung states that invariant, and a
  system message starts with an empty accessed set.  The segment inversions
  (`ri_staticcall_sha`) are stated for a warm call; a cold call adds `2` to the accessed set, so
  the `Keep` bookkeeping of the segments would not hold.

No call-depth condition is carried: at the maximal call depth (`sevm.depth = 0`) the SHA-256
`STATICCALL` fails and pushes `0`, which is the failure disjunct of `ri_staticcall_sha`.

The history rung is over retained traces (`ConfiguredHistoryTrace`), as for WETH9.  It is the
only contract-level rung kept: the message, transaction and block altitudes are one-line
instances of the same generic `*_admitted_sem` theorems at `beaconSpec_preservesAdmitted`.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune
open Blanc
open Blanc.Lift
open Blanc.ExecutionTrace

theorem code_toList_length : code.toList.length = 6358 := by
  rw [ByteArray.toList_eq_toList_data, Array.length_toList]
  decide +kernel

/-- The certified semantics of the deployed beacon deposit runtime: the frame runs its bytes. -/
def beaconSem : CodeSem where
  image := some code.toList
  Run sevm _ _ := sevm.code = code
  correct := by
    intro sevm pre post _ hcode
    have h : sevm.code.toList = code.toList := Option.some.inj hcode
    cases hs : sevm.code with
    | mk d =>
      cases hk : code with
      | mk d' =>
        rw [hs, hk] at h
        rw [ByteArray.toList_eq_toList_data, ByteArray.toList_eq_toList_data] at h
        exact congrArg ByteArray.mk (Array.toList_inj.mp h)
  ne_nil := by
    intro l hl h
    have h' : code.toList = l := Option.some.inj hl
    have hlen := code_toList_length
    rw [h', h] at hlen
    exact absurd hlen (by decide)
  not_delegation := by
    intro c hc hdel
    have h : c.toList = code.toList := Option.some.inj hc
    have hlen : c.toList.length = 6358 := h ▸ code_toList_length
    rw [ByteArray.toList_eq_toList_data, Array.length_toList] at hlen
    have hsize : c.size = eoaDelegatedCodeLength := hdel.1
    have hsz : c.size = c.data.size := rfl
    rw [hsz, hlen] at hsize
    exact absurd hsize (by decide)

/-- **The beacon deposit frame contract**: the storage abstracts the model state of some deposit
history. -/
def beaconSpec : ContractSpecSem where
  sem := beaconSem
  Inv := fun s _ _ => ∃ history, SolInv s history
  Side := fun _ => True
  inv_forget := id
  inv_mono := fun h _ => h
  inv_recv := fun h _ => h
  side_le := fun _ _ => trivial
  side_transfer := fun _ _ => trivial
  side_addBal := fun _ _ => trivial
  inv_transfer := by
    intro st st' caller callee ca wad v h_sub _ _ h_inv
    show ∃ history, SolInv _ history
    rw [getStor_subBal_addBal h_sub]
    exact h_inv
  inv_recv_transfer := by
    intro st st' caller ca wad h_sub _ _ h_inv
    show ∃ history, SolInv _ history
    rw [getStor_subBal_addBal h_sub]
    exact h_inv
  inv_addBal := by
    intro w ca a val v _ _ h_inv
    show ∃ history, SolInv _ history
    rw [getStor_addBal]
    exact h_inv

/-- The SHA-256 precompile is a precompile on every covered fork. -/
theorem isPrecomp_two {sevm : Sevm} (hfork : CoveredFork sevm.benvStat.fork) :
    decide (sevm.benvStat.rules.isPrecomp 2) = true :=
  decide_eq_true <| hfork.cases (motive := fun f => (Fork.ruleSet f).isPrecomp 2)
    (by decide) (by decide) (by decide) (by decide)

/-- **The carried entry condition** at every entered beacon frame: calldata length, the
precompile account's code is not a delegation, and the precompile is warm.  Each is explained in
the module docstring. -/
def beaconEntry : Sevm → Devm → Prop := fun sevm pre =>
  sevm.data.length < 2 ^ 256 ∧ getDelegatedCodeAddress (pre.getCode 2) = none ∧
    (2 : Adr) ∈ pre.accessedAddresses

/-- The full frame entry: fresh entry (discharged at the history rung) and `beaconEntry`. -/
def beaconFrameEntry : Sevm → Devm → Prop := fun sevm pre =>
  Exec.FreshEntry sevm pre ∧ beaconEntry sevm pre

/-- **Beacon frame soundness, trace-admitted**, from `deposit_frame_refines`. -/
theorem beaconSpec_soundAdmitted (ca : Adr) :
    beaconSpec.SoundAdmitted ca beaconFrameEntry := by
  intro sevm pre post hfork execution hrun hca admitted _ _ hpre
  subst hca
  obtain ⟨⟨hstack, hmem⟩, hcd, hnodeleg, hwarm⟩ := admitted.root rfl
  obtain ⟨history, hinv⟩ := hpre.inv.left rfl
  have hsha : ShaReady sevm pre := ⟨hnodeleg, hwarm, isPrecomp_two hfork, hfork⟩
  have h := deposit_frame_refines hrun hfork hcd hstack hmem hsha hinv execution
  refine ⟨trivial, ?_⟩
  show ∃ history, SolInv (Devm.getStor post sevm.currentTarget) history
  by_cases hsel : Sevm.selector sevm = BeaconDeposit.depositSelector
  · obtain ⟨_, _, _, _, _, hinv', _⟩ := h.1 hsel
    exact ⟨_, hinv'⟩
  · rw [(h.2 hsel).1]
    exact ⟨history, hinv⟩

/-- **Beacon frame preservation, trace-admitted**: the form the history rung consumes. -/
theorem beaconSpec_preservesAdmitted (ca : Adr) :
    beaconSpec.PreservesAdmitted ca beaconFrameEntry :=
  beaconSpec.preserves_inv_admitted ca beaconFrameEntry (beaconSpec_soundAdmitted ca)

/-- History rung: a configured history whose entered beacon frames satisfy `beaconEntry`
preserves the beacon state invariant. -/
theorem beacon_history_preserves_solInv {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : trace.FrameAdmitted ca beaconEntry)
    (inv : beaconSpec.StateInv ca checkpoint.state) :
    beaconSpec.StateInv ca future.state :=
  trace.stateInv_admitted_sem (beaconSpec_preservesAdmitted ca)
    ((trace.freshFrameAdmitted ca).and admitted) inv

end Blanc.Lift.BeaconDeposit
