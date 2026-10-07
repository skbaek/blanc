import Blanc.Lift.Curve3Crv.Safe
import Blanc.StorageOnlySpec
import Blanc.ContractAdmissionSem
import Blanc.ExecutionHistoryAdmission
import Blanc.ExecutionTraceFresh

/-!
# The 3Crv storage abstraction at history altitude

The 3Crv counterpart of `Blanc/Lift/BeaconDeposit/Ladder.lean`, reduced to its top rung.
`c3crvSem` is the certified code semantics of the deployed runtime (`code`); `c3crvSpec` is the
storage-only frame contract whose invariant is `∃ s K, VyInv (getStor ca) s K`: the contract's
storage abstracts, over some set of live keys, *some* model state.  `VyInv` carries the model's
conservation invariant (`VyInv.conserved : Conserved s`), so no separate conjunct is needed.  The
side condition is `True` (the invariant reads storage only; the balance obligations are the
`StorageOnlySpec` rewrites).

Frame soundness (`c3crvSpec_soundAdmitted`) uses `c3crv_frame_refines_raw` (`Safe.lean`): a writer
frame's post storage abstracts the model's post state over the extended live keys, every other
successful frame keeps every storage map.  The only call the contract makes is `set_name`'s
`STATICCALL` to the minter, which `c3crv_frame_refines_raw` already accounts for (a static callee
writes no storage), so the deeper-frame hypothesis is not consumed.

## The frame premises of `c3crv_frame_refines_raw`

* `CoveredFork`, the code (`sevm.code = code`): given by the ladder (`hfork`, `c3crvSem.Run`).
* empty stack and memory at frame start (`Exec.FreshEntry`): **discharged** at the history rung
  by `ConfiguredHistoryTrace.freshFrameAdmitted`, since every retained interpreter root is a
  freshly entered frame.  The frame-level soundness theorem, which starts from an arbitrary
  machine, takes it as part of `c3crvFrameEntry`.

Carried in `c3crvEntry` (the only entry condition the history rung asks for), each because frame
semantics does not supply it:

* `sevm.data.length < 2 ^ 256`: a transaction's calldata is an unbounded `Bytes` in the model;
  the bound is a fact about real transactions, not about the frame relation.
* `∃ s K, VyInv (pre.getStor ca) s K ∧ FreshKeys K (callKeys caller (decodeCall sevm))`: some
  abstraction of the entry storage under which the keys this call touches are fresh (each live
  or on a slot not in use, and pairwise on distinct slots).  It is a keccak-collision fact about
  this frame's keys against the slots in use (`Layout.lean`, module note), which no rung states.
  It is existential on purpose: the live-key set is history information that storage does not
  record, and the universal form (`∀ s K, VyInv … → FreshKeys K …`) is almost surely false for
  every frame touching a new key, because an abstraction may add, as a zero-valued live key,
  an allowance key whose slot equals the new key's slot (such a preimage almost surely exists).
  For a real history the history's own live-key set is a witness whenever the frame's touched
  slots avoid a collision with a slot in use.

The existential entry abstraction includes `VyInv.conserved`.  Thus this legacy rung assumes a
conserving abstraction anew at each target entry; it does not compose one initial model witness
through the history.  `CarriedHistory.lean`'s `c3crv_history_carried` supplies that composition using
independent calldata and raw-history key-separation premises.

The rung is over retained traces (`ConfiguredHistoryTrace`), as for WETH9 and the beacon deposit
contract.  By user rule only the top rung is stated; the message, transaction, body and block
rungs follow from the same `c3crvSpec_preservesAdmitted` exactly as in the beacon ladder.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune
open Blanc
open Blanc.Lift
open Blanc.ExecutionTrace

theorem code_toList_length : code.toList.length = 2276 := by
  rw [ByteArray.toList_eq_toList_data, Array.length_toList]
  decide +kernel

/-- The certified semantics of the deployed 3Crv runtime: the frame runs its bytes. -/
def c3crvSem : CodeSem where
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
    have hlen : c.toList.length = 2276 := h ▸ code_toList_length
    rw [ByteArray.toList_eq_toList_data, Array.length_toList] at hlen
    have hsize : c.size = eoaDelegatedCodeLength := hdel.1
    have hsz : c.size = c.data.size := rfl
    rw [hsz, hlen] at hsize
    exact absurd hsize (by decide)

end Blanc.Lift.Curve3Crv
