import Blanc.Lift.BeaconDeposit.CountView
import Blanc.Lift.BeaconDeposit.DepositArgs
import Blanc.Lift.BeaconDeposit.Layout
import Blanc.ForwardStorageAccess
import Blanc.Lift.ExactWalkCutOps

/-!
# The deployed `deposit` body: the vocabulary of its segment statements

The body of the deployed `deposit` (certificate entry 7, pc `0x0304`, through the insertion loop
and the return through entry 21) is proved in segments (`Body*.lean`, composed in `Body.lean`).
This module fixes what the segment statements share:

* `Keep b b'` — the world facts a precompile call (and nothing else) may move: storage, code,
  access sets, logs, output and error of `b'` are `b`'s.  Every segment hands its successor
  a base `b'` with `Keep X b'` for an explicit `X` (the expected base: `afterSload`, `addLog`,
  `afterSstore` of the segment's pre-state, or the pre-state itself).
* `BodyMem M n fp facts` — what a boundary knows of memory: well-formed, of size `n`, and
  reading as an image with the free pointer `fp` at `0x40` and each listed byte string at its
  offset.  All the body's memory addresses are constants (the three lengths are fixed by the
  guards), so `n`, `fp` and the offsets are numerals, except in the insertion loop, where they
  grow by `0x60` per hashing iteration.
* `ShaReady sevm b` (the shared kit's, `Blanc/Lift/ExactWalkCutOps.lean`) — the premises of
  the SHA-256 precompile step, carried across a `Keep` by `ShaReady.keep`.  The liveness
  theorems (the `Body*` segments) take the frame's nonzero depth (`sevm.depth ≠ 0`) as a
  separate premise, since at depth `0` the call fails; the segment inversions (`Safe*`) need
  no depth premise.
* the insertion loop's model quantities (`insertDepth`, `insertNode`) and the body's gas
  (`deadGas`, `deadRun`, `bodyGas`).

The segment boundaries, their stacks, memory sizes, free pointers and gas were read off a
concrete-and-symbolic simulation of the deployed bytes on the success path
(`evidence/beacon-deposit-bytecode-v1/w4` in Plans, `bodysim.py`), whose gas model reproduces the
proved `get_deposit_count` walk (1297 + 100) exactly.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-! ## World frames -/

/-- The world of `b'` is `b`'s, as far as the body can observe: storage, code, access sets,
logs, output, error and the created-account set (which the machine original read
`Devm.getOrigStorVal` consults when pricing an `SSTORE`).  (Balances and the return-data
buffer may differ: the precompile call touches both.) -/
structure Keep (b b' : Devm) : Prop where
  stor : ∀ a, Devm.getStor b' a = Devm.getStor b a
  code : ∀ a, b'.getCode a = b.getCode a
  addrs : b'.accessedAddresses = b.accessedAddresses
  keys : b'.accessedStorageKeys = b.accessedStorageKeys
  logs : b'.logs = b.logs
  output : b'.output = b.output
  error : b'.error = b.error
  created : b'.createdAccounts = b.createdAccounts

theorem Keep.refl (b : Devm) : Keep b b :=
  ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {b b' b'' : Devm} (h : Keep b b') (h' : Keep b' b'') : Keep b b'' :=
  ⟨fun a => (h'.stor a).trans (h.stor a), fun a => (h'.code a).trans (h.code a),
    h'.addrs.trans h.addrs, h'.keys.trans h.keys, h'.logs.trans h.logs,
    h'.output.trans h.output, h'.error.trans h.error, h'.created.trans h.created⟩

theorem _root_.Blanc.Lift.ShaReady.keep {sevm : Sevm} {b b' : Devm} (h : ShaReady sevm b)
    (hk : Keep b b') : ShaReady sevm b' :=
  h.of_eq hk.code hk.addrs

/-! ## Memory at a boundary -/

/-- `M` is well formed, of size `n`, and reads as an image holding the free pointer `fp` at
`0x40` and each `(offset, bytes)` of `facts`. -/
def BodyMem (M : Mem) (n : Nat) (fp : B256) (facts : List (Nat × Bytes)) : Prop :=
  Mem.Wf M ∧ M.size = n ∧
    ∃ img : Bytes, Mem.Reads M img ∧ img.sliceD 64 32 0 = fp.toBytes ∧
      ∀ p ∈ facts, img.sliceD p.1 p.2.length 0 = p.2

/-! ## The arguments -/

/-- The `i`-th dynamic argument's bytes, as the model reads them: `argLen` bytes of calldata
from `argPtr`. -/
def argBytes (sevm : Sevm) (i : Nat) : Bytes :=
  sevm.data.sliceD (argPtr sevm i).toNat (argLen sevm i).toNat 0

/-- The deposit amount in gwei, as the code computes it (`CALLVALUE / 1 gwei`). -/
def gweiAmount (sevm : Sevm) : B256 := sevm.value / (1000000000 : B256)

/-- The `DepositEvent` the code emits, from the three calldata payloads (at the pointers, with
the success path's lengths), the amount word and the count word. -/
def bodyEvent (sevm : Sevm) (pP wP sP amt cnt : B256) : BeaconDeposit.DepositEvent :=
  ⟨sevm.data.sliceD pP.toNat 48 0, sevm.data.sliceD wP.toNat 32 0,
    BeaconDeposit.le64 amt.toNat, sevm.data.sliceD sP.toNat 96 0, BeaconDeposit.le64 cnt.toNat⟩

/-! ## The insertion loop's model quantities -/

/-- The height at which the insertion loop stores: the number of trailing zero bits of the
incremented count `size` (checked for `fuel` heights). -/
def insertDepth : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, size => if size % 2 = 1 then 0 else insertDepth fuel (size / 2) + 1

/-- The node the insertion loop carries at height `h`: `h` combines of `branch[j]` on the left. -/
def insertNode (H : Bytes → B256) (branch : Nat → B256) : Nat → B256 → B256
  | 0, node => node
  | h + 1, node => BeaconDeposit.hashPair H (branch h) (insertNode H branch h node)

/-! ## Gas -/

/-- One hashing (dead) iteration of the insertion loop at height `h`, apart from its `SLOAD`:
867 and the memory expansion from `1024 + 96 h` to `1120 + 96 h` bytes. -/
def deadGas (h : Nat) : Nat :=
  867 + (calculateMemoryGasCost (1120 + 96 * h) - calculateMemoryGasCost (1024 + 96 * h))

/-- `m` dead iterations from height `h`, each with its `SLOAD` charged against the key set
`keys` (the pre-body set: no earlier body access touches a branch slot). -/
def deadRun (tgt : Adr) (keys : KeySet) (h : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => deadGas h + sloadCostOfKeys tgt keys (solBranchSlot h) + deadRun tgt keys (h + 1) m

/-- The storing (live) iteration's `SSTORE` of `node` at `solBranchSlot n`, charged against the
pre-body key set and storage. -/
def liveStoreCost (sevm : Sevm) (keys : KeySet) (stor : Stor) (n : Nat) (node : B256) : Nat :=
  (if (⟨sevm.currentTarget, solBranchSlot n⟩ : Adr × B256) ∈ keys then 0 else gasColdSload) +
    sstoreValueCost (getOrigStorVal sevm sevm.currentTarget (solBranchSlot n))
      (stor.get (solBranchSlot n)) node

/-- The count's `SSTORE` (the key is warm by then). -/
def countStoreCost (sevm : Sevm) (w : B256) : Nat :=
  sstoreValueCost (getOrigStorVal sevm sevm.currentTarget solCountSlot) w (1 + w)

/-- The count word the body reads. -/
def bodyCount (sevm : Sevm) (b : Devm) : B256 :=
  (Devm.getStor b sevm.currentTarget).get solCountSlot

/-- The height at which the body stores: the trailing zero bits of the incremented count. -/
def bodyDepth (sevm : Sevm) (b : Devm) : Nat :=
  insertDepth 32 ((bodyCount sevm b).toNat + 1)

/-- The node the body stores: the supplied root (equal to the reconstructed one on success)
climbed through the dead heights. -/
def bodyNode (sevm : Sevm) (b : Devm) : B256 :=
  insertNode Bytes.sha256 (solAcc (Devm.getStor b sevm.currentTarget)).branch (bodyDepth sevm b)
    (argRoot sevm)

/-- The storing `SSTORE`'s charge. -/
def bodyLiveCost (sevm : Sevm) (b : Devm) : Nat :=
  liveStoreCost sevm b.accessedStorageKeys (Devm.getStor b sevm.currentTarget) (bodyDepth sevm b)
    (bodyNode sevm b)

/-- The insertion loop's gas from its head: the dead iterations and the storing one (143 and
its `SSTORE`). -/
def bodyInsertGas (sevm : Sevm) (b : Devm) : Nat :=
  deadRun sevm.currentTarget b.accessedStorageKeys 0 (bodyDepth sevm b) + (143 + bodyLiveCost sevm b)

/-- **The body's gas** from `b`: 14551 fixed (segments 1882 + 1104 + 6205 + 2526 + 2553 + 281),
the first count `SLOAD` (warm or cold), the count `SSTORE`, and the insertion loop. -/
def bodyGas (sevm : Sevm) (b : Devm) : Nat :=
  14551 + sloadCostOfKeys sevm.currentTarget b.accessedStorageKeys solCountSlot +
    countStoreCost sevm (bodyCount sevm b) + bodyInsertGas sevm b

/-- The storage the body leaves at the contract: the count incremented, the node stored. -/
def bodyStor (sevm : Sevm) (b : Devm) : Stor :=
  ((Devm.getStor b sevm.currentTarget).set solCountSlot (1 + bodyCount sevm b)).set
    (solBranchSlot (bodyDepth sevm b)) (bodyNode sevm b)

/-! ## Machine-original pricing (Jaune `ca9f27d`)

Jaune prices `SSTORE` from the machine read `Devm.getOrigStorVal`, which is `0`
at accounts created in this transaction and the transaction-start snapshot
otherwise. The `...Of` variants below price the body's two stores from a
supplied original word, with `rfl` links back to the snapshot-priced
definitions above; the P2 liveness headers supply the entry base's machine
reads (Option A, decision blanc-repin-os-optionA-delegation-20261012). -/

/-! ## `...Of` cost variants priced from a supplied original word -/

/-- The storing (live) iteration's `SSTORE`, priced from a supplied original
word (see `liveStoreCost`). -/
def liveStoreCostOf (orig : B256) (sevm : Sevm) (keys : KeySet) (stor : Stor)
    (n : Nat) (node : B256) : Nat :=
  (if (⟨sevm.currentTarget, solBranchSlot n⟩ : Adr × B256) ∈ keys then 0 else gasColdSload) +
    sstoreValueCost orig (stor.get (solBranchSlot n)) node

/-- `liveStoreCost` is the `liveStoreCostOf` at the static snapshot read. -/
theorem liveStoreCost_eq_of (sevm : Sevm) (keys : KeySet) (stor : Stor)
    (n : Nat) (node : B256) :
    liveStoreCost sevm keys stor n node =
      liveStoreCostOf (getOrigStorVal sevm sevm.currentTarget (solBranchSlot n))
        sevm keys stor n node := rfl

/-- The count's `SSTORE`, priced from a supplied original word
(see `countStoreCost`). -/
def countStoreCostOf (orig : B256) (w : B256) : Nat :=
  sstoreValueCost orig w (1 + w)

/-- `countStoreCost` is the `countStoreCostOf` at the static snapshot read. -/
theorem countStoreCost_eq_of (sevm : Sevm) (w : B256) :
    countStoreCost sevm w =
      countStoreCostOf (getOrigStorVal sevm sevm.currentTarget solCountSlot)
        w := rfl

/-- `liveStoreCostOf` depends only on the stored cell. -/
theorem liveStoreCostOf_congr {orig : B256} {sevm : Sevm} {keys : KeySet}
    {s t : Stor} {n : Nat} {nd : B256}
    (h : s.get (solBranchSlot n) = t.get (solBranchSlot n)) :
    liveStoreCostOf orig sevm keys s n nd =
      liveStoreCostOf orig sevm keys t n nd := by
  unfold liveStoreCostOf; rw [h]

/-! ## Body-level `...Of` costs -/

/-- The storing `SSTORE`'s charge (`bodyLiveCost`), priced from a supplied original word. -/
def bodyLiveCostOf (orig : B256) (sevm : Sevm) (b : Devm) : Nat :=
  liveStoreCostOf orig sevm b.accessedStorageKeys (Devm.getStor b sevm.currentTarget)
    (bodyDepth sevm b) (bodyNode sevm b)

/-- The insertion loop's gas (`bodyInsertGas`), its `SSTORE` priced from a supplied original
word. -/
def bodyInsertGasOf (orig : B256) (sevm : Sevm) (b : Devm) : Nat :=
  deadRun sevm.currentTarget b.accessedStorageKeys 0 (bodyDepth sevm b) +
    (143 + bodyLiveCostOf orig sevm b)

/-- The body's gas (`bodyGas`), the storing `SSTORE` priced from `origLive` and the count
`SSTORE` from `origCount`. -/
def bodyGasOf (origLive origCount : B256) (sevm : Sevm) (b : Devm) : Nat :=
  14551 + sloadCostOfKeys sevm.currentTarget b.accessedStorageKeys solCountSlot +
    countStoreCostOf origCount (bodyCount sevm b) + bodyInsertGasOf origLive sevm b

theorem bodyLiveCost_eq_of (sevm : Sevm) (b : Devm) :
    bodyLiveCost sevm b =
      bodyLiveCostOf (getOrigStorVal sevm sevm.currentTarget (solBranchSlot (bodyDepth sevm b)))
        sevm b := rfl

theorem bodyInsertGas_eq_of (sevm : Sevm) (b : Devm) :
    bodyInsertGas sevm b =
      bodyInsertGasOf
        (getOrigStorVal sevm sevm.currentTarget (solBranchSlot (bodyDepth sevm b))) sevm b := rfl

theorem bodyGas_eq_of (sevm : Sevm) (b : Devm) :
    bodyGas sevm b =
      bodyGasOf (getOrigStorVal sevm sevm.currentTarget (solBranchSlot (bodyDepth sevm b)))
        (getOrigStorVal sevm sevm.currentTarget solCountSlot) sevm b := rfl

/-! ## Machine-read connection -/

/-- `sstoreCost` is the `liveStoreCostOf` at the machine's own storage and key
set, with the machine original read. -/
theorem sstoreCost_eq_liveStoreCostOf_self {sevm : Sevm} {b : Devm}
    {n : Nat} {nd : B256} :
    sstoreCost sevm b (solBranchSlot n) nd =
      liveStoreCostOf (b.getOrigStorVal sevm sevm.currentTarget (solBranchSlot n))
        sevm b.accessedStorageKeys (Devm.getStor b sevm.currentTarget) n nd := by
  unfold sstoreCost liveStoreCostOf
  show (if (⟨sevm.currentTarget, solBranchSlot n⟩ : Adr × B256) ∈
      b.accessedStorageKeys then 0 else gasColdSload) +
      sstoreValueCost (b.getOrigStorVal sevm sevm.currentTarget (solBranchSlot n))
        (b.getStorVal sevm.currentTarget (solBranchSlot n)) nd = _
  show _ = _ + sstoreValueCost _ ((Devm.getStor b sevm.currentTarget).get _) _
  rfl

/-- `sstoreCost` for the count bump is the `countStoreCostOf` at the machine
original read, at a warm count key (the body `SLOAD`s the count first). -/
theorem sstoreCost_eq_countStoreCostOf {sevm : Sevm} {b : Devm} {w : B256}
    (hwarm : (⟨sevm.currentTarget, solCountSlot⟩ : Adr × B256) ∈
      b.accessedStorageKeys)
    (hw : b.getStorVal sevm.currentTarget solCountSlot = w) :
    sstoreCost sevm b solCountSlot (1 + w) =
      countStoreCostOf (b.getOrigStorVal sevm sevm.currentTarget solCountSlot)
        w := by
  unfold sstoreCost countStoreCostOf
  rw [ite_eq_left hwarm, hw, Nat.zero_add]

end Blanc.Lift.BeaconDeposit
