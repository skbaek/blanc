import Blanc.Lift.BeaconDeposit.CountView
import Blanc.Lift.BeaconDeposit.DepositArgs
import Blanc.Lift.BeaconDeposit.Layout
import Blanc.ForwardStorageAccess

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
* `ShaReady sevm b` — the premises of the SHA-256 precompile step
  (`Ninst.runCompiled_staticcall_sha256_64_warm`): address 2 warm and undelegated, a precompile
  of the fork, a covered fork, nonzero depth.
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
logs, output and error.  (Balances and the return-data buffer may differ: the precompile call
touches both.) -/
structure Keep (b b' : Devm) : Prop where
  stor : ∀ a, Devm.getStor b' a = Devm.getStor b a
  code : ∀ a, b'.getCode a = b.getCode a
  addrs : b'.accessedAddresses = b.accessedAddresses
  keys : b'.accessedStorageKeys = b.accessedStorageKeys
  logs : b'.logs = b.logs
  output : b'.output = b.output
  error : b'.error = b.error

theorem Keep.refl (b : Devm) : Keep b b :=
  ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {b b' b'' : Devm} (h : Keep b b') (h' : Keep b' b'') : Keep b b'' :=
  ⟨fun a => (h'.stor a).trans (h.stor a), fun a => (h'.code a).trans (h.code a),
    h'.addrs.trans h.addrs, h'.keys.trans h.keys, h'.logs.trans h.logs,
    h'.output.trans h.output, h'.error.trans h.error⟩

theorem Keep.getStorVal {b b' : Devm} (h : Keep b b') (a : Adr) (k : B256) :
    b'.getStorVal a k = b.getStorVal a k := by
  show (Devm.getStor b' a).get k = (Devm.getStor b a).get k
  rw [h.stor]

/-- The SHA-256 precompile premises (`Ninst.runCompiled_staticcall_sha256_64_warm`). -/
structure ShaReady (sevm : Sevm) (b : Devm) : Prop where
  nodeleg : getDelegatedCodeAddress (b.getCode 2) = none
  warm : (2 : Adr) ∈ b.accessedAddresses
  pre : decide (sevm.benvStat.rules.isPrecomp 2) = true
  fork : CoveredFork sevm.benvStat.fork
  depth : sevm.depth ≠ 0

theorem ShaReady.keep {sevm : Sevm} {b b' : Devm} (h : ShaReady sevm b) (hk : Keep b b') :
    ShaReady sevm b' :=
  ⟨by rw [hk.code]; exact h.nodeleg, by rw [hk.addrs]; exact h.warm, h.pre, h.fork, h.depth⟩

/-! ## Memory at a boundary -/

/-- `M` is well formed, of size `n`, and reads as an image holding the free pointer `fp` at
`0x40` and each `(offset, bytes)` of `facts`. -/
def BodyMem (M : Mem) (n : Nat) (fp : B256) (facts : List (Nat × Bytes)) : Prop :=
  Mem.Wf M ∧ M.size = n ∧
    ∃ img : Bytes, Mem.Reads M img ∧ img.sliceD 64 32 0 = fp.toBytes ∧
      ∀ p ∈ facts, img.sliceD p.1 p.2.length 0 = p.2

theorem BodyMem.mono {M : Mem} {n : Nat} {fp : B256} {facts facts' : List (Nat × Bytes)}
    (h : BodyMem M n fp facts) (hsub : ∀ p ∈ facts', p ∈ facts) : BodyMem M n fp facts' := by
  obtain ⟨hwf, hs, img, hr, hfp, hf⟩ := h
  exact ⟨hwf, hs, img, hr, hfp, fun p hp => hf p (hsub p hp)⟩

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

end Blanc.Lift.BeaconDeposit
