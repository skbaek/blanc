import Blanc.Basic

/-!
# Beacon deposit contract — pure, hash-parametric model

A source-shaped model of the Ethereum beacon-chain deposit contract's
incremental-Merkle accumulator and encoding layer, mirroring the pinned
Solidity source vendored at
`scripts/reference/beacon-deposit/inputs/deposit_contract.sol`
(SHA-256 `2a8db249155e8502e1132f14410b8d7b2a924512723ed07a08167477d8f8c073`;
`ethereum/consensus-specs` commit `5dac261c78eda16b383f7b6d832495880bdd015c`).
Source line numbers in the doc comments below refer to that file.

The hash function is the **sole parameter**: every definition takes
`H : Bytes → B256`, the type of a 32-byte-digest hash over byte strings.
Nothing in this family depends on any property of SHA-256 beyond that type;
instantiating `H` (with Jaune's `Bytes.sha256`) is deliberately left to the
compiled-port successor. Every `H` call site below feeds exactly 64 bytes of
input, as every `sha256` call in the source does; `BeaconDepositCorrectness`
states those widths as lemmas.

Deliberate shape-preserving abstractions (each noted at its definition):

* Solidity `uint256` arithmetic is modeled by `Nat`. No operation here can
  wrap in `uint256`: `deposit_count + 1 ≤ 2^32 - 1` under the cap guard,
  `msg.value / 1 gwei < 2^256`, and comparisons/`%`/`/` agree with the
  unbounded readings on in-range values.
* The `uint64` casts in `to_little_endian_64(uint64 …)` truncate to 64 bits;
  `le64` reproduces that truncation by construction (byte extraction), so it
  agrees with the source even outside the guarded range.
* The storage arrays `branch` and `zero_hashes` (32 slots each) become a
  total function `Nat → B256` and the chain `zeroHash`; only indices `0..31`
  are ever read or written, `zero_hashes[0]` is the never-assigned storage
  default `0`, and the constructor materializes exactly `zeroHash 0 ..
  zeroHash 31` (lines 74–78).
* `bytes calldata` arguments become `Bytes` (`List UInt8`) with the exact
  source length guards; `bytes32` values are `B256`.
* Reverts become `Except Reason`; the `DepositEvent` payload is returned on
  success only, which is exactly the observable log semantics (the source
  emits before the last two guards, but a revert rolls the log back). The
  source's terminal `assert(false)` (line 158) is the honest
  `Reason.assert_false`, proved unreachable in `BeaconDepositCorrectness`.
-/

namespace Blanc.BeaconDeposit

open Jaune

/-- `sha256(abi.encodePacked(a, b))` for two `bytes32` words — the tree
combine used throughout the source (lines 77, 85, 87, 130, 134, 153). -/
def hashPair (H : Bytes → B256) (a b : B256) : B256 :=
  H (a.toBytes ++ b.toBytes)

/-- The zero-subtree chain: `zeroHash H 0 = 0` (the contract's never-assigned
`zero_hashes[0]` storage default) and `zeroHash H (h+1) =
H (zeroHash H h ‖ zeroHash H h)` — the constructor loop, source lines 74–78,
which materializes indices `0..31`. -/
def zeroHash (H : Bytes → B256) : Nat → B256
  | 0 => 0
  | h + 1 => let z := zeroHash H h; hashPair H z z

/-- Reference specification (not from the source): the depth-`d` zero-padded
Merkle root of a leaf list. `rootAt H 0 ls` is the single leaf (or the zero
leaf for `[]`); at `d+1` the list splits into the first `2^d` leaves and the
rest. Meaningful for `ls.length ≤ 2^d`; total regardless. -/
def rootAt (H : Bytes → B256) : Nat → List B256 → B256
  | 0, ls => ls.headD 0
  | d + 1, ls => hashPair H (rootAt H d (ls.take (2 ^ d))) (rootAt H d (ls.drop (2 ^ d)))

/-- The naive reference root of a leaf list: depth-32 zero-padded. -/
def rootOf (H : Bytes → B256) (ls : List B256) : B256 :=
  rootAt H 32 ls

/-- `to_little_endian_64` (source lines 165–177): the 8 little-endian bytes
of a `uint64`. `Nat.toUInt8` truncates each extracted byte, so the composite
reproduces the source's `uint64(…)` cast for any `Nat`. -/
def le64 (n : Nat) : Bytes :=
  [ n.toUInt8, (n >>> 8).toUInt8, (n >>> 16).toUInt8, (n >>> 24).toUInt8,
    (n >>> 32).toUInt8, (n >>> 40).toUInt8, (n >>> 48).toUInt8, (n >>> 56).toUInt8 ]

/-- `n` zero bytes (`bytes16(0)`, `bytes24(0)`, `bytes32(0)` paddings). -/
def zeros (n : Nat) : Bytes :=
  List.replicate n 0

/-- The count mix-in (source lines 90–94):
`sha256(node ‖ to_little_endian_64(uint64 count) ‖ bytes24(0))`. -/
def mixIn (H : Bytes → B256) (root : B256) (count : Nat) : B256 :=
  H (root.toBytes ++ le64 count ++ zeros 24)

/-- The reference mixed root: `rootOf` with the leaf count mixed in. -/
def mixedRootOf (H : Bytes → B256) (ls : List B256) : B256 :=
  mixIn H (rootOf H ls) ls.length

/-- The accumulator state: the contract's storage `branch` (32 `bytes32`
slots, as a total function on slot indices) and `deposit_count`
(source lines 69–70). -/
structure Acc where
  branch : Nat → B256
  count : Nat

/-- The freshly constructed contract: all-zero `branch` storage and
`deposit_count = 0` (storage defaults; the constructor writes only
`zero_hashes`). -/
def Acc.empty : Acc :=
  ⟨fun _ => 0, 0⟩

/-- The `get_deposit_root` fold (source lines 81–89), iterating heights
`h, h+1, …` with `k` iterations remaining, `size = count >>> h`, and `node`
the current subtree root: a live bit combines `branch[h]` on the left, a
dead bit combines `zero_hashes[h]` on the right, then `size /= 2`. -/
def climb (H : Bytes → B256) (branch : Nat → B256) : Nat → Nat → Nat → B256 → B256
  | 0, _, _, node => node
  | k + 1, h, size, node =>
      climb H branch k (h + 1) (size / 2)
        (if size % 2 = 1 then hashPair H (branch h) node
         else hashPair H node (zeroHash H h))

/-- `get_deposit_root()` (source lines 80–95): the 32-iteration fold from
`node = bytes32(0)` at height 0, then the count mix-in. The `uint64` cast in
the mix-in cannot truncate while `count ≤ 2^32 - 1`. -/
def Acc.root (H : Bytes → B256) (s : Acc) : B256 :=
  mixIn H (climb H s.branch 32 0 s.count 0) s.count

/-- `get_deposit_count()` (source lines 97–99). -/
def Acc.countBytes (s : Acc) : Bytes :=
  le64 s.count

/-- One storage write `branch[i] := v`, as a function override. -/
def setSlot (branch : Nat → B256) (i : Nat) (v : B256) : Nat → B256 :=
  fun j => if j = i then v else branch j

/-- The insertion walk (source lines 147–155), on the **incremented** count:
with `k` iterations remaining at height `h` and `size = newCount >>> h`, a
set low bit writes `node` into `branch[h]` and stops; a clear bit combines
`branch[h]` on the left and climbs. `none` is the loop running out — the
source's `assert(false)` fall-through (line 158). -/
def walk (H : Bytes → B256) (branch : Nat → B256) :
    Nat → Nat → Nat → B256 → Option (Nat → B256)
  | 0, _, _, _ => none
  | k + 1, h, size, node =>
      if size % 2 = 1 then some (setSlot branch h node)
      else walk H branch k (h + 1) (size / 2) (hashPair H (branch h) node)

/-- The tree-insertion tail of `deposit` (source lines 142–155): the
`MAX_DEPOSIT_COUNT` guard, the increment, and the 32-iteration walk. Under
the guard the walk always finds a live slot (`BeaconDepositCorrectness`
proves it), so `none` here is exactly the "merkle tree full" revert. -/
def Acc.insert (H : Bytes → B256) (s : Acc) (node : B256) : Option Acc :=
  if s.count < 2 ^ 32 - 1 then
    (walk H s.branch 32 0 (s.count + 1) node).map fun br => ⟨br, s.count + 1⟩
  else none

/-- `deposit`'s revert partition, one constructor per `require` in source
order plus the terminal `assert(false)`. The quoted strings are the exact
source revert reasons (lines 108–143). -/
inductive Reason
  /-- "DepositContract: invalid pubkey length" (line 108) -/
  | pubkey_length
  /-- "DepositContract: invalid withdrawal_credentials length" (line 109) -/
  | withdrawal_credentials_length
  /-- "DepositContract: invalid signature length" (line 110) -/
  | signature_length
  /-- "DepositContract: deposit value too low" (line 113) -/
  | value_too_low
  /-- "DepositContract: deposit value not multiple of gwei" (line 114) -/
  | value_not_gwei_multiple
  /-- "DepositContract: deposit value too high" (line 116) -/
  | value_too_high
  /-- "DepositContract: reconstructed DepositData does not match supplied
  deposit_data_root" (line 140) -/
  | deposit_data_root_mismatch
  /-- "DepositContract: merkle tree full" (line 143) -/
  | merkle_tree_full
  /-- `assert(false)` (line 158) — the walk fell through; proved
  unreachable. -/
  | assert_false
deriving DecidableEq

/-- The `DepositEvent` payload (source lines 19–25, 120–126): five dynamic
`bytes` fields, none indexed. -/
structure DepositEvent where
  pubkey : Bytes
  withdrawal_credentials : Bytes
  amount : Bytes
  signature : Bytes
  index : Bytes
deriving DecidableEq

/-- `1 ether` in wei. -/
def oneEther : Nat := 10 ^ 18

/-- `1 gwei` in wei. -/
def oneGwei : Nat := 10 ^ 9

/-- `sha256(abi.encodePacked(pubkey, bytes16(0)))` (source line 129):
input width 48 + 16 = 64 under the pubkey length guard. -/
def pubkeyRoot (H : Bytes → B256) (pubkey : Bytes) : B256 :=
  H (pubkey ++ zeros 16)

/-- `signature_root` (source lines 130–133): the signature splits at byte 64;
inputs 64, 32 + 32, and 32 + 32 bytes under the signature length guard. -/
def signatureRoot (H : Bytes → B256) (signature : Bytes) : B256 :=
  hashPair H (H (signature.take 64)) (H (signature.drop 64 ++ zeros 32))

/-- The reconstructed `DepositData` hash tree root `node` (source lines
134–137), over the already-encoded 8-byte little-endian amount. -/
def depositDataNode (H : Bytes → B256)
    (pubkey withdrawal_credentials signature amountLE : Bytes) : B256 :=
  hashPair H
    (H ((pubkeyRoot H pubkey).toBytes ++ withdrawal_credentials))
    (H (amountLE ++ zeros 24 ++ (signatureRoot H signature).toBytes))

/-- `deposit(pubkey, withdrawal_credentials, signature, deposit_data_root)`
with `value = msg.value` (source lines 101–159): the six input guards in
source order, the event payload (with the **pre-increment** count as
`index`, line 125), the `DepositData` root reconstruction and check, the
cap guard, and the insertion walk. Failure returns the first violated
guard's `Reason`; success returns the new state and the event. -/
def deposit (H : Bytes → B256) (s : Acc)
    (pubkey withdrawal_credentials signature : Bytes)
    (deposit_data_root : B256) (value : Nat) :
    Except Reason (Acc × DepositEvent) :=
  if pubkey.length ≠ 48 then .error .pubkey_length
  else if withdrawal_credentials.length ≠ 32 then .error .withdrawal_credentials_length
  else if signature.length ≠ 96 then .error .signature_length
  else if value < oneEther then .error .value_too_low
  else if value % oneGwei ≠ 0 then .error .value_not_gwei_multiple
  else if 2 ^ 64 - 1 < value / oneGwei then .error .value_too_high
  else
    let amount := le64 (value / oneGwei)
    let event : DepositEvent :=
      ⟨pubkey, withdrawal_credentials, amount, signature, le64 s.count⟩
    let node := depositDataNode H pubkey withdrawal_credentials signature amount
    if node ≠ deposit_data_root then .error .deposit_data_root_mismatch
    else if ¬ s.count < 2 ^ 32 - 1 then .error .merkle_tree_full
    else
      match walk H s.branch 32 0 (s.count + 1) node with
      | some br => .ok (⟨br, s.count + 1⟩, event)
      | none => .error .assert_false

/-- `supportsInterface` (source lines 161–163), over the two 4-byte
interface identifiers as `Bytes`. The concrete id words
(`0x01ffc9a7` and the `IDepositContract` XOR) are EVM/ABI-side facts pinned
by the vector oracle, not computed here. -/
def supportsInterface (erc165Id idepositId interfaceId : Bytes) : Bool :=
  interfaceId = erc165Id || interfaceId = idepositId

end Blanc.BeaconDeposit
