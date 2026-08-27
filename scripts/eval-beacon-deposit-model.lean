-- eval-beacon-deposit-model.lean : emit the BeaconDeposit pure model's
-- outputs under the keccak-256 instantiation of its hash parameter, for the
-- fail-closed comparison against the independent Python oracle's vectors
-- (`scripts/reference/beacon-deposit/vectors.json`, keccak256 regime).
--
-- This is an evaluator, not an owner: it holds no proof, no golden value,
-- and no SHA-256 — the model's SHA-256 instantiation is deliberately left
-- to the compiled-port successor, so the model-agreement channel runs under
-- keccak-256 (`Jaune.Bytes.keccak`), and the oracle separately anchors its
-- own SHA-256 regime to the upstream test constants. Everything here is
-- computed by `#eval` (compiler/interpreter evaluation); no kernel-level
-- decision procedures are involved.
--
-- The deterministic inputs below mirror the oracle generator's documented
-- rules; the compare script fails closed if any echoed input drifts from
-- the committed vectors.

import Blanc.BeaconDepositCorrectness
import Jaune.Hash

namespace Blanc.BeaconDeposit

open Jaune

def Hk : Bytes → B256 := Bytes.keccak

def hex32 (b : B256) : String := b.toBytes.toHex

/-- `leaf_rule`: leaf `i` is the 32-byte big-endian encoding of `i + 1`. -/
def leaf (i : Nat) : B256 := Nat.toB256 (i + 1)

def leaves (n : Nat) : List B256 := (List.range n).map leaf

/-- The incremental state after inserting leaves `0 .. n-1`; `none` if any
insert refuses (impossible for the counts exercised here — a `none` prints
a FAILURE line and the compare script fails). -/
def chain (n : Nat) : Option Acc :=
  (List.range n).foldlM (fun s i => Acc.insert Hk s (leaf i)) Acc.empty

def rootCounts : List Nat :=
  [0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65,
   127, 128, 129, 255, 256, 257, 511, 512, 513, 1024, 1025]

/-- The naive reference is evaluated through `rootAtE`, the derived form
proved equal to `rootAt` in `BeaconDepositCorrectness` (`rootAtE_eq`); the
primary spec's double recursion on empty subtrees is exponential to
evaluate, and the proved equation is what licenses the substitution. -/
def naiveCounts : List Nat := rootCounts

def branchCounts : List Nat := [0, 1, 2, 3, 4, 8, 9, 33, 257]

def le64Samples : List Nat :=
  [0, 1, 2, 255, 256, 65536, 4294967295, 4294967296,
   281474976710661, 18446744073709551615]

def emitZeroHashes : IO Unit := do
  for h in List.range 33 do
    IO.println s!"zero_hash {h} {hex32 (zeroHash Hk h)}"

def emitLe64 : IO Unit := do
  for n in le64Samples do
    IO.println s!"le64 {n} {(le64 n).toHex}"

def emitRoots : IO Unit := do
  for n in rootCounts do
    match chain n with
    | none => IO.println s!"FAILURE chain {n} insert refused"
    | some s => do
        IO.println s!"incremental_root {n} {hex32 (climb Hk s.branch 32 0 s.count 0)}"
        IO.println s!"incremental_mixed_root {n} {hex32 (Acc.root Hk s)}"
        IO.println s!"count_bytes {n} {(Acc.countBytes s).toHex}"
  for n in naiveCounts do
    let nv := rootAtE Hk 32 (leaves n)
    IO.println s!"naive_root {n} {hex32 nv}"
    IO.println s!"naive_mixed_root {n} {hex32 (mixIn Hk nv (leaves n).length)}"

def emitBranchStates : IO Unit := do
  for n in branchCounts do
    match chain n with
    | none => IO.println s!"FAILURE chain {n} insert refused"
    | some s => do
        let slots := (List.range 32).map fun h => hex32 (s.branch h)
        let joined := String.intercalate "," slots
        IO.println s!"branch_state {n} {joined}"

def mkBytes (len byte : Nat) : Bytes :=
  List.replicate len (UInt8.ofNat byte)

structure CaseInputs where
  pubkey : Bytes
  wc : Bytes
  sig : Bytes
  value : Nat

def depositInputs (i : Nat) : CaseInputs :=
  { pubkey := mkBytes 48 (0x10 + i)
    wc := mkBytes 32 (0x20 + i)
    sig := mkBytes 96 (0x30 + i)
    value := if i % 2 == 0 then 32 * 10 ^ 18 else 10 ^ 18 + i * 10 ^ 9 }

def reasonTag : Reason → String
  | .pubkey_length => "pubkey_length"
  | .withdrawal_credentials_length => "withdrawal_credentials_length"
  | .signature_length => "signature_length"
  | .value_too_low => "value_too_low"
  | .value_not_gwei_multiple => "value_not_gwei_multiple"
  | .value_too_high => "value_too_high"
  | .deposit_data_root_mismatch => "deposit_data_root_mismatch"
  | .merkle_tree_full => "merkle_tree_full"
  | .assert_false => "assert_false"

def emitDepositCases : IO Unit := do
  let mut s := Acc.empty
  for i in List.range 6 do
    let c := depositInputs i
    let amountLE := le64 (c.value / oneGwei)
    let node := depositDataNode Hk c.pubkey c.wc c.sig amountLE
    IO.println s!"deposit_inputs {i} {c.pubkey.toHex} {c.wc.toHex} {c.sig.toHex} {c.value}"
    IO.println s!"deposit_encoding {i} {amountLE.toHex} {hex32 (pubkeyRoot Hk c.pubkey)} {hex32 (signatureRoot Hk c.sig)} {hex32 node}"
    match deposit Hk s c.pubkey c.wc c.sig node c.value with
    | .error r => IO.println s!"FAILURE deposit {i} {reasonTag r}"
    | .ok (s', ev) => do
        IO.println s!"deposit_event {i} {ev.pubkey.toHex} {ev.withdrawal_credentials.toHex} {ev.amount.toHex} {ev.signature.toHex} {ev.index.toHex}"
        IO.println s!"deposit_after {i} {s'.count} {hex32 (Acc.root Hk s')}"
        s := s'

/-- Guard cases: the oracle generator's documented deterministic rules.
Base inputs are `depositInputs 0`; each case violates exactly one guard
while satisfying every earlier one. -/
def emitGuardCases : IO Unit := do
  let g := depositInputs 0
  let ether := oneEther
  let run (name : String) (st : Acc) (pk wc sig : Bytes) (root : B256)
      (value : Nat) : IO Unit := do
    let tag := match deposit Hk st pk wc sig root value with
      | .error r => reasonTag r
      | .ok _ => "ok"
    IO.println s!"guard_case {name} {pk.toHex} {wc.toHex} {sig.toHex} {hex32 root} {value} {tag}"
  let nodeFor (value : Nat) : B256 :=
    depositDataNode Hk g.pubkey g.wc g.sig (le64 (value / oneGwei))
  run "invalid_pubkey_length" Acc.empty (mkBytes 47 0x10) g.wc g.sig 0 ether
  run "invalid_withdrawal_credentials_length" Acc.empty g.pubkey
    (mkBytes 31 0x20) g.sig 0 ether
  run "invalid_signature_length" Acc.empty g.pubkey g.wc (mkBytes 95 0x30)
    0 ether
  run "deposit_value_too_low" Acc.empty g.pubkey g.wc g.sig
    (nodeFor (ether / 2)) (ether / 2)
  run "deposit_value_not_multiple_of_gwei" Acc.empty g.pubkey g.wc g.sig 0
    (ether + 1)
  run "deposit_value_too_high" Acc.empty g.pubkey g.wc g.sig 0
    ((2 ^ 64 - 1 + 1) * oneGwei)
  let goodNode := nodeFor ether
  let badRoot : B256 :=
    Bytes.toB256 ((goodNode.toBytes.take 31) ++
      [(goodNode.toBytes.getD 31 0).xor 0xFF])
  run "deposit_data_root_mismatch" Acc.empty g.pubkey g.wc g.sig badRoot ether
  run "merkle_tree_full" ⟨fun _ => 0, 2 ^ 32 - 1⟩ g.pubkey g.wc g.sig
    goodNode ether
  run "precedence_pubkey_before_value_low" Acc.empty (mkBytes 47 0x10) g.wc
    g.sig 0 (ether / 2)

def emitBoundary : IO Unit := do
  for c in [2 ^ 32 - 3, 2 ^ 32 - 2] do
    let ok := (Acc.insert Hk ⟨fun _ => 0, c⟩ (leaf 0)).isSome
    IO.println s!"insert_at_count {c} {ok}"
  let okAtCap := (Acc.insert Hk ⟨fun _ => 0, 2 ^ 32 - 1⟩ (leaf 0)).isSome
  IO.println s!"insert_at_count {2 ^ 32 - 1} {okAtCap}"
  let walkFalls := (walk Hk (fun _ => 0) 32 0 (2 ^ 32) (leaf 0)).isNone
  IO.println s!"walk_falls_through_at {2 ^ 32} {walkFalls}"

def emitErc165 : IO Unit := do
  let erc165Id : Bytes := [0x01, 0xff, 0xc9, 0xa7]
  let idepositId : Bytes := [0x85, 0x64, 0x09, 0x07]
  let probe (label : String) (x : Bytes) : IO Unit :=
    IO.println s!"supports_interface {label} {supportsInterface erc165Id idepositId x}"
  probe "erc165" erc165Id
  probe "ideposit" idepositId
  probe "ffffffff" [0xff, 0xff, 0xff, 0xff]
  probe "zero" [0x00, 0x00, 0x00, 0x00]

def emitAll : IO Unit := do
  IO.println "eval_beacon_deposit_model keccak256"
  emitZeroHashes
  emitLe64
  emitRoots
  emitBranchStates
  emitDepositCases
  emitGuardCases
  emitBoundary
  emitErc165
  IO.println "eval_done"

#eval emitAll

end Blanc.BeaconDeposit
