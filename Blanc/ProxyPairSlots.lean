import Blanc.CommonCore

/-!
# ERC-1967 storage slots, derived rather than assumed

The first member of Blanc's `proxy-pair` contract family.  It is imported by
`Blanc.lean`, is classified under `proxy-pair` in
`scripts/check-layering.py`, and imports only `Blanc.CommonCore` — a shared
module, so this file borrows no other contract's vocabulary and no upstream
layer depends on it.  Later `proxy-pair` members — the proxy and
implementation programs, their compiled bytes, and the properties over them —
sit beside this module rather than beneath it, per `README.md`'s "Module
hierarchy: contracts are siblings".

The file states what the ERC-1967 slots *are*, so that every later module can
cite a derived word instead of restating a hex literal.

## What the constants are

The three slot words below are the ERC-1967 logic, admin and beacon slots as
published in `ethereum/ERCs` at commit
`8dd085d159cb123f545c272c0d871a5339550e79`, file `ERCS/erc-1967.md`.  Each is
`keccak256(<ascii preimage>) - 1` — *minus* one, never plus one.

## What is derived and what is claimed

Nothing here assumes a digest.  Each slot is *defined* as
`Blanc.String.keccak <preimage> - 1`, so its definition mentions only Jaune's
Keccak-256 and Jaune's 256-bit wrapping subtraction.  The `_val` theorems then
prove that this derived word equals the published literal, and the kernel
computes the hash to check it.  The published hex digits are therefore a
*conclusion* of this file, not an input to it: were the ERC's value wrong, the
corresponding `_val` theorem would simply fail to elaborate.

**No keccak-injectivity assumption is used anywhere in this file, and none is
needed.**  A derived-equals-literal fact is a computation on one fixed input,
not a property of the hash function.  Likewise the separations below are
decided by comparing the two computed 256-bit words; they do not appeal to
collision resistance, and they would remain proofs even if Keccak-256 were
broken.  Any downstream use that needs "a slot no ordinary storage key can
collide with" must earn that from the separations actually proved here, which
are separations from *named* words only — the three slots and zero — and
never from the whole key space.

## Proof technique

Every hash is forced by `decide +kernel`.  The repository's trust surface bans
evaluation outside the kernel, which would add `Lean.ofReduceBool` to the
audited axioms; bare `decide`, `rfl` or a `simp` that unfolds `String.keccak`
would force the hash in the elaborator instead and exhaust the recursion-depth
ceiling.  The three hashes are
decided separately: they are three different subjects, and bundling distinct
subjects into one kernel decision has measurably regressed elaboration here
before.

Trust evidence is not restated in this file.  No module under `Blanc/` carries
its own `#print axioms` block; the repository-wide inventory is
`scripts/AxiomCheck.lean`, pinned row by row against exact expectations by
`scripts/check.sh`.
-/

namespace Blanc.ProxyPair

open Jaune

/-! ## Preimages

The ASCII strings themselves, so that the source shows what is being hashed.
No quotes, no NUL terminator and no trailing newline are part of any preimage;
all three are pure ASCII, so `Blanc.String.toBytes` (a `Char.toUInt8` map)
agrees with UTF-8 on them. -/

def implementationPreimage : String := "eip1967.proxy.implementation"
def adminPreimage : String := "eip1967.proxy.admin"
def beaconPreimage : String := "eip1967.proxy.beacon"

/-! ## The slots

`- 1` is `Jaune.B256.sub`, the wrapping 256-bit subtraction. -/

/-- ERC-1967 logic slot: `keccak256("eip1967.proxy.implementation") - 1`. -/
def implementationSlot : B256 := Blanc.String.keccak implementationPreimage - 1

/-- ERC-1967 admin slot: `keccak256("eip1967.proxy.admin") - 1`. -/
def adminSlot : B256 := Blanc.String.keccak adminPreimage - 1

/-- ERC-1967 beacon slot: `keccak256("eip1967.proxy.beacon") - 1`. -/
def beaconSlot : B256 := Blanc.String.keccak beaconPreimage - 1

/-! ## The derived words equal the published words

One kernel keccak per slot.  Everything below rewrites with these and then
compares numerals, so no later declaration recomputes a hash. -/

/-- The logic slot is the word ERC-1967 publishes for it. -/
theorem implementationSlot_val :
    implementationSlot =
      (0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc :
        B256) := by
  decide +kernel

/-- The admin slot is the word ERC-1967 publishes for it. -/
theorem adminSlot_val :
    adminSlot =
      (0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103 :
        B256) := by
  decide +kernel

/-- The beacon slot is the word ERC-1967 publishes for it. -/
theorem beaconSlot_val :
    beaconSlot =
      (0xa3f0ad74e5423aebfd80d3ef4346578335a9a72aeaee59ff6cb3582b35133d50 :
        B256) := by
  decide +kernel

/-! ## Pairwise separation

Each unordered pair is compared once on its words; the reverse direction is
that comparison read backwards. -/

/-- The logic and admin slots are distinct storage words. -/
theorem implementationSlot_ne_adminSlot : implementationSlot ≠ adminSlot := by
  rw [implementationSlot_val, adminSlot_val]; decide

/-- The logic and beacon slots are distinct storage words. -/
theorem implementationSlot_ne_beaconSlot : implementationSlot ≠ beaconSlot := by
  rw [implementationSlot_val, beaconSlot_val]; decide

/-- The admin and beacon slots are distinct storage words. -/
theorem adminSlot_ne_beaconSlot : adminSlot ≠ beaconSlot := by
  rw [adminSlot_val, beaconSlot_val]; decide

/-- `implementationSlot_ne_adminSlot`, read in the other direction. -/
theorem adminSlot_ne_implementationSlot : adminSlot ≠ implementationSlot :=
  implementationSlot_ne_adminSlot.symm

/-- `implementationSlot_ne_beaconSlot`, read in the other direction. -/
theorem beaconSlot_ne_implementationSlot : beaconSlot ≠ implementationSlot :=
  implementationSlot_ne_beaconSlot.symm

/-- `adminSlot_ne_beaconSlot`, read in the other direction. -/
theorem beaconSlot_ne_adminSlot : beaconSlot ≠ adminSlot :=
  adminSlot_ne_beaconSlot.symm

/-! ## Nonzero

Stated separately from the pairwise separations, since a slot being distinct
from `0` is wanted in contexts that name no other slot. -/

/-- The logic slot is not the zero word. -/
theorem implementationSlot_ne_zero : implementationSlot ≠ (0 : B256) := by
  rw [implementationSlot_val]; decide

/-- The admin slot is not the zero word. -/
theorem adminSlot_ne_zero : adminSlot ≠ (0 : B256) := by
  rw [adminSlot_val]; decide

/-- The beacon slot is not the zero word. -/
theorem beaconSlot_ne_zero : beaconSlot ≠ (0 : B256) := by
  rw [beaconSlot_val]; decide

end Blanc.ProxyPair
