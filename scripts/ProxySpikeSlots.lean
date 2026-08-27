import Blanc.CommonCore

/-!
# ERC-1967 storage slots, derived rather than assumed

Branch-local spike evidence for goal `proxy-delegatecall-spike-v1`, row P5.
This file is not imported by `Blanc.lean`; it lives under `scripts/` and is
self-contained, importing only `Blanc.CommonCore`.

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
are separations from *named* words only.

## Proof technique

Every hash is forced by `decide +kernel`.  `native_decide` is banned in this
repository and would add `Lean.ofReduceBool` to the axiom set; bare `decide`,
`rfl` or a `simp` that unfolds `String.keccak` would force the hash in the
elaborator instead and blow `maxRecDepth`.  The three hashes are decided
separately: they are three different subjects, and bundling distinct subjects
into one kernel decision has measurably regressed elaboration here before.

The `#print axioms` block at the end of the file covers every theorem stated
in it, so the trust evidence is part of this file's own output.
-/

namespace Blanc.ProxySpike

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

theorem implementationSlot_val :
    implementationSlot =
      (0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc :
        B256) := by
  decide +kernel

theorem adminSlot_val :
    adminSlot =
      (0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103 :
        B256) := by
  decide +kernel

theorem beaconSlot_val :
    beaconSlot =
      (0xa3f0ad74e5423aebfd80d3ef4346578335a9a72aeaee59ff6cb3582b35133d50 :
        B256) := by
  decide +kernel

/-! ## Pairwise separation

Each unordered pair is compared once on its words; the reverse direction is
that comparison read backwards. -/

theorem implementationSlot_ne_adminSlot : implementationSlot ≠ adminSlot := by
  rw [implementationSlot_val, adminSlot_val]; decide

theorem implementationSlot_ne_beaconSlot : implementationSlot ≠ beaconSlot := by
  rw [implementationSlot_val, beaconSlot_val]; decide

theorem adminSlot_ne_beaconSlot : adminSlot ≠ beaconSlot := by
  rw [adminSlot_val, beaconSlot_val]; decide

theorem adminSlot_ne_implementationSlot : adminSlot ≠ implementationSlot :=
  implementationSlot_ne_adminSlot.symm

theorem beaconSlot_ne_implementationSlot : beaconSlot ≠ implementationSlot :=
  implementationSlot_ne_beaconSlot.symm

theorem beaconSlot_ne_adminSlot : beaconSlot ≠ adminSlot :=
  adminSlot_ne_beaconSlot.symm

/-! ## Separation from the spike implementation's own storage region

The spike's implementation contract writes small, explicitly enumerated slots.
This is that region, written out rather than described. -/

def spikeImplRegion : List B256 := [0, 1, 2, 3]

/-! Membership in `spikeImplRegion` is decidable — `B256` derives
`DecidableEq` — so one `∉` theorem per slot discharges all four combinations
at once and is the form a consumer actually wants (`∀ k ∈ region, slot ≠ k`
follows by `List.forall_mem_ne`-style reasoning without recomputing anything).
That is why the region facts below are stated as non-membership rather than as
twelve separate inequalities: the same twelve numeral comparisons happen, but
the statement quantifies over the region instead of enumerating it, so growing
the region does not multiply theorem names. -/

theorem implementationSlot_notMem_spikeImplRegion :
    implementationSlot ∉ spikeImplRegion := by
  rw [implementationSlot_val]; decide

theorem adminSlot_notMem_spikeImplRegion : adminSlot ∉ spikeImplRegion := by
  rw [adminSlot_val]; decide

theorem beaconSlot_notMem_spikeImplRegion : beaconSlot ∉ spikeImplRegion := by
  rw [beaconSlot_val]; decide

/-- The pointwise reading of the three non-membership facts, for a caller
holding a region member rather than the region. -/
theorem ne_of_mem_spikeImplRegion {k : B256} (h : k ∈ spikeImplRegion) :
    implementationSlot ≠ k ∧ adminSlot ≠ k ∧ beaconSlot ≠ k :=
  ⟨fun e => implementationSlot_notMem_spikeImplRegion (e ▸ h),
   fun e => adminSlot_notMem_spikeImplRegion (e ▸ h),
   fun e => beaconSlot_notMem_spikeImplRegion (e ▸ h)⟩

/-! ## Nonzero

Stated separately from the region facts, since a slot being distinct from
`0` is wanted in contexts that have no region in scope. -/

theorem implementationSlot_ne_zero : implementationSlot ≠ (0 : B256) := by
  rw [implementationSlot_val]; decide

theorem adminSlot_ne_zero : adminSlot ≠ (0 : B256) := by
  rw [adminSlot_val]; decide

theorem beaconSlot_ne_zero : beaconSlot ≠ (0 : B256) := by
  rw [beaconSlot_val]; decide

/-! ## Trust surface

Every theorem stated above, in order.  A subset of
`[propext, Classical.choice, Quot.sound]` is the pass; any `sorryAx`,
`Lean.ofReduceBool` or `Lean.ofReduceNat` is a failure. -/

#print axioms implementationSlot_val
#print axioms adminSlot_val
#print axioms beaconSlot_val
#print axioms implementationSlot_ne_adminSlot
#print axioms implementationSlot_ne_beaconSlot
#print axioms adminSlot_ne_beaconSlot
#print axioms adminSlot_ne_implementationSlot
#print axioms beaconSlot_ne_implementationSlot
#print axioms beaconSlot_ne_adminSlot
#print axioms implementationSlot_notMem_spikeImplRegion
#print axioms adminSlot_notMem_spikeImplRegion
#print axioms beaconSlot_notMem_spikeImplRegion
#print axioms ne_of_mem_spikeImplRegion
#print axioms implementationSlot_ne_zero
#print axioms adminSlot_ne_zero
#print axioms beaconSlot_ne_zero

end Blanc.ProxySpike
