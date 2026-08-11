-- WETH10's deployment parameters, tagged storage keys, and logical projection.
-- This low program-support layer deliberately contains no callable program and
-- imports no proof ladder or sibling contract.

import Blanc.CommonCore

namespace Blanc

open Jaune

namespace Weth10

/-- Values fixed when a particular WETH10 runtime is deployed.  They live in
the generated program, not in storage. -/
structure DeployParams where
  deploymentChainId : B256
  cachedDomainSeparator : B256
deriving DecidableEq

/-- The source strings are definitions, rather than manually copied digests.
The network-free reference gate independently checks both UTF-8 preimages and
their keccak values against the vendored compiler input. -/
def callbackSuccessPreimage : String := "ERC3156FlashBorrower.onFlashLoan"
def permitTypehashPreimage : String :=
  "Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)"

def CALLBACK_SUCCESS : B256 := String.keccak callbackSuccessPreimage
def PERMIT_TYPEHASH : B256 := String.keccak permitTypehashPreimage

def flashMintedSlot : B256 := B256.max
def maxFlashMinted : Nat := 2 ^ 112 - 1

private def nonceTag : UInt64 := 0x4000000000000000
private def allowanceTag : UInt64 := 0x8000000000000000
private def tagMask : UInt64 := 0xc000000000000000
private def payloadMask : UInt64 := 0x3fffffffffffffff

/-- Region `00`: canonical address words are the balance keys. -/
def balanceKey (a : Adr) : B256 := a.toB256

/-- Region `01`: the address is retained verbatim below the two tag bits. -/
def nonceKey (a : Adr) : B256 := ⟨⟨nonceTag, a.1.toUInt64⟩, a.2⟩

def allowanceHash (owner spender : Adr) : B256 :=
  (owner.toB256.toBytes ++ spender.toB256.toBytes).keccak

/-- Clear the two most significant bits without normalizing the whole word. -/
def low254 (w : B256) : B256 :=
  ⟨⟨w.1.1 &&& payloadMask, w.1.2⟩, w.2⟩

/-- Region `10`: the low 254 bits of the canonical owner/spender-word hash. -/
def allowanceKey (owner spender : Adr) : B256 :=
  let h := allowanceHash owner spender
  ⟨⟨allowanceTag ||| (h.1.1 &&& payloadMask), h.1.2⟩, h.2⟩

private lemma UInt64.and_max' (x : UInt64) : x &&& UInt64.max = x := by
  apply UInt64.toBitVec_inj.mp
  rw [UInt64.toBitVec_and]
  have hmax : UInt64.max.toBitVec = BitVec.allOnes 64 := by rfl
  rw [hmax]
  exact BitVec.and_allOnes

private lemma B128.and_max' (x : B128) : x &&& B128.max = x := by
  apply Prod.ext <;> apply UInt64.and_max'

/-- The structural nonce encoding is exactly `2^254 OR address`. -/
theorem nonceKey_formula (a : Adr) :
    nonceKey a = Nat.toB256 (2 ^ 254) ||| a.toB256 := by
  have htag : Nat.toB256 (2 ^ 254) = (⟨⟨nonceTag, 0⟩, 0⟩ : B256) := by
    decide +kernel
  rw [htag]
  change (⟨⟨nonceTag, a.1.toUInt64⟩, a.2⟩ : B256) =
    (⟨⟨nonceTag ||| 0, 0 ||| a.1.toUInt64⟩, (0 : B128) ||| a.2⟩ : B256)
  rw [UInt64.or_zero, UInt64.zero_or, B128.zero_or]

/-- The structural projection is exactly a mask to the low 254 bits. -/
theorem low254_formula (w : B256) :
    low254 w = w &&& Nat.toB256 (2 ^ 254 - 1) := by
  have hmask : Nat.toB256 (2 ^ 254 - 1) =
      (⟨⟨payloadMask, UInt64.max⟩, B128.max⟩ : B256) := by
    decide +kernel
  rw [hmask]
  change (⟨⟨w.1.1 &&& payloadMask, w.1.2⟩, w.2⟩ : B256) =
    (⟨⟨w.1.1 &&& payloadMask, w.1.2 &&& UInt64.max⟩, w.2 &&& B128.max⟩ : B256)
  rw [UInt64.and_max', B128.and_max']

/-- The structural allowance encoding is exactly `2^255 OR low254(hash)`. -/
theorem allowanceKey_formula (owner spender : Adr) :
    allowanceKey owner spender =
      Nat.toB256 (2 ^ 255) ||| low254 (allowanceHash owner spender) := by
  have htag : Nat.toB256 (2 ^ 255) =
      (⟨⟨allowanceTag, 0⟩, 0⟩ : B256) := by
    decide +kernel
  rw [htag]
  change
    (⟨⟨allowanceTag ||| ((allowanceHash owner spender).1.1 &&& payloadMask),
       (allowanceHash owner spender).1.2⟩, (allowanceHash owner spender).2⟩ : B256) =
    (⟨⟨allowanceTag ||| ((allowanceHash owner spender).1.1 &&& payloadMask),
       0 ||| (allowanceHash owner spender).1.2⟩,
       (0 : B128) ||| (allowanceHash owner spender).2⟩ : B256)
  rw [UInt64.zero_or, B128.zero_or]

inductive KeyRegion
  | balance | nonce | allowance | flash
deriving DecidableEq

def regionTag : KeyRegion → UInt64
  | .balance => 0
  | .nonce => nonceTag
  | .allowance => allowanceTag
  | .flash => tagMask

def keyTag (w : B256) : UInt64 := tagMask &&& w.1.1
def InRegion (region : KeyRegion) (w : B256) : Prop :=
  keyTag w = regionTag region

private lemma allowanceTag_bits (x : UInt64) :
    tagMask &&& (allowanceTag ||| (x &&& payloadMask)) = allowanceTag := by
  apply UInt64.toBitVec_inj.mp
  rw [UInt64.toBitVec_and, UInt64.toBitVec_or, BitVec.and_or_distrib_left]
  simp only [UInt64.toBitVec_and]
  rw [← BitVec.and_assoc, BitVec.and_comm tagMask.toBitVec x.toBitVec,
    BitVec.and_assoc]
  have htags : tagMask.toBitVec &&& allowanceTag.toBitVec =
      allowanceTag.toBitVec := by rfl
  have hmask : tagMask.toBitVec &&& payloadMask.toBitVec = 0 := by rfl
  rw [htags, hmask]
  simp

theorem balanceKey_region (a : Adr) : InRegion .balance (balanceKey a) := by
  simp [InRegion, keyTag, balanceKey, regionTag, tagMask, Adr.toB256]

theorem nonceKey_region (a : Adr) : InRegion .nonce (nonceKey a) := by
  change tagMask &&& nonceTag = nonceTag
  decide +kernel

theorem allowanceKey_region (owner spender : Adr) :
    InRegion .allowance (allowanceKey owner spender) := by
  exact allowanceTag_bits _

theorem flashMintedSlot_region : InRegion .flash flashMintedSlot := by
  change tagMask &&& UInt64.max = tagMask
  decide +kernel

theorem regionTag_injective : Function.Injective regionTag := by
  intro x y
  cases x <;> cases y <;>
    simp [regionTag, nonceTag, allowanceTag, tagMask] at *

/-- One generic theorem covers all six pairwise region-disjointness cases. -/
theorem regions_disjoint {x y : KeyRegion} (hne : x ≠ y) :
    ∀ w, InRegion x w → InRegion y w → False := by
  intro w hx hy
  apply hne
  apply regionTag_injective
  rw [← hx, ← hy]

theorem balanceKey_valid (a : Adr) : ValidAdr (balanceKey a) := ⟨a, rfl⟩

theorem nonceKey_injective : Function.Injective nonceKey := by
  intro a b h
  have hh : a.1.toUInt64 = b.1.toUInt64 :=
    congrArg (fun w : B256 => w.1.2) h
  have hl : a.2 = b.2 := congrArg (fun w : B256 => w.2) h
  apply Adr.toB256_inj
  exact Prod.ext (Prod.ext rfl hh) hl

theorem nonceKey_not_valid (a : Adr) : ¬ ValidAdr (nonceKey a) := by
  rintro ⟨b, hb⟩
  exact regions_disjoint (x := .balance) (y := .nonce) (by decide)
    (nonceKey a) (hb ▸ balanceKey_region b) (nonceKey_region a)

theorem allowanceKey_not_valid (owner spender : Adr) :
    ¬ ValidAdr (allowanceKey owner spender) := by
  rintro ⟨a, ha⟩
  exact regions_disjoint (x := .balance) (y := .allowance) (by decide)
    (allowanceKey owner spender) (ha ▸ balanceKey_region a)
    (allowanceKey_region owner spender)

theorem flashMintedSlot_not_valid : ¬ ValidAdr flashMintedSlot := by
  rintro ⟨a, ha⟩
  exact regions_disjoint (x := .balance) (y := .flash) (by decide)
    flashMintedSlot (ha ▸ balanceKey_region a) flashMintedSlot_region

theorem balanceKey_ne_nonceKey (a b : Adr) : balanceKey a ≠ nonceKey b := by
  intro h
  exact regions_disjoint (x := .balance) (y := .nonce) (by decide)
    _ (balanceKey_region a) (h ▸ nonceKey_region b)

theorem balanceKey_ne_allowanceKey (a owner spender : Adr) :
    balanceKey a ≠ allowanceKey owner spender := by
  intro h
  exact regions_disjoint (x := .balance) (y := .allowance) (by decide)
    _ (balanceKey_region a) (h ▸ allowanceKey_region owner spender)

theorem balanceKey_ne_flashMintedSlot (a : Adr) :
    balanceKey a ≠ flashMintedSlot := by
  intro h
  exact regions_disjoint (x := .balance) (y := .flash) (by decide)
    _ (balanceKey_region a) (h ▸ flashMintedSlot_region)

theorem nonceKey_ne_allowanceKey (a owner spender : Adr) :
    nonceKey a ≠ allowanceKey owner spender := by
  intro h
  exact regions_disjoint (x := .nonce) (y := .allowance) (by decide)
    _ (nonceKey_region a) (h ▸ allowanceKey_region owner spender)

theorem nonceKey_ne_flashMintedSlot (a : Adr) : nonceKey a ≠ flashMintedSlot := by
  intro h
  exact regions_disjoint (x := .nonce) (y := .flash) (by decide)
    _ (nonceKey_region a) (h ▸ flashMintedSlot_region)

theorem allowanceKey_ne_flashMintedSlot (owner spender : Adr) :
    allowanceKey owner spender ≠ flashMintedSlot := by
  intro h
  exact regions_disjoint (x := .allowance) (y := .flash) (by decide)
    _ (allowanceKey_region owner spender) (h ▸ flashMintedSlot_region)

/-! ### Region-shape projections

The allowance-region transport arms all need the same three consequences of a
key carrying the allowance tag: it is not an address-shaped balance key, it is
not address-shaped at all, and it is not the flash counter slot.  They live
here beside `regions_disjoint`, the theorem they are all immediate corollaries
of. -/

/-- A tagged allowance key is never an address-shaped balance key. -/
theorem allowanceRegion_ne_validAdr {key k : B256}
    (hkey : InRegion .allowance key) (hvalid : ValidAdr k) : key ≠ k := by
  intro h
  rcases hvalid with ⟨a, ha⟩
  apply regions_disjoint (x := .allowance) (y := .balance) (by decide)
    key hkey
  rw [h, ← ha]
  simpa only [balanceKey] using balanceKey_region a

/-- A tagged allowance key is never itself address-shaped. -/
theorem allowanceRegion_not_valid {key : B256}
    (hkey : InRegion .allowance key) : ¬ ValidAdr key := fun hvalid =>
  allowanceRegion_ne_validAdr hkey hvalid rfl

/-- A tagged allowance key is never the flash counter slot. -/
theorem allowanceRegion_ne_flashSlot {key : B256}
    (hkey : InRegion .allowance key) : key ≠ flashMintedSlot := by
  intro h
  refine regions_disjoint (x := .allowance) (y := .flash) (by decide)
    key hkey ?_
  rw [h]
  exact flashMintedSlot_region

private theorem rest_set_of_not_valid {s : Stor} {k v : B256}
    (h : ¬ ValidAdr k) : Stor.rest (s.set k v) = Stor.rest s := by
  funext a
  unfold Stor.rest Function.comp
  rw [Stor.get_set_ne]
  intro heq
  exact h ⟨a, heq.symm⟩

theorem balSum_set_nonce (s : Stor) (a : Adr) (v : B256) :
    balSum (s.set (nonceKey a) v) = balSum s := by
  unfold balSum
  rw [rest_set_of_not_valid (nonceKey_not_valid a)]

theorem balSum_set_allowance (s : Stor) (owner spender : Adr) (v : B256) :
    balSum (s.set (allowanceKey owner spender) v) = balSum s := by
  unfold balSum
  rw [rest_set_of_not_valid (allowanceKey_not_valid owner spender)]

theorem balSum_set_flashMinted (s : Stor) (v : B256) :
    balSum (s.set flashMintedSlot v) = balSum s := by
  unfold balSum
  rw [rest_set_of_not_valid flashMintedSlot_not_valid]

/-! ## Logical projection

Balances, nonces, flashMinted, and ETH are total.  Allowances are observed only
on a finite trace-local set with an explicit local collision exclusion; no
global property of keccak is assumed. -/

def balanceOf (s : Stor) (a : Adr) : B256 := s.get (balanceKey a)
def nonceOf (s : Stor) (a : Adr) : B256 := s.get (nonceKey a)
def allowanceOf (s : Stor) (owner spender : Adr) : B256 :=
  s.get (allowanceKey owner spender)
def flashMintedOf (s : Stor) : B256 := s.get flashMintedSlot
def ethOf (ethBalance : Adr → B256) (self : Adr) : B256 := ethBalance self

structure LogicalState where
  balances : Adr → B256
  nonces : Adr → B256
  flashMinted : B256
  eth : B256

/-- Projection is relative to the identity of the compared contract. -/
def project (s : Stor) (ethBalance : Adr → B256) (self : Adr) : LogicalState where
  balances := balanceOf s
  nonces := nonceOf s
  flashMinted := flashMintedOf s
  eth := ethOf ethBalance self

abbrev AllowancePair := Adr × Adr

def AllowanceNoncolliding (observed : Finset AllowancePair) : Prop :=
  ∀ p ∈ observed, ∀ q ∈ observed,
    allowanceKey p.1 p.2 = allowanceKey q.1 q.2 → p = q

def ObservedAllowances (observed : Finset AllowancePair) (s : Stor)
    (logical : AllowancePair → B256) : Prop :=
  AllowanceNoncolliding observed ∧
    ∀ p ∈ observed, logical p = allowanceOf s p.1 p.2

/-- Explicitly maps the deployed reference's `address(this)` to the Blanc
instance's `address(this)` while leaving ordinary non-self addresses fixed. -/
structure AddressCorrespondence where
  referenceSelf : Adr
  blancSelf : Adr

def AddressCorrespondence.Rel (c : AddressCorrespondence)
    (reference blanc : Adr) : Prop :=
  (reference = c.referenceSelf ∧ blanc = c.blancSelf) ∨
  (reference ≠ c.referenceSelf ∧ blanc ≠ c.blancSelf ∧ reference = blanc)

end Weth10

end Blanc
