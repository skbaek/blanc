-- Exact functional observations for WETH10's ERC-2612 permit endpoint.
--
-- This module deliberately stays separate from `Weth10Sound`: permit is an
-- authentication theorem, not a consequence of the backing-only FuncSound
-- relation.  Its calldata and hash images are functions of the canonical
-- inputs, rather than descriptions of whatever the runtime happened to read.

import Blanc.Weth10Functional
import Blanc.Ladder
import Blanc.Weth10Errors

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Weth10

/-! ## Canonical static calldata

`Sevm.DecodesCallWithTail` serves the dynamic `bytes` endpoints.  Permit has
seven static words, so its canonical encoder is stated locally and without
mentioning any Blanc instruction. -/

abbrev permitSelector : B256 :=
  selector "permit"
    [.address, .address, .uint256, .uint256, .uint 8, .bytes 32, .bytes 32]

def permitCallData (owner spender : Adr) (value deadline : B256)
    (v : UInt8) (r s : B256) : Bytes :=
  abiSelectorBytes permitSelector ++
    (owner.toB256.toBytes ++
      (spender.toB256.toBytes ++
        (value.toBytes ++
          (deadline.toBytes ++
            ((Nat.toB256 v.toNat).toBytes ++ (r.toBytes ++ s.toBytes))))))

def DecodesPermit (e : Sevm) (owner spender : Adr)
    (value deadline : B256) (v : UInt8) (r s : B256) : Prop :=
  e.data = permitCallData owner spender value deadline v r s

lemma decodesPermit_split {e : Sevm} {owner spender : Adr}
    {value deadline : B256} {v : UInt8} {r s : B256}
    (h : DecodesPermit e owner spender value deadline v r s) :
    e.data = abiSelectorBytes permitSelector ++
      (owner.toB256.toBytes ++
        (spender.toB256.toBytes ++
          (value.toBytes ++
            (deadline.toBytes ++
              ((Nat.toB256 v.toNat).toBytes ++ (r.toBytes ++ s.toBytes)))))) := h

lemma argWord_zero_of_decodesPermit {e : Sevm} {owner spender : Adr}
    {value deadline : B256} {v : UInt8} {r s : B256}
    (h : DecodesPermit e owner spender value deadline v r s) :
    Sevm.argWord e 0 = owner.toB256 :=
  dataWord_of_append
    (by rw [abiSelectorBytes_length]; rfl) (decodesPermit_split h)

lemma argWord_one_of_decodesPermit {e : Sevm} {owner spender : Adr}
    {value deadline : B256} {v : UInt8} {r s : B256}
    (h : DecodesPermit e owner spender value deadline v r s) :
    Sevm.argWord e 1 = spender.toB256 := by
  have hd : e.data =
      (abiSelectorBytes permitSelector ++ owner.toB256.toBytes) ++
      (spender.toB256.toBytes ++
        (value.toBytes ++
          (deadline.toBytes ++
            ((Nat.toB256 v.toNat).toBytes ++ (r.toBytes ++ s.toBytes))))) := by
    rw [List.append_assoc]
    exact decodesPermit_split h
  exact dataWord_of_append
    (by rw [List.length_append, abiSelectorBytes_length,
      B256.length_toBytes]; rfl) hd

lemma argWord_two_of_decodesPermit {e : Sevm} {owner spender : Adr}
    {value deadline : B256} {v : UInt8} {r s : B256}
    (h : DecodesPermit e owner spender value deadline v r s) :
    Sevm.argWord e 2 = value := by
  have hd : e.data =
      (abiSelectorBytes permitSelector ++ owner.toB256.toBytes ++
        spender.toB256.toBytes) ++
      (value.toBytes ++
        (deadline.toBytes ++
          ((Nat.toB256 v.toNat).toBytes ++ (r.toBytes ++ s.toBytes)))) := by
    rw [List.append_assoc, List.append_assoc]
    exact decodesPermit_split h
  exact dataWord_of_append
    (by rw [List.length_append, List.length_append, abiSelectorBytes_length,
      B256.length_toBytes, B256.length_toBytes]; rfl) hd

lemma argWord_three_of_decodesPermit {e : Sevm} {owner spender : Adr}
    {value deadline : B256} {v : UInt8} {r s : B256}
    (h : DecodesPermit e owner spender value deadline v r s) :
    Sevm.argWord e 3 = deadline := by
  have hd : e.data =
      (abiSelectorBytes permitSelector ++ owner.toB256.toBytes ++
        spender.toB256.toBytes ++ value.toBytes) ++
      (deadline.toBytes ++
        ((Nat.toB256 v.toNat).toBytes ++ (r.toBytes ++ s.toBytes))) := by
    rw [List.append_assoc, List.append_assoc, List.append_assoc]
    exact decodesPermit_split h
  exact dataWord_of_append
    (by rw [List.length_append, List.length_append, List.length_append,
      abiSelectorBytes_length, B256.length_toBytes, B256.length_toBytes,
      B256.length_toBytes]; rfl) hd

lemma argWord_four_of_decodesPermit {e : Sevm} {owner spender : Adr}
    {value deadline : B256} {v : UInt8} {r s : B256}
    (h : DecodesPermit e owner spender value deadline v r s) :
    Sevm.argWord e 4 = Nat.toB256 v.toNat := by
  have hd : e.data =
      (abiSelectorBytes permitSelector ++ owner.toB256.toBytes ++
        spender.toB256.toBytes ++ value.toBytes ++ deadline.toBytes) ++
      ((Nat.toB256 v.toNat).toBytes ++ (r.toBytes ++ s.toBytes)) := by
    rw [List.append_assoc, List.append_assoc, List.append_assoc,
      List.append_assoc]
    exact decodesPermit_split h
  exact dataWord_of_append
    (by rw [List.length_append, List.length_append, List.length_append,
      List.length_append, abiSelectorBytes_length, B256.length_toBytes,
      B256.length_toBytes, B256.length_toBytes, B256.length_toBytes]; rfl) hd

lemma argWord_five_of_decodesPermit {e : Sevm} {owner spender : Adr}
    {value deadline : B256} {v : UInt8} {r s : B256}
    (h : DecodesPermit e owner spender value deadline v r s) :
    Sevm.argWord e 5 = r := by
  have hd : e.data =
      (abiSelectorBytes permitSelector ++ owner.toB256.toBytes ++
        spender.toB256.toBytes ++ value.toBytes ++ deadline.toBytes ++
        (Nat.toB256 v.toNat).toBytes) ++ (r.toBytes ++ s.toBytes) := by
    rw [List.append_assoc, List.append_assoc, List.append_assoc,
      List.append_assoc, List.append_assoc]
    exact decodesPermit_split h
  exact dataWord_of_append
    (by rw [List.length_append, List.length_append, List.length_append,
      List.length_append, List.length_append, abiSelectorBytes_length,
      B256.length_toBytes, B256.length_toBytes, B256.length_toBytes,
      B256.length_toBytes, B256.length_toBytes]; rfl) hd

lemma argWord_six_of_decodesPermit {e : Sevm} {owner spender : Adr}
    {value deadline : B256} {v : UInt8} {r s : B256}
    (h : DecodesPermit e owner spender value deadline v r s) :
    Sevm.argWord e 6 = s := by
  have hd : e.data =
      (abiSelectorBytes permitSelector ++ owner.toB256.toBytes ++
        spender.toB256.toBytes ++ value.toBytes ++ deadline.toBytes ++
        (Nat.toB256 v.toNat).toBytes ++ r.toBytes) ++ s.toBytes := by
    rw [List.append_assoc, List.append_assoc, List.append_assoc,
      List.append_assoc, List.append_assoc, List.append_assoc]
    exact decodesPermit_split h
  exact dataWord_of_append
    (by
      rw [List.length_append, List.length_append, List.length_append,
        List.length_append, List.length_append, List.length_append,
        abiSelectorBytes_length, B256.length_toBytes, B256.length_toBytes,
        B256.length_toBytes, B256.length_toBytes, B256.length_toBytes,
        B256.length_toBytes]
      rfl) hd

theorem argWords_of_decodesPermit {e : Sevm} {owner spender : Adr}
    {value deadline : B256} {v : UInt8} {r s : B256}
    (h : DecodesPermit e owner spender value deadline v r s) :
    Sevm.argWord e 0 = owner.toB256 ∧
    Sevm.argWord e 1 = spender.toB256 ∧
    Sevm.argWord e 2 = value ∧
    Sevm.argWord e 3 = deadline ∧
    Sevm.argWord e 4 = Nat.toB256 v.toNat ∧
    Sevm.argWord e 5 = r ∧ Sevm.argWord e 6 = s :=
  ⟨argWord_zero_of_decodesPermit h, argWord_one_of_decodesPermit h,
    argWord_two_of_decodesPermit h, argWord_three_of_decodesPermit h,
    argWord_four_of_decodesPermit h, argWord_five_of_decodesPermit h,
    argWord_six_of_decodesPermit h⟩

/-! ## Exact EIP-712 images

These are the byte strings consumed by the two KECCAK256 instructions and by
precompile 1.  They are definitions over the public inputs, so later machine
lemmas can identify memory reads with them without assuming any cryptographic
property of keccak or secp256k1. -/

def permitStructImage (owner spender : Adr) (value nonce deadline : B256) :
    Bytes :=
  PERMIT_TYPEHASH.toBytes ++ owner.toB256.toBytes ++ spender.toB256.toBytes ++
    value.toBytes ++ nonce.toBytes ++ deadline.toBytes

def permitStructHash (owner spender : Adr) (value nonce deadline : B256) :
    B256 :=
  (permitStructImage owner spender value nonce deadline).keccak

/-- The exact straight-line struct-hash suffix embedded in `permit`. -/
def permitStructPrepare : Line :=
  [pushB256 PERMIT_TYPEHASH] ++ mstoreAt 0 ++
  argCopy 1 0 3 ++ arg 3 ++ mstoreAt 5 ++
  pushList [192, 0] ++ [kec]

/-- The exact nonce-read/tentative-increment prefix embedded after permit's
deadline guard.  It retains the chain id for domain selection. -/
def permitNoncePrepare : Line :=
  [chainid] ++ addressArg 0 ++ [dup 0] ++ tagNonceKey ++
  [dup 0, sload, dup 0] ++ mstoreAt 4 ++
  [pushB256 1, add, swap 0, sstore, pop]

/-- Chain-selection and tail-call suffix after the struct hash is on top of
the retained chain id. -/
def permitDomainDispatch (dp : DeployParams) : Func :=
  dup 1 ::: pushDeployWord dp.deploymentChainId ::: eq :::
  (swap 0 ::: pop ::: pushDeployWord dp.cachedDomainSeparator :::
    .call permitRecoverSlot) <?>
  (swap 0 ::: calculateDomainSeparator +++ .call permitRecoverSlot)

/-- Successful continuation selected by the strict deadline guard. -/
def permitAfterDeadline (dp : DeployParams) : Func :=
  permitNoncePrepare +++ permitStructPrepare +++ permitDomainDispatch dp

lemma permit_eq_deadlineGuard (dp : DeployParams) :
    permit dp = arg 3 +++ [timestamp, gt] +++
      ((.call expiredPermitErrorSlot) <?> permitAfterDeadline dp) := by
  unfold permit permitAfterDeadline permitDomainDispatch
  rfl

/-- Exact straight-line deadline test at the head of `permit`. -/
def permitDeadlineLine : Line := arg 3 ++ [Ninst.timestamp, Ninst.gt]

/-- Reader-level image after nonce word 4 and the struct-hash suffix have
overwritten all six words of the permit struct. -/
def permitStructMemoryImage (img : Bytes) (owner spender : Adr)
    (value nonce deadline : B256) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt img 128 nonce.toBytes)
        0 PERMIT_TYPEHASH.toBytes)
      32 (owner.toB256.toBytes ++ spender.toB256.toBytes ++ value.toBytes))
    160 deadline.toBytes

def permitDomainImage (chainId : B256) (verifyingContract : Adr) : Bytes :=
  DOMAIN_TYPEHASH.toBytes ++ NAME_HASH.toBytes ++ VERSION_HASH.toBytes ++
    chainId.toBytes ++ verifyingContract.toB256.toBytes

/-- Complete reader-level memory image after the recomputed-domain fragment.
The chain word is stored first at word 3; the five final words nevertheless
form the canonical EIP-712 domain image independently of prior memory. -/
def permitDomainMemoryImage (img : Bytes) (chainId : B256)
    (verifyingContract : Adr) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt
          (Bytes.writeAt img 96 chainId.toBytes)
          0 DOMAIN_TYPEHASH.toBytes)
        32 NAME_HASH.toBytes)
      64 VERSION_HASH.toBytes)
    128 verifyingContract.toB256.toBytes

def permitDomainSeparator (dp : DeployParams) (chainId : B256)
    (verifyingContract : Adr) : B256 :=
  if chainId = dp.deploymentChainId then dp.cachedDomainSeparator
  else (permitDomainImage chainId verifyingContract).keccak

def permitDigestImage (domain structHash : B256) : Bytes :=
  eip712PrefixWord.toBytes.take 2 ++ domain.toBytes ++ structHash.toBytes

def permitDigestValue (domain structHash : B256) : B256 :=
  (permitDigestImage domain structHash).keccak

def permitEcrecoverImage (digest : B256) (v : UInt8) (r s : B256) : Bytes :=
  digest.toBytes ++ (Nat.toB256 v.toNat).toBytes ++ r.toBytes ++ s.toBytes

theorem permitStructImage_length (owner spender : Adr) (value nonce deadline : B256) :
    (permitStructImage owner spender value nonce deadline).length = 192 := by
  simp [permitStructImage, B256.length_toBytes]

lemma permitStruct_window (img : Bytes) (owner spender : Adr)
    (value nonce deadline : B256) :
    (permitStructMemoryImage img owner spender value nonce deadline).sliceD
        0 192 0 = permitStructImage owner spender value nonce deadline := by
  have ht : PERMIT_TYPEHASH.toBytes.length = 32 :=
    B256.length_toBytes PERMIT_TYPEHASH
  have ho : owner.toB256.toBytes.length = 32 :=
    B256.length_toBytes owner.toB256
  have hs : spender.toB256.toBytes.length = 32 :=
    B256.length_toBytes spender.toB256
  have hv : value.toBytes.length = 32 := B256.length_toBytes value
  have hn : nonce.toBytes.length = 32 := B256.length_toBytes nonce
  have hd : deadline.toBytes.length = 32 := B256.length_toBytes deadline
  let T := owner.toB256.toBytes ++ spender.toB256.toBytes ++ value.toBytes
  have hT : T.length = 96 := by
    unfold T
    simp only [List.length_append, ho, hs, hv]
  let A := Bytes.writeAt img 128 nonce.toBytes
  let B := Bytes.writeAt A 0 PERMIT_TYPEHASH.toBytes
  let C := Bytes.writeAt B 32 T
  have eA : A = List.takeD 128 img 0 ++
      (nonce.toBytes ++ img.drop 160) := by
    unfold A Bytes.writeAt
    rw [hn, List.append_assoc]
  have eAdrop : A.drop 128 = nonce.toBytes ++ img.drop 160 := by
    rw [eA, List.drop_append_of_le_length (by rw [List.takeD_length]),
      List.drop_eq_nil_of_le (by rw [List.takeD_length]), List.nil_append]
  have eB : B = PERMIT_TYPEHASH.toBytes ++ A.drop 32 := by
    unfold B Bytes.writeAt
    rw [ht, show List.takeD 0 A 0 = [] from rfl, List.nil_append,
      Nat.zero_add]
  have eBtake : List.takeD 32 B 0 = PERMIT_TYPEHASH.toBytes := by
    rw [eB, List.takeD_eq_take _ (by rw [List.length_append, ht]; omega),
      List.take_length_append' ht.symm]
  have eBdrop : B.drop 128 = A.drop 128 := by
    have hdrop : PERMIT_TYPEHASH.toBytes.drop 128 = [] :=
      List.drop_eq_nil_of_le (by rw [ht]; omega)
    rw [eB, List.drop_append, ht, hdrop, List.nil_append,
      show 128 - 32 = 96 by omega, List.drop_drop,
      show 96 + 32 = 128 by omega]
  have eC : C = PERMIT_TYPEHASH.toBytes ++
      (T ++ (nonce.toBytes ++ img.drop 160)) := by
    unfold C Bytes.writeAt
    rw [hT, eBtake, eBdrop, eAdrop, List.append_assoc]
  have eCtake : List.takeD 160 C 0 =
      PERMIT_TYPEHASH.toBytes ++ T ++ nonce.toBytes := by
    rw [eC, List.takeD_eq_take _ (by
      simp only [List.length_append, ht, hT, hn]
      omega)]
    rw [← List.append_assoc, ← List.append_assoc,
      List.take_length_append' (by
        simp only [List.length_append, ht, hT, hn])]
  change (Bytes.writeAt C 160 deadline.toBytes).sliceD 0 192 0 = _
  unfold permitStructImage Bytes.writeAt List.sliceD
  rw [hd, eCtake, List.drop_zero,
    List.takeD_eq_take _ (by
      simp only [List.length_append, ht, hT, hn, hd]
      omega)]
  change List.take 192
    (((PERMIT_TYPEHASH.toBytes ++ T ++ nonce.toBytes) ++ deadline.toBytes) ++
      C.drop 192) =
    PERMIT_TYPEHASH.toBytes ++ T ++ nonce.toBytes ++ deadline.toBytes
  rw [List.take_length_append' (by
    simp only [List.length_append, ht, hT, hn, hd])]

lemma permitData_args_zero_three {e : Sevm} {owner spender : Adr}
    {value deadline : B256} {v : UInt8} {r s : B256}
    (h : DecodesPermit e owner spender value deadline v r s) :
    e.data.sliceD 4 96 0 =
      owner.toB256.toBytes ++ spender.toB256.toBytes ++ value.toBytes := by
  rw [h]
  unfold permitCallData List.sliceD
  rw [List.drop_length_append' (abiSelectorBytes_length permitSelector).symm]
  rw [← List.append_assoc, ← List.append_assoc,
    List.takeD_eq_take _ (by
      simp only [List.length_append, B256.length_toBytes]
      omega),
    List.take_length_append' (by
      simp only [List.length_append, B256.length_toBytes])]

lemma permitData_args_zero_two {e : Sevm} {owner spender : Adr}
    {value deadline : B256} {v : UInt8} {r s : B256}
    (h : DecodesPermit e owner spender value deadline v r s) :
    e.data.sliceD 4 64 0 =
      owner.toB256.toBytes ++ spender.toB256.toBytes := by
  rw [h]
  unfold permitCallData List.sliceD
  rw [List.drop_length_append' (abiSelectorBytes_length permitSelector).symm]
  rw [← List.append_assoc,
    List.takeD_eq_take _ (by
      simp only [List.length_append, B256.length_toBytes]
      omega),
    List.take_length_append' (by
      simp only [List.length_append, B256.length_toBytes])]

lemma permitAllowanceRuntimeKey_eq (owner spender : Adr) :
    allowanceTagWord |||
        (allowancePayloadMask &&&
          (owner.toB256.toBytes ++ spender.toB256.toBytes).keccak) =
      allowanceKey owner spender := by
  rw [allowanceKey_formula, low254_formula]
  unfold allowanceTagWord allowancePayloadMask allowanceHash
  apply congrArg (Nat.toB256 (2 ^ 255) ||| ·)
  rcases (owner.toB256.toBytes ++ spender.toB256.toBytes).keccak with
    ⟨⟨a, b⟩, ⟨c, d⟩⟩
  apply Prod.ext <;> apply Prod.ext <;> exact UInt64.and_comm _ _

theorem permitDomainImage_length (chainId : B256) (verifyingContract : Adr) :
    (permitDomainImage chainId verifyingContract).length = 160 := by
  simp [permitDomainImage, B256.length_toBytes]

lemma permitDomain_window (img : Bytes) (chainId : B256)
    (verifyingContract : Adr) :
    (permitDomainMemoryImage img chainId verifyingContract).sliceD 0 160 0 =
      permitDomainImage chainId verifyingContract := by
  have ht : DOMAIN_TYPEHASH.toBytes.length = 32 :=
    B256.length_toBytes DOMAIN_TYPEHASH
  have hn : NAME_HASH.toBytes.length = 32 :=
    B256.length_toBytes NAME_HASH
  have hv : VERSION_HASH.toBytes.length = 32 :=
    B256.length_toBytes VERSION_HASH
  have hc : chainId.toBytes.length = 32 := B256.length_toBytes chainId
  have ha : verifyingContract.toB256.toBytes.length = 32 :=
    B256.length_toBytes verifyingContract.toB256
  let A := Bytes.writeAt img 96 chainId.toBytes
  let B := Bytes.writeAt A 0 DOMAIN_TYPEHASH.toBytes
  let C := Bytes.writeAt B 32 NAME_HASH.toBytes
  let D := Bytes.writeAt C 64 VERSION_HASH.toBytes
  have eA : A = List.takeD 96 img 0 ++
      (chainId.toBytes ++ img.drop 128) := by
    unfold A Bytes.writeAt
    rw [hc, List.append_assoc]
  have eAdrop : A.drop 96 = chainId.toBytes ++ img.drop 128 := by
    rw [eA, List.drop_append_of_le_length (by rw [List.takeD_length]),
      List.drop_eq_nil_of_le (by rw [List.takeD_length]), List.nil_append]
  have eB : B = DOMAIN_TYPEHASH.toBytes ++ A.drop 32 := by
    unfold B Bytes.writeAt
    rw [ht, show List.takeD 0 A 0 = [] from rfl, List.nil_append,
      Nat.zero_add]
  have eBtake : List.takeD 32 B 0 = DOMAIN_TYPEHASH.toBytes := by
    rw [eB, List.takeD_eq_take _ (by rw [List.length_append, ht]; omega),
      List.take_length_append' ht.symm]
  have eBdrop : B.drop 64 = A.drop 64 := by
    rw [eB, List.drop_append, ht,
      List.drop_eq_nil_of_le (by omega), List.nil_append,
      show 64 - 32 = 32 by omega, List.drop_drop,
      show 32 + 32 = 64 by omega]
  have eC : C = DOMAIN_TYPEHASH.toBytes ++
      (NAME_HASH.toBytes ++ A.drop 64) := by
    unfold C Bytes.writeAt
    rw [hn, eBtake, eBdrop, List.append_assoc]
  have eCtake : List.takeD 64 C 0 =
      DOMAIN_TYPEHASH.toBytes ++ NAME_HASH.toBytes := by
    rw [eC, List.takeD_eq_take _ (by
      rw [List.length_append, ht, List.length_append, hn]
      omega)]
    rw [← List.append_assoc,
      List.take_length_append' (by rw [List.length_append, ht, hn])]
  have eCdrop : C.drop 96 = A.drop 96 := by
    have hdrop :
        (DOMAIN_TYPEHASH.toBytes ++ NAME_HASH.toBytes).drop 96 = [] :=
      List.drop_eq_nil_of_le (by rw [List.length_append, ht, hn]; omega)
    rw [eC, ← List.append_assoc, List.drop_append,
      show (DOMAIN_TYPEHASH.toBytes ++ NAME_HASH.toBytes).length = 64 by
        rw [List.length_append, ht, hn],
      hdrop, List.nil_append,
      show 96 - 64 = 32 by omega, List.drop_drop,
      show 32 + 64 = 96 by omega]
  have eD : D = DOMAIN_TYPEHASH.toBytes ++
      (NAME_HASH.toBytes ++
        (VERSION_HASH.toBytes ++ (chainId.toBytes ++ img.drop 128))) := by
    unfold D Bytes.writeAt
    rw [hv, eCtake, eCdrop, eAdrop]
    simp only [List.append_assoc]
  have eDtake : List.takeD 128 D 0 =
      DOMAIN_TYPEHASH.toBytes ++ NAME_HASH.toBytes ++
        VERSION_HASH.toBytes ++ chainId.toBytes := by
    rw [eD, List.takeD_eq_take _ (by
      simp only [List.length_append, ht, hn, hv, hc]
      omega)]
    rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc,
      List.take_length_append' (by
        simp only [List.length_append, ht, hn, hv, hc])]
  change (Bytes.writeAt D 128 verifyingContract.toB256.toBytes).sliceD
      0 160 0 = _
  unfold permitDomainImage Bytes.writeAt List.sliceD
  rw [ha, eDtake, List.drop_zero,
    List.takeD_eq_take _ (by
      simp only [List.length_append, ht, hn, hv, hc, ha]
      omega)]
  change List.take 160
    ((DOMAIN_TYPEHASH.toBytes ++ NAME_HASH.toBytes ++
      VERSION_HASH.toBytes ++ chainId.toBytes ++
      verifyingContract.toB256.toBytes) ++ D.drop 160) =
    DOMAIN_TYPEHASH.toBytes ++ NAME_HASH.toBytes ++
      VERSION_HASH.toBytes ++ chainId.toBytes ++
      verifyingContract.toB256.toBytes
  rw [List.take_length_append' (by
    simp only [List.length_append, ht, hn, hv, hc, ha])]

theorem permitDigestImage_length (domain structHash : B256) :
    (permitDigestImage domain structHash).length = 66 := by
  simp [permitDigestImage, B256.length_toBytes]

theorem permitEcrecoverImage_length (digest : B256) (v : UInt8) (r s : B256) :
    (permitEcrecoverImage digest v r s).length = 128 := by
  simp [permitEcrecoverImage, B256.length_toBytes]

/-- Reader-level scratch image immediately before WETH10 executes its permit
`STATICCALL`: four ECRECOVER input words followed by the pre-zeroed output
word. -/
def permitRecoverMemoryImage (img : Bytes) (digest : B256) (v : UInt8)
    (r s : B256) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt
          (Bytes.writeAt img 0 digest.toBytes)
          32 (Nat.toB256 v.toNat).toBytes)
        64 r.toBytes)
      96 s.toBytes)
    128 (0 : B256).toBytes

lemma permitRecover_input_window (img : Bytes) (digest : B256) (v : UInt8)
    (r s : B256) :
    (permitRecoverMemoryImage img digest v r s).sliceD 0 128 0 =
      permitEcrecoverImage digest v r s := by
  have hd : digest.toBytes.length = 32 := B256.length_toBytes digest
  have hv : (Nat.toB256 v.toNat).toBytes.length = 32 :=
    B256.length_toBytes (Nat.toB256 v.toNat)
  have hr : r.toBytes.length = 32 := B256.length_toBytes r
  have hs : s.toBytes.length = 32 := B256.length_toBytes s
  have hz : (0 : B256).toBytes.length = 32 := B256.length_toBytes 0
  let A := Bytes.writeAt img 0 digest.toBytes
  let B := Bytes.writeAt A 32 (Nat.toB256 v.toNat).toBytes
  let C := Bytes.writeAt B 64 r.toBytes
  let D := Bytes.writeAt C 96 s.toBytes
  have eA : A = digest.toBytes ++ img.drop 32 := by
    unfold A Bytes.writeAt
    rw [hd, show List.takeD 0 img 0 = [] from rfl, List.nil_append,
      Nat.zero_add]
  have eAtake : List.takeD 32 A 0 = digest.toBytes := by
    rw [eA, List.takeD_eq_take _ (by rw [List.length_append, hd]; omega),
      List.take_length_append' hd.symm]
  have eAdrop : A.drop 64 = img.drop 64 := by
    rw [eA, List.drop_append, hd,
      List.drop_eq_nil_of_le (by
        rw [hd]
        omega), List.nil_append,
      show 64 - 32 = 32 by omega, List.drop_drop,
      show 32 + 32 = 64 by omega]
  have eB : B = digest.toBytes ++
      ((Nat.toB256 v.toNat).toBytes ++ img.drop 64) := by
    unfold B Bytes.writeAt
    rw [hv, eAtake, eAdrop, List.append_assoc]
  have eBtake : List.takeD 64 B 0 =
      digest.toBytes ++ (Nat.toB256 v.toNat).toBytes := by
    rw [eB, List.takeD_eq_take _ (by
      simp only [List.length_append, hd, hv]
      omega)]
    rw [← List.append_assoc,
      List.take_length_append' (by rw [List.length_append, hd, hv])]
  have eBdrop : B.drop 96 = img.drop 96 := by
    rw [eB, ← List.append_assoc, List.drop_append,
      show (digest.toBytes ++ (Nat.toB256 v.toNat).toBytes).length = 64 by
        rw [List.length_append, hd, hv],
      List.drop_eq_nil_of_le (by
        rw [List.length_append, hd, hv]
        omega), List.nil_append,
      show 96 - 64 = 32 by omega, List.drop_drop,
      show 32 + 64 = 96 by omega]
  have eC : C = digest.toBytes ++
      ((Nat.toB256 v.toNat).toBytes ++ (r.toBytes ++ img.drop 96)) := by
    unfold C Bytes.writeAt
    rw [hr, eBtake, eBdrop]
    simp only [List.append_assoc]
  have eCtake : List.takeD 96 C 0 =
      digest.toBytes ++ (Nat.toB256 v.toNat).toBytes ++ r.toBytes := by
    rw [eC, List.takeD_eq_take _ (by
      simp only [List.length_append, hd, hv, hr]
      omega)]
    rw [← List.append_assoc, ← List.append_assoc,
      List.take_length_append' (by
        simp only [List.length_append, hd, hv, hr])]
  have eCdrop : C.drop 128 = img.drop 128 := by
    rw [eC, ← List.append_assoc, ← List.append_assoc, List.drop_append,
      show (digest.toBytes ++ (Nat.toB256 v.toNat).toBytes ++ r.toBytes).length
          = 96 by simp only [List.length_append, hd, hv, hr],
      List.drop_eq_nil_of_le (by
        simp only [List.length_append, hd, hv, hr]
        omega), List.nil_append,
      show 128 - 96 = 32 by omega, List.drop_drop,
      show 32 + 96 = 128 by omega]
  have eD : D = digest.toBytes ++
      ((Nat.toB256 v.toNat).toBytes ++
        (r.toBytes ++ (s.toBytes ++ img.drop 128))) := by
    unfold D Bytes.writeAt
    rw [hs, eCtake, eCdrop]
    simp only [List.append_assoc]
  have eDtake : List.takeD 128 D 0 =
      digest.toBytes ++ (Nat.toB256 v.toNat).toBytes ++
        r.toBytes ++ s.toBytes := by
    rw [eD, List.takeD_eq_take _ (by
      simp only [List.length_append, hd, hv, hr, hs]
      omega)]
    rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc,
      List.take_length_append' (by
        simp only [List.length_append, hd, hv, hr, hs])]
  change (Bytes.writeAt D 128 (0 : B256).toBytes).sliceD 0 128 0 = _
  unfold permitEcrecoverImage Bytes.writeAt List.sliceD
  rw [hz, eDtake, List.drop_zero,
    List.takeD_eq_take _ (by
      simp only [List.length_append, hd, hv, hr, hs, hz]
      omega)]
  let P := digest.toBytes ++ (Nat.toB256 v.toNat).toBytes ++
    r.toBytes ++ s.toBytes
  have hP : P.length = 128 := by
    unfold P
    simp only [List.length_append, hd, hv, hr, hs]
  change List.take 128 (P ++ ((0 : B256).toBytes ++ D.drop 160)) = P
  rw [List.take_length_append' hP.symm]

lemma permitRecover_output_window (img : Bytes) (digest : B256) (v : UInt8)
    (r s : B256) :
    (permitRecoverMemoryImage img digest v r s).sliceD 128 32 0 =
      (0 : B256).toBytes := by
  unfold permitRecoverMemoryImage
  rw [← B256.length_toBytes (0 : B256)]
  exact Bytes.sliceD_writeAt
      (Bytes.writeAt
        (Bytes.writeAt
          (Bytes.writeAt
            (Bytes.writeAt img 0 digest.toBytes)
            32 (Nat.toB256 v.toNat).toBytes)
          64 r.toBytes)
        96 s.toBytes)
      (0 : B256).toBytes 128

/-! ## Precompile-1 image and result

`permitEcrecoverOutput` is intentionally the transparent Jaune spectrum:
malformed `v`, zero/out-of-range scalars, and failed recovery all return empty
bytes successfully; a recovered address returns one 32-byte canonical word.
This is not a cryptographic correctness axiom.  It is the exact result of
Jaune's `secp256k1.recover` on the four words WETH10 supplied. -/

def permitEcrecoverOutput (digest : B256) (v : UInt8) (r s : B256) : Bytes :=
  let vOpt := match Nat.toB256 v.toNat with
    | 0x1B => some false
    | 0x1C => some true
    | _ => none
  match vOpt with
  | none => []
  | some parity =>
    if r = 0 ∨ s = 0 ∨ r ≥ secp256k1.curveOrder.toB256 ∨
        s ≥ secp256k1.curveOrder.toB256 then []
    else
      match secp256k1.recover digest parity r s with
      | none => []
      | some adr => adr.toB256.toBytes

/-- The same spectrum in Jaune's native precompile result type.  Keeping this
definition transparent avoids postulating that an arbitrary recovery succeeds. -/
def permitEcrecoverResult (digest : B256) (v : UInt8) (r s : B256) :
    PrecompResult :=
  let vOpt := match Nat.toB256 v.toNat with
    | 0x1B => some false
    | 0x1C => some true
    | _ => none
  match vOpt with
  | none => .ok gasEcrecover []
  | some parity =>
    if r = 0 ∨ s = 0 ∨ r ≥ secp256k1.curveOrder.toB256 ∨
        s ≥ secp256k1.curveOrder.toB256 then .ok gasEcrecover []
    else
      match secp256k1.recover digest parity r s with
      | none => .ok gasEcrecover []
      | some adr => .ok gasEcrecover adr.toB256.toBytes

def permitRecoveredSignerWord (digest : B256) (v : UInt8) (r s : B256) :
    B256 :=
  Bytes.toB256 (permitEcrecoverOutput digest v r s)

lemma permitEcrecoverResult_eq (digest : B256) (v : UInt8) (r s : B256) :
    permitEcrecoverResult digest v r s =
      .ok gasEcrecover (permitEcrecoverOutput digest v r s) := by
  unfold permitEcrecoverResult permitEcrecoverOutput
  split
  case h_1 =>
    split
    · rfl
    · cases hrec : secp256k1.recover digest false r s <;> simp [hrec]
  case h_2 =>
    split
    · rfl
    · cases hrec : secp256k1.recover digest true r s <;> simp [hrec]
  case h_3 => rfl

private lemma toB256_sliceD_word {idx : Nat} {pre post : Bytes} {w : B256}
    (hlen : idx = pre.length) :
    Bytes.toB256 ((pre ++ (w.toBytes ++ post)).sliceD idx 32 0) = w := by
  simp only [List.sliceD]
  rw [List.drop_length_append' hlen,
    List.takeD_eq_take _ (by simp [List.length_append, B256.length_toBytes]),
    List.take_length_append' (B256.length_toBytes w).symm,
    B256.toB256_toBytes]

private lemma toB256_sliceD_word₀ {post : Bytes} {w : B256} :
    Bytes.toB256 ((w.toBytes ++ post).sliceD 0 32 0) = w := by
  simpa using toB256_sliceD_word (idx := 0) (pre := []) (w := w)
    (post := post) rfl

lemma permitEcrecoverImage_word_zero (digest : B256) (v : UInt8)
    (r s : B256) :
    Bytes.toB256 ((permitEcrecoverImage digest v r s).sliceD 0 32 0) =
      digest := by
  unfold permitEcrecoverImage
  rw [List.append_assoc, List.append_assoc]
  exact toB256_sliceD_word₀

lemma permitEcrecoverImage_word_one (digest : B256) (v : UInt8)
    (r s : B256) :
    Bytes.toB256 ((permitEcrecoverImage digest v r s).sliceD 32 32 0) =
      Nat.toB256 v.toNat := by
  unfold permitEcrecoverImage
  rw [List.append_assoc, List.append_assoc]
  exact toB256_sliceD_word (idx := 32) (pre := digest.toBytes)
    (w := Nat.toB256 v.toNat) (post := r.toBytes ++ s.toBytes)
    (by rw [B256.length_toBytes])

lemma permitEcrecoverImage_word_two (digest : B256) (v : UInt8)
    (r s : B256) :
    Bytes.toB256 ((permitEcrecoverImage digest v r s).sliceD 64 32 0) = r := by
  unfold permitEcrecoverImage
  rw [List.append_assoc (digest.toBytes ++ (Nat.toB256 v.toNat).toBytes)]
  exact toB256_sliceD_word (idx := 64)
    (pre := digest.toBytes ++ (Nat.toB256 v.toNat).toBytes)
    (w := r) (post := s.toBytes)
    (by rw [List.length_append, B256.length_toBytes, B256.length_toBytes])

lemma permitEcrecoverImage_word_three (digest : B256) (v : UInt8)
    (r s : B256) :
    Bytes.toB256 ((permitEcrecoverImage digest v r s).sliceD 96 32 0) = s := by
  unfold permitEcrecoverImage
  rw [show s.toBytes = s.toBytes ++ ([] : Bytes) from
    (List.append_nil _).symm]
  exact toB256_sliceD_word (idx := 96)
    (pre := (digest.toBytes ++ (Nat.toB256 v.toNat).toBytes) ++ r.toBytes)
    (w := s) (post := []) (by
    rw [List.length_append, List.length_append, B256.length_toBytes,
      B256.length_toBytes, B256.length_toBytes])

theorem permitEcrecoverResult_spectrum (digest : B256) (v : UInt8)
    (r s : B256) :
    permitEcrecoverResult digest v r s = .ok gasEcrecover [] ∨
      ∃ adr : Adr, permitEcrecoverResult digest v r s =
        .ok gasEcrecover adr.toB256.toBytes := by
  unfold permitEcrecoverResult
  split
  case h_1 =>
    split
    · exact Or.inl rfl
    · cases hrec : secp256k1.recover digest false r s with
      | none => exact Or.inl (by simp only [hrec])
      | some adr => exact Or.inr ⟨adr, by simp only [hrec]⟩
  case h_2 =>
    split
    · exact Or.inl rfl
    · cases hrec : secp256k1.recover digest true r s with
      | none => exact Or.inl (by simp only [hrec])
      | some adr => exact Or.inr ⟨adr, by simp only [hrec]⟩
  case h_3 => exact Or.inl rfl

/-- Exact ecrecover execution for WETH10's canonical 128-byte input. -/
theorem executeEcrecover_permitImage {evm : Evm} {digest : B256} {v : UInt8}
    {r s : B256}
    (hdata : evm.sta.data = permitEcrecoverImage digest v r s)
    (hgas : gasEcrecover ≤ evm.dyna.gasLeft) :
    executeEcrecover evm = permitEcrecoverResult digest v r s := by
  unfold executeEcrecover PrecompResult.chargeGas
  rw [if_pos hgas]
  simp only [hdata, permitEcrecoverImage_word_zero,
    permitEcrecoverImage_word_one, permitEcrecoverImage_word_two,
    permitEcrecoverImage_word_three]
  exact rfl

/-- The address-1 `executePrecomp` crossing: successful precompile execution
changes only gas/output on the child machine. -/
theorem executePrecomp_one_permitImage {evm : Evm} {digest : B256}
    {v : UInt8} {r s : B256}
    (hdata : evm.sta.data = permitEcrecoverImage digest v r s)
    (hgas : gasEcrecover ≤ evm.dyna.gasLeft) :
    executePrecomp evm 1 =
      applyPrecompResult evm (permitEcrecoverResult digest v r s) := by
  unfold executePrecomp
  change applyPrecompResult evm (executeEcrecover evm) = _
  rw [executeEcrecover_permitImage hdata hgas]

/-- The synchronous frame-level crossing used by WETH10's `STATICCALL`.
The hypotheses are precisely the generic frame facts: transfer preparation,
address-1 precompile selection, the canonical child input, and its fixed gas
charge.  No claim that signature recovery succeeds is assumed. -/
theorem Frame.enter_permitEcrecover {f : Frame} {benv : Benv}
    {digest : B256} {v : UInt8} {r s : B256}
    (h_bt : f.inner.benvAfterTransfer = .ok benv)
    (h_ca : (f.inner.withBenv benv).codeAddress = some 1)
    (h_pre :
      (!((f.inner.withBenv benv).disablePrecompiles) &&
        decide ((f.inner.withBenv benv).benv.stat.rules.isPrecomp 1)) = true)
    (hdata : (initEvm (f.inner.withBenv benv)).sta.data =
      permitEcrecoverImage digest v r s)
    (hgas : gasEcrecover ≤
      (initEvm (f.inner.withBenv benv)).dyna.gasLeft) :
    f.enter = .done
      (f.settle
        (applyPrecompResult (initEvm (f.inner.withBenv benv))
          (permitEcrecoverResult digest v r s))) := by
  rw [Frame.enter_eq_done_executePrecomp h_bt h_ca h_pre,
    executePrecomp_one_permitImage hdata hgas]

/-- A clean synchronous answer from address 1 necessarily paid ecrecover's
fixed charge.  This is the negative half of the precompile crossing: an
underfunded precompile is converted to an exceptional-halt child and therefore
cannot satisfy the clean-child premise exposed by `STATICCALL` inversion. -/
theorem gasEcrecover_le_of_processMessage_clean
    {sevm : Sevm} {parent child : Devm} {gas : Nat} {calldata : Bytes}
    {code : ByteArray} {xl : Xlot}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 1) = true)
    (hpm : ProcessMessage
      (callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
        calldata code false) xl (.ok child))
    (hclean : child.error.isSome = false) :
    gasEcrecover ≤ gas := by
  by_contra hgas
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp hpm
  unfold FrameBody at hbody
  rcases hbt :
      (callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
        calldata code false).benvAfterTransfer with e | benv <;>
    rw [hbt] at hbody
  · rw [hbody.2] at hset
    unfold processMessage.settle at hset
    cases hset
  · have hca :
        ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
          calldata code false).withBenv benv).codeAddress = some 1 := rfl
    rcases of_executeCode_someCode hca hbody with hpc | hinterp
    · have hexec := hpc.2.2
      rw [show executePrecomp
          (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
            calldata code false).withBenv benv)) 1 =
          applyPrecompResult
            (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
              calldata code false).withBenv benv))
            (executeEcrecover
              (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
                calldata code false).withBenv benv))) from rfl] at hexec
      unfold executeEcrecover PrecompResult.chargeGas at hexec
      rw [if_neg (by
        show ¬gasEcrecover ≤
          (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
            calldata code false).withBenv benv)).dyna.gasLeft
        change ¬gasEcrecover ≤ gas
        exact hgas)] at hexec
      simp only [applyPrecompResult, executeCode.handleError] at hexec
      rw [← hexec] at hset
      unfold processMessage.settle at hset
      simp only [bind, Except.bind, Option.isSome] at hset
      injection hset with hchild
      subst child
      change true = false at hclean
      contradiction
    · exact False.elim (hinterp.1 (by
        obtain ⟨st_mid, hsub, hbenv⟩ := of_benvAfterTransfer rfl hbt
        subst benv
        exact hpre))

/-- A clean synchronous address-1 child returns exactly the canonical
ECRECOVER image.  This identifies empty output with signature rejection and a
32-byte word with the recovered address; it does not assume recovery succeeds. -/
theorem output_of_processMessage_permitEcrecover_clean
    {sevm : Sevm} {parent child : Devm} {gas : Nat} {code : ByteArray}
    {xl : Xlot} {digest : B256} {v : UInt8} {sigR sigS : B256}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 1) = true)
    (hpm : ProcessMessage
      (callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
        (permitEcrecoverImage digest v sigR sigS) code false)
      xl (.ok child))
    (hclean : child.error.isSome = false) :
    child.output = permitEcrecoverOutput digest v sigR sigS := by
  have hgas : gasEcrecover ≤ gas :=
    gasEcrecover_le_of_processMessage_clean hpre hpm hclean
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp hpm
  unfold FrameBody at hbody
  rcases hbt :
      (callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
        (permitEcrecoverImage digest v sigR sigS) code false).benvAfterTransfer
    with e | benv <;> rw [hbt] at hbody
  · rw [hbody.2] at hset
    unfold processMessage.settle at hset
    cases hset
  · have hca :
        ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
          (permitEcrecoverImage digest v sigR sigS) code false).withBenv
          benv).codeAddress = some 1 := rfl
    rcases of_executeCode_someCode hca hbody with hpc | hinterp
    · have hexec := hpc.2.2
      rw [executePrecomp_one_permitImage (by rfl) (by
        change gasEcrecover ≤ gas
        exact hgas), permitEcrecoverResult_eq] at hexec
      simp only [applyPrecompResult, executeCode.handleError] at hexec
      rw [← hexec] at hset
      unfold processMessage.settle at hset
      simp only [bind, Except.bind, Option.isSome] at hset
      injection hset with hchild
      subst child
      rfl
    · exact False.elim (hinterp.1 (by
        obtain ⟨st_mid, hsub, hbenv⟩ := of_benvAfterTransfer rfl hbt
        subst benv
        exact hpre))

/-- An errored synchronous address-1 child has empty output.  ECRECOVER's
signature-rejection cases are ordinary clean successes, so the only enabled
precompile error here is the underfunded exceptional halt, whose output is
cleared before frame rollback. -/
theorem output_nil_of_processMessage_permitEcrecover_error
    {sevm : Sevm} {parent child : Devm} {gas : Nat} {code : ByteArray}
    {xl : Xlot} {digest : B256} {v : UInt8} {sigR sigS : B256}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 1) = true)
    (hpm : ProcessMessage
      (callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
        (permitEcrecoverImage digest v sigR sigS) code false)
      xl (.ok child))
    (herr : child.error.isSome = true) :
    child.output = [] := by
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp hpm
  unfold FrameBody at hbody
  rcases hbt :
      (callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
        (permitEcrecoverImage digest v sigR sigS) code false).benvAfterTransfer
    with e | benv <;> rw [hbt] at hbody
  · rw [hbody.2] at hset
    unfold processMessage.settle at hset
    cases hset
  · have hca :
        ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
          (permitEcrecoverImage digest v sigR sigS) code false).withBenv
          benv).codeAddress = some 1 := rfl
    rcases of_executeCode_someCode hca hbody with hpc | hinterp
    · have hexec := hpc.2.2
      by_cases hgas : gasEcrecover ≤ gas
      · rw [executePrecomp_one_permitImage (by rfl) (by
          change gasEcrecover ≤ gas
          exact hgas), permitEcrecoverResult_eq] at hexec
        simp only [applyPrecompResult, executeCode.handleError] at hexec
        rw [← hexec] at hset
        unfold processMessage.settle at hset
        simp only [bind, Except.bind, Option.isSome] at hset
        injection hset with hchild
        subst child
        change false = true at herr
        contradiction
      · rw [show executePrecomp
            (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true
              true (permitEcrecoverImage digest v sigR sigS) code false).withBenv
              benv)) 1 =
            applyPrecompResult
              (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true
                true (permitEcrecoverImage digest v sigR sigS) code
                false).withBenv benv))
              (executeEcrecover
                (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 1 1
                  true true (permitEcrecoverImage digest v sigR sigS) code
                  false).withBenv benv))) from rfl] at hexec
        unfold executeEcrecover PrecompResult.chargeGas at hexec
        rw [if_neg (by
          show ¬gasEcrecover ≤
            (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true
              true (permitEcrecoverImage digest v sigR sigS) code false).withBenv
              benv)).dyna.gasLeft
          change ¬gasEcrecover ≤ gas
          exact hgas)] at hexec
        simp only [applyPrecompResult, executeCode.handleError] at hexec
        rw [← hexec] at hset
        unfold processMessage.settle at hset
        simp only [bind, Except.bind, Option.isSome] at hset
        injection hset with hchild
        subst child
        rfl
    · exact False.elim (hinterp.1 (by
        obtain ⟨st_mid, hsub, hbenv⟩ := of_benvAfterTransfer rfl hbt
        subst benv
        exact hpre))

/-- A clean enabled ECRECOVER child changes neither persistent storage nor
logs.  Together with the exact output theorem above, this is the frame image
that the caller-side `STATICCALL` resume consumes.  Balance-transfer
preparation is deliberately projected only through storage: a zero-value
transfer can normalize a noncanonical account map, but cannot change any
account's storage. -/
theorem frame_of_processMessage_permitEcrecover_clean
    {sevm : Sevm} {parent child : Devm} {gas : Nat} {code : ByteArray}
    {xl : Xlot} {digest : B256} {v : UInt8} {sigR sigS : B256}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 1) = true)
    (hpm : ProcessMessage
      (callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
        (permitEcrecoverImage digest v sigR sigS) code false)
      xl (.ok child))
    (hclean : child.error.isSome = false) :
    (∀ a, Devm.getStor child a = Devm.getStor parent a) ∧
      child.logs = [] ∧
      child.output = permitEcrecoverOutput digest v sigR sigS := by
  have hout :=
    output_of_processMessage_permitEcrecover_clean hpre hpm hclean
  have hgas : gasEcrecover ≤ gas :=
    gasEcrecover_le_of_processMessage_clean hpre hpm hclean
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp hpm
  unfold FrameBody at hbody
  rcases hbt :
      (callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
        (permitEcrecoverImage digest v sigR sigS) code false).benvAfterTransfer
    with e | benv <;> rw [hbt] at hbody
  · rw [hbody.2] at hset
    unfold processMessage.settle at hset
    cases hset
  · obtain ⟨st_mid, hsub, hbenv⟩ := of_benvAfterTransfer rfl hbt
    subst benv
    have hca :
        ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
          (permitEcrecoverImage digest v sigR sigS) code false).withBenv
          (((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
            (permitEcrecoverImage digest v sigR sigS) code false).benv.withState
            st_mid).addBal 1 0)).codeAddress = some 1 := rfl
    rcases of_executeCode_someCode hca hbody with hpc | hinterp
    · have hexec := hpc.2.2
      rw [executePrecomp_one_permitImage (by rfl) (by
        change gasEcrecover ≤ gas
        exact hgas), permitEcrecoverResult_eq] at hexec
      simp only [applyPrecompResult, executeCode.handleError] at hexec
      rw [← hexec] at hset
      unfold processMessage.settle at hset
      simp only [bind, Except.bind, Option.isSome] at hset
      injection hset with hchild
      subst child
      refine ⟨?_, rfl, hout⟩
      intro a
      change ((st_mid.addBal 1 0).get a).stor = (parent.state.get a).stor
      exact (of_state_transfer_fields hsub).1 a
    · exact False.elim (hinterp.1 (by exact hpre))

/-! ## Recovery-call walk -/

/-- The scratch preparation and six `STATICCALL` operands, including the
runtime gas word.  Naming this prefix lets the call crossing stay separate
from the purely local memory writes. -/
def permitRecoverWrites : Line :=
  mstoreAt 0 ++
  arg 4 ++ mstoreAt 1 ++
  arg 5 ++ mstoreAt 2 ++
  arg 6 ++ mstoreAt 3 ++
  [pushB256 0] ++ mstoreAt 4 ++
  pushList [32, 128, 128, 0, 1]

def permitRecoverPrepare : Line := permitRecoverWrites ++ [gas]

lemma recoverPermitSigner_eq_prepare :
    recoverPermitSigner =
      permitRecoverPrepare ++ [statcall, pop, pushB256 128, mload] := by
  rfl

/-- The arbitrary word consumed into scratch word zero is enough to derive
the six exact ECRECOVER operands at the following `STATICCALL`. -/
theorem permitRecoverPrepare_stack
    {sevm : Sevm} {pre post : Devm} {word : B256} {tail : Stack}
    (hp : word :: tail <<+ pre.stack)
    (run : Line.Run sevm pre permitRecoverPrepare post) :
    ∃ gasWord : B256,
      gasWord :: (1 : B256) :: (0 : B256) :: (128 : B256) ::
        (128 : B256) :: (32 : B256) :: tail <<+ post.stack := by
  unfold permitRecoverPrepare permitRecoverWrites at run
  rcases of_run_append (mstoreAt 0) run with ⟨s1, h1, run⟩
  rcases of_run_mstoreAt_val h1 hp with ⟨hp1, _⟩
  rcases of_run_append (arg 4) run with ⟨s2, h2, run⟩
  have hp2 : Sevm.argWord sevm 4 :: tail <<+ s2.stack := prefix_of_arg hp1 h2
  rcases of_run_append (mstoreAt 1) run with ⟨s3, h3, run⟩
  rcases of_run_mstoreAt_val h3 hp2 with ⟨hp3, _⟩
  rcases of_run_append (arg 5) run with ⟨s4, h4, run⟩
  have hp4 : Sevm.argWord sevm 5 :: tail <<+ s4.stack := prefix_of_arg hp3 h4
  rcases of_run_append (mstoreAt 2) run with ⟨s5, h5, run⟩
  rcases of_run_mstoreAt_val h5 hp4 with ⟨hp5, _⟩
  rcases of_run_append (arg 6) run with ⟨s6, h6, run⟩
  have hp6 : Sevm.argWord sevm 6 :: tail <<+ s6.stack := prefix_of_arg hp5 h6
  rcases of_run_append (mstoreAt 3) run with ⟨s7, h7, run⟩
  rcases of_run_mstoreAt_val h7 hp6 with ⟨hp7, _⟩
  rcases of_run_append [pushB256 0] run with ⟨s8, h8, run⟩
  rcases Line.of_run_cons h8 with ⟨u8, q8, hnil⟩
  cases hnil
  have hp8 : (0 : B256) :: tail <<+ s8.stack :=
    prefix_of_push (of_run_pushB256 q8) hp7
  rcases of_run_append (mstoreAt 4) run with ⟨s9, h9, run⟩
  rcases of_run_mstoreAt_val h9 hp8 with ⟨hp9, _⟩
  rcases of_run_append (pushList [32, 128, 128, 0, 1]) run with
    ⟨s10, hpushes, hgas⟩
  simp only [pushList, List.map] at hpushes
  rcases Line.of_run_cons hpushes with ⟨u1, q1, hpushes⟩
  have hp10a : (32 : B256) :: tail <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp9
  rcases Line.of_run_cons hpushes with ⟨u2, q2, hpushes⟩
  have hp10b : (128 : B256) :: (32 : B256) :: tail <<+ u2.stack :=
    prefix_of_push (of_run_pushB256 q2) hp10a
  rcases Line.of_run_cons hpushes with ⟨u3, q3, hpushes⟩
  have hp10c : (128 : B256) :: (128 : B256) :: (32 : B256) ::
      tail <<+ u3.stack :=
    prefix_of_push (of_run_pushB256 q3) hp10b
  rcases Line.of_run_cons hpushes with ⟨u4, q4, hpushes⟩
  have hp10d : (0 : B256) :: (128 : B256) :: (128 : B256) ::
      (32 : B256) :: tail <<+ u4.stack :=
    prefix_of_push (of_run_pushB256 q4) hp10c
  rcases Line.of_run_cons hpushes with ⟨u5, q5, hnil⟩
  cases hnil
  have hp10 : (1 : B256) :: (0 : B256) :: (128 : B256) ::
      (128 : B256) :: (32 : B256) :: tail <<+ s10.stack :=
    prefix_of_push (of_run_pushB256 q5) hp10d
  rcases Line.of_run_cons hgas with ⟨s11, q11, hnil⟩
  cases hnil
  rcases of_run_gas q11 with ⟨gasWord, hpush⟩
  exact ⟨gasWord, prefix_of_push hpush hp10⟩

/-- Exact local image immediately before permit's `STATICCALL`. -/
theorem of_permitRecoverPrepare
    {sevm : Sevm} {s t : Devm}
    {owner spender : Adr} {value deadline digest : B256}
    {v : UInt8} {sigR sigS : B256} {xs : Stack} {img : Bytes}
    (hdec : DecodesPermit sevm owner spender value deadline v sigR sigS)
    (hp : digest :: xs <<+ s.stack)
    (hwf : Mem.Wf s.memory) (hr : Mem.Reads s.memory img)
    (run : Line.Run sevm s permitRecoverPrepare t) :
    ∃ g : B256,
      g :: (1 : B256) :: (0 : B256) :: (128 : B256) ::
        (128 : B256) :: (32 : B256) :: xs <<+ t.stack ∧
      Mem.Wf t.memory ∧
      Mem.Reads t.memory
        (permitRecoverMemoryImage img digest v sigR sigS) := by
  unfold permitRecoverPrepare permitRecoverWrites at run
  rcases of_run_append (mstoreAt 0) run with ⟨s1, h1, run⟩
  rcases of_run_mstoreAt_val h1 hp with ⟨hp1, hm1⟩
  rw [show (((0 : B256) * 32).toNat) = 0 from rfl] at hm1
  have hwf1 : Mem.Wf s1.memory := by
    rw [hm1]
    exact hwf.write _ _
  have hr1 : Mem.Reads s1.memory (Bytes.writeAt img 0 digest.toBytes) := by
    rw [hm1]
    exact Mem.Reads.write hwf hr 0 _
  rcases of_run_append (arg 4) run with ⟨s2, h2, run⟩
  have hp2 : Nat.toB256 v.toNat :: xs <<+ s2.stack := by
    rw [← argWord_four_of_decodesPermit hdec]
    exact prefix_of_arg hp1 h2
  have hm2 : s1.memory = s2.memory :=
    Line.of_inv Devm.memory (by line_inv) h2
  rcases of_run_append (mstoreAt 1) run with ⟨s3, h3, run⟩
  rcases of_run_mstoreAt_val h3 hp2 with ⟨hp3, hm3⟩
  rw [show (((1 : B256) * 32).toNat) = 32 from rfl] at hm3
  have hwf3 : Mem.Wf s3.memory := by
    rw [hm3, ← hm2]
    exact hwf1.write _ _
  have hr3 : Mem.Reads s3.memory
      (Bytes.writeAt (Bytes.writeAt img 0 digest.toBytes)
        32 (Nat.toB256 v.toNat).toBytes) := by
    rw [hm3, ← hm2]
    exact Mem.Reads.write hwf1 hr1 32 _
  rcases of_run_append (arg 5) run with ⟨s4, h4, run⟩
  have hp4 : sigR :: xs <<+ s4.stack := by
    rw [← argWord_five_of_decodesPermit hdec]
    exact prefix_of_arg hp3 h4
  have hm4 : s3.memory = s4.memory :=
    Line.of_inv Devm.memory (by line_inv) h4
  rcases of_run_append (mstoreAt 2) run with ⟨s5, h5, run⟩
  rcases of_run_mstoreAt_val h5 hp4 with ⟨hp5, hm5⟩
  rw [show (((2 : B256) * 32).toNat) = 64 from rfl] at hm5
  have hwf5 : Mem.Wf s5.memory := by
    rw [hm5, ← hm4]
    exact hwf3.write _ _
  have hr5 : Mem.Reads s5.memory
      (Bytes.writeAt
        (Bytes.writeAt (Bytes.writeAt img 0 digest.toBytes)
          32 (Nat.toB256 v.toNat).toBytes)
        64 sigR.toBytes) := by
    rw [hm5, ← hm4]
    exact Mem.Reads.write hwf3 hr3 64 _
  rcases of_run_append (arg 6) run with ⟨s6, h6, run⟩
  have hp6 : sigS :: xs <<+ s6.stack := by
    rw [← argWord_six_of_decodesPermit hdec]
    exact prefix_of_arg hp5 h6
  have hm6 : s5.memory = s6.memory :=
    Line.of_inv Devm.memory (by line_inv) h6
  rcases of_run_append (mstoreAt 3) run with ⟨s7, h7, run⟩
  rcases of_run_mstoreAt_val h7 hp6 with ⟨hp7, hm7⟩
  rw [show (((3 : B256) * 32).toNat) = 96 from rfl] at hm7
  have hwf7 : Mem.Wf s7.memory := by
    rw [hm7, ← hm6]
    exact hwf5.write _ _
  have hr7 : Mem.Reads s7.memory
      (Bytes.writeAt
        (Bytes.writeAt
          (Bytes.writeAt (Bytes.writeAt img 0 digest.toBytes)
            32 (Nat.toB256 v.toNat).toBytes)
          64 sigR.toBytes)
        96 sigS.toBytes) := by
    rw [hm7, ← hm6]
    exact Mem.Reads.write hwf5 hr5 96 _
  rcases of_run_append [pushB256 0] run with ⟨s8, h8, run⟩
  rcases Line.of_run_cons h8 with ⟨u8, q8, hnil⟩
  cases hnil
  have hp8 : (0 : B256) :: xs <<+ s8.stack :=
    prefix_of_push (of_run_pushB256 q8) hp7
  have hm8 : s7.memory = s8.memory :=
    Ninst.Hinv.inv (f := Devm.memory) q8
  rcases of_run_append (mstoreAt 4) run with ⟨s9, h9, run⟩
  rcases of_run_mstoreAt_val h9 hp8 with ⟨hp9, hm9⟩
  rw [show (((4 : B256) * 32).toNat) = 128 from rfl] at hm9
  have hwf9 : Mem.Wf s9.memory := by
    rw [hm9, ← hm8]
    exact hwf7.write _ _
  have hr9 : Mem.Reads s9.memory
      (permitRecoverMemoryImage img digest v sigR sigS) := by
    unfold permitRecoverMemoryImage
    rw [hm9, ← hm8]
    exact Mem.Reads.write hwf7 hr7 128 _
  rcases of_run_append (pushList [32, 128, 128, 0, 1]) run with
    ⟨s10, h10, run⟩
  simp only [pushList, List.map] at h10
  rcases Line.of_run_cons h10 with ⟨u1, q1, h10⟩
  have hp10a : (32 : B256) :: xs <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp9
  rcases Line.of_run_cons h10 with ⟨u2, q2, h10⟩
  have hp10b : (128 : B256) :: (32 : B256) :: xs <<+ u2.stack :=
    prefix_of_push (of_run_pushB256 q2) hp10a
  rcases Line.of_run_cons h10 with ⟨u3, q3, h10⟩
  have hp10c : (128 : B256) :: (128 : B256) :: (32 : B256) :: xs <<+
      u3.stack := prefix_of_push (of_run_pushB256 q3) hp10b
  rcases Line.of_run_cons h10 with ⟨u4, q4, h10⟩
  have hp10d : (0 : B256) :: (128 : B256) :: (128 : B256) ::
      (32 : B256) :: xs <<+ u4.stack :=
    prefix_of_push (of_run_pushB256 q4) hp10c
  rcases Line.of_run_cons h10 with ⟨u5, q5, hnil⟩
  cases hnil
  have hp10 : (1 : B256) :: (0 : B256) :: (128 : B256) ::
      (128 : B256) :: (32 : B256) :: xs <<+ s10.stack :=
    prefix_of_push (of_run_pushB256 q5) hp10d
  have hm10 : s9.memory = s10.memory := by
    calc
      s9.memory = u1.memory := Ninst.Hinv.inv (f := Devm.memory) q1
      _ = u2.memory := Ninst.Hinv.inv (f := Devm.memory) q2
      _ = u3.memory := Ninst.Hinv.inv (f := Devm.memory) q3
      _ = u4.memory := Ninst.Hinv.inv (f := Devm.memory) q4
      _ = s10.memory := Ninst.Hinv.inv (f := Devm.memory) q5
  rcases Line.of_run_cons run with ⟨s11, q11, hnil⟩
  cases hnil
  rcases of_run_gas q11 with ⟨g, hpush⟩
  refine ⟨g, prefix_of_push hpush hp10, ?_, ?_⟩
  · rw [← hpush.memory, ← hm10]
    exact hwf9
  · rw [← hpush.memory, ← hm10]
    exact hr9

/-- The local recovery preparation changes only stack, memory, and gas.  This
explicit frame lemma keeps the final `gas` instruction out of generic
`Line.Inv` search, since `gas` is inverted through its exact `PushBurn`
result. -/
theorem permitRecoverPrepare_frame
    {sevm : Sevm} {s t : Devm}
    (run : Line.Run sevm s permitRecoverPrepare t) :
    Devm.getStor s = Devm.getStor t ∧
      s.logs = t.logs ∧ s.output = t.output ∧ s.getCode = t.getCode := by
  unfold permitRecoverPrepare at run
  rcases of_run_append permitRecoverWrites run with ⟨q, hwrites, hgas⟩
  have hstor : Devm.getStor s = Devm.getStor q :=
    Line.of_inv Devm.getStor (by
      unfold permitRecoverWrites pushList
      line_inv) hwrites
  have hlogs : s.logs = q.logs :=
    Line.of_inv Devm.logs (by
      unfold permitRecoverWrites pushList
      line_inv) hwrites
  have houtput : s.output = q.output :=
    Line.of_inv Devm.output (by
      unfold permitRecoverWrites pushList
      line_inv) hwrites
  have hcode : s.getCode = q.getCode :=
    Line.of_inv Devm.getCode (by
      unfold permitRecoverWrites pushList
      line_inv) hwrites
  rcases Line.of_run_cons hgas with ⟨u, qgas, hnil⟩
  cases hnil
  rcases of_run_gas qgas with ⟨g, hpush⟩
  refine ⟨hstor.trans ?_, hlogs.trans hpush.logs,
    houtput.trans hpush.output, hcode.trans ?_⟩
  · funext a
    exact getStor_eq_of_state_eq hpush.state a
  · funext a
    exact getCode_eq_of_state_eq hpush.state a

lemma permitEcrecoverOutput_spectrum (digest : B256) (v : UInt8)
    (r s : B256) :
    permitEcrecoverOutput digest v r s = [] ∨
      ∃ adr : Adr, permitEcrecoverOutput digest v r s =
        adr.toB256.toBytes := by
  have h := permitEcrecoverResult_spectrum digest v r s
  rw [permitEcrecoverResult_eq] at h
  rcases h with h | ⟨adr, h⟩
  · left
    injection h
  · right
    refine ⟨adr, ?_⟩
    injection h

private lemma Bytes.writeAt_nil_of_le {bs : Bytes} {n : Nat}
    (h : n ≤ bs.length) : Bytes.writeAt bs n [] = bs := by
  unfold Bytes.writeAt
  simp only [List.append_nil, List.length_nil, Nat.add_zero]
  rw [List.takeD_eq_take _ h, List.take_append_drop]

/-- Reading permit's pre-zeroed output word after the `STATICCALL` copy gives
exactly the total ECRECOVER result word: zero for empty output and the
canonical address word for the 32-byte arm. -/
lemma permitRecover_copy_word (img : Bytes) (digest : B256) (v : UInt8)
    (r s : B256) (out : Bytes)
    (hspec : out = [] ∨ ∃ adr : Adr, out = adr.toB256.toBytes) :
    Bytes.toB256
      ((Bytes.writeAt (permitRecoverMemoryImage img digest v r s)
        128 (out.take 32)).sliceD 128 32 0) = Bytes.toB256 out := by
  rcases hspec with hout | ⟨adr, hout⟩
  · subst out
    rw [List.take_nil, Bytes.writeAt_nil_of_le (by
      unfold permitRecoverMemoryImage Bytes.writeAt
      simp only [List.length_append, List.takeD_length, List.length_drop,
        B256.length_toBytes]
      omega), permitRecover_output_window]
    simp only [B256.toB256_toBytes]
    rfl
  · subst out
    have hlen : adr.toB256.toBytes.length = 32 :=
      B256.length_toBytes adr.toB256
    rw [show adr.toB256.toBytes.take 32 = adr.toB256.toBytes by
      rw [← hlen, List.take_length],
      show 32 = adr.toB256.toBytes.length from hlen.symm,
      Bytes.sliceD_writeAt]

private lemma mload_logs_output {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s mload s') :
    s.logs = s'.logs ∧ s.output = s'.output := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨si, s1⟩, h1, run1⟩
  rcases Except.bind_eq_ok run1 with ⟨s2, h2, run2⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, hpop⟩
  have hburn := Devm.burn_of_chargeGas h2
  have hpush := Devm.push_of_push run2
  have hmemLogs : s2.logs = (s2.memRead si 32).2.logs := rfl
  have hmemOutput : s2.output = (s2.memRead si 32).2.output := rfl
  exact ⟨((hpop.logs.trans hburn.logs).trans hmemLogs).trans hpush.logs,
    ((hpop.output.trans hburn.output).trans hmemOutput).trans hpush.output⟩

/-- The local tail consumes the call-status flag and loads the precompile's
output word.  It only extends memory; storage, logs, and the enclosing output
are unchanged. -/
theorem of_permitRecoverTail
    {sevm : Sevm} {s t : Devm} {flag : B256} {xs : Stack} {img : Bytes}
    (hp : flag :: xs <<+ s.stack)
    (hwf : Mem.Wf s.memory) (hr : Mem.Reads s.memory img)
    (run : Line.Run sevm s [pop, pushB256 128, mload] t) :
    Bytes.toB256 (img.sliceD 128 32 0) :: xs <<+ t.stack ∧
      Mem.Wf t.memory ∧ Mem.Reads t.memory img ∧
      Devm.getStor s = Devm.getStor t ∧
      s.logs = t.logs ∧ s.output = t.output := by
  have hstor : Devm.getStor s = Devm.getStor t :=
    Line.of_inv Devm.getStor (by line_inv) run
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  rcases of_run_pop q1 with ⟨x, hpop⟩
  have hp1 : xs <<+ s1.stack := prefix_of_pop ⟨x, hpop⟩ hp
  rcases Line.of_run_cons run with ⟨s2, q2, run⟩
  have hpush := of_run_pushB256 q2
  have hp2 : (128 : B256) :: xs <<+ s2.stack :=
    prefix_of_push hpush hp1
  rcases Line.of_run_cons run with ⟨s3, q3, hnil⟩
  cases hnil
  have hlocal := mload_logs_output q3
  have hlogs : s.logs = t.logs :=
    (hpop.logs.trans hpush.logs).trans hlocal.1
  have houtput : s.output = t.output :=
    (hpop.output.trans hpush.output).trans hlocal.2
  rcases prefix_of_mload_val q3 hp2
      (hpush.memory ▸ hpop.memory ▸ hr) with ⟨hp3, hm3, hrd3⟩
  refine ⟨by
    rw [show (128 : B256).toNat = 128 from rfl] at hp3
    exact hp3, ?_, ?_, hstor, hlogs, houtput⟩
  · rw [hm3, ← hpush.memory, ← hpop.memory]
    exact hwf.extend 128 32
  · rw [hm3, ← hpush.memory, ← hpop.memory]
    exact Mem.Reads.extend hr 128 32

/-- Exact selected-line recovery crossing.  A completed line either loaded
zero (depth failure or an errored/empty ECRECOVER answer), or loaded Jaune's
canonical total ECRECOVER word while preserving storage, logs, and the outer
output.  The no-delegation premise is essential: an EIP-7702 designator at
address 1 disables the precompile branch. -/
theorem of_recoverPermitSigner
    {sevm : Sevm} {s t : Devm}
    {owner spender : Adr} {value deadline digest : B256}
    {v : UInt8} {sigR sigS : B256} {xs : Stack} {img : Bytes}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 1) = true)
    (hnodeleg : getDelegatedCodeAddress (s.getCode 1) = none)
    (hdec : DecodesPermit sevm owner spender value deadline v sigR sigS)
    (hp : digest :: xs <<+ s.stack)
    (hwf : Mem.Wf s.memory) (hr : Mem.Reads s.memory img)
    (run : Line.Run sevm s recoverPermitSigner t) :
    ∃ (signer : B256) (out : Bytes),
      signer :: xs <<+ t.stack ∧
      Mem.Wf t.memory ∧
      Mem.Reads t.memory
        (Bytes.writeAt (permitRecoverMemoryImage img digest v sigR sigS)
          128 (out.take 32)) ∧
      signer = Bytes.toB256 out ∧
      (signer = 0 ∨
        out = permitEcrecoverOutput digest v sigR sigS ∧
        Devm.getStor t = Devm.getStor s ∧
        t.logs = s.logs ∧ t.output = s.output) := by
  rw [recoverPermitSigner_eq_prepare] at run
  rcases of_run_append permitRecoverPrepare run with ⟨q, hprep, run⟩
  rcases of_permitRecoverPrepare hdec hp hwf hr hprep with
    ⟨g, hpq, hwfq, hrq⟩
  rcases permitRecoverPrepare_frame hprep with
    ⟨hstorPrep, hlogsPrep, houtputPrep, hcodePrep⟩
  have hnodelegQ : getDelegatedCodeAddress (q.getCode 1) = none := by
    rw [← congrFun hcodePrep 1]
    exact hnodeleg
  have hinput : (q.memory.read 0 128).1 =
      permitEcrecoverImage digest v sigR sigS := by
    rw [Mem.Reads.read hrq 0 128, permitRecover_input_window]
  rcases Line.of_run_cons run with ⟨u, qstat, htail⟩
  rcases of_run_statcall_val_with_depth_cause hpq qstat with
      hfail | hsuccess
  · rcases hfail with ⟨hpU, hworld, out, hret, hmem, hcause⟩
    have hout : out = [] := by
      rcases hcause with hout | hchild
      · exact hout
      · rcases hchild with
          ⟨parent, child, xl, dp, na, code, avail,
            hdepth, hstack, hstate, hmemory, hdel, hfill,
            hpm, herr, houtChild⟩
        rcases hdel with ⟨hnd, hna, hcode, hdp⟩ | ⟨d, hsome, _, hcode, hdp⟩
        · subst dp
          subst hna
          change ProcessMessage
            (callMsg sevm parent (min g.toNat (except64th avail)) 0
              sevm.currentTarget 1 1 true true
              (q.memory.read 0 128).1 code false)
            xl (.ok child) at hpm
          change code = q.getCode 1 at hcode
          rw [hinput, hcode] at hpm
          exact houtChild.trans
            (output_nil_of_processMessage_permitEcrecover_error
              hpre hpm herr)
        · change getDelegatedCodeAddress (q.getCode 1) = some d at hsome
          rw [hnodelegQ] at hsome
          cases hsome
    have hwfU : Mem.Wf u.memory := by
      rw [hmem]
      exact (Mem.Wf.extends _ hwfq).write _ _
    have hrU : Mem.Reads u.memory
        (Bytes.writeAt (permitRecoverMemoryImage img digest v sigR sigS)
          128 (out.take 32)) := by
      rw [hmem]
      exact Mem.Reads.write (Mem.Wf.extends _ hwfq)
        (Mem.Reads.extends _ hrq) 128 _
    rcases of_permitRecoverTail hpU hwfU hrU htail with
      ⟨hpT, hwfT, hrT, hstorTail, hlogsTail, houtputTail⟩
    have hword := permitRecover_copy_word img digest v sigR sigS out
      (Or.inl hout)
    rw [hword] at hpT
    refine ⟨Bytes.toB256 out, out, hpT, hwfT, hrT, rfl, Or.inl ?_⟩
    rw [hout]
    rfl
  · rcases hsuccess with
      ⟨parent, child, xl, dp, na, code, avail,
        hdepth, hstack, hstate, hmemory, hparentLogs, hparentOutput,
        hdel, hfill, hpm, hclean, hresume, hstateU, hret, hmem, hstackU⟩
    rcases hdel with ⟨hnd, hna, hcode, hdp⟩ | ⟨d, hsome, _, hcode, hdp⟩
    · subst dp
      subst hna
      change ProcessMessage
        (callMsg sevm parent (min g.toNat (except64th avail)) 0
          sevm.currentTarget 1 1 true true
          (q.memory.read 0 128).1 code false)
        xl (.ok child) at hpm
      change code = q.getCode 1 at hcode
      rw [hinput, hcode] at hpm
      rcases frame_of_processMessage_permitEcrecover_clean hpre hpm hclean with
        ⟨hchildStor, hchildLogs, hout⟩
      have hcleanNot : ¬ child.error.isSome = true := by
        rw [hclean]
        decide
      have hstorU : Devm.getStor u = Devm.getStor q := by
        funext a
        calc
          Devm.getStor u a = Devm.getStor child a :=
            getStor_eq_of_state_eq hstateU a
          _ = Devm.getStor parent a := hchildStor a
          _ = Devm.getStor q a := getStor_eq_of_state_eq hstate a
      have hlogsU : u.logs = q.logs := by
        rw [Resume.call_logs hresume, if_neg hcleanNot, hchildLogs,
          List.append_nil, hparentLogs]
      have houtputU : u.output = q.output := by
        rw [Resume.call_output hresume, hparentOutput]
      have hwfU : Mem.Wf u.memory := by
        rw [hmem, hmemory]
        exact (Mem.Wf.extends _ hwfq).write _ _
      have hrU : Mem.Reads u.memory
          (Bytes.writeAt (permitRecoverMemoryImage img digest v sigR sigS)
            128 (child.output.take 32)) := by
        rw [hmem, hmemory]
        exact Mem.Reads.write (Mem.Wf.extends _ hwfq)
          (Mem.Reads.extends _ hrq) 128 _
      have hpParent : xs <<+ parent.stack := by
        rw [hstack] at hpq
        exact cons_pref_cons_inv (cons_pref_cons_inv
          (cons_pref_cons_inv (cons_pref_cons_inv
            (cons_pref_cons_inv (cons_pref_cons_inv hpq)))))
      have hpU : (1 : B256) :: xs <<+ u.stack := by
        rw [hstackU]
        exact pref_cons hpParent
      rcases of_permitRecoverTail hpU hwfU hrU htail with
        ⟨hpT, hwfT, hrT, hstorTail, hlogsTail, houtputTail⟩
      have hword := permitRecover_copy_word img digest v sigR sigS child.output
        (by rw [hout]; exact permitEcrecoverOutput_spectrum digest v sigR sigS)
      rw [hword] at hpT
      refine ⟨Bytes.toB256 child.output, child.output, hpT, hwfT, hrT, rfl,
        Or.inr ⟨hout, ?_, ?_, ?_⟩⟩
      · calc
          Devm.getStor t = Devm.getStor u := hstorTail.symm
          _ = Devm.getStor q := hstorU
          _ = Devm.getStor s := hstorPrep.symm
      · calc
          t.logs = u.logs := hlogsTail.symm
          _ = q.logs := hlogsU
          _ = s.logs := hlogsPrep.symm
      · calc
          t.output = u.output := houtputTail.symm
          _ = q.output := houtputU
          _ = s.output := houtputPrep.symm
    · change getDelegatedCodeAddress (q.getCode 1) = some d at hsome
      rw [hnodelegQ] at hsome
      cases hsome

/-! ## Recomputed-domain walk -/

/-- Exact value-carrying inversion of `calculateDomainSeparator`.  This is the
forked-chain branch of permit: the five final memory words, and hence the bytes
supplied to KECCAK256, are identified without a hash axiom. -/
theorem of_calculateDomainSeparator {sevm : Sevm} {s t : Devm}
    {chainId : B256} {xs : Stack} {img : Bytes}
    (hp : chainId :: xs <<+ s.stack)
    (hwf : Mem.Wf s.memory) (hr : Mem.Reads s.memory img)
    (run : Line.Run sevm s calculateDomainSeparator t) :
    (permitDomainImage chainId sevm.currentTarget).keccak :: xs <<+
        t.stack ∧
      Mem.Wf t.memory ∧
      Mem.Reads t.memory
        (permitDomainMemoryImage img chainId sevm.currentTarget) ∧
      Devm.getCode t = Devm.getCode s ∧
      t.logs = s.logs ∧ t.output = s.output := by
  have hcode : Devm.getCode s = Devm.getCode t :=
    Line.of_inv Devm.getCode (by
      unfold calculateDomainSeparator pushList
      line_inv) run
  unfold calculateDomainSeparator at run
  rcases of_run_append (mstoreAt 3) run with ⟨s1, h1, run⟩
  rcases of_run_mstoreAt_val h1 hp with ⟨hp1, hm1⟩
  rw [show (((3 : B256) * 32).toNat) = 96 from rfl] at hm1
  have hwf1 : Mem.Wf s1.memory := by
    rw [hm1]
    exact hwf.write _ _
  have hr1 : Mem.Reads s1.memory
      (Bytes.writeAt img 96 chainId.toBytes) := by
    rw [hm1]
    simpa only using Mem.Reads.write hwf hr 96 chainId.toBytes
  rcases of_run_append [pushB256 DOMAIN_TYPEHASH] run with
    ⟨s2, h2, run⟩
  rcases Line.of_run_cons h2 with ⟨u2, q2, hnil⟩
  cases hnil
  have hp2 : DOMAIN_TYPEHASH :: xs <<+ s2.stack :=
    prefix_of_push (of_run_pushB256 q2) hp1
  have hm2 : s1.memory = s2.memory :=
    Ninst.Hinv.inv (f := Devm.memory) q2
  rcases of_run_append (mstoreAt 0) run with ⟨s3, h3, run⟩
  rcases of_run_mstoreAt_val h3 hp2 with ⟨hp3, hm3⟩
  rw [show (((0 : B256) * 32).toNat) = 0 from rfl] at hm3
  have hwf3 : Mem.Wf s3.memory := by
    rw [hm3, ← hm2]
    exact hwf1.write _ _
  have hr3 : Mem.Reads s3.memory
      (Bytes.writeAt (Bytes.writeAt img 96 chainId.toBytes)
        0 DOMAIN_TYPEHASH.toBytes) := by
    rw [hm3, ← hm2]
    exact Mem.Reads.write hwf1 hr1 0 _
  rcases of_run_append [pushB256 NAME_HASH] run with ⟨s4, h4, run⟩
  rcases Line.of_run_cons h4 with ⟨u4, q4, hnil⟩
  cases hnil
  have hp4 : NAME_HASH :: xs <<+ s4.stack :=
    prefix_of_push (of_run_pushB256 q4) hp3
  have hm4 : s3.memory = s4.memory :=
    Ninst.Hinv.inv (f := Devm.memory) q4
  rcases of_run_append (mstoreAt 1) run with ⟨s5, h5, run⟩
  rcases of_run_mstoreAt_val h5 hp4 with ⟨hp5, hm5⟩
  rw [show (((1 : B256) * 32).toNat) = 32 from rfl] at hm5
  have hwf5 : Mem.Wf s5.memory := by
    rw [hm5, ← hm4]
    exact hwf3.write _ _
  have hr5 : Mem.Reads s5.memory
      (Bytes.writeAt
        (Bytes.writeAt (Bytes.writeAt img 96 chainId.toBytes)
          0 DOMAIN_TYPEHASH.toBytes)
        32 NAME_HASH.toBytes) := by
    rw [hm5, ← hm4]
    exact Mem.Reads.write hwf3 hr3 32 _
  rcases of_run_append [pushB256 VERSION_HASH] run with
    ⟨s6, h6, run⟩
  rcases Line.of_run_cons h6 with ⟨u6, q6, hnil⟩
  cases hnil
  have hp6 : VERSION_HASH :: xs <<+ s6.stack :=
    prefix_of_push (of_run_pushB256 q6) hp5
  have hm6 : s5.memory = s6.memory :=
    Ninst.Hinv.inv (f := Devm.memory) q6
  rcases of_run_append (mstoreAt 2) run with ⟨s7, h7, run⟩
  rcases of_run_mstoreAt_val h7 hp6 with ⟨hp7, hm7⟩
  rw [show (((2 : B256) * 32).toNat) = 64 from rfl] at hm7
  have hwf7 : Mem.Wf s7.memory := by
    rw [hm7, ← hm6]
    exact hwf5.write _ _
  have hr7 : Mem.Reads s7.memory
      (Bytes.writeAt
        (Bytes.writeAt
          (Bytes.writeAt (Bytes.writeAt img 96 chainId.toBytes)
            0 DOMAIN_TYPEHASH.toBytes)
          32 NAME_HASH.toBytes)
        64 VERSION_HASH.toBytes) := by
    rw [hm7, ← hm6]
    exact Mem.Reads.write hwf5 hr5 64 _
  rcases of_run_append [address] run with ⟨s8, h8, run⟩
  rcases Line.of_run_cons h8 with ⟨u8, q8, hnil⟩
  cases hnil
  have hp8 : sevm.currentTarget.toB256 :: xs <<+ s8.stack :=
    prefix_of_push (of_run_address q8) hp7
  have hm8 : s7.memory = s8.memory :=
    Ninst.Hinv.inv (f := Devm.memory) q8
  rcases of_run_append (mstoreAt 4) run with ⟨s9, h9, run⟩
  rcases of_run_mstoreAt_val h9 hp8 with ⟨hp9, hm9⟩
  rw [show (((4 : B256) * 32).toNat) = 128 from rfl] at hm9
  have hwf9 : Mem.Wf s9.memory := by
    rw [hm9, ← hm8]
    exact hwf7.write _ _
  have hr9 : Mem.Reads s9.memory
      (permitDomainMemoryImage img chainId sevm.currentTarget) := by
    unfold permitDomainMemoryImage
    rw [hm9, ← hm8]
    exact Mem.Reads.write hwf7 hr7 128 _
  rcases Line.of_run_cons run with ⟨s10, q10, run⟩
  have hp10 : (160 : B256) :: xs <<+ s10.stack :=
    prefix_of_push (of_run_pushB256 q10) hp9
  have hm10 : s9.memory = s10.memory :=
    Ninst.Hinv.inv (f := Devm.memory) q10
  rcases Line.of_run_cons run with ⟨s11, q11, run⟩
  have hp11 : (0 : B256) :: (160 : B256) :: xs <<+ s11.stack :=
    prefix_of_push (of_run_pushB256 q11) hp10
  have hm11 : s10.memory = s11.memory :=
    Ninst.Hinv.inv (f := Devm.memory) q11
  rcases Line.of_run_cons run with ⟨s12, q12, hnil⟩
  cases hnil
  have hk := prefix_of_kec_val q12 hp11
  have hread : (s11.memory.read 0 160).1 =
      permitDomainImage chainId sevm.currentTarget := by
    rw [Mem.Reads.read (hm11 ▸ hm10 ▸ hr9) 0 160,
      permitDomain_window]
  have hk' : (s11.memory.read 0 160).1.keccak :: xs <<+ t.stack ∧
      t.memory = s11.memory.extend 0 160 := by
    rw [show (0 : B256).toNat = 0 from rfl,
      show (160 : B256).toNat = 160 from rfl] at hk
    exact hk
  rw [hread] at hk'
  have hlogs : s.logs = t.logs := by
    calc
      s.logs = s1.logs := Line.of_inv Devm.logs (by line_inv) h1
      _ = s2.logs := Line.of_inv Devm.logs (by line_inv) h2
      _ = s3.logs := Line.of_inv Devm.logs (by line_inv) h3
      _ = s4.logs := Line.of_inv Devm.logs (by line_inv) h4
      _ = s5.logs := Line.of_inv Devm.logs (by line_inv) h5
      _ = s6.logs := Line.of_inv Devm.logs (by line_inv) h6
      _ = s7.logs := Line.of_inv Devm.logs (by line_inv) h7
      _ = s8.logs := (of_run_address q8).logs
      _ = s9.logs := Line.of_inv Devm.logs (by line_inv) h9
      _ = s10.logs := Ninst.Hinv.inv (f := Devm.logs) q10
      _ = s11.logs := Ninst.Hinv.inv (f := Devm.logs) q11
      _ = t.logs := Ninst.Hinv.inv (f := Devm.logs) q12
  have houtput : s.output = t.output := by
    calc
      s.output = s1.output := Line.of_inv Devm.output (by line_inv) h1
      _ = s2.output := Line.of_inv Devm.output (by line_inv) h2
      _ = s3.output := Line.of_inv Devm.output (by line_inv) h3
      _ = s4.output := Line.of_inv Devm.output (by line_inv) h4
      _ = s5.output := Line.of_inv Devm.output (by line_inv) h5
      _ = s6.output := Line.of_inv Devm.output (by line_inv) h6
      _ = s7.output := Line.of_inv Devm.output (by line_inv) h7
      _ = s8.output := (of_run_address q8).output
      _ = s9.output := Line.of_inv Devm.output (by line_inv) h9
      _ = s10.output := Ninst.Hinv.inv (f := Devm.output) q10
      _ = s11.output := Ninst.Hinv.inv (f := Devm.output) q11
      _ = t.output := Ninst.Hinv.inv (f := Devm.output) q12
  refine ⟨hk'.1, ?_, ?_, hcode.symm, hlogs.symm, houtput.symm⟩
  · rw [hk'.2, ← hm11, ← hm10]
    exact hwf9.extend _ _
  · rw [hk'.2, ← hm11, ← hm10]
    exact Mem.Reads.extend hr9 _ _

/-! ## Nonce read and tentative increment -/

private lemma prefix_of_chainid {e : Sevm} {s s' : Devm} {xs : Stack}
    (hp : xs <<+ s.stack) (h : Ninst.Run e s chainid s') :
    e.benvStat.chainId.toB256 :: xs <<+ s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact prefix_of_push (Devm.pushBurn_of_pushItem run) hp

private lemma memory_eq_of_chainid {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s chainid s') : s.memory = s'.memory := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).memory

private lemma logs_eq_of_chainid {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s chainid s') : s.logs = s'.logs := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).logs

private lemma output_eq_of_chainid {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s chainid s') : s.output = s'.output := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).output

private lemma permit_sload_logs {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s sload s') : s.logs = s'.logs := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨key, s1⟩, h1, run1⟩
  refine (Devm.pop_of_pop h1).logs.trans ?_
  suffices H : ∀ (d : Devm) (c : Nat), s1.logs = d.logs →
      (chargeGas c d >>=
        fun y => Devm.push (Devm.getStorVal y e.currentTarget key) y) =
          .ok s' → s1.logs = s'.logs by
    split at run1
    · exact H s1 gasWarmAccess rfl run1
    · exact H (addAccessedStorageKey s1 e.currentTarget key)
        gasColdSload rfl run1
  intro d c hlogs run'
  rcases Except.bind_eq_ok run' with ⟨s2, h2, run2⟩
  exact (hlogs.trans (Devm.burn_of_chargeGas h2).logs).trans
    (Devm.push_of_push run2).logs

private lemma permit_sload_output {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s sload s') : s.output = s'.output := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨key, s1⟩, h1, run1⟩
  refine (Devm.pop_of_pop h1).output.trans ?_
  suffices H : ∀ (d : Devm) (c : Nat), s1.output = d.output →
      (chargeGas c d >>=
        fun y => Devm.push (Devm.getStorVal y e.currentTarget key) y) =
          .ok s' → s1.output = s'.output by
    split at run1
    · exact H s1 gasWarmAccess rfl run1
    · exact H (addAccessedStorageKey s1 e.currentTarget key)
        gasColdSload rfl run1
  intro d c houtput run'
  rcases Except.bind_eq_ok run' with ⟨s2, h2, run2⟩
  exact (houtput.trans (Devm.burn_of_chargeGas h2).output).trans
    (Devm.push_of_push run2).output

private lemma permit_add_logs {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s add s') : s.logs = s'.logs := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.logs

private lemma permit_add_output {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s add s') : s.output = s'.output := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.output

private lemma permit_normalizeAddress_owner (owner : Adr) :
    ((~~~ addressMask) &&& owner.toB256) = owner.toB256 := by
  have u64_and_max (x : UInt64) : UInt64.max &&& x = x := by
    apply UInt64.toBitVec_inj.mp
    rw [UInt64.toBitVec_and]
    have hmax : UInt64.max.toBitVec = BitVec.allOnes 64 := by rfl
    rw [hmax]
    exact BitVec.allOnes_and
  have b128_and_max (x : B128) : B128.max &&& x = x := by
    apply Prod.ext <;> apply u64_and_max
  have hm : (~~~ addressMask) =
      (⟨⟨0, 0x00000000ffffffff⟩, B128.max⟩ : B256) := by
    decide +kernel
  rw [hm]
  rcases owner with ⟨ahi, alo⟩
  simp only [Adr.toB256, B256.and_eq_and_prod_and,
    B128.and_eq_and_prod_and, UInt64.zero_and]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · change (-1 : UInt32).toUInt64 &&& ahi.toUInt64 = ahi.toUInt64
      rw [← UInt32.toUInt64_and]
      simp
  · exact b128_and_max alo

private lemma permit_prefix_of_addressArg {e : Sevm} {k : B256}
    {xs : Stack} {s s' : Devm} (hp : xs <<+ s.stack)
    (run : Line.Run e s (addressArg k) s') :
    ((~~~ addressMask) &&& Sevm.argWord e k) :: xs <<+ s'.stack := by
  unfold addressArg normalizeAddress at run
  rcases of_run_append (arg k) run with ⟨s1, harg, run1⟩
  have hp1 : Sevm.argWord e k :: xs <<+ s1.stack :=
    prefix_of_arg hp harg
  rcases of_run_append pushAddressMask run1 with ⟨s2, hmask, run2⟩
  have hp2 : addressMask :: Sevm.argWord e k :: xs <<+ s2.stack :=
    of_push_addressMask hp1 hmask
  rcases Line.of_run_cons run2 with ⟨s3, hnot, run3⟩
  have hp3 : (~~~ addressMask) :: Sevm.argWord e k :: xs <<+
      s3.stack := prefix_of_not hnot hp2
  rcases Line.of_run_cons run3 with ⟨s4, hand, hnil⟩
  cases hnil
  exact prefix_of_and hand hp3

/-- The exact nonce prefix reads the canonical owner's nonce, stores that
original word at memory word 4 for the signed struct, and tentatively writes
`nonce + 1` to the tagged nonce slot.  Later revert settlement may roll this
world write back; this theorem deliberately names the pre-call tentative
state. -/
theorem of_permitNoncePrepare {sevm : Sevm} {s t : Devm}
    {owner spender : Adr} {value deadline : B256}
    {v : UInt8} {r sigs : B256} {xs : Stack} {img : Bytes}
    (hdec : DecodesPermit sevm owner spender value deadline v r sigs)
    (hp : xs <<+ s.stack) (hwf : Mem.Wf s.memory)
    (hr : Mem.Reads s.memory img)
    (run : Line.Run sevm s permitNoncePrepare t) :
    let nonce := Devm.getStorVal s sevm.currentTarget (nonceKey owner)
    sevm.benvStat.chainId.toB256 :: xs <<+ t.stack ∧
      Devm.getStor t sevm.currentTarget =
        (Devm.getStor s sevm.currentTarget).set
          (nonceKey owner) (nonce + 1) ∧
      Devm.getCode t = Devm.getCode s ∧
      t.logs = s.logs ∧ t.output = s.output ∧
      Mem.Wf t.memory ∧
      Mem.Reads t.memory (Bytes.writeAt img 128 nonce.toBytes) := by
  dsimp only
  have hcode : Devm.getCode s = Devm.getCode t :=
    Line.of_inv Devm.getCode (by
      unfold permitNoncePrepare tagNonceKey
      line_inv) run
  unfold permitNoncePrepare at run
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  have hp1 : sevm.benvStat.chainId.toB256 :: xs <<+ s1.stack :=
    prefix_of_chainid hp q1
  rcases of_run_append (addressArg 0) run with ⟨s2, h2, run⟩
  have hp2 : owner.toB256 :: sevm.benvStat.chainId.toB256 :: xs <<+
      s2.stack := by
    have h := permit_prefix_of_addressArg hp1 h2
    rw [argWord_zero_of_decodesPermit hdec,
      permit_normalizeAddress_owner] at h
    exact h
  rcases Line.of_run_cons run with ⟨s3, q3, run⟩
  have hp3 : owner.toB256 :: owner.toB256 ::
      sevm.benvStat.chainId.toB256 :: xs <<+ s3.stack :=
    prefix_of_dup_val q3 (by show_nth) hp2
  rcases of_run_append tagNonceKey run with ⟨s4, h4, run⟩
  have hp4 : nonceKey owner :: owner.toB256 ::
      sevm.benvStat.chainId.toB256 :: xs <<+ s4.stack := by
    unfold tagNonceKey at h4
    rcases Line.of_run_cons h4 with ⟨u41, q41, h4'⟩
    have hp41 : nonceTagWord :: owner.toB256 :: owner.toB256 ::
        sevm.benvStat.chainId.toB256 :: xs <<+ u41.stack :=
      prefix_of_push (of_run_pushB256 q41) hp3
    rcases Line.of_run_cons h4' with ⟨u42, q42, hnil⟩
    cases hnil
    have h : (nonceTagWord ||| owner.toB256) :: owner.toB256 ::
        sevm.benvStat.chainId.toB256 :: xs <<+ s4.stack :=
      prefix_of_or q42 hp41
    simpa only [nonceTagWord, ← nonceKey_formula] using h
  rcases Line.of_run_cons run with ⟨s5, q5, run⟩
  have hp5 : nonceKey owner :: nonceKey owner :: owner.toB256 ::
      sevm.benvStat.chainId.toB256 :: xs <<+ s5.stack :=
    prefix_of_dup_val q5 (by show_nth) hp4
  rcases Line.of_run_cons run with ⟨s6, q6, run⟩
  rcases prefix_of_sload q6 hp5 with ⟨nonce, hp6, hnonce⟩
  have hstor5 : Devm.getStor s = Devm.getStor s5 := by
    calc
      Devm.getStor s = Devm.getStor s1 :=
        Ninst.Hinv.inv (f := Devm.getStor) q1
      _ = Devm.getStor s2 := Line.of_inv Devm.getStor (by line_inv) h2
      _ = Devm.getStor s3 := Ninst.Hinv.inv (f := Devm.getStor) q3
      _ = Devm.getStor s4 := Line.of_inv Devm.getStor (by
        unfold tagNonceKey
        line_inv) h4
      _ = Devm.getStor s5 := Ninst.Hinv.inv (f := Devm.getStor) q5
  have hnonce' :
      nonce = Devm.getStorVal s sevm.currentTarget (nonceKey owner) := by
    rw [hnonce]
    change (Devm.getStor s5 sevm.currentTarget).get (nonceKey owner) =
      (Devm.getStor s sevm.currentTarget).get (nonceKey owner)
    rw [← hstor5]
  rw [hnonce'] at hp6
  rcases Line.of_run_cons run with ⟨s7, q7, run⟩
  have hp7 : Devm.getStorVal s sevm.currentTarget (nonceKey owner) ::
      Devm.getStorVal s sevm.currentTarget (nonceKey owner) ::
      nonceKey owner :: owner.toB256 ::
      sevm.benvStat.chainId.toB256 :: xs <<+ s7.stack :=
    prefix_of_dup_val q7 (by show_nth) hp6
  rcases of_run_append (mstoreAt 4) run with ⟨s8, h8, run⟩
  rcases of_run_mstoreAt_val h8 hp7 with ⟨hp8, hm8⟩
  rw [show (((4 : B256) * 32).toNat) = 128 from rfl] at hm8
  rcases Line.of_run_cons run with ⟨s9, q9, run⟩
  have hp9 : (1 : B256) ::
      Devm.getStorVal s sevm.currentTarget (nonceKey owner) ::
      nonceKey owner :: owner.toB256 ::
      sevm.benvStat.chainId.toB256 :: xs <<+ s9.stack :=
    prefix_of_push (of_run_pushB256 q9) hp8
  rcases Line.of_run_cons run with ⟨s10, q10, run⟩
  have hp10 :
      (Devm.getStorVal s sevm.currentTarget (nonceKey owner) + 1) ::
      nonceKey owner :: owner.toB256 ::
      sevm.benvStat.chainId.toB256 :: xs <<+ s10.stack := by
    have h := prefix_of_add q10 hp9
    simpa only [B256.add_comm] using h
  rcases Line.of_run_cons run with ⟨s11, q11, run⟩
  have hp11 : nonceKey owner ::
      (Devm.getStorVal s sevm.currentTarget (nonceKey owner) + 1) ::
      owner.toB256 :: sevm.benvStat.chainId.toB256 :: xs <<+
      s11.stack := by
    have hswap : Stack.Swap (0 : Fin 16).val
        ((Devm.getStorVal s sevm.currentTarget (nonceKey owner) + 1) ::
          nonceKey owner :: owner.toB256 ::
          sevm.benvStat.chainId.toB256 :: xs)
        (nonceKey owner ::
          (Devm.getStorVal s sevm.currentTarget (nonceKey owner) + 1) ::
          owner.toB256 :: sevm.benvStat.chainId.toB256 :: xs) :=
      Stack.swapCore_zero
    exact Stack.prefix_of_swap hswap (of_run_swap q11) hp10
  rcases Line.of_run_cons run with ⟨s12, q12, run⟩
  have hset : Devm.getStor s12 sevm.currentTarget =
      (Devm.getStor s11 sevm.currentTarget).set (nonceKey owner)
        (Devm.getStorVal s sevm.currentTarget (nonceKey owner) + 1) :=
    sstore_getStor_set q12 hp11
  have hp12 : owner.toB256 :: sevm.benvStat.chainId.toB256 :: xs <<+
      s12.stack := prefix_of_sstore q12 hp11
  rcases Line.of_run_cons run with ⟨s13, q13, hnil⟩
  cases hnil
  rcases of_run_pop q13 with ⟨w13, hpop13⟩
  have hp13 : sevm.benvStat.chainId.toB256 :: xs <<+ t.stack :=
    (popBurn_pref hpop13 hp12).2
  have hstor11 : Devm.getStor s = Devm.getStor s11 := by
    calc
      Devm.getStor s = Devm.getStor s5 := hstor5
      _ = Devm.getStor s6 := Ninst.Hinv.inv (f := Devm.getStor) q6
      _ = Devm.getStor s7 := Ninst.Hinv.inv (f := Devm.getStor) q7
      _ = Devm.getStor s8 :=
        Line.of_inv Devm.getStor (by line_inv) h8
      _ = Devm.getStor s9 := Ninst.Hinv.inv (f := Devm.getStor) q9
      _ = Devm.getStor s10 := Ninst.Hinv.inv (f := Devm.getStor) q10
      _ = Devm.getStor s11 := Ninst.Hinv.inv (f := Devm.getStor) q11
  have hstor12 : Devm.getStor s12 = Devm.getStor t :=
    Ninst.Hinv.inv (f := Devm.getStor) q13
  have hm_to7 : s.memory = s7.memory := by
    calc
      s.memory = s1.memory := memory_eq_of_chainid q1
      _ = s2.memory := Line.of_inv Devm.memory (by line_inv) h2
      _ = s3.memory := Ninst.Hinv.inv (f := Devm.memory) q3
      _ = s4.memory := Line.of_inv Devm.memory (by
        unfold tagNonceKey
        line_inv) h4
      _ = s5.memory := Ninst.Hinv.inv (f := Devm.memory) q5
      _ = s6.memory := Ninst.Hinv.inv (f := Devm.memory) q6
      _ = s7.memory := Ninst.Hinv.inv (f := Devm.memory) q7
  have hm8_to_t : s8.memory = t.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons q9
        (Line.Run.cons q10
          (Line.Run.cons q11
            (Line.Run.cons q12 (Line.Run.cons q13 Line.Run.nil)))))
  have hlogs : s.logs = t.logs := by
    calc
      s.logs = s1.logs := logs_eq_of_chainid q1
      _ = s2.logs := Line.of_inv Devm.logs (by line_inv) h2
      _ = s3.logs := Ninst.Hinv.inv (f := Devm.logs) q3
      _ = s4.logs := Line.of_inv Devm.logs (by
        unfold tagNonceKey
        line_inv) h4
      _ = s5.logs := Ninst.Hinv.inv (f := Devm.logs) q5
      _ = s6.logs := permit_sload_logs q6
      _ = s7.logs := Ninst.Hinv.inv (f := Devm.logs) q7
      _ = s8.logs := Line.of_inv Devm.logs (by line_inv) h8
      _ = s9.logs := Ninst.Hinv.inv (f := Devm.logs) q9
      _ = s10.logs := permit_add_logs q10
      _ = s11.logs := Ninst.Hinv.inv (f := Devm.logs) q11
      _ = s12.logs := Ninst.Hinv.inv (f := Devm.logs) q12
      _ = t.logs := hpop13.logs
  have houtput : s.output = t.output := by
    calc
      s.output = s1.output := output_eq_of_chainid q1
      _ = s2.output := Line.of_inv Devm.output (by line_inv) h2
      _ = s3.output := Ninst.Hinv.inv (f := Devm.output) q3
      _ = s4.output := Line.of_inv Devm.output (by
        unfold tagNonceKey
        line_inv) h4
      _ = s5.output := Ninst.Hinv.inv (f := Devm.output) q5
      _ = s6.output := permit_sload_output q6
      _ = s7.output := Ninst.Hinv.inv (f := Devm.output) q7
      _ = s8.output := Line.of_inv Devm.output (by line_inv) h8
      _ = s9.output := Ninst.Hinv.inv (f := Devm.output) q9
      _ = s10.output := permit_add_output q10
      _ = s11.output := Ninst.Hinv.inv (f := Devm.output) q11
      _ = s12.output := Ninst.Hinv.inv (f := Devm.output) q12
      _ = t.output := hpop13.output
  refine ⟨hp13, ?_, hcode.symm, hlogs.symm, houtput.symm, ?_, ?_⟩
  · rw [← congrFun hstor12 sevm.currentTarget, hset,
      ← congrFun hstor11 sevm.currentTarget]
  · rw [← hm8_to_t, hm8, ← hm_to7]
    exact hwf.write _ _
  · rw [← hm8_to_t, hm8, ← hm_to7]
    exact Mem.Reads.write hwf hr 128 _

/-! ## Struct-hash walk -/

/-- Exact value-carrying inversion of the struct-hash suffix embedded in
`permit`.  The nonce is the word already tentatively written to memory word 4;
canonical calldata supplies owner, spender, value, and deadline. -/
theorem of_permitStructPrepare {sevm : Sevm} {s t : Devm}
    {owner spender : Adr} {value nonce deadline : B256}
    {v : UInt8} {r sigs : B256} {xs : Stack} {img : Bytes}
    (hdec : DecodesPermit sevm owner spender value deadline v r sigs)
    (hp : xs <<+ s.stack) (hwf : Mem.Wf s.memory)
    (hr : Mem.Reads s.memory (Bytes.writeAt img 128 nonce.toBytes))
    (run : Line.Run sevm s permitStructPrepare t) :
    permitStructHash owner spender value nonce deadline :: xs <<+ t.stack ∧
      Mem.Wf t.memory ∧
      Mem.Reads t.memory
        (permitStructMemoryImage img owner spender value nonce deadline) ∧
      Devm.getCode t = Devm.getCode s ∧
      t.logs = s.logs ∧ t.output = s.output := by
  have hcode : Devm.getCode s = Devm.getCode t :=
    Line.of_inv Devm.getCode (by
      unfold permitStructPrepare argCopy cdc pushList
      line_inv) run
  have hlogs : s.logs = t.logs :=
    Line.of_inv Devm.logs (by
      unfold permitStructPrepare argCopy cdc pushList
      line_inv) run
  have houtput : s.output = t.output :=
    Line.of_inv Devm.output (by
      unfold permitStructPrepare argCopy cdc pushList
      line_inv) run
  unfold permitStructPrepare at run
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  have hp1 : PERMIT_TYPEHASH :: xs <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp
  have hm1 : s.memory = s1.memory :=
    Ninst.Hinv.inv (f := Devm.memory) q1
  rcases of_run_append (mstoreAt 0) run with ⟨s2, h2, run⟩
  rcases of_run_mstoreAt_val h2 hp1 with ⟨hp2, hm2⟩
  rw [show (((0 : B256) * 32).toNat) = 0 from rfl] at hm2
  have hwf2 : Mem.Wf s2.memory := by
    rw [hm2, ← hm1]
    exact hwf.write _ _
  have hr2 : Mem.Reads s2.memory
      (Bytes.writeAt (Bytes.writeAt img 128 nonce.toBytes)
        0 PERMIT_TYPEHASH.toBytes) := by
    rw [hm2, ← hm1]
    exact Mem.Reads.write hwf hr 0 _
  rcases of_run_append (argCopy 1 0 3) run with ⟨s3, h3, run⟩
  unfold argCopy cdc at h3
  rcases Line.of_run_cons h3 with ⟨u31, q31, h3⟩
  have hp31 : (96 : B256) :: xs <<+ u31.stack :=
    prefix_of_push (of_run_pushB256 q31) hp2
  rcases Line.of_run_cons h3 with ⟨u32, q32, h3⟩
  have hp32 : (4 : B256) :: (96 : B256) :: xs <<+ u32.stack :=
    prefix_of_push (of_run_pushB256 q32) hp31
  rcases Line.of_run_cons h3 with ⟨u33, q33, h3⟩
  have hp33 : (32 : B256) :: (4 : B256) :: (96 : B256) :: xs <<+
      u33.stack := prefix_of_push (of_run_pushB256 q33) hp32
  rcases Line.of_run_cons h3 with ⟨u34, q34, hnil⟩
  cases hnil
  rcases prefix_of_calldatacopy_val q34 hp33 with ⟨hp3, hm3⟩
  rw [show (32 : B256).toNat = 32 from rfl,
    show (4 : B256).toNat = 4 from rfl,
    show (96 : B256).toNat = 96 from rfl,
    permitData_args_zero_three hdec] at hm3
  have hm31 : s2.memory = u31.memory :=
    Ninst.Hinv.inv (f := Devm.memory) q31
  have hm32 : u31.memory = u32.memory :=
    Ninst.Hinv.inv (f := Devm.memory) q32
  have hm33 : u32.memory = u33.memory :=
    Ninst.Hinv.inv (f := Devm.memory) q33
  have hwf3 : Mem.Wf s3.memory := by
    rw [hm3, ← hm33, ← hm32, ← hm31]
    exact hwf2.write _ _
  have hr3 : Mem.Reads s3.memory
      (Bytes.writeAt
        (Bytes.writeAt (Bytes.writeAt img 128 nonce.toBytes)
          0 PERMIT_TYPEHASH.toBytes)
        32 (owner.toB256.toBytes ++ spender.toB256.toBytes ++
          value.toBytes)) := by
    rw [hm3, ← hm33, ← hm32, ← hm31]
    exact Mem.Reads.write hwf2 hr2 32 _
  rcases of_run_append (arg 3) run with ⟨s4, h4, run⟩
  have hp4 : deadline :: xs <<+ s4.stack := by
    rw [← argWord_three_of_decodesPermit hdec]
    exact prefix_of_arg hp3 h4
  have hm4 : s3.memory = s4.memory :=
    Line.of_inv Devm.memory (by line_inv) h4
  rcases of_run_append (mstoreAt 5) run with ⟨s5, h5, run⟩
  rcases of_run_mstoreAt_val h5 hp4 with ⟨hp5, hm5⟩
  rw [show (((5 : B256) * 32).toNat) = 160 from rfl] at hm5
  have hwf5 : Mem.Wf s5.memory := by
    rw [hm5, ← hm4]
    exact hwf3.write _ _
  have hr5 : Mem.Reads s5.memory
      (permitStructMemoryImage img owner spender value nonce deadline) := by
    unfold permitStructMemoryImage
    rw [hm5, ← hm4]
    exact Mem.Reads.write hwf3 hr3 160 _
  rcases Line.of_run_cons run with ⟨s6, q6, run⟩
  have hp6 : (192 : B256) :: xs <<+ s6.stack :=
    prefix_of_push (of_run_pushB256 q6) hp5
  have hm6 : s5.memory = s6.memory :=
    Ninst.Hinv.inv (f := Devm.memory) q6
  rcases Line.of_run_cons run with ⟨s7, q7, run⟩
  have hp7 : (0 : B256) :: (192 : B256) :: xs <<+ s7.stack :=
    prefix_of_push (of_run_pushB256 q7) hp6
  have hm7 : s6.memory = s7.memory :=
    Ninst.Hinv.inv (f := Devm.memory) q7
  rcases Line.of_run_cons run with ⟨s8, q8, hnil⟩
  cases hnil
  have hk := prefix_of_kec_val q8 hp7
  have hread : (s7.memory.read 0 192).1 =
      permitStructImage owner spender value nonce deadline := by
    rw [Mem.Reads.read (hm7 ▸ hm6 ▸ hr5) 0 192, permitStruct_window]
  have hk' : (s7.memory.read 0 192).1.keccak :: xs <<+ t.stack ∧
      t.memory = s7.memory.extend 0 192 := by
    rw [show (0 : B256).toNat = 0 from rfl,
      show (192 : B256).toNat = 192 from rfl] at hk
    exact hk
  rw [hread] at hk'
  refine ⟨?_, ?_, ?_, hcode.symm, hlogs.symm, houtput.symm⟩
  · simpa only [permitStructHash] using hk'.1
  · rw [hk'.2, ← hm7, ← hm6]
    exact hwf5.extend _ _
  · rw [hk'.2, ← hm7, ← hm6]
    exact Mem.Reads.extend hr5 _ _

/-! ## Domain dispatch -/

private lemma prefix_of_pushDeployWord {e : Sevm} {s s' : Devm}
    {w : B256} {xs : Stack} (hp : xs <<+ s.stack)
    (h : Ninst.Run e s (pushDeployWord w) s') :
    w :: xs <<+ s'.stack := by
  unfold pushDeployWord at h
  rw [← B256.toB256_toBytes w]
  exact prefix_of_push (of_run_push h) hp

/-- On the deployment chain, domain dispatch uses the cached separator and
enters the fixed permit-recovery auxiliary function without changing storage
or memory. -/
theorem of_permitDomainDispatch_cached (dp : DeployParams)
    {sevm : Sevm} {s r : Devm} {structHash : B256} {xs : Stack}
    {img : Bytes}
    (hchain : sevm.benvStat.chainId.toB256 = dp.deploymentChainId)
    (hp : structHash :: sevm.benvStat.chainId.toB256 :: xs <<+ s.stack)
    (hwf : Mem.Wf s.memory) (hr : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (permitDomainDispatch dp) r) :
    ∃ t,
      dp.cachedDomainSeparator :: structHash :: xs <<+ t.stack ∧
      Devm.getStor t = Devm.getStor s ∧
      Devm.getCode t = Devm.getCode s ∧
      t.logs = s.logs ∧ t.output = s.output ∧
      Mem.Wf t.memory ∧ Mem.Reads t.memory img ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm t permitRecover r := by
  unfold permitDomainDispatch at run
  rcases of_run_next run with ⟨s1, q1, run⟩
  have hp1 : sevm.benvStat.chainId.toB256 :: structHash ::
      sevm.benvStat.chainId.toB256 :: xs <<+ s1.stack :=
    prefix_of_dup_val q1 (by show_nth) hp
  rcases of_run_next run with ⟨s2, q2, run⟩
  have hp2 : dp.deploymentChainId :: sevm.benvStat.chainId.toB256 ::
      structHash :: sevm.benvStat.chainId.toB256 :: xs <<+ s2.stack :=
    prefix_of_pushDeployWord hp1 q2
  rcases of_run_next run with ⟨s3, q3, run⟩
  have hp3 : (1 : B256) :: structHash ::
      sevm.benvStat.chainId.toB256 :: xs <<+ s3.stack := by
    have h := prefix_of_eq q3 hp2
    simpa [hchain, B256.eqCheck] using h
  have hstor3 : Devm.getStor s = Devm.getStor s3 := by
    calc
      Devm.getStor s = Devm.getStor s1 :=
        Ninst.Hinv.inv (f := Devm.getStor) q1
      _ = Devm.getStor s2 := by
        unfold pushDeployWord at q2
        exact Ninst.Hinv.inv (f := Devm.getStor) q2
      _ = Devm.getStor s3 := Ninst.Hinv.inv (f := Devm.getStor) q3
  have hmem3 : s.memory = s3.memory := by
    calc
      s.memory = s1.memory := Ninst.Hinv.inv (f := Devm.memory) q1
      _ = s2.memory := by
        unfold pushDeployWord at q2
        exact Ninst.Hinv.inv (f := Devm.memory) q2
      _ = s3.memory := Ninst.Hinv.inv (f := Devm.memory) q3
  rcases of_run_branch run with
      ⟨sz, hzero, hfork⟩ |
      ⟨w, sp, sb, hnz, hpop, hburn, hcached⟩
  · exact absurd (popBurn_pref hzero hp3).1 B256.zero_ne_one
  · rcases popBurn_pref hpop hp3 with ⟨-, hp4⟩
    have hp5 : structHash :: sevm.benvStat.chainId.toB256 :: xs <<+
        sb.stack := by
      rw [← hburn.stack]
      exact hp4
    rcases of_run_next hcached with ⟨s4, q4, hcached⟩
    have hswap : Stack.Swap (0 : Fin 16).val
        (structHash :: sevm.benvStat.chainId.toB256 :: xs)
        (sevm.benvStat.chainId.toB256 :: structHash :: xs) :=
      Stack.swapCore_zero
    have hp6 : sevm.benvStat.chainId.toB256 :: structHash :: xs <<+
        s4.stack := Stack.prefix_of_swap hswap (of_run_swap q4) hp5
    rcases of_run_next hcached with ⟨s5, q5, hcached⟩
    have hpop5 := (of_run_pop q5).choose_spec
    have hp7 : structHash :: xs <<+ s5.stack :=
      prefix_of_pop (of_run_pop q5) hp6
    rcases of_run_next hcached with ⟨s6, q6, hcall⟩
    have hp8 : dp.cachedDomainSeparator :: structHash :: xs <<+ s6.stack :=
      prefix_of_pushDeployWord hp7 q6
    rcases of_run_call hcall with ⟨f, t, hget, hcallBurn, hrecover⟩
    have hf : f = permitRecover := by
      simpa [weth10Aux, permitRecoverSlot] using hget.symm
    subst f
    have hstor : Devm.getStor s = Devm.getStor t := by
      calc
        Devm.getStor s = Devm.getStor s3 := hstor3
        _ = Devm.getStor sp := PopBurn.Inv.inv hpop
        _ = Devm.getStor sb := Burn.Inv.inv hburn
        _ = Devm.getStor s4 := Ninst.Hinv.inv (f := Devm.getStor) q4
        _ = Devm.getStor s5 := Ninst.Hinv.inv (f := Devm.getStor) q5
        _ = Devm.getStor s6 := by
          unfold pushDeployWord at q6
          exact Ninst.Hinv.inv (f := Devm.getStor) q6
        _ = Devm.getStor t := Burn.Inv.inv hcallBurn
    have hmem : s.memory = t.memory := by
      calc
        s.memory = s3.memory := hmem3
        _ = sp.memory := hpop.memory
        _ = sb.memory := hburn.memory
        _ = s4.memory := Ninst.Hinv.inv (f := Devm.memory) q4
        _ = s5.memory := Ninst.Hinv.inv (f := Devm.memory) q5
        _ = s6.memory := by
          unfold pushDeployWord at q6
          exact Ninst.Hinv.inv (f := Devm.memory) q6
        _ = t.memory := hcallBurn.memory
    have hcode : Devm.getCode s = Devm.getCode t := by
      funext a
      calc
        Devm.getCode s a = Devm.getCode s1 a := congrFun
          (Ninst.Hinv.inv (f := Devm.getCode) q1) a
        _ = Devm.getCode s2 a := by
          unfold pushDeployWord at q2
          exact congrFun (Ninst.Hinv.inv (f := Devm.getCode) q2) a
        _ = Devm.getCode s3 a := congrFun
          (Ninst.Hinv.inv (f := Devm.getCode) q3) a
        _ = Devm.getCode sp a := getCode_eq_of_state_eq hpop.state a
        _ = Devm.getCode sb a := getCode_eq_of_state_eq hburn.state a
        _ = Devm.getCode s4 a := congrFun
          (Ninst.Hinv.inv (f := Devm.getCode) q4) a
        _ = Devm.getCode s5 a := congrFun
          (Ninst.Hinv.inv (f := Devm.getCode) q5) a
        _ = Devm.getCode s6 a := by
          unfold pushDeployWord at q6
          exact congrFun (Ninst.Hinv.inv (f := Devm.getCode) q6) a
        _ = Devm.getCode t a := getCode_eq_of_state_eq hcallBurn.state a
    have hlogs : s.logs = t.logs := by
      calc
        s.logs = s1.logs := Ninst.Hinv.inv (f := Devm.logs) q1
        _ = s2.logs := by
          unfold pushDeployWord at q2
          exact Ninst.Hinv.inv (f := Devm.logs) q2
        _ = s3.logs := Ninst.Hinv.inv (f := Devm.logs) q3
        _ = sp.logs := hpop.logs
        _ = sb.logs := hburn.logs
        _ = s4.logs := Ninst.Hinv.inv (f := Devm.logs) q4
        _ = s5.logs := hpop5.logs
        _ = s6.logs := by
          unfold pushDeployWord at q6
          exact Ninst.Hinv.inv (f := Devm.logs) q6
        _ = t.logs := hcallBurn.logs
    have houtput : s.output = t.output := by
      calc
        s.output = s1.output := Ninst.Hinv.inv (f := Devm.output) q1
        _ = s2.output := by
          unfold pushDeployWord at q2
          exact Ninst.Hinv.inv (f := Devm.output) q2
        _ = s3.output := Ninst.Hinv.inv (f := Devm.output) q3
        _ = sp.output := hpop.output
        _ = sb.output := hburn.output
        _ = s4.output := Ninst.Hinv.inv (f := Devm.output) q4
        _ = s5.output := hpop5.output
        _ = s6.output := by
          unfold pushDeployWord at q6
          exact Ninst.Hinv.inv (f := Devm.output) q6
        _ = t.output := hcallBurn.output
    refine ⟨t, ?_, hstor.symm, hcode.symm, hlogs.symm, houtput.symm,
      ?_, ?_, hrecover⟩
    · rw [← hcallBurn.stack]
      exact hp8
    · exact hmem ▸ hwf
    · exact hmem ▸ hr

/-- On a different chain, domain dispatch recomputes the canonical five-word
domain image, hashes it, and enters the fixed permit-recovery auxiliary
function. -/
theorem of_permitDomainDispatch_fork (dp : DeployParams)
    {sevm : Sevm} {s r : Devm} {structHash : B256} {xs : Stack}
    {img : Bytes}
    (hchain : sevm.benvStat.chainId.toB256 ≠ dp.deploymentChainId)
    (hp : structHash :: sevm.benvStat.chainId.toB256 :: xs <<+ s.stack)
    (hwf : Mem.Wf s.memory) (hr : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (permitDomainDispatch dp) r) :
    ∃ t,
      (permitDomainImage sevm.benvStat.chainId.toB256
          sevm.currentTarget).keccak :: structHash :: xs <<+ t.stack ∧
      Devm.getStor t = Devm.getStor s ∧
      Devm.getCode t = Devm.getCode s ∧
      t.logs = s.logs ∧ t.output = s.output ∧
      Mem.Wf t.memory ∧
      Mem.Reads t.memory
        (permitDomainMemoryImage img sevm.benvStat.chainId.toB256
          sevm.currentTarget) ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm t permitRecover r := by
  unfold permitDomainDispatch at run
  rcases of_run_next run with ⟨s1, q1, run⟩
  have hp1 : sevm.benvStat.chainId.toB256 :: structHash ::
      sevm.benvStat.chainId.toB256 :: xs <<+ s1.stack :=
    prefix_of_dup_val q1 (by show_nth) hp
  rcases of_run_next run with ⟨s2, q2, run⟩
  have hp2 : dp.deploymentChainId :: sevm.benvStat.chainId.toB256 ::
      structHash :: sevm.benvStat.chainId.toB256 :: xs <<+ s2.stack :=
    prefix_of_pushDeployWord hp1 q2
  rcases of_run_next run with ⟨s3, q3, run⟩
  have hrev : dp.deploymentChainId ≠ sevm.benvStat.chainId.toB256 :=
    fun h => hchain h.symm
  have hp3 : (0 : B256) :: structHash ::
      sevm.benvStat.chainId.toB256 :: xs <<+ s3.stack := by
    have h := prefix_of_eq q3 hp2
    simpa [B256.eqCheck, hrev] using h
  have hstor3 : Devm.getStor s = Devm.getStor s3 := by
    calc
      Devm.getStor s = Devm.getStor s1 :=
        Ninst.Hinv.inv (f := Devm.getStor) q1
      _ = Devm.getStor s2 := by
        unfold pushDeployWord at q2
        exact Ninst.Hinv.inv (f := Devm.getStor) q2
      _ = Devm.getStor s3 := Ninst.Hinv.inv (f := Devm.getStor) q3
  have hmem3 : s.memory = s3.memory := by
    calc
      s.memory = s1.memory := Ninst.Hinv.inv (f := Devm.memory) q1
      _ = s2.memory := by
        unfold pushDeployWord at q2
        exact Ninst.Hinv.inv (f := Devm.memory) q2
      _ = s3.memory := Ninst.Hinv.inv (f := Devm.memory) q3
  have hcode3 : Devm.getCode s = Devm.getCode s3 := by
    funext a
    calc
      Devm.getCode s a = Devm.getCode s1 a := congrFun
        (Ninst.Hinv.inv (f := Devm.getCode) q1) a
      _ = Devm.getCode s2 a := by
        unfold pushDeployWord at q2
        exact congrFun (Ninst.Hinv.inv (f := Devm.getCode) q2) a
      _ = Devm.getCode s3 a := congrFun
        (Ninst.Hinv.inv (f := Devm.getCode) q3) a
  have hlogs3 : s.logs = s3.logs := by
    calc
      s.logs = s1.logs := Ninst.Hinv.inv (f := Devm.logs) q1
      _ = s2.logs := by
        unfold pushDeployWord at q2
        exact Ninst.Hinv.inv (f := Devm.logs) q2
      _ = s3.logs := Ninst.Hinv.inv (f := Devm.logs) q3
  have houtput3 : s.output = s3.output := by
    calc
      s.output = s1.output := Ninst.Hinv.inv (f := Devm.output) q1
      _ = s2.output := by
        unfold pushDeployWord at q2
        exact Ninst.Hinv.inv (f := Devm.output) q2
      _ = s3.output := Ninst.Hinv.inv (f := Devm.output) q3
  rcases of_run_branch run with
      ⟨sp, hpop, hfork⟩ |
      ⟨w, sp, sb, hnz, hpop, hburn, hcached⟩
  · rcases popBurn_pref hpop hp3 with ⟨-, hp4⟩
    rcases of_run_next hfork with ⟨s4, q4, hfork⟩
    have hswap : Stack.Swap (0 : Fin 16).val
        (structHash :: sevm.benvStat.chainId.toB256 :: xs)
        (sevm.benvStat.chainId.toB256 :: structHash :: xs) :=
      Stack.swapCore_zero
    have hp5 : structHash :: sevm.benvStat.chainId.toB256 :: xs <<+
        sp.stack := hp4
    have hp6 : sevm.benvStat.chainId.toB256 :: structHash :: xs <<+
        s4.stack := Stack.prefix_of_swap hswap (of_run_swap q4) hp5
    have hstor4 : Devm.getStor s = Devm.getStor s4 := by
      calc
        Devm.getStor s = Devm.getStor s3 := hstor3
        _ = Devm.getStor sp := PopBurn.Inv.inv hpop
        _ = Devm.getStor s4 := Ninst.Hinv.inv (f := Devm.getStor) q4
    have hmem4 : s.memory = s4.memory := by
      calc
        s.memory = s3.memory := hmem3
        _ = sp.memory := hpop.memory
        _ = s4.memory := Ninst.Hinv.inv (f := Devm.memory) q4
    have hcode4 : Devm.getCode s = Devm.getCode s4 := by
      funext a
      calc
        Devm.getCode s a = Devm.getCode s3 a := congrFun hcode3 a
        _ = Devm.getCode sp a := getCode_eq_of_state_eq hpop.state a
        _ = Devm.getCode s4 a := congrFun
          (Ninst.Hinv.inv (f := Devm.getCode) q4) a
    have hlogs4 : s.logs = s4.logs := by
      calc
        s.logs = s3.logs := hlogs3
        _ = sp.logs := hpop.logs
        _ = s4.logs := Ninst.Hinv.inv (f := Devm.logs) q4
    have houtput4 : s.output = s4.output := by
      calc
        s.output = s3.output := houtput3
        _ = sp.output := hpop.output
        _ = s4.output := Ninst.Hinv.inv (f := Devm.output) q4
    rcases of_run_prepend calculateDomainSeparator _ hfork with
      ⟨s5, hdomain, hcall⟩
    rcases of_calculateDomainSeparator hp6 (hmem4 ▸ hwf)
        (hmem4 ▸ hr) hdomain with
      ⟨hp7, hwf5, hr5, hdomainCode, hdomainLogs, hdomainOutput⟩
    rcases of_run_call hcall with ⟨f, t, hget, hcallBurn, hrecover⟩
    have hf : f = permitRecover := by
      simpa [weth10Aux, permitRecoverSlot] using hget.symm
    subst f
    have hstor : Devm.getStor s = Devm.getStor t := by
      calc
        Devm.getStor s = Devm.getStor s4 := hstor4
        _ = Devm.getStor s5 :=
          Line.of_inv Devm.getStor (by
            unfold calculateDomainSeparator
            line_inv) hdomain
        _ = Devm.getStor t := Burn.Inv.inv hcallBurn
    have hcode : Devm.getCode s = Devm.getCode t := by
      funext a
      calc
        Devm.getCode s a = Devm.getCode s4 a := congrFun hcode4 a
        _ = Devm.getCode s5 a := congrFun hdomainCode.symm a
        _ = Devm.getCode t a := getCode_eq_of_state_eq hcallBurn.state a
    have hlogs : s.logs = t.logs := by
      calc
        s.logs = s4.logs := hlogs4
        _ = s5.logs := hdomainLogs.symm
        _ = t.logs := hcallBurn.logs
    have houtput : s.output = t.output := by
      calc
        s.output = s4.output := houtput4
        _ = s5.output := hdomainOutput.symm
        _ = t.output := hcallBurn.output
    refine ⟨t, ?_, hstor.symm, hcode.symm, hlogs.symm, houtput.symm,
      ?_, ?_, hrecover⟩
    · rw [← hcallBurn.stack]
      exact hp7
    · exact hcallBurn.memory ▸ hwf5
    · exact hcallBurn.memory ▸ hr5
  · have hw0 : w = 0 := (popBurn_pref hpop hp3).1
    exact (hnz hw0).elim

/-- Memory image at the recovery call: cached-domain execution leaves the
struct image in place; fork execution replaces its first five words with the
fresh domain image. -/
def permitDomainDispatchMemoryImage (dp : DeployParams) (chainId : B256)
    (verifyingContract : Adr) (img : Bytes) : Bytes :=
  if chainId = dp.deploymentChainId then img
  else permitDomainMemoryImage img chainId verifyingContract

/-- Exact common postcondition of cached and forked domain dispatch. -/
theorem of_permitDomainDispatch (dp : DeployParams)
    {sevm : Sevm} {s r : Devm} {structHash : B256} {xs : Stack}
    {img : Bytes}
    (hp : structHash :: sevm.benvStat.chainId.toB256 :: xs <<+ s.stack)
    (hwf : Mem.Wf s.memory) (hr : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (permitDomainDispatch dp) r) :
    ∃ t,
      permitDomainSeparator dp sevm.benvStat.chainId.toB256
          sevm.currentTarget :: structHash :: xs <<+ t.stack ∧
      Devm.getStor t = Devm.getStor s ∧
      Devm.getCode t = Devm.getCode s ∧
      t.logs = s.logs ∧ t.output = s.output ∧
      Mem.Wf t.memory ∧
      Mem.Reads t.memory
        (permitDomainDispatchMemoryImage dp sevm.benvStat.chainId.toB256
          sevm.currentTarget img) ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm t permitRecover r := by
  by_cases hchain : sevm.benvStat.chainId.toB256 = dp.deploymentChainId
  · rcases of_permitDomainDispatch_cached dp hchain hp hwf hr run with
      ⟨t, hp', hstor, hcode, hlogs, houtput, hwf', hr', hrecover⟩
    refine ⟨t, ?_, hstor, hcode, hlogs, houtput, hwf', ?_, hrecover⟩
    · simpa [permitDomainSeparator, hchain] using hp'
    · simpa [permitDomainDispatchMemoryImage, hchain] using hr'
  · rcases of_permitDomainDispatch_fork dp hchain hp hwf hr run with
      ⟨t, hp', hstor, hcode, hlogs, houtput, hwf', hr', hrecover⟩
    refine ⟨t, ?_, hstor, hcode, hlogs, houtput, hwf', ?_, hrecover⟩
    · simpa [permitDomainSeparator, hchain] using hp'
    · simpa [permitDomainDispatchMemoryImage, hchain] using hr'

/-! ## The digest walk

The three stores overlap intentionally: the struct hash begins at byte 34,
the full prefix word at byte 0, and the domain at byte 2.  Consequently the
66-byte read is exactly `0x1901 || domain || structHash`, independently of the
memory image that preceded it. -/

def permitDigestMemoryImage (img : Bytes) (domain structHash : B256) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt img 34 structHash.toBytes)
      0 eip712PrefixWord.toBytes)
    2 domain.toBytes

lemma permitDigest_window (img : Bytes) (domain structHash : B256) :
    (permitDigestMemoryImage img domain structHash).sliceD 0 66 0 =
      permitDigestImage domain structHash := by
  unfold permitDigestImage
  have hp : eip712PrefixWord.toBytes.length = 32 :=
    B256.length_toBytes eip712PrefixWord
  have hd : domain.toBytes.length = 32 := B256.length_toBytes domain
  have hs : structHash.toBytes.length = 32 := B256.length_toBytes structHash
  let A := Bytes.writeAt img 34 structHash.toBytes
  let B := Bytes.writeAt A 0 eip712PrefixWord.toBytes
  have eA : A = List.takeD 34 img 0 ++
      (structHash.toBytes ++ img.drop 66) := by
    unfold A Bytes.writeAt
    rw [hs, List.append_assoc]
  have eB : B = eip712PrefixWord.toBytes ++ A.drop 32 := by
    unfold B Bytes.writeAt
    rw [hp, show List.takeD 0 A 0 = [] from rfl, List.nil_append,
      Nat.zero_add]
  have eAdrop : A.drop 34 = structHash.toBytes ++ img.drop 66 := by
    rw [eA, List.drop_append_of_le_length (by rw [List.takeD_length]),
      List.drop_eq_nil_of_le (by rw [List.takeD_length]), List.nil_append]
  have eBtake : List.takeD 2 B 0 = eip712PrefixWord.toBytes.take 2 := by
    rw [eB, List.takeD_eq_take _ (by rw [List.length_append, hp]; omega),
      List.take_append_of_le_length (by rw [hp]; omega)]
  have eBdrop : B.drop 34 = structHash.toBytes ++ img.drop 66 := by
    rw [eB, List.drop_append, hp,
      List.drop_eq_nil_of_le (by omega), List.nil_append,
      show 34 - 32 = 2 by omega, List.drop_drop,
      show 2 + 32 = 34 by omega, eAdrop]
  change (Bytes.writeAt B 2 domain.toBytes).sliceD 0 66 0 = _
  unfold Bytes.writeAt List.sliceD
  rw [hd, eBtake, eBdrop, List.drop_zero,
    List.takeD_eq_take _ (by simp [hp, hd, hs]; omega),
    ← List.append_assoc, List.take_left' (by simp [hp, hd, hs])]

/-- Exact value-carrying inversion of WETH10's `permitDigest` line.  No hash
collision, preimage, or signature assumption occurs: the conclusion names the
bytes supplied to Jaune's own KECCAK256 semantics. -/
theorem of_permitDigest {sevm : Sevm} {s t : Devm}
    {domain structHash : B256} {xs : Stack} {img : Bytes}
    (hp : domain :: structHash :: xs <<+ s.stack)
    (hwf : Mem.Wf s.memory) (hr : Mem.Reads s.memory img)
    (run : Line.Run sevm s permitDigest t) :
    permitDigestValue domain structHash :: xs <<+ t.stack ∧
      Mem.Wf t.memory ∧
      Mem.Reads t.memory (permitDigestMemoryImage img domain structHash) ∧
      Devm.getCode t = Devm.getCode s := by
  have hcode : Devm.getCode s = Devm.getCode t :=
    Line.of_inv Devm.getCode (by
      unfold permitDigest pushList
      line_inv) run
  unfold permitDigest at run
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  have hp1 : structHash :: domain :: xs <<+ s1.stack := by
    have hswap : Stack.Swap (0 : Fin 16).val
        (domain :: structHash :: xs) (structHash :: domain :: xs) :=
      Stack.swapCore_zero
    exact Stack.prefix_of_swap hswap (of_run_swap q1) hp
  have hm1 : s.memory = s1.memory := Ninst.Hinv.inv (f := Devm.memory) q1
  rcases Line.of_run_cons run with ⟨s2, q2, run⟩
  have hb2 := of_run_pushB256 q2
  have hp2 : (34 : B256) :: structHash :: domain :: xs <<+ s2.stack :=
    prefix_of_push hb2 hp1
  have hm2 : s1.memory = s2.memory := hb2.memory
  rcases Line.of_run_cons run with ⟨s3, q3, run⟩
  rcases prefix_of_mstore_val q3 hp2 with ⟨hp3, hm3⟩
  have hwf3 : Mem.Wf s3.memory := by
    rw [hm3, ← hm2, ← hm1]
    exact hwf.write _ _
  have hr3 : Mem.Reads s3.memory
      (Bytes.writeAt img 34 structHash.toBytes) := by
    rw [hm3, ← hm2, ← hm1]
    exact Mem.Reads.write hwf hr 34 _
  rcases Line.of_run_cons run with ⟨s4, q4, run⟩
  have hb4 := of_run_pushB256 q4
  have hp4 : eip712PrefixWord :: domain :: xs <<+ s4.stack :=
    prefix_of_push hb4 hp3
  have hm4 : s3.memory = s4.memory := hb4.memory
  rcases Line.of_run_cons run with ⟨s5, q5, run⟩
  have hb5 := of_run_pushB256 q5
  have hp5 : (0 : B256) :: eip712PrefixWord :: domain :: xs <<+ s5.stack :=
    prefix_of_push hb5 hp4
  have hm5 : s4.memory = s5.memory := hb5.memory
  rcases Line.of_run_cons run with ⟨s6, q6, run⟩
  rcases prefix_of_mstore_val q6 hp5 with ⟨hp6, hm6⟩
  have hwf6 : Mem.Wf s6.memory := by
    rw [hm6, ← hm5, ← hm4]
    exact hwf3.write _ _
  have hr6 : Mem.Reads s6.memory
      (Bytes.writeAt (Bytes.writeAt img 34 structHash.toBytes)
        0 eip712PrefixWord.toBytes) := by
    rw [hm6, ← hm5, ← hm4]
    exact Mem.Reads.write hwf3 hr3 0 _
  rcases Line.of_run_cons run with ⟨s7, q7, run⟩
  have hb7 := of_run_pushB256 q7
  have hp7 : (2 : B256) :: domain :: xs <<+ s7.stack :=
    prefix_of_push hb7 hp6
  have hm7 : s6.memory = s7.memory := hb7.memory
  rcases Line.of_run_cons run with ⟨s8, q8, run⟩
  rcases prefix_of_mstore_val q8 hp7 with ⟨hp8, hm8⟩
  have hwf8 : Mem.Wf s8.memory := by
    rw [hm8, ← hm7]
    exact hwf6.write _ _
  have hr8 : Mem.Reads s8.memory
      (permitDigestMemoryImage img domain structHash) := by
    rw [hm8, ← hm7]
    exact Mem.Reads.write hwf6 hr6 2 _
  rcases Line.of_run_cons run with ⟨s9, q9, run⟩
  have hb9 := of_run_pushB256 q9
  have hp9 : (66 : B256) :: xs <<+ s9.stack := prefix_of_push hb9 hp8
  have hm9 : s8.memory = s9.memory := hb9.memory
  rcases Line.of_run_cons run with ⟨s10, q10, run⟩
  have hb10 := of_run_pushB256 q10
  have hp10 : (0 : B256) :: (66 : B256) :: xs <<+ s10.stack :=
    prefix_of_push hb10 hp9
  have hm10 : s9.memory = s10.memory := hb10.memory
  rcases Line.of_run_cons run with ⟨s11, q11, hnil⟩
  cases hnil
  have hk := prefix_of_kec_val q11 hp10
  have hread : (s10.memory.read 0 66).1 =
      permitDigestImage domain structHash := by
    rw [Mem.Reads.read (hm10 ▸ hm9 ▸ hr8) 0 66, permitDigest_window]
  have hk' : (s10.memory.read 0 66).1.keccak :: xs <<+ t.stack ∧
      t.memory = s10.memory.extend 0 66 := by
    rw [show (0 : B256).toNat = 0 from rfl,
      show (66 : B256).toNat = 66 from rfl] at hk
    exact hk
  rw [hread] at hk'
  refine ⟨?_, ?_, ?_, hcode.symm⟩
  · simpa only [permitDigestValue] using hk'.1
  · rw [hk'.2, ← hm10, ← hm9]
    exact hwf8.extend _ _
  · rw [hk'.2, ← hm10, ← hm9]
    exact Mem.Reads.extend hr8 _ _

/-! ## Deadline guard

The source guard is strict (`timestamp > deadline`).  Equality therefore
belongs to the live arm.  More importantly, the observation below is proved
from a successful run through the exact WETH10 auxiliary table: a hypothetical
nonzero guard would have entered the fixed `expiredPermitError` reverter, which
has no successful `Func.Run`. -/

private lemma memory_eq_of_timestamp {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s timestamp s') : s.memory = s'.memory := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).memory

private lemma logs_eq_of_timestamp {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s timestamp s') : s.logs = s'.logs := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).logs

private lemma output_eq_of_timestamp {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s timestamp s') : s.output = s'.output := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).output

lemma permitDeadlineFlag_eq (t : B256) : (t >? t) = 0 := by
  simp [B256.gtCheck]

lemma permitDeadlineFlag_expired {timestamp deadline : B256}
    (h : timestamp > deadline) : (timestamp >? deadline) = 1 := by
  simp [B256.gtCheck, h]

/-- A successful selected-body execution must enter the live deadline arm.
The returned machine is exactly the start of the nonce prefix; the guard and
branch pop preserve storage and memory. -/
theorem of_permitDeadlineLive (dp : DeployParams)
    {sevm : Sevm} {s r : Devm} {xs : Stack}
    (hp : xs <<+ s.stack)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s (permit dp) r) :
    ∃ mid,
      xs <<+ mid.stack ∧
      Devm.getStor mid = Devm.getStor s ∧
      Devm.getCode mid = Devm.getCode s ∧
      mid.memory = s.memory ∧
      mid.logs = s.logs ∧ mid.output = s.output ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm mid
        (permitAfterDeadline dp) r := by
  rw [permit_eq_deadlineGuard] at run
  refine run_prepend_elim _ (arg 3 ++ [timestamp, gt]) ?_ run
  intro flagState hguard hbranch
  rcases of_run_append (arg 3) hguard with ⟨argState, harg, hrest⟩
  rcases Line.of_run_cons hrest with ⟨timeState, htime, hrest⟩
  rcases Line.of_run_cons hrest with ⟨gtState, hgt, hnil⟩
  cases hnil
  have hpArg : Sevm.argWord sevm 3 :: xs <<+ argState.stack :=
    prefix_of_arg hp harg
  have hpTime : sevm.benvStat.time :: Sevm.argWord sevm 3 :: xs <<+
      timeState.stack := prefix_of_timestamp hpArg htime
  have hpFlag : (sevm.benvStat.time >? Sevm.argWord sevm 3) :: xs <<+
      flagState.stack := prefix_of_gt hgt hpTime
  have hmemory : s.memory = flagState.memory := by
    calc
      s.memory = argState.memory :=
        Line.of_inv Devm.memory (by line_inv) harg
      _ = timeState.memory := memory_eq_of_timestamp htime
      _ = flagState.memory := Ninst.Hinv.inv (f := Devm.memory) hgt
  rcases of_run_branch hbranch with
      ⟨mid, hpop, hlive⟩ |
      ⟨w, mid0, mid, hnz, hpop, hburn, hexpired⟩
  · refine ⟨mid, (popBurn_pref hpop hpFlag).2, ?_, ?_, ?_, ?_, ?_, hlive⟩
    · calc
        Devm.getStor mid = Devm.getStor flagState :=
          (PopBurn.Inv.inv hpop).symm
        _ = Devm.getStor s :=
          (Line.of_inv Devm.getStor (by line_inv) hguard).symm
    · funext a
      calc
        Devm.getCode mid a = Devm.getCode flagState a :=
          getCode_eq_of_state_eq hpop.state.symm a
        _ = Devm.getCode s a := congrFun
          (Line.of_inv Devm.getCode (by line_inv) hguard).symm a
    · exact hpop.memory.symm.trans hmemory.symm
    · exact hpop.logs.symm.trans (by
        symm
        calc
          s.logs = argState.logs := Line.of_inv Devm.logs (by line_inv) harg
          _ = timeState.logs := logs_eq_of_timestamp htime
          _ = flagState.logs := Ninst.Hinv.inv (f := Devm.logs) hgt)
    · exact hpop.output.symm.trans (by
        symm
        calc
          s.output = argState.output :=
            Line.of_inv Devm.output (by line_inv) harg
          _ = timeState.output := output_eq_of_timestamp htime
          _ = flagState.output := Ninst.Hinv.inv (f := Devm.output) hgt)
  · rcases of_run_call hexpired with ⟨f, s3, hget, hcallBurn, hrev⟩
    have hf : f = expiredPermitError := by
      simpa [weth10Aux, expiredPermitErrorSlot] using hget.symm
    subst f
    exact absurd hrev Func.not_run_revWith

/-- Exact successful prefix from the live deadline arm to the recovery
function.  It exposes the original nonce in the signed struct, the tentative
nonce increment in storage, and the cached-or-recomputed domain image selected
by the current chain id. -/
theorem of_permitAfterDeadline (dp : DeployParams)
    {sevm : Sevm} {s r : Devm}
    {owner spender : Adr} {value deadline : B256}
    {v : UInt8} {sigR sigS : B256} {xs : Stack} {img : Bytes}
    (hdec : DecodesPermit sevm owner spender value deadline v sigR sigS)
    (hp : xs <<+ s.stack) (hwf : Mem.Wf s.memory)
    (hr : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (permitAfterDeadline dp) r) :
    let nonce := Devm.getStorVal s sevm.currentTarget (nonceKey owner)
    ∃ t,
      permitDomainSeparator dp sevm.benvStat.chainId.toB256
          sevm.currentTarget ::
        permitStructHash owner spender value nonce deadline :: xs <<+
          t.stack ∧
      Devm.getStor t sevm.currentTarget =
        (Devm.getStor s sevm.currentTarget).set
          (nonceKey owner) (nonce + 1) ∧
      Devm.getCode t = Devm.getCode s ∧
      t.logs = s.logs ∧ t.output = s.output ∧
      Mem.Wf t.memory ∧
      Mem.Reads t.memory
        (permitDomainDispatchMemoryImage dp sevm.benvStat.chainId.toB256
          sevm.currentTarget
          (permitStructMemoryImage img owner spender value nonce deadline)) ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm t permitRecover r := by
  dsimp only
  unfold permitAfterDeadline at run
  rcases of_run_prepend permitNoncePrepare _ run with
    ⟨s1, hnonceRun, run⟩
  rcases of_permitNoncePrepare hdec hp hwf hr hnonceRun with
    ⟨hp1, hstor1, hcode1, hlogs1, houtput1, hwf1, hr1⟩
  rcases of_run_prepend permitStructPrepare _ run with
    ⟨s2, hstructRun, hdomainRun⟩
  rcases of_permitStructPrepare hdec hp1 hwf1 hr1 hstructRun with
    ⟨hp2, hwf2, hr2, hcode2, hlogs2, houtput2⟩
  rcases of_permitDomainDispatch dp hp2 hwf2 hr2 hdomainRun with
    ⟨t, hp3, hstor3, hcode3, hlogs3, houtput3, hwf3, hr3, hrecover⟩
  refine ⟨t, hp3, ?_, hcode3.trans (hcode2.trans hcode1),
    hlogs3.trans (hlogs2.trans hlogs1),
    houtput3.trans (houtput2.trans houtput1), hwf3, hr3, hrecover⟩
  · calc
      Devm.getStor t sevm.currentTarget =
          Devm.getStor s2 sevm.currentTarget := congrFun hstor3 _
      _ = Devm.getStor s1 sevm.currentTarget :=
        congrFun (Line.of_inv Devm.getStor (by
          unfold permitStructPrepare
          line_inv) hstructRun).symm _
      _ = (Devm.getStor s sevm.currentTarget).set
          (nonceKey owner)
          (Devm.getStorVal s sevm.currentTarget (nonceKey owner) + 1) :=
        hstor1

/-- A successful selected permit body reaches `permitRecover` with the exact
EIP-712 domain/struct pair and the nonce increment only tentatively committed.
This is the selected-body theorem; compiled selector entry and transaction
rollback are layered separately. -/
theorem of_permitToRecover (dp : DeployParams)
    {sevm : Sevm} {s r : Devm}
    {owner spender : Adr} {value deadline : B256}
    {v : UInt8} {sigR sigS : B256} {xs : Stack} {img : Bytes}
    (hdec : DecodesPermit sevm owner spender value deadline v sigR sigS)
    (hp : xs <<+ s.stack) (hwf : Mem.Wf s.memory)
    (hr : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (permit dp) r) :
    let nonce := Devm.getStorVal s sevm.currentTarget (nonceKey owner)
    ∃ t,
      permitDomainSeparator dp sevm.benvStat.chainId.toB256
          sevm.currentTarget ::
        permitStructHash owner spender value nonce deadline :: xs <<+
          t.stack ∧
      Devm.getStor t sevm.currentTarget =
        (Devm.getStor s sevm.currentTarget).set
          (nonceKey owner) (nonce + 1) ∧
      Devm.getCode t = Devm.getCode s ∧
      t.logs = s.logs ∧ t.output = s.output ∧
      Mem.Wf t.memory ∧
      Mem.Reads t.memory
        (permitDomainDispatchMemoryImage dp sevm.benvStat.chainId.toB256
          sevm.currentTarget
          (permitStructMemoryImage img owner spender value nonce deadline)) ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm t permitRecover r := by
  dsimp only
  rcases of_permitDeadlineLive dp hp run with
    ⟨mid, hpMid, hstorMid, hcodeMid, hmemMid,
      hlogsMid, houtputMid, hlive⟩
  have hwfMid : Mem.Wf mid.memory := by
    rw [hmemMid]
    exact hwf
  have hrMid : Mem.Reads mid.memory img := by
    rw [hmemMid]
    exact hr
  rcases of_permitAfterDeadline dp hdec hpMid hwfMid hrMid hlive with
    ⟨t, hpT, hstorT, hcodeT, hlogsT, houtputT, hwfT, hrT, hrecover⟩
  have hnonce : Devm.getStorVal mid sevm.currentTarget (nonceKey owner) =
      Devm.getStorVal s sevm.currentTarget (nonceKey owner) := by
    change (Devm.getStor mid sevm.currentTarget).get (nonceKey owner) =
      (Devm.getStor s sevm.currentTarget).get (nonceKey owner)
    rw [hstorMid]
  rw [hnonce] at hpT hstorT hrT
  rw [hstorMid] at hstorT
  exact ⟨t, hpT, hstorT, hcodeT.trans hcodeMid,
    hlogsT.trans hlogsMid,
    houtputT.trans houtputMid, hwfT, hrT, hrecover⟩

/-! ## Signer guards

The recovery line is separated from the two Solidity-style guards.  This makes
the authentication policy observable independently of the `STATICCALL`
crossing: any successful continuation must have received a nonzero word equal
to the canonical owner argument, and must enter the approval tail with the
signer consumed. -/

def permitSignerGuards : Func :=
  dup 0 ::: iszero :::
  (.call invalidPermitErrorSlot) <?>
  (arg 0 +++ eq ::: iszero :::
    (.call invalidPermitErrorSlot) <?>
    approvePermit)

lemma permitRecover_eq :
    permitRecover = permitDigest +++ recoverPermitSigner +++ permitSignerGuards := by
  rfl

/-! ## Shared cursor decompositions

These names expose the exact WETH10 program fragments used by both the
allowance and holder-flow cursor proofs. -/

def approvePermitLine : Line :=
  argCopy 0 0 2 ++ allowanceKeyFromMemory ++
  Blanc.arg 2 ++ [Ninst.swap 0, Ninst.sstore] ++
  Blanc.arg 2 ++ mstoreAt 0 ++ Blanc.arg 1 ++ Blanc.arg 0 ++
  [Ninst.pushB256 Blanc.approvalEvent] ++ logWith 2 0 1

theorem approvePermit_shape :
    approvePermit = approvePermitLine +++ Func.stop := by
  simp only [approvePermit, approvePermitLine, prepend_append,
    List.append_assoc, prepend]

def permitFirstSignerGuardLine : Line :=
  [Ninst.pop, Ninst.pushB256 128, Ninst.mload, Ninst.dup 0, Ninst.iszero]

def permitSecondSignerGuardLine : Line :=
  arg 0 ++ [Ninst.eq, Ninst.iszero]

def permitAfterStaticcall : Func :=
  permitFirstSignerGuardLine +++
    (.branch
      (permitSecondSignerGuardLine +++
        (.branch approvePermit (.call invalidPermitErrorSlot)))
      (.call invalidPermitErrorSlot))

theorem permitRecover_afterStaticcall_shape :
    permitRecover =
      (permitDigest ++ permitRecoverPrepare) +++
        (Ninst.statcall ::: permitAfterStaticcall) := by
  rw [permitRecover_eq, recoverPermitSigner_eq_prepare]
  unfold permitSignerGuards permitAfterStaticcall
    permitFirstSignerGuardLine permitSecondSignerGuardLine
  rfl

def permitDomainTestLine (dp : DeployParams) : Line :=
  [Ninst.dup 1, pushDeployWord dp.deploymentChainId, Ninst.eq]

def permitCalculatedDomainPrefix : Line :=
  [Ninst.swap 0] ++ calculateDomainSeparator

def permitCachedDomainPrefix (dp : DeployParams) : Line :=
  [Ninst.swap 0, Ninst.pop, pushDeployWord dp.cachedDomainSeparator]

theorem permitDomainDispatch_shape (dp : DeployParams) :
    permitDomainDispatch dp =
      permitDomainTestLine dp +++
        (.branch
          (permitCalculatedDomainPrefix +++ .call permitRecoverSlot)
          (permitCachedDomainPrefix dp +++ .call permitRecoverSlot)) := by
  rfl

/-- Exact successful policy enforced after ECRECOVER, together with the frame
at the entry to `approvePermit`: zero and wrong-owner words cannot reach the
approval tail, and the two guards change no storage, memory, logs, or output.
This theorem deliberately begins after the recovery line; the address-1
precompile image is connected separately. -/
theorem of_permitSignerGuards_frame (dp : DeployParams)
    {sevm : Sevm} {s r : Devm}
    {owner spender : Adr} {value deadline : B256}
    {v : UInt8} {sigR sigS signer : B256} {xs : Stack}
    (hdec : DecodesPermit sevm owner spender value deadline v sigR sigS)
    (hp : signer :: xs <<+ s.stack)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      permitSignerGuards r) :
    signer ≠ 0 ∧ signer = owner.toB256 ∧
      ∃ t, xs <<+ t.stack ∧
        Devm.getStor t = Devm.getStor s ∧
        t.memory = s.memory ∧ t.logs = s.logs ∧ t.output = s.output ∧
        Func.Run ((weth10 dp).main :: weth10Aux) sevm t approvePermit r := by
  unfold permitSignerGuards at run
  rcases of_run_next run with ⟨s1, hdup, run⟩
  have hp1 : signer :: signer :: xs <<+ s1.stack :=
    prefix_of_dup_val hdup (by show_nth) hp
  rcases of_run_next run with ⟨s2, hzero, run⟩
  have hp2 : (signer =? 0) :: signer :: xs <<+ s2.stack :=
    prefix_of_iszero hzero hp1
  rcases of_run_branch run with
      ⟨s3, hpop1, run⟩ |
      ⟨w1, s3, s4, hnz1, hpop1, hburn1, hinvalid1⟩
  · have hflag1 : (0 : B256) = (signer =? 0) :=
      (popBurn_pref hpop1 hp2).1
    have hsigner : signer ≠ 0 := by
      intro hz
      subst signer
      simp [B256.eqCheck] at hflag1
      exact B256.zero_ne_one hflag1
    have hp3 : signer :: xs <<+ s3.stack := (popBurn_pref hpop1 hp2).2
    rcases of_run_prepend (arg 0) _ run with ⟨s4, harg0, run⟩
    have hp4 : owner.toB256 :: signer :: xs <<+ s4.stack := by
      rw [← argWord_zero_of_decodesPermit hdec]
      exact prefix_of_arg hp3 harg0
    rcases of_run_next run with ⟨s5, heq, run⟩
    have hp5 : (owner.toB256 =? signer) :: xs <<+ s5.stack :=
      prefix_of_eq heq hp4
    rcases of_run_next run with ⟨s6, hzero2, run⟩
    have hp6 : ((owner.toB256 =? signer) =? 0) :: xs <<+ s6.stack :=
      prefix_of_iszero hzero2 hp5
    rcases of_run_branch run with
        ⟨t, hpop2, happrove⟩ |
        ⟨w2, t0, t, hnz2, hpop2, hburn2, hinvalid2⟩
    · have hflag2 : (0 : B256) = ((owner.toB256 =? signer) =? 0) :=
        (popBurn_pref hpop2 hp6).1
      have howner : signer = owner.toB256 := by
        by_contra hne
        have hne' : owner.toB256 ≠ signer := Ne.symm hne
        simp [B256.eqCheck, hne'] at hflag2
        exact B256.zero_ne_one hflag2
      have hstor : Devm.getStor t = Devm.getStor s := by
        symm
        calc
          Devm.getStor s = Devm.getStor s1 :=
            Ninst.Hinv.inv (f := Devm.getStor) hdup
          _ = Devm.getStor s2 := Ninst.Hinv.inv (f := Devm.getStor) hzero
          _ = Devm.getStor s3 := PopBurn.Inv.inv hpop1
          _ = Devm.getStor s4 :=
            Line.of_inv Devm.getStor (by line_inv) harg0
          _ = Devm.getStor s5 := Ninst.Hinv.inv (f := Devm.getStor) heq
          _ = Devm.getStor s6 := Ninst.Hinv.inv (f := Devm.getStor) hzero2
          _ = Devm.getStor t := PopBurn.Inv.inv hpop2
      have hmemory : t.memory = s.memory := by
        symm
        calc
          s.memory = s1.memory := Ninst.Hinv.inv (f := Devm.memory) hdup
          _ = s2.memory := Ninst.Hinv.inv (f := Devm.memory) hzero
          _ = s3.memory := hpop1.memory
          _ = s4.memory := Line.of_inv Devm.memory (by line_inv) harg0
          _ = s5.memory := Ninst.Hinv.inv (f := Devm.memory) heq
          _ = s6.memory := Ninst.Hinv.inv (f := Devm.memory) hzero2
          _ = t.memory := hpop2.memory
      have hlogs : t.logs = s.logs := by
        symm
        calc
          s.logs = s1.logs := Ninst.Hinv.inv (f := Devm.logs) hdup
          _ = s2.logs := Ninst.Hinv.inv (f := Devm.logs) hzero
          _ = s3.logs := hpop1.logs
          _ = s4.logs := Line.of_inv Devm.logs (by line_inv) harg0
          _ = s5.logs := Ninst.Hinv.inv (f := Devm.logs) heq
          _ = s6.logs := Ninst.Hinv.inv (f := Devm.logs) hzero2
          _ = t.logs := hpop2.logs
      have houtput : t.output = s.output := by
        symm
        calc
          s.output = s1.output := Ninst.Hinv.inv (f := Devm.output) hdup
          _ = s2.output := Ninst.Hinv.inv (f := Devm.output) hzero
          _ = s3.output := hpop1.output
          _ = s4.output := Line.of_inv Devm.output (by line_inv) harg0
          _ = s5.output := Ninst.Hinv.inv (f := Devm.output) heq
          _ = s6.output := Ninst.Hinv.inv (f := Devm.output) hzero2
          _ = t.output := hpop2.output
      exact ⟨hsigner, howner, t, (popBurn_pref hpop2 hp6).2,
        hstor, hmemory, hlogs, houtput, happrove⟩
    · rcases of_run_call hinvalid2 with ⟨f, u, hget, hcallBurn, hrev⟩
      have hf : f = invalidPermitError := by
        simpa [weth10Aux, invalidPermitErrorSlot] using hget.symm
      subst f
      exact absurd hrev Func.not_run_revWith
  · rcases of_run_call hinvalid1 with ⟨f, u, hget, hcallBurn, hrev⟩
    have hf : f = invalidPermitError := by
      simpa [weth10Aux, invalidPermitErrorSlot] using hget.symm
    subst f
    exact absurd hrev Func.not_run_revWith

/-- Compatibility projection of `of_permitSignerGuards_frame`. -/
theorem of_permitSignerGuards (dp : DeployParams)
    {sevm : Sevm} {s r : Devm}
    {owner spender : Adr} {value deadline : B256}
    {v : UInt8} {sigR sigS signer : B256} {xs : Stack}
    (hdec : DecodesPermit sevm owner spender value deadline v sigR sigS)
    (hp : signer :: xs <<+ s.stack)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      permitSignerGuards r) :
    signer ≠ 0 ∧ signer = owner.toB256 ∧
      ∃ t, xs <<+ t.stack ∧
        Func.Run ((weth10 dp).main :: weth10Aux) sevm t approvePermit r := by
  rcases of_permitSignerGuards_frame dp hdec hp run with
    ⟨hsigner, howner, t, hpT, _, _, _, _, happrove⟩
  exact ⟨hsigner, howner, t, hpT, happrove⟩

/-! ## Canonical approval tail -/

private lemma of_permitArgCopyZeroTwo {e : Sevm} {s s' : Devm}
    {owner spender : Adr} {value deadline : B256}
    {v : UInt8} {sigR sigS : B256} {xs : Stack}
    (hdec : DecodesPermit e owner spender value deadline v sigR sigS)
    (hp : xs <<+ s.stack)
    (run : Line.Run e s (argCopy 0 0 2) s') :
    xs <<+ s'.stack ∧
      s'.memory = s.memory.write 0
        (owner.toB256.toBytes ++ spender.toB256.toBytes) := by
  simp only [argCopy, cdc] at run
  rcases Line.of_run_cons run with ⟨u1, q1, run⟩
  have hp1 : (64 : B256) :: xs <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp
  rcases Line.of_run_cons run with ⟨u2, q2, run⟩
  have hp2 : (4 : B256) :: 64 :: xs <<+ u2.stack :=
    prefix_of_push (of_run_pushB256 q2) hp1
  rcases Line.of_run_cons run with ⟨u3, q3, run⟩
  have hp3 : (0 : B256) :: 4 :: 64 :: xs <<+ u3.stack :=
    prefix_of_push (of_run_pushB256 q3) hp2
  rcases Line.of_run_cons run with ⟨u4, q4, hnil⟩
  cases hnil
  rcases prefix_of_calldatacopy_val q4 hp3 with ⟨hp4, hm4⟩
  refine ⟨hp4, ?_⟩
  rw [hm4,
    ← (Ninst.Hinv.inv (f := Devm.memory) q3),
    ← (Ninst.Hinv.inv (f := Devm.memory) q2),
    ← (Ninst.Hinv.inv (f := Devm.memory) q1),
    show (0 : B256).toNat = 0 from rfl,
    show (4 : B256).toNat = 4 from rfl,
    show (64 : B256).toNat = 64 from rfl,
    permitData_args_zero_two hdec]

private theorem of_permitAllowanceKeyFromMemory {e : Sevm}
    {s t : Devm} {owner spender : Adr} {xs : Stack} {img : Bytes}
    (hp : xs <<+ s.stack) (hwf : Mem.Wf s.memory)
    (hr : Mem.Reads s.memory
      (Bytes.writeAt img 0
        (owner.toB256.toBytes ++ spender.toB256.toBytes)))
    (run : Line.Run e s allowanceKeyFromMemory t) :
    allowanceKey owner spender :: xs <<+ t.stack ∧
      Mem.Wf t.memory ∧
      Mem.Reads t.memory
        (Bytes.writeAt img 0
          (owner.toB256.toBytes ++ spender.toB256.toBytes)) := by
  unfold allowanceKeyFromMemory pushList at run
  simp only [List.map] at run
  rcases Line.of_run_cons run with ⟨u1, q1, run⟩
  have hp1 : (64 : B256) :: xs <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp
  rcases Line.of_run_cons run with ⟨u2, q2, run⟩
  have hp2 : (0 : B256) :: 64 :: xs <<+ u2.stack :=
    prefix_of_push (of_run_pushB256 q2) hp1
  have hm2 : s.memory = u2.memory := by
    calc
      s.memory = u1.memory := Ninst.Hinv.inv (f := Devm.memory) q1
      _ = u2.memory := Ninst.Hinv.inv (f := Devm.memory) q2
  rcases Line.of_run_cons run with ⟨u3, q3, run⟩
  rcases prefix_of_kec_val q3 hp2 with ⟨hp3raw, hm3⟩
  rw [show (0 : B256).toNat = 0 from rfl,
    show (64 : B256).toNat = 64 from rfl] at hp3raw hm3
  have hread : (u2.memory.read 0 64).1 =
      owner.toB256.toBytes ++ spender.toB256.toBytes := by
    rw [Mem.Reads.read (hm2 ▸ hr) 0 64,
      show 64 = (owner.toB256.toBytes ++
        spender.toB256.toBytes).length by
          simp only [List.length_append, B256.length_toBytes],
      Bytes.sliceD_writeAt]
  have hp3 : allowanceHash owner spender :: xs <<+ u3.stack := by
    rw [hread] at hp3raw
    simpa only [allowanceHash] using hp3raw
  rcases Line.of_run_cons run with ⟨u4, q4, run⟩
  have hp4 : allowancePayloadMask :: allowanceHash owner spender :: xs <<+
      u4.stack := prefix_of_push (of_run_pushB256 q4) hp3
  rcases Line.of_run_cons run with ⟨u5, q5, run⟩
  have hp5 : (allowancePayloadMask &&& allowanceHash owner spender) :: xs <<+
      u5.stack := prefix_of_and q5 hp4
  rcases Line.of_run_cons run with ⟨u6, q6, run⟩
  have hp6 : allowanceTagWord ::
      (allowancePayloadMask &&& allowanceHash owner spender) :: xs <<+
      u6.stack := prefix_of_push (of_run_pushB256 q6) hp5
  rcases Line.of_run_cons run with ⟨u7, q7, hnil⟩
  cases hnil
  have hp7raw := prefix_of_or q7 hp6
  have hp7 : allowanceKey owner spender :: xs <<+ t.stack := by
    simpa only [allowanceHash, permitAllowanceRuntimeKey_eq] using hp7raw
  have hmTail : u3.memory = t.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons q4
        (Line.Run.cons q5 (Line.Run.cons q6 (Line.Run.cons q7 Line.Run.nil))))
  refine ⟨hp7, ?_, ?_⟩
  · rw [← hmTail, hm3, ← hm2]
    exact hwf.extend _ _
  · rw [← hmTail, hm3, ← hm2]
    exact Mem.Reads.extend hr _ _

/-- The approval tail's unique storage write is the canonical ERC-20
allowance entry for the signed owner/spender pair. -/
theorem approvePermit_storage
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    {owner spender : Adr} {value deadline : B256}
    {v : UInt8} {sigR sigS : B256} {xs : Stack} {img : Bytes}
    (hdec : DecodesPermit sevm owner spender value deadline v sigR sigS)
    (hp : xs <<+ s.stack) (hwf : Mem.Wf s.memory)
    (hr : Mem.Reads s.memory img)
    (run : Func.Run fs sevm s approvePermit r) :
    Devm.getStor r sevm.currentTarget =
      (Devm.getStor s sevm.currentTarget).set
        (allowanceKey owner spender) value := by
  unfold approvePermit at run
  rcases of_run_prepend (argCopy 0 0 2) _ run with
    ⟨s1, hcopy, run⟩
  rcases of_permitArgCopyZeroTwo hdec hp hcopy with ⟨hp1, hm1⟩
  have hwf1 : Mem.Wf s1.memory := by
    rw [hm1]
    exact hwf.write _ _
  have hr1 : Mem.Reads s1.memory
      (Bytes.writeAt img 0
        (owner.toB256.toBytes ++ spender.toB256.toBytes)) := by
    rw [hm1]
    exact Mem.Reads.write hwf hr 0 _
  rcases of_run_prepend allowanceKeyFromMemory _ run with
    ⟨s2, hkey, run⟩
  rcases of_permitAllowanceKeyFromMemory hp1 hwf1 hr1 hkey with
    ⟨hp2, hwf2, hr2⟩
  rcases of_run_prepend (arg 2) _ run with ⟨s3, harg, run⟩
  have hp3 : value :: allowanceKey owner spender :: xs <<+ s3.stack := by
    rw [← argWord_two_of_decodesPermit hdec]
    exact prefix_of_arg hp2 harg
  rcases of_run_next run with ⟨s4, hswap, run⟩
  have hswapCore : Stack.Swap (0 : Fin 16).val
      (value :: allowanceKey owner spender :: xs)
      (allowanceKey owner spender :: value :: xs) := Stack.swapCore_zero
  have hp4 : allowanceKey owner spender :: value :: xs <<+ s4.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp3
  rcases of_run_next run with ⟨s5, hstore, htail⟩
  have hset : Devm.getStor s5 sevm.currentTarget =
      (Devm.getStor s4 sevm.currentTarget).set
        (allowanceKey owner spender) value :=
    sstore_getStor_set hstore hp4
  have hbefore : Devm.getStor s = Devm.getStor s4 := by
    calc
      Devm.getStor s = Devm.getStor s1 :=
        Line.of_inv Devm.getStor (by line_inv) hcopy
      _ = Devm.getStor s2 :=
        Line.of_inv Devm.getStor (by
          unfold allowanceKeyFromMemory pushList
          line_inv) hkey
      _ = Devm.getStor s3 :=
        Line.of_inv Devm.getStor (by line_inv) harg
      _ = Devm.getStor s4 := Ninst.Hinv.inv (f := Devm.getStor) hswap
  have hafter : Devm.getStor s5 = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) htail
  rw [← congrFun hafter sevm.currentTarget, hset,
    ← congrFun hbefore sevm.currentTarget]

def permitApprovalLog (target : Adr) (owner spender : Adr)
    (value : B256) : Log :=
  ⟨target, [approvalEvent, owner.toB256, spender.toB256], value.toBytes⟩

/-- Exact successful effect of `approvePermit`: one canonical allowance write,
one canonical `Approval` log, and no return-data output mutation. -/
theorem approvePermit_effect
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    {owner spender : Adr} {value deadline : B256}
    {v : UInt8} {sigR sigS : B256} {xs : Stack} {img : Bytes}
    (hdec : DecodesPermit sevm owner spender value deadline v sigR sigS)
    (hp : xs <<+ s.stack) (hwf : Mem.Wf s.memory)
    (hr : Mem.Reads s.memory img)
    (run : Func.Run fs sevm s approvePermit r) :
    Devm.getStor r sevm.currentTarget =
        (Devm.getStor s sevm.currentTarget).set
          (allowanceKey owner spender) value ∧
      r.logs = s.logs ++
        [permitApprovalLog sevm.currentTarget owner spender value] ∧
      r.output = s.output := by
  have hstorage := approvePermit_storage hdec hp hwf hr run
  have houtput : s.output = r.output :=
    Func.of_inv Devm.output Devm.output (by
      unfold approvePermit allowanceKeyFromMemory argCopy cdc pushList
      func_inv) run
  unfold approvePermit at run
  rcases of_run_prepend (argCopy 0 0 2) _ run with
    ⟨s1, hcopy, run⟩
  rcases of_permitArgCopyZeroTwo hdec hp hcopy with ⟨hp1, hm1⟩
  have hwf1 : Mem.Wf s1.memory := by
    rw [hm1]
    exact hwf.write _ _
  have hr1 : Mem.Reads s1.memory
      (Bytes.writeAt img 0
        (owner.toB256.toBytes ++ spender.toB256.toBytes)) := by
    rw [hm1]
    exact Mem.Reads.write hwf hr 0 _
  rcases of_run_prepend allowanceKeyFromMemory _ run with
    ⟨s2, hkey, run⟩
  rcases of_permitAllowanceKeyFromMemory hp1 hwf1 hr1 hkey with
    ⟨hp2, hwf2, hr2⟩
  rcases of_run_prepend (arg 2) _ run with ⟨s3, harg2a, run⟩
  have hp3 : value :: allowanceKey owner spender :: xs <<+ s3.stack := by
    rw [← argWord_two_of_decodesPermit hdec]
    exact prefix_of_arg hp2 harg2a
  rcases of_run_next run with ⟨s4, hswap, run⟩
  have hswapCore : Stack.Swap (0 : Fin 16).val
      (value :: allowanceKey owner spender :: xs)
      (allowanceKey owner spender :: value :: xs) := Stack.swapCore_zero
  have hp4 : allowanceKey owner spender :: value :: xs <<+ s4.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp3
  rcases of_run_next run with ⟨s5, hstore, run⟩
  have hp5 : xs <<+ s5.stack := prefix_of_sstore hstore hp4
  rcases of_run_prepend (arg 2) _ run with ⟨s6, harg2b, run⟩
  have hp6 : value :: xs <<+ s6.stack := by
    rw [← argWord_two_of_decodesPermit hdec]
    exact prefix_of_arg hp5 harg2b
  have hm2to6 : s2.memory = s6.memory := by
    calc
      s2.memory = s3.memory :=
        Line.of_inv Devm.memory (by line_inv) harg2a
      _ = s4.memory := Ninst.Hinv.inv (f := Devm.memory) hswap
      _ = s5.memory := Ninst.Hinv.inv (f := Devm.memory) hstore
      _ = s6.memory := Line.of_inv Devm.memory (by line_inv) harg2b
  have hwf6 : Mem.Wf s6.memory := hm2to6 ▸ hwf2
  have hr6 : Mem.Reads s6.memory
      (Bytes.writeAt img 0
        (owner.toB256.toBytes ++ spender.toB256.toBytes)) := hm2to6 ▸ hr2
  rcases of_run_prepend (mstoreAt 0) _ run with ⟨s7, hmstore, run⟩
  rcases of_run_mstoreAt_val hmstore hp6 with ⟨hp7, hm7⟩
  rw [show (((0 : B256) * 32).toNat) = 0 from rfl] at hm7
  have hr7 : Mem.Reads s7.memory
      (Bytes.writeAt
        (Bytes.writeAt img 0
          (owner.toB256.toBytes ++ spender.toB256.toBytes))
        0 value.toBytes) := by
    rw [hm7]
    exact Mem.Reads.write hwf6 hr6 0 _
  rcases of_run_prepend (arg 1) _ run with ⟨s8, harg1, run⟩
  have hp8 : spender.toB256 :: xs <<+ s8.stack := by
    rw [← argWord_one_of_decodesPermit hdec]
    exact prefix_of_arg hp7 harg1
  rcases of_run_prepend (arg 0) _ run with ⟨s9, harg0, run⟩
  have hp9 : owner.toB256 :: spender.toB256 :: xs <<+ s9.stack := by
    rw [← argWord_zero_of_decodesPermit hdec]
    exact prefix_of_arg hp8 harg0
  rcases of_run_next run with ⟨s10, hevent, run⟩
  have hp10 : approvalEvent :: owner.toB256 :: spender.toB256 :: xs <<+
      s10.stack := prefix_of_push (of_run_pushB256 hevent) hp9
  have hm7to10 : s7.memory = s10.memory := by
    calc
      s7.memory = s8.memory := Line.of_inv Devm.memory (by line_inv) harg1
      _ = s9.memory := Line.of_inv Devm.memory (by line_inv) harg0
      _ = s10.memory := Ninst.Hinv.inv (f := Devm.memory) hevent
  have hread : (s10.memory.read 0 32).1 = value.toBytes := by
    rw [Mem.Reads.read (hm7to10 ▸ hr7) 0 32,
      show 32 = value.toBytes.length from (B256.length_toBytes value).symm,
      Bytes.sliceD_writeAt]
  have hlogsTo10 : s.logs = s10.logs := by
    calc
      s.logs = s1.logs := Line.of_inv Devm.logs (by
        unfold argCopy cdc
        line_inv) hcopy
      _ = s2.logs := Line.of_inv Devm.logs (by
        unfold allowanceKeyFromMemory pushList
        line_inv) hkey
      _ = s3.logs := Line.of_inv Devm.logs (by line_inv) harg2a
      _ = s4.logs := Ninst.Hinv.inv (f := Devm.logs) hswap
      _ = s5.logs := Ninst.Hinv.inv (f := Devm.logs) hstore
      _ = s6.logs := Line.of_inv Devm.logs (by line_inv) harg2b
      _ = s7.logs := Line.of_inv Devm.logs (by line_inv) hmstore
      _ = s8.logs := Line.of_inv Devm.logs (by line_inv) harg1
      _ = s9.logs := Line.of_inv Devm.logs (by line_inv) harg0
      _ = s10.logs := Ninst.Hinv.inv (f := Devm.logs) hevent
  rcases of_run_prepend (logWith 2 0 1) _ run with ⟨s11, hlog, hstop⟩
  rcases of_logWith201_val hp10 hlog with ⟨hp11, hlogs⟩
  rw [hread] at hlogs
  have hlogsStop : s11.logs = r.logs :=
    Func.of_inv Devm.logs Devm.logs (by
      unfold Func.stop
      func_inv) hstop
  refine ⟨hstorage, ?_, houtput.symm⟩
  calc
    r.logs = s11.logs := hlogsStop.symm
    _ = s10.logs ++
        [permitApprovalLog sevm.currentTarget owner spender value] := by
      simpa only [permitApprovalLog] using hlogs
    _ = s.logs ++
        [permitApprovalLog sevm.currentTarget owner spender value] := by
      rw [hlogsTo10]

private theorem permit_success_not_expired_core (dp : DeployParams)
    {sevm : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s (permit dp) r) :
    ¬ sevm.benvStat.time > Sevm.argWord sevm 3 := by
  unfold permit at run
  refine run_prepend_elim _ (arg 3 ++ [timestamp, gt]) ?_ run
  intro mid hline hbranch
  rcases of_run_append (arg 3) hline with ⟨s0, harg, hrest⟩
  have hp0 : Sevm.argWord sevm 3 :: [] <<+ s0.stack :=
    prefix_of_arg nil_pref harg
  rcases Line.of_run_cons hrest with ⟨s1, htime, hrest⟩
  have hp1 : sevm.benvStat.time :: Sevm.argWord sevm 3 :: [] <<+
      s1.stack := prefix_of_timestamp hp0 htime
  rcases Line.of_run_cons hrest with ⟨s2, hgt, hnil⟩
  cases hnil
  have hpflag :
      (sevm.benvStat.time >? Sevm.argWord sevm 3) :: [] <<+ mid.stack :=
    prefix_of_gt hgt hp1
  rcases of_run_branch hbranch with
      ⟨s1, hpop, hsuccess⟩ |
      ⟨w, s1, s2, hnz, hpop, hburn, hcall⟩
  · have hflag := (popBurn_pref hpop hpflag).1
    rw [B256.gtCheck] at hflag
    by_contra hgt
    rw [if_pos hgt] at hflag
    exact B256.zero_ne_one hflag
  · rcases of_run_call hcall with ⟨f, s3, hget, hcallBurn, hrev⟩
    have hf : f = expiredPermitError := by
      simpa [weth10Aux, expiredPermitErrorSlot] using hget.symm
    subst f
    exact absurd hrev Func.not_run_revWith

/-! ## Selected-body success composition -/

lemma permit_mem_weth10Funcs (dp : DeployParams) :
    (permitSelector, nonpayable (permit dp)) ∈ weth10Funcs dp := by
  simp [weth10Funcs, permitSelector]

/-- A successful canonical selected `permit` body has the exact ERC-2612
effect.  The signed nonce is the pre-state nonce, the nonce increment precedes
the allowance write, ECRECOVER's returned word is exactly the owner, one
canonical `Approval` log is appended, and the enclosing output is unchanged.

This theorem is deliberately at selected-body altitude.  The compiled public
selector and nonpayable ingress are lifted below, while failed executions use
Jaune's error/settlement semantics rather than `Func.Run`, which represents
successful bodies only. -/
theorem permit_selected_success_effect (dp : DeployParams)
    {sevm : Sevm} {s r : Devm}
    {owner spender : Adr} {value deadline : B256}
    {v : UInt8} {sigR sigS : B256} {xs : Stack} {img : Bytes}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 1) = true)
    (hnodeleg : getDelegatedCodeAddress (s.getCode 1) = none)
    (hdec : DecodesPermit sevm owner spender value deadline v sigR sigS)
    (hp : xs <<+ s.stack) (hwf : Mem.Wf s.memory)
    (hr : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (permit dp) r) :
    let nonce := Devm.getStorVal s sevm.currentTarget (nonceKey owner)
    let domain := permitDomainSeparator dp sevm.benvStat.chainId.toB256
      sevm.currentTarget
    let structHash := permitStructHash owner spender value nonce deadline
    let digest := permitDigestValue domain structHash
    ¬ sevm.benvStat.time > deadline ∧
      permitRecoveredSignerWord digest v sigR sigS = owner.toB256 ∧
      Devm.getStor r sevm.currentTarget =
        ((Devm.getStor s sevm.currentTarget).set
          (nonceKey owner) (nonce + 1)).set
            (allowanceKey owner spender) value ∧
      r.logs = s.logs ++
        [permitApprovalLog sevm.currentTarget owner spender value] ∧
      r.output = s.output := by
  dsimp only
  have hdeadline := permit_success_not_expired_core dp run
  rw [argWord_three_of_decodesPermit hdec] at hdeadline
  rcases of_permitToRecover dp hdec hp hwf hr run with
    ⟨preRecover, hpRecover, hstorRecover, hcodeRecover,
      hlogsRecover, houtputRecover, hwfRecover, hrRecover, recoverRun⟩
  rw [permitRecover_eq] at recoverRun
  rcases of_run_prepend permitDigest _ recoverRun with
    ⟨digestState, digestRun, recoverRun⟩
  rcases of_permitDigest hpRecover hwfRecover hrRecover digestRun with
    ⟨hpDigest, hwfDigest, hrDigest, hcodeDigest⟩
  have hnodelegDigest :
      getDelegatedCodeAddress (digestState.getCode 1) = none := by
    rw [congrFun hcodeDigest 1, congrFun hcodeRecover 1]
    exact hnodeleg
  have hstorDigest : Devm.getStor preRecover =
      Devm.getStor digestState :=
    Line.of_inv Devm.getStor (by
      unfold permitDigest pushList
      line_inv) digestRun
  have hlogsDigest : preRecover.logs = digestState.logs :=
    Line.of_inv Devm.logs (by
      unfold permitDigest pushList
      line_inv) digestRun
  have houtputDigest : preRecover.output = digestState.output :=
    Line.of_inv Devm.output (by
      unfold permitDigest pushList
      line_inv) digestRun
  rcases of_run_prepend recoverPermitSigner _ recoverRun with
    ⟨signerState, signerRun, guardsRun⟩
  rcases of_recoverPermitSigner hpre hnodelegDigest hdec hpDigest
      hwfDigest hrDigest signerRun with
    ⟨signer, out, hpSigner, hwfSigner, hrSigner, hsigner, hrecover⟩
  rcases of_permitSignerGuards_frame dp hdec hpSigner guardsRun with
    ⟨hsignerNonzero, hsignerOwner, approveState, hpApprove,
      hstorGuards, hmemoryGuards, hlogsGuards, houtputGuards, approveRun⟩
  rcases hrecover with hzero | ⟨hout, hstorSigner, hlogsSigner, houtputSigner⟩
  · exact (hsignerNonzero hzero).elim
  · have hwfApprove : Mem.Wf approveState.memory := by
      rw [hmemoryGuards]
      exact hwfSigner
    have hrApprove : Mem.Reads approveState.memory
        (Bytes.writeAt
          (permitRecoverMemoryImage
            (permitDigestMemoryImage
              (permitDomainDispatchMemoryImage dp
                sevm.benvStat.chainId.toB256 sevm.currentTarget
                (permitStructMemoryImage img owner spender value
                  (Devm.getStorVal s sevm.currentTarget (nonceKey owner))
                  deadline))
              (permitDomainSeparator dp sevm.benvStat.chainId.toB256
                sevm.currentTarget)
              (permitStructHash owner spender value
                (Devm.getStorVal s sevm.currentTarget (nonceKey owner))
                deadline))
            (permitDigestValue
              (permitDomainSeparator dp sevm.benvStat.chainId.toB256
                sevm.currentTarget)
              (permitStructHash owner spender value
                (Devm.getStorVal s sevm.currentTarget (nonceKey owner))
                deadline))
            v sigR sigS)
          128 (out.take 32)) := by
      rw [hmemoryGuards]
      exact hrSigner
    rcases approvePermit_effect hdec hpApprove hwfApprove hrApprove
        approveRun with ⟨hstorApprove, hlogsApprove, houtputApprove⟩
    have hcanonicalSigner :
        permitRecoveredSignerWord
          (permitDigestValue
            (permitDomainSeparator dp sevm.benvStat.chainId.toB256
              sevm.currentTarget)
            (permitStructHash owner spender value
              (Devm.getStorVal s sevm.currentTarget (nonceKey owner))
              deadline))
          v sigR sigS = owner.toB256 := by
      unfold permitRecoveredSignerWord
      rw [← hout, ← hsigner, hsignerOwner]
    refine ⟨hdeadline, hcanonicalSigner, ?_, ?_, ?_⟩
    · calc
        Devm.getStor r sevm.currentTarget =
            (Devm.getStor approveState sevm.currentTarget).set
              (allowanceKey owner spender) value := hstorApprove
        _ = (Devm.getStor signerState sevm.currentTarget).set
              (allowanceKey owner spender) value := by
            rw [congrFun hstorGuards sevm.currentTarget]
        _ = (Devm.getStor digestState sevm.currentTarget).set
              (allowanceKey owner spender) value := by
            rw [congrFun hstorSigner sevm.currentTarget]
        _ = (Devm.getStor preRecover sevm.currentTarget).set
              (allowanceKey owner spender) value := by
            rw [congrFun hstorDigest.symm sevm.currentTarget]
        _ = ((Devm.getStor s sevm.currentTarget).set
              (nonceKey owner)
                (Devm.getStorVal s sevm.currentTarget (nonceKey owner) + 1)).set
              (allowanceKey owner spender) value := by
            rw [hstorRecover]
    · calc
        r.logs = approveState.logs ++
            [permitApprovalLog sevm.currentTarget owner spender value] :=
          hlogsApprove
        _ = signerState.logs ++
            [permitApprovalLog sevm.currentTarget owner spender value] := by
          rw [hlogsGuards]
        _ = digestState.logs ++
            [permitApprovalLog sevm.currentTarget owner spender value] := by
          rw [hlogsSigner]
        _ = preRecover.logs ++
            [permitApprovalLog sevm.currentTarget owner spender value] := by
          rw [hlogsDigest]
        _ = s.logs ++
            [permitApprovalLog sevm.currentTarget owner spender value] := by
          rw [hlogsRecover]
    · calc
        r.output = approveState.output := houtputApprove
        _ = signerState.output := houtputGuards
        _ = digestState.output := houtputSigner
        _ = preRecover.output := houtputDigest.symm
        _ = s.output := houtputRecover

/-- A successful canonical selected `permit` body cannot touch WETH10's
temporary flash-mint accounting slot.  This is a direct consequence of the
exact nonce-then-allowance storage image above and the disjoint tagged-key
regions. -/
theorem permit_selected_success_preserves_flashMinted (dp : DeployParams)
    {sevm : Sevm} {s r : Devm}
    {owner spender : Adr} {value deadline : B256}
    {v : UInt8} {sigR sigS : B256} {xs : Stack} {img : Bytes}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 1) = true)
    (hnodeleg : getDelegatedCodeAddress (s.getCode 1) = none)
    (hdec : DecodesPermit sevm owner spender value deadline v sigR sigS)
    (hp : xs <<+ s.stack) (hwf : Mem.Wf s.memory)
    (hr : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (permit dp) r) :
    Devm.getStorVal r sevm.currentTarget flashMintedSlot =
      Devm.getStorVal s sevm.currentTarget flashMintedSlot := by
  have hsuccess := permit_selected_success_effect dp hpre hnodeleg hdec hp
    hwf hr run
  dsimp only at hsuccess
  rcases hsuccess with ⟨_, _, hstor, _, _⟩
  change (Devm.getStor r sevm.currentTarget).get flashMintedSlot =
    (Devm.getStor s sevm.currentTarget).get flashMintedSlot
  rw [hstor,
    Stor.get_set_ne _ (allowanceKey_ne_flashMintedSlot owner spender) _,
    Stor.get_set_ne _ (nonceKey_ne_flashMintedSlot owner) _]

/-- Public compiled-selector lift of `permit_selected_success_effect`.
Canonical calldata fixes every signed word; selector ingress and the
nonpayable wrapper preserve the entry world/log image and force zero call
value.  With an initially empty output field, successful permit returns empty
output exactly. -/
theorem permit_exec_success_effect (dp : DeployParams)
    {sevm : Sevm} {pre post : Devm}
    {owner spender : Adr} {value deadline : B256}
    {v : UInt8} {sigR sigS : B256} {img : Bytes}
    (hprecomp : decide (sevm.benvStat.rules.isPrecomp 1) = true)
    (hnodeleg : getDelegatedCodeAddress (pre.getCode 1) = none)
    (hdec : DecodesPermit sevm owner spender value deadline v sigR sigS)
    (hwf : Mem.Wf pre.memory) (hr : Mem.Reads pre.memory img)
    (houtputEmpty : pre.output = [])
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : some sevm.code.toList = Prog.compile (weth10 dp))
    (hsel : Sevm.selector sevm = permitSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0) :
    let nonce := Devm.getStorVal pre sevm.currentTarget (nonceKey owner)
    let domain := permitDomainSeparator dp sevm.benvStat.chainId.toB256
      sevm.currentTarget
    let structHash := permitStructHash owner spender value nonce deadline
    let digest := permitDigestValue domain structHash
    sevm.value = 0 ∧
      ¬ sevm.benvStat.time > deadline ∧
      permitRecoveredSignerWord digest v sigR sigS = owner.toB256 ∧
      Devm.getStor post sevm.currentTarget =
        ((Devm.getStor pre sevm.currentTarget).set
          (nonceKey owner) (nonce + 1)).set
            (allowanceKey owner spender) value ∧
      post.logs = pre.logs ++
        [permitApprovalLog sevm.currentTarget owner spender value] ∧
      post.output = [] := by
  dsimp only
  rcases exec_enters_weth10Nonpayable_logs exc hcode hsel hnonempty
      (permit_mem_weth10Funcs dp) with
    ⟨mid, hvalue, hstorEntry, hbalEntry, hcodeEntry, hmemoryEntry,
      hlogsEntry, houtputEntry, run⟩
  have hnodelegMid : getDelegatedCodeAddress (mid.getCode 1) = none := by
    rw [congrFun hcodeEntry 1]
    exact hnodeleg
  have hwfMid : Mem.Wf mid.memory := by
    rw [hmemoryEntry]
    exact hwf
  have hrMid : Mem.Reads mid.memory img := by
    rw [hmemoryEntry]
    exact hr
  have hsuccess := permit_selected_success_effect dp hprecomp hnodelegMid
    hdec nil_pref hwfMid hrMid run
  dsimp only at hsuccess
  rcases hsuccess with
    ⟨hdeadline, hsigner, hstor, hlogs, houtput⟩
  have hnonce : Devm.getStorVal mid sevm.currentTarget (nonceKey owner) =
      Devm.getStorVal pre sevm.currentTarget (nonceKey owner) := by
    change (Devm.getStor mid sevm.currentTarget).get (nonceKey owner) =
      (Devm.getStor pre sevm.currentTarget).get (nonceKey owner)
    rw [hstorEntry]
  rw [hnonce] at hsigner hstor
  refine ⟨hvalue, hdeadline, hsigner, ?_, ?_, ?_⟩
  · simpa only [congrFun hstorEntry sevm.currentTarget] using hstor
  · simpa only [hlogsEntry] using hlogs
  · calc
      post.output = mid.output := houtput
      _ = pre.output := houtputEntry
      _ = [] := houtputEmpty

/-- Public compiled-selector lift of flash-slot preservation.  Unlike the
full success image, this corollary needs no premise about the incoming output
field: selector/nonpayable ingress and the selected permit body both preserve
the slot independently of return-data bookkeeping. -/
theorem permit_exec_success_preserves_flashMinted (dp : DeployParams)
    {sevm : Sevm} {pre post : Devm}
    {owner spender : Adr} {value deadline : B256}
    {v : UInt8} {sigR sigS : B256} {img : Bytes}
    (hprecomp : decide (sevm.benvStat.rules.isPrecomp 1) = true)
    (hnodeleg : getDelegatedCodeAddress (pre.getCode 1) = none)
    (hdec : DecodesPermit sevm owner spender value deadline v sigR sigS)
    (hwf : Mem.Wf pre.memory) (hr : Mem.Reads pre.memory img)
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : some sevm.code.toList = Prog.compile (weth10 dp))
    (hsel : Sevm.selector sevm = permitSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0) :
    Devm.getStorVal post sevm.currentTarget flashMintedSlot =
      Devm.getStorVal pre sevm.currentTarget flashMintedSlot := by
  rcases exec_enters_weth10Nonpayable_logs exc hcode hsel hnonempty
      (permit_mem_weth10Funcs dp) with
    ⟨mid, _, hstorEntry, _, hcodeEntry, hmemoryEntry, _, _, run⟩
  have hnodelegMid : getDelegatedCodeAddress (mid.getCode 1) = none := by
    rw [congrFun hcodeEntry 1]
    exact hnodeleg
  have hwfMid : Mem.Wf mid.memory := by
    rw [hmemoryEntry]
    exact hwf
  have hrMid : Mem.Reads mid.memory img := by
    rw [hmemoryEntry]
    exact hr
  have hflash := permit_selected_success_preserves_flashMinted dp hprecomp
    hnodelegMid hdec nil_pref hwfMid hrMid run
  calc
    Devm.getStorVal post sevm.currentTarget flashMintedSlot =
        Devm.getStorVal mid sevm.currentTarget flashMintedSlot := hflash
    _ = Devm.getStorVal pre sevm.currentTarget flashMintedSlot := by
      change (Devm.getStor mid sevm.currentTarget).get flashMintedSlot =
        (Devm.getStor pre sevm.currentTarget).get flashMintedSlot
      rw [hstorEntry]

theorem permit_success_not_expired (dp : DeployParams)
    {sevm : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s (permit dp) r) :
    ¬ sevm.benvStat.time > Sevm.argWord sevm 3 :=
  permit_success_not_expired_core dp run

/-! ## Canonical failure exclusion and exact rollback

`Func.Run` and successful `Exec` witnesses cannot exist for an expired
canonical call or for a canonical ECRECOVER image different from the owner.
The exact-payload lemmas then expose the two locked error branches at compiled
guard altitude.  The final corollaries transport a supplied full-program
compiled revert through message settlement; they intentionally do not pretend
that a guard-tail walk is itself an entry-to-guard walk. -/

/-- Expiration excludes a successful selected permit body.  This is the
strict comparison used by the runtime, so deadline equality is not excluded. -/
theorem permit_selected_expired_no_success (dp : DeployParams)
    {sevm : Sevm} {s r : Devm}
    {owner spender : Adr} {value deadline : B256}
    {v : UInt8} {sigR sigS : B256}
    (hdec : DecodesPermit sevm owner spender value deadline v sigR sigS)
    (hexpired : sevm.benvStat.time > deadline) :
    ¬ Func.Run ((weth10 dp).main :: weth10Aux) sevm s (permit dp) r := by
  intro run
  have hlive := permit_success_not_expired dp run
  rw [argWord_three_of_decodesPermit hdec] at hlive
  exact hlive hexpired

/-- Public compiled-selector form of deadline precedence: an expired
canonical permit cannot return successfully, independently of nonce, domain,
or precompile state. -/
theorem permit_exec_expired_no_success (dp : DeployParams)
    {sevm : Sevm} {pre post : Devm}
    {owner spender : Adr} {value deadline : B256}
    {v : UInt8} {sigR sigS : B256}
    (hdec : DecodesPermit sevm owner spender value deadline v sigR sigS)
    (hexpired : sevm.benvStat.time > deadline)
    (hcode : some sevm.code.toList = Prog.compile (weth10 dp))
    (hsel : Sevm.selector sevm = permitSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0) :
    Exec 0 sevm pre (.ok post) → False := by
  intro exc
  rcases exec_enters_weth10Nonpayable_logs exc hcode hsel hnonempty
      (permit_mem_weth10Funcs dp) with
    ⟨mid, _, _, _, _, _, _, _, run⟩
  exact permit_selected_expired_no_success dp hdec hexpired run

/-- A canonical recovered word unequal to the owner excludes a successful
selected permit body.  The word is the exact deterministic precompile image,
not an abstract signer premise. -/
theorem permit_selected_invalid_no_success (dp : DeployParams)
    {sevm : Sevm} {s r : Devm}
    {owner spender : Adr} {value deadline : B256}
    {v : UInt8} {sigR sigS : B256} {xs : Stack} {img : Bytes}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 1) = true)
    (hnodeleg : getDelegatedCodeAddress (s.getCode 1) = none)
    (hdec : DecodesPermit sevm owner spender value deadline v sigR sigS)
    (hp : xs <<+ s.stack) (hwf : Mem.Wf s.memory)
    (hr : Mem.Reads s.memory img)
    (hinvalid :
      permitRecoveredSignerWord
        (permitDigestValue
          (permitDomainSeparator dp sevm.benvStat.chainId.toB256
            sevm.currentTarget)
          (permitStructHash owner spender value
            (Devm.getStorVal s sevm.currentTarget (nonceKey owner)) deadline))
        v sigR sigS ≠ owner.toB256) :
    ¬ Func.Run ((weth10 dp).main :: weth10Aux) sevm s (permit dp) r := by
  intro run
  have hsuccess := permit_selected_success_effect dp hpre hnodeleg hdec hp
    hwf hr run
  dsimp only at hsuccess
  exact hinvalid hsuccess.2.1

/-- Public compiled-selector form of invalid-signature exclusion. -/
theorem permit_exec_invalid_no_success (dp : DeployParams)
    {sevm : Sevm} {pre post : Devm}
    {owner spender : Adr} {value deadline : B256}
    {v : UInt8} {sigR sigS : B256} {img : Bytes}
    (hprecomp : decide (sevm.benvStat.rules.isPrecomp 1) = true)
    (hnodeleg : getDelegatedCodeAddress (pre.getCode 1) = none)
    (hdec : DecodesPermit sevm owner spender value deadline v sigR sigS)
    (hwf : Mem.Wf pre.memory) (hr : Mem.Reads pre.memory img)
    (hinvalid :
      permitRecoveredSignerWord
        (permitDigestValue
          (permitDomainSeparator dp sevm.benvStat.chainId.toB256
            sevm.currentTarget)
          (permitStructHash owner spender value
            (Devm.getStorVal pre sevm.currentTarget (nonceKey owner)) deadline))
        v sigR sigS ≠ owner.toB256)
    (hcode : some sevm.code.toList = Prog.compile (weth10 dp))
    (hsel : Sevm.selector sevm = permitSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0) :
    Exec 0 sevm pre (.ok post) → False := by
  intro exc
  rcases exec_enters_weth10Nonpayable_logs exc hcode hsel hnonempty
      (permit_mem_weth10Funcs dp) with
    ⟨mid, _, hstorEntry, _, hcodeEntry, hmemoryEntry, _, _, run⟩
  have hnodelegMid : getDelegatedCodeAddress (mid.getCode 1) = none := by
    rw [congrFun hcodeEntry 1]
    exact hnodeleg
  have hwfMid : Mem.Wf mid.memory := by
    rw [hmemoryEntry]
    exact hwf
  have hrMid : Mem.Reads mid.memory img := by
    rw [hmemoryEntry]
    exact hr
  have hnonce : Devm.getStorVal mid sevm.currentTarget (nonceKey owner) =
      Devm.getStorVal pre sevm.currentTarget (nonceKey owner) := by
    change (Devm.getStor mid sevm.currentTarget).get (nonceKey owner) =
      (Devm.getStor pre sevm.currentTarget).get (nonceKey owner)
    rw [hstorEntry]
  apply permit_selected_invalid_no_success dp hprecomp hnodelegMid hdec
    nil_pref hwfMid hrMid
  · simpa only [hnonce] using hinvalid
  · exact run

/-- The reached expiry guard has the exact locked ABI payload and gas delta. -/
theorem permitExpiredGuard_runCompiledTo {dp : DeployParams} {sevm : Sevm}
    {base : Devm} {G : Nat} {w : B256} {stack : List B256} {img : Bytes}
    {otherwise : Func}
    (h_ne : w ≠ 0)
    (hwf : Mem.Wf base.memory) (hr : Mem.Reads base.memory img)
    (halign : base.memory.size % 32 = 0)
    (h_blob : (errorData "WETH: Expired permit").length < 2 ^ 256)
    (h_words : 32 *
      (bytesWords (errorData "WETH: Expired permit")).length < 2 ^ 256)
    (h_room : stack.length < 1022) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨w :: stack, base.memory,
        G + errorGuardCost base "WETH: Expired permit"⟩)
      ((.call expiredPermitErrorSlot) <?> otherwise)
      (.error (.revert,
        (base.setMach ⟨stack,
          Mem.writeStoresRev base.memory
            (bytesWords (errorData "WETH: Expired permit")).zipIdx,
          G⟩).withOutput (errorData "WETH: Expired permit"))) := by
  simpa only [LockedError.reason, LockedError.slot] using
    (lockedErrorGuard_runCompiledTo (dp := dp) (sevm := sevm)
      (base := base) (G := G) (w := w) (stack := stack) (img := img)
      (otherwise := otherwise) .expiredPermit h_ne hwf hr halign
      h_blob h_words h_room)

/-- Either reached signer guard has the exact locked invalid-permit ABI
payload and gas delta. -/
theorem permitInvalidGuard_runCompiledTo {dp : DeployParams} {sevm : Sevm}
    {base : Devm} {G : Nat} {w : B256} {stack : List B256} {img : Bytes}
    {otherwise : Func}
    (h_ne : w ≠ 0)
    (hwf : Mem.Wf base.memory) (hr : Mem.Reads base.memory img)
    (halign : base.memory.size % 32 = 0)
    (h_blob : (errorData "WETH: invalid permit").length < 2 ^ 256)
    (h_words : 32 *
      (bytesWords (errorData "WETH: invalid permit")).length < 2 ^ 256)
    (h_room : stack.length < 1022) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨w :: stack, base.memory,
        G + errorGuardCost base "WETH: invalid permit"⟩)
      ((.call invalidPermitErrorSlot) <?> otherwise)
      (.error (.revert,
        (base.setMach ⟨stack,
          Mem.writeStoresRev base.memory
            (bytesWords (errorData "WETH: invalid permit")).zipIdx,
          G⟩).withOutput (errorData "WETH: invalid permit"))) := by
  simpa only [LockedError.reason, LockedError.slot] using
    (lockedErrorGuard_runCompiledTo (dp := dp) (sevm := sevm)
      (base := base) (G := G) (w := w) (stack := stack) (img := img)
      (otherwise := otherwise) .invalidPermit h_ne hwf hr halign
      h_blob h_words h_room)

/-- From the selected `permit` body entry, an expired canonical deadline
reaches the locked expiry reason before the nonce prefix.  The final world is
therefore the entry world; only error-payload memory, output, and the stated
gas delta differ.  Dispatcher and nonpayable-prefix cost are intentionally not
included in this selected-body theorem. -/
theorem permitExpired_selected_runCompiledTo
    {dp : DeployParams} {sevm : Sevm} {base : Devm}
    {owner spender : Adr} {value deadline : B256}
    {v : UInt8} {sigR sigS : B256}
    {G : Nat} {stack : List B256} {img : Bytes}
    (hdec : DecodesPermit sevm owner spender value deadline v sigR sigS)
    (hexpired : sevm.benvStat.time > deadline)
    (hwf : Mem.Wf base.memory) (hr : Mem.Reads base.memory img)
    (halign : base.memory.size % 32 = 0)
    (h_blob : (errorData "WETH: Expired permit").length < 2 ^ 256)
    (h_words : 32 *
      (bytesWords (errorData "WETH: Expired permit")).length < 2 ^ 256)
    (h_room : stack.length < 1020) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨stack, base.memory,
        (G + errorGuardCost base "WETH: Expired permit") + 11⟩)
      (permit dp)
      (.error (.revert,
        (base.setMach ⟨stack,
          Mem.writeStoresRev base.memory
            (bytesWords (errorData "WETH: Expired permit")).zipIdx,
          G⟩).withOutput (errorData "WETH: Expired permit"))) := by
  rw [permit_eq_deadlineGuard]
  func_run (4) [1]
  all_goals try {
    simp only [Devm.stack_setMach, List.length_cons] at *
    omega }
  all_goals try omega
  · change sevm.benvStat.time >? Sevm.argWord sevm 3 = 1
    rw [argWord_three_of_decodesPermit hdec]
    exact permitDeadlineFlag_expired hexpired
  · exact errorGuard_runCompiledTo (expiredPermitError_lookup dp)
      (by decide) rfl hwf hr halign h_blob h_words (by
        simp only [Devm.gasLeft_setMach, errorGuardCost, errorCallCost,
          errorBodyCost, Devm.extCost, Devm.memory_setMach]
        omega) (by
        simp only [Devm.stack_setMach, List.length_cons]
        omega)

/-- At the selected signer-policy tail, a zero ECRECOVER word takes the first
invalid-permit guard with the exact locked payload.  The earlier digest,
precompile, and nonce prefix are outside this tail theorem. -/
theorem permitSignerZero_runCompiledTo
    {dp : DeployParams} {sevm : Sevm} {base : Devm}
    {G : Nat} {stack : List B256} {img : Bytes}
    (hwf : Mem.Wf base.memory) (hr : Mem.Reads base.memory img)
    (halign : base.memory.size % 32 = 0)
    (h_blob : (errorData "WETH: invalid permit").length < 2 ^ 256)
    (h_words : 32 *
      (bytesWords (errorData "WETH: invalid permit")).length < 2 ^ 256)
    (h_room : stack.length < 1021) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨0 :: stack, base.memory,
        (G + errorGuardCost base "WETH: invalid permit") + 6⟩)
      permitSignerGuards
      (.error (.revert,
        (base.setMach ⟨0 :: stack,
          Mem.writeStoresRev base.memory
            (bytesWords (errorData "WETH: invalid permit")).zipIdx,
          G⟩).withOutput (errorData "WETH: invalid permit"))) := by
  unfold permitSignerGuards
  func_run (2) [1]
  all_goals try {
    simp only [Devm.stack_setMach, List.length_cons] at *
    omega }
  · exact errorGuard_runCompiledTo (invalidPermitError_lookup dp)
      (by decide) rfl hwf hr halign h_blob h_words (by
        simp only [Devm.gasLeft_setMach, errorGuardCost, errorCallCost,
          errorBodyCost, Devm.extCost, Devm.memory_setMach]
        omega) (by
        simp only [Devm.stack_setMach, List.length_cons]
        omega)

/-- An exact full-program expiry walk settles with the locked payload and
restores persistent and transient state. -/
theorem permitExpired_rollback_of_runCompiledTo
    {dp : DeployParams} {msg : Msg} {benv : Benv} {xl : Xlot}
    {out d : Devm}
    (h_pm : ProcessMessage msg xl (.ok out))
    (h_fill : Xlot.Filled xl)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles &&
        decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_code : some (initSevm (msg.withBenv benv)).code.toList =
      (weth10 dp).compile)
    (h_run : Prog.RunCompiledTo (initSevm (msg.withBenv benv))
      (initDevm (msg.withBenv benv)) (weth10 dp)
      (.error (.revert,
        d.withOutput (errorData "WETH: Expired permit")))) :
    out.error = some .revert ∧
      out.output = errorData "WETH: Expired permit" ∧
      out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage := by
  exact rollback_errorData_of_weth10_runCompiledTo
    h_pm h_fill h_bt h_prec h_code h_run

/-- An exact full-program invalid-signature walk rolls back the tentative
nonce increment and every other persistent/transient change, while retaining
the locked invalid-permit payload. -/
theorem permitInvalid_rollback_of_runCompiledTo
    {dp : DeployParams} {msg : Msg} {benv : Benv} {xl : Xlot}
    {out d : Devm}
    (h_pm : ProcessMessage msg xl (.ok out))
    (h_fill : Xlot.Filled xl)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles &&
        decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_code : some (initSevm (msg.withBenv benv)).code.toList =
      (weth10 dp).compile)
    (h_run : Prog.RunCompiledTo (initSevm (msg.withBenv benv))
      (initDevm (msg.withBenv benv)) (weth10 dp)
      (.error (.revert,
        d.withOutput (errorData "WETH: invalid permit")))) :
    out.error = some .revert ∧
      out.output = errorData "WETH: invalid permit" ∧
      out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage := by
  exact rollback_errorData_of_weth10_runCompiledTo
    h_pm h_fill h_bt h_prec h_code h_run

end Weth10

end Blanc
