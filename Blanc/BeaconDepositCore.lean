import Blanc.BeaconDepositModel
import Blanc.RevertPayload

/-!
# Beacon deposit compiled-port vocabulary

Contract-local storage, selector, ABI, event, and error vocabulary for Blanc's
own BeaconDeposit artifact.  The pure model remains the specification; none of
the definitions below changes it or defines decoding in terms of the program
that will consume the decoded values.
-/

namespace Blanc.BeaconDeposit

open Jaune

/-! ## Concrete storage layout and total projection -/

def branchBase : B256 := 0x100
def depositCountSlot : B256 := 0x200
def zeroHashBase : B256 := 0x300

def branchSlot (height : Nat) : B256 :=
  Nat.toB256 (0x100 + height)

def zeroHashSlot (height : Nat) : B256 :=
  Nat.toB256 (0x300 + height)

/-- Total projection from every concrete storage map to the model state.
Constructor correctness, the count bound, the model invariant, and the
zero-hash region are deliberately separate predicates. -/
def accOfStor (stor : Stor) : Acc :=
  { branch := fun height =>
      if height < 32 then stor.get (branchSlot height) else 0
    count := (stor.get depositCountSlot).toNat }

@[simp] theorem accOfStor_branch_of_lt (stor : Stor) (height : Nat)
    (h : height < 32) :
    (accOfStor stor).branch height = stor.get (branchSlot height) := by
  simp [accOfStor, h]

@[simp] theorem accOfStor_branch_of_ge (stor : Stor) (height : Nat)
    (h : 32 ≤ height) :
    (accOfStor stor).branch height = 0 := by
  simp [accOfStor, Nat.not_lt.mpr h]

@[simp] theorem accOfStor_count (stor : Stor) :
    (accOfStor stor).count = (stor.get depositCountSlot).toNat := rfl

/-- The constructor-owned zero-hash region is canonical through depth 31. -/
def ZeroHashesCorrect (stor : Stor) : Prop :=
  ∀ height, height < 32 →
    stor.get (zeroHashSlot height) = zeroHash Bytes.sha256 height

/-! ## ABI identities -/

def supportsInterfaceSelector : B256 :=
  selector "supportsInterface" [.bytes 4]

def depositSelector : B256 :=
  selector "deposit" [.dynBytes, .dynBytes, .dynBytes, .bytes 32]

def getDepositCountSelector : B256 :=
  selector "get_deposit_count" []

def getDepositRootSelector : B256 :=
  selector "get_deposit_root" []

def beaconSelectors : List B256 :=
  [supportsInterfaceSelector, depositSelector,
    getDepositCountSelector, getDepositRootSelector]

def erc165InterfaceId : B256 := 0x01ffc9a7
def depositInterfaceId : B256 := 0x85640907

def erc165InterfaceIdBytes : Bytes :=
  [0x01, 0xff, 0xc9, 0xa7]

def depositInterfaceIdBytes : Bytes :=
  [0x85, 0x64, 0x09, 0x07]

def depositEventTopic : B256 :=
  signatureHash "DepositEvent"
    [.dynBytes, .dynBytes, .dynBytes, .dynBytes, .dynBytes]

/-! ## Independent dynamic-calldata boundary -/

/-- A 32-byte big-endian word read from a byte string with EVM-style zero
padding.  This is an independent data function, not a projection of a Blanc
instruction run. -/
def calldataWord (data : Bytes) (offset : Nat) : B256 :=
  Bytes.toB256 (data.sliceD offset 32 0)

def dynamicOffset (data : Bytes) (head : Nat) : Nat :=
  (calldataWord data (4 + 32 * head)).toNat

def dynamicLength (data : Bytes) (head : Nat) : Nat :=
  (calldataWord data (4 + dynamicOffset data head)).toNat

def dynamicPayload (data : Bytes) (head : Nat) : Bytes :=
  data.sliceD (36 + dynamicOffset data head) (dynamicLength data head) 0

/-- The frozen machine boundary for one dynamic `bytes` tail.  Offset and
length words are restricted to 32 bits, the complete length word must exist,
and the whole padded payload must be in bounds. -/
def DynamicTailDecodable (data : Bytes) (head : Nat) : Prop :=
  let offset := dynamicOffset data head
  let length := dynamicLength data head
  offset < 2 ^ 32 ∧
    36 + offset ≤ data.length ∧
    length < 2 ^ 32 ∧
    36 + offset + ceil32 length ≤ data.length

/-- A complete decoded deposit call.  All three structural tail checks are
members of this single predicate, so no source-level length guard can hide a
malformed later tail. -/
structure DepositAbiDecodable
    (data pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) : Prop where
  head : 132 ≤ data.length
  pubkeyTail : DynamicTailDecodable data 0
  withdrawalCredentialsTail : DynamicTailDecodable data 1
  signatureTail : DynamicTailDecodable data 2
  pubkey_eq : dynamicPayload data 0 = pubkey
  withdrawalCredentials_eq : dynamicPayload data 1 = withdrawalCredentials
  signature_eq : dynamicPayload data 2 = signature
  root_eq : calldataWord data 100 = depositDataRoot

def firstDepositTailOffset : Nat := 4 * 32

def secondDepositTailOffset (pubkey : Bytes) : Nat :=
  firstDepositTailOffset + (abiBytesTail pubkey).length

def thirdDepositTailOffset
    (pubkey withdrawalCredentials : Bytes) : Nat :=
  secondDepositTailOffset pubkey +
    (abiBytesTail withdrawalCredentials).length

/-- Canonical Solidity ABI encoding of the four deposit arguments. -/
def abiDepositCall
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) : Bytes :=
  abiSelectorBytes depositSelector ++
    (Nat.toB256 firstDepositTailOffset).toBytes ++
    (Nat.toB256 (secondDepositTailOffset pubkey)).toBytes ++
    (Nat.toB256
      (thirdDepositTailOffset pubkey withdrawalCredentials)).toBytes ++
    depositDataRoot.toBytes ++
    abiBytesTail pubkey ++
    abiBytesTail withdrawalCredentials ++
    abiBytesTail signature

/-- Canonical calldata remains independent of the implementation's reads and
does not bake in the three source-level length guards. -/
def CanonicalDepositCalldata
    (data pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) : Prop :=
  data = abiDepositCall pubkey withdrawalCredentials signature
    depositDataRoot ∧
  (abiDepositCall pubkey withdrawalCredentials signature
    depositDataRoot).length < 2 ^ 32

def abiSupportsInterfaceCall (interfaceId : Bytes) : Bytes :=
  abiSelectorBytes supportsInterfaceSelector ++ interfaceId ++
    List.replicate (32 - interfaceId.length) 0

def CanonicalSupportsInterfaceCalldata
    (data interfaceId : Bytes) : Prop :=
  interfaceId.length = 4 ∧
    data = abiSupportsInterfaceCall interfaceId

/-! ## Return and event encodings -/

def abiDynamicBytesReturn (data : Bytes) : Bytes :=
  (32 : B256).toBytes ++ abiBytesTail data

def abiBoolReturn (answer : Bool) : Bytes :=
  (if answer then (1 : B256) else 0).toBytes

/-- Exact five-tail ABI image of `DepositEvent`. -/
def abiDepositEvent (event : DepositEvent) : Bytes :=
  (160 : B256).toBytes ++
    (256 : B256).toBytes ++
    (320 : B256).toBytes ++
    (384 : B256).toBytes ++
    (512 : B256).toBytes ++
    abiBytesTail event.pubkey ++
    abiBytesTail event.withdrawal_credentials ++
    abiBytesTail event.amount ++
    abiBytesTail event.signature ++
    abiBytesTail event.index

def CanonicalDepositEventData
    (event : DepositEvent) (data : Bytes) : Prop :=
  data = abiDepositEvent event

def depositEventLog (owner : Adr) (event : DepositEvent) : Log :=
  ⟨owner, [depositEventTopic], abiDepositEvent event⟩

/-! ## Source guard strings -/

/-- The eight `require` strings are exact.  The final label names the
model-only unreachable `assert(false)` arm and is never compiled as an
`Error(string)` auxiliary. -/
def reasonString : Reason → String
  | .pubkey_length => "DepositContract: invalid pubkey length"
  | .withdrawal_credentials_length =>
      "DepositContract: invalid withdrawal_credentials length"
  | .signature_length => "DepositContract: invalid signature length"
  | .value_too_low => "DepositContract: deposit value too low"
  | .value_not_gwei_multiple =>
      "DepositContract: deposit value not multiple of gwei"
  | .value_too_high => "DepositContract: deposit value too high"
  | .deposit_data_root_mismatch =>
      "DepositContract: reconstructed DepositData does not match supplied deposit_data_root"
  | .merkle_tree_full => "DepositContract: merkle tree full"
  | .assert_false => "assert(false)"

end Blanc.BeaconDeposit
