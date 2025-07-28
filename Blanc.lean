import Lean.Data.HashSet
import «Blanc».Weth

abbrev AccessList : Type := List (Adr × List B256)

instance : ToString AccessList := ⟨@List.toString _ _⟩


def longB8LToStrings (hd : String) (bs : B8L) : List String :=
  match List.chunks 31 bs with
  | [] => [hd]
  | [bs'] => [s!"{hd} : {B8L.toHex bs'}"]
  | bss => s!"{hd} :" :: bss.map (λ bs' => pad (B8L.toHex bs'))

def Lean.RBMap.toStrings {α β cmp} (m : Lean.RBMap α β cmp)
  (fmt : α × β → List String): List String :=
  let kvs := m.toArray.toList
  fork "map" (kvs.map fmt)

def String.trimLeftChar (s : String) (c : Char) : String :=
  ⟨s.data.dropWhile (c == ·)⟩

def String.trimHex (s : String) : String :=
  match s.trimLeftChar '0' with
  | "" => "0"
  | s => s

def Stor.toStrings (s : Stor) : List String :=
  let kvs := s.toArray.toList
  let kvToStrings : B256 × B256 → List String :=
    λ nb => [s!"0x{(B256.toHex nb.fst).trimHex} : 0x{(B256.toHex nb.snd).trimHex}"]
  fork "stor" (kvs.map kvToStrings)

def Option.toStrings {ξ : Type u} (f : ξ → List String): Option ξ → List String
  | none => ["none"]
  | some x => fork "some" [f x]

def AccessEntry.toStrings : (Adr × List B256) → List String
  | ⟨a, ks⟩ => fork a.toHex <| ks.map <| fun k => [k.toHex]

def AccessList.toStrings (al : AccessList) : List String :=
    fork "access list" <| al.map <| AccessEntry.toStrings

def Acct.toStrings (s : String) (a : Acct) : List String :=
  fork s [
    [s!"bal : 0x{a.bal.toHex.trimHex}"],
    [s!"nonce : 0x{a.nonce.toHex.trimHex}"],
    longB8LToStrings "code" a.code.toList,
    a.stor.toStrings
  ]

instance : ToString Acct := ⟨fun a => String.joinln (Acct.toStrings "account" a)⟩

def Wor.toStrings (w : Wor) : List String :=
  let kvs := w.toArray.toList
  let kvToStrings : Adr × Acct → List String :=
    fun x => Acct.toStrings ("0x" ++ x.fst.toHex.trimHex) x.snd
  fork "world" (kvs.map kvToStrings)

def Lean.Json.toIoList : Lean.Json → IO (List Json)
  | .arr a => return a.toList
  | _ => IO.throw "not an array"

def Lean.Json.toIoRBNode : Lean.Json → IO (RBNode String (λ _ => Json))
  | .obj r => return r
  | _ => IO.throw "not an object"

def Lean.Json.toString? : Lean.Json → Option String
  | .str s => some s
  | _ => none

def Lean.Json.toIoString : Lean.Json → IO String
  | .str s => return s
  | _ => IO.throw "not a string"

def Lean.Json.toB8L? (j : Json) : Option B8L := do
  let x ← toString? j >>= .remove0x
  (Hex.toB8L x)

def Lean.Json.toIoB8L (j : Json) : IO B8L := do
  let x ← toIoString j >>= .remove0x
  (Hex.toB8L x).toIO ""

def Lean.Json.toAdr? (j : Json) : Option Adr := do
  let x ← toString? j >>= .remove0x
  (Hex.toAdr? x)

def Lean.Json.toIoAdr (j : Json) : IO Adr := do
  let x ← toIoString j >>= .remove0x
  (Hex.toAdr? x).toIO ""

def Lean.Json.toIoAdrs (j : Json) : IO (List Adr) :=
  toIoList j >>= mapM toIoAdr

def Lean.Json.toB64? (j : Json) : Option B64:= do
  let x ← toString? j >>= .remove0x
  (Hex.toB64? x)

def Lean.Json.toIoB64 (j : Json) : IO B64 := do
  let x ← toIoString j >>= .remove0x
  (Hex.toB64? x).toIO

def Lean.Json.toB256? (j : Json) : Option B256 := do
  let x ← toString? j >>= .remove0x
  Hex.toB256? x

def Lean.Json.toIoB256 (j : Json) : IO B256 := do
  let x ← toIoString j >>= .remove0x
  (Hex.toB256? x).toIO ""

def Lean.Json.toIoB64P (j : Json) : IO B64 := do
  let x ← toIoString j >>= .remove0x
  let xs ← (Hex.toB8L x).toIO ""
  return (B8L.toB64P xs)

def Lean.Json.toIoB256P (j : Json) : IO B256 := do
  let x ← toIoString j >>= .remove0x
  let xs ← (Hex.toB8L x).toIO ""
  return (B8L.toB256P xs)

def Lean.Json.toIoAccessEntry (j : Json) : IO (Adr × List B256) := do
  let r ← toIoRBNode j
  let a ← (r.find compare "address").toIO "" >>= toIoAdr
  let ks ← (r.find compare "storageKeys").toIO "" >>= toIoList >>= mapM toIoB256P
  return ⟨a, ks⟩

def Lean.Json.toIoAccessList (j : Json) : IO AccessList := do
  toIoList j >>= mapM toIoAccessEntry


/-
class Authorization:
    """
    The authorization for a set code transaction.
    """

    chain_id: U256
    address: Address
    nonce: U64
    y_parity: U8
    r: U256
    s: U256
-/
structure Auth : Type where
  chainId : B64
  address : Adr
  nonce : B64
  yParity : Nat
  r : B256
  s : B256

inductive TxType : Type
  -- Legacy (including EIP-155)
  | zero
    (gasPrice : Nat)
  -- -- EIP-2930
  | one
    (gasPrice : Nat)
    (chainId : B64)
    (accessList : AccessList)
  -- EIP-1559
  | two
    (chainId : B64)
    (maxPriorityFee : Nat)
    (maxFee : Nat)
    (accessList : AccessList)
  -- EIP-4844
  | three
    (chainId : B64)
    (maxPriorityFee : Nat)
    (maxFee : Nat)
    (accessList : AccessList)
    (maxBlobFee : Nat)
    (blobHashes : List B256)
  | four
    (chainId : B64)
    (maxPriorityFee : Nat)
    (maxFee : Nat)
    (accessList : AccessList)
    (auths : List Auth)

structure Withdrawal : Type where
  (globalIndex : B64)
  (validatorIndex : B64)
  (recipient : Adr)
  (amount : B256)
-- structure Withdrawal : Type where
--   index : B64
--   validatorIndex: B64
--   address : Adr
--   amount : B256

structure Header : Type where
  parentHash : B256
  ommersHash : B256
  coinbase : Adr
  stateRoot : B256
  txsRoot : B256
  receiptRoot : B256
  bloom : B8L
  difficulty : Nat
  number : Nat
  gasLimit : Nat
  gasUsed : Nat
  timestamp : Nat
  extraData : B8L
  prevRandao : B256
  nonce : B64
  baseFeePerGas : Nat
  withdrawalsRoot : B256
  blobGasUsed : Nat
  excessBlobGas : Nat
  parentBeaconBlockRoot : B256
  requestsHash : Option B256

def Header.toStrings (header : Header) : List String :=
  fork "header" [
    [s!"parent hash : {header.parentHash}"],
    [s!"ommers hash : {header.ommersHash}"],
    [s!"coinbase : {header.coinbase}"],
    [s!"stateRoot : {header.stateRoot}"],
    [s!"transactions root : {header.txsRoot}"],
    [s!"receipt root : {header.receiptRoot}"],
    [s!"bloom : {header.bloom.toHex}"],
    [s!"difficulty : {header.difficulty}"],
    [s!"number : {header.number}"],
    [s!"gas limit : {header.gasLimit}"],
    [s!"gas used : {header.gasUsed}"],
    [s!"timestamp : {header.timestamp}"],
    [s!"extra data : {header.extraData.toHex}"],
    [s!"prevRandao : {header.prevRandao}"],
    [s!"nonce : {header.nonce}"],
    [s!"base fee per gas : {header.baseFeePerGas}"],
    [s!"withdrawals root : {header.withdrawalsRoot}"],
    [s!"blob gas used : {header.blobGasUsed}"],
    [s!"excess blob gas : {header.excessBlobGas}"],
    [s!"parent beacon block root : {header.parentBeaconBlockRoot}"],
    [s!"requests Hash : {header.requestsHash}"],
  ]

instance : ToString Header := ⟨String.joinln ∘ Header.toStrings⟩

def B256.toBytes (x : B256) : Bytes := x.toB8L.map B8.toByte
def B64.toBytes (x : B64) : Bytes := x.toB8L.map B8.toByte
def Adr.toBytes (adr : Adr) : Bytes := adr.toB8L.map B8.toByte

def Nat.toBytesNil (nat : Nat) : Bytes := nat.toB8L.map B8.toByte

def Header.toBLT (header : Header) : BLT :=
  BLT.list <| [
    BLT.b8s header.parentHash.toB8L,
    BLT.b8s header.ommersHash.toB8L,
    BLT.b8s header.coinbase.toB8L,
    BLT.b8s header.stateRoot.toB8L,
    BLT.b8s header.txsRoot.toB8L,
    BLT.b8s header.receiptRoot.toB8L,
    BLT.b8s header.bloom,
    BLT.b8s header.difficulty.toB8L,
    BLT.b8s header.number.toB8L,
    BLT.b8s header.gasLimit.toB8L,
    BLT.b8s header.gasUsed.toB8L,
    BLT.b8s header.timestamp.toB8L,
    BLT.b8s header.extraData,
    BLT.b8s header.prevRandao.toB8L,
    BLT.b8s header.nonce.toB8L,
    BLT.b8s header.baseFeePerGas.toB8L,
    BLT.b8s header.withdrawalsRoot.toB8L,
    BLT.b8s header.blobGasUsed.toB8L,
    BLT.b8s header.excessBlobGas.toB8L,
    BLT.b8s header.parentBeaconBlockRoot.toB8L
  ] ++
    match header.requestsHash with
    | none => []
    | some rh => [BLT.b8s rh.toB8L]

structure Tx : Type where
  (nonce : B64)
  (gas : Nat)
  (receiver : Option Adr)
  (value : Nat)
  (data : B8L)
  (v : Nat)
  (r : B8L)
  (s : B8L)
  (type : TxType)

structure Block : Type where
  header : Header
  txs : List (B8L ⊕ Tx)
  ommers : List Header
  wds : List Withdrawal

def TxType.toNat : TxType → Nat
  | .zero _ => 0
  | .one _ _ _ => 1
  | .two _ _ _ _ => 2
  | .three _ _ _ _ _ _ => 3
  | .four _ _ _ _ _ => 4

def TxType.accessList : TxType → AccessList
  | .zero _ => []
  | .one _ _ al => al
  | .two _ _ _ al => al
  | .three _ _ _ al _ _ => al
  | .four _ _ _ al _ => al

def Tx.accessList (tx : Tx) : AccessList := tx.type.accessList

def Tx.auths (tx : Tx) : List Auth :=
  match tx.type with
  | .four _ _ _ _ auths => auths
  | _ => []

def B8L.sig (bs : B8L) : B8L := List.dropWhile (· = 0) bs

def AccessList.toBLT (al : AccessList) : BLT :=
  let aux : Adr × List B256 → BLT
  | ⟨adr, words⟩ =>
    .list [.b8s adr.toB8L, .list (words.map (.b8s ∘ B256.toB8L))]
  .list (al.map aux)

def Auth.toBLT (auth : Auth) : BLT :=
  .list [
    .b8s auth.chainId.toB8L.sig,
    .b8s <| auth.address.toB8L,
    .b8s auth.nonce.toNat.toB8L,
    .b8s auth.yParity.toB8L,
    .b8s auth.r.toB8L,
    .b8s auth.s.toB8L,
  ]

def Tx.toBLT (tx : Tx) : BLT :=
  match tx.type with
  | .zero gasPrice =>
    .list [
      .b8s tx.nonce.toNat.toB8L,
      .b8s gasPrice.toB8L,
      .b8s tx.gas.toB8L,
      .b8s <| tx.receiver.rec [] Adr.toB8L,
      .b8s tx.value.toB8L,
      .b8s tx.data,
      .b8s tx.v.toB8L,
      .b8s tx.r,
      .b8s tx.s,
    ]
  | .one gasPrice chainId accessList =>
    .list [
      .b8s chainId.toB8L.sig,
      .b8s tx.nonce.toNat.toB8L,
      .b8s gasPrice.toB8L,
      .b8s tx.gas.toB8L,
      .b8s <| tx.receiver.rec [] Adr.toB8L,
      .b8s tx.value.toB8L,
      .b8s tx.data,
      accessList.toBLT,
      .b8s tx.v.toB8L,
      .b8s tx.r,
      .b8s tx.s
    ]
  | .two chainId maxPriorityFee maxFee accessList =>
    .list [
      .b8s chainId.toB8L.sig,
      .b8s tx.nonce.toNat.toB8L,
      .b8s maxPriorityFee.toB8L,
      .b8s maxFee.toB8L,
      .b8s tx.gas.toB8L,
      .b8s <| tx.receiver.rec [] Adr.toB8L,
      .b8s tx.value.toB8L,
      .b8s tx.data,
      accessList.toBLT,
      .b8s tx.v.toB8L,
      .b8s tx.r,
      .b8s tx.s
    ]
  | .three chainId maxPriorityFee maxFee accessList maxBlobFee blobHashes =>
    .list [
      .b8s chainId.toB8L.sig,
      .b8s tx.nonce.toNat.toB8L,
      .b8s maxPriorityFee.toB8L,
      .b8s maxFee.toB8L,
      .b8s tx.gas.toB8L,
      .b8s <| tx.receiver.rec [] Adr.toB8L,
      .b8s tx.value.toB8L,
      .b8s tx.data,
      accessList.toBLT,
      .b8s maxBlobFee.toB8L,
      .list <| blobHashes.map <| .b8s ∘ B256.toB8L,
      .b8s tx.v.toB8L,
      .b8s tx.r,
      .b8s tx.s
    ]
  | .four chainId maxPriorityFee maxFee accessList auths =>
    .list [
      .b8s chainId.toB8L.sig,
      .b8s tx.nonce.toNat.toB8L,
      .b8s maxPriorityFee.toB8L,
      .b8s maxFee.toB8L,
      .b8s tx.gas.toB8L,
      .b8s <| tx.receiver.rec [] Adr.toB8L,
      .b8s tx.value.toB8L,
      .b8s tx.data,
      accessList.toBLT,
      .list <| auths.map <| Auth.toBLT,
      .b8s tx.v.toB8L,
      .b8s tx.r,
      .b8s tx.s
    ]


def Auth.toStrings (auth : Auth) : List String :=
  fork
    "auth"
    [
      [s!"chain ID : {auth.chainId}"],
      [s!"address : {auth.address}"],
      [s!"nonce : {auth.nonce.toHex}"],
      [s!"y parity : {auth.yParity}"],
      [s!"r : {auth.r.toHex}"],
      [s!"s : {auth.s.toHex}"]
    ]

def Auths.toStrings (al : List Auth) : List String :=
    fork "auth list" <| al.map <| Auth.toStrings

def TxType.toStrings : TxType → List String
  | zero
    (gasPrice : Nat) =>
    fork "Type-0" [
      [s!"gas price : {gasPrice.repr}"]
    ]
  | one
    (gasPrice : Nat)
    (chainId : B64)
    (accessList : AccessList) =>
    fork "Type-1" [
      [s!"gas price : {gasPrice.repr}"],
      [s!"chain ID : {chainId}"],
      accessList.toStrings
    ]
  | two
    (chainId : B64)
    (maxPriorityFee : Nat)
    (maxFee : Nat)
    (accessList : AccessList) =>
    fork "Type-2" [
      [s!"chain ID : {chainId}"],
      [s!"max priority fee : {maxPriorityFee.repr}"],
      [s!"max fee : {maxFee.repr}"],
      accessList.toStrings
    ]
  | three
    (chainId : B64)
    (maxPriorityFee : Nat)
    (maxFee : Nat)
    (accessList : AccessList)
    (maxBlobFee : Nat)
    (blobHashes : List B256) =>
    fork "Type-3" [
      [s!"chain ID : {chainId}"],
      [s!"max priority fee : {maxPriorityFee.repr}"],
      [s!"max fee : {maxFee.repr}"],
      accessList.toStrings,
      [s!"max blob fee : {maxBlobFee.repr}"],
      fork "blob hashes" (blobHashes.map <| fun bh => [bh.toHex])
    ]
  | four
    (chainId : B64)
    (maxPriorityFee : Nat)
    (maxFee : Nat)
    (accessList : AccessList)
    (auths : List Auth) =>
    fork "Type-4" [
      [s!"chain ID : {chainId}"],
      [s!"max priority fee : {maxPriorityFee.repr}"],
      [s!"max fee : {maxFee.repr}"],
      accessList.toStrings,
      Auths.toStrings auths
    ]

instance : ToString TxType := ⟨String.joinln ∘ TxType.toStrings⟩

def Tx.toStrings (tx : Tx) : List String :=
  fork "tx" [
    [s!"nonce : {tx.nonce.toHex}"],
    [s!"gas limit : {tx.gas}"],
    [s!"receiver : {tx.receiver}"],
    [s!"value : {tx.value.repr}"],
    [s!"calldata : {tx.data.toHex}"],
    [s!"v : {tx.v}"],
    [s!"r : {tx.r.toHex}"],
    [s!"s : {tx.s.toHex}"],
    tx.type.toStrings
  ]

instance : ToString Tx := ⟨String.joinln ∘ Tx.toStrings⟩

def B8LOrTxToBLT : B8L ⊕ Tx → BLT
  | .inl bs => BLT.b8s bs
  | .inr tx => tx.toBLT

def Withdrawal.toBLT (wd : Withdrawal) : BLT :=
  BLT.list [
    BLT.b8s wd.globalIndex.toB8L.sig,
    BLT.b8s wd.validatorIndex.toB8L.sig,
    BLT.b8s wd.recipient.toB8L,
    BLT.b8s wd.amount.toB8L.sig
  ]

def Block.toIoBLT (block : Block) : IO BLT := do
  let txBLTs : List BLT := block.txs.map B8LOrTxToBLT
  .ok <| .list [
    Header.toBLT block.header,
    .list txBLTs,
    .list <| block.ommers.map Header.toBLT,
    .list <| block.wds.map Withdrawal.toBLT
  ]

def Lean.RBMap.singleton {ξ υ f} (x : ξ) (y : υ) : RBMap ξ υ f :=
  RBMap.empty.insert x y

def TxType.gasPrice (baseFee : Nat) : TxType → Nat
  | .zero gp => gp
  | .one gp _ _ => gp
  | .two _ mpf mf _ => min mf (baseFee + mpf)
  | .three _ mpf mf _ _ _ => min mf (baseFee + mpf)
  | .four _ mpf mf _ _ => min mf (baseFee + mpf)

def TxType.isBlobTx : TxType → Bool
  | .three _ _ _ _ _ _ => 1
  | _ => 0

def TxType.blobHashes : TxType → List B256
  | .zero _ => []
  | .one _ _ _ => []
  | .two _ _ _ _ => []
  | .three _ _ _ _ _ bhs => bhs
  | .four _ _ _ _ _ => []

def Tx.blobHashes (tx : Tx) : List B256 := tx.type.blobHashes

def BLT.toAdr : BLT → Option Adr
  | .b8s bs => bs.toAdr?
  | _ => none

def BLT.toB256 : BLT → Option B256
  | .b8s bs => some bs.toB256P
  | _ => none

def BLT.toAccessEntry : BLT → Option (Adr × List B256)
  | .list [.b8s ar, .list ksr] => do
    let a ← B8L.toAdr? ar
    let ks ← mapM toB256 ksr
    pure ⟨a, ks⟩
  | _ => none

def BLT.toAccessList : BLT → Option AccessList
  | .list rs => mapM toAccessEntry rs
  | _ => none

instance : ToString BLT := ⟨String.joinln ∘ BLT.toStrings⟩

def B8L.toReceiver? : B8L → Option Adr
  | [] => .none
  | xs@(_ :: _) => xs.toAdr?

def B8L.toReceiver : B8L → IO (Option Adr)
  | [] => pure .none
  | xs@(_ :: _) => (B8L.toAdr? xs).toIO "cannot convert bytes to receiver address"

def B8.toBool (x : B8) : Bool :=
  if x = 0 then .false else .true

def decodeV : B8 → IO (Bool × Option Nat)
  | 27 => pure ⟨0, .none⟩
  | 28 => pure ⟨1, .none⟩
  | v =>
    if v < 37
    then .throw "nonpositive chain ID"
    else
      let x := v - 35
      let yp : Bool := (x &&& 0x01).toBool
      let id : Nat := (x &&& 0xFE).toNat / 2
      pure ⟨yp, some id⟩

def decodeYParity : B8L → IO Bool
  | [] => pure Bool.false
  | [0x01] => pure Bool.true
  | yp => IO.throw s!"invalid yParity value : {yp.toHex}"

@[extern "ecrecover_flag"]
opaque ecrecoverFlag : ByteArray → UInt8 → ByteArray → ByteArray

@[extern "rip160"]
opaque rip160 : ByteArray → ByteArray

def ecrecover (h : B256) (v : Bool) (r : B256) (s : B256) : Option Adr :=
  let rsa : ByteArray := ⟨Array.mk (r.toB8L ++ s.toB8L)⟩
  let hsa : ByteArray := ⟨Array.mk h.toB8L⟩
  let ri : UInt8 := if v then 1 else 0
  match (ecrecoverFlag hsa ri rsa).toList with
  | [] => none
  | b :: pa =>
    if b = 0 ∨ pa.length ≠ 20
    then none
    else B8L.toAdr? pa

abbrev NTB := Lean.RBMap (List B8) (List B8) (@List.compare _ ⟨B8.compareLows⟩)

def NTB.toStrings (s : NTB) : List String :=
  let kvs := s.toArray.toList
  let kvToStrings : B8L × B8L → List String :=
    λ nb => [s!"{B4L.toHex (nb.fst.map B8.lows)} : {nb.snd.toHex}"]
  fork "NTB" (kvs.map kvToStrings)

def hpAux : B8L → (Option B8 × B8L)
  | [] => ⟨none, []⟩
  | n :: ns =>
    match hpAux ns with
    | ⟨none, bs⟩ => ⟨some n, bs⟩
    | ⟨some m, bs⟩ => ⟨none, ((n <<< 4) ||| m.lows) :: bs⟩

def hp (ns : B8L) (t : Bool) : B8L :=
  match hpAux ns with
  | ⟨none, bs⟩ => (cond t (0x20) 0) :: bs
  | ⟨some n, bs⟩ => ((cond t 0x30 0x10) ||| n.lows) :: bs

def commonPrefixCore : B8L → B8L → B8L
  | [], _ => []
  | _, [] => []
  | n :: ns, n' :: ns' =>
    if n = n' then n :: commonPrefixCore ns ns'
    else []

def commonPrefix (n : B8) (ns : B8L) : List B8L → Option B8L
  | [] => some (n :: ns)
  | ns' :: nss =>
    match commonPrefixCore (n :: ns) ns' with
    | [] => none
    | (n' :: ns'') => commonPrefix n' ns'' nss

def NTB.empty : NTB := Lean.RBMap.empty

def sansPrefix : B8L → B8L → Option B8L
  | [], ns => some ns
  | _, [] => none
  | n :: ns, n' :: ns' =>
    if n = n' then sansPrefix ns ns' else none

def insertSansPrefix (pfx : B8L) (m : NTB) (ns : B8L) (bs : B8L) : Option NTB := do
  (m.insert · bs) <$> sansPrefix pfx ns

def NTB.factor (m : NTB) : Option (B8L × NTB) := do
  let ((n :: ns) :: nss) ← some (m.toList.map Prod.fst) | none
  let pfx ← commonPrefix n ns nss
  let m' ← Lean.RBMap.foldM (insertSansPrefix pfx) NTB.empty m
  some ⟨pfx, m'⟩

structure NTBs : Type where
  (x0 : NTB) (x1 : NTB) (x2 : NTB) (x3 : NTB)
  (x4 : NTB) (x5 : NTB) (x6 : NTB) (x7 : NTB)
  (x8 : NTB) (x9 : NTB) (xA : NTB) (xB : NTB)
  (xC : NTB) (xD : NTB) (xE : NTB) (xF : NTB)

def NTBs.empty : NTBs :=
  ⟨ .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty ⟩

def NTBs.update (js : NTBs) (f : NTB → NTB) (k : B8) : NTBs :=
  match k.toBools with
  | ⟨_, _, _, _, 0, 0, 0, 0⟩ => { js with x0 := f js.x0}
  | ⟨_, _, _, _, 0, 0, 0, 1⟩ => { js with x1 := f js.x1}
  | ⟨_, _, _, _, 0, 0, 1, 0⟩ => { js with x2 := f js.x2}
  | ⟨_, _, _, _, 0, 0, 1, 1⟩ => { js with x3 := f js.x3}
  | ⟨_, _, _, _, 0, 1, 0, 0⟩ => { js with x4 := f js.x4}
  | ⟨_, _, _, _, 0, 1, 0, 1⟩ => { js with x5 := f js.x5}
  | ⟨_, _, _, _, 0, 1, 1, 0⟩ => { js with x6 := f js.x6}
  | ⟨_, _, _, _, 0, 1, 1, 1⟩ => { js with x7 := f js.x7}
  | ⟨_, _, _, _, 1, 0, 0, 0⟩ => { js with x8 := f js.x8}
  | ⟨_, _, _, _, 1, 0, 0, 1⟩ => { js with x9 := f js.x9}
  | ⟨_, _, _, _, 1, 0, 1, 0⟩ => { js with xA := f js.xA}
  | ⟨_, _, _, _, 1, 0, 1, 1⟩ => { js with xB := f js.xB}
  | ⟨_, _, _, _, 1, 1, 0, 0⟩ => { js with xC := f js.xC}
  | ⟨_, _, _, _, 1, 1, 0, 1⟩ => { js with xD := f js.xD}
  | ⟨_, _, _, _, 1, 1, 1, 0⟩ => { js with xE := f js.xE}
  | ⟨_, _, _, _, 1, 1, 1, 1⟩ => { js with xF := f js.xF}

def NTBs.insert (js : NTBs) : B8L → B8L → NTBs
  | [], _ => js
  | n :: ns, bs => js.update (Lean.RBMap.insert · ns bs) n

mutual
  def nodeComp : Nat → NTB → BLT
    | 0, _ => .b8s []
    | k + 1, j =>
      if j.isEmpty
      then .b8s []
      else let r := structComp k j
           if r.encode.length < 32
           then r
           else .b8s <| r.encode.keccak.toB8L

  def structComp : Nat → NTB → BLT
    | 0, _ => .b8s []
    | k + 1, j =>
      if j.isEmpty
      -- then .list (.replicate 17 <| .bytes []) -- what should be returned
      then .b8s [] -- what devtools actually return
      else if j.isSingleton
           then match j.toList with
                | [(k, v)] => .list [.b8s (hp k 1), .b8s v]
                | _ => .b8s [] -- unreachable code
           else match j.factor with
                | none =>
                  let js := Lean.RBMap.fold NTBs.insert NTBs.empty j
                  .list [ nodeComp k js.x0, nodeComp k js.x1, nodeComp k js.x2,
                          nodeComp k js.x3, nodeComp k js.x4, nodeComp k js.x5,
                          nodeComp k js.x6, nodeComp k js.x7, nodeComp k js.x8,
                          nodeComp k js.x9, nodeComp k js.xA, nodeComp k js.xB,
                          nodeComp k js.xC, nodeComp k js.xD, nodeComp k js.xE,
                          nodeComp k js.xF, .b8s (j.findD [] []) ]
                | some (pfx, j') => .list [.b8s (hp pfx 0), nodeComp k j']
end

def List.maxD {ξ} [Max ξ] : List ξ → ξ → ξ
  | [], y => y
  | x :: xs, y => maxD xs (max x y)

def NTB.maxKeyLength (j : NTB) : Nat := (j.toList.map (List.length ∘ Prod.fst)).maxD 0

def collapse (j : NTB) : BLT := structComp (2 * (j.maxKeyLength + 1)) j

def trie (j : NTB) : B256 :=
  B8L.keccak <| (collapse j).encode

def B256.keccak (x : B256) : B256 := B8L.keccak <| x.toB8L
def B256.toRLP (w : B256) : BLT := .b8s w.toB8L

def Stor.toNTB (s : Stor) : NTB :=
  let f : NTB → B256 → B256 → NTB :=
    λ j k v =>
      j.insert
        k.keccak.toB4s
        ((BLT.encode <| .b8s <| B8L.sig <| v.toB8L))
  Lean.RBMap.fold f NTB.empty s

def B256.zerocount (x : B256) : Nat → Nat
  | 0 => 0
  | k + 1 => if x = 0 then k + 1 else B256.zerocount (x >>> 8) k

def B256.bytecount (x : B256) : Nat := 32 - (B256.zerocount x 32)

def Acct.toVal (a : Acct) (w : B256) : B8L :=
  BLT.encode <| .list [
    .b8s a.nonce.toB8L.sig,
    .b8s a.bal.toB8L.sig,
    B256.toRLP w,
    B256.toRLP <| ByteArray.keccak 0 a.code.size a.code
  ]

def toKeyVal (pr : Adr × Acct) : B8L × B8L :=
  let ad := pr.fst
  let ac := pr.snd
  ⟨
    ad.toB8L.keccak.toB4s,
    let val' :=
      BLT.encode <| .list [
        .b8s (ac.nonce.toB8L.sig), --a.nonce,
        .b8s (ac.bal.toB8L.sig), --a.bal,
        B256.toRLP (trie ac.stor.toNTB),
        B256.toRLP <| (B8L.keccak ac.code.toList)
      ]
    val'
  ⟩

-- values --

def gHigh : Nat := 10
def gJumpdest : Nat := 1
def gTxcreate : Nat := 32000
def TX_CREATE_COST : Nat := 32000
def gAccesslistaddress : Nat := 2400
def gAccessliststorage : Nat := 1900
def GAS_INIT_CODE_WORD_COST : Nat := 2
def gBase : Nat := 2
def GAS_COPY : Nat := 3
def gReturnDataCopy : Nat := 3
def gMemory : Nat := 3
def gKeccak256 : Nat := 30
def GAS_KECCAK256_WORD : Nat := 6
def gVerylow : Nat := 3
def gLow : Nat := 5
def gMid : Nat := 8
def gExp : Nat := 10
def gExpbyte : Nat := 50
def GAS_COLD_SLOAD : Nat := 2100
def GAS_STORAGE_SET : Nat := 20000
def gSReset : Nat := 2900
def rSClear : Nat := 4800
def gTransaction : Nat := 21000
def gBlockhash : Nat := 20
def GAS_CODE_DEPOSIT : Nat := 200
def GAS_CREATE : Nat := 32000
def gHashopcode : Nat := 3
def gasPerBlob : B256 := B32.toB256 0x00020000
def gasStorageUpdate := 5000

def maxCodeSize : Nat := 24576 -- 0x00006000
def maxInitcodeSize : Nat := 49152 -- 0x0000C000

def initCodeCost (len : Nat) : Nat :=
  GAS_INIT_CODE_WORD_COST * (ceilDiv len 32)

instance {a b : Adr} : Decidable (a = b) := by
  cases a; cases b; simp; apply instDecidableAnd

instance : Hashable Adr := ⟨Adr.low⟩
instance : Hashable (Adr × B256) := ⟨λ x => x.1.low⟩

abbrev AdrSet : Type := @Std.HashSet Adr _ _
abbrev KeySet : Type := @Std.HashSet (Adr × B256) _ _

abbrev Tra : Type := Lean.RBMap Adr Stor compare

--def Sta : Type := Array B256 × Nat
def Sta : Type := Array B256 × Nat

instance : Inhabited Sta := ⟨⟨.empty, 0⟩⟩

--def cMem (a : Nat) := gMemory * a + ((a ^ 2) / 512)
def calculateMemoryGasCost (memSize : Nat) : Nat :=
  let memWordSize := ceilDiv memSize 32
  let linearCost := gMemory * memWordSize
  let quadraticCost := (memWordSize ^ 2) / 512
  linearCost + quadraticCost


structure Mem' : Type where
  data : Array B8
  size : Nat

def Mem'.empty : Mem' := ⟨.empty, 0⟩

structure Log : Type where
  (address : Adr)
  (topics : List B256)
  (data : B8L)

-- structure Environment : Type where
--   caller : Adr
--   block_hashes : List B256
--   origin : Adr
--   coinbase : Adr
--   number : Nat
--   base_fee_per_gas : Nat
--   gas_limit : Nat
--   gas_price : Nat
--   time : B256
--   prev_randao: B256
--   state: Wor
--   orig_state : Wor
--   created_accounts : AdrSet
--   chain_id: B64
--   excess_blob_gas: Nat
--   blob_versioned_hashes: List B256
--   transient_storage: Tra

/-
class Benvironment:
    """
    Items external to the virtual machine itself, provided by the environment.
    """

    chain_id: U64
    state: State
    block_gas_limit: Uint
    block_hashes: List[Hash32]
    coinbase: Address
    number: Uint
    base_fee_per_gas: Uint
    time: U256
    prev_randao: Bytes32
    excess_blob_gas: U64
    parent_beacon_block_root: Hash32
-/
structure Benv : Type where
  chainId : B64
  state : Wor
  origState : Wor
  createdAccounts : AdrSet
  blockGasLimit : Nat
  blockHashes: List B256
  coinbase : Adr
  number : Nat
  baseFeePerGas : Nat
  time : B256
  prevRandao : B256
  excessBlobGas : Nat
  parentBeaconBlockRoot : B256



/-
class TransactionEnvironment:
    """
    Items that are used by contract creation or msg call.
    """

    origin: Address
    gas_price: Uint
    gas: Uint
    access_list_addresses: Set[Address]
    access_list_storage_keys: Set[Tuple[Address, Bytes32]]
    transient_storage: TransientStorage
    blob_versioned_hashes: Tuple[VersionedHash, ...]
    authorizations: Tuple[Authorization, ...]
    index_in_block: Optional[Uint]
    tx_hash: Optional[Hash32]
    traces: List[dict]
-/
structure Tenv : Type where
    origin: Adr
    gasPrice: Nat
    gas: Nat
    accessListAddresses: AdrSet
    accessListStorageKeys: KeySet
    transientStorage: Tra
    blobVersionedHashes: List B256
    auths : List Auth
    indexInBlock : Option Nat
    txHash: Option B256
    -- traces: List[dict]

-- class Message:
--     """
--     Items that are used by contract creation or msg call.
--     """
--
--     block_env: Benvironment
--     tx_env: TransactionEnvironment
--     caller: Address
--     target: Bytes0 | Address
--     currentTarget: Address
--     gas: Uint
--     value: U256
--     data: Bytes
--     codeAddress: Optional[Address]
--     code: Bytes
--     depth: Uint
--     should_transfer_value: bool
--     isStatic: bool
--     accessedAddresses: Set[Address]
--     accessedStorageKeys: Set[Tuple[Address, Bytes32]]
--     disable_precompiles: bool
--     parent_evm: Optional["Evm"]

structure Msg : Type where
  benv: Benv
  tenv: Tenv
  caller: Adr
  target: Option Adr
  currentTarget: Adr
  gas: Nat
  value: B256
  data: B8L
  codeAddress: Option Adr
  code: ByteArray
  depth: Nat
  shouldTransferValue: Bool
  isStatic: Bool
  accessedAddresses: AdrSet
  accessedStorageKeys: KeySet
  disablePrecompiles : Bool

abbrev ExceptionalHalt (err : String) : Prop :=
  err ∈ [
    "StackUnderflowError",
    "StackOverflowError",
    "OutOfGasError",
    "InvalidOpcode",
    "InvalidJumpDestError",
    "StackDepthLimitError",
    "WriteInStaticContext",
    "OutOfBoundsRead",
    "InvalidParameter",
    "InvalidContractPrefix",
    "AddressCollision",
    "KZGProofError"
  ]

def hasErrorType (err errType : String) : Bool :=
  err = errType || String.isPrefixOf (errType ++ " : ") err

def isInvalidTransaction (err : String) : Bool :=
  List.any ["InvalidSenderError", "InvalidSignatureError"] (hasErrorType err)

def isEthereumException (err : String) : Bool :=
  hasErrorType err "InvalidBlock" || isInvalidTransaction err

def isRlpException (err : String) : Bool :=
  List.any ["EncodingError", "DecodingError"] (hasErrorType err)

structure Evm : Type where
  pc : Nat
  stack: List B256
  memory: Mem'
  code: ByteArray
  gas_left: Nat
  logs: List Log
  refund_counter: Int
  msg: Msg
  output: B8L
  accountsToDelete: AdrSet
  return_data: B8L
  error: Option String
  accessedAddresses: AdrSet
  accessedStorageKeys: KeySet

def Stack.toStrings (stack : List B256) : List String :=
  fork "STACK" [
    ["-------------------------- STACK TOP ---------------------------"] ++
    stack.map B256.toHex ++
    ["------------------------- STACK BOTTOM -------------------------"]

  ]

def Mem.toStrings (mem : Mem') : List String :=
  fork "MEM" [
    String.chunks 64 <| B8L.toHex mem.data.toList
  ]

def mkSingleton {ξ : Type u} : ξ → List ξ
  | x => [x]

def Log.toStrings (l : Log) : List String :=
  fork "log" [
    [s!"address : {l.address.toHex}"],
    fork "topics" (l.topics.map (mkSingleton ∘ B256.toHex)),
    fork "data" [String.chunks 64 l.data.toHex]
  ]


def Tra.toStrings (tra : Tra) : List String :=
  fork "TRANSIENT STORAGE" <| tra.toList.map <|
    fun kv =>
      fork kv.fst.toHex <| kv.snd.toList.map <|
        mkSingleton ∘ fun kv' => s!"{kv'.fst.toHex} : {B256.toHex kv'.snd}"

def Msg.toStrings (msg : Msg) : List String  :=
  fork "MESSAGE" [
    [s!"caller : {msg.caller.toHex}"],
    [s!"target : {(msg.target.rec "NONE" Adr.toHex : String)}"],
    [s!"current target : {msg.currentTarget.toHex}"],
    [s!"gas : {msg.gas}"],
    [s!"value : {msg.value.toHex}"],
    [s!"data : {msg.data.toHex}"],
    [s!"code address : {(msg.codeAddress.rec "None" Adr.toHex : String)}"],
    fork "CODE" [String.chunks 64 <| B8L.toHex msg.code.toList],
    [s!"depth : {msg.depth}"],
    [s!"should transfer value : {msg.shouldTransferValue}"],
    [s!"is static : {msg.isStatic}"],
    fork "ACCESSED ADDRESSES"
      (msg.accessedAddresses.toList.map (mkSingleton ∘ Adr.toHex)),
    fork "ACCESSED STORAGE KEYS"
      (msg.accessedStorageKeys.toList.map (fun kv => [s!"{kv.fst.toHex} : {B256.toHex kv.snd}"]))
  ]

def Benv.toStrings (benv : Benv) : List String :=
  fork "BLOCK ENVIRONMENT" [
    [s!"CHAIN ID : {benv.chainId}"],
    fork "STATE" [Wor.toStrings benv.state],
    [s!"BLOCK GAS LIMIT : {benv.blockGasLimit}"],
    fork "BLOCK HASHES" (benv.blockHashes.map (mkSingleton ∘ B256.toHex)),
    [s!"COINBASE : {benv.coinbase}"],
    [s!"BASE FEE PER GAS : {benv.baseFeePerGas}"],
    [s!"TIME : {benv.time.toHex}"],
    [s!"PREVRANDAO : {benv.prevRandao.toHex}"],
    [s!"EXCESS BLOB GAS : {benv.excessBlobGas}"],
    [s!"PARENT BEACON BLOCK ROOT : {benv.parentBeaconBlockRoot.toHex}"]
  ]

def Evm.toStrings (evm : Evm) : List String :=
  fork "EVM" [
    [s!"PC : {evm.pc}"],
    Stack.toStrings evm.stack,
    Mem.toStrings evm.memory,
    [s!"CODE : {B8L.toHex evm.code.toList}"],
    [s!"GAS LEFT : {evm.gas_left}"],
    -- Environment.toStrings evm.env,
    fork "LOGS" (evm.logs.map Log.toStrings),
    [s!"REFUND COUNTER : {evm.refund_counter}"],
    Msg.toStrings evm.msg,
    [s!"output : {evm.output.toHex}"],
    fork "ACCOUNTS TO DELETE"
      (evm.accountsToDelete.toList.map (mkSingleton ∘ Adr.toHex)),
    [s!"return data : {evm.return_data.toHex}"],
    fork "ACCESSED ADDRESSES"
      (evm.accessedAddresses.toList.map (mkSingleton ∘ Adr.toHex)),
    fork "ACCESSED STORAGE KEYS"
      (evm.accessedStorageKeys.toList.map (fun kv => [s!"{kv.fst.toHex} : {B256.toHex kv.snd}"]))
  ]

def Adr.toNat (x : Adr) : Nat :=
  x.high.toNat * (2 ^ 128) +
  x.mid.toNat * (2 ^ 64) +
  x.low.toNat

def Nat.toAdr (n : Nat) : Adr :=
  let h := n / (2 ^ 128)
  let r := n % (2 ^ 128)
  let m := r / (2 ^ 64)
  let l := r % (2 ^ 64)
  {
    high := h.toUInt32
    mid  := m.toUInt64
    low  := l.toUInt64
  }

instance {n} : OfNat Adr n := ⟨n.toAdr⟩

abbrev Adr.isPrecomp (a : Adr) : Prop :=
  1 ≤ a.toNat ∧ a.toNat ≤ 10

def gas_ecrecover : Nat := 3000

def safeSub {ξ} [Sub ξ] [LE ξ] [@DecidableRel ξ (· ≤ ·)] (x y : ξ) : Option ξ :=
  if y ≤ x then some (x - y) else none

def chargeGas (cost : Nat) (evm : Evm) : Except (Evm × String) Evm := do
  match safeSub evm.gas_left cost with
  | none => .error ⟨evm, "OutOfGasError"⟩
  | some gas => .ok {evm with gas_left := gas}

def Nat.secp256k1n : Nat := 15792089237316195423570985008687907852837564279074904382605163141518161494337
def B256.secp256k1n : B256 := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

def B256.toAdr : B256 → Adr
  | ⟨⟨_, x⟩, ⟨y, z⟩⟩ => {high := x.toUInt32, mid := y, low := z}

def Adr.toB256 (a : Adr) : B256 :=
  ⟨⟨0, a.high.toUInt64⟩ , ⟨a.mid, a.low⟩⟩

def execute_ecrec (evm : Evm) : Except (Evm × String) Evm := do
  let data := evm.msg.data
  let evm ← chargeGas gas_ecrecover evm
  let msg_hash := B8L.toB256P <| data.sliceD 0 32 (0x00 : B8)
  let v : Option Bool :=
    match (B8L.toB256P <| data.sliceD 32 32 (0x00 : B8)) with
    | 0x1B => some .false
    | 0x1C => some .true
    | _ => none
  let r := B8L.toB256P <| data.sliceD 64 32 (0x00 : B8)
  let s := B8L.toB256P <| data.sliceD 96 32 (0x00 : B8)
  if v.isNone ∨ r = 0 ∨ r ≥ .secp256k1n ∨ s = 0 ∨ s ≥ .secp256k1n
  then .ok evm
  else
    match ecrecover msg_hash v.get! r s with
    | none => .ok evm
    | some address =>
      let padded_address := address.toB256.toB8L
      .ok {evm with output := padded_address}

def GAS_SHA256 : Nat := 60
def GAS_SHA256_WORD : Nat := 12

def execute_sha (evm : Evm) : Except (Evm × String) Evm := do
  let data := evm.msg.data
  let word_count := ceilDiv data.length 32
  let evm ← chargeGas (GAS_SHA256 + GAS_SHA256_WORD * word_count) evm
  let hash : B256 := B8L.sha256 data
  .ok {evm with output := hash.toB8L}

def GAS_RIPEMD160 : Nat := 600
def GAS_RIPEMD160_WORD : Nat := 120

def execute_ripemd160 (evm : Evm) : Except (Evm × String) Evm := do
  let data := evm.msg.data
  let word_count := ceilDiv data.length 32
  let evm ← chargeGas (GAS_RIPEMD160 + GAS_RIPEMD160_WORD * word_count) evm
  let hash : B256 := B8L.toB256P <| (rip160 ⟨.mk data⟩).toList
  .ok {evm with output := hash.toB8L}

def GAS_IDENTITY : Nat := 15
def GAS_IDENTITY_WORD : Nat := 3

def execute_id (evm : Evm) : Except (Evm × String) Evm := do
  let data := evm.msg.data
  let word_count := ceilDiv data.length 32
  let evm ← chargeGas (GAS_IDENTITY + GAS_IDENTITY_WORD * word_count) evm
  .ok {evm with output := data}

abbrev altBn128Prime      : Nat := 21888242871839275222246405745257275088696311157297823662689037894645226208583
abbrev altBn128CurveOrder : Nat := 21888242871839275222246405745257275088548364400416034343698204186575808495617

structure FinField (p : Nat) : Type where
  (val : Nat)
deriving DecidableEq

abbrev BNF : Type := FinField altBn128Prime

instance {p} : ToString (FinField p) := ⟨fun x => toString x.val⟩

def FinField.ofNat {p : Nat} (n : Nat) : FinField p := ⟨n % p⟩

def FinField.ofInt {p : Nat} : Int → FinField p
  | .ofNat n => .ofNat n
  | .negSucc n => .ofNat (p - n.succ % p) -- handle negative integers by wrapping around the field size

instance {p n : Nat} : OfNat (FinField p) n := ⟨.ofNat n⟩

structure EllipticCurve (F : Type) (a b : F) : Type where
  (x : F)
  (y : F)
deriving DecidableEq

abbrev FinFields (p : Nat) : Type := List (FinField p)

structure GaloisField (p : Nat) (m : FinFields p) : Type where
  (val : FinFields p)
deriving DecidableEq

instance {p m} : ToString (GaloisField p m) := ⟨
  fun x =>
  String.joinln <|
    "  [" :: (x.val.map <| fun y => "    " ++ toString y ++ ",") ++ ["  ]"]
⟩

abbrev BNF2 : Type :=
  -- FinField altBn128Prime × FinField altBn128Prime
  GaloisField altBn128Prime [1, 0, 1]

-- def BNF2.i : BNF2 := ⟨[1, 0]⟩

def GaloisField.ofNat {p} {m} : Nat → GaloisField p m
  | 0 => ⟨[]⟩
  | n@(_ + 1) => ⟨[.ofNat n]⟩

instance {p m n} : OfNat (GaloisField p m) n := ⟨.ofNat n⟩


-- structure BNP2 : Type where
--   (x : BNF2)
--   (y : BNF2)
--
-- def BNP2.toString : BNP2 → String
--   | ⟨x, y⟩ => s!"⟨{x.val}, {y.val}⟩"
--
-- instance : ToString BNP2 := ⟨BNP2.toString⟩

def Nat.toHexit : Nat → Char
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | 9 => '9'
  | 10 => 'A'
  | 11 => 'B'
  | 12 => 'C'
  | 13 => 'D'
  | 14 => 'E'
  | 15 => 'F'
  | _   => 'X'

def Nat.toHexCore : Nat → List Char
  | 0 => []
  | n@(_ + 1) =>
    if n < 16
    then [n.toHexit]
    else (n % 16).toHexit :: (n / 16).toHexCore

def Nat.toHex (n : Nat) : String :=
  ⟨.reverse <| n.toHexCore⟩


def FinField.pow {p : Nat} (b : FinField p) (e : Nat) : FinField p :=
  ⟨Nat.powMod b.val e p⟩

instance {p} : HPow (FinField p) Nat (FinField p) := ⟨FinField.pow⟩

def FinField.add {p : Nat} (x y : FinField p) : FinField p :=
  ⟨(x.val + y.val) % p⟩

instance {p} : HAdd (FinField p) (FinField p) (FinField p) := ⟨FinField.add⟩

def FinField.sub {p : Nat} (x y : FinField p) : FinField p :=
  ⟨Int.natAbs <| (Int.ofNat x.val - Int.ofNat y.val) % p⟩

instance {p} : HSub (FinField p) (FinField p) (FinField p) := ⟨FinField.sub⟩

def FinField.mul {p : Nat} (x y : FinField p) : FinField p :=
  ⟨(x.val * y.val) % p⟩

instance {p} : HMul (FinField p) (FinField p) (FinField p) := ⟨FinField.mul⟩

def BNF2.mk (x y : Nat) : BNF2 :=
  ⟨[.ofNat x, .ofNat y]⟩

def extEuclid (x y : Nat) : Int × Int × Nat :=
  if hx : x > 0
  then
    if hy : y > 0
    then
      if _ : x < y
      then
        have _ : y % x < x := Nat.mod_lt _ hx
        let ⟨cy, cx, d⟩ := extEuclid (y % x) x
        ⟨cx - (cy * (y / x)), cy, d⟩
      else
        if _ : y < x
        then
          have _ : x % y < y := Nat.mod_lt _ hy
          let ⟨cy, cx, d⟩ := extEuclid y (x % y)
          ⟨cx, cy - (cx * (x / y)), d⟩
        else ⟨0, 1, x⟩
    else ⟨1, 0, x⟩
  else ⟨0, 1, y⟩
termination_by (x + y)

def FinField.inv {p : Nat} (x : FinField p) : FinField p :=
  let ⟨c, _, _⟩ := extEuclid x.val p
  ⟨(c % p).natAbs⟩

instance {p} : Inv (FinField p) := ⟨FinField.inv⟩

def FinField.div {p : Nat} (x y : FinField p) : FinField p := x * (y⁻¹)

instance {p} : HDiv (FinField p) (FinField p) (FinField p) := ⟨FinField.div⟩

instance {k} : Inhabited (FinField k) := ⟨0⟩

def trimZero {ξ} [Zero ξ] [DecidableEq ξ] (xs : List ξ) : List ξ :=
  List.dropWhile (· = 0) xs

def zipWithZero {ξ} [Zero ξ] : List ξ → List ξ → List (ξ × ξ)
  | [], [] => []
  | [], y :: ys => (0, y) :: zipWithZero [] ys
  | x :: xs, [] => (x, 0) :: zipWithZero xs []
  | x :: xs, y :: ys => (x, y) :: zipWithZero xs ys

lemma zipWithZero_length {ξ} [Zero ξ] (xs ys : List ξ) :
  (zipWithZero xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys with
    | nil =>
      induction ys with
      | nil => simp [zipWithZero]
      | cons y ys ih => simp [zipWithZero, ih]
    | cons x xs ih =>
      induction ys with
      | nil => simp [zipWithZero, ih]
      | cons y ys ih' =>
        simp [zipWithZero, ih, ih', List.length, Nat.succ_max_succ]

def zipWithZeroLeft {ξ} [Zero ξ] (xs ys : List ξ) : List (ξ × ξ) :=
  (zipWithZero xs.reverse ys.reverse).reverse

lemma zipWithZeroLeft_length {ξ} [Zero ξ] (xs ys : List ξ) :
  (zipWithZeroLeft xs ys).length = max xs.length ys.length := by
  simp [zipWithZeroLeft, zipWithZero_length]

lemma trimZero_length {ξ} [Zero ξ] [DecidableEq ξ] (xs : List ξ) :
  (trimZero xs).length ≤ xs.length := by
  simp [trimZero, List.length_dropWhile_le]

def FinFields.sub {p} (xs ys : FinFields p) : FinFields p :=
  trimZero <| (zipWithZeroLeft xs ys).map (fun ⟨x, y⟩ => x - y)

lemma FinFields.sub_length {p} (xs ys : FinFields p) :
  (FinFields.sub xs ys).length ≤ max xs.length ys.length := by
  apply le_trans (trimZero_length _)
  simp [List.length_map, zipWithZeroLeft_length]

def FinFields.add {p} (xs ys : FinFields p) : FinFields p :=
  trimZero <| (zipWithZeroLeft xs ys).map (fun ⟨x, y⟩ => x + y)

lemma FinFields.add_length {p} (xs ys : FinFields p) :
  (FinFields.add xs ys).length ≤ max xs.length ys.length := by
  apply le_trans (trimZero_length _)
  simp [List.length_map, zipWithZeroLeft_length]

def FinFields.mul {p} (xs : FinFields p) : FinFields p → FinFields p
  | [] => []
  | y :: ys =>
    let fromTail := FinFields.mul xs ys
    let fromHead := trimZero <| (xs.map (· * y)) ++ List.replicate ys.length 0
    FinFields.add fromHead fromTail

def FinFields.divMod {p} (xs ys : FinFields p) : FinFields p × FinFields p :=
  match xs, ys with
  | [], _ => ([], [])
  | xs, [] => ([], xs) -- similar to x / 0 = 0, x % 0 = x for Nat
  | x :: xs, y :: ys =>
    if hlt : xs.length < ys.length
    then ([], x :: xs)
    else
      have hle : ys.length ≤ xs.length := by
        rw [not_lt] at hlt; exact hlt
      let c := x * (y⁻¹)
      let zeroes := List.replicate (xs.length - ys.length) 0
      let cys := (ys.map (· * c)) ++ zeroes
      have cys_length : List.length cys = xs.length := by
        simp [cys, zeroes, List.length_append,  List.length_replicate, List.length_map];
        rw [← Nat.add_sub_assoc hle, Nat.add_sub_cancel_left];
      let xs' := FinFields.sub xs cys
      have h : xs'.length < (x :: xs).length := by
        rw [not_lt] at hlt; simp only [xs']
        apply lt_of_le_of_lt (FinFields.sub_length xs cys)
        simp [cys_length]
      let (div, mod) := FinFields.divMod xs' (y :: ys)
      (FinFields.add (c :: zeroes) div, mod)
termination_by xs.length

lemma FinFields.divMod_snd_length {p} (xs) (len) (y) (ys : FinFields p) :
  xs.length ≤ len → (FinFields.divMod xs (y :: ys)).snd.length ≤ ys.length := by
  revert xs
  induction len with
  | zero =>
    intro xs h_eq; rw [Nat.le_zero] at h_eq
    simp [List.length_eq_zero.mp h_eq, divMod]
  | succ len ih =>
    intro xs h_le
    rcases xs with _ | ⟨x, xs⟩ <;> simp [divMod] -- try {simp [divMod]; done}
    split
    · rename (_ < _) => h_lt
      simp [List.length]; apply Nat.succ_le_of_lt h_lt
    · rename (¬ _ < _) => h_le'
      simp [not_lt] at h_le'
      simp [List.length] at h_le
      apply ih
      apply le_trans (FinFields.sub_length _ _)
      simp [List.length_map, List.length_replicate, List.length_append, h_le]
      rw [← Nat.add_sub_assoc h_le', Nat.add_sub_cancel_left];
      apply h_le

def FinFields.div {p} (xs ys : FinFields p) : FinFields p :=
  (FinFields.divMod xs ys).fst

def FinFields.mod {p} (xs ys : FinFields p) : FinFields p :=
  (FinFields.divMod xs ys).snd

def GaloisField.add {p : Nat} {m : FinFields p}
  (xs ys : GaloisField p m) : GaloisField p m :=
  ⟨FinFields.add xs.val ys.val⟩

instance {p m} : HAdd (GaloisField p m) (GaloisField p m) (GaloisField p m) :=
  ⟨@GaloisField.add p m⟩

def GaloisField.sub {p : Nat} {m : FinFields p}
  (xs ys : GaloisField p m) : GaloisField p m :=
  ⟨FinFields.sub xs.val ys.val⟩

instance {p m} : HSub (GaloisField p m) (GaloisField p m) (GaloisField p m) :=
  ⟨@GaloisField.sub p m⟩

def GaloisField.mod {p : Nat} {m : FinFields p}
  (xs ys : GaloisField p m) : GaloisField p m :=
  ⟨FinFields.mod xs.val ys.val⟩

instance : HMod (GaloisField p m) (GaloisField p m) (GaloisField p m) :=
  ⟨GaloisField.mod⟩

def GaloisField.mul {p : Nat} {m : FinFields p}
  (xs ys : GaloisField p m) : GaloisField p m :=
  let product := FinFields.mul xs.val ys.val
  ⟨FinFields.mod product m⟩

instance {p m} : HMul (GaloisField p m) (GaloisField p m) (GaloisField p m) :=
  ⟨@GaloisField.mul p m⟩

def GaloisField.pow {p} {m} (x : GaloisField p m) : Nat → GaloisField p m
  | 0 => 1
  | n@(_ + 1) =>
    let root := GaloisField.pow x (n / 2)
    let whole := GaloisField.mul root root
    if (n % 2) = 0
    then
      whole
    else
      GaloisField.mul whole x

instance {p m} : HPow (GaloisField p m) Nat (GaloisField p m) :=
  ⟨@GaloisField.pow p m⟩

instance {p} : HMul (FinFields p) (FinFields p) (FinFields p) :=
  ⟨FinFields.mul⟩

instance {p} : HSub (FinFields p) (FinFields p) (FinFields p) :=
  ⟨FinFields.sub⟩

instance {p} : HDiv (FinFields p) (FinFields p) (FinFields p) :=
  ⟨FinFields.div⟩

instance {p} : HMod (FinFields p) (FinFields p) (FinFields p) :=
  ⟨FinFields.mod⟩

lemma FinFields.mod_cons_length {p} (y) (xs ys : FinFields p) :
  (xs % (y :: ys)).length < (y :: ys).length := by
  simp [List.length]; apply Nat.lt_succ_of_le
  apply FinFields.divMod_snd_length _ _ _ _ (le_refl _)

def FinFields.euclid {p} (xs ys : FinFields p) :
  FinFields p × FinFields p × FinFields p :=
  match xs, ys with
  | [], [] => ([], [], [])
  | [], ys@(y :: _) => ([0], [y⁻¹], ys.map (· * y⁻¹))
  | xs@(x :: _), [] => ([x⁻¹], [0], xs.map (· * x⁻¹))
  | xs@(_ :: _), ys@(_ :: _) =>
    have h : (xs % ys).length < ys.length := by
      rename (ys = _ :: _) => h_rw; rw [h_rw]
      apply FinFields.mod_cons_length
    let ⟨a, b, d⟩ := FinFields.euclid ys (xs % ys)
    ⟨b, a - (b * (xs / ys)), d⟩
termination_by ys.length

def GaloisField.inv {p} {m} (xs : GaloisField p m) : GaloisField p m :=
  let ⟨c, _, _⟩ := FinFields.euclid xs.val m
  ⟨c % m⟩

instance {p m} : Inv (GaloisField p m) := ⟨GaloisField.inv⟩

def GaloisField.div {p} {m} (xs ys : GaloisField p m) : GaloisField p m :=
  xs * (ys⁻¹)

instance {p m} : HDiv (GaloisField p m) (GaloisField p m) (GaloisField p m) :=
  ⟨GaloisField.div⟩

abbrev BNP2 : Type := EllipticCurve BNF2 0 ((3 : BNF2) / ⟨[1, 9]⟩)--(BNF2.i + (9 : BNF2)))

abbrev BNP : Type := EllipticCurve BNF (0 : BNF) (3 : BNF)

abbrev BNF12 : Type :=
  GaloisField
    altBn128Prime
    [1, 0, 0, 0, 0, 0, .ofInt (-18 : Int), 0, 0, 0, 0, 0, 82]

abbrev BNP12 : Type := EllipticCurve BNF12 (0 : BNF12) (3 : BNF12)

def EllipticCurve.toString {F} {a b} [ToString F] : EllipticCurve F a b → String
  | ⟨x, y⟩ => s!"⟨{x},{y}\n⟩"

instance {F} {a b} [ToString F] : ToString (EllipticCurve F a b) :=
  ⟨EllipticCurve.toString⟩

-- def BNP.mk? (x : Nat) (y : Nat) : Option BNP := do
--   let x' : BNF := FinField.ofNat x
--   let y' : BNF := FinField.ofNat y
--   if (x' = 0 ∧ y' = 0)
--   then some ⟨0, 0⟩
--   else if y' ^ 2 = (x' ^ 3) + 3
--        then some ⟨x', y'⟩
--        else none

def EllipticCurve.isOnCurve {F} [Zero F] [DecidableEq F]
  [HAdd F F F] [HMul F F F] [HPow F Nat F]
  {a b} (p : EllipticCurve F a b) : Prop :=
  (p.x = 0 ∧ p.y = 0) ∨ (p.y ^ 2 = (p.x ^ 3) + (a * p.x) + b)

instance {F} [Zero F] [DecidableEq F]
  [HAdd F F F] [HMul F F F] [HPow F Nat F]
  {a b} {p : EllipticCurve F a b} : Decidable p.isOnCurve :=
  instDecidableOr

def EllipticCurve.mk? {F} [Zero F] [DecidableEq F]
  [HAdd F F F] [HMul F F F] [HPow F Nat F]
  {a b} (x y : F) : Option (EllipticCurve F a b) :=
  let p : EllipticCurve F a b := ⟨x, y⟩
  if p.isOnCurve
  then some p
  else none

-- def EllipticCurve.mk? {F} [Zero F] [DecidableEq F]
--   [HAdd F F F] [HMul F F F] [HPow F Nat F]
--   {a b} (x y : F) : Option (EllipticCurve F a b) :=
--   if (x = 0 ∧ y = 0)
--   then some ⟨0, 0⟩
--   else
--     if y ^ 2 = (x ^ 3) + (a * x) + b
--     then some ⟨x, y⟩
--     else none

def BNP.mk? (x : Nat) (y : Nat) : Option BNP :=
  EllipticCurve.mk? (FinField.ofNat x) (FinField.ofNat y)


/-
def double(self: T) -> T:
    """
    Add a point to itself.
    """
    x, y, F = self.x, self.y, self.FIELD
    if x == 0 and y == 0:
        return self
    lam = (F.from_int(3) * x**2 + self.A) / (F.from_int(2) * y)
    new_x = lam**2 - x - x
    new_y = lam * (x - new_x) - y
    return self.__new__(type(self), new_x, new_y)
-/
def EllipticCurve.double {F} [Zero F] [DecidableEq F]
  [HAdd F F F] [HSub F F F] [HMul F F F] [HDiv F F F]
  [HPow F Nat F] [OfNat F 3] [OfNat F 2]
  [ToString F]
  {a b} (p : EllipticCurve F a b) : EllipticCurve F a b :=
  if p.x = 0 ∧ p.y = 0
  then
    p
  else
    let lam : F := (3 * (p.x ^ 2) + a) / (2 * p.y)
    let x : F := lam ^ 2 - p.x - p.x
    let y : F := lam * (p.x - x) - p.y
    ⟨x, y⟩

/-
def __add__(self: T, other: T) -> T:
    """
    Add two points together.
    """
    ZERO = self.FIELD.zero()
    self_x, self_y, other_x, other_y = self.x, self.y, other.x, other.y
    if self_x == ZERO and self_y == ZERO:
        return other
    if other_x == ZERO and other_y == ZERO:
        return self
    if self_x == other_x:
        if self_y == other_y:
            return self.double()
        else:
            return self.point_at_infinity()
    lam = (other_y - self_y) / (other_x - self_x)
    x = lam**2 - self_x - other_x
    y = lam * (self_x - x) - self_y
    return self.__new__(type(self), x, y)
-/
def EllipticCurve.add {F} [Zero F] [DecidableEq F]
  [HAdd F F F] [HSub F F F] [HMul F F F] [HDiv F F F]
  [HPow F Nat F] [OfNat F 3] [OfNat F 2]
  [ToString F]
  {a b} (p q : EllipticCurve F a b) : EllipticCurve F a b :=
  if p.x = 0 ∧ p.y = 0
  then q
  else
    if q.x = 0 ∧ q.y = 0
    then p
    else
      if p.x = q.x
      then
        if p.y = q.y
        then EllipticCurve.double p
        else ⟨0, 0⟩ -- point at infinity
      else
        let yDiff := q.y - p.y
        let xDiff := q.x - p.x
        let lam : F := yDiff / xDiff
        let x : F := lam ^ 2 - p.x - q.x
        let y : F := lam * (p.x - x) - p.y
        ⟨x, y⟩

instance {F} [Zero F] [DecidableEq F] [HAdd F F F] [HSub F F F]
  [HMul F F F] [HDiv F F F] [HPow F Nat F] [OfNat F 3] [OfNat F 2] {a b}
  [ToString F]
  :
  HAdd (EllipticCurve F a b) (EllipticCurve F a b) (EllipticCurve F a b) :=
  ⟨EllipticCurve.add⟩

def EllipticCurve.mulBy {F} [Zero F] [DecidableEq F]
  [HAdd F F F] [HSub F F F] [HMul F F F] [HDiv F F F]
  [HPow F Nat F] [OfNat F 3] [OfNat F 2]
  [ToString F]
  {a b} (p : EllipticCurve F a b) : Nat → EllipticCurve F a b
  | 0 => ⟨0, 0⟩
  | n@(_ + 1) =>
    let half := EllipticCurve.mulBy p (n / 2)
    let whole := half + half
    if (n % 2) = 0
    then whole
    else whole + p

instance {F} [Zero F] [DecidableEq F] [HAdd F F F] [HSub F F F]
  [HMul F F F] [HDiv F F F] [HPow F Nat F] [OfNat F 3] [OfNat F 2] {a b}
  [ToString F]

  :
  HMul (EllipticCurve F a b) Nat (EllipticCurve F a b) :=
  ⟨EllipticCurve.mulBy⟩

def BNP.toB8L (p : BNP) : B8L :=
  p.x.val.toB8L.pack 32 ++ p.y.val.toB8L.pack 32

def ecadd (input : B8L) : Option B8L := do
  let px : Nat := B8L.toNat <| input.sliceD 0 32 (0 : B8)
  let py : Nat := B8L.toNat <| input.sliceD 32 32 (0 : B8)
  let qx : Nat := B8L.toNat <| input.sliceD 64 32 (0 : B8)
  let qy : Nat := B8L.toNat <| input.sliceD 96 32 (0 : B8)
  let p ← BNP.mk? px py
  let q ← BNP.mk? qx qy
  let s := p + q
  some <| BNP.toB8L s

def ecmul (input : B8L) : Option B8L := do
  let px : Nat := B8L.toNat <| input.sliceD 0 32 (0 : B8)
  let py : Nat := B8L.toNat <| input.sliceD 32 32 (0 : B8)
  let n  : Nat := B8L.toNat <| input.sliceD 64 32 (0 : B8)
  let p ← BNP.mk? px py
  let s := p * n
  -- some s.toB8L
  some <| BNP.toB8L s

def execute_ecadd (evm : Evm) : Except (Evm × String) Evm := do
  let data := evm.msg.data
  let evm ← chargeGas 150 evm

  let x0_value : Nat := B8L.toNat <| data.sliceD 0  32 (0 : B8)
  let y0_value : Nat := B8L.toNat <| data.sliceD 32 32 (0 : B8)
  let x1_value : Nat := B8L.toNat <| data.sliceD 64 32 (0 : B8)
  let y1_value : Nat := B8L.toNat <| data.sliceD 96 32 (0 : B8)

  .assert
    ( x0_value < altBn128Prime ∧ x0_value < altBn128Prime ∧
      x1_value < altBn128Prime ∧ x1_value < altBn128Prime )
    ⟨evm, "OutOfGasError"⟩

  let p0 ← (BNP.mk? x0_value y0_value).toExcept ⟨evm, "OutOfGasError"⟩
  let p1 ← (BNP.mk? x1_value y1_value).toExcept ⟨evm, "OutOfGasError"⟩
  .ok {evm with output := BNP.toB8L (p0 + p1)}

def execute_ecmul (evm : Evm) : Except (Evm × String) Evm := do
  let data := evm.msg.data
  let evm ← chargeGas 6000 evm

  let x_value : Nat := B8L.toNat <| data.sliceD 0  32 (0 : B8)
  let y_value : Nat := B8L.toNat <| data.sliceD 32 32 (0 : B8)
  let n       : Nat := B8L.toNat <| data.sliceD 64 32 (0 : B8)

  .assert
    (x_value < altBn128Prime ∧ y_value < altBn128Prime)
    ⟨evm, "OutOfGasError"⟩

  let p ← (BNP.mk? x_value y_value).toExcept ⟨evm, "OutOfGasError"⟩

  .ok {evm with output := BNP.toB8L (p * n)}

inductive Ninst' : Type
  | reg : Rinst → Ninst'
  | exec : Xinst → Ninst'
  | push : B256 → Nat →  Ninst'

def Ninst'.toString : Ninst' → String
  | reg o => Rinst.toString o
  | exec o => Xinst.toString o
  | push _ 0 => "PUSH0"
  | push x len => "PUSH" ++ len.repr ++ " 0x" ++ x.toHex.trimHex

inductive Inst' : Type
  | last : Linst → Inst'
  | next : Ninst' → Inst'
  | jump : Jinst → Inst'

def getInstAux (code : ByteArray) (pc len off : Nat) : B8 :=
  if off < len
  then code.get! ((pc + len) - off)
  else 0

def Evm.getInst (evm : Evm) : Option Inst' :=
  if evm.pc < evm.code.size
  then
    let b : B8 := evm.code.get! evm.pc
    (b.toRinst <&> (.next ∘ .reg)) <|>
    (b.toXinst <&> (.next ∘ .exec)) <|>
    (b.toJinst <&> .jump) <|>
    (b.toLinst <&> .last) <|>
    (
      let bn := b.toNat
      if 95 ≤ bn ∧ bn ≤ 127
      then let len := bn - 95
           let x : B256 :=
             B8s.toB256
               (getInstAux evm.code evm.pc len 31)
               (getInstAux evm.code evm.pc len 30)
               (getInstAux evm.code evm.pc len 29)
               (getInstAux evm.code evm.pc len 28)
               (getInstAux evm.code evm.pc len 27)
               (getInstAux evm.code evm.pc len 26)
               (getInstAux evm.code evm.pc len 25)
               (getInstAux evm.code evm.pc len 24)
               (getInstAux evm.code evm.pc len 23)
               (getInstAux evm.code evm.pc len 22)
               (getInstAux evm.code evm.pc len 21)
               (getInstAux evm.code evm.pc len 20)
               (getInstAux evm.code evm.pc len 19)
               (getInstAux evm.code evm.pc len 18)
               (getInstAux evm.code evm.pc len 17)
               (getInstAux evm.code evm.pc len 16)
               (getInstAux evm.code evm.pc len 15)
               (getInstAux evm.code evm.pc len 14)
               (getInstAux evm.code evm.pc len 13)
               (getInstAux evm.code evm.pc len 12)
               (getInstAux evm.code evm.pc len 11)
               (getInstAux evm.code evm.pc len 10)
               (getInstAux evm.code evm.pc len  9)
               (getInstAux evm.code evm.pc len  8)
               (getInstAux evm.code evm.pc len  7)
               (getInstAux evm.code evm.pc len  6)
               (getInstAux evm.code evm.pc len  5)
               (getInstAux evm.code evm.pc len  4)
               (getInstAux evm.code evm.pc len  3)
               (getInstAux evm.code evm.pc len  2)
               (getInstAux evm.code evm.pc len  1)
               (getInstAux evm.code evm.pc len  0)
           some (.next <| .push x len)
      else none
    )
  else some (.last .stop)

def fakeExpAux (num den i : Nat) : Nat → Nat → Nat
  | _, 0 => panic! "error : recursion limit reached for fake exponentiation"
  | 0, _ => 0
  | numAcc, lim + 1 =>
    let numAcc' := (numAcc * num) / (den * i)
    numAcc + fakeExpAux num den (i + 1) numAcc' lim

def fakeExp (fac num den : Nat) : Nat :=
  let lim := (max (fac * num) <| num * num) + 2
  let out := fakeExpAux num den 1 (fac * den) lim
  out / den

def BLOB_BASE_FEE_UPDATE_FRACTION : Nat := 3338477

def calculate_blob_gas_price (excessBlobGas : Nat) : Nat :=
  fakeExp 1 excessBlobGas BLOB_BASE_FEE_UPDATE_FRACTION

def Evm.push (x : B256) (evm : Evm) : Except (Evm × String) Evm := do
  .assert
    (evm.stack.length < 1024)
    ⟨evm, "StackOverflowError"⟩
  .ok {evm with stack := x :: evm.stack}

def Evm.pop (evm : Evm) : Except (Evm × String) (B256 × Evm) := do
  match evm.stack with
  | [] => .error ⟨evm, "StackUnderflowError"⟩
  | x :: xs => .ok ⟨x, {evm with stack := xs}⟩

def Evm.stackTop (evm : Evm) : Except (Evm × String) B256 := do
  match evm.stack with
  | [] => .error ⟨evm, "StackUnderflowError"⟩
  | x :: _ => .ok x

def Evm.stackTop6 (evm : Evm) :
  Except (Evm × String) (B256 × B256 × B256 × B256 × B256 × B256) := do
  match evm.stack with
  | x :: y :: z :: a :: b :: c :: _ => .ok ⟨x, y, z, a, b, c⟩
  | _ => .error ⟨evm, "StackUnderflowError"⟩

def Evm.pop' (evm : Evm) : Except (Evm × String) Evm := do
  match evm.stack with
  | [] => .error ⟨evm, "StackUnderflowError"⟩
  | _ :: xs => .ok {evm with stack := xs}

def Evm.pop6 (evm : Evm) : Except (Evm × String) Evm := do
  match evm.stack with
  | _ :: _ :: _ :: _ :: _ :: _ :: xs => .ok {evm with stack := xs}
  | _ => .error ⟨evm, "StackUnderflowError"⟩

def Prod.mapFst {α₁ : Type u₁} {α₂ : Type u₂} {β : Type v} (f : α₁ → α₂) : α₁ × β → α₂ × β :=
  Prod.map f id

def Evm.popToNat (evm : Evm) : Except (Evm × String) (Nat × Evm) :=
  evm.pop <&> Prod.mapFst B256.toNat

def Evm.popN (evm : Evm) : Nat → Except (Evm × String) (List B256 × Evm)
  | 0 => .ok ⟨[], evm⟩
  | n + 1 => do
    let ⟨x, evm⟩ ← evm.pop
    let ⟨xs, evm⟩ ← evm.popN n
    .ok ⟨x :: xs, evm⟩

abbrev Execution : Type := Except (Evm × String) Evm

def Evm.incrPc (evm : Evm) : Execution :=
  .ok {evm with pc := evm.pc + 1}

def Evm.update (evm : Evm) (cost : Nat)
  (out : B8L := evm.output)
  (adrs : AdrSet := evm.accessedAddresses)
  (logs : List Log := evm.logs)
  (keys : KeySet := evm.accessedStorageKeys) : Execution := do
  let gas ← (safeSub evm.gas_left cost).toExcept ⟨evm, "OutOfGasError"⟩
  .ok {
    evm with
    pc := evm.pc + 1
    gas_left := gas
    output := out
    logs := logs
    accessedAddresses := adrs
    accessedStorageKeys := keys
  }

def pushItem (x : B256) (c : Nat) (evm : Evm) : Execution := do
  chargeGas c evm >>= Evm.push x >>= Evm.incrPc

def gNewAccount : Nat := 25000
def GAS_SELF_DESTRUCT_NEW_ACCOUNT : Nat := 25000
def gasCallValue : Nat := 9000
def gCallStipend : Nat := 2300
def gasWarmAccess : Nat := 100
def gasColdAccountAccess : Nat := 2600
def gSelfdestruct : Nat := 5000
def gLog : Nat := 375
def gLogdata : Nat := 8
def gLogtopic : Nat := 375

def access_cost (x : Adr) (a : AdrSet) : Nat :=
  if x ∈ a then gasWarmAccess else gasColdAccountAccess

def addAccessedAddress (evm : Evm) (a : Adr) : Evm :=
  {evm with accessedAddresses := evm.accessedAddresses.insert a}

def addAccessedStorageKey (evm : Evm) (a : Adr) (k : B256) : Evm :=
  {evm with accessedStorageKeys := evm.accessedStorageKeys.insert ⟨a, k⟩}

def add_account_to_delete (evm : Evm) (a : Adr) : Evm :=
  {evm with accountsToDelete := evm.accountsToDelete.insert a}

def add_created_account (benv : Benv) (adr : Adr) : Benv :=
  {benv with createdAccounts := benv.createdAccounts.insert adr}

def Acct.empty : Acct :=
  {
    nonce := 0
    bal := 0
    stor := .empty
    code := ByteArray.mk #[]
  }

def Acct.Erasable (ac : Acct) : Prop :=
  ac.nonce = 0 ∧
  ac.bal = 0 ∧
  ac.stor.isEmpty = .true ∧
  ac.code.size = 0

instance {ac : Acct} : Decidable ac.Erasable := instDecidableAnd

def Wor.get (w : Wor) (a : Adr) : Acct := (w.find? a).getD .empty

def Wor.set (w : Wor) (a : Adr) (ac : Acct) : Wor :=
  if ac.Erasable then w.erase a else w.insert a ac

def Acct.Empty (a : Acct) : Prop :=
  a.code.size = 0 ∧ a.nonce = 0 ∧ a.bal = 0

instance {a : Acct} : Decidable a.Empty := by
 apply instDecidableAnd

def destroyAccount (w : Wor) (a : Adr) : Wor := w.erase a

abbrev AccountExists (wor : Wor) (adr : Adr) : Prop :=
  let acct := wor.get adr
  ¬ (acct.Empty ∧ acct.stor.isEmpty)

abbrev AccountExistsAndIsEmpty (wor : Wor) (adr : Adr) : Prop :=
  let acct := wor.get adr
  acct.Empty ∧ !acct.stor.isEmpty

def destroyTouchedEmptyAccounts
    (state : Wor) (touchedAccounts: AdrSet) : Wor :=
  let aux : Wor → Adr → Wor :=
    fun wor adr =>
      if AccountExistsAndIsEmpty wor adr
      then destroyAccount wor adr
      else wor
  touchedAccounts.fold aux state

def Tra.set (τ : Tra) (a : Adr) (s : Stor) : Tra :=
  if s.isEmpty then τ.erase a else τ.insert a s

def Wor.setCode (ω : Wor) (a : Adr) (cd : ByteArray) : Wor :=
  let ac := ω.get a
  ω.set a {ac with code := cd}

def Evm.getOrigAcct (evm : Evm) (a : Adr) : Acct :=
  evm.msg.benv.origState.get a

def Evm.getAcct (evm : Evm) (a : Adr) : Acct :=
  evm.msg.benv.state.get a

def Benv.setAcct (benv : Benv) (a : Adr) (ac : Acct) : Benv :=
  {benv with state := benv.state.set a ac}

def Msg.setAcct (msg : Msg) (a : Adr) (ac : Acct) : Msg :=
  {msg with benv := msg.benv.setAcct a ac}

def Evm.setAcct (evm : Evm) (a : Adr) (ac : Acct) : Evm :=
  {evm with msg := evm.msg.setAcct a ac}

def Evm.balAt (evm : Evm) (a : Adr) : B256 := (evm.getAcct a).bal
def Evm.codeAt (evm : Evm) (a : Adr) : ByteArray := (evm.getAcct a).code
def Evm.storValAt (evm : Evm) (adr : Adr) (key : B256) : B256 :=
  (evm.getAcct adr).stor.findD key 0

def Stor.set (s : Stor) (k v : B256) : Stor :=
  if v = 0 then s.erase k else s.insert k v

def Wor.setStorVal (wor : Wor) (adr : Adr) (key val : B256) : Wor :=
  let acct : Acct := wor.get adr
  wor.set adr {acct with stor := acct.stor.set key val}

def Benv.setStorVal (benv : Benv) (adr : Adr) (key val : B256) : Benv :=
  {benv with state := benv.state.setStorVal adr key val}

def Msg.setStorVal (msg : Msg) (adr : Adr) (key val : B256) : Msg :=
 {msg with benv := msg.benv.setStorVal adr key val}

def Evm.setStorVal (evm : Evm) (adr : Adr) (key val : B256) : Evm :=
  {evm with msg := evm.msg.setStorVal adr key val}

def Tra.setStorVal (tra : Tra) (adr : Adr) (key val : B256) : Tra :=
  let stor : Stor := tra.findD adr .empty
  tra.set adr <| stor.set key val

def Tenv.setTransVal (tenv : Tenv) (adr : Adr) (key val : B256) : Tenv :=
  {tenv with transientStorage := tenv.transientStorage.setStorVal adr key val}

def Msg.setTransVal (msg : Msg) (adr : Adr) (key val : B256) : Msg :=
  {msg with tenv := msg.tenv.setTransVal adr key val}

def Evm.setTransVal (evm : Evm) (adr : Adr) (key val : B256) : Evm :=
  {evm with msg := evm.msg.setTransVal adr key val}

def Evm.origStorValAt (evm : Evm) (adr : Adr) (key : B256) : B256 :=
  (evm.getOrigAcct adr).stor.findD key 0

def Evm.getTransVal (evm : Evm) (adr : Adr) (key : B256) : B256 :=
  (evm.msg.tenv.transientStorage.findD adr .empty).findD key 0

def memExtSize
  (current_size access_index access_size : Nat) : Nat :=
  if access_size = 0
  then current_size
  else
    32 *
    ( max
        (ceilDiv current_size 32)
        (ceilDiv (access_index + access_size) 32) )

def memExtsSize : Nat → List (Nat × Nat) → Nat
  | initSize, [] => initSize
  | initSize, ⟨accessIndex, accessSize⟩ :: pairs =>
    let expSize := memExtSize initSize accessIndex accessSize
    memExtsSize expSize pairs

def Evm.extCost (evm : Evm) (pairs : List (Nat × Nat)) : Nat :=
  let extSize := memExtsSize evm.memory.size pairs
  calculateMemoryGasCost extSize - calculateMemoryGasCost evm.memory.size

def ceil32 (n : Nat) : Nat :=
  match n % 32 with
  | 0 => n
  | m@(_ + 1) => n + 32 - m

def Mem'.write (μ : Mem') (n : ℕ) : B8L → Mem'
  | [] => μ
  | xs@(_ :: _) =>
    if n + xs.length ≤ μ.size
    then
      if n + xs.length ≤ μ.data.size
      then
        ⟨Array.writeD μ.data n xs, μ.size⟩
      else
        let blank : Array B8 := Array.mkArray (n + xs.length) 0x00
        ⟨Array.writeD (Array.copyD μ.data blank) n xs, μ.size⟩

    else
      let newSize := ceil32 (n + xs.length)
      let blank : Array B8 := Array.mkArray newSize 0x00
      ⟨Array.writeD (Array.copyD μ.data blank) n xs, newSize⟩

def Mem'.extend (μ : Mem') (index size : Nat) : Mem' :=
  ⟨μ.data, memExtSize μ.size index size⟩

def Mem'.extends (μ : Mem') (pairs : List (Nat × Nat)) : Mem' :=
  ⟨μ.data, memExtsSize μ.size pairs⟩

def Mem'.read (μ : Mem') (index size : ℕ) : B8L × Mem' :=
  ⟨μ.data.sliceD index size 0, μ.extend index size⟩

def Dead (w : Wor) (a : Adr) : Prop :=
  match w.find? a with
  | none => True
  | some x => x.Empty

def Evm.memWrite (evm : Evm) (idx : Nat) (val : B8L) : Evm :=
  {evm with memory := evm.memory.write idx val}

def Evm.memRead (evm : Evm) (index size : Nat) : B8L × Evm :=
  let ⟨val, mem⟩ := evm.memory.read index size
  ⟨val, {evm with memory := mem}⟩

def Evm.memExtend (evm : Evm) (index size : Nat) : Evm :=
  let mem := evm.memory.extend index size
  {evm with memory := mem}

def Evm.memExtends (evm : Evm) (pairs : List (Nat × Nat)) : Evm :=
  let mem := evm.memory.extends pairs
  {evm with memory := mem}

def Evm.addLog (evm : Evm) (log : Log) : Evm :=
  {evm with logs := log :: evm.logs}

def applyUnary (f : B256 → B256) (cost : Nat) (evm : Evm) : Execution := do
  let ⟨x, evm⟩ ← evm.pop
  pushItem (f x) cost evm

def applyBinary (f : B256 → B256 → B256)
  (cost : Nat) (evm : Evm) : Execution := do
  let ⟨x, evm⟩ ← evm.pop
  let ⟨y, evm⟩ ← evm.pop
  pushItem (f x y) cost evm

def applyTernary (f : B256 → B256 → B256 → B256)
  (cost : Nat) (evm : Evm) : Execution := do
  let ⟨x, evm⟩ ← evm.pop
  let ⟨y, evm⟩ ← evm.pop
  let ⟨z, evm⟩ ← evm.pop
  pushItem (f x y z) cost evm

def List.swap : List ξ → Nat → Option (List ξ)
  | [], _ => none
  | x :: xs, k => do
    let y ← xs.get? k
    let ys := xs.set k x
    .some (y :: ys)

def Evm.contract (evm : Evm) : Adr := evm.msg.currentTarget

def Evm.assertDynamic (evm : Evm) : Except (Evm × String) Unit :=
  Except.assert (!evm.msg.isStatic) ⟨evm, s!"WriteInStaticContext"⟩

def Rinst.run (evm : Evm) : Rinst → Execution
  | .address => pushItem evm.contract.toB256 gBase evm
  | .basefee => pushItem evm.msg.benv.baseFeePerGas.toB256 gBase evm
  | .blobhash => do
    let ⟨x, evm⟩ ← evm.pop
    let y : B256 := evm.msg.tenv.blobVersionedHashes.getD x.toNat 0
    chargeGas gHashopcode evm >>= Evm.push y >>= Evm.incrPc
  | .blobbasefee => do
    let fee := calculate_blob_gas_price evm.msg.benv.excessBlobGas
    pushItem fee.toB256 gBase evm
  | .balance => do
    let ⟨x, evm⟩ ← evm.pop
    let a := x.toAdr
    let evm ←
      if a ∈ evm.accessedAddresses
      then chargeGas gasWarmAccess evm
      else chargeGas gasColdAccountAccess (addAccessedAddress evm a)
    evm.push (evm.balAt a) >>= Evm.incrPc
  | .origin => pushItem evm.msg.tenv.origin.toB256 gBase evm
  | .caller => pushItem evm.msg.caller.toB256 gBase evm
  | .callvalue => pushItem evm.msg.value gBase evm
  | .calldataload => do
    let ⟨start_index, evm⟩ ← evm.pop
    let evm ← chargeGas gVerylow evm
    let value := B8L.toB256P <| evm.msg.data.sliceD start_index.toNat 32 0
    evm.push value >>= Evm.incrPc
  | .calldatasize => pushItem evm.msg.data.length.toB256 gBase evm
  | .calldatacopy => do
    let ⟨memory_start_index, evm⟩ ← evm.popToNat
    let ⟨data_start_index, evm⟩ ← evm.popToNat
    let ⟨size, evm⟩ ← evm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := GAS_COPY * words
    let extend_memory_cost := evm.extCost [⟨memory_start_index, size⟩]
    let evm ← chargeGas (gVerylow + copy_gas_cost + extend_memory_cost) evm
    let value := evm.msg.data.sliceD data_start_index size 0
    let evm := evm.memWrite memory_start_index value
    evm.incrPc
  | .codesize => pushItem evm.msg.code.size.toB256 gBase evm
  | .codecopy => do
    let ⟨memory_start_index, evm⟩ ← evm.popToNat
    let ⟨code_start_index, evm⟩ ← evm.popToNat
    let ⟨size, evm⟩ ← evm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := GAS_COPY * words
    let extend_memory_cost := evm.extCost [⟨memory_start_index, size⟩]
    let evm ← chargeGas (gVerylow + copy_gas_cost + extend_memory_cost) evm
    let value := evm.code.sliceD code_start_index size (Linst.toB8 .stop)
    .ok {
      evm with
      pc := evm.pc + 1
      memory := evm.memory.write memory_start_index value
    }
  | .gasprice => pushItem evm.msg.tenv.gasPrice.toB256 gBase evm
  | .extcodesize => do
    let ⟨address_word, evm⟩ ← evm.pop
    let address := address_word.toAdr
    let evm ←
      if address ∈ evm.accessedAddresses
      then chargeGas gasWarmAccess evm
      else chargeGas gasColdAccountAccess (addAccessedAddress evm address)
    let codesize := (evm.codeAt address).size.toB256
    evm.push codesize >>= Evm.incrPc
  | .extcodecopy => do
    let ⟨address_word, evm⟩ ← evm.pop
    let address : Adr := address_word.toAdr
    let ⟨memory_start_index, evm⟩ ← evm.popToNat
    let ⟨code_start_index, evm⟩ ← evm.popToNat
    let ⟨size, evm⟩ ← evm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := GAS_COPY * words
    let extend_memory_cost := evm.extCost [⟨memory_start_index, size⟩]
    let evm ←
      if address ∈ evm.accessedAddresses
      then chargeGas (gasWarmAccess + copy_gas_cost + extend_memory_cost) evm
      else
        chargeGas
          (gasColdAccountAccess + copy_gas_cost + extend_memory_cost)
          (addAccessedAddress evm address)
    let code := evm.codeAt address
    let value := code.sliceD code_start_index size (Linst.toB8 .stop)
    .ok {
      evm with
      pc := evm.pc + 1
      memory := evm.memory.write memory_start_index value
    }
  | .retdatasize => pushItem evm.return_data.length.toB256 gBase evm
  | .retdatacopy => do
    let ⟨memory_start_index, evm⟩ ← evm.popToNat
    let ⟨return_data_start_index, evm⟩ ← evm.popToNat
    let ⟨size, evm⟩ ← evm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := gReturnDataCopy * words
    let extend_memory_cost := evm.extCost [⟨memory_start_index, size⟩]
    let evm ← chargeGas (gVerylow + copy_gas_cost + extend_memory_cost) evm

    .assertNot
      (evm.return_data.length < return_data_start_index + size)
      ⟨evm, "OutOfBoundsRead"⟩

    let value :=
      evm.return_data.sliceD return_data_start_index size 0
    .ok {
      evm with
      pc := evm.pc + 1
      memory := evm.memory.write memory_start_index value
    }
  | .extcodehash => do
    let ⟨address_word, evm⟩ ← evm.pop
    let address : Adr := address_word.toAdr
    let evm ←
      if address ∈ evm.accessedAddresses
      then chargeGas gasWarmAccess evm
      else chargeGas gasColdAccountAccess (addAccessedAddress evm address)
    let account := evm.getAcct address
    let codehash : B256 :=
      if account.Empty
      then 0
      else ByteArray.keccak 0 account.code.size account.code
    evm.push codehash >>= Evm.incrPc
  | .selfbalance => pushItem (evm.balAt evm.contract) gLow evm
  | .chainid => pushItem evm.msg.benv.chainId.toB256 gBase evm
  | .number => pushItem evm.msg.benv.number.toB256 gBase evm
  | .timestamp => pushItem evm.msg.benv.time gBase evm
  | .gaslimit => pushItem evm.msg.benv.blockGasLimit.toB256 gBase evm
  | .prevrandao => pushItem evm.msg.benv.prevRandao gBase evm
  | .coinbase => pushItem evm.msg.benv.coinbase.toB256 gBase evm
  | .msize => pushItem evm.memory.size.toB256 gBase evm
  | .mload => do
    let ⟨start_index, evm⟩ ← evm.popToNat
    let extend_memory_cost := evm.extCost [⟨start_index, 32⟩]
    let evm ← chargeGas (gVerylow + extend_memory_cost) evm
    let ⟨value, evm⟩  := evm.memRead start_index 32
    evm.push (B8L.toB256P value) >>= Evm.incrPc
  | .mstore => do
    -- let ⟨start_index, evm⟩ ← evm.popToNat
    let start_index ← evm.stackTop <&> B256.toNat
    let mut evm ← evm.pop'

    -- let ⟨value, evm⟩ ← evm.pop
    let value ← evm.stackTop
    evm ← evm.pop'

    let extend_memory_cost := evm.extCost [⟨start_index, 32⟩]
    evm ← chargeGas (gVerylow + extend_memory_cost) evm
    evm := evm.memWrite start_index value.toB8L
    evm.incrPc -- <| evm.memWrite start_index value.toB8L

  | .mstore8 => do
    let ⟨start_index, evm⟩ ← evm.popToNat
    let ⟨value, evm⟩ ← evm.pop
    let extend_memory_cost := evm.extCost [⟨start_index, 1⟩]
    let evm ← chargeGas (gVerylow + extend_memory_cost) evm
    let evm := evm.memWrite start_index [value.2.2.toUInt8]
    Evm.incrPc evm
  | .gas => do
    let evm ← chargeGas gBase evm
    evm.push evm.gas_left.toB256 >>= Evm.incrPc
  | .eq => applyBinary .eq_check gVerylow evm
  | .lt => applyBinary .lt_check gVerylow evm
  | .gt => applyBinary .gt_check gVerylow evm
  | .slt => applyBinary .slt_check gVerylow evm
  | .sgt => applyBinary .sgt_check gVerylow evm
  | .iszero => applyUnary (.eq_check · 0) gVerylow evm
  | .not => applyUnary (~~~ ·) gVerylow evm
  | .and => applyBinary B256.and gVerylow evm
  | .or => applyBinary B256.or gVerylow evm
  | .xor => applyBinary B256.xor gVerylow evm
  | .signextend => applyBinary B256.signext gLow evm
  | .pop => (evm.pop <&> Prod.snd) >>= chargeGas gBase >>= Evm.incrPc
  | .byte =>
    applyBinary (λ x y => (List.getD y.toB8L x.toNat 0).toB256) gVerylow evm
  | .shl => applyBinary (fun x y => y <<< x.toNat) gVerylow evm
  | .shr => applyBinary (fun x y => y >>> x.toNat) gVerylow evm
  | .sar => applyBinary (fun x y => B256.arithShiftRight y x.toNat) gVerylow evm
  | .kec => do
    let ⟨memory_start_index, evm⟩ ← evm.popToNat
    let ⟨size, evm⟩ ← evm.popToNat
    let words := ceilDiv size 32
    let word_gas_cost := GAS_KECCAK256_WORD * words
    let extend_memory_cost := evm.extCost [⟨memory_start_index, size⟩]
    let evm ← chargeGas (gKeccak256 + word_gas_cost + extend_memory_cost) evm

    let ⟨arg, evm⟩ := evm.memRead memory_start_index size
    --let hash := B8a.keccak memory_start_index size evm.memory

    evm.push arg.keccak >>= Evm.incrPc
  | .sub => applyBinary (· - ·) gVerylow evm
  | .mul => applyBinary (· * ·) gLow evm
  | .exp => do
    let ⟨base, evm⟩ ← evm.pop
    let ⟨exponent, evm⟩ ← evm.pop
    let evm ← chargeGas (gExp + (gExpbyte * exponent.bytecount)) evm
    evm.push (B256.bexp base exponent) >>= Evm.incrPc
  | .div => applyBinary (· / ·) gLow evm
  | .sdiv => applyBinary B256.sdiv gLow evm
  | .mod => applyBinary (· % ·) gLow evm
  | .smod => applyBinary B256.smod gLow evm
  | .add => applyBinary (· + ·) gVerylow evm
  | .addmod => applyTernary B256.addmod gMid evm
  | .mulmod => applyTernary B256.mulmod gMid evm
  | .swap n => do
    let evm ← chargeGas gVerylow evm
    match List.swap evm.stack n with
    | none => .error ⟨evm, "StackUnderflowError"⟩
    | some stack =>
      .ok {
        evm with
        pc := evm.pc + 1
        stack := stack
      }
  | .dup n => do
    let evm ← chargeGas gVerylow evm
    match evm.stack.get? n with
    | none => .error ⟨evm, "StackUnderflowError"⟩
    | some word => evm.push word >>= Evm.incrPc
  | .sload => do
    let ⟨key, evm⟩ ← evm.pop
    let ct := evm.contract
    let evm ←
      if ⟨ct, key⟩ ∈ evm.accessedStorageKeys
      then chargeGas gasWarmAccess evm
      else
        chargeGas GAS_COLD_SLOAD
          (addAccessedStorageKey evm ct key)
    evm.push (evm.storValAt ct key) >>= Evm.incrPc
  | .tload => do
    let ⟨key, evm⟩ ← evm.pop
    pushItem (evm.getTransVal evm.contract key) gasWarmAccess evm
  | .pc => pushItem evm.pc.toB256 gBase evm
  | .sstore => do
    let ⟨key, evm⟩ ← evm.pop
    let ⟨new_value, evm⟩ ← evm.pop
    let mut evm : Evm := evm

    .assert
      (gCallStipend < evm.gas_left)
      ⟨evm, "OutOfGasError"⟩
    let ct := evm.contract

    let original_value := evm.origStorValAt ct key
    let current_value := evm.storValAt ct key

    let mut gas_cost := 0

    if ⟨ct, key⟩ ∉ evm.accessedStorageKeys
      then
        evm := addAccessedStorageKey evm ct key
        gas_cost := gas_cost + GAS_COLD_SLOAD

    if original_value = current_value ∧ current_value ≠ new_value
      then
        if original_value = 0
        then gas_cost := gas_cost + GAS_STORAGE_SET
        else gas_cost := gas_cost + (gasStorageUpdate - GAS_COLD_SLOAD)
      else gas_cost := gas_cost + gasWarmAccess

    if current_value ≠ new_value
    then
      if original_value ≠ 0 ∧ current_value ≠ 0 ∧ new_value = 0
        then evm := {evm with refund_counter := evm.refund_counter + rSClear}
      if original_value ≠ 0 ∧ current_value = 0
        then evm := {evm with refund_counter := evm.refund_counter - rSClear}
      if original_value = new_value
        then
          if original_value = 0
          then
            evm := {
              evm with
              refund_counter := evm.refund_counter + (GAS_STORAGE_SET - gasWarmAccess)
            }
          else
            evm := {
              evm with
              refund_counter :=
                evm.refund_counter + (gasStorageUpdate - GAS_COLD_SLOAD - gasWarmAccess)
            }

    evm ← chargeGas gas_cost evm
    evm.assertDynamic
    (evm.setStorVal evm.contract key new_value).incrPc

  | .tstore => do
    let ⟨key, evm⟩ ← evm.pop
    let ⟨new_value, evm⟩ ← evm.pop
    let evm ← chargeGas gasWarmAccess evm
    evm.assertDynamic
    (evm.setTransVal evm.contract key new_value).incrPc
  | .mcopy => do
    let ⟨destination, evm⟩ ← evm.popToNat
    let ⟨source, evm⟩ ← evm.popToNat
    let ⟨length, evm⟩ ← evm.popToNat
    let words := ceilDiv length 32
    let copy_gas_cost := GAS_COPY * words
    let extend_memory_cost :=
      evm.extCost [⟨source, length⟩, ⟨destination, length⟩]
    let evm ← chargeGas (gVerylow + copy_gas_cost + extend_memory_cost) evm
    let ⟨value, evm⟩ := evm.memRead source length
    (evm.memWrite destination value).incrPc
  | .log n => do
    let ⟨memory_start_index, evm⟩ ← evm.popToNat
    let ⟨size, evm⟩ ← evm.popToNat
    let ⟨topics, evm⟩ ← evm.popN n
    let extend_memory_cost := evm.extCost [⟨memory_start_index, size⟩]
    let evm ←
      chargeGas
        (gLog + (gLogdata * size) + (gLogtopic * n) + extend_memory_cost)
        evm
    evm.assertDynamic
    let ⟨data, evm⟩ := evm.memRead memory_start_index size
    let log : Log := ⟨evm.contract, topics, data⟩
    (evm.addLog log).incrPc
  | .blockhash => do
    let ⟨blockNumberWord, evm⟩ ← evm.pop
    let blockNumber := blockNumberWord.toNat
    let evm ← chargeGas gBlockhash evm
    let maxBlockNumber := blockNumber + 256
    let hash : B256 :=
      if evm.msg.benv.number ≤ blockNumber ∨ maxBlockNumber < evm.msg.benv.number
      then 0
      else
        evm.msg.benv.blockHashes.getD
          (evm.msg.benv.blockHashes.length - (evm.msg.benv.number - blockNumber))
          0
    evm.push hash >>= Evm.incrPc

instance : Inhabited Benv := ⟨
  {
    chainId := 0
    state := .empty
    origState := .empty
    createdAccounts := .empty
    blockGasLimit := 0
    blockHashes := []
    coinbase := 0
    number := 0
    baseFeePerGas := 0
    time := 0
    prevRandao := 0
    excessBlobGas := 0
    parentBeaconBlockRoot := 0
  }
⟩

instance : Inhabited Tenv := ⟨
  {
    origin := 0
    gasPrice := 0
    gas := 0
    accessListAddresses := .empty
    accessListStorageKeys := .empty
    transientStorage := .empty
    blobVersionedHashes := []
    auths := []
    indexInBlock := none
    txHash := none
  }
⟩

instance : Inhabited Msg :=
  ⟨
    {
      benv := default
      tenv := default
      caller := 0
      target := .none
      currentTarget := 0
      gas := 0
      value := 0
      data := []
      codeAddress := .none
      code := .empty
      depth := 0
      shouldTransferValue := false
      isStatic := false
      accessedAddresses := .empty
      accessedStorageKeys := .empty
      disablePrecompiles := false
    }
  ⟩

instance : Inhabited Evm := ⟨
  {
    pc := 0
    stack := []
    memory := ⟨.empty, 0⟩
    code := .empty
    gas_left := 0
    logs := []
    refund_counter := 0
    msg := default
    output := []
    accountsToDelete := .empty
    return_data := []
    error := .none
    accessedAddresses := .empty
    accessedStorageKeys := .empty
  }
⟩

instance : Inhabited Execution := ⟨.ok default⟩


def noPushBefore (cd : ByteArray) : Nat → Nat → Bool
  | 0, _ => true
  | _, 0 => true
  | k + 1, m + 1 =>
    if k < cd.size
    then let b := cd.get! k
         if (b < (0x7F - m.toUInt8) || 0x7F < b)
         then noPushBefore cd k m
         else if noPushBefore cd k 32
              then false
              else noPushBefore cd k m
    else noPushBefore cd k m

def jumpable (cd : ByteArray) (k : Nat) : Bool :=
  if cd.get! k = (Jinst.toB8 .jumpdest)
  then noPushBefore cd k 32
  else false

def Jinst.run (evm : Evm) : Jinst → Execution
  | .jumpdest => chargeGas gJumpdest evm >>= Evm.incrPc
  | .jump => do
    let ⟨jump_dest, evm⟩ ← evm.pop
    let evm ← chargeGas gMid evm
    .assert
      (jumpable evm.code jump_dest.toNat)
      ⟨evm, "InvalidJumpDestError"⟩
    .ok {evm with pc := jump_dest.toNat}
  | .jumpi => do
    let ⟨dest, evm⟩ ← evm.pop
    let ⟨cond, evm⟩ ← evm.pop
    let evm ← chargeGas gHigh evm
    let pc ←
      if cond = 0
      then .ok <| evm.pc + 1
      else
        .assert
          (jumpable evm.code dest.toNat)
          ⟨evm, "InvalidJumpDestError"⟩
        .ok dest.toNat
    .ok {evm with pc := pc}

def Wor.subBal (wor : Wor) (adr : Adr) (val : B256) : Option Wor :=
  let acct := wor.get adr
  if acct.bal < val
  then .none
  else wor.set adr {acct with bal := acct.bal - val}

def Wor.addBal (wor : Wor) (adr : Adr) (val : B256) : Wor :=
  let acct := wor.get adr
  wor.set adr {acct with bal := acct.bal + val}

def Wor.addIntBal (wor : Wor) (adr : Adr) (val : Int) : Option Wor :=
  let absVal := val.natAbs.toB256
  if val < 0
  then wor.subBal adr absVal
  else .some <| wor.addBal adr absVal

def Wor.setBal (wor : Wor) (adr : Adr) (val : B256) : Wor :=
  let acct := wor.get adr
  wor.set adr {acct with bal := val}

def Benv.setBal (benv : Benv) (adr : Adr) (val : B256) : Benv :=
  {benv with state := benv.state.setBal adr val}

def Benv.subBal (benv : Benv) (adr : Adr) (val : B256) : Option Benv := do
  let wor ← benv.state.subBal adr val
  some {benv with state := wor}

def Benv.addBal (benv : Benv) (adr : Adr) (val : B256) : Benv :=
  {benv with state := benv.state.addBal adr val}

def Msg.setBal (msg : Msg) (adr : Adr) (val : B256) : Msg :=
  {msg with benv := msg.benv.setBal adr val}

def Evm.setBal (evm : Evm) (adr : Adr) (val : B256) : Evm :=
  {evm with msg := evm.msg.setBal adr val}

def Msg.subBal (msg : Msg) (adr : Adr) (val : B256) : Option Msg := do
  let benv ← msg.benv.subBal adr val
  some {msg with benv := benv}

def Evm.subBal (evm : Evm) (adr : Adr) (val : B256) : Option Evm := do
  let msg ← evm.msg.subBal adr val
  some {evm with msg := msg}

def Msg.addBal (msg : Msg) (adr : Adr) (val : B256) : Msg :=
  {msg with benv := msg.benv.addBal adr val}

def Evm.addBal (evm : Evm) (adr : Adr) (val : B256) : Evm :=
  {evm with msg := evm.msg.addBal adr val}

def Linst.run (evm : Evm) : Linst → Execution
  | .stop => .ok {evm with pc := evm.pc + 1}
  | .rev => do
    let ⟨memory_start_index, evm⟩ ← evm.popToNat
    let ⟨size, evm⟩ ← evm.popToNat
    let extend_memory_cost := evm.extCost [⟨memory_start_index, size⟩]
    let evm ← chargeGas extend_memory_cost evm
    let ⟨output, evm⟩ := evm.memRead memory_start_index size
    let evm := {evm with output := output}
    .error ⟨evm, "Revert"⟩
  | .ret => do
    let ⟨index, evm⟩ ← evm.popToNat
    let ⟨size, evm⟩ ← evm.popToNat

    let cost := evm.extCost [⟨index, size⟩]

    let evm ← chargeGas cost evm
    let ⟨output, evm⟩ := evm.memRead index size
    .ok {evm with output := output}
  | .dest => do
    let donor := evm.contract
    let ⟨donee, evm⟩ ← evm.pop <&> Prod.mapFst B256.toAdr
    let donorBal := (evm.getAcct evm.contract).bal

    let mut gas_cost := gSelfdestruct
    let mut evm := evm

    if donee ∉ evm.accessedAddresses
      then
        evm := addAccessedAddress evm donee
        gas_cost := gas_cost + gasColdAccountAccess

    if (evm.getAcct donee).Empty ∧ donorBal ≠ 0
      then gas_cost := gas_cost + GAS_SELF_DESTRUCT_NEW_ACCOUNT

    evm ← chargeGas gas_cost evm

    evm.assertDynamic

    evm ←
      (evm.subBal donor donorBal).toExcept
        ⟨evm, "ERROR : InsufficientBalanceError"⟩
    evm := evm.addBal donee donorBal

    if donor ∈ evm.msg.benv.createdAccounts
      then evm := add_account_to_delete (evm.setBal donor 0) donor

    .ok evm

def except64th (n : Nat) : Nat := n - (n / 64)

def calculate_msg_call_gas
  (value gas gas_left memory_cost extra_gas : Nat)
  (cs : Nat := gCallStipend) : Nat × Nat :=
  let call_stipend : Nat := if value = 0 then 0 else cs

  if gas_left < extra_gas + memory_cost
  then ⟨gas + extra_gas, gas + call_stipend⟩
  else
    let gas' := min gas (except64th (gas_left - memory_cost - extra_gas))
    ⟨gas' + extra_gas, gas' + call_stipend⟩

def ECRECOVER_ADDRESS : Adr := 0x01
def SHA256_ADDRESS : Adr := 0x02
def RIPEMD160_ADDRESS : Adr := 0x03
def IDENTITY_ADDRESS : Adr := 0x04
def MODEXP_ADDRESS : Adr := 0x05
def ALT_BN128_ADD_ADDRESS : Adr := 0x06
def ALT_BN128_MUL_ADDRESS : Adr := 0x07
def ALT_BN128_PAIRING_CHECK_ADDRESS : Adr := 0x08
def BLAKE2F_ADDRESS : Adr := 0x09
def POINT_EVALUATION_ADDRESS : Adr := 0x0a

def incorporateChildOnError (parent child : Evm) (returnData : B8L) : Evm :=
  {
    parent with
    gas_left := parent.gas_left + child.gas_left
    msg := {
      parent.msg with
      benv := child.msg.benv
      tenv := child.msg.tenv
    },
    return_data := returnData
  }

def incorporateChildOnSuccess (parent child : Evm) (returnData : B8L) : Evm :=
  {
    parent with
    gas_left := parent.gas_left + child.gas_left
    msg := {
      parent.msg with
      benv := child.msg.benv
      tenv := child.msg.tenv
    },
    logs := child.logs ++ parent.logs
    refund_counter := parent.refund_counter + child.refund_counter
    accountsToDelete := parent.accountsToDelete.union child.accountsToDelete
    return_data := returnData
    accessedAddresses := parent.accessedAddresses.union child.accessedAddresses
    accessedStorageKeys := parent.accessedStorageKeys.union child.accessedStorageKeys
  }

def compute_contract_address (sender : Adr) (nonce : B64) : Adr :=
  let LA : B8L :=
    BLT.encode <| .list [.b8s sender.toB8L, .b8s nonce.toB8L.sig]
  (B8L.keccak LA).toAdr

def create2NewAddress
  (sender : Adr) (salt : B256) (initCode : B8L): Adr :=
  let LA : B8L :=
    (0xFF : B8) :: (sender.toB8L ++ salt.toB8L ++ initCode.keccak.toB8L)
  (B8L.keccak LA).toAdr

def Wor.incrNonce (w : Wor) (a : Adr) : Wor :=
  let ac := w.get a
  let ac' : Acct := {ac with nonce := ac.nonce + 1}
  w.set a ac'

def Msg.incrNonce (msg : Msg) (adr : Adr) : Msg :=
  {
    msg with
    benv := {
      msg.benv with
      state := msg.benv.state.incrNonce adr
    }
  }

def Evm.incrNonce (evm : Evm) (adr : Adr) : Evm :=
  {evm with msg := evm.msg.incrNonce adr}

def Benv.incrNonce (benv : Benv) (adr : Adr) : Benv :=
  {benv with state := benv.state.incrNonce adr}

def Wor.setStor (w : Wor) (a : Adr) (s : Stor) : Wor :=
  let ac := (w.get a)
  w.set a {ac with stor := s}

def Benv.setStor (benv : Benv) (adr : Adr) (stor : Stor) : Benv :=
  {benv with state := benv.state.setStor adr stor}

def Evm.setBenv (evm : Evm) (benv : Benv) : Evm :=
  {evm with msg := {evm.msg with benv := benv}}

def Msg.setStor (msg : Msg) (adr : Adr) (stor : Stor) : Msg :=
  {msg with benv := msg.benv.setStor adr stor}

def Evm.setStor (evm : Evm) (adr : Adr) (stor : Stor) : Evm :=
  {evm with msg := evm.msg.setStor adr stor}

def Msg.setCode (msg : Msg) (adr : Adr) (code : ByteArray) : Msg :=
  {msg with benv := {msg.benv with state := msg.benv.state.setCode adr code}}

def Evm.setCode (evm : Evm) (adr : Adr) (code : ByteArray) : Evm :=
  {evm with msg := evm.msg.setCode adr code}

def Evm.rollback (evm : Evm) (wor : Wor) (tra : Tra) : Evm :=
  {
    evm with
    msg := {
      evm.msg with
      benv := {
        evm.msg.benv with
        state := wor
      },
      tenv := {
        evm.msg.tenv with
        transientStorage := tra
      }
    }
  }

def liftToExecution (evm : Evm)
  (f : Except (Benv × Tenv × String) Evm) : Execution := do
  match f with
  | .error ⟨benv, tenv, ex⟩ =>
    let evm' := {
      evm with
      msg := {
        evm.msg with
        benv := benv
        tenv := tenv
      }
    }
    .error ⟨evm', ex⟩
  | .ok evm => .ok evm

def GAS_ECRECOVER : Nat := 3000

def executeEcrecover (evm : Evm) : Execution := do
  let data := evm.msg.data
  let evm ← chargeGas GAS_ECRECOVER evm
  let h := B8L.toB256P <| data.sliceD 0 32 (0x00 : B8)
  let (some v : Option Bool) ←
    .ok
      ( match (B8L.toB256P <| data.sliceD 32 32 (0x00 : B8)) with
        | 0x1B => some false
        | 0x1C => some true
        | _ => .none ) | .ok evm
  let r := B8L.toB256P <| data.sliceD 64 32 (0x00 : B8)
  let s := B8L.toB256P <| data.sliceD 96 32 (0x00 : B8)
  if r = 0 ∨ r ≥ .secp256k1n ∨ s = 0 ∨ s ≥ .secp256k1n
  then .ok evm
  else
    match ecrecover h v r s with
    | .none => .ok evm
    | some adr => .ok {evm with output := adr.toB256.toB8L}

def executeSha256 (evm : Evm) : Execution := do
  let data := evm.msg.data
  let cost : Nat := 60 + (12 * (ceilDiv data.length 32))
  let evm ← chargeGas cost evm
  .ok {evm with output := (B8L.sha256 data).toB8L}

def executeRipemd160 (evm : Evm) : Execution := do
  let data := evm.msg.data
  let cost : Nat := 600 + (120 * (ceilDiv data.length 32))
  let evm ← chargeGas cost evm
  let output : B8L := B256.toB8L <| B8L.toB256P <| (rip160 ⟨.mk data⟩).toList
  .ok {evm with output := output}

def executeId (evm : Evm) : Execution := do
  let data := evm.msg.data
  let cost := 15 + (3 * (ceilDiv data.length 32))
  let evm ← chargeGas cost evm
  .ok {evm with output := data}

def B8L.sliceToNat (data : B8L) (start : Nat) (length : Nat) : Nat :=
  match data.drop start with
  | [] => 0
  | tail@(_ :: _)=>
    if tail.length < length
    then
      if tail.all (· = 0)
      then 0
      else B8L.toNat <| tail.takeD length (0 : B8)
    else B8L.toNat <| tail.take length

/-
def complexity(base_length: U256, modulus_length: U256) -> Uint:
    """
    Estimate the complexity of performing a modular exponentiation.

    Parameters
    ----------

    base_length :
        Length of the array representing the base integer.

    modulus_length :
        Length of the array representing the modulus integer.

    Returns
    -------

    complexity : `Uint`
        Complexity of performing the operation.
    """
    max_length = max(Uint(base_length), Uint(modulus_length))
    words = (max_length + Uint(7)) // Uint(8)
    return words ** Uint(2)
-/
def modexpComplexity
  (baseLength modulusLength : Nat) : Nat :=
  let maxLength := max baseLength modulusLength
  let words := ceilDiv maxLength 8
  words ^ 2

/-
def iterations(exponent_length: U256, exponent_head: Uint) -> Uint:
    """
    Calculate the number of iterations required to perform a modular
    exponentiation.

    Parameters
    ----------

    exponent_length :
        Length of the array representing the exponent integer.

    exponent_head :
        First 32 bytes of the exponent (with leading zero padding if it is
        shorter than 32 bytes), as an unsigned integer.

    Returns
    -------

    iterations : `Uint`
        Number of iterations.
    """
-/
def modexpIterations (expLength : Nat) (expHead : Nat) : Nat :=

/-
    if exponent_length <= U256(32) and exponent_head == U256(0):
        count = Uint(0)
    elif exponent_length <= U256(32):
        bit_length = Uint(exponent_head.bit_length())

        if bit_length > Uint(0):
            bit_length -= Uint(1)

        count = bit_length
    else:
        length_part = Uint(8) * (Uint(exponent_length) - Uint(32))
        bits_part = Uint(exponent_head.bit_length())

        if bits_part > Uint(0):
            bits_part -= Uint(1)

        count = length_part + bits_part

    return max(count, Uint(1))
-/
  let bitsPart : Nat := (Nat.log2 expHead)
  let count :=
    if expLength ≤ 32
    then
      if expHead = 0
      then 0
      else
        bitsPart
    else
      let lengthPart := 8 * (expLength - 32)
      lengthPart + bitsPart

  max count 1


/-
def gas_cost(
    base_length: U256,
    modulus_length: U256,
    exponent_length: U256,
    exponent_head: Uint,
) -> Uint:
    """
    Calculate the gas cost of performing a modular exponentiation.

    Parameters
    ----------

    base_length :
        Length of the array representing the base integer.

    modulus_length :
        Length of the array representing the modulus integer.

    exponent_length :
        Length of the array representing the exponent integer.

    exponent_head :
        First 32 bytes of the exponent (with leading zero padding if it is
        shorter than 32 bytes), as an unsigned integer.

    Returns
    -------

    gas_cost : `Uint`
        Gas required for performing the operation.
    """
-/
def modexpGascost
  (baseLength modulusLength expLength expHead : Nat) : Nat :=

/-
    multiplication_complexity = complexity(base_length, modulus_length)
    iteration_count = iterations(exponent_length, exponent_head)
-/
  let mulComplexity := modexpComplexity baseLength modulusLength
  let iterationCount := modexpIterations expLength expHead

/-
    cost = multiplication_complexity * iteration_count
    cost //= GQUADDIVISOR
    return max(Uint(200), cost)
-/
  let cost := (mulComplexity * iterationCount) / 3
  max 200 cost


def executeModexp (evm : Evm) : Execution := do

  let data := evm.msg.data
  let baseLength : Nat := B8L.sliceToNat data 0 32
  let expLength : Nat := B8L.sliceToNat data 32 32
  let modulusLength : Nat := B8L.sliceToNat data 64 32
  let expHead : Nat := B8L.sliceToNat data (96 + baseLength) (min 32 expLength)
  let cost : Nat := modexpGascost baseLength modulusLength expLength expHead

  let evm ← chargeGas cost evm

  if baseLength = 0 ∧ modulusLength = 0
    then return {evm with output := []}

  let base : Nat := B8L.sliceToNat data 96 baseLength
  let exp : Nat := B8L.sliceToNat data (96 + baseLength) expLength
  let modulus : Nat := B8L.sliceToNat data (96 + baseLength + expLength) modulusLength

  let output :=
    if modulus = 0
    then List.replicate modulusLength (0x00 : B8)
    else (Nat.powMod base exp modulus).toB8L.pack modulusLength

  .ok {evm with output := output}

def executeEcadd (evm : Evm) : Execution := do
  let data := evm.msg.data
  let evm ← chargeGas 150 evm
  let x0 : Nat := B8L.toNat <| data.sliceD 0 32 (0 : B8)
  let y0 : Nat := B8L.toNat <| data.sliceD 32 32 (0 : B8)
  let x1 : Nat := B8L.toNat <| data.sliceD 64 32 (0 : B8)
  let y1 : Nat := B8L.toNat <| data.sliceD 96 32 (0 : B8)

  .assert
    ( x0 < altBn128Prime ∧ y0 < altBn128Prime ∧
      x1 < altBn128Prime ∧ x1 < altBn128Prime )
    ⟨evm, "OutOfGasError"⟩

  let p0 ← (BNP.mk? x0 y0).toExcept ⟨evm, "OutOfGasError"⟩
  let p1 ← (BNP.mk? x1 y1).toExcept ⟨evm, "OutOfGasError"⟩

  .ok {evm with output := BNP.toB8L (p0 + p1)}

def executeEcmul (evm : Evm) : Execution := do
  let data := evm.msg.data
  let evm ← chargeGas 6000 evm
  let x : Nat := B8L.toNat <| data.sliceD 0 32 (0 : B8)
  let y : Nat := B8L.toNat <| data.sliceD 32 32 (0 : B8)
  let n : Nat := B8L.toNat <| data.sliceD 64 32 (0 : B8)

  .assert
    (x < altBn128Prime ∧ y < altBn128Prime)
    ⟨evm, "OutOfGasError"⟩
  let p ← (BNP.mk? x y).toExcept ⟨evm, "OutOfGasError"⟩

  .ok {evm with output := BNP.toB8L (p * n)}

structure Blake2 : Type where
  w: Nat
  mask_bits: Nat
  word_format: String
  R1: Nat
  R2: Nat
  R3: Nat
  R4: Nat



def blake2b : Blake2 :=
  {
    w := 64,
    mask_bits := 0xFFFFFFFFFFFFFFFF
    word_format := "Q",
    R1 := 32,
    R2 := 24,
    R3 := 16,
    R4 := 63
  }

def blake2IV : List Nat :=
  [
    0x6A09E667F3BCC908,
    0xBB67AE8584CAA73B,
    0x3C6EF372FE94F82B,
    0xA54FF53A5F1D36F1,
    0x510E527FADE682D1,
    0x9B05688C2B3E6C1F,
    0x1F83D9ABFB41BD6B,
    0x5BE0CD19137E2179
  ]

def blake2MixTable : List (List Nat) :=
  [
    [0, 4, 8, 12], [1, 5, 9, 13],
    [2, 6, 10, 14], [3, 7, 11, 15],
    [0, 5, 10, 15], [1, 6, 11, 12],
    [2, 7, 8, 13], [3, 4, 9, 14]
  ]

def blake2Sigma : List (List Nat) :=
  [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]
  ]

/-
def spit_le_to_uint(data: bytes, start: int, num_words: int) -> List[Uint]:
    """
    Extracts 8 byte words from a given data.

    Parameters
    ----------
    data :
        The data in bytes from which the words need to be extracted
    start :
        Position to start the extraction
    num_words:
        The number of words to be extracted
    """
    words = []
    for i in range(num_words):
        start_position = start + (i * 8)
        words.append(
            Uint.from_le_bytes(data[start_position : start_position + 8])
        )

    return words
-/
def spit_le_to_uint (data: B8L) : Nat → Nat → List Nat
  | _, 0 => []
  | start, num_words + 1 =>
    --let word := data.sliceToNat start 8
    let wordBytes := data.sliceD start 8 (0x00 : B8)
    let word := B8L.toNat wordBytes.reverse
    word :: spit_le_to_uint data (start + 8) num_words

def Nat.toBool? : Nat → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

/-
    def get_blake2_parameters(self, data: bytes) -> Tuple:
        """
        Extract the parameters required in the Blake2 compression function
        from the provided bytes data.

        Parameters
        ----------
        data :
            The bytes data that has been passed in the msg.
        """
        rounds = Uint.from_be_bytes(data[:4])
        h = spit_le_to_uint(data, 4, 8)
        m = spit_le_to_uint(data, 68, 16)
        t_0, t_1 = spit_le_to_uint(data, 196, 2)
        f = Uint.from_be_bytes(data[212:])

        return (rounds, h, m, t_0, t_1, f)
-/
def get_blake2_parameters (data : B8L) :
  Nat × List Nat × List Nat × Nat × Nat × Nat :=
  let rounds := B8L.sliceToNat data 0 4
  let h := spit_le_to_uint data 4 8
  let m := spit_le_to_uint data 68 16
  let t := spit_le_to_uint data 196 2
  let f := B8L.toNat <| data.drop 212
  ⟨rounds, h, m, t.getD 0 0, t.getD 1 0, f⟩


def Blake2.maxWord (b2 : Blake2) : Nat := 2 ^ b2.w
def Blake2.w_R1 (b2 : Blake2) : Nat := b2.w - b2.R1
def Blake2.w_R2 (b2 : Blake2) : Nat := b2.w - b2.R2
def Blake2.w_R3 (b2 : Blake2) : Nat := b2.w - b2.R3
def Blake2.w_R4 (b2 : Blake2) : Nat := b2.w - b2.R4

/-
def G(
    self, v: List, a: Uint, b: Uint, c: Uint, d: Uint, x: Uint, y: Uint
) -> List:
    """
    The mixing function used in Blake2
    https://datatracker.ietf.org/doc/html/rfc7693#section-3.1

    Parameters
    ----------
    v :
        The working vector to be mixed.
    a, b, c, d :
        Indexes within v of the words to be mixed.
    x, y :
        The two input words for the mixing.
    """
-/
def Blake2.g (b2 : Blake2) (v : List Nat) (a b c d x y : Nat) : List Nat :=

  /-
    v[a] = (v[a] + v[b] + x) % self.max_word
    v[d] = ((v[d] ^ v[a]) >> self.R1) ^ (
        (v[d] ^ v[a]) << self.w_R1
    ) % self.max_word
  -/
  let v := v.set a <| ((v.get! a) + (v.get! b) + x) % b2.maxWord
  let shiftArg : Nat := (v.get! d ^^^ v.get! a)
  let v := v.set d <| ((shiftArg >>> b2.R1) ^^^ (shiftArg <<< b2.w_R1)) % b2.maxWord

  /-
    v[c] = (v[c] + v[d]) % self.max_word
    v[b] = ((v[b] ^ v[c]) >> self.R2) ^ (
        (v[b] ^ v[c]) << self.w_R2
    ) % self.max_word
  -/
  let v := v.set c <| (v.get! c + v.get! d) % b2.maxWord
  let shiftArg : Nat := (v.get! b ^^^ v.get! c)
  let v := v.set b <| ((shiftArg >>> b2.R2) ^^^ (shiftArg <<< b2.w_R2)) % b2.maxWord

  /-
    v[a] = (v[a] + v[b] + y) % self.max_word
    v[d] = ((v[d] ^ v[a]) >> self.R3) ^ (
        (v[d] ^ v[a]) << self.w_R3
    ) % self.max_word
  -/
  let v := v.set a <| (v.get! a + v.get! b + y) % b2.maxWord
  let shiftArg : Nat := (v.get! d ^^^ v.get! a)
  let v := v.set d <| ((shiftArg >>> b2.R3) ^^^ (shiftArg <<< b2.w_R3)) % b2.maxWord

  /-
    v[c] = (v[c] + v[d]) % self.max_word
    v[b] = ((v[b] ^ v[c]) >> self.R4) ^ (
        (v[b] ^ v[c]) << self.w_R4
    ) % self.max_word
  -/
  let v := v.set c <| (v.get! c + v.get! d) % b2.maxWord
  let shiftArg : Nat := (v.get! b ^^^ v.get! c)
  let v := v.set b <| ((shiftArg >>> b2.R4) ^^^ (shiftArg <<< b2.w_R4)) % b2.maxWord

  /- return v -/
  v


def iterRange {ξ : Type} (k : Nat) (f : Nat → ξ → ξ) (x : ξ) : ξ :=
  let rec aux : Nat → Nat → ξ → ξ
    | _, 0, x => x
    | m, n + 1, x =>
      let i := m - (n + 1)
      aux m n <| f i x
  aux k k x

/-
def compress(
    self,
    num_rounds: Uint,
    h: List[Uint],
    m: List[Uint],
    t_0: Uint,
    t_1: Uint,
    f: bool,
) -> bytes:
    """
    'F Compression' from section 3.2 of RFC 7693:
    https://tools.ietf.org/html/rfc7693#section-3.2

    Parameters
    ----------
    num_rounds :
        The number of rounds. A 32-bit unsigned big-endian word
    h :
        The state vector. 8 unsigned 64-bit little-endian words
    m :
        The msg block vector. 16 unsigned 64-bit little-endian words
    t_0, t_1 :
        Offset counters. 2 unsigned 64-bit little-endian words
    f:
        The final block indicator flag. An 8-bit word
    """
-/
def Blake2.bCompress (b2 : Blake2) (numRounds : Nat)
  (h m : List Nat) (t0 t1 : Nat) (f : Bool) : B8L :=

  /-
    # Initialize local work vector v[0..15]
    v = [Uint(0)] * 16
    v[0:8] = h  # First half from state
    v[8:15] = self.IV  # Second half from IV

    v[12] = t_0 ^ self.IV[4]  # Low word of the offset
    v[13] = t_1 ^ self.IV[5]  # High word of the offset

    if f:
        v[14] = v[14] ^ self.mask_bits  # Invert all bits for last block
  -/
  let v14 : Nat := blake2IV.getD 6 0
  let v : List Nat :=
    h.take 8 ++
    (blake2IV).take 4 ++ [
      Nat.xor t0 (blake2IV.getD 4 0),
      Nat.xor t1 (blake2IV.getD 5 0),
      if f then Nat.xor v14 b2.mask_bits else v14,
      (blake2IV.getD 7 0),
      0
    ]

  /-
    # Mixing
    for r in range(num_rounds):
        # for more than sigma_len rounds, the schedule
        # wraps around to the beginning
        s = self.sigma[r % self.sigma_len]

        v = self.G(v, *self.MIX_TABLE[0], m[s[0]], m[s[1]])
        v = self.G(v, *self.MIX_TABLE[1], m[s[2]], m[s[3]])
        v = self.G(v, *self.MIX_TABLE[2], m[s[4]], m[s[5]])
        v = self.G(v, *self.MIX_TABLE[3], m[s[6]], m[s[7]])
        v = self.G(v, *self.MIX_TABLE[4], m[s[8]], m[s[9]])
        v = self.G(v, *self.MIX_TABLE[5], m[s[10]], m[s[11]])
        v = self.G(v, *self.MIX_TABLE[6], m[s[12]], m[s[13]])
        v = self.G(v, *self.MIX_TABLE[7], m[s[14]], m[s[15]])
  -/
  let innerFun (s : List Nat) (i : Nat) (v : List Nat) : List Nat :=

    b2.g v
      ((blake2MixTable.get! i).get! 0)
      ((blake2MixTable.get! i).get! 1)
      ((blake2MixTable.get! i).get! 2)
      ((blake2MixTable.get! i).get! 3)
      (m.get! (s.get! (i * 2)))
      (m.get! (s.get! ((i * 2) + 1)))

  let outerFun (r : Nat) (v : List Nat) : List Nat :=

    let s : List Nat := blake2Sigma.get! (r % blake2Sigma.length)
    iterRange 8 (innerFun s) v

  let v := iterRange numRounds outerFun v

  /-
    result_msg_words = (h[i] ^ v[i] ^ v[i + 8] for i in range(8))
    return struct.pack("<8%s" % self.word_format, *result_msg_words)
  -/
  let resultMsgWords :=
    (List.range 8).map <| fun i => h.get! i ^^^ v.get! i ^^^ v.get! (i + 8)

  let retVal := List.flatten <| resultMsgWords.map (fun n => n.toB8L.reverse.takeD 8 (0x00 : B8))

  retVal


def GAS_BLAKE2_PER_ROUND : Nat := 1
/-
def blake2f(evm: Evm) -> None:
    """
    Writes the Blake2 hash to output.

    Parameters
    ----------
    evm :
        The current EVM frame.
    """

    print("Running Blake2 precompiled contract")

    data = evm.msg.data
    if len(data) != 213:
        print(f"Invalid data length : {len(data)} bytes, expected 213 bytes")
        raise InvalidParameter

    blake2b = Blake2b()
    rounds, h, m, t_0, t_1, f = blake2b.get_blake2_parameters(data)

    charge_gas(evm, GAS_BLAKE2_PER_ROUND * rounds)

    if f not in [0, 1]:
        raise InvalidParameter

    evm.output = blake2b.compress(rounds, h, m, t_0, t_1, f)
-/

def executeBlake2F (evm : Evm) : Execution := do
  let data := evm.msg.data

  .assert (data.length = 213) ⟨evm, "InvalidParameter"⟩

  let ⟨rounds, h, m, t0, t1, f⟩ := get_blake2_parameters data
  let evm ← chargeGas (GAS_BLAKE2_PER_ROUND * rounds) evm
  let f ← f.toBool?.toExcept ⟨evm, "InvalidParameter"⟩
  let output := blake2b.bCompress rounds h m t0 t1 f

  .ok {evm with output := output}

def executePointEval (evm : Evm) : Execution := do
  let data := evm.msg.data
  .assert (data.length = 192) ⟨evm, "KZGProofError"⟩
  .error ⟨evm, "UNIMP : executePointEval"⟩

def BNP.toBNP12 : BNP → BNP12
  | ⟨x, y⟩ => ⟨⟨[x]⟩, ⟨[y]⟩⟩

-- # "Twist" a point in E(FQ2) into a point in E(FQ12)
-- w = FQ12([0, 1] + [0] * 10)
--
-- def twist(pt: Optimized_Point3D[FQP]) -> Optimized_Point3D[FQ12]:
--     _x, _y, _z = pt
--     # Field isomorphism from Z[p] / x**2 to Z[p] / x**2 - 18*x + 82
--     xcoeffs = [_x.coeffs[0] - _x.coeffs[1] * 9, _x.coeffs[1]]
--     ycoeffs = [_y.coeffs[0] - _y.coeffs[1] * 9, _y.coeffs[1]]
--     zcoeffs = [_z.coeffs[0] - _z.coeffs[1] * 9, _z.coeffs[1]]
--     nx = FQ12([xcoeffs[0]] + [0] * 5 + [xcoeffs[1]] + [0] * 5)
--     ny = FQ12([ycoeffs[0]] + [0] * 5 + [ycoeffs[1]] + [0] * 5)
--     nz = FQ12([zcoeffs[0]] + [0] * 5 + [zcoeffs[1]] + [0] * 5)
--     return (nx * w**2, ny * w**3, nz)
def twist (p : BNP2) : BNP12 :=
  let xs := List.ekat 2 p.x.val
  let ys := List.ekat 2 p.y.val
  let x0 := xs.get! 0
  let x1 := xs.get! 1
  let y0 := ys.get! 0
  let y1 := ys.get! 1
  let nx : BNF12 := ⟨[x0, 0, 0, 0, 0, 0, x1 - (x0 * 9)]⟩
  let ny : BNF12 := ⟨[y0, 0, 0, 0, 0, 0, y1 - (y0 * 9)]⟩
  let w : BNF12 := ⟨[1, 0]⟩
  ⟨nx * (w ^ 2), ny * (w ^ 3)⟩

def pseudoBinaryEncoding : List Int :=
  [
    0, 0, 0, 1, 0, 1, 0, -1,
    0, 0, 1, -1, 0, 0, 1, 0,
    0, 1, 1, 0, -1, 0, 0, 1,
    0, -1, 0, 0, 0, 0, 1, 1,
    1, 0, 0, -1, 0, 0, 1, 0,
    0, 0, 0, 0, -1, 0, 0, 1,
    1, 0, 0, -1, 0, 0, 0, 1,
    1, 0, -1, 0, 0, 1, 0, 1,
    1,
  ]

/-
# Create a function representing the line between P1 and P2,
# and evaluate it at T. Returns a numerator and a denominator
# to avoid unneeded divisions
def linefunc(
    P1: Optimized_Point3D[Optimized_Field],
    P2: Optimized_Point3D[Optimized_Field],
    T: Optimized_Point3D[Optimized_Field],
) -> Optimized_Point2D[Optimized_Field]:
    zero = P1[0].zero()
    x1, y1, z1 = P1
    x2, y2, z2 = P2
    xt, yt, zt = T
-/
def linefunc : BNP12 →  BNP12 → BNP12 → BNP12
  | ⟨x1, y1⟩, ⟨x2, y2⟩, ⟨xt, yt⟩ =>

/-
    # points in projective coords: (x / z, y / z)
    # hence, m = (y2/z2 - y1/z1) / (x2/z2 - x1/z1)
    # multiply numerator and denominator by z1z2 to get values below
    m_numerator = y2 * z1 - y1 * z2
    m_denominator = x2 * z1 - x1 * z2
    if m_denominator != zero:
        # m * ((xt/zt) - (x1/z1)) - ((yt/zt) - (y1/z1))
        return (
            m_numerator * (xt * z1 - x1 * zt) - m_denominator * (yt * z1 - y1 * zt),
            m_denominator * zt * z1,
        )
    elif m_numerator == zero:
        # m = 3(x/z)^2 / 2(y/z), multiply num and den by z**2
        m_numerator = 3 * x1 * x1
        m_denominator = 2 * y1 * z1
        return (
            m_numerator * (xt * z1 - x1 * zt) - m_denominator * (yt * z1 - y1 * zt),
            m_denominator * zt * z1,
        )
    else:
        return xt * z1 - x1 * zt, z1 * zt
-/
    let mNumerator : BNF12 := y2 - y1
    let mDenominator : BNF12 := x2 - x1
    if mDenominator ≠ 0
    then
      ⟨
        mNumerator * (xt - x1) - mDenominator * (yt - y1),
        mDenominator
      ⟩
    else
      if mNumerator = 0
      then
        let mNumerator := 3 * x1 * x1
        let mDenominator := 2 * y1
        ⟨
          mNumerator * (xt - x1) - mDenominator * (yt - y1),
          mDenominator
        ⟩
      else ⟨xt - x1, 1⟩


def FinFields.neg {p} (xs : FinFields p) : FinFields p :=
  FinFields.sub [] xs

def GaloidField.neg {p} {m} (xs : GaloisField p m) : GaloisField p m := 0 - xs

instance {p} {m} : Neg (GaloisField p m) where
  neg := GaloidField.neg

def EllipticCurve.neg {F} [Neg F] {a b} : EllipticCurve F a b → EllipticCurve F a b
  | ⟨x, y⟩ => ⟨x, -y⟩

/-
def miller_loop(
    Q: Optimized_Point3D[FQ12],
    P: Optimized_Point3D[FQ12],
    final_exponentiate: bool = True,
) -> FQ12:
-/
def millerLoop (q p : BNP12) (finalExp : Bool := true) : Option BNF12 := do

/-
    if Q is None or P is None:
        return FQ12.one()
    R: Optimized_Point3D[FQ12] = Q
    f_num, f_den = FQ12.one(), FQ12.one()
-/

  let mut r : BNP12 := q
  let mut fNum : BNF12 := 1
  let mut fDen : BNF12 := 1

/-
    # for i in range(log_ate_loop_count, -1, -1):
    for v in pseudo_binary_encoding[63::-1]:
        _n, _d = linefunc(R, R, P)
        f_num = f_num * f_num * _n
        f_den = f_den * f_den * _d
        R = double(R)
        # if ate_loop_count & (2**i):
        if v == 1:
            _n, _d = linefunc(R, Q, P)
            f_num = f_num * _n
            f_den = f_den * _d
            R = add(R, Q)
        elif v == -1:
            nQ = neg(Q)
            _n, _d = linefunc(R, nQ, P)
            f_num = f_num * _n
            f_den = f_den * _d
            R = add(R, nQ)
-/
  for v in (pseudoBinaryEncoding.take 64).reverse do
    let ⟨_n, _d⟩ := linefunc r r p
    fNum := fNum * fNum * _n
    fDen := fDen * fDen * _d
    r := r.double

    if v = 1 then do
      let ⟨_n, _d⟩ := linefunc r q p
      fNum := fNum * _n
      fDen := fDen * _d
      r := r + q
    if v = -1 then do
      let nq := EllipticCurve.neg q
      let ⟨_n, _d⟩ := linefunc r nq p
      fNum := fNum * _n
      fDen := fDen * _d
      r := r + nq

/-
    # assert R == multiply(Q, ate_loop_count)
    Q1 = (Q[0] ** field_modulus, Q[1] ** field_modulus, Q[2] ** field_modulus)
    # assert is_on_curve(Q1, b12)
    nQ2 = (Q1[0] ** field_modulus, -Q1[1] ** field_modulus, Q1[2] ** field_modulus)
    # assert is_on_curve(nQ2, b12)
    _n1, _d1 = linefunc(R, Q1, P)
    R = add(R, Q1)
    _n2, _d2 = linefunc(R, nQ2, P)
    f = f_num * _n1 * _n2 / (f_den * _d1 * _d2)
    # R = add(R, nQ2) This line is in many specifications but technically does nothing
    if final_exponentiate:
        return f ** ((field_modulus**12 - 1) // curve_order)
    else:
        return f
-/
  let q1 : BNP12 := ⟨q.x ^ altBn128Prime, q.y ^ altBn128Prime⟩
  let nq2 : BNP12 := ⟨q1.x ^ altBn128Prime , (-q1.y) ^ altBn128Prime⟩
  let ⟨_n1, _d1⟩ := linefunc r q1 p
  r := r + q1
  let ⟨_n2, _d2⟩ := linefunc r nq2 p
  let f := (fNum * _n1 * _n2) / (fDen * _d1 * _d2)

  return (
    if finalExp
    then f ^ ((altBn128Prime ^ 12 - 1) / altBn128CurveOrder)
    else f
  )

def pairing (q : BNP2) (p : BNP) (finalExp : Bool := true) : Option BNF12 := do
  guard q.isOnCurve
  guard p.isOnCurve
  if p = ⟨0, 0⟩ ∨ q = ⟨0, 0⟩ then
    return 1
  millerLoop (twist q) (p.toBNP12) finalExp

def executePairingCheck (evm : Evm) : Execution := do

  let data := evm.msg.data
  let evm ← chargeGas ((34000 * (data.length / 192)) + 45000) evm

  .assert (data.length % 192 = 0) ⟨evm, "OutOfGasError"⟩

  let mut result : BNF12 := 1

  for i in List.range (data.length / 192) do

    let arg0 := data.sliceToNat (i * 192) 32
    let arg1 := data.sliceToNat (i * 192 + 32) 32
    let arg2 := data.sliceToNat (i * 192 + 64) 32
    let arg3 := data.sliceToNat (i * 192 + 96) 32
    let arg4 := data.sliceToNat (i * 192 + 128) 32
    let arg5 := data.sliceToNat (i * 192 + 160) 32

    let p : BNP ← (BNP.mk? arg0 arg1).toExcept ⟨evm, "OutOfGasError"⟩
    let q : BNP2 ← (
      EllipticCurve.mk?
        (BNF2.mk arg2 arg3)
        (BNF2.mk arg4 arg5)
      ).toExcept ⟨evm, "OutOfGasError"⟩

    .assert (p * altBn128CurveOrder = ⟨0, 0⟩) ⟨evm, "OutOfGasError"⟩
    .assert (q * altBn128CurveOrder = ⟨0, 0⟩) ⟨evm, "OutOfGasError"⟩

    let pairResult ← (pairing q p).toExcept ⟨evm, "ValueError"⟩
    result := result * pairResult

  let output : B8L :=
    if result = 1
    then (1 : Nat).toB256.toB8L
    else (0 : Nat).toB256.toB8L

  .ok {evm with output := output}


def executePrecomp (evm : Evm) : Adr → Execution
  | 0x1 => executeEcrecover evm
  | 0x2 => executeSha256 evm
  | 0x3 => executeRipemd160 evm
  | 0x4 => executeId evm
  | 0x5 => executeModexp evm
  | 0x6 => executeEcadd evm
  | 0x7 => executeEcmul evm
  | 0x8 => executePairingCheck evm
  | 0x9 => executeBlake2F evm
  | 0xA => executePointEval evm
  | n => .error ⟨evm, s!"ERROR : precompiled contract {n} does not exist"⟩

inductive Inst : Type
  | last : Linst → Inst
  | next : Ninst → Inst
  | jump : Jinst → Inst

def Inst.toString : Inst → String
  | .next n => n.toString
  | .jump j => j.toString
  | .last l => l.toString

def Inst'.toString : Inst' → String
  | .next n => n.toString
  | .jump j => j.toString
  | .last l => l.toString

def stepString (evm : Evm) (i : Inst') : String :=
  "step(" ++
    s!"pc({evm.pc}), " ++
    s!"gas({evm.gas_left}), " ++
    s!"inst(\"{i.toString}\"), " ++
    s!"depth({evm.msg.depth}), " ++
    s!"actualMem({evm.memory.data.size}), " ++
    s!"{evm.stack.map (fun x => "0x" ++ x.toHex.trimHex)}" ++
  ")."

def showStep (vb : Bool) (evm : Evm) (i : Inst') : Except (Evm × String) Unit :=
  if vb
  then (dbg_trace (stepString evm i) ; .ok ())
  else .ok ()

def Wor.getStor (w : Wor) (a : Adr) : Stor := (w.get a).stor
def Wor.getStorVal (w : Wor) (a : Adr) (k : B256) : B256 := (w.get a).stor.findD k 0
def Wor.getNonce (w : Wor) (a : Adr) : B64 := (w.get a).nonce
def Wor.getCode (w : Wor) (a : Adr) : ByteArray := (w.get a).code
def Wor.getBal (w : Wor) (a : Adr) : B256 := (w.get a).bal
-- def Wor.storIsEmptyAt (w : Wor) (a : Adr) : Bool := (w.get a).stor.isEmpty

def showLim (lim : Nat) (evm : Evm) : Except (EVM × String) Unit :=
  match lim % 1000000 with
  | 0 => do
    dbg_trace s!"Recursion limit tracing, gas left : {evm.gas_left}"
    return ()
  | _ => return ()


def eoaDelegationMarker : B8L := [0xEF, 0x01, 0x00]
def EOA_DELEGATED_CODE_LENGTH : Nat := 23

def isValidDelegation (code: ByteArray) : Prop :=
  code.size = EOA_DELEGATED_CODE_LENGTH ∧
  code.sliceD 0 3 (0 : B8) = eoaDelegationMarker

instance {code} : Decidable (isValidDelegation code) := instDecidableAnd

-- def get_delegated_code_address(code: bytes) -> Optional[Address]:
--     if is_valid_delegation(code):
--         return Address(code[EOA_DELEGATION_MARKER_LENGTH:])
--     return None
def getDelegatedCodeAddress (code : ByteArray) : Option Adr :=
  if isValidDelegation code
  then
    let adrBytes := code.sliceD eoaDelegationMarker.length 20 (0 : B8)
    adrBytes.toAdr?
  else none

/-
def access_delegation(
    evm: Evm, address: Address
) -> Tuple[bool, Address, Bytes, Uint]:
    """
    Get the delegation address, code, and the cost of access from the address.

    Parameters
    ----------
    evm : `Evm`
        The execution frame.
    address : `Address`
        The address to get the delegation from.

    Returns
    -------
    delegation : `Tuple[bool, Address, Bytes, Uint]`
        The delegation address, code, and access gas cost.
    """
    state = evm.msg.block_env.state
    code = get_account(state, address).code
    if not is_valid_delegation(code):
        return False, address, code, Uint(0)

    address = Address(code[eoaDelegationMarker_LENGTH:])
    if address in evm.accessed_addresses:
        access_gas_cost = gasWarmAccess
    else:
        evm.accessed_addresses.add(address)
        access_gas_cost = GAS_COLD_ACCOUNT_ACCESS
    code = get_account(state, address).code

    return True, address, code, access_gas_cost
-/

instance : Inhabited Adr := ⟨0⟩

def accessDelegation (evm : Evm) (adr : Adr) :
  Bool × Adr × ByteArray × Nat × Evm :=
  let state := evm.msg.benv.state
  let code := state.getCode adr

  if isValidDelegation code
  then
    let adr :=
      (code.sliceD eoaDelegationMarker.length 20 (0 : B8)).toAdr?.get!
    let accessGasCost := access_cost adr evm.accessedAddresses
    let evm := addAccessedAddress evm adr
    let code := state.getCode adr
    ⟨true, adr, code, accessGasCost, evm⟩
  else ⟨false, adr, code, 0, evm⟩

mutual

  def executeCode (vb : Bool) (msg : Msg) :
    Nat → Except (Benv × Tenv × String) Evm
    | 0 => .error ⟨msg.benv, msg.tenv, "RecursionLimit"⟩
    | lim + 1 => do
      let evm : Evm := {
        pc := 0
        stack := []
        memory := .empty
        code := msg.code
        gas_left := msg.gas
        logs := []
        refund_counter := 0
        msg := msg
        output := []
        accountsToDelete := .empty
        return_data := []
        error := .none
        accessedAddresses := msg.accessedAddresses
        accessedStorageKeys := msg.accessedStorageKeys
      }

      let isPrecomp : Bool :=
        match msg.codeAddress with
        | .none => false
        | .some adr => adr.isPrecomp

      let result : Execution :=
        if isPrecomp
        then
          executePrecomp evm (msg.codeAddress.getD 0)
        else exec vb lim evm

      match result with
      | .ok evm => .ok evm
      | .error ⟨evm, err⟩ =>
        if ExceptionalHalt err
        then .ok {evm with gas_left := 0, output := [], error := some err}
        else
          if err = "Revert"
          then .ok {evm with error := some "Revert"}
          else .error ⟨evm.msg.benv, evm.msg.tenv, err⟩
  termination_by lim => lim

  def processMsg (vb : Bool) (msg : Msg) :
    Nat → Except (Benv × Tenv × String) Evm
    | 0 => .error ⟨msg.benv, msg.tenv, "RecursionLimit"⟩
    | lim + 1 => do
      .assert
        (msg.depth ≤ 1024)
        ⟨msg.benv, msg.tenv, "StackDepthLimitError"⟩

      let init_state := msg.benv.state
      let init_tra := msg.tenv.transientStorage

      let benv ←
        if msg.shouldTransferValue
        then
          let benv ←
            (msg.benv.subBal msg.caller msg.value).toExcept
              ⟨msg.benv, msg.tenv, "AssertionError"⟩
          .ok <| benv.addBal msg.currentTarget msg.value
        else .ok msg.benv

      let evm ← executeCode vb msg lim

      if evm.error.isSome
      then .ok <| evm.rollback init_state init_tra
      else .ok evm
  termination_by lim => lim

-- def process_create_msg(msg: Msg) -> Evm:
  def processCreateMsg (vb : Bool) (msg : Msg) :
    Nat → Except (Benv × Tenv × String) Evm
    | 0 => .error ⟨msg.benv, msg.tenv, "RecursionLimit"⟩
    | lim + 1 => do
      let init_state := msg.benv.state
      let init_tra := msg.tenv.transientStorage
      let adr := msg.currentTarget
      let mut benv := msg.benv.setStor adr .empty
      benv := add_created_account benv adr
      benv := benv.incrNonce adr
      let evm ← processMsg vb {msg with benv := benv} lim

      if evm.error.isNone
      then
        let contractCode := evm.output
        let contractCodeGas := contractCode.length * GAS_CODE_DEPOSIT
        let result : Execution :=
          match contractCode with
          | 0xEF :: _ => .error ⟨evm, "InvalidContractPrefix"⟩
          | _ => do
            let evm ← chargeGas contractCodeGas evm
            if maxCodeSize < contractCode.length
            then .error ⟨evm, "OutOfGasError"⟩
            else .ok evm
        match result with
        | .ok evm => .ok <| evm.setCode adr <| .mk <| .mk contractCode
        | .error (evm, err) =>
          if ExceptionalHalt err
          then
            let evm := evm.rollback init_state init_tra
            .ok {evm with gas_left := 0, output := [], error := .some err}
          else .error ⟨evm.msg.benv, evm.msg.tenv, err⟩

      else .ok <| evm.rollback init_state init_tra
  termination_by lim => lim

  def genericCreate
    (vb : Bool)
    (evm : Evm)
    (endowment : B256)
    (newAddress : Adr)
    (memoryIndex : Nat)
    (memorySize : Nat) : Nat → Execution
    | 0 => .error ⟨evm, "RecursionLimit"⟩
    | lim + 1 => do

      let calldata := evm.memory.data.sliceD memoryIndex memorySize 0

      .assert
        (memorySize ≤ maxInitcodeSize)
        ⟨evm, "OutOfGasError"⟩

      let mut evm := addAccessedAddress evm newAddress

      let createMsgGas := except64th evm.gas_left

      evm := {evm with gas_left := evm.gas_left - createMsgGas}
      evm.assertDynamic
      evm := {evm with return_data := []}

      let sender := evm.msg.benv.state.get evm.contract

      let .false ←
        .ok (
          (
            sender.bal < endowment ∨
            sender.nonce = B64.max ∨
            evm.msg.depth + 1 > 1024
          ) : Bool
        ) | ({evm with gas_left := evm.gas_left + createMsgGas}.push 0)

      evm := evm.incrNonce evm.contract

      let .false ←
        .ok (
          let target := evm.msg.benv.state.get newAddress
          (
            target.nonce ≠ (0 : B64) ∨
            target.code.size ≠ 0 ∨
            target.stor.size ≠ 0
          ) : Bool
        ) | evm.push 0

      let childMsg : Msg := {
        benv := evm.msg.benv
        tenv := evm.msg.tenv
        caller := evm.contract
        target := .none
        gas := createMsgGas
        value := endowment
        data := []
        code := .mk <| .mk calldata
        currentTarget := newAddress
        depth := evm.msg.depth + 1
        codeAddress := .none
        shouldTransferValue := true
        isStatic := false
        accessedAddresses := evm.accessedAddresses
        accessedStorageKeys := evm.accessedStorageKeys
        disablePrecompiles := false
      }

      let child ← liftToExecution evm <| processCreateMsg vb childMsg lim

      if child.error.isSome
      then (incorporateChildOnError evm child child.output).push 0
      else (incorporateChildOnSuccess evm child []).push child.contract.toB256

  termination_by lim => lim

  def generic_call
    (vb : Bool)
    (evm: Evm)
    (gas: Nat)
    (value: B256)
    (caller: Adr)
    (target: Adr)
    (codeAddress: Adr)
    (shouldTransferValue: Bool)
    (isStaticcall: Bool)
    (input_index:  Nat)
    (input_size:   Nat)
    (output_index: Nat)
    (output_size:  Nat)
    (code : ByteArray)
    (disablePrecompiles: Bool) : Nat → Execution
    | 0 => .error ⟨evm, "RecursionLimit"⟩
    | lim + 1 => do

      let mut evm := {evm with return_data := []}

      let .false ← .ok ((evm.msg.depth + 1 > 1024) : Bool)
        | ({evm with gas_left := evm.gas_left + gas}).push 0

      let calldata := evm.memory.data.sliceD input_index input_size 0
      -- let code := (evm.getAcct codeAddress).code

      let childMsg : Msg := {
        benv := evm.msg.benv
        tenv := evm.msg.tenv
        caller := caller
        target := target
        gas := gas
        currentTarget := target
        value := value
        data := calldata
        codeAddress := codeAddress
        code := code
        depth := evm.msg.depth + 1
        shouldTransferValue := shouldTransferValue
        isStatic := isStaticcall || evm.msg.isStatic
        accessedAddresses := evm.accessedAddresses
        accessedStorageKeys := evm.accessedStorageKeys
        disablePrecompiles := disablePrecompiles
      }

      let child ← liftToExecution evm <| processMsg vb childMsg lim

      evm ←
        if child.error.isSome
        then (incorporateChildOnError evm child child.output).push 0
        else (incorporateChildOnSuccess evm child child.output).push 1

      let actualOutput := child.output.take output_size

      .ok <| evm.memWrite output_index actualOutput

  termination_by lim => lim

  def Ninst'.run (vb : Bool) (evm : Evm) : Ninst' → Nat → Execution
    | .push x len, _ => do
      let evm ← chargeGas (if len = 0 then gBase else gVerylow) evm
      let evm ← evm.push x
      .ok {evm with pc := evm.pc + len + 1}
    | .reg r, _ => r.run evm
    | .exec _, 0 => .error ⟨evm, "RecursionLimit"⟩
    | .exec .create, lim + 1 => do
      let ⟨endowment, evm⟩ ← evm.pop
      let ⟨memory_index, evm⟩ ← evm.popToNat
      let ⟨memory_size, evm⟩ ← evm.popToNat
      let extend_cost := evm.extCost [⟨memory_index, memory_size⟩]
      let initCodeCost := GAS_INIT_CODE_WORD_COST * (ceilDiv memory_size 32)
      let evm ← chargeGas (GAS_CREATE + extend_cost + initCodeCost) evm
      let evm := evm.memExtends [⟨memory_index, memory_size⟩]
      let newAddress :=
        compute_contract_address
          evm.contract
          (evm.msg.benv.state.get evm.contract).nonce
      let evm ←
        genericCreate
          vb
          evm
          endowment
          newAddress
          memory_index
          memory_size
          lim
      evm.incrPc

    | .exec .create2, lim + 1 => do
      let ⟨endowment, evm⟩ ← evm.pop
      let ⟨memory_index, evm⟩ ← evm.popToNat
      let ⟨memory_size, evm⟩ ← evm.popToNat
      let ⟨salt, evm⟩ ← evm.pop
      let extend_cost := evm.extCost [⟨memory_index, memory_size⟩]
      let initCodeHashCost :=
        GAS_KECCAK256_WORD * ceilDiv memory_size 32
      let initCodeCost :=
        GAS_INIT_CODE_WORD_COST * (ceilDiv memory_size 32)
      let evm ←
        chargeGas
          (GAS_CREATE + initCodeHashCost + extend_cost + initCodeCost)
          evm
      let evm := evm.memExtends [⟨memory_index, memory_size⟩]
      let newAddress :=
        create2NewAddress
          evm.contract
          salt
          (evm.memory.data.sliceD memory_index memory_size 0)
      let evm ←
        genericCreate
          vb
          evm
          endowment
          newAddress
          memory_index
          memory_size
          lim
      evm.incrPc

    | .exec .call, lim + 1 => do
      let ⟨gas, evm⟩ ← evm.pop
      let ⟨callee, evm⟩ ← evm.pop <&> Prod.mapFst B256.toAdr
      let ⟨value, evm⟩ ← evm.pop
      let ⟨input_index, evm⟩ ← evm.popToNat
      let ⟨input_size, evm⟩ ← evm.popToNat
      let ⟨output_index, evm⟩ ← evm.popToNat
      let ⟨output_size, evm⟩ ← evm.popToNat

      let extend_cost :=
        evm.extCost [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]

      let mut access_cost := access_cost callee evm.accessedAddresses

      let evm := addAccessedAddress evm callee

      let ⟨disablePrecompiles, _, code, delegatedAccessGasCost, evm⟩ :=
        accessDelegation evm callee

      access_cost := access_cost + delegatedAccessGasCost

      let create_cost :=
        if (¬ (evm.getAcct callee).Empty) ∨ value = 0
        then 0
        else gNewAccount

      let transfer_cost := if value = 0 then 0 else gasCallValue

      let ⟨msg_call_cost, msg_call_stipend⟩ :=
        calculate_msg_call_gas
          value.toNat
          gas.toNat
          evm.gas_left
          extend_cost
          (access_cost + create_cost + transfer_cost)

      let evm ← chargeGas (msg_call_cost + extend_cost) evm

      .assert (!evm.msg.isStatic ∨ value = 0) ⟨evm, "WriteInStaticContext"⟩

      let evm :=
        evm.memExtends
          [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]

      let senderBal := (evm.getAcct evm.contract).bal

      let evm ←
        if senderBal < value
        then
          let evm ← evm.push 0
          .ok {
            evm with
            return_data := []
            gas_left := evm.gas_left + msg_call_stipend
          }
        else
          generic_call
            vb
            evm
            msg_call_stipend
            value
            evm.contract
            callee
            callee
            true
            false
            input_index
            input_size
            output_index
            output_size
            code
            disablePrecompiles
            lim

      evm.incrPc

    | .exec .callcode, lim + 1 => do

      let ⟨gas, evm⟩ ← evm.pop
      let ⟨codeAddress, evm⟩ ← evm.pop <&> Prod.mapFst B256.toAdr
      let ⟨value, evm⟩ ← evm.pop
      let ⟨input_index, evm⟩ ← evm.popToNat
      let ⟨input_size, evm⟩ ← evm.popToNat
      let ⟨output_index, evm⟩ ← evm.popToNat
      let ⟨output_size, evm⟩ ← evm.popToNat

      let target := evm.contract
      let extend_cost :=
        evm.extCost [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]
      let mut access_cost := access_cost codeAddress evm.accessedAddresses
      let evm := addAccessedAddress evm codeAddress

      let ⟨disablePrecompiles, codeAddress, code, delegatedAccessGasCost, evm⟩ :=
        accessDelegation evm codeAddress

      access_cost := access_cost + delegatedAccessGasCost

      let transfer_cost := if value = 0 then 0 else gasCallValue

      let ⟨msg_call_cost, msg_call_stipend⟩ :=
        calculate_msg_call_gas
          value.toNat
          gas.toNat
          evm.gas_left
          extend_cost
          (access_cost + transfer_cost)

      let evm ← chargeGas (msg_call_cost + extend_cost) evm

      let evm :=
        evm.memExtends
          [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]

      let senderBal := (evm.getAcct evm.contract).bal

      let evm ←
        if senderBal < value
        then
          let evm ← evm.push 0
          .ok {
            evm with
            return_data := []
            gas_left := evm.gas_left + msg_call_stipend
          }
        else
          generic_call
            vb
            evm
            msg_call_stipend
            value
            evm.contract
            target
            codeAddress
            true
            false
            input_index
            input_size
            output_index
            output_size
            code
            disablePrecompiles
            lim

      evm.incrPc

    | .exec .delcall, lim + 1 => do
      let ⟨gas, evm⟩ ← evm.pop
      let ⟨codeAddress, evm⟩ ← evm.pop <&> Prod.mapFst B256.toAdr
      let ⟨input_index, evm⟩ ← evm.popToNat
      let ⟨input_size, evm⟩ ← evm.popToNat
      let ⟨output_index, evm⟩ ← evm.popToNat
      let ⟨output_size, evm⟩ ← evm.popToNat

      let extend_cost :=
        evm.extCost [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]

      let mut access_cost := access_cost codeAddress evm.accessedAddresses
      let evm := addAccessedAddress evm codeAddress

      let ⟨disablePrecompiles, codeAddress, code, delegatedAccessGasCost, evm⟩ :=
        accessDelegation evm codeAddress

      access_cost := access_cost + delegatedAccessGasCost

      let ⟨msg_call_cost, msg_call_stipend⟩ :=
        calculate_msg_call_gas
          0
          gas.toNat
          evm.gas_left
          extend_cost
          access_cost

      let evm ← chargeGas (msg_call_cost + extend_cost) evm

      let evm :=
        evm.memExtends
          [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]

      let evm ←
        generic_call
          vb
          evm
          msg_call_stipend
          evm.msg.value
          evm.msg.caller
          evm.contract
          codeAddress
          false
          false
          input_index
          input_size
          output_index
          output_size
          code
          disablePrecompiles
          lim

      evm.incrPc

    | .exec .statcall, lim + 1 => do

      --let ⟨gas, evm⟩ ← evm.pop
      let gas ← evm.stackTop
      let mut evm ← evm.pop'

      -- let ⟨target, evm⟩ ← evm.pop <&> Prod.mapFst B256.toAdr
      let target ← evm.stackTop <&> B256.toAdr
      evm ← evm.pop'

      -- let ⟨input_index, evm⟩ ← evm.popToNat
      let input_index ← evm.stackTop <&> B256.toNat
      evm ← evm.pop'

      -- let ⟨input_size, evm⟩ ← evm.popToNat
      let input_size ← evm.stackTop <&> B256.toNat
      evm ← evm.pop'

      -- let ⟨output_index, evm⟩ ← evm.popToNat
      let output_index ← evm.stackTop <&> B256.toNat
      evm ← evm.pop'

      -- let ⟨output_size, evm⟩ ← evm.popToNat
      let output_size ← evm.stackTop <&> B256.toNat
      evm ← evm.pop'


      let extend_cost :=
        evm.extCost [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]

      let mut access_cost := access_cost target evm.accessedAddresses
      evm := addAccessedAddress evm target

      let ⟨disablePrecompiles, _, code, delegatedAccessGasCost, evm'⟩ :=
        accessDelegation evm target

      evm := evm'

      access_cost := access_cost + delegatedAccessGasCost

      let ⟨msg_call_cost, msg_call_stipend⟩ :=
        calculate_msg_call_gas
          0
          gas.toNat
          evm.gas_left
          extend_cost
          access_cost

      evm ← chargeGas (msg_call_cost + extend_cost) evm

      evm :=
        evm.memExtends
          [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]

      evm ←
        generic_call
          vb
          evm
          msg_call_stipend
          0
          evm.contract
          target
          target
          true
          true
          input_index
          input_size
          output_index
          output_size
          code
          disablePrecompiles
          lim

      evm.incrPc
  termination_by _ lim => lim

  def exec : Bool → Nat → Evm → Execution
    | vb, 0, evm =>
      dbg_trace "execution recursion limit (*NOT* execution depth limit) reached"
      .error ⟨evm, "RecursionLimit"⟩
    | vb, lim + 1, evm => do
      let mut evm := evm
      showLim lim evm
      let i ← (evm.getInst).toExcept ⟨evm, "InvalidOpcode"⟩
      showStep vb evm i
      match i with
      | .next n =>
         evm ← n.run vb evm lim
         exec vb lim evm
      | .jump j =>
        evm ← j.run evm
        exec vb lim evm
      | .last l => l.run evm
  termination_by _ lim _ => lim

end

lemma List.length_takeD {ξ : Type u} (n : Nat) (xs : List ξ) (x : ξ) :
    (List.takeD n xs x).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [takeD]

instance {w a} : Decidable (Dead w a) := by
  simp [Dead]
  cases (Lean.RBMap.find? w a)
  · simp; apply instDecidableTrue
  · simp [Acct.Empty]; apply instDecidableAnd

inductive CallCostType
  | all
  | noCreate
  | onlyAccess

def Wor.code (w : Wor) (a : Adr) : ByteArray :=
  match w.find? a with
  | none => ByteArray.mk #[]
  | some x => x.code

def Sta.init : Sta := ⟨Array.mkArray 1024 (0 : B256), 0⟩

def dataGas (cd : B8L) : Nat :=
  let aux : B8 → Nat := fun b => if b = 0 then 4 else 16
  (cd.map aux).sum

abbrev AccessList.collect (al : AccessList) : KeySet :=
  let addPair : Adr → KeySet → B256 → KeySet :=
    fun a aks k => aks.insert ⟨a, k⟩
  let addElem : KeySet → Adr × List B256 → KeySet :=
    fun aks pr => List.foldl (addPair pr.fst) aks pr.snd
  List.foldl addElem .empty al

def Sta.toListCore : Array B256 → Nat → Option (List B256)
  | _, 0 => .some []
  | arr, n + 1 => do
    let x ← arr.get? n
    let xs ← Sta.toListCore arr n
    .some (x :: xs)

def Sta.toList (s : Sta) : Option (List B256) := Sta.toListCore s.fst s.snd

def Sta.push1 : Sta → B256 → Option Sta
  | ⟨xs, n⟩, x => do
    guard (n < 1024)
    some ⟨xs.set! n x, n + 1⟩

def Sta.push2 : Sta → B256 → B256 → Option Sta
  | ⟨xs, n⟩, x, y => do
    guard (n < 1023)
    let xs' := xs.set! n y
    some ⟨xs'.set! (n + 1) x, n + 2⟩

def Sta.push3 : Sta → B256 → B256 → B256 → Option Sta
  | ⟨xs, n⟩, x, y, z => do
    guard (n < 1022)
    let xs' := xs.set! n z
    let xs'' := xs'.set! (n + 1) y
    some ⟨xs''.set! (n + 2) x, n + 3⟩

def KeySet.toStrings (ks : KeySet) : List String :=
  let f : (Adr × B256) → List String :=
    fun | ⟨a, x⟩ => [s!"{a.toHex} : {x.toHex}"]
  fork "KeySet" <| ks.toList.map f

instance : ToString KeySet := ⟨λ ks => String.joinln <| ks.toStrings⟩

def Sta.toStringsCore (xs : Array B256) : Nat → List String
  | 0 => []
  | n + 1 => ("0x" ++ (xs.getD n 0).toHex) :: Sta.toStringsCore xs n

def Sta.toStrings : Sta → List String
  | ⟨xs, n⟩ => Sta.toStringsCore xs n

def Sta.toString (s : Sta) : String := String.joinln s.toStrings

def Sta.swap : Sta → Nat → Option Sta
  | ⟨xs, n + 2⟩, k =>
    if n < k
    then none
    else some ⟨xs.swap! (n + 1) (n - k), n + 2⟩
  | _, _ => none

def Sta.dup : Sta → Nat → Option Sta
  | ⟨xs, n⟩, k =>
    if n < k + 1
    then none
    else do let x ← xs.get? (n - (k + 1))
            Sta.push1 ⟨xs, n⟩ x

def Sta.toProlog (σ : Sta) : String :=
  match σ.toList with
  | .none => "stack(retrieval_failed)"
  | .some xs => s!"stack({xs.map B256.toNat})"

instance : ToString Log := ⟨String.joinln ∘ Log.toStrings⟩

-- inductive Tx.Result : Type
--   | fail : TxEx → Tx.Result
--   | pass (Wor : Wor) (gas : Nat) (logs : List Log) (sta : Bool) : Tx.Result
--
-- def Tx.Result.toStrings : Tx.Result → List String
--   | .fail x => [x.toString]
--   | .pass w g l s =>
--     fork "pass" [
--       w.toStrings,
--       [s!"gas : {g}"],
--       fork "logs" (l.map Log.toStrings),
--       [s!"status : {s}"]
--     ]
--
-- instance : ToString Tx.Result := ⟨String.joinln ∘ Tx.Result.toStrings⟩

def eraseIfEmpty (w : Wor) (a : Adr) : Wor := w.set a <| w.get a

def IO.decide (φ : Prop) [Decidable φ] : IO Bool :=
  if φ then pure .true else pure .false

def correctBlobHashVersion (h : B256) : Prop :=
  h.toB8V[0] = 0x01

instance : DecidablePred correctBlobHashVersion := by
  intro h; simp [correctBlobHashVersion]; infer_instance

def eraseIfNew (ω₀ ω : Wor) (a : Adr) : Wor :=
  match ω₀.find? a with
  | none => ω.erase a
  | some _ => ω

structure  BlockInfo : Type where
  blockHashes : List B256
  baseFee : B256
  excessBlobGas : B256
  beneficiary : Adr
  prevRandao : B256
  gasLimit : B256
  timestamp : B256
  number : B256

def Log.toBLT (l : Log) : BLT :=
  .list [
    .b8s l.address.toB8L,
    .list (l.topics.map B256.toRLP),
    .b8s l.data
  ]

def BLT.toLog : BLT → Option Log
  | .list [ .b8s adr, .list topics, .b8s data ] => do
    let adr ← adr.toAdr?
    let topics ← topics.mapM BLT.toB256
    some {
      address := adr
      topics := topics
      data := data
    }
  | _ => none

def publicAddress? (hsa : ByteArray) (ri : UInt8) (rsa : ByteArray) : Option Adr :=
  match (ecrecoverFlag hsa ri rsa).toList with
  | [] => none
  | b :: pa =>
    if b = 0
    then none
    else (B8L.toAdr? pa)

def publicAddress (hsa : ByteArray) (ri : UInt8) (rsa : ByteArray) : IO Adr :=
  match (ecrecoverFlag hsa ri rsa).toList with
  | [] => IO.throw "Unreachable code : ecrecover should never return empty bytes"
  | b :: pa =>
    if b = 0
    then IO.throw "ecrecover failed"
    else (B8L.toAdr? pa).toIO "bytearray to address conversion failed"

def List.putIndex {ξ : Type u} : Nat → List ξ → List (Nat × ξ)
  | _, [] => []
  | k, x :: xs => (k, x) :: List.putIndex (k + 1) xs

inductive ExpectedWorldState : Type
  | wor : Wor → ExpectedWorldState
  | root : B256 → ExpectedWorldState

structure Test where
  (name : String)
  (info : Lean.Json)
  (blocks : Lean.Json)
  (gbh : Lean.Json)
  (grlp : Lean.Json)
  (lbh : Lean.Json)
  (network : Lean.Json)
  (pre : Lean.Json)
  (post : ExpectedWorldState)
  (sealEngine : Lean.Json)

def Test.toStrings (t : Test) : List String :=
  fork "test" [
    [s!"test name : {t.name}"],
    fork "info" [t.info.toStrings],
    fork "blocks" [t.blocks.toStrings],
    fork "genesisBlockHeader" [t.gbh.toStrings],
    fork "genesisRLP" [t.grlp.toStrings],
    fork "lastblockhash" [t.lbh.toStrings],
    fork "network" [t.network.toStrings],
    fork "pre" [t.pre.toStrings],
    --[s!"postRoot {t.postRoot.toHex}"],
    fork "sealEngine" [t.sealEngine.toStrings]
  ]

instance : ToString Test := ⟨String.joinln ∘ Test.toStrings⟩

def B8L.toByteArray (xs : B8L) : ByteArray := .mk <| .mk xs

def Lean.Json.toAcct : Lean.Json → IO Acct
  | .obj r => do
    let aux (xy :(_ : String) × Lean.Json) : IO (B256 × B256) := do
      let x ← .remove0x xy.fst
      let bs ← (Hex.toB8L x).toIO ""
      let bs' ← xy.snd.toIoB8L
      return ⟨bs.toB256P, bs'.toB256P⟩
    let bal_json ← (r.find compare "balance").toIO ""
    let nonce_json ← (r.find compare "nonce").toIO ""
    let code_json ← (r.find compare "code").toIO ""
    let stor_json ← (r.find compare "storage").toIO "" >>= Lean.Json.toIoRBNode
    let bal ← Lean.Json.toIoB256P bal_json
    let nonce ← Lean.Json.toIoB64P nonce_json
    let code ← Lean.Json.toIoB8L code_json
    let stor ← mapM aux stor_json.toArray.toList
    return ⟨nonce, bal, Lean.RBMap.fromList stor _, code.toByteArray⟩
  | _ => .throw "cannot parse account (not .obj)"

instance : ToString Wor := ⟨String.joinln ∘ Wor.toStrings⟩

def Lean.Json.toWorld (j : Lean.Json) : IO Wor := do
  let aux : Wor → ((_ : String) × Lean.Json) → IO Wor :=
    fun | w, ⟨s, j⟩ => do
      let adr ← (Hex.toAdr? <| remove0x s).toIO ""
      let acct ← j.toAcct
      pure <| w.set adr acct
  let ob ← j.toIoRBNode
  List.foldlM aux .empty ob.toArray.toList

def Lean.Json.find? : String → Lean.Json → Option Lean.Json
  | k, .obj r => r.find compare k
  | _, _ => .none

def Lean.Json.find : String → Lean.Json → IO Lean.Json
  | k, .obj r => (r.find compare k).toIO s!"ERROR : FAILED JSON RETRIEVAL WITH KEY : {k}"
  | k, _ => .throw s!"ERROR : INPUT JSON IS NOT OBJECT, FAILED RETRIEVAL WITH KEY : {k}"

def Lean.Json.get? : Nat → Lean.Json → IO Lean.Json
  | k, .arr js => (js.get? k).toIO ""
  | _, _ => .throw ""

def Wor.root (w : Wor) : B256 :=
  let keyVals := (List.map toKeyVal w.toList)
  let finalNTB : NTB := Lean.RBMap.fromList keyVals _
  trie finalNTB

def getXWS (j : Lean.Json) : IO ExpectedWorldState := do
  let r ← j.toIoRBNode
  match r.find compare "postState" with
  | some wj => do --hj.toB256?
    let w ← Lean.Json.toWorld wj
    pure (.wor w)
  | .none => do
    let hj ← j.find "postStateHash"
    let h ← hj.toIoB256
    pure (.root h)

def getPostRoot (j : Lean.Json) : IO B256 := do
  let r ← j.toIoRBNode
  match r.find compare "postStateHash" with
  | some hj => hj.toIoB256
  | none => do
    let wj ← j.find "postState"
    let w ← Lean.Json.toWorld wj
    pure w.root

def mkTest : ((_ : String) × Lean.Json) → IO Test
  | ⟨name, j⟩ => do
    let info ← j.find "_info"
    let blocks ← j.find "blocks"
    let gbh ← j.find "genesisBlockHeader"
    let grlp ← j.find "genesisRLP"
    let lbh ← j.find "lastblockhash"
    let network ← j.find "network"
    let xws ← getXWS j -- j.find "postState"
    let pre ← j.find "pre"
    let sealEngine ← j.find "sealEngine"
    return ⟨name, info, blocks, gbh, grlp, lbh, network, pre, xws, sealEngine⟩

def Lean.Json.toTests (j : Lean.Json) : IO (List Test) := do
  let r ← j.toIoRBNode
  let l := r.toArray.toList
  mapM mkTest l

instance : ToString BLT := ⟨String.joinln ∘ BLT.toStrings⟩

def BLT.toB8L : BLT → Option B8L
  | .b8s xs => some xs
  | _ => .none

def BLT.get? : Nat → BLT → Option BLT
  | k, .list rs => rs.get? k
  | _, _ => .none

def setupAdr : Adr := 0x000F3DF6D732807EF1319FB7B8BB8522D0BEAC02
def setupKey : B256 := 1000 --0x03E8

def toKeyVal' (pr : B8L × B8L) : B8L × B8L :=
  let ad := pr.fst
  let ac := pr.snd
  ⟨B8L.toB4s ad, ac⟩

def receiptRoot (w : List (B8L × B8L)) : B256 :=
  let keyVals : List (B8L × B8L) := (List.map toKeyVal' w)
  let finalNTB : NTB := Lean.RBMap.fromList keyVals _
  trie finalNTB

def addIndexToBloom (hash : B8L) (index : Nat) (bloom : B8L) : B8L :=
  let bitToSet : B16 :=
    (B8s.toB16 (hash.getD index 0) (hash.getD (index + 1) 0)) &&& (0x07FF : B16)
  let bitIndex : B16 := 0x07FF - bitToSet
  let byteIndex : Nat := (bitIndex / 8).toNat
  let bitValue : B8 := 0x01 <<< (0x07 - (bitIndex.lows &&& 0x07))
  let origValue : B8 := bloom.getD byteIndex 0
  bloom.set byteIndex (origValue ||| bitValue)

def addEntryToBloom (bloom : B8L) (entry : B8L) : B8L :=
  let hash := (B8L.keccak entry).toB8L
  addIndexToBloom hash 4 <|
  addIndexToBloom hash 2 <|
  addIndexToBloom hash 0 bloom

def addLogToBloom (bloom : B8L) (log : Log) : B8L :=
  let bloom' := addEntryToBloom bloom log.address.toB8L
  List.foldl addEntryToBloom bloom' (log.topics.map B256.toB8L)

def logs_bloom (l : List Log) : B8L :=
  List.foldl addLogToBloom (List.replicate 256 0x00) l

def Bool.toB8L : Bool → B8L
  | .false => []
  | .true => [0x01]

def Withdrawal.toStrings (wd : Withdrawal) : List String :=
  fork "withdrawal" [
    [s!"global index : 0x{wd.globalIndex.toHex}"],
    [s!"validator index : 0x{wd.validatorIndex.toHex}"],
    [s!"recipient : 0x{wd.recipient.toHex}"],
    [s!"amount : 0x{wd.amount.toHex}"]
  ]

instance : ToString Withdrawal := ⟨String.joinln ∘ Withdrawal.toStrings⟩

-- def checkTransactionsRoot (vb : Bool) (txbs : B8L) (root : B256) (txr : Tx.Result) : IO Unit :=
--   let root' : B256 :=
--     match txr with
--     | .fail _ => receiptRoot []
--     | .pass _ _ _ _ => receiptRoot [⟨[0x80], txbs⟩]
--   .check vb (root = root')
--     "Transactions trie root check : PASS\n"
--     s!"Transactions trie root check : FAIL, expected : {root.toHex}, computed : {root'.toHex}"

-- def checkWithdrawalsRoot (vb : Bool) (wds : List Withdrawal) (wr : B256) : IO Unit :=
--   let aux : (ℕ × Withdrawal) → (B8L × B8L) :=
--     fun | ⟨idx, wd⟩ => ⟨idx.toB8L, wd.toBLT.encode⟩
--   let temp : List (B8L × B8L) := (wds.putIndex 0).map aux
--   let wr' := receiptRoot temp
--   .check vb (wr = wr')
--     "withdrawals check : PASS\n"
--     s!"withdrawals check : FAIL, withdrawals : {wds}"

-- def getTxExMap (j : Lean.Json) : IO (Option TxEx × Lean.Json) := do
--   match j.find? "expectException" with
--   | .none => pure ⟨.none, j⟩
--   | .some exj => do
--     let exs ← exj.toString?
--     let ex ← (parseTxEx exs).toIO ""
--     let j' ← j.find "rlp_decoded"
--     pure ⟨.some ex, j'⟩

def getTxExMap (j : Lean.Json) : IO (Option String × B8L) := do
  let rlp ← j.find "rlp" >>= Lean.Json.toIoB8L
  match j.find? "expectException" with
  | .none => pure ⟨.none, rlp⟩
  | .some exj => do
    let exs ← exj.toIoString
    -- let ex ← (parseTxEx exs).toIO ""
    pure ⟨.some exs, rlp⟩

def getBlockHeader : Lean.Json → Option Lean.Json
  | .obj r =>
    r.find compare "blockHeader" <|>
    ( do let (.obj r') ← r.find compare "rlp_decoded" | .none
         r'.find compare "blockHeader" )
  | _ => .none

def Lean.Json.toWithdrawal (j : Lean.Json) : IO Withdrawal :=
  .throw "unimplemented : json-to-withdrawal parsing"

def BLT.toExStrHeader : BLT → Except String Header
  | .list (
      .b8s parentHash ::
      .b8s ommersHash ::
      .b8s coinbase ::
      .b8s stateRoot ::
      .b8s txsRoot ::
      .b8s receiptRoot ::
      .b8s bloom ::
      .b8s difficulty ::
      .b8s number ::
      .b8s gasLimit ::
      .b8s gasUsed ::
      .b8s timestamp ::
      .b8s extraData ::
      .b8s prevRandao ::
      .b8s nonce ::
      .b8s baseFeePerGas ::
      .b8s withdrawalsRoot ::
      .b8s blobGasUsed ::
      .b8s excessBlobGas ::
      .b8s parentBeaconBlockRoot ::
      tail
    ) => do
      let parentHash ← parentHash.toB256?.toExcept "parentHash to B256 conversion failed"
      let ommersHash ← ommersHash.toB256?.toExcept "ommersHash to B256 conversion failed"
      let coinbase ← coinbase.toAdr?.toExcept "coinbase to Adr conversion failed"
      let stateRoot ← stateRoot.toB256?.toExcept "stateRoot to B256 conversion failed"
      let txsRoot ← txsRoot.toB256?.toExcept "txsRoot to B256 conversion failed"
      let receiptRoot ← receiptRoot.toB256?.toExcept "receiptRoot to B256 conversion failed"
      let difficulty := difficulty.toNat
      let number := number.toNat
      let gasLimit := gasLimit.toNat
      let gasUsed := gasUsed.toNat
      let timestamp := timestamp.toNat
      let prevRandao ← prevRandao.toB256?.toExcept "prevRandao to B256 conversion failed"
      let nonce ← nonce.toB64?.toExcept "nonce to B64 conversion failed"
      let baseFeePerGas := baseFeePerGas.toNat
      let withdrawalsRoot ← withdrawalsRoot.toB256?.toExcept "withdrawalsRoot to B256 conversion failed"
      let blobGasUsed := blobGasUsed.toNat
      let excessBlobGas := excessBlobGas.toNat
      let previousBeaconBlockRoot ← parentBeaconBlockRoot.toB256?.toExcept "parentBeaconBlockRoot to B256 conversion failed"
      let requestsHash : Option B256 ←
        match tail with
        | [] => .ok none
        | [.b8s requestsHash] => requestsHash.toB256?.toExcept "requestsHash conversion failed"
        | _ => .error "BLT to Header conversion failed, incorrect list length"

      .ok {
        parentHash := parentHash
        ommersHash := ommersHash
        coinbase := coinbase
        stateRoot := stateRoot
        txsRoot := txsRoot
        receiptRoot := receiptRoot
        bloom := bloom
        difficulty := difficulty
        number := number
        gasLimit := gasLimit
        gasUsed := gasUsed
        timestamp := timestamp
        extraData := extraData
        prevRandao := prevRandao
        nonce := nonce
        baseFeePerGas := baseFeePerGas
        withdrawalsRoot := withdrawalsRoot
        blobGasUsed := blobGasUsed
        excessBlobGas := excessBlobGas
        parentBeaconBlockRoot := previousBeaconBlockRoot
        requestsHash := requestsHash
      }
  | _ =>
    .error "BLT to Header conversion failed, expected a list"

def Lean.Json.toHeader (json : Lean.Json) : IO Header := do
  let parentHash ← json.find "parentHash" >>= Lean.Json.toIoB256
  let ommersHash ← json.find "uncleHash" >>= Lean.Json.toIoB256
  let coinbase ← json.find "coinbase" >>= Lean.Json.toIoAdr
  let stateRoot ← json.find "stateRoot" >>= Lean.Json.toIoB256
  let txsRoot ← json.find "transactionsTrie" >>= Lean.Json.toIoB256
  let receiptRoot ← json.find "receiptTrie" >>= Lean.Json.toIoB256
  let bloom ← json.find "bloom" >>= Lean.Json.toIoB8L
  let difficulty ← (json.find "difficulty" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let number ← (json.find "number" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let gasLimit ← (json.find "gasLimit" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let gasUsed ← (json.find "gasUsed" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let timestamp ← (json.find "timestamp" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let extraData ← json.find "extraData" >>= Lean.Json.toIoB8L
  let prevRandao ← json.find "mixHash" >>= Lean.Json.toIoB256
  let nonce ← json.find "nonce" >>= Lean.Json.toIoB64
  let baseFeePerGas ← (json.find "baseFeePerGas" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let withdrawalsRoot ← json.find "withdrawalsRoot" >>= Lean.Json.toIoB256
  let blobGasUsed ← (json.find "blobGasUsed" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let excessBlobGas ← (json.find "excessBlobGas" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let parentBeaconBlockRoot ← json.find "parentBeaconBlockRoot" >>= Lean.Json.toIoB256
  let requestsHash := (json.find? "requestsHash" >>= Lean.Json.toB256?)
  .ok {
    parentHash := parentHash
    ommersHash := ommersHash
    coinbase := coinbase
    stateRoot := stateRoot
    txsRoot := txsRoot
    receiptRoot := receiptRoot
    bloom := bloom
    difficulty := difficulty
    number := number
    gasLimit := gasLimit
    gasUsed := gasUsed
    timestamp := timestamp
    extraData := extraData
    prevRandao := prevRandao
    nonce := nonce
    baseFeePerGas := baseFeePerGas
    withdrawalsRoot := withdrawalsRoot
    blobGasUsed := blobGasUsed
    excessBlobGas := excessBlobGas
    parentBeaconBlockRoot := parentBeaconBlockRoot
    requestsHash := requestsHash
  }

structure BlockChain : Type where
  blocks : List Block
  state : Wor
  chainId : B64

def Lean.Json.toIoLegacyTx (json : Lean.Json) : IO Tx := do
  let nonce ← (json.find "nonce" >>= Lean.Json.toIoB8L) <&> B8L.toB64P
  let gas ← (json.find "gasLimit" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let receiver ← json.find "to" >>= Lean.Json.toIoAdr
  let value ← (json.find "value" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let data ← json.find "data" >>= Lean.Json.toIoB8L
  let v ← (json.find "v" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let r ← json.find "r" >>= Lean.Json.toIoB8L
  let s ← json.find "s" >>= Lean.Json.toIoB8L
  let gasPrice ← (json.find "gasPrice" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  .ok {
    nonce := nonce
    gas := gas
    receiver := receiver
    value := value
    data := data
    v := v
    r := r
    s := s
    type := .zero gasPrice
  }

def Lean.Json.toIoTypeTwoTx (json : Lean.Json) : IO Tx := do
  let nonce ← (json.find "nonce" >>= Lean.Json.toIoB8L) <&> B8L.toB64P
  let gas ← (json.find "gasLimit" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let receiver ← json.find "to" >>= Lean.Json.toIoAdr
  let value ← (json.find "value" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let data ← json.find "data" >>= Lean.Json.toIoB8L
  let v ← (json.find "v" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let r ← json.find "r" >>= Lean.Json.toIoB8L
  let s ← json.find "s" >>= Lean.Json.toIoB8L

  let chainId ← (json.find "chainId" >>= Lean.Json.toIoB8L) <&> B8L.toB64P
  let maxFee ← (json.find "maxFeePerGas" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let maxPriorityFee ← (json.find "maxPriorityFeePerGas" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let temp ← json.find "accessList" >>= Lean.Json.toIoList
  .guard temp.isEmpty "UNIMP : access list read"

  .ok {
    nonce := nonce
    gas := gas
    receiver := receiver
    value := value
    data := data
    v := v
    r := r
    s := s
    type :=
      .two
        chainId
        maxPriorityFee
        maxFee
        []
  }

def Lean.Json.toIoTx (json : Lean.Json) : IO Tx :=
  json.toIoLegacyTx <|> json.toIoTypeTwoTx

def Block.toStrings (block : Block) : List String :=

  let aux : B8L ⊕ Tx → List String
    | .inl xs => fork "Encoded Tx" [String.chunks 80 xs.toHex]
    | .inr tx => tx.toStrings

  fork "BLOCK" [
    Header.toStrings block.header,
    fork "TXS" <| block.txs.map aux,
    fork "OMMERS" <| block.ommers.map Header.toStrings,
    fork "WDS" <| block.wds.map Withdrawal.toStrings
  ]

instance : ToString Block := ⟨String.joinln ∘ Block.toStrings⟩

def TARGET_BLOB_GAS_PER_BLOCK : Nat := 0x60000 -- U64(393216)

def calculateExcessBlobGas (parentHeader : Header) : Nat :=
  let parentBlobGas : Nat :=
    parentHeader.excessBlobGas + parentHeader.blobGasUsed
  parentBlobGas - TARGET_BLOB_GAS_PER_BLOCK

def ELASTICITY_MULTIPLIER : Nat := 2
def GAS_LIMIT_ADJUSTMENT_FACTOR : Nat := 1024
def GAS_LIMIT_MINIMUM : Nat := 5000

def BASE_FEE_MAX_CHANGE_DENOMINATOR := 8

abbrev checkGasLimit (gasLimit parentGasLimit : Nat) : Prop :=
  let maxAdjustmentDelta := parentGasLimit / GAS_LIMIT_ADJUSTMENT_FACTOR
  gasLimit < parentGasLimit + maxAdjustmentDelta ∧
  parentGasLimit - maxAdjustmentDelta < gasLimit ∧
  GAS_LIMIT_MINIMUM ≤ gasLimit

def calculateBaseFeePerGas
  (blockGasLimit parentGasLimit parentGasUsed parentBaseFeePerGas : Nat) :
  Except String Nat := do
  let parentGasTarget := parentGasLimit / ELASTICITY_MULTIPLIER
  .assert
    (checkGasLimit blockGasLimit parentGasLimit)
    "InvalidBlock"
  if parentGasUsed = parentGasTarget
  then .ok parentBaseFeePerGas
  else
    if parentGasUsed > parentGasTarget
    then
      let gasUsedDelta := parentGasUsed - parentGasTarget
      let parentFeeGasDelta := parentBaseFeePerGas * gasUsedDelta
      let targetFeeGasDelta := parentFeeGasDelta / parentGasTarget
      let baseFeePerGasDelta :=
        max (targetFeeGasDelta / BASE_FEE_MAX_CHANGE_DENOMINATOR) 1
      .ok <| parentBaseFeePerGas + baseFeePerGasDelta
    else

      let gasUsedDelta := parentGasTarget - parentGasUsed
      let parentFeeGasDelta := parentBaseFeePerGas * gasUsedDelta
      let targetFeeGasDelta := parentFeeGasDelta / parentGasTarget
      let baseFeePerGasDelta :=
        targetFeeGasDelta / BASE_FEE_MAX_CHANGE_DENOMINATOR
      .ok <| parentBaseFeePerGas - baseFeePerGasDelta

def EMPTY_OMMER_HASH : B256 := B8L.keccak []

def validateHeader (chain : BlockChain) (header : Header) :
  Except String Unit := do

  let parent ← chain.blocks.getLast?.toExcept "No parent block found"
  let expectedBaseFeePerGas ←
    calculateBaseFeePerGas
      header.gasLimit
      parent.header.gasLimit
      parent.header.gasUsed
      parent.header.baseFeePerGas
  let blockParentHash := (Header.toBLT parent.header).encode.keccak

  .assert
    (
      header.excessBlobGas = calculateExcessBlobGas parent.header ∧
      header.gasUsed ≤ header.gasLimit ∧
      expectedBaseFeePerGas = header.baseFeePerGas ∧
      header.timestamp > parent.header.timestamp ∧
      header.number = parent.header.number + 1 ∧
      header.extraData.length ≤ 32 ∧
      header.difficulty = 0 ∧
      header.nonce = 0 ∧
      header.ommersHash = EMPTY_OMMER_HASH ∧
      header.parentHash = blockParentHash
    )
    "InvalidBlock"

-- def validateHeader (header parentHeader : Header) :
--   Except String Unit := do
--
--   .assert
--     (header.gasUsed ≤ header.gasLimit)
--     "InvalidBlock"
--
--   let expectedBaseFeePerGas ←
--     calculateBaseFeePerGas
--       header.gasLimit
--       parentHeader.gasLimit
--       parentHeader.gasUsed
--       parentHeader.baseFeePerGas
--
--   .assert
--     (
--       expectedBaseFeePerGas = header.baseFeePerGas ∧
--       header.timestamp > parentHeader.timestamp ∧
--       header.number = parentHeader.number + 1 ∧
--       header.extraData.length ≤ 32 ∧
--       header.difficulty = 0 ∧
--       header.nonce = 0 ∧
--       header.ommersHash = EMPTY_OMMER_HASH
--     )
--     "InvalidBlock"
--
--   let blockParentHash := (Header.toBLT parentHeader).encode.keccak
--
--   .assert
--     (header.parentHash = blockParentHash)
--     "InvalidBlock"

def beaconRootsAddress : Adr := 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02
def historyStorageAddress : Adr := 0x0000F90827F1C53a10cb7A02335B175320002935
def systemAddress : Adr := 0xfffffffffffffffffffffffffffffffffffffffe
def systemTransactionGas : Nat := 30000000

structure ApplyBodyOutput : Type where
  blockGasUsed : Nat
  transactionsRoot : B256
  receiptRoot : B256
  blockLogsBloom : B8L
  stateRoot : B256
  withdrawalsRoot : B256
  blobGasUsed : Nat
  requests : List B256

structure MsgCallOutput : Type where
  gasLeft : Nat
  refundCounter : Int
  logs : List Log
  accountsToDelete : AdrSet
  error: Option String
  returnData : B8L

def Except.bimap
  {ε : Type u0} {δ : Type u1} {ξ : Type u2} {υ : Type u3}
  (f : ε → δ) (g : ξ → υ) : Except ε ξ → Except δ υ
  | .error e => .error <| f e
  | .ok x => .ok <| g x

def accountHasCodeOrNonce (state : Wor) (adr : Adr) : Bool :=
  state.getNonce adr > 0 || !(state.getCode adr).isEmpty

--         SET_CODE_TX_MAGIC
def setCodeTxMagic : B8L := [0x05]





/-
def processMsgCall (vb : Bool) (msg : Msg) (env : Environment) :
  Except String (Wor × MsgCallOutput) := do

  let (true : Bool) ← .ok (noCollision msg env)
    | .ok ⟨env.state, 0, 0, [], .empty, some "AddressCollision"⟩

  let evm ←
    match msg.target with
    | none => Except.bimap Prod.snd id <| processCreateMsg vb msg env (msg.gas + 50)
    | some _ => Except.bimap Prod.snd id <| processMsg vb msg env (msg.gas + 50)

  .ok <|
    if evm.error.isNone
    then ⟨
      evm.env.state,
      {
        gas_left := evm.gas_left
        refund_counter := evm.refund_counter
        logs := evm.logs
        accountsToDelete := evm.accountsToDelete
        error := evm.error
      }
    ⟩
    else ⟨
      evm.env.state,
      {
        gas_left := evm.gas_left
        refund_counter := 0
        logs := []
        accountsToDelete := .empty
        error := evm.error
      }
    ⟩
    -/



def Tx.signingHash (tx : Tx) : Option B256 :=
  match tx.type with
  | .zero gasPrice =>
    if tx.v = 27 || tx.v = 28
    then
      -- signing_hash_pre155,
      some <|
        B8L.keccak <|
          BLT.encode <|
            .list [
              .b8s tx.nonce.toB8L.sig,
              .b8s gasPrice.toB8L,
              .b8s tx.gas.toB8L,
              .b8s ((tx.receiver <&> Adr.toB8L).getD []),
              .b8s tx.value.toB8L,
              .b8s tx.data
            ]
    else do
      -- signing_hash_155,
      let chainId : Nat := (tx.v - 35) / 2
      some <|
        B8L.keccak <|
          BLT.encode <|
            .list [
              .b8s tx.nonce.toB8L.sig,
              .b8s gasPrice.toB8L,
              .b8s tx.gas.toB8L,
              .b8s ((tx.receiver <&> Adr.toB8L).getD []),
              .b8s tx.value.toB8L,
              .b8s tx.data,
              .b8s chainId.toB8L,
              .b8s [],
              .b8s []
            ]
  /-
  def signing_hash_2930(tx: AccessListTransaction) -> Hash32:
  """
  Compute the hash of a transaction used in a EIP 2930 signature.

  Parameters
  ----------
  tx :
      Transaction of interest.

  Returns
  -------
  hash : `ethereum.crypto.hash.Hash32`
      Hash of the transaction.
  """
  return keccak256(
      b"\x01"
      + rlp.encode(
          (
              tx.chain_id,
              tx.nonce,
              tx.gas_price,
              tx.gas,
              tx.to,
              tx.value,
              tx.data,
              tx.access_list,
          )
      )
  ) -/
  | .one gasPrice chainId accessList =>
    B8L.keccak <|
      .cons (0x01 : B8) <|
        BLT.encode <|
          .list [
            .b8s chainId.toB8L.sig,
            .b8s tx.nonce.toB8L.sig,
            .b8s gasPrice.toB8L,
            .b8s tx.gas.toB8L,
            .b8s ((tx.receiver <&> Adr.toB8L).getD []),
            .b8s tx.value.toB8L,
            .b8s tx.data,
            accessList.toBLT
          ]

  /-
  def signing_hash_1559(tx: FeeMarketTransaction) -> Hash32:
    """
    Compute the hash of a transaction used in a EIP 1559 signature.

    Parameters
    ----------
    tx :
        Transaction of interest.

    Returns
    -------
    hash : `ethereum.crypto.hash.Hash32`
        Hash of the transaction.
    """
    return keccak256(
        b"\x02"
        + rlp.encode(
            (
                tx.chain_id,
                tx.nonce,
                tx.max_priority_fee_per_gas,
                tx.max_fee_per_gas,
                tx.gas,
                tx.to,
                tx.value,
                tx.data,
                tx.access_list,
            )
        )
    )
  -/
  | .two chainId maxPriorityFee maxFee accessList =>
    B8L.keccak <|
      .cons (0x02 : B8) <|
        BLT.encode <|
          .list [
            .b8s chainId.toB8L.sig,
            .b8s tx.nonce.toB8L.sig,
            .b8s maxPriorityFee.toB8L,
            .b8s maxFee.toB8L,
            .b8s tx.gas.toB8L,
            .b8s ((tx.receiver <&> Adr.toB8L).getD []),
            .b8s tx.value.toB8L,
            .b8s tx.data,
            accessList.toBLT
          ]
  /-
  def signing_hash_4844(tx: BlobTransaction) -> Hash32:
    """
    Compute the hash of a transaction used in a EIP-4844 signature.

    Parameters
    ----------
    tx :
        Transaction of interest.

    Returns
    -------
    hash : `ethereum.crypto.hash.Hash32`
        Hash of the transaction.
    """
    return keccak256(
        b"\x03"
        + rlp.encode(
            (
                tx.chain_id,
                tx.nonce,
                tx.max_priority_fee_per_gas,
                tx.max_fee_per_gas,
                tx.gas,
                tx.to,
                tx.value,
                tx.data,
                tx.access_list,
                tx.max_fee_per_blob_gas,
                tx.blob_versioned_hashes,
            )
        )
    )
    -/
  | .three chainId maxPriorityFee maxFee accessList maxBlobFee blobHashes =>
    B8L.keccak <|
      .cons (0x03 : B8) <|
        BLT.encode <|
          .list [
            .b8s chainId.toB8L.sig,
            .b8s tx.nonce.toB8L.sig,
            .b8s maxPriorityFee.toB8L,
            .b8s maxFee.toB8L,
            .b8s tx.gas.toB8L,
            .b8s ((tx.receiver <&> Adr.toB8L).getD []),
            .b8s tx.value.toB8L,
            .b8s tx.data,
            accessList.toBLT,
            .b8s maxBlobFee.toB8L,
            .list <| blobHashes.map <| .b8s ∘ B256.toB8L
          ]
  -- def signing_hash_7702(tx: SetCodeTransaction) -> Hash32:
  --     """
  --     Compute the hash of a transaction used in a [EIP-7702] signature.
  --
  --     This function takes a transaction as a parameter and returns the
  --     signing hash of the transaction used in a [EIP-7702] signature.
  --
  --     [EIP-7702]: https://eips.ethereum.org/EIPS/eip-7702
  --     """
  --     return keccak256(
  --         b"\x04"
  --         + rlp.encode(
  --             (
  --                 tx.chain_id,
  --                 tx.nonce,
  --                 tx.max_priority_fee_per_gas,
  --                 tx.max_fee_per_gas,
  --                 tx.gas,
  --                 tx.to,
  --                 tx.value,
  --                 tx.data,
  --                 tx.access_list,
  --                 tx.authorizations,
  --             )
  --         )
  --     )
  | .four chainId maxPriorityFee maxFee accessList auths =>
    B8L.keccak <|
      .cons (0x04 : B8) <|
        BLT.encode <|
          .list [
            .b8s chainId.toB8L.sig,
            .b8s tx.nonce.toB8L.sig,
            .b8s maxPriorityFee.toB8L,
            .b8s maxFee.toB8L,
            .b8s tx.gas.toB8L,
            .b8s ((tx.receiver <&> Adr.toB8L).getD []),
            .b8s tx.value.toB8L,
            .b8s tx.data,
            accessList.toBLT,
            .list <| auths.map Auth.toBLT
          ]

def secp256k1nRecoverToAdr?
  (r s : B256) (v : Nat) (msg_hash : B256) : Option  Adr :=
  let rsa : ByteArray := ⟨Array.mk (r.toB8L ++ s.toB8L)⟩
  let ri : UInt8 := --Byte.toB8 (if tx.yParity then 1 else 0)
    match v with
    | 0 => 0
    | _ => 1
  let hsa : ByteArray := ⟨Array.mk msg_hash.toB8L⟩
  publicAddress? hsa ri rsa

/-
def recover_sender(chain_id: U64, tx: Transaction) -> Address:
    r, s = tx.r, tx.s

    if U256(0) >= r or r >= SECP256K1N:
        raise InvalidSignatureError("bad r")
    if U256(0) >= s or s > SECP256K1N // U256(2):
        raise InvalidSignatureError("bad s")

    if isinstance(tx, LegacyTransaction):
        v = tx.v
        if v == 27 or v == 28:
            public_key = secp256k1_recover(
                r, s, v - U256(27), signing_hash_pre155(tx)
            )
        else:
            chain_id_x2 = U256(chain_id) * U256(2)
            if v != U256(35) + chain_id_x2 and v != U256(36) + chain_id_x2:
                raise InvalidSignatureError("bad v")
            public_key = secp256k1_recover(
                r,
                s,
                v - U256(35) - chain_id_x2,
                signing_hash_155(tx, chain_id),
            )
    elif isinstance(tx, AccessListTransaction):
        if tx.y_parity not in (U256(0), U256(1)):
            raise InvalidSignatureError("bad y_parity")
        public_key = secp256k1_recover(
            r, s, tx.y_parity, signing_hash_2930(tx)
        )
    elif isinstance(tx, FeeMarketTransaction):
        if tx.y_parity not in (U256(0), U256(1)):
            raise InvalidSignatureError("bad y_parity")
        public_key = secp256k1_recover(
            r, s, tx.y_parity, signing_hash_1559(tx)
        )
    elif isinstance(tx, BlobTransaction):
        if tx.y_parity not in (U256(0), U256(1)):
            raise InvalidSignatureError("bad y_parity")
        public_key = secp256k1_recover(
            r, s, tx.y_parity, signing_hash_4844(tx)
        )

    return Address(keccak256(public_key)[12:32])
-/
def recoverSender (chain_id: B64) (tx: Tx) : Except String Adr := do

  let r := tx.r.toB256P
  let s := tx.s.toB256P
  .assertNot (r = 0 ∨ B256.secp256k1n ≤ r) "InvalidSignatureError : bad r"
  .assertNot (s = 0 ∨ B256.secp256k1n / 2 < s) "InvalidSignatureError : bad s"
  let v := tx.v

  let signingHash ←
    tx.signingHash.toExcept "InvalidSignatureError : signing hash is None"

  match tx.type with
  | .zero _  =>
    if v = 27 ∨ v = 28
    then
      (secp256k1nRecoverToAdr? r s (v - 27) signingHash).toExcept
        "sender recovery failed"
    else
      let chain_id_x2 := (chain_id.toNat) * (2)
      .assert (v = 35 + chain_id_x2 ∨ v = 36 + chain_id_x2) "InvalidSignatureError : bad v"
      (secp256k1nRecoverToAdr? r s (v - 35 - chain_id_x2) signingHash).toExcept
        "sender recovery failed"
  | _ =>
    .assert (v < 2) "InvalidSignatureError"
    (secp256k1nRecoverToAdr? r s v signingHash).toExcept "sender recovery failed"



-- def recover_authority(authorization: Authorization) -> Address:
def recoverAuthority (auth : Auth) : Except String Adr := do

--     y_parity, r, s = authorization.y_parity, authorization.r, authorization.s
  let yParity := auth.yParity
  let r := auth.r
  let s := auth.s

--     if y_parity not in (0, 1):
--         raise InvalidSignatureError("Invalid y_parity in authorization")
--     if U256(0) >= r or r >= SECP256K1N:
--         raise InvalidSignatureError("Invalid r value in authorization")
--     if U256(0) >= s or s > SECP256K1N // U256(2):
--         raise InvalidSignatureError("Invalid s value in authorization")
  if (
    1 < yParity ∨
    r = 0 ∨ B256.secp256k1n ≤ r ∨
    s = 0 ∨ (B256.secp256k1n / 2) < s
  ) then
    .error "InvalidSignatureError"

--     signing_hash = keccak256(
--         SET_CODE_TX_MAGIC
--         + rlp.encode(
--             (
--                 authorization.chain_id,
--                 authorization.address,
--                 authorization.nonce,
--             )
--         )
--     )
  let signingHash : B256 :=
    B8L.keccak <|
      List.append setCodeTxMagic <|
        BLT.encode <| .list [
          .b8s auth.chainId.toB8L.sig,
          .b8s auth.address.toB8L,
          .b8s auth.nonce.toB8L.sig
        ]

--     public_key = secp256k1_recover(r, s, U256(y_parity), signing_hash)
--     return Address(keccak256(public_key)[12:32])
  (secp256k1nRecoverToAdr? r s yParity signingHash).toExcept "sender recovery failed"

def perEmptyAccountCost := 25000
def perAuthBaseCost := 12500

-- def set_delegation(message: Message) -> U256:
def setDelegation (msg : Msg) : Except String (Msg × B256) := do

--     state = message.block_env.state
--     refund_counter = U256(0)
  let mut refundCounter : B256 := 0
  let mut msg := msg

--     for auth in message.tx_env.authorizations:
  for auth in msg.tenv.auths do

--         if auth.chain_id not in (message.block_env.chain_id, U256(0)):
--             continue
    if auth.chainId != msg.benv.chainId && auth.chainId != 0 then
      continue

--         if auth.nonce >= U64.MAX_VALUE:
--             continue
    if auth.nonce = B64.max then
      continue

--         try:
--             authority = recover_authority(auth)
--         except InvalidSignatureError:
--             continue
    let authority : Adr ←
      match recoverAuthority auth with
      | .error err =>
        if err = "InvalidSignatureError" then
          continue
        else
          .error err
      | .ok adr => .ok adr

--         message.accessed_addresses.add(authority)
    msg := {msg with accessedAddresses := msg.accessedAddresses.insert authority}

--         authority_account = get_account(state, authority)
    let authorityAccount : Acct :=
      msg.benv.state.get authority

--         authority_code = authority_account.code
--         if authority_code and not is_valid_delegation(authority_code):
--             continue
    let authorityCode : ByteArray := authorityAccount.code
    if ¬ (authorityCode.isEmpty ∧ isValidDelegation authorityCode) then
      continue

--         authority_nonce = authority_account.nonce
--         if authority_nonce != auth.nonce:
--             continue
    if authorityAccount.nonce != auth.nonce then
      continue

--         if account_exists(state, authority):
--             refund_counter += U256(PER_EMPTY_ACCOUNT_COST - PER_AUTH_BASE_COST)
    if AccountExists msg.benv.state authority then
      refundCounter :=
        refundCounter + (perEmptyAccountCost - perAuthBaseCost).toB256

--         if auth.address == NULL_ADDRESS:
--             code_to_set = b""
--         else:
--             code_to_set = eoaDelegationMarker + auth.address
    let codeToSet : ByteArray :=
      if auth.address = 0 then
        .empty
      else
        (eoaDelegationMarker ++ auth.address.toB8L).toByteArray

--         set_code(state, authority, code_to_set)
--         increment_nonce(state, authority)
    msg := msg.setCode authority codeToSet
    msg := msg.incrNonce authority

--     if message.code_address is None:
--         raise InvalidBlock("Invalid type 4 transaction: no target")
--     message.code = get_account(state, message.code_address).code
  msg ←
    match msg.codeAddress with
    | none =>
      .error "InvalidBlock : Invalid type 4 transaction: no target"
    | some ca =>
      .ok {
        msg with
        code := msg.benv.state.getCode ca
      }

  .ok ⟨msg, refundCounter⟩

def Int.toNat? (i : Int) : Option Nat :=
  if i < 0 then
    none
  else
    some (i.toNat)

/- def process_msg_call(msg: Msg) -> MsgCallOutput: -/
def processMsgCall (vb : Bool) (msg : Msg) :
  Except String (Wor × MsgCallOutput) := do

--block_env = msg.block_env
--refund_counter = U256(0)
  let benv := msg.benv
  let mut msg : Msg := msg
  let mut refundCounter : Nat := 0

--if msg.target == Bytes0(b""):
  let mut evm : Evm := default
  if msg.target.isNone then

--  is_collision = account_has_code_or_nonce(
--    block_env.state, msg.current_target
--  ) or account_has_storage(block_env.state, msg.current_target)
    let isCollision : Bool :=
      accountHasCodeOrNonce benv.state msg.currentTarget

--  if is_collision:
--    return MsgCallOutput(
--      Uint(0),
--      U256(0),
--      tuple(),
--      set(),
--      AddressCollision(),
--      Bytes(b""),
--    )
--  else:
--    evm = process_create_msg(msg)
    if isCollision then
      return ⟨benv.state, ⟨0, 0, [], .empty, "AddressCollision", []⟩⟩
    else
      evm ← Except.bimap (Prod.snd ∘ Prod.snd) id <| processCreateMsg vb msg (msg.gas + 50)

--else:
--  if msg.tx_env.authorizations != ():
--    refund_counter += set_delegation(msg)
  else
    if !msg.tenv.auths.isEmpty then
      let ⟨msg', setDelegationValue⟩ ← setDelegation msg
      msg := msg'
      refundCounter := refundCounter + setDelegationValue.toNat

--  delegated_address = get_delegated_code_address(msg.code)
--  if delegated_address is not None:
--    msg.disable_precompiles = True
--    msg.accessed_addresses.add(delegated_address)
--    msg.code = get_account(block_env.state, delegated_address).code
--    msg.code_address = delegated_address
    match getDelegatedCodeAddress msg.code with
    | none => .ok ()
    | some dca =>
      msg :=
        {
          msg with
          disablePrecompiles := true,
          accessedAddresses := msg.accessedAddresses.insert dca,
          code := benv.state.getCode dca,
          codeAddress := some dca
        }

--  evm = process_msg(msg)
    evm ← Except.bimap (Prod.snd ∘ Prod.snd) id <| processMsg vb msg (msg.gas + 50)

--if evm.error:
--  logs: Tuple[Log, ...] = ()
--  accountsToDelete = set()
--else:
--  logs = evm.logs
--  accountsToDelete = evm.accountsToDelete
--  refund_counter += U256(evm.refund_counter)
  let mut logs : List Log := []
  let mut accountsToDelete : AdrSet := .empty
  if evm.error.isNone then
    logs := evm.logs
    accountsToDelete := evm.accountsToDelete
    let evmRc ← (Int.toNat? evm.refund_counter).toExcept "ERROR : refund counter is negative"
    refundCounter := refundCounter + evmRc

--tx_end = TransactionEnd(
--  int(msg.gas) - int(evm.gas_left), evm.output, evm.error
--)
--evm_trace(evm, tx_end)

--return MsgCallOutput(
--  gas_left=evm.gas_left,
--  refund_counter=refund_counter,
--  logs=logs,
--  accountsToDelete=accounts_to_delete,
--  error=evm.error,
--  return_data=evm.output,
--)
  .ok ⟨
    msg.benv.state,
    {
      gasLeft := evm.gas_left,
      refundCounter := refundCounter
      logs := logs,
      accountsToDelete := accountsToDelete,
      error := evm.error,
      returnData := evm.output
    }
  ⟩

def txBaseCost : Nat := 21000

def Tx.maxPriorityFee? (tx : Tx) : Option Nat :=
  match tx.type with
  | .zero _ => none
  | .one _ _ _ => none
  | .two _ maxPriorityFee _ _ => some maxPriorityFee
  | .three _ maxPriorityFee _ _ _ _ => some maxPriorityFee
  | .four _ maxPriorityFee _ _ _ => some maxPriorityFee

def Tx.maxFee? (tx : Tx) : Option Nat :=
  match tx.type with
  | .zero _ => none
  | .one _ _ _ => none
  | .two _ _ maxFee _ => some maxFee
  | .three _ _ maxFee _ _ _ => some maxFee
  | .four _ _ maxFee _ _ => some maxFee

def Tx.isTypeOne (tx : Tx) : Bool :=
  match tx.type with
  | .one _ _ _ => true
  | _ => false

def Tx.isTypeTwo (tx : Tx) : Bool :=
  match tx.type with
  | .two _ _ _ _ => true
  | _ => false

def Tx.isTypeThree (tx : Tx) : Bool :=
  match tx.type with
  | .three _ _ _ _ _ _ => true
  | _ => false

def Tx.isTypeFour (tx : Tx) : Bool :=
  match tx.type with
  | .four _ _ _ _ _ => true
  | _ => false


def GAS_PER_BLOB : Nat:= (2 ^ 17)

/-
def calculate_total_blob_gas(tx: Transaction) -> Uint:
  """
  Calculate the total blob gas for a transaction.

  Parameters
  ----------
  tx :
      The transaction for which the blob gas is to be calculated.

  Returns
  -------
  total_blob_gas: `ethereum.base_types.Uint`
      The total blob gas for the transaction.
  """
  if isinstance(tx, BlobTransaction):
      return GAS_PER_BLOB * Uint(len(tx.blob_versioned_hashes))
  else:
      return Uint(0)
-/
def calculateTotalBlobGas (tx: Tx) : Nat :=
  match tx.type with
  | .three _ _ _ _ _ blobHashes => GAS_PER_BLOB * blobHashes.length
  | _ => 0

def maxBlobGasPerBlock : Nat := 786432

structure BlockOutput : Type where
  blockGasUsed : Nat
  transactionsTrie : Lean.RBMap B8L Tx compare
  receiptsTrie : Lean.RBMap B8L B8L compare
  receiptKeys : List B8L
  blockLogs : List Log
  withdrawalsTrie : Lean.RBMap B8L Withdrawal compare
  blobGasUsed : Nat
  requests : List B8L

def versionedHashVersionKzg : B8 := 0x01

-- def check_transaction(
--     block_env: vm.Benvironment,
--     block_output: vm.BlockOutput,
--     tx: Transaction,
-- ) -> Tuple[Address, Uint, Tuple[VersionedHash, ...], U64]:
def checkTransaction (benv : Benv) (blockOut : BlockOutput) (tx : Tx) :
  Except String (Adr × Nat × List B256 × Nat) := do

--     gas_available = block_env.block_gas_limit - block_output.block_gas_used
--     blob_gas_available = maxBlobGasPerBlock - block_output.blob_gas_used
  let gasAvailable := benv.blockGasLimit - blockOut.blockGasUsed
  let blobGasAvailable := maxBlobGasPerBlock - blockOut.blobGasUsed

--     if tx.gas > gas_available:
--         raise GasUsedExceedsLimitError("gas used exceeds limit")
  if tx.gas > gasAvailable then
    .error "GasUsedExceedsLimitError : gas used exceeds limit"

--     tx_blob_gas_used = calculate_total_blob_gas(tx)
  let txBlobGasUsed := calculateTotalBlobGas tx

--     if tx_blob_gas_used > blob_gas_available:
--         raise BlobGasLimitExceededError("blob gas limit exceeded")
  if txBlobGasUsed > blobGasAvailable then
    .error "BlobGasLimitExceededError : blob gas limit exceeded"

--     sender_address = recover_sender(block_env.chain_id, tx)
--     sender_account = get_account(block_env.state, sender_address)
  let senderAddress ← recoverSender benv.chainId tx
  let senderAccount := benv.state.get senderAddress

--     if isinstance(
--         tx, (FeeMarketTransaction, BlobTransaction, SetCodeTransaction)
--     ):
--         if tx.max_fee_per_gas < tx.max_priority_fee_per_gas:
--             raise PriorityFeeGreaterThanMaxFeeError(
--                 "priority fee greater than max fee"
--             )
--         if tx.max_fee_per_gas < block_env.base_fee_per_gas:
--             raise InsufficientMaxFeePerGasError(
--                 tx.max_fee_per_gas, block_env.base_fee_per_gas
--             )
--
--         priority_fee_per_gas = min(
--             tx.max_priority_fee_per_gas,
--             tx.max_fee_per_gas - block_env.base_fee_per_gas,
--         )
--         effective_gas_price = priority_fee_per_gas + block_env.base_fee_per_gas
--         max_gas_fee = tx.gas * tx.max_fee_per_gas
--     else:
--         if tx.gas_price < block_env.base_fee_per_gas:
--             raise InvalidBlock
--         effective_gas_price = tx.gas_price
--         max_gas_fee = tx.gas * tx.gas_price
  let mut effectiveGasPrice := 0
  let mut maxGasFee := 0
  let selector : Nat ⊕ (Nat × Nat) :=
    match tx.type with
    | .zero gasPrice => .inl gasPrice
    | .one gasPrice _ _ => .inl gasPrice
    | .two _ maxPriorityFee maxFee _ => .inr (maxPriorityFee, maxFee)
    | .three _ maxPriorityFee maxFee _ _ _ => .inr (maxPriorityFee, maxFee)
    | .four _ maxPriorityFee maxFee  _ _ => .inr (maxPriorityFee, maxFee)
  match selector with
  | .inr (maxPriorityFee, maxFee) =>
    if maxFee < maxPriorityFee then
      .error "PriorityFeeGreaterThanMaxFeeError : priority fee greater than max fee"
    if maxFee < benv.baseFeePerGas then
      .error "InsufficientMaxFeePerGasError"
    let priorityFeePerGas := min maxPriorityFee (maxFee - benv.baseFeePerGas)
    effectiveGasPrice := priorityFeePerGas + benv.baseFeePerGas
    maxGasFee := tx.gas * maxFee
  | .inl gasPrice =>
    if gasPrice < benv.baseFeePerGas then
      .error "InvalidBlock : gas price below base fee"
    effectiveGasPrice := gasPrice
    maxGasFee := tx.gas * gasPrice

--     if isinstance(tx, BlobTransaction):
--         if len(tx.blob_versioned_hashes) == 0:
--             raise NoBlobDataError("no blob data in transaction")
--         for blob_versioned_hash in tx.blob_versioned_hashes:
--             if blob_versioned_hash[0:1] != VERSIONED_HASH_VERSION_KZG:
--                 raise InvalidBlobVersionedHashError(
--                     "invalid blob versioned hash"
--                 )
--
--         blob_gas_price = calculate_blob_gas_price(block_env.excess_blob_gas)
--         if Uint(tx.max_fee_per_blob_gas) < blob_gas_price:
--             raise InsufficientMaxFeePerBlobGasError(
--                 "insufficient max fee per blob gas"
--             )
--
--         max_gas_fee += Uint(calculate_total_blob_gas(tx)) * Uint(
--             tx.max_fee_per_blob_gas
--         )
--         blob_versioned_hashes = tx.blob_versioned_hashes
--     else:
--         blob_versioned_hashes = ()
  let mut blobVersionedHashes : List B256 := []
  match tx.type with
  | .three _ _ _ _ maxBlobFee blobHashes =>
    if blobHashes.isEmpty then
      .error "NoBlobDataError : no blob data in transaction"
    if List.any blobHashes (λ bvh => bvh.toB8V.head ≠ versionedHashVersionKzg) then
      .error "InvalidBlobVersionedHashError : invalid blob versioned hash"
    let blobGasPrice := calculate_blob_gas_price benv.excessBlobGas
    if maxBlobFee < blobGasPrice then
      .error "InsufficientMaxFeePerBlobGasError : insufficient max fee per blob gas"
    maxGasFee := maxGasFee + calculateTotalBlobGas tx * maxBlobFee
    blobVersionedHashes := blobHashes
  | _ => .ok ()

--     if isinstance(tx, (BlobTransaction, SetCodeTransaction)):
--         if not isinstance(tx.to, Address):
--             raise TransactionTypeContractCreationError(tx)
  if tx.isTypeThree ∨ tx.isTypeFour then
    if tx.receiver.isNone then
      .error "TransactionTypeContractCreationError : receiver is none for type 3 or 4 tx"

--     if isinstance(tx, SetCodeTransaction):
--         if not any(tx.authorizations):
--             raise EmptyAuthorizationListError("empty authorization list")
  match tx.type with
  | .four _ _ _ _ [] =>
    .error "EmptyAuthorizationListError : empty authorization list"
  | _ => .ok ()

--     if sender_account.nonce > Uint(tx.nonce):
--         raise NonceMismatchError("nonce too low")
--     elif sender_account.nonce < Uint(tx.nonce):
--         raise NonceMismatchError("nonce too high")
  if senderAccount.nonce > tx.nonce then
    .error "NonceMismatchError : nonce too low"
  else if senderAccount.nonce < tx.nonce then
    .error "NonceMismatchError : nonce too high"

--     if Uint(sender_account.balance) < max_gas_fee + Uint(tx.value):
--         raise InsufficientBalanceError("insufficient sender balance")
  if senderAccount.bal.toNat < maxGasFee + tx.value then
    .error s!"InsufficientBalanceError : sender balance ({senderAccount.bal.toNat}) < max gas fee ({maxGasFee}) + tx value ({tx.value})"

--     if sender_account.code and not is_valid_delegation(sender_account.code):
--         raise InvalidSenderError("not EOA")
  if ¬ (senderAccount.code.isEmpty ∧ isValidDelegation senderAccount.code) then
    .error "InvalidSenderError : not EOA"

--     return (
--         sender_address,
--         effective_gas_price,
--         blob_versioned_hashes,
--         tx_blob_gas_used,
--     )
  .ok ⟨
    senderAddress,
    effectiveGasPrice,
    blobVersionedHashes,
    txBlobGasUsed
  ⟩

def TX_ACCESS_LIST_ADDRESS_COST : Nat := 2400
def TX_ACCESS_LIST_STORAGE_KEY_COST : Nat := 1900

def floorCalldataCost : Nat := 10

def standardCallDataTokenCost : Nat := 4

-- def calculate_intrinsic_cost(tx: Transaction) -> Tuple[Uint, Uint]:
--     """
--     Calculates the gas that is charged before execution is started.
--
--     The intrinsic cost of the transaction is charged before execution has
--     begun. Functions/operations in the EVM cost money to execute so this
--     intrinsic cost is for the operations that need to be paid for as part of
--     the transaction. Data transfer, for example, is part of this intrinsic
--     cost. It costs ether to send data over the wire and that ether is
--     accounted for in the intrinsic cost calculated in this function. This
--     intrinsic cost must be calculated and paid for before execution in order
--     for all operations to be implemented.
--
--     The intrinsic cost includes:
--     1. Base cost (`txBaseCost`)
--     2. Cost for data (zero and non-zero bytes)
--     3. Cost for contract creation (if applicable)
--     4. Cost for access list entries (if applicable)
--     5. Cost for authorizations (if applicable)
--
--
--     This function takes a transaction as a parameter and returns the intrinsic
--     gas cost of the transaction and the minimum gas cost used by the
--     transaction based on the calldata size.
--     """
--     from .vm.eoa_delegation import PER_EMPTY_ACCOUNT_COST
--     from .vm.gas import init_code_cost
def calculateIntrinsicCost (tx: Tx) : Nat × Nat :=

--     zero_bytes = 0
--     for byte in tx.data:
--         if byte == 0:
--             zero_bytes += 1
--
--     tokens_in_calldata = Uint(zero_bytes + (len(tx.data) - zero_bytes) * 4)
--     # EIP-7623 floor price (note: no EVM costs)
--     calldata_floor_gas_cost = (
--         tokens_in_calldata * FLOOR_CALLDATA_COST + txBaseCost
--     )
--
--     data_cost = tokens_in_calldata * STANDARD_CALLDATA_TOKEN_COST
  let tokensInCalldata : Nat :=
    (tx.data.map <| fun x => if x = 0 then 1 else 4).sum
  let callDataFloorGasCost : Nat :=
    tokensInCalldata * floorCalldataCost + txBaseCost
  let dataCost : Nat :=
    tokensInCalldata * standardCallDataTokenCost

--     if tx.to == Bytes0(b""):
--         create_cost = TX_CREATE_COST + init_code_cost(ulen(tx.data))
--     else:
--         create_cost = Uint(0)
  let createCost : Nat :=
      match tx.receiver with
      | none => TX_CREATE_COST + initCodeCost (tx.data).length
      | some _ => 0

--     access_list_cost = Uint(0)
--     if isinstance(
--         tx,
--         (
--             AccessListTransaction,
--             FeeMarketTransaction,
--             BlobTransaction,
--             SetCodeTransaction,
--         ),
--     ):
--         for access in tx.access_list:
--             access_list_cost += TX_ACCESS_LIST_ADDRESS_COST
--             access_list_cost += (
--                 ulen(access.slots) * TX_ACCESS_LIST_STORAGE_KEY_COST
--             )
  let accessListCost : Nat :=
    let accessList :=
      match tx.type with
      | .zero _ => []
      | .one _ _ accessList => accessList
      | .two _ _ _ accessList => accessList
      | .three _ _ _ accessList _ _ => accessList
      | .four _ _ _ accessList _ => accessList
    let accessItemCost : (Adr × List B256) → Nat
      | ⟨_, keys⟩ =>
        TX_ACCESS_LIST_ADDRESS_COST + keys.length * TX_ACCESS_LIST_STORAGE_KEY_COST
    (accessList.map accessItemCost).sum

--     auth_cost = Uint(0)
--     if isinstance(tx, SetCodeTransaction):
--         auth_cost += Uint(PER_EMPTY_ACCOUNT_COST * len(tx.authorizations))
  let authCost : Nat :=
    match tx.type with
    | .four _ _ _ _ auths => perEmptyAccountCost * auths.length
    | _ => 0

  ⟨
    txBaseCost + dataCost + createCost + accessListCost + authCost,
    callDataFloorGasCost
  ⟩


def maxInitCodeSize : Nat := maxCodeSize * 2


-- def validate_transaction(tx: Transaction) -> Tuple[Uint, Uint]:
--     intrinsic_gas, calldata_floor_gas_cost = calculate_intrinsic_cost(tx)
--     if max(intrinsic_gas, calldata_floor_gas_cost) > tx.gas:
--         raise InvalidTransaction("Insufficient gas")
--     if U256(tx.nonce) >= U256(U64.MAX_VALUE):
--         raise InvalidTransaction("Nonce too high")
--     if tx.to == Bytes0(b"") and len(tx.data) > MAX_INIT_CODE_SIZE:
--         raise InvalidTransaction("Code size too large")
--
--     return intrinsic_gas, calldata_floor_gas_cost

def validateTransaction (tx : Tx) : Except String (Nat × Nat) := do
  let ⟨intrinsicGas, callDataFloorGasCost⟩ := calculateIntrinsicCost tx


  if max intrinsicGas callDataFloorGasCost > tx.gas
    then .error "InvalidTransaction : Insufficient gas"

  if tx.nonce = B64.max
    then .error "InvalidTransaction : Nonce too high"

  if tx.receiver.isNone && tx.data.length > maxInitcodeSize
    then .error "InvalidTransaction : Code size too large"

  .ok ⟨intrinsicGas, callDataFloorGasCost⟩

def prepareMsg (benv: Benv) (tenv: Tenv) (tx: Tx) :
  Except String Msg := do

  let ⟨currentTarget, msgData, code, codeAddress⟩ :
    Adr × B8L × ByteArray × Option Adr :=
    match tx.receiver with
    | none => ⟨
        compute_contract_address
          tenv.origin
          (benv.state.getNonce tenv.origin - 1),
        [],
        .mk (.mk tx.data),
        none
      ⟩
    | some target => ⟨
        target,
        tx.data,
        benv.state.getCode target,
        target
      ⟩

  let accessedAddresses : AdrSet :=
    tenv.accessListAddresses.insertMany
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, tenv.origin, currentTarget]

  .ok {
    benv := benv,
    tenv := tenv,
    caller := tenv.origin,
    target := tx.receiver,
    gas := tenv.gas,
    value := tx.value.toB256,
    data := msgData,
    code := code,
    depth := 0,
    currentTarget := currentTarget,
    codeAddress := codeAddress
    shouldTransferValue := true,
    isStatic := false,
    accessedAddresses := accessedAddresses,
    accessedStorageKeys := tenv.accessListStorageKeys,
    disablePrecompiles := false
  }

/-
def calculate_total_blob_gas(tx: Transaction) -> Uint:
    """
    Calculate the total blob gas for a transaction.

    Parameters
    ----------
    tx :
        The transaction for which the blob gas is to be calculated.

    Returns
    -------
    total_blob_gas: `ethereum.base_types.Uint`
        The total blob gas for the transaction.
    """
    if isinstance(tx, BlobTransaction):
        return GAS_PER_BLOB * Uint(len(tx.blob_versioned_hashes))
    else:
        return Uint(0)
-/
def calculate_total_blob_gas (tx: Tx) : Nat :=
  match tx.type with
  | .three _ _ _ _ _ blobHashes => GAS_PER_BLOB * blobHashes.length
  | _ => 0


/-
def calculate_data_fee(excess_blob_gas: U64, tx: Transaction) -> Uint:
    """
    Calculate the blob data fee for a transaction.

    Parameters
    ----------
    excess_blob_gas :
        The excess_blob_gas for the execution.
    tx :
        The transaction for which the blob data fee is to be calculated.

    Returns
    -------
    data_fee: `Uint`
        The blob data fee.
    """
    return calculate_total_blob_gas(tx) * calculate_blob_gas_price(
        excess_blob_gas
    )
-/
def calculate_data_fee (excess_blob_gas: Nat) (tx: Tx) : Nat :=
  calculate_total_blob_gas tx * calculate_blob_gas_price excess_blob_gas


def addAssertPos (n : Nat) (z : Int) : Option Nat :=
  match Int.ofNat n + z with
  | .ofNat m => .some m
  | .negSucc _ => none

def subAssertPos (n : Nat) (z : Int) : Option Nat :=
  match Int.ofNat n - z with
  | .ofNat m => .some m
  | .negSucc _ => none

def getTxHash (tx : Tx) : B256 := tx.toBLT.encode.keccak

structure Receipt : Type where
  succeeded : Bool
  gasUsed : Nat
  bloom : B8L
  logs : List Log

def Receipt.toBLT (r : Receipt) : BLT :=
  .list [
    .b8s r.succeeded.toB8L,
    .b8s r.gasUsed.toB8LPack,
    .b8s r.bloom,
    .list (r.logs.map Log.toBLT)
  ]


/-
def make_receipt(
    tx: Transaction,
    error: Optional[EthereumException],
    gasUsed: Uint,
    logs: Tuple[Log, ...],
) -> Union[Bytes, Receipt]:
-/
def makeReceipt
  (tx: Tx)
  (error: Option String)
  (gasUsed: Nat)
  (logs: List Log) : B8L :=

--receipt = Receipt(
--  succeeded=error is None,
--  gasUsed=gasUsed,
--  bloom=logs_bloom(logs),
--  logs=logs,
--)
  let receipt : Receipt := {
    succeeded := error.isNone,
    gasUsed := gasUsed,
    bloom := logs_bloom logs,
    logs := logs
  }
/-
    if isinstance(tx, AccessListTransaction):
        return b"\x01" + rlp.encode(receipt)
    elif isinstance(tx, FeeMarketTransaction):
        return b"\x02" + rlp.encode(receipt)
    elif isinstance(tx, BlobTransaction):
        return b"\x03" + rlp.encode(receipt)
    else:
        return receipt
-/
  let head : B8L :=
    match tx.type with
    | .zero _ => []
    | .one _ _ _ => [0x01]
    | .two _ _ _ _ => [0x02]
    | .three _ _ _ _ _ _ => [0x03]
    | .four _ _ _ _ _ => [0x04]

  head ++ receipt.toBLT.encode


def BlockOutput.init : BlockOutput :=
  {
    blockGasUsed := 0
    transactionsTrie := .empty
    receiptsTrie := .empty
    receiptKeys := []
    blockLogs := []
    withdrawalsTrie := .empty
    blobGasUsed := 0
    requests := []
  }
-- def process_transaction(
--     block_env: vm.Benvironment,
--     block_output: vm.BlockOutput,
--     tx: Transaction,
--     index: Uint,
-- ) -> None:
--     """
--     Execute a transaction against the provided environment.
--
--     This function processes the actions needed to execute a transaction.
--     It decrements the sender's account after calculating the gas fee and
--     refunds them the proper amount after execution. Calling contracts,
--     deploying code, and incrementing nonces are all examples of actions that
--     happen within this function or from a call made within this function.
--
--     Accounts that are marked for deletion are processed and destroyed after
--     execution.
--
--     Parameters
--     ----------
--     block_env :
--         Environment for the Ethereum Virtual Machine.
--     block_output :
--         The block output for the current block.
--     tx :
--         Transaction to execute.
--     index:
--         Index of the transaction in the block.
--     """
def processTransaction
  (vb : Bool) (benv: Benv) (bout : BlockOutput)
  (tx: Tx) (index : Nat) : Except String (Wor × BlockOutput) := do

  -- trie_set(
  --     block_output.transactions_trie,
  --     rlp.encode(index),
  --     encode_transaction(tx),
  -- )
  let mut transactionsTrie : Lean.RBMap B8L Tx compare :=
    bout.transactionsTrie.insert (BLT.b8s index.toB8L).encode tx

--     intrinsic_gas, calldata_floor_gas_cost = validate_transaction(tx)
  let ⟨intrinsicGas, calldataFloorGasCost⟩ ← validateTransaction tx

  --   (
  --       sender,
  --       effective_gas_price,
  --       blob_versioned_hashes,
  --       tx_blob_gas_used,
  --   ) = check_transaction(
  --       block_env=block_env,
  --       block_output=block_output,
  --       tx=tx,
  --   )
  let ⟨
    sender,
    effectiveGasPrice,
    blobVersionedHashes,
    txBlobGasUsed
  ⟩ ← checkTransaction benv bout tx

--     sender_account = get_account(block_env.state, sender)

--     if isinstance(tx, BlobTransaction):
--         blob_gas_fee = calculate_data_fee(block_env.excess_blob_gas, tx)
--     else:
--         blob_gas_fee = Uint(0)
  let blobGasFee :=
    if tx.isTypeThree
    then calculate_data_fee benv.excessBlobGas tx
    else 0

--     effective_gas_fee = tx.gas * effective_gas_price
  let effectiveGasFee := tx.gas * effectiveGasPrice

--     gas = tx.gas - intrinsic_gas
  let gas := tx.gas - intrinsicGas

--     increment_nonce(block_env.state, sender)
  let mut state : Wor := benv.state.incrNonce sender

--     sender_balance_after_gas_fee = (
--         Uint(sender_account.balance) - effective_gas_fee - blob_gas_fee
--     )
--     set_account_balance(
--         block_env.state, sender, U256(sender_balance_after_gas_fee)
--     )
  state ← (state.subBal sender (effectiveGasFee + blobGasFee).toB256).toExcept
    "ERROR : balance underflow"

--     access_list_addresses = set()
--     access_list_storage_keys = set()
--     access_list_addresses.add(block_env.coinbase)
--     if isinstance(
--         tx,
--         (
--             AccessListTransaction,
--             FeeMarketTransaction,
--             BlobTransaction,
--             SetCodeTransaction,
--         ),
--     ):
--         for access in tx.access_list:
--             access_list_addresses.add(access.account)
--             for slot in access.slots:
--                 access_list_storage_keys.add((access.account, slot))
  let preaccessedAddresses : AdrSet :=
    .ofList (benv.coinbase :: tx.accessList.map Prod.fst)
  let preaccessedStorageKeys : KeySet :=
    .ofList (tx.accessList.map <| λ ⟨adr, keys⟩ => keys.map (⟨adr, ·⟩)).flatten

--     authorizations: Tuple[Authorization, ...] = ()
--     if isinstance(tx, SetCodeTransaction):
--         authorizations = tx.authorizations
--
--     tx_env = vm.TransactionEnvironment(
--         origin=sender,
--         gas_price=effective_gas_price,
--         gas=gas,
--         access_list_addresses=access_list_addresses,
--         access_list_storage_keys=access_list_storage_keys,
--         transient_storage=TransientStorage(),
--         blob_versioned_hashes=blob_versioned_hashes,
--         authorizations=authorizations,
--         index_in_block=index,
--         tx_hash=get_transaction_hash(encode_transaction(tx)),
--         traces=[],
--     )
  let tenv : Tenv := {
    origin := sender
    gasPrice := effectiveGasPrice
    gas := gas
    accessListAddresses := preaccessedAddresses
    accessListStorageKeys := preaccessedStorageKeys
    transientStorage := .empty
    blobVersionedHashes := blobVersionedHashes
    auths := tx.auths
    indexInBlock := index
    txHash := getTxHash tx
  }

--     msg = prepare_msg(block_env, tx_env, tx)
  let msg ← prepareMsg benv tenv tx

--     tx_output = process_msg_call(msg)
  let ⟨wor, txOutput⟩ ← processMsgCall vb msg
  state := wor

--     # For EIP-7623 we first calculate the execution_gas_used, which includes
--     # the execution gas refund.
--     tx_gas_used_before_refund = tx.gas - tx_output.gas_left
--     tx_gas_refund = min(
--         tx_gas_used_before_refund // Uint(5), Uint(tx_output.refund_counter)
--     )
  let txGasUsedBeforeRefund := tx.gas - txOutput.gasLeft
  let refundCounter : Nat ←
    (Int.toNat? txOutput.refundCounter).toExcept "ERROR : refund counter is negative"
  let mut txGasRefund : Nat :=
    min (txGasUsedBeforeRefund / 5) refundCounter


--     tx_gas_used_after_refund = tx_gas_used_before_refund - tx_gas_refund
--
--     # Transactions with less execution_gas_used than the floor pay at the
--     # floor cost.
--     tx_gas_used_after_refund = max(
--         tx_gas_used_after_refund, calldata_floor_gas_cost
--     )
  let txGasUsedAfterRefund : Nat :=
    max (txGasUsedBeforeRefund - txGasRefund) calldataFloorGasCost

--     tx_gas_left = tx.gas - tx_gas_used_after_refund
  let txGasLeft :=
    tx.gas - txGasUsedAfterRefund

--     gas_refund_amount = tx_gas_left * effective_gas_price
  let gasRefundAmount : Nat :=
    txGasLeft * effectiveGasPrice

--     # For non-1559 transactions effective_gas_price == tx.gas_price
--     priority_fee_per_gas = effective_gas_price - block_env.base_fee_per_gas
--     transaction_fee = tx_gas_used_after_refund * priority_fee_per_gas
  let priorityFeePerGas := effectiveGasPrice - benv.baseFeePerGas
  let transactionFee := txGasUsedAfterRefund * priorityFeePerGas

--     # refund gas
--     sender_balance_after_refund = get_account(
--         block_env.state, sender
--     ).balance + U256(gas_refund_amount)
--     set_account_balance(block_env.state, sender, sender_balance_after_refund)
  state := state.addBal sender gasRefundAmount.toB256

--     # transfer miner fees
--     coinbase_balance_after_mining_fee = get_account(
--         block_env.state, block_env.coinbase
--     ).balance + U256(transaction_fee)
--     if coinbase_balance_after_mining_fee != 0:
--         set_account_balance(
--             block_env.state,
--             block_env.coinbase,
--             coinbase_balance_after_mining_fee,
--         )
--     elif account_exists_and_is_empty(block_env.state, block_env.coinbase):
--         destroy_account(block_env.state, block_env.coinbase)
  state := state.addBal benv.coinbase transactionFee.toB256

--     for address in tx_output.accounts_to_delete:
--         destroy_account(block_env.state, address)
  for adr in txOutput.accountsToDelete do
    state := destroyAccount state adr

--     block_output.block_gas_used += tx_gas_used_after_refund
--     block_output.blob_gas_used += tx_blob_gas_used
  let mut bout := {
    bout with
    blockGasUsed := bout.blockGasUsed + txGasUsedAfterRefund,
    blobGasUsed := bout.blobGasUsed + txBlobGasUsed
  }

--     receipt = make_receipt(
--         tx, tx_output.error, block_output.block_gas_used, tx_output.logs
--     )
  let receipt :=
    makeReceipt tx txOutput.error bout.blockGasUsed txOutput.logs

--     receipt_key = rlp.encode(Uint(index))
  let receiptKey : B8L := BLT.encode <| .b8s index.toB8L

--     block_output.receipt_keys += (receipt_key,)
--     trie_set(
--         block_output.receipts_trie,
--         receipt_key,
--         receipt,
--     )
--
--     block_output.block_logs += tx_output.logs
  bout := {
    bout with
    receiptKeys := bout.receiptKeys ++ [receiptKey]
    receiptsTrie :=
      bout.receiptsTrie.insert receiptKey receipt
    blockLogs := bout.blockLogs ++ txOutput.logs
  }

  .ok ⟨state, bout⟩

-- /-
-- def process_withdrawal(
--     state: State,
--     wd: Withdrawal,
-- ) -> None:
--     """
--     Increase the balance of the withdrawing account.
--     """
--
--     def increase_recipient_balance(recipient: Account) -> None:
--         recipient.balance += wd.amount * U256(10**9)
--
--     modify_state(state, wd.address, increase_recipient_balance)
-- -/
-- def process_withdrawal -- (state: Wor) (wd: Withdrawal) : Except String Unit :=
--   (state : Wor) (wd : Withdrawal) :  Wor :=
--   state.addBal wd.recipient (wd.amount * (10 ^ 9).toB256)

def processWithdrawals
  (benv : Benv) (bout : BlockOutput) (wds : List Withdrawal) : Wor × BlockOutput :=
  let trie : Lean.RBMap B8L Withdrawal compare :=
    List.foldl (λ acc ⟨i, wd⟩ =>
      acc.insert (BLT.encode <| .b8s i.toB8L) wd) bout.withdrawalsTrie (wds.putIndex 0)
  let state :=
    List.foldl (λ acc wd => acc.addBal wd.recipient (wd.amount * (10 ^ 9).toB256)) benv.state wds
  ⟨state, {bout with withdrawalsTrie := trie}⟩

def B8L.toExStrTx : B8L → Except String Tx
  | [] => .error "error : cannot decode empty transaction BLT"
  | x :: xs =>
    match x, BLT.decode xs with
    | 0x01, BLT.list [
        .b8s chainId,
        .b8s nonce,
        .b8s gasPrice,
        .b8s gas,
        .b8s receiver,
        .b8s value,
        .b8s data,
        accessList,
        .b8s yParity,
        .b8s r,
        .b8s s
      ] => do .ok {
          nonce := nonce.toB64P,
          gas := gas.toNat,
          receiver := receiver.toReceiver?,
          value := value.toNat,
          data := data,
          v := yParity.toNat,
          r := (r.reverse.takeD 32 0).reverse,
          s := (s.reverse.takeD 32 0).reverse,
          type :=
            .one
              gasPrice.toNat
              chainId.toB64P
              (← accessList.toAccessList.toExcept "cannot decode access list")
        }

    | 0x02, BLT.list [
        .b8s chainId,
        .b8s nonce,
        .b8s maxPriorityFee,
        .b8s maxFee,
        .b8s gas,
        .b8s receiver,
        .b8s value,
        .b8s data,
        accessList,
        .b8s yParity,
        .b8s r,
        .b8s s
      ] => do .ok {
        nonce := nonce.toB64P,
        gas := gas.toNat,
        receiver := receiver.toReceiver?,
        value := value.toNat,
        data := data,
        v := yParity.toNat,
        r := (r.reverse.takeD 32 0).reverse,
        s := (s.reverse.takeD 32 0).reverse,
        type :=
          .two
            chainId.toB64P
            maxPriorityFee.toNat
            maxFee.toNat
            (← accessList.toAccessList.toExcept "cannot decode access list")
      }
    | 0x03, BLT.list [
        .b8s chainId,
        .b8s nonce,
        .b8s maxPriorityFee,
        .b8s maxFee,
        .b8s gas,
        .b8s receiver,
        .b8s value,
        .b8s data,
        accessList,
        .b8s maxBlobFee,
        .list blobHashes,
        .b8s yParity,
        .b8s r,
        .b8s s
      ] => do .ok {
        nonce := nonce.toB64P,
        gas := gas.toNat,
        receiver := receiver.toReceiver?,
        value := value.toNat,
        data := data,
        v := yParity.toNat,
        r := (r.reverse.takeD 32 0).reverse,
        s := (s.reverse.takeD 32 0).reverse,
        type :=
          .three
            chainId.toB64P
            maxPriorityFee.toNat
            maxFee.toNat
            (← accessList.toAccessList.toExcept "cannot decode access list")
            maxBlobFee.toNat
            (← mapM (λ r => r.toB256.toExcept "cannot decode blob hash") blobHashes)
      }

    | x, _ => .error s!"ERROR : type-{x} txs do not exist, decoding failed"

def decodeTx : B8L ⊕ Tx → Except String Tx
  | .inl xs => xs.toExStrTx
  | .inr tx => .ok tx

/-
def process_system_transaction(
  block_env: vm.Benvironment,
  target_address: Address,
  system_contract_code: Bytes,
  data: Bytes,
) -> MsgCallOutput:
-/
def processSystemTransaction (vb : Bool) (benv : Benv)
  (target : Adr) (code : ByteArray) (data : B8L) :
  Except String (Wor × MsgCallOutput) := do

--tx_env = vm.TransactionEnvironment(
--  origin=systemAddress,
--  gas_price=block_env.base_fee_per_gas,
--  gas=systemTransactionGas,
--  access_list_addresses=set(),
--  access_list_storage_keys=set(),
--  transient_storage=TransientStorage(),
--  blob_versioned_hashes=(),
--  authorizations=(),
--  index_in_block=None,
--  tx_hash=None,
--  traces=[],
--)
  let txEnv : Tenv := {
    origin := systemAddress,
    gasPrice := benv.baseFeePerGas,
    gas := systemTransactionGas,
    accessListAddresses := .empty,
    accessListStorageKeys := .empty,
    transientStorage := .empty,
    blobVersionedHashes := [],
    auths := [],
    indexInBlock := none,
    txHash := none
  }

--system_tx_msg = Msg(
--  block_env=block_env,
--  tx_env=tx_env,
--  caller=systemAddress,
--  target=target_address,
--  gas=systemTransactionGas,
--  value=U256(0),
--  data=data,
--  code=system_contract_code,
--  depth=Uint(0),
--  currentTarget=target_address,
--  codeAddress=target_address,
--  should_transfer_value=False,
--  isStatic=False,
--  accessedAddresses=set(),
--  accessedStorageKeys=set(),
--  disable_precompiles=False,
--  parent_evm=None,
--)
  let systemTxMsg : Msg := {
    benv := benv,
    tenv := txEnv,
    caller := systemAddress,
    target := target,
    gas := systemTransactionGas,
    value := 0,
    data := data,
    code := code,
    depth := 0,
    currentTarget := target,
    codeAddress := target,
    shouldTransferValue := false,
    isStatic := false,
    accessedAddresses := .empty,
    accessedStorageKeys := .empty
    disablePrecompiles := false
  }

--system_tx_output = process_msg_call(system_tx_msg)
--return system_tx_output
  processMsgCall vb systemTxMsg

def decodeReceipt : B8L ⊕ Receipt → Option Receipt
  | .inl [] => none
  | .inl (x :: xs) => do
    guard (x = 1 ∨ x = 2)
    match BLT.decode xs with
    | BLT.list [
        .b8s succeeded,
        .b8s gasUsed,
        .b8s bloom,
        .list logs
      ] =>
      let logs ← logs.mapM BLT.toLog
      some {
        succeeded := succeeded = []
        gasUsed := gasUsed.toNat,
        bloom := bloom,
        logs := logs
      }
    | _ => none
  | .inr receipt => some receipt


def depositContractAddress : Adr :=
  0x00000000219ab540356cbb839cbe05303d7705fa
def depositEventSignatureHash : B256 :=
  0x649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5

def depositEventLength : Nat := 576

def pubkeyOffset : Nat := 160
def amountOffset : Nat := 320
def signatureOffset : Nat := 384
def indexOffset : Nat := 512
def withdrawalCredentialsOffset := 256

def pubkeySize : Nat := 48
def amountSize : Nat := 8
def indexSize : Nat := 8
def signatureSize : Nat := 96
def withdrawalCredentialsSize : Nat := 32

/-
def extract_deposit_data(data: Bytes) -> Bytes:
-/
def extractDepositData (data : B8L) : Except String B8L := do

--if ulen(data) != DEPOSIT_EVENT_LENGTH:
--    raise InvalidBlock("Invalid deposit event data length")
  if data.length != depositEventLength then
    .error "InvalidBlock : Invalid deposit event data length"

--pubkey_offset = Uint.from_be_bytes(data[0:32])
--if pubkey_offset != PUBKEY_OFFSET:
--    raise InvalidBlock("Invalid pubkey offset in deposit log")
  if data.sliceToNat 0 32 ≠ pubkeyOffset then
    .error "InvalidBlock : Invalid pubkey offset in deposit log"

--withdrawal_credentials_offset = Uint.from_be_bytes(data[32:64])
--if withdrawal_credentials_offset != WITHDRAWAL_CREDENTIALS_OFFSET:
--    raise InvalidBlock(
--        "Invalid withdrawal credentials offset in deposit log"
--    )
  if data.sliceToNat 32 32 ≠ withdrawalCredentialsOffset then
    .error "InvalidBlock : Invalid withdrawal credentials offset in deposit log"

--amount_offset = Uint.from_be_bytes(data[64:96])
--if amount_offset != AMOUNT_OFFSET:
--    raise InvalidBlock("Invalid amount offset in deposit log")
  if data.sliceToNat 64 32 ≠ amountOffset then
    .error "InvalidBlock : Invalid amount offset in deposit log"

--signature_offset = Uint.from_be_bytes(data[96:128])
--if signature_offset != SIGNATURE_OFFSET:
--    raise InvalidBlock("Invalid signature offset in deposit log")
  if data.sliceToNat 96 32 ≠ signatureOffset then
    .error "InvalidBlock : Invalid signature offset in deposit log"

--index_offset = Uint.from_be_bytes(data[128:160])
--if index_offset != INDEX_OFFSET:
--    raise InvalidBlock("Invalid index offset in deposit log")
  if data.sliceToNat 128 32 ≠ indexOffset then
    .error "InvalidBlock : Invalid index offset in deposit log"

--pubkey_size = Uint.from_be_bytes(
--    data[pubkey_offset : pubkey_offset + Uint(32)]
--)
--if pubkey_size != PUBKEY_SIZE:
--    raise InvalidBlock("Invalid pubkey size in deposit log")
  if data.sliceToNat pubkeyOffset 32 ≠ pubkeySize then
    .error "InvalidBlock : Invalid pubkey size in deposit log"

--pubkey = data[
--    pubkey_offset + Uint(32) : pubkey_offset + Uint(32) + PUBKEY_SIZE
--]
  let pubkey : B8L := data.slice! (pubkeyOffset + 32) pubkeySize

--withdrawal_credentials_size = Uint.from_be_bytes(
--    data[
--        withdrawal_credentials_offset : withdrawal_credentials_offset
--        + Uint(32)
--    ],
--)
--if withdrawal_credentials_size != WITHDRAWAL_CREDENTIALS_SIZE:
--    raise InvalidBlock(
--        "Invalid withdrawal credentials size in deposit log"
--    )
  if data.sliceToNat withdrawalCredentialsOffset 32 ≠ withdrawalCredentialsSize then
    .error "InvalidBlock : Invalid withdrawal credentials size in deposit log"

--withdrawal_credentials = data[
--    withdrawal_credentials_offset
--    + Uint(32) : withdrawal_credentials_offset
--    + Uint(32)
--    + WITHDRAWAL_CREDENTIALS_SIZE
--]
  let withdrawalCredentials : B8L :=
    data.slice! (withdrawalCredentialsOffset + 32) withdrawalCredentialsSize

--amount_size = Uint.from_be_bytes(
--    data[amount_offset : amount_offset + Uint(32)]
--)
--if amount_size != AMOUNT_SIZE:
--    raise InvalidBlock("Invalid amount size in deposit log")
  if data.sliceToNat amountOffset 32 ≠ amountSize then
    .error "InvalidBlock : Invalid amount size in deposit log"
--
--amount = data[
--    amount_offset + Uint(32) : amount_offset + Uint(32) + AMOUNT_SIZE
--]
  let amount : B8L := data.slice! (amountOffset + 32) amountSize

--signature_size = Uint.from_be_bytes(
--    data[signature_offset : signature_offset + Uint(32)]
--)
--if signature_size != SIGNATURE_SIZE:
--    raise InvalidBlock("Invalid signature size in deposit log")
  if data.sliceToNat signatureOffset 32 ≠ signatureSize then
    .error "InvalidBlock : Invalid signature size in deposit log"

--signature = data[
--    signature_offset
--    + Uint(32) : signature_offset
--    + Uint(32)
--    + SIGNATURE_SIZE
--]
  let signature : B8L := data.slice! (signatureOffset + 32) signatureSize

--index_size = Uint.from_be_bytes(
--    data[index_offset : index_offset + Uint(32)]
--)
--if index_size != INDEX_SIZE:
--    raise InvalidBlock("Invalid index size in deposit log")
  if data.sliceToNat indexOffset 32 ≠ indexSize then
    .error "InvalidBlock : Invalid index size in deposit log"

--index = data[
--    index_offset + Uint(32) : index_offset + Uint(32) + INDEX_SIZE
--]
  let index : B8L := data.slice! (indexOffset + 32) indexSize

--return pubkey + withdrawal_credentials + amount + signature + index
  .ok (pubkey ++ withdrawalCredentials ++ amount ++ signature ++ index)

/-
def parse_deposit_requests(block_output: BlockOutput) -> Bytes:
-/
def parseDepositRequests
  (bout : BlockOutput) : Except String B8L := do

--deposit_requests: Bytes = b""
  let mut depositRequests : B8L := []

--for key in block_output.receipt_keys:
  for key in bout.receiptKeys do
--  receipt = trie_get(block_output.receipts_trie, key)
--  assert receipt is not None
    let receipt ←
      (bout.receiptsTrie.find? key).toExcept "ERROR : receipt not found"

--  decoded_receipt = decode_receipt(receipt)
    let decodedReceipt ←
      (decodeReceipt (.inl receipt)).toExcept "ERROR : cannot decode receipt"

--  for log in decoded_receipt.logs:
    for log in decodedReceipt.logs do

--    if log.address == DEPOSIT_CONTRACT_ADDRESS:
--      if (
--        len(log.topics) > 0
--        and log.topics[0] == DEPOSIT_EVENT_SIGNATURE_HASH
--      ):
--        request = extract_deposit_data(log.data)
--        deposit_requests += request
      if (
        log.address = depositContractAddress ∧
        log.topics.get? 0 = some depositEventSignatureHash
      ) then
        let request ← extractDepositData log.data
        depositRequests := depositRequests ++ request

--return deposit_requests
  .ok depositRequests


/-
def process_unchecked_system_transaction(
    block_env: vm.BlockEnvironment,
    target_address: Address,
    data: Bytes,
) -> MessageCallOutput:
-/
def processUncheckedSystemTransaction
  (vb : Bool) (benv : Benv) (target : Adr) (data : B8L) :
  Except String (Wor × MsgCallOutput) := do
--system_contract_code = get_account(block_env.state, target_address).code
--return process_system_transaction(
--    block_env,
--    target_address,
--    system_contract_code,
--    data,
--)
  let systemContractCode : ByteArray := benv.state.getCode target
  processSystemTransaction vb benv target systemContractCode data

/-
def process_checked_system_transaction(
    block_env: vm.BlockEnvironment,
    target_address: Address,
    data: Bytes,
) -> MessageCallOutput:
-/
def processCheckedSystemTransaction
  (vb : Bool) (benv : Benv) (target : Adr) (data : B8L) :
  Except String (Wor × MsgCallOutput) := do
--system_contract_code = get_account(block_env.state, target_address).code
  let systemContractCode : ByteArray := benv.state.getCode target

--if len(system_contract_code) == 0:
--    raise InvalidBlock(
--        f"System contract address {target_address.hex()} does not "
--        "contain code"
--    )
  if systemContractCode.isEmpty then
    .error s!"InvalidBlock : System contract address {target.toHex} does not contain code"

--system_tx_output = process_system_transaction(
--    block_env,
--    target_address,
--    system_contract_code,
--    data,
--)
  let ⟨state, systemTxOutput⟩ ←
    processSystemTransaction vb benv target systemContractCode data

--if system_tx_output.error:
--    raise InvalidBlock(
--        f"System contract ({target_address.hex()}) call failed: "
--        f"{system_tx_output.error}"
--    )
--
  if systemTxOutput.error.isSome then
    .error s!"InvalidBlock : System contract ({target.toHex}) call failed: {systemTxOutput.error.get!}"

--return system_tx_output
  .ok ⟨state, systemTxOutput⟩


def depositRequestType : B8L := [0]
def withdrawalRequestType : B8L := [1]
def consolidationRequestType : B8L := [2]

def withdrawalRequestPredeployAddress : Adr := 0x00000961Ef480Eb55e80D19ad83579A64c007002
def CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS : Adr := 0x0000BBdDc7CE488642fb579F8B00f3a590007251
def HISTORY_STORAGE_ADDRESS : Adr := 0x0000F90827F1C53a10cb7A02335B175320002935
def HISTORY_SERVE_WINDOW : Nat := 8192

/-
def process_general_purpose_requests(
    block_env: vm.BlockEnvironment,
    block_output: vm.BlockOutput,
) -> None:
-/
def processGeneralPurposeRequests
  (vb : Bool) (benv : Benv) (bout : BlockOutput) :
  Except String (Wor × BlockOutput) := do

--deposit_requests = parse_deposit_requests(block_output)
--requests_from_execution = block_output.requests
  let depositRequests ← parseDepositRequests bout
  let mut requestsFromExecution : List B8L := bout.requests

--if len(deposit_requests) > 0:
--  requests_from_execution.append(DEPOSIT_REQUEST_TYPE + deposit_requests)
  if depositRequests.length > 0 then
    requestsFromExecution :=
      requestsFromExecution ++ [depositRequestType ++ depositRequests]

--system_withdrawal_tx_output = process_checked_system_transaction(
--  block_env=block_env,
--  target_address=WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS,
--  data=b"",
--)
  let ⟨state, withdrawalOutput⟩  ←
    processCheckedSystemTransaction vb benv
      withdrawalRequestPredeployAddress
      []
  let benv := {benv with state := state}

--if len(system_withdrawal_tx_output.return_data) > 0:
--  requests_from_execution.append(
--    WITHDRAWAL_REQUEST_TYPE + system_withdrawal_tx_output.return_data
--  )
  if withdrawalOutput.returnData.length > 0 then
    requestsFromExecution :=
      requestsFromExecution ++ [withdrawalRequestType ++ withdrawalOutput.returnData]

--system_consolidation_tx_output = process_checked_system_transaction(
--  block_env=block_env,
--  target_address=CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS,
--  data=b"",
--)
  let ⟨state, consolidationOutput⟩  ←
    processCheckedSystemTransaction vb benv
      CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS
      []

--if len(system_consolidation_tx_output.return_data) > 0:
--  requests_from_execution.append(
--    CONSOLIDATION_REQUEST_TYPE
--    + system_consolidation_tx_output.return_data
--  )
  if consolidationOutput.returnData.length > 0 then
    requestsFromExecution :=
      requestsFromExecution ++ [consolidationRequestType ++ consolidationOutput.returnData]

  .ok ⟨state, {bout with requests := requestsFromExecution}⟩

/-
def apply_body(
  block_env: vm.BlockEnvironment,
  transactions: Tuple[LegacyTransaction | Bytes, ...],
  withdrawals: Tuple[Withdrawal, ...],
) -> vm.BlockOutput:
-/
def applyBody
  (vb : Bool) (benv : Benv) (txs : List (B8L ⊕ Tx)) (wds : List Withdrawal) :
  Except String (Wor × BlockOutput) := do

--block_output = vm.BlockOutput()
  let mut bout := BlockOutput.init


  if vb then
    dbg_trace
      "\n================================ BEACON ROOTS TX ================================\n"

--process_unchecked_system_transaction(
--    block_env=block_env,
--    target_address=BEACON_ROOTS_ADDRESS,
--    data=block_env.parent_beacon_block_root,
--)
  let ⟨state, _⟩ ←
    processUncheckedSystemTransaction vb benv
      beaconRootsAddress
      benv.parentBeaconBlockRoot.toB8L
  let mut benv : Benv := {benv with state := state}

  if vb then
    dbg_trace
      "\n================================ HISTORY STORAGE TX ================================\n"

--process_unchecked_system_transaction(
--    block_env=block_env,
--    target_address=HISTORY_STORAGE_ADDRESS,
--    data=block_env.block_hashes[-1],  # The parent hash
--)
  let lastHash ←
     benv.blockHashes.getLast?.toExcept "ERROR : block hashes is empty"
  let ⟨state, _⟩ ←
    processUncheckedSystemTransaction vb benv
      historyStorageAddress
      lastHash.toB8L
  benv := {benv with state := state}

  if vb then
    dbg_trace
      "\n================================ TEST TXS ================================\n"

--for i, tx in enumerate(map(decode_transaction, transactions)):
--    process_transaction(block_env, block_output, tx, Uint(i))
  for ⟨i, tx⟩ in (← txs.mapM decodeTx).putIndex 0 do
    let ⟨state, bout'⟩ ← processTransaction vb benv bout tx i
    benv := {benv with state := state}
    bout := bout'

--process_withdrawals(block_env, block_output, withdrawals)
  let ⟨state, bout'⟩ :=
    processWithdrawals benv bout wds
  benv := {benv with state := state}
  bout := bout'

--process_general_purpose_requests(
--    block_env=block_env,
--    block_output=block_output,
--)
  processGeneralPurposeRequests vb benv bout

-- def applyBody
--   (vb : Bool)
--   (state orig_state : Wor)
--   (created_accounts : AdrSet)
--   (block_hashes: List B256)
--   (coinbase: Adr)
--   (block_number: Nat)
--   (base_fee_per_gas: Nat)
--   (block_gas_limit: Nat)
--   (block_time: B256)
--   (prev_randao: B256)
--   (transactions: List (B8L ⊕ Tx))
--   (chain_id: B64)
--   (withdrawals: List Withdrawal)
--   (parent_beacon_block_root: B256)
--   (excess_blob_gas: Nat) : Except String (ApplyBodyOutput × Wor) := do
--
--   let mut blob_gas_used : Nat := 0
--   let mut gas_available := block_gas_limit
--
--   let mut transactions_trie : Lean.RBMap B8L Tx compare := .empty
--   let mut receipts_trie : Lean.RBMap B8L B8L compare := .empty
--   let mut withdrawals_trie : Lean.RBMap B8L Withdrawal compare := .empty
--   let mut block_logs : List Log := []
--   let beacon_block_roots_contract_code := state.getCode beaconRootsAddress
--
--   let system_tx_msg : Msg := {
--     caller := systemAddress,
--     target := beaconRootsAddress,
--     gas := systemTransactionGas,
--     value := 0
--     data := parent_beacon_block_root.toB8L,
--     code := beacon_block_roots_contract_code,
--     depth := 0
--     currentTarget := beaconRootsAddress,
--     codeAddress := beaconRootsAddress,
--     shouldTransferValue := false,
--     isStatic := False,
--     accessedAddresses := .empty
--     accessedStorageKeys := .empty
--   }
--
--   let system_tx_env : Environment := {
--     caller := systemAddress,
--     origin := systemAddress,
--     block_hashes := block_hashes,
--     coinbase := coinbase,
--     number := block_number,
--     gas_limit := block_gas_limit,
--     base_fee_per_gas := base_fee_per_gas,
--     gas_price := base_fee_per_gas,
--     time := block_time,
--     prev_randao := prev_randao,
--     state := state,
--     orig_state := orig_state,
--     created_accounts := created_accounts
--     chain_id := chain_id,
--     excess_blob_gas := excess_blob_gas,
--     blob_versioned_hashes := [],
--     transient_storage := .empty
--   }
--
--
--   if vb
--     then dbg_trace ("\n================================ SETUP TX ================================\n")
--
--   let mut ⟨state, _⟩ ← processMsgCall vb system_tx_msg system_tx_env
--
--   if vb
--     then
--       dbg_trace ("\nSTATE ROOT AFTER SETUP TX : \n")
--       dbg_trace s!"{state.root.toHex}\n"
--
--   if vb
--     then dbg_trace ("\n================================ TEST TX ================================\n")
--
--   for ⟨i, tx⟩ in (← transactions.mapM decodeTx).putIndex 0 do
--     transactions_trie :=
--       transactions_trie.insert (BLT.b8s i.toB8L).encode tx
--
--     let ⟨sender_address, effective_gas_price, blob_versioned_hashes⟩ ←
--       checkTransaction state tx gas_available chain_id base_fee_per_gas excess_blob_gas
--
--     let env : Environment := {
--         caller := sender_address,
--         origin := sender_address,
--         block_hashes := block_hashes,
--         coinbase := coinbase,
--         number := block_number,
--         gas_limit := block_gas_limit,
--         base_fee_per_gas := base_fee_per_gas,
--         gas_price := effective_gas_price,
--         time := block_time,
--         prev_randao := prev_randao,
--         state := state,
--         orig_state := orig_state,
--         created_accounts := created_accounts,
--         chain_id := chain_id,
--         excess_blob_gas := excess_blob_gas,
--         blob_versioned_hashes := blob_versioned_hashes,
--         transient_storage := .empty
--     }
--
--     let ⟨newState, gas_used, logs, error⟩ ← processTransaction vb env tx
--     state := newState
--     gas_available ← (subAssertPos gas_available gas_used).toExcept "gas underflow"
--
--     let receipt :=
--       make_receipt tx error (block_gas_limit - gas_available) logs
--
--     receipts_trie :=
--       receipts_trie.insert (BLT.b8s i.toB8L).encode receipt
--
--     block_logs := block_logs ++ logs
--     blob_gas_used := blob_gas_used + calculate_total_blob_gas tx
--
--   .assertNot (blob_gas_used > maxBlobGasPerBlock) "InvalidBlock"
--
--   let block_gas_used := block_gas_limit - gas_available
--
--   let block_logs_bloom := logs_bloom block_logs
--
--   for ⟨i, wd⟩ in withdrawals.putIndex 0 do
--     withdrawals_trie :=
--       withdrawals_trie.insert (BLT.b8s i.toB8L).encode wd
--     state := process_withdrawal state wd
--     if AccountExistsAndIsEmpty state wd.recipient then
--       state := destroyAccount state wd.recipient
--
--   let receiptRoot : B256 :=
--     let receiptAux (arg : B8L × B8L) : B8L × B8L :=
--       ⟨arg.fst.toB4s, arg.snd⟩
--     let temp := (List.map receiptAux receipts_trie.toList)
--     trie <| Lean.RBMap.fromList temp _
--
--   let transactionsRoot : B256 ← do
--     let transactionsAux (arg : B8L × Tx) : Except String (B8L × B8L) := do
--       let txBLT : BLT := arg.snd.toBLT
--       .ok ⟨arg.fst.toB4s, txBLT.encode⟩
--     let temp ← List.mapM transactionsAux transactions_trie.toList
--     .ok <| trie <| Lean.RBMap.fromList temp _
--
--   let withdrawalsRoot : B256 :=
--     let withdrawalsAux (arg : B8L × Withdrawal) : B8L × B8L :=
--       ⟨arg.fst.toB4s, arg.snd.toBLT.encode⟩
--     let temp := (List.map withdrawalsAux withdrawals_trie.toList)
--     trie <| Lean.RBMap.fromList temp _
--
--   .ok ⟨
--     {
--       blockGasUsed := block_gas_used
--       transactionsRoot := transactionsRoot
--       receiptRoot := receiptRoot
--       blockLogsBloom := block_logs_bloom
--       stateRoot := state.root
--       withdrawalsRoot := withdrawalsRoot
--       blobGasUsed := blob_gas_used
--       requests := sorry
--     },
--     state
--   ⟩

/-
def get_last_256_block_hashes(chain: BlockChain) -> List[Hash32]:
    """
    Obtain the list of hashes of the previous 256 blocks in order of
    increasing block number.

    This function will return less hashes for the first 256 blocks.

    The ``BLOCKHASH`` opcode needs to access the latest hashes on the chain,
    therefore this function retrieves them.

    Parameters
    ----------
    chain :
        History and current state.

    Returns
    -------
    recent_block_hashes : `List[Hash32]`
        Hashes of the recent 256 blocks in order of increasing block number.
    """
    recent_blocks = chain.blocks[-255:]
    # TODO: This function has not been tested rigorously
    if len(recent_blocks) == 0:
        return []

    recent_block_hashes = []

    for block in recent_blocks:
        prev_block_hash = block.header.parent_hash
        recent_block_hashes.append(prev_block_hash)

    # We are computing the hash only for the most recent block and not for
    # the rest of the blocks as they have successors which have the hash of
    # the current block as parent hash.
    most_recent_block_hash = keccak256(rlp.encode(recent_blocks[-1].header))
    recent_block_hashes.append(most_recent_block_hash)

    return recent_block_hashes
-/
def getLast256BlockHashes (chain : BlockChain) : List B256 :=
  match chain.blocks.reverse.take 255 with
  | [] => []
  | block :: blocks =>
    let hash : B256 := (Header.toBLT block.header).encode.keccak
    let hashes : List B256 :=
      blocks.map <| fun x => x.header.parentHash
    (hash :: hashes).reverse

def computeRequestsHash (requests : List B8L) : B256 :=
  let hashes := requests.map (fun r => r.keccak.toB8L)
  B8L.keccak <| List.flatten hashes




/-
def state_transition(chain: BlockChain, block: Block) -> None:
-/
def state_transition (vb : Bool) (chain : BlockChain) (block : Block) :
  Except String BlockChain := do

--validate_header(chain, block.header)
  validateHeader chain block.header

--if block.ommers != ():
--  raise InvalidBlock
  if ¬block.ommers.isEmpty then do
    .error "InvalidBlock"

--block_env = vm.BlockEnvironment(
--  chain_id=chain.chain_id,
--  state=chain.state,
--  block_gas_limit=block.header.gas_limit,
--  block_hashes=get_last_256_block_hashes(chain),
--  coinbase=block.header.coinbase,
--  number=block.header.number,
--  base_fee_per_gas=block.header.base_fee_per_gas,
--  time=block.header.timestamp,
--  prev_randao=block.header.prev_randao,
--  excess_blob_gas=block.header.excess_blob_gas,
--  parent_beacon_block_root=block.header.parent_beacon_block_root,
--)
  let benv : Benv := {
    chainId := chain.chainId,
    state := chain.state,
    origState := chain.state,
    createdAccounts := .empty,
    blockGasLimit := block.header.gasLimit,
    blockHashes := getLast256BlockHashes chain,
    coinbase := block.header.coinbase,
    number := block.header.number,
    baseFeePerGas := block.header.baseFeePerGas,
    time := block.header.timestamp.toB256,
    prevRandao := block.header.prevRandao,
    excessBlobGas := block.header.excessBlobGas,
    parentBeaconBlockRoot := block.header.parentBeaconBlockRoot
  }


--block_output = apply_body(
--    block_env=block_env,
--    transactions=block.transactions,
--    withdrawals=block.withdrawals,
--)
  let ⟨state, bout⟩ ← applyBody vb benv block.txs block.wds

--block_state_root = state_root(block_env.state)
  let blockStateRoot : B256 := state.root

--transactions_root = root(block_output.transactions_trie)
  let transactionsRoot : B256 ← do
    let transactionsAux (arg : B8L × Tx) : Except String (B8L × B8L) := do
      let txBLT : BLT := arg.snd.toBLT
      .ok ⟨arg.fst.toB4s, txBLT.encode⟩
    let temp ← List.mapM transactionsAux bout.transactionsTrie.toList
    .ok <| trie <| Lean.RBMap.fromList temp _

--receipt_root = root(block_output.receipts_trie)
  let receiptRoot : B256 :=
    let receiptAux (arg : B8L × B8L) : B8L × B8L :=
      ⟨arg.fst.toB4s, arg.snd⟩
    let temp := (List.map receiptAux bout.receiptsTrie.toList)
    trie <| Lean.RBMap.fromList temp _

--block_logs_bloom = logs_bloom(block_output.block_logs)
  let block_logs_bloom := logs_bloom bout.blockLogs

--withdrawals_root = root(block_output.withdrawals_trie)
  let withdrawalsRoot : B256 :=
    let withdrawalsAux (arg : B8L × Withdrawal) : B8L × B8L :=
      ⟨arg.fst.toB4s, arg.snd.toBLT.encode⟩
    let temp := (List.map withdrawalsAux bout.withdrawalsTrie.toList)
    trie <| Lean.RBMap.fromList temp _


--requests_hash = compute_requests_hash(block_output.requests)
  let requestsHash := computeRequestsHash bout.requests

--if block_output.block_gas_used != block.header.gas_used:
--    raise InvalidBlock(
--        f"{block_output.block_gas_used} != {block.header.gas_used}"
--    )
  if bout.blockGasUsed ≠ block.header.gasUsed then
    .error s!"InvalidBlock : {bout.blockGasUsed} != {block.header.gasUsed}"

--if transactions_root != block.header.transactions_root:
--    raise InvalidBlock
  if transactionsRoot ≠ block.header.txsRoot then
    .error "InvalidBlock : transactions root mismatch"

--if block_state_root != block.header.state_root:
--    raise InvalidBlock
  if blockStateRoot ≠ block.header.stateRoot then
    .error "InvalidBlock : state root mismatch"

--if receipt_root != block.header.receipt_root:
--    raise InvalidBlock
  if receiptRoot ≠ block.header.receiptRoot then
    .error "InvalidBlock : receipt root mismatch"

--if block_logs_bloom != block.header.bloom:
--    raise InvalidBlock
  if block_logs_bloom ≠ block.header.bloom then
    .error "InvalidBlock : bloom mismatch"

--if withdrawals_root != block.header.withdrawals_root:
--    raise InvalidBlock
  if withdrawalsRoot ≠ block.header.withdrawalsRoot then
    .error "InvalidBlock : withdrawals root mismatch"

--if block_output.blob_gas_used != block.header.blob_gas_used:
--    raise InvalidBlock
  if bout.blobGasUsed ≠ block.header.blobGasUsed then
    .error "InvalidBlock : blob gas used mismatch"

--if requests_hash != block.header.requests_hash:
--    raise InvalidBlock
  if some requestsHash ≠ block.header.requestsHash then
    .error "InvalidBlock : requests hash mismatch"

--chain.blocks.append(block)
--if len(chain.blocks) > 255:
--    # Real clients have to store more blocks to deal with reorgs, but the
--    # protocol only requires the last 255
--    chain.blocks = chain.blocks[-255:]
  .ok {
    state := state
    blocks := (block :: chain.blocks.reverse.take 254).reverse
    chainId := chain.chainId
  }


-- def state_transition (vb : Bool) (chain : BlockChain) (block : Block) :
--   Except String BlockChain :=
--   match chain.blocks.getLast? with
--   | none => .error "error : cannot fetch last block, chain is empty"
--   | some parentBlock =>
--     let parentHeader := parentBlock.header
--     let excessBlobGas := calculateExcessBlobGas parentHeader
--
--     if (excessBlobGas ≠ block.header.excessBlobGas)
--     then .error "InvalidBlock"
--
--     else do
--
--        validateHeader block.header parentHeader
--
--        .assert block.ommers.isEmpty "InvalidBlock"
--        let (⟨apply_body_output, state⟩ : ApplyBodyOutput × Wor) ←
--          applyBody
--            vb
--            chain.state
--            chain.state
--            .empty
--            (getLast256BlockHashes chain)
--            block.header.coinbase
--            block.header.number
--            block.header.baseFeePerGas
--            block.header.gasLimit
--            block.header.timestamp.toB256
--            block.header.prevRandao
--            block.txs
--            chain.chainId.toUInt64
--            block.wds
--            block.header.parentBeaconBlockRoot
--            excessBlobGas
--
--        .assert
--          ( (apply_body_output.blockGasUsed = block.header.gasUsed) ∧
--            (apply_body_output.transactionsRoot = block.header.txsRoot) ∧
--            (apply_body_output.stateRoot = block.header.stateRoot) ∧
--            (apply_body_output.receiptRoot = block.header.receiptRoot) ∧
--            (apply_body_output.blockLogsBloom = block.header.bloom) ∧
--            (apply_body_output.withdrawalsRoot = block.header.withdrawalsRoot) ∧
--            (apply_body_output.blobGasUsed = block.header.blobGasUsed) )
--          "InvalidBlock"
--
--        .ok {
--          state := state
--          blocks := (block :: chain.blocks.reverse.take 254).reverse
--          chainId := chain.chainId
--        }


def BLT.toExStrWithdrawal : BLT → Except String Withdrawal
  | .list [
      .b8s globalIndex,
      .b8s validatorIndex,
      .b8s recipient,
      .b8s amount
    ] => do
    let globalIndex := globalIndex.toB64P --.toExcept "error : invalid global index"
    let validatorIndex := validatorIndex.toB64P -- ?.toExcept "error : invalid validator index"
    let recipient ← recipient.toAdr?.toExcept "error : invalid recipient address"
    let amount := amount.toB256P -- "error : invalid withdrawal amount"

    .ok {
      globalIndex := globalIndex,
      validatorIndex := validatorIndex,
      recipient := recipient,
      amount := amount
    }
  | _ => .error "error : invalid withdrawal BLT format"

def BLT.toExStrOmmers : BLT → Except String (List Header)
  | .list ommers => ommers.mapM BLT.toExStrHeader
  | _ => .error "error : invalid ommers BLT format"

def BLT.toExStrTx : BLT → Except String Tx
  | .list [
      .b8s nonce,
      .b8s gasPrice,
      .b8s gas,
      .b8s receiver,
      .b8s value,
      .b8s data,
      .b8s v,
      .b8s r,
      .b8s s
    ] => .ok {
      nonce := nonce.toB64P,
      gas := gas.toNat
      receiver := receiver.toReceiver?,
      value := value.toNat,
      data := data,
      v := v.toNat,
      r := r,
      s := s,
      type := .zero gasPrice.toNat
    }
  | .list _ => .error "error : invalid transaction BLT format"
  | .b8s xs => xs.toExStrTx

def BLT.isList : BLT → Bool
  | .list _ => true
  | _ => false

def BLT.toExStrBlock : BLT → Except String Block
  | BLT.list [
      HeaderBLT,
      .list TxBLTs,
      .list OmmerBLTs,
      .list WithdrawalBLTs
    ] => do

    let aux : BLT → Except String (B8L ⊕ Tx)
      | blt@(.list _) => blt.toExStrTx <&> .inr
      | .b8s xs => .ok <| .inl xs

    let header ← HeaderBLT.toExStrHeader
    let txs ← mapM aux TxBLTs
    let ommers ← mapM BLT.toExStrHeader OmmerBLTs
    let withdrawals ← mapM BLT.toExStrWithdrawal WithdrawalBLTs
    .ok {
      header := header,
      txs := txs,
      ommers := ommers,
      wds := withdrawals
    }
  | _ => .error "error : invalid block BLT format"

def exStrToIO {ξ : Type} : Except String ξ → IO ξ
  | .ok x => .ok x
  | .error err => .throw err

/-
rlpToBlock is equivalent to json_to_block from execution-specs.
why does it accept the RLP bytes as input, and not the whole JSON?
the justification is that json_to_block expects the RLP bytes to be
always available, and always uses *only* the RLP bytes to obtain the
block, ignoring everything else in the JSON (the code path that deals
with nonexistent RLP bytes exists, but is unreachable). its return
type also omits the RLP bytes, since this is identical to the input.
-/
def rlpToBlock (rlp : B8L) : IO (Block × B256) := do
  let block_blt ← (BLT.decode rlp).toIO  "error : cannot decode block from rlp"
  let block ← exStrToIO <| block_blt.toExStrBlock
  return ⟨block, (Header.toBLT block.header).encode.keccak⟩



def addBlockToChain (vb : Bool) (chain : BlockChain) (blockRlp : B8L) :
  IO (BlockChain ⊕ String) := do

  let ⟨block, blockHeaderHash⟩ ← rlpToBlock blockRlp

  .cprintln vb "\nSTATE BEFORE TRANSITION :"
  .cprintln vb s!"{chain.state}"

  .guard ((Header.toBLT block.header).encode.keccak = blockHeaderHash) "ERROR : incorrect block header hash"

  let rlp' ← block.toIoBLT <&> BLT.encode

  .guard (blockRlp = rlp') "error : incorrect block rlp"

  let chain ←
    match state_transition vb chain block with
    | .error err => return (.inr err)
    | .ok chain => .ok chain

  .cprintln vb s!"\nSTATE AFTER TEST TX :"
  .cprintln vb s!"{chain.state}"
  .ok (.inl chain)

def getPostStateRoot (json : Lean.Json) : IO B256 :=
  ( do let stateJson ← json.find "postState"
       let state ← stateJson.toWorld
       .ok state.root ) <|>
  (json.find "postStateHash" >>= Lean.Json.toIoB256)

def processBlockJsons (vb : Bool) (chain : BlockChain) :
  List Lean.Json → IO (Option BlockChain)
  | j :: js => do
    let ⟨ex, j⟩ ← getTxExMap j
    match ex with
    | .none =>
      match (← addBlockToChain vb chain j) with
      | .inr ex => .throw s!"unexpected TX exception : {ex}"
      | .inl chain => processBlockJsons vb chain js
    | .some ex =>
      match (← addBlockToChain vb chain j) with
      | .inr ex' =>
        .guard
          --(ex = ex')
          (isEthereumException ex' || isRlpException ex')
          s!"ERROR : {ex'} is not an ethereum exception or an RLP exception"
        .ok none
      | .inl _ =>
        .throw "ERROR : expected exception not raised"
  | [] => .ok <| some chain

def runTest (vb : Bool) (idx? : Option Nat) (nw? : Option String)
  (incls excls : List String) : (Nat × (_ : String) × Lean.Json) → IO Unit
  | ⟨idx, name, json⟩ => do

    match idx? with
    | none => .ok ()
    | some specIdx =>
      if specIdx ≠ idx then
        return ()

    if ¬ (incls.isEmpty ∨ name ∈ incls)
      then return ()

    if name ∈ excls then return ()

    match nw? with
    | none => .ok ()
    | some specNw =>
      let nw ← json.find "network" >>= Lean.Json.toIoString
      if specNw ≠ nw then
        return ()

    .println s!"TEST NAME : {name}"

    let gbh_json ← json.find "genesisBlockHeader"
    let gbh ← gbh_json.toHeader
    let gb : Block := {header := gbh, txs := [], ommers := [], wds := []}
    let gbh_hash ← gbh_json.find "hash" >>= Lean.Json.toIoB256
    let gbh_hash' := (BLT.encode (Header.toBLT gbh)).keccak

    .guard (gbh_hash = gbh_hash') "error : unexpected genesis block header hash."
    let genesisRLP ← json.find "genesisRLP" >>= Lean.Json.toIoB8L
    let genesisRLP' ← gb.toIoBLT <&> BLT.encode
    .guard (genesisRLP = genesisRLP') "error : unexpected genesis block RLP."
    let (chainId : Nat) ←
      match gbh_json.find? "chainId" with
      | .none => .ok 1
      | .some chainIdJson => chainIdJson.toIoB64 <&> UInt64.toNat

    let preState ← json.find "pre" >>= Lean.Json.toWorld

    let chain : BlockChain :=
    {
      blocks := [gb]
      state := preState
      chainId := chainId.toUInt64
    }

    let blockJsons ← json.find "blocks" >>= Lean.Json.toIoList

    let (some chain) ← processBlockJsons vb chain blockJsons | .ok ()


    let lastBlockHash ← json.find "lastblockhash" >>= Lean.Json.toIoB256
    let lastBlock ← chain.blocks.getLast?.toIO "error : no last block "
    let lastBlockHash' := (Header.toBLT lastBlock.header).encode.keccak--  (B8L.keccak ∘ BLT.encode)
    .guard
      (lastBlockHash = lastBlockHash')
      s!"error : last block hash does not match\n  expected : {lastBlockHash}\n  computed : {lastBlockHash'}"

    let postStateRoot ← getPostStateRoot json
    .guard
      (postStateRoot = chain.state.root)
      s!"error : end state root does not match\n  expected : {postStateRoot}\n  computed : {chain.state.root}"

def runPyTestFile (vb : Bool) (idx : Option Nat) (nw : Option String)
  (incls excls : List String) (path : String) : IO Unit := do
  .println "\n================================================================\n"
  .println s!"Testing file : {path}\n"
  let rb ← readJsonFile path >>= Lean.Json.toIoRBNode
  let js := rb.toArray.toList.putIndex 0
  let _ ← js.mapM <| runTest vb idx nw incls excls
  .ok ()


def getTestNames (incls excls : List String) :
  List String → (List String × List String)
  | option :: arg :: strs =>
    if option = "--name"
    then getTestNames (arg :: incls) excls strs
    else
      if option = "--notName"
      then getTestNames incls (arg :: excls) strs
      else getTestNames incls excls (arg :: strs)
  | [_] => ⟨incls, excls⟩
  | [] => ⟨incls, excls⟩

def getTestNetwork : List String → Option String
  | s0 :: s1 :: ss =>
    if s0 = "--network"
    then some s1
    else getTestNetwork <| s1 :: ss
  | _ => none

def getTestIndex : List String → Option Nat
  | s0 :: s1 :: ss =>
    if s0 = "--index"
    then String.toNat? s1
    else getTestIndex <| s1 :: ss
  | _ => none

def main : List String → IO Unit
  | path :: opts => do
    let vb : Bool := List.contains opts "--verbose"
    let idx : Option Nat := getTestIndex opts
    let nw : Option String := getTestNetwork opts
    let ⟨incls, excls⟩ := getTestNames [] [] opts
    let b ← System.FilePath.isDir path
    if !b
    then runPyTestFile vb idx nw incls excls path
    else do
      let fs ← System.FilePath.walkDir path
      let _← mapM (runPyTestFile vb idx nw incls excls) (fs.toList.map System.FilePath.toString)
      pure ()
  | _ => IO.throw "error : invalid arguments"




-- def Bytes.toHexLine (bs : Bytes) : String :=
--   s!"hex\"{bs.toHex}\""
--
-- def WethByteCode : String :=
--   List.foldr
--      (λ s0 s1 => s0 ++ "\n" ++ s1)
--      "" <| List.map Bytes.toHexLine
--         <| List.chunks 31 <| Option.getD weth.compile []
