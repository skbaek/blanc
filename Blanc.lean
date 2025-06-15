import Lean.Data.Json
import Lean.Data.Json.Parser
import Lean.Data.HashSet
import Mathlib.Data.ZMod.Defs
import «Blanc».Weth

inductive TxEx : Type
  | noBlobs
  | tooManyBlobs
  | blobCreation
  | wrongBlobHashVersion
  | initCodeTooLong
  | nonceTooHigh
  | executionException
  | testException
  | invalidBlock
deriving DecidableEq

def TxEx.toString : TxEx → String
  | noBlobs => "noBlobs"
  | tooManyBlobs => "tooManyBlobs"
  | blobCreation => "blobCreation"
  | wrongBlobHashVersion => "wrongBlobHashVersion"
  | initCodeTooLong => "initCodeTooLong"
  | nonceTooHigh => "nonceTooHigh"
  | executionException => "executionException"
  | testException => "testException"
  | invalidBlock => "invalidBlock"

instance : ToString TxEx := ⟨TxEx.toString⟩

def AccessList : Type := List (Adr × List B256)

instance : ToString AccessList := ⟨λ x => @List.toString _ _ x⟩

def readJsonFile (filename : System.FilePath) : IO Lean.Json := do
  let contents ← IO.FS.readFile filename
  match Lean.Json.parse contents with
  | .ok json => pure json
  | .error err => throw (IO.userError err)


mutual
  partial def StringJson.toStrings : ((_ : String) × Lean.Json) → List String
    | ⟨n, j⟩ =>
      --(sj.fst :: Lean.Json.toStrings sj.snd) ++ StringJsons.toStrings sjs
      (fork n [Lean.Json.toStrings j])
  partial def StringJsons.toStrings : List ((_ : String) × Lean.Json) → List String
    | [] => []
    | ⟨n, j⟩ :: njs =>
      --(sj.fst :: Lean.Json.toStrings sj.snd) ++ StringJsons.toStrings sjs
      (fork n [Lean.Json.toStrings j]) ++ StringJsons.toStrings njs

  partial def Lean.Jsons.toStrings : List Lean.Json → List String
    | [] => []
    | j :: js => Lean.Json.toStrings j ++ Lean.Jsons.toStrings js

  partial def Lean.Json.toStrings : Lean.Json → List String
    | .null => ["[NULL]"]
    | .bool b => [s!"[BOOL] {b}"]
    | .num n => [s!"[NUM] {n}"]
    | .str s => --[s!"str : {s}"]
       fork "[STR]" [s.chunks 80]
    | .arr js =>
      fork "[ARR]" (js.toList.map Lean.Json.toStrings)
      --"arr :" :: (Lean.Jsons.toStrings js.toList).map ("  " ++ ·)
    | .obj m => do
      let kvs := m.toArray.toList
      --"obj : " :: (StringJsons.toStrings kvs).map ("  " ++ ·)
      fork "[OBJ]" (kvs.map StringJson.toStrings)
end

def Lean.Json.toString (j : Lean.Json) : String := String.joinln j.toStrings

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

def Lean.Json.fromArr : Lean.Json → IO (List Json)
  | .arr a => return a.toList
  | _ => IO.throw "not an array"

def Lean.Json.fromObj : Lean.Json → IO (RBNode String (λ _ => Json))
  | .obj r => return r
  | _ => IO.throw "not an object"

def Lean.Json.fromStr? : Lean.Json → Option String
  | .str s => some s
  | _ => none

def Lean.Json.fromStr : Lean.Json → IO String
  | .str s => return s
  | _ => IO.throw "not a string"

def Lean.Json.fromNum : Lean.Json → IO JsonNumber
  | .num n => return n
  | _ => IO.throw "not a number"

def Lean.JsonNumber.toNat : JsonNumber → IO Nat
  | ⟨.ofNat x, 0⟩ => return x
  | ⟨.negSucc _, _⟩ => IO.throw "negative mantissa"
  | ⟨_, e + 1⟩ => IO.throw s!"nonzero exponent : {e + 1}"

def Lean.Json.fromSingleton : Lean.Json → IO (String × Lean.Json)
  | .obj (.node _ .leaf k v .leaf) => return ⟨k, v⟩
  | j => IO.throw s!"non-singleton JSON : {j}"

def parseTxEx : String → Option TxEx
  | "TransactionException.TYPE_3_TX_ZERO_BLOBS" => some .noBlobs
  | "TransactionException.TYPE_3_TX_BLOB_COUNT_EXCEEDED" => some .tooManyBlobs
  | "TransactionException.TYPE_3_TX_CONTRACT_CREATION" => some .blobCreation
  | "TransactionException.TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH" => some .wrongBlobHashVersion
  | "TransactionException.INITCODE_SIZE_EXCEEDED" => some .initCodeTooLong
  | "TransactionException.NONCE_IS_MAX" => some .nonceTooHigh
  | _ => .none

def Lean.Json.toB8L? (j : Json) : Option B8L := do
  let x ← fromStr? j >>= .remove0x
  (Hex.toB8L x)

def Lean.Json.toIoB8L (j : Json) : IO B8L := do
  let x ← fromStr j >>= .remove0x
  (Hex.toB8L x).toIO ""

def Lean.Json.toAdr? (j : Json) : Option Adr := do
  let x ← fromStr? j >>= .remove0x
  (Hex.toAdr? x)

def Lean.Json.toIoAdr (j : Json) : IO Adr := do
  let x ← fromStr j >>= .remove0x
  (Hex.toAdr? x).toIO ""

-- def Lean.Json.toIoOptionAdr (j : Json) : IO (Option Adr) := do
--   let s ← fromStr j
--   match s with
--   | "" => pure .none
--   | _ => do
--     let s' ← .remove0x s
--     (Hex.toAdr s').toIO ""

def Lean.Json.toIoAdrs (j : Json) : IO (List Adr) :=
  fromArr j >>= mapM toIoAdr

def Lean.Json.toB64? (j : Json) : Option B64:= do
  let x ← fromStr? j >>= .remove0x
  (Hex.toB64? x)

def Lean.Json.toIoB64 (j : Json) : IO B64 := do
  let x ← fromStr j >>= .remove0x
  (Hex.toB64? x).toIO

def Lean.Json.toB256? (j : Json) : Option B256 := do
  let x ← fromStr? j >>= .remove0x
  Hex.toB256? x

def Lean.Json.toIoB256 (j : Json) : IO B256 := do
  let x ← fromStr j >>= .remove0x
  (Hex.toB256? x).toIO ""

def Lean.Json.toIoB64P (j : Json) : IO B64 := do
  let x ← fromStr j >>= .remove0x
  let xs ← (Hex.toB8L x).toIO ""
  return (B8L.toB64P xs)

def Lean.Json.toIoB256P (j : Json) : IO B256 := do
  let x ← fromStr j >>= .remove0x
  let xs ← (Hex.toB8L x).toIO ""
  return (B8L.toB256P xs)

def Lean.Json.toIoAccessEntry (j : Json) : IO (Adr × List B256) := do
  let r ← fromObj j
  let a ← (r.find compare "address").toIO "" >>= toIoAdr
  let ks ← (r.find compare "storageKeys").toIO "" >>= fromArr >>= mapM toIoB256P
  return ⟨a, ks⟩

def Lean.Json.toIoAccessList (j : Json) : IO AccessList := do
  fromArr j >>= mapM toIoAccessEntry

def helper (xy :(_ : String) × Lean.Json) : IO (B256 × B256) := do
  let x ← .remove0x xy.fst
  let bs ← (Hex.toB8L x).toIO ""
  let bs' ← xy.snd.toIoB8L
  return ⟨bs.toB256P, bs'.toB256P⟩

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
  ]

instance : ToString Header := ⟨String.joinln ∘ Header.toStrings⟩

def B256.toBytes (x : B256) : Bytes := x.toB8L.map B8.toByte
def B64.toBytes (x : B64) : Bytes := x.toB8L.map B8.toByte
def Adr.toBytes (adr : Adr) : Bytes := adr.toB8L.map B8.toByte

def Nat.toBytesNil (nat : Nat) : Bytes := nat.toB8LNew.map B8.toByte

def Header.toBLT (header : Header) : BLT :=
  BLT.list [
    BLT.b8s header.parentHash.toB8L,
    BLT.b8s header.ommersHash.toB8L,
    BLT.b8s header.coinbase.toB8L,
    BLT.b8s header.stateRoot.toB8L,
    BLT.b8s header.txsRoot.toB8L,
    BLT.b8s header.receiptRoot.toB8L,
    BLT.b8s header.bloom,
    BLT.b8s header.difficulty.toB8LNew,
    BLT.b8s header.number.toB8LNew,
    BLT.b8s header.gasLimit.toB8LNew,
    BLT.b8s header.gasUsed.toB8LNew,
    BLT.b8s header.timestamp.toB8LNew,
    BLT.b8s header.extraData,
    BLT.b8s header.prevRandao.toB8L,
    BLT.b8s header.nonce.toB8L,
    BLT.b8s header.baseFeePerGas.toB8LNew,
    BLT.b8s header.withdrawalsRoot.toB8L,
    BLT.b8s header.blobGasUsed.toB8LNew,
    BLT.b8s header.excessBlobGas.toB8LNew,
    BLT.b8s header.parentBeaconBlockRoot.toB8L
  ]

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

-- structure Tx : Type where
--   (nonce : B64)
--   (gasLimit : B256)
--   (receiver : Option Adr)
--   (val : B256)
--   (calldata : B8L)
--   (yParity : Bool)
--   (r : B8L)
--   (s : B8L)
--   (type : TxType)
--
-- structure Stx : Type where
--   (nonce : B64)
--   (gasLimit : B256)
--   (sender : Adr)
--   (receiver : Option Adr)
--   (val : B256)
--   (calldata : B8L)
--   (type : TxType)
--
-- structure LegacyTx : Type where
--   nonce : B64
--   gasPrice : Nat
--   gas : Nat
--   receiver : Option Adr
--   value : Nat
--   data : B8L
--   v : Nat
--   r : B8L --B256
--   s : B8L --B256

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

def B8L.sig (bs : B8L) : B8L := List.dropWhile (· = 0) bs

def AccessList.toBLT (al : AccessList) : BLT :=
  let aux : Adr × List B256 → BLT
  | ⟨adr, words⟩ =>
    .list [.b8s adr.toB8L, .list (words.map (.b8s ∘ B256.toB8L))]
  .list (al.map aux)

def Tx.toBLT (tx : Tx) : BLT :=
  match tx.type with
  | .zero gasPrice =>
    .list [
      .b8s tx.nonce.toNat.toB8LNew,
      .b8s gasPrice.toB8LNew,
      .b8s tx.gas.toB8LNew,
      .b8s <| tx.receiver.rec [] Adr.toB8L,
      .b8s tx.value.toB8LNew,
      .b8s tx.data,
      .b8s tx.v.toB8LNew,
      .b8s tx.r,
      .b8s tx.s,
    ]
  | .one gasPrice chainId accessList =>
    .list [
      .b8s chainId.toB8L.sig,
      .b8s tx.nonce.toNat.toB8LNew,
      .b8s gasPrice.toB8LNew,
      .b8s tx.gas.toB8LNew,
      .b8s <| tx.receiver.rec [] Adr.toB8L,
      .b8s tx.value.toB8LNew,
      .b8s tx.data,
      accessList.toBLT,
      .b8s tx.v.toB8LNew,
      .b8s tx.r,
      .b8s tx.s
    ]
  | .two chainId maxPriorityFee maxFee accessList =>
    .list [
      .b8s chainId.toB8L.sig,
      .b8s tx.nonce.toNat.toB8LNew,
      .b8s maxPriorityFee.toB8LNew,
      .b8s maxFee.toB8LNew,
      .b8s tx.gas.toB8LNew,
      .b8s <| tx.receiver.rec [] Adr.toB8L,
      .b8s tx.value.toB8LNew,
      .b8s tx.data,
      accessList.toBLT,
      .b8s tx.v.toB8LNew,
      .b8s tx.r,
      .b8s tx.s
    ]
  | .three chainId maxPriorityFee maxFee accessList maxBlobFee blobHashes =>
    .list [
      .b8s chainId.toB8L.sig,
      .b8s tx.nonce.toNat.toB8LNew,
      .b8s maxPriorityFee.toB8LNew,
      .b8s maxFee.toB8LNew,
      .b8s tx.gas.toB8LNew,
      .b8s <| tx.receiver.rec [] Adr.toB8L,
      .b8s tx.value.toB8LNew,
      .b8s tx.data,
      accessList.toBLT,
      .b8s maxBlobFee.toB8LNew,
      .list <| blobHashes.map <| .b8s ∘ B256.toB8L,
      .b8s tx.v.toB8LNew,
      .b8s tx.r,
      .b8s tx.s
    ]

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
    block.header.toBLT,
    .list txBLTs,
    .list <| block.ommers.map Header.toBLT,
    .list <| block.wds.map Withdrawal.toBLT
  ]

def Lean.RBMap.fromSingleton {ξ υ f} (m : RBMap ξ υ f) : Option (ξ × υ) :=
  match m.toList with
  | [kv] => some kv
  | _ => none

def Lean.RBMap.singleton {ξ υ f} (x : ξ) (y : υ) : RBMap ξ υ f := RBMap.empty.insert x y

def TxType.gasPrice (baseFee : Nat) : TxType → Nat
  | .zero gp => gp
  | .one gp _ _ => gp
  | .two _ mpf mf _ => min mf (baseFee + mpf)
  | .three _ mpf mf _ _ _ => min mf (baseFee + mpf)

-- def TxType.chainId : TxType → B64
--   | .zero _ cid => cid.getD 1
--   | .one _ cid _ => cid
--   | .two cid _ _ _ => cid
--   | .three cid _ _ _ _ _ => cid

def TxType.accessList : TxType → AccessList
  | .zero _ => []
  | .one _ _ al => al
  | .two _ _ _ al => al
  | .three _ _ _ al _ _ => al

def TxType.isBlobTx : TxType → Bool
  | .three _ _ _ _ _ _ => 1
  | _ => 0

def TxType.blobHashes : TxType → List B256
  | .zero _ => []
  | .one _ _ _ => []
  | .two _ _ _ _ => []
  | .three _ _ _ _ _ bhs => bhs

-- def Stx.blobHashes (tx : Stx) : List B256 := tx.type.blobHashes
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

-- def BLT.toLegacyTxHash : BLT → IO (Tx × B256)
--   | BLT.list [
--       .b8s nonce,
--       .b8s gasPrice,
--       .b8s gasLimit,
--       .b8s receiver,
--       .b8s val,
--       .b8s calldata,
--       .b8s [v],
--       .b8s r,
--       .b8s s
--     ] => do
--     let ⟨yParity, chainId⟩ ← decodeV v
--     let bs :=
--       BLT.encode <|
--         .list [
--           .b8s nonce,
--           .b8s gasPrice,
--           .b8s gasLimit,
--           .b8s receiver,
--           .b8s val,
--           .b8s calldata
--         ]
--     return ⟨
--       {
--         nonce := nonce.toB64P
--         gas := gasLimit.toNat --B256P
--         receiver := (← receiver.toReceiver)
--         value := val.toB256P
--         data := calldata
--         yParity := yParity
--         r := (r.reverse.takeD 32 0).reverse
--         s := (s.reverse.takeD 32 0).reverse
--         type :=
--           .zero gasPrice.toB256P chainId
--       },
--       bs.keccak
--     ⟩
--   | _ => IO.throw "error : cannot RLP-decode for type-0 tx"

-- def decodeTxHash : B8L → IO (Tx × B256)
--   | [] => IO.throw "error : cannot decode empty bytes"
--   | 0x01 :: _ => IO.throw "unimplemented : Type-1 tx decoding"
--   | 0x02 :: tbs =>
--     match BLT.decode tbs with
--     | BLT.list [
--         .b8s chainId,
--         .b8s nonce,
--         .b8s maxPriorityFee,
--         .b8s maxFee,
--         .b8s gasLimit,
--         .b8s receiver,
--         .b8s val,
--         .b8s calldata,
--         accessList,
--         .b8s yParity,
--         .b8s r,
--         .b8s s
--       ] => do
--       let bs : B8L :=
--         BLT.encode <|
--           .list [
--             .b8s chainId,
--             .b8s nonce,
--             .b8s maxPriorityFee,
--             .b8s maxFee,
--             .b8s gasLimit,
--             .b8s receiver,
--             .b8s val,
--             .b8s calldata,
--             accessList
--           ]
--
--       return ⟨
--         {
--           nonce := nonce.toB64P
--           gasLimit := gasLimit.toB256P
--           receiver := (← receiver.toReceiver)
--           val := val.toB256P
--           calldata := calldata
--           yParity := (← decodeYParity yParity)
--           r := (r.reverse.takeD 32 0).reverse
--           s := (s.reverse.takeD 32 0).reverse
--           type :=
--             .two
--               chainId.toNat
--               maxPriorityFee.toB256P
--               maxFee.toB256P
--               (← accessList.toAccessList.toIO "cannot decode access list")
--         },
--         B8L.keccak (0x02 :: bs)
--       ⟩
--     | _ => IO.throw "error : cannot decode type-2 tx"
--   | 0x03 :: tbs =>
--     match BLT.decode tbs with
--     | BLT.list [
--         .b8s chainId,
--         .b8s nonce,
--         .b8s maxPriorityFee,
--         .b8s maxFee,
--         .b8s gasLimit,
--         .b8s receiver,
--         .b8s val,
--         .b8s calldata,
--         accessList,
--         .b8s maxBlobFee,
--         .list blobHashes,
--         .b8s yParity,
--         .b8s r,
--         .b8s s
--       ] => do
--       let bs : B8L :=
--         BLT.encode <|
--           .list [
--             .b8s chainId,
--             .b8s nonce,
--             .b8s maxPriorityFee,
--             .b8s maxFee,
--             .b8s gasLimit,
--             .b8s receiver,
--             .b8s val,
--             .b8s calldata,
--             accessList,
--             .b8s maxBlobFee,
--             .list blobHashes,
--           ]
--       return ⟨
--         {
--           nonce := nonce.toB64P
--           gasLimit := gasLimit.toB256P
--           receiver := (← receiver.toReceiver)
--           val := val.toB256P
--           calldata := calldata
--           yParity := (← decodeYParity yParity)
--           r := (r.reverse.takeD 32 0).reverse
--           s := (s.reverse.takeD 32 0).reverse
--           type :=
--             .three
--               chainId.toNat
--               maxPriorityFee.toB256P
--               maxFee.toB256P
--               (← accessList.toAccessList.toIO "cannot decode access list")
--               maxBlobFee.toB256P
--               (← mapM (λ r => r.toB256.toIO "") blobHashes)
--         },
--         B8L.keccak (0x03 :: bs)
--         -- B8L.keccak (0x03 :: bs)
--       ⟩
--     | _ => IO.throw "error : cannot RLP-decode for type-3 tx"
--   | bs => do
--     let r ← (BLT.decode bs).toIO "cannot RLP-decode legacy TX"
--     r.toLegacyTxHash

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
def GAS_STORAGE_UPDATE := 5000

def maxCodeSize : Nat := 24576 -- 0x00006000
def maxInitcodeSize : Nat := 49152-- 0x0000C000
-- def maxNonce : Nat := (2 ^ 64) - 1

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


def Mem : Type := Array B8

structure Log : Type where
  (address : Adr)
  (topics : List B256)
  (data : B8L)

structure Environment : Type where
  caller : Adr
  block_hashes : List B256
  origin : Adr
  coinbase : Adr
  number : Nat
  base_fee_per_gas : Nat
  gas_limit : Nat
  gas_price : Nat
  time : B256
  prev_randao: B256
  state: Wor
  orig_state : Wor
  created_accounts : AdrSet
  chain_id: B64
  excess_blob_gas: Nat
  blob_versioned_hashes: List B256
  transient_storage: Tra --transient storage

structure Message : Type where
  caller: Adr
  target: Option Adr
  current_target: Adr
  gas: Nat
  value: B256
  data: B8L
  code_address: Option Adr
  code: ByteArray
  depth: Nat
  should_transfer_value: Bool
  is_static: Bool
  accessed_addresses: AdrSet
  accessed_storage_keys: KeySet
  -- parent_evm: Option Evm

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
    "KzgProofError"
  ]

def isException (ex : String) (exs : List String) : Bool :=
  let aux (s : String) : Bool :=
    s = ex || String.isPrefixOf (s ++ " : ") ex
  exs.any aux

def isEthereumException (ex : String) : Bool :=
  isException ex [
    "InvalidBlock",
    "InvalidTransaction"
  ]

def isRlpException (ex : String) : Bool :=
  isException ex [
    "EncodingError",
    "DecodingError"
  ]

--   | stackUnderflowError
--   | stackOverflowError
--   | outOfGasError
--   | invalidOpcode : B8 → ExHalt
--   | invalidJumpDestError
--   | stackDepthLimitError
--   | writeInStaticContext
--   | outOfBoundsRead
--   | invalidParameter
--   | invalidContractPrefix
--   | addressCollision
--   | kzgProofError

-- inductive ExHalt : Type
--   | stackUnderflowError
--   | stackOverflowError
--   | outOfGasError
--   | invalidOpcode : B8 → ExHalt
--   | invalidJumpDestError
--   | stackDepthLimitError
--   | writeInStaticContext
--   | outOfBoundsRead
--   | invalidParameter
--   | invalidContractPrefix
--   | addressCollision
--   | kzgProofError
-- deriving DecidableEq
--
-- inductive GenEx : Type
--   | assertionError
-- deriving DecidableEq
--
-- inductive EthEx : Type
--   | revert
--   | limit
--   | exHalt : ExHalt → EthEx
--   | gen : GenEx → EthEx
-- deriving DecidableEq

structure Evm : Type where
  pc : Nat
  stack: List B256
  memory: Mem
  code: ByteArray
  gas_left: Nat
  env: Environment
  -- valid_jump_destinations: Set[Uint]
  logs: List Log -- Tuple[Log, ...]
  refund_counter: Nat
  running: Bool
  message: Message
  output: B8L
  accounts_to_delete: AdrSet
  touched_accounts: AdrSet
  return_data: B8L
  error: Option String -- Optional[EthereumException]
  accessed_addresses: AdrSet
  accessed_storage_keys: KeySet

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
  ⟨⟨0, a.high.toUInt64⟩ , ⟨a.mid, a.low⟩ ⟩

def execute_ecrec (evm : Evm) : Except (Evm × String) Evm := do
  let data := evm.message.data
  let evm ← chargeGas gas_ecrecover evm
  let message_hash := B8L.toB256P <| data.sliceD 0 32 (0x00 : B8)
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
    match ecrecover message_hash v.get! r s with
    | none => .ok evm
    | some address =>
      let padded_address := address.toB256.toB8L
      .ok {evm with output := padded_address}

def GAS_SHA256 : Nat := 60
def GAS_SHA256_WORD : Nat := 12

def execute_sha (evm : Evm) : Except (Evm × String) Evm := do
  let data := evm.message.data
  let word_count := ceilDiv data.length 32
  let evm ← chargeGas (GAS_SHA256 + GAS_SHA256_WORD * word_count) evm
  let hash : B256 := B8L.sha256 data
  .ok {evm with output := hash.toB8L}

def GAS_RIPEMD160 : Nat := 600
def GAS_RIPEMD160_WORD : Nat := 120

def execute_ripemd160 (evm : Evm) : Except (Evm × String) Evm := do
  let data := evm.message.data
  let word_count := ceilDiv data.length 32
  let evm ← chargeGas (GAS_RIPEMD160 + GAS_RIPEMD160_WORD * word_count) evm
  let hash : B256 := B8L.toB256P <| (rip160 ⟨.mk data⟩).toList
  .ok {evm with output := hash.toB8L}

def GAS_IDENTITY : Nat := 15
def GAS_IDENTITY_WORD : Nat := 3

def execute_id (evm : Evm) : Except (Evm × String) Evm := do
  let data := evm.message.data
  let word_count := ceilDiv data.length 32
  let evm ← chargeGas (GAS_IDENTITY + GAS_IDENTITY_WORD * word_count) evm
  .ok {evm with output := data}

def execute_modexp (evm : Evm) : Except (Evm × String) Evm := do
  let data := evm.message.data
  let f : Nat → Nat := λ x => (ceilDiv x 8) ^ 2
  let gQuadDivisor : Nat := 3
  let l_B : Nat := B8L.toNat <| data.sliceD 0 32 (0x00 : B8)
  let l_E : Nat := B8L.toNat <| data.sliceD 32 32 (0x00 : B8)
  let l_M : Nat := B8L.toNat <| data.sliceD 64 32 (0x00 : B8)
  let B : Nat := B8L.toNat   <| data.sliceD 96 l_B (0 : B8)
  let E : Nat := B8L.toNat   <| data.sliceD (96 + l_B) l_E (0 : B8)
  let E_pfx : Nat := B8L.toNat <| data.sliceD (96 + l_B) 32 (0 : B8)
  let M : Nat := B8L.toNat   <| data.sliceD (96 + l_B + l_E) l_M (0 : B8)
  let l'_E : Nat :=
    if l_E ≤ 32
    then
      if E = 0
      then 0
      else Nat.log2 E
    else
      if E_pfx = 0
      then 8 * (l_E - 32)
      else (8 * (l_E - 32)) + Nat.log2 E_pfx
  let cost : Nat := max 200 <| (f (max l_M l_B) * max l'_E 1) / gQuadDivisor
  let evm ← chargeGas cost evm
  let expmod : Nat := Nat.powMod B E M
  .ok {evm with output := B8L.pack expmod.toB8LPack l_M}

abbrev altBn128Prime : Nat := 21888242871839275222246405745257275088696311157297823662689037894645226208583

structure FF (p : Nat) : Type where
  (val : Nat)
deriving DecidableEq

-- abbrev BNF : Type := ZMod altBn128Prime
abbrev BNF : Type := FF altBn128Prime

structure Point : Type where
  (x : BNF)
  (y : BNF)

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

def Point.toString : Point → String
  | ⟨x, y⟩ => s!"⟨{x.val.toHex}, {y.val.toHex}⟩"

instance : ToString Point := ⟨Point.toString⟩

def FF.mkMod {p : Nat} (n : Nat) : FF p := ⟨n % p⟩

instance {p n : Nat} : OfNat (FF p) n := ⟨.mkMod n⟩

def FF.pow {p : Nat} (b : FF p) (e : Nat) : FF p :=
  ⟨Nat.powMod b.val e p⟩

instance {p} : HPow (FF p) Nat (FF p) := ⟨FF.pow⟩

def FF.add {p : Nat} (x y : FF p) : FF p :=
  ⟨(x.val + y.val) % p⟩

instance {p} : HAdd (FF p) (FF p) (FF p) := ⟨FF.add⟩

def FF.sub {p : Nat} (x y : FF p) : FF p :=
  ⟨Int.natAbs <| (Int.ofNat x.val - Int.ofNat y.val) % p⟩

instance {p} : HSub (FF p) (FF p) (FF p) := ⟨FF.sub⟩

def FF.mul {p : Nat} (x y : FF p) : FF p :=
  ⟨(x.val * y.val) % p⟩

instance {p} : HMul (FF p) (FF p) (FF p) := ⟨FF.mul⟩

def Point.mk? (x : Nat) (y : Nat) : Option Point := do
  let x' : BNF := FF.mkMod x
  let y' : BNF := FF.mkMod y
  if (x' = 0 ∧ y' = 0)
  then some ⟨0, 0⟩
  else if y' ^ 2 = (x' ^ 3) + 3
       then some ⟨x', y'⟩
       else none

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


def FF.inv {p : Nat} (x : FF p) : FF p :=
  let ⟨c, _, _⟩ := extEuclid x.val p
  ⟨(c % p).natAbs⟩

instance {p} : Inv (FF p) := ⟨FF.inv⟩

def FF.div {p : Nat} (x y : FF p) : FF p := x * (y⁻¹)

instance {p} : HDiv (FF p) (FF p) (FF p) := ⟨FF.div⟩

def Point.double (p : Point) : Point :=
  if p.x = 0 ∧ p.y = 0
  then p
  else
    let lam : BNF := (3 * (p.x ^ 2)) / (2 * p.y)
    let x := lam ^ 2 - p.x - p.x
    let y := lam * (p.x - x) - p.y
    ⟨x, y⟩

def Point.add : Point → Point → Point
  | ⟨0, 0⟩, q => q
  | p, ⟨0, 0⟩ => p
  | ⟨selfX, selfY⟩, ⟨otherX, otherY⟩ =>
    if selfX = otherX
    then
      if selfY = otherY
      then Point.double ⟨selfX, selfY⟩
      else ⟨0, 0⟩
    else
      let yDiff := otherY - selfY
      let xDiff := otherX - selfX
      let lam := yDiff / xDiff
      let x := lam ^ 2 - selfX - otherX
      let y := lam * (selfX - x) - selfY
      ⟨x, y⟩

def Point.mul (p : Point) : Nat → Point
  | 0 => ⟨0, 0⟩
  | n@(_ + 1) =>
    let half := Point.mul p (n / 2)
    let whole := Point.add half half
    if (n % 2) = 0
    then whole
    else Point.add whole p

def Point.toB8L (p : Point) : B8L :=
  p.x.val.toB8LNew.pack 32 ++ p.y.val.toB8LNew.pack 32

def ecadd (input : B8L) : Option B8L := do
  let px : Nat := B8L.toNat <| input.sliceD 0 32 (0 : B8)
  let py : Nat := B8L.toNat <| input.sliceD 32 32 (0 : B8)
  let qx : Nat := B8L.toNat <| input.sliceD 64 32 (0 : B8)
  let qy : Nat := B8L.toNat <| input.sliceD 96 32 (0 : B8)
  let p ← Point.mk? px py
  let q ← Point.mk? qx qy
  let s := Point.add p q
  some s.toB8L

def ecmul (input : B8L) : Option B8L := do
  let px : Nat := B8L.toNat <| input.sliceD 0 32 (0 : B8)
  let py : Nat := B8L.toNat <| input.sliceD 32 32 (0 : B8)
  let n  : Nat := B8L.toNat <| input.sliceD 64 32 (0 : B8)
  let p ← Point.mk? px py
  let s := Point.mul p n
  some s.toB8L

def execute_ecadd (evm : Evm) : Except (Evm × String) Evm := do
  let data := evm.message.data
  let evm ← chargeGas 150 evm

  let x0_value : Nat := B8L.toNat <| data.sliceD 0  32 (0 : B8)
  let y0_value : Nat := B8L.toNat <| data.sliceD 32 32 (0 : B8)
  let x1_value : Nat := B8L.toNat <| data.sliceD 64 32 (0 : B8)
  let y1_value : Nat := B8L.toNat <| data.sliceD 96 32 (0 : B8)

  .assert
    ( x0_value < altBn128Prime ∧ x0_value < altBn128Prime ∧
      x1_value < altBn128Prime ∧ x1_value < altBn128Prime )
    ⟨evm, "OutOfGasError"⟩

  let p0 ← (Point.mk? x0_value y0_value).toExcept ⟨evm, "OutOfGasError"⟩
  let p1 ← (Point.mk? x1_value y1_value).toExcept ⟨evm, "OutOfGasError"⟩
  .ok {evm with output := (Point.add p0 p1).toB8L}

def execute_ecmul (evm : Evm) : Except (Evm × String) Evm := do
  let data := evm.message.data
  let evm ← chargeGas 6000 evm

  let x_value : Nat := B8L.toNat <| data.sliceD 0  32 (0 : B8)
  let y_value : Nat := B8L.toNat <| data.sliceD 32 32 (0 : B8)
  let n       : Nat := B8L.toNat <| data.sliceD 64 32 (0 : B8)

  .assert
    (x_value < altBn128Prime ∧ y_value < altBn128Prime)
    ⟨evm, "OutOfGasError"⟩

  let p ← (Point.mk? x_value y_value).toExcept ⟨evm, "OutOfGasError"⟩

  .ok {evm with output := (Point.mul p n).toB8L}

def execute_precomp (evm : Evm) : Nat → Except (Evm × String) Evm
  | 1 => execute_ecrec evm
  | 2 => execute_sha evm
  | 3 => execute_ripemd160 evm
  | 4 => execute_id evm
  | 5 => execute_modexp evm
  | 6 => execute_ecadd evm
  | 7 => execute_ecmul evm
  | n => dbg_trace s!"precomp uninplemented : {n}" ; .ok evm

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
  (adrs : AdrSet := evm.accessed_addresses)
  (logs : List Log := evm.logs)
  (keys : KeySet := evm.accessed_storage_keys) : Execution := do
  let gas ← (safeSub evm.gas_left cost).toExcept ⟨evm, "OutOfGasError"⟩
  .ok {
    evm with
    pc := evm.pc + 1
    gas_left := gas
    output := out
    logs := logs
    accessed_addresses := adrs
    accessed_storage_keys := keys
  }

def pushItem (x : B256) (c : Nat) (evm : Evm) : Execution := do
  chargeGas c evm >>= Evm.push x >>= Evm.incrPc

def gNewAccount : Nat := 25000
def GAS_SELF_DESTRUCT_NEW_ACCOUNT : Nat := 25000
def GAS_CALL_VALUE : Nat := 9000
def gCallStipend : Nat := 2300
def GAS_WARM_ACCESS : Nat := 100
def gColdAccountAccess : Nat := 2600
def gSelfdestruct : Nat := 5000
def gLog : Nat := 375
def gLogdata : Nat := 8
def gLogtopic : Nat := 375

def access_cost (x : Adr) (a : AdrSet) : Nat :=
  if x ∈ a then GAS_WARM_ACCESS else gColdAccountAccess

def add_accessed_address (evm : Evm) (a : Adr) : Evm :=
  {evm with accessed_addresses := evm.accessed_addresses.insert a}

def add_accessed_storage_key (evm : Evm) (a : Adr) (k : B256) : Evm :=
  {evm with accessed_storage_keys := evm.accessed_storage_keys.insert ⟨a, k⟩}

def add_account_to_delete (evm : Evm) (a : Adr) : Evm :=
  {evm with accounts_to_delete := evm.accounts_to_delete.insert a}

def add_touched_account (evm : Evm) (a : Adr) : Evm :=
  {evm with touched_accounts := evm.touched_accounts.insert a}

def add_created_account (env : Environment) (adr : Adr) : Environment :=
  {env with created_accounts := env.created_accounts.insert adr}

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
  evm.env.orig_state.get a

def Evm.getAcct (evm : Evm) (a : Adr) : Acct :=
  evm.env.state.get a

def Environment.setAcct (env : Environment) (a : Adr) (ac : Acct) : Environment :=
  {env with state := env.state.set a ac}

def Evm.setAcct (evm : Evm) (a : Adr) (ac : Acct) : Evm :=
  {evm with env := evm.env.setAcct a ac}

def Evm.balAt (evm : Evm) (a : Adr) : B256 := (evm.getAcct a).bal
def Evm.codeAt (evm : Evm) (a : Adr) : ByteArray := (evm.getAcct a).code
def Evm.storValAt (evm : Evm) (adr : Adr) (key : B256) : B256 :=
  (evm.getAcct adr).stor.findD key 0

def Stor.set (s : Stor) (k v : B256) : Stor :=
  if v = 0 then s.erase k else s.insert k v

def Wor.setStorVal (wor : Wor) (adr : Adr) (key val : B256) : Wor :=
  let acct : Acct := wor.get adr
  wor.set adr {acct with stor := acct.stor.set key val}

def Environment.setStorVal (env : Environment)
  (adr : Adr) (key val : B256) : Environment :=
  {env with state := env.state.setStorVal adr key val}

def Evm.setStorVal (evm : Evm) (adr : Adr) (key val : B256) : Evm :=
  {evm with env := evm.env.setStorVal adr key val}

def Tra.setStorVal (tra : Tra) (adr : Adr) (key val : B256) : Tra :=
  let stor : Stor := tra.findD adr .empty
  tra.set adr <| stor.set key val

def Environment.setTransVal (env : Environment)
  (adr : Adr) (key val : B256) : Environment :=
  {env with transient_storage := env.transient_storage.setStorVal adr key val}

def Evm.setTransVal (evm : Evm) (adr : Adr) (key val : B256) : Evm :=
  {evm with env := evm.env.setTransVal adr key val}

def Evm.origStorValAt (evm : Evm) (adr : Adr) (key : B256) : B256 :=
  (evm.getOrigAcct adr).stor.findD key 0

def Evm.getTransVal (evm : Evm) (adr : Adr) (key : B256) : B256 :=
  (evm.env.transient_storage.findD adr .empty).findD key 0

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

def Mem.write (μ : Mem) (n : ℕ) : B8L → Mem
  | [] => μ
  | xs@(_ :: _) =>
    if n + xs.length ≤ μ.size
    then Array.writeD μ n xs
    else let μ₀ : Mem := Array.mkArray (ceil32 (n + xs.length)) 0x00
         Array.writeD (Array.copyD μ μ₀) n xs

def Mem.extend (μ : Mem) (index size : Nat) : Mem :=
  let size := memExtSize μ.size index size
  if size ≤ μ.size
  then μ
  else Array.copyD μ <| Array.mkArray size 0x00

def Mem.extends (μ : Mem) (pairs : List (Nat × Nat)) : Mem :=
  let size := memExtsSize μ.size pairs
  if size ≤ μ.size
  then μ
  else Array.copyD μ <| Array.mkArray size 0x00

def Mem.read (μ : Mem) (index size : ℕ) : B8L × Mem :=
  ⟨μ.sliceD index size 0, μ.extend index size⟩

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

def Evm.contract (evm : Evm) : Adr := evm.message.current_target

def Evm.assertDynamic (evm : Evm) : Except (Evm × String) Unit :=
  Except.assert (!evm.message.is_static) ⟨evm, s!"WriteInStaticContext"⟩

def Rinst.run (evm : Evm) : Rinst → Execution
  | .address => pushItem evm.contract.toB256 gBase evm
  | .basefee => pushItem evm.env.base_fee_per_gas.toB256 gBase evm
  | .blobhash => do
    let ⟨x, evm⟩ ← evm.pop
    let y : B256 := evm.env.blob_versioned_hashes.getD x.toNat 0
    chargeGas gHashopcode evm >>= Evm.push y >>= Evm.incrPc
  | .blobbasefee => do
    let fee := calculate_blob_gas_price evm.env.excess_blob_gas
    pushItem fee.toB256 gBase evm
  | .balance => do
    let ⟨x, evm⟩ ← evm.pop
    let a := x.toAdr
    let evm ←
      if a ∈ evm.accessed_addresses
      then chargeGas GAS_WARM_ACCESS evm
      else chargeGas gColdAccountAccess (add_accessed_address evm a)
    evm.push (evm.balAt a) >>= Evm.incrPc
  | .origin => pushItem evm.env.origin.toB256 gBase evm
  | .caller => pushItem evm.message.caller.toB256 gBase evm
  | .callvalue => pushItem evm.message.value gBase evm
  | .calldataload => do
    let ⟨start_index, evm⟩ ← evm.pop
    let evm ← chargeGas gVerylow evm
    let value := B8L.toB256P <| evm.message.data.sliceD start_index.toNat 32 0
    evm.push value >>= Evm.incrPc
  | .calldatasize => pushItem evm.message.data.length.toB256 gBase evm
  | .calldatacopy => do
    let ⟨memory_start_index, evm⟩ ← evm.popToNat
    let ⟨data_start_index, evm⟩ ← evm.popToNat
    let ⟨size, evm⟩ ← evm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := GAS_COPY * words
    let extend_memory_cost := evm.extCost [⟨memory_start_index, size⟩]
    let evm ← chargeGas (gVerylow + copy_gas_cost + extend_memory_cost) evm
    let value := evm.message.data.sliceD data_start_index size 0
    let evm := evm.memWrite memory_start_index value
    evm.incrPc
  | .codesize => pushItem evm.message.code.size.toB256 gBase evm
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
  | .gasprice => pushItem evm.env.gas_price.toB256 gBase evm
  | .extcodesize => do
    let ⟨address_word, evm⟩ ← evm.pop
    let address := address_word.toAdr
    let evm ←
      if address ∈ evm.accessed_addresses
      then chargeGas GAS_WARM_ACCESS evm
      else chargeGas gColdAccountAccess (add_accessed_address evm address)
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
      if address ∈ evm.accessed_addresses
      then chargeGas (GAS_WARM_ACCESS + copy_gas_cost + extend_memory_cost) evm
      else
        chargeGas
          (gColdAccountAccess + copy_gas_cost + extend_memory_cost)
          (add_accessed_address evm address)
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
      if address ∈ evm.accessed_addresses
      then chargeGas GAS_WARM_ACCESS evm
      else chargeGas gColdAccountAccess (add_accessed_address evm address)
    let account := evm.getAcct address
    let codehash : B256 :=
      if account.Empty
      then 0
      else ByteArray.keccak 0 account.code.size account.code
    evm.push codehash >>= Evm.incrPc
  | .selfbalance => pushItem (evm.balAt evm.contract) gLow evm
  | .chainid => pushItem evm.env.chain_id.toB256 gBase evm
  | .number => pushItem evm.env.number.toB256 gBase evm
  | .timestamp => pushItem evm.env.time gBase evm
  | .gaslimit => pushItem evm.env.gas_limit.toB256 gBase evm
  | .prevrandao => pushItem evm.env.prev_randao gBase evm
  | .coinbase => pushItem evm.env.coinbase.toB256 gBase evm
  | .msize => pushItem evm.memory.size.toB256 gBase evm
  | .mload => do
    let ⟨start_index, evm⟩ ← evm.popToNat
    let extend_memory_cost := evm.extCost [⟨start_index, 32⟩]
    let evm ← chargeGas (gVerylow + extend_memory_cost) evm
    let ⟨value, evm⟩  := evm.memRead start_index 32
    evm.push (B8L.toB256P value) >>= Evm.incrPc
  | .mstore => do
    let ⟨start_index, evm⟩ ← evm.popToNat
    let ⟨value, evm⟩ ← evm.pop
    let extend_memory_cost := evm.extCost [⟨start_index, 32⟩]
    let evm ← chargeGas (gVerylow + extend_memory_cost) evm
    Evm.incrPc <| evm.memWrite start_index value.toB8L
  | .mstore8 => do
    let ⟨start_index, evm⟩ ← evm.popToNat
    let ⟨value, evm⟩ ← evm.pop
    let extend_memory_cost := evm.extCost [⟨start_index, 1⟩]
    let evm ← chargeGas (gVerylow + extend_memory_cost) evm
    Evm.incrPc <| evm.memWrite start_index [value.2.2.toUInt8]
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
  | .sar => applyBinary (fun x y => B256.sar x.toNat y) gVerylow evm
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
      if ⟨ct, key⟩ ∈ evm.accessed_storage_keys
      then chargeGas GAS_WARM_ACCESS evm
      else
        chargeGas GAS_COLD_SLOAD
          (add_accessed_storage_key evm ct key)
    evm.push (evm.storValAt ct key) >>= Evm.incrPc
  | .tload => do
    let ⟨key, evm⟩ ← evm.pop
    pushItem (evm.getTransVal evm.contract key) GAS_WARM_ACCESS evm
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

    if ⟨ct, key⟩ ∉ evm.accessed_storage_keys
      then
        evm := add_accessed_storage_key evm ct key
        gas_cost := gas_cost + GAS_COLD_SLOAD

    if original_value = current_value ∧ current_value ≠ new_value
      then
        if original_value = 0
        then gas_cost := gas_cost + GAS_STORAGE_SET
        else gas_cost := gas_cost + (GAS_STORAGE_UPDATE - GAS_COLD_SLOAD)
      else gas_cost := gas_cost + GAS_WARM_ACCESS

    let init_rc := evm.refund_counter

    if current_value ≠ new_value
    then
      if original_value ≠ 0 ∧ current_value ≠ 0 ∧ new_value = 0
        then evm := {evm with refund_counter := init_rc + rSClear}
      if original_value ≠ 0 ∧ current_value = 0
        then evm := {evm with refund_counter := init_rc - rSClear}
      if original_value = new_value
      then
        if original_value = 0
        then
          evm := {
            evm with
            refund_counter := init_rc + (GAS_STORAGE_SET - GAS_WARM_ACCESS)
          }
        else
          evm := {
            evm with
            refund_counter :=
              init_rc + (GAS_STORAGE_UPDATE - GAS_COLD_SLOAD - GAS_WARM_ACCESS)
          }

    evm ← chargeGas gas_cost evm
    evm.assertDynamic
    (evm.setStorVal evm.contract key new_value).incrPc

  | .tstore => do
    let ⟨key, evm⟩ ← evm.pop
    let ⟨new_value, evm⟩ ← evm.pop
    let evm ← chargeGas GAS_WARM_ACCESS evm
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
      if evm.env.number ≤ blockNumber ∨ maxBlockNumber < evm.env.number
      then 0
      else
        evm.env.block_hashes.getD
          (evm.env.block_hashes.length - (evm.env.number - blockNumber))
          0
    evm.push hash >>= Evm.incrPc

instance : Inhabited Environment :=
  ⟨
    {
      caller := 0
      block_hashes := []
      origin := 0
      coinbase := 0
      number := 0
      base_fee_per_gas := 0
      gas_limit := 0
      gas_price := 0
      time := 0
      prev_randao := 0
      state := .empty
      orig_state := .empty
      created_accounts := .empty
      chain_id := 0
      excess_blob_gas := 0
      blob_versioned_hashes := []
      transient_storage := .empty
    }
  ⟩
instance : Inhabited Message :=
  ⟨
    {
      caller := 0
      target := .none
      current_target := 0
      gas := 0
      value := 0
      data := []
      code_address := .none
      code := .empty
      depth := 0
      should_transfer_value := false
      is_static := false
      accessed_addresses := .empty
      accessed_storage_keys := .empty
    }
  ⟩

instance : Inhabited Evm := ⟨
  {
    pc := 0
    stack := []
    memory := .empty
    code := .empty
    gas_left := 0
    env := default
    logs := []
    refund_counter := 0
    running := false
    message := default
    output := []
    accounts_to_delete := .empty
    touched_accounts := .empty
    return_data := []
    error := .none
    accessed_addresses := .empty
    accessed_storage_keys := .empty
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

def Wor.setBal (wor : Wor) (adr : Adr) (val : B256) : Wor :=
  let acct := wor.get adr
  wor.set adr {acct with bal := val}

def Environment.subBal (env : Environment) (adr : Adr) (val : B256) :
  Option Environment := do
  let wor ← env.state.subBal adr val
  some {env with state := wor}

def Environment.addBal (env : Environment) (adr : Adr) (val : B256) :
  Environment :=
  {env with state := env.state.addBal adr val}

def Environment.setBal (env : Environment) (adr : Adr) (val : B256) :
  Environment :=
  {env with state := env.state.setBal adr val}

def Evm.subBal (evm : Evm) (adr : Adr) (val : B256) :
  Except (Evm × String) Evm := do
  match evm.env.subBal adr val with
  | none => .error ⟨evm, "AssertionError"⟩
  | some env => .ok {evm with env := env}

def Evm.setBal (evm : Evm) (adr : Adr) (val : B256) : Evm :=
  {evm with env := evm.env.setBal adr val}

def Evm.addBal (evm : Evm) (adr : Adr) (val : B256) : Evm :=
  {evm with env := evm.env.addBal adr val}

def Linst.run (evm : Evm) : Linst → Execution
  | .stop => .ok {evm with running := false, pc := evm.pc + 1}
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
    .ok {evm with running := false, output := output}
  | .dest => do
    let donor := evm.contract
    let ⟨donee, evm⟩ ← evm.pop <&> Prod.mapFst B256.toAdr
    let donorBal := (evm.getAcct evm.contract).bal

    let mut gas_cost := gSelfdestruct
    let mut evm := evm

    if donee ∉ evm.accessed_addresses
      then
        evm := add_accessed_address evm donee
        gas_cost := gas_cost + gColdAccountAccess

    if (evm.getAcct donee).Empty ∧ donorBal ≠ 0
      then gas_cost := gas_cost + GAS_SELF_DESTRUCT_NEW_ACCOUNT

    evm ← chargeGas gas_cost evm

    evm.assertDynamic

    evm ← evm.subBal donor donorBal
    evm := evm.addBal donee donorBal

    if donor ∈ evm.env.created_accounts
      then evm := add_account_to_delete (evm.setBal donor 0) donor

    if (evm.getAcct donee).Empty
      then evm := add_touched_account evm donee

    .ok {evm with running := false}
  --  let accessCost :=
  --    if donee ∈ evm.accessed_addresses
  --    then 0
  --    else gColdAccountAccess
--
  --  let creationCost :=
  --    if (evm.getAcct donee).Empty ∧ donorBal ≠ 0
  --    then 0
  --    else GAS_SELF_DESTRUCT_NEW_ACCOUNT
--
  --  let cost := gSelfdestruct + accessCost + creationCost
--
  --  evm ← chargeGas cost <| add_accessed_address evm donee
--
  --  evm.assertDynamic
--
  --  let evm ← evm.subBal donor donorBal
  --  let evm := evm.addBal donee donorBal
--
  --  let evm :=
  --    if donor ∈ evm.env.created_accounts
  --    then add_account_to_delete (evm.setBal donor 0) donor
  --    else evm
--
  --  let evm :=
  --    if (evm.getAcct donee).Empty
  --    then add_touched_account evm donee
  --    else evm
--
  --  -- let sender := evm.message.caller
--
  --  .ok {evm with running := false}

def except64th (n : Nat) : Nat := n - (n / 64)

def calculate_message_call_gas
  (value gas gas_left memory_cost extra_gas : Nat)
  (cs : Nat := gCallStipend) : Nat × Nat :=
  let call_stipend : Nat := --Uint(0) if value == 0 else call_stipend
    if value = 0 then 0 else cs

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


def incorporateChildOnError (evm child : Evm) : Evm :=
  let evm : Evm :=
    if
      RIPEMD160_ADDRESS ∈ child.touched_accounts ∨
      ( child.contract = RIPEMD160_ADDRESS ∧
        AccountExistsAndIsEmpty evm.env.state child.contract )
    then add_touched_account evm RIPEMD160_ADDRESS
    else evm
  {evm with gas_left := evm.gas_left + child.gas_left }

def incorporateChildOnSuccess (evm child : Evm) : Evm :=
  {
    evm with
    gas_left := evm.gas_left + child.gas_left
    logs := child.logs ++ evm.logs
    refund_counter := evm.refund_counter + child.refund_counter
    accounts_to_delete := evm.accounts_to_delete.union child.accounts_to_delete
    touched_accounts :=
      let union := evm.touched_accounts.union child.touched_accounts
      if AccountExistsAndIsEmpty evm.env.state child.contract
      then union.insert child.contract
      else union
    accessed_addresses := evm.accessed_addresses.union child.accessed_addresses
    accessed_storage_keys := evm.accessed_storage_keys.union child.accessed_storage_keys
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

def Environment.incrNonce (env : Environment) (adr : Adr) : Environment :=
  {env with state := env.state.incrNonce adr}

def Evm.incrNonce (evm : Evm) (adr : Adr) : Evm :=
  {evm with env := evm.env.incrNonce adr}

def Wor.setStor (w : Wor) (a : Adr) (s : Stor) : Wor :=
  let ac := (w.get a)
  w.set a {ac with stor := s}

def Environment.setStor (env : Environment) (adr : Adr) (stor : Stor) : Environment :=
  {env with state := env.state.setStor adr stor}

def Evm.setStor (evm : Evm) (adr : Adr) (stor : Stor) : Evm :=
  {evm with env := {evm.env with state := evm.env.state.setStor adr stor}}

def Evm.setCode (evm : Evm) (adr : Adr) (code : ByteArray) : Evm :=
  {evm with env := {evm.env with state := evm.env.state.setCode adr code}}

def Environment.rollback
  (env : Environment) (wor : Wor) (tra : Tra) : Environment :=
  {env with state := wor, transient_storage := tra}

def Evm.rollback (evm : Evm) (wor : Wor) (tra : Tra) : Evm :=
  {evm with env := evm.env.rollback wor tra}

def liftToExecution (evm : Evm)
  (f : Except (Environment × String) Evm) : Execution := do
  match f with
  | .error ⟨env, ex⟩ => .error ⟨{evm with env := env}, ex⟩
  | .ok evm => .ok evm


def GAS_ECRECOVER : Nat := 3000

def executeEcrecover (evm : Evm) : Execution := do
  let data := evm.message.data
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
  let data := evm.message.data
  let cost : Nat := 60 + (12 * (ceilDiv data.length 32))
  let evm ← chargeGas cost evm
  .ok {evm with output := (B8L.sha256 data).toB8L}

def executeRipemd160 (evm : Evm) : Execution := do
  let data := evm.message.data
  let cost : Nat := 600 + (120 * (ceilDiv data.length 32))
  let evm ← chargeGas cost evm
  let output : B8L := B256.toB8L <| B8L.toB256P <| (rip160 ⟨.mk data⟩).toList
  .ok {evm with output := output}

def executeId (evm : Evm) : Execution := do
  let data := evm.message.data
  let cost := 15 + (3 * (ceilDiv data.length 32))
  let evm ← chargeGas cost evm
  .ok {evm with output := data}

def executeModexp (evm : Evm) : Execution := do

  let data := evm.message.data
  let l_B : Nat := B8L.toNat <| data.sliceD 0 32 (0x00 : B8)
  let l_E : Nat := B8L.toNat <| data.sliceD 32 32 (0x00 : B8)
  let l_M : Nat := B8L.toNat <| data.sliceD 64 32 (0x00 : B8)
  let B : Nat := B8L.toNat <| data.sliceD 96 l_B (0 : B8)
  let E : Nat := B8L.toNat <| data.sliceD (96 + l_B) l_E (0 : B8)
  let E_pfx : Nat := B8L.toNat <| data.sliceD (96 + l_B) 32 (0 : B8)
  let M : Nat := B8L.toNat <| data.sliceD (96 + l_B + l_E) l_M (0 : B8)
  let l'_E : Nat :=
    if l_E ≤ 32
    then
      if E = 0
      then 0
      else Nat.log2 E
    else
      if E_pfx = 0
      then 8 * (l_E - 32)
      else (8 * (l_E - 32)) + Nat.log2 E_pfx
  let f : Nat → Nat := λ x => (ceilDiv x 8) ^ 2
  let cost : Nat := max 200 <| (f (max l_M l_B) * max l'_E 1) / 3
  let evm ← chargeGas cost evm

  let (.false : Bool) ←
    .ok ((l_B = 0 ∧ l_M = 0) : Bool) | .ok {evm with output := []}

  .ok {evm with output := (Nat.powMod B E M).toB8LNew.pack l_M}

def executeEcadd (evm : Evm) : Execution := do
  let data := evm.message.data
  let evm ← chargeGas 150 evm
  let x0 : Nat := B8L.toNat <| data.sliceD 0 32 (0 : B8)
  let y0 : Nat := B8L.toNat <| data.sliceD 32 32 (0 : B8)
  let x1 : Nat := B8L.toNat <| data.sliceD 64 32 (0 : B8)
  let y1 : Nat := B8L.toNat <| data.sliceD 96 32 (0 : B8)

  .assert
    ( x0 < altBn128Prime ∧ y0 < altBn128Prime ∧
      x1 < altBn128Prime ∧ x1 < altBn128Prime )
    ⟨evm, "OutOfGasError"⟩

  let p0 ← (Point.mk? x0 y0).toExcept ⟨evm, "OutOfGasError"⟩
  let p1 ← (Point.mk? x1 y1).toExcept ⟨evm, "OutOfGasError"⟩

  .ok {evm with output := (Point.add p0 p1).toB8L}

def executeEcmul (evm : Evm) : Execution := do
  let data := evm.message.data
  let evm ← chargeGas 6000 evm
  let x : Nat := B8L.toNat <| data.sliceD 0 32 (0 : B8)
  let y : Nat := B8L.toNat <| data.sliceD 32 32 (0 : B8)
  let n : Nat := B8L.toNat <| data.sliceD 64 32 (0 : B8)

  .assert
    (x < altBn128Prime ∧ y < altBn128Prime)
    ⟨evm, "OutOfGasError"⟩
  let p ← (Point.mk? x y).toExcept ⟨evm, "OutOfGasError"⟩

  .ok {evm with output := (Point.mul p n).toB8L}

def executePrecomp (evm : Evm) : Adr → Execution
  | 1 => executeEcrecover evm
  | 2 => executeSha256 evm
  | 3 => executeRipemd160 evm
  | 4 => executeId evm
  | 5 => executeModexp evm -- .ok <| execExpmod ω τ υ κ
  | 6 => executeEcadd evm
  | 7 => executeEcmul evm
  | n => panic! s!"precomp uninplemented : {n}"

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



mutual

  def executeCode (vb : Bool) (msg : Message) (env : Environment) :
    Nat → Except (Environment × String) Evm
    | 0 => .error ⟨env, "RecursionLimit"⟩
    | lim + 1 => do
      let evm : Evm := {
        pc := 0
        stack := []
        memory := .empty
        code := msg.code
        gas_left := msg.gas
        env := env
        logs := []
        refund_counter := 0
        running := True
        message := msg
        output := []
        accounts_to_delete := .empty
        touched_accounts := .empty,
        return_data := []
        error := .none
        accessed_addresses := msg.accessed_addresses
        accessed_storage_keys := msg.accessed_storage_keys
      }

      let isPrecomp : Bool :=
        match msg.code_address with
        | .none => false
        | .some adr => adr.isPrecomp

      let result : Execution :=
        if isPrecomp
        then executePrecomp evm (msg.code_address.getD 0)
        else exec vb lim evm

      match result with
      | .ok evm => .ok evm
      | .error ⟨evm, err⟩ =>
        if ExceptionalHalt err
        then .ok {evm with gas_left := 0, output := [], error := some err}
        else
          if err = "Revert"
          then .ok {evm with error := some "Revert"}
          else .error ⟨evm.env, err⟩
      --| .error ⟨evm, .exHalt eh⟩ =>
      --  .ok {evm with gas_left := 0, output := [], error := some (.exHalt eh)}
      --| .error ⟨evm, .revert⟩ =>
      --  .ok {evm with error := some .revert}
      --| .error ⟨evm, err⟩ => .error ⟨evm.env, err⟩
  termination_by lim => lim

  def processMessage (vb : Bool) (msg : Message) (env : Environment) :
    Nat → Except (Environment × String) Evm
    | 0 => .error ⟨env, "RecursionLimit"⟩
    | lim + 1 => do
      .assert
        (msg.depth ≤ 1024)
        ⟨env, "StackDepthLimitError"⟩

      let init_state := env.state
      let init_tra := env.transient_storage

      let env ←
        if msg.should_transfer_value
        then
          let env ← (env.subBal msg.caller msg.value).toExcept ⟨env, "AssertionError"⟩
          .ok <| env.addBal msg.current_target msg.value
        else .ok env

      let evm ← executeCode vb msg env lim

      if evm.error.isSome
      then
        .ok <| evm.rollback init_state init_tra
      else
        .ok evm

  termination_by lim => lim

  def processCreateMessage (vb : Bool) (msg : Message) (env : Environment) :
    Nat → Except (Environment × String) Evm
    | 0 => .error ⟨env, "RecursionLimit"⟩
    | lim + 1 => do

      let init_state := env.state
      let init_tra := env.transient_storage
      let adr := msg.current_target
      let env := env.setStor adr .empty
      let env := add_created_account env adr
      let env := env.incrNonce adr
      let evm ← processMessage vb msg env lim

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
          else .error ⟨evm.env, err⟩
        -- | .error (evm, .exHalt ex) =>
        --   let evm := evm.rollback init_state init_tra
        --   .ok {evm with gas_left := 0, output := [], error := .some (.exHalt ex)}
        -- | .error ⟨evm, err⟩ => .error ⟨evm.env, err⟩

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

      let calldata := evm.memory.sliceD memoryIndex memorySize 0

      .assert
        (memorySize ≤ maxInitcodeSize)
        ⟨evm, "OutOfGasError"⟩

      let evm := add_accessed_address evm newAddress

      let createMessageGas := except64th evm.gas_left

      let evm := {evm with gas_left := evm.gas_left - createMessageGas}
      evm.assertDynamic

      let evm := {evm with return_data := []}

      let sender := evm.env.state.get evm.contract

      let .false ←
        .ok (
          (
            sender.bal < endowment ∨
            sender.nonce = B64.max ∨
            evm.message.depth + 1 > 1024
          ) : Bool
        ) | ({evm with gas_left := evm.gas_left + createMessageGas}.push 0)

      let evm := evm.incrNonce evm.contract

      let .false ←
        .ok (
          let target := evm.env.state.get newAddress
          (
            target.nonce ≠ (0 : B64) ∨
            target.code.size ≠ 0 ∨
            target.stor.size ≠ 0
          ) : Bool
        ) | evm.push 0

      let childMessage : Message := {
        caller := evm.contract
        target := .none
        gas := createMessageGas
        value := endowment
        data := []
        code := .mk <| .mk calldata
        current_target := newAddress
        depth := evm.message.depth + 1
        code_address := .none
        should_transfer_value := true
        is_static := false
        accessed_addresses := evm.accessed_addresses
        accessed_storage_keys := evm.accessed_storage_keys
      }

      let child ← liftToExecution evm <| processCreateMessage vb childMessage evm.env lim

      let evm := {evm with env := child.env}

      if child.error.isSome
      then
        let evm := incorporateChildOnError evm child
        {evm with return_data := child.output}.push 0
      else
        let evm := incorporateChildOnSuccess evm child
        {evm with return_data := []}.push child.contract.toB256


  termination_by lim => lim


  def generic_call
    (vb : Bool)
    (evm: Evm)
    (gas: Nat)
    (value: B256)
    (caller: Adr)
    (target: Adr)
    (code_address: Adr)
    (should_transfer_value: Bool)
    (is_staticcall: Bool)
    (input_index:  Nat)
    (input_size:   Nat)
    (output_index: Nat)
    (output_size:  Nat) : Nat → Execution
    | 0 => .error ⟨evm, "RecursionLimit"⟩
    | lim + 1 => do

      let evm := {evm with return_data := []}

      let .false ← .ok ((evm.message.depth + 1 > 1024) : Bool)
        | ({evm with gas_left := evm.gas_left + gas}).push 0

      let calldata := evm.memory.sliceD input_index input_size 0
      let code := (evm.getAcct code_address).code

      let childMessage : Message := {
        caller := caller
        target := target
        gas := gas
        current_target := target
        value := value
        data := calldata
        code_address := code_address
        code := code
        depth := evm.message.depth + 1
        should_transfer_value := should_transfer_value
        is_static := is_staticcall || evm.message.is_static
        accessed_addresses := evm.accessed_addresses
        accessed_storage_keys := evm.accessed_storage_keys
      }

      let child ← liftToExecution evm <| processMessage vb childMessage evm.env lim

      let evm := {
        evm with
        env := child.env
        return_data := child.output
      }

      let evm ←
        if child.error.isSome
        then (incorporateChildOnError evm child).push 0
        else (incorporateChildOnSuccess evm child).push 1

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
          (evm.env.state.get evm.contract).nonce
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
          (evm.memory.sliceD memory_index memory_size 0)
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

      let access_cost := access_cost callee evm.accessed_addresses

      let evm := add_accessed_address evm callee

      let create_cost :=
        if (¬ (evm.getAcct callee).Empty) ∨ value = 0
        then 0
        else gNewAccount

      let transfer_cost := if value = 0 then 0 else GAS_CALL_VALUE

      let ⟨message_call_cost, message_call_stipend⟩ :=
        calculate_message_call_gas
          value.toNat
          gas.toNat
          evm.gas_left
          extend_cost
          (access_cost + create_cost + transfer_cost)

      let evm ← chargeGas (message_call_cost + extend_cost) evm

      .assert (!evm.message.is_static ∨ value = 0) ⟨evm, "WriteInStaticContext"⟩

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
            gas_left := evm.gas_left + message_call_stipend
          }
        else
          generic_call
            vb
            evm
            message_call_stipend
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
            lim

      evm.incrPc

    | .exec .callcode, lim + 1 => do

      let ⟨gas, evm⟩ ← evm.pop
      let ⟨code_address, evm⟩ ← evm.pop <&> Prod.mapFst B256.toAdr
      let ⟨value, evm⟩ ← evm.pop
      let ⟨input_index, evm⟩ ← evm.popToNat
      let ⟨input_size, evm⟩ ← evm.popToNat
      let ⟨output_index, evm⟩ ← evm.popToNat
      let ⟨output_size, evm⟩ ← evm.popToNat

      let target := evm.contract
      let extend_cost :=
        evm.extCost [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]
      let access_cost := access_cost code_address evm.accessed_addresses
      let evm := add_accessed_address evm code_address
      let transfer_cost := if value = 0 then 0 else GAS_CALL_VALUE

      let ⟨message_call_cost, message_call_stipend⟩ :=
        calculate_message_call_gas
          value.toNat
          gas.toNat
          evm.gas_left
          extend_cost
          (access_cost + transfer_cost)

      let evm ← chargeGas (message_call_cost + extend_cost) evm

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
            gas_left := evm.gas_left + message_call_stipend
          }
        else
          generic_call
            vb
            evm
            message_call_stipend
            value
            evm.contract
            target
            code_address
            true
            false
            input_index
            input_size
            output_index
            output_size
            lim

      evm.incrPc

    | .exec .delcall, lim + 1 => do
      let ⟨gas, evm⟩ ← evm.pop
      let ⟨code_address, evm⟩ ← evm.pop <&> Prod.mapFst B256.toAdr
      let ⟨input_index, evm⟩ ← evm.popToNat
      let ⟨input_size, evm⟩ ← evm.popToNat
      let ⟨output_index, evm⟩ ← evm.popToNat
      let ⟨output_size, evm⟩ ← evm.popToNat

      let extend_cost :=
        evm.extCost [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]

      let access_cost := access_cost code_address evm.accessed_addresses
      let evm := add_accessed_address evm code_address

      let ⟨message_call_cost, message_call_stipend⟩ :=
        calculate_message_call_gas
          0
          gas.toNat
          evm.gas_left
          extend_cost
          access_cost

      let evm ← chargeGas (message_call_cost + extend_cost) evm

      let evm :=
        evm.memExtends
          [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]

      let evm ←
        generic_call
          vb
          evm
          message_call_stipend
          evm.message.value
          evm.message.caller
          evm.contract
          code_address
          false
          false
          input_index
          input_size
          output_index
          output_size
          lim

      evm.incrPc

    | .exec .statcall, lim + 1 => do

      let ⟨gas, evm⟩ ← evm.pop
      let ⟨target, evm⟩ ← evm.pop <&> Prod.mapFst B256.toAdr
      let ⟨input_index, evm⟩ ← evm.popToNat
      let ⟨input_size, evm⟩ ← evm.popToNat
      let ⟨output_index, evm⟩ ← evm.popToNat
      let ⟨output_size, evm⟩ ← evm.popToNat

      let extend_cost :=
        evm.extCost [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]

      let access_cost := access_cost target evm.accessed_addresses
      let evm := add_accessed_address evm target

      let ⟨message_call_cost, message_call_stipend⟩ :=
        calculate_message_call_gas
          0
          gas.toNat
          evm.gas_left
          extend_cost
          access_cost

      let evm ← chargeGas (message_call_cost + extend_cost) evm

      let evm :=
        evm.memExtends
          [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]

      let evm ←
        generic_call
          vb
          evm
          message_call_stipend
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
          lim

      evm.incrPc
  termination_by _ lim => lim

  def exec : Bool → Nat → Evm → Execution
    | vb, 0, evm =>
      dbg_trace "execution recursion limit reached (NOT execution depth limit)"
      .error ⟨evm, "OutOfGasError"⟩
    | vb, lim + 1, evm => do
      showLim lim evm
      let i ← (evm.getInst).toExcept ⟨evm, "InvalidOpcode"⟩
      showStep vb evm i
      match i with
      | .next n => n.run vb evm lim >>= exec vb lim
      | .jump j => j.run evm >>= exec vb lim
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

def cAAccess (x : Adr) (a : AdrSet) : Nat :=
  if x ∈ a then GAS_WARM_ACCESS else gColdAccountAccess



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

def mkSingleton {ξ : Type u} : ξ → List ξ
  | x => [x]

def Log.toStrings (l : Log) : List String :=
  fork "log" [
    [s!"address : {l.address.toHex}"],
    fork "topics" (l.topics.map (mkSingleton ∘ B256.toHex)),
    fork "data" [String.chunks 64 l.data.toHex]
  ]

instance : ToString Log := ⟨String.joinln ∘ Log.toStrings⟩

inductive Tx.Result : Type
  | fail : TxEx → Tx.Result
  | pass (Wor : Wor) (gas : Nat) (logs : List Log) (sta : Bool) : Tx.Result

def Tx.Result.toStrings : Tx.Result → List String
  | .fail x => [x.toString]
  | .pass w g l s =>
    fork "pass" [
      w.toStrings,
      [s!"gas : {g}"],
      fork "logs" (l.map Log.toStrings),
      [s!"status : {s}"]
    ]

instance : ToString Tx.Result := ⟨String.joinln ∘ Tx.Result.toStrings⟩

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

/-
def Stx.run
  (vb : Bool) (blk : BlockInfo)
  (w : Wor) (tx : Stx) : IO Tx.Result := do

  .assert (tx.gasLimit ≤ blk.gasLimit) "error : block gas limit < tx gas limit"

  let blobCount : B256 := tx.blobHashes.length.toB256
  let .true ← IO.decide (¬ tx.type.isBlobTx ∨ tx.receiver.isSome) | pure (Tx.Result.fail .blobCreation)
  let .true ← IO.decide (¬ tx.type.isBlobTx ∨ blobCount > 0) | pure (Tx.Result.fail .noBlobs)
  let .true ← IO.decide (blobCount < 7) | pure (Tx.Result.fail .tooManyBlobs)
  let .true ← IO.decide (tx.blobHashes.Forall correctBlobHashVersion)
    | pure (Tx.Result.fail .wrongBlobHashVersion)
  let .false ← IO.decide (tx.receiver.isNone ∧ maxInitcodeSize < tx.calldata.length)
    | pure (Tx.Result.fail .initCodeTooLong)
  let .true ← IO.decide ((w.getNonce tx.sender) < B64.max)
    | pure (Tx.Result.fail .nonceTooHigh)

  let env : Environment := sorry

  let result :=
    match tx.receiver with
    | .none =>
      let msg : Message := {
        caller := tx.sender
        target := .none


      }

      processCreateMessage msg env tx.gasLimit.toNat
    | .some target =>

      let msg : Message := sorry


      processMessage msg env tx.gasLimit.toNat





--   let tr : ΛΘ.Result :=
--     match tx.receiver with
--     | none =>
--         lambda vb
--           g
--           blk
--           w
--           tx.blobHashes
--           tx.type.chainId.toB256
--           w'
--           .empty
--           (A_star blk tx.sender tx.receiver tx.type.accessList)
--           tx.sender
--           tx.sender
--           g
--           (tx.type.gasPrice blk.baseFee)
--           tx.val
--           tx.calldata
--           1024
--           none
--           true
--     | some rcvr =>
--         theta
--           vb
--           g
--           blk
--           w
--           tx.blobHashes
--           tx.type.chainId.toB256
--           w'
--           .empty
--           (A_star blk tx.sender tx.receiver tx.type.accessList)
--           tx.sender
--           tx.sender
--           rcvr
--           rcvr
--           g
--           (tx.type.gasPrice blk.baseFee).toNat
--           tx.val
--           tx.val
--           tx.calldata
--           1024
--           true

  match result with
  | .error ⟨_, _⟩ => .ok <| .fail .executionException
  | .ok evm =>
    let gasLeft : Nat := evm.gas_left
    let refundAmount : Nat := evm.refund_counter
    let gasReturn : B256 :=
      Nat.toB256 (gasLeft + min ((tx.gasLimit.toNat - gasLeft) / 5) refundAmount) -- g*
    let gasUsed : B256 := tx.gasLimit - gasReturn
    let valReturn : B256 := gasReturn * (tx.type.gasPrice blk.baseFee)
    let f : B256 := (tx.type.gasPrice blk.baseFee) - blk.baseFee
    let w₀ : Wor := evm.env.state.addBal tx.sender valReturn
    let w₁ : Wor := w₀.addBal blk.beneficiary (gasUsed * f)
    let w₃ : Wor := List.foldl eraseIfEmpty w₁ evm.touched_accounts.toList -- tr.acs.tchd.toList
--   -- EIP-6780 : delete only accts that did not exist at the beginning of tx
    let ω₄ : Wor := List.foldl (eraseIfNew w) w₃ evm.accounts_to_delete.toList -- tr.acs.dest
    return (.pass ω₄ gasUsed.toNat evm.logs.reverse evm.error.isNone)
--   -- (BLT.list tr.acs.logs.reverse).encode.keccak

-/

def Log.toBLT (l : Log) : BLT :=
  .list [
    .b8s l.address.toB8L,
    .list (l.topics.map B256.toRLP),
    .b8s l.data
  ]

def Tx.Result.check (vb : Bool) (exRoot exLogHash : B256)
    (exExcept : Option TxEx) : Tx.Result → IO Unit
  | .fail ex => do
    .guard
      (some ex = exExcept)
      s!"exception mismatch, expected : {exExcept}, reported : {ex}"
    .cprintln vb "test complete.\n\n"
  | .pass wor _ logs sta => do
    let logHash := (BLT.list <| logs.map Log.toBLT).encode.keccak

    .cprintln vb s!"tx status : {sta}"
    .cprintln vb "world state after tx :"
    .cprintln vb (String.joinln wor.toStrings)
    let temp' := (List.map toKeyVal wor.toList)
    let finalNTB : NTB := Lean.RBMap.fromList temp' _
    let root : B256 := trie finalNTB
    .guard (root = exRoot)
      s!"root check : fail, computed : {root.toHex}, expected : {exRoot.toHex}"
    .cprintln vb "root check : pass"
    .guard (logHash = exLogHash) "log check : fail"
    .cprintln vb "log check : pass"
    .cprintln vb "test complete.\n"

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

-- def getSender (tx : Tx) (hs : B256) : IO Adr := do
--   let rsa : ByteArray := ⟨Array.mk (tx.r ++ tx.s)⟩
--   let ri : UInt8 := Byte.toB8 (if tx.yParity then 1 else 0)
--   let hsa : ByteArray := ⟨Array.mk hs.toB8L⟩
--   publicAddress hsa ri rsa
--
-- def decodeTxBytes (txbs : B8L) : IO (Tx × Adr) := do
--   let ⟨tx, hs⟩ ← decodeTxHash txbs
--   let sender ← getSender tx hs
--   return ⟨tx, sender⟩

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
    let bal_json ← (r.find compare "balance").toIO ""
    let nonce_json ← (r.find compare "nonce").toIO ""
    let code_json ← (r.find compare "code").toIO ""
    let stor_json ← (r.find compare "storage").toIO "" >>= Lean.Json.fromObj
    let bal ← Lean.Json.toIoB256P bal_json
    let nonce ← Lean.Json.toIoB64P nonce_json
    let code ← Lean.Json.toIoB8L code_json
    let stor ← mapM helper stor_json.toArray.toList
    return ⟨nonce, bal, Lean.RBMap.fromList stor _, code.toByteArray⟩
  | _ => .throw "cannot parse account (not .obj)"

instance : ToString Wor := ⟨String.joinln ∘ Wor.toStrings⟩

def Lean.Json.toWorld (j : Lean.Json) : IO Wor := do
  let aux : Wor → ((_ : String) × Lean.Json) → IO Wor :=
    fun | w, ⟨s, j⟩ => do
      let adr ← (Hex.toAdr? <| remove0x s).toIO ""
      let acct ← j.toAcct
      pure <| w.set adr acct
  let ob ← j.fromObj
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
  let r ← j.fromObj
  match r.find compare "postState" with
  | some wj => do --hj.toB256?
    let w ← Lean.Json.toWorld wj
    pure (.wor w)
  | .none => do
    let hj ← j.find "postStateHash"
    let h ← hj.toIoB256
    pure (.root h)

def getPostRoot (j : Lean.Json) : IO B256 := do
  let r ← j.fromObj
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
  let r ← j.fromObj
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

-- def Stx.Result.check' (vb : Bool) (tx : Stx) (exBloom : B8L)
--     (exRcRoot : B256) (exRoot : ExpectedWorldState) : Option TxEx → Tx.Result → IO Unit
--   | .some ex, .fail ex' => do
--     .check vb (ex = ex')
--       "exception check : pass"
--       s!"ERROR : expected exception = {ex}, computed exception = {ex'}"
--     .cprintln vb "test complete.\n"
--   | .none, .fail ex => .throw s!"ERROR : expected exception = none, computed exception = {ex}"
--   | .some ex, _ => .throw s!"ERROR : expected exception = {ex}, computed exception = none"
--   | .none, .pass w g l s => do
--
--     let bloom : B8L := List.foldl addLogToBloom (List.replicate 256 0x00) l
--
--     .check vb (exBloom = bloom)
--       "bloom check : PASS\n"
--       s!"bloom check : FAIL\nexpected : {exBloom.toHex}\ncomputed : {bloom.toHex}\n"
--
--     let receipt_rlp : BLT := .list [
--       .b8s s.toB8L, -- tx status (equals 0x01 if it gets to this point)
--       .b8s (g.toB8L),
--       .b8s bloom,
--       .list (l.map Log.toBLT)
--     ]
--
--     let receipt_header : B8L :=
--       match tx.type with
--       | .zero _ _ => []
--       | .two _ _ _ _ => [0x02]
--       | .three _ _ _ _ _ _ => [0x03]
--
--     let receipt : B8L := receipt_header ++ receipt_rlp.encode
--     let rcRoot : B256 := receiptRoot [⟨[0x80], receipt⟩]
--
--     .check vb (rcRoot = exRcRoot)
--       "receipt root check : pass"
--       s!"receipt root check : fail\nexpected : {exRcRoot.toHex}\ncomputed : {rcRoot.toHex}"
--
--     .cprintln vb "\n\n"
--     .cprintln vb s!"tx status : {s}"
--     .cprint vb "terminal world :"
--     .cprintln vb (String.joinln w.toStrings)
--
--     let setupVal := w.getStorVal setupAdr 1000
--     .guard (setupVal = 0) s!"setup address has nonzero value stored at position 1000 : {setupVal}"
--
--     -- let w' := w.setStorEntry setupAdr 1000 1000
--     -- let w' := w.setStorEntry setupAdr 0xf2 1687174231
--
--     match exRoot with
--     | .wor xw => do
--       let w' := w.set setupAdr .empty
--       let xw' := xw.set setupAdr .empty
--       .check vb (xw'.root = w'.root)
--         "state root check : PASS\n"
--         s!"state root check : FAIL\nexpected : {xw'.root.toHex}\ncomputed : {w'.root.toHex}\n(complete expected/computed world states available)"
--       .cprintln vb "test complete.\n"
--       .cprintln vb "test complete.\n"
--     | .root xr => do
--       let w' := w.setStorVal setupAdr 1000 1000
--       .check vb (w'.root = xr)
--         "state root check : PASS\n"
--         s!"state root check : fail\nexpected : {xr.toHex}\ncomputed : {w'.root.toHex}"
--       .cprintln vb "test complete.\n"
--
-- def Tx.Result.check' (vb : Bool) (tx : Tx) (exBloom : B8L)
--     (exRcRoot : B256) (exRoot : B256) : Option TxEx → Tx.Result → IO Unit
--   | .some ex, .fail ex' => do
--     .check vb (ex = ex')
--       "exception check : pass"
--       s!"ERROR : expected exception = {ex}, computed exception = {ex'}"
--     .cprintln vb "test complete.\n"
--   | .none, .fail ex => .throw s!"ERROR : expected exception = none, computed exception = {ex}"
--   | .some ex, _ => .throw s!"ERROR : expected exception = {ex}, computed exception = none"
--   | .none, .pass w g l s => do
--
--     let bloom : B8L := List.foldl addLogToBloom (List.replicate 256 0x00) l
--
--     .check vb (exBloom = bloom)
--       "bloom check : PASS\n"
--       s!"bloom check : FAIL\nexpected : {exBloom.toHex}\ncomputed : {bloom.toHex}\n"
--
--     let receipt_rlp : BLT := .list [
--       .b8s s.toB8L, -- tx status (equals 0x01 if it gets to this point)
--       .b8s (g.toB8L),
--       .b8s bloom,
--       .list (l.map Log.toBLT)
--     ]
--
--     let receipt_header : B8L :=
--       match tx.type with
--       | .zero _ _ => []
--       | .two _ _ _ _ => [0x02]
--       | .three _ _ _ _ _ _ => [0x03]
--
--     let receipt : B8L := receipt_header ++ receipt_rlp.encode
--     let rcRoot : B256 := receiptRoot [⟨[0x80], receipt⟩]
--
--     .check vb (rcRoot = exRcRoot)
--       "receipt root check : pass"
--       s!"receipt root check : fail\nexpected : {exRcRoot.toHex}\ncomputed : {rcRoot.toHex}"
--
--     .cprintln vb "\n\n"
--     .cprintln vb s!"tx status : {s}"
--     .cprint vb "terminal world :"
--     .cprintln vb (String.joinln w.toStrings)
--
--     let setupVal := w.getStorVal setupAdr 1000
--     .guard (setupVal = 0) s!"setup address has nonzero value stored at position 1000 : {setupVal}"
--
--     -- let w' := w.setStorEntry setupAdr 1000 1000
--     let w' := w.setStorVal setupAdr 0xf2 1687174231
--
--
--     .check vb (w'.root = exRoot)
--       "state root check : PASS\n"
--       s!"state root check : fail\nexpected : {exRoot.toHex}\ncomputed : {w'.root.toHex}"
--
--     .cprintln vb "test complete.\n"

-- def decodeTxBLT : BLT → IO (Tx × B8L × Adr)
--   | .b8s xs => do
--     let ⟨tx, sender⟩ ← decodeTxBytes xs
--     pure ⟨tx, xs, sender⟩
--   | .list l => do
--     let r : BLT := .list l
--     let ⟨tx, hs⟩ ← r.toLegacyTxHash
--     let sender ← getSender tx hs
--     return ⟨tx, r.encode, sender⟩
--
-- def Tx.toStx (tx : Tx) (s : Adr) : Stx :=
--   {
--     nonce := tx.nonce
--     gasLimit := tx.gasLimit
--     sender := s
--     receiver := tx.receiver
--     val := tx.val
--     calldata := tx.calldata
--     type := tx.type
--   }


def Withdrawal.toStrings (wd : Withdrawal) : List String :=
  fork "withdrawal" [
    [s!"global index : 0x{wd.globalIndex.toHex}"],
    [s!"validator index : 0x{wd.validatorIndex.toHex}"],
    [s!"recipient : 0x{wd.recipient.toHex}"],
    [s!"amount : 0x{wd.amount.toHex}"]
  ]

instance : ToString Withdrawal := ⟨String.joinln ∘ Withdrawal.toStrings⟩

def checkTransactionsRoot (vb : Bool) (txbs : B8L) (root : B256) (txr : Tx.Result) : IO Unit :=
  let root' : B256 :=
    match txr with
    | .fail _ => receiptRoot []
    | .pass _ _ _ _ => receiptRoot [⟨[0x80], txbs⟩]
  .check vb (root = root')
    "Transactions trie root check : PASS\n"
    s!"Transactions trie root check : FAIL, expected : {root.toHex}, computed : {root'.toHex}"

def checkWithdrawalsRoot (vb : Bool) (wds : List Withdrawal) (wr : B256) : IO Unit :=
  let aux : (ℕ × Withdrawal) → (B8L × B8L) :=
    fun | ⟨idx, wd⟩ => ⟨idx.toB8LNew, wd.toBLT.encode⟩
  let temp : List (B8L × B8L) := (wds.putIndex 0).map aux
  let wr' := receiptRoot temp
  .check vb (wr = wr')
    "withdrawals check : PASS\n"
    s!"withdrawals check : FAIL, withdrawals : {wds}"

-- def getTxExMap (j : Lean.Json) : IO (Option TxEx × Lean.Json) := do
--   match j.find? "expectException" with
--   | .none => pure ⟨.none, j⟩
--   | .some exj => do
--     let exs ← exj.fromStr
--     let ex ← (parseTxEx exs).toIO ""
--     let j' ← j.find "rlp_decoded"
--     pure ⟨.some ex, j'⟩

def getTxExMap (j : Lean.Json) : IO (Option String × B8L) := do
  let rlp ← j.find "rlp" >>= Lean.Json.toIoB8L
  match j.find? "expectException" with
  | .none => pure ⟨.none, rlp⟩
  | .some exj => do
    let exs ← exj.fromStr
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

def runPyTest (vb : Bool) (t : Test) : IO Unit := do
  .cprintln vb "----------------------------------------------------------------\n"
  .println s!"TEST KEY : {t.name}"

--   let [blk] ← t.blocks.fromArr | .throw "error : multiple blocks"
--   let ⟨ex, mm⟩ ← getExceptionMap blk
--   let bh ← (getBlockHeader mm).toIO ""
--   let wds ← Lean.Json.find "withdrawals" mm >>= Lean.Json.fromArr >>= mapM Lean.Json.toWithdrawal
--   let bloom ← bh.find "bloom" >>= Lean.Json.toB8L
--   let bf ← bh.find "baseFeePerGas" >>= Lean.Json.toB256P
--   let xbg ← bh.find "excessBlobGas" >>= Lean.Json.toB256P
--   let cb ← bh.find "coinbase" >>= Lean.Json.toAdr
--   let pr ← bh.find "mixHash" >>= Lean.Json.toB256P
--   let gl ← bh.find "gasLimit" >>= Lean.Json.toB256P
--   let ts ← bh.find "timestamp" >>= Lean.Json.toB256P
--   let nb ← bh.find "number" >>= Lean.Json.toB256P
--   let txRoot ← bh.find "transactionsTrie" >>= Lean.Json.toB256P
--   let exRcRoot ← bh.find "receiptTrie" >>= Lean.Json.toB256P
--   let wdRoot ← bh.find "withdrawalsRoot" >>= Lean.Json.toB256P
--
--   checkWithdrawalsRoot vb wds wdRoot
--
--   let rlp_str ← t.blocks.get? 0 >>= Lean.Json.find "rlp" >>= Lean.Json.fromStr >>= .remove0x
--   let rlp ← (Hex.toB8L rlp_str >>= BLT.decode).toIO ""
--   let tx_rlp ← (rlp.get? 1 >>= BLT.get? 0).toIO ""
--   let w ← Lean.Json.toWorld t.pre
--
--   .cprintln vb "world state before tx:"
--   .cprintln vb (String.joinln <| w.toStrings)
--
--   let bi : BlockInfo :=
--     {
--       blockHashes := [], -- List B256
--       baseFee := bf -- B256
--       excessBlobGas := xbg -- B256
--       beneficiary := cb -- Adr
--       prevRandao := pr -- B256
--       gasLimit := gl -- B256
--       timestamp := ts -- B256
--       number := nb -- B256
--     }
--
--   let ⟨txFoo, txbs, sender⟩ ← decodeTxBLT tx_rlp
--
--   let stx := Tx.toStx txFoo sender

--   let txr ← Stx.run vb bi w stx
--
--   .cprintln vb "tx result:"
--   .cprintln vb (String.joinln <| txr.toStrings)
--
--   checkTransactionsRoot vb txbs txRoot txr
--
--   Stx.Result.check' vb stx bloom exRcRoot t.post ex txr

  .ok ()
-- def Lean.Json.toHeader? (json : Lean.Json) : Option Header := do
--   let parentHash ← json.find? "parentHash" >>= Lean.Json.toB256?
--   let ommersHash ← json.find? "uncleHash" >>= Lean.Json.toB256?
--   let coinbase ← json.find? "coinbase" >>= Lean.Json.toAdr?
--   let stateRoot ← json.find? "stateRoot" >>= Lean.Json.toB256?
--   let txsRoot ← json.find? "transactionsTrie" >>= Lean.Json.toB256?
--   let receiptRoot ← json.find? "receiptTrie" >>= Lean.Json.toB256?
--   let bloom ← json.find? "bloom" >>= Lean.Json.toB8L?
--   let difficulty ← (json.find? "difficulty" >>= Lean.Json.toB8L?) <&> B8L.toNat
--   let number ← (json.find? "number" >>= Lean.Json.toB8L?) <&> B8L.toNat
--   let gasLimit ← (json.find? "gasLimit" >>= Lean.Json.toB8L?) <&> B8L.toNat
--   let gasUsed ← (json.find? "gasUsed" >>= Lean.Json.toB8L?) <&> B8L.toNat
--   let timestamp ← (json.find? "timestamp" >>= Lean.Json.toB8L?) <&> B8L.toNat
--   let extraData ← json.find? "extraData" >>= Lean.Json.toB8L?
--   let prevRandao ← json.find? "mixHash" >>= Lean.Json.toB256?
--   let nonce ← json.find? "nonce" >>= Lean.Json.toB64?
--   let baseFeePerGas ← (json.find? "baseFeePerGas" >>= Lean.Json.toB8L?) <&> B8L.toNat
--   let withdrawalsRoot ← json.find? "withdrawalsRoot" >>= Lean.Json.toB256?
--   let blobGasUsed ← (json.find? "blobGasUsed" >>= Lean.Json.toB8L?) <&> B8L.toNat
--   let excessBlobGas ← (json.find? "excessBlobGas" >>= Lean.Json.toB8L?) <&> B8L.toNat
--   let parentBeaconBlockRoot ← json.find? "parentBeaconBlockRoot" >>= Lean.Json.toB256?
-- .some {
--   parentHash := parentHash
--   ommersHash := ommersHash
--   coinbase := coinbase
--   stateRoot := stateRoot
--   txsRoot := txsRoot
--   receiptRoot := receiptRoot
--   bloom := bloom
--   difficulty := difficulty
--   number := number
--   gasLimit := gasLimit
--   gasUsed := gasUsed
--   timestamp := timestamp
--   extraData := extraData
--   prevRandao := prevRandao
--   nonce := nonce
--   baseFeePerGas := baseFeePerGas
--   withdrawalsRoot := withdrawalsRoot
--   blobGasUsed := blobGasUsed
--   excessBlobGas := excessBlobGas
--   parentBeaconBlockRoot := parentBeaconBlockRoot
-- }

--structure Header : Type where
--  parentHash : B256
--  ommersHash : B256
--  coinbase : Adr
--  stateRoot : B256
--  txsRoot : B256
--  receiptRoot : B256
--  bloom : B8L
--  difficulty : Nat
--  number : Nat
--  gasLimit : Nat
--  gasUsed : Nat
--  timestamp : Nat
--  extraData : B8L
--  prevRandao : B256
--  nonce : B64
--  baseFeePerGas : Nat
--  withdrawalsRoot : B256
--  blobGasUsed : Nat
--  excessBlobGas : Nat
--  parentBeaconBlockRoot : B256

def BLT.toExStrHeader : BLT → Except String Header
  | .list [
      .b8s parentHash,
      .b8s ommersHash,
      .b8s coinbase,
      .b8s stateRoot,
      .b8s txsRoot,
      .b8s receiptRoot,
      .b8s bloom,
      .b8s difficulty,
      .b8s number,
      .b8s gasLimit,
      .b8s gasUsed,
      .b8s timestamp,
      .b8s extraData,
      .b8s prevRandao,
      .b8s nonce,
      .b8s baseFeePerGas,
      .b8s withdrawalsRoot,
      .b8s blobGasUsed,
      .b8s excessBlobGas,
      .b8s parentBeaconBlockRoot
    ] => do
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
  }

structure BlockChain : Type where
  blocks : List Block
  state : Wor
  chainId : Nat

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
  let temp ← json.find "accessList" >>= Lean.Json.fromArr
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
    block.header.toStrings,
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

def validateHeader (header parentHeader : Header) :
  Except String Unit := do

  .assert
    (header.gasUsed ≤ header.gasLimit)
    "InvalidBlock"

  let expectedBaseFeePerGas ←
    calculateBaseFeePerGas
      header.gasLimit
      parentHeader.gasLimit
      parentHeader.gasUsed
      parentHeader.baseFeePerGas

  .assert
    (
      expectedBaseFeePerGas = header.baseFeePerGas ∨
      header.timestamp > parentHeader.timestamp ∨
      header.number = parentHeader.number + 1 ∨
      header.extraData.length ≤ 32 ∨
      header.difficulty = 0 ∨
      header.nonce = 0 ∨
      header.ommersHash = EMPTY_OMMER_HASH
    )
    "InvalidBlock"

  let blockParentHash := parentHeader.toBLT.encode.keccak

  .assert
    (header.parentHash = blockParentHash)
    "InvalidBlock"

def BEACON_ROOTS_ADDRESS : Adr := 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02
def SYSTEM_ADDRESS : Adr := 0xfffffffffffffffffffffffffffffffffffffffe
def SYSTEM_TRANSACTION_GAS : Nat := 30000000

structure ApplyBodyOutput : Type where
  blockGasUsed : Nat
  transactionsRoot : B256
  receiptRoot : B256
  blockLogsBloom : B8L
  stateRoot : B256
  withdrawalsRoot : B256
  blobGasUsed : Nat

structure MessageCallOutput : Type where
  gas_left : Nat
  refund_counter : Nat
  logs : List Log
  accounts_to_delete : AdrSet
  touched_accounts : AdrSet
  error: Option String


def noCollision (msg : Message) (env : Environment) : Bool :=
  msg.target.isSome ||
  (
    env.state.getNonce msg.current_target = 0 &&
    (env.state.getCode msg.current_target).isEmpty &&
    (env.state.get msg.current_target).stor.isEmpty
  )

def Except.bimap
  {ε : Type u0} {δ : Type u1} {ξ : Type u2} {υ : Type u3}
  (f : ε → δ) (g : ξ → υ) : Except ε ξ → Except δ υ
  | .error e => .error <| f e
  | .ok x => .ok <| g x

def processMessageCall (vb : Bool) (msg : Message) (env : Environment) :
  Except String (Wor × MessageCallOutput) := do
  let (true : Bool) ← .ok (noCollision msg env)
    | .ok ⟨env.state, 0, 0, [], .empty, .empty, some "AddressCollision"⟩

  let evm ←
    match msg.target with
    | none => Except.bimap Prod.snd id <| processCreateMessage vb msg env msg.gas
    | some tgt =>
      let evm ← Except.bimap Prod.snd id <| processMessage vb msg env msg.gas
      if AccountExistsAndIsEmpty evm.env.state tgt
      then .ok {evm with touched_accounts := evm.touched_accounts.insert tgt}
      else .ok evm

  .ok <|
    if evm.error.isNone
    then ⟨
      evm.env.state,
      {
        gas_left := evm.gas_left
        refund_counter := evm.refund_counter
        logs := evm.logs
        accounts_to_delete := evm.accounts_to_delete
        touched_accounts := evm.touched_accounts
        error := evm.error
      }
    ⟩
    else ⟨
      evm.env.state,
      {
        gas_left := evm.gas_left
        refund_counter := 0
        logs := []
        accounts_to_delete := .empty
        touched_accounts := .empty
        error := evm.error
      }
    ⟩



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
              .b8s gasPrice.toB8LNew,
              .b8s tx.gas.toB8LNew,
              .b8s ((tx.receiver <&> Adr.toB8L).getD []),
              .b8s tx.value.toB8LNew,
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
              .b8s gasPrice.toB8LNew,
              .b8s tx.gas.toB8LNew,
              .b8s ((tx.receiver <&> Adr.toB8L).getD []),
              .b8s tx.value.toB8LNew,
              .b8s tx.data,
              .b8s chainId.toB8LNew,
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
            .b8s gasPrice.toB8LNew,
            .b8s tx.gas.toB8LNew,
            .b8s ((tx.receiver <&> Adr.toB8L).getD []),
            .b8s tx.value.toB8LNew,
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
            .b8s maxPriorityFee.toB8LNew,
            .b8s maxFee.toB8LNew,
            .b8s tx.gas.toB8LNew,
            .b8s ((tx.receiver <&> Adr.toB8L).getD []),
            .b8s tx.value.toB8LNew,
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
            .b8s maxPriorityFee.toB8LNew,
            .b8s maxFee.toB8LNew,
            .b8s tx.gas.toB8LNew,
            .b8s ((tx.receiver <&> Adr.toB8L).getD []),
            .b8s tx.value.toB8LNew,
            .b8s tx.data,
            accessList.toBLT,
            .b8s maxBlobFee.toB8LNew,
            .list <| blobHashes.map <| .b8s ∘ B256.toB8L
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
    """
    Extracts the sender address from a transaction.

    The v, r, and s values are the three parts that make up the signature
    of a transaction. In order to recover the sender of a transaction the two
    components needed are the signature (``v``, ``r``, and ``s``) and the
    signing hash of the transaction. The sender's public key can be obtained
    with these two values and therefore the sender address can be retrieved.

    Parameters
    ----------
    tx :
        Transaction of interest.
    chain_id :
        ID of the executing chain.

    Returns
    -------
    sender : `ethereum.fork_types.Address`
        The address of the account that signed the transaction.
    """
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
  | .one _ _ _ =>
    .assert (v = 0 ∨ v = 1) "InvalidSignatureError : bad y_parity"
    (secp256k1nRecoverToAdr? r s v signingHash).toExcept "sender recovery failed"
  | .two _ _ _ _ =>
    .assert (v < 2) "InvalidSignatureError"
    (secp256k1nRecoverToAdr? r s v signingHash).toExcept "sender recovery failed"
  | .three _ _ _ _ _ _=>
    .assert (v < 2) "InvalidSignatureError"
    (secp256k1nRecoverToAdr? r s v signingHash).toExcept "sender recovery failed"


def TX_BASE_COST : Nat := 21000

def Tx.maxPriorityFee? (tx : Tx) : Option Nat :=
  match tx.type with
  | .zero _ => none
  | .one _ _ _ => none
  | .two _ maxPriorityFee _ _ => some maxPriorityFee
  | .three _ maxPriorityFee _ _ _ _ => some maxPriorityFee

def Tx.maxFee? (tx : Tx) : Option Nat :=
  match tx.type with
  | .zero _ => none
  | .one _ _ _ => none
  | .two _ _ maxFee _ => some maxFee
  | .three _ _ maxFee _ _ _ => some maxFee

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

/-
def check_transaction(
    state: State,
    tx: Transaction,
    gas_available: Uint,
    chain_id: U64,
    base_fee_per_gas: Uint,
    excess_blob_gas: U64,
) -> Tuple[Address, Uint, Tuple[VersionedHash, ...]]:
    """
    Check if the transaction is includable in the block.

    Parameters
    ----------
    state :
        Current state.
    tx :
        The transaction.
    gas_available :
        The gas remaining in the block.
    chain_id :
        The ID of the current chain.
    base_fee_per_gas :
        The block base fee.
    excess_blob_gas :
        The excess blob gas.

    Returns
    -------
    sender_address :
        The sender of the transaction.
    effective_gas_price :
        The price to charge for gas when the transaction is executed.
    blob_versioned_hashes :
        The blob versioned hashes of the transaction.

    Raises
    ------
    InvalidBlock :
        If the transaction is not includable.
    """
    if tx.gas > gas_available:
        raise InvalidBlock

    sender_address = recover_sender(chain_id, tx)

    sender_account = get_account(state, sender_address)

    if isinstance(tx, (FeeMarketTransaction, BlobTransaction)):
        if tx.max_fee_per_gas < tx.max_priority_fee_per_gas:
            raise InvalidBlock
        if tx.max_fee_per_gas < base_fee_per_gas:
            raise InvalidBlock

        priority_fee_per_gas = min(
            tx.max_priority_fee_per_gas,
            tx.max_fee_per_gas - base_fee_per_gas,
        )
        effective_gas_price = priority_fee_per_gas + base_fee_per_gas
        max_gas_fee = tx.gas * tx.max_fee_per_gas
    else:
        if tx.gas_price < base_fee_per_gas:
            raise InvalidBlock
        effective_gas_price = tx.gas_price
        max_gas_fee = tx.gas * tx.gas_price

    if isinstance(tx, BlobTransaction):
        if not isinstance(tx.to, Address):
            raise InvalidBlock
        if len(tx.blob_versioned_hashes) == 0:
            raise InvalidBlock
        for blob_versioned_hash in tx.blob_versioned_hashes:
            if blob_versioned_hash[0:1] != VERSIONED_HASH_VERSION_KZG:
                raise InvalidBlock

        blob_gas_price = calculate_blob_gas_price(excess_blob_gas)
        if Uint(tx.max_fee_per_blob_gas) < blob_gas_price:
            raise InvalidBlock

        max_gas_fee += calculate_total_blob_gas(tx) * Uint(
            tx.max_fee_per_blob_gas
        )
        blob_versioned_hashes = tx.blob_versioned_hashes
    else:
        blob_versioned_hashes = ()
    if sender_account.nonce != tx.nonce:
        raise InvalidBlock
    if Uint(sender_account.balance) < max_gas_fee + Uint(tx.value):
        raise InvalidBlock
    if sender_account.code != bytearray():
        raise InvalidSenderError("not EOA")

    return sender_address, effective_gas_price, blob_versioned_hashes
-/

def checkTransaction
  (state: Wor)
  (tx: Tx)
  (gas_available: Nat)
  (chain_id: B64)
  (base_fee_per_gas: Nat)
  (excess_blob_gas: Nat) :
  Except String (Adr × Nat × List B256) := do

  .assertNot (tx.gas > gas_available) "InvalidBlock : gas exceeds available gas"

  let senderAdr ← recoverSender chain_id tx

  let senderAcct := state.get senderAdr

  let mut max_gas_fee : Nat := 0

  let mut effective_gas_price : Nat := 0

  let selector : Nat ⊕ (Nat × Nat) :=
    match tx.type with
    | .zero gasPrice => .inl gasPrice
    | .one gasPrice _ _ => .inl gasPrice
    | .two _ maxPriorityFee maxFee _ => .inr (maxPriorityFee, maxFee)
    | .three _ maxPriorityFee maxFee _ _ _ => .inr (maxPriorityFee, maxFee)

  match selector with
  | .inl gasPrice =>
    .assertNot (gasPrice < base_fee_per_gas) "InvalidBlock : gas price below base fee"
    effective_gas_price := gasPrice
    max_gas_fee := tx.gas * gasPrice
  | .inr (maxPriorityFee, maxFee) =>

    .assertNot (maxFee < maxPriorityFee) "InvalidBlock : max fee below priority fee"

    .assertNot (maxFee < base_fee_per_gas) "InvalidBlock : max fee below base fee"

    let priority_fee_per_gas := min maxPriorityFee (maxFee - base_fee_per_gas)
    effective_gas_price := priority_fee_per_gas + base_fee_per_gas
    max_gas_fee := tx.gas * maxFee

  let blob_versioned_hashes : List B256 :=
    match tx.type with
    | .three _ _ _ _ _ blobHashes => blobHashes
    | _ => []

  match tx.type with
  | .three _ _ maxFee _ _ blobHashes =>
    if tx.receiver.isNone then
      .error "InvalidBlock : receiver is none for type 3 tx"
    if blobHashes.isEmpty then
      .error "InvalidBlock : no blob versioned hashes for type 3 tx"
    if !blobHashes.all (λ bvh => bvh.toB8V.head = 0x01) then
      .error "InvalidBlock : blob versioned hashes do not match KZG version"
    let blob_gas_price := calculate_blob_gas_price excess_blob_gas
    if maxFee < blob_gas_price then
      .error "InvalidBlock : max fee per blob gas below base fee per blob gas"
    max_gas_fee := max_gas_fee + calculateTotalBlobGas tx * maxFee
  | _ => .ok ()

  if senderAcct.nonce ≠ tx.nonce
    then .error "InvalidBlock : nonce mismatch"

  if senderAcct.bal.toNat < max_gas_fee + tx.value
    then
      .error s!"InvalidBlock : sender balance ({senderAcct.bal.toNat}) < max gas fee ({max_gas_fee}) + tx value ({tx.value})"

  if !senderAcct.code.isEmpty
    then .error "InvalidSenderError : not EOA"

  .ok ⟨senderAdr, effective_gas_price, blob_versioned_hashes⟩


/-
def calculate_intrinsic_cost(tx: Transaction) -> Uint:
    """
    Calculates the gas that is charged before execution is started.

    The intrinsic cost of the transaction is charged before execution has
    begun. Functions/operations in the EVM cost money to execute so this
    intrinsic cost is for the operations that need to be paid for as part of
    the transaction. Data transfer, for example, is part of this intrinsic
    cost. It costs ether to send data over the wire and that ether is
    accounted for in the intrinsic cost calculated in this function. This
    intrinsic cost must be calculated and paid for before execution in order
    for all operations to be implemented.

    Parameters
    ----------
    tx :
        Transaction to compute the intrinsic cost of.

    Returns
    -------
    verified : `ethereum.base_types.Uint`
        The intrinsic cost of the transaction.
    """
    from .vm.gas import init_code_cost

    data_cost = 0

    for byte in tx.data:
        if byte == 0:
            data_cost += TX_DATA_COST_PER_ZERO
        else:
            data_cost += TX_DATA_COST_PER_NON_ZERO

    if tx.to == Bytes0(b""):
        create_cost = TX_CREATE_COST + int(init_code_cost(Uint(len(tx.data))))
    else:
        create_cost = 0

    access_list_cost = 0
    if isinstance(
        tx, (AccessListTransaction, FeeMarketTransaction, BlobTransaction)
    ):
        for _address, keys in tx.access_list:
            access_list_cost += TX_ACCESS_LIST_ADDRESS_COST
            access_list_cost += len(keys) * TX_ACCESS_LIST_STORAGE_KEY_COST

    return Uint(TX_BASE_COST + data_cost + create_cost + access_list_cost)
-/

def TX_ACCESS_LIST_ADDRESS_COST : Nat := 2400
def TX_ACCESS_LIST_STORAGE_KEY_COST : Nat := 1900

def calculate_intrinsic_cost (tx: Tx) : Nat :=

  let dataCost : Nat := dataGas tx.data

  let createCost : Nat :=
    match tx.receiver with
    | none => TX_CREATE_COST + initCodeCost (tx.data).length
    | some _ => 0

  let accessList :=
    match tx.type with
    | .zero _ => []
    | .one _ _ accessList => accessList
    | .two _ _ _ accessList => accessList
    | .three _ _ _ accessList _ _ => accessList

  let accessItemCost : (Adr × List B256) → Nat
    | ⟨_, keys⟩ =>
      TX_ACCESS_LIST_ADDRESS_COST + keys.length * TX_ACCESS_LIST_STORAGE_KEY_COST

  let accessListCost : Nat := (accessList.map accessItemCost).sum

  TX_BASE_COST + dataCost + createCost + accessListCost

def MAX_CODE_SIZE : Nat := 0x6000

/-
def validate_transaction(tx: Transaction) -> bool:
    """
    Verifies a transaction.

    The gas in a transaction gets used to pay for the intrinsic cost of
    operations, therefore if there is insufficient gas then it would not
    be possible to execute a transaction and it will be declared invalid.

    Additionally, the nonce of a transaction must not equal or exceed the
    limit defined in `EIP-2681 <https://eips.ethereum.org/EIPS/eip-2681>`_.
    In practice, defining the limit as ``2**64-1`` has no impact because
    sending ``2**64-1`` transactions is improbable. It's not strictly
    impossible though, ``2**64-1`` transactions is the entire capacity of the
    Ethereum blockchain at 2022 gas limits for a little over 22 years.

    Parameters
    ----------
    tx :
        Transaction to validate.

    Returns
    -------
    verified : `bool`
        True if the transaction can be executed, or False otherwise.
    """
    from .vm.interpreter import MAX_CODE_SIZE

    if calculate_intrinsic_cost(tx) > tx.gas:
        return False
    if tx.nonce >= U256(U64.MAX_VALUE):
        return False
    if tx.to == Bytes0(b"") and len(tx.data) > 2 * MAX_CODE_SIZE:
        return False

    return True
-/
abbrev validateTransaction (tx: Tx) : Prop :=
  calculate_intrinsic_cost tx ≤ tx.gas ∧
  tx.nonce ≠ B64.max ∧
  (tx.receiver.isSome ∨ tx.data.length ≤ MAX_CODE_SIZE * 2)


/-
def prepare_message(
    caller: Address,
    target: Union[Bytes0, Address],
    value: U256,
    data: Bytes,
    gas: Uint,
    env: Environment,
    code_address: Optional[Address] = None,
    should_transfer_value: bool = True,
    is_static: bool = False,
    preaccessed_addresses: FrozenSet[Address] = frozenset(),
    preaccessed_storage_keys: FrozenSet[
        Tuple[(Address, Bytes32)]
    ] = frozenset(),
) -> Message:
    """
    Execute a transaction against the provided environment.

    Parameters
    ----------
    caller :
        Address which initiated the transaction
    target :
        Address whose code will be executed
    value :
        Value to be transferred.
    data :
        Array of bytes provided to the code in `target`.
    gas :
        Gas provided for the code in `target`.
    env :
        Environment for the Ethereum Virtual Machine.
    code_address :
        This is usually same as the `target` address except when an alternative
        accounts code needs to be executed.
        eg. `CALLCODE` calling a precompile.
    should_transfer_value :
        if True ETH should be transferred while executing a message call.
    is_static:
        if True then it prevents all state-changing operations from being
        executed.
    preaccessed_addresses:
        Addresses that should be marked as accessed prior to the message call
    preaccessed_storage_keys:
        Storage keys that should be marked as accessed prior to the message
        call

    Returns
    -------
    message: `ethereum.cancun.vm.Message`
        Items containing contract creation or message call specific data.
    """
    if isinstance(target, Bytes0):
        current_target = compute_contract_address(
            caller,
            get_account(env.state, caller).nonce - Uint(1),
        )
        msg_data = Bytes(b"")
        code = data
    elif isinstance(target, Address):
        current_target = target
        msg_data = data
        code = get_account(env.state, target).code
        if code_address is None:
            code_address = target
    else:
        raise AssertionError("Target must be address or empty bytes")

    accessed_addresses = set()
    accessed_addresses.add(current_target)
    accessed_addresses.add(caller)
    accessed_addresses.update(PRE_COMPILED_CONTRACTS.keys())
    accessed_addresses.update(preaccessed_addresses)

    return Message(
        caller=caller,
        target=target,
        gas=gas,
        value=value,
        data=msg_data,
        code=code,
        depth=Uint(0),
        current_target=current_target,
        code_address=code_address,
        should_transfer_value=should_transfer_value,
        is_static=is_static,
        accessed_addresses=accessed_addresses,
        accessed_storage_keys=set(preaccessed_storage_keys),
        parent_evm=None,
    )
-/
def prepare_message
  (caller: Adr)
  (target: Option Adr)
  (value: B256)
  (data: B8L)
  (gas: Nat)
  (env: Environment)
  (code_address: Option Adr := none)
  (should_transfer_value: Bool := True)
  (is_static: Bool := False)
  (preaccessed_addresses: AdrSet := .empty)
  (preaccessed_storage_keys: KeySet := .empty) :
  Except String Message := do

  let ⟨current_target, msg_data, code, code_address⟩ :
    Adr × B8L × ByteArray × Option Adr :=
    match target with
    | none => ⟨
        compute_contract_address caller (env.state.getNonce caller - 1),
        [],
        .mk (.mk data),
        code_address
      ⟩
    | some target => ⟨
        target,
        data,
        env.state.getCode target,
        code_address <|> target
      ⟩

  let accessed_addresses : AdrSet :=
    preaccessed_addresses.insertMany
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, current_target, caller]

  .ok {
    caller := caller,
    target := target,
    gas := gas,
    value := value,
    data := msg_data,
    code := code,
    depth := 0,
    current_target := current_target,
    code_address := code_address,
    should_transfer_value := should_transfer_value,
    is_static := is_static,
    accessed_addresses := accessed_addresses,
    accessed_storage_keys := preaccessed_storage_keys
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

/-
def process_transaction(
    env: vm.Environment, tx: Transaction
) -> Tuple[Uint, Tuple[Log, ...], Optional[EthereumException]]:
    """
    Execute a transaction against the provided environment.

    This function processes the actions needed to execute a transaction.
    It decrements the sender's account after calculating the gas fee and
    refunds them the proper amount after execution. Calling contracts,
    deploying code, and incrementing nonces are all examples of actions that
    happen within this function or from a call made within this function.

    Accounts that are marked for deletion are processed and destroyed after
    execution.

    Parameters
    ----------
    env :
        Environment for the Ethereum Virtual Machine.
    tx :
        Transaction to execute.

    Returns
    -------
    gas_left : `ethereum.base_types.U256`
        Remaining gas after execution.
    logs : `Tuple[ethereum.blocks.Log, ...]`
        Logs generated during execution.
    """
-/
def processTransaction
  (vb : Bool) (env: Environment) (tx: Tx) :
  Except String (Wor × Nat × List Log × Option String) := do

/-
    if not validate_transaction(tx):
        raise InvalidBlock

    sender = env.origin
    sender_account = get_account(env.state, sender)
-/
  .assert (validateTransaction tx) "InvalidBlock"
  let sender := env.origin

/-
    if isinstance(tx, BlobTransaction):
        blob_gas_fee = calculate_data_fee(env.excess_blob_gas, tx)
    else:
        blob_gas_fee = Uint(0)
-/
  let blob_gas_fee :=
    if tx.isTypeThree
    then calculate_data_fee env.excess_blob_gas tx
    else 0

/-
    effective_gas_fee = tx.gas * env.gas_price
    gas = tx.gas - calculate_intrinsic_cost(tx)
    increment_nonce(env.state, sender)
-/
  let effective_gas_fee := tx.gas * env.gas_price
  let gas := tx.gas - calculate_intrinsic_cost tx


  let mut env := env.incrNonce sender

/-
    sender_balance_after_gas_fee = (
        Uint(sender_account.balance) - effective_gas_fee - blob_gas_fee
    )
    set_account_balance(env.state, sender, U256(sender_balance_after_gas_fee))
-/
  env := (env.subBal sender (effective_gas_fee + blob_gas_fee).toB256).getD env

/-
    preaccessed_addresses = set()
    preaccessed_storage_keys = set()
    preaccessed_addresses.add(env.coinbase)
-/
  let mut preaccessed_addresses : AdrSet :=
    Std.HashSet.empty.insert env.coinbase
  let mut preaccessed_storage_keys : KeySet := .empty

/-
    if isinstance(
        tx, (AccessListTransaction, FeeMarketTransaction, BlobTransaction)
    ):
        for address, keys in tx.access_list:
            preaccessed_addresses.add(address)
            for key in keys:
                preaccessed_storage_keys.add((address, key))
-/
  let accessList :=
    match tx.type with
    | .zero _ => []
    | .one _ _ accessList => accessList
    | .two _ _ _ accessList => accessList
    | .three _ _ _ accessList _ _ => accessList

  for ⟨address, keys⟩ in accessList do
    preaccessed_addresses := preaccessed_addresses.insert address
    for key in keys do
      preaccessed_storage_keys := preaccessed_storage_keys.insert (address, key)

/-
    message = prepare_message(
        sender,
        tx.to,
        tx.value,
        tx.data,
        gas,
        env,
        preaccessed_addresses=frozenset(preaccessed_addresses),
        preaccessed_storage_keys=frozenset(preaccessed_storage_keys),
    )
-/
  let message ←
    prepare_message
        sender
        tx.receiver
        tx.value.toB256
        tx.data
        gas
        env
        (preaccessed_addresses := preaccessed_addresses)
        (preaccessed_storage_keys := preaccessed_storage_keys)

/-
    output = process_message_call(message, env)
    gas_used = tx.gas - output.gas_left
    gas_refund = min(gas_used // Uint(5), Uint(output.refund_counter))
    gas_refund_amount = (output.gas_left + gas_refund) * env.gas_price
-/
  let mut ⟨state, output⟩ ← processMessageCall vb message env
  let gas_used := tx.gas - output.gas_left
  let gas_refund := min (gas_used / 5) output.refund_counter
  let gas_refund_amount := (output.gas_left + gas_refund) * env.gas_price

/-
    # For non-1559 transactions env.gas_price == tx.gas_price
    priority_fee_per_gas = env.gas_price - env.base_fee_per_gas
    transaction_fee = (
        tx.gas - output.gas_left - gas_refund
    ) * priority_fee_per_gas

    total_gas_used = gas_used - gas_refund
-/
  let priority_fee_per_gas := env.gas_price - env.base_fee_per_gas
  let transaction_fee :=
    (tx.gas - output.gas_left - gas_refund) * priority_fee_per_gas
  let total_gas_used := gas_used - gas_refund

/-
    # refund gas
    sender_balance_after_refund = get_account(
        env.state, sender
    ).balance + U256(gas_refund_amount)
    set_account_balance(env.state, sender, sender_balance_after_refund)

    # transfer miner fees
    coinbase_balance_after_mining_fee = get_account(
        env.state, env.coinbase
    ).balance + U256(transaction_fee)

    if coinbase_balance_after_mining_fee != 0:
        set_account_balance(
            env.state, env.coinbase, coinbase_balance_after_mining_fee
        )
    elif account_exists_and_is_empty(env.state, env.coinbase):
        destroy_account(env.state, env.coinbase)
-/
  state := state.addBal sender gas_refund_amount.toB256
  state := state.addBal env.coinbase transaction_fee.toB256

  if AccountExistsAndIsEmpty state env.coinbase then
    state := destroyAccount state env.coinbase

/-
    for address in output.accounts_to_delete:
        destroy_account(env.state, address)

    destroy_touched_empty_accounts(env.state, output.touched_accounts)

    return total_gas_used, output.logs, output.error
-/
  for address in output.accounts_to_delete do
    state := destroyAccount state address

  state := destroyTouchedEmptyAccounts state output.touched_accounts

  .ok ⟨state, total_gas_used, output.logs, output.error⟩

structure Receipt : Type where
  succeeded : Bool
  cumulative_gas_used : Nat
  bloom : B8L
  logs : List Log

def Receipt.toBLT (r : Receipt) : BLT :=
  .list [
    .b8s r.succeeded.toB8L,
    .b8s r.cumulative_gas_used.toB8LPack,
    .b8s r.bloom,
    .list (r.logs.map Log.toBLT)
  ]


/-
def make_receipt(
    tx: Transaction,
    error: Optional[EthereumException],
    cumulative_gas_used: Uint,
    logs: Tuple[Log, ...],
) -> Union[Bytes, Receipt]:
    """
    Make the receipt for a transaction that was executed.

    Parameters
    ----------
    tx :
        The executed transaction.
    error :
        Error in the top level frame of the transaction, if any.
    cumulative_gas_used :
        The total gas used so far in the block after the transaction was
        executed.
    logs :
        The logs produced by the transaction.

    Returns
    -------
    receipt :
        The receipt for the transaction.
    """
-/
def make_receipt
  (tx: Tx)
  (error: Option String)
  (cumulative_gas_used: Nat)
  (logs: List Log) : B8L :=

/-
    receipt = Receipt(
        succeeded=error is None,
        cumulative_gas_used=cumulative_gas_used,
        bloom=logs_bloom(logs),
        logs=logs,
    )
-/
  let receipt : Receipt := {
    succeeded := error.isNone,
    cumulative_gas_used := cumulative_gas_used,
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

  head ++ receipt.toBLT.encode


def MAX_BLOB_GAS_PER_BLOCK : Nat := 786432

/-
def process_withdrawal(
    state: State,
    wd: Withdrawal,
) -> None:
    """
    Increase the balance of the withdrawing account.
    """

    def increase_recipient_balance(recipient: Account) -> None:
        recipient.balance += wd.amount * U256(10**9)

    modify_state(state, wd.address, increase_recipient_balance)
-/
def process_withdrawal -- (state: Wor) (wd: Withdrawal) : Except String Unit :=
  (state : Wor) (wd : Withdrawal) :  Wor :=
  state.addBal wd.recipient (wd.amount * (10 ^ 9).toB256)

-- def decodeTxBLT : BLT → IO (Tx × B8L × Adr)
--   | .b8s xs => do
--     let ⟨tx, sender⟩ ← decodeTxBytes xs
--     pure ⟨tx, xs, sender⟩
--   | .list l => do
--     let r : BLT := .list l
--     let ⟨tx, hs⟩ ← r.toLegacyTxHash
--     let sender ← getSender tx hs
--     return ⟨tx, r.encode, sender⟩
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
def apply_body(
    state: State,
    block_hashes: List[Hash32],
    coinbase: Address,
    block_number: Uint,
    base_fee_per_gas: Uint,
    block_gas_limit: Uint,
    block_time: U256,
    prev_randao: Bytes32,
    transactions: Tuple[Union[LegacyTransaction, Bytes], ...],
    chain_id: U64,
    withdrawals: Tuple[Withdrawal, ...],
    parent_beacon_block_root: Root,
    excess_blob_gas: U64,
) -> ApplyBodyOutput:
    """
    Executes a block.

    Many of the contents of a block are stored in data structures called
    tries. There is a transactions trie which is similar to a ledger of the
    transactions stored in the current block. There is also a receipts trie
    which stores the results of executing a transaction, like the post state
    and gas used. This function creates and executes the block that is to be
    added to the chain.

    Parameters
    ----------
    state :
        Current account state.
    block_hashes :
        List of hashes of the previous 256 blocks in the order of
        increasing block number.
    coinbase :
        Address of account which receives block reward and transaction fees.
    block_number :
        Position of the block within the chain.
    base_fee_per_gas :
        Base fee per gas of within the block.
    block_gas_limit :
        Initial amount of gas available for execution in this block.
    block_time :
        Time the block was produced, measured in seconds since the epoch.
    prev_randao :
        The previous randao from the beacon chain.
    transactions :
        Transactions included in the block.
    ommers :
        Headers of ancestor blocks which are not direct parents (formerly
        uncles.)
    chain_id :
        ID of the executing chain.
    withdrawals :
        Withdrawals to be processed in the current block.
    parent_beacon_block_root :
        The root of the beacon block from the parent block.
    excess_blob_gas :
        Excess blob gas calculated from the previous block.

    Returns
    -------
    apply_body_output : `ApplyBodyOutput`
        Output of applying the block body to the state.
    """

    blob_gas_used = Uint(0)
    gas_available = block_gas_limit
    transactions_trie: Trie[
        Bytes, Optional[Union[Bytes, LegacyTransaction]]
    ] = Trie(secured=False, default=None)
    receipts_trie: Trie[Bytes, Optional[Union[Bytes, Receipt]]] = Trie(
        secured=False, default=None
    )
    withdrawals_trie: Trie[Bytes, Optional[Union[Bytes, Withdrawal]]] = Trie(
        secured=False, default=None
    )
    block_logs: Tuple[Log, ...] = ()

    beacon_block_roots_contract_code = get_account(
        state, BEACON_ROOTS_ADDRESS
    ).code

    system_tx_message = Message(
        caller=SYSTEM_ADDRESS,
        target=BEACON_ROOTS_ADDRESS,
        gas=SYSTEM_TRANSACTION_GAS,
        value=U256(0),
        data=parent_beacon_block_root,
        code=beacon_block_roots_contract_code,
        depth=Uint(0),
        current_target=BEACON_ROOTS_ADDRESS,
        code_address=BEACON_ROOTS_ADDRESS,
        should_transfer_value=False,
        is_static=False,
        accessed_addresses=set(),
        accessed_storage_keys=set(),
        parent_evm=None,
    )

    system_tx_env = vm.Environment(
        caller=SYSTEM_ADDRESS,
        origin=SYSTEM_ADDRESS,
        block_hashes=block_hashes,
        coinbase=coinbase,
        number=block_number,
        gas_limit=block_gas_limit,
        base_fee_per_gas=base_fee_per_gas,
        gas_price=base_fee_per_gas,
        time=block_time,
        prev_randao=prev_randao,
        state=state,
        chain_id=chain_id,
        traces=[],
        excess_blob_gas=excess_blob_gas,
        blob_versioned_hashes=(),
        transient_storage=TransientStorage(),
    )

    print("\n================================ SETUP TX ================================\n")

    system_tx_output = process_message_call(system_tx_message, system_tx_env)

    destroy_touched_empty_accounts(
        system_tx_env.state, system_tx_output.touched_accounts
    )

    print("\n================================ TEST TX ================================\n")

    for i, tx in enumerate(map(decode_transaction, transactions)):

        print(f"i : {i}")
        print(f"rlp.encode(Uint(i)).hex() : {rlp.encode(Uint(i)).hex()}")

        trie_set(
            transactions_trie, rlp.encode(Uint(i)), encode_transaction(tx)
        )

        (
            sender_address,
            effective_gas_price,
            blob_versioned_hashes,
        ) = check_transaction(
            state,
            tx,
            gas_available,
            chain_id,
            base_fee_per_gas,
            excess_blob_gas,
        )

        env = vm.Environment(
            caller=sender_address,
            origin=sender_address,
            block_hashes=block_hashes,
            coinbase=coinbase,
            number=block_number,
            gas_limit=block_gas_limit,
            base_fee_per_gas=base_fee_per_gas,
            gas_price=effective_gas_price,
            time=block_time,
            prev_randao=prev_randao,
            state=state,
            chain_id=chain_id,
            traces=[],
            excess_blob_gas=excess_blob_gas,
            blob_versioned_hashes=blob_versioned_hashes,
            transient_storage=TransientStorage(),
        )

        gas_used, logs, error = process_transaction(env, tx)
        gas_available -= gas_used

        receipt = make_receipt(
            tx, error, (block_gas_limit - gas_available), logs
        )

        trie_set(
            receipts_trie,
            rlp.encode(Uint(i)),
            receipt,
        )

        block_logs += logs
        blob_gas_used += calculate_total_blob_gas(tx)
    if blob_gas_used > MAX_BLOB_GAS_PER_BLOCK:
        raise InvalidBlock
    block_gas_used = block_gas_limit - gas_available

    block_logs_bloom = logs_bloom(block_logs)

    for i, wd in enumerate(withdrawals):
        trie_set(withdrawals_trie, rlp.encode(Uint(i)), rlp.encode(wd))

        process_withdrawal(state, wd)

        if account_exists_and_is_empty(state, wd.address):
            destroy_account(state, wd.address)

    return ApplyBodyOutput(
        block_gas_used,
        root(transactions_trie),
        root(receipts_trie),
        block_logs_bloom,
        state_root(state),
        root(withdrawals_trie),
        blob_gas_used,
    )
-/
def applyBody
  (vb : Bool)
  (state orig_state : Wor)
  (created_accounts : AdrSet)
  (block_hashes: List B256)
  (coinbase: Adr)
  (block_number: Nat)
  (base_fee_per_gas: Nat)
  (block_gas_limit: Nat)
  (block_time: B256)
  (prev_randao: B256)
  (transactions: List (B8L ⊕ Tx))
  (chain_id: B64)
  (withdrawals: List Withdrawal)
  (parent_beacon_block_root: B256)
  (excess_blob_gas: Nat) : Except String (ApplyBodyOutput × Wor) := do

  let mut blob_gas_used : Nat := 0
  let mut gas_available := block_gas_limit

  let mut transactions_trie : Lean.RBMap B8L Tx compare := .empty
  let mut receipts_trie : Lean.RBMap B8L B8L compare := .empty
  let mut withdrawals_trie : Lean.RBMap B8L Withdrawal compare := .empty
  let mut block_logs : List Log := []
  let beacon_block_roots_contract_code := state.getCode BEACON_ROOTS_ADDRESS

  let system_tx_message : Message := {
    caller := SYSTEM_ADDRESS,
    target := BEACON_ROOTS_ADDRESS,
    gas := SYSTEM_TRANSACTION_GAS,
    value := 0
    data := parent_beacon_block_root.toB8L,
    code := beacon_block_roots_contract_code,
    depth := 0
    current_target := BEACON_ROOTS_ADDRESS,
    code_address := BEACON_ROOTS_ADDRESS,
    should_transfer_value := false,
    is_static := False,
    accessed_addresses := .empty
    accessed_storage_keys := .empty
  }

  let system_tx_env : Environment :=  {
    caller := SYSTEM_ADDRESS,
    origin := SYSTEM_ADDRESS,
    block_hashes := block_hashes,
    coinbase := coinbase,
    number := block_number,
    gas_limit := block_gas_limit,
    base_fee_per_gas := base_fee_per_gas,
    gas_price := base_fee_per_gas,
    time := block_time,
    prev_randao := prev_randao,
    state := state,
    orig_state := orig_state,
    created_accounts := created_accounts
    chain_id := chain_id,
    excess_blob_gas := excess_blob_gas,
    blob_versioned_hashes := [],
    transient_storage := .empty
  }


  if vb
    then dbg_trace ("\n================================ SETUP TX ================================\n")

  let mut ⟨state, system_tx_output⟩ ← processMessageCall vb system_tx_message system_tx_env

  state := destroyTouchedEmptyAccounts state system_tx_output.touched_accounts

  if vb
    then
      dbg_trace ("\nSTATE ROOT AFTER SETUP TX : \n")
      dbg_trace s!"{state.root.toHex}\n"

  if vb
    then dbg_trace ("\n================================ TEST TX ================================\n")

  for ⟨i, tx⟩ in (← transactions.mapM decodeTx).putIndex 0 do
    transactions_trie :=
      transactions_trie.insert (BLT.b8s i.toB8LNew).encode tx

    let ⟨sender_address, effective_gas_price, blob_versioned_hashes⟩ ←
      checkTransaction state tx gas_available chain_id base_fee_per_gas excess_blob_gas

    let env : Environment := {
        caller := sender_address,
        origin := sender_address,
        block_hashes := block_hashes,
        coinbase := coinbase,
        number := block_number,
        gas_limit := block_gas_limit,
        base_fee_per_gas := base_fee_per_gas,
        gas_price := effective_gas_price,
        time := block_time,
        prev_randao := prev_randao,
        state := state,
        orig_state := orig_state,
        created_accounts := created_accounts,
        chain_id := chain_id,
        excess_blob_gas := excess_blob_gas,
        blob_versioned_hashes := blob_versioned_hashes,
        transient_storage := .empty
    }

    let ⟨newState, gas_used, logs, error⟩ ← processTransaction vb env tx
    state := newState
    gas_available := gas_available - gas_used

    let receipt :=
      make_receipt tx error (block_gas_limit - gas_available) logs

    receipts_trie :=
      receipts_trie.insert (BLT.b8s i.toB8LNew).encode receipt

    block_logs := block_logs ++ logs
    blob_gas_used := blob_gas_used + calculate_total_blob_gas tx

  .assertNot (blob_gas_used > MAX_BLOB_GAS_PER_BLOCK) "InvalidBlock"

  let block_gas_used := block_gas_limit - gas_available

  let block_logs_bloom := logs_bloom block_logs

  for ⟨i, wd⟩ in withdrawals.putIndex 0 do
    withdrawals_trie :=
      withdrawals_trie.insert (BLT.b8s i.toB8LNew).encode wd
    state := process_withdrawal state wd
    if AccountExistsAndIsEmpty state wd.recipient then
      state := destroyAccount state wd.recipient

  let receiptRoot : B256 :=
    let receiptAux (arg : B8L × B8L) : B8L × B8L :=
      ⟨arg.fst.toB4s, arg.snd⟩
    let temp := (List.map receiptAux receipts_trie.toList)
    trie <| Lean.RBMap.fromList temp _

  let transactionsRoot : B256 ← do
    let transactionsAux (arg : B8L × Tx) : Except String (B8L × B8L) := do
      let txBLT : BLT := arg.snd.toBLT
      .ok ⟨arg.fst.toB4s, txBLT.encode⟩
    let temp ← List.mapM transactionsAux transactions_trie.toList
    .ok <| trie <| Lean.RBMap.fromList temp _

  let withdrawalsRoot : B256 :=
    let withdrawalsAux (arg : B8L × Withdrawal) : B8L × B8L :=
      ⟨arg.fst.toB4s, arg.snd.toBLT.encode⟩
    let temp := (List.map withdrawalsAux withdrawals_trie.toList)
    trie <| Lean.RBMap.fromList temp _

  .ok ⟨
    {
      blockGasUsed := block_gas_used
      transactionsRoot := transactionsRoot
      receiptRoot := receiptRoot
      blockLogsBloom := block_logs_bloom
      stateRoot := state.root
      withdrawalsRoot := withdrawalsRoot
      blobGasUsed := blob_gas_used
    },
    state
  ⟩

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
def get_last_256_block_hashes (chain : BlockChain) : List B256 :=
  match chain.blocks.reverse.take 255 with
  | [] => []
  | block :: blocks =>
    let hash : B256 := block.header.toBLT.encode.keccak
    let hashes : List B256 :=
      blocks.map <| fun x => x.header.parentHash
    (hash :: hashes).reverse

/-
def state_transition(chain: BlockChain, block: Block) -> None:
    """
    Attempts to apply a block to an existing block chain.

    All parts of the block's contents need to be verified before being added
    to the chain. Blocks are verified by ensuring that the contents of the
    block make logical sense with the contents of the parent block. The
    information in the block's header must also match the corresponding
    information in the block.

    To implement Ethereum, in theory clients are only required to store the
    most recent 255 blocks of the chain since as far as execution is
    concerned, only those blocks are accessed. Practically, however, clients
    should store more blocks to handle reorgs.

    Parameters
    ----------
    chain :
        History and current state.
    block :
        Block to apply to `chain`.
    """
    parent_header = chain.blocks[-1].header
    excess_blob_gas = calculate_excess_blob_gas(parent_header)

    if block.header.excess_blob_gas != excess_blob_gas:
        raise InvalidBlock

    validate_header(block.header, parent_header)
    if block.ommers != ():
        raise InvalidBlock
    apply_body_output = apply_body(
        chain.state,
        get_last_256_block_hashes(chain),
        block.header.coinbase,
        block.header.number,
        block.header.base_fee_per_gas,
        block.header.gas_limit,
        block.header.timestamp,
        block.header.prev_randao,
        block.transactions,
        chain.chain_id,
        block.withdrawals,
        block.header.parent_beacon_block_root,
        excess_blob_gas,
    )
    if apply_body_output.block_gas_used != block.header.gas_used:
        raise InvalidBlock(
            f"{apply_body_output.block_gas_used} != {block.header.gas_used}"
        )
    if apply_body_output.transactions_root != block.header.transactions_root:
        raise InvalidBlock
    if apply_body_output.state_root != block.header.state_root:
        raise InvalidBlock
    if apply_body_output.receipt_root != block.header.receipt_root:
        raise InvalidBlock
    if apply_body_output.block_logs_bloom != block.header.bloom:
        raise InvalidBlock
    if apply_body_output.withdrawals_root != block.header.withdrawals_root:
        raise InvalidBlock
    if apply_body_output.blob_gas_used != block.header.blob_gas_used:
        raise InvalidBlock

    chain.blocks.append(block)
    if len(chain.blocks) > 255:
        # Real clients have to store more blocks to deal with reorgs, but the
        # protocol only requires the last 255
        chain.blocks = chain.blocks[-255:]
-/
def state_transition (vb : Bool) (chain : BlockChain) (block : Block) :
  Except String BlockChain :=
  match chain.blocks.getLast? with
  | none => .error "error : cannot fetch last block, chain is empty"
  | some parentBlock =>
    let parentHeader := parentBlock.header
    let excessBlobGas := calculateExcessBlobGas parentHeader
    if (excessBlobGas ≠ block.header.excessBlobGas)
    then .error "InvalidBlock"
    else do
       validateHeader block.header parentHeader
       .assert block.ommers.isEmpty "InvalidBlock"
       let (⟨apply_body_output, state⟩ : ApplyBodyOutput × Wor) ←
         applyBody
           vb
           chain.state
           chain.state
           .empty
           (get_last_256_block_hashes chain)
           block.header.coinbase
           block.header.number
           block.header.baseFeePerGas
           block.header.gasLimit
           block.header.timestamp.toB256
           block.header.prevRandao
           block.txs
           chain.chainId.toUInt64
           block.wds
           block.header.parentBeaconBlockRoot
           excessBlobGas

       .assert
         ( (apply_body_output.blockGasUsed = block.header.gasUsed) ∨
           (apply_body_output.transactionsRoot = block.header.txsRoot) ∨
           (apply_body_output.stateRoot = block.header.stateRoot) ∨
           (apply_body_output.receiptRoot = block.header.receiptRoot) ∨
           (apply_body_output.blockLogsBloom = block.header.bloom) ∨
           (apply_body_output.withdrawalsRoot = block.header.withdrawalsRoot) ∨
           (apply_body_output.blobGasUsed = block.header.blobGasUsed) )
         "InvalidBlock"

       .ok {
         state := state
         blocks := (block :: chain.blocks.reverse.take 254).reverse
         chainId := chain.chainId
       }


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
  return ⟨block, block.header.toBLT.encode.keccak⟩

def addBlockToChain (vb : Bool) (chain : BlockChain) (blockRlp : B8L) :
  IO (BlockChain ⊕ String) := do

  --let ⟨block, blockHeaderHash, blockRlp⟩ ← Lean.Json.toBlock json
  let ⟨block, blockHeaderHash⟩ ← rlpToBlock blockRlp

--  let headerJson ← json.find "blockHeader"
--  let rlp ← json.find "rlp" >>= Lean.Json.toIoB8L
--  let blockHeaderHash ← headerJson.find "hash" >>= Lean.Json.toIoB256
--  let header ← headerJson.toHeader
--
--  let txJsons ← json.find "transactions" >>= Lean.Json.fromArr
--
--  let txs ← mapM Lean.Json.toIoTx txJsons
--
--  let [] ← json.find "uncleHeaders" >>= Lean.Json.fromArr | .throw "error : nonempty uncleHeaders"
--  let [] ← json.find "withdrawals" >>= Lean.Json.fromArr | .throw "error : nonempty withdrawals"
--
--  let block : Block := {
--    header := header
--    txs := txs
--    ommers := []
--    wds := []
--  }

  .cprintln vb "\nSTATE BEFORE TRANSITION :"
  .cprintln vb s!"{chain.state}"

  .guard (block.header.toBLT.encode.keccak = blockHeaderHash) "error : incorrect block header hash"

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

def runTest (vb : Bool) (nw : Option String) : ((_ : String) × Lean.Json) → IO Unit
  | ⟨name, json⟩ => do
    .println s!"TEST KEY : {name}"

    match nw with
    | none => .ok ()
    | some specNw =>
      let testNw ← json.find "network" >>= Lean.Json.fromStr
      if specNw ≠ testNw then
        .println s!"specified network '{specNw}' ≠ test network '{testNw}', skipping."
        return ()

    let gbh_json ← json.find "genesisBlockHeader"
    let gbh ← gbh_json.toHeader
    let gb : Block := {header := gbh, txs := [], ommers := [], wds := []}
    let gbh_hash ← gbh_json.find "hash" >>= Lean.Json.toIoB256
    let gbh_hash' := (BLT.encode gbh.toBLT).keccak
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
      chainId := chainId
    }

    let blockJsons ← json.find "blocks" >>= Lean.Json.fromArr

    let (some chain) ← processBlockJsons vb chain blockJsons | .ok ()


    let lastBlockHash ← json.find "lastblockhash" >>= Lean.Json.toIoB256
    let lastBlock ← chain.blocks.getLast?.toIO "error : no last block "
    let lastBlockHash' := lastBlock.header.toBLT.encode.keccak--  (B8L.keccak ∘ BLT.encode)
    .guard
      (lastBlockHash = lastBlockHash')
      s!"error : last block hash does not match\n  expected : {lastBlockHash}\n  computed : {lastBlockHash'}"

    let postStateRoot ← getPostStateRoot json
    .guard
      (postStateRoot = chain.state.root)
      s!"error : end state root does not match\n  expected : {postStateRoot}\n  computed : {chain.state.root}"


-- def mkTest : ((_ : String) × Lean.Json) → IO Test
--   | ⟨name, j⟩ => do
--     let info ← j.find "_info"
--     let blocks ← j.find "blocks"
--     let gbh ← j.find "genesisBlockHeader"
--     let grlp ← j.find "genesisRLP"
--     let lbh ← j.find "lastblockhash"
--     let network ← j.find "network"
--     let xws ← getXWS j -- j.find "postState"
--     let pre ← j.find "pre"
--     let sealEngine ← j.find "sealEngine"
--     return ⟨name, info, blocks, gbh, grlp, lbh, network, pre, xws, sealEngine⟩


def runPyTestFile (vb : Bool) (idx : Option Nat)
  (nw : Option String) (path : String) : IO Unit := do
  .println "\n================================================================\n"
  .println s!"Testing file : {path}\n"
  let rb ← readJsonFile path >>= Lean.Json.fromObj
  let js := rb.toArray.toList
  match idx with
  | none => let _ ← mapM (runTest vb nw) js
  | some k =>
    match js.get? k with
    | none => .println s!"Test #{k} does not exist, skipping."
    | some j => runTest vb nw j



  --let ts ← j.toTests
  --match idx with
  --| none => let _ ← mapM (runPyTest vb) ts
  --| some k =>
  --  match ts.get? k with
  --  | none => pure ()
  --  | some t => runPyTest vb t

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
    let b ← System.FilePath.isDir path
    if !b
    then runPyTestFile vb idx nw path
    else do
      let fs ← System.FilePath.walkDir path
      let _← mapM (runPyTestFile vb idx nw) (fs.toList.map System.FilePath.toString)
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
