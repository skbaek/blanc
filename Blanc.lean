import Lean.Data.Json
import Lean.Data.Json.Parser
import Lean.Data.HashSet
import Mathlib.Data.ZMod.Defs
import «Blanc».Weth

inductive Exception : Type
  | noBlobs
  | tooManyBlobs
  | blobCreation
  | wrongBlobHashVersion
  | initCodeTooLong
  | nonceTooHigh
deriving DecidableEq

def Exception.toString : Exception → String
  | noBlobs => "noBlobs"
  | tooManyBlobs => "tooManyBlobs"
  | blobCreation => "blobCreation"
  | wrongBlobHashVersion => "wrongBlobHashVersion"
  | initCodeTooLong => "initCodeTooLong"
  | nonceTooHigh => "nonceTooHigh"

instance : ToString Exception := ⟨Exception.toString⟩

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

def Stor.toStrings (s : Stor) : List String :=
  let kvs := s.toArray.toList
  let kvToStrings : B256 × B256 → List String :=
    λ nb => [s!"{B256.toHex nb.fst} : {B256.toHex nb.snd}"]
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
    [s!"nonce : 0x{a.nonce.toHex}"],
    [s!"bal : 0x{a.bal.toHex}"],
    a.stor.toStrings,
    longB8LToStrings "code" a.code.toList
  ]

def Wor.toStrings (w : Wor) : List String :=
  let kvs := w.toArray.toList
  let kvToStrings : Adr × Acct → List String :=
    fun x => Acct.toStrings x.fst.toHex x.snd
  fork "world" (kvs.map kvToStrings)

def Lean.Json.fromArr : Lean.Json → IO (List Json)
  | .arr a => return a.toList
  | _ => IO.throw "not an array"

def Lean.Json.fromObj : Lean.Json → IO (RBNode String (λ _ => Json))
  | .obj r => return r
  | _ => IO.throw "not an object"

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

def parseException : String → Option Exception
  | "TransactionException.TYPE_3_TX_ZERO_BLOBS" => some .noBlobs
  | "TransactionException.TYPE_3_TX_BLOB_COUNT_EXCEEDED" => some .tooManyBlobs
  | "TransactionException.TYPE_3_TX_CONTRACT_CREATION" => some .blobCreation
  | "TransactionException.TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH" => some .wrongBlobHashVersion
  | "TransactionException.INITCODE_SIZE_EXCEEDED" => some .initCodeTooLong
  | "TransactionException.NONCE_IS_MAX" => some .nonceTooHigh
  | _ => .none

def Lean.Json.toB8L (j : Json) : IO B8L := do
  let x ← fromStr j >>= .remove0x
  (Hex.toB8L x).toIO ""

def Lean.Json.toAdr (j : Json) : IO Adr := do
  let x ← fromStr j >>= .remove0x
  (Hex.toAdr x).toIO ""

def Lean.Json.toOptionAdr (j : Json) : IO (Option Adr) := do
  let s ← fromStr j
  match s with
  | "" => pure .none
  | _ => do
    let s' ← .remove0x s
    (Hex.toAdr s').toIO ""

def Lean.Json.toAdrs (j : Json) : IO (List Adr) :=
  fromArr j >>= mapM toAdr

def Lean.Json.toB256? (j : Json) : IO B256 := do
  let x ← fromStr j >>= .remove0x
  (Hex.toB256? x).toIO ""

def Lean.Json.toB256P (j : Json) : IO B256 := do
  let x ← fromStr j >>= .remove0x
  let xs ← (Hex.toB8L x).toIO ""
  return (B8L.toB256P xs)

def Lean.Json.toAccessEntry (j : Json) : IO (Adr × List B256) := do
  let r ← fromObj j
  let a ← (r.find compare "address").toIO "" >>= toAdr
  let ks ← (r.find compare "storageKeys").toIO "" >>= fromArr >>= mapM toB256P
  return ⟨a, ks⟩

def Lean.Json.toAccessList (j : Json) : IO AccessList := do
  fromArr j >>= mapM toAccessEntry

def helper (xy :(_ : String) × Lean.Json) : IO (B256 × B256) := do
  let x ← .remove0x xy.fst
  let bs ← (Hex.toB8L x).toIO ""
  let bs' ← xy.snd.toB8L
  return ⟨bs.toB256P, bs'.toB256P⟩

inductive TxType : Type
  -- Legacy (including EIP-155)
  | zero
    (gasPrice : B256)
    (chainId : Option Nat)
  -- -- EIP-2930
  -- | one : TxType
  -- EIP-1559
  | two
    (chainId : Nat)
    (maxPriorityFee : B256)
    (maxFee : B256)
    (accessList : AccessList)
  -- EIP-4844
  | three
    (chainId : Nat)
    (maxPriorityFee : B256)
    (maxFee : B256)
    (accessList : AccessList)
    (maxBlobFee : B256)
    (blobHashes : List B256)

def Lean.RBMap.fromSingleton {ξ υ f} (m : RBMap ξ υ f) : Option (ξ × υ) :=
  match m.toList with
  | [kv] => some kv
  | _ => none

def Lean.RBMap.singleton {ξ υ f} (x : ξ) (y : υ) : RBMap ξ υ f := RBMap.empty.insert x y

structure Tx : Type where
  (nonce : B256)
  (gasLimit : B256)
  (receiver : Option Adr)
  (val : B256)
  (calldata : B8L)
  (yParity : Bool)
  (r : B8L)
  (s : B8L)
  (type : TxType)

structure Stx : Type where
  (nonce : B256)
  (gasLimit : B256)
  (sender : Adr)
  (receiver : Option Adr)
  (val : B256)
  (calldata : B8L)
  (type : TxType)

def TxType.toStrings : TxType → List String
  | zero
    (gasPrice : B256)
    (chainId : Option Nat) =>
    fork "Type-0" [
      fork "gas price" [[gasPrice.toHex]],
      fork "chain ID" [[s!"{chainId}"]]
    ]
  | two
    (chainId : Nat)
    (maxPriorityFee : B256)
    (maxFee : B256)
    (accessList : AccessList) =>
    fork "Type-2" [
      [s!"chain ID : {chainId}"],
      [s!"max priority fee : {maxPriorityFee.toHex}"],
      [s!"max fee : {maxFee.toHex}"],
      accessList.toStrings
    ]
  | three
    (chainId : Nat)
    (maxPriorityFee : B256)
    (maxFee : B256)
    (accessList : AccessList)
    (maxBlobFee : B256)
    (blobHashes : List B256) =>
    fork "Type-3" [
      [s!"chain ID : {chainId}"],
      [s!"max priority fee : {maxPriorityFee.toHex}"],
      [s!"max fee : {maxFee.toHex}"],
      accessList.toStrings,
      [s!"max blob fee : {maxBlobFee.toHex}"],
      fork "blob hashes" (blobHashes.map <| fun bh => [bh.toHex])
    ]


instance : ToString TxType := ⟨String.joinln ∘ TxType.toStrings⟩

def Tx.toStrings (tx : Tx) : List String :=
  fork "tx" [
    [s!"nonce : {tx.nonce.toHex}"],
    [s!"gas limit : {tx.gasLimit.toHex}"],
    [s!"receiver : {tx.receiver}"],
    [s!"value : {tx.val.toHex}"],
    [s!"calldata : {tx.calldata.toHex}"],
    [s!"y-parity : {tx.yParity}"],
    [s!"r : {tx.r.toHex}"],
    [s!"s : {tx.s.toHex}"],
    tx.type.toStrings
  ]

instance : ToString Tx := ⟨String.joinln ∘ Tx.toStrings⟩

def TxType.gasPrice (baseFee : B256) : TxType → B256
  | .zero gp _ => gp
  | .two _ mpf mf _ => min mf (baseFee + mpf)
  | .three _ mpf mf _ _ _ => min mf (baseFee + mpf)

def TxType.chainId : TxType → Nat
  | .zero _ cid => cid.getD 1
  | .two cid _ _ _ => cid
  | .three cid _ _ _ _ _ => cid

def TxType.accessList : TxType → AccessList
  | .zero _ _ => []
  | .two _ _ _ al => al
  | .three _ _ _ al _ _ => al

def TxType.isBlobTx : TxType → Bool
  | .three _ _ _ _ _ _ => 1
  | _ => 0

def TxType.blobHashes : TxType → List B256
  | .zero _ _ => []
  | .two _ _ _ _ => []
  | .three _ _ _ _ _ bhs => bhs

def Stx.blobHashes (tx : Stx) : List B256 := tx.type.blobHashes
def Tx.blobHashes (tx : Tx) : List B256 := tx.type.blobHashes

def BLT.toAdr : BLT → Option Adr
  | .b8s bs => bs.toAdr
  | _ => none

def BLT.toB256 : BLT → Option B256
  | .b8s bs => some bs.toB256P
  | _ => none

def BLT.toAccessEntry : BLT → Option (Adr × List B256)
  | .list [.b8s ar, .list ksr] => do
    let a ← B8L.toAdr ar
    let ks ← mapM toB256 ksr
    pure ⟨a, ks⟩
  | _ => none

def BLT.toAccessList : BLT → Option AccessList
  | .list rs => mapM toAccessEntry rs
  | _ => none

instance : ToString BLT := ⟨String.joinln ∘ BLT.toStrings⟩

def B8L.toReceiver : B8L → IO (Option Adr)
  | [] => pure .none
  | xs@(_ :: _) => (B8L.toAdr xs).toIO "cannot convert bytes to receiver address"

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

def BLT.toLegacyTxHash : BLT → IO (Tx × B256)
  | BLT.list [
      .b8s nonce,
      .b8s gasPrice,
      .b8s gasLimit,
      .b8s receiver,
      .b8s val,
      .b8s calldata,
      .b8s [v],
      .b8s r,
      .b8s s
    ] => do
    let ⟨yParity, chainId⟩ ← decodeV v
    let bs :=
      BLT.encode <|
        .list [
          .b8s nonce,
          .b8s gasPrice,
          .b8s gasLimit,
          .b8s receiver,
          .b8s val,
          .b8s calldata
        ]
    return ⟨
      {
        nonce := nonce.toB256P
        gasLimit := gasLimit.toB256P
        receiver := (← receiver.toReceiver)
        val := val.toB256P
        calldata := calldata
        yParity := yParity
        r := (r.reverse.takeD 32 0).reverse
        s := (s.reverse.takeD 32 0).reverse
        type :=
          .zero gasPrice.toB256P chainId
      },
      bs.keccak
    ⟩
  | _ => IO.throw "error : cannot RLP-decode for type-0 tx"


def decodeTxHash : B8L → IO (Tx × B256)
  | [] => IO.throw "error : cannot decode empty bytes"
  | 0x01 :: _ => IO.throw "unimplemented : Type-1 tx decoding"
  | 0x02 :: tbs =>
    match BLT.decode tbs with
    | BLT.list [
        .b8s chainId,
        .b8s nonce,
        .b8s maxPriorityFee,
        .b8s maxFee,
        .b8s gasLimit,
        .b8s receiver,
        .b8s val,
        .b8s calldata,
        accessList,
        .b8s yParity,
        .b8s r,
        .b8s s
      ] => do
      let bs : B8L :=
        BLT.encode <|
          .list [
            .b8s chainId,
            .b8s nonce,
            .b8s maxPriorityFee,
            .b8s maxFee,
            .b8s gasLimit,
            .b8s receiver,
            .b8s val,
            .b8s calldata,
            accessList
          ]

      return ⟨
        {
          nonce := nonce.toB256P
          gasLimit := gasLimit.toB256P
          receiver := (← receiver.toReceiver)
          val := val.toB256P
          calldata := calldata
          yParity := (← decodeYParity yParity)
          r := (r.reverse.takeD 32 0).reverse
          s := (s.reverse.takeD 32 0).reverse
          type :=
            .two
              chainId.toNat
              maxPriorityFee.toB256P
              maxFee.toB256P
              (← accessList.toAccessList.toIO "cannot decode access list")
        },
        B8L.keccak (0x02 :: bs)
      ⟩
    | _ => IO.throw "error : cannot decode type-2 tx"
  | 0x03 :: tbs =>
    match BLT.decode tbs with
    | BLT.list [
        .b8s chainId,
        .b8s nonce,
        .b8s maxPriorityFee,
        .b8s maxFee,
        .b8s gasLimit,
        .b8s receiver,
        .b8s val,
        .b8s calldata,
        accessList,
        .b8s maxBlobFee,
        .list blobHashes,
        .b8s yParity,
        .b8s r,
        .b8s s
      ] => do
      let bs : B8L :=
        BLT.encode <|
          .list [
            .b8s chainId,
            .b8s nonce,
            .b8s maxPriorityFee,
            .b8s maxFee,
            .b8s gasLimit,
            .b8s receiver,
            .b8s val,
            .b8s calldata,
            accessList,
            .b8s maxBlobFee,
            .list blobHashes,
          ]
      return ⟨
        {
          nonce := nonce.toB256P
          gasLimit := gasLimit.toB256P
          receiver := (← receiver.toReceiver)
          val := val.toB256P
          calldata := calldata
          yParity := (← decodeYParity yParity)
          r := (r.reverse.takeD 32 0).reverse
          s := (s.reverse.takeD 32 0).reverse
          type :=
            .three
              chainId.toNat
              maxPriorityFee.toB256P
              maxFee.toB256P
              (← accessList.toAccessList.toIO "cannot decode access list")
              maxBlobFee.toB256P
              (← mapM (λ r => r.toB256.toIO "") blobHashes)
        },
        B8L.keccak (0x03 :: bs)
        -- B8L.keccak (0x03 :: bs)
      ⟩
    | _ => IO.throw "error : cannot RLP-decode for type-3 tx"
  | bs => do
    let r ← (BLT.decode bs).toIO "cannot RLP-decode legacy TX"
    r.toLegacyTxHash

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
    else B8L.toAdr pa

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

def B8L.sig (bs : B8L) : B8L := List.dropWhile (· = 0) bs

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
def gAccesslistaddress : Nat := 2400
def gAccessliststorage : Nat := 1900
def gInitcodeword : Nat := 2
def gBase : Nat := 2
def GAS_COPY : Nat := 3
def gReturnDataCopy : Nat := 3
def gMemory : Nat := 3
def gKeccak256 : Nat := 30
def gKeccak256Word : Nat := 6
def cMem (a : Nat) := gMemory * a + ((a ^ 2) / 512)
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
def gCodedeposit : Nat := 200
def gCreate : Nat := 32000
def gHashopcode : Nat := 3
def gasPerBlob : B256 := B32.toB256 0x00020000
def GAS_STORAGE_UPDATE := 5000

def maxCodeSize : Nat := 24576 -- 0x00006000
def maxInitcodeSize : Nat := 49152-- 0x0000C000
def maxNonce : Nat := (2 ^ 64) - 1

def initCodeCost (cd : B8L) : Nat :=
  gInitcodeword * ((cd.length / 32) + if 32 ∣ cd.length then 0 else 1)

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
  excess_blob_gas: B64
  blob_versioned_hashes: List B256
  transient_storage: Tra --nsientStorage

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

inductive ExHalt : Type
  | stackUnderflowError
  | stackOverflowError
  | outOfGasError
  | invalidOpcode : B8 → ExHalt
  | invalidJumpDestError
  | stackDepthLimitError
  | writeInStaticContext
  | outOfBoundsRead
  | invalidParameter
  | invalidContractPrefix
  | addressCollision
  | kzgProofError
deriving DecidableEq

inductive GenEx : Type
  | assertionError
deriving DecidableEq

inductive EthEx : Type
  | revert
  | exHalt : ExHalt → EthEx
  | gen : GenEx → EthEx
deriving DecidableEq

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
  error: Option EthEx -- Optional[EthereumException]
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

def chargeGas (cost : Nat) (evm : Evm) : Except (Evm × EthEx) Evm := do
  let gas ← (safeSub evm.gas_left cost).toExcept ⟨evm, .exHalt .outOfGasError⟩
  .ok {evm with gas_left := gas}

def Nat.secp256k1n : Nat := 15792089237316195423570985008687907852837564279074904382605163141518161494337
def B256.secp256k1n : B256 := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

def B256.toAdr : B256 → Adr
  | ⟨⟨_, x⟩, ⟨y, z⟩⟩ => {high := x.toUInt32, mid := y, low := z}

def Adr.toB256 (a : Adr) : B256 :=
  ⟨⟨0, a.high.toUInt64⟩ , ⟨a.mid, a.low⟩ ⟩

def execute_ecrec (evm : Evm) : Except (Evm × EthEx) Evm := do
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

def execute_sha (evm : Evm) : Except (Evm × EthEx) Evm := do
  let data := evm.message.data
  let word_count := ceilDiv data.length 32
  let evm ← chargeGas (GAS_SHA256 + GAS_SHA256_WORD * word_count) evm
  let hash : B256 := B8L.sha256 data
  .ok {evm with output := hash.toB8L}

def GAS_RIPEMD160 : Nat := 600
def GAS_RIPEMD160_WORD : Nat := 120

def execute_ripemd160 (evm : Evm) : Except (Evm × EthEx) Evm := do
  let data := evm.message.data
  let word_count := ceilDiv data.length 32
  let evm ← chargeGas (GAS_RIPEMD160 + GAS_RIPEMD160_WORD * word_count) evm
  let hash : B256 := B8L.toB256P <| (rip160 ⟨.mk data⟩).toList
  .ok {evm with output := hash.toB8L}

def GAS_IDENTITY : Nat := 15
def GAS_IDENTITY_WORD : Nat := 3

def execute_id (evm : Evm) : Except (Evm × EthEx) Evm := do
  let data := evm.message.data
  let word_count := ceilDiv data.length 32
  let evm ← chargeGas (GAS_IDENTITY + GAS_IDENTITY_WORD * word_count) evm
  .ok {evm with output := data}

def execute_modexp (evm : Evm) : Except (Evm × EthEx) Evm := do
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
  .ok {evm with output := B8L.pack expmod.toB8L l_M}

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
  p.x.val.toB8L.pack 32 ++ p.y.val.toB8L.pack 32

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

def EthEx.oog : EthEx := .exHalt .outOfGasError

def execute_ecadd (evm : Evm) : Except (Evm × EthEx) Evm := do
  let data := evm.message.data
  let evm ← chargeGas 150 evm

  let x0_value : Nat := B8L.toNat <| data.sliceD 0  32 (0 : B8)
  let y0_value : Nat := B8L.toNat <| data.sliceD 32 32 (0 : B8)
  let x1_value : Nat := B8L.toNat <| data.sliceD 64 32 (0 : B8)
  let y1_value : Nat := B8L.toNat <| data.sliceD 96 32 (0 : B8)

  .guard ⟨evm, .exHalt .outOfGasError⟩  (
    x0_value < altBn128Prime ∧
    x0_value < altBn128Prime ∧
    x1_value < altBn128Prime ∧
    x1_value < altBn128Prime
  )

  let p0 ← (Point.mk? x0_value y0_value).toExcept ⟨evm, .oog⟩
  let p1 ← (Point.mk? x1_value y1_value).toExcept ⟨evm, .oog⟩
  .ok {evm with output := (Point.add p0 p1).toB8L}

def execute_ecmul (evm : Evm) : Except (Evm × EthEx) Evm := do
  let data := evm.message.data
  let evm ← chargeGas 6000 evm

  let x_value : Nat := B8L.toNat <| data.sliceD 0  32 (0 : B8)
  let y_value : Nat := B8L.toNat <| data.sliceD 32 32 (0 : B8)
  let n       : Nat := B8L.toNat <| data.sliceD 64 32 (0 : B8)

  .guard ⟨evm, .exHalt .outOfGasError⟩
    (x_value < altBn128Prime ∧ y_value < altBn128Prime)

  let p ← (Point.mk? x_value y_value).toExcept ⟨evm, .oog⟩

  .ok {evm with output := (Point.mul p n).toB8L}

def execute_precomp (evm : Evm) : Nat → Except (Evm × EthEx) Evm
  | 1 => execute_ecrec evm
  | 2 => execute_sha evm
  | 3 => execute_ripemd160 evm
  | 4 => execute_id evm
  | 5 => execute_modexp evm
  | 6 => execute_ecadd evm
  | 7 => execute_ecmul evm
  | n => dbg_trace s!"precomp uninplemented : {n}" ; .ok evm

def execute (evm : Evm) : Except (Evm × EthEx) Evm := sorry

inductive Ninst' : Type
  | reg : Rinst → Ninst'
  | exec : Xinst → Ninst'
  | push : B256 → Nat →  Ninst' --∀ bs : B8L, bs.length ≤ 32 → Ninst'

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

def get_base_fee_per_blob_gas (excessBlobGas : Nat) : Nat :=
  fakeExp 1 excessBlobGas BLOB_BASE_FEE_UPDATE_FRACTION

def Evm.push (x : B256) (evm : Evm) : Except (Evm × EthEx) Evm := do
  .guard ⟨evm, .exHalt .stackOverflowError⟩ (evm.stack.length < 1024)
  .ok {evm with stack := x :: evm.stack}

def Evm.pop (evm : Evm) : Except (Evm × EthEx) (B256 × Evm) := do
  match evm.stack with
  | [] => .error ⟨evm, .exHalt .stackUnderflowError⟩
  | x :: xs => .ok ⟨x, {evm with stack := xs}⟩

def Prod.mapFst {α₁ : Type u₁} {α₂ : Type u₂} {β : Type v} (f : α₁ → α₂) : α₁ × β → α₂ × β :=
  Prod.map f id

def Evm.popToNat (evm : Evm) : Except (Evm × EthEx) (Nat × Evm) :=
  evm.pop <&> Prod.mapFst B256.toNat

def Evm.popN (evm : Evm) : Nat → Except (Evm × EthEx) (List B256 × Evm)
  | 0 => .ok ⟨[], evm⟩
  | n + 1 => do
    let ⟨x, evm⟩ ← evm.pop
    let ⟨xs, evm⟩ ← evm.popN n
    .ok ⟨x :: xs, evm⟩

abbrev Execution : Type := Except (Evm × EthEx) Evm

def Evm.incrPc (evm : Evm) : Execution :=
  .ok {evm with pc := evm.pc + 1}

def Evm.update (evm : Evm) (cost : Nat)
  (out : B8L := evm.output)
  (adrs : AdrSet := evm.accessed_addresses)
  (logs : List Log := evm.logs)
  (keys : KeySet := evm.accessed_storage_keys) : Execution := do
  let gas ← (safeSub evm.gas_left cost).toExcept ⟨evm, .exHalt .outOfGasError⟩
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
def gCallValue : Nat := 9000
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

def Environment.setTransVal (env : Environment)
  (adr : Adr) (key val : B256) : Environment :=
  {env with state := env.state.setStorVal adr key val}

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
    max current_size (ceilDiv (access_index + access_size) 32)

def memExtsSize : Nat → List (Nat × Nat) → Nat
  | initSize, [] => initSize
  | initSize, ⟨accessIndex, accessSize⟩ :: pairs =>
    let expSize := memExtSize initSize accessIndex accessSize
    memExtsSize expSize pairs

def Evm.extCost (evm : Evm) (pairs : List (Nat × Nat)) : Nat :=
  let extSize := memExtsSize evm.memory.size pairs
  cMem extSize - cMem evm.memory.size

-- def memCost (υ : Var) (lc sz : B256) : Nat :=
--   let act' : Nat := memExp υ.act lc sz
--   cMem act' - cMem υ.act
--
-- def memExpCost (υ : Var) (lc sz : B256) : Nat × Nat :=
--   let act' : Nat := memExp υ.act lc sz
--   ⟨act', cMem act' - cMem υ.act⟩

-- def Evm.extCost (evm : Evm) (access_start_index access_size : B256) : Nat :=
--   let extended_size : Nat :=
--     memExp evm.memory.size access_start_index access_size
--   cMem extended_size - cMem evm.memory.size

def Mem.write (μ : Mem) (n : ℕ) : B8L → Mem
  | [] => μ
  | xs@(_ :: _) =>
    if n + xs.length ≤ μ.size
    then Array.writeD μ n xs
    else let μ₀ : Mem := Array.mkArray (n + xs.length) 0x00
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

def Acct.Empty (a : Acct) : Prop :=
  a.code.size = 0 ∧ a.nonce = 0 ∧ a.bal = 0

instance {a : Acct} : Decidable a.Empty := by
 apply instDecidableAnd

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

def Rinst.run (evm : Evm) : Rinst → Execution
  | .address => pushItem evm.contract.toB256 gBase evm
  | .basefee => pushItem evm.env.base_fee_per_gas.toB256 gBase evm
  | .blobhash => do
    let ⟨x, evm⟩ ← evm.pop
    let y : B256 := evm.env.blob_versioned_hashes.getD x.toNat 0
    chargeGas gHashopcode evm >>= Evm.push y >>= Evm.incrPc
  | .blobbasefee => do
    let fee := get_base_fee_per_blob_gas evm.env.excess_blob_gas.toNat
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
    let value := evm.memory.sliceD data_start_index size 0
    Evm.incrPc <| evm.memWrite memory_start_index value
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
    let ⟨memory_start_index, evm⟩ ← evm.pop
    let ⟨return_data_start_index, evm⟩ ← evm.pop
    let ⟨size, evm⟩ ← evm.pop
    let words := ceilDiv size.toNat 32
    let copy_gas_cost := gReturnDataCopy * words
    let extend_memory_cost := evm.extCost [⟨memory_start_index, size⟩]
    let evm ← chargeGas (gVerylow + copy_gas_cost + extend_memory_cost) evm
    .guard
      ⟨evm, .exHalt .outOfBoundsRead⟩
      (evm.return_data.length < return_data_start_index.toNat + size.toNat)
    let value :=
      evm.return_data.sliceD return_data_start_index.toNat size.toNat 0
    .ok {
      evm with
      pc := evm.pc + 1
      memory := evm.memory.write memory_start_index.toNat value
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
  | .msize => pushItem (evm.memory.size * 32).toB256 gBase evm
  | .mload => do
    let ⟨start_index, evm⟩ ← evm.pop
    let extend_memory_cost := evm.extCost [⟨start_index, 32⟩]
    let evm ← chargeGas (gVerylow + extend_memory_cost) evm
    let value := B8L.toB256P <| evm.memory.sliceD start_index.toNat 32 0
    evm.push value >>= Evm.incrPc
  | .mstore => do
    let ⟨start_index, evm⟩ ← evm.pop
    let ⟨value, evm⟩ ← evm.pop
    let extend_memory_cost := evm.extCost [⟨start_index, 32⟩]
    let evm ← chargeGas (gVerylow + extend_memory_cost) evm
    Evm.incrPc <| evm.memWrite start_index.toNat value.toB8L
  | .mstore8 => do
    let ⟨start_index, evm⟩ ← evm.pop
    let ⟨value, evm⟩ ← evm.pop
    let extend_memory_cost := evm.extCost [⟨start_index, 1⟩]
    let evm ← chargeGas (gVerylow + extend_memory_cost) evm
    Evm.incrPc <| evm.memWrite start_index.toNat [value.2.2.toUInt8]
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
    let ⟨memory_start_index, evm⟩ ← evm.pop
    let ⟨size, evm⟩ ← evm.pop
    let words := ceilDiv size.toNat 32
    let word_gas_cost := gKeccak256Word * words
    let extend_memory_cost := evm.extCost [⟨memory_start_index, size⟩]
    let evm ← chargeGas (gKeccak256 + word_gas_cost + extend_memory_cost) evm
    let hash := B8a.keccak memory_start_index.toNat size.toNat evm.memory
    evm.push hash >>= Evm.incrPc
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
    | none => .error ⟨evm, .exHalt .stackUnderflowError⟩
    | some stack =>
      .ok {
        evm with
        pc := evm.pc + 1
        stack := stack
      }
  | .dup n => do
    let evm ← chargeGas gVerylow evm
    match evm.stack.get? n with
    | none => .error ⟨evm, .exHalt .stackUnderflowError⟩
    | some word => evm.push word >>= Evm.incrPc
  | .sload => do
    let ⟨key, evm⟩ ← evm.pop
    let ct := evm.contract
    let evm ←
      if ⟨ct, key⟩ ∈ evm.accessed_storage_keys
      then chargeGas GAS_WARM_ACCESS evm
      else
        chargeGas gColdAccountAccess
          (add_accessed_storage_key evm ct key)
    evm.push (evm.storValAt ct key) >>= Evm.incrPc
  | .tload => do
    let ⟨key, evm⟩ ← evm.pop
    pushItem (evm.getTransVal evm.contract key) GAS_WARM_ACCESS evm
  | .pc => pushItem evm.pc.toB256 gBase evm
  | .sstore => do
    let ⟨key, evm⟩ ← evm.pop
    let ⟨new_value, evm⟩ ← evm.pop
    .guard ⟨evm, .oog⟩ (gCallStipend < evm.gas_left)
    let ct := evm.contract
    let original_value := evm.origStorValAt ct key
    let current_value := evm.storValAt ct key

    let access_cost :=
      if ⟨ct, key⟩ ∈ evm.accessed_storage_keys
      then 0
      else GAS_COLD_SLOAD

    let update_cost :=
      if original_value = current_value ∧ current_value ≠ new_value
      then
        if original_value = 0
        then GAS_STORAGE_SET
        else GAS_STORAGE_UPDATE - GAS_COLD_SLOAD
      else GAS_WARM_ACCESS

    let gas_cost := access_cost + update_cost

    let evm : Evm :=
      if ⟨ct, key⟩ ∈ evm.accessed_storage_keys
      then evm
      else add_accessed_storage_key evm ct key

    let rc := evm.refund_counter
    let rc :=
      if current_value ≠ new_value
      then
        let rc :=
          if original_value ≠ 0 ∧ current_value ≠ 0 ∧ new_value = 0
          then rc + rSClear
          else rc
        let rc :=
          if original_value ≠ 0 ∧ current_value = 0
          then rc - rSClear
          else rc
        if original_value = new_value
        then
          if original_value = 0
          then rc + GAS_STORAGE_SET - GAS_WARM_ACCESS
          else rc + GAS_STORAGE_UPDATE - GAS_COLD_SLOAD - GAS_WARM_ACCESS
        else rc
      else rc

    let evm := {evm with refund_counter := rc}
    let evm ← chargeGas gas_cost evm

    .guard ⟨evm, .exHalt .writeInStaticContext⟩ !evm.message.is_static
    (evm.setStorVal evm.contract key new_value).incrPc
  | .tstore => do
    let ⟨key, evm⟩ ← evm.pop
    let ⟨new_value, evm⟩ ← evm.pop
    let evm ← chargeGas GAS_WARM_ACCESS evm
    .guard ⟨evm, .exHalt .writeInStaticContext⟩ !evm.message.is_static
    (evm.setTransVal evm.contract key new_value).incrPc
  | .mcopy => do
    let ⟨destination, evm⟩ ← evm.pop
    let ⟨source, evm⟩ ← evm.pop
    let ⟨length, evm⟩ ← evm.pop
    let words := ceilDiv length.toNat 32
    let copy_gas_cost := GAS_COPY * words
    let extend_memory_cost :=
      evm.extCost [⟨source, length⟩, ⟨destination, length⟩]
    let evm ← chargeGas (gVerylow + copy_gas_cost + extend_memory_cost) evm
    let value := evm.memory.sliceD source.toNat length.toNat 0
    (evm.memWrite destination.toNat value).incrPc
  | .log n => do
    let ⟨memory_start_index, evm⟩ ← evm.pop
    let ⟨size, evm⟩ ← evm.pop
    let ⟨topics, evm⟩ ← evm.popN n
    let extend_memory_cost := evm.extCost [⟨memory_start_index, size⟩]
    let evm ←
      chargeGas
        (
          gLog + (gLogdata * size.toNat) +
          (gLogtopic * n) + extend_memory_cost
        )
        evm
    .guard ⟨evm, .exHalt .writeInStaticContext⟩ !evm.message.is_static
    let data : B8L := evm.memory.sliceD memory_start_index.toNat size.toNat 0
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
    .guard ⟨evm, .exHalt .invalidJumpDestError⟩ (jumpable evm.code jump_dest.toNat)
    .ok {evm with pc := jump_dest.toNat}
  | .jumpi => do
    let ⟨dest, evm⟩ ← evm.pop
    let ⟨cond, evm⟩ ← evm.pop
    let evm ← chargeGas gHigh evm
    let pc ←
      if cond = 0
      then .ok <| evm.pc + 1
      else
        .guard ⟨evm, .exHalt .invalidJumpDestError⟩ (jumpable evm.code dest.toNat)
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
  Except (Evm × EthEx) Evm := do
  match evm.env.subBal adr val with
  | none => .error ⟨evm, .gen .assertionError⟩
  | some env => .ok {evm with env := env}

def Evm.setBal (evm : Evm) (adr : Adr) (val : B256) : Evm :=
  {evm with env := evm.env.setBal adr val}

def Evm.addBal (evm : Evm) (adr : Adr) (val : B256) : Evm :=
  {evm with env := evm.env.addBal adr val}

def Linst.run (evm : Evm) : Linst → Execution
  | .stop => .ok {evm with running := false, pc := evm.pc + 1}
  | .rev => do
    let ⟨memory_start_index, evm⟩ ← evm.pop
    let ⟨size, evm⟩ ← evm.pop
    let extend_memory_cost := evm.extCost [⟨memory_start_index, size⟩]
    let evm ← chargeGas extend_memory_cost evm
    let output := evm.memory.sliceD memory_start_index.toNat size.toNat 0
    let evm := {evm with output := output}
    .error ⟨evm, .revert⟩
  | .ret => do
    let ⟨index, evm⟩ ← evm.pop
    let ⟨size, evm⟩ ← evm.pop
    let cost := evm.extCost [⟨index, size⟩]
    let evm ← chargeGas cost evm
    let ⟨output, evm⟩ := evm.memRead index.toNat size.toNat
    .ok {evm with running := false, output := output}
  | .dest => do
    let ⟨donee, evm⟩ ← evm.pop <&> Prod.mapFst B256.toAdr
    let donor := evm.contract
    let donorBal := (evm.getAcct evm.contract).bal

    let accessCost :=
      if donee ∈ evm.accessed_addresses
      then 0
      else gColdAccountAccess

    let creationCost :=
      if (evm.getAcct donee).Empty ∧ donorBal ≠ 0
      then 0
      else GAS_SELF_DESTRUCT_NEW_ACCOUNT

    let cost := gSelfdestruct + accessCost + creationCost

    let evm ← chargeGas cost <| add_accessed_address evm donee
    .guard ⟨evm, .exHalt .writeInStaticContext⟩ !evm.message.is_static

    let evm ← evm.subBal donor donorBal
    let evm := evm.addBal donee donorBal

    let evm :=
      if donor ∈ evm.env.created_accounts
      then add_account_to_delete (evm.setBal donor 0) donor
      else evm

    let evm :=
      if (evm.getAcct donee).Empty
      then add_touched_account evm donee
      else evm

    .ok {evm with running := false}

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

mutual

  def generic_call
      (evm: Evm)
      (gas: Nat)
      (value: B256)
      (caller: Adr)
      (callee: Adr)
      (code_address: Adr)
      (should_transfer_value: Bool)
      (is_staticcall: Bool)
      (input_index: B256)
      (input_size: B256)
      (output_index: B256)
      (output_size: B256) : Execution := sorry

  def Ninst'.run (evm : Evm) : Ninst' → Execution
    | .push x len => do
      let evm ← chargeGas (if len = 0 then gBase else gVerylow) evm
      let evm ← evm.push x
      .ok {evm with pc := evm.pc + len + 1}
    | .reg r => r.run evm
    | .exec .create => _
    | .exec .create2 => _
    | .exec .call => do
      let ⟨gas, evm⟩ ← evm.pop
      let ⟨callee, evm⟩ ← evm.pop <&> Prod.mapFst B256.toAdr
      let ⟨value, evm⟩ ← evm.pop
      let ⟨input_index, evm⟩ ← evm.pop
      let ⟨input_size, evm⟩ ← evm.pop
      let ⟨output_index, evm⟩ ← evm.pop
      let ⟨output_size, evm⟩ ← evm.pop

      let extend_cost :=
        evm.extCost [⟨input_index, input_size⟩, ⟨output_index, output_size⟩]

      let access_cost := access_cost callee evm.accessed_addresses

      let evm := add_accessed_address evm callee

      let create_cost :=
        if (¬ (evm.getAcct callee).Empty) ∨ value = 0
        then 0
        else gNewAccount

      let transfer_cost :=
        if value = 0
        then 0
        else gCallValue

      let ⟨message_call_cost, message_call_stipend⟩ :=
        calculate_message_call_gas
          value.toNat
          gas.toNat
          evm.gas_left
          extend_cost
          (access_cost + create_cost + transfer_cost)

      let evm ← chargeGas (message_call_cost + extend_cost) evm

      .guard
        ⟨evm, .exHalt .writeInStaticContext⟩
        (!evm.message.is_static ∨ value = 0)

      let evm :=
        Evm.memExtend
          (evm.memExtend input_index.toNat input_size.toNat)
          output_index.toNat
          output_size.toNat

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

      evm.incrPc

    | .exec .callcode => _
    | .exec .delcall => _
    | .exec .statcall => _

  def exec : Nat → Evm → Execution
    | 0, evm =>
      dbg_trace "execution recursion limit reached (NOT execution depth limit)"
      .error ⟨evm, .oog⟩
    | lim + 1, evm => do
      -- showLim vb lim υ
      let i ← (evm.getInst).toExcept ⟨evm, .exHalt (.invalidOpcode (evm.code.get! evm.pc))⟩
      -- showStep vb σ υ κ i
      match i with
      | .next n => n.run evm >>= exec lim
      | .jump j => j.run evm >>= exec lim
      | .last l => l.run evm
end

#exit
def execute_code (message: Message) (env: Environment) :
  Except (Environment × EthEx) Evm := do
  let code := message.code
  let evm : Evm := {
    pc := 0
    stack := []
    memory := .mk []
    code := code
    gas_left := message.gas
    env := env -- env,
    -- valid_jump_destinations := _ -- valid_jump_destinations,
    logs := [] --
    refund_counter := 0 -- 0,
    running := .true -- True,
    message := message
    output := [] -- b"",
    accounts_to_delete := .empty -- set(),
    touched_accounts := .empty -- set(),
    return_data := [] -- b"",
    error := .none -- None,
    accessed_addresses := message.accessed_addresses
    accessed_storage_keys := message.accessed_storage_keys
  }

  let code_address := evm.message.code_address.getD 0

  let xr :=
    if code_address.isPrecomp
    then execute_precomp evm code_address.toNat--execPre vb ωp τ .init #[] υp κp c.toNat
    else execute evm -- exec vb lim ωp τ .init #[] υp κp

  match xr with
  | .error ⟨evm, ex⟩ =>
    if ex.exceptionalHalt
    then
      .ok {
        evm with
        gas_left := 0
        output := []
        error := ex
      }
    else
      if ex.revert
      then .ok {evm with error := ex}
      else .error ⟨evm.env, ex⟩
  | .ok evm => .ok evm

#exit
  _
    evm = Evm(
        pc=Uint(0),
        stack=[],
        memory=bytearray(),
        code=code,
        gas_left=message.gas,
        env=env,
        valid_jump_destinations=valid_jump_destinations,
        logs=(),
        refund_counter=0,
        running=True,
        message=message,
        output=b"",
        accounts_to_delete=set(),
        touched_accounts=set(),
        return_data=b"",
        error=None,
        accessed_addresses=message.accessed_addresses,
        accessed_storage_keys=message.accessed_storage_keys,
    )

-/
#exit

inductive PyMo (ξ υ : Type u) : Type u
  | pure : υ → PyMo ξ υ
  | raise : PyEx → PyMo ξ υ
  | return : ξ → PyMo ξ υ

def PyMo.bind {ξ υ ζ : Type u} : PyMo ξ υ → (υ → PyMo ξ ζ) → PyMo ξ ζ
  | .raise e, _ => .raise e
  | .return z, _ => .return z
  | .pure y, p => p y

instance {ξ} : Monad (PyMo ξ) where
  pure := .pure
  bind := .bind

def foo : Nat := do
  _

#exit
def PyMo.tryExAux {ξ υ} (p : PyMo ξ υ) (l : List ((PyEx → Bool) × (PyMo ξ υ))) : PyMo ξ υ :=

def PyMo.tryEx {ξ υ} (p : PyMo ξ υ) (l : List ((PyEx → Bool) × (PyMo ξ υ))) : PyMo ξ υ :=
  match p with
  | .pure x => .pure x

#exit


structure Acr where
  (dest : List Adr)  -- A_s
  (adrs : AdrSet)    -- A_a
  (keys : KeySet)     -- A_k
  (ref : Nat)         -- A_r
  (logs : List Log)  -- A_l
  (tchd : AdrSet) -- A_t
  (created : AdrSet)

-- A^0
def Acr.init : Acr :=
  {
    dest := []
    adrs := .ofList [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] -- precompiled contracts
    keys := .empty
    ref := 0
    logs := []
    tchd := .empty
    created := .empty
  }

instance : Inhabited Acr := ⟨.init⟩

structure Var where
  (gas : Nat) -- μ_g
  (pc : Nat)  -- μ_pc
  (ret : B8L) -- μ_o
  (act : Nat) -- μ_i
  (acr : Acr) -- μ_i
  -- -------------------------
  -- (dest : List Adr)  -- A_s
  -- (adrs : AdrSet)    -- A_a
  -- (keys : KeySet)     -- A_k
  -- (ref : Nat)         -- A_r
  -- (logs : List Log)  -- A_l
  -- (tchd : AdrSet) -- A_t


-- def Var.toAcs (υ : Var) : Acs :=
--   {
--     dest := υ.dest
--     adrs := υ.adrs
--     keys := υ.keys
--     ref := υ.ref
--     logs := υ.logs
--     tchd := υ.tchd
--   }

-- def Acs.toVar (A : Acs)
--   (gas : Nat := 0)
--   (pc : Nat := 0)
--   (ret : B8L := [])
--   (act : Nat := 0) : Var :=
--   {
--     gas := gas
--     pc := pc
--     ret := ret
--     act := act
--     dest := A.dest
--     adrs := A.adrs
--     keys := A.keys
--     ref := A.ref
--     logs := A.logs
--     tchd := A.tchd
--   }

-- μ_i : no need to make it a separate field of Machine,
-- when it is completely determined by Machine.mem
def Mem.msz (μ : Mem) : Nat := ceilDiv μ.size 32

structure BlockInfo where
  (blockHashes : List B256)
  (baseFee : B256) -- H_f
  (excessBlobGas : B256)
  (beneficiary : Adr) -- H_c
  (prevRandao : B256) -- H_a
  (gasLimit : B256) -- H_l
  (timestamp : B256) -- H_s
  (number : B256) -- H_s

  -- (chainId : B256) -- β

structure Con where
  (blk : BlockInfo) -- block (YP : H)
  (blobHashes : List B256) -- blog hashes
  (chainId : B256)
  (wor0 : Wor)

  (cta : Adr) -- contract address (YP : I_a)
  (oga : Adr) -- origin address (YP : I_o)
  (gpr : B256) -- gas price (YP : I_p)
  (cld : B8L) -- calldata (YP : I_d)
  (cla : Adr) -- caller Addr (YP : I_s)
  (clv : B256) -- callvalue (YP : I_v)
  (code : ByteArray) -- contract code  (YP : I_b)
  (exd : Nat) -- execution depth (YP : I_e)
  (wup : Bool) -- World-State update permission (YP : I_w)

-- YP says that this type should also have a field for
-- execution environment, but it was omitted since the
-- environment does not change and is already known.

structure ExecRes where
  (wor : Wor)
  (tra : Tra)
  (gas : Nat)
  (acs : Acr)
  (ret : B8L)
  (err : Bool)

instance : Inhabited ExecRes :=
  ⟨
    {
      wor := .empty
      tra := .empty
      gas := 0
      acs := Inhabited.default
      ret := []
      err := true
    }
  ⟩


-- structure ΞR where
--   (wt : Option (Wor × Tra))
--   (gas : Nat)
--   (acs : Acr)
--   (ret : Option B8L)

-- instance : Inhabited ΞR :=
--   ⟨
--     {
--       wt := .none
--       gas := 0
--       acs := Inhabited.default
--       ret := .none
--     }
--   ⟩

inductive Inst : Type
  | last : Linst → Inst
  | next : Ninst → Inst
  | jump : Jinst → Inst

lemma List.length_takeD {ξ : Type u} (n : Nat) (xs : List ξ) (x : ξ) :
    (List.takeD n xs x).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [takeD]

def Inst.toString : Inst → String
  | .next n => n.toString
  | .jump j => j.toString
  | .last l => l.toString


def getInstAux (cd : ByteArray) (pc len off : Nat) : B8 :=
  if off < len
  then cd.get! ((pc + len) - off)
  else 0

def getInst (υ : Var) (κ : Con)  : Option Inst' :=
  if υ.pc < κ.code.size
  then
    let b : B8 := κ.code.get! υ.pc
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
               (getInstAux κ.code υ.pc len 31)
               (getInstAux κ.code υ.pc len 30)
               (getInstAux κ.code υ.pc len 29)
               (getInstAux κ.code υ.pc len 28)
               (getInstAux κ.code υ.pc len 27)
               (getInstAux κ.code υ.pc len 26)
               (getInstAux κ.code υ.pc len 25)
               (getInstAux κ.code υ.pc len 24)
               (getInstAux κ.code υ.pc len 23)
               (getInstAux κ.code υ.pc len 22)
               (getInstAux κ.code υ.pc len 21)
               (getInstAux κ.code υ.pc len 20)
               (getInstAux κ.code υ.pc len 19)
               (getInstAux κ.code υ.pc len 18)
               (getInstAux κ.code υ.pc len 17)
               (getInstAux κ.code υ.pc len 16)
               (getInstAux κ.code υ.pc len 15)
               (getInstAux κ.code υ.pc len 14)
               (getInstAux κ.code υ.pc len 13)
               (getInstAux κ.code υ.pc len 12)
               (getInstAux κ.code υ.pc len 11)
               (getInstAux κ.code υ.pc len 10)
               (getInstAux κ.code υ.pc len  9)
               (getInstAux κ.code υ.pc len  8)
               (getInstAux κ.code υ.pc len  7)
               (getInstAux κ.code υ.pc len  6)
               (getInstAux κ.code υ.pc len  5)
               (getInstAux κ.code υ.pc len  4)
               (getInstAux κ.code υ.pc len  3)
               (getInstAux κ.code υ.pc len  2)
               (getInstAux κ.code υ.pc len  1)
               (getInstAux κ.code υ.pc len  0)
           some (.next <| .push x len)
      else -- dbg_trace s!"undefined opcode : {b}"
           none
    )
  else some (.last .stop)


-- abbrev Exmo (ξ : Type u) := Except ΞR ξ
abbrev Exmo (ξ : Type u) := Except ExecRes ξ


-- structure EVMS : Type
--
-- inductive Execution (ξ : Type u) : Type u
--   | halt : ΞR → Execution ξ
--   | cont : (EVMS → EVMS) → ξ → Execution ξ
--
-- #exit
--
-- #synth Monad Option
--
-- def Execution.pure {ξ : Type u} (x : ξ) : Execution ξ := .cont id x
-- def Execution.bind {α β : Type} : Execution α → (α → Execution β) → Execution β
--   | .halt xr, _ => .halt xr
--   | .cont f x, ex =>
--     match ex x with
--     | .halt xr => .halt xr
--     | .cont g y => .cont (g ∘ f) y
--
--
--
--
-- #exit
-- instance {ξ : Type u} : Monad Execution where
--   pure := .pure
--   bind := _
--
--
-- #exit
--
--
-- #exit

-- def xhs (υ : Var) : ExecRes :=
  -- {wt := none, gas := υ.gas, acs := υ.acr, ret := none}
def xhs (υ : Var) : ExecRes :=
  {wor := .empty, tra := .empty, gas := υ.gas, acs := υ.acr, ret := [], err := true}

-- def xhs0 (υ : Var) : ΞR :=
--   {wt := none, gas := 0, acs := υ.acr, ret := none}

def xhs0 (υ : Var) : ExecRes :=
  {wor := .empty, tra := .empty, gas := 0, acs := υ.acr, ret := [], err := true}


def deductGas (υ : Var) (c : Nat) : Exmo Nat :=
  -- according to revm, executions that end with 'out of gas` outcome
  -- should contribute 0 gas back to the parent execution.
  (safeSub υ.gas c).toExcept (xhs0 υ)

def chargeGas (υ : Var) (c : Nat) : Exmo Var := do
  let g ← deductGas υ c
  .ok {υ with gas := g}


def Acct.empty : Acct :=
  {
    nonce := 0
    bal := 0
    stor := .empty
    code := ByteArray.mk #[]
  }


def Wor.codeAt (w : Wor) (a : Adr) : ByteArray := (w.get a).code




def Wor.nonceAt (w : Wor) (a : Adr) : B256 := (w.get a).nonce
def Wor.balAt (w : Wor) (a : Adr) : B256 := (w.get a).bal
def Wor.storEntryAt (w : Wor) (a : Adr) (k : B256) : B256 := (w.get a).stor.findD k 0

def Wor.storIsEmptyAt (w : Wor) (a : Adr) : Bool := (w.get a).stor.isEmpty



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

def cExtra (ct : CallCostType) (ω : Wor) (υ : Var) (t : Adr) (v : B256) : Nat :=
  let cAcc : Nat := cAAccess t υ.acr.adrs
  let cNew : Nat :=
    if (Dead ω t ∧ v ≠ 0)
    then gNewAccount
    else 0
  let cXfer : Nat := if v ≠ 0 then gCallValue else 0
  match ct with
  | .all => cAcc + cXfer + cNew
  | .noCreate => cAcc + cXfer
  | .onlyAccess => cAcc

def cGasCap (ct : CallCostType) (ω : Wor) (υ : Var) (g : Nat)
    (mc : Nat) (t : Adr) (v : B256) : Nat :=
  let cx := cExtra ct ω υ t v
  if (mc + cx) ≤ υ.gas
  then min (except64th (υ.gas - (mc + cx))) g
  else g

def cCallGas (ct : CallCostType) (ω : Wor) (υ : Var)
   (g : Nat) (mc : Nat) (t : Adr) (v : B256) : Nat :=
  if v ≠ 0
  then cGasCap ct ω υ g mc t v + gCallStipend
  else cGasCap ct ω υ g mc t v

def cCall (ct : CallCostType) (ω : Wor) (υ : Var)
    (g : Nat) (mc : Nat) (t : Adr) (v : B256) : Nat :=
  let mainCost := cGasCap ct ω υ g mc t v
  let extraCost := cExtra ct ω υ t v
  mainCost + extraCost

structure ΛΘ.Result : Type where
  (wor : Wor)
  (tra : Tra)
  (gas : Nat)
  (acs : Acr)
  (status : Bool)
  (ret : B8L)

def Wor.code (w : Wor) (a : Adr) : ByteArray :=
  match w.find? a with
  | none => ByteArray.mk #[]
  | some x => x.code

def Sta.init : Sta := ⟨Array.mkArray 1024 (0 : B256), 0⟩

def dataGas (cd : B8L) : Nat :=
  let aux : B8 → Nat := fun b => if b = 0 then 4 else 16
  (cd.map aux).sum

def intrinsicGas (Rcv : Option Adr) (cd : B8L) (Ta : List (Adr × List B256)) : Nat :=
  let aux : (Adr × List B256) → Nat :=
    fun | ⟨_, l⟩ => gAccesslistaddress + (gAccessliststorage * l.length)
  let createCost : Nat := Rcv.rec (gTxcreate + initCodeCost cd) (fun _ => 0)
  let accessListCost : Nat := (Ta.map aux).sum
  gTransaction +
  dataGas cd +
  createCost +
  accessListCost

-- checkpoint is an 'Option' type because computation of checkpoints
-- may fail for invalid txs. this is *not* the case for any subsequent
-- steps of a tx: once you get to a checkpoint, the tx *always* goes
-- through and yields a new state. i.e., there is no invalid tx that
-- has a checkpoint.
def checkpoint (w : Wor) (ad : Adr) (v : B256) : Option Wor := do
  let ac ← w.find? ad
  let bal' ← safeSub ac.bal v
  some <| w.set ad {ac with bal := bal', nonce := ac.nonce + 1}





abbrev AccessList.collect (al : AccessList) : KeySet :=
  let addPair : Adr → KeySet → B256 → KeySet :=
    fun a aks k => aks.insert ⟨a, k⟩
  let addElem : KeySet → Adr × List B256 → KeySet :=
    fun aks pr => List.foldl (addPair pr.fst) aks pr.snd
  List.foldl addElem .empty al

def A_star (H : BlockInfo) (ST : Adr) (Tt : Option Adr) (TA : AccessList) : Acr :=
  let a : AdrSet :=
    Acr.init.adrs.insertMany
      (Std.HashSet.ofList (ST :: H.beneficiary:: TA.map Prod.fst))
  {
    Acr.init with
    adrs := Tt.rec a (a.insert)
    keys := TA.collect
  }



def Sta.pop1 : Sta → Option (B256 × Sta)
  | ⟨xs, n + 1⟩ => do
    let x ← xs.get? n
    some ⟨x, xs, n⟩
  | _ => none

def Sta.pop2 : Sta → Option (B256 × B256 × Sta)
  | ⟨xs, n + 2⟩ => do
    let x ← xs.get? (n + 1)
    let y ← xs.get? n
    some ⟨x, y, xs, n⟩
  | _ => none

def Sta.pop3 : Sta → Option (B256 × B256 × B256 × Sta)
  | ⟨xs, n + 3⟩ => do
    let x ← xs.get? (n + 2)
    let y ← xs.get? (n + 1)
    let z ← xs.get? n
    some ⟨x, y, z, xs, n⟩
  | _ => none

def Sta.pop4 : Sta → Option (B256 × B256 × B256 × B256 × Sta)
  | ⟨xs, n + 4⟩ => do
    let a ← xs.get? (n + 3)
    let b ← xs.get? (n + 2)
    let c ← xs.get? (n + 1)
    let d ← xs.get? n
    some ⟨a, b, c, d, xs, n⟩
  | _ => none

def Sta.pop5 : Sta → Option (B256 × B256 × B256 × B256 × B256 × Sta)
  | ⟨xs, n + 5⟩ => do
    let a ← xs.get? (n + 4)
    let b ← xs.get? (n + 3)
    let c ← xs.get? (n + 2)
    let d ← xs.get? (n + 1)
    let e ← xs.get? n
    some ⟨a, b, c, d, e, xs, n⟩
  | _ => none

def Sta.pop6 : Sta → Option (B256 × B256 × B256 × B256 × B256 × B256 × Sta)
  | ⟨xs, n + 6⟩ => do
    let a ← xs.get? (n + 5)
    let b ← xs.get? (n + 4)
    let c ← xs.get? (n + 3)
    let d ← xs.get? (n + 2)
    let e ← xs.get? (n + 1)
    let f ← xs.get? n
    some ⟨a, b, c, d, e, f, xs, n⟩
  | _ => none

def Sta.pop7 : Sta → Option (B256 × B256 × B256 × B256 × B256 × B256 × B256 × Sta)
  | ⟨xs, n + 7⟩ => do
    let a ← xs.get? (n + 6)
    let b ← xs.get? (n + 5)
    let c ← xs.get? (n + 4)
    let d ← xs.get? (n + 3)
    let e ← xs.get? (n + 2)
    let f ← xs.get? (n + 1)
    let g ← xs.get? n
    some ⟨a, b, c, d, e, f, g, xs, n⟩
  | _ => none

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

def Sta.popN (σ : Sta) : Nat → Option (List B256 × Sta)
  | 0 => some ⟨[], σ⟩
  | n + 1 => do
    let (x, σ') ← σ.pop1
    let (xs, σ'') ← σ'.popN n
    some ⟨x :: xs, σ''⟩

def Option.toExmo {ξ : Type u} (υ : Var) : Option ξ → Exmo ξ
  | none => .error <| xhs υ
  | some x => .ok x

def KeySet.toStrings (ks : KeySet) : List String :=
  let f : (Adr × B256) → List String :=
    fun | ⟨a, x⟩ => [s!"{a.toHex} : {x.toHex}"]
  fork "KeySet" <| ks.toList.map f

instance : ToString KeySet := ⟨λ ks => String.joinln <| ks.toStrings⟩

def sstoreStep (ω : Wor) (σ : Sta) (υ : Var) (κ : Con) :
    Exmo (Wor × Sta × Var) := do
  Except.guard (xhs0 υ) (κ.wup ∧ gCallStipend < υ.gas)
  let (x, v', σ') ← σ.pop2.toExcept (xhs υ)
  let (a₀ : Acct) := (κ.wor0.find? κ.cta).getD Acct.empty
  let (v₀ : B256) := ((a₀.stor.find? x).getD 0)
  let (a : Acct) := (ω.find? κ.cta).getD Acct.empty
  let (v : B256) := ((a.stor.find? x).getD 0)

  -- v₀ : orig value at beginning of tx
  -- v : current value
  -- v' : new value

  let c₀ : Nat := cond (υ.acr.keys.contains ⟨κ.cta, x⟩) 0 GAS_COLD_SLOAD
  let c₁ : Nat :=
    if v = v' ∨ v₀ ≠ v
    then GAS_WARM_ACCESS
    else if v₀ = 0
         then GAS_STORAGE_SET
         else gSReset

  let c : Nat := c₀ + c₁

  let rDirtyClear : Int :=
    if v₀ ≠ 0 ∧ v = 0
    then (- rSClear)
    else if v₀ ≠ 0 ∧ v' = 0
         then rSClear
         else 0
  let rDirtyReset : Int :=
    if v₀ = v'
    then if v₀ = 0
         then GAS_STORAGE_SET - GAS_WARM_ACCESS
         else gSReset - GAS_WARM_ACCESS
    else 0
  let r : Int :=
    if v = v'
    then 0
    else if v₀ = v
         then if v' = 0
              then rSClear
              else 0
         else rDirtyClear + rDirtyReset
  let g' ← deductGas υ c
  let ref' :=
    match (Int.ofNat υ.acr.ref + r) with
    | .ofNat noo => noo
    | _ => panic! "negative refund"
  let a' : Acct := {a with stor := a.stor.set x v'}

  .ok
    ⟨
      ω.set κ.cta a',
      σ',
      {
        υ with
        gas := g'
        pc := υ.pc + 1
        acr :=
          {
            υ.acr with
            keys := υ.acr.keys.insert ⟨κ.cta, x⟩
            ref := ref'
          }
      }
    ⟩

def tstoreStep (τ : Tra) (σ : Sta) (υ : Var) (κ : Con) :
  Exmo (Tra × Sta × Var) := do
  Except.guard (xhs0 υ) (κ.wup)
  let (x, v', σ') ← σ.pop2.toExcept (xhs υ)
  let s : Stor := (τ.find? κ.cta).getD .empty
  let s' : Stor := s.set x v'
  let g' ← deductGas υ 100
  .ok
    ⟨
      τ.set κ.cta s',
      σ', --σ',
      {υ with gas := g', pc := υ.pc + 1}
    ⟩


def memExp (s : Nat) (f l : B256) : Nat :=
  if l = 0
  then s
  else max s (ceilDiv (f.toNat + l.toNat) 32)

def nextVar (υ : Var) (cost : Nat)
  (act' : Option Nat := none)
  (ret' : B8L := υ.ret)
  (adrs' : AdrSet := υ.acr.adrs)
  (logs' : List Log := υ.acr.logs)
  (keys' : KeySet := υ.acr.keys) : Exmo Var := do
  let gas' ←
    match act' with
    | none => deductGas υ cost
    | some k => deductGas υ (cost + (cMem k - cMem υ.act))
  .ok {
      gas := gas',
      pc := υ.pc + 1,
      ret := ret'
      act := act'.getD υ.act
      acr :=
        {
          υ.acr with
          adrs := adrs'
          keys := keys'
          logs := logs'
        }
    }


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

def pushItem (ω : Wor) (τ : Tra) (σ : Sta) (μ : Mem) (υ : Var) (x : B256) (c : Nat) :
    Exmo (Wor × Tra × Sta × Mem × Var) := do
  let σ' ← (σ.push1 x).toExcept (xhs0 υ)
  let υ' ← nextVar υ c
  .ok ⟨ω, τ, σ', μ, υ'⟩

def checkRemGas (υ : Var) (cost : Nat) (act' : Nat) : Exmo Unit := do
  let mc : Nat := cMem act' - cMem υ.act
  let _ ← deductGas υ (cost + mc)
  return ()

def applyUnary (ω : Wor) (τ : Tra) (σ : Sta) (μ : Mem) (υ : Var)
  (f : B256 → B256) (cost : Nat) : Exmo (Wor × Tra × Sta × Mem × Var) := do
  let (x, σ') ← σ.pop1.toExmo υ
  let σ'' ← (σ'.push1 (f x)).toExmo υ
  let υ' ← nextVar υ cost
  .ok ⟨ω, τ, σ'', μ, υ'⟩

def applyBinary (ω : Wor) (τ : Tra) (σ : Sta) (μ : Mem) (υ : Var)
  (f : B256 → B256 → B256) (cost : Nat) : Exmo (Wor × Tra × Sta × Mem × Var) := do
  let (x, y, σ') ← σ.pop2.toExmo υ
  let σ'' ← (σ'.push1 (f x y)).toExmo υ
  let υ' ← nextVar υ cost
  .ok ⟨ω, τ, σ'', μ, υ'⟩

def applyTernary (ω : Wor) (τ : Tra) (σ : Sta) (μ : Mem) (υ : Var)
  (f : B256 → B256 → B256 → B256) (cost : Nat) : Exmo (Wor × Tra × Sta × Mem × Var) := do
  let (x, y, z, σ') ← σ.pop3.toExmo υ
  let σ'' ← (σ'.push1 (f x y z)).toExmo υ
  let υ' ← nextVar υ cost
  .ok ⟨ω, τ, σ'', μ, υ'⟩







def Rinst.run (ω : Wor) (τ : Tra) (σ : Sta) (μ : Mem) (υ : Var) (κ : Con) :
    Rinst → Exmo (Wor × Tra × Sta × Mem × Var)
  | .address => pushItem ω τ σ μ υ κ.cta.toB256 gBase
  | .basefee => pushItem ω τ σ μ υ κ.blk.baseFee gBase
  | .blobhash => do
    let (x, σ') ← (σ.pop1).toExmo υ
    let y : B256 := κ.blobHashes.getD x.toNat 0
    let σ'' ← (σ'.push1 y).toExmo υ
    let υ' ← nextVar υ gHashopcode
    .ok ⟨ω, τ, σ'', μ, υ'⟩
  | .blobbasefee => do
    let fee := get_base_fee_per_blob_gas κ.blk.excessBlobGas.toNat
    pushItem ω τ σ μ υ fee.toB256 gBase
  | .balance => do
    let (x, σ') ← σ.pop1.toExmo υ
    let a := x.toAdr
    let adrs' : AdrSet := υ.acr.adrs.insert a
    let σ'' ← (σ'.push1 (ω.get a).bal).toExmo υ
    let υ' ← nextVar υ (cAAccess a υ.acr.adrs) (adrs' := adrs')
    .ok ⟨ω, τ, σ'', μ, υ'⟩
  | .origin => pushItem ω τ σ μ υ κ.oga.toB256 gBase
  | .caller => pushItem ω τ σ μ υ κ.cla.toB256 gBase
  | .callvalue => pushItem ω τ σ μ υ κ.clv gBase
  | .calldataload => do
    let (x, σ') ← (σ.pop1).toExmo υ
    let cd :=
      match B8L.toB256? (κ.cld.sliceD x.toNat 32 0) with
      | some cd => cd
      | _ => panic! "error : slice length should be 32"
    let σ'' ← (σ'.push1 cd).toExmo υ
    let υ' ← nextVar υ gVerylow
    .ok ⟨ω, τ, σ'', μ, υ'⟩
  | .calldatasize => pushItem ω τ σ μ υ κ.cld.length.toB256 gBase
  | .calldatacopy => do
    let (x, y, z, σ') ← (σ.pop3).toExmo υ
    let bs : B8L := κ.cld.sliceD y.toNat z.toNat 0
    let υ' ←
      nextVar υ
        (gVerylow + (GAS_COPY * ceilDiv z.toNat 32))
        (act' := memExp υ.act x z)
    .ok ⟨ω, τ, σ', μ.write x.toNat bs, υ'⟩
  | .codesize => pushItem ω τ σ μ υ κ.code.size.toB256 gBase
  | .codecopy => do
    let (x, y, z, σ') ← (σ.pop3).toExmo υ
    let cost := gVerylow + (GAS_COPY * ceilDiv z.toNat 32)
    let υ' ← nextVar υ cost (act' := memExp υ.act x z)
    let bs := κ.code.sliceD y.toNat z.toNat (Linst.toB8 .stop)
    .ok ⟨ω, τ, σ', μ.write x.toNat bs, υ'⟩
  | .gasprice => pushItem ω τ σ μ υ κ.gpr gBase
  | .extcodesize => do
    let (x, σ') ← (σ.pop1).toExmo υ
    let a := x.toAdr
    let adrs' : AdrSet := υ.acr.adrs.insert a
    let σ'' ← (σ'.push1 (ω.get a).code.size.toB256).toExmo υ
    let υ' ← nextVar υ (cAAccess a υ.acr.adrs) (adrs' := adrs')
    .ok ⟨ω, τ, σ'', μ, υ'⟩
  | .extcodecopy => do
    let (x, y, z, w, σ') ← (σ.pop4).toExmo υ
    let a := x.toAdr
    let cost := cAAccess x.toAdr υ.acr.adrs + (GAS_COPY * ceilDiv w.toNat 32)
    let adrs' : AdrSet := υ.acr.adrs.insert a
    let υ' ← nextVar υ cost (act' := memExp υ.act y w) (adrs' := adrs')
    let cd : ByteArray := (ω.get a).code
    let bs := cd.sliceD z.toNat w.toNat (Linst.toB8 .stop)
    .ok ⟨ω, τ, σ', .write μ y.toNat bs, υ'⟩
  | .retdatasize =>
    pushItem ω τ σ μ υ υ.ret.length.toB256 gBase
  | .retdatacopy => do
    let (x, y, z, σ') ← (σ.pop3).toExmo υ
    let act' := memExp υ.act x z
    let υ' ← nextVar υ (gVerylow + (GAS_COPY * (ceilDiv z.toNat 32))) (act' := act')
    let bs ← (υ.ret.slice? y.toNat z.toNat).toExmo υ
    .ok ⟨ω, τ, σ', .write μ x.toNat bs, υ'⟩
  | .extcodehash => do
    let (x, σ') ← (σ.pop1).toExmo υ
    let a := x.toAdr
    let adrs' := υ.acr.adrs.insert a
    let υ' ← nextVar υ (cAAccess a υ.acr.adrs) (adrs' := adrs')
    let hash : B256 :=
      if (Dead ω a)
      then 0
      else let cd := (ω.get a).code
           ByteArray.keccak 0 cd.size cd
    let σ'' ← (σ'.push1 hash).toExmo υ
    .ok ⟨ω, τ, σ'', μ, υ'⟩
  | .selfbalance => pushItem ω τ σ μ υ (ω.get κ.cta).bal gLow
  | .chainid => pushItem ω τ σ μ υ κ.chainId gBase
  | .number => pushItem ω τ σ μ υ κ.blk.number gBase
  | .timestamp => pushItem ω τ σ μ υ κ.blk.timestamp gBase
  | .gaslimit => pushItem ω τ σ μ υ κ.blk.gasLimit gBase
  | .prevrandao => pushItem ω τ σ μ υ κ.blk.prevRandao gBase
  | .coinbase => pushItem ω τ σ μ υ κ.blk.beneficiary.toB256 gBase
  | .msize => pushItem ω τ σ μ υ (υ.act * 32).toB256 gBase
  | .mload => do
    let (x, σ') ← (σ.pop1).toExmo υ
    let act' := memExp υ.act x (32 : Nat).toB256
    let υ' ← nextVar υ gVerylow (act' := act')
    let bs : B8L := μ.sliceD x.toNat 32 0
    let y : B256 :=
      match B8L.toB256? bs with
      | .some y => y
      | .none => panic! "error : byte slice should always be correct size (32)"
    let σ'' ← (σ'.push1 y).toExmo υ
    .ok ⟨ω, τ, σ'', μ, υ'⟩
  | .mstore => do
    let (x, y, σ') ← (σ.pop2).toExmo υ
    let act' := memExp υ.act x (32 : Nat).toB256
    let υ' ← nextVar υ gVerylow (act' := act')
    .ok ⟨ω, τ, σ', .write μ x.toNat y.toB8L, υ'⟩
  | .mstore8 => do
    let (x, y, σ') ← (σ.pop2).toExmo υ
    let act' := memExp υ.act x 1
    let υ' ← nextVar υ gVerylow (act' := act')
    .ok ⟨ω, τ, σ', .write μ x.toNat [y.2.2.toUInt8], υ'⟩
  | .gas => pushItem ω τ σ μ υ (υ.gas - gBase).toB256 gBase
  | .eq => applyBinary ω τ σ μ υ .eq_check gVerylow
  | .lt => applyBinary ω τ σ μ υ .lt_check gVerylow
  | .gt => applyBinary ω τ σ μ υ .gt_check gVerylow
  | .slt => applyBinary ω τ σ μ υ .slt_check gVerylow
  | .sgt => applyBinary ω τ σ μ υ .sgt_check gVerylow
  | .iszero => applyUnary ω τ σ μ υ (.eq_check · 0) gVerylow
  | .not => applyUnary ω τ σ μ υ (~~~ ·) gVerylow
  | .and => applyBinary ω τ σ μ υ B256.and gVerylow
  | .or => applyBinary ω τ σ μ υ B256.or gVerylow
  | .xor => applyBinary ω τ σ μ υ B256.xor gVerylow
  | .signextend => applyBinary ω τ σ μ υ B256.signext gLow
  | .pop => do
    let (_, σ') ← (σ.pop1).toExmo υ
    let υ' ← nextVar υ gBase
    .ok ⟨ω, τ, σ', μ, υ'⟩
  | .byte =>
    applyBinary ω τ σ μ υ (λ x y => (List.getD y.toB8L x.toNat 0).toB256) gVerylow
  | .shl => applyBinary ω τ σ μ υ (fun x y => y <<< x.toNat) gVerylow
  | .shr => applyBinary ω τ σ μ υ (fun x y => y >>> x.toNat) gVerylow
  | .sar => applyBinary ω τ σ μ υ (fun x y => B256.sar x.toNat y) gVerylow
  | .kec => do
    let (x, y, σ') ← (σ.pop2).toExmo υ
    let act' := memExp υ.act x y
    let cost := gKeccak256 + (gKeccak256Word * (ceilDiv y.toNat 32))
    let υ' ← nextVar υ cost (act' := act')
    let σ'' ← (σ'.push1 <| B8a.keccak x.toNat y.toNat μ).toExmo υ
    .ok ⟨ω, τ, σ'', μ, υ'⟩
  | .sub => applyBinary ω τ σ μ υ (· - ·) gVerylow
  | .mul => applyBinary ω τ σ μ υ (· * ·) gLow
  | .exp => do
    let (x, y, σ') ← (σ.pop2).toExmo υ
    let cost := gExp + (gExpbyte * y.bytecount)
    let σ'' ← (σ'.push1 (B256.bexp x y)).toExmo υ
    let υ' ← nextVar υ cost
    .ok ⟨ω, τ, σ'', μ, υ'⟩
  | .div => applyBinary ω τ σ μ υ (· / ·) gLow
  | .sdiv => applyBinary ω τ σ μ υ B256.sdiv gLow
  | .mod => applyBinary ω τ σ μ υ (· % ·) gLow
  | .smod => applyBinary ω τ σ μ υ B256.smod gLow
  | .add => applyBinary ω τ σ μ υ (· + ·) gVerylow
  | .addmod => applyTernary ω τ σ μ υ B256.addmod gMid
  | .mulmod => applyTernary ω τ σ μ υ B256.mulmod gMid
  | .swap n => do
    let σ' ← (σ.swap n).toExmo υ
    let υ' ← nextVar υ gVerylow
    .ok ⟨ω, τ, σ', μ, υ'⟩
  | .dup n => do
    let σ' ← (σ.dup n).toExmo υ
    let υ' ← nextVar υ gVerylow
    .ok ⟨ω, τ, σ', μ, υ'⟩
  | .sload => do
    let (x, σ') ← (σ.pop1).toExmo υ
    let cost : Nat := if υ.acr.keys.contains ⟨κ.cta, x⟩ then GAS_WARM_ACCESS else GAS_COLD_SLOAD
    let ac := ω.findD κ.cta Acct.empty
    let y := (ac.stor.find? x).getD 0
    let σ'' ← (σ'.push1 y).toExmo υ
    let υ' ← nextVar υ cost (keys' := υ.acr.keys.insert ⟨κ.cta, x⟩)
    .ok ⟨ω, τ, σ'', μ, υ'⟩
  | .tload => do
    let (x, σ') ← (σ.pop1).toExmo υ
    let cost : Nat := 100 --if υ.acr.keys.contains ⟨κ.cta, x⟩ then GAS_WARM_ACCESS else GAS_COLD_SLOAD
    let s := τ.findD κ.cta .empty
    let y := (s.find? x).getD 0
    let σ'' ← (σ'.push1 y).toExmo υ
    let υ' ← nextVar υ cost
    .ok ⟨ω, τ, σ'', μ, υ'⟩
  | .sstore => do
    let ⟨ω', σ', υ'⟩ ← sstoreStep ω σ υ κ --α ε
    .ok ⟨ω', τ, σ', μ, υ'⟩
  | .tstore => do
    let ⟨τ', σ', υ'⟩ ← tstoreStep τ σ υ κ --α ε
    .ok ⟨ω, τ', σ', μ, υ'⟩
  | .mcopy => do
    let (x, y, z, σ') ← (σ.pop3).toExmo υ
    let act' : Nat := memExp (memExp υ.act x z) y z
    let υ' ←
      nextVar υ
        (gVerylow + (GAS_COPY * ceilDiv z.toNat 32))
        (act' := act')
    let bs : B8L := μ.sliceD y.toNat z.toNat 0
    .ok ⟨ω, τ, σ', .write μ x.toNat bs, υ'⟩
  | .pc => pushItem ω τ σ μ υ υ.pc.toB256 gBase
  | .log n => do
    Except.guard (xhs0 υ) κ.wup
    let ⟨x :: y :: xs, σ'⟩ ←
      (σ.popN (n + 2)).toExmo υ | (panic! "error : popN should return 2 or more items")
    let act' := memExp υ.act x y
    let cost := gLog + (gLogdata * y.toNat) + (n * gLogtopic)
    checkRemGas υ cost act'
    let bs : B8L := μ.sliceD x.toNat y.toNat 0
    let log : Log := ⟨κ.cta,  xs, bs⟩
    let υ' ← nextVar υ cost (act' := act') (logs' := log :: υ.acr.logs)
    .ok ⟨ω, τ, σ', μ, υ'⟩
  | .blockhash => do
    let (x, σ') ← (σ.pop1).toExmo υ
    let bn := κ.blk.number
    let h : B256 :=
      if bn ≤ x
      then 0
      else let d := bn - (x + 1)
           if 255 < d
           then 0
           else List.getD κ.blk.blockHashes d.toNat 0
    let σ'' ← (σ'.push1 h).toExmo υ
    let υ' ← nextVar υ gBlockhash
    .ok ⟨ω, τ, σ'', μ, υ'⟩



-- w₀ : the 'checkpoint' world saved at the preparation stage of tx

-- The intended behavior of 'execCore' is identical to the 'X' function of YP,
-- except that it returns 'none' if
--   (1) the VM is *CURRENTLY* (i.e, not at some later point in code) at
--       exceptional halting state due to the code byte that the program counter
--       points to, or
--   (2) recursion limit is reached (which should never happen with correct usage)


def Wor.subBal (w : Wor) (a : Adr) (v : B256) : Wor :=
  let ac := w.get a
  let ac' : Acct := {ac with bal := ac.bal - v}
  w.set a ac'

def Wor.addBal (w : Wor) (a : Adr) (v : B256) : Wor :=
  let ac := w.get a
  let ac' : Acct := {ac with bal := ac.bal + v}
  w.set a ac'

def Wor.setBal (w : Wor) (a : Adr) (v : B256) : Wor :=
  let ac := w.get a
  let ac' : Acct := {ac with bal := v}
  w.set a ac'

def Wor.setStor (w : Wor) (a : Adr) (s : Stor) : Wor :=
  let ac := (w.get a)
  w.set a {ac with stor := s}

def Wor.setStorEntry (w : Wor) (a : Adr) (k v : B256) : Wor :=
  let ac := (w.get a)
  let st := ac.stor
  let s' : Stor := st.insert k v
  let ac' : Acct := {ac with stor := s'}
  w.set a ac'

def Wor.incrNonce (w : Wor) (a : Adr) : Wor :=
  let ac := w.get a
  let ac' : Acct := {ac with nonce := ac.nonce + 1}
  w.set a ac'

def Jinst.run (σ : Sta) (υ : Var) (κ : Con) :
    Jinst → Exmo (Sta × Var)
  | .jumpdest => do
    let g' ← deductGas υ gJumpdest
    .ok ⟨σ, {υ with gas := g', pc := υ.pc + 1}⟩
  | .jump => do
    let (loc, σ') ← (σ.pop1).toExmo υ
    let g' ← deductGas υ gMid
    Except.guard (xhs υ) (jumpable κ.code loc.toNat)
    .ok ⟨σ', {υ with gas := g', pc := loc.toNat}⟩
  | .jumpi => do
    let (loc, val, σ') ← (σ.pop2).toExmo υ
    let g' ← deductGas υ gHigh
    if val = 0
    then .ok ⟨σ', {υ with gas := g', pc := υ.pc + 1}⟩
    else do
      Except.guard (xhs υ) (jumpable κ.code loc.toNat)
      .ok ⟨σ', {υ with gas := g', pc := loc.toNat}⟩

def Ninst'.run (ω : Wor) (τ : Tra) (σ : Sta) (μ : Mem) (υ : Var) (κ : Con) :
    Ninst' → Exmo (Wor × Tra × Sta × Mem × Var)
  | .push x len => do
    let g' ← deductGas υ (if len = 0 then gBase else gVerylow)
    let σ' ← (σ.push1 x).toExmo υ
    let υ' := {υ with gas := g', pc := υ.pc + len + 1}
    .ok ⟨ω, τ, σ', μ, υ'⟩
  | .reg r => r.run ω τ σ μ υ κ
  | .exec e => panic! s!"unimplemented xinst : {e.toString}"


@[inline] def Char.isEq (c c' : Char) : Bool := c == c'

@[inline] def Substring.trimLeftChar (s : Substring) (c : Char) : Substring :=
  s.dropWhile (Char.isEq c)

@[inline] def String.trimLeftChar (s : String) (c : Char) : String :=
  (s.toSubstring.trimLeftChar c).toString

def Ninst'.toString : Ninst' → String
  | reg o => Rinst.toString o
  | exec o => Xinst.toString o
  | push _ 0 => "PUSH0"
  | push x len => "PUSH" ++ len.repr ++ " 0x" ++ (x.toHex.trimLeftChar '0')

def Inst'.toString : Inst' → String
  | .next n => n.toString
  | .jump j => j.toString
  | .last l => l.toString

def showLim (vb : Bool) (lim : Nat) (m : Var) : Exmo Unit :=
  if vb
  then match lim % 1000000 with
       | 0 => do
         dbg_trace s!"gas : {m.gas}"
         return ()
       | _ => return ()
  else return ()

-- Bal
-- Nonce
-- Code
-- Tstor
-- Pstor

def Sta.toProlog (σ : Sta) : String :=
  match σ.toList with
  | .none => "stack(retrieval_failed)"
  | .some xs => s!"stack({xs.map B256.toNat})"

def showStep (vb :Bool) (σ : Sta) (υ : Var) (κ : Con) (i : Inst') : Exmo Unit :=
  if vb
  then let σ_fmt : List B256 := σ.fst.toList
       -- dbg_trace s!"step(pc({υ.pc}), gas({υ.gas}), inst({i.toString}), stack({σ_fmt}))."
       -- dbg_trace s!"step(pc({υ.pc}), gas({υ.gas}), inst(\"{i.toString}\"), {σ.toProlog}, ret(\"0x{υ.ret.toHex}\"), depth({κ.exd}))."
       dbg_trace s!"step(pc({υ.pc}), gas({υ.gas}), inst(\"{i.toString}\"), {σ.toProlog}, depth({κ.exd}))."
       return ()
  else return ()


def ExecRes.onlyAcr (A : Acr) : ExecRes :=
  {wor := .empty, tra := .empty, gas := 0, acs := A, ret := [], err := true}

def execEcrec (ω : Wor) (τ : Tra) (υ : Var) (κ : Con) : ExecRes :=
  match safeSub υ.gas 3000 with
  | none =>
    -- {wt := none, gas := 0, acs := υ.acr, ret := some []}
    .onlyAcr υ.acr
  | some g' =>
    let h := B8L.toB256P <| κ.cld.sliceD 0 32 (0x00 : B8)
    let v : Option Bool :=
      match (B8L.toB256P <| κ.cld.sliceD 32 32 (0x00 : B8)) with
      | 0x1B => some .false
      | 0x1C => some .true
      | _ => none
    let r := B8L.toB256P <| κ.cld.sliceD 64 32 (0x00 : B8)
    let s := B8L.toB256P <| κ.cld.sliceD 96 32 (0x00 : B8)
    let o : B8L :=
      if v.isNone ∨ r = 0 ∨ r ≥ .secp256k1n ∨ s = 0 ∨ s ≥ .secp256k1n
      then (dbg_trace "exception detected, abort precomp-1 (ECREC)" ; [])
      else
        match ecrecover h v.get! r s with
        | none => []
        | some rcv =>
          (
            dbg_trace "ECREC RESULT : {rcv.toHex}" ;
            B256.toB8L (Adr.toB256 rcv)
          )
    -- {wt := some ⟨ω, τ⟩, gas := g', acs := υ.acr, ret := some o}
    {wor := ω, tra := τ, gas := g', acs := υ.acr, ret := o, err := false}

def execSha (ω : Wor) (τ : Tra) (υ : Var) (κ : Con) : ExecRes :=
  let g_r : Nat := 60 + (12 * (ceilDiv κ.cld.length 32))
  match safeSub υ.gas g_r with
  | none =>
    --{wt := none, gas := 0, acs := υ.acr, ret := some []}
    .onlyAcr υ.acr
  | some g' =>
    let hash : B256 := B8L.sha256 κ.cld
    -- {wt := some ⟨ω, τ⟩, gas := g', acs := υ.acr, ret := some hash.toB8L}
    {wor := ω, tra := τ, gas := g', acs := υ.acr, ret := hash.toB8L, err := false}

def execRip160 (ω : Wor) (τ : Tra) (υ : Var) (κ : Con) : ExecRes :=
  let g_r : Nat := 600 + (120 * (ceilDiv κ.cld.length 32))
  match safeSub υ.gas g_r with
  | none =>
    -- {wt := none, gas := 0, acs := υ.acr, ret := some []}
    .onlyAcr υ.acr
  | some g' =>
    let out : B8L := B256.toB8L <| B8L.toB256P <| (rip160 ⟨Array.mk κ.cld⟩).toList
    -- {wt := some ⟨ω, τ⟩, gas := g', acs := υ.acr, ret := some out}
    {wor := ω, tra := τ, gas := g', acs := υ.acr, ret := out, err := false}


def execId (ω : Wor) (τ : Tra) (υ : Var) (κ : Con) : ExecRes :=
  let g_r : Nat := 15 + (3 * (ceilDiv κ.cld.length 32))
  match safeSub υ.gas g_r with
  | none =>
    --{wt := none, gas := 0, acs := υ.acr, ret := some []}
    .onlyAcr υ.acr
  | some g' =>
  -- {wt := some ⟨ω, τ⟩, gas := g', acs := υ.acr, ret := some κ.cld}
    {wor := ω, tra := τ, gas := g', acs := υ.acr, ret :=  κ.cld, err := false}

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
  then dbg_trace "infinite point construction succeeded"
       some ⟨0, 0⟩
  else if y' ^ 2 = (x' ^ 3) + 3
       then dbg_trace "finite point construction succeeded"
            some ⟨x', y'⟩
       else dbg_trace "point construction failed"
            dbg_trace s!"y ^ 2 = {(y' ^ 2).val.toHex}"
            dbg_trace s!"x ^ 3 = {(x' ^ 3).val.toHex}"
            none

-- cx * x + cy * y' = d
-- let m := y / x

-- (cx - (cy * m)) * x + cy * y = d
-- (cx - (cy * m)) * x + cy * (y' + x * m) = d
-- ((cx * x) - (cy * m) * x)) + ((cy * y') + (cy * x * m)) = d


-- @[extern "lean_nat_gcd"]
-- def gcd (m n : @& Nat) : Nat :=
--   if m = 0 then
--     n
--   else
--     gcd (n % m) m
--   termination_by m
--   decreasing_by simp_wf; apply mod_lt _ (zero_lt_of_ne_zero _); assumption


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
  p.x.val.toB8L.pack 32 ++ p.y.val.toB8L.pack 32

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

def execEcmul (ω : Wor) (τ : Tra) (υ : Var) (κ : Con) : ExecRes :=
  match safeSub υ.gas 6000 with
  | none =>
    --{wt := none, gas := 0, acs := υ.acr, ret := some []}
    .onlyAcr υ.acr
  | some g' =>
    let slc := κ.cld.sliceD 0 96 (0x00 : B8)
    match (ecmul slc) with
    | some out =>
      --{wt := some ⟨ω, τ⟩, gas := g', acs := υ.acr, ret := some out}
      {wor := ω, tra := τ, gas := g', acs := υ.acr, ret := out, err := false}
    | _ =>
      --{wt := none, gas := 0, acs := υ.acr, ret := some []}
      .onlyAcr υ.acr

def execEcadd (ω : Wor) (τ : Tra) (υ : Var) (κ : Con) : ExecRes :=
  match safeSub υ.gas 150 with
  | none =>
    --{wt := none, gas := 0, acs := υ.acr, ret := some []}
    .onlyAcr υ.acr
  | some g' =>
    let slc := κ.cld.sliceD 0 128 (0x00 : B8)
    match (ecadd slc) with
    | some out => --{wt := some ⟨ω, τ⟩, gas := g', acs := υ.acr, ret := some out}
      {wor := ω, tra := τ, gas := g', acs := υ.acr, ret := out, err := false}
    | _ => -- {wt := none, gas := 0, acs := υ.acr, ret := some []}
      .onlyAcr υ.acr

def execExpmod (ω : Wor) (τ : Tra) (υ : Var) (κ : Con) : ExecRes :=
  let f : Nat → Nat := λ x => (ceilDiv x 8) ^ 2
  let gQuadDivisor : Nat := 3
  let l_B : Nat := B8L.toNat <| κ.cld.sliceD 0 32 (0x00 : B8)
  let l_E : Nat := B8L.toNat <| κ.cld.sliceD 32 32 (0x00 : B8)
  let l_M : Nat := B8L.toNat <| κ.cld.sliceD 64 32 (0x00 : B8)
  let B : Nat := B8L.toNat <| κ.cld.sliceD 96 l_B (0 : B8)
  let E : Nat := B8L.toNat <| κ.cld.sliceD (96 + l_B) l_E (0 : B8)
  let E_pfx : Nat := B8L.toNat <| κ.cld.sliceD (96 + l_B) 32 (0 : B8)
  let M : Nat := B8L.toNat <| κ.cld.sliceD (96 + l_B + l_E) l_M (0 : B8)
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
  let g_r : Nat := max 200 <| (f (max l_M l_B) * max l'_E 1) / gQuadDivisor
  match safeSub υ.gas g_r with
  | none => -- {wt := none, gas := 0, acs := υ.acr, ret := some []}
    .onlyAcr υ.acr
  | some g' =>
    -- let expmod : Nat := Nat.mod (B ^ E) M
    let expmod : Nat := Nat.powMod B E M
    -- {wt := some ⟨ω, τ⟩, gas := g', acs := υ.acr, ret := B8L.pack expmod.toB8L l_M}
    {wor := ω, tra := τ, gas := g', acs := υ.acr, ret := B8L.pack expmod.toB8L l_M, err := false}

def execPre (vb : Bool) (ω : Wor) (τ : Tra) (σ : Sta) (μ : Mem) (υ : Var) (κ : Con) : Nat → Exmo ExecRes
  | 1 => .ok <| execEcrec ω τ υ κ
  | 2 => .ok <| execSha ω τ υ κ
  | 3 => .ok <| execRip160 ω τ υ κ
  | 4 => .ok <| execId ω τ υ κ
  | 5 => .ok <| execExpmod ω τ υ κ
  | 6 => .ok <| execEcadd ω τ υ κ
  | 7 => .ok <| execEcmul ω τ υ κ
  | n => panic! s!"precomp uninplemented : {n}"

-- STATCALL: Θ(σ, A∗, Ia, Io, t,  t, C_CALLGAS(σ, μ, A), I_p, 0,     0,     i, Ie + 1, false)
-- CALL:     Θ(σ, A∗, Ia, Io, t,  t, C_CALLGAS(σ, μ, A), I_p, μs[2], μs[2], i, Ie + 1, Iw)
-- CALLCODE: Θ(σ, A∗, Ia, Io, Ia, t, C_CALLGAS(σ, μ, A), I_p, μs[2], μs[2], i, Ie + 1, Iw)
-- DELCALL:  Θ(σ, A∗, Is, Io, Ia, t, C_CALLGAS(σ, μ, A), I_p, 0,     I_v,   i, Ie + 1, Iw)

--  Θ(σ, A∗, Ia, Io, t,  t, C_CALLGAS(σ, μ, A), I_p, μs[2], μs[2], i, Ie + 1, Iw)

-- A* : υ, adr
-- I_o : κ
-- t : adr
-- C_CALLGAS(...) : ω, υ, gas, ilc, isz, olc, osz, adr, clv
-- I_p : κ
-- i : μ, ilc, isz
-- I_e : κ

-- θ( ω, μ, υ, κ, gas, adr, clv, ilc, isz, olc, osz,
--    sender, receiver, trans_val, report_val, update? )

-- succeeds in all cases EXCEPT there is insufficient gas
-- to execute a CALL/CALLCODE/DELCALL/STATCALL instruction,
-- which is an exceptional halting state.

def θ.prep
  (ω₀ : Wor)
  (H : BlockInfo)
  (bhs : List B256)
  (ci : B256)
  (ω : Wor)
  (A : Acr)
  (s : Adr)
  (o : Adr)
  (r : Adr)
  (c : Adr)
  (g : Nat)
  (p : Nat)
  (v : B256)
  (v_app : B256)
  (d : B8L)
  (e : Nat)
  (w : Bool) :
  Wor × Var × Con :=
  let ω₁ : Wor := (ω.addBal r v).subBal s v
  let κ : Con := {
    wor0 := ω₀
    blobHashes := bhs
    chainId := ci
    cta := r, oga := o, gpr := p.toB256, cld := d
    cla := s, clv := v_app, code := ω.code c, blk := H, exd := e, wup := w
  }
  let υ : Var := {
    gas := g, pc := 0, ret := [], act := 0, acr := A
    -- dest := A.dest, adrs := A.adrs, keys := A.keys,
    -- ref := A.ref, logs := A.logs, tchd := A.tchd
  }
  ⟨ω₁, υ, κ⟩



-- the X function of YP, except that the return type is modified to match
-- that of the Ξ function: the machine state (μ) returned by 'X' is never
-- used for anything except for remaining gas, so it is safe to discard the
-- unused information by the time X is returning.
-- This function returns `none` only when either the recursion limit or an
-- unimplemented opcode is reached. returns 'some _' for all other cases.
-- in particular, exceptional halting state should not cause it to return
-- a `none`.

def Linst.run (ω : Wor) (τ : Tra) (σ : Sta) (μ : Mem) (υ : Var) (κ : Con) :
    Linst → Exmo ExecRes
  | .invalid => .ok <| xhs υ
  | .stop =>
    -- .ok {wt := some ⟨ω, τ⟩, gas := υ.gas, acs := υ.acr, ret := some []}
    .ok {wor := ω, tra := τ, gas := υ.gas, acs := υ.acr, ret := [], err := false}
  | .ret => do
    let (rlc, rsz, _) ← σ.pop2.toExcept (xhs0 υ)
    let mc := memCost υ rlc rsz
    let g' ← deductGas υ mc
    let r := μ.sliceD rlc.toNat rsz.toNat 0
    --.ok {wt := some ⟨ω, τ⟩, gas := g', acs := υ.acr, ret := r}
    .ok {wor := ω, tra := τ, gas := g', acs := υ.acr, ret := r, err := false}
  | .rev => do
    let ⟨rlc, rsz, _⟩ ← σ.pop2.toExmo υ
    let mc := memCost υ rlc rsz
    let g' ← deductGas υ mc
    let o : B8L := μ.sliceD rlc.toNat rsz.toNat 0
    -- .ok {wt := none, gas := g', acs := υ.acr, ret := some o}
    .ok {wor := .empty, tra := .empty, gas := g', acs := υ.acr, ret := o, err := true}
  | .dest => do
    Except.guard (xhs0 υ) κ.wup
    let (x, _) ← σ.pop1.toExmo υ

    let a := x.toAdr -- recipient
    let cost :=
      gSelfdestruct
      + (if a ∈ υ.acr.adrs then 0 else gColdAccountAccess)
      + ( if Dead ω a ∧ ω.balAt κ.cta ≠ 0
          then gNewAccount
          else 0 )
    let gas' ← deductGas υ cost
    .ok
      {
        wor :=
          if a = κ.cta
          then ω
          else let v := (ω.get κ.cta).bal
               let ω' := ω.setBal κ.cta 0
               ω'
        tra := τ
        gas := gas'
        acs :=
          {
            υ.acr with
            dest := κ.cta :: υ.acr.dest
            adrs := υ.acr.adrs.insert a
          }
        ret := []
        err := false
      }



-- `ADDR` of YP
def newContAdr (s : Adr) (nc : B256) (ζ : Option B256) (ic : B8L): Adr :=
  let LA : B8L :=
    match ζ with
    | none => BLT.encode <| .list [.b8s s.toB8L, .b8s nc.toB8L.sig]
    | some z => (0xFF : B8) :: (s.toB8L ++ z.toB8L ++ ic.keccak.toB8L)
  (B8L.keccak LA).toAdr


/-
lambda-def  : Λ(σ,  A, s,  o,  g,      p,  v,      i, e,      ζ, w  )
lambda-call : Λ(σ∗, A, Ia, Io, L(μ_g), Ip, μ_s[0], i, Ie + 1, ζ, I_w)
-/



/-
for correct operation, `Λ.prep` requires:
A. `s` ≠ `a`
B. stor at `a` is empty
C. nonce at `a` is 0
D. no code at `a`

we may assume (C) and (D) because contract creation will roll back
and state changes will be undone if they fail to hold in later parts
of the lambda function, so whatever returned by `Λ.prep` will be
a moot point in that case. (A) can be deduced from (C) because `s` is
the address of either
  - the EOA that initiated a contract creation transaction
  - the contract whose code includes, and is now executing,
    a `CREATE` or `CREATE2` instruction
In either case, the nonce of `s` is at least 1, so `s` ≠ `a`.
Similarly, the storage of `a` must be empty because there is no way
to alter the storage of an account without incrementing its nonce.
-/

-- ν : Nonce
-- β : Bal
-- γ : Code
-- π : Pstor
-- τ : Tstor

def Λ.prep
  (ω : Wor)
  (A : Acr)
  (s : Adr)
  (v : B256)
  (i : B8L)
  (ζ : Option B256) : Wor × Acr × Adr :=
  let oldNonce : B256 := (ω.nonceAt s - 1)
  let a : Adr := newContAdr s oldNonce ζ i
  let ω' : Wor := ((ω.addBal a v).incrNonce a).subBal s v -- σ*
  dbg_trace s!"adding contract address to access list : {a}"
  let adrs' : AdrSet := A.adrs.insert a
  dbg_trace s!"updated access list : {adrs'.toList}"
  let A' : Acr := {A with adrs := adrs'}
  ⟨ω', A', a⟩

def ByteArray.fromList : B8L → ByteArray := .mk ∘ .mk

/-
def Λ.wrapCore (ω : Wor) (τ : Tra) (A_star : Acr) (a : Adr) (xr : ΞR) : ΛΘ.Result :=
  let o : B8L := xr.ret.getD []
  let c : Nat :=
    -- if `xr.ret = None`, value of `c` doesn't matter, but
    -- we use getD here to get a placeholder that typechecks
    if xr.wt.isNone then 0 else gCodedeposit * o.length
  let F : Prop :=
    (ω.nonceAt a ≠ 0) ∨
    !(ω.codeAt a).isEmpty ∨
    !ω.storIsEmptyAt a ∨
    xr.ret.isNone ∨ -- YP definition is `xr.wor.isNone ∧ xr.ret.isNone`,
                    -- but left conjunct is implied by right and superfluous;
                    -- YP's of `X` function shows that `xr.ret.isNone` only
                    -- in XHS, in which case also `xr.wor.isNone`.
    xr.gas < c ∨
    24576 < o.length ∨
    o.head? = some 0xEF

  let ⟨ω', τ'⟩ : Wor × Tra :=
    if F
    then ⟨ω, τ⟩
    else
      match xr.wt with
      | none => ⟨ω, τ⟩
      | some ⟨ω', τ'⟩ =>
        match ω'.find? a with
        | none => ⟨ω', τ'⟩
        | some ac =>
          if ac.Empty
          then panic! "error : empty account stored to world"
          else ⟨ω'.setCode a <| .fromList o, τ'⟩

  {
    wor := ω'
    tra := τ'
    gas :=
      if F
      then
        dbg_trace "lambda-wrap gas set to 0 due to F"
        0
      else
        dbg_trace "lambda-wrap gas set to xr.gas - c"
        xr.gas - c
    acs := if F ∨ xr.wt.isNone then A_star else xr.acs
    status :=
    if F
    then (
           -- dbg_trace
           --   (
           --     if (ω.nonceAt a ≠ 0) then "nonce ≠ 0; " else "" ++
           --     if !(ω.codeAt a).isEmpty then "empty code; " else "" ++
           --     if  xr.ret.isNone then "ret is none; " else "" ++
           --     if xr.gas < c then s!"gas(:={xr.gas}) < c(:={c}); " else "" ++
           --     if 24576 < o.length then "24576 < ||o||; " else "" ++
           --     if o.head? = some 0xEF then "head = 0xEF" else ""
           --   );
           0
         )
    else if xr.wt.isNone then 0 else 1
    ret := if xr.gas < c then [] else o
  }

def Λ.wrap (ω : Wor) (τ : Tra) (A_star : Acr) (a : Adr) : Exmo ΞR → ΛΘ.Result
  | .error (xr) => Λ.wrapCore ω τ A_star a xr
  | .ok xr => Λ.wrapCore ω τ A_star a xr
  -/

def Exmo.print (vb : Bool) (s : String) : Exmo Unit :=
  if vb
  then dbg_trace s ; pure ()
  else pure ()

def Exmo.println (vb : Bool) (s : String) : Exmo Unit :=
  .print vb (s ++ "\n")

def createMemoryAccess (μ : Mem) (υ : Var) (code_loc code_sz : B256) :
  Exmo (B8L × Nat × Nat) := do
  Except.guard (xhs0 υ) (code_sz.toNat ≤ maxInitcodeSize)
  let i : B8L := μ.sliceD code_loc.toNat code_sz.toNat 0
  let initCodeCost : Nat := gInitcodeword * (ceilDiv code_sz.toNat 32)
  let ⟨act', mc⟩ := memExpCost υ code_loc code_sz
  pure ⟨i, initCodeCost + mc + gCreate, act'⟩


def process_message : ExecRes := _

def invalidContractPrefix : B8L → Bool
  | 0xEF :: _ => true
  | _ => false

def create.run
  (vb : Bool) (lim : Nat) (ω : Wor) (τ : Tra)
  (σ : Sta) (μ : Mem) (υ : Var) (κ : Con) :
  Exmo (Wor × Tra × Sta × Mem × Var) := do
  let (val, code_loc, code_sz, σ) ← σ.pop3.toExcept (xhs0 υ)

  dbg_trace s!"first argument (value) : {val}"
  dbg_trace s!"second argument (value) : {code_loc}"
  dbg_trace s!"third argument (value) : {code_sz}"

  let act₀ := υ.act

  let ⟨act, extend_memory_cost⟩ := memExpCost υ code_loc code_sz

  dbg_trace s!"extend memory cost : {extend_memory_cost}"
  dbg_trace s!"extend memory by : {act - act₀}"

  let init_code_gas : Nat := gInitcodeword * (ceilDiv code_sz.toNat 32)

  dbg_trace s!"init code gas : {init_code_gas}"

  let gas ← deductGas υ <| init_code_gas + extend_memory_cost + gCreate

  let υ := {υ with gas := gas}
  dbg_trace s!"gas after deduction : {υ.gas}"

  let υ := {υ with act := act}
  dbg_trace s!"memory size after expansion : {υ.act}"

  let calldata : B8L := μ.sliceD code_loc.toNat code_sz.toNat 0

  let a : Adr := newContAdr κ.cta (ω.nonceAt κ.cta) .none calldata
  dbg_trace s!"new contract address : {a}"

  -- begin generic_create

  dbg_trace s!"calldata : {calldata}"

  .guard (xhs0 υ) (code_sz.toNat ≤ maxInitcodeSize)
  dbg_trace "CHECKED : code size ≤ max size"

  let adrs : AdrSet := υ.acr.adrs.insert a
  let υ := {υ with acr := {υ.acr with adrs := υ.acr.adrs.insert a}}
  dbg_trace s!"updated access list length : {adrs.toList.length}"

  let createGas := except64th gas
  dbg_trace s!"create message gas : {createGas}"

  let υ := {υ with gas := υ.gas - createGas}
  dbg_trace s!"gas after deducting create message gas : {υ.gas}"

  .guard (xhs0 υ) κ.wup
  dbg_trace "CHECKED : write permission = true"

  if  (ω.get κ.cta).bal < val ∨
      maxNonce ≤ (ω.nonceAt κ.cta).toNat ∨
      κ.exd = 0
  then
    do let σ : Sta ← (σ.push1 0).toExmo υ
       let υ : Var := {
         υ with
         gas := υ.gas + createGas
         pc := υ.pc + 1
         ret := []
       }
       .ok ⟨ω, τ, σ, μ, υ⟩
  else do
    dbg_trace "CHECKED : val ≤ sender balance"
    dbg_trace "CHECKED : sender nonce ≤ max nonce"
    dbg_trace "CHECKED : exec depth not at limit"

    let ω := ω.incrNonce κ.cta

    if ω.nonceAt a ≠ 0 ∨ !(ω.codeAt a).isEmpty ∨ !(ω.storIsEmptyAt a)
    then do
      dbg_trace "CASE : new contract address is already used"
      let σ : Sta ← (σ.push1 0).toExmo υ
       let υ : Var := {
         υ with
         pc := υ.pc + 1
         ret := []
       }
      .ok ⟨ω, τ, σ, μ, υ⟩
    else
      dbg_trace s!"nonce of {κ.cta} increased to : {ω.nonceAt κ.cta}"
      _


#exit
      let ω_bak := ω
      let τ_bak := τ
      dbg_trace "snapshot taken"

      let ω := ω.setStor a .empty
      dbg_trace "storage destroyed"

      let υ := {υ with acr := {υ.acr with created := υ.acr.created.insert a}}
      dbg_trace s!"updated access list size : {υ.acr.created.size}"

      let ω := ω.incrNonce a
      dbg_trace s!"nonce of {a} increased to : {ω.nonceAt a}"

      let er := process_message

      if er.err
      then .ok ⟨ω_bak, τ_bak, σ, μ, υ⟩
      else
        -- contract_code_gas = Uint(len(contract_code)) * GAS_CODE_DEPOSIT
        let contract_code_gas := er.ret.length * gCodedeposit --Uint(len(contract_code)) * GAS_CODE_DEPOSIT
        if invalidContractPrefix er.ret --er.ret.length > maxCodeSize
        then .ok ⟨ω_bak, τ_bak, σ, μ, {υ with gas := 0 }⟩
        else _

      --.error (xhs0 υ)

#exit

def Var.insertAdr (υ : Var) (a : Adr) : Var :=
  {υ with acr := {υ.acr with adrs := υ.acr.adrs.insert a}}

def Var.chargeGas (υ : Var) (c : Nat) : Exmo Var := do
  let g ← deductGas υ c
  .ok {υ with gas := g}

set_option maxHeartbeats 300000

mutual

  def theta
    (vb : Bool)
    (lim : Nat)
    (H : BlockInfo)
    (ω₀ : Wor)
    (bhs : List B256)
    (ci : B256)
    (ω : Wor)
    (τ : Tra)
    (A : Acr)
    (s : Adr)
    (o : Adr)
    (r : Adr)
    (c : Adr)
    (g : Nat)
    (p : Nat)
    (v : B256)
    (v_app : B256)
    (d : B8L)
    (e : Nat)
    (w : Bool) : ΛΘ.Result :=
    let ⟨ωp, υp, κp⟩ := θ.prep ω₀ H bhs ci ω A s o r c g p v v_app d e w
    let xr :=
      if (0 < c.toNat ∧ c.toNat < 10)
      then execPre vb ωp τ .init #[] υp κp c.toNat
      else exec vb lim ωp τ .init #[] υp κp
    θ.wrap ω τ A xr


  def callRun (vb : Bool) (lim : Nat) (ct : CallCostType)
    (ω : Wor) (τ : Tra) (σ : Sta) (μ : Mem) (υ : Var) (κ : Con)
    (gas adr ilc isz olc osz : B256)
    (sender receiver : Adr) (tval rval : B256) (wup : Bool) :
    Exmo (Wor × Tra × Sta × Mem × Var) := do

    let cod := adr.toAdr
    let as' : AdrSet := υ.acr.adrs.insert cod
    let A' : Acr := {υ.acr with adrs := as'}
    let act' : Nat := memExp (memExp υ.act ilc isz) olc osz
    let mc : Nat := cMem act' - cMem υ.act
    let cg : Nat := cCallGas ct ω υ gas.toNat mc cod tval

    dbg_trace s!"mc : {mc}"

    let totalCost := (cCall ct ω υ gas.toNat mc cod tval) + mc

    let g' ← (safeSub υ.gas totalCost).toExcept (xhs0 υ)

    dbg_trace s!"gas after deducting totalcost : {g'}"

    if 0 = κ.exd ∨ (ω.get κ.cta).bal < tval
    then
      let σ' ← (σ.push1 0).toExmo υ
      let υ' : Var := {
        gas := g' + cg
        pc := υ.pc + 1
        ret := []
        act := act'
        acr := A'
      }
      pure ⟨ω, τ, σ', μ, υ'⟩
    else
      let i : B8L := μ.sliceD ilc.toNat isz.toNat 0
      let ⟨ω', τ', rg, A'', z, o⟩ :=
        theta vb lim κ.blk κ.wor0 κ.blobHashes κ.chainId ω τ A' sender
          κ.oga receiver cod cg κ.gpr.toNat tval rval i (κ.exd - 1) wup
      let σ' ← (σ.push1 (if z then 1 else 0)).toExmo υ

      dbg_trace s!"gas returned from theta : {rg}"
      dbg_trace s!"gas after adding rg : {g' + rg}"

      let υ' : Var := {
        gas := g' + rg
        pc := υ.pc + 1
        ret := o
        act := act'
        acr := A''
      }
      pure ⟨ω', τ', σ', μ.write olc.toNat (o.take osz.toNat), υ'⟩

  def createRun (vb : Bool) (lim : Nat) (ω : Wor) (τ : Tra)
    (σ : Sta) (μ : Mem) (υ : Var) (κ : Con)
    (val code_loc code_sz : B256) (salt? : Option B256) :
    Exmo (Wor × Tra × Sta × Var) := do

    dbg_trace "ENTER : createRun"

    Except.guard (xhs0 υ) κ.wup
    let ⟨i, createMemCost, act'⟩ ← createMemoryAccess μ υ code_loc code_sz
    let otherCost : Nat :=
      salt?.rec 0 (fun _ => gKeccak256Word * (ceilDiv code_sz.toNat 32))
    let interGas ← deductGas υ <| createMemCost + otherCost
    let a : Adr := newContAdr κ.cta (ω.nonceAt κ.cta) salt? i

    dbg_trace s!"new cont adr : {a}"


    if (
      0 = κ.exd ∨
      (ω.get κ.cta).bal < val ∨
      maxNonce ≤ (ω.nonceAt κ.cta).toNat
    )
    then
      let σ' : Sta ← (σ.push1 0).toExmo υ
      let υ' : Var := {
        gas := interGas
        pc := υ.pc + 1
        ret := []
        act := act'
        acr := υ.acr
      }
      .ok ⟨ω, τ, σ', υ'⟩
    else

      dbg_trace "depth, ba, nonce all good"

      let createGas := except64th interGas
      if ω.nonceAt a ≠ 0 ∨ !(ω.codeAt a).isEmpty ∨ !(ω.storIsEmptyAt a)
      then
        let ω' := ω.incrNonce κ.cta
        let σ' : Sta ← (σ.push1 0).toExmo υ

        let adrs' : AdrSet := υ.acr.adrs.insert a
        dbg_trace s!"updated access list : {adrs'.toList}"
        let A' : Acr := {υ.acr with adrs := adrs'}
        let υ' : Var := {
          gas := interGas - createGas
          pc := υ.pc + 1
          ret := []
          act := act'
          acr := A'
        }
        .ok ⟨ω', τ, σ', υ'⟩
      else
        let ωp := ω.incrNonce κ.cta

        dbg_trace "CALL : lambda"

        let ⟨ω', τ', g', A', z, o⟩ :=
          lambda
            vb lim κ.blk κ.wor0 κ.blobHashes κ.chainId ωp τ υ.acr
            κ.cta κ.oga createGas κ.gpr val i κ.exd salt? κ.wup

        dbg_trace s!"gas left by lambda : {g'}"

        let x : B256 := if z = 0 then 0 else a.toB256
        let σ' : Sta ← (σ.push1 x).toExmo υ
        let υ' := {
          gas := (interGas - createGas) + g'
          pc := υ.pc + 1
          ret := if z = 1 then [] else o
          act := act'
          acr := A'
        }
        .ok ⟨ω', τ', σ', υ'⟩

  def Ninst'.run'
    (vb : Bool) (lim : Nat) (ω : Wor) (τ : Tra)
    (σ : Sta) (μ : Mem) (υ : Var) (κ : Con) :
    Ninst' → Exmo (Wor × Tra × Sta × Mem × Var)
    | .reg r => r.run ω τ σ μ υ κ
    | .push x len => do
      let g' ← deductGas υ (if len = 0 then gBase else gVerylow)
      let σ' ← (σ.push1 x).toExmo υ
      let υ' := {υ with gas := g', pc := υ.pc + len + 1}
      .ok ⟨ω, τ, σ', μ, υ'⟩
    | .exec .create => do
      let (val, code_loc, code_sz, σ') ← σ.pop3.toExcept (xhs0 υ)
      let ⟨ω', τ', σ'', υ'⟩ ← createRun vb lim ω τ σ' μ υ κ val code_loc code_sz .none
      pure ⟨ω', τ', σ'', μ, υ'⟩
      -- create.run vb lim ω τ σ μ υ κ
    | .exec .create2 => do
      let (val, code_loc, code_sz, salt, σ') ← σ.pop4.toExcept (xhs0 υ)
      let ⟨ω', τ', σ'', υ'⟩ ← createRun vb lim ω τ σ' μ υ κ val code_loc code_sz (.some salt)
      pure ⟨ω', τ', σ'', μ, υ'⟩
    /-
    | .exec .create2 => do
      let (val, code_loc, code_sz, salt, σ') ← σ.pop4.toExcept (xhs0 υ)


      let initCodeCost : Nat := gInitcodeword * (ceilDiv code_sz.toNat 32)
      dbg_trace s!"initCodeCost : {initCodeCost}"

      let ⟨act', mc⟩ := memExpCost υ code_loc code_sz
      dbg_trace s!"mc : {mc}"

      let upfrontCost := initCodeCost + mc + gCreate + (gKeccak256Word * (ceilDiv code_sz.toNat 32))

      dbg_trace s!"upfront const : {upfrontCost}"

      let interGas ← deductGas υ upfrontCost
      dbg_trace s!"gas after deduction : {interGas}"

      let i : B8L := μ.sliceD code_loc.toNat code_sz.toNat 0
      dbg_trace s!"calldata : {i}"

      let a : Adr := newContAdr κ.cta (ω.nonceAt κ.cta) (.some salt) i
      dbg_trace s!"new contract address : {a}"

      .guard (xhs0 υ) (code_sz.toNat ≤ maxInitcodeSize)
      dbg_trace "code size checked."

      let adrs' : AdrSet := υ.acr.adrs.insert a

      dbg_trace s!"updated access list : {adrs'.toList}"

      let createGas := except64th interGas
      dbg_trace s!"create message gas : {createGas}"

      dbg_trace s!"gas after deducting create message gas : {interGas - createGas}"

      .guard (xhs0 υ) κ.wup
      dbg_trace "write permission checked."

      if  (ω.get κ.cta).bal < val ∨
          maxNonce ≤ (ω.nonceAt κ.cta).toNat ∨
          κ.exd = 0
      then
        do let σ' : Sta ← (σ.push1 0).toExmo υ
           let υ' : Var := {
             gas := interGas
             pc := υ.pc + 1
             ret := []
             act := act'
             acr := υ.acr
           }
           .ok ⟨ω, τ, σ', μ, υ'⟩
      else do
        dbg_trace "sender balance & sender nonce & exec depth checked."
        if ω.nonceAt a ≠ 0 ∨ !(ω.codeAt a).isEmpty ∨ !(ω.storIsEmptyAt a)
        then do

          dbg_trace s!"increasing nonce of address : {κ.cta}"
          let ω' := ω.incrNonce κ.cta
          let σ' : Sta ← (σ.push1 0).toExmo υ
           let υ' : Var := {
             gas := interGas - createGas
             pc := υ.pc + 1
             ret := []
             act := act'
             acr := υ.acr
           }
          .ok ⟨ω', τ, σ', μ, υ'⟩
        else _ -- .error (xhs0 υ)
    -/

    | .exec .call => do
      let (gas, adr, clv, ilc, isz, olc, osz, σ') ← σ.pop7.toExmo υ
      Except.guard (xhs0 υ) (κ.wup ∨ clv = 0)
      callRun vb lim .all ω τ σ' μ υ κ
        gas adr ilc isz olc osz κ.cta adr.toAdr clv clv κ.wup
    | .exec .statcall => do
      let (gas, adr, ilc, isz, olc, osz, σ') ← σ.pop6.toExmo υ
      callRun vb lim .onlyAccess ω τ σ' μ υ κ
        gas adr ilc isz olc osz κ.cta adr.toAdr 0 0 false
    | .exec .callcode => do
      let (gas, adr, clv, ilc, isz, olc, osz, σ') ← σ.pop7.toExmo υ
      callRun vb lim .noCreate ω τ σ' μ υ κ
        gas adr ilc isz olc osz κ.cta κ.cta clv clv κ.wup
    | .exec .delcall => do
      let (gas, adr, ilc, isz, olc, osz, σ') ← σ.pop6.toExmo υ
      callRun vb lim .onlyAccess ω τ σ' μ υ κ
       gas adr ilc isz olc osz κ.cla κ.cta 0 κ.clv κ.wup

  def lambda
    (vb : Bool) (lim : Nat) (H : BlockInfo) (ω₀ : Wor)
    (bhs : List B256) (ci : B256) (ω : Wor)
    (τ : Tra) (A : Acr) (s : Adr) (o : Adr)
    (g : Nat) (p : B256) (v : B256) (i : B8L)
    (e : Nat) (ζ : Option B256) (w : Bool) : ΛΘ.Result :=
    let ⟨ω', A', a⟩ := Λ.prep ω A s v i ζ
    let κ : Con :=
      {
        blk := H, wor0 := ω₀
        blobHashes := bhs, chainId := ci
        cta := a, oga := o
        gpr := p, cld := []
        cla := s, clv := v
        code := ByteArray.mk (.mk i)
        exd := e - 1, wup := w
      }
    let xr :=
      exec vb lim ω' τ .init #[] {gas := g, pc := 0, ret := [], act := 0, acr := A'} κ
    Λ.wrap ω τ A' a xr

  def exec (vb : Bool): Nat → Wor → Tra → Sta → Mem → Var → Con → Exmo ΞR
    | 0, _, _, _, _, _, _ =>
      panic! "execution recursion limit reached (NOT execution depth limit)"
    | lim + 1, ω, τ, σ, μ, υ, κ => do
      showLim vb lim υ
      let i ← (getInst υ κ).toExmo υ
      showStep vb σ υ κ i
      match i with
      | .next n => do
        let ⟨ω', τ', σ', μ', υ'⟩ ← n.run' vb lim ω τ σ μ υ κ
        exec vb lim ω' τ' σ' μ' υ' κ
      | .jump j => do
        let ⟨σ', υ'⟩ ← j.run σ υ κ
        exec vb lim ω τ σ' μ υ' κ
      | .last l => l.run ω τ σ μ υ κ
end

def publicAddress (hsa : ByteArray) (ri : UInt8) (rsa : ByteArray) : IO Adr :=
  match (ecrecoverFlag hsa ri rsa).toList with
  | [] => IO.throw "Unreachable code : ecrecover should never return empty bytes"
  | b :: pa =>
    if b = 0
    then IO.throw "ecrecover failed"
    else (B8L.toAdr pa).toIO "bytearray to address conversion failed"


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
  | fail : Exception → Tx.Result
  | pass (Wor : Wor) (gas : Nat) (logs : List Log) (sta : Bool) : Tx.Result

def Tx.Result.toStrings : Tx.Result → List String
  | .fail x => [x.toString]
  | .pass w g l s =>
    fork "pass" [
      w.toStrings,
      [s!"gas : {g}"],
      --[s!"logs : {l}"],
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

def Stx.run
  (vb : Bool) (blk : BlockInfo)
  (w : Wor) (tx : Stx) : IO Tx.Result := do

  IO.guard (tx.gasLimit ≤ blk.gasLimit) "error : block gas limit < tx gas limit"

  let gIntrinsic : Nat :=
    intrinsicGas tx.receiver tx.calldata tx.type.accessList
  let g : Nat := tx.gasLimit.toNat - gIntrinsic

  let blobCount : B256 := tx.blobHashes.length.toB256

  let .true ← IO.decide (¬ tx.type.isBlobTx ∨ tx.receiver.isSome) | pure (Tx.Result.fail .blobCreation)
  let .true ← IO.decide (¬ tx.type.isBlobTx ∨ blobCount > 0) | pure (Tx.Result.fail .noBlobs)
  let .true ← IO.decide (blobCount < 7) | pure (Tx.Result.fail .tooManyBlobs)
  let .true ← IO.decide (tx.blobHashes.Forall correctBlobHashVersion)
    | pure (Tx.Result.fail .wrongBlobHashVersion)
  let .false ← IO.decide (tx.receiver.isNone ∧ maxInitcodeSize < tx.calldata.length)
    | pure (Tx.Result.fail .initCodeTooLong)

  let .true ← IO.decide ((w.nonceAt tx.sender).toNat < maxNonce) | pure (Tx.Result.fail .nonceTooHigh)

  let totalBlobGas : B256 := (gasPerBlob * blobCount)

  let blobGasPrice : B256 :=
    Nat.toB256 <| get_base_fee_per_blob_gas blk.excessBlobGas.toNat

  let cpVal : B256 :=
    (tx.gasLimit * tx.type.gasPrice blk.baseFee) + (totalBlobGas * blobGasPrice)
  let w' ← (checkpoint w tx.sender cpVal).toIO "checkpoint creation failed"

  let tr : ΛΘ.Result :=
    match tx.receiver with
    | none =>
        lambda vb
          g
          blk
          w
          tx.blobHashes
          tx.type.chainId.toB256
          w'
          .empty
          (A_star blk tx.sender tx.receiver tx.type.accessList)
          tx.sender
          tx.sender
          g
          (tx.type.gasPrice blk.baseFee)
          tx.val
          tx.calldata
          1024
          none
          true
    | some rcvr =>
        theta
          vb
          g
          blk
          w
          tx.blobHashes
          tx.type.chainId.toB256
          w'
          .empty
          (A_star blk tx.sender tx.receiver tx.type.accessList)
          tx.sender
          tx.sender
          rcvr
          rcvr
          g
          (tx.type.gasPrice blk.baseFee).toNat
          tx.val
          tx.val
          tx.calldata
          1024
          true

  let gasLeft : Nat := tr.gas
  let refundAmount : Nat := tr.acs.ref
  let gasReturn : B256 :=
    Nat.toB256 (gasLeft + min ((tx.gasLimit.toNat - gasLeft) / 5) refundAmount) -- g*
  let gasUsed : B256 := tx.gasLimit - gasReturn
  let valReturn : B256 := gasReturn * (tx.type.gasPrice blk.baseFee)
  let f : B256 := (tx.type.gasPrice blk.baseFee) - blk.baseFee
  let w₀ : Wor := tr.wor.addBal tx.sender valReturn
  let w₁ : Wor := w₀.addBal blk.beneficiary (gasUsed * f)
  let w₃ : Wor := List.foldl eraseIfEmpty w₁ tr.acs.tchd.toList
  -- EIP-6780 : delete only accts that did not exist at the beginning of tx
  let ω₄ : Wor := List.foldl (eraseIfNew w) w₃ tr.acs.dest
  return (.pass ω₄ gasUsed.toNat tr.acs.logs.reverse tr.status)
  -- (BLT.list tr.acs.logs.reverse).encode.keccak

def Log.toBLT (l : Log) : BLT :=
  .list [
    .b8s l.address.toB8L,
    .list (l.topics.map B256.toRLP),
    .b8s l.data
  ]

def Tx.Result.check (vb : Bool) (exRoot exLogHash : B256)
    (exExcept : Option Exception) : Tx.Result → IO Unit
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


def getSender (tx : Tx) (hs : B256) : IO Adr := do
  let rsa : ByteArray := ⟨Array.mk (tx.r ++ tx.s)⟩
  let ri : UInt8 := Byte.toB8 (if tx.yParity then 1 else 0)
  let hsa : ByteArray := ⟨Array.mk hs.toB8L⟩
  publicAddress hsa ri rsa

def decodeTxBytes (txbs : B8L) : IO (Tx × Adr) := do
  let ⟨tx, hs⟩ ← decodeTxHash txbs
  let sender ← getSender tx hs
  return ⟨tx, sender⟩

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

def Lean.Json.toAcct : Lean.Json → IO Acct
  | .obj r => do
    let bal_json ← (r.find compare "balance").toIO ""
    let nonce_json ← (r.find compare "nonce").toIO ""
    let code_json ← (r.find compare "code").toIO ""
    let stor_json ← (r.find compare "storage").toIO "" >>= Lean.Json.fromObj
    let bal ← Lean.Json.toB256P bal_json
    let nonce ← Lean.Json.toB256P nonce_json
    let code ← Lean.Json.toB8L code_json
    let stor ← mapM helper stor_json.toArray.toList
    return ⟨nonce, bal, Lean.RBMap.fromList stor _, ByteArray.fromList code⟩
  | _ => .throw "cannot parse account (not .obj)"

instance : ToString Wor := ⟨String.joinln ∘ Wor.toStrings⟩

def Lean.Json.toWorld (j : Lean.Json) : IO Wor := do
  let aux : Wor → ((_ : String) × Lean.Json) → IO Wor :=
    fun | w, ⟨s, j⟩ => do
      let adr ← (Hex.toAdr <| remove0x s).toIO ""
      let acct ← j.toAcct
      pure <| w.set adr acct
  let ob ← j.fromObj
  List.foldlM aux .empty ob.toArray.toList

def Lean.Json.find? : String → Lean.Json → Option Lean.Json
  | k, .obj r => r.find compare k
  | _, _ => .none

def Lean.Json.find : String → Lean.Json → IO Lean.Json
  | k, .obj r => (r.find compare k).toIO ""
  | _, _ => .throw ""

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
    let h ← hj.toB256?
    pure (.root h)

def getPostRoot (j : Lean.Json) : IO B256 := do
  let r ← j.fromObj
  match r.find compare "postStateHash" with
  | some hj => hj.toB256?
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

def Bool.toB8L : Bool → B8L
  | .false => []
  | .true => [0x01]

def Stx.Result.check' (vb : Bool) (tx : Stx) (exBloom : B8L)
    (exRcRoot : B256) (exRoot : ExpectedWorldState) : Option Exception → Tx.Result → IO Unit
  | .some ex, .fail ex' => do
    .check vb (ex = ex')
      "exception check : pass"
      s!"ERROR : expected exception = {ex}, computed exception = {ex'}"
    .cprintln vb "test complete.\n"
  | .none, .fail ex => .throw s!"ERROR : expected exception = none, computed exception = {ex}"
  | .some ex, _ => .throw s!"ERROR : expected exception = {ex}, computed exception = none"
  | .none, .pass w g l s => do

    let bloom : B8L := List.foldl addLogToBloom (List.replicate 256 0x00) l

    .check vb (exBloom = bloom)
      "bloom check : PASS\n"
      s!"bloom check : FAIL\nexpected : {exBloom.toHex}\ncomputed : {bloom.toHex}\n"

    let receipt_rlp : BLT := .list [
      .b8s s.toB8L, -- tx status (equals 0x01 if it gets to this point)
      .b8s (g.toB8L),
      .b8s bloom,
      .list (l.map Log.toBLT)
    ]

    let receipt_header : B8L :=
      match tx.type with
      | .zero _ _ => []
      | .two _ _ _ _ => [0x02]
      | .three _ _ _ _ _ _ => [0x03]

    let receipt : B8L := receipt_header ++ receipt_rlp.encode
    let rcRoot : B256 := receiptRoot [⟨[0x80], receipt⟩]

    .check vb (rcRoot = exRcRoot)
      "receipt root check : pass"
      s!"receipt root check : fail\nexpected : {exRcRoot.toHex}\ncomputed : {rcRoot.toHex}"

    .cprintln vb "\n\n"
    .cprintln vb s!"tx status : {s}"
    .cprint vb "terminal world :"
    .cprintln vb (String.joinln w.toStrings)

    let setupVal := w.storEntryAt setupAdr 1000
    .guard (setupVal = 0) s!"setup address has nonzero value stored at position 1000 : {setupVal}"

    -- let w' := w.setStorEntry setupAdr 1000 1000
    -- let w' := w.setStorEntry setupAdr 0xf2 1687174231

    match exRoot with
    | .wor xw => do
      let w' := w.set setupAdr .empty
      let xw' := xw.set setupAdr .empty
      .check vb (xw'.root = w'.root)
        "state root check : PASS\n"
        s!"state root check : FAIL\nexpected : {xw'.root.toHex}\ncomputed : {w'.root.toHex}\n(complete expected/computed world states available)"
      .cprintln vb "test complete.\n"
      .cprintln vb "test complete.\n"
    | .root xr => do
      let w' := w.setStorEntry setupAdr 1000 1000
      .check vb (w'.root = xr)
        "state root check : PASS\n"
        s!"state root check : fail\nexpected : {xr.toHex}\ncomputed : {w'.root.toHex}"
      .cprintln vb "test complete.\n"

def Tx.Result.check' (vb : Bool) (tx : Tx) (exBloom : B8L)
    (exRcRoot : B256) (exRoot : B256) : Option Exception → Tx.Result → IO Unit
  | .some ex, .fail ex' => do
    .check vb (ex = ex')
      "exception check : pass"
      s!"ERROR : expected exception = {ex}, computed exception = {ex'}"
    .cprintln vb "test complete.\n"
  | .none, .fail ex => .throw s!"ERROR : expected exception = none, computed exception = {ex}"
  | .some ex, _ => .throw s!"ERROR : expected exception = {ex}, computed exception = none"
  | .none, .pass w g l s => do

    let bloom : B8L := List.foldl addLogToBloom (List.replicate 256 0x00) l

    .check vb (exBloom = bloom)
      "bloom check : PASS\n"
      s!"bloom check : FAIL\nexpected : {exBloom.toHex}\ncomputed : {bloom.toHex}\n"

    let receipt_rlp : BLT := .list [
      .b8s s.toB8L, -- tx status (equals 0x01 if it gets to this point)
      .b8s (g.toB8L),
      .b8s bloom,
      .list (l.map Log.toBLT)
    ]

    let receipt_header : B8L :=
      match tx.type with
      | .zero _ _ => []
      | .two _ _ _ _ => [0x02]
      | .three _ _ _ _ _ _ => [0x03]

    let receipt : B8L := receipt_header ++ receipt_rlp.encode
    let rcRoot : B256 := receiptRoot [⟨[0x80], receipt⟩]

    .check vb (rcRoot = exRcRoot)
      "receipt root check : pass"
      s!"receipt root check : fail\nexpected : {exRcRoot.toHex}\ncomputed : {rcRoot.toHex}"

    .cprintln vb "\n\n"
    .cprintln vb s!"tx status : {s}"
    .cprint vb "terminal world :"
    .cprintln vb (String.joinln w.toStrings)

    let setupVal := w.storEntryAt setupAdr 1000
    .guard (setupVal = 0) s!"setup address has nonzero value stored at position 1000 : {setupVal}"

    -- let w' := w.setStorEntry setupAdr 1000 1000
    let w' := w.setStorEntry setupAdr 0xf2 1687174231


    .check vb (w'.root = exRoot)
      "state root check : PASS\n"
      s!"state root check : fail\nexpected : {exRoot.toHex}\ncomputed : {w'.root.toHex}"

    .cprintln vb "test complete.\n"

def decodeTxBLT : BLT → IO (Tx × B8L × Adr)
  | .b8s xs => do
    let ⟨tx, sender⟩ ← decodeTxBytes xs
    pure ⟨tx, xs, sender⟩
  | .list l => do
    let r : BLT := .list l
    let ⟨tx, hs⟩ ← r.toLegacyTxHash
    let sender ← getSender tx hs
    return ⟨tx, r.encode, sender⟩

def Tx.toStx (tx : Tx) (s : Adr) : Stx :=
  {
    nonce := tx.nonce
    gasLimit := tx.gasLimit
    sender := s
    receiver := tx.receiver
    val := tx.val
    calldata := tx.calldata
    type := tx.type
  }

structure Withdrawal : Type where
  (globalIndex : B64)
  (validatorIndex : B64)
  (recipient : Adr)
  (amount : B256)

def Withdrawal.toStrings (wd : Withdrawal) : List String :=
  fork "withdrawal" [
    [s!"global index : 0x{wd.globalIndex.toHex}"],
    [s!"validator index : 0x{wd.validatorIndex.toHex}"],
    [s!"recipient : 0x{wd.recipient.toHex}"],
    [s!"amount : 0x{wd.amount.toHex}"]
  ]

instance : ToString Withdrawal := ⟨String.joinln ∘ Withdrawal.toStrings⟩

def Withdrawal.toBLT (w : Withdrawal) : BLT :=
  .list [
    .b8s w.globalIndex.toB8L,
    .b8s w.validatorIndex.toB8L,
    .b8s w.recipient.toB8L,
    .b8s w.amount.toB8L
  ]

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
    fun | ⟨idx, wd⟩ => ⟨idx.toB8LNil, wd.toBLT.encode⟩
  let temp : List (B8L × B8L) := (wds.putIndex 0).map aux
  let wr' := receiptRoot temp
  .check vb (wr = wr')
    "withdrawals check : PASS\n"
    s!"withdrawals check : FAIL, withdrawals : {wds}"

def getExceptionMap (j : Lean.Json) : IO (Option Exception × Lean.Json) := do
  match j.find? "expectException" with
  | .none => pure ⟨.none, j⟩
  | .some exj => do
    let exs ← exj.fromStr
    let ex ← (parseException exs).toIO ""
    let j' ← j.find "rlp_decoded"
    pure ⟨.some ex, j'⟩

def getBlockHeader : Lean.Json → Option Lean.Json
  | .obj r =>
    r.find compare "blockHeader" <|>
    ( do let (.obj r') ← r.find compare "rlp_decoded" | .none
         r'.find compare "blockHeader" )
  | _ => .none

def Lean.Json.toWithdrawal (j : Lean.Json) : IO Withdrawal :=
  .throw "unimplemented : json-to-withdrawal parsing"

def runPyTest (vb : Bool) (t : Test) : IO Unit := do
  .cprintln vb "----------------------------------------------------------------"
  .println s!"Running test : {t.name}"

  let [blk] ← t.blocks.fromArr | .throw "error : multiple blocks"
  let ⟨ex, mm⟩ ← getExceptionMap blk
  let bh ← (getBlockHeader mm).toIO ""
  let wds ← Lean.Json.find "withdrawals" mm >>= Lean.Json.fromArr >>= mapM Lean.Json.toWithdrawal
  let bloom ← bh.find "bloom" >>= Lean.Json.toB8L
  let bf ← bh.find "baseFeePerGas" >>= Lean.Json.toB256P
  let xbg ← bh.find "excessBlobGas" >>= Lean.Json.toB256P
  let cb ← bh.find "coinbase" >>= Lean.Json.toAdr
  let pr ← bh.find "mixHash" >>= Lean.Json.toB256P
  let gl ← bh.find "gasLimit" >>= Lean.Json.toB256P
  let ts ← bh.find "timestamp" >>= Lean.Json.toB256P
  let nb ← bh.find "number" >>= Lean.Json.toB256P
  let txRoot ← bh.find "transactionsTrie" >>= Lean.Json.toB256P
  let exRcRoot ← bh.find "receiptTrie" >>= Lean.Json.toB256P
  let wdRoot ← bh.find "withdrawalsRoot" >>= Lean.Json.toB256P

  checkWithdrawalsRoot vb wds wdRoot

  let rlp_str ← t.blocks.get? 0 >>= Lean.Json.find "rlp" >>= Lean.Json.fromStr >>= .remove0x
  let rlp ← (Hex.toB8L rlp_str >>= BLT.decode).toIO ""
  let tx_rlp ← (rlp.get? 1 >>= BLT.get? 0).toIO ""
  let w ← Lean.Json.toWorld t.pre

  .cprintln vb "world state before tx:"
  .cprintln vb (String.joinln <| w.toStrings)

  let bi : BlockInfo :=
    {
      blockHashes := [],
      baseFee := bf
      excessBlobGas := xbg
      beneficiary := cb
      prevRandao := pr
      gasLimit := gl
      timestamp := ts
      number := nb
    }

  let ⟨txFoo, txbs, sender⟩ ← decodeTxBLT tx_rlp

  let stx := Tx.toStx txFoo sender

  let txr ← Stx.run vb bi w stx

  .cprintln vb "tx result:"
  .cprintln vb (String.joinln <| txr.toStrings)

  checkTransactionsRoot vb txbs txRoot txr

  Stx.Result.check' vb stx bloom exRcRoot t.post ex txr


def runPyTestFile (vb : Bool) (idx : Option Nat) (path : String) : IO Unit := do
  .println "\n================================================================\n"
  .println s!"Testing file : {path}\n"
  let j ← readJsonFile path
  let ts ← j.toTests
  match idx with
  | none => let _ ← mapM (runPyTest vb) ts
  | some k =>
    match ts.get? k with
    | none => pure ()
    | some t => runPyTest vb t

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
    let b ← System.FilePath.isDir path
    if !b
    then runPyTestFile vb idx path
    else do
      let fs ← System.FilePath.walkDir path
      let _← mapM (runPyTestFile vb idx) (fs.toList.map System.FilePath.toString)
      pure ()
  | _ => IO.throw "error : invalid arguments"

#exit




-- def Bytes.toHexLine (bs : Bytes) : String :=
--   s!"hex\"{bs.toHex}\""
--
-- def WethByteCode : String :=
--   List.foldr
--      (λ s0 s1 => s0 ++ "\n" ++ s1)
--      "" <| List.map Bytes.toHexLine
--         <| List.chunks 31 <| Option.getD weth.compile []
