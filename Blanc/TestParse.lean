import Lean.Data.Json
import Lean.Data.Json.Parser
import Blanc.Common

structure EnvData where
  (baseFee : B256)
  (excessBlobGas : B256)
  (coinbase : Adr)
  (prevRandao : B256)
  (blockGasLimit : B256)
  (timestamp : B256)
  (number : B256)

structure PreData where
  (addr : Adr)
  (nonce : B8L)
  (bal : B8L)
  (stor : Stor)
  (code : B8L)

inductive Exception : Type
  | noBlobs
  | tooManyBlobs
  | blobCreation
  | wrongBlobHashVersion
deriving DecidableEq

def Exception.toString : Exception → String
  | noBlobs => "noBlobs"
  | tooManyBlobs => "tooManyBlobs"
  | blobCreation => "blobCreation"
  | wrongBlobHashVersion => "wrongBlobHashVersion"

instance : ToString Exception := ⟨Exception.toString⟩

structure PostData where
  (expectedException : Option Exception)
  (hash : B256)
  (dataIdx : Nat)
  (gasIdx : Nat)
  (valueIdx : Nat)
  (logs : B256)
  (txdata : B8L)

def AccessList : Type := List (Adr × List B256)

instance : ToString AccessList := ⟨λ x => @List.toString _ _ x⟩

structure TransactionData : Type where
  (accessLists : Option (List AccessList))
  (bvhs : Option (List B256))
  (data : List B8L)
  (gasLimit : List B256)
  (fee : B256 ⊕ (B256 × B256))
  (nonce : B256)
  (secretKey : B256)
  (sender : Adr)
  (receiver : Option Adr)
  (value : List B256)

-- #exit
-- inductive TransactionData : Type
--   | zero
--     (data : List B8L)
--     (gasLimit : List B256)
--     (gasPrice : B256)
--     (nonce : B256)
--     (secretKey : B256)
--     (sender : Adr)
--     (receiver : Adr)
--     (value : List B256) : TransactionData
--   | two
--     (accessLists : List (List Adr))
--     (data : List B8L)
--     (gasLimit : List B256)
--     (maxFeePerGas : B256)
--     (maxPriorityFeePerGas : B256)
--     (nonce : B256)
--     (secretKey : B256)
--     (sender : Adr)
--     (receiver : Adr)
--     (value : List B256) : TransactionData


-- def TransactionData.gasLimit : TransactionData → List B256
--   | .zero data gasLimit gasPrice nonce secretKey sender receiver value  => gasLimit
--   | .two accessLists data gasLimit maxFeePerGas maxPriorityFeePerGas nonce secretKey sender receiver value => gasLimit
--
-- def TransactionData.data :  TransactionData → List B8L
--   | .zero data gasLimit gasPrice nonce secretKey sender receiver value => data
--   | .two accessLists data gasLimit maxFeePerGas maxPriorityFeePerGas nonce secretKey sender receiver value => data
-- def TransactionData.value :  TransactionData → List B256
--   | .zero data gasLimit gasPrice nonce secretKey sender receiver value => value
--   | .two accessLists data gasLimit maxFeePerGas maxPriorityFeePerGas nonce secretKey sender receiver value => value
--
-- def TransactionData.nonce :  TransactionData → B256
--   | .zero data gasLimit gasPrice nonce secretKey sender receiver value => nonce
--   | .two accessLists data gasLimit maxFeePerGas maxPriorityFeePerGas nonce secretKey sender receiver value => nonce
--
-- def TransactionData.secretKey :  TransactionData → B256
--   | .zero data gasLimit gasPrice nonce secretKey sender receiver value => secretKey
--   | .two accessLists data gasLimit maxFeePerGas maxPriorityFeePerGas nonce secretKey sender receiver value => secretKey
--
-- def TransactionData.sender :  TransactionData → Adr
--   | .zero data gasLimit gasPrice nonce secretKey sender receiver value => sender
--   | .two accessLists data gasLimit maxFeePerGas maxPriorityFeePerGas nonce secretKey sender receiver value => sender
--
-- def TransactionData.receiver : TransactionData → Adr
--   | .zero data gasLimit gasPrice nonce secretKey sender receiver value => receiver
--   | .two accessLists data gasLimit maxFeePerGas maxPriorityFeePerGas nonce secretKey sender receiver value => receiver
--
def TransactionData.gasPrice (baseFee : B256) (txd : TransactionData) : B256 :=
  match txd.fee with
  | .inl gp => gp
  | .inr ⟨mpf, mf⟩ => min mf (baseFee + mpf)

-- def TransactionData.gasPrice (baseFee : B256) : TransactionData → B256
--   | .zero data gasLimit gasPrice nonce secretKey sender receiver value => gasPrice
--   | .two accessLists data gasLimit maxFeePerGas maxPriorityFeePerGas nonce secretKey sender receiver value =>
--     min maxFeePerGas (baseFee + maxPriorityFeePerGas)
--
-- structure TransactionData : Type where
--   (data : List B8L)
--   (gasLimit : List B256)
--   (gasPrice : B256)
--   (nonce : B256)
--   (secretKey : B256)
--   (sender : Adr)
--   (receiver : Adr)
--   (value : List B256)

structure TestSet where
  (name : String)
  (info : Lean.Json)
  (env  : EnvData)
  (pre  : List PreData)
  (post : List PostData)
  (tx   : TransactionData)

def readJsonFile (filename : System.FilePath) : IO Lean.Json := do
  let contents ← IO.FS.readFile filename
  match Lean.Json.parse contents with
  | .ok json => pure json
  | .error err => throw (IO.userError err)

mutual
  partial def StringJsons.toStrings : List ((_ : String) × Lean.Json) → List String
    | [] => []
    | sj :: sjs =>
      (sj.fst :: Lean.Json.toStrings sj.snd) ++ StringJsons.toStrings sjs

  partial def Lean.Jsons.toStrings : List Lean.Json → List String
    | [] => []
    | j :: js => Lean.Json.toStrings j ++ Lean.Jsons.toStrings js

  partial def Lean.Json.toStrings : Lean.Json → List String
    | .null => ["null"]
    | .bool b => [s!"bool : {b}"]
    | .num n => [s!"num : {n}"]
    | .str s => [s!"str : {s}"]
    | .arr js =>
      "arr :" :: (Lean.Jsons.toStrings js.toList).map ("  " ++ ·)
    | .obj m => do
      let kvs := m.toArray.toList
      "obj : " :: (StringJsons.toStrings kvs).map ("  " ++ ·)
end

def Lean.Json.toString (j : Lean.Json) : String := String.joinln j.toStrings


def List.chunksCore {ξ} (m : Nat) : Nat → List ξ → List (List ξ)
  | _, [] => [[]]
  | 0, x :: xs =>
    match chunksCore m m xs with
    | [] => [[], [x]]
    | ys :: yss => [] :: (x :: ys) :: yss
  | n + 1, x :: xs =>
    match chunksCore m n xs with
    | [] => [[x]]
    | ys :: yss => (x :: ys) :: yss

def List.chunks {ξ} (m : Nat) : List ξ → List (List ξ) := List.chunksCore m (m + 1)

def longB8LToStrings (hd : String) (bs : B8L) : List String :=
  match List.chunks 31 bs with
  | [] => [hd]
  | [bs'] => [s!"{hd} : {B8L.toHex bs'}"]
  | bss => s!"{hd} :" :: bss.map (λ bs' => pad (B8L.toHex bs'))

def txdataToStrings (tx : B8L) : List String :=
  match List.chunks 31 tx with
  | [] => ["txdata :"]
  | [bs] => [s!"txdata : {B8L.toHex bs}"]
  | bss => "txdata :" :: bss.map (λ bs => pad (B8L.toHex bs))

def postAcct.toStrings (p : PostData) : List String :=
  fork "Post Acct" [
    [s!"hash : {p.hash.toHex}"],
    [s!"data index : {p.dataIdx}"],
    [s!"gas index : {p.gasIdx}"],
    [s!"value index : {p.valueIdx}"],
    [s!"logs : {B256.toHex p.logs}"],
    txdataToStrings p.txdata
  ]

def Lean.RBMap.toStrings {α β cmp} (m : Lean.RBMap α β cmp)
  (fmt : α × β → List String): List String :=
  let kvs := m.toArray.toList
  fork "map" (kvs.map fmt)

def Stor.toStrings (s : Stor) : List String :=
  let kvs := s.toArray.toList
  let kvToStrings : B256 × B256 → List String :=
    λ nb => [s!"{B256.toHex nb.fst} : {B256.toHex nb.snd}"]
  fork "stor" (kvs.map kvToStrings)

def preAcct.toStrings (p : PreData) : List String :=
  fork "Pre Acct" [
    [s!"address : {p.addr.toHex}"],
    [s!"nonce : {B8L.toHex p.nonce}"],
    [s!"balance : {B8L.toHex p.bal}"],
    p.stor.toStrings,
    [s!"code : {B8L.toHex p.code}"]
  ]

def postToStrings (ps : List PostData) : List String :=
  fork "Post" [List.toStrings postAcct.toStrings ps]

def EnvData.toStrings (e : EnvData) : List String :=
  fork "env" [
    [s!"coinbase : {e.coinbase.toHex}"],
  ]

def preToStrings (l : List PreData) : List String :=
  fork "pre" [List.toStrings preAcct.toStrings l]

def Option.toStrings {ξ : Type u} (f : ξ → List String): Option ξ → List String
  | none => ["none"]
  | some x => fork "some" [f x]

-- (accessLists : Option (List (List Adr)))
-- (data : List B8L)
-- (gasLimit : List B256)
-- (fee : B256 ⊕ (B256 × B256))
-- (nonce : B256)
-- (secretKey : B256)
-- (sender : Adr)
-- (receiver : Adr)
-- (value : List B256)

def AccessList.toStrings (al : AccessList) : List String :=
    fork "accessList" <| al.map <|
      fun
        | ⟨a, ks⟩ =>
          fork "accessEntry" [
            ["address : 0x" ++ a.toHex],
            fork "keys" <| ks.map <| λ k => ["0x" ++ k.toHex]
          ]

def TransactionData.toStrings (txd : TransactionData) : List String :=
  let feeToStrings : (B256 ⊕ (B256 × B256)) → List String :=
    fun
      | .inl gp => ["gasPrice : 0x" ++ gp.toHex]
      | .inr ⟨mpf, mf⟩ =>
        fork "fees" [
          ["maxPriorityFee : 0x" ++ mpf.toHex],
          ["maxFee : 0x" ++ mf.toHex]
        ]

  let bvhsToStrings (bvhs : List B256) : List String :=
    fork "blobVersionedHashes" <| bvhs.map <| λ bvh => ["0x" ++ bvh.toHex]

  let accessListsToStrings (als : List AccessList) : List String :=
    fork "accessLists" <| als.map AccessList.toStrings

  fork "transaction" [
    Option.toStrings accessListsToStrings txd.accessLists,
    Option.toStrings bvhsToStrings txd.bvhs,
    fork "data" [List.toStrings (λ x => [B8L.toHex x]) txd.data],
    fork "gasLimit" [List.toStrings (λ x => [x.toHex]) txd.gasLimit],
    feeToStrings txd.fee,
    [s!"nonce :     {txd.nonce.toHex}"],
    [s!"secretKey : {txd.secretKey.toHex}"],
    [s!"sender : {txd.sender.toHex}"],
    [s!"to : {txd.receiver <&> Adr.toHex}"],
    fork "value" [List.toStrings (λ x => [x.toHex]) txd.value]
  ]

structure Test' where
  (expectedException : Option Exception)
  (baseFee : B256)
  (excessBlobGas : B256)
  (coinbase : Adr)
  (prevRandao : B256)
  (blockGasLimit : B256)
  (number : B256)
  (timestamp : B256)
  (world  : Wor)
  (txdata : B8L)
  (nonce : B256)
  (gasPrice : B256)
  (gasLimit : B256)
  (sender : Adr)
  (receiver : Option Adr)
  (value : B256)
  (calldata : B8L)
  (hash : B256) -- ?
  (logs : B256) -- keccak hash of (RLP-encoded) log items
  (secret : B256)

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

def Test'.toStrings (t : Test') : List String :=
  fork "VM Test" [
    [s!"coinbase : {t.coinbase.toHex}"],
    t.world.toStrings,
    txdataToStrings t.txdata,
    [s!"nonce : 0x{t.nonce.toHex}"],
    [s!"gas price : 0x{t.gasPrice.toHex}"],
    [s!"gas limit : 0x{t.gasLimit.toHex}"],
    [s!"sender : 0x{t.sender.toHex}"],
    [s!"receiver : 0x{(t.receiver <&> Adr.toHex).getD ""}"],
    [s!"value : 0x{t.value.toHex}"],
    longB8LToStrings "calldata" t.calldata,
    [s!"hash : 0x{t.hash.toHex}"],
    [s!"logs : 0x{t.logs.toHex}"],
    [s!"secret : 0x{t.secret.toHex}"]
  ]

def TestSet.toStrings (t : TestSet) : List String :=
  fork "VM Test" [
    ["info ..."],--t.info.toStrings,
    EnvData.toStrings t.env,
    preToStrings t.pre,
    postToStrings t.post,
    t.tx.toStrings
  ]

def TestSet.toString (t : TestSet) : String := String.joinln t.toStrings
def Test.toString (t : Test') : String := String.joinln t.toStrings

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

def Lean.Json.toPostData : Json → IO PostData
  | .obj r => do
    let ex : Option Exception ←
      match (r.find compare "expectException") with
      | none => pure none
      | some j => do
        let exStr ← fromStr j
        match exStr with
        | "TransactionException.TYPE_3_TX_ZERO_BLOBS" => pure <| some .noBlobs
        | "TransactionException.TYPE_3_TX_BLOB_COUNT_EXCEEDED" => pure <| some .tooManyBlobs
        | "TransactionException.TYPE_3_TX_CONTRACT_CREATION" => pure <| some .blobCreation
        | "TransactionException.TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH" => pure <| some .wrongBlobHashVersion
        | _ => IO.throw s!"unknown exception : {exStr}"
    let hsx ← (r.find compare "hash").toIO "cannot retrieve hash bytes" >>= fromStr >>= Hex.from0x
    let hs ← (Hex.toB256? hsx).toIO "cannot convert hash bytes to word"
    let lgx ← (r.find compare "logs").toIO "cannot get logs bytes" >>= fromStr >>= Hex.from0x
    let lg ← (Hex.toB256? lgx).toIO "cannot convert logs bytes to word"
    let txx ← (r.find compare "txbytes").toIO "cannot get tx bytes" >>= fromStr >>= Hex.from0x
    let tx ← (Hex.toB8L txx).toIO "cannot convert tx bytes to word"
    let dgv ← (r.find compare "indexes").toIO "cannot get indexes" >>= Json.fromObj
    let d ← (dgv.find compare "data").toIO "cannot get data" >>= Json.fromNum >>= JsonNumber.toNat
    let g ← (dgv.find compare "gas").toIO "cannot get gas" >>= Json.fromNum >>= JsonNumber.toNat
    let v ← (dgv.find compare "value").toIO "cannot get value" >>= Json.fromNum >>= JsonNumber.toNat
    return ⟨ex, hs, d, g, v, lg, tx⟩
  | _ => IO.throw "Json-to-PostData failed"

def Lean.Json.toB8L (j : Json) : IO B8L := do
  let x ← fromStr j >>= Hex.from0x
  (Hex.toB8L x).toIO ""

def Lean.Json.toAdr (j : Json) : IO Adr := do
  let x ← fromStr j >>= Hex.from0x
  (Hex.toAdr x).toIO ""

def Lean.Json.toOptionAdr (j : Json) : IO (Option Adr) := do
  let s ← fromStr j
  match s with
  | "" => pure .none
  | _ => do
    let s' ← Hex.from0x s
    (Hex.toAdr s').toIO ""

def Lean.Json.toAdrs (j : Json) : IO (List Adr) :=
  fromArr j >>= mapM toAdr

def Lean.Json.toB256? (j : Json) : IO B256 := do
  let x ← fromStr j >>= Hex.from0x
  (Hex.toB256? x).toIO ""

def Lean.Json.toB256P (j : Json) : IO B256 := do
  let x ← fromStr j >>= Hex.from0x
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
  let x ← Hex.from0x xy.fst
  let bs ← (Hex.toB8L x).toIO ""
  let bs' ← xy.snd.toB8L
  return ⟨bs.toB256P, bs'.toB256P⟩

def Lean.Json.toPreData (sj : (_ : String) × Json) : IO PreData := do
  let ax ← Hex.from0x sj.fst
  let a ← (Hex.toAdr ax).toIO ""
  let r ← sj.snd.fromObj
  let b ← (r.find Ord.compare "balance").toIO "" >>= toB8L
  let c ← (r.find Ord.compare "code").toIO "" >>= toB8L
  let n ← (r.find Ord.compare "nonce").toIO "" >>= toB8L
  let l ← (r.find Ord.compare "storage").toIO "" >>= fromObj
  let s ← mapM helper l.toArray.toList
  return ⟨a, n, b, Lean.RBMap.fromList s _, c⟩

def Lean.Json.toEnvData (j : Lean.Json) : IO EnvData := do
  let r ← j.fromObj
  let bfj ← (r.find compare "currentBaseFee").toIO "No basefee"
  let cbj ← (r.find compare "currentCoinbase").toIO "No coinbase"
  let prj ← (r.find compare "currentRandom").toIO "No random"
  let glj ← (r.find compare "currentGasLimit").toIO "No gas limit"
  let tsj ← (r.find compare "currentTimestamp").toIO "No timestamp"
  let nj  ← (r.find compare "currentNumber").toIO "No number"
  let xbgj  ← (r.find compare "currentExcessBlobGas").toIO "No blob gas"
  let bf ← bfj.toB256P
  let cb ← cbj.toAdr
  let pr ← prj.toB256?
  let gl ← glj.toB256P
  let ts ← tsj.toB256P
  let n  ← nj.toB256P
  let xbg  ← xbgj.toB256P
  return {
    baseFee := bf
    coinbase := cb
    prevRandao := pr
    blockGasLimit := gl
    timestamp := ts
    number := n
    excessBlobGas := xbg
  }

def Lean.Json.toPreDatas (j : Lean.Json) : IO (List PreData) := do
  let r ← j.fromObj
  let kvs := r.toArray.toList
  mapM Lean.Json.toPreData kvs

def Lean.Json.toPost (j : Lean.Json) : IO (List PostData) := do
  let r ← j.fromObj
  let j' ← (r.find Ord.compare "Cancun").toIO "no Cancun"
  -- let ⟨k, j'⟩ ← j.fromSingleton
  let l ← j'.fromArr
  let js ← mapM Lean.Json.toPostData l
  return js

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

def Lean.Json.transactionDataType (j : Lean.Json) : IO Nat := do
  let r ← j.fromObj
  match (r.find Ord.compare "gasPrice") with
  | some _ =>
    match r.size with
    | 8 => return 0
    | _ => IO.throw "error : unknown tx type"
  | none =>
    match (r.find Ord.compare "blobVersionedHashes") with
    | none => return 2
    | some _ => return 3

def Lean.Json.toTransactionDataZero (j : Lean.Json) : IO TransactionData := do
  let r ← j.fromObj
  let ds ← (r.find Ord.compare "data").toIO "" >>= fromArr >>= mapM toB8L
  let gls ← (r.find Ord.compare "gasLimit").toIO "" >>= fromArr >>= mapM toB256P
  let gp ← ((r.find Ord.compare "gasPrice").toIO "" >>= toB256P)
  let nc ← ((r.find Ord.compare "nonce").toIO "" >>= toB256P)
  let sk ← (r.find Ord.compare "secretKey").toIO "" >>= toB256?
  let sd ← (r.find Ord.compare "sender").toIO "" >>= toAdr
  let rc ← (r.find Ord.compare "to").toIO "" >>= toOptionAdr
  let vs ← (r.find Ord.compare "value").toIO "" >>= fromArr >>= mapM toB256P
  pure {
    accessLists := none
    bvhs := none
    data := ds
    gasLimit := gls
    fee := .inl gp
    nonce := nc
    secretKey := sk
    sender := sd
    receiver := rc
    value := vs
  }


def Lean.Json.toTransactionDataTwo (j : Lean.Json) : IO TransactionData := do
  let r ← j.fromObj
  let als ← (r.find Ord.compare "accessLists").toIO "" >>= fromArr >>= mapM toAccessList
  let ds ← (r.find Ord.compare "data").toIO "" >>= fromArr >>= mapM toB8L
  let gls ← (r.find Ord.compare "gasLimit").toIO "" >>= fromArr >>= mapM toB256P
  let mpf ← ((r.find Ord.compare "maxPriorityFeePerGas").toIO "" >>= toB256P)
  let mf ← ((r.find Ord.compare "maxFeePerGas").toIO "" >>= toB256P)
  let nc ← ((r.find Ord.compare "nonce").toIO "" >>= toB256P)
  let sk ← (r.find Ord.compare "secretKey").toIO "" >>= toB256?
  let sd ← (r.find Ord.compare "sender").toIO "" >>= toAdr
  let rc ← (r.find Ord.compare "to").toIO "" >>= toOptionAdr
  let vs ← (r.find Ord.compare "value").toIO "" >>= fromArr >>= mapM toB256P
  pure {
    accessLists := als
    bvhs := none
    data := ds
    gasLimit := gls
    fee := .inr ⟨mpf, mf⟩
    nonce := nc
    secretKey := sk
    sender := sd
    receiver := rc
    value := vs
  }

def Lean.Json.toTransactionDataThree (j : Lean.Json) : IO TransactionData := do
  let r ← j.fromObj
  let als ← (r.find Ord.compare "accessLists").toIO "" >>= fromArr >>= mapM toAccessList
  let bvhs ← (r.find Ord.compare "blobVersionedHashes").toIO "" >>= fromArr >>= mapM toB256P
  let ds ← (r.find Ord.compare "data").toIO "" >>= fromArr >>= mapM toB8L
  let gls ← (r.find Ord.compare "gasLimit").toIO "" >>= fromArr >>= mapM toB256P
  let mpf ← ((r.find Ord.compare "maxPriorityFeePerGas").toIO "" >>= toB256P)
  let mf ← ((r.find Ord.compare "maxFeePerGas").toIO "" >>= toB256P)
  let nc ← ((r.find Ord.compare "nonce").toIO "" >>= toB256P)
  let sk ← (r.find Ord.compare "secretKey").toIO "" >>= toB256?
  let sd ← (r.find Ord.compare "sender").toIO "" >>= toAdr
  let rc ← (r.find Ord.compare "to").toIO "" >>= toOptionAdr
  let vs ← (r.find Ord.compare "value").toIO "" >>= fromArr >>= mapM toB256P
  pure {
    accessLists := als
    bvhs := some bvhs
    data := ds
    gasLimit := gls
    fee := .inr ⟨mpf, mf⟩
    nonce := nc
    secretKey := sk
    sender := sd
    receiver := rc
    value := vs
  }

def Lean.Json.toTransactionData (j : Lean.Json) : IO TransactionData := do
  let ty ← j.transactionDataType
  match ty with
  | 0 => do
    j.toTransactionDataZero
  | 2 => do
    j.toTransactionDataTwo
  | 3 => do
    j.toTransactionDataThree
  | n => IO.throw s!"unimplemented tx type : {n}"

def mkTestSet : ((_ : String) × Lean.Json) → IO TestSet
  | ⟨name, js⟩ => do
    let r ← js.fromObj
    let info ← (r.find compare "_info").toIO ""
    let env ← (r.find compare "env").toIO "" >>= Lean.Json.toEnvData
    let pre ← (r.find compare "pre").toIO "" >>= Lean.Json.toPreDatas
    let post ← (r.find compare "post").toIO "" >>= Lean.Json.toPost
    let tx ← (r.find compare "transaction").toIO "" >>= Lean.Json.toTransactionData
    return ⟨name, info, env, pre, post, tx⟩

def Lean.Json.toTestSets (j : Lean.Json) : IO (List TestSet) := do
  let r ← j.fromObj
  let l := r.toArray.toList
  mapM mkTestSet l

def TestSet.world (td : TestSet) : Option Wor :=
  let aux : PreData → Option (Adr × Acct) :=
    fun pd => do
      some  ⟨
        pd.addr,
        {
          nonce := pd.nonce.toB256P
          bal := pd.bal.toB256P
          stor := pd.stor
          code := ByteArray.mk <| Array.mk pd.code
        }
    ⟩
  do let l ← List.mapM aux td.pre
     some <| Lean.RBMap.fromList l _

def getTest (td : TestSet) (p : PostData) : IO Test' := do
  let cd ← (List.get? td.tx.data p.dataIdx).toIO ""
  let gl ← (List.get? td.tx.gasLimit p.gasIdx).toIO ""
  let vl ← (List.get? td.tx.value p.valueIdx).toIO ""
  let w ← td.world.toIO ""
  return {
    expectedException := p.expectedException
    baseFee := td.env.baseFee
    excessBlobGas := td.env.excessBlobGas
    coinbase := td.env.coinbase
    prevRandao := td.env.prevRandao
    blockGasLimit := td.env.blockGasLimit
    number := td.env.number
    timestamp := td.env.timestamp
    world := w
    txdata := p.txdata
    calldata := cd
    gasLimit := gl
    gasPrice := td.tx.gasPrice td.env.baseFee
    nonce := td.tx.nonce
    secret := td.tx.secretKey
    sender := td.tx.sender
    receiver := td.tx.receiver
    value := vl
    hash := p.hash
    logs := p.logs
  }

def getTests (t : TestSet) : IO (List Test') := do
  mapM (getTest t) t.post

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

def Tx.gasPrice (baseFee : B256) (tx : Tx) : B256 :=
  match tx.type with
  | .zero gp _ => gp
  | .two _ mpf mf _ => min mf (baseFee + mpf)
  | .three _ mpf mf _ _ _ => min mf (baseFee + mpf)

def Tx.chainId (tx : Tx) : Nat :=
  match tx.type with
  | .zero _ cid => cid.getD 1
  | .two cid _ _ _ => cid
  | .three cid _ _ _ _ _ => cid

def Tx.accessList (tx : Tx) : AccessList :=
  match tx.type with
  | .zero _ _ => []
  | .two _ _ _ al => al
  | .three _ _ _ al _ _ => al

def Tx.isBlobTx (tx : Tx) : Bool :=
  match tx.type with
  | .three _ _ _ _ _ _ => 1
  | _ => 0

def Tx.blobHashes (tx : Tx) : List B256 :=
  match tx.type with
  | .zero _ _ => []
  | .two _ _ _ _ => []
  | .three _ _ _ _ _ bhs => bhs

def RLP'.toAdr : RLP' → Option Adr
  | .b8s bs => bs.toAdr
  | _ => none

def RLP'.toB256 : RLP' → Option B256
  | .b8s bs => some bs.toB256P
  | _ => none

def RLP'.toAccessEntry : RLP' → Option (Adr × List B256)
  | .list [.b8s ar, .list ksr] => do
    let a ← B8L.toAdr ar
    let ks ← mapM toB256 ksr
    pure ⟨a, ks⟩
  | _ => none

def RLP'.toAccessList : RLP' → Option AccessList
  | .list rs => mapM toAccessEntry rs
  | _ => none

def RLP'.toString (r : RLP') : String := String.join r.toStrings

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

def decodeTxHash : B8L → IO (Tx × B256)
  | [] => IO.throw "error : cannot decode empty bytes"
  | 0x01 :: _ => IO.throw "unimplemented : Type-1 tx decoding"
  | 0x02 :: tbs =>
    match RLP'.decode tbs with
    | RLP'.list [
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
        RLP'.encode <|
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
    match RLP'.decode tbs with
    | RLP'.list [
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
        RLP'.encode <|
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
        B8L.keccak (0x02 :: bs)
      ⟩
    | _ => IO.throw "error : cannot RLP-decode for type-3 tx"
  | bs@(b :: _) =>
    if b ≤ 0xF7
    then IO.throw s!"error : invalid head tx byte : {b.toHex}"
    else
      match RLP'.decode bs with
      | RLP'.list [
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
          RLP'.encode <|
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
