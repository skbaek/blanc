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

structure PostData where
  (hash : B256)
  (dataIdx : Nat)
  (gasIdx : Nat)
  (valueIdx : Nat)
  (logs : B256)
  (txdata : B8L)

inductive TransactionData : Type
  | zero
    (data : List B8L)
    (gasLimit : List B256)
    (gasPrice : B256)
    (nonce : B256)
    (secretKey : B256)
    (sender : Adr)
    (receiver : Adr)
    (value : List B256) : TransactionData
  | two
    (accessLists : List (List Adr))
    (data : List B8L)
    (gasLimit : List B256)
    (maxFeePerGas : B256)
    (maxPriorityFeePerGas : B256)
    (nonce : B256)
    (secretKey : B256)
    (sender : Adr)
    (receiver : Adr)
    (value : List B256) : TransactionData


def TransactionData.gasLimit : TransactionData → List B256
  | .zero data gasLimit gasPrice nonce secretKey sender receiver value  => gasLimit
  | .two accessLists data gasLimit maxFeePerGas maxPriorityFeePerGas nonce secretKey sender receiver value => gasLimit

def TransactionData.data :  TransactionData → List B8L
  | .zero data gasLimit gasPrice nonce secretKey sender receiver value => data
  | .two accessLists data gasLimit maxFeePerGas maxPriorityFeePerGas nonce secretKey sender receiver value => data
def TransactionData.value :  TransactionData → List B256
  | .zero data gasLimit gasPrice nonce secretKey sender receiver value => value
  | .two accessLists data gasLimit maxFeePerGas maxPriorityFeePerGas nonce secretKey sender receiver value => value

def TransactionData.nonce :  TransactionData → B256
  | .zero data gasLimit gasPrice nonce secretKey sender receiver value => nonce
  | .two accessLists data gasLimit maxFeePerGas maxPriorityFeePerGas nonce secretKey sender receiver value => nonce

def TransactionData.secretKey :  TransactionData → B256
  | .zero data gasLimit gasPrice nonce secretKey sender receiver value => secretKey
  | .two accessLists data gasLimit maxFeePerGas maxPriorityFeePerGas nonce secretKey sender receiver value => secretKey

def TransactionData.sender :  TransactionData → Adr
  | .zero data gasLimit gasPrice nonce secretKey sender receiver value => sender
  | .two accessLists data gasLimit maxFeePerGas maxPriorityFeePerGas nonce secretKey sender receiver value => sender

def TransactionData.receiver : TransactionData → Adr
  | .zero data gasLimit gasPrice nonce secretKey sender receiver value => receiver
  | .two accessLists data gasLimit maxFeePerGas maxPriorityFeePerGas nonce secretKey sender receiver value => receiver

def TransactionData.gasPrice (baseFee : B256) : TransactionData → B256
  | .zero data gasLimit gasPrice nonce secretKey sender receiver value => gasPrice
  | .two accessLists data gasLimit maxFeePerGas maxPriorityFeePerGas nonce secretKey sender receiver value =>
    min maxFeePerGas (baseFee + maxPriorityFeePerGas)

-- structure TransactionData : Type where
--   (data : List B8L)
--   (gasLimit : List B256)
--   (gasPrice : B256)
--   (nonce : B256)
--   (secretKey : B256)
--   (sender : Adr)
--   (receiver : Adr)
--   (value : List B256)
structure TestData where
  (info : Lean.Json)
  (env  : EnvData)
  (pre  : List PreData)
  (post : String × List PostData)
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

def postToStrings : (String × List PostData) → List String
  | ⟨s, ps⟩ => fork "Post" [[s], listToStrings postAcct.toStrings ps]

def EnvData.toStrings (e : EnvData) : List String :=
  fork "env" [
    [s!"coinbase : {e.coinbase.toHex}"],
  ]

def preToStrings (l : List PreData) : List String :=
  fork "pre" [listToStrings preAcct.toStrings l]

--inductive TransactionData : Type
--  | zero
--    (data : List B8L)
--    (gasLimit : List B256)
--    (gasPrice : B256)
--    (nonce : B256)
--    (secretKey : B256)
--    (sender : Adr)
--    (receiver : Adr)
--    (value : List B256) : TransactionData
--  | two
--    (accessLists : List (List Adr))
--    (data : List B8L)
--    (gasLimit : List B256)
--    (maxFeePerGas : B256)
--    (maxPriorityFeePerGas : B256)
--    (nonce : B256)
--    (secretKey : B256)
--    (sender : Adr)
--    (receiver : Adr)
--    (value : List B256) : TransactionData

def TransactionData.toStrings : TransactionData → List String
  | .zero
    data
    gasLimit
    gasPrice
    nonce
    secretKey
    sender
    receiver
    value =>
    fork "transaction (Type-0/legacy)" [
      fork "data" [listToStrings (λ x => [B8L.toHex x]) data],
      fork "gasLimit" [listToStrings (λ x => [x.toHex]) gasLimit],
      [s!"gasPrice : {gasPrice.toHex}"],
      [s!"nonce :     {nonce.toHex}"],
      [s!"secretKey : {secretKey.toHex}"],
      [s!"sender : {sender.toHex}"],
      [s!"to : {receiver.toHex}"],
      fork "value" [listToStrings (λ x => [x.toHex]) value]
    ]
  | .two
    accessLists
    data
    gasLimit
    maxFeePerGas
    maxPriorityFeePerGas
    nonce
    secretKey
    sender
    receiver
    value =>
    fork "transaction (Type-2/EIP-1559)" [
      fork "accessLists" <| accessLists.map <|
          λ aas => fork "accessList" <| aas.map <| λ aa => ["0x" ++ aa.toHex],
      fork "data" [listToStrings (λ x => ["0x" ++ B8L.toHex x]) data],
      fork "gasLimit" [listToStrings (λ x => ["0x" ++ x.toHex]) gasLimit],
      [s!"maxFeePerGas : 0x{maxFeePerGas.toHex}"],
      [s!"maxPriorityFeePerGas : 0x{maxPriorityFeePerGas.toHex}"],
      [s!"nonce :0x{nonce.toHex}"],
      [s!"secretKey : 0x{secretKey.toHex}"],
      [s!"sender : 0x{sender.toHex}"],
      [s!"to : 0x{receiver.toHex}"],
      fork "value" [listToStrings (λ x => ["0x" ++ x.toHex]) value]
    ]

-- def TransactionData.toStrings (tx : TransactionData) : List String :=
--   fork "transaction" [
--     fork "data" [listToStrings (λ x => [B8L.toHex x]) tx.data],
--     fork "gasLimit" [listToStrings (λ x => [x.toHex]) tx.gasLimit],
--     [s!"gasPrice : {tx.gasPrice.toHex}"],
--     [s!"nonce :     {tx.nonce.toHex}"],
--     [s!"secretKey : {tx.secretKey.toHex}"],
--     [s!"sender : {tx.sender.toHex}"],
--     [s!"to : {tx.receiver.toHex}"],
--     fork "value" [listToStrings (λ x => [x.toHex]) tx.value]
--   ]
--
structure Test where
  (baseFee : B256)
  (excessBlobGas : B256)
  (blobHashes : Array B256)
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
  (receiver : Adr)
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

def Test.toStrings (t : Test) : List String :=
  fork "VM Test" [
    [s!"coinbase : {t.coinbase.toHex}"],
    t.world.toStrings,
    txdataToStrings t.txdata,
    [s!"nonce : 0x{t.nonce.toHex}"],
    [s!"gas price : 0x{t.gasPrice.toHex}"],
    [s!"gas limit : 0x{t.gasLimit.toHex}"],
    [s!"sender : 0x{t.sender.toHex}"],
    [s!"receiver : 0x{t.receiver.toHex}"],
    [s!"value : 0x{t.value.toHex}"],
    longB8LToStrings "calldata" t.calldata,
    [s!"hash : 0x{t.hash.toHex}"],
    [s!"logs : 0x{t.logs.toHex}"],
    [s!"secret : 0x{t.secret.toHex}"]
  ]

def TestData.toStrings (t : TestData) : List String :=
  fork "VM Test" [
    ["info ..."],--t.info.toStrings,
    EnvData.toStrings t.env,
    preToStrings t.pre,
    postToStrings t.post,
    t.tx.toStrings
  ]

def TestData.toString (t : TestData) : String := String.joinln t.toStrings
def Test.toString (t : Test) : String := String.joinln t.toStrings

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
  | _ => IO.throw "not a string"

def Lean.JsonNumber.toNat : JsonNumber → IO Nat
  | ⟨.ofNat x, 0⟩ => return x
  | ⟨.negSucc _, _⟩ => IO.throw "negative mantissa"
  | ⟨_, e + 1⟩ => IO.throw s!"nonzero exponent : {e + 1}"

def Lean.Json.fromSingleton : Lean.Json → IO (String × Lean.Json)
  | .obj (.node _ .leaf k v .leaf) => return ⟨k, v⟩
  | _ => IO.throw "not a singleton"


def Lean.Json.toPostData : Json → IO PostData
  | .obj r => do
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
    return ⟨hs, d, g, v, lg, tx⟩
  | _ => IO.throw "Json-to-PostData failed"


def Lean.Json.toB8L (j : Json) : IO B8L := do
  let x ← fromStr j >>= Hex.from0x
  (Hex.toB8L x).toIO ""

def Lean.Json.toAdr (j : Json) : IO Adr := do
  let x ← fromStr j >>= Hex.from0x
  (Hex.toAdr x).toIO ""

def Lean.Json.toAdrs (j : Json) : IO (List Adr) :=
  fromArr j >>= mapM toAdr

def Lean.Json.toB256? (j : Json) : IO B256 := do
  let x ← fromStr j >>= Hex.from0x
  (Hex.toB256? x).toIO ""

def Lean.Json.toB256P (j : Json) : IO B256 := do
  let x ← fromStr j >>= Hex.from0x
  let xs ← (Hex.toB8L x).toIO ""
  return (B8L.toB256P xs)

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

def Lean.Json.toPost (j : Lean.Json) : IO (String × List PostData) := do
  let ⟨k, j'⟩ ← j.fromSingleton
  let l ← j'.fromArr
  let js ← mapM Lean.Json.toPostData l
  return ⟨k, js⟩

inductive TxType : Type
  -- Legacy (including EIP-155)
  | zero : TxType
  -- EIP-2930
  | one : TxType
  -- EIP-1559
  | two : TxType
  -- EIP-4844
  -- | three : TxType

def Lean.Json.transactionDataType (j : Lean.Json) : IO TxType := do
  let r ← j.fromObj
  match (r.find Ord.compare "gasPrice") with
  | some _ =>
    match r.size with
    | 8 => return .zero
    | _ => IO.throw "error : unknown tx type, possibly EIP-155"
  | none =>
    match (r.find Ord.compare "blobVersionedHashes") with
    | none => return .two
    -- | some _ => IO.throwreturn .three
    | _ => IO.throw "error : unknown tx type, possibly EIP-4844"

def Lean.Json.toTransactionDataOrig (j : Lean.Json) : IO TransactionData := do
  let r ← j.fromObj
  let ds ← (r.find Ord.compare "data").toIO "" >>= fromArr >>= mapM toB8L
  let gls ← (r.find Ord.compare "gasLimit").toIO "" >>= fromArr >>= mapM toB256P
  let gp ← ((r.find Ord.compare "gasPrice").toIO "" >>= toB256P)
  let n ← ((r.find Ord.compare "nonce").toIO "" >>= toB256P)
  let sk ← (r.find Ord.compare "secretKey").toIO "" >>= toB256?
  let sd ← (r.find Ord.compare "sender").toIO "" >>= toAdr
  let rc ← (r.find Ord.compare "to").toIO "" >>= toAdr
  let vs ← (r.find Ord.compare "value").toIO "" >>= fromArr >>= mapM toB256P
  return .zero ds gls gp n sk sd rc vs

def Lean.Json.toTransactionDataTwo (j : Lean.Json) : IO TransactionData := do
  let r ← j.fromObj
  let al ← (r.find Ord.compare "accessLists").toIO "" >>= fromArr >>= mapM toAdrs
  let ds ← (r.find Ord.compare "data").toIO "" >>= fromArr >>= mapM toB8L
  let gls ← (r.find Ord.compare "gasLimit").toIO "" >>= fromArr >>= mapM toB256P
  let mf ← ((r.find Ord.compare "maxFeePerGas").toIO "" >>= toB256P)
  let mpf ← ((r.find Ord.compare "maxPriorityFeePerGas").toIO "" >>= toB256P)
  let nc ← ((r.find Ord.compare "nonce").toIO "" >>= toB256P)
  let sk ← (r.find Ord.compare "secretKey").toIO "" >>= toB256?
  let sd ← (r.find Ord.compare "sender").toIO "" >>= toAdr
  let rc ← (r.find Ord.compare "to").toIO "" >>= toAdr
  let vs ← (r.find Ord.compare "value").toIO "" >>= fromArr >>= mapM toB256P
  return .two al ds gls mf mpf nc sk sd rc vs

def Lean.Json.toTransactionData (j : Lean.Json) : IO TransactionData := do
  let ty ← j.transactionDataType
  match ty with
  | .zero => do
    .println "type-0 detected"
    j.toTransactionDataOrig
  | .one => IO.throw "unimplemented : type-1 tx"
  | .two => do
    .println "type-2 detected"
    j.toTransactionDataTwo

def Lean.Json.toTestData (j : Lean.Json) : IO TestData := do
  let (_, .obj r) ← j.fromSingleton | IO.throw "not singleton object"
  let info ← (r.find compare "_info").toIO ""
  let env ←  (r.find compare "env").toIO "" >>= Lean.Json.toEnvData
  let pre ←  (r.find compare "pre").toIO "" >>= Lean.Json.toPreDatas
  let post ← (r.find compare "post").toIO "" >>= Lean.Json.toPost
  let tx ←   (r.find compare "transaction").toIO "" >>= Lean.Json.toTransactionData
  return ⟨info, env, pre, post, tx⟩

def TestData.world (td : TestData) : Option Wor :=
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

def getTest (td : TestData) (p : PostData) : IO Test := do
  let cd ← (List.get? td.tx.data p.dataIdx).toIO ""
  let gl ← (List.get? td.tx.gasLimit p.gasIdx).toIO ""
  let vl ← (List.get? td.tx.value p.valueIdx).toIO ""
  let w ← td.world.toIO ""
  return {
    baseFee := td.env.baseFee
    excessBlobGas := td.env.excessBlobGas
    blobHashes := #[]
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

def getTests (t : TestData) : IO (List Test) := do
  have ps := t.post.snd
  mapM (getTest t) ps

def Lean.RBMap.fromSingleton {ξ υ f} (m : RBMap ξ υ f) : Option (ξ × υ) :=
  match m.toList with
  | [kv] => some kv
  | _ => none

def Lean.RBMap.singleton {ξ υ f} (x : ξ) (y : υ) : RBMap ξ υ f := RBMap.empty.insert x y

inductive Tx : Type
  | zero
    (nonce : B256)
    (gasPrice : B256)
    (gasLimit : B256)
    (receiver : Adr)
    (val : B256)
    (calldata : B8L)
    (yParity : Bool)
    (chainId : Option Nat)
    (r : B8L)
    (s : B8L) : Tx
  | two
    (chainId : Nat)
    (nonce : B256)
    (maxPriorityFee : B256)
    (maxFee : B256)
    (gasLimit : B256)
    (receiver : Adr)
    (val : B256)
    (calldata : B8L)
    (accessList : List Adr)
    (yParity : Bool)
    (r : B8L)
    (s : B8L) : Tx

def Tx.val : Tx → B256
  | zero
    nonce
    gasPrice
    gasLimit
    receiver
    val
    calldata
    yParity
    chainId
    r
    s => val
  | two
    chainId
    nonce
    maxPriorityFee
    maxFee
    gasLimit
    receiver
    val
    calldata
    accessList
    yParity
    r
    s => val

def Tx.calldata : Tx → B8L
  | zero
    nonce
    gasPrice
    gasLimit
    receiver
    val
    calldata
    yParity
    chainId
    r
    s => calldata
  | two
    chainId
    nonce
    maxPriorityFee
    maxFee
    gasLimit
    receiver
    val
    calldata
    accessList
    yParity
    r
    s => calldata

def Tx.receiver : Tx → Adr
  | zero
    nonce
    gasPrice
    gasLimit
    receiver
    val
    calldata
    yParity
    chainId
    r
    s => receiver
  | two
    chainId
    nonce
    maxPriorityFee
    maxFee
    gasLimit
    receiver
    val
    calldata
    accessList
    yParity
    r
    s => receiver

def Tx.gasLimit : Tx → B256
  | zero
    nonce
    gasPrice
    gasLimit
    receiver
    val
    calldata
    yParity
    chainId
    r
    s => gasLimit
  | two
    chainId
    nonce
    maxPriorityFee
    maxFee
    gasLimit
    receiver
    val
    calldata
    accessList
    yParity
    r
    s => gasLimit

def Tx.nonce : Tx → B256
  | zero
    nonce
    gasPrice
    gasLimit
    receiver
    val
    calldata
    yParity
    chainId
    r
    s => nonce
  | two
    chainId
    nonce
    maxPriorityFee
    maxFee
    gasLimit
    receiver
    val
    calldata
    accessList
    yParity
    r
    s => nonce

def Tx.gasPrice (baseFee : B256) : Tx → B256
  | zero
    nonce
    gasPrice
    gasLimit
    receiver
    val
    calldata
    yParity
    chainId
    r
    s => gasPrice
  | two
    chainId
    nonce
    maxPriorityFee
    maxFee
    gasLimit
    receiver
    val
    calldata
    accessList
    yParity
    r
    s => min maxFee (baseFee + maxPriorityFee)

def Tx.yParity : Tx → Bool
  | zero
    nonce
    gasPrice
    gasLimit
    receiver
    val
    calldata
    yParity
    chainId
    r
    s => yParity
  | two
    chainId
    nonce
    maxPriorityFee
    maxFee
    gasLimit
    receiver
    val
    calldata
    accessList
    yParity
    r
    s => yParity

def Tx.r : Tx → B8L
  | zero
    nonce
    gasPrice
    gasLimit
    receiver
    val
    calldata
    yParity
    chainId
    r
    s => r
  | two
    chainId
    nonce
    maxPriorityFee
    maxFee
    gasLimit
    receiver
    val
    calldata
    accessList
    yParity
    r
    s => r

def Tx.s : Tx → B8L
  | zero
    nonce
    gasPrice
    gasLimit
    receiver
    val
    calldata
    yParity
    chainId
    r
    s => s
  | two
    chainId
    nonce
    maxPriorityFee
    maxFee
    gasLimit
    receiver
    val
    calldata
    accessList
    yParity
    r
    s => s

--0x02 || rlp([chain_id, nonce, max_priority_fee_per_gas, max_fee_per_gas, gas_limit, destination, amount, data, access_list, signature_y_parity, signature_r, signature_s])

structure TxBytesContent : Type where
  (chainId : Option Nat)
  (yParity : Bool)
  (type : TxType)
  (nonce : B256)
  (gasPrice : B256)
  (gasLimit : B256)
  (receiver : Adr)
  (val : B256)
  (calldata : B8L)
  (r : B8L)
  (s : B8L)
  (acc : List (Adr × List B256))

def RLP'.toAdr : RLP' → Option Adr
  | .b8s bs => bs.toAdr
  | _ => none

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
        .list accessList,
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
            .list accessList
          ]

      let recAdr ← (B8L.toAdr receiver).toIO "cannot convert bytes to receiver address"
      let yp : Bool ←
        match yParity with
        | [] => pure Bool.false
        -- | [0x00] => pure Bool.false
        | [0x01] => pure Bool.true
        | _ => IO.throw s!"invalid yParity value : {yParity.toHex}"
      let aas : List Adr ←
        mapM
          (λ r => r.toAdr.toIO s!"cannot convert RLP to address : {r.toStrings}")
          accessList
      return ⟨
        .two
        chainId.toNat -- (chainId : Nat)
        nonce.toB256P-- (nonce : B256)
        maxPriorityFee.toB256P-- (maxPriorityFee : B256)
        maxFee.toB256P-- (maxFee : B256)
        gasLimit.toB256P-- (gasLimit : B256)
        recAdr -- (receiver : Adr)
        val.toB256P -- (val : B256)
        calldata -- (calldata : B8L)
        aas -- (accessList : List Adr)
        yp -- (yParity : Bool)
        (r.reverse.takeD 32 0).reverse
        (s.reverse.takeD 32 0).reverse,
        B8L.keccak (0x02 :: bs)
      ⟩
    | _ => IO.throw "error : cannot RLP-decode for type-2 tx"
  | 0x03 :: _ => IO.throw "unimplemented : Type-3 tx decoding"
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
        IO.guard (v = 27 ∨ v = 28) "unimplemented : EIP-155 tx handling"
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
        let recAdr ← (B8L.toAdr receiver).toIO "cannot convert bytes to receiver address"
        return ⟨
          .zero
          nonce.toB256P
          gasPrice.toB256P
          gasLimit.toB256P
          recAdr
          val.toB256P
          calldata
          (if (v - 0x1B) = 0 then 0 else 1)
          none
          (r.reverse.takeD 32 0).reverse
          (s.reverse.takeD 32 0).reverse,
          bs.keccak
        ⟩
      | _ => IO.throw "error : cannot RLP-decode for type-0 tx"

  #exit

def decodeLegacyTxBytes (tbs : B8L) : IO (TxBytesContent × B256) :=
  match RLP'.decode tbs with
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
    let recAdr ← (B8L.toAdr receiver).toIO "cannot convert bytes to receiver address"
    return ⟨
      {
        chainId := none
        yParity := if (v - 0x1B) = 0 then 0 else 1
        type := .zero
        nonce    := nonce.toB256P
        gasPrice := gasPrice.toB256P
        gasLimit := gasLimit.toB256P
        receiver := recAdr
        val := val.toB256P
        calldata := calldata
        r := (r.reverse.takeD 32 0).reverse
        s := (s.reverse.takeD 32 0).reverse
        acc := []
      },
      bs.keccak
    ⟩
  | _ => IO.throw "Error : TX bytes decoding failed"

def decodeTxBytes : B8L → IO (TxBytesContent × B256)
  | [] => IO.throw "empty tx bytes"
  | 0x01 :: bs => IO.throw "unimplemented : EIP-2930 transaction"
  | 0x02 :: bs => IO.throw "unimplemented : EIP-1559 transaction"
  | bs => decodeLegacyTxBytes bs
