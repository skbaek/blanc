import Lean.Data.Json
import Lean.Data.Json.Parser
import Blanc.Common

structure EnvData where
  (baseFee : B256)
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

structure TransactionData : Type where
  (data : List B8L)
  (gasLimit : List B256)
  (gasPrice : B256)
  (nonce : B256)
  (secretKey : B256)
  (sender : Adr)
  (receiver : Adr)
  (value : List B256)

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

def TransactionData.toStrings (tx : TransactionData) : List String :=
  fork "transaction" [
    fork "data" [listToStrings (λ x => [B8L.toHex x]) tx.data],
    fork "gasLimit" [listToStrings (λ x => [x.toHex]) tx.gasLimit],
    [s!"gasPrice : {tx.gasPrice.toHex}"],
    [s!"nonce :     {tx.nonce.toHex}"],
    [s!"secretKey : {tx.secretKey.toHex}"],
    [s!"sender : {tx.sender.toHex}"],
    [s!"to : {tx.receiver.toHex}"],
    fork "value" [listToStrings (λ x => [x.toHex]) tx.value]
  ]

structure Test where
  (baseFee : B256)
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
  let bf ← bfj.toB256P
  let cb ← cbj.toAdr
  let pr ← prj.toB256?
  let gl ← glj.toB256P
  let ts ← tsj.toB256P
  let n  ← nj.toB256P
  return {
    baseFee := bf
    coinbase := cb
    prevRandao := pr
    blockGasLimit := gl
    timestamp := ts
    number := n
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

def Lean.Json.toTransactionData (j : Lean.Json) : IO TransactionData := do
  let r ← j.fromObj
  let ds ← (r.find Ord.compare "data").toIO "" >>= fromArr >>= mapM toB8L
  let gls ← (r.find Ord.compare "gasLimit").toIO "" >>= fromArr >>= mapM toB256P
  let gp ← ((r.find Ord.compare "gasPrice").toIO "" >>= toB256P)
  let n ← ((r.find Ord.compare "nonce").toIO "" >>= toB256P)
  let sk ← (r.find Ord.compare "secretKey").toIO "" >>= toB256?
  let sd ← (r.find Ord.compare "sender").toIO "" >>= toAdr
  let rc ← (r.find Ord.compare "to").toIO "" >>= toAdr
  let vs ← (r.find Ord.compare "value").toIO "" >>= fromArr >>= mapM toB256P
  return ⟨ds, gls, gp, n, sk, sd, rc, vs⟩

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
    coinbase := td.env.coinbase
    prevRandao := td.env.prevRandao
    blockGasLimit := td.env.blockGasLimit
    number := td.env.number
    timestamp := td.env.timestamp
    world := w
    txdata := p.txdata
    calldata := cd
    gasLimit := gl
    gasPrice := td.tx.gasPrice
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

inductive TxType : Type
  | zero : TxType
  -- access list (T_A)
  | one : AccessList → TxType
  -- access list (T_A), max fee per gas (T_m), max priority fee per gas (T_f)
  | two : AccessList → B256 → B256 → TxType


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

def decodeTxBytes (tbs : B8L) : IO (TxBytesContent × B256) :=
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
