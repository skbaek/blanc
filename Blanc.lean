import Lean.Data.Json
import Lean.Data.Json.Parser
import Lean.Data.HashSet
import «Blanc».Weth



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

def Bytes.toHexLine (bs : Bytes) : String :=
  s!"hex\"{bs.toHex}\""

def WethByteCode : String :=
  List.foldr
     (λ s0 s1 => s0 ++ "\n" ++ s1)
     "" <| List.map Bytes.toHexLine
        <| List.chunks 31 <| Option.getD weth.compile []

def Strings.join : List String → String
  | [] => ""
  | s :: ss => s ++ "\n" ++ Strings.join ss

def Nibs.toBytes : List Nib → Option Bytes
  | [] => some []
  | [_] => none
  | h0 :: h1 :: hs => (Ox h0 h1 :: ·) <$> Nibs.toBytes hs

def Hex.toBytes (s : String) : Option Bytes :=
  s.data.mapM Hexit.toNib >>= Nibs.toBytes

def Option.toIO {ξ} (o : Option ξ) (msg : String) : IO ξ := do
  match o with
  | none => throw (IO.Error.userError msg)
  | some x => pure x

@[extern "ecrecover_flag"]
opaque ecrecoverFlag : ByteArray → UInt8 → ByteArray → ByteArray

def Bool.toByte : Bool → Byte
  | true => Ox x0 x1
  | false => Ox x0 x0

def Bytes.toBytesArray (bs : Bytes) : ByteArray := ⟨⟨List.map Byte.toB8 bs⟩⟩
def ByteArray.toBytes (a : ByteArray) : Bytes := a.data.toList.map B8.toByte

def ecrecover (h : Word) (v : Bool) (r : Word) (s : Word) : Option Addr :=
  let rsa : ByteArray := Bytes.toBytesArray <| @Bits.toBytes 64 (r ++ s)
  let hsa : ByteArray := Bytes.toBytesArray (@Bits.toBytes 32 h)
  let ri : UInt8 := if v then 1 else 0
  match (ecrecoverFlag hsa ri rsa).toBytes with
  | [] => none
  | b :: pa =>
    if b = 0 ∨ pa.length ≠ 20
    then none
    else some (Bytes.toBits 20 pa)

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

def Lean.Json.toString (j : Lean.Json) : String := Strings.join j.toStrings

def Bits.ordering {n} (xs ys : Bits n) : Ordering :=
  if xs < ys
  then .lt
  else if xs = ys
       then .eq
       else .gt

instance {n} : Ord (Bits n) := ⟨Bits.ordering⟩

def List.compare {ξ : Type u} [Ord ξ] : List ξ → List ξ → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
    match Ord.compare x y with
    | .eq => List.compare xs ys
    | o => o

def B128.compare : B128 → B128 → Ordering
  | ⟨x, y⟩, ⟨x', y'⟩ =>
    match Ord.compare x x' with
    | .eq => Ord.compare y y'
    | o => o

instance : Ord B128 := ⟨B128.compare⟩

def B256.compare : B256 → B256 → Ordering
  | ⟨x, y⟩, ⟨x', y'⟩ =>
    match Ord.compare x x' with
    | .eq => Ord.compare y y'
    | o => o

instance {ξ : Type u} [Ord ξ] : Ord (List ξ) := ⟨List.compare⟩
instance : Ord B256 := ⟨B256.compare⟩

def B8.compareLows (x y : B8) : Ordering :=
  Ord.compare x.lows y.lows

abbrev NTB := Lean.RBMap Nibs Bytes compare
abbrev NTB' := Lean.RBMap (List B8) (List B8) (@List.compare _ ⟨B8.compareLows⟩)

abbrev Stor := Lean.RBMap Word Word compare
abbrev Stor' := Lean.RBMap B256 B256 compare

structure EnvData where
  (baseFee : Word)
  (coinbase : Addr)
  (prevRandao : Word)
  (blockGasLimit : Word)
  (timestamp : Word)
  (number : Word)

structure PreData where
  (addr : Addr)
  (nonce : Bytes)
  (bal : Bytes)
  (stor : Stor')
  (code : Bytes)

structure PostData where
  (hash : Word)
  (dataIdx : Nat)
  (gasIdx : Nat)
  (valueIdx : Nat)
  (logs : B256)
  (txdata : Bytes)

structure TransactionData : Type where
  (data : List Bytes)
  (gasLimit : List Word)
  (gasPrice : Word)
  (nonce : Word)
  (secretKey : Word)
  (sender : Addr)
  (receiver : Addr)
  (value : List Word)

structure TestData where
  (info : Lean.Json)
  (env  : EnvData)
  (pre  : List PreData)
  (post : String × List PostData)
  (tx   : TransactionData)

structure Acct where
  (nonce : Word)
  (bal : Word)
  (stor : Stor')
  (code : Array Byte)

abbrev World' : Type := Lean.RBMap Addr Acct compare

structure Test where
  (baseFee : Word)
  (coinbase : Addr)
  (prevRandao : Word)
  (blockGasLimit : Word)
  (number : Word)
  (timestamp : Word)

  (world  : World')
  (txdata : Bytes)

  (nonce : Word)
  (gasPrice : Word)
  (gasLimit : Word)
  (sender : Addr)
  (receiver : Addr)
  (value : Word)
  (calldata : Bytes)

  (hash : Word) -- ?
  (logs : B256) -- keccak hash of (RLP-encoded) log items
  (secret : Word)

def pad : String → String
  | s => "  " ++ s

def padMid : String -> String
  | s => "│ " ++ s

def padsMid : List String → List String
  | [] => []
  | s :: ss => ("├─" ++ s) :: ss.map padMid

def padsEnd : List String → List String
  | [] => []
  | s :: ss => ("└─" ++ s) :: ss.map pad

def padss : List (List String) -> List String
  | [] => []
  | [ss] => padsEnd ss
  | ss :: sss => padsMid ss ++ padss sss

def fork (s : String) : List (List String) → List String
  | [[s']] => [s ++ "──" ++ s']
  | sss => s :: padss sss

def encloseStrings : List String → List String
  | [] => ["[]"]
  | [s] => ["[" ++ s ++ "]"]
  | ss => "┌─" :: ss.map padMid ++ ["└─"]

def listToStrings {ξ} (f : ξ -> List String) (xs : List ξ) : List String :=
  encloseStrings (xs.map f).flatten

def longBytesToStrings (hd : String) (bs : Bytes) : List String :=
  match List.chunks 31 bs with
  | [] => [hd]
  | [bs'] => [s!"{hd} : {Bytes.toHex bs'}"]
  | bss => s!"{hd} :" :: bss.map (λ bs' => pad (Bytes.toHex bs'))

def txdataToStrings (tx : Bytes) : List String :=
  match List.chunks 31 tx with
  | [] => ["txdata :"]
  | [bs] => [s!"txdata : {Bytes.toHex bs}"]
  | bss => "txdata :" :: bss.map (λ bs => pad (Bytes.toHex bs))

def Word.toHex (w : Word) : String := @Bits.toHex 64 w

def Stor.toStrings (s : Stor) : List String :=
  let kvs := s.toArray.toList
  let kvToStrings : Word × Word → List String :=
    λ nb => [s!"{Word.toHex nb.fst} : {Word.toHex nb.snd}"]
  fork "stor" (kvs.map kvToStrings)

def Stor'.toStrings (s : Stor') : List String :=
  let kvs := s.toArray.toList
  let kvToStrings : B256 × B256 → List String :=
    λ nb => [s!"{Word.toHex nb.fst.toBits} : {Word.toHex nb.snd.toBits}"]
  fork "stor" (kvs.map kvToStrings)

def Acct.toStrings (s : String) (a : Acct) : List String :=
  fork s [
    [s!"nonce : 0x{a.nonce.toHex}"],
    [s!"bal : 0x{a.bal.toHex}"],
    a.stor.toStrings,
    longBytesToStrings "code" a.code.toList
  ]

def postAcct.toStrings (p : PostData) : List String :=
  fork "Post Acct" [
    [s!"hash : {Bits.toHex 64 p.hash}"],
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

def World'.toStrings (w : World') : List String :=
  let kvs := w.toArray.toList
  let kvToStrings : Addr × Acct → List String :=
    fun x => Acct.toStrings (x.fst.toHex 40) x.snd
  fork "world" (kvs.map kvToStrings)

def Nib.toB8 : Nib → B8
  | ⦃b0, b1, b2, b3⦄ =>
    (cond b0 (8 : UInt8) 0) |||
    (cond b1 (4 : UInt8) 0) |||
    (cond b2 (2 : UInt8) 0) |||
    (cond b3 (1 : UInt8) 0)

def B8.toNib (x : B8) : Nib :=
   match x.toBools with
   | ⟨_, _, _, _, b0, b1, b2, b3⟩ => ⦃b0, b1, b2, b3⦄

def NTB'.toStrings (s : NTB') : List String :=
  let kvs := s.toArray.toList
  let kvToStrings : B8s × B8s → List String :=
    λ nb => [s!"{Nibs.toHex (nb.fst.map B8.toNib)} : {nb.snd.toHex}"]
  fork "NTB'" (kvs.map kvToStrings)

def NTB.toStrings (s : NTB) : List String :=
  let kvs := s.toArray.toList
  let kvToStrings : Nibs × Bytes → List String :=
    λ nb => [s!"{nb.fst.toHex} : {nb.snd.toHex}"]
  fork "NTB" (kvs.map kvToStrings)

def preAcct.toStrings (p : PreData) : List String :=
  fork "Pre Acct" [
    [s!"address : {Bits.toHex 40 p.addr}"],
    [s!"nonce : {Bytes.toHex p.nonce}"],
    [s!"balance : {Bytes.toHex p.bal}"],
    p.stor.toStrings,
    [s!"code : {Bytes.toHex p.code}"]
  ]

def postToStrings : (String × List PostData) → List String
  | ⟨s, ps⟩ => fork "Post" [[s], listToStrings postAcct.toStrings ps]

def EnvData.toStrings (e : EnvData) : List String :=
  fork "env" [
    [s!"coinbase : {Bits.toHex 40 e.coinbase}"],
  ]

def preToStrings (l : List PreData) : List String :=
  fork "pre" [listToStrings preAcct.toStrings l]

def TransactionData.toStrings (tx : TransactionData) : List String :=
  fork "transaction" [
    fork "data" [listToStrings (λ x => [Bytes.toHex x]) tx.data],
    fork "gasLimit" [listToStrings (λ x => [Bits.toHex 64 x]) tx.gasLimit],
    [s!"gasPrice : {Bits.toHex 64 tx.gasPrice}"],
    [s!"nonce : {Bits.toHex 64 tx.nonce}"],
    [s!"secretKey : {Bits.toHex 64 tx.secretKey}"],
    [s!"sender : {Bits.toHex 40 tx.sender}"],
    [s!"to : {Bits.toHex 40 tx.receiver}"],
    fork "value" [listToStrings (λ x => [Bits.toHex 64 x]) tx.value]
  ]

def Test.toStrings (t : Test) : List String :=
  fork "VM Test" [
    [s!"coinbase : {t.coinbase.toHex 40}"],
    t.world.toStrings,
    txdataToStrings t.txdata,
    [s!"nonce : 0x{t.nonce.toHex}"],
    [s!"gas price : 0x{t.gasPrice.toHex}"],
    [s!"gas limit : 0x{t.gasLimit.toHex}"],
    [s!"sender : 0x{t.sender.toHex 40}"],
    [s!"receiver : 0x{t.receiver.toHex 40}"],
    [s!"value : 0x{t.value.toHex}"],
    longBytesToStrings "calldata" t.calldata,
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

def TestData.toString (t : TestData) : String := Strings.join t.toStrings
def Test.toString (t : Test) : String := Strings.join t.toStrings

def IO.throw {ξ} (s : String) : IO ξ := MonadExcept.throw <| IO.Error.userError s

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

def Lean.JsonNumber.toString' : JsonNumber → String
  | ⟨x, y⟩ => s!"<mantissa : {x}, exponent : {y}>"

def Lean.JsonNumber.toNat : JsonNumber → IO Nat
  | ⟨.ofNat x, 0⟩ => return x
  | ⟨.negSucc _, _⟩ => IO.throw "negative mantissa"
  | ⟨_, e + 1⟩ => IO.throw s!"nonzero exponent : {e + 1}"

def Lean.Json.fromSingleton : Lean.Json → IO (String × Lean.Json)
  | .obj (.node _ .leaf k v .leaf) => return ⟨k, v⟩
  | _ => IO.throw "not a singleton"

def Hex.from0x : String → IO String
  | ⟨'0' :: 'x' :: s⟩ => return ⟨s⟩
  | _ => IO.throw "prefix not 0x"

def Lean.Json.toPostData : Json → IO PostData
  | .obj r => do
    let hsx ← (r.find compare "hash").toIO "cannot retrieve hash bytes" >>= fromStr >>= Hex.from0x
    let hs ← (Hex.toBits 64 hsx).toIO "cannot convert hash bytes to word"
    let lgx ← (r.find compare "logs").toIO "cannot get logs bytes" >>= fromStr >>= Hex.from0x
    let lg ← (Hex.toBits 64 lgx).toIO "cannot convert logs bytes to word"
    let txx ← (r.find compare "txbytes").toIO "cannot get tx bytes" >>= fromStr >>= Hex.from0x
    let tx ← (Hex.toBytes txx).toIO "cannot convert tx bytes to word"
    let dgv ← (r.find compare "indexes").toIO "cannot get indexes" >>= Json.fromObj
    let d ← (dgv.find compare "data").toIO "cannot get data" >>= Json.fromNum >>= JsonNumber.toNat
    let g ← (dgv.find compare "gas").toIO "cannot get gas" >>= Json.fromNum >>= JsonNumber.toNat
    let v ← (dgv.find compare "value").toIO "cannot get value" >>= Json.fromNum >>= JsonNumber.toNat
    return ⟨hs, d, g, v, lg.toB256, tx⟩
  | _ => IO.throw "Json-to-PostData failed"

def Lean.Json.toBytes (j : Json) : IO Bytes := do
  let x ← fromStr j >>= Hex.from0x
  (Hex.toBytes x).toIO ""

def Lean.Json.toBits (n : Nat) (j : Json) : IO (Bits (4 * n)) := do
  let x ← fromStr j >>= Hex.from0x
  (Hex.toBits n x).toIO ""

def helper (xy :(_ : String) × Lean.Json) : IO (B256 × B256) := do
  let x ← Hex.from0x xy.fst
  let bs ← (Hex.toBytes x).toIO ""
  let bs' ← xy.snd.toBytes
  return ⟨(Bytes.toBits 32 bs).toB256, (Bytes.toBits 32 bs').toB256⟩

def Lean.Json.toPreData (sj : (_ : String) × Json) : IO PreData := do
  let ax ← Hex.from0x sj.fst
  let a ← (Hex.toBits 40 ax).toIO ""
  let r ← sj.snd.fromObj
  let b ← (r.find Ord.compare "balance").toIO "" >>= toBytes
  let c ← (r.find Ord.compare "code").toIO "" >>= toBytes
  let n ← (r.find Ord.compare "nonce").toIO "" >>= toBytes
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
  let bf ← bfj.toBytes
  let cb ← cbj.toBytes
  let pr ← prj.toBytes
  let gl ← glj.toBytes
  let ts ← tsj.toBytes
  let n  ← nj.toBytes
  return {
    baseFee := bf.toBits 32,
    coinbase := cb.toBits 20,
    prevRandao := pr.toBits 32,
    blockGasLimit := gl.toBits 32
    timestamp := ts.toBits 32
    number := n.toBits 32
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

def Bytes.toWord : Bytes → Word := Bytes.toBits 32

def Lean.Json.toTransactionData (j : Lean.Json) : IO TransactionData := do
  let r ← j.fromObj
  let ds ← (r.find Ord.compare "data").toIO "" >>= fromArr >>= mapM toBytes
  let gls ← (r.find Ord.compare "gasLimit").toIO "" >>= fromArr >>= mapM toBytes
  let gp ← ((r.find Ord.compare "gasPrice").toIO "" >>= toBytes) <&> Bytes.toWord
  let n ← ((r.find Ord.compare "nonce").toIO "" >>= toBytes) <&> Bytes.toWord
  let sk ← (r.find Ord.compare "secretKey").toIO "" >>= toBits 64
  let sd ← (r.find Ord.compare "sender").toIO "" >>= toBits 40
  let rc ← (r.find Ord.compare "to").toIO "" >>= toBits 40
  let vs ← (r.find Ord.compare "value").toIO "" >>= fromArr >>= mapM toBytes
  return ⟨ds, gls.map Bytes.toWord, gp, n, sk, sd, rc, vs.map Bytes.toWord⟩

def Lean.Json.toTestData (j : Lean.Json) : IO TestData := do
  let (_, .obj r) ← j.fromSingleton | IO.throw "not singleton object"
  let info ← (r.find compare "_info").toIO ""
  let env ←  (r.find compare "env").toIO "" >>= Lean.Json.toEnvData
  let pre ←  (r.find compare "pre").toIO "" >>= Lean.Json.toPreDatas
  let post ← (r.find compare "post").toIO "" >>= Lean.Json.toPost
  let tx ←   (r.find compare "transaction").toIO "" >>= Lean.Json.toTransactionData
  return ⟨info, env, pre, post, tx⟩

def TestData.world (td : TestData) : World' :=
  let aux : PreData → (Addr × Acct) :=
    fun pd => ⟨
      pd.addr,
      {
        nonce := pd.nonce.toBits 32,
        bal := pd.bal.toBits 32
        stor := pd.stor
        code := Array.mk pd.code
      }
    ⟩
  Lean.RBMap.fromList (td.pre.map aux) _

def getTest (td : TestData) (p : PostData) : IO Test := do
  let cd ← (List.get? td.tx.data p.dataIdx).toIO ""
  let gl ← (List.get? td.tx.gasLimit p.gasIdx).toIO ""
  let vl ← (List.get? td.tx.value p.valueIdx).toIO ""
  return {
    baseFee := td.env.baseFee
    coinbase := td.env.coinbase
    prevRandao := td.env.prevRandao
    blockGasLimit := td.env.blockGasLimit
    number := td.env.number
    timestamp := td.env.timestamp
    world := td.world
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

def hpAux' : B8s → (Option B8 × B8s)
  | [] => ⟨none, []⟩
  | n :: ns =>
    match hpAux' ns with
    | ⟨none, bs⟩ => ⟨some n, bs⟩
    | ⟨some m, bs⟩ => ⟨none, ((n <<< 4) ||| m.lows) :: bs⟩

def hpAux : Nibs → (Option Nib × Bytes)
  | [] => ⟨none, []⟩
  | n :: ns =>
    match hpAux ns with
    | ⟨none, bs⟩ => ⟨some n, bs⟩
    | ⟨some m, bs⟩ => ⟨none, (n ++ m) :: bs⟩

def hp' (ns : B8s) (t : Bool) : B8s :=
  match hpAux' ns with
  | ⟨none, bs⟩ => (cond t (0x20) 0) :: bs
  | ⟨some n, bs⟩ => ((cond t 0x30 0x10) ||| n.lows) :: bs

def hp (ns : Nibs) (t : Bool) : Bytes :=
  match hpAux ns with
  | ⟨none, bs⟩ => ⦃0, 0, t, 0, 0, 0, 0, 0⦄ :: bs
  | ⟨some n, bs⟩ => (⦃0, 0, t, 1⦄ ++ n) :: bs

def commonPrefixCore : Nibs → Nibs → Nibs
  | [], _ => []
  | _, [] => []
  | n :: ns, n' :: ns' =>
    if n = n' then n :: commonPrefixCore ns ns'
    else []
def commonPrefix (n : Nib) (ns : Nibs) : List Nibs → Option Nibs
  | [] => some (n :: ns)
  | ns' :: nss =>
    match commonPrefixCore (n :: ns) ns' with
    | [] => none
    | (n' :: ns'') => commonPrefix n' ns'' nss

def commonPrefixCore' : B8s → B8s → B8s
  | [], _ => []
  | _, [] => []
  | n :: ns, n' :: ns' =>
    if n = n' then n :: commonPrefixCore' ns ns'
    else []
def commonPrefix' (n : B8) (ns : B8s) : List B8s → Option B8s
  | [] => some (n :: ns)
  | ns' :: nss =>
    match commonPrefixCore' (n :: ns) ns' with
    | [] => none
    | (n' :: ns'') => commonPrefix' n' ns'' nss

def NTB.empty : NTB := Lean.RBMap.empty
def NTB'.empty : NTB' := Lean.RBMap.empty

def sansPrefix : Nibs → Nibs → Option Nibs
  | [], ns => some ns
  | _, [] => none
  | n :: ns, n' :: ns' =>
    if n = n' then sansPrefix ns ns' else none
def sansPrefix' : B8s → B8s → Option B8s
  | [], ns => some ns
  | _, [] => none
  | n :: ns, n' :: ns' =>
    if n = n' then sansPrefix' ns ns' else none

def insertSansPrefix (pfx : Nibs) (m : NTB) (ns : Nibs) (bs : Bytes) : Option NTB := do
  (m.insert · bs) <$> sansPrefix pfx ns

def insertSansPrefix' (pfx : B8s) (m : NTB') (ns : B8s) (bs : B8s) : Option NTB' := do
  (m.insert · bs) <$> sansPrefix' pfx ns

def NTB'.factor (m : NTB') : Option (B8s × NTB') := do
  let ((n :: ns) :: nss) ← some (m.toList.map Prod.fst) | none
  let pfx ← commonPrefix' n ns nss
  let m' ← Lean.RBMap.foldM (insertSansPrefix' pfx) NTB'.empty m
  some ⟨pfx, m'⟩

def NTB.factor (m : NTB) : Option (Nibs × NTB) := do
  let ((n :: ns) :: nss) ← some (m.toList.map Prod.fst) | none
  let pfx ← commonPrefix n ns nss
  let m' ← Lean.RBMap.foldM (insertSansPrefix pfx) NTB.empty m
  some ⟨pfx, m'⟩

structure NTBs : Type where
  (x0 : NTB) (x1 : NTB) (x2 : NTB) (x3 : NTB)
  (x4 : NTB) (x5 : NTB) (x6 : NTB) (x7 : NTB)
  (x8 : NTB) (x9 : NTB) (xA : NTB) (xB : NTB)
  (xC : NTB) (xD : NTB) (xE : NTB) (xF : NTB)

structure NTBs' : Type where
  (x0 : NTB') (x1 : NTB') (x2 : NTB') (x3 : NTB')
  (x4 : NTB') (x5 : NTB') (x6 : NTB') (x7 : NTB')
  (x8 : NTB') (x9 : NTB') (xA : NTB') (xB : NTB')
  (xC : NTB') (xD : NTB') (xE : NTB') (xF : NTB')

def NTBs'.empty : NTBs' :=
  ⟨ .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty ⟩

def NTBs.empty : NTBs :=
  ⟨ .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty ⟩

def NTBs'.update (js : NTBs') (f : NTB' → NTB') (k : B8) : NTBs' :=
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

def NTBs.update (js : NTBs) (f : NTB → NTB) : Nib → NTBs
  | ⦃0, 0, 0, 0⦄ => { js with x0 := f js.x0}
  | ⦃0, 0, 0, 1⦄ => { js with x1 := f js.x1}
  | ⦃0, 0, 1, 0⦄ => { js with x2 := f js.x2}
  | ⦃0, 0, 1, 1⦄ => { js with x3 := f js.x3}
  | ⦃0, 1, 0, 0⦄ => { js with x4 := f js.x4}
  | ⦃0, 1, 0, 1⦄ => { js with x5 := f js.x5}
  | ⦃0, 1, 1, 0⦄ => { js with x6 := f js.x6}
  | ⦃0, 1, 1, 1⦄ => { js with x7 := f js.x7}
  | ⦃1, 0, 0, 0⦄ => { js with x8 := f js.x8}
  | ⦃1, 0, 0, 1⦄ => { js with x9 := f js.x9}
  | ⦃1, 0, 1, 0⦄ => { js with xA := f js.xA}
  | ⦃1, 0, 1, 1⦄ => { js with xB := f js.xB}
  | ⦃1, 1, 0, 0⦄ => { js with xC := f js.xC}
  | ⦃1, 1, 0, 1⦄ => { js with xD := f js.xD}
  | ⦃1, 1, 1, 0⦄ => { js with xE := f js.xE}
  | ⦃1, 1, 1, 1⦄ => { js with xF := f js.xF}

def NTBs.insert (js : NTBs) : Nibs → Bytes → NTBs
  | [], _ => js
  | n :: ns, bs => js.update (Lean.RBMap.insert · ns bs) n

def NTBs'.insert (js : NTBs') : B8s → B8s → NTBs'
  | [], _ => js
  | n :: ns, bs => js.update (Lean.RBMap.insert · ns bs) n

mutual
  def nodeComp' : Nat → NTB' → RLP'
    | 0, _ => .b8s []
    | k + 1, j =>
      if j.isEmpty
      then .b8s []
      else let r := structComp' k j
           if r.encode.length < 32
           then r
           else .b8s <| r.encode.keccak.toB8s

  def structComp' : Nat → NTB' → RLP'
    | 0, _ => .b8s []
    | k + 1, j =>
      if j.isEmpty
      -- then .list (.replicate 17 <| .bytes []) -- what should be returned
      then .b8s [] -- what devtools actually return
      else if j.isSingleton
           then match j.toList with
                | [(k, v)] => .list [.b8s (hp' k 1), .b8s v]
                | _ => .b8s [] -- unreachable code
           else match j.factor with
                | none =>
                  let js := Lean.RBMap.fold NTBs'.insert NTBs'.empty j
                  .list [ nodeComp' k js.x0, nodeComp' k js.x1, nodeComp' k js.x2,
                          nodeComp' k js.x3, nodeComp' k js.x4, nodeComp' k js.x5,
                          nodeComp' k js.x6, nodeComp' k js.x7, nodeComp' k js.x8,
                          nodeComp' k js.x9, nodeComp' k js.xA, nodeComp' k js.xB,
                          nodeComp' k js.xC, nodeComp' k js.xD, nodeComp' k js.xE,
                          nodeComp' k js.xF, .b8s (j.findD [] []) ]
                | some (pfx, j') => .list [.b8s (hp' pfx 0), nodeComp' k j']
end

mutual
  def nodeComp : Nat → NTB → RLP
    | 0, _ => .bytes []
    | k + 1, j =>
      if j.isEmpty
      then .bytes []
      else let r := structComp k j
           if r.encode.length < 32
           then r
           else .bytes <| @Bits.toBytes 32 r.encode.keccak

  def structComp : Nat → NTB → RLP
    | 0, _ => .bytes []
    | k + 1, j =>
      if j.isEmpty
      -- then .list (.replicate 17 <| .bytes []) -- what should be returned
      then .bytes [] -- what devtools actually return
      else if j.isSingleton
           then match j.toList with
                | [(k, v)] => .list [.bytes (hp k 1), .bytes v]
                | _ => .bytes [] -- unreachable code
           else match j.factor with
                | none =>
                  let js := Lean.RBMap.fold NTBs.insert NTBs.empty j
                  .list [ nodeComp k js.x0, nodeComp k js.x1, nodeComp k js.x2,
                          nodeComp k js.x3, nodeComp k js.x4, nodeComp k js.x5,
                          nodeComp k js.x6, nodeComp k js.x7, nodeComp k js.x8,
                          nodeComp k js.x9, nodeComp k js.xA, nodeComp k js.xB,
                          nodeComp k js.xC, nodeComp k js.xD, nodeComp k js.xE,
                          nodeComp k js.xF, .bytes (j.findD [] []) ]
                | some (pfx, j') => .list [.bytes (hp pfx 0), nodeComp k j']
end


def List.maxD {ξ} [Max ξ] : List ξ → ξ → ξ
  | [], y => y
  | x :: xs, y => maxD xs (max x y)

def NTB.maxKeyLength (j : NTB) : Nat := (j.toList.map (List.length ∘ Prod.fst)).maxD 0
def NTB'.maxKeyLength (j : NTB') : Nat := (j.toList.map (List.length ∘ Prod.fst)).maxD 0

def collapse (j : NTB) : RLP := structComp (2 * (j.maxKeyLength + 1)) j
def collapse' (j : NTB') : RLP' := structComp' (2 * (j.maxKeyLength + 1)) j

def trie (j : NTB) : Word :=
  let bs := (collapse j).encode
  bs.keccak

def trie' (j : NTB') : B256 :=
  let bs := (collapse' j).encode
  bs.keccak

def Word.toBytes (w : Word) : Bytes := (@Bits.toBytes 32 w)
def Word.toRLP (w : Word) : RLP := .bytes w.toBytes
def B256.toRLP (w : B256) : RLP' := .b8s w.toB8s
def Word.keccak (w : Word) : Word := (@Bits.toBytes 32 w).keccak
def B16.toB8s (x : B16) : List B8 := [x.highs, x.lows]
def B32.toB8s (x : B32) : List B8 := x.highs.toB8s ++ x.lows.toB8s
def B8.toB4s (x : B8) : List B8 := [x.highs, x.lows]
def B16.toB4s (x : B16) : List B8 := x.highs.toB4s ++ x.lows.toB4s
def B32.toB4s (x : B32) : List B8 := x.highs.toB4s ++ x.lows.toB4s
def B64.toB4s (x : B64) : List B8 := x.highs.toB4s ++ x.lows.toB4s
def B128.toB4s (x : B128) : List B8 := x.1.toB4s ++ x.2.toB4s
def B256.toB4s (x : B256) : List B8 := x.1.toB4s ++ x.2.toB4s
def B256.keccak (x : B256) : B256 := B8s.keccak <| x.toB8s

def Stor'.toNTB (s : Stor') : NTB :=
  let f : NTB → B256 → B256 → NTB :=
    λ j k v =>
      j.insert
        (@Bits.toNibs 64 (Word.keccak k.toBits))
        (RLP.encode <| .bytes <| Bytes.sig <| @Bits.toBytes 32 v.toBits)
         --k.keccak.toB4s
         --((RLP.encode <| .bytes <| Bytes.sig <| v.toB8s.map B8.toByte).map Byte.toB8)
  Lean.RBMap.fold f NTB.empty s

def Stor'.toNTB' (s : Stor') : NTB' :=
  let f : NTB' → B256 → B256 → NTB' :=
    λ j k v =>
      j.insert
        k.keccak.toB4s
        ((RLP.encode <| .bytes <| Bytes.sig <| v.toB8s.map B8.toByte).map Byte.toB8)
  Lean.RBMap.fold f NTB'.empty s

def Stor.toNTB (s : Stor) : NTB :=
  let f : NTB → Word → Word → NTB :=
    λ j k v =>
      j.insert
        (@Bits.toNibs 64 k.keccak)
        (RLP.encode <| .bytes <| Bytes.sig <| @Bits.toBytes 32 v)
  Lean.RBMap.fold f NTB.empty s


def Acct.toVal (a : Acct) (w : Word) : Bytes :=
  RLP.encode <| .list [
    .bytes a.nonce.toBytes.sig, --a.nonce,
    .bytes a.bal.toBytes.sig, --a.bal,
    Word.toRLP w,
    Word.toRLP <| Bytes.keccak a.code.toList

  ]

def Addr.toB8s (a : Addr) : B8s :=
  (@Bits.toBytes 20 a).map Byte.toB8

def Nib.toHex (n : Nib) : String := ⟨[n.toHexit]⟩

def compareRLP : RLP → RLP' → Option Unit
  | .bytes xs, .b8s ys =>
    if (xs = List.map B8.toByte ys)
    then some ()
    else none
  | .list [], .list [] => some ()
  | .list (x :: xs), .list (y :: ys) => do
    (compareRLP x y)
    compareRLP (.list xs) (.list ys)
  | _, _ => none

def toKeyVal' (pr : Addr × Acct) : B8s × B8s :=
  let ad := pr.fst
  let ac := pr.snd
  ⟨
    let key' := ad.toB8s.keccak.toB4s
    -- dbg_trace "key' : {@List.toString _ ⟨λ x => x.toNib.toHex⟩ key'} "
    key',
    let val' :=
      RLP'.encode <| .list [
        .b8s (ac.nonce.toBytes.sig.map Byte.toB8), --a.nonce,
        .b8s (ac.bal.toBytes.sig.map Byte.toB8), --a.bal,
        B256.toRLP (trie' ac.stor.toNTB'),
        B256.toRLP <| (Bytes.keccak ac.code.toList).toB256
      ]
    -- dbg_trace "val : {@List.toString _ ⟨B8.toHex⟩ val'}"
    val'
  ⟩

def G_txcreate : Nat := 32000
def G_accesslistaddress : Nat := 2400
def G_accessliststorage : Nat := 1900
def G_initcodeword : Nat := 2

def initCodeCost (cd : Bytes) : Nat :=
  G_initcodeword * ((cd.length / 32) + if 32 ∣ cd.length then 0 else 1)


instance : Hashable Addr := ⟨Bits.toB64 ∘ @Bits.suffix 64 96⟩
instance : Hashable (Addr × Word) := ⟨Bits.toB64 ∘ @Bits.suffix 64 96 ∘ Prod.fst⟩
instance : Hashable (Addr × B256) := ⟨Bits.toB64 ∘ @Bits.suffix 64 96 ∘ Prod.fst⟩

abbrev AddrSet : Type := @Std.HashSet Addr _ _ --⟨Bits.toUInt64 ∘ @Bits.suffix 64 96⟩
abbrev KeySet : Type := @Std.HashSet (Addr × B256) _ _

structure Accrual where
  (dest : List Addr) -- A_s
  (adrs : AddrSet) -- A_a
  (keys : KeySet) -- A_k
  (ref : Nat) -- A_r
  (logs : List RLP') -- A_l
  (touched : AddrSet) -- A_t
  -- (sac : Nat) -- A_r

def Stack' : Type := List B256

structure Machine where
  (gas : Nat) -- μ_g
  (pc : Nat) -- μ_pc
  (mem : Array Byte) -- μ_m
  (ret : Bytes) -- μ_o
  (stk : Stack') -- μ_s
  (act : Nat) -- μ_i

def ceilDiv (m n : Nat) := m / n + if m % n = 0 then 0 else 1

-- μ_i : no need to make it a separate field of Machine,
-- when it is completely determined by Machine.mem
def Machine.msz (m : Machine) : Nat := ceilDiv m.mem.size 32

structure Block where
  (baseFee : Word) -- H_f
  (ben : Addr) -- H_c
  (prevRandao : Word) -- H_a
  (gasLimit : Word) -- H_l
  (timestamp : Word) -- H_s
  (number : Word) -- H_s
  (chainId : Word) -- β

structure Env' where
  (cta : Addr) -- contract address (YP : a)
  (oga : Addr) -- origin address (YP : o)
  (gpr : B256) -- gas price (YP : p)
  (cld : Bytes) -- calldata (YP : d)
  (cla : Addr) -- caller Addr (YP : s)
  (clv : Word) -- callvalue (YP : v)
  (code : Array Byte) -- contract code  (YP : b)
  (blk : Block) -- block (YP : H)
  (exd : Nat) -- execution depth (YP : e)
  (wup : Bool) -- World-State update permission (YP : w)

structure State' where
  (wld : World')
  (mcn : Machine)
  (acr : Accrual)
  (env : Env')

structure Ξ.Result where
  (wld : Option World')
  (gas : Nat)
  (acr : Accrual)
  (ret : Option Bytes)

-- YP says that this type should also have a field for
-- execution environment, but it was omitted since the
-- environment does not change and is already known.
structure exec.Result where
  (wld : Option World')
  (mcn : Machine)
  (acr : Accrual)
  (ret : Option Bytes)

inductive Inst : Type
  | last : Linst → Inst
  | next : Ninst → Inst
  | jump : Jinst → Inst

lemma List.length_takeD {ξ : Type u} (n : Nat) (xs : List ξ) (x : ξ) :
    (List.takeD n xs x).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [takeD]

def Nat.decrement : Nat → Nat → Option Nat
  | m, 0 => some m
  | 0, _ + 1 => none
  | m + 1, n + 1 => Nat.decrement m n

def Bytes.jumpable : Bytes → Nat → Nat → Bool
  | [], _, 0 => (dbg_trace "false-0" ; false)
  | b :: _, m + 1, 0 => (dbg_trace "not jumpable to : {b.toHex}, m = {m}" ; false)
  | ⦃0, 1, 0, 1, 1, 0, 1, 1⦄ :: _, 0, 0 => true
  | _ :: _, 0, 0 => (dbg_trace "false-2" ; false)
  | [], _, _ + 1 => (dbg_trace "false-3" ; false)
  | _ :: bs, m + 1, n + 1 => Bytes.jumpable bs m n
  | b :: bs, 0, n + 1 =>
    if (Ox x5 xF ≤ b ∧ b ≤ Ox x7 xF)
    then Bytes.jumpable bs (b - Ox x5 xF).toNat n
    else Bytes.jumpable bs 0 n

def Jinst.toString : Jinst → String
  | .jump => "JUMP"
  | .jumpdest => "JUMPDEST"
  | .jumpi => "JUMPI"

def Inst.toString : Inst → String
  | .next n => n.toString
  | .jump j => j.toString
  | .last l => l.toString

def noPushBefore (cd : Array Byte) : Nat → Nat → Bool
  | 0, _ => true
  | _, 0 => true
  | k + 1, m + 1 =>
    match cd.get? k with
    | none => noPushBefore cd k m
    | some b =>
      if (b < (Ox x7 xF - m.toByte) || Ox x7 xF < b)
      then noPushBefore cd k m
      else if noPushBefore cd k 32
           then dbg_trace "jumpdest check : is a push arg" ; false
           else noPushBefore cd k m

def ByteArray.jumpable (cd : Array Byte) (k : Nat) : Bool :=
  if cd.get? k = some (Jinst.toByte .jumpdest)
  then noPushBefore cd k 32
  else dbg_trace s!"jumpdest check : no jumpdest op, loc : {k}" ; false

def State'.jumpable (s : State') (k : Nat) : Bool :=
  if s.env.code.get? k = some (Jinst.toByte .jumpdest)
  then noPushBefore s.env.code k 32
  else dbg_trace s!"jumpdest check : no jumpdest op, loc : {k}" ; false

  --match s.wld.find? s.env.cta with
  --| none => dbg_trace "jumpdest check : no account" ; false
  ---- | some a => a.code.jumpable 0 k
  --| some a => ByteArray.jumpable a.code k

def Array.sliceD {ξ : Type u} (xs : Array ξ) : Nat → Nat → ξ → List ξ
  | _, 0, _ => []
  | m, n + 1, d => xs.getD m d :: Array.sliceD xs (m + 1) n d

lemma Array.length_sliceD {ξ} {xs : Array ξ} {m n x} :
    (Array.sliceD xs m n x).length = n := by
  induction n generalizing m with
  | zero => simp [sliceD]
  | succ n ih => simp [sliceD, List.length, ih]

def State'.instCore (s : State') : Option Inst :=
  match s.env.code.get? s.mcn.pc with
  | none => some (.last .stop)
  | some b =>
    (b.toRinst? <&> (.next ∘ .reg)) <|>
    (b.toXinst? <&> (.next ∘ .exec)) <|>
    (b.toJinst? <&> .jump) <|>
    (b.toLinst? <&> .last) <|>
    ( if h : 95 ≤ b.toNat ∧ b.toNat ≤ 127
      then let len := b.toNat - 95
           let slc := s.env.code.sliceD (s.mcn.pc + 1) len 0
           let h_slc : slc.length ≤ 32 := by
             simp [len, slc, Array.length_sliceD, h.right]
           some (.next <| .push slc h_slc)
      else none )

def State'.inst (s : State') : Option Inst :=
  -- dbg_trace "remaining gas : {s.mcn.gas}"
  match s.instCore with
  | none =>
    -- dbg_trace "no inst"
    none
  | some i =>
    -- dbg_trace s!"fetched inst : {i.toString}" ;
    some i

  -- match s.wld.find? s.env.cta with
  -- | none => some (.last .stop)
  -- | some a =>
  --   match a.code.get? s.mcn.pc with
  --   | none => return (.last .stop)
  --   | some b =>
  --     (b.toRinst? <&> (.next ∘ .reg)) <|>
  --     (b.toXinst? <&> (.next ∘ .exec)) <|>
  --     (b.toJinst? <&> .jump) <|>
  --     (b.toLinst? <&> .last) <|>
  --     ( if h : 95 ≤ b.toNat ∧ b.toNat ≤ 127
  --       then let len := b.toNat - 95
  --            let slc := a.code.sliceD (s.mcn.pc + 1) len 0
  --            let h_slc : slc.length ≤ 32 := by
  --              simp [len, slc, List.sliceD, h.right]
  --            some (.next <| .push slc h_slc)
  --       else none )

def g_zero : Nat := 0
def gVerylow : Nat := 3
def gLow : Nat := 5
def g_mid : Nat := 8
def g_exp : Nat := 10
def g_expbyte : Nat := 50

def safeSub {ξ} [Sub ξ] [LE ξ] [@DecidableRel ξ (· ≤ ·)] (x y : ξ) : Option ξ :=
  if y ≤ x then some (x - y) else none

def State'.deductGas (s : State') (c : Nat) : Option Nat := safeSub s.mcn.gas c


def Acct.Empty (a : Acct) : Prop :=
  a.code = #[] ∧ a.nonce = 0 ∧ a.bal = 0

def Dead (w : World') (a : Addr) : Prop :=
  match w.find? a with
  | none => True
  | some x => x.Empty

def World'.balAt (w : World') (a : Addr) : Word :=
  match w.find? a with
  | none => 0
  | some x => x.bal

def gNewAccount : Nat := 25000
def gCallValue : Nat := 9000
def gCallStipend : Nat := 2300
def gWarmAccess : Nat := 100
def gColdAccountAccess : Nat := 2600
def gSelfdestruct : Nat := 5000
def gLog : Nat := 375
def gLogdata : Nat := 8
def gLogtopic : Nat := 375

instance {w a} : Decidable (Dead w a) := by
  simp [Dead]
  cases (Lean.RBMap.find? w a)
  · simp; apply instDecidableTrue
  · simp [Acct.Empty]; apply instDecidableAnd


def cAAccess (x : Addr) (a : AddrSet) : Nat :=
  if x ∈ a then gWarmAccess else gColdAccountAccess

def except64th (n : Nat) : Nat := n - (n / 64)

def cExtra (s : State') (t : Addr) (v : Word) : Nat :=
  let cAcc : Nat := cAAccess t s.acr.adrs
  let cNew : Nat := if (Dead s.wld t ∧ v ≠ 0) then gNewAccount else 0
  let cXfer : Nat := if v ≠ 0 then gCallValue else 0
  (cAcc + cXfer + cNew)

def cGasCap (s : State') (g : Nat) (memCost : Nat) (t : Addr) (v : Word) : Nat :=
    if (memCost + cExtra s t v) ≤ s.mcn.gas
    then min (except64th (s.mcn.gas - (memCost + cExtra s t v))) g
    else g

def cCallGas (s : State') (g : Nat) (memCost : Nat) (t : Addr) (v : Word) : Nat :=
  if v ≠ 0
  then cGasCap s g memCost t v + gCallStipend
  else cGasCap s g memCost t v

def cCall (s : State') (g : Nat) (memCost : Nat) (t : Addr) (v : Word) : Nat :=
  cGasCap s g memCost t v + cExtra s t v

structure theta.Result : Type where
  (wld : World')
  (gas : Nat)
  (acr : Accrual)
  (sta : Bool)
  (ret : Bytes)

def World'.code (w : World') (a : Addr) : Array Byte :=
  match w.find? a with
  | none => #[]
  | some x => x.code

def Acct.empty : Acct :=
  {
    nonce := 0
    bal := 0
    stor := .empty
    code := #[]
  }


-- need further update for precompiled contracts
def θ.prep
  (H : Block)
  (σ : World')
  (A : Accrual)
  (s : Addr)
  (o : Addr)
  (r : Addr)
  (c : Addr)
  (g : Nat)
  (p : Nat)
  (v : Word)
  (v_app : Word)
  (d : Bytes)
  (e : Nat)
  (w : Bool) :
  State' :=
  let σ'₁ : World' :=
    match σ.find? r with
    | none =>
      if v = 0
      then σ
      else σ.insert r {nonce := 0, bal := v, stor := .empty, code := #[]}
    | some aᵣ => σ.insert r {aᵣ with bal := aᵣ.bal + v}
  let σ₁ : World' :=
    match σ'₁.find? s with
    | none =>
      if v = 0
      then σ'₁
      else (dbg_trace "unreachable code : nonzero value calls from empty accounts should never happen" ; σ'₁)
    | some aₛ => σ'₁.insert s {aₛ with bal := aₛ.bal - v}
  let cd : Array Byte := σ.code c
  let I : Env' := {
    cta := r, oga := o, gpr := p.toB256, cld := d
    cla := s, clv := v_app, code := cd, blk := H, exd := e, wup := w
  }
  let μ : Machine := {gas := g, pc := 0, mem := #[], ret := [], stk := [], act := 0}
  ⟨σ₁, μ, A, I⟩

def θ.wrap (wld : World') (acr : Accrual) (Ξr : Ξ.Result) : theta.Result :=
  -- let Ξr : Ξ.Result := {wld := xr.wld, gas := xr.mcn.gas, acr := xr.acr, ret := xr.ret}
  let σ_stars : Option World' := Ξr.wld
  let g_stars : Nat := Ξr.gas
  let A_stars : Accrual := Ξr.acr
  let o : Option Bytes := Ξr.ret

  let σ' : World' := σ_stars.getD wld
  let g' : Nat := if σ_stars.isNone ∧ o.isNone then (dbg_trace "zero trigger"; 0) else g_stars
  let A' : Accrual := if σ_stars.isNone then acr else A_stars
  let z : Bool := if σ_stars.isNone then 0 else 1

  -- o' is not from YP, but necessary to cast from 'Option Bytes' to 'Bytes'
  -- (YP is a bit sloppy with types here)
  let o' : Bytes := o.getD []
  ⟨σ', g', A', z, o'⟩

def execAux (s : State') (f : State' → Option exec.Result) : exec.Result :=
  (f s).getD ⟨none, s.mcn, s.acr, none⟩

-- def execAux (s s' : State') (f : State' → Option exec.Result) : exec.Result :=
--   let g' : Nat := s'.mcn.gas
--   let s'' := {s' with mcn := {s'.mcn with gas := g'}}
--   (f s'').getD ⟨none, s''.mcn, s''.acr, none⟩

def gColdSLoad : Nat := 2100
def gSSet : Nat := 20000
def gSReset : Nat := 2900
def rSClear : Nat := 4800


def Bits.min {n} : Bits n → Bits n → Bits n
  | xs, ys => if xs ≤ ys then xs else ys

instance {n} : Min (Bits n) := ⟨.min⟩

def dataGas (cd : Bytes) : Nat :=
  let aux : Byte → Nat := fun b => if b = 0 then 4 else 16
  (cd.map aux).sum

def gTransaction : Nat := 21000

def intrinsicGas (Rcv : Option Addr) (cd : Bytes) (Ta : List (Addr × List Word)) : Nat :=
  let aux : (Addr × List Word) → Nat :=
    fun | ⟨_, l⟩ => G_accesslistaddress + (G_accessliststorage * l.length)
  dataGas cd +
  Rcv.rec (G_txcreate + initCodeCost cd) (fun _ => 0) +
  gTransaction +
  (Ta.map aux).sum

def World'.transfer? (wld : World') (src : Addr) (clv : Word) (dst : Addr) : Option World' := do
  let src_acct ← wld.find? src
  let dst_acct ← wld.find? dst
  let new_src_bal ← safeSub src_acct.bal clv
  let wor' := wld.insert src {src_acct with bal := new_src_bal}
  return wor'.insert dst {dst_acct with bal := dst_acct.bal + clv}

-- checkpoint is an 'Option' type because computation of checkpoints
-- may fail for invalid txs. this is *not* the case for any subsequent
-- steps of a tx: once you get to a checkpoint, the tx *always* goes
-- through and yields a new state. i.e., there is no invalid tx that
-- has a checkpoint.
def checkpoint (w : World') (ad : Addr) (v : Word) : Option World' := do
  let ac ← w.find? ad
  let bal' ← safeSub ac.bal v
  some <| w.insert ad {ac with bal := bal', nonce := ac.nonce + 1}


-- A^0
def Accrual.init : Accrual :=
  {
    dest := []
    adrs := .ofList [1, 2, 3, 4, 5, 6, 7, 8, 9] -- precompiled contracts
    keys := .empty
    ref := 0
    logs := []
    touched := .empty
  }

abbrev AccessList : Type := List (Addr × List B256)

abbrev AccessList.collect (al : AccessList) : KeySet :=
  let addPair : Addr → KeySet → B256 → KeySet :=
    fun a aks k => aks.insert ⟨a, k⟩
  let addElem : KeySet → Addr × List B256 → KeySet :=
    fun aks pr => List.foldl (addPair pr.fst) aks pr.snd
  List.foldl addElem .empty al

def A_star (H : Block) (ST : Addr) (Tt : Option Addr) (TA : AccessList) : Accrual :=
  let a : AddrSet :=
    Accrual.init.adrs.insertMany
      (Std.HashSet.ofList (ST :: H.ben :: TA.map Prod.fst))
  {
    Accrual.init with
    adrs := Tt.rec a (a.insert)
    keys := TA.collect
  }

def Stor.insert' (s : Stor) (k v : Word) : Stor :=
  if v = 0 then s.erase k else s.insert k v

def Stor'.insert' (s : Stor') (k v : B256) : Stor' :=
  if v = 0 then s.erase k else s.insert k v

def sstoreStep (w₀ : World') (s : State') : Option State' := do
  let ⟨σ, μ, A, I⟩ := s
  let (x :: v' :: xs) ← (return μ.stk) | none
  let (a₀ : Acct) ← w₀.find? I.cta
  let (v₀ : B256) := ((a₀.stor.find? x).getD 0)
  let (a : Acct) ← σ.find? s.env.cta
  let (v : B256) := ((a.stor.find? x).getD 0)
  let c₀ : Nat := cond (A.keys.contains ⟨I.cta, x⟩) 0 gColdSLoad
  let c₁ : Nat :=
    if v = v' ∨ v₀ ≠ v
    then gWarmAccess
    else if v₀ = 0
         then gSSet
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
         then gSSet - gWarmAccess
         else gSReset - gWarmAccess
    else 0
  let r : Int :=
    if v = v'
    then 0
    else if v₀ = v
         then if v' = 0
              then rSClear
              else 0
         else rDirtyClear + rDirtyReset
  let g' ← safeSub s.mcn.gas c
  let ref' ← (Int.ofNat A.ref + r).toNat'
  let a' : Acct := {a with stor := a.stor.insert' x v'}

  some
    {
      wld := σ.insert I.cta a'
      mcn := {
        s.mcn with
        gas := g'
        pc := s.mcn.pc + 1
        stk := xs
      }
      acr := {
        s.acr with
        keys := s.acr.keys.insert ⟨s.env.cta, x⟩
        ref := ref'
      }
      env := s.env
    }

def Option.trace {ξ} [ToString ξ] : Option ξ → Option ξ
  | none => none
  | some x => dbg_trace x; some x

def Addr.toHex (a :Addr) : String := @Bits.toHex 40 a

def Word.bytecount (w : Word) : Nat := (@Bits.toBytes 32 w).sig.length

def B256.zerocount (x : B256) : Nat → Nat
  | 0 => 0
  | k + 1 => if x = 0 then k + 1 else B256.zerocount (x >>> 8) k

def B256.bytecount (x : B256) : Nat := 32 - (B256.zerocount x 32)

def List.swapCore {ξ} (x : ξ) : Nat → List ξ → Option (ξ × List ξ)
  | 0, [] => none
  | 0, y :: ys => some ⟨y, x :: ys⟩
  | _ + 1, [] => none
  | n + 1, y :: ys =>
    match swapCore x n ys with
    | some ⟨z, zs⟩ => some ⟨z, y :: zs⟩
    | none => none

def List.swap {ξ} (n : Nat) : List ξ → Option (List ξ)
  | [] => none
  | x :: xs =>
    match swapCore x n xs with
    | some ⟨y, ys⟩ => some (y :: ys)
    | none => none

def gBase : Nat := 2

def Bits.replicate : ∀ n : Nat, Bool → Bits n
  | 0, _ => ⦃⦄
  | n + 1, b => b +> Bits.replicate n b

def Bits.takeD : ∀ {m} n, Bits m → Bool → Bits n
  | _, 0, _, _ => ⦃⦄
  | 0, n + 1, ⦃⦄, y => y +> Bits.takeD n ⦃⦄ y
  | _ + 1, n + 1, x +> xs, y => x +> Bits.takeD n xs y

def Bits.shlCore {m n : Nat} : Nat → Bits m → Bits n
  | 0, xs => Bits.takeD n xs 0
  | _, ⦃⦄ => Bits.replicate n 0
  | k + 1, _ +> xs => @Bits.shlCore _ n k xs

def Bits.shl' (m : Nat) {n} (xs : Bits n) : Bits n := @Bits.shlCore n n m xs

def memExp (s : Nat) (f l : B256) : Nat :=
  if l = 0
  then s
  else max s (ceilDiv (f.toNat + l.toNat) 32)

-- 'List.put xs n y z' is similar to 'List.set xs n y', except that
-- the former extends the input list (using the default filler 'z')
-- to ensure that 'y' is the 'n'th element of the resultant list.
def List.put {ξ : Type u} : List ξ → Nat → ξ → ξ → List ξ
  | _ :: xs, 0, y, _ => y :: xs
  | [], 0, y, _ => [y]
  | x :: xs, n + 1, y, z => x :: (List.put xs n y z)
  | [], n + 1, y, z => z :: (List.put [] n y z)

def List.puts {ξ : Type u} (xs : List ξ) (n : Nat) (ys : List ξ) (z : ξ) : List ξ :=
  xs.takeD n z ++ ys ++ xs.drop (n + ys.length)

def Mem : Type := Array Byte

def Array.writeD {ξ : Type u} (xs : Array ξ) (n : ℕ) : List ξ → Array ξ
  | [] => xs
  | y :: ys =>
    if h : n < xs.size
    then let xs' := xs.setN n y
         writeD xs' (n + 1) ys
    else xs

def Array.copyD {ξ : Type u} (xs ys : Array ξ) : Array ξ :=
  let f : (Array ξ × Nat) → ξ → (Array ξ × Nat) :=
    λ ysn x => ⟨Array.setD ysn.fst ysn.snd x, ysn.snd + 1⟩
  (Array.foldl f ⟨ys, 0⟩ xs).fst

def Array.writeX {ξ : Type u} (xs : Array ξ) (n : ℕ) (ys : List ξ) (d : ξ) : Array ξ :=
  if n + ys.length ≤ xs.size
  then Array.writeD xs n ys
  else let zs : Array ξ := Array.mkArray (n + ys.length) d
       let zs' : Array ξ := Array.copyD xs zs
       Array.writeD zs' n ys

def gCopy : Nat := 3
def gMemory : Nat := 3
def gKeccak256 : Nat := 30
def gKeccak256Word : Nat := 6

def cMem (a : Nat) := gMemory * a + ((a ^ 2) / 512)

def nextState (s : State') (cost : Nat)
  (act' : Nat := s.mcn.act)
  (stk' : Stack' := s.mcn.stk)
  (mem' : Array Byte := s.mcn.mem)
  (ret' : Bytes := s.mcn.ret)
  (adrs' : AddrSet := s.acr.adrs)
  (logs' : List RLP' := s.acr.logs) : Option State' := do
  let memCost : Nat := cMem act' - cMem s.mcn.act
  let gas' ← s.deductGas (cost + memCost)
  let μ' : Machine :=
    {
      gas := gas',
      pc := s.mcn.pc + 1,
      mem := mem',
      ret := ret'
      stk := stk'
      act := act'
    }
  let A' : Accrual :=
    {
      dest := s.acr.dest
      adrs := adrs'
      keys := s.acr.keys
      ref := s.acr.ref
      logs := logs'
      touched := s.acr.touched
    }
  some {s with mcn := μ', acr := A'}

def World'.get (w : World') (a : Addr) : Acct := (w.find? a).getD .empty

def B256.toAddr (x : B256) : Addr :=
  match x.1.2.toB8t with
  | ⟨_, _, _, _, b0, b1, b2, b3⟩ =>
    b0.toByte ++ b1.toByte ++ b2.toByte ++ b3.toByte ++ x.2.toBits

def Addr.toB256 (a : Addr) : B256 := Bits.toB256 ((0 : Bits 96) ++ a)

def Rinst.run (H : Block) (w₀ : World') (s : State') : Rinst → Option State'
  | .address =>
    nextState s (cost := gBase) (stk' := s.env.cta.toB256 :: s.mcn.stk)
  | .balance => do
    let (x :: xs) ← (return s.mcn.stk) | none
    let a := x.toAddr
    let adrs' : AddrSet := s.acr.adrs.insert a
    nextState s
      (cost := cAAccess a s.acr.adrs)
      (stk' := (s.wld.get a).bal.toB256 :: xs)
      (adrs' := adrs')
  | .origin => nextState s (cost := gBase) (stk' := s.env.oga.toB256 :: s.mcn.stk)
  | .caller => nextState s (cost := gBase) (stk' := s.env.cla.toB256 :: s.mcn.stk)
  | .callvalue => nextState s (cost := gBase) (stk' := s.env.clv.toB256 :: s.mcn.stk)
  | .calldataload => do
    let (x :: xs) ← (return s.mcn.stk) | none
    let cd : Word := Bytes.toBits 32 (s.env.cld.sliceD x.toBits.toNat 32 0)
    nextState s (cost := gVerylow) (stk' := cd.toB256 :: xs)
  | .calldatasize => nextState s (cost := gBase) (stk' := s.env.cld.length.toB256 :: s.mcn.stk)
  | .calldatacopy => do
    let (x :: y :: z :: xs) ← (return s.mcn.stk) | none
    let bs : Bytes := s.env.cld.sliceD y.toBits.toNat z.toBits.toNat 0
    nextState s
      (cost := gVerylow + (gCopy * (ceilDiv z.toBits.toNat 32)))
      (act' := memExp s.mcn.act x z)
      (stk' := xs)
      --(mem' := List.puts s.mcn.mem x.toNat bs 0)
      (mem' := Array.writeX s.mcn.mem x.toNat bs 0)
  | .codesize => nextState s (cost := gBase) (stk' := s.env.code.size.toB256 :: s.mcn.stk)
  | .codecopy => do
    let (x :: y :: z :: xs) ← (return s.mcn.stk) | none

    let act' := memExp s.mcn.act x z
    let cost := gVerylow + (gCopy * (ceilDiv z.toNat 32))
    let memCost : Nat := cMem act' - cMem s.mcn.act
    let _ ← s.deductGas (cost + memCost)

    let bs : Bytes := s.env.code.sliceD y.toNat z.toNat (Linst.toByte .stop)
    nextState s
      (cost := cost)-- gVerylow + (gCopy * (ceilDiv z.toNat 32)))
      (act' := act')-- memExp s.mcn.act x z)
      (stk' := xs)
      (mem' := Array.writeX s.mcn.mem x.toNat bs 0)
  | .gasprice => nextState s (cost := gBase) (stk' := s.env.gpr :: s.mcn.stk)
  | .extcodesize => do
    let (x :: xs) ← (return s.mcn.stk) | none
    let a := x.toAddr
    let adrs' : AddrSet := s.acr.adrs.insert a
    nextState s
      (cost := cAAccess a s.acr.adrs)
      (stk' := (s.wld.get a).code.size.toB256 :: xs)
      (adrs' := adrs')
  | .extcodecopy => do
    let (x :: y :: z :: w :: xs) ← (return s.mcn.stk) | none
    let a : Acct := s.wld.get x.toAddr
    let bs : Bytes := a.code.sliceD z.toNat w.toNat (Linst.toByte .stop)
    nextState s
      (cost := cAAccess x.toAddr s.acr.adrs + (gCopy * (ceilDiv z.toNat 32)))
      (act' := memExp s.mcn.act y w)
      (stk' := xs)
      (mem' := Array.writeX s.mcn.mem y.toNat bs 0)
  | .retdatasize =>
    nextState s (cost := gBase) (stk' := s.mcn.ret.length.toB256 :: s.mcn.stk)
  | .retdatacopy => do
    let (x :: y :: z :: xs) ← (return s.mcn.stk) | none
    let bs ← s.mcn.ret.slice? y.toNat z.toNat
    nextState s
      (cost := gVerylow + (gCopy * (ceilDiv z.toNat 32)))
      (act' := memExp s.mcn.act x z)
      (stk' := xs)
      (mem' := Array.writeX s.mcn.mem x.toNat bs 0)
  | .extcodehash => do
    let (x :: xs) ← (return s.mcn.stk) | none
    let a := x.toAddr
    let adrs' : AddrSet := s.acr.adrs.insert a
    let hash : Word :=
      if (Dead s.wld a)
      then 0
      else B8a.keccak <| Array.map Byte.toB8 (s.wld.get a).code -- (s.wld.get a).code.keccak
    nextState s
      (cost := cAAccess a s.acr.adrs)
      (stk' := hash.toB256 :: xs)
      (adrs' := adrs')
  | .selfbalance =>
    let bal := (s.wld.get s.env.cta).bal
    nextState s (cost := gLow) (stk' := bal.toB256 :: s.mcn.stk)
  | .chainid =>
    nextState s (cost := gBase) (stk' := H.chainId.toB256 :: s.mcn.stk)
  | .number =>
    nextState s (cost := gBase) (stk' := H.number.toB256 :: s.mcn.stk)
  | .timestamp =>
    nextState s (cost := gBase) (stk' := H.timestamp.toB256 :: s.mcn.stk)
  | .gaslimit =>
    nextState s (cost := gBase) (stk' := H.gasLimit.toB256 :: s.mcn.stk)
  | .prevrandao =>
    nextState s (cost := gBase) (stk' := H.prevRandao.toB256 :: s.mcn.stk)
  | .coinbase =>
    nextState s (cost := gBase) (stk' := H.ben.toWord.toB256 :: s.mcn.stk)
  | .msize =>
    nextState s (cost := gBase) (stk' := (s.mcn.act * 32).toB256 :: s.mcn.stk)
  | .mload => do
    let (x :: xs) ← (return s.mcn.stk) | none
    let bs : Bytes := s.mcn.mem.sliceD x.toNat 32 0
    nextState s (cost := gVerylow)
      (act' := memExp s.mcn.act x (32 : Nat).toB256)
      (stk' := (@Bytes.toBits 32 bs).toB256 :: xs)
  | .mstore => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    let act' := memExp s.mcn.act x (32 : Nat).toB256
    let memCost : Nat := cMem act' - cMem s.mcn.act
    let g' ← s.deductGas (gVerylow + memCost)
    let m' : Machine :=
      {
        s.mcn with
        stk := xs,
        gas := g',
        -- mem := List.puts s.mcn.mem x.toNat (@Bits.toBytes 32 y) 0,
        mem := Array.writeX s.mcn.mem x.toNat (y.toB8s.map B8.toByte) 0,
        pc := s.mcn.pc + 1
        act := act'
      }
    some {s with mcn := m'}
  | .mstore8 => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    dbg_trace s!"x : {x.toNat}"
    let act' := memExp s.mcn.act x 1
    let memCost : Nat := cMem act' - cMem s.mcn.act
    dbg_trace s!"mem cost : {memCost}"
    let g' ← s.deductGas (gVerylow + memCost)
    let m' : Machine :=
      {
        s.mcn with
        stk := xs,
        gas := g',
        mem := Array.writeX s.mcn.mem x.toNat [B8.toByte y.2.2.toUInt8] 0,
        pc := s.mcn.pc + 1
        act := act'
      }
    some {s with mcn := m'}
  | .gas => do
    let g' ← s.deductGas gBase
    nextState s (cost := gBase) (stk' := g'.toB256 :: s.mcn.stk)
  | .eq => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    nextState s (cost := gVerylow) (stk' := .eq_check x y :: xs)
  | .lt => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    nextState s (cost := gVerylow) (stk' := .lt_check x y :: xs)
  | .gt => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    nextState s (cost := gVerylow) (stk' := .gt_check x y :: xs)
  | .slt => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    nextState s (cost := gVerylow) (stk' := .slt_check x y :: xs)
  | .sgt => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    nextState s (cost := gVerylow) (stk' := .sgt_check x y :: xs)
  | .iszero => do
    let (x :: xs) ← (return s.mcn.stk) | none
    nextState s (cost := gVerylow) (stk' := B256.eq_check x 0 :: xs)
  | .not => do
    let (x :: xs) ← (return s.mcn.stk) | none
    nextState s (cost := gVerylow) (stk' := ~~~ x :: xs)
  | .and => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    nextState s (cost := gVerylow) (stk' := B256.and x y :: xs)
  | .or => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    nextState s (cost := gVerylow) (stk' := B256.or x y :: xs)
  | .xor => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    nextState s (cost := gVerylow) (stk' := B256.xor x y :: xs)
  | .signextend => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    let g' ← s.deductGas gLow
    some {s with mcn := {s.mcn with stk := B256.signext x y :: xs, gas := g', pc := s.mcn.pc + 1}}
  | .pop => do
    let (_ :: xs) ← (return s.mcn.stk) | none
    let g' ← s.deductGas gBase
    some {s with mcn := {s.mcn with stk := xs, gas := g', pc := s.mcn.pc + 1}}
  | .byte => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    let g' ← s.deductGas gVerylow
    let b : B8 := (List.getD y.toB8s x.toNat 0)
    --let z : Word := (0 : Bits 248) ++ b
    some {s with mcn := {s.mcn with stk := b.toB256 :: xs, gas := g', pc := s.mcn.pc + 1}}
  | .shl => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    let g' ← s.deductGas gVerylow
    -- let z : Word := Bits.shl' x.toNat y
    let z : B256 := y <<< x.toNat
    some {s with mcn := {s.mcn with stk := z :: xs, gas := g', pc := s.mcn.pc + 1}}
  | .shr => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    let g' ← s.deductGas gVerylow
    --let z : Word := Bits.shr x.toNat y
    let z : B256 := y >>> x.toNat
    some {s with mcn := {s.mcn with stk := z :: xs, gas := g', pc := s.mcn.pc + 1}}
  | .sar => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    let g' ← s.deductGas gVerylow
    let z : B256 := B256.sar x.toNat y
    some {s with mcn := {s.mcn with stk := z :: xs, gas := g', pc := s.mcn.pc + 1}}
  | .kec => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    let act' := memExp s.mcn.act x y
    let cost := gKeccak256 + (gKeccak256Word * (ceilDiv y.toNat 32))
    let memCost : Nat := cMem act' - cMem s.mcn.act
    let _ ← s.deductGas (cost + memCost)
    let bs : Bytes := s.mcn.mem.sliceD x.toNat y.toNat 0
    let hash : B256 := B8s.keccak (List.map Byte.toB8 bs)
    nextState s
      (cost := gKeccak256 + (gKeccak256Word * (ceilDiv y.toNat 32)))
      (act' := act')
      (stk' := hash :: xs)
  | .sub => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    let g' ← safeSub s.mcn.gas gVerylow
    some {s with mcn := {s.mcn with stk := (x - y) :: xs, gas := g', pc := s.mcn.pc + 1}}
  | .mul => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    let g' ← safeSub s.mcn.gas gLow
    some {s with mcn := {s.mcn with stk := (x * y) :: xs, gas := g', pc := s.mcn.pc + 1}}
  | .exp => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    let x' : B256 := x
    let y' : B256 := y
    let xpy : B256 := (B256.bexp x' y')
    nextState s
      (cost := g_exp + (g_expbyte * y.bytecount))
      (stk' := xpy :: xs)
  | .div => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    let z : B256 := (x / y)
    nextState s (cost := gLow) (stk' := z :: xs)
  | .sdiv => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    let g' ← safeSub s.mcn.gas gLow
    some {s with mcn := {s.mcn with stk := .sdiv x y :: xs, gas := g', pc := s.mcn.pc + 1}}
  | .mod => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    let z : B256 := (x % y)
    let g' ← safeSub s.mcn.gas gLow
    some {s with mcn := {s.mcn with stk := z :: xs, gas := g', pc := s.mcn.pc + 1}}
  | .smod => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    let g' ← safeSub s.mcn.gas gLow
    some {s with mcn := {s.mcn with stk := (.smod x y) :: xs, gas := g', pc := s.mcn.pc + 1}}
  | .add => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    nextState s (cost := gVerylow) (stk' := (x + y) :: xs)
  | .addmod => do
    let (x :: y :: z :: xs) ← (return s.mcn.stk) | none
    let g' ← safeSub s.mcn.gas g_mid
    some {s with mcn := {s.mcn with stk := .addmod x y z :: xs, gas := g', pc := s.mcn.pc + 1}}
  | .mulmod => do
    let (x :: y :: z :: xs) ← (return s.mcn.stk) | none
    let g' ← safeSub s.mcn.gas g_mid
    some {s with mcn := {s.mcn with stk := .mulmod x y z :: xs, gas := g', pc := s.mcn.pc + 1}}
  | .swap n => do
    let stk' ← List.swap n s.mcn.stk
    let g' ← safeSub s.mcn.gas gVerylow
    some {s with mcn := {s.mcn with stk := stk', gas := g', pc := s.mcn.pc + 1}}
  | .dup n => do
    let x ← s.mcn.stk.get? n
    let g' ← safeSub s.mcn.gas gVerylow
    some {s with mcn := {s.mcn with stk := x :: s.mcn.stk, gas := g', pc := s.mcn.pc + 1}}
  | .sload => do
    let (x :: xs) ← (return s.mcn.stk) | none
    let c : Nat := if s.acr.keys.contains ⟨s.env.cta, x⟩ then gWarmAccess else gColdSLoad
    let g' ← safeSub s.mcn.gas c
    let ac ← s.wld.find? s.env.cta
    let y := (ac.stor.find? x).getD 0
    some {
      s with
      mcn := {s.mcn with stk := y :: xs, gas := g', pc := s.mcn.pc + 1}
      acr := {s.acr with keys := s.acr.keys.insert ⟨s.env.cta, x⟩}
    }
  | .sstore => sstoreStep w₀ s
  | .pc => nextState s (cost := gBase) (stk' := s.mcn.pc.toB256 :: s.mcn.stk)
  | .log n => do
    let (x :: y :: xys) ← (return s.mcn.stk) | none
    let cost := gLog + (gLogdata * y.toNat) + (n * gLogtopic)
    let act' := memExp s.mcn.act x y
    let memCost : Nat := cMem act' - cMem s.mcn.act
    let _ ← s.deductGas (cost + memCost)
    let ⟨xs, ys⟩ ← List.splitAt? n xys
    let bs : B8s := (s.mcn.mem.sliceD x.toNat y.toNat 0).map Byte.toB8
    let log : RLP' :=
      .list [
        .b8s ((@Bits.toBytes 20 s.env.cta).map Byte.toB8),
        .list (xs.map B256.toRLP),
        .b8s bs
      ]
    nextState s
      (cost := cost)
      (stk' := ys)
      (act' := act')
      (logs' := log :: s.acr.logs)
  | i => dbg_trace s!"UNIMPLEMENTED REGULAR INSTRUCTION EXECUTION : {i.toString}"; none


-- w₀ : the 'checkpoint' world saved at the preparation stage of tx

-- The intended behavior of 'execCore' is identical to the 'X' function of YP,
-- except that it returns 'none' if
--   (1) the VM is *CURRENTLY* (i.e, not at some later point in code) at
--       exceptional halting state due to the code byte that the program counter
--       points to, or
--   (2) recursion limit is reached (which should never happen with correct usage)

-- def memExp (s : Nat) (f l : Word) : Nat :=
--   if l = 0
--   then s
--   else max s (ceilDiv (f.toNat + 1) l.toNat)

def gHigh : Nat := 10
def gJumpdest : Nat := 1

def Acct.isEmpty (ac : Acct) : Prop :=
  ac.nonce = 0 ∧
  ac.bal = 0 ∧
  ac.stor.isEmpty = .true ∧
  ac.code = #[]

instance {ac : Acct} : Decidable ac.isEmpty := instDecidableAnd

def World'.set (w : World') (a : Addr) (ac : Acct) : World' :=
  if ac.isEmpty then w.erase a else w.insert a ac

def World'.addBal (w : World') (a : Addr) (v : Word) : World' :=
  let ac := w.get a
  let ac' : Acct := {ac with bal := ac.bal + v}
  w.set a ac'

def World'.setBal (w : World') (a : Addr) (v : Word) : World' :=
  let ac := w.get a
  let ac' : Acct := {ac with bal := v}
  w.set a ac'

def Jinst.run (s : State') : Jinst → Option State'
  | .jumpdest => do
    let g' ← safeSub s.mcn.gas gJumpdest
    some {s with mcn := {s.mcn with gas := g', pc := s.mcn.pc + 1}}
  | .jump => do
    let (loc :: stk') ← (return s.mcn.stk) | none
    let g' ← safeSub s.mcn.gas g_mid
    match s.jumpable loc.toNat with
    | true => some {s with mcn := {s.mcn with stk := stk', gas := g', pc := loc.toNat}}
    | false => dbg_trace s!"non-jumpable destination : {loc.toHex}" ; none
  | .jumpi => do
    let (loc :: val :: stk') ← (return s.mcn.stk) | none
    let g' ← safeSub s.mcn.gas gHigh
    if val = 0
    then some {s with mcn := {s.mcn with stk := stk', gas := g', pc := s.mcn.pc + 1}}
    else do
         guard (s.jumpable loc.toNat)
         some {s with mcn := {s.mcn with stk := stk', gas := g', pc := loc.toNat}}

def Ninst.run (B : Block) (w₀ : World') (s : State') : Ninst → Option State'
  | .push bs _ => do
    let g' ← safeSub s.mcn.gas (if bs = [] then gBase else gVerylow)
    let m' : Machine :=
      { s.mcn with
        gas := g'
        pc := s.mcn.pc + bs.length + 1,
        stk := (bs.toBits 32).toB256 :: s.mcn.stk }
    some {s with mcn := m'}
  | .reg r => Rinst.run B w₀ s r
  | .exec e => dbg_trace s!"unimplemented xinst : {e.toString}\n" ; none

def retRun (s : State') : Option Ξ.Result := do
  let (rlc :: rsz :: _) ← (return s.mcn.stk) | none
  let act' : Nat := memExp s.mcn.act rlc rsz
  let memCost : Nat := cMem act' - cMem s.mcn.act
  let g' ← safeSub s.mcn.gas memCost
  let r := s.mcn.mem.sliceD rlc.toNat rsz.toNat 0
  some {wld := s.wld, gas := g', acr := s.acr, ret := r}

def State'.xh (s : State') : Ξ.Result :=
  {wld := none, gas := s.mcn.gas, acr := s.acr, ret := none}


structure theta.Cont : Type where
  (olc : B256)
  (osz : B256)
  (gas : Nat)
  (mem : Array Byte)
  (pc : Nat)
  (stk : Stack')
  (act : Nat)
  (env : Env')

def theta.Result.toState (ct : theta.Cont) (tr : theta.Result) : State' :=
  let cpy : Bytes := List.take ct.osz.toNat tr.ret
  let m' : Machine := {
    gas := ct.gas + tr.gas
    pc := ct.pc + 1
    --mem := ct.mem.takeD ct.olc.toNat 0 ++ cpy ++ ct.mem.drop (ct.olc.toNat + cpy.length)
    mem := Array.writeX ct.mem ct.olc.toNat cpy 0
    ret := tr.ret
    --stk := @Bool.toBits 256 tr.sta :: ct.stk
    stk := (if tr.sta then 1 else 0) :: ct.stk
    act := ct.act
  }
  {wld := tr.wld, mcn := m', acr := tr.acr, env := ct.env}

def midspan : Inst → Bool
  | .next (.exec .call) => false
  | .next (.exec .callcode) => false
  | .next (.exec .delcall) => false
  | .next (.exec .statcall) => false
  | .next (.exec .create) => false
  | .next (.exec .create2) => false
  | .last _ => false
  | _ => true


/-
-- - 'none' if recursion limit or unimplemented opcode is reached
-- - 'some ⟨s, none⟩' if s = exceptional halting state
-- - 'some ⟨s, some i⟩' if i is calling or halting opcode
def span (H : Block) (w₀ : World') :
    Nat → State' → Option (State' × Option Inst)
  | 0, _ => none
  | lim + 1, s => do
    -- dbg_trace s!"span gas : {s.mcn.gas}"
    let (some i) ← (some s.inst) | some ⟨s, none⟩
    -- dbg_trace s!"span :: executing inst : {i.toString}"
    let .true ← (some (midspan i)) | some ⟨s, some i⟩
    match i with
    | .next n =>
      match n.run H w₀ s with
      | none => some ⟨s, none⟩
      | some s' => span H w₀ lim s'
    | .jump j =>
      match j.run s with
      | none => some ⟨s, none⟩
      | some s' => span H w₀ lim s'
    | .last _ => none -- unreachable code


-- the X function of YP, except that the return type is modified to match
-- that of the Ξ function: the machine state (μ) returned by 'X' is never
-- used for anything except for remaining gas, so it is safe to discard the
-- unused information by the time X is returning.
-- This function returns 'none' only when either the recursion limit or an
-- unimplemented opcode is reached. returns 'some _' for all other cases.
-- return values :
def exec (H : Block) (w₀ : World') : Nat → State' → Option Ξ.Result
  | 0, _ => dbg_trace "execution limit reached\n" ; none
  | lim + 1, s₀ => do
    dbg_trace s!"exec gas : {s₀.mcn.gas}"
    let ⟨s, oi⟩ ← span H w₀ (lim + 1) s₀
    let some i ← some oi | some s.xh
    match i with
    | .next (.exec .call) => do
      let gas :: adr :: clv :: ilc :: isz :: olc :: osz :: stk
        ← (return s.mcn.stk) | (some s.xh)
      let i : Bytes := s.mcn.mem.sliceD ilc.toNat isz.toNat 0
      let t : Addr := toAddr adr
      dbg_trace s!"nested call to address : {t.toHex}"
      let as' : AddrSet := s.acr.adrs.insert t
      let A' : Accrual := {s.acr with adrs := as'}
      let act' : Nat := memExp (memExp s.mcn.act ilc isz) olc osz
      let memCost : Nat := cMem act' - cMem s.mcn.act
      let cg : Nat := cCallGas s gas.toNat memCost t clv
      let totalCost := (cCall s gas.toNat memCost t clv) + memCost
      let (some g') ← (return (safeSub s.mcn.gas totalCost)) | some s.xh
      let bd : theta.Cont :=
        {
          olc := olc
          osz := osz
          gas := g'
          mem := s.mcn.mem
          pc := s.mcn.pc
          stk := stk
          act := act'
          env := s.env
        }
      let s'' : State' ←
        if 0 = s.env.exd ∨ (s.wld.get s.env.cta).bal < clv
        then some (theta.Result.toState bd ⟨s.wld, cg, A', 0, []⟩)
        else do let s' : State' :=
                      θ.prep
                        H
                        s.wld
                        A'
                        s.env.cta
                        s.env.oga
                        t
                        t
                        cg
                        s.env.gpr.toNat
                        clv
                        clv
                        i
                        (s.env.exd - 1)
                        s.env.wup
                let xr ← exec H w₀ lim s'
                let θr := θ.wrap s'.wld s'.acr xr
                some (theta.Result.toState bd θr)
      exec H w₀ lim s''
    -- | .next (.exec .delcall) => _
    -- | .next (.exec .callcode) => _
    -- | .next (.exec .statcall) => _
    -- | .next (.exec .create) => _
    -- | .next (.exec .create2) => _
    | .last .stop => some {wld := s.wld, gas := s.mcn.gas, acr := s.acr, ret := some []}
    | .last .ret => some <| (retRun s).getD s.xh
    | .last .dest => do
      let (x :: _) ← (return s.mcn.stk) | none
      let a := toAddr x -- recipient
      let cost :=
        gSelfdestruct
        + (if a ∈ s.acr.adrs then 0 else gColdAccountAccess)
        + ( if Dead s.wld a ∧ s.wld.balAt s.env.cta ≠ 0
            then gNewAccount
            else 0 )
      let gas' ← s.deductGas cost
      some
        {
          wld :=
            if a = s.env.cta
            then s.wld
            else let v := (s.wld.get s.env.cta).bal
                 let wld' := s.wld.setBal s.env.cta 0
                 wld'.addBal a v
          gas := gas'
          acr :=
            {
              s.acr with
              dest := s.env.cta :: s.acr.dest
              adrs := s.acr.adrs.insert a
            }
          ret := some []
        }
    | _ =>
      dbg_trace s!"exec :: unimplemented inst : {i.toString}"
      none
-/

def fooo (lim : Nat) (s : State') : Option Unit :=
  match lim % 100000 with
  | 0 => do
    dbg_trace s!"gas : {s.mcn.gas}"
    return ()
  | _ => return ()


def exec (H : Block) (w₀ : World') : Nat → State' → Option Ξ.Result
  | 0, _ => none --dbg_trace "execution limit reached\n" ; none
  | lim + 1, s => do
    let () ← fooo lim s
    match s.inst with
    | none => some s.xh
    | some i =>
      -- dbg_trace s!"gas remaining : {s.mcn.gas}"
      -- dbg_trace s!"executing inst : {i.toString}"
      match i with
      | .next (.exec .delcall) => do
        let gas :: adr :: ilc :: isz :: olc :: osz :: stk
          ← (return s.mcn.stk) | (some s.xh)
        let i : Bytes := s.mcn.mem.sliceD ilc.toNat isz.toNat 0
        let t : Addr := adr.toAddr
        -- dbg_trace s!"nested delgatecall to address : {t.toHex}"
        let as' : AddrSet := s.acr.adrs.insert t
        let A' : Accrual := {s.acr with adrs := as'}
        let act' : Nat := memExp (memExp s.mcn.act ilc isz) olc osz
        let memCost : Nat := cMem act' - cMem s.mcn.act
        let cg : Nat := cCallGas s gas.toNat memCost t 0
        let totalCost := (cCall s gas.toNat memCost t 0) + memCost
        let (some g') ← (return (safeSub s.mcn.gas totalCost)) | some s.xh
        let bd : theta.Cont :=
          {
            olc := olc
            osz := osz
            gas := g'
            mem := s.mcn.mem
            pc := s.mcn.pc
            stk := stk
            act := act'
            env := s.env
          }
        let s'' : State' ←
          if 0 = s.env.exd
          then some (theta.Result.toState bd ⟨s.wld, cg, A', 0, []⟩)
          else do let s' : State' :=
                        θ.prep
                          H
                          s.wld
                          A'
                          s.env.cla
                          s.env.oga
                          s.env.cta
                          t
                          cg
                          s.env.gpr.toNat
                          0
                          s.env.clv
                          i
                          (s.env.exd - 1)
                          s.env.wup
                  let xr ← exec H w₀ lim s'
                  let θr := θ.wrap s'.wld s'.acr xr
                  some (theta.Result.toState bd θr)
        exec H w₀ lim s''

      | .next (.exec .call) => do
        let gas :: adr :: clv :: ilc :: isz :: olc :: osz :: stk
          ← (return s.mcn.stk) | (some s.xh)
        let i : Bytes := s.mcn.mem.sliceD ilc.toNat isz.toNat 0
        let t : Addr := adr.toAddr
        -- dbg_trace s!"nested call to address : {t.toHex}"
        let as' : AddrSet := s.acr.adrs.insert t
        let A' : Accrual := {s.acr with adrs := as'}
        let act' : Nat := memExp (memExp s.mcn.act ilc isz) olc osz
        let memCost : Nat := cMem act' - cMem s.mcn.act
        let cg : Nat := cCallGas s gas.toNat memCost t clv.toBits
        let totalCost := (cCall s gas.toNat memCost t clv.toBits) + memCost
        let (some g') ← (return (safeSub s.mcn.gas totalCost)) | some s.xh
        let bd : theta.Cont :=
          {
            olc := olc
            osz := osz
            gas := g'
            mem := s.mcn.mem
            pc := s.mcn.pc
            stk := stk
            act := act'
            env := s.env
          }
        let s'' : State' ←
          if 0 = s.env.exd ∨ (s.wld.get s.env.cta).bal < clv.toBits
          then some (theta.Result.toState bd ⟨s.wld, cg, A', 0, []⟩)
          else do let s' : State' :=
                        θ.prep
                          H
                          s.wld
                          A'
                          s.env.cta
                          s.env.oga
                          t
                          t
                          cg
                          s.env.gpr.toNat
                          clv.toBits
                          clv.toBits
                          i
                          (s.env.exd - 1)
                          s.env.wup
                  let xr ← exec H w₀ lim s'
                  let θr := θ.wrap s'.wld s'.acr xr
                  some (theta.Result.toState bd θr)
        exec H w₀ lim s''
      | .next n =>
        match n.run H w₀ s with
        | none => some s.xh
        | some s' => exec H w₀ lim s'
      | .jump j =>
         match j.run s with
         | none => some s.xh
         | some s' => exec H w₀ lim s'
      | .last .stop => some {wld := s.wld, gas := s.mcn.gas, acr := s.acr, ret := some []}
      | .last .ret => some <| (retRun s).getD s.xh
      | .last .dest => do
        let (x :: _) ← (return s.mcn.stk) | none
        let a := x.toAddr -- recipient
        let cost :=
          gSelfdestruct
          + (if a ∈ s.acr.adrs then 0 else gColdAccountAccess)
          + ( if Dead s.wld a ∧ s.wld.balAt s.env.cta ≠ 0
              then gNewAccount
              else 0 )
        let gas' ← s.deductGas cost
        some
          {
            wld :=
              if a = s.env.cta
              then s.wld
              else let v := (s.wld.get s.env.cta).bal
                   let wld' := s.wld.setBal s.env.cta 0
                   wld'.addBal a v
            gas := gas'
            acr :=
              {
                s.acr with
                dest := s.env.cta :: s.acr.dest
                adrs := s.acr.adrs.insert a
              }
            ret := some []
          }

      | _ => none --dbg_trace s!"unimplemented instruction : {i.toString}"; none

def theta
  -- Extra arguments not mentioned by YP,
  -- but still necessary for correct execution
  (H : Block)
  (σ₀ : World')

  -- Arguments specified by YP
  (σ : World')
  (A : Accrual)
  (s : Addr)
  (o : Addr)
  (r : Addr)
  (c : Addr)
  (g : Nat)
  (p : Nat)
  (v : Word)
  (v_app : Word)
  (d : Bytes)
  (e : Nat)
  (w : Bool) :
  Option theta.Result :=
  let st := θ.prep H σ A s o r c g p v v_app d e w
  match exec H σ₀ g st with
  | none => none
  | some xr => some (θ.wrap st.wld st.acr xr)

def publicAddress (hsa : ByteArray) (ri : UInt8) (rsa : ByteArray) : IO Addr :=
  match (ecrecoverFlag hsa ri rsa).toBytes with
  | [] => IO.throw "Unreachable code : ecrecover should never return empty bytes"
  | b :: pa =>
    if b = 0
    then IO.throw "ecrecover failed"
    else return (Bytes.toBits 20 pa)

def IO.guard (φ : Prop) [Decidable φ] (msg : String) : IO Unit :=
  if φ then return () else IO.throw msg

inductive TxType : Type
  | zero : TxType
  -- access list (T_A)
  | one : AccessList → TxType
  -- access list (T_A), max fee per gas (T_m), max priority fee per gas (T_f)
  | two : AccessList → Word → Word → TxType

structure TxBytesContent : Type where
  (chainId : Option Nat)
  (yParity : Bool)
  (type : TxType)
  (nonce : Word)
  (gasPrice : Word)
  (gasLimit : Word)
  (receiver : Addr)
  (val : Word)
  (calldata : Bytes)
  (r : Bytes)
  (s : Bytes)
  (acc : AccessList)

structure transact.Result : Type where
  (wld : World')
  (gas : Nat)
  (log : B256)
  (sta : Bool)

#check List.toString
#check Char.toString
#check Nibs.toHex


def prettyFoo : (Nibs × Bytes) → String
  | ⟨ns, bs⟩ => s!"{ns.toHex} :: {bs.toHex}"

def prettyBar : (B8s × B8s) → String
  | ⟨ns, bs⟩ => prettyFoo ⟨ns.map B8.toNib, bs.map B8.toByte⟩

def decodeTxBytes (tbs : Bytes) : IO (TxBytesContent × Word) := do
  match RLP.decode tbs with
  | RLP.list [
      .bytes nonce,
      .bytes gasPrice,
      .bytes gasLimit,
      .bytes toAddr,
      .bytes val,
      .bytes calldata,
      .bytes [v],
      .bytes r,
      .bytes s
    ] =>
    let bs :=
      RLP.encode <|
        .list [
          .bytes nonce,
          .bytes gasPrice,
          .bytes gasLimit,
          .bytes toAddr,
          .bytes val,
          .bytes calldata
        ]
    return ⟨
      {
        chainId := none
        yParity := if (v - Ox x1 xB) = 0 then 0 else 1
        type := .zero
        nonce := @Bytes.toBits 32 nonce
        gasPrice := @Bytes.toBits 32 gasPrice
        gasLimit := @Bytes.toBits 32 gasLimit
        receiver := @Bytes.toBits 20 toAddr
        val := @Bytes.toBits 32 val
        calldata := calldata
        r := (r.reverse.takeD 32 0).reverse
        s := (s.reverse.takeD 32 0).reverse
        acc := []
      },
      bs.keccak
    ⟩
  | _ => IO.throw "Error : TX bytes decoding failed"

def eqTest {ξ} [DecidableEq ξ] (x y : ξ) (testName : String) : IO Unit := do
  .guard (x = y) (testName ++ " : fail")
  .println (testName ++ " : pass")

def eraseIfEmpty (w : World') (a : Addr) : World' := w.set a <| w.get a

def Tx.run
  (blk : Block) (w : World') (tx : TxBytesContent)
  (sender : Addr) : IO transact.Result := do
  let g : Nat := tx.gasLimit.toNat - intrinsicGas (some tx.receiver) tx.calldata []
  let w ← (checkpoint w sender (tx.gasLimit * tx.gasPrice)).toIO ""

  let tr ←
    (
      theta
        blk
        w w
        (A_star blk sender (some tx.receiver) [])
        sender
        sender
        tx.receiver
        tx.receiver
        g
        tx.gasPrice.toNat
        tx.val
        tx.val
        tx.calldata
        1024
        true
    ).toIO "theta failed"

  let gasLeft : Nat := tr.gas -- g'
  let refundAmount : Nat := tr.acr.ref
  let gasReturn : Word :=
    Nat.toBits' 256 (gasLeft + min ((tx.gasLimit.toNat - gasLeft) / 5) refundAmount) -- g*
  let gasUsed : Word := tx.gasLimit - gasReturn
  let valReturn : Word := gasReturn * tx.gasPrice

  let f : Word :=
    match tx.type with
      | .two _ tm tf => min tf (tm - blk.baseFee)
      | _ => tx.gasPrice - blk.baseFee

  let w₀ : World' := tr.wld.addBal sender valReturn
  let w₁ : World' := w₀.addBal blk.ben (gasUsed * f)
  --let w₂ : World' := List.foldl Lean.RBMap.erase w₁ tr.acr.dest
  --let w₃ : World' := List.foldl eraseIfEmpty w₂ tr.acr.touched.toList
  let w₃ : World' := List.foldl eraseIfEmpty w₁ tr.acr.touched.toList

  return {
    wld := w₃,
    gas := gasUsed.toNat
    log := (RLP'.list tr.acr.logs.reverse).encode.keccak
    sta := tr.sta
  }

def String.joinnl (l : List String) : String :=
  l.foldl (fun r s => r ++ "\n" ++ s) ""

def Test.run (t : Test) : IO Unit := do
  let ⟨tx, hsh⟩ ← decodeTxBytes t.txdata
--  .println s!"r-value : {tx.r.toHex}"
--  .println s!"s-value : {tx.s.toHex}"

  let rsa : ByteArray := Bytes.toBytesArray (tx.r ++ tx.s)
  let hsa : ByteArray := Bytes.toBytesArray (@Bits.toBytes 32 hsh)
  let ri : UInt8 := Byte.toB8 (if tx.yParity then 1 else 0)
  let sender ← publicAddress hsa ri rsa

  .println "initial world : "
  .println (Strings.join t.world.toStrings)

  -- let initNTB : NTB :=
  --   Lean.RBMap.fromList (List.map toKeyVal t.world.toList) _
  -- let initRoot : Word := trie initNTB
  -- .println s!"initial state root : {initRoot.toHex}"

  let sa₀ ← (t.world.find? sender).toIO "no sender account"

  .guard (tx.nonce = t.nonce) "nonce check 1 : fail"
  .println "nonce check 1 : pass"

  .guard (tx.nonce = sa₀.nonce) "nonce check 2 : fail"
  .println "nonce check 2 : pass"

  .guard (sender = t.sender) "sender check : fail"
  .println "sender check : pass"

  .guard (tx.receiver = t.receiver) "receiver check : fail"
  .println s!"receiver : {tx.receiver.toHex}"

  .guard (tx.gasLimit = t.gasLimit) "gas limit check : fail"
  .println "gas limit check : pass"

  .guard (tx.gasPrice = t.gasPrice) "gas price check : fail"
  .println "gas price check : pass"

  .guard (tx.val = t.value) "value check : fail"
  .println "value check : pass"

  .guard (tx.calldata = t.calldata) "calldata check : fail"
  .println "calldata check : pass"

  let rst ←
    Tx.run
      {
        baseFee := t.baseFee,
        ben := t.coinbase
        prevRandao := t.prevRandao
        gasLimit := t.blockGasLimit
        timestamp := t.timestamp
        number := t.number
        chainId := 1
      }
      t.world
      tx
      sender

  .println s!"tx status : {rst.sta}"
  .println "world state after tx :"
  .println (Strings.join rst.wld.toStrings)

  -- let _ ← (mapM toKeyValTest rst.wld.toList).toIO "match test failed"

  -- let temp := (List.map toKeyVal rst.wld.toList)
  let temp' := (List.map toKeyVal' rst.wld.toList)

  -- let finalNTB : NTB := Lean.RBMap.fromList temp _
  let finalNTB' : NTB' := Lean.RBMap.fromList temp' _

  -- dbg_trace "collapsed NTB :"
  -- dbg_trace (Strings.join (RLP.toStrings (collapse finalNTB)))
  -- dbg_trace "collapsed NTB' :"
  -- dbg_trace (Strings.join (RLP'.toStrings (collapse' finalNTB')))
  -- let root : Word  := trie finalNTB
  let root' : B256 := trie' finalNTB'

  --.println s!"computed final root  : {root.toHex}"
  .println s!"computed final root' : {root'.toHex}"
  .println s!"expected final root  : {t.hash.toHex}"

  -- .guard (root = t.hash) "state root check : fail"
  -- .println "state root check : pass"
  .guard (root' = t.hash.toB256) "state root' check : fail"
  .println "state root' check : pass"

  .guard (rst.log = t.logs) "log hash check : fail"
  .println "log hash check : pass"
  .println "test complete."

def Tests.run : Nat → List Test → IO Unit
  | _, [] => return ()
  | n, t :: ts => do
    .println s!"================ Running test {n} ================"
    t.run
    Tests.run (n + 1) ts

def List.toNTB (l : List (Word × Word)) : NTB :=
  Stor.toNTB <| .fromList l _

def main (args : List String) : IO Unit := do
  let testPath ← args.head?.toIO "no command line argument"
  let td ← readJsonFile testPath >>= Lean.Json.toTestData
  let ts ← getTests td
  --((ts.get? 2).toIO "test #2 does not exist") >>= Test.run
  Tests.run 1 ts

#exit

def main (args : List String) : IO Unit := do
  let arg ← args.head?.toIO "no command line argument"
  match arg.toNat? with
  | none => IO.println "Argument is not a number"
  | some n =>
    let w : Word := UInt8a.keccak (Array.mkArray n 0)
    IO.println s!"keccak of zeroes : {w.toHex}"

def main : IO Unit := do
  let td ← readJsonFile "not.json" >>= Lean.Json.toTestData
  IO.println td.toString

def main : IO Unit := IO.println WethByteCode
def main : IO Unit := do IO.println <| Bits.toHex 64 (trie testNTB)

def main : IO Unit := do
  let bs := notTxBytes
  let (RLP.list [nonce, gasPrice, gasLimit, toAddr, val, calldata, .bytes [v], .bytes r, .bytes s])
    ← (Option.toIO <| RLP.decode bs) ""
    | throw (IO.Error.userError "Error : RLP decoding failed")
  let bs' := RLP.encode <| .list [nonce, gasPrice, gasLimit, toAddr, val, calldata]
  let hs := bs'.keccak

  IO.println <| s!"v : {Bits.toHex 2 v}"
  IO.println <| s!"r : {r.toHex}"
  IO.println <| s!"s : {s.toHex}"
  IO.println <| s!"Hash of txdata excluding signature: {Bits.toHex 64 hs}"

  let rsa : ByteArray := Bytes.toBytesArray (r ++ s)
  let hsa : ByteArray := Bytes.toBytesArray (@Bits.toBytes 32 hs)
  let ri : UInt8 := Byte.toUInt8 (v - Ox x1 xB)

  match (ecrecoverFlag hsa ri rsa).toBytes with
  | [] => IO.println "Unreachable code : ecrecover should never return empty bytes"
  | b :: pa =>
    if b = 0
    then IO.println "ecrecover failed"
    else IO.println <| s!"Recovered public address : {Bytes.toHex pa}"
