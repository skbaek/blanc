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

-- #exit
-- partial def Bytes.chunks (bs : Bytes) : List Bytes :=
--   match bs.splitAt 32 with
--   | (_, []) => [bs]
--   | (bs', bs'') => bs' :: chunks bs''

def Bytes.toHexLine (bs : Bytes) : String :=
  s!"hex\"{bs.toHex}\""

def WethByteCode : String :=
  List.foldr
     (λ s0 s1 => s0 ++ "\n" ++ s1)
     "" <| List.map Bytes.toHexLine
        <| List.chunks 31 <| Option.getD weth.compile []


inductive RLP : Type
  | bytes : Bytes → RLP
  | list : List RLP → RLP

def List.splitAt? {ξ : Type u} : Nat → List ξ → Option (List ξ × List ξ)
  | 0, xs => some ([], xs)
  | _ + 1, [] => none
  | n + 1, x :: xs => .map (x :: ·) id <$> xs.splitAt? n


def Bytes.toNat' : Nat → Bytes → Nat
  | k, [] => k
  | k, b :: bs => Bytes.toNat' ((k * 256) + b.toNat) bs

def Bytes.toNat (bs : Bytes) : Nat := bs.toNat' 0


def Nat.toBytesCore (n : Nat) : Bytes :=
  if n < 256
  then [n.toByte]
  else (n % 256).toByte :: (n / 256).toBytesCore

def Nat.toBytes (n : Nat) : Bytes := n.toBytesCore.reverse

def Nat.toBool : Nat → Bool
  | 0 => 0
  | _ => 1

def Nat.toBitsAux' (n : Nat) : List Bool :=
  if n < 2
  then [n.toBool]
  else (n % 2).toBool :: (n / 2).toBitsAux'

def Nat.toBits' (m n : Nat) : Bits m :=
  let bs := (List.takeD m (Nat.toBitsAux' n) 0).reverse
  Bools.toBits m bs

mutual
  def RLP.decode' : Nat → Bytes → Option (RLP × Bytes)
    | _, [] => none
    | 0, _ :: _ => none
    | _ + 1, b@⦃0, _, _, _, _, _, _, _⦄ :: bs => some (.bytes [b], bs)
    | _ + 1, b@⦃1, 0, 1, 1, 1, _, _, _⦄ :: bs => do
      let (lbs, bs') ← List.splitAt? (b - Ox xB x7).toNat bs
      let (rbs, bs'') ← List.splitAt? (Bytes.toNat lbs) bs'
      return ⟨.bytes rbs, bs''⟩
    | _ + 1, b@⦃1, 0, _, _, _, _, _, _⦄ :: bs =>
      .map .bytes id <$> List.splitAt? (b - Ox x8 x0).toNat bs
    | k + 1, b@⦃1, 1, 1, 1, 1, _, _, _⦄ :: bs => do
      let (lbs, bs') ← List.splitAt? (b - Ox xF x7).toNat bs
      let (rbs, bs'') ← List.splitAt? (Bytes.toNat lbs) bs'
      let rs ← RLPs.decode k rbs
      return ⟨.list rs, bs''⟩
    | k + 1, b@⦃1, 1, _, _, _, _, _, _⦄ :: bs => do
      let (rbs, bs') ← List.splitAt? (b - Ox xC x0).toNat bs
      let rs ← RLPs.decode k rbs
      return ⟨.list rs, bs'⟩
  def RLPs.decode : Nat → Bytes → Option (List RLP)
    | _, [] => some []
    | 0, _ :: _ => none
    | k + 1, bs@(_ :: _) => do
      let (r, bs') ← RLP.decode' (k + 1) bs
      let rs ← RLPs.decode k bs'
      return (r :: rs)
end

def RLP.decode (bs : Bytes) : Option RLP :=
  match RLP.decode' bs.length bs with
  | some (r, []) => some r
  | _ => none

def RLP.encodeBytes : Bytes → Bytes
  | [b] =>
    if b < (Ox x8 x0)
    then [b]
    else [Ox x8 x1, b]
  | bs =>
    if bs.length < 56
    then (Ox x8 x0 + bs.length.toByte) :: bs
    else let lbs : Bytes := bs.length.toBytes
         (Ox xB x7 + lbs.length.toByte) :: (lbs ++ bs)

mutual
  def RLP.encode : RLP → Bytes
    | .bytes [b] =>
      if b < (Ox x8 x0)
      then [b]
      else [Ox x8 x1, b]
    | .bytes bs =>
      if bs.length < 56
      then (Ox x8 x0 + bs.length.toByte) :: bs
      else let lbs : Bytes := bs.length.toBytes
           (Ox xB x7 + lbs.length.toByte) :: (lbs ++ bs)
    | .list rs => RLPs.encode rs
  def RLPs.encodeMap : List RLP → Bytes
    | .nil => []
    | .cons r rs => r.encode ++ RLPs.encodeMap rs
  def RLPs.encode (rs : List RLP) : Bytes :=
    let bs := RLPs.encodeMap rs
    let len := bs.length
    if len < 56
    then (Ox xC x0 + len.toByte) :: bs
    else let lbs : Bytes := len.toBytes
         (Ox xF x7 + lbs.length.toByte) :: (lbs ++ bs)
end

partial def RLP.toStrings : RLP → List String
  | .bytes bs => [s!"0x{bs.toHex}"]
  | .list rs => "List:" :: (rs.map RLP.toStrings).flatten.map ("  " ++ ·)

def Strings.join : List String → String
  | [] => ""
  | s :: ss => s ++ "\n" ++ Strings.join ss

def Nibs.toBytes : List Nib → Option Bytes
  | [] => some []
  | [_] => none
  | h0 :: h1 :: hs => (Ox h0 h1 :: ·) <$> Nibs.toBytes hs

def Hex.toBytes (s : String) : Option Bytes :=
  s.data.mapM Hexit.toNib >>= Nibs.toBytes

def notTxBytes : Bytes :=
  (Hex.toBytes "f885800a8404c4b40094cccccccccccccccccccccccccccccccccccccccc01a4693c613900000000000000000000000000000000000000000000000000000000000000001ba0e8ff56322287185f6afd3422a825b47bf5c1a4ccf0dc0389cdc03f7c1c32b7eaa0776b02f9f5773238d3ff36b74a123f409cd6420908d7855bbe4c8ff63e00d698").getD []

def badTxBytes : Bytes :=
  (Hex.toBytes "f885800a8404c4b40094ccccc76482364981768476182936712638712ccc01a4693c613900000000000000000000000000000000000000000000000000000000000000001ba0e8ff56322287185f6afd3422a825b47bf5c1a4ccf0dc0389cdc03f7c1c32b7eaa0776b02f9f5773238d3ff36b74a123f409cd6420908d7855bbe4c8ff63e00d698").getD []

def highValueTxBytes : Bytes :=
  (Hex.toBytes "f87f800182520894095e7baea6a6c7c4c2dfeb977efac326af552d87a0ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff801ba048b55bfa915ac795c431978d8a6a992b628d557da5ff759b307d495a36649353a01fffd310ac743f371de3b9f7f9cb56c0b28ad43601b4ab949f53faa07bd2c804").getD []

def Option.toIO {ξ} (o : Option ξ) (msg : String) : IO ξ := do
  match o with
  | none => throw (IO.Error.userError msg)
  | some x => pure x

@[extern "ecrecover_flag"]
opaque ecrecoverFlag : ByteArray → UInt8 → ByteArray → ByteArray

def Bool.toByte : Bool → Byte
  | true => Ox x0 x1
  | false => Ox x0 x0

def Byte.toUInt8 (b : Byte) : UInt8 := ⟨⟨b.toNat, b.toNat_lt_pow⟩⟩
def UInt8.toByte (i : UInt8) : Byte := i.toBitVec.toFin.val.toByte
def Bits.toUInt64 (xs : Bits 64) : UInt64 := ⟨⟨xs.toNat, xs.toNat_lt_pow⟩⟩
def UInt64.toBits (i : UInt64) : Bits 64 := Nat.toBits 64 i.toBitVec.toFin.val

def Bytes.toBytesArray (bs : Bytes) : ByteArray := ⟨⟨List.map Byte.toUInt8 bs⟩⟩
def ByteArray.toBytes (a : ByteArray) : Bytes := a.data.toList.map UInt8.toByte

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

-- inductive Json where
--   | null
--   | bool (b : Bool)
--   | num (n : JsonNumber)
--   | str (s : String)
--   | arr (elems : Array Json)
--   -- uses RBNode instead of RBMap because RBMap is a def
--   -- and thus currently cannot be used to define a type that
--   -- is recursive in one of its parameters
--   | obj (kvPairs : RBNode String (fun _ => Json))
--   deriving Inhabited


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

-- def Stor := Lean.RBMap Word Word Ord.compare

def List.compare {ξ : Type u} [Ord ξ] : List ξ → List ξ → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: _, y :: _ => Ord.compare x y

instance {ξ : Type u} [Ord ξ] : Ord (List ξ) := ⟨List.compare⟩

abbrev NTB := Lean.RBMap Nibs Bytes compare
abbrev Stor := Lean.RBMap Word Word compare

structure EnvData where
  (coinbase : Addr)

structure PreData where
  (addr : Addr)
  (nonce : Bytes)
  (bal : Bytes)
  (stor : Stor)
  (code : Bytes)

structure PostData where
  (hash : Word)
  (dataIdx : Nat)
  (gasIdx : Nat)
  (valueIdx : Nat)
  (logs : Word)
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
  (stor : Stor)
  (code : Bytes)

abbrev World' : Type := Lean.RBMap Addr Acct compare

structure Test where
  (coinbase : Addr)
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
  (logs : Word) -- keccak hash of (RLP-encoded) log items
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
  | bss => "{hd} :" :: bss.map (λ bs' => pad (Bytes.toHex bs'))

def txdataToStrings (tx : Bytes) : List String :=
  match List.chunks 31 tx with
  | [] => ["txdata :"]
  | [bs] => [s!"txdata : {Bytes.toHex bs}"]
  | bss => "txdata :" :: bss.map (λ bs => pad (Bytes.toHex bs))

def Stor.toStrings (s : Stor) : List String :=
  let kvs := s.toArray.toList
  let kvToStrings : Word × Word → List String :=
    λ nb => [s!"{nb.fst.toString} : {nb.snd.toString}"]
  fork "stor" (kvs.map kvToStrings)

  -- nonce : Word)
  -- bal : Word)
  -- stor : Stor)
  -- code : Bytes)
def Acct.toStrings (s : String) (a : Acct) : List String :=
  fork s [
    [s!"nonce : 0x{a.nonce.toHex 64}"],
    [s!"bal : 0x{a.bal.toHex 64}"],
    a.stor.toStrings,
    longBytesToStrings "code" a.code
  ]

def postAcct.toStrings (p : PostData) : List String :=
  fork "Post Acct" [
    [s!"hash : {Bits.toHex 64 p.hash}"],
    [s!"data index : {p.dataIdx}"],
    [s!"gas index : {p.gasIdx}"],
    [s!"value index : {p.valueIdx}"],
    [s!"logs : {Bits.toHex 64 p.logs}"],
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
    [s!"nonce : 0x{t.nonce.toHex 64}"],
    [s!"gas price : 0x{t.gasPrice.toHex 64}"],
    [s!"gas limit : 0x{t.gasLimit.toHex 64}"],
    [s!"sender : 0x{t.sender.toHex 40}"],
    [s!"receiver : 0x{t.receiver.toHex 40}"],
    [s!"value : 0x{t.value.toHex 64}"],
    longBytesToStrings "calldata" t.calldata,
    [s!"hash : 0x{t.hash.toHex 64}"],
    [s!"logs : 0x{t.logs.toHex 64}"],
    [s!"secret : 0x{t.secret.toHex 64}"]
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
    return ⟨hs, d, g, v, lg, tx⟩
  | _ => IO.throw "Json-to-PostData failed"


-- def kbAdd {ξ υ o} (s : Lean.RBMap ξ υ o) (kv : (_ : String) × Json) : IO Stor := return s

def Lean.Json.toBytes (j : Json) : IO Bytes := do
  let x ← fromStr j >>= Hex.from0x
  (Hex.toBytes x).toIO ""

def Lean.Json.toBits (n : Nat) (j : Json) : IO (Bits (4 * n)) := do
  let x ← fromStr j >>= Hex.from0x
  (Hex.toBits n x).toIO ""


def Lean.Json.toPreData (sj : (_ : String) × Json) : IO PreData := do
  let ax ← Hex.from0x sj.fst
  let a ← (Hex.toBits 40 ax).toIO ""
  let r ← sj.snd.fromObj
  let b ← ((r.find Ord.compare "balance").toIO "" >>= toBytes)
  let c ← (r.find Ord.compare "code").toIO "" >>= toBytes
  let n ← ((r.find Ord.compare "nonce").toIO "" >>= toBytes)
  return ⟨a, n, b, Lean.RBMap.empty, c⟩

def Lean.Json.toEnvData (j : Lean.Json) : IO EnvData := do
  let r ← j.fromObj
  let cbj ← (r.find compare "currentCoinbase").toIO "No coinbase"
  let bs ← cbj.toBytes
  return ⟨bs.toBits 20⟩

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
        code := pd.code
      }
    ⟩
  Lean.RBMap.fromList (td.pre.map aux) _

def getTest (td : TestData) (p : PostData) : IO Test := do
  let cd ← (List.get? td.tx.data p.dataIdx).toIO ""
  let gl ← (List.get? td.tx.gasLimit p.gasIdx).toIO ""
  let vl ← (List.get? td.tx.value p.valueIdx).toIO ""
  return {
    coinbase := td.env.coinbase
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

def hpAux : Nibs → (Option Nib × Bytes)
  | [] => ⟨none, []⟩
  | n :: ns =>
    match hpAux ns with
    | ⟨none, bs⟩ => ⟨some n, bs⟩
    | ⟨some m, bs⟩ => ⟨none, (n ++ m) :: bs⟩

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


def NTB.empty : NTB := Lean.RBMap.empty

def sansPrefix : Nibs → Nibs → Option Nibs
  | [], ns => some ns
  | _, [] => none
  | n :: ns, n' :: ns' =>
    if n = n' then sansPrefix ns ns' else none

def insertSansPrefix (pfx : Nibs) (m : NTB) (ns : Nibs) (bs : Bytes) : Option NTB := do
  (m.insert · bs) <$> sansPrefix pfx ns

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

def NTBs.empty : NTBs :=
  ⟨ .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty ⟩

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

def collapse (j : NTB) : RLP := structComp (2 * (j.maxKeyLength + 1)) j

def trie (j : NTB) : Word := (collapse j).encode.keccak

def Word.toBytes (w : Word) : Bytes :=
  (@Bits.toBytes 32 w)

def Word.toRLP (w : Word) : RLP := .bytes w.toBytes

def Word.keccak (w : Word) : Word := (@Bits.toBytes 32 w).keccak

def Stor.toNTB (s : Stor) : NTB :=
  let f : NTB → Word → Word → NTB :=
    λ j k v =>
      j.insert
        (@Bits.toNibs 64 k.keccak)
        (RLP.encode <| .bytes <| @Bits.toBytes 32 v)
  Lean.RBMap.fold f NTB.empty s

def PreData.toKV (a : PreData) : Nibs × Bytes :=
  ⟨
    @Bits.toNibs 64 (@Bits.toBytes 20 a.addr).keccak,
    RLP.encode <| .list [
      .bytes a.nonce,
      .bytes a.bal,
      Word.toRLP (trie a.stor.toNTB),
      Word.toRLP <| Bytes.keccak a.code
    ]
  ⟩


def G_initcodeword : Nat := 2

def initCodeCost (cd : Bytes) : Nat :=
  G_initcodeword * ((cd.length / 32) + if 32 ∣ cd.length then 0 else 1)

def G_txcreate : Nat := 32000
def G_accesslistaddress : Nat := 2400
def G_accessliststorage : Nat := 1900




instance : Hashable Addr := ⟨Bits.toUInt64 ∘ @Bits.suffix 64 96⟩
instance : Hashable (Addr × Word) := ⟨Bits.toUInt64 ∘ @Bits.suffix 64 96 ∘ Prod.fst⟩

abbrev AddrSet : Type := @Std.HashSet Addr _ _ --⟨Bits.toUInt64 ∘ @Bits.suffix 64 96⟩
abbrev StorKeySet : Type := @Std.HashSet (Addr × Word) _ _

structure Accrual where
  (dest : List Addr) -- A_s
  (adrs : AddrSet) -- A_s
  (keys : StorKeySet) -- A_k
  (ref : Nat) -- A_r
  -- (sac : Nat) -- A_r

structure Machine where
  (gas : Nat) -- μ_g
  (pc : Nat) -- μ_pc
  (mem : Bytes) -- μ_m
  (ret : Bytes) -- μ_o
  (stk : Stack) -- μ_s

def ceilDiv (m n : Nat) := m / n + if m % n = 0 then 0 else 1

-- μ_i : no need to make it a separate field of Machine,
-- when it is completely determined by Machine.mem
def Machine.msz (m : Machine) : Nat := ceilDiv m.mem.length 32

structure Block where
  (ben : Addr) -- H_c

structure Env' where
  (cta : Addr) -- contract address (YP : a)
  (oga : Addr) -- origin address (YP : o)
  (gpr : Word) -- gas price (YP : p)
  (cld : Bytes) -- calldata (YP : d)
  (cla : Addr) -- caller Addr (YP : s)
  (clv : Word) -- callvalue (YP : v)
  (code : Bytes) -- contract code  (YP : b)
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

def State'.inst (s : State') : Option Inst := do
  let a ← s.wld.find? s.env.cta
  match a.code.get? s.mcn.pc with
  | none => return (.last .stop)
  | some b =>
    (b.toRinst? <&> (.next ∘ .reg)) <|>
    (b.toXinst? <&> (.next ∘ .exec)) <|>
    (b.toJinst? <&> .jump) <|>
    (b.toLinst? <&> .last) <|>
    ( if h : 95 ≤ b.toNat ∧ b.toNat ≤ 127
      then let len := b.toNat - 95
           let slc := a.code.sliceD (s.mcn.pc + 1) len 0
           let h_slc : slc.length ≤ 32 := by
             simp [len, slc, List.sliceD, h.right]
           some (.next <| .push slc h_slc)
      else none )

def g_zero : Nat := 0
def g_verylow : Nat := 3

def safeSub {ξ} [Sub ξ] [LE ξ] [@DecidableRel ξ (· ≤ ·)] (x y : ξ) : Option ξ :=
  if y ≤ x then some (x - y) else none

def State'.deductGas (s : State') (c : Nat) : Option Nat := safeSub s.mcn.gas c

def Rinst.run (s : State') : Rinst → Option State'
  | .add => do
    let (x :: y :: xs) ← (return s.mcn.stk) | none
    let g' ← safeSub s.mcn.gas g_verylow
    return {s with mcn := {s.mcn with stk := (x + y) :: xs, gas := g', pc := s.mcn.pc + 1}}
  | .calldataload => do
    let (x :: xs) ← (return s.mcn.stk) | none
    let g' ← s.deductGas g_verylow
    let cd : Word := Bytes.toBits 32 (s.env.cld.sliceD x.toNat 32 0)
    return {s with mcn := {s.mcn with stk := cd :: xs, gas := g', pc := s.mcn.pc + 1}}
  | _ => none

def Acct.Empty (a : Acct) : Prop :=
  a.code = [] ∧ a.nonce = 0 ∧ a.bal = 0

def Dead (w : World') (a : Addr) : Prop :=
  match w.find? a with
  | none => True
  | some x => x.Empty

def gNewAccount : Nat := 25000
def gCallValue : Nat := 9000
def gCallStipend : Nat := 2300

instance {w a} : Decidable (Dead w a) := by
  simp [Dead]
  cases (Lean.RBMap.find? w a)
  · simp; apply instDecidableTrue
  · simp [Acct.Empty]; apply instDecidableAnd

def gWarmAccess : Nat := 100
def gColdAccountAccess : Nat := 2600

def cAAccess (x : Addr) (a : AddrSet) : Nat :=
  if x ∈ a then gWarmAccess else gColdAccountAccess

def except64th (n : Nat) : Nat := n - (n / 64)

def cExtra (s : State') (t : Addr) (v : Word) : Nat :=
  let cNew : Nat := if (Dead s.wld t ∧ v ≠ 0) then gNewAccount else 0
  let cXfer : Nat := if v ≠ 0 then gCallValue else 0
  cAAccess t s.acr.adrs + cXfer + cNew

def cGasCap (s : State') (g : Nat) (t : Addr) (v : Word) : Nat :=
    if cExtra s t v ≤ s.mcn.gas
    then min (except64th (s.mcn.gas - cExtra s t v)) g
    else g

def cCallGas (s : State') (g : Nat) (t : Addr) (v : Word) : Nat :=
  if v ≠ 0
  then cGasCap s g t v + gCallStipend
  else cGasCap s g t v

def cCall (s : State') (g : Nat) (t : Addr) (v : Word) : Nat :=
  cGasCap s g t v + cExtra s t v

structure theta.Result : Type where
  (wld : World')
  (gas : Nat)
  (acr : Accrual)
  (sta : Word)
  (ret : Bytes)

def World'.code (w : World') (a : Addr) : Bytes :=
  match w.find? a with
  | none => []
  | some x => x.code

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
      else σ.insert r {nonce := 0, bal := v, stor := .empty, code := []}
    | some aᵣ => σ.insert r {aᵣ with bal := aᵣ.bal + v}
  let σ₁ : World' :=
    match σ'₁.find? s with
    | none =>
      if v = 0
      then σ'₁
      else (dbg_trace "unreachable code : nonzero value calls from empty accounts should never happen" ; σ'₁)
    | some aₛ => σ.insert s {aₛ with bal := aₛ.bal - v}
  let cd : Bytes := σ.code c
  let I : Env' := {
    cta := r, oga := o, gpr := @Nat.toBits 256 p, cld := d
    cla := s, clv := v_app, code := cd, blk := H, exd := e, wup := w
  }
  let μ : Machine := {gas := g, pc := 0, mem := [], ret := [], stk := []}
  ⟨σ₁, μ, A, I⟩

def θ.wrap (s : State') (oxr : Option exec.Result) : theta.Result :=
  let xr : exec.Result := oxr.getD ⟨none, s.mcn, s.acr, none⟩
  let Ξr : Ξ.Result := {wld := xr.wld, gas := xr.mcn.gas, acr := xr.acr, ret := xr.ret}
  let σ_stars : Option World' := Ξr.wld
  let g_stars : Nat := Ξr.gas
  let A_stars : Accrual := Ξr.acr
  let o : Option Bytes := Ξr.ret

  let σ' : World' := σ_stars.getD s.wld
  let g' : Nat := if σ_stars.isNone ∧ o.isNone then 0 else g_stars
  let A' : Accrual := if σ_stars.isNone then s.acr else A_stars
  let z : Word := if σ_stars.isNone then 0 else 1

  -- o' is not from YP, but necessary to cast from 'Option Bytes' to 'Bytes'
  -- (YP is a bit sloppy with types here)
  let o' : Bytes := o.getD []
  ⟨σ', g', A', z, o'⟩


-- returns 'none' IFF either
-- (1) VM is CURRENTLY at EHS, due to the code byte at PC (not at some later point in code), or
-- (2) recursion limit is reached (should never happen with correct usage)
def execAux (s s' : State') (f : State' → Option exec.Result) : exec.Result :=
  let g' : Nat := s'.mcn.gas
  let s'' := {s' with mcn := {s'.mcn with gas := g'}}
  (f s'').getD ⟨none, s''.mcn, s''.acr, none⟩

def gColdSLoad : Nat := 2100
def gSSet : Nat := 20000
def gSReset : Nat := 2900
def rSClear : Nat := 4800

def Jinst.toString : Jinst → String
  | .jump => "JUMP"
  | .jumpdest => "JUMPDEST"
  | .jumpi => "JUMPI"

def Inst.toString : Inst → String
  | .next n => n.toString
  | .jump j => j.toString
  | .last l => l.toString

def Bits.min {n} : Bits n → Bits n → Bits n
  | xs, ys => if xs ≤ ys then xs else ys

instance {n} : Min (Bits n) := ⟨.min⟩

def testStor : Stor :=
  Lean.RBMap.singleton 0
    ((Hex.toWord "fffffffffffffffffffffffffffffffffffffffffffffffffedcba9876543210").getD 0)

def testerAdr : Addr := (Hex.toBits 40 "0000000000000000000000000000000000001000").getD 0
def senderAdr : Addr := (Hex.toBits 40 "a94f5374fce5edbc8e2a8697c15331677e6ebf0b").getD 0
def receiverAdr : Addr := (Hex.toBits 40 "cccccccccccccccccccccccccccccccccccccccc").getD 0

def beforeBal : Word := Bytes.toBits 32 <| (Hex.toBytes "0ba1a9ce0ba1a9ce").getD []


def beforeTesterAcct : Acct :=
  {
    nonce := 0
    bal := beforeBal
    stor := .empty
    code := (Hex.toBytes "670123456789abcdef1960005500").getD []
  }

def afterTesterAcct : PreData :=
  {
    addr := testerAdr
    nonce := []
    bal := (Hex.toBytes "0ba1a9ce0ba1a9ce").getD []
    stor := testStor
    code := (Hex.toBytes "670123456789abcdef1960005500").getD []
  }

def beforeSenderAcct : Acct :=
  {
    nonce := 0
    bal := beforeBal
    stor := .empty
    code := []
  }

def afterSenderAcct : PreData :=
  {
    addr := senderAdr
    nonce := [Ox x0 x1]
    bal := (Hex.toBytes "0ba1a9ce0b9aa79f").getD []
    stor := .empty
    code := []
  }

def beforeReceiverAcct : Acct :=
  {
    nonce := 0
    bal := beforeBal
    stor := .empty
    code := (Hex.toBytes "600060006000600060006004356110000162fffffff100").getD []
  }

def afterReceiverAcct : PreData :=
  {
    addr := receiverAdr
    nonce := []
    bal := (Hex.toBytes "0ba1a9ce0ba1a9cf").getD []
    stor := .empty
    code := (Hex.toBytes "600060006000600060006004356110000162fffffff100").getD []
  }

def afterPreDatas : List PreData :=
  [
    afterTesterAcct,
    afterSenderAcct,
    afterReceiverAcct
  ]

def testNTB : NTB := Lean.RBMap.fromList (List.map PreData.toKV afterPreDatas) compare


def beforeWorld : World' :=
  Lean.RBMap.fromList
    [
      ⟨testerAdr, beforeTesterAcct⟩,
      ⟨senderAdr, beforeSenderAcct⟩,
      ⟨receiverAdr, beforeReceiverAcct⟩
    ]
    _

def afterWorld : World' :=
  let aux : PreData → (Addr × Acct) :=
    fun pa => ⟨pa.addr, ⟨pa.nonce.toBits 32, pa.bal.toBits 32, pa.stor, pa.code⟩⟩
  Lean.RBMap.fromList (afterPreDatas.map aux) _


-- gas limit ('T_g' in YP)
def Tg : Nat := ((Hex.toBytes "04C4B400").getD []).toNat
def testGasLimit : Nat := ((Hex.toBytes "04C4B400").getD []).toNat

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

def testCallData : Bytes :=
  (Hex.toBytes "693c61390000000000000000000000000000000000000000000000000000000000000000").getD []

def g₀ : Nat := intrinsicGas (some receiverAdr) testCallData []

def g : Nat := Tg - g₀


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

def testCoinbase : Addr := (Hex.toBits 40 "2adc25665018aa1fe0e6bc666dac8fc2697ff9ba").getD 0

def testCheckpoint : World' := (checkpoint beforeWorld senderAdr 1).getD beforeWorld

-- A^0
def Accrual.init : Accrual :=
  {
    dest := []
    adrs := Std.HashSet.ofList [1, 2, 3, 4, 5, 6, 7, 8, 9]
    keys := .empty
    ref := 0
  }

abbrev AccessList : Type := List (Addr × List Word)

abbrev AccessList.collect (al : AccessList) : StorKeySet :=
  let addPair : Addr → StorKeySet → Word → StorKeySet :=
    fun a aks k => aks.insert ⟨a, k⟩
  let addElem : StorKeySet → Addr × List Word → StorKeySet :=
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

def testBlock : Block := {ben := testCoinbase}

def sstoreStep (w₀ : World') (s : State') : Option State' := do
  let ⟨σ, μ, A, I⟩ := s
  let (x :: v' :: xs) ← (return μ.stk) | none
  let (a₀ : Acct) ← w₀.find? I.cta
  let (v₀ : Word) := (a₀.stor.find? x).getD 0
  let (a : Acct) ← σ.find? s.env.cta
  let (v : Word) := (a.stor.find? x).getD 0
  let c₀ : Nat := cond (A.keys.contains ⟨I.cta, x⟩) 0 gColdSLoad
  -- let .true ← (dbg_trace s!"v₀ : {Bits.toHex 64 v₀}\nv : {Bits.toHex 64 v}\nv' : {Bits.toHex 64 v'}"; return true) | none
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
         then if v₀ = 0
              then rSClear
              else 0
         else rDirtyClear + rDirtyReset
  let g' ← safeSub s.mcn.gas c
  let ref' ← (Int.ofNat A.ref + r).toNat'
  let a' : Acct := {a with stor := a.stor.insert x v'}

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


-- match (dbg_trace "Gas left : {μ.gas}\n\nPC : {μ.pc}\nInst read : {i.toString}"; i) with
-- w₀ : the 'checkpoint' world saved at the preparation stage of tx
def exec (H : Block) (w₀ : World') : Nat → State' → Option exec.Result
  | 0, _ => do (dbg_trace "NO INST\n"; none)
  | lim + 1, s@⟨σ, μ, A, I⟩ => do
    let i ← s.inst
    match i with
    | .next (.push bs _) => do
       let g' ← safeSub μ.gas g_verylow
       let m' : Machine := {
         s.mcn with
         gas := g'
         pc := μ.pc + bs.length + 1
         stk := (bs.toBits 32) :: s.mcn.stk
       }
       execAux s {s with mcn := m'} (exec H w₀ lim)
    | .next (.reg .calldataload) => do
      let (x :: xs) ← (return s.mcn.stk) | none
      let g' ← s.deductGas g_verylow
      let cd : Word := Bytes.toBits 32 (s.env.cld.sliceD x.toNat 32 0)
      let s' := {s with mcn := {s.mcn with stk := cd :: xs, gas := g', pc := s.mcn.pc + 1}}
      execAux s s' (exec H w₀ lim)
    | .next (.reg .not) => do
      let (x :: xs) ← (return s.mcn.stk) | none
      let g' ← safeSub s.mcn.gas g_verylow
      let s' := {s with mcn := {s.mcn with stk := x.not :: xs, gas := g', pc := s.mcn.pc + 1}}
      execAux s s' (exec H w₀ lim)

    | .next (.reg .add) => do
      let (x :: y :: xs) ← (return s.mcn.stk) | none
      let g' ← safeSub s.mcn.gas g_verylow
      let s' := {s with mcn := {s.mcn with stk := (x + y) :: xs, gas := g', pc := s.mcn.pc + 1}}
      execAux s s' (exec H w₀ lim)
    | .next (.exec .call) => do
      let (gas :: adr :: clv :: ilc :: isz :: olc :: osz :: stk)
        ← (return s.mcn.stk) | none
      let i : Bytes := s.mcn.mem.sliceD ilc.toNat isz.toNat 0
      let t : Addr := toAddr adr
      let acct ← s.wld.find? s.env.cta
      let as' : AddrSet := s.acr.adrs.insert (toAddr adr)
      let A' : Accrual := {s.acr with adrs := as'}


      let cg : Nat := cCallGas s gas.toNat t clv

      --let g' ← (dbg_trace "after EIP-2929 : "; (safeSub s.mcn.gas gColdAccountAccess).trace)
      let g' ← safeSub s.mcn.gas gColdAccountAccess
      --let g'' ← (dbg_trace "after deducting callgas : "; (safeSub g' cg).trace)
      let g'' ← safeSub g' cg

      let trState : State' :=
         θ.prep H s.wld A' s.env.cta s.env.oga t t cg s.env.gpr.toNat clv clv i (s.env.exd - 1) s.env.wup
      let trCore : theta.Result := θ.wrap trState (exec H w₀ lim trState)

      let tr : theta.Result :=
        if 0 < s.env.exd ∧ clv ≤ acct.bal
        then trCore
        else ⟨s.wld, cg, A', 0, []⟩
      let cpy : Bytes := List.take osz.toNat tr.ret
      let m' : Machine := {
        gas := g'' + tr.gas
        pc := s.mcn.pc + 1
        mem := s.mcn.mem.takeD olc.toNat 0 ++ cpy ++ s.mcn.mem.drop (olc.toNat + cpy.length)
        ret := tr.ret
        stk := tr.sta :: stk
      }

      let s' : State' := {wld := tr.wld, mcn := m', acr := tr.acr, env := s.env}
      let s'' : State' := s' -- todo : make s'' the result of deducting
                             -- memory expansion gas costs from s'
      execAux s s'' (exec H w₀ lim)
    | .next (.reg .sstore) => do
      let s' ← sstoreStep w₀ s
      execAux s s' (exec H w₀ lim)
    | .last .stop => some {wld := σ, mcn := μ, acr := A, ret := some []}
    | _ => none

def theta
  (H : Block)
  (σ₀ : World')
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
  theta.Result :=
  let xr := θ.prep H σ A s o r c g p v v_app d e w
  θ.wrap xr (exec H σ₀ 100 xr)

def foo :=
  theta
    testBlock
    testCheckpoint
    testCheckpoint
    (A_star testBlock senderAdr (some receiverAdr) [])
    senderAdr
    senderAdr
    receiverAdr
    receiverAdr
    g
    10
    1
    1
    testCallData
    1024
    true


def g' : Nat := foo.gas

def A_r : Nat := 0 -- SSTORE used only once, cannot change from 0

def gstar : Nat := g' + min ((Tg - g') / 5) A_r

def balInit : Nat := Bytes.toNat ((Hex.toBytes "0ba1a9ce0ba1a9ce").getD [])

def txVal : Nat := 1

-- def Yg : Nat := Tg - gstar
def Yg : Nat := Tg - gstar

def gasPrice : Nat := 10

def balFinal : Nat := balInit - ((Yg * gasPrice) + txVal)

#eval (Nat.toBytes balFinal).toHex
#check Nat.toBytes


def publicAddress (hsa : ByteArray) (ri : UInt8) (rsa : ByteArray) : IO Addr :=
  match (ecrecoverFlag hsa ri rsa).toBytes with
  | [] => IO.throw "Unreachable code : ecrecover should never return empty bytes"
  | b :: pa =>
    if b = 0
    then IO.throw "ecrecover failed"
    else return (Bytes.toBits 20 pa)

def IO.guard (φ : Prop) [Decidable φ] (msg : String) : IO Unit :=
  if φ then return () else IO.throw msg


structure TxData : Type where
  (nonce : Word)
  (gasPrice : Word)
  (gasLimit : Word)
  (receiver : Addr)
  (val : Word)
  (calldata : Bytes)
  (v : Byte)
  (r : Bytes)
  (s : Bytes)
  (hash : Word)

def decodeTxBytes (tbs : Bytes) : IO TxData := do
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
    return {
      nonce := @Bytes.toBits 32 nonce
      gasPrice := @Bytes.toBits 32 gasPrice
      gasLimit := @Bytes.toBits 32 gasLimit
      receiver := @Bytes.toBits 20 toAddr
      val := @Bytes.toBits 32 val
      calldata := calldata
      v := v
      r := r
      s := s
      hash := bs.keccak
    }
  | _ => IO.throw "Error : TX bytes decoding failed"

def eqTest {ξ} [DecidableEq ξ] (x y : ξ) (testName : String) : IO Unit := do
  .guard (x = y) (testName ++ " : fail")
  .println (testName ++ " : pass")

def main : IO Unit := do
  let td ← readJsonFile "not.json" >>= Lean.Json.toTestData
  IO.println td.toString
  IO.println "======================================================"
  let [t] ← getTests td | IO.throw "more than one test"
  IO.println t.toString
  let txd ← decodeTxBytes t.txdata

  IO.println <| s!"v : {Bits.toHex 2 txd.v}"
  IO.println <| s!"r : {txd.r.toHex}"
  IO.println <| s!"s : {txd.s.toHex}"
  IO.println <| s!"Hash of txdata excluding signature: {Bits.toHex 64 txd.hash}"

  let rsa : ByteArray := Bytes.toBytesArray (txd.r ++ txd.s)
  let hsa : ByteArray := Bytes.toBytesArray (@Bits.toBytes 32 txd.hash)
  let ri : UInt8 := Byte.toUInt8 (txd.v - Ox x1 xB)

  let sender ← publicAddress hsa ri rsa
  IO.println <| s!"Recovered public address : {@Bits.toHex 40 sender}"

  eqTest txd.nonce t.nonce "nonce check"
  eqTest txd.gasPrice t.gasPrice "gas price check"
  eqTest txd.gasLimit t.gasLimit "gas limit check"
  eqTest sender t.sender "sender address check"
  eqTest txd.receiver t.receiver "sender address check"
  eqTest txd.val t.value "value check"
  eqTest txd.calldata t.calldata "value check"


  let g : Nat := txd.gasLimit.toNat - intrinsicGas (some txd.receiver) txd.calldata []

  let blk : Block := {ben := t.coinbase}
  let w ← (checkpoint t.world sender txd.val).toIO ""

  let tr : theta.Result :=
    theta
      blk
      w w
      (A_star blk sender (some txd.receiver) [])
      sender
      sender
      txd.receiver
      txd.receiver
      g
      txd.gasPrice.toNat
      txd.val
      txd.val
      txd.calldata
      1024
      true

  let gasLeft : Nat := tr.gas
  let refundAmount : Nat := 0 -- SSTORE used only once, cannot change from 0
  let gasReturn : Nat := gasLeft + min ((Tg - g') / 5) refundAmount
  let gasDiff : Nat := txd.gasLimit.toNat - gasReturn
  let senderAcct ← (w.find? sender).toIO ""
  let newBal : Nat := senderAcct.bal.toNat - (gasDiff * txd.gasPrice.toNat)

  let newBalWord : Word := Nat.toBits' 256 newBal

  IO.println s!"New sender balance : {@Bits.toHex 64 newBalWord}"

  return ()


#exit

-- def main : IO Unit := do
--   let td ← readJsonFile "not.json" >>= Lean.Json.toTestData
--   IO.println td.toString

-- def main : IO Unit := IO.println WethByteCode
-- def main : IO Unit := do IO.println <| Bits.toHex 64 (trie testNTB)

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


-- mutual
--
--   def Ξ
--     (σ : World')
--     (g : Nat)
--     (A : Accrual)
--     (I : Env) :
--     Ξ.Result :=
--   let μ : Machine := {gas := g, pc := 0, mem := [], ret := [], stk := []}
--   let xr : exec.Result := (execCore ⟨σ, μ, A, I⟩).getD ⟨none, μ, A, none⟩
--   {wld := xr.wld, gas := xr.mcn.gas, acr := xr.acr, ret := xr.ret}
--
--
--   def θ
--     (lim : Measure)
--     (σ : World')
--     (A : Accrual)
--     (s : Addr)
--     (o : Addr)
--     (r : Addr)
--     (c : Addr)
--     (g : Nat)
--     (p : Nat)
--     (v : Word)
--     (v_app : Word)
--     (d : Bytes)
--     (e : Nat)
--     (w : Bool) :
--     theta.Result :=
--   let σ'₁ : World' :=
--     match σ.find? r with
--     | none =>
--       if v = 0
--       then σ
--       else σ.insert r {nonce := 0, bal := v, stor := .empty, code := []}
--     | some aᵣ => σ.insert r {aᵣ with bal := aᵣ.bal + v}
--   let σ₁ : World' :=
--     match σ'₁.find? s with
--     | none =>
--       if v = 0
--       then σ'₁
--       else (dbg_trace "unreachable code : nonzero value calls from empty accounts should never happen" ; σ'₁)
--     | some aₛ => σ.insert s {aₛ with bal := aₛ.bal - v}
--   let cd : Bytes := σ.code c
--   let I : Env := {
--     cta := r, oga := o, gpr := @Nat.toBits 256 p, cld := d
--     cla := s, clv := v_app, code := cd, exd := e, wup := w
--   }
--   let Ξr : Ξ.Result :=
--     match c.toNat with
--     | 1 => (dbg_trace "unimplemented : precompiled contract"; sorry)
--     | 2 => (dbg_trace "unimplemented : precompiled contract"; sorry)
--     | 3 => (dbg_trace "unimplemented : precompiled contract"; sorry)
--     | 4 => (dbg_trace "unimplemented : precompiled contract"; sorry)
--     | 5 => (dbg_trace "unimplemented : precompiled contract"; sorry)
--     | 6 => (dbg_trace "unimplemented : precompiled contract"; sorry)
--     | 7 => (dbg_trace "unimplemented : precompiled contract"; sorry)
--     | 8 => (dbg_trace "unimplemented : precompiled contract"; sorry)
--     | 9 => (dbg_trace "unimplemented : precompiled contract"; sorry)
--     | _ => Ξ lim σ₁ g A I
--
--   let σ_stars : Option World' := Ξr.wld
--   let g_stars : Nat := Ξr.gas
--   let A_stars : Accrual := Ξr.acr
--   let o : Option Bytes := Ξr.ret
--
--   let σ' : World' := σ_stars.getD σ
--   let g' : Nat := if σ_stars.isNone ∧ o.isNone then 0 else g_stars
--   let A' : Accrual := if σ_stars.isNone then A else A_stars
--   let z : Word := if σ_stars.isNone then 0 else 1
--   -- o' is not from YP, but necessary to cast from 'Option Bytes' to 'Bytes'
--   let o' : Bytes := o.getD []
--   ⟨σ', g', A', z, o'⟩
--   termination_by lim
--
--   -- if EVM is in EHS at the point of running the Xinst, return 'none'.
--   -- in all other cases, return 'some'
--   def Xinst.run (lim : Measure) (s : State') : Xinst → Option State'
--     | .call => do
--       let (gas :: adr :: clv :: ilc :: isz :: olc :: osz :: stk)
--         ← (return s.mcn.stk) | none
--       let i : Bytes := s.mcn.mem.sliceD ilc.toNat isz.toNat 0
--       let t : Addr := toAddr adr
--       let acct ← s.wld.find? s.env.cta
--       let as' : AddrSet := s.acr.adrs.insert (toAddr adr)
--       let A' : Accrual := {s.acr with adrs := as'}
--       let cg : Nat := cCallGas s gas.toNat t clv
--       let tr : theta.Result :=
--         if 0 < s.env.exd ∧ clv ≤ acct.bal
--         then θ lim s.wld A' s.env.cta s.env.oga t t cg
--                s.env.gpr.toNat clv clv i (s.env.exd - 1) s.env.wup
--         else ⟨s.wld, cg, A', 0, []⟩
--       let cpy : Bytes := List.take osz.toNat tr.ret
--       let m' : Machine := {
--         gas := s.mcn.gas - cg + tr.gas
--         pc := s.mcn.pc + 1
--         mem := s.mcn.mem.takeD olc.toNat 0 ++ cpy ++ s.mcn.mem.drop (olc.toNat + cpy.length)
--         ret := tr.ret
--         stk := tr.sta :: s.mcn.stk
--       }
--       some {wld := tr.wld, mcn := m', acr := tr.acr, env := s.env}
--     | _ => none
--   termination_by lim
--
--   def Ninst.run (lim : Measure) (s : State') : Ninst → Option State'
--     | .push bs _ => do
--       let g' ← safeSub s.mcn.gas g_verylow
--       return {s with mcn := {s.mcn with stk := (bs.toBits 32) :: s.mcn.stk, gas := g'}}
--     | .exec x => x.run lim s
--     | .reg r => r.run s
--   termination_by lim
--
--   def execCore (lim : Measure) (s : State') : Option exec.Result :=
--     match lim with
--     | 0 => none
--     | k + 1 =>  do
--       let i ← s.inst
--       match i with
--       | .next n => n.run k s >>= execCore k --⟨k, false⟩
--       | .jump j => none
--       | .last l => none
--   termination_by lim
--
  -- -- X of YP
  -- def exec (s : State') : exec.Result :=
  --   (execCore (s.mcn.gas + 1) s).getD ⟨none, s.mcn, s.acr, none⟩
