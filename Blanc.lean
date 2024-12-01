import Lean.Data.Json
import Lean.Data.Json.Parser
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

-- def main : IO Unit := IO.println WethByteCode

--mutual
--  inductive RLP : Type
--    | bytes : Bytes → RLP
--    | list : RLPs → RLP
--  inductive RLPs : Type
--    | nil : RLPs
--    | cons : RLP → RLPs → RLPs
--end
--
--#exit
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

#eval (RLP.encode (.list [])).toHex

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

structure PreAcct where
  (addr : Addr)
  (nonce : Bytes)
  (bal : Bytes)
  (stor : Stor)
  (code : Bytes)

structure PostAcct where
  (hash : Word)
  (dataIdx : Nat)
  (gasIdx : Nat)
  (valueIdx : Nat)
  (logs : Word)
  (txdata : Bytes)

structure TX : Type where
  (data : List Bytes)
  (gasLimit : List Word)
  (gasPrice : Word)
  (nonce : Word)
  (secretKey : Word)
  (sender : Addr)
  (receiver : Addr)
  (value : List Word)

structure TestFile where
  (info : Lean.Json)
  (env  : Lean.Json)
  (pre  : List PreAcct)
  (post : String × List PostAcct)
  (tx   : TX)

structure Test where
  (pre  : List PreAcct)
  (txdata : Bytes)
  (data : Bytes)
  (gasLimit : Word)
  (gasPrice : Word)
  (nonce : Word)
  (secretKey : Word)
  (sender : Addr)
  (receiver : Addr)
  (value : Word)
  (hash : Word) -- ?
  (logs : Word) -- keccak hash of (RLP-encoded) log items

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

def txdataToStrings (tx : Bytes) : List String :=
  match List.chunks 31 tx with
  | [] => ["txdata :"]
  | [bs] => [s!"txdata : {Bytes.toHex bs}"]
  | bss => "txdata :" :: bss.map (λ bs => pad (Bytes.toHex bs))

def postAcct.toStrings (p : PostAcct) : List String :=
  fork "Post Acct" [
    [s!"hash : {Bits.toHex 64 p.hash}"],
    [s!"data index : {p.dataIdx}"],
    [s!"gas index : {p.gasIdx}"],
    [s!"value index : {p.valueIdx}"],
    [s!"logs : {Bits.toHex 64 p.logs}"],
    txdataToStrings p.txdata
  ]

def Stor.toStrings (s : Stor) : List String :=
  let kvs := s.toArray.toList
  let kvToStrings : Word × Word → List String :=
    λ nb => [s!"{nb.fst.toString} : {nb.snd.toString}"]
  fork "stor" (kvs.map kvToStrings)

#check Bytes.toHex

def NTB.toStrings (s : NTB) : List String :=
  let kvs := s.toArray.toList
  let kvToStrings : Nibs × Bytes → List String :=
    λ nb => [s!"{nb.fst.toHex} : {nb.snd.toHex}"]
  fork "NTB" (kvs.map kvToStrings)

def preAcct.toStrings (p : PreAcct) : List String :=
  fork "Pre Acct" [
    [s!"address : {Bits.toHex 40 p.addr}"],
    [s!"nonce : {Bytes.toHex p.nonce}"],
    [s!"balance : {Bytes.toHex p.bal}"],
    p.stor.toStrings,
    [s!"code : {Bytes.toHex p.code}"]
  ]

def postToStrings : (String × List PostAcct) → List String
  | ⟨s, ps⟩ => fork "Post" [[s], listToStrings postAcct.toStrings ps]

def preToStrings (l : List PreAcct) : List String :=
  fork "pre" [listToStrings preAcct.toStrings l]

def TX.toStrings (tx : TX) : List String :=
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

def TestFile.toStrings (t : TestFile) : List String :=
  fork "VM Test" [
    ["info ..."],--t.info.toStrings,
    ["env ..."],--t.env.toStrings,
    preToStrings t.pre,
    postToStrings t.post,
    t.tx.toStrings
  ]

def TestFile.toString (t : TestFile) : String := Strings.join t.toStrings

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

def Lean.Json.toPostAcct : Json → IO PostAcct
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
  | _ => IO.throw "Json-to-PostAcct failed"


-- def kbAdd {ξ υ o} (s : Lean.RBMap ξ υ o) (kv : (_ : String) × Json) : IO Stor := return s

def Lean.Json.toBytes (j : Json) : IO Bytes := do
  let x ← fromStr j >>= Hex.from0x
  (Hex.toBytes x).toIO ""

def Lean.Json.toBits (n : Nat) (j : Json) : IO (Bits (4 * n)) := do
  let x ← fromStr j >>= Hex.from0x
  (Hex.toBits n x).toIO ""


def Lean.Json.toPreAcct (sj : (_ : String) × Json) : IO PreAcct := do
  -- let a ← Hex.from0x sj.fst >>= (Option.toIO ∘ Hex.toBits 40)
  let ax ← Hex.from0x sj.fst
  let a ← (Hex.toBits 40 ax).toIO ""
  let r ← sj.snd.fromObj
  let b ← ((r.find Ord.compare "balance").toIO "" >>= toBytes) --<&> Bytes.toBits 32
  let c ← (r.find Ord.compare "code").toIO "" >>= toBytes
  let n ← ((r.find Ord.compare "nonce").toIO "" >>= toBytes) -- <&> Bytes.toBits 32
  --let sr ← (r.find Ord.compare "storage").toIO >>= fromObj
  --let kvs := sr.toArray.toList
  --let s ← kvs.foldlM Stor.add (Lean.RBMap.empty : Stor)
  return ⟨a, n, b, Lean.RBMap.empty, c⟩

def Lean.Json.toPre (j : Lean.Json) : IO (List PreAcct) := do
  let r ← j.fromObj
  let kvs := r.toArray.toList
  mapM Lean.Json.toPreAcct kvs

def Lean.Json.toPost (j : Lean.Json) : IO (String × List PostAcct) := do
  let ⟨k, j'⟩ ← j.fromSingleton
  let l ← j'.fromArr
  let js ← mapM Lean.Json.toPostAcct l
  return ⟨k, js⟩

def Bytes.toWord : Bytes → Word := Bytes.toBits 32

def Lean.Json.toTX (j : Lean.Json) : IO TX := do
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

def Lean.Json.toTestFile (j : Lean.Json) : IO TestFile := do
  let (_, .obj r) ← j.fromSingleton | IO.throw "not singleton object"
  let info ← (r.find compare "_info").toIO ""
  let env ←  (r.find compare "env").toIO ""
  let pre ←  (r.find compare "pre").toIO "" >>= Lean.Json.toPre
  let post ← (r.find compare "post").toIO "" >>= Lean.Json.toPost
  let tx ←   (r.find compare "transaction").toIO "" >>= Lean.Json.toTX
  return ⟨info, env, pre, post, tx⟩

-- structure PostAcct where
--   (hash : Word)
--   (dataIdx : Nat)
--   (gasIdx : Nat)
--   (valueIdx : Nat)
--   (logs : Word)
--   (txdata : Bytes)
--
-- structure TX : Type where
--   (data : List Bytes)
--   (gasLimit : List Word)
--   (gasPrice : Word)
--   (nonce : Word)
--   (secretKey : Word)
--   (sender : Addr)
--   (receiver : Addr)
--   (value : List Word)

def getTest (ps : List PreAcct) (tx : TX) (p : PostAcct) : IO Test := do
  let d ← (List.get? tx.data p.dataIdx).toIO ""
  let gl ← (List.get? tx.gasLimit p.gasIdx).toIO ""
  let vl ← (List.get? tx.value p.valueIdx).toIO ""
  return {
    pre := ps
    txdata := p.txdata
    data := d
    gasLimit := gl
    gasPrice := tx.gasPrice
    nonce := tx.nonce
    secretKey := tx.secretKey
    sender := tx.sender
    receiver := tx.receiver
    value := vl
    hash := p.hash
    logs := p.logs
  }

def getTests (t : TestFile) : IO (List Test) := do
  have ps := t.post.snd
  mapM (getTest t.pre t.tx) ps

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

def PreAcct.toKV (a : PreAcct) : Nibs × Bytes :=
  ⟨
    @Bits.toNibs 64 (@Bits.toBytes 20 a.addr).keccak,
    RLP.encode <| .list [
      .bytes a.nonce,
      .bytes a.bal,
      Word.toRLP (trie a.stor.toNTB),
      Word.toRLP <| Bytes.keccak a.code
    ]
  ⟩

def testStor : Stor :=
  Lean.RBMap.singleton 0
    ((Hex.toWord "fffffffffffffffffffffffffffffffffffffffffffffffffedcba9876543210").getD 0)

def testPreAcct1 : PreAcct :=
  {
    addr := (Hex.toBits 40 "0000000000000000000000000000000000001000").getD 0
    nonce := []
    bal := (Hex.toBytes "0ba1a9ce0ba1a9ce").getD []
    stor := testStor
    code := (Hex.toBytes "670123456789abcdef1960005500").getD []
  }

def testPreAcct2 : PreAcct :=
  {
    addr := (Hex.toBits 40 "a94f5374fce5edbc8e2a8697c15331677e6ebf0b").getD 0
    nonce := [Ox x0 x1]
    bal := (Hex.toBytes "0ba1a9ce0b9aa79f").getD []
    stor := .empty
    code := []
  }

def testPreAcct3 : PreAcct :=
  {
    addr := (Hex.toBits 40 "cccccccccccccccccccccccccccccccccccccccc").getD 0
    nonce := []
    bal := (Hex.toBytes "0ba1a9ce0ba1a9cf").getD []
    stor := .empty
    code := (Hex.toBytes "600060006000600060006004356110000162fffffff100").getD []
  }

def testPreAccts : List PreAcct := [testPreAcct1, testPreAcct2, testPreAcct3]

def testNTB : NTB := Lean.RBMap.fromList (List.map PreAcct.toKV testPreAccts) compare

-- def main : IO Unit := do IO.println <| Bits.toHex 64 (trie testNTB)

-- def main : IO Unit := do
--   let t ← readJsonFile "not.json" >>= Lean.Json.toTestFile
--   IO.println t.toString

def callData : Bytes :=
  (Hex.toBytes "693c6139").getD []

def dataGas (cd : Bytes) : Nat :=
  let aux : Byte → Nat := fun b => if b = 0 then 4 else 16
  (cd.map aux).sum

def G_initcodeword : Nat := 2

def initCodeCost (cd : Bytes) : Nat :=
  G_initcodeword * ((cd.length / 32) + if 32 ∣ cd.length then 0 else 1)

def G_txcreate : Nat := 32000
def G_accesslistaddress : Nat := 2400
def G_accessliststorage : Nat := 1900

def intrinsicGas (Tt : Bytes) (cd : Bytes) (Ta : List (Addr × List Word)) : Nat :=
  let aux : (Addr × List Word) → Nat :=
    fun | ⟨_, l⟩ => G_accesslistaddress + (G_accessliststorage * l.length)
  dataGas cd +
  (if Tt = [] then G_txcreate + initCodeCost cd else 0) +
  2100 +
  (Ta.map aux).sum

def Tg : Nat := ((Hex.toBytes "04C4B400").getD []).toNat

def g : Nat := Tg - intrinsicGas ((Hex.toBytes "cccccccccccccccccccccccccccccccccccccccc").getD []) callData []

def C : Nat := _ + _

def g' : Nat := g - C

structure Acct where
  (nonce : Word)
  (bal : Word)
  (stor : Stor)
  (code : Bytes)

abbrev World' : Type := Lean.RBMap Addr Acct compare

structure State' where
  (w : World')
  (cta : Addr)
  (pc : Nat)

def testWorld : World' :=
  let aux : PreAcct → (Addr × Acct) :=
    fun pa => ⟨pa.addr, ⟨pa.nonce.toBits 32, pa.bal.toBits 32, pa.stor, pa.code⟩⟩
  Lean.RBMap.fromList (testPreAccts.map aux) _

def testState : State' :=
  {
    w := testWorld
    cta := (Hex.toBits 40 "cccccccccccccccccccccccccccccccccccccccc").getD 0
    pc := 0
  }

def State'.inst (s : State') : IO (Inst ⊕ Hinst) := do
  let a ← (s.w.find? s.cta).toIO "contract does not exist in state"
  match a.code.get? s.pc with
  | none =>
    if a.code.length = s.pc
    then return (.inr .stop)
    else .throw "unreachable code : out-of-bound instruction lookup inconsistent with normal usage"
  | some b => _

#exit

def State'.gas (s : State') : IO Nat := do
  let a ← (s.w.find? s.cta).toIO "cannot get acct"
  let c ← (a.code.get? s.pc).toIO "cannot"

  _


#exit


def Bits.min {n} : Bits n → Bits n → Bits n
  | xs, ys => if xs ≤ ys then xs else ys

instance {n} : Min (Bits n) := ⟨.min⟩

def A_r : Word := 0 -- SSTORE used only once, cannot change from 0

def gstar : Word := g' + min ((Tg - gprime) / 5) A_r

def balInit : Word := Bytes.toWord ((Hex.toBytes "0ba1a9ce0ba1a9ce").getD [])

def txVal : Word := 1

def Yg : Word := Tg - gstar

def gasPrice : Word := 10--Bytes.toWord ((Hex.toBytes "0a").getD [])

def balFinal : Word := balInit - ((Yg * gasPrice) + txVal)


#exit


def main : IO Unit := do
  let bs := notTxBytes
  let (RLP.list [nonce, gasPrice, gasLimit, toAddr, val, calldata, .bytes [v], .bytes r, .bytes s])
    ← (Option.toIO <| RLP.decode bs)
    | throw (IO.Error.userError "Error : RLP decoding failed")
  let bs' := RLP.encode <| .list [txType, nonce, gasPrice, toAddr, val, calldata]
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
