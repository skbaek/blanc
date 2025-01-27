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

def Hexit.toB4 : Char → Option B8
  | '0' => some 0x00
  | '1' => some 0x01
  | '2' => some 0x02
  | '3' => some 0x03
  | '4' => some 0x04
  | '5' => some 0x05
  | '6' => some 0x06
  | '7' => some 0x07
  | '8' => some 0x08
  | '9' => some 0x09
  | 'a' => some 0x0A
  | 'b' => some 0x0B
  | 'c' => some 0x0C
  | 'd' => some 0x0D
  | 'e' => some 0x0E
  | 'f' => some 0x0F
  | 'A' => some 0x0A
  | 'B' => some 0x0B
  | 'C' => some 0x0C
  | 'D' => some 0x0D
  | 'E' => some 0x0E
  | 'F' => some 0x0F
  |  _  => none

def B4L.toB8L : B8L → Option B8L
  | [] => some []
  | [_] => none
  | x :: y :: xs =>
    let xy := (x <<< 4) ||| y
    (xy :: ·) <$> B4L.toB8L xs

def Hex.toB8L (s : String) : Option B8L :=
  s.data.mapM Hexit.toB4 >>= B4L.toB8L

def Option.toIO {ξ} (o : Option ξ) (msg : String) : IO ξ := do
  match o with
  | none => throw (IO.Error.userError msg)
  | some x => pure x

@[extern "ecrecover_flag"]
opaque ecrecoverFlag : ByteArray → UInt8 → ByteArray → ByteArray

def Bool.toByte : Bool → Byte
  | true => Ox x0 x1
  | false => Ox x0 x0

structure Adr : Type where
  (high : B32)
  (mid : B64)
  (low : B64)

def Adr.toHex (a : Adr) : String :=
  a.high.toHex ++ a.mid.toHex ++ a.low.toHex

def B8L.toAdr : B8L → Option Adr
  | x0 :: x1 :: x2 :: x3 ::
    y0 :: y1 :: y2 :: y3 ::
    y4 :: y5 :: y6 :: y7 ::
    z0 :: z1 :: z2 :: z3 ::
    z4 :: z5 :: z6 :: z7 :: _ =>
    some ⟨
      B8s.toB32 x0 x1 x2 x3,
      B8s.toB64 y0 y1 y2 y3 y4 y5 y6 y7,
      B8s.toB64 z0 z1 z2 z3 z4 z5 z6 z7,
    ⟩
  | _ => none

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

def Adr.ordering : Adr → Adr → Ordering
  | ⟨xh, xm, xl⟩, ⟨yh, ym, yl⟩ =>
    match compare xh yh with
    | .eq =>
      match compare xm ym with
      | .eq => compare xl yl
      | o => o
    | o => o

instance : Ord Adr := ⟨Adr.ordering⟩

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

abbrev NTB := Lean.RBMap (List B8) (List B8) (@List.compare _ ⟨B8.compareLows⟩)

abbrev Stor := Lean.RBMap B256 B256 compare

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

structure Acct where
  (nonce : B256)
  (bal : B256)
  (stor : Stor)
  (code : ByteArray)

abbrev Wor : Type := Lean.RBMap Adr Acct compare

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

def Stor.toStrings (s : Stor) : List String :=
  let kvs := s.toArray.toList
  let kvToStrings : B256 × B256 → List String :=
    λ nb => [s!"{B256.toHex nb.fst} : {B256.toHex nb.snd}"]
  fork "stor" (kvs.map kvToStrings)

def Acct.toStrings (s : String) (a : Acct) : List String :=
  fork s [
    [s!"nonce : 0x{a.nonce.toHex}"],
    [s!"bal : 0x{a.bal.toHex}"],
    a.stor.toStrings,
    longB8LToStrings "code" a.code.toList
  ]

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

def Wor.toStrings (w : Wor) : List String :=
  let kvs := w.toArray.toList
  let kvToStrings : Adr × Acct → List String :=
    fun x => Acct.toStrings x.fst.toHex x.snd
  fork "world" (kvs.map kvToStrings)

def B4L.toHex : B8L → String
  | [] => ""
  | [b] => ⟨[b.toHexit]⟩
  | b :: bs => ⟨[b.toHexit] ++ (toHex bs).data⟩

def NTB.toStrings (s : NTB) : List String :=
  let kvs := s.toArray.toList
  let kvToStrings : B8L × B8L → List String :=
    λ nb => [s!"{B4L.toHex (nb.fst.map B8.lows)} : {nb.snd.toHex}"]
  fork "NTB" (kvs.map kvToStrings)

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

def B8s.toB128
  (x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 : B8) : B128 :=
  ⟨ B8s.toB64 x0 x1 x2 x3 x4 x5 x6 x7,
    B8s.toB64 y0 y1 y2 y3 y4 y5 y6 y7 ⟩

def B8s.toB256
  ( x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 xA xB xC xD xE xF
    y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 yA yB yC yD yE yF : B8 ) : B256 :=
  ⟨ B8s.toB128 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 xA xB xC xD xE xF,
    B8s.toB128 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 yA yB yC yD yE yF ⟩

def B8L.toB128Diff : B8L → Option (B128 × B8L)
  | x0 :: x1 :: x2 :: x3 ::
    x4 :: x5 :: x6 :: x7 ::
    y0 :: y1 :: y2 :: y3 ::
    y4 :: y5 :: y6 :: y7 :: xs =>
    some ⟨
        ⟨ B8s.toB64 x0 x1 x2 x3 x4 x5 x6 x7,
          B8s.toB64 y0 y1 y2 y3 y4 y5 y6 y7 ⟩,
        xs
      ⟩
  | _ => none

def List.ekatD {ξ : Type u} (n : Nat) (xs : List ξ) (x : ξ) : List ξ :=
  (xs.reverse.takeD n x).reverse

lemma List.length_ekatD {ξ : Type u} (n : Nat) (xs : List ξ) (x : ξ) :
    (List.ekatD n xs x).length = n := by
  apply Eq.trans (List.length_reverse _)
  apply Eq.trans (List.takeD_length _ _ _) rfl

def B8L.toB256? (xs : B8L) : Option B256 := do
  let ⟨h, xs'⟩ ← xs.toB128Diff
  let ⟨l, []⟩ ← xs'.toB128Diff | none
  some ⟨h, l⟩

def Hex.toB256? (hx : String) : Option B256 := do
  Hex.toB8L hx >>= B8L.toB256?

def B8V.toB128 : Vec B8 16 → B128
  | ⟨ [ b0, b1, b2, b3, b4, b5, b6, b7,
        b8, b9, bA, bB, bC, bD, bE, bF ], _ ⟩ =>
    ⟨ B8s.toB64 b0 b1 b2 b3 b4 b5 b6 b7,
      B8s.toB64 b8 b9 bA bB bC bD bE bF ⟩

def B8V.toB256 (xs : Vec B8 32) : B256 :=
  let h : Vec B8 16 := xs.take 16
  let l : Vec B8 16 := xs.drop 16
  ⟨B8V.toB128 h, B8V.toB128 l⟩

def B8L.pack (xs : B8L) (n : Nat) : B8L := List.ekatD n xs 0

def B8L.toB8V (xs : B8L) (n : Nat) : Vec B8 n :=
  ⟨xs.pack n, List.length_ekatD _ _ _⟩

def B8L.toB256P (xs : B8L) : B256 := B8V.toB256 (xs.toB8V 32)

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

def Hex.toAdr (hx : String) : Option Adr := Hex.toB8L hx >>= B8L.toAdr

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
  def nodeComp : Nat → NTB → RLP'
    | 0, _ => .b8s []
    | k + 1, j =>
      if j.isEmpty
      then .b8s []
      else let r := structComp k j
           if r.encode.length < 32
           then r
           else .b8s <| r.encode.keccak.toB8L

  def structComp : Nat → NTB → RLP'
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

def collapse (j : NTB) : RLP' := structComp (2 * (j.maxKeyLength + 1)) j

def trie (j : NTB) : B256 :=
  let bs := (collapse j).encode
  bs.keccak

def B256.toRLP (w : B256) : RLP' := .b8s w.toB8L
def B16.toB8L (x : B16) : List B8 := [x.highs, x.lows]
def B32.toB8L (x : B32) : List B8 := x.highs.toB8L ++ x.lows.toB8L
def B8.toB4s (x : B8) : List B8 := [x.highs, x.lows]
def B16.toB4s (x : B16) : List B8 := x.highs.toB4s ++ x.lows.toB4s
def B32.toB4s (x : B32) : List B8 := x.highs.toB4s ++ x.lows.toB4s
def B64.toB4s (x : B64) : List B8 := x.highs.toB4s ++ x.lows.toB4s
def B128.toB4s (x : B128) : List B8 := x.1.toB4s ++ x.2.toB4s
def B256.toB4s (x : B256) : List B8 := x.1.toB4s ++ x.2.toB4s
def B256.keccak (x : B256) : B256 := B8L.keccak <| x.toB8L

def B8L.sig (bs : B8L) : B8L := List.dropWhile (· = 0) bs

def Stor.toNTB (s : Stor) : NTB :=
  let f : NTB → B256 → B256 → NTB :=
    λ j k v =>
      j.insert
        k.keccak.toB4s
        ((RLP'.encode <| .b8s <| B8L.sig <| v.toB8L))
  Lean.RBMap.fold f NTB.empty s

def B256.zerocount (x : B256) : Nat → Nat
  | 0 => 0
  | k + 1 => if x = 0 then k + 1 else B256.zerocount (x >>> 8) k

def B256.bytecount (x : B256) : Nat := 32 - (B256.zerocount x 32)

def Acct.toVal (a : Acct) (w : B256) : B8L :=
  RLP'.encode <| .list [
    .b8s a.nonce.toB8L.sig,
    .b8s a.bal.toB8L.sig,
    B256.toRLP w,
    B256.toRLP <| B8L.keccak (a.code.toList)
  ]

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

def Adr.toB8L (a : Adr) : B8L :=
  a.high.toB8L ++ a.mid.toB8L ++ a.low.toB8L

def toKeyVal (pr : Adr × Acct) : B8L × B8L :=
  let ad := pr.fst
  let ac := pr.snd
  ⟨
    let key' := ad.toB8L.keccak.toB4s
    key',
    let val' :=
      RLP'.encode <| .list [
        .b8s (ac.nonce.toB8L.sig), --a.nonce,
        .b8s (ac.bal.toB8L.sig), --a.bal,
        B256.toRLP (trie ac.stor.toNTB),
        B256.toRLP <| (B8L.keccak ac.code.toList)
      ]
    val'
  ⟩

-- values --

def G_txcreate : Nat := 32000
def G_accesslistaddress : Nat := 2400
def G_accessliststorage : Nat := 1900
def G_initcodeword : Nat := 2

def initCodeCost (cd : B8L) : Nat :=
  G_initcodeword * ((cd.length / 32) + if 32 ∣ cd.length then 0 else 1)

instance {a b : Adr} : Decidable (a = b) := by
  cases a; cases b; simp; apply instDecidableAnd

instance : Hashable Adr := ⟨Adr.low⟩
instance : Hashable (Adr × B256) := ⟨λ x => x.1.low⟩

abbrev AdrSet : Type := @Std.HashSet Adr _ _
abbrev KeySet : Type := @Std.HashSet (Adr × B256) _ _

def Sta : Type := Array B256 × Nat
def Mem : Type := Array B8

structure Acs where
  (dest : List Adr)  -- A_s
  (adrs : AdrSet)    -- A_a
  (keys : KeySet)     -- A_k
  (ref : Nat)         -- A_r
  (logs : List RLP')  -- A_l
  (tchd : AdrSet) -- A_t

structure Var where
  (gas : Nat) -- μ_g
  (pc : Nat)  -- μ_pc
  (ret : B8L) -- μ_o
  (act : Nat) -- μ_i
  -------------------------
  (dest : List Adr)  -- A_s
  (adrs : AdrSet)    -- A_a
  (keys : KeySet)     -- A_k
  (ref : Nat)         -- A_r
  (logs : List RLP')  -- A_l
  (tchd : AdrSet) -- A_t

def Var.toAcs (υ : Var) : Acs :=
  {
    dest := υ.dest
    adrs := υ.adrs
    keys := υ.keys
    ref := υ.ref
    logs := υ.logs
    tchd := υ.tchd
  }

def ceilDiv (m n : Nat) := m / n + if m % n = 0 then 0 else 1

-- μ_i : no need to make it a separate field of Machine,
-- when it is completely determined by Machine.mem
def Mem.msz (μ : Mem) : Nat := ceilDiv μ.size 32

structure Block where
  (baseFee : B256) -- H_f
  (ben : Adr) -- H_c
  (prevRandao : B256) -- H_a
  (gasLimit : B256) -- H_l
  (timestamp : B256) -- H_s
  (number : B256) -- H_s
  (chainId : B256) -- β

structure Con where
  (cta : Adr) -- contract address (YP : a)
  (oga : Adr) -- origin address (YP : o)
  (gpr : B256) -- gas price (YP : p)
  (cld : B8L) -- calldata (YP : d)
  (cla : Adr) -- caller Addr (YP : s)
  (clv : B256) -- callvalue (YP : v)
  (code : ByteArray) -- contract code  (YP : b)
  (blk : Block) -- block (YP : H)
  (exd : Nat) -- execution depth (YP : e)
  (wup : Bool) -- World-State update permission (YP : w)

-- YP says that this type should also have a field for
-- execution environment, but it was omitted since the
-- environment does not change and is already known.
structure Ξ.Result where
  (wor : Option Wor)
  (gas : Nat)
  (acs : Acs)
  (ret : Option B8L)

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

def Jinst.toString : Jinst → String
  | .jump => "JUMP"
  | .jumpdest => "JUMPDEST"
  | .jumpi => "JUMPI"

def Inst.toString : Inst → String
  | .next n => n.toString
  | .jump j => j.toString
  | .last l => l.toString

def noPushBefore' (cd : ByteArray) : Nat → Nat → Bool
  | 0, _ => true
  | _, 0 => true
  | k + 1, m + 1 =>
    if k < cd.size
    then let b := cd.get! k
         if (b < (0x7F - m.toUInt8) || 0x7F < b)
         then noPushBefore' cd k m
         else if noPushBefore' cd k 32
              then false
              else noPushBefore' cd k m
    else noPushBefore' cd k m

def noPushBefore (cd : Array B8) : Nat → Nat → Bool
  | 0, _ => true
  | _, 0 => true
  | k + 1, m + 1 =>
    match cd.get? k with
    | none => noPushBefore cd k m
    | some b =>
      if (b < (0x7F - m.toUInt8) || 0x7F < b)
      then noPushBefore cd k m
      else if noPushBefore cd k 32
           then false
           else noPushBefore cd k m

def Jinst.toB8 : Jinst → B8
  | jump => 0x56     -- 0x56 / 1 / 0 / Unconditional jump.
  | jumpi => 0x57    -- 0x57 / 2 / 0 / Conditional jump.
  | jumpdest => 0x5B -- 0x5b / 0 / 0 / Mark a valid jump destination.

def jumpable' (cd : ByteArray) (k : Nat) : Bool :=
  if cd.get! k = (Jinst.toB8 .jumpdest)
  then noPushBefore' cd k 32
  else false

def jumpable (cd : Array B8) (k : Nat) : Bool :=
  if cd.get? k = some (Jinst.toB8 .jumpdest)
  then noPushBefore cd k 32
  else false

def ByteArray.sliceD (xs : ByteArray) : Nat → Nat → B8 → B8L
  | _, 0, _ => []
  | m, n + 1, d => --xs.getD m d :: Array.sliceD xs (m + 1) n d
    if m < xs.size
    then xs.get! m :: ByteArray.sliceD xs (m + 1) n d
    else List.replicate (n + 1) d

lemma ByteArray.length_sliceD {xs : ByteArray} {m n x} :
    (ByteArray.sliceD xs m n x).length = n := by
  induction n generalizing m with
  | zero => simp [sliceD]
  | succ n ih =>
    simp [sliceD]
    by_cases h : m < xs.size
    · rw [if_pos h]; simp [List.length]; apply ih
    · rw [if_neg h]; apply List.length_replicate

def Array.sliceD {ξ : Type u} (xs : Array ξ) : Nat → Nat → ξ → List ξ
  | _, 0, _ => []
  | m, n + 1, d => xs.getD m d :: Array.sliceD xs (m + 1) n d

lemma Array.length_sliceD {ξ} {xs : Array ξ} {m n x} :
    (Array.sliceD xs m n x).length = n := by
  induction n generalizing m with
  | zero => simp [sliceD]
  | succ n ih => simp [sliceD, List.length, ih]

def B8.toRinst : B8 → Option Rinst
  | 0x01 => some .add -- 0x01 / 2 / 1 / addition operation.
  | 0x02 => some .mul -- 0x02 / 2 / 1 / multiplication operation.
  | 0x03 => some .sub -- 0x03 / 2 / 1 / subtraction operation.
  | 0x04 => some .div -- 0x04 / 2 / 1 / integer division operation.
  | 0x05 => some .sdiv -- 0x05 / 2 / 1 / signed integer division operation.
  | 0x06 => some .mod -- 0x06 / 2 / 1 / modulo operation.
  | 0x07 => some .smod -- 0x07 / 2 / 1 / signed modulo operation.
  | 0x08 => some .addmod -- 0x08 / 3 / 1 / modulo addition operation.
  | 0x09 => some .mulmod -- 0x09 / 3 / 1 / modulo multiplication operation.
  | 0x0a => some .exp -- 0x0a / 2 / 1 / exponentiation operation.
  | 0x0b => some .signextend -- 0x0b / 2 / 1 / sign extend operation.
  | 0x10 => some .lt -- 0x10 / 2 / 1 / less-than comparison.
  | 0x11 => some .gt -- 0x11 / 2 / 1 / greater-than comparison.
  | 0x12 => some .slt -- 0x12 / 2 / 1 / signed less-than comparison.
  | 0x13 => some .sgt -- 0x13 / 2 / 1 / signed greater-than comparison.
  | 0x14 => some .eq -- 0x14 / 2 / 1 / equality comparison.
  | 0x15 => some .iszero -- 0x15 / 1 / 1 / tests if the input is zero.
  | 0x16 => some .and -- 0x16 / 2 / 1 / bitwise and operation.
  | 0x17 => some .or -- 0x17 / 2 / 1 / bitwise or operation.
  | 0x18 => some .xor -- 0x18 / 2 / 1 / bitwise xor operation.
  | 0x19 => some .not -- 0x19 / 1 / 1 / bitwise not operation.
  | 0x1a => some .byte -- 0x1a / 2 / 1 / retrieve a single byte from a word.
  | 0x1b => some .shl -- 0x1b / 2 / 1 / logical shift right operation.
  | 0x1c => some .shr -- 0x1c / 2 / 1 / logical shift left operation.
  | 0x1d => some .sar -- 0x1d / 2 / 1 / arithmetic (signed) shift right operation.
  | 0x20 => some .kec -- 0x20 / 2 / 1 / compute Keccak-256 hash.
  | 0x30 => some .address -- 0x30 / 0 / 1 / Get the address of the currently executing account.
  | 0x31 => some .balance -- 0x31 / 1 / 1 / Get the balance of the specified account.
  | 0x32 => some .origin -- 0x32 / 0 / 1 / Get the address that initiated the current transaction.
  | 0x33 => some .caller -- 0x33 / 0 / 1 / Get the address that directly called the currently executing contract.
  | 0x34 => some .callvalue -- 0x34 / 0 / 1 / Get the value (in wei) sent with the current transaction.
  | 0x35 => some .calldataload -- 0x35 / 1 / 1 / Load input data from the current transaction.
  | 0x36 => some .calldatasize -- 0x36 / 0 / 1 / Get the size of the input data from the current transaction.
  | 0x37 => some .calldatacopy -- 0x37 / 3 / 0 / Copy input data from the current transaction to memory.
  | 0x38 => some .codesize -- 0x38 / 0 / 1 / Get the size of the code of the currently executing contract.
  | 0x39 => some .codecopy -- 0x39 / 3 / 0 / Copy the code of the currently executing contract to memory.
  | 0x3a => some .gasprice -- 0x3a / 0 / 1 / Get the gas price of the current transaction.
  | 0x3b => some .extcodesize -- 0x3b / 1 / 1 / Get the size of the code of an external account.
  | 0x3c => some .extcodecopy -- 0x3c / 4 / 0 / Copy the code of an external account to memory.
  | 0x3d => some .retdatasize -- 0x3d / 0 / 1 / Get the size of the output data from the previous call.
  | 0x3e => some .retdatacopy -- 0x3e / 3 / 0 / Copy output data from the previous call to memory.
  | 0x3f => some .extcodehash -- 0x3f / 1 / 1 / Get the code hash of an external account.
  | 0x40 => some .blockhash -- 0x40 / 1 / 1 / get the hash of the specified block.
  | 0x41 => some .coinbase -- 0x41 / 0 / 1 / get the address of the current block's miner.
  | 0x42 => some .timestamp -- 0x42 / 0 / 1 / get the timestamp of the current block.
  | 0x43 => some .number -- 0x43 / 0 / 1 / get the current block number.
  | 0x44 => some .prevrandao -- 0x44 / 0 / 1 / get the difficulty of the current block.
  | 0x45 => some .gaslimit -- 0x45 / 0 / 1 / get the gas limit of the current block.
  | 0x46 => some .chainid -- 0x46 / 0 / 1 / get the chain id of the current blockchain.
  | 0x47 => some .selfbalance -- 0x46 / 0 / 1 / get the chain id of the current blockchain.
  | 0x48 => some .basefee -- 0x46 / 0 / 1 / get the chain id of the current blockchain.
  | 0x50 => some .pop -- 0x50 / 1 / 0 / Remove an item from the stack.
  | 0x51 => some .mload -- 0x51 / 1 / 1 / Load a word from memory.
  | 0x52 => some .mstore -- 0x52 / 2 / 0 / Store a word in memory.
  | 0x53 => some .mstore8 -- 0x53 / 2 / 0 / Store a byte in memory.
  | 0x54 => some .sload -- 0x54 / 1 / 1 / Load a word from storage.
  | 0x55 => some .sstore -- 0x55 / 2 / 0 / Store a word in storage.
  | 0x58 => some .pc -- 0x58 / 0 / 1 / Get the current program counter value.
  | 0x59 => some .msize -- 0x59 / 0 / 1 / Get the size of the memory.
  | 0x5a => some .gas -- 0x5a / 0 / 1 / Get the amount of remaining gas.
  | 0x80 => some (.dup 0)
  | 0x81 => some (.dup 1)
  | 0x82 => some (.dup 2)
  | 0x83 => some (.dup 3)
  | 0x84 => some (.dup 4)
  | 0x85 => some (.dup 5)
  | 0x86 => some (.dup 6)
  | 0x87 => some (.dup 7)
  | 0x88 => some (.dup 8)
  | 0x89 => some (.dup 9)
  | 0x8A => some (.dup 10)
  | 0x8B => some (.dup 11)
  | 0x8C => some (.dup 12)
  | 0x8D => some (.dup 13)
  | 0x8E => some (.dup 14)
  | 0x8F => some (.dup 15)
  | 0x90 => some (.swap 0)
  | 0x91 => some (.swap 1)
  | 0x92 => some (.swap 2)
  | 0x93 => some (.swap 3)
  | 0x94 => some (.swap 4)
  | 0x95 => some (.swap 5)
  | 0x96 => some (.swap 6)
  | 0x97 => some (.swap 7)
  | 0x98 => some (.swap 8)
  | 0x99 => some (.swap 9)
  | 0x9A => some (.swap 10)
  | 0x9B => some (.swap 11)
  | 0x9C => some (.swap 12)
  | 0x9D => some (.swap 13)
  | 0x9E => some (.swap 14)
  | 0x9F => some (.swap 15)
  | 0xA0 => some (.log 0)
  | 0xA1 => some (.log 1)
  | 0xA2 => some (.log 2)
  | 0xA3 => some (.log 3)
  | 0xA4 => some (.log 4)
  | _ => none

def B8.toXinst : B8 → Option Xinst
  | 0xF0 => some .create
  | 0xF1 => some .call
  | 0xF2 => some .callcode
  | 0xF4 => some .delcall
  | 0xF5 => some .create2
  | 0xFA => some .statcall
  | _    => none

def B8.toJinst : B8 → Option Jinst
  | 0x56 => some .jump
  | 0x57 => some .jumpi
  | 0x5B => some .jumpdest
  | _    => none

def B8.toLinst : B8 → Option Linst
  | 0x00 => some .stop
  | 0xF3 => some .ret
  | 0xFD => some .rev
  | 0xFF => some .dest
  | 0xFE => some .invalid
  | _ => none

inductive Ninst' : Type
  | reg : Rinst → Ninst'
  | exec : Xinst → Ninst'
  | push : B256 → Nat →  Ninst' --∀ bs : B8L, bs.length ≤ 32 → Ninst'

inductive Inst' : Type
  | last : Linst → Inst'
  | next : Ninst' → Inst'
  | jump : Jinst → Inst'

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
      else none
    )
  else some (.last .stop)

-- def getInst (υ : Var) (κ : Con)  : Option Inst' :=
--   match κ.code.get? υ.pc with
--   | none => some (.last .stop)
--   | some b =>
--     (b.toRinst <&> (.next ∘ .reg)) <|>
--     (b.toXinst <&> (.next ∘ .exec)) <|>
--     (b.toJinst <&> .jump) <|>
--     (b.toLinst <&> .last) <|>
--     ( if h : 95 ≤ b.toNat ∧ b.toNat ≤ 127
--       then let len := b.toNat - 95
--            let slc := κ.code.sliceD (υ.pc + 1) len 0
--            let h_slc : slc.length ≤ 32 := by
--              simp [len, slc, Array.length_sliceD, h.right]
--            some (.next <| .push slc h_slc)
--       else none )
--
def g_zero : Nat := 0
def gVerylow : Nat := 3
def gLow : Nat := 5
def g_mid : Nat := 8
def g_exp : Nat := 10
def g_expbyte : Nat := 50

def safeSub {ξ} [Sub ξ] [LE ξ] [@DecidableRel ξ (· ≤ ·)] (x y : ξ) : Option ξ :=
  if y ≤ x then some (x - y) else none

def deductGas (υ : Var) (c : Nat) : Option Nat := safeSub υ.gas c

def Acct.Empty (a : Acct) : Prop :=
  a.code.size = 0 ∧ a.nonce = 0 ∧ a.bal = 0

def Dead (w : Wor) (a : Adr) : Prop :=
  match w.find? a with
  | none => True
  | some x => x.Empty

def Wor.balAt (w : Wor) (a : Adr) : B256 :=
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

def cAAccess (x : Adr) (a : AdrSet) : Nat :=
  if x ∈ a then gWarmAccess else gColdAccountAccess

def except64th (n : Nat) : Nat := n - (n / 64)

def cExtra (ω : Wor) (υ : Var) (t : Adr) (v : B256) : Nat :=
  let cAcc : Nat := cAAccess t υ.adrs
  let cNew : Nat := if (Dead ω t ∧ v ≠ 0) then gNewAccount else 0
  let cXfer : Nat := if v ≠ 0 then gCallValue else 0
  (cAcc + cXfer + cNew)

def cGasCap (ω : Wor) (υ : Var) (g : Nat)
    (memCost : Nat) (t : Adr) (v : B256) : Nat :=
  if (memCost + cExtra ω υ t v) ≤ υ.gas
  then min (except64th (υ.gas - (memCost + cExtra ω υ t v))) g
  else g

def cCallGas (ω : Wor) (υ : Var)
   (g : Nat) (memCost : Nat) (t : Adr) (v : B256) : Nat :=
  if v ≠ 0
  then cGasCap ω υ g memCost t v + gCallStipend
  else cGasCap ω υ g memCost t v

def cCall (ω : Wor) (υ : Var)
    (g : Nat) (memCost : Nat) (t : Adr) (v : B256) : Nat :=
  cGasCap ω υ g memCost t v + cExtra ω υ t v

structure theta.Result : Type where
  (wor : Wor)
  (gas : Nat)
  (acs : Acs)
  (status : Bool)
  (ret : B8L)

def Wor.code (w : Wor) (a : Adr) : ByteArray :=
  match w.find? a with
  | none => ByteArray.mk #[]
  | some x => x.code

def Acct.empty : Acct :=
  {
    nonce := 0
    bal := 0
    stor := .empty
    code := ByteArray.mk #[]
  }

def Sta.init : Sta := ⟨Array.mkArray 1024 (0 : B256), 0⟩

-- need further update for precompiled contracts
def θ.prep
  (H : Block)
  (ω : Wor)
  (A : Acs)
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
  Wor × Sta × Mem × Var × Con :=
  let ω'₁ : Wor :=
    match ω.find? r with
    | none =>
      if v = 0
      then ω
      else ω.insert r {nonce := 0, bal := v, stor := .empty, code := ByteArray.mk #[]}
    | some aᵣ => ω.insert r {aᵣ with bal := aᵣ.bal + v}
  let ω₁ : Wor :=
    match ω'₁.find? s with
    | none =>
      if v = 0
      then ω'₁
      else (dbg_trace "unreachable code : nonzero value calls from empty accounts should never happen" ; ω'₁)
    | some aₛ => ω'₁.insert s {aₛ with bal := aₛ.bal - v}
  let cd : ByteArray := ω.code c
  let κ : Con := {
    cta := r, oga := o, gpr := p.toB256, cld := d
    cla := s, clv := v_app, code := cd, blk := H, exd := e, wup := w
  }
  let υ : Var := {
    gas := g, pc := 0, ret := [], act := 0
    dest := A.dest, adrs := A.adrs, keys := A.keys,
    ref := A.ref, logs := A.logs, tchd := A.tchd
  }
  ⟨ω₁, .init, #[], υ, κ⟩

def θ.wrap (wor : Wor) (acs : Acs) (Ξr : Ξ.Result) : theta.Result :=
  let ω_stars : Option Wor := Ξr.wor
  let g_stars : Nat := Ξr.gas
  let A_stars : Acs := Ξr.acs
  let o : Option B8L := Ξr.ret
  let ω' : Wor := ω_stars.getD wor
  let g' : Nat :=
    if ω_stars.isNone ∧ o.isNone
    then (dbg_trace "EXCEPTIONAL HALTING STATE"; 0)
    else g_stars
  let A' : Acs := if ω_stars.isNone then acs else A_stars
  let z : Bool := if ω_stars.isNone then 0 else 1

  -- o' is not from YP, but necessary to cast from 'Option B8L to 'B8L'
  -- (YP is a bit sloppy with types here)
  let o' : B8L := o.getD []
  ⟨ω', g', A', z, o'⟩

def gColdSLoad : Nat := 2100
def gSSet : Nat := 20000
def gSReset : Nat := 2900
def rSClear : Nat := 4800


def B256.min : B256 → B256 → B256
  | xs, ys => if xs ≤ ys then xs else ys
instance : Min B256 := ⟨.min⟩

def dataGas (cd : B8L) : Nat :=
  let aux : B8 → Nat := fun b => if b = 0 then 4 else 16
  (cd.map aux).sum

def gTransaction : Nat := 21000

def intrinsicGas (Rcv : Option Adr) (cd : B8L) (Ta : List (Adr × List B256)) : Nat :=
  let aux : (Adr × List B256) → Nat :=
    fun | ⟨_, l⟩ => G_accesslistaddress + (G_accessliststorage * l.length)
  dataGas cd +
  Rcv.rec (G_txcreate + initCodeCost cd) (fun _ => 0) +
  gTransaction +
  (Ta.map aux).sum

def Wor.transfer? (wor : Wor) (src : Adr) (clv : B256) (dst : Adr) : Option Wor := do
  let src_acct ← wor.find? src
  let dst_acct ← wor.find? dst
  let new_src_bal ← safeSub src_acct.bal clv
  let wor' := wor.insert src {src_acct with bal := new_src_bal}
  return wor'.insert dst {dst_acct with bal := dst_acct.bal + clv}

-- checkpoint is an 'Option' type because computation of checkpoints
-- may fail for invalid txs. this is *not* the case for any subsequent
-- steps of a tx: once you get to a checkpoint, the tx *always* goes
-- through and yields a new state. i.e., there is no invalid tx that
-- has a checkpoint.
def checkpoint (w : Wor) (ad : Adr) (v : B256) : Option Wor := do
  let ac ← w.find? ad
  let bal' ← safeSub ac.bal v
  some <| w.insert ad {ac with bal := bal', nonce := ac.nonce + 1}

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

-- A^0
def Acs.init : Acs :=
  {
    dest := []
    adrs := .ofList [1, 2, 3, 4, 5, 6, 7, 8, 9] -- precompiled contracts
    keys := .empty
    ref := 0
    logs := []
    tchd := .empty
  }

abbrev AccessList : Type := List (Adr × List B256)

abbrev AccessList.collect (al : AccessList) : KeySet :=
  let addPair : Adr → KeySet → B256 → KeySet :=
    fun a aks k => aks.insert ⟨a, k⟩
  let addElem : KeySet → Adr × List B256 → KeySet :=
    fun aks pr => List.foldl (addPair pr.fst) aks pr.snd
  List.foldl addElem .empty al

def A_star (H : Block) (ST : Adr) (Tt : Option Adr) (TA : AccessList) : Acs :=
  let a : AdrSet :=
    Acs.init.adrs.insertMany
      (Std.HashSet.ofList (ST :: H.ben :: TA.map Prod.fst))
  {
    Acs.init with
    adrs := Tt.rec a (a.insert)
    keys := TA.collect
  }

def Stor.insertNonzero (s : Stor) (k v : B256) : Stor :=
  if v = 0 then s.erase k else s.insert k v

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

def Sta.popN (s : Sta ) : Nat → Option (List B256 × Sta)
  | 0 => some ⟨[], s⟩
  | n + 1 => do
    let (x, s') ← s.pop1
    let (xs, s'') ← s'.popN n
    some ⟨x :: xs, s''⟩

def sstoreStep (w₀ : Wor) (ω : Wor) (σ : Sta) (υ : Var) (κ : Con) :
    Option (Wor × Sta ×  Var) := do
  let (x, v', σ') ← σ.pop2
  let (a₀ : Acct) ← w₀.find? κ.cta
  let (v₀ : B256) := ((a₀.stor.find? x).getD 0)
  let (a : Acct) ← ω.find? κ.cta
  let (v : B256) := ((a.stor.find? x).getD 0)
  let c₀ : Nat := cond (υ.keys.contains ⟨κ.cta, x⟩) 0 gColdSLoad
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
  let g' ← safeSub υ.gas c
  let ref' ← (Int.ofNat υ.ref + r).toNat'
  let a' : Acct := {a with stor := a.stor.insertNonzero x v'}

  some
    ⟨
      ω.insert κ.cta a',
      σ',
      {
        υ with
        gas := g'
        pc := υ.pc + 1
        keys := υ.keys.insert ⟨κ.cta, x⟩
        ref := ref'
      }
    ⟩

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

def nextState (υ : Var) (cost : Nat)
  (act' : Option Nat := none)
  (ret' : B8L := υ.ret)
  (adrs' : AdrSet := υ.adrs)
  (logs' : List RLP' := υ.logs)
  (keys' : KeySet := υ.keys) : Option Var := do
  --let memCost : Nat := cMem act' - cMem υ.act
  let gas' ←
    match act' with
    | none => deductGas υ cost
    | some k => deductGas υ (cost + (cMem k - cMem υ.act))
  some {
      gas := gas',
      pc := υ.pc + 1,
      ret := ret'
      act := act'.getD υ.act
      dest := υ.dest
      adrs := adrs'
      keys := keys'
      ref := υ.ref
      logs := logs'
      tchd := υ.tchd
    }

def Wor.get (w : Wor) (a : Adr) : Acct := (w.find? a).getD .empty

def Sta.toStringsCore (xs : Array B256) : Nat → List String
  | 0 => []
  | n + 1 => ("0x" ++ (xs.getD n 0).toHex) :: Sta.toStringsCore xs n

def Sta.toStrings : Sta → List String
  | ⟨xs, n⟩ => Sta.toStringsCore xs n

def Sta.toString (s : Sta) : String := Strings.join s.toStrings

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

def Linst.toB8 : Linst → B8
  | .stop => 0x00
  | .ret => 0xF3
  | .rev => 0xFD
  | .dest => 0xFF
  | .invalid => 0xFE

def pushItem (σ : Sta) (μ : Mem) (υ : Var) (x : B256) (c : Nat) :
    Option (Sta × Mem × Var) := do
  let σ' ← σ.push1 x
  let υ' ← nextState υ c
  some ⟨σ', μ, υ'⟩

def checkRemGas (υ : Var) (cost : Nat) (act' : Nat) : Option Unit := do
  let memCost : Nat := cMem act' - cMem υ.act
  let _ ← deductGas υ (cost + memCost)
  return ()

def applyUnary (σ : Sta) (μ : Mem) (υ : Var) (f : B256 → B256) (cost : Nat) :
    Option (Sta × Mem × Var) := do
  let (x, σ') ← σ.pop1
  let σ'' ← σ'.push1 (f x)
  let υ' ← nextState υ cost
  some ⟨σ'', μ, υ'⟩

def applyBinary (σ : Sta) (μ : Mem) (υ : Var) (f : B256 → B256 → B256) (cost : Nat) :
    Option (Sta × Mem × Var) := do
  let (x, y, σ') ← σ.pop2
  let σ'' ← σ'.push1 (f x y)
  let υ' ← nextState υ cost
  some ⟨σ'', μ, υ'⟩

def applyTernary (σ : Sta) (μ : Mem) (υ : Var) (f : B256 → B256 → B256 → B256) (cost : Nat) :
    Option (Sta × Mem × Var) := do
  let (x, y, z, σ') ← σ.pop3
  let σ'' ← σ'.push1 (f x y z)
  let υ' ← nextState υ cost
  some ⟨σ'', μ, υ'⟩

def B256.toAdr : B256 → Adr
  | ⟨⟨_, x⟩, ⟨y, z⟩⟩ => {high := x.toUInt32, mid := y, low := z}

def Adr.toB256 (a : Adr) : B256 :=
  ⟨⟨0, a.high.toUInt64⟩ , ⟨a.mid, a.low⟩ ⟩

def Rinst.run (ω : Wor) (σ : Sta) (μ : Mem) (υ : Var) (κ : Con) :
    Rinst → Option (Sta × Mem × Var)
  | .address => pushItem σ μ υ κ.cta.toB256 gBase
  | .balance => do
    let (x, σ') ← σ.pop1
    let a := x.toAdr
    let adrs' : AdrSet := υ.adrs.insert a
    let σ'' ← σ'.push1 (ω.get a).bal
    let υ' ← nextState υ (cAAccess a υ.adrs) (adrs' := adrs')
    some ⟨σ'', μ, υ'⟩
  | .origin => pushItem σ μ υ κ.oga.toB256 gBase
  | .caller => pushItem σ μ υ κ.cla.toB256 gBase
  | .callvalue => pushItem σ μ υ κ.clv gBase
  | .calldataload => do
    let (x, σ') ← σ.pop1
    let cd  ← B8L.toB256? (κ.cld.sliceD x.toNat 32 0)
    let σ'' ← σ'.push1 cd
    let υ' ← nextState υ gVerylow
    some ⟨σ'', μ, υ'⟩
  | .calldatasize => pushItem σ μ υ κ.cld.length.toB256 gBase
  | .calldatacopy => do
    let (x, y, z, σ') ← σ.pop3
    let bs : B8L := κ.cld.sliceD y.toNat z.toNat 0
    let υ' ←
      nextState υ
        (gVerylow + (gCopy * ceilDiv z.toNat 32))
        (act' := memExp υ.act x z)
    some ⟨σ', Array.writeX μ x.toNat bs 0, υ'⟩
  | .codesize => pushItem σ μ υ κ.code.size.toB256 gBase
  | .codecopy => do
    let (x, y, z, σ') ← σ.pop3
    let cost := gVerylow + (gCopy * ceilDiv z.toNat 32)
    let υ' ← nextState υ cost (act' := memExp υ.act x z)
    let bs := κ.code.sliceD y.toNat z.toNat (Linst.toB8 .stop)
    some ⟨σ', Array.writeX μ x.toNat bs 0, υ'⟩
  | .gasprice => pushItem σ μ υ κ.gpr gBase
  | .extcodesize => do
    let (x, σ') ← σ.pop1
    let a := x.toAdr
    let adrs' : AdrSet := υ.adrs.insert a
    let σ'' ← σ'.push1 (ω.get a).code.size.toB256
    let υ' ← nextState υ (cAAccess a υ.adrs) (adrs' := adrs')
    some ⟨σ'', μ, υ'⟩
  | .extcodecopy => do
    let (x, y, z, w, σ') ← σ.pop4
    let cost := cAAccess x.toAdr υ.adrs + (gCopy * ceilDiv z.toNat 32)
    let υ' ← nextState υ cost (act' := memExp υ.act y w)
    let bs := κ.code.sliceD z.toNat w.toNat (Linst.toB8 .stop)
    some ⟨σ', Array.writeX μ y.toNat bs 0, υ'⟩
  | .retdatasize => pushItem σ μ υ υ.ret.length.toB256 gBase
  | .retdatacopy => do
    let (x, y, z, σ') ← σ.pop3
    let bs ← υ.ret.slice? y.toNat z.toNat
    let act' := memExp υ.act x z
    checkRemGas υ (gVerylow + (gCopy * (ceilDiv z.toNat 32))) act'
    let υ' ← nextState υ (gVerylow + (gCopy * (ceilDiv z.toNat 32))) (act' := act')
    some ⟨σ', Array.writeX μ x.toNat bs 0, υ'⟩
  | .extcodehash => do
    let (x, σ') ← σ.pop1
    let a := x.toAdr
    let adrs' := υ.adrs.insert a
    let hash : B256 :=
      if (Dead ω a)
      then 0
      else let cd := (ω.get a).code
           ByteArray.keccak 0 cd.size cd
    let σ'' ← σ'.push1 hash
    let υ' ← nextState υ (cAAccess a υ.adrs) (adrs' := adrs')
    some ⟨σ'', μ, υ'⟩
  | .selfbalance => pushItem σ μ υ (ω.get κ.cta).bal gLow
  | .chainid => pushItem σ μ υ κ.blk.chainId gBase
  | .number => pushItem σ μ υ κ.blk.number gBase
  | .timestamp => pushItem σ μ υ κ.blk.timestamp gBase
  | .gaslimit => pushItem σ μ υ κ.blk.gasLimit gBase
  | .prevrandao => pushItem σ μ υ κ.blk.prevRandao gBase
  | .coinbase => pushItem σ μ υ κ.blk.ben.toB256 gBase
  | .msize => pushItem σ μ υ (υ.act * 32).toB256 gBase
  | .mload => do
    let (x, σ') ← σ.pop1
    let bs : B8L := μ.sliceD x.toNat 32 0
    let y : B256 ← B8L.toB256? bs
    let act' := memExp υ.act x (32 : Nat).toB256
    checkRemGas υ gVerylow act'
    let σ'' ← σ'.push1 y
    let υ' ← nextState υ gVerylow (act' := act')
    some ⟨σ'', μ, υ'⟩
  | .mstore => do
    let (x, y, σ') ← σ.pop2
    let act' := memExp υ.act x (32 : Nat).toB256
    checkRemGas υ gVerylow act'
    let υ' ← nextState υ gVerylow (act' := act')
    some ⟨σ', Array.writeX μ x.toNat y.toB8L 0, υ'⟩
  | .mstore8 => do
    let (x, y, σ') ← σ.pop2
    let act' := memExp υ.act x 1
    checkRemGas υ gVerylow act'
    let υ' ← nextState υ gVerylow (act' := act')
    some ⟨σ', Array.writeX μ x.toNat [y.2.2.toUInt8] 0, υ'⟩
  | .gas => pushItem σ μ υ (υ.gas - gBase).toB256 gBase
  | .eq => applyBinary σ μ υ .eq_check gVerylow
  | .lt => applyBinary σ μ υ .lt_check gVerylow
  | .gt => applyBinary σ μ υ .gt_check gVerylow
  | .slt => applyBinary σ μ υ .slt_check gVerylow
  | .sgt => applyBinary σ μ υ .sgt_check gVerylow
  | .iszero => applyUnary σ μ υ (.eq_check · 0) gVerylow
  | .not => applyUnary σ μ υ (~~~ ·) gVerylow
  | .and => applyBinary σ μ υ B256.and gVerylow
  | .or => applyBinary σ μ υ B256.or gVerylow
  | .xor => applyBinary σ μ υ B256.xor gVerylow
  | .signextend => applyBinary σ μ υ B256.signext gLow


  -- | .pop => do
  --   let (_, σ') ← σ.pop1
  --   nextState μ σ' α (cost := gBase)
  | .pop => do
    let (_, σ') ← σ.pop1
    let υ' ← nextState υ gBase
    some ⟨σ', μ, υ'⟩

  -- | .byte => do
  --   let (x, y, σ') ← σ.pop2
  --   let b : B8 := (List.getD y.toB8L x.toNat 0)
  --   let σ'' ← σ'.push1 (b.toB256)
  --   nextState μ σ'' α (cost := gVerylow)
  | .byte =>
    applyBinary σ μ υ (λ x y => (List.getD y.toB8L x.toNat 0).toB256) gVerylow
  | .shl => applyBinary σ μ υ (fun x y => y <<< x.toNat) gVerylow
  | .shr => applyBinary σ μ υ (fun x y => y >>> x.toNat) gVerylow
  | .sar => applyBinary σ μ υ (fun x y => B256.sar x.toNat y) gVerylow
  | .kec => do
    let (x, y, σ') ← σ.pop2
    let act' := memExp υ.act x y
    let cost := gKeccak256 + (gKeccak256Word * (ceilDiv y.toNat 32))
    checkRemGas υ cost act'
    let σ'' ← σ'.push1 <| B8a.keccak x.toNat y.toNat μ
    let υ' ← nextState υ cost (act' := act')
    some ⟨σ'', μ, υ'⟩
  | .sub => applyBinary σ μ υ (· - ·) gVerylow
  | .mul => applyBinary σ μ υ (· * ·) gLow
  | .exp => do
    let (x, y, σ') ← σ.pop2
    let cost := g_exp + (g_expbyte * y.bytecount)
    let σ'' ← σ'.push1 (B256.bexp x y)
    let υ' ← nextState υ cost
    some ⟨σ'', μ, υ'⟩
  | .div => applyBinary σ μ υ (· / ·) gLow
  | .sdiv => applyBinary σ μ υ B256.sdiv gLow
  | .mod => applyBinary σ μ υ (· % ·) gLow
  | .smod => applyBinary σ μ υ B256.smod gLow
  | .add => applyBinary σ μ υ (· + ·) gVerylow
  | .addmod => applyTernary σ μ υ B256.addmod g_mid
  | .mulmod => applyTernary σ μ υ B256.mulmod g_mid
  | .swap n => do
    let σ' ← σ.swap n
    let υ' ← nextState υ gVerylow
    some ⟨σ', μ, υ'⟩
  | .dup n => do
    let σ' ← σ.dup n
    let υ' ← nextState υ gVerylow
    some ⟨σ', μ, υ'⟩
  | .sload => do
    let (x, σ') ← σ.pop1
    let cost : Nat := if υ.keys.contains ⟨κ.cta, x⟩ then gWarmAccess else gColdSLoad
    let ac ← ω.find? κ.cta
    let y := (ac.stor.find? x).getD 0
    let σ'' ← σ'.push1 y
    let υ' ← nextState υ cost (keys' := υ.keys.insert ⟨κ.cta, x⟩)
    some ⟨σ'', μ, υ'⟩
  | .pc => pushItem σ μ υ υ.pc.toB256 gBase
  | .log n => do
    let (x, y, σ') ← σ.pop2
    let act' := memExp υ.act x y
    let cost := gLog + (gLogdata * y.toNat) + (n * gLogtopic)
    checkRemGas υ cost act'
    let ⟨xs, σ''⟩ ← σ'.popN n
    let bs : B8L := μ.sliceD x.toNat y.toNat 0
    let log : RLP' :=
      .list [
        .b8s κ.cta.toB8L,
        .list (xs.map B256.toRLP),
        .b8s bs
      ]
    let υ' ← nextState υ cost (act' := act') (logs' := log :: υ.logs)
    some ⟨σ'', μ, υ'⟩
  | i => dbg_trace s!"UNIMPLEMENTED REGULAR INSTRUCTION EXECUTION : {i.toString}"; none


-- w₀ : the 'checkpoint' world saved at the preparation stage of tx

-- The intended behavior of 'execCore' is identical to the 'X' function of YP,
-- except that it returns 'none' if
--   (1) the VM is *CURRENTLY* (i.e, not at some later point in code) at
--       exceptional halting state due to the code byte that the program counter
--       points to, or
--   (2) recursion limit is reached (which should never happen with correct usage)

def gHigh : Nat := 10
def gJumpdest : Nat := 1

def Acct.isEmpty (ac : Acct) : Prop :=
  ac.nonce = 0 ∧
  ac.bal = 0 ∧
  ac.stor.isEmpty = .true ∧
  ac.code.size = 0

instance {ac : Acct} : Decidable ac.isEmpty := instDecidableAnd

def Wor.set (w : Wor) (a : Adr) (ac : Acct) : Wor :=
  if ac.isEmpty then w.erase a else w.insert a ac

def Wor.addBal (w : Wor) (a : Adr) (v : B256) : Wor :=
  let ac := w.get a
  let ac' : Acct := {ac with bal := ac.bal + v}
  w.set a ac'

def Wor.setBal (w : Wor) (a : Adr) (v : B256) : Wor :=
  let ac := w.get a
  let ac' : Acct := {ac with bal := v}
  w.set a ac'

def Jinst.run (σ : Sta) (υ : Var) (κ : Con) :
    Jinst → Option (Sta × Var)
  | .jumpdest => do
    let g' ← safeSub υ.gas gJumpdest
    some ⟨σ, {υ with gas := g', pc := υ.pc + 1}⟩
  | .jump => do
    let (loc, σ') ← σ.pop1
    let g' ← safeSub υ.gas g_mid
    if jumpable' κ.code loc.toNat
    then some ⟨σ', {υ with gas := g', pc := loc.toNat}⟩
    else none
  | .jumpi => do
    let (loc, val, σ') ← σ.pop2
    let g' ← safeSub υ.gas gHigh
    if val = 0
    then some ⟨σ', {υ with gas := g', pc := υ.pc + 1}⟩
    else if jumpable' κ.code loc.toNat
         then some ⟨σ', {υ with gas := g', pc := loc.toNat}⟩
         else none

def Ninst'.run (w₀ : Wor) (ω : Wor)
    (σ : Sta) (μ : Mem) (υ : Var) (κ : Con) :
    Ninst' → Option (Wor × Sta × Mem × Var)
  | .push x len => do
    let g' ← safeSub υ.gas (if len = 0 then gBase else gVerylow)
    --let x ← B8L.toB256? <| List.ekatD 32 bs 0
    let σ' ← σ.push1 x
    let υ' := {υ with gas := g', pc := υ.pc + len + 1}
    some ⟨ω, σ', μ, υ'⟩
  | .reg (.sstore) => do
    let ⟨ω', σ', υ'⟩ ← sstoreStep w₀ ω σ υ κ --α ε
    some ⟨ω', σ', μ, υ'⟩
  | .reg r => do
    let ⟨μ', σ', α'⟩ ← Rinst.run ω σ μ υ κ r --α ε r
    some ⟨ω, μ', σ', α'⟩
  | .exec e => dbg_trace s!"unimplemented xinst : {e.toString}\n" ; none

def retRun (ω : Wor) (σ : Sta) (μ : Mem) (υ : Var) : Option Ξ.Result := do
  let (rlc, rsz, _) ← σ.pop2
  let act' : Nat := memExp υ.act rlc rsz
  let memCost : Nat := cMem act' - cMem υ.act
  let g' ← safeSub υ.gas memCost
  let r := μ.sliceD rlc.toNat rsz.toNat 0
  some {wor := ω, gas := g', acs := υ.toAcs, ret := r}

def xhs (υ : Var) : Ξ.Result :=
  {wor := none, gas := υ.gas, acs := υ.toAcs, ret := none}

structure theta.Cont : Type where
  (olc : B256)
  (osz : B256)
  (gas : Nat)
  (mem : Array B8)
  (pc : Nat)
  (sta : Sta)
  (act : Nat)

-- Wor × Sta × Mem × Var × Con
def theta.Result.toState (ct : theta.Cont) (tr : theta.Result) :
    Option (Wor × Sta × Mem × Var) := do
  let cpy : B8L := List.take ct.osz.toNat tr.ret
  let xs ← ct.sta.push1 (if tr.status then 1 else 0)
  let υ' : Var := {
    gas := ct.gas + tr.gas
    pc := ct.pc + 1
    ret := tr.ret
    act := ct.act
    dest := tr.acs.dest
    adrs := tr.acs.adrs
    keys := tr.acs.keys
    ref := tr.acs.ref
    logs := tr.acs.logs
    tchd := tr.acs.tchd
  }
  some ⟨tr.wor, xs, Array.writeX ct.mem ct.olc.toNat cpy 0, υ'⟩

-- the X function of YP, except that the return type is modified to match
-- that of the Ξ function: the machine state (μ) returned by 'X' is never
-- used for anything except for remaining gas, so it is safe to discard the
-- unused information by the time X is returning.
-- This function returns 'none' only when either the recursion limit or an
-- unimplemented opcode is reached. returns 'some _' for all other cases.
-- return values :

def Ninst'.toString : Ninst' → String
  | reg o => Rinst.toString o
  | exec o => Xinst.toString o
  | push _ 0 => "PUSH0"
  | push x len => "PUSH" ++ len.repr ++ " " ++ x.toHex

def Inst'.toString : Inst' → String
  | .next n => n.toString
  | .jump j => j.toString
  | .last l => l.toString

def showLim (lim : Nat) (m : Var) : Option Unit :=
  match lim % 1000000 with
  | 0 => do
    dbg_trace s!"gas : {m.gas}"
    return ()
  | _ => return ()

def showExec (i : Inst') : Option Unit := do
  dbg_trace s!"executing inst : {i.toString}"
  return ()

def exec (w₀ : Wor) :
    Nat → Wor → Sta → Mem → Var → Con → Option Ξ.Result
  | 0, _, _, _, _, _ => none
  | lim + 1, ω, σ, μ, υ, κ  => do
    showLim lim υ
    match getInst υ κ  with
    | none => some <| xhs υ
    | some i => do
      -- dbg_trace s!"remaining gas : {υ.gas}"
      -- showExec i
      -- dbg_trace s!"current stack :\n{Sta.toString σ}"
      match i with
      | .next (.exec .delcall) => do
        let (gas, adr, ilc, isz, olc, osz, σ') ← σ.pop6
        let i : B8L := μ.sliceD ilc.toNat isz.toNat 0
        let t : Adr := adr.toAdr
        -- dbg_trace s!"nested delgatecall to address : {t.toHex}"
        let as' : AdrSet := υ.adrs.insert t
        let A' : Acs := {υ.toAcs with adrs := as'}
        let act' : Nat := memExp (memExp υ.act ilc isz) olc osz
        let memCost : Nat := cMem act' - cMem υ.act
        let cg : Nat := cCallGas ω υ gas.toNat memCost t 0
        let totalCost := (cCall ω υ gas.toNat memCost t 0) + memCost
        let (some g') ← (return (safeSub υ.gas totalCost)) | some (xhs υ)
        let bd : theta.Cont :=
          {
            olc := olc
            osz := osz
            gas := g'
            mem := μ
            pc := υ.pc
            sta := σ'
            act := act'
          }
        let ⟨ω?, σ?, μ?, υ?⟩ ←
          if 0 = κ.exd
          then (theta.Result.toState bd ⟨ω, cg, A', 0, []⟩)
          else do let ⟨ω!, σ!, μ!, υ!, κ!⟩ :=
                        θ.prep
                          κ.blk
                          ω
                          A'
                          κ.cla
                          κ.oga
                          κ.cta
                          t
                          cg
                          κ.gpr.toNat
                          0
                          κ.clv
                          i
                          (κ.exd - 1)
                          κ.wup
                  let xr ← exec w₀ lim ω! σ! μ! υ! κ!
                  let θr := θ.wrap ω! υ!.toAcs xr
                  (theta.Result.toState bd θr)
        exec w₀ lim ω? σ? μ? υ? κ
      | .next (.exec .call) => do
        let (gas, adr, clv, ilc, isz, olc, osz, σ') ← σ.pop7
        let i : B8L := μ.sliceD ilc.toNat isz.toNat 0
        let t : Adr := adr.toAdr
        -- dbg_trace s!"nested call to address : {t.toHex}"
        let as' : AdrSet := υ.adrs.insert t
        let A' : Acs := {υ.toAcs with adrs := as'}
        let act' : Nat := memExp (memExp υ.act ilc isz) olc osz
        let memCost : Nat := cMem act' - cMem υ.act
        let cg : Nat := cCallGas ω υ gas.toNat memCost t clv
        let totalCost := (cCall ω υ gas.toNat memCost t clv) + memCost
        let (some g') ← (return (safeSub υ.gas totalCost)) | some (xhs υ)
        let bd : theta.Cont :=
          {
            olc := olc
            osz := osz
            gas := g'
            mem := μ
            pc := υ.pc
            sta := σ'
            act := act'
          }
        let ⟨ω?, σ?, μ?, υ?⟩ ←
          if 0 = κ.exd ∨ (ω.get κ.cta).bal < clv
          then (theta.Result.toState bd ⟨ω, cg, A', 0, []⟩)
          else do let ⟨ω!, σ!, μ!, υ!, κ!⟩  : (Wor × Sta × Mem × Var × Con) :=
                        θ.prep
                          κ.blk
                          ω
                          A'
                          κ.cta
                          κ.oga
                          t
                          t
                          cg
                          κ.gpr.toNat
                          clv
                          clv
                          i
                          (κ.exd - 1)
                          κ.wup
                  -- dbg_trace s!"code of nested delcall : {B8L.toHex s'.env.code.toList}"
                  let xr ← exec w₀ lim ω! σ! μ! υ! κ!
                  let θr := θ.wrap ω! υ!.toAcs xr
                  (theta.Result.toState bd θr)
        exec w₀ lim ω? σ? μ? υ? κ
      | .next n =>
        match n.run w₀ ω σ μ υ κ  with
        | none => some (xhs υ)
        | some ⟨ω', σ', μ', υ'⟩ => exec w₀ lim ω' σ' μ' υ' κ --s'.env s'.acr s'.wor s'.mcn
      | .jump j =>
         match j.run σ υ κ with
         | none => some (xhs υ)
         | some ⟨σ', υ'⟩ => exec w₀ lim ω σ' μ υ' κ
      | .last .stop => some {wor := ω, gas := υ.gas, acs := υ.toAcs, ret := some []}
      | .last .ret => some <| (retRun ω σ μ υ).getD (xhs υ)
      | .last .dest => do
        let (x, _) ← σ.pop1
        let a := x.toAdr -- recipient
        let cost :=
          gSelfdestruct
          + (if a ∈ υ.adrs then 0 else gColdAccountAccess)
          + ( if Dead ω a ∧ ω.balAt κ.cta ≠ 0
              then gNewAccount
              else 0 )
        let gas' ← deductGas υ cost
        some
          {
            wor :=
              if a = κ.cta
              then ω
              else let v := (ω.get κ.cta).bal
                   let wor' := ω.setBal κ.cta 0
                   wor'.addBal a v
            gas := gas'
            acs :=
              {
                υ.toAcs with
                dest := κ.cta :: υ.dest
                adrs := υ.adrs.insert a
              }
            ret := some []
          }

      | _ => none --dbg_trace s!"unimplemented instruction : {i.toString}"; none

def theta
  -- Extra arguments not mentioned by YP,
  -- but still necessary for correct execution
  (H : Block)
  (ω₀ : Wor)

  -- Arguments specified by YP
  (ω : Wor)
  (A : Acs)
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
  Option theta.Result :=
  let ⟨ω?, σ?, μ?, υ?, κ?⟩ := θ.prep H ω A s o r c g p v v_app d e w
  match exec ω₀ g ω? σ? μ? υ? κ? with
  | none => none
  | some xr => some (θ.wrap ω? υ?.toAcs xr)

def publicAddress (hsa : ByteArray) (ri : UInt8) (rsa : ByteArray) : IO Adr :=
  match (ecrecoverFlag hsa ri rsa).toList with
  | [] => IO.throw "Unreachable code : ecrecover should never return empty bytes"
  | b :: pa =>
    if b = 0
    then IO.throw "ecrecover failed"
    else (B8L.toAdr pa).toIO "bytearray to address conversion failed"

def IO.guard (φ : Prop) [Decidable φ] (msg : String) : IO Unit :=
  if φ then return () else IO.throw msg

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
  (acc : AccessList)

structure transact.Result : Type where
  (wor : Wor)
  (gas : Nat)
  (log : B256)
  (sta : Bool)

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

def eqTest {ξ} [DecidableEq ξ] (x y : ξ) (testName : String) : IO Unit := do
  .guard (x = y) (testName ++ " : fail")
  .println (testName ++ " : pass")

def eraseIfEmpty (w : Wor) (a : Adr) : Wor := w.set a <| w.get a

def Tx.run
  (blk : Block) (w : Wor) (tx : TxBytesContent)
  (sender : Adr) : IO transact.Result := do

  IO.println s!"block gas limit : 0x{blk.gasLimit.toHex}"
  IO.println s!"tx gas limit    : 0x{tx.gasLimit.toHex}"
  IO.guard (tx.gasLimit ≤ blk.gasLimit) "error : block gas limit < tx gas limit"

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
  let refundAmount : Nat := tr.acs.ref
  let gasReturn : B256 :=
    Nat.toB256 (gasLeft + min ((tx.gasLimit.toNat - gasLeft) / 5) refundAmount) -- g*
  let gasUsed : B256 := tx.gasLimit - gasReturn
  let valReturn : B256 := gasReturn * tx.gasPrice

  let f : B256 :=
    match tx.type with
      | .two _ tm tf => min tf (tm - blk.baseFee)
      | _ => tx.gasPrice - blk.baseFee

  let w₀ : Wor := tr.wor.addBal sender valReturn
  let w₁ : Wor := w₀.addBal blk.ben (gasUsed * f)
  --let w₂ : Wor := List.foldl Lean.RBMap.erase w₁ tr.acr.dest
  --let w₃ : Wor := List.foldl eraseIfEmpty w₂ tr.acr.tchd.toList
  let w₃ : Wor := List.foldl eraseIfEmpty w₁ tr.acs.tchd.toList

  return {
    wor := w₃,
    gas := gasUsed.toNat
    log := (RLP'.list tr.acs.logs.reverse).encode.keccak
    sta := tr.status
  }

def String.joinnl (l : List String) : String :=
  l.foldl (fun r s => r ++ "\n" ++ s) ""

def Test.run (t : Test) : IO Unit := do
  let ⟨tx, hsh⟩ ← decodeTxBytes t.txdata
  let rsa : ByteArray := ⟨Array.mk (tx.r ++ tx.s)⟩
  let hsa : ByteArray := ⟨Array.mk hsh.toB8L⟩
  let ri : UInt8 := Byte.toB8 (if tx.yParity then 1 else 0)
  let sender ← publicAddress hsa ri rsa

  .println "initial world : "
  .println (Strings.join t.world.toStrings)

  let sa₀ ← (t.world.find? sender).toIO "no sender account"

  .guard (tx.nonce = t.nonce) "nonce check 1 : fail"
  .println "nonce check 1 : pass"

  .guard (tx.nonce = sa₀.nonce) "nonce check 2 : fail"
  .println "nonce check 2 : pass"

  .guard (sender = t.sender) "sender check : fail"
  .println "sender check : pass"

  .guard (tx.receiver = t.receiver) "receiver check : fail"
  .println s!"receiver : {tx.receiver.toHex}"

  .guard (tx.gasLimit = t.gasLimit) s!"gas limit check failed. tx.gasLimit : {tx.gasLimit.toHex}, t.gasLimit = {t.gasLimit.toHex}"
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
  .println (Strings.join rst.wor.toStrings)

  let temp' := (List.map toKeyVal rst.wor.toList)
  let finalNTB : NTB := Lean.RBMap.fromList temp' _
  let root' : B256 := trie finalNTB

  .println s!"computed final root' : {root'.toHex}"
  .println s!"expected final root  : {t.hash.toHex}"

  .guard (root' = t.hash) "state root' check : fail"
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

def main : List String → IO Unit
  | [testPath] => do
    let j ← readJsonFile testPath
    let td ← Lean.Json.toTestData j
    let ts ← getTests td
    Tests.run 1 ts
  | [testPath, testNum] => do
    let n ← testNum.toNat?.toIO "error : second argument is not a number"
    let j ← readJsonFile testPath
    let td ← Lean.Json.toTestData j
    let ts ← getTests td
    ((ts.get? n).toIO s!"test #{n} does not exist") >>= Test.run
  | _ => IO.throw "error : invalid arguments"
