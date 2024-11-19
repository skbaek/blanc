import «Blanc».Weth

partial def Bytes.chunks (bs : Bytes) : List Bytes :=
  match bs.splitAt 32 with
  | (_, []) => [bs]
  | (bs', bs'') => bs' :: chunks bs''

def Bytes.toHexLine (bs : Bytes) : String :=
  s!"hex\"{bs.toHextring}\""

def WethByteCode : String :=
  List.foldr
     (λ s0 s1 => s0 ++ "\n" ++ s1)
     "" <| List.map Bytes.toHexLine
        <| Bytes.chunks <| Option.getD weth.compile []

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


def Nat.toBytes' (n : Nat) : Bytes :=
  if n < 256
  then [n.toByte]
  else (n % 256).toByte :: (n / 256).toBytes'

def Nat.toBytes (n : Nat) : Bytes := n.toBytes'.reverse

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
  | .bytes bs => [s!"0x{bs.toHextring}"]
  | .list rs => "List:" :: (rs.map RLP.toStrings).flatten.map ("  " ++ ·)

def Strings.join : List String → String
  | [] => ""
  | s :: ss => s ++ "\n" ++ Strings.join ss

def Hexes.toBytes : List Hex → Option Bytes
  | [] => some []
  | [_] => none
  | h0 :: h1 :: hs => (Ox h0 h1 :: ·) <$> Hexes.toBytes hs

def Hextring.toBytes (s : String) : Option Bytes :=
  Hexes.toBytes <| s.data.map Hexar.toHex

def notTxBytes : Bytes :=
  (Hextring.toBytes "f885800a8404c4b40094cccccccccccccccccccccccccccccccccccccccc01a4693c613900000000000000000000000000000000000000000000000000000000000000001ba0e8ff56322287185f6afd3422a825b47bf5c1a4ccf0dc0389cdc03f7c1c32b7eaa0776b02f9f5773238d3ff36b74a123f409cd6420908d7855bbe4c8ff63e00d698").getD []

def highValueTxBytes : Bytes :=
  (Hextring.toBytes "f87f800182520894095e7baea6a6c7c4c2dfeb977efac326af552d87a0ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff801ba048b55bfa915ac795c431978d8a6a992b628d557da5ff759b307d495a36649353a01fffd310ac743f371de3b9f7f9cb56c0b28ad43601b4ab949f53faa07bd2c804").getD []

def optionToIO {ξ} (o : Option ξ) : IO ξ := do
  match o with
  | none => throw (IO.Error.userError "none value")
  | some x => pure x

@[extern "ecrecover"]
opaque ecrecover : ByteArray → ByteArray → ByteArray

def Byte.toUInt8 (b : Byte) : UInt8 := ⟨⟨b.toNat, b.toNat_lt_pow⟩⟩
def UInt8.toByte (i : UInt8) : Byte := i.toBitVec.toFin.val.toByte

def Bytes.toBytesArray (bs : Bytes) : ByteArray := ⟨⟨List.map Byte.toUInt8 bs⟩⟩
def ByteArray.toBytes (a : ByteArray) : Bytes := a.data.toList.map UInt8.toByte

def main : IO Unit := do
  let bs := highValueTxBytes
  let (RLP.list [txType, nonce, gasPrice, toAddr, val, calldata, .bytes v, .bytes r, .bytes s])
    ← (optionToIO <| RLP.decode bs)
    | throw (IO.Error.userError "Error : decoded list length ≠ 9")
  let bs' := RLP.encode <| .list [txType, nonce, gasPrice, toAddr, val, calldata]
  let hs := bs'.keccak

  IO.println <| s!"v : {v.toNat}"
  IO.println <| s!"r : {r.toHextring}"
  IO.println <| s!"s : {s.toHextring}"
  IO.println <| s!"Hash of txdata excluding signature: {Bits.toHextring 32 hs}"

  let rsa : ByteArray := Bytes.toBytesArray (r ++ s)
  let hsa : ByteArray := Bytes.toBytesArray (@Bits.toBytes 32 hs)

  match (ecrecover rsa hsa).toBytes with
  | [] => IO.println "Unreachable code : ecrecover should never return empty bytes"
  | b :: pa =>
    if b = 0
    then IO.println "ecrecover failed"
    else IO.println <| s!"Recovered public address : {Bytes.toHextring pa}"
