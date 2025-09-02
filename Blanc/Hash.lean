import Blanc.Basic



namespace RIPEMD160

------------------------------ RIPEMD-160 ------------------------------

-- RIPEMD-160 hash function. Ported from David Turner's
-- C implementation (https://github.com/DaveCTurner/tiny-ripemd160)

-- ripemf160_shifts
def shiftLists : List B32L :=
  [
    [11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8],
    [12, 13, 11, 15, 6, 9, 9, 7, 12, 15, 11, 13, 7, 8, 7, 7],
    [13, 15, 14, 11, 7, 7, 6, 8, 13, 14, 13, 12, 5, 5, 6, 9],
    [14, 11, 12, 14, 8, 6, 5, 5, 15, 12, 15, 14, 9, 9, 8, 6],
    [15, 12, 13, 13, 9, 5, 8, 6, 14, 11, 12, 11, 8, 6, 5, 5]
  ]

-- ripemd160_constants_left
def constantsLeft : B32L :=
  [0x00000000, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e]

-- ripemd160_constants_right
def constantsRight : B32L :=
  [0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0x00000000]

-- ripemd160_fns_left
def fnsLeft : List Nat := [1, 2, 3, 4, 5]

-- ripemd160_fns_right
def fnsRight : List Nat := [5, 4, 3, 2, 1]

def rho : List Nat :=
  [ 0x7, 0x4, 0xd, 0x1, 0xa, 0x6, 0xf, 0x3,
    0xc, 0x0, 0x9, 0x5, 0x2, 0xe, 0xb, 0x8 ]

def computeLine (digest : B32L) (chunk : B32L) (index : List Nat)
  (shiftss : List B32L) (ks : B32L) (fns : List Nat) : Id B32L := do
  let mut index := index
  let mut w0 : B32 := digest.get! 0
  let mut w1 : B32 := digest.get! 1
  let mut w2 : B32 := digest.get! 2
  let mut w3 : B32 := digest.get! 3
  let mut w4 : B32 := digest.get! 4
  for round in [0, 1, 2, 3, 4] do
    let shifts : B32L := shiftss.get! round
    let k : B32 := ks.get! round
    let fn : Nat := fns.get! round
    for i in List.range 16 do
      let mut tmp : B32 :=
        match fn with
        | 1 => w1 ^^^ w2 ^^^ w3
        | 2 => (w1 &&& w2) ||| (~~~ w1 &&& w3)
        | 3 => (w1 ||| ~~~ w2) ^^^ w3
        | 4 => (w1 &&& w3) ||| (w2 &&& ~~~ w3)
        | _ => w1 ^^^ (w2 ||| ~~~ w3)
      tmp := tmp + w0 + (chunk.get! (index.get! i)) + k
      tmp := B32.rol tmp (shifts.get! (index.get! i)) + w4
      w0 := w4
      w4 := w3
      w3 := B32.rol w2 10
      w2 := w1
      w1 := tmp
    index := index.map rho.get!
  return [w0, w1, w2, w3, w4]

def updateDigest (digest : B32L) (chunk : B32L) : Id B32L := do
  let indexLeft : List Nat := List.range 16
  let wordsLeft : B32L ←
    computeLine digest chunk indexLeft shiftLists constantsLeft fnsLeft
  let indexRight : List Nat :=
    [ 0x05, 0x0e, 0x07, 0x00, 0x09, 0x02, 0x0b, 0x04,
      0x0d, 0x06, 0x0f, 0x08, 0x01, 0x0a, 0x03, 0x0c ]
  let wordsRight : B32L ←
    computeLine digest chunk indexRight
      shiftLists constantsRight fnsRight
  return [
    digest.get! 1 + wordsLeft.get! 2 + wordsRight.get! 3,
    digest.get! 2 + wordsLeft.get! 3 + wordsRight.get! 4,
    digest.get! 3 + wordsLeft.get! 4 + wordsRight.get! 0,
    digest.get! 4 + wordsLeft.get! 0 + wordsRight.get! 1,
    digest.get! 0 + wordsLeft.get! 1 + wordsRight.get! 2
  ]

def B8L.toB32Rev : B8L → B32L
  | (b0 :: b1 :: b2 :: b3 :: bs) =>
    B8s.toB32 b3 b2 b1 b0 :: B8L.toB32Rev bs
  | _ => []

def processChunks (digest : B32L) (data : B8L) (lenSfx : B32L) : Nat → B32L
  | 0 =>
    if data.length > 55 then
      let penultChunk : B32L :=
        B8L.toB32Rev (List.takeD 64 (data ++ [0x80]) 0)
      let digest' := updateDigest digest penultChunk
      let lastChunk : B32L := List.replicate 14 (0 : B32) ++ lenSfx
      updateDigest digest' lastChunk
    else
      let lastChunk : B32L :=
        B8L.toB32Rev (List.takeD 56 (data ++ [0x80]) 0) ++ lenSfx
      updateDigest digest lastChunk
  | n + 1 =>
    let ⟨pfx, data'⟩ := data.splitAt 64
    let chunk : B32L := B8L.toB32Rev pfx
    let digest' := updateDigest digest chunk
    processChunks digest' data' lenSfx n

def run (data : B8L) : B8L := do
  let initDigest : B32L :=
    [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]
  let len : B32 := data.length.toUInt32
  let digest : B32L :=
    processChunks initDigest data [len <<< 3, len >>> 29] (data.length / 64)
  List.foldr (fun x acc => x.toB8L.reverse ++ acc) [] digest

end RIPEMD160

def B8L.ripemd160 : B8L → B8L := RIPEMD160.run



------------------------------SHA256------------------------------

-- 256-bit SHA-2 hash function. Ported from Alain Mosnier's
-- C implementation (https://github.com/amosnier/sha-2)

namespace SHA256

def initChunk : B32A :=
  #[ 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
     0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ]

def B8L.toChunks (lenB8L : B8L) : Nat → B8L → Nat → List B8A
  | 0, _, _ => []
  | _ + 1, _, 0 =>
    [((Array.mkArray 64 0x00).set! 0 0x80).writeD 56 lenB8L]
  | k + 1, xs, len' + 64 =>
      let ⟨pfx, xs'⟩ := List.splitToArray 64 xs 0
      let xss := B8L.toChunks lenB8L k xs' len'
      pfx :: xss
  | _ + 1, xs, _ + 56 =>
    [ ⟨xs ++ (0x80 :: List.replicate (64 - (xs.length + 1)) 0x00)⟩,
      ⟨(List.replicate (56 : Nat) 0x00) ++ lenB8L⟩ ]
  | _ + 1, xs, _ =>
    [⟨xs ++ (0x80 :: List.replicate (64 - (xs.length + 9)) 0x00) ++ lenB8L⟩]

def getAddMod (w : B32A) (j n : Nat) := (w.getD ((j + n) % 16) 0)

def roundConstants : B32A :=
 #[ 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 ]

def computeNewEntry (w : B32A) (p : B8A) (i j : Nat) : B32 :=
  if i = 0
  then
    B8s.toB32
      (p.getD (4 * j) 0)
      (p.getD ((4 * j) + 1) 0)
      (p.getD ((4 * j) + 2) 0)
      (p.getD ((4 * j) + 3) 0)
  else
    let s0 : B32 :=
      (B32.ror (getAddMod w j 1) 7) ^^^
      (B32.ror (getAddMod w j 1) 18) ^^^
      ((getAddMod w j 1) >>> 3)
    let s1 :=
      (B32.ror (getAddMod w j 14) 17) ^^^
      (B32.ror (getAddMod w j 14) 19) ^^^
      ((getAddMod w j 14) >>> 10)
    (w.getD j 0) + s0 + (getAddMod w j 9) + s1

def computeTemps (ah w' : B32A) (i j : Nat): B32 × B32 :=
  let s1 : B32 :=
    (B32.ror (ah.get! 4) 6) ^^^
    (B32.ror (ah.get! 4) 11) ^^^
    (B32.ror (ah.get! 4) 25)
  let ch : B32 :=
    (ah.get! 4 &&& ah.get! 5) ^^^
    ((~~~ (ah.get! 4)) &&& ah.get! 6)
  let temp1 : B32 :=
    (ah.get! 7) + s1 + ch +
    (roundConstants.get! ((i * 16) + j)) +
    (w'.get! j)
  let s0 : B32 :=
    (B32.ror (ah.get! 0) 2) ^^^
    (B32.ror (ah.get! 0) 13) ^^^
    (B32.ror (ah.get! 0) 22)
  let maj : B32 :=
    (ah.get! 0 &&& ah.get! 1) ^^^
    (ah.get! 0 &&& ah.get! 2) ^^^
    (ah.get! 1 &&& ah.get! 2)
  let temp2 : B32 := s0 + maj
  ⟨temp1, temp2⟩

def indices : List (Nat × Nat) :=
  [
    (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7),
    (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15),
    (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7),
    (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (1, 15),
    (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7),
    (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (2, 15),
    (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7),
    (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 15)
  ]

def consumeChunk (h : B32A) (p : B8A) : B32A :=
  let aux : (B32A × B32A) → (Nat × Nat) → B32A × B32A
    | ⟨h, w⟩, ⟨i, j⟩ =>
      let newEntry : B32 := computeNewEntry w p i j
      let w' := Array.set! w j newEntry
      let ⟨temp1, temp2⟩ := computeTemps h w' i j
      let h' :=
        ⟨ [ temp1 + temp2, h.get! 0, h.get! 1, h.get! 2,
            h.get! 3 + temp1, h.get! 4, h.get! 5, h.get! 6 ] ⟩
      ⟨h', w'⟩
  let h' := List.foldl aux ⟨h, .mkArray 16 0⟩ indices |>.fst
  ⟨
    [
      h.get! 0 + h'.get! 0,
      h.get! 1 + h'.get! 1,
      h.get! 2 + h'.get! 2,
      h.get! 3 + h'.get! 3,
      h.get! 4 + h'.get! 4,
      h.get! 5 + h'.get! 5,
      h.get! 6 + h'.get! 6,
      h.get! 7 + h'.get! 7
    ]
  ⟩

def run (data : B8L) : B256 :=
  let xss : List B8A :=
    B8L.toChunks
      (B64.toB8L (data.length * 8).toUInt64)
      (data.length / 64).succ
      data
      data.length
  let hash := List.foldl consumeChunk initChunk xss
  match hash with
  | ⟨[x0, x1, x2, x3, y0, y1, y2, y3]⟩ =>
    B32s.toB256 x0 x1 x2 x3 y0 y1 y2 y3
  | _ => (dbg_trace "incorrect number of 32-bit numbers in hash"; 0)

end SHA256

def B8L.sha256 : B8L → B256 := SHA256.run



------------------------------KECCAK------------------------------

-- 256-bit keccak hash function. Ported from Andrey Jivsov's
-- C implementation (https://github.com/brainhub/SHA3IUF)

namespace KECCAK

def Array.app {ξ : Type u} (k : Nat) (f : ξ → ξ) (ws : Array ξ) : Array ξ :=
  match ws.get? k with
  | none => panic "Array.app out of bounds"
  | some x => ws.set! k (f x)

def Bits.rol {n} (xs : Bits n) (y : Nat) : Bits n :=
  Bits.or (xs.shl y) (xs.shr (n - y))

def B64.rol (xs : B64) (y : Nat) : B64 :=
  (xs <<< y.toUInt64) ||| (xs >>> (64 - y).toUInt64)

def θ {ξ : Type u} [Xor ξ] [Inhabited ξ]
  (ws : Array ξ) (rol : ξ → Nat → ξ) : Array ξ :=
  let prep (x : Fin 5) : ξ :=
    ws.get! x ^^^
    ws.get! (x + 5) ^^^
    ws.get! (x + 10) ^^^
    ws.get! (x + 15) ^^^
    ws.get! (x + 20)
  let initVec : Vec ξ 5 :=
    ⟨[prep 0, prep 1, prep 2, prep 3, prep 4], rfl⟩
  let rec inner (t : ξ) (i : Nat) : Nat → Array ξ → Array ξ
    | 0, ws => ws
    | j + 1, ws => inner t i j <| Array.app ((j * 5) + i) (· ^^^ t) ws
  let rec outer (bc : Vec ξ 5) : Nat → Array ξ → Array ξ
    | 0, ws => ws
    | i + 1, ws =>
      let t : ξ := bc.get (i + 4) ^^^ rol (bc.get (i + 1)) 1
      outer bc i <| inner t i 5 ws
  outer initVec 5 ws

def keccak_rdnc_00 : Bits 64 := Hex.toBits! 16 "0000000000000001"
def keccak_rdnc_01 : Bits 64 := Hex.toBits! 16 "0000000000008082"
def keccak_rdnc_02 : Bits 64 := Hex.toBits! 16 "800000000000808a"
def keccak_rdnc_03 : Bits 64 := Hex.toBits! 16 "8000000080008000"
def keccak_rdnc_04 : Bits 64 := Hex.toBits! 16 "000000000000808b"
def keccak_rdnc_05 : Bits 64 := Hex.toBits! 16 "0000000080000001"
def keccak_rdnc_06 : Bits 64 := Hex.toBits! 16 "8000000080008081"
def keccak_rdnc_07 : Bits 64 := Hex.toBits! 16 "8000000000008009"
def keccak_rdnc_08 : Bits 64 := Hex.toBits! 16 "000000000000008a"
def keccak_rdnc_09 : Bits 64 := Hex.toBits! 16 "0000000000000088"
def keccak_rdnc_10 : Bits 64 := Hex.toBits! 16 "0000000080008009"
def keccak_rdnc_11 : Bits 64 := Hex.toBits! 16 "000000008000000a"
def keccak_rdnc_12 : Bits 64 := Hex.toBits! 16 "000000008000808b"
def keccak_rdnc_13 : Bits 64 := Hex.toBits! 16 "800000000000008b"
def keccak_rdnc_14 : Bits 64 := Hex.toBits! 16 "8000000000008089"
def keccak_rdnc_15 : Bits 64 := Hex.toBits! 16 "8000000000008003"
def keccak_rdnc_16 : Bits 64 := Hex.toBits! 16 "8000000000008002"
def keccak_rdnc_17 : Bits 64 := Hex.toBits! 16 "8000000000000080"
def keccak_rdnc_18 : Bits 64 := Hex.toBits! 16 "000000000000800a"
def keccak_rdnc_19 : Bits 64 := Hex.toBits! 16 "800000008000000a"
def keccak_rdnc_20 : Bits 64 := Hex.toBits! 16 "8000000080008081"
def keccak_rdnc_21 : Bits 64 := Hex.toBits! 16 "8000000000008080"
def keccak_rdnc_22 : Bits 64 := Hex.toBits! 16 "0000000080000001"
def keccak_rdnc_23 : Bits 64 := Hex.toBits! 16 "8000000080008008"

def Bits.rdnc : Array (Bits 64) :=
  #[
    keccak_rdnc_00, keccak_rdnc_01, keccak_rdnc_02, keccak_rdnc_03,
    keccak_rdnc_04, keccak_rdnc_05, keccak_rdnc_06, keccak_rdnc_07,
    keccak_rdnc_08, keccak_rdnc_09, keccak_rdnc_10, keccak_rdnc_11,
    keccak_rdnc_12, keccak_rdnc_13, keccak_rdnc_14, keccak_rdnc_15,
    keccak_rdnc_16, keccak_rdnc_17, keccak_rdnc_18, keccak_rdnc_19,
    keccak_rdnc_20, keccak_rdnc_21, keccak_rdnc_22, keccak_rdnc_23
  ]

def B64.rdnc : Array B64 :=
  #[ 0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
     0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
     0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
     0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
     0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
     0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008 ]

def keccakf_rotc : Array Nat :=
  #[ 1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14,
     27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44 ]

def keccakf_piln : Array Nat :=
  #[ 10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4,
     15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1 ]

def ρπ {ξ : Type u} [Inhabited ξ] (ws : Array ξ) (rol : ξ → Nat → ξ) : Array ξ :=
  let rec aux : Nat → ξ → Array ξ → Array ξ
    | 0, _, ws => ws
    | k + 1, t, ws =>
      let i := 23 - k
      let j := keccakf_piln.get! i
      let ws' := ws.set! j (rol t <| keccakf_rotc.get! i)
      aux k (ws.get! j) ws'
  aux 24 (ws.get! 1) ws

def χ {ξ : Type u} [Xor ξ] [Complement ξ] [HAnd ξ ξ ξ] [Inhabited ξ]
  (ws : Array ξ) : Array ξ :=
  let rec inner (ws : Array ξ) (bc : Array ξ) (j : Nat) : Nat → Array ξ
    | 0 => ws
    | i + 1 =>
      let ws' :=
        Array.app (j + i)
          (· ^^^ ((~~~ bc.get! ((i + 1) % 5)) &&& (bc.get! ((i + 2) % 5)))) ws
      inner ws' bc j i
  let rec outer (ws : Array ξ) : Nat → Array ξ
    | 0 => ws
    | k + 1 =>
      let j := k * 5
      let f : Nat → ξ := λ x => ws.get! (j + x)
      let bc : Array ξ := #[f 0, f 1, f 2, f 3, f 4]
      let ws' : Array ξ := inner ws bc j 5
      outer ws' k
  outer ws 5

def ι {ξ : Type u} [Xor ξ] [Inhabited ξ]
  (round : Nat) (rdnc : Array ξ) (ws : Array ξ) : Array ξ :=
  Array.app 0 (· ^^^ (Array.get! rdnc round)) ws

def f {ξ : Type u} [Xor ξ] [Complement ξ] [HAnd ξ ξ ξ] [Inhabited ξ]
  (rdnc : Array ξ) (ws : Array ξ) (rol : ξ → Nat → ξ) : Array ξ :=
  let rec aux : Nat → Array ξ → Array ξ
    | 0, ws => ws
    | 24, ws =>
      let temp := θ ws rol
      aux 23 <| ι 0 rdnc <| χ <| ρπ temp rol
    | n + 1, ws =>
      aux n <| ι (23 - n) rdnc <| χ <| ρπ (θ ws rol) rol
  aux 24 ws

def Bytes.run : Fin 17 → Bytes → Array (Bits 64)→ Word
  | wc, b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs, ws =>
    let t : Bits 64 := Bytes.toBits 8 [b7, b6, b5, b4, b3, b2, b1, b0]
    let ws' := Array.app wc (· ^^^ t) ws
    Bytes.run (wc + 1) bs <| if wc = 16 then (f Bits.rdnc ws' Bits.rol) else ws'
  | wc, bs, ws =>
    let rev (w : Bits 64) : Bits 64 :=
      Bytes.toBits 8 (@Bits.toBytes 8 w).reverse
    let t : Bits 64 := Bytes.toBits' 8 ((bs ++ [Bits.one 8]).takeD 8 (.zero 8)).reverse
    let s := (Hex.toBits 16 "8000000000000000").getD 0
    let temp0 := Array.app wc (· ^^^ t) ws
    let temp1 := Array.app 16 (· ^^^ s) temp0
    let ws' := f Bits.rdnc temp1 Bits.rol
    (rev <| ws'.get! 0) ++ (rev <| ws'.get! 1) ++
    (rev <| ws'.get! 2) ++ (rev <| ws'.get! 3)

def B8L.run : Fin 17 → B8L → Array B64 → B256
  | wc, b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs, ws =>
    let t : B64 := B8s.toB64 b7 b6 b5 b4 b3 b2 b1 b0
    let ws' := Array.app wc (· ^^^ t) ws
    B8L.run (wc + 1) bs <| if wc = 16 then (f B64.rdnc ws' B64.rol) else ws'
  | wc, bs, ws =>
    let us := (bs ++ [(1 : B8)]).takeD 8 (0 : B8)
    let t : B64 :=
      B8s.toB64
        (us.get! 7) (us.get! 6) (us.get! 5) (us.get! 4)
        (us.get! 3) (us.get! 2) (us.get! 1) (us.get! 0)
    let s : B64 := (8 : B64) <<< 60
    let temp0 := Array.app wc (· ^^^ t) ws
    let temp1 := Array.app 16 (· ^^^ s) temp0
    let ws' := f B64.rdnc temp1 B64.rol
    (B64.reverse (ws'.get! 0) ++ B64.reverse (ws'.get! 1)) ++
    (B64.reverse (ws'.get! 2) ++ B64.reverse (ws'.get! 3))

def ByteArray.run (bnd n : Nat) (wc : Fin 17) (bs : ByteArray) (ws : Array B64) : B256 :=
  if 7 < n then
    let b0 : B8 := bs.get! (bnd - n)
    let b1 : B8 := bs.get! (bnd - (n - 1))
    let b2 : B8 := bs.get! (bnd - (n - 2))
    let b3 : B8 := bs.get! (bnd - (n - 3))
    let b4 : B8 := bs.get! (bnd - (n - 4))
    let b5 : B8 := bs.get! (bnd - (n - 5))
    let b6 : B8 := bs.get! (bnd - (n - 6))
    let b7 : B8 := bs.get! (bnd - (n - 7))
    let t : B64 := B8s.toB64 b7 b6 b5 b4 b3 b2 b1 b0
    let ws' := Array.app wc (UInt64.xor · t) ws
    ByteArray.run bnd (n - 8) (wc + 1) bs <|
      if wc = 16 then (f B64.rdnc ws' B64.rol) else ws'
  else
    let rec aux (bnd : Nat) (bs : ByteArray) : Nat → Nat → List B8
      | _, 0 => [] -- unreachable code
      | 0, n + 1 => 1 :: List.replicate n 0
      | m + 1, n + 1 =>
        (bs.get! (bnd - (m + 1))) :: aux bnd bs m n
    let us := aux bnd bs n 8
    let t : B64 :=
      B8s.toB64
        (us.getD 7 0)
        (us.getD 6 0)
        (us.getD 5 0)
        (us.getD 4 0)
        (us.getD 3 0)
        (us.getD 2 0)
        (us.getD 1 0)
        (us.getD 0 0)
    let s : B64 := (8 : B64) <<< 60
    let temp0 := Array.app wc (· ^^^ t) ws
    let temp1 := Array.app 16 (· ^^^ s) temp0
    let ws' := f B64.rdnc temp1 B64.rol
    (B64.reverse (ws'.get! 0) ++ B64.reverse (ws'.get! 1)) ++
    (B64.reverse (ws'.get! 2) ++ B64.reverse (ws'.get! 3))

end KECCAK

def Bytes.keccak (bs : Bytes) : Word :=
  KECCAK.Bytes.run (0 : Fin 17) bs <| .mkArray 25 <| .zero 64

def B8L.keccak (bs : B8L) : B256 :=
  KECCAK.B8L.run (0 : Fin 17) bs <| .mkArray 25 0

def ByteArray.keccak (loc sz : Nat) (bs : ByteArray) : B256 :=
  KECCAK.ByteArray.run (loc + sz) sz (0 : Fin 17) bs <| .mkArray 25 0

def String.keccak (s : String) : Word :=
  Bytes.keccak s.toBytes
