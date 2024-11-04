
/- First, let's define our basic types and constants -/
def Byte := UInt8
def Word64 := UInt64

structure SHA3Context where
  state : Array Word64 := mkArray 25 0
  wordIndex : Nat := 0
  byteIndex : Nat := 0
  saved : Word64 := 0
deriving Inhabited

def KECCAK_ROUNDS : Nat := 24

/- Round constants -/
def keccakf_rndc : Array Word64 := #[
  0x0000000000000001, 0x0000000000008082,
  0x800000000000808a, 0x8000000080008000,
  0x000000000000808b, 0x0000000080000001,
  0x8000000080008081, 0x8000000000008009,
  0x000000000000008a, 0x0000000000000088,
  0x0000000080008009, 0x000000008000000a,
  0x000000008000808b, 0x800000000000008b,
  0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080,
  0x000000000000800a, 0x800000008000000a,
  0x8000000080008081, 0x8000000000008080,
  0x0000000080000001, 0x8000000080008008
]

def keccakf_rotc : Array Nat := #[
  1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14,
  27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44
]

def keccakf_piln : Array Nat := #[
  10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4,
  15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1
]

/- Helper functions -/
def rotl64 (x : Word64) (y : Nat) : Word64 :=
  (x <<< y.toUInt64) ||| (x >>> (64 - y).toUInt64)

/- Core Keccak-f function -/
def keccakf (s : Array Word64) : Array Word64 := Id.run do
  let mut state := s
  let mut bc := mkArray 5 (0 : Word64)

  for round in [:KECCAK_ROUNDS] do
    -- Theta
    for i in [:5] do
      bc := bc.set! i (state[i] ^^^ state[i + 5] ^^^ state[i + 10] ^^^ state[i + 15] ^^^ state[i + 20])

    for i in [:5] do
      let t := bc[(i + 4) % 5] ^^^ rotl64 bc[(i + 1) % 5] 1
      for j in [0:25:5] do
        state := state.set! (j + i) (state[j + i] ^^^ t)

    -- Rho Pi
    let mut t := state[1]
    for i in [:24] do
      let j := keccakf_piln[i]
      let bc0 := state[j]
      state := state.set! j (rotl64 t keccakf_rotc[i])
      t := bc0

    -- Chi
    for j in [0:25:5] do
      for i in [:5] do
        bc := bc.set! i state[j + i]
      for i in [:5] do
        state := state.set! (j + i) (state[j + i] ^^^ (~~~bc[(i + 1) % 5] &&& bc[(i + 2) % 5]))

    -- Iota
    state := state.set! 0 (state[0] ^^^ keccakf_rndc[round])

  return state

/- Main hash function -/
def keccak256 (input : List Byte) : Array Byte := Id.run do
  let mut ctx := SHA3Context.mk

  -- Process input in chunks
  let mut i := 0
  while i + 8 ≤ input.length do
    let chunk := input.drop i |>.take 8
    let word := chunk.foldl (fun acc b => acc ||| ((b.toUInt64 <<< (8 * (i % 8)).toUInt64))) 0
    ctx := { ctx with
      state := ctx.state.set! ctx.wordIndex (ctx.state[ctx.wordIndex] ^^^ word),
      wordIndex := (ctx.wordIndex + 1) % 17
    }
    if ctx.wordIndex == 0 then
      ctx := { ctx with state := keccakf ctx.state }
    i := i + 8

  -- Process remaining bytes
  let remaining := input.drop i
  let mut saved := ctx.saved
  let mut byteIndex := ctx.byteIndex
  for b in remaining do
    saved := saved ||| (b.toUInt64 <<< (byteIndex * 8).toUInt64)
    byteIndex := byteIndex + 1

  -- Finalization
  let t := 1.toUInt64 <<< (byteIndex * 8).toUInt64
  ctx := { ctx with
    state := ctx.state.set! ctx.wordIndex (ctx.state[ctx.wordIndex] ^^^ saved ^^^ t),
    state := ctx.state.set! 16 (ctx.state[16] ^^^ 0x8000000000000000)
  }

  let finalState := keccakf ctx.state

  -- Convert to bytes
  let mut result := mkArray 32 (0 : Byte)
  for i in [:16] do
    let word := finalState[i]
    for j in [:8] do
      result := result.set! (i * 8 + j) ((word >>> (j * 8).toUInt64).toUInt8)

  return result
