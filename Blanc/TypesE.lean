-- Types.lean : types used by both executable and abstract semantics of EVM and Blanc.

import Blanc.BasicE

structure Adr : Type where
  (high : B32)
  (mid : B64)
  (low : B64)
deriving DecidableEq

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

def Adr.ordering : Adr → Adr → Ordering
  | ⟨xh, xm, xl⟩, ⟨yh, ym, yl⟩ =>
    match compare xh yh with
    | .eq =>
      match compare xm ym with
      | .eq => compare xl yl
      | o => o
    | o => o

instance : Ord Adr := ⟨Adr.ordering⟩

def Adr.toHex (a : Adr) : String :=
  a.high.toHex ++ a.mid.toHex ++ a.low.toHex

instance : ToString Adr := ⟨Adr.toHex⟩

def String.dropZeroes (s : String) : String :=
  match ⟨s.data.dropWhile (· == '0')⟩ with
  | "" => "0"
  | s => s

abbrev Stor := Lean.RBMap B256 B256 compare

def Stor.toStrings (s : Stor) : List String :=
  let kvs := s.toArray.toList
  let kvToStrings : B256 × B256 → List String :=
    λ nb => [s!"0x{(B256.toHex nb.fst).dropZeroes} : 0x{(B256.toHex nb.snd).dropZeroes}"]
  fork "STOR" (kvs.map kvToStrings)

instance : ToString Stor := ⟨String.joinln ∘ Stor.toStrings⟩

structure Acct where
  (nonce : B64)
  (bal : B256)
  (stor : Stor)
  (code : ByteArray)

def Acct.toStrings (s : String) (a : Acct) : List String :=
  let codeStrings : List String :=
    let xs := a.code.toList
    let sz := xs.length
    if sz = 0 then
      []
    else if sz ≤ 32 then
      [s!"{B8L.toHex xs} ({sz} bytes)"]
    else
      [s!"{B8L.toHex (xs.take 32)}... ({sz} bytes)"]

  fork s [
    [s!"BAL : 0x{a.bal.toHex.dropZeroes}"],
    [s!"NONCE : 0x{a.nonce.toHex.dropZeroes}"],
    --longB8LToStrings "code" a.code.toList,
    --fork "CODE" [String.chunks 64 <| B8L.toHex a.code.toList],
    fork "CODE" [codeStrings],
    a.stor.toStrings
  ]

instance : ToString Acct := ⟨fun a => String.joinln (Acct.toStrings "account" a)⟩
def B8L.toAdr? : B8L → Option Adr
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

def Hex.toAdr? (hx : String) : Option Adr := Hex.toB8L hx >>= B8L.toAdr?

def Adr.toB8L (a : Adr) : B8L :=
  a.high.toB8L ++ a.mid.toB8L ++ a.low.toB8L

inductive Rinst : Type
  | add -- 0x01 / 2 / 1 / addition operation.
  | mul -- 0x02 / 2 / 1 / multiplication operation.
  | sub -- 0x03 / 2 / 1 / subtraction operation.
  | div -- 0x04 / 2 / 1 / integer division operation.
  | sdiv -- 0x05 / 2 / 1 / signed integer division operation.
  | mod -- 0x06 / 2 / 1 / modulo operation.
  | smod -- 0x07 / 2 / 1 / signed modulo operation.
  | addmod -- 0x08 / 3 / 1 / modulo addition operation.
  | mulmod -- 0x09 / 3 / 1 / modulo multiplication operation.
  | exp -- 0x0A / 2 / 1 / exponentiation operation.
  | signextend -- 0x0B / 2 / 1 / sign extend operation.
  | lt -- 0x10 / 2 / 1 / less-than comparison.
  | gt -- 0x11 / 2 / 1 / greater-than comparison.
  | slt -- 0x12 / 2 / 1 / signed less-than comparison.
  | sgt -- 0x13 / 2 / 1 / signed greater-than comparison.
  | eq -- 0x14 / 2 / 1 / equality comparison.
  | iszero -- 0x15 / 1 / 1 / tests if the input is zero.
  | and -- 0x16 / 2 / 1 / bitwise and operation.
  | or -- 0x17 / 2 / 1 / bitwise or operation.
  | xor -- 0x18 / 2 / 1 / bitwise xor operation.
  | not -- 0x19 / 1 / 1 / bitwise not operation.
  | byte -- 0x1A / 2 / 1 / retrieve a single Byte from a Word.
  | shr -- 0x1B / 2 / 1 / logical shift right operation.
  | shl -- 0x1C / 2 / 1 / logical shift left operation.
  | sar -- 0x1D / 2 / 1 / arithmetic (signed) shift right operation.
  | kec -- 0x20 / 2 / 1 / compute Keccak-256 hash.
  | address -- 0x30 / 0 / 1 / Get the Addr of the currently executing account.
  | balance -- 0x31 / 1 / 1 / Get the balance of the specified account.
  | origin -- 0x32 / 0 / 1 / Get the Addr that initiated the current transaction.
  | caller -- 0x33 / 0 / 1 / Get the Addr that directly called the currently executing contract.
  | callvalue -- 0x34 / 0 / 1 / Get the value (in wei) sent with the current transaction.
  | calldataload -- 0x35 / 1 / 1 / Load input data from the current transaction.
  | calldatasize -- 0x36 / 0 / 1 / Get the size of the input data from the current transaction.
  | calldatacopy -- 0x37 / 3 / 0 / Copy input data from the current transaction to Memory.
  | codesize -- 0x38 / 0 / 1 / Get the size of the code of the currently executing contract.
  | codecopy -- 0x39 / 3 / 0 / Copy the code of the currently executing contract to memory.
  | gasprice -- 0x3a / 0 / 1 / Get the gas price of the current transaction.
  | extcodesize -- 0x3B / 1 / 1 / Get the size of the code of an external account.
  | extcodecopy -- 0x3C / 4 / 0 / Copy the code of an external account to memory.
  | retdatasize -- 0x3D / 0 / 1 / Get the size of the output data from the previous call.
  | retdatacopy -- 0x3E / 3 / 0 / Copy output data from the previous call to memory.
  | extcodehash -- 0x3F / 1 / 1 / Get the code hash of an external account.
  | blockhash -- 0x40 / 1 / 1 / get the hash of the specified block.
  | coinbase -- 0x41 / 0 / 1 / get the Addr of the current block's miner.
  | timestamp -- 0x42 / 0 / 1 / get the timestamp of the current block.
  | number -- 0x43 / 0 / 1 / get the current block number.
  | prevrandao -- 0x44 / 0 / 1 / get the latest RANDAO mix of the post beacon state of the previous block.
  | gaslimit -- 0x45 / 0 / 1 / get the gas limit of the current block.
  | chainid -- 0x46 / 0 / 1 / get the chain id of the current blockchain.
  | selfbalance -- 0x47 / 0 / 1 / get the balance of the currently executing account.
  | basefee -- 0x48 / 0 / 1 / get the current block's base fee.
  | blobhash -- 0x49 / 1 / 1 /
  | blobbasefee -- 0x4A / 0 / 1 / get the current block's blob base fee.
  | pop -- 0x50 / 1 / 0 / Remove an item from the Stack.
  | mload -- 0x51 / 1 / 1 / Load a Word from memory.
  | mstore -- 0x52 / 2 / 0 / Store a Word in memory.
  | mstore8 -- 0x53 / 2 / 0 / store a Byte in memory.
  | sload -- 0x54 / 1 / 1 / load a word from storage.
  | sstore -- 0x55 / 2 / 0 / store a word in storage.
  | tload -- 0x5C / 1 / 1 / load a word from transient torage.
  | tstore -- 0x5D / 2 / 0 / store a word in transient storage.
  | mcopy -- 0x5E / 3 / 0 /
  | pc -- 0x58 / 0 / 1 / Get the current program counter value.
  | msize -- 0x59 / 0 / 1 / Get the size of the memory.
  | gas -- 0x5a / 0 / 1 / Get the amount of remaining gas.
  | dup : Fin 16 → Rinst
  | swap : Fin 16 → Rinst
  | log : Fin 5 → Rinst
-- deriving DecidableEq

inductive Jinst : Type
  | jump -- 0x56 / 1 / 0 / Unconditional jump.
  | jumpi -- 0x57 / 2 / 0 / Conditional jump.
  | jumpdest -- 0x5b / 0 / 0 / Mark a valid jump destination.
deriving DecidableEq

inductive Xinst : Type
  | create -- 0xf0 / 3 / 1 / Create a new contract account.
  | call -- 0xf1 / 7 / 1 / Call an existing account, which can be either a contract or a non-contract account.
  | callcode -- 0xf2 / 7 / 1 / Call an existing contract's code using the current contract's Storage and Addr.
  | delcall -- 0xf4 / 6 / 1 / Call an existing contract's code using the current contract's Storage and the calling contract's Addr and value.
  | create2 -- 0xf5 / 4 / 1 / Create a new contract account at a deterministic Addr using a salt value.
  | statcall -- 0xfa / 6 / 1 / Perform a read-only call to an existing contract.
deriving DecidableEq

inductive Linst : Type
  | stop -- 0x00 / 0 / 0 / halts execution.
  | ret -- 0xf3 / 2 / 0 / Halt execution and return output data.
  | rev -- 0xfd / 2 / 0 / Halt execution and revert State changes, returning output data.
  | dest -- 0xff / 1 / 0 / Halt execution and destroy the current contract, transferring remaining Ether to a specified Addr.
  -- | invalid -- 0xFE / 0 / 0 / Designated invalid instruction.
deriving DecidableEq


def Rinst.toString : Rinst → String
  | add => "ADD"
  | mul => "MUL"
  | sub => "SUB"
  | div => "DIV"
  | sdiv => "SDIV"
  | mod => "MOD"
  | smod => "SMOD"
  | addmod => "ADDMOD"
  | mulmod => "MULMOD"
  | exp => "EXP"
  | signextend => "SIGNEXTEND"
  | lt => "LT"
  | gt => "GT"
  | slt => "SLT"
  | sgt => "SGT"
  | eq => "EQ"
  | iszero => "ISZERO"
  | and => "AND"
  | or => "OR"
  | xor => "XOR"
  | not => "NOT"
  | byte => "BYTE"
  | shr => "SHR"
  | shl => "SHL"
  | sar => "SAR"
  | kec => "KEC"
  | address => "ADDRESS"
  | balance => "BALANCE"
  | origin => "ORIGIN"
  | caller => "CALLER"
  | callvalue => "CALLVALUE"
  | calldataload => "CALLDATALOAD"
  | calldatasize => "CALLDATASIZE"
  | calldatacopy => "CALLDATACOPY"
  | codesize => "CODESIZE"
  | codecopy => "CODECOPY"
  | gasprice => "GASPRICE"
  | extcodesize => "EXTCODESIZE"
  | extcodecopy => "EXTCODECOPY"
  | retdatasize => "RETDATASIZE"
  | retdatacopy => "RETDATACOPY"
  | extcodehash => "EXTCODEHASH"
  | blockhash => "BLOCKHASH"
  | coinbase => "COINBASE"
  | timestamp => "TIMESTAMP"
  | number => "NUMBER"
  | prevrandao => "PREVRANDAO"
  | gaslimit => "GASLIMIT"
  | chainid => "CHAINID"
  | selfbalance => "SELFBALANCE"
  | basefee => "BASEFEE"
  | blobhash => "BLOBHASH"
  | blobbasefee => "BLOBBASEFEE"
  | pop => "POP"
  | mload => "MLOAD"
  | mstore => "MSTORE"
  | mstore8 => "MSTORE8"
  | sload => "SLOAD"
  | sstore => "SSTORE"
  | tload => "TLOAD"
  | tstore => "TSTORE"
  | mcopy => "MCOPY"
  | pc => "PC"
  | msize => "MSIZE"
  | gas => "GAS"
  | dup n => "DUP" ++ n.val.repr
  | swap n => "SWAP" ++ n.val.repr
  | log n => "LOG" ++ n.val.repr

def Xinst.toString : Xinst → String
  | create => "CREATE"
  | call => "CALL"
  | callcode => "CALLCODE"
  | delcall => "DELEGATECALL"
  | create2 => "CREATE2"
  | statcall => "STATICCALL"

def Linst.toString : Linst → String
  | .stop => "STOP"
  | .dest => "SELFDESTRUCT"
  | .rev => "REVERT"
  | .ret => "RETURN"
  -- | .invalid => "INVALID"

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
  | 0x48 => some .basefee -- 0x48 / 0 / 1 /
  | 0x49 => some .blobhash -- 0x49 / 1 / 1 /
  | 0x4A => some .blobbasefee -- 0x4A / 0 / 1 /
  | 0x50 => some .pop -- 0x50 / 1 / 0 / Remove an item from the stack.
  | 0x51 => some .mload -- 0x51 / 1 / 1 / Load a word from memory.
  | 0x52 => some .mstore -- 0x52 / 2 / 0 / Store a word in memory.
  | 0x53 => some .mstore8 -- 0x53 / 2 / 0 / Store a byte in memory.
  | 0x54 => some .sload -- 0x54 / 1 / 1 / Load a word from storage.
  | 0x55 => some .sstore -- 0x55 / 2 / 0 / Store a word in storage.
  | 0x58 => some .pc -- 0x58 / 0 / 1 / Get the current program counter value.
  | 0x59 => some .msize -- 0x59 / 0 / 1 / Get the size of the memory.
  | 0x5a => some .gas -- 0x5a / 0 / 1 / Get the amount of remaining gas.
  | 0x5C => some .tload -- 0x54 / 1 / 1 / Load a word from storage.
  | 0x5D => some .tstore -- 0x55 / 2 / 0 / Store a word in storage.
  | 0x5E => some .mcopy -- 0x55 / 2 / 0 / Store a word in storage.
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
  | _ => none

def Linst.toB8 : Linst → B8
  | .stop => 0x00
  | .ret => 0xF3
  | .rev => 0xFD
  | .dest => 0xFF

def Jinst.toB8 : Jinst → B8
  | jump => 0x56     -- 0x56 / 1 / 0 / Unconditional jump.
  | jumpi => 0x57    -- 0x57 / 2 / 0 / Conditional jump.
  | jumpdest => 0x5B -- 0x5b / 0 / 0 / Mark a valid jump destination.

instance : Repr Rinst := ⟨λ o _ => o.toString⟩
instance : Repr Xinst := ⟨λ o _ => o.toString⟩

def Jinst.toString : Jinst → String
  | .jump => "JUMP"
  | .jumpdest => "JUMPDEST"
  | .jumpi => "JUMPI"
