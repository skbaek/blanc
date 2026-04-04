-- Semantics.lean : formalized semantics of the EVM and Blanc


import Blanc.Basic
import Elevm.Hash
import Elevm.Execution
def Rinst.toB8 : Rinst → B8
  | add          => 0x01
  | mul          => 0x02
  | sub          => 0x03
  | div          => 0x04
  | sdiv         => 0x05
  | mod          => 0x06
  | smod         => 0x07
  | addmod       => 0x08
  | mulmod       => 0x09
  | exp          => 0x0A
  | signextend   => 0x0B
  | lt           => 0x10
  | gt           => 0x11
  | slt          => 0x12
  | sgt          => 0x13
  | eq           => 0x14
  | iszero       => 0x15
  | and          => 0x16
  | or           => 0x17
  | xor          => 0x18
  | not          => 0x19
  | byte         => 0x1A
  | shl          => 0x1B
  | shr          => 0x1C
  | sar          => 0x1D
  | kec          => 0x20
  | address      => 0x30
  | balance      => 0x31
  | origin       => 0x32
  | caller       => 0x33
  | callvalue    => 0x34
  | calldataload => 0x35
  | calldatasize => 0x36
  | calldatacopy => 0x37
  | codesize     => 0x38
  | codecopy     => 0x39
  | gasprice     => 0x3A
  | extcodesize  => 0x3B
  | extcodecopy  => 0x3C
  | retdatasize  => 0x3D
  | retdatacopy  => 0x3E
  | extcodehash  => 0x3F
  | blockhash    => 0x40
  | coinbase     => 0x41
  | timestamp    => 0x42
  | number       => 0x43
  | prevrandao   => 0x44
  | gaslimit     => 0x45
  | chainid      => 0x46
  | selfbalance  => 0x47
  | basefee      => 0x48
  | blobhash     => 0x49
  | blobbasefee  => 0x4A
  | pop          => 0x50
  | mload        => 0x51
  | mstore       => 0x52
  | mstore8      => 0x53
  | sload        => 0x54
  | sstore       => 0x55
  | pc           => 0x58
  | msize        => 0x59
  | gas          => 0x5A
  | tload        => 0x5C
  | tstore       => 0x5D
  | mcopy        => 0x5E
  | dup n        => 0x80 + n.val.toUInt8
  | swap n       => 0x90 + n.val.toUInt8
  | log n        => 0xA0 + n.val.toUInt8

def Memory : Type := B256 → B8
def Storage : Type := B256 → B256
abbrev Balances : Type := Adr → B256
abbrev Storages : Type := Adr → Storage
abbrev Codes : Type := Adr → B8L

structure Env where
  (cta : Adr) -- contract address (YP : a)
  (oga : Adr) -- origin address (YP : o)
  (gpr : B256) -- gas price (YP : p)
  (cld : B8L) -- calldata (YP : d)
  (cla : Adr) -- caller Adr (YP : s)
  (clv : B256) -- callvalue (YP : v)
  (code : B8L) -- contract code  (YP : b)
  (exd : Nat) -- execution depth (YP : e)
  (wup : Bool) -- World-State update permission (YP : w)

structure World where
  (bal : Balances)
  (stor : Storages)
  (code : Codes)

abbrev Stack : Type := List B256

def Stack.Push (x y xy : Stack) : Prop := x <++ xy ++> y
def Stack.Pop (x xy y : Stack) : Prop := x <++ xy ++> y
def Stack.Diff (xs zs : Stack) (s s'' : Stack) : Prop :=
  ∃ s' : Stack, Pop xs s s' ∧ Push zs s' s''

def Stack.SwapCore (x y : B256) : Nat → Stack → Stack → Prop
  | 0, y' :: xs, x' :: xs' => x = x' ∧ y = y' ∧ xs = xs'
  | n + 1, z :: xs, z' :: xs' => z = z' ∧ SwapCore x y n xs xs'
  | _, _, _ => False

def Stack.Swap (n : Nat) : Stack → Stack → Prop
  | x :: xs, y :: xs' => SwapCore x y n xs xs'
  | _, _ => False

inductive Stack.Nth : Nat → B256 → Stack → Prop
  | head : ∀ x xs, Nth 0 x (x :: xs)
  | tail : ∀ m x y xs, Nth m x xs → Nth (m + 1) x (y :: xs)

def Stack.Dup (n : Nat) (s s' : Stack) : Prop := ∃ x, Push [x] s s' ∧ Stack.Nth n x s

structure Desc where
  -- balance, storage, & code : parts of the world state
  (bal : Adr → B256)
  (stor : Adr → Storage)
  (code : Adr → B8L)
  -- stack, memory, & return data from last call: parts of the machine state
  (stk : Stack)
  (mem : Memory)
  (ret : B8L)
  -- addresses marked for destruction : part of the substate
  (dest : List Adr)

-- Q : should 'ret' (the 'return buffer' part of machine State) be represented by an
-- option type, such that the last field of structure above is (r : Option B8L) instead?
-- At a cursory glance this seems to be the case, since YP discusses varions edge cases
-- where o = ∅. But upon closer inspection, it seems '∅' is always an intermediate
-- helper term for defining how the return buffer should be updated in edge cases, but
-- never a final value that the return buffer is updated *to*. In other B256s, there are
-- parts that say "if the code execution Result is o = ∅, then do this..." but never any
-- case that says "the return beffer is o = ∅ at the end of the transition". Therefore,
-- it seems safe to assume that the return buffer is always a definite List of Bytes at
-- any given moment, and there is no need to use an option type.
--
-- Related Q : what should be the initial value for the return buffer, at the beginning
-- of a code execution? YP does not specify this, but it seems reasonable to assume it
-- is an empty Byte array of length 0. (Confirm this from other sources if possible)

structure Result where
  -- balance, Storage, & code : parts of the 'World-State'
  (bal : Adr → B256)
  (stor : Adr → Storage)
  (code : Adr → B8L)
  -- ret : similar to 'ret' of State, but this is the Byte
  -- sequence returned at the end of a code execution
  (ret : B8L)
  -- List of Adres earmarke for destruction : parts of the 'subState'
  (dest : List Adr)



-- operational semantics

-- "slice xs x y ys" and "sliceFill xs x y ys" are two different
-- ways to denote that ys is a slice of Bytes ocurring in Byte sequence xs,
-- beginning at position x with length y. The former is strict and implies
-- all of ys actually occurs in xs at the exact positions, whereas the latter
-- is flexible and implies every z ∈ ys is either
--
--   (1) actually in xs at the specified position, or
--   (2) the position is out-of-bounds in xs, and z = 0
--
-- YP is often unclear which shall be used. We default to sliceFill,
-- and only use slice when YP explicitly States out-of-bounds reads
-- should revert.

-- This definition of memory slice allows looping around the
-- maximum address 2^256 - 1. It seems that this is the natural
-- interpretation of YP which doesn't mention address overflow,
-- and in any case it shouldn't be a practical concern since
-- 2^256 bytes will never be allocated, but it would be good to
-- double-check it is indeed correct.

def Memory.slice' : Memory → B256 → Nat → B8L
  | _, _, 0 => []
  | m, x, n + 1 => m x :: slice' m (x + 1) n

def Memory.slice (m : Memory) (x y : B256) : B8L := slice' m x y.toNat

def Memory.store (x : B256) : B8L → Memory → Memory
  | [], m => m
  | b :: bs, m =>
    let m' := store (x + 1) bs m
    λ y => if x = y then b else m' y

def Memory.init : Memory := λ _ => 0

-- def Mstored (x : B256) (bs : B8L) (m m' : Memory) : Prop := m' = Memory.store x bs m

def Decrease (k : Adr) (v : B256) (f g : Adr → B256) : Prop :=
  Frel k (λ x y => x - v = y) f g

def Increase (k : Adr) (v : B256) (f g : Adr → B256) : Prop :=
  Frel k (λ x y => x + v = y) f g

def Transfer
    (b : Adr → B256)
    (kd : Adr) (v : B256) (ki : Adr)
    (d : Adr → B256) : Prop :=
    v ≤ b kd ∧
  ∃ c : Adr → B256,
    Decrease kd v b c ∧
    Increase ki v c d

structure Evm.Rels where
  -- (pc : Nat → Nat → Prop)
  (stack : List B256 → List B256 → Prop)
  (memory : Mem → Mem → Prop)
  (code : ByteArray → ByteArray → Prop)
  -- (gasLeft : Nat → Nat → Prop)
  (logs : List Log → List Log → Prop)
  -- (refundCounter : Int → Int → Prop)
  (msg : Msg → Msg → Prop)
  (output : B8L → B8L → Prop)
  -- (accountsToDelete : AdrSet → AdrSet → Prop)
  (returnData : B8L → B8L → Prop)
  (error : Option String → Option String → Prop)
  -- (accessedAddresses : AdrSet → AdrSet → Prop)
  -- (accessedStorageKeys : KeySet → KeySet → Prop)

def Evm.Rels.equiv : Evm.Rels where
  -- pc := Eq
  stack := Eq
  memory := Eq
  code := Eq
  -- gasLeft := Eq
  logs := Eq
  -- refundCounter := Eq
  msg := Eq
  output := Eq
  -- accountsToDelete := Eq
  returnData := Eq
  error := Eq
  -- accessedAddresses := Eq
  -- accessedStorageKeys := Eq

structure Evm.Rel (rels : Evm.Rels) (evm evm' : Evm) : Prop where
  -- (pc : rels.pc evm.pc evm'.pc)
  (stack : rels.stack evm.stack evm'.stack)
  (memory : rels.memory evm.memory evm'.memory)
  (code : rels.code evm.code evm'.code)
  -- (gasLeft : rels.gasLeft evm.gasLeft evm'.gasLeft)
  (logs : rels.logs evm.logs evm'.logs)
  -- (refundCounter : rels.refundCounter evm.refundCounter evm'.refundCounter)
  (msg : rels.msg evm.msg evm'.msg)
  (output : rels.output evm.output evm'.output)
  -- ( accountsToDelete :
  --   rels.accountsToDelete evm.accountsToDelete evm'.accountsToDelete)
  (returnData : rels.returnData evm.returnData evm'.returnData)
  (error : rels.error evm.error evm'.error)
  -- ( accessedAddresses :
  --   rels.accessedAddresses evm.accessedAddresses evm'.accessedAddresses )
  -- ( accessedStorageKeys :
  --   rels.accessedStorageKeys evm.accessedStorageKeys evm'.accessedStorageKeys )

def Evm.Diff (xs ys : List B256) : Evm → Evm → Prop :=
  Rel {Rels.equiv with stack := Stack.Diff xs ys}

def Evm.Push (xs : List B256) : Evm → Evm → Prop :=
  Rel {Rels.equiv with stack := Stack.Push xs}

def Evm.Pop (xs : List B256) : Evm → Evm → Prop :=
  Rel {Rels.equiv with stack := Stack.Pop xs}

def Evm.Swap (n : Nat) : Evm → Evm → Prop :=
  Rel {Rels.equiv with stack := Stack.Swap n}

def Evm.Dup (n : Nat) : Evm → Evm → Prop :=
  Rel {Rels.equiv with stack := Stack.Dup n}

def Evm.Add (evm evm' : Evm) : Prop :=  ∃ x y, Evm.Diff [x, y] [x + y] evm evm'
def Evm.Sub (evm evm' : Evm) : Prop :=  ∃ x y, Evm.Diff [x, y] [x - y] evm evm'
def Evm.Mul (evm evm' : Evm) : Prop := ∃ x y, Evm.Diff [x, y] [x * y] evm evm'
def Evm.Div (evm evm' : Evm) : Prop := ∃ x y, Evm.Diff [x, y] [x / y] evm evm'
def Evm.Mod (evm evm' : Evm) : Prop := ∃ x y, Evm.Diff [x, y] [x % y] evm evm'
def Evm.Sdiv (evm evm' : Evm) : Prop := ∃ x y, Evm.Diff [x, y] [B256.sdiv x y] evm evm'
def Evm.Smod (evm evm' : Evm) : Prop := ∃ x y, Evm.Diff [x, y] [B256.smod x y] evm evm'
def Evm.Addmod (evm evm' : Evm) : Prop := ∃ x y z, Evm.Diff [x, y, z] [B256.addmod x y z] evm evm'
def Evm.Mulmod (evm evm' : Evm) : Prop := ∃ x y z, Evm.Diff [x, y, z] [B256.mulmod x y z] evm evm'
def Evm.Exp (evm evm' : Evm) : Prop := ∃ x y, Evm.Diff [x, y] [x ^ y] evm evm'

--def Desc.Add (s s' : Desc) : Prop :=  ∃ x y, Evm.Diff [x, y] [x + y] s s'
--def Desc.Sub (s s' : Desc) : Prop :=  ∃ x y, Evm.Diff [x, y] [x - y] s s'
--def Desc.Mul (s s' : Desc) : Prop := ∃ x y, Evm.Diff [x, y] [x * y] s s'
--def Desc.Div (s s' : Desc) : Prop := ∃ x y, Evm.Diff [x, y] [x / y] s s'
--def Desc.Mod (s s' : Desc) : Prop := ∃ x y, Evm.Diff [x, y] [x % y] s s'
--def Desc.Sdiv (s s' : Desc) : Prop := ∃ x y, Evm.Diff [x, y] [B256.sdiv x y] s s'
--def Desc.Smod (s s' : Desc) : Prop := ∃ x y, Evm.Diff [x, y] [B256.smod x y] s s'
--def Desc.Addmod (s s' : Desc) : Prop := ∃ x y z, Evm.Diff [x, y, z] [B256.addmod x y z] s s'
--def Desc.Mulmod (s s' : Desc) : Prop := ∃ x y z, Evm.Diff [x, y, z] [B256.mulmod x y z] s s'
--def Desc.Exp (s s' : Desc) : Prop := ∃ x y, Evm.Diff [x, y] [x ^ y] s s'

def Evm.Signextend (s s' : Evm) : Prop :=
  ∃ x y z,
    Evm.Diff [x, y] [z] s s' ∧
    B256.signext x y = z

infix:70 " <? "  => B256.lt_check
infix:70 " >? "  => B256.gt_check
infix:70 " ±<? " => B256.slt_check
infix:70 " ±>? " => B256.sgt_check
infix:70 " =? "  => B256.eq_check

def Char.toB8 (c : Char) : B8 := Nat.toUInt8 c.toNat
def String.toB8L (s : String) : B8L := s.data.map Char.toB8

def Mem.slice (μ : Mem) (x y : B256) : B8L := μ.data.sliceD x.toNat y.toNat 0

def B8L.Size (bs : B8L) (sz : B256) : Prop := bs.length = sz.toNat
def String.keccak (s : String) : B256 := s.toB8L.keccak

def Evm.Lt (s s' : Evm) : Prop := ∃ x y, Evm.Diff [x, y] [x <? y] s s'
def Evm.Gt (s s' : Evm) : Prop := ∃ x y, Evm.Diff [x, y] [x >? y] s s'
def Evm.Slt (s s' : Evm) : Prop := ∃ x y, Evm.Diff [x, y] [x ±<? y] s s'
def Evm.Sgt (s s' : Evm) : Prop := ∃ x y, Evm.Diff [x, y] [x ±>? y] s s'
def Evm.Eq (s s' : Evm) : Prop := ∃ x y, Evm.Diff [x, y] [x =? y] s s'
def Evm.Iszero (s s' : Evm) : Prop := ∃ x, Evm.Diff [x] [x =? 0] s s'
def Evm.And (s s' : Evm) : Prop := ∃ x y, Evm.Diff [x, y] [x &&& y] s s'
def Evm.Or (s s' : Evm) : Prop := ∃ x y, Evm.Diff [x, y] [x ||| y] s s'
def Evm.Xor (s s' : Evm) : Prop := ∃ x y, Evm.Diff [x, y] [x ^^^ y] s s'
def Evm.Not (s s' : Evm) : Prop := ∃ x, Evm.Diff [x] [~~~ x] s s'
def Evm.Byte (s s' : Evm) : Prop :=
  ∃ (x y : B256),
    Evm.Diff [x, y] [(List.getD y.toB8L x.toNat 0).toB256] s s'
def Evm.Shl (s s' : Evm) : Prop := ∃ x y, Evm.Diff [x, y] [y <<< x.toNat] s s'
def Evm.Shr (s s' : Evm) : Prop := ∃ x y, Evm.Diff [x, y] [y >>> x.toNat] s s'
def Evm.Sar (s s' : Evm) : Prop := ∃ x y, Evm.Diff [x, y] [B256.arithShiftRight y x.toNat] s s'
def Evm.Kec (s s' : Evm) : Prop :=
  ∃ x y, Evm.Diff [x, y] [(s.memory.slice x y).keccak] s s'
def Evm.Adress (s s' : Evm) : Prop := Evm.Push [Adr.toB256 s.contract] s s'
def Evm.Balance (s s' : Evm) : Prop :=
  ∃ x : B256, Evm.Diff [x] [s.getBal x.toAdr] s s'
def Evm.Origin (s s' : Evm) : Prop := Evm.Push [s.msg.tenv.origin.toB256] s s'
def Evm.Caller (s s' : Evm) : Prop := Evm.Push [s.msg.caller.toB256] s s'
def Evm.Callvalue (s s' : Evm) : Prop := Evm.Push [s.msg.value] s s'
def Evm.Calldatasize (s s' : Evm) : Prop :=
  Evm.Push [s.msg.data.length.toB256] s s'
def Evm.Codesize (s s' : Evm) : Prop :=
  Evm.Push [s.msg.code.size.toB256] s s'
def Evm.Gasprice (s s' : Evm) : Prop :=
  Evm.Push [s.msg.tenv.gasPrice.toB256] s s'
def Evm.Extcodesize (s s' : Evm) : Prop :=
  ∃ x, Evm.Diff [x] [(s.getCode x.toAdr).size.toB256] s s'
def Evm.Retdatasize (s s' : Evm) : Prop :=
  Evm.Push [s.returnData.length.toB256] s s'
def Evm.Extcodehash (s s' : Evm) : Prop :=
  ∃ x : B256,
    let account := s.getAcct x.toAdr
    let codehash : B256 :=
      if account.Empty then 0
      else ByteArray.keccak 0 account.code.size account.code
    Evm.Diff [x] [codehash] s s'


-- def Desc.Extcodehash (s s' : Evm) : Prop :=
--   let codehash : B256 :=
--     if account.Empty then 0
--       else ByteArray.keccak 0 account.code.size account.code
--   ∃ x y,
--     Evm.Diff [x] [y] s s'
--

def Evm.Calldataload (s s' : Evm) : Prop :=
  ∃ x, Evm.Diff [x] [B8L.toB256 (s.msg.data.sliceD x.toNat 32 0)] s s'

-- def Desc.Calldataload (e : Env) (s s' : Evm) : Prop :=
--   ∃ x y,
--     Evm.Diff [x] [y] s s' ∧
--     List.sliceD e.cld x.toNat 32 0 = y.toB8L
--
--     let ⟨x, evm⟩ ← evm.popToNat
--     let ⟨y, evm⟩ ← evm.popToNat
--     let ⟨z, evm⟩ ← evm.popToNat
--
--     let value := evm.msg.data.sliceD y z 0
--     memory := evm.memory.write x value

-- def Evm.memWrite (evm : Evm) (idx : Nat) (val : B8L) : Evm :=
--   {evm with memory := evm.memory.write idx val}

-- def FOo

def Mstored (x : B256) (bs : B8L) (m m' : Mem) : Prop :=
  m'.data = (m.write x.toNat bs).data

def Evm.Calldatacopy (s s' : Evm) : Prop :=
  ∃ x y z,
    Evm.Rel
      { Evm.Rels.equiv with
        stack := Stack.Pop [x, y, z],
        memory :=
          λ mem mem' =>
            mem' = mem.write x.toNat (s.msg.data.sliceD y.toNat z.toNat 0)
      } s s'


-- def Mem.read (μ : Mem) (index size : ℕ) : B8L × Mem :=
--   ⟨μ.data.sliceD index size 0, μ.extend index size⟩

-- def Evm.memRead (evm : Evm) (index size : Nat) : B8L × Evm :=
--   let ⟨val, mem⟩ := evm.memory.read index size
--   ⟨val, {evm with memory := mem}⟩

   -- let ⟨x, evm⟩ ← evm.popToNat
   -- let ⟨y, evm⟩ ← evm.popToNat
   -- let ⟨z, evm⟩ ← evm.popToNat
   -- let words := ceilDiv z 32
   -- let copy_gas_cost := gasCopy * words
   -- let extend_memory_cost :=
   --   evm.extCost [⟨y, z⟩, ⟨x, z⟩]
   -- let evm ← chargeGas (gVerylow + copy_gas_cost + extend_memory_cost) evm
   -- let ⟨value, evm⟩ := evm.memRead y z
   -- (evm.memWrite x value).incrPc


def Evm.Mcopy (s s' : Evm) : Prop :=
  ∃ x y z,
    Evm.Rel
      { Evm.Rels.equiv with
        stack := Stack.Pop [x, y, z],
        memory :=
          λ mem mem' =>
            let value := mem.data.sliceD y.toNat z.toNat 0
            mem'.data = (mem.write x.toNat value).data } s s'


def Evm.Codecopy (s s' : Evm) : Prop :=
  ∃ x y z,
    Evm.Rel
      { Evm.Rels.equiv with
        stack := Stack.Pop [x, y, z],
        memory :=
          Mstored x (s.code.sliceD y.toNat z.toNat (Linst.toB8 .stop)) } s s'

def Evm.Extcodecopy (s s' : Evm) : Prop :=
  ∃ w x y z,
    Evm.Rel
      { Evm.Rels.equiv with
        stack := Stack.Pop [w, x, y, z],
        memory :=
          let code := s.getCode w.toAdr
          let value := code.sliceD y.toNat z.toNat (Linst.toB8 .stop)
          Mstored x value } s s'

def Evm.Retdatacopy (s s' : Evm) : Prop :=
  -- x -- let ⟨memory_start_index, evm⟩ ← evm.popToNat
  -- y -- let ⟨return_data_start_index, evm⟩ ← evm.popToNat
  -- z -- let ⟨size, evm⟩ ← evm.popToNat
  ∃ x y z,
    Evm.Rel
      { Evm.Rels.equiv with
        stack := Stack.Pop [x, y, z],
        memory :=
          let value := s.returnData.sliceD y.toNat z.toNat 0
          Mstored x value } s s'

-- One thing that all block operations have in common is that they consume
-- no Stack items, leave exactly one new item on the Stack, and change nothing
-- else in the Desc. The contents of the new item depend on the operation used,
-- but their differences are immaterial for current purposes of the formalization,
-- so that part is unspecified here. These definitions will need to be augmented
-- to  verify more detailed properties about block operations.


def Evm.Tstore (s s' : Evm) : Prop :=
  ∃ x y : B256,
    Evm.Rel
    { Evm.Rels.equiv with
      -- todo : add t-storage condition
      stack := Stack.Diff [x, y] [] } s s' ∧
    s.msg.isStatic = 0

def Evm.Sstore (s s' : Evm) : Prop :=
  -- x -- let ⟨key, evm1⟩ ← evm.pop
  -- y -- let ⟨new_value, evm2⟩ ← evm1.pop
  ∃ x y : B256,
    Evm.Rel
    { Evm.Rels.equiv with
      stack := Stack.Diff [x, y] []
      msg := λ m m' => m' = m.setStorVal s.contract x y } s s' ∧
    s.msg.isStatic = 0

def Evm.Sload (s s' : Evm) : Prop :=
  ∃ x, Evm.Diff [x] [s.getStorVal s.contract x] s s'

def Evm.Tload (s s' : Evm) : Prop :=
  ∃ x y, Evm.Diff [x] [y] s s' -- todo : use value from t-storage

def Evm.Mload (s s' : Evm) : Prop :=
  ∃ x,
    let value : B8L := s.memory.data.sliceD x.toNat 32 0
    Evm.Diff [x] [value.toB256] s s'

def Evm.Mstore (s s' : Evm) : Prop :=
  ∃ x y,
    Evm.Rel
      { Evm.Rels.equiv with
        stack := Stack.Diff [x, y] [],
        memory := Mstored x y.toB8L }
      s s'

def Evm.Mstore8 (s s' : Evm) : Prop :=
  ∃ (x y : B256),
    Evm.Rel
      { Evm.Rels.equiv with
        stack := Stack.Diff [x, y] [],
        memory := Mstored x [y.2.2.toUInt8] } s s'

-- Design choice notes: in this formalization, definition of EVM operational semantics
-- does not follow the 'obvious' path that a cursory reading of YP may suggest,
-- i.e. by defining functions/relations that correspond 1:1 with the Θ/Λ/Ξ/X/O functions.
-- This is due to definition circularity, and tradeoffs in proof simplicity: Θ and Λ
-- depend on Ξ, which depends on X, which in turn depends on O, but O includes call/create
-- opcode cases that are defined in terms of Θ and Λ. Doing this in lean with mutual
-- recursion/induction isn't impossible, but comes with significant additional complexity
-- & proof difficulty that aren't justified by marginal improvements in staying faithful
-- to the original defs. In other B256s, this formalization asks users to squint a little
-- harder to convince themselves that it really describes the EVM, because it is worth it.

def Result.wrap (s : Desc) (ret : B8L) : Result :=
  {
    bal := s.bal,
    stor := s.stor,
    code := s.code,
    ret := ret,
    dest := s.dest
  }

def Xinst.toB8 : Xinst → B8
  | create   => 0xF0
  | call     => 0xF1
  | callcode => 0xF2
  | delcall  => 0xF4
  | create2  => 0xF5
  | statcall => 0xFA

def pushToB8 (bs : B8L) : B8 := 0x5F + Nat.toUInt8 bs.length
def pushToB8L (bs : B8L) : B8L := pushToB8 bs :: bs

def Linst.At (code : ByteArray) (pc : Nat) (l : Linst) : Prop := code.getInst pc = some (.last l)
def Ninst.At (code : ByteArray) (pc : Nat) (n : Ninst) : Prop := code.getInst pc = some (.next n)
def Jinst.At (code : ByteArray) (pc : Nat) (j : Jinst) : Prop := code.getInst pc = some (.jump j)
def Rinst.At (code : ByteArray) (pc : Nat) (r : Rinst) : Prop := code.getInst pc = some (.next (.reg r))


-- def PushAt (e : Env) (pc : Nat) (bs : B8L) : Prop :=
--   List.Slice e.code pc (pushToB8L bs) ∧ bs.length ≤ 32

-- inductive Linst.Run : Env → Desc → Linst → Result → Prop
--   | stop : ∀ e s, Linst.Run e s Linst.stop (Result.wrap s [])
--   | ret :
--     ∀ e s x y,
--       ([x, y] <+: s.stk) →
--       Linst.Run e s Linst.ret (.wrap s <| s.mem.slice x y)
--   | dest :
--     ∀ (e : Env) (s : Desc) x bal bal',
--       s.msg.isStatic = 0 →
--       ([x] <+: s.stk) →
--       Overwrite e.cta 0 s.bal bal →
--       Increase x.toAdr (s.bal e.cta) bal bal' →
--       Linst.Run e s Linst.dest {s with bal := bal', ret := [], dest := e.cta :: s.dest}

-- def Fail (s : Desc) (o : Xinst) (s' : Desc) : Prop :=
--   match o with
--   | .create => ∃ x y z, Desc.Pop [x, y, z] s s'
--   | .call => ∃ x₀ x₁ x₂ x₃ x₄ x₅ x₆, Desc.Pop [x₀, x₁, x₂, x₃, x₄, x₅, x₆] s s'
--   | .callcode => ∃ x₀ x₁ x₂ x₃ x₄ x₅ x₆, Desc.Pop [x₀, x₁, x₂, x₃, x₄, x₅, x₆] s s'
--   | .delcall => ∃ x₀ x₁ x₂ x₃ x₄ x₅, Desc.Pop [x₀, x₁, x₂, x₃, x₄, x₅] s s'
--   | .create2 => ∃ x₀ x₁ x₂ x₃, Desc.Pop [x₀, x₁, x₂, x₃] s s'
--   | .statcall => ∃ x₀ x₁ x₂ x₃ x₄ x₅, Desc.Pop [x₀, x₁, x₂, x₃, x₄, x₅] s s'


-- Blanc semantics --

inductive Func : Type
  | branch : Func → Func → Func
  | last : Linst → Func
  | next : Ninst → Func → Func
  | call : Nat → Func
-- deriving DecidableEq

structure Prog : Type where
  (main : Func)
  (aux : List Func)

infixr:65 " <?> " => λ f g => Func.branch g f

infixr:65 " ::: " => Func.next
postfix:100 " ::. " => Func.last



def Rinst.Run : Evm → Rinst → Evm → Prop :=
  Function.swap <|
    fun
    | Rinst.add => Evm.Add
    | Rinst.sub => Evm.Sub
    | Rinst.mul => Evm.Mul
    | Rinst.div => Evm.Div
    | Rinst.mod => Evm.Mod
    | Rinst.sdiv => Evm.Sdiv
    | Rinst.smod => Evm.Smod
    | Rinst.addmod => Evm.Addmod
    | Rinst.mulmod => Evm.Mulmod
    | Rinst.exp => Evm.Exp
    | Rinst.signextend => Evm.Signextend
    | Rinst.lt => Evm.Lt
    | Rinst.gt => Evm.Gt
    | Rinst.slt => Evm.Slt
    | Rinst.sgt => Evm.Sgt
    | Rinst.eq => Evm.Eq
    | Rinst.iszero => Evm.Iszero
    | Rinst.and => Evm.And
    | Rinst.or => Evm.Or
    | Rinst.xor => Evm.Xor
    | Rinst.not => Evm.Not
    | Rinst.byte => Evm.Byte
    | Rinst.shl => Evm.Shl
    | Rinst.shr => Evm.Shr
    | Rinst.sar => Evm.Sar
    | Rinst.kec => Evm.Kec
    | Rinst.address => Evm.Adress
    | Rinst.balance => Evm.Balance
    | Rinst.origin => Evm.Origin
    | Rinst.caller => Evm.Caller
    | Rinst.callvalue => Evm.Callvalue
    | Rinst.calldataload => Evm.Calldataload
    | Rinst.calldatasize => Evm.Calldatasize
    | Rinst.calldatacopy => Evm.Calldatacopy
    | Rinst.codesize => Evm.Codesize
    | Rinst.codecopy => Evm.Codecopy
    | Rinst.gasprice => Evm.Gasprice
    | Rinst.extcodesize => Evm.Extcodesize
    | Rinst.extcodecopy => Evm.Extcodecopy
    | Rinst.retdatasize => Evm.Retdatasize
    | Rinst.retdatacopy => Evm.Retdatacopy
    | Rinst.extcodehash => Evm.Extcodehash
    | Rinst.blockhash => λ s s' => ∃ x, Evm.Push [x] s s'
    | Rinst.coinbase => λ s s' => ∃ x, Evm.Push [x] s s'
    | Rinst.timestamp => λ s s' => ∃ x, Evm.Push [x] s s'
    | Rinst.number => λ s s' => ∃ x, Evm.Push [x] s s'
    | Rinst.prevrandao => λ s s' => ∃ x, Evm.Push [x] s s'
    | Rinst.gaslimit => λ s s' => ∃ x, Evm.Push [x] s s'
    | Rinst.chainid => λ s s' => ∃ x, Evm.Push [x] s s'
    | Rinst.selfbalance => λ s s' => ∃ x, Evm.Push [x] s s'
    | Rinst.basefee => λ s s' => ∃ x, Evm.Push [x] s s'
    | Rinst.blobhash => λ s s' => ∃ x y, Evm.Diff [x] [y] s s'
    | Rinst.blobbasefee => λ s s' => ∃ x, Evm.Push [x] s s'
    | Rinst.pop => λ s s' => ∃ x, Evm.Pop [x] s s'
    | Rinst.mload => Evm.Mload
    | Rinst.mstore => Evm.Mstore
    | Rinst.mstore8 => Evm.Mstore8
    | Rinst.sload => Evm.Sload
    | Rinst.sstore => Evm.Sstore
    | Rinst.tload => Evm.Tload
    | Rinst.tstore => Evm.Tstore
    | Rinst.mcopy => Evm.Mcopy
    | Rinst.msize => λ s s' => ∃ x, Evm.Push [x] s s'
    | Rinst.gas => λ s s' => ∃ x, Evm.Push [x] s s'
    | Rinst.pc => λ s s' => ∃ x, Evm.Push [x] s s'
    | Rinst.dup n => Evm.Dup n.val
    | Rinst.swap n => Evm.Swap n.val
    | Rinst.log n =>
      match n with
      | ⟨0, _⟩ => λ s s' => ∃ x₀ x₁, Evm.Pop [x₀, x₁] s s'
      | ⟨1, _⟩ => λ s s' => ∃ x₀ x₁ x₂, Evm.Pop [x₀, x₁, x₂] s s'
      | ⟨2, _⟩ => λ s s' => ∃ x₀ x₁ x₂ x₃, Evm.Pop [x₀, x₁, x₂, x₃] s s'
      | ⟨3, _⟩ => λ s s' => ∃ x₀ x₁ x₂ x₃ x₄, Evm.Pop [x₀, x₁, x₂, x₃, x₄] s s'
      | ⟨4, _⟩ => λ s s' => ∃ x₀ x₁ x₂ x₃ x₄ x₅, Evm.Pop [x₀, x₁, x₂, x₃, x₄, x₅] s s'
      | ⟨5, h⟩ => False.elim <| Nat.lt_irrefl _ h
    -- | Rinst.invalid => λ _ _ => False

-- inductive Jinst.Run : Env → Desc → Nat → Jinst → Desc → Nat → Prop
--   | jump :
--     ∀ e s s' pc x,
--       Desc.Pop [x] s s' →
--       Jumpable e x.toNat →
--       Jinst.Run e s pc jump s' x.toNat
--   | zero :
--     ∀ e s s' pc x,
--       Desc.Pop [x, 0] s s' →
--       Jinst.Run e s pc jumpi s' (pc + 1)
--   | succ :
--     ∀ e s s' pc x y,
--       Desc.Pop [x, y] s s' →
--       y ≠ 0 →
--       Jumpable e x.toNat →
--       Jinst.Run e s pc jumpi s' x.toNat
--   | dest :
--     ∀ e s pc, Jinst.Run e s pc jumpdest s (pc + 1)

structure PreRun (s : Desc) (r : Result) : Prop where
  (bal : s.bal = r.bal)
  (stor : s.stor = r.stor)
  (code : s.code = r.code)
  (dest : s.dest = r.dest)

inductive Xinst.isCall : Xinst → Prop
| call : Xinst.isCall .call
| callcode : Xinst.isCall .callcode
| delcall : Xinst.isCall .delcall
| statcall : Xinst.isCall .statcall

def Env.prep (e : Env) (s : Desc)
    (cta : Adr) (cld : B8L) (cla : Adr)
    (clv : B256) (cda : Adr) (exd : Nat) (wup : Bool) : Env :=
  { cta := cta, oga := e.oga, gpr := e.gpr, cld := cld, cla := cla,
    clv := clv, code := s.code cda, exd := exd, wup := wup }

def Env.prep' (e : Env)
    (cta : Adr) (clv : B256) (ctc : B8L) (exd : Nat) : Env :=
  { cta := cta, oga := e.oga, gpr := e.gpr, cld := [], cla := e.cta,
    clv := clv, code := ctc, exd := exd, wup := 1 }

def Desc.prep (s : Desc) (bal : Balances) : Desc :=
  { bal := bal, stor := s.stor, code := s.code, stk := [],
    mem := Memory.init, ret := [], dest := s.dest }

def Desc.wrap (r : Result) (stk : Stack) (mem : Memory) : Desc :=
  { bal := r.bal, stor := r.stor, code := r.code,
    stk := stk, mem := mem, ret := r.ret, dest := r.dest }

def Desc.wrap' (r : Result) (cd : Codes) (mem : Memory) (stk : Stack) : Desc :=
  { bal := r.bal, stor := r.stor, code := cd, mem := mem,
    stk := stk, ret := r.ret, dest := r.dest }

/-
def storeRet (mem : Memory) (ret : B8L) (loc sz : B256) (mem' : Memory) : Prop :=
  Mstored loc (List.take sz.toNat ret) mem mem'

inductive Xinst.Run' : Env → Desc → Env → Desc → Xinst → Result → Desc → Prop
  | create :
    ∀ e : Env, e.wup = 1 →
    ∀ exd, e.exd = exd.succ →
    ∀ (s : Desc) (cta : Adr), s.code cta = [] →
    ∀ (clv clc csz : B256) (stk : Stack),
      Stack.Diff [clv, clc, csz] [Adr.toB256 cta] s.stk stk →
    ∀ bal : Balances, Transfer s.bal e.cta clv cta bal →
    ∀ (r : Result) (cd : Codes),
      Overwrite cta r.ret r.code cd →
      Xinst.Run' e s (.prep' e cta clv (s.mem.slice clc csz) exd)
        (.prep s bal) .create r (.wrap' r cd s.mem stk)
  | create2 :
    ∀ e : Env, e.wup = 1 →
    ∀ exd, e.exd = exd.succ →
    ∀ (s : Desc) (cta : Adr), s.code cta = [] →
    ∀ (clv clc csz slt : B256) (stk : Stack),
      Stack.Diff [clv, clc, csz, slt] [Adr.toB256 cta] s.stk stk →
    ∀ bal : Balances, Transfer s.bal e.cta clv cta bal →
    ∀ (r : Result) (cd : Codes),
      Overwrite cta r.ret r.code cd →
      Xinst.Run' e s (.prep' e cta clv (s.mem.slice clc csz) exd)
        (.prep s bal) .create r (.wrap' r cd s.mem stk)
  | call :
    ∀ (e : Env) exd, e.exd = exd.succ →
    ∀ gas adr clv ilc isz olc osz s stk,
      Stack.Diff [gas, adr, clv, ilc, isz, olc, osz] [1] s.stk stk →
    ∀ bal : Balances, Transfer s.bal e.cta clv adr.toAdr bal →
    ∀ r : Result,
    ∀ mem : Memory, storeRet s.mem r.ret olc osz mem →
      Xinst.Run' e s
        (.prep e s adr.toAdr (s.mem.slice ilc isz) e.cta clv adr.toAdr exd e.wup)
        (.prep s bal) .call r (.wrap r stk mem)
  -- Two design flaws of CALLCODE:
  -- (1) it accepts a useless call value argument that doesn't actually do anything
  -- (2) it updates the caller address when it shouldn't
  | callcode :
    ∀ (e : Env) exd, e.exd = exd.succ →
    ∀ gas adr clv ilc isz olc osz s stk,
      Stack.Diff [gas, adr, clv, ilc, isz, olc, osz] [1] s.stk stk →
    ∀ r : Result,
    ∀ mem : Memory, storeRet s.mem r.ret olc osz mem →
      Xinst.Run' e s
        (.prep e s e.cta (s.mem.slice ilc isz) e.cta clv adr.toAdr exd e.wup)
        (.prep s s.bal) .callcode r (.wrap r stk mem)
  | delcall :
    ∀ (e : Env) exd, e.exd = exd.succ →
    ∀ gas adr ilc isz olc osz s stk,
      Stack.Diff [gas, adr, ilc, isz, olc, osz] [1] s.stk stk →
    ∀ r : Result,
    ∀ mem : Memory, storeRet s.mem r.ret olc osz mem →
      Xinst.Run' e s
        (.prep e s e.cta (s.mem.slice ilc isz) e.cla e.clv adr.toAdr exd e.wup)
        (.prep s s.bal) .delcall r (.wrap r stk mem)
  | statcall :
    ∀ (e : Env) exd, e.exd = exd.succ →
    ∀ gas adr ilc isz olc osz s stk,
      Stack.Diff [gas, adr, ilc, isz, olc, osz] [1] s.stk stk →
    ∀ r : Result,
    ∀ mem : Memory, storeRet s.mem r.ret olc osz mem →
      Xinst.Run' e s
        (.prep e s adr.toAdr (s.mem.slice ilc isz) e.cta 0 adr.toAdr exd 0)
        (.prep s s.bal) .statcall r (.wrap r stk mem)

inductive Halt : Env → Desc → Nat → Result → Prop
  | inst :
    ∀ e s pc o r,
      Linst.At e pc o →
      Linst.Run e s o r →
      Halt e s pc r
  | eoc : ∀ e s, Halt e s e.code.length (.wrap s [])
-/

-- inductive ExecOld : Env → Desc → Nat → Result → Type
--   | step :
--     ∀ {e s pc s' pc' r},
--       Step e s pc s' pc' →
--       ExecOld e s' pc' r →
--       ExecOld e s pc r
--   | exec :
--     ∀ {e s pc ep sp o r s' r'},
--       Xinst.At e pc o →
--       Xinst.Run' e s ep sp o r s' →
--       ExecOld ep sp 0 r →
--       ExecOld e s' (pc + 1) r' →
--       ExecOld e s pc r'
--   | halt :
--     ∀ {e s pc r},
--       Halt e s pc r →
--       ExecOld e s pc r

-- def Desc.init (bal : Adr → B256) (stor : Adr → Storage) (code : Adr → B8L) : Desc :=
--   {
--     bal := bal,
--     stor := stor,
--     code := code,
--     stk := [],
--     mem := Memory.init,
--     ret := [],
--     dest := []
--   }

--- -- The execution part of transaction, which happens after the deduction of
--- -- upfront gas payment, and before the distribution of gas refund/reward and
--- -- deletion of self-destructed contract codes.
--- inductive MessageCall
---     (sda : Adr) -- tx sender address
---                  -- (always an EOA & never has contract code, per EIP-3607)
---     (rca : Adr) -- tx receiver address
---                  -- · for contract calls, rca = address of called contract
---                  -- · for contract creations, rca = address of newly created contract
---     (w : World)  -- initial world state
---     : Result → Prop
---   | create :
---     ∀ gpr clv ctc bal r code,
---       Transfer w.bal sda clv rca bal →
---       w.code rca = [] →
---       ExecOld
---         { cta := rca, oga := sda, gpr := gpr, cld := [], cla := sda,
---           clv := clv, code := ctc, exd := 1024, wup := true }
---         --{ bal := bal, stor := w.stor, code := w.code, stk := [],
---         --  mem := Memory.init, ret := [], dest := [] }
---         (Desc.init bal w.stor w.code)
---         0 r →
---       Overwrite rca r.ret r.code code →
---       MessageCall sda rca w {r with code := code}
---   | call :
---     ∀ gpr cld clv bal r,
---       Transfer w.bal sda clv rca bal →
---       ExecOld
---         { cta := rca, oga := sda, gpr := gpr, cld := cld, cla := sda,
---           clv := clv, code := w.code rca, exd := 1024, wup := true }
---         -- { bal := bal, stor := w.stor, code := w.code, stk := []
---         --   mem := Memory.init, ret := [], dest := []}
---         (Desc.init bal w.stor w.code)
---         0 r →
---       MessageCall sda rca w r
---   | pre :
---     ∀ clv bal ret,
---       Transfer w.bal sda clv rca bal →
---       MessageCall sda rca w
---         {bal := bal, stor := w.stor, code := w.code, ret := ret, dest := []}
---   | fail : MessageCall sda rca w {w with ret := .nil, dest := []}

def DeleteCodes : List Adr → Codes → Codes → Prop
  | [], c, c' => c = c'
  | a :: as, c, c'' => ∃ c' : Codes, Overwrite a [] c c' ∧ DeleteCodes as c' c''

  -- structure Transaction (w w' : World) : Type where
  --   (vs : B256) -- gas ultimately refunded to sender
  --   (vv : B256) -- gas ultimately rewarded to validator
  --   (vb : B256) -- gas ultimately burned
  --   (nof : vs.toNat + vv.toNat + vb.toNat < 2 ^ 256)
  --   (sda : Adr) -- tx sender address
  --   (eoa : w.code sda = []) -- per EIP-3607
  --   (bal : Balances) -- balances after upfront deduction
  --   (decr : Decrease sda (vs + vv + vb) w.bal bal)
  --   (le : vs + vv + vb ≤ w.bal sda)
  --   (rca : Adr) -- tx receiver address
  --   (r : Result) -- execution result
  --   (act : MessageCall sda rca {w with bal := bal} r)
  --   (bal' : Balances) -- balances after refund to sender
  --   (incr : Increase sda vs r.bal bal')
  --   (vla : Adr) -- validator address
  --   (incr' : Increase vla vv bal' w'.bal)
  --   (del : DeleteCodes r.dest r.code w'.code)
  --   (stor : w'.stor = r.stor)
--



def Ninst.toB8L : Ninst → B8L
  | reg o => [o.toB8]
  | exec o => [o.toB8]
  | push bs _ => pushToB8L bs

-- inductive Xinst.Run : Env → Desc → Xinst → Desc → Prop
--   | exec :
--     ∀ {e s ep sp o r s'},
--       Xinst.Run' e s ep sp o r s' →
--       ExecOld ep sp 0 r →
--       Xinst.Run e s o s'
--   | pre :
--     ∀ {e s ep sp o r s'},
--       o.isCall →
--       Xinst.Run' e s ep sp o r s' →
--       PreRun sp r →
--       Xinst.Run e s o s'
--   | fail : ∀ {e s o s'}, Fail s o s' → Xinst.Run e s o s'
--
--
-- def Evm.Pop (xs : List B256) : Evm → Evm → Prop :=
--   Rel {Rels.equiv with stack := Stack.Pop xs}

def Jinst.Run (evm : Evm) : Jinst → Execution → Prop := λ j ex => j.run evm = ex
def Linst.Run (evm : Evm) : Linst → Execution → Prop := λ l ex => l.run evm = ex





----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------




def Except.IsError {ξ υ : Type} (e : Except ξ υ) : Prop :=
  match e with
  | .error _ => True
  | .ok _ => False

def Xlot : Type := Option (Evm × Execution)

def Except.Split {ξ υ ζ : Type}
    (e : Except ξ υ) (e' : Except ξ ζ) (q : υ → Prop) : Prop :=
  (∃ x, e = .error x ∧ e' = .error x) ∨ (∃ y : υ, e = .ok y ∧ q y)

def ExecuteCode (msg : Msg) (xl : Xlot)
    (ex : Except (String × Benv × Tenv) Evm) : Prop :=
  let evm : Evm := initEvm msg
  match msg.codeAddress with
  | .none =>
    ∃ ex', xl = .some ⟨evm, ex'⟩ ∧ executeCode.handleError ex' = ex
  | .some adr =>
    if adr.isPrecomp then
      (xl = .none ∧  executeCode.handleError (executePrecomp evm adr) = ex)
    else
      ∃ ex', xl = .some ⟨evm, ex'⟩ ∧ executeCode.handleError ex' = ex

def ProcessMessage (msg : Msg) (xl : Xlot)
    (ex : Except (String × Benv × Tenv) Evm) : Prop :=
    ( Except.assert (msg.depth ≤ 1024)
        ⟨"StackDepthLimitError", msg.benv, msg.tenv⟩ ).Split ex <|
  λ _ =>
    msg.benvAfterTransfer.Split ex <|
  λ benv =>
  ∃ ex' : Except (String × Benv × Tenv) Evm,
    And (ExecuteCode (msg.withBenv benv) xl ex') <|
    ex'.Split ex <|
  λ evm =>
    if evm.error.isSome then
      .ok (evm.rollback msg.benv.state msg.tenv.transientStorage) = ex
    else
      .ok evm = ex

def ProcessCreateMessage (msg : Msg) (xl : Xlot)
    (ex : Except (String × Benv × Tenv) Evm) : Prop :=
  ∃ ex' : Except (String × Benv × Tenv) Evm,
    And (ProcessMessage (processCreateMessage.msg msg) xl ex') <|
    ex'.Split ex <|
  λ evm =>
  if evm.error.isNone then
    match processCreateMessage.chargeCodeGas evm with
    | .ok evm => .ok (evm.setCode msg.currentTarget ⟨⟨evm.output⟩⟩) = ex
    | .error (err, evm) =>
      if isExceptionalHalt err then
        .ok
          ( processCreateMessage.exceptionalHalt evm err
              msg.benv.state
              msg.tenv.transientStorage ) = ex
      else
        .error ⟨err, evm.msg.benv, evm.msg.tenv⟩ = ex
  else
    .ok (evm.rollback msg.benv.state msg.tenv.transientStorage) = ex

def GenericCreate (evm : Evm) (endowment : B256) (newAddress : Adr)
    (memoryIndex memorySize : Nat) (xl : Xlot) (ex : Execution) : Prop :=
  ∃ callData : B8L,
    And (callData = evm.memory.data.sliceD memoryIndex memorySize 0) <|
    (Except.assert (memorySize ≤ maxInitcodeSize) ⟨"OutOfGasError", evm⟩).Split ex <|
  λ _ =>
  ∃ evm1 : Evm,
    And (evm1 = addAccessedAddress evm newAddress) <|
  ∃ createMsgGas : ℕ,
    And (createMsgGas = except64th evm1.gasLeft) <|
  ∃ evm2 : Evm,
    And (evm2 = {evm1 with gasLeft := evm1.gasLeft - createMsgGas}) <|
    evm2.assertDynamic.Split ex <|
  λ _ =>
  ∃ evm3 : Evm,
    And (evm3 = {evm2 with returnData := []}) <|
  ∃ sender : Acct,
    And (sender = evm3.msg.benv.state.get evm3.contract) <|
  if ( sender.bal < endowment ∨
       sender.nonce = B64.max ∨ evm3.msg.depth + 1 > 1024 ) then
    ({evm3 with gasLeft := evm3.gasLeft + createMsgGas}.push 0 = ex)
  else
  ∃ evm4 : Evm,
    And (evm4 = evm3.incrNonce evm3.contract) <|
  if
    ( let target := evm4.msg.benv.state.get newAddress
      target.nonce ≠ (0 : B64) ∨
      target.code.size ≠ 0 ∨
      target.stor.size ≠ 0 ) then
    (evm4.push 0 = ex)
  else
  ∃ childMsg : Msg,
    And (
      childMsg = {
        benv := evm4.msg.benv
        tenv := evm4.msg.tenv
        caller := evm4.contract
        target := .none
        gas := createMsgGas
        value := endowment
        data := []
        code := .mk <| .mk callData
        currentTarget := newAddress
        depth := evm4.msg.depth + 1
        codeAddress := .none
        shouldTransferValue := true
        isStatic := false
        accessedAddresses := evm4.accessedAddresses
        accessedStorageKeys := evm4.accessedStorageKeys
        disablePrecompiles := false
      }
    ) <|
  ∃ ex',
    And (ProcessCreateMessage childMsg xl ex') <|
    (liftToExecution evm4 ex').Split ex <|
  λ child =>
    if child.error.isSome  then
      (incorporateChildOnError evm4 child child.output).push 0 = ex
    else
      (incorporateChildOnSuccess evm4 child []).push child.contract.toB256 = ex


def GenericCall (evm : Evm) (gas : ℕ) (value : B256)
    (caller target codeAddress : Adr) (shouldTransferValue isStaticcall : Bool)
    (input_index input_size output_index output_size : ℕ)
    (code : ByteArray) (disablePrecompiles : Bool) (xlot : Xlot) (ex : Execution) : Prop :=
  ∃ evm1,
    And (evm1 = {evm with returnData := []}) <|
  if (evm1.msg.depth + 1 > 1024) then
    ({evm1 with gasLeft := evm1.gasLeft + gas}.push 0 = ex)
  else
    --Or ( evm1.msg.depth + 1 > 1024 ∧
    --     {evm1 with gasLeft := evm1.gasLeft + gas}.push 0 = ex ) <|
    --And (¬ evm1.msg.depth + 1 > 1024) <|
  ∃ calldata,
    And (calldata = evm1.memory.data.sliceD input_index input_size 0) <|
  ∃ childMsg : Msg,
    And (
      childMsg = {
        benv := evm1.msg.benv
        tenv := evm1.msg.tenv
        caller := caller
        target := target
        gas := gas
        currentTarget := target
        value := value
        data := calldata
        codeAddress := codeAddress
        code := code
        depth := evm1.msg.depth + 1
        shouldTransferValue := shouldTransferValue
        isStatic := isStaticcall || evm1.msg.isStatic
        accessedAddresses := evm1.accessedAddresses
        accessedStorageKeys := evm1.accessedStorageKeys
        disablePrecompiles := disablePrecompiles
      }
    ) <|
  ∃ ex' : Except (String × Benv × Tenv) Evm,
    And (ProcessMessage childMsg xlot ex') <|
    (liftToExecution evm1 ex').Split ex <|
  -- λ child =>
  --   ( if child.error.isSome then
  --       (incorporateChildOnError evm1 child child.output).push 0
  --     else
  --       (incorporateChildOnSuccess evm1 child child.output).push 1 ).Split ex <|
  -- λ evm2 =>
  --   let actualOutput := child.output.take output_size
  --   .ok (evm2.memWrite output_index actualOutput) = ex
  λ child =>
  let actualOutput := child.output.take output_size
  if child.error.isSome then
    ((incorporateChildOnError evm1 child child.output).push 0).Split ex <|
    λ evm2 => .ok (evm2.memWrite output_index actualOutput) = ex
  else
    ((incorporateChildOnSuccess evm1 child child.output).push 1 ).Split ex <|
    λ evm2 => .ok (evm2.memWrite output_index actualOutput) = ex



-- def Xlot.Good (lim : Nat) (ex : Execution) : Xlot → Prop
--   | .none => True
--   | .some (evm', ex') =>
--     ∃ lim' < lim,
--       exec false lim' evm' = ex' ∧
--       (ex'.IsError → ex' = ex)

def Except.toError? {ξ υ} : Except (String × ξ) υ → Option String
  | .ok _ => none
  | .error ⟨err, _⟩ => some err

-- def Execution.Good (oerr : Option String) : Execution → Prop
--   | .ok _ => True
--   | .error ⟨_, err⟩ =>
--     err = "RecursionLimit" →  oerr = some "RecursionLimit"

def Xlot.Good (lim : Nat) (oe : Option String) : Xlot → Prop
  | .none => True
  | .some (evm, ex) =>
    ∃ lim' < lim,
      exec false evm lim' = ex ∧
      (ex.toError? = some "RecursionLimit" → oe = some "RecursionLimit")

def Except.Limited {ξ υ} (ex : Except (String × ξ) υ) : Prop :=
  ex.toError? = some "RecursionLimit"

def Except.Unlim {ξ υ} (ex : Except (String × ξ) υ) : Prop := ¬ ex.Limited

def Xlot.Good' : Xlot → Prop
  | .none => True
  | .some (evm, ex) =>
    ¬ ex.Limited ∧ ∃ lim, exec false evm lim = ex

lemma Except.of_toError?_eq_some {ξ} (ex : Except (String × ξ) Evm)
    (err : String) (eq : ex.toError? = some err) :
    ∃ x, ex = .error ⟨err, x⟩ := by
  rcases ex with ⟨err', _⟩ | _ <;> simp [Except.toError?] at eq
  cases eq; refine ⟨_, rfl⟩


lemma Xlot.good_of_good_of_notLimited {lim lim' : Nat} {oe oe' : Option String}
    {xl : Xlot} (le : lim ≤ lim') (ne : oe ≠ some "RecursionLimit")
    (good : xl.Good lim oe) : xl.Good lim' oe' := by
  rcases xl with _ | ⟨evm, ex⟩; {constructor}
  rcases good with ⟨_, lt, exec, of_eq⟩
  refine' ⟨_, Nat.lt_of_lt_of_le lt le, exec,  _⟩
  intro eq; cases ne <| of_eq eq


syntax "okStep1 " ident rcasesPat : tactic
macro_rules
  | `(tactic| okStep1 $h $pat1) => `(tactic|
      rcases of_bind_eq $h with ⟨_, ⟨_⟩, _⟩ | ⟨$pat1, temp_eq, eq'⟩;
      clear $h; rename' eq' => $h;
      apply Exists.imp
        (λ _ (conj : _ ∧ _) => ⟨conj.1, ⟨_, (Except.ok.inj temp_eq).symm, conj.2⟩⟩);
      clear temp_eq
    )

syntax "okStep2 " ident rcasesPat rcasesPat : tactic
macro_rules
  | `(tactic| okStep2 $h $pat1 $pat2) => `(tactic|
      rcases of_bind_eq $h with ⟨_, ⟨_⟩, _⟩ | ⟨⟨$pat1, $pat2⟩, temp_eq, eq'⟩;
      clear $h; rename' eq' => $h;
      apply Exists.imp
        (λ _ (conj : _ ∧ _) => ⟨conj.1, ⟨_, _, (Except.ok.inj temp_eq).symm, conj.2⟩⟩);
      clear temp_eq
    )

syntax "okStep5 " ident rcasesPat rcasesPat rcasesPat rcasesPat rcasesPat : tactic
macro_rules
  | `(tactic| okStep5 $h $pat1 $pat2 $pat3 $pat4 $pat5) => `(tactic|
      rcases of_bind_eq $h
        with ⟨_, ⟨_⟩, _⟩ | ⟨⟨$pat1, $pat2, $pat3, $pat4, $pat5⟩, temp_eq, eq'⟩;
      clear $h; rename' eq' => $h;
      apply Exists.imp
        (λ _ (conj : _ ∧ _) => ⟨conj.1, ⟨_, _, _, _, _, (Except.ok.inj temp_eq).symm, conj.2⟩⟩);
      clear temp_eq
    )

syntax "bind_step_good " ident rcasesPat : tactic
macro_rules
  | `(tactic| bind_step_good $h $pat) => `(tactic|
      rcases of_bind_eq $h with im | ⟨$pat, temp_eq, eq'⟩;
      { refine ⟨.none, .intro, .inl im⟩ };
      clear $h; rename' eq' => $h;
      apply Exists.imp
        (λ _ (conj : _ ∧ _) => ⟨conj.1, Or.inr ⟨_, temp_eq, conj.2⟩⟩);
      clear temp_eq
    )

syntax "bind_step' " ident rcasesPat : tactic
macro_rules
  | `(tactic| bind_step' $h $pat) => `(tactic|
      rcases of_bind_eq $h with im | ⟨$pat, temp_eq, eq'⟩;
      {left; exact im}; clear $h; rename' eq' => $h;
      right; refine' ⟨_, temp_eq, _⟩; clear temp_eq
    )

lemma Except.of_error_bind_eq {ξ υ ζ : Type}
    {x : ξ} {f : υ → Except ξ ζ} (e : Except ξ ζ)
    (eq : (Except.error x) >>= f = e) : Except.error x = e := by
  simp [bind, Except.bind] at eq; exact eq

lemma Execution.notLimited_of_notLimited
    {f : Execution} {g : Evm → Execution} {ex : Execution}
    (notLimited : ¬ ex.Limited) (eq : f >>= g = ex) : ¬ f.Limited := by
  intro rw; rcases f with ⟨evm, err⟩ | _ <;>
    simp [Except.Limited, Except.toError?] at rw
  rw [rw] at eq; rw [← eq] at notLimited; cases notLimited rfl

lemma Except.notLimited_of_notLimited
    {f : Except (String × Benv × Tenv) Evm}
    {g : Evm → Except (String × Benv × Tenv) Evm}
    {ex : Except (String × Benv × Tenv) Evm}
    (notLimited : ¬ ex.Limited) (eq : f >>= g = ex) : ¬ f.Limited := by
  intro rw; rcases f with ⟨benv, tenv, err⟩ | _ <;>
    simp [Except.Limited, Except.toError?] at rw
  rw [rw] at eq; rw [← eq] at notLimited; cases notLimited rfl

lemma of_limited_bind {ξ υ ζ} {x : Except (String × ξ) υ}
    {f : υ → Except (String × ξ) ζ} (h : (x >>= f).Limited) :
    x.Limited ∨ (∃ y, x = .ok y ∧ (f y).Limited) := by
  rcases x with ⟨err, s⟩ | y
  · left; simp [bind, Except.bind] at h; exact h
  · right; use y; constructor; rfl
    simp [bind, Except.bind] at h; exact h

lemma of_unlim_bind {ξ υ ζ} {x : Except (String × ξ) υ}
    {f : υ → Except (String × ξ) ζ} (unlim : (x >>= f).Unlim) :
    x.Unlim ∧ (∀ y, x = .ok y → (f y).Unlim) := by
  constructor
  · intro ltd
    rcases x with ⟨_, _⟩ | _
    · injection ltd; rename_i rw; rw [rw] at unlim; cases unlim rfl
    · cases ltd
  · intro y eq; rw [eq] at unlim; exact unlim







lemma of_executeCode {msg : Msg} {lim : Nat}
    {ex : Except (String × Benv × Tenv) Evm}
    (notLimited : ex.toError? ≠ some "RecursionLimit")
    (eq : executeCode false msg lim = ex) :
    ∃ xl : Xlot, xl.Good lim ex.toError? ∧ ExecuteCode msg xl ex := by
  rcases lim with _ | lim <;> simp only [executeCode] at eq
  {rw [← eq] at notLimited; cases notLimited rfl}
  split at eq
  · rename msg.codeAddress = .none => eq_none
    refine'
      ⟨ .some ⟨initEvm msg, exec false (initEvm msg) lim⟩,
        ⟨lim, (by omega), rfl, λ halts => _⟩, _ ⟩
    · rcases Except.of_toError?_eq_some _ _ halts with ⟨evm, rw⟩
      rw [← eq, rw] at notLimited; cases notLimited rfl
    · simp only [ExecuteCode]; rw [eq_none]; refine' ⟨_, rfl, eq⟩
  · rename Adr => adr
    rename msg.codeAddress = .some adr => eq_some
    split at eq
    · rename_i pos; refine' ⟨.none, .intro, _⟩
      simp only [ExecuteCode]; rw [eq_some]
      simp only []; rw [if_pos pos]; simp [eq]
    · rename_i neg
      refine'
        ⟨ .some ⟨initEvm msg, exec false (initEvm msg) lim⟩,
          ⟨lim, (by omega), rfl, λ halts => _⟩, _ ⟩
      · rcases Except.of_toError?_eq_some _ _ halts with ⟨evm, rw⟩
        rw [← eq, rw] at notLimited; cases notLimited rfl
      · simp only [ExecuteCode]; rw [eq_some]
        simp only []; rw [if_neg neg]; refine' ⟨_, rfl, eq⟩

lemma of_limited_handleError {ex : Execution} :
    (executeCode.handleError ex).Limited → ex.Limited := by
  rcases ex with ⟨err, err⟩ | _ <;>
    simp only [executeCode.handleError] <;> intro h
  · split at h; {cases h}; split at h; {cases h}; exact h
  · exact h

lemma limited_handleError {ex : Execution} :
    ex.Limited → (executeCode.handleError ex).Limited := by
  intro h; rcases ex with ⟨err, err⟩ | _ <;>
    simp [Except.Limited, Except.toError?] at h
  rw [h]; rfl

lemma of_processMessage (msg : Msg) (lim : Nat)
    (ex : Except (String × Benv × Tenv) Evm)
    (notLimited : ex.toError? ≠ some "RecursionLimit")
    (eq : processMessage false msg lim = ex) :
    ∃ xl : Xlot, xl.Good lim ex.toError? ∧ ProcessMessage msg xl ex := by
  rcases lim with _ | lim <;> simp only [processMessage] at eq
  {rw [← eq] at notLimited; cases notLimited rfl}
  bind_step_good eq _; bind_step_good eq _
  have notLimited' := Except.notLimited_of_notLimited notLimited eq
  rcases of_executeCode notLimited' rfl with ⟨xl, good, ec⟩
  refine' ⟨_, Xlot.good_of_good_of_notLimited (by omega) notLimited' good, _, ec, _⟩
  bind_step' eq _; split at eq
  · rename_i pos; rw [if_pos pos]; exact eq
  · rename_i neg; rw [if_neg neg]; exact eq

lemma ite_of_true {c : Prop} [Decidable c] {p q : Prop} :
    c → p → if c then p else q := by
  intro hc hp; rw [if_pos hc]; exact hp

lemma ite_of_false {c : Prop} [Decidable c] {p q : Prop} :
    ¬ c → q → if c then p else q := by
  intro hc hp; rw [if_neg hc]; exact hp
lemma of_genericCall {evm : Evm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {input_index input_size output_index output_size : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {lim : Nat} {ex : Execution}
    (notLimited : ¬ ex.Limited)
    ( eq :
      genericCall false evm gas value caller target codeAddress
        shouldTransferValue isStaticcall input_index input_size
        output_index output_size code disablePrecompiles lim = ex ) :
    ∃ xl : Xlot,
      xl.Good lim ex.toError? ∧
      GenericCall evm gas value caller target codeAddress
        shouldTransferValue isStaticcall input_index input_size
        output_index output_size code disablePrecompiles xl ex := by
  rcases lim with _ | lim <;> simp only [genericCall] at eq
  {rw [← eq] at notLimited; cases notLimited rfl}
  okStep1 eq _; split at eq
  { rename_i pos; refine' ⟨.none, .intro, _⟩
    simp only [bind_pure] at eq; rw [if_pos pos, eq] }
  rename_i neg
  apply Exists.imp (λ _ (h' : _ ∧ _) => ⟨h'.1, ite_of_false neg h'.2⟩);
  simp only [pure_bind] at eq
  okStep1 eq _; okStep1 eq msg
  have notLimited' :
    (processMessage false msg lim).toError? ≠ some "RecursionLimit" := by
    intro pm_eq
    rcases Except.of_toError?_eq_some _ _ pm_eq with ⟨_, rw⟩
    rw [← eq, rw] at notLimited
    cases notLimited rfl
  rcases of_processMessage msg lim _ notLimited' rfl
    with ⟨xl, good, pm⟩
  refine' ⟨_, Xlot.good_of_good_of_notLimited (by omega) notLimited' good, _, pm, _⟩
  bind_step' eq _
  split at eq
  · rename_i pos; rw [if_pos pos]; bind_step' eq _; exact eq
  · rename_i neg; rw [if_neg neg]; bind_step' eq _; exact eq

lemma of_processCreateMessage (msg : Msg) (lim : Nat)
    (ex : Except (String × Benv × Tenv) Evm)
    (notLimited : ex.toError? ≠ some "RecursionLimit")
    (eq : processCreateMessage false msg lim = ex) :
    ∃ xl : Xlot,
      xl.Good lim ex.toError? ∧
      ProcessCreateMessage msg xl ex := by
  rcases lim with _ | lim <;> simp only [processCreateMessage] at eq
  {rw [← eq] at notLimited; cases notLimited rfl}
  have notLimited' :
    (processMessage false (processCreateMessage.msg msg) lim).toError?
      ≠ some "RecursionLimit" := by
    intro pm_eq
    rcases Except.of_toError?_eq_some _ _ pm_eq with ⟨_, rw⟩
    rw [← eq, rw] at notLimited
    cases notLimited rfl
  rcases @of_processMessage _ _ _ notLimited' rfl
    with ⟨xl, good, pcm⟩
  refine' ⟨_, Xlot.good_of_good_of_notLimited (by omega) notLimited' good, _, pcm, _⟩
  bind_step' eq evm'
  split at eq
  · rename_i pos; rw [if_pos pos]
    cases pcm_eq : processCreateMessage.chargeCodeGas evm'
    · simp only []
      rw [pcm_eq] at eq
      simp only [] at eq
      split at eq
      · rename_i pos; rw [if_pos pos]; exact eq
      · rename_i neg; rw [if_neg neg]; exact eq
    · rw [pcm_eq] at eq; exact eq
  · rename_i neg; rw [if_neg neg]; exact eq

lemma of_genericCreate
    {evm : Evm} {endow : B256} {newAdr : Adr}
    {memIndex memSize lim : ℕ} {ex : Execution}
    (notLimited : ex.toError? ≠ some "RecursionLimit")
    (eq : genericCreate false evm endow newAdr memIndex memSize lim = ex) :
    ∃ xl : Xlot,
      xl.Good lim ex.toError? ∧
      GenericCreate evm endow newAdr memIndex memSize xl ex := by
  rcases lim with _ | lim <;> simp only [genericCreate] at eq
  {rw [← eq] at notLimited; cases notLimited rfl}
  okStep1 eq _; bind_step_good eq _; okStep1 eq _; okStep1 eq _
  okStep1 eq _; bind_step_good eq _; okStep1 eq _; okStep1 eq _
  split at eq
  · rename_i pos
    apply Exists.imp (λ _ (conj : _ ∧ _) => ⟨conj.1, ite_of_true pos conj.2⟩)
    rcases of_bind_eq eq with ⟨es, push_eq, ex_eq⟩ | ⟨evm, push_eq, eq_ex⟩;
    · refine' ⟨.none, .intro, _⟩; rw [ex_eq]; exact push_eq
    · refine' ⟨.none, .intro, _⟩; rw [← eq_ex]; exact push_eq
  · rename_i neg
    apply Exists.imp (λ _ (conj : _ ∧ _) => ⟨conj.1, ite_of_false neg conj.2⟩)
    clear neg; simp at eq
    okStep1 eq evm'
    split at eq
    · rename_i pos
      apply Exists.imp (λ _ (conj : _ ∧ _) => ⟨conj.1, ite_of_true pos conj.2⟩)
      refine' ⟨.none, .intro, eq⟩
    · rename_i neg
      apply Exists.imp (λ _ (conj : _ ∧ _) => ⟨conj.1, ite_of_false neg conj.2⟩)
      clear neg
      okStep1 eq msg
      have notLimited' :
          (processCreateMessage false msg lim).toError?
            ≠ some "RecursionLimit" := by
        intro pm_eq
        rcases Except.of_toError?_eq_some _ _ pm_eq with ⟨_, rw⟩
        rw [← eq, rw] at notLimited; cases notLimited rfl
      rcases of_processCreateMessage _ _ _ notLimited' rfl
        with ⟨xl, good, pm⟩
      refine' ⟨_, Xlot.good_of_good_of_notLimited (by omega) notLimited' good, _, pm, _⟩
      bind_step' eq _
      split at eq
      · rename_i pos; rw [if_pos pos]; exact eq
      · rename_i neg; rw [if_neg neg]; exact eq

def Ninst.Run' (evm : Evm) : Ninst → Xlot → Execution → Prop
  | .push xs _, _, ex =>
    ( do
        let evm1 ← chargeGas (if xs = [] then gBase else gVerylow) evm
        let evm2 ← evm1.push xs.toB256
        .ok {evm2 with pc := evm2.pc + xs.length + 1} ) = ex
  | .reg r, _, ex =>
    r.run evm = ex
  | .exec .create, xl, ex =>
      (evm.pop).Split ex <|
    λ ⟨endowment, evm1⟩ =>
      (evm1.popToNat).Split ex <|
    λ ⟨memoryIndex, evm2⟩ =>
      (evm2.popToNat).Split ex <|
    λ ⟨memorySize, evm3⟩ =>
    ∃ extendCost,
      And (extendCost = evm3.extCost [⟨memoryIndex, memorySize⟩]) <|
    ∃ initCodeCost,
      And (initCodeCost = gasInitCodeWordCost * (ceilDiv memorySize 32)) <|
      (chargeGas (gasCreate + extendCost + initCodeCost) evm3).Split ex <|
    λ evm4 =>
    ∃ evm5,
      And (evm5 = evm4.memExtends [⟨memoryIndex, memorySize⟩]) <|
    ∃ newAddress,
      And (newAddress = compute_contract_address evm5.contract (evm5.msg.benv.state.get evm5.contract).nonce) <|
    ∃ ex',
      And (GenericCreate evm5 endowment newAddress memoryIndex memorySize xl ex') <|
      ex'.Split ex <|
    λ evm6 =>
      evm6.incrPc = ex
  | .exec .create2, xl, ex =>
      (evm.pop).Split ex <|
    λ ⟨endowment, evm1⟩ =>
      (evm1.popToNat).Split ex <|
    λ ⟨memoryIndex, evm2⟩ =>
      (evm2.popToNat).Split ex <|
    λ ⟨memorySize, evm3⟩ =>
      (evm3.pop).Split ex <|
    λ ⟨salt, evm4⟩ =>
    ∃ extendCost,
      And (extendCost = evm4.extCost [⟨memoryIndex, memorySize⟩]) <|
    ∃ initCodeHashCost,
      And (initCodeHashCost = gasKeccak256Word * ceilDiv memorySize 32) <|
    ∃ initCodeCost,
      And (initCodeCost = gasInitCodeWordCost * (ceilDiv memorySize 32)) <|
      (chargeGas (gasCreate + initCodeHashCost + extendCost + initCodeCost) evm4).Split ex <|
    λ evm5 =>
    ∃ evm6,
      And (evm6 = evm5.memExtends [⟨memoryIndex, memorySize⟩]) <|
    ∃ newAddress,
      And (newAddress = create2NewAddress evm6.contract salt (evm6.memory.data.sliceD memoryIndex memorySize 0)) <|
    ∃ ex',
      And (GenericCreate evm6 endowment newAddress memoryIndex memorySize xl ex') <|
      ex'.Split ex <|
    λ evm7 =>
      evm7.incrPc = ex
  | .exec .call, xl, ex =>
      (evm.pop).Split ex <|
    λ ⟨gas, evm1⟩ =>
      (evm1.popToAdr).Split ex <|
    λ ⟨callee, evm2⟩ =>
      (evm2.pop).Split ex <|
    λ ⟨value, evm3⟩ =>
      (evm3.popToNat).Split ex <|
    λ ⟨inputIndex, evm4⟩ =>
      (evm4.popToNat).Split ex <|
    λ ⟨inputSize, evm5⟩ =>
      (evm5.popToNat).Split ex <|
    λ ⟨outputIndex, evm6⟩ =>
      (evm6.popToNat).Split ex <|
    λ ⟨outputSize, evm7⟩ =>
    ∃ extendCost,
      And (extendCost = evm7.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]) <|
    ∃ preAccessCost,
      And (preAccessCost = access_cost callee evm7.accessedAddresses) <|
    ∃ evm8,
      And (evm8 = addAccessedAddress evm7 callee) <|
    ∃ disablePrecompiles codeAdr code delegatedAccessGasCost evm9,
      And
        ( ⟨disablePrecompiles, codeAdr, code, delegatedAccessGasCost, evm9⟩ =
          accessDelegation evm8 callee ) <|
    ∃ accessCost,
      And (accessCost = preAccessCost + delegatedAccessGasCost) <|
    ∃ createCost,
      And (createCost = if (¬ (evm9.getAcct callee).Empty) ∨ value = 0 then 0 else gNewAccount) <|
    ∃ transferCost,
      And (transferCost = if value = 0 then 0 else gasCallValue) <|
    ∃ msgCallCost msgCallStipend,
      And (⟨msgCallCost, msgCallStipend⟩ = calculate_msg_call_gas value.toNat gas.toNat evm9.gasLeft extendCost (accessCost + createCost + transferCost)) <|
      (chargeGas (msgCallCost + extendCost) evm9).Split ex <|
    λ evm10 =>
      (Except.assert (!evm10.msg.isStatic ∨ value = 0) ⟨"WriteInStaticContext", evm10⟩).Split ex <|
    λ _ =>
    ∃ evm11,
      And (evm11 = evm10.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]) <|
    ∃ senderBal,
      And (senderBal = (evm11.getAcct evm11.contract).bal) <|
    if senderBal < value then
        (evm11.push 0).Split ex <|
      λ evm12 =>
        { evm12 with
          returnData := []
          gasLeft := evm12.gasLeft + msgCallStipend }.incrPc = ex
    else
      ∃ ex',
        And
          ( GenericCall evm11 msgCallStipend value evm11.contract callee
            callee true false inputIndex inputSize outputIndex outputSize
            code disablePrecompiles xl ex' ) <|
        ex'.Split ex <|
      λ evm12 =>
        evm12.incrPc = ex
  | .exec .callcode, xl, ex =>
      (evm.pop).Split ex <|
    λ ⟨gas, evm1⟩ =>
      (evm1.popToAdr).Split ex <|
    λ ⟨codeAddress, evm2⟩ =>
      (evm2.pop).Split ex <|
    λ ⟨value, evm3⟩ =>
      (evm3.popToNat).Split ex <|
    λ ⟨inputIndex, evm4⟩ =>
      (evm4.popToNat).Split ex <|
    λ ⟨inputSize, evm5⟩ =>
      (evm5.popToNat).Split ex <|
    λ ⟨outputIndex, evm6⟩ =>
      (evm6.popToNat).Split ex <|
    λ ⟨outputSize, evm7⟩ =>
    ∃ target,
      And (target = evm7.contract) <|
    ∃ extendCost,
      And (extendCost = evm7.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]) <|
    ∃ preAccessCost,
      And (preAccessCost = access_cost codeAddress evm7.accessedAddresses) <|
    ∃ evm8,
      And (evm8 = addAccessedAddress evm7 codeAddress) <|
    ∃ disablePrecompiles newCodeAddress code delegatedAccessGasCost evm9,
      And (⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, evm9⟩ = accessDelegation evm8 codeAddress) <|
    ∃ accessCost,
      And (accessCost = preAccessCost + delegatedAccessGasCost) <|
    ∃ transferCost,
      And (transferCost = if value = 0 then 0 else gasCallValue) <|
    ∃ msgCallCost msgCallStipend,
      And (⟨msgCallCost, msgCallStipend⟩ = calculate_msg_call_gas value.toNat gas.toNat evm9.gasLeft extendCost (accessCost + transferCost)) <|
      (chargeGas (msgCallCost + extendCost) evm9).Split ex <|
    λ evm10 =>
    ∃ evm11,
      And (evm11 = evm10.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]) <|
    ∃ senderBal,
      And (senderBal = (evm11.getAcct evm11.contract).bal) <|
    if senderBal < value then
        (evm11.push 0).Split ex <|
      λ evm12 =>
        {evm12 with returnData := [], gasLeft := evm12.gasLeft + msgCallStipend}.incrPc = ex
    else
      ∃ ex',
        And
          ( GenericCall evm11 msgCallStipend value evm11.contract target
            newCodeAddress true false inputIndex inputSize outputIndex outputSize
            code disablePrecompiles xl ex' ) <|
        ex'.Split ex <|
      λ evm12 =>
        evm12.incrPc = ex
  | .exec .delcall, xl, ex =>
      (evm.pop).Split ex <|
    λ ⟨gas, evm1⟩ =>
      (evm1.popToAdr).Split ex <|
    λ ⟨codeAddress, evm2⟩ =>
      (evm2.popToNat).Split ex <|
    λ ⟨inputIndex, evm3⟩ =>
      (evm3.popToNat).Split ex <|
    λ ⟨inputSize, evm4⟩ =>
      (evm4.popToNat).Split ex <|
    λ ⟨outputIndex, evm5⟩ =>
      (evm5.popToNat).Split ex <|
    λ ⟨outputSize, evm6⟩ =>
    ∃ extendCost,
      And (extendCost = evm6.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]) <|
    ∃ preAccessCost,
      And (preAccessCost = access_cost codeAddress evm6.accessedAddresses) <|
    ∃ evm7,
      And (evm7 = addAccessedAddress evm6 codeAddress) <|
    ∃ disablePrecompiles newCodeAddress code delegatedAccessGasCost evm8,
      And (⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, evm8⟩ = accessDelegation evm7 codeAddress) <|
    ∃ accessCost,
      And (accessCost = preAccessCost + delegatedAccessGasCost) <|
    ∃ msgCallCost msgCallStipend,
      And (⟨msgCallCost, msgCallStipend⟩ = calculate_msg_call_gas 0 gas.toNat evm8.gasLeft extendCost accessCost) <|
      (chargeGas (msgCallCost + extendCost) evm8).Split ex <|
    λ evm9 =>
    ∃ evm10,
      And (evm10 = evm9.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]) <|
    ∃ ex',
      And
        ( GenericCall evm10 msgCallStipend evm10.msg.value evm10.msg.caller
          evm10.contract newCodeAddress false false inputIndex inputSize outputIndex
          outputSize code disablePrecompiles xl ex' ) <|
      ex'.Split ex <|
    λ evm11 =>
    evm11.incrPc = ex
  | .exec .statcall, xl, ex =>
      (evm.pop).Split ex <|
    λ ⟨gas, evm1⟩ =>
      (evm1.popToAdr).Split ex <|
    λ ⟨target, evm2⟩ =>
      (evm2.popToNat).Split ex <|
    λ ⟨inputIndex, evm3⟩ =>
      (evm3.popToNat).Split ex <|
    λ ⟨inputSize, evm4⟩ =>
      (evm4.popToNat).Split ex <|
    λ ⟨outputIndex, evm5⟩ =>
      (evm5.popToNat).Split ex <|
    λ ⟨outputSize, evm6⟩ =>
    ∃ extendCost,
      And (extendCost = evm6.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]) <|
    ∃ preAccessCost,
      And (preAccessCost = access_cost target evm6.accessedAddresses) <|
    ∃ evm7,
      And (evm7 = addAccessedAddress evm6 target) <|
    ∃ disablePrecompiles codeAdr code delegatedAccessGasCost evm8,
      And (⟨disablePrecompiles, codeAdr, code, delegatedAccessGasCost, evm8⟩ = accessDelegation evm7 target) <|
    ∃ accessCost,
      And (accessCost = preAccessCost + delegatedAccessGasCost) <|
    ∃ msgCallCost msgCallStipend,
      And (⟨msgCallCost, msgCallStipend⟩ = calculate_msg_call_gas 0 gas.toNat evm8.gasLeft extendCost accessCost) <|
      (chargeGas (msgCallCost + extendCost) evm8).Split ex <|
    λ evm9 =>
    ∃ evm10,
      And (evm10 = evm9.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]) <|
    ∃ ex',
      And
        ( GenericCall evm10 msgCallStipend 0 evm10.contract target target true true
          inputIndex inputSize outputIndex outputSize code disablePrecompiles xl ex' ) <|
      ex'.Split ex <|
    λ evm11 =>
      evm11.incrPc = ex


lemma Except.bind_eq_bind {ξ υ ζ} {e : Except ξ υ} {f g : υ → Except ξ ζ}
    (eq : ∀ x, e = Except.ok x → f x = g x) : e >>= f = e >>= g := by
  cases e; rfl; apply eq _ rfl

def ok_bind {ξ : Type u} {υ ζ : Type v} {y : υ} {g : υ → Except ξ ζ} :
    (.ok y) >>= g = g y := rfl


syntax "eee_bind " ident  : tactic
macro_rules
  | `(tactic| eee_bind $unlim) => `(tactic|

      apply Except.bind_eq_bind;
      intro _ eq_ok;
      have temp := $unlim; clear $unlim;
      have $unlim :=
        @Eq.subst _ (Except.Unlim) _ _ ok_bind <|
          @Eq.subst _ (λ e => Except.Unlim (e >>= _)) _ _ eq_ok temp;
      clear temp eq_ok
    )

lemma of_unlim_liftToExecution {evm : Evm}
    {f : Except (String × Benv × Tenv) Evm} :
    (liftToExecution evm f).Unlim → f.Unlim := by
  rcases f with ⟨err, _⟩ | _ <;> intro unlim ltd
  · injection ltd; rename_i rw; rw [rw] at unlim; cases unlim rfl
  · cases ltd

def Saturates {ξ υ} (n : Nat) (f : Nat → Except (String × ξ) υ) : Prop :=
  (f n).Unlim → ∀ m, n < m → (f n = f m)

structure Saturation (lim : Nat) : Prop where
  (executeCode : ∀ (msg : Msg), Saturates lim (executeCode false msg))
  (processMessage : ∀ (msg : Msg), Saturates lim (processMessage false msg))
  ( processCreateMessage :
    ∀ (msg : Msg), Saturates lim (processCreateMessage false msg) )
  ( genericCreate :
    ∀ (evm : Evm) (endowment : B256) (newAddress : Adr)
      (memoryIndex : Nat) (memorySize : Nat),
      Saturates lim
        (genericCreate false evm endowment newAddress memoryIndex memorySize) )
  ( genericCall :
    ∀ (evm : Evm) (gas : Nat) (value : B256) (caller : Adr) (target : Adr)
      (codeAddress : Adr) (shouldTransferValue : Bool) (isStaticcall : Bool)
      (inputIndex :Nat) (inputSize : Nat) (outputIndex : Nat)
      (outputSize : Nat) (code : ByteArray) (disablePrecompiles: Bool),
      Saturates lim
        ( genericCall false evm gas value caller target codeAddress
            shouldTransferValue isStaticcall inputIndex inputSize outputIndex
            outputSize code disablePrecompiles ) )
  (run : ∀ (evm : Evm) (n : Ninst), Saturates lim (Ninst.run false evm n))
  (exec : ∀ (evm : Evm), Saturates lim (exec false evm))

lemma saturation (lim : Nat) : Saturation lim := by
  induction lim
  case zero =>
    refine' ⟨_, _, _, _, _, _, _⟩
    · intro _ unlim; simp only [executeCode] at unlim; cases unlim rfl
    · intro _ unlim; simp only [processMessage] at unlim; cases unlim rfl
    · intro _ unlim; simp only [processCreateMessage] at unlim; cases unlim rfl
    · intro _ _ _ _ _ unlim; simp only [genericCreate] at unlim; cases unlim rfl
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ unlim;
      simp only [genericCall] at unlim; cases unlim rfl
    · intro _ n unlim; cases n
      · simp only [Ninst.run, implies_true]
      · simp only [Ninst.run] at unlim; cases unlim rfl
      · simp only [Ninst.run, implies_true]
    · intro _ unlim; simp only [exec] at unlim; cases unlim rfl
  case succ lim ih =>
    refine' ⟨_, _, _, _, _, _, _⟩
    · intro _ unlim lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      simp only [executeCode] at *
      split at unlim
      · rw [ih.exec _ (limited_handleError.mt unlim) lim' (by omega)]
      · split at unlim
        · rename_i pos; rw [if_pos pos, if_pos pos]
        · rename_i neg; rw [if_neg neg, if_neg neg]
          rw [ih.exec _ (limited_handleError.mt unlim) lim' (by omega)]
    · intro _ unlim lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      simp only [processMessage] at *
      eee_bind unlim; eee_bind unlim
      rw [ih.executeCode _ (of_unlim_bind unlim).1 lim' (by omega)]
    · intro _ unlim lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      simp only [processCreateMessage] at *
      rw [ih.processMessage _ (of_unlim_bind unlim).1 lim' (by omega)]
    · intro _ _ _ _ _ unlim lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      simp only [genericCreate] at *
      iterate 8 (eee_bind unlim);
      split; {rfl}
      rename_i neg; rw [if_neg neg] at unlim; clear neg
      eee_bind unlim; eee_bind unlim; split; {rfl}
      rename_i neg; rw [if_neg neg] at unlim; clear neg
      eee_bind unlim; eee_bind unlim
      have unlim' := of_unlim_liftToExecution (of_unlim_bind unlim).1
      rw [ih.processCreateMessage _ unlim' lim' (by omega)]
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ unlim lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      simp only [genericCall] at *
      eee_bind unlim; split at unlim
      · rename_i pos; rw [if_pos pos, if_pos pos]
      · rename_i neg; rw [if_neg neg, if_neg neg]
        iterate 3 (eee_bind unlim)
        have unlim' := of_unlim_liftToExecution (of_unlim_bind unlim).1
        rw [ih.processMessage _ unlim' lim' (by omega)]
    · intro _ n unlim lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      rcases n  with _ | (_ | _ | _ | _ | _ | _) | _ <;>
        simp only [Ninst.run] at *
      · iterate 8 (eee_bind unlim)
        rw [ih.genericCreate _ _ _ _ _ (of_unlim_bind unlim).1 lim' (by omega)]
      · iterate 19 (eee_bind unlim)
        split; {rfl}; rename_i neg
        rw [if_neg neg] at unlim; clear neg
        rw [ ih.genericCall _ _ _ _ _ _ _ _ _ _ _ _ _ _
             (of_unlim_bind unlim).1 lim' (by omega) ]
      · iterate 18 (eee_bind unlim)
        split; {rfl}; rename_i neg
        rw [if_neg neg] at unlim; clear neg
        rw [ ih.genericCall _ _ _ _ _ _ _ _ _ _ _ _ _ _
             (of_unlim_bind unlim).1 lim' (by omega) ]
      · iterate 14 (eee_bind unlim)
        rw [ ih.genericCall _ _ _ _ _ _ _ _ _ _ _ _ _ _
             (of_unlim_bind unlim).1 lim' (by omega) ]
      · iterate 10 (eee_bind unlim)
        rw [ih.genericCreate _ _ _ _ _ (of_unlim_bind unlim).1 lim' (by omega)]
      · iterate 14 (eee_bind unlim)
        rw [ ih.genericCall _ _ _ _ _ _ _ _ _ _ _ _ _ _
             (of_unlim_bind unlim).1 lim' (by omega) ]
    · intro _ unlim lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      simp only [exec] at *; eee_bind unlim; split
      · simp only at unlim
        rw [← ih.run _ _ (of_unlim_bind unlim).1 lim' (by omega)]
        eee_bind unlim; apply ih.exec _ unlim lim' (by omega)
      · simp only at unlim; eee_bind unlim
        apply ih.exec _ unlim lim' (by omega)
      · rfl











/-
lemma forall_eq_of_le_of_unlim :
    ∀ (lim lim' : Nat),
      lim ≤ lim' →
      ( ∀ (msg : Msg),
          (executeCode false msg lim).Unlim →
          (executeCode false msg lim = executeCode false msg lim') ) ∧
      ( ∀ (msg : Msg),
          (processMessage false msg lim).Unlim →
          (processMessage false msg lim = processMessage false msg lim') ) ∧
      ( ∀ (msg : Msg),
          (processCreateMessage false msg lim).Unlim →
          (processCreateMessage false msg lim = processCreateMessage false msg lim') ) ∧
      ( ∀ (evm : Evm) (endowment : B256) (newAddress : Adr)
          (memoryIndex : Nat) (memorySize : Nat),
          (genericCreate false evm endowment newAddress memoryIndex memorySize lim).Unlim →
          (genericCreate false evm endowment newAddress memoryIndex memorySize lim) =
          (genericCreate false evm endowment newAddress memoryIndex memorySize lim') ) ∧
      ( ∀ (evm : Evm) (gas : Nat) (value : B256) (caller : Adr) (target : Adr)
          (codeAddress : Adr) (shouldTransferValue : Bool) (isStaticcall : Bool)
          (inputIndex :Nat) (inputSize : Nat) (outputIndex : Nat)
          (outputSize : Nat) (code : ByteArray) (disablePrecompiles: Bool),
          ( genericCall false evm gas value caller target codeAddress
              shouldTransferValue isStaticcall inputIndex inputSize outputIndex
              outputSize code disablePrecompiles lim ).Unlim →
          ( genericCall false evm gas value caller target codeAddress
              shouldTransferValue isStaticcall inputIndex inputSize
              outputIndex outputSize code disablePrecompiles lim =
            genericCall false evm gas value caller target codeAddress
              shouldTransferValue isStaticcall inputIndex inputSize
              outputIndex outputSize code disablePrecompiles lim' ) ) ∧
      ( ∀ (evm : Evm) (n : Ninst),
          (Ninst.run false evm n lim).Unlim →
          (Ninst.run false evm n lim = Ninst.run false evm n lim') ) ∧
      ( ∀ (evm : Evm),
          (exec false evm lim).Unlim →
          (exec false evm lim = exec false evm lim') ) := by
  apply Nat.rec
  · intro lim' le
    refine' ⟨_, _, _, _, _, _, _⟩
    · simp only [Nat.zero_eq, executeCode]; intro _ unlim; cases unlim rfl
    · simp only [Nat.zero_eq, processMessage]; intro _ unlim; cases unlim rfl
    · simp only [Nat.zero_eq, processCreateMessage]; intro _ unlim; cases unlim rfl
    · simp only [Nat.zero_eq, genericCreate]
      intro _ _ _ _ _ unlim; cases unlim rfl
    · simp only [Nat.zero_eq, genericCall]
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ unlim; cases unlim rfl
    · simp only [Nat.zero_eq]
      intro _ n unlim; cases n
      · simp [Ninst.run]
      · simp [Ninst.run] at unlim; cases unlim rfl
      · simp [Ninst.run]
    · simp only [Nat.zero_eq, exec]; intro _ unlim; cases unlim rfl
  · intro lim ih lim' le
    rcases lim' with _ | lim'; {cases Nat.not_succ_le_zero  _ le}
    refine' ⟨_, _, _, _, _, _, _⟩
    · simp only [executeCode]; intro msg unlim
      have ih' :=
        (ih lim' (by omega)).right.right.right.right.right.right (initEvm msg)
      clear ih
      split at unlim
      · rw [ih' <| limited_handleError.mt unlim]
      · split at unlim
        · rename_i pos; rw [if_pos pos, if_pos pos]
        · rename_i neg; rw [if_neg neg, if_neg neg]
          rw [ih' <| limited_handleError.mt unlim]
    · simp only [processMessage]; intro msg unlim
      eee_bind unlim; eee_bind unlim
      rw [(ih lim' (by omega)).1 _ (of_unlim_bind unlim).1]
    · have ih' := (ih lim' (by omega)).right.left
      clear ih;
      intro msg unlim
      simp only [processCreateMessage]
      simp only [processCreateMessage] at unlim
      rw [ih' _ (of_unlim_bind unlim).1]
    · have ih' := (ih lim' (by omega)).right.right.left
      clear ih; simp only [genericCreate]
      intro _ _ _ _ _ unlim
      eee_bind unlim; eee_bind unlim; eee_bind unlim
      eee_bind unlim; eee_bind unlim; eee_bind unlim
      eee_bind unlim; eee_bind unlim; split
      · rfl
      · rename_i neg
        rw [if_neg neg] at unlim; clear neg
        eee_bind unlim; eee_bind unlim; split
        · rfl
        · rename_i neg
          rw [if_neg neg] at unlim; clear neg
          eee_bind unlim; eee_bind unlim
          rw [ih' _ <| of_unlim_liftToExecution (of_unlim_bind unlim).1]
    · have ih' := (ih lim' (by omega)).right.left
      clear ih; simp only [genericCall]
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ unlim
      eee_bind unlim; split at unlim
      · rename_i pos; rw [if_pos pos, if_pos pos]
      · rename_i neg; rw [if_neg neg, if_neg neg]
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        rw [ih' _ <| of_unlim_liftToExecution (of_unlim_bind unlim).1]
    · have ih_call := (ih lim' (by omega)).right.right.right.right.left
      have ih_create := (ih lim' (by omega)).right.right.right.left
      clear ih; intro _ n unlim;
      rcases n  with _ | (_ | _ | _ | _ | _ | _) | _ <;> simp only [Ninst.run]
      · rename (Except.Unlim _) => unlim
        simp only [Ninst.run] at unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim
        rw [ih_create _ _ _ _ _ (of_unlim_bind unlim).1]
      · simp only [Ninst.run] at unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; split; {rfl}
        rename_i neg; rw [if_neg neg] at unlim; clear neg
        rw [ih_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ (of_unlim_bind unlim).1]
      · simp only [Ninst.run] at unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        split; {rfl}; rename_i neg; rw [if_neg neg] at unlim; clear neg
        rw [ih_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ (of_unlim_bind unlim).1]
      · simp only [Ninst.run] at unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim;
        rw [ih_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ (of_unlim_bind unlim).1]
      · simp only [Ninst.run] at unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim;
        rw [ih_create _ _ _ _ _ (of_unlim_bind unlim).1]
      · simp only [Ninst.run] at unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim; eee_bind unlim
        eee_bind unlim; eee_bind unlim;
        rw [ih_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ (of_unlim_bind unlim).1]
    · simp only [exec]; intro _ unlim; eee_bind unlim; split
      · have ih' := (ih lim' (by omega)).right.right.right.right.right.left
        have ih'' := (ih lim' (by omega)).right.right.right.right.right.right
        clear ih; simp at unlim; rw [← ih' _ _ (of_unlim_bind unlim).1]
        eee_bind unlim; apply ih'' _ unlim
      · have ih'' := (ih lim' (by omega)).right.right.right.right.right.right
        clear ih; simp only at unlim; eee_bind unlim; apply ih'' _ unlim
      · rfl
-/





-- lemma Ninst.of_run {evm : Evm} {n : Ninst} {lim : Nat}
--     {ex : Execution} (notLimited : ex.Unlim)
--     (eq : Ninst.run false evm n lim = ex) :
--     (∀ lim' ≥ lim, Ninst.run false evm n lim' = ex) ∧
--     ∃ xl : Xlot,
--       xl.Good lim ex.toError? ∧
--       Ninst.Run' evm n xl ex :=
--   match n, lim with
--   | exec _, 0 => by
--     simp only [Ninst.run] at eq
--     rw [← eq] at notLimited
--     cases notLimited rfl
--   | push xs lt, lim => by
--     simp [Ninst.run] at eq; simp [Ninst.run]
--     refine' ⟨λ _ _ => eq, .none, .intro, eq⟩
--   | reg r, _ => by
--     simp [Ninst.run] at eq; simp [Ninst.run]
--     refine' ⟨λ _ _ => eq, .none, .intro, eq⟩
--   | exec .create, lim + 1 => by
--     simp [Ninst.run] at eq; simp [Ninst.Run']
--     constructor
--     · intro lim' ge; rcases lim' with _ | lim'
--       {cases Nat.not_succ_le_zero _ ge}
--       simp [run]
--   | reg r, _ => sorry


lemma Ninst.of_run {evm : Evm} {n : Ninst} {lim : Nat}
    {ex : Execution} (notLimited : ex.Unlim)
    (eq : Ninst.run false evm n lim = ex) :
    ∃ xl : Xlot,
      xl.Good lim ex.toError? ∧
      Ninst.Run' evm n xl ex :=
  match n, lim with
  | exec _, 0 => by
    simp only [Ninst.run] at eq
    rw [← eq] at notLimited
    cases notLimited rfl
  | push xs lt, lim => by
    refine' ⟨.none, .intro, _⟩
    simp only [Ninst.run] at eq; apply eq
  | reg r, _ => by
    simp [Ninst.run] at eq
    refine' ⟨.none, .intro, eq⟩
  | exec .create, lim + 1 => by
    simp only [Ninst.run] at eq
    bind_step_good eq _; bind_step_good eq _; bind_step_good eq _; okStep1 eq _;
    okStep1 eq _; bind_step_good eq _; okStep1 eq _; okStep1 eq _;
    have notLimited' := Execution.notLimited_of_notLimited notLimited eq
    rcases of_genericCreate notLimited' rfl with ⟨xl, good, gc⟩
    refine' ⟨_, Xlot.good_of_good_of_notLimited (by omega) notLimited' good, _, gc, _⟩
    bind_step' eq _; exact eq
  | exec .create2, lim + 1 => by
    simp only [Ninst.run] at eq
    bind_step_good eq _; bind_step_good eq _; bind_step_good eq _;
    bind_step_good eq _; okStep1 eq _; okStep1 eq _; okStep1 eq _;
    bind_step_good eq _; okStep1 eq _; okStep1 eq _;
    have notLimited' := Execution.notLimited_of_notLimited notLimited eq
    rcases of_genericCreate notLimited' rfl with ⟨xl, good, gc⟩
    refine' ⟨_, Xlot.good_of_good_of_notLimited (by omega) notLimited' good, _, gc, _⟩
    bind_step' eq _; exact eq
  | exec .call, lim + 1 => by
    simp only [Ninst.run] at eq
    bind_step_good eq _; bind_step_good eq _; bind_step_good eq _;
    bind_step_good eq _; bind_step_good eq _; bind_step_good eq _;
    bind_step_good eq _; okStep1 eq _; okStep1 eq _; okStep1 eq _;
    okStep5 eq _ _ _ _ _; okStep1 eq _; okStep1 eq _; okStep1 eq _;
    okStep2 eq _ _; bind_step_good eq _; bind_step_good eq _;
    okStep1 eq _; okStep1 eq _; split at eq
    · rename_i lt
      refine' ⟨.none, .intro, _⟩
      rw [if_pos lt]
      bind_step' eq _; exact eq
    · rename_i nlt
      apply Exists.imp (λ _ (conj : _ ∧ _) => ⟨conj.1, ite_of_false nlt conj.2⟩)
      have notLimited' := Execution.notLimited_of_notLimited notLimited eq
      rcases of_genericCall notLimited' rfl with ⟨xl, good, gc⟩
      refine' ⟨_, Xlot.good_of_good_of_notLimited (by omega) notLimited' good, _, gc, _⟩
      bind_step' eq _; exact eq
  | exec .callcode, lim + 1 => by
    simp only [Ninst.run] at eq
    bind_step_good eq _; bind_step_good eq _; bind_step_good eq _;
    bind_step_good eq _; bind_step_good eq _; bind_step_good eq _;
    bind_step_good eq _; okStep1 eq _; okStep1 eq _; okStep1 eq _;
    okStep1 eq _; okStep5 eq _ _ _ _ _; okStep1 eq _; okStep1 eq _;
    okStep2 eq _ _; bind_step_good eq _; okStep1 eq _; okStep1 eq _;
    split at eq
    · rename_i lt; refine' ⟨.none, .intro, _⟩
      rw [if_pos lt]; bind_step' eq _; exact eq
    · rename_i nlt
      apply Exists.imp (λ _ (conj : _ ∧ _) => ⟨conj.1, ite_of_false nlt conj.2⟩)
      have notLimited' := Execution.notLimited_of_notLimited notLimited eq
      rcases of_genericCall notLimited' rfl with ⟨xl, good, gc⟩
      refine' ⟨_, Xlot.good_of_good_of_notLimited (by omega) notLimited' good, _, gc, _⟩
      bind_step' eq _; exact eq
  | exec .delcall, lim + 1 => by
    simp only [Ninst.run] at eq
    bind_step_good eq _; bind_step_good eq _; bind_step_good eq _;
    bind_step_good eq _; bind_step_good eq _; bind_step_good eq _;
    okStep1 eq _; okStep1 eq _; okStep1 eq _; okStep5 eq _ _ _ _ _;
    okStep1 eq _; okStep2 eq _ _; bind_step_good eq _; okStep1 eq _;
    have notLimited' := Execution.notLimited_of_notLimited notLimited eq
    rcases of_genericCall notLimited' rfl with ⟨xl, good, gc⟩
    refine' ⟨_, Xlot.good_of_good_of_notLimited (by omega) notLimited' good, _, gc, _⟩
    bind_step' eq _; exact eq
  | exec .statcall, lim + 1 => by
    simp only [Ninst.run] at eq
    bind_step_good eq _; bind_step_good eq _; bind_step_good eq _;
    bind_step_good eq _; bind_step_good eq _; bind_step_good eq _;
    okStep1 eq _; okStep1 eq _; okStep1 eq _; okStep5 eq _ _ _ _ _;
    okStep1 eq _; okStep2 eq _ _; bind_step_good eq _; okStep1 eq _;
    have notLimited' := Execution.notLimited_of_notLimited notLimited eq
    rcases of_genericCall notLimited' rfl with ⟨xl, good, gc⟩
    refine' ⟨_, Xlot.good_of_good_of_notLimited (by omega) notLimited' good, _, gc, _⟩
    bind_step' eq _; exact eq

lemma Ninst.run_of_run {evm : Evm} {n : Ninst} {lim : Nat}
    {ex : Execution} (notLimited : ¬ ex.Limited)
    (eq : Ninst.run false evm n lim = ex) :
    ∃ xl : Xlot,
      xl.Good lim ex.toError? ∧
      Ninst.Run' evm n xl ex :=
  match n, lim with
  | exec _, 0 => by
    simp only [Ninst.run] at eq
    rw [← eq] at notLimited
    cases notLimited rfl
  | push xs lt, lim => by
    refine' ⟨.none, .intro, _⟩
    simp only [Ninst.run] at eq; apply eq
  | reg r, _ => by
    simp [Ninst.run] at eq
    refine' ⟨.none, .intro, eq⟩
  | exec .create, lim + 1 => by
    simp only [Ninst.run] at eq
    bind_step_good eq _; bind_step_good eq _; bind_step_good eq _; okStep1 eq _;
    okStep1 eq _; bind_step_good eq _; okStep1 eq _; okStep1 eq _;
    have notLimited' := Execution.notLimited_of_notLimited notLimited eq
    rcases of_genericCreate notLimited' rfl with ⟨xl, good, gc⟩
    refine' ⟨_, Xlot.good_of_good_of_notLimited (by omega) notLimited' good, _, gc, _⟩
    bind_step' eq _; exact eq
  | exec .create2, lim + 1 => by
    simp only [Ninst.run] at eq
    bind_step_good eq _; bind_step_good eq _; bind_step_good eq _;
    bind_step_good eq _; okStep1 eq _; okStep1 eq _; okStep1 eq _;
    bind_step_good eq _; okStep1 eq _; okStep1 eq _;
    have notLimited' := Execution.notLimited_of_notLimited notLimited eq
    rcases of_genericCreate notLimited' rfl with ⟨xl, good, gc⟩
    refine' ⟨_, Xlot.good_of_good_of_notLimited (by omega) notLimited' good, _, gc, _⟩
    bind_step' eq _; exact eq
  | exec .call, lim + 1 => by
    simp only [Ninst.run] at eq
    bind_step_good eq _; bind_step_good eq _; bind_step_good eq _;
    bind_step_good eq _; bind_step_good eq _; bind_step_good eq _;
    bind_step_good eq _; okStep1 eq _; okStep1 eq _; okStep1 eq _;
    okStep5 eq _ _ _ _ _; okStep1 eq _; okStep1 eq _; okStep1 eq _;
    okStep2 eq _ _; bind_step_good eq _; bind_step_good eq _;
    okStep1 eq _; okStep1 eq _; split at eq
    · rename_i lt
      refine' ⟨.none, .intro, _⟩
      rw [if_pos lt]
      bind_step' eq _; exact eq
    · rename_i nlt
      apply Exists.imp (λ _ (conj : _ ∧ _) => ⟨conj.1, ite_of_false nlt conj.2⟩)
      have notLimited' := Execution.notLimited_of_notLimited notLimited eq
      rcases of_genericCall notLimited' rfl with ⟨xl, good, gc⟩
      refine' ⟨_, Xlot.good_of_good_of_notLimited (by omega) notLimited' good, _, gc, _⟩
      bind_step' eq _; exact eq
  | exec .callcode, lim + 1 => by
    simp only [Ninst.run] at eq
    bind_step_good eq _; bind_step_good eq _; bind_step_good eq _;
    bind_step_good eq _; bind_step_good eq _; bind_step_good eq _;
    bind_step_good eq _; okStep1 eq _; okStep1 eq _; okStep1 eq _;
    okStep1 eq _; okStep5 eq _ _ _ _ _; okStep1 eq _; okStep1 eq _;
    okStep2 eq _ _; bind_step_good eq _; okStep1 eq _; okStep1 eq _;
    split at eq
    · rename_i lt; refine' ⟨.none, .intro, _⟩
      rw [if_pos lt]; bind_step' eq _; exact eq
    · rename_i nlt
      apply Exists.imp (λ _ (conj : _ ∧ _) => ⟨conj.1, ite_of_false nlt conj.2⟩)
      have notLimited' := Execution.notLimited_of_notLimited notLimited eq
      rcases of_genericCall notLimited' rfl with ⟨xl, good, gc⟩
      refine' ⟨_, Xlot.good_of_good_of_notLimited (by omega) notLimited' good, _, gc, _⟩
      bind_step' eq _; exact eq
  | exec .delcall, lim + 1 => by
    simp only [Ninst.run] at eq
    bind_step_good eq _; bind_step_good eq _; bind_step_good eq _;
    bind_step_good eq _; bind_step_good eq _; bind_step_good eq _;
    okStep1 eq _; okStep1 eq _; okStep1 eq _; okStep5 eq _ _ _ _ _;
    okStep1 eq _; okStep2 eq _ _; bind_step_good eq _; okStep1 eq _;
    have notLimited' := Execution.notLimited_of_notLimited notLimited eq
    rcases of_genericCall notLimited' rfl with ⟨xl, good, gc⟩
    refine' ⟨_, Xlot.good_of_good_of_notLimited (by omega) notLimited' good, _, gc, _⟩
    bind_step' eq _; exact eq
  | exec .statcall, lim + 1 => by
    simp only [Ninst.run] at eq
    bind_step_good eq _; bind_step_good eq _; bind_step_good eq _;
    bind_step_good eq _; bind_step_good eq _; bind_step_good eq _;
    okStep1 eq _; okStep1 eq _; okStep1 eq _; okStep5 eq _ _ _ _ _;
    okStep1 eq _; okStep2 eq _ _; bind_step_good eq _; okStep1 eq _;
    have notLimited' := Execution.notLimited_of_notLimited notLimited eq
    rcases of_genericCall notLimited' rfl with ⟨xl, good, gc⟩
    refine' ⟨_, Xlot.good_of_good_of_notLimited (by omega) notLimited' good, _, gc, _⟩
    bind_step' eq _; exact eq


/- Exec evm ex is provable iff
    ∃ lim : Nat, ∀ vb : bool, exec vb lim evm = ex
   holds, and ex is not a recursion limit error case.  -/
inductive Exec : Evm → Execution → Type
  | invOp {evm : Evm} :
    evm.getInst = none →
    Exec evm (.error ⟨"InvalidOpcode", evm⟩)
  | nextNoneErr {evm : Evm} {n : Ninst} {exn : Execution} :
    n.At evm.code evm.pc →
    Ninst.Run' evm n .none exn →
    exn.IsError → Exec evm exn
  | nextSomeErr {evm : Evm} {n : Ninst}
    {evm' : Evm} {ex' : Execution } {exn : Execution} :
    n.At evm.code evm.pc→
    Ninst.Run' evm n (.some (evm', ex')) exn →
    Exec evm' ex' → exn.IsError → Exec evm exn
  | nextNoneRec {evm : Evm} {n : Ninst} {evm' : Evm} {exn : Execution} :
    n.At evm.code evm.pc→
    Ninst.Run' evm n .none (.ok evm') →
    Exec evm' exn → Exec evm exn
  | nextSomeRec {evm : Evm} {n : Ninst} {evm' : Evm}
    {exn' : Execution} {evm'' : Evm} {exn : Execution} :
    n.At evm.code evm.pc→
    Ninst.Run' evm n (.some (evm', exn')) (.ok evm'') →
    Exec evm' exn' → Exec evm'' exn → Exec evm exn
  | jumpErr {evm : Evm} {j : Jinst} {exn : Execution} :
    j.At evm.code evm.pc →
    Jinst.Run evm j exn →
    exn.IsError → Exec evm exn
  | jumpRec {evm : Evm} {j : Jinst} {evm' : Evm} {exn : Execution} :
    j.At evm.code evm.pc →
    Jinst.Run evm j (.ok evm') →
    Exec evm' exn → Exec evm exn
  | last {evm : Evm} {l : Linst} {exn : Execution} :
    l.At evm.code evm.pc → Linst.Run evm l exn → Exec evm exn

syntax "bind_step " ident rcasesPat : tactic
macro_rules
  | `(tactic| bind_step $h $pat) => `(tactic|
      rcases of_bind_eq $h with im | ⟨$pat, temp_eq, eq'⟩;
      { refine ⟨.none, .inl im, .intro⟩ };
      clear $h; rename' eq' => $h;
      apply Exists.imp (λ _ (h' : _ ∧ _) => ⟨Or.inr ⟨_, temp_eq, h'.1⟩, h'.2⟩);
      clear temp_eq
    )

syntax "ok_step " ident rcasesPat : tactic
macro_rules
  | `(tactic| ok_step $h $pat) => `(tactic|
      rcases of_bind_eq $h with ⟨_, ⟨_⟩, _⟩ | ⟨$pat, temp_eq, eq'⟩;
      clear $h; rename' eq' => $h;
      apply Exists.imp (λ _ (h' : _ ∧ _) => ⟨Or.inr ⟨_, temp_eq, h'.1⟩, h'.2⟩);
      clear temp_eq
    )

lemma of_itr_eq {ξ : Type u} {υ : Type v} (P : Prop) [Decidable P] (x y z  : Except ξ υ)
    ( eq :
      ( do
          if P then
            return (← x)
          y ) = z ) :
    (P ∧ x = z) ∨ (¬ P ∧ y = z) := by
  by_cases h : P <;> simp [h] at eq
  · left; refine ⟨h, eq⟩
  · right; refine ⟨h, eq⟩

def of_exec :
    ∀ (lim : Nat) (evm : Evm) (ex : Execution),
      ex.Unlim → (exec false evm lim = ex) → Nonempty (Exec evm ex) := by
  apply Nat.strongRec; intro lim ih evm ex notLimited exec_eq;
  cases lim with
  | zero =>
    rw [← exec_eq] at notLimited
    simp [exec, Except.toError?, Except.Unlim, Except.Limited] at notLimited
  | succ lim =>
    simp [exec] at exec_eq
    rcases Option.eq_none_or_eq_some evm.getInst with
      getInst_eq | ⟨i, getInst_eq⟩
      <;> rw [getInst_eq] at exec_eq
      <;> simp [Option.toExcept] at exec_eq
    · rw [← Except.of_error_bind_eq _ exec_eq]
      constructor; apply Exec.invOp getInst_eq
    · rw [ok_bind] at exec_eq
      rcases i with l | n | j <;> simp only [] at exec_eq
      · constructor;
        apply Exec.last getInst_eq exec_eq
      · rcases of_bind_eq exec_eq with
          ⟨es, run_eq, ex_eq⟩ | ⟨evm', run_eq, ex_eq⟩
        · rw [ex_eq] at notLimited
          rcases Ninst.run_of_run notLimited run_eq
            with ⟨_ | ⟨evm', ex'⟩, good, run⟩
          · rw [ex_eq]; constructor
            exact Exec.nextNoneErr getInst_eq run .intro
          · rw [ex_eq];
            have ne_ex : Nonempty (Exec evm' ex') := by
              rcases good with ⟨lim', lt, exec_eq', notLimited_of⟩
              have notLimited' : ¬ ex'.Limited := by
                intro h; cases notLimited <| notLimited_of h
              apply @ih _ (by omega) _ _ notLimited' exec_eq'
            rcases ne_ex with ⟨foo⟩
            constructor
            apply Exec.nextSomeErr getInst_eq run foo .intro
        · rcases Ninst.run_of_run (by {intro h; cases h}) run_eq
            with ⟨_ | ⟨evm', ex'⟩, good, run⟩
          · rcases (ih _ (by omega) _ _ notLimited ex_eq) with ⟨foo⟩
            constructor
            apply @Exec.nextNoneRec _ _ _ _ getInst_eq run foo ;
          · rcases good with ⟨lim', lt, exec_eq', notLimited_of⟩
            have notLimited' : ¬ ex'.Limited := by intro h; cases notLimited_of h
            rcases @ih _ (by omega) _ _ notLimited' exec_eq' with ⟨ih'⟩
            rcases @ih _ (by omega) _ _ notLimited ex_eq with ⟨ih''⟩
            constructor
            apply @Exec.nextSomeRec _ _ _ _ _ _ getInst_eq run ih' ih''
      · rcases of_bind_eq exec_eq
          with ⟨es, run_eq, ex_eq⟩ | ⟨evm', run_eq, ex_eq⟩
        · rw [ex_eq]; constructor
          exact Exec.jumpErr getInst_eq run_eq .intro
        · rcases ih _ (Nat.lt_succ_self _) _ _ notLimited ex_eq with ⟨ih'⟩
          constructor; apply Exec.jumpRec getInst_eq run_eq ih'

--- def of_exec :
---     ∀ (lim : Nat) (evm : Evm) (ex : Execution),
---       ex.Unlim → (exec false evm lim = ex) → Exec evm ex := by
---   apply Nat.strongRec; intro lim ih evm ex notLimited exec_eq;
---   cases lim with
---   | zero =>
---     rw [← exec_eq] at notLimited
---     simp [exec, Except.toError?, Except.Unlim, Except.Limited] at notLimited
---   | succ lim =>
---     simp [exec] at exec_eq
---     rcases Option.eq_none_or_eq_some evm.getInst with
---       getInst_eq | ⟨i, getInst_eq⟩
---       <;> rw [getInst_eq] at exec_eq
---       <;> simp [Option.toExcept] at exec_eq
---     · rw [← exec_eq];
---       apply Exec.invOp getInst_eq
---     · rw [ok_bind] at exec_eq
---       rcases i with l | n | j <;> simp only [] at exec_eq
---       · apply Exec.last getInst_eq exec_eq
---       · rcases of_bind_eq exec_eq with
---           ⟨es, run_eq, ex_eq⟩ | ⟨evm', run_eq, ex_eq⟩
---         · rw [ex_eq] at notLimited
---           rcases Ninst.run_of_run notLimited run_eq
---             with ⟨_ | ⟨evm', ex'⟩, good, run⟩
---           · rw [ex_eq]; exact Exec.nextNoneErr getInst_eq run .intro
---           · rw [ex_eq];
---             apply Exec.nextSomeErr getInst_eq run _ .intro
---             rcases good with ⟨lim', lt, exec_eq', notLimited_of⟩
---             have notLimited' : ¬ ex'.Limited := by
---               intro h; cases notLimited <| notLimited_of h
---             apply @ih _ (by omega) _ _ notLimited' exec_eq'
---         · rcases Ninst.run_of_run (by {intro h; cases h}) run_eq
---             with ⟨_ | ⟨evm', ex'⟩, good, run⟩
---           · apply @Exec.nextNoneRec _ _ _ _ getInst_eq run ;
---             apply ih _ (by omega) _ _ notLimited ex_eq;
---           · rcases good with ⟨lim', lt, exec_eq', notLimited_of⟩
---             have notLimited' : ¬ ex'.Limited := by intro h; cases notLimited_of h
---             have ih'  := @ih _ (by omega) _ _ notLimited' exec_eq'
---             apply @Exec.nextSomeRec _ _ _ _ _ _ getInst_eq run ih'
---             apply @ih _ (by omega) _ _ notLimited ex_eq
---       · rcases of_bind_eq exec_eq
---           with ⟨es, run_eq, ex_eq⟩ | ⟨evm', run_eq, ex_eq⟩
---         · rw [ex_eq]; exact Exec.jumpErr getInst_eq run_eq .intro
---         · apply Exec.jumpRec getInst_eq run_eq
---           apply ih _ (Nat.lt_succ_self _) _ _ notLimited ex_eq
---

lemma unlim_push {evm : Evm} {x : B256} : ¬ (evm.push x).Limited := by
  unfold Except.Limited Evm.push Except.assert
  split
  · simp [Except.toError?, bind, Except.bind]
  · simp [Except.toError?, bind, Except.bind]

lemma unlim_pop {evm : Evm} : ¬ evm.pop.Limited := by
  simp only [Except.Limited, Evm.pop, Except.toError?]
  cases evm.stack <;> simp

lemma unlim_popToNat {evm : Evm} : ¬ evm.popToNat.Limited := by
  simp only [Except.Limited, Evm.popToNat, Except.toError?, Evm.pop]
  cases evm.stack <;> simp

lemma unlim_pop_to_adr {evm : Evm} : ¬ evm.popToAdr.Limited := by
  simp only [Except.Limited, Evm.popToAdr, Except.toError?, Evm.pop]
  cases evm.stack <;> simp

lemma unlim_chargeGas {cost : Nat} {evm : Evm} :
    ¬ (chargeGas cost evm).Limited := by
  simp only [Except.Limited, Except.toError?, chargeGas]
  cases safeSub evm.gasLeft cost <;> simp

lemma unlim_assert {p ξ} [Decidable p]
    {s : String} {x : ξ} (ne : s ≠ "RecursionLimit") :
    ¬ (Except.assert p ⟨s, x⟩).Limited := by
  by_cases h : p <;>
    simp [h, Except.assert, Except.toError?, Except.Limited, ne]

lemma unlim_assertDynamic {evm : Evm} :
    ¬ evm.assertDynamic.Limited := unlim_assert (by decide)

lemma unlim_to_except {ξ υ} {x : ξ} {o : Option υ}
    {s : String} (ne : s ≠ "RecursionLimit") :
    ¬ (@Option.toExcept (String × ξ) υ ⟨s, x⟩ o).Limited := by
  simp only [Except.Limited, Except.toError?, Option.toExcept]
  cases o <;> simp [ne]

lemma unlim_ok {ξ υ} {y : υ} :
    ¬ (.ok y : Except (String × ξ) υ).Limited := by intro h; cases h

syntax "unlim_bind_step " ident term : tactic
macro_rules
  | `(tactic| unlim_bind_step $ltd $lem) => `(tactic|
      rcases of_limited_bind $ltd with ltd' | ⟨_, temp, ltd'⟩ <;>
      [
        (clear $ltd; apply $lem ltd' <;> clear ltd');
        (clear $ltd temp; rename' ltd' => $ltd)
      ]
    )

syntax "unlim_bind_step' " ident term : tactic
macro_rules
  | `(tactic| unlim_bind_step' $ltd $lem) => `(tactic|
      rcases of_limited_bind $ltd with ltd' | ⟨_, temp, ltd'⟩;
      swap; {apply $lem ltd'};
      clear $ltd; rename' ltd' => $ltd
    )

lemma unlim_execute_ecrecover (evm : Evm) :
    (executeEcrecover evm).Unlim := by
  intro ltd;

  unlim_bind_step ltd unlim_chargeGas

  unlim_bind_step ltd unlim_ok
  split at ltd
  · simp only [] at ltd
    split at ltd; {cases ltd}
    split at ltd <;> cases ltd
  · cases ltd

lemma unlim_for_in {ξ υ} {xs : List Nat} {y : υ}
    {f : Nat → υ → Except (String × ξ) (ForInStep υ)}
    (unlim : ∀ n y, (f n y).Unlim) : (ForIn.forIn xs y f).Unlim := by
  induction xs generalizing y with
    | nil => rw [List.forIn_nil]; intro ltd; cases ltd
    | cons x xs ih =>
      rw [List.forIn_cons]; intro ltd
      unlim_bind_step ltd (unlim _ _); split at ltd
      · cases ltd
      · apply ih ltd

lemma unlim_toExStrBNP {xs} :
    B8L.toExStrBNP xs ≠ .error "RecursionLimit" := by
  simp only [B8L.toExStrBNP]; intro ltd
  split at ltd; {injection ltd; contradiction}
  split at ltd; {injection ltd; contradiction}
  split at ltd; {injection ltd; contradiction}
  simp [Option.toExcept] at ltd;
  split at ltd; {injection ltd; contradiction}
  cases ltd

lemma unlim_toExStrBNP2 {xs} :
    B8L.toExStrBNP2 xs ≠ .error "RecursionLimit" := by
  simp only [B8L.toExStrBNP2]; intro ltd
  split at ltd; {injection ltd; contradiction}
  split at ltd; {injection ltd; contradiction}
  simp [Option.toExcept] at ltd;
  split at ltd; {injection ltd; contradiction}
  cases ltd

lemma unlim_catch_with_oog {ξ : Type U} {evm : Evm} {cond : String → Bool}
    {ex : Except String ξ} (unlim : ex ≠ .error "RecursionLimit") :
    (catchWithOOG evm cond ex).Unlim := by
  simp only [catchWithOOG]; split
  · apply unlim_ok
  · split <;> intro ltd <;> injection ltd
    · contradiction
    . rename_i rw; rw [rw] at unlim; cases unlim rfl

lemma unlim_execute_precomp (evm : Evm) (adr : Adr) :
    (executePrecomp evm adr).Unlim := by
  simp only [executePrecomp]; split
  · apply unlim_execute_ecrecover
  · intro ltd; unlim_bind_step ltd unlim_chargeGas; cases ltd
  · intro ltd; unlim_bind_step ltd unlim_chargeGas; cases ltd
  · intro ltd; unlim_bind_step ltd unlim_chargeGas; cases ltd
  · intro ltd; unlim_bind_step ltd unlim_chargeGas
    split at ltd <;> cases ltd
  · intro ltd;
    unlim_bind_step ltd unlim_chargeGas
    unlim_bind_step ltd (unlim_assert (by decide))
    unlim_bind_step ltd (unlim_to_except (by decide))
    unlim_bind_step ltd (unlim_to_except (by decide))
    cases ltd
  · intro ltd; unlim_bind_step ltd unlim_chargeGas
    unlim_bind_step ltd (unlim_assert (by decide))
    unlim_bind_step ltd (unlim_to_except (by decide))
    cases ltd
  · intro ltd; unlim_bind_step ltd unlim_chargeGas
    unlim_bind_step ltd (unlim_assert (by decide))
    unlim_bind_step ltd (unlim_for_in _)
    · intro n y ltd
      unlim_bind_step ltd (unlim_catch_with_oog unlim_toExStrBNP)
      unlim_bind_step ltd (unlim_catch_with_oog unlim_toExStrBNP2)
      unlim_bind_step ltd (unlim_assert (by decide))
      unlim_bind_step ltd (unlim_assert (by decide))
      unlim_bind_step ltd (unlim_to_except (by decide))
      cases ltd
    · cases ltd
  · intro ltd;
    unlim_bind_step ltd (unlim_assert (by decide))
    unlim_bind_step ltd unlim_chargeGas
    split at ltd
    · unlim_bind_step ltd unlim_ok
      unlim_bind_step ltd (unlim_to_except (by decide))
      cases ltd
    · unlim_bind_step ltd unlim_ok
      unlim_bind_step ltd (unlim_to_except (by decide))
      cases ltd
    · injection ltd; contradiction
  · intro ltd
    unlim_bind_step ltd (unlim_assert (by decide))
    injection ltd; contradiction
  · intro ltd
    unlim_bind_step ltd (unlim_assert (by decide))
    injection ltd; contradiction
  · intro ltd; simp only [executeBls12G1Msm] at ltd
    split at ltd
    · injection ltd; rename_i eq
      cases congr_arg String.head eq
    · simp only [pure_bind] at ltd
      unlim_bind_step ltd unlim_chargeGas
      injection ltd; contradiction
  · intro ltd; simp only [executeBls12G2Add] at ltd
    split at ltd
    · injection ltd; contradiction
    · simp only [pure_bind] at ltd
      unlim_bind_step ltd unlim_chargeGas
      injection ltd; contradiction
  · intro ltd; simp only [executeBls12G2Msm] at ltd
    split at ltd
    · injection ltd; rename_i eq
      cases congr_arg String.head eq
    · simp only [pure_bind] at ltd
      unlim_bind_step ltd unlim_chargeGas
      injection ltd; contradiction
  · intro ltd; simp only [executeBls12Pairing] at ltd
    split at ltd
    · injection ltd; rename_i eq
      cases congr_arg String.head eq
    · simp only [pure_bind] at ltd
      unlim_bind_step ltd unlim_chargeGas
      injection ltd; contradiction
  · intro ltd; simp only [executeBls12MapFpToG1] at ltd
    split at ltd
    · injection ltd; contradiction
    · simp only [pure_bind] at ltd
      unlim_bind_step ltd unlim_chargeGas
      injection ltd; contradiction
  · intro ltd; simp only [executeBls12MapFp2ToG2] at ltd
    unlim_bind_step ltd (unlim_assert (by decide))
    unlim_bind_step ltd unlim_chargeGas
    injection ltd; contradiction
  · intro ltd; injection ltd; rename_i eq
    cases congr_arg String.head eq


lemma and_of_imp_right_of_and {p q r} (imp : q → r) (and : p ∧ q) : p ∧ r :=
  ⟨and.1, imp and.2⟩

lemma bind_eq_of_eq_ok_of_eq {ξ υ ζ} {x : Except ξ υ} {y} {z : Except ξ ζ}
    {f : υ → Except ξ ζ} (eq_ok : x = .ok y) (eq : f y = z) : (x >>= f) = z := by
  rw [eq_ok]; exact eq

lemma ok_bind' {ξ υ ζ} {y : υ}
    {f : υ → Except ξ ζ} {z : Except ξ ζ}
    (eq : f y = z) : (.ok y >>= f) = z := by
  rw [ok_bind]; exact eq

lemma bind_eq_of_false {ξ υ ζ} {x : Except ξ υ} {z : Except ξ ζ}
    {f : υ → Except ξ ζ} (false : False) : (x >>= f) = z := by cases false

lemma unlim_benvAfterTransfer {msg : Msg} : msg.benvAfterTransfer.Unlim := by
  simp only [Msg.benvAfterTransfer]; intro ltd
  split at ltd
  · unlim_bind_step ltd (unlim_to_except (by decide)); exact unlim_ok ltd
  · exact unlim_ok ltd

lemma ite_eq_left_of_true {ξ : Sort u} {C : Prop} [h : Decidable C]
    {x y z : ξ} (c : C) (eq : x = z) : (if C then x else y) = z := by simp [c, eq]

lemma ite_eq_right_of_false {ξ : Sort u} {C : Prop} [h : Decidable C]
    {x y z : ξ} (c : ¬ C) (eq : y = z) : (if C then x else y) = z := by simp [c, eq]

lemma or_of_ite {c p q : Prop} [h : Decidable c] (h : if c then p else q) :
    (c ∧ p) ∨ (¬ c ∧ q) := by
  by_cases hc : c <;> simp [hc] at h
  · left; exact ⟨hc, h⟩
  · right; exact ⟨hc, h⟩

lemma forall_gt_of_forall_gt_succ_pred {p : Nat → Prop} (n : Nat) :
    (∀ m > n, p (m.pred + 1)) → (∀ m > n, p m) := by
  intro fa m gt; rcases m with _ | m
  · cases Nat.not_lt_zero _ gt
  · apply fa (m + 1) gt

lemma forall_gt_iff_forall_ge_succ {n} {p : Nat → Prop} :
    (∀ m > n, p m) ↔ (∀ m ≥ n, p (m + 1)) := by
  constructor <;> intro fa m ineq
  · apply fa (m + 1); omega
  · rcases m with _ | m
    · simp at ineq
    · apply fa m; omega

lemma exists_forall_gt_imp {p q : Nat → Prop} :
    (∀ n, p n → q n) → (∃ n, ∀ m > n, p m) → (∃ n, ∀ m > n, q m) := by
  intro imp ⟨n, fa⟩; refine ⟨n, λ m gt => imp m (fa m gt)⟩

syntax "ule_split " ident term : tactic
macro_rules
  | `(tactic| ule_split $eq $lem) => `(tactic|
      have temp := $eq; clear $eq;
      rcases temp with ⟨⟨_, _, _⟩, rw, rw'⟩ | ⟨_, eq', $eq⟩ <;>
      [
        ( constructor <;>
          [
            (rw [rw']; apply @Eq.subst _ (Except.Unlim) _ _ rw $lem);
            (refine' ⟨1, _⟩; simp only [rw]; apply rw'.symm)
          ]
        );
        (
          apply and_of_imp_right_of_and <| Exists.imp <| λ lim => bind_eq_of_eq_ok_of_eq eq';
          clear eq'
        )
      ]
    )

syntax "split_step " ident : tactic
macro_rules
  | `(tactic| split_step $eq) => `(tactic|
        have temp := $eq; clear $eq;
        rcases temp with ⟨⟨_, _, _⟩, rw, rw'⟩ | ⟨_, eq', $eq⟩ <;>
        [
          (simp only [rw]; apply rw'.symm);
          (apply bind_eq_of_eq_ok_of_eq eq')
        ]
    )

syntax "ule_exists " ident : tactic
macro_rules
  | `(tactic| ule_exists $eq) => `(tactic|
      have temp := $eq; clear $eq;
      rcases temp with ⟨_, eq', $eq⟩;
      rw [← eq']; clear eq';
      apply and_of_imp_right_of_and <| Exists.imp <| λ lim => ok_bind';
    )

syntax "ule_exists_2 " ident : tactic
macro_rules
  | `(tactic| ule_exists_2 $eq) => `(tactic|
      have temp := $eq; clear $eq;
      rcases temp with ⟨_, _, eq', $eq⟩;
      rw [← eq']; clear eq';
      apply and_of_imp_right_of_and <| Exists.imp <| λ lim => ok_bind';
    )

syntax "ule_exists_5 " ident : tactic
macro_rules
  | `(tactic| ule_exists_5 $eq) => `(tactic|
      have temp := $eq; clear $eq;
      rcases temp with ⟨_, _, _, _, _, eq', $eq⟩;
      rw [← eq']; clear eq';
      apply and_of_imp_right_of_and <| Exists.imp <| λ lim => ok_bind';
    )

syntax "ule_exec " ident ident term:max term : tactic
macro_rules
  | `(tactic| ule_exec $eq $good $lem $lem') => `(tactic|
      have temp := $eq; clear $eq;
      rcases temp with ⟨ex', runs, $eq⟩;
      have temp := $lem $good runs;
      rcases temp with ⟨unlim, lim, run_eq⟩;
      clear $good runs;
      refine' ⟨_, lim + 1, _⟩ <;> [
        (
          have temp := $eq; clear $eq;
          rcases temp with ⟨_, rw, rw'⟩ | ⟨_, _, $eq⟩ <;> [
            (rw [rw', ← rw]; apply ($lem' unlim));
            skip
          ]
        );
        (rw [run_eq]; clear unlim run_eq)
      ]
    )

syntax "unlim_and_step_exec " ident ident term:max term : tactic
macro_rules
  | `(tactic| unlim_and_step_exec $run $good $lem $lem') => `(tactic|
      have temp := $run; clear $run;
      rcases temp with ⟨ex', runs, $run⟩;
      have temp := $lem $good runs;
      rcases temp with ⟨unlim, lim, run_eq⟩;
      clear $good runs;
      refine' ⟨_, lim + 1, _⟩ <;> [
        ( have temp := $run; clear $run;
          rcases temp with ⟨_, rw, rw'⟩ | ⟨_, _, $run⟩ <;>
          [(rw [rw', ← rw]; apply ($lem' unlim)); skip] );
        (
          intro lim_temp gt;
          have gt_temp : lim_temp.pred > lim := by
            cases lim_temp <;>
            [ (cases Nat.not_lt_zero _ gt);
              (exact Nat.lt_of_succ_lt_succ gt) ];
          rw [run_eq lim_temp.pred gt_temp];
          clear gt_temp unlim run_eq; revert gt lim_temp
        )

      ]
    )

syntax "ule_of_ite " ident : tactic
macro_rules
  | `(tactic| ule_of_ite $eq) => `(tactic|
      rename' $eq => temp;
      rcases or_of_ite temp with ⟨pos, $eq⟩ | ⟨neg, $eq⟩ <;> clear temp <;>
      [
        (
          apply and_of_imp_right_of_and <| Exists.imp <| λ lim => ite_eq_left_of_true pos;
          clear pos
        ) ;
        (
          apply and_of_imp_right_of_and <| Exists.imp <| λ lim => ite_eq_right_of_false neg;
          clear neg
        )
      ]
  )

syntax "eq_split " ident : tactic
macro_rules
  | `(tactic| eq_split $eq) => `(tactic|
      have temp := $eq; clear $eq;
      rcases temp with ⟨⟨_, _, _⟩, rw', rw⟩ | ⟨_, eq', $eq⟩ <;> [
        (rw [rw', rw]; rfl);
        (apply bind_eq_of_eq_ok_of_eq eq'; clear eq')
      ]
    )

syntax "eq_ite " ident : tactic
macro_rules
  | `(tactic| eq_ite $eq) => `(tactic|
      rename' $eq => temp;
      rcases or_of_ite temp with ⟨pos, $eq⟩ | ⟨neg, $eq⟩ <;> clear temp <;>
      [
        (apply ite_eq_left_of_true pos; clear pos) ;
        (apply ite_eq_right_of_false neg; clear neg)
      ]
    )

lemma of_execute_code' {msg : Msg} {xl : Xlot}
    {ex : Except (String × Benv × Tenv) Evm}
    (good : xl.Good') (ec : ExecuteCode msg xl ex) :
    ex.Unlim ∧ ∃ lim, ∀ lim' > lim, executeCode false msg lim' = ex := by
  simp only [ExecuteCode] at ec; split at ec
  · rename (msg.codeAddress = none) => eq_none
    rcases ec with ⟨ex', xl_eq, eq_ex⟩
    rw [xl_eq] at good
    simp [Xlot.Good'] at good
    rcases good with ⟨unlim', lim, eq_ex'⟩
    have unlim : ¬ ex.Limited := by
      rw [← eq_ex]
      exact (of_limited_handleError).mt unlim'
    refine' ⟨unlim, lim + 1, _⟩
    intro lim' gt
    rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [executeCode]
    rw [eq_none]; simp only
    rw [← eq_ex'] at unlim'
    rw [← (saturation lim).exec _ unlim' lim' (by omega), eq_ex', eq_ex]
  · rename Adr => adr
    rename (msg.codeAddress = some adr) => eq_some
    split at ec
    · rename_i pos; constructor
      · rw [← ec.2]; intro ltd
        cases unlim_execute_precomp _ _ <| of_limited_handleError ltd
      · refine' ⟨1, _⟩; intro lim' gt
        rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
        simp only [executeCode, eq_some, if_pos pos]; exact ec.2
    · rename_i neg; rcases ec with ⟨ex', xl_eq, eq_ex⟩
      rw [xl_eq] at good; simp [Xlot.Good'] at good
      rcases good with ⟨unlim, lim, eq_ex'⟩
      constructor
      · rw [← eq_ex]; intro ltd;
        cases unlim <| of_limited_handleError ltd
      · refine' ⟨lim + 1, _⟩; intro lim' gt
        rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
        simp only [executeCode]
        rw [eq_some]; simp only
        rw [if_neg neg]; rw [← eq_ex'] at unlim
        rw [← (saturation lim).exec _ unlim lim' (by omega), eq_ex', eq_ex]

-- lemma of_execute_code' {msg : Msg} {xl : Xlot}
--     {ex : Except (String × Benv × Tenv) Evm} (good : xl.Good')
--     (exec : ExecuteCode msg xl ex) :
--     ex.Unlim ∧ ∃ lim, executeCode false msg (lim + 1) = ex := by
--   simp only [ExecuteCode] at exec
--   split at exec
--   · rename (msg.codeAddress = none) => eq_none
--     rcases exec with ⟨ex', xl_eq, eq_ex⟩
--     rw [xl_eq] at good
--     simp [Xlot.Good'] at good
--     rcases good with ⟨unlim', lim, eq_ex'⟩
--     have unlim : ¬ ex.Limited := by
--       rw [← eq_ex]
--       exact (executeCode.of_limited_handleError ex').mt unlim'
--     refine' ⟨unlim, lim, _⟩
--     simp only [executeCode]
--     rw [eq_none]; simp
--     rw [eq_ex', eq_ex]
--   · rename Adr => adr
--     rename (msg.codeAddress = some adr) => eq_some
--     split at exec
--     · rename_i pos; constructor
--       · rw [← exec.2]; intro ltd
--         cases
--           unlim_execute_precomp _ _ <| executeCode.of_limited_handleError _ ltd
--       · refine' ⟨1, _⟩;
--         simp only [executeCode, eq_some, if_pos pos]
--         exact exec.2
--     · rename_i neg
--       rcases exec with ⟨ex', xl_eq, eq_ex⟩
--       rw [xl_eq] at good
--       simp [Xlot.Good'] at good
--       rcases good with ⟨unlim, lim, eq_ex'⟩
--       have hh := executeCode.of_limited_handleError
--       constructor
--       · rw [← eq_ex]; intro ltd; cases unlim <| hh _ ltd
--       · refine' ⟨lim, _⟩
--         simp only [executeCode]
--         rw [eq_some]; simp
--         rw [if_neg neg]
--         rw [eq_ex', eq_ex]

lemma unlim_of_split_of_unlim {ξ υ ζ} {x : Except (String × ξ) υ}
    {p : υ → Prop} {ex : Except (String × ξ) ζ}
    (split : Except.Split x ex p) (unlim : x.Unlim) :
    (∀ y, x = .ok y → p y → ex.Unlim) → ex.Unlim := by
  intro prem
  rcases split with ⟨⟨err, _⟩ , rw, rw'⟩ | ⟨y, eq, py⟩
  · rw [rw']; intro ltd; injection ltd with rw''
    rw [rw, rw''] at unlim; cases unlim rfl
  · exact (prem _ eq py)

lemma bind_eq_of_split {ξ υ ζ} {x : Except (String × ξ) υ}
    {ex : Except (String × ξ) ζ} {p : υ → Prop}
    {f : υ → Except (String × ξ) ζ} (split : Except.Split x ex p) :
    (∀ y, x = .ok y → p y → f y = ex) → (x >>= f) = ex := by
  intro prem
  rcases split with ⟨⟨err, _⟩ , rw, rw'⟩ | ⟨y, eq, py⟩
  · rw [rw, rw']; rfl
  · rw [eq]; apply prem _ eq py

lemma exists_forall_gt_ok_bind_eq {ξ υ ζ}
    {f : Nat → υ → Except (String × ξ) ζ} {y : υ} {ex : Except (String × ξ) ζ} :
    (∃ lim, ∀ lim' > lim, (f lim' y) = ex) →
    ∃ lim, ∀ lim' > lim, (.ok y >>= f lim') = ex := id

lemma exists_forall_gt_of_split {ξ υ ζ} {x : Except (String × ξ) υ}
    {ex : Except (String × ξ) ζ} {p : υ → Prop}
    {f : Nat → υ → Except (String × ξ) ζ} (split : Except.Split x ex p) :
    (∀ y, x = .ok y → p y → ∃ lim, ∀ lim' > lim, (f lim' y) = ex) →
    ∃ lim, ∀ lim' > lim, (x >>= f lim') = ex := by
  intro prem
  rcases split with ⟨⟨err, _⟩ , rw, rw'⟩ | ⟨y, eq, py⟩
  · refine' ⟨0, _⟩; intro _ _; rw [rw, rw']; rfl
  · rcases (prem _ eq py) with ⟨lim, fa⟩
    refine' ⟨lim, _⟩; intro lim' gt; rw [eq]; apply fa _ gt

syntax "unlim_step_split " ident term : tactic
macro_rules
  | `(tactic| unlim_step_split $run $lem) =>
    `(tactic|
      apply unlim_of_split_of_unlim $run $lem;
      clear $run; intro _ temp $run; clear temp;
    )

syntax "unlim_step_exec " ident ident term:max term : tactic
macro_rules
  | `(tactic| unlim_step_exec $run $good $lem $lem') =>
    `(tactic|
      have temp := $run; clear $run;
      rcases temp with ⟨ex', runs, $run⟩;
      have temp := $lem $good runs; clear $good runs;
      rcases temp with ⟨unlim, lim, run_eq⟩; clear lim run_eq;
      unlim_step_split $run ($lem' unlim); clear unlim
    )

syntax "efg_step_split " ident : tactic
macro_rules
  | `(tactic| efg_step_split $run) =>
    `(tactic|
      apply exists_forall_gt_of_split $run; clear $run;
      intro _ temp $run; clear temp
    )

syntax "efg_step_exec " ident ident term:max : tactic
macro_rules
  | `(tactic| efg_step_exec $run $good $lem) =>
    `(tactic|
      have temp := $run; clear $run;
      rcases temp with ⟨ex', runs, $run⟩;
      have temp := $lem $good runs;
      clear $good runs;
      rcases temp with ⟨unlim, lim, run_eq⟩;
      clear unlim;
      refine' ⟨lim + 1, _⟩;
      intro lim' gt;
      have gt' : lim'.pred > lim :=
      ( by cases lim' <;>
           [ (cases Nat.not_lt_zero _ gt);
             (exact Nat.lt_of_succ_lt_succ gt) ] );
      rw [run_eq lim'.pred gt'];
      clear gt gt' run_eq;
    )

lemma of_process_message' {msg : Msg} {xl : Xlot}
    {ex : Except (String × Benv × Tenv) Evm} (good : xl.Good')
    (run : ProcessMessage msg xl ex) :
    ex.Unlim ∧ ∃ lim, ∀ lim' > lim, processMessage false msg lim' = ex := by
  simp only [ProcessMessage] at run; constructor
  · unlim_step_split run (unlim_assert (by decide))
    unlim_step_split run unlim_benvAfterTransfer
    unlim_step_exec run good of_execute_code' id
    split at run <;> (rw [← run]; apply unlim_ok)
  · apply Exists.imp forall_gt_of_forall_gt_succ_pred
    simp only [processMessage]
    efg_step_split run; efg_step_split run;
    --efg_step_exec run good of_execute_code'

    have temp := run; clear run;
    rcases temp with ⟨ex', runs, run⟩;
    have temp := of_execute_code' good runs;
    clear good runs;
    rcases temp with ⟨unlim, lim, run_eq⟩;
    clear unlim;

    refine' ⟨lim + 1, _⟩;

    intro lim' gt;
    have gt' : lim'.pred > lim :=
    ( by cases lim' <;>
         [ (cases Nat.not_lt_zero _ gt);
           (exact Nat.lt_of_succ_lt_succ gt) ] );

    rw [run_eq lim'.pred gt'];
    clear gt gt' run_eq;



    eq_split run; eq_ite run <;> exact run


--- lemma of_process_message'' {msg : Msg} {xl : Xlot}
---     {ex : Except (String × Benv × Tenv) Evm} (good : xl.Good')
---     (eq : ProcessMessage msg xl ex) :
---     ex.Unlim ∧ ∃ lim, processMessage false msg (lim + 1) = ex := by
---   simp only [processMessage]
---   ule_split eq (unlim_assert (by decide))
---   ule_split eq unlim_benvAfterTransfer
---   ule_exec eq good of_execute_code' id
---   · split at eq <;> {rw [← eq]; apply unlim_ok}
---   · eq_split eq; eq_ite eq <;> exact eq

lemma processCreateMessage.unlim_chargeCodeGas {evm : Evm} :
    (processCreateMessage.chargeCodeGas evm).Unlim := by
  simp only [processCreateMessage.chargeCodeGas]; intro ltd
  split at ltd
  · injection ltd; contradiction
  · unlim_bind_step ltd unlim_chargeGas
    split at ltd
    · injection ltd; contradiction
    · cases ltd

lemma of_process_create_message' {msg : Msg} {xl : Xlot}
    {ex : Except (String × Benv × Tenv) Evm} (good : xl.Good')
    (run : ProcessCreateMessage msg xl ex) :
    ex.Unlim ∧
      ∃ lim, ∀ lim' > lim, processCreateMessage false msg lim' = ex := by
  simp only [ProcessCreateMessage] at run; constructor
  · unlim_step_exec run good of_process_message' id
    rename Evm => evm; split at run
    · split at run; {rw [← run]; apply unlim_ok}
      rename_i eq; split at run
      · rw [← run]; apply unlim_ok
      · rw [← run]; intro ltd; injection ltd with rw
        have unlim := @processCreateMessage.unlim_chargeCodeGas evm
        rw [eq, rw] at unlim; cases unlim rfl
    · rw [← run]; apply unlim_ok
  · apply Exists.imp forall_gt_of_forall_gt_succ_pred
    simp only [processCreateMessage]
    efg_step_exec run good of_process_message'
    eq_split run; eq_ite run
    · split at run <;> rename_i rw <;> rw [rw]
      · exact run
      · eq_ite run <;> exact run
    · exact run

-- lemma of_process_create_message' {msg : Msg} {xl : Xlot}
--     {ex : Except (String × Benv × Tenv) Evm} (good : xl.Good')
--     (eq : ProcessCreateMessage msg xl ex) :
--     ex.Unlim ∧ ∃ lim, processCreateMessage false msg (lim + 1) = ex := by
--   simp only [processCreateMessage]
--   simp only [ProcessCreateMessage] at eq
--   ule_exec eq good of_process_message' id
--   · split at eq
--     · rename Evm => evm;
--       split at eq; {rw [← eq]; apply unlim_ok}
--       rename_i rw;
--       split at eq; {rw [← eq]; apply unlim_ok}
--       have unlim := @processCreateMessage.unlim_chargeCodeGas evm
--       rw [rw] at unlim; rw [← eq]; exact unlim
--     · rw [← eq]; apply unlim_ok
--   · eq_split eq; eq_ite eq
--     · split at eq <;> rename_i rw <;> rw [rw]
--       · exact eq
--       · eq_ite eq <;> exact eq
--     · exact eq

syntax "unlim_step_exists " ident : tactic
macro_rules
  | `(tactic| unlim_step_exists $run) =>
    `(tactic|
      have temp := $run; clear $run;
      rcases temp with ⟨_, temp, $run⟩; clear temp
    )

syntax "unlim_step_exists_2 " ident : tactic
macro_rules
  | `(tactic| unlim_step_exists_2 $run) =>
    `(tactic|
      have temp := $run; clear $run;
      rcases temp with ⟨_, _, temp, $run⟩; clear temp
    )

syntax "unlim_step_exists_5 " ident : tactic
macro_rules
  | `(tactic| unlim_step_exists_5 $run) =>
    `(tactic|
      have temp := $run; clear $run;
      rcases temp with ⟨_, _, _, _, _, temp, $run⟩; clear temp
    )

syntax "efg_step_exists_2 " ident : tactic
macro_rules
  | `(tactic| efg_step_exists_2 $run) =>
    `(tactic|
      have temp := $run; clear $run;
      rcases temp with ⟨_, _, rw, $run⟩;
      rw [← rw]; clear rw;
      apply exists_forall_gt_ok_bind_eq
    )

syntax "efg_step_exists_5 " ident : tactic
macro_rules
  | `(tactic| efg_step_exists_5 $run) =>
    `(tactic|
      have temp := $run; clear $run;
      rcases temp with ⟨_, _, _, _, _, rw, $run⟩;
      rw [← rw]; clear rw;
      apply exists_forall_gt_ok_bind_eq
    )

syntax "efg_step_exists " ident : tactic
macro_rules
  | `(tactic| efg_step_exists $run) =>
    `(tactic|
      have temp := $run; clear $run;
      rcases temp with ⟨_, rw, $run⟩;
      rw [← rw]; clear rw;
      apply exists_forall_gt_ok_bind_eq
    )

syntax "efg_step_ite " ident : tactic
macro_rules
  | `(tactic| efg_step_ite $run) =>
    `(tactic|
      have temp := $run; clear $run;
      rcases or_of_ite temp with ⟨pos, $run⟩ | ⟨neg, $run⟩ <;> clear temp <;> [
        ( apply exists_forall_gt_imp (λ _ => ite_eq_left_of_true pos);
          simp only [bind_pure]; clear pos );
        ( apply exists_forall_gt_imp (λ _ => ite_eq_right_of_false neg);
          clear neg )
      ]
    )

syntax "efg_step_early " ident : tactic
macro_rules
  | `(tactic| efg_step_early $run) =>
    `(tactic|
      have temp := $run; clear $run;
      rcases or_of_ite temp with ⟨pos, $run⟩ | ⟨neg, $run⟩ <;> clear temp <;> [
        ( apply exists_forall_gt_imp (λ _ => ite_eq_left_of_true pos);
          simp only [bind_pure]; clear pos );
        ( apply exists_forall_gt_imp (λ _ => ite_eq_right_of_false neg ∘ ok_bind');
          clear neg )
      ]
    )

lemma unlim_liftToExecution {evm : Evm} {f : Except (String × Benv × Tenv) Evm}
    (unlim : f.Unlim) : (liftToExecution evm f).Unlim := by
  cases f
  · exact unlim
  · simp only [liftToExecution]; intro ltd; cases ltd

lemma of_generic_create' {evm : Evm} {endowment : B256} {newAddress : Adr}
    {memoryIndex memorySize : ℕ} {xl : Xlot} {ex : Execution} (good : xl.Good')
    (run : GenericCreate evm endowment newAddress memoryIndex memorySize xl ex) :
    ex.Unlim ∧
      ∃ lim,
        ∀ lim' > lim,
          genericCreate false evm endowment
            newAddress memoryIndex memorySize lim' = ex := by
  simp only [GenericCreate] at run; constructor
  · unlim_step_exists run
    unlim_step_split run (unlim_assert (by decide))
    iterate 3 (unlim_step_exists run);
    unlim_step_split run unlim_assertDynamic
    iterate 2 (unlim_step_exists run);
    split at run; {rw [← run]; apply unlim_push}
    unlim_step_exists run
    split at run; {rw [← run]; apply unlim_push}
    unlim_step_exists run
    unlim_step_exec run good of_process_create_message' unlim_liftToExecution
    split at run <;> (rw [← run]; apply unlim_push)
  · apply Exists.imp forall_gt_of_forall_gt_succ_pred
    simp only [genericCreate]
    efg_step_exists run; efg_step_split run
    iterate 3 (efg_step_exists run)
    efg_step_split run; iterate 2 (efg_step_exists run)
    efg_step_early run; {refine' ⟨0, _⟩; intro _ _; exact run}
    efg_step_exists run
    efg_step_early run; {refine' ⟨0, _⟩; intro _ _; exact run}
    efg_step_exists run
    efg_step_exec run good of_process_create_message'
    eq_split run; eq_ite run <;> exact run

-- lemma of_generic_create' {evm : Evm} {endowment : B256} {newAddress : Adr}
--     {memoryIndex memorySize : ℕ} {xl : Xlot} {ex : Execution} (good : xl.Good')
--     (eq : GenericCreate evm endowment newAddress memoryIndex memorySize xl ex) :
--     ex.Unlim ∧
--       ∃ lim,
--         genericCreate false evm endowment newAddress memoryIndex memorySize (lim + 1) =
--           ex := by
--   simp only [GenericCreate] at eq
--   simp only [genericCreate]
--   ule_exists eq; ule_split eq (unlim_assert (by decide))
--   ule_exists eq; ule_exists eq; ule_exists eq
--   ule_split eq (unlim_assert (by decide))
--   ule_exists eq; ule_exists eq; ule_of_ite eq
--   · refine' ⟨_, 0, _⟩
--     · rw [← eq]; apply unlim_push
--     · simp [eq]
--   · simp only [bind_pure, pure_bind]
--     ule_exists eq; ule_of_ite eq
--     · refine' ⟨_, 0, eq⟩
--       rw [← eq]; apply unlim_push
--     · ule_exists eq
--       ule_exec eq good of_process_create_message' unlim_liftToExecution
--       · split at eq <;> {rw [← eq]; apply unlim_push}
--       · eq_split eq; eq_ite eq <;> exact eq
--

lemma of_generic_call' {evm : Evm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {input_index input_size output_index output_size : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {xl : Xlot} {ex : Execution} (good : xl.Good')
    ( run :
      GenericCall evm gas value caller target codeAddress
        shouldTransferValue isStaticcall input_index input_size
        output_index output_size code disablePrecompiles xl ex ) :
    ex.Unlim ∧
      ∃ lim, ∀ lim' > lim,
        genericCall false evm gas value caller target codeAddress
          shouldTransferValue isStaticcall input_index input_size
          output_index output_size code disablePrecompiles lim' = ex := by
  simp only [GenericCall] at run; constructor
  · unlim_step_exists run
    split at run; {rw [← run]; apply unlim_push}
    unlim_step_exists run
    unlim_step_exists run
    unlim_step_exec run good of_process_message' unlim_liftToExecution
    split at run <;>
    {unlim_step_split run unlim_push; rw [← run]; apply unlim_ok}
  · apply Exists.imp forall_gt_of_forall_gt_succ_pred
    simp only [genericCall]; efg_step_exists run;
    efg_step_early run; {refine' ⟨0, _⟩; intro _ _; exact run}
    efg_step_exists run; efg_step_exists run;
    efg_step_exec run good of_process_message'; eq_split run;
    eq_ite run <;> {eq_split run; exact run}

-- lemma of_generic_call' {evm : Evm} {gas : Nat} {value : B256}
--     {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
--     {input_index input_size output_index output_size : Nat} {code : ByteArray}
--     {disablePrecompiles : Bool} {xl : Xlot} {ex : Execution} (good : xl.Good')
--     ( eq :
--       GenericCall evm gas value caller target codeAddress
--         shouldTransferValue isStaticcall input_index input_size
--         output_index output_size code disablePrecompiles xl ex ) :
--     ex.Unlim ∧
--       ∃ lim,
--         genericCall false evm gas value caller target codeAddress
--           shouldTransferValue isStaticcall input_index input_size
--           output_index output_size code disablePrecompiles (lim + 1) = ex := by
--   simp only [GenericCall] at eq
--   simp only [genericCall]
--   ule_exists eq; ule_of_ite eq
--   · refine' ⟨_, 0, _⟩
--     · rw [← eq]; apply unlim_push
--     · simp only [bind_pure]; exact eq
--   · simp only [pure_bind]
--     ule_exists eq; ule_exists eq
--     ule_exec eq good of_process_message' unlim_liftToExecution
--     · split at eq <;>
--       { rcases eq with ⟨_, eq', eq⟩ | ⟨_, eq', eq⟩ <;>
--         [(rw [eq, ← eq']; apply unlim_push); (rw [← eq]; apply unlim_ok)] }
--     · eq_split eq; eq_ite eq <;> {eq_split eq; exact eq}

lemma unlim_pop_n {evm : Evm} {n : Nat} : ¬ (evm.popN n).Limited := by
  induction n generalizing evm
  case zero =>
    simp [Evm.popN, Except.Limited, Except.toError?]
  case succ n ih =>
    simp only [Evm.popN]; intro ltd
    unlim_bind_step ltd unlim_pop
    unlim_bind_step ltd ih; cases ltd

lemma Linst.unlim_of_run {evm : Evm} {l : Linst} {ex : Execution}
    (run : Linst.Run evm l ex) : ¬ ex.Limited := by
  intro ltd;
  simp only [Linst.Run] at run
  rw [← run] at ltd; cases l
  case stop => cases ltd
  case rev =>
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_chargeGas
    simp [Except.Limited, Except.toError?] at ltd
  case ret =>
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_chargeGas
    simp [Except.Limited, Except.toError?] at ltd
  case dest =>
    simp only [Evm.popToAdr, bind_map_left, Linst.run] at ltd
    unlim_bind_step ltd unlim_pop
    unlim_bind_step ltd unlim_chargeGas
    unlim_bind_step ltd unlim_assertDynamic
    have ne : "ERROR : InsufficientBalanceError" ≠ "RecursionLimit" := by decide
    unlim_bind_step ltd (unlim_to_except ne)
    split at ltd <;> simp [Except.Limited, Except.toError?] at ltd

lemma unlim_pushItem {x : B256} {c : Nat} {evm : Evm} :
    ¬ (pushItem x c evm).Limited := by
  simp only [pushItem]; intro run
  rcases of_limited_bind run with run' | ⟨_, _, run'⟩
  · clear run
    rcases of_limited_bind run' with run | ⟨_, _, run⟩
    · cases unlim_chargeGas run
    · cases unlim_push run
  · simp [Evm.incrPc, Except.toError?, Except.Limited] at run'

lemma unlim_applyUnary {f : B256 → B256} {cost : Nat} {evm : Evm} :
    ¬ (applyUnary f cost evm).Limited := by
  simp only [applyUnary]; intro run
  rcases of_limited_bind run with run' | ⟨_, _, run'⟩
  · cases unlim_pop run'
  · cases unlim_pushItem run'

lemma unlim_applyBinary {f : B256 → B256 → B256} {cost : Nat} {evm : Evm} :
    ¬ (applyBinary f cost evm).Limited := by
  simp only [applyBinary]; intro ltd
  unlim_bind_step ltd unlim_pop
  unlim_bind_step ltd unlim_pop
  cases unlim_pushItem ltd

lemma unlim_applyTernary {f : B256 → B256 → B256 → B256} {cost : Nat} {evm : Evm} :
    ¬ (applyTernary f cost evm).Limited := by
  simp only [applyTernary]; intro ltd
  unlim_bind_step ltd unlim_pop
  unlim_bind_step ltd unlim_pop
  unlim_bind_step ltd unlim_pop
  cases unlim_pushItem ltd

lemma of_limited_map_rev {ξ υ ζ} {x : Except (String × ξ) υ}
    {f : υ → ζ} (ltd : (x <&> f).Limited) : x.Limited := by
  cases x <;> simp [Except.toError?, Except.Limited] at *; exact ltd

lemma unlim_map_rev {ξ υ ζ} {x : Except (String × ξ) υ}
    {f : υ → ζ} : x.Unlim → (x <&> f).Unlim  := of_limited_map_rev.mt

lemma Rinst.unlim_run (evm : Evm) (r : Rinst) :
    ¬ (Rinst.run evm r).Limited := by
  intro ltd; cases r <;> simp only [Rinst.run] at ltd
  case add => exact unlim_applyBinary ltd
  case mul => exact unlim_applyBinary ltd
  case sub => exact unlim_applyBinary ltd
  case div => exact unlim_applyBinary ltd
  case sdiv => exact unlim_applyBinary ltd
  case mod => exact unlim_applyBinary ltd
  case smod => exact unlim_applyBinary ltd
  case addmod => exact unlim_applyTernary ltd
  case mulmod => exact unlim_applyTernary ltd
  case exp =>
    unlim_bind_step ltd unlim_pop
    unlim_bind_step ltd unlim_pop
    unlim_bind_step ltd unlim_chargeGas
    unlim_bind_step ltd unlim_push
    cases ltd
  case signextend => exact unlim_applyBinary ltd
  case lt => exact unlim_applyBinary ltd
  case gt => exact unlim_applyBinary ltd
  case slt => exact unlim_applyBinary ltd
  case sgt => exact unlim_applyBinary ltd
  case eq => exact unlim_applyBinary ltd
  case iszero => exact unlim_applyUnary ltd
  case and => exact unlim_applyBinary ltd
  case or => exact unlim_applyBinary ltd
  case xor => exact unlim_applyBinary ltd
  case not => exact unlim_applyUnary ltd
  case byte => exact unlim_applyBinary ltd
  case shr => exact unlim_applyBinary ltd
  case shl => exact unlim_applyBinary ltd
  case sar => exact unlim_applyBinary ltd
  case kec =>
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_chargeGas
    unlim_bind_step ltd unlim_push
    cases ltd
  case address => exact unlim_pushItem ltd
  case balance =>
    unlim_bind_step ltd unlim_pop
    split at ltd <;>
    { unlim_bind_step ltd unlim_chargeGas;
      unlim_bind_step ltd unlim_push; cases ltd }
  case origin => exact unlim_pushItem ltd
  case caller => exact unlim_pushItem ltd
  case callvalue => exact unlim_pushItem ltd
  case calldataload =>
    unlim_bind_step ltd unlim_pop
    unlim_bind_step ltd unlim_chargeGas
    unlim_bind_step ltd unlim_push
    simp [Evm.incrPc, Except.toError?, Except.Limited] at ltd
  case calldatasize => exact unlim_pushItem ltd
  case calldatacopy =>
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_chargeGas
    simp [Evm.memWrite, Evm.incrPc, Except.toError?, Except.Limited] at ltd
  case codesize => exact unlim_pushItem ltd
  case codecopy =>
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_chargeGas
    simp [Except.toError?, Except.Limited] at ltd
  case gasprice => exact unlim_pushItem ltd
  case extcodesize =>
    unlim_bind_step ltd unlim_pop_to_adr
    split at ltd <;> unlim_bind_step ltd unlim_chargeGas
    · unlim_bind_step ltd unlim_push
      simp [Evm.incrPc, Except.toError?, Except.Limited] at ltd
    · unlim_bind_step ltd unlim_push
      simp [Evm.incrPc, Except.toError?, Except.Limited] at ltd
  case extcodecopy =>
    unlim_bind_step ltd unlim_pop_to_adr
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_popToNat
    split at ltd <;> unlim_bind_step ltd unlim_chargeGas
    · simp [Except.toError?, Except.Limited] at ltd
    · simp [Except.toError?, Except.Limited] at ltd
  case retdatasize => exact unlim_pushItem ltd
  case retdatacopy =>
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_chargeGas
    split at ltd <;> rename_i h_retdat
    · simp only [bind, Except.bind, Except.Limited, Except.toError?] at ltd; injection ltd; contradiction
    · simp [Except.toError?, Except.Limited] at ltd
  case extcodehash =>
    unlim_bind_step ltd unlim_pop_to_adr
    split at ltd <;> unlim_bind_step ltd unlim_chargeGas
    · unlim_bind_step ltd unlim_push
      simp [Evm.incrPc, Except.toError?, Except.Limited] at ltd
    · unlim_bind_step ltd unlim_push
      simp [Evm.incrPc, Except.toError?, Except.Limited] at ltd
  case blockhash =>
    unlim_bind_step ltd unlim_pop
    unlim_bind_step ltd unlim_chargeGas
    unlim_bind_step ltd unlim_push
    simp [Evm.incrPc, Except.toError?, Except.Limited] at ltd
  case coinbase => exact unlim_pushItem ltd
  case timestamp => exact unlim_pushItem ltd
  case number => exact unlim_pushItem ltd
  case prevrandao => exact unlim_pushItem ltd
  case gaslimit => exact unlim_pushItem ltd
  case chainid => exact unlim_pushItem ltd
  case selfbalance => exact unlim_pushItem ltd
  case basefee => exact unlim_pushItem ltd
  case blobhash =>
    unlim_bind_step ltd unlim_pop
    unlim_bind_step' ltd unlim_ok
    unlim_bind_step ltd unlim_chargeGas
    exact unlim_push ltd
  case blobbasefee => exact unlim_pushItem ltd
  case pop =>
    unlim_bind_step' ltd unlim_ok
    unlim_bind_step' ltd unlim_chargeGas
    exact unlim_pop <| of_limited_map_rev ltd
  case mload =>
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_chargeGas
    unlim_bind_step ltd unlim_push
    simp [Evm.incrPc, Except.toError?, Except.Limited] at ltd
  case mstore =>
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_pop
    unlim_bind_step ltd unlim_chargeGas
    simp [Evm.memWrite, Evm.incrPc, Except.toError?, Except.Limited] at ltd
  case mstore8 =>
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_pop
    unlim_bind_step ltd unlim_chargeGas
    simp [Evm.memWrite, Evm.incrPc, Except.toError?, Except.Limited] at ltd
  case sload =>
    unlim_bind_step ltd unlim_pop
    split at ltd <;> unlim_bind_step ltd unlim_chargeGas
    · unlim_bind_step ltd unlim_push
      simp [Evm.incrPc, Except.toError?, Except.Limited] at ltd
    · unlim_bind_step ltd unlim_push
      simp [Evm.incrPc, Except.toError?, Except.Limited] at ltd
  case sstore =>
    unlim_bind_step ltd unlim_pop
    unlim_bind_step ltd unlim_pop
    have ne : "OutOfGasError" ≠ "RecursionLimit" := by decide
    unlim_bind_step ltd (unlim_assert ne)
    unlim_bind_step ltd unlim_chargeGas
    unlim_bind_step ltd unlim_assertDynamic
    cases ltd
  case tload =>
    unlim_bind_step ltd unlim_pop
    exact unlim_pushItem ltd
  case tstore =>
    unlim_bind_step ltd unlim_pop
    unlim_bind_step ltd unlim_pop
    unlim_bind_step ltd unlim_chargeGas
    unlim_bind_step ltd unlim_assertDynamic
    cases ltd
  case mcopy =>
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_chargeGas
    cases ltd
  case pc => exact unlim_pushItem ltd
  case msize => exact unlim_pushItem ltd
  case gas =>
    unlim_bind_step ltd unlim_chargeGas
    unlim_bind_step ltd unlim_push
    cases ltd
  case dup =>
    unlim_bind_step ltd unlim_chargeGas
    split at ltd
    · simp [Except.toError?, Except.Limited] at ltd
    · unlim_bind_step ltd unlim_push; cases ltd
  case swap =>
    unlim_bind_step ltd unlim_chargeGas
    split at ltd
    · simp [Except.toError?, Except.Limited] at ltd
    · cases ltd
  case log =>
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_popToNat
    unlim_bind_step ltd unlim_pop_n
    unlim_bind_step ltd unlim_chargeGas
    unlim_bind_step ltd unlim_assertDynamic
    cases ltd

lemma Ninst.run_of_run' {evm : Evm} {n : Ninst} (xl : Xlot)
    {ex : Execution} (good : xl.Good') (run : Ninst.Run' evm n xl ex) :
    ex.Unlim ∧ ∃ lim, ∀ lim' > lim, Ninst.run false evm n lim' = ex := by
  rcases n with r | x | ⟨xs, le⟩
  · simp only [Ninst.Run'] at run
    simp only [Ninst.run]; constructor;
    · rw [← run]; apply Rinst.unlim_run
    · refine ⟨0, λ _ _ => run⟩;
  · cases x <;>
      ( simp only [Ninst.Run'] at run; constructor <;>
        [ skip;
          ( apply Exists.imp forall_gt_of_forall_gt_succ_pred;
            simp only [Ninst.run] ) ] )
    · unlim_step_split run unlim_pop
      unlim_step_split run unlim_popToNat
      unlim_step_split run unlim_popToNat
      unlim_step_exists run; unlim_step_exists run
      unlim_step_split run unlim_chargeGas
      unlim_step_exists run; unlim_step_exists run
      unlim_step_exec run good of_generic_create' id
      rw [← run]; apply unlim_ok
    · iterate 3 (efg_step_split run)
      efg_step_exists run; efg_step_exists run
      efg_step_split run
      efg_step_exists run; efg_step_exists run
      efg_step_exec run good of_generic_create'
      eq_split run; exact run
    · unlim_step_split run unlim_pop
      unlim_step_split run (unlim_map_rev unlim_pop)
      unlim_step_split run unlim_pop
      iterate 4 (unlim_step_split run unlim_popToNat)
      iterate 3 (unlim_step_exists run)
      unlim_step_exists_5 run
      iterate 3 (unlim_step_exists run)
      unlim_step_exists_2 run
      unlim_step_split run unlim_chargeGas
      unlim_step_split run (unlim_assert (by decide))
      unlim_step_exists run; unlim_step_exists run
      split at run
      · unlim_step_split run unlim_push
        rw [← run]; apply unlim_ok
      · unlim_step_exec run good of_generic_call' id
        rw [← run]; apply unlim_ok
    · iterate 7 (efg_step_split run)
      iterate 3 (efg_step_exists run)
      efg_step_exists_5 run;
      iterate 3 (efg_step_exists run)
      efg_step_exists_2 run;
      efg_step_split run; efg_step_split run;
      efg_step_exists run; efg_step_exists run;
      efg_step_ite run;
      · efg_step_split run; refine ⟨0, λ _ _ => run⟩
      · efg_step_exec run good of_generic_call'
        eq_split run; exact run
    · unlim_step_split run unlim_pop
      unlim_step_split run (unlim_map_rev unlim_pop)
      unlim_step_split run unlim_pop
      iterate 4 (unlim_step_split run unlim_popToNat)
      iterate 4 (unlim_step_exists run)
      unlim_step_exists_5 run
      unlim_step_exists run; unlim_step_exists run
      unlim_step_exists_2 run
      unlim_step_split run unlim_chargeGas
      unlim_step_exists run; unlim_step_exists run
      split at run
      · unlim_step_split run unlim_push
        rw [← run]; apply unlim_ok
      · unlim_step_exec run good of_generic_call' id
        rw [← run]; apply unlim_ok
    · iterate 7 (efg_step_split run)
      iterate 4 (efg_step_exists run)
      efg_step_exists_5 run;
      iterate 2 (efg_step_exists run)
      efg_step_exists_2 run;
      efg_step_split run
      iterate 2 (efg_step_exists run)
      efg_step_ite run
      · efg_step_split run; refine ⟨0, λ _ _ => run⟩
      · efg_step_exec run good of_generic_call'
        eq_split run; exact run
    · unlim_step_split run unlim_pop
      unlim_step_split run (unlim_map_rev unlim_pop)
      iterate 4 (unlim_step_split run unlim_popToNat)
      iterate 3 (unlim_step_exists run)
      unlim_step_exists_5 run
      unlim_step_exists run
      unlim_step_exists_2 run
      unlim_step_split run unlim_chargeGas
      unlim_step_exists run;
      unlim_step_exec run good of_generic_call' id
      rw [← run]; apply unlim_ok
    · iterate 6 (efg_step_split run)
      iterate 3 (efg_step_exists run)
      efg_step_exists_5 run;
      efg_step_exists run
      efg_step_exists_2 run;
      efg_step_split run
      efg_step_exists run
      efg_step_exec run good of_generic_call'
      eq_split run; exact run
    · unlim_step_split run unlim_pop
      iterate 2 (unlim_step_split run unlim_popToNat)
      unlim_step_split run unlim_pop
      iterate 3 (unlim_step_exists run)
      unlim_step_split run unlim_chargeGas
      iterate 2 (unlim_step_exists run)
      unlim_step_exec run good of_generic_create' id
      rw [← run]; apply unlim_ok
    · iterate 4 (efg_step_split run)
      iterate 3 (efg_step_exists run)
      efg_step_split run
      iterate 2 (efg_step_exists run)
      efg_step_exec run good of_generic_create'
      eq_split run; exact run
    · unlim_step_split run unlim_pop
      unlim_step_split run (unlim_map_rev unlim_pop)
      iterate 4 (unlim_step_split run unlim_popToNat)
      iterate 3 (unlim_step_exists run)
      unlim_step_exists_5 run
      unlim_step_exists run
      unlim_step_exists_2 run
      unlim_step_split run unlim_chargeGas
      unlim_step_exists run;
      unlim_step_exec run good of_generic_call' id
      rw [← run]; apply unlim_ok
    · iterate 6 (efg_step_split run)
      iterate 3 (efg_step_exists run)
      efg_step_exists_5 run;
      efg_step_exists run
      efg_step_exists_2 run;
      efg_step_split run
      efg_step_exists run
      efg_step_exec run good of_generic_call'
      eq_split run; exact run
  · simp [Ninst.Run'] at run; constructor
    · rw [← run]; intro ltd
      unlim_bind_step ltd unlim_chargeGas
      unlim_bind_step ltd unlim_push; cases ltd
    · simp only [Ninst.run]; refine' ⟨0, λ _ _ => run⟩



/-
lemma Ninst.run_of_run' (evm : Evm) (n : Ninst) (xl : Xlot)
    (ex : Execution) (good : xl.Good') (run : Ninst.Run' evm n xl ex) :
    ex.Unlim ∧ ∃ lim, Ninst.run false evm n (lim + 1) = ex := by
  rcases n with r | x | ⟨xs, le⟩
  · simp only [Ninst.Run'] at run
    simp only [Ninst.run]
    constructor
    · rw [← run]; apply Rinst.unlim_run
    · refine ⟨0, run⟩
  · cases x <;> (simp only [Ninst.Run'] at run; simp only [Ninst.run])
    · ule_split run unlim_pop
      ule_split run unlim_popToNat
      ule_split run unlim_popToNat
      ule_exists run; ule_exists run
      ule_split run unlim_chargeGas
      ule_exists run; ule_exists run
      ule_exec run good of_generic_create' id
      · rw [← run]; apply unlim_ok
      · eq_split run; exact run
    · ule_split run unlim_pop; ule_split run (unlim_map_rev unlim_pop)
      ule_split run unlim_pop; ule_split run unlim_popToNat
      ule_split run unlim_popToNat; ule_split run unlim_popToNat
      ule_split run unlim_popToNat; ule_exists run; ule_exists run;
      ule_exists run
      ule_exists_5 run
      ule_exists run
      ule_exists run
      ule_exists run
      ule_exists_2 run
      ule_split run unlim_chargeGas
      ule_split run (unlim_assert (by decide))
      ule_exists run
      ule_exists run
      ule_of_ite run
      · ule_split run unlim_push
        refine' ⟨_, 0, run⟩
        rw [← run]; intro ltd; cases ltd
      · ule_exec run good of_generic_call' id
        · rw [← run]; intro ltd; cases ltd
        · eq_split run; exact run
    · ule_split run unlim_pop; ule_split run (unlim_map_rev unlim_pop)
      ule_split run unlim_pop; ule_split run unlim_popToNat
      ule_split run unlim_popToNat
      ule_split run unlim_popToNat
      ule_split run unlim_popToNat
      ule_exists run
      ule_exists run
      ule_exists run
      ule_exists run
      ule_exists_5 run
      ule_exists run
      ule_exists run
      ule_exists_2 run
      ule_split run unlim_chargeGas
      ule_exists run
      ule_exists run
      ule_of_ite run
      · ule_split run unlim_push
        refine' ⟨_, 0, run⟩
        rw [← run]; intro ltd; cases ltd
      · ule_exec run good of_generic_call' id
        · rw [← run]; intro ltd; cases ltd
        · eq_split run; exact run
    · ule_split run unlim_pop; ule_split run (unlim_map_rev unlim_pop)
      ule_split run unlim_popToNat
      ule_split run unlim_popToNat
      ule_split run unlim_popToNat
      ule_split run unlim_popToNat
      ule_exists run
      ule_exists run
      ule_exists run
      ule_exists_5 run
      ule_exists run
      ule_exists_2 run
      ule_split run unlim_chargeGas
      ule_exists run
      ule_exec run good of_generic_call' id
      · rw [← run]; intro ltd; cases ltd
      · eq_split run; exact run
    · ule_split run unlim_pop; ule_split run (unlim_map_rev unlim_pop)
      ule_split run unlim_popToNat
      ule_split run unlim_pop
      ule_exists run
      ule_exists run
      ule_exists run
      ule_split run unlim_chargeGas
      ule_exists run
      ule_exists run
      ule_exec run good of_generic_create' id
      · rw [← run]; intro ltd; cases ltd
      · eq_split run; exact run
    · ule_split run unlim_pop; ule_split run (unlim_map_rev unlim_pop)
      ule_split run unlim_popToNat
      ule_split run unlim_popToNat
      ule_split run unlim_popToNat
      ule_split run unlim_popToNat
      ule_exists run
      ule_exists run
      ule_exists run
      ule_exists_5 run
      ule_exists run
      ule_exists_2 run
      ule_split run unlim_chargeGas
      ule_exists run
      ule_exec run good of_generic_call' id
      · rw [← run]; intro ltd; cases ltd
      · eq_split run; exact run
  · simp [Ninst.Run'] at run
    simp only [Ninst.run]
    refine' ⟨_, 0, run⟩
    rw [← run]; clear run; intro ltd
    unlim_bind_step ltd unlim_chargeGas
    unlim_bind_step ltd unlim_push
    cases ltd
-/

--lemma Ninst.unlim_run (evm : Evm) (n : Ninst) :
--    ¬ (Rinst.run evm r).Limited := by
--  sorry

lemma Except.bind_eq_of_is_error {ξ υ : Type} {e : Except ξ υ}
    {f : υ → Except ξ υ} : e.IsError → (e >>= f) = e := by
  intro h; cases e
  · rfl
  · cases h

lemma exec_succ {evm : Evm} {lim : Nat} :
  exec false evm (lim + 1) =
    ( do let i ← (evm.getInst).toExcept ⟨"InvalidOpcode", evm⟩
         match i with
         | .next n =>
           let evm ← n.run false evm lim
           exec false evm lim
         | .jump j =>
           let evm ← j.run evm
           exec false evm lim
         | .last l => l.run evm ) := by
  simp only [exec]; rfl

lemma Jinst.unlim_run {evm} {j : Jinst} :
    ¬ (Jinst.run evm j).Limited := by
  intro ltd; cases j <;> simp only [Jinst.run] at ltd
  case jumpi =>
    unlim_bind_step ltd unlim_pop
    unlim_bind_step ltd unlim_pop
    unlim_bind_step ltd unlim_chargeGas
    split at ltd
    · unlim_bind_step ltd unlim_ok; cases ltd
    · unlim_bind_step ltd (unlim_assert (by decide))
      unlim_bind_step ltd unlim_ok; cases ltd
  case jumpdest =>
    unlim_bind_step ltd unlim_chargeGas; cases ltd
  case jump =>
    unlim_bind_step ltd unlim_pop
    unlim_bind_step ltd unlim_chargeGas
    unlim_bind_step ltd (unlim_assert (by decide))
    cases ltd

lemma of_exec' :
    ∀ (evm : Evm) (ex : Execution), Exec evm ex →
      ex.Unlim ∧ ∃ lim, ∀ lim' > lim, (exec false evm lim' = ex) := by
  apply Exec.rec
  · intro evm eq; refine' ⟨_, 0, _⟩
    · intro ltd; injection ltd; contradiction
    · intro lim' gt; cases lim'; {cases Nat.not_lt_zero _ gt}
      simp only [exec, Option.toExcept, eq]; rfl
  · intro evm n ex get run is_err
    rcases Ninst.run_of_run' .none .intro run
      with ⟨unlim, lim, eq⟩
    refine' ⟨unlim, lim + 2, _⟩
    intro lim' gt; rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [Ninst.At] at get
    simp only [Evm.getInst, ok_bind, exec, Option.toExcept, get]
    rw [eq lim' (by omega)]
    apply Except.bind_eq_of_is_error; exact is_err
  · intro evm n evm' ex' ex get run exc isErr ⟨unlim', limExec, exec_eq⟩
    rcases
      Ninst.run_of_run'
        (.some ⟨evm', ex'⟩)
        ⟨unlim', limExec + 1, exec_eq _ (by omega)⟩
        run
      with ⟨unlim, limRun, run_eq⟩
    refine' ⟨unlim, (max limExec limRun) + 1, _⟩
    intro lim' gt; rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [Ninst.At] at get
    simp only [Evm.getInst, ok_bind, exec, Option.toExcept, get]
    rw [run_eq lim' (by omega)]
    apply Except.bind_eq_of_is_error; exact isErr
  · intro evm n evm' ex get run exc ⟨unlim, limExec, exec_eq⟩
    rcases Ninst.run_of_run' .none .intro run
      with ⟨temp, limRun, run_eq⟩; clear temp
    refine' ⟨unlim, (max limExec limRun) + 1, _⟩
    intro lim' gt; rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [Ninst.At] at get
    simp only [Evm.getInst, ok_bind, exec, Option.toExcept, get]
    rw [run_eq lim' (by omega)]
    apply exec_eq _ (by omega)
  · intro evm n evm' ex' evm'' ex get run exec' exec
      ⟨unlim', limExec', exec_eq'⟩
      ⟨unlim, limExec, exec_eq⟩
    rcases
      Ninst.run_of_run'
        (.some ⟨evm', ex'⟩)
        ⟨unlim', limExec' + 1, exec_eq' _ (by omega)⟩
        run
      with ⟨unlimRun, limRun, run_eq⟩
    refine' ⟨unlim, max limRun limExec + 1, _⟩
    intro lim' gt; rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [Ninst.At] at get
    simp only [Evm.getInst, ok_bind, _root_.exec, Option.toExcept, get]
    rw [run_eq lim' (by omega)]
    apply exec_eq _ (by omega)
  · intro evm j ex get run is_err;
    simp only [Jinst.At] at get
    simp only [Jinst.Run] at run
    constructor
    · rw [← run]; apply Jinst.unlim_run
    · refine' ⟨0, _⟩; intro lim gt
      rcases lim with _ | lim; {cases Nat.not_lt_zero _ gt}
      simp only [Evm.getInst, exec, get, Option.toExcept, ok_bind, run]
      apply Except.bind_eq_of_is_error; exact is_err
  · intro evm j evm' ex get run exc ⟨unlim, lim, exec_eq⟩  ----is_err;
    simp only [Jinst.At] at get
    simp only [Jinst.Run] at run
    refine' ⟨unlim, lim + 1, _⟩; intro lim' gt
    rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [Evm.getInst, exec, get, Option.toExcept, ok_bind, run]
    apply exec_eq _ (by omega)
  · intro evm l ex get run;
    simp only [Linst.At] at get
    simp only [Linst.Run] at run
    refine' ⟨Linst.unlim_of_run run, 0, _⟩; intro lim' gt
    rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [Evm.getInst, exec, get, Option.toExcept, ok_bind, run]

lemma exec_iff_exec (evm : Evm) (ex : Execution) :
    --Exec evm ex ↔ (ex.Unlim ∧ ∃ lim, exec false evm lim = ex) := by
    Nonempty (Exec evm ex) ↔ (ex.Unlim ∧ ∃ lim, exec false evm lim = ex) := by
  constructor
  · intro ⟨exc⟩; rcases of_exec' _ _ exc with ⟨unlim, lim, eq⟩
    refine ⟨unlim, lim + 1, eq (lim + 1) (by omega)⟩
  · intro ⟨unlim, lim, eq⟩; exact of_exec _ _ _ unlim eq

def Xlot.Filled : Xlot → Prop
  | .none => True
  | .some ⟨evm, exn⟩ => Nonempty (Exec evm exn)

def Ninst.Run (evm : Evm) (n : Ninst) (evm' : Evm) : Prop :=
  ∃ xl, xl.Filled ∧ Ninst.Run' evm n xl (.ok evm')

def Evm.Equiv (evm evm' : Evm) : Prop :=
  Evm.Rel Evm.Rels.equiv evm evm'

infix:70 " ≅ "  => Evm.Equiv

lemma Evm.equiv_refl (evm : Evm) : evm ≅ evm := by
  constructor <;> rfl

lemma Evm.equiv_symm {evm evm' : Evm} (h : evm ≅ evm') : evm' ≅ evm := by
  constructor
  · exact h.stack.symm
  · exact h.memory.symm
  · exact h.code.symm
  · exact h.logs.symm
  · exact h.msg.symm
  · exact h.output.symm
  · exact h.returnData.symm
  · exact h.error.symm

lemma Evm.equiv_trans {evm₁ evm₂ evm₃ : Evm} (h1 : evm₁ ≅ evm₂) (h2 : evm₂ ≅ evm₃) : evm₁ ≅ evm₃ := by
  constructor
  · exact h1.stack.trans h2.stack
  · exact h1.memory.trans h2.memory
  · exact h1.code.trans h2.code
  · exact h1.logs.trans h2.logs
  · exact h1.msg.trans h2.msg
  · exact h1.output.trans h2.output
  · exact h1.returnData.trans h2.returnData
  · exact h1.error.trans h2.error

lemma rel_of_rel_of_equiv {evm evm' evm''} {rs : Evm.Rels}
    (rel : Evm.Rel rs evm evm') (equiv : evm' ≅ evm'') :
    Evm.Rel rs evm evm'' := by
  constructor
  · rw [← equiv.stack]; exact rel.stack
  · rw [← equiv.memory]; exact rel.memory
  · rw [← equiv.code]; exact rel.code
  · rw [← equiv.logs]; exact rel.logs
  · rw [← equiv.msg]; exact rel.msg
  · rw [← equiv.output]; exact rel.output
  · rw [← equiv.returnData]; exact rel.returnData
  · rw [← equiv.error]; exact rel.error

lemma rel_of_equiv_of_rel {evm evm' evm''} {rs : Evm.Rels}
    (equiv : evm ≅ evm') (rel : Evm.Rel rs evm' evm'') :
    Evm.Rel rs evm evm'' := by
  constructor
  · rw [equiv.stack]; exact rel.stack
  · rw [equiv.memory]; exact rel.memory
  · rw [equiv.code]; exact rel.code
  · rw [equiv.logs]; exact rel.logs
  · rw [equiv.msg]; exact rel.msg
  · rw [equiv.output]; exact rel.output
  · rw [equiv.returnData]; exact rel.returnData
  · rw [equiv.error]; exact rel.error

inductive Func.Run : List Func → Evm → Func → Evm → Prop
  | zero :
    ∀ {fs evm evm' f g evm''},
      Evm.Pop [0] evm evm' →
      Func.Run fs evm' f evm'' →
      Func.Run fs evm (branch f g) evm''
  | succ :
    ∀ {fs evm w evm' f g evm''},
      w ≠ 0 →
      Evm.Pop [w] evm evm' →
      Func.Run fs evm' g evm'' →
      Func.Run fs evm (branch f g) evm''
  | last :
    ∀ {fs evm evm' i evm'' evm'''},
      evm ≅ evm' →
      Linst.Run evm' i (.ok evm'') →
      evm'' ≅ evm''' →
      Func.Run fs evm (last i) evm'''
  | next :
    ∀ {fs evm evm' i evm'' f evm'''},
      evm ≅ evm' →
      Ninst.Run evm' i evm'' →
      Func.Run fs evm'' f evm''' →
      Func.Run fs evm (next i f) evm'''
  | call :
    ∀ {fs evm k f evm'},
      fs[k]? = some f →
      Func.Run fs evm f evm' →
      Func.Run fs evm (call k) evm'

lemma Func.run_well_def {fs ievm ievm' f fevm fevm'}
    (run : Func.Run fs ievm f fevm) (ieqv : ievm ≅ ievm')
    (feqv : fevm ≅ fevm') : Func.Run fs ievm' f fevm' := by
  induction run generalizing ievm' fevm'
  case zero pop run ih =>
    apply Func.Run.zero (rel_of_equiv_of_rel (Evm.equiv_symm ieqv) pop)
    apply ih (Evm.equiv_refl _) feqv
  case succ h pop run ih =>
    apply Func.Run.succ h (rel_of_equiv_of_rel (Evm.equiv_symm ieqv) pop)
    apply ih (Evm.equiv_refl _) feqv
  case last h_eqv run_l h_eqv' =>
    apply Func.Run.last (Evm.equiv_trans (Evm.equiv_symm ieqv) h_eqv) run_l
    apply Evm.equiv_trans h_eqv' feqv
  case next eqv_next run_i run_f ih =>
    apply Func.Run.next (Evm.equiv_trans (Evm.equiv_symm ieqv) eqv_next) run_i
    apply ih (Evm.equiv_refl _) feqv
  case call h_get run ih =>
    apply Func.Run.call h_get
    apply ih ieqv feqv

def Prog.Run (evm : Evm) (p : Prog) (evm' : Evm) : Prop :=
  Func.Run (p.main :: p.aux) evm p.main evm'

#exit
inductive Func.Run : List Func → Evm → Func → Execution → Prop
  | zero :
    ∀ {fs evm evm' f g exn},
      Evm.Pop [0] evm evm' →
      Func.Run fs evm' f exn →
      Func.Run fs evm (branch f g) exn
  | succ :
    ∀ {fs evm w evm' f g exn},
      w ≠ 0 →
      Evm.Pop [w] evm evm' →
      Func.Run fs evm' g exn →
      Func.Run fs evm (branch f g) exn
  | last :
    ∀ {fs evm i exn},
      Linst.Run' evm i exn →
      Func.Run fs evm (last i) exn
  | next :
    ∀ {fs evm i evm' f exn},
      Ninst.Run evm i evm' →
      Func.Run fs evm' f exn →
      Func.Run fs evm (next i f) exn
  | call :
    ∀ {fs evm k f exn},
      fs[k]? = some f →
      Func.Run fs evm f exn →
      Func.Run fs evm (call k) exn


def Prog.Run (evm : Evm) (p : Prog) (exn : Execution) : Prop :=
  Func.Run (p.main :: p.aux) evm p.main exn




#exit


-- inductive Ninst.Run : Env → Desc → Ninst → Desc → Prop
--   | reg :
--     ∀ {e s o s'},
--       Rinst.Run e s o s' →
--       Ninst.Run e s (Ninst.reg o) s'
--   | exec :
--     ∀ {e s o s'},
--       Xinst.Run e s o s' →
--       Ninst.Run e s (Ninst.exec o) s'
--   | push :
--     ∀ e {s bs h s'},
--       Evm.Push [B8L.toB256 bs] s s' →
--       Ninst.Run e s (Ninst.push bs h) s'


#check Rinst.Run

#exit
inductive Ninst.Run : Evm → Ninst → Evm → Prop
  | reg :
    ∀ {e s o s'},
      Rinst.Run e s o s' →
      Ninst.Run e s (Ninst.reg o) s'
  | exec :
    ∀ {e s o s'},
      Xinst.Run e s o s' →
      Ninst.Run e s (Ninst.exec o) s'
  | push :
    ∀ e {s bs h s'},
      Evm.Push [B8L.toB256 bs] s s' →
      Ninst.Run e s (Ninst.push bs h) s'












#exit
lemma of_exec (evm : Evm) (ex : Execution) :
    Exec evm ex → (¬ ex.Limited ∧ ∃ lim, exec false lim evm = ex) := by sorry

lemma notLimited_of_exec (evm : Evm) (ex : Execution) :
    Exec evm ex → ¬ ex.Limited := by sorry

lemma exists_exec_of_exec (evm : Evm) (ex : Execution) :
    Exec evm ex → ∃ lim, (exec false lim evm = ex) := by sorry

def exec_iff (evm : Evm) (ex : Execution) :
    Exec evm ex ↔ ((∃ lim, exec false lim evm = ex) ∧ ¬ ex.Limited) := by
  constructor <;> intro h
  · refine ⟨exists_exec_of_exec _ _ h, notLimited_of_exec _ _ h⟩
  · rcases h with ⟨⟨lim, eq⟩, notLimited⟩
    apply exec_of_exec _ _ _ notLimited eq

def ValidateHeader (chain : BlockChain) (header : Header)
    (ex : Except String Unit) : Prop :=
    (chain.blocks.getLast?.toExcept "No parent block found").Split ex <|
  λ parent =>
    ( calculateBaseFeePerGas
      header.gasLimit
      parent.header.gasLimit
      parent.header.gasUsed
      parent.header.baseFeePerGas ).Split ex <|
  λ expectedBaseFeePerGas =>
  ∃ blockParentHash,
    And (blockParentHash = (Header.toBLT parent.header).toB8L.keccak) <|
  if header.excessBlobGas ≠ calculateExcessBlobGas parent.header then
    (.error "InvalidBlock : ExcessBlobGas does not match expected value") = ex
  else if header.gasUsed > header.gasLimit then
    (.error s!"InvalidBlock : gas used = {header.gasUsed} > gas limit = {header.gasLimit}") = ex
  else if expectedBaseFeePerGas ≠ header.baseFeePerGas then
    (.error "InvalidBlock : BaseFeePerGas does not match expected value") = ex
  else if header.timestamp ≤ parent.header.timestamp then
    (.error "InvalidBlock : Timestamp does not match expected value") = ex
  else if header.number ≠ parent.header.number + 1 then
    (.error "InvalidBlock : number does not match expected value") = ex
  else if header.extraData.length > 32 then
    (.error "InvalidBlock : ExtraData exceeds 32 bytes") = ex
  else if header.difficulty ≠ 0 then
    (.error "InvalidBlock : Difficulty does not match expected value") = ex
  else if header.nonce ≠ 0 then
    (.error "InvalidBlock : nonce does not match expected value") = ex
  else if header.ommersHash ≠ emptyOmmerHash then
    (.error s!"InvalidBlock : expected ommers hash = {emptyOmmerHash}, computed ommers hash") = ex
  else if header.parentHash ≠ blockParentHash then
    (.error "InvalidBlock : parentHash does not match expected value") = ex
  else
    .ok () = ex

def StateTransitionOmmersCheck (ommers : List Header)
    (ex : Except String Unit) : Prop :=
  if ¬ommers.isEmpty then
    .error "InvalidBlock" = ex
  else
    .ok () = ex

def StateTransition (vb : Bool) (ch : BlockChain) (block : Block)
    (ex : Except String BlockChain) : Prop :=
    (validateHeader ch block.header).Split ex <|
  λ _ =>
    (stateTransitionOmmersCheck block.ommers).Split ex <|
  λ _ =>
    let benv : Benv := initBenv ch block.header
    (applyBody vb benv block.txs block.wds).Split ex <|
  λ ⟨st, bout⟩ =>
    let blockStateRoot : B256 := st.root
    let transactionsRoot : B256 := getTransactionsRoot bout
    let receiptRoot : B256 := getReceiptRoot bout
    let blockLogsBloom : B8L := logsBloom bout.blockLogs
    let withdrawalsRoot : B256 := getWithdrawalsRoot bout
    let requestsHash := computeRequestsHash bout.requests
    ( stateTransitionChecks bout block.header
      transactionsRoot blockStateRoot receiptRoot
      blockLogsBloom withdrawalsRoot requestsHash ).Split ex <|
  λ _ =>
    .ok ⟨appendBlock ch.blocks block, st, ch.chainId⟩ = ex
