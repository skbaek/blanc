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
  | tload        => 0x5C
  | tstore       => 0x5D
  | mcopy        => 0x5E
  | pc           => 0x58
  | msize        => 0x59
  | gas          => 0x5A
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
def Stack.Diff (xs zs : Stack) (s s'' : Stack) : Prop := -- Pop xs ⊚ Push ys
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

def Mstored (x : B256) (bs : B8L) (m m' : Memory) : Prop := m' = Memory.store x bs m

-- def Decrease (k : Adr) (v : B256) (f g : Adr → B256) : Prop :=
--   Frel k (λ x y => x - v = y) f g
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

structure Desc.Rels where
  (bal : Balances → Balances → Prop)
  (stor : Storages → Storages → Prop)
  (code : Codes → Codes → Prop)
  (stk : Stack → Stack → Prop)
  (mem : Memory → Memory → Prop)
  (ret : B8L → B8L → Prop)
  (dest : List Adr → List Adr → Prop)

def Desc.Rels.dft : Rels :=
  {bal := Eq, stor := Eq, code := Eq, stk := Eq, mem := Eq, ret := Eq, dest := Eq}

structure Desc.Rel (r : Rels) (s s' : Desc) : Prop where
  (bal  : r.bal  (Desc.bal s) (Desc.bal s'))
  (stor : r.stor (Desc.stor s) (Desc.stor s'))
  (code : r.code (Desc.code s) (Desc.code s'))
  (stk  : r.stk  (Desc.stk s) (Desc.stk s'))
  (mem  : r.mem  (Desc.mem s) (Desc.mem s'))
  (ret  : r.ret  (Desc.ret s) (Desc.ret s'))
  (dest : r.dest (Desc.dest s) (Desc.dest s'))

def Desc.Diff (xs ys : List B256) : Desc → Desc → Prop :=
  Rel {Rels.dft with stk := Stack.Diff xs ys}

def Desc.Push (xs : List B256) : Desc → Desc → Prop :=
  Rel {Rels.dft with stk := Stack.Push xs}

def Desc.Pop (xs : List B256) : Desc → Desc → Prop :=
  Rel {Rels.dft with stk := Stack.Pop xs}

def Desc.Swap (n : Nat) : Desc → Desc → Prop :=
  Rel {Rels.dft with stk := Stack.Swap n}

def Desc.Dup (n : Nat) : Desc → Desc → Prop :=
  Rel {Rels.dft with stk := Stack.Dup n}

def Desc.Add (s s' : Desc) : Prop :=  ∃ x y, Desc.Diff [x, y] [x + y] s s'
def Desc.Sub (s s' : Desc) : Prop :=  ∃ x y, Desc.Diff [x, y] [x - y] s s'
def Desc.Mul (s s' : Desc) : Prop := ∃ x y, Desc.Diff [x, y] [x * y] s s'
def Desc.Div (s s' : Desc) : Prop := ∃ x y, Desc.Diff [x, y] [x / y] s s'
def Desc.Mod (s s' : Desc) : Prop := ∃ x y, Desc.Diff [x, y] [x % y] s s'
def Desc.Sdiv (s s' : Desc) : Prop := ∃ x y, Desc.Diff [x, y] [B256.sdiv x y] s s'
def Desc.Smod (s s' : Desc) : Prop := ∃ x y, Desc.Diff [x, y] [B256.smod x y] s s'
def Desc.Addmod (s s' : Desc) : Prop := ∃ x y z, Desc.Diff [x, y, z] [B256.addmod x y z] s s'
def Desc.Mulmod (s s' : Desc) : Prop := ∃ x y z, Desc.Diff [x, y, z] [B256.mulmod x y z] s s'
def Desc.Exp (s s' : Desc) : Prop := ∃ x y, Desc.Diff [x, y] [x ^ y] s s'

-- def B256.Signext (x y y' : B256) : Prop :=
--   ∃ b, Bits.Signext (256 - (8 * (x.toNat + 1))) b y y'

def Desc.Signextend (s s' : Desc) : Prop :=
  ∃ x y z,
    Desc.Diff [x, y] [z] s s' ∧
    -- B256.Signext x y z
    B256.signext x y = z


-- def lt_check (x y : B256) : B256 := if x < y then 1 else 0
-- def gt_check (x y : B256) : B256 := if x > y then 1 else 0
-- def slt_check (x y : B256) : B256 := if x ±< y then 1 else 0
-- def sgt_check (x y : B256) : B256 := if x ±> y then 1 else 0
-- def eq_check (x y : B256) : B256 := if x = y then 1 else 0

infix:70 " <? "  => B256.lt_check
infix:70 " >? "  => B256.gt_check
infix:70 " ±<? " => B256.slt_check
infix:70 " ±>? " => B256.sgt_check
infix:70 " =? "  => B256.eq_check

def Char.toB8 (c : Char) : B8 := Nat.toUInt8 c.toNat
def String.toB8L (s : String) : B8L := s.data.map Char.toB8



-- def Bytes.keccak (xs : Bytes) : B256 :=
--   xs.toB8L.keccak.toBits


def String.keccak (s : String) : B256 := s.toB8L.keccak

def Desc.Lt (s s' : Desc) : Prop := ∃ x y, Desc.Diff [x, y] [x <? y] s s'
def Desc.Gt (s s' : Desc) : Prop := ∃ x y, Desc.Diff [x, y] [x >? y] s s'
def Desc.Slt (s s' : Desc) : Prop := ∃ x y, Desc.Diff [x, y] [x ±<? y] s s'
def Desc.Sgt (s s' : Desc) : Prop := ∃ x y, Desc.Diff [x, y] [x ±>? y] s s'
def Desc.Eq (s s' : Desc) : Prop := ∃ x y, Desc.Diff [x, y] [x =? y] s s'
def Desc.Iszero (s s' : Desc) : Prop := ∃ x, Desc.Diff [x] [x =? 0] s s'
def Desc.And (s s' : Desc) : Prop := ∃ x y, Desc.Diff [x, y] [x &&& y] s s'
def Desc.Or (s s' : Desc) : Prop := ∃ x y, Desc.Diff [x, y] [x ||| y] s s'
def Desc.Xor (s s' : Desc) : Prop := ∃ x y, Desc.Diff [x, y] [x ^^^ y] s s'
def Desc.Not (s s' : Desc) : Prop := ∃ x, Desc.Diff [x] [~~~ x] s s'
-- def Desc.Byte (s s' : Desc) : Prop :=
--   ∃ (x y : B256) (b : B8),
--     Desc.Diff [x, y] [(0 : Bits 248) ++ b] s s' ∧
--     List.getD (@Bits.toBytes 32 y) x.toNat 0 = b
def Desc.Byte (s s' : Desc) : Prop :=
  ∃ (x y : B256),
    Desc.Diff [x, y] [(List.getD y.toB8L x.toNat 0).toB256] s s'
def Desc.Shl (s s' : Desc) : Prop := ∃ x y, Desc.Diff [x, y] [y <<< x.toNat] s s'
def Desc.Shr (s s' : Desc) : Prop := ∃ x y, Desc.Diff [x, y] [y >>> x.toNat] s s'
def Desc.Sar (s s' : Desc) : Prop := ∃ x y, Desc.Diff [x, y] [B256.arithShiftRight y x.toNat] s s'
def Desc.Kec (s s' : Desc) : Prop :=
  ∃ x y, Desc.Diff [x, y] [(Memory.slice s.mem x y).keccak] s s'
def B8L.Size (bs : B8L) (sz : B256) : Prop := bs.length = sz.toNat
def Desc.Adress (e : Env) (s s' : Desc) : Prop := Desc.Push [Adr.toB256 e.cta] s s'
def Desc.Balance (s s' : Desc) : Prop :=
  ∃ x : B256, Desc.Diff [x] [s.bal x.toAdr] s s'
def Desc.Origin (e : Env) (s s' : Desc) : Prop := Desc.Push [Adr.toB256 e.oga] s s'
def Desc.Caller (e : Env) (s s' : Desc) : Prop := Desc.Push [Adr.toB256 e.cla] s s'
def Desc.Callvalue (e : Env) (s s' : Desc) : Prop := Desc.Push [e.clv] s s'
def Desc.Calldatasize (e : Env) (s s' : Desc) : Prop := ∃ sz, Desc.Push [sz] s s' ∧ B8L.Size e.cld sz
def Desc.Codesize (e : Env) (s s' : Desc) : Prop := ∃ sz, Desc.Push [sz] s s' ∧ B8L.Size e.code sz
def Desc.Gasprice (e : Env) (s s' : Desc) : Prop := Desc.Push [e.gpr] s s'
def Desc.Extcodesize (s s' : Desc) : Prop :=
  ∃ x sz, Desc.Diff [x] [sz] s s' ∧ B8L.Size (s.code x.toAdr) sz
def Desc.Retdatasize (s s' : Desc) : Prop :=
  ∃ x r, Desc.Push [x] s s' ∧ s.ret = r ∧ B8L.Size r x

-- For verification tasks where using correct values of Keccak hashes is crucial for correctness,
-- we can define a (keccak : B8L → B256) and use it in the definition of Desc.extcodehash,
-- and also the Rinst.kec constructor of 'step'. For correctness of the WETH contract, however,
-- it suffices to require that _some_ hash value is computed and added to the Stack.

def Desc.Extcodehash (s s' : Desc) : Prop :=
  ∃ x y, Desc.Diff [x] [y] s s'

def Desc.Calldataload (e : Env) (s s' : Desc) : Prop :=
  ∃ x y,
    Desc.Diff [x] [y] s s' ∧
    List.sliceD e.cld x.toNat 32 0 = y.toB8L -- @Bits.toBytes 32 y

def Desc.Calldatacopy (e : Env) (s s' : Desc) : Prop :=
  ∃ x y z,
    Desc.Rel
      { Desc.Rels.dft with
        stk := Stack.Pop [x, y, z],
        mem := Mstored x <| List.sliceD e.cld y.toNat z.toNat 0 } s s'

def Desc.Mcopy (s s' : Desc) : Prop :=
  ∃ x y z,
    Desc.Rel
      {
        Desc.Rels.dft with
        stk := Stack.Pop [x, y, z],
        mem := Mstored x <| Memory.slice s.mem y z
      }
      s s'

def Desc.Codecopy (e : Env) (s s' : Desc) : Prop :=
  ∃ x y z bs,
    Desc.Rel
      { Desc.Rels.dft with
        stk := Stack.Pop [x, y, z],
        mem := Mstored x bs } s s' ∧
    List.slice? e.code y.toNat z.toNat = some bs

def Desc.Extcodecopy (s s' : Desc) : Prop :=
  ∃ w x y z bs,
    Desc.Rel
      { Desc.Rels.dft with
        stk := Stack.Pop [w, x, y, z],
        mem := Mstored x bs }
      s s' ∧
    List.slice? (s.code w.toAdr) y.toNat z.toNat = some bs

def Desc.Retdatacopy (s s' : Desc) : Prop :=
  ∃ x y z,
    Desc.Rel
      { Desc.Rels.dft with
        stk := Stack.Pop [x, y, z],
        mem := Mstored x <| List.sliceD s.ret y.toNat z.toNat 0 }
      s s'

-- One thing that all block operations have in common is that they consume
-- no Stack items, leave exactly one new item on the Stack, and change nothing
-- else in the Desc. The contents of the new item depend on the operation used,
-- but their differences are immaterial for current purposes of the formalization,
-- so that part is unspecified here. These definitions will need to be augmented
-- to  verify more detailed properties about block operations.

def Desc.Tstore (e : Env) (s s' : Desc) : Prop :=
  ∃ x y : B256,
    Desc.Rel
    { Desc.Rels.dft with
      -- todo : add t-storage condition
      stk := Stack.Diff [x, y] [] } s s' ∧
    e.wup = 1

def Desc.Sstore (e : Env) (s s' : Desc) : Prop :=
  ∃ x y : B256,
    Desc.Rel
    { Desc.Rels.dft with
      stor := Frel e.cta (Overwrite x y),
      stk := Stack.Diff [x, y] [] } s s' ∧
    e.wup = 1

def Desc.Sload (e : Env) (s s' : Desc) : Prop :=
  ∃ x, Desc.Diff [x] [s.stor e.cta x] s s'

def Desc.Tload (s s' : Desc) : Prop :=
  ∃ x y, Desc.Diff [x] [y] s s' -- todo : use value from t-storage

def Desc.Mload (s s' : Desc) : Prop :=
  ∃ x y, Desc.Diff [x] [y] s s' ∧
    Memory.slice s.mem x 32 = y.toB8L

def Desc.Mstore (s s' : Desc) : Prop :=
  ∃ x y,
    Desc.Rel
      { Desc.Rels.dft with
        stk := Stack.Diff [x, y] [],
        mem := Mstored x y.toB8L }
      s s'

def Desc.Mstore8 (s s' : Desc) : Prop :=
  ∃ (x y : B256),
    Desc.Rel
      { Desc.Rels.dft with
        stk := Stack.Diff [x, y] [],
        mem := Mstored x [y.2.2.toUInt8] } s s'

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

def Rinst.At (e : Env) (pc : Nat) (o : Rinst) : Prop := e.code[pc]? = some (Rinst.toB8 o)
def Jinst.At (e : Env) (pc : Nat) (o : Jinst) : Prop := e.code[pc]? = some (Jinst.toB8 o)
def Xinst.At (e : Env) (pc : Nat) (o : Xinst) : Prop := e.code[pc]? = some (Xinst.toB8 o)
def Linst.At (e : Env) (pc : Nat) (o : Linst) : Prop := e.code[pc]? = some (Linst.toB8 o)
def PushAt (e : Env) (pc : Nat) (bs : B8L) : Prop :=
  List.Slice e.code pc (pushToB8L bs) ∧ bs.length ≤ 32

inductive Linst.Run : Env → Desc → Linst → Result → Prop
  | stop : ∀ e s, Linst.Run e s Linst.stop (Result.wrap s [])
  | ret :
    ∀ e s x y,
      ([x, y] <+: s.stk) →
      Linst.Run e s Linst.ret (.wrap s <| s.mem.slice x y)
  | dest :
    ∀ (e : Env) (s : Desc) x bal bal',
      e.wup = 1 →
      ([x] <+: s.stk) →
      Overwrite e.cta 0 s.bal bal →
      Increase x.toAdr (s.bal e.cta) bal bal' →
      Linst.Run e s Linst.dest {s with bal := bal', ret := [], dest := e.cta :: s.dest}

def insidePushArg (e : Env) (loc : Nat) : Prop :=
  ∃ (pc : Nat) (bs : B8L), PushAt e pc bs ∧ pc < loc ∧ loc ≤ pc + bs.length

def Jumpable (e : Env) (n : Nat) : Prop :=
  Jinst.At e n Jinst.jumpdest ∧ ¬ insidePushArg e n

def Fail (s : Desc) (o : Xinst) (s' : Desc) : Prop :=
  match o with
  | .create => ∃ x y z, Desc.Pop [x, y, z] s s'
  | .call => ∃ x₀ x₁ x₂ x₃ x₄ x₅ x₆, Desc.Pop [x₀, x₁, x₂, x₃, x₄, x₅, x₆] s s'
  | .callcode => ∃ x₀ x₁ x₂ x₃ x₄ x₅ x₆, Desc.Pop [x₀, x₁, x₂, x₃, x₄, x₅, x₆] s s'
  | .delcall => ∃ x₀ x₁ x₂ x₃ x₄ x₅, Desc.Pop [x₀, x₁, x₂, x₃, x₄, x₅] s s'
  | .create2 => ∃ x₀ x₁ x₂ x₃, Desc.Pop [x₀, x₁, x₂, x₃] s s'
  | .statcall => ∃ x₀ x₁ x₂ x₃ x₄ x₅, Desc.Pop [x₀, x₁, x₂, x₃, x₄, x₅] s s'

def Rinst.Run (e : Env) : Desc → Rinst → Desc → Prop :=
  Function.swap <|
    fun
    | Rinst.add => Desc.Add
    | Rinst.sub => Desc.Sub
    | Rinst.mul => Desc.Mul
    | Rinst.div => Desc.Div
    | Rinst.mod => Desc.Mod
    | Rinst.sdiv => Desc.Sdiv
    | Rinst.smod => Desc.Smod
    | Rinst.addmod => Desc.Addmod
    | Rinst.mulmod => Desc.Mulmod
    | Rinst.exp => Desc.Exp
    | Rinst.signextend => Desc.Signextend
    | Rinst.lt => Desc.Lt
    | Rinst.gt => Desc.Gt
    | Rinst.slt => Desc.Slt
    | Rinst.sgt => Desc.Sgt
    | Rinst.eq => Desc.Eq
    | Rinst.iszero => Desc.Iszero
    | Rinst.and => Desc.And
    | Rinst.or => Desc.Or
    | Rinst.xor => Desc.Xor
    | Rinst.not => Desc.Not
    | Rinst.byte => Desc.Byte
    | Rinst.shl => Desc.Shl
    | Rinst.shr => Desc.Shr
    | Rinst.sar => Desc.Sar
    | Rinst.kec => Desc.Kec
    | Rinst.address => Desc.Adress e
    | Rinst.balance => Desc.Balance
    | Rinst.origin => Desc.Origin e
    | Rinst.caller => Desc.Caller e
    | Rinst.callvalue => Desc.Callvalue e
    | Rinst.calldataload => Desc.Calldataload e
    | Rinst.calldatasize => Desc.Calldatasize e
    | Rinst.calldatacopy => Desc.Calldatacopy e
    | Rinst.codesize => Desc.Codesize e
    | Rinst.codecopy => Desc.Codecopy e
    | Rinst.gasprice => Desc.Gasprice e
    | Rinst.extcodesize => Desc.Extcodesize
    | Rinst.extcodecopy => Desc.Extcodecopy
    | Rinst.retdatasize => Desc.Retdatasize
    | Rinst.retdatacopy => Desc.Retdatacopy
    | Rinst.extcodehash => Desc.Extcodehash
    | Rinst.blockhash => λ s s' => ∃ x, Desc.Push [x] s s'
    | Rinst.coinbase => λ s s' => ∃ x, Desc.Push [x] s s'
    | Rinst.timestamp => λ s s' => ∃ x, Desc.Push [x] s s'
    | Rinst.number => λ s s' => ∃ x, Desc.Push [x] s s'
    | Rinst.prevrandao => λ s s' => ∃ x, Desc.Push [x] s s'
    | Rinst.gaslimit => λ s s' => ∃ x, Desc.Push [x] s s'
    | Rinst.chainid => λ s s' => ∃ x, Desc.Push [x] s s'
    | Rinst.selfbalance => λ s s' => ∃ x, Desc.Push [x] s s'
    | Rinst.basefee => λ s s' => ∃ x, Desc.Push [x] s s'
    | Rinst.blobhash => λ s s' => ∃ x y, Desc.Diff [x] [y] s s'
    | Rinst.blobbasefee => λ s s' => ∃ x, Desc.Push [x] s s'
    | Rinst.pop => λ s s' => ∃ x, Desc.Pop [x] s s'
    | Rinst.mload => Desc.Mload
    | Rinst.mstore => Desc.Mstore
    | Rinst.mstore8 => Desc.Mstore8
    | Rinst.sload => Desc.Sload e
    | Rinst.sstore => Desc.Sstore e
    | Rinst.tload => Desc.Tload
    | Rinst.tstore => Desc.Tstore e
    | Rinst.mcopy => Desc.Mcopy
    | Rinst.msize => λ s s' => ∃ x, Desc.Push [x] s s'
    | Rinst.gas => λ s s' => ∃ x, Desc.Push [x] s s'
    | Rinst.pc => λ s s' => ∃ x, Desc.Push [x] s s'
    | Rinst.dup n => Desc.Dup n.val
    | Rinst.swap n => Desc.Swap n.val
    | Rinst.log n =>
      match n with
      | ⟨0, _⟩ => λ s s' => ∃ x₀ x₁, Desc.Pop [x₀, x₁] s s'
      | ⟨1, _⟩ => λ s s' => ∃ x₀ x₁ x₂, Desc.Pop [x₀, x₁, x₂] s s'
      | ⟨2, _⟩ => λ s s' => ∃ x₀ x₁ x₂ x₃, Desc.Pop [x₀, x₁, x₂, x₃] s s'
      | ⟨3, _⟩ => λ s s' => ∃ x₀ x₁ x₂ x₃ x₄, Desc.Pop [x₀, x₁, x₂, x₃, x₄] s s'
      | ⟨4, _⟩ => λ s s' => ∃ x₀ x₁ x₂ x₃ x₄ x₅, Desc.Pop [x₀, x₁, x₂, x₃, x₄, x₅] s s'
      | ⟨5, h⟩ => False.elim <| Nat.lt_irrefl _ h
    -- | Rinst.invalid => λ _ _ => False

inductive Jinst.Run : Env → Desc → Nat → Jinst → Desc → Nat → Prop
  | jump :
    ∀ e s s' pc x,
      Desc.Pop [x] s s' →
      Jumpable e x.toNat →
      Jinst.Run e s pc jump s' x.toNat
  | zero :
    ∀ e s s' pc x,
      Desc.Pop [x, 0] s s' →
      Jinst.Run e s pc jumpi s' (pc + 1)
  | succ :
    ∀ e s s' pc x y,
      Desc.Pop [x, y] s s' →
      y ≠ 0 →
      Jumpable e x.toNat →
      Jinst.Run e s pc jumpi s' x.toNat
  | dest :
    ∀ e s pc, Jinst.Run e s pc jumpdest s (pc + 1)

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

inductive Step : Env → Desc → Nat → Desc → Nat → Type
  | reg :
    ∀ e s pc o s',
      Rinst.At e pc o →
      Rinst.Run e s o s' →
      Step e s pc s' (pc + 1)
  | pre :
    ∀ e s pc ep sp o r s' ,
      Xinst.At e pc o →
      o.isCall →
      Xinst.Run' e s ep sp o r s' →
      PreRun sp r →
      Step e s pc s' (pc + 1)
  | fail :
    ∀ e s pc o s',
      Xinst.At e pc o →
      Fail s o s' →
      Step e s pc s' (pc + 1)
  | jump :
    ∀ e s pc s' pc',
      Jinst.At e pc o →
      Jinst.Run e s pc o s' pc' →
      Step e s pc s' pc'
  | push :
    ∀ e s pc bs s',
      PushAt e pc bs →
      Desc.Push [B8L.toB256 bs] s s' →
      Step e s pc s' (pc + bs.length + 1)

inductive Halt : Env → Desc → Nat → Result → Prop
  | inst :
    ∀ e s pc o r,
      Linst.At e pc o →
      Linst.Run e s o r →
      Halt e s pc r
  | eoc : ∀ e s, Halt e s e.code.length (.wrap s [])

inductive Exec : Env → Desc → Nat → Result → Type
  | step :
    ∀ {e s pc s' pc' r},
      Step e s pc s' pc' →
      Exec e s' pc' r →
      Exec e s pc r
  | exec :
    ∀ {e s pc ep sp o r s' r'},
      Xinst.At e pc o →
      Xinst.Run' e s ep sp o r s' →
      Exec ep sp 0 r →
      Exec e s' (pc + 1) r' →
      Exec e s pc r'
  | halt :
    ∀ {e s pc r},
      Halt e s pc r →
      Exec e s pc r

-- The execution part of transaction, which happens after the deduction of
-- upfront gas payment, and before the distribution of gas refund/reward and
-- deletion of self-destructed contract codes.
inductive Transact
    (sda : Adr) -- tx sender address
                 -- (always an EOA & never has contract code, per EIP-3607)
    (rca : Adr) -- tx receiver address
                 -- · for contract calls, rca = address of called contract
                 -- · for contract creations, rca = address of newly created contract
    (w : World)  -- initial world state
    : Result → Prop
  | create :
    ∀ gpr clv ctc bal r code,
      Transfer w.bal sda clv rca bal →
      w.code rca = [] →
      Exec
        { cta := rca, oga := sda, gpr := gpr, cld := [], cla := sda,
          clv := clv, code := ctc, exd := 1024, wup := true }
        { bal := bal, stor := w.stor, code := w.code, stk := [],
          mem := Memory.init, ret := [], dest := [] }
        0 r →
      Overwrite rca r.ret r.code code →
      Transact sda rca w {r with code := code}
  | call :
    ∀ gpr cld clv bal r,
      Transfer w.bal sda clv rca bal →
      Exec
        { cta := rca, oga := sda, gpr := gpr, cld := cld, cla := sda,
          clv := clv, code := w.code rca, exd := 1024, wup := true }
        { bal := bal, stor := w.stor, code := w.code, stk := []
          mem := Memory.init, ret := [], dest := []}
        0 r →
      Transact sda rca w r
  | pre :
    ∀ clv bal ret,
      Transfer w.bal sda clv rca bal →
      Transact sda rca w
        {bal := bal, stor := w.stor, code := w.code, ret := ret, dest := []}
  | fail : Transact sda rca w {w with ret := .nil, dest := []}

def DeleteCodes : List Adr → Codes → Codes → Prop
  | [], c, c' => c = c'
  | a :: as, c, c'' => ∃ c' : Codes, Overwrite a [] c c' ∧ DeleteCodes as c' c''

  structure Transaction (w w' : World) : Type where
    (vs : B256) -- gas ultimately refunded to sender
    (vv : B256) -- gas ultimately rewarded to validator
    (vb : B256) -- gas ultimately burned
    (nof : vs.toNat + vv.toNat + vb.toNat < 2 ^ 256)
    (sda : Adr) -- tx sender address
    (eoa : w.code sda = []) -- per EIP-3607
    (bal : Balances) -- balances after upfront deduction
    (decr : Decrease sda (vs + vv + vb) w.bal bal)
    (le : vs + vv + vb ≤ w.bal sda)
    (rca : Adr) -- tx receiver address
    (r : Result) -- execution result
    (act : Transact sda rca {w with bal := bal} r)
    (bal' : Balances) -- balances after refund to sender
    (incr : Increase sda vs r.bal bal')
    (vla : Adr) -- validator address
    (incr' : Increase vla vv bal' w'.bal)
    (del : DeleteCodes r.dest r.code w'.code)
    (stor : w'.stor = r.stor)



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

def Ninst.toBytes : Ninst → B8L
  | reg o => [o.toB8]
  | exec o => [o.toB8]
  | push bs _ => pushToB8L bs

def Ninst.At (e : Env) (pc : Nat) : Ninst → Prop
  | reg o => o.At e pc
  | exec o => o.At e pc
  | push bs _ => PushAt e pc bs

inductive Xinst.Run : Env → Desc → Xinst → Desc → Prop
  | exec :
    ∀ {e s ep sp o r s'},
      Xinst.Run' e s ep sp o r s' →
      Exec ep sp 0 r →
      Xinst.Run e s o s'
  | pre :
    ∀ {e s ep sp o r s'},
      o.isCall →
      Xinst.Run' e s ep sp o r s' →
      PreRun sp r →
      Xinst.Run e s o s'
  | fail : ∀ {e s o s'}, Fail s o s' → Xinst.Run e s o s'

inductive Ninst.Run : Env → Desc → Ninst → Desc → Prop
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
      Desc.Push [B8L.toB256 bs] s s' →
      Ninst.Run e s (Ninst.push bs h) s'

inductive Func.Run : List Func → Env → Desc → Func → Result → Prop
  | zero :
    ∀ {fs e s s' f g r},
      Desc.Pop [0] s s' →
      Func.Run fs e s' f r →
      Func.Run fs e s (branch f g) r
  | succ :
    ∀ {fs e s w s' f g r},
      w ≠ 0 →
      Desc.Pop [w] s s' →
      Func.Run fs e s' g r →
      Func.Run fs e s (branch f g) r
  | last :
    ∀ {fs e s i r},
      Linst.Run e s i r →
      Func.Run fs e s (last i) r
  | next :
    ∀ {fs e s i s' f r},
      Ninst.Run e s i s' →
      Func.Run fs e s' f r →
      Func.Run fs e s (next i f) r
  | call :
    ∀ {fs e s k f r},
      fs[k]? = some f →
      Func.Run fs e s f r →
      Func.Run fs e s (call k) r

def Prog.Run (e : Env) (s : Desc) (p : Prog) (r : Result) : Prop :=
  Func.Run (p.main :: p.aux) e s p.main r
