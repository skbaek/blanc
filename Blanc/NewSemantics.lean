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
    List.sliceD e.cld x.toNat 32 0 = y.toB8L

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

inductive ExecOld : Env → Desc → Nat → Result → Type
  | step :
    ∀ {e s pc s' pc' r},
      Step e s pc s' pc' →
      ExecOld e s' pc' r →
      ExecOld e s pc r
  | exec :
    ∀ {e s pc ep sp o r s' r'},
      Xinst.At e pc o →
      Xinst.Run' e s ep sp o r s' →
      ExecOld ep sp 0 r →
      ExecOld e s' (pc + 1) r' →
      ExecOld e s pc r'
  | halt :
    ∀ {e s pc r},
      Halt e s pc r →
      ExecOld e s pc r

def Desc.init (bal : Adr → B256) (stor : Adr → Storage) (code : Adr → B8L) : Desc :=
  {
    bal := bal,
    stor := stor,
    code := code,
    stk := [],
    mem := Memory.init,
    ret := [],
    dest := []
  }

-- The execution part of transaction, which happens after the deduction of
-- upfront gas payment, and before the distribution of gas refund/reward and
-- deletion of self-destructed contract codes.
inductive MessageCall
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
      ExecOld
        { cta := rca, oga := sda, gpr := gpr, cld := [], cla := sda,
          clv := clv, code := ctc, exd := 1024, wup := true }
        --{ bal := bal, stor := w.stor, code := w.code, stk := [],
        --  mem := Memory.init, ret := [], dest := [] }
        (Desc.init bal w.stor w.code)
        0 r →
      Overwrite rca r.ret r.code code →
      MessageCall sda rca w {r with code := code}
  | call :
    ∀ gpr cld clv bal r,
      Transfer w.bal sda clv rca bal →
      ExecOld
        { cta := rca, oga := sda, gpr := gpr, cld := cld, cla := sda,
          clv := clv, code := w.code rca, exd := 1024, wup := true }
        -- { bal := bal, stor := w.stor, code := w.code, stk := []
        --   mem := Memory.init, ret := [], dest := []}
        (Desc.init bal w.stor w.code)
        0 r →
      MessageCall sda rca w r
  | pre :
    ∀ clv bal ret,
      Transfer w.bal sda clv rca bal →
      MessageCall sda rca w
        {bal := bal, stor := w.stor, code := w.code, ret := ret, dest := []}
  | fail : MessageCall sda rca w {w with ret := .nil, dest := []}

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
    (act : MessageCall sda rca {w with bal := bal} r)
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

def Ninst.toB8L : Ninst → B8L
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
      ExecOld ep sp 0 r →
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

----------------------------------------------------------------------------------------

def Except.isError {ξ υ : Type} (e : Except ξ υ) : Prop :=
  match e with
  | .error _ => True
  | .ok _ => False

def Evm.GetInst (evm : Evm) (i : Inst) : Prop :=
  evm.getInst = some i

def Xlot : Type := Option (Evm × Execution)

def Jinst.Run' (evm : Evm) : Jinst → Execution → Prop := λ j ex => j.run evm = ex
def Linst.Run' (evm : Evm) : Linst → Execution → Prop := λ l ex => l.run evm = ex

-- def Except.Split {ξ υ : Type}
--     (e : Except ξ υ) (p : ξ → Prop) (q : υ → Prop) : Prop :=
--   (∃ x : ξ, e = .error x ∧ p x) ∨ (∃ y : υ, e = .ok y ∧ q y)

def Except.Split {ξ υ ζ : Type}
    (e : Except ξ υ)  (e' : Except ξ ζ) (q : υ → Prop) : Prop :=
  (∃ x, e = .error x ∧ e' = .error x) ∨ (∃ y : υ, e = .ok y ∧ q y)


  -- def executeCode (vb : Bool) (msg : Msg) :
  --   Nat → Except (Benv × Tenv × String) Evm
  --   | 0 => .error ⟨msg.benv, msg.tenv, "RecursionLimit"⟩
  --   | lim + 1 => do
  --     let evm : Evm := initEvm msg
  --     match msg.codeAddress with
  --     | .none =>
  --       executeCode.handleError <| exec vb lim evm
  --     | .some adr =>
  --       if adr.isPrecomp then
  --         executeCode.handleError <| executePrecomp evm adr
  --       else
  --         executeCode.handleError <| exec vb lim evm
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
    And (createMsgGas = except64th evm1.gas_left) <|
  ∃ evm2 : Evm,
    And (evm2 = {evm1 with gas_left := evm1.gas_left - createMsgGas}) <|
    evm2.assertDynamic.Split ex <|
  λ _ =>
  ∃ evm3 : Evm,
    And (evm3 = {evm2 with return_data := []}) <|
  ∃ sender : Acct,
    And (sender = evm3.msg.benv.state.get evm3.contract) <|
  if (sender.bal < endowment ∨ sender.nonce = B64.max ∨ evm3.msg.depth + 1 > 1024) then
    ({evm3 with gas_left := evm3.gas_left + createMsgGas}.push 0 = ex)
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
    And (evm1 = {evm with return_data := []}) <|
    Or ( evm1.msg.depth + 1 > 1024 ∧
         {evm1 with gas_left := evm1.gas_left + gas}.push 0 = ex ) <|
    And (¬ evm1.msg.depth + 1 > 1024) <|
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
  λ child =>
    ( if child.error.isSome then
        (incorporateChildOnError evm1 child child.output).push 0
      else
        (incorporateChildOnSuccess evm1 child child.output).push 1 ).Split ex <|
  λ evm2 =>
    let actualOutput := child.output.take output_size
    .ok (evm2.memWrite output_index actualOutput) = ex

-- def Xlot.Good (lim : Nat) (ex : Execution) : Xlot → Prop
--   | .none => True
--   | .some (evm', ex') =>
--     ∃ lim' < lim,
--       exec false lim' evm' = ex' ∧
--       (ex'.isError → ex' = ex)

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
      exec false lim' evm = ex ∧
      (ex.toError? = some "RecursionLimit" → oe = some "RecursionLimit")

-- def Execution.Good (ex : Except (Benv × Tenv × String) Evm) : Execution → Prop
--   | .ok _ => True
--   | .error ⟨evm, err⟩ =>
--     (isExceptionalHalt err) ∨
--     (err = "Revert") ∨
--     (.error ⟨evm.msg.benv, evm.msg.tenv, err⟩) = ex
--
-- def Xlot.Good (lim : Nat) (ex : Except (Benv × Tenv × String) Evm) : Xlot → Prop
--   | .none => True
--   | .some (evm', ex') =>
--     ∃ lim' < lim,
--       exec false lim' evm' = ex' ∧
--       ex'.Good ex
--       --match ex' with
--       --| .ok _ => True
--       --| .error ⟨evm, err⟩ =>
--       --  (isExceptionalHalt err) ∨
--       --  (err = "Revert") ∨
--       --  (.error ⟨evm.msg.benv, evm.msg.tenv, err⟩) = ex

--def liftToExecution (evm : Evm)
--  (f : Except (Benv × Tenv × String) Evm) : Execution := do
--  match f with
--  | .error ⟨benv, tenv, ex⟩ =>
--    let evm' := {
--      evm with
--      msg := {
--        evm.msg with
--        benv := benv
--        tenv := tenv
--      }
--    }
--    .error ⟨evm', ex⟩
--  | .ok evm => .ok evm

-- lemma of_liftToExecution_eq_error (evm : Evm)
--     (ex : Except (Benv × Tenv × String) Evm) (err)
--     (h : liftToExecution evm ex = .error err) : False := by
--
--
-- #exit
--      --: Execution := do

lemma Except.of_toError?_eq_some {ξ} (ex : Except (String × ξ) Evm)
    (err : String) (eq : ex.toError? = some err) :
    ∃ x, ex = .error ⟨err, x⟩ := by
  rcases ex with ⟨err', _⟩ | _ <;> simp [Except.toError?] at eq
  cases eq; refine ⟨_, rfl⟩

def Except.Limited {ξ υ} (ex : Except (String × ξ) υ) : Prop :=
  ex.toError? = some "RecursionLimit"

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

lemma Except.of_limited_bind {ξ υ ζ : Type}
    {x : Except (String × ξ) υ} {f : υ → Except (String × ξ) ζ}
    (h : (x >>= f).Limited) : x.Limited ∨ (∃ y, x = .ok y ∧ (f y).Limited) := by
  rcases x with ⟨err, s⟩ | y
  · left; simp [bind, Except.bind] at h; exact h
  · right; use y; constructor; rfl
    simp [bind, Except.bind] at h; exact h

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
      ⟨ .some ⟨initEvm msg, exec false lim (initEvm msg)⟩,
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
        ⟨ .some ⟨initEvm msg, exec false lim (initEvm msg)⟩,
          ⟨lim, (by omega), rfl, λ halts => _⟩, _ ⟩
      · rcases Except.of_toError?_eq_some _ _ halts with ⟨evm, rw⟩
        rw [← eq, rw] at notLimited; cases notLimited rfl
      · simp only [ExecuteCode]; rw [eq_some]
        simp only []; rw [if_neg neg]; refine' ⟨_, rfl, eq⟩

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
  okStep1 eq _
  split at eq
  {rename_i gt; simp at eq; refine' ⟨.none, .intro, .inl ⟨gt, eq⟩⟩}
  rename_i not_gt
  apply Exists.imp (λ _ (h' : _ ∧ _) => ⟨h'.1, .inr ⟨not_gt, h'.2⟩⟩);
  rcases of_bind_eq eq with ⟨_, ⟨_⟩, _⟩ | ⟨_, temp_eq, eq'⟩;
  clear temp_eq eq; rename' eq' => eq;
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

lemma ite_of_true {c : Prop} [Decidable c] {p q : Prop} :
    c → p → if c then p else q := by
  intro hc hp; rw [if_pos hc]; exact hp

lemma ite_of_false {c : Prop} [Decidable c] {p q : Prop} :
    ¬ c → q → if c then p else q := by
  intro hc hp; rw [if_neg hc]; exact hp

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
      (chargeGas (if xs = [] then gBase else gVerylow) evm).Split ex <|
    λ evm1 =>
      (evm1.push xs.toB256).Split ex <|
    λ evm2 =>
     .ok {evm2 with pc := evm2.pc + xs.length + 1} = ex
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
      (evm1.pop <&> Prod.mapFst B256.toAdr).Split ex <|
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
    ∃ disablePrecompiles fooo code delegatedAccessGasCost evm9,
      And
        (⟨disablePrecompiles, fooo, code, delegatedAccessGasCost, evm9⟩ = accessDelegation evm8 callee) <|
    ∃ accessCost,
      And (accessCost = preAccessCost + delegatedAccessGasCost) <|
    ∃ createCost,
      And (createCost = if (¬ (evm9.getAcct callee).Empty) ∨ value = 0 then 0 else gNewAccount) <|
    ∃ transferCost,
      And (transferCost = if value = 0 then 0 else gasCallValue) <|
    ∃ msgCallCost msgCallStipend,
      And (⟨msgCallCost, msgCallStipend⟩ = calculate_msg_call_gas value.toNat gas.toNat evm9.gas_left extendCost (accessCost + createCost + transferCost)) <|
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
          return_data := []
          gas_left := evm12.gas_left + msgCallStipend }.incrPc = ex
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
      (evm1.pop <&> Prod.mapFst B256.toAdr).Split ex <|
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
      And (⟨msgCallCost, msgCallStipend⟩ = calculate_msg_call_gas value.toNat gas.toNat evm9.gas_left extendCost (accessCost + transferCost)) <|
      (chargeGas (msgCallCost + extendCost) evm9).Split ex <|
    λ evm10 =>
    ∃ evm11,
      And (evm11 = evm10.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]) <|
    ∃ senderBal,
      And (senderBal = (evm11.getAcct evm11.contract).bal) <|
    if senderBal < value then
        (evm11.push 0).Split ex <|
      λ evm12 =>
        {evm12 with return_data := [], gas_left := evm12.gas_left + msgCallStipend}.incrPc = ex
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
      (evm1.pop <&> Prod.mapFst B256.toAdr).Split ex <|
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
      And (⟨msgCallCost, msgCallStipend⟩ = calculate_msg_call_gas 0 gas.toNat evm8.gas_left extendCost accessCost) <|
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
      (evm1.pop <&> Prod.mapFst B256.toAdr).Split ex <|
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
    ∃ disablePrecompiles fooo code delegatedAccessGasCost evm8,
      And (⟨disablePrecompiles, fooo, code, delegatedAccessGasCost, evm8⟩ = accessDelegation evm7 target) <|
    ∃ accessCost,
      And (accessCost = preAccessCost + delegatedAccessGasCost) <|
    ∃ msgCallCost msgCallStipend,
      And (⟨msgCallCost, msgCallStipend⟩ = calculate_msg_call_gas 0 gas.toNat evm8.gas_left extendCost accessCost) <|
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
    simp [Ninst.run] at eq
    rcases of_bind_eq eq with im | ⟨evm1, chargeGas_eq, eq'⟩; {left; apply im}
    clear eq; rename' eq' => eq;
    right; refine' ⟨_, chargeGas_eq, _⟩; clear chargeGas_eq
    rcases of_bind_eq eq with im | ⟨evm2, push_eq, eq'⟩; {left; apply im}
    clear eq; rename' eq' => eq;
    right; refine' ⟨_, push_eq, _⟩; clear push_eq
    apply eq
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
inductive Exec : Evm → Execution → Prop
  | invOp {evm : Evm} :
    evm.getInst = none →
    Exec evm (.error ⟨"InvalidOpcode", evm⟩)
  | nextNoneErr {evm : Evm} {n : Ninst} {ex : Execution} :
    evm.GetInst (.next n) →
    Ninst.Run' evm n .none ex →
    ex.isError → Exec evm ex
  | nextSomeErr {evm : Evm} {n : Ninst}
    {evm' : Evm} {ex' : Execution } {ex : Execution} :
    evm.GetInst (.next n) →
    Ninst.Run' evm n (.some (evm', ex')) ex →
    Exec evm' ex' → ex.isError → Exec evm ex
  | nextNoneRec {evm : Evm} {n : Ninst} {evm' : Evm} {ex : Execution} :
    evm.GetInst (.next n) →
    Ninst.Run' evm n .none (.ok evm') →
    Exec evm' ex → Exec evm ex
  | nextSomeRec {evm : Evm} {n : Ninst} {evm' : Evm}
    {ex' : Execution} {evm'' : Evm} {ex : Execution} :
    evm.GetInst (.next n) →
    Ninst.Run' evm n (.some (evm', ex')) (.ok evm'') →
    Exec evm' ex' → Exec evm'' ex → Exec evm ex
  | jumpErr {evm : Evm} {j : Jinst} {ex : Execution} :
    evm.GetInst (.jump j) →
    Jinst.Run' evm j ex →
    ex.isError → Exec evm ex
  | jumpRec {evm : Evm} {j : Jinst} {evm' : Evm} {ex : Execution} :
    evm.GetInst (.jump j) →
    Jinst.Run' evm j (.ok evm') →
    Exec evm' ex → Exec evm ex
  | last {evm : Evm} {l : Linst} {ex : Execution} :
    evm.GetInst (.last l) → Linst.Run' evm l ex → Exec evm ex

def ok_bind {ξ : Type u} {υ ζ : Type v} {y : υ} {g : υ → Except ξ ζ} :
    (.ok y) >>= g = g y := rfl

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

def exec_of_exec :
    ∀ (lim : Nat) (evm : Evm) (ex : Execution),
      ¬ ex.Limited → (exec false lim evm = ex) → Exec evm ex := by
  apply Nat.strongRec; intro lim ih evm ex notLimited exec_eq;
  cases lim with
  | zero =>
    rw [← exec_eq] at notLimited
    simp [exec, Except.toError?, Except.Limited] at notLimited
  | succ lim =>
    simp [exec] at exec_eq
    rcases Option.eq_none_or_eq_some evm.getInst with
      getInst_eq | ⟨i, getInst_eq⟩
      <;> rw [getInst_eq] at exec_eq
      <;> simp [Option.toExcept] at exec_eq
    · rw [← exec_eq]; apply Exec.invOp getInst_eq
    · rw [ok_bind] at exec_eq
      rcases i with l | n | j <;> simp only [] at exec_eq
      · apply Exec.last getInst_eq exec_eq
      · rcases of_bind_eq exec_eq with
          ⟨es, run_eq, ex_eq⟩ | ⟨evm', run_eq, ex_eq⟩
        · rw [ex_eq] at notLimited
          rcases Ninst.run_of_run notLimited run_eq
            with ⟨_ | ⟨evm', ex'⟩, good, run⟩
          · rw [ex_eq]; exact Exec.nextNoneErr getInst_eq run .intro
          · rw [ex_eq];
            apply Exec.nextSomeErr getInst_eq run _ .intro
            rcases good with ⟨lim', lt, exec_eq', notLimited_of⟩
            have notLimited' : ¬ ex'.Limited := by
              intro h; cases notLimited <| notLimited_of h
            apply @ih _ (by omega) _ _ notLimited' exec_eq'
        · rcases Ninst.run_of_run (by {intro h; cases h}) run_eq
            with ⟨_ | ⟨evm', ex'⟩, good, run⟩
          · apply @Exec.nextNoneRec _ _ _ _ getInst_eq run ;
            apply ih _ (by omega) _ _ notLimited ex_eq;
          · rcases good with ⟨lim', lt, exec_eq', notLimited_of⟩
            have notLimited' : ¬ ex'.Limited := by intro h; cases notLimited_of h
            have ih'  := @ih _ (by omega) _ _ notLimited' exec_eq'
            apply @Exec.nextSomeRec _ _ _ _ _ _ getInst_eq run ih'
            apply @ih _ (by omega) _ _ notLimited ex_eq
      · rcases of_bind_eq exec_eq
          with ⟨es, run_eq, ex_eq⟩ | ⟨evm', run_eq, ex_eq⟩
        · rw [ex_eq]; exact Exec.jumpErr getInst_eq run_eq .intro
        · apply Exec.jumpRec getInst_eq run_eq
          apply ih _ (Nat.lt_succ_self _) _ _ notLimited ex_eq
--inductive Linst : Type
--  | stop -- 0x00 / 0 / 0 / halts execution.
--  | ret -- 0xf3 / 2 / 0 / Halt execution and return output data.
--  | rev -- 0xfd / 2 / 0 / Halt execution and revert State changes, returning output data.
--  | dest -- 0xff / 1 / 0 / Halt execution and destroy the current contract, transferring remaining Ether to a specified Addr.
--  -- | invalid -- 0xFE / 0 / 0 / Designated invalid instruction.

lemma Evm.not_limited_push {evm : Evm} {x : B256} : ¬ (evm.push x).Limited := by
  unfold Except.Limited Evm.push Except.assert
  split
  · simp [Except.toError?, bind, Except.bind]
  · simp [Except.toError?, bind, Except.bind]

lemma Evm.not_limited_pop {evm : Evm} : ¬ evm.pop.Limited := by
  simp only [Except.Limited, Evm.pop, Except.toError?]
  cases evm.stack <;> simp

lemma Evm.not_limited_popToNat {evm : Evm} : ¬ evm.popToNat.Limited := by
  simp only [Except.Limited, Evm.popToNat, Except.toError?, Evm.pop]
  cases evm.stack <;> simp

lemma not_limited_chargeGas {cost : Nat} {evm : Evm} :
    ¬ (chargeGas cost evm).Limited := by
  simp only [Except.Limited, Except.toError?, chargeGas]
  cases safeSub evm.gas_left cost <;> simp

lemma Evm.not_limited_assertDynamic {evm : Evm} :
    ¬ evm.assertDynamic.Limited := by
  intro h
  unfold Except.Limited Evm.assertDynamic Except.assert Except.toError? at h
  split at h <;> rename_i h_eq
  · simp at h
  · split at h_eq
    · contradiction
    · injection h_eq with h_inner
      injection h_inner with h_err _
      rw [← h_err] at h
      simp [toString] at h

lemma Option.not_limited_toExcept {ξ υ} (x : ξ) (o : Option υ)
    {s : String} (ne : s ≠ "RecursionLimit") :
    ¬ (@Option.toExcept (String × ξ) υ ⟨s, x⟩ o).Limited := by
  simp only [Except.Limited, Except.toError?, Option.toExcept]
  cases o <;> simp [ne]

syntax "not_limited_bind_step " ident term : tactic
macro_rules
  | `(tactic| not_limited_bind_step $ltd $lem) => `(tactic|
      rcases Except.of_limited_bind $ltd with ltd' | ⟨_, temp, ltd'⟩;
      {cases $lem ltd'}; clear $ltd temp; rename' ltd' => $ltd
    )

lemma Linst.not_limited_of_run (evm : Evm) (l : Linst) (ex : Execution)
    (run : Linst.Run' evm l ex) : ¬ ex.Limited := by
  intro ltd;
  simp only [Linst.Run'] at run
  rw [← run] at ltd; cases l
  case stop => cases ltd
  case rev =>
    not_limited_bind_step ltd Evm.not_limited_popToNat
    not_limited_bind_step ltd Evm.not_limited_popToNat
    not_limited_bind_step ltd not_limited_chargeGas
    simp [Except.Limited, Except.toError?] at ltd
  case ret =>
    not_limited_bind_step ltd Evm.not_limited_popToNat
    not_limited_bind_step ltd Evm.not_limited_popToNat
    not_limited_bind_step ltd not_limited_chargeGas
    simp [Except.Limited, Except.toError?] at ltd
  case dest =>
    simp only [bind_map_left, Linst.run] at ltd
    not_limited_bind_step ltd Evm.not_limited_pop
    not_limited_bind_step ltd not_limited_chargeGas
    not_limited_bind_step ltd Evm.not_limited_assertDynamic
    have ne : "ERROR : InsufficientBalanceError" ≠ "RecursionLimit" := by decide
    not_limited_bind_step ltd (Option.not_limited_toExcept _ _ ne)
    split at ltd <;> simp [Except.Limited, Except.toError?] at ltd

lemma not_limited_pushItem {x : B256} {c : Nat} {evm : Evm} :
    ¬ (pushItem x c evm).Limited := by
  simp only [pushItem]; intro run
  rcases Except.of_limited_bind run with run' | ⟨_, _, run'⟩
  · clear run
    rcases Except.of_limited_bind run' with run | ⟨_, _, run⟩
    · cases not_limited_chargeGas run
    · cases Evm.not_limited_push run
  · simp [Evm.incrPc, Except.toError?, Except.Limited] at run'

lemma not_limited_applyUnary {f : B256 → B256} {cost : Nat} {evm : Evm} :
    ¬ (applyUnary f cost evm).Limited := by
  simp only [applyUnary]; intro run
  rcases Except.of_limited_bind run with run' | ⟨_, _, run'⟩
  · cases Evm.not_limited_pop run'
  · cases not_limited_pushItem run'

lemma not_limited_applyBinary {f : B256 → B256 → B256} {cost : Nat} {evm : Evm} :
    ¬ (applyBinary f cost evm).Limited := by
  simp only [applyBinary]; intro ltd
  not_limited_bind_step ltd Evm.not_limited_pop
  not_limited_bind_step ltd Evm.not_limited_pop
  cases not_limited_pushItem ltd

lemma not_limited_applyTernary {f : B256 → B256 → B256 → B256} {cost : Nat} {evm : Evm} :
    ¬ (applyTernary f cost evm).Limited := by
  simp only [applyTernary]; intro ltd
  not_limited_bind_step ltd Evm.not_limited_pop
  not_limited_bind_step ltd Evm.not_limited_pop
  not_limited_bind_step ltd Evm.not_limited_pop
  cases not_limited_pushItem ltd

lemma Rinst.not_limited_run (evm : Evm) (r : Rinst) :
    ¬ (Rinst.run evm r).Limited := by
  intro ltd; cases r
  case add => sorry -- 0x01 / 2 / 1 / addition operation.
  case mul => sorry -- 0x02 / 2 / 1 / multiplication operation.
  case sub => sorry -- 0x03 / 2 / 1 / subtraction operation.
  case div => sorry -- 0x04 / 2 / 1 / integer division operation.
  case sdiv => sorry -- 0x05 / 2 / 1 / signed integer division operation.
  case mod => sorry -- 0x06 / 2 / 1 / modulo operation.
  case smod => sorry -- 0x07 / 2 / 1 / signed modulo operation.
  case addmod => sorry -- 0x08 / 3 / 1 / modulo addition operation.
  case mulmod => sorry -- 0x09 / 3 / 1 / modulo multiplication operation.
  case exp => sorry -- 0x0A / 2 / 1 / exponentiation operation.
  case signextend => sorry -- 0x0B / 2 / 1 / sign extend operation.
  case lt => sorry -- 0x10 / 2 / 1 / less-than comparison.
  case gt => sorry -- 0x11 / 2 / 1 / greater-than comparison.
  case slt => sorry -- 0x12 / 2 / 1 / signed less-than comparison.
  case sgt => sorry -- 0x13 / 2 / 1 / signed greater-than comparison.
  case eq => sorry -- 0x14 / 2 / 1 / equality comparison.
  case iszero => sorry -- 0x15 / 1 / 1 / tests if the input is zero.
  case and => sorry -- 0x16 / 2 / 1 / bitwise and operation.
  case or => sorry -- 0x17 / 2 / 1 / bitwise or operation.
  case xor => sorry -- 0x18 / 2 / 1 / bitwise xor operation.
  case not => sorry -- 0x19 / 1 / 1 / bitwise not operation.
  case byte => sorry -- 0x1A / 2 / 1 / retrieve a single Byte from a Word.
  case shr => sorry -- 0x1B / 2 / 1 / logical shift right operation.
  case shl => sorry -- 0x1C / 2 / 1 / logical shift left operation.
  case sar => sorry -- 0x1D / 2 / 1 / arithmetic (signed) shift right operation.
  case kec => sorry -- 0x20 / 2 / 1 / compute Keccak-256 hash.
  case address => sorry -- 0x30 / 0 / 1 / Get the Addr of the currently executing account.
  case balance => sorry -- 0x31 / 1 / 1 / Get the balance of the specified account.
  case origin => sorry -- 0x32 / 0 / 1 / Get the Addr that initiated the current transaction.
  case caller => sorry -- 0x33 / 0 / 1 / Get the Addr that directly called the currently executing contract.
  case callvalue => sorry -- 0x34 / 0 / 1 / Get the value (in wei) sent with the current transaction.
  case calldataload => sorry -- 0x35 / 1 / 1 / Load input data from the current transaction.
  case calldatasize => sorry -- 0x36 / 0 / 1 / Get the size of the input data from the current transaction.
  case calldatacopy => sorry -- 0x37 / 3 / 0 / Copy input data from the current transaction to Memory.
  case codesize => sorry -- 0x38 / 0 / 1 / Get the size of the code of the currently executing contract.
  case codecopy => sorry -- 0x39 / 3 / 0 / Copy the code of the currently executing contract to memory.
  case gasprice => sorry -- 0x3a / 0 / 1 / Get the gas price of the current transaction.
  case extcodesize => sorry -- 0x3B / 1 / 1 / Get the size of the code of an external account.
  case extcodecopy => sorry -- 0x3C / 4 / 0 / Copy the code of an external account to memory.
  case retdatasize => sorry -- 0x3D / 0 / 1 / Get the size of the output data from the previous call.
  case retdatacopy => sorry -- 0x3E / 3 / 0 / Copy output data from the previous call to memory.
  case extcodehash => sorry -- 0x3F / 1 / 1 / Get the code hash of an external account.
  case blockhash => sorry -- 0x40 / 1 / 1 / get the hash of the specified block.
  case coinbase => sorry -- 0x41 / 0 / 1 / get the Addr of the current block's miner.
  case timestamp => sorry -- 0x42 / 0 / 1 / get the timestamp of the current block.
  case number => sorry -- 0x43 / 0 / 1 / get the current block number.
  case prevrandao => sorry -- 0x44 / 0 / 1 / get the latest RANDAO mix of the post beacon state of the previous block.
  case gaslimit => sorry -- 0x45 / 0 / 1 / get the gas limit of the current block.
  case chainid => sorry -- 0x46 / 0 / 1 / get the chain id of the current blockchain.
  case selfbalance => sorry -- 0x47 / 0 / 1 / get the balance of the currently executing account.
  case basefee => sorry -- 0x48 / 0 / 1 / get the current block's base fee.
  case blobhash => sorry -- 0x49 / 1 / 1 /
  case blobbasefee => sorry -- 0x4A / 0 / 1 / get the current block's blob base fee.
  case pop => sorry -- 0x50 / 1 / 0 / Remove an item from the Stack.
  case mload => sorry -- 0x51 / 1 / 1 / Load a Word from memory.
  case mstore => sorry -- 0x52 / 2 / 0 / Store a Word in memory.
  case mstore8 => sorry -- 0x53 / 2 / 0 / store a Byte in memory.
  case sload => sorry -- 0x54 / 1 / 1 / load a word from storage.
  case sstore => sorry -- 0x55 / 2 / 0 / store a word in storage.
  case tload => sorry -- 0x5C / 1 / 1 / load a word from transient torage.
  case tstore => sorry -- 0x5D / 2 / 0 / store a word in transient storage.
  case mcopy => sorry -- 0x5E / 3 / 0 /
  case pc => sorry -- 0x58 / 0 / 1 / Get the current program counter value.
  case msize => sorry -- 0x59 / 0 / 1 / Get the size of the memory.
  case gas => sorry -- 0x5a / 0 / 1 / Get the amount of remaining gas.
  case dup => sorry
  case swap => sorry
  case log => sorry




#exit
lemma Rinst.not_limited_run (evm : Evm) (r : Rinst) : ¬ (Rinst.run evm r).Limited := by
  cases r <;> simp only [Rinst.run]
  case address => exact not_limited_pushItem
  case basefee => exact not_limited_pushItem
  case blobhash =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.pop) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.toError?, Evm.pop] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]; exact not_limited_pushItem
  case blobbasefee => exact not_limited_pushItem
  case balance =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.pop) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.toError?, Evm.pop] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]
      rcases of_bind_eq (f := if x.toAdr ∈ evm1.accessedAddresses then chargeGas gasWarmAccess evm1 else chargeGas gasColdAccountAccess (addAccessedAddress evm1 x.toAdr)) with im' | ⟨evm2, charge_eq, eq''⟩
      · split at im' <;> { simp [Except.toError?, chargeGas] at im'; cases safeSub _ _ <;> simp at im' }
      · simp only [bind, Except.bind, charge_eq, Evm.push]
        rcases of_bind_eq (f := Evm.push (evm2.getBal x.toAdr) evm2) with im'' | ⟨evm3, push_eq, eq'''⟩
        · simp [Except.toError?, Evm.push] at im''; split at im'' <;> simp at im''
        · simp only [bind, Except.bind, push_eq, Evm.incrPc]
  case origin => exact not_limited_pushItem
  case caller => exact not_limited_pushItem
  case callvalue => exact not_limited_pushItem
  case calldataload =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.pop) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.toError?, Evm.pop] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]
      rcases of_bind_eq (f := chargeGas gVerylow evm1) with im' | ⟨evm2, charge_eq, eq''⟩
      · simp [Except.toError?, chargeGas] at im'; cases safeSub _ _ <;> simp at im'
      · simp only [bind, Except.bind, charge_eq, Evm.push]
        rcases of_bind_eq (f := Evm.push (B8L.toB256 (evm2.msg.data.sliceD x.toNat 32 0)) evm2) with im'' | ⟨evm3, push_eq, eq'''⟩
        · simp [Except.toError?, Evm.push] at im''; split at im'' <;> simp at im''
        · simp only [bind, Except.bind, push_eq, Evm.incrPc]
  case calldatasize => exact not_limited_pushItem
  case calldatacopy =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.popToNat) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]
      rcases of_bind_eq (f := evm1.popToNat) with im' | ⟨⟨y, evm2⟩, pop_eq', eq''⟩
      · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im'; cases evm1.stack <;> simp at im'
      · simp only [bind, Except.bind, pop_eq']
        rcases of_bind_eq (f := evm2.popToNat) with im'' | ⟨⟨z, evm3⟩, pop_eq'', eq'''⟩
        · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im''; cases evm2.stack <;> simp at im''
        · simp only [bind, Except.bind, pop_eq'']
          rcases of_bind_eq (f := chargeGas (gVerylow + gasCopy * (ceilDiv z 32) + evm3.extCost [(x, z)]) evm3) with im''' | ⟨evm4, charge_eq, eq''''⟩
          · simp [Except.toError?, chargeGas] at im'''; cases safeSub _ _ <;> simp at im'''
          · simp only [bind, Except.bind, charge_eq, Evm.memWrite, Evm.incrPc]
  case codesize => exact not_limited_pushItem
  case codecopy =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.popToNat) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]
      rcases of_bind_eq (f := evm1.popToNat) with im' | ⟨⟨y, evm2⟩, pop_eq', eq''⟩
      · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im'; cases evm1.stack <;> simp at im'
      · simp only [bind, Except.bind, pop_eq']
        rcases of_bind_eq (f := evm2.popToNat) with im'' | ⟨⟨z, evm3⟩, pop_eq'', eq'''⟩
        · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im''; cases evm2.stack <;> simp at im''
        · simp only [bind, Except.bind, pop_eq'']
          rcases of_bind_eq (f := chargeGas (gVerylow + gasCopy * (ceilDiv z 32) + evm3.extCost [(x, z)]) evm3) with im''' | ⟨evm4, charge_eq, eq''''⟩
          · simp [Except.toError?, chargeGas] at im'''; cases safeSub _ _ <;> simp at im'''
          · simp only [bind, Except.bind, charge_eq]
  case gasprice => exact not_limited_pushItem
  case extcodesize =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.pop) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.toError?, Evm.pop] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]
      rcases of_bind_eq (f := if x.toAdr ∈ evm1.accessedAddresses then chargeGas gasWarmAccess evm1 else chargeGas gasColdAccountAccess (addAccessedAddress evm1 x.toAdr)) with im' | ⟨evm2, charge_eq, eq''⟩
      · split at im' <;> { simp [Except.toError?, chargeGas] at im'; cases safeSub _ _ <;> simp at im' }
      · simp only [bind, Except.bind, charge_eq, Evm.push]
        rcases of_bind_eq (f := Evm.push (evm2.getCode x.toAdr).size.toB256 evm2) with im'' | ⟨evm3, push_eq, eq'''⟩
        · simp [Except.toError?, Evm.push] at im''; split at im'' <;> simp at im''
        · simp only [bind, Except.bind, push_eq, Evm.incrPc]
  case extcodecopy =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.pop) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.toError?, Evm.pop] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]
      rcases of_bind_eq (f := evm1.popToNat) with im' | ⟨⟨y, evm2⟩, pop_eq', eq''⟩
      · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im'; cases evm1.stack <;> simp at im'
      · simp only [bind, Except.bind, pop_eq']
        rcases of_bind_eq (f := evm2.popToNat) with im'' | ⟨⟨z, evm3⟩, pop_eq'', eq'''⟩
        · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im''; cases evm2.stack <;> simp at im''
        · simp only [bind, Except.bind, pop_eq'']
          rcases of_bind_eq (f := evm3.popToNat) with im''' | ⟨⟨w, evm4⟩, pop_eq''', eq''''⟩
          · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im'''; cases evm3.stack <;> simp at im'''
          · simp only [bind, Except.bind, pop_eq''']
            rcases of_bind_eq (f := if x.toAdr ∈ evm4.accessedAddresses then chargeGas (gasWarmAccess + gasCopy * (ceilDiv w 32) + evm4.extCost [(y, w)]) evm4 else chargeGas (gasColdAccountAccess + gasCopy * (ceilDiv w 32) + evm4.extCost [(y, w)]) (addAccessedAddress evm4 x.toAdr)) with im'''' | ⟨evm5, charge_eq, eq'''''⟩
            · split at im'''' <;> { simp [Except.toError?, chargeGas] at im''''; cases safeSub _ _ <;> simp at im'''' }
            · simp only [bind, Except.bind, charge_eq]
  case retdatasize => exact not_limited_pushItem
  case retdatacopy =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.popToNat) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]
      rcases of_bind_eq (f := evm1.popToNat) with im' | ⟨⟨y, evm2⟩, pop_eq', eq''⟩
      · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im'; cases evm1.stack <;> simp at im'
      · simp only [bind, Except.bind, pop_eq']
        rcases of_bind_eq (f := evm2.popToNat) with im'' | ⟨⟨z, evm3⟩, pop_eq'', eq'''⟩
        · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im''; cases evm2.stack <;> simp at im''
        · simp only [bind, Except.bind, pop_eq'']
          rcases of_bind_eq (f := chargeGas (gVerylow + gReturnDataCopy * (ceilDiv z 32) + evm3.extCost [(x, z)]) evm3) with im''' | ⟨evm4, charge_eq, eq''''⟩
          · simp [Except.toError?, chargeGas] at im'''; cases safeSub _ _ <;> simp at im'''
          · simp only [bind, Except.bind, charge_eq]
            split at eq'''' <;> simp [eq'''']
  case extcodehash =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.pop) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.toError?, Evm.pop] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]
      rcases of_bind_eq (f := if x.toAdr ∈ evm1.accessedAddresses then chargeGas gasWarmAccess evm1 else chargeGas gasColdAccountAccess (addAccessedAddress evm1 x.toAdr)) with im' | ⟨evm2, charge_eq, eq''⟩
      · split at im' <;> { simp [Except.toError?, chargeGas] at im'; cases safeSub _ _ <;> simp at im' }
      · simp only [bind, Except.bind, charge_eq, Evm.push]
        rcases of_bind_eq (f := Evm.push (if (evm2.getAcct x.toAdr).Empty then 0 else ByteArray.keccak 0 (evm2.getAcct x.toAdr).code.size (evm2.getAcct x.toAdr).code) evm2) with im'' | ⟨evm3, push_eq, eq'''⟩
        · simp [Except.toError?, Evm.push] at im''; split at im'' <;> simp at im''
        · simp only [bind, Except.bind, push_eq, Evm.incrPc]
  case selfbalance => exact not_limited_pushItem
  case chainid => exact not_limited_pushItem
  case number => exact not_limited_pushItem
  case timestamp => exact not_limited_pushItem
  case gaslimit => exact not_limited_pushItem
  case prevrandao => exact not_limited_pushItem
  case coinbase => exact not_limited_pushItem
  case msize => exact not_limited_pushItem
  case mload =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.popToNat) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]
      rcases of_bind_eq (f := chargeGas (gVerylow + evm1.extCost [(x, 32)]) evm1) with im' | ⟨evm2, charge_eq, eq''⟩
      · simp [Except.toError?, chargeGas] at im'; cases safeSub _ _ <;> simp at im'
      · simp only [bind, Except.bind, charge_eq, Evm.push]
        rcases of_bind_eq (f := Evm.push (B8L.toB256 (evm2.memRead x 32).1) (evm2.memRead x 32).2) with im'' | ⟨evm3, push_eq, eq'''⟩
        · simp [Except.toError?, Evm.push] at im''; split at im'' <;> simp at im''
        · simp only [bind, Except.bind, push_eq, Evm.incrPc]
  case mstore =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.popToNat) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]
      rcases of_bind_eq (f := evm1.pop) with im' | ⟨⟨y, evm2⟩, pop_eq', eq''⟩
      · simp [Except.toError?, Evm.pop] at im'; cases evm1.stack <;> simp at im'
      · simp only [bind, Except.bind, pop_eq']
        rcases of_bind_eq (f := chargeGas (gVerylow + evm2.extCost [(x, 32)]) evm2) with im'' | ⟨evm3, charge_eq, eq'''⟩
        · simp [Except.toError?, chargeGas] at im''; cases safeSub _ _ <;> simp at im''
        · simp only [bind, Except.bind, charge_eq, Evm.memWrite, Evm.incrPc]
  case mstore8 =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.popToNat) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]
      rcases of_bind_eq (f := evm1.pop) with im' | ⟨⟨y, evm2⟩, pop_eq', eq''⟩
      · simp [Except.toError?, Evm.pop] at im'; cases evm1.stack <;> simp at im'
      · simp only [bind, Except.bind, pop_eq']
        rcases of_bind_eq (f := chargeGas (gVerylow + evm2.extCost [(x, 1)]) evm2) with im'' | ⟨evm3, charge_eq, eq'''⟩
        · simp [Except.toError?, chargeGas] at im''; cases safeSub _ _ <;> simp at im''
        · simp only [bind, Except.bind, charge_eq, Evm.memWrite, Evm.incrPc]
  case gas =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := chargeGas gBase evm) with im | ⟨evm1, charge_eq, eq'⟩
    · simp [Except.toError?, chargeGas] at im; cases safeSub _ _ <;> simp at im
    · simp only [bind, Except.bind, charge_eq, Evm.push]
      rcases of_bind_eq (f := Evm.push evm1.gas_left.toB256 evm1) with im' | ⟨evm2, push_eq, eq''⟩
      · simp [Except.toError?, Evm.push] at im'; split at im' <;> simp at im'
      · simp only [bind, Except.bind, push_eq, Evm.incrPc]
  case eq => exact not_limited_applyBinary
  case lt => exact not_limited_applyBinary
  case gt => exact not_limited_applyBinary
  case slt => exact not_limited_applyBinary
  case sgt => exact not_limited_applyBinary
  case iszero => exact not_limited_applyUnary
  case not => exact not_limited_applyUnary
  case and => exact not_limited_applyBinary
  case or => exact not_limited_applyBinary
  case xor => exact not_limited_applyBinary
  case signextend => exact not_limited_applyBinary
  case pop =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.pop) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.toError?, Evm.pop] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]
      rcases of_bind_eq (f := chargeGas gBase evm1) with im' | ⟨evm2, charge_eq, eq''⟩
      · simp [Except.toError?, chargeGas] at im'; cases safeSub _ _ <;> simp at im'
      · simp only [bind, Except.bind, charge_eq, Evm.incrPc]
  case byte => exact not_limited_applyBinary
  case shl => exact not_limited_applyBinary
  case shr => exact not_limited_applyBinary
  case sar => exact not_limited_applyBinary
  case kec =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.popToNat) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]
      rcases of_bind_eq (f := evm1.popToNat) with im' | ⟨⟨y, evm2⟩, pop_eq', eq''⟩
      · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im'; cases evm1.stack <;> simp at im'
      · simp only [bind, Except.bind, pop_eq']
        rcases of_bind_eq (f := chargeGas (gKeccak256 + gasKeccak256Word * (ceilDiv y 32) + evm2.extCost [(x, y)]) evm2) with im'' | ⟨evm3, charge_eq, eq'''⟩
        · simp [Except.toError?, chargeGas] at im''; cases safeSub _ _ <;> simp at im''
        · simp only [bind, Except.bind, charge_eq, Evm.push]
          rcases of_bind_eq (f := Evm.push (evm3.memRead x y).1.keccak (evm3.memRead x y).2) with im''' | ⟨evm4, push_eq, eq''''⟩
          · simp [Except.toError?, Evm.push] at im'''; split at im''' <;> simp at im'''
          · simp only [bind, Except.bind, push_eq, Evm.incrPc]
  case sub => exact not_limited_applyBinary
  case mul => exact not_limited_applyBinary
  case exp =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.pop) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.toError?, Evm.pop] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]
      rcases of_bind_eq (f := evm1.pop) with im' | ⟨⟨y, evm2⟩, pop_eq', eq''⟩
      · simp [Except.toError?, Evm.pop] at im'; cases evm1.stack <;> simp at im'
      · simp only [bind, Except.bind, pop_eq']
        rcases of_bind_eq (f := chargeGas (gExp + gExpbyte * y.bytecount) evm2) with im'' | ⟨evm3, charge_eq, eq'''⟩
        · simp [Except.toError?, chargeGas] at im''; cases safeSub _ _ <;> simp at im''
        · simp only [bind, Except.bind, charge_eq, Evm.push]
          rcases of_bind_eq (f := Evm.push (B256.bexp x y) evm3) with im''' | ⟨evm4, push_eq, eq''''⟩
          · simp [Except.toError?, Evm.push] at im'''; split at im''' <;> simp at im'''
          · simp only [bind, Except.bind, push_eq, Evm.incrPc]
  case div => exact not_limited_applyBinary
  case sdiv => exact not_limited_applyBinary
  case mod => exact not_limited_applyBinary
  case smod => exact not_limited_applyBinary
  case add => exact not_limited_applyBinary
  case addmod => exact not_limited_applyTernary
  case mulmod => exact not_limited_applyTernary
  case swap n =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := chargeGas gVerylow evm) with im | ⟨evm1, charge_eq, eq'⟩
    · simp [Except.toError?, chargeGas] at im; cases safeSub _ _ <;> simp at im
    · simp only [bind, Except.bind, charge_eq]
      match h_swap : List.swap evm1.stack n with
      | none => simp [h_swap]
      | some stack => simp [h_swap]
  case dup n =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := chargeGas gVerylow evm) with im | ⟨evm1, charge_eq, eq'⟩
    · simp [Except.toError?, chargeGas] at im; cases safeSub _ _ <;> simp at im
    · simp only [bind, Except.bind, charge_eq]
      match h_dup : evm1.stack[n]? with
      | none => simp [h_dup]
      | some word =>
        simp [h_dup]
        rcases of_bind_eq (f := evm1.push word) with im' | ⟨evm2, push_eq, eq''⟩
        · simp [Except.toError?, Evm.push] at im'; split at im' <;> simp at im'
        · simp only [bind, Except.bind, push_eq, Evm.incrPc]
  case sload =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.pop) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.toError?, Evm.pop] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]
      rcases of_bind_eq (f := if (evm1.contract, x) ∈ evm1.accessedStorageKeys then chargeGas gasWarmAccess evm1 else chargeGas gasColdSload (addAccessedStorageKey evm1 evm1.contract x)) with im' | ⟨evm2, charge_eq, eq''⟩
      · split at im' <;> { simp [Except.toError?, chargeGas] at im'; cases safeSub _ _ <;> simp at im' }
      · simp only [bind, Except.bind, charge_eq, Evm.push]
        rcases of_bind_eq (f := Evm.push (evm2.getStorVal evm2.contract x) evm2) with im'' | ⟨evm3, push_eq, eq'''⟩
        · simp [Except.toError?, Evm.push] at im''; split at im'' <;> simp at im''
        · simp only [bind, Except.bind, push_eq, Evm.incrPc]
  case tload =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.pop) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.toError?, Evm.pop] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]
      exact not_limited_pushItem
  case pc => exact not_limited_pushItem
  case sstore =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.pop) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.toError?, Evm.pop] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]
      rcases of_bind_eq (f := evm1.pop) with im' | ⟨⟨y, evm2⟩, pop_eq', eq''⟩
      · simp [Except.toError?, Evm.pop] at im'; cases evm1.stack <;> simp at im'
      · simp only [bind, Except.bind, pop_eq']
        rcases of_bind_eq (f := Except.assert (gCallStipend < evm2.gas_left) (s!"OutOfGasError", evm2)) with im'' | ⟨_, assert_eq, eq'''⟩
        · simp [Except.assert, Except.toError?] at im''; split at im'' <;> simp at im''
        · simp only [bind, Except.bind, assert_eq]
          rcases of_bind_eq (f := chargeGas (if (evm2.contract, x) ∈ evm2.accessedStorageKeys then (if evm2.getOrigStorVal evm2.contract x = evm2.getStorVal evm2.contract x ∧ evm2.getStorVal evm2.contract x ≠ y then (if evm2.getOrigStorVal evm2.contract x = 0 then gasStorageSet else (gasStorageUpdate - gasColdSload)) else gasWarmAccess) else (gasColdSload + (if evm2.getOrigStorVal evm2.contract x = evm2.getStorVal evm2.contract x ∧ evm2.getStorVal evm2.contract x ≠ y then (if evm2.getOrigStorVal evm2.contract x = 0 then gasStorageSet else (gasStorageUpdate - gasColdSload)) else gasWarmAccess))) evm2) with im''' | ⟨evm3, charge_eq, eq''''⟩
          · simp [Except.toError?, chargeGas] at im'''; cases safeSub _ _ <;> simp at im'''
          · simp only [bind, Except.bind, charge_eq, Evm.assertDynamic]
            rcases of_bind_eq (f := evm3.assertDynamic) with im'''' | ⟨_, assert_eq', eq'''''⟩
            · simp [Evm.assertDynamic, Except.assert, Except.toError?] at im''''; split at im'''' <;> simp at im''''
            · simp only [bind, Except.bind, assert_eq', Evm.incrPc]
  case tstore =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.pop) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.toError?, Evm.pop] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]
      rcases of_bind_eq (f := evm1.pop) with im' | ⟨⟨y, evm2⟩, pop_eq', eq''⟩
      · simp [Except.toError?, Evm.pop] at im'; cases evm1.stack <;> simp at im'
      · simp only [bind, Except.bind, pop_eq']
        rcases of_bind_eq (f := chargeGas gasWarmAccess evm2) with im'' | ⟨evm3, charge_eq, eq'''⟩
        · simp [Except.toError?, chargeGas] at im''; cases safeSub _ _ <;> simp at im''
        · simp only [bind, Except.bind, charge_eq, Evm.assertDynamic]
          rcases of_bind_eq (f := evm3.assertDynamic) with im''' | ⟨_, assert_eq', eq''''⟩
          · simp [Evm.assertDynamic, Except.assert, Except.toError?] at im'''; split at im''' <;> simp at im'''
          · simp only [bind, Except.bind, assert_eq', Evm.incrPc]
  case mcopy =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.popToNat) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]
      rcases of_bind_eq (f := evm1.popToNat) with im' | ⟨⟨y, evm2⟩, pop_eq', eq''⟩
      · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im'; cases evm1.stack <;> simp at im'
      · simp only [bind, Except.bind, pop_eq']
        rcases of_bind_eq (f := evm2.popToNat) with im'' | ⟨⟨z, evm3⟩, pop_eq'', eq'''⟩
        · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im''; cases evm2.stack <;> simp at im''
        · simp only [bind, Except.bind, pop_eq'']
          rcases of_bind_eq (f := chargeGas (gVerylow + gasCopy * (ceilDiv z 32) + evm3.extCost [(y, z), (x, z)]) evm3) with im''' | ⟨evm4, charge_eq, eq''''⟩
          · simp [Except.toError?, chargeGas] at im'''; cases safeSub _ _ <;> simp at im'''
          · simp only [bind, Except.bind, charge_eq, Evm.memRead, Evm.memWrite, Evm.incrPc]
  case log n =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.popToNat) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]
      rcases of_bind_eq (f := evm1.popToNat) with im' | ⟨⟨y, evm2⟩, pop_eq', eq''⟩
      · simp [Except.Limited, Evm.popToNat, Evm.pop, Except.toError?] at im'; cases evm1.stack <;> simp at im'
      · simp only [bind, Except.bind, pop_eq']
        rcases of_bind_eq (f := evm2.popN n) with im'' | ⟨⟨ts, evm3⟩, pop_eq'', eq'''⟩
        · simp [Evm.popN, Except.toError?] at im''; induction n generalizing evm2 <;> simp [Evm.popN, bind, Except.bind] at im''
          case succ n' ih =>
            rcases of_bind_eq (f := evm2.pop) with im_p | ⟨⟨x', evm2'⟩, pop_eq_p, eq_p⟩
            · simp [Evm.pop, Except.toError?] at im_p; cases evm2.stack <;> simp at im_p
            · simp [pop_eq_p] at im''; exact ih _ im''
        · simp only [bind, Except.bind, pop_eq'']
          rcases of_bind_eq (f := chargeGas (gLog + gLogdata * y + gLogtopic * n + evm3.extCost [(x, y)]) evm3) with im''' | ⟨evm4, charge_eq, eq''''⟩
          · simp [Except.toError?, chargeGas] at im'''; cases safeSub _ _ <;> simp at im'''
          · simp only [bind, Except.bind, charge_eq, Evm.assertDynamic]
            rcases of_bind_eq (f := evm4.assertDynamic) with im'''' | ⟨_, assert_eq, eq'''''⟩
            · simp [Evm.assertDynamic, Except.assert, Except.toError?] at im''''; split at im'''' <;> simp at im''''
            · simp only [bind, Except.bind, assert_eq, Evm.memRead, Evm.addLog, Evm.incrPc]
  case blockhash =>
    simp only [Except.Limited, Except.toError?]
    rcases of_bind_eq (f := evm.pop) with im | ⟨⟨x, evm1⟩, pop_eq, eq'⟩
    · simp [Except.toError?, Evm.pop] at im; cases evm.stack <;> simp at im
    · simp only [bind, Except.bind, pop_eq]
      rcases of_bind_eq (f := chargeGas gBlockhash evm1) with im' | ⟨evm2, charge_eq, eq''⟩
      · simp [Except.toError?, chargeGas] at im'; cases safeSub _ _ <;> simp at im'
      · simp only [bind, Except.bind, charge_eq, Evm.push]
        rcases of_bind_eq (f := Evm.push (if evm2.msg.benv.number ≤ x.toNat ∨ x.toNat + 256 < evm2.msg.benv.number then 0 else evm2.msg.benv.blockHashes.getD (evm2.msg.benv.blockHashes.length - (evm2.msg.benv.number - x.toNat)) 0) evm2) with im'' | ⟨evm3, push_eq, eq'''⟩
        · simp [Except.toError?, Evm.push] at im''; split at im'' <;> simp at im''
        · simp only [bind, Except.bind, push_eq, Evm.incrPc]

#exit

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
