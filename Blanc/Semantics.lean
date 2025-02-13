-- Semantics.lean : formalized semantics of the EVM and Blanc

import Blanc.Basic



-- EVM semantics --

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
  | pop -- 0x50 / 1 / 0 / Remove an item from the Stack.
  | mload -- 0x51 / 1 / 1 / Load a Word from memory.
  | mstore -- 0x52 / 2 / 0 / Store a Word in memory.
  | mstore8 -- 0x53 / 2 / 0 / Store a Byte in memory.
  | sload -- 0x54 / 1 / 1 / Load a Word from Storage.
  | sstore -- 0x55 / 2 / 0 / Store a Word in Storage.
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
  | invalid -- 0xFE / 0 / 0 / Designated invalid instruction.
deriving DecidableEq

def Rinst.toByte : Rinst → Byte
  | add          => Ox x0 x1
  | mul          => Ox x0 x2
  | sub          => Ox x0 x3
  | div          => Ox x0 x4
  | sdiv         => Ox x0 x5
  | mod          => Ox x0 x6
  | smod         => Ox x0 x7
  | addmod       => Ox x0 x8
  | mulmod       => Ox x0 x9
  | exp          => Ox x0 xA
  | signextend   => Ox x0 xB
  | lt           => Ox x1 x0
  | gt           => Ox x1 x1
  | slt          => Ox x1 x2
  | sgt          => Ox x1 x3
  | eq           => Ox x1 x4
  | iszero       => Ox x1 x5
  | and          => Ox x1 x6
  | or           => Ox x1 x7
  | xor          => Ox x1 x8
  | not          => Ox x1 x9
  | byte         => Ox x1 xA
  | shl          => Ox x1 xB
  | shr          => Ox x1 xC
  | sar          => Ox x1 xD
  | kec          => Ox x2 x0
  | address      => Ox x3 x0
  | balance      => Ox x3 x1
  | origin       => Ox x3 x2
  | caller       => Ox x3 x3
  | callvalue    => Ox x3 x4
  | calldataload => Ox x3 x5
  | calldatasize => Ox x3 x6
  | calldatacopy => Ox x3 x7
  | codesize     => Ox x3 x8
  | codecopy     => Ox x3 x9
  | gasprice     => Ox x3 xA
  | extcodesize  => Ox x3 xB
  | extcodecopy  => Ox x3 xC
  | retdatasize  => Ox x3 xD
  | retdatacopy  => Ox x3 xE
  | extcodehash  => Ox x3 xF
  | blockhash    => Ox x4 x0
  | coinbase     => Ox x4 x1
  | timestamp    => Ox x4 x2
  | number       => Ox x4 x3
  | prevrandao   => Ox x4 x4
  | gaslimit     => Ox x4 x5
  | chainid      => Ox x4 x6
  | selfbalance  => Ox x4 x7
  | basefee      => Ox x4 x8
  | pop          => Ox x5 x0
  | mload        => Ox x5 x1
  | mstore       => Ox x5 x2
  | mstore8      => Ox x5 x3
  | sload        => Ox x5 x4
  | sstore       => Ox x5 x5
  | pc           => Ox x5 x8
  | msize        => Ox x5 x9
  | gas          => Ox x5 xA
  | dup n        => Ox x8 (@Nat.toBits 4 n)
  | swap n       => Ox x9 (@Nat.toBits 4 n)
  | log n        => Ox xA (@Nat.toBits 4 n)

def Memory : Type := Word → Byte
def Storage : Type := Word → Word
abbrev Balances : Type := Addr → Word
abbrev Storages : Type := Addr → Storage
abbrev Codes : Type := Addr → Bytes

structure Env where
  (cta : Addr) -- contract address (YP : a)
  (oga : Addr) -- origin address (YP : o)
  (gpr : Word) -- gas price (YP : p)
  (cld : Bytes) -- calldata (YP : d)
  (cla : Addr) -- caller Addr (YP : s)
  (clv : Word) -- callvalue (YP : v)
  (code : Bytes) -- contract code  (YP : b)
  (exd : Nat) -- execution depth (YP : e)
  (wup : Bool) -- World-State update permission (YP : w)

structure World where
  (bal : Balances)
  (stor : Storages)
  (code : Codes)

abbrev Stack : Type := List Word

def Stack.Push (x y xy : Stack) : Prop := x <++ xy ++> y
def Stack.Pop (x xy y : Stack) : Prop := x <++ xy ++> y
def Stack.Diff (xs zs : Stack) (s s'' : Stack) : Prop := -- Pop xs ⊚ Push ys
  ∃ s' : Stack, Pop xs s s' ∧ Push zs s' s''

def Stack.SwapCore (x y : Word) : Nat → Stack → Stack → Prop
  | 0, y' :: xs, x' :: xs' => x = x' ∧ y = y' ∧ xs = xs'
  | n + 1, z :: xs, z' :: xs' => z = z' ∧ SwapCore x y n xs xs'
  | _, _, _ => False

def Stack.Swap (n : Nat) : Stack → Stack → Prop
  | x :: xs, y :: xs' => SwapCore x y n xs xs'
  | _, _ => False

inductive Stack.Nth : Nat → Word → Stack → Prop
  | head : ∀ x xs, Nth 0 x (x :: xs)
  | tail : ∀ m x y xs, Nth m x xs → Nth (m + 1) x (y :: xs)

def Stack.Dup (n : Nat) (s s' : Stack) : Prop := ∃ x, Push [x] s s' ∧ Stack.Nth n x s

abbrev Stor := Lean.RBMap B256 B256 compare

structure Acct where
  (nonce : B256)
  (bal : B256)
  (stor : Stor)
  (code : ByteArray)

structure Adr : Type where
  (high : B32)
  (mid : B64)
  (low : B64)

def Adr.ordering : Adr → Adr → Ordering
  | ⟨xh, xm, xl⟩, ⟨yh, ym, yl⟩ =>
    match compare xh yh with
    | .eq =>
      match compare xm ym with
      | .eq => compare xl yl
      | o => o
    | o => o

instance : Ord Adr := ⟨Adr.ordering⟩
abbrev Wor : Type := Lean.RBMap Adr Acct compare


structure State where
  -- balance, storage, & code : parts of the world state
  (bal : Addr → Word)
  (stor : Addr → Storage)
  (code : Addr → Bytes)
  -- stack, memory, & return data from last call: parts of the machine state
  (stk : Stack)
  (mem : Memory)
  (ret : Bytes)
  -- addresses marked for destruction : part of the substate
  (dest : List Addr)

-- Q : should 'ret' (the 'return buffer' part of machine State) be represented by an
-- option type, such that the last field of structure above is (r : Option Bytes) instead?
-- At a cursory glance this seems to be the case, since YP discusses varions edge cases
-- where o = ∅. But upon closer inspection, it seems '∅' is always an intermediate
-- helper term for defining how the return buffer should be updated in edge cases, but
-- never a final value that the return buffer is updated *to*. In other Words, there are
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
  (bal : Addr → Word)
  (stor : Addr → Storage)
  (code : Addr → Bytes)
  -- ret : similar to 'ret' of State, but this is the Byte
  -- sequence returned at the end of a code execution
  (ret : Bytes)
  -- List of Addres earmarke for destruction : parts of the 'subState'
  (dest : List Addr)



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

def Memory.slice' : Memory → Word → Nat → Bytes
  | _, _, 0 => []
  | m, x, n + 1 => m x :: slice' m x.succ n

def Memory.slice (m : Memory) (x y : Word) : Bytes := slice' m x y.toNat

def Memory.store (x : Word) : Bytes → Memory → Memory
  | [], m => m
  | b :: bs, m =>
    let m' := store x.succ bs m
    λ y => if x = y then b else m' y

def Memory.init : Memory := λ _ => Bits.zero _

def Mstored (x : Word) (bs : Bytes) (m m' : Memory) : Prop := m' = Memory.store x bs m

def Decrease {m n} (k : Bits m) (v : Bits n) (f g : Bits m → Bits n) : Prop :=
  Frel k (λ x y => x - v = y) f g

def Increase {m n} (k : Bits m) (v : Bits n) (f g : Bits m → Bits n) : Prop :=
  Frel k (λ x y => x + v = y) f g

def Transfer {m n : Nat}
    (b : Bits m → Bits n)
    (kd : Bits m) (v : Bits n) (ki : Bits m)
    (d : Bits m → Bits n) : Prop :=
    v ≤ b kd ∧
  ∃ c : Bits m → Bits n,
    Decrease kd v b c ∧
    Increase ki v c d

structure State.Rels where
  (bal : Balances → Balances → Prop)
  (stor : Storages → Storages → Prop)
  (code : Codes → Codes → Prop)
  (stk : Stack → Stack → Prop)
  (mem : Memory → Memory → Prop)
  (ret : Bytes → Bytes → Prop)
  (dest : List Addr → List Addr → Prop)

def State.Rels.dft : Rels :=
  {bal := Eq, stor := Eq, code := Eq, stk := Eq, mem := Eq, ret := Eq, dest := Eq}

structure State.Rel (r : Rels) (s s' : State) : Prop where
  (bal  : r.bal  (State.bal s) (State.bal s'))
  (stor : r.stor (State.stor s) (State.stor s'))
  (code : r.code (State.code s) (State.code s'))
  (stk  : r.stk  (State.stk s) (State.stk s'))
  (mem  : r.mem  (State.mem s) (State.mem s'))
  (ret  : r.ret  (State.ret s) (State.ret s'))
  (dest : r.dest (State.dest s) (State.dest s'))

def State.Diff (xs ys : List (Bits 256)) : State → State → Prop :=
  Rel {Rels.dft with stk := Stack.Diff xs ys}

def State.Push (xs : List (Bits 256)) : State → State → Prop :=
  Rel {Rels.dft with stk := Stack.Push xs}

def State.Pop (xs : List (Bits 256)) : State → State → Prop :=
  Rel {Rels.dft with stk := Stack.Pop xs}

def State.Swap (n : Nat) : State → State → Prop :=
  Rel {Rels.dft with stk := Stack.Swap n}

def State.Dup (n : Nat) : State → State → Prop :=
  Rel {Rels.dft with stk := Stack.Dup n}

def State.Add (s s' : State) : Prop :=  ∃ x y, State.Diff [x, y] [x + y] s s'
def State.Sub (s s' : State) : Prop :=  ∃ x y, State.Diff [x, y] [x - y] s s'
def State.Mul (s s' : State) : Prop := ∃ x y, State.Diff [x, y] [x * y] s s'
def State.Div (s s' : State) : Prop := ∃ x y, State.Diff [x, y] [x / y] s s'
def State.Mod (s s' : State) : Prop := ∃ x y, State.Diff [x, y] [x % y] s s'
def State.Sdiv (s s' : State) : Prop := ∃ x y, State.Diff [x, y] [Bits.sdiv x y] s s'
def State.Smod (s s' : State) : Prop := ∃ x y, State.Diff [x, y] [Bits.smod x y] s s'
def State.Addmod (s s' : State) : Prop := ∃ x y z, State.Diff [x, y, z] [Bits.addmod x y z] s s'
def State.Mulmod (s s' : State) : Prop := ∃ x y z, State.Diff [x, y, z] [Bits.mulmod x y z] s s'
def State.Exp (s s' : State) : Prop := ∃ x y, State.Diff [x, y] [x ^ y] s s'
def State.Signextend (s s' : State) : Prop :=
  ∃ x y z,
    State.Diff [x, y] [z] s s' ∧
    Word.Signext x y z

instance slt_decidable {n} (xs ys : Bits n) : Decidable (xs ±< ys) := by
  induction n with
  | zero => cases xs; cases ys; apply instDecidableFalse
  | succ n ih =>
    cases n with
    | zero =>
      match xs, ys with
      | ⦃x⦄, ⦃y⦄ =>
        rw [Bits.singleton_slt_singleton]
        apply instDecidableAnd
    | succ m =>
      match xs, ys with
      | xs +> x, ys +> y =>
      apply instDecidableOr

instance {n} (xs ys : Bits n) : Decidable (xs ±> ys) := by
  unfold Bits.Sgt; apply slt_decidable

def lt_check (x y : Bits 256) : Bits 256 := if x < y then 1 else 0
def gt_check (x y : Bits 256) : Bits 256 := if x > y then 1 else 0
def slt_check (x y : Bits 256) : Bits 256 := if x ±< y then 1 else 0
def sgt_check (x y : Bits 256) : Bits 256 := if x ±> y then 1 else 0
def eq_check (x y : Bits 256) : Bits 256 := if x = y then 1 else 0

def B256.lt_check  (x y : B256) : B256 := if x < y then 1 else 0
def B256.gt_check  (x y : B256) : B256 := if x > y then 1 else 0
def B256.slt_check (x y : B256) : B256 := if B256.Slt x y then 1 else 0
def B256.sgt_check (x y : B256) : B256 := if B256.Sgt x y then 1 else 0
def B256.eq_check  (x y : B256) : B256 := if x = y then 1 else 0

infix:70 " <? " => lt_check
infix:70 " >? " => gt_check
infix:70 " ±<? " => slt_check
infix:70 " ±>? " => sgt_check
infix:70 " =? " => eq_check


def State.Lt (s s' : State) : Prop := ∃ x y, State.Diff [x, y] [x <? y] s s'
def State.Gt (s s' : State) : Prop := ∃ x y, State.Diff [x, y] [x >? y] s s'
def State.Slt (s s' : State) : Prop := ∃ x y, State.Diff [x, y] [x ±<? y] s s'
def State.Sgt (s s' : State) : Prop := ∃ x y, State.Diff [x, y] [x ±>? y] s s'
def State.Eq (s s' : State) : Prop := ∃ x y, State.Diff [x, y] [x =? y] s s'
def State.Iszero (s s' : State) : Prop := ∃ x, State.Diff [x] [x =? 0] s s'
def State.And (s s' : State) : Prop := ∃ x y, State.Diff [x, y] [Bits.and x y] s s'
def State.Or (s s' : State) : Prop := ∃ x y, State.Diff [x, y] [Bits.or x y] s s'
def State.Xor (s s' : State) : Prop := ∃ x y, State.Diff [x, y] [Bits.xor x y] s s'
def State.Not (s s' : State) : Prop := ∃ x, State.Diff [x] [~ x] s s'
def State.Byte (s s' : State) : Prop :=
  ∃ (x y : Word) (b : Bits 8),
    State.Diff [x, y] [(0 : Bits 248) ++ b] s s' ∧
    List.getD (@Bits.toBytes 32 y) x.toNat 0 = b
def State.Shl (s s' : State) : Prop := ∃ x y, State.Diff [x, y] [Bits.shl x.toNat y] s s'
def State.Shr (s s' : State) : Prop := ∃ x y, State.Diff [x, y] [Bits.shr x.toNat y] s s'
def State.Sar (s s' : State) : Prop := ∃ x y, State.Diff [x, y] [Bits.sar x.toNat y] s s'
def State.Kec (s s' : State) : Prop :=
  ∃ x y, State.Diff [x, y] [(Memory.slice s.mem x y).keccak] s s'

def Bytes.Size (bs : Bytes) (sz : Word) : Prop := bs.length = sz.toNat

def State.Address (e : Env) (s s' : State) : Prop := State.Push [Addr.toWord e.cta] s s'
def State.Balance (s s' : State) : Prop := ∃ x, State.Diff [x] [s.bal (toAddr x)] s s'
def State.Origin (e : Env) (s s' : State) : Prop := State.Push [Addr.toWord e.oga] s s'
def State.Caller (e : Env) (s s' : State) : Prop := State.Push [Addr.toWord e.cla] s s'
def State.Callvalue (e : Env) (s s' : State) : Prop := State.Push [e.clv] s s'
def State.Calldatasize (e : Env) (s s' : State) : Prop := ∃ sz, State.Push [sz] s s' ∧ Bytes.Size e.cld sz
def State.Codesize (e : Env) (s s' : State) : Prop := ∃ sz, State.Push [sz] s s' ∧ Bytes.Size e.code sz
def State.Gasprice (e : Env) (s s' : State) : Prop := State.Push [e.gpr] s s'
def State.Extcodesize (s s' : State) : Prop :=
  ∃ x sz, State.Diff [x] [sz] s s' ∧ Bytes.Size (s.code (toAddr x)) sz
def State.Retdatasize (s s' : State) : Prop :=
  ∃ x r, State.Push [x] s s' ∧ s.ret = r ∧ Bytes.Size r x

-- For verification tasks where using correct values of Keccak hashes is crucial for correctness,
-- we can define a (keccak : Bytes → Word) and use it in the definition of State.extcodehash,
-- and also the Rinst.kec constructor of 'step'. For correctness of the WETH contract, however,
-- it suffices to require that _some_ hash value is computed and added to the Stack.

def State.Extcodehash (s s' : State) : Prop :=
  ∃ x y, State.Diff [x] [y] s s'

def State.Calldataload (e : Env) (s s' : State) : Prop :=
  ∃ x y,
    State.Diff [x] [y] s s' ∧
    List.sliceD e.cld x.toNat 32 0 = @Bits.toBytes 32 y

def State.Calldatacopy (e : Env) (s s' : State) : Prop :=
  ∃ x y z,
    State.Rel
      { State.Rels.dft with
        stk := Stack.Pop [x, y, z],
        mem := Mstored x <| List.sliceD e.cld y.toNat z.toNat 0 } s s'

def State.Codecopy (e : Env) (s s' : State) : Prop :=
  ∃ x y z bs,
    State.Rel
      { State.Rels.dft with
        stk := Stack.Pop [x, y, z],
        mem := Mstored x bs } s s' ∧
    List.slice? e.code y.toNat z.toNat = some bs

def State.Extcodecopy (s s' : State) : Prop :=
  ∃ w x y z bs,
    State.Rel
      { State.Rels.dft with
        stk := Stack.Pop [w, x, y, z],
        mem := Mstored x bs }
      s s' ∧
    List.slice? (s.code <| toAddr w) y.toNat z.toNat = some bs

def State.Retdatacopy (s s' : State) : Prop :=
  ∃ x y z,
    State.Rel
      { State.Rels.dft with
        stk := Stack.Pop [x, y, z],
        mem := Mstored x <| List.sliceD s.ret y.toNat z.toNat 0 }
      s s'

-- One thing that all block operations have in common is that they consume
-- no Stack items, leave exactly one new item on the Stack, and change nothing
-- else in the State. The contents of the new item depend on the operation used,
-- but their differences are immaterial for current purposes of the formalization,
-- so that part is unspecified here. These definitions will need to be augmented
-- to  verify more detailed properties about block operations.

def State.Sstore (e : Env) (s s' : State) : Prop :=
  ∃ x y : Word,
    State.Rel
    { State.Rels.dft with
      stor := Frel e.cta (Overwrite x y),
      stk := Stack.Diff [x, y] [] } s s' ∧
    e.wup = 1

def State.Sload (e : Env) (s s' : State) : Prop :=
 ∃ x, State.Diff [x] [s.stor e.cta x] s s'

def State.Mload (s s' : State) : Prop :=
  ∃ x y, State.Diff [x] [y] s s' ∧
    Memory.slice s.mem x 32 = @Bits.toBytes 32 y

def State.Mstore (s s' : State) : Prop :=
  ∃ x y,
    State.Rel
      { State.Rels.dft with
        stk := Stack.Diff [x, y] [],
        mem := Mstored x (@Bits.toBytes 32 y) }
      s s'

def State.Mstore8 (s s' : State) : Prop :=
  ∃ (x y : Word),
    State.Rel
      { State.Rels.dft with
        stk := Stack.Diff [x, y] [],
        mem := Mstored x [@Bits.suffix 8 248 y] } s s'

-- Design choice notes: in this formalization, definition of EVM operational semantics
-- does not follow the 'obvious' path that a cursory reading of YP may suggest,
-- i.e. by defining functions/relations that correspond 1:1 with the Θ/Λ/Ξ/X/O functions.
-- This is due to definition circularity, and tradeoffs in proof simplicity: Θ and Λ
-- depend on Ξ, which depends on X, which in turn depends on O, but O includes call/create
-- opcode cases that are defined in terms of Θ and Λ. Doing this in lean with mutual
-- recursion/induction isn't impossible, but comes with significant additional complexity
-- & proof difficulty that aren't justified by marginal improvements in staying faithful
-- to the original defs. In other Words, this formalization asks users to squint a little
-- harder to convince themselves that it really describes the EVM, because it is worth it.

def Result.wrap (s : State) (ret : Bytes) : Result :=
  {
    bal := s.bal,
    stor := s.stor,
    code := s.code,
    ret := ret,
    dest := s.dest
  }

def Linst.toByte : Linst → Byte
  | .stop => Ox x0 x0
  | .ret => Ox xF x3
  | .rev => Ox xF xD
  | .dest => Ox xF xF
  | .invalid      => Ox xF xE

def Jinst.toByte : Jinst → Byte
  | jump => Ox x5 x6     -- 0x56 / 1 / 0 / Unconditional jump.
  | jumpi => Ox x5 x7    -- 0x57 / 2 / 0 / Conditional jump.
  | jumpdest => Ox x5 xB -- 0x5b / 0 / 0 / Mark a valid jump destination.

def Xinst.toByte : Xinst → Byte
  | create   => Ox xF x0
  | call     => Ox xF x1
  | callcode => Ox xF x2
  | delcall  => Ox xF x4
  | create2  => Ox xF x5
  | statcall => Ox xF xA

def pushToByte (bs : Bytes) : Byte := Ox x5 xF + Nat.toByte bs.length
def pushToBytes (bs : Bytes) : Bytes := pushToByte bs :: bs

def Rinst.At (e : Env) (pc : Nat) (o : Rinst) : Prop :=
  List.get? e.code pc = some (Rinst.toByte o)
def Jinst.At (e : Env) (pc : Nat) (o : Jinst) : Prop :=
  List.get? e.code pc = some (Jinst.toByte o)
def Xinst.At (e : Env) (pc : Nat) (o : Xinst) : Prop :=
  List.get? e.code pc = some (Xinst.toByte o)
def Linst.At (e : Env) (pc : Nat) (o : Linst) : Prop :=
  List.get? e.code pc = some (Linst.toByte o)
def PushAt (e : Env) (pc : Nat) (bs : Bytes) : Prop :=
  List.Slice e.code pc (pushToBytes bs) ∧ bs.length ≤ 32

inductive Linst.Run : Env → State → Linst → Result → Prop
  | stop : ∀ e s, Linst.Run e s Linst.stop (Result.wrap s [])
  | ret :
    ∀ e s x y,
      ([x, y] <+: s.stk) →
      Linst.Run e s Linst.ret (.wrap s <| s.mem.slice x y)
  | dest :
    ∀ (e : Env) (s : State) x bal bal',
      e.wup = 1 →
      ([x] <+: s.stk) →
      Overwrite e.cta 0 s.bal bal →
      Increase (toAddr x) (s.bal e.cta) bal bal' →
      Linst.Run e s Linst.dest {s with bal := bal', ret := [], dest := e.cta :: s.dest}

def insidePushArg (e : Env) (loc : Nat) : Prop :=
  ∃ (pc : Nat) (bs : Bytes), PushAt e pc bs ∧ pc < loc ∧ loc ≤ pc + bs.length

def Jumpable (e : Env) (n : Nat) : Prop :=
  Jinst.At e n Jinst.jumpdest ∧ ¬ insidePushArg e n

def Fail (s : State) (o : Xinst) (s' : State) : Prop :=
  match o with
  | .create => ∃ x y z, State.Pop [x, y, z] s s'
  | .call => ∃ x₀ x₁ x₂ x₃ x₄ x₅ x₆, State.Pop [x₀, x₁, x₂, x₃, x₄, x₅, x₆] s s'
  | .callcode => ∃ x₀ x₁ x₂ x₃ x₄ x₅ x₆, State.Pop [x₀, x₁, x₂, x₃, x₄, x₅, x₆] s s'
  | .delcall => ∃ x₀ x₁ x₂ x₃ x₄ x₅, State.Pop [x₀, x₁, x₂, x₃, x₄, x₅] s s'
  | .create2 => ∃ x₀ x₁ x₂ x₃, State.Pop [x₀, x₁, x₂, x₃] s s'
  | .statcall => ∃ x₀ x₁ x₂ x₃ x₄ x₅, State.Pop [x₀, x₁, x₂, x₃, x₄, x₅] s s'

def Rinst.Run (e : Env) : State → Rinst → State → Prop :=
  Function.swap <|
    fun
    | Rinst.add => State.Add
    | Rinst.sub => State.Sub
    | Rinst.mul => State.Mul
    | Rinst.div => State.Div
    | Rinst.mod => State.Mod
    | Rinst.sdiv => State.Sdiv
    | Rinst.smod => State.Smod
    | Rinst.addmod => State.Addmod
    | Rinst.mulmod => State.Mulmod
    | Rinst.exp => State.Exp
    | Rinst.signextend => State.Signextend
    | Rinst.lt => State.Lt
    | Rinst.gt => State.Gt
    | Rinst.slt => State.Slt
    | Rinst.sgt => State.Sgt
    | Rinst.eq => State.Eq
    | Rinst.iszero => State.Iszero
    | Rinst.and => State.And
    | Rinst.or => State.Or
    | Rinst.xor => State.Xor
    | Rinst.not => State.Not
    | Rinst.byte => State.Byte
    | Rinst.shl => State.Shl
    | Rinst.shr => State.Shr
    | Rinst.sar => State.Sar
    | Rinst.kec => State.Kec
    | Rinst.address => State.Address e
    | Rinst.balance => State.Balance
    | Rinst.origin => State.Origin e
    | Rinst.caller => State.Caller e
    | Rinst.callvalue => State.Callvalue e
    | Rinst.calldataload => State.Calldataload e
    | Rinst.calldatasize => State.Calldatasize e
    | Rinst.calldatacopy => State.Calldatacopy e
    | Rinst.codesize => State.Codesize e
    | Rinst.codecopy => State.Codecopy e
    | Rinst.gasprice => State.Gasprice e
    | Rinst.extcodesize => State.Extcodesize
    | Rinst.extcodecopy => State.Extcodecopy
    | Rinst.retdatasize => State.Retdatasize
    | Rinst.retdatacopy => State.Retdatacopy
    | Rinst.extcodehash => State.Extcodehash
    | Rinst.blockhash => λ s s' => ∃ x, State.Push [x] s s'
    | Rinst.coinbase => λ s s' => ∃ x, State.Push [x] s s'
    | Rinst.timestamp => λ s s' => ∃ x, State.Push [x] s s'
    | Rinst.number => λ s s' => ∃ x, State.Push [x] s s'
    | Rinst.prevrandao => λ s s' => ∃ x, State.Push [x] s s'
    | Rinst.gaslimit => λ s s' => ∃ x, State.Push [x] s s'
    | Rinst.chainid => λ s s' => ∃ x, State.Push [x] s s'
    | Rinst.selfbalance => λ s s' => ∃ x, State.Push [x] s s'
    | Rinst.basefee => λ s s' => ∃ x, State.Push [x] s s'
    | Rinst.pop => λ s s' => ∃ x, State.Pop [x] s s'
    | Rinst.mload => State.Mload
    | Rinst.mstore => State.Mstore
    | Rinst.mstore8 => State.Mstore8
    | Rinst.sload => State.Sload e
    | Rinst.sstore => State.Sstore e
    | Rinst.msize => λ s s' => ∃ x, State.Push [x] s s'
    | Rinst.gas => λ s s' => ∃ x, State.Push [x] s s'
    | Rinst.pc => λ s s' => ∃ x, State.Push [x] s s'
    | Rinst.dup n => State.Dup n.val
    | Rinst.swap n => State.Swap n.val
    | Rinst.log n =>
      match n with
      | ⟨0, _⟩ => λ s s' => ∃ x₀ x₁, State.Pop [x₀, x₁] s s'
      | ⟨1, _⟩ => λ s s' => ∃ x₀ x₁ x₂, State.Pop [x₀, x₁, x₂] s s'
      | ⟨2, _⟩ => λ s s' => ∃ x₀ x₁ x₂ x₃, State.Pop [x₀, x₁, x₂, x₃] s s'
      | ⟨3, _⟩ => λ s s' => ∃ x₀ x₁ x₂ x₃ x₄, State.Pop [x₀, x₁, x₂, x₃, x₄] s s'
      | ⟨4, _⟩ => λ s s' => ∃ x₀ x₁ x₂ x₃ x₄ x₅, State.Pop [x₀, x₁, x₂, x₃, x₄, x₅] s s'
      | ⟨5, h⟩ => False.elim <| Nat.lt_irrefl _ h
    -- | Rinst.invalid => λ _ _ => False

inductive Jinst.Run : Env → State → Nat → Jinst → State → Nat → Prop
  | jump :
    ∀ e s s' pc x,
      State.Pop [x] s s' →
      Jumpable e x.toNat →
      Jinst.Run e s pc jump s' x.toNat
  | zero :
    ∀ e s s' pc x,
      State.Pop [x, 0] s s' →
      Jinst.Run e s pc jumpi s' (pc + 1)
  | succ :
    ∀ e s s' pc x y,
      State.Pop [x, y] s s' →
      y ≠ 0 →
      Jumpable e x.toNat →
      Jinst.Run e s pc jumpi s' x.toNat
  | dest :
    ∀ e s pc, Jinst.Run e s pc jumpdest s (pc + 1)

structure PreRun (s : State) (r : Result) : Prop where
  (bal : s.bal = r.bal)
  (stor : s.stor = r.stor)
  (code : s.code = r.code)
  (dest : s.dest = r.dest)

inductive Xinst.isCall : Xinst → Prop
| call : Xinst.isCall .call
| callcode : Xinst.isCall .callcode
| delcall : Xinst.isCall .delcall
| statcall : Xinst.isCall .statcall

def Env.prep (e : Env) (s : State)
    (cta : Addr) (cld : Bytes) (cla : Addr)
    (clv : Word) (cda : Addr) (exd : Nat) (wup : Bool) : Env :=
  { cta := cta, oga := e.oga, gpr := e.gpr, cld := cld, cla := cla,
    clv := clv, code := s.code cda, exd := exd, wup := wup }

def Env.prep' (e : Env)
    (cta : Addr) (clv : Word) (ctc : Bytes) (exd : Nat) : Env :=
  { cta := cta, oga := e.oga, gpr := e.gpr, cld := [], cla := e.cta,
    clv := clv, code := ctc, exd := exd, wup := 1 }

def State.prep (s : State) (bal : Balances) : State :=
  { bal := bal, stor := s.stor, code := s.code, stk := [],
    mem := Memory.init, ret := [], dest := s.dest }

def State.wrap (r : Result) (stk : Stack) (mem : Memory) : State :=
  { bal := r.bal, stor := r.stor, code := r.code,
    stk := stk, mem := mem, ret := r.ret, dest := r.dest }

def State.wrap' (r : Result) (cd : Codes) (mem : Memory) (stk : Stack) : State :=
  { bal := r.bal, stor := r.stor, code := cd, mem := mem,
    stk := stk, ret := r.ret, dest := r.dest }

def storeRet (mem : Memory) (ret : Bytes) (loc sz : Word) (mem' : Memory) : Prop :=
  Mstored loc (List.take sz.toNat ret) mem mem'

inductive Xinst.Run' : Env → State → Env → State → Xinst → Result → State → Prop
  | create :
    ∀ e : Env, e.wup = 1 →
    ∀ exd, e.exd = exd.succ →
    ∀ (s : State) (cta : Addr), s.code cta = [] →
    ∀ (clv clc csz : Word) (stk : Stack),
      Stack.Diff [clv, clc, csz] [Addr.toWord cta] s.stk stk →
    ∀ bal : Balances, Transfer s.bal e.cta clv cta bal →
    ∀ (r : Result) (cd : Codes),
      Overwrite cta r.ret r.code cd →
      Xinst.Run' e s (.prep' e cta clv (s.mem.slice clc csz) exd)
        (.prep s bal) .create r (.wrap' r cd s.mem stk)
  | create2 :
    ∀ e : Env, e.wup = 1 →
    ∀ exd, e.exd = exd.succ →
    ∀ (s : State) (cta : Addr), s.code cta = [] →
    ∀ (clv clc csz slt : Word) (stk : Stack),
      Stack.Diff [clv, clc, csz, slt] [Addr.toWord cta] s.stk stk →
    ∀ bal : Balances, Transfer s.bal e.cta clv cta bal →
    ∀ (r : Result) (cd : Codes),
      Overwrite cta r.ret r.code cd →
      Xinst.Run' e s (.prep' e cta clv (s.mem.slice clc csz) exd)
        (.prep s bal) .create r (.wrap' r cd s.mem stk)
  | call :
    ∀ (e : Env) exd, e.exd = exd.succ →
    ∀ gas adr clv ilc isz olc osz s stk,
      Stack.Diff [gas, adr, clv, ilc, isz, olc, osz] [1] s.stk stk →
    ∀ bal : Balances, Transfer s.bal e.cta clv (toAddr adr) bal →
    ∀ r : Result,
    ∀ mem : Memory, storeRet s.mem r.ret olc osz mem →
      Xinst.Run' e s
        (.prep e s (toAddr adr) (s.mem.slice ilc isz) e.cta clv (toAddr adr) exd e.wup)
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
        (.prep e s e.cta (s.mem.slice ilc isz) e.cta clv (toAddr adr) exd e.wup)
        (.prep s s.bal) .callcode r (.wrap r stk mem)
  | delcall :
    ∀ (e : Env) exd, e.exd = exd.succ →
    ∀ gas adr ilc isz olc osz s stk,
      Stack.Diff [gas, adr, ilc, isz, olc, osz] [1] s.stk stk →
    ∀ r : Result,
    ∀ mem : Memory, storeRet s.mem r.ret olc osz mem →
      Xinst.Run' e s
        (.prep e s e.cta (s.mem.slice ilc isz) e.cla e.clv (toAddr adr) exd e.wup)
        (.prep s s.bal) .delcall r (.wrap r stk mem)
  | statcall :
    ∀ (e : Env) exd, e.exd = exd.succ →
    ∀ gas adr ilc isz olc osz s stk,
      Stack.Diff [gas, adr, ilc, isz, olc, osz] [1] s.stk stk →
    ∀ r : Result,
    ∀ mem : Memory, storeRet s.mem r.ret olc osz mem →
      Xinst.Run' e s
        (.prep e s (toAddr adr) (s.mem.slice ilc isz) e.cta 0 (toAddr adr) exd 0)
        (.prep s s.bal) .statcall r (.wrap r stk mem)

inductive Step : Env → State → Nat → State → Nat → Type
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
      State.Push [bs.toBits 32] s s' →
      Step e s pc s' (pc + bs.length + 1)

inductive Halt : Env → State → Nat → Result → Prop
  | inst :
    ∀ e s pc o r,
      Linst.At e pc o →
      Linst.Run e s o r →
      Halt e s pc r
  | eoc : ∀ e s, Halt e s e.code.length (.wrap s [])

inductive Exec : Env → State → Nat → Result → Type
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
    (sda : Addr) -- tx sender address
                 -- (always an EOA & never has contract code, per EIP-3607)
    (rca : Addr) -- tx receiver address
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

def DeleteCodes : List Addr → Codes → Codes → Prop
  | [], c, c' => c = c'
  | a :: as, c, c'' => ∃ c' : Codes, Overwrite a [] c c' ∧ DeleteCodes as c' c''

  structure Transaction (w w' : World) : Type where
    (vs : Word) -- gas ultimately refunded to sender
    (vv : Word) -- gas ultimately rewarded to validator
    (vb : Word) -- gas ultimately burned
    (nof : vs.toNat + vv.toNat + vb.toNat < 2 ^ 256)
    (sda : Addr) -- tx sender address
    (eoa : w.code sda = []) -- per EIP-3607
    (bal : Balances) -- balances after upfront deduction
    (decr : Decrease sda (vs + vv + vb) w.bal bal)
    (le : vs + vv + vb ≤ w.bal sda)
    (rca : Addr) -- tx receiver address
    (r : Result) -- execution result
    (act : Transact sda rca {w with bal := bal} r)
    (bal' : Balances) -- balances after refund to sender
    (incr : Increase sda vs r.bal bal')
    (vla : Addr) -- validator address
    (incr' : Increase vla vv bal' w'.bal)
    (del : DeleteCodes r.dest r.code w'.code)
    (stor : w'.stor = r.stor)



-- Blanc semantics --

inductive Ninst : Type
  | reg : Rinst → Ninst
  | exec : Xinst → Ninst
  | push : ∀ bs : Bytes, bs.length ≤ 32 → Ninst

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

def Ninst.toBytes : Ninst → Bytes
  | reg o => [o.toByte]
  | exec o => [o.toByte]
  | push bs _ => pushToBytes bs

def Ninst.At (e : Env) (pc : Nat) : Ninst → Prop
  | reg o => o.At e pc
  | exec o => o.At e pc
  | push bs _ => PushAt e pc bs

inductive Xinst.Run : Env → State → Xinst → State → Prop
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

inductive Ninst.Run : Env → State → Ninst → State → Prop
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
      State.Push [Bytes.toBits 32 bs] s s' →
      Ninst.Run e s (Ninst.push bs h) s'

inductive Func.Run : List Func → Env → State → Func → Result → Prop
  | zero :
    ∀ {fs e s s' f g r},
      State.Pop [0] s s' →
      Func.Run fs e s' f r →
      Func.Run fs e s (branch f g) r
  | succ :
    ∀ {fs e s w s' f g r},
      w ≠ 0 →
      State.Pop [w] s s' →
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
      List.get? fs k = some f →
      Func.Run fs e s f r →
      Func.Run fs e s (call k) r

def Prog.Run (e : Env) (s : State) (p : Prog) (r : Result) : Prop :=
  Func.Run (p.main :: p.aux) e s p.main r
