-- CommonCore.lean : definitions and lemmas generally useful for writing and
-- verifying Blanc programs. The Blanc compiler's correctness proof lives in
-- CommonProofs.lean, and the tactics for automating Blanc program
-- verification live in Tactics.lean.

import Mathlib.Tactic.Have
import Mathlib.Tactic.Clear_
import Blanc.Semantics
import Jaune.Transaction

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat

def Func.toString : Func → String
  | .last o => Linst.toString o ++ " ::."
  | .next o p => o.toString ++ " ::: " ++ p.toString
  | .branch p q => "{" ++ q.toString ++ "} <?> {" ++ p.toString ++ "}"
  | .call _ => "[TAIL]"

instance : Repr Func := ⟨λ p _ => Func.toString p⟩

def Func.stop : Func := .last .stop
def Func.rev : Func := .last .rev
def Func.ret : Func := .last .ret

def Ninst.pushB256 (w : B256) : Ninst :=
  Jaune.Ninst.push w.toBytes.sig <|
    le_of_le_of_eq (List.length_dropWhile_le _ _) (B256.length_toBytes _)

abbrev Ninst.add : Ninst := Ninst.reg Rinst.add
abbrev Ninst.mul : Ninst := Ninst.reg Rinst.mul
abbrev Ninst.sub : Ninst := Ninst.reg Rinst.sub
abbrev Ninst.div : Ninst := Ninst.reg Rinst.div
abbrev Ninst.sdiv : Ninst := Ninst.reg Rinst.sdiv
abbrev Ninst.mod : Ninst := Ninst.reg Rinst.mod
abbrev Ninst.smod : Ninst := Ninst.reg Rinst.smod
abbrev Ninst.addmod : Ninst := Ninst.reg Rinst.addmod
abbrev Ninst.mulmod : Ninst := Ninst.reg Rinst.mulmod
abbrev Ninst.exp : Ninst := Ninst.reg Rinst.exp
abbrev Ninst.signextend : Ninst := Ninst.reg Rinst.signextend
abbrev Ninst.lt : Ninst := Ninst.reg Rinst.lt
abbrev Ninst.gt : Ninst := Ninst.reg Rinst.gt
abbrev Ninst.slt : Ninst := Ninst.reg Rinst.slt
abbrev Ninst.sgt : Ninst := Ninst.reg Rinst.sgt
abbrev Ninst.eq : Ninst := Ninst.reg Rinst.eq
abbrev Ninst.iszero : Ninst := Ninst.reg Rinst.iszero
abbrev Ninst.and : Ninst := Ninst.reg Rinst.and
abbrev Ninst.or : Ninst := Ninst.reg Rinst.or
abbrev Ninst.xor : Ninst := Ninst.reg Rinst.xor
abbrev Ninst.not : Ninst := Ninst.reg Rinst.not
abbrev Ninst.byte : Ninst := Ninst.reg Rinst.byte
abbrev Ninst.shr : Ninst := Ninst.reg Rinst.shr
abbrev Ninst.shl : Ninst := Ninst.reg Rinst.shl
abbrev Ninst.sar : Ninst := Ninst.reg Rinst.sar
abbrev Ninst.clz : Ninst := Ninst.reg Rinst.clz
abbrev Ninst.kec : Ninst := Ninst.reg Rinst.kec
abbrev Ninst.address : Ninst := Ninst.reg Rinst.address
abbrev Ninst.balance : Ninst := Ninst.reg Rinst.balance
abbrev Ninst.origin : Ninst := Ninst.reg Rinst.origin
abbrev Ninst.caller : Ninst := Ninst.reg Rinst.caller
abbrev Ninst.callvalue : Ninst := Ninst.reg Rinst.callvalue
abbrev Ninst.calldataload : Ninst := Ninst.reg Rinst.calldataload
abbrev Ninst.calldatasize : Ninst := Ninst.reg Rinst.calldatasize
abbrev Ninst.calldatacopy : Ninst := Ninst.reg Rinst.calldatacopy
abbrev Ninst.codesize : Ninst := Ninst.reg Rinst.codesize
abbrev Ninst.codecopy : Ninst := Ninst.reg Rinst.codecopy
abbrev Ninst.gasprice : Ninst := Ninst.reg Rinst.gasprice
abbrev Ninst.extcodesize : Ninst := Ninst.reg Rinst.extcodesize
abbrev Ninst.extcodecopy : Ninst := Ninst.reg Rinst.extcodecopy
abbrev Ninst.retdatasize : Ninst := Ninst.reg Rinst.retdatasize
abbrev Ninst.retdatacopy : Ninst := Ninst.reg Rinst.retdatacopy
abbrev Ninst.extcodehash : Ninst := Ninst.reg Rinst.extcodehash
abbrev Ninst.blockhash : Ninst := Ninst.reg Rinst.blockhash
abbrev Ninst.coinbase : Ninst := Ninst.reg Rinst.coinbase
abbrev Ninst.timestamp : Ninst := Ninst.reg Rinst.timestamp
abbrev Ninst.number : Ninst := Ninst.reg Rinst.number
abbrev Ninst.prevrandao : Ninst := Ninst.reg Rinst.prevrandao
abbrev Ninst.gaslimit : Ninst := Ninst.reg Rinst.gaslimit
abbrev Ninst.chainid : Ninst := Ninst.reg Rinst.chainid
abbrev Ninst.selfbalance : Ninst := Ninst.reg Rinst.selfbalance
abbrev Ninst.basefee : Ninst := Ninst.reg Rinst.basefee
abbrev Ninst.blobhash : Ninst := Ninst.reg Rinst.blobhash
abbrev Ninst.blobbasefee : Ninst := Ninst.reg Rinst.blobbasefee
abbrev Ninst.pop : Ninst := Ninst.reg Rinst.pop
abbrev Ninst.mload : Ninst := Ninst.reg Rinst.mload
abbrev Ninst.mstore : Ninst := Ninst.reg Rinst.mstore
abbrev Ninst.mstore8 : Ninst := Ninst.reg Rinst.mstore8
abbrev Ninst.sload : Ninst := Ninst.reg Rinst.sload
abbrev Ninst.sstore : Ninst := Ninst.reg Rinst.sstore
abbrev Ninst.tload : Ninst := Ninst.reg Rinst.tload
abbrev Ninst.tstore : Ninst := Ninst.reg Rinst.tstore
abbrev Ninst.mcopy : Ninst := Ninst.reg Rinst.mcopy
abbrev Ninst.pc : Ninst := Ninst.reg Rinst.pc
abbrev Ninst.msize : Ninst := Ninst.reg Rinst.msize
abbrev Ninst.gas : Ninst := Ninst.reg Rinst.gas
abbrev Ninst.dup (n : Fin 16) : Ninst := Ninst.reg (Rinst.dup n)
abbrev Ninst.swap (n : Fin 16) : Ninst := Ninst.reg (Rinst.swap n)
abbrev Ninst.log (n : Fin 5) : Ninst := Ninst.reg (Rinst.log n)
abbrev Ninst.create : Ninst := Ninst.exec Xinst.create
abbrev Ninst.call : Ninst := Ninst.exec Xinst.call
abbrev Ninst.callcode : Ninst := Ninst.exec Xinst.callcode
abbrev Ninst.delcall : Ninst := Ninst.exec Xinst.delcall
abbrev Ninst.create2 : Ninst := Ninst.exec Xinst.create2
abbrev Ninst.statcall : Ninst := Ninst.exec Xinst.statcall

abbrev Line : Type := List Ninst

infixr:65 " <?> " => λ f g => Func.branch g f
infixr:65 " ::: " => Func.next
postfix:100 " ::. " => Func.last

def prepend : Line → Func → Func
  | [], x => x
  | i :: is, x => i ::: prepend is x

infixr:65 " +++ " => prepend

inductive Line.Run : Sevm → Devm → Line → Devm → Prop
  | nil : ∀ {e s}, Line.Run e s [] s
  | cons :
    ∀ {e s i s' l s''},
      Ninst.Run e s i s' →
      Line.Run e s' l s'' →
      Line.Run e s (i :: l) s''

open Jaune.Ninst Ninst

def mstoreAt (x : B256) : Line := [pushB256 (x * 32), mstore]

-- assumes : k = # of indexed items (max 3)
-- assumes : Stack = ev_sig :: idx_item_0 ... idx_item_{k-1}
-- assumes : mem[x * 32, (x + y) * 32 - 1] = unindexed data
def logWith (k : Fin 4) (x y : B256) : Line :=
  pushB256 (y * 32) :: pushB256 (x * 32) :: -- x * 32 :: y * 32 :: ev_sig :: idx_item_0 ... idx_item_{k+1}
  log k.succ :: []

-- cdc X Y Z := calldatacopy(X, Y, Z)
-- I.e., look at the calldata, skip its first Y bytes,
-- and copy the next Z bytes into location X of memory.
def cdc (x y z : B256) : Line :=
  pushB256 z :: -- z
  pushB256 y :: -- y :: z
  pushB256 x :: -- x :: y :: z
  calldatacopy :: []

def argCopy (x y z : B256) : Line :=
  cdc (x * 32) ((y * 32) + 4) (z * 32)

def pushList : List B256 → Line := List.map pushB256

def returnMemoryRange (x y : B256) : Func := pushList [y, x] +++ Func.ret

def cdl (x : B256) : Line := [pushB256 x, calldataload]

-- Read the k-th argument word: skip the 4-byte selector, then k whole words.
--
-- Two conventions are baked in here, both inherited from WETH rather than
-- decided on, and both worth revisiting before a second contract:
--
-- (1) The 32-byte stride is right for every *head* word, which is every
--     `ArgType` except `dynBytes`. A dynamic argument's head word is an
--     *offset* into a tail, so `arg` on it yields the offset, not the value;
--     a caller wanting the payload follows that offset itself. `arg` is
--     head-word access, not an ABI decoder — see the note at `ArgType`.
-- (2) There is no calldata-length validation anywhere — `calldatasize` is in
--     the instruction set and unused. `calldataload` zero-pads past the end of
--     calldata, so a call with a truncated argument list reads zeros and
--     proceeds rather than reverting. This is not a divergence from deployed
--     WETH9, whose solc 0.4.x decoder also zero-pads (see WETH_DEVIATIONS.md,
--     "Checked similarities"); it is simply a convention Blanc has never had
--     to state, because it has only ever had one contract to satisfy.
def arg (k : B256) : Line := cdl ((32 * k) + 4)

-- Forward the payload of a dynamic `bytes` argument out of our own calldata
-- into memory, ABI-encoded for a call we are about to make.
--
-- ( -- len ), writing the length word at memory word `lenWord` and the payload
-- immediately after it, at memory byte `(lenWord + 1) * 32`.
--
-- This is the decoding step `arg` deliberately does not do (see the notes at
-- `arg` and at `ArgType`): argument `k`'s head word is an *offset*, so this
-- follows it to the length word, republishes the length, and `calldatacopy`s
-- the payload. Offset and length are used exactly as the caller supplied them
-- — there is no validation that either lies inside calldata, which is the
-- Blanc-wide convention `arg` already documents. `calldatacopy` zero-fills
-- anything past the end of calldata rather than reading out of bounds, so a
-- malformed tail forwards zeros; an absurd length is bounded only by
-- memory-expansion gas.
--
-- One parameter covers both destinations because the ABI fixes their relation:
-- a dynamic argument's payload always begins in the word after its length. The
-- payload is *not* padded up to a word boundary here — the region above it is
-- left untouched, so a caller wanting the zero padding a reference encoder
-- produces gets it from memory being zero-initialised, and must therefore not
-- have written above `(lenWord + 1) * 32` earlier in the frame.
def forwardArgTail (k lenWord : B256) : Line :=
  arg k ++                              -- off  (relative to calldata byte 4)
  pushB256 4 :: add ::                  -- p := 4 + off  (absolute: length word)
  dup 0 :: calldataload ::              -- len :: p
  dup 0 :: mstoreAt lenWord ++          -- len :: p  || mem[lenWord] = len
  dup 0 :: swap 1 ::                    -- p :: len :: len
  pushB256 32 :: add ::                 -- p + 32 :: len :: len   (the payload)
  pushB256 ((lenWord + 1) * 32) ::      -- dst :: p + 32 :: len :: len
  calldatacopy :: []                    -- len

-- Is the last call's return data shorter than `n` bytes?
--
-- ( -- retdatasize <? n )
--
-- The companion guard to `checkRetdataHead` below, and it must be branched on
-- first: `retdatacopy` is an exceptional halt when the requested range runs
-- past the return data, so reading a head word that may not be there is not a
-- check that fails, it is a check that aborts the frame.
def retdataShorterThan (n : B256) : Line := [pushB256 n, retdatasize, lt]

-- Does the last call's return data begin with the word `w`?
--
-- ( -- head =? w ), clobbering memory word `m`.
--
-- Assumes return data of at least 32 bytes; guard with `retdataShorterThan 32`
-- first. Return data *longer* than a word passes: this compares the head word
-- and says nothing about the rest, which is the same boundary Solidity's
-- `bytes32` return decoder draws.
def checkRetdataHead (w m : B256) : Line :=
  pushList [32, 0, m * 32] ++           -- m * 32 :: 0 :: 32
  retdatacopy ::                        -- || mem[m] = the head word
  pushB256 (m * 32) :: mload ::         -- head
  pushB256 w :: eq :: []                -- (head =? w)

-- Is this 256-bit word the image of an address? Both token contracts guard on
-- it and `Stor.rest` sums over exactly these keys, so it is neither's property.
def ValidAdr (w : B256) : Prop := ∃ a : Adr, a.toB256 = w

-- The same test as a mask: the ninety-six high bits, all set. `validAdr_iff` in
-- `Blanc/CommonProofs.lean` is the bridge, and `addressMask_eq_shl` relates it
-- to the six bytes `pushAddressMask` emits.
def addressMask : B256 := ⟨⟨.max, 0xffffffff00000000⟩, 0⟩

-- Push a 256-bit word used for testing address validity.
-- NOT and SHL are used so it takes up only 6 bytes of code,
-- whereas pushing the value directly would take up 32.

def pushAddressMask : Line := [pushB256 0, not, pushB256 (Nat.toB256 160), shl]

-- ( adr -- adr_invalid? )
def checkNonAddress : Line := pushAddressMask ++ [Ninst.and]

-- ( adr -- adr_valid? )
def checkAddress : Line := checkNonAddress ++ [iszero]

def returnTrue : Func :=
  pushB256 1 ::: mstoreAt 0 +++ -- || 1
  pushList [32, 0] +++ -- 0 :: 32 || 1
  Func.ret

abbrev Exec.Pred : Type :=
  ∀ pc sevm devm exc, Exec pc sevm devm exc → Prop

abbrev Prog.Pred : Type :=
  Nat → Sevm → Devm → Prog → Execution → Prop

def Exec.Fa (π : Exec.Pred) : Prop :=
  ∀ e s pc r (ex : Exec e s pc r), π _ _ _ _ ex

def Fortify (π : Exec.Pred) : Exec.Pred :=
  λ _ sevm _ _ exn =>
    (Exec.Fa <| λ _ sevm' _ _ exn' => sevm'.depth < sevm.depth → π _ _ _ _ exn') → π _ _ _ _ exn

lemma Exec.strong_rec (π : Exec.Pred)
  (h_fa : Exec.Fa (Fortify π)) : Exec.Fa π := by
  intros pc sevm devm exn exc
  apply
    @Nat.strongRecOn
      (λ n => ∀ pc_ sevm_ devm_ exn_ (exc_ : Exec pc_ sevm_ devm_ exn_), n = sevm_.depth → π _ _ _ _ exc_)
      sevm.depth
  · intros n h pc_ sevm_ devm_ exn_ exc_ h_eq; apply h_fa
    intros pc' sevm' devm' exn' exc' h_lt; rw [← h_eq] at h_lt
    apply h sevm'.depth h_lt _ _ _ _ exc' rfl
  · rfl

def sumBelow (f : Adr → B256) : Nat → Nat
  | 0 => 0
  | n + 1 => sumBelow f n + (f n.toAdr).toNat

theorem sumBelow_succ {f : Adr → B256} {n} :
    sumBelow f (n + 1) = sumBelow f n + (f n.toAdr).toNat := by
  delta sumBelow; rfl

def sum (f : Adr → B256) : Nat :=
  sumBelow f Adr.max.toNat.succ

/-- A contract's storage restricted to its address-shaped keys.  Both token
contracts in this repository key balances by `Adr.toB256 holder`, so for either
of them this is the balance map; the definition itself names no contract. -/
def Stor.rest (s : Stor) : Adr → B256 := s.get ∘ Adr.toB256

/-- The sum of the values a contract books at address-shaped keys.  Formerly
`wbsum` in `Blanc/Solvent.lean`, where both the name ("weth balance sum") and
the placement made a contract-agnostic notion look WETH-owned: WETH pairs it
with the ETH balance to state solvency (`Stor.Solvent`), fmint pairs it with
the supply slot to state conservation (`Stor.Conserved`), and neither use is
prior to the other.  Keys that are not address-shaped — fmint's `supplySlot`
among them — lie outside the sum by construction. -/
def balSum (s : Stor) : Nat := sum (Stor.rest s)

def pushToB8 (bs : Bytes) : UInt8 := 0x5F + Nat.toUInt8 bs.length
def pushToB8L (bs : Bytes) : Bytes := pushToB8 bs :: bs

def Xinst.toUInt8 : Xinst → UInt8
  | .create   => 0xF0
  | .call     => 0xF1
  | .callcode => 0xF2
  | .delcall  => 0xF4
  | .create2  => 0xF5
  | .statcall => 0xFA

def Ninst.toBytes : Ninst → Bytes
  | .reg o => [Rinst.toUInt8 o]
  | .exec o => [Xinst.toUInt8 o]
  | .push bs _ => pushToB8L bs

def compsize : Func → Nat
  | .last _ => 1
  | .next i p => compsize p + (Ninst.toBytes i).length
  | .branch p q => compsize p + compsize q + 5
  | .call _ => 4

def table : Nat → List Func → List (Nat × Func)
| _, [] => []
| k, f :: fs => ⟨k, f⟩ :: table (k + compsize f + 1) fs

def Func.compile (l : List (Nat × Func)) (n : Nat) : Func → Option Bytes
  | .last o => pure [o.toUInt8]
  | .next i p => do
    let p_bts ← Func.compile l (n + i.size) p
    pure <| Ninst.toBytes i ++ p_bts
  | .branch p q => do
    let pbs ← Func.compile l (n + 4) p
    let loc := n + pbs.length + 4
    guard (loc < 2 ^ 16)
    let qbs ← Func.compile l (loc + 1) q
    pure $
      ([0x61] : Bytes) ++
      [(loc >>> 8).toUInt8, loc.toUInt8] ++
      [Jinst.toUInt8 .jumpi] ++ pbs ++
      [Jinst.toUInt8 .jumpdest] ++ qbs
  | .call k => do
    let (loc, _) ← l[k]?
    guard (loc < 2 ^ 16)
    pure $
      ([0x61] : Bytes) ++
      [(loc >>> 8).toUInt8, loc.toUInt8] ++
      [Jinst.toUInt8 Jinst.jump]

def Table.compile (l : List (Nat × Func)) : List (Nat × Func) → Option Bytes
| [] => pure []
| (n, p) :: nps => do
  let bs ← Func.compile l (n + 1) p
  let bss ← Table.compile l nps
  pure <| [Jinst.toUInt8 .jumpdest] ++ bs ++ bss

lemma Table.compile_cons_eq_some {l n p l' bs}
    (h : Table.compile l ((n, p) :: l') = some bs) :
    ∃ cp cl',
      Func.compile l (n + 1) p = some cp ∧
      Table.compile l l' = some cl' ∧
      bs = [Jinst.toUInt8 .jumpdest] ++ cp ++ cl' := by
  rcases of_bind_eq_some h with ⟨cp, h_cp, h'⟩; clear h
  rcases of_bind_eq_some h' with ⟨cl', h_cl', h_eq⟩; clear h'
  simp at h_eq; refine' ⟨cp, cl', h_cp, h_cl', h_eq.symm⟩

def Prog.compile (p : Prog) : Option Bytes :=
  let t : List (Nat × Func) := table 0 (p.main :: p.aux)
  Table.compile t t


lemma Prog.compile_ne_nil {p} : Prog.compile p ≠ some [] := by
  simp only [Prog.compile]; intro h
  rcases of_bind_eq_some h with ⟨bs, _, h'⟩; clear h
  rcases of_bind_eq_some h' with ⟨bs', _, h⟩; clear h'; simp at h

def subcode (cd : Bytes) (k : Nat) : Option Bytes → Prop
  | none => False
  | some bs => List.Slice cd k bs

lemma Rinst.at_unique {e pc o o'} (h : At e pc o) (h' : At e pc o') : o = o' := by
  injection Eq.trans h.symm h' with eq
  injection eq with eq; injection eq with eq

lemma Xinst.at_unique {e pc o o'} (h : At e pc o) (h' : At e pc o') : o = o' := by
  injection Eq.trans h.symm h' with eq
  injection eq with eq; injection eq with eq

lemma Jinst.at_unique {e pc o o'} (h : At e pc o) (h' : At e pc o') : o = o' := by
  injection Eq.trans h.symm h' with eq; injection eq with eq

lemma Linst.at_unique {e pc o o'} (h : At e pc o) (h' : At e pc o') : o = o' := by
  injection Eq.trans h.symm h' with eq; injection eq with eq

lemma Ninst.at_unique {e pc o o'} (h : At e pc o) (h' : At e pc o') : o = o' := by
  injection Eq.trans h.symm h' with eq; injection eq with eq


lemma toInstType_pushToB8 {bs : Bytes} (h : bs.length ≤ 32) :
    (pushToB8 bs).toInstType = .P := by
  rw [← Nat.lt_succ_iff] at h
  simp only [pushToB8]; revert h
  generalize bs.length = n; revert n
  repeat (rw [Nat.forall_lt_succ_right']; refine' ⟨_, rfl⟩)
  simp only [Nat.not_lt_zero, Nat.toUInt8_eq, IsEmpty.forall_iff, implies_true]

lemma toInstType_toUInt8_swap (x : Fin 16) :
    (Rinst.toUInt8 (Rinst.swap x)).toInstType = .R := by
  rcases x with ⟨n, h⟩; revert h n
  repeat (rw [Nat.forall_lt_succ_left']; refine' ⟨rfl, _⟩)
  simp

lemma toInstType_toUInt8_dup (x : Fin 16) :
    (Rinst.toUInt8 (Rinst.dup x)).toInstType = .R := by
  rcases x with ⟨n, h⟩; revert h n
  repeat (rw [Nat.forall_lt_succ_left']; refine' ⟨rfl, _⟩)
  simp

lemma toInstType_toUInt8_log (x : Fin 5) :
    (Rinst.toUInt8 (Rinst.log x)).toInstType = .R := by
  rcases x with ⟨n, h⟩; revert h n
  repeat (rw [Nat.forall_lt_succ_left']; refine' ⟨rfl, _⟩)
  simp

lemma Rinst.toInstType_toUInt8 (r : Rinst) :
    (Rinst.toUInt8 r).toInstType = .R := by
  cases r <;> try {rfl}
  · apply toInstType_toUInt8_dup
  · apply toInstType_toUInt8_swap
  · apply toInstType_toUInt8_log


lemma Xinst.toInstType_toUInt8 (x : Xinst) :
    (Xinst.toUInt8 x).toInstType = .X := by
  cases x <;> rfl


lemma ByteArray.toList_eq_toList_data {xs : ByteArray} :
    xs.toList = xs.data.toList := by
  have gen :
      ∀ xs ys : List UInt8,
        _root_.ByteArray.toList.loop
          ⟨⟨xs ++ ys⟩⟩ xs.length xs.reverse = xs ++ ys := by
    intro xs ys;
    induction ys generalizing xs with
      | nil =>
        unfold _root_.ByteArray.toList.loop
        rw [if_neg _, List.reverse_reverse, List.append_nil]
        simp [ByteArray.size]
      | cons y ys ih =>
        unfold _root_.ByteArray.toList.loop
        have rw : ByteArray.get! ⟨⟨xs ++ y :: ys⟩⟩ xs.length = y := by
          simp [ByteArray.get!]
        have rw' : xs.length + 1 = (xs ++ [y]).length := by simp
        have rw'' : y :: xs.reverse = (xs ++ [y]).reverse := by simp
        rw [if_pos _, rw, List.append_cons, rw', rw'', ih]
        simp [ByteArray.size]
  rcases xs with ⟨⟨xs⟩⟩; apply gen [] xs

lemma ByteArray.of_getElem?_eq_some {xs : ByteArray} {n} {x} :
    xs.toList[n]? = .some x → xs.get! n = x := by
  rw [ByteArray.toList_eq_toList_data]
  simp only [ByteArray.get!, Array.getElem?_toList]
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  intro h; rw [h]; simp

lemma ByteArray.lt_size_of_getElem?_eq_some {xs : ByteArray} {n} {x}
    (eq : xs.toList[n]? = some x) : n < xs.size := by
  simp only [ByteArray.size, Array.size]
  rcases List.getElem?_eq_some_iff.mp eq with ⟨lt, _⟩
  rw [ByteArray.toList_eq_toList_data] at lt; exact lt

/-- Proof-indexed variant of `ByteArray.of_getElem?_eq_some`, matching the
dependent reads `ByteArray.getInst` performs since the Jaune partiality
closure (integrity Step 7). -/
lemma ByteArray.getElem_of_getElem?_eq_some {xs : ByteArray} {n : Nat} {x : UInt8}
    (eq : xs.toList[n]? = .some x) (h : n < xs.size) : xs[n] = x := by
  rw [ByteArray.toList_eq_toList_data, Array.getElem?_toList] at eq
  exact (Array.getElem?_eq_some_iff.mp eq).choose_spec

lemma Jinst.at_of_slice {code : ByteArray} {pc : Nat} {j : Jinst} {xs : Bytes}
    (slice : List.Slice code.toList pc (j.toUInt8 :: xs)) :
    Jinst.At code pc j := by
  have eq := List.get?_eq_of_slice slice
  simp only [Jinst.At, ByteArray.getInst]
  rw [dif_pos (ByteArray.lt_size_of_getElem?_eq_some eq)]
  have rw := ByteArray.getElem_of_getElem?_eq_some eq
    (ByteArray.lt_size_of_getElem?_eq_some eq)
  split <;>
  try { rename (UInt8.toInstType _ = _) => h
        rw [rw, Jinst.toInstType_toUInt8] at h; cases h }
  rw [rw, toJinst_toUInt8]; rfl

lemma Linst.at_of_slice {code : ByteArray} {pc : Nat} {l : Linst} {xs : Bytes}
    (slice : List.Slice code.toList pc (l.toUInt8 :: xs)) :
    Linst.At code pc l := by
  have eq := List.get?_eq_of_slice slice
  simp only [Linst.At, ByteArray.getInst]
  rw [dif_pos (ByteArray.lt_size_of_getElem?_eq_some eq)]
  have rw := ByteArray.getElem_of_getElem?_eq_some eq
    (ByteArray.lt_size_of_getElem?_eq_some eq)
  split <;>
  try { rename (UInt8.toInstType _ = _) => h
        rw [rw, Linst.toInstType_toUInt8] at h; cases h }
  rw [rw, toLinst_toUInt8]; rfl

lemma dup_toByte_toRinst? :
  ∀ n, UInt8.toRinst (Rinst.toUInt8 (Rinst.dup n)) = some (.dup n)
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | 13 => rfl
  | 14 => rfl
  | 15 => rfl
  | ⟨n + 16, h⟩ => by
    rw [← Nat.not_le] at h
    cases h (Nat.le_add_left _ _)

lemma swap_toByte_toRinst?
  : ∀ n, UInt8.toRinst (Rinst.toUInt8 (Rinst.swap n)) = some (.swap n)
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | 13 => rfl
  | 14 => rfl
  | 15 => rfl
  | ⟨n + 16, h⟩ => by
    rw [← Nat.not_le] at h
    cases h (Nat.le_add_left _ _)

lemma log_toByte_toRinst? :
  ∀ n, UInt8.toRinst (Rinst.toUInt8 (Rinst.log n)) = some (.log n)
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | ⟨n + 5, h⟩ => by
    rw [← Nat.not_le] at h
    cases h (Nat.le_add_left _ _)

lemma toUInt8_toRinst {i : Rinst} :
    UInt8.toRinst (Rinst.toUInt8 i) = some i := by
  cases i <;> try {rfl}
  · apply dup_toByte_toRinst?
  · apply swap_toByte_toRinst?
  · apply log_toByte_toRinst?

lemma Linst.run_of_at {pc sevm devm l exn}
    (cr : Exec pc sevm devm exn)
    (h_at : Linst.At sevm.code pc l) :
    Linst.Run sevm devm l exn :=
  (cr.last_inv h_at).symm

def PushAt (code : ByteArray) (pc : Nat) (xs : Bytes) : Prop :=
  ∃ le : xs.length ≤ 32, code.getInst pc = some (.next (.push xs le))

lemma toUInt8_toXinst {o : Xinst} :
    UInt8.toXinst (Xinst.toUInt8 o) = some o := by cases o <;> rfl


lemma toNat_pushToB8_eq {xs : Bytes} (le : xs.length ≤ 32) :
    (pushToB8 xs).toNat = xs.length + 95:= by
  simp only [pushToB8]; rw [UInt8.toNat_add_lo, Nat.lo_eq_of_lt] <;>
  {simp [UInt8.toNat_ofNat, UInt8.toNat_ofNat', Nat.toUInt8]; omega}


lemma ByteArray.get!_eq_getElem!_toList
    (xs : ByteArray) (i : Nat) : xs.get! i = xs.toList[i]! := by
  simp only [ByteArray.get!]
  rw [List.getElem!_eq_getElem?_getD, Array.getElem!_eq_getD]
  rw [Array.getD_eq_getD_getElem?, ByteArray.toList_eq_toList_data]
  rcases Nat.lt_or_ge i xs.data.size with lt | ge
  · rw [Array.getElem?_eq_getElem lt, List.getElem?_eq_getElem lt]; rfl
  · rw [Array.getElem?_eq_none ge, List.getElem?_eq_none ge]

lemma List.getD_eq_getElem!_of_lt_length {ξ} [Inhabited ξ]
    {xs : List ξ} {i : Nat} {d : ξ} : i < xs.length → xs.getD i d = xs[i]! := by
  intro lt; rw [List.getD_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem lt]; rfl

lemma ByteArray.size_eq_length_toList (xs : ByteArray) :
    xs.size = xs.toList.length := by
  simp only [ByteArray.size, Array.size]
  rw [ByteArray.toList_eq_toList_data]


lemma ByteArray.sliceD_eq_replicate (xs : ByteArray) (m n : Nat) (d : UInt8)
    (le : xs.size ≤ m) : ByteArray.sliceD xs m n d = List.replicate n d := by
  induction n generalizing xs m
  case zero => rfl
  case succ n ih =>
    simp only [ByteArray.sliceD];
    rw [dif_neg (not_lt.mpr le)]

lemma ByteArray.sliceD_eq (xs : ByteArray) (m n : Nat) (d : UInt8) :
    ByteArray.sliceD xs m n d = xs.toList.sliceD m n d := by
  induction n generalizing xs m
  case zero => rfl
  case succ n ih =>
    simp only [ByteArray.sliceD]; split
    · rename (_ < _) => lt
      have lt' : m < xs.toList.length := by
        simp only [ByteArray.size] at lt
        rw [ Array.size_eq_length_toList,
             ← ByteArray.toList_eq_toList_data ] at lt
        apply lt
      rw [List.sliceD_succ, ih]
      rw [ByteArray.getElem_of_getElem?_eq_some (List.getElem?_eq_getElem lt') lt]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem lt']
    · rename (¬ _ < _) => nlt
      rw [not_lt] at nlt
      simp only [List.replicate]
      rw [List.sliceD_succ]
      apply congr_arg₂
      · rw [ByteArray.size_eq_length_toList] at nlt
        rw [List.getD_eq_default nlt]
      · rw [← ih]; rw [ByteArray.sliceD_eq_replicate]; omega



lemma pushAt_of_slice {code : ByteArray} {pc} {xs : Bytes} (le : xs.length ≤ 32)
    (slice : List.Slice code.toList pc (pushToB8L xs)) : PushAt code pc xs := by
  have eq := List.get?_eq_of_slice slice
  have rw := ByteArray.getElem_of_getElem?_eq_some eq
    (ByteArray.lt_size_of_getElem?_eq_some eq)
  simp only [PushAt, ByteArray.getInst]
  refine' ⟨le, _⟩
  rw [dif_pos (ByteArray.lt_size_of_getElem?_eq_some eq)]
  split <;>
  try { rename (UInt8.toInstType _ = _) => h
        rw [rw, toInstType_pushToB8 le] at h; cases h }
  apply congr_arg; apply congr_arg; apply Ninst.push_ext
  rcases slice with ⟨len, slice⟩
  have rw' : UInt8.toNat (code[pc]'(ByteArray.lt_size_of_getElem?_eq_some eq)) - 95
      = xs.length := by
    rw [rw, toNat_pushToB8_eq le]; omega
  rw [rw', ByteArray.sliceD_eq]; simp [pushToB8L] at slice
  rw [List.length_slice? slice, List.length_cons] at slice
  apply List.sliceD_eq_of_slice?_eq_some (List.slice?_eq_cons_iff.mp slice).2

lemma Ninst.at_of_slice {code : ByteArray} {pc : Nat} {n : Ninst}
    (slice : List.Slice code.toList pc (Ninst.toBytes n)) :
    Ninst.At code pc n := by
  cases n
  case reg r =>
    simp [Ninst.toBytes] at slice
    have eq := List.get?_eq_of_slice slice
    simp only [Ninst.At, ByteArray.getInst]
    rw [dif_pos (ByteArray.lt_size_of_getElem?_eq_some eq)]
    have rw := ByteArray.getElem_of_getElem?_eq_some eq
      (ByteArray.lt_size_of_getElem?_eq_some eq)
    split <;>
    try { rename (UInt8.toInstType _ = _) => h
          rw [rw, Rinst.toInstType_toUInt8] at h; cases h }
    rw [rw, toUInt8_toRinst]; rfl
  case exec x =>
    simp [Ninst.toBytes] at slice
    have eq := List.get?_eq_of_slice slice
    simp only [Ninst.At, ByteArray.getInst]
    rw [dif_pos (ByteArray.lt_size_of_getElem?_eq_some eq)]
    have rw := ByteArray.getElem_of_getElem?_eq_some eq
      (ByteArray.lt_size_of_getElem?_eq_some eq)
    split <;>
    try { rename (UInt8.toInstType _ = _) => h
          rw [rw, Xinst.toInstType_toUInt8] at h; cases h }
    rw [rw, toUInt8_toXinst]; rfl
  case push xs le => apply (pushAt_of_slice le slice).2


lemma of_subcode {cd k} :
    ∀ {obs}, subcode cd k obs →
       ∃ bs, obs = some bs ∧ List.Slice cd k bs
  | none, h => by cases h
  | some bs, h => ⟨bs, rfl, h⟩

lemma subcode_compile_branch {code : ByteArray} {k l p q}
  (h : subcode code.toList k (Func.compile l k (Func.branch p q))) :
    ∃ loc : Nat,
      loc < 2 ^ 16 ∧
      Ninst.At code k (.push [(loc >>> 8).toUInt8, loc.toUInt8] two_le_32) ∧
      Jinst.At code (k + 3) Jinst.jumpi ∧
      subcode code.toList (k + 4) (Func.compile l (k + 4) p) ∧
      Jinst.At code loc Jinst.jumpdest ∧
      subcode code.toList (loc + 1) (Func.compile l (loc + 1) q) := by
  rcases of_subcode h with ⟨cd, h', h_slice⟩; clear h
  rcases of_bind_eq_some h' with ⟨qcd, h_qcd, h⟩; clear h'
  rcases of_guard_eq_some h with ⟨h_loc, h'⟩; clear h
  rcases of_bind_eq_some h' with ⟨pcd, h_pcd, h⟩; clear h'
  rw [← of_pure_eq_some h] at h_slice; clear h cd; rename' h_slice => h
  rw [List.append_assoc, List.append_assoc, List.append_assoc] at h
  let loc : Nat := k + qcd.length + 4
  refine' ⟨loc, h_loc, _⟩
  have pat : At code k (push [(loc >>> 8).toUInt8, loc.toUInt8] two_le_32) := by
    apply @Ninst.at_of_slice code k
    simp only [loc, Ninst.toBytes, pushToB8L, pushToB8]
    apply List.slice_prefix h
  refine' ⟨pat, _⟩; clear pat
  have h' := List.slice_suffix h; clear h
  rw [← List.singleton_append] at h'
  have jat : Jinst.At code (k + 3) Jinst.jumpi := by
    simp [Nat.toUInt8, List.length] at h'
    apply Jinst.at_of_slice (List.slice_prefix h')
  refine' ⟨jat, _⟩; clear jat
  have h := List.slice_suffix h'; clear h'
  rw [Nat.add_assoc] at h; simp [List.length] at h; rw [h_qcd]
  refine' ⟨List.slice_prefix h, _⟩
  have h' := List.slice_suffix h; clear h
  have h_rw : k + 4 + List.length qcd = k + List.length qcd + 4 := by omega
  rw [h_rw, ← List.singleton_append] at h'; simp [loc]; rw [h_pcd]
  refine' ⟨Jinst.at_of_slice (List.slice_prefix h'), List.slice_suffix h'⟩

lemma Prog.get?_table {m n} {c : List Func} :
    (Prod.snd <$> (table m c)[n]? : Option Func) =
      ((@getElem? (List Func) Nat Func _ _ c n) : Option Func) := by
  induction c generalizing m n with
  | nil => rfl
  | cons p c' ih =>
    cases n with
    | zero => simp [table]
    | succ n => simp [table]; apply ih

-- alternative version of Exec which rolls all arguments into a structure.

structure Exec.Deriv : Type where
  (pc : Nat)
  (sevm : Sevm)
  (devm : Devm)
  (exn : Execution)
  (exc : Exec pc sevm devm exn)

/-- The immediate sub-derivation relation.  One constructor per recursive
premise of `Exec`: the same-frame continuation (`cont`, `doneOk`), the child
derivation of a spawn (`runErrChild`, `runOkChild`), and the parent's
continuation after a spawn returns (`runOkCont`). -/
inductive Exec.Deriv.Prec : Exec.Deriv → Exec.Deriv → Prop
  | cont {pc : Nat} {sevm : Sevm} {devm : Devm} {pc' : Nat}
    {devm' : Devm} {exn : Execution}
    (hstep : Evm.step ⟨pc, sevm, devm⟩ = .cont pc' devm')
    (exc : Exec pc' sevm devm' exn) :
    Exec.Deriv.Prec
      ⟨pc', sevm, devm', exn, exc⟩
      ⟨pc, sevm, devm, exn, .cont hstep exc⟩
  | doneOk {pc : Nat} {sevm : Sevm} {devm : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat} {r} {devm' : Devm} {exn : Execution}
    (hstep : Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc')
    (henter : f.enter = .done r)
    (hr : rsm.run r = .ok devm')
    (exc : Exec pc' sevm devm' exn) :
    Exec.Deriv.Prec
      ⟨pc', sevm, devm', exn, exc⟩
      ⟨pc, sevm, devm, exn, .doneOk hstep henter hr exc⟩
  | runErrChild {pc : Nat} {sevm : Sevm} {devm : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat} {cevm : Evm} {raw : Execution} {e}
    (hstep : Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc')
    (henter : f.enter = .run cevm)
    (excChild : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hr : rsm.run (f.settle raw) = .error e) :
    Exec.Deriv.Prec
      ⟨cevm.pc, cevm.sta, cevm.dyna, raw, excChild⟩
      ⟨pc, sevm, devm, .error e, .runErr hstep henter excChild hr⟩
  | runOkChild {pc : Nat} {sevm : Sevm} {devm : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat} {cevm : Evm} {raw : Execution}
    {devm' : Devm} {exn : Execution}
    (hstep : Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc')
    (henter : f.enter = .run cevm)
    (excChild : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hr : rsm.run (f.settle raw) = .ok devm')
    (exc : Exec pc' sevm devm' exn) :
    Exec.Deriv.Prec
      ⟨cevm.pc, cevm.sta, cevm.dyna, raw, excChild⟩
      ⟨pc, sevm, devm, exn, .runOk hstep henter excChild hr exc⟩
  | runOkCont {pc : Nat} {sevm : Sevm} {devm : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat} {cevm : Evm} {raw : Execution}
    {devm' : Devm} {exn : Execution}
    (hstep : Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc')
    (henter : f.enter = .run cevm)
    (excChild : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hr : rsm.run (f.settle raw) = .ok devm')
    (exc : Exec pc' sevm devm' exn) :
    Exec.Deriv.Prec
      ⟨pc', sevm, devm', exn, exc⟩
      ⟨pc, sevm, devm, exn, .runOk hstep henter excChild hr exc⟩

infix:70 " ≺ " => Exec.Deriv.Prec

inductive Exec.Deriv.le : Exec.Deriv → Exec.Deriv → Prop
  | refl : ∀ p, Exec.Deriv.le p p
  | step : ∀ {p p' p''}, Exec.Deriv.le p p' → p' ≺ p'' → Exec.Deriv.le p p''

def Exec.Deriv.lt (pk pk'' : Exec.Deriv) : Prop :=
  ∃ pk' : Exec.Deriv, Exec.Deriv.le pk pk' ∧ Exec.Deriv.Prec pk' pk''

lemma Exec.Deriv.lt_of_prec {pk pk' : Exec.Deriv} (h : pk ≺ pk') : lt pk pk' :=
  ⟨pk, .refl _, h⟩

abbrev Exec.Deriv.gt (pk pk' : Exec.Deriv) : Prop := Exec.Deriv.lt pk' pk

lemma Exec.Deriv.eq_or_lt_of_le :
  ∀ {p p'}, Exec.Deriv.le p p' → p = p' ∨ Exec.Deriv.lt p p' := by
  intros p p'' h0; rcases h0 with _ | ⟨le, prec⟩
  · left; rfl
  · right; refine ⟨_, le, prec⟩

lemma Exec.Deriv.acc_of_le {pk pk' : Exec.Deriv}
    (h_le : Exec.Deriv.le pk pk') (h_acc : Acc Exec.Deriv.lt pk') : Acc Exec.Deriv.lt pk := by
  cases Exec.Deriv.eq_or_lt_of_le h_le with
  | inl h => rw [h]; exact h_acc
  | inr h => exact Acc.inv h_acc h

theorem Exec.Deriv.lt.well_founded : WellFounded Exec.Deriv.lt := by
  constructor;
  intro pk; rcases pk with ⟨_, _, _, _, _⟩
  apply
    @Exec.rec
      (λ pc sevm devm exn exc => Acc Exec.Deriv.lt ⟨pc, sevm, devm, exn, exc⟩) <;>
    clear *-
  -- halt : no sub-derivation
  · intro _ _ _ _ _; constructor
    intro _ lt; rcases lt with ⟨_, _, ⟨_⟩⟩
  -- cont : the same-frame continuation
  · intro _ _ _ _ _ _ _ _ ih
    constructor; intro _ lt
    rcases lt with ⟨_, le, prec⟩
    cases prec; exact acc_of_le le ih
  -- doneErr : no sub-derivation
  · intro _ _ _ _ _ _ _ _ _ _ _; constructor
    intro _ lt; rcases lt with ⟨_, _, ⟨_⟩⟩
  -- doneOk : the same-frame continuation
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ ih
    constructor; intro _ lt
    rcases lt with ⟨_, le, prec⟩
    cases prec; exact acc_of_le le ih
  -- runErr : the child derivation only
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ ihc
    constructor; intro _ lt
    rcases lt with ⟨_, le, prec⟩
    cases prec; exact acc_of_le le ihc
  -- runOk : the child derivation and the parent's continuation
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihc ih
    constructor; intro _ lt
    rcases lt with ⟨_, le, prec⟩
    cases prec
    · exact acc_of_le le ihc
    · exact acc_of_le le ih

abbrev Exec.Deriv.Pred : Type := Exec.Deriv → Prop

def Exec.Deriv.imp (π π' : Exec.Deriv.Pred) : Exec.Deriv.Pred := λ pk => π pk → π' pk

infix:70 " →p " => Exec.Deriv.imp

def Exec.Deriv.Fa (π : Exec.Deriv.Pred) : Prop := ∀ pk, π pk

notation "□p" => Exec.Deriv.Fa

def carryover (π : Exec.Deriv.Pred) : Exec.Deriv.Pred :=
(λ pk => □p (Exec.Deriv.gt pk →p π)) →p π

theorem Exec.Deriv.strongRec (π : Exec.Deriv.Pred) : □p (carryover π) → □p π := by
  intro ih pk
  apply @WellFounded.induction _ Exec.Deriv.lt Exec.Deriv.lt.well_founded π pk
  clear pk; intro pk ih'
  apply ih
  intro pk' h_gt
  apply ih' _ h_gt

lemma Rinst.run_of_at {pc sevm pre r post}
    (exc : Exec pc sevm pre (.ok post)) (rat : Rinst.At sevm.code pc r) :
    ∃ (inter : Devm) (exc' : Exec (pc + 1) sevm inter (.ok post)),
      Rinst.run ⟨pc, sevm, pre⟩ r = .ok inter ∧
      ⟨pc + 1, sevm, inter, .ok post, exc'⟩ ≺
        ⟨pc, sevm, pre, .ok post, exc⟩ := by
  have hstep : Evm.step ⟨pc, sevm, pre⟩ =
      Step.ofExecution (pc + 1) (r.run ⟨pc, sevm, pre⟩) :=
    Evm.step_next (n := .reg r) rat
  cases exc with
  | halt h => cases Step.ofExecution_ne_halt_ok (hstep.symm.trans h)
  | cont h exc' =>
    obtain ⟨hpc, hrun⟩ := Step.ofExecution_cont (hstep.symm.trans h)
    cases hpc
    exact ⟨_, exc', hrun, Exec.Deriv.Prec.cont h exc'⟩
  | doneOk h _ _ _ => cases Step.ofExecution_ne_spawn (hstep.symm.trans h)
  | runOk h _ _ _ _ => cases Step.ofExecution_ne_spawn (hstep.symm.trans h)

lemma Jinst.run_of_at {pc sevm pre j post}
    (exc : Exec pc sevm pre (.ok post)) (jat : Jinst.At sevm.code pc j) :
    ∃ (pc' : Nat) (inter : Devm), ∃ (exc' : Exec pc' sevm inter (.ok post)),
      Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩) ∧
      ⟨pc', sevm, inter, .ok post, exc'⟩ ≺ ⟨pc, sevm, pre, .ok post, exc⟩ := by
  have hstep : Evm.step ⟨pc, sevm, pre⟩ = Step.ofJump (j.run ⟨pc, sevm, pre⟩) :=
    Evm.step_jump jat
  cases exc with
  | halt h => cases Step.ofJump_ne_halt_ok (hstep.symm.trans h)
  | cont h exc' =>
    exact ⟨_, _, exc', Step.ofJump_cont (hstep.symm.trans h),
      Exec.Deriv.Prec.cont h exc'⟩
  | doneOk h _ _ _ => cases Step.ofJump_ne_spawn (hstep.symm.trans h)
  | runOk h _ _ _ _ => cases Step.ofJump_ne_spawn (hstep.symm.trans h)

lemma Ninst.run_of_at {pc sevm pre n post}
    (exc : Exec pc sevm pre (.ok post))
    (nat : Ninst.At sevm.code pc n) :
    ∃ (inter : Devm)
      (exc' : Exec (pc + n.size) sevm inter (.ok post)),
      Ninst.Run sevm pre n inter ∧
      Exec.Deriv.Prec
        ⟨(pc + n.size), sevm, inter, .ok post, exc'⟩
        ⟨pc, sevm, pre, .ok post, exc⟩ := by
  have hstep : Evm.step ⟨pc, sevm, pre⟩ = Ninst.step ⟨pc, sevm, pre⟩ n :=
    Evm.step_next nat
  cases exc with
  | halt h => cases Ninst.step_ne_halt_ok (hstep.symm.trans h)
  | cont h exc' =>
    have hs := hstep.symm.trans h
    cases Ninst.step_cont_pc hs
    refine ⟨_, exc', ⟨.none, trivial, pc, ?_⟩, Exec.Deriv.Prec.cont h exc'⟩
    simp only [Ninst.StepRun, hs, Step.Run]
    exact ⟨trivial, trivial⟩
  | doneOk h henter hr exc' =>
    have hs := hstep.symm.trans h
    cases Ninst.step_spawn_pc hs
    refine ⟨_, exc', ⟨.none, trivial, pc, ?_⟩,
      Exec.Deriv.Prec.doneOk h henter hr exc'⟩
    simp only [Ninst.StepRun, hs, Step.Run]
    exact ⟨_, RunFrame.of_done henter, hr.symm⟩
  | runOk h henter excChild hr exc' =>
    have hs := hstep.symm.trans h
    cases Ninst.step_spawn_pc hs
    refine ⟨_, exc', ⟨.some ⟨_, _⟩, ⟨excChild⟩, pc, ?_⟩,
      Exec.Deriv.Prec.runOkCont h henter excChild hr exc'⟩
    simp only [Ninst.StepRun, hs, Step.Run]
    exact ⟨_, RunFrame.of_run henter, hr.symm⟩

lemma Ninst.size_eq_length_toBytes (n : Ninst) :
    n.size = (Ninst.toBytes n).length := by cases n <;> rfl

def Devm.Pop (xs : List B256): Devm → Devm → Prop :=
  Rel {Rels.eq with stack := Stack.Pop xs}

def Devm.PushBurn (xs : List B256): Devm → Devm → Prop :=
  Rel {Devm.Rels.eq with stack := Stack.Push xs, gasLeft := (· ≥ ·)}

lemma Devm.pushBurn_of_run {x : B256} {pre inter : Devm} {cost : Nat} :
    (chargeGas cost pre >>= fun d => d.push x) = .ok inter →
    Devm.PushBurn [x] pre inter := by
  intro run
  simp only [bind, Except.bind] at run
  split at run; {cases run}
  rename_i d h_charge
  simp only [chargeGas_def] at h_charge
  split at h_charge
  · cases h_charge
  · rename_i gas h_safe
    injection h_charge with eq_d; subst eq_d
    unfold safeSub at h_safe
    split at h_safe
    · injection h_safe with eq_gas; subst eq_gas
      rw [Devm.push_def] at run
      simp only [Except.assert, bind, Except.bind] at run
      split at run; {cases run}
      injection run with eq_inter; subst eq_inter
      constructor <;>
        simp [Stack.Push, Split, Devm.Rels.eq, Devm.setMach, Devm.stack,
          Devm.memory, Devm.gasLeft, Devm.logs, Devm.refundCounter, Devm.output,
          Devm.accountsToDelete, Devm.returnData, Devm.error, Devm.accessedAddresses,
          Devm.accessedStorageKeys, Devm.state, Devm.createdAccounts,
          Devm.transientStorage]
    · contradiction

lemma Devm.pop_of_pop {x : B256} {devm devm' : Devm} :
    Devm.pop devm = .ok ⟨x, devm'⟩ → Devm.Pop [x] devm devm' := by
  intro pop
  simp only [Devm.pop_def] at pop
  split at pop; {cases pop}
  injection pop with eq; injection eq with eq eq'
  constructor <;> simp <;> rw [← eq'] <;> try {rfl}
  rename (devm.stack = _) => rw; rw [rw, eq]; rfl

lemma Devm.burn_of_chargeGas {cost : Nat} {devm devm' : Devm} :
    chargeGas cost devm = .ok devm' → Devm.Burn devm devm' := by
  intro eq
  simp only [chargeGas_def] at eq
  cases h : safeSub devm.gasLeft cost with
  | none =>
    rw [h] at eq
    cases eq
  | some gas =>
    rw [h] at eq
    injection eq with eq'
    rw [← eq']
    constructor <;> try {rfl}
    revert h
    unfold safeSub
    split
    · intro h
      injection h with h
      change devm.gasLeft ≥ gas
      omega
    · intro h
      cases h

lemma Devm.pop_append {xs ys : List B256} {devm devm' devm'' : Devm} :
    Devm.Pop xs devm devm' →
    Devm.Pop ys devm' devm'' →
    Devm.Pop (xs ++ ys) devm devm'' := by
  rintro ⟨_⟩; rename Stack.Pop _ _ _ => pop1
  rintro ⟨_⟩; rename Stack.Pop _ _ _ => pop2
  constructor <;> try {exact Eq.trans asm asm} -- h2_mem
  exact append_split pop1 pop2


lemma Devm.popBurn_of_pop_of_burn
    {xs devm devm' devm''}
    (pop : Devm.Pop xs devm devm')
    (burn : Devm.Burn devm' devm'') :
    Devm.PopBurn xs devm devm'' := by
  constructor
  · exact burn.stack ▸ pop.stack
  · exact Eq.trans pop.memory burn.memory
  · rw [pop.gasLeft]; exact burn.gasLeft
  · exact Eq.trans pop.logs burn.logs
  · exact Eq.trans pop.refundCounter burn.refundCounter
  · exact Eq.trans pop.output burn.output
  · exact Eq.trans pop.accountsToDelete burn.accountsToDelete
  · exact Eq.trans pop.returnData burn.returnData
  · exact Eq.trans pop.error burn.error
  · exact Eq.trans pop.accessedAddresses burn.accessedAddresses
  · exact Eq.trans pop.accessedStorageKeys burn.accessedStorageKeys
  · exact Eq.trans pop.state burn.state
  · exact Eq.trans pop.createdAccounts burn.createdAccounts
  · exact Eq.trans pop.transientStorage burn.transientStorage

lemma of_jumpi_run {pc sevm pre pc' inter}
    ( run :
      Jinst.Run
        {pc := pc, sta := sevm, dyna := pre}
        .jumpi (.ok ⟨pc', inter⟩) ) :
    ( ∃ (x : B256) ,
        pc' = pc + 1 ∧
        Devm.PopBurn [x, 0] pre inter ) ∨
    ( ∃ (x y : B256),
        pc' = x.toNat ∧
        Devm.PopBurn [x, y] pre inter ∧
        jumpable sevm.code x.toNat = true ∧
        y ≠ 0 ) := by
  rcases Except.bind_eq_ok run with ⟨⟨x, devm1⟩, eq1, run'⟩; clear run
  rcases Except.bind_eq_ok run' with ⟨⟨y, devm2⟩, eq2, run⟩; clear run'
  rcases Except.bind_eq_ok run with ⟨devm3, eq3, run'⟩; clear run
  split at run'
  · left;
    injection run' with eq; injection eq
    iterate 3 (rename_i eq; cases eq)
    refine' ⟨x, rfl, _⟩
    have pop1 := Devm.pop_of_pop eq1; clear eq1
    have pop2 := Devm.pop_of_pop eq2; clear eq2
    have pop := Devm.pop_append pop1 pop2; clear pop1 pop2
    have burn := Devm.burn_of_chargeGas eq3; clear eq3
    exact Devm.popBurn_of_pop_of_burn pop burn
  · right
    rcases Except.bind_eq_ok run' with ⟨u, eq4, run⟩; clear run'
    injection run with eq; injection eq
    iterate 2 (rename_i eq; cases eq)
    refine' ⟨x, y, rfl, _, Except.assert_eq_ok eq4, asm⟩
    have pop1 := Devm.pop_of_pop eq1; clear eq1
    have pop2 := Devm.pop_of_pop eq2; clear eq2
    have pop := Devm.pop_append pop1 pop2; clear pop1 pop2
    have burn := Devm.burn_of_chargeGas eq3; clear eq3
    exact Devm.popBurn_of_pop_of_burn pop burn

lemma of_jumpdest_run {pc sevm pre pc' inter}
    ( run :
      Jinst.Run
        {pc := pc, sta := sevm, dyna := pre}
        .jumpdest (.ok ⟨pc', inter⟩) ) :
    pc' = pc + 1 ∧ Devm.Burn pre inter := by
  rcases Except.bind_eq_ok run with ⟨devm, eq_charge, eq_ok⟩
  injection eq_ok with eq
  injection eq with eq_pc eq_devm
  cases eq_pc; cases eq_devm
  refine' ⟨rfl, Devm.burn_of_chargeGas eq_charge⟩

lemma jumpdest_at {pc sevm pre post}
    (exc : Exec pc sevm pre (.ok post))
    (jat : Jinst.At sevm.code pc .jumpdest) :
    ∃ (inter : Devm) (exc' : Exec (pc + 1) sevm inter (.ok post)),
      Devm.Burn pre inter ∧
      ⟨pc + 1, sevm, inter, .ok post, exc'⟩ ≺
      ⟨pc, sevm, pre, .ok post, exc⟩ := by
  rcases Jinst.run_of_at exc jat with ⟨pc', inter, exc', run, prec⟩
  rcases of_jumpdest_run run with ⟨eq_pc, burn⟩
  cases eq_pc
  refine' ⟨inter, exc', burn, prec⟩

lemma of_jump_run {pc sevm pre pc' inter}
    ( run :
      Jinst.Run
        {pc := pc, sta := sevm, dyna := pre}
        .jump (.ok ⟨pc', inter⟩) ) :
    ∃ (x : B256),
      pc' = x.toNat ∧
      Devm.PopBurn [x] pre inter ∧
      jumpable sevm.code x.toNat = true := by
  rcases Except.bind_eq_ok run with ⟨⟨x, devm1⟩, eq1, run⟩
  rcases Except.bind_eq_ok run with ⟨devm2, eq2, run⟩
  rcases Except.bind_eq_ok run with ⟨_, eq3, run⟩
  injection run with eq; injection eq with eq_pc eq_devm
  cases eq_pc; cases eq_devm
  refine' ⟨x, rfl, Devm.popBurn_of_pop_of_burn (Devm.pop_of_pop eq1) (Devm.burn_of_chargeGas eq2), Except.assert_eq_ok eq3⟩

lemma jump_at {pc sevm pre post}
    (exc : Exec pc sevm pre (.ok post))
    (jat : Jinst.At sevm.code pc .jump) :
    ∃ (x : B256) (inter : Devm) (exc' : Exec x.toNat sevm inter (.ok post)),
      Devm.PopBurn [x] pre inter ∧
      jumpable sevm.code x.toNat = true ∧
      ⟨x.toNat, sevm, inter, .ok post, exc'⟩ ≺
      ⟨pc, sevm, pre, .ok post, exc⟩ := by
  rcases Jinst.run_of_at exc jat with ⟨pc', inter, exc', run, prec⟩
  rcases of_jump_run run with ⟨x, eq_pc, pb, jp⟩
  cases eq_pc
  refine' ⟨x, inter, exc', pb, jp, prec⟩

lemma jumpi_at {pc sevm pre post}
    (exc : Exec pc sevm pre (.ok post))
    (jat : Jinst.At sevm.code pc .jumpi) :
    ( ∃ (x : B256) (inter : Devm)
        (exc' : Exec (pc + 1) sevm inter (.ok post)),
        Devm.PopBurn [x, 0] pre inter ∧
        ⟨pc + 1, sevm, inter, .ok post, exc'⟩ ≺
        ⟨pc, sevm, pre, .ok post, exc⟩ ) ∨
    ( ∃ (x y : B256) (inter : Devm)
        (exc' : Exec x.toNat sevm inter (.ok post)),
        Devm.PopBurn [x, y] pre inter ∧
        jumpable sevm.code x.toNat = true ∧ y ≠ 0 ∧
        ⟨x.toNat, sevm, inter, .ok post, exc'⟩ ≺
          ⟨pc, sevm, pre, .ok post, exc⟩ ) := by
  rcases Jinst.run_of_at exc jat
    with ⟨pc', inter, exc', run, prec⟩
  rcases of_jumpi_run run with
      ⟨x, pc_eq, pb⟩
    | ⟨x, y, pc_eq, pb, jumpable_eq, ne_zero⟩
  · left; cases pc_eq; refine' ⟨x, inter, exc', pb, prec⟩
  · right; cases pc_eq;
    refine' ⟨x, y, inter, exc', pb, jumpable_eq, ne_zero, prec⟩

lemma push_of_pushAt
    {pc sevm pre xs post} (exc : Exec pc sevm pre (.ok post))
    (h_at : PushAt sevm.code pc xs) :
    ∃ (inter : Devm) (exc' : Exec (pc + xs.length + 1) sevm inter (.ok post)),
      Devm.PushBurn [Bytes.toB256 xs] pre inter ∧
      ⟨pc + xs.length + 1, sevm, inter, .ok post, exc'⟩ ≺
        ⟨pc, sevm, pre, .ok post, exc⟩ := by
  rcases h_at with ⟨le, h_at⟩
  have hstep : Evm.step ⟨pc, sevm, pre⟩ = Ninst.step ⟨pc, sevm, pre⟩ (.push xs le) :=
    Evm.step_next h_at
  cases exc with
  | halt h => cases Ninst.step_ne_halt_ok (hstep.symm.trans h)
  | cont h exc' =>
    have hs := hstep.symm.trans h
    rw [Ninst.step_push] at hs
    obtain ⟨hpc, hrun⟩ := Step.ofExecution_cont hs
    cases hpc
    exact ⟨_, exc', Devm.pushBurn_of_run hrun, Exec.Deriv.Prec.cont h exc'⟩
  | doneOk h _ _ _ =>
    have hs := hstep.symm.trans h
    rw [Ninst.step_push] at hs
    cases Step.ofExecution_ne_spawn hs
  | runOk h _ _ _ _ =>
    have hs := hstep.symm.trans h
    rw [Ninst.step_push] at hs
    cases Step.ofExecution_ne_spawn hs

def Func.RunIfOk (fs : List Func) (sevm : Sevm) (devm : Devm) (f : Func) : Execution → Prop
  | .error _ => True
  | .ok devm' => Func.Run fs sevm devm f devm'
















lemma Stack.push_cons_pop_cons
    {x y} {xs ys} {s s' s''}
    (h : Stack.Push (x :: xs) s s')
    (h' : Stack.Pop (y :: ys) s' s'') :
    (x = y ∧ ∃ zs, Stack.Push xs s zs ∧ Stack.Pop ys zs s'') := by
  simp [Stack.Push, Split] at h
  simp [Stack.Pop, Split] at h'
  match s' with
  | [] => cases h
  | z :: zs =>
    rw [List.cons_eq_cons] at h
    rw [List.cons_eq_cons] at h'
    refine' ⟨Eq.trans h.left.symm h'.left, zs, h.right, h'.right⟩

lemma Devm.pushBurn_cons_popBurn_cons
    {x y} {xs ys} {s s' s''}
    (h : Devm.PushBurn (x :: xs) s s')
    (h' : Devm.PopBurn (y :: ys) s' s'') :
    (x = y ∧ ∃ st, Devm.PushBurn xs s st ∧ Devm.PopBurn ys st s'') := by
  rcases h with ⟨h_stack, h_mem, h_gas, h_logs, h_refund, h_out, h_del, h_ret, h_err, h_acc, h_keys, h_state, h_cas, h_trans⟩
  rcases h' with ⟨h'_stack, h'_mem, h'_gas, h'_logs, h'_refund, h'_out, h'_del, h'_ret, h'_err, h'_acc, h'_keys, h'_cas, h'_state, h'_trans⟩
  have push_pop_stack := Stack.push_cons_pop_cons h_stack h'_stack
  rcases push_pop_stack with ⟨h_eq, stk, h_push, h_pop⟩
  refine' ⟨
    h_eq,
    s'.withStack stk,
    ⟨h_push, h_mem, h_gas, h_logs, h_refund, h_out, h_del, h_ret, h_err, h_acc, h_keys, h_state, h_cas, h_trans⟩,
    ⟨h_pop, h'_mem, h'_gas, h'_logs, h'_refund, h'_out, h'_del, h'_ret, h'_err, h'_acc, h'_keys, h'_cas, h'_state, h'_trans⟩
  ⟩

lemma Devm.burn_of_popBurn_nil {s s'} (h : Devm.PopBurn [] s s') :
    Devm.Burn s s' := by
  refine ⟨?_, h.memory, h.gasLeft, h.logs, h.refundCounter, h.output, h.accountsToDelete, h.returnData, h.error, h.accessedAddresses, h.accessedStorageKeys, h.state, h.createdAccounts, h.transientStorage⟩; change s.stack = s'.stack; simpa only [Stack.Pop, Split, List.nil_append] using h.stack

lemma Devm.burn_of_pushBurn_nil {s s'} (h : Devm.PushBurn [] s s') :
    Devm.Burn s s' := by
  rcases h with
    ⟨h_stack, h_mem, h_gas, h_logs, h_refund, h_out, h_del, h_ret, h_err,
      h_acc, h_keys, h_state, h_cas, h_trans⟩
  refine ⟨?_, h_mem, h_gas, h_logs, h_refund, h_out, h_del, h_ret, h_err, h_acc, h_keys, h_state, h_cas, h_trans⟩; change s.stack = s'.stack; simpa only [Stack.Push, Split, List.nil_append] using h_stack.symm

lemma Devm.burn_trans {x y z} (h1 : Devm.Burn x y) (h2 : Devm.Burn y z) : Devm.Burn x z := by
  rcases h1 with ⟨h1_stack, h1_mem, h1_gas, h1_logs, h1_refund, h1_out, h1_del, h1_ret, h1_err, h1_acc, h1_keys, h1_state, h1_cas, h1_trans⟩
  rcases h2 with ⟨h2_stack, h2_mem, h2_gas, h2_logs, h2_refund, h2_out, h2_del, h2_ret, h2_err, h2_acc, h2_keys, h2_state, h2_cas, h2_trans⟩
  refine' ⟨Eq.trans h1_stack h2_stack, Eq.trans h1_mem h2_mem, Nat.le_trans h2_gas h1_gas, Eq.trans h1_logs h2_logs, Eq.trans h1_refund h2_refund, Eq.trans h1_out h2_out, Eq.trans h1_del h2_del, Eq.trans h1_ret h2_ret, Eq.trans h1_err h2_err, Eq.trans h1_acc h2_acc, Eq.trans h1_keys h2_keys, Eq.trans h1_state h2_state, Eq.trans h1_cas h2_cas, Eq.trans h1_trans h2_trans⟩

lemma Devm.popBurn_of_burn_of_popBurn {devm devm' devm''} {xs}
    (burn : Devm.Burn devm devm')
    (popBurn : Devm.PopBurn xs devm' devm'') :
    Devm.PopBurn xs devm devm'' := by
  constructor
  · exact burn.stack ▸ popBurn.stack
  · exact Eq.trans burn.memory popBurn.memory
  · exact Nat.le_trans popBurn.gasLeft burn.gasLeft
  · exact Eq.trans burn.logs popBurn.logs
  · exact Eq.trans burn.refundCounter popBurn.refundCounter
  · exact Eq.trans burn.output popBurn.output
  · exact Eq.trans burn.accountsToDelete popBurn.accountsToDelete
  · exact Eq.trans burn.returnData popBurn.returnData
  · exact Eq.trans burn.error popBurn.error
  · exact Eq.trans burn.accessedAddresses popBurn.accessedAddresses
  · exact Eq.trans burn.accessedStorageKeys popBurn.accessedStorageKeys
  · exact Eq.trans burn.state popBurn.state
  · exact Eq.trans burn.createdAccounts popBurn.createdAccounts
  · exact Eq.trans burn.transientStorage popBurn.transientStorage

lemma Devm.popBurn_of_popBurn_of_pop {devm devm' devm''} {xs}
    (popBurn : Devm.PopBurn xs devm devm')
    (burn : Devm.Burn devm' devm'') :
    Devm.PopBurn xs devm devm'' := by
  constructor
  · exact burn.stack ▸ popBurn.stack
  · exact Eq.trans popBurn.memory burn.memory
  · exact Nat.le_trans burn.gasLeft popBurn.gasLeft
  · exact Eq.trans popBurn.logs burn.logs
  · exact Eq.trans popBurn.refundCounter burn.refundCounter
  · exact Eq.trans popBurn.output burn.output
  · exact Eq.trans popBurn.accountsToDelete burn.accountsToDelete
  · exact Eq.trans popBurn.returnData burn.returnData
  · exact Eq.trans popBurn.error burn.error
  · exact Eq.trans popBurn.accessedAddresses burn.accessedAddresses
  · exact Eq.trans popBurn.accessedStorageKeys burn.accessedStorageKeys
  · exact Eq.trans popBurn.state burn.state
  · exact Eq.trans popBurn.createdAccounts burn.createdAccounts
  · exact Eq.trans popBurn.transientStorage burn.transientStorage




lemma table_suffix {c k pfx sfx} (h : pfx <++ (table k c) ++> sfx) :
    ∃ k' c', sfx = table k' c' := by
  induction c generalizing k pfx sfx with
  | nil => refine' ⟨k, [], (List.append_eq_nil_iff.mp h.symm).right⟩
  | cons p ps ih =>
    simp [table] at h
    rcases List.cons_eq_append_iff.mp h with
      ⟨_, h'⟩ | ⟨pfx', _, h'⟩
    · refine ⟨k, p :: ps, h'⟩
    · exact ih h'

lemma Func.length_compile {l k p bs} (h : Func.compile l k p = some bs) :
    bs.length = compsize p := by
  induction p generalizing k bs with
  | branch p q ihp ihq =>
    rcases of_bind_eq_some h with ⟨cp, h_cp, h'⟩; clear h
    rcases of_guard_eq_some h' with ⟨h'', h⟩; clear h' h''
    rcases of_bind_eq_some h with ⟨cq, h_cq, h'⟩; clear h
    simp at h'; rw [← h']
    simp [List.length_append, List.length, compsize]
    rw [ihp h_cp, ihq h_cq]; omega
  | last o => simp [compile] at h; rw [← h]; rfl
  | next o p ih =>
    rcases of_bind_eq_some h with ⟨bs', h, h'⟩;
    simp at h'; rw [← h']
    simp [List.length_append, compsize]
    rw [ih h, Nat.add_comm]
  | call m =>
    rcases of_bind_eq_some h with ⟨⟨_, _⟩, _, h'⟩; clear h
    rcases of_guard_eq_some h' with ⟨h'', h⟩; clear h' h''
    simp at h; rw [← h];
    simp [List.length, compsize]

lemma of_get?_table_eq_some {f fs} {bs} {m n : ℕ} {p : Func}
    (h_eq : some bs = Prog.compile ⟨f, fs⟩)
    (h_get : (table 0 (f :: fs))[m]? = some (n, p)) :
    ∃ lft rgt,
      lft.length = m ∧
      (lft <++ (table 0 (f :: fs)) ++> ((n, p) :: rgt)) ∧
    ∃ pfx sfx,
      pfx.length = n ∧
      (pfx <++ bs ++> sfx) ∧
      (some sfx = Table.compile (table 0 (f :: fs)) ((n, p) :: rgt)) := by
  revert n p h_get
  induction m with
  | zero =>
    intro n p h_get
    simp [table] at h_get
    cases h_get.left; cases h_get.right; clear h_get
    simp only [table]
    refine' ⟨ [], _ , rfl, List.nil_append _, [],
              bs, rfl, (List.nil_append _).symm, _ ⟩
    rw [h_eq]; simp [Prog.compile, table]
  | succ m ih =>
    intro n p h_get
    rcases List.of_get?_succ_eq_some h_get with ⟨⟨k, q⟩, h⟩
    rcases ih h with
      ⟨lft, rgt, h_lft, h_split, pfx, sfx, h_pfx, h_split', h_sfx⟩
    clear ih h
    refine' ⟨lft ++ [(k, q)], _⟩
    have h : ∃ rgt', rgt = (n, p) :: rgt' := by
      have h_sub : m.succ - m = 1 := by omega
      have h_le : List.length lft ≤ Nat.succ m := by
        rw [h_lft]; apply Nat.le_succ
      have heq : (lft ++ (k, q) :: rgt)[m.succ]? = ((k, q) :: rgt)[m.succ - lft.length]? := by
        simp [List.getElem?_append_right, h_le]
      rw [h_split, heq, h_lft, h_sub] at h_get
      match rgt with
      | [] => simp  at h_get
      | _ :: rgt' =>
        simp at h_get
        rw [h_get]; refine ⟨_, rfl⟩
    rcases h with ⟨rgt', h_rgt'⟩
    refine' ⟨rgt', _, _, _⟩
    · simp [List.length, h_lft]
    · simp [Split]; rw [← h_rgt', h_split]
    · rcases Table.compile_cons_eq_some h_sfx.symm with
        ⟨cq, cl, h_cq, h_cl, h_sfx'⟩
      refine' ⟨pfx ++ ([Jinst.jumpdest.toUInt8] ++ cq), cl, _, _, _⟩
      · have hn : n = k + compsize q + 1 := by
          rcases table_suffix h_split with
            ⟨k', _ | ⟨q', c'⟩, h⟩ <;> simp [table] at h
          rcases h with ⟨⟨⟨_⟩,⟨_⟩⟩, h⟩
          rw [h_rgt'] at h
          cases c' <;> simp [table] at h
          apply h.left.left
        simp [List.length_append, List.length]
        rw [h_pfx, hn, Func.length_compile h_cq]
        omega
      · simp only [Split]; rw [List.append_assoc, ← h_sfx', h_split']
      · rw [← h_cl, ← h_rgt']

lemma subcode_of_get?_eq_some {f fs} {code : ByteArray} {k loc : ℕ} {p : Func}
    (h_eq : some code.toList = Prog.compile ⟨f, fs⟩)
    (h_get : getElem? (table 0 (f :: fs)) k = some ⟨loc, p⟩) :
    Jinst.At code loc Jinst.jumpdest ∧
    subcode code.toList (loc + 1) (Func.compile (table 0 (f :: fs)) (loc + 1) p) := by
  rcases of_get?_table_eq_some h_eq h_get with
    ⟨lft, rgt, _, _, pfx, sfx, h_pfx, h_split', h_sfx⟩
  rcases Table.compile_cons_eq_some h_sfx.symm with ⟨bs, bs', h_bs, _, h_sfx'⟩
  have h_slice : List.Slice code.toList loc sfx := by
    rw [← h_pfx, h_split']; apply List.append_slice_suffix
  rw [h_sfx', List.append_assoc] at h_slice
  constructor
  · apply Jinst.at_of_slice
    apply List.slice_prefix h_slice
  · rw [h_bs]; simp [subcode]
    apply List.slice_prefix <| List.slice_suffix h_slice

lemma subcode_compile_call {code : ByteArray} {l m n}
  (h : subcode code.toList m (Func.compile l m (Func.call n))) :
    ∃ (loc : Nat) (p : Func),
      l[n]? = some (loc, p) ∧
      loc < 2 ^ 16 ∧
      PushAt code m ([(loc >>> 8).toUInt8, loc.toUInt8]) ∧
      Jinst.At code (m + 3) Jinst.jump := by
  rcases of_subcode h with ⟨cd, h', h_slice⟩; clear h
  rcases of_bind_eq_some h' with ⟨⟨loc, p⟩, h_get, h⟩; clear h'
  simp at h
  rcases of_guard_eq_some h with ⟨h_lt, h_eq⟩; clear h
  refine' ⟨loc, p, h_get, h_lt, _⟩
  simp at h_eq; rw [← h_eq] at h_slice
  have le : ([(loc >>> 8).toUInt8, loc.toUInt8] : Bytes).length ≤ 32 := by simp [List.length]
  have h_push_slice : List.Slice code.toList m
      (Ninst.toBytes (Ninst.push [(loc >>> 8).toUInt8, loc.toUInt8] le)) := by
    exact List.slice_prefix h_slice
  have h_jump_slice : List.Slice code.toList (m + 3) [Jinst.jump.toUInt8] := by
    have hh := @List.slice_suffix _ _ m [_, _, _] _ h_slice
    exact hh
  refine ⟨⟨le, Ninst.at_of_slice h_push_slice⟩, Jinst.at_of_slice h_jump_slice⟩

theorem correct_core (f : Func) (fs : List Func) :
    ∀ (pk : Exec.Deriv) (p : Func),
      some pk.sevm.code.toList = Prog.compile ⟨f, fs⟩ →
      subcode pk.sevm.code.toList pk.pc (Func.compile (table 0 (f :: fs)) pk.pc p) →
      Func.RunIfOk (f :: fs) pk.sevm pk.devm p pk.exn := by
  apply Exec.Deriv.strongRec; intro pk ih p h_eq sub
  rcases pk with ⟨pc, sevm, pre, exn, exc⟩
  simp only
  rcases exn with _ | post; {constructor}
  match p with
  | .last l =>
    exact Func.Run.last <| Linst.run_of_at exc <| Linst.at_of_slice sub
  | .next n p =>
    rcases of_subcode sub with ⟨cd, h_eq', h_slice⟩;
    rcases of_bind_eq_some h_eq' with ⟨cd', h_eq'', h_rw⟩; clear h_eq'
    simp [pure] at h_rw;
    rw [← h_rw] at h_slice;
    clear h_rw cd
    have h_at : Ninst.At sevm.code pc n := by
      apply Ninst.at_of_slice
      apply List.slice_prefix h_slice
    have bar' :
      ∃ inter exc',
        Run sevm pre n inter ∧
        ⟨pc + n.size, sevm, inter, .ok post, exc'⟩ ≺ ⟨pc, sevm, pre, .ok post, exc⟩ := by
      have bar := @Ninst.run_of_at pc sevm pre n post
      apply bar exc h_at
    rcases bar' with ⟨inter, exc', h_run, h_prec⟩
    apply @Func.Run.next (f :: fs) sevm pre n inter p post h_run
    have quz :
      subcode sevm.code.toList (pc + n.size)
        (Func.compile (table 0 (f :: fs)) (pc + n.size) p) := by
      rw [h_eq'']
      simp only [subcode]
      rw [Ninst.size_eq_length_toBytes]
      apply List.slice_suffix h_slice
    apply
      ih ⟨pc + n.size, sevm, inter, .ok post, exc'⟩
        (Exec.Deriv.lt_of_prec h_prec)
        p
        h_eq
        quz
  | .branch p q =>
    rcases subcode_compile_branch sub with
      ⟨loc, h_loc, pushAt, h_jumpi, h_scp, h_jumpdest, h_scq⟩
    have h :
        ∃ (devm' : Devm) (exc' : Exec (pc + 3) sevm devm' (.ok post)),
          Devm.PushBurn [Nat.toB256 loc] pre devm' ∧
          ⟨pc + 3, sevm, devm', .ok post, exc'⟩ ≺ ⟨pc, sevm, pre, .ok post, exc⟩ := by
      simp at pushAt
      rcases push_of_pushAt exc ⟨_, pushAt⟩ with ⟨s', cr', h, h_prec⟩
      rw [List.toB256_pair _ h_loc] at h
      refine' ⟨s', cr', h, h_prec⟩
    rcases h with ⟨devm', exc', pushBurn, h_prec⟩
    rcases jumpi_at exc' h_jumpi with
        ⟨x, devm'', exc'', popBurn, prec⟩
      | ⟨x, y, devm'', exc'', popBurn, jumpable, ne, prec⟩ <;> clear h_jumpi
    · clear h_scq h_jumpdest
      have h_pop' : Devm.PopBurn [0] pre devm'' := by
        rcases (Devm.pushBurn_cons_popBurn_cons pushBurn popBurn).right
          with ⟨st, pushBurn', popBurn'⟩
        apply Devm.popBurn_of_burn_of_popBurn _ popBurn'
        apply Devm.burn_of_pushBurn_nil pushBurn'
      apply Func.Run.zero h_pop'
      have h_lt :
          Exec.Deriv.lt
            ⟨pc + 4, sevm, devm'', .ok post, exc''⟩
            ⟨pc, sevm, pre, .ok post, exc⟩ := by
        refine' ⟨_, _, h_prec⟩;
        apply Exec.Deriv.le.step _ prec
        apply Exec.Deriv.le.refl _
      apply ih ⟨pc + 4, sevm, devm'', .ok post, exc''⟩ h_lt p h_eq h_scp
    · clear h_scp
      have h_loc' : loc < 2 ^ 256 := by
        apply Nat.lt_trans h_loc
        rw [Nat.pow_lt_pow_iff_right] <;> omega
      have h : x.toNat = loc ∧ Devm.PopBurn [y] pre devm'' := by
        rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn
          with ⟨hx, st, pushBurn', popBurn'⟩
        have h_loc_toNat : loc.toB256.toNat = loc := by
          rw [B256.toNat_toB256, Nat.lo_eq_of_lt h_loc']
        rw [← congrArg B256.toNat hx, h_loc_toNat]
        refine ⟨rfl, Devm.popBurn_of_burn_of_popBurn (Devm.burn_of_pushBurn_nil pushBurn') popBurn'⟩
      rcases h with ⟨hx, popBurn'⟩
      rw [← hx] at h_jumpdest
      rcases jumpdest_at exc'' h_jumpdest with ⟨inter_jd, exc_jd, burn_jd, prec_jd⟩
      have run : Func.Run (f :: fs) sevm inter_jd q post := by
        have h_lt : Exec.Deriv.lt ⟨x.toNat + 1, sevm, inter_jd, .ok post, exc_jd⟩ ⟨pc, sevm, pre, .ok post, exc⟩ := by
          refine' ⟨_, _, h_prec⟩
          apply Exec.Deriv.le.step _ prec
          apply Exec.Deriv.le.step _ prec_jd
          apply Exec.Deriv.le.refl _
        rw [← hx] at h_scq
        apply ih ⟨x.toNat + 1, sevm, inter_jd, .ok post, exc_jd⟩ h_lt q h_eq h_scq
      apply Func.Run.succ ne popBurn' burn_jd run
  | .call k =>
    rcases subcode_compile_call sub with ⟨loc, p, h_get, h_loc, pushAt, h_jump⟩
    have h_get' : (f :: fs)[k]? = some p := by
      rw [← @Prog.get?_table 0 k (f :: fs), h_get]; rfl
    have hd :
      ∃ (devm' : Devm) (exc' : Exec (pc + 3) sevm devm' (.ok post)),
        Devm.PushBurn [loc.toB256] pre devm' ∧
        ⟨pc + 3, sevm, devm', .ok post, exc'⟩ ≺ ⟨pc, sevm, pre, .ok post, exc⟩ := by
      rcases push_of_pushAt exc pushAt with ⟨inter, exc', h, h_prec⟩
      rw [List.toB256_pair _ h_loc] at h
      refine' ⟨inter, exc', h, h_prec⟩
    rcases hd with ⟨devm', exc', h_push, h_prec⟩
    rcases jump_at exc' h_jump with ⟨x, devm'', exc'', h_pop, h_jumpable, h_prec'⟩
    rcases subcode_of_get?_eq_some h_eq h_get with ⟨h_jd, hp⟩; clear h_get
    have h_loc' : loc < 2 ^ 256 := by
      apply Nat.lt_trans h_loc
      rw [Nat.pow_lt_pow_iff_right] <;> omega
    have h_rw : loc = x.toNat ∧ Devm.Burn pre devm'' := by
      rcases Devm.pushBurn_cons_popBurn_cons h_push h_pop with ⟨hx, st, pushBurn', popBurn'⟩
      have h_loc_toNat : loc.toB256.toNat = loc := by
        rw [B256.toNat_toB256_of_lt h_loc']
      rw [← congrArg B256.toNat hx, h_loc_toNat]
      have b1 := Devm.burn_of_pushBurn_nil pushBurn'
      have b2 := Devm.burn_of_popBurn_nil popBurn'
      refine ⟨rfl, Devm.burn_trans b1 b2⟩
    rcases h_rw with ⟨h_rw, h_burn⟩
    rw [h_rw] at h_jd
    rcases jumpdest_at exc'' h_jd with ⟨inter_jd, exc''', burn_jd, h_prec''⟩
    rw [h_rw] at hp
    have h_lt : Exec.Deriv.lt ⟨x.toNat + 1, sevm, inter_jd, .ok post, exc'''⟩ ⟨pc, sevm, pre, .ok post, exc⟩ := by
      refine' ⟨_, _, h_prec⟩
      apply Exec.Deriv.le.step _ h_prec'
      apply Exec.Deriv.le.step _ h_prec''
      apply Exec.Deriv.le.refl _
    have run : Func.Run (f :: fs) sevm inter_jd p post := by
      apply ih ⟨x.toNat + 1, sevm, inter_jd, .ok post, exc'''⟩ h_lt p h_eq hp
    exact Func.Run.call h_get' (Devm.burn_trans h_burn burn_jd) run

theorem correct (sevm : Sevm) (pre : Devm) (p : Prog) (post : Devm)
    (exc : Exec 0 sevm pre (.ok post))
    (eq : some sevm.code.toList = p.compile) :
    Prog.Run sevm pre p post := by
  rcases @subcode_of_get?_eq_some p.main p.aux sevm.code 0 _ p.main eq rfl
    with ⟨h_at, h_sub⟩
  rcases jumpdest_at exc h_at with ⟨inter, exc', burn, prec⟩;
  apply @Func.Run.call (p.main :: p.aux) sevm pre inter 0 p.main post rfl burn
  apply correct_core p.main p.aux ⟨1, sevm, inter, .ok post, exc'⟩ p.main eq h_sub

def String.toBytes (s : String) : Bytes := s.toList.map Char.toUInt8
def String.keccak (s : String) : B256 := (String.toBytes s).keccak

-- The ABI argument types this file can name in a signature string.
--
-- All but the last are *static*: each occupies exactly one 32-byte calldata
-- word, which is the stride `arg` and `argCopy` assume, so for those the type
-- being nameable and the type being readable coincide.
--
-- `dynBytes` — the dynamic `bytes` of `flashLoan(address,address,uint256,bytes)`
-- and `onFlashLoan(address,address,uint256,uint256,bytes)` — is the one
-- exception, and the distinction it introduces is worth stating rather than
-- inferring. Admitting it here says only that a signature string may contain
-- the word `bytes`; it does NOT say `arg` can decode such an argument, and
-- `arg` still cannot. A dynamic argument's head word is an *offset* into a
-- tail, so `arg k` on it yields the offset, not the value: following that
-- offset to the length word and copying the payload is separate work the
-- contract does explicitly (`calldatacopy`). Naming the type and decoding it
-- are two different capabilities, and only the first is added here.
--
-- Still absent, for the same reason as before: `string`, arrays, and tuples
-- containing them. Nothing in Blanc needs to name one yet, and adding a
-- constructor per unimplemented type would misrepresent this list as an ABI
-- model.
--
-- Note the name. `bytes (size : Nat)` is the *fixed-size* family and keeps its
-- `bytes1 … bytes32` rendering untouched; the dynamic type is a different ABI
-- type that happens to be spelled with the same word, so it gets its own
-- constructor rather than a sentinel size. Because this is a new constructor
-- and no existing case's rendering moves, no existing signature string — and
-- so no existing selector or event topic — can change. The WETH selector
-- regeneration tripwire checks exactly that.
inductive ArgType
  | address
  | bool
  | uint (bits : Nat)   -- uint8 … uint256, `bits` a multiple of 8
  | int (bits : Nat)    -- int8 … int256
  | bytes (size : Nat)  -- bytes1 … bytes32, the fixed-size family only
  | dynBytes            -- the dynamic `bytes`; nameable, not `arg`-decodable

def ArgType.toString : ArgType → String
  | address => "address"
  | bool => "bool"
  | uint bits => s!"uint{bits}"
  | int bits => s!"int{bits}"
  | bytes size => s!"bytes{size}"
  | dynBytes => "bytes"

-- The overwhelmingly common width, so call sites can write `.uint256`.
abbrev ArgType.uint256 : ArgType := .uint 256

def selectorArgs : List ArgType → String
  | [] => ""
  | t :: ts => List.foldl (λ s t' => s!"{s},{t'.toString}") t.toString ts

-- The keccak of an ABI signature string, e.g. "transfer(address,uint256)".
-- Both of the words a contract derives from a signature are projections of
-- this one hash: an event's topic0 is the hash itself, and a function
-- selector is its top four bytes.
def signatureHash (name : String) (args : List ArgType) : B256 :=
  Blanc.String.keccak s!"{name}({selectorArgs args})"

def selector (name : String) (args : List ArgType) : B256 :=
  (signatureHash name args).shiftRight 224

def isMax : Line := [not, iszero]

inductive DispatchTree : Type
  | leaf : B256 → Func → DispatchTree
  | fork : DispatchTree → DispatchTree → DispatchTree

open DispatchTree

def DispatchTree.mem : DispatchTree → (B256 × Func) → Prop
  | (leaf w p), wp => wp = (w, p)
  | (fork tl tr), wp => DispatchTree.mem tl wp ∨ DispatchTree.mem tr wp

instance : Membership (B256 × Func) DispatchTree := ⟨DispatchTree.mem⟩

def leftmostFsig : DispatchTree → B256
  | (DispatchTree.leaf w _) => w
  | (DispatchTree.fork t _) => leftmostFsig t

-- Is this list of (signature, function) pairs in strictly ascending signature
-- order? This is assumption (2) of `dispatchWith` below, as a decidable check
-- rather than a comment: `#guard` it, or state it as a theorem closed by
-- `decide +kernel`, and a misordered entry becomes a build failure instead of
-- a silently unreachable function.
def DispatchTree.sorted : List (B256 × Func) → Bool
  | [] => true
  | [_] => true
  | x :: y :: ys => decide (x.fst < y.fst) && sorted (y :: ys)

-- Build a balanced tree from a list, splitting every fork at ⌈n/2⌉ so the left
-- subtree is never smaller than the right. The `Nat` is structural fuel;
-- `ofSorted` passes the list's length, which always suffices. The two
-- degenerate rows are unreachable from `ofSorted` on a nonempty list.
--
-- Note that this compares nothing: the shape comes from `List.take`/`drop` and
-- `List.length` alone. That is deliberate. A version that sorted the list here
-- reduces fine in the kernel, but forces every signature word — and so every
-- `String.keccak` behind a `selector` call — during `whnf` in the *elaborator*,
-- which blows `maxRecDepth` in any downstream proof that has to case on the
-- resulting tree. Keeping the comparisons in `sorted` leaves the leaves opaque.
def DispatchTree.build : Nat → List (B256 × Func) → DispatchTree
  | _, [] => leaf 0 .rev
  | _, [(w, p)] => leaf w p
  | 0, (x :: _ :: _) => leaf x.fst x.snd
  | n + 1, xs =>
    fork (build n (xs.take ((xs.length + 1) / 2)))
         (build n (xs.drop ((xs.length + 1) / 2)))

-- Assemble a dispatch tree from a list of (signature, function) pairs given in
-- ascending signature order — pair it with `sorted` to check that order.
--
-- Together they retire the hand-written tree shape. `dispatchWith`'s binary
-- search needs the leaves laid out so that every fork's right subtree holds
-- strictly larger signatures; writing that nesting out by hand means a
-- maintainer can put a leaf in the wrong subtree, and `dispatchWith` will
-- compile it into a program where that function is simply unreachable.
def DispatchTree.ofSorted (xs : List (B256 × Func)) : DispatchTree :=
  build xs.length xs

-- given a dispatch tree of functions and their signatures, construct the main program.
-- note it assumes that:
-- (1) the calldata function selector is already at the top of the stack (i.e, it has to be preceded by 'fsig').
-- (2) the functions are ordered in ascending order of their signatures (right is higher)

def dispatchWith (k : Nat) : DispatchTree → Func
  | DispatchTree.leaf w p => pushB256 w ::: eq ::: (p <?> .call k)
  | DispatchTree.fork tl tr =>
    dup 0 :::
    pushB256 (leftmostFsig tr) ::: gt :::
    (dispatchWith k tl <?> dispatchWith k tr)

def dispatch : DispatchTree → Func
  | DispatchTree.leaf w p => pushB256 w ::: eq ::: (p <?> .rev)
  | DispatchTree.fork tl tr =>
    dup 0 :::
    pushB256 (leftmostFsig tr) ::: gt :::
    (dispatch tl <?> dispatch tr)

def shiftRight (w : B256) : Line := [pushB256 w, shr]

-- load the calldata function selector: the first 4 bytes of calldata,
-- right-aligned in a word. This is what 'dispatch'/'dispatchWith' assume
-- has already run (assumption (1) above).
def fsig : Line := cdl 0 ++ shiftRight 224

def Func.main (dt : DispatchTree) : Func := fsig +++ dispatch dt
def Func.mainWith (k : Nat) (dt : DispatchTree) : Func := fsig +++ dispatchWith k dt

/-! ## The shared ERC-20 surface

Fourteen definitions that two contracts build the same way, and that neither
contract owns. They arrived here by the route README.md's *Module hierarchy:
contracts are siblings* prescribes and `balSum` walked first: WETH defined them,
fmint reproduced them verbatim inside `namespace Fmint`, and a property layer
that needed to speak about both would have had to import across the sibling
boundary. So they move up, to the layer both contracts already import, and both
now reference one constant.

The set is exactly the definitions that were `rfl`-equal across the two
contracts *and* whose dependencies were too — the second clause is not
redundant. `approve` and `transferFrom` are byte-identical in both sources and
are **not** here, because they call `prepApprove` and `updateAllowance`, which
fork on fmint's extended allowance-slot guard. Neither are `name`, `symbol` or
`totalSupply`, which differ by content. Those seven stay in their contracts, and
a name that exists in both namespaces with different content must never be
deleted from one: inside `namespace Fmint` the bare name would then resolve here
and still elaborate, silently re-pointing fmint at WETH's code. The compile
witnesses `Blanc.wethCode_compile` and `Blanc.fmintCode_compile` are what catch
that.

Names are unchanged by the move. `transfer` claims no contract, so the README's
rename clause — the one that turned `wbsum` into `balSum` — does not fire.

`Blanc/CommonProofs.lean` carries the lemma half of the same hoist. -/

/-! ### Event topics

A topic0 word is the keccak of the event's ABI signature string — the same
`signatureHash` a function selector is built from, without the shift that
narrows one to four bytes. Spelling these as signature strings inlined at the
log sites is how the same event ends up with two spellings and, one typo later,
two topics.

ERC-20's two events are here; WETH's `Deposit` and `Withdrawal` are its own and
stay in `Blanc/Weth.lean`. -/

def approvalEvent : B256 := signatureHash "Approval" [.address, .address, .uint256]
def transferEvent : B256 := signatureHash "Transfer" [.address, .address, .uint256]

/-! ### The read-only surface -/

-- decimals() --

def decimals : Func :=
  pushB256 0x12 ::: -- 0x12 ||
  mstoreAt 0 +++ -- || 0x12
  returnMemoryRange 0 32

-- balanceOf(address guy) --

def balanceOf : Func :=
  arg 0 +++ -- guy ||
  sload ::: -- guy_bal ||
  mstoreAt 0 +++ -- || guy_bal
  returnMemoryRange 0 32

-- allowance(address src, address dst) --

def allowance : Func :=
  argCopy 0 0 2 +++ -- || src dst
  pushList [64, 0] +++ -- 0 :: 64 || src dst
  kec ::: -- hash ||
  sload ::: -- allowAmnt ||
  mstoreAt 0 +++ -- || allow_amnt
  returnMemoryRange 0 32

/-! ### Log fragments -/

-- assumes : args = [guy, wad]
def logApprove : Line :=
  argCopy 0 1 1 ++ -- || wad
  arg 0 ++ caller ::
  pushB256 approvalEvent :: -- approvalEventSig :: caller :: guy || wad
  logWith 2 0 1 -- 2 indexed topics : caller address, approvee address
                -- 1 unindexed data : approval value

-- assumes : args = [dst, wad]
def logTransfer : Line :=
  argCopy 0 1 1 ++ -- || wad
  arg 0 ++ caller ::
  pushB256 transferEvent :: -- transferEventSig :: src :: dst || wad
  logWith 2 0 1 -- 2 indexed topics : source address, destination address
                -- 1 unindexed data : transfer value

-- ( dst :: wad :: src -- wad :: src )
def transferFromLog : Line :=
  dup 2 :: -- src :: dst :: wad :: src
  pushB256 transferEvent :: -- transferEventSig :: src :: dst :: wad :: src
  dup 3 :: mstoreAt 0 ++ -- transferEventSig :: src :: dst :: wad :: src || wad
  logWith 2 0 1 -- [Transfer(src,dst,wad) is logged]
                -- wad :: src

/-! ### transfer(address dst, uint wad) and its fragments -/

-- ( wad dst -- )
def incrWbal : Line :=
  dup 1 :: -- dst :: wad :: dst
  sload :: -- dst_bal :: wad :: dst
  add :: -- (dst_bal + wad) :: dst
  swap 0 :: -- dst :: (dst_bal + wad)
  sstore :: []

-- assumes : arg = [dst, wad]
-- ( -- dst_invalid :: dst )
def transferTestDst : Line :=
  arg 0 ++ dup 0 :: -- dst :: dst
  checkNonAddress -- dst_invalid :: dst

-- assumes : arg = [_, wad]
-- ( -- caller_bal_<_wad? caller_bal wad wad )
def transferTestLt : Line :=
  arg 1 ++ -- wad :: dst
  caller :: -- caller :: wad :: dst
  dup 0 :: -- caller :: caller :: wad :: dst
  sload :: -- caller_bal :: caller :: wad :: dst
  swap 0 :: -- caller :: caller_bal :: wad :: dst
  dup 2 :: -- wad :: caller :: caller_bal :: wad :: dst
  dup 0 :: -- wad :: wad :: caller :: caller_bal :: wad :: dst
  dup 3 :: -- caller_bal :: wad :: wad :: caller :: caller_bal :: wad :: dst
  sub ::   -- caller_bal - wad :: wad :: caller :: caller_bal :: wad :: dst
  swap 2 :: -- caller_bal :: wad :: caller :: caller_bal - wad :: wad :: dst
  lt :: [] -- caller_bal_<_wad? :: caller :: caller_bal - wad :: wad :: dst

-- ( caller :: caller_bal - wad :: wad :: dst -- * )
def transferCore : Func :=
  sstore ::: -- wad :: dst [caller balance up to date]
  incrWbal +++ -- [destination balance up todate]
  logTransfer +++
  returnTrue

-- assumes : arg = [dst, wad]
def transfer : Func :=
  transferTestDst +++ -- dst_invalid? :: dst
  .rev <?> -- [if dst is not a valid address, revert]
           -- dst
  transferTestLt +++ -- (caller_bal < wad) :: caller :: caller_bal - wad :: wad :: dst
  .rev <?> -- [if caller balance < transfer amount, revert]
        -- caller :: caller_bal - wad :: wad :: dst
  transferCore

/-! ### transferFrom's shared fragment -/

-- ( sbal :: wad :: wad :: src -- wad :: src )
def transferFromUpdateSbal : Line :=
  sub :: -- (sbal - wad) :: wad :: src
  dup 2 :: -- src :: (sbal - wad) :: wad :: src
  sstore :: -- [source balance is up to date]
  []        -- wad :: src

end Blanc
