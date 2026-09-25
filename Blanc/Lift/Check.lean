import Blanc.Lift.Transfer

/-!
# Lift certificates and their checker

A certificate is a list of entries, each a program counter, the abstract frame
the code there runs with, the number of words its function leaves when it
returns, and the synthetic tree for the code from that program counter.  The
trees are the synthetic program; `Cert.check` validates all of them against
the bytes in one decidable pass, and `Blanc/Lift/Sound.lean` turns a successful
check into the lifting theorem.

**Frames.**  An abstract frame describes the operand-stack words above the
current function's base, top first.  A word is a known constant, the current
function's own return address (`ret`), or unknown.  Everything below the base
belongs to callers and is never read: an instruction that needs more words than
the frame holds fails the check.

**Calls.**  A `callNext k f` site jumps to entry `k` whose declared frame is a
prefix of the caller's frame.  Wherever the callee's frame says `ret`, the
caller's word must be one and the same constant: the program counter of the
continuation `f`.  When the callee returns it leaves exactly `rets` words, so
the continuation runs with that many unknown words on top of the caller's
remaining frame.

The checker is untrusted-input tolerant: any tree, frame or entry list that
does not describe the bytes is rejected, never believed.
-/

namespace Blanc.Lift

open Jaune AbstractStackSafety

inductive AVal : Type
  | const : B256 → AVal
  | ret : AVal
  | unk : AVal
deriving DecidableEq

structure Entry : Type where
  pc : Nat
  frame : List AVal
  rets : Nat
deriving DecidableEq

/-- The byte at `pc`, if any.  Both byte readers go through `code.data.toList`,
a projection, rather than `ByteArray.toList`, whose index loop is quadratic
under kernel reduction (`ByteArray.toList_eq_toList_data` relates them). -/
def byteAt (code : ByteArray) (pc : Nat) : Option UInt8 := code.data.toList[pc]?

/-- The bytes at `pc` begin with `bs`. -/
def bytesAt (code : ByteArray) (pc : Nat) (bs : Bytes) : Bool :=
  decide ((code.data.toList.drop pc).take bs.length = bs)

/-- Index labels `0, 1, …` for a frame of length `k`. -/
def indexPattern (k : Nat) : Pattern :=
  (List.range k).map fun i => some (Nat.toB256 i)

/-- Read one transferred index label back into the frame. -/
def readBack (frame : List AVal) : Option B256 → Option AVal
  | none => some .unk
  | some i => frame[i.toNat]?

/-- The abstract effect of one non-jump instruction on a frame.  Frames longer
than the EVM's 1024-word stack are rejected: beyond that, index labels would
alias modulo `2 ^ 256`. -/
def absNinst (n : Ninst) (frame : List AVal) : Option (List AVal) :=
  match n with
  | .push bs _ => some (.const (Bytes.toB256 bs) :: frame)
  | n => do
    guard (frame.length ≤ 1024)
    let out ← ninstTransfer n (indexPattern frame.length)
    out.mapM (readBack frame)

/-- A goto target's declared frame admits the current frame. -/
def gotoCompat : List AVal → List AVal → Bool
  | [], [] => true
  | _ :: a, .unk :: e => gotoCompat a e
  | .const c :: a, .const c' :: e => c == c' && gotoCompat a e
  | .ret :: a, .ret :: e => gotoCompat a e
  | _, _ => false

/-- A callee's declared frame admits the top of the caller's frame, with every
`ret` position holding the continuation address `t`. -/
def callCompat (t : B256) : List AVal → List AVal → Bool
  | _, [] => true
  | _ :: a, .unk :: e => callCompat t a e
  | .const c :: a, .const c' :: e => c == c' && callCompat t a e
  | .const c :: a, .ret :: e => c == t && callCompat t a e
  | _, _ => false

def checkNode (code : ByteArray) (es : List Entry) (m : Nat) :
    Nat → List AVal → SFunc → Bool
  | pc, a, .next n f =>
    bytesAt code pc (Ninst.toBytes n) && Ninst.pcFree n &&
      match absNinst n a with
      | some a' => checkNode code es m (pc + n.size) a' f
      | none => false
  | pc, _, .last l => byteAt code pc == some l.toUInt8
  | pc, a, .dest f =>
    byteAt code pc == some (Jinst.toUInt8 .jumpdest) && checkNode code es m (pc + 1) a f
  | pc, a, .branch f g =>
    match a with
    | .const t :: _ :: a' =>
      byteAt code pc == some (Jinst.toUInt8 .jumpi) &&
        checkNode code es m (pc + 1) a' f && checkNode code es m t.toNat a' g
    | _ => false
  | pc, a, .branchTo f k =>
    match a, es[k]? with
    | .const t :: _ :: a', some e =>
      byteAt code pc == some (Jinst.toUInt8 .jumpi) && e.pc == t.toNat &&
        e.rets == m && gotoCompat a' e.frame && checkNode code es m (pc + 1) a' f
    | _, _ => false
  | pc, a, .jump k =>
    match a, es[k]? with
    | .const t :: a', some e =>
      byteAt code pc == some (Jinst.toUInt8 .jump) && e.pc == t.toNat &&
        e.rets == m && gotoCompat a' e.frame
    | _, _ => false
  | pc, a, .callNext k f =>
    match a, f, es[k]? with
    | .const t :: a', .dest _, some e =>
      byteAt code pc == some (Jinst.toUInt8 .jump) && e.pc == t.toNat &&
        decide (e.frame.length ≤ a'.length) &&
        (match e.frame.findIdx? (· == .ret) with
         | some i =>
           match a'[i]? with
           | some (.const r) =>
             callCompat r a' e.frame &&
               checkNode code es m r.toNat
                 (List.replicate e.rets .unk ++ a'.drop e.frame.length) f
           | _ => false
         | none => callCompat 0 a' e.frame)
    | _, _, _ => false
  | pc, a, .ret =>
    match a with
    | .ret :: a' => byteAt code pc == some (Jinst.toUInt8 .jump) && a'.length == m
    | _ => false
  | pc, _, .undefined => (code.getInst pc).isNone

/-- A lift certificate: entry `0` is the frame's start at pc `0` with an empty
frame, and every entry's tree checks against the bytes. -/
def Cert : Type := List (Entry × SFunc)

def Cert.entries (c : Cert) : List Entry := List.map Prod.fst c
def Cert.prog (c : Cert) : List SFunc := List.map Prod.snd c

def Cert.check (code : ByteArray) (c : Cert) : Bool :=
  (match c with
   | (e, _) :: _ => e.pc == 0 && e.frame == []
   | [] => false) &&
    c.all fun (e, f) => checkNode code c.entries e.rets e.pc e.frame f

end Blanc.Lift
