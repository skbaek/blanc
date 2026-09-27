import Blanc.Lift.Check

/-!
# The certificate checker with a constant memory map

`checkNodeM` is `checkNode` (`Blanc/Lift/Check.lean`) carrying, beside the
abstract frame, a `MemMap`: abstract words at fixed memory offsets.  With the
flag `b` off it is `checkNode` exactly (`checkNode_eq_checkNodeM`), so every
certificate checked by `Cert.check` is checked by `Cert.checkM` with `b = false`
and no maps, and the soundness proofs are stated once, over `checkNodeM`.

With `b` on:

* `MSTORE` at a constant offset records its value, `CALLDATACOPY` over a
  constant window forgets the words it overlaps, the instructions of
  `ninstMemKeeps` keep the map, and every other instruction forgets it
  (`absMem`);
* `MLOAD` at a recorded constant offset pushes the recorded word (`memTop`);
* a goto (`jump`, the taken side of `branchTo`) requires the target entry's
  declared map to be recorded identically (`memCompat`);
* a callee entry declares the empty map, and a `callNext` continuation starts
  from it: nothing is known about memory a callee may have written.

The per-instruction facts are in `Blanc/Lift/MemMap.lean`.
-/

namespace Blanc.Lift

open Jaune

/-- Abstract words at fixed memory offsets. -/
abbrev MemMap : Type := List (Nat × AVal)

/-- Forget every word overlapping the window `[lo, hi)`. -/
def memKill (mem : MemMap) (lo hi : Nat) : MemMap :=
  mem.filter fun p => decide (p.1 + 32 ≤ lo) || decide (hi ≤ p.1)

/-- Regular instructions whose successful step leaves every memory byte as it
was and never shrinks the logical size (a read may extend it). -/
def rinstMemKeeps : Rinst → Bool
  | .add | .mul | .sub | .div | .sdiv | .mod | .smod | .signextend | .lt | .gt | .slt
  | .sgt | .eq | .and | .or | .xor | .byte | .shl | .shr | .sar | .iszero | .not
  | .address | .origin | .caller | .callvalue | .calldatasize | .codesize | .gasprice
  | .returndatasize | .coinbase | .timestamp | .number | .prevrandao | .gaslimit | .chainid
  | .basefee | .blobbasefee | .msize
  | .pop | .calldataload | .mload | .keccak256 | .dup _ | .swap _
  | .sload | .sstore | .tload | .tstore | .log _ => true
  | _ => false

/-- Every `PUSH`, and the regular instructions of `rinstMemKeeps`. -/
def ninstMemKeeps : Ninst → Bool
  | .push _ _ => true
  | .reg r => rinstMemKeeps r
  | _ => false

/-- The map after one instruction. -/
def absMem (n : Ninst) (a : List AVal) (mem : MemMap) : MemMap :=
  match n, a with
  | .reg .mstore, .const o :: v :: _ => (o.toNat, v) :: memKill mem o.toNat (o.toNat + 32)
  | .reg .calldatacopy, .const d :: _ :: .const z :: _ =>
    memKill mem d.toNat (d.toNat + z.toNat)
  | n, _ => if ninstMemKeeps n then mem else []

/-- The word an `MLOAD` at a constant offset reads, when the map records it. -/
def memTop (n : Ninst) (a : List AVal) (mem : MemMap) : Option AVal :=
  match n, a with
  | .reg .mload, .const o :: _ => mem.lookup o.toNat
  | _, _ => none

/-- Replace the top of a transferred frame by a recorded `MLOAD` result. -/
def memFold : Option AVal → List AVal → List AVal
  | some v, _ :: a => v :: a
  | _, a => a

/-- Every word the declared map records, the current map records identically. -/
def memCompat (cur decl : MemMap) : Bool :=
  decl.all fun p => cur.lookup p.1 == some p.2

/-- `checkNode` with a memory map, which it tracks when `b` is on. -/
def checkNodeM (code : ByteArray) (es : List Entry) (ms : List MemMap) (b : Bool) (m : Nat) :
    Nat → List AVal → MemMap → SFunc → Bool
  | pc, a, μ, .next n f =>
    bytesAt code pc (Ninst.toBytes n) && Ninst.pcFree n &&
      match absNinst n a with
      | some a' =>
        checkNodeM code es ms b m (pc + n.size) (if b then memFold (memTop n a μ) a' else a')
          (if b then absMem n a μ else []) f
      | none => false
  | pc, _, _, .last l => byteAt code pc == some l.toUInt8
  | pc, a, μ, .dest f =>
    byteAt code pc == some (Jinst.toUInt8 .jumpdest) && checkNodeM code es ms b m (pc + 1) a μ f
  | pc, a, μ, .branch f g =>
    match a with
    | .const t :: v :: a' =>
      byteAt code pc == some (Jinst.toUInt8 .jumpi) &&
        (v.jumps? == some true || checkNodeM code es ms b m (pc + 1) a' μ f) &&
        (v.jumps? == some false || checkNodeM code es ms b m t.toNat a' μ g)
    | _ => false
  | pc, a, μ, .branchTo f k =>
    match a, es[k]? with
    | .const t :: v :: a', some e =>
      byteAt code pc == some (Jinst.toUInt8 .jumpi) && e.pc == t.toNat &&
        e.rets == m && gotoCompat a' e.frame && memCompat μ (ms.getD k []) &&
        (v.jumps? == some true || checkNodeM code es ms b m (pc + 1) a' μ f)
    | _, _ => false
  | pc, a, μ, .jump k =>
    match a, es[k]? with
    | .const t :: a', some e =>
      byteAt code pc == some (Jinst.toUInt8 .jump) && e.pc == t.toNat &&
        e.rets == m && gotoCompat a' e.frame && memCompat μ (ms.getD k [])
    | _, _ => false
  | pc, a, _, .callNext k f =>
    match a, f, es[k]? with
    | .const t :: a', .dest _, some e =>
      byteAt code pc == some (Jinst.toUInt8 .jump) && e.pc == t.toNat &&
        decide (e.frame.length ≤ a'.length) && (ms.getD k []).isEmpty &&
        (match e.frame.findIdx? (· == .ret) with
         | some i =>
           match a'[i]? with
           | some (.const r) =>
             callCompat r a' e.frame &&
               checkNodeM code es ms b m r.toNat
                 (List.replicate e.rets .unk ++ a'.drop e.frame.length) [] f
           | _ => false
         | none => callCompat 0 a' e.frame)
    | _, _, _ => false
  | pc, a, _, .ret =>
    match a with
    | .ret :: a' => byteAt code pc == some (Jinst.toUInt8 .jump) && a'.length == m
    | _ => false
  | pc, a, μ, .pcAt p f =>
    bytesAt code pc (Ninst.toBytes (.reg .pc)) && p == pc &&
      checkNodeM code es ms b m (pc + 1) (.const (Nat.toB256 pc) :: a) μ f
  | pc, _, _, .undefined => (code.getInst pc).isNone

/-- Every entry, `k`-th, checks from its declared map `ms[k]` (default empty). -/
def Cert.checkEntriesM (code : ByteArray) (es : List Entry) (ms : List MemMap) (b : Bool) :
    Nat → Cert → Bool
  | _, [] => true
  | k, (e, f) :: c =>
    checkNodeM code es ms b e.rets e.pc e.frame (ms.getD k []) f &&
      Cert.checkEntriesM code es ms b (k + 1) c

/-- A memory-tracking lift certificate: `Cert.check`'s entry-`0` conditions,
entry `0` declaring no memory, and every entry checking from its map. -/
def Cert.checkM (code : ByteArray) (c : Cert) (ms : List MemMap) (b : Bool) : Bool :=
  (match c with
   | (e, _) :: _ => e.pc == 0 && e.frame == []
   | [] => false) &&
    (ms.getD 0 []).isEmpty && Cert.checkEntriesM code c.entries ms b 0 c

/-- With tracking off and no maps, `checkNodeM` is `checkNode`. -/
theorem checkNode_eq_checkNodeM (code : ByteArray) (es : List Entry) (m : Nat)
    (f : SFunc) (pc : Nat) (a : List AVal) :
    checkNode code es m pc a f = checkNodeM code es [] false m pc a [] f := by
  let Q : SFunc → Prop := fun f =>
    ∀ (pc : Nat) (a : List AVal), checkNode code es m pc a f = checkNodeM code es [] false m pc a [] f
  let P : SFunc → Prop := fun f =>
    Q f ∧ match f with
    | .dest g => Q g
    | _ => True
  have hall : ∀ f : SFunc, P f := by
    intro f
    induction f with
    | next n f ih =>
      refine ⟨fun pc a => ?_, by simp [P]⟩
      cases h : absNinst n a <;> simp [Q, checkNode, checkNodeM, h, ih.1]
    | last l => exact ⟨fun pc a => by simp [Q, checkNode, checkNodeM], by simp [P]⟩
    | dest f ih => exact ⟨fun pc a => by simp [Q, checkNode, checkNodeM, ih.1], ih.1⟩
    | branch f g ihf ihg =>
      refine ⟨fun pc a => ?_, by simp [P]⟩
      rcases a with _ | ⟨_ | _ | _, _ | ⟨_, a⟩⟩ <;> simp [Q, checkNode, checkNodeM, ihf.1, ihg.1]
    | branchTo f k ih =>
      refine ⟨fun pc a => ?_, by simp [P]⟩
      rcases a with _ | ⟨_ | _ | _, _ | ⟨_, a⟩⟩ <;> cases h : es[k]? <;>
        simp [Q, checkNode, checkNodeM, ih.1, memCompat, h]
    | jump k =>
      refine ⟨fun pc a => ?_, by simp [P]⟩
      rcases a with _ | ⟨_ | _ | _, a⟩ <;> cases h : es[k]? <;>
        simp [Q, checkNode, checkNodeM, memCompat, h]
    | callNext k f ih =>
      refine ⟨fun pc a => ?_, by simp [P]⟩
      rcases a with _ | ⟨_ | _ | _, a⟩ <;> cases f <;> cases h : es[k]? <;>
        simp [Q, checkNode, checkNodeM, ih.1, ih.2, h] <;> rfl
    | ret => exact ⟨fun pc a => by rcases a with _ | ⟨_ | _ | _, a⟩ <;> simp [Q, checkNode, checkNodeM],
        by simp [P]⟩
    | pcAt p f ih =>
      exact ⟨fun pc a => by simp [Q, checkNode, checkNodeM, ih.1], by simp [P]⟩
    | undefined => exact ⟨fun pc a => by simp [Q, checkNode, checkNodeM], by simp [P]⟩
  exact (hall f).1 pc a

end Blanc.Lift
