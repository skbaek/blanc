-- Basic.lean : generic definitions and lemmas (e.g. for Booleans, lists,
-- bit vectors and bytes) that are useful for but not specific to Blanc

import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Lemmas
-- import Mathlib.Util.Notation3
-- import Mathlib.Data.Vector.Basic

instance : @Zero Bool := ⟨false⟩
instance : @One Bool := ⟨true⟩

abbrev B8 : Type := UInt8
abbrev B16 : Type := UInt16
abbrev B32 : Type := UInt32
abbrev B64 : Type := UInt64
abbrev B8L : Type := List B8
abbrev B8A : Type := Array B8

def B8.highBit (x : B8) : Bool := (x &&& 0x80) != 0
def B8.lowBit (x : B8) : Bool := (x &&& 0x01) != 0

def B16.highBit (x : B16) : Bool := (x &&& 0x8000) != 0
def B16.lowBit  (x : B16) : Bool := (x &&& 0x0001) != 0

def B32.highBit (x : B32) : Bool := (x &&& 0x80000000) != 0
def B32.lowBit  (x : B32) : Bool := (x &&& 0x00000001) != 0

def B64.highBit (x : B64) : Bool := (x &&& 0x8000000000000000) != 0
def B64.lowBit  (x : B64) : Bool := (x &&& 0x0000000000000001) != 0

def B128 : Type := B64 × B64
deriving DecidableEq

instance : Inhabited B128 := ⟨⟨0, 0⟩⟩

def B256 : Type := B128 × B128
deriving DecidableEq

instance : Inhabited B256 := ⟨⟨Inhabited.default, Inhabited.default⟩⟩

def B128.highBit (x : B128) : Bool := x.1.highBit
def B128.lowBit  (x : B128) : Bool := x.2.lowBit

def B256.highBit (x : B256) : Bool := x.1.highBit
def B256.lowBit  (x : B256) : Bool := x.2.lowBit

instance : HAppend B64 B64 B128 := ⟨λ xs ys => ⟨xs, ys⟩⟩
instance : HAppend B128 B128 B256 := ⟨λ xs ys => ⟨xs, ys⟩⟩

def B64.max : B64 := 0xFFFFFFFFFFFFFFFF
def B128.max : B128 := (.max : B64) ++ (.max : B64)
def B256.max : B256 := (.max : B128) ++ (.max : B128)

instance {x y : B128} : Decidable (x = y) := by
  rw [@Prod.ext_iff B64 B64 x y]; apply instDecidableAnd

instance {x y : B256} : Decidable (x = y) := by
  rw [@Prod.ext_iff B128 B128 x y]; apply instDecidableAnd

def B128.LT (x y : B128) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)
instance : @LT B128 := ⟨B128.LT⟩
instance {x y : B128} : Decidable (x < y) := instDecidableOr

def B256.LT (x y : B256) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)

instance : @LT B256 := ⟨B256.LT⟩
instance {x y : B256} : Decidable (x < y) := instDecidableOr

def Nat.toB128 (n : Nat) : B128 :=
  let q := n / (2 ^ 64)
  q.toUInt64 ++ n.toUInt64

def Nat.toB256 (n : Nat) : B256 :=
  let q := n / (2 ^ 128)
  q.toB128 ++ n.toB128

instance {n} : OfNat B128 n := ⟨n.toB128⟩
instance {n} : OfNat B256 n := ⟨n.toB256⟩

def B8.toHexit : B8 → Char
  | 0x0 => '0'
  | 0x1 => '1'
  | 0x2 => '2'
  | 0x3 => '3'
  | 0x4 => '4'
  | 0x5 => '5'
  | 0x6 => '6'
  | 0x7 => '7'
  | 0x8 => '8'
  | 0x9 => '9'
  | 0xA => 'a' -- 'A'
  | 0xB => 'b' -- 'B'
  | 0xC => 'c' -- 'C'
  | 0xD => 'd' -- 'D'
  | 0xE => 'e' -- 'E'
  | 0xF => 'f' -- 'F'
  | _   => 'x' -- 'X'

def B8.highs (x : B8) : B8 := (x >>> 4)
def B8.lows (x : B8) : B8 := (x &&& 0x0F)

def B8.toHex (x : B8) : String :=
  ⟨[x.highs.toHexit, x.lows.toHexit]⟩

def B8L.toHex (bs : B8L) : String :=
  List.foldr (λ b s => B8.toHex b ++ s) "" bs

def B16.highs (x : B16) : B8 := (x >>> 8).toUInt8
def B16.lows : B16 → B8 := UInt16.toUInt8
def B16.toHex (x : B16) : String := x.highs.toHex ++ x.lows.toHex

def B32.highs (x : B32) : B16 := (x >>> 16).toUInt16
def B32.lows : B32 → B16 := UInt32.toUInt16
def B32.toHex (x : B32) : String := x.highs.toHex ++ x.lows.toHex


def B64.highs (x : B64) : B32 := (x >>> 32).toUInt32
def B64.lows : B64 → B32 := UInt64.toUInt32
def B64.toHex (x : B64) : String := x.highs.toHex ++ x.lows.toHex

def B128.toHex (x : B128) : String := x.1.toHex ++ x.2.toHex
def B256.toHex (x : B256) : String := x.1.toHex ++ x.2.toHex

instance : ToString B8 := ⟨B8.toHex⟩
instance : ToString B16 := ⟨B16.toHex⟩
instance : ToString B32 := ⟨B32.toHex⟩
instance : ToString B64 := ⟨B64.toHex⟩
instance : ToString B128 := ⟨B128.toHex⟩
instance : ToString B256 := ⟨B256.toHex⟩

def B128.LE (x y : B128) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)
instance : @LE B128 := ⟨B128.LE⟩
instance {x y : B128} : Decidable (x ≤ y) := instDecidableOr

def B256.LE (x y : B256) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)
instance : @LE B256 := ⟨B256.LE⟩
instance {x y : B256} : Decidable (x ≤ y) := instDecidableOr


def B128.shiftLeft : B128 → Nat → B128
  | ⟨xs, ys⟩, os =>
    if os = 0
    then ⟨xs, ys⟩
    else if os < 64
         then ⟨ (xs <<< os.toUInt64) ||| (ys >>> (64 - os).toUInt64),
                ys <<< os.toUInt64 ⟩
         else if os < 128
              then ⟨ys <<< (os - 64).toUInt64, 0⟩
              else ⟨0, 0⟩
instance : HShiftLeft B128 Nat B128 := ⟨B128.shiftLeft⟩

def B128.shiftRight : B128 → Nat → B128
  | ⟨xs, ys⟩, os =>
    if os = 0
    then ⟨xs, ys⟩
    else if os < 64
         then ⟨ xs >>> os.toUInt64,
                (xs <<< (64 - os).toUInt64) ||| (ys >>> os.toUInt64) ⟩
         else if os < 128
              then ⟨0, xs >>> (os - 64).toUInt64⟩
              else ⟨0, 0⟩
instance : HShiftRight B128 Nat B128 := ⟨B128.shiftRight⟩

def B128.or : B128 → B128 → B128
  | ⟨xh, xl⟩, ⟨yh, yl⟩ => ⟨xh ||| yh, xl ||| yl⟩
instance : HOr B128 B128 B128 := ⟨B128.or⟩
def B128.and : B128 → B128 → B128
  | ⟨xh, xl⟩, ⟨yh, yl⟩ => ⟨xh &&& yh, xl &&& yl⟩
instance : HAnd B128 B128 B128 := ⟨B128.and⟩

def B256.or : B256 → B256 → B256
  | ⟨xh, xl⟩, ⟨yh, yl⟩ => ⟨xh ||| yh, xl ||| yl⟩
instance : HOr B256 B256 B256 := ⟨B256.or⟩
def B256.and : B256 → B256 → B256
  | ⟨xh, xl⟩, ⟨yh, yl⟩ => ⟨xh &&& yh, xl &&& yl⟩
instance : HAnd B256 B256 B256 := ⟨B256.and⟩

def B128.xor : B128 → B128 → B128
  | ⟨xh, xl⟩, ⟨yh, yl⟩ => ⟨xh ^^^ yh, xl ^^^ yl⟩
instance : HXor B128 B128 B128 := ⟨B128.xor⟩
def B256.xor : B256 → B256 → B256
  | ⟨xh, xl⟩, ⟨yh, yl⟩ => ⟨xh ^^^ yh, xl ^^^ yl⟩
instance : HXor B256 B256 B256 := ⟨B256.xor⟩

def B256.shiftRight : B256 → Nat → B256
  | ⟨xs, ys⟩, os =>
    if os = 0
    then ⟨xs, ys⟩
    else if os < 128
         then ⟨ xs >>> os,
                (xs <<< (128 - os)) ||| (ys >>> os) ⟩
         else if os < 256
              then ⟨0, xs >>> (os - 128)⟩
              else ⟨0, 0⟩
instance : HShiftRight B256 Nat B256 := ⟨B256.shiftRight⟩


def B256.shiftLeft : B256 → Nat → B256
  | ⟨xs, ys⟩, os =>
    if os = 0
    then ⟨xs, ys⟩
    else  if os < 128
         then ⟨(xs <<< os) ||| (ys >>> (128 - os)), ys <<< os⟩
         else if os < 256
              then ⟨ys <<< (os - 128), 0⟩
              else ⟨0, 0⟩
instance : HShiftLeft B256 Nat B256 := ⟨B256.shiftLeft⟩

def B256.isNeg : B256 → Bool := B256.highBit

def B256.arithShiftRight (xs : B256) (os : Nat) : B256 :=
  let xs' := xs >>> os
  if xs.isNeg
  then
    let mask := B256.max <<< (256 - os)
    xs' ||| mask
  else xs'

def B256.Slt (xs ys : B256) : Prop :=
  let x := xs.highBit
  let y := ys.highBit
  let xs' : B256 := xs &&& (B256.max >>> 1)
  let ys' : B256 := ys &&& (B256.max >>> 1)
  y < x ∨ (x = y ∧ xs' < ys')
instance {xs ys : B256} : Decidable (B256.Slt xs ys) := instDecidableOr

def B256.Sgt (xs ys : B256) : Prop := B256.Slt ys xs
instance {xs ys : B256} : Decidable (B256.Sgt xs ys) := instDecidableOr

def B128.complement : B128 → B128
  | ⟨xs, ys⟩ => ⟨~~~ xs, ~~~ ys⟩
instance : Complement B128 := ⟨B128.complement⟩

def B256.complement : B256 → B256
  | ⟨xs, ys⟩ => ⟨~~~ xs, ~~~ ys⟩
instance : Complement B256 := ⟨B256.complement⟩

def B8.toB256  (x : B8)  : B256 := ⟨0, ⟨0, x.toUInt64⟩⟩
def B16.toB256 (x : B16) : B256 := ⟨0, ⟨0, x.toUInt64⟩⟩
def B32.toB256 (x : B32) : B256 := ⟨0, ⟨0, x.toUInt64⟩⟩
def B64.toB256 (x : B64) : B256 := ⟨0, ⟨0, x⟩⟩

def B128.zero : B128 := ⟨0, 0⟩
instance : Zero B128 := ⟨.zero⟩
def B128.one : B128 := ⟨0, 1⟩
instance : One B128 := ⟨.one⟩
def B256.zero : B256 := ⟨0, 0⟩
instance : Zero B256 := ⟨.zero⟩
def B256.one : B256 := ⟨0, 1⟩
instance : One B256 := ⟨.one⟩

def B128.sub (x y : B128) : B128 :=
  let l := x.2 - y.2
  let c : B64 := if x.2 < y.2 then 1 else 0
  ⟨(x.1 - y.1) - c, l⟩
instance : HSub B128 B128 B128 := ⟨B128.sub⟩

def B128.add (x y : B128) : B128 :=
  let l := x.2 + y.2
  let c : B64 := if l < x.2 then 1 else 0
  ⟨x.1 + y.1 + c, l⟩
instance : HAdd B128 B128 B128 := ⟨B128.add⟩

def B256.add (x y : B256) : B256 :=
  let l := x.2 + y.2
  let c : B128 := if l < x.2 then 1 else 0
  ⟨x.1 + y.1 + c, l⟩
instance : HAdd B256 B256 B256 := ⟨B256.add⟩

def B256.sub (x y : B256) : B256 :=
  let l := x.2 - y.2
  let c : B128 := if x.2 < y.2 then 1 else 0
  ⟨(x.1 - y.1) - c, l⟩
instance : HSub B256 B256 B256 := ⟨B256.sub⟩
instance : Sub B256 := ⟨B256.sub⟩

def B256.neg (xs : B256) : B256 := (~~~ xs) + B256.one

-- minimum possible value in 2's complement
def B64.smin : B64 := 0x8000000000000000
def B128.smin : B128 := ⟨.smin, 0⟩
def B256.smin : B256 := ⟨.smin, 0⟩

def B64.negOne  : B64  := .max
def B128.negOne : B128 := .max
def B256.negOne : B256 := .max

def Nat.toBool : Nat → Bool
  | 0 => 0
  | _ => 1

abbrev Vec := Vector

def B64.toB8V (x : B64) : Vec B8 8 :=
  ⟨ #[ (x >>> 56).toUInt8, (x >>> 48).toUInt8,
       (x >>> 40).toUInt8, (x >>> 32).toUInt8,
       (x >>> 24).toUInt8, (x >>> 16).toUInt8,
       (x >>> 8).toUInt8, x.toUInt8 ], rfl ⟩

def B64.toB8L (x : B64) : B8L :=
  [ (x >>> 56).toUInt8, (x >>> 48).toUInt8,
    (x >>> 40).toUInt8, (x >>> 32).toUInt8,
    (x >>> 24).toUInt8, (x >>> 16).toUInt8,
    (x >>> 8).toUInt8, x.toUInt8 ]

def B64.reverse (w : B64) : B64 :=
  ((w <<< 56) &&& (0xFF00000000000000 : B64)) |||
  ((w <<< 40) &&& (0x00FF000000000000 : B64)) |||
  ((w <<< 24) &&& (0x0000FF0000000000 : B64)) |||
  ((w <<< 8)  &&& (0x000000FF00000000 : B64)) |||
  ((w >>> 8)  &&& (0x00000000FF000000 : B64)) |||
  ((w >>> 24) &&& (0x0000000000FF0000 : B64)) |||
  ((w >>> 40) &&& (0x000000000000FF00 : B64)) |||
  ((w >>> 56) &&& (0x00000000000000FF : B64))

def B128.toB8L (x : B128) : B8L := x.1.toB8L ++ x.2.toB8L
def B256.toB8L (x : B256) : B8L := x.1.toB8L ++ x.2.toB8L

def B128.toB8V (x : B128) : Vec B8 16 :=
  Vector.append x.1.toB8V x.2.toB8V

def B256.toB8V (x : B256) : Vec B8 32 :=
  Vector.append x.1.toB8V x.2.toB8V

def B128.toNat (x : B128) : Nat := (x.1.toNat * (2 ^ 64)) + x.2.toNat
def B256.toNat (x : B256) : Nat := (x.1.toNat * (2 ^ 128)) + x.2.toNat

def B256.addmod (x y z : B256) : B256 :=
  if z = 0
  then 0
  else ((x.toNat + y.toNat) % z.toNat).toB256 -- (x + y) % z

def B256.mulmod (x y z : B256) : B256 :=
  if z = 0
  then 0
  else ((x.toNat * y.toNat) % z.toNat).toB256 -- (x + y) % z

def B256.signext (x y : B256) : B256 :=
  if h : x < 31 then
    have h' : (32 - (x.toNat + 1)) < 32 := by omega
    let z : B8 := y.toB8V.get ⟨32 - (x.toNat + 1), h'⟩
    cond z.highBit
      ((B256.max <<< (8 * (x.toNat + 1))) ||| y)
      ((B256.max >>> (256 - (8 * (x.toNat + 1)))) &&& y)
  else y

theorem List.length_dropWhile_le {ξ : Type u} (xs : List ξ) (f : ξ → Bool) :
    (dropWhile f xs ).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases h : f x
    · rw [List.dropWhile_cons_of_pos h]
      apply le_trans ih; simp
    · rw [List.dropWhile_cons_of_neg h]

instance {ξ : Type u} {ρ : ξ → Prop} {xs : List ξ}
    [d : ∀ x : ξ, Decidable (ρ x)] : Decidable (xs.Forall ρ) := by
  induction xs with
  | nil => apply instDecidableTrue
  | cons x xs ih => simp; apply instDecidableAnd

def List.drop? {ξ : Type u} : Nat → List ξ → Option (List ξ)
  | 0, xs => some xs
  | _ + 1, [] => none
  | n + 1, _ :: xs => xs.drop? n

def List.take? {ξ : Type u} : Nat → List ξ → Option (List ξ)
  | 0, _ => some []
  | _ + 1, [] => none
  | n + 1, x :: xs => (x :: ·) <$> xs.take? n

def List.slice? {ξ : Type u} (xs : List ξ) (m n : Nat) : Option (List ξ) :=
  drop? m xs >>= take? n

def List.sliceD {ξ : Type u} (xs : List ξ) (m n : Nat) (x : ξ) : List ξ :=
  takeD n (drop m xs) x

def List.slice! {ξ : Type u} [Inhabited ξ] (xs : List ξ) (m n : Nat) : List ξ :=
  takeD n (drop m xs) default

def B64.lows' (i : B64) : B64 := (i &&& 0x00000000FFFFFFFF)
def B64.highs' (i : B64) : B64 := (i >>> 32)

def B64.mulx (x y : B64) : B128 :=
  let xh := x.highs'
  let xl := x.lows'
  let yh := y.highs'
  let yl := y.lows'
  let ll := xl * yl
  let lh := xl * yh
  let hl := xh * yl
  let hh := xh * yh
  let lhl := lh <<< 32
  let hll := hl <<< 32
  let lt := ll + lhl
  let l := lt + hll
  let c : B64 :=
    match (lt < ll : Bool), (l < lt : Bool) with
    | true, true => 2
    | false, false => 0
    | _, _  => 1
  let h := hh + lh.highs' + hl.highs' + c --0 + c1
  ⟨h, l⟩

def B128.mulx (x y : B128) : B256 :=
  let ll := B64.mulx x.2 y.2
  let lh := B64.mulx x.2 y.1
  let hl := B64.mulx x.1 y.2
  let hh := B64.mulx x.1 y.1
  let lhl : B128 := ⟨lh.2, 0⟩
  let hll : B128 := ⟨hl.2, 0⟩
  let lt := ll + lhl
  let l := lt + hll
  let c : B128 :=
    match (lt < ll : Bool), (l < lt : Bool) with
    | true, true => ⟨0, 2⟩
    | false, false => ⟨0, 0⟩
    | _, _  => ⟨0, 1⟩
  let h := hh + ⟨0, lh.1⟩ + ⟨0, hl.1⟩ + c --0 + c1
  ⟨h, l⟩

def B256.mul (x y : B256) : B256 :=
  let ll := B128.mulx x.2 y.2
  let lh := B128.mulx x.2 y.1
  let hl := B128.mulx x.1 y.2
  ll + ⟨lh.2, 0⟩ + ⟨hl.2, 0⟩
instance : HMul B256 B256 B256 := ⟨B256.mul⟩

def divOffset : Nat → B256 → B256 → Option Nat
  | 0, _, _ => some 0
  | m + 1, x, y =>
    if x < y
    then none
    else if B256.smin ≤ y
         then some 0
         else match divOffset m x (y <<< 1) with
                   | none => some 0
                   | some n => some (n + 1)


def B256.divModCore : Nat → B256 → B256 → B256 → (B256 × B256)
  | 0,     x, _, z => ⟨z, x⟩
  | n + 1, x, y, z =>
    if x < y
    then divModCore n x (y >>> 1) (z <<< 1)
    else divModCore n (x - y) (y >>> 1) ((z <<< 1) + 1)
def B256.divMod (x y : B256) : B256 × B256 :=
  if y = 0
  then ⟨0, 0⟩
  else let os := divOffset 255 x y
       match os with
       | none => ⟨0, x⟩
       | some n =>
         B256.divModCore (n + 1) x (y <<< n) 0

instance : HDiv B256 B256 B256 := ⟨λ x y => (B256.divMod x y).fst⟩
instance : HMod B256 B256 B256 := ⟨λ x y => (B256.divMod x y).snd⟩

def B256.sdiv (xs ys : B256) : B256 :=
  if ys = 0
  then 0
  else if xs = smin ∧ ys = negOne
       then smin
       else match (isNeg xs, isNeg ys) with
            | (0, 0) => xs / ys
            | (1, 0) => neg ((neg xs) / ys)
            | (0, 1) => neg (xs / (neg ys))
            | (1, 1) => (neg xs) / (neg ys)

def B256.abs (xs : B256) : B256 := if isNeg xs then neg xs else xs

def B256.smod (xs ys : B256) : B256 :=
  if ys = 0
  then 0
  else let mod := (abs xs) % (abs ys)
       if isNeg xs then neg mod else mod

def B64.teg (xs : B64) (n : Nat) : Bool :=
  ((xs >>> n.toUInt64) &&& 0x0000000000000001) != 0

def B128.teg (xs : B128) (n : Nat) : Bool :=
  if n < 64
  then xs.2.teg n
  else xs.1.teg (n - 64)

def B256.teg (xs : B256) (n : Nat) : Bool :=
  if n < 128
  then xs.2.teg n
  else xs.1.teg (n - 128)

def B256.bexpCore : Nat → B256 → B256 → (B256 × B256)
 | 0, xs, _ => ⟨1, xs⟩
 | n + 1, xs, ys =>
   let ⟨r, s⟩ := B256.bexpCore n xs ys
   let y : Bool := ys.teg n
   ⟨(cond y s 1) * r, s * s⟩

def B256.bexp (xs ys : B256) : B256 :=
  (B256.bexpCore 256 xs ys).fst

instance : HPow B256 B256 B256 := ⟨B256.bexp⟩

/-- Efficient modular exponentiation using the square-and-multiply algorithm -/
def Nat.powMod (base exp m : Nat) : Nat :=
  if m ≤ 1 then 0 else
    let rec go (e : Nat) (b : Nat) (res : Nat) : Nat :=
      match e with
      | 0 => res
      | e@(_ + 1) =>
        let res' := if e % 2 = 1 then (res * b) % m else res
        let b' := (b * b) % m
        go (e / 2) b' res'
    go exp base 1

def String.joinln : List String → String :=
  String.intercalate "\n"

def Hexit.toB4 : Char → Option B8
  | '0' => some 0x00
  | '1' => some 0x01
  | '2' => some 0x02
  | '3' => some 0x03
  | '4' => some 0x04
  | '5' => some 0x05
  | '6' => some 0x06
  | '7' => some 0x07
  | '8' => some 0x08
  | '9' => some 0x09
  | 'a' => some 0x0A
  | 'b' => some 0x0B
  | 'c' => some 0x0C
  | 'd' => some 0x0D
  | 'e' => some 0x0E
  | 'f' => some 0x0F
  | 'A' => some 0x0A
  | 'B' => some 0x0B
  | 'C' => some 0x0C
  | 'D' => some 0x0D
  | 'E' => some 0x0E
  | 'F' => some 0x0F
  |  _  => none

def B4L.toB8L : B8L → Option B8L
  | [] => some []
  | [_] => none
  | x :: y :: xs =>
    let xy := (x <<< 4) ||| y
    (xy :: ·) <$> B4L.toB8L xs

def Hex.toB8L (s : String) : Option B8L :=
  s.data.mapM Hexit.toB4 >>= B4L.toB8L

def Option.toIO {ξ} (o : Option ξ)
  (msg : String := "error : option-to-IO lift failed, input is 'none'") :
  IO ξ := do
  match o with
  | none => throw (IO.Error.userError msg)
  | some x => pure x

def List.compare {ξ : Type u} [Ord ξ] : List ξ → List ξ → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
    match Ord.compare x y with
    | .eq => List.compare xs ys
    | o => o

def B128.compare : B128 → B128 → Ordering
  | ⟨x, y⟩, ⟨x', y'⟩ =>
    match Ord.compare x x' with
    | .eq => Ord.compare y y'
    | o => o

instance : Ord B128 := ⟨B128.compare⟩

def B256.compare : B256 → B256 → Ordering
  | ⟨x, y⟩, ⟨x', y'⟩ =>
    match Ord.compare x x' with
    | .eq => Ord.compare y y'
    | o => o

instance {ξ : Type u} [Ord ξ] : Ord (List ξ) := ⟨List.compare⟩
instance : Ord B256 := ⟨B256.compare⟩

def B8.compareLows (x y : B8) : Ordering :=
  Ord.compare x.lows y.lows

def pad : String → String
  | s => "  " ++ s

def padMid : String -> String
  | s => "│ " ++ s

def padsMid : List String → List String
  | [] => []
  | s :: ss => ("├─" ++ s) :: ss.map padMid

def padsEnd : List String → List String
  | [] => []
  | s :: ss => ("└─" ++ s) :: ss.map pad

def padss : List (List String) -> List String
  | [] => []
  | [ss] => padsEnd ss
  | ss :: sss => padsMid ss ++ padss sss

def addComma (ss : List String) : Option (List String) :=
  let rec aux (s : String) : List String -> List String
    | [] => [s ++ ","]
    | s' :: ss' => s :: (aux s' ss')
  match ss with
  | [] => none
  | s :: ss' => some <| aux s ss'

def addCommas  (ss : List String) : List (List String) -> Option (List String)
  | [] => ss
  | ss' :: sss' => do
    let ssc ← addComma ss
    let ssc' ← addCommas ss' sss'
    ssc ++ ssc'

def mkProlog (s : String) : List (List String) → Option (List String)
  | [] => some [s]
  | (ss :: sss) => do
    let ssc ← addCommas ss sss
    (s ++ "(") :: (ssc.map pad ++ [")"])

def fork (s : String) : List (List String) → List String
  | [[s']] => [s ++ "──" ++ s']
  | sss => s :: padss sss

def encloseStrings : List String → List String
  | [] => ["[]"]
  | [s] => ["[" ++ s ++ "]"]
  | ss => "┌─" :: ss.map padMid ++ ["└─"]

def List.toStrings {ξ} (f : ξ -> List String) (xs : List ξ) : List String :=
  encloseStrings (xs.map f).flatten

def B4L.toHex : B8L → String
  | [] => ""
  | [b] => ⟨[b.toHexit]⟩
  | b :: bs => ⟨[b.toHexit] ++ (toHex bs).data⟩
def IO.throw {ξ} (s : String) : IO ξ := MonadExcept.throw <| IO.Error.userError s

def IO.remove0x : String → IO String
  | ⟨'0' :: 'x' :: s⟩ => return ⟨s⟩
  | _ => IO.throw "prefix not 0x"

def Option.remove0x : String → Option String
  | ⟨'0' :: 'x' :: s⟩ => return ⟨s⟩
  | _ => .none

def remove0x : String → String
  | ⟨'0' :: 'x' :: s⟩ => ⟨s⟩
  | s => s

def B8s.toB16 (a b : B8) : B16 :=
  let a16 : B16 := a.toUInt16
  let b16 : B16 := b.toUInt16
  (a16 <<< 8) ||| b16

def B8s.toB32 (a b c d : B8) : B32 :=
  let a32 : B32 := a.toUInt32
  let b32 : B32 := b.toUInt32
  let c32 : B32 := c.toUInt32
  let d32 : B32 := d.toUInt32
  (a32 <<< 24) ||| (b32 <<< 16) ||| (c32 <<< 8) ||| d32

def B8s.toB64 (a b c d e f g h : B8) : B64 :=
  let a64 : B64 := a.toUInt64
  let b64 : B64 := b.toUInt64
  let c64 : B64 := c.toUInt64
  let d64 : B64 := d.toUInt64
  let e64 : B64 := e.toUInt64
  let f64 : B64 := f.toUInt64
  let g64 : B64 := g.toUInt64
  let h64 : B64 := h.toUInt64
  (a64 <<< 56) |||
  (b64 <<< 48) |||
  (c64 <<< 40) |||
  (d64 <<< 32) |||
  (e64 <<< 24) |||
  (f64 <<< 16) |||
  (g64 <<< 8)  |||
  h64

def B8s.toB128
  (x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 : B8) : B128 :=
  ⟨ B8s.toB64 x0 x1 x2 x3 x4 x5 x6 x7,
    B8s.toB64 y0 y1 y2 y3 y4 y5 y6 y7 ⟩

def B8s.toB256
  ( x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 xA xB xC xD xE xF
    y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 yA yB yC yD yE yF : B8 ) : B256 :=
  ⟨ B8s.toB128 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 xA xB xC xD xE xF,
    B8s.toB128 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 yA yB yC yD yE yF ⟩

def B8L.toB64? : B8L → Option B64
  | [x0, x1, x2, x3, x4, x5, x6, x7] => B8s.toB64 x0 x1 x2 x3 x4 x5 x6 x7
  | _ => .none

def B8L.toB128Diff : B8L → Option (B128 × B8L)
  | x0 :: x1 :: x2 :: x3 ::
    x4 :: x5 :: x6 :: x7 ::
    y0 :: y1 :: y2 :: y3 ::
    y4 :: y5 :: y6 :: y7 :: xs =>
    some
      ⟨
        ⟨ B8s.toB64 x0 x1 x2 x3 x4 x5 x6 x7,
          B8s.toB64 y0 y1 y2 y3 y4 y5 y6 y7 ⟩,
        xs
      ⟩
  | _ => none

def List.ekat {ξ : Type u} (n : Nat) (xs : List ξ) : List ξ :=
  (xs.reverse.take n).reverse

def List.ekatD {ξ : Type u} (n : Nat) (xs : List ξ) (x : ξ) : List ξ :=
  (xs.reverse.takeD n x).reverse

theorem List.length_takeD {ξ : Type u} (n : Nat) (xs : List ξ) (x : ξ) :
    (List.takeD n xs x).length = n := by
  induction n generalizing xs with
  | zero => simp
  | succ n ih => simp; apply ih

theorem List.length_ekatD {ξ : Type u} (n : Nat) (xs : List ξ) (x : ξ) :
    (List.ekatD n xs x).length = n := by
  apply Eq.trans List.length_reverse
  apply Eq.trans (List.length_takeD _ _ _) rfl

def B8L.toB256? (xs : B8L) : Option B256 := do
  let ⟨h, xs'⟩ ← xs.toB128Diff
  let ⟨l, []⟩ ← xs'.toB128Diff | none
  some ⟨h, l⟩

def Hex.toB64? (hx : String) : Option B64 := do
  Hex.toB8L hx >>= B8L.toB64?

def Hex.toB256? (hx : String) : Option B256 := do
  Hex.toB8L hx >>= B8L.toB256?

def B8V.toB64 (v : Vec B8 8) : B64 :=
  B8s.toB64 v[0] v[1] v[2] v[3] v[4] v[5] v[6] v[7]

def B8V.toB128 (v : Vec B8 16) : B128 :=
    ⟨ B8s.toB64 v[0x0] v[0x1] v[0x2] v[0x3] v[0x4] v[0x5] v[0x6] v[0x7],
      B8s.toB64 v[0x8] v[0x9] v[0xA] v[0xB] v[0xC] v[0xD] v[0xE] v[0xF] ⟩

def B8V.toB256 (xs : Vec B8 32) : B256 :=
  let h : Vec B8 16 := xs.take 16
  let l : Vec B8 16 := xs.drop 16
  ⟨B8V.toB128 h, B8V.toB128 l⟩

def B8L.pack (xs : B8L) (n : Nat) : B8L := List.ekatD n xs 0

def B8L.toB8V (xs : B8L) (n : Nat) : Vec B8 n :=
  ⟨⟨xs.pack n⟩, List.length_ekatD _ _ _⟩

def B8L.toB256P (xs : B8L) : B256 := B8V.toB256 (xs.toB8V 32)
def B8L.toB64P (xs : B8L) : B64 := B8V.toB64 (xs.toB8V 8)

def IO.guard (φ : Prop) [Decidable φ] (msg : String) : IO Unit :=
  if φ then return () else IO.throw msg

def Array.writeD {ξ : Type u} (xs : Array ξ) (n : ℕ) : List ξ → Array ξ
  | [] => xs
  | y :: ys =>
    if h : n < xs.size
    then let xs' := xs.setN n y
         writeD xs' (n + 1) ys
    else xs

def Array.copyD {ξ : Type u} (xs ys : Array ξ) : Array ξ :=
  let f : (Array ξ × Nat) → ξ → (Array ξ × Nat) :=
    λ ysn x => ⟨Array.set! ysn.fst ysn.snd x, ysn.snd + 1⟩
  (Array.foldl f ⟨ys, 0⟩ xs).fst

def ByteArray.sliceD (xs : ByteArray) : Nat → Nat → B8 → B8L
  | _, 0, _ => []
  | m, n + 1, d =>
    if m < xs.size
    then xs.get! m :: ByteArray.sliceD xs (m + 1) n d
    else List.replicate (n + 1) d

def Array.sliceD {ξ : Type u} (xs : Array ξ) : Nat → Nat → ξ → List ξ :=
  let rec aux (xs : Array ξ) : List ξ → Nat → Nat → ξ → List ξ
    | Acc, _, 0, _ => Acc
    | Acc, m, n + 1, d =>
      aux xs (xs.getD (m + n) d :: Acc) m n d
  aux xs []

def B256.min : B256 → B256 → B256
  | xs, ys => if xs ≤ ys then xs else ys
instance : Min B256 := ⟨.min⟩

def B16.toB8L (x : B16) : List B8 := [x.highs, x.lows]
def B32.toB8L (x : B32) : List B8 := x.highs.toB8L ++ x.lows.toB8L
def B8.toB4s (x : B8) : List B8 := [x.highs, x.lows]
def B16.toB4s (x : B16) : List B8 := x.highs.toB4s ++ x.lows.toB4s
def B32.toB4s (x : B32) : List B8 := x.highs.toB4s ++ x.lows.toB4s
def B64.toB4s (x : B64) : List B8 := x.highs.toB4s ++ x.lows.toB4s
def B128.toB4s (x : B128) : List B8 := x.1.toB4s ++ x.2.toB4s
def B256.toB4s (x : B256) : List B8 := x.1.toB4s ++ x.2.toB4s

def B8L.toB4s : B8L → B8L
  | [] => []
  | x :: xs => x.toB4s ++ B8L.toB4s xs

abbrev B32L : Type := List B32
abbrev B32A : Type := Array B32

def List.splitAt? {ξ : Type u} (n : Nat) (xs : List ξ) : Option (List ξ × List ξ) :=
  let rec aux : Nat → List ξ →  List ξ → Option (List ξ × List ξ)
    | 0, xs, ys => some (xs.reverse, ys)
    | _ + 1, _, [] => none
    | n + 1, xs, y :: ys => aux n (y :: xs) ys
  aux n [] xs

def B8L.toNat (bs : B8L) : Nat :=
  let rec aux (acc : Nat) : B8L → Nat
    | [] => acc
    | b :: bs => aux ((acc * 256) + b.toNat) bs
  aux 0 bs

def Nat.toB8L (n : Nat) : B8L :=
  let rec aux (acc : B8L) : Nat → B8L
  | 0 => acc
  | n@(_ + 1) => aux ((n % 256).toUInt8 :: acc) (n / 256)
  aux [] n

def Nat.toB8LPack : Nat → B8L
  | 0 => [0]
  | n@(_ + 1) => n.toB8L

def Except.assert (p : Prop) [inst : Decidable p]
  {ξ : Type u} (x : ξ) : Except ξ Unit :=
  if p then .ok () else .error x

def Option.toExcept {ξ : Type u} {υ : Type v} (x : ξ) : Option υ → Except ξ υ
  | .none => .error x
  | .some y => .ok y

inductive BLT : Type
  | b8s : B8L → BLT
  | list : List BLT → BLT

def B8.toBools (x0 : B8) :
    Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool :=
  let x1 := x0 <<< 1
  let x2 := x1 <<< 1
  let x3 := x2 <<< 1
  let x4 := x3 <<< 1
  let x5 := x4 <<< 1
  let x6 := x5 <<< 1
  let x7 := x6 <<< 1
  ⟨ x0.highBit, x1.highBit, x2.highBit, x3.highBit,
    x4.highBit, x5.highBit, x6.highBit, x7.highBit ⟩

mutual

  def B8L.toBLTDiff? : Nat → B8L → Option (BLT × B8L)
    | _, [] => none
    | 0, _ :: _ => none
    | k + 1, b :: bs =>
      match b.toBools with
    | ⟨0, _, _, _, _, _, _, _⟩ => some (.b8s [b], bs)
    | ⟨1, 0, 1, 1, 1, _, _, _⟩ => do
      let (lbs, bs') ← List.splitAt? (b - 0xB7).toNat bs
      let (rbs, bs'') ← List.splitAt? (B8L.toNat lbs) bs'
      return ⟨.b8s rbs, bs''⟩
    | ⟨1, 0, _, _, _, _, _, _⟩ =>
      .map .b8s id <$> List.splitAt? (b - 0x80).toNat bs
    | ⟨1, 1, 1, 1, 1, _, _, _⟩ => do
      let (lbs, bs') ← List.splitAt? (b - 0xF7).toNat bs
      let (rbs, bs'') ← List.splitAt? (B8L.toNat lbs) bs'
      let rs ← B8L.toBLTs? k rbs
      return ⟨.list rs, bs''⟩
    | ⟨1, 1, _, _, _, _, _, _⟩ => do
      let (rbs, bs') ← List.splitAt? (b - 0xC0).toNat bs
      let rs ← B8L.toBLTs? k rbs
      return ⟨.list rs, bs'⟩

  def B8L.toBLTs? : Nat → B8L → Option (List BLT)
    | _, [] => some []
    | 0, _ :: _ => none
    | k + 1, bs@(_ :: _) => do
      let (r, bs') ← B8L.toBLTDiff? (k + 1) bs
      let rs ← B8L.toBLTs? k bs'
      return (r :: rs)

end

def B8L.toBLT? (bs : B8L) : Option BLT :=
  match B8L.toBLTDiff? bs.length bs with
  | some (r, []) => some r
  | _ => none

mutual

  def BLT.toB8L : BLT → B8L
    | .b8s [b] => if b < (0x80) then [b] else [0x81, b]
    | .b8s bs =>
      if bs.length < 56
      then (0x80 + bs.length.toUInt8) :: bs
      else let lbs : B8L := bs.length.toB8LPack
           (0xB7 + lbs.length.toUInt8) :: (lbs ++ bs)
    | .list rs => BLTs.toB8L rs

  def BLTs.toB8LsJoin : List BLT → B8L
    | .nil => []
    | .cons r rs => r.toB8L ++ BLTs.toB8LsJoin rs

  def BLTs.toB8L (rs : List BLT) : B8L :=
    let bs := BLTs.toB8LsJoin rs
    let len := bs.length
    if len < 56
    then (0xC0 + len.toUInt8) :: bs
    else let lbs : B8L := len.toB8LPack
         (0xF7 + lbs.length.toUInt8) :: (lbs ++ bs)

end

def List.chunksCore {ξ} (m : Nat) : Nat → List ξ → List (List ξ)
  | _, [] => []
  | 0, x :: xs =>
    match chunksCore m m xs with
    | [] => [[], [x]]
    | ys :: yss => [] :: (x :: ys) :: yss
  | n + 1, x :: xs =>
    match chunksCore m n xs with
    | [] => [[x]]
    | ys :: yss => (x :: ys) :: yss

def List.chunks {ξ} (m : Nat) : List ξ → List (List ξ) := List.chunksCore m (m + 1)

def String.chunks : Nat → String → List String
  | 0, _ => []
  | m + 1, s => (List.chunks m s.data).map String.mk

mutual

  def BLT.toStrings : BLT → List String
    | .b8s bs => fork "[B8L]" [(List.chunks 31 bs).map B8L.toHex]
    | .list rs => fork "[LIST]" (BLTs.toStringss rs)

  def BLTs.toStringss : List BLT → List (List String)
    | [] => []
    | r :: rs => r.toStrings :: BLTs.toStringss rs

end

instance : ToString BLT := ⟨String.joinln ∘ BLT.toStrings⟩

def readJsonFile (filename : System.FilePath) : IO Lean.Json := do
  let contents ← IO.FS.readFile filename
  match Lean.Json.parse contents with
  | .ok json => pure json
  | .error err => throw (IO.userError err)

mutual

  partial def StringJson.toStrings : (String × Lean.Json) → List String
    | ⟨n, j⟩ =>
      (fork n [Lean.Json.toStrings j])

  partial def StringJsons.toStrings : List ((_ : String) × Lean.Json) → List String
    | [] => []
    | ⟨n, j⟩ :: njs =>
      (fork n [Lean.Json.toStrings j]) ++ StringJsons.toStrings njs

  partial def Lean.Jsons.toStrings : List Lean.Json → List String
    | [] => []
    | j :: js => Lean.Json.toStrings j ++ Lean.Jsons.toStrings js

  partial def Lean.Json.toStrings : Lean.Json → List String
    | .null => ["NULL"]
    | .bool b => [s!"BOOL : {b}"]
    | .num n => [s!"NUM : {n}"]
    | .str s =>
       fork "STR" [s.chunks 80]
    | .arr js =>
      fork "ARR" (js.toList.map Lean.Json.toStrings)
    | .obj m => do
      let kvs := m.toArray.toList
      fork "OBJ" (kvs.map StringJson.toStrings)

end

def Lean.Json.toString (j : Lean.Json) : String := String.joinln j.toStrings

def B256.lt_check  (x y : B256) : B256 := if x < y then 1 else 0
def B256.gt_check  (x y : B256) : B256 := if x > y then 1 else 0
def B256.slt_check (x y : B256) : B256 := if B256.Slt x y then 1 else 0
def B256.sgt_check (x y : B256) : B256 := if B256.Sgt x y then 1 else 0
def B256.eq_check  (x y : B256) : B256 := if x = y then 1 else 0

def ceilDiv (m n : Nat) := m / n + if m % n = 0 then 0 else 1

def B32.rol (x n : B32) : B32 :=
  x <<< n ||| (x >>> (32 - n))
def B32.ror (x n : B32): B32 :=
  x >>> n ||| (x <<< (32 - n))

def B32s.toB64 (x y : B32) : B64 :=
  x.toUInt64 <<< 32 ||| y.toUInt64

def B32s.toB128 (x0 x1 y0 y1 : B32) : B128 :=
  ⟨B32s.toB64 x0 x1, B32s.toB64 y0 y1⟩

def B32s.toB256 (x0 x1 x2 x3 y0 y1 y2 y3: B32) : B256 :=
  ⟨B32s.toB128 x0 x1 x2 x3, B32s.toB128 y0 y1 y2 y3⟩

def List.splitToArray {ξ : Type u}
  (sz : Nat) (xs : List ξ) (x : ξ) : Array ξ × List ξ :=
  let rec aux : Nat → Array ξ → Nat → List ξ → Array ξ × List ξ
    | _, array, _, [] => ⟨array, []⟩
    | _, array, 0, list => ⟨array, list⟩
    | idx, array, sz + 1, item :: list =>
      aux (idx + 1) (array.set! idx item) sz list
  aux 0 (.replicate sz x) sz xs

def Nat.toHexit : Nat → Char
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | 9 => '9'
  | 10 => 'A'
  | 11 => 'B'
  | 12 => 'C'
  | 13 => 'D'
  | 14 => 'E'
  | 15 => 'F'
  | _   => 'X'

def Nat.toHex (n : Nat) : String :=
  let rec aux : Nat → List Char
    | 0 => []
    | n@(_ + 1) =>
      if n < 16
      then [n.toHexit]
      else (n % 16).toHexit :: aux (n / 16)
  ⟨.reverse <| aux n⟩

def List.maxD {ξ} [Max ξ] : List ξ → ξ → ξ
  | [], y => y
  | x :: xs, y => maxD xs (max x y)

def cprint {m : Type → Type v}  [inst : Monad m] (vb : Bool) (msg : String) : m Unit := do
  if vb then do
    dbg_trace msg

def Except.print {ξ : Type} (msg : String) : Except ξ Unit := do
  dbg_trace msg
