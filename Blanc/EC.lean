import Blanc.Basic

abbrev altBn128Prime      : Nat := 21888242871839275222246405745257275088696311157297823662689037894645226208583
abbrev altBn128CurveOrder : Nat := 21888242871839275222246405745257275088548364400416034343698204186575808495617

structure FinField (p : Nat) : Type where
  (val : Nat)
deriving DecidableEq

abbrev BNF : Type := FinField altBn128Prime

instance {p} : ToString (FinField p) := ⟨fun x => toString x.val⟩

def FinField.ofNat {p : Nat} (n : Nat) : FinField p := ⟨n % p⟩

def FinField.ofInt {p : Nat} : Int → FinField p
  | .ofNat n => .ofNat n
  | .negSucc n => .ofNat (p - n.succ % p) -- handle negative integers by wrapping around the field size

instance {p n : Nat} : OfNat (FinField p) n := ⟨.ofNat n⟩

structure EllipticCurve (F : Type) (a b : F) : Type where
  (x : F)
  (y : F)
deriving DecidableEq

abbrev FinFields (p : Nat) : Type := List (FinField p)

structure GaloisField (p : Nat) (m : FinFields p) : Type where
  (val : FinFields p)
deriving DecidableEq

instance {p m} : ToString (GaloisField p m) := ⟨
  fun x =>
  String.joinln <|
    "  [" :: (x.val.map <| fun y => "    " ++ toString y ++ ",") ++ ["  ]"]
⟩

abbrev BNF2 : Type :=
  -- FinField altBn128Prime × FinField altBn128Prime
  GaloisField altBn128Prime [1, 0, 1]

-- def BNF2.i : BNF2 := ⟨[1, 0]⟩

def GaloisField.ofNat {p} {m} : Nat → GaloisField p m
  | 0 => ⟨[]⟩
  | n@(_ + 1) => ⟨[.ofNat n]⟩

instance {p m n} : OfNat (GaloisField p m) n := ⟨.ofNat n⟩

def FinField.pow {p : Nat} (b : FinField p) (e : Nat) : FinField p :=
  ⟨Nat.powMod b.val e p⟩

instance {p} : HPow (FinField p) Nat (FinField p) := ⟨FinField.pow⟩

def FinField.add {p : Nat} (x y : FinField p) : FinField p :=
  ⟨(x.val + y.val) % p⟩

instance {p} : HAdd (FinField p) (FinField p) (FinField p) := ⟨FinField.add⟩

def FinField.sub {p : Nat} (x y : FinField p) : FinField p :=
  ⟨Int.natAbs <| (Int.ofNat x.val - Int.ofNat y.val) % p⟩

instance {p} : HSub (FinField p) (FinField p) (FinField p) := ⟨FinField.sub⟩

def FinField.mul {p : Nat} (x y : FinField p) : FinField p :=
  ⟨(x.val * y.val) % p⟩

instance {p} : HMul (FinField p) (FinField p) (FinField p) := ⟨FinField.mul⟩

def BNF2.mk (x y : Nat) : BNF2 :=
  ⟨[.ofNat x, .ofNat y]⟩

def extEuclid (x y : Nat) : Int × Int × Nat :=
  if hx : x > 0
  then
    if hy : y > 0
    then
      if _ : x < y
      then
        have _ : y % x < x := Nat.mod_lt _ hx
        let ⟨cy, cx, d⟩ := extEuclid (y % x) x
        ⟨cx - (cy * (y / x)), cy, d⟩
      else
        if _ : y < x
        then
          have _ : x % y < y := Nat.mod_lt _ hy
          let ⟨cy, cx, d⟩ := extEuclid y (x % y)
          ⟨cx, cy - (cx * (x / y)), d⟩
        else ⟨0, 1, x⟩
    else ⟨1, 0, x⟩
  else ⟨0, 1, y⟩
termination_by (x + y)

def FinField.inv {p : Nat} (x : FinField p) : FinField p :=
  let ⟨c, _, _⟩ := extEuclid x.val p
  ⟨(c % p).natAbs⟩

instance {p} : Inv (FinField p) := ⟨FinField.inv⟩

def FinField.div {p : Nat} (x y : FinField p) : FinField p := x * (y⁻¹)

instance {p} : HDiv (FinField p) (FinField p) (FinField p) := ⟨FinField.div⟩

instance {k} : Inhabited (FinField k) := ⟨0⟩

def trimZero {ξ} [Zero ξ] [DecidableEq ξ] (xs : List ξ) : List ξ :=
  List.dropWhile (· = 0) xs

def zipWithZero {ξ} [Zero ξ] : List ξ → List ξ → List (ξ × ξ)
  | [], [] => []
  | [], y :: ys => (0, y) :: zipWithZero [] ys
  | x :: xs, [] => (x, 0) :: zipWithZero xs []
  | x :: xs, y :: ys => (x, y) :: zipWithZero xs ys

lemma zipWithZero_length {ξ} [Zero ξ] (xs ys : List ξ) :
  (zipWithZero xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys with
    | nil =>
      induction ys with
      | nil => simp [zipWithZero]
      | cons y ys ih => simp [zipWithZero, ih]
    | cons x xs ih =>
      induction ys with
      | nil => simp [zipWithZero, ih]
      | cons y ys ih' =>
        simp [zipWithZero, ih, ih', List.length, Nat.succ_max_succ]

def zipWithZeroLeft {ξ} [Zero ξ] (xs ys : List ξ) : List (ξ × ξ) :=
  (zipWithZero xs.reverse ys.reverse).reverse

lemma zipWithZeroLeft_length {ξ} [Zero ξ] (xs ys : List ξ) :
  (zipWithZeroLeft xs ys).length = max xs.length ys.length := by
  simp [zipWithZeroLeft, zipWithZero_length]

lemma trimZero_length {ξ} [Zero ξ] [DecidableEq ξ] (xs : List ξ) :
  (trimZero xs).length ≤ xs.length := by
  simp [trimZero, List.length_dropWhile_le]

def FinFields.sub {p} (xs ys : FinFields p) : FinFields p :=
  trimZero <| (zipWithZeroLeft xs ys).map (fun ⟨x, y⟩ => x - y)

lemma FinFields.sub_length {p} (xs ys : FinFields p) :
  (FinFields.sub xs ys).length ≤ max xs.length ys.length := by
  apply le_trans (trimZero_length _)
  simp [List.length_map, zipWithZeroLeft_length]

def FinFields.add {p} (xs ys : FinFields p) : FinFields p :=
  trimZero <| (zipWithZeroLeft xs ys).map (fun ⟨x, y⟩ => x + y)

lemma FinFields.add_length {p} (xs ys : FinFields p) :
  (FinFields.add xs ys).length ≤ max xs.length ys.length := by
  apply le_trans (trimZero_length _)
  simp [List.length_map, zipWithZeroLeft_length]

def FinFields.mul {p} (xs : FinFields p) : FinFields p → FinFields p
  | [] => []
  | y :: ys =>
    let fromTail := FinFields.mul xs ys
    let fromHead := trimZero <| (xs.map (· * y)) ++ List.replicate ys.length 0
    FinFields.add fromHead fromTail

def FinFields.divMod {p} (xs ys : FinFields p) : FinFields p × FinFields p :=
  match xs, ys with
  | [], _ => ([], [])
  | xs, [] => ([], xs) -- similar to x / 0 = 0, x % 0 = x for Nat
  | x :: xs, y :: ys =>
    if hlt : xs.length < ys.length
    then ([], x :: xs)
    else
      have hle : ys.length ≤ xs.length := by
        rw [not_lt] at hlt; exact hlt
      let c := x * (y⁻¹)
      let zeroes := List.replicate (xs.length - ys.length) 0
      let cys := (ys.map (· * c)) ++ zeroes
      have cys_length : List.length cys = xs.length := by
        simp [cys, zeroes, List.length_append,  List.length_replicate, List.length_map];
        rw [← Nat.add_sub_assoc hle, Nat.add_sub_cancel_left];
      let xs' := FinFields.sub xs cys
      have h : xs'.length < (x :: xs).length := by
        rw [not_lt] at hlt; simp only [xs']
        apply lt_of_le_of_lt (FinFields.sub_length xs cys)
        simp [cys_length]
      let (div, mod) := FinFields.divMod xs' (y :: ys)
      (FinFields.add (c :: zeroes) div, mod)
termination_by xs.length

lemma FinFields.divMod_snd_length {p} (xs) (len) (y) (ys : FinFields p) :
  xs.length ≤ len → (FinFields.divMod xs (y :: ys)).snd.length ≤ ys.length := by
  revert xs
  induction len with
  | zero =>
    intro xs h_eq; rw [Nat.le_zero] at h_eq
    simp [List.length_eq_zero.mp h_eq, divMod]
  | succ len ih =>
    intro xs h_le
    rcases xs with _ | ⟨x, xs⟩ <;> simp [divMod] -- try {simp [divMod]; done}
    split
    · rename (_ < _) => h_lt
      simp [List.length]; apply Nat.succ_le_of_lt h_lt
    · rename (¬ _ < _) => h_le'
      simp [not_lt] at h_le'
      simp [List.length] at h_le
      apply ih
      apply le_trans (FinFields.sub_length _ _)
      simp [List.length_map, List.length_replicate, List.length_append, h_le]
      rw [← Nat.add_sub_assoc h_le', Nat.add_sub_cancel_left];
      apply h_le

def FinFields.div {p} (xs ys : FinFields p) : FinFields p :=
  (FinFields.divMod xs ys).fst

def FinFields.mod {p} (xs ys : FinFields p) : FinFields p :=
  (FinFields.divMod xs ys).snd

def GaloisField.add {p : Nat} {m : FinFields p}
  (xs ys : GaloisField p m) : GaloisField p m :=
  ⟨FinFields.add xs.val ys.val⟩

instance {p m} : HAdd (GaloisField p m) (GaloisField p m) (GaloisField p m) :=
  ⟨@GaloisField.add p m⟩

def GaloisField.sub {p : Nat} {m : FinFields p}
  (xs ys : GaloisField p m) : GaloisField p m :=
  ⟨FinFields.sub xs.val ys.val⟩

instance {p m} : HSub (GaloisField p m) (GaloisField p m) (GaloisField p m) :=
  ⟨@GaloisField.sub p m⟩

def GaloisField.mod {p : Nat} {m : FinFields p}
  (xs ys : GaloisField p m) : GaloisField p m :=
  ⟨FinFields.mod xs.val ys.val⟩

instance : HMod (GaloisField p m) (GaloisField p m) (GaloisField p m) :=
  ⟨GaloisField.mod⟩

def GaloisField.mul {p : Nat} {m : FinFields p}
  (xs ys : GaloisField p m) : GaloisField p m :=
  let product := FinFields.mul xs.val ys.val
  ⟨FinFields.mod product m⟩

instance {p m} : HMul (GaloisField p m) (GaloisField p m) (GaloisField p m) :=
  ⟨@GaloisField.mul p m⟩

def GaloisField.pow {p} {m} (x : GaloisField p m) : Nat → GaloisField p m
  | 0 => 1
  | n@(_ + 1) =>
    let root := GaloisField.pow x (n / 2)
    let whole := GaloisField.mul root root
    if (n % 2) = 0
    then
      whole
    else
      GaloisField.mul whole x

instance {p m} : HPow (GaloisField p m) Nat (GaloisField p m) :=
  ⟨@GaloisField.pow p m⟩

instance {p} : HMul (FinFields p) (FinFields p) (FinFields p) :=
  ⟨FinFields.mul⟩

instance {p} : HSub (FinFields p) (FinFields p) (FinFields p) :=
  ⟨FinFields.sub⟩

instance {p} : HDiv (FinFields p) (FinFields p) (FinFields p) :=
  ⟨FinFields.div⟩

instance {p} : HMod (FinFields p) (FinFields p) (FinFields p) :=
  ⟨FinFields.mod⟩

lemma FinFields.mod_cons_length {p} (y) (xs ys : FinFields p) :
  (xs % (y :: ys)).length < (y :: ys).length := by
  simp [List.length]; apply Nat.lt_succ_of_le
  apply FinFields.divMod_snd_length _ _ _ _ (le_refl _)

def FinFields.euclid {p} (xs ys : FinFields p) :
  FinFields p × FinFields p × FinFields p :=
  match xs, ys with
  | [], [] => ([], [], [])
  | [], ys@(y :: _) => ([0], [y⁻¹], ys.map (· * y⁻¹))
  | xs@(x :: _), [] => ([x⁻¹], [0], xs.map (· * x⁻¹))
  | xs@(_ :: _), ys@(_ :: _) =>
    have h : (xs % ys).length < ys.length := by
      rename (ys = _ :: _) => h_rw; rw [h_rw]
      apply FinFields.mod_cons_length
    let ⟨a, b, d⟩ := FinFields.euclid ys (xs % ys)
    ⟨b, a - (b * (xs / ys)), d⟩
termination_by ys.length

def GaloisField.inv {p} {m} (xs : GaloisField p m) : GaloisField p m :=
  let ⟨c, _, _⟩ := FinFields.euclid xs.val m
  ⟨c % m⟩

instance {p m} : Inv (GaloisField p m) := ⟨GaloisField.inv⟩

def GaloisField.div {p} {m} (xs ys : GaloisField p m) : GaloisField p m :=
  xs * (ys⁻¹)

instance {p m} : HDiv (GaloisField p m) (GaloisField p m) (GaloisField p m) :=
  ⟨GaloisField.div⟩

abbrev BNP2 : Type := EllipticCurve BNF2 0 ((3 : BNF2) / ⟨[1, 9]⟩)--(BNF2.i + (9 : BNF2)))

abbrev BNP : Type := EllipticCurve BNF (0 : BNF) (3 : BNF)

abbrev BNF12 : Type :=
  GaloisField
    altBn128Prime
    [1, 0, 0, 0, 0, 0, .ofInt (-18 : Int), 0, 0, 0, 0, 0, 82]

abbrev BNP12 : Type := EllipticCurve BNF12 (0 : BNF12) (3 : BNF12)

def EllipticCurve.toString {F} {a b} [ToString F] : EllipticCurve F a b → String
  | ⟨x, y⟩ => s!"⟨{x},{y}\n⟩"

instance {F} {a b} [ToString F] : ToString (EllipticCurve F a b) :=
  ⟨EllipticCurve.toString⟩

-- def BNP.mk? (x : Nat) (y : Nat) : Option BNP := do
--   let x' : BNF := FinField.ofNat x
--   let y' : BNF := FinField.ofNat y
--   if (x' = 0 ∧ y' = 0)
--   then some ⟨0, 0⟩
--   else if y' ^ 2 = (x' ^ 3) + 3
--        then some ⟨x', y'⟩
--        else none

def EllipticCurve.isOnCurve {F} [Zero F] [DecidableEq F]
  [HAdd F F F] [HMul F F F] [HPow F Nat F]
  {a b} (p : EllipticCurve F a b) : Prop :=
  (p.x = 0 ∧ p.y = 0) ∨ (p.y ^ 2 = (p.x ^ 3) + (a * p.x) + b)

instance {F} [Zero F] [DecidableEq F]
  [HAdd F F F] [HMul F F F] [HPow F Nat F]
  {a b} {p : EllipticCurve F a b} : Decidable p.isOnCurve :=
  instDecidableOr

def EllipticCurve.mk? {F} [Zero F] [DecidableEq F]
  [HAdd F F F] [HMul F F F] [HPow F Nat F]
  {a b} (x y : F) : Option (EllipticCurve F a b) :=
  let p : EllipticCurve F a b := ⟨x, y⟩
  if p.isOnCurve
  then some p
  else none

-- def EllipticCurve.mk? {F} [Zero F] [DecidableEq F]
--   [HAdd F F F] [HMul F F F] [HPow F Nat F]
--   {a b} (x y : F) : Option (EllipticCurve F a b) :=
--   if (x = 0 ∧ y = 0)
--   then some ⟨0, 0⟩
--   else
--     if y ^ 2 = (x ^ 3) + (a * x) + b
--     then some ⟨x, y⟩
--     else none

def BNP.mk? (x : Nat) (y : Nat) : Option BNP :=
  EllipticCurve.mk? (FinField.ofNat x) (FinField.ofNat y)


/-
def double(self: T) -> T:
    """
    Add a point to itself.
    """
    x, y, F = self.x, self.y, self.FIELD
    if x == 0 and y == 0:
        return self
    lam = (F.from_int(3) * x**2 + self.A) / (F.from_int(2) * y)
    new_x = lam**2 - x - x
    new_y = lam * (x - new_x) - y
    return self.__new__(type(self), new_x, new_y)
-/
def EllipticCurve.double {F} [Zero F] [DecidableEq F]
  [HAdd F F F] [HSub F F F] [HMul F F F] [HDiv F F F]
  [HPow F Nat F] [OfNat F 3] [OfNat F 2]
  [ToString F]
  {a b} (p : EllipticCurve F a b) : EllipticCurve F a b :=
  if p.x = 0 ∧ p.y = 0
  then
    p
  else
    let lam : F := (3 * (p.x ^ 2) + a) / (2 * p.y)
    let x : F := lam ^ 2 - p.x - p.x
    let y : F := lam * (p.x - x) - p.y
    ⟨x, y⟩

/-
def __add__(self: T, other: T) -> T:
    """
    Add two points together.
    """
    ZERO = self.FIELD.zero()
    self_x, self_y, other_x, other_y = self.x, self.y, other.x, other.y
    if self_x == ZERO and self_y == ZERO:
        return other
    if other_x == ZERO and other_y == ZERO:
        return self
    if self_x == other_x:
        if self_y == other_y:
            return self.double()
        else:
            return self.point_at_infinity()
    lam = (other_y - self_y) / (other_x - self_x)
    x = lam**2 - self_x - other_x
    y = lam * (self_x - x) - self_y
    return self.__new__(type(self), x, y)
-/
def EllipticCurve.add {F} [Zero F] [DecidableEq F]
  [HAdd F F F] [HSub F F F] [HMul F F F] [HDiv F F F]
  [HPow F Nat F] [OfNat F 3] [OfNat F 2]
  [ToString F]
  {a b} (p q : EllipticCurve F a b) : EllipticCurve F a b :=
  if p.x = 0 ∧ p.y = 0
  then q
  else
    if q.x = 0 ∧ q.y = 0
    then p
    else
      if p.x = q.x
      then
        if p.y = q.y
        then EllipticCurve.double p
        else ⟨0, 0⟩ -- point at infinity
      else
        let yDiff := q.y - p.y
        let xDiff := q.x - p.x
        let lam : F := yDiff / xDiff
        let x : F := lam ^ 2 - p.x - q.x
        let y : F := lam * (p.x - x) - p.y
        ⟨x, y⟩

instance {F} [Zero F] [DecidableEq F] [HAdd F F F] [HSub F F F]
  [HMul F F F] [HDiv F F F] [HPow F Nat F] [OfNat F 3] [OfNat F 2] {a b}
  [ToString F]
  :
  HAdd (EllipticCurve F a b) (EllipticCurve F a b) (EllipticCurve F a b) :=
  ⟨EllipticCurve.add⟩

def EllipticCurve.mulBy {F} [Zero F] [DecidableEq F]
  [HAdd F F F] [HSub F F F] [HMul F F F] [HDiv F F F]
  [HPow F Nat F] [OfNat F 3] [OfNat F 2]
  [ToString F]
  {a b} (p : EllipticCurve F a b) : Nat → EllipticCurve F a b
  | 0 => ⟨0, 0⟩
  | n@(_ + 1) =>
    let half := EllipticCurve.mulBy p (n / 2)
    let whole := half + half
    if (n % 2) = 0
    then whole
    else whole + p

instance {F} [Zero F] [DecidableEq F] [HAdd F F F] [HSub F F F]
  [HMul F F F] [HDiv F F F] [HPow F Nat F] [OfNat F 3] [OfNat F 2] {a b}
  [ToString F]

  :
  HMul (EllipticCurve F a b) Nat (EllipticCurve F a b) :=
  ⟨EllipticCurve.mulBy⟩

def BNP.toB8L (p : BNP) : B8L :=
  p.x.val.toB8L.pack 32 ++ p.y.val.toB8L.pack 32

def BNP.toBNP12 : BNP → BNP12
  | ⟨x, y⟩ => ⟨⟨[x]⟩, ⟨[y]⟩⟩

-- # "Twist" a point in E(FQ2) into a point in E(FQ12)
-- w = FQ12([0, 1] + [0] * 10)
--
-- def twist(pt: Optimized_Point3D[FQP]) -> Optimized_Point3D[FQ12]:
--     _x, _y, _z = pt
--     # Field isomorphism from Z[p] / x**2 to Z[p] / x**2 - 18*x + 82
--     xcoeffs = [_x.coeffs[0] - _x.coeffs[1] * 9, _x.coeffs[1]]
--     ycoeffs = [_y.coeffs[0] - _y.coeffs[1] * 9, _y.coeffs[1]]
--     zcoeffs = [_z.coeffs[0] - _z.coeffs[1] * 9, _z.coeffs[1]]
--     nx = FQ12([xcoeffs[0]] + [0] * 5 + [xcoeffs[1]] + [0] * 5)
--     ny = FQ12([ycoeffs[0]] + [0] * 5 + [ycoeffs[1]] + [0] * 5)
--     nz = FQ12([zcoeffs[0]] + [0] * 5 + [zcoeffs[1]] + [0] * 5)
--     return (nx * w**2, ny * w**3, nz)
def twist (p : BNP2) : BNP12 :=
  let xs := List.ekat 2 p.x.val
  let ys := List.ekat 2 p.y.val
  let x0 := xs.get! 0
  let x1 := xs.get! 1
  let y0 := ys.get! 0
  let y1 := ys.get! 1
  let nx : BNF12 := ⟨[x0, 0, 0, 0, 0, 0, x1 - (x0 * 9)]⟩
  let ny : BNF12 := ⟨[y0, 0, 0, 0, 0, 0, y1 - (y0 * 9)]⟩
  let w : BNF12 := ⟨[1, 0]⟩
  ⟨nx * (w ^ 2), ny * (w ^ 3)⟩

def pseudoBinaryEncoding : List Int :=
  [
    0, 0, 0, 1, 0, 1, 0, -1,
    0, 0, 1, -1, 0, 0, 1, 0,
    0, 1, 1, 0, -1, 0, 0, 1,
    0, -1, 0, 0, 0, 0, 1, 1,
    1, 0, 0, -1, 0, 0, 1, 0,
    0, 0, 0, 0, -1, 0, 0, 1,
    1, 0, 0, -1, 0, 0, 0, 1,
    1, 0, -1, 0, 0, 1, 0, 1,
    1,
  ]

/-
# Create a function representing the line between P1 and P2,
# and evaluate it at T. Returns a numerator and a denominator
# to avoid unneeded divisions
def linefunc(
    P1: Optimized_Point3D[Optimized_Field],
    P2: Optimized_Point3D[Optimized_Field],
    T: Optimized_Point3D[Optimized_Field],
) -> Optimized_Point2D[Optimized_Field]:
    zero = P1[0].zero()
    x1, y1, z1 = P1
    x2, y2, z2 = P2
    xt, yt, zt = T
-/
def linefunc : BNP12 →  BNP12 → BNP12 → BNP12
  | ⟨x1, y1⟩, ⟨x2, y2⟩, ⟨xt, yt⟩ =>

/-
    # points in projective coords: (x / z, y / z)
    # hence, m = (y2/z2 - y1/z1) / (x2/z2 - x1/z1)
    # multiply numerator and denominator by z1z2 to get values below
    m_numerator = y2 * z1 - y1 * z2
    m_denominator = x2 * z1 - x1 * z2
    if m_denominator != zero:
        # m * ((xt/zt) - (x1/z1)) - ((yt/zt) - (y1/z1))
        return (
            m_numerator * (xt * z1 - x1 * zt) - m_denominator * (yt * z1 - y1 * zt),
            m_denominator * zt * z1,
        )
    elif m_numerator == zero:
        # m = 3(x/z)^2 / 2(y/z), multiply num and den by z**2
        m_numerator = 3 * x1 * x1
        m_denominator = 2 * y1 * z1
        return (
            m_numerator * (xt * z1 - x1 * zt) - m_denominator * (yt * z1 - y1 * zt),
            m_denominator * zt * z1,
        )
    else:
        return xt * z1 - x1 * zt, z1 * zt
-/
    let mNumerator : BNF12 := y2 - y1
    let mDenominator : BNF12 := x2 - x1
    if mDenominator ≠ 0
    then
      ⟨
        mNumerator * (xt - x1) - mDenominator * (yt - y1),
        mDenominator
      ⟩
    else
      if mNumerator = 0
      then
        let mNumerator := 3 * x1 * x1
        let mDenominator := 2 * y1
        ⟨
          mNumerator * (xt - x1) - mDenominator * (yt - y1),
          mDenominator
        ⟩
      else ⟨xt - x1, 1⟩


def FinFields.neg {p} (xs : FinFields p) : FinFields p :=
  FinFields.sub [] xs

def GaloidField.neg {p} {m} (xs : GaloisField p m) : GaloisField p m := 0 - xs

instance {p} {m} : Neg (GaloisField p m) where
  neg := GaloidField.neg

def EllipticCurve.neg {F} [Neg F] {a b} : EllipticCurve F a b → EllipticCurve F a b
  | ⟨x, y⟩ => ⟨x, -y⟩

/-
def miller_loop(
    Q: Optimized_Point3D[FQ12],
    P: Optimized_Point3D[FQ12],
    final_exponentiate: bool = True,
) -> FQ12:
-/
def millerLoop (q p : BNP12) (finalExp : Bool := true) : Option BNF12 := do

/-
    if Q is None or P is None:
        return FQ12.one()
    R: Optimized_Point3D[FQ12] = Q
    f_num, f_den = FQ12.one(), FQ12.one()
-/

  let mut r : BNP12 := q
  let mut fNum : BNF12 := 1
  let mut fDen : BNF12 := 1

/-
    # for i in range(log_ate_loop_count, -1, -1):
    for v in pseudo_binary_encoding[63::-1]:
        _n, _d = linefunc(R, R, P)
        f_num = f_num * f_num * _n
        f_den = f_den * f_den * _d
        R = double(R)
        # if ate_loop_count & (2**i):
        if v == 1:
            _n, _d = linefunc(R, Q, P)
            f_num = f_num * _n
            f_den = f_den * _d
            R = add(R, Q)
        elif v == -1:
            nQ = neg(Q)
            _n, _d = linefunc(R, nQ, P)
            f_num = f_num * _n
            f_den = f_den * _d
            R = add(R, nQ)
-/
  for v in (pseudoBinaryEncoding.take 64).reverse do
    let ⟨_n, _d⟩ := linefunc r r p
    fNum := fNum * fNum * _n
    fDen := fDen * fDen * _d
    r := r.double

    if v = 1 then do
      let ⟨_n, _d⟩ := linefunc r q p
      fNum := fNum * _n
      fDen := fDen * _d
      r := r + q
    if v = -1 then do
      let nq := EllipticCurve.neg q
      let ⟨_n, _d⟩ := linefunc r nq p
      fNum := fNum * _n
      fDen := fDen * _d
      r := r + nq

/-
    # assert R == multiply(Q, ate_loop_count)
    Q1 = (Q[0] ** field_modulus, Q[1] ** field_modulus, Q[2] ** field_modulus)
    # assert is_on_curve(Q1, b12)
    nQ2 = (Q1[0] ** field_modulus, -Q1[1] ** field_modulus, Q1[2] ** field_modulus)
    # assert is_on_curve(nQ2, b12)
    _n1, _d1 = linefunc(R, Q1, P)
    R = add(R, Q1)
    _n2, _d2 = linefunc(R, nQ2, P)
    f = f_num * _n1 * _n2 / (f_den * _d1 * _d2)
    # R = add(R, nQ2) This line is in many specifications but technically does nothing
    if final_exponentiate:
        return f ** ((field_modulus**12 - 1) // curve_order)
    else:
        return f
-/
  let q1 : BNP12 := ⟨q.x ^ altBn128Prime, q.y ^ altBn128Prime⟩
  let nq2 : BNP12 := ⟨q1.x ^ altBn128Prime , (-q1.y) ^ altBn128Prime⟩
  let ⟨_n1, _d1⟩ := linefunc r q1 p
  r := r + q1
  let ⟨_n2, _d2⟩ := linefunc r nq2 p
  let f := (fNum * _n1 * _n2) / (fDen * _d1 * _d2)

  return (
    if finalExp
    then f ^ ((altBn128Prime ^ 12 - 1) / altBn128CurveOrder)
    else f
  )

def pairing (q : BNP2) (p : BNP) (finalExp : Bool := true) : Option BNF12 := do
  guard q.isOnCurve
  guard p.isOnCurve
  if p = ⟨0, 0⟩ ∨ q = ⟨0, 0⟩ then
    return 1
  millerLoop (twist q) (p.toBNP12) finalExp
