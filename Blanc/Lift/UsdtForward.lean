import Blanc.Lift.Usdt.Jumps
import Blanc.Lift.UsdtForwardSteps
import Blanc.Lift.UsdtFrames

/-!
# USDT: forward runs of `transfer`, `transferFrom` and `balanceOf`
-/

namespace Blanc.Lift.Usdt

open Jaune Blanc Blanc.Lift
open Blanc.Lift.AccumulatedWalk

/-- `m20`. -/
local notation "m20" => Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-- The free-memory pointer, `0x60`. -/
local notation "fp60" => Bytes.toB256 [96]

/-- **Entry 50, SafeMath `sub(y, x)`**, forward. -/
@[irreducible] noncomputable def e50W (sevm : Sevm) (b : Devm) (x y ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // x.toNat ≤ y.toNat → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (x :: y :: ret :: S) M (X + c)) t_2ae0_c50
        (.returned (St b ((y - x) :: S) M X))} :=
  ⟨_, fun hle room X => by
    have hg : B256.gtCheck x y = 0 := B256.gtCheck_eq_zero_of_toNat_le hle
    xrun⟩

/-- **Entry 51, SafeMath `add(y, x)`**, forward. -/
@[irreducible] noncomputable def e51W (sevm : Sevm) (b : Devm) (x y ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // x.toNat + y.toNat < 2 ^ 256 → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (x :: y :: ret :: S) M (X + c)) t_2af9_c51
        (.returned (St b ((y + x) :: S) M X))} :=
  ⟨_, fun hle room X => by
    have hg : B256.ltCheck (y + x) y = 0 := by
      rw [B256.add_comm]
      exact ltCheck_add_zero hle
    xrun⟩

/-- A product that fits divides back. -/
theorem mul_div_back {x y : B256} (hy : y ≠ 0) (h : y.toNat * x.toNat < 2 ^ 256) : (y * x) / y = x := by
  apply B256.toNat_inj
  have hpos : 0 < y.toNat := Nat.pos_of_ne_zero fun e => hy (B256.toNat_inj _ _ (e.trans B256.toNat_zero.symm))
  rw [B256.toNat_div hy, B256.toNat_mul_eq_of_nofm h]
  exact Nat.mul_div_cancel_left _ hpos

/-- **Entry 61, SafeMath `mul(y, x)`, `y = 0`**, forward. -/
@[irreducible] noncomputable def e61ZW (sevm : Sevm) (b : Devm) (x y ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // y = 0 → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (x :: y :: ret :: S) M (X + c)) t_2a03_c61
        (.returned (St b ((y * x) :: S) M X))} :=
  ⟨_, fun hy room X => by
    subst hy
    have e : (0 : B256) * x = Bytes.toB256 [0] := by
      show Nat.toB256 ((0 : B256).toNat * x.toNat) = _
      rw [B256.toNat_zero, Nat.zero_mul]
      rfl
    rw [e]
    xrun⟩

/-- **Entry 61, SafeMath `mul(y, x)`, `y ≠ 0`**, forward: a product that does not fit stops at the
`assert`. -/
@[irreducible] noncomputable def e61NW (sevm : Sevm) (b : Devm) (x y ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // y ≠ 0 → y.toNat * x.toNat < 2 ^ 256 → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (x :: y :: ret :: S) M (X + c)) t_2a03_c61
        (.returned (St b ((y * x) :: S) M X))} :=
  ⟨_, fun hy hm room X => by
    have h0 : B256.eqCheck y 0 = 0 := eqCheck_ne hy
    have h0' : B256.eqCheck y (Bytes.toB256 [0]) = 0 := eqCheck_ne (by rw [lit0]; exact hy)
    have h1 : B256.eqCheck ((y * x) / y) x = 1 := eqCheck_one (mul_div_back hy hm)
    xrun⟩

/-- **Entry 61, SafeMath `mul(y, x)`**, forward. -/
noncomputable def e61W (sevm : Sevm) (b : Devm) (x y ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // y.toNat * x.toNat < 2 ^ 256 → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (x :: y :: ret :: S) M (X + c)) t_2a03_c61
        (.returned (St b ((y * x) :: S) M X))} :=
  if hy : y = 0 then ⟨(e61ZW sevm b x y ret S M).1, fun _ room X => (e61ZW sevm b x y ret S M).2 hy room X⟩
  else ⟨(e61NW sevm b x y ret S M).1, fun hm room X => (e61NW sevm b x y ret S M).2 hy hm room X⟩

/-- **Entry 63, SafeMath `div(y, x)`**, forward. -/
@[irreducible] noncomputable def e63W (sevm : Sevm) (b : Devm) (x y ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // x ≠ 0 → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (x :: y :: ret :: S) M (X + c)) t_2ac5_c63
        (.returned (St b ((y / x) :: S) M X))} :=
  ⟨_, fun hx room X => by
    have h0 : B256.eqCheck x 0 = 0 := eqCheck_ne hx
    xrun⟩

/-! ## The moves -/

/-- The balance key of `a` as the walk computes it. -/
abbrev ky (a : B256) : B256 := mapSlot (m20 &&& (m20 &&& a)) (Bytes.toB256 [2])

/-- The scratch image of one mapping-slot hash. -/
abbrev scr (M : Mem) (k base : B256) : Mem := (M.write 0 k.toBytes).write 32 base.toBytes

/-- The ERC-20 `Transfer` event topic. -/
abbrev transferTopic : B256 := Bytes.toB256 [221, 242, 82, 173, 27, 226, 200, 155, 105, 194, 176, 104,
  252, 55, 141, 170, 149, 43, 167, 241, 99, 196, 161, 22, 40, 245, 90, 77, 245, 35, 179, 239]

/-- The packed read at offset `0` of slot 0, masked as the walk masks the owner. -/
abbrev ownW (w : B256) : B256 :=
  m20 &&& (m20 &&& (m20 &&& w / B256.bexp (Bytes.toB256 [1, 0]) (Bytes.toB256 [0])))

/-- The owner's balance key at base `C`, as the walk computes it. -/
abbrev oky (sevm : Sevm) (C : Devm) : B256 :=
  mapSlot (ownW (C.getStorVal sevm.currentTarget (Bytes.toB256 [0]))) (Bytes.toB256 [2])

/-- The base after a move's debit. -/
def mvDebited (sevm : Sevm) (b : Devm) (v r : B256) : Devm :=
  afterSstore sevm (afterSload sevm b (ky r)) (ky r) (b.getStorVal sevm.currentTarget (ky r) - v)

/-- The base after a move's credit of `a`. -/
def mvCredited (sevm : Sevm) (b : Devm) (v a t r : B256) : Devm :=
  afterSstore sevm (afterSload sevm (mvDebited sevm b v r) (ky t)) (ky t)
    ((mvDebited sevm b v r).getStorVal sevm.currentTarget (ky t) + a)

/-- The base after the two reads of the owner's cut. -/
def ownRead (sevm : Sevm) (C : Devm) : Devm :=
  afterSload sevm (afterSload sevm C (Bytes.toB256 [0])) (oky sevm C)

/-- The base after the owner's credit of `f`. -/
def ownCredited (sevm : Sevm) (C : Devm) (f : B256) : Devm :=
  afterSstore sevm (afterSload sevm (ownRead sevm C) (Bytes.toB256 [0])) (oky sevm (ownRead sevm C))
    ((afterSload sevm C (Bytes.toB256 [0])).getStorVal sevm.currentTarget (oky sevm C) + f)

/-- The base after the owner's event. -/
def ownLogged (sevm : Sevm) (C : Devm) (f r : B256) : Devm :=
  (afterSload sevm (ownCredited sevm C f) (Bytes.toB256 [0])).addLog
    ⟨sevm.currentTarget, [transferTopic, m20 &&& r,
      m20 &&& (m20 &&& ((ownCredited sevm C f).getStorVal sevm.currentTarget (Bytes.toB256 [0]) /
        B256.bexp (Bytes.toB256 [1, 0]) (Bytes.toB256 [0])))], f.toBytes⟩

/-- The image after the owner's cut. -/
abbrev ownMem (sevm : Sevm) (M : Mem) (C : Devm) (f : B256) : Mem :=
  (scr (scr M (ownW (C.getStorVal sevm.currentTarget (Bytes.toB256 [0]))) (Bytes.toB256 [2]))
    (ownW ((ownRead sevm C).getStorVal sevm.currentTarget (Bytes.toB256 [0]))) (Bytes.toB256 [2])).write 96 f.toBytes

/-- The image after a move's four hashes. -/
abbrev mvScr (M : Mem) (t r : B256) : Mem :=
  scr (scr (scr (scr M (m20 &&& (m20 &&& r)) (Bytes.toB256 [2])) (m20 &&& (m20 &&& r)) (Bytes.toB256 [2]))
    (m20 &&& (m20 &&& t)) (Bytes.toB256 [2])) (m20 &&& (m20 &&& t)) (Bytes.toB256 [2])

/-- **The owner's cut of `BasicToken.transfer`**, forward. -/
@[irreducible] noncomputable def e13OW (sevm : Sevm) (C : Devm) (p a f v t ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false → FpM fp60 96 M → S.length < 980 →
      f.toNat + ((afterSload sevm C (Bytes.toB256 [0])).getStorVal sevm.currentTarget (oky sevm C)).toNat < 2 ^ 256 →
      ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm (St C (p :: a :: f :: v :: t :: ret :: S) M (X + c)) t_283a_c13
        (.returned (St ((ownLogged sevm C f sevm.caller.toB256).addLog
            ⟨sevm.currentTarget, [transferTopic, m20 &&& sevm.caller.toB256, m20 &&& t], a.toBytes⟩) S
          ((ownMem sevm M C f).write 96 a.toBytes) X))} :=
  ⟨_, fun fork static hM room hnof X hX => by
    yrun
    xcallM e51W 3 [] hnof (by xroom)
    yrun
    all_goals ((try unfold gCallStipend); omega)⟩

/-- The base `BasicToken.transfer`'s move returns with. -/
def mvPost (sevm : Sevm) (b : Devm) (v f t r : B256) : Devm :=
  if f = 0 then
    (mvCredited sevm b v (v - f) t r).addLog
      ⟨sevm.currentTarget, [transferTopic, m20 &&& r, m20 &&& t], (v - f).toBytes⟩
  else
    (ownLogged sevm (mvCredited sevm b v (v - f) t r) f r).addLog
      ⟨sevm.currentTarget, [transferTopic, m20 &&& r, m20 &&& t], (v - f).toBytes⟩

/-- The image a move returns with. -/
def mvMem (sevm : Sevm) (b : Devm) (M : Mem) (v f t r : B256) : Mem :=
  if f = 0 then (mvScr M t r).write 96 (v - f).toBytes
  else (ownMem sevm (mvScr M t r) (mvCredited sevm b v (v - f) t r) f).write 96 (v - f).toBytes

theorem ky_bal (r : B256) : ky r = balSlot r.toAdr := by
  unfold ky balSlot
  rw [ff20_and_word, ff20_and_word, toAdr_toB256, lit2]

theorem mvDebited_getStor (sevm : Sevm) (b : Devm) (v r : B256) :
    Devm.getStor (mvDebited sevm b v r) sevm.currentTarget = debit (Devm.getStor b sevm.currentTarget) r.toAdr v := by
  unfold mvDebited debit
  simp only [afterSstore_getStor_self, afterSload_getStor, gsv, ky_bal]

theorem mvCredited_getStor (sevm : Sevm) (b : Devm) (v a t r : B256) :
    Devm.getStor (mvCredited sevm b v a t r) sevm.currentTarget =
      credit (debit (Devm.getStor b sevm.currentTarget) r.toAdr v) t.toAdr a := by
  unfold mvCredited credit
  simp only [afterSstore_getStor_self, afterSload_getStor, gsv, ky_bal, mvDebited_getStor]

theorem ownW_eq (w : B256) : ownW w = w.toAdr.toB256 := by
  simp only [ownW, ff20_and_word, toAdr_toB256, div_bexp_zero]

theorem oky_eq (sevm : Sevm) (C : Devm) :
    oky sevm C = balSlot (ownerOf (Devm.getStor C sevm.currentTarget)) := by
  unfold oky balSlot ownerOf
  rw [ownW_eq, lit2, lit0, gsv]

/-- `BasicToken.transfer`'s move at charge `c`. -/
abbrev Move13 (sevm : Sevm) (b : Devm) (p q f v t ret : B256) (S : List B256) (M : Mem) (c : Nat) : Prop :=
  CoveredFork sevm.benvStat.fork → sevm.isStatic = false → FpM fp60 96 M → S.length < 970 →
    MoveOk (Devm.getStor b sevm.currentTarget) sevm.caller t.toAdr v f → ∀ X, 2300 ≤ X →
    SFunc.RunExact cert.prog sevm (St b (p :: q :: f :: v :: t :: ret :: S) M (X + c)) t_26f1_c13
      (.returned (St (mvPost sevm b v f t sevm.caller.toB256) S (mvMem sevm b M v f t sevm.caller.toB256) X))

/-- **`BasicToken.transfer`'s move, no fee**, forward. -/
@[irreducible] noncomputable def e13ZW (sevm : Sevm) (b : Devm) (p q f v t ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // f = 0 → Move13 sevm b p q f v t ret S M c} :=
  ⟨_, fun hf fork static hM room ok X hX => by
    unfold mvPost mvMem
    rw [ite_eq_left hf, ite_eq_left hf]
    have h1 := ok.fee_le
    have h2 : v.toNat ≤ (b.getStorVal sevm.currentTarget (ky sevm.caller.toB256)).toNat := by
      rw [ky_bal, gsv, toAdr_toB256]; exact ok.debit_le
    have h3 : (v - f).toNat + ((mvDebited sevm b v sevm.caller.toB256).getStorVal sevm.currentTarget (ky t)).toNat
        < 2 ^ 256 := by
      rw [gsv, mvDebited_getStor, ky_bal, toAdr_toB256]; exact ok.credit_lt
    have hg : B256.eqCheck (B256.gtCheck f (Bytes.toB256 [0])) 0 ≠ 0 := by
      subst hf; decide
    yrun
    xcallM e50W 3 [] h1 (by xroom)
    yrun
    xcallM e50W 3 [] h2 (by xroom)
    yrun
    xcallM e51W 3 [] h3 (by xroom)
    yrun
    all_goals ((try unfold gCallStipend); omega)⟩

/-- **`BasicToken.transfer`'s move, a fee**, forward. -/
@[irreducible] noncomputable def e13NW (sevm : Sevm) (b : Devm) (p q f v t ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // f ≠ 0 → Move13 sevm b p q f v t ret S M c} :=
  ⟨_, fun hf fork static hM room ok X hX => by
    unfold mvPost mvMem
    rw [ite_eq_right hf, ite_eq_right hf]
    have h1 := ok.fee_le
    have h2 : v.toNat ≤ (b.getStorVal sevm.currentTarget (ky sevm.caller.toB256)).toNat := by
      rw [ky_bal, gsv, toAdr_toB256]; exact ok.debit_le
    have h3 : (v - f).toNat + ((mvDebited sevm b v sevm.caller.toB256).getStorVal sevm.currentTarget (ky t)).toNat
        < 2 ^ 256 := by
      rw [gsv, mvDebited_getStor, ky_bal, toAdr_toB256]; exact ok.credit_lt
    have h4 : f.toNat + ((afterSload sevm (mvCredited sevm b v (v - f) t sevm.caller.toB256) (Bytes.toB256 [0])).getStorVal
        sevm.currentTarget (oky sevm (mvCredited sevm b v (v - f) t sevm.caller.toB256))).toNat < 2 ^ 256 := by
      have := ok.owner_lt hf
      rw [getStorVal_afterSload, oky_eq, gsv, mvCredited_getStor, toAdr_toB256]
      exact this
    have hg : B256.eqCheck (B256.gtCheck f (Bytes.toB256 [0])) 0 = 0 := by
      refine eqCheck_ne fun h0 => hf (B256.toNat_inj _ _ ?_)
      have := toNat_le_of_gtCheck_eq_zero h0
      rw [lit0, B256.toNat_zero] at this
      rw [B256.toNat_zero]
      omega
    yrun
    xcallM e50W 3 [] h1 (by xroom)
    yrun
    xcallM e50W 3 [] h2 (by xroom)
    yrun
    xcallM e51W 3 [] h3 (by xroom)
    yrunTo t_283a_c13
    exact (e13OW sevm (mvCredited sevm b v (v - f) t sevm.caller.toB256) p (v - f) f v t ret S (mvScr M t sevm.caller.toB256)).2 fork static (by xfp) (by xroom) h4 X hX
    all_goals ((try unfold gCallStipend); omega)⟩

/-- **`BasicToken.transfer`'s move**, forward, the fee word on the stack named `f`. -/
noncomputable def e13W (sevm : Sevm) (b : Devm) (p q f0 f v t ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false → FpM fp60 96 M → S.length < 970 →
      f0 = f → MoveOk (Devm.getStor b sevm.currentTarget) sevm.caller t.toAdr v f → ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (p :: q :: f0 :: v :: t :: ret :: S) M (X + c)) t_26f1_c13
        (.returned (St (mvPost sevm b v f t sevm.caller.toB256) S (mvMem sevm b M v f t sevm.caller.toB256) X))} :=
  if hf : f = 0 then
    ⟨(e13ZW sevm b p q f v t ret S M).1, fun fork static hM room e ok X hX => by
      subst e; exact (e13ZW sevm b p q f0 v t ret S M).2 hf fork static hM room ok X hX⟩
  else
    ⟨(e13NW sevm b p q f v t ret S M).1, fun fork static hM room e ok X hX => by
      subst e; exact (e13NW sevm b p q f0 v t ret S M).2 hf fork static hM room ok X hX⟩

/-! ## The fee -/

/-- The fee read from storage is capped at `maximumFee`. -/
abbrev Capped (σ : Stor) (v : B256) : Prop :=
  B256.eqCheck (B256.gtCheck ((v * σ.get (Bytes.toB256 [3])) / Bytes.toB256 [39, 16])
    (σ.get (Bytes.toB256 [4]))) 0 = 0

/-- **The fee rule fits**: `v * basisPointsRate` does not trip SafeMath's `assert`. -/
abbrev FeeFits (σ : Stor) (v : B256) : Prop := v.toNat * (σ.get 3).toNat < 2 ^ 256

/-- The base after the fee rule's reads. -/
noncomputable def feeBase (sevm : Sevm) (b : Devm) (v : B256) : Devm :=
  if Capped (Devm.getStor b sevm.currentTarget) v then
    afterSload sevm (afterSload sevm (afterSload sevm b (Bytes.toB256 [3])) (Bytes.toB256 [4])) (Bytes.toB256 [4])
  else afterSload sevm (afterSload sevm b (Bytes.toB256 [3])) (Bytes.toB256 [4])

theorem feeBase_getStor (sevm : Sevm) (b : Devm) (v : B256) (a : Adr) :
    Devm.getStor (feeBase sevm b v) a = Devm.getStor b a := by
  unfold feeBase
  split <;> simp only [afterSload_getStor]

theorem feeBase_keeps {sevm : Sevm} {pre b : Devm} (h : Keeps sevm pre b) (v : B256) :
    Keeps sevm pre (feeBase sevm b v) := by
  unfold feeBase
  split
  · exact ((h.sload _).sload _).sload _
  · exact (h.sload _).sload _

/-- Entry 60 at charge `c`. -/
abbrev Xfer60 (sevm : Sevm) (b : Devm) (v t ret : B256) (S : List B256) (M : Mem) (c : Nat) : Prop :=
  CoveredFork sevm.benvStat.fork → sevm.isStatic = false → FpM fp60 96 M → S.length < 960 →
    B256.ltCheck (Nat.toB256 sevm.data.length) (Bytes.toB256 [64] + Bytes.toB256 [4]) = 0 →
    FeeFits (Devm.getStor b sevm.currentTarget) v →
    MoveOk (Devm.getStor b sevm.currentTarget) sevm.caller t.toAdr v (feeOf (Devm.getStor b sevm.currentTarget) v) →
    ∀ X, 2300 ≤ X →
    SFunc.RunExact cert.prog sevm (St b (v :: t :: ret :: S) M (X + c)) t_269b_c60
      (.returned (St (mvPost sevm (feeBase sevm b v) v (feeOf (Devm.getStor b sevm.currentTarget) v) t sevm.caller.toB256) S
        (mvMem sevm (feeBase sevm b v) M v (feeOf (Devm.getStor b sevm.currentTarget) v) t sevm.caller.toB256) X))

/-- **Entry 60, `BasicToken.transfer(t, v)`, the fee capped**, forward. -/
@[irreducible] noncomputable def e60CW (sevm : Sevm) (b : Devm) (v t ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // Capped (Devm.getStor b sevm.currentTarget) v → Xfer60 sevm b v t ret S M c} :=
  ⟨_, fun hcap fork static hM room hsz hfee ok X hX => by
    have hm : v.toNat * (b.getStorVal sevm.currentTarget (Bytes.toB256 [3])).toNat < 2 ^ 256 := by
      rw [gsv, lit3]; exact hfee
    have hg : B256.eqCheck (B256.gtCheck ((v * b.getStorVal sevm.currentTarget (Bytes.toB256 [3])) / Bytes.toB256 [39, 16])
        (b.getStorVal sevm.currentTarget (Bytes.toB256 [4]))) 0 = 0 := by
      simp only [gsv]; exact hcap
    have hB : feeBase sevm b v = afterSload sevm (afterSload sevm (afterSload sevm b (Bytes.toB256 [3])) (Bytes.toB256 [4])) (Bytes.toB256 [4]) := by
      unfold feeBase; exact ite_eq_left hcap
    rw [hB] at *
    yrun
    xcallM e61W 3 [] hm (by xroom)
    yrun
    xcallM e63W 3 [] (by decide) (by xroom)
    yrunTo t_26f1_c13
    refine (e13W sevm _ _ _ _ (feeOf (Devm.getStor b sevm.currentTarget) v) v t ret S M).2 fork static hM (by xroom) ?_ ?_ X hX
    · rw [feeOf_cap hcap]
      simp only [afterSload_getStor, gsv]
    · simp only [afterSload_getStor]; exact ok⟩

/-- **Entry 60, `BasicToken.transfer(t, v)`, the fee under its cap**, forward. -/
@[irreducible] noncomputable def e60KW (sevm : Sevm) (b : Devm) (v t ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // ¬ Capped (Devm.getStor b sevm.currentTarget) v → Xfer60 sevm b v t ret S M c} :=
  ⟨_, fun hcap fork static hM room hsz hfee ok X hX => by
    have hm : v.toNat * (b.getStorVal sevm.currentTarget (Bytes.toB256 [3])).toNat < 2 ^ 256 := by
      rw [gsv, lit3]; exact hfee
    have hg : B256.eqCheck (B256.gtCheck ((v * b.getStorVal sevm.currentTarget (Bytes.toB256 [3])) / Bytes.toB256 [39, 16])
        (b.getStorVal sevm.currentTarget (Bytes.toB256 [4]))) 0 ≠ 0 := by
      simp only [gsv]; exact hcap
    have hB : feeBase sevm b v = afterSload sevm (afterSload sevm b (Bytes.toB256 [3])) (Bytes.toB256 [4]) := by
      unfold feeBase; exact ite_eq_right hcap
    rw [hB] at *
    yrun
    xcallM e61W 3 [] hm (by xroom)
    yrun
    xcallM e63W 3 [] (by decide) (by xroom)
    yrunTo t_26f1_c13
    refine (e13W sevm _ _ _ _ (feeOf (Devm.getStor b sevm.currentTarget) v) v t ret S M).2 fork static hM (by xroom) ?_ ?_ X hX
    · rw [feeOf_keep hcap]
      simp only [gsv]
    · simp only [afterSload_getStor]; exact ok⟩

/-- **Entry 60, `BasicToken.transfer(t, v)`**, forward. -/
noncomputable def e60W (sevm : Sevm) (b : Devm) (v t ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // Xfer60 sevm b v t ret S M c} :=
  if hc : Capped (Devm.getStor b sevm.currentTarget) v then
    ⟨(e60CW sevm b v t ret S M).1, (e60CW sevm b v t ret S M).2 hc⟩
  else
    ⟨(e60KW sevm b v t ret S M).1, (e60KW sevm b v t ret S M).2 hc⟩

/-! ## The gate: pause, blacklist and deprecation -/

/-- **The owner has not paused the token.** -/
abbrev NotPaused (σ : Stor) : Prop := flag20 (σ.get 0) = 0

/-- **The owner has not blacklisted `a`.** -/
abbrev NotListed (σ : Stor) (a : Adr) : Prop := listedByte σ a = 0

/-- **The owner has not deprecated the token in favour of an upgraded address.** While the flag is set
these selectors forward to an owner-chosen address, and nothing is claimed. -/
abbrev NotDeprecated (σ : Stor) : Prop := flag20 (σ.get 10) = 0

/-- The base after the gate's three reads, for source word `a`. -/
abbrev gateBase (sevm : Sevm) (b : Devm) (a : B256) : Devm :=
  afterSload sevm (afterSload sevm (afterSload sevm b (Bytes.toB256 [0]))
    (mapSlot (m20 &&& (m20 &&& a)) (Bytes.toB256 [6]))) (Bytes.toB256 [10])

theorem gateBase_getStor (sevm : Sevm) (b : Devm) (a : B256) (x : Adr) :
    Devm.getStor (gateBase sevm b a) x = Devm.getStor b x := by
  simp only [afterSload_getStor]

/-- The gate's three flags, on the words the walk reads. -/
structure GateW (sevm : Sevm) (b : Devm) (a : B256) : Prop where
  paused : (Bytes.toB256 [255] &&& b.getStorVal sevm.currentTarget (Bytes.toB256 [0]) /
    B256.bexp (Bytes.toB256 [1, 0]) (Bytes.toB256 [20])) = 0
  listed : (Bytes.toB256 [255] &&& b.getStorVal sevm.currentTarget (mapSlot a.toAdr.toB256 (Bytes.toB256 [6])) /
    B256.bexp (Bytes.toB256 [1, 0]) (Bytes.toB256 [0])) = 0
  deprecated : (Bytes.toB256 [255] &&& b.getStorVal sevm.currentTarget (Bytes.toB256 [10]) /
    B256.bexp (Bytes.toB256 [1, 0]) (Bytes.toB256 [20])) = 0

theorem gateW_of {sevm : Sevm} {b : Devm} {a : B256}
    (hp : NotPaused (Devm.getStor b sevm.currentTarget))
    (hl : NotListed (Devm.getStor b sevm.currentTarget) a.toAdr)
    (hd : NotDeprecated (Devm.getStor b sevm.currentTarget)) : GateW sevm b a := by
  refine ⟨?_, ?_, ?_⟩
  · rw [gsv, lit0]; exact hp
  · rw [div_bexp_zero, gsv,
      show Bytes.toB256 [6] = 6 by decide]
    exact hl
  · rw [gsv, lit10]; exact hd

/-- **Entry 39, `TetherToken.transfer(t, v)`**, forward. -/
@[irreducible] noncomputable def e39W (sevm : Sevm) (b : Devm) (v t ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false → FpM fp60 96 M → S.length < 950 →
      GateW sevm b sevm.caller.toB256 →
      B256.ltCheck (Nat.toB256 sevm.data.length) (Bytes.toB256 [64] + Bytes.toB256 [4]) = 0 →
      FeeFits (Devm.getStor b sevm.currentTarget) v →
      MoveOk (Devm.getStor b sevm.currentTarget) sevm.caller t.toAdr v (feeOf (Devm.getStor b sevm.currentTarget) v) →
      ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (v :: t :: ret :: S) M (X + c)) t_14f4_c39
        (.returned (St
          (mvPost sevm (feeBase sevm (gateBase sevm b sevm.caller.toB256) v) v
            (feeOf (Devm.getStor b sevm.currentTarget) v) t sevm.caller.toB256) S
          (mvMem sevm (feeBase sevm (gateBase sevm b sevm.caller.toB256) v)
            (scr M (m20 &&& (m20 &&& sevm.caller.toB256)) (Bytes.toB256 [6])) v
            (feeOf (Devm.getStor b sevm.currentTarget) v) t sevm.caller.toB256) X))} :=
  ⟨_, fun fork static hM room gate hsz hfee ok X hX => by
    obtain ⟨g1, g2, g3⟩ := gate
    simp only [toAdr_toB256] at g2
    have e := gateBase_getStor sevm b sevm.caller.toB256 sevm.currentTarget
    have hfee' := hfee
    have ok' := ok
    rw [← e] at hfee' ok'
    rw [← e]
    yrun
    xcallMT e60W 3 [] fork static (by xfp) (by xroom) hsz hfee' ok'
    yrun
    all_goals omega⟩

/-! ## `transferFrom` -/

/-- **The owner's cut of `StandardToken.transferFrom`**, forward. -/
@[irreducible] noncomputable def e11OW (sevm : Sevm) (C : Devm) (p a' f a v t r ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false → FpM fp60 96 M → S.length < 980 →
      f.toNat + ((afterSload sevm C (Bytes.toB256 [0])).getStorVal sevm.currentTarget (oky sevm C)).toNat < 2 ^ 256 →
      ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm (St C (p :: a' :: f :: a :: v :: t :: r :: ret :: S) M (X + c)) t_2487_c11
        (.returned (St ((ownLogged sevm C f r).addLog
            ⟨sevm.currentTarget, [transferTopic, m20 &&& r, m20 &&& t], a'.toBytes⟩) S
          ((ownMem sevm M C f).write 96 a'.toBytes) X))} :=
  ⟨_, fun fork static hM room hnof X hX => by
    yrun
    xcallM e51W 3 [] hnof (by xroom)
    yrun
    all_goals ((try unfold gCallStipend); omega)⟩

/-- `StandardToken.transferFrom`'s move at charge `c`. -/
abbrev Move11 (sevm : Sevm) (b : Devm) (p q f a v t r ret : B256) (S : List B256) (M : Mem) (c : Nat) : Prop :=
  CoveredFork sevm.benvStat.fork → sevm.isStatic = false → FpM fp60 96 M → S.length < 970 →
    MoveOk (Devm.getStor b sevm.currentTarget) r.toAdr t.toAdr v f → ∀ X, 2300 ≤ X →
    SFunc.RunExact cert.prog sevm (St b (p :: q :: f :: a :: v :: t :: r :: ret :: S) M (X + c)) t_233e_c11
      (.returned (St (mvPost sevm b v f t r) S (mvMem sevm b M v f t r) X))

/-- **`StandardToken.transferFrom`'s move, no fee**, forward. -/
@[irreducible] noncomputable def e11ZW (sevm : Sevm) (b : Devm) (p q f a v t r ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // f = 0 → Move11 sevm b p q f a v t r ret S M c} :=
  ⟨_, fun hf fork static hM room ok X hX => by
    unfold mvPost mvMem
    rw [ite_eq_left hf, ite_eq_left hf]
    have h1 := ok.fee_le
    have h2 : v.toNat ≤ (b.getStorVal sevm.currentTarget (ky r)).toNat := by
      rw [ky_bal, gsv]; exact ok.debit_le
    have h3 : (v - f).toNat + ((mvDebited sevm b v r).getStorVal sevm.currentTarget (ky t)).toNat < 2 ^ 256 := by
      rw [gsv, mvDebited_getStor, ky_bal]; exact ok.credit_lt
    have hg : B256.eqCheck (B256.gtCheck f (Bytes.toB256 [0])) 0 ≠ 0 := by
      subst hf; decide
    yrun
    xcallM e50W 3 [] h1 (by xroom)
    yrun
    xcallM e50W 3 [] h2 (by xroom)
    yrun
    xcallM e51W 3 [] h3 (by xroom)
    yrun
    all_goals ((try unfold gCallStipend); omega)⟩

/-- **`StandardToken.transferFrom`'s move, a fee**, forward. -/
@[irreducible] noncomputable def e11NW (sevm : Sevm) (b : Devm) (p q f a v t r ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // f ≠ 0 → Move11 sevm b p q f a v t r ret S M c} :=
  ⟨_, fun hf fork static hM room ok X hX => by
    unfold mvPost mvMem
    rw [ite_eq_right hf, ite_eq_right hf]
    have h1 := ok.fee_le
    have h2 : v.toNat ≤ (b.getStorVal sevm.currentTarget (ky r)).toNat := by
      rw [ky_bal, gsv]; exact ok.debit_le
    have h3 : (v - f).toNat + ((mvDebited sevm b v r).getStorVal sevm.currentTarget (ky t)).toNat < 2 ^ 256 := by
      rw [gsv, mvDebited_getStor, ky_bal]; exact ok.credit_lt
    have h4 : f.toNat + ((afterSload sevm (mvCredited sevm b v (v - f) t r) (Bytes.toB256 [0])).getStorVal
        sevm.currentTarget (oky sevm (mvCredited sevm b v (v - f) t r))).toNat < 2 ^ 256 := by
      have := ok.owner_lt hf
      rw [getStorVal_afterSload, oky_eq, gsv, mvCredited_getStor]
      exact this
    have hg : B256.eqCheck (B256.gtCheck f (Bytes.toB256 [0])) 0 = 0 := by
      refine eqCheck_ne fun h0 => hf (B256.toNat_inj _ _ ?_)
      have := toNat_le_of_gtCheck_eq_zero h0
      rw [lit0, B256.toNat_zero] at this
      rw [B256.toNat_zero]
      omega
    yrun
    xcallM e50W 3 [] h1 (by xroom)
    yrun
    xcallM e50W 3 [] h2 (by xroom)
    yrun
    xcallM e51W 3 [] h3 (by xroom)
    yrunTo t_2487_c11
    exact (e11OW sevm (mvCredited sevm b v (v - f) t r) p (v - f) f a v t r ret S (mvScr M t r)).2 fork static (by xfp)
      (by xroom) h4 X hX
    all_goals ((try unfold gCallStipend); omega)⟩

/-- **`StandardToken.transferFrom`'s move**, forward. -/
noncomputable def e11W (sevm : Sevm) (b : Devm) (p q f0 f a v t r ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false → FpM fp60 96 M → S.length < 970 →
      f0 = f → MoveOk (Devm.getStor b sevm.currentTarget) r.toAdr t.toAdr v f → ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (p :: q :: f0 :: a :: v :: t :: r :: ret :: S) M (X + c)) t_233e_c11
        (.returned (St (mvPost sevm b v f t r) S (mvMem sevm b M v f t r) X))} :=
  if hf : f = 0 then
    ⟨(e11ZW sevm b p q f a v t r ret S M).1, fun fork static hM room e ok X hX => by
      subst e; exact (e11ZW sevm b p q f0 a v t r ret S M).2 hf fork static hM room ok X hX⟩
  else
    ⟨(e11NW sevm b p q f a v t r ret S M).1, fun fork static hM room e ok X hX => by
      subst e; exact (e11NW sevm b p q f0 a v t r ret S M).2 hf fork static hM room ok X hX⟩

/-- The word `uint(-1)`. -/
local notation "mx" => Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
  255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

/-- The allowance key of owner `r`, spender `c`, as the walk computes it. -/
abbrev ak (r c : B256) : B256 :=
  mapSlot (m20 &&& (m20 &&& c)) (mapSlot (m20 &&& (m20 &&& r)) (Bytes.toB256 [5]))

/-- The scratch image of the allowance hash of owner `r`, spender `c`. -/
abbrev am (M : Mem) (r c : B256) : Mem :=
  scr (scr M (m20 &&& (m20 &&& r)) (Bytes.toB256 [5])) (m20 &&& (m20 &&& c))
    (mapSlot (m20 &&& (m20 &&& r)) (Bytes.toB256 [5]))

theorem ak_allow (r : B256) (sp : Adr) : ak r sp.toB256 = allowSlot r.toAdr sp := by
  unfold ak allowSlot
  simp only [ff20_and_word, toAdr_toB256, lit5]

/-- The base after `transferFrom`'s allowance step. -/
noncomputable def spentBase (sevm : Sevm) (b : Devm) (a v r : B256) : Devm :=
  if a = maxUint then b else afterSstore sevm b (ak r sevm.caller.toB256) (a - v)

/-- The image after `transferFrom`'s allowance step. -/
noncomputable def spentMem (sevm : Sevm) (M : Mem) (a r : B256) : Mem :=
  if a = maxUint then M else am M r sevm.caller.toB256

theorem spentBase_getStor (sevm : Sevm) (b : Devm) (a v r : B256)
    (ha : a = (Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sevm.caller)) :
    Devm.getStor (spentBase sevm b a v r) sevm.currentTarget =
      spendStor (Devm.getStor b sevm.currentTarget) r.toAdr sevm.caller v := by
  unfold spentBase spendStor
  rw [← ha]
  split
  · rfl
  · rw [afterSstore_getStor_self, ak_allow]

/-- **Tree `0x2282` of entry 10, a limited allowance**, forward. -/
@[irreducible] noncomputable def e10LW (sevm : Sevm) (b : Devm) (p q f0 f a v t r ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false → FpM fp60 96 M → S.length < 960 →
      f0 = f → a ≠ maxUint → v.toNat ≤ a.toNat →
      MoveOk (Devm.getStor (afterSstore sevm b (ak r sevm.caller.toB256) (a - v)) sevm.currentTarget) r.toAdr t.toAdr v f →
      ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (p :: q :: f0 :: a :: v :: t :: r :: ret :: S) M (X + c)) t_2282_c10
        (.returned (St (mvPost sevm (afterSstore sevm b (ak r sevm.caller.toB256) (a - v)) v f t r) S
          (mvMem sevm (afterSstore sevm b (ak r sevm.caller.toB256) (a - v)) (am M r sevm.caller.toB256) v f t r) X))} :=
  ⟨_, fun fork static hM room e hne hle ok X hX => by
    have hg : B256.eqCheck (B256.ltCheck a mx) 0 = 0 := by
      by_contra c
      exact hne (eq_max_of c)
    yrun
    xcallM e50W 3 [] hle (by xroom)
    yrunTo t_233e_c11
    exact (e11W sevm (afterSstore sevm b (ak r sevm.caller.toB256) (a - v)) p q f0 f a v t r ret S
      (am M r sevm.caller.toB256)).2 fork static (by xfp) (by xroom) e ok X hX
    all_goals ((try unfold gCallStipend); omega)⟩

/-- **Tree `0x2282` of entry 10, an unlimited allowance**, forward. -/
@[irreducible] noncomputable def e10MW (sevm : Sevm) (b : Devm) (p q f0 f a v t r ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false → FpM fp60 96 M → S.length < 960 →
      f0 = f → a = maxUint →
      MoveOk (Devm.getStor b sevm.currentTarget) r.toAdr t.toAdr v f → ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (p :: q :: f0 :: a :: v :: t :: r :: ret :: S) M (X + c)) t_2282_c10
        (.returned (St (mvPost sevm b v f t r) S (mvMem sevm b M v f t r) X))} :=
  ⟨_, fun fork static hM room e he ok X hX => by
    have hg : B256.eqCheck (B256.ltCheck a mx) 0 ≠ 0 := by
      subst he; decide +kernel
    yrunTo t_233e_c11
    exact (e11W sevm b p q f0 f a v t r ret S M).2 fork static hM (by xroom) e ok X hX⟩

/-- **Tree `0x2282` of entry 10**, forward. -/
noncomputable def e10W (sevm : Sevm) (b : Devm) (p q f0 f a v t r ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false → FpM fp60 96 M → S.length < 960 →
      f0 = f → (a ≠ maxUint → v.toNat ≤ a.toNat) →
      MoveOk (Devm.getStor (spentBase sevm b a v r) sevm.currentTarget) r.toAdr t.toAdr v f →
      ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (p :: q :: f0 :: a :: v :: t :: r :: ret :: S) M (X + c)) t_2282_c10
        (.returned (St (mvPost sevm (spentBase sevm b a v r) v f t r) S
          (mvMem sevm (spentBase sevm b a v r) (spentMem sevm M a r) v f t r) X))} :=
  if ha : a = maxUint then
    ⟨(e10MW sevm b p q f0 f a v t r ret S M).1, fun fork static hM room e _ ok X hX => by
      unfold spentBase at ok ⊢
      unfold spentMem
      rw [ite_eq_left ha] at ok ⊢
      rw [ite_eq_left ha]
      exact (e10MW sevm b p q f0 f a v t r ret S M).2 fork static hM room e ha ok X hX⟩
  else
    ⟨(e10LW sevm b p q f0 f a v t r ret S M).1, fun fork static hM room e hle ok X hX => by
      unfold spentBase at ok ⊢
      unfold spentMem
      rw [ite_eq_right ha] at ok ⊢
      rw [ite_eq_right ha]
      exact (e10LW sevm b p q f0 f a v t r ret S M).2 fork static hM room e ha (hle ha) ok X hX⟩

/-- The base `transferFrom`'s body has read its allowance from. -/
abbrev alBase (sevm : Sevm) (b : Devm) (r : B256) : Devm := afterSload sevm b (ak r sevm.caller.toB256)

/-- The base entry 56 returns with. -/
noncomputable abbrev pullPost (sevm : Sevm) (b : Devm) (v t r : B256) : Devm :=
  mvPost sevm (spentBase sevm (feeBase sevm (alBase sevm b r) v)
      (b.getStorVal sevm.currentTarget (ak r sevm.caller.toB256)) v r) v
    (feeOf (Devm.getStor b sevm.currentTarget) v) t r

/-- The image entry 56 returns with. -/
noncomputable abbrev pullMem (sevm : Sevm) (b : Devm) (M : Mem) (v t r : B256) : Mem :=
  mvMem sevm (spentBase sevm (feeBase sevm (alBase sevm b r) v)
      (b.getStorVal sevm.currentTarget (ak r sevm.caller.toB256)) v r)
    (spentMem sevm (am M r sevm.caller.toB256) (b.getStorVal sevm.currentTarget (ak r sevm.caller.toB256)) r)
    v (feeOf (Devm.getStor b sevm.currentTarget) v) t r

/-- The fits of entry 56's allowance debit and move. -/
structure PullMove (σ : Stor) (r sp t : Adr) (v : B256) : Prop where
  fee : FeeFits σ v
  allowance : σ.get (allowSlot r sp) ≠ maxUint → v.toNat ≤ (σ.get (allowSlot r sp)).toNat
  move : MoveOk (spendStor σ r sp v) r t v (feeOf σ v)

/-- Entry 56 at charge `c`. -/
abbrev Pull56 (sevm : Sevm) (b : Devm) (v t r ret : B256) (S : List B256) (M : Mem) (c : Nat) : Prop :=
  CoveredFork sevm.benvStat.fork → sevm.isStatic = false → FpM fp60 96 M → S.length < 940 →
    B256.ltCheck (Nat.toB256 sevm.data.length) (Bytes.toB256 [96] + Bytes.toB256 [4]) = 0 →
    PullMove (Devm.getStor b sevm.currentTarget) r.toAdr sevm.caller t.toAdr v → ∀ X, 2300 ≤ X →
    SFunc.RunExact cert.prog sevm (St b (v :: t :: r :: ret :: S) M (X + c)) t_21ab_c56
      (.returned (St (pullPost sevm b v t r) S (pullMem sevm b M v t r) X))

/-- **Entry 56, `StandardToken.transferFrom(r, t, v)`, the fee capped**, forward. -/
@[irreducible] noncomputable def e56CW (sevm : Sevm) (b : Devm) (v t r ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // Capped (Devm.getStor b sevm.currentTarget) v → Pull56 sevm b v t r ret S M c} :=
  ⟨_, fun hcap fork static hM room hsz pm X hX => by
    obtain ⟨hfee, hal, ok⟩ := pm
    have hm : v.toNat * (b.getStorVal sevm.currentTarget (Bytes.toB256 [3])).toNat < 2 ^ 256 := by
      rw [gsv, lit3]; exact hfee
    have hg : B256.eqCheck (B256.gtCheck ((v * b.getStorVal sevm.currentTarget (Bytes.toB256 [3])) / Bytes.toB256 [39, 16])
        (b.getStorVal sevm.currentTarget (Bytes.toB256 [4]))) 0 = 0 := by
      simp only [gsv]; exact hcap
    have hB : feeBase sevm (alBase sevm b r) v = afterSload sevm (afterSload sevm (afterSload sevm (alBase sevm b r)
        (Bytes.toB256 [3])) (Bytes.toB256 [4])) (Bytes.toB256 [4]) := by
      unfold feeBase; exact ite_eq_left (by simp only [afterSload_getStor]; exact hcap)
    have ha : b.getStorVal sevm.currentTarget (ak r sevm.caller.toB256) =
        (Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sevm.caller) := by rw [gsv, ak_allow]
    unfold pullPost pullMem
    rw [hB]
    yrun
    xcallM e61W 3 [] (by xnorm; with_reducible assumption) (by xroom)
    yrun
    xcallM e63W 3 [] (by decide) (by xroom)
    yrunTo t_2282_c10
    refine (e10W sevm _ _ _ _ (feeOf (Devm.getStor b sevm.currentTarget) v) _ v t r ret S _).2 fork static (by xfp) (by xroom) ?_ ?_ ?_ X hX
    · rw [feeOf_cap hcap]
      simp only [afterSload_getStor, gsv]
    · rw [ha]; exact hal
    · rw [spentBase_getStor _ _ _ _ _ (by simp only [afterSload_getStor, gsv, ak_allow])]
      simp only [afterSload_getStor]
      exact ok⟩

/-- **Entry 56, `StandardToken.transferFrom(r, t, v)`, the fee under its cap**, forward. -/
@[irreducible] noncomputable def e56KW (sevm : Sevm) (b : Devm) (v t r ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // ¬ Capped (Devm.getStor b sevm.currentTarget) v → Pull56 sevm b v t r ret S M c} :=
  ⟨_, fun hcap fork static hM room hsz pm X hX => by
    obtain ⟨hfee, hal, ok⟩ := pm
    have hm : v.toNat * (b.getStorVal sevm.currentTarget (Bytes.toB256 [3])).toNat < 2 ^ 256 := by
      rw [gsv, lit3]; exact hfee
    have hg : B256.eqCheck (B256.gtCheck ((v * b.getStorVal sevm.currentTarget (Bytes.toB256 [3])) / Bytes.toB256 [39, 16])
        (b.getStorVal sevm.currentTarget (Bytes.toB256 [4]))) 0 ≠ 0 := by
      simp only [gsv]; exact hcap
    have hB : feeBase sevm (alBase sevm b r) v = afterSload sevm (afterSload sevm (alBase sevm b r)
        (Bytes.toB256 [3])) (Bytes.toB256 [4]) := by
      unfold feeBase; exact ite_eq_right (by simp only [afterSload_getStor]; exact hcap)
    have ha : b.getStorVal sevm.currentTarget (ak r sevm.caller.toB256) =
        (Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sevm.caller) := by rw [gsv, ak_allow]
    unfold pullPost pullMem
    rw [hB]
    yrun
    xcallM e61W 3 [] (by xnorm; with_reducible assumption) (by xroom)
    yrun
    xcallM e63W 3 [] (by decide) (by xroom)
    yrunTo t_2282_c10
    refine (e10W sevm _ _ _ _ (feeOf (Devm.getStor b sevm.currentTarget) v) _ v t r ret S _).2 fork static (by xfp) (by xroom) ?_ ?_ ?_ X hX
    · rw [feeOf_keep hcap]
      simp only [afterSload_getStor, gsv]
    · rw [ha]; exact hal
    · rw [spentBase_getStor _ _ _ _ _ (by simp only [afterSload_getStor, gsv, ak_allow])]
      simp only [afterSload_getStor]
      exact ok⟩

/-- **Entry 56, `StandardToken.transferFrom(r, t, v)`**, forward. -/
noncomputable def e56W (sevm : Sevm) (b : Devm) (v t r ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // Pull56 sevm b v t r ret S M c} :=
  if hc : Capped (Devm.getStor b sevm.currentTarget) v then
    ⟨(e56CW sevm b v t r ret S M).1, (e56CW sevm b v t r ret S M).2 hc⟩
  else
    ⟨(e56KW sevm b v t r ret S M).1, (e56KW sevm b v t r ret S M).2 hc⟩

/-- **Entry 23, `TetherToken.transferFrom(r, t, v)`**, forward. -/
@[irreducible] noncomputable def e23W (sevm : Sevm) (b : Devm) (v t r ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false → FpM fp60 96 M → S.length < 930 →
      GateW sevm b r →
      B256.ltCheck (Nat.toB256 sevm.data.length) (Bytes.toB256 [96] + Bytes.toB256 [4]) = 0 →
      PullMove (Devm.getStor b sevm.currentTarget) r.toAdr sevm.caller t.toAdr v → ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (v :: t :: r :: ret :: S) M (X + c)) t_0ebd_c23
        (.returned (St (pullPost sevm (gateBase sevm b r) v t r) S
          (pullMem sevm (gateBase sevm b r) (scr M (m20 &&& (m20 &&& r)) (Bytes.toB256 [6])) v t r) X))} :=
  ⟨_, fun fork static hM room gate hsz pm X hX => by
    obtain ⟨g1, g2, g3⟩ := gate
    have e := gateBase_getStor sevm b r sevm.currentTarget
    have pm' := pm
    rw [← e] at pm'
    yrun
    xcallMT e56W 4 [] fork static (by xfp) (by xroom) hsz pm'
    yrun
    all_goals omega⟩

/-! ## `balanceOf` -/

/-- **Entry 57, `BasicToken.balanceOf(a)`**, forward. -/
@[irreducible] noncomputable def e57W (sevm : Sevm) (b : Devm) (a ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → FpM fp60 96 M → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (a :: ret :: S) M (X + c)) t_2652_c57
        (.returned (St (afterSload sevm b (ky a)) (b.getStorVal sevm.currentTarget (ky a) :: S)
          (scr M (m20 &&& (m20 &&& a)) (Bytes.toB256 [2])) X))} :=
  ⟨_, fun fork hM room X => by
    yrun⟩

/-- **Entry 33, `TetherToken.balanceOf(a)`, not deprecated**, forward. -/
@[irreducible] noncomputable def e33W (sevm : Sevm) (b : Devm) (a ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → FpM fp60 96 M → S.length < 990 →
      (Bytes.toB256 [255] &&& b.getStorVal sevm.currentTarget (Bytes.toB256 [10]) /
        B256.bexp (Bytes.toB256 [1, 0]) (Bytes.toB256 [20])) = 0 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (a :: ret :: S) M (X + c)) t_1239_c33
        (.returned (St (afterSload sevm (afterSload sevm b (Bytes.toB256 [10])) (ky a))
          ((afterSload sevm b (Bytes.toB256 [10])).getStorVal sevm.currentTarget (ky a) :: S)
          (scr M (m20 &&& (m20 &&& a)) (Bytes.toB256 [2])) X))} :=
  ⟨_, fun fork hM room hd X => by
    yrun
    xcallM e57W 2 [] fork hM (by xroom)
    yrun⟩

/-! ## The frames -/

/-- A frame's selector word as a solc 0.4 dispatcher reads it. -/
abbrev selL (sevm : Sevm) : B256 :=
  Bytes.toB256 [0xff, 0xff, 0xff, 0xff] &&& Sevm.dataWord sevm (Bytes.toB256 [0x00]) /
    Bytes.toB256 [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

/-- The guards a solc 0.4 prologue, wrapper and `onlyPayloadSize` make, with `n` argument bytes. -/
structure LGuards (sevm : Sevm) (sel n : B256) : Prop where
  value : sevm.value = 0
  short : B256.ltCheck (Nat.toB256 sevm.data.length) (Bytes.toB256 [4]) = 0
  args : B256.ltCheck (Nat.toB256 sevm.data.length) (n + Bytes.toB256 [4]) = 0
  sel : selL sevm = sel

/-- The prologue's image. -/
abbrev mem0 : Mem := Mem.empty.write 64 (fp60).toBytes

/-- **The dispatcher to `transfer`'s wrapper**. -/
@[irreducible] noncomputable def xDisp (sevm : Sevm) (b : Devm) :
    {c : Nat // B256.ltCheck (Nat.toB256 sevm.data.length) (Bytes.toB256 [4]) = 0 → selL sevm = 0xa9059cbb → ∀ o X,
      SFunc.RunExact cert.prog sevm (St b [selL sevm] mem0 X) t_074a_c85 o →
      SFunc.RunExact cert.prog sevm (St b [] Mem.empty (X + c)) t_0000_c0 o} :=
  ⟨_, fun short sel o X k => by
    yrunTo t_074a_c85
    exact rk0 k⟩

/-- **The dispatcher to `transferFrom`'s wrapper**. -/
@[irreducible] noncomputable def pDisp (sevm : Sevm) (b : Devm) :
    {c : Nat // B256.ltCheck (Nat.toB256 sevm.data.length) (Bytes.toB256 [4]) = 0 → selL sevm = 0x23b872dd → ∀ o X,
      SFunc.RunExact cert.prog sevm (St b [selL sevm] mem0 X) t_0333_c70 o →
      SFunc.RunExact cert.prog sevm (St b [] Mem.empty (X + c)) t_0000_c0 o} :=
  ⟨_, fun short sel o X k => by
    yrunTo t_0333_c70
    exact rk0 k⟩

/-- **The dispatcher to `balanceOf`'s wrapper**. -/
@[irreducible] noncomputable def bDisp (sevm : Sevm) (b : Devm) :
    {c : Nat // B256.ltCheck (Nat.toB256 sevm.data.length) (Bytes.toB256 [4]) = 0 → selL sevm = 0x70a08231 → ∀ o X,
      SFunc.RunExact cert.prog sevm (St b [selL sevm] mem0 X) t_05b0_c80 o →
      SFunc.RunExact cert.prog sevm (St b [] Mem.empty (X + c)) t_0000_c0 o} :=
  ⟨_, fun short sel o X k => by
    yrunTo t_05b0_c80
    exact rk0 k⟩

/-- `transfer`'s arguments as its wrapper decodes them. -/
abbrev xTo (sevm : Sevm) : B256 := m20 &&& Sevm.dataWord sevm (Bytes.toB256 [4])
abbrev xVal (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4])

/-- The base `transfer` halts with. -/
noncomputable def xferBase (sevm : Sevm) (b : Devm) : Devm :=
  mvPost sevm (feeBase sevm (gateBase sevm b sevm.caller.toB256) (xVal sevm)) (xVal sevm)
    (feeOf (Devm.getStor b sevm.currentTarget) (xVal sevm)) (xTo sevm) sevm.caller.toB256

/-- The image `transfer` halts with. -/
noncomputable def xferMem (sevm : Sevm) (b : Devm) : Mem :=
  mvMem sevm (feeBase sevm (gateBase sevm b sevm.caller.toB256) (xVal sevm))
    (scr (Mem.empty.write 64 (fp60).toBytes) (m20 &&& (m20 &&& sevm.caller.toB256)) (Bytes.toB256 [6])) (xVal sevm)
    (feeOf (Devm.getStor b sevm.currentTarget) (xVal sevm)) (xTo sevm) sevm.caller.toB256

/-- **The `transfer` frame, forward**: it stops, with an empty reply. -/
@[irreducible] noncomputable def xferW (sevm : Sevm) (b : Devm) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      LGuards sevm 0xa9059cbb (Bytes.toB256 [64]) → GateW sevm b sevm.caller.toB256 →
      FeeFits (Devm.getStor b sevm.currentTarget) (xVal sevm) →
      MoveOk (Devm.getStor b sevm.currentTarget) sevm.caller (xTo sevm).toAdr (xVal sevm)
        (feeOf (Devm.getStor b sevm.currentTarget) (xVal sevm)) → ∀ G, 2300 ≤ G →
      SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + c)) t_0000_c0
        (.halted (St (xferBase sevm b) [selL sevm] (xferMem sevm b) G))} :=
  ⟨_, fun fork static facts gate hfee ok G hG => by
    obtain ⟨value, short, args, sel⟩ := facts
    apply rk
    refine (xDisp sevm b).2 short sel _ _ ?_
    yrun
    xcallMT e39W 3 [] fork static (by xfp) (by xroom) gate args hfee ok
    yrun
    exact rk0 rx_stop
    all_goals omega⟩

/-- `transferFrom`'s arguments as its wrapper decodes them. -/
abbrev pSrc (sevm : Sevm) : B256 := m20 &&& Sevm.dataWord sevm (Bytes.toB256 [4])
abbrev pTo (sevm : Sevm) : B256 := m20 &&& Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4])
abbrev pVal (sevm : Sevm) : B256 :=
  Sevm.dataWord sevm (Bytes.toB256 [32] + (Bytes.toB256 [32] + Bytes.toB256 [4]))

/-- **The `transferFrom` frame, forward**: it stops, with an empty reply. -/
@[irreducible] noncomputable def pullW (sevm : Sevm) (b : Devm) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      LGuards sevm 0x23b872dd (Bytes.toB256 [96]) → GateW sevm b (pSrc sevm) →
      PullMove (Devm.getStor b sevm.currentTarget) (pSrc sevm).toAdr sevm.caller (pTo sevm).toAdr (pVal sevm) →
      ∀ G, 2300 ≤ G →
      SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + c)) t_0000_c0
        (.halted (St (pullPost sevm (gateBase sevm b (pSrc sevm)) (pVal sevm) (pTo sevm) (pSrc sevm)) [selL sevm]
          (pullMem sevm (gateBase sevm b (pSrc sevm))
            (scr (Mem.empty.write 64 (fp60).toBytes) (m20 &&& (m20 &&& pSrc sevm)) (Bytes.toB256 [6]))
            (pVal sevm) (pTo sevm) (pSrc sevm)) G))} :=
  ⟨_, fun fork static facts gate pm G hG => by
    obtain ⟨value, short, args, sel⟩ := facts
    apply rk
    refine (pDisp sevm b).2 short sel _ _ ?_
    yrun
    xcallMT e23W 4 [] fork static (by xfp) (by xroom) gate args pm
    yrun
    exact rk0 rx_stop
    all_goals omega⟩

/-- `balanceOf`'s argument as its wrapper decodes it. -/
abbrev bHolder (sevm : Sevm) : B256 := m20 &&& Sevm.dataWord sevm (Bytes.toB256 [4])

/-- The answer of `balanceOf`. -/
abbrev bAns (sevm : Sevm) (b : Devm) : B256 :=
  (afterSload sevm b (Bytes.toB256 [10])).getStorVal sevm.currentTarget (ky (bHolder sevm))

/-- The halting state of a frame returning the word `w` at the pointer `0x60`. -/
def ret60 (B : Devm) (S : List B256) (M : Mem) (w : B256) (G : Nat) : Devm :=
  ((St B S M G).memRead (fp60).toNat (Bytes.toB256 [32] + fp60 - fp60).toNat).2.withOutput w.toBytes

/-- The image `balanceOf` halts with. -/
abbrev balMem (sevm : Sevm) (b : Devm) : Mem :=
  (scr (Mem.empty.write 64 (fp60).toBytes) (m20 &&& (m20 &&& bHolder sevm)) (Bytes.toB256 [2])).write 96 (bAns sevm b).toBytes

/-- The base `balanceOf` halts with. -/
abbrev balBase (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm (afterSload sevm b (Bytes.toB256 [10])) (ky (bHolder sevm))

/-- **The `balanceOf` frame, not deprecated, forward**, static or not. -/
@[irreducible] noncomputable def balW (sevm : Sevm) (b : Devm) :
    {c : Nat // CoveredFork sevm.benvStat.fork → LGuards sevm 0x70a08231 (Bytes.toB256 [32]) →
      (Bytes.toB256 [255] &&& b.getStorVal sevm.currentTarget (Bytes.toB256 [10]) /
        B256.bexp (Bytes.toB256 [1, 0]) (Bytes.toB256 [20])) = 0 → ∀ G,
      SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + c)) t_0000_c0
        (.halted (ret60 (balBase sevm b) [selL sevm] (balMem sevm b) (bAns sevm b) G))} :=
  ⟨_, fun fork facts hd G => by
    obtain ⟨value, short, args, sel⟩ := facts
    apply rk
    refine (bDisp sevm b).2 short sel _ _ ?_
    yrun
    xcallM e33W 2 [] fork (by xfp) (by xroom) hd
    yrun
    refine rk0 ?_
    exact rx_returnAt (i0 := 96) (n := 128) rfl (by xfp) (by xfp) (by decide) (by decide) (by decide)⟩

/-! ## The charges -/

section Charges

variable (sevm : Sevm) (b : Devm) (p q f0 f v t r a ret : B256) (S : List B256) (M : Mem) (n : Nat)

theorem e50W_le : (e50W sevm b v t ret S M).1 ≤ 68 := by
  unfold e50W; dsimp only; xcost []

theorem e51W_le : (e51W sevm b v t ret S M).1 ≤ 81 := by
  unfold e51W; dsimp only; xcost []

theorem e61ZW_le : (e61ZW sevm b v t ret S M).1 ≤ 72 := by
  unfold e61ZW; dsimp only; xcost []

theorem e61NW_le : (e61NW sevm b v t ret S M).1 ≤ 138 := by
  unfold e61NW; dsimp only; xcost []

theorem e61W_le : (e61W sevm b v t ret S M).1 ≤ 138 := by
  unfold e61W
  split
  · exact (e61ZW_le ..).trans (by decide)
  · exact (e61NW_le ..).trans (by decide)

theorem e63W_le : (e63W sevm b v t ret S M).1 ≤ 74 := by
  unfold e63W; dsimp only; xcost []

theorem e13OW_le : (e13OW sevm b p q f v t ret S M).1 ≤ 34597 := by
  unfold e13OW; dsimp only; xcost [e51W_le, memC_le]

theorem e13ZW_le : (e13ZW sevm b p q f v t ret S M).1 ≤ 50986 := by
  unfold e13ZW; dsimp only; xcost [e50W_le, e51W_le, memC_le]

theorem e13NW_le : (e13NW sevm b p q f v t ret S M).1 ≤ 83733 := by
  unfold e13NW; dsimp only; xcost [e50W_le, e51W_le, memC_le, e13OW_le]

theorem e13W_le : (e13W sevm b p q f0 f v t ret S M).1 ≤ 83733 := by
  unfold e13W
  split
  · exact (e13ZW_le ..).trans (by decide)
  · exact (e13NW_le ..).trans (by decide)

theorem e60CW_le : (e60CW sevm b v t ret S M).1 ≤ 90407 := by
  unfold e60CW; dsimp only; xcost [e61W_le, e63W_le, e13W_le]

theorem e60KW_le : (e60KW sevm b v t ret S M).1 ≤ 88299 := by
  unfold e60KW; dsimp only; xcost [e61W_le, e63W_le, e13W_le]

theorem e60W_le : (e60W sevm b v t ret S M).1 ≤ 90407 := by
  unfold e60W
  split
  · exact (e60CW_le ..).trans (by decide)
  · exact (e60KW_le ..).trans (by decide)

theorem e39W_le : (e39W sevm b v t ret S M).1 ≤ 97111 := by
  unfold e39W; dsimp only; xcost [e60W_le, memC_le]

theorem xDisp_le : (xDisp sevm b).1 ≤ 546 := by
  unfold xDisp; dsimp only; xcost []

theorem xferW_le : (xferW sevm b).1 ≤ 97756 := by
  unfold xferW; dsimp only; xcost [xDisp_le, e39W_le]

theorem e11OW_le (a' : B256) : (e11OW sevm b p a' q a v t r ret S M).1 ≤ 34603 := by
  unfold e11OW; dsimp only; xcost [e51W_le, memC_le]

theorem e11ZW_le : (e11ZW sevm b p q f a v t r ret S M).1 ≤ 50993 := by
  unfold e11ZW; dsimp only; xcost [e50W_le, e51W_le, memC_le]

theorem e11NW_le : (e11NW sevm b p q f a v t r ret S M).1 ≤ 83741 := by
  unfold e11NW; dsimp only; xcost [e50W_le, e51W_le, memC_le, e11OW_le]

theorem e11W_le : (e11W sevm b p q f0 f a v t r ret S M).1 ≤ 83741 := by
  unfold e11W
  split
  · exact (e11ZW_le ..).trans (by decide)
  · exact (e11NW_le ..).trans (by decide)

theorem e10LW_le : (e10LW sevm b p q f0 f a v t r ret S M).1 ≤ 106161 := by
  unfold e10LW; dsimp only; xcost [e50W_le, e11W_le]

theorem e10MW_le : (e10MW sevm b p q f0 f a v t r ret S M).1 ≤ 83767 := by
  unfold e10MW; dsimp only; xcost [e11W_le]

theorem e10W_le : (e10W sevm b p q f0 f a v t r ret S M).1 ≤ 106161 := by
  unfold e10W
  split
  · exact (e10MW_le ..).trans (by decide)
  · exact (e10LW_le ..).trans (by decide)

theorem e56CW_le : (e56CW sevm b v t r ret S M).1 ≤ 115125 := by
  unfold e56CW; dsimp only; xcost [e61W_le, e63W_le, e10W_le]

theorem e56KW_le : (e56KW sevm b v t r ret S M).1 ≤ 113017 := by
  unfold e56KW; dsimp only; xcost [e61W_le, e63W_le, e10W_le]

theorem e56W_le : (e56W sevm b v t r ret S M).1 ≤ 115125 := by
  unfold e56W
  split
  · exact (e56CW_le ..).trans (by decide)
  · exact (e56KW_le ..).trans (by decide)

theorem e23W_le : (e23W sevm b v t r ret S M).1 ≤ 121835 := by
  unfold e23W; dsimp only; xcost [e56W_le]

theorem pDisp_le : (pDisp sevm b).1 ≤ 216 := by
  unfold pDisp; dsimp only; xcost []

theorem pullW_le : (pullW sevm b).1 ≤ 122180 := by
  unfold pullW; dsimp only; xcost [pDisp_le, e23W_le]

theorem e57W_le : (e57W sevm b a ret S M).1 ≤ 2218 := by
  unfold e57W; dsimp only; xcost []

theorem e33W_le : (e33W sevm b a ret S M).1 ≤ 4468 := by
  unfold e33W; dsimp only; xcost [e57W_le]

theorem bDisp_le : (bDisp sevm b).1 ≤ 436 := by
  unfold bDisp; dsimp only; xcost []

theorem balW_le : (balW sevm b).1 ≤ 5031 := by
  unfold balW; dsimp only; xcost [bDisp_le, e33W_le, memC_le]

end Charges

end Blanc.Lift.Usdt
