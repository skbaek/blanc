import Blanc.Composition.Curve3PoolExitView

/-!
# Each coin's `transfer` from a cold start: cost, refund, storage

The closed sums of `DaiExact`, `UsdtExact` and `UsdcExact`, evaluated where every slot of the coin is cold and at its
value at the transaction's start. `debitG` and `creditG` are the two stores' value classes.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.Lift.AccumulatedWalk
open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.Curve3PoolCoinExactKit

/-- A debit's store: unchanged when nothing moves. -/
def debitG (v : Nat) : Nat := if v = 0 then 100 else 2900

/-- A credit's store: `startsEntry` more when it starts an empty entry. -/
def creditG (y v : Nat) : Nat := debitG v + startsEntry y v

theorem debit_class {x v : B256} (hv : v.toNat ≤ x.toNat) : sstoreValueCost x x (x - v) = debitG v.toNat := by
  rw [first_value]
  unfold debitG
  have hsub := B256.toNat_sub_eq_of_le x v (B256.le_iff_toNat_le_toNat.2 hv)
  by_cases h0 : v.toNat = 0
  · have hv0 : v = 0 := B256.toNat_inj _ _ h0
    subst hv0
    rw [ite_eq_left (B256.toNat_inj _ _ (by omega)), ite_eq_left h0]
  · have hne : x ≠ x - v := fun e => by
      have := congrArg B256.toNat e
      omega
    have hx0 : x ≠ 0 := fun e => by
      rw [e] at hv
      have : (0 : B256).toNat = 0 := by decide
      omega
    rw [ite_eq_right hne, ite_eq_right hx0, ite_eq_right h0]

theorem credit_class {y v : B256} (hv : v.toNat + y.toNat < 2 ^ 256) :
    sstoreValueCost y y (y + v) = creditG y.toNat v.toNat := by
  rw [first_value]
  unfold creditG debitG startsEntry
  have hadd : (y + v).toNat = y.toNat + v.toNat := B256.toNat_add_eq_of_nof _ _ (by unfold B256.Nof; omega)
  have h00 : (0 : B256).toNat = 0 := by decide
  by_cases h0 : v.toNat = 0
  · rw [ite_eq_left (B256.toNat_inj _ _ (by omega)), ite_eq_left h0, ite_eq_right (by omega)]
  · have hne : y ≠ y + v := fun e => by
      have := congrArg B256.toNat e
      omega
    rw [ite_eq_right hne, ite_eq_right h0]
    by_cases hy : y.toNat = 0
    · have hy0 : y = 0 := B256.toNat_inj _ _ (by omega)
      rw [ite_eq_left hy0, ite_eq_left ⟨hy, by omega⟩]
    · have hy0 : y ≠ 0 := fun e => hy (by rw [e]; exact h00)
      rw [ite_eq_right hy0, ite_eq_right (fun e => hy e.1)]

/-- The refund of a debit that empties a word. -/
theorem debit_refund {x v : B256} (hv : v.toNat ≤ x.toNat) (g : GasSchedule) (hg : g.storageClearRefund = 4800) (rc : Int) :
    sstoreNewRefundCounter g (x - v) x x rc = rc + ((4800 * empties x.toNat v.toNat : Nat) : Int) := by
  rw [first_refund, hg]
  have hsub := B256.toNat_sub_eq_of_le x v (B256.le_iff_toNat_le_toNat.2 hv)
  have h00 : (0 : B256).toNat = 0 := by decide
  unfold empties
  by_cases h : 0 < v.toNat ∧ v.toNat = x.toNat
  · rw [ite_eq_left h, ite_eq_left ⟨fun e => by rw [e] at h; omega, B256.toNat_inj _ _ (by omega)⟩]
  · rw [ite_eq_right h, ite_eq_right (fun e => by
      have e2 := congrArg B256.toNat e.2
      have e1 : x.toNat ≠ 0 := fun e' => e.1 (B256.toNat_inj _ _ (by omega))
      omega)]
    rfl

/-- A credit that fits refunds nothing. -/
theorem credit_refund {y v : B256} (hv : v.toNat + y.toNat < 2 ^ 256) (g : GasSchedule) (rc : Int) :
    sstoreNewRefundCounter g (y + v) y y rc = rc := by
  have hadd : (y + v).toNat = y.toNat + v.toNat := B256.toNat_add_eq_of_nof _ _ (by unfold B256.Nof; omega)
  have h00 : (0 : B256).toNat = 0 := by decide
  rw [first_refund, ite_eq_right (fun e => by
    have e2 := congrArg B256.toNat e.2
    have e1 : y.toNat ≠ 0 := fun e' => e.1 (B256.toNat_inj _ _ (by omega))
    omega), Int.add_zero]

section Store

variable {s : Sevm} {b : Devm} {K : List B256} {σ : Stor}

/-- A frame's own first store to a slot, at its transaction-start value. -/
structure Fresh (s : Sevm) (b : Devm) (k : B256) (x : B256) : Prop where
  clean : Clean b
  orig : (getOrigAcct s s.currentTarget).stor.get k = x
  cur : b.getStorVal s.currentTarget k = x

theorem mv_debit {k x v : B256} (h : Fresh s b k x) (hv : v.toNat ≤ x.toNat) (hg : s.benvStat.rules.gas.storageClearRefund = 4800) :
    Mv [s.currentTarget] ((4800 * empties x.toNat v.toNat : Nat) : Int) b (afterSstore s b k (x - v)) :=
  mv_afterSstore s b k _ (by rw [h.clean.orig, h.orig, h.cur, debit_refund hv _ hg])

theorem mv_credit {k y v : B256} (h : Fresh s b k y) (hv : v.toNat + y.toNat < 2 ^ 256) :
    Mv [s.currentTarget] 0 b (afterSstore s b k (y + v)) :=
  mv_afterSstore s b k _ (by rw [h.clean.orig, h.orig, h.cur, credit_refund hv, Int.add_zero])

theorem cost_debit {K : List B256} {k x v : B256} (h : Fresh s b k x) (hA : At s.currentTarget K σ b) (hk : k ∈ K)
    (hv : v.toNat ≤ x.toNat) : sstoreCost s b k (x - v) = debitG v.toNat := by
  rw [hA.sstoreCost_warm hk, h.clean.orig, h.orig, ← hA.val, h.cur, debit_class hv]

theorem cost_credit {K : List B256} {k y v : B256} (h : Fresh s b k y) (hA : At s.currentTarget K σ b) (hk : k ∈ K)
    (hv : v.toNat + y.toNat < 2 ^ 256) : sstoreCost s b k (y + v) = creditG y.toNat v.toNat := by
  rw [hA.sstoreCost_warm hk, h.clean.orig, h.orig, ← hA.val, h.cur, credit_class hv]

end Store

/-! ## A move -/

section Move

variable {s : Sevm} {a : Devm} {K : List B256} {σ : Stor} {kr kt v u : B256}

/-- The two stores of a move, over `a`: the debit `x - v` at `kr`, then the credit `y + u` at `kt`. -/
def moved (s : Sevm) (a : Devm) (kr kt v u : B256) : Devm :=
  afterSstore s (afterSload s (afterSstore s (afterSload s a kr) kr (a.getStorVal s.currentTarget kr - v)) kt) kt
    ((afterSstore s (afterSload s a kr) kr (a.getStorVal s.currentTarget kr - v)).getStorVal s.currentTarget kt + u)

/-- **A move, its slots at their transaction-start values, the word sums fitting.** -/
theorem move_view (hg : s.benvStat.rules.gas.storageClearRefund = 4800) (hA : At s.currentTarget K σ a) (hc : Clean a)
    (hor : (getOrigAcct s s.currentTarget).stor.get kr = σ.get kr)
    (hot : (getOrigAcct s s.currentTarget).stor.get kt = σ.get kt) (hne : kr ≠ kt)
    (hle : v.toNat ≤ (σ.get kr).toNat) (hnof : u.toNat + (σ.get kt).toNat < 2 ^ 256) :
    At s.currentTarget (kt :: kt :: kr :: kr :: K) ((σ.set kr (σ.get kr - v)).set kt (σ.get kt + u)) (moved s a kr kt v u) ∧
      Mv [s.currentTarget] ((4800 * empties (σ.get kr).toNat v.toNat : Nat) : Int) a (moved s a kr kt v u) := by
  have hg1 := hA.sload kr
  have hm1 := mv_afterSload s a kr
  have hc1 := hm1.clean hc
  have hf1 : Fresh s (afterSload s a kr) kr (σ.get kr) := ⟨hc1, hor, hg1.val kr⟩
  have hm2 := mv_debit (v := v) hf1 hle hg
  have hA2 := hg1.sstore kr (σ.get kr - v)
  have hc2 := hm2.clean hc1
  have hm3 := mv_afterSload s (afterSstore s (afterSload s a kr) kr (σ.get kr - v)) kt
  have hA3 := hA2.sload kt
  have hc3 := hm3.clean hc2
  have hyt : (σ.set kr (σ.get kr - v)).get kt = σ.get kt := Stor.get_set_ne _ hne _
  have hf3 : Fresh s (afterSload s (afterSstore s (afterSload s a kr) kr (σ.get kr - v)) kt) kt (σ.get kt) :=
    ⟨hc3, hot, by rw [hA3.val, hyt]⟩
  have hm4 := mv_credit (v := u) hf3 hnof
  have hA4 := hA3.sstore kt (σ.get kt + u)
  have e : moved s a kr kt v u = afterSstore s (afterSload s (afterSstore s (afterSload s a kr) kr (σ.get kr - v)) kt) kt
      (σ.get kt + u) := by
    unfold moved
    have hv : (afterSstore s (afterSload s a kr) kr (σ.get kr - v)).getStorVal s.currentTarget kt = σ.get kt := by
      rw [hA2.val, hyt]
    rw [hA.val, hv]
  rw [e, hyt] at *
  refine ⟨hA4, ?_⟩
  have := ((hm1.trans hm2).trans hm3).trans hm4
  simpa only [Int.zero_add, Int.add_zero] using this.mono (fun x hx => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
    exact List.mem_singleton.2 hx)

end Move

/-! ## DAI -/

section Dai

open Blanc.Lift.Dai

variable {s : Sevm} {b : Devm}

/-- `m20`. -/
local notation "m20" => Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

theorem retAt_mv {T : List Adr} {r : Int} {b B : Devm} {S : List B256} {M : Mem} {w : B256} {G : Nat} (h : Mv T r b B) :
    Mv T r b (retAt B S M w G) := h.halted ..

theorem retAt_at {x : Adr} {K : List B256} {σ : Stor} {B : Devm} {l : Log} {S : List B256} {M : Mem} {w : B256} {G : Nat}
    (h : At x K σ B) : At x K σ (retAt (B.addLog l) S M w G) := ⟨h.keys, h.stor⟩

theorem xferPost_moved (s : Sevm) (b : Devm) (R : Nat) : xferPost s b R =
    retAt ((moved s (afterSload s b (ky s.caller.toB256)) (ky s.caller.toB256) (ky (xTo s)) (xVal s) (xVal s)).addLog
      ⟨s.currentTarget, [Dai.transferTopic, m20 &&& s.caller.toB256, m20 &&& xTo s], (xVal s).toBytes⟩) [selW s] (xferMem s)
      okWord R := by
  unfold xferPost xferBase mvBase mvDebited moved
  rfl

/-- **DAI's `transfer` from a cold start.** -/
theorem dai_child (hg : s.benvStat.rules.gas.storageClearRefund = 4800) (hc : Clean b)
    (hk : ∀ k, (⟨s.currentTarget, k⟩ : Adr × B256) ∉ b.accessedStorageKeys)
    (ho : (getOrigAcct s s.currentTarget).stor = b.getStor s.currentTarget)
    (hne : ky s.caller.toB256 ≠ ky (xTo s))
    (hle : (xVal s).toNat ≤ ((b.getStor s.currentTarget).get (ky s.caller.toB256)).toNat)
    (hnof : (xVal s).toNat + ((b.getStor s.currentTarget).get (ky (xTo s))).toNat < 2 ^ 256) :
    xferG s b = 7274 + debitG (xVal s).toNat +
        creditG ((b.getStor s.currentTarget).get (ky (xTo s))).toNat (xVal s).toNat ∧
      Mv [s.currentTarget] ((4800 * empties ((b.getStor s.currentTarget).get (ky s.caller.toB256)).toNat (xVal s).toNat : Nat) : Int)
        b (xferPost s b 0) ∧
      (xferPost s b 0).getStor s.currentTarget =
        ((b.getStor s.currentTarget).set (ky s.caller.toB256)
          ((b.getStor s.currentTarget).get (ky s.caller.toB256) - xVal s)).set (ky (xTo s))
          ((b.getStor s.currentTarget).get (ky (xTo s)) + xVal s) := by
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = b.getStor s.currentTarget := ⟨_, rfl⟩
  rw [← hσ] at ho hle hnof ⊢
  have hA0 : At s.currentTarget [] σ b :=
    ⟨fun k => ⟨fun h => absurd h (hk k), fun h => absurd h List.not_mem_nil⟩, hσ.symm⟩
  have hor : ∀ k, (getOrigAcct s s.currentTarget).stor.get k = σ.get k := fun k => by rw [ho]
  refine ⟨?_, ?_, ?_⟩
  · rw [xferG_cold (hk _) (hk _) hne, hc.orig, hc.orig, ho, hA0.val, hA0.val, debit_class hle, credit_class hnof]
  all_goals
    have h1 := mv_afterSload s b (ky s.caller.toB256)
    have hA1 := hA0.sload (ky s.caller.toB256)
    obtain ⟨hm, h2⟩ := move_view (kr := ky s.caller.toB256) (kt := ky (xTo s)) (v := xVal s) (u := xVal s) hg hA1 (h1.clean hc)
      (hor _) (hor _) hne hle hnof
    rw [xferPost_moved]
  · have h3 := (h1.trans h2).trans (mv_addLog _ ⟨s.currentTarget, [Dai.transferTopic, m20 &&& s.caller.toB256, m20 &&& xTo s], (xVal s).toBytes⟩)
    exact (retAt_mv h3).one (fun x hx => by
      simp only [List.append_nil, List.mem_append, List.mem_singleton, or_self] at hx
      exact hx) (by rw [Int.add_zero, Int.zero_add])
  · exact (retAt_at (h := hm)).stor

end Dai

/-! ## USDT -/

section Usdt

open Blanc.Lift.Usdt

variable {s : Sevm} {b : Devm}

/-- `m20`. -/
local notation "m20" => Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-- USDT's owner's entry, as the walk computes it. -/
abbrev ownerKey (σ : Stor) : B256 := mapSlot (ownW (σ.get (Bytes.toB256 [0]))) (Bytes.toB256 [2])

/-- The slots USDT's gate and fee rule read, for a source word `r`. -/
abbrev usdtRead (r : B256) : List B256 :=
  [Bytes.toB256 [4], Bytes.toB256 [3], Bytes.toB256 [10], mapSlot (m20 &&& (m20 &&& r)) (Bytes.toB256 [6]), Bytes.toB256 [0]]

/-- The storage after USDT's move, and the owner's credit if a fee is due. -/
def usdtAfter (σ : Stor) (kr kt : B256) (v f : B256) : Stor :=
  if f = 0 then (σ.set kr (σ.get kr - v)).set kt (σ.get kt + (v - f))
  else ((σ.set kr (σ.get kr - v)).set kt (σ.get kt + (v - f))).set (ownerKey σ) (σ.get (ownerKey σ) + f)

theorem feeBase_view {K : List B256} {σ : Stor} {G : Devm} (v : B256) (hA : At s.currentTarget K σ G) :
    At s.currentTarget (Bytes.toB256 [4] :: Bytes.toB256 [3] :: K) σ (feeBase s G v) ∧ Mv [s.currentTarget] 0 G (feeBase s G v) := by
  unfold feeBase
  split
  · refine ⟨((hA.sload _).sload _ |>.sload _).congr ?_, (((mv_afterSload ..).trans (mv_afterSload ..)).trans (mv_afterSload ..)).one ?_ rfl⟩
    · intro k; simp only [List.mem_cons]; tauto
    · intro a ha; simpa only [List.mem_append, List.mem_singleton, or_self] using ha
  · exact ⟨(hA.sload _).sload _, ((mv_afterSload ..).trans (mv_afterSload ..)).one
      (fun a ha => by simpa only [List.mem_append, List.mem_singleton, or_self] using ha) rfl⟩

/-- The owner's cut, from a state at `C`. -/
theorem own_view {K : List B256} {σ : Stor} {C : Devm} {f : B256} (hg : s.benvStat.rules.gas.storageClearRefund = 4800)
    (hA : At s.currentTarget K σ C) (hc : Clean C) (h0 : Bytes.toB256 [0] ∈ K) (hk : ownerKey σ ∉ K)
    (ho : (getOrigAcct s s.currentTarget).stor.get (ownerKey σ) = σ.get (ownerKey σ))
    (hnof : f.toNat + (σ.get (ownerKey σ)).toNat < 2 ^ 256) (hne0 : ownerKey σ ≠ Bytes.toB256 [0]) :
    ownG s C f = 2400 + creditG (σ.get (ownerKey σ)).toNat f.toNat ∧
      Mv [s.currentTarget] 0 C (ownCredited s C f) ∧
      At s.currentTarget (ownerKey σ :: Bytes.toB256 [0] :: ownerKey σ :: Bytes.toB256 [0] :: K)
        (σ.set (ownerKey σ) (σ.get (ownerKey σ) + f)) (ownCredited s C f) := by
  have hky : oky s C = ownerKey σ := by rw [oky, hA.val]
  have e : ownCredited s C f = afterSstore s (afterSload s (afterSload s (afterSload s C (Bytes.toB256 [0])) (ownerKey σ)) (Bytes.toB256 [0]))
      (ownerKey σ) (σ.get (ownerKey σ) + f) := by
    simp only [ownCredited, ownRead, oky, curVal_afterSload, hA.val]
  have h1 := hA.sload (Bytes.toB256 [0])
  have h2 := h1.sload (ownerKey σ)
  have h3 := h2.sload (Bytes.toB256 [0])
  have hm3 := ((mv_afterSload s C (Bytes.toB256 [0])).trans (mv_afterSload s _ (ownerKey σ))).trans (mv_afterSload s _ (Bytes.toB256 [0]))
  have hc3 := hm3.clean hc
  have hf : Fresh s (afterSload s (afterSload s (afterSload s C (Bytes.toB256 [0])) (ownerKey σ)) (Bytes.toB256 [0])) (ownerKey σ) (σ.get (ownerKey σ)) :=
    ⟨hc3, ho, h3.val _⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [ownG_cold ((hA.keys _).2 h0) (by rw [hky]; exact fun hm => hk ((hA.keys _).1 hm)), hky, hc.orig, ho, hA.val, credit_class hnof]
  · rw [e]
    exact (hm3.trans (mv_credit hf hnof)).one (fun a ha => by
      simpa only [List.mem_append, List.mem_singleton, or_self] using ha) (by rw [Int.zero_add, Int.zero_add, Int.add_zero])
  · rw [e]
    exact h3.sstore _ _

/-- **USDT's `transfer` from a cold start.** -/
theorem usdt_child (hg : s.benvStat.rules.gas.storageClearRefund = 4800) (hc : Clean b)
    (hk : ∀ k, (⟨s.currentTarget, k⟩ : Adr × B256) ∉ b.accessedStorageKeys)
    (ho : (getOrigAcct s s.currentTarget).stor = b.getStor s.currentTarget)
    (hL : Bytes.toB256 [0] ≠ mapSlot (m20 &&& (m20 &&& s.caller.toB256)) (Bytes.toB256 [6]) ∧
      mapSlot (m20 &&& (m20 &&& s.caller.toB256)) (Bytes.toB256 [6]) ≠ Bytes.toB256 [10] ∧
      mapSlot (m20 &&& (m20 &&& s.caller.toB256)) (Bytes.toB256 [6]) ≠ Bytes.toB256 [3] ∧
      mapSlot (m20 &&& (m20 &&& s.caller.toB256)) (Bytes.toB256 [6]) ≠ Bytes.toB256 [4])
    (hr : ky s.caller.toB256 ∉ usdtRead s.caller.toB256) (ht : ky (xTo s) ∉ usdtRead s.caller.toB256)
    (hne : ky s.caller.toB256 ≠ ky (xTo s))
    (hle : (xVal s).toNat ≤ ((b.getStor s.currentTarget).get (ky s.caller.toB256)).toNat)
    (hnof : (xVal s - feeOf (b.getStor s.currentTarget) (xVal s)).toNat + ((b.getStor s.currentTarget).get (ky (xTo s))).toNat < 2 ^ 256)
    (hown : feeOf (b.getStor s.currentTarget) (xVal s) ≠ 0 →
      ownerKey (b.getStor s.currentTarget) ∉ usdtRead s.caller.toB256 ∧
      ownerKey (b.getStor s.currentTarget) ≠ ky s.caller.toB256 ∧ ownerKey (b.getStor s.currentTarget) ≠ ky (xTo s) ∧
      (feeOf (b.getStor s.currentTarget) (xVal s)).toNat + ((b.getStor s.currentTarget).get (ownerKey (b.getStor s.currentTarget))).toNat < 2 ^ 256) :
    xferG s b = 15749 + e61G (xVal s) + (if Capped (b.getStor s.currentTarget) (xVal s) then 336 else 228) +
        (if feeOf (b.getStor s.currentTarget) (xVal s) = 0 then 2586
          else 7230 + creditG ((b.getStor s.currentTarget).get (ownerKey (b.getStor s.currentTarget))).toNat
            (feeOf (b.getStor s.currentTarget) (xVal s)).toNat) +
        debitG (xVal s).toNat +
        creditG ((b.getStor s.currentTarget).get (ky (xTo s))).toNat (xVal s - feeOf (b.getStor s.currentTarget) (xVal s)).toNat ∧
      Mv [s.currentTarget] ((4800 * empties ((b.getStor s.currentTarget).get (ky s.caller.toB256)).toNat (xVal s).toNat : Nat) : Int)
        b (xferPost s b 0) ∧
      (xferPost s b 0).getStor s.currentTarget = usdtAfter (b.getStor s.currentTarget) (ky s.caller.toB256) (ky (xTo s)) (xVal s)
        (feeOf (b.getStor s.currentTarget) (xVal s)) := by
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = b.getStor s.currentTarget := ⟨_, rfl⟩
  rw [← hσ] at ho hle hnof hown ⊢
  have hA0 : At s.currentTarget [] σ b :=
    ⟨fun k => ⟨fun h => absurd h (hk k), fun h => absurd h List.not_mem_nil⟩, hσ.symm⟩
  have hor : ∀ k, (getOrigAcct s s.currentTarget).stor.get k = σ.get k := fun k => by rw [ho]
  obtain ⟨L0, L10, L3, L4⟩ := hL
  obtain ⟨Ls, hLs⟩ : ∃ L, L = mapSlot (m20 &&& (m20 &&& s.caller.toB256)) (Bytes.toB256 [6]) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = xVal s := ⟨_, rfl⟩
  obtain ⟨kr, hkr⟩ : ∃ k, k = ky s.caller.toB256 := ⟨_, rfl⟩
  obtain ⟨kt, hkt⟩ : ∃ k, k = ky (xTo s) := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, f = feeOf σ v := ⟨_, rfl⟩
  have hgA : At s.currentTarget [Bytes.toB256 [10], Ls, Bytes.toB256 [0]] σ (gateBase s b s.caller.toB256) := by
    rw [hLs]
    exact ((hA0.sload _).sload _).sload _
  have hgM : Mv [s.currentTarget] 0 b (gateBase s b s.caller.toB256) :=
    (((mv_afterSload ..).trans (mv_afterSload ..)).trans (mv_afterSload ..)).one
      (fun a ha => by simpa only [List.mem_append, List.mem_singleton, or_self] using ha) rfl
  obtain ⟨hfA, hfM⟩ := feeBase_view (s := s) v hgA
  have hcF := hfM.clean (hgM.clean hc)
  obtain ⟨hmA, hmM⟩ := move_view (kr := kr) (kt := kt) (v := v) (u := v - f) hg hfA hcF (hor _) (hor _)
    (by rw [hkr, hkt]; exact hne) (by rw [hv, hkr]; exact hle) (by rw [hf, hkt, hv]; exact hnof)
  have hK5 : ∀ k, k ∈ [Bytes.toB256 [4], Bytes.toB256 [3], Bytes.toB256 [10], Ls, Bytes.toB256 [0]] →
      k ∈ usdtRead s.caller.toB256 := fun k hk' => by rw [hLs] at hk'; exact hk'
  have hcC := hmM.clean hcF
  have hmc : mvCredited s (feeBase s (gateBase s b s.caller.toB256) v) v (v - f) (xTo s) s.caller.toB256 =
      moved s (feeBase s (gateBase s b s.caller.toB256) v) kr kt v (v - f) := by
    rw [hkr, hkt]; rfl
  have hown' : f ≠ 0 → ownerKey σ ∉ usdtRead s.caller.toB256 ∧ ownerKey σ ≠ kr ∧ ownerKey σ ≠ kt ∧ f.toNat + (σ.get (ownerKey σ)).toNat < 2 ^ 256 := by
    rw [hf, hv, hkr, hkt]; exact hown
  have hK1 : ∀ k, k ≠ kr → k ≠ kt → k ∉ usdtRead s.caller.toB256 → k ∉ kt :: kt :: kr :: kr :: [Bytes.toB256 [4], Bytes.toB256 [3], Bytes.toB256 [10], Ls, Bytes.toB256 [0]] :=
    fun k h1 h2 h3 hm => by
      rcases List.mem_cons.1 hm with e | hm
      · exact h2 e
      rcases List.mem_cons.1 hm with e | hm
      · exact h2 e
      rcases List.mem_cons.1 hm with e | hm
      · exact h1 e
      rcases List.mem_cons.1 hm with e | hm
      · exact h1 e
      · exact h3 (hK5 _ hm)
  have h0m : Bytes.toB256 [0] ∈ kt :: kt :: kr :: kr :: [Bytes.toB256 [4], Bytes.toB256 [3], Bytes.toB256 [10], Ls, Bytes.toB256 [0]] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
  have h0ne : kr ≠ Bytes.toB256 [0] ∧ kt ≠ Bytes.toB256 [0] := by
    refine ⟨fun e => hr (by rw [← hkr, e]; simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]),
      fun e => ht (by rw [← hkt, e]; simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true])⟩
  obtain ⟨σ1, hσ1⟩ : ∃ σ1, σ1 = (σ.set kr (σ.get kr - v)).set kt (σ.get kt + (v - f)) := ⟨_, rfl⟩
  rw [← hσ1] at hmA
  have h10 : σ1.get (Bytes.toB256 [0]) = σ.get (Bytes.toB256 [0]) := by
    rw [hσ1, Stor.get_set_ne _ h0ne.2, Stor.get_set_ne _ h0ne.1]
  have hkey : ownerKey σ1 = ownerKey σ := by rw [ownerKey, ownerKey, h10]
  have hoV : f ≠ 0 → ownG s (moved s (feeBase s (gateBase s b s.caller.toB256) v) kr kt v (v - f)) f =
        2400 + creditG (σ.get (ownerKey σ)).toNat f.toNat ∧
      Mv [s.currentTarget] 0 (moved s (feeBase s (gateBase s b s.caller.toB256) v) kr kt v (v - f))
        (ownCredited s (moved s (feeBase s (gateBase s b s.caller.toB256) v) kr kt v (v - f)) f) ∧
      At s.currentTarget (ownerKey σ :: Bytes.toB256 [0] :: ownerKey σ :: Bytes.toB256 [0] :: kt :: kt :: kr :: kr :: [Bytes.toB256 [4], Bytes.toB256 [3], Bytes.toB256 [10], Ls, Bytes.toB256 [0]])
        (σ1.set (ownerKey σ) (σ.get (ownerKey σ) + f))
        (ownCredited s (moved s (feeBase s (gateBase s b s.caller.toB256) v) kr kt v (v - f)) f) := by
    intro hf0
    obtain ⟨o1, o2, o3, o4⟩ := hown' hf0
    have hv1 : σ1.get (ownerKey σ) = σ.get (ownerKey σ) := by
      rw [hσ1, Stor.get_set_ne _ o3.symm, Stor.get_set_ne _ o2.symm]
    have := own_view (s := s) (f := f) hg hmA hcC h0m (by rw [hkey]; exact hK1 _ o2 o3 o1)
      (by rw [hkey, hv1]; exact hor _) (by rw [hkey, hv1]; exact o4)
      (by rw [hkey]; exact fun e => o1 (by rw [e]; simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]))
    rw [hkey, hv1] at this
    exact this
  have hT1 : ∀ a ∈ [s.currentTarget] ++ [s.currentTarget] ++ [s.currentTarget], a = s.currentTarget := fun a ha => by
    simp only [List.mem_append, List.mem_singleton, or_self] at ha
    exact ha
  have hrr : (0 : Int) + 0 + ((4800 * empties (σ.get kr).toNat v.toNat : Nat) : Int) =
      ((4800 * empties (σ.get (ky s.caller.toB256)).toNat (xVal s).toNat : Nat) : Int) := by
    rw [Int.zero_add, Int.zero_add, hkr, hv]
  have hne' : kr ≠ kt := by rw [hkr, hkt]; exact hne
  have hxp : xferPost s b 0 = St (mvPost s (feeBase s (gateBase s b s.caller.toB256) v) v f (xTo s) s.caller.toB256)
      [selL s] (xferMem s b) 0 := by
    rw [hf, hv, hσ]; rfl
  have hstM : ∀ {T : List Adr} {r : Int} {B : Devm} {S : List B256} {M : Mem}, Mv T r b B → Mv T r b (St B S M 0) :=
    fun h => ⟨fun x hx => ⟨(h.same x hx).keys, (h.same x hx).stor, (h.same x hx).warm⟩, h.refund,
      fun hc' => ⟨(h.clean hc').created, (h.clean hc').del, (h.clean hc').error⟩⟩
  have hlog : ∀ {T : List Adr} {r : Int} {B : Devm} {l : Log}, Mv T r b B → Mv T r b (B.addLog l) :=
    fun h => ⟨fun x hx => ⟨(h.same x hx).keys, (h.same x hx).stor, (h.same x hx).warm⟩, h.refund,
      fun hc' => ⟨(h.clean hc').created, (h.clean hc').del, (h.clean hc').error⟩⟩
  have hbase := (hgM.trans hfM).trans hmM
  refine ⟨?_, ?_, ?_⟩
  · have e : xferG s b = 1049 + gateG s b s.caller.toB256 + (feeG s (gateBase s b s.caller.toB256) v +
        mvG 2586 4830 s (feeBase s (gateBase s b s.caller.toB256) v) v f (xTo s) s.caller.toB256) := by
      rw [hf, hv, ← hgA.stor]; rfl
    have h3 : (⟨s.currentTarget, Bytes.toB256 [3]⟩ : Adr × B256) ∉ (gateBase s b s.caller.toB256).accessedStorageKeys := fun hm => by
      have := (hgA.keys _).1 hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with e | e | e
      · exact absurd e (by decide)
      · rw [hLs] at e; exact L3 e.symm
      · exact absurd e (by decide)
    have h4 : (⟨s.currentTarget, Bytes.toB256 [4]⟩ : Adr × B256) ∉ (gateBase s b s.caller.toB256).accessedStorageKeys := fun hm => by
      have := (hgA.keys _).1 hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with e | e | e
      · exact absurd e (by decide)
      · rw [hLs] at e; exact L4 e.symm
      · exact absurd e (by decide)
    have hcr : (⟨s.currentTarget, ky s.caller.toB256⟩ : Adr × B256) ∉ (feeBase s (gateBase s b s.caller.toB256) v).accessedStorageKeys :=
      fun hm => hr (hK5 _ ((hfA.keys _).1 hm))
    have hct : (⟨s.currentTarget, ky (xTo s)⟩ : Adr × B256) ∉ (feeBase s (gateBase s b s.caller.toB256) v).accessedStorageKeys :=
      fun hm => ht (hK5 _ ((hfA.keys _).1 hm))
    rw [e, gateG_cold (hk _) (hk _) (hk _) L0 L10, feeG_cold h3 h4, mvG_cold 2586 4830 hcr hct hne, hgA.stor, hcF.orig, hcF.orig,
      ho, hfA.val, hfA.val, ← hkr, ← hkt, debit_class (by rw [hv, hkr]; exact hle), credit_class (by rw [hf, hkt, hv]; exact hnof), ← hv, ← hf]
    by_cases hf0 : f = 0
    · simp only [hf0, ↓reduceIte]
      omega
    · have hO := hoV hf0
      rw [hmc]
      simp only [hf0, ↓reduceIte, hO.1]
      omega
  · rw [hxp]
    refine hstM ?_
    unfold mvPost
    split
    · refine hlog ?_
      rw [hmc]
      exact hbase.one hT1 hrr
    · rename_i hf0
      refine hlog ?_
      unfold ownLogged
      refine hlog ?_
      rw [hmc]
      refine ((hbase.trans (hoV hf0).2.1).trans (mv_afterSload ..)).one ?_ ?_
      · intro a ha
        simp only [List.mem_append, List.mem_singleton, or_self] at ha
        exact ha
      · rw [Int.add_zero, Int.add_zero]; exact hrr
  · have hSt : ∀ (B : Devm) (S : List B256) (M : Mem), (St B S M 0).getStor s.currentTarget = B.getStor s.currentTarget :=
      fun _ _ _ => rfl
    rw [hxp, hSt]
    unfold mvPost usdtAfter
    rw [← hv, ← hf, ← hkr, ← hkt]
    split
    · rw [Devm.addLog_getStor, hmc, ← hσ1]
      exact hmA.stor
    · rename_i hf0
      unfold ownLogged
      rw [Devm.addLog_getStor, Devm.addLog_getStor, afterSload_getStor, hmc, ← hσ1]
      exact (hoV hf0).2.2.stor

end Usdt

/-! ## USDC -/

section Usdc

open Blanc.Lift.Usdc Blanc.Composition.UsdcLive

/-- `l255`. -/
local notation "l255" => Bytes.toB256 [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

theorem h_stor (B : Devm) (S : List B256) (M : Mem) (G a n : Nat) (w : Bytes) (x : Adr) :
    (((St B S M G).memRead a n).2.withOutput w).getStor x = B.getStor x := rfl

theorem l255_unfrozen {w : B256} (h : frozenBit w = false) : (l255 &&& w) = w := by
  apply B256.toNat_inj
  rw [l255_and_toNat]
  unfold balanceBits
  unfold frozenBit at h
  exact Nat.mod_eq_of_lt (by simpa only [decide_eq_false_iff_not, not_le] using h)

variable {s : Sevm} {b : Devm} {K : List B256} {σ : Stor}

/-- **V2_2's `transfer` frame**, its balance slots and the pause slot cold. -/
theorem impl_child (hg : s.benvStat.rules.gas.storageClearRefund = 4800) (hc : Clean b)
    (hA : At s.currentTarget K σ b)
    (ho : (getOrigAcct s s.currentTarget).stor = σ)
    (h1 : Bytes.toB256 [1] ∉ K) (hz : ky s.caller.toB256 ∉ K) (hy : ky (xTo s) ∉ K)
    (h1z : Bytes.toB256 [1] ≠ ky s.caller.toB256) (h1y : Bytes.toB256 [1] ≠ ky (xTo s))
    (hne : ky s.caller.toB256 ≠ ky (xTo s))
    (fz : frozenBit (σ.get (ky s.caller.toB256)) = false) (fy : frozenBit (σ.get (ky (xTo s))) = false)
    (hle : (xVal s).toNat ≤ (σ.get (ky s.caller.toB256)).toNat)
    (hnof : (xVal s).toNat + (σ.get (ky (xTo s))).toNat < 2 ^ 256) :
    implXferG s b = 10463 + debitG (xVal s).toNat + creditG (σ.get (ky (xTo s))).toNat (xVal s).toNat ∧
      Mv [s.currentTarget] ((4800 * empties (σ.get (ky s.caller.toB256)).toNat (xVal s).toNat : Nat) : Int)
        b (implXferPost s b 0) ∧
      (implXferPost s b 0).getStor s.currentTarget =
        (σ.set (ky s.caller.toB256) (σ.get (ky s.caller.toB256) - xVal s)).set (ky (xTo s))
          (σ.get (ky (xTo s)) + xVal s) := by
  obtain ⟨kz, hkz⟩ : ∃ k, k = ky s.caller.toB256 := ⟨_, rfl⟩
  obtain ⟨ky1, hky1⟩ : ∃ k, k = ky (xTo s) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = xVal s := ⟨_, rfl⟩
  have hkz' : ky' s.caller.toB256 = kz := by rw [hkz, ky'_bal, ky_bal]
  have hky' : ky' (xTo s) = ky1 := by rw [hky1, ky'_bal, ky_bal]
  simp only [← hkz, ← hky1, ← hv] at hz hy h1z h1y hne fz fy hle hnof ⊢
  have a1 := hA.sload (Bytes.toB256 [1])
  have a2 := a1.sload kz
  have a3 := a2.sload ky1
  have m3 := ((mv_afterSload s b (Bytes.toB256 [1])).trans (mv_afterSload s _ kz)).trans (mv_afterSload s _ ky1)
  have c3 := m3.clean hc
  obtain ⟨b3, hb3⟩ : ∃ b3, b3 = afterSload s (afterSload s (afterSload s b (Bytes.toB256 [1])) kz) ky1 := ⟨_, rfl⟩
  rw [← hb3] at a3 m3 c3
  have wz : (⟨s.currentTarget, kz⟩ : Adr × B256) ∈ b3.accessedStorageKeys :=
    (a3.keys _).2 (by simp only [List.mem_cons, true_or, or_true])
  have wy : (⟨s.currentTarget, ky1⟩ : Adr × B256) ∈ b3.accessedStorageKeys :=
    (a3.keys _).2 (by simp only [List.mem_cons, true_or])
  have hor : ∀ k, (getOrigAcct s s.currentTarget).stor.get k = σ.get k := fun k => by rw [ho]
  obtain ⟨X, hX⟩ : ∃ X, X = σ.get kz := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = σ.get ky1 := ⟨_, rfl⟩
  rw [← hX] at fz hle ⊢
  rw [← hY] at fy hnof ⊢
  have hXl := l255_unfrozen fz
  have hYl := l255_unfrozen fy
  obtain ⟨D, hD⟩ : ∃ D, D = afterSstore s b3 kz (X - v) := ⟨_, rfl⟩
  have a4 : At s.currentTarget (kz :: ky1 :: kz :: Bytes.toB256 [1] :: K) (σ.set kz (X - v)) D := by
    rw [hD]; exact a3.sstore _ _
  have f4 : Fresh s b3 kz X := ⟨c3, by rw [hor, hX], by rw [a3.val, hX]⟩
  have m4 : Mv [s.currentTarget] ((4800 * empties X.toNat v.toNat : Nat) : Int) b3 D := by
    rw [hD]; exact mv_debit f4 hle hg
  have c4 := m4.clean c3
  have vy : D.getStorVal s.currentTarget ky1 = Y := by
    rw [a4.val, Stor.get_set_ne _ hne, hY]
  have wy4 : (⟨s.currentTarget, ky1⟩ : Adr × B256) ∈ D.accessedStorageKeys := by
    rw [hD]; exact mem_afterSstore_of_mem wy
  have f5 : Fresh s D ky1 Y := ⟨c4, by rw [hor, hY], vy⟩
  have m5 := mv_credit (v := v) f5 hnof
  have hDeb : e93Debited s b3 v s.caller.toB256 = D := by
    unfold e93Debited
    rw [← hkz, hkz', afterSload_of_warm wz, afterSload_of_warm wz, afterSload_of_warm wz, a3.val, ← hX, hXl, hD]
  have h37 : e37Pre s b (xTo s) = b3 := by rw [hb3, hkz, hky1]
  have hPost : ∃ l, e93Post s b3 v (xTo s) s.caller.toB256 = (afterSstore s D ky1 (Y + v)).addLog l := by
    unfold e93Post
    rw [hDeb, ← hky1, hky', afterSload_of_warm wy4, afterSload_of_warm wy4, vy, hYl, (B256.add_comm : v + Y = Y + v)]
    exact ⟨_, rfl⟩
  have hAll := m3.trans (m4.trans m5)
  have hzne : kz ≠ Bytes.toB256 [1] := fun e => h1z e.symm
  have hyne : ky1 ≠ Bytes.toB256 [1] := fun e => h1y e.symm
  have hzy : ky1 ≠ kz := fun e => hne e.symm
  have hzw : ∀ T : List Adr, T = [s.currentTarget] ++ [s.currentTarget] ++ [s.currentTarget] ++ ([s.currentTarget] ++ [s.currentTarget]) → ∀ a ∈ T, a = s.currentTarget := by
    rintro T rfl a ha
    simpa only [List.mem_append, List.mem_singleton, or_self] using ha
  obtain ⟨l, hl⟩ := hPost
  refine ⟨?_, ?_, ?_⟩
  · have e : implXferG s b = 358 + (367 + sloadCost s b (Bytes.toB256 [1]) + sloadCost s (afterSload s b (Bytes.toB256 [1])) kz +
        sloadCost s (afterSload s (afterSload s b (Bytes.toB256 [1])) kz) ky1 + e93G s b3 v (xTo s) s.caller.toB256) := by
      rw [hb3, hkz, hky1, hv]; rfl
    rw [e]
    unfold e93G e99G
    rw [hDeb, ← hkz, ← hky1, hkz', hky', afterSload_of_warm wz, afterSload_of_warm wz, afterSload_of_warm wy4,
      sloadCost_of_warm wz, sloadCost_of_warm wy4, a3.val, ← hX, hXl, vy, hYl, (B256.add_comm : v + Y = Y + v),
      hA.sloadCost_cold h1, a1.sloadCost_cold (by simp only [List.mem_cons, not_or]; exact ⟨hzne, hz⟩),
      a2.sloadCost_cold (by simp only [List.mem_cons, not_or]; exact ⟨hzy, hyne, hy⟩),
      afterSload_of_warm wz, afterSload_of_warm wy4,
      cost_debit f4 a3 (by simp only [List.mem_cons, true_or, or_true]) hle,
      cost_credit f5 a4 (by simp only [List.mem_cons, true_or, or_true]) hnof]
    simp only [gasWarmAccess]
    omega
  · have hF : implXferPost s b 0 = ((St (e93Post s b3 v (xTo s) s.caller.toB256)
        [Sevm.dataWord s (Bytes.toB256 [0]) >>> (Bytes.toB256 [224]).toNat] (implXferMem s) 0).memRead
          (Bytes.toB256 [128]).toNat (Bytes.toB256 [32] + (Bytes.toB256 [128] - Bytes.toB256 [128])).toNat).2.withOutput
        (B256.eqCheck (B256.eqCheck (Bytes.toB256 [1]) 0) 0).toBytes := by
      rw [← h37, hv]; rfl
    rw [hF, hl]
    exact ((hAll.trans (mv_addLog _ l)).halted _ _ _ _ _ _).one (fun a ha => by
      simpa only [List.append_nil, List.mem_append, List.mem_singleton, or_self] using ha) (by
      simp only [Int.zero_add, Int.add_zero])
  · have hF : implXferPost s b 0 = ((St (e93Post s b3 v (xTo s) s.caller.toB256)
        [Sevm.dataWord s (Bytes.toB256 [0]) >>> (Bytes.toB256 [224]).toNat] (implXferMem s) 0).memRead
          (Bytes.toB256 [128]).toNat (Bytes.toB256 [32] + (Bytes.toB256 [128] - Bytes.toB256 [128])).toNat).2.withOutput
        (B256.eqCheck (B256.eqCheck (Bytes.toB256 [1]) 0) 0).toBytes := by
      rw [← h37, hv]; rfl
    rw [hF, hl]
    rw [h_stor, Devm.addLog_getStor]
    exact (a4.sstore ky1 (Y + v)).stor

theorem spawn_refund (d : Devm) (a : Adr) (c ii is oi os : Nat) :
    (callSpawnParent (addAccessedAddress d a) c ii is oi os).refundCounter = d.refundCounter := rfl

theorem spawn_clean {d : Devm} (h : Clean d) (a : Adr) (c ii is oi os : Nat) :
    Clean (callSpawnParent (addAccessedAddress d a) c ii is oi os) := ⟨h.created, h.del, h.error⟩

theorem St_clean {d : Devm} (h : Clean d) (S : List B256) (M : Mem) (G : Nat) : Clean (St d S M G) :=
  ⟨h.created, h.del, h.error⟩

theorem proxyPost_mv {T : List Adr} {r : Int} {b C : Devm} {s : Sevm} {p : Devm} {w : B256}
    (h : Mv T r b (callChildPost (dParent s p 0) C (Bytes.toB256 [0]).toNat (Bytes.toB256 [0]).toNat)) :
    Mv T r b (proxyPost s p 0 0 C w) := by
  unfold proxyPost
  exact h.halted _ _ _ _ _ _

theorem proxyPost_stor {s : Sevm} {p C : Devm} {w : B256} (x : Adr) :
    (proxyPost s p 0 0 C w).getStor x = C.getStor x := by
  unfold proxyPost
  exact (h_stor _ _ _ _ _ _ _ _).trans rfl

/-- The proxy's windows never grow its memory. -/
theorem dExt_zero (s : Sevm) (p : Devm) (hlen : s.data.length = 68) : dExt s p = 0 := by
  obtain ⟨h32, h96⟩ := pMem_size s
  have hl : (Nat.toB256 s.data.length).toNat = 68 := by rw [hlen]; decide
  have h0 : (Bytes.toB256 [0]).toNat = 0 := by decide
  simp only [dExt, Devm.extCost, memExtsSize, hl, h0]
  show calculateMemoryGasCost (memExtSize (memExtSize (pMem s).size 0 68) 0 0) - calculateMemoryGasCost (pMem s).size = 0
  rw [memExtSize_of_le h32 (by omega), memExtSize_of_le h32 (by omega), Nat.sub_self]

/-- The proxy's charge up to its `DELEGATECALL`, both its slots cold. -/
theorem proxyPreG_cold {s : Sevm} {p : Devm} {σ : Stor} (hA : At s.currentTarget [] σ p) (hKK : pKA ≠ pKI)
    (hlen : s.data.length = 68) : proxyPreG s p = 4645 := by
  have h96 : (Mem.empty.write 64 (Bytes.toB256 [128]).toBytes).size = 96 := by
    rw [Mem.size_write_word_at]; rfl
  have hl : (Nat.toB256 s.data.length).toNat = 68 := by rw [hlen]; decide
  have h0 : (Bytes.toB256 [0]).toNat = 0 := by decide
  have he : preExt s p = 0 := by
    unfold preExt
    rw [hl, h0, St]
    exact Devm.extCost_zero_of_le (by rw [h96]) (by rw [h96]; omega)
  unfold proxyPreG
  rw [he, hl, hA.sloadCost_cold List.not_mem_nil, (hA.sload pKA).sloadCost_cold (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact fun e => hKK e.symm)]
  rfl

/-- **USDC's `transfer` through the proxy, from a cold start.** -/
theorem usdc_child {s : Sevm} {p : Devm} (hg : s.benvStat.rules.gas.storageClearRefund = 4800) (hc : Clean p)
    (hk : ∀ k, (⟨s.currentTarget, k⟩ : Adr × B256) ∉ p.accessedStorageKeys)
    (ho : (getOrigAcct s s.currentTarget).stor = p.getStor s.currentTarget)
    (hlen : s.data.length = 68) (himpl : ((p.getStor s.currentTarget).get pKI).toAdr ∉ p.accessedAddresses)
    (hKK : pKA ≠ pKI)
    (h1 : Bytes.toB256 [1] ≠ pKA ∧ Bytes.toB256 [1] ≠ pKI)
    (hz : ky s.caller.toB256 ≠ pKA ∧ ky s.caller.toB256 ≠ pKI) (hy : ky (xTo s) ≠ pKA ∧ ky (xTo s) ≠ pKI)
    (h1z : Bytes.toB256 [1] ≠ ky s.caller.toB256) (h1y : Bytes.toB256 [1] ≠ ky (xTo s))
    (hne : ky s.caller.toB256 ≠ ky (xTo s))
    (fz : frozenBit ((p.getStor s.currentTarget).get (ky s.caller.toB256)) = false)
    (fy : frozenBit ((p.getStor s.currentTarget).get (ky (xTo s))) = false)
    (hle : (xVal s).toNat ≤ ((p.getStor s.currentTarget).get (ky s.caller.toB256)).toNat)
    (hnof : (xVal s).toNat + ((p.getStor s.currentTarget).get (ky (xTo s))).toNat < 2 ^ 256) :
    xferG s p = 17752 + debitG (xVal s).toNat + creditG ((p.getStor s.currentTarget).get (ky (xTo s))).toNat (xVal s).toNat ∧
      Mv [s.currentTarget, ((p.getStor s.currentTarget).get pKI).toAdr]
        ((4800 * empties ((p.getStor s.currentTarget).get (ky s.caller.toB256)).toNat (xVal s).toNat : Nat) : Int)
        p (proxyCanon 1 (fun s p => implXferPost s p 0) s p) ∧
      (proxyCanon 1 (fun s p => implXferPost s p 0) s p).getStor s.currentTarget =
        ((p.getStor s.currentTarget).set (ky s.caller.toB256)
          ((p.getStor s.currentTarget).get (ky s.caller.toB256) - xVal s)).set (ky (xTo s))
          ((p.getStor s.currentTarget).get (ky (xTo s)) + xVal s) := by
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = p.getStor s.currentTarget := ⟨_, rfl⟩
  simp only [← hσ] at ho himpl fz fy hle hnof ⊢
  have hA0 : At s.currentTarget [] σ p :=
    ⟨fun k => ⟨fun h => absurd h (hk k), fun h => absurd h List.not_mem_nil⟩, hσ.symm⟩
  have a1 := hA0.sload pKA
  have a2 := a1.sload pKI
  have m2 := (mv_afterSload s p pKA).trans (mv_afterSload s _ pKI)
  have c2 := m2.clean hc
  have hpI : pI s p = σ.get pKI := by
    show (afterSload s p pKA).getStorVal s.currentTarget pKI = _
    rw [a1.val]
  have hdI : dI s p = (σ.get pKI).toAdr := by rw [dI, hpI]
  have hdata := dMsg_data s p 0 (by omega)
  have hdw : Sevm.dataWord (initSevm (dMsg s p 0)) = Sevm.dataWord s := by
    funext i; unfold Sevm.dataWord; rw [hdata]
  have hxv : xVal (initSevm (dMsg s p 0)) = xVal s := by unfold xVal; rw [hdw]
  have hxt : xTo (initSevm (dMsg s p 0)) = xTo s := by unfold xTo; rw [hdw]
  have hcc : (initSevm (dMsg s p 0)).caller = s.caller := rfl
  have aC : At (initSevm (dMsg s p 0)).currentTarget [pKI, pKA] σ (initDevm (dMsg s p 0)) := ⟨a2.keys, a2.stor⟩
  have hcC : Clean (initDevm (dMsg s p 0)) := by
    refine ⟨c2.created, fun a hm => ?_, rfl⟩
    have hm' : a ∈ (if s.benvStat.rules.settle.selfdestructRefund = 0 then (.emptyWithCapacity : AdrSet)
        else (dParent s p 0).accountsToDelete) := hm
    split at hm'
    · exact Std.HashSet.not_mem_emptyWithCapacity hm'
    · exact c2.del a hm'
  have hm2 : ∀ k, k ≠ pKA → k ≠ pKI → k ∉ [pKI, pKA] := fun k h h' hm => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    exact hm.elim h' h
  obtain ⟨iC, iM, iS⟩ := impl_child (s := initSevm (dMsg s p 0)) (b := initDevm (dMsg s p 0)) (K := [pKI, pKA]) (σ := σ)
    hg hcC aC ho (hm2 _ h1.1 h1.2)
    (by rw [hcc]; exact hm2 _ hz.1 hz.2) (by rw [hxt]; exact hm2 _ hy.1 hy.2)
    (by rw [hcc]; exact h1z) (by rw [hxt]; exact h1y) (by rw [hcc, hxt]; exact hne)
    (by rw [hcc]; exact fz) (by rw [hxt]; exact fy) (by rw [hcc, hxv]; exact hle) (by rw [hxt, hxv]; exact hnof)
  simp only [hcc, hxt, hxv] at iC iM iS
  have hAd : (pBase s p).accessedAddresses = p.accessedAddresses := by
    simp only [pBase, afterSload_accessedAddresses]
  refine ⟨?_, ?_, ?_⟩
  · have hT : tailG s (dParent s p 0) (pRest s p) (dParent s p 0).memory 1 = 44 := by
      obtain ⟨h32, hge⟩ := dParent_size s p 0
      have hl32 : (Nat.toB256 (1 : B256).toBytes.length).toNat = 32 := by rw [B256.length_toBytes]; decide
      have h0 : (Bytes.toB256 [0]).toNat = 0 := by decide
      unfold tailG
      rw [hl32, h0, St, Devm.extCost_zero_of_le h32 (by omega)]
      rfl
    have hAc : dAcc s p = 2600 := by
      unfold dAcc accessCost
      rw [hAd, hdI, ite_eq_right himpl]
      rfl
    show proxyPreG s p + (tailG s (dParent s p 0) (pRest s p) (dParent s p 0).memory 1 + dAcc s p + dExt s p +
      implXferG (initSevm (dMsg s p 0)) (initDevm (dMsg s p 0))) = _
    rw [proxyPreG_cold hA0 hKK hlen, hT, hAc, dExt_zero s p hlen, iC]
    omega
  · have hS : ∀ a, a ∉ [(σ.get pKI).toAdr, s.currentTarget] → Same a (pBase s p) (dParent s p 0) := fun a ha => by
      refine ⟨fun _ => Iff.rfl, rfl, ?_⟩
      show a ∈ (pBase s p).accessedAddresses.insert (dI s p) ↔ _
      rw [Std.HashSet.mem_insert, hdI]
      refine ⟨fun h => h.elim (fun e => absurd (List.mem_cons.2 (Or.inl (by simpa only [beq_iff_eq] using e : (σ.get pKI).toAdr = a).symm)) ha) id, Or.inr⟩
    have hch : ∀ a, a ∉ [(σ.get pKI).toAdr, s.currentTarget] → Same a (dParent s p 0) (implXferPost (initSevm (dMsg s p 0)) (initDevm (dMsg s p 0)) 0) := fun a ha => by
      have e : Same a (dParent s p 0) (initDevm (dMsg s p 0)) := ⟨fun _ => Iff.rfl, rfl, Iff.rfl⟩
      exact e.trans (iM.same a (fun hm => ha (List.mem_cons_of_mem _ hm)))
    have hRf : (dParent s p 0).refundCounter = (pBase s p).refundCounter := spawn_refund _ _ _ _ _ _ _
    have hc' : Mv [(σ.get pKI).toAdr, s.currentTarget] ((4800 * empties (σ.get (ky s.caller.toB256)).toNat (xVal s).toNat : Nat) : Int) (pBase s p) _ :=
      mv_callChild (Bytes.toB256 [0]).toNat (Bytes.toB256 [0]).toNat hS hRf
        (fun h => spawn_clean (St_clean h _ _ _) _ _ _ _ _ _) hch (iM.refund.trans (Int.zero_add _)) (fun _ => iM.clean hcC)
    have h2 := (m2.trans hc').mono (T' := [s.currentTarget, (σ.get pKI).toAdr]) (fun a ha => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at ha ⊢
      exact ha.elim Or.inl (fun h => h.elim Or.inr Or.inl))
    rw [Int.zero_add, Int.zero_add] at h2
    exact proxyPost_mv h2
  · unfold proxyCanon
    rw [proxyPost_stor]
    exact iS

end Usdc

end Blanc.Composition.Curve3PoolPublic
