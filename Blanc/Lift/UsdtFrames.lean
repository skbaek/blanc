import Blanc.Lift.Usdt.Check
import Blanc.Lift.InvWalkLegacy

/-!
# USDT: the frames of `transfer`, `transferFrom` and `balanceOf`, inverted
-/

namespace Blanc.Lift.Usdt

open Jaune Blanc Blanc.Lift

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- The internal callees of `transfer`, `transferFrom` and `balanceOf`: none halts the frame. -/
def familyCallees : List Nat := [5, 10, 11, 12, 13, 14, 15, 23, 33, 39, 50, 51, 55, 56, 57, 59, 60,
  61, 63]

theorem familyCallees_noHalt : NoHaltSet cert.prog familyCallees = true := by decide +kernel

/-- Enter callee entry `k` (tree `T`) of `familyCallees` from a cut run `h`; the callee run is
`hc`, the continuation `h`. -/
macro "ucall " h:ident hc:ident k:num T:term : tactic => `(tactic|
  (have h' := ric_callR (k := $k) (g := $T) rfl
    (fun hh => SFunc.RunP.not_halted_entry familyCallees_noHalt
      (by decide : $k ∈ familyCallees) rfl hh rfl) $h
   clear $h
   obtain ⟨_, _, $hc:ident, $h:ident⟩ := h'))

/-- **Entry 50, SafeMath `sub(y, x)`**. -/
theorem e50_inv {x y ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: ret :: S) M G) t_2ae0_c50 o) :
    x.toNat ≤ y.toNat ∧ ∃ G', o = .returned (St b ((y - x) :: S) M G') := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  cases e
  exact ⟨toNat_le_of_gtCheck_eq_zero (zero_of_iszero3 c), _, rfl⟩

/-- **Entry 51, SafeMath `add(y, x)`**. -/
theorem e51_inv {x y ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: ret :: S) M G) t_2af9_c51 o) :
    x.toNat + y.toNat < 2 ^ 256 ∧ ∃ G', o = .returned (St b ((y + x) :: S) M G') := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  cases e
  rw [B256.add_comm] at c
  exact ⟨(add_nof_of_ltCheck (zero_of_iszero3 c)).1, _, by rw [B256.add_comm]⟩

/-- **Entry 61, SafeMath `mul(y, x)`**: `y = 0` returns `0`, otherwise the product, its division
checked. -/
theorem e61_inv {x y ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: ret :: S) M G) t_2a03_c61 o) :
    ∃ G', o = .returned (St b ((y * x) :: S) M G') := by
  have h := run.cut
  clear run
  repeat ustep h
  have h' := ric_branch h
  clear h
  rcases h' with ⟨c, _, h⟩ | ⟨c, _, h⟩
  · repeat ustep h
    obtain ⟨_, e⟩ := ric_ret h
    cases e
    have hy : y = 0 := eq_zero_of_iszero_lit c
    subst hy
    rw [show (0 : B256) * x = 0 by
      show Nat.toB256 ((0 : B256).toNat * x.toNat) = 0
      rw [B256.toNat_zero, Nat.zero_mul]
      rfl]
    exact ⟨_, rfl⟩
  · repeat ustep h
    ibranch h c1
    repeat ustep h
    ibranch h c2
    repeat ustep h
    obtain ⟨_, e⟩ := ric_ret h
    cases e
    exact ⟨_, rfl⟩

/-- **Entry 63, SafeMath `div(y, x)`**. -/
theorem e63_inv {x y ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: ret :: S) M G) t_2ac5_c63 o) :
    ∃ G', o = .returned (St b ((y / x) :: S) M G') := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  cases e
  exact ⟨_, rfl⟩

/-! ## The ledger -/

/-- A balance entry (`mapping(address => uint256)` at slot 2). -/
def balSlot (a : Adr) : B256 := mapSlot a.toB256 2

/-- The owner: the low twenty bytes of slot 0, shared with `paused`. -/
def ownerOf (σ : Stor) : Adr := (σ.get 0).toAdr

/-- `balances[a] -= v`. -/
def debit (σ : Stor) (a : Adr) (v : B256) : Stor := σ.set (balSlot a) (σ.get (balSlot a) - v)

/-- `balances[a] += v`. -/
def credit (σ : Stor) (a : Adr) (v : B256) : Stor := σ.set (balSlot a) (σ.get (balSlot a) + v)

/-- The move of `v` from `src` to `dst` with fee `f`: `src` debited `v`, `dst` credited `v - f`, and a
nonzero fee credited to the owner the contract reads after those two writes. -/
def moveStor (σ : Stor) (src dst : Adr) (v f : B256) : Stor :=
  if f = 0 then credit (debit σ src v) dst (v - f)
  else credit (credit (debit σ src v) dst (v - f)) (ownerOf (credit (debit σ src v) dst (v - f))) f

/-- The conditions of a successful move. -/
structure MoveOk (σ : Stor) (src dst : Adr) (v f : B256) : Prop where
  fee_le : f.toNat ≤ v.toNat
  debit_le : v.toNat ≤ (σ.get (balSlot src)).toNat
  credit_lt : (v - f).toNat + ((debit σ src v).get (balSlot dst)).toNat < 2 ^ 256
  owner_lt : f ≠ 0 → f.toNat + ((credit (debit σ src v) dst (v - f)).get
    (balSlot (ownerOf (credit (debit σ src v) dst (v - f))))).toNat < 2 ^ 256

theorem lit2 : Bytes.toB256 [2] = 2 := by decide

theorem lit5 : Bytes.toB256 [5] = 5 := by decide

/-- The word normal form of a USDT walk's stack and facts. -/
macro "unorm " h:ident : tactic => `(tactic|
  (simp (config := { failIfUnchanged := false }) only [keccak_u, ff20_and_word, word_ff20,
     toAdr_toB256, getStorVal_afterSload, div_bexp_zero, lit2, lit5, afterSstore_getStor_self,
     AccumulatedWalk.getStorVal_afterSstore_self, afterSload_getStor, gsv] at $h:ident
   simp (config := { failIfUnchanged := false }) only [lit0] at $h:ident))

/-- `unorm` and `umem`, across a segment. -/
macro "useg " h:ident : tactic => `(tactic|
  (repeat ustep $h
   unorm $h
   umem $h))

/-- **Tree `0x26f1` of entry 13, the moves of `BasicToken.transfer`**. -/
theorem e13_inv {p q f v t ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (h : SFunc.RunCut cert.prog sevm [] (St b (p :: q :: f :: v :: t :: ret :: S) M G) t_26f1_c13 (Seg.done o)) :
    MoveOk (Devm.getStor b sevm.currentTarget) sevm.caller t.toAdr v f ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧
        Devm.getStor b' sevm.currentTarget =
          moveStor (Devm.getStor b sevm.currentTarget) sevm.caller t.toAdr v f := by
  repeat ustep h
  ucall h hc 50 t_2ae0_c50
  obtain ⟨c1, G1, e⟩ := e50_inv fork hc
  cases e
  clear hc
  useg h
  ucall h hc 50 t_2ae0_c50
  obtain ⟨c2, G2, e⟩ := e50_inv fork hc
  cases e
  clear hc
  useg h
  ucall h hc 51 t_2af9_c51
  obtain ⟨c3, G3, e⟩ := e51_inv fork hc
  cases e
  clear hc
  useg h
  ubranchTo h c4
  · have hf : f ≠ 0 := by
      rintro rfl
      exact absurd c4 (by decide)
    useg h
    ucall h hc 51 t_2af9_c51
    obtain ⟨c5, G5, e⟩ := e51_inv fork hc
    cases e
    clear hc
    repeat ustep h
    obtain ⟨_, e⟩ := ric_ret h
    clear h
    obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
    clear e
    unorm c5
    refine ⟨⟨c1, c2, c3, fun _ => c5⟩, B, MB, GB, eo, ?_⟩
    rw [sB]
    simp only [Devm.addLog_getStor, afterSstore_getStor_self, afterSload_getStor, keccak_u,
      ff20_and_word, toAdr_toB256, getStorVal_afterSload, div_bexp_zero, lit2, gsv,
      AccumulatedWalk.getStorVal_afterSstore_self]
    unfold moveStor
    rw [if_neg hf]
    rfl
  · have hf : f = 0 := by
      have := toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero c4)
      apply B256.toNat_inj
      rw [B256.toNat_zero]
      exact Nat.le_zero.mp this
    subst hf
    repeat ustep h
    obtain ⟨_, e⟩ := ric_ret h
    clear h
    obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
    clear e
    refine ⟨⟨c1, c2, c3, fun h => absurd rfl h⟩, B, MB, GB, eo, ?_⟩
    rw [sB]
    simp only [Devm.addLog_getStor, afterSstore_getStor_self, afterSload_getStor]
    unfold moveStor
    rw [if_pos rfl]
    rfl

/-- The fee of a move of `v`: `v * basisPointsRate / 10000`, capped at `maximumFee` (slots 3, 4). -/
def feeOf (σ : Stor) (v : B256) : B256 :=
  if (σ.get 4).toNat < ((v * σ.get 3) / Bytes.toB256 [39, 16]).toNat then σ.get 4
  else (v * σ.get 3) / Bytes.toB256 [39, 16]

theorem lit3 : Bytes.toB256 [3] = 3 := by decide
theorem lit4 : Bytes.toB256 [4] = 4 := by decide

theorem feeOf_cap {σ : Stor} {v : B256}
    (c : B256.eqCheck (B256.gtCheck ((v * σ.get (Bytes.toB256 [3])) / Bytes.toB256 [39, 16])
      (σ.get (Bytes.toB256 [4]))) 0 = 0) : feeOf σ v = σ.get (Bytes.toB256 [4]) := by
  rw [lit3, lit4] at *
  unfold feeOf
  rw [if_pos]
  by_contra hlt
  have hg := B256.gtCheck_eq_zero_of_toNat_le (Nat.le_of_not_lt hlt)
  rw [hg] at c
  exact absurd c (by decide)

theorem feeOf_keep {σ : Stor} {v : B256}
    (c : B256.eqCheck (B256.gtCheck ((v * σ.get (Bytes.toB256 [3])) / Bytes.toB256 [39, 16])
      (σ.get (Bytes.toB256 [4]))) 0 ≠ 0) :
    feeOf σ v = (v * σ.get (Bytes.toB256 [3])) / Bytes.toB256 [39, 16] := by
  rw [lit3, lit4] at *
  unfold feeOf
  rw [if_neg]
  exact Nat.not_lt.mpr (toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero c))

/-- **Entry 60, `BasicToken.transfer(t, v)`**: a short payload reverts; the move of `v` with fee
`feeOf`. -/
theorem e60_inv {v t ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (v :: t :: ret :: S) M G) t_269b_c60 o) :
    MoveOk (Devm.getStor b sevm.currentTarget) sevm.caller t.toAdr v
        (feeOf (Devm.getStor b sevm.currentTarget) v) ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧
        Devm.getStor b' sevm.currentTarget =
          moveStor (Devm.getStor b sevm.currentTarget) sevm.caller t.toAdr v
            (feeOf (Devm.getStor b sevm.currentTarget) v) := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  useg h
  ucall h hc 61 t_2a03_c61
  obtain ⟨G1, e⟩ := e61_inv fork hc
  cases e
  clear hc
  useg h
  ucall h hc 63 t_2ac5_c63
  obtain ⟨G2, e⟩ := e63_inv fork hc
  cases e
  clear hc
  repeat ustep h
  unorm h
  ubranchTo h c2
  · iterate 4 ustep h
    unorm h
    have e13 := e13_inv fork h
    simp only [afterSload_getStor] at e13
    rw [feeOf_cap c2]
    rw [lit3, lit4] at *
    exact e13
  · have e13 := e13_inv fork h
    simp only [afterSload_getStor] at e13
    rw [feeOf_keep c2]
    rw [lit3] at *
    exact e13

/-- **Tree `0x233e` of entry 11, the moves of `StandardToken.transferFrom`**. -/
theorem e11_inv {p q f a v t r ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (h : SFunc.RunCut cert.prog sevm []
      (St b (p :: q :: f :: a :: v :: t :: r :: ret :: S) M G) t_233e_c11 (Seg.done o)) :
    MoveOk (Devm.getStor b sevm.currentTarget) r.toAdr t.toAdr v f ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧
        Devm.getStor b' sevm.currentTarget =
          moveStor (Devm.getStor b sevm.currentTarget) r.toAdr t.toAdr v f := by
  repeat ustep h
  ucall h hc 50 t_2ae0_c50
  obtain ⟨c1, G1, e⟩ := e50_inv fork hc
  cases e
  clear hc
  useg h
  ucall h hc 50 t_2ae0_c50
  obtain ⟨c2, G2, e⟩ := e50_inv fork hc
  cases e
  clear hc
  useg h
  ucall h hc 51 t_2af9_c51
  obtain ⟨c3, G3, e⟩ := e51_inv fork hc
  cases e
  clear hc
  useg h
  ubranchTo h c4
  · have hf : f ≠ 0 := by
      rintro rfl
      exact absurd c4 (by decide)
    useg h
    ucall h hc 51 t_2af9_c51
    obtain ⟨c5, G5, e⟩ := e51_inv fork hc
    cases e
    clear hc
    repeat ustep h
    obtain ⟨_, e⟩ := ric_ret h
    clear h
    obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
    clear e
    unorm c5
    refine ⟨⟨c1, c2, c3, fun _ => c5⟩, B, MB, GB, eo, ?_⟩
    rw [sB]
    simp only [Devm.addLog_getStor, afterSstore_getStor_self, afterSload_getStor, keccak_u,
      ff20_and_word, toAdr_toB256, getStorVal_afterSload, div_bexp_zero, lit2, gsv,
      AccumulatedWalk.getStorVal_afterSstore_self]
    unfold moveStor
    rw [if_neg hf]
    rfl
  · have hf : f = 0 := by
      have := toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero c4)
      apply B256.toNat_inj
      rw [B256.toNat_zero]
      exact Nat.le_zero.mp this
    subst hf
    repeat ustep h
    obtain ⟨_, e⟩ := ric_ret h
    clear h
    obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
    clear e
    refine ⟨⟨c1, c2, c3, fun h => absurd rfl h⟩, B, MB, GB, eo, ?_⟩
    rw [sB]
    simp only [Devm.addLog_getStor, afterSstore_getStor_self, afterSload_getStor]
    unfold moveStor
    rw [if_pos rfl]
    rfl

/-- An allowance entry (`mapping(address => mapping(address => uint256))` at slot 5). -/
def allowSlot (o s : Adr) : B256 := mapSlot s.toB256 (mapSlot o.toB256 5)

/-- The allowance's "unlimited" sentinel: `MAX_UINT`. -/
def maxUint : B256 := Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
  255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

/-- `transferFrom`'s allowance step: a limited allowance is lowered by `v`, an unlimited one kept. -/
def spendStor (σ : Stor) (o s : Adr) (v : B256) : Stor :=
  if σ.get (allowSlot o s) = maxUint then σ else σ.set (allowSlot o s) (σ.get (allowSlot o s) - v)

theorem eq_max_of {a : B256} (c : B256.eqCheck (B256.ltCheck a maxUint) 0 ≠ 0) : a = maxUint := by
  have h := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero c)
  apply B256.toNat_inj
  have hm : maxUint.toNat = 2 ^ 256 - 1 := by decide
  have ha := B256.toNat_lt a
  omega

/-- **Tree `0x2282` of entry 10, `transferFrom`'s allowance step and moves**. -/
theorem e10_inv {p q f a v t r ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (ha : a = (Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sevm.caller))
    (h : SFunc.RunCut cert.prog sevm []
      (St b (p :: q :: f :: a :: v :: t :: r :: ret :: S) M G) t_2282_c10 (Seg.done o)) :
    ((Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sevm.caller) ≠ maxUint →
        v.toNat ≤ ((Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sevm.caller)).toNat) ∧
      MoveOk (spendStor (Devm.getStor b sevm.currentTarget) r.toAdr sevm.caller v) r.toAdr t.toAdr v f ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧
        Devm.getStor b' sevm.currentTarget =
          moveStor (spendStor (Devm.getStor b sevm.currentTarget) r.toAdr sevm.caller v)
            r.toAdr t.toAdr v f := by
  subst ha
  repeat ustep h
  ubranchTo h c1
  · have hne : (Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sevm.caller) ≠ maxUint := by
      intro he
      rw [he] at c1
      exact absurd c1 (by decide +kernel)
    repeat ustep h
    ucall h hc 50 t_2ae0_c50
    obtain ⟨c2, G2, e⟩ := e50_inv fork hc
    cases e
    clear hc
    iterate 40 ustep h
    unorm h
    have e11 := e11_inv fork h
    simp only [afterSstore_getStor_self, afterSload_getStor] at e11
    have hs : spendStor (Devm.getStor b sevm.currentTarget) r.toAdr sevm.caller v =
        (Devm.getStor b sevm.currentTarget).set (allowSlot r.toAdr sevm.caller)
          ((Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sevm.caller) - v) := by
      unfold spendStor
      rw [if_neg hne]
    rw [hs]
    exact ⟨fun _ => c2, e11⟩
  · have he := eq_max_of c1
    have e11 := e11_inv fork h
    have hs : spendStor (Devm.getStor b sevm.currentTarget) r.toAdr sevm.caller v =
        Devm.getStor b sevm.currentTarget := by
      unfold spendStor
      rw [if_pos he]
    rw [hs]
    exact ⟨fun hne => absurd he hne, e11⟩

/-- **Entry 56, `StandardToken.transferFrom(r, t, v)`**. -/
theorem e56_inv {v t r ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (v :: t :: r :: ret :: S) M G) t_21ab_c56 o) :
    ((Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sevm.caller) ≠ maxUint →
        v.toNat ≤ ((Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sevm.caller)).toNat) ∧
      MoveOk (spendStor (Devm.getStor b sevm.currentTarget) r.toAdr sevm.caller v) r.toAdr t.toAdr v
        (feeOf (Devm.getStor b sevm.currentTarget) v) ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧
        Devm.getStor b' sevm.currentTarget =
          moveStor (spendStor (Devm.getStor b sevm.currentTarget) r.toAdr sevm.caller v)
            r.toAdr t.toAdr v (feeOf (Devm.getStor b sevm.currentTarget) v) := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  useg h
  ucall h hc 61 t_2a03_c61
  obtain ⟨G1, e⟩ := e61_inv fork hc
  cases e
  clear hc
  useg h
  ucall h hc 63 t_2ac5_c63
  obtain ⟨G2, e⟩ := e63_inv fork hc
  cases e
  clear hc
  repeat ustep h
  unorm h
  ubranchTo h c2
  · iterate 4 ustep h
    unorm h
    have e10 := e10_inv fork (a := (Devm.getStor b sevm.currentTarget).get
      (mapSlot sevm.caller.toB256 (mapSlot r.toAdr.toB256 5))) (by simp only [afterSload_getStor]; rfl) h
    simp only [afterSload_getStor] at e10
    rw [feeOf_cap c2]
    rw [lit3, lit4] at *
    exact e10
  · have e10 := e10_inv fork (a := (Devm.getStor b sevm.currentTarget).get
      (mapSlot sevm.caller.toB256 (mapSlot r.toAdr.toB256 5))) (by simp only [afterSload_getStor]; rfl) h
    simp only [afterSload_getStor] at e10
    rw [feeOf_keep c2]
    rw [lit3] at *
    exact e10

/-- The flag byte at offset 20 of a word: `paused` in slot 0, `deprecated` in slot 10. -/
def flag20 (w : B256) : B256 :=
  Bytes.toB256 [255] &&& w / B256.bexp (Bytes.toB256 [1, 0]) (Bytes.toB256 [20])

/-- `isBlackListed[a]`, the low byte of the mapping entry at slot 6. -/
def listedByte (σ : Stor) (a : Adr) : B256 := Bytes.toB256 [255] &&& σ.get (mapSlot a.toB256 6)

theorem lit6 : Bytes.toB256 [6] = 6 := by decide
theorem lit10 : Bytes.toB256 [10] = 10 := by decide

/-- **Entry 39, `TetherToken.transfer(t, v)`, not deprecated**. -/
theorem e39_inv {v t ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (hdep : flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (run : SFunc.Run cert.prog sevm (St b (v :: t :: ret :: S) M G) t_14f4_c39 o) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 0) = 0 ∧
      listedByte (Devm.getStor b sevm.currentTarget) sevm.caller = 0 ∧
      MoveOk (Devm.getStor b sevm.currentTarget) sevm.caller t.toAdr v
        (feeOf (Devm.getStor b sevm.currentTarget) v) ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧
        Devm.getStor b' sevm.currentTarget =
          moveStor (Devm.getStor b sevm.currentTarget) sevm.caller t.toAdr v
            (feeOf (Devm.getStor b sevm.currentTarget) v) := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  useg h
  ibranch h c2
  useg h
  unorm c1
  unorm c2
  rw [lit10] at h
  have h' := ric_branch h
  clear h
  rcases h' with ⟨c3, _, h⟩ | ⟨c3, _, h⟩
  · exfalso
    rw [show (Bytes.toB256 [255] &&& (Devm.getStor b sevm.currentTarget).get 10 /
      B256.bexp (Bytes.toB256 [1, 0]) (Bytes.toB256 [20])) = 0 from hdep] at c3
    exact absurd c3 (by decide)
  repeat ustep h
  ucall h hc 60 t_269b_c60
  obtain ⟨d1, B, MB, GB, e, sB⟩ := e60_inv fork hc
  cases e
  clear hc
  simp only [afterSload_getStor] at d1 sB
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B', MB', GB', eo, sB'⟩ := ret_named e
  exact ⟨zero_of_iszero3 c1, zero_of_iszero3 c2, d1, B', MB', GB', eo, by rw [sB', sB]⟩

/-- **Entry 23, `TetherToken.transferFrom(r, t, v)`, not deprecated**. -/
theorem e23_inv {v t r ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (hdep : flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (run : SFunc.Run cert.prog sevm (St b (v :: t :: r :: ret :: S) M G) t_0ebd_c23 o) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 0) = 0 ∧
      listedByte (Devm.getStor b sevm.currentTarget) r.toAdr = 0 ∧
      ((Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sevm.caller) ≠ maxUint →
        v.toNat ≤ ((Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sevm.caller)).toNat) ∧
      MoveOk (spendStor (Devm.getStor b sevm.currentTarget) r.toAdr sevm.caller v) r.toAdr t.toAdr v
        (feeOf (Devm.getStor b sevm.currentTarget) v) ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧
        Devm.getStor b' sevm.currentTarget =
          moveStor (spendStor (Devm.getStor b sevm.currentTarget) r.toAdr sevm.caller v)
            r.toAdr t.toAdr v (feeOf (Devm.getStor b sevm.currentTarget) v) := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  useg h
  ibranch h c2
  useg h
  unorm c1
  unorm c2
  rw [lit10] at h
  have h' := ric_branch h
  clear h
  rcases h' with ⟨c3, _, h⟩ | ⟨c3, _, h⟩
  · exfalso
    rw [show (Bytes.toB256 [255] &&& (Devm.getStor b sevm.currentTarget).get 10 /
      B256.bexp (Bytes.toB256 [1, 0]) (Bytes.toB256 [20])) = 0 from hdep] at c3
    exact absurd c3 (by decide)
  repeat ustep h
  ucall h hc 56 t_21ab_c56
  obtain ⟨d0, d1, B, MB, GB, e, sB⟩ := e56_inv fork hc
  cases e
  clear hc
  simp only [afterSload_getStor] at d0 d1 sB
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B', MB', GB', eo, sB'⟩ := ret_named e
  exact ⟨zero_of_iszero3 c1, zero_of_iszero3 c2, d0, d1, B', MB', GB', eo, by rw [sB', sB]⟩

/-- **Entry 57, `BasicToken.balanceOf(a)`**. -/
theorem e57_inv {a ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (a :: ret :: S) M G) t_2652_c57 o) :
    ∃ b' M' G', o = .returned (St b' ((Devm.getStor b sevm.currentTarget).get (balSlot a.toAdr) :: S) M' G') ∧
      Devm.getStor b' = Devm.getStor b := by
  have h := run.cut
  clear run
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  cases e
  simp only [keccak_u, ff20_and_word, toAdr_toB256, lit2, gsv, balSlot]
  refine ⟨_, _, _, rfl, funext fun x => afterSload_getStor _ _ _ x⟩

/-- **Entry 33, `TetherToken.balanceOf(a)`, not deprecated**. -/
theorem e33_inv {a ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (hdep : flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (run : SFunc.Run cert.prog sevm (St b (a :: ret :: S) M G) t_1239_c33 o) :
    ∃ b' M' G', o = .returned (St b' ((Devm.getStor b sevm.currentTarget).get (balSlot a.toAdr) :: S) M' G') ∧
      Devm.getStor b' = Devm.getStor b := by
  have h := run.cut
  clear run
  useg h
  rw [lit10] at h
  have h' := ric_branch h
  clear h
  rcases h' with ⟨c3, _, h⟩ | ⟨c3, _, h⟩
  · exfalso
    rw [show (Bytes.toB256 [255] &&& (Devm.getStor b sevm.currentTarget).get 10 /
      B256.bexp (Bytes.toB256 [1, 0]) (Bytes.toB256 [20])) = 0 from hdep] at c3
    exact absurd c3 (by decide)
  repeat ustep h
  ucall h hc 57 t_2652_c57
  obtain ⟨B, MB, GB, e, sB⟩ := e57_inv fork hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  cases e
  simp only [afterSload_getStor] at sB ⊢
  have sB' := funext fun x => (congrFun sB x).trans (afterSload_getStor _ _ _ x)
  exact ⟨_, _, _, rfl, sB'⟩

theorem lit4w : Bytes.toB256 [4] = 4 := by decide
theorem lit36 : Bytes.toB256 [32] + Bytes.toB256 [4] = 36 := by decide

/-- **The `balanceOf(a)` frame of TetherToken, not deprecated**: it keeps the storage. -/
theorem frame_balanceOf {post : Devm} (fork : CoveredFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0x70a08231)
    (hdep : flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    Devm.getStor post = Devm.getStor b := by
  have h := run.cut
  clear run
  iterate 7 ustep h
  ibranch h c0
  iterate 7 ustep h
  rw [legacy_selector_word, sel] at h
  repeat udisp h
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ucall h hc 33 t_1239_c33
  obtain ⟨B, MB, GB, e, sB⟩ := e33_inv fork hdep hc
  cases e
  clear hc
  repeat ustep h
  rw [ric_return_getStor h, sB]

/-- **The `transfer(to, v)` frame of TetherToken, not deprecated.** -/
theorem frame_transfer {post : Devm} (fork : CoveredFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0xa9059cbb)
    (hdep : flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 0) = 0 ∧
      listedByte (Devm.getStor b sevm.currentTarget) sevm.caller = 0 ∧
      MoveOk (Devm.getStor b sevm.currentTarget) sevm.caller (Sevm.dataWord sevm 4).toAdr
        (Sevm.dataWord sevm 36) (feeOf (Devm.getStor b sevm.currentTarget) (Sevm.dataWord sevm 36)) ∧
      Devm.getStor post sevm.currentTarget =
        moveStor (Devm.getStor b sevm.currentTarget) sevm.caller (Sevm.dataWord sevm 4).toAdr
          (Sevm.dataWord sevm 36) (feeOf (Devm.getStor b sevm.currentTarget) (Sevm.dataWord sevm 36)) := by
  have h := run.cut
  clear run
  iterate 7 ustep h
  ibranch h c0
  iterate 7 ustep h
  rw [legacy_selector_word, sel] at h
  repeat udisp h
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ucall h hc 39 t_14f4_c39
  obtain ⟨d1, d2, d3, B, MB, GB, e, sB⟩ := e39_inv fork hdep hc
  cases e
  clear hc
  repeat ustep h
  have sp := ric_stop_keeps h
  clear h
  simp only [lit36] at d3 sB
  simp only [ff20_and_word, toAdr_toB256, lit4w] at d3 sB
  exact ⟨d1, d2, d3, by rw [sp, sB]⟩

/-- **The `transferFrom(r, to, v)` frame of TetherToken, not deprecated.** -/
theorem frame_transferFrom {post : Devm} (fork : CoveredFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0x23b872dd)
    (hdep : flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 0) = 0 ∧
      listedByte (Devm.getStor b sevm.currentTarget) (Sevm.dataWord sevm 4).toAdr = 0 ∧
      ((Devm.getStor b sevm.currentTarget).get (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller) ≠ maxUint →
        (Sevm.dataWord sevm 68).toNat ≤
          ((Devm.getStor b sevm.currentTarget).get (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller)).toNat) ∧
      MoveOk (spendStor (Devm.getStor b sevm.currentTarget) (Sevm.dataWord sevm 4).toAdr sevm.caller
          (Sevm.dataWord sevm 68)) (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr
        (Sevm.dataWord sevm 68) (feeOf (Devm.getStor b sevm.currentTarget) (Sevm.dataWord sevm 68)) ∧
      Devm.getStor post sevm.currentTarget =
        moveStor (spendStor (Devm.getStor b sevm.currentTarget) (Sevm.dataWord sevm 4).toAdr sevm.caller
            (Sevm.dataWord sevm 68)) (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr
          (Sevm.dataWord sevm 68) (feeOf (Devm.getStor b sevm.currentTarget) (Sevm.dataWord sevm 68)) := by
  have h := run.cut
  clear run
  iterate 7 ustep h
  ibranch h c0
  iterate 7 ustep h
  rw [legacy_selector_word, sel] at h
  repeat udisp h
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ucall h hc 23 t_0ebd_c23
  obtain ⟨d1, d2, d0, d3, B, MB, GB, e, sB⟩ := e23_inv fork hdep hc
  cases e
  clear hc
  repeat ustep h
  have sp := ric_stop_keeps h
  clear h
  simp only [lit36, show Bytes.toB256 [32] + 36 = 68 by decide] at d0 d2 d3 sB
  simp only [ff20_and_word, toAdr_toB256, lit4w] at d0 d2 d3 sB
  exact ⟨d1, d2, d0, d3, by rw [sp, sB]⟩

/-! ## Credits: a move lowers only its source -/

theorem set_get_ge {σ : Stor} {j k : B256} {x w : B256}
    (hnof : x.toNat + (σ.get j).toNat < 2 ^ 256) (hw : w = σ.get j + x) :
    (σ.get k).toNat ≤ ((σ.set j w).get k).toNat := by
  by_cases hk : k = j
  · subst hk
    have hn : (σ.get k).toNat + x.toNat < 2 ^ 256 := by omega
    rw [Stor.get_set_self, hw, B256.toNat_add_eq_of_nof _ _ hn]
    omega
  · rw [Stor.get_set_ne _ (Ne.symm hk)]

/-- **A move does not lower any slot but its source's entry.**  The recipient's entry and the owner's
rise by what the move credits, and every other slot is untouched.  The slot apartness is the
consumer's hash premise. -/
theorem moveStor_ge {σ : Stor} {src dst : Adr} {v f k : B256} (ok : MoveOk σ src dst v f)
    (hk : k ≠ balSlot src) :
    (σ.get k).toNat ≤ ((moveStor σ src dst v f).get k).toNat := by
  have h1 : (σ.get k).toNat = ((debit σ src v).get k).toNat := by
    unfold debit
    rw [Stor.get_set_ne _ (Ne.symm hk)]
  have h2 : ((debit σ src v).get k).toNat ≤ ((credit (debit σ src v) dst (v - f)).get k).toNat :=
    set_get_ge (by exact ok.credit_lt) rfl
  unfold moveStor
  split
  · omega
  · rename_i hf
    have h3 := set_get_ge (σ := credit (debit σ src v) dst (v - f)) (k := k) (ok.owner_lt hf) rfl
    exact (h1.le.trans h2).trans h3

end Blanc.Lift.Usdt
