import Blanc.Lift.Curve3Pool.U3Bounds
import Blanc.Lift.Curve3Pool.U3History
import Blanc.Lift.Curve3Pool.StepCallFree
import Blanc.Lift.Curve3Pool.Refine

/-!
# What one step of the pool does to its books of one coin

`step_flow`: an accepted step moves the recorded balance of coin `k` in one of three ways, each read off the
model's own calls and answers:

* `plain`: the books fall by at least what it pushes and rise by at most what it pulls;
* `measured`: the fee coin's pull, credited by the difference of its two `balanceOf` answers;
* `read`: `withdraw_admin_fees` and `donate_admin_fees`, whose books and pushes together are at most the coin's answer.

This is pure model arithmetic, with nothing about what the coins do.
-/

namespace Blanc.Composition.Curve3PoolBacked

open Blanc.Lift.Curve3Pool Blanc.StableSwapNewton

/-- What the calls pull from coin `k`, as they name it. -/
def pulled (k : Fin 3) : List ExtCall → Nat
  | [] => 0
  | .pull i _ a :: cs => (if i = k then a else 0) + pulled k cs
  | _ :: cs => pulled k cs

/-- What the calls push out of coin `k`, as they name it. -/
def pushed (k : Fin 3) : List ExtCall → Nat
  | [] => 0
  | .push i _ a :: cs => (if i = k then a else 0) + pushed k cs
  | _ :: cs => pushed k cs

/-- **How a step moves the books of coin `k`.** -/
inductive Flow (s : State) (e : Env) (o : Out) (k : Fin 3) : Prop
  /-- By what it names. -/
  | plain (books : o.state.balances.get k + pushed k o.calls ≤ s.balances.get k + pulled k o.calls)
      (fits : pulled k o.calls < 2 ^ 256) (notFee : k = feeIndex → pulled k o.calls = 0)
  /-- The fee coin's pull, by what the coin answers around it. -/
  | measured {p q : Nat} (fee : k = feeIndex) (hp : (e.coin k).balPre = some p) (hq : (e.coin k).balPost = some q)
      (le : p ≤ q) (books : o.state.balances.get k ≤ s.balances.get k + (q - p)) (out : pushed k o.calls = 0)
  /-- From what the coin answers. -/
  | read {p : Nat} (hp : (e.coin k).balPre = some p) (books : o.state.balances.get k + pushed k o.calls ≤ p)
      (inn : pulled k o.calls = 0)

theorem pulled_append (k : Fin 3) : ∀ xs ys : List ExtCall, pulled k (xs ++ ys) = pulled k xs + pulled k ys
  | [], _ => by simp only [List.nil_append, pulled, Nat.zero_add]
  | c :: xs, ys => by
    cases c <;> simp only [List.cons_append, pulled, pulled_append k xs ys, Nat.add_assoc]

theorem pushed_append (k : Fin 3) : ∀ xs ys : List ExtCall, pushed k (xs ++ ys) = pushed k xs + pushed k ys
  | [], _ => by simp only [List.nil_append, pushed, Nat.zero_add]
  | c :: xs, ys => by
    cases c <;> simp only [List.cons_append, pushed, pushed_append k xs ys, Nat.add_assoc]

theorem pulled_pullCalls (c : Nat) (am : V3) (k : Fin 3) :
    pulled k (pullCalls c am) = if am.get k > 0 then am.get k else 0 := by
  match k with
  | 0 | 1 | 2 =>
    unfold pullCalls
    by_cases h0 : am.get 0 > 0 <;> by_cases h1 : am.get 1 > 0 <;> by_cases h2 : am.get 2 > 0 <;>
      simp only [
        Fin.isValue, gt_iff_lt, h0, ↓reduceIte, Option.some.injEq, List.filterMap_cons_some, h1, h2, List.filterMap_nil, pulled, one_ne_zero, Fin.reduceEq, add_zero, List.filterMap_cons_none, zero_ne_one, zero_add]

theorem pushed_pullCalls (c : Nat) (am : V3) (k : Fin 3) : pushed k (pullCalls c am) = 0 := by
  unfold pullCalls
  by_cases h0 : am.get 0 > 0 <;> by_cases h1 : am.get 1 > 0 <;> by_cases h2 : am.get 2 > 0 <;>
    simp only [
      gt_iff_lt, Fin.isValue, h0, ↓reduceIte, Option.some.injEq, List.filterMap_cons_some, h1, h2, List.filterMap_nil, pushed, List.filterMap_cons_none]

theorem pushed_pushCalls (c : Nat) (am : V3) (k : Fin 3) : pushed k (pushCalls c am) = am.get k := by
  match k with
  | 0 | 1 | 2 =>
    unfold pushCalls
    by_cases h0 : am.get 0 ≠ 0 <;> by_cases h1 : am.get 1 ≠ 0 <;> by_cases h2 : am.get 2 ≠ 0 <;>
      simp_all only [
        Fin.isValue, ne_eq, ite_not, ↓reduceIte, Option.some.injEq, List.filterMap_cons_some, List.filterMap_nil, pushed, one_ne_zero, Fin.reduceEq, add_zero, Decidable.not_not, List.filterMap_cons_none, zero_ne_one, zero_add]

theorem pulled_pushCalls (c : Nat) (am : V3) (k : Fin 3) : pulled k (pushCalls c am) = 0 := by
  unfold pushCalls
  by_cases h0 : am.get 0 ≠ 0 <;> by_cases h1 : am.get 1 ≠ 0 <;> by_cases h2 : am.get 2 ≠ 0 <;>
    simp only [
      ne_eq, ite_not, Fin.isValue, h0, ↓reduceIte, Option.some.injEq, List.filterMap_cons_some, h1, h2, List.filterMap_nil, pulled, ite_eq_left_iff, reduceCtorEq, imp_self, List.filterMap_cons_none]

/-- The stored balance never exceeds the new one. -/
theorem feeAt_stored_le {fee adm D0 D1 : Nat} {old new : V3} {i : Fin 3} {f st af : Nat}
    (h : feeAt fee adm D0 D1 old new i = some (f, st, af)) : st ≤ new.get i := by
  unfold feeAt at h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  dsimp only at h
  split at h <;> obtain ⟨_, -, h⟩ := bind_some h <;> obtain ⟨p, hp, h⟩ := bind_some h <;>
    obtain ⟨f', hf, h⟩ := bind_some h <;> obtain ⟨q, hq, h⟩ := bind_some h <;>
    obtain ⟨r, hr, h⟩ := bind_some h <;> obtain ⟨st', hst, h⟩ := bind_some h <;>
    obtain ⟨af', haf, h⟩ := bind_some h <;> cases Option.some.inj h <;>
    · rw [(chkSub_some hst).1]
      exact Nat.sub_le _ _

theorem feeLoop_stored_le {fee adm D0 D1 : Nat} {old new fees st af : V3}
    (h : feeLoop fee adm D0 D1 old new = some (fees, st, af)) : ∀ k, st.get k ≤ new.get k := by
  unfold feeLoop at h
  obtain ⟨r0, h0, h⟩ := bind_some h
  obtain ⟨r1, h1, h⟩ := bind_some h
  obtain ⟨r2, h2, h⟩ := bind_some h
  cases Option.some.inj h
  intro k
  match k with
  | 0 => exact feeAt_stored_le (st := r0.2.1) (f := r0.1) (af := r0.2.2) h0
  | 1 => exact feeAt_stored_le (st := r1.2.1) (f := r1.1) (af := r1.2.2) h1
  | 2 => exact feeAt_stored_le (st := r2.2.1) (f := r2.1) (af := r2.2.2) h2

/-- One coin's `pullAdd`: what it credits, and the sum fits. -/
theorem pullAdd_some {e : Env} {T : Nat} {old am : V3} {i : Fin 3} {r : Nat} (h : pullAdd e T old am i = some r) :
    ∃ cr, (if am.get i > 0 then pullIn e i (am.get i) else some 0) = some cr ∧ chkAdd (old.get i) cr = some r := by
  unfold pullAdd at h
  dsimp only at h
  split at h <;> obtain ⟨_, -, h⟩ := bind_some h <;>
    by_cases pos : am.get i > 0 <;> simp only [pos, ↓reduceIte] at h ⊢ <;>
    first
    | exact bind_some h
    | exact ⟨0, rfl, h⟩

/-- `add_liquidity`'s accepted shape: its new balances, stored balances at most those, and its calls. -/
theorem add_shape {s : State} {e : Env} {am : V3} {mm : Nat} {o : Out} (h : addLiquidity s e am mm = some o) :
    ∃ T new stored mint, V3.ofFnM (pullAdd e T s.balances am) = some new ∧ (∀ j, stored.get j ≤ new.get j) ∧
      o.state.balances = stored ∧ o.calls = pullCalls e.caller am ++ [ExtCall.mint e.caller mint] := by
  unfold addLiquidity at h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨fee, -, h⟩ := bind_some h
  obtain ⟨amp, -, h⟩ := bind_some h
  obtain ⟨T, -, h⟩ := bind_some h
  dsimp only at h
  by_cases hT : T > 0
  · have hT0 : T ≠ 0 := Nat.ne_of_gt hT
    simp only [hT, hT0, ↓reduceIte] at h
    obtain ⟨D0, -, h⟩ := bind_some h
    obtain ⟨new, hnew, h⟩ := bind_some h
    obtain ⟨D1, -, h⟩ := bind_some h
    obtain ⟨_, -, h⟩ := bind_some h
    obtain ⟨x3, hfl, h⟩ := bind_some h
    obtain ⟨fees, stored, after⟩ := x3
    obtain ⟨D2, -, h⟩ := bind_some h
    obtain ⟨x4, hx4, h⟩ := bind_some h
    cases Option.some.inj hx4
    obtain ⟨d, -, h⟩ := bind_some h
    obtain ⟨m, -, h⟩ := bind_some h
    obtain ⟨mint, -, h⟩ := bind_some h
    obtain ⟨_, -, h⟩ := bind_some h
    obtain ⟨_, -, h⟩ := bind_some h
    obtain ⟨_, -, h⟩ := bind_some h
    cases Option.some.inj h
    exact ⟨T, new, stored, mint, hnew, feeLoop_stored_le hfl, rfl, rfl⟩
  · have hT0 : T = 0 := by omega
    subst hT0
    simp only [Nat.lt_irrefl, gt_iff_lt, ↓reduceIte] at h
    obtain ⟨D0, -, h⟩ := bind_some h
    obtain ⟨new, hnew, h⟩ := bind_some h
    obtain ⟨D1, -, h⟩ := bind_some h
    obtain ⟨_, -, h⟩ := bind_some h
    obtain ⟨x, hx, h⟩ := bind_some h
    cases Option.some.inj hx
    obtain ⟨m, hm, h⟩ := bind_some h
    cases Option.some.inj hm
    iterate 3 obtain ⟨_, -, h⟩ := bind_some h
    cases Option.some.inj h
    exact ⟨0, new, new, _, hnew, fun _ => Nat.le_refl _, rfl, rfl⟩

theorem flow_addLiquidity {s : State} {e : Env} {am : V3} {mm : Nat} {o : Out}
    (h : addLiquidity s e am mm = some o) (k : Fin 3) : Flow s e o k := by
  obtain ⟨T, new, stored, mint, hnew, storedLe, hb, hc⟩ := add_shape h
  obtain ⟨credited, hcr, hk⟩ := pullAdd_some (ofFnM_some hnew k)
  have hadd := chkAdd_some hk
  have hlt := chkAdd_some_lt hk
  have sk := storedLe k
  have ep : pulled k o.calls = if am.get k > 0 then am.get k else 0 := by
    rw [hc, pulled_append, pulled_pullCalls]
    rfl
  have eq : pushed k o.calls = 0 := by
    rw [hc, pushed_append, pushed_pullCalls]
    rfl
  rw [← hb] at sk
  have wide : (2 : Nat) ^ 256 = wordSize := rfl
  by_cases pos : am.get k > 0
  · rw [if_pos pos] at hcr ep
    unfold pullIn at hcr
    by_cases fee : k = feeIndex
    · rw [if_pos fee] at hcr
      obtain ⟨p, hp, hcr⟩ := bind_some hcr
      obtain ⟨_, -, hcr⟩ := bind_some hcr
      obtain ⟨q, hq, hcr⟩ := bind_some hcr
      obtain ⟨hc', hle⟩ := chkSub_some hcr
      exact .measured fee hp hq hle (by omega) eq
    · rw [if_neg fee] at hcr
      obtain ⟨_, -, hcr⟩ := bind_some hcr
      cases Option.some.inj hcr
      exact .plain (by omega) (by omega) (fun f => absurd f fee)
  · rw [if_neg pos] at hcr ep
    cases Option.some.inj hcr
    exact .plain (by omega) (by omega) (fun _ => ep)

theorem flow_exchange {s : State} {e : Env} {i j : Fin 3} {dx md : Nat} {o : Out}
    (h : exchange s e i j dx md = some o) (k : Fin 3) : Flow s e o k := by
  unfold exchange at h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨xp, -, h⟩ := bind_some h
  obtain ⟨dxw, hdxw, h⟩ := bind_some h
  obtain ⟨p1, -, h⟩ := bind_some h
  obtain ⟨q1, -, h⟩ := bind_some h
  obtain ⟨x, -, h⟩ := bind_some h
  obtain ⟨amp, -, h⟩ := bind_some h
  obtain ⟨y, hy, h⟩ := bind_some h
  obtain ⟨d1, -, h⟩ := bind_some h
  obtain ⟨dy, -, h⟩ := bind_some h
  obtain ⟨p2, -, h⟩ := bind_some h
  obtain ⟨dyFee, -, h⟩ := bind_some h
  obtain ⟨d3, -, h⟩ := bind_some h
  obtain ⟨p3, -, h⟩ := bind_some h
  obtain ⟨dyOut, -, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨p4, -, h⟩ := bind_some h
  obtain ⟨adm1, -, h⟩ := bind_some h
  obtain ⟨p5, -, h⟩ := bind_some h
  obtain ⟨adm2, -, h⟩ := bind_some h
  obtain ⟨bi, hbi, h⟩ := bind_some h
  obtain ⟨d6, hd6, h⟩ := bind_some h
  obtain ⟨bj, hbj, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  cases Option.some.inj h
  have hij : i ≠ j := fun e => by
    unfold getYChk at hy
    simp only [e, ↓reduceIte, reduceCtorEq] at hy
  have hbiE := chkAdd_some hbi
  have hbiL := chkAdd_some_lt hbi
  obtain ⟨hd6E, hd6L⟩ := chkSub_some hd6
  obtain ⟨hbjE, hbjL⟩ := chkSub_some hbj
  have wide : (2 : Nat) ^ 256 = wordSize := rfl
  have ep : pulled k [ExtCall.pull i e.caller dx, ExtCall.push j e.caller dyOut] = if i = k then dx else 0 := by
    simp only [pulled, Nat.add_zero]
  have eq : pushed k [ExtCall.pull i e.caller dx, ExtCall.push j e.caller dyOut] = if j = k then dyOut else 0 := by
    simp only [pushed, Nat.add_zero]
  by_cases kj : k = j
  · subst kj
    have ni : i ≠ k := hij
    refine .plain ?_ ?_ ?_
    · dsimp only
      rw [ep, eq, if_neg ni, if_pos rfl, V3.get_set_self]
      omega
    · rw [ep, if_neg ni]
      omega
    · intro _
      rw [ep, if_neg ni]
  · have nj : j ≠ k := fun e => kj e.symm
    by_cases ki : k = i
    · subst ki
      have hget : ((s.balances.set k bi).set j bj).get k = bi := by
        rw [V3.get_set_ne _ kj, V3.get_set_self]
      unfold pullIn at hdxw
      by_cases fee : k = feeIndex
      · rw [if_pos fee] at hdxw
        obtain ⟨p, hp, hdxw⟩ := bind_some hdxw
        obtain ⟨_, -, hdxw⟩ := bind_some hdxw
        obtain ⟨q, hq, hdxw⟩ := bind_some hdxw
        obtain ⟨hc', hle⟩ := chkSub_some hdxw
        refine .measured fee hp hq hle ?_ ?_
        · dsimp only
          rw [hget]
          omega
        · rw [eq, if_neg nj]
      · rw [if_neg fee] at hdxw
        obtain ⟨_, -, hdxw⟩ := bind_some hdxw
        cases Option.some.inj hdxw
        refine .plain ?_ ?_ (fun f => absurd f fee)
        · dsimp only
          rw [ep, eq, if_pos rfl, if_neg nj, hget]
          omega
        · rw [ep, if_pos rfl]
          omega
    · have ni : i ≠ k := fun e => ki e.symm
      refine .plain ?_ ?_ ?_
      · dsimp only
        rw [ep, eq, if_neg ni, if_neg nj, V3.get_set_ne _ kj, V3.get_set_ne _ ki]
      · rw [ep, if_neg ni]
        omega
      · intro _
        rw [ep, if_neg ni]

theorem flow_removeLiquidity {s : State} {e : Env} {a : Nat} {mins : V3} {o : Out}
    (h : removeLiquidity s e a mins = some o) (k : Fin 3) : Flow s e o k := by
  unfold removeLiquidity at h
  obtain ⟨T, -, h⟩ := bind_some h
  obtain ⟨vals, -, h⟩ := bind_some h
  obtain ⟨b, hb, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨T', -, h⟩ := bind_some h
  cases Option.some.inj h
  obtain ⟨hE, hL⟩ := chkSub_some (ofFnM_some hb k)
  have ep : pulled k [ExtCall.push 0 e.caller vals.v0, ExtCall.push 1 e.caller vals.v1,
      ExtCall.push 2 e.caller vals.v2, ExtCall.burn e.caller a] = 0 := by
    simp only [pulled]
  have eq : pushed k [ExtCall.push 0 e.caller vals.v0, ExtCall.push 1 e.caller vals.v1,
      ExtCall.push 2 e.caller vals.v2, ExtCall.burn e.caller a] = vals.get k := by
    match k with
    | 0 | 1 | 2 => simp only [
      pushed, Fin.isValue, ↓reduceIte, one_ne_zero, Fin.reduceEq, add_zero, V3.get, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_ne_one, zero_add, Nat.one_mod, Nat.mod_succ, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
  refine .plain ?_ (by rw [ep]; exact Nat.two_pow_pos _) (fun _ => ep)
  dsimp only
  rw [ep, eq, hE]
  omega

theorem flow_imbalance {s : State} {e : Env} {am : V3} {mb : Nat} {o : Out}
    (h : removeLiquidityImbalance s e am mb = some o) (k : Fin 3) : Flow s e o k := by
  unfold removeLiquidityImbalance at h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨T, -, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨fee, -, h⟩ := bind_some h
  obtain ⟨amp, -, h⟩ := bind_some h
  obtain ⟨D0, -, h⟩ := bind_some h
  obtain ⟨new, hnew, h⟩ := bind_some h
  obtain ⟨D1, -, h⟩ := bind_some h
  obtain ⟨x3, hfl, h⟩ := bind_some h
  obtain ⟨fees, stored, after⟩ := x3
  iterate 9 obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨T', -, h⟩ := bind_some h
  cases Option.some.inj h
  obtain ⟨hE, hL⟩ := chkSub_some (ofFnM_some hnew k)
  have sk := feeLoop_stored_le hfl k
  have ep : ∀ b, pulled k (ExtCall.burn e.caller b :: pushCalls e.caller am) = 0 := fun _ => by
    simp only [pulled, pulled_pushCalls]
  have eq : ∀ b, pushed k (ExtCall.burn e.caller b :: pushCalls e.caller am) = am.get k := fun _ => by
    simp only [pushed, pushed_pushCalls]
  refine .plain ?_ (by rw [ep]; exact Nat.two_pow_pos _) (fun _ => ep _)
  dsimp only
  rw [ep, eq]
  omega

theorem flow_oneCoin {s : State} {e : Env} {a : Nat} {i : Fin 3} {mn : Nat} {o : Out}
    (h : removeLiquidityOneCoin s e a i mn = some o) (k : Fin 3) : Flow s e o k := by
  unfold removeLiquidityOneCoin at h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨x2, -, h⟩ := bind_some h
  obtain ⟨dy, dyFee⟩ := x2
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨p, -, h⟩ := bind_some h
  obtain ⟨r, -, h⟩ := bind_some h
  obtain ⟨take, htake, h⟩ := bind_some h
  obtain ⟨bi, hbi, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  cases Option.some.inj h
  have ht := chkAdd_some htake
  obtain ⟨hE, hL⟩ := chkSub_some hbi
  have ep : pulled k [ExtCall.burn e.caller a, ExtCall.push i e.caller dy] = 0 := by
    simp only [pulled]
  have eq : pushed k [ExtCall.burn e.caller a, ExtCall.push i e.caller dy] = if i = k then dy else 0 := by
    simp only [pushed, Nat.add_zero]
  refine .plain ?_ (by rw [ep]; exact Nat.two_pow_pos _) (fun _ => ep)
  dsimp only
  rw [ep, eq]
  by_cases ik : i = k
  · subst ik
    rw [if_pos rfl, V3.get_set_self]
    omega
  · rw [if_neg ik, V3.get_set_ne _ (fun e => ik e.symm)]

theorem flow_withdraw {s : State} {e : Env} {o : Out} (h : withdrawAdminFees s e = some o) (k : Fin 3) :
    Flow s e o k := by
  unfold withdrawAdminFees at h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨v, hv, h⟩ := bind_some h
  cases Option.some.inj h
  have hk := ofFnM_some hv k
  obtain ⟨p, hp, hk⟩ := bind_some hk
  obtain ⟨x, hx, hk⟩ := bind_some hk
  obtain ⟨hE, hL⟩ := chkSub_some hx
  dsimp only at hk
  have hvk : v.get k = x := by
    split at hk <;> obtain ⟨_, -, hk⟩ := bind_some hk <;> exact (Option.some.inj hk).symm
  refine .read hp ?_ (pulled_pushCalls _ _ _)
  dsimp only
  rw [pushed_pushCalls, hvk, hE]
  omega

theorem flow_donate {s : State} {e : Env} {o : Out} (h : donateAdminFees s e = some o) (k : Fin 3) :
    Flow s e o k := by
  unfold donateAdminFees at h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨b, hb, h⟩ := bind_some h
  cases Option.some.inj h
  exact .read (ofFnM_some hb k) (Nat.le_refl _) rfl

/-- A step that names no call and keeps the balances. -/
theorem flow_keep {s : State} {e : Env} {o : Out} {k : Fin 3} (hb : o.state.balances = s.balances) (hc : o.calls = []) :
    Flow s e o k := by
  refine .plain ?_ ?_ ?_
  · rw [hb, hc]
    exact Nat.le_refl _
  · rw [hc]
    exact Nat.two_pow_pos _
  · intro _
    rw [hc]
    rfl

theorem pull_mem_pullCalls {c src a : Nat} {am : V3} {j : Fin 3} (h : ExtCall.pull j src a ∈ pullCalls c am) : src = c := by
  unfold pullCalls at h
  obtain ⟨k, -, hk⟩ := List.mem_filterMap.mp h
  split at hk
  · cases Option.some.inj hk
    rfl
  · cases hk

theorem pull_not_mem_pushCalls {c src a : Nat} {am : V3} {j : Fin 3} : ExtCall.pull j src a ∉ pushCalls c am := by
  intro h
  unfold pushCalls at h
  obtain ⟨k, -, hk⟩ := List.mem_filterMap.mp h
  split at hk
  · cases Option.some.inj hk
  · cases hk

/-- **Every pull a step makes is from its caller.** -/
theorem step_pull_src {s : State} {e : Env} {c : Call} {o : Out} (h : step s e c = some o) {j : Fin 3} {src a : Nat}
    (mem : ExtCall.pull j src a ∈ o.calls) : src = e.caller := by
  have hb := pool_step_body h
  cases c with
  | addLiquidity am m =>
    obtain ⟨_, _, _, _, _, _, _, hc⟩ := add_shape hb
    rw [hc, List.mem_append] at mem
    rcases mem with mem | mem
    · exact pull_mem_pullCalls mem
    · simp only [List.mem_singleton, reduceCtorEq] at mem
  | exchange i' j' dx m =>
    simp only [body, Option.bind_eq_bind] at hb
    obtain ⟨_, -, hb⟩ := bind_some hb
    obtain ⟨_, -, hb⟩ := bind_some hb
    unfold exchange at hb
    repeat obtain ⟨_, -, hb⟩ := bind_some hb
    cases Option.some.inj hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, ExtCall.pull.injEq, reduceCtorEq] at mem
    exact mem.2.1
  | removeLiquidity a' m =>
    replace hb : removeLiquidity s e a' m = some o := hb
    unfold removeLiquidity at hb
    repeat obtain ⟨_, -, hb⟩ := bind_some hb
    cases Option.some.inj hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at mem
  | removeLiquidityImbalance am m =>
    replace hb : removeLiquidityImbalance s e am m = some o := hb
    unfold removeLiquidityImbalance at hb
    repeat obtain ⟨_, -, hb⟩ := bind_some hb
    cases Option.some.inj hb
    simp only [List.mem_cons, reduceCtorEq, false_or] at mem
    exact absurd mem pull_not_mem_pushCalls
  | removeLiquidityOneCoin a' i' m =>
    simp only [body, Option.bind_eq_bind] at hb
    obtain ⟨_, -, hb⟩ := bind_some hb
    unfold removeLiquidityOneCoin at hb
    repeat obtain ⟨_, -, hb⟩ := bind_some hb
    cases Option.some.inj hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at mem
  | withdrawAdminFees =>
    replace hb : withdrawAdminFees s e = some o := hb
    unfold withdrawAdminFees at hb
    repeat obtain ⟨_, -, hb⟩ := bind_some hb
    cases Option.some.inj hb
    exact absurd mem pull_not_mem_pushCalls
  | _ =>
    rw [step_calls_nil rfl h] at mem
    exact absurd mem List.not_mem_nil

/-- **How an accepted step moves the books of each coin.** -/
theorem step_flow {s : State} {e : Env} {c : Call} {o : Out} (h : step s e c = some o) (k : Fin 3) : Flow s e o k := by
  have hb := pool_step_body h
  cases c with
  | addLiquidity am m => exact flow_addLiquidity hb k
  | exchange i j dx m =>
    simp only [body, Option.bind_eq_bind] at hb
    obtain ⟨i', -, hb⟩ := bind_some hb
    obtain ⟨j', -, hb⟩ := bind_some hb
    exact flow_exchange hb k
  | removeLiquidity a m => exact flow_removeLiquidity hb k
  | removeLiquidityImbalance am m => exact flow_imbalance hb k
  | removeLiquidityOneCoin a i m =>
    simp only [body, Option.bind_eq_bind] at hb
    obtain ⟨i', -, hb⟩ := bind_some hb
    exact flow_oneCoin hb k
  | withdrawAdminFees => exact flow_withdraw hb k
  | donateAdminFees => exact flow_donate hb k
  | _ =>
    refine flow_keep (V3.ext_get fun j => ?_) (step_calls_nil rfl h)
    refine Eq.symm ((step_keeps h).1 (.bal j) ?_)
    simp only [footprint, balFlds, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self, not_false_eq_true]

end Blanc.Composition.Curve3PoolBacked
