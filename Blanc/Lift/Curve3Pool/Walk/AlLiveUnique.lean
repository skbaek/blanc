import Blanc.Lift.Curve3Pool.Walk.AlLiveModel

/-!
# `add_liquidity`: the output determined by the stored balances and the fees

`al_out_unique`: two successful model `add_liquidity` steps from the same state and arguments,
in environments agreeing on the time, the caller and the supply, whose outputs store the same
balances and log the same fees, are the same output. (The environments may differ in the fee
coin's balance answers: the stored balances and fees pin its credit.)
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The fees `add_liquidity`'s event logs. -/
def alFees (o : Out) : V3 :=
  match o.events with
  | [.addLiquidity _ _ f _ _] => f
  | _ => V3.zero

/-- One fee iteration determines the new balance from the stored one and the fee. -/
theorem al_feeAt_new {fee AF D0 D1 D0' D1' : Nat} {old new new' : V3} {i : Fin 3}
    {f st af af' : Nat}
    (h : feeAt fee AF D0 D1 old new i = some (f, st, af))
    (h' : feeAt fee AF D0' D1' old new' i = some (f, st, af')) : new.get i = new'.get i := by
  have key : ∀ {D0 D1 : Nat} {new : V3} {af : Nat},
      feeAt fee AF D0 D1 old new i = some (f, st, af) →
      ∃ adm, chkDiv (f * AF) feeDen = some adm ∧ st = new.get i - adm ∧ adm ≤ new.get i := by
    intro D0 D1 new af h
    have tail : ∀ diff, (do
        let m2 ← chkMul fee diff
        let f ← chkDiv m2 feeDen
        let m3 ← chkMul f AF
        let adm ← chkDiv m3 feeDen
        let st ← chkSub (new.get i) adm
        let af ← chkSub (new.get i) f
        some (f, st, af)) = some (f, st, af) →
        ∃ adm, chkDiv (f * AF) feeDen = some adm ∧ st = new.get i - adm ∧ adm ≤ new.get i := by
      intro diff h
      obtain ⟨m2, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨f0, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨m3, hm3, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨adm, hadm, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st0, hst0, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨af0, -, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      unfold chkMul at hm3
      split at hm3
      · obtain rfl := (Option.some.inj hm3).symm
        obtain ⟨rfl, hle⟩ := chkSub_some hst0
        exact ⟨adm, hadm, rfl, hle⟩
      · cases hm3
    unfold feeAt at h
    obtain ⟨m1, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ideal, -, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    · obtain ⟨diff, -, h⟩ := Option.bind_eq_some_iff.mp h
      exact tail diff h
    · obtain ⟨diff, -, h⟩ := Option.bind_eq_some_iff.mp h
      exact tail diff h
  obtain ⟨adm, hadm, hst, hle⟩ := key h
  obtain ⟨adm', hadm', hst', hle'⟩ := key h'
  obtain rfl : adm' = adm := Option.some.inj (hadm'.symm.trans hadm)
  omega

/-- The fee loop determines the new balances from the stored ones and the fees. -/
theorem al_feeLoop_new {fee AF D0 D1 D0' D1' : Nat} {old new new' fees stored after after' : V3}
    (h : feeLoop fee AF D0 D1 old new = some (fees, stored, after))
    (h' : feeLoop fee AF D0' D1' old new' = some (fees, stored, after')) : new = new' := by
  have dec : ∀ {D0 D1 : Nat} {new after : V3},
      feeLoop fee AF D0 D1 old new = some (fees, stored, after) →
      ∃ a0 a1 a2, feeAt fee AF D0 D1 old new 0 = some (fees.v0, stored.v0, a0) ∧
        feeAt fee AF D0 D1 old new 1 = some (fees.v1, stored.v1, a1) ∧
        feeAt fee AF D0 D1 old new 2 = some (fees.v2, stored.v2, a2) := by
    intro D0 D1 new after h
    unfold feeLoop at h
    obtain ⟨r0, hr0, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r1, hr1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r2, hr2, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨r0.2.2, r1.2.2, r2.2.2, hr0, hr1, hr2⟩
  obtain ⟨a0, a1, a2, h0, h1, h2⟩ := dec h
  obtain ⟨b0, b1, b2, g0, g1, g2⟩ := dec h'
  exact V3.ext_get fun k => by
    rcases k with ⟨_ | _ | _ | n, hk⟩
    · exact al_feeAt_new h0 g0
    · exact al_feeAt_new h1 g1
    · exact al_feeAt_new h2 g2
    · omega

/-- **The output is pinned by the stored balances and the fees** (see the module note). -/
theorem al_out_unique {s : State} {e e' : Env} {a : V3} {m : Nat} {o o' : Out}
    (h : addLiquidity s e a m = some o) (h' : addLiquidity s e' a m = some o')
    (ht : e'.time = e.time) (hc : e'.caller = e.caller) (hs : e'.supply = e.supply)
    (hbal : o'.state.balances = o.state.balances) (hfees : alFees o' = alFees o) : o' = o := by
  obtain ⟨-, fee, amp, T, new, D1, mint, T', hfee, hamp, hT, -, hD1, -, -, hT', hbr⟩ :=
    addLiquidity_inv h
  obtain ⟨-, fee', amp', T₂, new', D1', mint', T'', hfee', hamp', hT₂, -, hD1'', -, -, hT'', hbr'⟩ :=
    addLiquidity_inv h'
  obtain rfl : fee' = fee := Option.some.inj (hfee'.symm.trans hfee)
  obtain rfl : amp' = amp := Option.some.inj (hamp'.symm.trans (ht ▸ hamp))
  obtain rfl : T₂ = T := Option.some.inj (hT₂.symm.trans (hs ▸ hT))
  rcases hbr with ⟨rfl, -, rfl, rfl⟩ | ⟨hT0, D0, fees, stored, after, D2, x, y, hD0, -, hfl, hD2, hx,
    hy, hm, rfl⟩
  · rcases hbr' with ⟨-, -, rfl, rfl⟩ | ⟨hT0, -⟩
    · obtain rfl : new' = new := hbal
      obtain rfl : mint' = mint := Option.some.inj (hD1''.symm.trans hD1)
      obtain rfl : T'' = T' := Option.some.inj (hT''.symm.trans hT')
      rw [hc]
    · exact absurd rfl hT0
  · rcases hbr' with ⟨h0, -⟩ | ⟨-, D0', fees', stored', after', D2', x', y', hD0', -, hfl', hD2',
      hx', hy', hm', rfl⟩
    · exact absurd h0 hT0
    · obtain rfl : D0' = D0 := Option.some.inj (hD0'.symm.trans hD0)
      obtain rfl : stored' = stored := hbal
      obtain rfl : fees' = fees := hfees
      obtain rfl : new' = new := (al_feeLoop_new hfl hfl').symm
      obtain rfl : D1' = D1 := Option.some.inj (hD1''.symm.trans hD1)
      obtain rfl : after' = after := by
        have := hfl'.symm.trans hfl
        simp only [Option.some.injEq, Prod.mk.injEq] at this
        exact this.2.2
      obtain rfl : D2' = D2 := Option.some.inj (hD2'.symm.trans hD2)
      obtain rfl : x' = x := Option.some.inj (hx'.symm.trans hx)
      obtain rfl : y' = y := Option.some.inj (hy'.symm.trans hy)
      obtain rfl : mint' = mint := Option.some.inj (hm'.symm.trans hm)
      obtain rfl : T'' = T' := Option.some.inj (hT''.symm.trans hT')
      rw [hc]

end Blanc.Lift.Curve3Pool
