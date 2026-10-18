import Blanc.Lift.Curve3Pool.Walk.AlLiveUnique
import Blanc.Lift.Curve3Pool.Walk.AlLiveWords

/-!
# `add_liquidity`: the forward run's end against a raw effect

`al_event_fees`: an `AddLiquidity` log's data words 3–5 are its fees. `al_bal_link`: a storage
effect's new balances read the post-storage's balance slots. `al_end_bal`: the forward run's final
storage at those slots.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

theorem al_wordsV3_length (v : V3) : (wordsV3 v).length = 96 := by
  simp only [wordsV3, word, List.length_append, B256.length_toBytes]

/-- **An `AddLiquidity` log's data words 3–5 are its fees.** -/
theorem al_event_fees {pool pool' : Adr} {p inv sup : Nat} {am fees : V3} {ts : List B256}
    {data : Bytes}
    (h : eventLog pool (.addLiquidity p am fees inv sup) = ⟨pool', ts, data⟩) :
    Bytes.toB256 (data.sliceD 0x60 32 0) = Nat.toB256 fees.v0 ∧
      Bytes.toB256 (data.sliceD 0x80 32 0) = Nat.toB256 fees.v1 ∧
      Bytes.toB256 (data.sliceD 0xa0 32 0) = Nat.toB256 fees.v2 := by
  unfold eventLog at h
  injection h with _ _ hd
  subst hd
  have hR := List.sliceD_zero_of_length (xs := wordsV3 am ++ wordsV3 fees ++ word inv ++ word sup)
    rfl
  have hR' : Region (wordsV3 am ++ wordsV3 fees ++ word inv ++ word sup) 0
      (wordsV3 am ++ wordsV3 fees ++ word inv ++ word sup) := hR
  have hF := hR'.left.left.right
  rw [al_wordsV3_length, Nat.zero_add] at hF
  unfold wordsV3 at hF
  have h0 := hF.left.left
  have h1 := hF.left.right
  have h2 := hF.right
  refine ⟨?_, ?_, ?_⟩
  · exact (h0.read (B256.length_toBytes _)).trans (B256.toB256_toBytes _)
  · exact (h1.read (B256.length_toBytes _)).trans (B256.toB256_toBytes _)
  · exact (h2.read (B256.length_toBytes _)).trans (B256.toB256_toBytes _)

/-- **A storage effect's new balances read the post-storage's balance slots.** -/
theorem al_bal_link {a : V3} {m : Nat} {pre post : Stor} {s' : State}
    (hst : StorEffect (.addLiquidity a m) pre post s') :
    s'.balances = ⟨(post.get (balanceSlot 0)).toNat, (post.get (balanceSlot 1)).toNat,
      (post.get (balanceSlot 2)).toNat⟩ := by
  have r : ∀ k : Fin 3, (post.get (balanceSlot k)).toNat = s'.balances.get k := fun k =>
    hst.written (.bal k) (by
      rcases k with ⟨_ | _ | _ | n, hk⟩
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · omega)
  exact V3.ext_get fun k => by
    rw [← r k]
    rcases k with ⟨_ | _ | _ | n, hk⟩
    · rfl
    · rfl
    · rfl
    · omega

/-- **The forward run's final storage at the balance slots.** -/
theorem al_end_bal (σ : Stor) (s0 s1 s2 : B256) :
    (alUnlock (alStor3 (alLocked1 σ) s0 s1 s2)).get (balanceSlot 0) = s0 ∧
    (alUnlock (alStor3 (alLocked1 σ) s0 s1 s2)).get (balanceSlot 1) = s1 ∧
    (alUnlock (alStor3 (alLocked1 σ) s0 s1 s2)).get (balanceSlot 2) = s2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Stor.get_set_ne _ (by decide), Stor.get_set_ne _ (by decide),
      Stor.get_set_ne _ (by decide), show balanceSlot 0 = balancesBase + Nat.toB256 0 from rfl,
      Stor.get_set_self]
  · rw [Stor.get_set_ne _ (by decide), Stor.get_set_ne _ (by decide),
      show balanceSlot 1 = balancesBase + Nat.toB256 1 from rfl, Stor.get_set_self]
  · rw [Stor.get_set_ne _ (by decide), show balanceSlot 2 = balancesBase + Nat.toB256 2 from rfl,
      Stor.get_set_self]

/-- A fee iteration's fee is a word. -/
theorem al_feeAt_lt {fee AF D0 D1 : Nat} {old new : V3} {i : Fin 3} {f st af : Nat}
    (h : feeAt fee AF D0 D1 old new i = some (f, st, af)) : f < 2 ^ 256 := by
  have tail : ∀ diff, (do
      let m2 ← chkMul fee diff
      let f ← chkDiv m2 feeDen
      let m3 ← chkMul f AF
      let adm ← chkDiv m3 feeDen
      let st ← chkSub (new.get i) adm
      let af ← chkSub (new.get i) f
      some (f, st, af)) = some (f, st, af) → f < 2 ^ 256 := by
    intro diff h
    obtain ⟨m2, hm2, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨f0, hf0, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨m3, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨adm, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨st0, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨af0, -, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    unfold chkMul at hm2
    split at hm2
    · rename_i hlt
      obtain rfl := (Option.some.inj hm2).symm
      unfold chkDiv at hf0
      split at hf0
      · cases hf0
      · obtain rfl := (Option.some.inj hf0).symm
        have := Nat.div_le_self (fee * diff) feeDen
        unfold wordSize at hlt
        omega
    · cases hm2
  unfold feeAt at h
  obtain ⟨m1, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ideal, -, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · obtain ⟨diff, -, h⟩ := Option.bind_eq_some_iff.mp h
    exact tail diff h
  · obtain ⟨diff, -, h⟩ := Option.bind_eq_some_iff.mp h
    exact tail diff h

/-- The fee loop's fees are words. -/
theorem al_feeLoop_lt {fee AF D0 D1 : Nat} {old new fees stored after : V3}
    (h : feeLoop fee AF D0 D1 old new = some (fees, stored, after)) :
    fees.v0 < 2 ^ 256 ∧ fees.v1 < 2 ^ 256 ∧ fees.v2 < 2 ^ 256 := by
  unfold feeLoop at h
  obtain ⟨r0, hr0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r1, hr1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r2, hr2, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -, -⟩ := h
  exact ⟨al_feeAt_lt hr0, al_feeAt_lt hr1, al_feeAt_lt hr2⟩

end Blanc.Lift.Curve3Pool
