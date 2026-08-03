-- Ladder.lean : the contract-generic half of the solvency ladder.
--
-- `~/plans/solvent-split.md`, the axis-2 cut of `Solvent.lean`.  This module
-- sits *below* `Blanc.Solvent`: it holds the world-state and balance-sum
-- algebra that the ladder rests on, and the `ContractSpec` record that the
-- contract-generic band of the ladder is parameterized by.  `Solvent.lean`
-- imports it and is the WETH instance.
--
-- What the record is for.  The band of `Solvent.lean` from the
-- sub-execution-carryover tier upwards is contract-generic in substance but
-- WETH-monomorphic in statement: every theorem names `weth`, `Stor.Solvent`,
-- `SumNof`, `Precond`, `Postcond` or `State.Inv`.  `ContractSpec` is the
-- interface those statements actually consume — a program, an invariant, a
-- global balance side condition, and the handful of closure properties the
-- ladder's proofs use.  Two instances exist: `wethSpec` in `Blanc/Solvent.lean`,
-- the shipped contract, shown there to reproduce the existing `Precond` /
-- `Postcond` / `State.Inv` bundles exactly; and `fwethSpec` in
-- `Blanc/Flashmint.lean`, the ERC-3156 flash-mint contract of
-- `~/plans/flashmint-proposal.md`, a statement-level instance only.

import Blanc.CommonProofs

namespace Blanc

open Jaune

/-! ## Generic world-state and balance-sum algebra

Moved down from `Solvent.lean`, unchanged: none of it mentions WETH, and both
the ladder above and the WETH instance below consume it. -/

-- balance-sum & transfer infrastructure (ported from Common.lean) --

def SumNof (f : Adr → B256) : Prop := sum f < 2 ^ 256

def Decrease (k : Adr) (v : B256) (f g : Adr → B256) : Prop :=
  Frel k (λ x y => x - v = y) f g

def Increase (k : Adr) (v : B256) (f g : Adr → B256) : Prop :=
  Frel k (λ x y => x + v = y) f g

def Transfer
    (b : Adr → B256)
    (kd : Adr) (v : B256) (ki : Adr)
    (d : Adr → B256) : Prop :=
    v ≤ b kd ∧
  ∃ c : Adr → B256,
    Decrease kd v b c ∧
    Increase ki v c d

lemma frel_of_frel {ξ υ} {x : ξ} {r s : υ → υ → Prop} {f g : ξ → υ}
    (h : r (f x) (g x) → s (f x) (g x)) (h' : Frel x r f g) : Frel x s f g := by
  intro x'; constructor <;> intro hx
  · cases hx; exact h <| (h' x).left rfl
  · exact (h' x').right hx

lemma le_sumBelow (f : Adr → B256) {k : Adr} {n} (h : k.toNat < n) :
    (f k).toNat ≤ sumBelow f n := by
  induction n with
  | zero => cases Nat.not_lt_zero _ h
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hk | hk
    · apply le_trans (ih hk); rw [sumBelow_succ]; apply Nat.le_add_right
    · rw [sumBelow_succ, ← hk, toAdr_toNat]; apply Nat.le_add_left

def EqBelow (n : Nat) (f g : Adr → B256) : Prop :=
  ∀ k, k.toNat < n → f k = g k

lemma sumBelow_eq_sumBelow_of_eq_below {m n} {f g : Adr → B256}
    (hm : m < 2 ^ 160) (h_le : m ≤ n) (h_eqb : EqBelow n f g) :
    sumBelow f m = sumBelow g m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [sumBelow_succ, sumBelow_succ]
    have hm' : m < 2 ^ 160 := Nat.lt_of_succ_lt hm
    rw [ih hm' (Nat.le_of_succ_le h_le), h_eqb m.toAdr]
    rw [Nat.toNat_toAdr, Nat.lo_eq_of_lt hm']
    apply Nat.lt_of_succ_le h_le

lemma eq_below_of_frel {k} {r} {f g : Adr → B256} (h : Frel k r f g) :
    EqBelow k.toNat f g := by
  intro x hx; apply (h x).2
  intro h; rw [h] at hx; cases lt_irrefl _ hx

lemma sumBelow_sub_assoc {k : Adr} {v : B256} {n} {f g : Adr → B256}
    (dec : Decrease k v f g) (k_lt_n : k.toNat < n)
    (hv : v ≤ f k) (hn : n ≤ 2 ^ 160) :
    sumBelow f n - v.toNat = sumBelow g n := by
  induction n with
  | zero => cases Nat.not_lt_zero _ k_lt_n
  | succ n ih =>
    rw [sumBelow_succ, sumBelow_succ]
    rw [Nat.lt_succ_iff_lt_or_eq] at k_lt_n
    rcases k_lt_n with hk | hk
    · have h_ne : k ≠ n.toAdr := by
        intro hc;
        rw [hc, Nat.toNat_toAdr, Nat.lo_eq_of_lt] at hk
        apply lt_irrefl _ hk; apply Nat.lt_of_succ_le hn
      rw [← ih hk (le_trans (Nat.le_succ _) hn), (dec n.toAdr).2 h_ne]
      rw [Nat.sub_add_comm]
      apply le_trans _ <| le_sumBelow f hk
      apply B256.toNat_le_toNat hv
    · have rw1 : sumBelow g n = sumBelow f n := by
        have hn' : n < 2 ^ 160 := Nat.lt_of_succ_le hn
        have hkn : n ≤ k.toNat := by rw [hk]
        have h_eq := eq_below_of_frel dec
        rw [← sumBelow_eq_sumBelow_of_eq_below hn' hkn h_eq]
      rw [rw1]; clear rw1
      have rw2 : n.toAdr = k := by rw [← hk, toAdr_toNat]
      rw [rw2]; clear rw2
      rw [← (dec k).1 rfl, B256.toNat_sub_eq_of_le _ _ hv]
      rw [Nat.add_sub_assoc (B256.toNat_le_toNat hv)]

lemma sum_sub_assoc {k v} {f g : Adr → B256}
    (dec : Decrease k v f g) (v_le : v ≤ f k) : sum f - v.toNat = sum g :=
  sumBelow_sub_assoc dec (Adr.toNat_lt_size k) v_le (Nat.le_refl _)

lemma le_sum {f : Adr → B256} {k} : (f k).toNat ≤ sum f :=
  le_sumBelow f (Adr.toNat_lt_size k)

lemma sumBelow_add_assoc {k v} {n} {f g : Adr → B256} (inc : Increase k v f g)
    (k_lt : k.toNat < n) (nof : B256.Nof (f k) v) (n_lt : n ≤ 2 ^ 160) :
    sumBelow f n + v.toNat = sumBelow g n := by
  induction n with
  | zero => cases Nat.not_lt_zero _ k_lt
  | succ n ih =>
    rw [sumBelow_succ, sumBelow_succ]
    rw [Nat.lt_succ_iff_lt_or_eq] at k_lt
    rcases k_lt with hk | hk
    · have h_ne : k ≠ n.toAdr := by
        intro hc; rw [hc, Nat.toNat_toAdr, Nat.lo_eq_of_lt] at hk
        apply lt_irrefl _ hk; apply Nat.lt_of_succ_le n_lt
      rw [← ih hk (le_trans (Nat.le_succ _) n_lt), (inc n.toAdr).2 h_ne]
      omega
    · have rw1 : sumBelow g n = sumBelow f n := by
        have hn' : n < 2 ^ 160 := Nat.lt_of_succ_le n_lt
        have hkn : n ≤ k.toNat := by rw [hk]
        have h_eq := eq_below_of_frel inc
        rw [← sumBelow_eq_sumBelow_of_eq_below hn' hkn h_eq]
      rw [rw1]; clear rw1
      have rw2 : n.toAdr = k := by rw [← hk, toAdr_toNat]
      rw [rw2]; clear rw2
      rw [← (inc k).1 rfl, B256.toNat_add_eq_of_nof _ _ nof, Nat.add_assoc]

lemma sum_add_assoc {k v} {f g : Adr → B256}
    (inc : Increase k v f g) (nof : B256.Nof (f k) v) :
    sum f + v.toNat = sum g :=
  sumBelow_add_assoc inc
    (Adr.toNat_lt_size _)
    nof
    (Nat.succ_le_of_lt <| Adr.toNat_lt_size _)

lemma add_le_sumBelow (f : Adr → B256) {x y : Adr} {n}
    (x_lt : x.toNat < y.toNat) (y_lt : y.toNat < n) :
    (f x).toNat + (f y).toNat ≤ sumBelow f n := by
  induction n with
  | zero => cases Nat.not_lt_zero _ y_lt
  | succ n ih =>
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ y_lt) with y_lt' | y_eq
    · apply le_trans (ih y_lt'); rw [sumBelow_succ]; apply Nat.le_add_right
    · rw [sumBelow_succ, ← y_eq, toAdr_toNat]
      apply Nat.add_le_add_right
      apply le_sumBelow _ x_lt

lemma Adr.toNat_inj {x y : Adr} (h : x.toNat = y.toNat) : x = y := by
  rw [← toAdr_toNat x, ← toAdr_toNat y, h]

lemma add_le_sum_of_ne (f : Adr → B256) {x y : Adr} (ne : x ≠ y) :
    (f x).toNat + (f y).toNat ≤ sum f := by
  rcases Nat.lt_trichotomy x.toNat y.toNat with x_lt_y | x_eq_y | y_lt_x
  · apply add_le_sumBelow f x_lt_y (Adr.toNat_lt_size y)
  · cases ne <| Adr.toNat_inj x_eq_y
  · rw [Nat.add_comm]
    apply add_le_sumBelow f y_lt_x (Adr.toNat_lt_size x)

lemma transfer_preserves_sum {kd ki v} {b d : Adr → B256}
    (hb : SumNof b) (h : Transfer b kd v ki d) : sum b = sum d := by
  rcases h with ⟨h, c, hd, hi⟩
  apply @Eq.trans _ _ (sum c + v.toNat)
  · rw [← sum_sub_assoc hd h, Nat.sub_add_cancel]
    apply Nat.le_trans (B256.toNat_le_toNat h) le_sum
  · apply @sum_add_assoc ki
    apply frel_of_frel _ hi; intro h_eq; exact h_eq
    by_cases hk : ki = kd
    · rw [hk, ← (hd kd).left rfl]; simp only [B256.Nof]
      rw [B256.toNat_sub_eq_of_le _ _ h, Nat.sub_add_cancel (B256.toNat_le_toNat h)]
      apply B256.toNat_lt
    · rw [← (hd ki).right (Ne.symm hk)]
      apply lt_of_le_of_lt (Nat.le_trans _ <| add_le_sum_of_ne b hk) hb
      apply Nat.add_le_add_left <| B256.toNat_le_toNat h

lemma B256.le_add_right {xs ys : B256} (h : B256.Nof xs ys) : xs ≤ xs + ys := by
  rw [B256.le_iff_toNat_le_toNat, B256.toNat_add_eq_of_nof _ _ h]; simp

-- helper lemmas for reasoning about the balance transfer performed by `call`



lemma State.setBal_get_self {st : Jaune.State} {adr : Adr} {v : B256} :
    (st.setBal adr v).get adr = (st.get adr).withBal v := State.get_set_self _ _ _

lemma State.setBal_get_ne {st : Jaune.State} {adr a : Adr} {v : B256} (h : adr ≠ a) :
    (st.setBal adr v).get a = st.get a := State.get_set_ne _ h _

lemma State.setBal_get_stor {st : Jaune.State} {b a : Adr} {v : B256} :
    ((st.setBal b v).get a).stor = (st.get a).stor := by
  by_cases h : b = a
  · subst h; rw [State.setBal_get_self]; rfl
  · rw [State.setBal_get_ne h]

lemma State.setBal_get_code {st : Jaune.State} {b a : Adr} {v : B256} :
    ((st.setBal b v).get a).code = (st.get a).code := by
  by_cases h : b = a
  · subst h; rw [State.setBal_get_self]; rfl
  · rw [State.setBal_get_ne h]

lemma State.of_subBal {st st' : Jaune.State} {ct : Adr} {wad : B256}
    (h : st.subBal ct wad = some st') :
    wad ≤ st.bal ct ∧ st' = st.setBal ct (st.bal ct - wad) := by
  unfold State.subBal at h
  split_ifs at h with h_lt
  cases h
  exact ⟨B256.not_lt.mp h_lt, rfl⟩

lemma of_state_transfer_fields {st st' : Jaune.State} {ct callee : Adr} {wad : B256}
    (h_sub : st.subBal ct wad = some st') :
    (∀ a, ((st'.addBal callee wad).get a).stor = (st.get a).stor) ∧
    (∀ a, ((st'.addBal callee wad).get a).code = (st.get a).code) ∧
    wad ≤ st.bal ct ∧
    (callee = ct → (st'.addBal callee wad).bal ct = st.bal ct) ∧
    (callee ≠ ct → (st'.addBal callee wad).bal ct = st.bal ct - wad) := by
  rcases State.of_subBal h_sub with ⟨h_le, h_st'⟩
  subst h_st'
  unfold State.addBal
  refine' ⟨_, _, h_le, _, _⟩
  · intro a; rw [State.setBal_get_stor, State.setBal_get_stor]
  · intro a; rw [State.setBal_get_code, State.setBal_get_code]
  · intro h_eq; subst h_eq
    show ((Jaune.State.setBal _ callee _).get callee).bal = _
    rw [State.setBal_get_self]
    show (st.setBal callee (st.bal callee - wad)).bal callee + wad = _
    show ((st.setBal callee (st.bal callee - wad)).get callee).bal + wad = _
    rw [State.setBal_get_self]
    show st.bal callee - wad + wad = _
    rw [B256.sub_add_cancel]
  · intro h_ne
    show ((Jaune.State.setBal _ callee _).get ct).bal = _
    rw [State.setBal_get_ne h_ne]
    show ((st.setBal ct (st.bal ct - wad)).get ct).bal = _
    rw [State.setBal_get_self]; rfl

-- The `nof`-requiring conjunct of `of_state_transfer`, on its own.
lemma of_state_transfer_sum {st st' : Jaune.State} {ct callee : Adr} {wad : B256}
    (h_sub : st.subBal ct wad = some st')
    (h_nof : sum st.bal < 2 ^ 256) :
    sum (st'.addBal callee wad).bal = sum st.bal := by
  rcases State.of_subBal h_sub with ⟨h_le, h_st'⟩
  subst h_st'
  unfold State.addBal
  -- the total sum of balances is preserved by the transfer
  have h_dec : Decrease ct wad st.bal (st.setBal ct (st.bal ct - wad)).bal := by
    intro a; constructor
    · intro h_eq; subst h_eq
      show _ = ((st.setBal ct (st.bal ct - wad)).get ct).bal
      rw [State.setBal_get_self]; rfl
    · intro h_ne
      show st.bal a = ((st.setBal ct (st.bal ct - wad)).get a).bal
      rw [State.setBal_get_ne h_ne]; rfl
  have h_sum_dec : sum st.bal - wad.toNat = sum (st.setBal ct (st.bal ct - wad)).bal :=
    sum_sub_assoc h_dec h_le
  have h_wad_le : wad.toNat ≤ sum st.bal :=
    le_trans (B256.toNat_le_toNat h_le) le_sum
  set mid := st.setBal ct (st.bal ct - wad) with h_mid
  have h_inc : Increase callee wad mid.bal (mid.setBal callee (mid.bal callee + wad)).bal := by
    intro a; constructor
    · intro h_eq; subst h_eq
      show _ = ((mid.setBal callee (mid.bal callee + wad)).get callee).bal
      rw [State.setBal_get_self]; rfl
    · intro h_ne
      show mid.bal a = ((mid.setBal callee (mid.bal callee + wad)).get a).bal
      rw [State.setBal_get_ne h_ne]; rfl
  have h_nof' : B256.Nof (mid.bal callee) wad := by
    unfold B256.Nof
    have h1 : (mid.bal callee).toNat ≤ sum mid.bal := le_sum
    omega
  have h_sum_inc : sum mid.bal + wad.toNat = sum (mid.setBal callee (mid.bal callee + wad)).bal :=
    sum_add_assoc h_inc h_nof'
  omega

-- The original bundle, unchanged in statement: the `nof`-free fields of
-- `of_state_transfer_fields` together with the balance-sum conjunct.
lemma of_state_transfer {st st' : Jaune.State} {ct callee : Adr} {wad : B256}
    (h_sub : st.subBal ct wad = some st')
    (h_nof : sum st.bal < 2 ^ 256) :
    (∀ a, ((st'.addBal callee wad).get a).stor = (st.get a).stor) ∧
    (∀ a, ((st'.addBal callee wad).get a).code = (st.get a).code) ∧
    sum (st'.addBal callee wad).bal = sum st.bal ∧
    wad ≤ st.bal ct ∧
    (callee = ct → (st'.addBal callee wad).bal ct = st.bal ct) ∧
    (callee ≠ ct → (st'.addBal callee wad).bal ct = st.bal ct - wad) := by
  obtain ⟨h_stor, h_code, h_le, h_self, h_ne⟩ := of_state_transfer_fields (callee := callee) h_sub
  exact ⟨h_stor, h_code, of_state_transfer_sum h_sub h_nof, h_le, h_self, h_ne⟩

lemma State.setCode_get_bal {st : Jaune.State} {adr a : Adr} {c : ByteArray} :
    ((st.setCode adr c).get a).bal = (st.get a).bal := by
  unfold State.setCode
  by_cases h : adr = a
  · subst h; rw [State.get_set_self]
  · rw [State.get_set_ne _ h]

lemma State.setCode_get_stor {st : Jaune.State} {adr a : Adr} {c : ByteArray} :
    ((st.setCode adr c).get a).stor = (st.get a).stor := by
  unfold State.setCode
  by_cases h : adr = a
  · subst h; rw [State.get_set_self]
  · rw [State.get_set_ne _ h]

lemma State.setCode_get_code_ne {st : Jaune.State} {adr a : Adr} {c : ByteArray}
    (h : adr ≠ a) : ((st.setCode adr c).get a).code = (st.get a).code := by
  unfold State.setCode
  rw [State.get_set_ne _ h]

lemma State.setStor_get_bal {st : Jaune.State} {adr a : Adr} {s : Stor} :
    ((st.setStor adr s).get a).bal = (st.get a).bal := by
  unfold State.setStor
  by_cases h : adr = a
  · subst h; rw [State.get_set_self]
  · rw [State.get_set_ne _ h]

lemma State.setStor_get_code {st : Jaune.State} {adr a : Adr} {s : Stor} :
    ((st.setStor adr s).get a).code = (st.get a).code := by
  unfold State.setStor
  by_cases h : adr = a
  · subst h; rw [State.get_set_self]
  · rw [State.get_set_ne _ h]

lemma State.setStor_get_stor_ne {st : Jaune.State} {adr a : Adr} {s : Stor}
    (h : adr ≠ a) : ((st.setStor adr s).get a).stor = (st.get a).stor := by
  unfold State.setStor
  rw [State.get_set_ne _ h]

-- balance of an uninvolved account is unchanged by a transfer
lemma of_transfer_bal_other {st st_mid : Jaune.State} {caller target a : Adr} {value : B256}
    (h_sub : st.subBal caller value = some st_mid)
    (h_ne_c : caller ≠ a) (h_ne_t : target ≠ a) :
    (st_mid.addBal target value).bal a = st.bal a := by
  rcases State.of_subBal h_sub with ⟨_, h_mid⟩
  subst h_mid
  show ((Jaune.State.setBal _ target _).get a).bal = _
  rw [State.setBal_get_ne h_ne_t]
  show ((st.setBal caller _).get a).bal = _
  rw [State.setBal_get_ne h_ne_c]
  rfl

-- balance of the recipient is increased by a transfer from a distinct sender
lemma of_transfer_bal_target {st st_mid : Jaune.State} {caller target : Adr} {value : B256}
    (h_sub : st.subBal caller value = some st_mid)
    (h_ne : caller ≠ target)
    (h_nof : sum st.bal < 2 ^ 256) :
    ((st_mid.addBal target value).bal target).toNat
      = (st.bal target).toNat + value.toNat := by
  rcases State.of_subBal h_sub with ⟨h_le, h_mid⟩
  subst h_mid
  have h_bal_t : (st.setBal caller (st.bal caller - value)).bal target = st.bal target := by
    show ((st.setBal caller _).get target).bal = _
    rw [State.setBal_get_ne h_ne]
    rfl
  have h_eq : ((st.setBal caller (st.bal caller - value)).addBal target value).bal target
      = st.bal target + value := by
    show ((Jaune.State.setBal _ target _).get target).bal = _
    rw [State.setBal_get_self]
    show (st.setBal caller (st.bal caller - value)).bal target + value = _
    rw [h_bal_t]
  rw [h_eq]
  apply B256.toNat_add_eq_of_nof
  unfold B256.Nof
  have h1 := B256.toNat_le_toNat h_le
  have h2 := add_le_sum_of_ne st.bal (Ne.symm h_ne)
  omega

lemma State.incrNonce_get_bal {st : Jaune.State} {adr a : Adr} :
    ((st.incrNonce adr).get a).bal = (st.get a).bal := by
  simp only [State.incrNonce]
  by_cases h : adr = a
  · subst h; rw [State.get_set_self]
  · rw [State.get_set_ne _ h]

lemma State.incrNonce_get_stor {st : Jaune.State} {adr a : Adr} :
    ((st.incrNonce adr).get a).stor = (st.get a).stor := by
  simp only [State.incrNonce]
  by_cases h : adr = a
  · subst h; rw [State.get_set_self]
  · rw [State.get_set_ne _ h]

lemma State.incrNonce_get_code {st : Jaune.State} {adr a : Adr} :
    ((st.incrNonce adr).get a).code = (st.get a).code := by
  simp only [State.incrNonce]
  by_cases h : adr = a
  · subst h; rw [State.get_set_self]
  · rw [State.get_set_ne _ h]

-- ## Sum after addBal

lemma sum_addBal_eq (st : Jaune.State) (a : Adr) (v : B256)
    (h : sum st.bal + v.toNat < 2 ^ 256) :
    sum (st.addBal a v).bal = sum st.bal + v.toNat := by
  have hnof : B256.Nof (st.bal a) v := by
    unfold B256.Nof; have := @le_sum st.bal a; omega
  have h1 := State.balSum_setBal st a (st.bal a + v)
  rw [B256.toNat_add_eq_of_nof _ _ hnof] at h1
  have h2 : State.balSum (st.setBal a (st.bal a + v)) =
      sum (st.addBal a v).bal := rfl
  have h3 : State.balSum st = sum st.bal := rfl
  omega

/-! ## The record -/

/-- The interface the contract-generic band of the solvency ladder consumes.

`Inv` is the contract-level invariant, applied to the contract's storage, the
callvalue in flight into the current frame, and the contract's ETH balance.
`Side` is the global side condition on the world's balance map — WETH's
`SumNof`; a balance-independent contract declines it with `fun _ => True`.

The remaining fields are the *slots*: the closure properties the ladder's
proofs use.  They come in two tiers.  The first three are the invariant's own
algebra and mention nothing outside it.  The last four are the
balance-movement tier (`subBal`/`addBal` at the world-state level, which is
what `Xinst`'s value transfers, `processMessageCall` and `processTransaction`
all reduce to); they carry `Side` in hypothesis position, which is exactly how
a contract that declines the `nof` condition also declines the obligation to
reason about wrap-around. -/
structure ContractSpec where
  /-- The contract's source program.  The ladder consumes it only through
  `Prog.compile` — code preservation across sub-executions, code
  non-emptiness (`Prog.compile_ne_nil`) and non-delegation
  (`not_delegation_of_compile`), all three of which are already generic in
  the program and therefore need no slot. -/
  prog : Prog
  /-- storage at the contract address → callvalue in flight → the contract's
  ETH balance → Prop. -/
  Inv : Stor → B256 → B256 → Prop
  /-- The global side condition on the world's balance map. -/
  Side : (Adr → B256) → Prop
  /-- Once a frame has terminated there is no callvalue in flight.
  (WETH: `solvent_zero_of_solvent`.) -/
  inv_forget : ∀ {s : Stor} {v b : B256}, Inv s v b → Inv s 0 b
  /-- The invariant survives a rise in the contract's own balance. -/
  inv_mono : ∀ {s : Stor} {v b b' : B256}, Inv s v b → b.toNat ≤ b'.toNat → Inv s v b'
  /-- A callvalue that has already been credited to the contract's balance may
  be taken into flight. -/
  inv_recv : ∀ {s : Stor} {v b b' : B256}, Inv s 0 b → b'.toNat = b.toNat + v.toNat → Inv s v b'
  /-- The side condition survives any change that does not raise the total. -/
  side_le : ∀ {f g : Adr → B256}, Side f → sum g ≤ sum f → Side g
  /-- The side condition survives a value transfer. -/
  side_transfer : ∀ {st st' : Jaune.State} {caller callee : Adr} {wad : B256},
    st.subBal caller wad = some st' → Side st.bal → Side (st'.addBal callee wad).bal
  /-- The side condition survives a credit that stays under the bound.  The
  bound is supplied by the caller's wei-conservation argument, exactly as in
  `State.Inv.addBal`. -/
  side_addBal : ∀ {w : Jaune.State} {a : Adr} {val : B256},
    sum w.bal + val.toNat < 2 ^ 256 → Side w.bal → Side (w.addBal a val).bal
  /-- The invariant survives a value transfer that does not debit the
  contract.  The callee may be the contract itself, in which case its balance
  rises; `Side` is what rules out a wrap. -/
  inv_transfer : ∀ {st st' : Jaune.State} {caller callee ca : Adr} {wad v : B256},
    st.subBal caller wad = some st' → caller ≠ ca → Side st.bal →
    Inv (st.getStor ca) v (st.bal ca) →
    Inv ((st'.addBal callee wad).getStor ca) v ((st'.addBal callee wad).bal ca)
  /-- Entering a frame *at* the contract with callvalue `wad`: the transfer has
  already credited `wad` to the contract's balance, and the child frame carries
  it in flight. -/
  inv_recv_transfer : ∀ {st st' : Jaune.State} {caller ca : Adr} {wad : B256},
    st.subBal caller wad = some st' → caller ≠ ca → Side st.bal →
    Inv (st.getStor ca) 0 (st.bal ca) →
    Inv ((st'.addBal ca wad).getStor ca) wad ((st'.addBal ca wad).bal ca)
  /-- The invariant survives a bare credit under the wei-conservation bound
  (`State.Inv.addBal`: gas refunds, the coinbase fee, withdrawals). -/
  inv_addBal : ∀ {w : Jaune.State} {ca a : Adr} {val v : B256},
    sum w.bal + val.toNat < 2 ^ 256 → Side w.bal →
    Inv (w.getStor ca) v (w.bal ca) →
    Inv ((w.addBal a val).getStor ca) v ((w.addBal a val).bal ca)

namespace ContractSpec

variable (c : ContractSpec)

/-- The frame-entry form of the invariant: the callvalue is in flight exactly
when the current frame is executing the contract itself. -/
def PreInv (devm : Devm) (ca : Adr) (sevm : Sevm) : Prop :=
  (sevm.currentTarget = ca → c.Inv (Devm.getStor devm ca) sevm.value (devm.getBal ca)) ∧
  (sevm.currentTarget ≠ ca → c.Inv (Devm.getStor devm ca) 0 (devm.getBal ca))

/-- The frame-exit form of the invariant. -/
def PostInv (devm : Devm) (ca : Adr) : Prop :=
  c.Inv (Devm.getStor devm ca) 0 (devm.getBal ca)

/-- The generic counterpart of `Blanc.Precond`. -/
structure Pre (ca : Adr) (sevm : Sevm) (devm : Devm) : Prop where
  (code : some (devm.getCode ca).toList = Prog.compile c.prog)
  (side : c.Side devm.getBal)
  (inv : c.PreInv devm ca sevm)

/-- The generic counterpart of `Blanc.Postcond`. -/
structure Post (ca : Adr) (_sevm : Sevm) (devm : Devm) : Prop where
  (side : c.Side devm.getBal)
  (inv : c.PostInv devm ca)

/-- The generic counterpart of `Blanc.State.Inv`. -/
structure StateInv (ca : Adr) (w : Jaune.State) : Prop where
  (code : some (w.getCode ca).toList = Prog.compile c.prog)
  (side : c.Side w.bal)
  (inv : c.Inv (w.getStor ca) 0 (w.bal ca))

end ContractSpec

end Blanc
