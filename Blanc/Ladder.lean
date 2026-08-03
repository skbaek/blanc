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

/-! ## Generic frame-level infrastructure

WETH-free, moved down from `Solvent.lean` unchanged (`code_eq_of_exec` is
generalized from `weth` to an arbitrary program). -/

lemma Jinst.preserves_state
    {pc sevm devm j pc' devm'}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j (.ok ⟨pc', devm'⟩)) :
    devm'.state = devm.state := by
  cases h1 : devm.stack <;> simp only [Devm.stack] at h1
  · cases j
    · simp only [Jinst.Run, Jinst.run, Jinst.runCore, chargeGas_def, Devm.pop_def,
        Devm.setMach, Devm.stack, Devm.gasLeft, Except.assert, safeSub, bind, Except.bind] at run
      rw [h1] at run
      dsimp at run
      contradiction
    · simp only [Jinst.Run, Jinst.run, Jinst.runCore, chargeGas_def, Devm.pop_def,
        Devm.setMach, Devm.stack, Devm.gasLeft, Except.assert, safeSub, bind, Except.bind] at run
      rw [h1] at run
      dsimp at run
      contradiction
    · by_cases h_gas : gJumpdest ≤ devm.gasLeft
      · simp only [Jinst.Run, Jinst.run, Jinst.runCore, chargeGas_def, Devm.setMach,
          bind, Except.bind, safeSub] at run
        rw [h1] at run
        simp only [h_gas, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
        cases run
        subst_vars
        rfl
      · simp only [Jinst.Run, Jinst.run, Jinst.runCore, chargeGas_def, Devm.setMach,
          bind, Except.bind, safeSub] at run
        rw [h1] at run
        have h_gas_not : ¬(gJumpdest ≤ devm.gasLeft) := by omega
        simp only [h_gas_not] at run
        try contradiction
  · rename_i x xs
    cases h2 : xs
    · cases j
      · simp only [Jinst.Run, Jinst.run, Jinst.runCore, chargeGas_def, Devm.pop_def,
          Devm.setMach, Devm.stack, Devm.gasLeft, bind, Except.bind, safeSub] at run
        rw [h1] at run
        dsimp at run
        by_cases h_gas : gMid ≤ devm.gasLeft <;> simp only [Devm.gasLeft] at h_gas
        · simp only [h_gas, if_pos] at run
          by_cases h_jump : jumpable sevm.code x.toNat = true
          · simp only [h_jump] at run
            cases run
            subst_vars
            rfl
          · simp only [h_jump] at run
            contradiction
        · simp only [h_gas] at run
          contradiction
      · simp only [Jinst.Run, Jinst.run, Jinst.runCore, chargeGas_def, Devm.pop_def,
          Devm.setMach, Devm.stack, Devm.gasLeft, bind, Except.bind, safeSub] at run
        rw [h1] at run
        rw [h2] at run
        dsimp at run
        contradiction
      · simp only [Jinst.Run, Jinst.run, Jinst.runCore, chargeGas_def, Devm.setMach,
          bind, Except.bind, safeSub] at run
        rw [h1] at run
        by_cases h_gas : gJumpdest ≤ devm.gasLeft
        · simp only [h_gas, if_pos] at run
          cases run
          subst_vars
          rfl
        · have h_gas_not : ¬(gJumpdest ≤ devm.gasLeft) := by omega
          simp only [h_gas_not] at run
          contradiction
    · rename_i x2 xs2
      cases j
      · simp only [Jinst.Run, Jinst.run, Jinst.runCore, chargeGas_def, Devm.pop_def,
          Devm.setMach, Devm.stack, Devm.gasLeft, bind, Except.bind, safeSub] at run
        rw [h1] at run
        dsimp at run
        by_cases h_gas : gMid ≤ devm.gasLeft <;> simp only [Devm.gasLeft] at h_gas
        · simp only [h_gas, if_pos] at run
          by_cases h_jump : jumpable sevm.code x.toNat = true
          · simp only [h_jump] at run
            cases run
            subst_vars
            rfl
          · simp only [h_jump] at run
            contradiction
        · simp only [h_gas] at run
          contradiction
      · simp only [Jinst.Run, Jinst.run, Jinst.runCore, chargeGas_def, Devm.pop_def,
          Devm.setMach, Devm.stack, Devm.gasLeft, bind, Except.bind, safeSub] at run
        rw [h1] at run
        rw [h2] at run
        dsimp at run
        by_cases h_gas : gHigh ≤ devm.gasLeft <;> simp only [Devm.gasLeft] at h_gas
        · simp only [h_gas, if_pos] at run
          by_cases h_cond : x2 = 0
          · simp only [h_cond, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
            cases run
            subst_vars
            rfl
          · simp only [h_cond] at run
            by_cases h_jump : jumpable sevm.code x.toNat = true
            · simp only [h_jump] at run
              cases run
              subst_vars
              rfl
            · simp only [h_jump] at run
              contradiction
        · simp only [h_gas] at run
          contradiction
      · simp only [Jinst.Run, Jinst.run, Jinst.runCore, chargeGas_def, Devm.setMach,
          bind, Except.bind, safeSub] at run
        rw [h1] at run
        by_cases h_gas : gJumpdest ≤ devm.gasLeft
        · simp only [h_gas, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
          cases run
          subst_vars
          rfl
        · have h_gas_not : ¬(gJumpdest ≤ devm.gasLeft) := by omega
          simp only [h_gas_not] at run
          contradiction

lemma setStorVal_getStor_ne {devm : Devm} {adr a : Adr} {key val : B256} (h : adr ≠ a) :
    Devm.getStor (devm.setStorVal adr key val) a = Devm.getStor devm a := by
  simp only [Devm.getStor, Devm.getAcct, Devm.setStorVal, Devm.withState,
    Devm.setWorld, State.setStorVal]
  simp only [Devm.state, State.get_set_ne _ h]

lemma sstore_preserves_getStor_ne {pc : Nat} {sevm : Sevm} {s s' : Devm} {a : Adr}
    (run : Rinst.run ⟨pc, sevm, s⟩ .sstore = .ok s')
    (h_ne : sevm.currentTarget ≠ a) :
    Devm.getStor s' a = Devm.getStor s a := by
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨key, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨val, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨_, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨⟨s₃, g₂⟩, h4, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨g₃, h5, run₅⟩
  rcases Except.bind_eq_ok run₅ with ⟨s₄, h6, run₆⟩
  rcases Except.bind_eq_ok run₆ with ⟨s₅, h7, run₇⟩
  rcases Except.bind_eq_ok run₇ with ⟨_, h8, h9⟩
  have e1 : Devm.getStor s = Devm.getStor s₁ := Devm.pop_getStor_eq h1
  have e2 : Devm.getStor s₁ = Devm.getStor s₂ := Devm.pop_getStor_eq h2
  have e4 : Devm.getStor s₂ = Devm.getStor s₃ := by
    split at h4 <;> (injection h4 with eq; injection eq with eq _; subst eq)
    · exact addAccessedStorageKey_getStor.symm
    · rfl
  have e6 : Devm.getStor s₃ = Devm.getStor s₄ := by
    injection h6 with eq; rw [← eq]; rfl
  have e7 : Devm.getStor s₄ = Devm.getStor s₅ := chargeGas_getStor_eq h7
  have E : Devm.getStor s = Devm.getStor s₅ := e1.trans (e2.trans (e4.trans (e6.trans e7)))
  injection h9 with eq
  rw [← eq, setStorVal_getStor_ne h_ne]
  exact (congr_fun E a).symm


lemma addAccessedAddress_state {devm : Devm} {a : Adr} :
    (addAccessedAddress devm a).state = devm.state := by
  exact (addAccessedAddress_worldEq devm a).1.symm

lemma of_benvAfterTransfer_no {msg : Msg} {benv' : Benv}
    (h_stv : ¬ msg.shouldTransferValue = true)
    (h : msg.benvAfterTransfer = .ok benv') : benv' = msg.benv := by
  unfold Msg.benvAfterTransfer at h
  rw [if_neg h_stv] at h
  exact (Except.ok.inj h).symm

lemma of_executeCode_noneCode {msg : Msg} {xl : Xlot}
    {ex : Except (EvmError × Jaune.State × AdrSet × Tra) Devm}
    (h_ca : msg.codeAddress = .none)
    (h : ExecuteCode msg xl ex) :
    ∃ ex', xl = .some ⟨initEvm msg, ex'⟩ ∧
      executeCode.handleError ex' = ex := by
  unfold ExecuteCode executeCode.enter at h
  simp only [h_ca] at h
  rcases h with ⟨ex', hxl, hh⟩
  exact ⟨ex', hxl, hh.symm⟩

lemma chargeCodeGas_state_ok {rules : ForkRules} {d d' : Devm}
    (h : processCreateMessage.chargeCodeGas rules d = .ok d') :
    d'.state = d.state := by
  simp only [processCreateMessage.chargeCodeGas] at h
  split at h
  · cases h
  · rcases Except.bind_eq_ok h with ⟨dG, h_charge, h_if⟩
    split_ifs at h_if
    rw [← Except.ok.inj h_if]
    exact ((Devm.burn_of_chargeGas h_charge).state).symm

lemma Devm.setCode_state {d : Devm} {adr : Adr} {c : ByteArray} :
    (d.setCode adr c).state = d.state.setCode adr c := rfl

-- nonempty code is unchanged by a (sub-)execution
lemma code_eq_of_exec {p : Prog} {sevm' : Sevm} {devm' child : Devm} {wa : Adr}
    (ex_sub : Exec 0 sevm' devm' (.ok child))
    (h_code : some (devm'.getCode wa).toList = Prog.compile p) :
    child.getCode wa = devm'.getCode wa := by
  have h_ne : (devm'.getCode wa).toList ≠ [] := by
    intro hc
    apply @Prog.compile_ne_nil p
    rw [← h_code, hc]
  exact Exec.preserves_getCode ex_sub wa h_ne

/-! ## Generic EVM plumbing

More WETH-free material moved down from `Solvent.lean` unchanged: the
`Linst.Hinv` instances for the balance and storage projections, and the
sub-execution entry/exit case analyses the ladder above consumes. -/

instance : Linst.Hinv Devm.getBal Devm.getBal Linst.stop := by
  constructor; intros e s r h; injection h with h_eq; subst h_eq; rfl

instance : Linst.Hinv Devm.getBal Devm.getBal Linst.ret := by
  constructor; intros e s r h
  simp only [Linst.Run, Linst.run] at h
  rcases Except.bind_eq_ok h with ⟨⟨n1, s1⟩, h1, h2⟩
  rcases Except.bind_eq_ok h2 with ⟨⟨n2, s2⟩, h3, h4⟩
  rcases Except.bind_eq_ok h4 with ⟨s3, h5, h6⟩
  injection h6 with h6
  funext a
  rw [← h6]
  have h_mem : s3.memRead n1 n2 = ⟨(s3.memRead n1 n2).1, (s3.memRead n1 n2).2⟩ := rfl
  show s.getBal a = (s3.memRead n1 n2).2.getBal a
  rw [memRead_getBal_eq h_mem a, chargeGas_getBal_eq h5 a, Devm.popToNat_getBal_eq h3 a, Devm.popToNat_getBal_eq h1 a]

instance : Linst.Hinv Devm.getBal Devm.getBal Linst.rev := by
  constructor; intros e s r h
  simp only [Linst.Run, Linst.run] at h
  rcases Except.bind_eq_ok h with ⟨v1, h1, h2⟩
  rcases Except.bind_eq_ok h2 with ⟨v2, h3, h4⟩
  rcases Except.bind_eq_ok h4 with ⟨v3, h5, h6⟩
  contradiction

instance : Linst.Hinv Devm.getStor Devm.getStor Linst.stop := by
  constructor; intros e s r h; injection h with h_eq; subst h_eq; rfl

instance : Linst.Hinv Devm.getStor Devm.getStor Linst.ret := by
  constructor; intros e s r h
  simp only [Linst.Run, Linst.run] at h
  rcases Except.bind_eq_ok h with ⟨⟨n1, s1⟩, h1, h2⟩
  rcases Except.bind_eq_ok h2 with ⟨⟨n2, s2⟩, h3, h4⟩
  rcases Except.bind_eq_ok h4 with ⟨s3, h5, h6⟩
  injection h6 with h6
  rw [← h6]
  have h_mem : s3.memRead n1 n2 = ⟨(s3.memRead n1 n2).1, (s3.memRead n1 n2).2⟩ := rfl
  show Devm.getStor s = Devm.getStor (s3.memRead n1 n2).2
  rw [memRead_getStor_eq h_mem, ← chargeGas_getStor_eq h5, ← Devm.popToNat_getStor_eq h3, ← Devm.popToNat_getStor_eq h1]

instance : Linst.Hinv Devm.getStor Devm.getStor Linst.rev := by
  constructor; intros e s r h
  simp only [Linst.Run, Linst.run] at h
  rcases Except.bind_eq_ok h with ⟨v1, h1, h2⟩
  rcases Except.bind_eq_ok h2 with ⟨v2, h3, h4⟩
  rcases Except.bind_eq_ok h4 with ⟨v3, h5, h6⟩
  contradiction

lemma Devm.pop_of_popToAdr {a : Adr} {devm devm' : Devm}
    (h : Devm.popToAdr devm = .ok ⟨a, devm'⟩) :
    ∃ x, x.toAdr = a ∧ Devm.pop devm = .ok ⟨x, devm'⟩ := by
  rw [Devm.popToAdr_def] at h
  rcases hp : devm.pop with _ | ⟨x, d⟩ <;> rw [hp] at h
  · cases h
  · dsimp [Prod.mapFst, Prod.map, id] at h
    injection h with h'
    have h1 : x.toAdr = a := congrArg Prod.fst h'
    have h2 : d = devm' := congrArg Prod.snd h'
    rw [← h2]
    exact ⟨x, h1, rfl⟩

lemma accessDelegation_state {devm : Devm} {adr : Adr} :
    (accessDelegation devm adr).2.2.2.2.state = devm.state := by
  dsimp only [accessDelegation]
  cases getDelegatedCodeAddress (devm.state.getCode adr) <;> rfl

lemma accessDelegation_code_of_not {devm : Devm} {adr : Adr}
    (h : ¬ isValidDelegation (devm.state.getCode adr)) :
    (accessDelegation devm adr).2.2.1 = devm.state.getCode adr := by
  have hnone : getDelegatedCodeAddress (devm.state.getCode adr) = none := by
    dsimp only [getDelegatedCodeAddress]
    rw [if_neg h]
  dsimp only [accessDelegation]
  rw [hnone]

lemma getStor_eq_of_state_eq {d d' : Devm} (h : d.state = d'.state) (a : Adr) :
    Devm.getStor d a = Devm.getStor d' a := by
  simp only [Devm.getStor, Devm.getAcct]; rw [h]

lemma getBal_eq_of_state_eq {d d' : Devm} (h : d.state = d'.state) (a : Adr) :
    d.getBal a = d'.getBal a := by
  simp only [Devm.getBal, Devm.getAcct]; rw [h]

lemma getCode_eq_of_state_eq {d d' : Devm} (h : d.state = d'.state) (a : Adr) :
    d.getCode a = d'.getCode a := by
  simp only [Devm.getCode, Devm.getAcct]; rw [h]

-- solvency is preserved when the state is unchanged, given that it was

lemma of_handleError_err {err : EvmError} {d : Devm}
    {ex : Except (EvmError × Jaune.State × AdrSet × Tra) Devm}
    (h : executeCode.handleError (.error ⟨err, d⟩) = ex) :
    (∃ evm2 : Devm, ex = .ok evm2 ∧ evm2.error.isSome = true ∧ evm2.state = d.state) ∨
    (∃ e, ex = .error e) := by
  cases err <;>
    simp only [executeCode.handleError] at h <;>
    first
      | exact Or.inl ⟨_, h.symm, rfl, rfl⟩
      | exact Or.inr ⟨_, h.symm⟩

lemma of_benvAfterTransfer {msg : Msg} {benv' : Benv}
    (h_stv : msg.shouldTransferValue = true)
    (h : msg.benvAfterTransfer = .ok benv') :
    ∃ st_mid, msg.benv.state.subBal msg.caller msg.value = some st_mid ∧
      benv' = (msg.benv.withState st_mid).addBal msg.currentTarget msg.value := by
  unfold Msg.benvAfterTransfer at h
  rw [h_stv] at h
  simp only [if_true] at h
  unfold Benv.subBal at h
  rcases hq : msg.benv.state.subBal msg.caller msg.value with _ | st_mid <;>
    rw [hq] at h <;>
    simp only [Option.toExcept, bind, Option.bind, Except.bind] at h
  · cases h
  · injection h with h
    exact ⟨st_mid, rfl, h.symm⟩

lemma of_executeCode_someCode {msg : Msg} {adr : Adr} {xl : Xlot}
    {ex : Except (EvmError × Jaune.State × AdrSet × Tra) Devm}
    (h_ca : msg.codeAddress = some adr)
    (h : ExecuteCode msg xl ex) :
    ((!msg.disablePrecompiles && decide (msg.benv.stat.rules.isPrecomp adr)) = true ∧
      xl = .none ∧
      executeCode.handleError (executePrecomp (initEvm msg) adr) = ex) ∨
    (¬ (!msg.disablePrecompiles && decide (msg.benv.stat.rules.isPrecomp adr)) = true ∧
      ∃ ex', xl = .some ⟨initEvm msg, ex'⟩ ∧
      executeCode.handleError ex' = ex) := by
  unfold ExecuteCode executeCode.enter at h
  simp only [h_ca] at h
  split_ifs at h with h_pre
  · exact Or.inl ⟨h_pre, h.1, h.2.symm⟩
  · rcases h with ⟨ex', hxl, hh⟩
    exact Or.inr ⟨h_pre, ex', hxl, hh.symm⟩

lemma state_of_executePrecomp_ok {evm : Evm} {adr : Adr} {child : Devm}
    (h : executeCode.handleError (executePrecomp evm adr) = .ok child)
    (h_err : ¬ child.error.isSome = true) :
    child.state = evm.dyna.state := by
  unfold executePrecomp applyPrecompResult at h
  split at h
  · rcases of_handleError_err h with ⟨evm4, h_ok4, h_some4, _⟩ | ⟨e, h_err4⟩
    · injection h_ok4 with h_ok4
      rw [← h_ok4] at h_some4
      exact absurd h_some4 h_err
    · cases h_err4
  · simp only [executeCode.handleError] at h
    injection h with h
    rw [← h]
    rfl

/-! ## The contract-generic ladder -/

namespace ContractSpec

variable {c : ContractSpec}

/-- Once the frame has terminated the callvalue is no longer in flight.  This
is the `inv_forget` slot and nothing else. -/
lemma post_of_pre {ca : Adr} {sevm : Sevm} {devm : Devm}
    (h : c.Pre ca sevm devm) : c.Post ca sevm devm := by
  refine ⟨h.side, ?_⟩
  by_cases hc : sevm.currentTarget = ca
  · exact c.inv_forget (h.inv.left hc)
  · exact h.inv.right hc

lemma Pre.state_eq {wa sevm devm devm'}
    (h_pc : c.Pre wa sevm devm) (h_eq : devm'.state = devm.state) :
    c.Pre wa sevm devm' := by
  cases h_pc with
  | mk h_code h_nof h_solv =>
    have h_bal : devm'.getBal = devm.getBal := by
      funext a; simp [Devm.getBal, Devm.getAcct]; rw [h_eq]
    have h_stor : ∀ a, Devm.getStor devm' a = Devm.getStor devm a := by
      intro a; simp [Devm.getStor, Devm.getAcct]; rw [h_eq]
    constructor
    · have h_gc : devm'.getCode wa = devm.getCode wa := by
        simp [Devm.getCode, Devm.getAcct]; rw [h_eq]
      rw [h_gc]; exact h_code
    · rw [h_bal]; exact h_nof
    · cases h_solv with
      | intro hl hr =>
        constructor
        · intro h; rw [h_bal, h_stor wa]; exact hl h
        · intro h; rw [h_bal, h_stor wa]; exact hr h

lemma Pre.of_eqs {wa : Adr} {sevm : Sevm} {pre inter : Devm}
    (h_pc : c.Pre wa sevm pre)
    (h_code : inter.getCode wa = pre.getCode wa)
    (h_bal : inter.getBal = pre.getBal)
    (h_stor : Devm.getStor inter wa = Devm.getStor pre wa) :
    c.Pre wa sevm inter := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_code]; exact h_pc.code
  · rw [h_bal]; exact h_pc.side
  · intro h; rw [h_bal, h_stor]; exact h_pc.inv.left h
  · intro h; rw [h_bal, h_stor]; exact h_pc.inv.right h

/-- The precondition survives a value transfer that does not debit the
contract.  Slots: `side_transfer` and `inv_transfer`. -/
lemma Pre.transfer_state {ca : Adr} {sevm : Sevm} {pre inter : Devm}
    {caller callee : Adr} {wad : B256} {st_mid : Jaune.State}
    (h_pc : c.Pre ca sevm pre)
    (h_ne : caller ≠ ca)
    (h_sub : pre.state.subBal caller wad = some st_mid)
    (h_state : inter.state = st_mid.addBal callee wad) :
    c.Pre ca sevm inter := by
  rcases of_state_transfer_fields (callee := callee) h_sub with ⟨h_t_stor, h_t_code, -, -, -⟩
  have h_stor_eq : Devm.getStor inter ca = (st_mid.addBal callee wad).getStor ca := by
    show (inter.state.get ca).stor = _
    rw [h_state]; rfl
  have h_bal_eq : inter.getBal ca = (st_mid.addBal callee wad).bal ca := by
    show (inter.state.get ca).bal = _
    rw [h_state]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · show some (inter.state.get ca).code.toList = _
    rw [h_state, h_t_code ca]; exact h_pc.code
  · show c.Side inter.state.bal
    rw [h_state]; exact c.side_transfer h_sub h_pc.side
  · intro h
    show c.Inv (Devm.getStor inter ca) sevm.value (inter.getBal ca)
    rw [h_stor_eq, h_bal_eq]
    exact c.inv_transfer h_sub h_ne h_pc.side (h_pc.inv.left h)
  · intro h
    show c.Inv (Devm.getStor inter ca) 0 (inter.getBal ca)
    rw [h_stor_eq, h_bal_eq]
    exact c.inv_transfer h_sub h_ne h_pc.side (h_pc.inv.right h)

lemma GenericCall.none_preserves_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm}
    {gas : Nat} {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    (h_run : GenericCall sevm devm gas value caller target codeAddress stv
      isStatic ii is oi os code dp .none (.ok inter))
    (h_ne : stv = true → caller ≠ wa)
    (h_pc : c.Pre wa sevm devm) :
    c.Pre wa sevm inter := by
  unfold GenericCall genericCall.step at h_run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_run
  repeat' split at h_run
  all_goals simp only [XStep.ofExcept, XStep.Run] at h_run
  -- depth-zero early exit, push failed
  · cases h_run.2
  -- depth-zero early exit, push succeeded
  · rename_i h_push
    apply h_pc.state_eq
    rw [Except.ok.inj h_run.2, ← (Devm.push_of_push h_push).state]
    rfl
  -- a child frame was entered, but it settled without a sub-derivation
  · obtain ⟨r, hframe, hres⟩ := h_run
    obtain ⟨childMsg, hframe, hc_state, hc_stv, hc_caller, hc_value, hc_ct,
        hc_ca⟩ :
        ∃ m : Msg, ProcessMessage m .none r ∧
          m.benv.state = devm.state ∧ m.shouldTransferValue = stv ∧
          m.caller = caller ∧ m.value = value ∧ m.currentTarget = target ∧
          m.codeAddress = some codeAddress :=
      ⟨_, hframe, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rcases r with err | child
    · cases Resume.call_run_error hres.symm
    have h_inter_state : inter.state = child.state := Resume.call_state hres.symm
    obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp hframe
    unfold FrameBody at hbody
    rcases eq_bt : childMsg.benvAfterTransfer with e | benv <;> rw [eq_bt] at hbody
    · rw [hbody.2, processMessage.settle_error] at hset
      cases hset
    have run_ec : ExecuteCode (childMsg.withBenv benv) .none r0 := hbody
    rcases r0 with x | evm2
    · rw [processMessage.settle_error] at hset
      cases hset
    unfold processMessage.settle at hset
    dsimp only [bind, Except.bind] at hset
    by_cases h_err2 : evm2.error.isSome = true
    · rw [if_pos h_err2] at hset
      apply h_pc.state_eq
      rw [h_inter_state, ← Except.ok.inj hset.symm]
      show childMsg.benv.state = devm.state
      exact hc_state
    · rw [if_neg h_err2] at hset
      have h_eq_child := Except.ok.inj hset.symm
      subst h_eq_child
      have hc_ca2 : (childMsg.withBenv benv).codeAddress = some codeAddress := hc_ca
      rcases of_executeCode_someCode hc_ca2 run_ec with
        ⟨_, _, h_he⟩ | ⟨_, exn, h_xl_some, _⟩
      · have h_child_state : evm2.state = benv.state := by
          have h := state_of_executePrecomp_ok h_he h_err2
          rw [h]; rfl
        by_cases h_stv : stv = true
        · rcases of_benvAfterTransfer (hc_stv.trans h_stv) eq_bt with ⟨st_mid, h_sub, hB⟩
          rw [hc_state, hc_caller, hc_value] at h_sub
          have hBs : benv.state = st_mid.addBal target value := by
            rw [hB, hc_ct, hc_value]; rfl
          have h_state : inter.state = st_mid.addBal target value := by
            rw [h_inter_state, h_child_state, hBs]
          exact Pre.transfer_state h_pc (h_ne h_stv) h_sub h_state
        · have h_stv2 : ¬ childMsg.shouldTransferValue = true := by
            rw [hc_stv]; exact h_stv
          have h_benv : benv = childMsg.benv := of_benvAfterTransfer_no h_stv2 eq_bt
          apply h_pc.state_eq
          rw [h_inter_state, h_child_state, h_benv]
          exact hc_state
      · cases h_xl_some

lemma GenericCreate.none_preserves_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm}
    {endowment : B256} {newAddress : Adr} {memoryIndex memorySize : Nat}
    (h_run : GenericCreate sevm devm endowment newAddress memoryIndex memorySize
      .none (.ok inter))
    (h_pc : c.Pre wa sevm devm) :
    c.Pre wa sevm inter := by
  unfold GenericCreate genericCreate.step at h_run
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic, Pure.pure,
    Except.pure] at h_run
  repeat' split at h_run
  all_goals simp only [XStep.ofExcept, XStep.Run] at h_run
  -- init-code-size assertion failed
  · cases h_run.2
  -- static-context assertion failed
  · cases h_run.2
  -- balance / max-nonce / depth-zero early exit, push failed
  · cases h_run.2
  -- balance / max-nonce / depth-zero early exit, push succeeded
  · rename_i h_push
    apply h_pc.state_eq
    rw [Except.ok.inj h_run.2, ← (Devm.push_of_push h_push).state]
    rfl
  -- address-collision early exit, push failed
  · cases h_run.2
  -- address-collision early exit, push succeeded
  · rename_i h_push
    have h_state : inter.state = devm.state.incrNonce sevm.currentTarget := by
      rw [Except.ok.inj h_run.2, ← (Devm.push_of_push h_push).state]
      rfl
    refine Pre.of_eqs h_pc ?_ ?_ ?_
    · show (inter.state.get wa).code = (devm.state.get wa).code
      rw [h_state]
      exact State.incrNonce_get_code
    · funext b
      show (inter.state.get b).bal = (devm.state.get b).bal
      rw [h_state]
      exact State.incrNonce_get_bal
    · show (inter.state.get wa).stor = (devm.state.get wa).stor
      rw [h_state]
      exact State.incrNonce_get_stor
  -- a child frame was entered : impossible with an empty slot, since a create
  -- frame always runs interpreted code
  · exfalso
    obtain ⟨r, hframe, hres⟩ := h_run
    obtain ⟨childMsg, hframe, hc_ca⟩ :
        ∃ m : Msg, ProcessCreateMessage m .none r ∧ m.codeAddress = .none :=
      ⟨_, hframe, rfl⟩
    obtain ⟨r1, hpm, hset⟩ := ProcessCreateMessage.iff_processMessage.mp hframe
    obtain ⟨r0, hbody, hset1⟩ := ProcessMessage.iff_body.mp hpm
    unfold FrameBody at hbody
    rcases eq_bt : (processCreateMessage.msg childMsg).benvAfterTransfer with e | benv <;>
      rw [eq_bt] at hbody
    · rw [hbody.2, processMessage.settle_error] at hset1
      rw [hset1, processCreateMessage.settle_error] at hset
      rw [hset] at hres
      exact Resume.create_run_error hres.symm
    · have hca :
        ((processCreateMessage.msg childMsg).withBenv benv).codeAddress = .none := hc_ca
      obtain ⟨exn, h_xl, -⟩ := of_executeCode_noneCode hca hbody
      cases h_xl

lemma Xinst.none_preserves_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm} {x : Xinst}
    (h_run : Xinst.Run sevm devm x .none (.ok inter))
    (h_ne : sevm.currentTarget ≠ wa)
    (h_pc : c.Pre wa sevm devm) :
    c.Pre wa sevm inter := by
  unfold Xinst.Run at h_run
  rcases Xinst.step_shape sevm devm x with ⟨ex, hs, hframe⟩ |
    ⟨d, e, na, mi, ms, hf, hs⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, hcal, -, hs⟩ <;> rw [hs] at h_run
  · obtain ⟨-, hex⟩ := h_run
    rw [← hex] at hframe
    have hif : Devm.InstructionFrame devm inter := hframe
    exact h_pc.state_eq hif.state.symm
  · exact GenericCreate.none_preserves_precond h_run (h_pc.state_eq hf.state.symm)
  · refine GenericCall.none_preserves_precond h_run ?_ (h_pc.state_eq hf.state.symm)
    rintro hstv
    rcases hcal with ⟨-, rfl⟩ | ⟨hsf, -⟩
    · exact h_ne
    · rw [hsf] at hstv; cases hstv



-- the precondition carries over to the initial state of a sub-execution

-- the precondition carries over to the initial state of a sub-execution
-- started after a balance transfer from a sender that is not the contract
lemma Pre.child_of_transfer {ca : Adr} {sevm sevm' : Sevm} {devm devm' : Devm}
    {st st_mid : Jaune.State} {caller target : Adr} {value : B256}
    (h_pc : c.Pre ca sevm devm)
    (h_ct_ne : sevm.currentTarget ≠ ca)
    (h_ne : caller ≠ ca)
    (h_stor : (st.get ca).stor = (devm.state.get ca).stor)
    (h_code : (st.get ca).code = (devm.state.get ca).code)
    (h_bal : ∀ a, (st.get a).bal = (devm.state.get a).bal)
    (h_sub : st.subBal caller value = some st_mid)
    (h_state : devm'.state = st_mid.addBal target value)
    (h_ct' : sevm'.currentTarget = target)
    (h_val : sevm'.currentTarget = ca → sevm'.value = value) :
    c.Pre ca sevm' devm' := by
  have h_bal_st : st.bal = devm.getBal := by funext a; exact h_bal a
  have h_side_st : c.Side st.bal := by rw [h_bal_st]; exact h_pc.side
  rcases of_state_transfer_fields (callee := target) h_sub with
    ⟨h_t_stor, h_t_code, _, _, _⟩
  have h_inv_st : c.Inv (st.getStor ca) 0 (st.bal ca) := by
    show c.Inv (st.get ca).stor 0 (st.get ca).bal
    rw [h_stor, h_bal ca]
    exact h_pc.inv.right h_ct_ne
  have h_stor' : Devm.getStor devm' ca = (st_mid.addBal target value).getStor ca := by
    show (devm'.state.get ca).stor = _
    rw [h_state]; rfl
  have h_bal' : devm'.getBal ca = (st_mid.addBal target value).bal ca := by
    show (devm'.state.get ca).bal = _
    rw [h_state]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · show some (devm'.state.get ca).code.toList = _
    rw [h_state, h_t_code ca, h_code]; exact h_pc.code
  · show c.Side devm'.state.bal
    rw [h_state]; exact c.side_transfer h_sub h_side_st
  · intro h_eq
    have h_t_ca : target = ca := h_ct'.symm.trans h_eq
    subst h_t_ca
    show c.Inv (Devm.getStor devm' target) sevm'.value (devm'.getBal target)
    rw [h_stor', h_bal', h_val h_eq]
    exact c.inv_recv_transfer h_sub h_ne h_side_st h_inv_st
  · intro h_ne_ct
    have h_t_ne : target ≠ ca := fun hc => h_ne_ct (h_ct'.trans hc)
    show c.Inv (Devm.getStor devm' ca) 0 (devm'.getBal ca)
    rw [h_stor', h_bal']
    exact c.inv_transfer h_sub h_ne h_side_st h_inv_st

-- the precondition carries over to the initial state of a sub-execution
-- started without a balance transfer
lemma Pre.child_of_eqs {wa : Adr} {sevm sevm' : Sevm} {devm devm' : Devm}
    (h_pc : c.Pre wa sevm devm)
    (h_ct_ne : sevm.currentTarget ≠ wa)
    (h_state : devm'.state = devm.state)
    (h_val : sevm'.currentTarget = wa → sevm'.value = 0) :
    c.Pre wa sevm' devm' := by
  have h_solv := h_pc.inv.right h_ct_ne
  have h_stor' := getStor_eq_of_state_eq h_state wa
  have h_bal' := getBal_eq_of_state_eq h_state wa
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [getCode_eq_of_state_eq h_state wa]; exact h_pc.code
  · have h_bf : devm'.getBal = devm.getBal := funext (getBal_eq_of_state_eq h_state)
    rw [h_bf]; exact h_pc.side
  · intro h_eq; rw [h_val h_eq, h_stor', h_bal']; exact h_solv
  · intro _; rw [h_stor', h_bal']; exact h_solv

-- the precondition is restored after a successful sub-execution whose final
-- state satisfies the postcondition
lemma Pre.of_postcond {wa : Adr} {sevm sevm' : Sevm} {child inter devm' : Devm}
    (h_post : c.Post wa sevm' child)
    (h_ct_ne : sevm.currentTarget ≠ wa)
    (h_code_pre : some (devm'.getCode wa).toList = Prog.compile c.prog)
    (h_code_eq : child.getCode wa = devm'.getCode wa)
    (h_stor : (inter.state.get wa).stor = (child.state.get wa).stor)
    (h_code : (inter.state.get wa).code = (child.state.get wa).code)
    (h_bal : ∀ a, (inter.state.get a).bal = (child.state.get a).bal) :
    c.Pre wa sevm inter := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show some (inter.state.get wa).code.toList = Prog.compile c.prog
    rw [h_code]
    show some (child.getCode wa).toList = Prog.compile c.prog
    rw [h_code_eq]
    exact h_code_pre
  · have h_bf : inter.getBal = child.getBal := by
      funext a; exact h_bal a
    rw [h_bf]; exact h_post.side
  · intro h_eq; exact absurd h_eq h_ct_ne
  · intro _
    have h_stor' : Devm.getStor inter wa = Devm.getStor child wa := h_stor
    have h_bal' : inter.getBal wa = child.getBal wa := h_bal wa
    rw [h_stor', h_bal']
    exact h_post.inv

lemma GenericCall.some_preserves_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm}
    {gas : Nat} {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    {evm' : Evm} {exn' : Execution}
    (h_run : GenericCall sevm devm gas value caller target codeAddress stv
      isStatic ii is oi os code dp (.some ⟨evm', exn'⟩) (.ok inter))
    (ex_sub : Exec evm'.pc evm'.sta evm'.dyna exn')
    (h_ct_ne : sevm.currentTarget ≠ wa)
    (h_ne : stv = true → caller ≠ wa)
    (h_tv : stv = false → target = wa → value = 0)
    (h_pc : c.Pre wa sevm devm) :
    c.Pre wa evm'.sta evm'.dyna ∧
      (ifOk (c.Post wa evm'.sta) exn' → c.Pre wa sevm inter) := by
  unfold GenericCall genericCall.step at h_run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_run
  repeat' split at h_run
  all_goals simp only [XStep.ofExcept, XStep.Run] at h_run
  -- the two depth-zero exits leave the slot empty
  · cases h_run.1
  · cases h_run.1
  -- the child frame was entered
  obtain ⟨r, hframe, hres⟩ := h_run
  obtain ⟨childMsg, hframe, hc_state, hc_stv, hc_caller, hc_value, hc_ct, hc_ca⟩ :
      ∃ m : Msg, ProcessMessage m (.some ⟨evm', exn'⟩) r ∧
        m.benv.state = devm.state ∧ m.shouldTransferValue = stv ∧
        m.caller = caller ∧ m.value = value ∧ m.currentTarget = target ∧
        m.codeAddress = some codeAddress :=
    ⟨_, hframe, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rcases r with err | child
  · cases Resume.call_run_error hres.symm
  have h_inter_state : inter.state = child.state := Resume.call_state hres.symm
  obtain ⟨henter, hr⟩ := RunFrame.some_inv hframe
  obtain ⟨benv, eq_bt, h_evm⟩ := Frame.enter_run_inv henter
  have hpc0 : evm'.pc = 0 := Frame.enter_run_pc henter
  -- projections of the sub-execution's initial machine
  have h_ds : evm'.dyna.state = benv.state := by rw [h_evm]; rfl
  have h_ct' : evm'.sta.currentTarget = target := by rw [h_evm]; exact hc_ct
  have h_v' : evm'.sta.value = value := by rw [h_evm]; exact hc_value
  -- the frame's settlement, unfolded
  have hr2 : processMessage.settle childMsg (executeCode.handleError exn')
      = .ok child := hr.symm
  rcases h_he : executeCode.handleError exn' with x | evm2
  · rw [h_he, processMessage.settle_error] at hr2
    cases hr2
  rw [h_he] at hr2
  unfold processMessage.settle at hr2
  dsimp only [bind, Except.bind] at hr2
  -- part 1 : the precondition holds for the sub-execution's initial state
  have h_pre1 : c.Pre wa evm'.sta evm'.dyna := by
    by_cases h_stv : stv = true
    · rcases of_benvAfterTransfer (hc_stv.trans h_stv) eq_bt with ⟨st_mid, h_sub, hB⟩
      rw [hc_state, hc_caller, hc_value] at h_sub
      have h_state : evm'.dyna.state = st_mid.addBal target value := by
        rw [h_ds, hB, hc_ct, hc_value]
        rfl
      exact Pre.child_of_transfer h_pc h_ct_ne (h_ne h_stv) rfl rfl (fun _ => rfl)
        h_sub h_state h_ct' (fun _ => h_v')
    · have h_stv2 : ¬ childMsg.shouldTransferValue = true := by rw [hc_stv]; exact h_stv
      have h_benv : benv = childMsg.benv := of_benvAfterTransfer_no h_stv2 eq_bt
      have h_state : evm'.dyna.state = devm.state := by
        rw [h_ds, h_benv]; exact hc_state
      apply Pre.child_of_eqs h_pc h_ct_ne h_state
      intro h_eq
      have h_sf : stv = false := by
        cases stv
        · rfl
        · exact absurd rfl h_stv
      rw [h_v']
      exact h_tv h_sf (h_ct'.symm.trans h_eq)
  refine ⟨h_pre1, ?_⟩
  -- part 2 : the precondition is restored after the call returns
  intro h_ifOk
  rcases exn' with ⟨err3, d3⟩ | child3
  · -- sub-execution ended in error : the parent state is rolled back
    rcases of_handleError_err h_he with ⟨evm2', h_ok2, h_some2, _⟩ | ⟨e, h_err2⟩
    · have h_eq2 : evm2 = evm2' := Except.ok.inj h_ok2
      subst h_eq2
      rw [if_pos h_some2] at hr2
      have h_child := Except.ok.inj hr2
      apply h_pc.state_eq
      rw [h_inter_state, ← h_child]
      show childMsg.benv.state = devm.state
      exact hc_state
    · cases h_err2
  · -- sub-execution succeeded
    dsimp only [executeCode.handleError] at h_he
    have h_eq2 : child3 = evm2 := Except.ok.inj h_he
    subst h_eq2
    have h_post : c.Post wa evm'.sta child3 := h_ifOk
    by_cases h_err : child3.error.isSome = true
    · -- the sub-execution set the error flag : the parent state is rolled back
      rw [if_pos h_err] at hr2
      have h_child := Except.ok.inj hr2
      apply h_pc.state_eq
      rw [h_inter_state, ← h_child]
      show childMsg.benv.state = devm.state
      exact hc_state
    · -- clean success : reconstruct the precondition from the postcondition
      rw [if_neg h_err] at hr2
      have h_child := Except.ok.inj hr2
      subst h_child
      exact Pre.of_postcond h_post h_ct_ne h_pre1.code
        (code_eq_of_exec (hpc0 ▸ ex_sub) h_pre1.code)
        (congrArg (fun st => (st.get wa).stor) h_inter_state)
        (congrArg (fun st => (st.get wa).code) h_inter_state)
        (fun a => congrArg (fun st => (st.get a).bal) h_inter_state)


lemma GenericCreate.some_preserves_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm}
    {endowment : B256} {newAddress : Adr} {memoryIndex memorySize : Nat}
    {evm' : Evm} {exn' : Execution}
    (h_run : GenericCreate sevm devm endowment newAddress memoryIndex memorySize
      (.some ⟨evm', exn'⟩) (.ok inter))
    (ex_sub : Exec evm'.pc evm'.sta evm'.dyna exn')
    (h_ct_ne : sevm.currentTarget ≠ wa)
    (h_pc : c.Pre wa sevm devm) :
    c.Pre wa evm'.sta evm'.dyna ∧
      (ifOk (c.Post wa evm'.sta) exn' → c.Pre wa sevm inter) := by
  unfold GenericCreate genericCreate.step at h_run
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic, Pure.pure,
    Except.pure] at h_run
  repeat' split at h_run
  all_goals simp only [XStep.ofExcept, XStep.Run] at h_run
  -- every childless outcome leaves the slot empty
  · cases h_run.1
  · cases h_run.1
  · cases h_run.1
  · cases h_run.1
  · cases h_run.1
  · cases h_run.1
  -- the child frame is entered
  rename_i h_coll
  push Not at h_coll
  obtain ⟨r, hframe, hres⟩ := h_run
  obtain ⟨devm5, childMsg, hframe, h_st5, hc_state, hc_caller, hc_value, hc_ct,
      hc_ca, hc_stv, hcoll5⟩ :
      ∃ (d5 : Devm) (m : Msg), ProcessCreateMessage m (.some ⟨evm', exn'⟩) r ∧
        d5.state = devm.state.incrNonce sevm.currentTarget ∧
        m.benv.state = d5.state ∧ m.caller = sevm.currentTarget ∧
        m.value = endowment ∧ m.currentTarget = newAddress ∧
        m.codeAddress = .none ∧ m.shouldTransferValue = true ∧
        (d5.state.get newAddress).code.size = 0 :=
    ⟨_, _, hframe, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h_coll.2.1⟩
  -- the new address cannot be the WETH address, whose code is nonempty
  have h_new_ne : newAddress ≠ wa := by
    intro hc
    subst hc
    apply @Prog.compile_ne_nil c.prog
    rw [← h_pc.code]
    have h_code4 : (devm5.state.get newAddress).code = devm.getCode newAddress := by
      rw [h_st5]
      exact State.incrNonce_get_code
    rw [← h_code4]
    have h_nil : (devm5.state.get newAddress).code.toList = [] := by
      have h_len := ByteArray.size_eq_length_toList (devm5.state.get newAddress).code
      rw [hcoll5] at h_len
      cases h_toList : (devm5.state.get newAddress).code.toList
      · rfl
      · rw [h_toList] at h_len
        cases h_len
    rw [h_nil]
  -- the instruction succeeded, so the sub-message result must be ok
  rcases r with err | child
  · cases Resume.create_run_error hres.symm
  have h_inter_state : inter.state = child.state := Resume.create_state hres.symm
  obtain ⟨henter, hr⟩ := RunFrame.some_inv hframe
  have hpc0 : evm'.pc = 0 := Frame.enter_run_pc henter
  obtain ⟨benv', eq_bt, h_evm⟩ := Frame.enter_run_inv henter
  have hset : processCreateMessage.settle childMsg
      (processMessage.settle (processCreateMessage.msg childMsg)
        (executeCode.handleError exn')) = .ok child := hr.symm
  rcases h_he : executeCode.handleError exn' with x | evmB
  · rw [h_he, processMessage.settle_error, processCreateMessage.settle_error] at hset
    cases hset
  rw [h_he] at hset
  rcases hA : processMessage.settle (processCreateMessage.msg childMsg) (.ok evmB) with
    x | evmA
  · rw [hA, processCreateMessage.settle_error] at hset
    cases hset
  rw [hA] at hset
  unfold processMessage.settle at hA
  dsimp only [bind, Except.bind] at hA
  unfold processCreateMessage.settle at hset
  dsimp only [bind, Except.bind] at hset
  have h_ifB := hA
  have h_ifA := hset
  -- projections of the create message
  have hP_state : (processCreateMessage.msg childMsg).benv.state
      = (childMsg.benv.state.setStor childMsg.currentTarget Stor.empty).incrNonce
          childMsg.currentTarget := rfl
  have hP_caller : (processCreateMessage.msg childMsg).caller = sevm.currentTarget :=
    hc_caller
  have hP_value : (processCreateMessage.msg childMsg).value = endowment := hc_value
  have hP_stv : (processCreateMessage.msg childMsg).shouldTransferValue = true := hc_stv
  have h_ds : evm'.dyna.state = benv'.state := by rw [h_evm]; rfl
  have h_ct' : evm'.sta.currentTarget = newAddress := by rw [h_evm]; exact hc_ct
  -- the balance transfer performed before the sub-execution
  rcases of_benvAfterTransfer hP_stv eq_bt with ⟨st_mid, h_sub, hB⟩
  rw [hP_state, hP_caller, hP_value, hc_ct] at h_sub
  have h_base_stor :
      (((childMsg.benv.state.setStor newAddress Stor.empty).incrNonce newAddress).get wa).stor
        = (devm.state.get wa).stor := by
    rw [State.incrNonce_get_stor, State.setStor_get_stor_ne h_new_ne, hc_state, h_st5,
      State.incrNonce_get_stor]
  have h_base_code :
      (((childMsg.benv.state.setStor newAddress Stor.empty).incrNonce newAddress).get wa).code
        = (devm.state.get wa).code := by
    rw [State.incrNonce_get_code, State.setStor_get_code, hc_state, h_st5,
      State.incrNonce_get_code]
  have h_base_bal : ∀ a,
      (((childMsg.benv.state.setStor newAddress Stor.empty).incrNonce newAddress).get a).bal
        = (devm.state.get a).bal := by
    intro a
    rw [State.incrNonce_get_bal, State.setStor_get_bal, hc_state, h_st5,
      State.incrNonce_get_bal]
  -- part 1 : the precondition holds for the sub-execution's initial state
  have h_pre1 : c.Pre wa evm'.sta evm'.dyna := by
    have h_state : evm'.dyna.state = st_mid.addBal newAddress endowment := by
      rw [h_ds, hB]
      show st_mid.addBal childMsg.currentTarget childMsg.value = _
      rw [hc_ct, hc_value]
    apply Pre.child_of_transfer h_pc h_ct_ne h_ct_ne h_base_stor h_base_code h_base_bal
      h_sub h_state h_ct'
    intro hc
    exact absurd (h_ct'.symm.trans hc) h_new_ne
  refine ⟨h_pre1, ?_⟩
  -- part 2 : the precondition is restored after the create returns
  intro h_ifOk
  -- when the sub-message rolls back, the parent state is unchanged modulo the nonce
  have h_rb : child.state = childMsg.benv.state → c.Pre wa sevm inter := by
    intro h_cs
    refine Pre.of_eqs h_pc ?_ ?_ ?_
    · show (inter.state.get wa).code = (devm.state.get wa).code
      rw [h_inter_state, h_cs, hc_state, h_st5]
      exact State.incrNonce_get_code
    · funext b
      show (inter.state.get b).bal = (devm.state.get b).bal
      rw [h_inter_state, h_cs, hc_state, h_st5]
      exact State.incrNonce_get_bal
    · show (inter.state.get wa).stor = (devm.state.get wa).stor
      rw [h_inter_state, h_cs, hc_state, h_st5]
      exact State.incrNonce_get_stor
  have h_isNone_false : ∀ {dX : Devm}, dX.error.isSome = true → dX.error.isNone ≠ true := by
    intro dX h_some hc
    rw [Option.isNone_iff_eq_none] at hc
    rw [hc] at h_some
    cases h_some
  have h_isNone_true : ∀ {dX : Devm}, ¬ dX.error.isSome = true → dX.error.isNone = true := by
    intro dX h_ns
    rcases h_opt : dX.error with _ | v
    · rfl
    · rw [h_opt] at h_ns
      exact absurd rfl h_ns
  rcases exn' with ⟨err4, d4⟩ | child4
  · -- sub-execution ended in error : the parent state is rolled back
    rcases of_handleError_err h_he with ⟨evmB', h_okB, h_someB, _⟩ | ⟨e, h_errB⟩
    · have h_eqB : evmB = evmB' := Except.ok.inj h_okB
      subst h_eqB
      rw [if_pos h_someB] at h_ifB
      have h_A := Except.ok.inj h_ifB
      have h_someA : evmA.error.isSome = true := by
        rw [← h_A]
        exact h_someB
      rw [if_neg (h_isNone_false h_someA)] at h_ifA
      have h_child := Except.ok.inj h_ifA
      apply h_rb
      rw [← h_child]
      rfl
    · cases h_errB
  · -- sub-execution succeeded
    dsimp only [executeCode.handleError] at h_he
    have h_eqB : child4 = evmB := Except.ok.inj h_he
    subst h_eqB
    have h_post : c.Post wa evm'.sta child4 := h_ifOk
    by_cases h_errC : child4.error.isSome = true
    · -- the sub-execution set the error flag : the parent state is rolled back
      rw [if_pos h_errC] at h_ifB
      have h_A := Except.ok.inj h_ifB
      have h_someA : evmA.error.isSome = true := by
        rw [← h_A]
        exact h_errC
      rw [if_neg (h_isNone_false h_someA)] at h_ifA
      have h_child := Except.ok.inj h_ifA
      apply h_rb
      rw [← h_child]
      rfl
    · -- clean success
      rw [if_neg h_errC] at h_ifB
      have h_A := Except.ok.inj h_ifB
      subst h_A
      rw [if_pos (h_isNone_true h_errC)] at h_ifA
      rcases h_cc : processCreateMessage.chargeCodeGas childMsg.benv.stat.rules child4
        with ⟨errC, evmC⟩ | evmC
      · -- code-deposit gas charge failed
        simp only [h_cc] at h_ifA
        cases errC
        case halt reason =>
          have h_child := Except.ok.inj h_ifA
          apply h_rb
          rw [← h_child]
          rfl
        all_goals cases h_ifA
      · -- code deposit succeeded : reconstruct the precondition
        simp only [h_cc] at h_ifA
        have h_child := Except.ok.inj h_ifA
        have h_stC : evmC.state = child4.state := chargeCodeGas_state_ok h_cc
        apply Pre.of_postcond h_post h_ct_ne h_pre1.code
          (code_eq_of_exec (hpc0 ▸ ex_sub) h_pre1.code)
        · rw [h_inter_state, ← h_child, Devm.setCode_state, h_stC, hc_ct,
            State.setCode_get_stor]
        · rw [h_inter_state, ← h_child, Devm.setCode_state, h_stC, hc_ct,
            State.setCode_get_code_ne h_new_ne]
        · intro a
          rw [h_inter_state, ← h_child, Devm.setCode_state, h_stC, hc_ct,
            State.setCode_get_bal]


lemma Xinst.some_preserves_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm} {x : Xinst}
    {evm' : Evm} {exn' : Execution}
    (h_run : Xinst.Run sevm devm x (.some ⟨evm', exn'⟩) (.ok inter))
    (ex_sub : Exec evm'.pc evm'.sta evm'.dyna exn')
    (h_ne : sevm.currentTarget ≠ wa)
    (h_pc : c.Pre wa sevm devm) :
    c.Pre wa evm'.sta evm'.dyna ∧
      (ifOk (c.Post wa evm'.sta) exn' → c.Pre wa sevm inter) := by
  unfold Xinst.Run at h_run
  rcases Xinst.step_shape sevm devm x with ⟨ex, hs, hframe⟩ |
    ⟨d, e, na, mi, ms, hfr, hs⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hfr, -, hcal, -, hs⟩ <;> rw [hs] at h_run
  -- a childless outcome cannot fill the slot
  · cases h_run.1
  -- dispatched to the CREATE family
  · exact GenericCreate.some_preserves_precond h_run ex_sub h_ne
      (h_pc.state_eq hfr.state.symm)
  -- dispatched to the CALL family
  · refine GenericCall.some_preserves_precond h_run ex_sub h_ne ?_ ?_
      (h_pc.state_eq hfr.state.symm)
    · rintro hstv
      rcases hcal with ⟨-, rfl⟩ | ⟨hsf, -⟩
      · exact h_ne
      · rw [hsf] at hstv; cases hstv
    · rintro hsf ht
      rcases hcal with ⟨hst, -⟩ | ⟨-, rfl⟩
      · rw [hsf] at hst; cases hst
      · exact absurd ht h_ne


lemma Post.dest_delete {ca : Adr} {sevm : Sevm} {devm : Devm}
    (h_ne : sevm.currentTarget ≠ ca) (h_pc : c.Pre ca sevm devm) :
    c.Post ca sevm
      (addAccountToDelete (devm.setBal sevm.currentTarget 0) sevm.currentTarget) := by
  have h_bal_self :
      (addAccountToDelete (devm.setBal sevm.currentTarget 0) sevm.currentTarget).getBal
        sevm.currentTarget = 0 := by
    show ((devm.state.setBal sevm.currentTarget 0).get sevm.currentTarget).bal = 0
    rw [State.setBal_get_self]; rfl
  have h_bal_ne : ∀ a, sevm.currentTarget ≠ a →
      (addAccountToDelete (devm.setBal sevm.currentTarget 0) sevm.currentTarget).getBal a =
        devm.getBal a := by
    intro a ha
    show ((devm.state.setBal sevm.currentTarget 0).get a).bal = (devm.state.get a).bal
    rw [State.setBal_get_ne ha]
  have h_stor_eq :
      Devm.getStor (addAccountToDelete (devm.setBal sevm.currentTarget 0) sevm.currentTarget) ca =
        Devm.getStor devm ca := by
    show ((devm.state.setBal sevm.currentTarget 0).get ca).stor = (devm.state.get ca).stor
    apply State.setBal_get_stor
  have h_dec :
      Decrease sevm.currentTarget (devm.getBal sevm.currentTarget) devm.getBal
        (addAccountToDelete (devm.setBal sevm.currentTarget 0) sevm.currentTarget).getBal := by
    intro a
    constructor
    · intro h_eq; subst h_eq
      rw [h_bal_self, B256.sub_self]
    · intro ha; exact (h_bal_ne a ha).symm
  have h_sum :
      sum devm.getBal - (devm.getBal sevm.currentTarget).toNat =
        sum (addAccountToDelete (devm.setBal sevm.currentTarget 0) sevm.currentTarget).getBal :=
    sum_sub_assoc h_dec (B256.le_of_toNat_le_toNat (Nat.le_refl _))
  refine ⟨c.side_le h_pc.side (by omega), ?_⟩
  show c.Inv (Devm.getStor (addAccountToDelete (devm.setBal sevm.currentTarget 0)
      sevm.currentTarget) ca) 0
    ((addAccountToDelete (devm.setBal sevm.currentTarget 0) sevm.currentTarget).getBal ca)
  rw [h_stor_eq, h_bal_ne ca h_ne]
  exact h_pc.inv.right h_ne

lemma Linst.inv_postcond {wa : Adr} {sevm : Sevm} {pre post : Devm} {l : Linst}
    (h_run : Linst.Run sevm pre l (.ok post))
    (h_ne : sevm.currentTarget ≠ wa)
    (h_pc : c.Pre wa sevm pre) :
    c.Post wa sevm post := by
  cases l
  case stop =>
    dsimp [Linst.Run, Linst.run] at h_run
    injection h_run with h_eq; subst h_eq
    exact post_of_pre h_pc
  case ret =>
    have h_bal : pre.getBal = post.getBal :=
      ((inferInstance : Linst.Hinv Devm.getBal Devm.getBal Linst.ret)).inv h_run
    have h_stor : Devm.getStor pre = Devm.getStor post :=
      ((inferInstance : Linst.Hinv Devm.getStor Devm.getStor Linst.ret)).inv h_run
    constructor
    · rw [← h_bal]; exact h_pc.side
    · show c.Inv (Devm.getStor post wa) 0 (post.getBal wa)
      have hb : post.getBal wa = pre.getBal wa := (congr_fun h_bal wa).symm
      have hs : Devm.getStor post wa = Devm.getStor pre wa := (congr_fun h_stor wa).symm
      rw [hb, hs]
      exact h_pc.inv.right h_ne
  case rev =>
    dsimp [Linst.Run, Linst.run] at h_run
    rcases Except.bind_eq_ok h_run with ⟨_, _, h2⟩
    rcases Except.bind_eq_ok h2 with ⟨_, _, h4⟩
    rcases Except.bind_eq_ok h4 with ⟨_, _, h6⟩
    contradiction
  case dest =>
    dsimp [Linst.Run, Linst.run] at h_run
    rcases Except.bind_eq_ok h_run with ⟨⟨dest_a, devm1⟩, h_pop, h_run1⟩
    rcases Except.bind_eq_ok h_run1 with ⟨devm2, h_charge, h_run2⟩
    rcases Except.bind_eq_ok h_run2 with ⟨_, h_assert, h_run3⟩
    rcases Except.bind_eq_ok h_run3 with ⟨devm3, h_sub, h_run4⟩
    have h_sub_some : devm2.subBal sevm.currentTarget ((dest_a, devm1).2.getAcct sevm.currentTarget).bal = some devm3 := by
      cases eq : devm2.subBal sevm.currentTarget ((dest_a, devm1).2.getAcct sevm.currentTarget).bal
      · rw [eq] at h_sub; contradiction
      · rw [eq] at h_sub; injection h_sub with h; subst h; rfl
    have h_sub_st : devm2.state.subBal sevm.currentTarget ((dest_a, devm1).2.getAcct sevm.currentTarget).bal = some devm3.state := by
      dsimp [Devm.subBal, Option.bind] at h_sub_some
      cases h : devm2.state.subBal sevm.currentTarget ((dest_a, devm1).2.getAcct sevm.currentTarget).bal
      · rw [h] at h_sub_some; contradiction
      · rw [h] at h_sub_some; injection h_sub_some with h2; subst h2; rfl
    have h_bal2 : devm2.getBal = devm1.getBal := by
      ext a
      have := chargeGas_getBal_eq h_charge a
      rw [this]
      split
      · simp [Devm.getBal, Devm.getAcct]
        rw [addAccessedAddress_state]
      · rfl
    have h_pc1 : c.Pre wa sevm devm1 := by
      apply Pre.of_eqs h_pc
      · exact Devm.popToAdr_getCode_eq h_pop wa
      · ext a; exact Devm.popToAdr_getBal_eq h_pop a
      · exact congr_fun (Devm.popToAdr_getStor_eq h_pop).symm wa
    have h_pc2 : c.Pre wa sevm devm2 := by
      apply Pre.of_eqs h_pc1
      · have h_code : devm2.getCode = devm1.getCode := by
          funext a
          have h1 := chargeGas_getCode_eq h_charge a
          have h2 : (if ((dest_a, devm1).1 ∉ (dest_a, devm1).2.accessedAddresses) then (addAccessedAddress (dest_a, devm1).2 (dest_a, devm1).1, gasSelfDestruct + gasColdAccountAccess) else ((dest_a, devm1).2, gasSelfDestruct)).1.getCode a = devm1.getCode a := by
            split <;> rfl
          exact h1.trans h2
        exact congr_fun h_code wa
      · exact h_bal2
      · have h_stor : Devm.getStor devm2 = Devm.getStor devm1 := by
          have h1 := (chargeGas_getStor_eq h_charge).symm
          have h2 : Devm.getStor ((if ((dest_a, devm1).1 ∉ (dest_a, devm1).2.accessedAddresses) then (addAccessedAddress (dest_a, devm1).2 (dest_a, devm1).1, gasSelfDestruct + gasColdAccountAccess) else ((dest_a, devm1).2, gasSelfDestruct)).1) = Devm.getStor devm1 := by
            split <;> rfl
          exact h1.trans h2
        exact congr_fun h_stor wa
    have h_pc3 : c.Pre wa sevm (devm3.addBal dest_a ((dest_a, devm1).2.getAcct sevm.currentTarget).bal) := by
      exact Pre.transfer_state h_pc2 h_ne h_sub_st rfl
    clear h_run h_run1 h_run2 h_run3
    split at h_run4
    · rw [← Except.ok.inj h_run4]
      exact Post.dest_delete h_ne h_pc3
    · rw [← Except.ok.inj h_run4]
      exact post_of_pre h_pc3

/-! ### The frame-level ladder

`lift_inv` (CommonProofs.lean) is already generic in the program and in the two
predicates; what was WETH-specific about `weth_preserves_solvent` was only the
five obligations fed to it.  Four of those are discharged here once and for
all, for every contract.  The fifth — that a top-level run of the contract's
own program takes the precondition to the postcondition — is the contract's
own work and stays a hypothesis. -/

theorem preserves_inv (c : ContractSpec) (ca : Adr)
    ( body :
      ∀ {sevm pre post},
        Prog.Run sevm pre c.prog post →
        sevm.currentTarget = ca →
        ( ∀ pc' sevm' pre' post',
            Exec pc' sevm' pre' (.ok post') →
            sevm'.depth < sevm.depth →
            Prog.At c.prog ca pc' sevm' pre' →
            c.Pre ca sevm' pre' →
            c.Post ca sevm' post' ) →
        c.Pre ca sevm pre →
        c.Post ca sevm post ) :
    ∀ sevm pre post,
      Exec 0 sevm pre (.ok post) →
      (sevm.currentTarget = ca → some sevm.code.toList = Prog.compile c.prog) →
      c.Pre ca sevm pre →
      c.Post ca sevm post := by
  intro sevm devm exn exc h_code h_pc
  apply lift_inv ca c.prog (c.Pre ca) (c.Post ca)
  · exact body
  · intro pc' sevm' pre' n' inter' h_at' h_run' h_ne' h_pc'
    cases n' with
    | push xs le =>
      simp only [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at h_run'
      rcases Except.bind_eq_ok h_run'.2.symm with ⟨devm1, h_charge, h_push⟩
      exact h_pc'.state_eq
        (((Devm.burn_of_chargeGas h_charge).state).trans
          ((Devm.push_of_push h_push).state)).symm
    | reg r =>
      have h_reg : Rinst.run ⟨pc', sevm', pre'⟩ r = .ok inter' := by
        simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at h_run'
        exact h_run'.2.symm
      by_cases h_ss : r = Rinst.sstore
      · subst h_ss
        have h_frame := Rinst.sstore_run_stateWriteFrame pc' pre' sevm'
        rw [h_reg] at h_frame
        refine Pre.of_eqs h_pc' (h_frame.getCode_eq ca).symm ?_
          (sstore_preserves_getStor_ne h_reg h_ne')
        funext b
        exact (h_frame.getBal_eq b).symm
      · exact Pre.of_eqs h_pc' (Rinst.preserves_getCode h_reg ca) (Rinst.preserves_bal h_reg).symm
          (congr_fun (Rinst.preserves_stor h_ss h_reg) ca).symm
    | exec x =>
      refine Xinst.none_preserves_precond (x := x) ?_ h_ne' h_pc'
      simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.Run] using h_run'
  · intro pc' sevm' pre' n' evm'' exn'' inter' h_at' h_run' ex_sub' h_ne' h_pc'
    cases n' with
    | push xs le =>
      simp only [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at h_run'
      cases h_run'.1
    | reg r =>
      simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at h_run'
      cases h_run'.1
    | exec x =>
      refine Xinst.some_preserves_precond (x := x) ?_ ex_sub' h_ne' h_pc'
      simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.Run] using h_run'
  · intro pc' sevm' pre' j' pc'' inter' h_at' h_run' h_ne' h_pc'
    exact Pre.state_eq h_pc' (Jinst.preserves_state h_run')
  · intro pc' sevm' pre' l' post' h_at' h_run' h_ne' h_pc'
    exact Linst.inv_postcond h_run' h_ne' h_pc'
  · exact exc
  · exact ⟨h_pc.1, λ h => ⟨h_code h, rfl⟩⟩
  · exact h_pc

end ContractSpec

end Blanc
