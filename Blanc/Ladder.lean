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
-- `Postcond` / `State.Inv` bundles exactly; and `fmintSpec` in
-- `Blanc/Conserved.lean`, the ERC-3156 flash-mint contract of
-- `~/plans/flashmint-proposal.md`, whose twelve `FuncSound` obligations and
-- reverting fallback are all discharged there and assembled through
-- `ContractSpec.sound_of_dispatch` / `ContractSpec.preserves_inv` into
-- `fmint_preserves_conserved`.  (It was a statement-level instance only until
-- Arc B of that proposal closed; both instances now carry proofs.)

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

/-- Two storage maps that agree away from the address-shaped keys.

The complement of `Stor.rest`, which sees the address-shaped keys and nothing
else.  `Increase` / `Decrease` / `Transfer` say what a balance write does to the
keys Σ sums over; `AgreeOffAdr` is the other half of the same characterization —
that *nothing else* moved.  A contract whose invariant mentions a fixed
non-address slot needs both halves, and the ERC-20 writers supply both because
every key they write is address-shaped or explicitly guarded. -/
def Stor.AgreeOffAdr (s s' : Stor) : Prop :=
  ∀ k : B256, ¬ ValidAdr k → s.get k = s'.get k

theorem Stor.AgreeOffAdr.rfl {s : Stor} : Stor.AgreeOffAdr s s := fun _ _ => Eq.refl _

theorem Stor.AgreeOffAdr.of_eq {s s' : Stor} (h : s = s') : Stor.AgreeOffAdr s s' :=
  fun _ _ => congrFun (congrArg Stor.get h) _

theorem Stor.AgreeOffAdr.trans {s s' s'' : Stor}
    (h : Stor.AgreeOffAdr s s') (h' : Stor.AgreeOffAdr s' s'') : Stor.AgreeOffAdr s s'' :=
  fun k hk => (h k hk).trans (h' k hk)

/-- A write at an address-shaped key is invisible off the address-shaped keys. -/
theorem Stor.AgreeOffAdr.set {s : Stor} {k v : B256} (h : ValidAdr k) :
    Stor.AgreeOffAdr s (s.set k v) := by
  intro k' hk'
  refine (Stor.get_set_ne _ (fun hc => hk' ?_) _).symm
  exact hc ▸ h

/-- A single balance write that adds `v` at an address-shaped key, seen by
`Σ`'s domain: the `Increase` half of a mint's storage effect, in the exact
`set` form a walked `sstore` delivers. -/
lemma Stor.increase_set (s : Stor) (a : Adr) (v : B256) :
    Increase a v (Stor.rest s) (Stor.rest (s.set a.toB256 (v + s.get a.toB256))) := by
  intro b
  constructor
  · rintro rfl
    show s.get a.toB256 + v = (s.set a.toB256 _).get a.toB256
    rw [Stor.get_set_self, B256.add_comm]
  · intro hb
    show s.get b.toB256 = (s.set a.toB256 _).get b.toB256
    exact (Stor.get_set_ne _ (fun hc => hb (Adr.toB256_inj hc)) _).symm

/-- The `Decrease` half of a burn's storage effect, same form. -/
lemma Stor.decrease_set (s : Stor) (a : Adr) (v : B256) :
    Decrease a v (Stor.rest s) (Stor.rest (s.set a.toB256 (s.get a.toB256 - v))) := by
  intro b
  constructor
  · rintro rfl
    show s.get a.toB256 - v = (s.set a.toB256 _).get a.toB256
    rw [Stor.get_set_self]
  · intro hb
    show s.get b.toB256 = (s.set a.toB256 _).get b.toB256
    exact (Stor.get_set_ne _ (fun hc => hb (Adr.toB256_inj hc)) _).symm

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

section

open Jaune.Ninst Ninst

/-! ## The shared ERC-20 writers, and their effect on storage

Hoisted out of `Blanc/Solvent.lean` byte-identically with the rest of the
shared ERC-20 proof layer (`Blanc/CommonProofs.lean`, *The shared ERC-20 proof
layer*). These land here rather than there for two reasons, both about what is
defined below `CommonProofs` and above them: `incrAt_of_incrWbal`,
`of_transferFromUpdateSbal` and `transfer_of_transfer` are stated in terms of
the `Increase`/`Decrease`/`Transfer` algebra at the top of this module, and all
four need the `Linst.Hinv` instances immediately above to discharge their
`func_inv` side goals. Nothing in them mentions a contract.

Each of the three effect lemmas reports **both** halves of what its write does:
the `Increase`/`Decrease`/`Transfer` fact about the keys `Stor.rest` sums over,
and a `Stor.AgreeOffAdr` fact saying that nothing outside them moved.  A
solvency-style invariant needs only the first; an invariant that mentions a
fixed non-address slot — `Blanc/Conserved.lean`'s supply slot — needs the
second as well, and it is free here because every key these writers touch is
address-shaped by an already-discharged guard. -/

lemma transfer_preserves_bal : Func.Inv Devm.getBal Devm.getBal transfer := by func_inv

lemma incrAt_of_incrWbal {sevm : Sevm} {s s' : Devm} {wad dst} (h_dst : ValidAdr dst)
    (h_run : Line.Run sevm s incrWbal s') (h_stk : [wad, dst] <<+ s.stack) :
    Increase dst.toAdr wad (Stor.rest (Devm.getStor s sevm.currentTarget)) (Stor.rest (Devm.getStor s' sevm.currentTarget)) ∧
      Stor.AgreeOffAdr (Devm.getStor s sevm.currentTarget) (Devm.getStor s' sevm.currentTarget) := by
  simp only [incrWbal] at h_run
  rcases of_run_append [dup 1, sload, add, swap 0] h_run with ⟨sm, h_pre, h_post⟩
  clear h_run
  have h_stor : Devm.getStor s = Devm.getStor sm := Line.of_inv Devm.getStor (by line_inv) h_pre
  -- decompose the prefix line to track the stack
  rcases Line.of_run_cons h_pre with ⟨s1, r_dup, h1⟩
  rcases Line.of_run_cons h1 with ⟨s2, r_sload, h2⟩
  rcases Line.of_run_cons h2 with ⟨s3, r_add, h3⟩
  rcases Line.of_run_cons h3 with ⟨s4, r_swap, h4⟩
  cases h4
  clear h1 h2 h3 h_pre
  -- dup 1 : push element at index 1 (= dst)
  rcases of_run_dup r_dup with ⟨x, hx, pb_dup⟩
  have hx_dst : x = dst := by
    have h_nth : Stack.Nth 1 dst [wad, dst] :=
      Stack.Nth.tail 0 dst wad [dst] (Stack.Nth.head dst [])
    have h_get : s.stack[(1 : Fin 16).val]? = some dst := Stack.nth_getElem h_nth h_stk
    rw [h_get] at hx; injection hx with hx; exact hx.symm
  subst x
  have hp1 : [dst, wad, dst] <<+ s1.stack := prefix_of_push pb_dup h_stk
  -- sload : pop dst, push its stored value
  rcases prefix_of_sload r_sload hp1 with ⟨dbal, hp2, h_dbal⟩
  -- add : dbal + wad
  have hp3 : (dbal + wad) :: [dst] <<+ s3.stack := prefix_of_add r_add hp2
  -- swap 0 : [dst, dbal + wad]
  have h_swap : Stack.Swap (0 : Fin 16).val [dbal + wad, dst] [dst, dbal + wad] :=
    Stack.swapCore_zero
  have hp4 : [dst, dbal + wad] <<+ sm.stack :=
    Stack.prefix_of_swap h_swap (of_run_swap r_swap) hp3
  -- sstore
  rcases Line.of_run_cons h_post with ⟨s5, r_sstore, h5⟩
  cases h5
  have h_set : Devm.getStor s' sevm.currentTarget
      = (Devm.getStor sm sevm.currentTarget).set dst (dbal + wad) :=
    sstore_getStor_set r_sstore hp4
  -- dbal = value at dst in s's storage
  have hs1 : Devm.getStor s = Devm.getStor s1 :=
    Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r_dup Line.Run.nil)
  have h_dbal' : dbal = (Devm.getStor s sevm.currentTarget).get dst := by
    rw [h_dbal]; show (Devm.getStor s1 sevm.currentTarget).get dst = _; rw [hs1]
  -- assemble the Increase
  refine ⟨?_, ?_⟩
  · intro a
    constructor
    · intro h_eq
      subst h_eq
      simp only [Stor.rest, Function.comp_apply]
      rw [toB256_toAdr h_dst, h_set, Stor.get_set_self, ← h_dbal']
    · intro h_ne
      simp only [Stor.rest, Function.comp_apply]
      rw [h_set]
      have h_key_ne : a.toB256 ≠ dst := by
        intro hc; apply h_ne; rw [← toAdr_toB256 a, hc]
      rw [Stor.get_set_ne _ h_key_ne.symm, h_stor]
  -- and the half that says nothing off the address-shaped keys moved
  · rw [h_set, congr_fun h_stor sevm.currentTarget]
    exact Stor.AgreeOffAdr.set h_dst

lemma of_transferFromUpdateSbal {sevm : Sevm} {s₀ sₙ : Devm} {sbal wad src}
    (h_src : ValidAdr src) (h_sbal : sbal = (Devm.getStor s₀ sevm.currentTarget).get src)
    (h_le : wad ≤ sbal) (hp₀ : [sbal, wad, wad, src] <<+ s₀.stack) :
    Line.Run sevm s₀ transferFromUpdateSbal sₙ →
    ( Decrease src.toAdr wad (Stor.rest (Devm.getStor s₀ sevm.currentTarget)) (Stor.rest (Devm.getStor sₙ sevm.currentTarget)) ∧
      wad ≤ Stor.rest (Devm.getStor s₀ sevm.currentTarget) src.toAdr ∧
      Stor.AgreeOffAdr (Devm.getStor s₀ sevm.currentTarget) (Devm.getStor sₙ sevm.currentTarget) ) := by
  intro h_run
  simp only [transferFromUpdateSbal] at h_run
  rcases of_run_append [sub, dup 2] h_run with ⟨sm, h_pre, h_post⟩
  clear h_run
  have h_stor : Devm.getStor s₀ = Devm.getStor sm := Line.of_inv Devm.getStor (by line_inv) h_pre
  rcases Line.of_run_cons h_pre with ⟨s1, r_sub, h1⟩
  rcases Line.of_run_cons h1 with ⟨s2, r_dup, h2⟩
  cases h2
  clear h1 h_pre
  -- sub : [sbal - wad, wad, src]
  have hp1 : (sbal - wad) :: [wad, src] <<+ s1.stack := prefix_of_sub r_sub hp₀
  -- dup 2 : push element at index 2 (= src)
  rcases of_run_dup r_dup with ⟨x, hx, pb_dup⟩
  have hx_src : x = src := by
    have h_nth : Stack.Nth 2 src [sbal - wad, wad, src] :=
      Stack.Nth.tail 1 src (sbal - wad) [wad, src]
        (Stack.Nth.tail 0 src wad [src] (Stack.Nth.head src []))
    have h_get : s1.stack[(2 : Fin 16).val]? = some src := Stack.nth_getElem h_nth hp1
    rw [h_get] at hx; injection hx with hx; exact hx.symm
  subst x
  have hp2 : [src, sbal - wad, wad, src] <<+ sm.stack := prefix_of_push pb_dup hp1
  -- sstore
  rcases Line.of_run_cons h_post with ⟨s3, r_sstore, h3⟩
  cases h3
  have h_set : Devm.getStor sₙ sevm.currentTarget
      = (Devm.getStor sm sevm.currentTarget).set src (sbal - wad) :=
    sstore_getStor_set r_sstore hp2
  refine ⟨?_, ?_, ?_⟩
  · intro a
    constructor
    · intro h_eq
      subst h_eq
      simp only [Stor.rest, Function.comp_apply]
      rw [toB256_toAdr h_src, h_set, Stor.get_set_self, ← h_sbal]
    · intro h_ne
      simp only [Stor.rest, Function.comp_apply]
      rw [h_set]
      have h_key_ne : a.toB256 ≠ src := by
        intro hc; apply h_ne; rw [← toAdr_toB256 a, hc]
      rw [Stor.get_set_ne _ h_key_ne.symm, h_stor]
  · simp only [Stor.rest, Function.comp_apply]
    rw [toB256_toAdr h_src, ← h_sbal]; exact h_le
  -- the source write lands on an address-shaped key
  · rw [h_set, congr_fun h_stor sevm.currentTarget]
    exact Stor.AgreeOffAdr.set h_src

lemma transfer_of_transfer {fs : List Func} {sevm : Sevm} {s r : Devm} :
    Func.Run fs sevm s transfer r →
    (∃ (x : B256) (a a' : Adr),
      Transfer (Stor.rest (Devm.getStor s sevm.currentTarget)) a x a'
        (Stor.rest (Devm.getStor r sevm.currentTarget))) ∧
    Stor.AgreeOffAdr (Devm.getStor s sevm.currentTarget)
      (Devm.getStor r sevm.currentTarget) := by
  intro h_run
  simp only [transfer] at h_run
  -- transferTestDst : [dst_invalid?, dst]
  rcases of_run_prepend transferTestDst _ h_run with ⟨s1, h1, h_run⟩
  rcases of_transferTestDst h1 with ⟨dst_invalid, dst, hp1, h_dst⟩
  have hg1 : Devm.getStor s = Devm.getStor s1 := Line.of_inv Devm.getStor (by line_inv) h1
  clear h1
  -- rev-branch : dst is a valid address
  rcases of_run_branch_rev h_run with ⟨s2, hp2b, h_run⟩
  have hp2bs := hp2b.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp2bs
  rw [hp2bs] at hp1
  have h_dst_valid : ValidAdr dst := h_dst.mp (pref_head_unique hp1 (pref_append [0] s2.stack))
  rw [pref_head_unique hp1 (pref_append [0] s2.stack)] at hp1
  have hp2 : [dst] <<+ s2.stack := cons_pref_cons_inv hp1
  have hg2 : Devm.getStor s = Devm.getStor s2 :=
    hg1.trans (funext (fun a => (Devm.PopBurn.getStor hp2b a).symm))
  clear hp1 hp2bs hp2b h_dst
  -- transferTestLt : [lt?, caller, cbal - wad, wad, dst]
  rcases of_run_prepend transferTestLt _ h_run with ⟨s3, h3, h_run⟩
  rcases of_transferTestLt hp2 h3 with ⟨lt?, caller, wad, hp3, h_le, h_caller⟩
  have hg3 : Devm.getStor s = Devm.getStor s3 :=
    hg2.trans (Line.of_inv Devm.getStor (by line_inv) h3)
  clear h3 hp2
  -- rev-branch : wad ≤ caller balance
  rcases of_run_branch_rev h_run with ⟨s4, hp4b, h_run⟩
  have hp4bs := hp4b.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp4bs
  rw [hp4bs] at hp3
  have h_lt0 : lt? = 0 := pref_head_unique hp3 (pref_append [0] s4.stack)
  have h_le' : wad ≤ Devm.getStorVal s3 sevm.currentTarget caller := h_le.mp h_lt0
  rw [h_lt0] at hp3
  have hp4 : [caller, Devm.getStorVal s3 sevm.currentTarget caller - wad, wad, dst] <<+ s4.stack :=
    cons_pref_cons_inv hp3
  have hg4 : Devm.getStor s = Devm.getStor s4 :=
    hg3.trans (funext (fun a => (Devm.PopBurn.getStor hp4b a).symm))
  clear hp3 hp4bs hp4b h_le h_lt0
  -- transferCore : sstore ::: incrWbal +++ logTransfer +++ returnTrue
  simp only [transferCore] at h_run
  -- sstore : set caller's WETH balance to cbal - wad
  rcases of_run_next h_run with ⟨s5, r5, h_run⟩
  have h_set : Devm.getStor s5 sevm.currentTarget
      = (Devm.getStor s4 sevm.currentTarget).set caller
          (Devm.getStorVal s3 sevm.currentTarget caller - wad) :=
    sstore_getStor_set r5 hp4
  have hp5 : [wad, dst] <<+ s5.stack := prefix_of_sstore r5 hp4
  clear hp4
  -- incrWbal : increase destination balance
  rcases of_run_prepend incrWbal _ h_run with ⟨s6, h6, h_run⟩
  rcases incrAt_of_incrWbal h_dst_valid h6 hp5 with ⟨h_incr, h_off6⟩
  -- logTransfer, returnTrue : do not touch storage
  have h_rest : Devm.getStor s6 sevm.currentTarget = Devm.getStor r sevm.currentTarget :=
    congr_fun (Func.of_inv Devm.getStor Devm.getStor (by func_inv) h_run) sevm.currentTarget
  -- assemble the Transfer
  refine ⟨⟨wad, caller.toAdr, dst.toAdr, ?_,
    (Stor.rest (Devm.getStor s5 sevm.currentTarget)), ?_, ?_⟩, ?_⟩
  · show wad ≤ (Stor.rest (Devm.getStor s sevm.currentTarget)) caller.toAdr
    simp only [Stor.rest, Function.comp_apply]
    rw [toB256_toAdr h_caller, congr_fun hg3 sevm.currentTarget]
    exact h_le'
  · intro a
    constructor
    · intro h_eq; subst h_eq
      simp only [Stor.rest, Function.comp_apply]
      rw [toB256_toAdr h_caller, h_set, Stor.get_set_self, congr_fun hg3 sevm.currentTarget]
      rfl
    · intro h_ne
      simp only [Stor.rest, Function.comp_apply]
      rw [h_set]
      have h_key_ne : a.toB256 ≠ caller := by
        intro hc; apply h_ne; rw [← toAdr_toB256 a, hc]
      rw [Stor.get_set_ne _ h_key_ne.symm, congr_fun hg4 sevm.currentTarget]
  · rw [← h_rest]; exact h_incr
  -- both balance writes land on address-shaped keys, so nothing else moved
  · refine Stor.AgreeOffAdr.trans
      (Stor.AgreeOffAdr.of_eq (congr_fun hg4 sevm.currentTarget)) ?_
    refine Stor.AgreeOffAdr.trans ?_
      (h_off6.trans (Stor.AgreeOffAdr.of_eq h_rest))
    rw [h_set]
    exact Stor.AgreeOffAdr.set h_caller

end

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

/-- Resolving a delegation designator only records an access; it touches the
transient store no more than it touches the persistent one.  The
`transientStorage` companion of `accessDelegation_state`, needed by any caller
that wants the *world*, not just the state, carried across the `CALL`
step's delegation resolution. -/
lemma accessDelegation_transientStorage {devm : Devm} {adr : Adr} :
    (accessDelegation devm adr).2.2.2.2.transientStorage
      = devm.transientStorage := by
  dsimp only [accessDelegation]
  cases getDelegatedCodeAddress (devm.state.getCode adr) <;> rfl

lemma accessDelegation_stack {devm : Devm} {adr : Adr} :
    (accessDelegation devm adr).2.2.2.2.stack = devm.stack := by
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

lemma State.get_erase_ne {w : Jaune.State} {a b : Adr} (h : b ≠ a) :
    State.get (w.erase a) b = State.get w b := by
  unfold State.get
  have hc : compare a b ≠ Ordering.eq := fun hcc => h (compare_eq_iff_eq.mp hcc).symm
  rw [Std.TreeMap.getD_erase]; simp [hc]

-- `handleError` only returns a clean (`error = none`) devm when the underlying
-- execution itself returned `.ok`; the exceptional-halt / revert branches all
-- set the error flag, and the hard-error branch returns `.error`.
lemma exec_ok_of_handleError {exn : Execution} {evm' : Devm}
    (h : executeCode.handleError exn = .ok evm') (herr : ¬ evm'.error.isSome = true) :
    exn = .ok evm' := by
  cases exn with
  | error ee =>
    obtain ⟨err, d⟩ := ee
    rcases of_handleError_err h with ⟨evm2, h_ok, h_some, _⟩ | ⟨e2, h_e2⟩
    · rw [Except.ok.inj h_ok] at herr; exact absurd h_some herr
    · exact absurd h_e2 (by simp)
  | ok e =>
    simp only [executeCode.handleError] at h; rw [Except.ok.inj h]

/-! ## Frame rollback when no successful execution exists

These contract-neutral transport lemmas connect an `Exec`-level impossibility
to the enclosing message frame.  They name `msg`'s own frame, not the whole
transaction; they conclude only that an error is present, not which error; and
they remain partial-correctness statements because the settled run is a
hypothesis.  `h_fill` exposes the execution stored by `ProcessMessage`, while
`h_prec` excludes the precompile entry mode, which has no `Exec` for `h_none`
to contradict. -/

/-- A filled message frame with no successful interpreted execution settles
with an error and restores the frame's entry state and transient storage. -/
theorem rollback_of_no_success {msg : Msg} {benv : Benv} {xl : Xlot} {out : Devm}
    (h_pm : ProcessMessage msg xl (.ok out))
    (h_fill : Xlot.Filled xl)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles && decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_none : ∀ post, Exec 0 (initSevm (msg.withBenv benv))
        (initDevm (msg.withBenv benv)) (.ok post) → False) :
    out.error.isSome ∧
      out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage := by
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp h_pm
  unfold FrameBody at hbody
  rw [h_bt] at hbody
  rcases r0 with x | evm'
  · rw [processMessage.settle_error] at hset
    cases hset
  unfold processMessage.settle at hset
  dsimp only [bind, Except.bind] at hset
  by_cases herr : evm'.error.isSome = true
  · rw [if_pos herr] at hset
    have h_err : out.error.isSome = true := by rw [Except.ok.inj hset]; exact herr
    exact ⟨h_err, ProcessMessage.rollback_of_error h_pm h_err⟩
  · exfalso
    rw [if_neg herr] at hset
    have h_eq : evm' = out := Except.ok.inj hset.symm
    subst h_eq
    rcases h_ca : (msg.withBenv benv).codeAddress with _ | adr
    · obtain ⟨ex', h_xl, h_he⟩ := of_executeCode_noneCode h_ca hbody
      subst h_xl
      obtain ⟨exc⟩ := h_fill
      rw [exec_ok_of_handleError h_he herr] at exc
      exact h_none _ exc
    · rcases of_executeCode_someCode h_ca hbody with ⟨h_pre, -, -⟩ | ⟨-, ex', h_xl, h_he⟩
      · exact h_prec adr h_ca h_pre
      · subst h_xl
        obtain ⟨exc⟩ := h_fill
        rw [exec_ok_of_handleError h_he herr] at exc
        exact h_none _ exc

/-- Total-function form of `rollback_of_no_success`; the run equation supplies
both the execution slot and its `Xlot.Filled` witness. -/
theorem rollback_of_no_success_total {msg : Msg} {benv : Benv} {out : Devm}
    (h_run : processMessage msg = .ok out)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles && decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_none : ∀ post, Exec 0 (initSevm (msg.withBenv benv))
        (initDevm (msg.withBenv benv)) (.ok post) → False) :
    out.error.isSome ∧
      out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage := by
  obtain ⟨xl, h_fill, h_pm⟩ := of_processMessage msg (.ok out) h_run
  exact rollback_of_no_success h_pm h_fill h_bt h_prec h_none

lemma accessDelegation_memory {devm : Devm} {adr : Adr} :
    (accessDelegation devm adr).2.2.2.2.memory = devm.memory := by
  dsimp only [accessDelegation]
  cases getDelegatedCodeAddress (devm.state.getCode adr) <;> rfl

/-- Delegation resolution may warm an address, but it does not emit logs. -/
lemma accessDelegation_logs {devm : Devm} {adr : Adr} :
    (accessDelegation devm adr).2.2.2.2.logs = devm.logs := by
  dsimp only [accessDelegation]
  cases getDelegatedCodeAddress (devm.state.getCode adr) <;> rfl

/-- Delegation resolution does not change the enclosing frame's output. -/
lemma accessDelegation_output {devm : Devm} {adr : Adr} :
    (accessDelegation devm adr).2.2.2.2.output = devm.output := by
  dsimp only [accessDelegation]
  cases getDelegatedCodeAddress (devm.state.getCode adr) <;> rfl

/-- On the successful path the CALL-family return pushes `0` after a failed
child and `1` after a clean one; incorporating the child and the output write
leave the stack alone otherwise.  The flag-carrying refinement of
`Resume.call_stack`, for a caller whose next instructions branch on the call's
success. -/
lemma Resume.call_stack_flag {parent child : Devm} {oi os : Nat} {sf : Devm}
    (h : (Resume.call parent oi os).run (.ok child) = .ok sf) :
    sf.stack = (if child.error.isSome then (0 : B256) else 1) :: parent.stack := by
  have key : ∀ d : Devm, d.stack = parent.stack → ∀ v : B256,
      (Devm.push v d >>= fun d' =>
        (.ok (d'.memWrite oi (child.output.take os)) : Execution)) = .ok sf →
      sf.stack = v :: parent.stack := by
    intro d hd v hh
    rcases hp : Devm.push v d with e | evm2 <;> rw [hp] at hh
    · cases hh
    · injection hh with hh
      subst hh
      have h_push := (Devm.push_of_push hp).stack
      show evm2.stack = _
      rw [h_push, hd]
      rfl
  unfold Resume.run liftToExecution at h
  dsimp only [bind, Except.bind] at h
  split at h
  · rename_i herr
    rw [if_pos herr]
    exact key (incorporateChildOnError parent child child.output) rfl 0 h
  · rename_i herr
    rw [if_neg herr]
    exact key (incorporateChildOnSuccess parent child child.output) rfl 1 h

/-- The CALL-family return path hands the parent exactly the child's output as
its new returndata, on the failed and the clean path alike. -/
lemma Resume.call_returnData {parent child : Devm} {oi os : Nat} {sf : Devm}
    (h : (Resume.call parent oi os).run (.ok child) = .ok sf) :
    sf.returnData = child.output := by
  have key : ∀ d : Devm, d.returnData = child.output → ∀ v : B256,
      (Devm.push v d >>= fun d' =>
        (.ok (d'.memWrite oi (child.output.take os)) : Execution)) = .ok sf →
      sf.returnData = child.output := by
    intro d hd v hh
    rcases hp : Devm.push v d with e | evm2 <;> rw [hp] at hh
    · cases hh
    · injection hh with hh
      subst hh
      have h_push := (Devm.push_of_push hp).returnData
      show evm2.returnData = _
      rw [← h_push, hd]
  unfold Resume.run liftToExecution at h
  dsimp only [bind, Except.bind] at h
  split at h
  · exact key (incorporateChildOnError parent child child.output) rfl 0 h
  · exact key (incorporateChildOnSuccess parent child child.output) rfl 1 h

/-- The CALL-family return path leaves the parent's memory as it was, plus the
output write at the requested window. -/
lemma Resume.call_memory {parent child : Devm} {oi os : Nat} {sf : Devm}
    (h : (Resume.call parent oi os).run (.ok child) = .ok sf) :
    sf.memory = parent.memory.write oi (child.output.take os) := by
  have key : ∀ d : Devm, d.memory = parent.memory → ∀ v : B256,
      (Devm.push v d >>= fun d' =>
        (.ok (d'.memWrite oi (child.output.take os)) : Execution)) = .ok sf →
      sf.memory = parent.memory.write oi (child.output.take os) := by
    intro d hd v hh
    rcases hp : Devm.push v d with e | evm2 <;> rw [hp] at hh
    · cases hh
    · injection hh with hh
      subst hh
      have h_push := (Devm.push_of_push hp).memory
      show evm2.memory.write oi (child.output.take os) = _
      rw [← h_push, hd]
  unfold Resume.run liftToExecution at h
  dsimp only [bind, Except.bind] at h
  split at h
  · exact key (incorporateChildOnError parent child child.output) rfl 0 h
  · exact key (incorporateChildOnSuccess parent child child.output) rfl 1 h

/-- The CALL-family return path never changes the parent's enclosing output
field.  Child returndata is installed in `returnData` and copied to memory;
the outer frame's own output remains untouched. -/
lemma Resume.call_output {parent child : Devm} {oi os : Nat} {sf : Devm}
    (h : (Resume.call parent oi os).run (.ok child) = .ok sf) :
    sf.output = parent.output := by
  have key : ∀ d : Devm, d.output = parent.output → ∀ v : B256,
      (Devm.push v d >>= fun d' =>
        (.ok (d'.memWrite oi (child.output.take os)) : Execution)) = .ok sf →
      sf.output = parent.output := by
    intro d hd v hh
    rcases hp : Devm.push v d with e | evm2 <;> rw [hp] at hh
    · cases hh
    · injection hh with hh
      subst hh
      have h_push := (Devm.push_of_push hp).output
      change evm2.output = parent.output
      rw [← h_push, hd]
  unfold Resume.run liftToExecution at h
  dsimp only [bind, Except.bind] at h
  split at h
  · exact key (incorporateChildOnError parent child child.output) rfl 0 h
  · exact key (incorporateChildOnSuccess parent child child.output) rfl 1 h

/-- Exact CALL-family log incorporation.  An errored child contributes no
logs; a clean child appends its log list to the parent's. -/
lemma Resume.call_logs {parent child : Devm} {oi os : Nat} {sf : Devm}
    (h : (Resume.call parent oi os).run (.ok child) = .ok sf) :
    sf.logs = if child.error.isSome then parent.logs
      else parent.logs ++ child.logs := by
  have key : ∀ d : Devm,
      d.logs = (if child.error.isSome then parent.logs
        else parent.logs ++ child.logs) → ∀ v : B256,
      (Devm.push v d >>= fun d' =>
        (.ok (d'.memWrite oi (child.output.take os)) : Execution)) = .ok sf →
      sf.logs = if child.error.isSome then parent.logs
        else parent.logs ++ child.logs := by
    intro d hd v hh
    rcases hp : Devm.push v d with e | evm2 <;> rw [hp] at hh
    · cases hh
    · injection hh with hh
      subst hh
      have h_push := (Devm.push_of_push hp).logs
      change evm2.logs = if child.error.isSome then parent.logs
        else parent.logs ++ child.logs
      rw [← h_push, hd]
  unfold Resume.run liftToExecution at h
  dsimp only [bind, Except.bind] at h
  by_cases herr : child.error.isSome
  · rw [if_pos herr] at h ⊢
    simpa [if_pos herr] using
      key (incorporateChildOnError parent child child.output)
        (by rw [if_pos herr]; rfl) 0 h
  · rw [if_neg herr] at h ⊢
    simpa [if_neg herr] using
      key (incorporateChildOnSuccess parent child child.output)
        (by rw [if_neg herr]; rfl) 1 h

/-- The `transientStorage` companion of `Resume.call_state`: on both settled
paths the CALL-family return installs the child's transient store alongside
its state, and neither the status push nor the output write touches it.

Both `incorporateChildOnError` and `incorporateChildOnSuccess` set
`transientStorage := child.transientStorage`, so the two arms are the same
argument, exactly as in `Resume.call_state`. -/
lemma Resume.call_transientStorage {parent child : Devm} {oi os : Nat}
    {sf : Devm} (h : (Resume.call parent oi os).run (.ok child) = .ok sf) :
    sf.transientStorage = child.transientStorage := by
  have key : ∀ d : Devm, d.transientStorage = child.transientStorage →
      ∀ v : B256,
      (Devm.push v d >>= fun d' =>
        (.ok (d'.memWrite oi (child.output.take os)) : Execution)) = .ok sf →
      sf.transientStorage = child.transientStorage := by
    intro d hd v hh
    rcases hp : Devm.push v d with e | evm2 <;> rw [hp] at hh
    · cases hh
    · injection hh with hh
      subst hh
      have h_push := (Devm.push_of_push hp).transientStorage
      show (evm2.memWrite oi (child.output.take os)).transientStorage = _
      rw [← (Devm.memWrite_instructionFrame evm2 oi
        (child.output.take os)).transientStorage, ← h_push, hd]
  unfold Resume.run liftToExecution at h
  dsimp only [bind, Except.bind] at h
  split at h
  · exact key (incorporateChildOnError parent child child.output) rfl 0 h
  · exact key (incorporateChildOnSuccess parent child child.output) rfl 1 h

/-- A gas charge that returned `.ok` was affordable. -/
lemma chargeGas_le {cost : Nat} {devm devm' : Devm}
    (h : chargeGas cost devm = .ok devm') : cost ≤ devm.gasLeft := by
  rw [chargeGas_def] at h
  split at h
  · cases h
  · rename_i gas heq
    unfold safeSub at heq
    by_cases hc : cost ≤ devm.gasLeft
    · exact hc
    · rw [if_neg hc] at heq
      cases heq

/-- When the CALL-family gas charge went through, the stipend the child was
granted is EIP-150's: the minimum of the request and the 63/64 remainder of
what the caller had, plus the value stipend.  The other `calculateMsgCallGas`
branch quotes a cost the charge cannot afford, so it never coexists with a
successful charge. -/
lemma calculateMsgCallGas_stipend {value gas gasLeft mem extra : Nat}
    (h : (calculateMsgCallGas value gas gasLeft mem extra).1 + mem ≤ gasLeft) :
    ∃ avail, (calculateMsgCallGas value gas gasLeft mem extra).2
      = min gas (except64th avail) + (if value = 0 then 0 else gCallStipend) := by
  unfold calculateMsgCallGas at h ⊢
  by_cases hlow : gasLeft < extra + mem
  · rw [if_pos hlow] at h
    dsimp only [] at h
    omega
  · rw [if_neg hlow]
    exact ⟨gasLeft - mem - extra, rfl⟩

/-- **The value-carrying `KECCAK256` inversion.**  `kec` pushes the hash of
*the memory window its two operands name* — the fact `of_run_kec` forgets.

A caller holding a `Mem.Reads` image rewrites the `Mem.read` with
`Mem.Reads.read` and learns which bytes the hash is taken of, which is what
turns "some hash" into "the allowance key of this pair of addresses".

Placed here rather than beside `of_run_kec` in `Blanc/CommonProofs.lean` for
the same reason `of_run_call_val` is: the shared module is against this arc's
predeclared elaboration falsifier with little margin, and this module has
headroom.

Like `LOG`, `KECCAK256` only *extends* memory — it reads a window and hashes
it — so the second conjunct is what carries a `Mem.Wf`/`Mem.Reads` pair across
it. -/
lemma of_run_kec_val {e : Sevm} {s s' : Devm} (h : Ninst.Run e s Ninst.kec s') :
    ∃ x y, Stack.Diff [x, y] [(s.memory.read x.toNat y.toNat).1.keccak]
      s.stack s'.stack ∧ s'.memory = s.memory.extend x.toNat y.toNat := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨s₃, h3, run₃⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  rcases Devm.pop_of_popToNat_val h2 with ⟨y, p2, rfl⟩
  have hb := Devm.burn_of_chargeGas h3
  have hmem : s.memory = s₃.memory := (p1.memory.trans p2.memory).trans hb.memory
  have hpush : Devm.Push [(s₃.memRead x.toNat y.toNat).1.keccak]
      (s₃.memRead x.toNat y.toNat).2 s' := Devm.push_of_push run₃
  have hval : (s.memory.read x.toNat y.toNat).1.keccak
      = (s₃.memRead x.toNat y.toNat).1.keccak := by rw [hmem]; rfl
  refine ⟨x, y, ⟨s₂.stack, (Devm.pop_append p1 p2).stack, ?_⟩, ?_⟩
  · rw [hval, show s₂.stack = s₃.stack from hb.stack,
      ← Devm.memRead_stack s₃ x.toNat y.toNat]
    exact hpush.stack
  · rw [← hpush.memory,
      show (s₃.memRead x.toNat y.toNat).2.memory = s₃.memory.extend x.toNat y.toNat
        from rfl, hmem]

/-- `prefix_of_kec`, with the hashed window named and the memory extension
recorded. -/
lemma prefix_of_kec_val {e} {x y xs} {s s' : Devm}
    (h : Ninst.Run e s Ninst.kec s') (hp : x :: y :: xs <<+ s.stack) :
    ((s.memory.read x.toNat y.toNat).1.keccak :: xs <<+ s'.stack) ∧
      s'.memory = s.memory.extend x.toNat y.toNat := by
  rcases of_run_kec_val h with ⟨x', y', ⟨stk, h2, h3⟩, hm⟩
  rcases of_cons_cons_pref_of_cons_cons_pref hp (pref_of_split h2) with ⟨hx, hy, -⟩
  rw [hx, hy] at hp ⊢
  exact ⟨append_pref h3 (of_append_pref h2 hp), hm⟩

/-- **What a `RETURN` returns.**  `Linst.run .ret` pops the window, charges for
it and sets `Devm.output` from *memory* — so a `Func` ending in `Func.ret` is
specified by an equation about `Devm.output`, never about a stack word, and a
caller holding a `Mem.Reads` image reads the returned bytes off it.

Same placement note as the two inversions above. -/
lemma of_run_ret_val {fs : List Func} {sevm : Sevm} {s r : Devm} {i n : B256} {xs}
    (hp : i :: n :: xs <<+ s.stack) (h : Func.Run fs sevm s Func.ret r) :
    Devm.output r = (s.memory.read i.toNat n.toNat).1 ∧
      Devm.getCode s = Devm.getCode r := by
  cases h with
  | last hl =>
    refine ⟨?_, funext (fun x => (Linst.run_codeFrame hl x).symm)⟩
    simp only [Linst.Run, Linst.run] at hl
    rcases Except.bind_eq_ok hl with ⟨⟨idx, s₁⟩, h1, run₁⟩
    rcases Except.bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
    rcases Except.bind_eq_ok run₂ with ⟨s₃, h3, run₃⟩
    rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
    rcases Devm.pop_of_popToNat_val h2 with ⟨y, p2, rfl⟩
    have hb := Devm.burn_of_chargeGas h3
    have hmem : s.memory = s₃.memory := (p1.memory.trans p2.memory).trans hb.memory
    have hstk : s.stack = x :: y :: s₂.stack := by
      have hpp := (Devm.pop_append p1 p2).stack
      simpa only [Stack.Pop, Split, List.cons_append, List.nil_append] using hpp
    rw [hstk] at hp
    have hx : i = x := pref_head_unique hp (pref_append [x] (y :: s₂.stack))
    subst hx
    have hy : n = y := pref_head_unique (cons_pref_cons_inv hp) (pref_append [y] s₂.stack)
    subst hy
    injection run₃ with hr
    rw [← hr, hmem]
    rfl

/-! ### Shared ABI-true return observation -/

/-- A frame returned canonical ABI `true`: one complete word containing `1`. -/
def AbiReturnsTrue (d : Devm) : Prop :=
  Devm.output d = (1 : B256).toBytes

/-- `returnTrue` writes `1` to memory word zero and returns that complete word.
The memory image on entry is arbitrary because the write covers the returned
window. -/
lemma of_returnTrue_shared {fs : List Func} {sevm : Sevm} {s r : Devm}
    {img : Bytes} {xs}
    (hp : xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (h : Func.Run fs sevm s returnTrue r) :
    AbiReturnsTrue r ∧ Devm.getCode s = Devm.getCode r := by
  simp only [returnTrue] at h
  rcases of_run_next h with ⟨s1, r1, h⟩
  have hp1 : (1 : B256) :: xs <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 r1) hp
  have hm1 : s.memory = s1.memory :=
    Ninst.Hinv.inv (f := Devm.memory) r1
  rcases of_run_prepend (mstoreAt 0) _ h with ⟨s2, h2, h⟩
  rcases of_run_mstoreAt_val h2 hp1 with ⟨hp2, hm2⟩
  have hwf2 : Mem.Wf s2.memory := by
    rw [hm2, ← hm1]
    exact h_wf.write _ _
  have hrd2 :
      Mem.Reads s2.memory (Bytes.writeAt img 0 (1 : B256).toBytes) := by
    rw [hm2, ← hm1]
    exact Mem.Reads.write h_wf h_reads 0 _
  rcases of_run_prepend (pushList [32, 0]) _ h with ⟨s3, h3, h⟩
  rcases Line.of_run_cons h3 with ⟨u1, q1, h3'⟩
  rcases Line.of_run_cons h3' with ⟨u2, q2, hnil⟩
  cases hnil
  have hu1 : (32 : B256) :: xs <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp2
  have hu2 : (0 : B256) :: (32 : B256) :: xs <<+ s3.stack :=
    prefix_of_push (of_run_pushB256 q2) hu1
  have hm3 : s2.memory = s3.memory :=
    Line.of_inv Devm.memory (by line_inv) h3
  have hgc : Devm.getCode s = Devm.getCode s3 :=
    ((Ninst.Hinv.inv (f := Devm.getCode) r1).trans
      (Line.of_inv Devm.getCode (by line_inv) h2)).trans
      (Line.of_inv Devm.getCode (by line_inv) h3)
  refine ⟨?_, hgc.trans (of_run_ret_val hu2 h).2⟩
  show Devm.output r = _
  rw [(of_run_ret_val hu2 h).1,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    Mem.Reads.read (hm3 ▸ hrd2) 0 32,
    show (32 : Nat) = (1 : B256).toBytes.length from
      (B256.length_toBytes 1).symm,
    Bytes.sliceD_writeAt]

/-- **The value-carrying `CALL` inversion.**  A successful `call` step whose
seven operands are known either pushed the failure flag `0` — the depth guard,
the balance guard, or a child frame that failed, rollback included — **and left
the caller's world exactly as it found it** — or spawned a child frame whose
message is pinned field by field, and resumed from exactly that child with the
flag `1`.

**What the first disjunct pins, and whose frame it names.**  Beside the pushed
flag it now carries `Devm.WorldEq s sf`: the *caller's* state and transient
storage at resumption are the ones it entered the `CALL` with.  This is a
frame-level statement about `s`, the caller, and it says nothing whatever about
the transaction: a caller that catches this failure may go on to succeed, and a
caller that does not may revert its own frame afterwards for its own reasons.
It also names no error kind — the three branches that reach it are the balance
guard, the depth guard and a child frame that settled with *some* error, and
which one occurred is deliberately not recoverable from the conclusion.  In the
third branch the world equation is the child frame's rollback
(`ProcessMessage.rollback_of_error`) composed with the resumption's world
installation; in the first two no frame ever opened, so nothing could have been
written.

Nothing here asserts that a `CALL` ever fails: the disjunct is reached only
from a hypothesised run.

What the second disjunct pins, clause by clause: `parent` is the caller's own
frame after the seven pops, with its stack residue, state and memory image
intact; the callee is the popped word's 160-bit truncation; the calldata is
the caller's memory window at the popped offsets, phrased as `Mem.read` so a
caller holding a `Mem.Reads` image can rewrite it; the value is the popped
word, and the gas is EIP-150's grant — `min` of the request and the 63/64
remainder, never "all gas"; the code is the callee account's own unless that
account is an EIP-7702 delegation designator, in which case it is the
designated account's — the delegation case is *covered*, not excluded; the
child ran to a settled result with no error, which excludes the in-frame
rollback; and `sf` is the resumption from exactly that child.

The statement is a disjunction rather than a postcondition because a `CALL`
that never entered a frame also returns `.ok`: Blanc's compiled callers branch
on the pushed flag, so a caller holding the success guard dismisses the first
disjunct with it. -/
lemma of_run_call_val_with_depth_frame
    {sevm : Sevm} {s sf : Devm} {g c v ii is oi os : B256}
    {xs : Stack}
    (hp : (g :: c :: v :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_run : Ninst.Run sevm s Ninst.call sf) :
    (((0 : B256) :: xs <<+ sf.stack) ∧ Devm.WorldEq s sf) ∨
    ∃ (parent child : Devm) (xl : Xlot) (dp : Bool) (code : ByteArray)
      (avail pc : Nat),
      Ninst.StepRun pc sevm s Ninst.call xl (.ok sf) ∧
      0 < sevm.depth ∧
      s.stack = g :: c :: v :: ii :: is :: oi :: os :: parent.stack ∧
      parent.state = s.state ∧
      parent.memory
        = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] ∧
      parent.logs = s.logs ∧
      parent.output = s.output ∧
      ((getDelegatedCodeAddress (s.getCode c.toAdr) = none ∧
          code = s.getCode c.toAdr ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (s.getCode c.toAdr) = some d ∧
          code = s.getCode d ∧ dp = true)) ∧
      Xlot.Filled xl ∧
      ProcessMessage
        (callMsg sevm parent
          (min g.toNat (except64th avail)
            + (if v.toNat = 0 then 0 else gCallStipend))
          v sevm.currentTarget c.toAdr c.toAdr true false
          ((s.memory.read ii.toNat is.toNat).1) code dp)
        xl (.ok child) ∧
      child.error.isSome = false ∧
      (Resume.call parent oi.toNat os.toNat).run (.ok child) = .ok sf ∧
      sf.state = child.state ∧
      sf.returnData = child.output ∧
      sf.memory = parent.memory.write oi.toNat (child.output.take os.toNat) ∧
      sf.stack = (1 : B256) :: parent.stack := by
  rcases h_run with ⟨xl, h_fill, pc, h_run⟩
  have h_step : Ninst.StepRun pc sevm s Ninst.call xl (.ok sf) := h_run
  simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step,
    Bind.bind, Except.bind, Except.assert] at h_run
  -- pop gas
  rcases eq1 : Devm.pop s with _ | ⟨gas1, devm1⟩ <;> simp only [eq1] at h_run
  · cases XStep.run_ofExcept_error h_run
  have f1 := Devm.pop_of_pop eq1
  have e1 := f1.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1
  rw [e1] at hp
  have hv1 : g = gas1 := pref_head_unique hp (pref_append [gas1] devm1.stack)
  subst hv1
  replace hp := cons_pref_cons_inv hp
  -- pop callee
  rcases eq2 : Devm.popToAdr devm1 with _ | ⟨callee, devm2⟩ <;>
    simp only [eq2] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToAdr eq2 with ⟨x2, hx2, h_pop2⟩
  have f2 := Devm.pop_of_pop h_pop2
  have e2 := f2.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e2
  rw [e2] at hp
  have hv2 : c = x2 := pref_head_unique hp (pref_append [x2] devm2.stack)
  subst hv2
  subst hx2
  replace hp := cons_pref_cons_inv hp
  -- pop value
  rcases eq3 : Devm.pop devm2 with _ | ⟨value, devm3⟩ <;> simp only [eq3] at h_run
  · cases XStep.run_ofExcept_error h_run
  have f3 := Devm.pop_of_pop eq3
  have e3 := f3.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e3
  rw [e3] at hp
  have hv3 : v = value := pref_head_unique hp (pref_append [value] devm3.stack)
  subst hv3
  replace hp := cons_pref_cons_inv hp
  -- pop the four indices/sizes, keeping each popped word's `toNat`
  rcases eq4 : Devm.popToNat devm3 with _ | ⟨inputIndex, devm4⟩ <;>
    simp only [eq4] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat_val eq4 with ⟨x4, f4, hk4⟩
  have e4 := f4.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e4
  rw [e4] at hp
  have hv4 : ii = x4 := pref_head_unique hp (pref_append [x4] devm4.stack)
  subst hv4
  subst hk4
  replace hp := cons_pref_cons_inv hp
  rcases eq5 : Devm.popToNat devm4 with _ | ⟨inputSize, devm5⟩ <;>
    simp only [eq5] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat_val eq5 with ⟨x5, f5, hk5⟩
  have e5 := f5.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e5
  rw [e5] at hp
  have hv5 : is = x5 := pref_head_unique hp (pref_append [x5] devm5.stack)
  subst hv5
  subst hk5
  replace hp := cons_pref_cons_inv hp
  rcases eq6 : Devm.popToNat devm5 with _ | ⟨outputIndex, devm6⟩ <;>
    simp only [eq6] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat_val eq6 with ⟨x6, f6, hk6⟩
  have e6 := f6.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e6
  rw [e6] at hp
  have hv6 : oi = x6 := pref_head_unique hp (pref_append [x6] devm6.stack)
  subst hv6
  subst hk6
  replace hp := cons_pref_cons_inv hp
  rcases eq7 : Devm.popToNat devm6 with _ | ⟨outputSize, devm7⟩ <;>
    simp only [eq7] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat_val eq7 with ⟨x7, f7, hk7⟩
  have e7 := f7.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e7
  rw [e7] at hp
  have hv7 : os = x7 := pref_head_unique hp (pref_append [x7] devm7.stack)
  subst hv7
  subst hk7
  replace hp := cons_pref_cons_inv hp
  -- the seven pops: exact stack decomposition, state and memory carried
  have e_stack : s.stack
      = g :: c :: v :: ii :: is :: oi :: os :: devm7.stack := by
    rw [e1, e2, e3, e4, e5, e6, e7]
  have h_st7 : s.state = devm7.state :=
    (f1.state).trans ((f2.state).trans ((f3.state).trans ((f4.state).trans
      ((f5.state).trans ((f6.state).trans f7.state)))))
  have h_mem7 : s.memory = devm7.memory :=
    (f1.memory).trans ((f2.memory).trans ((f3.memory).trans ((f4.memory).trans
      ((f5.memory).trans ((f6.memory).trans f7.memory)))))
  have h_tra7 : s.transientStorage = devm7.transientStorage :=
    (f1.transientStorage).trans ((f2.transientStorage).trans
      ((f3.transientStorage).trans ((f4.transientStorage).trans
        ((f5.transientStorage).trans
          ((f6.transientStorage).trans f7.transientStorage)))))
  have h_logs7 : s.logs = devm7.logs :=
    (f1.logs).trans ((f2.logs).trans ((f3.logs).trans
      ((f4.logs).trans ((f5.logs).trans ((f6.logs).trans f7.logs)))))
  have h_output7 : s.output = devm7.output :=
    (f1.output).trans ((f2.output).trans ((f3.output).trans
      ((f4.output).trans ((f5.output).trans ((f6.output).trans f7.output)))))
  clear e1 e2 e3 e4 e5 e6 e7 f1 f2 f3 f4 f5 f6 f7
  clear eq1 eq2 eq3 eq4 eq5 eq6 eq7 h_pop2
  -- delegation resolution
  rcases hp11 : accessDelegation (addAccessedAddress devm7 c.toAdr) c.toAdr with
    ⟨dp, na, code0, dagc, devm9⟩
  simp only [hp11] at h_run
  have h_st9 : devm9.state = devm7.state := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).state) hp11
    dsimp at h
    rw [← h, accessDelegation_state]
    rfl
  have h_stk9 : devm9.stack = devm7.stack := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).stack) hp11
    dsimp at h
    rw [← h, accessDelegation_stack]
    rfl
  have h_mem9 : devm9.memory = devm7.memory := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).memory) hp11
    dsimp at h
    rw [← h, accessDelegation_memory]
    rfl
  have h_tra9 : devm9.transientStorage = devm7.transientStorage := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).transientStorage) hp11
    dsimp at h
    rw [← h, accessDelegation_transientStorage]
    rfl
  have h_logs9 : devm9.logs = devm7.logs := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).logs) hp11
    dsimp at h
    rw [← h, accessDelegation_logs]
    rfl
  have h_output9 : devm9.output = devm7.output := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).output) hp11
    dsimp at h
    rw [← h, accessDelegation_output]
    rfl
  -- the code the child will run, and the delegation disjunction
  have h_gc7 : (addAccessedAddress devm7 c.toAdr).state.getCode c.toAdr
      = s.getCode c.toAdr := by
    show devm7.state.getCode c.toAdr = s.getCode c.toAdr
    rw [← h_st7]
    rfl
  have h_del :
      (getDelegatedCodeAddress (s.getCode c.toAdr) = none ∧
        code0 = s.getCode c.toAdr ∧ dp = false) ∨
      (∃ d, getDelegatedCodeAddress (s.getCode c.toAdr) = some d ∧
        code0 = s.getCode d ∧ dp = true) := by
    have h_acc := hp11
    dsimp only [accessDelegation] at h_acc
    rw [h_gc7] at h_acc
    rcases hdel : getDelegatedCodeAddress (s.getCode c.toAdr) with _ | d <;>
      rw [hdel] at h_acc <;>
      simp only [Prod.mk.injEq] at h_acc
    · exact Or.inl ⟨rfl, h_acc.2.2.1.symm, h_acc.1.symm⟩
    · refine Or.inr ⟨d, rfl, ?_, h_acc.1.symm⟩
      rw [← h_acc.2.2.1]
      show (addAccessedAddress devm7 c.toAdr).state.getCode d = s.getCode d
      show devm7.state.getCode d = s.getCode d
      rw [← h_st7]
      rfl
  -- charge the call gas
  split at h_run
  · cases XStep.run_ofExcept_error h_run
  rename_i devm10 eq16
  have h_st10 : devm9.state = devm10.state := (Devm.burn_of_chargeGas eq16).state
  have h_stk10 : devm9.stack = devm10.stack := (Devm.burn_of_chargeGas eq16).stack
  have h_mem10 : devm9.memory = devm10.memory := (Devm.burn_of_chargeGas eq16).memory
  have h_tra10 : devm9.transientStorage = devm10.transientStorage :=
    (Devm.burn_of_chargeGas eq16).transientStorage
  have h_logs10 : devm9.logs = devm10.logs :=
    (Devm.burn_of_chargeGas eq16).logs
  have h_output10 : devm9.output = devm10.output :=
    (Devm.burn_of_chargeGas eq16).output
  -- static-context assertion
  split at h_run
  case h_1 => cases XStep.run_ofExcept_error h_run
  case h_2 =>
  split at h_run
  · -- insufficient balance : the failure flag is pushed, no frame opens
    split at h_run
    case h_1 => cases XStep.run_ofExcept_error h_run
    case h_2 =>
    rename_i devm12 eq20
    left
    have h_ex := Except.ok.inj h_run.2
    rw [h_ex]
    have h_stk := (Devm.push_of_push eq20).stack
    refine ⟨?_, ?_, ?_⟩
    · show ((0 : B256) :: xs)
        <<+ ((devm12.withReturnData []).withGasLeft _).stack
      show ((0 : B256) :: xs) <<+ devm12.stack
      rw [h_stk]
      show ((0 : B256) :: xs) <<+ (0 : B256) ::
        (devm10.memExtends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).stack
      have h_stk11 :
          (devm10.memExtends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).stack
            = devm7.stack := by
        show devm10.stack = devm7.stack
        rw [← h_stk10, h_stk9]
      rw [h_stk11]
      exact pref_cons hp
    · -- no frame opened, so the state is the caller's own, seven pops later
      show s.state = ((devm12.withReturnData []).withGasLeft _).state
      show s.state = devm12.state
      rw [← (Devm.push_of_push eq20).state]
      show s.state = devm10.state
      rw [← h_st10, h_st9, ← h_st7]
    · -- and likewise the transient store
      show s.transientStorage
        = ((devm12.withReturnData []).withGasLeft _).transientStorage
      show s.transientStorage = devm12.transientStorage
      rw [← (Devm.push_of_push eq20).transientStorage]
      show s.transientStorage = devm10.transientStorage
      rw [← h_tra10, h_tra9, ← h_tra7]
  · -- balance is sufficient : the call goes through
    simp only [genericCall.step] at h_run
    split at h_run
    · -- depth limit reached : the failure flag is pushed, no frame opens
      simp only [Bind.bind, Except.bind] at h_run
      split at h_run
      case h_1 => cases XStep.run_ofExcept_error h_run
      case h_2 =>
      rename_i devm12 h_push
      left
      have h_ex := Except.ok.inj h_run.2
      rw [h_ex]
      have h_stk := (Devm.push_of_push h_push).stack
      refine ⟨?_, ?_, ?_⟩
      · show ((0 : B256) :: xs) <<+ devm12.stack
        rw [h_stk]
        show ((0 : B256) :: xs) <<+ (0 : B256) ::
          ((devm10.memExtends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData
            []).stack
        show ((0 : B256) :: xs) <<+ (0 : B256) ::
          (devm10.memExtends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).stack
        have h_stk11 :
            (devm10.memExtends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).stack
              = devm7.stack := by
          show devm10.stack = devm7.stack
          rw [← h_stk10, h_stk9]
        rw [h_stk11]
        exact pref_cons hp
      · -- the depth guard opened no frame either
        show s.state = devm12.state
        rw [← (Devm.push_of_push h_push).state]
        show s.state = devm10.state
        rw [← h_st10, h_st9, ← h_st7]
      · show s.transientStorage = devm12.transientStorage
        rw [← (Devm.push_of_push h_push).transientStorage]
        show s.transientStorage = devm10.transientStorage
        rw [← h_tra10, h_tra9, ← h_tra7]
    · -- the call is executed
      rename_i h_depth_ne
      simp only [XStep.Run] at h_run
      rcases h_run with ⟨ex', run_pm₀, h_split⟩
      rcases ex' with err' | child
      · cases Resume.call_run_error h_split.symm
      -- the parent-side residue
      have h_stk_par :
          ((devm10.memExtends
            [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData []).stack
            = devm7.stack := by
        show devm10.stack = devm7.stack
        rw [← h_stk10, h_stk9]
      have h_st_par :
          ((devm10.memExtends
            [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData
            []).state = s.state := by
        show devm10.state = s.state
        rw [← h_st10, h_st9, ← h_st7]
      have h_tra_par :
          ((devm10.memExtends
            [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData
            []).transientStorage = s.transientStorage := by
        show devm10.transientStorage = s.transientStorage
        rw [← h_tra10, h_tra9, ← h_tra7]
      by_cases herr : child.error.isSome
      · -- the child failed : the failure flag is pushed on resumption, and the
        -- child frame's own rollback has already undone everything it wrote
        left
        have h_roll : Devm.WorldEq child
            ((devm10.memExtends
              [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData []) :=
          ProcessMessage.rollback_of_error run_pm₀ herr
        refine ⟨?_, ?_, ?_⟩
        · have hsf := Resume.call_stack_flag h_split.symm
          rw [if_pos herr] at hsf
          rw [hsf, h_stk_par]
          exact pref_cons hp
        · rw [Resume.call_state h_split.symm, h_roll.1, h_st_par]
        · rw [Resume.call_transientStorage h_split.symm, h_roll.2, h_tra_par]
      · -- the child succeeded : the boundary holds
        right
        have h_mem_par :
            ((devm10.memExtends
              [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData
              []).memory
              = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] := by
          show (devm10.memory).extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]
            = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]
          rw [← h_mem10, h_mem9, ← h_mem7]
        have h_logs_par :
            ((devm10.memExtends
              [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData
              []).logs = s.logs := by
          show devm10.logs = s.logs
          rw [← h_logs10, h_logs9, ← h_logs7]
        have h_output_par :
            ((devm10.memExtends
              [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData
              []).output = s.output := by
          show devm10.output = s.output
          rw [← h_output10, h_output9, ← h_output7]
        -- EIP-150 : the charge went through, so the stipend took the 63/64 form
        obtain ⟨avail, hstip⟩ := calculateMsgCallGas_stipend (chargeGas_le eq16)
        rw [hstip] at run_pm₀
        -- the calldata is the caller's memory window
        have h_cd : Array.sliceD
            ((devm10.memExtends
              [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData
              []).memory.data ii.toNat is.toNat 0
            = (s.memory.read ii.toNat is.toNat).1 := by
          rw [h_mem_par]
          rfl
        rw [h_cd] at run_pm₀
        refine ⟨(devm10.memExtends
            [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData [],
          child, xl, dp, code0, avail, pc, h_step,
          by omega, by rw [e_stack, h_stk_par], h_st_par, h_mem_par,
          h_logs_par, h_output_par, h_del, h_fill,
          run_pm₀, by simpa using herr, h_split.symm,
          Resume.call_state h_split.symm, Resume.call_returnData h_split.symm,
          Resume.call_memory h_split.symm,
          by rw [Resume.call_stack_flag h_split.symm, if_neg herr]⟩

/-- Compatibility projection of `of_run_call_val_with_depth_frame`.  Existing
consumers retain the original CALL inversion while log/output-aware consumers
can use the strengthened frame theorem above. -/
lemma of_run_call_val_with_depth
    {sevm : Sevm} {s sf : Devm} {g c v ii is oi os : B256}
    {xs : Stack}
    (hp : (g :: c :: v :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_run : Ninst.Run sevm s Ninst.call sf) :
    (((0 : B256) :: xs <<+ sf.stack) ∧ Devm.WorldEq s sf) ∨
    ∃ (parent child : Devm) (xl : Xlot) (dp : Bool) (code : ByteArray)
      (avail : Nat),
      0 < sevm.depth ∧
      s.stack = g :: c :: v :: ii :: is :: oi :: os :: parent.stack ∧
      parent.state = s.state ∧
      parent.memory
        = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] ∧
      ((getDelegatedCodeAddress (s.getCode c.toAdr) = none ∧
          code = s.getCode c.toAdr ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (s.getCode c.toAdr) = some d ∧
          code = s.getCode d ∧ dp = true)) ∧
      Xlot.Filled xl ∧
      ProcessMessage
        (callMsg sevm parent
          (min g.toNat (except64th avail)
            + (if v.toNat = 0 then 0 else gCallStipend))
          v sevm.currentTarget c.toAdr c.toAdr true false
          ((s.memory.read ii.toNat is.toNat).1) code dp)
        xl (.ok child) ∧
      child.error.isSome = false ∧
      (Resume.call parent oi.toNat os.toNat).run (.ok child) = .ok sf ∧
      sf.state = child.state ∧
      sf.returnData = child.output ∧
      sf.memory = parent.memory.write oi.toNat (child.output.take os.toNat) ∧
      sf.stack = (1 : B256) :: parent.stack := by
  rcases of_run_call_val_with_depth_frame hp h_run with hfail | hsuccess
  · exact Or.inl hfail
  · rcases hsuccess with
      ⟨parent, child, xl, dp, code, avail, _pc, _hstep,
        hdepth, hstack, hstate, hmemory, hlogs, houtput, hrest⟩
    exact Or.inr ⟨parent, child, xl, dp, code, avail,
      hdepth, hstack, hstate, hmemory, hrest⟩

/-- Compatibility projection of `of_run_call_val_with_depth`.  Existing
consumers that do not need the entered-frame depth fact keep the original API. -/
lemma of_run_call_val {sevm : Sevm} {s sf : Devm} {g c v ii is oi os : B256}
    {xs : Stack}
    (hp : (g :: c :: v :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_run : Ninst.Run sevm s Ninst.call sf) :
    (((0 : B256) :: xs <<+ sf.stack) ∧ Devm.WorldEq s sf) ∨
    ∃ (parent child : Devm) (xl : Xlot) (dp : Bool) (code : ByteArray)
      (avail : Nat),
      s.stack = g :: c :: v :: ii :: is :: oi :: os :: parent.stack ∧
      parent.state = s.state ∧
      parent.memory
        = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] ∧
      ((getDelegatedCodeAddress (s.getCode c.toAdr) = none ∧
          code = s.getCode c.toAdr ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (s.getCode c.toAdr) = some d ∧
          code = s.getCode d ∧ dp = true)) ∧
      Xlot.Filled xl ∧
      ProcessMessage
        (callMsg sevm parent
          (min g.toNat (except64th avail)
            + (if v.toNat = 0 then 0 else gCallStipend))
          v sevm.currentTarget c.toAdr c.toAdr true false
          ((s.memory.read ii.toNat is.toNat).1) code dp)
        xl (.ok child) ∧
      child.error.isSome = false ∧
      (Resume.call parent oi.toNat os.toNat).run (.ok child) = .ok sf ∧
      sf.state = child.state ∧
      sf.returnData = child.output ∧
      sf.memory = parent.memory.write oi.toNat (child.output.take os.toNat) ∧
      sf.stack = (1 : B256) :: parent.stack := by
  rcases of_run_call_val_with_depth hp h_run with h_fail | h_enter
  · exact Or.inl h_fail
  · rcases h_enter with ⟨parent, child, xl, dp, code, avail, _, h_enter⟩
    exact Or.inr ⟨parent, child, xl, dp, code, avail, h_enter⟩

/-- Why a value-carrying `STATICCALL` returned its failure flag.  The depth
case has no child and therefore empty returndata.  The other case records the
exact errored child message, including delegation resolution and calldata. -/
def StatcallFailureCause (sevm : Sevm) (s : Devm)
    (g t ii is oi os : B256) (out : Bytes) : Prop :=
  out = [] ∨
    ∃ (parent child : Devm) (xl : Xlot) (dp : Bool) (code : ByteArray)
      (avail : Nat),
      0 < sevm.depth ∧
      s.stack = g :: t :: ii :: is :: oi :: os :: parent.stack ∧
      parent.state = s.state ∧
      parent.memory
        = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] ∧
      ((getDelegatedCodeAddress (s.getCode t.toAdr) = none ∧
          code = s.getCode t.toAdr ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (s.getCode t.toAdr) = some d ∧
          code = s.getCode d ∧ dp = true)) ∧
      Xlot.Filled xl ∧
      ProcessMessage
        (callMsg sevm parent (min g.toNat (except64th avail)) 0
          sevm.currentTarget t.toAdr t.toAdr true true
          ((s.memory.read ii.toNat is.toNat).1) code dp)
        xl (.ok child) ∧
      child.error.isSome = true ∧
      out = child.output

/-- **The value-carrying `STATICCALL` inversion with failure cause.**  With the six operands
known, a successful instruction either returned the failure flag `0` while
restoring the caller's world, or entered/resolved the exact static child
message and resumed with that child's output as returndata.

The successful-child arm includes synchronous precompiles (`xl = .none`) as
well as interpreted code.  In particular it does not assume that the target
has code, that a precompile succeeds, or that the child returns any fixed
number of bytes. -/
lemma of_run_statcall_val_with_depth_cause
    {sevm : Sevm} {s sf : Devm} {g t ii is oi os : B256} {xs : Stack}
    (hp : (g :: t :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_run : Ninst.Run sevm s Ninst.statcall sf) :
    (((0 : B256) :: xs <<+ sf.stack) ∧ Devm.WorldEq s sf ∧
      ∃ out : Bytes,
        sf.returnData = out ∧
        sf.memory = (s.memory.extends
          [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write
            oi.toNat (out.take os.toNat) ∧
        StatcallFailureCause sevm s g t ii is oi os out) ∨
    ∃ (parent child : Devm) (xl : Xlot) (dp : Bool) (code : ByteArray)
      (avail : Nat),
      0 < sevm.depth ∧
      s.stack = g :: t :: ii :: is :: oi :: os :: parent.stack ∧
      parent.state = s.state ∧
      parent.memory
        = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] ∧
      parent.logs = s.logs ∧
      parent.output = s.output ∧
      ((getDelegatedCodeAddress (s.getCode t.toAdr) = none ∧
          code = s.getCode t.toAdr ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (s.getCode t.toAdr) = some d ∧
          code = s.getCode d ∧ dp = true)) ∧
      Xlot.Filled xl ∧
      ProcessMessage
        (callMsg sevm parent (min g.toNat (except64th avail)) 0
          sevm.currentTarget t.toAdr t.toAdr true true
          ((s.memory.read ii.toNat is.toNat).1) code dp)
        xl (.ok child) ∧
      child.error.isSome = false ∧
      (Resume.call parent oi.toNat os.toNat).run (.ok child) = .ok sf ∧
      sf.state = child.state ∧
      sf.returnData = child.output ∧
      sf.memory = parent.memory.write oi.toNat (child.output.take os.toNat) ∧
      sf.stack = (1 : B256) :: parent.stack := by
  rcases h_run with ⟨xl, h_fill, pc, h_run⟩
  simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step,
    Bind.bind, Except.bind] at h_run
  -- pop gas
  rcases eq1 : Devm.pop s with _ | ⟨gas1, devm1⟩ <;> simp only [eq1] at h_run
  · cases XStep.run_ofExcept_error h_run
  have f1 := Devm.pop_of_pop eq1
  have e1 := f1.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1
  rw [e1] at hp
  have hv1 : g = gas1 := pref_head_unique hp (pref_append [gas1] devm1.stack)
  subst hv1
  replace hp := cons_pref_cons_inv hp
  -- pop target
  rcases eq2 : Devm.popToAdr devm1 with _ | ⟨target, devm2⟩ <;>
    simp only [eq2] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToAdr eq2 with ⟨x2, hx2, h_pop2⟩
  have f2 := Devm.pop_of_pop h_pop2
  have e2 := f2.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e2
  rw [e2] at hp
  have hv2 : t = x2 := pref_head_unique hp (pref_append [x2] devm2.stack)
  subst hv2
  subst hx2
  replace hp := cons_pref_cons_inv hp
  -- pop the four indices/sizes
  rcases eq3 : Devm.popToNat devm2 with _ | ⟨inputIndex, devm3⟩ <;>
    simp only [eq3] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat_val eq3 with ⟨x3, f3, hk3⟩
  have e3 := f3.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e3
  rw [e3] at hp
  have hv3 : ii = x3 := pref_head_unique hp (pref_append [x3] devm3.stack)
  subst hv3
  subst hk3
  replace hp := cons_pref_cons_inv hp
  rcases eq4 : Devm.popToNat devm3 with _ | ⟨inputSize, devm4⟩ <;>
    simp only [eq4] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat_val eq4 with ⟨x4, f4, hk4⟩
  have e4 := f4.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e4
  rw [e4] at hp
  have hv4 : is = x4 := pref_head_unique hp (pref_append [x4] devm4.stack)
  subst hv4
  subst hk4
  replace hp := cons_pref_cons_inv hp
  rcases eq5 : Devm.popToNat devm4 with _ | ⟨outputIndex, devm5⟩ <;>
    simp only [eq5] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat_val eq5 with ⟨x5, f5, hk5⟩
  have e5 := f5.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e5
  rw [e5] at hp
  have hv5 : oi = x5 := pref_head_unique hp (pref_append [x5] devm5.stack)
  subst hv5
  subst hk5
  replace hp := cons_pref_cons_inv hp
  rcases eq6 : Devm.popToNat devm5 with _ | ⟨outputSize, devm6⟩ <;>
    simp only [eq6] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat_val eq6 with ⟨x6, f6, hk6⟩
  have e6 := f6.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e6
  rw [e6] at hp
  have hv6 : os = x6 := pref_head_unique hp (pref_append [x6] devm6.stack)
  subst hv6
  subst hk6
  replace hp := cons_pref_cons_inv hp
  have e_stack : s.stack = g :: t :: ii :: is :: oi :: os :: devm6.stack := by
    rw [e1, e2, e3, e4, e5, e6]
  have h_st6 : s.state = devm6.state :=
    (f1.state).trans ((f2.state).trans ((f3.state).trans
      ((f4.state).trans ((f5.state).trans f6.state))))
  have h_mem6 : s.memory = devm6.memory :=
    (f1.memory).trans ((f2.memory).trans ((f3.memory).trans
      ((f4.memory).trans ((f5.memory).trans f6.memory))))
  have h_tra6 : s.transientStorage = devm6.transientStorage :=
    (f1.transientStorage).trans ((f2.transientStorage).trans
      ((f3.transientStorage).trans ((f4.transientStorage).trans
        ((f5.transientStorage).trans f6.transientStorage))))
  have h_logs6 : s.logs = devm6.logs :=
    (f1.logs).trans ((f2.logs).trans ((f3.logs).trans
      ((f4.logs).trans ((f5.logs).trans f6.logs))))
  have h_output6 : s.output = devm6.output :=
    (f1.output).trans ((f2.output).trans ((f3.output).trans
      ((f4.output).trans ((f5.output).trans f6.output))))
  clear e1 e2 e3 e4 e5 e6 f1 f2 f3 f4 f5 f6
  clear eq1 eq2 eq3 eq4 eq5 eq6 h_pop2
  -- delegation resolution
  rcases hp10 : accessDelegation (addAccessedAddress devm6 t.toAdr) t.toAdr with
    ⟨dp, na, code0, dagc, devm8⟩
  simp only [hp10] at h_run
  have h_st8 : devm8.state = devm6.state := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).state) hp10
    dsimp at h
    rw [← h, accessDelegation_state]
    rfl
  have h_stk8 : devm8.stack = devm6.stack := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).stack) hp10
    dsimp at h
    rw [← h, accessDelegation_stack]
    rfl
  have h_mem8 : devm8.memory = devm6.memory := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).memory) hp10
    dsimp at h
    rw [← h, accessDelegation_memory]
    rfl
  have h_tra8 : devm8.transientStorage = devm6.transientStorage := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).transientStorage) hp10
    dsimp at h
    rw [← h, accessDelegation_transientStorage]
    rfl
  have h_logs8 : devm8.logs = devm6.logs := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).logs) hp10
    dsimp at h
    rw [← h, accessDelegation_logs]
    rfl
  have h_output8 : devm8.output = devm6.output := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).output) hp10
    dsimp at h
    rw [← h, accessDelegation_output]
    rfl
  have h_gc6 : (addAccessedAddress devm6 t.toAdr).state.getCode t.toAdr
      = s.getCode t.toAdr := by
    show devm6.state.getCode t.toAdr = s.getCode t.toAdr
    rw [← h_st6]
    rfl
  have h_del :
      (getDelegatedCodeAddress (s.getCode t.toAdr) = none ∧
        code0 = s.getCode t.toAdr ∧ dp = false) ∨
      (∃ d, getDelegatedCodeAddress (s.getCode t.toAdr) = some d ∧
        code0 = s.getCode d ∧ dp = true) := by
    have h_acc := hp10
    dsimp only [accessDelegation] at h_acc
    rw [h_gc6] at h_acc
    rcases hdel : getDelegatedCodeAddress (s.getCode t.toAdr) with _ | d <;>
      rw [hdel] at h_acc <;>
      simp only [Prod.mk.injEq] at h_acc
    · exact Or.inl ⟨rfl, h_acc.2.2.1.symm, h_acc.1.symm⟩
    · refine Or.inr ⟨d, rfl, ?_, h_acc.1.symm⟩
      rw [← h_acc.2.2.1]
      show (addAccessedAddress devm6 t.toAdr).state.getCode d = s.getCode d
      show devm6.state.getCode d = s.getCode d
      rw [← h_st6]
      rfl
  -- charge the parent-side overhead
  split at h_run
  · cases XStep.run_ofExcept_error h_run
  rename_i devm9 eq14
  have h_st9 : devm8.state = devm9.state := (Devm.burn_of_chargeGas eq14).state
  have h_stk9 : devm8.stack = devm9.stack := (Devm.burn_of_chargeGas eq14).stack
  have h_mem9 : devm8.memory = devm9.memory := (Devm.burn_of_chargeGas eq14).memory
  have h_tra9 : devm8.transientStorage = devm9.transientStorage :=
    (Devm.burn_of_chargeGas eq14).transientStorage
  have h_logs9 : devm8.logs = devm9.logs :=
    (Devm.burn_of_chargeGas eq14).logs
  have h_output9 : devm8.output = devm9.output :=
    (Devm.burn_of_chargeGas eq14).output
  simp only [genericCall.step] at h_run
  split at h_run
  · -- depth limit: no frame opened
    simp only [Bind.bind, Except.bind] at h_run
    split at h_run
    case h_1 => cases XStep.run_ofExcept_error h_run
    case h_2 =>
    rename_i devm11 h_push
    left
    have h_ex := Except.ok.inj h_run.2
    rw [h_ex]
    have h_stk := (Devm.push_of_push h_push).stack
    refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
    · show ((0 : B256) :: xs) <<+ devm11.stack
      rw [h_stk]
      show ((0 : B256) :: xs) <<+ (0 : B256) ::
        ((devm9.memExtends
          [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData []).stack
      show ((0 : B256) :: xs) <<+ (0 : B256) ::
        (devm9.memExtends
          [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).stack
      have h_stk10 :
          (devm9.memExtends
            [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).stack
            = devm6.stack := by
        show devm9.stack = devm6.stack
        rw [← h_stk9, h_stk8]
      rw [h_stk10]
      exact pref_cons hp
    · show s.state = devm11.state
      rw [← (Devm.push_of_push h_push).state]
      show s.state = devm9.state
      rw [← h_st9, h_st8, ← h_st6]
    · show s.transientStorage = devm11.transientStorage
      rw [← (Devm.push_of_push h_push).transientStorage]
      show s.transientStorage = devm9.transientStorage
      rw [← h_tra9, h_tra8, ← h_tra6]
    · refine ⟨[], ?_, ?_, Or.inl rfl⟩
      · show devm11.returnData = []
        exact (Devm.push_of_push h_push).returnData.symm
      · show devm11.memory =
          (s.memory.extends
            [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write
              oi.toNat (([] : Bytes).take os.toNat)
        simp only [List.take_nil]
        change devm11.memory =
          s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]
        rw [← (Devm.push_of_push h_push).memory]
        show devm9.memory.extends
            [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] = _
        rw [← h_mem9, h_mem8, ← h_mem6]
  · -- the static child is executed (synchronously for precompiles)
    rename_i h_depth_ne
    simp only [XStep.Run] at h_run
    rcases h_run with ⟨ex', run_pm₀, h_split⟩
    rcases ex' with err' | child
    · cases Resume.call_run_error h_split.symm
    have h_stk_par :
        ((devm9.memExtends
          [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData []).stack
          = devm6.stack := by
      show devm9.stack = devm6.stack
      rw [← h_stk9, h_stk8]
    have h_st_par :
        ((devm9.memExtends
          [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData []).state
          = s.state := by
      show devm9.state = s.state
      rw [← h_st9, h_st8, ← h_st6]
    have h_tra_par :
        ((devm9.memExtends
          [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData
          []).transientStorage = s.transientStorage := by
      show devm9.transientStorage = s.transientStorage
      rw [← h_tra9, h_tra8, ← h_tra6]
    have h_mem_par :
        ((devm9.memExtends
          [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData
          []).memory
          = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] := by
      show devm9.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]
        = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]
      rw [← h_mem9, h_mem8, ← h_mem6]
    have h_logs_par :
        ((devm9.memExtends
          [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData
          []).logs = s.logs := by
      show devm9.logs = s.logs
      rw [← h_logs9, h_logs8, ← h_logs6]
    have h_output_par :
        ((devm9.memExtends
          [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData
          []).output = s.output := by
      show devm9.output = s.output
      rw [← h_output9, h_output8, ← h_output6]
    obtain ⟨avail, hstip⟩ := calculateMsgCallGas_stipend (chargeGas_le eq14)
    rw [hstip] at run_pm₀
    have h_cd : Array.sliceD
        ((devm9.memExtends
          [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData
          []).memory.data ii.toNat is.toNat 0
        = (s.memory.read ii.toNat is.toNat).1 := by
      rw [h_mem_par]
      rfl
    rw [h_cd] at run_pm₀
    by_cases herr : child.error.isSome
    · left
      have h_roll : Devm.WorldEq child
          ((devm9.memExtends
            [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData []) :=
        ProcessMessage.rollback_of_error run_pm₀ herr
      refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
      · have hsf := Resume.call_stack_flag h_split.symm
        rw [if_pos herr] at hsf
        rw [hsf, h_stk_par]
        exact pref_cons hp
      · rw [Resume.call_state h_split.symm, h_roll.1, h_st_par]
      · rw [Resume.call_transientStorage h_split.symm, h_roll.2, h_tra_par]
      · refine ⟨child.output, Resume.call_returnData h_split.symm, ?_,
          Or.inr ?_⟩
        · rw [Resume.call_memory h_split.symm, h_mem_par]
        · refine ⟨
            (devm9.memExtends
              [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData [],
            child, xl, dp, code0, avail,
            by omega, by rw [e_stack, h_stk_par], h_st_par, h_mem_par,
            h_del, h_fill, ?_, by simpa using herr, rfl⟩
          simpa [ProcessMessage] using run_pm₀
    · right
      refine ⟨(devm9.memExtends
          [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData [],
        child, xl, dp, code0, avail,
        by omega, by rw [e_stack, h_stk_par], h_st_par, h_mem_par,
        h_logs_par, h_output_par, h_del,
        h_fill, ?_, by simpa using herr, h_split.symm,
        Resume.call_state h_split.symm, Resume.call_returnData h_split.symm,
        Resume.call_memory h_split.symm,
        by rw [Resume.call_stack_flag h_split.symm, if_neg herr]⟩
      simpa [ProcessMessage] using run_pm₀

/-- The compatibility projection of `of_run_statcall_val_with_depth_cause`.
Consumers that only need the flag/world/returndata dichotomy do not have to
carry the failure-cause witness. -/
lemma of_run_statcall_val_with_depth
    {sevm : Sevm} {s sf : Devm} {g t ii is oi os : B256} {xs : Stack}
    (hp : (g :: t :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_run : Ninst.Run sevm s Ninst.statcall sf) :
    (((0 : B256) :: xs <<+ sf.stack) ∧ Devm.WorldEq s sf ∧
      ∃ out : Bytes,
        sf.returnData = out ∧
        sf.memory = (s.memory.extends
          [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write
            oi.toNat (out.take os.toNat)) ∨
    ∃ (parent child : Devm) (xl : Xlot) (dp : Bool) (code : ByteArray)
      (avail : Nat),
      0 < sevm.depth ∧
      s.stack = g :: t :: ii :: is :: oi :: os :: parent.stack ∧
      parent.state = s.state ∧
      parent.memory
        = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] ∧
      ((getDelegatedCodeAddress (s.getCode t.toAdr) = none ∧
          code = s.getCode t.toAdr ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (s.getCode t.toAdr) = some d ∧
          code = s.getCode d ∧ dp = true)) ∧
      Xlot.Filled xl ∧
      ProcessMessage
        (callMsg sevm parent (min g.toNat (except64th avail)) 0
          sevm.currentTarget t.toAdr t.toAdr true true
          ((s.memory.read ii.toNat is.toNat).1) code dp)
        xl (.ok child) ∧
      child.error.isSome = false ∧
      (Resume.call parent oi.toNat os.toNat).run (.ok child) = .ok sf ∧
      sf.state = child.state ∧
      sf.returnData = child.output ∧
      sf.memory = parent.memory.write oi.toNat (child.output.take os.toNat) ∧
      sf.stack = (1 : B256) :: parent.stack := by
  rcases of_run_statcall_val_with_depth_cause hp h_run with hfail | hsuccess
  · rcases hfail with ⟨hstack, hworld, out, hret, hmem, hcause⟩
    exact Or.inl ⟨hstack, hworld, out, hret, hmem⟩
  · rcases hsuccess with
      ⟨parent, child, xl, dp, code, avail,
        hdepth, hstack, hstate, hmemory, hlogs, houtput, hrest⟩
    exact Or.inr ⟨parent, child, xl, dp, code, avail,
      hdepth, hstack, hstate, hmemory, hrest⟩

/-- The deeper-frame induction hypothesis, as the ladder's consumers use it:
every successful sub-execution of `p` at `ca` strictly below depth `k` takes
`σ` to `ρ`.  Generic in the program and in both predicates. -/
def Exec.InvDepth (k : Nat) (ca : Adr) (p : Prog)
  (σ : Sevm → Devm → Prop) (ρ : Sevm → Devm → Prop) : Prop :=
  ForallDeeperAt k ca p (λ _ sevm pre exn _ => σ sevm pre → ifOk (ρ sevm) exn)


/-! ## The contract-generic ladder -/

/-- A successful synchronous generic call cannot change persistent storage.
This includes empty-code and precompile execution as well as failed child
settlement; value transfer changes balances only. -/
lemma GenericCall.none_getStor_eq {sevm : Sevm} {devm inter : Devm}
    {gas : Nat} {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    (h_run : GenericCall sevm devm gas value caller target codeAddress stv
      isStatic ii is oi os code dp .none (.ok inter)) :
    Devm.getStor inter = Devm.getStor devm := by
  unfold GenericCall genericCall.step at h_run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_run
  repeat' split at h_run
  all_goals simp only [XStep.ofExcept, XStep.Run] at h_run
  · cases h_run.2
  · rename_i h_push
    apply funext
    apply getStor_eq_of_state_eq
    rw [Except.ok.inj h_run.2, ← (Devm.push_of_push h_push).state]
    rfl
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
    rcases eq_bt : childMsg.benvAfterTransfer with e | benv <;>
      rw [eq_bt] at hbody
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
      apply funext
      apply getStor_eq_of_state_eq
      rw [h_inter_state, ← Except.ok.inj hset.symm]
      exact hc_state
    · rw [if_neg h_err2] at hset
      have h_eq_child := Except.ok.inj hset.symm
      subst h_eq_child
      have hc_ca2 : (childMsg.withBenv benv).codeAddress = some codeAddress :=
        hc_ca
      rcases of_executeCode_someCode hc_ca2 run_ec with
        ⟨_, _, h_he⟩ | ⟨_, exn, h_xl_some, _⟩
      · have h_child_state : evm2.state = benv.state := by
          have h := state_of_executePrecomp_ok h_he h_err2
          rw [h]
          rfl
        by_cases h_stv : stv = true
        · rcases of_benvAfterTransfer (hc_stv.trans h_stv) eq_bt with
            ⟨st_mid, h_sub, hB⟩
          rw [hc_state, hc_caller, hc_value] at h_sub
          have hBs : benv.state = st_mid.addBal target value := by
            rw [hB, hc_ct, hc_value]
            rfl
          apply funext
          intro a
          show (inter.state.get a).stor = (devm.state.get a).stor
          rw [h_inter_state, h_child_state, hBs]
          exact (of_state_transfer_fields h_sub).1 a
        · have h_stv2 : ¬ childMsg.shouldTransferValue = true := by
            rw [hc_stv]
            exact h_stv
          have h_benv : benv = childMsg.benv :=
            of_benvAfterTransfer_no h_stv2 eq_bt
          apply funext
          apply getStor_eq_of_state_eq
          rw [h_inter_state, h_child_state, h_benv]
          exact hc_state
      · cases h_xl_some

/-- A successful synchronous generic create cannot change persistent storage.
The only nontrivial childless success increments the creator nonce. -/
lemma GenericCreate.none_getStor_eq {sevm : Sevm} {devm inter : Devm}
    {endowment : B256} {newAddress : Adr} {memoryIndex memorySize : Nat}
    (h_run : GenericCreate sevm devm endowment newAddress memoryIndex memorySize
      .none (.ok inter)) :
    Devm.getStor inter = Devm.getStor devm := by
  unfold GenericCreate genericCreate.step at h_run
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic, Pure.pure,
    Except.pure] at h_run
  repeat' split at h_run
  all_goals simp only [XStep.ofExcept, XStep.Run] at h_run
  · cases h_run.2
  · cases h_run.2
  · cases h_run.2
  · rename_i h_push
    apply funext
    apply getStor_eq_of_state_eq
    rw [Except.ok.inj h_run.2, ← (Devm.push_of_push h_push).state]
    rfl
  · cases h_run.2
  · rename_i h_push
    have h_state : inter.state = devm.state.incrNonce sevm.currentTarget := by
      rw [Except.ok.inj h_run.2, ← (Devm.push_of_push h_push).state]
      rfl
    apply funext
    intro a
    show (inter.state.get a).stor = (devm.state.get a).stor
    rw [h_state]
    exact State.incrNonce_get_stor
  · exfalso
    obtain ⟨r, hframe, hres⟩ := h_run
    obtain ⟨childMsg, hframe, hc_ca⟩ :
        ∃ m : Msg, ProcessCreateMessage m .none r ∧ m.codeAddress = .none :=
      ⟨_, hframe, rfl⟩
    obtain ⟨r1, hpm, hset⟩ := ProcessCreateMessage.iff_processMessage.mp hframe
    obtain ⟨r0, hbody, hset1⟩ := ProcessMessage.iff_body.mp hpm
    unfold FrameBody at hbody
    rcases eq_bt : (processCreateMessage.msg childMsg).benvAfterTransfer with
      e | benv <;> rw [eq_bt] at hbody
    · rw [hbody.2, processMessage.settle_error] at hset1
      rw [hset1, processCreateMessage.settle_error] at hset
      rw [hset] at hres
      exact Resume.create_run_error hres.symm
    · have hca :
          ((processCreateMessage.msg childMsg).withBenv benv).codeAddress =
            .none := hc_ca
      obtain ⟨exn, h_xl, -⟩ := of_executeCode_noneCode hca hbody
      cases h_xl

/-- Any successful childless executable instruction preserves persistent
storage at every address. -/
lemma Xinst.none_getStor_eq {sevm : Sevm} {devm inter : Devm} {x : Xinst}
    (h_run : Xinst.Run sevm devm x .none (.ok inter)) :
    Devm.getStor inter = Devm.getStor devm := by
  unfold Xinst.Run at h_run
  rcases Xinst.step_shape sevm devm x with ⟨ex, hs, hframe⟩ |
    ⟨d, e, na, mi, ms, hf, hs⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, hcal, -, hs⟩ <;> rw [hs] at h_run
  · obtain ⟨-, hex⟩ := h_run
    rw [← hex] at hframe
    have hif : Devm.InstructionFrame devm inter := hframe
    exact (funext hif.getStor).symm
  · exact GenericCreate.none_getStor_eq h_run |>.trans
      (funext hf.getStor).symm
  · exact GenericCall.none_getStor_eq h_run |>.trans
      (funext hf.getStor).symm

/-- Every successfully terminating last instruction preserves persistent
storage at every address; `SELFDESTRUCT` changes balances and deletion marks
only. -/
theorem Linst.getStor_eq
    {sevm : Sevm} {pre post : Devm} {l : Linst}
    (run : Linst.Run sevm pre l (.ok post)) :
    Devm.getStor post = Devm.getStor pre := by
  funext owner
  cases l with
  | stop =>
      simp [Linst.Run, Linst.run] at run
      subst post
      rfl
  | ret =>
      have hframe := Linst.run_instructionFrame sevm pre .ret (by decide)
      rw [run] at hframe
      exact (hframe.getStor owner).symm
  | rev =>
      dsimp [Linst.Run, Linst.run] at run
      rcases Except.bind_eq_ok run with ⟨first, hfirst, rest⟩
      rcases Except.bind_eq_ok rest with ⟨second, hsecond, rest⟩
      rcases Except.bind_eq_ok rest with ⟨third, hthird, rest⟩
      contradiction
  | dest =>
      dsimp [Linst.Run, Linst.run] at run
      rcases Except.bind_eq_ok run with
        ⟨⟨donee, devm1⟩, pop, rest⟩
      rcases Except.bind_eq_ok rest with
        ⟨devm2, charge, rest⟩
      rcases Except.bind_eq_ok rest with
        ⟨_, asserted, rest⟩
      rcases Except.bind_eq_ok rest with
        ⟨devm3, sub, final⟩
      have subSome : devm2.subBal sevm.currentTarget
          (devm1.getAcct sevm.currentTarget).bal = some devm3 := by
        cases eq : devm2.subBal sevm.currentTarget
            (devm1.getAcct sevm.currentTarget).bal
        · rw [eq] at sub
          contradiction
        · rw [eq] at sub
          injection sub with equal
          subst equal
          rfl
      have subState : devm2.state.subBal sevm.currentTarget
          (devm1.getAcct sevm.currentTarget).bal = some devm3.state := by
        dsimp [Devm.subBal, Option.bind] at subSome
        cases eq : devm2.state.subBal sevm.currentTarget
            (devm1.getAcct sevm.currentTarget).bal
        · rw [eq] at subSome
          contradiction
        · rw [eq] at subSome
          injection subSome with equal
          subst equal
          rfl
      let transferred := devm3.addBal donee
        (devm1.getAcct sevm.currentTarget).bal
      have preToOne : Devm.getStor pre owner = Devm.getStor devm1 owner :=
        congrFun (Devm.popToAdr_getStor_eq pop) owner
      have charged : Devm.getStor devm1 owner =
          Devm.getStor devm2 owner := by
        have chargedEq := chargeGas_getStor_eq charge
        have head : Devm.getStor
            (if donee ∉ devm1.accessedAddresses then
              (addAccessedAddress devm1 donee,
                gasSelfDestruct + gasColdAccountAccess)
            else (devm1, gasSelfDestruct)).1 owner =
              Devm.getStor devm1 owner := by
          split <;> rfl
        exact head.symm.trans (congrFun chargedEq owner)
      have transferredEq : Devm.getStor devm2 owner =
          Devm.getStor transferred owner :=
        (of_state_transfer_fields subState).1 owner |>.symm
      have postEq : Devm.getStor transferred owner =
          Devm.getStor post owner := by
        dsimp only [transferred] at final ⊢
        split at final
        · have equal := Except.ok.inj final
          rw [← equal]
          exact State.setBal_get_stor.symm
        · have equal := Except.ok.inj final
          rw [← equal]
      exact (preToOne.trans (charged.trans
        (transferredEq.trans postEq))).symm

/-! ## Static propagation across a spawned frame -/

/-- A `CALL`-family child inherits its parent's static flag: `callMsg` sets
`isStatic := isStaticcall || sevm.isStatic`. -/
theorem genericCall.step_spawn_isStatic
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {f : Jaune.Frame} {rsm : Resume}
    (hs : genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles = .spawn f rsm)
    (hstatic : sevm.isStatic = true) :
    f.inner.isStatic = true := by
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals simp only [Jaune.Frame.ofCall, callMsg, hstatic, Bool.or_true]

/-- A `CREATE`-family child is never spawned from a static context: the
`assertDynamic` guard precedes the spawn. -/
theorem genericCreate.step_spawn_not_static
    {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {memoryIndex memorySize : Nat} {f : Jaune.Frame} {rsm : Resume}
    (hs : genericCreate.step sevm devm endowment newAddress memoryIndex
      memorySize = .spawn f rsm) :
    sevm.isStatic = false := by
  simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
    assertDynamic, Pure.pure, Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
  all_goals simp_all

/-- Every child frame spawned by a recursive instruction from a static
context is itself static. -/
theorem Xinst.step_spawn_isStatic {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Jaune.Frame} {rsm : Resume}
    (hs : Xinst.step sevm devm x = .spawn f rsm)
    (hstatic : sevm.isStatic = true) :
    f.inner.isStatic = true := by
  cases x <;>
    simp only [Xinst.step, Bind.bind, Except.bind, Except.assert,
      Pure.pure, Except.pure] at hs <;>
    repeat' split at hs
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
  all_goals
    first
      | exact absurd hstatic
          (by rw [genericCreate.step_spawn_not_static hs]; exact Bool.noConfusion)
      | exact genericCall.step_spawn_isStatic hs hstatic

/-- Every child frame spawned by one driver step from a static context is
itself static. -/
theorem Evm.step_spawn_isStatic {pc pc' : Nat} {sevm : Sevm} {devm : Devm}
    {f : Jaune.Frame} {rsm : Resume}
    (hs : Jaune.Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc')
    (hstatic : sevm.isStatic = true) :
    f.inner.isStatic = true := by
  obtain ⟨_, _, hx, _⟩ := Evm.step_spawn_inv hs
  exact Xinst.step_spawn_isStatic hx hstatic

/-- Frame entry hands the spawned message's static flag straight to the
interpreted child context: `initSevm`'s `isStatic` *is* `msg.isStatic`, and
neither `Msg.withBenv` nor the value transfer touches it. -/
theorem executeCode.enter_inl_isStatic {msg : Msg} {e : Evm}
    (h : executeCode.enter msg = .inl e) : e.sta.isStatic = msg.isStatic := by
  unfold executeCode.enter at h
  split at h
  · cases h
    rfl
  · split at h
    · cases h
    · cases h
      rfl

theorem Frame.enter_run_isStatic {f : Jaune.Frame} {cevm : Evm}
    (henter : f.enter = .run cevm) :
    cevm.sta.isStatic = f.inner.isStatic := by
  unfold Jaune.Frame.enter at henter
  split at henter
  · cases henter
  · rename_i benv _
    split at henter
    · rename_i e he
      cases henter
      exact executeCode.enter_inl_isStatic (msg := f.inner.withBenv benv) he
    · cases henter

/-- The composite propagation step consumed by the subtree induction: an
interpreted child of a static frame runs statically. -/
theorem Evm.step_run_isStatic {pc pc' : Nat} {sevm : Sevm} {devm : Devm}
    {f : Jaune.Frame} {rsm : Resume} {cevm : Evm}
    (hs : Jaune.Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc')
    (henter : f.enter = .run cevm)
    (hstatic : sevm.isStatic = true) :
    cevm.sta.isStatic = true :=
  (Frame.enter_run_isStatic henter).trans
    (Evm.step_spawn_isStatic hs hstatic)

/-! ## `STATICCALL` children are static whatever their parent is -/

/-- `STATICCALL` passes `isStaticcall := true`, so its child is static even
from a dynamic parent. -/
theorem genericCall.step_spawn_isStatic_of_staticcall
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {f : Jaune.Frame} {rsm : Resume}
    (hs : genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue true inputIndex inputSize outputIndex
      outputSize code disablePrecompiles = .spawn f rsm) :
    f.inner.isStatic = true := by
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals simp only [Jaune.Frame.ofCall, callMsg, Bool.true_or]

theorem Xinst.step_statcall_spawn_isStatic
    {sevm : Sevm} {devm : Devm} {f : Jaune.Frame} {rsm : Resume}
    (hs : Xinst.step sevm devm .statcall = .spawn f rsm) :
    f.inner.isStatic = true := by
  simp only [Xinst.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
  all_goals exact genericCall.step_spawn_isStatic_of_staticcall hs

theorem Ninst.step_statcall_spawn_isStatic
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {f : Jaune.Frame} {rsm : Resume}
    (hspawn : Ninst.step ⟨pc, sevm, pre⟩ Ninst.statcall = .spawn f rsm pc') :
    f.inner.isStatic = true := by
  have hx : Xinst.step sevm pre .statcall = .spawn f rsm :=
    XStep.toStep_spawn (by
      simpa only [Ninst.statcall, Ninst.step_exec] using hspawn)
  exact Xinst.step_statcall_spawn_isStatic hx

/-- An interpreted child of a `STATICCALL` runs statically. -/
theorem Ninst.step_statcall_run_isStatic
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {f : Jaune.Frame} {rsm : Resume} {cevm : Evm}
    (hspawn : Ninst.step ⟨pc, sevm, pre⟩ Ninst.statcall = .spawn f rsm pc')
    (henter : f.enter = .run cevm) :
    cevm.sta.isStatic = true :=
  (Frame.enter_run_isStatic henter).trans
    (Ninst.step_statcall_spawn_isStatic hspawn)

/-- Exact CALL frame and resumption selected by a successful generic spawn. -/
theorem genericCall_step_spawn_exact
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool}
    {ii isz oi osz : Nat} {code : ByteArray} {dp : Bool}
    {frame : Frame} {resume : Resume}
    (hspawn : genericCall.step sevm devm gas value caller target codeAddress
      stv isSt ii isz oi osz code dp = .spawn frame resume) :
    frame = Frame.ofCall
      (callMsg sevm (devm.withReturnData []) gas value caller target
        codeAddress stv isSt ((devm.memory.read ii isz).1) code dp) ∧
    resume = .call (devm.withReturnData []) oi osz := by
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hspawn
  repeat' split at hspawn
  all_goals
    simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hspawn
  all_goals obtain ⟨rfl, rfl⟩ := hspawn
  all_goals exact ⟨rfl, rfl⟩

/-- Exact CREATE frame and resumption selected by a successful generic spawn. -/
theorem genericCreate_step_spawn_exact
    {sevm : Sevm} {devm : Devm} {endowment : B256}
    {newAddress : Adr} {mi ms : Nat}
    {frame : Frame} {resume : Resume}
    (hspawn : genericCreate.step sevm devm endowment newAddress mi ms =
      .spawn frame resume) :
    frame = Frame.ofCreate
      (createMsg sevm
        (addAccessedAddress
          (((devm.withGasLeft
              (devm.gasLeft - except64th devm.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) newAddress)
        (except64th devm.gasLeft) endowment newAddress
        ((devm.memory.read mi ms).1)) ∧
    resume = .create
      (addAccessedAddress
        (((devm.withGasLeft
            (devm.gasLeft - except64th devm.gasLeft)).withReturnData
          []).incrNonce sevm.currentTarget) newAddress)
      newAddress := by
  simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
    assertDynamic, Pure.pure, Except.pure] at hspawn
  repeat' split at hspawn
  all_goals
    simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hspawn
  all_goals obtain ⟨rfl, rfl⟩ := hspawn
  all_goals exact ⟨rfl, rfl⟩

/-- A recursive CREATE spawn passed the collision check, so the target's
persistent storage was empty before fresh-account preparation. -/
theorem genericCreate_step_spawn_getStor_empty
    {sevm : Sevm} {devm : Devm} {endowment : B256}
    {newAddress : Adr} {mi ms : Nat}
    {frame : Frame} {resume : Resume}
    (hspawn : genericCreate.step sevm devm endowment newAddress mi ms =
      .spawn frame resume) :
    Devm.getStor devm newAddress = .empty := by
  simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
    assertDynamic, Pure.pure, Except.pure] at hspawn
  repeat' split at hspawn
  all_goals
    simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hspawn
  all_goals obtain ⟨rfl, -⟩ := hspawn
  rename_i collision
  push Not at collision
  let createPre :=
    addAccessedAddress
      (((devm.withGasLeft
          (devm.gasLeft - except64th devm.gasLeft)).withReturnData
        []).incrNonce sevm.currentTarget) newAddress
  have storageEq : Devm.getStor createPre = Devm.getStor devm := by
    funext owner
    have stateEq : createPre.state =
        devm.state.incrNonce sevm.currentTarget := by
      rfl
    change createPre.state.getStor owner = devm.state.getStor owner
    rw [stateEq]
    exact State.incrNonce_get_stor
  have sizeZero : (Devm.getStor devm newAddress).size = 0 := by
    have atCreate : (Devm.getStor createPre newAddress).size = 0 := by
      exact collision.2.2
    rw [storageEq] at atCreate
    exact atCreate
  apply Jaune.Std.TreeMap.eq_empty_iff_isEmpty.mpr
  rw [Std.TreeMap.isEmpty_eq_size_eq_zero]
  simp [sizeZero]

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

/-! ### The contract's obligation, and the frame-level result it yields -/

/-- What a contract must prove about its own program: that a top-level run
takes the precondition to the postcondition, given the induction hypothesis for
deeper frames.  This is the sole input `preserves_inv` cannot supply. -/
def Sound (c : ContractSpec) (ca : Adr) : Prop :=
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
    c.Post ca sevm post

/-- What the frame-level ladder delivers, and what every rung above it
consumes.  `preserves_inv : c.Sound ca → c.Preserves ca`. -/
def Preserves (c : ContractSpec) (ca : Adr) : Prop :=
  ∀ sevm pre post,
    Exec 0 sevm pre (.ok post) →
    (sevm.currentTarget = ca → some sevm.code.toList = Prog.compile c.prog) →
    c.Pre ca sevm pre →
    c.Post ca sevm post

/-! ### The frame-level ladder

`lift_inv` (CommonProofs.lean) is already generic in the program and in the two
predicates; what was WETH-specific about `weth_preserves_solvent` was only the
five obligations fed to it.  Four of those are discharged here once and for
all, for every contract.  The fifth — that a top-level run of the contract's
own program takes the precondition to the postcondition — is the contract's
own work and stays a hypothesis. -/

theorem preserves_inv (c : ContractSpec) (ca : Adr) (body : c.Sound ca) :
    c.Preserves ca := by
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

/-- The `exec` counterpart: with sufficiency proved in Jaune there is no fuel
to quantify away, so the hypothesis is a plain equation about the interpreter. -/
theorem exec_preserves_inv (c : ContractSpec) (ca : Adr) (hp : c.Preserves ca)
    (sevm : Sevm) (pre post : Devm)
    (h_run : exec ⟨0, sevm, pre⟩ = .ok post)
    (h_code : sevm.currentTarget = ca → some sevm.code.toList = Prog.compile c.prog)
    (h_pc : c.Pre ca sevm pre) : c.Post ca sevm post := by
  obtain ⟨exc⟩ := (exec_iff_exec_eq 0 sevm pre (.ok post)).mpr h_run
  exact hp sevm pre post exc h_code h_pc


/-! ### The dispatcher decomposition of `Sound`

The plain Blanc dispatch protocol has program shape
`⟨Func.mainWith k (DispatchTree.ofSorted funcs), aux⟩`; receive-aware contracts
put one empty-calldata branch in front of that same dispatcher.  The reasoning
that carries a run from `fsig` down to one of its dispatch targets is shared in
full by `post_of_run_dispatch`.  `sound_of_dispatch` absorbs the plain
`Prog.Run`/`call 0` unwrap and `fsig` prefix, while
`sound_of_receive_dispatch` also absorbs the receive split.  Both reuse
`dispatchWith_inv`'s two scratch-line side conditions and its tree-shaped
membership obligation, and leave a contract with one `FuncSound` obligation per
entry of its own function *list*, plus one for the fallback at index `k`.

Two notes on the hypotheses, both results rather than bookkeeping:

* **There is no sortedness hypothesis.**  `Sound` is a safety property, and
  sortedness governs reachability, not safety: a misordered list makes some
  target unreachable, which cannot make the dispatcher unsound.  The one step
  that might plausibly have consumed it — turning tree membership into list
  membership — needs only `funcs ≠ []`, by
  `DispatchTree.mem_of_mem_ofSorted`.  Pair `DispatchTree.sorted` with a
  contract to get reachability; it is not needed for soundness.

* **`fsig` is discharged field-wise, not through `Devm.state`.**  The three
  dispatcher obligations below are all one argument — the world state did not
  change, so the precondition survives — via `Line.Inv Devm.state` and
  `Pre.state_eq`.  `fsig` is not: `line_inv` cannot prove
  `Line.Inv Devm.state fsig`, because the `Ninst.Hinv Devm.state` family has
  members only for the scratch instructions (`pushB256`, `eq`, `dup`, `gt`) and
  none for `calldataload` or `shr`.  It needs no hypothesis of its own either —
  `Pre.of_eqs` transports the precondition along the three field observables,
  each of which `line_inv` does prove across `fsig`. -/

/-- The per-function obligation left by `sound_of_dispatch`: `f`'s walk takes
the contract's precondition to its postcondition, given the entry state the
dispatcher hands it and the induction hypothesis for deeper frames.  That
induction hypothesis is part of the entry condition and is not optional — a
target that re-enters the contract (WETH's `withdraw`) genuinely consumes it.

The frame is executing the contract itself (`sevm.currentTarget = ca`); this is
`Sound`'s own hypothesis, carried down to the targets.  It is what lets a
contract state its per-function lemmas at `sevm.currentTarget`, as WETH's ten
do, instead of restating them at an abstract address.

Stated relative to the program's aux context rather than to `c.prog.aux`,
because `Func.call` indices are positional: a lemma relating
`FuncSound c ca aux f` to `FuncSound c' ca (aux ++ extra) f` is what would make
an extension's obligations reusable, and it wants `aux` in hand. -/
def FuncSound (c : ContractSpec) (ca : Adr) (aux : List Func) (f : Func) : Prop :=
  ∀ {sevm : Sevm} {s r : Devm},
    sevm.currentTarget = ca →
    c.Pre ca sevm s →
    Exec.InvDepth sevm.depth ca c.prog (c.Pre ca) (c.Post ca) →
    Func.Run (c.prog.main :: aux) sevm s f r →
    c.Post ca sevm r

/-- The contract-neutral core of dispatcher soundness.  Starting immediately
after `fsig`, a successful walk through a generated dispatch tree reaches
either its indexed fallback or one of the listed targets.  Keeping this as a
run-level theorem lets alternate public ingress shapes (notably a payable
empty-calldata receive branch) share the exact selector/fallback proof. -/
theorem post_of_run_dispatch {c : ContractSpec} {ca : Adr} {k : Nat}
    {funcs : List (B256 × Func)} {aux : List Func} {fallback : Func}
    (h_ne : funcs ≠ [])
    (h_fb : (c.prog.main :: aux)[k]? = some fallback)
    (h_funcs : ∀ p ∈ funcs, FuncSound c ca aux p.2)
    (h_fall : FuncSound c ca aux fallback)
    {sevm : Sevm} {s r : Devm}
    (h_ca : sevm.currentTarget = ca)
    (h_pre : c.Pre ca sevm s)
    (h_ih : Exec.InvDepth sevm.depth ca c.prog (c.Pre ca) (c.Post ca))
    (h_run :
      Func.Run (c.prog.main :: aux) sevm s
        (dispatchWith k (DispatchTree.ofSorted funcs)) r) :
    c.Post ca sevm r := by
  apply
    ( @dispatchWith_inv
        (c.prog.main :: aux) k fallback
        ( fun e s =>
            e.currentTarget = ca ∧
            c.Pre ca e s ∧
            Exec.InvDepth e.depth ca c.prog (c.Pre ca) (c.Post ca) )
        (fun e r => c.Post ca e r)
        ?_ ?_ h_fb ?_ (DispatchTree.ofSorted funcs) ?_
        sevm s r ⟨h_ca, h_pre, h_ih⟩ h_run )
  · intro e s x w s' s'' ⟨h_ct, hp, hih⟩ hline hpop
    refine ⟨h_ct, ?_, hih⟩
    have h_state : s.state = s'.state :=
      Line.of_inv Devm.state (by line_inv) hline
    exact hp.state_eq (hpop.state.symm.trans h_state.symm)
  · intro e s x w s' s'' ⟨h_ct, hp, hih⟩ hline hpop
    refine ⟨h_ct, ?_, hih⟩
    have h_state : s.state = s'.state :=
      Line.of_inv Devm.state (by line_inv) hline
    exact hp.state_eq (hpop.state.symm.trans h_state.symm)
  · intro e s s' r ⟨h_ct, hp, hih⟩ hburn hrun
    exact h_fall h_ct (hp.state_eq hburn.state.symm) hih hrun
  · intro e s r wf h_mem ⟨h_ct, hp, hih⟩ hrun
    exact h_funcs wf (DispatchTree.mem_of_mem_ofSorted h_ne h_mem)
      h_ct hp hih hrun

/-- `Sound` for a dispatcher-shaped program, reduced to one `FuncSound` per
dispatch target plus one for the fallback.  `h_fb` locates the fallback at the
index the generated `Func.call k` uses; at a concrete contract it is `rfl`. -/
theorem sound_of_dispatch {c : ContractSpec} {ca : Adr} {k : Nat}
    {funcs : List (B256 × Func)} {aux : List Func} {fallback : Func}
    (h_shape : c.prog = ⟨Func.mainWith k (DispatchTree.ofSorted funcs), aux⟩)
    (h_ne : funcs ≠ [])
    (h_fb : (c.prog.main :: aux)[k]? = some fallback)
    (h_funcs : ∀ p ∈ funcs, FuncSound c ca aux p.2)
    (h_fall : FuncSound c ca aux fallback) :
    c.Sound ca := by
  have h_aux : c.prog.aux = aux := by rw [h_shape]
  have h_main : c.prog.main = Func.mainWith k (DispatchTree.ofSorted funcs) := by rw [h_shape]
  have h_fs : Func.mainWith k (DispatchTree.ofSorted funcs) :: aux = c.prog.main :: aux := by
    rw [h_main]
  intro sevm pre post run h_ca ih h_pre
  -- `Sound` hands the deeper-frame hypothesis in its raw form; every consumer
  -- below wants the `ifOk`-wrapped one.
  have ih' : Exec.InvDepth sevm.depth ca c.prog (c.Pre ca) (c.Post ca) := by
    intro pc' sevm' devm' exn'
    cases exn'
    · simp only [ifOk, implies_true]
    · apply ih
  clear ih
  -- unwrap the initial `call 0` into a run of the program's own `main`
  dsimp only [Prog.Run] at run
  rw [h_aux] at run
  cases run
  rename (_ = _) => h_eq
  rename (Func.Run _ _ _ _ _) => run
  rename (Devm.Burn _ _) => burn
  rename Devm => s₀
  cases h_eq
  have h_pre₀ : c.Pre ca sevm s₀ := h_pre.state_eq burn.state.symm
  clear h_pre burn pre
  rw [h_main] at run
  -- run off the `fsig` prefix of `Func.mainWith`
  refine run_prepend_elim _ fsig ?_ run
  intro s₁ h₁ run₁
  have h_pre₁ : c.Pre ca sevm s₁ :=
    h_pre₀.of_eqs
      (congrFun (Line.of_inv Devm.getCode (by line_inv) h₁).symm ca)
      (Line.of_inv Devm.getBal (by line_inv) h₁).symm
      (congrFun (Line.of_inv Devm.getStor (by line_inv) h₁).symm ca)
  clear h_pre₀ h₁ run s₀
  rw [h_fs] at run₁
  exact post_of_run_dispatch h_ne h_fb h_funcs h_fall h_ca h_pre₁ ih' run₁

/-- `Sound` for the receive-aware public ingress used by wrapped-native-token
contracts.  Empty calldata takes `receive`; nonempty calldata runs the same
`fsig`/generated-dispatch protocol as `sound_of_dispatch`.  Successful receive,
fallback, and selector walks are reduced uniformly to `FuncSound`. -/
theorem sound_of_receive_dispatch {c : ContractSpec} {ca : Adr} {k : Nat}
    {funcs : List (B256 × Func)} {aux : List Func}
    {fallback receive : Func}
    (h_shape : c.prog =
      ⟨Ninst.calldatasize ::: Ninst.iszero :::
        (receive <?>
          (fsig +++ dispatchWith k (DispatchTree.ofSorted funcs))), aux⟩)
    (h_ne : funcs ≠ [])
    (h_fb : (c.prog.main :: aux)[k]? = some fallback)
    (h_funcs : ∀ p ∈ funcs, FuncSound c ca aux p.2)
    (h_fall : FuncSound c ca aux fallback)
    (h_receive : FuncSound c ca aux receive) :
    c.Sound ca := by
  have h_aux : c.prog.aux = aux := by rw [h_shape]
  have h_main : c.prog.main =
      Ninst.calldatasize ::: Ninst.iszero :::
        (receive <?>
          (fsig +++ dispatchWith k (DispatchTree.ofSorted funcs))) := by
    rw [h_shape]
  have h_ctx :
      (Ninst.calldatasize ::: Ninst.iszero :::
        (receive <?>
          (fsig +++ dispatchWith k (DispatchTree.ofSorted funcs)))) :: aux =
        c.prog.main :: aux := by
    rw [h_main]
  intro sevm pre post run h_ca ih h_pre
  have ih' : Exec.InvDepth sevm.depth ca c.prog (c.Pre ca) (c.Post ca) := by
    intro pc' sevm' devm' exn'
    cases exn'
    · simp only [ifOk, implies_true]
    · apply ih
  clear ih
  dsimp only [Prog.Run] at run
  rw [h_aux] at run
  cases run
  rename (_ = _) => h_eq
  rename (Func.Run _ _ _ _ _) => run
  rename (Devm.Burn _ _) => burn
  rename Devm => s₀
  cases h_eq
  have h_pre₀ : c.Pre ca sevm s₀ := h_pre.state_eq burn.state.symm
  clear h_pre burn pre
  rw [h_main] at run
  refine run_prepend_elim _ [Ninst.calldatasize, Ninst.iszero] ?_ run
  intro s₁ h₁ run₁
  have h_pre₁ : c.Pre ca sevm s₁ :=
    h_pre₀.of_eqs
      (congrFun (Line.of_inv Devm.getCode (by line_inv) h₁).symm ca)
      (Line.of_inv Devm.getBal (by line_inv) h₁).symm
      (congrFun (Line.of_inv Devm.getStor (by line_inv) h₁).symm ca)
  clear h_pre₀ h₁ run s₀
  rcases of_run_branch run₁ with
    ⟨s₂, h_pop, h_dispatch⟩ |
    ⟨w, s₂, s₃, h_ne_zero, h_pop, h_burn, h_receive_run⟩
  · rw [h_ctx] at h_dispatch
    refine run_prepend_elim _ fsig ?_ h_dispatch
    intro s₃ h_fsig h_dispatch'
    have h_pre₃ : c.Pre ca sevm s₃ :=
      (h_pre₁.state_eq h_pop.state.symm).of_eqs
        (congrFun (Line.of_inv Devm.getCode (by line_inv) h_fsig).symm ca)
        (Line.of_inv Devm.getBal (by line_inv) h_fsig).symm
        (congrFun (Line.of_inv Devm.getStor (by line_inv) h_fsig).symm ca)
    exact post_of_run_dispatch h_ne h_fb h_funcs h_fall
      h_ca h_pre₃ ih' h_dispatch'
  · rw [h_ctx] at h_receive_run
    exact h_receive h_ca
      (h_pre₁.state_eq (h_burn.state.symm.trans h_pop.state.symm))
      ih' h_receive_run



theorem StateInv.incrNonce {wa a : Adr} {w : Jaune.State}
    (h : c.StateInv wa w) : c.StateInv wa (w.incrNonce a) := by
  have hbal : (w.incrNonce a).bal = w.bal := by
    funext b
    show ((w.incrNonce a).get b).bal = (w.get b).bal
    by_cases hb : b = a
    · subst hb; simp only [State.incrNonce, State.get_set_self]
    · simp only [State.incrNonce, State.get_set_ne _ (Ne.symm hb)]
  have hstor : (w.incrNonce a).getStor wa = w.getStor wa := by
    show ((w.incrNonce a).get wa).stor = (w.get wa).stor
    by_cases hb : wa = a
    · subst hb; simp only [State.incrNonce, State.get_set_self]
    · simp only [State.incrNonce, State.get_set_ne _ (Ne.symm hb)]
  have hcode : (w.incrNonce a).getCode wa = w.getCode wa := by
    show ((w.incrNonce a).get wa).code = (w.get wa).code
    by_cases hb : wa = a
    · subst hb; simp only [State.incrNonce, State.get_set_self]
    · simp only [State.incrNonce, State.get_set_ne _ (Ne.symm hb)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hcode]; exact h.code
  · rw [hbal]; exact h.side
  · show c.Inv ((w.incrNonce a).getStor wa) 0 ((w.incrNonce a).bal wa)
    rw [hstor, hbal]; exact h.inv

-- `addBal` can only raise a balance: `code` (bal field only) survives, and both
-- the side condition and the invariant are moved by the `*_addBal` slots under
-- the pre-sum bound `sum w.bal + val < 2 ^ 256`, supplied by the caller's
-- wei-conservation argument (a bound on the *result* would not rule out a
-- wrap, so it is not enough).
theorem StateInv.addBal {ca a : Adr} {val : B256} {w : Jaune.State}
    (hsum : sum w.bal + val.toNat < 2 ^ 256)
    (h : c.StateInv ca w) : c.StateInv ca (w.addBal a val) := by
  refine ⟨?_, c.side_addBal hsum h.side, c.inv_addBal hsum h.side h.inv⟩
  show some (((w.addBal a val).get ca).code).toList = Prog.compile c.prog
  unfold State.addBal; rw [State.setBal_get_code]; exact h.code

-- `subBal` lowers a balance, so the side condition survives by `side_le`;
-- dropping `ca`'s balance could break the invariant, hence `a ≠ ca`.
theorem StateInv.subBal {ca a : Adr} {val : B256} {w w' : Jaune.State}
    (hne : a ≠ ca) (h_sub : w.subBal a val = some w')
    (h : c.StateInv ca w) : c.StateInv ca w' := by
  rcases State.of_subBal h_sub with ⟨h_le, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · show some (((w.setBal a (w.bal a - val)).get ca).code).toList = Prog.compile c.prog
    rw [State.setBal_get_code]; exact h.code
  · have hdec : Decrease a val w.bal (w.setBal a (w.bal a - val)).bal := by
      intro b; constructor
      · intro heq; subst heq
        show w.bal a - val = ((w.setBal a (w.bal a - val)).get a).bal
        rw [State.setBal_get_self]; rfl
      · intro hnb
        show w.bal b = ((w.setBal a (w.bal a - val)).get b).bal
        rw [State.setBal_get_ne hnb]; rfl
    have hsum := sum_sub_assoc hdec h_le
    exact c.side_le h.side (by omega)
  · show c.Inv (((w.setBal a (w.bal a - val)).get ca).stor) 0
      ((w.setBal a (w.bal a - val)).get ca).bal
    rw [State.setBal_get_stor, State.setBal_get_ne hne]; exact h.inv

-- Deleting a foreign account (`a ≠ ca`) removes its balance from the sum and
-- leaves `ca`'s code/balance/storage alone.
theorem StateInv.destroyAccount {ca a : Adr} {w : Jaune.State}
    (hne : a ≠ ca) (h : c.StateInv ca w) : c.StateInv ca (destroyAccount w a) := by
  have hget : (Jaune.destroyAccount w a).get ca = w.get ca :=
    State.get_erase_ne (Ne.symm hne)
  refine ⟨?_, ?_, ?_⟩
  · show some (((Jaune.destroyAccount w a).get ca).code).toList = Prog.compile c.prog
    rw [hget]; exact h.code
  · have h0 : ((Jaune.destroyAccount w a).get a).bal = 0 := by
      show (State.get (w.erase a) a).bal = 0
      unfold State.get
      rw [Std.TreeMap.getD_erase]; simp [Acct.nil]
    have hdec : Decrease a (w.bal a) w.bal (Jaune.destroyAccount w a).bal := by
      intro b; constructor
      · intro heq; subst heq
        show w.bal a - w.bal a = ((Jaune.destroyAccount w a).get a).bal
        rw [h0, B256.sub_self]
      · intro hnb
        show w.bal b = (State.get (w.erase a) b).bal
        rw [State.get_erase_ne (Ne.symm hnb)]; rfl
    have hsum := sum_sub_assoc hdec (le_refl _)
    exact c.side_le h.side (by omega)
  · show c.Inv (((Jaune.destroyAccount w a).get ca).stor) 0
      ((Jaune.destroyAccount w a).get ca).bal
    rw [hget]; exact h.inv

-- Folded form for the `accountsToDelete` set (post-linearization `foldl`).
-- This one is proved outright from the atomic lemma to exercise the pattern.
theorem StateInv.foldl_destroyAccount {wa : Adr} :
    ∀ {as : List Adr} {w : Jaune.State},
      (∀ a ∈ as, a ≠ wa) → c.StateInv wa w →
        c.StateInv wa (as.foldl Jaune.destroyAccount w)
  | [], _, _, h => h
  | a :: as, w, hne, h => by
    rw [List.foldl_cons]
    exact StateInv.foldl_destroyAccount
      (fun b hb => hne b (List.mem_cons_of_mem _ hb))
      (h.destroyAccount (hne a List.mem_cons_self))

-- `Devm.get{Bal,Stor,Code}` are by definition the corresponding `State.*`
-- projections of `devm.state`, so a `Post` plus code-preservation is exactly
-- `StateInv` on the underlying state.
lemma StateInv.of_postcond {ca : Adr} {sevm : Sevm} {devm : Devm}
    (h_post : c.Post ca sevm devm)
    (h_code : some (devm.state.getCode ca).toList = Prog.compile c.prog) :
    c.StateInv ca devm.state :=
  ⟨h_code, h_post.side, h_post.inv⟩

-- The `StateInv` counterpart of `Pre.child_of_transfer`: it only ever consults
-- the parent's `code`/`side`/value-free invariant, which are exactly the three
-- fields of `StateInv`.  `caller ≠ ca` is required so the credited value keeps
-- the invariant when `target = ca`.
lemma Pre.of_inv_transfer {ca : Adr} {sevm' : Sevm} {devm' : Devm}
    {st st_mid : Jaune.State} {caller target : Adr} {value : B256}
    (h_inv : c.StateInv ca st)
    (h_ne : caller ≠ ca)
    (h_sub : st.subBal caller value = some st_mid)
    (h_state : devm'.state = st_mid.addBal target value)
    (h_ct' : sevm'.currentTarget = target)
    (h_val : sevm'.currentTarget = ca → sevm'.value = value) :
    c.Pre ca sevm' devm' := by
  rcases of_state_transfer_fields (callee := target) h_sub with ⟨-, h_t_code, -, -, -⟩
  have h_stor' : Devm.getStor devm' ca = (st_mid.addBal target value).getStor ca := by
    show (devm'.state.get ca).stor = _
    rw [h_state]; rfl
  have h_bal' : devm'.getBal ca = (st_mid.addBal target value).bal ca := by
    show (devm'.state.get ca).bal = _
    rw [h_state]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · show some (devm'.state.get ca).code.toList = Prog.compile c.prog
    rw [h_state, h_t_code ca]; exact h_inv.code
  · show c.Side devm'.state.bal
    rw [h_state]; exact c.side_transfer h_sub h_inv.side
  · intro h_eq
    have h_t_ca : target = ca := h_ct'.symm.trans h_eq
    subst h_t_ca
    show c.Inv (Devm.getStor devm' target) sevm'.value (devm'.getBal target)
    rw [h_stor', h_bal', h_val h_eq]
    exact c.inv_recv_transfer h_sub h_ne h_inv.side h_inv.inv
  · intro _
    show c.Inv (Devm.getStor devm' ca) 0 (devm'.getBal ca)
    rw [h_stor', h_bal']
    exact c.inv_transfer h_sub h_ne h_inv.side h_inv.inv

-- No-transfer counterpart of `Pre.of_inv_transfer`: when no value moves,
-- the pre-state is the invariant state itself, and `PreSolvent` reduces to the
-- value-free solvency provided `value = 0` whenever the frame targets `wa`.
lemma Pre.of_inv_eqs {wa : Adr} {sevm : Sevm} {devm : Devm}
    (h_inv : c.StateInv wa devm.state)
    (h_val0 : sevm.currentTarget = wa → sevm.value = 0) :
    c.Pre wa sevm devm := by
  refine ⟨h_inv.code, h_inv.side, ?_, ?_⟩
  · intro h_eq
    rw [h_val0 h_eq]; exact h_inv.inv
  · intro _; exact h_inv.inv

-- The precondition for the sub-execution's initial `evm`, built directly from
-- the bare-state invariant across `benvAfterTransfer` (transfer / no-transfer).
lemma Pre.of_inv_benvAfterTransfer {wa : Adr} {msg : Msg} {benv : Benv}
    (h_ne : msg.shouldTransferValue = true → msg.caller ≠ wa)
    (h_val0 : msg.shouldTransferValue = false → msg.currentTarget = wa → msg.value = 0)
    (hb : msg.benvAfterTransfer = .ok benv)
    (h_inv : c.StateInv wa msg.benv.state) :
    c.Pre wa (initSevm (msg.withBenv benv)) (initDevm (msg.withBenv benv)) := by
  by_cases h_stv : msg.shouldTransferValue = true
  · rcases Blanc.of_benvAfterTransfer h_stv hb with ⟨st_mid, h_sub, hbenv⟩
    have hbs : (initDevm (msg.withBenv benv)).state
        = st_mid.addBal msg.currentTarget msg.value := by
      show benv.state = _; rw [hbenv]; rfl
    exact Pre.of_inv_transfer h_inv (h_ne h_stv) h_sub hbs rfl (fun _ => rfl)
  · have hbenv : benv = msg.benv := of_benvAfterTransfer_no h_stv hb
    have h_false : msg.shouldTransferValue = false := by
      cases hh : msg.shouldTransferValue
      · rfl
      · exact absurd hh h_stv
    have h_inv' : c.StateInv wa (initDevm (msg.withBenv benv)).state := by
      show c.StateInv wa benv.state; rw [hbenv]; exact h_inv
    exact Pre.of_inv_eqs h_inv' (fun he => h_val0 h_false he)

-- The post-transfer state itself still satisfies `StateInv`: the transfer only
-- credits `ca` or moves value between accounts other than `ca`, which is
-- exactly what `side_transfer` and `inv_transfer` say.
lemma StateInv.of_benvAfterTransfer {ca : Adr} {msg : Msg} {benv : Benv}
    (h_ne : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (hb : msg.benvAfterTransfer = .ok benv)
    (h_inv : c.StateInv ca msg.benv.state) :
    c.StateInv ca benv.state := by
  by_cases h_stv : msg.shouldTransferValue = true
  · rcases Blanc.of_benvAfterTransfer h_stv hb with ⟨st_mid, h_sub, hbenv⟩
    have hbs : benv.state = st_mid.addBal msg.currentTarget msg.value := by
      rw [hbenv]; rfl
    rcases of_state_transfer_fields (callee := msg.currentTarget) h_sub with
      ⟨-, h_t_code, -, -, -⟩
    rw [hbs]
    exact ⟨by rw [show ((st_mid.addBal msg.currentTarget msg.value).getCode ca)
                   = ((st_mid.addBal msg.currentTarget msg.value).get ca).code from rfl,
                 h_t_code ca]; exact h_inv.code,
           c.side_transfer h_sub h_inv.side,
           c.inv_transfer h_sub (h_ne h_stv) h_inv.side h_inv.inv⟩
  · have hbenv : benv = msg.benv := Blanc.of_benvAfterTransfer_no h_stv hb
    rw [hbenv]; exact h_inv

lemma StateInv.setStor_ne {wa a : Adr} {s : Stor} {w : Jaune.State}
    (hne : a ≠ wa) (h : c.StateInv wa w) : c.StateInv wa (w.setStor a s) := by
  have hget : (w.setStor a s).get wa = w.get wa := by
    unfold State.setStor; exact State.get_set_ne _ hne _
  refine ⟨?_, ?_, ?_⟩
  · show some (((w.setStor a s).get wa).code).toList = Prog.compile c.prog
    rw [hget]; exact h.code
  · rw [State.setStor_bal]; exact h.side
  · show c.Inv (((w.setStor a s).get wa).stor) 0 ((w.setStor a s).get wa).bal
    rw [hget]; exact h.inv

-- Likewise for installing code at a foreign account.
lemma StateInv.setCode_ne {wa a : Adr} {cd : ByteArray} {w : Jaune.State}
    (hne : a ≠ wa) (h : c.StateInv wa w) : c.StateInv wa (w.setCode a cd) := by
  have hget : (w.setCode a cd).get wa = w.get wa := by
    unfold State.setCode; exact State.get_set_ne _ hne _
  refine ⟨?_, ?_, ?_⟩
  · show some (((w.setCode a cd).get wa).code).toList = Prog.compile c.prog
    rw [hget]; exact h.code
  · rw [State.setCode_bal]; exact h.side
  · show c.Inv (((w.setCode a cd).get wa).stor) 0 ((w.setCode a cd).get wa).bal
    rw [hget]; exact h.inv

end ContractSpec

/-! ## The quantified open-contract layer

`~/plans/fmint-conserved.md` Step 6.  Two results sit here, both additive.

**The named statement** is `ContractSpec.preserves_of_dispatch` below: the
invariant of *any* dispatcher-shaped program all of whose targets satisfy
`FuncSound` is preserved by arbitrary executions — `sound_of_dispatch`
composed with `preserves_inv`, named so the quantified claim is a theorem
rather than a proof pattern.  `Blanc/Conserved.lean`'s `fmintSpec_preserves`
is its instantiation.

**Context stability** is the rest of the section.  `FuncSound` cannot be
weakened across a program extension directly — `Pre`'s `code` field pins
`Prog.compile c.prog`, and an extension changes the program's bytes — so
stability is stated over the *program-free core* (`Func.Core`) that a
storage-only invariant's non-reentrant obligations factor through.  The
engine is `Func.Run.mono`: the run relation consults its context only
through the `call` constructor's lookup, so contexts that agree at every
reachable index support the same runs.  `Func.Core.of_extended` is the
context-weakening theorem for the generator's append-only extension shape,
and `Func.Core.of_callFree` is the degenerate but common case — a target
with no `Func.call` at all has the same runs in *every* context.
`ContractSpec.funcSound_of_core` closes the loop: for a spec with trivial
`Side` and a storage-only `Inv`, a transported core re-enters `FuncSound`
against the *new* program with no re-walk. -/

/-- The call indices a `Func` mentions: `f.CallsIn P` holds iff every
`Func.call k` in `f`'s body has `P k`. -/
def Func.CallsIn (P : Nat → Prop) : Func → Prop
  | .branch f g => Func.CallsIn P f ∧ Func.CallsIn P g
  | .last _ => True
  | .next _ f => Func.CallsIn P f
  | .call k => P k

/-- The same, computably, for discharge at concrete programs. -/
def Func.callsIn (p : Nat → Bool) : Func → Bool
  | .branch f g => f.callsIn p && g.callsIn p
  | .last _ => true
  | .next _ f => f.callsIn p
  | .call k => p k

/-- A `Func` whose body contains no `Func.call` at all.  Every non-reentrant
fmint dispatch target is call-free; the contract's only `Func.call`s are
`flashLoan`'s two `burnSlot` tail jumps and the dispatcher's own. -/
abbrev Func.callFree : Func → Bool := Func.callsIn (fun _ => false)

theorem Func.CallsIn.of_callsIn {p : Nat → Bool} {P : Nat → Prop}
    (hp : ∀ k, p k = true → P k) {f : Func} (h : f.callsIn p = true) :
    Func.CallsIn P f := by
  induction f with
  | branch f g ihf ihg =>
      simp only [Func.callsIn, Bool.and_eq_true] at h
      exact ⟨ihf h.1, ihg h.2⟩
  | last _ => trivial
  | next _ f ih => exact ih h
  | call k => exact hp k h

/-- A call-free body satisfies any call-index predicate vacuously. -/
theorem Func.CallsIn.of_callFree {P : Nat → Prop} {f : Func}
    (h : Func.callFree f = true) : Func.CallsIn P f :=
  Func.CallsIn.of_callsIn (fun _ h' => nomatch h') h

/-- **Context transport for `Func.Run`.**  The run relation consults its
context only through the `call` constructor's lookup `fs[k]? = some g`, so
two contexts that agree at every index a derivation can reach support the
same runs.  `P` delimits the reachable indices: `f`'s own call indices
satisfy it (`h_f`), lookups at `P`-indices agree (`h_agree`), and the callee
at a `P`-index has its call indices inside `P` again (`h_closed`). -/
theorem Func.Run.mono {P : Nat → Prop} {fs fs' : List Func}
    (h_agree : ∀ k, P k → fs[k]? = fs'[k]?)
    (h_closed : ∀ k g, P k → fs[k]? = some g → Func.CallsIn P g)
    {sevm : Sevm} {s : Devm} {f : Func} {r : Devm}
    (h_f : Func.CallsIn P f) (h_run : Func.Run fs sevm s f r) :
    Func.Run fs' sevm s f r := by
  revert h_f
  induction h_run with
  | zero h1 _ ih => exact fun h_f => .zero h1 (ih h_f.1)
  | succ h1 h2 h3 _ ih => exact fun h_f => .succ h1 h2 h3 (ih h_f.2)
  | last h1 => exact fun _ => .last h1
  | next h1 _ ih => exact fun h_f => .next h1 (ih h_f)
  | call h_get h_burn _ ih =>
      exact fun h_f =>
        .call ((h_agree _ h_f).symm.trans h_get) h_burn (ih (h_closed _ _ h_f h_get))

/-- A call-free `Func` runs identically in every context: its derivation
never performs a lookup. -/
theorem Func.Run.of_callFree {fs fs' : List Func} {sevm : Sevm} {s : Devm}
    {f : Func} {r : Devm} (h_cf : Func.callFree f = true)
    (h_run : Func.Run fs sevm s f r) : Func.Run fs' sevm s f r :=
  Func.Run.mono (P := fun _ => False) (fun _ h => h.elim)
    (fun _ _ h => h.elim) (Func.CallsIn.of_callFree h_cf) h_run

/-- **Append-only extension, the generator's shape.**  An extension replaces
`main` (index 0) and appends to `aux`, so every old in-aux index resolves
identically; a target whose reachable call indices all point into the old
aux therefore has the same runs under the extended program.  Index 0 — the
dispatcher — is the one genuinely new resolution, which is why the index
predicate excludes it. -/
theorem Func.Run.of_extended {main main' : Func} {aux extra : List Func}
    {sevm : Sevm} {s : Devm} {f : Func} {r : Devm}
    (h_f : Func.CallsIn (fun k => 1 ≤ k ∧ k ≤ aux.length) f)
    (h_aux : ∀ g ∈ aux, Func.CallsIn (fun k => 1 ≤ k ∧ k ≤ aux.length) g)
    (h_run : Func.Run (main' :: (aux ++ extra)) sevm s f r) :
    Func.Run (main :: aux) sevm s f r := by
  refine Func.Run.mono (P := fun k => 1 ≤ k ∧ k ≤ aux.length) ?_ ?_ h_f h_run
  · rintro k ⟨h1, h2⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [List.getElem?_cons_succ]
    exact List.getElem?_append_left (by omega)
  · rintro k g ⟨h1, h2⟩ h_get
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [List.getElem?_cons_succ, List.getElem?_append_left (by omega)] at h_get
    exact h_aux g (List.mem_of_getElem? h_get)

/-- The program-free core of a per-target obligation: `f`'s successful walk
preserves `Q` at the frame's own target.  No `Pre`, no code equation, no
deeper-frame hypothesis — the shape that survives program extension, and the
shape `Blanc/Conserved.lean`'s `fmintSpec_funcSound` consumes. -/
def Func.Core (fs : List Func) (Q : Stor → Prop) (f : Func) : Prop :=
  ∀ {sevm : Sevm} {s r : Devm},
    Func.Run fs sevm s f r →
    Q (Devm.getStor s sevm.currentTarget) →
    Q (Devm.getStor r sevm.currentTarget)

/-- **The context-weakening theorem** over the program-free core, for the
fixed generator shape: a core proved at `main :: aux` holds verbatim at any
extension `main' :: (aux ++ extra)`. -/
theorem Func.Core.of_extended {main main' : Func} {aux extra : List Func}
    {Q : Stor → Prop} {f : Func}
    (h_f : Func.CallsIn (fun k => 1 ≤ k ∧ k ≤ aux.length) f)
    (h_aux : ∀ g ∈ aux, Func.CallsIn (fun k => 1 ≤ k ∧ k ≤ aux.length) g)
    (h : Func.Core (main :: aux) Q f) :
    Func.Core (main' :: (aux ++ extra)) Q f :=
  fun {_ _ _} h_run hq => h (Func.Run.of_extended h_f h_aux h_run) hq

/-- A call-free core is context-universal. -/
theorem Func.Core.of_callFree {fs fs' : List Func} {Q : Stor → Prop}
    {f : Func} (h_cf : Func.callFree f = true) (h : Func.Core fs Q f) :
    Func.Core fs' Q f :=
  fun {_ _ _} h_run hq => h (Func.Run.of_callFree h_cf h_run) hq

namespace ContractSpec

/-- **The quantified open-contract statement**: the invariant of any
dispatcher-shaped program all of whose targets satisfy `FuncSound` is
preserved by arbitrary executions — including arbitrary reentrant callback
code, which is what `FuncSound`'s deeper-frame hypothesis carries.
`sound_of_dispatch` composed with `preserves_inv`; fmint instantiates it
(`Blanc/Conserved.lean`, `fmintSpec_preserves`) with twelve discharged
obligations and a vacuous fallback. -/
theorem preserves_of_dispatch {c : ContractSpec} {ca : Adr}
    {k : Nat} {funcs : List (B256 × Func)} {aux : List Func} {fallback : Func}
    (h_shape : c.prog = ⟨Func.mainWith k (DispatchTree.ofSorted funcs), aux⟩)
    (h_ne : funcs ≠ [])
    (h_fb : (c.prog.main :: aux)[k]? = some fallback)
    (h_funcs : ∀ p ∈ funcs, c.FuncSound ca aux p.2)
    (h_fall : c.FuncSound ca aux fallback) :
    c.Preserves ca :=
  c.preserves_inv ca (sound_of_dispatch h_shape h_ne h_fb h_funcs h_fall)

/-- The receive-aware counterpart of `preserves_of_dispatch`.  It adds exactly
one contract obligation: `FuncSound` for the empty-calldata receive target. -/
theorem preserves_of_receive_dispatch {c : ContractSpec} {ca : Adr}
    {k : Nat} {funcs : List (B256 × Func)} {aux : List Func}
    {fallback receive : Func}
    (h_shape : c.prog =
      ⟨Ninst.calldatasize ::: Ninst.iszero :::
        (receive <?>
          (fsig +++ dispatchWith k (DispatchTree.ofSorted funcs))), aux⟩)
    (h_ne : funcs ≠ [])
    (h_fb : (c.prog.main :: aux)[k]? = some fallback)
    (h_funcs : ∀ p ∈ funcs, c.FuncSound ca aux p.2)
    (h_fall : c.FuncSound ca aux fallback)
    (h_receive : c.FuncSound ca aux receive) :
    c.Preserves ca :=
  c.preserves_inv ca
    (sound_of_receive_dispatch h_shape h_ne h_fb h_funcs h_fall h_receive)

/-- A storage-only invariant's per-target obligation is exactly its
program-free core: for a spec whose `Side` is trivial and whose `Inv`
ignores the callvalue and balance arguments, `FuncSound` follows from
`Func.Core` alone.  This is how a transported core re-enters the extended
contract's obligations without a re-walk. -/
theorem funcSound_of_core {c : ContractSpec} {ca : Adr}
    {aux : List Func} {f : Func}
    (h_side : ∀ bal, c.Side bal)
    (h_stor : ∀ {s : Stor} {v b v' b' : B256}, c.Inv s v b → c.Inv s v' b')
    (h_core : Func.Core (c.prog.main :: aux) (fun st => c.Inv st 0 0) f) :
    c.FuncSound ca aux f := by
  intro sevm s r h_ct h_pre _ h_run
  subst h_ct
  exact ⟨h_side _, h_stor (h_core h_run (h_stor (h_pre.inv.1 rfl)))⟩

end ContractSpec

/-! ## Generic message-, transaction- and block-level plumbing

Moved down from `Solvent.lean`, unchanged: the no-deletion (`NoDel`) tier, the
`setDelegation` frame algebra, the transaction-level affordability helpers and
the wei-conservation (`sum_le`) tier.  None of it mentions the contract. -/

lemma of_executeCode_cases {msg : Msg} {xl : Xlot}
    {ex : Except (EvmError × Jaune.State × AdrSet × Tra) Devm}
    (h : ExecuteCode msg xl ex) :
    (∃ adr, executeCode.handleError (executePrecomp (initEvm msg) adr) = ex) ∨
    (∃ ex', xl = .some ⟨initEvm msg, ex'⟩ ∧
      executeCode.handleError ex' = ex) := by
  rcases h_ca : msg.codeAddress with _ | adr
  · refine Or.inr ?_
    unfold ExecuteCode executeCode.enter at h
    simp only [h_ca] at h
    rcases h with ⟨ex', hxl, hh⟩
    exact ⟨ex', hxl, hh.symm⟩
  · rcases of_executeCode_someCode h_ca h with ⟨_, _, h'⟩ | ⟨_, ex', h1, h2⟩
    · exact Or.inl ⟨adr, h'⟩
    · exact Or.inr ⟨ex', h1, h2⟩

lemma ExecuteCode.inv_noDel {wa : Adr} {msg : Msg} {xl : Xlot}
    {ex : Except (EvmError × Jaune.State × AdrSet × Tra) Devm}
    (inv : Xlot.InvNoDel wa xl)
    (run : ExecuteCode msg xl ex)
    (h : Msg.NoDel wa msg) : MsgResult.NoDel wa ex := by
  rcases of_executeCode_cases run with ⟨adr, h_precomp⟩ | ⟨ex', h_xl, h_err⟩
  · have h_init : Devm.NoDel wa (initDevm msg) := Msg.NoDel.initDevm h
    have h_ex_noDel : Execution.NoDel wa (executePrecomp (initEvm msg) adr) := executePrecomp_noDel rfl h_init
    rw [← h_precomp]
    exact handleError_noDel h_ex_noDel
  · rw [h_xl] at inv
    dsimp [Xlot.InvNoDel] at inv
    have h_init : Devm.NoDel wa (initDevm msg) := Msg.NoDel.initDevm h
    have h_ex'_noDel : Execution.NoDel wa ex' := inv h_init
    rw [← h_err]
    exact handleError_noDel h_ex'_noDel

lemma ProcessMessage.inv_noDel {wa : Adr} {msg : Msg} {xl : Xlot}
    {ex : Except (EvmError × Jaune.State × AdrSet × Tra) Devm}
    (inv : Xlot.InvNoDel wa xl)
    (run : ProcessMessage msg xl ex)
    (h : Msg.NoDel wa msg) : MsgResult.NoDel wa ex := by
  obtain ⟨r0, hbody, rfl⟩ := ProcessMessage.iff_body.mp run
  unfold FrameBody at hbody
  rcases eq_bt : msg.benvAfterTransfer with e | benv' <;> rw [eq_bt] at hbody
  · rw [hbody.2, processMessage.settle_error]
    exact Msg.NoDel.benvAfterTransfer_err eq_bt h
  · have h_nof' : Msg.NoDel wa (msg.withBenv benv') := Msg.NoDel.benvAfterTransfer eq_bt h
    have h_exec : MsgResult.NoDel wa r0 := ExecuteCode.inv_noDel inv hbody h_nof'
    unfold processMessage.settle
    rcases r0 with x | evm2
    · exact h_exec
    · dsimp only [bind, Except.bind]
      split
      · exact Devm.NoDel.rollback h_exec.atd h_exec.ca h.code
      · exact h_exec

lemma ProcessCreateMessage.inv_noDel {wa : Adr} {msg : Msg} {xl : Xlot}
    {ex : Except (EvmError × Jaune.State × AdrSet × Tra) Devm}
    (inv : Xlot.InvNoDel wa xl)
    (run : ProcessCreateMessage msg xl ex)
    (h_ct : msg.currentTarget ≠ wa)
    (h : Msg.NoDel wa msg) : MsgResult.NoDel wa ex := by
  obtain ⟨ex', run_pm, rfl⟩ := ProcessCreateMessage.iff_processMessage.mp run
  have h_seed : Msg.NoDel wa (processCreateMessage.msg msg) :=
    Msg.NoDel.processCreateMessage_msg h_ct h
  have h_pm : MsgResult.NoDel wa ex' :=
    ProcessMessage.inv_noDel inv run_pm h_seed
  unfold processCreateMessage.settle
  rcases ex' with x | evm
  · exact h_pm
  · have h_evm : Devm.NoDel wa evm := h_pm
    dsimp only [bind, Except.bind]
    by_cases h_err : evm.error.isNone = true
    · rw [if_pos h_err]
      cases h_cg : processCreateMessage.chargeCodeGas msg.benv.stat.rules evm with
      | error e =>
        rcases e with ⟨err, evm'⟩
        have h_ds : Devm.delSets evm' = Devm.delSets evm := chargeCodeGas_delSets_err h_cg
        have h_atd_eq : evm'.accountsToDelete = evm.accountsToDelete := congrArg Prod.fst h_ds
        have h_ca_eq : evm'.createdAccounts = evm.createdAccounts := congrArg Prod.snd h_ds
        have h_atd : wa ∉ evm'.accountsToDelete := by rw [h_atd_eq]; exact h_evm.atd
        have h_ca : wa ∉ evm'.createdAccounts := by rw [h_ca_eq]; exact h_evm.ca
        have h_gc : evm'.getCode wa = evm.getCode wa := by
          have hh := processCreateMessage.chargeCodeGas_getCode_gen h_cg wa
          simpa only [Execution.getCode] using hh
        cases err
        case halt reason => exact ⟨h_atd, h_ca, h.code⟩
        all_goals
          refine ⟨h_ca, ?_⟩
          show (evm'.state.getCode wa).toList ≠ []
          rw [← Devm.getCode_state, h_gc]
          exact h_evm.code
      | ok evm' =>
        dsimp only []
        have h_ds : Devm.delSets evm' = Devm.delSets evm := chargeCodeGas_delSets_ok h_cg
        have h_atd_eq : evm'.accountsToDelete = evm.accountsToDelete := congrArg Prod.fst h_ds
        have h_ca_eq : evm'.createdAccounts = evm.createdAccounts := congrArg Prod.snd h_ds
        have h_atd : wa ∉ evm'.accountsToDelete := by rw [h_atd_eq]; exact h_evm.atd
        have h_ca : wa ∉ evm'.createdAccounts := by rw [h_ca_eq]; exact h_evm.ca
        have h_gc : evm'.getCode wa = evm.getCode wa := by
          have hh := processCreateMessage.chargeCodeGas_getCode_gen h_cg wa
          simpa only [Execution.getCode] using hh
        refine ⟨h_atd, h_ca, ?_⟩
        show ((evm'.setCode msg.currentTarget ⟨⟨evm'.output⟩⟩).getCode wa).toList ≠ []
        rw [setCode_getCode h_ct, h_gc]
        exact h_pm.code
    · rw [if_neg h_err]
      exact Devm.NoDel.rollback h_pm.atd h_pm.ca h.code

lemma Devm.NoDel.of_instructionFrame {wa : Adr} {d d' : Devm}
    (hf : Devm.InstructionFrame d d') (h : Devm.NoDel wa d) : Devm.NoDel wa d' :=
  Devm.NoDel.of_eqs hf.delSets (hf.getCode wa) h

lemma Execution.NoDel.of_instructionFrame {wa : Adr} {d : Devm} {ex : Execution}
    (hf : Execution.Rel Devm.InstructionFrame d ex) (h : Devm.NoDel wa d) :
    Execution.NoDel wa ex := by
  cases ex with
  | error e => exact Devm.NoDel.of_instructionFrame hf h
  | ok d' => exact Devm.NoDel.of_instructionFrame hf h

/-- The CALL-family return path preserves the no-deletion invariant. -/
lemma Resume.call_noDel {wa : Adr} {parent : Devm} {oi os : Nat}
    {r : Except (EvmError × Jaune.State × AdrSet × Tra) Devm}
    (hnd : Devm.NoDel wa parent) (h : MsgResult.NoDel wa r) :
    Execution.NoDel wa ((Resume.call parent oi os).run r) := by
  unfold Resume.run liftToExecution
  rcases r with ⟨e_str, e_st, e_ca, e_tra⟩ | child <;> dsimp only [bind, Except.bind]
  · rcases h with ⟨h_ca, h_code⟩
    exact ⟨hnd.atd, h_ca, h_code⟩
  · have h_child : Devm.NoDel wa child := h
    split
    · rcases hp : (incorporateChildOnError parent child child.output).push 0 with e | evm2
      · exact Devm.push_noDel hp (incorporateChildOnError_noDel hnd.atd h_child)
      · exact Devm.NoDel.of_eqs (Devm.push_delSets_eq hp).symm
          (Devm.push_getCode_gen hp wa).symm
          (incorporateChildOnError_noDel hnd.atd h_child)
    · rcases hp : (incorporateChildOnSuccess parent child child.output).push 1 with e | evm2
      · exact Devm.push_noDel hp (incorporateChildOnSuccess_noDel hnd.atd h_child)
      · exact Devm.NoDel.of_eqs (Devm.push_delSets_eq hp).symm
          (Devm.push_getCode_gen hp wa).symm
          (incorporateChildOnSuccess_noDel hnd.atd h_child)

/-- The CREATE-family return path preserves the no-deletion invariant. -/
lemma Resume.create_noDel {wa : Adr} {parent : Devm} {newAddress : Adr}
    {r : Except (EvmError × Jaune.State × AdrSet × Tra) Devm}
    (hnd : Devm.NoDel wa parent) (h : MsgResult.NoDel wa r) :
    Execution.NoDel wa ((Resume.create parent newAddress).run r) := by
  unfold Resume.run liftToExecution
  rcases r with ⟨e_str, e_st, e_ca, e_tra⟩ | child <;> dsimp only [bind, Except.bind]
  · rcases h with ⟨h_ca, h_code⟩
    exact ⟨hnd.atd, h_ca, h_code⟩
  · have h_child : Devm.NoDel wa child := h
    split
    · exact Devm.push_noDel rfl (incorporateChildOnError_noDel hnd.atd h_child)
    · exact Devm.push_noDel rfl (incorporateChildOnSuccess_noDel hnd.atd h_child)

lemma GenericCall.inv_noDel {wa : Adr} {sevm : Sevm} {devm : Devm}
    {gas : Nat} {value : B256} {caller target codeAddress : Adr}
    {stv istat : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    {xl : Xlot} {exn : Execution}
    (inv : Xlot.InvNoDel wa xl)
    (h : GenericCall sevm devm gas value caller target codeAddress
      stv istat ii is oi os code dp xl exn)
    (hnd : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  unfold GenericCall genericCall.step at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  repeat' split at h
  all_goals simp only [XStep.ofExcept, XStep.Run] at h
  -- depth-zero early exit, push failed
  · obtain ⟨-, rfl⟩ := h
    rename_i heq
    exact Devm.push_noDel heq ⟨hnd.atd, hnd.ca, hnd.code⟩
  -- depth-zero early exit, push succeeded
  · obtain ⟨-, rfl⟩ := h
    rename_i heq
    exact Devm.push_noDel heq ⟨hnd.atd, hnd.ca, hnd.code⟩
  -- the child frame is entered
  · obtain ⟨r, hframe, rfl⟩ := h
    exact Resume.call_noDel ⟨hnd.atd, hnd.ca, hnd.code⟩
      (ProcessMessage.inv_noDel inv hframe ⟨hnd.ca, hnd.code⟩)

lemma GenericCreate.inv_noDel {wa : Adr} {sevm : Sevm} {devm : Devm}
    {endowment : B256} {newAddress : Adr} {mi ms : Nat}
    {xl : Xlot} {exn : Execution}
    (inv : Xlot.InvNoDel wa xl)
    (h : GenericCreate sevm devm endowment newAddress mi ms xl exn)
    (hnd : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  have hnd5 : Devm.NoDel wa
      (addAccessedAddress
        (((devm.withGasLeft (devm.gasLeft - except64th devm.gasLeft)).withReturnData
          []).incrNonce sevm.currentTarget) newAddress) := by
    refine Devm.NoDel.of_eqs (d := devm) rfl ?_ hnd
    rw [addAccessedAddress_getCode]
    exact Devm.incrNonce_getCode.symm
  unfold GenericCreate genericCreate.step at h
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic, Pure.pure,
    Except.pure] at h
  repeat' split at h
  all_goals simp only [XStep.ofExcept, XStep.Run] at h
  -- init-code-size assertion failed
  · obtain ⟨-, rfl⟩ := h
    rename_i heq
    split at heq <;> cases heq
    exact hnd
  -- static-context assertion failed
  · obtain ⟨-, rfl⟩ := h
    rename_i heq
    split at heq <;> cases heq
    exact Devm.NoDel.of_eqs (d := devm) rfl rfl hnd
  -- balance / max-nonce / depth-zero early exit, push failed
  · obtain ⟨-, rfl⟩ := h
    rename_i heq
    exact Devm.push_noDel heq ⟨hnd.atd, hnd.ca, hnd.code⟩
  -- balance / max-nonce / depth-zero early exit, push succeeded
  · obtain ⟨-, rfl⟩ := h
    rename_i heq
    exact Devm.push_noDel heq ⟨hnd.atd, hnd.ca, hnd.code⟩
  -- address-collision early exit, push failed
  · obtain ⟨-, rfl⟩ := h
    rename_i heq
    exact Devm.push_noDel heq hnd5
  -- address-collision early exit, push succeeded
  · obtain ⟨-, rfl⟩ := h
    rename_i heq
    exact Devm.push_noDel heq hnd5
  -- the child frame is entered
  · rename_i h_c2
    obtain ⟨r, hframe, rfl⟩ := h
    have h_ct : newAddress ≠ wa := by
      push Not at h_c2
      exact ne_wa_of_code_size_zero hnd5.code h_c2.2.1
    exact Resume.create_noDel hnd5
      (ProcessCreateMessage.inv_noDel inv hframe h_ct ⟨hnd5.ca, hnd5.code⟩)

lemma Xinst.inv_noDel_gen {wa : Adr} {sevm : Sevm} {s : Devm} {x : Xinst}
    {xl : Xlot} {exn : Execution}
    (inv : Xlot.InvNoDel wa xl)
    (h : Xinst.Run sevm s x xl exn)
    (hnd : Devm.NoDel wa s) : Execution.NoDel wa exn := by
  unfold Xinst.Run at h
  rcases Xinst.step_shape sevm s x with ⟨ex, hs, hframe⟩ |
    ⟨d, e, na, mi, ms, hf, hs⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, -, -, hs⟩ <;> rw [hs] at h
  · obtain ⟨-, rfl⟩ := h
    exact Execution.NoDel.of_instructionFrame hframe hnd
  · exact GenericCreate.inv_noDel inv h (Devm.NoDel.of_instructionFrame hf hnd)
  · exact GenericCall.inv_noDel inv h (Devm.NoDel.of_instructionFrame hf hnd)


lemma Ninst.inv_noDel_gen {wa : Adr} {pc : Nat} {sevm : Sevm} {devm : Devm}
    {n : Ninst} {xl : Xlot} {exn : Execution}
    (inv : Xlot.InvNoDel wa xl)
    (run : Ninst.StepRun pc sevm devm n xl exn)
    (h : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  cases n with
  | push xs le =>
    simp only [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at run
    obtain ⟨-, rfl⟩ := run
    · cases h_charge : chargeGas (if xs = [] then gBase else gVerylow) devm
      case error err =>
        exact Devm.NoDel.of_eqs (chargeGas_delSets_err h_charge).symm (chargeGas_getCode_err h_charge wa).symm h
      case ok d1 =>
        have h1 : Devm.NoDel wa d1 := Devm.NoDel.of_eqs (chargeGas_delSets_eq h_charge).symm (chargeGas_getCode_eq h_charge wa).symm h
        dsimp only [bind, Except.bind]
        cases h_push : Devm.push xs.toB256 d1
        case error err2 =>
          exact Devm.NoDel.of_eqs (Devm.push_delSets_err h_push).symm (Devm.push_getCode_err h_push wa).symm h1
        case ok d2 =>
          exact Devm.NoDel.of_eqs (Devm.push_delSets_eq h_push).symm (Devm.push_getCode_eq h_push wa).symm h1
  | reg rg =>
    simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at run
    obtain ⟨-, rfl⟩ := run
    · cases h_run : Rinst.run { pc := pc, sta := sevm, dyna := devm } rg
      case error err =>
        exact Devm.NoDel.of_eqs (Rinst.inv_delSets_err h_run).symm (Rinst.preserves_getCode_err h_run wa).symm h
      case ok d1 =>
        exact Devm.NoDel.of_eqs (Rinst.inv_delSets h_run) (Rinst.preserves_getCode h_run wa).symm h
  | exec xinst =>
    simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at run
    exact Xinst.inv_noDel_gen (x := xinst) inv run h

-- The composite relation carried through `Exec.effect` for the NoDel invariant.
def Devm.NoDelCode (wa : Adr) (pre post : Devm) : Prop :=
  Devm.NoDel wa pre → Devm.NoDel wa post

lemma noDelCode_refl_trans (wa : Adr) :
    ReflexiveRel (Devm.NoDelCode wa) ∧ TransitiveRel (Devm.NoDelCode wa) := by
  constructor
  · exact fun _ => id
  · intro a b c hab hbc
    exact fun h => hbc (hab h)

lemma Xlot.invNoDel_of_rel {wa : Adr} {xl : Xlot}
    (h : Xlot.Rel (Devm.NoDelCode wa) xl) : Xlot.InvNoDel wa xl := by
  rcases xl with _ | ⟨evm, exn⟩
  · trivial
  · intro hnd
    cases exn with
    | error e => exact h hnd
    | ok d => exact h hnd

lemma Ninst.noDelCode_effectRec (wa : Adr) (n : Ninst) :
    Ninst.EffectRec (Devm.NoDelCode wa) n := by
  intro pc sevm pre xl out hxl hrun
  have hnd := fun h =>
    Ninst.inv_noDel_gen (Xlot.invNoDel_of_rel hxl) hrun h
  cases out with
  | error e => exact hnd
  | ok d => exact hnd

lemma Jinst.noDelCode_effect (wa : Adr) (j : Jinst) :
    Jinst.Effect (Devm.NoDelCode wa) j := by
  intro evm out hrun
  rcases evm with ⟨pc, sevm, devm⟩
  have hcode := Jinst.preserves_getCode_gen hrun
  cases out with
  | error e =>
    rcases e with ⟨err, devm'⟩
    refine fun h => ?_
    exact Devm.NoDel.of_eqs (Jinst.inv_delSets_err hrun).symm (hcode wa).symm h
  | ok v =>
    rcases v with ⟨pc', devm'⟩
    refine fun h => ?_
    exact Devm.NoDel.of_eqs (Jinst.inv_delSets hrun).symm (hcode wa).symm h

lemma Linst.noDelCode_effect (wa : Adr) (l : Linst) :
    Linst.Effect (Devm.NoDelCode wa) l := by
  intro sevm pre out hrun
  have hnd := Linst.inv_noDel (wa := wa) hrun
  cases out with
  | error e => exact hnd
  | ok d => exact hnd

lemma Exec.inv_noDel {wa : Adr} {pc : Nat} {sevm : Sevm} {devm : Devm}
    {exn : Execution}
    (run : Exec pc sevm devm exn)
    (h : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  have heff := Exec.effect (noDelCode_refl_trans wa).1 (noDelCode_refl_trans wa).2
    (Ninst.noDelCode_effectRec wa) (Jinst.noDelCode_effect wa)
    (Linst.noDelCode_effect wa) run
  cases exn with
  | error e => exact heff h
  | ok d => exact heff h

theorem processMessage_preserves_noDel {wa : Adr} {msg : Msg} {evm : Devm}
    (h_run : processMessage msg = .ok evm)
    (h : Msg.NoDel wa msg) : Devm.NoDel wa evm := by
  obtain ⟨xl, hfill, hrel⟩ := of_processMessage msg (.ok evm) h_run
  have hinv : Xlot.InvNoDel wa xl := by
    rcases xl with _ | ⟨cevm, cexn⟩
    · trivial
    · intro hnd
      obtain ⟨exc⟩ := hfill
      exact Exec.inv_noDel exc hnd
  exact ProcessMessage.inv_noDel hinv hrel h

theorem processCreateMessage_preserves_noDel {wa : Adr} {msg : Msg} {evm : Devm}
    (h_run : processCreateMessage msg = .ok evm)
    (h_ct : msg.currentTarget ≠ wa)
    (h : Msg.NoDel wa msg) : Devm.NoDel wa evm := by
  rw [processCreateMessage_eq] at h_run
  have h_inv_cm : Msg.NoDel wa (processCreateMessage.msg msg) :=
    Msg.NoDel.processCreateMessage_msg h_ct h
  rcases hpm0 : processMessage (processCreateMessage.msg msg) with x | evm2
  · rw [hpm0, processCreateMessage.settle_error] at h_run
    cases h_run
  rw [hpm0] at h_run
  have h_rest := h_run
  have h_pm : Devm.NoDel wa evm2 := processMessage_preserves_noDel hpm0 h_inv_cm
  unfold processCreateMessage.settle at h_rest
  dsimp only [bind, Except.bind] at h_rest
  · by_cases herr : evm2.error.isNone = true
    · rw [if_pos herr] at h_rest
      rcases hcg : processCreateMessage.chargeCodeGas msg.benv.stat.rules evm2
        with ⟨err, evm3⟩ | evm3
      · rw [hcg] at h_rest
        cases err
        case halt reason =>
          rw [← Except.ok.inj h_rest]
          have h_ds : Devm.delSets evm3 = Devm.delSets evm2 := chargeCodeGas_delSets_err hcg
          have h_atd_eq : evm3.accountsToDelete = evm2.accountsToDelete := congrArg Prod.fst h_ds
          have h_ca_eq : evm3.createdAccounts = evm2.createdAccounts := congrArg Prod.snd h_ds
          have h_atd : wa ∉ evm3.accountsToDelete := by rw [h_atd_eq]; exact h_pm.atd
          have h_ca : wa ∉ evm3.createdAccounts := by rw [h_ca_eq]; exact h_pm.ca
          unfold processCreateMessage.exceptionalHalt
          exact Devm.NoDel.of_eqs (d := evm3.rollback msg.benv.state msg.tenv.transientStorage) rfl rfl (Devm.NoDel.rollback h_atd h_ca h.code)
        all_goals cases h_rest
      · rw [hcg] at h_rest; dsimp only at h_rest
        rw [← Except.ok.inj h_rest]
        have h_ds : Devm.delSets evm3 = Devm.delSets evm2 := chargeCodeGas_delSets_ok hcg
        have h_atd_eq : evm3.accountsToDelete = evm2.accountsToDelete := congrArg Prod.fst h_ds
        have h_ca_eq : evm3.createdAccounts = evm2.createdAccounts := congrArg Prod.snd h_ds
        have h_atd : wa ∉ evm3.accountsToDelete := by rw [h_atd_eq]; exact h_pm.atd
        have h_ca : wa ∉ evm3.createdAccounts := by rw [h_ca_eq]; exact h_pm.ca
        have h_gc : evm3.getCode wa = evm2.getCode wa := by
          have hh := processCreateMessage.chargeCodeGas_getCode_gen hcg wa
          simpa only [Execution.getCode] using hh
        refine ⟨h_atd, h_ca, ?_⟩
        show ((evm3.setCode msg.currentTarget ⟨⟨evm3.output⟩⟩).getCode wa).toList ≠ []
        rw [setCode_getCode h_ct, h_gc]
        exact h_pm.code
    · rw [if_neg herr] at h_rest
      rw [← Except.ok.inj h_rest]
      exact Devm.NoDel.rollback h_pm.atd h_pm.ca h.code

lemma setDelegationStep_benv_equiv {auth : Auth} {msg msg' : Msg} {refund refund' : B256}
    (h : setDelegationStep auth msg refund = .ok (msg', refund')) :
    Benv.EquivForDelegation msg.benv msg'.benv := by
  unfold setDelegationStep at h
  split at h
  · injection h with h1; injection h1 with h2 h3; subst h2
    exact Benv.EquivForDelegation_refl _
  · split at h
    · injection h with h1; injection h1 with h2 h3; subst h2
      exact Benv.EquivForDelegation_refl _
    · split at h
      · injection h with h1; injection h1 with h2 h3; subst h2
        exact Benv.EquivForDelegation_refl _
      · contradiction
      · rename_i authority heq
        dsimp only at h
        split at h
        · injection h with h1; injection h1 with h2 h3; subst h2
          exact Benv.EquivForDelegation_refl _
        · split at h
          · injection h with h1; injection h1 with h2 h3; subst h2
            exact Benv.EquivForDelegation_refl _
          · injection h with h1; injection h1 with h_msg h_refund
            subst h_msg
            refine ⟨rfl, fun a ha h_not_del => ?_⟩
            have h_ne : authority ≠ a := by
              intro h_eq
              subst a
              by_cases h_empty :
                  (msg.benv.state.get authority).code.isEmpty = true
              · have h_size :
                    (msg.benv.state.get authority).code.size = 0 := by
                  simpa [ByteArray.isEmpty] using h_empty
                exact (ne_wa_of_code_size_zero ha h_size) rfl
              · have h_valid :
                    isValidDelegation (msg.benv.state.get authority).code := by
                  simp_all
                exact h_not_del (by simpa [State.getCode] using h_valid)
            change ((_ : Msg).benv.incrNonce authority).state.getCode a = _
            rw [Benv.incrNonce_getCode]
            dsimp [Msg.setCode, State.getCode]
            rw [State.setCode_get_code_ne h_ne]

lemma setDelegationLoop_benv_equiv {auths : List Auth} {msg msg' : Msg} {refund refund' : B256}
    (h : setDelegationLoop auths msg refund = .ok (msg', refund')) :
    Benv.EquivForDelegation msg.benv msg'.benv := by
  induction auths generalizing msg refund with
  | nil =>
    injection h with h1; injection h1 with h2 h3; subst h2
    exact Benv.EquivForDelegation_refl _
  | cons auth auths_tail ih =>
    unfold setDelegationLoop at h
    rcases Except.bind_eq_ok h with ⟨⟨msg1, refund1⟩, h_step, h_tail⟩
    have h_equiv1 := setDelegationStep_benv_equiv h_step
    have h_equiv2 := ih h_tail
    exact Benv.EquivForDelegation_trans h_equiv1 h_equiv2

lemma setDelegation_benv_equiv {msg msg' : Msg} {v : B256}
    (h_run : setDelegation msg = .ok ⟨msg', v⟩) :
    Benv.EquivForDelegation msg.benv msg'.benv := by
  unfold setDelegation at h_run
  dsimp [bind, Except.bind] at h_run
  apply Except.bind_eq_ok at h_run
  rcases h_run with ⟨⟨msg_mid, refundCounter⟩, h_loop, h_rest⟩
  have h_eq_benv : msg_mid.benv = msg'.benv := by
    dsimp only at h_rest
    split at h_rest
    · contradiction
    · simpa using congrArg Msg.benv (congrArg Prod.fst (Except.ok.inj h_rest))
  rw [← h_eq_benv]
  exact setDelegationLoop_benv_equiv h_loop

theorem setDelegation_msg_noDel {wa : Adr} {msg msg' : Msg} {v : B256}
    (h_run : setDelegation msg = .ok ⟨msg', v⟩)
    (h : Msg.NoDel wa msg)
    (h_not_del : ¬ isValidDelegation (msg.benv.state.getCode wa)) :
    Msg.NoDel wa msg' := by
  have heq := setDelegation_benv_equiv h_run
  rcases heq with ⟨h_ca, h_code⟩
  have h_code_wa := h_code wa
  have h2 := h_code_wa h.code h_not_del
  constructor
  · rw [h_ca]; exact h.ca
  · rw [h2]; exact h.code

lemma setDelegationStep_fields {auth : Auth} {msg msg' : Msg}
    {refund refund' : B256}
    (h_run : setDelegationStep auth msg refund = .ok (msg', refund')) :
    msg'.caller = msg.caller ∧
    msg'.target = msg.target ∧
    msg'.currentTarget = msg.currentTarget ∧
    msg'.shouldTransferValue = msg.shouldTransferValue ∧
    msg'.value = msg.value ∧
    msg'.codeAddress = msg.codeAddress := by
  unfold setDelegationStep at h_run
  split at h_run
  · injection h_run with h1; injection h1 with h_msg h_refund
    subst h_msg
    simp
  · split at h_run
    · injection h_run with h1; injection h1 with h_msg h_refund
      subst h_msg
      simp
    · split at h_run
      · injection h_run with h1; injection h1 with h_msg h_refund
        subst h_msg
        simp
      · contradiction
      · dsimp only at h_run
        split at h_run
        · injection h_run with h1; injection h1 with h_msg h_refund
          subst h_msg
          simp
        · split at h_run
          · injection h_run with h1; injection h1 with h_msg h_refund
            subst h_msg
            simp
          · injection h_run with h1; injection h1 with h_msg h_refund
            subst h_msg
            simp [Msg.setCode, Msg.incrNonce]

lemma setDelegationLoop_fields {auths : List Auth} {msg msg' : Msg}
    {refund refund' : B256}
    (h_run : setDelegationLoop auths msg refund = .ok (msg', refund')) :
    msg'.caller = msg.caller ∧
    msg'.target = msg.target ∧
    msg'.currentTarget = msg.currentTarget ∧
    msg'.shouldTransferValue = msg.shouldTransferValue ∧
    msg'.value = msg.value ∧
    msg'.codeAddress = msg.codeAddress := by
  induction auths generalizing msg refund with
  | nil =>
    injection h_run with h1; injection h1 with h_msg h_refund
    subst h_msg
    simp
  | cons auth auths_tail ih =>
    unfold setDelegationLoop at h_run
    rcases Except.bind_eq_ok h_run with ⟨⟨msg1, refund1⟩, h_step, h_tail⟩
    rcases setDelegationStep_fields h_step with ⟨hc1, htgt1, ht1, hstv1, hv1, hca1⟩
    rcases ih h_tail with ⟨hc2, htgt2, ht2, hstv2, hv2, hca2⟩
    exact ⟨hc2.trans hc1, htgt2.trans htgt1, ht2.trans ht1, hstv2.trans hstv1, hv2.trans hv1, hca2.trans hca1⟩

lemma setDelegation_fields {msg msg' : Msg} {v : B256}
    (h_run : setDelegation msg = .ok ⟨msg', v⟩) :
    msg'.caller = msg.caller ∧
    msg'.target = msg.target ∧
    msg'.currentTarget = msg.currentTarget ∧
    msg'.shouldTransferValue = msg.shouldTransferValue ∧
    msg'.value = msg.value ∧
    msg'.codeAddress = msg.codeAddress := by
  unfold setDelegation at h_run
  dsimp [bind, Except.bind] at h_run
  apply Except.bind_eq_ok at h_run
  rcases h_run with ⟨⟨msg_mid, refundCounter⟩, h_loop, h_rest⟩
  rcases setDelegationLoop_fields h_loop with ⟨hc, htgt, hct, hstv, hv, hca⟩
  dsimp only at h_rest
  split at h_rest
  · contradiction
  · rename_i ca h_ca
    have h_msg' : msg' =
        { msg_mid with code := msg_mid.benv.state.getCode ca } := by
      exact (congrArg Prod.fst (Except.ok.inj h_rest)).symm
    subst msg'
    exact ⟨hc, htgt, hct, hstv, hv, hca⟩

theorem processMessageCall_preserves_noDel {wa : Adr} {msg : Msg} {st' : Jaune.State}
    {out : MsgCallOutput}
    (h_run : processMessageCall msg = .ok ⟨st', out⟩)
    (h : Msg.NoDel wa msg)
    (h_not_del : ¬ isValidDelegation (msg.benv.state.getCode wa)) :
    wa ∉ out.accountsToDelete := by
  unfold processMessageCall at h_run
  split at h_run
  · unfold processMessageCall.create at h_run
    dsimp only at h_run
    split at h_run
    · injection h_run with h_eq
      injection h_eq with _ h_out
      subst h_out
      exact AdrSet.not_mem_empty
    · rename_i h_col
      simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at h_col
      have h_ct := ne_wa_of_not_hasCodeOrNonce h.code h_col.1
      revert h_run
      rcases h_evm : processCreateMessage msg with ⟨err⟩ | ⟨evm⟩
      · simp only [Except.bimap, bind, Except.bind]
        intro h_run
        injection h_run
      · simp only [Except.bimap, bind, Except.bind]
        intro h_run
        have h_nodel := processCreateMessage_preserves_noDel h_evm h_ct h
        change (if evm.error.isNone = true then _ else _) = _ at h_run
        split at h_run
        · split at h_run
          · injection h_run
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h_run
            rcases h_run with ⟨_, rfl⟩
            simp_all only [id_eq, if_pos]
            exact h_nodel.atd
        · simp only [id_eq, Except.ok.injEq, Prod.mk.injEq] at h_run
          rcases h_run with ⟨_, rfl⟩
          simp_all
  · rename_i h_target
    have h_target_false : msg.target.isNone = false := by
      cases ht : msg.target.isNone <;> simp [ht] at h_target ⊢
    unfold processMessageCall.call at h_run
    dsimp only at h_run
    split at h_run
    · simp only [bind, Except.bind] at h_run
      unfold Except.bimap at h_run
      split at h_run
      · injection h_run
      · rename_i evm h_evm
        split at h_evm
        · injection h_evm
        · rename_i evm' h_pm
          simp only [id_eq, Except.ok.injEq] at h_evm
          subst h_evm
          have h_pc : Msg.NoDel wa (match getDelegatedCodeAddress msg.code with | none => msg | some dca => { benv := msg.benv, tenv := msg.tenv, caller := msg.caller, target := msg.target, currentTarget := msg.currentTarget, gas := msg.gas, value := msg.value, data := msg.data, codeAddress := some dca, code := msg.benv.state.getCode dca, depth := msg.depth, shouldTransferValue := msg.shouldTransferValue, isStatic := msg.isStatic, accessedAddresses := Std.HashSet.insert msg.accessedAddresses dca, accessedStorageKeys := msg.accessedStorageKeys, disablePrecompiles := true }) := by
            split
            · exact h
            · exact ⟨h.ca, h.code⟩
          have h_nodel_evm := processMessage_preserves_noDel h_pm h_pc
          split at h_run
          · split at h_run
            · injection h_run
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h_run
              rcases h_run with ⟨_, rfl⟩
              exact h_nodel_evm.atd
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h_run
            rcases h_run with ⟨_, rfl⟩
            exact AdrSet.not_mem_empty
    · rename_i h_col
      rcases h_del : setDelegation msg with ⟨err⟩ | ⟨⟨msgDelegation, val⟩⟩
      · simp only [h_del, bind, Except.bind] at h_run
        injection h_run
      · simp only [h_del, bind, Except.bind] at h_run
        have h_del_nodel := setDelegation_msg_noDel h_del h h_not_del
        unfold Except.bimap at h_run
        split at h_run
        · injection h_run
        · rename_i evm h_evm
          split at h_evm
          · injection h_evm
          · rename_i evm' h_pm
            simp only [id_eq, Except.ok.injEq] at h_evm
            subst h_evm
            have h_pc : Msg.NoDel wa (match getDelegatedCodeAddress msgDelegation.code with | none => msgDelegation | some dca => { benv := msgDelegation.benv, tenv := msgDelegation.tenv, caller := msgDelegation.caller, target := msgDelegation.target, currentTarget := msgDelegation.currentTarget, gas := msgDelegation.gas, value := msgDelegation.value, data := msgDelegation.data, codeAddress := some dca, code := msgDelegation.benv.state.getCode dca, depth := msgDelegation.depth, shouldTransferValue := msgDelegation.shouldTransferValue, isStatic := msgDelegation.isStatic, accessedAddresses := Std.HashSet.insert msgDelegation.accessedAddresses dca, accessedStorageKeys := msgDelegation.accessedStorageKeys, disablePrecompiles := true }) := by
              split
              · exact h_del_nodel
              · exact ⟨h_del_nodel.ca, h_del_nodel.code⟩
            have h_nodel_evm := processMessage_preserves_noDel h_pm h_pc
            split at h_run
            · split at h_run
              · injection h_run
              · simp only [Except.ok.injEq, Prod.mk.injEq] at h_run
                rcases h_run with ⟨_, rfl⟩
                exact h_nodel_evm.atd
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h_run
              rcases h_run with ⟨_, rfl⟩
              exact AdrSet.not_mem_empty

theorem processMessageCall_accountsToDelete_ne {wa : Adr} {msg : Msg}
    {st' : Jaune.State} {out : MsgCallOutput}
    (h_run : processMessageCall msg = .ok ⟨st', out⟩)
    (h : Msg.NoDel wa msg)
    (h_not_del : ¬ isValidDelegation (msg.benv.state.getCode wa)) :
    ∀ a ∈ out.accountsToDelete.toList, a ≠ wa := by
  intro a ha heq
  subst heq
  exact processMessageCall_preserves_noDel h_run h h_not_del
    (Std.HashSet.mem_toList.mp ha)

lemma prepareMessage_benv {benv : Benv} {tenv : Tenv} {tx : Tx} {msg : Msg}
    (h_prep : prepareMessage benv tenv tx = .ok msg) :
    msg.benv = benv := by
  -- `prepareMessage` only constructs the message wrapper; it installs the
  -- supplied block environment unchanged into the resulting message.
  unfold prepareMessage at h_prep
  injection h_prep with h
  rw [← h]

private lemma if_error_eq_ok {ε α : Type} {p : Prop} [Decidable p]
    {err : ε} {a b : α}
    (h : (if p then Except.error err else Except.ok a) = Except.ok b) : a = b := by
  split at h
  · contradiction
  · exact Except.ok.inj h

-- A successfully checked transaction can afford its actual up-front gas and
-- blob charge.  In particular, that charge is represented exactly by B256.
lemma checkTransaction_upfront_lt_modulus {benv : Benv} {bout : BlockOutput}
    {tx : Tx} {sender : Adr} {effectiveGasPrice : Nat}
    {blobVersionedHashes : List B256} {txBlobGasUsed : Nat}
    (h_check :
      checkTransaction benv bout tx =
        .ok ⟨sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed⟩) :
    tx.gas * effectiveGasPrice +
      (if tx.isTypeThree = true then
        calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx
      else 0) < 2 ^ 256 := by
  unfold checkTransaction at h_check
  rcases Except.bind_eq_ok h_check with ⟨txBlobGasUsed', h_limit, h_check⟩
  rcases Except.bind_eq_ok h_check with ⟨_, h_chain, h_check⟩
  rcases Except.bind_eq_ok h_check with ⟨senderAddress, h_recover, h_check⟩
  rcases Except.bind_eq_ok h_check with ⟨fee, h_fee, h_check⟩
  rcases fee with ⟨effectiveGasPrice', maxGasFee⟩
  rcases Except.bind_eq_ok h_check with ⟨blob, h_blob, h_check⟩
  rcases blob with ⟨maxGasFee', blobVersionedHashes'⟩
  rcases Except.bind_eq_ok h_check with ⟨_, h_receiver, h_check⟩
  rcases Except.bind_eq_ok h_check with ⟨_, h_auth, h_check⟩
  rcases Except.bind_eq_ok h_check with ⟨_, h_account, h_check⟩
  have h_result := Except.ok.inj h_check
  simp only [Prod.mk.injEq] at h_result
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h_result
  have h_afford :
      maxGasFee' ≤ ((benv.state.get senderAddress).bal).toNat := by
    unfold checkTransactionSenderAccount at h_account
    split at h_account <;> try contradiction
    split at h_account <;> try contradiction
    split at h_account <;> try contradiction
    rename_i hlt
    omega
  have h_balance_lt :
      ((benv.state.get senderAddress).bal).toNat < 2 ^ 256 :=
    B256.toNat_lt _
  cases h_type : tx.type with
  | zero gasPrice receiver =>
    simp only [checkTransactionGasFee, h_type, checkTransactionLegacyGasFee] at h_fee
    rw [Except.mapError_eq_ok_iff] at h_fee
    split at h_fee
    · cases h_fee
    · have h_fee' := if_error_eq_ok h_fee
      simp only [Prod.mk.injEq] at h_fee'
      obtain ⟨rfl, rfl⟩ := h_fee'
      simp only [checkTransactionBlobData, h_type] at h_blob
      have h_blob' := Except.ok.inj h_blob
      simp only [Prod.mk.injEq] at h_blob'
      obtain ⟨rfl, rfl⟩ := h_blob'
      simp only [Tx.isTypeThree, h_type, Bool.false_eq_true, if_false]
      omega
  | one chainId gasPrice receiver accessList =>
    simp only [checkTransactionGasFee, h_type, checkTransactionLegacyGasFee] at h_fee
    rw [Except.mapError_eq_ok_iff] at h_fee
    split at h_fee
    · cases h_fee
    · have h_fee' := if_error_eq_ok h_fee
      simp only [Prod.mk.injEq] at h_fee'
      obtain ⟨rfl, rfl⟩ := h_fee'
      simp only [checkTransactionBlobData, h_type] at h_blob
      have h_blob' := Except.ok.inj h_blob
      simp only [Prod.mk.injEq] at h_blob'
      obtain ⟨rfl, rfl⟩ := h_blob'
      simp only [Tx.isTypeThree, h_type, Bool.false_eq_true, if_false]
      omega
  | two chainId maxPriorityFeePerGas maxFeePerGas receiver accessList =>
    simp only [checkTransactionGasFee, h_type, checkTransactionDynamicGasFee] at h_fee
    rw [Except.mapError_eq_ok_iff] at h_fee
    split at h_fee
    · cases h_fee
    · split at h_fee
      · cases h_fee
      · rename_i h_priority h_base_fee
        have h_fee' := if_error_eq_ok h_fee
        simp only [Prod.mk.injEq] at h_fee'
        obtain ⟨rfl, rfl⟩ := h_fee'
        simp only [checkTransactionBlobData, h_type] at h_blob
        have h_blob' := Except.ok.inj h_blob
        simp only [Prod.mk.injEq] at h_blob'
        obtain ⟨rfl, rfl⟩ := h_blob'
        simp only [Tx.isTypeThree, h_type, Bool.false_eq_true, if_false]
        have h_effective :
            min maxPriorityFeePerGas (maxFeePerGas - benv.stat.baseFeePerGas) +
                benv.stat.baseFeePerGas ≤ maxFeePerGas := by
          omega
        have h_mul := Nat.mul_le_mul_left tx.gas h_effective
        omega
  | three chainId maxPriorityFeePerGas maxFeePerGas receiver accessList
      maxFeePerBlobGas blobHashes =>
    simp only [checkTransactionGasFee, h_type, checkTransactionDynamicGasFee] at h_fee
    rw [Except.mapError_eq_ok_iff] at h_fee
    split at h_fee
    · cases h_fee
    · split at h_fee
      · cases h_fee
      · rename_i h_priority h_base_fee
        have h_fee' := if_error_eq_ok h_fee
        simp only [Prod.mk.injEq] at h_fee'
        obtain ⟨rfl, rfl⟩ := h_fee'
        simp only [checkTransactionBlobData, h_type] at h_blob
        rw [Except.mapError_eq_ok_iff] at h_blob
        split at h_blob
        · cases h_blob
        · rcases Except.bind_eq_ok h_blob with ⟨_, _, h_blob⟩
          split at h_blob
          · cases h_blob
          · split at h_blob
            · cases h_blob
            · rename_i h_blob_fee
              have h_blob' := Except.ok.inj h_blob
              simp only [Prod.mk.injEq] at h_blob'
              obtain ⟨rfl, rfl⟩ := h_blob'
              simp only [Tx.isTypeThree, h_type, reduceIte]
              have h_effective :
                  min maxPriorityFeePerGas
                      (maxFeePerGas - benv.stat.baseFeePerGas) +
                      benv.stat.baseFeePerGas ≤ maxFeePerGas := by
                omega
              have h_mul := Nat.mul_le_mul_left tx.gas h_effective
              have h_blob_mul :
                  calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx ≤
                    calculateTotalBlobGas tx * maxFeePerBlobGas := by
                unfold calculateDataFee
                exact Nat.mul_le_mul_left _ (by omega)
              omega
  | four chainId maxPriorityFeePerGas maxFeePerGas receiver accessList auths =>
    simp only [checkTransactionGasFee, h_type, checkTransactionDynamicGasFee] at h_fee
    rw [Except.mapError_eq_ok_iff] at h_fee
    split at h_fee
    · cases h_fee
    · split at h_fee
      · cases h_fee
      · rename_i h_priority h_base_fee
        have h_fee' := if_error_eq_ok h_fee
        simp only [Prod.mk.injEq] at h_fee'
        obtain ⟨rfl, rfl⟩ := h_fee'
        simp only [checkTransactionBlobData, h_type] at h_blob
        have h_blob' := Except.ok.inj h_blob
        simp only [Prod.mk.injEq] at h_blob'
        obtain ⟨rfl, rfl⟩ := h_blob'
        simp only [Tx.isTypeThree, h_type, Bool.false_eq_true, if_false]
        have h_effective :
            min maxPriorityFeePerGas (maxFeePerGas - benv.stat.baseFeePerGas) +
                benv.stat.baseFeePerGas ≤ maxFeePerGas := by
          omega
        have h_mul := Nat.mul_le_mul_left tx.gas h_effective
        omega

lemma validateTransaction_calldataFloorGasCost_le_gas {rules : ForkRules} {tx : Tx}
    {intrinsicGas calldataFloorGasCost : Nat}
    (h_validate :
      validateTransaction rules tx = .ok ⟨intrinsicGas, calldataFloorGasCost⟩) :
    calldataFloorGasCost ≤ tx.gas := by
  unfold validateTransaction at h_validate
  rcases h_cost : calculateIntrinsicCost tx with ⟨ig, floorCost⟩
  rw [h_cost] at h_validate
  dsimp only at h_validate
  split at h_validate
  · cases h_validate
  · rename_i h_gas
    cases h_limit : rules.tx.maxGas with
    | none =>
      simp only [h_limit] at h_validate
      split at h_validate
      · cases h_validate
      · unfold checkInitcodeSize at h_validate
        split at h_validate
        · cases h_validate
        · have h_result := Except.ok.inj h_validate
          simp only [Prod.mk.injEq] at h_result
          obtain ⟨rfl, rfl⟩ := h_result
          omega
    | some maxGas =>
      simp only [h_limit] at h_validate
      unfold checkInitcodeSize at h_validate
      split at h_validate
      · cases h_validate
      · unfold checkTransactionGasCap at h_validate
        simp only [h_limit] at h_validate
        split at h_validate
        · cases h_validate
        · split at h_validate
          · cases h_validate
          · have h_result := Except.ok.inj h_validate
            simp only [Prod.mk.injEq] at h_result
            obtain ⟨rfl, rfl⟩ := h_result
            omega

-- Total wei credited by a list of withdrawals, computed in ℕ. Withdrawals
-- mint ether with wrapping addition (`State.addBal`), so the block-level
-- theorems need the bound `sum _.bal + wdsum wds < 2 ^ 256` : without it,
-- a withdrawal crediting `wa` could wrap `wa`'s balance to near zero and
-- destroy both solvency and `SumNof`.
def wdsum (wds : List Withdrawal) : Nat :=
  (wds.map (fun wd => wd.amount.toNat * 10 ^ 9)).sum

-- Helper: `toB256` truncates, so its `toNat` is at most the original Nat.
lemma toB256_toNat_le (n : Nat) : n.toB256.toNat ≤ n := by
  rw [B256.toNat_toB256]
  unfold Nat.lo
  exact Nat.mod_le _ _

-- Erasing an account removes its balance from the total: nonincreasing.
lemma destroyAccount_sum_le (w : Jaune.State) (a : Adr) :
    sum (Jaune.destroyAccount w a).bal ≤ sum w.bal := by
  have h0 : ((Jaune.destroyAccount w a).get a).bal = 0 := by
    show (State.get (w.erase a) a).bal = 0
    unfold State.get
    rw [Std.TreeMap.getD_erase]; simp [Acct.nil]
  have hdec : Decrease a (w.bal a) w.bal (Jaune.destroyAccount w a).bal := by
    intro b; constructor
    · intro heq; subst heq
      show w.bal a - w.bal a = ((Jaune.destroyAccount w a).get a).bal
      rw [h0, B256.sub_self]
    · intro hnb
      show w.bal b = (State.get (w.erase a) b).bal
      rw [State.get_erase_ne (Ne.symm hnb)]; rfl
  have hsum := sum_sub_assoc hdec (le_refl _)
  omega

lemma foldl_destroyAccount_sum_le :
    ∀ (as : List Adr) (w : Jaune.State),
      sum ((as.foldl Jaune.destroyAccount w).bal) ≤ sum w.bal
  | [], _ => le_refl _
  | a :: as, w => by
    rw [List.foldl_cons]
    exact le_trans (foldl_destroyAccount_sum_le as _) (destroyAccount_sum_le w a)

-- Affordability: a successfully checked transaction's up-front debit
-- (gas fee plus blob fee) fits in 256 bits, because `checkTransaction`
-- verifies the sender's (256-bit) balance covers the *max* gas fee.
-- Validation bound: the calldata floor gas cost never exceeds the gas limit.
-- One-step wei conservation for `processTransaction`.
lemma processTransaction_sum_le {benv : Benv} {bout bout' : BlockOutput}
    {tx : Tx} {i : Nat} {st : Jaune.State}
    (h_run : processTransaction benv bout tx i = .ok ⟨st, bout'⟩) :
    sum st.bal ≤ sum benv.state.bal := by
  unfold processTransaction at h_run
  -- as in `processTransaction_preserves_solvent`: `beginTransaction` touches only
  -- `stat.origState`, which no balance below reads.
  simp only [Benv.beginTransaction] at h_run
  rcases Except.bind_eq_ok h_run with ⟨bout0, hbout0, h_run⟩
  rcases Except.bind_eq_ok h_run with ⟨gasInfo, hval, h_run⟩
  rcases gasInfo with ⟨intrinsicGas, calldataFloorGasCost⟩
  rcases Except.bind_eq_ok h_run with ⟨chk, hcheck, h_run⟩
  rcases chk with ⟨sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed⟩
  rcases Except.bind_eq_ok h_run with ⟨state1, hsub, h_run⟩
  rcases Except.bind_eq_ok h_run with ⟨msg, hprep, h_run⟩
  rcases Except.bind_eq_ok h_run with ⟨pmout, hpm, h_run⟩
  rcases pmout with ⟨state2, txOutput⟩
  rw [Except.mapError_eq_ok_iff] at hval hpm
  rcases Except.bind_eq_ok h_run with ⟨refundCounter, hrefund, h_run⟩
  simp only at h_run
  rcases h_run with ⟨rfl, rfl⟩
  have hsub_some :
      (benv.state.incrNonce sender).subBal sender
        (tx.gas * effectiveGasPrice +
          if tx.isTypeThree = true then
            calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx
          else
            0).toB256 = some state1 := by
    generalize hopt : (benv.state.incrNonce sender).subBal sender
        (tx.gas * effectiveGasPrice +
          if tx.isTypeThree = true then
            calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx
          else
            0).toB256 = o at hsub ⊢
    cases o with
    | none => simp [Option.toExcept] at hsub
    | some s => simpa [Option.toExcept] using hsub
  -- the up-front debit does not wrap
  have hfee_lt := checkTransaction_upfront_lt_modulus hcheck
  -- `hcheck` carries the `beginTransaction` environment, so this arrives with an
  -- unreduced `stat` projection; put it back in terms of `benv` (as `hsub_some`
  -- already is) or `omega` below sees the two blob-fee terms as distinct atoms.
  dsimp only at hfee_lt
  have hcdf := validateTransaction_calldataFloorGasCost_le_gas hval
  -- sum bookkeeping
  have h1 := foldl_destroyAccount_sum_le txOutput.accountsToDelete.toList
    ((state2.addBal sender
        ((tx.gas -
            max (tx.gas - txOutput.gasLeft -
              min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
              calldataFloorGasCost) *
          effectiveGasPrice).toB256).addBal
      benv.stat.coinbase
        (max (tx.gas - txOutput.gasLeft -
            min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
            calldataFloorGasCost *
          (effectiveGasPrice - benv.stat.baseFeePerGas)).toB256)
  have h2 := State.addBal_growth
    (state2.addBal sender
      ((tx.gas -
          max (tx.gas - txOutput.gasLeft -
            min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
            calldataFloorGasCost) *
        effectiveGasPrice).toB256)
    benv.stat.coinbase
      (max (tx.gas - txOutput.gasLeft -
          min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
          calldataFloorGasCost *
        (effectiveGasPrice - benv.stat.baseFeePerGas)).toB256
  have h3 := State.addBal_growth state2 sender
    ((tx.gas -
        max (tx.gas - txOutput.gasLeft -
          min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
          calldataFloorGasCost) *
      effectiveGasPrice).toB256
  have h4 : sum state2.bal ≤ sum state1.bal := by
    have h := processMessageCall_sum_le hpm
    rw [prepareMessage_benv hprep] at h
    exact h
  have h5 := State.balSum_subBal hsub_some
  dsimp only [State.BalGrowth, State.balSum] at h2 h3 h5
  rw [State.incrNonce_bal] at h5
  -- credits are bounded by their Nat values
  have h7 := toB256_toNat_le
    ((tx.gas -
        max (tx.gas - txOutput.gasLeft -
          min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
          calldataFloorGasCost) *
      effectiveGasPrice)
  have h8 := toB256_toNat_le
    (max (tx.gas - txOutput.gasLeft -
        min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
        calldataFloorGasCost *
      (effectiveGasPrice - benv.stat.baseFeePerGas))
  -- the debit is exactly its Nat value
  have h6 := B256.toNat_toB256_of_lt hfee_lt
  -- Nat arithmetic: refund + tip ≤ gas fee
  have hGle : max (tx.gas - txOutput.gasLeft -
      min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
      calldataFloorGasCost ≤ tx.gas := by
    apply max_le _ hcdf
    omega
  have hkey : (tx.gas -
        max (tx.gas - txOutput.gasLeft -
          min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
          calldataFloorGasCost) *
      effectiveGasPrice +
      max (tx.gas - txOutput.gasLeft -
          min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
          calldataFloorGasCost *
        (effectiveGasPrice - benv.stat.baseFeePerGas) ≤
      tx.gas * effectiveGasPrice := by
    apply le_trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) _)
    rw [← Nat.add_mul, Nat.sub_add_cancel hGle]
  omega

/-
(1) Difficulty: ★★★★☆
(2) Proof plan: first prove the one-step statement for `processTransaction`.
Invert its successful do-block as in `processTransaction_preserves_solvent`; use
`State.balSum_subBal` for the up-front debit,
`processMessageCall_sum_le` for the call, and `State.addBal_growth` for the
sender refund and coinbase tip.  The inequalities checked by
`checkTransaction`, together with the definitions of refunded gas and the
priority fee, show that the two credits are at most the up-front debit (the
blob fee is simply an additional debit).  Account destruction is
nonincreasing.  Then induct over `txis`, composing the one-step inequalities.
-/
lemma applyTransactions_sum_le
    {txis : List (Nat × Tx)} {benv benv' : Benv}
    {bout bout' : BlockOutput}
    (h_run : applyTransactions txis benv bout = .ok ⟨benv', bout'⟩) :
    sum benv'.state.bal ≤ sum benv.state.bal := by
  induction txis generalizing benv bout with
  | nil =>
    rw [applyTransactions] at h_run
    obtain ⟨hb, hbo⟩ := Prod.mk.inj (Except.ok.inj h_run)
    subst hb; exact le_refl _
  | cons hd tl ih =>
    obtain ⟨i, tx⟩ := hd
    rw [applyTransactions] at h_run
    obtain ⟨⟨st, bout''⟩, h1, h2⟩ := Except.bind_eq_ok h_run
    exact le_trans (ih h2) (processTransaction_sum_le h1)

lemma processCheckedSystemTransaction_to_unchecked {benv : Benv} {target : Adr} {data : Bytes}
    {st : Jaune.State} {out : MsgCallOutput}
    (h : processCheckedSystemTransaction benv target data = .ok ⟨st, out⟩) :
    processUncheckedSystemTransaction benv target data = .ok ⟨st, out⟩ := by
  dsimp [processCheckedSystemTransaction, processUncheckedSystemTransaction] at h ⊢
  split at h
  · cases h
  · rcases Except.bind_eq_ok h with ⟨⟨st', out'⟩, h1, h2⟩
    split at h2
    · cases h2
    · obtain ⟨h3, h4⟩ := Prod.mk.inj (Except.ok.inj h2)
      rw [Except.mapError_eq_ok_iff] at h1
      subst h3; subst h4; exact h1

/-! ## Chain-level reachability

`BlockChain.Reach` and `BlockChain.ReachUsing` appear in audited statements, so
their names and definitions are frozen; they are moved down verbatim because
neither mentions any contract. -/

-- `BlockChain.Reach ch ch'` : chain `ch'` is reachable from `ch` by a
-- sequence of valid blocks, each of whose withdrawals stays within the
-- no-overflow bound.
inductive BlockChain.Reach : BlockChain → BlockChain → Prop
  | refl (ch : BlockChain) : Reach ch ch
  | step {ch ch' ch'' : BlockChain} {block : Block} :
      Reach ch ch' →
      sum ch'.state.bal + wdsum block.wds < 2 ^ 256 →
      stateTransition ch' block = .ok ch'' →
      Reach ch ch''

-- `BlockChain.ReachUsing cfg ch ch'` : the same reachability on a *configured*
-- chain. Each step imports one block through the configured transition, so the
-- fork it runs under is whichever one `cfg` schedules at that block's
-- timestamp. A sequence crossing Prague, Osaka, BPO1, and BPO2 is one chain of
-- these steps, not four separate relations.
--
-- The base constructor carries the configured-chain context evidence (P0.1
-- item 6): the schedule is validated, the starting snapshot is a valid
-- execution context, and the configuration names the snapshot's own chain
-- identity. A zero-step reach over a mismatched or never-validated pair no
-- longer exists, and every `step` re-establishes the identity agreement on
-- its own — a successful `stateTransitionUsing` is impossible across
-- contradictory chain IDs (`stateTransitionUsing_success_chainId_eq`) and
-- runs `cfg.validate` inside its rules lookup.
inductive BlockChain.ReachUsing (cfg : ChainConfig) : BlockChain → BlockChain → Prop
  | refl (ch : BlockChain)
      (h_cfg : cfg.Valid)
      (h_ctx : ch.ValidContext)
      (h_id : cfg.chainId = ch.chainId) :
      ReachUsing cfg ch ch
  | step {ch ch' ch'' : BlockChain} {block : Block} :
      ReachUsing cfg ch ch' →
      sum ch'.state.bal + wdsum block.wds < 2 ^ 256 →
      stateTransitionUsing cfg ch' block = .ok ch'' →
      ReachUsing cfg ch ch''

/-- Every successful Prague step copies the snapshot's chain identity, so a
whole Prague reachability chain does. -/
lemma BlockChain.Reach.chainId_eq {ch ch' : BlockChain}
    (h_reach : BlockChain.Reach ch ch') : ch'.chainId = ch.chainId := by
  induction h_reach with
  | refl => rfl
  | step h_reach' h_bound h_st ih =>
      rw [stateTransitionWith_preserves_chainId h_st, ih]

-- A Prague-only schedule is the Prague chain: every `Reach` step is a
-- `ReachUsing (ChainConfig.pragueOnly ch.chainId)` step, because
-- `stateTransitionUsing` on that schedule reduces to `stateTransition`.
-- The corrected `ReachUsing.refl` demands real evidence, so the conversion
-- carries it rather than being true because the identity was ignored: the
-- Prague-only schedule is valid for every identity
-- (`ChainConfig.pragueOnly_valid`), it names the base snapshot's own chain ID
-- by construction, and the base snapshot's context validity is the one fact
-- plain `Reach` never established, so it enters as a hypothesis.
theorem BlockChain.Reach.toReachUsing {ch ch' : BlockChain}
    (h_ctx : ch.ValidContext)
    (h_reach : BlockChain.Reach ch ch') :
    BlockChain.ReachUsing (ChainConfig.pragueOnly ch.chainId) ch ch' := by
  induction h_reach with
  | refl => exact .refl ch (ChainConfig.pragueOnly_valid _) h_ctx rfl
  | step h_reach' h_bound h_st ih =>
      refine .step ih h_bound ?_
      rw [stateTransitionUsing_eq_of_chainId_eq
        (show (ChainConfig.pragueOnly ch.chainId).chainId = _ from
          (Reach.chainId_eq h_reach').symm),
        ChainConfig.pragueOnly_rulesAt]
      exact h_st

namespace ContractSpec

/-! ### The message- and block-environment forms of the invariant

The generic counterparts of `Blanc.Msg.InvSolvent` and `Blanc.Benv.InvSolvent`. -/

structure MsgInv (c : ContractSpec) (wa : Adr) (msg : Msg) : Prop where
  (state : c.StateInv wa msg.benv.state)
  (nodel : Msg.NoDel wa msg)
  (code : msg.target.isNone = false → msg.currentTarget = wa →
    some msg.code.toList = Prog.compile c.prog)
  (codeAddress : msg.target.isNone = false → msg.currentTarget = wa →
    msg.codeAddress = some wa)
  (ne : msg.shouldTransferValue = true → msg.caller ≠ wa)
  (val0 : msg.shouldTransferValue = false → msg.currentTarget = wa → msg.value = 0)

structure BenvInv (c : ContractSpec) (wa : Adr) (benv : Benv) : Prop where
  (state : c.StateInv wa benv.state)
  (ca : wa ∉ benv.createdAccounts)

variable {c : ContractSpec}

lemma StateInv.of_exec_precond {wa : Adr} {sevm : Sevm} {pre post : Devm}
    (hp : c.Preserves wa)
    (h_pc : c.Pre wa sevm pre)
    (h_code : sevm.currentTarget = wa → some sevm.code.toList = Prog.compile c.prog)
    (exc : Exec 0 sevm pre (.ok post)) :
    c.StateInv wa post.state := by
  have h_post : c.Post wa sevm post := hp sevm pre post exc h_code h_pc
  apply StateInv.of_postcond h_post
  have h_ce : post.getCode wa = pre.getCode wa := code_eq_of_exec exc h_pc.code
  show some (post.state.getCode wa).toList = Prog.compile c.prog
  rw [show post.state.getCode wa = post.getCode wa from rfl, h_ce]
  exact h_pc.code



-- Deep helper: one `processMessage` run preserves `c.StateInv` and never
-- self-destructs `wa`.  This is where the frame-level `exec_preserves_solvent` gets
-- lifted: `processMessage` = `benvAfterTransfer` (value transfer) then
-- `executeCode` (→ `exec (initEvm ·)`) with on-error rollback.  The `nof`
-- and `getCode` parts are already available through the relational-mirror
-- stacks (`ProcessMessage.preserves_nof`, `ProcessMessage.preserves_getCode_gen`); the
-- solvency part is the genuinely new content, obtained from `exec_preserves_solvent`
-- via `c.Post` and `StateInv.of_postcond`.  Still open.
theorem processMessage_preserves_inv {wa : Adr} {msg : Msg} {evm : Devm}
    (hp : c.Preserves wa)
    (h_run : processMessage msg = .ok evm)
    (h_code : msg.currentTarget = wa → some msg.code.toList = Prog.compile c.prog)
    (h_ne : msg.shouldTransferValue = true → msg.caller ≠ wa)
    (h_val0 : msg.shouldTransferValue = false → msg.currentTarget = wa → msg.value = 0)
    (h_inv : c.StateInv wa msg.benv.state) :
    c.StateInv wa evm.state := by
  obtain ⟨xl, hfill, hrel⟩ := of_processMessage msg (.ok evm) h_run
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp hrel
  unfold FrameBody at hbody
  rcases h_bt : msg.benvAfterTransfer with e | benv <;> rw [h_bt] at hbody
  · rw [hbody.2, processMessage.settle_error] at hset
    cases hset
  have h_pc : c.Pre wa (initSevm (msg.withBenv benv)) (initDevm (msg.withBenv benv)) :=
    Pre.of_inv_benvAfterTransfer h_ne h_val0 h_bt h_inv
  have h_code' : (initSevm (msg.withBenv benv)).currentTarget = wa →
      some (initSevm (msg.withBenv benv)).code.toList = Prog.compile c.prog := h_code
  rcases r0 with x | evm'
  · rw [processMessage.settle_error] at hset
    cases hset
  unfold processMessage.settle at hset
  dsimp only [bind, Except.bind] at hset
  by_cases herr : evm'.error.isSome = true
  · -- sub-execution failed : state rolled back to the pre-transfer state
    rw [if_pos herr] at hset
    rw [Except.ok.inj hset]
    exact h_inv
  · -- clean success
    rw [if_neg herr] at hset
    have h_eq : evm' = evm := Except.ok.inj hset.symm
    subst h_eq
    rcases of_executeCode_cases hbody with ⟨adr, h_he⟩ | ⟨exn, h_xl, h_he⟩
    · -- precompile : the state is left untouched
      rw [state_of_executePrecomp_ok h_he herr]
      exact StateInv.of_benvAfterTransfer h_ne h_bt h_inv
    · -- interpreted code : hand off to the driver-level theorem
      subst h_xl
      obtain ⟨exc⟩ := hfill
      rw [exec_ok_of_handleError h_he herr] at exc
      exact StateInv.of_exec_precond hp h_pc h_code' exc


-- Overwriting the storage of a *foreign* account (`a ≠ wa`) preserves `c.StateInv`
-- (`wa`'s account is untouched, and `setStor` leaves every balance alone).

-- Create path.  `processCreateMessage` seeds the account being created
-- (`setStor .empty` + `incrNonce`, both at `currentTarget ≠ wa`), runs
-- `processMessage`, then on clean success charges code gas and installs the
-- returned code at `currentTarget`; the exceptional-halt and error paths roll
-- the state back to `msg.benv.state`.
-- `h_ct_ne` (the create address is fresh, hence `≠ wa`) subsumes both the
-- WETH-code condition and the `value = 0` condition: their premises are all
-- `currentTarget = wa`, so `h_ct_ne` discharges them vacuously.
theorem processCreateMessage_preserves_inv {wa : Adr} {msg : Msg} {evm : Devm}
    (hp : c.Preserves wa)
    (h_run : processCreateMessage msg = .ok evm)
    (h_ct_ne : msg.currentTarget ≠ wa)
    (h_ne : msg.shouldTransferValue = true → msg.caller ≠ wa)
    (h_inv : c.StateInv wa msg.benv.state) :
    c.StateInv wa evm.state := by
  rw [processCreateMessage_eq] at h_run
  -- the seeded sub-message still satisfies the invariant (`currentTarget ≠ wa`)
  have h_inv_cm : c.StateInv wa (processCreateMessage.msg msg).benv.state := by
    show c.StateInv wa ((msg.benv.state.setStor msg.currentTarget .empty).incrNonce
      msg.currentTarget)
    exact StateInv.incrNonce (StateInv.setStor_ne h_ct_ne h_inv)
  rcases hpm : processMessage (processCreateMessage.msg msg) with x | evm2
  · rw [hpm, processCreateMessage.settle_error] at h_run
    cases h_run
  rw [hpm] at h_run
  have h_rest := h_run
  have h_pm : c.StateInv wa evm2.state :=
    processMessage_preserves_inv hp hpm (fun h => absurd h h_ct_ne) h_ne
      (fun _ h => absurd h h_ct_ne) h_inv_cm
  unfold processCreateMessage.settle at h_rest
  dsimp only [bind, Except.bind] at h_rest
  by_cases herr : evm2.error.isNone = true
  · rw [if_pos herr] at h_rest
    rcases hcg : processCreateMessage.chargeCodeGas msg.benv.stat.rules evm2
      with ⟨err, evm3⟩ | evm3
    · -- code-gas charge failed
      rw [hcg] at h_rest
      cases err
      case halt reason =>
        -- exceptional halt : state rolled back to `msg.benv.state`
        rw [← Except.ok.inj h_rest]; exact h_inv
      all_goals cases h_rest
    · -- clean success : install the returned code at `currentTarget ≠ wa`
      rw [hcg] at h_rest; dsimp only at h_rest
      rw [← Except.ok.inj h_rest, Devm.setCode_state, chargeCodeGas_state_ok hcg]
      exact StateInv.setCode_ne h_ct_ne h_pm
  · -- sub-message failed : state rolled back to `msg.benv.state`
    rw [if_neg herr] at h_rest
    rw [← Except.ok.inj h_rest]; exact h_inv

lemma setDelegationStep_preserves_inv {wa : Adr} {auth : Auth} {msg msg' : Msg}
    {refund refund' : B256}
    (h_run : setDelegationStep auth msg refund = .ok (msg', refund'))
    (h_inv : c.StateInv wa msg.benv.state) :
    c.StateInv wa msg'.benv.state := by
  unfold setDelegationStep at h_run
  split at h_run
  · injection h_run with h1; injection h1 with h_msg h_refund
    subst h_msg
    exact h_inv
  · split at h_run
    · injection h_run with h1; injection h1 with h_msg h_refund
      subst h_msg
      exact h_inv
    · split at h_run
      · injection h_run with h1; injection h1 with h_msg h_refund
        subst h_msg
        exact h_inv
      · contradiction
      · rename_i authority heq
        dsimp only at h_run
        split at h_run
        · injection h_run with h1; injection h1 with h_msg h_refund
          subst h_msg
          exact h_inv
        · split at h_run
          · injection h_run with h1; injection h1 with h_msg h_refund
            subst h_msg
            exact h_inv
          · injection h_run with h1; injection h1 with h_msg h_refund
            subst h_msg
            have h_code_ne : (msg.benv.state.getCode wa).toList ≠ [] := by
              intro h_empty
              exact Prog.compile_ne_nil (p := c.prog) (by rw [← h_inv.code, h_empty])
            have h_not_del : ¬ isValidDelegation (msg.benv.state.getCode wa) :=
              not_delegation_of_compile h_inv.code
            have h_ne : authority ≠ wa := by
              intro h_eq
              subst authority
              by_cases h_empty : (msg.benv.state.get wa).code.isEmpty = true
              · have h_size : (msg.benv.state.get wa).code.size = 0 := by
                  simpa [ByteArray.isEmpty] using h_empty
                exact (ne_wa_of_code_size_zero h_code_ne h_size) rfl
              · have h_valid : isValidDelegation (msg.benv.state.get wa).code := by
                  simp_all
                exact h_not_del (by simpa [State.getCode] using h_valid)
            change c.StateInv wa ((msg.benv.state.setCode authority _).incrNonce authority)
            exact StateInv.incrNonce (StateInv.setCode_ne h_ne h_inv)

lemma setDelegationLoop_preserves_inv {wa : Adr} {auths : List Auth} {msg msg' : Msg}
    {refund refund' : B256}
    (h_run : setDelegationLoop auths msg refund = .ok (msg', refund'))
    (h_inv : c.StateInv wa msg.benv.state) :
    c.StateInv wa msg'.benv.state := by
  induction auths generalizing msg refund with
  | nil =>
    injection h_run with h1; injection h1 with h_msg h_refund
    subst h_msg
    exact h_inv
  | cons auth auths_tail ih =>
    unfold setDelegationLoop at h_run
    rcases Except.bind_eq_ok h_run with ⟨⟨msg1, refund1⟩, h_step, h_tail⟩
    exact ih h_tail (setDelegationStep_preserves_inv h_step h_inv)

lemma setDelegation_preserves_inv {wa : Adr} {msg msg' : Msg} {v : B256}
    (h_run : setDelegation msg = .ok ⟨msg', v⟩)
    (h_inv : c.StateInv wa msg.benv.state) :
    c.StateInv wa msg'.benv.state := by
  unfold setDelegation at h_run
  dsimp [bind, Except.bind] at h_run
  apply Except.bind_eq_ok at h_run
  rcases h_run with ⟨⟨msg_mid, refundCounter⟩, h_loop, h_rest⟩
  have h_eq_benv : msg_mid.benv = msg'.benv := by
    dsimp only at h_rest
    split at h_rest
    · contradiction
    · simpa using congrArg Msg.benv (congrArg Prod.fst (Except.ok.inj h_rest))
  rw [← h_eq_benv]
  exact setDelegationLoop_preserves_inv h_loop h_inv


lemma MsgInv.pc {wa : Adr} {msg : Msg} {codeSrc : Adr → ByteArray}
    (h : c.MsgInv wa msg) :
    c.MsgInv wa
      (match getDelegatedCodeAddress msg.code with
      | none => msg
      | some dca =>
        { msg with
          disablePrecompiles := true,
          accessedAddresses := msg.accessedAddresses.insert dca,
          code := codeSrc dca,
          codeAddress := some dca }) := by
  split
  · exact h
  · rename_i dca h_dca
    refine ⟨h.state, ⟨h.nodel.ca, h.nodel.code⟩, ?_, ?_, h.ne, h.val0⟩
    · intro h_tgt h_ct
      have h_not_del : ¬ isValidDelegation msg.code :=
        not_delegation_of_compile
          (h.code (by simpa using h_tgt) (by simpa using h_ct))
      unfold getDelegatedCodeAddress at h_dca
      split at h_dca
      · rename_i h_del
        exact False.elim (h_not_del h_del)
      · contradiction
    · intro h_tgt h_ct
      have h_not_del : ¬ isValidDelegation msg.code :=
        not_delegation_of_compile
          (h.code (by simpa using h_tgt) (by simpa using h_ct))
      unfold getDelegatedCodeAddress at h_dca
      split at h_dca
      · rename_i h_del
        exact False.elim (h_not_del h_del)
      · contradiction

lemma setDelegation_preserves_msgInv {wa : Adr} {msg msg' : Msg} {v : B256}
    (h_run : setDelegation msg = .ok ⟨msg', v⟩)
    (h : c.MsgInv wa msg) :
    c.MsgInv wa msg' := by
  have h_run_orig := h_run
  have h_not_del : ¬ isValidDelegation (msg.benv.state.getCode wa) :=
    not_delegation_of_compile h.state.code
  refine ⟨setDelegation_preserves_inv h_run h.state,
    setDelegation_msg_noDel h_run h.nodel h_not_del, ?_, ?_, ?_, ?_⟩
  · intro h_tgt h_ct
    unfold setDelegation at h_run
    dsimp [bind, Except.bind] at h_run
    apply Except.bind_eq_ok at h_run
    rcases h_run with ⟨⟨msg_mid, refundCounter⟩, h_loop, h_rest⟩
    rcases setDelegationLoop_fields h_loop with ⟨_, h_mid_tgt, h_mid_ct, _, _, h_mid_ca⟩
    have h_loop_equiv := setDelegationLoop_benv_equiv h_loop
    rcases h_loop_equiv with ⟨_, h_code⟩
    have h_code_ne : (msg.benv.state.getCode wa).toList ≠ [] := by
      intro h_empty
      exact Prog.compile_ne_nil (p := c.prog) (by rw [← h.state.code, h_empty])
    have h_code_wa := h_code wa h_code_ne h_not_del
    dsimp only at h_rest
    split at h_rest
    · contradiction
    · rename_i ca h_ca
      have h_msg' : msg' =
          { msg_mid with code := msg_mid.benv.state.getCode ca } := by
        exact (congrArg Prod.fst (Except.ok.inj h_rest)).symm
      subst msg'
      change some (msg_mid.benv.state.getCode ca).toList = Prog.compile c.prog
      change msg_mid.currentTarget = wa at h_ct
      rw [h_mid_ct] at h_ct
      have h_ca_wa : ca = wa := by
        have h_msg_tgt : msg.target.isNone = false := by
          change msg_mid.target.isNone = false at h_tgt
          rwa [h_mid_tgt] at h_tgt
        have h_msg_ca := h.codeAddress h_msg_tgt h_ct
        rw [h_mid_ca, h_msg_ca] at h_ca
        injection h_ca with h_eq
        exact h_eq.symm
      subst h_ca_wa
      rw [h_code_wa]
      exact h.state.code
  · intro h_tgt h_ct
    unfold setDelegation at h_run_orig
    dsimp [bind, Except.bind] at h_run_orig
    apply Except.bind_eq_ok at h_run_orig
    rcases h_run_orig with ⟨⟨msg_mid, refundCounter⟩, h_loop, h_rest⟩
    rcases setDelegationLoop_fields h_loop with ⟨_, h_mid_tgt, h_mid_ct, _, _, h_mid_ca⟩
    dsimp only at h_rest
    split at h_rest
    · contradiction
    · rename_i ca h_ca
      have h_msg' : msg' =
          { msg_mid with code := msg_mid.benv.state.getCode ca } := by
        exact (congrArg Prod.fst (Except.ok.inj h_rest)).symm
      subst msg'
      change msg_mid.codeAddress = some wa
      change msg_mid.currentTarget = wa at h_ct
      rw [h_mid_ct] at h_ct
      rw [h_mid_ca]
      apply h.codeAddress
      · change msg_mid.target.isNone = false at h_tgt
        rwa [h_mid_tgt] at h_tgt
      · exact h_ct
  · intro h_stv
    unfold setDelegation at h_run_orig
    dsimp [bind, Except.bind] at h_run_orig
    apply Except.bind_eq_ok at h_run_orig
    rcases h_run_orig with ⟨⟨msg_mid, refundCounter⟩, h_loop, h_rest⟩
    rcases setDelegationLoop_fields h_loop with ⟨h_mid_caller, _, _, h_mid_stv, _, _⟩
    dsimp only at h_rest
    split at h_rest
    · contradiction
    · rename_i ca h_ca
      have h_msg' : msg' =
          { msg_mid with code := msg_mid.benv.state.getCode ca } := by
        exact (congrArg Prod.fst (Except.ok.inj h_rest)).symm
      subst msg'
      change msg_mid.caller ≠ wa
      rw [h_mid_caller]
      apply h.ne
      change msg_mid.shouldTransferValue = true at h_stv
      rwa [h_mid_stv] at h_stv
  · intro h_stv h_ct
    unfold setDelegation at h_run_orig
    dsimp [bind, Except.bind] at h_run_orig
    apply Except.bind_eq_ok at h_run_orig
    rcases h_run_orig with ⟨⟨msg_mid, refundCounter⟩, h_loop, h_rest⟩
    rcases setDelegationLoop_fields h_loop with ⟨_, _, h_mid_ct, h_mid_stv, h_mid_val, _⟩
    dsimp only at h_rest
    split at h_rest
    · contradiction
    · rename_i ca h_ca
      have h_msg' : msg' =
          { msg_mid with code := msg_mid.benv.state.getCode ca } := by
        exact (congrArg Prod.fst (Except.ok.inj h_rest)).symm
      subst msg'
      change msg_mid.value = 0
      rw [h_mid_val]
      apply h.val0
      · change msg_mid.shouldTransferValue = false at h_stv
        rwa [h_mid_stv] at h_stv
      · change msg_mid.currentTarget = wa at h_ct
        rwa [h_mid_ct] at h_ct

theorem processMessageCall_preserves_inv {wa : Adr} {msg : Msg} {st' : Jaune.State}
    {out : MsgCallOutput}
    (hp : c.Preserves wa)
    (h_run : processMessageCall msg = .ok ⟨st', out⟩)
    (h_inv : c.MsgInv wa msg) :
    c.StateInv wa st' ∧ (∀ a ∈ out.accountsToDelete.toList, a ≠ wa) := by
  refine ⟨?_, processMessageCall_accountsToDelete_ne h_run h_inv.nodel
    (not_delegation_of_compile h_inv.state.code)⟩
  unfold processMessageCall at h_run
  split at h_run
  · unfold processMessageCall.create at h_run
    dsimp only at h_run
    split at h_run
    · injection h_run with h_eq
      cases h_eq
      exact h_inv.state
    · rename_i h_col
      simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at h_col
      have h_ct : msg.currentTarget ≠ wa :=
        ne_wa_of_not_hasCodeOrNonce h_inv.nodel.code h_col.1
      revert h_run
      rcases h_evm : processCreateMessage msg with ⟨err⟩ | ⟨evm⟩
      · simp only [Except.bimap, bind, Except.bind]
        intro h_run
        injection h_run
      · simp only [Except.bimap, bind, Except.bind]
        intro h_run
        have h_pm := processCreateMessage_preserves_inv hp h_evm h_ct
          h_inv.ne h_inv.state
        change (if evm.error.isNone = true then _ else _) = _ at h_run
        split at h_run
        · split at h_run
          · injection h_run
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h_run
            rcases h_run with ⟨rfl, _⟩
            exact h_pm
        · simp only [id_eq, Except.ok.injEq, Prod.mk.injEq] at h_run
          rcases h_run with ⟨rfl, _⟩
          exact h_pm
  · rename_i h_target
    have h_target_false : msg.target.isNone = false := by
      cases ht : msg.target.isNone <;> simp [ht] at h_target ⊢
    unfold processMessageCall.call at h_run
    dsimp only at h_run
    split at h_run
    · simp only [bind, Except.bind] at h_run
      unfold Except.bimap at h_run
      split at h_run
      · injection h_run
      · rename_i evm h_evm
        split at h_evm
        · injection h_evm
        · rename_i evm' h_pm
          simp only [id_eq, Except.ok.injEq] at h_evm
          subst h_evm
          have h_pc : c.MsgInv wa
              (match getDelegatedCodeAddress msg.code with
              | none => msg
              | some dca =>
                { msg with
                  disablePrecompiles := true,
                  accessedAddresses := msg.accessedAddresses.insert dca,
                  code := msg.benv.state.getCode dca,
                  codeAddress := some dca }) :=
            MsgInv.pc (codeSrc := fun dca => msg.benv.state.getCode dca) h_inv
          have h_tgt_pc :
              (match getDelegatedCodeAddress msg.code with
              | none => msg
              | some dca =>
                { msg with
                  disablePrecompiles := true,
                  accessedAddresses := msg.accessedAddresses.insert dca,
                  code := msg.benv.state.getCode dca,
                  codeAddress := some dca }).target.isNone = false := by
            split <;> simpa using h_target_false
          have h_evm_inv :=
            processMessage_preserves_inv hp h_pm
              (fun hct => h_pc.code h_tgt_pc hct)
              h_pc.ne h_pc.val0 h_pc.state
          split at h_run
          · split at h_run
            · injection h_run
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h_run
              rcases h_run with ⟨rfl, _⟩
              exact h_evm_inv
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h_run
            rcases h_run with ⟨rfl, _⟩
            exact h_evm_inv
    · rename_i h_col
      rcases h_del : setDelegation msg with ⟨err⟩ | ⟨⟨msgDelegation, val⟩⟩
      · simp only [h_del, bind, Except.bind] at h_run
        injection h_run
      · simp only [h_del, bind, Except.bind] at h_run
        have h_del_inv := setDelegation_preserves_msgInv h_del h_inv
        unfold Except.bimap at h_run
        split at h_run
        · injection h_run
        · rename_i evm h_evm
          split at h_evm
          · injection h_evm
          · rename_i evm' h_pm
            simp only [id_eq, Except.ok.injEq] at h_evm
            subst h_evm
            have h_pc : c.MsgInv wa
                (match getDelegatedCodeAddress msgDelegation.code with
                | none => msgDelegation
                | some dca =>
                  { msgDelegation with
                    disablePrecompiles := true,
                    accessedAddresses := msgDelegation.accessedAddresses.insert dca,
                    code := msgDelegation.benv.state.getCode dca,
                    codeAddress := some dca }) :=
              MsgInv.pc (codeSrc := fun dca => msgDelegation.benv.state.getCode dca) h_del_inv
            have h_del_fields := setDelegation_fields h_del
            have h_msgDelegation_target_false : msgDelegation.target.isNone = false := by
              rw [h_del_fields.2.1]
              exact h_target_false
            have h_tgt_pc :
                (match getDelegatedCodeAddress msgDelegation.code with
                | none => msgDelegation
                | some dca =>
                  { msgDelegation with
                    disablePrecompiles := true,
                    accessedAddresses := msgDelegation.accessedAddresses.insert dca,
                    code := msgDelegation.benv.state.getCode dca,
                    codeAddress := some dca }).target.isNone = false := by
              split <;> simpa using h_msgDelegation_target_false
            have h_evm_inv :=
              processMessage_preserves_inv hp h_pm
                (fun hct => h_pc.code h_tgt_pc hct)
                h_pc.ne h_pc.val0 h_pc.state
            split at h_run
            · split at h_run
              · injection h_run
              · simp only [Except.ok.injEq, Prod.mk.injEq] at h_run
                rcases h_run with ⟨rfl, _⟩
                exact h_evm_inv
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h_run
              rcases h_run with ⟨rfl, _⟩
              exact h_evm_inv

/-! ### Transaction-level helper lemmas

The proof of `processTransaction_preserves_inv` factors into three local facts.
They are intentionally stated at the executable-definition boundary:

* a checked transaction sender cannot be the WETH account, since successful
  `checkTransaction` accepted the sender as an EOA/delegation account;
* `prepareMessage` packages the post-upfront-fee state into a message satisfying
  `c.MsgInv`;
* the final transaction gas credits are funded by the earlier upfront debit, so
  the two `addBal`s cannot overflow the global balance sum.

These are the intended follow-up proof obligations; with them available, the
main transaction invariant proof below is just definition inversion and
composition of already-proved message-level invariants. -/

lemma checkTransaction_sender_ne_of_inv {wa : Adr}
    {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {sender : Adr} {effectiveGasPrice : Nat}
    {blobVersionedHashes : List B256} {txBlobGasUsed : Nat}
    (h_check :
      checkTransaction benv bout tx =
        .ok ⟨sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed⟩)
    (h_inv : c.BenvInv wa benv) :
    sender ≠ wa := by
  intro hsender
  subst sender
  unfold checkTransaction at h_check
  rcases Except.bind_eq_ok h_check with ⟨_, _, h_check⟩
  rcases Except.bind_eq_ok h_check with ⟨_, _, h_check⟩
  rcases Except.bind_eq_ok h_check with ⟨senderAddress, _, h_check⟩
  rcases Except.bind_eq_ok h_check with ⟨_, _, h_check⟩
  rcases Except.bind_eq_ok h_check with ⟨_, _, h_check⟩
  rcases Except.bind_eq_ok h_check with ⟨_, _, h_check⟩
  rcases Except.bind_eq_ok h_check with ⟨_, _, h_check⟩
  rcases Except.bind_eq_ok h_check with ⟨_, hg, h_check⟩
  have hs : senderAddress = wa := congrArg Prod.fst (Except.ok.inj h_check)
  subst senderAddress
  unfold checkTransactionSenderAccount at hg
  split at hg <;> try contradiction
  split at hg <;> try contradiction
  split at hg <;> try contradiction
  have h_no : ¬ ((benv.state.get wa).code.isEmpty ∨ isValidDelegation (benv.state.get wa).code) := by
    intro h
    rcases h with h_empty | h_del
    · have h_empty' : (benv.state.getCode wa).toList = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [← ByteArray.size_eq_length_toList]
        unfold ByteArray.isEmpty at h_empty; simp at h_empty; simpa [State.getCode] using congrArg ByteArray.size h_empty
      exact Prog.compile_ne_nil (p := c.prog) (by rw [← h_inv.state.code, h_empty'])
    · exact not_delegation_of_compile h_inv.state.code h_del
  simp [checkTransactionSenderCode, h_no] at hg

lemma prepareMessage_preserves_inv {wa : Adr}
    {benv : Benv} {tenv : Tenv} {tx : Tx} {msg : Msg}
    (h_prep : prepareMessage benv tenv tx = .ok msg)
    (h_state : c.StateInv wa benv.state)
    (h_ca : wa ∉ benv.createdAccounts)
    (h_origin_ne : tenv.stat.origin ≠ wa) :
    c.MsgInv wa msg := by
  -- `prepareMessage` sets `caller = tenv.stat.origin`,
  -- `shouldTransferValue = true`, and preserves `benv`.  In the call case, if
  -- `currentTarget = wa`, then the installed code/codeAddress are exactly WETH's
  -- code and `some wa`; in the create case `target.isNone = true`, so those
  -- conditional fields are vacuous.
  unfold prepareMessage at h_prep
  cases hrecv : tx.type.receiver? with
  | none =>
    simp [hrecv] at h_prep
    subst msg
    refine ⟨h_state, ⟨h_ca, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro h_empty
      exact Prog.compile_ne_nil (p := c.prog) (by rw [← h_state.code, h_empty])
    · simp
    · simp
    · simpa using h_origin_ne
    · simp
  | some target =>
    simp [hrecv] at h_prep
    subst msg
    refine ⟨h_state, ⟨h_ca, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro h_empty
      exact Prog.compile_ne_nil (p := c.prog) (by rw [← h_state.code, h_empty])
    · intro _ h_target
      change target = wa at h_target
      subst target
      simpa using h_state.code
    · intro _ h_target
      change target = wa at h_target
      subst target
      rfl
    · simpa using h_origin_ne
    · simp

lemma StateInv.add_transaction_gas_credits {wa : Adr}
    {baseState debitState postMsgState : Jaune.State}
    {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {sender : Adr} {effectiveGasPrice : Nat}
    {blobVersionedHashes : List B256} {txBlobGasUsed : Nat}
    {intrinsicGas calldataFloorGasCost refundCounter : Nat}
    {txOutput : MsgCallOutput}
    (h_validate :
      validateTransaction benv.stat.rules tx =
        .ok ⟨intrinsicGas, calldataFloorGasCost⟩)
    (h_check :
      checkTransaction benv bout tx =
        .ok ⟨sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed⟩)
    (h_debit :
      (baseState.incrNonce sender).subBal sender
        (tx.gas * effectiveGasPrice +
          if tx.isTypeThree = true then
            calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx
          else
            0).toB256 =
        some debitState)
    (h_msg_sum : sum postMsgState.bal ≤ sum debitState.bal)
    (h_base_sum : sum baseState.bal < 2 ^ 256)
    (h_post : c.StateInv wa postMsgState) :
    c.StateInv wa
      ((postMsgState.addBal sender
          ((tx.gas -
              max (tx.gas - txOutput.gasLeft -
                min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
                calldataFloorGasCost) *
            effectiveGasPrice).toB256).addBal
        benv.stat.coinbase
          (max (tx.gas - txOutput.gasLeft -
              min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
              calldataFloorGasCost *
            (effectiveGasPrice - benv.stat.baseFeePerGas)).toB256) := by
  have h_fee_lt := checkTransaction_upfront_lt_modulus h_check
  have h_floor := validateTransaction_calldataFloorGasCost_le_gas h_validate
  have h_debit_sum := State.balSum_subBal h_debit
  dsimp only [State.balSum] at h_debit_sum
  rw [State.incrNonce_bal] at h_debit_sum
  have h_debit_exact := B256.toNat_toB256_of_lt h_fee_lt
  rw [h_debit_exact] at h_debit_sum
  have h_used_le :
      max (tx.gas - txOutput.gasLeft -
          min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
          calldataFloorGasCost ≤ tx.gas := by
    apply max_le
    · omega
    · exact h_floor
  have h_credits_le :
      (tx.gas -
          max (tx.gas - txOutput.gasLeft -
            min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
            calldataFloorGasCost) *
        effectiveGasPrice +
      max (tx.gas - txOutput.gasLeft -
          min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
          calldataFloorGasCost *
        (effectiveGasPrice - benv.stat.baseFeePerGas) ≤
      tx.gas * effectiveGasPrice := by
    apply le_trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left _
        (Nat.sub_le effectiveGasPrice benv.stat.baseFeePerGas)) _)
    rw [← Nat.add_mul, Nat.sub_add_cancel h_used_le]
  have h_refund_le :
      (((tx.gas -
          max (tx.gas - txOutput.gasLeft -
            min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
            calldataFloorGasCost) *
        effectiveGasPrice).toB256).toNat ≤
      (tx.gas -
          max (tx.gas - txOutput.gasLeft -
            min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
            calldataFloorGasCost) *
        effectiveGasPrice := by
    rw [B256.toNat_toB256]
    unfold Nat.lo
    exact Nat.mod_le _ _
  have h_tip_le :
      ((max (tx.gas - txOutput.gasLeft -
          min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
          calldataFloorGasCost *
        (effectiveGasPrice - benv.stat.baseFeePerGas)).toB256).toNat ≤
      max (tx.gas - txOutput.gasLeft -
          min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
          calldataFloorGasCost *
        (effectiveGasPrice - benv.stat.baseFeePerGas) := by
    rw [B256.toNat_toB256]
    unfold Nat.lo
    exact Nat.mod_le _ _
  have h_sender_sum :
      sum postMsgState.bal +
        (((tx.gas -
            max (tx.gas - txOutput.gasLeft -
              min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
              calldataFloorGasCost) *
          effectiveGasPrice).toB256).toNat < 2 ^ 256 := by
    omega
  have h_sender_inv :=
    StateInv.addBal (a := sender) h_sender_sum h_post
  have h_growth := State.addBal_growth postMsgState sender
    ((tx.gas -
        max (tx.gas - txOutput.gasLeft -
          min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
          calldataFloorGasCost) *
      effectiveGasPrice).toB256
  dsimp only [State.BalGrowth, State.balSum] at h_growth
  apply StateInv.addBal
  · omega
  · exact h_sender_inv

theorem processTransaction_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (benv : Benv) (bout bout' : BlockOutput) (tx : Tx) (i : Nat) (st : Jaune.State)
    (h_run : processTransaction benv bout tx i = .ok ⟨st, bout'⟩)
    (h_sum : sum benv.state.bal < 2 ^ 256)
    (h_inv : c.BenvInv wa benv) : c.BenvInv wa (benv.withState st) := by
  unfold processTransaction at h_run
  -- `beginTransaction` only refreshes `stat.origState`, which no balance here
  -- reads; project it away so the state/fee terms stay in terms of `benv`.
  simp only [Benv.beginTransaction] at h_run
  rcases Except.bind_eq_ok h_run with ⟨bout0, hbout0, h_run⟩
  rcases Except.bind_eq_ok h_run with ⟨gasInfo, hval, h_run⟩
  rcases gasInfo with ⟨intrinsicGas, calldataFloorGasCost⟩
  rcases Except.bind_eq_ok h_run with ⟨chk, hcheck, h_run⟩
  rcases chk with ⟨sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed⟩
  rcases Except.bind_eq_ok h_run with ⟨state1, hsub, h_run⟩
  rcases Except.bind_eq_ok h_run with ⟨msg, hprep, h_run⟩
  rcases Except.bind_eq_ok h_run with ⟨pmout, hpm, h_run⟩
  rcases pmout with ⟨state2, txOutput⟩
  rw [Except.mapError_eq_ok_iff] at hval hpm
  rcases Except.bind_eq_ok h_run with ⟨refundCounter, hrefund, h_run⟩
  simp only at h_run
  rcases h_run with ⟨rfl, rfl⟩
  have hsender : sender ≠ wa :=
    -- `beginTransaction` leaves `state` and `createdAccounts` alone, which is
    -- all `InvSolvent` constrains, so the invariant transfers field-wise.
    checkTransaction_sender_ne_of_inv hcheck ⟨h_inv.state, h_inv.ca⟩
  have hsub_some :
      (benv.state.incrNonce sender).subBal sender
        (tx.gas * effectiveGasPrice +
          if tx.isTypeThree = true then
            calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx
          else
            0).toB256 = some state1 := by
    generalize hopt : (benv.state.incrNonce sender).subBal sender
        (tx.gas * effectiveGasPrice +
          if tx.isTypeThree = true then
            calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx
          else
            0).toB256 = o at hsub ⊢
    cases o with
    | none => simp [Option.toExcept] at hsub
    | some s => simpa [Option.toExcept] using hsub
  have hstate1 : c.StateInv wa state1 :=
    StateInv.subBal hsender hsub_some (StateInv.incrNonce h_inv.state)
  have horigin :
      ({ transientStorage := Std.TreeMap.empty,
          stat :=
            { origin := sender, gasPrice := effectiveGasPrice,
              gas := tx.gas - intrinsicGas,
              accessListAddresses :=
                Std.HashSet.ofList (benv.stat.coinbase :: List.map Prod.fst tx.accessList),
              accessListStorageKeys :=
                Std.HashSet.ofList
                  (List.map
                    (fun x =>
                      match x with
                      | (adr, keys) => List.map (fun x => (adr, x)) keys)
                    tx.accessList).flatten,
              blobVersionedHashes := blobVersionedHashes, auths := tx.auths,
              indexInBlock := some i, txHash := some (getTxHash tx) } } :
            Tenv).stat.origin ≠ wa := by
    exact hsender
  have hmsg : c.MsgInv wa msg :=
    prepareMessage_preserves_inv hprep hstate1 (by simpa using h_inv.ca) horigin
  have hpm_inv := processMessageCall_preserves_inv hp hpm hmsg
  have hmsg_benv := prepareMessage_benv hprep
  have hsum_le : sum state2.bal ≤ sum state1.bal := by
    have h := processMessageCall_sum_le hpm
    rw [hmsg_benv] at h
    exact h
  have hcredits : c.StateInv wa
      ((state2.addBal sender
          ((tx.gas -
              max (tx.gas - txOutput.gasLeft -
                min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
                calldataFloorGasCost) *
            effectiveGasPrice).toB256).addBal
        benv.stat.coinbase
          (max (tx.gas - txOutput.gasLeft -
              min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
              calldataFloorGasCost *
            (effectiveGasPrice - benv.stat.baseFeePerGas)).toB256) :=
    StateInv.add_transaction_gas_credits hval hcheck hsub_some hsum_le h_sum
      hpm_inv.1
  refine ⟨?_, ?_⟩
  · exact StateInv.foldl_destroyAccount hpm_inv.2 hcredits
  · simpa [Benv.withState] using h_inv.ca

theorem applyTransactions_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (txis : List (Nat × Tx)) (benv benv' : Benv) (bout bout' : BlockOutput)
    (h_run : applyTransactions txis benv bout = .ok ⟨benv', bout'⟩)
    (h_sum : sum benv.state.bal < 2 ^ 256)
    (h_inv : c.BenvInv wa benv) : c.BenvInv wa benv' := by
  -- list induction over `txis`; each step is `processTransaction_preserves_inv`
  -- (note `processTransaction` threads `Benv`, so track `benv.state`).
  induction txis generalizing benv bout with
  | nil =>
    rw [applyTransactions] at h_run
    obtain ⟨hb, hbo⟩ := Prod.mk.inj (Except.ok.inj h_run)
    subst hb; exact h_inv
  | cons hd tl ih =>
    obtain ⟨i, tx⟩ := hd
    rw [applyTransactions] at h_run
    obtain ⟨⟨st, bout''⟩, h1, h2⟩ := Except.bind_eq_ok h_run
    have hstep := processTransaction_preserves_inv wa hp benv bout bout'' tx i st h1 h_sum h_inv
    have hsum' : sum (benv.withState st).state.bal < 2 ^ 256 := by
      have := processTransaction_sum_le h1
      simpa [Benv.withState] using Nat.lt_of_le_of_lt this h_sum
    exact ih (benv.withState st) bout'' h2 hsum' hstep

/-
(1) Difficulty: ★★☆☆☆
(2) Proof plan: unfold the two system-transaction wrappers, build
`c.MsgInv` for the resulting zero-value/no-transfer message from the
`c.BenvInv` hypothesis, and apply `processMessageCall_preserves_inv` and
`processMessageCall_sum_le`.  The wrapper only chooses the target's current
code and otherwise does not alter the starting state.
-/
lemma processUncheckedSystemTransaction_preserves_inv_sum_le (wa : Adr)
    (hp : c.Preserves wa)
    (benv : Benv) (target : Adr) (data : Bytes)
    (st : Jaune.State) (out : MsgCallOutput)
    (h_run : processUncheckedSystemTransaction benv target data = .ok ⟨st, out⟩)
    (h_inv : c.BenvInv wa benv) :
    c.StateInv wa st ∧ sum st.bal ≤ sum benv.state.bal := by
  dsimp [processUncheckedSystemTransaction, processSystemTransaction] at h_run
  -- The system transaction opens on `benv.beginTransaction`; that only
  -- refreshes `stat.origState`, so every field the invariant reads is defeq to
  -- the corresponding field of `benv`.
  have h_msg : c.MsgInv wa
      (processSystemTransactionMsg benv.beginTransaction
        (processSystemTransactionTenv benv.beginTransaction)
        target data (benv.state.getCode target)) := by
    refine ⟨h_inv.state, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨h_inv.ca, ?_⟩
      intro hnil
      have hnil' : (benv.state.getCode wa).toList = [] := by
        simpa only [processSystemTransactionMsg, Benv.beginTransaction] using hnil
      exact Prog.compile_ne_nil (p := c.prog) (by
        rw [← h_inv.state.code, hnil'])
    · intro _ htarget
      simp only [processSystemTransactionMsg] at htarget ⊢
      subst target
      exact h_inv.state.code
    · intro _ htarget
      simp only [processSystemTransactionMsg] at htarget ⊢
      subst target
      rfl
    · simp [processSystemTransactionMsg]
    · simp [processSystemTransactionMsg]
  have hsum := processMessageCall_sum_le h_run
  exact ⟨(processMessageCall_preserves_inv hp h_run h_msg).1, hsum⟩

/-
(1) Difficulty: ★★★☆☆
(2) Proof plan: induct on `wds`, generalizing the starting state.  For the
head withdrawal, prove that
`(wd.amount * (10 ^ 9).toB256).toNat = wd.amount.toNat * 10 ^ 9`; the product
cannot wrap because a withdrawal amount is 64-bit.  The head/tail decomposition
of `wdsum` and the global bound then gives the exact pre-sum bound required by
`StateInv.addBal`.  Apply that lemma for the head and feed the resulting sum
identity (or `State.balSum_setBal`) and residual bound to the induction
hypothesis.
-/

lemma processWithdrawalsState_preserves_inv (wa : Adr)
    (st : Jaune.State) (wds : List Withdrawal)
    (h_bound : sum st.bal + wdsum wds < 2 ^ 256)
    (h_inv : c.StateInv wa st) :
    c.StateInv wa (processWithdrawalsState st wds) := by
  induction wds generalizing st with
  | nil => exact h_inv
  | cons wd wds ih =>
    have h_cons : wdsum (wd :: wds) = wd.amount.toNat * 10 ^ 9 + wdsum wds := by
      simp [wdsum]
    rw [h_cons] at h_bound
    have h_val : (wd.amount * (10 ^ 9).toB256).toNat =
        wd.amount.toNat * 10 ^ 9 := by
      have h9 : (10 : Nat) ^ 9 ↾ 256 = 10 ^ 9 := Nat.lo_eq_of_lt (by omega)
      rw [B256.toNat_mul, B256.toNat_toB256, h9, Nat.lo_eq_of_lt (by omega)]
    have h_step : processWithdrawalsState st (wd :: wds) =
        processWithdrawalsState
          (st.addBal wd.recipient (wd.amount * (10 ^ 9).toB256)) wds := rfl
    rw [h_step]
    have hb : sum st.bal + (wd.amount * (10 ^ 9).toB256).toNat < 2 ^ 256 := by
      rw [h_val]; exact lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_right (wd.amount.toNat * 10 ^ 9) (wdsum wds)) (sum st.bal)) h_bound
    have h_sum := sum_addBal_eq st wd.recipient _ hb
    apply ih
    · rw [h_sum, h_val]; omega
    · exact StateInv.addBal hb h_inv

/-
(1) Difficulty: ★★☆☆☆
(2) Proof plan: invert `processGeneralPurposeRequests`.  Parsing deposits and
updating the request list do not touch state.  Each of the two checked system
transactions reduces, on its successful branch, to the corresponding
unchecked system transaction, so apply
`processUncheckedSystemTransaction_preserves_inv_sum_le` twice.  Thread
`createdAccounts` through `Benv.withState` and compose the two sum
inequalities.
-/
lemma processGeneralPurposeRequests_preserves_inv_sum_le (wa : Adr)
    (hp : c.Preserves wa)
    (benv : Benv) (bout : BlockOutput)
    (st : Jaune.State) (bout' : BlockOutput)
    (h_run : processGeneralPurposeRequests benv bout = .ok ⟨st, bout'⟩)
    (h_inv : c.BenvInv wa benv) :
    c.StateInv wa st ∧ sum st.bal ≤ sum benv.state.bal := by
  rw [processGeneralPurposeRequests] at h_run
  rcases Except.bind_eq_ok h_run with ⟨deposits, h_dep, h_run⟩
  dsimp only at h_run
  split at h_run <;>
    (rcases Except.bind_eq_ok h_run with ⟨⟨st1, out1⟩, h1, h_run⟩;
     dsimp only at h_run;
     have hu1 := processUncheckedSystemTransaction_preserves_inv_sum_le wa hp benv
       withdrawalRequestPredeployAddress [] st1 out1
       (processCheckedSystemTransaction_to_unchecked h1) h_inv;
     have h_inv1 : c.BenvInv wa (benv.withState st1) :=
       ⟨hu1.1, by simpa [Benv.withState] using h_inv.ca⟩;
     split at h_run <;>
       (rcases Except.bind_eq_ok h_run with ⟨⟨st2, out2⟩, h2, h_run⟩;
        have hu2 := processUncheckedSystemTransaction_preserves_inv_sum_le wa hp
          (benv.withState st1)
          consolidationRequestPredeployAddress [] st2 out2
          (processCheckedSystemTransaction_to_unchecked h2) h_inv1;
        split at h_run <;>
          (obtain ⟨h3, h4⟩ := Prod.mk.inj (Except.ok.inj h_run);
           subst h3;
           exact ⟨hu2.1, le_trans (by simpa [Benv.withState] using hu2.2) hu1.2⟩)))

theorem applyBody_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (benv : Benv) (txs : List (Bytes ⊕ Tx)) (wds : List Withdrawal)
    (st : Jaune.State) (bout : BlockOutput)
    (h_run : applyBody benv txs wds = .ok ⟨st, bout⟩)
    (h_wds : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (h_inv : c.BenvInv wa benv) : c.StateInv wa st := by
  rw [applyBody] at h_run
  simp only at h_run
  rcases Except.bind_eq_ok h_run with ⟨⟨stBeacon, outBeacon⟩, h_beacon, h_run⟩
  rcases Except.bind_eq_ok h_run with ⟨lastHash, h_lastHash, h_run⟩
  rcases Except.bind_eq_ok h_run with ⟨⟨stHistory, outHistory⟩, h_history, h_run⟩
  rcases Except.bind_eq_ok h_run with ⟨decodedTxs, h_decode, h_run⟩
  rcases Except.bind_eq_ok h_run with ⟨⟨benvTxs, boutTxs⟩, h_txs, h_requests⟩
  dsimp only at h_history h_txs h_requests
  rw [Except.mapError_eq_ok_iff] at h_beacon h_history
  have h_beacon_inv :=
    processUncheckedSystemTransaction_preserves_inv_sum_le wa hp benv
      beaconRootsAddress benv.stat.parentBeaconBlockRoot.toBytes
      stBeacon outBeacon h_beacon h_inv
  have h_benv_beacon : c.BenvInv wa (benv.withState stBeacon) :=
    ⟨h_beacon_inv.1, by simpa [Benv.withState] using h_inv.ca⟩
  have h_history_inv :=
    processUncheckedSystemTransaction_preserves_inv_sum_le wa hp
      (benv.withState stBeacon) historyStorageAddress lastHash.toBytes
      stHistory outHistory h_history h_benv_beacon
  have h_benv_history :
      c.BenvInv wa ((benv.withState stBeacon).withState stHistory) :=
    ⟨h_history_inv.1, by simpa [Benv.withState] using h_benv_beacon.ca⟩
  have h_hist_bound :
      sum ((benv.withState stBeacon).withState stHistory).state.bal < 2 ^ 256 := by
    have h_beacon_sum : sum stBeacon.bal ≤ sum benv.state.bal := h_beacon_inv.2
    have h_history_sum : sum stHistory.bal ≤ sum stBeacon.bal := by
      simpa [Benv.withState] using h_history_inv.2
    simp only [Benv.withState]
    omega
  have h_txs_inv : c.BenvInv wa benvTxs :=
    applyTransactions_preserves_inv wa hp decodedTxs.putIndex
      ((benv.withState stBeacon).withState stHistory) benvTxs
      BlockOutput.init boutTxs h_txs h_hist_bound h_benv_history
  have h_txs_sum := applyTransactions_sum_le h_txs
  dsimp [processWithdrawals] at h_requests
  have h_txs_bound : sum benvTxs.state.bal + wdsum wds < 2 ^ 256 := by
    have h_history_sum : sum stHistory.bal ≤ sum stBeacon.bal := by
      simpa [Benv.withState] using h_history_inv.2
    have h_txs_sum' : sum benvTxs.state.bal ≤ sum stHistory.bal := by
      simpa [Benv.withState] using h_txs_sum
    omega
  have h_wds_inv :=
    processWithdrawalsState_preserves_inv wa benvTxs.state wds
      h_txs_bound h_txs_inv.state
  have h_benv_wds : c.BenvInv wa
      (benvTxs.withState (processWithdrawalsState benvTxs.state wds)) :=
    ⟨h_wds_inv, by simpa [Benv.withState] using h_txs_inv.ca⟩
  exact (processGeneralPurposeRequests_preserves_inv_sum_le wa hp
    (benvTxs.withState (processWithdrawalsState benvTxs.state wds))
    (boutTxs.withWithdrawalsTrie
      (processWithdrawalsTrie boutTxs.withdrawalsTrie wds))
    st bout h_requests h_benv_wds).1

-- The state transition preserves WETH solvency whichever fork's rules it runs.
-- This is the general theorem, and it is general for a reason rather than by
-- luck: `applyBody_preserves_inv` never asks which rules it is running, because
-- solvency is a statement about how value moves and no fork rule moves value.
-- Everything below -- Prague, an explicitly named fork, a configured chain
-- crossing Osaka and the BPO forks -- is an instance of this one proof.

theorem stateTransitionWith_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (rules : ForkRules)
    (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransitionWith rules ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : c.StateInv wa ch.state) : c.StateInv wa ch'.state := by
  -- invert the typed core behind the byte-identical renderer adapter
  -- (`stateTransitionWith_eq_ok_iff`); the state change is `applyBody`, so
  -- this is `applyBody_preserves_inv` (the block-check helpers don't touch state).
  rw [stateTransitionWith_eq_ok_iff, stateTransitionE] at h_run
  obtain ⟨_, _, h_run⟩ := Except.bind_eq_ok h_run
  obtain ⟨_, _, h_run⟩ := Except.bind_eq_ok h_run
  dsimp only at h_run
  obtain ⟨⟨st, bout⟩, h_ab, h_run⟩ := Except.bind_eq_ok h_run
  dsimp only at h_run
  obtain ⟨_, _, h_run⟩ := Except.bind_eq_ok h_run
  rw [← Except.ok.inj h_run]
  exact applyBody_preserves_inv wa hp (initBenv rules ch block.header) block.txs
    block.wds st bout h_ab h_wds ⟨h_inv, AdrSet.not_mem_empty⟩



/-! ### The chain-level rungs -/

theorem stateTransitionUsing_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (cfg : ChainConfig) (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransitionUsing cfg ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : c.StateInv wa ch.state) : c.StateInv wa ch'.state := by
  -- the configured entry point checks the chain identity first; the invariant
  -- needs neither that fact nor which rules the schedule picked.
  rw [stateTransitionUsing] at h_run
  obtain ⟨_, _, h_run⟩ := Except.bind_eq_ok h_run
  obtain ⟨rules, _, h_run⟩ := Except.bind_eq_ok h_run
  exact stateTransitionWith_preserves_inv wa hp rules ch ch' block h_run h_wds h_inv

/-- Prague is the `rules := pragueRules` instance, and `stateTransition` is
*definitionally* `stateTransitionWith pragueRules`. -/
theorem stateTransition_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransition ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : c.StateInv wa ch.state) : c.StateInv wa ch'.state :=
  stateTransitionWith_preserves_inv wa hp pragueRules ch ch' block h_run h_wds h_inv

/-- Chain-level induction over a configured chain: no sequence of valid blocks
can break the invariant, whatever schedule the chain follows and whichever
activations that sequence crosses. -/
theorem chainUsing_preserves_inv (wa : Adr) (hp : c.Preserves wa) (cfg : ChainConfig)
    (ch ch' : BlockChain) (h_reach : BlockChain.ReachUsing cfg ch ch')
    (h_inv : c.StateInv wa ch.state) : c.StateInv wa ch'.state := by
  induction h_reach with
  | refl => exact h_inv
  | step h_reach' h_bound h_st ih =>
    exact stateTransitionUsing_preserves_inv wa hp cfg _ _ _ h_st h_bound ih

/-- The Prague corollary of the same induction. -/
theorem chain_preserves_inv (wa : Adr) (hp : c.Preserves wa) (ch ch' : BlockChain)
    (h_reach : BlockChain.Reach ch ch')
    (h_inv : c.StateInv wa ch.state) : c.StateInv wa ch'.state := by
  induction h_reach with
  | refl => exact h_inv
  | step h_reach' h_bound h_st ih =>
    exact stateTransition_preserves_inv wa hp _ _ _ h_st h_bound ih

/-- Preservation through RLP decoding and block-hash checks, under any fork's
rules. -/
theorem addBlockToChainWith_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (rules : ForkRules) (ch ch' : BlockChain) (rlp : Bytes)
    (h_run : addBlockToChainWith rules ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : c.StateInv wa ch.state) : c.StateInv wa ch'.state := by
  -- invert the raw import through Jaune's own bridge, then one
  -- `stateTransitionWith_preserves_inv` step at the decoded block.
  obtain ⟨block, hash, h_rlp, h_size, h_st⟩ := addBlockToChainWith_eq_ok_inl h_run
  exact stateTransitionWith_preserves_inv wa hp rules ch ch' block h_st
    (h_wds block hash h_rlp) h_inv

/-- Block import on a configured chain validates the schedule and chain
identity before decoding; once decoding supplies the timestamp the configured
core delegates to the same canonical import. -/
theorem addBlockToChainUsing_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (cfg : ChainConfig) (ch ch' : BlockChain) (rlp : Bytes)
    (h_run : addBlockToChainUsing cfg ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : c.StateInv wa ch.state) : c.StateInv wa ch'.state := by
  unfold addBlockToChainUsing at h_run
  cases hE : addBlockToChainUsingE cfg ch rlp with
  | error failure =>
      rw [hE] at h_run
      simp [ImportOutcome.renderLegacy] at h_run
  | ok outcome =>
      rw [hE] at h_run
      cases outcome with
      | inr rejection =>
          simp [ImportOutcome.renderLegacy] at h_run
      | inl chResult =>
          simp only [ImportOutcome.renderLegacy, Except.ok.injEq,
            Sum.inl.injEq] at h_run
          subst chResult
          unfold addBlockToChainUsingE at hE
          obtain ⟨_, _, hE⟩ := Except.bind_eq_ok hE
          obtain ⟨_, _, hE⟩ := Except.bind_eq_ok hE
          split at hE
          · simp at hE
          · rename_i block hash h_decode
            obtain ⟨rules, _, hE⟩ := Except.bind_eq_ok hE
            obtain ⟨_, h_st⟩ := addBlockToChainCanonicalE_eq_ok_inl hE
            exact stateTransitionWith_preserves_inv wa hp rules ch ch' block
              (stateTransitionWith_eq_ok_iff.mpr h_st)
              (h_wds block hash (rlpToBlock_eq_ok_iff.mpr h_decode)) h_inv

/-- Prague is the `rules := pragueRules` instance here too. -/
theorem addBlockToChain_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (ch ch' : BlockChain) (rlp : Bytes)
    (h_run : addBlockToChain ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : c.StateInv wa ch.state) : c.StateInv wa ch'.state :=
  addBlockToChainWith_preserves_inv wa hp pragueRules ch ch' rlp h_run h_wds h_inv

end ContractSpec

end Blanc
