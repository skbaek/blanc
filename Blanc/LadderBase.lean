import Blanc.CommonProofs

namespace Blanc

open Jaune

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

/-- Read-after-write at an address-shaped key, seen through `Stor.rest`.

The bare halves of `Stor.increase_set` / `Stor.decrease_set`, for a caller
that books an exact movement of its own rather than an `Increase`/`Decrease`
relation: a ledger write is visible at its own row, and only there. -/
lemma Stor.rest_set_self (s : Stor) (a : Adr) (v : B256) :
    Stor.rest (s.set a.toB256 v) a = v :=
  Stor.get_set_self _ _ _

/-- A ledger write at one address-shaped key is invisible at every other. -/
lemma Stor.rest_set_ne (s : Stor) {a b : Adr} (ne : b ≠ a) (v : B256) :
    Stor.rest (s.set a.toB256 v) b = Stor.rest s b :=
  Stor.get_set_ne _ (fun hc => ne (Adr.toB256_inj hc).symm) _

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

/-- One row rises by exactly `m` and no other row moves, so `Σ` rises by `m`.

The `Nat`-level reading of `sum_add_assoc`, for a caller holding an exact
per-row `Nat` equation rather than a `B256`-valued `Increase`.  No overflow
side condition is asked for: the post row is itself a word, so it witnesses
that the rise fits. -/
lemma sum_eq_add_of_row_add {f g : Adr → B256} {x : Adr} {m : Nat}
    (row : (g x).toNat = (f x).toNat + m)
    (rest : ∀ b : Adr, b ≠ x → g b = f b) :
    sum g = sum f + m := by
  have g_lt := B256.toNat_lt (g x)
  have word : (Nat.toB256 m).toNat = m :=
    B256.toNat_toB256_of_lt (by omega)
  have nof : B256.Nof (f x) (Nat.toB256 m) := by
    show (f x).toNat + (Nat.toB256 m).toNat < 2 ^ 256
    rw [word, ← row]; exact g_lt
  have inc : Increase x (Nat.toB256 m) f g := by
    intro b
    refine ⟨?_, fun hb => (rest b (Ne.symm hb)).symm⟩
    rintro rfl
    exact B256.toNat_inj _ _
      (by rw [B256.toNat_add_eq_of_nof _ _ nof, word, row])
  have := sum_add_assoc inc nof
  omega

/-- One row falls by exactly `m` from a row that covers it and no other row
moves, so `Σ` falls by `m`: the `Nat`-level reading of `sum_sub_assoc`. -/
lemma sum_eq_sub_of_row_sub {f g : Adr → B256} {x : Adr} {m : Nat}
    (cover : m ≤ (f x).toNat)
    (row : (g x).toNat = (f x).toNat - m)
    (rest : ∀ b : Adr, b ≠ x → g b = f b) :
    sum g = sum f - m := by
  have f_lt := B256.toNat_lt (f x)
  have word : (Nat.toB256 m).toNat = m :=
    B256.toNat_toB256_of_lt (by omega)
  have le : Nat.toB256 m ≤ f x := by
    rw [B256.le_iff_toNat_le_toNat, word]; exact cover
  have dec : Decrease x (Nat.toB256 m) f g := by
    intro b
    refine ⟨?_, fun hb => (rest b (Ne.symm hb)).symm⟩
    rintro rfl
    exact B256.toNat_inj _ _
      (by rw [B256.toNat_sub_eq_of_le _ _ le, word, row])
  have := sum_sub_assoc dec le
  omega

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

lemma sstore_preserves_getStor_ne {pc : Nat} {sevm : Sevm} {s s' : Devm} {a : Adr}
    (run : Rinst.run ⟨pc, sevm, s⟩ .sstore = .ok s')
    (h_ne : sevm.currentTarget ≠ a) :
    Devm.getStor s' a = Devm.getStor s a := by
  simp only [Rinst.run, Rinst.runCore] at run
  cases hsg : sevm.benvStat.rules.stateGas
  · -- Covered forks: the historical eight-bind walk.
    simp only [hsg] at run
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
      · have hbr : Devm.getStor s₂ =
            Devm.getStor (Devm.balReadStorage sevm.benvStat.rules sevm.currentTarget key s₂) := rfl
        exact hbr.trans addAccessedStorageKey_getStor.symm
      · rfl
    have e6 : Devm.getStor s₃ = Devm.getStor s₄ := by
      injection h6 with eq; rw [← eq]; rfl
    have e7 : Devm.getStor s₄ = Devm.getStor s₅ := chargeGas_getStor_eq h7
    have E : Devm.getStor s = Devm.getStor s₅ := e1.trans (e2.trans (e4.trans (e6.trans e7)))
    have E' : Devm.getStor s =
        Devm.getStor (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget s₅) :=
      E.trans rfl
    injection h9 with eq
    rw [← eq, setStorVal_getStor_ne h_ne]
    exact (congr_fun E' a).symm
  · -- Amsterdam: static check first, state-gas second dimension.
    simp only [hsg] at run
    rcases Except.bind_eq_ok run with ⟨_, h0, run₁⟩
    rcases Except.bind_eq_ok run₁ with ⟨⟨key, s₁⟩, h1, run₂⟩
    rcases Except.bind_eq_ok run₂ with ⟨⟨val, s₂⟩, h2, run₃⟩
    rcases Except.bind_eq_ok run₃ with ⟨_, h3, run₄⟩
    rcases Except.bind_eq_ok run₄ with ⟨s₃, hchg, run₅⟩
    rcases Except.bind_eq_ok run₅ with ⟨s₄, hstg, h9⟩
    have e1 : Devm.getStor s = Devm.getStor s₁ := Devm.pop_getStor_eq h1
    have e2 : Devm.getStor s₁ = Devm.getStor s₂ := Devm.pop_getStor_eq h2
    have echg : Devm.getStor s₂ = Devm.getStor s₃ := by
      have e1' := chargeGas_getStor_eq hchg
      have e2' : Devm.getStor s₂ = Devm.getStor s₃ := by
        rw [← e1']
        simp only [Devm.creditStateGasRefund, Mach.creditStateGasRefund,
          Devm.withRefundCounter, Devm.balReadStorage]
        try split <;> (try split) <;> rfl
      exact e2'
    have estg : Devm.getStor s₃ = Devm.getStor s₄ :=
      Devm.chargeStateGas_getStor hstg
    have E : Devm.getStor s = Devm.getStor s₄ := e1.trans (e2.trans (echg.trans estg))
    have E' : Devm.getStor s =
        Devm.getStor (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget s₄) :=
      E.trans rfl
    injection h9 with eq
    rw [← eq, setStorVal_getStor_ne h_ne]
    exact (congr_fun E' a).symm


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
      executeCode.handleErrorWith msg.benv.stat.rules.stateGas ex' = ex := by
  unfold ExecuteCode executeCode.enter at h
  simp only [h_ca] at h
  rcases h with ⟨ex', hxl, hh⟩
  exact ⟨ex', hxl, hh.symm⟩

lemma chargeCodeGas_state_ok {rules : ForkRules} {d d' : Devm}
    (h : processCreateMessage.chargeCodeGas rules d = .ok d') :
    d'.state = d.state := by
  simp only [processCreateMessage.chargeCodeGas] at h
  cases hsg : rules.stateGas
  · simp only [hsg] at h
    split at h
    · cases h
    · rcases Except.bind_eq_ok h with ⟨dG, h_charge, h_if⟩
      split_ifs at h_if
      rw [← Except.ok.inj h_if]
      exact ((Devm.burn_of_chargeGas h_charge).state).symm
  · simp only [hsg] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rcases Except.bind_eq_ok h with ⟨dG1, h_c1, h2⟩
        have hst : d'.state = dG1.state :=
          (chargeStateGas_worldEq_of_ok h2).1.symm
        have hburn : dG1.state = d.state :=
          ((Devm.burn_of_chargeGas h_c1).state).symm
        exact hst.trans hburn

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

instance : Linst.Hinv Devm.getCode Devm.getCode Linst.stop := by
  constructor; intros e s r h; injection h with h_eq; subst h_eq; rfl

instance : Linst.Hinv Devm.getCode Devm.getCode Linst.revert := by
  constructor; intros e s r h
  simp only [Linst.Run, Linst.run] at h
  rcases Except.bind_eq_ok h with ⟨v1, h1, h2⟩
  rcases Except.bind_eq_ok h2 with ⟨v2, h3, h4⟩
  rcases Except.bind_eq_ok h4 with ⟨v3, h5, h6⟩
  contradiction

instance : Linst.Hinv Devm.getBal Devm.getBal Linst.stop := by
  constructor; intros e s r h; injection h with h_eq; subst h_eq; rfl

instance : Linst.Hinv Devm.getBal Devm.getBal Linst.return_ := by
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

instance : Linst.Hinv Devm.getBal Devm.getBal Linst.revert := by
  constructor; intros e s r h
  simp only [Linst.Run, Linst.run] at h
  rcases Except.bind_eq_ok h with ⟨v1, h1, h2⟩
  rcases Except.bind_eq_ok h2 with ⟨v2, h3, h4⟩
  rcases Except.bind_eq_ok h4 with ⟨v3, h5, h6⟩
  contradiction

instance : Linst.Hinv Devm.getStor Devm.getStor Linst.stop := by
  constructor; intros e s r h; injection h with h_eq; subst h_eq; rfl

instance : Linst.Hinv Devm.getStor Devm.getStor Linst.return_ := by
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

instance : Linst.Hinv Devm.getStor Devm.getStor Linst.revert := by
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
  -- revert-branch : dst is a valid address
  rcases of_run_branch_revert h_run with ⟨s2, hp2b, h_run⟩
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
  -- revert-branch : wad ≤ caller balance
  rcases of_run_branch_revert h_run with ⟨s4, hp4b, h_run⟩
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

lemma of_handleError_err {sg : Option StateGasRules} {err : EvmError} {d : Devm}
    {ex : Except (EvmError × Jaune.State × AdrSet × Tra) Devm}
    (h : executeCode.handleErrorWith sg (.error ⟨err, d⟩) = ex) :
    (∃ evm2 : Devm, ex = .ok evm2 ∧ evm2.error.isSome = true ∧ evm2.state = d.state) ∨
    (∃ e, ex = .error e) := by
  cases sg <;> simp only [executeCode.handleErrorWith] at h
  · cases err <;>
      simp only [executeCode.handleError] at h <;>
      first
        | exact Or.inl ⟨_, h.symm, rfl, rfl⟩
        | exact Or.inr ⟨_, h.symm⟩
  · cases err <;>
      simp only [executeCode.handleErrorAmsterdam] at h <;>
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
      executeCode.handleErrorWith msg.benv.stat.rules.stateGas (executePrecomp (initEvm msg) adr) = ex) ∨
    (¬ (!msg.disablePrecompiles && decide (msg.benv.stat.rules.isPrecomp adr)) = true ∧
      ∃ ex', xl = .some ⟨initEvm msg, ex'⟩ ∧
      executeCode.handleErrorWith msg.benv.stat.rules.stateGas ex' = ex) := by
  unfold ExecuteCode executeCode.enter at h
  simp only [h_ca] at h
  split_ifs at h with h_pre
  · exact Or.inl ⟨h_pre, h.1, h.2.symm⟩
  · rcases h with ⟨ex', hxl, hh⟩
    exact Or.inr ⟨h_pre, ex', hxl, hh.symm⟩

lemma state_of_executePrecomp_ok {sg : Option StateGasRules} {evm : Evm} {adr : Adr}
    {child : Devm}
    (h : executeCode.handleErrorWith sg (executePrecomp evm adr) = .ok child)
    (h_err : ¬ child.error.isSome = true) :
    child.state = evm.dyna.state := by
  unfold executePrecomp applyPrecompResult at h
  split at h
  · rcases of_handleError_err h with ⟨evm4, h_ok4, h_some4, _⟩ | ⟨e, h_err4⟩
    · injection h_ok4 with h_ok4
      rw [← h_ok4] at h_some4
      exact absurd h_some4 h_err
    · cases h_err4
  · rw [executeCode.handleErrorWith_ok] at h
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
lemma exec_ok_of_handleError {sg : Option StateGasRules} {exn : Execution} {evm' : Devm}
    (h : executeCode.handleErrorWith sg exn = .ok evm')
    (herr : ¬ evm'.error.isSome = true) :
    exn = .ok evm' := by
  cases exn with
  | error ee =>
    obtain ⟨err, d⟩ := ee
    rcases of_handleError_err h with ⟨evm2, h_ok, h_some, _⟩ | ⟨e2, h_e2⟩
    · rw [Except.ok.inj h_ok] at herr; exact absurd h_some herr
    · exact absurd h_e2 (by simp)
  | ok e =>
    rw [executeCode.handleErrorWith_ok] at h; rw [Except.ok.inj h]

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

/-- Gas-schedule twins of the `accessDelegation_*` projection family: the
schedule-parameterized resolution differs from `accessDelegation` only in the
`dagc` component, so every projection proof is the same case split. -/
lemma GasSchedule.accessDelegation_state {gas : GasSchedule} {devm : Devm} {adr : Adr} :
    (gas.accessDelegation devm adr).2.2.2.2.state = devm.state := by
  dsimp only [GasSchedule.accessDelegation]
  cases getDelegatedCodeAddress (devm.state.getCode adr) <;> rfl

lemma GasSchedule.accessDelegation_stack {gas : GasSchedule} {devm : Devm} {adr : Adr} :
    (gas.accessDelegation devm adr).2.2.2.2.stack = devm.stack := by
  dsimp only [GasSchedule.accessDelegation]
  cases getDelegatedCodeAddress (devm.state.getCode adr) <;> rfl

lemma GasSchedule.accessDelegation_memory {gas : GasSchedule} {devm : Devm} {adr : Adr} :
    (gas.accessDelegation devm adr).2.2.2.2.memory = devm.memory := by
  dsimp only [GasSchedule.accessDelegation]
  cases getDelegatedCodeAddress (devm.state.getCode adr) <;> rfl

lemma GasSchedule.accessDelegation_transientStorage {gas : GasSchedule} {devm : Devm} {adr : Adr} :
    (gas.accessDelegation devm adr).2.2.2.2.transientStorage
      = devm.transientStorage := by
  dsimp only [GasSchedule.accessDelegation]
  cases getDelegatedCodeAddress (devm.state.getCode adr) <;> rfl

lemma GasSchedule.accessDelegation_logs {gas : GasSchedule} {devm : Devm} {adr : Adr} :
    (gas.accessDelegation devm adr).2.2.2.2.logs = devm.logs := by
  dsimp only [GasSchedule.accessDelegation]
  cases getDelegatedCodeAddress (devm.state.getCode adr) <;> rfl

lemma GasSchedule.accessDelegation_output {gas : GasSchedule} {devm : Devm} {adr : Adr} :
    (gas.accessDelegation devm adr).2.2.2.2.output = devm.output := by
  dsimp only [GasSchedule.accessDelegation]
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

/-- **The value-carrying `KECCAK256` inversion.**  `keccak256` pushes the hash of
*the memory window its two operands name* — the fact `of_run_keccak256` forgets.

A caller holding a `Mem.Reads` image rewrites the `Mem.read` with
`Mem.Reads.read` and learns which bytes the hash is taken of, which is what
turns "some hash" into "the allowance key of this pair of addresses".

Placed here rather than beside `of_run_keccak256` in `Blanc/CommonProofs.lean` for
the same reason `of_run_call_val` is: the shared module is against this arc's
predeclared elaboration falsifier with little margin, and this module has
headroom.

Like `LOG`, `KECCAK256` only *extends* memory — it reads a window and hashes
it — so the second conjunct is what carries a `Mem.Wf`/`Mem.Reads` pair across
it. -/
lemma of_run_keccak256_val {e : Sevm} {s s' : Devm} (h : Ninst.Run e s Ninst.keccak256 s') :
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

/-- `prefix_of_keccak256`, with the hashed window named and the memory extension
recorded. -/
lemma prefix_of_keccak256_val {e} {x y xs} {s s' : Devm}
    (h : Ninst.Run e s Ninst.keccak256 s') (hp : x :: y :: xs <<+ s.stack) :
    ((s.memory.read x.toNat y.toNat).1.keccak :: xs <<+ s'.stack) ∧
      s'.memory = s.memory.extend x.toNat y.toNat := by
  rcases of_run_keccak256_val h with ⟨x', y', ⟨stk, h2, h3⟩, hm⟩
  rcases of_cons_cons_pref_of_cons_cons_pref hp (pref_of_split h2) with ⟨hx, hy, -⟩
  rw [hx, hy] at hp ⊢
  exact ⟨append_pref h3 (of_append_pref h2 hp), hm⟩

/-- **What a `RETURN` returns.**  `Linst.run .return_` pops the window, charges for
it and sets `Devm.output` from *memory* — so a `Func` ending in `Func.return_` is
specified by an equation about `Devm.output`, never about a stack word, and a
caller holding a `Mem.Reads` image reads the returned bytes off it.

Same placement note as the two inversions above. -/
lemma of_run_return_val {fs : List Func} {sevm : Sevm} {s r : Devm} {i n : B256} {xs}
    (hp : i :: n :: xs <<+ s.stack) (h : Func.Run fs sevm s Func.return_ r) :
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
  refine ⟨?_, hgc.trans (of_run_return_val hu2 h).2⟩
  show Devm.output r = _
  rw [(of_run_return_val hu2 h).1,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    Mem.Reads.read (hm3 ▸ hrd2) 0 32,
    show (32 : Nat) = (1 : B256).toBytes.length from
      (B256.length_toBytes 1).symm,
    Bytes.sliceD_writeAt]

/-! ### Shared one-word return observation

The `AbiReturnsTrue` pair above is the constant-`1` case of a shape every
contract with a `uint256` view or a value-returning entry point ends in: store
the known stack head at memory word zero, then `RETURN` that complete word.
Nothing here names a contract, so the general form belongs beside it rather
than once per contract. -/

/-- A one-word ABI result is observed at the terminal output bytes, not as a
residual stack word: `RETURN` reads its bytes from memory. -/
def ReturnsWord (w : B256) (d : Devm) : Prop :=
  Devm.output d = w.toBytes

/-- Store the known stack head at memory word zero and return that complete
word.  This is the common tail of constant getters, storage getters and
value-returning entry points.  The entry memory image is arbitrary because the
write covers the complete returned window. -/
lemma of_storeReturnWord {fs : List Func} {sevm : Sevm} {s r : Devm}
    {w : B256} {img : Bytes} {xs}
    (hp : w :: xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (h : Func.Run fs sevm s (mstoreAt 0 +++ returnMemoryRange 0 32) r) :
    ReturnsWord w r ∧ Devm.getCode s = Devm.getCode r := by
  rcases of_run_prepend (mstoreAt 0) _ h with ⟨s2, h2, h⟩
  rcases of_run_mstoreAt_val h2 hp with ⟨hp2, hm2⟩
  have hwf2 : Mem.Wf s2.memory := by
    rw [hm2]
    exact h_wf.write _ _
  have hrd2 : Mem.Reads s2.memory (Bytes.writeAt img 0 w.toBytes) := by
    rw [hm2]
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
    (Line.of_inv Devm.getCode (by line_inv) h2).trans
      (Line.of_inv Devm.getCode (by line_inv) h3)
  refine ⟨?_, hgc.trans (of_run_return_val hu2 h).2⟩
  show Devm.output r = _
  rw [(of_run_return_val hu2 h).1,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    Mem.Reads.read (hm3 ▸ hrd2) 0 32,
    show (32 : Nat) = w.toBytes.length from
      (B256.length_toBytes w).symm,
    Bytes.sliceD_writeAt]

/-- The same fragment with no memory side condition at all.  A caller that
holds a `Mem.Wf` / `Mem.Reads` image should prefer `of_storeReturnWord`, whose
proof rewrites through that image; a caller that holds neither gets the same
conclusion here, because `Mem.read_write_zero` reads the just-written word back
off the raw write without knowing anything about the rest of memory. -/
lemma returnsWord_of_storeReturn
    {fs : List Func} {sevm : Sevm} {s r : Devm} {w : B256} {xs}
    (hp : w :: xs <<+ s.stack)
    (h : Func.Run fs sevm s (mstoreAt 0 +++ returnMemoryRange 0 32) r) :
    ReturnsWord w r ∧ Devm.getCode s = Devm.getCode r := by
  rcases of_run_prepend (mstoreAt 0) _ h with ⟨s2, h2, h⟩
  rcases of_run_mstoreAt_val h2 hp with ⟨hp2, hm2⟩
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
  have hne : w.toBytes ≠ [] := by
    intro hnil
    have hlen := B256.length_toBytes w
    rw [hnil] at hlen
    simp at hlen
  have hcode : Devm.getCode s = Devm.getCode s3 :=
    (Line.of_inv Devm.getCode (by line_inv) h2).trans
      (Line.of_inv Devm.getCode (by line_inv) h3)
  refine ⟨?_, hcode.trans (of_run_return_val hu2 h).2⟩
  show Devm.output r = w.toBytes
  rw [(of_run_return_val hu2 h).1, ← hm3, hm2,
    show ((0 : B256) * 32).toNat = 0 from by decide,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    show (32 : Nat) = w.toBytes.length from (B256.length_toBytes w).symm,
    Mem.read_write_zero _ hne]

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
    (h_run : Ninst.Run sevm s Ninst.call sf)
    (hfork : CoveredFork sevm.benvStat.fork) :
    (((0 : B256) :: xs <<+ sf.stack) ∧ Devm.WorldEq s sf) ∨
    ∃ (parent child : Devm) (xl : Xlot) (dp : Bool) (na : Adr)
      (code : ByteArray) (avail pc : Nat),
      Ninst.StepRun pc sevm s Ninst.call xl (.ok sf) ∧
      0 < sevm.depth ∧
      s.stack = g :: c :: v :: ii :: is :: oi :: os :: parent.stack ∧
      parent.state = s.state ∧
      parent.memory
        = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] ∧
      parent.logs = s.logs ∧
      parent.output = s.output ∧
      ((getDelegatedCodeAddress (s.getCode c.toAdr) = none ∧
          na = c.toAdr ∧ code = s.getCode c.toAdr ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (s.getCode c.toAdr) = some d ∧
          na = d ∧ code = s.getCode d ∧ dp = true)) ∧
      Xlot.Filled xl ∧
      ProcessMessage
        (callMsg sevm parent
          (min g.toNat (except64th avail)
            + (if v.toNat = 0 then 0 else gCallStipend))
          v sevm.currentTarget c.toAdr na true false
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
  · cases XStep.run_ofExcept_error_stateGas h_run
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
  · cases XStep.run_ofExcept_error_stateGas h_run
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
  · cases XStep.run_ofExcept_error_stateGas h_run
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
  · cases XStep.run_ofExcept_error_stateGas h_run
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
  · cases XStep.run_ofExcept_error_stateGas h_run
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
  · cases XStep.run_ofExcept_error_stateGas h_run
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
  · cases XStep.run_ofExcept_error_stateGas h_run
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
  rcases hp11 : sevm.benvStat.rules.gas.accessDelegation (addAccessedAddress devm7 c.toAdr) c.toAdr with
    ⟨dp, na, code0, dagc, devm9⟩
  simp only [hp11] at h_run
  have h_st9 : devm9.state = devm7.state := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).state) hp11
    dsimp at h
    rw [← h, GasSchedule.accessDelegation_state]
    rfl
  have h_stk9 : devm9.stack = devm7.stack := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).stack) hp11
    dsimp at h
    rw [← h, GasSchedule.accessDelegation_stack]
    rfl
  have h_mem9 : devm9.memory = devm7.memory := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).memory) hp11
    dsimp at h
    rw [← h, GasSchedule.accessDelegation_memory]
    rfl
  have h_tra9 : devm9.transientStorage = devm7.transientStorage := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).transientStorage) hp11
    dsimp at h
    rw [← h, GasSchedule.accessDelegation_transientStorage]
    rfl
  have h_logs9 : devm9.logs = devm7.logs := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).logs) hp11
    dsimp at h
    rw [← h, GasSchedule.accessDelegation_logs]
    rfl
  have h_output9 : devm9.output = devm7.output := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).output) hp11
    dsimp at h
    rw [← h, GasSchedule.accessDelegation_output]
    rfl
  -- the code the child will run, and the delegation disjunction
  have h_gc7 : (addAccessedAddress devm7 c.toAdr).state.getCode c.toAdr
      = s.getCode c.toAdr := by
    show devm7.state.getCode c.toAdr = s.getCode c.toAdr
    rw [← h_st7]
    rfl
  have h_del :
      (getDelegatedCodeAddress (s.getCode c.toAdr) = none ∧
        na = c.toAdr ∧ code0 = s.getCode c.toAdr ∧ dp = false) ∨
      (∃ d, getDelegatedCodeAddress (s.getCode c.toAdr) = some d ∧
        na = d ∧ code0 = s.getCode d ∧ dp = true) := by
    have h_acc := hp11
    dsimp only [GasSchedule.accessDelegation] at h_acc
    rw [h_gc7] at h_acc
    rcases hdel : getDelegatedCodeAddress (s.getCode c.toAdr) with _ | d <;>
      rw [hdel] at h_acc <;>
      simp only [Prod.mk.injEq] at h_acc
    · exact Or.inl ⟨rfl, h_acc.2.1.symm, h_acc.2.2.1.symm, h_acc.1.symm⟩
    · refine Or.inr ⟨d, rfl, h_acc.2.1.symm, ?_, h_acc.1.symm⟩
      rw [← h_acc.2.2.1]
      show (addAccessedAddress devm7 c.toAdr).state.getCode d = s.getCode d
      show devm7.state.getCode d = s.getCode d
      rw [← h_st7]
      rfl
  -- charge the call gas (the Amsterdam lane contradicts covered forks)
  have hsg : sevm.benvStat.rules.stateGas = none := hfork.rules_stateGas_none
  rcases heqS : sevm.benvStat.rules.stateGas with _ | state
  swap
  · rw [hsg] at heqS; cases heqS
  simp only [heqS] at h_run
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
          child, xl, dp, na, code0, avail, pc, h_step,
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
    (h_run : Ninst.Run sevm s Ninst.call sf)
    (hfork : CoveredFork sevm.benvStat.fork) :
    (((0 : B256) :: xs <<+ sf.stack) ∧ Devm.WorldEq s sf) ∨
    ∃ (parent child : Devm) (xl : Xlot) (dp : Bool) (na : Adr)
      (code : ByteArray) (avail : Nat),
      0 < sevm.depth ∧
      s.stack = g :: c :: v :: ii :: is :: oi :: os :: parent.stack ∧
      parent.state = s.state ∧
      parent.memory
        = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] ∧
      ((getDelegatedCodeAddress (s.getCode c.toAdr) = none ∧
          na = c.toAdr ∧ code = s.getCode c.toAdr ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (s.getCode c.toAdr) = some d ∧
          na = d ∧ code = s.getCode d ∧ dp = true)) ∧
      Xlot.Filled xl ∧
      ProcessMessage
        (callMsg sevm parent
          (min g.toNat (except64th avail)
            + (if v.toNat = 0 then 0 else gCallStipend))
          v sevm.currentTarget c.toAdr na true false
          ((s.memory.read ii.toNat is.toNat).1) code dp)
        xl (.ok child) ∧
      child.error.isSome = false ∧
      (Resume.call parent oi.toNat os.toNat).run (.ok child) = .ok sf ∧
      sf.state = child.state ∧
      sf.returnData = child.output ∧
      sf.memory = parent.memory.write oi.toNat (child.output.take os.toNat) ∧
      sf.stack = (1 : B256) :: parent.stack := by
  rcases of_run_call_val_with_depth_frame hp h_run hfork with hfail | hsuccess
  · exact Or.inl hfail
  · rcases hsuccess with
      ⟨parent, child, xl, dp, na, code, avail, _pc, _hstep,
        hdepth, hstack, hstate, hmemory, hlogs, houtput, hrest⟩
    exact Or.inr ⟨parent, child, xl, dp, na, code, avail,
      hdepth, hstack, hstate, hmemory, hrest⟩

/-- Compatibility projection of `of_run_call_val_with_depth`.  Existing
consumers that do not need the entered-frame depth fact keep the original API. -/
lemma of_run_call_val {sevm : Sevm} {s sf : Devm} {g c v ii is oi os : B256}
    {xs : Stack}
    (hp : (g :: c :: v :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_run : Ninst.Run sevm s Ninst.call sf)
    (hfork : CoveredFork sevm.benvStat.fork) :
    (((0 : B256) :: xs <<+ sf.stack) ∧ Devm.WorldEq s sf) ∨
    ∃ (parent child : Devm) (xl : Xlot) (dp : Bool) (na : Adr)
      (code : ByteArray) (avail : Nat),
      s.stack = g :: c :: v :: ii :: is :: oi :: os :: parent.stack ∧
      parent.state = s.state ∧
      parent.memory
        = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] ∧
      ((getDelegatedCodeAddress (s.getCode c.toAdr) = none ∧
          na = c.toAdr ∧ code = s.getCode c.toAdr ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (s.getCode c.toAdr) = some d ∧
          na = d ∧ code = s.getCode d ∧ dp = true)) ∧
      Xlot.Filled xl ∧
      ProcessMessage
        (callMsg sevm parent
          (min g.toNat (except64th avail)
            + (if v.toNat = 0 then 0 else gCallStipend))
          v sevm.currentTarget c.toAdr na true false
          ((s.memory.read ii.toNat is.toNat).1) code dp)
        xl (.ok child) ∧
      child.error.isSome = false ∧
      (Resume.call parent oi.toNat os.toNat).run (.ok child) = .ok sf ∧
      sf.state = child.state ∧
      sf.returnData = child.output ∧
      sf.memory = parent.memory.write oi.toNat (child.output.take os.toNat) ∧
      sf.stack = (1 : B256) :: parent.stack := by
  rcases of_run_call_val_with_depth hp h_run hfork with h_fail | h_enter
  · exact Or.inl h_fail
  · rcases h_enter with
      ⟨parent, child, xl, dp, na, code, avail, _, h_enter⟩
    exact Or.inr ⟨parent, child, xl, dp, na, code, avail, h_enter⟩

/-- Why a value-carrying `STATICCALL` returned its failure flag.  The depth
case has no child and therefore empty returndata.  The other case records the
exact errored child message, including delegation resolution and calldata. -/
def StatcallFailureCause (sevm : Sevm) (s : Devm)
    (g t ii is oi os : B256) (out : Bytes) : Prop :=
  out = [] ∨
    ∃ (parent child : Devm) (xl : Xlot) (dp : Bool) (na : Adr)
      (code : ByteArray) (avail : Nat),
      0 < sevm.depth ∧
      s.stack = g :: t :: ii :: is :: oi :: os :: parent.stack ∧
      parent.state = s.state ∧
      parent.memory
        = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] ∧
      ((getDelegatedCodeAddress (s.getCode t.toAdr) = none ∧
          na = t.toAdr ∧ code = s.getCode t.toAdr ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (s.getCode t.toAdr) = some d ∧
          na = d ∧ code = s.getCode d ∧ dp = true)) ∧
      Xlot.Filled xl ∧
      ProcessMessage
        (callMsg sevm parent (min g.toNat (except64th avail)) 0
          sevm.currentTarget t.toAdr na true true
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
lemma of_run_staticcall_val_with_depth_cause
    {sevm : Sevm} {s sf : Devm} {g t ii is oi os : B256} {xs : Stack}
    (hp : (g :: t :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_run : Ninst.Run sevm s Ninst.staticcall sf)
    (hfork : CoveredFork sevm.benvStat.fork) :
    (((0 : B256) :: xs <<+ sf.stack) ∧ Devm.WorldEq s sf ∧
      ∃ out : Bytes,
        sf.returnData = out ∧
        sf.memory = (s.memory.extends
          [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write
            oi.toNat (out.take os.toNat) ∧
        StatcallFailureCause sevm s g t ii is oi os out) ∨
    ∃ (parent child : Devm) (xl : Xlot) (dp : Bool) (na : Adr)
      (code : ByteArray) (avail : Nat),
      0 < sevm.depth ∧
      s.stack = g :: t :: ii :: is :: oi :: os :: parent.stack ∧
      parent.state = s.state ∧
      parent.memory
        = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] ∧
      parent.logs = s.logs ∧
      parent.output = s.output ∧
      ((getDelegatedCodeAddress (s.getCode t.toAdr) = none ∧
          na = t.toAdr ∧ code = s.getCode t.toAdr ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (s.getCode t.toAdr) = some d ∧
          na = d ∧ code = s.getCode d ∧ dp = true)) ∧
      Xlot.Filled xl ∧
      ProcessMessage
        (callMsg sevm parent (min g.toNat (except64th avail)) 0
          sevm.currentTarget t.toAdr na true true
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
  · cases XStep.run_ofExcept_error_stateGas h_run
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
  · cases XStep.run_ofExcept_error_stateGas h_run
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
  · cases XStep.run_ofExcept_error_stateGas h_run
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
  · cases XStep.run_ofExcept_error_stateGas h_run
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
  · cases XStep.run_ofExcept_error_stateGas h_run
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
  · cases XStep.run_ofExcept_error_stateGas h_run
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
  rcases hp10 : sevm.benvStat.rules.gas.accessDelegation (addAccessedAddress devm6 t.toAdr) t.toAdr with
    ⟨dp, na, code0, dagc, devm8⟩
  simp only [hp10] at h_run
  have h_st8 : devm8.state = devm6.state := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).state) hp10
    dsimp at h
    rw [← h, GasSchedule.accessDelegation_state]
    rfl
  have h_stk8 : devm8.stack = devm6.stack := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).stack) hp10
    dsimp at h
    rw [← h, GasSchedule.accessDelegation_stack]
    rfl
  have h_mem8 : devm8.memory = devm6.memory := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).memory) hp10
    dsimp at h
    rw [← h, GasSchedule.accessDelegation_memory]
    rfl
  have h_tra8 : devm8.transientStorage = devm6.transientStorage := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).transientStorage) hp10
    dsimp at h
    rw [← h, GasSchedule.accessDelegation_transientStorage]
    rfl
  have h_logs8 : devm8.logs = devm6.logs := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).logs) hp10
    dsimp at h
    rw [← h, GasSchedule.accessDelegation_logs]
    rfl
  have h_output8 : devm8.output = devm6.output := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).output) hp10
    dsimp at h
    rw [← h, GasSchedule.accessDelegation_output]
    rfl
  have h_gc6 : (addAccessedAddress devm6 t.toAdr).state.getCode t.toAdr
      = s.getCode t.toAdr := by
    show devm6.state.getCode t.toAdr = s.getCode t.toAdr
    rw [← h_st6]
    rfl
  have h_del :
      (getDelegatedCodeAddress (s.getCode t.toAdr) = none ∧
        na = t.toAdr ∧ code0 = s.getCode t.toAdr ∧ dp = false) ∨
      (∃ d, getDelegatedCodeAddress (s.getCode t.toAdr) = some d ∧
        na = d ∧ code0 = s.getCode d ∧ dp = true) := by
    have h_acc := hp10
    dsimp only [GasSchedule.accessDelegation] at h_acc
    rw [h_gc6] at h_acc
    rcases hdel : getDelegatedCodeAddress (s.getCode t.toAdr) with _ | d <;>
      rw [hdel] at h_acc <;>
      simp only [Prod.mk.injEq] at h_acc
    · exact Or.inl ⟨rfl, h_acc.2.1.symm, h_acc.2.2.1.symm, h_acc.1.symm⟩
    · refine Or.inr ⟨d, rfl, h_acc.2.1.symm, ?_, h_acc.1.symm⟩
      rw [← h_acc.2.2.1]
      show (addAccessedAddress devm6 t.toAdr).state.getCode d = s.getCode d
      show devm6.state.getCode d = s.getCode d
      rw [← h_st6]
      rfl
  -- charge the parent-side overhead (Amsterdam lane contradicts covered forks)
  have hsg : sevm.benvStat.rules.stateGas = none := hfork.rules_stateGas_none
  rcases heqS : sevm.benvStat.rules.stateGas with _ | state
  swap
  · rw [hsg] at heqS; cases heqS
  simp only [heqS] at h_run
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
            child, xl, dp, na, code0, avail,
            by omega, by rw [e_stack, h_stk_par], h_st_par, h_mem_par,
            h_del, h_fill, ?_, by simpa using herr, rfl⟩
          simpa [ProcessMessage] using run_pm₀
    · right
      refine ⟨(devm9.memExtends
          [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData [],
        child, xl, dp, na, code0, avail,
        by omega, by rw [e_stack, h_stk_par], h_st_par, h_mem_par,
        h_logs_par, h_output_par, h_del,
        h_fill, ?_, by simpa using herr, h_split.symm,
        Resume.call_state h_split.symm, Resume.call_returnData h_split.symm,
        Resume.call_memory h_split.symm,
        by rw [Resume.call_stack_flag h_split.symm, if_neg herr]⟩
      simpa [ProcessMessage] using run_pm₀

/-- The compatibility projection of `of_run_staticcall_val_with_depth_cause`.
Consumers that only need the flag/world/returndata dichotomy do not have to
carry the failure-cause witness. -/
lemma of_run_staticcall_val_with_depth
    {sevm : Sevm} {s sf : Devm} {g t ii is oi os : B256} {xs : Stack}
    (hp : (g :: t :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_run : Ninst.Run sevm s Ninst.staticcall sf)
    (hfork : CoveredFork sevm.benvStat.fork) :
    (((0 : B256) :: xs <<+ sf.stack) ∧ Devm.WorldEq s sf ∧
      ∃ out : Bytes,
        sf.returnData = out ∧
        sf.memory = (s.memory.extends
          [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write
            oi.toNat (out.take os.toNat)) ∨
    ∃ (parent child : Devm) (xl : Xlot) (dp : Bool) (na : Adr)
      (code : ByteArray) (avail : Nat),
      0 < sevm.depth ∧
      s.stack = g :: t :: ii :: is :: oi :: os :: parent.stack ∧
      parent.state = s.state ∧
      parent.memory
        = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] ∧
      ((getDelegatedCodeAddress (s.getCode t.toAdr) = none ∧
          na = t.toAdr ∧ code = s.getCode t.toAdr ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (s.getCode t.toAdr) = some d ∧
          na = d ∧ code = s.getCode d ∧ dp = true)) ∧
      Xlot.Filled xl ∧
      ProcessMessage
        (callMsg sevm parent (min g.toNat (except64th avail)) 0
          sevm.currentTarget t.toAdr na true true
          ((s.memory.read ii.toNat is.toNat).1) code dp)
        xl (.ok child) ∧
      child.error.isSome = false ∧
      (Resume.call parent oi.toNat os.toNat).run (.ok child) = .ok sf ∧
      sf.state = child.state ∧
      sf.returnData = child.output ∧
      sf.memory = parent.memory.write oi.toNat (child.output.take os.toNat) ∧
      sf.stack = (1 : B256) :: parent.stack := by
  rcases of_run_staticcall_val_with_depth_cause hp h_run hfork with hfail | hsuccess
  · rcases hfail with ⟨hstack, hworld, out, hret, hmem, hcause⟩
    exact Or.inl ⟨hstack, hworld, out, hret, hmem⟩
  · rcases hsuccess with
      ⟨parent, child, xl, dp, na, code, avail,
        hdepth, hstack, hstate, hmemory, hlogs, houtput, hrest⟩
    exact Or.inr ⟨parent, child, xl, dp, na, code, avail,
      hdepth, hstack, hstate, hmemory, hrest⟩

/-- The deeper-frame induction hypothesis, as the ladder's consumers use it:
every successful sub-execution of `p` at `ca` strictly below depth `k` takes
`σ` to `ρ`.  Generic in the program and in both predicates. -/
def Exec.InvDepth (k : Nat) (ca : Adr) (p : Prog)
  (σ : Sevm → Devm → Prop) (ρ : Sevm → Devm → Prop) : Prop :=
  ForallDeeperAt k ca p (λ _ sevm pre exn _ =>
    CoveredFork sevm.benvStat.fork → σ sevm pre → ifOk (ρ sevm) exn)


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
    obtain ⟨evm2, h_r0, h_settle⟩ := processMessage.settle_ok_cases hset.symm
    subst h_r0
    rcases h_settle with ⟨h_err2, h_child⟩ | ⟨h_err2, h_child⟩
    · apply funext
      apply getStor_eq_of_state_eq
      rw [h_inter_state, ← h_child]
      exact hc_state
    · subst h_child
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

/-- A successful Amsterdam CALL resumption finishes in a state supplied by the
child.  Gas and meta-data reconciliation do not alter that state. -/
private lemma resume_callAmsterdam_state
    {state : StateGasRules} {parent child sf : Devm}
    {oi os : Nat} {nac : Bool}
    (h : (Resume.callAmsterdam state parent oi os nac).run (.ok child) = .ok sf) :
    sf.state = child.state := by
  have key : ∀ d : Devm, d.state = child.state → ∀ v : B256, ∀ o : Bytes,
      (d.push v >>= fun d' => .ok (d'.memWrite oi o)) = .ok sf →
        sf.state = child.state := by
    intro d hd v o hh
    cases hpush : d.push v with
    | error e =>
        simp [hpush] at hh
    | ok d' =>
        simp only [hpush, bind, Except.bind] at hh
        have hpushFrame := Devm.push_instructionFrame v d
        rw [hpush] at hpushFrame
        have hpushFrame' : Devm.InstructionFrame d d' := hpushFrame
        have hmemFrame : Devm.InstructionFrame d' (d'.memWrite oi o) :=
          Devm.memWrite_instructionFrame d' oi o
        have eq : d'.memWrite oi o = sf := Except.ok.inj hh
        rw [← eq, ← hmemFrame.state, ← hpushFrame'.state, hd]
  unfold Resume.run liftToExecution at h
  dsimp only [bind, Except.bind, Except.assert] at h
  split at h
  · by_cases hP : child.AmsterdamFailedChildSettled
    · rw [ite_eq_left hP] at h
      dsimp only at h
      by_cases hnac : nac = true
      · rw [ite_eq_left hnac] at h
        exact key (Devm.creditStateGasRefund state.newAccount
          (incorporateChildAmsterdamOnError parent child child.output)) rfl 0
          (child.output.take os) h
      · rw [ite_eq_right hnac] at h
        exact key (incorporateChildAmsterdamOnError parent child child.output) rfl 0
          (child.output.take os) h
    · rw [ite_eq_right hP] at h
      cases h
  · by_cases hP : child.AmsterdamChildUncommitted
    · rw [ite_eq_left hP] at h
      dsimp only at h
      exact key (incorporateChildAmsterdamOnSuccess parent child child.output) rfl 1
        (child.output.take os) h
    · rw [ite_eq_right hP] at h
      cases h

/-- A successful synchronous Amsterdam generic call cannot change persistent
storage.  Its preflight only changes gas, and a childless call cannot commit a
child state. -/
lemma GenericCallAmsterdam.none_getStor_eq
    {sevm : Sevm} {state : StateGasRules} {devm inter : Devm}
    {gas reservoir : Nat} {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray} {dp nac ib : Bool}
    (h_run : GenericCallAmsterdam sevm state devm gas reservoir value caller target
      codeAddress stv isStatic ii is oi os code dp nac ib .none (.ok inter)) :
    Devm.getStor inter = Devm.getStor devm := by
  unfold GenericCallAmsterdam genericCallAmsterdam.step at h_run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_run
  repeat' split at h_run
  all_goals simp only [XStep.ofExcept, XStep.Run] at h_run
  · cases h_run.2
  · rename_i h_push
    apply funext
    intro a
    change (inter.state.get a).stor = (devm.state.get a).stor
    rw [Except.ok.inj h_run.2, ← (Devm.push_of_push h_push).state]
    by_cases hnac : nac = true
    · rw [ite_eq_left hnac]
      rfl
    · rw [ite_eq_right hnac]
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
    · unfold Resume.run liftToExecution at hres
      cases hres
    have h_inter_state : inter.state = child.state :=
      resume_callAmsterdam_state hres.symm
    obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp hframe
    unfold FrameBody at hbody
    rcases eq_bt : childMsg.benvAfterTransfer with e | benv <;>
      rw [eq_bt] at hbody
    · rw [hbody.2, processMessage.settle_error] at hset
      cases hset
    have run_ec : ExecuteCode (childMsg.withBenv benv) .none r0 := hbody
    obtain ⟨evm2, h_r0, h_settle⟩ := processMessage.settle_ok_cases hset.symm
    subst h_r0
    rcases h_settle with ⟨h_err2, h_child⟩ | ⟨h_err2, h_child⟩
    · apply funext
      apply getStor_eq_of_state_eq
      rw [h_inter_state, ← h_child]
      exact hc_state
    · subst h_child
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

/-- The Amsterdam creation access prefix changes only instruction-frame
metadata and therefore preserves persistent storage. -/
private lemma create_access_getStor
    {sevm : Sevm} {devm : Devm} {newAddress : Adr} :
    Devm.getStor
      (Devm.balReadAccount sevm.benvStat.rules newAddress
        (addAccessedAddress
          (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget
            (devm.withReturnData []))
          newAddress)) =
      Devm.getStor devm := by
  calc
    Devm.getStor
        (Devm.balReadAccount sevm.benvStat.rules newAddress
          (addAccessedAddress
            (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget
              (devm.withReturnData []))
            newAddress)) =
        Devm.getStor
          (addAccessedAddress
            (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget
              (devm.withReturnData []))
            newAddress) := by
          funext a
          exact (Devm.balReadAccount_instructionFrame _ _ _).getStor a |>.symm
    _ = Devm.getStor
          (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget
            (devm.withReturnData [])) := by
          funext a
          exact (addAccessedAddress_instructionFrame _ _).getStor a |>.symm
    _ = Devm.getStor devm := by
          funext a
          exact (Devm.balReadAccount_instructionFrame _ _ _).getStor a |>.symm

private lemma create_collision_getStor
    {sevm : Sevm} {devm d : Devm}
    (hd : Devm.getStor d = Devm.getStor devm) :
    Devm.getStor (d.withholdCreateGas.2.incrNonce sevm.currentTarget) =
      Devm.getStor devm := by
  calc
    Devm.getStor (d.withholdCreateGas.2.incrNonce sevm.currentTarget) =
        Devm.getStor d.withholdCreateGas.2 := by
      funext a
      exact State.incrNonce_get_stor
    _ = Devm.getStor d := by
      funext a
      exact (Devm.withholdCreateGas_instructionFrame d).getStor a |>.symm
    _ = Devm.getStor devm := hd

private lemma push_getStor {d inter devm : Devm} {v : B256}
    (hp : d.push v = .ok inter)
    (h : Devm.getStor d = Devm.getStor devm) :
    Devm.getStor inter = Devm.getStor devm := by
  funext a
  change (inter.state.get a).stor = (devm.state.get a).stor
  rw [← (Devm.push_of_push hp).state]
  exact congrFun h a

/-- A successful childless Amsterdam generic create cannot change persistent
storage.  Its direct exits only alter frame metadata or the creator nonce. -/
lemma GenericCreateAmsterdam.none_getStor_eq
    {sevm : Sevm} {state : StateGasRules} {devm inter : Devm}
    {endowment : B256} {newAddress : Adr} {mi ms : Nat}
    (h_run : GenericCreateAmsterdam sevm state devm endowment newAddress mi ms
      .none (.ok inter)) :
    Devm.getStor inter = Devm.getStor devm := by
  unfold GenericCreateAmsterdam genericCreateAmsterdam.step at h_run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_run
  repeat' split at h_run
  all_goals simp only [XStep.ofExcept, XStep.Run] at h_run
  all_goals try cases h_run.2
  · rename_i hpush
    exact push_getStor hpush (by
      funext a
      exact (Devm.balReadAccount_instructionFrame _ _ _).getStor a |>.symm)
  · rename_i hpre hnew xcharge v hchg hcollision xpush hpush
    exact push_getStor hpush
      (create_collision_getStor
        ((Devm.chargeStateGas_getStor hchg).symm.trans create_access_getStor))
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
      unfold Resume.run liftToExecution at hres
      cases hres
    · have hca :
          ((processCreateMessage.msg childMsg).withBenv benv).codeAddress =
            .none := hc_ca
      obtain ⟨exn, h_xl, -⟩ := of_executeCode_noneCode hca hbody
      cases h_xl
  · rename_i hpush
    exact push_getStor hpush
      (create_collision_getStor create_access_getStor)
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
      unfold Resume.run liftToExecution at hres
      cases hres
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
      hf, -, hcal, -, hs⟩ |
    ⟨d, state, e, na, mi, ms, hf, hs⟩ |
    ⟨d, d₀, state, g, reservoir, v, c, t, cadr, stv, isSt, ii, isz, oi,
      osz, code, dp, nac, ib, hf, -, hcal, -, hs⟩ <;> rw [hs] at h_run
  · obtain ⟨-, hex⟩ := h_run
    rw [← hex] at hframe
    have hif : Devm.InstructionFrame devm inter := hframe
    exact (funext hif.getStor).symm
  · exact GenericCreate.none_getStor_eq h_run |>.trans
      (funext hf.getStor).symm
  · exact GenericCall.none_getStor_eq h_run |>.trans
      (funext hf.getStor).symm
  · exact GenericCreateAmsterdam.none_getStor_eq h_run |>.trans
      (funext hf.getStor).symm
  · exact GenericCallAmsterdam.none_getStor_eq h_run |>.trans
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
  | return_ =>
      have hframe := Linst.run_instructionFrame sevm pre .return_ (by decide)
      rw [run] at hframe
      exact (hframe.getStor owner).symm
  | revert =>
      dsimp [Linst.Run, Linst.run] at run
      rcases Except.bind_eq_ok run with ⟨first, hfirst, rest⟩
      rcases Except.bind_eq_ok rest with ⟨second, hsecond, rest⟩
      rcases Except.bind_eq_ok rest with ⟨third, hthird, rest⟩
      contradiction
  | selfdestruct =>
      dsimp [Linst.Run, Linst.run] at run
      cases hsg : sevm.benvStat.rules.stateGas
      · simp only [hsg] at run
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
          rw [← chargedEq]
          split
          · dsimp only
            exact (((Devm.balReadAccount_instructionFrame _ _ _).getStor owner).trans
              ((Devm.balReadAccount_instructionFrame _ _ _).getStor owner)).trans
              ((addAccessedAddress_instructionFrame _ _).getStor owner)
          · dsimp only
            exact ((Devm.balReadAccount_instructionFrame _ _ _).getStor owner).trans
              ((Devm.balReadAccount_instructionFrame _ _ _).getStor owner)
        have transferredEq : Devm.getStor devm2 owner =
            Devm.getStor transferred owner :=
          (of_state_transfer_fields subState).1 owner |>.symm
        have postEq : Devm.getStor transferred owner =
            Devm.getStor post owner := by
          dsimp only [transferred] at final ⊢
          by_cases h_if : sevm.currentTarget ∈
              (devm3.addBal donee (devm1.getAcct sevm.currentTarget).bal).createdAccounts
          · simp only [h_if, if_pos] at final
            have equal := Except.ok.inj final
            rw [← equal]
            exact State.setBal_get_stor.symm
          · simp only [h_if, if_neg] at final
            have equal := Except.ok.inj final
            rw [← equal]
        exact (preToOne.trans (charged.trans
          (transferredEq.trans postEq))).symm
      · simp only [hsg] at run
        rcases Except.bind_eq_ok run with ⟨_, h0, rest⟩
        rcases Except.bind_eq_ok rest with ⟨⟨donee, devm1⟩, pop, rest⟩
        rcases Except.bind_eq_ok rest with ⟨_, asserted, rest⟩
        rcases Except.bind_eq_ok rest with ⟨devm2, charge, rest⟩
        rcases Except.bind_eq_ok rest with ⟨devm2b, stg, rest⟩
        rcases Except.bind_eq_ok rest with ⟨devm3, sub, final⟩
        have hp1 : (donee, devm1).1 = donee := rfl
        have hp2 : (donee, devm1).2 = devm1 := rfl
        rw [hp1, hp2] at final
        have subSome : devm2b.subBal sevm.currentTarget ((if donee ∉ devm1.accessedAddresses then addAccessedAddress devm1 donee else devm1).getAcct sevm.currentTarget).bal = some devm3 := by
          cases eq : devm2b.subBal sevm.currentTarget ((if donee ∉ devm1.accessedAddresses then addAccessedAddress devm1 donee else devm1).getAcct sevm.currentTarget).bal
          · rw [eq] at sub
            contradiction
          · rw [eq] at sub
            injection sub with equal
            subst equal
            rfl
        have subState : devm2b.state.subBal sevm.currentTarget ((if donee ∉ devm1.accessedAddresses then addAccessedAddress devm1 donee else devm1).getAcct sevm.currentTarget).bal = some devm3.state := by
          dsimp [Devm.subBal, Option.bind] at subSome
          cases eq : devm2b.state.subBal sevm.currentTarget ((if donee ∉ devm1.accessedAddresses then addAccessedAddress devm1 donee else devm1).getAcct sevm.currentTarget).bal
          · rw [eq] at subSome
            contradiction
          · rw [eq] at subSome
            injection subSome with equal
            subst equal
            rfl
        let transferred := (devm3.addBal donee ((if donee ∉ devm1.accessedAddresses then addAccessedAddress devm1 donee else devm1).getAcct sevm.currentTarget).bal).emitTransferLog sevm.currentTarget donee ((if donee ∉ devm1.accessedAddresses then addAccessedAddress devm1 donee else devm1).getAcct sevm.currentTarget).bal
        have preToOne : Devm.getStor pre owner = Devm.getStor devm1 owner :=
          congrFun (Devm.popToAdr_getStor_eq pop) owner
        have charged : Devm.getStor devm1 owner = Devm.getStor devm2 owner := by
          have chargedEq := chargeGas_getStor_eq charge
          rw [← chargedEq]
          split
          · exact ((addAccessedAddress_instructionFrame _ _).getStor owner).trans
              (((Devm.balReadAccount_instructionFrame _ _ _).getStor owner).trans
                ((Devm.balReadAccount_instructionFrame _ _ _).getStor owner))
          · exact ((Devm.balReadAccount_instructionFrame _ _ _).getStor owner).trans
              ((Devm.balReadAccount_instructionFrame _ _ _).getStor owner)
        have stged : Devm.getStor devm2 owner = Devm.getStor devm2b owner :=
          congrFun (Devm.chargeStateGas_getStor stg) owner
        have h_tr1 : Devm.getStor devm2b owner =
            Devm.getStor (devm3.addBal donee ((if donee ∉ devm1.accessedAddresses then addAccessedAddress devm1 donee else devm1).getAcct sevm.currentTarget).bal) owner :=
          (of_state_transfer_fields subState).1 owner |>.symm
        have h_tr2 : Devm.getStor (devm3.addBal donee ((if donee ∉ devm1.accessedAddresses then addAccessedAddress devm1 donee else devm1).getAcct sevm.currentTarget).bal) owner =
            Devm.getStor transferred owner :=
          (Devm.emitTransferLog_instructionFrame _ _ _ _).getStor owner
        have transferredEq : Devm.getStor devm2b owner = Devm.getStor transferred owner :=
          h_tr1.trans h_tr2
        have postEq : Devm.getStor transferred owner = Devm.getStor post owner := by
          by_cases h_if : sevm.currentTarget ∈
              ((devm3.addBal donee ((if donee ∉ devm1.accessedAddresses then addAccessedAddress devm1 donee else devm1).getAcct sevm.currentTarget).bal).emitTransferLog sevm.currentTarget donee ((if donee ∉ devm1.accessedAddresses then addAccessedAddress devm1 donee else devm1).getAcct sevm.currentTarget).bal).createdAccounts
          · simp only [h_if, if_pos] at final
            have equal := Except.ok.inj final
            rw [← equal]
            rfl
          · simp only [h_if, if_neg] at final
            have equal := Except.ok.inj final
            rw [← equal]
        exact (preToOne.trans (charged.trans (stged.trans
          (transferredEq.trans postEq)))).symm

/-! ## Clean childless settlement and pointwise balance monotonicity -/

/-- A clean no-slot message with a successful transfer ends at that exact
entry world.  Empty interpreted slots therefore hide no later world-state
change; the only executable no-slot branch is a synchronous precompile. -/
theorem ProcessMessage.none_ok_state_eq_entry_of_clean
    {msg : Msg} {entry : Benv} {post : Devm}
    (run : ProcessMessage msg .none (.ok post))
    (transfer : msg.benvAfterTransfer = .ok entry)
    (clean : post.error.isSome = false) :
    post.state = entry.state := by
  obtain ⟨result, body, settle⟩ := ProcessMessage.iff_body.mp run
  rcases ProcessMessage.clean_input_state_of_settle settle.symm clean with
    ⟨raw, result_eq, _, postState⟩
  unfold FrameBody at body
  rw [transfer, result_eq] at body
  change ExecuteCode (msg.withBenv entry) .none (.ok raw) at body
  unfold ExecuteCode at body
  cases entered : executeCode.enter (msg.withBenv entry) with
  | inl evm =>
      rw [entered] at body
      rcases body with ⟨execution, slot, _⟩
      cases slot
  | inr execution =>
      rw [entered] at body
      rcases executeCode.enter_inr entered with ⟨address, execution_eq⟩
      have handled : executeCode.handleErrorWith
          (msg.withBenv entry).benv.stat.rules.stateGas
          (executePrecomp (initEvm (msg.withBenv entry)) address) =
          .ok raw := by
        rw [← execution_eq, ← body.2]
      exact postState.trans
        (executeCode.handle_precompile_ok_state handled)

/-- A successful call/message with no interpreter child cannot lower the
balance of an address distinct from every actual value-transfer caller. -/
theorem ProcessMessage.targetBalanceMono_of_none
    {ca : Adr} {msg : Msg} {post : Devm}
    (run : ProcessMessage msg .none (.ok post))
    (caller_ne : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (sum_nof : sum msg.benv.state.bal < 2 ^ 256) :
    (msg.benv.state.bal ca).toNat ≤ (post.state.bal ca).toNat := by
  rcases ProcessMessage.none_ok_state_cases run with rollback |
      ⟨entry, transfer, post_eq⟩
  · rw [rollback]
  · rw [post_eq]
    cases shouldTransfer : msg.shouldTransferValue with
    | false =>
        have noTransfer : ¬ msg.shouldTransferValue = true := by
          simp [shouldTransfer]
        have entry_eq := of_benvAfterTransfer_no noTransfer transfer
        subst entry
        exact Nat.le_refl _
    | true =>
        rcases of_benvAfterTransfer shouldTransfer transfer with
          ⟨debit, sub, rfl⟩
        by_cases target_eq : msg.currentTarget = ca
        · subst ca
          change (msg.benv.state.bal msg.currentTarget).toNat ≤
            ((debit.addBal msg.currentTarget msg.value).bal
              msg.currentTarget).toNat
          rw [of_transfer_bal_target sub (caller_ne shouldTransfer) sum_nof]
          omega
        · change (msg.benv.state.bal ca).toNat ≤
            ((debit.addBal msg.currentTarget msg.value).bal ca).toNat
          rw [of_transfer_bal_other sub (caller_ne shouldTransfer) target_eq]

/-- CREATE settlement around a no-interpreter constructor preserves the same
foreign-source monotonicity.  Failed creation rolls back; successful code
deposit changes code only after the inner no-slot message has settled. -/
theorem ProcessCreateMessage.targetBalanceMono_of_none
    {ca : Adr} {msg : Msg} {post : Devm}
    (run : ProcessCreateMessage msg .none (.ok post))
    (caller_ne : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (sum_nof : sum msg.benv.state.bal < 2 ^ 256) :
    (msg.benv.state.bal ca).toNat ≤ (post.state.bal ca).toNat := by
  cases errored : post.error.isSome with
  | true =>
      rw [ProcessCreateMessage.rollback_of_error run errored]
  | false =>
      rcases ProcessCreateMessage.ok_state_eq_inner_of_no_error
          run errored with ⟨inner, innerRun, postBalance⟩
      have callerSeed :
          (processCreateMessage.msg msg).shouldTransferValue = true →
            (processCreateMessage.msg msg).caller ≠ ca := by
        simpa [processCreateMessage.msg, Msg.withBenv] using caller_ne
      have sumSeed :
          sum (processCreateMessage.msg msg).benv.state.bal < 2 ^ 256 := by
        rw [processCreateMessage_msg_bal_eq]
        exact sum_nof
      have innerMono := ProcessMessage.targetBalanceMono_of_none
        innerRun callerSeed sumSeed
      rw [postBalance,
        ← congrFun (processCreateMessage_msg_bal_eq msg) ca]
      exact innerMono

/-- A no-interpreter CALL-family instruction whose actual transfer caller is
distinct from `ca` cannot lower `ca`'s balance. -/
theorem GenericCall.targetBalanceMono_of_none
    {ca : Adr} {sevm : Sevm} {pre : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv istat : Bool}
    {ii is oi os : Nat} {code : ByteArray} {delegated : Bool}
    {post : Devm}
    (run : GenericCall sevm pre gas value caller target codeAddress
      stv istat ii is oi os code delegated .none (.ok post))
    (caller_ne : stv = true → caller ≠ ca)
    (sum_nof : sum pre.state.bal < 2 ^ 256) :
    (pre.state.bal ca).toNat ≤ (post.state.bal ca).toNat := by
  unfold GenericCall genericCall.step at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  · cases run.2
  · rename_i state_eq
    have post_eq := Except.ok.inj run.2
    subst post
    have pushed := Devm.push_instructionFrame 0
      ((pre.withReturnData []).withGasLeft
        ((pre.withReturnData []).gasLeft + gas))
    rw [state_eq] at pushed
    exact Nat.le_of_eq
      (congrArg (fun state : State => (state.bal ca).toNat)
        pushed.state)
  · obtain ⟨result, frameRun, resumeRun⟩ := run
    cases result with
    | error error =>
        simp [Resume.run, liftToExecution] at resumeRun
    | ok child =>
        have callerNe :
            (callMsg sevm (pre.withReturnData [])
              gas value caller target codeAddress stv istat
              ((pre.memory.read ii is).1) code delegated
            ).shouldTransferValue = true →
              (callMsg sevm (pre.withReturnData [])
                gas value caller target codeAddress stv istat
                ((pre.memory.read ii is).1) code delegated
              ).caller ≠ ca := by
          simpa [callMsg] using caller_ne
        have childMono := ProcessMessage.targetBalanceMono_of_none
          frameRun callerNe sum_nof
        have postState : post.state = child.state :=
          Resume.call_state resumeRun.symm
        rw [postState]
        exact childMono

/-- A no-interpreter CREATE-family instruction whose creator is distinct from
`ca` cannot lower `ca`'s balance. -/
theorem GenericCreate.targetBalanceMono_of_none
    {ca : Adr} {sevm : Sevm} {pre : Devm}
    {endowment : B256} {newAddress : Adr} {mi ms : Nat}
    {post : Devm}
    (run : GenericCreate sevm pre endowment newAddress mi ms
      .none (.ok post))
    (target_ne : sevm.currentTarget ≠ ca)
    (sum_nof : sum pre.state.bal < 2 ^ 256) :
    (pre.state.bal ca).toNat ≤ (post.state.bal ca).toNat := by
  unfold GenericCreate genericCreate.step at run
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic,
    Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  · cases run.2
  · cases run.2
  · cases run.2
  · rename_i state_eq
    have post_eq := Except.ok.inj run.2
    subst post
    have pushed := Devm.push_instructionFrame 0
      (((pre.withGasLeft
          (pre.gasLeft - except64th pre.gasLeft)).withReturnData
        []).withGasLeft
          (((pre.withGasLeft
              (pre.gasLeft - except64th pre.gasLeft)).withReturnData
            []).gasLeft + except64th pre.gasLeft))
    rw [state_eq] at pushed
    exact Nat.le_of_eq
      (congrArg (fun state : State => (state.bal ca).toNat)
        pushed.state)
  · cases run.2
  · rename_i state_eq
    have post_eq := Except.ok.inj run.2
    subst post
    have pushed := Devm.push_instructionFrame 0
      (addAccessedAddress
        (((pre.withGasLeft
          (pre.gasLeft - except64th pre.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) newAddress)
    rw [state_eq] at pushed
    rw [← congrFun (genericCreate_prepared_bal sevm pre newAddress) ca]
    exact Nat.le_of_eq
      (congrArg (fun state : State => (state.bal ca).toNat)
        pushed.state)
  · obtain ⟨result, frameRun, resumeRun⟩ := run
    cases result with
    | error error =>
        simp [Resume.run, liftToExecution] at resumeRun
    | ok child =>
        have callerNe :
            (createMsg sevm
              (addAccessedAddress
                (((pre.withGasLeft
                    (pre.gasLeft - except64th pre.gasLeft)).withReturnData
                  []).incrNonce sevm.currentTarget) newAddress)
              (except64th pre.gasLeft) endowment newAddress
              ((pre.memory.read mi ms).1)).shouldTransferValue = true →
            (createMsg sevm
              (addAccessedAddress
                (((pre.withGasLeft
                    (pre.gasLeft - except64th pre.gasLeft)).withReturnData
                  []).incrNonce sevm.currentTarget) newAddress)
              (except64th pre.gasLeft) endowment newAddress
              ((pre.memory.read mi ms).1)).caller ≠ ca := by
          intro _
          simpa [createMsg] using target_ne
        have sumParent :
            sum (createMsg sevm
              (addAccessedAddress
                (((pre.withGasLeft
                    (pre.gasLeft - except64th pre.gasLeft)).withReturnData
                  []).incrNonce sevm.currentTarget) newAddress)
              (except64th pre.gasLeft) endowment newAddress
              ((pre.memory.read mi ms).1)).benv.state.bal < 2 ^ 256 := by
          change sum (addAccessedAddress
            (((pre.withGasLeft
                (pre.gasLeft - except64th pre.gasLeft)).withReturnData
              []).incrNonce sevm.currentTarget) newAddress).state.bal <
                2 ^ 256
          rw [genericCreate_prepared_bal]
          exact sum_nof
        have childMono := ProcessCreateMessage.targetBalanceMono_of_none
          frameRun callerNe sumParent
        have postState : post.state = child.state :=
          Resume.create_state resumeRun.symm
        rw [postState]
        change
          ((addAccessedAddress
            (((pre.withGasLeft
                (pre.gasLeft - except64th pre.gasLeft)).withReturnData
              []).incrNonce sevm.currentTarget) newAddress).state.bal ca).toNat ≤
            (child.state.bal ca).toNat at childMono
        rw [genericCreate_prepared_bal] at childMono
        exact childMono

/-- Every successful no-interpreter executable instruction in a frame whose
current target differs from `ca` cannot lower `ca`'s balance. -/
theorem Xinst.targetBalanceMono_of_none
    {ca : Adr} {sevm : Sevm} {pre post : Devm} {x : Xinst}
    (hfork : CoveredFork sevm.benvStat.fork)
    (run : Xinst.Run sevm pre x .none (.ok post))
    (target_ne : sevm.currentTarget ≠ ca)
    (sum_nof : sum pre.state.bal < 2 ^ 256) :
    (pre.state.bal ca).toNat ≤ (post.state.bal ca).toNat := by
  unfold Xinst.Run at run
  rcases Xinst.step_shapeCovered sevm pre x hfork with
    ⟨ex, step_eq, frame⟩ |
    ⟨d, endowment, newAddress, mi, ms, framePrefix, step_eq⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, inputSize, oi, outputSize, code, delegated, framePrefix, _, callerShape,
      _, step_eq⟩ <;>
    rw [step_eq] at run
  · obtain ⟨-, rfl⟩ := run
    exact Nat.le_of_eq
      (congrArg (fun state : State => (state.bal ca).toNat) frame.state)
  · have sumD : sum d.state.bal < 2 ^ 256 := by
      rw [← framePrefix.state]
      exact sum_nof
    have mono := GenericCreate.targetBalanceMono_of_none
      run target_ne sumD
    rw [framePrefix.state]
    exact mono
  · have sumD : sum d.state.bal < 2 ^ 256 := by
      rw [← framePrefix.state]
      exact sum_nof
    have callerNe : stv = true → caller ≠ ca := by
      intro transfer
      rcases callerShape with ⟨_, caller_eq⟩ | ⟨no_transfer, _⟩
      · rw [caller_eq]
        exact target_ne
      · rw [transfer] at no_transfer
        contradiction
    have mono := GenericCall.targetBalanceMono_of_none
      run callerNe sumD
    rw [framePrefix.state]
    exact mono

/-- Every successful nonrecursive instruction in a foreign frame cannot lower
the observed account's balance. -/
theorem Ninst.targetBalanceMono_of_none
    {ca : Adr} {pc : Nat} {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (hfork : CoveredFork sevm.benvStat.fork)
    (run : Ninst.StepRun pc sevm pre n .none (.ok post))
    (target_ne : sevm.currentTarget ≠ ca)
    (sum_nof : sum pre.state.bal < 2 ^ 256) :
    (pre.state.bal ca).toNat ≤ (post.state.bal ca).toNat := by
  cases n with
  | reg regular =>
      have regularRun : Rinst.run ⟨pc, sevm, pre⟩ regular = .ok post :=
        ((Step.run_ofExecution (xl := (.none : Xlot))).mp run).2.symm
      exact Nat.le_of_eq (congrArg B256.toNat
        (congrFun (Rinst.preserves_bal regularRun) ca))
  | exec executable =>
      simp only [Ninst.StepRun, Ninst.step_exec] at run
      exact Xinst.targetBalanceMono_of_none hfork
        (XStep.run_toStep.mp run) target_ne sum_nof
  | push bytes bound =>
      have frame := Ninst.push_instructionFrame_effectRec
        (hxs := bound) (xl := .none) trivial run
      exact Nat.le_of_eq
        (congrArg (fun state : State => (state.bal ca).toNat) frame.state)
  | dupn imm =>
      have frame := Ninst.dupn_instructionFrame_effectRec
        (xl := .none) trivial run
      exact Nat.le_of_eq
        (congrArg (fun state : State => (state.bal ca).toNat) frame.state)
  | swapn imm =>
      have frame := Ninst.swapn_instructionFrame_effectRec
        (xl := .none) trivial run
      exact Nat.le_of_eq
        (congrArg (fun state : State => (state.bal ca).toNat) frame.state)
  | exchange imm =>
      have frame := Ninst.exchange_instructionFrame_effectRec
        (xl := .none) trivial run
      exact Nat.le_of_eq
        (congrArg (fun state : State => (state.bal ca).toNat) frame.state)

/-- Every successful nonrecursive instruction in a foreign frame preserves
the observed account's persistent storage. -/
theorem Ninst.foreignNone_getStor_eq
    {ca : Adr} {pc : Nat} {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (_hfork : CoveredFork sevm.benvStat.fork)
    (run : Ninst.StepRun pc sevm pre n .none (.ok post))
    (target_ne : sevm.currentTarget ≠ ca) :
    Devm.getStor post ca = Devm.getStor pre ca := by
  cases n with
  | reg regular =>
      have regularRun : Rinst.run ⟨pc, sevm, pre⟩ regular = .ok post :=
        ((Step.run_ofExecution (xl := (.none : Xlot))).mp run).2.symm
      by_cases store : regular = .sstore
      · subst regular
        exact sstore_preserves_getStor_ne regularRun target_ne
      · exact (congrFun (Rinst.preserves_stor store regularRun) ca).symm
  | exec executable =>
      simp only [Ninst.StepRun, Ninst.step_exec] at run
      exact congrFun (Xinst.none_getStor_eq (XStep.run_toStep.mp run)) ca
  | push bytes bound =>
      have frame := Ninst.push_instructionFrame_effectRec
        (hxs := bound) (xl := .none) trivial run
      exact (frame.getStor ca).symm
  | dupn imm =>
      have frame := Ninst.dupn_instructionFrame_effectRec
        (xl := .none) trivial run
      exact (frame.getStor ca).symm
  | swapn imm =>
      have frame := Ninst.swapn_instructionFrame_effectRec
        (xl := .none) trivial run
      exact (frame.getStor ca).symm
  | exchange imm =>
      have frame := Ninst.exchange_instructionFrame_effectRec
        (xl := .none) trivial run
      exact (frame.getStor ca).symm

/-- A successful terminal instruction executed by an account other than `ca`
cannot lower `ca`'s balance.  The only world-changing arm is SELFDESTRUCT,
which either leaves `ca` unrelated or credits it from the foreign source. -/
theorem Linst.targetBalanceMono_of_foreign
    {ca : Adr} {sevm : Sevm} {pre post : Devm} {l : Linst}
    (run : Linst.Run sevm pre l (.ok post))
    (target_ne : sevm.currentTarget ≠ ca)
    (sum_nof : sum pre.state.bal < 2 ^ 256) :
    (pre.state.bal ca).toNat ≤ (post.state.bal ca).toNat := by
  cases l with
  | stop =>
      simp [Linst.Run, Linst.run] at run
      subst post
      exact Nat.le_refl _
  | return_ =>
      have frame := Linst.run_instructionFrame sevm pre .return_ (by decide)
      rw [run] at frame
      exact Nat.le_of_eq
        (congrArg (fun state : State => (state.bal ca).toNat) frame.state)
  | revert =>
      unfold Linst.Run Linst.run at run
      rcases firstPop : pre.popToNat with error | ⟨index, devm1⟩
      · simp [firstPop, bind, Except.bind] at run
      · simp only [firstPop, bind, Except.bind] at run
        rcases secondPop : devm1.popToNat with error | ⟨size, devm2⟩
        · simp [secondPop] at run
        · simp only [secondPop] at run
          rcases charged : chargeGas
              (devm2.extCost [(index, size)]) devm2 with error | devm3
          · simp [charged] at run
          · simp [charged] at run
  | selfdestruct =>
      dsimp [Linst.Run, Linst.run] at run
      cases hsg : sevm.benvStat.rules.stateGas
      · simp only [hsg] at run
        rcases Except.bind_eq_ok run with
          ⟨⟨destination, devm1⟩, popped, rest⟩
        rcases Except.bind_eq_ok rest with
          ⟨devm2, charged, rest⟩
        rcases Except.bind_eq_ok rest with
          ⟨_, asserted, rest⟩
        rcases Except.bind_eq_ok rest with
          ⟨devm3, subtracted, final⟩
        have subtractedSome : devm2.subBal sevm.currentTarget
            (devm1.getAcct sevm.currentTarget).bal = some devm3 := by
          cases equal : devm2.subBal sevm.currentTarget
              (devm1.getAcct sevm.currentTarget).bal
          · rw [equal] at subtracted
            contradiction
          · rw [equal] at subtracted
            injection subtracted with state_eq
            subst state_eq
            rfl
        have subtractedState : devm2.state.subBal sevm.currentTarget
            (devm1.getAcct sevm.currentTarget).bal = some devm3.state := by
          dsimp [Devm.subBal, Option.bind] at subtractedSome
          cases equal : devm2.state.subBal sevm.currentTarget
              (devm1.getAcct sevm.currentTarget).bal
          · rw [equal] at subtractedSome
            contradiction
          · rw [equal] at subtractedSome
            injection subtractedSome with state_eq
            subst state_eq
            rfl
        have chargedBalance : devm2.state.bal = pre.state.bal := by
          have h1 : devm1.getBal = devm2.getBal := by
            funext address
            have hchg := chargeGas_getBal_eq charged address
            rw [hchg]
            split
            · dsimp only
              exact (((Devm.balReadAccount_instructionFrame _ _ _).getBal address).trans
                ((Devm.balReadAccount_instructionFrame _ _ _).getBal address)).trans
                ((addAccessedAddress_instructionFrame _ _).getBal address)
            · dsimp only
              exact ((Devm.balReadAccount_instructionFrame _ _ _).getBal address).trans
                ((Devm.balReadAccount_instructionFrame _ _ _).getBal address)
          have h2 : devm1.getBal = pre.getBal := by
            funext address
            exact Devm.popToAdr_getBal_eq popped address
          change devm2.getBal = pre.getBal
          exact h1.symm.trans h2
        have sumCharged : sum devm2.state.bal < 2 ^ 256 := by
          rw [chargedBalance]
          exact sum_nof
        let transferred := devm3.addBal destination
          (devm1.getAcct sevm.currentTarget).bal
        have transferMono :
            (devm2.state.bal ca).toNat ≤
              (transferred.state.bal ca).toNat := by
          change (devm2.state.bal ca).toNat ≤
            ((devm3.state.addBal destination
              (devm1.getAcct sevm.currentTarget).bal).bal ca).toNat
          by_cases destination_eq : destination = ca
          · subst destination
            rw [of_transfer_bal_target subtractedState target_ne sumCharged]
            omega
          · rw [of_transfer_bal_other subtractedState target_ne destination_eq]
        have postBalance : post.state.bal ca = transferred.state.bal ca := by
          dsimp only [transferred] at final ⊢
          by_cases h_if : sevm.currentTarget ∈
              (devm3.addBal destination (devm1.getAcct sevm.currentTarget).bal).createdAccounts
          · simp only [h_if, if_pos] at final
            have state_eq := Except.ok.inj final
            rw [← state_eq]
            change ((transferred.setBal sevm.currentTarget 0).state.bal ca) =
              transferred.state.bal ca
            show ((transferred.state.setBal sevm.currentTarget 0).get ca).bal =
              (transferred.state.get ca).bal
            rw [State.setBal_get_ne target_ne]
          · simp only [h_if, if_neg] at final
            have state_eq := Except.ok.inj final
            rw [← state_eq]
        rw [← chargedBalance, postBalance]
        exact transferMono
      · simp only [hsg] at run
        rcases Except.bind_eq_ok run with ⟨_, h0, rest⟩
        rcases Except.bind_eq_ok rest with ⟨⟨destination, devm1⟩, popped, rest⟩
        rcases Except.bind_eq_ok rest with ⟨_, asserted, rest⟩
        rcases Except.bind_eq_ok rest with ⟨devm2, charged, rest⟩
        rcases Except.bind_eq_ok rest with ⟨devm2b, stg, rest⟩
        rcases Except.bind_eq_ok rest with ⟨devm3, subtracted, final⟩
        have hp1 : (destination, devm1).1 = destination := rfl
        have hp2 : (destination, devm1).2 = devm1 := rfl
        rw [hp1, hp2] at final
        have subtractedSome : devm2b.subBal sevm.currentTarget
            ((if destination ∉ devm1.accessedAddresses then addAccessedAddress devm1 destination else devm1).getAcct sevm.currentTarget).bal = some devm3 := by
          cases equal : devm2b.subBal sevm.currentTarget
              ((if destination ∉ devm1.accessedAddresses then addAccessedAddress devm1 destination else devm1).getAcct sevm.currentTarget).bal
          · rw [equal] at subtracted
            contradiction
          · rw [equal] at subtracted
            injection subtracted with state_eq
            subst state_eq
            rfl
        have subtractedState : devm2b.state.subBal sevm.currentTarget
            ((if destination ∉ devm1.accessedAddresses then addAccessedAddress devm1 destination else devm1).getAcct sevm.currentTarget).bal = some devm3.state := by
          cases hss : devm2b.state.subBal sevm.currentTarget
              ((if destination ∉ devm1.accessedAddresses then addAccessedAddress devm1 destination else devm1).getAcct sevm.currentTarget).bal with
          | none =>
              have hnone : Devm.subBal devm2b sevm.currentTarget ((if destination ∉ devm1.accessedAddresses then addAccessedAddress devm1 destination else devm1).getAcct sevm.currentTarget).bal = none := by
                simp only [Devm.subBal, hss, Option.bind]; rfl
              rw [hnone] at subtractedSome
              cases subtractedSome
          | some st =>
              simp only [Devm.subBal, hss, Option.bind] at subtractedSome
              have hde : devm3 = devm2b.withState st :=
                (Option.some.inj subtractedSome).symm
              have hst : devm3.state = st := by rw [hde]; rfl
              rw [hst]
        have chargedBalance : devm2b.state.bal = pre.state.bal := by
          have hchg : devm1.getBal = devm2.getBal := by
            funext address
            have h := chargeGas_getBal_eq charged address
            rw [h]
            split
            · exact ((addAccessedAddress_instructionFrame _ _).getBal address).trans
                (((Devm.balReadAccount_instructionFrame _ _ _).getBal address).trans
                  ((Devm.balReadAccount_instructionFrame _ _ _).getBal address))
            · exact ((Devm.balReadAccount_instructionFrame _ _ _).getBal address).trans
                ((Devm.balReadAccount_instructionFrame _ _ _).getBal address)
          have hstg : devm2.getBal = devm2b.getBal := by
            funext address
            exact (chargeStateGas_worldEq_of_ok stg).getBal address
          have hpop : devm1.getBal = pre.getBal := by
            funext address
            exact Devm.popToAdr_getBal_eq popped address
          change devm2b.getBal = pre.getBal
          exact hstg.symm.trans (hchg.symm.trans hpop)
        have sumCharged : sum devm2b.state.bal < 2 ^ 256 := by
          rw [chargedBalance]
          exact sum_nof
        let transferred := (devm3.addBal destination ((if destination ∉ devm1.accessedAddresses then addAccessedAddress devm1 destination else devm1).getAcct sevm.currentTarget).bal).emitTransferLog sevm.currentTarget destination ((if destination ∉ devm1.accessedAddresses then addAccessedAddress devm1 destination else devm1).getAcct sevm.currentTarget).bal
        have transferMono :
            (devm2b.state.bal ca).toNat ≤
              (transferred.state.bal ca).toNat := by
          have hem : transferred.state = (devm3.addBal destination ((if destination ∉ devm1.accessedAddresses then addAccessedAddress devm1 destination else devm1).getAcct sevm.currentTarget).bal).state :=
            (Devm.emitTransferLog_instructionFrame _ _ _ _).state.symm
          rw [hem]
          change (devm2b.state.bal ca).toNat ≤
            ((devm3.state.addBal destination ((if destination ∉ devm1.accessedAddresses then addAccessedAddress devm1 destination else devm1).getAcct sevm.currentTarget).bal).bal ca).toNat
          by_cases destination_eq : destination = ca
          · subst destination_eq
            rw [of_transfer_bal_target subtractedState target_ne sumCharged]
            omega
          · rw [of_transfer_bal_other subtractedState target_ne destination_eq]
        have postBalance : post.state.bal ca = transferred.state.bal ca := by
          by_cases h_if : sevm.currentTarget ∈ ((devm3.addBal destination ((if destination ∉ devm1.accessedAddresses then addAccessedAddress devm1 destination else devm1).getAcct sevm.currentTarget).bal).emitTransferLog sevm.currentTarget destination ((if destination ∉ devm1.accessedAddresses then addAccessedAddress devm1 destination else devm1).getAcct sevm.currentTarget).bal).createdAccounts
          · simp only [h_if, if_pos] at final
            have state_eq := Except.ok.inj final
            rw [← state_eq]
            rfl
          · simp only [h_if, if_neg] at final
            have state_eq := Except.ok.inj final
            rw [← state_eq]
        rw [← chargedBalance, postBalance]
        exact transferMono

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

/-- Amsterdam sibling: the grant-carrying child message still sets
`isStatic := isStaticcall || sevm.isStatic`. -/
theorem genericCallAmsterdam.step_spawn_isStatic
    {sevm : Sevm} {state : StateGasRules} {devm : Devm} {gas reservoir : Nat}
    {value : B256} {caller target codeAddress : Adr}
    {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray}
    {disablePrecompiles newAccountCharged insufficientBalance : Bool}
    {f : Jaune.Frame} {rsm : Resume}
    (hs : genericCallAmsterdam.step sevm state devm gas reservoir value caller
      target codeAddress shouldTransferValue isStaticcall inputIndex inputSize
      outputIndex outputSize code disablePrecompiles newAccountCharged
      insufficientBalance = .spawn f rsm)
    (hstatic : sevm.isStatic = true) :
    f.inner.isStatic = true := by
  simp only [genericCallAmsterdam.step, Bind.bind, Except.bind, Pure.pure,
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
      | exact genericCallAmsterdam.step_spawn_isStatic hs hstatic
      | exact absurd hstatic (by simp_all [assertDynamic, Except.assert])

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

/-- Amsterdam sibling: `isStaticcall := true` still forces a static child. -/
theorem genericCallAmsterdam.step_spawn_isStatic_of_staticcall
    {sevm : Sevm} {state : StateGasRules} {devm : Devm} {gas reservoir : Nat}
    {value : B256} {caller target codeAddress : Adr} {shouldTransferValue : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray}
    {disablePrecompiles newAccountCharged insufficientBalance : Bool}
    {f : Jaune.Frame} {rsm : Resume}
    (hs : genericCallAmsterdam.step sevm state devm gas reservoir value caller
      target codeAddress shouldTransferValue true inputIndex inputSize
      outputIndex outputSize code disablePrecompiles newAccountCharged
      insufficientBalance = .spawn f rsm) :
    f.inner.isStatic = true := by
  simp only [genericCallAmsterdam.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals simp only [Jaune.Frame.ofCall, callMsg, Bool.true_or]

theorem Xinst.step_staticcall_spawn_isStatic
    {sevm : Sevm} {devm : Devm} {f : Jaune.Frame} {rsm : Resume}
    (hs : Xinst.step sevm devm .staticcall = .spawn f rsm) :
    f.inner.isStatic = true := by
  simp only [Xinst.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
  all_goals
    first
      | exact genericCall.step_spawn_isStatic_of_staticcall hs
      | exact genericCallAmsterdam.step_spawn_isStatic_of_staticcall hs

theorem Ninst.step_staticcall_spawn_isStatic
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {f : Jaune.Frame} {rsm : Resume}
    (hspawn : Ninst.step ⟨pc, sevm, pre⟩ Ninst.staticcall = .spawn f rsm pc') :
    f.inner.isStatic = true := by
  have hx : Xinst.step sevm pre .staticcall = .spawn f rsm :=
    XStep.toStep_spawn (by
      simpa only [Ninst.staticcall, Ninst.step_exec] using hspawn)
  exact Xinst.step_staticcall_spawn_isStatic hx

/-- An interpreted child of a `STATICCALL` runs statically. -/
theorem Ninst.step_staticcall_run_isStatic
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {f : Jaune.Frame} {rsm : Resume} {cevm : Evm}
    (hspawn : Ninst.step ⟨pc, sevm, pre⟩ Ninst.staticcall = .spawn f rsm pc')
    (henter : f.enter = .run cevm) :
    cevm.sta.isStatic = true :=
  (Frame.enter_run_isStatic henter).trans
    (Ninst.step_staticcall_spawn_isStatic hspawn)

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

/-- Exact Amsterdam CALL frame and resumption selected by a successful
generic spawn: the grant rides on the child message. -/
theorem genericCallAmsterdam_step_spawn_exact
    {sevm : Sevm} {state : StateGasRules} {devm : Devm} {gas reservoir : Nat}
    {value : B256} {caller target codeAddress : Adr} {stv isSt : Bool}
    {ii isz oi osz : Nat} {code : ByteArray} {dp nac ib : Bool}
    {frame : Frame} {resume : Resume}
    (hspawn : genericCallAmsterdam.step sevm state devm gas reservoir value
      caller target codeAddress stv isSt ii isz oi osz code dp nac ib =
      .spawn frame resume) :
    frame = Frame.ofCall
      ({ callMsg sevm (devm.withReturnData []) gas value caller target
          codeAddress stv isSt
          (((devm.withReturnData []).memory.data.sliceD ii isz 0)) code dp
        with stateGasGrant := reservoir }) ∧
    resume = .callAmsterdam state (devm.withReturnData []) oi osz nac := by
  simp only [genericCallAmsterdam.step, Bind.bind, Except.bind, Pure.pure,
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

/-- An Amsterdam CREATE spawn hands the parent's current target to the child
as caller.  Stated as the caller projection (not the full frame) because the
monadic creation-charge bind gives the two spawn lanes different parent
terms. -/
theorem genericCreateAmsterdam_step_spawn_caller
    {sevm : Sevm} {state : StateGasRules} {devm : Devm} {endowment : B256}
    {newAddress : Adr} {mi ms : Nat}
    {frame : Frame} {resume : Resume}
    (hspawn : genericCreateAmsterdam.step sevm state devm endowment newAddress
      mi ms = .spawn frame resume) :
    frame.inner.caller = sevm.currentTarget := by
  simp only [genericCreateAmsterdam.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hspawn
  repeat' split at hspawn
  all_goals
    simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hspawn
  all_goals obtain ⟨rfl, -⟩ := hspawn
  all_goals rfl

/-- Every recursive instruction child either receives the parent's current
target as its caller or keeps that target as its own execution context.  This
is the common caller-separation fact behind direct callbacks into a distinct
installed contract. -/
theorem Xinst.step_spawn_caller_eq_parent_or_target_eq_parent
    {sevm : Sevm} {devm : Devm} {x : Xinst}
    {frame : Frame} {resume : Resume}
    (spawn : Xinst.step sevm devm x = .spawn frame resume) :
    frame.inner.caller = sevm.currentTarget ∨
      frame.inner.currentTarget = sevm.currentTarget := by
  rcases Xinst.step_shape sevm devm x with ⟨execution, shape, -⟩ |
      ⟨d, endowment, newAddress, mi, ms, -, shape⟩ |
      ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
        ii, isz, oi, osz, code, delegated, -, -, callKind, -, shape⟩ |
      ⟨d, state, endowment, newAddress, mi, ms, -, shape⟩ |
      ⟨d, d₀, state, gas, reservoir, value, caller, target, codeAddress,
        stv, isSt, ii, isz, oi, osz, code, dp, nac, ib, -, -, callKind,
        -, shape⟩ <;>
    rw [shape] at spawn
  · cases spawn
  · rcases genericCreate_step_spawn_exact spawn with ⟨rfl, -⟩
    exact Or.inl rfl
  · rcases genericCall_step_spawn_exact spawn with ⟨rfl, -⟩
    rcases callKind with ⟨-, caller_eq⟩ | ⟨-, target_eq⟩
    · exact Or.inl caller_eq
    · exact Or.inr target_eq
  · exact Or.inl (genericCreateAmsterdam_step_spawn_caller spawn)
  · rcases genericCallAmsterdam_step_spawn_exact spawn with ⟨rfl, -⟩
    rcases callKind with ⟨-, caller_eq⟩ | ⟨-, target_eq⟩
    · exact Or.inl caller_eq
    · exact Or.inr target_eq

/-- A child aimed at `ca` from a parent executing elsewhere cannot itself
have `ca` as caller. -/
theorem Xinst.step_spawn_caller_ne_of_target_eq
    {ca : Adr} {sevm : Sevm} {devm : Devm} {x : Xinst}
    {frame : Frame} {resume : Resume}
    (spawn : Xinst.step sevm devm x = .spawn frame resume)
    (parent_ne : sevm.currentTarget ≠ ca)
    (target_eq : frame.inner.currentTarget = ca) :
    frame.inner.caller ≠ ca := by
  rcases Xinst.step_spawn_caller_eq_parent_or_target_eq_parent spawn with
      caller_eq | child_eq
  · rw [caller_eq]
    exact parent_ne
  · exact (parent_ne (child_eq.symm.trans target_eq)).elim

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
  calc
    (Devm.getStor devm newAddress).isEmpty =
        ((Devm.getStor devm newAddress).size == 0) :=
      Std.TreeMap.isEmpty_eq_size_eq_zero
    _ = true := by simp [sizeZero]

/-! ### What a spawned child frame starts with in memory

Entering a frame runs `initEvm`, whose `Devm` is `initDevm`, whose memory is
`Mem.empty`.  This is the companion of `Frame.enter_run_pc` / `_code` /
`_currentTarget` / `_getCode`, and it is the *only* new machine fact the
memory-well-formedness thread needs: `Mem.Wf` is established at frame entry
and nowhere else, because `Mem.write`'s in-place branch preserves `¬Mem.Wf`
just as faithfully as it preserves `Mem.Wf`. -/

lemma Frame.enter_run_memory {f : Frame} {cevm : Evm} (h : f.enter = .run cevm) :
    cevm.dyna.memory = Mem.empty := by
  obtain ⟨benv, -, rfl⟩ := Frame.enter_run_inv h; rfl

/-- A filled child slot on a call-type instruction carries a frame-entry
`Devm`, so its memory is well-formed. -/
lemma Xinst.some_child_wf {sevm : Sevm} {devm : Devm} {x : Xinst}
    {evm' : Evm} {exn' ex : Execution}
    (h_run : Xinst.Run sevm devm x (.some ⟨evm', exn'⟩) ex) :
    Mem.Wf evm'.dyna.memory := by
  obtain ⟨f, rsm, -, henter, -⟩ := XStep.Run.some_inv h_run
  rw [Frame.enter_run_memory henter]
  exact Mem.wf_empty



/-! ## The quantified open-contract layer

From the conservation arc's Step 6.  Two results sit here, both additive.

**The named statement** is `ContractSpec.preserves_of_dispatch` below: the
invariant of *any* dispatcher-shaped program all of whose targets satisfy
`FuncSound` is preserved by arbitrary executions — `sound_of_dispatch`
composed with `preserves_inv`, named so the quantified claim is a theorem
rather than a proof pattern.  `preservesNoMem_of_dispatch` beside it is the
premise-free form, for a program none of whose targets reads memory; that is
the one `Blanc/Conserved.lean`'s `fmintSpec_preservesNoMem` instantiates.

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



/-! ## Generic message-, transaction- and block-level plumbing

Moved down from `Solvent.lean`, unchanged: the no-deletion (`NoDel`) tier, the
`setDelegation` frame algebra, the transaction-level affordability helpers and
the wei-conservation (`sum_le`) tier.  None of it mentions the contract. -/

lemma of_executeCode_cases {msg : Msg} {xl : Xlot}
    {ex : Except (EvmError × Jaune.State × AdrSet × Tra) Devm}
    (h : ExecuteCode msg xl ex) :
    (∃ adr, executeCode.handleErrorWith msg.benv.stat.rules.stateGas (executePrecomp (initEvm msg) adr) = ex) ∨
    (∃ ex', xl = .some ⟨initEvm msg, ex'⟩ ∧
      executeCode.handleErrorWith msg.benv.stat.rules.stateGas ex' = ex) := by
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
        case halt reason =>
          unfold processCreateMessage.exceptionalHalt
          cases hsg : msg.benv.stat.rules.stateGas <;>
            exact Devm.NoDel.of_eqs (d := evm'.rollback msg.benv.state msg.tenv.transientStorage) rfl rfl
              (Devm.NoDel.rollback h_atd h_ca h.code)
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
    (hfork : CoveredFork sevm.benvStat.fork)
    (inv : Xlot.InvNoDel wa xl)
    (h : Xinst.Run sevm s x xl exn)
    (hnd : Devm.NoDel wa s) : Execution.NoDel wa exn := by
  unfold Xinst.Run at h
  rcases Xinst.step_shapeCovered sevm s x hfork with ⟨ex, hs, hframe⟩ |
    ⟨d, e, na, mi, ms, hf, hs⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, -, -, hs⟩ <;> rw [hs] at h
  · obtain ⟨-, rfl⟩ := h
    exact Execution.NoDel.of_instructionFrame hframe hnd
  · exact GenericCreate.inv_noDel inv h (Devm.NoDel.of_instructionFrame hf hnd)
  · exact GenericCall.inv_noDel inv h (Devm.NoDel.of_instructionFrame hf hnd)


lemma Ninst.inv_noDel_gen {wa : Adr} {pc : Nat} {sevm : Sevm} {devm : Devm}
    {n : Ninst} {xl : Xlot} {exn : Execution}
    (hfork : CoveredFork sevm.benvStat.fork)
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
    exact Xinst.inv_noDel_gen (x := xinst) hfork inv run h
  | dupn imm =>
      have h0 : xl = .none := by
        simp only [Ninst.StepRun, Ninst.step_dupn, Step.run_ofExecution] at run
        exact run.1
      subst h0
      have frame := Ninst.dupn_instructionFrame_effectRec
        (xl := .none) trivial run
      exact Execution.NoDel.of_instructionFrame frame h
  | swapn imm =>
      have h0 : xl = .none := by
        simp only [Ninst.StepRun, Ninst.step_swapn, Step.run_ofExecution] at run
        exact run.1
      subst h0
      have frame := Ninst.swapn_instructionFrame_effectRec
        (xl := .none) trivial run
      exact Execution.NoDel.of_instructionFrame frame h
  | exchange imm =>
      have h0 : xl = .none := by
        simp only [Ninst.StepRun, Ninst.step_exchange, Step.run_ofExecution] at run
        exact run.1
      subst h0
      have frame := Ninst.exchange_instructionFrame_effectRec
        (xl := .none) trivial run
      exact Execution.NoDel.of_instructionFrame frame h

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
    Ninst.EffectRecFork (Devm.NoDelCode wa) n := by
  intro pc sevm pre xl out hfork hxl hrun
  have hnd := fun h =>
    Ninst.inv_noDel_gen hfork (Xlot.invNoDel_of_rel hxl) hrun h
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
    (hfork : CoveredFork sevm.benvStat.fork)
    (run : Exec pc sevm devm exn)
    (h : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  have heff := Exec.effectFork (noDelCode_refl_trans wa).1 (noDelCode_refl_trans wa).2
    (Ninst.noDelCode_effectRec wa) (Jinst.noDelCode_effect wa)
    (Linst.noDelCode_effect wa) run hfork
  cases exn with
  | error e => exact heff h
  | ok d => exact heff h

theorem processMessage_preserves_noDel {wa : Adr} {msg : Msg} {evm : Devm}
    (hfork : CoveredFork msg.benv.stat.fork)
    (h_run : processMessage msg = .ok evm)
    (h : Msg.NoDel wa msg) : Devm.NoDel wa evm := by
  obtain ⟨xl, hfill, hrel⟩ := of_processMessage msg (.ok evm) h_run
  have hinv : Xlot.InvNoDel wa xl := by
    rcases xl with _ | ⟨cevm, cexn⟩
    · trivial
    · intro hnd
      obtain ⟨exc⟩ := hfill
      have hbenv : cevm.sta.benvStat = msg.benv.stat := RunFrame.benvStat_eq hrel
      have hfork_c : CoveredFork cevm.sta.benvStat.fork := by
        rw [hbenv]; exact hfork
      exact Exec.inv_noDel hfork_c exc hnd
  exact ProcessMessage.inv_noDel hinv hrel h

theorem processCreateMessage_preserves_noDel {wa : Adr} {msg : Msg} {evm : Devm}
    (hfork : CoveredFork msg.benv.stat.fork)
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
  have hfork' : CoveredFork (processCreateMessage.msg msg).benv.stat.fork := by
    rw [processCreateMessage.msg_benvStat]; exact hfork
  have h_pm : Devm.NoDel wa evm2 := processMessage_preserves_noDel hfork' hpm0 h_inv_cm
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
          cases hsg : msg.benv.stat.rules.stateGas <;>
            exact Devm.NoDel.of_eqs (d := evm3.rollback msg.benv.state msg.tenv.transientStorage) rfl rfl
              (Devm.NoDel.rollback h_atd h_ca h.code)
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
    (hfork : CoveredFork msg.benv.stat.fork)
    (h_run : processMessageCall msg = .ok ⟨st', out⟩)
    (h : Msg.NoDel wa msg)
    (h_not_del : ¬ isValidDelegation (msg.benv.state.getCode wa)) :
    wa ∉ out.accountsToDelete := by
  have hsg : msg.benv.stat.rules.stateGas = none := hfork.rules_stateGas_none
  unfold processMessageCall at h_run
  split at h_run
  · unfold processMessageCall.create at h_run
    dsimp only at h_run
    rw [hsg] at h_run
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
        have h_nodel := processCreateMessage_preserves_noDel hfork h_evm h_ct h
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
    rw [hsg] at h_run
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
          have h_pc : Msg.NoDel wa (match getDelegatedCodeAddress msg.code with | none => msg | some dca => { benv := msg.benv, tenv := msg.tenv, caller := msg.caller, target := msg.target, currentTarget := msg.currentTarget, gas := msg.gas, value := msg.value, data := msg.data, codeAddress := some dca, code := msg.benv.state.getCode dca, depth := msg.depth, shouldTransferValue := msg.shouldTransferValue, isStatic := msg.isStatic, accessedAddresses := Std.HashSet.insert msg.accessedAddresses dca, accessedStorageKeys := msg.accessedStorageKeys, disablePrecompiles := true, stateGasGrant := msg.stateGasGrant }) := by
            split
            · exact h
            · exact ⟨h.ca, h.code⟩
          have hfork' : CoveredFork (match getDelegatedCodeAddress msg.code with | none => msg | some dca => { benv := msg.benv, tenv := msg.tenv, caller := msg.caller, target := msg.target, currentTarget := msg.currentTarget, gas := msg.gas, value := msg.value, data := msg.data, codeAddress := some dca, code := msg.benv.state.getCode dca, depth := msg.depth, shouldTransferValue := msg.shouldTransferValue, isStatic := msg.isStatic, accessedAddresses := Std.HashSet.insert msg.accessedAddresses dca, accessedStorageKeys := msg.accessedStorageKeys, disablePrecompiles := true, stateGasGrant := msg.stateGasGrant }).benv.stat.fork := by
            have hbenv : (match getDelegatedCodeAddress msg.code with | none => msg | some dca => { benv := msg.benv, tenv := msg.tenv, caller := msg.caller, target := msg.target, currentTarget := msg.currentTarget, gas := msg.gas, value := msg.value, data := msg.data, codeAddress := some dca, code := msg.benv.state.getCode dca, depth := msg.depth, shouldTransferValue := msg.shouldTransferValue, isStatic := msg.isStatic, accessedAddresses := Std.HashSet.insert msg.accessedAddresses dca, accessedStorageKeys := msg.accessedStorageKeys, disablePrecompiles := true, stateGasGrant := msg.stateGasGrant }).benv = msg.benv := by split <;> rfl
            rw [hbenv]; exact hfork
          have h_nodel_evm := processMessage_preserves_noDel hfork' h_pm h_pc
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
            have h_pc : Msg.NoDel wa (match getDelegatedCodeAddress msgDelegation.code with | none => msgDelegation | some dca => { benv := msgDelegation.benv, tenv := msgDelegation.tenv, caller := msgDelegation.caller, target := msgDelegation.target, currentTarget := msgDelegation.currentTarget, gas := msgDelegation.gas, value := msgDelegation.value, data := msgDelegation.data, codeAddress := some dca, code := msgDelegation.benv.state.getCode dca, depth := msgDelegation.depth, shouldTransferValue := msgDelegation.shouldTransferValue, isStatic := msgDelegation.isStatic, accessedAddresses := Std.HashSet.insert msgDelegation.accessedAddresses dca, accessedStorageKeys := msgDelegation.accessedStorageKeys, disablePrecompiles := true, stateGasGrant := msgDelegation.stateGasGrant }) := by
              split
              · exact h_del_nodel
              · exact ⟨h_del_nodel.ca, h_del_nodel.code⟩
            have hfork' : CoveredFork (match getDelegatedCodeAddress msgDelegation.code with | none => msgDelegation | some dca => { benv := msgDelegation.benv, tenv := msgDelegation.tenv, caller := msgDelegation.caller, target := msgDelegation.target, currentTarget := msgDelegation.currentTarget, gas := msgDelegation.gas, value := msgDelegation.value, data := msgDelegation.data, codeAddress := some dca, code := msgDelegation.benv.state.getCode dca, depth := msgDelegation.depth, shouldTransferValue := msgDelegation.shouldTransferValue, isStatic := msgDelegation.isStatic, accessedAddresses := Std.HashSet.insert msgDelegation.accessedAddresses dca, accessedStorageKeys := msgDelegation.accessedStorageKeys, disablePrecompiles := true, stateGasGrant := msgDelegation.stateGasGrant }).benv.stat.fork := by
              have hbenv : (match getDelegatedCodeAddress msgDelegation.code with | none => msgDelegation | some dca => { benv := msgDelegation.benv, tenv := msgDelegation.tenv, caller := msgDelegation.caller, target := msgDelegation.target, currentTarget := msgDelegation.currentTarget, gas := msgDelegation.gas, value := msgDelegation.value, data := msgDelegation.data, codeAddress := some dca, code := msgDelegation.benv.state.getCode dca, depth := msgDelegation.depth, shouldTransferValue := msgDelegation.shouldTransferValue, isStatic := msgDelegation.isStatic, accessedAddresses := Std.HashSet.insert msgDelegation.accessedAddresses dca, accessedStorageKeys := msgDelegation.accessedStorageKeys, disablePrecompiles := true, stateGasGrant := msgDelegation.stateGasGrant }).benv = msgDelegation.benv := by split <;> rfl
              have hstat : msgDelegation.benv.stat = msg.benv.stat :=
                setDelegation_benvStat h_del
              rw [hbenv, hstat]; exact hfork
            have h_nodel_evm := processMessage_preserves_noDel hfork' h_pm h_pc
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
    (hfork : CoveredFork msg.benv.stat.fork)
    (h_run : processMessageCall msg = .ok ⟨st', out⟩)
    (h : Msg.NoDel wa msg)
    (h_not_del : ¬ isValidDelegation (msg.benv.state.getCode wa)) :
    ∀ a ∈ out.accountsToDelete.toList, a ≠ wa := by
  intro a ha heq
  subst heq
  exact processMessageCall_preserves_noDel hfork h_run h h_not_del
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
    {sender : Adr} {intrinsicGas calldataFloorGasCost : Nat}
    (h_validate :
      validateTransaction rules tx sender = .ok ⟨intrinsicGas, calldataFloorGasCost⟩) :
    calldataFloorGasCost ≤ tx.gas := by
  unfold validateTransaction at h_validate
  split at h_validate
  · -- none lane : the max-intrinsic/floor affordability check
    rcases h_cost : calculateIntrinsicCost rules tx sender with ⟨ig, floorCost⟩
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
  · -- some lane : the structural checks cannot fail on an ok run, and the
    -- separate floor check yields the bound
    rcases h_cost : calculateIntrinsicCost rules tx sender with ⟨ig, floorCost⟩
    rw [h_cost] at h_validate
    dsimp only at h_validate
    split at h_validate
    · dsimp only [bind, Except.bind] at h_validate
      cases h_validate
    · dsimp only [bind, Except.bind] at h_validate
      rcases Except.bind_eq_ok h_validate with ⟨_, _, h_validate⟩
      rcases Except.bind_eq_ok h_validate with ⟨_, _, h_validate⟩
      rcases Except.bind_eq_ok h_validate with ⟨_, _, h_validate⟩
      rcases Except.bind_eq_ok h_validate with ⟨_, _, h_validate⟩
      rcases Except.bind_eq_ok h_validate with ⟨_, _, h_validate⟩
      split at h_validate
      · cases h_validate
      · split at h_validate
        · cases h_validate
        · rename_i h_floor
          cases h_limit : rules.tx.maxGas with
          | none =>
            simp only [h_limit] at h_validate
            have h_result := Except.ok.inj h_validate
            simp only [Prod.mk.injEq] at h_result
            obtain ⟨rfl, rfl⟩ := h_result
            omega
          | some maxGas =>
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
    (h_run : processTransaction benv bout tx i = .ok ⟨st, bout'⟩)
    (hgas : benv.stat.rules.stateGas = none) :
    sum st.bal ≤ sum benv.state.bal := by
  unfold processTransaction at h_run
  -- as in `processTransaction_preserves_solvent`: `beginTransaction` touches only
  -- `stat.origState`, which no balance below reads.
  simp only [Benv.beginTransaction] at h_run
  rcases Except.bind_eq_ok h_run with ⟨bout0, hbout0, h_run⟩
  rcases Except.bind_eq_ok h_run with ⟨validationSender, hrec, h_run⟩
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
  -- `hsub` carries the `beginTransaction` stat record; its debit term is
  -- defeq (not syntactic) to the stated one, which is all `exact` needs.
  have hsub_some :
      (benv.state.incrNonce sender).subBal sender
        (tx.gas * effectiveGasPrice +
          if tx.isTypeThree = true then
            calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx
          else
            0).toB256 = some state1 :=
    Option.toExcept_eq_ok hsub
  -- the up-front debit does not wrap
  -- (`hcheck` carries the `beginTransaction` environment; ascribe the bound in
  -- `benv` form so `omega` below sees one blob-fee atom, not two.)
  have hfee_lt : tx.gas * effectiveGasPrice +
        (if tx.isTypeThree = true then
          calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx
        else 0) < 2 ^ 256 :=
    checkTransaction_upfront_lt_modulus hcheck
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
    have hgas_msg : msg.benv.stat.rules.stateGas = none := by
      rw [prepareMessage_benv hprep]
      exact hgas
    have h := processMessageCall_sum_le hgas_msg hpm
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
  -- normalize the goal's settlements to the none-lane arithmetic `h1` uses
  simp only [settleSelfdestructs, settleTransactionGas, BenvStat.rules] at hgas ⊢
  simp only [hgas] at ⊢
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
    (h_run : applyTransactions txis benv bout = .ok ⟨benv', bout'⟩)
    (hgas : benv.stat.rules.stateGas = none) :
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
    exact le_trans (ih h2 hgas) (processTransaction_sum_le h1 hgas)

lemma applyTransactions_benvStat_eq
    {txis : List (Nat × Tx)} {benv benv' : Benv}
    {bout bout' : BlockOutput}
    (h_run : applyTransactions txis benv bout = .ok ⟨benv', bout'⟩) :
    benv'.stat = benv.stat := by
  induction txis generalizing benv bout with
  | nil =>
    rw [applyTransactions] at h_run
    obtain ⟨hb, hbo⟩ := Prod.mk.inj (Except.ok.inj h_run)
    subst hb; rfl
  | cons hd tl ih =>
    obtain ⟨i, tx⟩ := hd
    rw [applyTransactions] at h_run
    obtain ⟨⟨st, bout''⟩, _, h2⟩ := Except.bind_eq_ok h_run
    have h := ih h2
    simpa [Benv.withState] using h

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
      rw [stateTransitionAt_preserves_chainId h_st, ih]

-- A Prague-only schedule is the Prague chain: every `Reach` step is a
-- `ReachUsing (ChainConfig.pragueOnly ch.chainId)` step, because
-- `stateTransitionUsing` on that schedule reduces to `stateTransition`.
-- The corrected `ReachUsing.refl` demands real evidence, so the conversion
-- carries it rather than being true because the identity was ignored: the
-- Prague-only schedule is valid for every identity
-- (`ChainConfig.pragueOnly_valid`), it names the base snapshot's own chain ID
-- by construction, and the base snapshot's context validity is the one fact
-- plain `Reach` never established, so it enters as a hypothesis.
theorem ChainConfig.pragueOnly_forkAt (chainId : UInt64) (t : Nat) :
    (ChainConfig.pragueOnly chainId).forkAt t = .ok .prague := by
  have h : (ChainConfig.pragueOnly chainId).forkAt? t = some .prague := by
    unfold ChainConfig.forkAt? ChainConfig.pragueOnly
    simp
  unfold ChainConfig.forkAt
  simp [ChainConfig.pragueOnly_validate, h, Except.mapError, Bind.bind,
    Except.bind]

/-- A fork a configured lookup selects is one the schedule activates. -/
theorem ChainConfig.forkAt_mem {cfg : ChainConfig} {t : Nat} {f : Fork}
    (h : cfg.forkAt t = .ok f) : f ∈ cfg.activations.map (·.fork) := by
  have hsome : cfg.forkAt? t = some f := by
    unfold ChainConfig.forkAt at h
    cases hv : cfg.validate with
    | error e =>
      simp [hv, Except.mapError, Bind.bind, Except.bind] at h
    | ok u =>
      cases hq : cfg.forkAt? t with
      | none => simp [hv, hq, Except.mapError, Bind.bind, Except.bind] at h
      | some g =>
        simp [hv, hq, Except.mapError, Bind.bind, Except.bind] at h
        rw [h]
  unfold ChainConfig.forkAt? at hsome
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hsome
  exact List.mem_map.mpr
    ⟨a, List.mem_of_mem_filter (List.mem_of_getLast? ha), rfl⟩

/-- Every fork the mainnet schedule selects is covered: its activations are
exactly Prague, Osaka, BPO1, and BPO2. -/
theorem mainnetChainConfig_covered (t : Nat) (f : Fork)
    (h : mainnetChainConfig.forkAt t = .ok f) : CoveredFork f := by
  have hmem := ChainConfig.forkAt_mem h
  simp only [mainnetChainConfig, List.map_cons, List.map_nil] at hmem
  exact hmem

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
        ChainConfig.pragueOnly_forkAt]
      exact h_st


end Blanc
