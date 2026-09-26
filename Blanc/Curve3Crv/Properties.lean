-- Curve3Crv/Properties.lean : theorems of the 3Crv token model.

import Blanc.Curve3Crv.Model

/-!
# Properties of the 3Crv token model

Stated, not inherited: the model has no Blanc implementation to agree with, so
its intended behaviour is fixed here as theorems.

* exact success conditions of every state-changing function (`*_eq_ok`);
* supply conservation `totalSupply = Σ balanceOf` across every call
  (`step_conserved`, seeded by `init_conserved`);
* only the minter changes the supply or the minter (`supply_change_by_minter`,
  `minter_change_by_minter`);
* allowance semantics: a non-minter `transferFrom` spends exactly the value
  (no infinite approval at this revision: `transferFrom_spends_max_allowance`),
  the minter bypasses allowances, `approve` enforces zero-first, and only the
  owner's `approve` or the spender's `transferFrom` moves an allowance
  (`allowance_change_authorized`);
* a balance falls only by its holder's own call, the minter's call, or a
  spender's allowance-covered `transferFrom` (`balance_debit_authorized`);
* with conservation, the overflow reverts are dead and the source comments'
  "reverts on insufficient balance/allowance" are the exact conditions
  (`transfer_ok_iff`, `transferFrom_ok_iff`, `mint_ok_iff`, `burnFrom_ok_iff`).
-/

namespace Blanc

open Jaune

namespace Curve3Crv

/-! ## Exact success conditions -/

theorem step_eq_ok {ctx : Ctx} {c : Call} {s : State} {out : Out} :
    step ctx c s = .ok out ↔ ctx.value = 0 ∧ body ctx c s = .ok out := by
  cases c <;> simp only [step, body] <;> (try split_ifs) <;> simp_all

theorem setMinter_eq_ok {ctx : Ctx} {m : B256} {s : State} {out : Out} :
    setMinter ctx m s = .ok out ↔
      m.toNat < 2 ^ 160 ∧ ctx.sender = s.minter ∧
      out = ({ s with minter := m.toAdr }, [], .stop) := by
  unfold setMinter; split_ifs <;> simp_all [eq_comm]

theorem setName_eq_ok {ctx : Ctx} {n y : Bytes} {s : State} {out : Out} :
    setName ctx n y s = .ok out ↔
      n.length ≤ 64 ∧ y.length ≤ 32 ∧ ctx.ownerOf s.minter = some ctx.sender.toB256 ∧
      out = ({ s with name := n, symbol := y }, [], .stop) := by
  unfold setName
  cases hw : ctx.ownerOf s.minter <;> split_ifs <;> simp_all
  split_ifs <;> simp_all [eq_comm]

theorem transfer_eq_ok {ctx : Ctx} {d v : B256} {s : State} {out : Out} :
    transfer ctx d v s = .ok out ↔
      d.toNat < 2 ^ 160 ∧ v ≤ s.balanceOf ctx.sender ∧
      B256.Nof (ledgerDebit s.balanceOf ctx.sender v d.toAdr) v ∧
      out = ({ s with balanceOf :=
                (ledgerCredit (ledgerDebit s.balanceOf ctx.sender v) d.toAdr v) },
             [.transfer ctx.sender d.toAdr v], .bool true) := by
  unfold transfer B256.Nof; split_ifs <;> simp_all [eq_comm]

theorem transferFrom_eq_ok {ctx : Ctx} {f d v : B256} {s : State} {out : Out} :
    transferFrom ctx f d v s = .ok out ↔
      f.toNat < 2 ^ 160 ∧ d.toNat < 2 ^ 160 ∧ v ≤ s.balanceOf f.toAdr ∧
      B256.Nof (ledgerDebit s.balanceOf f.toAdr v d.toAdr) v ∧
      (ctx.sender ≠ s.minter → v ≤ s.allowances f.toAdr ctx.sender) ∧
      out = ({ s with
                balanceOf := ledgerCredit (ledgerDebit s.balanceOf f.toAdr v) d.toAdr v,
                allowances := (if ctx.sender = s.minter then s.allowances else
                  Function.update s.allowances f.toAdr
                    (ledgerDebit (s.allowances f.toAdr) ctx.sender v)) },
             [.transfer f.toAdr d.toAdr v], .bool true) := by
  unfold transferFrom B256.Nof; split_ifs <;> simp_all [eq_comm]

theorem approve_eq_ok {ctx : Ctx} {p v : B256} {s : State} {out : Out} :
    approve ctx p v s = .ok out ↔
      p.toNat < 2 ^ 160 ∧ (v = 0 ∨ s.allowances ctx.sender p.toAdr = 0) ∧
      out = ({ s with allowances := (Function.update s.allowances ctx.sender
                (Function.update (s.allowances ctx.sender) p.toAdr v)) },
             [.approval ctx.sender p.toAdr v], .bool true) := by
  unfold approve; split_ifs <;> simp_all [eq_comm]

theorem mint_eq_ok {ctx : Ctx} {d v : B256} {s : State} {out : Out} :
    mint ctx d v s = .ok out ↔
      d.toNat < 2 ^ 160 ∧ ctx.sender = s.minter ∧ d ≠ 0 ∧
      B256.Nof s.totalSupply v ∧ B256.Nof (s.balanceOf d.toAdr) v ∧
      out = ({ s with totalSupply := s.totalSupply + v,
                      balanceOf := ledgerCredit s.balanceOf d.toAdr v },
             [.transfer 0 d.toAdr v], .bool true) := by
  unfold mint B256.Nof; split_ifs <;> simp_all [eq_comm]

theorem burnFrom_eq_ok {ctx : Ctx} {f v : B256} {s : State} {out : Out} :
    burnFrom ctx f v s = .ok out ↔
      f.toNat < 2 ^ 160 ∧ ctx.sender = s.minter ∧ f ≠ 0 ∧
      v ≤ s.totalSupply ∧ v ≤ s.balanceOf f.toAdr ∧
      out = ({ s with totalSupply := s.totalSupply - v,
                      balanceOf := ledgerDebit s.balanceOf f.toAdr v },
             [.transfer f.toAdr 0 v], .bool true) := by
  unfold burnFrom; split_ifs <;> simp_all [eq_comm]

/-- The six views. -/
def Call.IsView : Call → Prop
  | .totalSupply | .allowance _ _ | .name | .symbol | .decimals | .balanceOf _ => True
  | _ => False

/-- Views leave the state alone and log nothing. -/
theorem body_view {ctx : Ctx} {c : Call} {s : State} {out : Out}
    (hc : c.IsView) (h : body ctx c s = .ok out) : out.1 = s ∧ out.2.1 = [] := by
  cases c <;> simp only [Call.IsView] at hc
  all_goals simp only [body, totalSupplyView, allowanceView, nameView, symbolView,
    decimalsView, balanceOfView] at h
  all_goals (try split_ifs at h)
  all_goals (simp only [Except.ok.injEq] at h; subst h; simp)

/-! ## Supply conservation -/

/-- The token's ledger invariant: the supply is exactly the sum of balances. -/
def Conserved (s : State) : Prop := s.totalSupply.toNat = sum s.balanceOf

theorem Conserved.sumNof {s : State} (h : Conserved s) : SumNof s.balanceOf := by
  unfold SumNof; rw [← h]; exact B256.toNat_lt _

theorem Conserved.le_supply {s : State} (h : Conserved s) (a : Adr) :
    (s.balanceOf a).toNat ≤ s.totalSupply.toNat := by
  rw [h]; exact le_sum

theorem body_conserved {ctx : Ctx} {c : Call} {s : State} {out : Out}
    (hs : Conserved s) (h : body ctx c s = .ok out) : Conserved out.1 := by
  cases c with
  | setMinter m =>
    obtain ⟨-, -, rfl⟩ := setMinter_eq_ok.mp h; exact hs
  | setName n y =>
    obtain ⟨-, -, -, rfl⟩ := setName_eq_ok.mp h; exact hs
  | transfer d v =>
    obtain ⟨-, hv, -, rfl⟩ := transfer_eq_ok.mp h
    show _ = _
    rw [sum_ledgerDebit_credit hs.sumNof hv]; exact hs
  | transferFrom f d v =>
    obtain ⟨-, -, hv, -, -, rfl⟩ := transferFrom_eq_ok.mp h
    show _ = _
    rw [sum_ledgerDebit_credit hs.sumNof hv]; exact hs
  | approve p v =>
    obtain ⟨-, -, rfl⟩ := approve_eq_ok.mp h; exact hs
  | mint d v =>
    obtain ⟨-, -, -, hsup, hbal, rfl⟩ := mint_eq_ok.mp h
    show _ = _
    rw [sum_ledgerCredit hbal, B256.toNat_add_eq_of_nof _ _ hsup, hs]
  | burnFrom f v =>
    obtain ⟨-, -, -, hsup, hbal, rfl⟩ := burnFrom_eq_ok.mp h
    show _ = _
    rw [sum_ledgerDebit hbal, B256.toNat_sub_eq_of_le _ _ hsup, hs]
  | other => simp [body] at h
  | totalSupply | allowance _ _ | name | symbol | decimals | balanceOf _ =>
    have hv := (body_view (by trivial) h).1
    rw [hv]; exact hs

/-- **Supply conservation.** Every successful call preserves
`totalSupply = Σ balanceOf`. -/
theorem step_conserved {ctx : Ctx} {c : Call} {s : State} {out : Out}
    (hs : Conserved s) (h : step ctx c s = .ok out) : Conserved out.1 :=
  body_conserved hs (step_eq_ok.mp h).2

/-- The constructor establishes conservation. -/
theorem init_conserved {ctx : Ctx} {n y : Bytes} {d sup : B256} {s : State}
    {evs : List Event} (h : init ctx n y d sup = .ok (s, evs)) : Conserved s := by
  unfold init at h
  split_ifs at h with _ _ hmul
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  show _ = _
  have word : (Nat.toB256 (sup.toNat * 10 ^ d.toNat)).toNat = sup.toNat * 10 ^ d.toNat :=
    B256.toNat_toB256_of_lt hmul
  rw [sum_eq_add_of_row_add (f := fun _ => 0) (x := ctx.sender)
      (m := sup.toNat * 10 ^ d.toNat) (by simp [word, B256.toNat_zero])
      (fun b hb => by simp [Function.update_of_ne hb])]
  simp [sum, sumBelow_zero, word]

/-! ## Minter authority -/

/-- **Only the minter moves the supply**, and only through `mint`/`burnFrom`. -/
theorem supply_change_by_minter {ctx : Ctx} {c : Call} {s : State} {out : Out}
    (h : step ctx c s = .ok out) (hne : out.1.totalSupply ≠ s.totalSupply) :
    ctx.sender = s.minter ∧ ∃ a v, c = .mint a v ∨ c = .burnFrom a v := by
  obtain ⟨-, h⟩ := step_eq_ok.mp h
  cases c with
  | mint d v => exact ⟨(mint_eq_ok.mp h).2.1, d, v, .inl rfl⟩
  | burnFrom f v => exact ⟨(burnFrom_eq_ok.mp h).2.1, f, v, .inr rfl⟩
  | setMinter m => obtain ⟨-, -, rfl⟩ := setMinter_eq_ok.mp h; exact absurd rfl hne
  | setName n y => obtain ⟨-, -, -, rfl⟩ := setName_eq_ok.mp h; exact absurd rfl hne
  | transfer d v => obtain ⟨-, -, -, rfl⟩ := transfer_eq_ok.mp h; exact absurd rfl hne
  | transferFrom f d v =>
    obtain ⟨-, -, -, -, -, rfl⟩ := transferFrom_eq_ok.mp h; exact absurd rfl hne
  | approve p v => obtain ⟨-, -, rfl⟩ := approve_eq_ok.mp h; exact absurd rfl hne
  | other => simp [body] at h
  | totalSupply | allowance _ _ | name | symbol | decimals | balanceOf _ =>
    have hv := (body_view (by trivial) h).1
    rw [hv] at hne; exact absurd rfl hne

/-- **Only the minter replaces the minter.** -/
theorem minter_change_by_minter {ctx : Ctx} {c : Call} {s : State} {out : Out}
    (h : step ctx c s = .ok out) (hne : out.1.minter ≠ s.minter) :
    ctx.sender = s.minter := by
  obtain ⟨-, h⟩ := step_eq_ok.mp h
  cases c with
  | setMinter m => exact (setMinter_eq_ok.mp h).2.1
  | mint d v => exact (mint_eq_ok.mp h).2.1
  | burnFrom f v => exact (burnFrom_eq_ok.mp h).2.1
  | setName n y => obtain ⟨-, -, -, rfl⟩ := setName_eq_ok.mp h; exact absurd rfl hne
  | transfer d v => obtain ⟨-, -, -, rfl⟩ := transfer_eq_ok.mp h; exact absurd rfl hne
  | transferFrom f d v =>
    obtain ⟨-, -, -, -, -, rfl⟩ := transferFrom_eq_ok.mp h; exact absurd rfl hne
  | approve p v => obtain ⟨-, -, rfl⟩ := approve_eq_ok.mp h; exact absurd rfl hne
  | other => simp [body] at h
  | totalSupply | allowance _ _ | name | symbol | decimals | balanceOf _ =>
    have hv := (body_view (by trivial) h).1
    rw [hv] at hne; exact absurd rfl hne

/-! ## Allowance semantics -/

/-- A non-minter `transferFrom` spends exactly `value` of the caller's
allowance, which must cover it. -/
theorem transferFrom_spends_allowance {ctx : Ctx} {f d v : B256} {s : State} {out : Out}
    (h : step ctx (.transferFrom f d v) s = .ok out) (hm : ctx.sender ≠ s.minter) :
    v ≤ s.allowances f.toAdr ctx.sender ∧
      out.1.allowances f.toAdr ctx.sender = s.allowances f.toAdr ctx.sender - v := by
  obtain ⟨-, h⟩ := step_eq_ok.mp h
  obtain ⟨-, -, -, -, hal, rfl⟩ := transferFrom_eq_ok.mp h
  exact ⟨hal hm, by simp [hm]⟩

/-- **No infinite approval at this revision**: even the all-ones allowance is
decremented by a non-minter `transferFrom` of a nonzero value. -/
theorem transferFrom_spends_max_allowance {ctx : Ctx} {f d v : B256} {s : State}
    {out : Out} (h : step ctx (.transferFrom f d v) s = .ok out)
    (hm : ctx.sender ≠ s.minter) (hv : v ≠ 0) :
    out.1.allowances f.toAdr ctx.sender ≠ s.allowances f.toAdr ctx.sender := by
  obtain ⟨hle, heq⟩ := transferFrom_spends_allowance h hm
  rw [heq]
  intro hc
  apply hv
  have h1 := B256.toNat_sub_eq_of_le _ _ hle
  have h0 := B256.toNat_le_toNat hle
  rw [hc] at h1
  have h2 : v.toNat = 0 := by omega
  exact B256.toNat_inj _ _ (by rw [h2, B256.toNat_zero])

/-- "minter is allowed to transfer anything": the minter's `transferFrom`
leaves every allowance unchanged. -/
theorem transferFrom_minter_keeps_allowances {ctx : Ctx} {f d v : B256} {s : State}
    {out : Out} (h : step ctx (.transferFrom f d v) s = .ok out)
    (hm : ctx.sender = s.minter) : out.1.allowances = s.allowances := by
  obtain ⟨-, h⟩ := step_eq_ok.mp h
  obtain ⟨-, -, -, -, -, rfl⟩ := transferFrom_eq_ok.mp h
  simp [hm]

/-- `approve` enforces the zero-first discipline its comment recommends: a
nonzero allowance can only be set from zero. -/
theorem approve_zero_first {ctx : Ctx} {p v : B256} {s : State} {out : Out}
    (h : step ctx (.approve p v) s = .ok out) (hv : v ≠ 0) :
    s.allowances ctx.sender p.toAdr = 0 ∧ out.1.allowances ctx.sender p.toAdr = v := by
  obtain ⟨-, h⟩ := step_eq_ok.mp h
  obtain ⟨-, hz, rfl⟩ := approve_eq_ok.mp h
  exact ⟨hz.resolve_left hv, by simp⟩

/-- **Only the owner's `approve` or the spender's own non-minter
`transferFrom` moves an allowance.** -/
theorem allowance_change_authorized {ctx : Ctx} {c : Call} {s : State} {out : Out}
    {o p : Adr} (h : step ctx c s = .ok out)
    (hne : out.1.allowances o p ≠ s.allowances o p) :
    (ctx.sender = o ∧ ∃ w v, c = .approve w v ∧ w.toAdr = p) ∨
      (ctx.sender = p ∧ ctx.sender ≠ s.minter ∧ ∃ f d v, c = .transferFrom f d v ∧ f.toAdr = o) := by
  obtain ⟨-, h⟩ := step_eq_ok.mp h
  cases c with
  | approve w v =>
    obtain ⟨-, -, rfl⟩ := approve_eq_ok.mp h
    by_cases ho : o = ctx.sender
    · by_cases hp : p = w.toAdr
      · exact .inl ⟨ho.symm, w, v, rfl, hp.symm⟩
      · subst ho; simp [Function.update_of_ne hp] at hne
    · simp [Function.update_of_ne ho] at hne
  | transferFrom f d v =>
    obtain ⟨-, -, -, -, -, rfl⟩ := transferFrom_eq_ok.mp h
    by_cases hm : ctx.sender = s.minter
    · simp [hm] at hne
    · by_cases ho : o = f.toAdr
      · by_cases hp : p = ctx.sender
        · exact .inr ⟨hp.symm, hm, f, d, v, rfl, ho.symm⟩
        · subst ho; simp [hm, ledgerDebit_ne v hp] at hne
      · simp [hm, Function.update_of_ne ho] at hne
  | setMinter m => obtain ⟨-, -, rfl⟩ := setMinter_eq_ok.mp h; exact absurd rfl hne
  | setName n y => obtain ⟨-, -, -, rfl⟩ := setName_eq_ok.mp h; exact absurd rfl hne
  | transfer d v => obtain ⟨-, -, -, rfl⟩ := transfer_eq_ok.mp h; exact absurd rfl hne
  | mint d v => obtain ⟨-, -, -, -, -, rfl⟩ := mint_eq_ok.mp h; exact absurd rfl hne
  | burnFrom f v => obtain ⟨-, -, -, -, -, rfl⟩ := burnFrom_eq_ok.mp h; exact absurd rfl hne
  | other => simp [body] at h
  | totalSupply | allowance _ _ | name | symbol | decimals | balanceOf _ =>
    have hv := (body_view (by trivial) h).1
    rw [hv] at hne; exact absurd rfl hne

/-! ## Balance authority -/

theorem ledgerCredit_debit_ne {f : Adr → B256} {src dst a : Adr} {v : B256}
    (nof : B256.Nof (ledgerDebit f src v dst) v) (ha : a ≠ src) :
    f a ≤ ledgerCredit (ledgerDebit f src v) dst v a := by
  by_cases hd : a = dst
  · subst hd
    rw [ledgerCredit_self, ledgerDebit_ne v ha]
    rw [ledgerDebit_ne v ha] at nof
    rw [B256.le_iff_toNat_le_toNat, B256.toNat_add_eq_of_nof _ _ nof]
    omega
  · rw [ledgerCredit_ne v hd, ledgerDebit_ne v ha]

/-- **A balance falls only by its holder's own `transfer`, the minter's
`transferFrom`/`burnFrom`, or a spender's allowance-covered `transferFrom`.** -/
theorem balance_debit_authorized {ctx : Ctx} {c : Call} {s : State} {out : Out}
    {a : Adr} (h : step ctx c s = .ok out)
    (hlt : out.1.balanceOf a < s.balanceOf a) :
    ctx.sender = a ∨ ctx.sender = s.minter ∨
      ∃ f d v, c = .transferFrom f d v ∧ f.toAdr = a ∧
        v ≤ s.allowances a ctx.sender ∧
        out.1.allowances a ctx.sender = s.allowances a ctx.sender - v := by
  obtain ⟨-, h⟩ := step_eq_ok.mp h
  have keep : ∀ {t : State}, t.balanceOf = s.balanceOf → ¬ t.balanceOf a < s.balanceOf a :=
    fun ht => by rw [ht]; exact lt_irrefl _
  cases c with
  | transfer d v =>
    obtain ⟨-, -, nof, rfl⟩ := transfer_eq_ok.mp h
    by_cases ha : a = ctx.sender
    · exact .inl ha.symm
    · exact absurd hlt (not_lt.mpr (ledgerCredit_debit_ne nof ha))
  | transferFrom f d v =>
    obtain ⟨-, -, -, nof, hal, rfl⟩ := transferFrom_eq_ok.mp h
    by_cases hm : ctx.sender = s.minter
    · exact .inr (.inl hm)
    by_cases ha : a = f.toAdr
    · subst ha
      exact .inr (.inr ⟨f, d, v, rfl, rfl, hal hm, by simp [hm]⟩)
    · exact absurd hlt (not_lt.mpr (ledgerCredit_debit_ne nof ha))
  | burnFrom f v => exact .inr (.inl (burnFrom_eq_ok.mp h).2.1)
  | mint d v => exact .inr (.inl (mint_eq_ok.mp h).2.1)
  | setMinter m => obtain ⟨-, -, rfl⟩ := setMinter_eq_ok.mp h; exact absurd hlt (keep rfl)
  | setName n y => obtain ⟨-, -, -, rfl⟩ := setName_eq_ok.mp h; exact absurd hlt (keep rfl)
  | approve p v => obtain ⟨-, -, rfl⟩ := approve_eq_ok.mp h; exact absurd hlt (keep rfl)
  | other => simp [body] at h
  | totalSupply | allowance _ _ | name | symbol | decimals | balanceOf _ =>
    have hv := (body_view (by trivial) h).1
    rw [hv] at hlt; exact absurd hlt (lt_irrefl _)

/-! ## Exact revert conditions under conservation

With `Conserved`, every overflow revert is dead: the conditions below are
exactly the source's `assert`s, clamps and the underflow reverts its comments
promise ("the following subtraction would revert on insufficient balance",
"... on insufficient allowance"). -/

theorem transfer_ok_iff {ctx : Ctx} {d v : B256} {s : State} (hs : Conserved s) :
    (∃ out, step ctx (.transfer d v) s = .ok out) ↔
      ctx.value = 0 ∧ d.toNat < 2 ^ 160 ∧ v ≤ s.balanceOf ctx.sender := by
  simp only [step_eq_ok, body, transfer_eq_ok]
  constructor
  · rintro ⟨_, hv, hd, hb, -, -⟩; exact ⟨hv, hd, hb⟩
  · rintro ⟨hv, hd, hb⟩
    exact ⟨_, hv, hd, hb, ledgerDebit_credit_nof hs.sumNof hb, rfl⟩

theorem transferFrom_ok_iff {ctx : Ctx} {f d v : B256} {s : State} (hs : Conserved s) :
    (∃ out, step ctx (.transferFrom f d v) s = .ok out) ↔
      ctx.value = 0 ∧ f.toNat < 2 ^ 160 ∧ d.toNat < 2 ^ 160 ∧ v ≤ s.balanceOf f.toAdr ∧
      (ctx.sender ≠ s.minter → v ≤ s.allowances f.toAdr ctx.sender) := by
  simp only [step_eq_ok, body, transferFrom_eq_ok]
  constructor
  · rintro ⟨_, hv, hf, hd, hb, -, ha, -⟩; exact ⟨hv, hf, hd, hb, ha⟩
  · rintro ⟨hv, hf, hd, hb, ha⟩
    exact ⟨_, hv, hf, hd, hb, ledgerDebit_credit_nof hs.sumNof hb, ha, rfl⟩

theorem approve_ok_iff {ctx : Ctx} {p v : B256} {s : State} :
    (∃ out, step ctx (.approve p v) s = .ok out) ↔
      ctx.value = 0 ∧ p.toNat < 2 ^ 160 ∧ (v = 0 ∨ s.allowances ctx.sender p.toAdr = 0) := by
  simp only [step_eq_ok, body, approve_eq_ok]
  constructor
  · rintro ⟨_, hv, hp, hz, -⟩; exact ⟨hv, hp, hz⟩
  · rintro ⟨hv, hp, hz⟩; exact ⟨_, hv, hp, hz, rfl⟩

theorem mint_ok_iff {ctx : Ctx} {d v : B256} {s : State} (hs : Conserved s) :
    (∃ out, step ctx (.mint d v) s = .ok out) ↔
      ctx.value = 0 ∧ d.toNat < 2 ^ 160 ∧ ctx.sender = s.minter ∧ d ≠ 0 ∧
      B256.Nof s.totalSupply v := by
  simp only [step_eq_ok, body, mint_eq_ok]
  constructor
  · rintro ⟨_, hv, hd, hm, hz, hn, -, -⟩; exact ⟨hv, hd, hm, hz, hn⟩
  · rintro ⟨hv, hd, hm, hz, hn⟩
    have hb : B256.Nof (s.balanceOf d.toAdr) v := by
      have := hs.le_supply d.toAdr
      unfold B256.Nof at hn ⊢; omega
    exact ⟨_, hv, hd, hm, hz, hn, hb, rfl⟩

theorem burnFrom_ok_iff {ctx : Ctx} {f v : B256} {s : State} (hs : Conserved s) :
    (∃ out, step ctx (.burnFrom f v) s = .ok out) ↔
      ctx.value = 0 ∧ f.toNat < 2 ^ 160 ∧ ctx.sender = s.minter ∧ f ≠ 0 ∧
      v ≤ s.balanceOf f.toAdr := by
  simp only [step_eq_ok, body, burnFrom_eq_ok]
  constructor
  · rintro ⟨_, hv, hf, hm, hz, -, hb, -⟩; exact ⟨hv, hf, hm, hz, hb⟩
  · rintro ⟨hv, hf, hm, hz, hb⟩
    have hsup : v ≤ s.totalSupply := by
      rw [B256.le_iff_toNat_le_toNat] at hb ⊢
      exact le_trans hb (hs.le_supply f.toAdr)
    exact ⟨_, hv, hf, hm, hz, hsup, hb, rfl⟩

end Curve3Crv

end Blanc
