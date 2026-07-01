-- Solvent.lean : proof of solvency for WETH implementation


import Blanc.Weth
import Std.Data.TreeMap.Lemmas


def Storage.rest (s : Storage) : Adr → B256 := s ∘ Adr.toB256

-- sum of all WETH balances, provided that s is the storage of WETH contract
def wbsum (s : Storage) : Nat := sum s.rest

def Storage.Solvent (s : Storage) (v : B256) (b : B256) : Prop :=
  wbsum s + v.toNat ≤ b.toNat

def World.Solvent (w : World) (a : Adr) : Prop :=
  Storage.Solvent (w.stor a) 0 (w.bal a)

def Desc.Solvent (s : Desc) (a : Adr) (e : Env) : Prop :=
  (e.cta = a → Storage.Solvent (s.stor a) e.clv (s.bal a)) ∧
  (e.cta ≠ a → Storage.Solvent (s.stor a) 0 (s.bal a))

def Result.Solvent (r : Result) (a : Adr) : Prop :=
  Storage.Solvent (r.stor a) 0 (r.bal a)

lemma solvent_of_same_stor {s s' : Storage} {v : B256} {b b' : B256} :
    s.Solvent v b → s = s' → b = b' → s'.Solvent v b' := by
  intros h0 h1 h2; rw [h1, h2] at h0; exact h0

lemma Rinst.inv_solvent {e s o s' wa}
    (h : Rinst.Run e s o s') (h_ne : e.cta ≠ wa) (h_sv : s.Solvent wa e) : s'.Solvent wa e := by
  simp [h_ne, Desc.Solvent] at h_sv
  simp [h_ne, Desc.Solvent]
  rw [← Rinst.inv_bal h, ← Rinst.inv_stor h h_ne]; exact h_sv

lemma transfer_inv_solvent {a wa} {v} {s : Storage} {b b' : Balances}
    (h_ne : a ≠ wa)
    (h_nof : SumNof b)
    (h_di : Transfer b a v wa b')
    (h_sv : s.Solvent 0 (b wa)) :
    s.Solvent v (b' wa) := by
  simp [Storage.Solvent]
  simp [Storage.Solvent] at h_sv
  rw [B256.toNat_zero, Nat.add_zero] at h_sv
  have h_eq : b' wa = b wa + v := by
    rcases h_di with ⟨_, _, hd, hi⟩
    rw [(hd wa).right h_ne, (hi wa).left rfl]
  have h_nof : B256.Nof (b wa) v := by
    unfold B256.Nof ; apply Nat.lt_of_le_of_lt _ h_nof
    apply le_trans _ <| add_le_sum_of_ne b h_ne.symm
    apply Nat.add_le_add (le_refl _)
    apply B256.toNat_le_toNat h_di.left
  rw [h_eq, B256.toNat_add_eq_of_nof _ _ h_nof]
  apply Nat.add_le_add h_sv (le_refl _)

lemma Xinst.prep_inv_solvent'
    {e s ep sp o rx sw wa}
    (ho : ¬ Xinst.isCall o)
    (h_cr : Xinst.Run' e s ep sp o rx sw)
    (ha : e.cta ≠ wa) (ha' : ep.cta ≠ wa)
    (h_sv : s.Solvent wa e) : sp.Solvent wa ep := by
  simp [Desc.Solvent, ha] at h_sv
  simp [Desc.Solvent, ha']
  cases h_cr <;> try {apply (ho cst).elim} <;>
  { simp [Desc.prep]
    rcases (asm : Transfer _ _ _ _ _) with ⟨_, b, hd, hi⟩
    rw [← (hi wa).right ha', ← (hd wa).right ha]
    apply h_sv }

lemma Env.prep_eq (e : Env) (s : Desc)
    (cta : Adr) (cld : B8L) (cla : Adr)
    (clv : B256) (cda : Adr) (exd : Nat) (wup : Bool) :
    Env.prep (e : Env) (s : Desc)
      (cta : Adr) (cld : B8L) (cla : Adr)
      (clv : B256) (cda : Adr) (exd : Nat) (wup : Bool) =
    { cta := cta, oga := e.oga, gpr := e.gpr, cld := cld, cla := cla,
      clv := clv, code := s.code cda, exd := exd, wup := wup } := by rfl

lemma Xinst.prep_inv_solvent
    {e s ep sp o rx sw wa}
    (ho : Xinst.isCall o)
    (h_cr : Xinst.Run' e s ep sp o rx sw)
    (ha : e.cta ≠ wa) (h_nof : SumNof s.bal)
    (h_sv : s.Solvent wa e) : sp.Solvent wa ep := by
  have h_stor := (Xinst.prep_inv_stor h_cr).symm
  cases h_cr <;> try {cases ho} <;>
  try {rw [Env.prep_eq]; simp [Desc.Solvent, Desc.prep, ha]; apply h_sv.right ha}
  simp [Env.prep, Desc.prep, Desc.Solvent]
  constructor <;> intro ha'
  · apply transfer_inv_solvent ha h_nof
    · rw [← ha']; assumption
    · apply h_sv.right ha
  · rename Balances => bal
    have h_bal' : bal wa = s.bal wa := by
      rcases (asm : Transfer _ _ _ _ _) with ⟨_, b, hd, hi⟩
      rw [(hd wa).right ha, (hi wa).right ha']
    rw [h_bal']; apply h_sv.right ha

-- Precond & Postcond : invariants in the main induction for proof of solvency preservation

structure Precond (wa : Adr) (e : Env) (s : Desc) : Prop where
  (code : some (s.code wa) = Prog.compile weth)
  (nof : sum s.bal < 2 ^ 256)
  (solvent : s.Solvent wa e)

structure Postcond (wa : Adr) (e : Env) (r : Result) : Prop where
  (code : some (r.code wa) = Prog.compile weth)
  (nof : sum r.bal < 2 ^ 256)
  (solvent : r.Solvent wa)

open Ninst

lemma addressMask_eq_shl :
    addressMask = B256.shiftLeft B256.max (160 : Nat).toB256.toNat := by
  rw [toNat_toB256, Nat.lo_eq_of_lt (by omega)]; rfl

theorem B256.invert_zero_eq_max : ~~~ (0 : B256) = .max := by rfl

lemma of_push_addressMask {e} {s s' : Desc} {xs}
    (h_pfx : xs <<+ s.stk) (h_run : Line.Run e s pushAddressMask s') :
    (addressMask :: xs <<+ s'.stk) := by
  rw [addressMask_eq_shl, ← B256.invert_zero_eq_max]
  revert s; simp only [pushAddressMask]; line_pref

lemma of_check_non_address {e} {s s' : Desc} {x xs}
    (h_pfx : x :: xs <<+ s.stk) (h_run : Line.Run e s checkNonAddress s') :
    ∃ y, (y :: xs <<+ s'.stk) ∧ (y = 0 ↔ ValidAdr x) := by
  rename' s' => s''; rcases_append
  rename Line.Run _ _ pushAddressMask _ => h_run
  rename Line.Run _ _ [_] _ => h_run'
  rename Desc => s'
  have h_pfx' := of_push_addressMask h_pfx h_run; clear h_pfx h_run s
  have h_pfx : (addressMask &&& x) :: xs <<+ s''.stk := by
    revert h_run'; revert s'; line_pref
  refine ⟨_, h_pfx, Iff.symm validAdr_iff⟩

lemma of_check_address {e} {s s' : Desc} {x xs} :
    (x :: xs <<+ s.stk) →
    Line.Run e s checkAddress s' →
    ∃ y, (y :: xs <<+ s'.stk) ∧ (y = 0 ↔ ¬ ValidAdr x) := by
  rename' s' => s''; intros h_pfx h_run;
  rcases of_run_append _ h_run with ⟨s', hs', h_run'⟩; clear h_run
  rcases of_check_non_address h_pfx hs'
    with ⟨y, h_pfx', h_iff⟩; clear h_pfx hs' s
  have h_pfx : (ite (y = 0) 1 0 :: xs <<+ s''.stk) := by
    revert h_run'; revert s'; line_pref
  refine' ⟨_, h_pfx, _⟩; rw [← h_iff]
  apply Ne.ite_eq_right_iff <| Ne.symm B256.zero_ne_one

lemma frel_to_address {w : B256} {r} {f g : Storage} :
    ValidAdr w → Frel w r f g → Frel w.toAdr r f.rest g.rest := by
  intros h0 h1 a; constructor <;> intro h3
  · apply (h1 <| Adr.toB256 a).left; rw [← h3, toB256_toAdr h0]
  · apply (h1 <| Adr.toB256 a).right
    intro hc; apply h3; rw [hc, toAdr_toB256]

lemma incrAt_of_incrWbal {e s s' wad dst} (h_dst : ValidAdr dst)
    (h0 : Line.Run e s incrWbal s') (h1 : [wad, dst] <<+ s.stk) :
    Increase dst.toAdr wad (s.stor e.cta).rest (s'.stor e.cta).rest := by
  rcases of_run_append [dup 1, sload] h0 with ⟨s0, h2, h3⟩; clear h0
  have h_s0_stk : ([s.stor e.cta dst, wad, dst] <<+ s0.stk) := by
    rcases of_run_append [dup 1] h2 with ⟨sm, hm, h_run⟩; clear h2
    have h_stk : ([dst, wad, dst] <<+ sm.stk) := by
      clear h_run; revert hm; revert s; line_pref
    have h_stor : s.stor = sm.stor := by linv
    rw [h_stor]
    cases of_run_singleton h_run
    apply prefix_of_sload asm h_stk
  have h_s0_stor : s.stor = s0.stor := by linv
  clear h1 h2
  rcases of_run_append [add, swap 0] h3 with ⟨s1, h1, h2⟩; clear h3
  have h_s1_stk : [dst, (s.stor e.cta dst) + wad] <<+ s1.stk := by
    clear h2 h_s0_stor; revert h1 s0; line_pref
  have h_s1_stor : s.stor = s1.stor := by rw [h_s0_stor]; linv
  clear h1 h_s0_stk h_s0_stor s0
  have h_sstore := of_run_singleton' h2
  have h3 := (frel_of_sstore h_sstore h_s1_stk e.cta).left rfl
  simp [Overwrite] at h3; rw [← h_s1_stor] at h3
  have h4 := frel_to_address h_dst h3
  intro a; refine' ⟨λ ha => _, (h4 a).right⟩
  have h5 : s.stor e.cta dst + wad = s'.stor e.cta dst := by
    have h5 := (h4 a).left ha
    simp [Storage.rest] at h5
    rw [← ha, toB256_toAdr h_dst] at h5
    apply h5
  simp [Storage.rest]
  rw [← ha, toB256_toAdr h_dst, h5]

lemma sstore_inv_stor_rest {x xs} {e} {s s' : Desc} :
  ¬ ValidAdr x →
  (x :: xs <<+ s.stk) →
  Desc.Sstore e s s' →
  (s.stor e.cta).rest = (s'.stor e.cta).rest := by
  intros h_nv h_pfx_fst h_sstore
  have h_pfx : ∃ y, ([x, y] <<+ s.stk) := by
    rcases h_sstore with ⟨x', y, h0, h1⟩; clear h1
    refine' ⟨y, _⟩
    have h_pfx_snd := pref_of_split (Stack.of_diff_nil h0.stk)
    rw [(pref_head_unique h_pfx_fst h_pfx_snd)]
    apply h_pfx_snd
  rcases h_pfx with ⟨y, h_pfx⟩
  apply funext; intro a
  simp [Storage.rest]
  apply ((frel_of_sstore h_sstore h_pfx e.cta).left rfl a.toB256).right
  intro hc; apply h_nv
  refine ⟨a, hc.symm⟩

lemma of_transferFromUpdateSbal {e s₀ sₙ} {sbal wad src}
    (h_src : ValidAdr src) (h_sbal : sbal = s₀.stor e.cta src)
    (h_le : wad ≤ sbal) (hp₀ : [sbal, wad, wad, src] <<+ s₀.stk) :
    Line.Run e s₀ transferFromUpdateSbal sₙ →
    ( Decrease src.toAdr wad (s₀.stor e.cta).rest (sₙ.stor e.cta).rest ∧
      wad ≤ (s₀.stor e.cta).rest src.toAdr ) := by
  lexen 2; lstor; intro h₂
  have hp₁ : [src, sbal - wad, wad, src] <<+ s₁.stk := by lpfx
  have h_ow : Overwrite src (sbal - wad) (s₁.stor e.cta) (sₙ.stor e.cta) :=
    (frel_of_sstore (of_run_singleton' h₂) hp₁ e.cta).left rfl
  simp [Storage.rest]; constructor
  · intro a; constructor <;> intro ha
    · rw [← ha]; simp
      rw [toB256_toAdr h_src, ← h_sbal]
      apply (h_ow src).left rfl
    · apply (h_ow <| Adr.toB256 a).right
      intro hc; apply ha; rw [← toAdr_toB256 a, hc]
  · rw [toB256_toAdr h_src, ← h_sbal]; exact h_le

lemma updateAllowance_inv_stor_rest {wad dst} {e s r}
    (hs : [wad, dst] <<+ s.stk) :
    Func.Run c e s updateAllowance r →
    (s.stor e.cta).rest = (r.stor e.cta).rest := by
  pexen 3; lstor; apply branch_elim
  · intro h; clear h
    apply prepend_kec_next_elim [_, _, _, _, _, _, _, _, _] (_ = _)
    intro hash; pexen 14
    have h_run := run_append h₁ h₂
    clear h₁; lstor; clear h₂
    have hs₂ : [hash, wad, hash] <<+ s₂.stk := by lpfx
    clear s₁; cstate s
    pexec checkAddress
    rcases of_check_address hs₂ h₃ with ⟨va_hash, hs₃, h_hash⟩
    lstor; cstate s₂; apply rev_branch_elim' (_ = _) hs₃
    intro h_eq; simp [h_eq] at h_hash; clear h_eq;
    apply prepend_sload_next_elim [_, _] (_ = _)
    intro amnt; pexen 7
    have hs₄ : [~~~ amnt =? 0, amnt, wad, hash] <<+ s₄.stk := by lpfx
    lstor; cstate s₃; apply branch_elim' (_ = _) hs₄ <;> intro h
    · intro h₅; rw [Func.of_inv Desc.stor Result.stor _ h₅]; prog_inv
    · clear h; pexen 4;
      have hs₅ : [amnt <? wad, amnt, wad, hash] <<+ s₅.stk := by lpfx
      lstor; cstate s₄; apply rev_branch_elim' (_ = _) hs₅
      intro h; clear h; pexen 3
      have hs₆ : [hash, amnt - wad] <<+ s₆.stk := by lpfx
      lstor; cstate s₅; pexen 1; intro h₈
      rw [sstore_inv_stor_rest h_hash hs₆ <| of_run_singleton' h₇]
      rw [Func.of_inv Desc.stor Result.stor _ h₈]; prog_inv
  · intro _ h; rw [Func.of_inv Desc.stor Result.stor _ h]; prog_inv

lemma transfer_of_transferFrom {e : Env} {s : Desc} {r : Result} :
    Func.Run c e s transferFrom r →
    ∃ (x : B256) (a a' : Adr),
      Transfer (s.stor e.cta).rest a x a' (r.stor e.cta).rest := by
  rename' s => s₀; apply cdl_prepend_elim; intro src
  have hp₀ : [] <<+ s₀.stk := nil_pref; pexec [_, _]
  have hp₁ : [src, src] <<+ s₁.stk := by lpfx
  lstor; cstate s₀; pexec checkNonAddress
  rcases of_check_non_address hp₁ asm with ⟨na_src, hp₂, h_src⟩
  lstor; cstate s₁; apply rev_branch_elim; intro hp₂'
  simp [(pref_head_unique hp₂ hp₂')] at h_src
  clear hp₂'; apply prepend_cdl_prepend_elim [_];
  intro wad; pexen 4
  have hp₃ : [src, wad, wad, src] <<+ s₃.stk := by lpfx
  lstor; cstate s₂; pexen 1
  rcases prefix_of_sload' (of_run_singleton' h₄) hp₃
    with ⟨sbal, hp₄, h_sbal⟩
  lstor; cstate s₃; pexen 3
  have hp₅ : [(sbal <? wad), sbal, wad, wad, src] <<+ s₅.stk := by lpfx
  lstor; cstate s₄
  apply rev_branch_elim' (∃ _, _) hp₅; intro h_eq
  have h_le : wad ≤ sbal := by
    rw [← B256.not_lt]; apply (Ne.ite_eq_right_iff B256.zero_ne_one.symm).mp h_eq
  clear h_eq; pexen 1
  have hp₆ : [sbal, wad, wad, src] <<+ s₆.stk := by lpfx
  lstor; cstate s₅; pexec transferFromUpdateSbal
  have hp₇ : [wad, src] <<+ s₇.stk := by lpfx
  have ⟨h_dec, h_le'⟩ := of_transferFromUpdateSbal h_src h_sbal h_le hp₆ h₇
  clear h_src h_sbal h_le hp₆ h₇
  apply cdl_prepend_elim; intro dst; pexen 2
  have hp₈ : [dst, dst, wad, src] <<+ s₈.stk := by lpfx
  lstor; cstate s₇; pexec checkNonAddress
  rcases of_check_non_address hp₈ asm with ⟨vs_dst, hp₉, h_dst⟩
  lstor; cstate s₈; apply rev_branch_elim' (∃ x, _) hp₉
  intro h_eq; simp [h_eq] at h_dst; clear h_eq; pexen 3
  have hp₁₀ : [wad, dst, dst, wad, src] <<+ s₁₀.stk := by lpfx
  lstor; cstate s₉; pexec incrWbal;
  have hp₁₁ : [dst, wad, src] <<+ s₁₁.stk := by
    revert h₁₁; apply append_sload_cons_elim [_]
    intro dst_bal; intro h₁₁; lpfx
  intro h₁₂
  refine' ⟨wad, src.toAdr, dst.toAdr, h_le', (s₁₀.stor e.cta).rest, h_dec, _⟩
  have h_eq : (s₁₁.stor e.cta).rest = (r.stor e.cta).rest := by
    revert h₁₂; cstate s₁₀; pexec transferFromLog
    have hp₁₂ : [wad, src] <<+ s₁₂.stk := by lpfx
    lstor; apply updateAllowance_inv_stor_rest hp₁₂
  rw [← h_eq]; apply incrAt_of_incrWbal h_dst h₁₁ <| pref_trans ⟨_, rfl⟩ hp₁₀

theorem of_transferTestDst {e : Env} {s s' : Desc} :
  Line.Run e s transferTestDst s' →
  ∃ na_dst dst,
    ([na_dst, dst] <<+ s'.stk) ∧
    (na_dst = 0 ↔ ValidAdr dst) := by
  rename' s => s₀; lexec (arg 0)
  rcases Stack.push_of_cdl h₁ with ⟨dst, h_push⟩; clear h₁
  have hp₁ : [dst] <<+ s₁.stk := pref_of_split h_push
  clear h_push s₀; lexec [dup 0]
  have hp₂ : [dst, dst] <<+ s₂.stk := by lpfx
  clear hp₁ h₂ s₁; intro h;
  rcases of_check_non_address hp₂ h
    with ⟨na_dst, h_pfx, h_iff⟩; clear h hp₂
  refine ⟨_, _, h_pfx, h_iff⟩

theorem of_transferTestLt {e s s'} {dst} (h_stk : [dst] <<+ s.stk) :
    Line.Run e s transferTestLt s' →
    ∃ lt? caller wad,
      ([lt?, caller, s.stor e.cta caller - wad, wad, dst] <<+ s'.stk) ∧
      (lt? = 0 ↔ wad ≤ s.stor e.cta caller) ∧
      ValidAdr caller := by
  rename' s => s₀, h_stk => hp₀; lexec (arg 1)
  rcases Stack.push_of_cdl h₁ with ⟨wad, h_push⟩
  have hp₁ : [wad, dst] <<+ s₁.stk := append_pref h_push hp₀
  lstor; cstate s₀; lexec [_, _]
  have hp₂ : [Adr.toB256 e.cla, Adr.toB256 e.cla, wad, dst] <<+ s₂.stk := by lpfx
  lstor; cstate s₁; lexec [_]
  have hp₃ : [s₂.stor e.cta (Adr.toB256 e.cla), Adr.toB256 e.cla, wad, dst] <<+ s₃.stk :=
    prefix_of_sload (opRun_of_instRun <| of_run_singleton h₃) hp₂
  lstor; cstate s₂; intro h
  have hp' :
    [ if (s₃.stor e.cta (Adr.toB256 e.cla) < wad) then 1 else 0, Adr.toB256 e.cla,
      s₃.stor e.cta (Adr.toB256 e.cla) - wad, wad, dst ] <<+ s'.stk := by lpfx
  lstor;
  refine'
    ⟨ if (s'.stor e.cta (Adr.toB256 e.cla) < wad) then 1 else 0,
      Adr.toB256 e.cla, wad, hp', _, validAdr_toB256 _ ⟩
  rw [Ne.ite_eq_right_iff B256.zero_ne_one.symm, B256.not_lt]

theorem transfer_of_transfer {e : Env} {s : Desc} {r : Result} :
    Func.Run c e s transfer r →
    ∃ x a a', Transfer (s.stor e.cta).rest a x a' (r.stor e.cta).rest := by
  simp only [Transfer, Increase]
  rename' s => s₀; pexec transferTestDst
  rcases of_transferTestDst asm with ⟨dst_invalid, dst, hp₁, h_dst⟩
  lstor; cstate s₀;
  apply rev_branch_elim; intro hp₁'
  simp [(pref_head_unique hp₁ hp₁')] at h_dst
  clear hp₁'; pexec [_]
  have hp₂ : [dst] <<+ s₂.stk := by lpfx
  lstor; cstate s₁; pexec transferTestLt
  rcases of_transferTestLt hp₂ h₃ with ⟨_, caller, wad, hp₃, h_le, h_caller⟩
  lstor; cstate s₂
  apply rev_branch_elim; intro hp₃'
  simp [(pref_head_unique hp₃ hp₃')] at h_le
  clear hp₃' dst_invalid; pexec [_]
  have hp₄ : [caller, s₃.stor e.cta caller - wad, wad, dst] <<+ s₄.stk := by lpfx
  lstor; cstate s₃; pexec [_]
  have hp₅ : [wad, dst] <<+ s₅.stk := by lpfx
  have hs₅ :
    Frel e.cta (Overwrite caller (s₄.stor e.cta caller - wad)) s₄.stor s₅.stor := by
    have h := opRun_of_instRun <| of_run_singleton asm
    apply frel_of_sstore h hp₄
  clear hp₄ h₅; intro h_run'
  refine'
    ⟨wad, caller.toAdr, dst.toAdr, _, (s₅.stor e.cta).rest, _, _ ⟩
  · simp [Storage.rest]; rw [toB256_toAdr h_caller]; exact h_le
  · apply frel_of_frel _ <| frel_to_address h_caller <| (hs₅ e.cta).left rfl
    simp [Storage.rest, toB256_toAdr h_caller]
  · revert h_run'; pexec incrWbal; intro hr
    have h : s₆.stor = r.stor := by apply Func.of_inv _ _ _ hr; prog_inv
    rw [← h]; apply incrAt_of_incrWbal h_dst h₆ hp₅

lemma of_prepApprove {e s s'} :
    Line.Run e s prepApprove s' →
    ∃ vx x y, ([vx, x, y] <<+ s'.stk) ∧ (vx = 0 ↔ ¬ ValidAdr x) := by
  lexen 7;
  have hp₁ : [] <<+ s₁.stk := nil_pref
  cstate s; apply cdl_append_elim; intro wad; lexen 3
  have hp₂ : [0, 64, wad] <<+ s₂.stk := by lpfx
  cstate s₁; apply kec_cons_elim; intro hash; lexen 4
  have hp₃ : [hash, hash, wad] <<+ s₃.stk := by lpfx
  cstate s₂; intro h
  rcases of_check_address hp₃ h with ⟨vx, h_vx, h_iff⟩
  refine ⟨vx, hash, wad, h_vx, h_iff⟩

lemma approve_inv_wbal {e s r} (h_run : Func.Run c e s approve r) :
    (s.stor e.cta).rest = (r.stor e.cta).rest := by
  rcases of_run_prepend (arg 0 ++ checkNonAddress) _ h_run
    with ⟨s0, h_s0, h_run'⟩; clear h_run
  have h_s0_stor : s.stor = s0.stor := by linv
  rw [h_s0_stor]; clear h_s0_stor h_s0 s
  rcases of_run_branch_rev h_run' with ⟨s1, h_pop, h_run⟩; clear h_run'
  have h_s1_stor : s0.stor = s1.stor := h_pop.stor
  rw [h_s1_stor]; clear h_s1_stor h_pop s0
  rcases of_run_prepend prepApprove _ h_run
    with ⟨s2, h_s2, h_run'⟩; clear h_run
  rcases of_prepApprove h_s2
    with ⟨hash_valid, hash, wad, h_s2_stk, h_iff⟩
  have h_s2_stor : s1.stor = s2.stor := by linv
  rw [h_s2_stor]; clear h_s2 h_s2_stor s1
  rcases of_run_branch_rev h_run' with ⟨s3, h_pop, h_run⟩; clear h_run'
  have h_hv_eq_zero : hash_valid = 0 :=
    (pref_head_unique h_s2_stk (pref_of_split h_pop.stk))
  rw [h_hv_eq_zero] at h_s2_stk
  simp [h_hv_eq_zero] at h_iff
  clear h_hv_eq_zero hash_valid
  have h_s3_stk : [hash, wad] <<+ s3.stk :=
    of_append_pref h_pop.stk h_s2_stk
  clear h_s2_stk
  have h_s3_stor : s2.stor = s3.stor := h_pop.stor
  rw [h_s3_stor]; clear h_s3_stor h_pop s2
  rcases of_run_next h_run with ⟨s4, h_sstore, h_run'⟩; clear h_run
  have hh := sstore_inv_stor_rest h_iff (pref_trans (by show_pref) h_s3_stk)
               <| opRun_of_instRun h_sstore
  have h_r_stor : s4.stor = r.stor := by
    apply Func.of_inv _ _ _ h_run'; prog_inv
  rw [← h_r_stor]; apply hh

lemma transferFrom_inv_bal : Func.Inv Desc.bal Result.bal transferFrom := by prog_inv

lemma transfer_inv_bal : Func.Inv Desc.bal Result.bal transfer := by prog_inv

lemma solvent_zero_of_solvent {s : Storage} {v : B256} {b : B256}
    (h : s.Solvent v b) : s.Solvent 0 b := by
  simp [Storage.Solvent, B256.toNat_zero]
  apply Nat.le_trans (Nat.le_add_right _ _) h

lemma storage_solvent_zero_of_state_solvent {s : Desc} {a e}
    (h : s.Solvent a e) : (s.stor a).Solvent 0 (s.bal a) := by
  by_cases h' : e.cta = a <;> simp [Desc.Solvent, h'] at h
  · apply solvent_zero_of_solvent h
  · exact h

lemma result_solvent_of_state_solvent' {e : Env} {s : Desc} {r : Result}
    (h_sv : s.Solvent e.cta e)
    (h_sum : wbsum (s.stor e.cta) = wbsum (r.stor e.cta))
    (h_bal : s.bal e.cta = r.bal e.cta) : r.Solvent e.cta := by
  apply @solvent_zero_of_solvent _ e.clv
  simp [Desc.Solvent, Storage.Solvent] at *
  rw [← h_sum, ← h_bal]; exact h_sv

lemma result_solvent_of_state_solvent {e : Env} {s : Desc} {r : Result} :
    (s.stor e.cta).rest = (r.stor e.cta).rest →
      s.bal e.cta = r.bal e.cta →
      s.Solvent e.cta e → r.Solvent e.cta := by
  simp [Desc.Solvent, Result.Solvent]
  intros h_wbsum h_bal h_solvent
  apply @solvent_zero_of_solvent _ e.clv
  simp [Storage.Solvent, wbsum]
  rw [← h_wbsum, ← h_bal]; exact h_solvent

lemma approve_inv_bal : Func.Inv Desc.bal Result.bal approve := by prog_inv

theorem approve_inv_solvent {e s r} (h : Func.Run c e s approve r)
    (h' : s.Solvent e.cta e) : r.Solvent e.cta := by
  apply result_solvent_of_state_solvent (approve_inv_wbal h) _ h'
  rw [approve_inv_bal h]

lemma nof_of_solvent {s a e} (h : Desc.Solvent s a e) : SumNof (s.stor a).rest := by
  apply lt_of_le_of_lt _ (B256.toNat_lt <| s.bal a)
  simp [Desc.Solvent, Storage.Solvent] at h
  by_cases h' : e.cta = a
  · apply le_trans (Nat.le_add_right _ _) (h.left h')
  · apply le_trans (Nat.le_add_right _ _) (h.right h')

theorem transfer_inv_solvent' {e s r} :
    Func.Run c e s transfer r → s.Solvent e.cta e → r.Solvent e.cta := by
  intros h_run h_solvent
  rcases transfer_of_transfer h_run with ⟨x, a, a', h_di⟩
  apply
    result_solvent_of_state_solvent'
      h_solvent
      (transfer_inv_sum (nof_of_solvent h_solvent) h_di)
      (congr_fun (transfer_inv_bal h_run) _)

theorem transferFrom_inv_solvent {e s r}
    (h : Func.Run c e s transferFrom r) (h' : s.Solvent e.cta e) : r.Solvent e.cta := by
  rcases transfer_of_transferFrom h with ⟨x, a, a', h_di⟩
  apply @result_solvent_of_state_solvent' e s r h'
  · apply transfer_inv_sum (nof_of_solvent h') h_di
  · rw [transferFrom_inv_bal h]

syntax "simple_solvent" : tactic
macro_rules
| `(tactic| simple_solvent) =>
  `(tactic| simp [Desc.Solvent]; intro h h';
            apply solvent_zero_of_solvent <| solvent_of_same_stor h' _ _ <;>
            apply congr_fun <| Func.of_inv _ _ (by prog_inv) h )

theorem symbol_inv_solvent {e s r} :
    Func.Run c e s symbol r → s.Solvent e.cta e → r.Solvent e.cta := by simple_solvent

theorem name_inv_solvent {e s r} :
    Func.Run c e s name r → s.Solvent e.cta e → r.Solvent e.cta := by simple_solvent

theorem balanceOf_inv_solvent {e s r} :
  Func.Run c e s balanceOf r → s.Solvent e.cta e → r.Solvent e.cta := by simple_solvent

theorem allowance_inv_solvent {e s r} :
  Func.Run c e s allowance r → s.Solvent e.cta e → r.Solvent e.cta := by simple_solvent

theorem decimals_inv_solvent {e s r} :
  Func.Run c e s decimals r → s.Solvent e.cta e → r.Solvent e.cta := by simple_solvent

theorem totalSupply_inv_solvent {e s r} :
  Func.Run c e s totalSupply r → s.Solvent e.cta e → r.Solvent e.cta := by simple_solvent

theorem wbsum_after_deposit {e : Env} {s : Desc} {r}
    (h_nof : (wbsum (s.stor e.cta)) + e.clv.toNat < 2 ^ 256) :
    Func.Run c e s deposit r →
    wbsum (s.stor e.cta) + e.clv.toNat = wbsum (r.stor e.cta) := by
  have hp0 : [] <<+ s.stk := nil_pref; pexen 1
  have hp₁ : [Adr.toB256 e.cla] <<+ s₁.stk := by lpfx
  lstor; cstate s; pexen 1
  rcases prefix_of_sload' (of_run_singleton' h₂) hp₁ with ⟨cbal, h_stk, h_cbal⟩
  lstor; cstate s₁; pexen 3
  have hp₃ : [Adr.toB256 e.cla, e.clv + cbal] <<+ s₃.stk := by lpfx
  lstor; cstate s₂; pexen 1; intro h₅
  have h_stor : s₄.stor = r.stor := by apply Func.of_inv _ _ _ h₅; prog_inv
  rw [← h_stor]; clear h_stor h₅
  have h_incr : Increase e.cla e.clv (s₃.stor e.cta).rest (s₄.stor e.cta).rest := by
    have h := (frel_of_sstore (of_run_singleton' h₄) hp₃ e.cta).left rfl
    intro x; constructor <;> intro hx
    · simp [Storage.rest]; rw [← hx, ← h_cbal, B256.add_comm]
      exact (h (Adr.toB256 e.cla)).left rfl
    · apply (h (Adr.toB256 x)).right <| mt (@Adr.toB256_inj e.cla x) hx
  have h_nof' : B256.Nof (Storage.rest (s₃.stor e.cta) e.cla) e.clv := by
    simp only [B256.Nof ]; apply lt_of_le_of_lt _ h_nof
    rw [Nat.add_le_add_iff_right]; apply le_sum
  exact sum_add_assoc h_incr h_nof'

lemma solvent_zero_iff {s b} : Storage.Solvent s 0 b ↔ wbsum s ≤ b.toNat := by
  simp [Storage.Solvent, wbsum, B256.toNat_zero]

theorem deposit_inv_solvent {e s r} :
    Func.Run c e s deposit r → s.Solvent e.cta e → r.Solvent e.cta := by
  intros h_run h_solvent
  simp [Result.Solvent]
  have h_bal : s.bal = r.bal := by
    apply Func.of_inv _ _ _ h_run; prog_inv
  rw [solvent_zero_iff, ← h_bal]
  simp [Desc.Solvent, Storage.Solvent] at h_solvent
  have h_lt : wbsum (s.stor e.cta) + B256.toNat e.clv < 2 ^ 256 :=
    lt_of_le_of_lt h_solvent (B256.toNat_lt _)
  rw [← wbsum_after_deposit h_lt h_run]
  apply h_solvent

lemma of_withdrawLoadCheck {e : Env} {s s'} (h : Line.Run e s withdrawLoadCheck s') :
    s.bal = s'.bal ∧
    s.stor = s'.stor ∧
    s.code = s'.code ∧
    ∃ wad cbal,
      ([cbal <? wad, cbal, wad, wad] <<+ s'.stk) ∧
      (cbal = s'.stor e.cta (Adr.toB256 e.cla)) := by
  refine' ⟨_, _, _, _⟩ <;> try {linv}; revert h
  apply cdl_append_elim (∃ _, _); intro wad; lexen 3
  have hs₀ : [] <<+ s.stk := nil_pref
  have hs₁ : [Adr.toB256 e.cla, wad, wad] <<+ s₁.stk := by lpfx
  cstate s; lexen 1
  rcases prefix_of_sload' (of_run_singleton' h₂) hs₁ with ⟨cbal, hs₂, h_cbal⟩
  lstor; cstate s₁; intro h₃
  have hs₃ : [cbal <? wad, cbal, wad, wad] <<+ s'.stk := by lpfx
  lstor; refine ⟨wad, cbal, hs₃, h_cbal⟩

lemma precond_of_precond {a e} {s s' : Desc}
    (h : Precond a e s) (h_bal : s.bal = s'.bal)
    (h_stor : s.stor = s'.stor) (h_code : s.code = s'.code) :
    Precond a e s' := by
  refine' ⟨_, _, _⟩
  · rw [← h_code]; apply h.code
  · rw [← h_bal]; apply h.nof
  · simp [Desc.Solvent]; rw [← h_stor, ← h_bal]; apply h.solvent

lemma solvent_of_callPrep {e s ep sp r sw send_gas send_amnt}
    (cr : Xinst.Run' e s ep sp .call r sw)
    (h_stk : [send_gas, (Adr.toB256 e.cla), send_amnt] <<+ s.stk)
    (h_sv : Storage.Solvent (s.stor e.cta) 0 (s.bal e.cta - send_amnt)) :
    sp.Solvent e.cta ep := by
  have h_clv : ep.clv = send_amnt := by
    cases cr; rcases (asm : Stack.Diff _ _ _ _) with ⟨_, h_pop, _⟩
    have h0 : Stack.Nth 2 send_amnt s.stk := by
      apply Stack.nth_of_prefix _ h_stk; show_nth
    have h1 : Stack.Nth 2 _ s.stk :=
      Stack.nth_of_prefix (by show_nth) (pref_of_split h_pop)
    simp [Env.prep, Stack.nth_unique h1 h0]
  have h_di : Transfer s.bal e.cta send_amnt ep.cta sp.bal := by
    cases cr; rw [← h_clv]; assumption
  rcases h_di with ⟨h_le, s', hd, hi⟩
  constructor <;> (intro h_cta; rw [← Xinst.prep_inv_stor cr])
  · conv => arg 3; tactic => apply ((hi e.cta).left h_cta).symm
    simp [Storage.Solvent, B256.toNat_zero] at h_sv
    rw [B256.toNat_sub_eq_of_le _ _ h_le] at h_sv
    rw [← (hd e.cta).left rfl]
    simp [Storage.Solvent, B256.sub_add_cancel]
    rw [← Nat.sub_add_cancel (B256.toNat_le_toNat h_le), h_clv]
    apply Nat.add_le_add_right h_sv send_amnt.toNat
  · rw [← (hi e.cta).right h_cta, ← (hd e.cta).left rfl]; exact h_sv

def Exec.InvDepth (k : Nat) (ca : Adr) (p : Prog)
    (σ : Env → Desc → Prop) (ρ : Env → Result → Prop) : Prop :=
  ForallDeeperAt k ca p (λ e s _ r _ => σ e s → ρ e r)

lemma of_send_to_caller' {e : Env} {s sf} {wad}
    (ih : Exec.InvDepth e.exd e.cta weth (Precond e.cta) (Postcond e.cta))
    (hp : [wad] <<+ s.stk)
    (h_code : some (s.code e.cta) = Prog.compile weth)
    (h_nof : SumNof s.bal)
    (h_le : wad ≤ s.bal e.cta)
    (h_sv : Storage.Solvent (s.stor e.cta) 0 (s.bal e.cta - wad)) :
    Line.Run e s sendToCaller sf →
    Storage.Solvent (sf.stor e.cta) 0 (sf.bal e.cta) := by
  have h_nof' : wbsum (s.stor e.cta) + wad.toNat < 2 ^ 256 := by
    simp [Storage.Solvent, B256.toNat_zero] at h_sv
    rw [B256.toNat_sub_eq_of_le _ _ h_le] at h_sv
    apply lt_of_le_of_lt <| Nat.add_le_add_right h_sv wad.toNat
    rw [Nat.sub_add_cancel <| B256.toNat_le_toNat  h_le]
    apply B256.toNat_lt
  lexen 7
  have hs₁ :
      [B8L.toB256 [0x52, 0x08], e.cla.toB256, wad, 0, 0, 0, 0] <<+ s₁.stk :=
    by lpfx
  have hc₁ : s.code = s₁.code := by apply Line.of_inv _ _ asm; line_inv
  rw [hc₁] at h_code; clear hc₁
  have hb₁ : s.bal = s₁.bal := by linv
  rw [hb₁] at h_nof h_sv h_le; clear hb₁
  lstor; cstate s; lexen 1; intro h₃; cases h₃
  rcases of_run_call <| of_run_singleton h₂ with ⟨ep, sp, r, h_rm, h_run⟩ | hf
  · have h_exd := Xinst.exd_lt_of_run' h_rm
    have h_weth' : some (sp.code e.cta) = Prog.compile weth := by
      rw [← Xinst.prep_inv_code h_rm, h_code]
    have h_teth' : SumNof sp.bal := Xinst.prep_inv_nof h_rm h_nof
    have h_sv : Desc.Solvent sp e.cta ep := by
      have hs : [ B8L.toB256 [0x52, 0x08], Adr.toB256 e.cla, wad] <<+ s₁.stk := by
        apply pref_trans _ hs₁; show_pref
      apply solvent_of_callPrep h_rm hs h_sv
    have h_pc : Precond e.cta ep sp := by refine' ⟨h_weth', h_teth', h_sv⟩
    simp [Storage.Solvent]
    rw [← Xinst.wrap_inv_stor h_rm, ← Xinst.wrap_inv_bal h_rm]
    rcases h_run with ⟨cr, ⟨_⟩⟩ | hf
    · apply (ih ep sp 0 r asm h_exd ⟨h_weth', _⟩ h_pc).solvent
      intro h_eq; rw [ctc_eq_of_call h_rm, h_eq, h_code]; simp
    · have h_bal : r.bal = sp.bal := Eq.symm (PreRun.bal asm)
      have h_stor : r.stor = sp.stor := Eq.symm (PreRun.stor asm)
      rw [h_bal, h_stor]
      by_cases h_cta : ep.cta = e.cta
      · apply solvent_zero_of_solvent (h_sv.left h_cta)
      · apply h_sv.right h_cta
  · rw [← fail_inv_bal hf, ← fail_inv_stor hf]; apply le_trans h_sv
    rw [B256.toNat_sub_eq_of_le _ _ h_le]; apply Nat.sub_le

lemma solvent_of_withdraw_update_bal' {e : Env} {s s'} {lt? cbal wad}
    (h_pc : Precond e.cta e s)
    (h_stk : [lt?, cbal, wad, wad] <<+ s.stk)
    (h_cbal : cbal = s.stor e.cta (Adr.toB256 e.cla))
    (h_le : wad ≤ cbal)
    (h_run : Line.Run e s [pop, sub, caller, sstore] s') :
    wad ≤ s'.bal e.cta ∧
    Storage.Solvent (s'.stor e.cta) 0 (s'.bal e.cta - wad) := by
  revert h_run; lexen 3
  have h_pc' : Precond e.cta e s₁ := by
    apply precond_of_precond h_pc <;> (apply Line.of_inv _ _ h₁; line_inv)
  have hp₁ : [Adr.toB256 e.cla, cbal - wad, wad] <<+ s₁.stk := by lpfx
  lstor; cstate s; intro h₂
  have h_dec : Decrease e.cla wad (s₁.stor e.cta).rest (s'.stor e.cta).rest := by
    have h := (frel_of_sstore (of_run_singleton' h₂) hp₁ e.cta).left rfl
    intro a; constructor <;> (intro ha; simp [Storage.rest])
    · rw [← ha, ← h_cbal]; apply (h (Adr.toB256 e.cla)).left rfl
    · apply (h (Adr.toB256 a)).right <| mt Adr.toB256_inj ha
  have h_eq : wbsum (s₁.stor e.cta) - wad.toNat = wbsum (s'.stor e.cta) := by
    apply sum_sub_assoc h_dec
    simp [Storage.rest]; rw [← h_cbal]; exact h_le
  clear h_dec
  have h_le' : wad.toNat ≤ wbsum (s₁.stor e.cta) := by
    apply Nat.le_trans (B256.toNat_le_toNat  h_le); rw [h_cbal]
    apply @le_sum (s₁.stor e.cta).rest
  have h_bal : s₁.bal = s'.bal := by apply Line.of_inv _ _ h₂; line_inv
  rw [← h_bal]
  have h_le'' : wad.toNat ≤ (s₁.bal e.cta).toNat := by
    apply le_trans h_le' <| le_trans _ <| h_pc'.solvent.left rfl
    apply Nat.le_add_right
  have h_le''' := B256.le_of_toNat_le_toNat h_le''
  refine' ⟨h_le''', _⟩
  · simp [Storage.Solvent, B256.toNat_zero]
    rw [B256.toNat_sub_eq_of_le _ _ h_le''', ← h_eq, Nat.sub_le_sub_iff_right h_le'']
    have h' := solvent_zero_of_solvent <| (Precond.solvent asm).left rfl
    simp [Storage.Solvent, B256.toNat_zero] at h'; exact h'

theorem withdraw_inv_solvent {e : Env} {s r} (h_pc : Precond e.cta e s)
    (ih : Exec.InvDepth e.exd e.cta weth (Precond e.cta) (Postcond e.cta)) :
    Func.Run c e s withdraw r → r.Solvent e.cta := by
  pexec withdrawLoadCheck
  rcases of_withdrawLoadCheck asm
    with ⟨h_bal, h_stor, h_code, wad, cbal, hp₁, h_cbal⟩
  have h_pc' := precond_of_precond h_pc h_bal h_stor h_code
  cstate s; rename' h_pc' => h_pc
  apply rev_branch_elim' (Result.Solvent _ _) hp₁
  intro h_eq
  have h_wad : wad ≤ cbal := by
    rw [← B256.not_lt];
    apply (Ne.ite_eq_right_iff <| Ne.symm B256.zero_ne_one).mp h_eq
  clear h_eq; pexen 4
  rcases solvent_of_withdraw_update_bal' h_pc hp₁ h_cbal h_wad h₂ with ⟨h_le, h_sv⟩
  clear h_cbal h_wad
  have h_code : some (s₂.code e.cta) = Prog.compile weth := by
    rw [← Line.of_inv Desc.code (by line_inv) h₂]; apply h_pc.code
  have h_nof : sum s₂.bal < 2 ^ 256 := by
    rw [← Line.of_inv Desc.bal (by line_inv) h₂]; apply h_pc.nof
  have hp₂ : [wad] <<+ s₂.stk := by lpfx
  cstate s₁; pexec sendToCaller; intro h₄
  unfold Result.Solvent
  rw [← Func.of_inv Desc.stor Result.stor (by prog_inv) h₄]
  rw [← Func.of_inv Desc.bal Result.bal (by prog_inv) h₄]
  apply of_send_to_caller' ih hp₂ h_code h_nof h_le h_sv h₃

lemma Line.inv_solvent {e e' s l s' a}
    (h_bal : Line.Inv Desc.bal l) (h_stor : Line.Inv Desc.stor l)
    (h_sv : Desc.Solvent s a e) (h_run : Line.Run e' s l s') : Desc.Solvent s' a e := by
  unfold Desc.Solvent; rw [← h_bal h_run, ← h_stor h_run]; exact h_sv

lemma run_inv_cond (f : Func)
    (h : ∀ {e : Env} {s : Desc} {r : Result}, Func.Run c e s f r →
       Desc.Solvent s e.cta e → Result.Solvent r e.cta) :
    ∀ {e : Env} {s : Desc} {r : Result}, Func.Run c e s f r →
      Precond e.cta e s → Postcond e.cta e r := by
  intro e s r h_run h_pc
  refine' ⟨_, Func.inv_nof h_run h_pc.nof, h h_run h_pc.solvent⟩
  have hcode : s.code e.cta ≠ [] := by
    intro h; apply @Prog.compile_ne_nil weth; rw [← h_pc.code, h]
  rw [← Func.inv_code h_run hcode]; exact h_pc.code

lemma weth_inv' {e s r}
    (hs : Precond e.cta e s)
    (ih : Exec.InvDepth e.exd e.cta weth (Precond e.cta) (Postcond e.cta)) :
    Func.Run (weth.main :: weth.aux) e s weth.main r →
    Postcond e.cta e r := by
  pexec fsig
  have hs₁ : Precond e.cta e s₁ := by
    refine' ⟨_, _, _⟩
    · rw [← Line.of_inv Desc.code (by line_inv) h₁, hs.code]
    · rw [← Line.of_inv Desc.bal (by line_inv) h₁]; exact hs.nof
    · apply Line.inv_solvent _ _ hs.solvent h₁ <;> line_inv
  clear hs
  apply
    @dispatchWith_inv
      (weth.main :: weth.aux) 1 deposit
      (λ e s => Precond e.cta e s ∧
                Exec.InvDepth e.exd e.cta weth (Precond e.cta) (Postcond e.cta) )
      (λ e r => Postcond e.cta e r)
      _ _ rfl _ wethTree _ e s₁ r ⟨hs₁, ih⟩ <;>
    (clear h₁ hs₁ ih e s r s₁; simp)
  · intro e s x s' h_pc h_inv h_run;
    refine' ⟨⟨_, _, _⟩, h_inv⟩
    · rw [← Line.of_inv Desc.code (by line_inv) h_run]; apply h_pc.code
    · rw [← Line.of_inv Desc.bal (by line_inv) h_run]; apply h_pc.nof
    · apply Line.inv_solvent _ _ h_pc.solvent h_run <;> line_inv
  · intro e s x s' h_pc h_inv h_run;
    refine' ⟨⟨_, _, _⟩, h_inv⟩
    · rw [← Line.of_inv Desc.code (by line_inv) h_run]; apply h_pc.code
    · rw [← Line.of_inv Desc.bal (by line_inv) h_run]; apply h_pc.nof
    · apply Line.inv_solvent _ _ h_pc.solvent h_run <;> line_inv
  · intro e s r h_pc _ h_run
    apply run_inv_cond _ deposit_inv_solvent h_run h_pc
  · intro e s r w p h_mem h_pc h_inv h_run
    rcases h_mem with (((h | h) | h) | (h | h)) | (((h | h) | h) | (h | h)) <;>
      (cases h)
    · apply run_inv_cond _ name_inv_solvent h_run h_pc
    · apply run_inv_cond _ approve_inv_solvent h_run h_pc
    · apply run_inv_cond _ totalSupply_inv_solvent h_run h_pc
    · apply run_inv_cond _ transferFrom_inv_solvent h_run h_pc
    · refine' ⟨_, Func.inv_nof h_run h_pc.nof, withdraw_inv_solvent h_pc h_inv h_run⟩
      have hcode : s.code e.cta ≠ [] := by
        intro h; apply @Prog.compile_ne_nil weth; rw [← h_pc.code, h]
      rw [← Func.inv_code h_run hcode]; exact h_pc.code
    · apply run_inv_cond _ decimals_inv_solvent h_run h_pc
    · apply run_inv_cond _ balanceOf_inv_solvent h_run h_pc
    · apply run_inv_cond _ symbol_inv_solvent h_run h_pc
    · apply run_inv_cond _ transfer_inv_solvent' h_run h_pc
    · apply run_inv_cond _ allowance_inv_solvent h_run h_pc

lemma Xinst.wrap_inv_solvent {e s ep sp o r sw wa}
    (h : Xinst.Run' e s ep sp o r sw)
    (h_ne : e.cta ≠ wa) (h_sv : r.Solvent wa) : sw.Solvent wa e := by
  simp [h_ne, Desc.Solvent];
  cases h <;> {simp [Desc.wrap, Desc.wrap']; apply h_sv}

theorem weth_inv_solvent (wa : Adr) :
    ∀ e s r,
      Exec e s 0 r →
      some (s.code wa) = Prog.compile weth →
      (e.cta = wa → some e.code = Prog.compile weth) →
      Precond wa e s → Postcond wa e r := by
  intro e s r ex h h'
  apply
    lift_inv wa weth (Precond wa) (Postcond wa) _ _ _ _
      e s 0 r ex ⟨h, λ h_eq => ⟨h' h_eq, rfl⟩⟩ <;> clear e s r ex h h'
  · intro e s r h_run h_eq; rw [← h_eq]
    intro h_inv h_pc;
    dsimp [Prog.Run] at h_run
    apply weth_inv' h_pc h_inv h_run
  · intros e s pc s' pc' h_step h_ne h_pc; constructor
    · rw [← Step.inv_code h_step, h_pc.code]
    · have h_nof := h_pc.nof; clear h_pc
      cases h_step with
      | reg => rw [← Rinst.inv_bal asm]; exact h_nof
      | pre =>
        apply Xinst.wrap_inv_nof asm
        have h := PreRun.bal asm; rw [← h]
        apply Xinst.prep_inv_nof asm h_nof
      | fail => rw [← fail_inv_bal asm]; exact h_nof
      | jump => rw [← Jinst.inv_bal asm]; exact h_nof
      | push =>
        have h := Desc.Rel.bal asm
        rw [← h]; exact h_nof
    · have h_sv := h_pc.solvent
      have h_nof := h_pc.nof
      cases h_step with
      | reg => exact Rinst.inv_solvent asm h_ne h_sv
      | pre =>
        apply Xinst.wrap_inv_solvent asm h_ne
        unfold Result.Solvent
        have h := PreRun.stor asm
        have h' := PreRun.bal asm
        rw [← h, ← h']
        apply
          storage_solvent_zero_of_state_solvent
            <| Xinst.prep_inv_solvent asm asm h_ne h_nof h_sv
      | fail =>
        simp at *; unfold Desc.Solvent
        rw [← fail_inv_bal asm, ← fail_inv_stor asm]; exact h_sv
      | jump =>
        have h := Jinst.inv_stor asm
        have h' := Jinst.inv_bal asm
        unfold Desc.Solvent; rw [← h, ← h']; exact h_sv
      | push =>
        have h := Desc.Rel.bal asm
        have h' := Desc.Rel.stor asm
        unfold Desc.Solvent; rw [← h, ← h']; exact h_sv
  · intros e s ep sp o rx sw h_cr ha h_pc; constructor
    · constructor
      · rw [← Xinst.prep_inv_code h_cr, h_pc.code]
      · apply Xinst.prep_inv_nof h_cr h_pc.nof
      · by_cases ho : o.isCall
        · apply Xinst.prep_inv_solvent ho h_cr ha h_pc.nof h_pc.solvent
        · have ha' : ep.cta ≠ wa := by
            intro hc; apply @Prog.compile_ne_nil weth
            rw [← h_pc.code, ← hc, Xinst.code_eq_nil_of_run' asm ho]
          apply Xinst.prep_inv_solvent' asm h_cr ha ha' h_pc.solvent
    · intro h_pc'; constructor
      by_cases ho : o.isCall
      · rw [← Xinst.wrap_inv_code asm ho, h_pc'.code]
      · have ha' : ep.cta ≠ wa := by
          intro hc; apply @Prog.compile_ne_nil weth
          rw [← h_pc.code, ← hc, Xinst.code_eq_nil_of_run' asm ho]
        rw [← Xinst.wrap_inv_code' asm asm, h_pc'.code]
      · exact Xinst.wrap_inv_nof asm h_pc'.nof
      · exact Xinst.wrap_inv_solvent asm ha h_pc'.solvent
  · intros e s pc r h h_ne h_pc; cases h
    · constructor
      · rw [← Linst.inv_code asm]; apply h_pc.code
      · exact Linst.inv_nof asm h_pc.nof
      · have h_sv : Storage.Solvent (s.stor wa) 0 (s.bal wa) := by
          have h := h_pc.solvent; simp [Desc.Solvent, h_ne] at h; exact h
        have h_le : (s.bal wa).toNat ≤ (r.bal wa).toNat := by
          rename Linst.Run _ _ _ _ => h_run
          cases (asm : Linst) with
          | stop => cases h_run; apply Nat.le_refl
          | ret => cases h_run; apply Nat.le_refl
          | rev => cases h_run
          | dest =>
            rcases of_run_dest h_run with ⟨a, _, bal, hd, hi⟩
            by_cases ha : a = wa
            · have h_rw : r.bal wa = s.bal wa + s.bal e.cta := by
                rw [(hd wa).right h_ne]; apply ((hi wa).left ha).symm
              have hle : B256.Nof (s.bal wa) (s.bal e.cta) :=
                lt_of_le_of_lt (add_le_sum_of_ne s.bal h_ne.symm) h_pc.nof
              rw [h_rw, B256.toNat_add_eq_of_nof _ _ hle]; apply Nat.le_add_right
            · rw [(hd wa).right h_ne, (hi wa).right ha]
          -- | invalid => cases h_run
        unfold Result.Solvent; rw [← Linst.inv_stor asm]
        apply le_trans h_sv h_le
    · refine' ⟨h_pc.code, h_pc.nof, _⟩
      have h := h_pc.solvent
      simp [Desc.Solvent, h_ne] at h
      apply h

lemma transact_inv_solvent {ST RT w r wa}
    (h : MessageCall ST RT w r) (h_wa : ST ≠ wa)
    (h_nof : SumNof w.bal) (h_wb : w.Solvent wa)
    (h_code : some (w.code wa) = Prog.compile weth) : r.Solvent wa := by
  cases h with
  | create gpr clv ctc bal r cd h_di h_nil cr =>
    have h_ne : RT ≠ wa := by
      intro hc; apply @Prog.compile_ne_nil weth
      rw [← h_code, ← hc, h_nil]
    have h_eq : w.bal wa = bal wa := by
      rcases h_di with ⟨_, bal', hd, hi⟩
      apply Eq.trans ((hd wa).right h_wa) ((hi wa).right h_ne)
    apply (@weth_inv_solvent wa _ _ _ cr h_code _ _).solvent
    · intro hc; cases h_ne hc
    · refine' ⟨h_code, _, _, _⟩
      · simp only [Desc.init]
        rw [← transfer_inv_sum h_nof h_di]
        exact h_nof
      · simp only []
        intro hc; cases h_ne hc
      · intro h; clear h; simp only [Desc.init]
        rw [← h_eq]; apply h_wb
  | call gpr cld clv bal _ h_di cr =>
    apply (@weth_inv_solvent wa _ _ _ cr h_code _ _).solvent
    · simp; intro h_eq; rw [h_eq]; apply h_code
    · refine' ⟨h_code, _, _, _⟩
      · simp only [Desc.init]
        rw [← transfer_inv_sum h_nof h_di]
        exact h_nof
      · simp only []; intro h_eq
        have h_eq : w.bal wa + clv = bal wa := by
          rcases h_di with ⟨_, bal', hd, hi⟩
          rw [(hd wa).right h_wa, ← (hi wa).left h_eq]
        have h_nof : B256.Nof (w.bal wa) clv := by
          apply lt_of_le_of_lt _ <| h_nof
          apply le_trans _ <| add_le_sum_of_ne w.bal h_wa
          rw [Nat.add_comm, Nat.add_le_add_iff_right]
          apply B256.toNat_le_toNat
          rcases h_di with ⟨h_le, _⟩; exact h_le
        simp only [Desc.init]; rw [← h_eq]; simp [Storage.Solvent]
        rw [B256.toNat_add_eq_of_nof _ _ h_nof, Nat.add_le_add_iff_right]
        simp [World.Solvent, Storage.Solvent, B256.toNat_zero] at h_wb
        apply h_wb
      · simp only []; intro h_ne
        have h_eq : w.bal wa = bal wa := by
          rcases h_di with ⟨_, bal', hd, hi⟩
          apply Eq.trans ((hd wa).right h_wa) ((hi wa).right h_ne)
        simp only [Desc.init]; rw [← h_eq]; apply h_wb
  | pre clv bal ret h_di =>
    apply le_trans h_wb
    rcases of_nof_of_transfer h_nof h_di with ⟨bal', hd, hi, h_nof'⟩
    rw [(hd wa).right h_wa]
    apply B256.toNat_le_toNat  <| le_of_increase hi h_nof' _
  | fail => apply h_wb

theorem transact_inv_sum_bal {sda rca w r} (h : MessageCall sda rca w r)
    (h' : SumNof w.bal) : sum w.bal = sum r.bal := by
  cases h with
  | create =>
    rename Exec _ _ _ _ => cr
    rw [transfer_inv_sum h' asm]
    apply Exec.inv_sum_bal cr
    apply transfer_inv_nof asm h'
  | call =>
    rename Exec _ _ _ _ => cr
    rw [transfer_inv_sum h' asm]
    apply Exec.inv_sum_bal cr
    apply transfer_inv_nof asm h'
  | pre => rw [transfer_inv_sum h' asm]
  | fail => rfl

theorem transaction_inv_solvent
    (wa : Adr) (w w' : World)
    (h_code : some (w.code wa) = weth.compile)
    (h_solv : w.Solvent wa)
    (h_bal : SumNof w.bal)
    (tx : Transaction w w') :
    w'.Solvent wa := by
  have h_ne : tx.sda ≠ wa := by
    intro h; rw [← h, tx.eoa] at h_code
    cases Prog.compile_ne_nil h_code.symm
  have h_nof_bal :
    sum tx.bal + tx.vs.toNat + tx.vv.toNat + tx.vb.toNat < 2 ^ 256 := by
    have h_nof' : B256.Nof tx.vs tx.vv :=
      lt_of_le_of_lt (Nat.le_add_right _ _) tx.nof
    have h_nof'' :B256.Nof (tx.vs + tx.vv) tx.vb := by
      simp only [B256.Nof]; rw [B256.toNat_add_eq_of_nof _ _ h_nof']; apply tx.nof
    have h_eq :
      (tx.vs + tx.vv + tx.vb).toNat =
        tx.vs.toNat + tx.vv.toNat + tx.vb.toNat := by
      rw [B256.toNat_add_eq_of_nof _ _ h_nof'', B256.toNat_add_eq_of_nof _ _ h_nof']
    have h_eq' :
      sum tx.bal + tx.vs.toNat + tx.vv.toNat + tx.vb.toNat = sum w.bal := by
      rw [Nat.add_assoc (sum _), Nat.add_assoc, ← h_eq]
      have h_le : B256.toNat (tx.vs + tx.vv + tx.vb) ≤ sum w.bal := by
        apply le_trans <| B256.toNat_le_toNat  <| tx.le
        apply le_sum
      rw [← sum_sub_assoc tx.decr tx.le, Nat.sub_add_cancel h_le]
    rw [h_eq']; apply h_bal
  have h_nof : SumNof tx.bal := by
    apply lt_of_le_of_lt (le_trans _ <| Nat.le_add_right _ _) h_nof_bal
    apply le_trans (Nat.le_add_right _ _) <| Nat.le_add_right _ _
  have h_sv : Storage.Solvent (w.stor wa) 0 (tx.bal wa) := by
    rw [← (tx.decr wa).right h_ne]; apply h_solv
  have hq := transact_inv_solvent tx.act h_ne h_nof h_sv h_code
  have h_nof' : B256.Nof (tx.r.bal tx.sda) tx.vs := by
    apply lt_of_le_of_lt _ h_nof_bal
    apply le_trans _ <| Nat.le_add_right _ _
    apply le_trans _ <| Nat.le_add_right _ _
    apply Nat.add_le_add_right _ _
    rw [transact_inv_sum_bal tx.act h_nof]
    apply le_sum
  simp [Result.Solvent] at hq
  simp [World.Solvent]
  rw [tx.stor]
  apply le_trans hq
  rw [(tx.incr wa).right h_ne]
  apply B256.toNat_le_toNat
  have h_nof'' : B256.Nof (tx.bal' tx.vla) tx.vv := by
    simp only [B256.Nof]
    rw [ transact_inv_sum_bal tx.act h_nof,
         sum_add_assoc tx.incr h_nof' ] at h_nof_bal
    apply lt_of_le_of_lt _ h_nof_bal
    apply le_trans _ <| Nat.le_add_right _ _
    apply Nat.add_le_add_right _ _
    apply le_sum
  apply le_of_increase tx.incr' h_nof''


#exit
def State.codes (s : State) : Codes :=
  ByteArray.toList ∘ s.getCode

def State.stor (s : State) : Storages :=
  λ a k => (s.getStor a).getD k 0

def State.toWorld (s : State) : World :=
  { code := ByteArray.toList ∘ s.getCode,
    stor := λ a k => (s.getStor a).getD k 0,
    bal  := s.bal }

def BlockChain.toWorld (c : BlockChain) : World :=
  c.state.toWorld
  --{ code := ByteArray.toList ∘ c.state.getCode
  --  stor := λ a k => (c.state.getStor a).getD k 0,
  --  bal  := c.state.bal }

def State.Solvent (s : State) (wa : Adr) : Prop :=
  Storage.Solvent (s.stor wa) 0 (s.bal wa)

def BlockChain.Solvent (c : BlockChain) (wa : Adr) : Prop :=
  c.state.Solvent wa

lemma ByteArray.toList.loop_eq
    {bs : ByteArray} {i : Nat} (r : List UInt8) :
    ByteArray.toList.loop bs i r =
    if i < bs.size then
      ByteArray.toList.loop bs (i + 1) (bs.get! i :: r)
    else
      r.reverse := by
  conv => lhs; unfold ByteArray.toList.loop

lemma ByteArray.toList.loop_eq_of_lt
    {bs : ByteArray} {i : Nat} (h : i < bs.size) (r : List UInt8) :
    ByteArray.toList.loop bs i r
      = ByteArray.toList.loop bs (i + 1) (bs.get! i :: r) := by
  apply Eq.trans (ByteArray.toList.loop_eq r); rw [if_pos h]

lemma ByteArray.toList.loop_eq_of_ge
    {bs : ByteArray} {i : Nat} (h : i ≥ bs.size) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse := by
  apply Eq.trans (ByteArray.toList.loop_eq r)
  rw [if_neg]; rw [Nat.not_lt]; apply h


lemma ByteArray.toList.loop_eq_append (m) :
    ∀ n (xs ys : B8L),
      m = (⟨⟨xs⟩⟩ : ByteArray).size - n →
      ByteArray.toList.loop ⟨⟨xs⟩⟩ n ys = ys.reverse ++ xs.drop n := by
  induction m with
    | zero =>
      intro n xs ys h
      rw [Eq.comm, Nat.sub_eq_zero_iff_le] at h
      rw [ByteArray.toList.loop_eq_of_ge h]
      simp [List.drop_eq_nil_of_le h]
    | succ m ih =>
      intro n xs ys h
      have lt := Nat.lt_of_sub_eq_succ h.symm
      rw [ByteArray.toList.loop_eq_of_lt lt]
      have eq : m = (⟨⟨xs⟩⟩ : ByteArray).size - (n + 1) := by omega
      apply Eq.trans <| ih (n + 1) xs ((⟨⟨xs⟩⟩ : ByteArray).get! n :: ys) eq
      rw [List.reverse_cons, List.append_assoc]
      apply congr_arg₂ _ rfl
      apply Eq.trans _ List.drop_eq_getElem?_toList_append.symm
      apply congr_arg₂ _ _ rfl
      simp [ByteArray.get!]
      have hh :=
        Option.eq_some_of_isSome <| (iff_of_eq <| isSome_getElem? xs n).mpr lt
      rw [hh]
      simp

lemma toList_toByteArray (xs : B8L) :
    xs.toByteArray.toList = xs := by
  simp only [B8L.toByteArray, ByteArray.toList]
  apply Eq.trans (ByteArray.toList.loop_eq_append xs.length 0 xs [] _)
  · simp [List.reverse_nil]
  · simp [Nat.sub_zero]; rfl

def Evm.toResult (evm : Evm) : Result :=
  let hh := evm.msg.benv.state
  {
    bal := hh.bal,
    stor := hh.stor,
    code := ByteArray.toList ∘ hh.getCode,
    ret := evm.output,
    dest := evm.accountsToDelete.toList
  }

def Msg.toEnv (msg : Msg) : Env :=
  {
    cta := msg.currentTarget,
    oga := msg.tenv.origin,
    gpr := msg.tenv.gasPrice.toB256,
    cld := msg.data
    cla := msg.caller,
    clv := msg.value,
    code := msg.code.toList,
    exd := 1024 - msg.depth,
    wup := !msg.isStatic
  }

def Msg.toDesc (msg : Msg) : Desc :=
  {
    bal := msg.benv.state.bal,
    stor := msg.benv.state.stor,
    code := ByteArray.toList ∘ msg.benv.state.getCode,
    stk := [],
    mem := .init
    ret := []
    dest := []
  }

lemma exec_of_executeCode
    (msg : Msg) (lim : Nat) (evm : Evm)
    (xc : (executeCode false msg lim) = .ok evm) :
    Nonempty (
      Exec
        msg.toEnv
        msg.toDesc
        (msg.codeAddress.getD 0).toNat evm.toResult
    ) := by
  sorry

def mkResult (s : State) (mco : MsgCallOutput) : Result :=
  {
    bal := s.bal
    stor := s.stor
    code := s.codes
    ret := mco.returnData
    dest := mco.accountsToDelete.toList
  }

lemma Std.HashSet.toList_emptyWithCapacity
    {α : Type u} [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] (k : Nat) :
    (Std.HashSet.emptyWithCapacity k : Std.HashSet α).toList = [] := by
  rw [List.eq_nil_iff_length_eq_zero, Std.HashSet.length_toList]
  apply Std.HashSet.size_emptyWithCapacity

lemma Except.of_bimap_eq_ok
  {ε : Type u0} {δ : Type u1} {ξ : Type u2} {υ : Type u3}
  (f : ε → δ) (g : ξ → υ) (e : Except ε ξ) (y : υ)
  (eq : Except.bimap f g e = .ok y) :
    ∃ x : ξ, e = .ok x ∧ g x = y := by
  rcases e with _ | x <;> simp [Except.bimap] at eq
  refine' ⟨x, rfl, eq⟩

lemma Except.match_error {ξ υ ζ} (f : ξ → ζ) (g : υ → ζ) (x : ξ) :
  (
    match (.error x : Except ξ υ) with
    | .ok y' => g y'
    | .error x' => f x'
  ) = f x := by rfl

#check processCreateMessage
lemma of_processCreateMessage (msg : Msg) (evm : Evm) (lim : Nat)
    (h : processCreateMessage false msg lim = .ok evm) :
    ∃ (evm' : Evm) (lim' : Nat),
      processMessage false
        (processCreateMessageMsg msg) lim' = .ok evm' ∧
      if evm'.error.isNone then
        (

          (
            ∃ evm'' : Evm,
              processCreateMessageExecution evm' = .ok evm'' ∧
              evm = evm''.setCode msg.currentTarget ⟨⟨evm''.output⟩⟩
          ) ∨
          (
            ∃ (evm'' : Evm) (err : String),
              isExceptionalHalt err ∧
              processCreateMessageExecution evm' = .error (evm'', err) ∧
              evm = processCreateMessageExeptionalHalt evm'' err
                msg.benv.state
                msg.tenv.transientStorage
          )
        )
      else
        evm = evm'.rollback msg.benv.state msg.tenv.transientStorage := by
  rcases lim with _ | lim' <;> try {simp [processCreateMessage] at h; done}
  simp only [processCreateMessage] at h
  rename' h => h'
  rcases of_bind_eq_ok h' with ⟨evm', h0, h⟩; clear h'
  refine' ⟨evm', lim', h0, _⟩; clear h0
  by_cases h_isNone : evm'.error.isNone
  · rw [if_pos h_isNone] at h
    rw [if_pos h_isNone]
    revert h
    rcases (processCreateMessageExecution evm') with ⟨evm'', err⟩ | evm''
    · intro h;
      simp only [] at h
      by_cases h_err : isExceptionalHalt err
      · rw [if_pos h_err] at h
        refine' .inr ⟨evm'', err, h_err, rfl, _⟩
        cases h; rfl
      · rw [if_neg h_err] at h
        cases h
    · intro h
      simp only [] at h
      refine' .inl ⟨evm'', rfl, _⟩
      cases h; rfl
  · rw [if_neg h_isNone] at h
    rw [if_neg h_isNone]
    cases h; rfl

structure Benv.Rels where
  (chainId : B64 → B64 → Prop)
  (state : State → State → Prop)
  (origState : State → State → Prop)
  (createdAccounts : AdrSet → AdrSet → Prop)
  (blockGasLimit : Nat → Nat → Prop)
  (blockHashes : List B256 → List B256 → Prop)
  (coinbase : Adr → Adr → Prop)
  (number : Nat → Nat → Prop)
  (baseFeePerGas : Nat → Nat → Prop)
  (time : B256 → B256 → Prop)
  (prevRandao : B256 → B256 → Prop)
  (excessBlobGas : Nat → Nat → Prop)
  (parentBeaconBlockRoot : B256 → B256 → Prop)

def Benv.Rels.dft : Benv.Rels where
  chainId := Eq
  state := Eq
  origState := Eq
  createdAccounts := Eq
  blockGasLimit := Eq
  blockHashes := Eq
  coinbase := Eq
  number := Eq
  baseFeePerGas := Eq
  time := Eq
  prevRandao := Eq
  excessBlobGas := Eq
  parentBeaconBlockRoot := Eq

structure Benv.Rel (r : Benv.Rels) (b b' : Benv) : Prop where
  (chainId : r.chainId b.chainId b'.chainId)
  (state : r.state b.state b'.state)
  (origState : r.origState b.origState b'.origState)
  (createdAccounts :
    r.createdAccounts b.createdAccounts b'.createdAccounts)
  (blockGasLimit :
    r.blockGasLimit b.blockGasLimit b'.blockGasLimit)
  (blockHashes :
    r.blockHashes b.blockHashes b'.blockHashes)
  (coinbase : r.coinbase b.coinbase b'.coinbase)
  (number : r.number b.number b'.number)
  (baseFeePerGas :
    r.baseFeePerGas b.baseFeePerGas b'.baseFeePerGas)
  (time : r.time b.time b'.time)
  (prevRandao : r.prevRandao b.prevRandao b'.prevRandao)
  (excessBlobGas :
    r.excessBlobGas b.excessBlobGas b'.excessBlobGas)
  (parentBeaconBlockRoot :
    r.parentBeaconBlockRoot
      b.parentBeaconBlockRoot
      b'.parentBeaconBlockRoot)



-- #exit
-- def Benv.Transfer (benv : Benv) (kd : Adr) (v : B256) (ki : Adr) (benv' : Benv) : Prop :=
--   benv' = benv.withState benv'.state ∧
--   _root_.Transfer benv.state.bal kd v ki benv'.state.bal

structure Msg.Rels where
  (benv : Benv → Benv → Prop)
  (tenv : Tenv → Tenv → Prop)
  (caller : Adr → Adr → Prop)
  (target : Option Adr → Option Adr → Prop)
  (currentTarget : Adr → Adr → Prop)
  (gas : Nat → Nat → Prop)
  (value : B256 → B256 → Prop)
  (data : B8L → B8L → Prop)
  (codeAddress : Option Adr → Option Adr → Prop)
  (code : ByteArray → ByteArray → Prop)
  (depth : Nat → Nat → Prop)
  (shouldTransferValue : Bool → Bool → Prop)
  (isStatic : Bool → Bool → Prop)
  (accessedAddresses : AdrSet → AdrSet → Prop)
  (accessedStorageKeys : KeySet → KeySet → Prop)
  (disablePrecompiles : Bool → Bool → Prop)

def Msg.Rels.dft : Msg.Rels where
  benv := Eq
  tenv := Eq
  caller := Eq
  target := Eq
  currentTarget := Eq
  gas := Eq
  value := Eq
  data := Eq
  codeAddress := Eq
  code := Eq
  depth := Eq
  shouldTransferValue := Eq
  isStatic := Eq
  accessedAddresses := Eq
  accessedStorageKeys := Eq
  disablePrecompiles := Eq

structure Msg.Rel (r : Rels) (m m' : Msg) : Prop where
  (benv : r.benv m.benv m'.benv)
  (tenv : r.tenv m.tenv m'.tenv)
  (caller : r.caller m.caller m'.caller)
  (target : r.target m.target m'.target)
  (currentTarget : r.currentTarget m.currentTarget m'.currentTarget)
  (gas : r.gas m.gas m'.gas)
  (value : r.value m.value m'.value)
  (data : r.data m.data m'.data)
  (codeAddress : r.codeAddress m.codeAddress m'.codeAddress)
  (code : r.code m.code m'.code)
  (depth : r.depth m.depth m'.depth)
  (shouldTransferValue :
    r.shouldTransferValue m.shouldTransferValue m'.shouldTransferValue)
  (isStatic : r.isStatic m.isStatic m'.isStatic)
  (accessedAddresses :
    r.accessedAddresses m.accessedAddresses m'.accessedAddresses)
  (accessedStorageKeys :
    r.accessedStorageKeys m.accessedStorageKeys m'.accessedStorageKeys)
  (disablePrecompiles :
    r.disablePrecompiles m.disablePrecompiles m'.disablePrecompiles)

lemma Except.of_assert_eq_ok {ξ} (p : Prop) [Decidable p] (x : ξ)
    (h : Except.assert p x = .ok ()) : p := by
  simp [Except.assert] at h; apply h

/-
lemma Lean.RBNode.find_setBlack
    (α : Type u) (β : Type v) (cmp : α → α → Ordering)
    (nd : RBNode α (fun _ ↦ β)) (a : α) : nd.setBlack.find cmp a = nd.find cmp a := by
  induction nd <;> simp [find, RBNode.setBlack]

lemma Ordering.trichotomy {α : Type u} (cmp : α → α → Ordering) (a b : α) :
    (cmp a b = .lt) ∨ (cmp a b = .eq) ∨ (cmp a b = .gt) := by
  cases h : cmp a b <;> simp [h]

def Lean.RBNode.sizeRec (α : Type u) (β : α → Type v) (p : RBNode α β → Type w)
    (h : (x : RBNode α β) → ((y : RBNode α β) → y.size < x.size → p y) → p x) :
    ∀ x : RBNode α β, p x := by
  intro x
  let r := fun (a b : RBNode α β) => a.size < b.size
  let wf_nat := Nat.lt_wfRel.wf
  let wf := InvImage.wf (@Lean.RBNode.size α β) wf_nat
  apply @WellFounded.fix (RBNode α β) p r wf
  exact h


lemma Lean.RBNode.balLeft_cases (α : Type u) (β : α → Type v)
    (k : α) (v : β k) (l r : RBNode α β) :
    ( ∃ a kx vx b,
        l = node .red a kx vx b ∧
        RBNode.balLeft l k v r = node .red (node .black a kx vx b) k v r ) ∨
    ( ∃ a ky vy b,
        r = .node .black a ky vy b ∧
        RBNode.balLeft l k v r = .balance2 l k v (node .red a ky vy b) ) ∨
    ( ∃ a ky vy b kz vz c,
        r = node .red (node .black a ky vy b) kz vz c ∧
        RBNode.balLeft l k v r =
          node .red (node .black l k v a) ky vy (balance2 b kz vz (setRed c)) ) ∨
    (RBNode.balLeft l k v r = .node .red l k v r) := by
  rcases l with _ | ⟨(_ | _), _⟩
  · right;
    rcases r with _ | ⟨(_ | _), l', _⟩
    · right; right; rfl
    · rcases l' with _ | ⟨(_ | _), _⟩
      · right; right; rfl
      · right; right; rfl
      · right; left; refine ⟨_, _, _, _, _, _, _, rfl, rfl⟩
    · left; refine ⟨_, _, _, _, rfl, rfl⟩
  · left; refine' ⟨_, _, _, _, rfl, _⟩; simp only [balLeft]
  · right;
    rcases r with _ | ⟨(_ | _), l', _⟩
    · right; right; rfl
    · rcases l' with _ | ⟨(_ | _), _⟩
      · right; right; rfl
      · right; right; rfl
      · right; left; refine ⟨_, _, _, _, _, _, _, rfl, rfl⟩
    · left; refine ⟨_, _, _, _, rfl, rfl⟩

lemma Lean.RBNode.find_balLeft {α : Type u} {β : Type v} (cmp : α → α → Ordering)
    (k k' : α) (v : β) (l r : RBNode α (fun x ↦ β)) (c : RBColor) :
    (RBNode.balLeft l k v r).find cmp k' = (node c l k v r).find cmp k' := by
  rcases Lean.RBNode.balLeft_cases α (fun x ↦ β) k v l r with
      ⟨a, kx, vx, b, eq, rw⟩
    | ⟨a, ky, vy, b, eq, rw⟩
    | ⟨a, ky, vy, b, kz, vz, c, eq, rw⟩
    | bar

  · rw [rw, eq]; simp only [find]
  · sorry
  · rw [rw, eq]
    simp only [find]
    rcases Ordering.trichotomy cmp k' k with hk | hk | hk
      <;> rw [hk] <;> simp only []

lemma Lean.RBNode.find_del {α : Type u} {β : Type v} (cmp : α → α → Ordering)
    (j : α) (x : RBNode α fun x ↦ β) :
    RBNode.find cmp (RBNode.del cmp j x) j = none := by
  induction x with
  | leaf => simp [RBNode.del, RBNode.find]
  | node cl l k v r ihl ihr  =>
    simp only [del]
    rcases Ordering.trichotomy cmp j k with jk | jk | jk
      <;> rw [jk] <;> simp only []
    · by_cases l_color : l.isBlack = true
      · rw [if_pos l_color]
        have fooo := ((del cmp j l).balLeft k v r)

lemma Lean.RBNode.find_del {α : Type u} {β : Type v} (cmp : α → α → Ordering)
    (j : α) (x : RBNode α fun x ↦ β) :
    RBNode.find cmp (RBNode.del cmp j x) j = none := by
  let wf := InvImage.wf (@Lean.RBNode.size α (fun x ↦ β)) Nat.lt_wfRel.wf
  induction x using WellFounded.induction (hwf := wf)
  rename (RBNode α (fun x ↦ β)) => x
  rename (∀ (x : RBNode α (fun x ↦ β)), _) => ih
  cases x with
  | leaf => simp [RBNode.del, RBNode.find]
  | node cl l k v r  =>
    simp only [del]
    rcases Ordering.trichotomy cmp j k with rw | rw | rw <;> rw [rw] <;> simp only []
    · by_cases h_color : l.isBlack = true
      · rw [if_pos h_color]
        rcases Lean.RBNode.balLeft_cases α (fun x ↦ β) k v (del cmp j l) r with
          ⟨a, kx, vx, b, eq, rw'⟩ | bar`
        · rw [rw']
          simp only [find]
          rw [rw]; simp only []














lemma Lean.RBMap.find?_erase (α : Type u) (β : Type v) (cmp : α → α → Ordering)
    (m : Lean.RBMap α β cmp) (a : α) : (m.erase a).find? a = .none := by
  rcases m with ⟨nd, wf⟩

  simp [Lean.RBMap.erase, Lean.RBMap.find?,
    Lean.RBNode.erase,
  ]
  rw [Lean.RBNode.find_setBlack]


-/

#synth Ord Nat
#synth LT B256
#check B128
#check B256.lt_iff_toNat_lt_toNat
#synth Ord Adr --instOrdAdr
#check instOrdAdr
#check Ord Adr --instOrdAdr

lemma B32.lt_trichotomy (a b : B32) : a < b ∨ a = b ∨ b < a := by
  by_cases ab : a < b
  · left; exact ab
  · right; rw [eq_comm, or_comm];
    apply UInt32.lt_or_eq_of_le <| UInt32.not_lt.mp ab

lemma B64.lt_trichotomy (a b : B64) : a < b ∨ a = b ∨ b < a := by
  by_cases ab : a < b
  · left; exact ab
  · right; rw [eq_comm, or_comm];
    apply UInt64.lt_or_eq_of_le <| UInt64.not_lt.mp ab

lemma B128.lt_trichotomy (a b : B128) : a < b ∨ a = b ∨ b < a := by
  by_cases ab : a < b
  · left; exact ab
  · right; rw [eq_comm, or_comm];
    apply B128.lt_or_eq_of_le <| B128.not_lt.mp ab


lemma B256.lt_trichotomy (a b : B256) : a < b ∨ a = b ∨ b < a := by
  by_cases ab : a < b
  · left; exact ab
  · right; rw [eq_comm, or_comm];
    apply B256.lt_or_eq_of_le <| B256.not_lt.mp ab

lemma Adr.lt_trichotomy (a b : Adr) : a < b ∨ a = b ∨ b < a := by
  by_cases ab : a ≤ b <;> by_cases ba : b ≤ a
  · right; left; apply Adr.le_antisymm ab ba
  · left; apply Adr.lt_iff_le_not_ge.mpr ⟨ab, ba⟩
  · right; right; apply Adr.lt_iff_le_not_ge.mpr ⟨ba, ab⟩
  · cases not_or_intro ab ba <| Adr.le_total _ _

instance : @Std.OrientedCmp B32 (@compare B32 instOrdUInt32) := by
  constructor; intro a b
  simp only [compare, compareOfLessAndEq]
  rcases B32.lt_trichotomy a b with h | h | h
  · rw [if_pos h, if_neg <| UInt32.lt_asymm h]
    rw [if_neg <| ne_comm.mp <| UInt32.ne_of_lt h]; rfl
  · cases h; rw [if_neg (UInt32.lt_irrefl _), if_pos rfl]; rfl
  · rw [if_pos h, if_neg <| UInt32.lt_asymm h]
    rw [if_neg <| ne_comm.mp <| UInt32.ne_of_lt h]; rfl

instance : @Std.OrientedCmp B64 (@compare B64 instOrdUInt64) := by
  constructor; intro a b
  simp only [compare, compareOfLessAndEq]
  rcases B64.lt_trichotomy a b with h | h | h
  · rw [if_pos h, if_neg <| UInt64.lt_asymm h]
    rw [if_neg <| ne_comm.mp <| UInt64.ne_of_lt h]; rfl
  · cases h; rw [if_neg (UInt64.lt_irrefl _), if_pos rfl]; rfl
  · rw [if_pos h, if_neg <| UInt64.lt_asymm h]
    rw [if_neg <| ne_comm.mp <| UInt64.ne_of_lt h]; rfl

lemma B128.ne_of_lt {a b : B128} (h : a < b) : a ≠ b := by
  intro h'; rw [h'] at h; apply B128.lt_irrefl b h

lemma B256.ne_of_lt {a b : B256} (h : a < b) : a ≠ b := by
  intro h'; rw [h'] at h; apply B256.lt_irrefl b h

lemma Adr.ne_of_lt {a b : Adr} (h : a < b) : a ≠ b := by
  intro h'; rw [h'] at h; apply Adr.lt_irrefl b h

instance : @Std.OrientedCmp B128 (@compare B128 instOrdB128) := by
  constructor; intro a b
  simp only [compare, compareOfLessAndEq]
  rcases B128.lt_trichotomy a b with h | h | h
  · rw [if_pos h, if_neg <| B128.lt_asymm h]
    rw [if_neg <| ne_comm.mp <| B128.ne_of_lt h]; rfl
  · cases h; rw [if_neg (B128.lt_irrefl _), if_pos rfl]; rfl
  · rw [if_pos h, if_neg <| B128.lt_asymm h]
    rw [if_neg <| ne_comm.mp <| B128.ne_of_lt h]; rfl

instance : @Std.OrientedCmp B256 (@compare B256 instOrdB256) := by
  constructor; intro a b
  simp only [compare, compareOfLessAndEq]
  rcases B256.lt_trichotomy a b with h | h | h
  · rw [if_pos h, if_neg <| B256.lt_asymm h]
    rw [if_neg <| ne_comm.mp <| B256.ne_of_lt h]; rfl
  · cases h; rw [if_neg (B256.lt_irrefl _), if_pos rfl]; rfl
  · rw [if_pos h, if_neg <| B256.lt_asymm h]
    rw [if_neg <| ne_comm.mp <| B256.ne_of_lt h]; rfl

instance : @Std.OrientedCmp Adr (@compare Adr instOrdAdr) := by
  constructor; intro a b
  simp only [compare, compareOfLessAndEq]
  rcases Adr.lt_trichotomy a b with h | h | h
  · rw [if_pos h, if_neg <| Adr.lt_asymm h]
    rw [if_neg <| ne_comm.mp <| Adr.ne_of_lt h]; rfl
  · cases h; rw [if_neg (Adr.lt_irrefl _), if_pos rfl]; rfl
  · rw [if_pos h, if_neg <| Adr.lt_asymm h]
    rw [if_neg <| ne_comm.mp <| Adr.ne_of_lt h]; rfl


-- instance : @Std.OrientedCmp Adr (@compare Adr instOrdAdr) := by
--   constructor; intro ⟨x, x'⟩ ⟨y, y'⟩
--   simp only [compare]; simp only [Adr.compare]
--   have rw : compare x y = (compare y x).swap := Std.OrientedCmp.eq_swap
--   have rw' : compare x' y' = (compare y' x').swap := Std.OrientedCmp.eq_swap
--   rw [rw, rw']; cases (compare y x) <;> cases (compare y' x') <;> simp

-- def Adr.LE (x y : Adr) : Prop :=
--   x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)
-- instance : @LE Adr := ⟨Adr.LE⟩
-- instance {x y : Adr} : Decidable (x ≤ y) := instDecidableOr
--
-- lemma Adr.le_iff (x y : Adr) :
--   x ≤ y ↔ (x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)) := Iff.refl _
--
-- lemma Adr.le_refl (x : Adr) : x ≤ x := by
--   right; refine ⟨rfl, B128.le_refl _⟩
--
-- lemma Adr.le_trans {a b c : Adr} (ab : a ≤ b) (bc : b ≤ c) : a ≤ c := by
--   rcases ab with ab | ab <;> rcases bc with bc | bc
--   · left; apply UInt32.lt_trans ab bc
--   · left; rw [← bc.1]; exact ab
--   · left; rw [ab.1]; exact bc
--   · right; refine ⟨Eq.trans ab.1 bc.1, B128.le_trans ab.2 bc.2⟩
--
-- lemma Adr.lt_iff_le_not_ge {a b : Adr} : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
--   constructor <;> intro h
--   · rcases h with h | h
--     · refine' ⟨.inl h, not_or_intro (UInt32.lt_asymm h) _⟩
--       apply not_and_of_not_left _ <| Ne.symm <| UInt32.ne_of_lt h
--     · refine' ⟨.inr ⟨h.1, B128.le_of_lt h.2⟩, not_or_intro _ _⟩
--       · rw [h.1]; apply UInt32.lt_irrefl
--       · apply not_and_of_not_right; rw [B128.not_le]; apply h.2
--   · rcases h with ⟨h | ⟨h1, h2⟩, h'⟩
--     · apply Or.inl h
--     · rcases not_or.mp h' with ⟨h1', h2'⟩
--       right; refine' ⟨h1, B128.lt_iff_le_not_ge.mpr ⟨h2, not_and.mp h2' h1.symm⟩⟩
--
-- instance : Preorder Adr where
--   le_refl := Adr.le_refl
--   le_trans _ _ _ := Adr.le_trans
--   lt := Adr.LT
--   lt_iff_le_not_ge _ _ := Adr.lt_iff_le_not_ge
--
-- lemma Adr.le_antisymm {a b : Adr} : a ≤ b → b ≤ a → a = b := by
--   intro h₁ h₂
--   rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
--   · cases lt_asymm h₁ h₂
--   · cases UInt32.ne_of_lt h₁ h₂.1.symm
--   · cases UInt32.ne_of_lt h₂ h₁.1.symm
--   · exact Prod.ext h₁.1 <| B128.le_antisymm h₁.2 h₂.2
--
-- instance : PartialOrder Adr where
--   le_antisymm _ _ := Adr.le_antisymm
--
-- lemma Adr.le_total (m n : Adr) : m ≤ n ∨ n ≤ m := by
--   by_cases h : m.1 < n.1
--   · left; left; exact h
--   · rw [not_lt, UInt32.le_iff_lt_or_eq] at h
--     rcases h with h | h
--     · right; left; exact h
--     · rcases B128.le_total m.2 n.2 with h' | h'
--       · left; right; refine ⟨h.symm, h'⟩
--       · right; right; refine ⟨h, h'⟩
--
-- instance : DecidableLT Adr :=
--   fun a b => by rw [Adr.lt_iff]; infer_instance
--
-- instance : DecidableLE Adr :=
--   fun a b => by rw [Adr.le_iff]; infer_instance
--
-- instance : DecidableEq Adr :=
--   fun a b => by rw [Prod.ext_iff]; infer_instance
--
--
-- instance : LinearOrder Adr where
--   le_total := Adr.le_total
--   toDecidableLE := by infer_instance
--



-- lemma B64.isLE_compare_eq_true (a b : B64) :
--     (compare a b).isLE = true ↔ (a ≤ b) := by
--   simp [Ord.compare, compareOfLessAndEq]
--   by_cases h : a < b
--   · rw [if_pos h]; simp; apply le_of_lt h
--   · rw [if_neg h]
--     by_cases h' : a = b
--     · rw [if_pos h']; simp; apply UInt64.le_of_eq h'
--     · rw [if_neg h']; simp
--       have h'' := lt_trichotomy a b
--       simp [h, h'] at h''; apply h''




-- lemma B128.isLE_compare_eq_true (a b : B128) :
--     (compare a b).isLE = true ↔ (a ≤ b) := by
--   rcases a with ⟨a1, a2⟩;  rcases b with ⟨b1, b2⟩
--   simp [B128.compare, LE.le, B128.LE, Ord.compare, compareOfLessAndEq]
--   by_cases h1 : a1 < b1
--   · rw [if_pos h1]; simp [h1]
--   · rw [if_neg h1]
--     by_cases h2 : a1 = b1
--     · rw [if_pos h2]; simp [h2]
--       apply B64.isLE_compare_eq_true
--     · rw [if_neg h2]; simp [h1, h2]

-- lemma B32.not_lt {a b : B32} : ¬ a < b ↔ b ≤ a := UInt32.not_lt
--
-- lemma Adr.isLE_compare_eq_true (a b : Adr) :
--     (compare a b).isLE = true ↔ (a ≤ b) := by
--
--   simp [Adr.compare, LE.le, Adr.LE, Ord.compare,compareOfLessAndEq]
--   by_cases h1 : a.1 < b.1
--   · rw [if_pos h1]; simp [h1]
--   · rw [if_neg h1]
--     by_cases h2 : a.1 = b.1
--     · rw [if_pos h2]; simp; simp [h2]
--       apply compare_le_iff_le
--
--


--
--lemma Adr.le_trans {a b c : Adr} (ab : a ≤ b) (bc : b ≤ c) : a ≤ c := by
--  rcases ab with ab | ab <;> rcases bc with bc | bc
--  · left; apply UInt32.lt_trans ab bc
--  · left; rw [← bc.1]; exact ab
--  · left; rw [ab.1]; exact bc
--  · right; refine ⟨Eq.trans ab.1 bc.1, B128.le_trans ab.2 bc.2⟩

instance : @Std.TransCmp Adr (@compare Adr instOrdAdr) := by
  constructor; intro a b c
  iterate 3 rw [Ordering.isLE_iff_ne_gt, ← ne_eq, compare_le_iff_le]
  apply Adr.le_trans

lemma State.setBal_eq (st : State) (adr : Adr) (val : B256) :
    st.setBal adr val = st.set adr ((st.get adr).withBal val) := rfl

lemma State.bal_eq (st : State) (adr : Adr) :
    st.bal adr = (st.get adr).bal := rfl

lemma State.get_set (st : State) (adr adr' : Adr) (acct : Acct) :
    (st.set adr acct).get adr' = if adr = adr' then acct else st.get adr' := by
  simp only [set, get]
  by_cases erase : acct = Acct.nil
  · rw [if_pos erase]; apply Eq.trans Std.TreeMap.getD_erase
    rw [ite_eq_ite_of_iff compare_eq_iff_eq rfl rfl, erase]
  · rw [if_neg erase]; apply Eq.trans Std.TreeMap.getD_insert
    rw [ite_eq_ite_of_iff compare_eq_iff_eq rfl rfl]

lemma State.bal_setBal (st : State) (adr adr' : Adr) (val : B256) :
    (st.setBal adr val).bal adr' = if adr = adr' then val else st.bal adr' := by
  rw [setBal_eq, bal_eq, get_set, @ite_distrib _ _ Acct.bal]; rfl

lemma State.bal_setBal_self (st : State) (adr : Adr) (val : B256) :
    (st.setBal adr val).bal adr = val := by rw [bal_setBal, if_pos rfl]

lemma State.bal_set_self (st : State) (adr : Adr) (acct : Acct) :
    (st.set adr acct).bal adr = acct.bal := by
  rw [bal_eq, get_set, if_pos rfl]

lemma State.get_setBal (st : State) (adr adr' : Adr) (val : B256) :
    (st.setBal adr val).get adr' =
      if adr = adr' then (st.get adr).withBal val else st.get adr' := by
  rw [setBal_eq, get_set]

def Acct.addBal (ac : Acct) (val : B256) : Acct := {ac with bal := ac.bal + val}

lemma State.get_addBal (st : State) (adr adr' : Adr) (val : B256) :
    (st.addBal adr val).get adr' =
      if adr = adr' then (st.get adr).addBal val else st.get adr' := by
  rw [State.addBal, get_setBal]; rfl




-- lemma Std.TreeMap.getD_erase_of_ne {α : Type u} {β : Type v}
--     {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp}
--     [Std.TransCmp cmp] {k a : α} {fallback : β} :
--     (t.erase k).getD a fallback = if cmp k a = Ordering.eq then fallback else t.getD a fallback
--

--lemma B64.compare_eq_iff_eq {a b : B64} :
--    B128.compare a b = Ordering.eq ↔ a = b := by



--lemma B128.compare_eq_iff_eq {a b : B128} :
--    B128.compare a b = Ordering.eq ↔ a = b := by
--  rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩
--  simp only [B128.compare, Ord.compare, compareOfLessAndEq]
--  by_cases h : a1 < b1
--  · rw [if_pos h]; simp; intro eq
--    have rw := congr_arg Prod.fst eq
--    simp at rw; rw [rw] at h; cases UInt64.lt_irrefl _ h
--  · rw [if_neg h]
--    by_cases h' : a1 = b1
--    · rw [if_pos h']; simp; --rw [compare_eq_iff_eq]
--
--
--
--










    --cases UInt32.lt_irrefl _ h





--
--lemma Adr.compare_eq_iff_eq {a b : Adr} : Adr.compare a b = Ordering.eq ↔ a = b := by
--  simp only [Adr.compare, Ord.compare, compareOfLessAndEq]
--  by_cases h : a.1 < b.1
--  · rw [if_pos h]; simp; intro eq
--    rw [congr_arg Prod.fst eq] at h; cases UInt32.lt_irrefl _ h
--  · rw [if_neg h]
--    by_cases h' : a.1 = b.1
--    · rw [if_pos h']; simp; rw [B128.compare_eq_iff_eq]
--      rw [@Prod.eq_iff_fst_eq_snd_eq B32]; simp [h']
--    · rw [if_neg h']; rw [@Prod.eq_iff_fst_eq_snd_eq B32]; simp [h']

lemma State.bal_set_of_ne {st : State} {adr adr' : Adr} {acct : Acct}
    (ne : adr ≠ adr') : (st.set adr acct).bal adr' = st.bal adr' := by
  rw [bal_eq, get_set, if_neg ne, ← bal_eq]

lemma State.of_subBal_eq_some {st st' : State} {adr : Adr} {val : B256}
    (h : st.subBal adr val = .some st') :
    Decrease adr val st.bal st'.bal := by
  simp [State.subBal] at h
  rcases h with ⟨le, eq⟩; simp [Decrease]
  intro adr'; constructor <;> intro h_adr'
  · cases h_adr'; rw [← eq, bal_setBal_self]
  · rw [← eq, eq_comm]; apply bal_set_of_ne h_adr'

lemma Benv.withState_eq (benv : Benv) (st : State) :
  benv.withState st = {benv with state := st} := rfl

lemma Benv.le_of_subBal_eq_some {benv benv' : Benv} {adr : Adr} {val : B256}
    (h : benv.subBal adr val = .some benv') : val ≤ benv.state.bal adr := by
  by_contra h'; rcases Option.bind_eq_some_iff.mp h with ⟨st, h_sub, eq⟩
  simp [State.subBal] at h_sub; exact h' h_sub.1


--   (nonce : B64)
--   (bal : B256)
--   (stor : Stor)
--   (code : ByteArray)

structure Acct.Rels where
  (nonce : B64 → B64 → Prop)
  (bal : B256 → B256 → Prop)
  (stor : Stor → Stor → Prop)
  (code : ByteArray → ByteArray → Prop)

def Acct.Rels.dft : Acct.Rels where
  nonce := Eq
  bal := Eq
  stor := Eq
  code := Eq

structure Acct.Rel (r : Acct.Rels) (a a' : Acct) : Prop where
  (nonce : r.nonce a.nonce a'.nonce)
  (bal : r.bal a.bal a'.bal)
  (stor : r.stor a.stor a'.stor)
  (code : r.code a.code a'.code)

-- def State.Decrease (st : State) (adr : Adr) (val : B256) (st' : State) : Prop :=
--   Frel adr (λ ac ac' => Acct.Decrease ac val ac') st.get st'.get

-- def Transfer
--     (b : Adr → B256)
--     (kd : Adr) (v : B256) (ki : Adr)
--     (d : Adr → B256) : Prop :=
--     v ≤ b kd ∧
--   ∃ c : Adr → B256,
--     Decrease kd v b c ∧
--     Increase ki v c d

def Acct.Increase (ac : Acct) (val : B256) (ac' : Acct) : Prop :=
  Acct.Rel {Rels.dft with bal := λ x y => x + val = y} ac ac'

def Acct.Decrease (ac : Acct) (val : B256) (ac' : Acct) : Prop :=
  Acct.Rel {Rels.dft with bal := λ x y => x - val = y} ac ac'

def Acct.SafeDecrease (ac : Acct) (val : B256) (ac' : Acct) : Prop :=
  Acct.Rel {
    Rels.dft with bal := λ x y => val ≤ x ∧ x - val = y
  } ac ac'

def State.Increase (st : State) (adr : Adr) (val : B256) (st' : State) : Prop :=
  Frel adr (λ ac ac' => Acct.Increase ac val ac') st.get st'.get

def State.Decrease (st : State) (adr : Adr) (val : B256) (st' : State) : Prop :=
  Frel adr (λ ac ac' => Acct.Decrease ac val ac') st.get st'.get

def State.SafeDecrease (st : State) (adr : Adr) (val : B256) (st' : State) : Prop :=
  Frel adr (λ ac ac' => Acct.SafeDecrease ac val ac') st.get st'.get

def State.Transfer (st : State) (kd : Adr) (v : B256) (ki : Adr) (st'' : State) : Prop :=
  ∃ st' : State,
    State.SafeDecrease st kd v st' ∧
    State.Increase st' ki v st''

def Benv.Increase (benv : Benv) (adr : Adr) (val : B256) (benv' : Benv) : Prop :=
  Rel {Rels.dft with state := λ st st' => State.Increase st adr val st'} benv benv'

def Benv.Decrease (benv : Benv) (adr : Adr) (val : B256) (benv' : Benv) : Prop :=
  Rel {Rels.dft with state := λ st st' => State.Decrease st adr val st'} benv benv'

def Benv.SafeDecrease (benv : Benv) (adr : Adr) (val : B256) (benv' : Benv) : Prop :=
  Rel {Rels.dft with state := λ st st' => State.SafeDecrease st adr val st'} benv benv'

def Benv.Transfer (benv : Benv) (kd : Adr) (v : B256) (ki : Adr) (benv' : Benv) : Prop :=
  Rel {Rels.dft with state := λ st st' => State.Transfer st kd v ki st'} benv benv'

def Msg.Transfer (msg : Msg) (kd : Adr) (v : B256) (ki : Adr) (msg' : Msg) : Prop :=
  Rel {Rels.dft with benv := λ benv benv' => Benv.Transfer benv kd v ki benv'} msg msg'

lemma State.increase_of_addBal (st st' : State) (adr : Adr) (val : B256)
    (h : State.addBal st adr val = st') :
    State.Increase st adr val st' := by
  rw [← h]; intro x; constructor
  · intro eq; rw [get_addBal, if_pos eq, eq]; constructor <;> rfl
  · intro ne; rw [get_addBal, if_neg ne]

lemma Benv.of_subBal_eq_some (benv benv' : Benv) (adr : Adr) (val : B256)
    (h : benv.subBal adr val = .some benv') :
    ∃ st : State,
      benv' = benv.withState st ∧
      _root_.Decrease adr val benv.state.bal st.bal := by
  rcases Option.bind_eq_some_iff.mp h with ⟨st, h_sub, eq⟩
  simp at eq; refine' ⟨st, eq.symm, State.of_subBal_eq_some h_sub⟩

lemma Benv.increase_of_addBal {benv benv' : Benv} {adr : Adr} {val : B256}
    (h : benv.addBal adr val = benv') :
    Benv.Increase benv adr val benv' := by
  rw [← h]; constructor <;> try {rfl}
  simp [Benv.addBal, Benv.withState]
  apply State.increase_of_addBal _ _ _ _ rfl

lemma State.decrease_of_subBal (st st' : State) (adr : Adr) (val : B256)
    (h : State.subBal st adr val = .some st') :
    State.Decrease st adr val st' := by
  simp [subBal] at h; simp [Decrease]; rw [← h.2]
  intro adr'; constructor
  · intro eq; cases eq;
    rw [get_setBal, if_pos rfl]; constructor <;> rfl
  · intro ne; rw [get_setBal, if_neg ne]

lemma State.safeDecrease_of_subBal (st st' : State) (adr : Adr) (val : B256)
    (h : State.subBal st adr val = .some st') :
    State.SafeDecrease st adr val st' := by
  simp [subBal] at h; simp [SafeDecrease]; rw [← h.2]
  intro adr'; constructor
  · intro eq; cases eq;
    rw [get_setBal, if_pos rfl];
    constructor <;> try {rfl}; refine' ⟨h.1, rfl⟩
  · intro ne; rw [get_setBal, if_neg ne]

lemma Benv.decrease_of_subBal {benv benv' : Benv} {adr : Adr} {val : B256}
    (h : benv.subBal adr val = .some benv') :
    Benv.Decrease benv adr val benv' := by
  rcases of_bind_eq_some h with ⟨st, h', h''⟩
  rw [← Option.some_inj.mp h'']
  constructor <;> try {rfl}
  simp [Benv.withState]
  apply State.decrease_of_subBal _ _ _ _ h'

lemma Benv.safeDecrease_of_subBal {benv benv' : Benv} {adr : Adr} {val : B256}
    (h : benv.subBal adr val = .some benv') :
    Benv.SafeDecrease benv adr val benv' := by
  rcases of_bind_eq_some h with ⟨st, h', h''⟩
  rw [← Option.some_inj.mp h'']
  constructor <;> try {rfl}
  simp [Benv.withState]
  apply State.safeDecrease_of_subBal _ _ _ _ h'

-- lemma Benv.of_addBal_eq (benv benv' : Benv) (adr : Adr) (val : B256)
--     (h : benv.addBal adr val = benv') :
--     Increase adr val benv.state.bal benv'.state.bal := by
--   simp only [Increase]; rw [← h];
--   simp [Benv.addBal, State.addBal, State.bal, Benv.withState]
--   intro x; constructor
--   · intro eq; rw [State.bal_setBal, if_pos eq, ← State.bal_eq, eq]
--   · intro ne; rw [State.bal_setBal, if_neg ne]

-- lemma Benv.of_subBal_eq_some (benv benv' : Benv) (adr : Adr) (val : B256)
--     (h : benv.subBal adr val = .some benv') :
--     ∃ st : State,
--       benv' = benv.withState st ∧
--       Decrease adr val benv.state.bal st.bal := by
--   rcases Option.bind_eq_some_iff.mp h with ⟨st, h_sub, eq⟩
--   simp at eq; refine' ⟨st, eq.symm, State.of_subBal_eq_some h_sub⟩

lemma Option.toExcept_eq_ok {ξ : Type u} {υ : Type v} (x : ξ) (y : υ) (o : Option υ) :
    Option.toExcept x o = Except.ok y ↔ o = .some y := by
  cases o <;> simp [toExcept]

def Benv.bal (benv : Benv) : Adr → B256 := benv.state.bal
def Msg.bal (msg : Msg) : Adr → B256 := msg.benv.bal

lemma Benv.transfer_of_subBal_of_addBal {benv benv' benv'' : Benv}
    {src tgt : Adr} {val : B256}
    (sub : benv.subBal src val = some benv')
    (add : benv'.addBal tgt val = benv'') :
    Benv.Transfer benv src val tgt benv'' := by
  have dec := Benv.safeDecrease_of_subBal sub
  have inc := Benv.increase_of_addBal add
  constructor <;> simp
  · apply Eq.trans dec.chainId inc.chainId
  · refine' ⟨benv'.state, dec.state, inc.state⟩
  · apply Eq.trans dec.origState inc.origState
  · apply Eq.trans dec.createdAccounts inc.createdAccounts
  · apply Eq.trans dec.blockGasLimit inc.blockGasLimit
  · apply Eq.trans dec.blockHashes inc.blockHashes
  · apply Eq.trans dec.coinbase inc.coinbase
  · apply Eq.trans dec.number inc.number
  · apply Eq.trans dec.baseFeePerGas inc.baseFeePerGas
  · apply Eq.trans dec.time inc.time
  · apply Eq.trans dec.prevRandao inc.prevRandao
  · apply Eq.trans dec.excessBlobGas inc.excessBlobGas
  · apply Eq.trans dec.parentBeaconBlockRoot inc.parentBeaconBlockRoot

-- lemma transfer_of_subBal_of_addBal {benv benv' benv'' : Benv}
--     {src tgt : Adr} {val : B256}
--     (sub : benv.subBal src val = some benv')
--     (add : benv'.addBal tgt val = benv'') :
--     Transfer benv.bal src val tgt benv''.bal := by
--   rcases @Benv.of_subBal_eq_some benv benv' src val sub with ⟨st, h_st, h_dec⟩
--   refine' ⟨Benv.le_of_subBal_eq_some sub, _, h_dec, _⟩
--   have h_inc := Benv.of_addBal_eq _ _ _ _ add
--   rw [h_st] at h_inc; simp [Benv.withState] at h_inc; apply h_inc

lemma of_processMessage (msg : Msg) (lim : Nat) (evm : Evm)
    (h_value : msg.shouldTransferValue = true)
    (h_error : evm.error.isNone = true)
    (h : processMessage false msg lim = .ok evm) :
    msg.depth ≤ 1024 ∧
    ∃ msg' : Msg,
      Msg.Transfer msg msg.caller msg.value msg.currentTarget msg' ∧
    ∃ lim' : Nat,
      lim' + 1 = lim ∧
      executeCode false msg' lim' = .ok evm := by
  rcases lim with _ | lim' <;> try {simp [processMessage] at h; done}
  rename' h => h'

  simp only [processMessage] at h'




  simp [Msg.benvAfterTransfer] at h'

  rcases of_bind_eq_ok h' with ⟨_, h_depth, h⟩; clear h'


  rw [if_pos h_value] at h

  simp [Except.assert] at h_depth

  refine' ⟨h_depth, _⟩


  rename' h => h'
  rcases of_bind_eq_ok h' with ⟨benv'', h_benv', h⟩; clear h'

  rcases of_bind_eq_ok h_benv' with ⟨benv', h_subbal, h_addbal⟩; clear h_benv'

  rw [Option.toExcept_eq_ok] at h_subbal
  rw [Except.ok.injEq] at h_addbal


  rename' h => h'
  rcases of_bind_eq_ok h' with ⟨evm', exec, h⟩; clear h'
  have eq : evm' = evm := by
    by_cases h_some : evm'.error.isSome = true
    · rw [if_pos h_some] at h
      cases h; simp [Evm.rollback] at h_error
      rw [h_error] at h_some; simp at h_some
    · rw [if_neg h_some] at h
      cases h; rfl
  rw [eq] at exec
  refine' ⟨msg.withBenv benv'', _, lim', rfl, exec⟩
  constructor <;> try {rfl}; simp
  simp only [Msg.withBenv]
  apply Benv.transfer_of_subBal_of_addBal h_subbal h_addbal














/-
def processMessageCall (vb : Bool) (msg : Msg) :
  Except String (State × MsgCallOutput) := do
  let benv := msg.benv
  let mut msg : Msg := msg
  let mut refundCounter : Nat := 0
  let mut evm : Evm := default
  if msg.target.isNone then
    let isCollision : Bool :=
      accountHasCodeOrNonce benv.state msg.currentTarget || accountHasStorage benv.state msg.currentTarget
    if isCollision then
      ...
    else
      evm ← Except.bimap (Prod.snd ∘ Prod.snd) id <| processCreateMessage vb msg (msg.gas + 50)
  else
    ...
  let mut logs : List Log := []
  let mut accountsToDelete : AdrSet := .emptyWithCapacity
  if evm.error.isNone then
    logs := evm.logs
    accountsToDelete := evm.accountsToDelete
    let evmRc ← (Int.toNat? evm.refund_counter).toExcept "ERROR : refund counter is negative"
    refundCounter := refundCounter + evmRc
  .ok ⟨
    evm.msg.benv.state,
    {
      gasLeft := evm.gas_left,
      refundCounter := refundCounter
      logs := logs,
      accountsToDelete := accountsToDelete,
      error := evm.error,
      returnData := evm.output
    }
  ⟩
-/

/-
  def processCreateMessage (vb : Bool) (msg : Msg) :
    Nat → Except (Benv × Tenv × String) Evm
    | 0 => ...
    | lim + 1 => do
      let init_state := msg.benv.state
      let init_tra := msg.tenv.transientStorage
      let evm ← processMessage vb (processCreateMessageMsg msg) lim
      if evm.error.isNone
      then
        let result : Execution :=
          processCreateMessageExecution evm
        match result with
        | .ok evm => .ok <| evm.setCode msg.currentTarget ⟨⟨evm.output⟩⟩
        | .error (evm, err) => ...
      else ...
-/

/-

def processCreateMessageMsg (msg : Msg) : Msg :=
  let adr := msg.currentTarget
  let benv := msg.benv.setStor adr .empty
  let benv := add_created_account benv adr
  let benv := benv.incrNonce adr
  msg.withBenv benv
-/

/-

tx target is none
receiver account has no code
receiver account nonce is 0
receiver account has no stor
processCreateMessage
  processCreateMessageMsg
    set receiver stor to empty
    add receiver to created accounts
    increment receiver nonce
  processMessage
    depth ≤ 1024
    benvAfterTransfer
      transfer from caller to currentTarget
    executeCode
  processCreateMessageExecution
  set new code

error is none
refund counter from processCreateMessage is not negative
add [refund counter from processCreateMessage] to total refund counter

-----------------------------------

eth transferred from sender to receiver
receiver has no code
exec
write code to receiver account

-/
/-
  def processMessage (vb : Bool) (msg : Msg) :
    Nat → Except (Benv × Tenv × String) Evm
    | 0 => ...
    | lim + 1 => do
      .assert
        (msg.depth ≤ 1024)
        ⟨msg.benv, msg.tenv, "StackDepthLimitError"⟩
      let benv ← msg.benvAfterTransfer
      let mut evm ← executeCode vb (msg.withBenv benv) lim
      if evm.error.isSome
        then ...
      .ok evm
-/

/-
    ∀ gpr clv ctc bal r code,
      Transfer w.bal sda clv rca bal →
      w.code rca = [] →
      Exec
        { cta := rca, oga := sda, gpr := gpr, cld := [], cla := sda,
          clv := clv, code := ctc, exd := 1024, wup := true }
        --{ bal := bal, stor := w.stor, code := w.code, stk := [],
        --  mem := Memory.init, ret := [], dest := [] }
        (Desc.init bal w.stor w.code)
        0 r →
      Overwrite rca r.ret r.code code →
      MessageCall sda rca w {r with code := code}
-/

/-
def Msg.benvAfterTransfer (msg : Msg) :
    Except (Benv × Tenv × String) Benv :=
  if msg.shouldTransferValue then do
    let benv ←
      (msg.benv.subBal msg.caller msg.value).toExcept
        ⟨msg.benv, msg.tenv, "AssertionError"⟩
    .ok <| benv.addBal msg.currentTarget msg.value
  else
    .ok msg.benv
-/



lemma transfer_of_benvAfterTransfer (msg : Msg) (benv : Benv)
    (should : msg.shouldTransferValue = true)
    (eq : msg.benvAfterTransfer = .ok benv) :
    Transfer msg.bal msg.caller msg.value msg.currentTarget benv.bal := by
  simp [Msg.benvAfterTransfer, if_pos should] at eq
  rcases of_bind_eq_ok eq with ⟨benv', sub, add⟩; clear eq
  rw [Option.toExcept_eq_ok] at sub; simp at add
  --apply transfer_of_subBal_of_addBal sub add
  have hh := Benv.transfer_of_subBal_of_addBal sub add--msg.benv benv' benv sub add
  simp [Transfer]
  sorry




lemma messageCall_of_processMessageCall
    (msg : Msg) (s : State) (mco : MsgCallOutput)
    (should : msg.shouldTransferValue = true)
    (h : processMessageCall false msg = .ok (s, mco)) :
    MessageCall
      msg.caller
      msg.currentTarget
      msg.benv.state.toWorld
      (mkResult s mco) := by

  simp [processMessageCall] at h

  by_cases h_target : msg.target = none
  · rw [if_pos h_target] at h


    by_cases h_account :
      accountHasCodeOrNonce msg.benv.state msg.currentTarget = true
        ∨ accountHasStorage msg.benv.state msg.currentTarget = true

    · rw [if_pos h_account] at h
      cases h
      simp [mkResult]
      have hh := @MessageCall.fail
      rw [Std.HashSet.toList_emptyWithCapacity]
      apply hh
    · rw [if_neg h_account] at h

      rw [not_or] at h_account
      rcases h_account with ⟨h_code_or_nonce, h_stor⟩
      rename' h => h'
      rcases of_bind_eq_ok h' with ⟨evm', h0, h⟩; clear h'
      rcases Except.of_bimap_eq_ok _ _ _ _ h0 with ⟨evm, h_evm, ⟨_⟩⟩
      clear h0
      by_cases h_error : (id evm).error = none
      · rw [if_pos h_error] at h
        rename' h => h'
        rcases of_bind_eq_ok h' with ⟨rc, h1, h⟩; clear h'
        -- simp only [] at h
        rcases h with ⟨hs, h_mco⟩

        rcases (of_processCreateMessage msg evm (msg.gas + 50) h_evm)
          with ⟨evm', lim', h_pm, h⟩

        by_cases h_isNone : evm'.error.isNone
        · rw [if_pos h_isNone] at h
          rcases h with ⟨evm'', h, h'⟩ | h
          · have should' :
                (processCreateMessageMsg msg).shouldTransferValue = true := by
              simp only [processCreateMessageMsg, Msg.withBenv]; exact should




            rcases of_processMessage _ _ _ should' h_isNone h_pm
              with ⟨le1024, msg', h_transfer, lim'', eq_lim', h_exec⟩

            have hh := @MessageCall.create























            sorry
          sorry
        · sorry
      · sorry
  · sorry


inductive MessageCallNT
    (sda : Adr) -- tx sender address
                 -- (always an EOA & never has contract code, per EIP-3607)
    (rca : Adr) -- tx receiver address
                 -- · for contract calls, rca = address of called contract
                 -- · for contract creations, rca = address of newly created contract
    (w : World)  -- initial world state
    : Result → Prop
  -- | create :
  --   ∀ gpr clv ctc bal r code,
  --     Transfer w.bal sda clv rca bal →
  --     w.code rca = [] →
  --     Exec
  --       { cta := rca, oga := sda, gpr := gpr, cld := [], cla := sda,
  --         clv := clv, code := ctc, exd := 1024, wup := true }
  --       --{ bal := bal, stor := w.stor, code := w.code, stk := [],
  --       --  mem := Memory.init, ret := [], dest := [] }
  --       (Desc.init bal w.stor w.code)
  --       0 r →
  --     Overwrite rca r.ret r.code code →
  --     MessageCall sda rca w {r with code := code}
  | call :
    ∀ gpr cld r,
      -- Transfer w.bal sda clv rca bal →
      Exec
        { cta := rca, oga := sda, gpr := gpr, cld := cld, cla := sda,
          clv := 0, code := w.code rca, exd := 1024, wup := true }
        -- { bal := bal, stor := w.stor, code := w.code, stk := []
        --   mem := Memory.init, ret := [], dest := []}
        (Desc.init w.bal w.stor w.code)
        0 r →
      MessageCallNT sda rca w r
  -- | pre :
  --   ∀ clv bal ret,
  --     Transfer w.bal sda clv rca bal →
  --     MessageCall sda rca w
  --       {bal := bal, stor := w.stor, code := w.code, ret := ret, dest := []}
  -- | fail : MessageCall sda rca w {w with ret := .nil, dest := []}


lemma of_processSystemTransaction
    (benv : Benv) (target : Adr) (code : ByteArray)
    (data : B8L) (st : State) (mco : MsgCallOutput)
    (stx : processSystemTransaction false benv target code data = .ok (st, mco)) :
    MessageCallNT
      systemAddress
      target
      benv.state.toWorld
      (mkResult st mco) := by
  sorry

-- def processUncheckedSystemTransaction
--   (vb : Bool) (benv : Benv) (target : Adr) (data : B8L) :
--   Except String (State × MsgCallOutput) := do
--   let systemContractCode : ByteArray := benv.state.getCode target
--   processSystemTransaction vb benv target systemContractCode data

lemma of_processUncheckedSystemTransaction
   (benv : Benv) (target : Adr) (data : B8L) (st : State) (mco : MsgCallOutput)
   (ustx : processUncheckedSystemTransaction false benv target data = .ok (st, mco)) :
   MessageCallNT
     systemAddress
     target
     benv.state.toWorld
     (mkResult st mco) := by

  _

#exit

/-
lemma transaction_of_processTransaction (benv : Benv) (bout : BlockOutput)
    (tx : Tx) (idx : Nat) (sf : State) (bout' : BlockOutput)
    (h : processTransaction false benv bout tx idx = .ok (sf, bout)) :
    ∃ x : Transaction benv.state.toWorld sf.toWorld, True := by
  rename' h => h'
  rcases of_bind_eq_ok h' with ⟨⟨intrinsicGas, calldataFloorGasCost⟩, h0, h⟩
  simp at h

#exit


  clear h'
  rename' h => h'
  rcases of_bind_eq_ok h' with ⟨
    ⟨sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed⟩,
    h1,
    h
  ⟩
  clear h'
  rename' h => h'
  rcases of_bind_eq_ok h' with ⟨s1, h2, h⟩
  clear h'
  rename' h => h'
  rcases of_bind_eq_ok h' with ⟨msg, h3, h⟩
  clear h'
  rename' h => h'
  rcases of_bind_eq_ok h' with ⟨⟨s1, mco⟩, h4, h⟩
  clear h'
  rename' h => h'
  rcases of_bind_eq_ok h' with ⟨refundCounter, h5, h⟩; clear h'
  rename' h => h'
  rcases of_bind_eq_ok h' with ⟨s2, h6, h⟩; clear h'
  simp at h6
  simp at h

-/



def Transition (c c' : BlockChain) : Prop :=
  ∃ b : Block, stateTransition false c b = Except.ok c'

-- structure Transaction (w w' : World) : Type where
--   (vs : B256) -- gas ultimately refunded to sender
--   (vv : B256) -- gas ultimately rewarded to validator
--   (vb : B256) -- gas ultimately burned
--   (nof : vs.toNat + vv.toNat + vb.toNat < 2 ^ 256)
--   (sda : Adr) -- tx sender address
--   (eoa : w.code sda = []) -- per EIP-3607
--   (bal : Balances) -- balances after upfront deduction
--   (decr : Decrease sda (vs + vv + vb) w.bal bal)
--   (le : vs + vv + vb ≤ w.bal sda)
--   (rca : Adr) -- tx receiver address
--   (r : Result) -- execution result
--   (act : MessageCall sda rca {w with bal := bal} r)
--   (bal' : Balances) -- balances after refund to sender
--   (incr : Increase sda vs r.bal bal')
--   (vla : Adr) -- validator address
--   (incr' : Increase vla vv bal' w'.bal)
--   (del : DeleteCodes r.dest r.code w'.code)
--   (stor : w'.stor = r.stor)

inductive Transactions : World → World → Type
  | refl {w : World} : Transactions w w
  | step {w1 w2 w3 : World}
      (tx : Transaction w1 w2)
      (txs : Transactions w2 w3) :
      Transactions w1 w3


def ProcessUncheckedSystemTransaction (w w' : World) : Prop := sorry
def ProcessWithdrawals (w w' : World) : Prop := sorry

structure ApplyBody (wInit wFinal : World) : Type where
  (wBeacon : World)
  (beacon : ProcessUncheckedSystemTransaction wInit wBeacon)
  (wHistory : World)
  (history : ProcessUncheckedSystemTransaction wBeacon wHistory)
  (wTxs : World)
  (txs : Transactions wHistory wTxs)
  (withdrawals : ProcessWithdrawals wTxs wFinal)

-- def applyBody
--   (vb : Bool) (benv : Benv) (txs : List (B8L ⊕ Tx)) (wds : List Withdrawal) :
--   Except String (State × BlockOutput) := do
--   let mut bout := BlockOutput.init
--   cprint vb "\n================================ BEACON ROOTS TX ================================\n"
--   let ⟨state, _⟩ ←
--     processUncheckedSystemTransaction false benv
--       beaconRootsAddress
--       benv.parentBeaconBlockRoot.toB8L
--   let mut benv : Benv := {benv with state := state}
--   cprint vb "\n================================ HISTORY STORAGE TX ================================\n"
--   let lastHash ←
--      benv.blockHashes.getLast?.toExcept "ERROR : block hashes is empty"
--   let ⟨state, _⟩ ←
--     processUncheckedSystemTransaction false benv
--       historyStorageAddress
--       lastHash.toB8L
--   benv := {benv with state := state}
--   cprint vb "\n================================ MAIN TXS ================================\n"
--   for ⟨i, tx⟩ in (← txs.mapM decodeTx).putIndex do
--     let ⟨state, bout'⟩ ← processTransaction vb benv bout tx i
--     benv := {benv with state := state}
--     bout := bout'
--   cprint vb s!"\nSTATE AFTER TEST TXS :"
--   cprint vb s!"{benv.state}"
--   cprint vb "\n================================ PROCESS WITHDRAWALS ================================\n"
--   let ⟨state, bout'⟩ :=
--     processWithdrawals benv bout wds
--   benv := {benv with state := state}
--   bout := bout'
--   cprint vb "\n================================ PROCESS GENERAL PURPOSE REQUESTS ================================\n"
--   processGeneralPurposeRequests vb benv bout


lemma applyBody_of_applyBody
    (ch ch' : BlockChain) (blk : Block) (st' : State) (bo' : BlockOutput)
    (app : applyBody false (initBenv ch blk.header) blk.txs blk.wds =
      Except.ok (st', bo')) :
    Nonempty (ApplyBody ch.toWorld st'.toWorld) := by
  rcases of_bind_eq_ok app with ⟨⟨_⟩, ⟨_⟩, beaconCont⟩
  clear app

  rcases of_bind_eq_ok beaconCont with ⟨⟨stBeacon, mo⟩, beacon, printCont⟩

  clear beaconCont

  rcases of_bind_eq_ok printCont with ⟨⟨_⟩, ⟨_⟩, hashCont⟩
  clear printCont;

  rcases of_bind_eq_ok hashCont with ⟨lastHash, eqLastHash, historyCont⟩


  clear hashCont eqLastHash
  rcases of_bind_eq_ok historyCont with ⟨⟨stHistory, moHistory⟩, history, cont⟩
  clear historyCont

  rcases of_bind_eq_ok cont with ⟨⟨_⟩, ⟨_⟩, decodeCont⟩
  clear cont
  rcases of_bind_eq_ok decodeCont with ⟨txs, decode, txsCont⟩
  clear decodeCont

  rcases of_bind_eq_ok txsCont with ⟨⟨benvTxs, boTxs⟩, applyTxs, printCont⟩
  clear txsCont
  rcases of_bind_eq_ok printCont with ⟨⟨_⟩, ⟨_⟩, printCont'⟩
  clear printCont
  rcases of_bind_eq_ok printCont' with ⟨⟨_⟩, ⟨_⟩, printCont⟩
  clear printCont'
  rcases of_bind_eq_ok printCont with ⟨⟨_⟩, ⟨_⟩, withdrawalCont⟩
  clear printCont


  rcases of_bind_eq_ok withdrawalCont with ⟨⟨_⟩, print, requests⟩

  clear withdrawalCont print
  have hh :=
    @ApplyBody.mk
      ch.toWorld
      st'.toWorld
      stBeacon.toWorld




































#exit
  --rcases of_bind_eq_ok cont with ⟨foo, bar, cont⟩

  rcases of_bind_eq_ok cont with ⟨foo', bar', cont'⟩
  clear cont



















































#exit

lemma transaction_of_transition (c c' : BlockChain)
    (tn : Transition c c') : ∃ tx : Transaction c.toWorld c'.toWorld, True := by

  rcases tn with ⟨b, h⟩
  rename' h => h'
  rcases of_bind_eq_ok h' with ⟨u, h0, h⟩
  clear h'
  rename' h => h'
  rcases of_bind_eq_ok h' with ⟨_, h1, h⟩
  clear h'
  rename' h => h'
  rcases of_bind_eq_ok h' with ⟨⟨s, bo⟩, h2, h⟩
  clear h'
  simp at h

  rename' h => h'
  rcases of_bind_eq_ok h' with ⟨_, h3, h⟩

  clear h'

  simp at h
  refine' ⟨_, .intro⟩

  rw [← h]; clear h


  simp [BlockChain.toWorld]
  sorry



































theorem transition_inv_solvent
    (wa : Adr) (c c' : BlockChain)
    (code_eq : some (c.state.getCode wa) = weth.compile <&> B8L.toByteArray)
    (solv : c.Solvent wa)
    (nof : SumNof c.state.bal)
    (tn : Transition c c') :
    c'.Solvent wa := by

  have prm : some (c.toWorld.code wa) = weth.compile := by
    simp [BlockChain.toWorld]
    rcases Option.eq_none_or_eq_some weth.compile with rw | ⟨cd, rw⟩
    · rw [rw] at code_eq; cases code_eq
    · have h : some (c.state.getCode wa).toList = weth.compile := by
        rw [rw] at code_eq;
        rw [rw, Option.some_inj.mp code_eq]
        apply congr_arg
        rw [toList_toByteArray]
      apply h
  have solv' : c.toWorld.Solvent wa := by
    simp [BlockChain.toWorld, World.Solvent]
    simp [BlockChain.Solvent, State.Solvent] at solv
    apply solv

  rcases transaction_of_transition _ _ tn with ⟨tx, _⟩

  have hh :=
    transaction_inv_solvent wa
      c.toWorld
      c'.toWorld
      prm
      solv'
      nof
      tx

  apply hh
