-- Solvent.lean : proof of solvency preservation for the ported WETH contract

import Blanc.Weth

def Storage.rest (s : Storage) : Addr → Word := s ∘ Addr.toWord

-- sum of all WETH balances, provided that s is the storage of WETH contract
def wbsum (s : Storage) : Nat := sum s.rest

def Storage.Solvent (s : Storage) (v : Word) (b : Word) : Prop :=
  wbsum s + v.toNat ≤ b.toNat

def World.Solvent (w : World) (a : Addr) : Prop :=
  Storage.Solvent (w.stor a) 0 (w.bal a)

def State.Solvent (s : State) (a : Addr) (e : Env) : Prop :=
  (e.cta = a → Storage.Solvent (s.stor a) e.clv (s.bal a)) ∧
  (e.cta ≠ a → Storage.Solvent (s.stor a) 0 (s.bal a))

def Result.Solvent (r : Result) (a : Addr) : Prop :=
  Storage.Solvent (r.stor a) 0 (r.bal a)

lemma solvent_of_same_stor {s s' : Storage} {v : Word} {b b' : Word} :
    s.Solvent v b → s = s' → b = b' → s'.Solvent v b' := by
  intros h0 h1 h2; rw [h1, h2] at h0; exact h0

lemma Rinst.inv_solvent {e s o s' wa}
    (h : Rinst.Run e s o s') (h_ne : e.cta ≠ wa) (h_sv : s.Solvent wa e) : s'.Solvent wa e := by
  simp [h_ne, State.Solvent] at h_sv
  simp [h_ne, State.Solvent]
  rw [← Rinst.inv_bal h, ← Rinst.inv_stor h h_ne]; exact h_sv

lemma transfer_inv_solvent {a wa} {v} {s : Storage} {b b' : Balances}
    (h_ne : a ≠ wa)
    (h_nof : SumNof b)
    (h_di : Transfer b a v wa b')
    (h_sv : s.Solvent 0 (b wa)) :
    s.Solvent v (b' wa) := by
  simp [Storage.Solvent]
  simp [Storage.Solvent] at h_sv
  rw [Bits.toNat_zero, Nat.add_zero] at h_sv
  have h_eq : b' wa = b wa + v := by
    rcases h_di with ⟨_, _, hd, hi⟩
    rw [(hd wa).right h_ne, (hi wa).left rfl]
  have h_nof : Nof  (b wa) v := by
    unfold Nof ; apply Nat.lt_of_le_of_lt _ h_nof
    apply le_trans _ <| add_le_sum_of_ne b h_ne.symm
    apply Nat.add_le_add (le_refl _)
    apply Bits.toNat_le_toNat _ _ h_di.left
  rw [h_eq, Bits.toNat_add_eq_of_nof _ _ h_nof]
  apply Nat.add_le_add h_sv (le_refl _)

lemma Xinst.prep_inv_solvent'
    {e s ep sp o rx sw wa}
    (ho : ¬ Xinst.isCall o)
    (h_cr : Xinst.Run' e s ep sp o rx sw)
    (ha : e.cta ≠ wa) (ha' : ep.cta ≠ wa)
    (h_sv : s.Solvent wa e) : sp.Solvent wa ep := by
  simp [State.Solvent, ha] at h_sv
  simp [State.Solvent, ha']
  cases h_cr <;> try {apply (ho cst).elim} <;>
  { simp [State.prep]
    rcases (asm : Transfer _ _ _ _ _) with ⟨_, b, hd, hi⟩
    rw [← (hi wa).right ha', ← (hd wa).right ha]
    apply h_sv }

lemma Xinst.prep_inv_solvent
    {e s ep sp o rx sw wa}
    (ho : Xinst.isCall o)
    (h_cr : Xinst.Run' e s ep sp o rx sw)
    (ha : e.cta ≠ wa) (h_nof : SumNof s.bal)
    (h_sv : s.Solvent wa e) : sp.Solvent wa ep := by
  have h_stor := (Xinst.prep_inv_stor h_cr).symm
  cases h_cr <;> try {cases ho} <;>
  try {simp [State.Solvent, Env.prep, State.prep, ha]; apply h_sv.right ha}
  simp [Env.prep, State.prep, State.Solvent]
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

structure Precond (wa : Addr) (e : Env) (s : State) : Prop :=
  (code : some (s.code wa) = Prog.compile weth)
  (nof : sum s.bal < 2 ^ 256)
  (solvent : s.Solvent wa e)

structure Postcond (wa : Addr) (e : Env) (r : Result) : Prop :=
  (code : some (r.code wa) = Prog.compile weth)
  (nof : sum r.bal < 2 ^ 256)
  (solvent : r.Solvent wa)

open Ninst

lemma of_push_addressMask {e} {s s' : State} {xs}
    (h_pfx : xs <<+ s.stk) (h_run : Line.Run e s pushAddressMask s') :
    (addressMask :: xs <<+ s'.stk) := by
  rw [addressMask_eq_shl, ← Bits.invert_zero_eq_max]
  revert s; simp only [pushAddressMask]; line_pref

lemma of_check_non_address {e} {s s' : State} {x xs}
    (h_pfx : x :: xs <<+ s.stk) (h_run : Line.Run e s checkNonAddress s') :
    ∃ y, (y :: xs <<+ s'.stk) ∧ (y = 0 ↔ ValidAddr x) := by
  rename' s' => s''; rcases_append
  rename Line.Run _ _ pushAddressMask _ => h_run
  rename Line.Run _ _ [_] _ => h_run'
  rename State => s'
  have h_pfx' := of_push_addressMask h_pfx h_run; clear h_pfx h_run s
  have h_pfx : Bits.and addressMask x :: xs <<+ s''.stk := by
    revert h_run'; revert s'; line_pref
  refine ⟨_, h_pfx, Iff.symm validAddr_iff⟩

lemma of_check_address {e} {s s' : State} {x xs} :
    (x :: xs <<+ s.stk) →
    Line.Run e s checkAddress s' →
    ∃ y, (y :: xs <<+ s'.stk) ∧ (y = 0 ↔ ¬ ValidAddr x) := by
  rename' s' => s''; intros h_pfx h_run;
  rcases of_run_append _ h_run with ⟨s', hs', h_run'⟩; clear h_run
  rcases of_check_non_address h_pfx hs'
    with ⟨y, h_pfx', h_iff⟩; clear h_pfx hs' s
  have h_pfx : (ite (y = 0) 1 0 :: xs <<+ s''.stk) := by
    revert h_run'; revert s'; line_pref
  refine' ⟨_, h_pfx, _⟩; rw [← h_iff]
  apply Ne.ite_eq_right_iff <| Ne.symm Bits.zero_ne_succ

lemma frel_to_address {w r} {f g : Storage} :
    ValidAddr w → Frel w r f g → Frel (toAddr w) r f.rest g.rest := by
  intros h0 h1 a; constructor <;> intro h3
  · apply (h1 <| Addr.toWord a).left; rw [← h3, toAddr_toWord_eq h0]
  · apply (h1 <| Addr.toWord a).right
    intro hc; apply h3; rw [hc, toAddr_toWord]

lemma incrAt_of_incrWbal {e s s' wad dst} (h_dst : ValidAddr dst)
    (h0 : Line.Run e s incrWbal s') (h1 : [wad, dst] <<+ s.stk) :
    Increase (toAddr dst) wad (s.stor e.cta).rest (s'.stor e.cta).rest := by
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
    rw [← ha, toAddr_toWord_eq h_dst] at h5
    apply h5
  simp [Storage.rest]
  rw [← ha, toAddr_toWord_eq h_dst, h5]

lemma sstore_inv_stor_rest {x xs} {e} {s s' : State} :
  ¬ ValidAddr x →
  (x :: xs <<+ s.stk) →
  State.Sstore e s s' →
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
  apply ((frel_of_sstore h_sstore h_pfx e.cta).left rfl a.toWord).right
  intro hc; apply h_nv
  refine ⟨a, hc.symm⟩

lemma of_transferFromUpdateSbal {e s₀ sₙ} {sbal wad src}
    (h_src : ValidAddr src) (h_sbal : sbal = s₀.stor e.cta src)
    (h_le : wad ≤ sbal) (hp₀ : [sbal, wad, wad, src] <<+ s₀.stk) :
    Line.Run e s₀ transferFromUpdateSbal sₙ →
    ( Decrease (toAddr src) wad (s₀.stor e.cta).rest (sₙ.stor e.cta).rest ∧
      wad ≤ (s₀.stor e.cta).rest (toAddr src) ) := by
  lexen 2; lstor; intro h₂
  have hp₁ : [src, sbal - wad, wad, src] <<+ s₁.stk := by lpfx
  have h_ow : Overwrite src (sbal - wad) (s₁.stor e.cta) (sₙ.stor e.cta) :=
    (frel_of_sstore (of_run_singleton' h₂) hp₁ e.cta).left rfl
  simp [Storage.rest]; constructor
  · intro a; constructor <;> intro ha
    · rw [← ha]; simp
      rw [toAddr_toWord_eq h_src, ← h_sbal]
      apply (h_ow src).left rfl
    · apply (h_ow <| Addr.toWord a).right
      intro hc; apply ha; rw [← toAddr_toWord a, hc]
  · rw [toAddr_toWord_eq h_src, ← h_sbal]; exact h_le

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
    have hs₄ : [~ amnt =? 0, amnt, wad, hash] <<+ s₄.stk := by lpfx
    lstor; cstate s₃; apply branch_elim' (_ = _) hs₄ <;> intro h
    · intro h₅; rw [Func.of_inv State.stor Result.stor _ h₅]; prog_inv
    · clear h; pexen 4;
      have hs₅ : [amnt <? wad, amnt, wad, hash] <<+ s₅.stk := by lpfx
      lstor; cstate s₄; apply rev_branch_elim' (_ = _) hs₅
      intro h; clear h; pexen 3
      have hs₆ : [hash, amnt - wad] <<+ s₆.stk := by lpfx
      lstor; cstate s₅; pexen 1; intro h₈
      rw [sstore_inv_stor_rest h_hash hs₆ <| of_run_singleton' h₇]
      rw [Func.of_inv State.stor Result.stor _ h₈]; prog_inv
  · intro _ h; rw [Func.of_inv State.stor Result.stor _ h]; prog_inv

lemma transfer_of_transferFrom {e : Env} {s : State} {r : Result} :
    Func.Run c e s transferFrom r →
    ∃ (x : Word) (a a' : Addr),
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
    rw [← Bits.not_lt]; apply (Ne.ite_eq_right_iff Bits.zero_ne_succ.symm).mp h_eq
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
  refine' ⟨wad, toAddr src, toAddr dst, h_le', (s₁₀.stor e.cta).rest, h_dec, _⟩
  have h_eq : (s₁₁.stor e.cta).rest = (r.stor e.cta).rest := by
    revert h₁₂; cstate s₁₀; pexec transferFromLog
    have hp₁₂ : [wad, src] <<+ s₁₂.stk := by lpfx
    lstor; apply updateAllowance_inv_stor_rest hp₁₂
  rw [← h_eq]; apply incrAt_of_incrWbal h_dst h₁₁ <| pref_trans ⟨_, rfl⟩ hp₁₀

theorem of_transferTestDst {e : Env} {s s' : State} :
  Line.Run e s transferTestDst s' →
  ∃ na_dst dst,
    ([na_dst, dst] <<+ s'.stk) ∧
    (na_dst = 0 ↔ ValidAddr dst) := by
  rename' s => s₀; lexec (arg 0)
  rcases Stack.push_of_cdl h₁ with ⟨dst, h_push⟩; clear h₁
  have hp₁ : [dst] <<+ s₁.stk := pref_of_split h_push
  clear h_push s₀; lexec [dup 0]
  have hp₂ : [dst, dst] <<+ s₂.stk := by lpfx
  clear hp₁ h₂ s₁; intro h;
  rcases of_check_non_address hp₂ h
    with ⟨na_dst, h_pfx, h_iff⟩; clear h hp₂
  refine ⟨_, _, h_pfx, h_iff⟩

lemma Bits.zero_ne_one {n} : (0 : Bits (n + 1)) ≠ (1 : Bits (n + 1)) := by
  apply Bits.zero_ne_succ

theorem of_transferTestLt {e s s'} {dst} (h_stk : [dst] <<+ s.stk) :
    Line.Run e s transferTestLt s' →
    ∃ lt? caller wad,
      ([lt?, caller, s.stor e.cta caller - wad, wad, dst] <<+ s'.stk) ∧
      (lt? = 0 ↔ wad ≤ s.stor e.cta caller) ∧
      ValidAddr caller := by
  rename' s => s₀, h_stk => hp₀; lexec (arg 1)
  rcases Stack.push_of_cdl h₁ with ⟨wad, h_push⟩
  have hp₁ : [wad, dst] <<+ s₁.stk := append_pref h_push hp₀
  lstor; cstate s₀; lexec [_, _]
  have hp₂ : [Addr.toWord e.cla, Addr.toWord e.cla, wad, dst] <<+ s₂.stk := by lpfx
  lstor; cstate s₁; lexec [_]
  have hp₃ : [s₂.stor e.cta (Addr.toWord e.cla), Addr.toWord e.cla, wad, dst] <<+ s₃.stk :=
    prefix_of_sload (opRun_of_instRun <| of_run_singleton h₃) hp₂
  lstor; cstate s₂; intro h
  have hp' :
    [ if (s₃.stor e.cta (Addr.toWord e.cla) < wad) then 1 else 0, Addr.toWord e.cla,
      s₃.stor e.cta (Addr.toWord e.cla) - wad, wad, dst ] <<+ s'.stk := by lpfx
  lstor;
  refine'
    ⟨ if (s'.stor e.cta (Addr.toWord e.cla) < wad) then 1 else 0,
      Addr.toWord e.cla, wad, hp', _, validAddr_toWord _ ⟩
  rw [Ne.ite_eq_right_iff Bits.zero_ne_one.symm, Bits.not_lt]


theorem transfer_of_transfer {e : Env} {s : State} {r : Result} :
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
    ⟨wad, toAddr caller, toAddr dst, _, (s₅.stor e.cta).rest, _, _ ⟩
  · simp [Storage.rest]; rw [toAddr_toWord_eq h_caller]; exact h_le
  · apply frel_of_frel _ <| frel_to_address h_caller <| (hs₅ e.cta).left rfl
    simp [Storage.rest, toAddr_toWord_eq h_caller]
  · revert h_run'; pexec incrWbal; intro hr
    have h : s₆.stor = r.stor := by apply Func.of_inv _ _ _ hr; prog_inv
    rw [← h]; apply incrAt_of_incrWbal h_dst h₆ hp₅

lemma of_prepApprove {e s s'} :
    Line.Run e s prepApprove s' →
    ∃ vx x y, ([vx, x, y] <<+ s'.stk) ∧ (vx = 0 ↔ ¬ ValidAddr x) := by
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

lemma transferFrom_inv_bal : Func.Inv State.bal Result.bal transferFrom := by prog_inv

lemma transfer_inv_bal : Func.Inv State.bal Result.bal transfer := by prog_inv

lemma solvent_zero_of_solvent {s : Storage} {v : Word} {b : Word}
    (h : s.Solvent v b) : s.Solvent 0 b := by
  simp [Storage.Solvent, Bits.toNat_zero]
  apply Nat.le_trans (Nat.le_add_right _ _) h

lemma storage_solvent_zero_of_state_solvent {s : State} {a e}
    (h : s.Solvent a e) : (s.stor a).Solvent 0 (s.bal a) := by
  by_cases h' : e.cta = a <;> simp [State.Solvent, h'] at h
  · apply solvent_zero_of_solvent h
  · exact h

lemma result_solvent_of_state_solvent' {e : Env} {s : State} {r : Result}
    (h_sv : s.Solvent e.cta e)
    (h_sum : wbsum (s.stor e.cta) = wbsum (r.stor e.cta))
    (h_bal : s.bal e.cta = r.bal e.cta) : r.Solvent e.cta := by
  apply @solvent_zero_of_solvent _ e.clv
  simp [State.Solvent, Result.Solvent, Storage.Solvent] at *
  rw [← h_sum, ← h_bal]; exact h_sv

lemma result_solvent_of_state_solvent {e : Env} {s : State} {r : Result} :
    (s.stor e.cta).rest = (r.stor e.cta).rest →
      s.bal e.cta = r.bal e.cta →
      s.Solvent e.cta e → r.Solvent e.cta := by
  simp [State.Solvent, Result.Solvent]
  intros h_wbsum h_bal h_solvent
  apply @solvent_zero_of_solvent _ e.clv
  simp [Storage.Solvent, wbsum]
  rw [← h_wbsum, ← h_bal]; exact h_solvent

lemma approve_inv_bal : Func.Inv State.bal Result.bal approve := by prog_inv

theorem approve_inv_solvent {e s r} (h : Func.Run c e s approve r)
    (h' : s.Solvent e.cta e) : r.Solvent e.cta := by
  apply result_solvent_of_state_solvent (approve_inv_wbal h) _ h'
  rw [approve_inv_bal h]

lemma nof_of_solvent {s a e} (h : State.Solvent s a e) : SumNof (s.stor a).rest := by
  apply lt_of_le_of_lt _ (Bits.toNat_lt_pow <| s.bal a)
  simp [State.Solvent, Storage.Solvent] at h
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
  `(tactic| simp [State.Solvent]; intro h h';
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

theorem wbsum_after_deposit {e : Env} {s : State} {r}
    (h_nof : (wbsum (s.stor e.cta)) + e.clv.toNat < 2 ^ 256) :
    Func.Run c e s deposit r →
    wbsum (s.stor e.cta) + e.clv.toNat = wbsum (r.stor e.cta) := by
  have hp0 : [] <<+ s.stk := nil_pref; pexen 1
  have hp₁ : [Addr.toWord e.cla] <<+ s₁.stk := by lpfx
  lstor; cstate s; pexen 1
  rcases prefix_of_sload' (of_run_singleton' h₂) hp₁ with ⟨cbal, h_stk, h_cbal⟩
  lstor; cstate s₁; pexen 3
  have hp₃ : [Addr.toWord e.cla, e.clv + cbal] <<+ s₃.stk := by lpfx
  lstor; cstate s₂; pexen 1; intro h₅
  have h_stor : s₄.stor = r.stor := by apply Func.of_inv _ _ _ h₅; prog_inv
  rw [← h_stor]; clear h_stor h₅
  have h_incr : Increase e.cla e.clv (s₃.stor e.cta).rest (s₄.stor e.cta).rest := by
    have h := (frel_of_sstore (of_run_singleton' h₄) hp₃ e.cta).left rfl
    intro x; constructor <;> intro hx
    · simp [Storage.rest]; rw [← hx, ← h_cbal, Bits.add_comm]
      exact (h (Addr.toWord e.cla)).left rfl
    · apply (h (Addr.toWord x)).right <| mt (@Addr.toWord_inj e.cla x) hx
  have h_nof' : Nof (Storage.rest (s₃.stor e.cta) e.cla) e.clv := by
    simp only [Nof ]; apply lt_of_le_of_lt _ h_nof
    rw [Nat.add_le_add_iff_right]; apply le_sum
  exact sum_add_assoc h_incr h_nof'

lemma solvent_zero_iff {s b} : Storage.Solvent s 0 b ↔ wbsum s ≤ b.toNat := by
  simp [Storage.Solvent, wbsum, Bits.toNat_zero]

theorem deposit_inv_solvent {e s r} :
    Func.Run c e s deposit r → s.Solvent e.cta e → r.Solvent e.cta := by
  intros h_run h_solvent
  simp [Result.Solvent]
  have h_bal : s.bal = r.bal := by
    apply Func.of_inv _ _ _ h_run; prog_inv
  rw [solvent_zero_iff, ← h_bal]
  simp [State.Solvent, Storage.Solvent] at h_solvent
  have h_lt : wbsum (s.stor e.cta) + Bits.toNat e.clv < 2 ^ 256 :=
    lt_of_le_of_lt h_solvent (Bits.toNat_lt_pow _)
  rw [← wbsum_after_deposit h_lt h_run]
  apply h_solvent

lemma of_withdrawLoadCheck {e : Env} {s s'} (h : Line.Run e s withdrawLoadCheck s') :
    s.bal = s'.bal ∧
    s.stor = s'.stor ∧
    s.code = s'.code ∧
    ∃ wad cbal,
      ([cbal <? wad, cbal, wad, wad] <<+ s'.stk) ∧
      (cbal = s'.stor e.cta (Addr.toWord e.cla)) := by
  refine' ⟨_, _, _, _⟩ <;> try {linv; done}; revert h
  apply cdl_append_elim (∃ _, _); intro wad; lexen 3
  have hs₀ : [] <<+ s.stk := nil_pref
  have hs₁ : [Addr.toWord e.cla, wad, wad] <<+ s₁.stk := by lpfx
  cstate s; lexen 1
  rcases prefix_of_sload' (of_run_singleton' h₂) hs₁ with ⟨cbal, hs₂, h_cbal⟩
  lstor; cstate s₁; intro h₃
  have hs₃ : [cbal <? wad, cbal, wad, wad] <<+ s'.stk := by lpfx
  lstor; refine ⟨wad, cbal, hs₃, h_cbal⟩

lemma precond_of_precond {a e} {s s' : State}
    (h : Precond a e s) (h_bal : s.bal = s'.bal)
    (h_stor : s.stor = s'.stor) (h_code : s.code = s'.code) :
    Precond a e s' := by
  refine' ⟨_, _, _⟩
  · rw [← h_code]; apply h.code
  · rw [← h_bal]; apply h.nof
  · simp [State.Solvent]; rw [← h_stor, ← h_bal]; apply h.solvent

lemma solvent_of_callPrep {e s ep sp r sw send_gas send_amnt}
    (cr : Xinst.Run' e s ep sp .call r sw)
    (h_stk : [send_gas, (Addr.toWord e.cla), send_amnt] <<+ s.stk)
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
    simp [Storage.Solvent, Bits.toNat_zero] at h_sv
    rw [Bits.toNat_sub_eq_of_le _ _ h_le] at h_sv
    rw [← (hd e.cta).left rfl]
    simp [Storage.Solvent, Bits.sub_add_cancel]
    rw [← Nat.sub_add_cancel (Bits.toNat_le_toNat _ _ h_le), h_clv]
    apply Nat.add_le_add_right h_sv send_amnt.toNat
  · rw [← (hi e.cta).right h_cta, ← (hd e.cta).left rfl]; exact h_sv

def Exec.InvDepth (k : Nat) (ca : Addr) (p : Prog)
    (σ : Env → State → Prop) (ρ : Env → Result → Prop) : Prop :=
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
    simp [Storage.Solvent, Bits.toNat_zero] at h_sv
    rw [Bits.toNat_sub_eq_of_le _ _ h_le] at h_sv
    apply lt_of_le_of_lt <| Nat.add_le_add_right h_sv wad.toNat
    rw [Nat.sub_add_cancel <| Bits.toNat_le_toNat _ _ h_le]
    apply Bits.toNat_lt_pow
  lexen 7
  have hs₁ :
    [ Bytes.toBits 32 [Ox x5 x2, Ox x0 x8],
      Addr.toWord e.cla, wad, 0, 0, 0, 0 ] <<+ s₁.stk := by lpfx
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
    have h_sv : State.Solvent sp e.cta ep := by
      have hs : [ Bytes.toBits 32 [Ox x5 x2, Ox x0 x8], Addr.toWord e.cla, wad] <<+ s₁.stk := by
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
    rw [Bits.toNat_sub_eq_of_le _ _ h_le]; apply Nat.sub_le

lemma solvent_of_withdraw_update_bal' {e : Env} {s s'} {lt? cbal wad}
    (h_pc : Precond e.cta e s)
    (h_stk : [lt?, cbal, wad, wad] <<+ s.stk)
    (h_cbal : cbal = s.stor e.cta (Addr.toWord e.cla))
    (h_le : wad ≤ cbal)
    (h_run : Line.Run e s [pop, sub, caller, sstore] s') :
    wad ≤ s'.bal e.cta ∧
    Storage.Solvent (s'.stor e.cta) 0 (s'.bal e.cta - wad) := by
  revert h_run; lexen 3
  have h_pc' : Precond e.cta e s₁ := by
    apply precond_of_precond h_pc <;> (apply Line.of_inv _ _ h₁; line_inv)
  have hp₁ : [Addr.toWord e.cla, cbal - wad, wad] <<+ s₁.stk := by lpfx
  lstor; cstate s; intro h₂
  have h_dec : Decrease e.cla wad (s₁.stor e.cta).rest (s'.stor e.cta).rest := by
    have h := (frel_of_sstore (of_run_singleton' h₂) hp₁ e.cta).left rfl
    intro a; constructor <;> (intro ha; simp [Storage.rest])
    · rw [← ha, ← h_cbal]; apply (h (Addr.toWord e.cla)).left rfl
    · apply (h (Addr.toWord a)).right <| mt Addr.toWord_inj ha
  have h_eq : wbsum (s₁.stor e.cta) - wad.toNat = wbsum (s'.stor e.cta) := by
    apply sum_sub_assoc h_dec
    simp [Storage.rest]; rw [← h_cbal]; exact h_le
  clear h_dec
  have h_le' : wad.toNat ≤ wbsum (s₁.stor e.cta) := by
    apply Nat.le_trans (Bits.toNat_le_toNat _ _ h_le); rw [h_cbal]
    apply @le_sum _ _ (s₁.stor e.cta).rest
  have h_bal : s₁.bal = s'.bal := by apply Line.of_inv _ _ h₂; line_inv
  rw [← h_bal]
  have h_le'' : wad.toNat ≤ (s₁.bal e.cta).toNat := by
    apply le_trans h_le' <| le_trans _ <| h_pc'.solvent.left rfl
    apply Nat.le_add_right
  have h_le''' := Bits.of_toNat_le_toNat h_le''
  refine' ⟨h_le''', _⟩
  · simp [Storage.Solvent, Bits.toNat_zero]
    rw [Bits.toNat_sub_eq_of_le _ _ h_le''', ← h_eq, Nat.sub_le_sub_iff_right h_le'']
    have h' := solvent_zero_of_solvent <| (Precond.solvent asm).left rfl
    simp [Storage.Solvent, Bits.toNat_zero] at h'; exact h'

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
    rw [← Bits.not_lt];
    apply (Ne.ite_eq_right_iff <| Ne.symm Bits.zero_ne_one).mp h_eq
  clear h_eq; pexen 4
  rcases solvent_of_withdraw_update_bal' h_pc hp₁ h_cbal h_wad h₂ with ⟨h_le, h_sv⟩
  clear h_cbal h_wad
  have h_code : some (s₂.code e.cta) = Prog.compile weth := by
    rw [← Line.of_inv State.code (by line_inv) h₂]; apply h_pc.code
  have h_nof : sum s₂.bal < 2 ^ 256 := by
    rw [← Line.of_inv State.bal (by line_inv) h₂]; apply h_pc.nof
  have hp₂ : [wad] <<+ s₂.stk := by lpfx
  cstate s₁; pexec sendToCaller; intro h₄
  unfold Result.Solvent
  rw [← Func.of_inv State.stor Result.stor (by prog_inv) h₄]
  rw [← Func.of_inv State.bal Result.bal (by prog_inv) h₄]
  apply of_send_to_caller' ih hp₂ h_code h_nof h_le h_sv h₃

lemma Line.inv_solvent {e e' s l s' a}
    (h_bal : Line.Inv State.bal l) (h_stor : Line.Inv State.stor l)
    (h_sv : State.Solvent s a e) (h_run : Line.Run e' s l s') : State.Solvent s' a e := by
  unfold State.Solvent; rw [← h_bal h_run, ← h_stor h_run]; exact h_sv

lemma run_inv_cond (f : Func)
    (h : ∀ {e : Env} {s : State} {r : Result}, Func.Run c e s f r →
       State.Solvent s e.cta e → Result.Solvent r e.cta) :
    ∀ {e : Env} {s : State} {r : Result}, Func.Run c e s f r →
      Precond e.cta e s → Postcond e.cta e r := by
  intro e s r h_run h_pc
  refine' ⟨_, Func.inv_nof h_run h_pc.nof, h h_run h_pc.solvent⟩
  have hcode : s.code e.cta ≠ [] := by
    intro h; apply @Prog.compile_ne_nil weth; rw [← h_pc.code, h]
  rw [← Func.inv_code h_run hcode]; exact h_pc.code

lemma weth_inv' {e s r}
    (hs : Precond e.cta e s)
    (ih : Exec.InvDepth e.exd e.cta weth (Precond e.cta) (Postcond e.cta)) :
    Func.Run (weth.main :: weth.aux) e s (Func.mainWith 1 wethTree) r →
    Postcond e.cta e r := by
  pexec fsig
  have hs₁ : Precond e.cta e s₁ := by
    refine' ⟨_, _, _⟩
    · rw [← Line.of_inv State.code (by line_inv) h₁, hs.code]
    · rw [← Line.of_inv State.bal (by line_inv) h₁]; exact hs.nof
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
    · rw [← Line.of_inv State.code (by line_inv) h_run]; apply h_pc.code
    · rw [← Line.of_inv State.bal (by line_inv) h_run]; apply h_pc.nof
    · apply Line.inv_solvent _ _ h_pc.solvent h_run <;> line_inv
  · intro e s x s' h_pc h_inv h_run;
    refine' ⟨⟨_, _, _⟩, h_inv⟩
    · rw [← Line.of_inv State.code (by line_inv) h_run]; apply h_pc.code
    · rw [← Line.of_inv State.bal (by line_inv) h_run]; apply h_pc.nof
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
  simp [h_ne, State.Solvent];
  cases h <;> {simp [State.wrap, State.wrap']; apply h_sv}

theorem weth_inv_solvent (wa : Addr) :
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
    intro h_inv h_pc; apply weth_inv' h_pc h_inv asm
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
        have h := State.Rel.bal asm
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
        simp [State.Rels.dft] at *; unfold State.Solvent
        rw [← fail_inv_bal asm, ← fail_inv_stor asm]; exact h_sv
      | jump =>
        have h := Jinst.inv_stor asm
        have h' := Jinst.inv_bal asm
        unfold State.Solvent; rw [← h, ← h']; exact h_sv
      | push =>
        have h := State.Rel.bal asm
        have h' := State.Rel.stor asm
        unfold State.Solvent; rw [← h, ← h']; exact h_sv
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
          have h := h_pc.solvent; simp [State.Solvent, h_ne] at h; exact h
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
              have hle : Nof  (s.bal wa) (s.bal e.cta) :=
                lt_of_le_of_lt (add_le_sum_of_ne s.bal h_ne.symm) h_pc.nof
              rw [h_rw, Bits.toNat_add_eq_of_nof _ _ hle]; apply Nat.le_add_right
            · rw [(hd wa).right h_ne, (hi wa).right ha]
          | invalid => cases h_run
        unfold Result.Solvent; rw [← Linst.inv_stor asm]
        apply le_trans h_sv h_le
    · refine' ⟨h_pc.code, h_pc.nof, _⟩
      have h := h_pc.solvent
      simp [State.Solvent, h_ne] at h
      apply h

lemma transact_inv_solvent {ST RT w r wa}
    (h : Transact ST RT w r) (h_wa : ST ≠ wa)
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
      · simp only []
        rw [← transfer_inv_sum h_nof h_di]
        exact h_nof
      · simp only [State.Solvent]
        intro hc; cases h_ne hc
      · intro h; clear h; simp only [State.Solvent]
        rw [← h_eq]; apply h_wb
  | call gpr cld clv bal _ h_di cr =>
    apply (@weth_inv_solvent wa _ _ _ cr h_code _ _).solvent
    · simp; intro h_eq; rw [h_eq]; apply h_code
    · refine' ⟨h_code, _, _, _⟩
      · simp only []
        rw [← transfer_inv_sum h_nof h_di]
        exact h_nof
      · simp only [State.Solvent]; intro h_eq
        have h_eq : w.bal wa + clv = bal wa := by
          rcases h_di with ⟨_, bal', hd, hi⟩
          rw [(hd wa).right h_wa, ← (hi wa).left h_eq]
        have h_nof : Nof  (w.bal wa) clv := by
          apply lt_of_le_of_lt _ <| h_nof
          apply le_trans _ <| add_le_sum_of_ne w.bal h_wa
          rw [Nat.add_comm, Nat.add_le_add_iff_right]
          apply Bits.toNat_le_toNat
          rcases h_di with ⟨h_le, _⟩; exact h_le
        rw [← h_eq]; simp [Storage.Solvent]
        rw [Bits.toNat_add_eq_of_nof _ _ h_nof, Nat.add_le_add_iff_right]
        simp [World.Solvent, Storage.Solvent, Bits.toNat_zero] at h_wb
        apply h_wb
      · simp only [State.Solvent]; intro h_ne
        have h_eq : w.bal wa = bal wa := by
          rcases h_di with ⟨_, bal', hd, hi⟩
          apply Eq.trans ((hd wa).right h_wa) ((hi wa).right h_ne)
        rw [← h_eq]; apply h_wb
  | pre clv bal ret h_di =>
    apply le_trans h_wb
    rcases of_nof_of_transfer h_nof h_di with ⟨bal', hd, hi, h_nof'⟩
    rw [(hd wa).right h_wa]
    apply Bits.toNat_le_toNat _ _ <| le_of_increase hi h_nof' _
  | fail => apply h_wb

theorem transact_inv_sum_bal {sda rca w r} (h : Transact sda rca w r)
    (h' : SumNof w.bal) : sum w.bal = sum r.bal := by
  cases h with
  | create =>
    rename Exec _ _ _ _ => cr
    rw [transfer_inv_sum h' asm, Exec.inv_sum_bal cr _]
    apply transfer_inv_nof asm h'
  | call =>
    rename Exec _ _ _ _ => cr
    rw [transfer_inv_sum h' asm, Exec.inv_sum_bal cr _]
    apply transfer_inv_nof asm h'
  | pre => rw [transfer_inv_sum h' asm]
  | fail => rfl

theorem transaction_inv_solvent
    (wa : Addr) (w w' : World)
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
    have h_nof' : Nof tx.vs tx.vv :=
      lt_of_le_of_lt (Nat.le_add_right _ _) tx.nof
    have h_nof'' : Nof  (tx.vs + tx.vv) tx.vb := by
      simp only [Nof ]; rw [Bits.toNat_add_eq_of_nof _ _ h_nof']; apply tx.nof
    have h_eq :
      (tx.vs + tx.vv + tx.vb).toNat =
        tx.vs.toNat + tx.vv.toNat + tx.vb.toNat := by
      rw [Bits.toNat_add_eq_of_nof _ _ h_nof'', Bits.toNat_add_eq_of_nof _ _ h_nof']
    have h_eq' :
      sum tx.bal + tx.vs.toNat + tx.vv.toNat + tx.vb.toNat = sum w.bal := by
      rw [Nat.add_assoc (sum _), Nat.add_assoc, ← h_eq]
      have h_le : Bits.toNat (tx.vs + tx.vv + tx.vb) ≤ sum w.bal := by
        apply le_trans <| Bits.toNat_le_toNat _ _ <| tx.le
        apply le_sum
      rw [← sum_sub_assoc tx.decr tx.le, Nat.sub_add_cancel h_le]
    rw [h_eq']; apply h_bal
  have h_nof : SumNof tx.bal := by
    apply lt_of_le_of_lt (le_trans _ <| Nat.le_add_right _ _) h_nof_bal
    apply le_trans (Nat.le_add_right _ _) <| Nat.le_add_right _ _
  have h_sv : Storage.Solvent (w.stor wa) 0 (tx.bal wa) := by
    rw [← (tx.decr wa).right h_ne]; apply h_solv
  have hq := transact_inv_solvent tx.act h_ne h_nof h_sv h_code
  have h_nof' : Nof (tx.r.bal tx.sda) tx.vs := by
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
  apply Bits.toNat_le_toNat
  have h_nof'' : Nof (tx.bal' tx.vla) tx.vv := by
    simp only [Nof ]
    rw [ transact_inv_sum_bal tx.act h_nof,
         sum_add_assoc tx.incr h_nof' ] at h_nof_bal
    apply lt_of_le_of_lt _ h_nof_bal
    apply le_trans _ <| Nat.le_add_right _ _
    apply Nat.add_le_add_right _ _
    apply le_sum
  apply le_of_increase tx.incr' h_nof''
