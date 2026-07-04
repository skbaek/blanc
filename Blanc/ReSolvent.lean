-- Solvent.lean : proof of solvency for WETH implementation


import Blanc.ReWeth
import Blanc.ReCommon
import Std.Data.TreeMap.Lemmas


def Stor.rest (s : Stor) : Adr → B256 := s.get ∘ Adr.toB256

-- sum of all WETH balances, provided that s is the storage of WETH contract
def wbsum (s : Stor) : Nat := sum s.rest

def Stor.Solvent (s : Stor) (v : B256) (b : B256) : Prop :=
  wbsum s + v.toNat ≤ b.toNat

def State.Solvent (w : State) (a : Adr) : Prop :=
  Stor.Solvent (w.getStor a) 0 (w.bal a)

def Devm.PreSolvent (devm : Devm) (a : Adr) (sevm : Sevm) : Prop :=
  (sevm.currentTarget = a → Stor.Solvent (devm.getStor a) sevm.value (devm.getBal a)) ∧
  (sevm.currentTarget ≠ a → Stor.Solvent (devm.getStor a) 0 (devm.getBal a))

def Devm.PostSolvent (devm : Devm) (a : Adr) : Prop :=
  Stor.Solvent (devm.getStor a) 0 (devm.getBal a)

lemma solvent_of_same_stor {s s' : Stor} {v : B256} {b b' : B256} :
    Stor.Solvent s v b → s = s' → b = b' → Stor.Solvent s' v b' := by
  intros h0 h1 h2; rw [h1, h2] at h0; exact h0

lemma solvent_zero_of_solvent {s : Stor} {v : B256} {b : B256}
    (h : Stor.Solvent s v b) : Stor.Solvent s 0 b := by
  simp [Stor.Solvent] at h
  simp [Stor.Solvent, B256.toNat_zero]
  omega

structure Precond (wa : Adr) (sevm : Sevm) (devm : Devm) : Prop where
  (nof : sum devm.getBal < 2 ^ 256)
  (solvent : devm.PreSolvent wa sevm)

structure Postcond (wa : Adr) (sevm : Sevm) (devm : Devm) : Prop where
  (nof : sum devm.getBal < 2 ^ 256)
  (solvent : devm.PostSolvent wa)

lemma postcond_of_precond {wa : Adr} {sevm : Sevm} {devm : Devm}
    (h : Precond wa sevm devm) : Postcond wa sevm devm := by
  constructor
  · exact h.nof
  · unfold Devm.PostSolvent
    have h_solv := h.solvent
    unfold Devm.PreSolvent at h_solv
    by_cases hc : sevm.currentTarget = wa
    · have h1 := h_solv.left hc
      unfold Stor.Solvent at h1
      unfold Stor.Solvent
      rw [B256.toNat_zero] at *
      omega
    · exact h_solv.right hc

lemma Precond.state_eq {wa sevm devm devm'}
    (h_pc : Precond wa sevm devm) (h_eq : devm'.state = devm.state) :
    Precond wa sevm devm' := by
  cases h_pc with
  | mk h_nof h_solv =>
    have h_bal : devm'.getBal = devm.getBal := by
      funext a; simp [Devm.getBal, Devm.getAcct]; rw [h_eq]
    have h_stor : ∀ a, devm'.getStor a = devm.getStor a := by
      intro a; simp [Devm.getStor, Devm.getAcct]; rw [h_eq]
    constructor
    · rw [h_bal]; exact h_nof
    · cases h_solv with
      | intro hl hr =>
        constructor
        · intro h; rw [h_bal, h_stor wa]; exact hl h
        · intro h; rw [h_bal, h_stor wa]; exact hr h

def Inv0 {ξ} (r : Devm → ξ) (f : Devm → Except (String × Devm) Devm) : Prop :=
    ∀ {pre post}, f pre = .ok post → r pre = r post

def Inv1 {ξ υ} (r : Devm → ξ) (f : Devm → Except (String × Devm) (υ × Devm)) : Prop :=
    ∀ {pre y post}, f pre = .ok ⟨y, post⟩ → r pre = r post

class Hinv0 {ξ} (r : Devm → ξ) (f : Devm → Except (String × Devm) Devm) where
  (inv : Inv0 r f)

class Hinv1 {ξ υ} (r : Devm → ξ)
    (f : Devm → Except (String × Devm) (υ × Devm)) where
  (inv : Inv1 r f)

def Exec.InvDepth (k : Nat) (ca : Adr) (p : Prog)
  (σ : Sevm → Devm → Prop) (ρ : Sevm → Devm → Prop) : Prop :=
  ForallDeeperAt k ca p (λ _ sevm pre exn _ => σ sevm pre → ifOk (ρ sevm) exn)

lemma Line.inv_solvent {e e' s l s' a}
    (h_bal : Line.Inv Devm.getBal l) (h_stor : Line.Inv Devm.getStor l)
    (h_sv : Devm.PreSolvent s a e) (h_run : Line.Run e' s l s') : Devm.PreSolvent s' a e := by
  unfold Devm.PreSolvent; rw [← h_bal h_run, ← h_stor h_run]; exact h_sv

instance {x} : Ninst.Hinv Devm.getBal (Ninst.pushB256 x) := ⟨by
  intros e s s' h
  rcases h with ⟨xl, h_filled, pc, run⟩
  cases xl with
  | some _ => cases run
  | none =>
    dsimp [Ninst.Run', Ninst.pushB256] at run
    rcases hc : chargeGas (if (x.toB8L.sig) = [] then gBase else gVerylow) s with _ | s_gas
    · rw [hc] at run; dsimp [bind, Except.bind] at run; contradiction
    · rw [hc] at run; dsimp [bind, Except.bind] at run
      rcases hp : Devm.push x.toB8L.sig.toB256 s_gas with _ | s''
      · rw [hp] at run; contradiction
      · rw [hp] at run
        injection run with h_eq; subst h_eq
        apply funext; intro a
        exact (chargeGas_getBal_eq hc a).symm.trans (Devm.push_getBal_eq hp a).symm
⟩

instance {x} : Ninst.Hinv Devm.getStor (Ninst.pushB256 x) := ⟨by
  intros e s s' h
  rcases h with ⟨xl, h_filled, pc, run⟩
  cases xl with
  | some _ => cases run
  | none =>
    dsimp [Ninst.Run', Ninst.pushB256] at run
    rcases hc : chargeGas (if (x.toB8L.sig) = [] then gBase else gVerylow) s with _ | s_gas
    · rw [hc] at run; dsimp [bind, Except.bind] at run; contradiction
    · rw [hc] at run; dsimp [bind, Except.bind] at run
      rcases hp : Devm.push x.toB8L.sig.toB256 s_gas with _ | s''
      · rw [hp] at run; contradiction
      · rw [hp] at run
        injection run with h_eq; subst h_eq
        exact (chargeGas_getStor_eq hc).trans (Devm.push_getStor_eq hp)
⟩

instance {x} : Ninst.Hinv Devm.getCode (Ninst.pushB256 x) := ⟨by
  intros e s s' h
  rcases h with ⟨xl, h_filled, pc, run⟩
  cases xl with
  | some _ => cases run
  | none =>
    dsimp [Ninst.Run', Ninst.pushB256] at run
    rcases hc : chargeGas (if (x.toB8L.sig) = [] then gBase else gVerylow) s with _ | s_gas
    · rw [hc] at run; dsimp [bind, Except.bind] at run; contradiction
    · rw [hc] at run; dsimp [bind, Except.bind] at run
      rcases hp : Devm.push x.toB8L.sig.toB256 s_gas with _ | s''
      · rw [hp] at run; contradiction
      · rw [hp] at run
        injection run with h_eq; subst h_eq
        apply funext; intro a
        exact (chargeGas_getCode_eq hc a).symm.trans (Devm.push_getCode_eq hp a).symm
⟩

instance {x} : Ninst.Hinv Devm.state (Ninst.pushB256 x) := ⟨by
  intros e s s' h
  rcases h with ⟨xl, h_filled, pc, run⟩
  cases xl with
  | some _ => cases run
  | none =>
    dsimp [Ninst.Run', Ninst.pushB256] at run
    have h_pb := Devm.pushBurn_of_run run
    rcases h_pb with ⟨_, _, _, _, _, _, _, _, _, _, _, h_state, _⟩
    exact h_state
⟩

instance : Ninst.Hinv Devm.state (Ninst.reg Rinst.eq) := ⟨by
  intros e s s' h
  rcases h with ⟨xl, h_filled, pc, run⟩
  cases xl with
  | some _ => cases run
  | none =>
    dsimp [Ninst.Run', Rinst.run, Rinst.runCore, applyBinary] at run
    rcases hp1 : Devm.pop s with _ | val1
    · rw [hp1] at run; dsimp [bind, Except.bind] at run; contradiction
    · rw [hp1] at run; dsimp [bind, Except.bind] at run
      rcases val1 with ⟨x1, s1⟩
      rcases hp2 : Devm.pop s1 with _ | val2
      · rw [hp2] at run; dsimp [bind, Except.bind] at run; contradiction
      · rw [hp2] at run; dsimp [bind, Except.bind] at run
        rcases val2 with ⟨x2, s2⟩
        rcases hpush : pushItem _ gVerylow s2 with _ | s''
        · rw [hpush] at run; contradiction
        · rw [hpush] at run
          injection run with h_eq; subst h_eq
          have h_pop1 := Devm.pop_of_pop hp1
          have h_pop2 := Devm.pop_of_pop hp2
          have h_push := Devm.pushBurn_of_run hpush
          rcases h_pop1 with ⟨_, _, _, _, _, _, _, _, _, _, _, hs1, _⟩
          rcases h_pop2 with ⟨_, _, _, _, _, _, _, _, _, _, _, hs2, _⟩
          rcases h_push with ⟨_, _, _, _, _, _, _, _, _, _, _, hs3, _⟩
          exact hs1.trans (hs2.trans hs3)
⟩

instance {n} : Ninst.Hinv Devm.state (Ninst.dup n) := ⟨by
  intros e s s' h
  rcases h with ⟨xl, h_filled, pc, run⟩
  cases xl with
  | some _ => cases run
  | none =>
    dsimp [Ninst.Run', Rinst.run, Rinst.runCore] at run
    rcases hc : chargeGas gVerylow s with _ | s_gas
    · rw [hc] at run; dsimp [bind, Except.bind] at run; contradiction
    · rw [hc] at run; dsimp [bind, Except.bind] at run
      split at run
      · contradiction
      · rename_i rh word
        have h_run_eq : (chargeGas gVerylow s >>= fun d => d.push rh) = .ok s' := by
          dsimp [bind, Except.bind]; rw [hc]; exact run
        have h_pb := Devm.pushBurn_of_run h_run_eq
        rcases h_pb with ⟨_, _, _, _, _, _, _, _, _, _, _, h_state, _⟩
        exact h_state
⟩

instance : Ninst.Hinv Devm.state (Ninst.reg Rinst.gt) := ⟨by
  intros e s s' h
  rcases h with ⟨xl, h_filled, pc, run⟩
  cases xl with
  | some _ => cases run
  | none =>
    dsimp [Ninst.Run', Rinst.run, Rinst.runCore, applyBinary] at run
    rcases hp1 : Devm.pop s with _ | val1
    · rw [hp1] at run; dsimp [bind, Except.bind] at run; contradiction
    · rw [hp1] at run; dsimp [bind, Except.bind] at run
      rcases val1 with ⟨x1, s1⟩
      rcases hp2 : Devm.pop s1 with _ | val2
      · rw [hp2] at run; dsimp [bind, Except.bind] at run; contradiction
      · rw [hp2] at run; dsimp [bind, Except.bind] at run
        rcases val2 with ⟨x2, s2⟩
        rcases hpush : pushItem _ gVerylow s2 with _ | s''
        · rw [hpush] at run; contradiction
        · rw [hpush] at run
          injection run with h_eq; subst h_eq
          have h_pop1 := Devm.pop_of_pop hp1
          have h_pop2 := Devm.pop_of_pop hp2
          have h_push := Devm.pushBurn_of_run hpush
          rcases h_pop1 with ⟨_, _, _, _, _, _, _, _, _, _, _, hs1, _⟩
          rcases h_pop2 with ⟨_, _, _, _, _, _, _, _, _, _, _, hs2, _⟩
          rcases h_push with ⟨_, _, _, _, _, _, _, _, _, _, _, hs3, _⟩
          exact hs1.trans (hs2.trans hs3)
⟩

instance : Linst.Hinv Devm.getBal Devm.getBal Linst.stop := by
  constructor; intros e s r h; injection h with h_eq; subst h_eq; rfl

instance : Linst.Hinv Devm.getBal Devm.getBal Linst.ret := by
  constructor; intros e s r h
  simp only [Linst.Run, Linst.run] at h
  rcases of_bind_eq_ok h with ⟨⟨n1, s1⟩, h1, h2⟩
  rcases of_bind_eq_ok h2 with ⟨⟨n2, s2⟩, h3, h4⟩
  rcases of_bind_eq_ok h4 with ⟨s3, h5, h6⟩
  injection h6 with h6
  funext a
  rw [← h6]
  have h_mem : s3.memRead n1 n2 = ⟨(s3.memRead n1 n2).1, (s3.memRead n1 n2).2⟩ := rfl
  show s.getBal a = (s3.memRead n1 n2).2.getBal a
  rw [memRead_getBal_eq h_mem a, chargeGas_getBal_eq h5 a, Devm.popToNat_getBal_eq h3 a, Devm.popToNat_getBal_eq h1 a]

instance : Linst.Hinv Devm.getBal Devm.getBal Linst.rev := by
  constructor; intros e s r h
  simp only [Linst.Run, Linst.run] at h
  rcases of_bind_eq_ok h with ⟨v1, h1, h2⟩
  rcases of_bind_eq_ok h2 with ⟨v2, h3, h4⟩
  rcases of_bind_eq_ok h4 with ⟨v3, h5, h6⟩
  contradiction

instance : Linst.Hinv Devm.getStor Devm.getStor Linst.stop := by
  constructor; intros e s r h; injection h with h_eq; subst h_eq; rfl

instance : Linst.Hinv Devm.getStor Devm.getStor Linst.ret := by
  constructor; intros e s r h
  simp only [Linst.Run, Linst.run] at h
  rcases of_bind_eq_ok h with ⟨⟨n1, s1⟩, h1, h2⟩
  rcases of_bind_eq_ok h2 with ⟨⟨n2, s2⟩, h3, h4⟩
  rcases of_bind_eq_ok h4 with ⟨s3, h5, h6⟩
  injection h6 with h6
  rw [← h6]
  have h_mem : s3.memRead n1 n2 = ⟨(s3.memRead n1 n2).1, (s3.memRead n1 n2).2⟩ := rfl
  show s.getStor = (s3.memRead n1 n2).2.getStor
  rw [memRead_getStor_eq h_mem, ← chargeGas_getStor_eq h5, ← Devm.popToNat_getStor_eq h3, ← Devm.popToNat_getStor_eq h1]

lemma deposit_inv_bal : Func.Inv Devm.getBal Devm.getBal deposit := by prog_inv

lemma wbsum_after_deposit {sevm : Sevm} {s r : Devm}
    (h_nof : wbsum (s.getStor sevm.currentTarget) + sevm.value.toNat < 2 ^ 256)
    (run : Func.Run (weth.main :: weth.aux) sevm s deposit r) :
    wbsum (s.getStor sevm.currentTarget) + sevm.value.toNat = wbsum (r.getStor sevm.currentTarget) := sorry

lemma deposit_inv_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s deposit r)
    (h_sv : s.PreSolvent sevm.currentTarget sevm) :
    r.PostSolvent sevm.currentTarget := by
  unfold Devm.PostSolvent
  unfold Stor.Solvent
  rw [B256.toNat_zero]
  have h_bal : s.getBal = r.getBal := Func.of_inv _ _ deposit_inv_bal run
  rw [← h_bal]
  have h_sv' : wbsum (s.getStor sevm.currentTarget) + sevm.value.toNat ≤ (s.getBal sevm.currentTarget).toNat := by
    have h := h_sv.left rfl
    unfold Stor.Solvent at h
    exact h
  have h_lt : wbsum (s.getStor sevm.currentTarget) + sevm.value.toNat < 2 ^ 256 := by
    apply lt_of_le_of_lt h_sv'
    apply B256.toNat_lt
  rw [← wbsum_after_deposit h_lt run]
  rw [Nat.add_zero]
  exact h_sv'

syntax "simple_solvent" : tactic
set_option hygiene false in
macro_rules
| `(tactic| simple_solvent) =>
  `(tactic| revert h_sv; simp [Devm.PostSolvent, Devm.PreSolvent]; intro h_sv;
            apply solvent_zero_of_solvent;
            apply solvent_of_same_stor h_sv <;>
            apply congr_fun <| Func.of_inv _ _ (by prog_inv) run )

lemma name_inv_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s name r)
    (h_sv : s.PreSolvent sevm.currentTarget sevm) :
    r.PostSolvent sevm.currentTarget := by simple_solvent

lemma approve_inv_bal : Func.Inv Devm.getBal Devm.getBal approve := by prog_inv

def ValidAdr (w : B256) : Prop := ∃ a : Adr, a.toB256 = w

def validAdr_toB256 (a : Adr) : ValidAdr a.toB256 := ⟨a, rfl⟩

lemma toB256_toAdr {w : B256} :
    ValidAdr w → w.toAdr.toB256 = w := by
  intro h; rcases h with ⟨a, ha⟩;
  rw [← ha, toAdr_toB256]

lemma cons_pref_cons_inv {α} {x : α} {xs ys : List α} (h : (x :: xs) <<+ (x :: ys)) : xs <<+ ys := by
  rcases h with ⟨zs, h⟩
  injection h with _ h_tail
  exact ⟨zs, h_tail⟩

open Lean.Elab.Tactic
open Lean.Parser.Tactic
open Lean.Elab.Term
open Lean
open Qq
open Ninst

def Line.take : Nat → Q(Line) → TacticM Q(Line)
| 0, _ => pure q([] : Line)
| n + 1, l => do
  let l' : Q(Line) ← Meta.whnf l
  match l' with
  | ~q([]) => failure
  | ~q($i :: $is) =>
    let x ← Line.take n is
    pure q($i :: $x)
  | _ => failure

elab "lexen" e:num : tactic =>
  withMainContext do
    let n := Lean.TSyntax.getNat e
    let g : Q(Prop) ← getMainTarget
    match g with
    | ~q(Line.Run _ $s $l _ → $c) =>
      let ss ← findSubscript s
      let x ← Line.take n l
      Lean.Expr.apply (Lean.mkApp2 q(@run_append_elim) c x)
      Strings.intro ["s" ++ ss, "h" ++ ss]
    | _ => throwError "unexpected goal for lexen"

elab "lexec" e:term : tactic =>
  withMainContext do
    let x ← elabTermForApply e
    let g : Q(Prop) ← getMainTarget
    match g with
    | ~q(Line.Run _ $s _ _ → $c) =>
      let ss ← findSubscript s
      Lean.Expr.apply (Lean.mkApp2 q(@run_append_elim) c x)
      Strings.intro ["s" ++ ss, "h" ++ ss]
    | _ => throwError "unexpected goal for lexec"

def addressMask : B256 := ⟨⟨.max, 0xffffffff00000000⟩, 0⟩

lemma B128.and_eq_and_prod_and (x y : B128) :
    x &&& y = ⟨x.1 &&& y.1, x.2 &&& y.2⟩ := rfl

lemma B256.and_eq_and_prod_and (x y : B256) :
    x &&& y = ⟨x.1 &&& y.1, x.2 &&& y.2⟩ := rfl

lemma B128.zero_and {x : B128} : 0 &&& x = 0 := by
  simp [B128.and_eq_and_prod_and]
  apply Prod.ext <;> simp

lemma B64.mask_and_eq_zero (x : B32) :
    (0xffffffff00000000 : B64) &&& x.toB64 = 0 := by
  simp only [B32.toB64]
  rw [← @UInt32.and_neg_one x, UInt32.toUInt64_and]
  rw [UInt64.and_comm (UInt32.toUInt64 _), ← UInt64.and_assoc]
  apply UInt64.zero_and

lemma validAdr_iff {w : B256} :
    ValidAdr w ↔ addressMask &&& w = 0 := by
  constructor <;> intro h
  · rcases h with ⟨⟨a32, a128⟩, ⟨_⟩⟩
    simp [Adr.toB256, addressMask]
    rw [B256.and_eq_and_prod_and]
    simp [B128.zero_and]
    rw [B128.and_eq_and_prod_and]
    simp
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply B64.mask_and_eq_zero
    · rfl
  · refine' ⟨w.toAdr, _⟩
    rcases w with ⟨⟨wz, wh⟩, wl⟩
    simp only [addressMask, B256.and_eq_and_prod_and, B128.and_eq_and_prod_and] at h
    rw [show (0 : B256) = ((0, 0), (0, 0)) from rfl,
      Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨hz, hm⟩, -⟩ := h
    have h_wz : wz = 0 := by simp only [B64.max] at hz; bv_decide
    have h_wh : wh.toB32.toB64 = wh := by rw [toB64_toB32]; bv_decide
    simp only [B256.toAdr, Adr.toB256, h_wz, h_wh]

lemma addressMask_eq_shl :
    addressMask = (~~~ (0 : B256)) <<< (160 : Nat).toB256.toNat := by
  rw [toNat_toB256, Nat.lo_eq_of_lt (by omega)]; rfl

lemma of_push_addressMask {e : Sevm} {s s' : Devm} {xs}
    (h_pfx : xs <<+ s.stack) (h_run : Line.Run e s pushAddressMask s') :
    (addressMask :: xs <<+ s'.stack) := by
  rw [addressMask_eq_shl]
  revert s; simp only [pushAddressMask]; line_pref

lemma of_check_non_address {e : Sevm} {s s' : Devm} {x xs}
    (h_pfx : x :: xs <<+ s.stack) (h_run : Line.Run e s checkNonAddress s') :
    ∃ y, (y :: xs <<+ s'.stack) ∧ (y = 0 ↔ ValidAdr x) := by
  rename' s' => s''
  rcases of_run_append _ h_run with ⟨sm, h_push, h_and⟩; clear h_run
  have h_pfx' := of_push_addressMask h_pfx h_push; clear h_pfx h_push s
  have h_pfx2 : (addressMask &&& x) :: xs <<+ s''.stack := by
    revert h_and; revert sm; line_pref
  refine ⟨_, h_pfx2, Iff.symm validAdr_iff⟩

lemma of_check_address {e : Sevm} {s s' : Devm} {x xs} :
    (x :: xs <<+ s.stack) →
    Line.Run e s checkAddress s' →
    ∃ y, (y :: xs <<+ s'.stack) ∧ (y = 0 ↔ ¬ ValidAdr x) := by
  rename' s' => s''; intros h_pfx h_run
  rcases of_run_append _ h_run with ⟨sm, hs', h_run'⟩; clear h_run
  rcases of_check_non_address h_pfx hs' with ⟨y, h_pfx', h_iff⟩; clear h_pfx hs' s
  have h_pfx2 : ((y =? 0) :: xs <<+ s''.stack) := by
    revert h_run'; revert sm; line_pref
  refine' ⟨_, h_pfx2, _⟩; rw [← h_iff]
  apply Ne.ite_eq_right_iff <| Ne.symm B256.zero_ne_one

lemma of_prepApprove {sevm : Sevm} {s s' : Devm} :
    Line.Run sevm s prepApprove s' →
    ∃ vx x y, ([vx, x, y] <<+ s'.stack) ∧ (vx = 0 ↔ ¬ ValidAdr x) := by
  lexen 7
  have hp₀ : [] <<+ s₁.stack := nil_pref
  cstate s
  lexen 2
  rcases prefix_of_cdl hp₀ h₂ with ⟨wad, hp₁⟩
  cstate s₁
  lexen 2
  have hp₂ : [0, 64, wad] <<+ s₃.stack := by lpfx
  cstate s₂
  lexen 1
  rcases prefix_of_kec (of_run_singleton h₄) hp₂ with ⟨hash, hp₃⟩
  cstate s₃
  lexen 1
  have hp₄ : [hash, hash, wad] <<+ s₅.stack := by lpfx
  cstate s₄
  intro h
  rcases of_check_address hp₄ h with ⟨vx, h_vx, h_iff⟩
  refine ⟨vx, hash, wad, h_vx, h_iff⟩

lemma State.get_set_self {w : _root_.State} {a : Adr} {ac : Acct} :
    (w.set a ac).get a = ac := by
  unfold State.set State.get
  split_ifs with h
  · rw [Std.TreeMap.getD_erase]; simp; exact h.symm
  · rw [Std.TreeMap.getD_insert]; simp

lemma setStorVal_getStor_self {devm : Devm} {adr : Adr} {key val : B256} :
    (devm.setStorVal adr key val).getStor adr = (devm.getStor adr).set key val := by
  simp only [Devm.getStor, Devm.getAcct, Devm.setStorVal, State.setStorVal]
  rw [State.get_set_self]

lemma Stor.get_set_ne {s : Stor} {k k' v : B256} (h : k ≠ k') :
    (s.set k' v).get k = s.get k := by
  unfold Stor.set Stor.get
  have hc : compare k' k ≠ Ordering.eq := by
    intro hcc; exact h (compare_eq_iff_eq.mp hcc).symm
  split_ifs with hv
  · rw [Std.TreeMap.getD_erase]; simp [hc]
  · rw [Std.TreeMap.getD_insert]; simp [hc]

lemma sstore_getStor_setStorVal {sevm : Sevm} {s s' : Devm} {x xs}
    (h_run : Ninst.Run sevm s .sstore s') (hx : x :: xs <<+ s.stack) :
    ∃ v, s'.getStor sevm.currentTarget = (s.getStor sevm.currentTarget).set x v := by
  rcases of_run_reg h_run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨⟨key, s₁⟩, h1, run₁⟩
  rcases of_bind_eq_ok run₁ with ⟨⟨val, s₂⟩, h2, run₂⟩
  rcases of_bind_eq_ok run₂ with ⟨_, h3, run₃⟩
  rcases of_bind_eq_ok run₃ with ⟨⟨s₃, g₂⟩, h4, run₄⟩
  rcases of_bind_eq_ok run₄ with ⟨g₃, h5, run₅⟩
  rcases of_bind_eq_ok run₅ with ⟨s₄, h6, run₆⟩
  rcases of_bind_eq_ok run₆ with ⟨s₅, h7, run₇⟩
  rcases of_bind_eq_ok run₇ with ⟨_, h8, h9⟩
  have hkx : x = key :=
    (List.of_cons_pref_of_cons_pref hx (pref_of_split (Devm.pop_of_pop h1).stack)).left
  have e1 : s.getStor = s₁.getStor := Devm.pop_getStor_eq h1
  have e2 : s₁.getStor = s₂.getStor := Devm.pop_getStor_eq h2
  have e4 : s₂.getStor = s₃.getStor := by
    split at h4 <;> (injection h4 with eq; injection eq with eq _; subst eq)
    · exact addAccessedStorageKey_getStor.symm
    · rfl
  have e6 : s₃.getStor = s₄.getStor := by
    injection h6 with eq; rw [← eq]; rfl
  have e7 : s₄.getStor = s₅.getStor := chargeGas_getStor_eq h7
  have E : s.getStor = s₅.getStor := e1.trans (e2.trans (e4.trans (e6.trans e7)))
  injection h9 with eq
  refine ⟨val, ?_⟩
  rw [← eq, setStorVal_getStor_self, hkx, E]

lemma sstore_inv_stor_rest {x xs} {sevm : Sevm} {s s' : Devm} :
  ¬ ValidAdr x →
  (x :: xs <<+ s.stack) →
  Ninst.Run sevm s .sstore s' →
  (s.getStor sevm.currentTarget).rest = (s'.getStor sevm.currentTarget).rest := by
  intro h_nv h_pfx h_run
  rcases sstore_getStor_setStorVal h_run h_pfx with ⟨v, h_set⟩
  rw [h_set]
  funext a
  have hne : a.toB256 ≠ x := fun hc => h_nv ⟨a, hc⟩
  simp only [Stor.rest, Function.comp_apply]
  rw [Stor.get_set_ne hne]

lemma Stor.get_set_self {s : Stor} {k v : B256} :
    (s.set k v).get k = v := by
  unfold Stor.set Stor.get
  split_ifs with hv
  · rw [Std.TreeMap.getD_erase]; simp; exact hv.symm
  · rw [Std.TreeMap.getD_insert]; simp

lemma sstore_getStor_set {sevm : Sevm} {s s' : Devm} {x y xs}
    (h_run : Ninst.Run sevm s .sstore s') (hx : x :: y :: xs <<+ s.stack) :
    s'.getStor sevm.currentTarget = (s.getStor sevm.currentTarget).set x y := by
  rcases of_run_reg h_run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨⟨key, s₁⟩, h1, run₁⟩
  rcases of_bind_eq_ok run₁ with ⟨⟨val, s₂⟩, h2, run₂⟩
  rcases of_bind_eq_ok run₂ with ⟨_, h3, run₃⟩
  rcases of_bind_eq_ok run₃ with ⟨⟨s₃, g₂⟩, h4, run₄⟩
  rcases of_bind_eq_ok run₄ with ⟨g₃, h5, run₅⟩
  rcases of_bind_eq_ok run₅ with ⟨s₄, h6, run₆⟩
  rcases of_bind_eq_ok run₆ with ⟨s₅, h7, run₇⟩
  rcases of_bind_eq_ok run₇ with ⟨_, h8, h9⟩
  have hs : s.stack = key :: s₁.stack := (Devm.pop_of_pop h1).stack
  have hs2 : s₁.stack = val :: s₂.stack := (Devm.pop_of_pop h2).stack
  have hxy : x = key ∧ y = val := by
    rw [hs, hs2] at hx
    rcases hx with ⟨sfx, heq⟩
    injection heq with hk hrest
    injection hrest with hv _
    exact ⟨hk.symm, hv.symm⟩
  have e1 : s.getStor = s₁.getStor := Devm.pop_getStor_eq h1
  have e2 : s₁.getStor = s₂.getStor := Devm.pop_getStor_eq h2
  have e4 : s₂.getStor = s₃.getStor := by
    split at h4 <;> (injection h4 with eq; injection eq with eq _; subst eq)
    · exact addAccessedStorageKey_getStor.symm
    · rfl
  have e6 : s₃.getStor = s₄.getStor := by
    injection h6 with eq; rw [← eq]; rfl
  have e7 : s₄.getStor = s₅.getStor := chargeGas_getStor_eq h7
  have E : s.getStor = s₅.getStor := e1.trans (e2.trans (e4.trans (e6.trans e7)))
  injection h9 with eq
  rw [← eq, setStorVal_getStor_self, hxy.left, hxy.right, E]

syntax "linv" : tactic
macro_rules
| `(tactic| linv) =>
  `(tactic| first | apply Line.of_inv _ _ (by assumption); line_inv
                  | apply Func.of_inv _ _ _ (by assumption); prog_inv)

lemma of_run_next {fs sevm devm i f devm''}
    (h : Func.Run fs sevm devm (Func.next i f) devm'') :
    ∃ devm', Ninst.Run sevm devm i devm' ∧ Func.Run fs sevm devm' f devm'' := by
  cases h with
  | next h1 h2 => exact ⟨_, h1, h2⟩

lemma of_withdrawLoadCheck {sevm : Sevm} {s s' : Devm}
    (h : Line.Run sevm s withdrawLoadCheck s') :
    s.getBal = s'.getBal ∧
    s.getStor = s'.getStor ∧
    s.getCode = s'.getCode ∧
    ∃ wad cbal, ([cbal <? wad, cbal, wad, wad] <<+ s'.stack) ∧
      (cbal = Devm.getStorVal s' sevm.currentTarget sevm.caller.toB256) := by
  refine ⟨by linv, by linv, by linv, ?_⟩
  revert h
  lexen 2
  rcases prefix_of_cdl nil_pref h₁ with ⟨wad, hp₁⟩
  cstate s
  lexen 2
  have hp₂ : [sevm.caller.toB256, wad, wad] <<+ s₂.stack := by lpfx
  cstate s₁
  lexen 1
  rcases prefix_of_sload' (of_run_singleton h₃) hp₂ with ⟨cbal, hp₃, h_cbal⟩
  have hstor3 : Devm.getStorVal s₂ sevm.currentTarget sevm.caller.toB256
              = Devm.getStorVal s₃ sevm.currentTarget sevm.caller.toB256 := by
    show (s₂.getStor _).get _ = (s₃.getStor _).get _
    rw [Line.of_inv Devm.getStor (by line_inv) h₃]
  rw [hstor3] at h_cbal
  cstate s₂
  intro h₄
  have hp₄ : [cbal <? wad, cbal, wad, wad] <<+ s'.stack := by lpfx
  have hstor4 : Devm.getStorVal s₃ sevm.currentTarget sevm.caller.toB256
              = Devm.getStorVal s' sevm.currentTarget sevm.caller.toB256 := by
    show (s₃.getStor _).get _ = (s'.getStor _).get _
    rw [Line.of_inv Devm.getStor (by line_inv) h₄]
  rw [hstor4] at h_cbal
  exact ⟨wad, cbal, hp₄, h_cbal⟩

lemma approve_inv_wbal {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s approve r) :
    (s.getStor sevm.currentTarget).rest = (r.getStor sevm.currentTarget).rest := by
  rcases of_run_prepend (arg 0 ++ checkNonAddress) _ run
    with ⟨s0, h_s0, h_run'⟩; clear run
  have h_s0_stor_eq : s.getStor = s0.getStor := by linv
  have h_s0_stor : s.getStor sevm.currentTarget = s0.getStor sevm.currentTarget :=
    congr_fun h_s0_stor_eq sevm.currentTarget
  rw [h_s0_stor]; clear h_s0_stor h_s0_stor_eq h_s0 s
  rcases of_run_branch_rev h_run' with ⟨s1, h_pop, h_run⟩; clear h_run'
  have h_s1_stor : s0.getStor sevm.currentTarget = s1.getStor sevm.currentTarget :=
    (Devm.PopBurn.getStor h_pop sevm.currentTarget).symm
  rw [h_s1_stor]; clear h_s1_stor h_pop s0
  rcases of_run_prepend prepApprove _ h_run
    with ⟨s2, h_s2, h_run'⟩; clear h_run
  rcases of_prepApprove h_s2
    with ⟨hash_valid, hash, wad, h_s2_stk, h_iff⟩
  have h_s2_stor_eq : s1.getStor = s2.getStor := by linv
  have h_s2_stor : s1.getStor sevm.currentTarget = s2.getStor sevm.currentTarget :=
    congr_fun h_s2_stor_eq sevm.currentTarget
  rw [h_s2_stor]; clear h_s2_stor h_s2_stor_eq h_s2 s1
  rcases of_run_branch_rev h_run' with ⟨s3, h_pop, h_run⟩; clear h_run'
  have h_hv_eq_zero : hash_valid = 0 := by
    have h_pop_stk := h_pop.stack
    simp [Stack.Pop, Split] at h_pop_stk
    have h_s2_pref : [0] <<+ s2.stack := by
      rw [h_pop_stk]
      exact pref_append _ _
    exact pref_head_unique h_s2_stk h_s2_pref
  rw [h_hv_eq_zero] at h_s2_stk
  simp [h_hv_eq_zero] at h_iff
  clear h_hv_eq_zero hash_valid
  have h_s3_stk : [hash, wad] <<+ s3.stack := by
    have h_pop_stk := h_pop.stack
    simp [Stack.Pop, Split] at h_pop_stk
    rw [h_pop_stk] at h_s2_stk
    exact cons_pref_cons_inv h_s2_stk
  clear h_s2_stk
  have h_s3_stor : s2.getStor sevm.currentTarget = s3.getStor sevm.currentTarget :=
    (Devm.PopBurn.getStor h_pop sevm.currentTarget).symm
  rw [h_s3_stor]; clear h_s3_stor h_pop s2
  rcases of_run_next h_run with ⟨s4, h_sstore, h_run'⟩; clear h_run
  have hh := sstore_inv_stor_rest h_iff h_s3_stk h_sstore
  have h_r_stor_eq : s4.getStor = r.getStor := by
    apply Func.of_inv Devm.getStor Devm.getStor _ h_run'
    prog_inv
  have h_r_stor : s4.getStor sevm.currentTarget = r.getStor sevm.currentTarget :=
    congr_fun h_r_stor_eq sevm.currentTarget
  rw [← h_r_stor]
  apply hh

lemma result_solvent_of_state_solvent {sevm : Sevm} {s r : Devm}
    (h_wbsum : (s.getStor sevm.currentTarget).rest = (r.getStor sevm.currentTarget).rest)
    (h_bal : s.getBal sevm.currentTarget = r.getBal sevm.currentTarget)
    (h_solvent : s.PreSolvent sevm.currentTarget sevm) :
    r.PostSolvent sevm.currentTarget := by
  unfold Devm.PostSolvent Stor.Solvent
  rw [B256.toNat_zero, Nat.add_zero]
  have h_sv' := h_solvent.left rfl
  unfold Stor.Solvent at h_sv'
  rw [← h_bal]
  have h_wbsum_eq : wbsum (s.getStor sevm.currentTarget) = wbsum (r.getStor sevm.currentTarget) := by
    simp [wbsum, h_wbsum]
  rw [← h_wbsum_eq]
  omega

lemma approve_inv_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s approve r)
    (h_sv : s.PreSolvent sevm.currentTarget sevm) :
    r.PostSolvent sevm.currentTarget := by
  have h_bal_fun := Func.of_inv Devm.getBal Devm.getBal approve_inv_bal run
  have h_bal := congr_fun h_bal_fun sevm.currentTarget
  exact result_solvent_of_state_solvent (approve_inv_wbal run) h_bal h_sv

lemma totalSupply_inv_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s totalSupply r)
    (h_sv : s.PreSolvent sevm.currentTarget sevm) :
    r.PostSolvent sevm.currentTarget := by simple_solvent

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

def eq_below (n : Nat) (f g : Adr → B256) : Prop :=
  ∀ k, k.toNat < n → f k = g k

lemma Adr.toNat_lt_size (a : Adr) : a.toNat < 2 ^ 160 := by
  rw [← toAdr_toNat a, Nat.toNat_toAdr, Nat.lo]
  apply Nat.mod_lt _ (Nat.two_pow_pos _)

lemma sumBelow_eq_sumBelow_of_eq_below {m n} {f g : Adr → B256}
    (hm : m < 2 ^ 160) (h_le : m ≤ n) (h_eqb : eq_below n f g) :
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
    eq_below k.toNat f g := by
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

lemma transfer_inv_sum {kd ki v} {b d : Adr → B256}
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

lemma incrAt_of_incrWbal {sevm : Sevm} {s s' : Devm} {wad dst} (h_dst : ValidAdr dst)
    (h_run : Line.Run sevm s incrWbal s') (h_stk : [wad, dst] <<+ s.stack) :
    Increase dst.toAdr wad (s.getStor sevm.currentTarget).rest (s'.getStor sevm.currentTarget).rest := by
  simp only [incrWbal] at h_run
  rcases of_run_append [dup 1, sload, add, swap 0] h_run with ⟨sm, h_pre, h_post⟩
  clear h_run
  have h_stor : s.getStor = sm.getStor := Line.of_inv Devm.getStor (by line_inv) h_pre
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
  rcases prefix_of_sload' r_sload hp1 with ⟨dbal, hp2, h_dbal⟩
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
  have h_set : s'.getStor sevm.currentTarget
      = (sm.getStor sevm.currentTarget).set dst (dbal + wad) :=
    sstore_getStor_set r_sstore hp4
  -- dbal = value at dst in s's storage
  have hs1 : s.getStor = s1.getStor :=
    Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r_dup Line.Run.nil)
  have h_dbal' : dbal = (s.getStor sevm.currentTarget).get dst := by
    rw [h_dbal]; show (s1.getStor sevm.currentTarget).get dst = _; rw [hs1]
  -- assemble the Increase
  intro a
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
    rw [Stor.get_set_ne h_key_ne, h_stor]

lemma of_transferFromUpdateSbal {sevm : Sevm} {s₀ sₙ : Devm} {sbal wad src}
    (h_src : ValidAdr src) (h_sbal : sbal = (s₀.getStor sevm.currentTarget).get src)
    (h_le : wad ≤ sbal) (hp₀ : [sbal, wad, wad, src] <<+ s₀.stack) :
    Line.Run sevm s₀ transferFromUpdateSbal sₙ →
    ( Decrease src.toAdr wad (s₀.getStor sevm.currentTarget).rest (sₙ.getStor sevm.currentTarget).rest ∧
      wad ≤ (s₀.getStor sevm.currentTarget).rest src.toAdr ) := by
  intro h_run
  simp only [transferFromUpdateSbal] at h_run
  rcases of_run_append [sub, dup 2] h_run with ⟨sm, h_pre, h_post⟩
  clear h_run
  have h_stor : s₀.getStor = sm.getStor := Line.of_inv Devm.getStor (by line_inv) h_pre
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
  have h_set : sₙ.getStor sevm.currentTarget
      = (sm.getStor sevm.currentTarget).set src (sbal - wad) :=
    sstore_getStor_set r_sstore hp2
  constructor
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
      rw [Stor.get_set_ne h_key_ne, h_stor]
  · simp only [Stor.rest, Function.comp_apply]
    rw [toB256_toAdr h_src, ← h_sbal]; exact h_le

lemma updateAllowance_inv_stor_rest {fs : List Func} {sevm : Sevm} {s r : Devm} {wad dst}
    (hs : [wad, dst] <<+ s.stack)
    (h_run : Func.Run fs sevm s updateAllowance r) :
    (s.getStor sevm.currentTarget).rest = (r.getStor sevm.currentTarget).rest := by
  rcases of_run_prepend [caller, dup 2, eq] _ h_run with ⟨s0, h_s0, h_run0⟩
  clear h_run
  rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) h_s0) sevm.currentTarget]
  rcases of_run_branch h_run0 with
    ⟨s1, h_pop, h_runP⟩ | ⟨w, s1, s2, h_ne, h_pop, h_burn, h_runQ⟩
  · -- update path
    -- pop the `(dst =? caller)` flag (= 0, since this is the update branch)
    have hs0 : [dst =? Adr.toB256 sevm.caller, wad, dst] <<+ s0.stack := by lpfx
    have hp0 := h_pop.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp0
    rw [hp0] at hs0
    have hs1 : [wad, dst] <<+ s1.stack := by
      have hflag : (dst =? Adr.toB256 sevm.caller) = 0 :=
        pref_head_unique hs0 (pref_append [0] s1.stack)
      rw [hflag] at hs0; exact cons_pref_cons_inv hs0
    rw [(Devm.PopBurn.getStor h_pop sevm.currentTarget).symm]
    clear hs0 hp0 h_pop h_s0 h_run0 hs
    -- segment 1 : swap 0 :: mstoreAt 0  ( wad dst -- wad )
    rcases of_run_prepend (swap 0 :: mstoreAt 0) _ h_runP with ⟨sA, hA, h_runP⟩
    have hsA : [wad] <<+ sA.stack := by lpfx
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hA) sevm.currentTarget]
    clear hA hs1
    -- segment 2 : caller  ( wad -- caller wad )
    rcases of_run_next h_runP with ⟨sB, rB, h_runP⟩
    have hsB : [Adr.toB256 sevm.caller, wad] <<+ sB.stack :=
      prefix_of_push (of_run_caller rB) hsA
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons rB Line.Run.nil)) sevm.currentTarget]
    clear rB hsA
    -- segment 3 : mstoreAt 1  ( caller wad -- wad )
    rcases of_run_prepend (mstoreAt 1) _ h_runP with ⟨sC, hC, h_runP⟩
    have hsC : [wad] <<+ sC.stack := by lpfx
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hC) sevm.currentTarget]
    clear hC hsB
    -- segment 4 : pushList [64, 0]  ( wad -- 0 64 wad )
    rcases of_run_prepend (pushList [64, 0]) _ h_runP with ⟨sD, hD, h_runP⟩
    have hsD : [0, 64, wad] <<+ sD.stack := by lpfx
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hD) sevm.currentTarget]
    clear hD hsC
    -- segment 5 : kec  ( 0 64 wad -- hash wad )
    rcases of_run_next h_runP with ⟨sE, rE, h_runP⟩
    rcases prefix_of_kec rE hsD with ⟨hash, hsE⟩
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons rE Line.Run.nil)) sevm.currentTarget]
    clear rE hsD
    -- segment 6 : swap 0  ( hash wad -- wad hash )
    rcases of_run_next h_runP with ⟨sF, rF, h_runP⟩
    have h_swapF : Stack.Swap (0 : Fin 16).val [hash, wad] [wad, hash] :=
      Stack.swapCore_zero
    have hsF : [wad, hash] <<+ sF.stack :=
      Stack.prefix_of_swap h_swapF (of_run_swap rF) hsE
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons rF Line.Run.nil)) sevm.currentTarget]
    clear rF hsE
    -- segment 7 : dup 1  ( wad hash -- hash wad hash )
    rcases of_run_next h_runP with ⟨sG1, rG1, h_runP⟩
    rcases of_run_dup rG1 with ⟨y, hy, pbG1⟩
    have hy_hash : y = hash := by
      have h_nth : Stack.Nth 1 hash [wad, hash] :=
        Stack.Nth.tail 0 hash wad [hash] (Stack.Nth.head hash [])
      have h_get : sF.stack[(1 : Fin 16).val]? = some hash := Stack.nth_getElem h_nth hsF
      rw [h_get] at hy; injection hy with hy; exact hy.symm
    subst y
    have hsG1 : [hash, wad, hash] <<+ sG1.stack := prefix_of_push pbG1 hsF
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons rG1 Line.Run.nil)) sevm.currentTarget]
    clear rG1 pbG1 hsF
    -- segment 8 : checkAddress  ( hash wad hash -- va(hash) wad hash )
    rcases of_run_prepend checkAddress _ h_runP with ⟨sG, hG, h_runP⟩
    rcases of_check_address hsG1 hG with ⟨va, hsG, h_iff⟩
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hG) sevm.currentTarget]
    clear hG hsG1
    -- rev-branch : checkAddress guarantees `hash` is not a valid address
    rcases of_run_branch_rev h_runP with ⟨sH, h_popH, h_runP⟩
    have hpH := h_popH.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpH
    rw [hpH] at hsG
    have hva0 : va = 0 := pref_head_unique hsG (pref_append [0] sH.stack)
    have hnva : ¬ ValidAdr hash := h_iff.mp hva0
    rw [hva0] at hsG
    have hsH : [wad, hash] <<+ sH.stack := cons_pref_cons_inv hsG
    rw [(Devm.PopBurn.getStor h_popH sevm.currentTarget).symm]
    clear hsG hpH h_popH h_iff hva0
    -- dup 1  ( wad hash -- hash wad hash )
    rcases of_run_next h_runP with ⟨sI, rI, h_runP⟩
    rcases of_run_dup rI with ⟨y, hyI, pbI⟩
    have hyI' : y = hash := by
      have h_nth : Stack.Nth 1 hash [wad, hash] :=
        Stack.Nth.tail 0 hash wad [hash] (Stack.Nth.head hash [])
      have h_get : sH.stack[(1 : Fin 16).val]? = some hash := Stack.nth_getElem h_nth hsH
      rw [h_get] at hyI; injection hyI with hyI; exact hyI.symm
    subst y
    have hsI : [hash, wad, hash] <<+ sI.stack := prefix_of_push pbI hsH
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons rI Line.Run.nil)) sevm.currentTarget]
    clear rI pbI hsH
    -- sload  ( hash wad hash -- amnt wad hash )
    rcases of_run_next h_runP with ⟨sJ, rJ, h_runP⟩
    rcases prefix_of_sload' rJ hsI with ⟨amnt, hsJ, _⟩
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons rJ Line.Run.nil)) sevm.currentTarget]
    clear rJ hsI
    -- dup 0  ( amnt wad hash -- amnt amnt wad hash )
    rcases of_run_next h_runP with ⟨sK, rK, h_runP⟩
    rcases of_run_dup rK with ⟨y, hyK, pbK⟩
    have hyK' : y = amnt := by
      have h_nth : Stack.Nth 0 amnt [amnt, wad, hash] := Stack.Nth.head amnt [wad, hash]
      have h_get : sJ.stack[(0 : Fin 16).val]? = some amnt := Stack.nth_getElem h_nth hsJ
      rw [h_get] at hyK; injection hyK with hyK; exact hyK.symm
    subst y
    have hsK : [amnt, amnt, wad, hash] <<+ sK.stack := prefix_of_push pbK hsJ
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons rK Line.Run.nil)) sevm.currentTarget]
    clear rK pbK hsJ
    -- isMax = [not, iszero]  ( amnt amnt wad hash -- flag amnt wad hash )
    rcases of_run_prepend isMax _ h_runP with ⟨sL, hL, h_runP⟩
    rcases Line.of_run_cons hL with ⟨sK', rNot, hL'⟩
    rcases Line.of_run_cons hL' with ⟨sK'', rIsz, hLnil⟩
    cases hLnil
    have hsL0 : (~~~ amnt) :: [amnt, wad, hash] <<+ sK'.stack := prefix_of_not rNot hsK
    have hsL : ((~~~ amnt) =? 0) :: [amnt, wad, hash] <<+ sL.stack := prefix_of_iszero rIsz hsL0
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hL) sevm.currentTarget]
    clear hL rNot rIsz hsK hsL0
    -- returnTrue-branch : early-return when allowance is infinite
    rcases of_run_branch h_runP with
      ⟨sM, h_popM, h_runP⟩ | ⟨w2, sM, sM2, h_ne2, h_popM, h_burnM, h_runQ2⟩
    · -- continue path
      have hpM := h_popM.stack
      simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpM
      rw [hpM] at hsL
      have hflagM : ((~~~ amnt) =? 0) = 0 := pref_head_unique hsL (pref_append [0] sM.stack)
      rw [hflagM] at hsL
      have hsM : [amnt, wad, hash] <<+ sM.stack := cons_pref_cons_inv hsL
      rw [(Devm.PopBurn.getStor h_popM sevm.currentTarget).symm]
      clear hsL hpM h_popM hflagM
      -- dup 1  ( amnt wad hash -- wad amnt wad hash )
      rcases of_run_next h_runP with ⟨sN1, rN1, h_runP⟩
      rcases of_run_dup rN1 with ⟨y, hyN1, pbN1⟩
      have hyN1' : y = wad := by
        have h_nth : Stack.Nth 1 wad [amnt, wad, hash] :=
          Stack.Nth.tail 0 wad amnt [wad, hash] (Stack.Nth.head wad [hash])
        have h_get : sM.stack[(1 : Fin 16).val]? = some wad := Stack.nth_getElem h_nth hsM
        rw [h_get] at hyN1; injection hyN1 with hyN1; exact hyN1.symm
      subst y
      have hsN1 : [wad, amnt, wad, hash] <<+ sN1.stack := prefix_of_push pbN1 hsM
      rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons rN1 Line.Run.nil)) sevm.currentTarget]
      clear rN1 pbN1 hsM
      -- dup 1  ( wad amnt wad hash -- amnt wad amnt wad hash )
      rcases of_run_next h_runP with ⟨sN2, rN2, h_runP⟩
      rcases of_run_dup rN2 with ⟨y, hyN2, pbN2⟩
      have hyN2' : y = amnt := by
        have h_nth : Stack.Nth 1 amnt [wad, amnt, wad, hash] :=
          Stack.Nth.tail 0 amnt wad [amnt, wad, hash] (Stack.Nth.head amnt [wad, hash])
        have h_get : sN1.stack[(1 : Fin 16).val]? = some amnt := Stack.nth_getElem h_nth hsN1
        rw [h_get] at hyN2; injection hyN2 with hyN2; exact hyN2.symm
      subst y
      have hsN2 : [amnt, wad, amnt, wad, hash] <<+ sN2.stack := prefix_of_push pbN2 hsN1
      rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons rN2 Line.Run.nil)) sevm.currentTarget]
      clear rN2 pbN2 hsN1
      -- lt  ( amnt wad amnt wad hash -- (amnt<?wad) amnt wad hash )
      rcases of_run_next h_runP with ⟨sN, rN, h_runP⟩
      have hsN : (amnt <? wad) :: [amnt, wad, hash] <<+ sN.stack := prefix_of_lt rN hsN2
      rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons rN Line.Run.nil)) sevm.currentTarget]
      clear rN hsN2
      -- rev-branch : guarantees allowance ≥ wad
      rcases of_run_branch_rev h_runP with ⟨sO, h_popO, h_runP⟩
      have hpO := h_popO.stack
      simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpO
      rw [hpO] at hsN
      have hflagO : (amnt <? wad) = 0 := pref_head_unique hsN (pref_append [0] sO.stack)
      rw [hflagO] at hsN
      have hsO : [amnt, wad, hash] <<+ sO.stack := cons_pref_cons_inv hsN
      rw [(Devm.PopBurn.getStor h_popO sevm.currentTarget).symm]
      clear hsN hpO h_popO hflagO
      -- sub  ( amnt wad hash -- (amnt-wad) hash )
      rcases of_run_next h_runP with ⟨sP, rP, h_runP⟩
      have hsP : (amnt - wad) :: [hash] <<+ sP.stack := prefix_of_sub rP hsO
      rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons rP Line.Run.nil)) sevm.currentTarget]
      clear rP hsO
      -- swap 0  ( (amnt-wad) hash -- hash (amnt-wad) )
      rcases of_run_next h_runP with ⟨sQ, rQ, h_runP⟩
      have h_swapQ : Stack.Swap (0 : Fin 16).val [amnt - wad, hash] [hash, amnt - wad] :=
        Stack.swapCore_zero
      have hsQ : [hash, amnt - wad] <<+ sQ.stack :=
        Stack.prefix_of_swap h_swapQ (of_run_swap rQ) hsP
      rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons rQ Line.Run.nil)) sevm.currentTarget]
      clear rQ hsP
      -- sstore  ( key `hash` is not a valid address, so `.rest` is unchanged )
      rcases of_run_next h_runP with ⟨sR, rR, h_runP⟩
      rw [sstore_inv_stor_rest hnva hsQ rR]
      -- returnTrue
      rw [congr_fun (Func.of_inv Devm.getStor Devm.getStor (by prog_inv) h_runP)
        sevm.currentTarget]
    · -- early return (allowance infinite) : `returnTrue` preserves storage
      rw [← Devm.PopBurn.getStor h_popM sevm.currentTarget,
          ← Devm.Burn.getStor h_burnM sevm.currentTarget,
          congr_fun (Func.of_inv Devm.getStor Devm.getStor (by prog_inv) h_runQ2)
            sevm.currentTarget]
  · -- early return : `returnTrue` preserves storage
    have h_eq : s0.getStor sevm.currentTarget = r.getStor sevm.currentTarget := by
      rw [← Devm.PopBurn.getStor h_pop sevm.currentTarget,
          ← Devm.Burn.getStor h_burn sevm.currentTarget,
          congr_fun (Func.of_inv Devm.getStor Devm.getStor (by prog_inv) h_runQ)
            sevm.currentTarget]
    rw [h_eq]

lemma transfer_of_transferFrom {fs : List Func} {sevm : Sevm} {s r : Devm} :
    Func.Run fs sevm s transferFrom r →
    ∃ (x : B256) (a a' : Adr),
      Transfer (s.getStor sevm.currentTarget).rest a x a'
        (r.getStor sevm.currentTarget).rest := by
  intro h_run
  simp only [transferFrom] at h_run
  -- arg 0 : push src
  rcases of_run_prepend (arg 0) _ h_run with ⟨a1, h1, h_run⟩
  rcases prefix_of_cdl nil_pref h1 with ⟨src, hs1⟩
  have hg : s.getStor = a1.getStor := Line.of_inv Devm.getStor (by line_inv) h1
  clear h1
  -- dup 0 : [src, src]
  rcases of_run_next h_run with ⟨a2, r2, h_run⟩
  rcases of_run_dup r2 with ⟨y, hy2, pb2⟩
  have hy2' : y = src := by
    have h_get : a1.stack[(0 : Fin 16).val]? = some src :=
      Stack.nth_getElem (Stack.Nth.head src []) hs1
    rw [h_get] at hy2; injection hy2 with hy2; exact hy2.symm
  subst y
  have hs2 : [src, src] <<+ a2.stack := prefix_of_push pb2 hs1
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r2 Line.Run.nil))
  clear r2 pb2 hs1
  -- checkNonAddress
  rcases of_run_prepend checkNonAddress _ h_run with ⟨a3, h3, h_run⟩
  rcases of_check_non_address hs2 h3 with ⟨na_src, hs3, h_src_iff⟩
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h3)
  clear h3 hs2
  -- rev-branch : src is a valid address
  rcases of_run_branch_rev h_run with ⟨a4, hp4, h_run⟩
  have hp4s := hp4.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp4s
  rw [hp4s] at hs3
  have h_src : ValidAdr src := h_src_iff.mp (pref_head_unique hs3 (pref_append [0] a4.stack))
  rw [pref_head_unique hs3 (pref_append [0] a4.stack)] at hs3
  have hs4 : [src] <<+ a4.stack := cons_pref_cons_inv hs3
  have hg := hg.trans (funext (fun a => (Devm.PopBurn.getStor hp4 a).symm))
  clear hs3 hp4s hp4 h_src_iff
  -- arg 2 : push wad
  rcases of_run_prepend (arg 2) _ h_run with ⟨a5, h5, h_run⟩
  rcases prefix_of_cdl hs4 h5 with ⟨wad, hs5⟩
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h5)
  clear h5 hs4
  -- dup 0 : [wad, wad, src]
  rcases of_run_next h_run with ⟨a6, r6, h_run⟩
  rcases of_run_dup r6 with ⟨y, hy6, pb6⟩
  have hy6' : y = wad := by
    have h_get : a5.stack[(0 : Fin 16).val]? = some wad :=
      Stack.nth_getElem (Stack.Nth.head wad [src]) hs5
    rw [h_get] at hy6; injection hy6 with hy6; exact hy6.symm
  subst y
  have hs6 : [wad, wad, src] <<+ a6.stack := prefix_of_push pb6 hs5
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r6 Line.Run.nil))
  clear r6 pb6 hs5
  -- dup 2 : [src, wad, wad, src]
  rcases of_run_next h_run with ⟨a7, r7, h_run⟩
  rcases of_run_dup r7 with ⟨y, hy7, pb7⟩
  have hy7' : y = src := by
    have h_get : a6.stack[(2 : Fin 16).val]? = some src :=
      Stack.nth_getElem
        (Stack.Nth.tail 1 src wad [wad, src]
          (Stack.Nth.tail 0 src wad [src] (Stack.Nth.head src []))) hs6
    rw [h_get] at hy7; injection hy7 with hy7; exact hy7.symm
  subst y
  have hs7 : [src, wad, wad, src] <<+ a7.stack := prefix_of_push pb7 hs6
  have hg7 : s.getStor = a7.getStor :=
    hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r7 Line.Run.nil))
  clear r7 pb7 hs6
  -- sload : [sbal, wad, wad, src]
  rcases of_run_next h_run with ⟨a8, r8, h_run⟩
  rcases prefix_of_sload' r8 hs7 with ⟨sbal, hs8, h_sbal⟩
  have hg := hg7.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r8 Line.Run.nil))
  clear r8 hs7
  -- dup 1 : [wad, sbal, wad, wad, src]
  rcases of_run_next h_run with ⟨a9, r9, h_run⟩
  rcases of_run_dup r9 with ⟨y, hy9, pb9⟩
  have hy9' : y = wad := by
    have h_get : a8.stack[(1 : Fin 16).val]? = some wad :=
      Stack.nth_getElem
        (Stack.Nth.tail 0 wad sbal [wad, wad, src] (Stack.Nth.head wad [wad, src])) hs8
    rw [h_get] at hy9; injection hy9 with hy9; exact hy9.symm
  subst y
  have hs9 : [wad, sbal, wad, wad, src] <<+ a9.stack := prefix_of_push pb9 hs8
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r9 Line.Run.nil))
  clear r9 pb9 hs8
  -- dup 1 : [sbal, wad, sbal, wad, wad, src]
  rcases of_run_next h_run with ⟨a10, r10, h_run⟩
  rcases of_run_dup r10 with ⟨y, hy10, pb10⟩
  have hy10' : y = sbal := by
    have h_get : a9.stack[(1 : Fin 16).val]? = some sbal :=
      Stack.nth_getElem
        (Stack.Nth.tail 0 sbal wad [sbal, wad, wad, src] (Stack.Nth.head sbal [wad, wad, src])) hs9
    rw [h_get] at hy10; injection hy10 with hy10; exact hy10.symm
  subst y
  have hs10 : [sbal, wad, sbal, wad, wad, src] <<+ a10.stack := prefix_of_push pb10 hs9
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r10 Line.Run.nil))
  clear r10 pb10 hs9
  -- lt : [(sbal <? wad), sbal, wad, wad, src]
  rcases of_run_next h_run with ⟨a11, r11, h_run⟩
  have hs11 : (sbal <? wad) :: [sbal, wad, wad, src] <<+ a11.stack := prefix_of_lt r11 hs10
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r11 Line.Run.nil))
  clear r11 hs10
  -- rev-branch : source balance ≥ wad
  rcases of_run_branch_rev h_run with ⟨a12, hp12, h_run⟩
  have hp12s := hp12.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp12s
  rw [hp12s] at hs11
  have h_ltflag : (sbal <? wad) = 0 := pref_head_unique hs11 (pref_append [0] a12.stack)
  have h_le : wad ≤ sbal := by
    rw [← B256.not_lt]; intro hlt
    rw [B256.lt_check, if_pos hlt] at h_ltflag
    exact B256.zero_ne_one h_ltflag.symm
  rw [h_ltflag] at hs11
  have hs12 : [sbal, wad, wad, src] <<+ a12.stack := cons_pref_cons_inv hs11
  have hg12 : s.getStor = a12.getStor :=
    hg.trans (funext (fun a => (Devm.PopBurn.getStor hp12 a).symm))
  clear hs11 hp12s hp12 h_ltflag
  -- transferFromUpdateSbal : decrease source balance
  rcases of_run_prepend transferFromUpdateSbal _ h_run with ⟨a13, h13, h_run⟩
  have h_sbal' : sbal = (a12.getStor sevm.currentTarget).get src := by
    rw [h_sbal]
    show (a7.getStor sevm.currentTarget).get src = _
    rw [congr_fun (hg7.symm.trans hg12) sevm.currentTarget]
  rcases of_transferFromUpdateSbal h_src h_sbal' h_le hs12 h13 with ⟨h_dec, h_le'⟩
  have hs13 : [wad, src] <<+ a13.stack := by lpfx
  clear h13 hs12 h_sbal h_sbal' h_le
  -- arg 1 : push dst
  rcases of_run_prepend (arg 1) _ h_run with ⟨a14, h14, h_run⟩
  rcases prefix_of_cdl hs13 h14 with ⟨dst, hs14⟩
  have hg' : a13.getStor = a14.getStor := Line.of_inv Devm.getStor (by line_inv) h14
  clear h14 hs13
  -- dup 0 : [dst, dst, wad, src]
  rcases of_run_next h_run with ⟨a15, r15, h_run⟩
  rcases of_run_dup r15 with ⟨y, hy15, pb15⟩
  have hy15' : y = dst := by
    have h_get : a14.stack[(0 : Fin 16).val]? = some dst :=
      Stack.nth_getElem (Stack.Nth.head dst [wad, src]) hs14
    rw [h_get] at hy15; injection hy15 with hy15; exact hy15.symm
  subst y
  have hs15 : [dst, dst, wad, src] <<+ a15.stack := prefix_of_push pb15 hs14
  have hg' := hg'.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r15 Line.Run.nil))
  clear r15 pb15 hs14
  -- checkNonAddress
  rcases of_run_prepend checkNonAddress _ h_run with ⟨a16, h16, h_run⟩
  rcases of_check_non_address hs15 h16 with ⟨na_dst, hs16, h_dst_iff⟩
  have hg' := hg'.trans (Line.of_inv Devm.getStor (by line_inv) h16)
  clear h16 hs15
  -- rev-branch : dst is a valid address
  rcases of_run_branch_rev h_run with ⟨a17, hp17, h_run⟩
  have hp17s := hp17.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp17s
  rw [hp17s] at hs16
  have h_dst : ValidAdr dst := h_dst_iff.mp (pref_head_unique hs16 (pref_append [0] a17.stack))
  rw [pref_head_unique hs16 (pref_append [0] a17.stack)] at hs16
  have hs17 : [dst, wad, src] <<+ a17.stack := cons_pref_cons_inv hs16
  have hg' := hg'.trans (funext (fun a => (Devm.PopBurn.getStor hp17 a).symm))
  clear hs16 hp17s hp17 h_dst_iff
  -- dup 0 : [dst, dst, wad, src]
  rcases of_run_next h_run with ⟨a18, r18, h_run⟩
  rcases of_run_dup r18 with ⟨y, hy18, pb18⟩
  have hy18' : y = dst := by
    have h_get : a17.stack[(0 : Fin 16).val]? = some dst :=
      Stack.nth_getElem (Stack.Nth.head dst [wad, src]) hs17
    rw [h_get] at hy18; injection hy18 with hy18; exact hy18.symm
  subst y
  have hs18 : [dst, dst, wad, src] <<+ a18.stack := prefix_of_push pb18 hs17
  have hg' := hg'.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r18 Line.Run.nil))
  clear r18 pb18 hs17
  -- dup 2 : [wad, dst, dst, wad, src]
  rcases of_run_next h_run with ⟨a19, r19, h_run⟩
  rcases of_run_dup r19 with ⟨y, hy19, pb19⟩
  have hy19' : y = wad := by
    have h_get : a18.stack[(2 : Fin 16).val]? = some wad :=
      Stack.nth_getElem
        (Stack.Nth.tail 1 wad dst [dst, wad, src]
          (Stack.Nth.tail 0 wad dst [wad, src] (Stack.Nth.head wad [src]))) hs18
    rw [h_get] at hy19; injection hy19 with hy19; exact hy19.symm
  subst y
  have hs19 : [wad, dst, dst, wad, src] <<+ a19.stack := prefix_of_push pb19 hs18
  have hg19 : a13.getStor = a19.getStor :=
    hg'.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r19 Line.Run.nil))
  clear r19 pb19 hs18
  -- incrWbal : increase destination balance
  rcases of_run_prepend incrWbal _ h_run with ⟨a20, h20, h_run⟩
  have h_incr : Increase dst.toAdr wad (a19.getStor sevm.currentTarget).rest
      (a20.getStor sevm.currentTarget).rest :=
    incrAt_of_incrWbal h_dst h20 (pref_trans ⟨[dst, wad, src], rfl⟩ hs19)
  have hs20 : [dst, wad, src] <<+ a20.stack := by
    rcases of_run_append [dup 1, sload, add, swap 0] h20 with ⟨am, ham, hend⟩
    rcases Line.of_run_cons ham with ⟨b1, rd1, ham⟩
    rcases Line.of_run_cons ham with ⟨b2, rsl, ham⟩
    rcases Line.of_run_cons ham with ⟨b3, radd, ham⟩
    rcases Line.of_run_cons ham with ⟨b4, rsw, ham⟩
    cases ham
    rcases Line.of_run_cons hend with ⟨a20', r_sstore, hend⟩
    cases hend
    rcases of_run_dup rd1 with ⟨y, hy, pb⟩
    have hyd : y = dst := by
      have h_get : a19.stack[(1 : Fin 16).val]? = some dst :=
        Stack.nth_getElem
          (Stack.Nth.tail 0 dst wad [dst, dst, wad, src] (Stack.Nth.head dst [dst, wad, src])) hs19
      rw [h_get] at hy; injection hy with hy; exact hy.symm
    subst y
    have hb1 : [dst, wad, dst, dst, wad, src] <<+ b1.stack := prefix_of_push pb hs19
    rcases prefix_of_sload' rsl hb1 with ⟨dbal, hb2, _⟩
    have hb3 : (dbal + wad) :: [dst, dst, wad, src] <<+ b3.stack := prefix_of_add radd hb2
    have h_swap : Stack.Swap (0 : Fin 16).val
        [dbal + wad, dst, dst, wad, src] [dst, dbal + wad, dst, wad, src] := Stack.swapCore_zero
    have hb4 : [dst, dbal + wad, dst, wad, src] <<+ am.stack :=
      Stack.prefix_of_swap h_swap (of_run_swap rsw) hb3
    exact prefix_of_sstore r_sstore hb4
  clear h20 hs19
  -- transferFromLog : does not touch storage
  rcases of_run_prepend transferFromLog _ h_run with ⟨a21, h21, h_run⟩
  have hs21 : [wad, src] <<+ a21.stack := by lpfx
  have hg_log : a20.getStor = a21.getStor := Line.of_inv Devm.getStor (by line_inv) h21
  clear h21
  -- updateAllowance : preserves the WETH balance storage
  have h_ua : (a21.getStor sevm.currentTarget).rest = (r.getStor sevm.currentTarget).rest :=
    updateAllowance_inv_stor_rest hs21 h_run
  -- assemble the Transfer
  refine ⟨wad, src.toAdr, dst.toAdr, ?_, (a13.getStor sevm.currentTarget).rest, ?_, ?_⟩
  · rw [congr_fun hg12 sevm.currentTarget]; exact h_le'
  · rw [congr_fun hg12 sevm.currentTarget]; exact h_dec
  · rw [congr_fun hg19 sevm.currentTarget, ← h_ua, ← congr_fun hg_log sevm.currentTarget]
    exact h_incr

lemma nof_of_solvent {sevm : Sevm} {s : Devm} {a}
    (h : s.PreSolvent a sevm) : SumNof (s.getStor a).rest := by
  apply lt_of_le_of_lt _ (B256.toNat_lt (s.getBal a))
  unfold Devm.PreSolvent at h
  by_cases h' : sevm.currentTarget = a
  · have hh := h.left h'; unfold Stor.Solvent wbsum at hh
    apply le_trans (Nat.le_add_right _ _) hh
  · have hh := h.right h'; unfold Stor.Solvent wbsum at hh
    apply le_trans (Nat.le_add_right _ _) hh

lemma result_solvent_of_state_solvent' {sevm : Sevm} {s r : Devm}
    (h_sv : s.PreSolvent sevm.currentTarget sevm)
    (h_sum : wbsum (s.getStor sevm.currentTarget) = wbsum (r.getStor sevm.currentTarget))
    (h_bal : s.getBal sevm.currentTarget = r.getBal sevm.currentTarget) :
    r.PostSolvent sevm.currentTarget := by
  unfold Devm.PostSolvent Stor.Solvent
  rw [B256.toNat_zero, Nat.add_zero]
  have h_sv' := h_sv.left rfl
  unfold Stor.Solvent at h_sv'
  rw [← h_bal, ← h_sum]
  omega

lemma transferFrom_inv_bal : Func.Inv Devm.getBal Devm.getBal transferFrom := by prog_inv

lemma transferFrom_inv_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s transferFrom r)
    (h_sv : s.PreSolvent sevm.currentTarget sevm) :
    r.PostSolvent sevm.currentTarget := by
  rcases transfer_of_transferFrom run with ⟨x, a, a', h_di⟩
  refine result_solvent_of_state_solvent' h_sv ?_ ?_
  · exact transfer_inv_sum (nof_of_solvent h_sv) h_di
  · exact congr_fun (Func.of_inv Devm.getBal Devm.getBal transferFrom_inv_bal run)
      sevm.currentTarget

lemma withdraw_inv_solvent {sevm : Sevm} {s r : Devm}
    (cond : Precond sevm.currentTarget sevm s)
    (ih : Exec.InvDepth sevm.depth sevm.currentTarget weth (Precond sevm.currentTarget) (Postcond sevm.currentTarget))
    (run : Func.Run (weth.main :: weth.aux) sevm s withdraw r) :
    r.PostSolvent sevm.currentTarget := sorry

lemma decimals_inv_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s decimals r)
    (h_sv : s.PreSolvent sevm.currentTarget sevm) :
    r.PostSolvent sevm.currentTarget := by simple_solvent

lemma balanceOf_inv_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s balanceOf r)
    (h_sv : s.PreSolvent sevm.currentTarget sevm) :
    r.PostSolvent sevm.currentTarget := by simple_solvent

lemma symbol_inv_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s symbol r)
    (h_sv : s.PreSolvent sevm.currentTarget sevm) :
    r.PostSolvent sevm.currentTarget := by simple_solvent

lemma transfer_inv_solvent' {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s transfer r)
    (h_sv : s.PreSolvent sevm.currentTarget sevm) :
    r.PostSolvent sevm.currentTarget := sorry

lemma allowance_inv_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s allowance r)
    (h_sv : s.PreSolvent sevm.currentTarget sevm) :
    r.PostSolvent sevm.currentTarget := by simple_solvent

lemma Func.inv_nof {c : List Func} {sevm : Sevm} {s r : Devm} {f : Func}
    (run : Func.Run c sevm s f r) (h_nof : sum s.getBal < 2 ^ 256) :
    sum r.getBal < 2 ^ 256 := sorry

lemma run_inv_cond (f : Func)
    ( h_solv :
      ∀ {sevm : Sevm} {s r : Devm},
        Func.Run (weth.main :: weth.aux) sevm s f r →
        s.PreSolvent sevm.currentTarget sevm →
        r.PostSolvent sevm.currentTarget ) :
    ∀ {sevm : Sevm} {s r : Devm},
      Func.Run (weth.main :: weth.aux) sevm s f r →
      Precond sevm.currentTarget sevm s →
      Postcond sevm.currentTarget sevm r := by
  intro sevm s r run cond
  constructor
  · apply Func.inv_nof run cond.nof
  · apply h_solv run cond.solvent

lemma weth_inv {sevm : Sevm} {s r}
    (cond : Precond sevm.currentTarget sevm s)
    ( ih :
      Exec.InvDepth sevm.depth sevm.currentTarget weth
        (Precond sevm.currentTarget)
        (Postcond sevm.currentTarget) ) :
    Func.Run (weth.main :: weth.aux) sevm s (Func.call 0) r →
    Postcond sevm.currentTarget sevm r := by
  -- unwrap the initial `call 0` (this part does not exist in original proof in Solvent.lean)
  intro run; cases run
  rename (_ = _) => eq
  rename (Func.Run _ _ _ _ _) => run
  rename (Devm.Burn _ _) => burn
  rename Devm => s₀
  cases eq
  have cond₀ : Precond sevm.currentTarget sevm s₀ :=
    Precond.state_eq cond burn.state.symm
  clear cond burn s
  revert run
  pexec fsig
  have cond₁ : Precond sevm.currentTarget sevm s₁ := by
    refine' ⟨_, _⟩
    · rw [← Line.of_inv Devm.getBal (by line_inv) h₁]; exact cond₀.nof
    · apply Line.inv_solvent _ _ cond₀.solvent h₁ <;> line_inv
  clear cond₀
  clear h₁
  clear s₀
  intro temp
  apply
    ( @dispatchWith_inv
      (weth.main :: weth.aux) 1 deposit
      (λ e s =>
         Precond e.currentTarget e s ∧
         Exec.InvDepth e.depth e.currentTarget weth (Precond e.currentTarget) (Postcond e.currentTarget) )
      (λ e r => Postcond e.currentTarget e r)
      ?_ ?_ rfl ?_ wethTree ?_ sevm s₁ r ⟨cond₁, ih⟩ temp )
    <;> clear temp cond₁ ih r s₁ sevm
  · intro e s x w s' s'' ⟨h_cond, h_ih⟩ h_run h_pop
    refine' ⟨_, h_ih⟩
    have h_run_state : s.state = s'.state := Line.of_inv Devm.state (by line_inv) h_run
    rcases h_pop with ⟨_, _, _, _, _, _, _, _, _, _, _, h_pop_state, _⟩
    apply Precond.state_eq h_cond
    exact h_pop_state.symm.trans h_run_state.symm
  · intro e s x w s' s'' ⟨h_cond, h_ih⟩ h_run h_pop
    refine' ⟨_, h_ih⟩
    have h_run_state : s.state = s'.state := Line.of_inv Devm.state (by line_inv) h_run
    rcases h_pop with ⟨_, _, _, _, _, _, _, _, _, _, _, h_pop_state, _⟩
    apply Precond.state_eq h_cond
    exact h_pop_state.symm.trans h_run_state.symm
  · intro e s s' r ⟨cond, ih⟩ burn run
    have cond' : Precond e.currentTarget e s' := Precond.state_eq cond burn.state.symm
    --have cond_c : Cond e.currentTarget e s' := Cond.of_precond cond'
    have r_cond : Postcond e.currentTarget e r :=
      run_inv_cond deposit deposit_inv_solvent run cond'
    exact r_cond
  · intro e s r wf h_mem ⟨cond, ih⟩ h_run
    rcases h_mem with (((h | h) | h) | (h | h)) | (((h | h) | h) | (h | h)) <;>
      (cases h)
    · apply run_inv_cond name name_inv_solvent h_run cond
    · apply run_inv_cond approve approve_inv_solvent h_run cond
    · apply run_inv_cond totalSupply totalSupply_inv_solvent h_run cond
    · apply run_inv_cond transferFrom transferFrom_inv_solvent h_run cond
    · constructor
      · apply Func.inv_nof h_run cond.nof
      · apply withdraw_inv_solvent cond ih h_run
    · apply run_inv_cond decimals decimals_inv_solvent h_run cond
    · apply run_inv_cond balanceOf balanceOf_inv_solvent h_run cond
    · apply run_inv_cond symbol symbol_inv_solvent h_run cond
    · apply run_inv_cond transfer transfer_inv_solvent' h_run cond
    · apply run_inv_cond allowance allowance_inv_solvent h_run cond

theorem weth_inv_solvent (wa : Adr) :
    ∀ sevm pre post,
      Exec 0 sevm pre (.ok post)  →
      (sevm.currentTarget = wa → some sevm.code.toList = Prog.compile weth) →
      Precond wa sevm pre →
      Postcond wa sevm post := by
  intro sevm devm exn exc h_code h_pc
  apply lift_inv wa weth (Precond wa) (Postcond wa)
  · intro sevm pre post run eq; rw [← eq]
    dsimp [Prog.Run] at run
    intro ih cond; apply weth_inv cond _ run
    intro pc' sevm' devm' exn'
    cases exn'; {simp only [ifOk, implies_true]}
    apply ih
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
