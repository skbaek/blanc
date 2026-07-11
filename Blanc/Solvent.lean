-- Solvent.lean : proof of solvency for WETH implementation


import Blanc.Common
import Blanc.Weth
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
  (code : some (devm.getCode wa).toList = Prog.compile weth)
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
  | mk h_code h_nof h_solv =>
    have h_bal : devm'.getBal = devm.getBal := by
      funext a; simp [Devm.getBal, Devm.getAcct]; rw [h_eq]
    have h_stor : ∀ a, devm'.getStor a = devm.getStor a := by
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

instance {xs} {p : xs.length ≤ 32} : Ninst.Hinv Devm.getBal (Ninst.push xs p) := ⟨by
  intros e s s' h
  rcases h with ⟨xl, h_filled, pc, run⟩
  cases xl with
  | some _ => cases run
  | none =>
    dsimp [Ninst.Run'] at run
    have h_pb := Devm.pushBurn_of_run run
    funext a; simp only [Devm.getBal, Devm.getAcct]; rw [h_pb.state]
⟩

instance {xs} {p : xs.length ≤ 32} : Ninst.Hinv Devm.getStor (Ninst.push xs p) := ⟨by
  intros e s s' h
  rcases h with ⟨xl, h_filled, pc, run⟩
  cases xl with
  | some _ => cases run
  | none =>
    dsimp [Ninst.Run'] at run
    have h_pb := Devm.pushBurn_of_run run
    funext a; simp only [Devm.getStor, Devm.getAcct]; rw [h_pb.state]
⟩

instance {xs} {p : xs.length ≤ 32} : Ninst.Hinv Devm.getCode (Ninst.push xs p) := ⟨by
  intros e s s' h
  rcases h with ⟨xl, h_filled, pc, run⟩
  cases xl with
  | some _ => cases run
  | none =>
    dsimp [Ninst.Run'] at run
    have h_pb := Devm.pushBurn_of_run run
    funext a; simp only [Devm.getCode, Devm.getAcct]; rw [h_pb.state]
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

instance : Linst.Hinv Devm.getStor Devm.getStor Linst.rev := by
  constructor; intros e s r h
  simp only [Linst.Run, Linst.run] at h
  rcases of_bind_eq_ok h with ⟨v1, h1, h2⟩
  rcases of_bind_eq_ok h2 with ⟨v2, h3, h4⟩
  rcases of_bind_eq_ok h4 with ⟨v3, h5, h6⟩
  contradiction

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

lemma deposit_inv_bal : Func.Inv Devm.getBal Devm.getBal deposit := by prog_inv

lemma wbsum_after_deposit {sevm : Sevm} {s r : Devm}
    (h_nof : wbsum (s.getStor sevm.currentTarget) + sevm.value.toNat < 2 ^ 256)
    (run : Func.Run (weth.main :: weth.aux) sevm s deposit r) :
    wbsum (s.getStor sevm.currentTarget) + sevm.value.toNat = wbsum (r.getStor sevm.currentTarget) := by
  unfold deposit at run
  rcases of_run_next run with ⟨s1, h_caller, run1⟩
  rcases of_run_next run1 with ⟨s2, h_sload, run2⟩
  rcases of_run_next run2 with ⟨s3, h_callvalue, run3⟩
  rcases of_run_next run3 with ⟨s4, h_add, run4⟩
  rcases of_run_next run4 with ⟨s5, h_caller2, run5⟩
  rcases of_run_next run5 with ⟨s6, h_sstore, run6⟩
  have hp0 : [] <<+ s.stack := nil_pref
  have hp1 : [sevm.caller.toB256] <<+ s1.stack := prefix_of_push (of_run_caller h_caller) hp0
  have hs1 : s.getStor = s1.getStor := Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons h_caller Line.Run.nil)

  rcases prefix_of_sload' h_sload hp1 with ⟨cbal, hp2, hcbal⟩
  have hs2 : s1.getStor = s2.getStor := Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons h_sload Line.Run.nil)

  have hp3 : [sevm.value, cbal] <<+ s3.stack := prefix_of_push (of_run_callvalue h_callvalue) hp2
  have hs3 : s2.getStor = s3.getStor := Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons h_callvalue Line.Run.nil)

  have hp4 : [sevm.value + cbal] <<+ s4.stack := prefix_of_add h_add hp3
  have hs4 : s3.getStor = s4.getStor := Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons h_add Line.Run.nil)

  have hp5 : [sevm.caller.toB256, sevm.value + cbal] <<+ s5.stack := prefix_of_push (of_run_caller h_caller2) hp4
  have hs5 : s4.getStor = s5.getStor := Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons h_caller2 Line.Run.nil)

  have hs_eq : s.getStor = s5.getStor := by rw [hs1, hs2, hs3, hs4, hs5]
  have hcbal' : cbal = (s5.getStor sevm.currentTarget).get sevm.caller.toB256 := by
    rw [hcbal]; show (s1.getStor sevm.currentTarget).get sevm.caller.toB256 = _
    rw [hs2, hs3, hs4, hs5]

  have h_set : s6.getStor sevm.currentTarget = (s5.getStor sevm.currentTarget).set sevm.caller.toB256 (sevm.value + cbal) :=
    sstore_getStor_set h_sstore hp5

  have hs6 : s6.getStor = r.getStor := by apply Func.of_inv _ _ _ run6; prog_inv

  have h_incr : Increase sevm.caller sevm.value (s5.getStor sevm.currentTarget).rest (s6.getStor sevm.currentTarget).rest := by
    intro a
    constructor
    · intro h_eq
      simp [Stor.rest, ← h_eq, h_set, Stor.get_set_self]
      rw [← hcbal', B256.add_comm]
    · intro h_neq
      simp [Stor.rest, h_set]
      exact (Stor.get_set_ne (fun hc => h_neq (Adr.toB256_inj hc).symm)).symm

  have h_nof' : B256.Nof ((s5.getStor sevm.currentTarget).rest sevm.caller) sevm.value := by
    simp only [B256.Nof]
    apply lt_of_le_of_lt _ h_nof
    rw [hs_eq, Nat.add_le_add_iff_right]
    apply le_sum

  rw [hs_eq, ← hs6]
  exact sum_add_assoc h_incr h_nof'

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

lemma of_nof_of_transfer {a b : Adr} {v : B256} {f h : Adr → B256}
    (h_nof : SumNof f) (h_di : Transfer f a v b h) :
    ∃ g, Decrease a v f g ∧ Increase b v g h ∧ B256.Nof (g b) v := by
  rcases h_di with ⟨h_le, g, hd, hi⟩; refine' ⟨g, hd, hi, _⟩
  apply lt_of_le_of_lt _ h_nof
  by_cases h_ab : a = b
  · rw [← (hd b).left h_ab, ← h_ab, B256.toNat_sub_eq_of_le _ _ h_le]
    rw [Nat.sub_add_cancel (B256.toNat_le_toNat h_le)]
    exact le_sum
  · rw [← (hd b).right h_ab, Nat.add_comm]
    apply _root_.le_trans (Nat.add_le_add_right _ _) <| add_le_sum_of_ne f h_ab
    apply B256.toNat_le_toNat h_le

lemma B256.le_add_right {xs ys : B256} (h : B256.Nof xs ys) : xs ≤ xs + ys := by
  rw [B256.le_iff_toNat_le_toNat, B256.toNat_add_eq_of_nof _ _ h]; simp

lemma le_of_increase {k : Adr} {v : B256} {f g : Adr → B256}
    (h : Increase k v f g) (h' : B256.Nof (f k) v) : ∀ k', f k' ≤ g k' := by
  intro k'; by_cases h_eq : k = k'
  · rw [← h_eq]
    have h_rw : f k + v = g k := (h k).left rfl
    rw [← h_rw]; apply B256.le_add_right h'
  · rw [(h k').right h_eq]

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

lemma precond_of_precond {wa : Adr} {sevm : Sevm} {s s' : Devm}
    (h : Precond wa sevm s) (h_bal : s.getBal = s'.getBal)
    (h_stor : s.getStor = s'.getStor) (h_code : s.getCode = s'.getCode) :
    Precond wa sevm s' := by
  refine' ⟨_, _, _⟩
  · rw [← congr_fun h_code wa]; exact h.code
  · rw [← h_bal]; exact h.nof
  · unfold Devm.PreSolvent
    rw [← congr_fun h_stor wa, ← congr_fun h_bal wa]; exact h.solvent

lemma solvent_of_withdraw_update_bal' {sevm : Sevm} {s s' : Devm} {cbal wad}
    (h_pc : Precond sevm.currentTarget sevm s)
    (h_stk : [cbal, wad, wad] <<+ s.stack)
    (h_cbal : cbal = Devm.getStorVal s sevm.currentTarget sevm.caller.toB256)
    (h_le : wad ≤ cbal)
    (h_run : Line.Run sevm s [.sub, .caller, .sstore] s') :
    wad ≤ s'.getBal sevm.currentTarget ∧
    Stor.Solvent (s'.getStor sevm.currentTarget) 0 (s'.getBal sevm.currentTarget - wad) := by
  have h_cbal' : (s.getStor sevm.currentTarget).get sevm.caller.toB256 = cbal := h_cbal.symm
  have h_bal : s.getBal = s'.getBal := Line.of_inv Devm.getBal (by line_inv) h_run
  rcases Line.of_run_cons h_run with ⟨s₁, r_sub, h1⟩
  rcases Line.of_run_cons h1 with ⟨s₂, r_caller, h2⟩
  rcases Line.of_run_cons h2 with ⟨s₃, r_sstore, h3⟩
  cases h3
  clear h_run h1 h2
  -- sub : [cbal - wad, wad]
  have hp1 : (cbal - wad) :: [wad] <<+ s₁.stack := prefix_of_sub r_sub h_stk
  -- caller : [caller, cbal - wad, wad]
  have hp2 : [sevm.caller.toB256, cbal - wad, wad] <<+ s₂.stack :=
    prefix_of_push (of_run_caller r_caller) hp1
  -- sub and caller do not touch storage
  have h_stor : s.getStor = s₂.getStor :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons r_sub (Line.Run.cons r_caller Line.Run.nil))
  -- sstore : set caller's WETH balance to cbal - wad
  have h_set : s'.getStor sevm.currentTarget
      = (s₂.getStor sevm.currentTarget).set sevm.caller.toB256 (cbal - wad) :=
    sstore_getStor_set r_sstore hp2
  have h_dec : Decrease sevm.caller wad
      (s.getStor sevm.currentTarget).rest (s'.getStor sevm.currentTarget).rest := by
    intro a
    constructor
    · intro h_eq; subst h_eq
      simp only [Stor.rest, Function.comp_apply]
      rw [h_set, Stor.get_set_self, h_cbal']
    · intro h_ne
      simp only [Stor.rest, Function.comp_apply]
      rw [h_set]
      have h_key_ne : a.toB256 ≠ sevm.caller.toB256 := by
        intro hc; apply h_ne
        rw [← toAdr_toB256 a, hc, toAdr_toB256]
      rw [Stor.get_set_ne h_key_ne, h_stor]
  have h_le_rest : wad ≤ (s.getStor sevm.currentTarget).rest sevm.caller := by
    simp only [Stor.rest, Function.comp_apply]
    rw [h_cbal']; exact h_le
  have h_eq : wbsum (s.getStor sevm.currentTarget) - wad.toNat
      = wbsum (s'.getStor sevm.currentTarget) := sum_sub_assoc h_dec h_le_rest
  have h_le' : wad.toNat ≤ wbsum (s.getStor sevm.currentTarget) := by
    apply le_trans (B256.toNat_le_toNat h_le)
    have h := @le_sum (s.getStor sevm.currentTarget).rest sevm.caller
    simp only [Stor.rest, Function.comp_apply] at h
    rw [h_cbal'] at h
    exact h
  have h_solv := h_pc.solvent.left rfl
  unfold Stor.Solvent at h_solv
  have h_le_bal : wad.toNat ≤ (s.getBal sevm.currentTarget).toNat := by omega
  have h_le_bal' : wad ≤ s'.getBal sevm.currentTarget := by
    rw [← congr_fun h_bal sevm.currentTarget]
    exact B256.le_of_toNat_le_toNat h_le_bal
  refine' ⟨h_le_bal', _⟩
  unfold Stor.Solvent
  rw [B256.toNat_zero, Nat.add_zero, ← congr_fun h_bal sevm.currentTarget]
  rw [B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat h_le_bal), ← h_eq]
  omega

-- helper lemmas for reasoning about the balance transfer performed by `call`



lemma State.setBal_get_self {st : _root_.State} {adr : Adr} {v : B256} :
    (st.setBal adr v).get adr = (st.get adr).withBal v := State.get_set_self

lemma State.setBal_get_ne {st : _root_.State} {adr a : Adr} {v : B256} (h : adr ≠ a) :
    (st.setBal adr v).get a = st.get a := State.get_set_ne h

lemma State.setBal_get_stor {st : _root_.State} {b a : Adr} {v : B256} :
    ((st.setBal b v).get a).stor = (st.get a).stor := by
  by_cases h : b = a
  · subst h; rw [State.setBal_get_self]; rfl
  · rw [State.setBal_get_ne h]

lemma State.setBal_get_code {st : _root_.State} {b a : Adr} {v : B256} :
    ((st.setBal b v).get a).code = (st.get a).code := by
  by_cases h : b = a
  · subst h; rw [State.setBal_get_self]; rfl
  · rw [State.setBal_get_ne h]

lemma State.of_subBal {st st' : _root_.State} {ct : Adr} {wad : B256}
    (h : st.subBal ct wad = some st') :
    wad ≤ st.bal ct ∧ st' = st.setBal ct (st.bal ct - wad) := by
  unfold State.subBal at h
  split_ifs at h with h_lt
  cases h
  exact ⟨B256.not_lt.mp h_lt, rfl⟩

lemma of_state_transfer {st st' : _root_.State} {ct callee : Adr} {wad : B256}
    (h_sub : st.subBal ct wad = some st')
    (h_nof : sum st.bal < 2 ^ 256) :
    (∀ a, ((st'.addBal callee wad).get a).stor = (st.get a).stor) ∧
    (∀ a, ((st'.addBal callee wad).get a).code = (st.get a).code) ∧
    sum (st'.addBal callee wad).bal = sum st.bal ∧
    wad ≤ st.bal ct ∧
    (callee = ct → (st'.addBal callee wad).bal ct = st.bal ct) ∧
    (callee ≠ ct → (st'.addBal callee wad).bal ct = st.bal ct - wad) := by
  rcases State.of_subBal h_sub with ⟨h_le, h_st'⟩
  subst h_st'
  unfold State.addBal
  refine' ⟨_, _, _, h_le, _, _⟩
  · intro a; rw [State.setBal_get_stor, State.setBal_get_stor]
  · intro a; rw [State.setBal_get_code, State.setBal_get_code]
  · -- the total sum of balances is preserved by the transfer
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
  · intro h_eq; subst h_eq
    show ((_root_.State.setBal _ callee _).get callee).bal = _
    rw [State.setBal_get_self]
    show (st.setBal callee (st.bal callee - wad)).bal callee + wad = _
    show ((st.setBal callee (st.bal callee - wad)).get callee).bal + wad = _
    rw [State.setBal_get_self]
    show st.bal callee - wad + wad = _
    rw [B256.sub_add_cancel]
  · intro h_ne
    show ((_root_.State.setBal _ callee _).get ct).bal = _
    rw [State.setBal_get_ne h_ne]
    show ((st.setBal ct (st.bal ct - wad)).get ct).bal = _
    rw [State.setBal_get_self]; rfl

lemma Devm.pop_of_popToAdr {a : Adr} {devm devm' : Devm}
    (h : Devm.popToAdr devm = .ok ⟨a, devm'⟩) :
    ∃ x, x.toAdr = a ∧ Devm.pop devm = .ok ⟨x, devm'⟩ := by
  dsimp [Devm.popToAdr, Functor.map, Except.map] at h
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
  split_ifs <;> rfl

lemma accessDelegation_code_of_not {devm : Devm} {adr : Adr}
    (h : ¬ isValidDelegation (devm.state.getCode adr)) :
    (accessDelegation devm adr).2.2.1 = devm.state.getCode adr := by
  dsimp only [accessDelegation]
  rw [if_neg h]

lemma getStor_eq_of_state_eq {d d' : Devm} (h : d.state = d'.state) (a : Adr) :
    d.getStor a = d'.getStor a := by
  simp only [Devm.getStor, Devm.getAcct]; rw [h]

lemma getBal_eq_of_state_eq {d d' : Devm} (h : d.state = d'.state) (a : Adr) :
    d.getBal a = d'.getBal a := by
  simp only [Devm.getBal, Devm.getAcct]; rw [h]

lemma getCode_eq_of_state_eq {d d' : Devm} (h : d.state = d'.state) (a : Adr) :
    d.getCode a = d'.getCode a := by
  simp only [Devm.getCode, Devm.getAcct]; rw [h]

-- solvency is preserved when the state is unchanged, given that it was
-- already solvent with `wad` subtracted from the balance
lemma solvent_of_state_eq {sf s₁ : Devm} {ct : Adr} {wad : B256}
    (h_state : sf.state = s₁.state)
    (h_le : wad ≤ s₁.getBal ct)
    (h_sv : Stor.Solvent (s₁.getStor ct) 0 (s₁.getBal ct - wad)) :
    Stor.Solvent (sf.getStor ct) 0 (sf.getBal ct) := by
  rw [getStor_eq_of_state_eq h_state, getBal_eq_of_state_eq h_state]
  unfold Stor.Solvent at *
  rw [B256.toNat_sub_eq_of_le _ _ h_le] at h_sv
  omega

lemma state_of_push_split {d sf : Devm} {v : B256} {idx : Nat} {out : B8L}
    (h : (d.push v).Split (Except.ok sf)
      (fun evm2 => (Except.ok (evm2.memWrite idx out) : Execution) = Except.ok sf)) :
    sf.state = d.state := by
  rcases h with ⟨x, _, h_contra⟩ | ⟨evm2, h_push, h_sf⟩
  · cases h_contra
  · injection h_sf with h_sf
    rw [← h_sf]
    exact ((Devm.push_of_push h_push).state).symm

lemma of_handleError_err {err : String} {d : Devm}
    {ex : Except (String × _root_.State × AdrSet × Tra) Devm}
    (h : executeCode.handleError (.error ⟨err, d⟩) = ex) :
    (∃ evm2 : Devm, ex = .ok evm2 ∧ evm2.error.isSome = true ∧ evm2.state = d.state) ∨
    (∃ e, ex = .error e) := by
  simp only [executeCode.handleError] at h
  split_ifs at h
  · exact Or.inl ⟨_, h.symm, rfl, rfl⟩
  · exact Or.inl ⟨_, h.symm, rfl, rfl⟩
  · exact Or.inr ⟨_, h.symm⟩

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
    {ex : Except (String × _root_.State × AdrSet × Tra) Devm}
    (h_ca : msg.codeAddress = some adr)
    (h : ExecuteCode msg xl ex) :
    (adr.isPrecomp ∧ xl = .none ∧
      executeCode.handleError (executePrecomp (initEvm msg) adr) = ex) ∨
    (¬ adr.isPrecomp ∧ ∃ ex', xl = .some ⟨initSevm msg, initDevm msg, ex'⟩ ∧
      executeCode.handleError ex' = ex) := by
  unfold ExecuteCode at h
  rw [h_ca] at h
  dsimp only [initEvm] at h
  split_ifs at h with h_pre
  · exact Or.inl ⟨h_pre, h⟩
  · exact Or.inr ⟨h_pre, h⟩

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

lemma of_send_to_caller' {sevm : Sevm} {s sf : Devm} {wad}
    (ih : Exec.InvDepth sevm.depth sevm.currentTarget weth
      (Precond sevm.currentTarget) (Postcond sevm.currentTarget))
    (hp : [wad] <<+ s.stack)
    (h_code : some (s.getCode sevm.currentTarget).toList = Prog.compile weth)
    (h_nof : sum s.getBal < 2 ^ 256)
    (h_le : wad ≤ s.getBal sevm.currentTarget)
    (h_sv : Stor.Solvent (s.getStor sevm.currentTarget) 0 (s.getBal sevm.currentTarget - wad)) :
    Line.Run sevm s sendToCaller sf →
    Stor.Solvent (sf.getStor sevm.currentTarget) 0 (sf.getBal sevm.currentTarget) := by
  lexen 7
  have hs₁ : [0, sevm.caller.toB256, wad, 0, 0, 0, 0] <<+ s₁.stack := by
    lpfx
  -- transport the hypotheses to s₁
  have h_bal₁ : s.getBal = s₁.getBal := Line.of_inv Devm.getBal (by line_inv) h₁
  have h_stor₁ : s.getStor = s₁.getStor := Line.of_inv Devm.getStor (by line_inv) h₁
  have h_code₁ : s.getCode = s₁.getCode := Line.of_inv Devm.getCode (by line_inv) h₁
  rw [h_bal₁] at h_nof
  rw [congr_fun h_bal₁ sevm.currentTarget] at h_le h_sv
  rw [congr_fun h_stor₁ sevm.currentTarget] at h_sv
  rw [congr_fun h_code₁ sevm.currentTarget] at h_code
  clear h_bal₁ h_stor₁ h_code₁ h₁ hp s
  -- the call instruction
  intro h₂
  rcases of_run_singleton h₂ with ⟨xl, h_fill, pc, h_run⟩
  dsimp only [Ninst.Run'] at h_run
  dsimp only [Xinst.Run] at h_run
  -- pop gas
  rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨gas, devm1⟩, eq1, h_run⟩; · cases h_contra
  have e1 := (Devm.pop_of_pop eq1).stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1
  rw [e1] at hs₁
  have h_gas : (0 : B256) = gas :=
    pref_head_unique hs₁ (pref_append [gas] devm1.stack)
  subst h_gas
  have hs₂ : [sevm.caller.toB256, wad, 0, 0, 0, 0] <<+ devm1.stack := cons_pref_cons_inv hs₁
  -- pop callee
  rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨callee, devm2⟩, eq2, h_run⟩; · cases h_contra
  rcases Devm.pop_of_popToAdr eq2 with ⟨x, hx, h_pop2⟩
  have e2 := (Devm.pop_of_pop h_pop2).stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e2
  rw [e2] at hs₂
  have h_x : sevm.caller.toB256 = x := pref_head_unique hs₂ (pref_append [x] devm2.stack)
  subst h_x
  rw [toAdr_toB256] at hx
  subst hx
  have hs₃ : [wad, 0, 0, 0, 0] <<+ devm2.stack := cons_pref_cons_inv hs₂
  -- pop value
  rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨value, devm3⟩, eq3, h_run⟩; · cases h_contra
  have e3 := (Devm.pop_of_pop eq3).stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e3
  rw [e3] at hs₃
  have h_wad : wad = value := pref_head_unique hs₃ (pref_append [value] devm3.stack)
  subst h_wad
  -- pop the four indices/sizes
  rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨inputIndex, devm4⟩, eq4, h_run⟩; · cases h_contra
  rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨inputSize, devm5⟩, eq5, h_run⟩; · cases h_contra
  rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨outputIndex, devm6⟩, eq6, h_run⟩; · cases h_contra
  rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨outputSize, devm7⟩, eq7, h_run⟩; · cases h_contra
  -- state is unchanged by the seven pops
  rcases Devm.pop_of_popToNat eq4 with ⟨_, h_pop4⟩
  rcases Devm.pop_of_popToNat eq5 with ⟨_, h_pop5⟩
  rcases Devm.pop_of_popToNat eq6 with ⟨_, h_pop6⟩
  rcases Devm.pop_of_popToNat eq7 with ⟨_, h_pop7⟩
  have h_st7 : s₁.state = devm7.state :=
    ((Devm.pop_of_pop eq1).state).trans
      (((Devm.pop_of_pop h_pop2).state).trans
        (((Devm.pop_of_pop eq3).state).trans
          ((h_pop4.state).trans
            ((h_pop5.state).trans ((h_pop6.state).trans h_pop7.state)))))
  clear e1 e2 e3 hs₁ hs₂ hs₃ eq1 eq2 eq3 eq4 eq5 eq6 eq7
  clear h_pop2 h_pop4 h_pop5 h_pop6 h_pop7 h₂
  -- gas/access bookkeeping
  rcases h_run with ⟨extendCost, hp8, h_run⟩
  rcases h_run with ⟨preAccessCost, hp9, h_run⟩
  rcases h_run with ⟨devm8, hp10, h_run⟩
  subst hp10
  rcases h_run with ⟨⟨dp, na, code0, dagc, devm9⟩, hp11, h_run⟩
  rcases h_run with ⟨accessCost, hp12, h_run⟩
  rcases h_run with ⟨createCost, hp13, h_run⟩
  rcases h_run with ⟨transferCost, hp14, h_run⟩
  rcases h_run with ⟨⟨msgCallCost, msgCallStipend⟩, hp15, h_run⟩
  rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨devm10, eq16, h_run⟩; · cases h_contra
  rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨_, _, h_run⟩; · cases h_contra
  rcases h_run with ⟨devm11, hp18, h_run⟩
  subst hp18
  rcases h_run with ⟨senderBal, hp19, h_run⟩
  -- state facts through the bookkeeping steps
  have h_st9 : devm9.state = devm7.state := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).state) hp11
    dsimp at h
    rw [h, accessDelegation_state]
    rfl
  have h_code0 : code0 = (accessDelegation (addAccessedAddress devm7 sevm.caller) sevm.caller).2.2.1 := by
    have h := congrArg (fun q => (q.2.2.1 : ByteArray)) hp11
    dsimp at h
    exact h
  have h_st10 : devm9.state = devm10.state := (Devm.burn_of_chargeGas eq16).state
  have h_st11 : (devm10.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).state = s₁.state := by
    show devm10.state = s₁.state
    rw [← h_st10, h_st9, ← h_st7]
  have h_st_devm7 : devm7.state = s₁.state := h_st7.symm
  clear hp8 hp9 hp12 hp13 hp14 hp15 eq16 h_st10 h_st9 h_st7
  split_ifs at h_run with h_sb
  · -- insufficient balance : call fails, state unchanged
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨devm12, eq20, h_run⟩; · cases h_contra
    rcases h_run with ⟨h_xl, h_ex⟩
    have h_ex := Except.ok.inj h_ex
    apply solvent_of_state_eq _ h_le h_sv
    rw [← h_ex]
    show devm12.state = s₁.state
    rw [← (Devm.push_of_push eq20).state]
    exact h_st11
  · -- balance is sufficient : the call goes through
    dsimp only [GenericCall] at h_run
    rcases h_run with ⟨evm1, hp_evm1, h_run⟩
    subst hp_evm1
    split_ifs at h_run with h_depth
    · -- depth limit reached : call fails, state unchanged
      rcases h_run with ⟨h_xl, h_push⟩
      apply solvent_of_state_eq _ h_le h_sv
      rw [← (Devm.push_of_push h_push).state]
      exact h_st11
    · -- the call is executed
      rcases h_run with ⟨calldata, hp_cd, h_run⟩
      rcases h_run with ⟨childMsg, hp_cm, h_run⟩
      rcases h_run with ⟨ex', run_pm, h_split⟩
      -- extract the projections of childMsg we need, keeping childMsg abstract
      have hc_stv : childMsg.shouldTransferValue = true := by rw [hp_cm]; rfl
      have hc_state : childMsg.benv.state = s₁.state := by rw [hp_cm]; exact h_st11
      have hc_caller : childMsg.caller = sevm.currentTarget := by rw [hp_cm]; rfl
      have hc_value : childMsg.value = wad := by rw [hp_cm]; rfl
      have hc_ct : childMsg.currentTarget = sevm.caller := by rw [hp_cm]; rfl
      have hc_ca : childMsg.codeAddress = some sevm.caller := by rw [hp_cm]; rfl
      have hc_code : childMsg.code = code0 := by rw [hp_cm]; rfl
      have hc_depth : childMsg.depth = sevm.depth - 1 := by rw [hp_cm]; rfl
      clear hp_cm hp_cd
      -- resolve the outer split : the sub-message result must be ok
      rcases ex' with err' | child
      · obtain ⟨e1, e2, e3, e4⟩ := err'
        dsimp only [liftToExecution] at h_split
        rcases h_split with ⟨x, _, h_contra⟩ | ⟨c, h_contra, _⟩ <;> cases h_contra
      dsimp only [liftToExecution] at h_split
      rcases h_split with ⟨x, h_contra, _⟩ | ⟨c, h_c, h_body⟩
      · cases h_contra
      cases h_c
      have h_sf_state : sf.state = child.state := by
        by_cases h_err : child.error.isSome = true
        · rw [if_pos h_err] at h_body
          have h := state_of_push_split h_body; exact h
        · rw [if_neg h_err] at h_body
          have h := state_of_push_split h_body; exact h
      clear h_body
      -- unpack the process-message run
      dsimp only [ProcessMessage] at run_pm
      rcases run_pm with ⟨errv, _, h_contra, _⟩ | ⟨benv', eq_bt, run_pm⟩
      · cases h_contra
      rcases run_pm with ⟨ex'', run_ec, h_split2⟩
      -- the value transfer performed before the sub-message run
      rcases of_benvAfterTransfer hc_stv eq_bt with ⟨st_mid, h_sub, hB⟩
      rw [hc_state, hc_caller, hc_value] at h_sub
      have h_nof' : sum s₁.state.bal < 2 ^ 256 := h_nof
      rcases of_state_transfer (callee := sevm.caller) h_sub h_nof' with
        ⟨h_t_stor, h_t_code, h_t_sum, h_t_le, h_t_self, h_t_ne⟩
      have hBs : benv'.state = st_mid.addBal sevm.caller wad := by
        rw [hB, hc_ct, hc_value]; rfl
      -- resolve the inner split : either rollback or a clean sub-message result
      rcases h_split2 with ⟨x, _, h_contra⟩ | ⟨evm2, h_ex'', h_if⟩
      · cases h_contra
      by_cases h_err2 : evm2.error.isSome = true
      · -- sub-message failed : state rolled back to the pre-transfer state
        rw [if_pos h_err2] at h_if
        have h_if := Except.ok.inj h_if
        apply solvent_of_state_eq _ h_le h_sv
        rw [h_sf_state, ← h_if]
        show childMsg.benv.state = s₁.state
        exact hc_state
      -- sub-message succeeded
      rw [if_neg h_err2] at h_if
      have h_if := (Except.ok.inj h_if).symm
      subst h_if
      subst h_ex''
      have h_wb_ca : (childMsg.withBenv benv').codeAddress = some sevm.caller := hc_ca
      rcases of_executeCode_someCode h_wb_ca run_ec with
        ⟨h_prec, h_xl_none, h_he⟩ | ⟨h_prec, ex''', h_xl_some, h_he⟩
      · -- callee is a precompile : no sub-execution, only the transfer
        have h_child_state : child.state = benv'.state := by
          have h := state_of_executePrecomp_ok h_he h_err2
          rw [h]; rfl
        have h_stor_eq : sf.getStor sevm.currentTarget = s₁.getStor sevm.currentTarget := by
          show (sf.state.get sevm.currentTarget).stor = (s₁.state.get sevm.currentTarget).stor
          rw [h_sf_state, h_child_state, hBs]
          exact h_t_stor sevm.currentTarget
        have h_bal_eq : sf.getBal sevm.currentTarget = benv'.state.bal sevm.currentTarget := by
          show (sf.state.get sevm.currentTarget).bal = (benv'.state.get sevm.currentTarget).bal
          rw [h_sf_state, h_child_state]
        rw [h_stor_eq, h_bal_eq, hBs]
        by_cases h_callee : sevm.caller = sevm.currentTarget
        · rw [h_t_self h_callee]
          unfold Stor.Solvent at h_sv ⊢
          rw [B256.toNat_sub_eq_of_le _ _ h_le] at h_sv
          have h_defeq : (s₁.state.bal sevm.currentTarget).toNat = (s₁.getBal sevm.currentTarget).toNat := rfl
          omega
        · rw [h_t_ne h_callee]
          exact h_sv
      · -- callee is a regular account : a sub-execution takes place
        rw [h_xl_some] at h_fill
        dsimp only [Xlot.Filled] at h_fill
        rcases ex''' with ⟨err3, d3⟩ | child3
        · -- sub-execution error : contradicts the clean sub-message result
          rcases of_handleError_err h_he with ⟨evm4, h_ok4, h_some4, _⟩ | ⟨e, h_err4⟩
          · have h_ok4 := Except.ok.inj h_ok4
            rw [← h_ok4] at h_some4
            exact absurd h_some4 h_err2
          · cases h_err4
        -- clean sub-execution : apply the induction hypothesis
        simp only [executeCode.handleError] at h_he
        have h_he := (Except.ok.inj h_he).symm
        subst h_he
        obtain ⟨ex_sub⟩ := h_fill
        -- abbreviations for the sub-message's initial sevm/devm
        have h_sd_state : (initDevm (childMsg.withBenv benv')).state = benv'.state := rfl
        have h_ss_ct : (initSevm (childMsg.withBenv benv')).currentTarget = sevm.caller := hc_ct
        -- code at the target is the WETH code
        have h_code_at :
            some ((initDevm (childMsg.withBenv benv')).getCode sevm.currentTarget).toList
              = weth.compile := by
          show some ((initDevm (childMsg.withBenv benv')).state.get sevm.currentTarget).code.toList
            = weth.compile
          rw [h_sd_state, hBs, h_t_code sevm.currentTarget]
          exact h_code
        -- the target program invariant for the sub-execution
        have h_at : Prog.At weth sevm.currentTarget 0
            (initSevm (childMsg.withBenv benv')) (initDevm (childMsg.withBenv benv')) := by
          refine ⟨h_code_at, ?_⟩
          intro h_eq_ct
          rw [h_ss_ct] at h_eq_ct
          refine ⟨?_, rfl⟩
          show some (initSevm (childMsg.withBenv benv')).code.toList = weth.compile
          have h_code_c : (initSevm (childMsg.withBenv benv')).code = code0 := hc_code
          rw [h_code_c, h_code0]
          have h_ad : (addAccessedAddress devm7 sevm.caller).state.getCode sevm.caller
              = s₁.getCode sevm.currentTarget := by
            show devm7.state.getCode sevm.caller = s₁.getCode sevm.currentTarget
            rw [h_st_devm7, h_eq_ct]; rfl
          have h_notdel : ¬ isValidDelegation
              ((addAccessedAddress devm7 sevm.caller).state.getCode sevm.caller) := by
            rw [h_ad]; exact not_delegation_of_compile h_code
          rw [accessDelegation_code_of_not h_notdel, h_ad]
          exact h_code
        -- the depth of the sub-execution is strictly smaller
        have h_depth_lt : (initSevm (childMsg.withBenv benv')).depth < sevm.depth := by
          have h_dep : (initSevm (childMsg.withBenv benv')).depth = sevm.depth - 1 := hc_depth
          rw [h_dep]; omega
        -- the precondition holds for the sub-message
        have h_gs : (initDevm (childMsg.withBenv benv')).getStor sevm.currentTarget
            = s₁.getStor sevm.currentTarget := by
          show ((initDevm (childMsg.withBenv benv')).state.get sevm.currentTarget).stor
            = (s₁.state.get sevm.currentTarget).stor
          rw [h_sd_state, hBs, h_t_stor sevm.currentTarget]
        have h_precond : Precond sevm.currentTarget
            (initSevm (childMsg.withBenv benv')) (initDevm (childMsg.withBenv benv')) := by
          refine ⟨h_code_at, ?_, ?_⟩
          · -- nof
            have h_gb_fun : (initDevm (childMsg.withBenv benv')).getBal = benv'.state.bal := by
              funext a
              show ((initDevm (childMsg.withBenv benv')).state.get a).bal = (benv'.state.get a).bal
              rw [h_sd_state]
            rw [h_gb_fun, hBs, h_t_sum]; exact h_nof
          · -- PreSolvent
            refine ⟨?_, ?_⟩
            · intro h_eq
              rw [h_ss_ct] at h_eq
              have h_gv : (initSevm (childMsg.withBenv benv')).value = wad := hc_value
              rw [h_gs, h_gv]
              have h_gb : (initDevm (childMsg.withBenv benv')).getBal sevm.currentTarget
                  = s₁.getBal sevm.currentTarget := by
                show ((initDevm (childMsg.withBenv benv')).state.get sevm.currentTarget).bal
                  = (s₁.state.get sevm.currentTarget).bal
                rw [h_sd_state, hBs]
                show (st_mid.addBal sevm.caller wad).bal sevm.currentTarget
                  = (s₁.state.get sevm.currentTarget).bal
                rw [h_t_self h_eq]; rfl
              rw [h_gb]
              unfold Stor.Solvent at h_sv ⊢
              rw [B256.toNat_zero, Nat.add_zero] at h_sv
              rw [B256.toNat_sub_eq_of_le _ _ h_le] at h_sv
              have := B256.toNat_le_toNat h_le
              omega
            · intro h_ne
              rw [h_ss_ct] at h_ne
              rw [h_gs]
              have h_gb : (initDevm (childMsg.withBenv benv')).getBal sevm.currentTarget
                  = s₁.getBal sevm.currentTarget - wad := by
                show ((initDevm (childMsg.withBenv benv')).state.get sevm.currentTarget).bal
                  = s₁.getBal sevm.currentTarget - wad
                rw [h_sd_state, hBs]
                show (st_mid.addBal sevm.caller wad).bal sevm.currentTarget
                  = s₁.getBal sevm.currentTarget - wad
                rw [h_t_ne h_ne]; rfl
              rw [h_gb]; exact h_sv
        -- apply the induction hypothesis
        have hpost : Postcond sevm.currentTarget (initSevm (childMsg.withBenv benv')) child :=
          ih 0 (initSevm (childMsg.withBenv benv')) (initDevm (childMsg.withBenv benv'))
            (.ok child) ex_sub h_depth_lt h_at h_precond
        rw [getStor_eq_of_state_eq h_sf_state sevm.currentTarget,
            getBal_eq_of_state_eq h_sf_state sevm.currentTarget]
        exact hpost.solvent

lemma withdraw_inv_solvent {sevm : Sevm} {s r : Devm}
    (cond : Precond sevm.currentTarget sevm s)
    (ih : Exec.InvDepth sevm.depth sevm.currentTarget weth (Precond sevm.currentTarget) (Postcond sevm.currentTarget))
    (run : Func.Run (weth.main :: weth.aux) sevm s withdraw r) :
    r.PostSolvent sevm.currentTarget := by
  revert run
  pexec withdrawLoadCheck
  rcases of_withdrawLoadCheck h₁ with ⟨h_bal, h_stor, h_code, wad, cbal, hp₁, h_cbal⟩
  have cond₁ : Precond sevm.currentTarget sevm s₁ :=
    precond_of_precond cond h_bal h_stor h_code
  clear cond h₁ h_bal h_stor h_code
  intro h_run
  -- rev-branch : the caller's WETH balance must cover the withdrawal
  rcases of_run_branch_rev h_run with ⟨s₂, h_pop, h_run'⟩
  have hp2s := h_pop.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp2s
  rw [hp2s] at hp₁
  have h_ltflag : (cbal <? wad) = 0 := pref_head_unique hp₁ (pref_append [0] s₂.stack)
  have h_wad : wad ≤ cbal := by
    rw [← B256.not_lt]; intro hlt
    rw [B256.lt_check, if_pos hlt] at h_ltflag
    exact B256.zero_ne_one h_ltflag.symm
  rw [h_ltflag] at hp₁
  have hp₂ : [cbal, wad, wad] <<+ s₂.stack := cons_pref_cons_inv hp₁
  have cond₂ : Precond sevm.currentTarget sevm s₂ :=
    Precond.state_eq cond₁ h_pop.state.symm
  have h_cbal₂ : cbal = Devm.getStorVal s₂ sevm.currentTarget sevm.caller.toB256 := by
    rw [h_cbal]
    show (s₁.getStor sevm.currentTarget).get sevm.caller.toB256
      = (s₂.getStor sevm.currentTarget).get sevm.caller.toB256
    rw [Devm.PopBurn.getStor h_pop sevm.currentTarget]
  clear h_cbal hp₁ hp2s h_ltflag cond₁ h_run
  -- update the caller's WETH balance in storage
  revert h_run'
  pexen 3
  rcases solvent_of_withdraw_update_bal' cond₂ hp₂ h_cbal₂ h_wad h₃ with ⟨h_le, h_sv⟩
  have h_code₃ : some (s₃.getCode sevm.currentTarget).toList = Prog.compile weth := by
    rw [← congr_fun (Line.of_inv Devm.getCode (by line_inv) h₃) sevm.currentTarget]
    exact cond₂.code
  have h_nof₃ : sum s₃.getBal < 2 ^ 256 := by
    rw [← Line.of_inv Devm.getBal (by line_inv) h₃]
    exact cond₂.nof
  have hp₃ : [wad] <<+ s₃.stack := by lpfx
  -- send the withdrawn amount to the caller
  pexec sendToCaller
  intro h₅
  unfold Devm.PostSolvent
  rw [← congr_fun (Func.of_inv Devm.getStor Devm.getStor (by prog_inv) h₅) sevm.currentTarget]
  rw [← congr_fun (Func.of_inv Devm.getBal Devm.getBal (by prog_inv) h₅) sevm.currentTarget]
  exact of_send_to_caller' ih hp₃ h_code₃ h_nof₃ h_le h_sv h₄

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

lemma transfer_inv_bal : Func.Inv Devm.getBal Devm.getBal transfer := by prog_inv

lemma of_transferTestDst {sevm : Sevm} {s s' : Devm} :
    Line.Run sevm s transferTestDst s' →
    ∃ na_dst dst,
      ([na_dst, dst] <<+ s'.stack) ∧
      (na_dst = 0 ↔ ValidAdr dst) := by
  simp only [transferTestDst]
  lexec (arg 0)
  rcases prefix_of_cdl nil_pref h₁ with ⟨dst, hp₁⟩
  clear h₁
  lexen 1
  have hp₂ : [dst, dst] <<+ s₂.stack := by lpfx
  clear hp₁ h₂
  intro h
  rcases of_check_non_address hp₂ h with ⟨na_dst, h_pfx, h_iff⟩
  exact ⟨_, _, h_pfx, h_iff⟩

lemma of_transferTestLt {sevm : Sevm} {s s' : Devm} {dst}
    (h_stk : [dst] <<+ s.stack) :
    Line.Run sevm s transferTestLt s' →
    ∃ lt? caller wad,
      ([lt?, caller, Devm.getStorVal s' sevm.currentTarget caller - wad, wad, dst] <<+ s'.stack) ∧
      (lt? = 0 ↔ wad ≤ Devm.getStorVal s' sevm.currentTarget caller) ∧
      ValidAdr caller := by
  simp only [transferTestLt]
  -- arg 1 : push wad
  lexec (arg 1)
  rcases prefix_of_cdl h_stk h₁ with ⟨wad, hp₁⟩
  clear h₁
  -- caller, dup 0 : [caller, caller, wad, dst]
  lexen 2
  have hp₂ : [sevm.caller.toB256, sevm.caller.toB256, wad, dst] <<+ s₂.stack := by lpfx
  clear h₂
  -- sload : [cbal, caller, wad, dst]
  lexen 1
  rcases prefix_of_sload' (of_run_singleton h₃) hp₂ with ⟨cbal, hp₃, h_cbal⟩
  have hstor23 : s₂.getStor = s₃.getStor := Line.of_inv Devm.getStor (by line_inv) h₃
  clear h₃
  -- swap 0, dup 2, dup 0, dup 3, sub, swap 2, lt :
  --   [cbal <? wad, caller, cbal - wad, wad, dst]
  intro h₄
  have hp₄ : [cbal <? wad, sevm.caller.toB256, cbal - wad, wad, dst] <<+ s'.stack := by lpfx
  have hstor34 : s₃.getStor = s'.getStor := Line.of_inv Devm.getStor (by line_inv) h₄
  have h_cbal' : cbal = Devm.getStorVal s' sevm.currentTarget sevm.caller.toB256 := by
    rw [h_cbal]
    show (s₂.getStor _).get _ = (s'.getStor _).get _
    rw [hstor23, hstor34]
  refine ⟨cbal <? wad, sevm.caller.toB256, wad, ?_, ?_, validAdr_toB256 sevm.caller⟩
  · rw [← h_cbal']; exact hp₄
  · rw [← h_cbal', B256.lt_check, Ne.ite_eq_right_iff B256.zero_ne_one.symm, B256.not_lt]

lemma transfer_of_transfer {fs : List Func} {sevm : Sevm} {s r : Devm} :
    Func.Run fs sevm s transfer r →
    ∃ (x : B256) (a a' : Adr),
      Transfer (s.getStor sevm.currentTarget).rest a x a'
        (r.getStor sevm.currentTarget).rest := by
  intro h_run
  simp only [transfer] at h_run
  -- transferTestDst : [dst_invalid?, dst]
  rcases of_run_prepend transferTestDst _ h_run with ⟨s1, h1, h_run⟩
  rcases of_transferTestDst h1 with ⟨dst_invalid, dst, hp1, h_dst⟩
  have hg1 : s.getStor = s1.getStor := Line.of_inv Devm.getStor (by line_inv) h1
  clear h1
  -- rev-branch : dst is a valid address
  rcases of_run_branch_rev h_run with ⟨s2, hp2b, h_run⟩
  have hp2bs := hp2b.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp2bs
  rw [hp2bs] at hp1
  have h_dst_valid : ValidAdr dst := h_dst.mp (pref_head_unique hp1 (pref_append [0] s2.stack))
  rw [pref_head_unique hp1 (pref_append [0] s2.stack)] at hp1
  have hp2 : [dst] <<+ s2.stack := cons_pref_cons_inv hp1
  have hg2 : s.getStor = s2.getStor :=
    hg1.trans (funext (fun a => (Devm.PopBurn.getStor hp2b a).symm))
  clear hp1 hp2bs hp2b h_dst
  -- transferTestLt : [lt?, caller, cbal - wad, wad, dst]
  rcases of_run_prepend transferTestLt _ h_run with ⟨s3, h3, h_run⟩
  rcases of_transferTestLt hp2 h3 with ⟨lt?, caller, wad, hp3, h_le, h_caller⟩
  have hg3 : s.getStor = s3.getStor :=
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
  have hg4 : s.getStor = s4.getStor :=
    hg3.trans (funext (fun a => (Devm.PopBurn.getStor hp4b a).symm))
  clear hp3 hp4bs hp4b h_le h_lt0
  -- transferCore : sstore ::: incrWbal +++ logTransfer +++ returnTrue
  simp only [transferCore] at h_run
  -- sstore : set caller's WETH balance to cbal - wad
  rcases of_run_next h_run with ⟨s5, r5, h_run⟩
  have h_set : s5.getStor sevm.currentTarget
      = (s4.getStor sevm.currentTarget).set caller
          (Devm.getStorVal s3 sevm.currentTarget caller - wad) :=
    sstore_getStor_set r5 hp4
  have hp5 : [wad, dst] <<+ s5.stack := prefix_of_sstore r5 hp4
  clear hp4
  -- incrWbal : increase destination balance
  rcases of_run_prepend incrWbal _ h_run with ⟨s6, h6, h_run⟩
  have h_incr : Increase dst.toAdr wad (s5.getStor sevm.currentTarget).rest
      (s6.getStor sevm.currentTarget).rest :=
    incrAt_of_incrWbal h_dst_valid h6 hp5
  -- logTransfer, returnTrue : do not touch storage
  have h_rest : s6.getStor sevm.currentTarget = r.getStor sevm.currentTarget :=
    congr_fun (Func.of_inv Devm.getStor Devm.getStor (by prog_inv) h_run) sevm.currentTarget
  -- assemble the Transfer
  refine ⟨wad, caller.toAdr, dst.toAdr, ?_, (s5.getStor sevm.currentTarget).rest, ?_, ?_⟩
  · show wad ≤ (s.getStor sevm.currentTarget).rest caller.toAdr
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
      rw [Stor.get_set_ne h_key_ne, congr_fun hg4 sevm.currentTarget]
  · rw [← h_rest]; exact h_incr

lemma transfer_inv_solvent' {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s transfer r)
    (h_sv : s.PreSolvent sevm.currentTarget sevm) :
    r.PostSolvent sevm.currentTarget := by
  rcases transfer_of_transfer run with ⟨x, a, a', h_di⟩
  refine result_solvent_of_state_solvent' h_sv ?_ ?_
  · exact transfer_inv_sum (nof_of_solvent h_sv) h_di
  · exact congr_fun (Func.of_inv Devm.getBal Devm.getBal transfer_inv_bal run)
      sevm.currentTarget

lemma allowance_inv_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s allowance r)
    (h_sv : s.PreSolvent sevm.currentTarget sevm) :
    r.PostSolvent sevm.currentTarget := by simple_solvent

lemma Linst.inv_nof {sevm : Sevm} {s r : Devm} {o : Linst}
    (h : Linst.Run sevm s o (.ok r)) (h_nof : sum s.getBal < 2 ^ 256) :
    sum r.getBal < 2 ^ 256 := by
  cases o
  case stop => cases h; exact h_nof
  case ret =>
    have h_bal : s.getBal = r.getBal :=
      (inferInstanceAs (Linst.Hinv Devm.getBal Devm.getBal Linst.ret)).inv h
    rw [← h_bal]
    exact h_nof
  case rev =>
    dsimp [Linst.Run, Linst.run] at h
    rcases of_bind_eq_ok h with ⟨_, _, h2⟩
    rcases of_bind_eq_ok h2 with ⟨_, _, h4⟩
    rcases of_bind_eq_ok h4 with ⟨_, _, h6⟩
    contradiction
  case dest =>
    dsimp [Linst.Run, Linst.run] at h
    rcases of_bind_eq_ok h with ⟨⟨dest_a, devm1⟩, h_pop, h_run1⟩
    rcases of_bind_eq_ok h_run1 with ⟨devm2, h_charge, h_run2⟩
    rcases of_bind_eq_ok h_run2 with ⟨_, h_assert, h_run3⟩
    rcases of_bind_eq_ok h_run3 with ⟨devm3, h_sub, h_run4⟩
    have h_sub_some : devm2.subBal sevm.currentTarget ((dest_a, devm1).2.getAcct sevm.currentTarget).bal = some devm3 := by
      cases eq : devm2.subBal sevm.currentTarget ((dest_a, devm1).2.getAcct sevm.currentTarget).bal
      · rw [eq] at h_sub; contradiction
      · rw [eq] at h_sub; injection h_sub with h'; subst h'; rfl
    have h_sub_st : devm2.state.subBal sevm.currentTarget ((dest_a, devm1).2.getAcct sevm.currentTarget).bal = some devm3.state := by
      dsimp [Devm.subBal, Option.bind] at h_sub_some
      cases hq : devm2.state.subBal sevm.currentTarget ((dest_a, devm1).2.getAcct sevm.currentTarget).bal
      · rw [hq] at h_sub_some; contradiction
      · rw [hq] at h_sub_some; injection h_sub_some with h'; subst h'; rfl
    have h_bal1 : devm1.getBal = s.getBal := by
      funext a; exact Devm.popToAdr_getBal_eq h_pop a
    have h_bal2 : devm2.getBal = devm1.getBal := by
      ext a
      have := chargeGas_getBal_eq h_charge a
      rw [this]
      split
      · rfl
      · rfl
    have h_nof2 : sum devm2.state.bal < 2 ^ 256 := by
      have h_eq : devm2.state.bal = s.getBal := h_bal2.trans h_bal1
      rw [h_eq]; exact h_nof
    rcases of_state_transfer h_sub_st h_nof2 with ⟨_, _, h_sum, _, _, _⟩
    have h_bal4 : (devm3.addBal dest_a ((dest_a, devm1).2.getAcct sevm.currentTarget).bal).getBal
        = (devm3.state.addBal dest_a ((dest_a, devm1).2.getAcct sevm.currentTarget).bal).bal := rfl
    have h_nof4 : sum (devm3.addBal dest_a ((dest_a, devm1).2.getAcct sevm.currentTarget).bal).getBal < 2 ^ 256 := by
      rw [h_bal4, h_sum]; exact h_nof2
    split at h_run4
    · rw [← Except.ok.inj h_run4]
      set devm4 := devm3.addBal dest_a ((dest_a, devm1).2.getAcct sevm.currentTarget).bal with h_devm4
      have h_bal_self :
          (addAccountToDelete (devm4.setBal sevm.currentTarget 0) sevm.currentTarget).getBal
            sevm.currentTarget = 0 := by
        show ((devm4.state.setBal sevm.currentTarget 0).get sevm.currentTarget).bal = 0
        rw [State.setBal_get_self]; rfl
      have h_bal_ne : ∀ a, sevm.currentTarget ≠ a →
          (addAccountToDelete (devm4.setBal sevm.currentTarget 0) sevm.currentTarget).getBal a =
            devm4.getBal a := by
        intro a ha
        show ((devm4.state.setBal sevm.currentTarget 0).get a).bal = (devm4.state.get a).bal
        rw [State.setBal_get_ne ha]
      have h_dec :
          Decrease sevm.currentTarget (devm4.getBal sevm.currentTarget) devm4.getBal
            (addAccountToDelete (devm4.setBal sevm.currentTarget 0) sevm.currentTarget).getBal := by
        intro a
        constructor
        · intro h_eq; subst h_eq
          rw [h_bal_self, B256.sub_self]
        · intro ha; exact (h_bal_ne a ha).symm
      have h_sum' :
          sum devm4.getBal - (devm4.getBal sevm.currentTarget).toNat =
            sum (addAccountToDelete (devm4.setBal sevm.currentTarget 0) sevm.currentTarget).getBal :=
        sum_sub_assoc h_dec (B256.le_of_toNat_le_toNat (Nat.le_refl _))
      omega
    · rw [← Except.ok.inj h_run4]
      exact h_nof4

lemma Jinst.inv_state
    {pc sevm devm j pc' devm'}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j (.ok ⟨pc', devm'⟩)) :
    devm'.state = devm.state := by
  cases h1 : devm.stack
  · cases j
    · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, safeSub, bind, Except.bind] at run
      rw [h1] at run
      dsimp at run
      contradiction
    · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, Except.assert, safeSub, bind, Except.bind] at run
      rw [h1] at run
      dsimp at run
      contradiction
    · by_cases h_gas : gJumpdest ≤ devm.gasLeft
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, bind, Except.bind, safeSub] at run
        rw [h1] at run
        simp only [h_gas, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
        cases run
        subst_vars
        rfl
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, bind, Except.bind, safeSub] at run
        rw [h1] at run
        have h_gas_not : ¬(gJumpdest ≤ devm.gasLeft) := by omega
        simp only [h_gas_not] at run
        try contradiction
  · rename_i x xs
    cases h2 : xs
    · cases j
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, bind, Except.bind, safeSub] at run
        rw [h1] at run
        dsimp at run
        by_cases h_gas : gMid ≤ devm.gasLeft
        · simp only [h_gas, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
          by_cases h_jump : jumpable sevm.code x.toNat = true
          · simp only [h_jump, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
            cases run
            subst_vars
            rfl
          · simp only [h_jump, if_neg, Except.ok.injEq, Prod.mk.injEq] at run
            contradiction
        · have h_gas_not : ¬(gMid ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg, Except.ok.injEq, Prod.mk.injEq] at run
          contradiction
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, bind, Except.bind, safeSub] at run
        rw [h1] at run
        rw [h2] at run
        dsimp at run
        contradiction
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, bind, Except.bind, safeSub] at run
        rw [h1] at run
        by_cases h_gas : gJumpdest ≤ devm.gasLeft
        · simp only [h_gas, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
          cases run
          subst_vars
          rfl
        · have h_gas_not : ¬(gJumpdest ≤ devm.gasLeft) := by omega
          simp only [h_gas_not] at run
          contradiction
    · rename_i x2 xs2
      cases j
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, bind, Except.bind, safeSub] at run
        rw [h1] at run
        dsimp at run
        by_cases h_gas : gMid ≤ devm.gasLeft
        · simp only [h_gas, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
          by_cases h_jump : jumpable sevm.code x.toNat = true
          · simp only [h_jump, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
            cases run
            subst_vars
            rfl
          · simp only [h_jump, if_neg, Except.ok.injEq, Prod.mk.injEq] at run
            contradiction
        · have h_gas_not : ¬(gMid ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg, Except.ok.injEq, Prod.mk.injEq] at run
          contradiction
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, Devm.pop, bind, Except.bind, safeSub] at run
        rw [h1] at run
        rw [h2] at run
        dsimp at run
        by_cases h_gas : gHigh ≤ devm.gasLeft
        · simp only [h_gas, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
          by_cases h_cond : x2 = 0
          · simp only [h_cond, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
            cases run
            subst_vars
            rfl
          · simp only [h_cond, if_neg, Except.ok.injEq, Prod.mk.injEq] at run
            by_cases h_jump : jumpable sevm.code x.toNat = true
            · simp only [h_jump, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
              cases run
              subst_vars
              rfl
            · simp only [h_jump, if_neg, Except.ok.injEq, Prod.mk.injEq] at run
              contradiction
        · have h_gas_not : ¬(gHigh ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg, Except.ok.injEq, Prod.mk.injEq] at run
          contradiction
      · simp only [Jinst.Run, Jinst.run, runCore, chargeGas, bind, Except.bind, safeSub] at run
        rw [h1] at run
        by_cases h_gas : gJumpdest ≤ devm.gasLeft
        · simp only [h_gas, if_pos, Except.ok.injEq, Prod.mk.injEq] at run
          cases run
          subst_vars
          rfl
        · have h_gas_not : ¬(gJumpdest ≤ devm.gasLeft) := by omega
          simp only [h_gas_not, if_neg, Except.ok.injEq, Prod.mk.injEq] at run
          contradiction

-- nof-invariance of the sub-execution recorded in an Xlot oracle
def Xlot.InvNof : Xlot → Prop
  | .none => True
  | .some ⟨_, devm_, exn_⟩ =>
    ∀ devm' : Devm, exn_ = .ok devm' →
      sum devm_.getBal < 2 ^ 256 → sum devm'.getBal < 2 ^ 256

lemma sum_getBal_state {d : Devm} : sum d.getBal = sum d.state.bal := by
  have h : d.getBal = d.state.bal := funext (fun _ => rfl)
  rw [h]

lemma nof_of_state_eq {d d' : Devm} (h : d'.state = d.state)
    (h_nof : sum d.getBal < 2 ^ 256) : sum d'.getBal < 2 ^ 256 := by
  have h' : d'.getBal = d.getBal := funext (getBal_eq_of_state_eq h)
  rw [h']; exact h_nof

-- the value transfer preceding a sub-message run preserves the balance sum
lemma sum_bal_of_benvAfterTransfer {msg : Msg} {benv' : Benv}
    (h : msg.benvAfterTransfer = .ok benv')
    (h_nof : sum msg.benv.state.bal < 2 ^ 256) :
    sum benv'.state.bal = sum msg.benv.state.bal := by
  by_cases h_stv : msg.shouldTransferValue = true
  · rcases of_benvAfterTransfer h_stv h with ⟨st_mid, h_sub, hB⟩
    have hBs : benv'.state = st_mid.addBal msg.currentTarget msg.value := by
      rw [hB]; rfl
    rw [hBs]
    exact (of_state_transfer h_sub h_nof).2.2.1
  · unfold Msg.benvAfterTransfer at h
    rw [if_neg h_stv] at h
    rw [← Except.ok.inj h]

lemma of_executeCode_cases {msg : Msg} {xl : Xlot}
    {ex : Except (String × _root_.State × AdrSet × Tra) Devm}
    (h : ExecuteCode msg xl ex) :
    (∃ adr, executeCode.handleError (executePrecomp (initEvm msg) adr) = ex) ∨
    (∃ ex', xl = .some ⟨initSevm msg, initDevm msg, ex'⟩ ∧
      executeCode.handleError ex' = ex) := by
  rcases h_ca : msg.codeAddress with _ | adr
  · unfold ExecuteCode at h
    rw [h_ca] at h
    dsimp only [initEvm] at h
    exact Or.inr h
  · rcases of_executeCode_someCode h_ca h with ⟨_, _, h'⟩ | ⟨_, ex', h1, h2⟩
    · exact Or.inl ⟨adr, h'⟩
    · exact Or.inr ⟨ex', h1, h2⟩

lemma chargeCodeGas_state {d d' : Devm}
    (h : processCreateMessage.chargeCodeGas d = .ok d') : d'.state = d.state := by
  unfold processCreateMessage.chargeCodeGas at h
  dsimp only at h
  split at h
  · cases h
  · rcases of_bind_eq_ok h with ⟨d1, h_charge, h_rest⟩
    split_ifs at h_rest
    cases h_rest
    exact (Devm.burn_of_chargeGas h_charge).state.symm

lemma ProcessMessage.inv_nof {msg : Msg} {xl : Xlot}
    {ex : Except (String × _root_.State × AdrSet × Tra) Devm} {child : Devm}
    (inv : Xlot.InvNof xl)
    (run : ProcessMessage msg xl ex)
    (h_ex : ex = .ok child)
    (h_nof : sum msg.benv.state.bal < 2 ^ 256) :
    sum child.state.bal < 2 ^ 256 := by
  subst h_ex
  dsimp only [ProcessMessage] at run
  rcases run with ⟨_, _, h_contra, _⟩ | ⟨benv', eq_bt, run⟩
  · cases h_contra
  rcases run with ⟨ex'', run_ec, h_split⟩
  have h_nof' : sum benv'.state.bal < 2 ^ 256 := by
    rw [sum_bal_of_benvAfterTransfer eq_bt h_nof]; exact h_nof
  rcases h_split with ⟨_, _, h_contra⟩ | ⟨evm2, h_ex'', h_if⟩
  · cases h_contra
  by_cases h_err : evm2.error.isSome = true
  · -- sub-message failed : state rolled back to the pre-transfer state
    rw [if_pos h_err] at h_if
    rw [← Except.ok.inj h_if]
    exact h_nof
  · rw [if_neg h_err] at h_if
    rw [← Except.ok.inj h_if]
    rcases of_executeCode_cases run_ec with ⟨adr, h_he⟩ | ⟨ex₀, h_xl, h_he⟩
    · -- precompile : state unchanged from the post-transfer state
      rw [h_ex''] at h_he
      have h_state : evm2.state = benv'.state :=
        state_of_executePrecomp_ok h_he h_err
      rw [h_state]; exact h_nof'
    · -- proper sub-execution recorded in the oracle
      rw [h_xl] at inv
      dsimp only [Xlot.InvNof] at inv
      rw [h_ex''] at h_he
      rcases ex₀ with e | dc
      · rcases of_handleError_err h_he with ⟨evm4, h_ok4, h_some4, _⟩ | ⟨_, h_err4⟩
        · rw [← Except.ok.inj h_ok4] at h_some4
          exact absurd h_some4 h_err
        · cases h_err4
      · simp only [executeCode.handleError] at h_he
        rw [← Except.ok.inj h_he]
        have h_nof_in : sum (initDevm (msg.withBenv benv')).getBal < 2 ^ 256 := by
          rw [sum_getBal_state]
          exact h_nof'
        have h_out := inv dc rfl h_nof_in
        rw [sum_getBal_state] at h_out
        exact h_out

lemma GenericCall.inv_nof {sevm : Sevm} {devm : Devm}
    {gas : Nat} {value : B256} {caller target codeAddress : Adr}
    {stv istat : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    {xl : Xlot} {r : Devm}
    (inv : Xlot.InvNof xl)
    (h : GenericCall sevm devm gas value caller target codeAddress
      stv istat ii is oi os code dp xl (.ok r))
    (h_nof : sum devm.getBal < 2 ^ 256) :
    sum r.getBal < 2 ^ 256 := by
  dsimp only [GenericCall] at h
  rcases h with ⟨evm1, h_evm1, h⟩
  split_ifs at h with h_depth
  · -- depth limit reached : call fails, state unchanged
    rcases h with ⟨_, h_push⟩
    apply nof_of_state_eq _ h_nof
    rw [← (Devm.push_of_push h_push).state, h_evm1]
    rfl
  · rcases h with ⟨calldata, _, h⟩
    rcases h with ⟨childMsg, h_cm, h⟩
    rcases h with ⟨ex', run_pm, h_split⟩
    have h_nof_cm : sum childMsg.benv.state.bal < 2 ^ 256 := by
      have h_st : childMsg.benv.state = devm.state := by rw [h_cm, h_evm1]; rfl
      rw [h_st, ← sum_getBal_state]
      exact h_nof
    rcases ex' with e | child
    · rcases e with ⟨e1, e2, e3, e4⟩
      dsimp only [liftToExecution] at h_split
      rcases h_split with ⟨_, _, h_contra⟩ | ⟨_, h_contra, _⟩ <;> cases h_contra
    · dsimp only [liftToExecution] at h_split
      rcases h_split with ⟨_, h_contra, _⟩ | ⟨c, h_c, h_body⟩
      · cases h_contra
      cases h_c
      have h_child : sum child.state.bal < 2 ^ 256 :=
        ProcessMessage.inv_nof inv run_pm rfl h_nof_cm
      by_cases h_err : child.error.isSome = true
      · rw [if_pos h_err] at h_body
        rw [sum_getBal_state, state_of_push_split h_body]
        exact h_child
      · rw [if_neg h_err] at h_body
        rw [sum_getBal_state, state_of_push_split h_body]
        exact h_child

lemma ProcessCreateMessage.inv_nof {msg : Msg} {xl : Xlot}
    {ex : Except (String × _root_.State × AdrSet × Tra) Devm} {child : Devm}
    (inv : Xlot.InvNof xl)
    (run : ProcessCreateMessage msg xl ex)
    (h_ex : ex = .ok child)
    (h_nof : sum msg.benv.state.bal < 2 ^ 256) :
    sum child.state.bal < 2 ^ 256 := by
  subst h_ex
  dsimp only [ProcessCreateMessage] at run
  rcases run with ⟨ex', run_pm, h_split⟩
  have h_nof' : sum (processCreateMessage.msg msg).benv.state.bal < 2 ^ 256 := by
    have h_st : (processCreateMessage.msg msg).benv.state
        = (msg.benv.state.setStor msg.currentTarget .empty).incrNonce
            msg.currentTarget := rfl
    rw [h_st, State.incrNonce_bal, State.setStor_bal]
    exact h_nof
  rcases h_split with ⟨_, _, h_contra⟩ | ⟨evm, h_ex', h_if⟩
  · cases h_contra
  have h_evm : sum evm.state.bal < 2 ^ 256 :=
    ProcessMessage.inv_nof inv run_pm h_ex' h_nof'
  by_cases h_err : evm.error.isNone = true
  · rw [if_pos h_err] at h_if
    rcases h_cg : processCreateMessage.chargeCodeGas evm with ⟨err, evm'⟩ | evm' <;>
      rw [h_cg] at h_if <;> dsimp only at h_if
    · split_ifs at h_if with h_halt
      rw [← Except.ok.inj h_if]
      exact h_nof
    · rw [← Except.ok.inj h_if]
      have h_st : (evm'.setCode msg.currentTarget ⟨⟨evm'.output⟩⟩).state
          = evm'.state.setCode msg.currentTarget ⟨⟨evm'.output⟩⟩ := rfl
      rw [h_st, State.setCode_bal, chargeCodeGas_state h_cg]
      exact h_evm
  · rw [if_neg h_err] at h_if
    rw [← Except.ok.inj h_if]
    exact h_nof

lemma GenericCreate.inv_nof {sevm : Sevm} {devm : Devm} {endowment : B256}
    {newAddress : Adr} {mi ms : Nat} {xl : Xlot} {r : Devm}
    (inv : Xlot.InvNof xl)
    (h : GenericCreate sevm devm endowment newAddress mi ms xl (.ok r))
    (h_nof : sum devm.getBal < 2 ^ 256) :
    sum r.getBal < 2 ^ 256 := by
  dsimp only [GenericCreate] at h
  rcases h with ⟨calldata, _, h⟩
  rcases h with ⟨_, _, h_contra, _⟩ | ⟨_, _, h⟩
  · cases h_contra
  rcases h with ⟨devm1, h_d1, h⟩
  rcases h with ⟨createMsgGas, _, h⟩
  rcases h with ⟨devm2, h_d2, h⟩
  rcases h with ⟨_, _, h_contra, _⟩ | ⟨_, _, h⟩
  · cases h_contra
  rcases h with ⟨devm3, h_d3, h⟩
  rcases h with ⟨sender, _, h⟩
  have h_st1 : devm1.state = devm.state := by rw [h_d1]; rfl
  have h_st2 : devm2.state = devm1.state := by rw [h_d2]
  have h_st3 : devm3.state = devm2.state := by rw [h_d3]
  have h_nof3 : sum devm3.state.bal < 2 ^ 256 := by
    rw [h_st3, h_st2, h_st1, ← sum_getBal_state]
    exact h_nof
  split_ifs at h with h_c1
  · -- create fails : state unchanged
    rcases h with ⟨_, h_push⟩
    rw [sum_getBal_state, ← (Devm.push_of_push h_push).state]
    exact h_nof3
  · rcases h with ⟨devm4, h_d4, h⟩
    have h_bal4 : devm4.state.bal = devm3.state.bal := by
      rw [h_d4, Devm.incrNonce_state, State.incrNonce_bal]
    have h_nof4 : sum devm4.state.bal < 2 ^ 256 := by
      rw [h_bal4]; exact h_nof3
    split_ifs at h with h_c2
    · -- target account exists : create fails, state unchanged
      rcases h with ⟨_, h_push⟩
      rw [sum_getBal_state, ← (Devm.push_of_push h_push).state]
      exact h_nof4
    · rcases h with ⟨childMsg, h_cm, h⟩
      rcases h with ⟨ex', run_pcm, h_split⟩
      have h_nof_cm : sum childMsg.benv.state.bal < 2 ^ 256 := by
        have h_st : childMsg.benv.state = devm4.state := by rw [h_cm]
        rw [h_st]; exact h_nof4
      rcases ex' with e | child
      · rcases e with ⟨e1, e2, e3, e4⟩
        dsimp only [liftToExecution] at h_split
        rcases h_split with ⟨_, _, h_contra⟩ | ⟨_, h_contra, _⟩ <;> cases h_contra
      · dsimp only [liftToExecution] at h_split
        rcases h_split with ⟨_, h_contra, _⟩ | ⟨c, h_c, h_body⟩
        · cases h_contra
        cases h_c
        have h_child : sum child.state.bal < 2 ^ 256 :=
          ProcessCreateMessage.inv_nof inv run_pcm rfl h_nof_cm
        by_cases h_err : child.error.isSome = true
        · rw [if_pos h_err] at h_body
          rw [sum_getBal_state, ← (Devm.push_of_push h_body).state]
          exact h_child
        · rw [if_neg h_err] at h_body
          rw [sum_getBal_state, ← (Devm.push_of_push h_body).state]
          exact h_child

lemma Xinst.inv_nof_gen {sevm : Sevm} {s r : Devm} {x : Xinst} {xl : Xlot}
    (inv : Xlot.InvNof xl)
    (h : Xinst.Run sevm s x xl (.ok r))
    (h_nof : sum s.getBal < 2 ^ 256) :
    sum r.getBal < 2 ^ 256 := by
  cases x
  case create =>
    dsimp only [Xinst.Run] at h
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨endowment, d1⟩, e1, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨mi, d2⟩, e2, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨ms, d3⟩, e3, h⟩; · cases h_contra
    rcases h with ⟨extendCost, _, h⟩
    rcases h with ⟨initCodeCost, _, h⟩
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨d4, e4, h⟩; · cases h_contra
    rcases h with ⟨d5, h_d5, h⟩
    rcases h with ⟨newAddress, _, h⟩
    rcases Devm.pop_of_popToNat e2 with ⟨_, hp2⟩
    rcases Devm.pop_of_popToNat e3 with ⟨_, hp3⟩
    have h_st3 : s.state = d3.state :=
      ((Devm.pop_of_pop e1).state).trans (hp2.state.trans hp3.state)
    have h_st4 : d3.state = d4.state := (Devm.burn_of_chargeGas e4).state
    have h_st5 : d5.state = d4.state := by rw [h_d5]; rfl
    apply GenericCreate.inv_nof inv h
    apply nof_of_state_eq _ h_nof
    rw [h_st5, ← h_st4, ← h_st3]
  case create2 =>
    dsimp only [Xinst.Run] at h
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨endowment, d1⟩, e1, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨mi, d2⟩, e2, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨ms, d3⟩, e3, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨salt, d4⟩, e4, h⟩; · cases h_contra
    rcases h with ⟨extendCost, _, h⟩
    rcases h with ⟨initCodeHashCost, _, h⟩
    rcases h with ⟨initCodeCost, _, h⟩
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨d5, e5, h⟩; · cases h_contra
    rcases h with ⟨d6, h_d6, h⟩
    rcases h with ⟨newAddress, _, h⟩
    rcases Devm.pop_of_popToNat e2 with ⟨_, hp2⟩
    rcases Devm.pop_of_popToNat e3 with ⟨_, hp3⟩
    have h_st4 : s.state = d4.state :=
      ((Devm.pop_of_pop e1).state).trans
        (hp2.state.trans (hp3.state.trans (Devm.pop_of_pop e4).state))
    have h_st5 : d4.state = d5.state := (Devm.burn_of_chargeGas e5).state
    have h_st6 : d6.state = d5.state := by rw [h_d6]; rfl
    apply GenericCreate.inv_nof inv h
    apply nof_of_state_eq _ h_nof
    rw [h_st6, ← h_st5, ← h_st4]
  case call =>
    dsimp only [Xinst.Run] at h
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨gas, d1⟩, e1, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨callee, d2⟩, e2, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨value, d3⟩, e3, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨ii, d4⟩, e4, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨is, d5⟩, e5, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨oi, d6⟩, e6, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨os, d7⟩, e7, h⟩; · cases h_contra
    rcases h with ⟨extendCost, _, h⟩
    rcases h with ⟨preAccessCost, _, h⟩
    rcases h with ⟨d8, h_d8, h⟩
    rcases h with ⟨⟨dp, na, code0, dagc, d9⟩, h_d9, h⟩
    rcases h with ⟨accessCost, _, h⟩
    rcases h with ⟨createCost, _, h⟩
    rcases h with ⟨transferCost, _, h⟩
    rcases h with ⟨⟨mcc, mcs⟩, _, h⟩
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨d10, e10, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨_, _, h⟩; · cases h_contra
    rcases h with ⟨d11, h_d11, h⟩
    rcases h with ⟨senderBal, _, h⟩
    rcases Devm.pop_of_popToAdr e2 with ⟨_, _, hp2⟩
    rcases Devm.pop_of_popToNat e4 with ⟨_, hp4⟩
    rcases Devm.pop_of_popToNat e5 with ⟨_, hp5⟩
    rcases Devm.pop_of_popToNat e6 with ⟨_, hp6⟩
    rcases Devm.pop_of_popToNat e7 with ⟨_, hp7⟩
    have h_st7 : s.state = d7.state :=
      ((Devm.pop_of_pop e1).state).trans
        (((Devm.pop_of_pop hp2).state).trans
          (((Devm.pop_of_pop e3).state).trans
            (hp4.state.trans (hp5.state.trans (hp6.state.trans hp7.state)))))
    have h_st8 : d8.state = d7.state := by rw [h_d8]; rfl
    have h_st9 : d9.state = d8.state := by
      have hq := congrArg (fun q => (q.2.2.2.2 : Devm).state) h_d9
      dsimp at hq
      rw [hq, accessDelegation_state]
    have h_st10 : d9.state = d10.state := (Devm.burn_of_chargeGas e10).state
    have h_st11 : d11.state = d10.state := by rw [h_d11]; rfl
    have h_nof11 : sum d11.getBal < 2 ^ 256 := by
      apply nof_of_state_eq _ h_nof
      rw [h_st11, ← h_st10, h_st9, h_st8, ← h_st7]
    split_ifs at h with h_lt
    · rcases h with ⟨_, _, h_contra, _⟩ | ⟨d12, e12, h⟩; · cases h_contra
      rcases h with ⟨_, h_ex⟩
      rw [← Except.ok.inj h_ex]
      apply nof_of_state_eq _ h_nof11
      exact ((Devm.push_of_push e12).state).symm
    · exact GenericCall.inv_nof inv h h_nof11
  case callcode =>
    dsimp only [Xinst.Run] at h
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨gas, d1⟩, e1, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨codeAddress, d2⟩, e2, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨value, d3⟩, e3, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨ii, d4⟩, e4, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨is, d5⟩, e5, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨oi, d6⟩, e6, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨os, d7⟩, e7, h⟩; · cases h_contra
    rcases h with ⟨extendCost, _, h⟩
    rcases h with ⟨preAccessCost, _, h⟩
    rcases h with ⟨d8, h_d8, h⟩
    rcases h with ⟨⟨dp, na, code0, dagc, d9⟩, h_d9, h⟩
    rcases h with ⟨accessCost, _, h⟩
    rcases h with ⟨transferCost, _, h⟩
    rcases h with ⟨⟨mcc, mcs⟩, _, h⟩
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨d10, e10, h⟩; · cases h_contra
    rcases h with ⟨d11, h_d11, h⟩
    rcases h with ⟨senderBal, _, h⟩
    rcases Devm.pop_of_popToAdr e2 with ⟨_, _, hp2⟩
    rcases Devm.pop_of_popToNat e4 with ⟨_, hp4⟩
    rcases Devm.pop_of_popToNat e5 with ⟨_, hp5⟩
    rcases Devm.pop_of_popToNat e6 with ⟨_, hp6⟩
    rcases Devm.pop_of_popToNat e7 with ⟨_, hp7⟩
    have h_st7 : s.state = d7.state :=
      ((Devm.pop_of_pop e1).state).trans
        (((Devm.pop_of_pop hp2).state).trans
          (((Devm.pop_of_pop e3).state).trans
            (hp4.state.trans (hp5.state.trans (hp6.state.trans hp7.state)))))
    have h_st8 : d8.state = d7.state := by rw [h_d8]; rfl
    have h_st9 : d9.state = d8.state := by
      have hq := congrArg (fun q => (q.2.2.2.2 : Devm).state) h_d9
      dsimp at hq
      rw [hq, accessDelegation_state]
    have h_st10 : d9.state = d10.state := (Devm.burn_of_chargeGas e10).state
    have h_st11 : d11.state = d10.state := by rw [h_d11]; rfl
    have h_nof11 : sum d11.getBal < 2 ^ 256 := by
      apply nof_of_state_eq _ h_nof
      rw [h_st11, ← h_st10, h_st9, h_st8, ← h_st7]
    split_ifs at h with h_lt
    · rcases h with ⟨_, _, h_contra, _⟩ | ⟨d12, e12, h⟩; · cases h_contra
      rcases h with ⟨_, h_ex⟩
      rw [← Except.ok.inj h_ex]
      apply nof_of_state_eq _ h_nof11
      exact ((Devm.push_of_push e12).state).symm
    · exact GenericCall.inv_nof inv h h_nof11
  case delcall =>
    dsimp only [Xinst.Run] at h
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨gas, d1⟩, e1, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨codeAddress, d2⟩, e2, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨ii, d3⟩, e3, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨is, d4⟩, e4, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨oi, d5⟩, e5, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨os, d6⟩, e6, h⟩; · cases h_contra
    rcases h with ⟨extendCost, _, h⟩
    rcases h with ⟨preAccessCost, _, h⟩
    rcases h with ⟨d7, h_d7, h⟩
    rcases h with ⟨⟨dp, na, code0, dagc, d8⟩, h_d8, h⟩
    rcases h with ⟨accessCost, _, h⟩
    rcases h with ⟨⟨mcc, mcs⟩, _, h⟩
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨d9, e9, h⟩; · cases h_contra
    rcases h with ⟨d10, h_d10, h⟩
    rcases Devm.pop_of_popToAdr e2 with ⟨_, _, hp2⟩
    rcases Devm.pop_of_popToNat e3 with ⟨_, hp3⟩
    rcases Devm.pop_of_popToNat e4 with ⟨_, hp4⟩
    rcases Devm.pop_of_popToNat e5 with ⟨_, hp5⟩
    rcases Devm.pop_of_popToNat e6 with ⟨_, hp6⟩
    have h_st6 : s.state = d6.state :=
      ((Devm.pop_of_pop e1).state).trans
        (((Devm.pop_of_pop hp2).state).trans
          (hp3.state.trans (hp4.state.trans (hp5.state.trans hp6.state))))
    have h_st7 : d7.state = d6.state := by rw [h_d7]; rfl
    have h_st8 : d8.state = d7.state := by
      have hq := congrArg (fun q => (q.2.2.2.2 : Devm).state) h_d8
      dsimp at hq
      rw [hq, accessDelegation_state]
    have h_st9 : d8.state = d9.state := (Devm.burn_of_chargeGas e9).state
    have h_st10 : d10.state = d9.state := by rw [h_d10]; rfl
    apply GenericCall.inv_nof inv h
    apply nof_of_state_eq _ h_nof
    rw [h_st10, ← h_st9, h_st8, h_st7, ← h_st6]
  case statcall =>
    dsimp only [Xinst.Run] at h
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨gas, d1⟩, e1, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨target, d2⟩, e2, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨ii, d3⟩, e3, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨is, d4⟩, e4, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨oi, d5⟩, e5, h⟩; · cases h_contra
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨⟨os, d6⟩, e6, h⟩; · cases h_contra
    rcases h with ⟨extendCost, _, h⟩
    rcases h with ⟨preAccessCost, _, h⟩
    rcases h with ⟨d7, h_d7, h⟩
    rcases h with ⟨⟨dp, na, code0, dagc, d8⟩, h_d8, h⟩
    rcases h with ⟨accessCost, _, h⟩
    rcases h with ⟨⟨mcc, mcs⟩, _, h⟩
    rcases h with ⟨_, _, h_contra, _⟩ | ⟨d9, e9, h⟩; · cases h_contra
    rcases h with ⟨d10, h_d10, h⟩
    rcases Devm.pop_of_popToAdr e2 with ⟨_, _, hp2⟩
    rcases Devm.pop_of_popToNat e3 with ⟨_, hp3⟩
    rcases Devm.pop_of_popToNat e4 with ⟨_, hp4⟩
    rcases Devm.pop_of_popToNat e5 with ⟨_, hp5⟩
    rcases Devm.pop_of_popToNat e6 with ⟨_, hp6⟩
    have h_st6 : s.state = d6.state :=
      ((Devm.pop_of_pop e1).state).trans
        (((Devm.pop_of_pop hp2).state).trans
          (hp3.state.trans (hp4.state.trans (hp5.state.trans hp6.state))))
    have h_st7 : d7.state = d6.state := by rw [h_d7]; rfl
    have h_st8 : d8.state = d7.state := by
      have hq := congrArg (fun q => (q.2.2.2.2 : Devm).state) h_d8
      dsimp at hq
      rw [hq, accessDelegation_state]
    have h_st9 : d8.state = d9.state := (Devm.burn_of_chargeGas e9).state
    have h_st10 : d10.state = d9.state := by rw [h_d10]; rfl
    apply GenericCall.inv_nof inv h
    apply nof_of_state_eq _ h_nof
    rw [h_st10, ← h_st9, h_st8, h_st7, ← h_st6]

lemma Ninst.inv_nof_gen {pc : Nat} {sevm : Sevm} {devm devm' : Devm}
    {n : Ninst} {xl : Xlot}
    (inv : Xlot.InvNof xl)
    (run : Ninst.Run' pc sevm devm n xl (.ok devm'))
    (h_nof : sum devm.getBal < 2 ^ 256) :
    sum devm'.getBal < 2 ^ 256 := by
  cases n with
  | push xs le =>
    cases xl with
    | none =>
      dsimp only [Ninst.Run'] at run
      rcases of_bind_eq_ok run with ⟨d1, h_charge, h_push⟩
      apply nof_of_state_eq _ h_nof
      exact ((Devm.burn_of_chargeGas h_charge).state.trans
        (Devm.push_of_push h_push).state).symm
    | some y => dsimp only [Ninst.Run'] at run
  | reg rg =>
    cases xl with
    | none =>
      dsimp only [Ninst.Run'] at run
      have h_bal := (inferInstanceAs (Rinst.Hinv Devm.getBal rg)).inv run
      rw [← h_bal]; exact h_nof
    | some y => dsimp only [Ninst.Run'] at run
  | exec xinst =>
    dsimp only [Ninst.Run'] at run
    exact Xinst.inv_nof_gen inv run h_nof

lemma Exec.inv_nof {pc : Nat} {sevm : Sevm} {devm : Devm} {exn : Execution}
    (run : Exec pc sevm devm exn) :
    ∀ r : Devm, exn = .ok r →
      sum devm.getBal < 2 ^ 256 → sum r.getBal < 2 ^ 256 := by
  revert exn devm sevm pc
  apply Exec.rec
  · intro _ _ _ _ r h_eq; cases h_eq
  · intro _ _ _ _ _ _ _ _ r h_eq; cases h_eq
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ r h_eq; cases h_eq
  · intro pc sevm devm n devm' exn h_at h_run ex ih r h_eq h_nof
    exact ih r h_eq (Ninst.inv_nof_gen (xl := .none) trivial h_run h_nof)
  · intro pc sevm devm n sevm_ devm_ exn_ devm' exn h_at h_run ex_sub ex ih_sub ih
      r h_eq h_nof
    refine ih r h_eq
      (Ninst.inv_nof_gen (xl := some ⟨sevm_, devm_, exn_⟩) ?_ h_run h_nof)
    exact fun d' hd' h' => ih_sub d' hd' h'
  · intro _ _ _ _ _ _ _ _ r h_eq; cases h_eq
  · intro pc sevm devm j pc' devm' exn h_at h_run ex ih r h_eq h_nof
    exact ih r h_eq (nof_of_state_eq (Jinst.inv_state h_run) h_nof)
  · intro pc sevm devm l exn h_at h_run r h_eq h_nof
    subst h_eq
    exact Linst.inv_nof h_run h_nof

lemma Xinst.inv_nof {sevm : Sevm} {s r : Devm} {x : Xinst} {xl : Xlot}
    (h : Xinst.Run sevm s x xl (.ok r)) (h_nof : sum s.getBal < 2 ^ 256)
    (h_fill : xl.Filled) :
    sum r.getBal < 2 ^ 256 := by
  apply Xinst.inv_nof_gen _ h h_nof
  cases xl with
  | none => trivial
  | some y =>
    rcases y with ⟨sevm_, devm_, exn_⟩
    obtain ⟨ex_sub⟩ := h_fill
    exact fun d' hd' h' => Exec.inv_nof ex_sub d' hd' h'

lemma Ninst.inv_nof {sevm : Sevm} {s r : Devm} {i : Ninst}
    (h : Ninst.Run sevm s i r) (h_nof : sum s.getBal < 2 ^ 256) :
    sum r.getBal < 2 ^ 256 := by
  rcases h with ⟨xl, h_filled, pc, h_run'⟩
  cases xl with
  | none =>
    cases i with
    | push xs n =>
      dsimp [Ninst.Run'] at h_run'
      rcases of_bind_eq_ok h_run' with ⟨s', h_charge, h_push⟩
      have h_eq1 : s.getBal = s'.getBal := by
        funext a
        exact (chargeGas_getBal_eq h_charge a).symm
      have h_eq2 : s'.getBal = r.getBal := by
        funext a
        exact (Devm.push_getBal_eq h_push a).symm
      have h_eq : s.getBal = r.getBal := h_eq1.trans h_eq2
      rw [← h_eq]
      exact h_nof
    | reg reg_inst =>
      dsimp [Ninst.Run'] at h_run'
      have h_bal := (inferInstanceAs (Rinst.Hinv Devm.getBal reg_inst)).inv h_run'
      rw [← h_bal]
      exact h_nof
    | exec xinst =>
      dsimp [Ninst.Run'] at h_run'
      exact Xinst.inv_nof h_run' h_nof h_filled
  | some y =>
    cases i with
    | push xs n =>
      dsimp [Ninst.Run'] at h_run'
    | reg reg_inst =>
      dsimp [Ninst.Run'] at h_run'
    | exec xinst =>
      dsimp [Ninst.Run'] at h_run'
      exact Xinst.inv_nof h_run' h_nof h_filled

lemma Func.inv_nof {c : List Func} {sevm : Sevm} {s r : Devm} {f : Func}
    (run : Func.Run c sevm s f r) (h_nof : sum s.getBal < 2 ^ 256) :
    sum r.getBal < 2 ^ 256 := by
  induction run with
  | zero h_pop _ ih =>
    have h_bal : _ = _ := (inferInstanceAs (PopBurn.Inv Devm.getBal)).inv h_pop
    rw [h_bal] at h_nof
    exact ih h_nof
  | succ _ h_pop h_burn _ ih =>
    have h_bal1 : _ = _ := (inferInstanceAs (PopBurn.Inv Devm.getBal)).inv h_pop
    have h_bal2 : _ = _ := (inferInstanceAs (Burn.Inv Devm.getBal)).inv h_burn
    rw [h_bal1, h_bal2] at h_nof
    exact ih h_nof
  | last h_run =>
    exact Linst.inv_nof h_run h_nof
  | next h_run _ ih =>
    exact ih (Ninst.inv_nof h_run h_nof)
  | call _ h_burn _ ih =>
    have h_bal : _ = _ := (inferInstanceAs (Burn.Inv Devm.getBal)).inv h_burn
    rw [h_bal] at h_nof
    exact ih h_nof

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
    refine' ⟨_, _, _⟩
    · rw [← Line.of_inv Devm.getCode (by line_inv) h₁]; exact cond₀.code
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

lemma Precond.of_eqs {wa : Adr} {sevm : Sevm} {pre inter : Devm}
    (h_pc : Precond wa sevm pre)
    (h_code : inter.getCode wa = pre.getCode wa)
    (h_bal : inter.getBal = pre.getBal)
    (h_stor : inter.getStor wa = pre.getStor wa) :
    Precond wa sevm inter := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_code]; exact h_pc.code
  · rw [h_bal]; exact h_pc.nof
  · intro h; rw [h_bal, h_stor]; exact h_pc.solvent.left h
  · intro h; rw [h_bal, h_stor]; exact h_pc.solvent.right h

lemma setStorVal_getStor_ne {devm : Devm} {adr a : Adr} {key val : B256} (h : adr ≠ a) :
    (devm.setStorVal adr key val).getStor a = devm.getStor a := by
  simp only [Devm.getStor, Devm.getAcct, Devm.setStorVal, State.setStorVal]
  rw [State.get_set_ne h]

lemma sstore_inv_getStor_ne {pc : Nat} {sevm : Sevm} {s s' : Devm} {a : Adr}
    (run : Rinst.run ⟨pc, sevm, s⟩ .sstore = .ok s')
    (h_ne : sevm.currentTarget ≠ a) :
    s'.getStor a = s.getStor a := by
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨⟨key, s₁⟩, h1, run₁⟩
  rcases of_bind_eq_ok run₁ with ⟨⟨val, s₂⟩, h2, run₂⟩
  rcases of_bind_eq_ok run₂ with ⟨_, h3, run₃⟩
  rcases of_bind_eq_ok run₃ with ⟨⟨s₃, g₂⟩, h4, run₄⟩
  rcases of_bind_eq_ok run₄ with ⟨g₃, h5, run₅⟩
  rcases of_bind_eq_ok run₅ with ⟨s₄, h6, run₆⟩
  rcases of_bind_eq_ok run₆ with ⟨s₅, h7, run₇⟩
  rcases of_bind_eq_ok run₇ with ⟨_, h8, h9⟩
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
  rw [← eq, setStorVal_getStor_ne h_ne]
  exact (congr_fun E a).symm

lemma State.incrNonce_get_bal {st : _root_.State} {adr a : Adr} :
    ((st.incrNonce adr).get a).bal = (st.get a).bal := by
  simp only [State.incrNonce]
  by_cases h : adr = a
  · subst h; rw [State.get_set_self]
  · rw [State.get_set_ne h]

lemma State.incrNonce_get_stor {st : _root_.State} {adr a : Adr} :
    ((st.incrNonce adr).get a).stor = (st.get a).stor := by
  simp only [State.incrNonce]
  by_cases h : adr = a
  · subst h; rw [State.get_set_self]
  · rw [State.get_set_ne h]

lemma State.incrNonce_get_code {st : _root_.State} {adr a : Adr} :
    ((st.incrNonce adr).get a).code = (st.get a).code := by
  simp only [State.incrNonce]
  by_cases h : adr = a
  · subst h; rw [State.get_set_self]
  · rw [State.get_set_ne h]

lemma addAccessedAddress_state {devm : Devm} {a : Adr} :
    (addAccessedAddress devm a).state = devm.state := rfl

lemma of_benvAfterTransfer_no {msg : Msg} {benv' : Benv}
    (h_stv : ¬ msg.shouldTransferValue = true)
    (h : msg.benvAfterTransfer = .ok benv') : benv' = msg.benv := by
  unfold Msg.benvAfterTransfer at h
  rw [if_neg h_stv] at h
  exact (Except.ok.inj h).symm

lemma of_executeCode_noneCode {msg : Msg} {xl : Xlot}
    {ex : Except (String × _root_.State × AdrSet × Tra) Devm}
    (h_ca : msg.codeAddress = .none)
    (h : ExecuteCode msg xl ex) :
    ∃ ex', xl = .some ⟨initSevm msg, initDevm msg, ex'⟩ ∧
      executeCode.handleError ex' = ex := by
  unfold ExecuteCode at h
  rw [h_ca] at h
  exact h

lemma Precond.transfer_state {wa : Adr} {sevm : Sevm} {pre inter : Devm}
    {caller callee : Adr} {wad : B256} {st_mid : _root_.State}
    (h_pc : Precond wa sevm pre)
    (h_ne : caller ≠ wa)
    (h_sub : pre.state.subBal caller wad = some st_mid)
    (h_state : inter.state = st_mid.addBal callee wad) :
    Precond wa sevm inter := by
  have h_nof : sum pre.state.bal < 2 ^ 256 := h_pc.nof
  rcases of_state_transfer (callee := callee) h_sub h_nof with
    ⟨h_t_stor, h_t_code, h_t_sum, h_t_le, _, _⟩
  have h_stor_eq : inter.getStor wa = pre.getStor wa := by
    show (inter.state.get wa).stor = (pre.state.get wa).stor
    rw [h_state]; exact h_t_stor wa
  have h_code_eq : inter.getCode wa = pre.getCode wa := by
    show (inter.state.get wa).code = (pre.state.get wa).code
    rw [h_state]; exact h_t_code wa
  have h_bal_fun : inter.getBal = (st_mid.addBal callee wad).bal := by
    funext b
    show (inter.state.get b).bal = ((st_mid.addBal callee wad).get b).bal
    rw [h_state]
  have h_mid : st_mid.bal wa = pre.state.bal wa := by
    rcases State.of_subBal h_sub with ⟨_, h_st'⟩
    rw [h_st']
    show ((pre.state.setBal caller _).get wa).bal = (pre.state.get wa).bal
    rw [State.setBal_get_ne h_ne]
  have h_bal_ge : (pre.getBal wa).toNat ≤ ((st_mid.addBal callee wad).bal wa).toNat := by
    show (pre.state.bal wa).toNat ≤ _
    by_cases h_eq : callee = wa
    · have h_add : (st_mid.addBal callee wad).bal wa = pre.state.bal wa + wad := by
        rw [h_eq]
        show ((st_mid.setBal wa (st_mid.bal wa + wad)).get wa).bal = _
        rw [State.setBal_get_self]
        show st_mid.bal wa + wad = _
        rw [h_mid]
      rw [h_add]
      have h_le_wad : wad.toNat ≤ (pre.state.bal caller).toNat := B256.toNat_le_toNat h_t_le
      have h_two : (pre.state.bal wa).toNat + (pre.state.bal caller).toNat ≤ sum pre.state.bal :=
        add_le_sum_of_ne pre.state.bal (fun hc => h_ne hc.symm)
      have h_nof' : B256.Nof (pre.state.bal wa) wad := by
        unfold B256.Nof; omega
      rw [B256.toNat_add_eq_of_nof _ _ h_nof']
      omega
    · have h_other : (st_mid.addBal callee wad).bal wa = pre.state.bal wa := by
        show ((st_mid.setBal callee _).get wa).bal = _
        rw [State.setBal_get_ne h_eq]
        exact h_mid
      rw [h_other]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_code_eq]; exact h_pc.code
  · rw [h_bal_fun, h_t_sum]; exact h_nof
  · intro h
    have hs := h_pc.solvent.left h
    rw [h_stor_eq, h_bal_fun]
    unfold Stor.Solvent at hs ⊢
    omega
  · intro h
    have hs := h_pc.solvent.right h
    rw [h_stor_eq, h_bal_fun]
    unfold Stor.Solvent at hs ⊢
    omega

lemma GenericCall.none_inv_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm}
    {gas : Nat} {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    (h_run : GenericCall sevm devm gas value caller target codeAddress stv
      isStatic ii is oi os code dp .none (.ok inter))
    (h_ne : stv = true → caller ≠ wa)
    (h_pc : Precond wa sevm devm) :
    Precond wa sevm inter := by
  dsimp only [GenericCall] at h_run
  rcases h_run with ⟨evm1, hp_evm1, h_run⟩
  subst hp_evm1
  split_ifs at h_run with h_depth
  · rcases h_run with ⟨_, h_push⟩
    exact h_pc.state_eq ((Devm.push_of_push h_push).state).symm
  · rcases h_run with ⟨calldata, _, h_run⟩
    rcases h_run with ⟨childMsg, hp_cm, h_run⟩
    rcases h_run with ⟨ex', run_pm, h_split⟩
    have hc_state : childMsg.benv.state = devm.state := by rw [hp_cm]; rfl
    have hc_stv : childMsg.shouldTransferValue = stv := by rw [hp_cm]; rfl
    have hc_caller : childMsg.caller = caller := by rw [hp_cm]; rfl
    have hc_value : childMsg.value = value := by rw [hp_cm]; rfl
    have hc_ct : childMsg.currentTarget = target := by rw [hp_cm]; rfl
    have hc_ca : childMsg.codeAddress = some codeAddress := by rw [hp_cm]; rfl
    rcases ex' with err' | child
    · obtain ⟨e1, e2, e3, e4⟩ := err'
      dsimp only [liftToExecution] at h_split
      rcases h_split with ⟨x, _, h_contra⟩ | ⟨c, h_contra, _⟩ <;> cases h_contra
    · dsimp only [liftToExecution] at h_split
      rcases h_split with ⟨x, h_contra, _⟩ | ⟨c, h_c, h_body⟩
      · cases h_contra
      cases h_c
      have h_inter_state : inter.state = child.state := by
        by_cases h_err : child.error.isSome = true
        · rw [if_pos h_err] at h_body
          have h := state_of_push_split h_body
          exact h
        · rw [if_neg h_err] at h_body
          have h := state_of_push_split h_body
          exact h
      dsimp only [ProcessMessage] at run_pm
      rcases run_pm with ⟨errv, _, h_contra, _⟩ | ⟨benv', eq_bt, run_pm⟩
      · cases h_contra
      rcases run_pm with ⟨ex'', run_ec, h_split2⟩
      rcases h_split2 with ⟨x, _, h_contra⟩ | ⟨evm2, h_ex'', h_if⟩
      · cases h_contra
      by_cases h_err2 : evm2.error.isSome = true
      · rw [if_pos h_err2] at h_if
        apply h_pc.state_eq
        rw [h_inter_state, ← Except.ok.inj h_if]
        show childMsg.benv.state = devm.state
        exact hc_state
      · rw [if_neg h_err2] at h_if
        have h_eq_child := Except.ok.inj h_if
        subst h_eq_child
        subst h_ex''
        have hc_ca' : (childMsg.withBenv benv').codeAddress = some codeAddress := hc_ca
        rcases of_executeCode_someCode hc_ca' run_ec with
          ⟨_, _, h_he⟩ | ⟨_, ex''', h_xl_some, _⟩
        · have h_child_state : evm2.state = benv'.state := by
            have h := state_of_executePrecomp_ok h_he h_err2
            rw [h]; rfl
          by_cases h_stv : stv = true
          · rcases of_benvAfterTransfer (hc_stv.trans h_stv) eq_bt with ⟨st_mid, h_sub, hB⟩
            rw [hc_state, hc_caller, hc_value] at h_sub
            have hBs : benv'.state = st_mid.addBal target value := by
              rw [hB, hc_ct, hc_value]; rfl
            have h_state : inter.state = st_mid.addBal target value := by
              rw [h_inter_state, h_child_state, hBs]
            exact Precond.transfer_state h_pc (h_ne h_stv) h_sub h_state
          · have h_stv' : ¬ childMsg.shouldTransferValue = true := by
              rw [hc_stv]; exact h_stv
            have h_benv : benv' = childMsg.benv := of_benvAfterTransfer_no h_stv' eq_bt
            apply h_pc.state_eq
            rw [h_inter_state, h_child_state, h_benv]
            exact hc_state
        · cases h_xl_some

lemma GenericCreate.none_inv_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm}
    {endowment : B256} {newAddress : Adr} {memoryIndex memorySize : Nat}
    (h_run : GenericCreate sevm devm endowment newAddress memoryIndex memorySize
      .none (.ok inter))
    (h_pc : Precond wa sevm devm) :
    Precond wa sevm inter := by
  dsimp only [GenericCreate] at h_run
  rcases h_run with ⟨calldata, _, h_run⟩
  rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨_, _, h_run⟩; · cases h_contra
  rcases h_run with ⟨devm1, hp1, h_run⟩
  rcases h_run with ⟨createMsgGas, _, h_run⟩
  rcases h_run with ⟨devm2, hp2, h_run⟩
  rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨_, _, h_run⟩; · cases h_contra
  rcases h_run with ⟨devm3, hp3, h_run⟩
  rcases h_run with ⟨sender, _, h_run⟩
  have h_st3 : devm3.state = devm.state := by
    rw [hp3, hp2, hp1]; rfl
  split_ifs at h_run with h_chk
  · rcases h_run with ⟨_, h_push⟩
    apply h_pc.state_eq
    rw [← (Devm.push_of_push h_push).state]
    show devm3.state = devm.state
    exact h_st3
  · rcases h_run with ⟨devm4, hp4, h_run⟩
    split_ifs at h_run with h_coll
    · rcases h_run with ⟨_, h_push⟩
      have h_state : inter.state = devm.state.incrNonce sevm.currentTarget := by
        rw [← (Devm.push_of_push h_push).state, hp4]
        show devm3.state.incrNonce sevm.currentTarget = devm.state.incrNonce sevm.currentTarget
        rw [h_st3]
      refine Precond.of_eqs h_pc ?_ ?_ ?_
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
    · rcases h_run with ⟨childMsg, hp_cm, h_run⟩
      rcases h_run with ⟨ex', run_pcm, h_split⟩
      exfalso
      dsimp only [ProcessCreateMessage] at run_pcm
      rcases run_pcm with ⟨ex'', run_pm, h_split2⟩
      dsimp only [ProcessMessage] at run_pm
      rcases run_pm with ⟨errv, _, h_e', _⟩ | ⟨benv', _, run_pm⟩
      · subst h_e'
        rcases h_split2 with ⟨x, _, h_ex'⟩ | ⟨y, h_contra, _⟩
        · subst h_ex'
          obtain ⟨e1, e2, e3, e4⟩ := x
          dsimp only [liftToExecution] at h_split
          rcases h_split with ⟨z, _, h_contra⟩ | ⟨c, h_contra, _⟩ <;> cases h_contra
        · cases h_contra
      · rcases run_pm with ⟨ex''', run_ec, _⟩
        rcases of_executeCode_noneCode (by rw [hp_cm]; rfl) run_ec with ⟨ex4, h_xl, _⟩
        cases h_xl

lemma Xinst.none_inv_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm} {x : Xinst}
    (h_run : Xinst.Run sevm devm x .none (.ok inter))
    (h_ne : sevm.currentTarget ≠ wa)
    (h_pc : Precond wa sevm devm) :
    Precond wa sevm inter := by
  cases x
  case create =>
    dsimp only [Xinst.Run] at h_run
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨endowment, devm1⟩, eq1, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨memoryIndex, devm2⟩, eq2, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨memorySize, devm3⟩, eq3, h_run⟩; · cases h_contra
    rcases h_run with ⟨extendCost, _, h_run⟩
    rcases h_run with ⟨initCodeCost, _, h_run⟩
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨devm4, eq4, h_run⟩; · cases h_contra
    rcases h_run with ⟨devm5, hp5, h_run⟩
    rcases h_run with ⟨newAddress, _, h_run⟩
    subst hp5
    rcases Devm.pop_of_popToNat eq2 with ⟨_, h_pop2⟩
    rcases Devm.pop_of_popToNat eq3 with ⟨_, h_pop3⟩
    have h_st : (devm4.memExtends [(memoryIndex, memorySize)]).state = devm.state := by
      show devm4.state = devm.state
      rw [← (Devm.burn_of_chargeGas eq4).state, ← h_pop3.state, ← h_pop2.state,
        ← (Devm.pop_of_pop eq1).state]
    exact GenericCreate.none_inv_precond h_run (h_pc.state_eq h_st)
  case create2 =>
    dsimp only [Xinst.Run] at h_run
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨endowment, devm1⟩, eq1, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨memoryIndex, devm2⟩, eq2, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨memorySize, devm3⟩, eq3, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨salt, devm4⟩, eq4, h_run⟩; · cases h_contra
    rcases h_run with ⟨extendCost, _, h_run⟩
    rcases h_run with ⟨initCodeHashCost, _, h_run⟩
    rcases h_run with ⟨initCodeCost, _, h_run⟩
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨devm5, eq5, h_run⟩; · cases h_contra
    rcases h_run with ⟨devm6, hp6, h_run⟩
    rcases h_run with ⟨newAddress, _, h_run⟩
    subst hp6
    rcases Devm.pop_of_popToNat eq2 with ⟨_, h_pop2⟩
    rcases Devm.pop_of_popToNat eq3 with ⟨_, h_pop3⟩
    have h_st : (devm5.memExtends [(memoryIndex, memorySize)]).state = devm.state := by
      show devm5.state = devm.state
      rw [← (Devm.burn_of_chargeGas eq5).state, ← (Devm.pop_of_pop eq4).state,
        ← h_pop3.state, ← h_pop2.state, ← (Devm.pop_of_pop eq1).state]
    exact GenericCreate.none_inv_precond h_run (h_pc.state_eq h_st)
  case call =>
    dsimp only [Xinst.Run] at h_run
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨gas, devm1⟩, eq1, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨callee, devm2⟩, eq2, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨value, devm3⟩, eq3, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨inputIndex, devm4⟩, eq4, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨inputSize, devm5⟩, eq5, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨outputIndex, devm6⟩, eq6, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨outputSize, devm7⟩, eq7, h_run⟩; · cases h_contra
    rcases h_run with ⟨extendCost, _, h_run⟩
    rcases h_run with ⟨preAccessCost, _, h_run⟩
    rcases h_run with ⟨devm8, hp10, h_run⟩
    subst hp10
    rcases h_run with ⟨⟨dp, na, code0, dagc, devm9⟩, hp11, h_run⟩
    rcases h_run with ⟨accessCost, _, h_run⟩
    rcases h_run with ⟨createCost, _, h_run⟩
    rcases h_run with ⟨transferCost, _, h_run⟩
    rcases h_run with ⟨⟨msgCallCost, msgCallStipend⟩, _, h_run⟩
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨devm10, eq16, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨_, _, h_run⟩; · cases h_contra
    rcases h_run with ⟨devm11, hp18, h_run⟩
    subst hp18
    rcases h_run with ⟨senderBal, _, h_run⟩
    rcases Devm.pop_of_popToAdr eq2 with ⟨_, _, h_pop2⟩
    rcases Devm.pop_of_popToNat eq4 with ⟨_, h_pop4⟩
    rcases Devm.pop_of_popToNat eq5 with ⟨_, h_pop5⟩
    rcases Devm.pop_of_popToNat eq6 with ⟨_, h_pop6⟩
    rcases Devm.pop_of_popToNat eq7 with ⟨_, h_pop7⟩
    have h_st9 : devm9.state = devm7.state := by
      have h := congrArg (fun q => (q.2.2.2.2 : Devm).state) hp11
      dsimp at h
      rw [h, accessDelegation_state]
      rfl
    have h_st : (devm10.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).state
        = devm.state := by
      show devm10.state = devm.state
      rw [← (Devm.burn_of_chargeGas eq16).state, h_st9, ← h_pop7.state, ← h_pop6.state,
        ← h_pop5.state, ← h_pop4.state, ← (Devm.pop_of_pop eq3).state,
        ← (Devm.pop_of_pop h_pop2).state, ← (Devm.pop_of_pop eq1).state]
    split_ifs at h_run with h_sb
    · rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨devm12, eq20, h_run⟩; · cases h_contra
      rcases h_run with ⟨_, h_ex⟩
      apply h_pc.state_eq
      rw [← Except.ok.inj h_ex]
      show devm12.state = devm.state
      rw [← (Devm.push_of_push eq20).state]
      exact h_st
    · exact GenericCall.none_inv_precond h_run (fun _ => h_ne) (h_pc.state_eq h_st)
  case callcode =>
    dsimp only [Xinst.Run] at h_run
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨gas, devm1⟩, eq1, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨codeAdr, devm2⟩, eq2, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨value, devm3⟩, eq3, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨inputIndex, devm4⟩, eq4, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨inputSize, devm5⟩, eq5, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨outputIndex, devm6⟩, eq6, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨outputSize, devm7⟩, eq7, h_run⟩; · cases h_contra
    rcases h_run with ⟨extendCost, _, h_run⟩
    rcases h_run with ⟨preAccessCost, _, h_run⟩
    rcases h_run with ⟨devm8, hp10, h_run⟩
    subst hp10
    rcases h_run with ⟨⟨dp, nca, code0, dagc, devm9⟩, hp11, h_run⟩
    rcases h_run with ⟨accessCost, _, h_run⟩
    rcases h_run with ⟨transferCost, _, h_run⟩
    rcases h_run with ⟨⟨msgCallCost, msgCallStipend⟩, _, h_run⟩
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨devm10, eq16, h_run⟩; · cases h_contra
    rcases h_run with ⟨devm11, hp18, h_run⟩
    subst hp18
    rcases h_run with ⟨senderBal, _, h_run⟩
    rcases Devm.pop_of_popToAdr eq2 with ⟨_, _, h_pop2⟩
    rcases Devm.pop_of_popToNat eq4 with ⟨_, h_pop4⟩
    rcases Devm.pop_of_popToNat eq5 with ⟨_, h_pop5⟩
    rcases Devm.pop_of_popToNat eq6 with ⟨_, h_pop6⟩
    rcases Devm.pop_of_popToNat eq7 with ⟨_, h_pop7⟩
    have h_st9 : devm9.state = devm7.state := by
      have h := congrArg (fun q => (q.2.2.2.2 : Devm).state) hp11
      dsimp at h
      rw [h, accessDelegation_state]
      rfl
    have h_st : (devm10.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).state
        = devm.state := by
      show devm10.state = devm.state
      rw [← (Devm.burn_of_chargeGas eq16).state, h_st9, ← h_pop7.state, ← h_pop6.state,
        ← h_pop5.state, ← h_pop4.state, ← (Devm.pop_of_pop eq3).state,
        ← (Devm.pop_of_pop h_pop2).state, ← (Devm.pop_of_pop eq1).state]
    split_ifs at h_run with h_sb
    · rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨devm12, eq20, h_run⟩; · cases h_contra
      rcases h_run with ⟨_, h_ex⟩
      apply h_pc.state_eq
      rw [← Except.ok.inj h_ex]
      show devm12.state = devm.state
      rw [← (Devm.push_of_push eq20).state]
      exact h_st
    · exact GenericCall.none_inv_precond h_run (fun _ => h_ne) (h_pc.state_eq h_st)
  case delcall =>
    dsimp only [Xinst.Run] at h_run
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨gas, devm1⟩, eq1, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨codeAdr, devm2⟩, eq2, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨inputIndex, devm3⟩, eq3, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨inputSize, devm4⟩, eq4, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨outputIndex, devm5⟩, eq5, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨outputSize, devm6⟩, eq6, h_run⟩; · cases h_contra
    rcases h_run with ⟨extendCost, _, h_run⟩
    rcases h_run with ⟨preAccessCost, _, h_run⟩
    rcases h_run with ⟨devm7, hp7, h_run⟩
    subst hp7
    rcases h_run with ⟨⟨dp, nca, code0, dagc, devm8⟩, hp8, h_run⟩
    rcases h_run with ⟨accessCost, _, h_run⟩
    rcases h_run with ⟨⟨msgCallCost, msgCallStipend⟩, _, h_run⟩
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨devm9, eq10, h_run⟩; · cases h_contra
    rcases h_run with ⟨devm10, hp10', h_run⟩
    subst hp10'
    rcases Devm.pop_of_popToAdr eq2 with ⟨_, _, h_pop2⟩
    rcases Devm.pop_of_popToNat eq3 with ⟨_, h_pop3⟩
    rcases Devm.pop_of_popToNat eq4 with ⟨_, h_pop4⟩
    rcases Devm.pop_of_popToNat eq5 with ⟨_, h_pop5⟩
    rcases Devm.pop_of_popToNat eq6 with ⟨_, h_pop6⟩
    have h_st8 : devm8.state = devm6.state := by
      have h := congrArg (fun q => (q.2.2.2.2 : Devm).state) hp8
      dsimp at h
      rw [h, accessDelegation_state]
      rfl
    have h_st : (devm9.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).state
        = devm.state := by
      show devm9.state = devm.state
      rw [← (Devm.burn_of_chargeGas eq10).state, h_st8, ← h_pop6.state, ← h_pop5.state,
        ← h_pop4.state, ← h_pop3.state, ← (Devm.pop_of_pop h_pop2).state,
        ← (Devm.pop_of_pop eq1).state]
    exact GenericCall.none_inv_precond h_run (fun h => absurd h Bool.false_ne_true)
      (h_pc.state_eq h_st)
  case statcall =>
    dsimp only [Xinst.Run] at h_run
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨gas, devm1⟩, eq1, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨target, devm2⟩, eq2, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨inputIndex, devm3⟩, eq3, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨inputSize, devm4⟩, eq4, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨outputIndex, devm5⟩, eq5, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨outputSize, devm6⟩, eq6, h_run⟩; · cases h_contra
    rcases h_run with ⟨extendCost, _, h_run⟩
    rcases h_run with ⟨preAccessCost, _, h_run⟩
    rcases h_run with ⟨devm7, hp7, h_run⟩
    subst hp7
    rcases h_run with ⟨⟨dp, na, code0, dagc, devm8⟩, hp8, h_run⟩
    rcases h_run with ⟨accessCost, _, h_run⟩
    rcases h_run with ⟨⟨msgCallCost, msgCallStipend⟩, _, h_run⟩
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨devm9, eq10, h_run⟩; · cases h_contra
    rcases h_run with ⟨devm10, hp10', h_run⟩
    subst hp10'
    rcases Devm.pop_of_popToAdr eq2 with ⟨_, _, h_pop2⟩
    rcases Devm.pop_of_popToNat eq3 with ⟨_, h_pop3⟩
    rcases Devm.pop_of_popToNat eq4 with ⟨_, h_pop4⟩
    rcases Devm.pop_of_popToNat eq5 with ⟨_, h_pop5⟩
    rcases Devm.pop_of_popToNat eq6 with ⟨_, h_pop6⟩
    have h_st8 : devm8.state = devm6.state := by
      have h := congrArg (fun q => (q.2.2.2.2 : Devm).state) hp8
      dsimp at h
      rw [h, accessDelegation_state]
      rfl
    have h_st : (devm9.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).state
        = devm.state := by
      show devm9.state = devm.state
      rw [← (Devm.burn_of_chargeGas eq10).state, h_st8, ← h_pop6.state, ← h_pop5.state,
        ← h_pop4.state, ← h_pop3.state, ← (Devm.pop_of_pop h_pop2).state,
        ← (Devm.pop_of_pop eq1).state]
    exact GenericCall.none_inv_precond h_run (fun _ => h_ne) (h_pc.state_eq h_st)

-- helper lemmas for the case of Xinst execution with a filled xlot,
-- i.e. when an actual nested execution takes place

lemma of_splitXl_some {ξ υ ζ : Type} {e : Except ξ υ} {v : Sevm × Devm × Execution}
    {e' : Except ξ ζ} {q : υ → Prop}
    (h : e.SplitXl (some v) e' q) : ∃ y, e = .ok y ∧ q y := by
  rcases h with ⟨_, _, _, h_contra⟩ | h
  · cases h_contra
  · exact h

lemma of_split_ok {ξ υ ζ : Type} {e : Except ξ υ} {z : ζ} {q : υ → Prop}
    (h : e.Split (.ok z) q) : ∃ y, e = .ok y ∧ q y := by
  rcases h with ⟨_, _, h_contra⟩ | h
  · cases h_contra
  · exact h

lemma of_liftToExecution_split_ok {d inter : Devm}
    {ex : Except (String × _root_.State × AdrSet × Tra) Devm} {q : Devm → Prop}
    (h : (liftToExecution d ex).Split (Except.ok inter) q) :
    ∃ child, ex = .ok child ∧ q child := by
  rcases ex with err | child
  · obtain ⟨e1, e2, e3, e4⟩ := err
    dsimp only [liftToExecution] at h
    rcases h with ⟨_, _, h_contra⟩ | ⟨_, h_contra, _⟩ <;> cases h_contra
  · dsimp only [liftToExecution] at h
    rcases h with ⟨_, h_contra, _⟩ | ⟨y, h_y, h_q⟩
    · cases h_contra
    · cases h_y
      exact ⟨child, rfl, h_q⟩

lemma State.setCode_get_bal {st : _root_.State} {adr a : Adr} {c : ByteArray} :
    ((st.setCode adr c).get a).bal = (st.get a).bal := by
  unfold State.setCode
  by_cases h : adr = a
  · subst h; rw [State.get_set_self]
  · rw [State.get_set_ne h]

lemma State.setCode_get_stor {st : _root_.State} {adr a : Adr} {c : ByteArray} :
    ((st.setCode adr c).get a).stor = (st.get a).stor := by
  unfold State.setCode
  by_cases h : adr = a
  · subst h; rw [State.get_set_self]
  · rw [State.get_set_ne h]

lemma State.setCode_get_code_ne {st : _root_.State} {adr a : Adr} {c : ByteArray}
    (h : adr ≠ a) : ((st.setCode adr c).get a).code = (st.get a).code := by
  unfold State.setCode
  rw [State.get_set_ne h]

lemma State.setStor_get_bal {st : _root_.State} {adr a : Adr} {s : Stor} :
    ((st.setStor adr s).get a).bal = (st.get a).bal := by
  unfold State.setStor
  by_cases h : adr = a
  · subst h; rw [State.get_set_self]
  · rw [State.get_set_ne h]

lemma State.setStor_get_code {st : _root_.State} {adr a : Adr} {s : Stor} :
    ((st.setStor adr s).get a).code = (st.get a).code := by
  unfold State.setStor
  by_cases h : adr = a
  · subst h; rw [State.get_set_self]
  · rw [State.get_set_ne h]

lemma State.setStor_get_stor_ne {st : _root_.State} {adr a : Adr} {s : Stor}
    (h : adr ≠ a) : ((st.setStor adr s).get a).stor = (st.get a).stor := by
  unfold State.setStor
  rw [State.get_set_ne h]

-- balance of an uninvolved account is unchanged by a transfer
lemma of_transfer_bal_other {st st_mid : _root_.State} {caller target a : Adr} {value : B256}
    (h_sub : st.subBal caller value = some st_mid)
    (h_ne_c : caller ≠ a) (h_ne_t : target ≠ a) :
    (st_mid.addBal target value).bal a = st.bal a := by
  rcases State.of_subBal h_sub with ⟨_, h_mid⟩
  subst h_mid
  show ((_root_.State.setBal _ target _).get a).bal = _
  rw [State.setBal_get_ne h_ne_t]
  show ((st.setBal caller _).get a).bal = _
  rw [State.setBal_get_ne h_ne_c]
  rfl

-- balance of the recipient is increased by a transfer from a distinct sender
lemma of_transfer_bal_target {st st_mid : _root_.State} {caller target : Adr} {value : B256}
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
    show ((_root_.State.setBal _ target _).get target).bal = _
    rw [State.setBal_get_self]
    show (st.setBal caller (st.bal caller - value)).bal target + value = _
    rw [h_bal_t]
  rw [h_eq]
  apply B256.toNat_add_eq_of_nof
  unfold B256.Nof
  have h1 := B256.toNat_le_toNat h_le
  have h2 := add_le_sum_of_ne st.bal (Ne.symm h_ne)
  omega

-- the precondition carries over to the initial state of a sub-execution
-- started after a balance transfer from a non-WETH sender
lemma Precond.child_of_transfer {wa : Adr} {sevm sevm' : Sevm} {devm devm' : Devm}
    {st st_mid : _root_.State} {caller target : Adr} {value : B256}
    (h_pc : Precond wa sevm devm)
    (h_ct_ne : sevm.currentTarget ≠ wa)
    (h_ne : caller ≠ wa)
    (h_stor : (st.get wa).stor = (devm.state.get wa).stor)
    (h_code : (st.get wa).code = (devm.state.get wa).code)
    (h_bal : ∀ a, (st.get a).bal = (devm.state.get a).bal)
    (h_sub : st.subBal caller value = some st_mid)
    (h_state : devm'.state = st_mid.addBal target value)
    (h_ct' : sevm'.currentTarget = target)
    (h_val : sevm'.currentTarget = wa → sevm'.value = value) :
    Precond wa sevm' devm' := by
  have h_sum_st : sum st.bal = sum devm.getBal := by
    apply congrArg; funext a; exact h_bal a
  have h_nof_st : sum st.bal < 2 ^ 256 := by rw [h_sum_st]; exact h_pc.nof
  rcases of_state_transfer (callee := target) h_sub h_nof_st with
    ⟨h_t_stor, h_t_code, h_t_sum, _, _, _⟩
  have h_stor' : devm'.getStor wa = devm.getStor wa := by
    show (devm'.state.get wa).stor = (devm.state.get wa).stor
    rw [h_state, h_t_stor wa, h_stor]
  have h_code' : devm'.getCode wa = devm.getCode wa := by
    show (devm'.state.get wa).code = (devm.state.get wa).code
    rw [h_state, h_t_code wa, h_code]
  have h_bal_fun : ∀ a, devm'.getBal a = (st_mid.addBal target value).bal a := by
    intro a
    show (devm'.state.get a).bal = _
    rw [h_state]
    rfl
  have h_solv := h_pc.solvent.right h_ct_ne
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_code']; exact h_pc.code
  · have h_sum' : sum devm'.getBal = sum st.bal := by
      apply Eq.trans _ h_t_sum
      apply congrArg; funext a; exact h_bal_fun a
    rw [h_sum', h_sum_st]; exact h_pc.nof
  · intro h_eq
    have h_v : sevm'.value = value := h_val h_eq
    have h_t_wa : target = wa := h_ct'.symm.trans h_eq
    subst h_t_wa
    have h_bal_wa : (devm'.getBal target).toNat
        = (devm.getBal target).toNat + value.toNat := by
      rw [h_bal_fun target, of_transfer_bal_target h_sub h_ne h_nof_st]
      have h2 : st.bal target = devm.getBal target := h_bal target
      rw [h2]
    rw [h_stor', h_v]
    unfold Stor.Solvent at h_solv ⊢
    rw [B256.toNat_zero] at h_solv
    omega
  · intro h_ne_ct
    have h_t_ne : target ≠ wa := fun hc => h_ne_ct (h_ct'.trans hc)
    have h_bal_wa : devm'.getBal wa = devm.getBal wa := by
      rw [h_bal_fun wa, of_transfer_bal_other h_sub h_ne h_t_ne]
      exact h_bal wa
    rw [h_stor', h_bal_wa]
    exact h_solv

-- the precondition carries over to the initial state of a sub-execution
-- started without a balance transfer
lemma Precond.child_of_eqs {wa : Adr} {sevm sevm' : Sevm} {devm devm' : Devm}
    (h_pc : Precond wa sevm devm)
    (h_ct_ne : sevm.currentTarget ≠ wa)
    (h_state : devm'.state = devm.state)
    (h_val : sevm'.currentTarget = wa → sevm'.value = 0) :
    Precond wa sevm' devm' := by
  have h_solv := h_pc.solvent.right h_ct_ne
  have h_stor' := getStor_eq_of_state_eq h_state wa
  have h_bal' := getBal_eq_of_state_eq h_state wa
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [getCode_eq_of_state_eq h_state wa]; exact h_pc.code
  · have h_bf : devm'.getBal = devm.getBal := funext (getBal_eq_of_state_eq h_state)
    rw [h_bf]; exact h_pc.nof
  · intro h_eq; rw [h_val h_eq, h_stor', h_bal']; exact h_solv
  · intro _; rw [h_stor', h_bal']; exact h_solv

-- nonempty code is unchanged by a (sub-)execution
lemma code_eq_of_exec {sevm' : Sevm} {devm' child : Devm} {wa : Adr}
    (ex_sub : Exec 0 sevm' devm' (.ok child))
    (h_code : some (devm'.getCode wa).toList = Prog.compile weth) :
    child.getCode wa = devm'.getCode wa := by
  have h_ne : (devm'.getCode wa).toList ≠ [] := by
    intro hc
    apply @Prog.compile_ne_nil weth
    rw [← h_code, hc]
  exact Exec.inv_getCode ex_sub wa h_ne

-- the precondition is restored after a successful sub-execution whose final
-- state satisfies the postcondition
lemma Precond.of_postcond {wa : Adr} {sevm sevm' : Sevm} {child inter devm' : Devm}
    (h_post : Postcond wa sevm' child)
    (h_ct_ne : sevm.currentTarget ≠ wa)
    (h_code_pre : some (devm'.getCode wa).toList = Prog.compile weth)
    (h_code_eq : child.getCode wa = devm'.getCode wa)
    (h_stor : (inter.state.get wa).stor = (child.state.get wa).stor)
    (h_code : (inter.state.get wa).code = (child.state.get wa).code)
    (h_bal : ∀ a, (inter.state.get a).bal = (child.state.get a).bal) :
    Precond wa sevm inter := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show some (inter.state.get wa).code.toList = Prog.compile weth
    rw [h_code]
    show some (child.getCode wa).toList = Prog.compile weth
    rw [h_code_eq]
    exact h_code_pre
  · have h_bf : inter.getBal = child.getBal := by
      funext a; exact h_bal a
    rw [h_bf]; exact h_post.nof
  · intro h_eq; exact absurd h_eq h_ct_ne
  · intro _
    have h_stor' : inter.getStor wa = child.getStor wa := h_stor
    have h_bal' : inter.getBal wa = child.getBal wa := h_bal wa
    rw [h_stor', h_bal']
    exact h_post.solvent

lemma chargeCodeGas_state_ok {d d' : Devm}
    (h : processCreateMessage.chargeCodeGas d = .ok d') : d'.state = d.state := by
  simp only [processCreateMessage.chargeCodeGas] at h
  split at h
  · cases h
  · rcases of_bind_eq_ok h with ⟨dG, h_charge, h_if⟩
    split_ifs at h_if
    rw [← Except.ok.inj h_if]
    exact ((Devm.burn_of_chargeGas h_charge).state).symm

lemma GenericCall.some_inv_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm}
    {gas : Nat} {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    {sevm' : Sevm} {devm' : Devm} {exn' : Execution}
    (h_run : GenericCall sevm devm gas value caller target codeAddress stv
      isStatic ii is oi os code dp (.some ⟨sevm', devm', exn'⟩) (.ok inter))
    (ex_sub : Exec 0 sevm' devm' exn')
    (h_ct_ne : sevm.currentTarget ≠ wa)
    (h_ne : stv = true → caller ≠ wa)
    (h_tv : stv = false → target = wa → value = 0)
    (h_pc : Precond wa sevm devm) :
    Precond wa sevm' devm' ∧ (ifOk (Postcond wa sevm') exn' → Precond wa sevm inter) := by
  dsimp only [GenericCall] at h_run
  rcases h_run with ⟨evm1, hp_evm1, h_run⟩
  subst hp_evm1
  split_ifs at h_run with h_depth
  · rcases h_run with ⟨h_contra, _⟩; cases h_contra
  rcases h_run with ⟨calldata, _, h_run⟩
  rcases h_run with ⟨childMsg, hp_cm, h_run⟩
  rcases h_run with ⟨ex', run_pm, h_split⟩
  -- extract the projections of childMsg we need, keeping childMsg abstract
  have hc_state : childMsg.benv.state = devm.state := by rw [hp_cm]; rfl
  have hc_stv : childMsg.shouldTransferValue = stv := by rw [hp_cm]; rfl
  have hc_caller : childMsg.caller = caller := by rw [hp_cm]; rfl
  have hc_value : childMsg.value = value := by rw [hp_cm]; rfl
  have hc_ct : childMsg.currentTarget = target := by rw [hp_cm]; rfl
  have hc_ca : childMsg.codeAddress = some codeAddress := by rw [hp_cm]; rfl
  clear hp_cm
  -- the instruction succeeded, so the sub-message result must be ok
  rcases of_liftToExecution_split_ok h_split with ⟨child, h_ex', h_body⟩
  subst h_ex'
  have h_inter_state : inter.state = child.state := by
    by_cases h_err : child.error.isSome = true
    · rw [if_pos h_err] at h_body
      have h := state_of_push_split h_body
      exact h
    · rw [if_neg h_err] at h_body
      have h := state_of_push_split h_body
      exact h
  clear h_body
  -- unpack the process-message run
  dsimp only [ProcessMessage] at run_pm
  rcases of_splitXl_some run_pm with ⟨benv', eq_bt, run_pm'⟩
  rcases run_pm' with ⟨ex'', run_ec, h_split2⟩
  rcases of_split_ok h_split2 with ⟨evm2, h_ex'', h_if⟩
  -- the xlot contents are the initial state of the sub-execution
  have hc_ca' : (childMsg.withBenv benv').codeAddress = some codeAddress := hc_ca
  rcases of_executeCode_someCode hc_ca' run_ec with
    ⟨_, h_xl_none, _⟩ | ⟨_, ex''', h_xl_some, h_he⟩
  · cases h_xl_none
  have h_tup := Option.some.inj h_xl_some
  have h_sevm' : sevm' = initSevm (childMsg.withBenv benv') := congrArg Prod.fst h_tup
  have h_devm' : devm' = initDevm (childMsg.withBenv benv') :=
    congrArg (fun p => p.2.1) h_tup
  have h_exn' : exn' = ex''' := congrArg (fun p => p.2.2) h_tup
  subst h_exn'
  clear h_tup h_xl_some
  -- projections of the sub-execution's initial state
  have h_ds : devm'.state = benv'.state := by rw [h_devm']; rfl
  have h_ct' : sevm'.currentTarget = target := by rw [h_sevm']; exact hc_ct
  have h_v' : sevm'.value = value := by rw [h_sevm']; exact hc_value
  -- part 1 : the precondition holds for the sub-execution's initial state
  have h_pre1 : Precond wa sevm' devm' := by
    by_cases h_stv : stv = true
    · rcases of_benvAfterTransfer (hc_stv.trans h_stv) eq_bt with ⟨st_mid, h_sub, hB⟩
      rw [hc_state, hc_caller, hc_value] at h_sub
      have h_state : devm'.state = st_mid.addBal target value := by
        rw [h_ds, hB, hc_ct, hc_value]
        rfl
      exact Precond.child_of_transfer h_pc h_ct_ne (h_ne h_stv) rfl rfl (fun _ => rfl)
        h_sub h_state h_ct' (fun _ => h_v')
    · have h_stv' : ¬ childMsg.shouldTransferValue = true := by rw [hc_stv]; exact h_stv
      have h_benv : benv' = childMsg.benv := of_benvAfterTransfer_no h_stv' eq_bt
      have h_state : devm'.state = devm.state := by
        rw [h_ds, h_benv]; exact hc_state
      apply Precond.child_of_eqs h_pc h_ct_ne h_state
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
    · have h_eq2 : evm2 = evm2' := Except.ok.inj (h_ex''.symm.trans h_ok2)
      subst h_eq2
      rw [if_pos h_some2] at h_if
      have h_child := Except.ok.inj h_if
      apply h_pc.state_eq
      rw [h_inter_state, ← h_child]
      show childMsg.benv.state = devm.state
      exact hc_state
    · rw [h_ex''] at h_err2
      cases h_err2
  · -- sub-execution succeeded
    dsimp only [executeCode.handleError] at h_he
    have h_eq2 : child3 = evm2 := Except.ok.inj (h_he.trans h_ex'')
    subst h_eq2
    have h_post : Postcond wa sevm' child3 := h_ifOk
    by_cases h_err : child3.error.isSome = true
    · -- the sub-execution set the error flag : the parent state is rolled back
      rw [if_pos h_err] at h_if
      have h_child := Except.ok.inj h_if
      apply h_pc.state_eq
      rw [h_inter_state, ← h_child]
      show childMsg.benv.state = devm.state
      exact hc_state
    · -- clean success : reconstruct the precondition from the postcondition
      rw [if_neg h_err] at h_if
      have h_child := Except.ok.inj h_if
      subst h_child
      exact Precond.of_postcond h_post h_ct_ne h_pre1.code
        (code_eq_of_exec ex_sub h_pre1.code)
        (congrArg (fun st => (st.get wa).stor) h_inter_state)
        (congrArg (fun st => (st.get wa).code) h_inter_state)
        (fun a => congrArg (fun st => (st.get a).bal) h_inter_state)

lemma Devm.setCode_state {d : Devm} {adr : Adr} {c : ByteArray} :
    (d.setCode adr c).state = d.state.setCode adr c := rfl

lemma GenericCreate.some_inv_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm}
    {endowment : B256} {newAddress : Adr} {memoryIndex memorySize : Nat}
    {sevm' : Sevm} {devm' : Devm} {exn' : Execution}
    (h_run : GenericCreate sevm devm endowment newAddress memoryIndex memorySize
      (.some ⟨sevm', devm', exn'⟩) (.ok inter))
    (ex_sub : Exec 0 sevm' devm' exn')
    (h_ct_ne : sevm.currentTarget ≠ wa)
    (h_pc : Precond wa sevm devm) :
    Precond wa sevm' devm' ∧ (ifOk (Postcond wa sevm') exn' → Precond wa sevm inter) := by
  dsimp only [GenericCreate] at h_run
  rcases h_run with ⟨calldata, _, h_run⟩
  rcases of_splitXl_some h_run with ⟨_, _, h_run⟩
  rcases h_run with ⟨devm1, hp1, h_run⟩
  rcases h_run with ⟨createMsgGas, _, h_run⟩
  rcases h_run with ⟨devm2, hp2, h_run⟩
  rcases of_splitXl_some h_run with ⟨_, _, h_run⟩
  rcases h_run with ⟨devm3, hp3, h_run⟩
  rcases h_run with ⟨sender, _, h_run⟩
  split_ifs at h_run with h_chk
  · rcases h_run with ⟨h_contra, _⟩; cases h_contra
  rcases h_run with ⟨devm4, hp4, h_run⟩
  split_ifs at h_run with h_coll
  · rcases h_run with ⟨h_contra, _⟩; cases h_contra
  rcases h_run with ⟨childMsg, hp_cm, h_run⟩
  rcases h_run with ⟨ex', run_pcm, h_split⟩
  -- state at the point of message creation
  have h_st4 : devm4.state = devm.state.incrNonce sevm.currentTarget := by
    rw [hp4, hp3, hp2, hp1]
    rfl
  -- the new address cannot be the WETH address, whose code is nonempty
  have h_new_ne : newAddress ≠ wa := by
    intro hc
    subst hc
    push_neg at h_coll
    have h_size := h_coll.2.1
    apply @Prog.compile_ne_nil weth
    rw [← h_pc.code]
    have h_code4 : (devm4.state.get newAddress).code = devm.getCode newAddress := by
      rw [h_st4]
      exact State.incrNonce_get_code
    rw [← h_code4]
    have h_nil : (devm4.state.get newAddress).code.toList = [] := by
      have h_len := ByteArray.size_eq_length_toList (devm4.state.get newAddress).code
      rw [h_size] at h_len
      cases h_toList : (devm4.state.get newAddress).code.toList
      · rfl
      · rw [h_toList] at h_len
        cases h_len
    rw [h_nil]
  -- projections of childMsg
  have hc_state : childMsg.benv.state = devm4.state := by rw [hp_cm]
  have hc_caller : childMsg.caller = sevm.currentTarget := by rw [hp_cm]
  have hc_value : childMsg.value = endowment := by rw [hp_cm]
  have hc_ct : childMsg.currentTarget = newAddress := by rw [hp_cm]
  have hc_ca : childMsg.codeAddress = .none := by rw [hp_cm]
  have hc_stv : childMsg.shouldTransferValue = true := by rw [hp_cm]
  clear hp_cm
  -- the instruction succeeded, so the sub-message result must be ok
  rcases of_liftToExecution_split_ok h_split with ⟨child, h_ex', h_body⟩
  subst h_ex'
  have h_inter_state : inter.state = child.state := by
    by_cases h_err : child.error.isSome = true
    · rw [if_pos h_err] at h_body
      have h := (Devm.push_of_push h_body).state
      exact h.symm
    · rw [if_neg h_err] at h_body
      have h := (Devm.push_of_push h_body).state
      exact h.symm
  clear h_body
  -- unpack the process-create-message run
  dsimp only [ProcessCreateMessage] at run_pcm
  rcases run_pcm with ⟨ex'', run_pm, h_split2⟩
  rcases of_split_ok h_split2 with ⟨evmA, h_ex'', h_ifA⟩
  dsimp only [ProcessMessage] at run_pm
  rcases of_splitXl_some run_pm with ⟨benv', eq_bt, run_pm'⟩
  rcases run_pm' with ⟨ex''', run_ec, h_split3⟩
  rw [h_ex''] at h_split3
  rcases of_split_ok h_split3 with ⟨evmB, h_ex''', h_ifB⟩
  -- projections of the create message
  have hP_state : (processCreateMessage.msg childMsg).benv.state
      = (childMsg.benv.state.setStor childMsg.currentTarget Stor.empty).incrNonce
          childMsg.currentTarget := rfl
  have hP_caller : (processCreateMessage.msg childMsg).caller = sevm.currentTarget :=
    hc_caller
  have hP_value : (processCreateMessage.msg childMsg).value = endowment := hc_value
  have hP_stv : (processCreateMessage.msg childMsg).shouldTransferValue = true := hc_stv
  -- the xlot contents are the initial state of the sub-execution
  have h_ca' : ((processCreateMessage.msg childMsg).withBenv benv').codeAddress = .none :=
    hc_ca
  rcases of_executeCode_noneCode h_ca' run_ec with ⟨ex4, h_xl_some, h_he⟩
  have h_tup := Option.some.inj h_xl_some
  have h_sevm' : sevm' = initSevm ((processCreateMessage.msg childMsg).withBenv benv') :=
    congrArg Prod.fst h_tup
  have h_devm' : devm' = initDevm ((processCreateMessage.msg childMsg).withBenv benv') :=
    congrArg (fun p => p.2.1) h_tup
  have h_exn' : exn' = ex4 := congrArg (fun p => p.2.2) h_tup
  subst h_exn'
  clear h_tup h_xl_some
  have h_ds : devm'.state = benv'.state := by rw [h_devm']; rfl
  have h_ct' : sevm'.currentTarget = newAddress := by rw [h_sevm']; exact hc_ct
  -- the balance transfer performed before the sub-execution
  rcases of_benvAfterTransfer hP_stv eq_bt with ⟨st_mid, h_sub, hB⟩
  rw [hP_state, hP_caller, hP_value, hc_ct] at h_sub
  have h_base_stor :
      (((childMsg.benv.state.setStor newAddress Stor.empty).incrNonce newAddress).get wa).stor
        = (devm.state.get wa).stor := by
    rw [State.incrNonce_get_stor, State.setStor_get_stor_ne h_new_ne, hc_state, h_st4,
      State.incrNonce_get_stor]
  have h_base_code :
      (((childMsg.benv.state.setStor newAddress Stor.empty).incrNonce newAddress).get wa).code
        = (devm.state.get wa).code := by
    rw [State.incrNonce_get_code, State.setStor_get_code, hc_state, h_st4,
      State.incrNonce_get_code]
  have h_base_bal : ∀ a,
      (((childMsg.benv.state.setStor newAddress Stor.empty).incrNonce newAddress).get a).bal
        = (devm.state.get a).bal := by
    intro a
    rw [State.incrNonce_get_bal, State.setStor_get_bal, hc_state, h_st4,
      State.incrNonce_get_bal]
  -- part 1 : the precondition holds for the sub-execution's initial state
  have h_pre1 : Precond wa sevm' devm' := by
    have h_state : devm'.state = st_mid.addBal newAddress endowment := by
      rw [h_ds, hB]
      show st_mid.addBal childMsg.currentTarget childMsg.value = _
      rw [hc_ct, hc_value]
    apply Precond.child_of_transfer h_pc h_ct_ne h_ct_ne h_base_stor h_base_code h_base_bal
      h_sub h_state h_ct'
    intro hc
    exact absurd (h_ct'.symm.trans hc) h_new_ne
  refine ⟨h_pre1, ?_⟩
  -- part 2 : the precondition is restored after the create returns
  intro h_ifOk
  -- when the sub-message rolls back, the parent state is unchanged modulo the nonce
  have h_rb : child.state = childMsg.benv.state → Precond wa sevm inter := by
    intro h_cs
    refine Precond.of_eqs h_pc ?_ ?_ ?_
    · show (inter.state.get wa).code = (devm.state.get wa).code
      rw [h_inter_state, h_cs, hc_state, h_st4]
      exact State.incrNonce_get_code
    · funext b
      show (inter.state.get b).bal = (devm.state.get b).bal
      rw [h_inter_state, h_cs, hc_state, h_st4]
      exact State.incrNonce_get_bal
    · show (inter.state.get wa).stor = (devm.state.get wa).stor
      rw [h_inter_state, h_cs, hc_state, h_st4]
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
    · have h_eqB : evmB = evmB' := Except.ok.inj (h_ex'''.symm.trans h_okB)
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
    · rw [h_ex'''] at h_errB
      cases h_errB
  · -- sub-execution succeeded
    dsimp only [executeCode.handleError] at h_he
    have h_eqB : child4 = evmB := Except.ok.inj (h_he.trans h_ex''')
    subst h_eqB
    have h_post : Postcond wa sevm' child4 := h_ifOk
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
      rcases h_cc : processCreateMessage.chargeCodeGas child4 with ⟨errC, evmC⟩ | evmC
      · -- code-deposit gas charge failed
        simp only [h_cc] at h_ifA
        by_cases h_eh : isExceptionalHalt errC
        · rw [if_pos h_eh] at h_ifA
          have h_child := Except.ok.inj h_ifA
          apply h_rb
          rw [← h_child]
          rfl
        · rw [if_neg h_eh] at h_ifA
          cases h_ifA
      · -- code deposit succeeded : reconstruct the precondition
        simp only [h_cc] at h_ifA
        have h_child := Except.ok.inj h_ifA
        have h_stC : evmC.state = child4.state := chargeCodeGas_state_ok h_cc
        apply Precond.of_postcond h_post h_ct_ne h_pre1.code
          (code_eq_of_exec ex_sub h_pre1.code)
        · rw [h_inter_state, ← h_child, Devm.setCode_state, h_stC, hc_ct,
            State.setCode_get_stor]
        · rw [h_inter_state, ← h_child, Devm.setCode_state, h_stC, hc_ct,
            State.setCode_get_code_ne h_new_ne]
        · intro a
          rw [h_inter_state, ← h_child, Devm.setCode_state, h_stC, hc_ct,
            State.setCode_get_bal]

lemma Xinst.some_inv_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm} {x : Xinst}
    {sevm' : Sevm} {devm' : Devm} {exn' : Execution}
    (h_run : Xinst.Run sevm devm x (.some ⟨sevm', devm', exn'⟩) (.ok inter))
    (ex_sub : Exec 0 sevm' devm' exn')
    (h_ne : sevm.currentTarget ≠ wa)
    (h_pc : Precond wa sevm devm) :
    Precond wa sevm' devm' ∧ (ifOk (Postcond wa sevm') exn' → Precond wa sevm inter) := by
  cases x
  case create =>
    dsimp only [Xinst.Run] at h_run
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨endowment, devm1⟩, eq1, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨memoryIndex, devm2⟩, eq2, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨memorySize, devm3⟩, eq3, h_run⟩; · cases h_contra
    rcases h_run with ⟨extendCost, _, h_run⟩
    rcases h_run with ⟨initCodeCost, _, h_run⟩
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨devm4, eq4, h_run⟩; · cases h_contra
    rcases h_run with ⟨devm5, hp5, h_run⟩
    rcases h_run with ⟨newAddress, _, h_run⟩
    subst hp5
    rcases Devm.pop_of_popToNat eq2 with ⟨_, h_pop2⟩
    rcases Devm.pop_of_popToNat eq3 with ⟨_, h_pop3⟩
    have h_st : (devm4.memExtends [(memoryIndex, memorySize)]).state = devm.state := by
      show devm4.state = devm.state
      rw [← (Devm.burn_of_chargeGas eq4).state, ← h_pop3.state, ← h_pop2.state,
        ← (Devm.pop_of_pop eq1).state]
    exact GenericCreate.some_inv_precond h_run ex_sub h_ne (h_pc.state_eq h_st)
  case create2 =>
    dsimp only [Xinst.Run] at h_run
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨endowment, devm1⟩, eq1, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨memoryIndex, devm2⟩, eq2, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨memorySize, devm3⟩, eq3, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨salt, devm4⟩, eq4, h_run⟩; · cases h_contra
    rcases h_run with ⟨extendCost, _, h_run⟩
    rcases h_run with ⟨initCodeHashCost, _, h_run⟩
    rcases h_run with ⟨initCodeCost, _, h_run⟩
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨devm5, eq5, h_run⟩; · cases h_contra
    rcases h_run with ⟨devm6, hp6, h_run⟩
    rcases h_run with ⟨newAddress, _, h_run⟩
    subst hp6
    rcases Devm.pop_of_popToNat eq2 with ⟨_, h_pop2⟩
    rcases Devm.pop_of_popToNat eq3 with ⟨_, h_pop3⟩
    have h_st : (devm5.memExtends [(memoryIndex, memorySize)]).state = devm.state := by
      show devm5.state = devm.state
      rw [← (Devm.burn_of_chargeGas eq5).state, ← (Devm.pop_of_pop eq4).state,
        ← h_pop3.state, ← h_pop2.state, ← (Devm.pop_of_pop eq1).state]
    exact GenericCreate.some_inv_precond h_run ex_sub h_ne (h_pc.state_eq h_st)
  case call =>
    dsimp only [Xinst.Run] at h_run
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨gas, devm1⟩, eq1, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨callee, devm2⟩, eq2, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨value, devm3⟩, eq3, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨inputIndex, devm4⟩, eq4, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨inputSize, devm5⟩, eq5, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨outputIndex, devm6⟩, eq6, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨outputSize, devm7⟩, eq7, h_run⟩; · cases h_contra
    rcases h_run with ⟨extendCost, _, h_run⟩
    rcases h_run with ⟨preAccessCost, _, h_run⟩
    rcases h_run with ⟨devm8, hp10, h_run⟩
    subst hp10
    rcases h_run with ⟨⟨dp, na, code0, dagc, devm9⟩, hp11, h_run⟩
    rcases h_run with ⟨accessCost, _, h_run⟩
    rcases h_run with ⟨createCost, _, h_run⟩
    rcases h_run with ⟨transferCost, _, h_run⟩
    rcases h_run with ⟨⟨msgCallCost, msgCallStipend⟩, _, h_run⟩
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨devm10, eq16, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨_, _, h_run⟩; · cases h_contra
    rcases h_run with ⟨devm11, hp18, h_run⟩
    subst hp18
    rcases h_run with ⟨senderBal, _, h_run⟩
    rcases Devm.pop_of_popToAdr eq2 with ⟨_, _, h_pop2⟩
    rcases Devm.pop_of_popToNat eq4 with ⟨_, h_pop4⟩
    rcases Devm.pop_of_popToNat eq5 with ⟨_, h_pop5⟩
    rcases Devm.pop_of_popToNat eq6 with ⟨_, h_pop6⟩
    rcases Devm.pop_of_popToNat eq7 with ⟨_, h_pop7⟩
    have h_st9 : devm9.state = devm7.state := by
      have h := congrArg (fun q => (q.2.2.2.2 : Devm).state) hp11
      dsimp at h
      rw [h, accessDelegation_state]
      rfl
    have h_st : (devm10.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).state
        = devm.state := by
      show devm10.state = devm.state
      rw [← (Devm.burn_of_chargeGas eq16).state, h_st9, ← h_pop7.state, ← h_pop6.state,
        ← h_pop5.state, ← h_pop4.state, ← (Devm.pop_of_pop eq3).state,
        ← (Devm.pop_of_pop h_pop2).state, ← (Devm.pop_of_pop eq1).state]
    split_ifs at h_run with h_sb
    · rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨devm12, eq20, h_run⟩; · cases h_contra
      rcases h_run with ⟨h_xl, _⟩
      cases h_xl
    · exact GenericCall.some_inv_precond h_run ex_sub h_ne (fun _ => h_ne)
        (fun h => Bool.noConfusion h) (h_pc.state_eq h_st)
  case callcode =>
    dsimp only [Xinst.Run] at h_run
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨gas, devm1⟩, eq1, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨codeAdr, devm2⟩, eq2, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨value, devm3⟩, eq3, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨inputIndex, devm4⟩, eq4, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨inputSize, devm5⟩, eq5, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨outputIndex, devm6⟩, eq6, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨outputSize, devm7⟩, eq7, h_run⟩; · cases h_contra
    rcases h_run with ⟨extendCost, _, h_run⟩
    rcases h_run with ⟨preAccessCost, _, h_run⟩
    rcases h_run with ⟨devm8, hp10, h_run⟩
    subst hp10
    rcases h_run with ⟨⟨dp, nca, code0, dagc, devm9⟩, hp11, h_run⟩
    rcases h_run with ⟨accessCost, _, h_run⟩
    rcases h_run with ⟨transferCost, _, h_run⟩
    rcases h_run with ⟨⟨msgCallCost, msgCallStipend⟩, _, h_run⟩
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨devm10, eq16, h_run⟩; · cases h_contra
    rcases h_run with ⟨devm11, hp18, h_run⟩
    subst hp18
    rcases h_run with ⟨senderBal, _, h_run⟩
    rcases Devm.pop_of_popToAdr eq2 with ⟨_, _, h_pop2⟩
    rcases Devm.pop_of_popToNat eq4 with ⟨_, h_pop4⟩
    rcases Devm.pop_of_popToNat eq5 with ⟨_, h_pop5⟩
    rcases Devm.pop_of_popToNat eq6 with ⟨_, h_pop6⟩
    rcases Devm.pop_of_popToNat eq7 with ⟨_, h_pop7⟩
    have h_st9 : devm9.state = devm7.state := by
      have h := congrArg (fun q => (q.2.2.2.2 : Devm).state) hp11
      dsimp at h
      rw [h, accessDelegation_state]
      rfl
    have h_st : (devm10.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).state
        = devm.state := by
      show devm10.state = devm.state
      rw [← (Devm.burn_of_chargeGas eq16).state, h_st9, ← h_pop7.state, ← h_pop6.state,
        ← h_pop5.state, ← h_pop4.state, ← (Devm.pop_of_pop eq3).state,
        ← (Devm.pop_of_pop h_pop2).state, ← (Devm.pop_of_pop eq1).state]
    split_ifs at h_run with h_sb
    · rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨devm12, eq20, h_run⟩; · cases h_contra
      rcases h_run with ⟨h_xl, _⟩
      cases h_xl
    · exact GenericCall.some_inv_precond h_run ex_sub h_ne (fun _ => h_ne)
        (fun h => Bool.noConfusion h) (h_pc.state_eq h_st)
  case delcall =>
    dsimp only [Xinst.Run] at h_run
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨gas, devm1⟩, eq1, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨codeAdr, devm2⟩, eq2, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨inputIndex, devm3⟩, eq3, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨inputSize, devm4⟩, eq4, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨outputIndex, devm5⟩, eq5, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨outputSize, devm6⟩, eq6, h_run⟩; · cases h_contra
    rcases h_run with ⟨extendCost, _, h_run⟩
    rcases h_run with ⟨preAccessCost, _, h_run⟩
    rcases h_run with ⟨devm7, hp7, h_run⟩
    subst hp7
    rcases h_run with ⟨⟨dp, nca, code0, dagc, devm8⟩, hp8, h_run⟩
    rcases h_run with ⟨accessCost, _, h_run⟩
    rcases h_run with ⟨⟨msgCallCost, msgCallStipend⟩, _, h_run⟩
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨devm9, eq10, h_run⟩; · cases h_contra
    rcases h_run with ⟨devm10, hp10', h_run⟩
    subst hp10'
    rcases Devm.pop_of_popToAdr eq2 with ⟨_, _, h_pop2⟩
    rcases Devm.pop_of_popToNat eq3 with ⟨_, h_pop3⟩
    rcases Devm.pop_of_popToNat eq4 with ⟨_, h_pop4⟩
    rcases Devm.pop_of_popToNat eq5 with ⟨_, h_pop5⟩
    rcases Devm.pop_of_popToNat eq6 with ⟨_, h_pop6⟩
    have h_st8 : devm8.state = devm6.state := by
      have h := congrArg (fun q => (q.2.2.2.2 : Devm).state) hp8
      dsimp at h
      rw [h, accessDelegation_state]
      rfl
    have h_st : (devm9.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).state
        = devm.state := by
      show devm9.state = devm.state
      rw [← (Devm.burn_of_chargeGas eq10).state, h_st8, ← h_pop6.state, ← h_pop5.state,
        ← h_pop4.state, ← h_pop3.state, ← (Devm.pop_of_pop h_pop2).state,
        ← (Devm.pop_of_pop eq1).state]
    exact GenericCall.some_inv_precond h_run ex_sub h_ne (fun h => Bool.noConfusion h)
      (fun _ h => absurd h h_ne) (h_pc.state_eq h_st)
  case statcall =>
    dsimp only [Xinst.Run] at h_run
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨gas, devm1⟩, eq1, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨target, devm2⟩, eq2, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨inputIndex, devm3⟩, eq3, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨inputSize, devm4⟩, eq4, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨outputIndex, devm5⟩, eq5, h_run⟩; · cases h_contra
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨⟨outputSize, devm6⟩, eq6, h_run⟩; · cases h_contra
    rcases h_run with ⟨extendCost, _, h_run⟩
    rcases h_run with ⟨preAccessCost, _, h_run⟩
    rcases h_run with ⟨devm7, hp7, h_run⟩
    subst hp7
    rcases h_run with ⟨⟨dp, na, code0, dagc, devm8⟩, hp8, h_run⟩
    rcases h_run with ⟨accessCost, _, h_run⟩
    rcases h_run with ⟨⟨msgCallCost, msgCallStipend⟩, _, h_run⟩
    rcases h_run with ⟨_, _, h_contra, _⟩ | ⟨devm9, eq10, h_run⟩; · cases h_contra
    rcases h_run with ⟨devm10, hp10', h_run⟩
    subst hp10'
    rcases Devm.pop_of_popToAdr eq2 with ⟨_, _, h_pop2⟩
    rcases Devm.pop_of_popToNat eq3 with ⟨_, h_pop3⟩
    rcases Devm.pop_of_popToNat eq4 with ⟨_, h_pop4⟩
    rcases Devm.pop_of_popToNat eq5 with ⟨_, h_pop5⟩
    rcases Devm.pop_of_popToNat eq6 with ⟨_, h_pop6⟩
    have h_st8 : devm8.state = devm6.state := by
      have h := congrArg (fun q => (q.2.2.2.2 : Devm).state) hp8
      dsimp at h
      rw [h, accessDelegation_state]
      rfl
    have h_st : (devm9.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).state
        = devm.state := by
      show devm9.state = devm.state
      rw [← (Devm.burn_of_chargeGas eq10).state, h_st8, ← h_pop6.state, ← h_pop5.state,
        ← h_pop4.state, ← h_pop3.state, ← (Devm.pop_of_pop h_pop2).state,
        ← (Devm.pop_of_pop eq1).state]
    exact GenericCall.some_inv_precond h_run ex_sub h_ne (fun _ => h_ne)
      (fun h => Bool.noConfusion h) (h_pc.state_eq h_st)

lemma Postcond.dest_delete {wa : Adr} {sevm : Sevm} {devm : Devm}
    (h_ne : sevm.currentTarget ≠ wa) (h_pc : Precond wa sevm devm) :
    Postcond wa sevm
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
      (addAccountToDelete (devm.setBal sevm.currentTarget 0) sevm.currentTarget).getStor wa =
        devm.getStor wa := by
    show ((devm.state.setBal sevm.currentTarget 0).get wa).stor = (devm.state.get wa).stor
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
  constructor
  · have h_nof := h_pc.nof
    omega
  · unfold Devm.PostSolvent
    rw [h_stor_eq, h_bal_ne wa h_ne]
    exact h_pc.solvent.right h_ne

lemma Linst.inv_postcond {wa : Adr} {sevm : Sevm} {pre post : Devm} {l : Linst}
    (h_run : Linst.Run sevm pre l (.ok post))
    (h_ne : sevm.currentTarget ≠ wa)
    (h_pc : Precond wa sevm pre) :
    Postcond wa sevm post := by
  cases l
  case stop =>
    dsimp [Linst.Run, Linst.run] at h_run
    injection h_run with h_eq; subst h_eq
    exact postcond_of_precond h_pc
  case ret =>
    have h_bal : pre.getBal = post.getBal :=
      (inferInstanceAs (Linst.Hinv Devm.getBal Devm.getBal Linst.ret)).inv h_run
    have h_stor : pre.getStor = post.getStor :=
      (inferInstanceAs (Linst.Hinv Devm.getStor Devm.getStor Linst.ret)).inv h_run
    constructor
    · rw [← h_bal]; exact h_pc.nof
    · unfold Devm.PostSolvent Stor.Solvent
      have hb : post.getBal wa = pre.getBal wa := (congr_fun h_bal wa).symm
      have hs : post.getStor wa = pre.getStor wa := (congr_fun h_stor wa).symm
      rw [hb, hs]
      exact h_pc.solvent.right h_ne
  case rev =>
    dsimp [Linst.Run, Linst.run] at h_run
    rcases of_bind_eq_ok h_run with ⟨_, _, h2⟩
    rcases of_bind_eq_ok h2 with ⟨_, _, h4⟩
    rcases of_bind_eq_ok h4 with ⟨_, _, h6⟩
    contradiction
  case dest =>
    dsimp [Linst.Run, Linst.run] at h_run
    rcases of_bind_eq_ok h_run with ⟨⟨dest_a, devm1⟩, h_pop, h_run1⟩
    rcases of_bind_eq_ok h_run1 with ⟨devm2, h_charge, h_run2⟩
    rcases of_bind_eq_ok h_run2 with ⟨_, h_assert, h_run3⟩
    rcases of_bind_eq_ok h_run3 with ⟨devm3, h_sub, h_run4⟩
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
    have h_pc1 : Precond wa sevm devm1 := by
      apply Precond.of_eqs h_pc
      · exact Devm.popToAdr_getCode_eq h_pop wa
      · ext a; exact Devm.popToAdr_getBal_eq h_pop a
      · exact congr_fun (Devm.popToAdr_getStor_eq h_pop).symm wa
    have h_pc2 : Precond wa sevm devm2 := by
      apply Precond.of_eqs h_pc1
      · have h_code : devm2.getCode = devm1.getCode := by
          funext a
          have h1 := chargeGas_getCode_eq h_charge a
          have h2 : (if ((dest_a, devm1).1 ∉ (dest_a, devm1).2.accessedAddresses) then (addAccessedAddress (dest_a, devm1).2 (dest_a, devm1).1, gasSelfDestruct + gasColdAccountAccess) else ((dest_a, devm1).2, gasSelfDestruct)).1.getCode a = devm1.getCode a := by
            split <;> rfl
          exact h1.trans h2
        exact congr_fun h_code wa
      · exact h_bal2
      · have h_stor : devm2.getStor = devm1.getStor := by
          have h1 := (chargeGas_getStor_eq h_charge).symm
          have h2 : (if ((dest_a, devm1).1 ∉ (dest_a, devm1).2.accessedAddresses) then (addAccessedAddress (dest_a, devm1).2 (dest_a, devm1).1, gasSelfDestruct + gasColdAccountAccess) else ((dest_a, devm1).2, gasSelfDestruct)).1.getStor = devm1.getStor := by
            split <;> rfl
          exact h1.trans h2
        exact congr_fun h_stor wa
    have h_pc3 : Precond wa sevm (devm3.addBal dest_a ((dest_a, devm1).2.getAcct sevm.currentTarget).bal) := by
      exact Precond.transfer_state h_pc2 h_ne h_sub_st rfl
    clear h_run h_run1 h_run2 h_run3
    split at h_run4
    · rw [← Except.ok.inj h_run4]
      exact Postcond.dest_delete h_ne h_pc3
    · rw [← Except.ok.inj h_run4]
      exact postcond_of_precond h_pc3

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
  · intro pc' sevm' pre' n' inter' h_at' h_run' h_ne' h_pc'
    cases n' with
    | push xs le =>
      dsimp only [Ninst.Run'] at h_run'
      rcases of_bind_eq_ok h_run' with ⟨devm1, h_charge, h_push⟩
      exact h_pc'.state_eq
        (((Devm.burn_of_chargeGas h_charge).state).trans
          ((Devm.push_of_push h_push).state)).symm
    | reg r =>
      have h_reg : Rinst.run ⟨pc', sevm', pre'⟩ r = .ok inter' := h_run'
      by_cases h_ss : r = Rinst.sstore
      · subst h_ss
        refine Precond.of_eqs h_pc' (sstore_inv_getCode h_reg wa) ?_
          (sstore_inv_getStor_ne h_reg h_ne')
        funext b
        exact sstore_inv_getBal h_reg b
      · exact Precond.of_eqs h_pc' (Rinst.inv_getCode h_reg wa) (Rinst.inv_bal h_reg).symm
          (congr_fun (Rinst.inv_stor h_ss h_reg) wa).symm
    | exec x => exact Xinst.none_inv_precond h_run' h_ne' h_pc'
  · intro pc' sevm' pre' n' sevm'' devm'' exn'' inter' h_at' h_run' ex_sub' h_ne' h_pc'
    cases n' with
    | push xs le => exact h_run'.elim
    | reg r => exact h_run'.elim
    | exec x => exact Xinst.some_inv_precond h_run' ex_sub' h_ne' h_pc'
  · intro pc' sevm' pre' j' pc'' inter' h_at' h_run' h_ne' h_pc'
    exact Precond.state_eq h_pc' (Jinst.inv_state h_run')
  · intro pc' sevm' pre' l' post' h_at' h_run' h_ne' h_pc'
    exact Linst.inv_postcond h_run' h_ne' h_pc'
  · exact exc
  · exact ⟨h_pc.1, λ h => ⟨h_code h, rfl⟩⟩
  · exact h_pc



-- Solvency preservation above the frame level : the theorems below lift
-- `weth_inv_solvent` through each layer of the executable semantics in
-- Elevm/Execution.lean, stated directly over the raw execution functions.

-- The WETH invariant on a bare world state, as it stands between
-- transactions and blocks (no active call frame).
structure State.Inv (wa : Adr) (w : _root_.State) : Prop where
  (code : some (w.getCode wa).toList = Prog.compile weth)
  (nof : _root_.SumNof w.bal)
  (solvent : w.Solvent wa)

-- Counterpart of `weth_inv_solvent` for the raw executable `exec`, with
-- the recursion limit quantified away.
theorem exec_inv_solvent (wa : Adr) (lim : Nat)
    (sevm : Sevm) (pre post : Devm)
    (h_run : exec ⟨0, sevm, pre⟩ lim = .ok post)
    (h_code : sevm.currentTarget = wa → some sevm.code.toList = Prog.compile weth)
    (h_pc : Precond wa sevm pre) : Postcond wa sevm post := by
  have fit : (Except.ok post : Execution).Fit := by
    simp [Except.Fit, Except.Lim, Except.toError?]
  obtain ⟨exc⟩ := (exec_iff_exec_eq 0 sevm pre (.ok post)).mpr ⟨fit, lim, h_run⟩
  exact weth_inv_solvent wa sevm pre post exc h_code h_pc

/-! ### Atomic `State.Inv`-preservation lemmas

`processTransaction` mutates the world state through exactly five operations:
`incrNonce`, `subBal`, `processMessageCall`, `addBal`, and `destroyAccount`.
Each preserves `State.Inv wa` under the minimal side condition noted below.
The `code` field survives every op (all of them touch only `bal`/`nonce`/erase
a foreign account); `solvent` needs `a ≠ wa` wherever `wa`'s own balance could
drop; `nof` (`SumNof`) survives the *decreasing* ops for free but for `addBal`
is deferred to the caller via a hypothesis, to be discharged by the global
wei-conservation argument (a transaction moves but never mints ether, so the
total balance is non-increasing — hence no overflow bound is needed on the
theorem, unlike the withdrawal-carrying `applyBody`/`stateTransition`).

Bodies are `sorry` — this is the scaffold. -/

-- Bumping a nonce leaves `code`, `bal`, and `stor` untouched.
theorem State.Inv.incrNonce {wa a : Adr} {w : _root_.State}
    (h : State.Inv wa w) : State.Inv wa (w.incrNonce a) := by
  have hbal : (w.incrNonce a).bal = w.bal := by
    funext b
    show ((w.incrNonce a).get b).bal = (w.get b).bal
    by_cases hb : b = a
    · subst hb; simp only [State.incrNonce, State.get_set_self]
    · simp only [State.incrNonce, State.get_set_ne (Ne.symm hb)]
  have hstor : (w.incrNonce a).getStor wa = w.getStor wa := by
    show ((w.incrNonce a).get wa).stor = (w.get wa).stor
    by_cases hb : wa = a
    · subst hb; simp only [State.incrNonce, State.get_set_self]
    · simp only [State.incrNonce, State.get_set_ne (Ne.symm hb)]
  have hcode : (w.incrNonce a).getCode wa = w.getCode wa := by
    show ((w.incrNonce a).get wa).code = (w.get wa).code
    by_cases hb : wa = a
    · subst hb; simp only [State.incrNonce, State.get_set_self]
    · simp only [State.incrNonce, State.get_set_ne (Ne.symm hb)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hcode]; exact h.code
  · rw [hbal]; exact h.nof
  · show Stor.Solvent ((w.incrNonce a).getStor wa) 0 ((w.incrNonce a).bal wa)
    rw [hstor, hbal]; exact h.solvent

-- `addBal` can only raise a balance: `code` (bal field only) and `solvent`
-- (`bal wa` only grows) survive.  Both `nof` of the result *and* the absence of
-- a wrap at `wa` need the pre-sum bound `sum w.bal + val < 2 ^ 256`, supplied by
-- the caller's wei-conservation argument (a `SumNof` on the *result* would not
-- rule out a wrap, so it is not enough).
theorem State.Inv.addBal {wa a : Adr} {val : B256} {w : _root_.State}
    (hsum : sum w.bal + val.toNat < 2 ^ 256)
    (h : State.Inv wa w) : State.Inv wa (w.addBal a val) := by
  have hnof_a : B256.Nof (w.bal a) val := by
    unfold B256.Nof; have := @le_sum w.bal a; omega
  have hinc : Increase a val w.bal (w.addBal a val).bal := by
    intro b; constructor
    · intro heq; subst heq
      show w.bal a + val = ((w.addBal a val).get a).bal
      unfold State.addBal; rw [State.setBal_get_self]; rfl
    · intro hnb
      show w.bal b = ((w.addBal a val).get b).bal
      unfold State.addBal; rw [State.setBal_get_ne hnb]; rfl
  have hsum' := sum_add_assoc hinc hnof_a
  have hstor_wa : ((w.addBal a val).get wa).stor = (w.get wa).stor := by
    unfold State.addBal; rw [State.setBal_get_stor]
  have hbal_wa : (w.bal wa).toNat ≤ ((w.addBal a val).get wa).bal.toNat := by
    by_cases hwa : a = wa
    · subst hwa
      unfold State.addBal; rw [State.setBal_get_self]
      change (w.bal a).toNat ≤ (w.bal a + val).toNat
      rw [B256.toNat_add_eq_of_nof _ _ hnof_a]; omega
    · unfold State.addBal; rw [State.setBal_get_ne hwa]; exact Nat.le_refl _
  refine ⟨?_, ?_, ?_⟩
  · show some (((w.addBal a val).get wa).code).toList = Prog.compile weth
    unfold State.addBal; rw [State.setBal_get_code]; exact h.code
  · unfold _root_.SumNof; omega
  · show Stor.Solvent (((w.addBal a val).get wa).stor) 0 ((w.addBal a val).get wa).bal
    have hsolv := h.solvent
    unfold State.Solvent Stor.Solvent at hsolv
    unfold Stor.Solvent
    rw [hstor_wa]
    simp only [B256.toNat_zero, Nat.add_zero] at hsolv ⊢
    change wbsum ((w.get wa).stor) ≤ _
    have : wbsum (w.getStor wa) = wbsum ((w.get wa).stor) := rfl
    omega

-- `subBal` lowers a balance, so `nof` survives; dropping `wa`'s balance could
-- break solvency, hence `a ≠ wa`.  (In `processTransaction` the debited account
-- is the tx `sender`, which differs from the code-carrying `wa` by EIP-3607.)
theorem State.Inv.subBal {wa a : Adr} {val : B256} {w w' : _root_.State}
    (hne : a ≠ wa) (h_sub : w.subBal a val = some w')
    (h : State.Inv wa w) : State.Inv wa w' := by
  rcases State.of_subBal h_sub with ⟨h_le, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · -- code: `wa`'s account is untouched (`a ≠ wa`)
    show some (((w.setBal a (w.bal a - val)).get wa).code).toList = Prog.compile weth
    rw [State.setBal_get_code]; exact h.code
  · -- nof: the total sum can only decrease
    have hdec : Decrease a val w.bal (w.setBal a (w.bal a - val)).bal := by
      intro b; constructor
      · intro heq; subst heq
        show w.bal a - val = ((w.setBal a (w.bal a - val)).get a).bal
        rw [State.setBal_get_self]; rfl
      · intro hnb
        show w.bal b = ((w.setBal a (w.bal a - val)).get b).bal
        rw [State.setBal_get_ne hnb]; rfl
    have hsum := sum_sub_assoc hdec h_le
    have hnof := h.nof; unfold _root_.SumNof at hnof ⊢
    omega
  · -- solvent: `wa`'s storage and balance are both untouched
    show Stor.Solvent (((w.setBal a (w.bal a - val)).get wa).stor) 0
      ((w.setBal a (w.bal a - val)).get wa).bal
    rw [State.setBal_get_stor, State.setBal_get_ne hne]; exact h.solvent

lemma State.get_erase_ne {w : _root_.State} {a b : Adr} (h : b ≠ a) :
    State.get (w.erase a) b = State.get w b := by
  unfold State.get
  have hc : compare a b ≠ Ordering.eq := fun hcc => h (compare_eq_iff_eq.mp hcc).symm
  rw [Std.TreeMap.getD_erase]; simp [hc]

-- Deleting a foreign account (`a ≠ wa`) removes its balance from the sum and
-- leaves `wa`'s code/balance/storage alone.  (`_root_.destroyAccount` is used
-- explicitly in the body: its return type is `State`, so `.get`/`.bal` resolve
-- to `State.*` rather than the underlying `Std.TreeMap.*`, and the bare name
-- would clash with the theorem being defined.)
theorem State.Inv.destroyAccount {wa a : Adr} {w : _root_.State}
    (hne : a ≠ wa) (h : State.Inv wa w) : State.Inv wa (destroyAccount w a) := by
  have hget : (_root_.destroyAccount w a).get wa = w.get wa :=
    State.get_erase_ne (Ne.symm hne)
  refine ⟨?_, ?_, ?_⟩
  · show some (((_root_.destroyAccount w a).get wa).code).toList = Prog.compile weth
    rw [hget]; exact h.code
  · -- nof: erasing `a` removes its balance from the sum
    have h0 : ((_root_.destroyAccount w a).get a).bal = 0 := by
      show (State.get (w.erase a) a).bal = 0
      unfold State.get
      rw [Std.TreeMap.getD_erase]; simp [Acct.nil]
    have hdec : Decrease a (w.bal a) w.bal (_root_.destroyAccount w a).bal := by
      intro b; constructor
      · intro heq; subst heq
        show w.bal a - w.bal a = ((_root_.destroyAccount w a).get a).bal
        rw [h0, B256.sub_self]
      · intro hnb
        show w.bal b = (State.get (w.erase a) b).bal
        rw [State.get_erase_ne (Ne.symm hnb)]; rfl
    have hsum := sum_sub_assoc hdec (le_refl _)
    have hnof := h.nof; unfold _root_.SumNof at hnof ⊢
    omega
  · show Stor.Solvent (((_root_.destroyAccount w a).get wa).stor) 0
      ((_root_.destroyAccount w a).get wa).bal
    rw [hget]; exact h.solvent

-- Folded form for the `accountsToDelete` set (post-linearization `foldl`).
-- This one is proved outright from the atomic lemma to exercise the pattern.
theorem State.Inv.foldl_destroyAccount {wa : Adr} :
    ∀ {as : List Adr} {w : _root_.State},
      (∀ a ∈ as, a ≠ wa) → State.Inv wa w →
        State.Inv wa (as.foldl _root_.destroyAccount w)
  | [], _, _, h => h
  | a :: as, w, hne, h => by
    rw [List.foldl_cons]
    exact State.Inv.foldl_destroyAccount
      (fun b hb => hne b (List.mem_cons_of_mem _ hb))
      (h.destroyAccount (hne a List.mem_cons_self))

/-! ### Bridge to the frame-level invariant

The substantive gap: descend from the message-call layer to the already-proven
`exec_inv_solvent`.  This must connect `processMessageCall` — via
`prepareMessage`, the interpreter loop, and `processMessageCall.{call,create}` —
to the `Exec`/`weth_inv_solvent` machinery, discharge the WETH-code
precondition, and certify that a WETH run never self-destructs `wa`
(so the deletion set avoids `wa`). -/

-- Translation between the bare-state invariant and the frame-level
-- `Postcond`: `Devm.get{Bal,Stor,Code}` are by definition the corresponding
-- `State.*` projections of `devm.state`, so a `Postcond` plus code-preservation
-- is exactly `State.Inv` on the underlying state.
lemma State.Inv.of_postcond {wa : Adr} {sevm : Sevm} {devm : Devm}
    (h_post : Postcond wa sevm devm)
    (h_code : some (devm.state.getCode wa).toList = Prog.compile weth) :
    State.Inv wa devm.state := by
  refine ⟨h_code, ?_, ?_⟩
  · show sum devm.state.bal < 2 ^ 256
    rw [← sum_getBal_state]; exact h_post.nof
  · have hs := h_post.solvent
    unfold Devm.PostSolvent at hs
    exact hs

-- Building `Precond` for a sub-execution's initial state directly from the
-- bare-state invariant across a value transfer.  This is the `State.Inv`
-- counterpart of `Precond.child_of_transfer`: that lemma only ever consults the
-- parent's `code`/`nof`/`solvent.right` (the value-free solvency), which are
-- exactly the three fields of `State.Inv`.  As there, `caller ≠ wa` is required
-- so the credited value keeps `wa` over-collateralized when `target = wa`.
lemma Precond.of_inv_transfer {wa : Adr} {sevm' : Sevm} {devm' : Devm}
    {st st_mid : _root_.State} {caller target : Adr} {value : B256}
    (h_inv : State.Inv wa st)
    (h_ne : caller ≠ wa)
    (h_sub : st.subBal caller value = some st_mid)
    (h_state : devm'.state = st_mid.addBal target value)
    (h_ct' : sevm'.currentTarget = target)
    (h_val : sevm'.currentTarget = wa → sevm'.value = value) :
    Precond wa sevm' devm' := by
  have h_nof_st : sum st.bal < 2 ^ 256 := h_inv.nof
  rcases of_state_transfer (callee := target) h_sub h_nof_st with
    ⟨h_t_stor, h_t_code, h_t_sum, _, _, _⟩
  have h_stor' : devm'.getStor wa = st.getStor wa := by
    show (devm'.state.get wa).stor = (st.get wa).stor
    rw [h_state, h_t_stor wa]
  have h_code' : devm'.getCode wa = st.getCode wa := by
    show (devm'.state.get wa).code = (st.get wa).code
    rw [h_state, h_t_code wa]
  have h_bal_fun : ∀ a, devm'.getBal a = (st_mid.addBal target value).bal a := by
    intro a; show (devm'.state.get a).bal = _; rw [h_state]; rfl
  have h_solv := h_inv.solvent
  refine ⟨?_, ?_, ?_, ?_⟩
  · show some (devm'.getCode wa).toList = Prog.compile weth
    rw [h_code']; exact h_inv.code
  · have h_sum' : sum devm'.getBal = sum st.bal := by
      apply Eq.trans _ h_t_sum
      apply congrArg; funext a; exact h_bal_fun a
    rw [h_sum']; exact h_inv.nof
  · intro h_eq
    have h_v : sevm'.value = value := h_val h_eq
    have h_t_wa : target = wa := h_ct'.symm.trans h_eq
    subst h_t_wa
    have h_bal_wa : (devm'.getBal target).toNat
        = (st.bal target).toNat + value.toNat := by
      rw [h_bal_fun target, of_transfer_bal_target h_sub h_ne h_nof_st]
    rw [h_stor', h_v]
    unfold State.Solvent Stor.Solvent at h_solv
    unfold Stor.Solvent
    rw [B256.toNat_zero] at h_solv
    omega
  · intro h_ne_ct
    have h_t_ne : target ≠ wa := fun hc => h_ne_ct (h_ct'.trans hc)
    have h_bal_wa : devm'.getBal wa = st.bal wa := by
      rw [h_bal_fun wa, of_transfer_bal_other h_sub h_ne h_t_ne]
    rw [h_stor', h_bal_wa]
    show Stor.Solvent (st.getStor wa) 0 (st.bal wa)
    exact h_solv

-- Reusable core: a full `exec` run started after a value transfer preserves
-- `State.Inv`.  Combines `Precond.of_inv_transfer` (build the precondition),
-- `exec_inv_solvent` (frame-level solvency + nof), and `code_eq_of_exec` (the
-- WETH code at `wa` is untouched) through `State.Inv.of_postcond`.
lemma State.Inv.of_exec_transfer {wa : Adr} {sevm : Sevm} {pre post : Devm}
    {st st_mid : _root_.State} {caller target : Adr} {value : B256} {lim : Nat}
    (h_inv : State.Inv wa st)
    (h_ne : caller ≠ wa)
    (h_sub : st.subBal caller value = some st_mid)
    (h_pre_state : pre.state = st_mid.addBal target value)
    (h_ct : sevm.currentTarget = target)
    (h_val : sevm.currentTarget = wa → sevm.value = value)
    (h_code : sevm.currentTarget = wa → some sevm.code.toList = Prog.compile weth)
    (h_run : exec ⟨0, sevm, pre⟩ lim = .ok post) :
    State.Inv wa post.state := by
  have h_pc : Precond wa sevm pre :=
    Precond.of_inv_transfer h_inv h_ne h_sub h_pre_state h_ct h_val
  have h_post : Postcond wa sevm post :=
    exec_inv_solvent wa lim sevm pre post h_run h_code h_pc
  apply State.Inv.of_postcond h_post
  have fit : (Except.ok post : Execution).Fit := by
    simp [Except.Fit, Except.Lim, Except.toError?]
  obtain ⟨exc⟩ := (exec_iff_exec_eq 0 sevm pre (.ok post)).mpr ⟨fit, lim, h_run⟩
  have h_ce : post.getCode wa = pre.getCode wa := code_eq_of_exec exc h_pc.code
  show some (post.state.getCode wa).toList = Prog.compile weth
  rw [show post.state.getCode wa = post.getCode wa from rfl, h_ce]
  exact h_pc.code

-- No-transfer counterpart of `Precond.of_inv_transfer`: when no value moves,
-- the pre-state is the invariant state itself, and `PreSolvent` reduces to the
-- value-free solvency provided `value = 0` whenever the frame targets `wa`.
lemma Precond.of_inv_eqs {wa : Adr} {sevm : Sevm} {devm : Devm}
    (h_inv : State.Inv wa devm.state)
    (h_val0 : sevm.currentTarget = wa → sevm.value = 0) :
    Precond wa sevm devm := by
  refine ⟨h_inv.code, ?_, ?_, ?_⟩
  · show sum devm.getBal < 2 ^ 256
    rw [sum_getBal_state]; exact h_inv.nof
  · intro h_eq
    rw [h_val0 h_eq]; exact h_inv.solvent
  · intro _; exact h_inv.solvent

-- Shared tail: given the precondition already holds for `pre`, a successful
-- `exec` run preserves `State.Inv` (frame solvency + nof via `exec_inv_solvent`,
-- code via `code_eq_of_exec`).
lemma State.Inv.of_exec_precond {wa : Adr} {sevm : Sevm} {pre post : Devm} {lim : Nat}
    (h_pc : Precond wa sevm pre)
    (h_code : sevm.currentTarget = wa → some sevm.code.toList = Prog.compile weth)
    (h_run : exec ⟨0, sevm, pre⟩ lim = .ok post) :
    State.Inv wa post.state := by
  have h_post : Postcond wa sevm post :=
    exec_inv_solvent wa lim sevm pre post h_run h_code h_pc
  apply State.Inv.of_postcond h_post
  have fit : (Except.ok post : Execution).Fit := by
    simp [Except.Fit, Except.Lim, Except.toError?]
  obtain ⟨exc⟩ := (exec_iff_exec_eq 0 sevm pre (.ok post)).mpr ⟨fit, lim, h_run⟩
  have h_ce : post.getCode wa = pre.getCode wa := code_eq_of_exec exc h_pc.code
  show some (post.state.getCode wa).toList = Prog.compile weth
  rw [show post.state.getCode wa = post.getCode wa from rfl, h_ce]
  exact h_pc.code

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

-- The precondition for the sub-execution's initial `evm`, built directly from
-- the bare-state invariant across `benvAfterTransfer` (transfer / no-transfer).
lemma Precond.of_inv_benvAfterTransfer {wa : Adr} {msg : Msg} {benv : Benv}
    (h_ne : msg.shouldTransferValue = true → msg.caller ≠ wa)
    (h_val0 : msg.shouldTransferValue = false → msg.currentTarget = wa → msg.value = 0)
    (hb : msg.benvAfterTransfer = .ok benv)
    (h_inv : State.Inv wa msg.benv.state) :
    Precond wa (initSevm (msg.withBenv benv)) (initDevm (msg.withBenv benv)) := by
  by_cases h_stv : msg.shouldTransferValue = true
  · rcases of_benvAfterTransfer h_stv hb with ⟨st_mid, h_sub, hbenv⟩
    have hbs : (initDevm (msg.withBenv benv)).state
        = st_mid.addBal msg.currentTarget msg.value := by
      show benv.state = _; rw [hbenv]; rfl
    exact Precond.of_inv_transfer h_inv (h_ne h_stv) h_sub hbs rfl (fun _ => rfl)
  · have hbenv : benv = msg.benv := of_benvAfterTransfer_no h_stv hb
    have h_false : msg.shouldTransferValue = false := by
      cases hh : msg.shouldTransferValue
      · rfl
      · exact absurd hh h_stv
    have h_inv' : State.Inv wa (initDevm (msg.withBenv benv)).state := by
      show State.Inv wa benv.state; rw [hbenv]; exact h_inv
    exact Precond.of_inv_eqs h_inv' (fun he => h_val0 h_false he)

-- The post-transfer state itself still satisfies `State.Inv` (the transfer only
-- credits `wa` or moves value between accounts other than `wa`).  Used for the
-- precompile branch, where `executePrecomp` leaves the state untouched.
lemma State.Inv.of_benvAfterTransfer {wa : Adr} {msg : Msg} {benv : Benv}
    (h_ne : msg.shouldTransferValue = true → msg.caller ≠ wa)
    (hb : msg.benvAfterTransfer = .ok benv)
    (h_inv : State.Inv wa msg.benv.state) :
    State.Inv wa benv.state := by
  by_cases h_stv : msg.shouldTransferValue = true
  · rcases _root_.of_benvAfterTransfer h_stv hb with ⟨st_mid, h_sub, hbenv⟩
    have hbs : benv.state = st_mid.addBal msg.currentTarget msg.value := by
      rw [hbenv]; rfl
    rw [hbs]
    have h_inv_mid : State.Inv wa st_mid := State.Inv.subBal (h_ne h_stv) h_sub h_inv
    rcases State.of_subBal h_sub with ⟨h_le, h_mid⟩
    have hdec : Decrease msg.caller msg.value msg.benv.state.bal st_mid.bal := by
      rw [h_mid]; intro b; constructor
      · intro he; subst he
        show msg.benv.state.bal msg.caller - msg.value
          = ((msg.benv.state.setBal msg.caller
              (msg.benv.state.bal msg.caller - msg.value)).get msg.caller).bal
        rw [State.setBal_get_self]; rfl
      · intro hnb
        show msg.benv.state.bal b
          = ((msg.benv.state.setBal msg.caller
              (msg.benv.state.bal msg.caller - msg.value)).get b).bal
        rw [State.setBal_get_ne hnb]; rfl
    have hss := sum_sub_assoc hdec h_le
    have h_vle : msg.value.toNat ≤ sum msg.benv.state.bal :=
      le_trans (B256.toNat_le_toNat h_le) le_sum
    have hnof := h_inv.nof; unfold _root_.SumNof at hnof
    exact State.Inv.addBal (by omega) h_inv_mid
  · have hbenv : benv = msg.benv := _root_.of_benvAfterTransfer_no h_stv hb
    rw [hbenv]; exact h_inv

-- Deep helper: one `processMessage` run preserves `State.Inv` and never
-- self-destructs `wa`.  This is where the frame-level `exec_inv_solvent` gets
-- lifted: `processMessage` = `benvAfterTransfer` (value transfer) then
-- `executeCode` (→ `exec (initEvm ·) lim`) with on-error rollback.  The `nof`
-- and `getCode` parts are already available through the relational-mirror
-- stacks (`ProcessMessage.inv_nof`, `ProcessMessage.inv_getCode_gen`); the
-- solvency part is the genuinely new content, obtained from `exec_inv_solvent`
-- via `Postcond` and `State.Inv.of_postcond`.  Still open.
theorem processMessage_inv_solvent {wa : Adr} {msg : Msg} {evm : Devm} {lim : Nat}
    (h_run : processMessage msg lim = .ok evm)
    (h_code : msg.currentTarget = wa → some msg.code.toList = Prog.compile weth)
    (h_ne : msg.shouldTransferValue = true → msg.caller ≠ wa)
    (h_val0 : msg.shouldTransferValue = false → msg.currentTarget = wa → msg.value = 0)
    (h_inv : State.Inv wa msg.benv.state) :
    State.Inv wa evm.state := by
  cases lim with
  | zero => simp [processMessage] at h_run
  | succ k =>
    rw [processMessage] at h_run
    rcases of_bind_eq_ok h_run with ⟨benv, hb, h_run'⟩
    rcases of_bind_eq_ok h_run' with ⟨evm', hec, h_if⟩
    by_cases herr : evm'.error.isSome = true
    · -- sub-execution failed : state rolled back to the pre-transfer state
      rw [if_pos herr] at h_if
      rw [← Except.ok.inj h_if]; exact h_inv
    · -- clean success : `evm = evm'` comes straight from `executeCode`
      rw [if_neg herr] at h_if
      rw [← Except.ok.inj h_if]
      have h_pc : Precond wa (initSevm (msg.withBenv benv)) (initDevm (msg.withBenv benv)) :=
        Precond.of_inv_benvAfterTransfer h_ne h_val0 hb h_inv
      have h_code' : (initSevm (msg.withBenv benv)).currentTarget = wa →
          some (initSevm (msg.withBenv benv)).code.toList = Prog.compile weth := h_code
      cases k with
      | zero => simp [executeCode] at hec
      | succ j =>
        rw [executeCode] at hec
        rcases hca : (msg.withBenv benv).codeAddress with _ | adr
        · -- no code address : run the interpreter directly
          rw [hca] at hec
          exact State.Inv.of_exec_precond h_pc h_code' (exec_ok_of_handleError hec herr)
        · rw [hca] at hec
          dsimp only at hec
          by_cases hp : adr.isPrecomp
          · -- precompile : the state is left untouched
            rw [if_pos hp] at hec
            rw [state_of_executePrecomp_ok hec herr]
            exact State.Inv.of_benvAfterTransfer h_ne hb h_inv
          · -- ordinary code at a delegated address : run the interpreter
            rw [if_neg hp] at hec
            exact State.Inv.of_exec_precond h_pc h_code' (exec_ok_of_handleError hec herr)

-- Overwriting the storage of a *foreign* account (`a ≠ wa`) preserves `State.Inv`
-- (`wa`'s account is untouched, and `setStor` leaves every balance alone).
lemma State.Inv.setStor_ne {wa a : Adr} {s : Stor} {w : _root_.State}
    (hne : a ≠ wa) (h : State.Inv wa w) : State.Inv wa (w.setStor a s) := by
  have hget : (w.setStor a s).get wa = w.get wa := by
    unfold State.setStor; exact State.get_set_ne hne
  refine ⟨?_, ?_, ?_⟩
  · show some (((w.setStor a s).get wa).code).toList = Prog.compile weth
    rw [hget]; exact h.code
  · rw [State.setStor_bal]; exact h.nof
  · show Stor.Solvent (((w.setStor a s).get wa).stor) 0 ((w.setStor a s).get wa).bal
    rw [hget]; exact h.solvent

-- Likewise for installing code at a foreign account.
lemma State.Inv.setCode_ne {wa a : Adr} {cd : ByteArray} {w : _root_.State}
    (hne : a ≠ wa) (h : State.Inv wa w) : State.Inv wa (w.setCode a cd) := by
  have hget : (w.setCode a cd).get wa = w.get wa := by
    unfold State.setCode; exact State.get_set_ne hne
  refine ⟨?_, ?_, ?_⟩
  · show some (((w.setCode a cd).get wa).code).toList = Prog.compile weth
    rw [hget]; exact h.code
  · rw [State.setCode_bal]; exact h.nof
  · show Stor.Solvent (((w.setCode a cd).get wa).stor) 0 ((w.setCode a cd).get wa).bal
    rw [hget]; exact h.solvent

-- Create path.  `processCreateMessage` seeds the account being created
-- (`setStor .empty` + `incrNonce`, both at `currentTarget ≠ wa`), runs
-- `processMessage`, then on clean success charges code gas and installs the
-- returned code at `currentTarget`; the exceptional-halt and error paths roll
-- the state back to `msg.benv.state`.
-- `h_ct_ne` (the create address is fresh, hence `≠ wa`) subsumes both the
-- WETH-code condition and the `value = 0` condition: their premises are all
-- `currentTarget = wa`, so `h_ct_ne` discharges them vacuously.
theorem processCreateMessage_inv_solvent {wa : Adr} {msg : Msg} {evm : Devm} {lim : Nat}
    (h_run : processCreateMessage msg lim = .ok evm)
    (h_ct_ne : msg.currentTarget ≠ wa)
    (h_ne : msg.shouldTransferValue = true → msg.caller ≠ wa)
    (h_inv : State.Inv wa msg.benv.state) :
    State.Inv wa evm.state := by
  cases lim with
  | zero => simp [processCreateMessage] at h_run
  | succ k =>
    rw [processCreateMessage] at h_run
    rcases of_bind_eq_ok h_run with ⟨evm2, hpm, h_rest⟩
    -- the seeded sub-message still satisfies the invariant (`currentTarget ≠ wa`)
    have h_inv_cm : State.Inv wa (processCreateMessage.msg msg).benv.state := by
      show State.Inv wa ((msg.benv.state.setStor msg.currentTarget .empty).incrNonce
        msg.currentTarget)
      exact State.Inv.incrNonce (State.Inv.setStor_ne h_ct_ne h_inv)
    have h_pm : State.Inv wa evm2.state :=
      processMessage_inv_solvent hpm (fun h => absurd h h_ct_ne) h_ne
        (fun _ h => absurd h h_ct_ne) h_inv_cm
    by_cases herr : evm2.error.isNone = true
    · rw [if_pos herr] at h_rest
      rcases hcg : processCreateMessage.chargeCodeGas evm2 with ⟨err, evm3⟩ | evm3
      · -- code-gas charge failed
        rw [hcg] at h_rest; dsimp only at h_rest
        by_cases hex : isExceptionalHalt err
        · -- exceptional halt : state rolled back to `msg.benv.state`
          rw [if_pos hex] at h_rest
          rw [← Except.ok.inj h_rest]; exact h_inv
        · rw [if_neg hex] at h_rest; exact absurd h_rest (by simp)
      · -- clean success : install the returned code at `currentTarget ≠ wa`
        rw [hcg] at h_rest; dsimp only at h_rest
        rw [← Except.ok.inj h_rest, Devm.setCode_state, chargeCodeGas_state_ok hcg]
        exact State.Inv.setCode_ne h_ct_ne h_pm
    · -- sub-message failed : state rolled back to `msg.benv.state`
      rw [if_neg herr] at h_rest
      rw [← Except.ok.inj h_rest]; exact h_inv


lemma ExecuteCode.inv_noDel {wa : Adr} {msg : Msg} {xl : Xlot}
    {ex : Except (String × _root_.State × AdrSet × Tra) Devm}
    (inv : Xlot.InvNoDel wa xl) (invc : xl.InvGetCode)
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
    {ex : Except (String × _root_.State × AdrSet × Tra) Devm}
    (inv : Xlot.InvNoDel wa xl) (invc : xl.InvGetCode)
    (run : ProcessMessage msg xl ex)
    (h : Msg.NoDel wa msg) : MsgResult.NoDel wa ex := by
  dsimp only [ProcessMessage] at run
  rcases run with ⟨x, eq_bt_err, eq_ex_err, _⟩ | ⟨benv', eq_bt, run⟩
  · rw [eq_ex_err]
    exact Msg.NoDel.benvAfterTransfer_err eq_bt_err h
  · have h_nof' : Msg.NoDel wa (msg.withBenv benv') := Msg.NoDel.benvAfterTransfer eq_bt h
    rcases run with ⟨ex'', run_ec, h_split⟩
    rcases h_split with ⟨x, eq_ec_err, eq_ex_err⟩ | ⟨evm2, h_ex'', h_if⟩
    · rw [eq_ex_err]
      have h_exec : MsgResult.NoDel wa ex'' := ExecuteCode.inv_noDel inv invc run_ec h_nof'
      rw [eq_ec_err] at h_exec
      exact h_exec
    · by_cases h_err : evm2.error.isSome = true
      · rw [if_pos h_err] at h_if
        rw [← h_if]
        have h_exec : MsgResult.NoDel wa ex'' := ExecuteCode.inv_noDel inv invc run_ec h_nof'
        rw [h_ex''] at h_exec
        exact Devm.NoDel.rollback h_exec.atd h_exec.ca h.code
      · rw [if_neg h_err] at h_if
        rw [← h_if]
        have h_exec : MsgResult.NoDel wa ex'' := ExecuteCode.inv_noDel inv invc run_ec h_nof'
        rw [h_ex''] at h_exec
        exact h_exec

lemma ProcessCreateMessage.inv_noDel {wa : Adr} {msg : Msg} {xl : Xlot}
    {ex : Except (String × _root_.State × AdrSet × Tra) Devm}
    (inv : Xlot.InvNoDel wa xl) (invc : xl.InvGetCode)
    (run : ProcessCreateMessage msg xl ex)
    (h_ct : msg.currentTarget ≠ wa)
    (h : Msg.NoDel wa msg) : MsgResult.NoDel wa ex := by
  dsimp only [ProcessCreateMessage] at run
  rcases run with ⟨ex', run_pm, h_split⟩
  have h_seed : Msg.NoDel wa (processCreateMessage.msg msg) :=
    Msg.NoDel.processCreateMessage_msg h_ct h
  have h_pm : MsgResult.NoDel wa ex' :=
    ProcessMessage.inv_noDel inv invc run_pm h_seed
  rcases h_split with ⟨x, h_err_eq, h_ex_eq⟩ | ⟨evm, h_ex', h_if⟩
  · rw [h_err_eq] at h_pm
    rw [h_ex_eq]
    exact h_pm
  · rw [h_ex'] at h_pm
    have h_evm : Devm.NoDel wa evm := h_pm
    by_cases h_err : evm.error.isNone = true
    · rw [if_pos h_err] at h_if
      rcases h_cg : processCreateMessage.chargeCodeGas evm with ⟨err, evm'⟩ | evm' <;>
        rw [h_cg] at h_if <;> dsimp only at h_if
      · have h_ds : evm'.delSets = evm.delSets := chargeCodeGas_delSets_err h_cg
        have h_atd_eq : evm'.accountsToDelete = evm.accountsToDelete := congrArg Prod.fst h_ds
        have h_ca_eq : evm'.createdAccounts = evm.createdAccounts := congrArg Prod.snd h_ds
        have h_atd : wa ∉ evm'.accountsToDelete := by rw [h_atd_eq]; exact h_evm.atd
        have h_ca : wa ∉ evm'.createdAccounts := by rw [h_ca_eq]; exact h_evm.ca
        have h_gc : evm'.getCode wa = evm.getCode wa := by
          have hh := processCreateMessage.chargeCodeGas_getCode_gen h_cg wa
          simpa only [Execution.getCode] using hh
        split_ifs at h_if with h_halt
        · rw [← h_if]
          exact ⟨h_atd, h_ca, h.code⟩
        · rw [← h_if]
          refine ⟨h_ca, ?_⟩
          show (evm'.state.getCode wa).toList ≠ []
          rw [← Devm.getCode_state, h_gc]
          exact h_evm.code
      · rw [← h_if]
        have h_ds : evm'.delSets = evm.delSets := chargeCodeGas_delSets_ok h_cg
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
    · rw [if_neg h_err] at h_if
      rw [← h_if]
      exact Devm.NoDel.rollback h_pm.atd h_pm.ca h.code

lemma GenericCall.inv_noDel {wa : Adr} {sevm : Sevm} {devm : Devm}
    {gas : Nat} {value : B256} {caller target codeAddress : Adr}
    {stv istat : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    {xl : Xlot} {exn : Execution}
    (inv : Xlot.InvNoDel wa xl) (invc : xl.InvGetCode)
    (h : GenericCall sevm devm gas value caller target codeAddress
      stv istat ii is oi os code dp xl exn)
    (hnd : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  dsimp only [GenericCall] at h
  rcases h with ⟨evm1, eq_evm1, h⟩; subst eq_evm1
  split at h
  · rcases h with ⟨_, eq_ok⟩
    exact Devm.push_noDel eq_ok ⟨hnd.atd, hnd.ca, hnd.code⟩
  · rcases h with ⟨calldata, _, h⟩
    rcases h with ⟨childMsg, eq_childMsg, h⟩
    rcases h with ⟨ex', run_pm, h_split⟩
    have h_cm : Msg.NoDel wa childMsg := by
      rw [eq_childMsg]; exact ⟨hnd.ca, hnd.code⟩
    have h_pm : MsgResult.NoDel wa ex' :=
      ProcessMessage.inv_noDel inv invc run_pm h_cm
    rcases h_split with ⟨x, h_err, eq_err⟩ | ⟨child, h_ok, run⟩
    · rw [eq_err]
      rcases ex' with err | c
      · rcases err with ⟨e_str, e_st, e_ca, e_tra⟩
        dsimp only [liftToExecution] at h_err
        injection h_err with h_eq
        subst h_eq
        rcases h_pm with ⟨h_ca, h_code⟩
        exact ⟨hnd.atd, h_ca, h_code⟩
      · dsimp only [liftToExecution] at h_err
        contradiction
    · have h_child : Devm.NoDel wa child := by
        rcases ex' with err | c
        · dsimp only [liftToExecution] at h_ok
          contradiction
        · dsimp only [liftToExecution] at h_ok
          injection h_ok with h_eq
          subst h_eq
          exact h_pm
      split at run
      · rcases run with ⟨y, h_perr, eq_err⟩ | ⟨evm2, h_pok, eq_ok⟩
        · rw [eq_err]
          exact Devm.push_noDel h_perr (incorporateChildOnError_noDel hnd.atd h_child)
        · rw [← eq_ok]
          exact Devm.NoDel.of_eqs (Devm.push_delSets_eq h_pok).symm
            (Devm.push_getCode_gen h_pok wa).symm
            (incorporateChildOnError_noDel hnd.atd h_child)
      · rcases run with ⟨y, h_perr, eq_err⟩ | ⟨evm2, h_pok, eq_ok⟩
        · rw [eq_err]
          exact Devm.push_noDel h_perr (incorporateChildOnSuccess_noDel hnd.atd h_child)
        · rw [← eq_ok]
          exact Devm.NoDel.of_eqs (Devm.push_delSets_eq h_pok).symm
            (Devm.push_getCode_gen h_pok wa).symm
            (incorporateChildOnSuccess_noDel hnd.atd h_child)

lemma GenericCreate.inv_noDel {wa : Adr} {sevm : Sevm} {devm : Devm}
    {endowment : B256} {newAddress : Adr} {mi ms : Nat}
    {xl : Xlot} {exn : Execution}
    (inv : Xlot.InvNoDel wa xl) (invc : xl.InvGetCode)
    (h : GenericCreate sevm devm endowment newAddress mi ms xl exn)
    (hnd : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  dsimp only [GenericCreate] at h
  rcases h with ⟨calldata, eq_calldata, h⟩; subst eq_calldata
  rcases h with ⟨x, h_err, eq_err, _⟩ | ⟨_, _, h⟩
  · rw [eq_err]
    dsimp only [Except.assert] at h_err
    split at h_err
    · contradiction
    · injection h_err with h_eq; subst h_eq; exact hnd
  · rcases h with ⟨devm1, eq_devm1, h⟩
    rcases h with ⟨createMsgGas, _, h⟩
    rcases h with ⟨devm2, eq_devm2, h⟩
    have hnd2 : Devm.NoDel wa devm2 := by
      refine Devm.NoDel.of_eqs (d := devm) ?_ ?_ hnd
      · rw [eq_devm2, eq_devm1]; rfl
      · rw [eq_devm2, eq_devm1]; rfl
    rcases h with ⟨x, h_err, eq_err, _⟩ | ⟨_, _, h⟩
    · rw [eq_err]
      dsimp only [assertDynamic, Except.assert] at h_err
      split at h_err
      · contradiction
      · injection h_err with h_eq; subst h_eq; exact hnd2
    · rcases h with ⟨devm3, eq_devm3, h⟩
      rcases h with ⟨sender, _, h⟩
      have hnd3 : Devm.NoDel wa devm3 := by
        refine Devm.NoDel.of_eqs (d := devm2) ?_ ?_ hnd2
        · rw [eq_devm3]; rfl
        · rw [eq_devm3]; rfl
      split at h
      · rcases h with ⟨_, h_push⟩
        refine Devm.push_noDel h_push ?_
        exact Devm.NoDel.of_eqs (d := devm3) rfl rfl hnd3
      · rcases h with ⟨devm4, eq_devm4, h⟩
        have hnd4 : Devm.NoDel wa devm4 := by
          refine Devm.NoDel.of_eqs (d := devm3) ?_ ?_ hnd3
          · rw [eq_devm4]; rfl
          · rw [eq_devm4]; exact Devm.incrNonce_getCode.symm
        split at h
        · rcases h with ⟨_, h_push⟩
          exact Devm.push_noDel h_push hnd4
        · rename_i h_c2
          rcases h with ⟨childMsg, eq_childMsg, h⟩; subst eq_childMsg
          rcases h with ⟨ex', run_pcm, h_split⟩
          have h_ct : newAddress ≠ wa := by
            push_neg at h_c2
            exact ne_wa_of_code_size_zero hnd4.code h_c2.2.1
          have h_pm : MsgResult.NoDel wa ex' :=
            ProcessCreateMessage.inv_noDel inv invc run_pcm h_ct ⟨hnd4.ca, hnd4.code⟩
          rcases h_split with ⟨y, h_lift_err, eq_exn⟩ | ⟨child, h_lift_ok, run⟩
          · rw [eq_exn]
            rcases ex' with err | c
            · rcases err with ⟨e_str, e_st, e_ca, e_tra⟩
              dsimp only [liftToExecution] at h_lift_err
              injection h_lift_err with h_eq; subst h_eq
              rcases h_pm with ⟨h_ca, h_code⟩
              exact ⟨hnd4.atd, h_ca, h_code⟩
            · dsimp only [liftToExecution] at h_lift_err; contradiction
          · have h_child : Devm.NoDel wa child := by
              rcases ex' with err | c
              · dsimp only [liftToExecution] at h_lift_ok; contradiction
              · dsimp only [liftToExecution] at h_lift_ok
                injection h_lift_ok with h_eq; subst h_eq; exact h_pm
            split at run
            · exact Devm.push_noDel run (incorporateChildOnError_noDel hnd4.atd h_child)
            · exact Devm.push_noDel run (incorporateChildOnSuccess_noDel hnd4.atd h_child)

lemma Xinst.inv_noDel_gen {wa : Adr} {sevm : Sevm} {s : Devm} {x : Xinst}
    {xl : Xlot} {exn : Execution}
    (inv : Xlot.InvNoDel wa xl) (invc : xl.InvGetCode)
    (h : Xinst.Run sevm s x xl exn)
    (hnd : Devm.NoDel wa s) : Execution.NoDel wa exn := by
  cases x
  case create =>
    dsimp only [Xinst.Run] at h
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨endowment, d1⟩, e1, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd (Devm.pop_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨mi, d2⟩, e2, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of (hnd.pop e1) (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨ms, d3⟩, e3, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((hnd.pop e1).popToNat e2) (Devm.popToNat_err_snd h_e)
    rcases h with ⟨extendCost, _, h⟩
    rcases h with ⟨initCodeCost, _, h⟩
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨d4, e4, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of (((hnd.pop e1).popToNat e2).popToNat e3)
        (chargeGas_err_snd h_e)
    rcases h with ⟨d5, h_d5, h⟩
    rcases h with ⟨newAddress, _, h⟩
    have hnd4 : Devm.NoDel wa d4 := (((hnd.pop e1).popToNat e2).popToNat e3).chargeGas e4
    have hnd5 : Devm.NoDel wa d5 := by rw [h_d5]; exact hnd4.memExtends
    exact GenericCreate.inv_noDel inv invc h hnd5
  case create2 =>
    dsimp only [Xinst.Run] at h
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨endowment, d1⟩, e1, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd (Devm.pop_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨mi, d2⟩, e2, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of (hnd.pop e1) (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨ms, d3⟩, e3, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((hnd.pop e1).popToNat e2) (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨salt, d4⟩, e4, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of (((hnd.pop e1).popToNat e2).popToNat e3)
        (Devm.pop_err_snd h_e)
    rcases h with ⟨extendCost, _, h⟩
    rcases h with ⟨initCodeHashCost, _, h⟩
    rcases h with ⟨initCodeCost, _, h⟩
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨d5, e5, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((((hnd.pop e1).popToNat e2).popToNat e3).pop e4)
        (chargeGas_err_snd h_e)
    rcases h with ⟨d6, h_d6, h⟩
    rcases h with ⟨newAddress, _, h⟩
    have hnd5 : Devm.NoDel wa d5 :=
      ((((hnd.pop e1).popToNat e2).popToNat e3).pop e4).chargeGas e5
    have hnd6 : Devm.NoDel wa d6 := by rw [h_d6]; exact hnd5.memExtends
    exact GenericCreate.inv_noDel inv invc h hnd6
  case call =>
    dsimp only [Xinst.Run] at h
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨gas, d1⟩, e1, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd (Devm.pop_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨callee, d2⟩, e2, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of (hnd.pop e1) (Devm.popToAdr_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨value, d3⟩, e3, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((hnd.pop e1).popToAdr e2) (Devm.pop_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨ii, d4⟩, e4, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of (((hnd.pop e1).popToAdr e2).pop e3)
        (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨is, d5⟩, e5, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((((hnd.pop e1).popToAdr e2).pop e3).popToNat e4)
        (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨oi, d6⟩, e6, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of
        (((((hnd.pop e1).popToAdr e2).pop e3).popToNat e4).popToNat e5)
        (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨os, d7⟩, e7, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of
        ((((((hnd.pop e1).popToAdr e2).pop e3).popToNat e4).popToNat e5).popToNat e6)
        (Devm.popToNat_err_snd h_e)
    have hnd7 : Devm.NoDel wa d7 :=
      ((((((hnd.pop e1).popToAdr e2).pop e3).popToNat e4).popToNat e5).popToNat e6).popToNat e7
    rcases h with ⟨extendCost, _, h⟩
    rcases h with ⟨preAccessCost, _, h⟩
    rcases h with ⟨d8, h_d8, h⟩
    have hnd8 : Devm.NoDel wa d8 := by rw [h_d8]; exact hnd7.addAccessedAddress
    rcases h with ⟨⟨dp, na, code0, dagc, d9⟩, h_d9, h⟩
    have hnd9 : Devm.NoDel wa d9 := hnd8.of_accessDelegation h_d9
    rcases h with ⟨accessCost, _, h⟩
    rcases h with ⟨createCost, _, h⟩
    rcases h with ⟨transferCost, _, h⟩
    rcases h with ⟨⟨mcc, mcs⟩, _, h⟩
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨d10, e10, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd9 (chargeGas_err_snd h_e)
    have hnd10 : Devm.NoDel wa d10 := hnd9.chargeGas e10
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨_, _, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd10 (Except.assert_err_snd h_e)
    rcases h with ⟨d11, h_d11, h⟩
    have hnd11 : Devm.NoDel wa d11 := by rw [h_d11]; exact hnd10.memExtends
    rcases h with ⟨senderBal, _, h⟩
    split_ifs at h with h_lt
    · rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨d12, e12, h⟩
      · rw [h_ex]; exact Devm.push_noDel h_e hnd11
      · rcases h with ⟨_, h_ex⟩
        rw [← h_ex]
        exact Devm.NoDel.of_eqs (d := d12)
          (d' := (d12.withReturnData []).withGasLeft (d12.gasLeft + mcs))
          rfl rfl (Devm.push_noDel e12 hnd11)
    · exact GenericCall.inv_noDel inv invc h hnd11
  case callcode =>
    dsimp only [Xinst.Run] at h
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨gas, d1⟩, e1, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd (Devm.pop_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨codeAddress, d2⟩, e2, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of (hnd.pop e1) (Devm.popToAdr_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨value, d3⟩, e3, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((hnd.pop e1).popToAdr e2) (Devm.pop_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨ii, d4⟩, e4, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of (((hnd.pop e1).popToAdr e2).pop e3)
        (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨is, d5⟩, e5, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((((hnd.pop e1).popToAdr e2).pop e3).popToNat e4)
        (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨oi, d6⟩, e6, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of
        (((((hnd.pop e1).popToAdr e2).pop e3).popToNat e4).popToNat e5)
        (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨os, d7⟩, e7, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of
        ((((((hnd.pop e1).popToAdr e2).pop e3).popToNat e4).popToNat e5).popToNat e6)
        (Devm.popToNat_err_snd h_e)
    have hnd7 : Devm.NoDel wa d7 :=
      ((((((hnd.pop e1).popToAdr e2).pop e3).popToNat e4).popToNat e5).popToNat e6).popToNat e7
    rcases h with ⟨extendCost, _, h⟩
    rcases h with ⟨preAccessCost, _, h⟩
    rcases h with ⟨d8, h_d8, h⟩
    have hnd8 : Devm.NoDel wa d8 := by rw [h_d8]; exact hnd7.addAccessedAddress
    rcases h with ⟨⟨dp, newCodeAddress, code0, dagc, d9⟩, h_d9, h⟩
    have hnd9 : Devm.NoDel wa d9 := hnd8.of_accessDelegation h_d9
    rcases h with ⟨accessCost, _, h⟩
    rcases h with ⟨transferCost, _, h⟩
    rcases h with ⟨⟨mcc, mcs⟩, _, h⟩
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨d10, e10, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd9 (chargeGas_err_snd h_e)
    have hnd10 : Devm.NoDel wa d10 := hnd9.chargeGas e10
    rcases h with ⟨d11, h_d11, h⟩
    have hnd11 : Devm.NoDel wa d11 := by rw [h_d11]; exact hnd10.memExtends
    rcases h with ⟨senderBal, _, h⟩
    split_ifs at h with h_lt
    · rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨d12, e12, h⟩
      · rw [h_ex]; exact Devm.push_noDel h_e hnd11
      · rcases h with ⟨_, h_ex⟩
        rw [← h_ex]
        exact Devm.NoDel.of_eqs (d := d12)
          (d' := (d12.withReturnData []).withGasLeft (d12.gasLeft + mcs))
          rfl rfl (Devm.push_noDel e12 hnd11)
    · exact GenericCall.inv_noDel inv invc h hnd11
  case delcall =>
    dsimp only [Xinst.Run] at h
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨gas, d1⟩, e1, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd (Devm.pop_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨codeAddress, d2⟩, e2, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of (hnd.pop e1) (Devm.popToAdr_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨ii, d3⟩, e3, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((hnd.pop e1).popToAdr e2) (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨is, d4⟩, e4, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of (((hnd.pop e1).popToAdr e2).popToNat e3)
        (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨oi, d5⟩, e5, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((((hnd.pop e1).popToAdr e2).popToNat e3).popToNat e4)
        (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨os, d6⟩, e6, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of
        (((((hnd.pop e1).popToAdr e2).popToNat e3).popToNat e4).popToNat e5)
        (Devm.popToNat_err_snd h_e)
    have hnd6 : Devm.NoDel wa d6 :=
      (((((hnd.pop e1).popToAdr e2).popToNat e3).popToNat e4).popToNat e5).popToNat e6
    rcases h with ⟨extendCost, _, h⟩
    rcases h with ⟨preAccessCost, _, h⟩
    rcases h with ⟨d7, h_d7, h⟩
    have hnd7 : Devm.NoDel wa d7 := by rw [h_d7]; exact hnd6.addAccessedAddress
    rcases h with ⟨⟨dp, newCodeAddress, code0, dagc, d8⟩, h_d8, h⟩
    have hnd8 : Devm.NoDel wa d8 := hnd7.of_accessDelegation h_d8
    rcases h with ⟨accessCost, _, h⟩
    rcases h with ⟨⟨mcc, mcs⟩, _, h⟩
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨d9, e9, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd8 (chargeGas_err_snd h_e)
    have hnd9 : Devm.NoDel wa d9 := hnd8.chargeGas e9
    rcases h with ⟨d10, h_d10, h⟩
    have hnd10 : Devm.NoDel wa d10 := by rw [h_d10]; exact hnd9.memExtends
    exact GenericCall.inv_noDel inv invc h hnd10
  case statcall =>
    dsimp only [Xinst.Run] at h
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨gas, d1⟩, e1, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd (Devm.pop_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨target, d2⟩, e2, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of (hnd.pop e1) (Devm.popToAdr_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨ii, d3⟩, e3, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((hnd.pop e1).popToAdr e2) (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨is, d4⟩, e4, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of (((hnd.pop e1).popToAdr e2).popToNat e3)
        (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨oi, d5⟩, e5, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of ((((hnd.pop e1).popToAdr e2).popToNat e3).popToNat e4)
        (Devm.popToNat_err_snd h_e)
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨⟨os, d6⟩, e6, h⟩
    · rw [h_ex]
      exact Execution.NoDel.error_of
        (((((hnd.pop e1).popToAdr e2).popToNat e3).popToNat e4).popToNat e5)
        (Devm.popToNat_err_snd h_e)
    have hnd6 : Devm.NoDel wa d6 :=
      (((((hnd.pop e1).popToAdr e2).popToNat e3).popToNat e4).popToNat e5).popToNat e6
    rcases h with ⟨extendCost, _, h⟩
    rcases h with ⟨preAccessCost, _, h⟩
    rcases h with ⟨d7, h_d7, h⟩
    have hnd7 : Devm.NoDel wa d7 := by rw [h_d7]; exact hnd6.addAccessedAddress
    rcases h with ⟨⟨dp, newCodeAddress, code0, dagc, d8⟩, h_d8, h⟩
    have hnd8 : Devm.NoDel wa d8 := hnd7.of_accessDelegation h_d8
    rcases h with ⟨accessCost, _, h⟩
    rcases h with ⟨⟨mcc, mcs⟩, _, h⟩
    rcases h with ⟨xerr, h_e, h_ex, _⟩ | ⟨d9, e9, h⟩
    · rw [h_ex]; exact Execution.NoDel.error_of hnd8 (chargeGas_err_snd h_e)
    have hnd9 : Devm.NoDel wa d9 := hnd8.chargeGas e9
    rcases h with ⟨d10, h_d10, h⟩
    have hnd10 : Devm.NoDel wa d10 := by rw [h_d10]; exact hnd9.memExtends
    exact GenericCall.inv_noDel inv invc h hnd10

lemma Ninst.inv_noDel_gen {wa : Adr} {pc : Nat} {sevm : Sevm} {devm : Devm}
    {n : Ninst} {xl : Xlot} {exn : Execution}
    (inv : Xlot.InvNoDel wa xl) (invc : xl.InvGetCode)
    (run : Ninst.Run' pc sevm devm n xl exn)
    (h : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  cases n with
  | push xs le =>
    cases xl with
    | none =>
      dsimp only [Ninst.Run'] at run
      rw [← run]
      cases h_charge : chargeGas (if xs = [] then gBase else gVerylow) devm
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
    | some y => dsimp only [Ninst.Run'] at run
  | reg rg =>
    cases xl with
    | none =>
      dsimp only [Ninst.Run'] at run
      rw [← run]
      cases h_run : Rinst.run { pc := pc, sta := sevm, dyna := devm } rg
      case error err =>
        exact Devm.NoDel.of_eqs (Rinst.inv_delSets_err h_run).symm (Rinst.inv_getCode_err h_run wa).symm h
      case ok d1 =>
        exact Devm.NoDel.of_eqs (Rinst.inv_delSets h_run) (Rinst.inv_getCode h_run wa).symm h
    | some y => dsimp only [Ninst.Run'] at run
  | exec xinst =>
    dsimp only [Ninst.Run'] at run
    exact Xinst.inv_noDel_gen inv invc run h

lemma Exec.inv_noDel {wa : Adr} {pc : Nat} {sevm : Sevm} {devm : Devm}
    {exn : Execution}
    (run : Exec pc sevm devm exn)
    (h : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  revert exn devm sevm pc
  apply Exec.rec
  · intro pc sevm devm h_inst h_nof
    exact h_nof
  · intro pc sevm devm n err devm' h_at h_run h_nof
    exact Ninst.inv_noDel_gen (xl := .none) trivial trivial h_run h_nof
  · intro pc sevm devm n sevm_ devm_ exn_ err devm' h_at h_run ex_sub ih_sub h_nof
    exact Ninst.inv_noDel_gen (xl := some ⟨sevm_, devm_, exn_⟩) ih_sub ⟨ex_sub, fun a ha => (Exec.inv_getCode ex_sub a ha).symm⟩ h_run h_nof
  · intro pc sevm devm n devm' exn h_at h_run ex ih h_nof
    exact ih (Ninst.inv_noDel_gen (xl := .none) trivial trivial h_run h_nof)
  · intro pc sevm devm n sevm_ devm_ exn_ devm' exn h_at h_run ex_sub ex ih_sub ih h_nof
    exact ih (Ninst.inv_noDel_gen (xl := some ⟨sevm_, devm_, exn_⟩) ih_sub ⟨ex_sub, fun a ha => (Exec.inv_getCode ex_sub a ha).symm⟩ h_run h_nof)
  · intro pc sevm devm j err devm' h_at h_run h_nof
    exact Devm.NoDel.of_eqs (Jinst.inv_delSets_err h_run).symm (Jinst.inv_getCode_gen h_run wa).symm h_nof
  · intro pc sevm devm j pc' devm' exn h_at h_run ex ih h_nof
    exact ih (Devm.NoDel.of_eqs (Jinst.inv_delSets h_run).symm (Jinst.inv_getCode_gen h_run wa).symm h_nof)
  · intro pc sevm devm l exn h_at h_run h_nof
    exact Linst.inv_noDel h_run h_nof

theorem exec_inv_noDel {wa : Adr} (lim : Nat) (sevm : Sevm) (pre : Devm)
    (exn : Execution)
    (h_run : exec ⟨0, sevm, pre⟩ lim = exn) (h_fit : exn.Fit)
    (h : Devm.NoDel wa pre) : Execution.NoDel wa exn := by
  obtain ⟨exc⟩ := (exec_iff_exec_eq 0 sevm pre exn).mpr ⟨h_fit, lim, h_run⟩
  exact Exec.inv_noDel exc h

lemma Fit_of_handleError_ok {exn : Execution} {evm : Devm}
    (h : executeCode.handleError exn = .ok evm) : exn.Fit := by
  cases exn
  · dsimp [executeCode.handleError] at h
    split at h
    · next h_halt =>
      intro h_lim
      simp only [Except.Lim, Except.toError?, Option.some.injEq] at h_lim
      rw [h_lim] at h_halt
      revert h_halt
      decide
    · split at h
      · next h_rev =>
        intro h_lim
        simp only [Except.Lim, Except.toError?, Option.some.injEq] at h_lim
        rw [h_lim] at h_rev
        revert h_rev
        decide
      · contradiction
  · intro h_lim
    cases h_lim

theorem executeCode_inv_noDel {wa : Adr} {msg : Msg} {lim : Nat} {evm : Devm}
    (h_run : executeCode msg lim = .ok evm)
    (h : Msg.NoDel wa msg) : Devm.NoDel wa evm := by
  cases lim with
  | zero => simp [executeCode] at h_run
  | succ j =>
    rw [executeCode] at h_run
    rcases hca : msg.codeAddress with _ | adr
    · rw [hca] at h_run
      dsimp only at h_run
      have h_fit := Fit_of_handleError_ok h_run
      have h_ex := exec_inv_noDel j (initSevm msg) (initDevm msg) _ rfl h_fit (Msg.NoDel.initDevm h)
      have h_res := handleError_noDel h_ex
      dsimp only [initEvm] at h_run h_res
      rw [h_run] at h_res
      exact h_res
    · rw [hca] at h_run
      dsimp only at h_run
      by_cases hp : adr.isPrecomp
      · rw [if_pos hp] at h_run
        have h_ex := executePrecomp_noDel (evm := initEvm msg) (adr := adr) rfl (Msg.NoDel.initDevm h)
        have h_res := handleError_noDel h_ex
        dsimp only [initEvm] at h_run h_res
        rw [h_run] at h_res
        exact h_res
      · rw [if_neg hp] at h_run
        have h_fit := Fit_of_handleError_ok h_run
        have h_ex := exec_inv_noDel j (initSevm msg) (initDevm msg) _ rfl h_fit (Msg.NoDel.initDevm h)
        have h_res := handleError_noDel h_ex
        dsimp only [initEvm] at h_run h_res
        rw [h_run] at h_res
        exact h_res

theorem processMessage_inv_noDel {wa : Adr} {msg : Msg} {evm : Devm} {lim : Nat}
    (h_run : processMessage msg lim = .ok evm)
    (h : Msg.NoDel wa msg) : Devm.NoDel wa evm := by
  cases lim with
  | zero => simp [processMessage] at h_run
  | succ k =>
    rw [processMessage] at h_run
    rcases of_bind_eq_ok h_run with ⟨benv, hb, h_run'⟩
    rcases of_bind_eq_ok h_run' with ⟨evm', hec, h_if⟩
    by_cases herr : evm'.error.isSome = true
    · rw [if_pos herr] at h_if
      have h_evm : evm = evm'.rollback msg.benv.state msg.tenv.transientStorage := by
        rw [← Except.ok.inj h_if]
      rw [h_evm]
      have hbenv := Msg.NoDel.benvAfterTransfer hb h
      have hevm' := executeCode_inv_noDel hec hbenv
      exact Devm.NoDel.rollback hevm'.atd hevm'.ca h.code
    · rw [if_neg herr] at h_if
      have h_evm : evm = evm' := by
        rw [← Except.ok.inj h_if]
      rw [h_evm]
      have hbenv := Msg.NoDel.benvAfterTransfer hb h
      exact executeCode_inv_noDel hec hbenv

theorem processCreateMessage_inv_noDel {wa : Adr} {msg : Msg} {evm : Devm}
    {lim : Nat}
    (h_run : processCreateMessage msg lim = .ok evm)
    (h_ct : msg.currentTarget ≠ wa)
    (h : Msg.NoDel wa msg) : Devm.NoDel wa evm := by
  cases lim with
  | zero => simp [processCreateMessage] at h_run
  | succ k =>
    rw [processCreateMessage] at h_run
    rcases of_bind_eq_ok h_run with ⟨evm2, hpm, h_rest⟩
    have h_inv_cm : Msg.NoDel wa (processCreateMessage.msg msg) :=
      Msg.NoDel.processCreateMessage_msg h_ct h
    have h_pm : Devm.NoDel wa evm2 :=
      processMessage_inv_noDel hpm h_inv_cm
    by_cases herr : evm2.error.isNone = true
    · rw [if_pos herr] at h_rest
      rcases hcg : processCreateMessage.chargeCodeGas evm2 with ⟨err, evm3⟩ | evm3
      · rw [hcg] at h_rest; dsimp only at h_rest
        by_cases hex : isExceptionalHalt err
        · rw [if_pos hex] at h_rest
          rw [← Except.ok.inj h_rest]
          have h_ds : evm3.delSets = evm2.delSets := chargeCodeGas_delSets_err hcg
          have h_atd_eq : evm3.accountsToDelete = evm2.accountsToDelete := congrArg Prod.fst h_ds
          have h_ca_eq : evm3.createdAccounts = evm2.createdAccounts := congrArg Prod.snd h_ds
          have h_atd : wa ∉ evm3.accountsToDelete := by rw [h_atd_eq]; exact h_pm.atd
          have h_ca : wa ∉ evm3.createdAccounts := by rw [h_ca_eq]; exact h_pm.ca
          unfold processCreateMessage.exceptionalHalt
          exact Devm.NoDel.of_eqs (d := evm3.rollback msg.benv.state msg.tenv.transientStorage) rfl rfl (Devm.NoDel.rollback h_atd h_ca h.code)
        · rw [if_neg hex] at h_rest
          exact absurd h_rest (by simp)
      · rw [hcg] at h_rest; dsimp only at h_rest
        rw [← Except.ok.inj h_rest]
        have h_ds : evm3.delSets = evm2.delSets := chargeCodeGas_delSets_ok hcg
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
            refine ⟨rfl, fun a ha => ?_⟩
            have h_emp : (msg.benv.state.get authority).code.isEmpty = true := by
              simp_all
            have h_size : (msg.benv.state.get authority).code.size = 0 := by
              simp_all [ByteArray.isEmpty]
            have h_ne : authority ≠ a := ne_wa_of_code_size_zero ha h_size
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
    rcases bind_eq_ok_Except h with ⟨⟨msg1, refund1⟩, h_step, h_tail⟩
    have h_equiv1 := setDelegationStep_benv_equiv h_step
    have h_equiv2 := ih h_tail
    exact Benv.EquivForDelegation_trans h_equiv1 h_equiv2

lemma setDelegation_benv_equiv {msg msg' : Msg} {v : B256}
    (h_run : setDelegation msg = .ok ⟨msg', v⟩) :
    Benv.EquivForDelegation msg.benv msg'.benv := by
  unfold setDelegation at h_run
  dsimp [bind, Except.bind] at h_run
  apply bind_eq_ok_Except at h_run
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
    (h : Msg.NoDel wa msg) : Msg.NoDel wa msg' := by
  have heq := setDelegation_benv_equiv h_run
  rcases heq with ⟨h_ca, h_code⟩
  have h_code_wa := h_code wa
  have h2 := h_code_wa h.code
  constructor
  · rw [h_ca]; exact h.ca
  · rw [h2]; exact h.code

lemma setDelegationStep_inv_solvent {wa : Adr} {auth : Auth} {msg msg' : Msg}
    {refund refund' : B256}
    (h_run : setDelegationStep auth msg refund = .ok (msg', refund'))
    (h_inv : State.Inv wa msg.benv.state) :
    State.Inv wa msg'.benv.state := by
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
              exact Prog.compile_ne_nil (p := weth) (by rw [← h_inv.code, h_empty])
            have h_emp : (msg.benv.state.get authority).code.isEmpty = true := by
              simp_all
            have h_size : (msg.benv.state.get authority).code.size = 0 := by
              simp_all [ByteArray.isEmpty]
            have h_ne : authority ≠ wa := ne_wa_of_code_size_zero h_code_ne h_size
            change State.Inv wa ((msg.benv.state.setCode authority _).incrNonce authority)
            exact State.Inv.incrNonce (State.Inv.setCode_ne h_ne h_inv)

lemma setDelegationLoop_inv_solvent {wa : Adr} {auths : List Auth} {msg msg' : Msg}
    {refund refund' : B256}
    (h_run : setDelegationLoop auths msg refund = .ok (msg', refund'))
    (h_inv : State.Inv wa msg.benv.state) :
    State.Inv wa msg'.benv.state := by
  induction auths generalizing msg refund with
  | nil =>
    injection h_run with h1; injection h1 with h_msg h_refund
    subst h_msg
    exact h_inv
  | cons auth auths_tail ih =>
    unfold setDelegationLoop at h_run
    rcases bind_eq_ok_Except h_run with ⟨⟨msg1, refund1⟩, h_step, h_tail⟩
    exact ih h_tail (setDelegationStep_inv_solvent h_step h_inv)

lemma setDelegation_inv_solvent {wa : Adr} {msg msg' : Msg} {v : B256}
    (h_run : setDelegation msg = .ok ⟨msg', v⟩)
    (h_inv : State.Inv wa msg.benv.state) :
    State.Inv wa msg'.benv.state := by
  unfold setDelegation at h_run
  dsimp [bind, Except.bind] at h_run
  apply bind_eq_ok_Except at h_run
  rcases h_run with ⟨⟨msg_mid, refundCounter⟩, h_loop, h_rest⟩
  have h_eq_benv : msg_mid.benv = msg'.benv := by
    dsimp only at h_rest
    split at h_rest
    · contradiction
    · simpa using congrArg Msg.benv (congrArg Prod.fst (Except.ok.inj h_rest))
  rw [← h_eq_benv]
  exact setDelegationLoop_inv_solvent h_loop h_inv

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
    rcases bind_eq_ok_Except h_run with ⟨⟨msg1, refund1⟩, h_step, h_tail⟩
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
  apply bind_eq_ok_Except at h_run
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

structure Msg.InvSolvent (wa : Adr) (msg : Msg) : Prop where
  (state : State.Inv wa msg.benv.state)
  (nodel : Msg.NoDel wa msg)
  (code : msg.target.isNone = false → msg.currentTarget = wa →
    some msg.code.toList = Prog.compile weth)
  (codeAddress : msg.target.isNone = false → msg.currentTarget = wa →
    msg.codeAddress = some wa)
  (ne : msg.shouldTransferValue = true → msg.caller ≠ wa)
  (val0 : msg.shouldTransferValue = false → msg.currentTarget = wa → msg.value = 0)

structure Benv.InvSolvent (wa : Adr) (benv : Benv) : Prop where
  (state : State.Inv wa benv.state)
  (ca : wa ∉ benv.createdAccounts)

lemma Msg.InvSolvent.pc {wa : Adr} {msg : Msg} {codeSrc : Adr → ByteArray}
    (h : Msg.InvSolvent wa msg) :
    Msg.InvSolvent wa
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

lemma setDelegation_inv_msg_solvent {wa : Adr} {msg msg' : Msg} {v : B256}
    (h_run : setDelegation msg = .ok ⟨msg', v⟩)
    (h : Msg.InvSolvent wa msg) :
    Msg.InvSolvent wa msg' := by
  have h_run_orig := h_run
  refine ⟨setDelegation_inv_solvent h_run h.state,
    setDelegation_msg_noDel h_run h.nodel, ?_, ?_, ?_, ?_⟩
  · intro h_tgt h_ct
    unfold setDelegation at h_run
    dsimp [bind, Except.bind] at h_run
    apply bind_eq_ok_Except at h_run
    rcases h_run with ⟨⟨msg_mid, refundCounter⟩, h_loop, h_rest⟩
    rcases setDelegationLoop_fields h_loop with ⟨_, h_mid_tgt, h_mid_ct, _, _, h_mid_ca⟩
    have h_loop_equiv := setDelegationLoop_benv_equiv h_loop
    rcases h_loop_equiv with ⟨_, h_code⟩
    have h_code_ne : (msg.benv.state.getCode wa).toList ≠ [] := by
      intro h_empty
      exact Prog.compile_ne_nil (p := weth) (by rw [← h.state.code, h_empty])
    have h_code_wa := h_code wa h_code_ne
    dsimp only at h_rest
    split at h_rest
    · contradiction
    · rename_i ca h_ca
      have h_msg' : msg' =
          { msg_mid with code := msg_mid.benv.state.getCode ca } := by
        exact (congrArg Prod.fst (Except.ok.inj h_rest)).symm
      subst msg'
      change some (msg_mid.benv.state.getCode ca).toList = Prog.compile weth
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
    apply bind_eq_ok_Except at h_run_orig
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
    apply bind_eq_ok_Except at h_run_orig
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
    apply bind_eq_ok_Except at h_run_orig
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

theorem processMessageCall_inv_noDel {wa : Adr} {msg : Msg} {st' : _root_.State}
    {out : MsgCallOutput}
    (h_run : processMessageCall msg = .ok ⟨st', out⟩)
    (h : Msg.NoDel wa msg) : wa ∉ out.accountsToDelete := by
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
      rcases h_evm : processCreateMessage msg (msg.gas + 50) with ⟨err⟩ | ⟨evm⟩
      · simp only [Except.bimap, bind, Except.bind]
        intro h_run
        injection h_run
      · simp only [Except.bimap, bind, Except.bind]
        intro h_run
        have h_nodel := processCreateMessage_inv_noDel h_evm h_ct h
        split at h_run
        · split at h_run
          · injection h_run
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h_run
            rcases h_run with ⟨_, rfl⟩
            exact h_nodel.atd
        · simp only [id_eq, Except.ok.injEq, Prod.mk.injEq] at h_run
          rcases h_run with ⟨_, rfl⟩
          exact AdrSet.not_mem_empty
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
          have h_nodel_evm := processMessage_inv_noDel h_pm h_pc
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
        have h_del_nodel := setDelegation_msg_noDel h_del h
        unfold Except.bimap at h_run
        split at h_run
        · injection h_run
        · rename_i evm h_evm
          split at h_evm
          · injection h_evm
          · rename_i evm' h_pm
            simp only [id_eq, Except.ok.injEq] at h_evm
            subst h_evm
            have h_pc : Msg.NoDel wa (match getDelegatedCodeAddress msgDelegation.code with | none => msgDelegation | some dca => { benv := msgDelegation.benv, tenv := msgDelegation.tenv, caller := msgDelegation.caller, target := msgDelegation.target, currentTarget := msgDelegation.currentTarget, gas := msgDelegation.gas, value := msgDelegation.value, data := msgDelegation.data, codeAddress := some dca, code := msg.benv.state.getCode dca, depth := msgDelegation.depth, shouldTransferValue := msgDelegation.shouldTransferValue, isStatic := msgDelegation.isStatic, accessedAddresses := Std.HashSet.insert msgDelegation.accessedAddresses dca, accessedStorageKeys := msgDelegation.accessedStorageKeys, disablePrecompiles := true }) := by
              split
              · exact h_del_nodel
              · exact ⟨h_del_nodel.ca, h_del_nodel.code⟩
            have h_nodel_evm := processMessage_inv_noDel h_pm h_pc
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
    {st' : _root_.State} {out : MsgCallOutput}
    (h_run : processMessageCall msg = .ok ⟨st', out⟩)
    (h : Msg.NoDel wa msg) :
    ∀ a ∈ out.accountsToDelete.toList, a ≠ wa := by
  intro a ha heq
  subst heq
  exact processMessageCall_inv_noDel h_run h (Std.HashSet.mem_toList.mp ha)

theorem processMessageCall_inv_solvent {wa : Adr} {msg : Msg} {st' : _root_.State}
    {out : MsgCallOutput}
    (h_run : processMessageCall msg = .ok ⟨st', out⟩)
    (h_inv : Msg.InvSolvent wa msg) :
    State.Inv wa st' ∧ (∀ a ∈ out.accountsToDelete.toList, a ≠ wa) := by
  refine ⟨?_, processMessageCall_accountsToDelete_ne h_run h_inv.nodel⟩
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
      rcases h_evm : processCreateMessage msg (msg.gas + 50) with ⟨err⟩ | evm
      · simp only [Except.bimap, bind, Except.bind]
        intro h_run
        injection h_run
      · simp only [Except.bimap, bind, Except.bind]
        intro h_run
        have h_pm := processCreateMessage_inv_solvent h_evm h_ct h_inv.ne h_inv.state
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
          have h_pc : Msg.InvSolvent wa
              (match getDelegatedCodeAddress msg.code with
              | none => msg
              | some dca =>
                { msg with
                  disablePrecompiles := true,
                  accessedAddresses := msg.accessedAddresses.insert dca,
                  code := msg.benv.state.getCode dca,
                  codeAddress := some dca }) :=
            Msg.InvSolvent.pc (codeSrc := fun dca => msg.benv.state.getCode dca) h_inv
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
            processMessage_inv_solvent h_pm (fun hct => h_pc.code h_tgt_pc hct)
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
        have h_del_inv := setDelegation_inv_msg_solvent h_del h_inv
        unfold Except.bimap at h_run
        split at h_run
        · injection h_run
        · rename_i evm h_evm
          split at h_evm
          · injection h_evm
          · rename_i evm' h_pm
            simp only [id_eq, Except.ok.injEq] at h_evm
            subst h_evm
            have h_pc : Msg.InvSolvent wa
                (match getDelegatedCodeAddress msgDelegation.code with
                | none => msgDelegation
                | some dca =>
                  { msgDelegation with
                    disablePrecompiles := true,
                    accessedAddresses := msgDelegation.accessedAddresses.insert dca,
                    code := msg.benv.state.getCode dca,
                    codeAddress := some dca }) :=
              Msg.InvSolvent.pc (codeSrc := fun dca => msg.benv.state.getCode dca) h_del_inv
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
                    code := msg.benv.state.getCode dca,
                    codeAddress := some dca }).target.isNone = false := by
              split <;> simpa using h_msgDelegation_target_false
            have h_evm_inv :=
              processMessage_inv_solvent h_pm (fun hct => h_pc.code h_tgt_pc hct)
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

The proof of `processTransaction_inv_solvent` factors into three local facts.
They are intentionally stated at the executable-definition boundary:

* a checked transaction sender cannot be the WETH account, since successful
  `checkTransaction` accepted the sender as an EOA/delegation account;
* `prepareMessage` packages the post-upfront-fee state into a message satisfying
  `Msg.InvSolvent`;
* the final transaction gas credits are funded by the earlier upfront debit, so
  the two `addBal`s cannot overflow the global balance sum.

These are the intended follow-up proof obligations; with them available, the
main transaction invariant proof below is just definition inversion and
composition of already-proved message-level invariants. -/

lemma checkTransaction_sender_ne_of_inv_solvent {wa : Adr}
    {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {sender : Adr} {effectiveGasPrice : Nat}
    {blobVersionedHashes : List B256} {txBlobGasUsed : Nat}
    (h_check :
      checkTransaction benv bout tx =
        .ok ⟨sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed⟩)
    (h_inv : Benv.InvSolvent wa benv) :
    sender ≠ wa := by
  intro hsender
  subst sender
  unfold checkTransaction at h_check
  rcases of_bind_eq_ok h_check with ⟨_, _, h_check⟩
  rcases of_bind_eq_ok h_check with ⟨senderAddress, _, h_check⟩
  rcases of_bind_eq_ok h_check with ⟨_, _, h_check⟩
  rcases of_bind_eq_ok h_check with ⟨_, _, h_check⟩
  rcases of_bind_eq_ok h_check with ⟨_, _, h_check⟩
  rcases of_bind_eq_ok h_check with ⟨_, _, h_check⟩
  rcases of_bind_eq_ok h_check with ⟨_, hg, h_check⟩
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
        simpa [ByteArray.isEmpty] using h_empty
      exact Prog.compile_ne_nil (p := weth) (by rw [← h_inv.state.code, h_empty'])
    · exact not_delegation_of_compile h_inv.state.code h_del
  simp [checkTransactionSenderCode, h_no] at hg

lemma prepareMessage_benv {benv : Benv} {tenv : Tenv} {tx : Tx} {msg : Msg}
    (h_prep : prepareMessage benv tenv tx = .ok msg) :
    msg.benv = benv := by
  -- `prepareMessage` only constructs the message wrapper; it installs the
  -- supplied block environment unchanged into the resulting message.
  unfold prepareMessage at h_prep
  injection h_prep with h
  rw [← h]

lemma prepareMessage_inv_solvent {wa : Adr}
    {benv : Benv} {tenv : Tenv} {tx : Tx} {msg : Msg}
    (h_prep : prepareMessage benv tenv tx = .ok msg)
    (h_state : State.Inv wa benv.state)
    (h_ca : wa ∉ benv.createdAccounts)
    (h_origin_ne : tenv.stat.origin ≠ wa) :
    Msg.InvSolvent wa msg := by
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
      exact Prog.compile_ne_nil (p := weth) (by rw [← h_state.code, h_empty])
    · simp
    · simp
    · simpa using h_origin_ne
    · simp
  | some target =>
    simp [hrecv] at h_prep
    subst msg
    refine ⟨h_state, ⟨h_ca, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro h_empty
      exact Prog.compile_ne_nil (p := weth) (by rw [← h_state.code, h_empty])
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
        calculate_data_fee benv.stat.excessBlobGas tx
      else 0) < 2 ^ 256 := by
  unfold checkTransaction at h_check
  rcases of_bind_eq_ok h_check with ⟨txBlobGasUsed', h_limit, h_check⟩
  rcases of_bind_eq_ok h_check with ⟨senderAddress, h_recover, h_check⟩
  rcases of_bind_eq_ok h_check with ⟨fee, h_fee, h_check⟩
  rcases fee with ⟨effectiveGasPrice', maxGasFee⟩
  rcases of_bind_eq_ok h_check with ⟨blob, h_blob, h_check⟩
  rcases blob with ⟨maxGasFee', blobVersionedHashes'⟩
  rcases of_bind_eq_ok h_check with ⟨_, h_receiver, h_check⟩
  rcases of_bind_eq_ok h_check with ⟨_, h_auth, h_check⟩
  rcases of_bind_eq_ok h_check with ⟨_, h_account, h_check⟩
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
    split at h_fee
    · cases h_fee
    · have h_fee' := Except.ok.inj h_fee
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
    split at h_fee
    · cases h_fee
    · have h_fee' := Except.ok.inj h_fee
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
    split at h_fee
    · cases h_fee
    · split at h_fee
      · cases h_fee
      · rename_i h_priority h_base_fee
        have h_fee' := Except.ok.inj h_fee
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
    split at h_fee
    · cases h_fee
    · split at h_fee
      · cases h_fee
      · rename_i h_priority h_base_fee
        have h_fee' := Except.ok.inj h_fee
        simp only [Prod.mk.injEq] at h_fee'
        obtain ⟨rfl, rfl⟩ := h_fee'
        simp only [checkTransactionBlobData, h_type] at h_blob
        split at h_blob
        · cases h_blob
        · split at h_blob
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
                  calculate_data_fee benv.stat.excessBlobGas tx ≤
                    calculateTotalBlobGas tx * maxFeePerBlobGas := by
                unfold calculate_data_fee
                exact Nat.mul_le_mul_left _ (by omega)
              omega
  | four chainId maxPriorityFeePerGas maxFeePerGas receiver accessList auths =>
    simp only [checkTransactionGasFee, h_type, checkTransactionDynamicGasFee] at h_fee
    split at h_fee
    · cases h_fee
    · split at h_fee
      · cases h_fee
      · rename_i h_priority h_base_fee
        have h_fee' := Except.ok.inj h_fee
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

lemma validateTransaction_calldataFloorGasCost_le_gas {tx : Tx}
    {intrinsicGas calldataFloorGasCost : Nat}
    (h_validate :
      validateTransaction tx = .ok ⟨intrinsicGas, calldataFloorGasCost⟩) :
    calldataFloorGasCost ≤ tx.gas := by
  unfold validateTransaction at h_validate
  rcases h_cost : calculateIntrinsicCost tx with ⟨ig, floorCost⟩
  rw [h_cost] at h_validate
  dsimp only at h_validate
  split at h_validate
  · cases h_validate
  · split at h_validate
    · cases h_validate
    · split at h_validate
      · cases h_validate
      · rename_i h_gas _ _
        have h_result := Except.ok.inj h_validate
        simp only [Prod.mk.injEq] at h_result
        obtain ⟨rfl, rfl⟩ := h_result
        omega

lemma State.Inv.add_transaction_gas_credits {wa : Adr}
    {baseState debitState postMsgState : _root_.State}
    {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {sender : Adr} {effectiveGasPrice : Nat}
    {blobVersionedHashes : List B256} {txBlobGasUsed : Nat}
    {intrinsicGas calldataFloorGasCost refundCounter : Nat}
    {txOutput : MsgCallOutput}
    (h_validate :
      validateTransaction tx = .ok ⟨intrinsicGas, calldataFloorGasCost⟩)
    (h_check :
      checkTransaction benv bout tx =
        .ok ⟨sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed⟩)
    (h_debit :
      (baseState.incrNonce sender).subBal sender
        (tx.gas * effectiveGasPrice +
          if tx.isTypeThree = true then
            calculate_data_fee benv.stat.excessBlobGas tx
          else
            0).toB256 =
        some debitState)
    (h_msg_sum : sum postMsgState.bal ≤ sum debitState.bal)
    (h_base : State.Inv wa baseState)
    (h_post : State.Inv wa postMsgState) :
    State.Inv wa
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
  have h_debit_exact := toNat_toB256_of_lt h_fee_lt
  rw [h_debit_exact] at h_debit_sum
  have h_base_sum := h_base.nof
  unfold _root_.SumNof at h_base_sum
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
    rw [toNat_toB256]
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
    rw [toNat_toB256]
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
    State.Inv.addBal (a := sender) h_sender_sum h_post
  have h_growth := State.addBal_growth postMsgState sender
    ((tx.gas -
        max (tx.gas - txOutput.gasLeft -
          min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
          calldataFloorGasCost) *
      effectiveGasPrice).toB256
  dsimp only [State.BalGrowth, State.balSum] at h_growth
  apply State.Inv.addBal
  · omega
  · exact h_sender_inv

theorem processTransaction_inv_solvent (wa : Adr)
    (benv : Benv) (bout bout' : BlockOutput) (tx : Tx) (i : Nat) (st : _root_.State)
    (h_run : processTransaction benv bout tx i = .ok ⟨st, bout'⟩)
    (h_inv : Benv.InvSolvent wa benv) : Benv.InvSolvent wa (benv.withState st) := by
  unfold processTransaction at h_run
  rcases of_bind_eq_ok h_run with ⟨bout0, hbout0, h_run⟩
  rcases of_bind_eq_ok h_run with ⟨gasInfo, hval, h_run⟩
  rcases gasInfo with ⟨intrinsicGas, calldataFloorGasCost⟩
  rcases of_bind_eq_ok h_run with ⟨chk, hcheck, h_run⟩
  rcases chk with ⟨sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed⟩
  rcases of_bind_eq_ok h_run with ⟨state1, hsub, h_run⟩
  rcases of_bind_eq_ok h_run with ⟨msg, hprep, h_run⟩
  rcases of_bind_eq_ok h_run with ⟨pmout, hpm, h_run⟩
  rcases pmout with ⟨state2, txOutput⟩
  rcases of_bind_eq_ok h_run with ⟨refundCounter, hrefund, h_run⟩
  simp only [Prod.mk.injEq] at h_run
  rcases h_run with ⟨rfl, rfl⟩
  have hsender : sender ≠ wa :=
    checkTransaction_sender_ne_of_inv_solvent hcheck h_inv
  have hsub_some :
      (benv.state.incrNonce sender).subBal sender
        (tx.gas * effectiveGasPrice +
          if tx.isTypeThree = true then
            calculate_data_fee benv.stat.excessBlobGas tx
          else
            0).toB256 = some state1 := by
    generalize hopt : (benv.state.incrNonce sender).subBal sender
        (tx.gas * effectiveGasPrice +
          if tx.isTypeThree = true then
            calculate_data_fee benv.stat.excessBlobGas tx
          else
            0).toB256 = o at hsub ⊢
    cases o with
    | none => simp [Option.toExcept] at hsub
    | some s => simpa [Option.toExcept] using hsub
  have hstate1 : State.Inv wa state1 :=
    State.Inv.subBal hsender hsub_some (State.Inv.incrNonce h_inv.state)
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
  have hmsg : Msg.InvSolvent wa msg :=
    prepareMessage_inv_solvent hprep hstate1 (by simpa using h_inv.ca) horigin
  have hpm_inv := processMessageCall_inv_solvent hpm hmsg
  have hmsg_benv := prepareMessage_benv hprep
  have hsum_le : sum state2.bal ≤ sum state1.bal := by
    have h := processMessageCall_sum_le hpm
    rw [hmsg_benv] at h
    exact h
  have hcredits : State.Inv wa
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
    State.Inv.add_transaction_gas_credits hval hcheck hsub_some hsum_le
      h_inv.state hpm_inv.1
  refine ⟨?_, ?_⟩
  · exact State.Inv.foldl_destroyAccount hpm_inv.2 hcredits
  · simpa [Benv.withState] using h_inv.ca

theorem applyTransactions_inv_solvent (wa : Adr)
    (txis : List (Nat × Tx)) (benv benv' : Benv) (bout bout' : BlockOutput)
    (h_run : applyTransactions txis benv bout = .ok ⟨benv', bout'⟩)
    (h_inv : Benv.InvSolvent wa benv) : Benv.InvSolvent wa benv' := by
  -- list induction over `txis`; each step is `processTransaction_inv_solvent`
  -- (note `processTransaction` threads `Benv`, so track `benv.state`).
  induction txis generalizing benv bout with
  | nil =>
    rw [applyTransactions] at h_run
    obtain ⟨hb, hbo⟩ := Prod.mk.inj (Except.ok.inj h_run)
    subst hb; exact h_inv
  | cons hd tl ih =>
    obtain ⟨i, tx⟩ := hd
    rw [applyTransactions] at h_run
    obtain ⟨⟨st, bout''⟩, h1, h2⟩ := of_bind_eq_ok h_run
    have hstep := processTransaction_inv_solvent wa benv bout bout'' tx i st h1 h_inv
    exact ih (benv.withState st) bout'' h2 hstep

/-
(1) Difficulty: ★★☆☆☆
(2) Proof plan: unfold the two system-transaction wrappers, build
`Msg.InvSolvent` for the resulting zero-value/no-transfer message from the
`Benv.InvSolvent` hypothesis, and apply `processMessageCall_inv_solvent` and
`processMessageCall_sum_le`.  The wrapper only chooses the target's current
code and otherwise does not alter the starting state.
-/
lemma processUncheckedSystemTransaction_inv_solvent_sum_le (wa : Adr)
    (benv : Benv) (target : Adr) (data : B8L)
    (st : _root_.State) (out : MsgCallOutput)
    (h_run : processUncheckedSystemTransaction benv target data = .ok ⟨st, out⟩)
    (h_inv : Benv.InvSolvent wa benv) :
    State.Inv wa st ∧ sum st.bal ≤ sum benv.state.bal := by
  dsimp [processUncheckedSystemTransaction, processSystemTransaction] at h_run
  have h_msg : Msg.InvSolvent wa
      (processSystemTransactionMsg benv (processSystemTransactionTenv benv)
        target data (benv.state.getCode target)) := by
    refine ⟨h_inv.state, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨h_inv.ca, ?_⟩
      intro hnil
      exact Prog.compile_ne_nil (p := weth) (by
        rw [← h_inv.state.code]
        simpa [processSystemTransactionMsg] using hnil)
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
  exact ⟨(processMessageCall_inv_solvent h_run h_msg).1, hsum⟩

-- Total wei credited by a list of withdrawals, computed in ℕ. Withdrawals
-- mint ether with wrapping addition (`State.addBal`), so the block-level
-- theorems need the bound `sum _.bal + wdsum wds < 2 ^ 256` : without it,
-- a withdrawal crediting `wa` could wrap `wa`'s balance to near zero and
-- destroy both solvency and `SumNof`.
def wdsum (wds : List Withdrawal) : Nat :=
  (wds.map (fun wd => wd.amount.toNat * 10 ^ 9)).sum

-- Helper: `toB256` truncates, so its `toNat` is at most the original Nat.
lemma toB256_toNat_le (n : Nat) : n.toB256.toNat ≤ n := by
  rw [toNat_toB256]
  unfold Nat.lo
  exact Nat.mod_le _ _

-- Erasing an account removes its balance from the total: nonincreasing.
lemma destroyAccount_sum_le (w : _root_.State) (a : Adr) :
    sum (_root_.destroyAccount w a).bal ≤ sum w.bal := by
  have h0 : ((_root_.destroyAccount w a).get a).bal = 0 := by
    show (State.get (w.erase a) a).bal = 0
    unfold State.get
    rw [Std.TreeMap.getD_erase]; simp [Acct.nil]
  have hdec : Decrease a (w.bal a) w.bal (_root_.destroyAccount w a).bal := by
    intro b; constructor
    · intro heq; subst heq
      show w.bal a - w.bal a = ((_root_.destroyAccount w a).get a).bal
      rw [h0, B256.sub_self]
    · intro hnb
      show w.bal b = (State.get (w.erase a) b).bal
      rw [State.get_erase_ne (Ne.symm hnb)]; rfl
  have hsum := sum_sub_assoc hdec (le_refl _)
  omega

lemma foldl_destroyAccount_sum_le :
    ∀ (as : List Adr) (w : _root_.State),
      sum ((as.foldl _root_.destroyAccount w).bal) ≤ sum w.bal
  | [], _ => le_refl _
  | a :: as, w => by
    rw [List.foldl_cons]
    exact le_trans (foldl_destroyAccount_sum_le as _) (destroyAccount_sum_le w a)

-- Affordability: a successfully checked transaction's up-front debit
-- (gas fee plus blob fee) fits in 256 bits, because `checkTransaction`
-- verifies the sender's (256-bit) balance covers the *max* gas fee.
lemma checkTransaction_fee_lt {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {sender : Adr} {egp : Nat} {bvh : List B256} {tbgu : Nat}
    (h : checkTransaction benv bout tx = .ok ⟨sender, egp, bvh, tbgu⟩) :
    tx.gas * egp +
      (if tx.isTypeThree = true then
        calculate_data_fee benv.stat.excessBlobGas tx
      else 0) < 2 ^ 256 := by
  unfold checkTransaction at h
  rcases of_bind_eq_ok h with ⟨tbgu', hlim, h⟩
  rcases of_bind_eq_ok h with ⟨senderAddress, hrecover, h⟩
  rcases of_bind_eq_ok h with ⟨fee, hfee, h⟩
  rcases fee with ⟨egp', maxGasFee⟩
  rcases of_bind_eq_ok h with ⟨blob, hblob, h⟩
  rcases blob with ⟨maxGasFee2, bvh'⟩
  rcases of_bind_eq_ok h with ⟨u1, hrecv, h⟩
  rcases of_bind_eq_ok h with ⟨u2, hauth, h⟩
  rcases of_bind_eq_ok h with ⟨u3, hacct, h⟩
  have h' := Except.ok.inj h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
  -- the sender's balance covers `maxGasFee2`
  have hbal : maxGasFee2 ≤ ((benv.state.get senderAddress).bal).toNat := by
    unfold checkTransactionSenderAccount at hacct
    split at hacct <;> try contradiction
    split at hacct <;> try contradiction
    split at hacct <;> try contradiction
    rename_i hlt
    omega
  have hbal_lt : ((benv.state.get senderAddress).bal).toNat < 2 ^ 256 :=
    B256.toNat_lt _
  -- gas fee bound: `tx.gas * egp' ≤ maxGasFee`
  cases htt : tx.type with
  | zero gasPrice recv =>
    simp only [checkTransactionGasFee, htt, checkTransactionLegacyGasFee] at hfee
    split at hfee
    · cases hfee
    · have hfe := Except.ok.inj hfee
      simp only [Prod.mk.injEq] at hfe
      obtain ⟨rfl, rfl⟩ := hfe
      simp only [checkTransactionBlobData, htt] at hblob
      have hbe := Except.ok.inj hblob
      simp only [Prod.mk.injEq] at hbe
      obtain ⟨rfl, rfl⟩ := hbe
      simp only [Tx.isTypeThree, htt, Bool.false_eq_true, if_false]
      omega
  | one cid gasPrice recv al =>
    simp only [checkTransactionGasFee, htt, checkTransactionLegacyGasFee] at hfee
    split at hfee
    · cases hfee
    · have hfe := Except.ok.inj hfee
      simp only [Prod.mk.injEq] at hfe
      obtain ⟨rfl, rfl⟩ := hfe
      simp only [checkTransactionBlobData, htt] at hblob
      have hbe := Except.ok.inj hblob
      simp only [Prod.mk.injEq] at hbe
      obtain ⟨rfl, rfl⟩ := hbe
      simp only [Tx.isTypeThree, htt, Bool.false_eq_true, if_false]
      omega
  | two cid mpf maxFee recv al =>
    simp only [checkTransactionGasFee, htt, checkTransactionDynamicGasFee] at hfee
    split at hfee
    · cases hfee
    · split at hfee
      · cases hfee
      · rename_i hmp hbf
        have hfe := Except.ok.inj hfee
        simp only [Prod.mk.injEq] at hfe
        obtain ⟨rfl, rfl⟩ := hfe
        simp only [checkTransactionBlobData, htt] at hblob
        have hbe := Except.ok.inj hblob
        simp only [Prod.mk.injEq] at hbe
        obtain ⟨rfl, rfl⟩ := hbe
        simp only [Tx.isTypeThree, htt, Bool.false_eq_true, if_false]
        have hegp : min mpf (maxFee - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas ≤ maxFee := by omega
        have hmul : tx.gas * (min mpf (maxFee - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas) ≤ tx.gas * maxFee :=
          Nat.mul_le_mul_left _ hegp
        omega
  | three cid mpf maxFee recv al mbf bh =>
    simp only [checkTransactionGasFee, htt, checkTransactionDynamicGasFee] at hfee
    split at hfee
    · cases hfee
    · split at hfee
      · cases hfee
      · rename_i hmp hbf
        have hfe := Except.ok.inj hfee
        simp only [Prod.mk.injEq] at hfe
        obtain ⟨rfl, rfl⟩ := hfe
        simp only [checkTransactionBlobData, htt] at hblob
        split at hblob
        · cases hblob
        · split at hblob
          · cases hblob
          · split at hblob
            · cases hblob
            · rename_i hbfee
              have hbe := Except.ok.inj hblob
              simp only [Prod.mk.injEq] at hbe
              obtain ⟨rfl, rfl⟩ := hbe
              simp only [Tx.isTypeThree, htt, reduceIte]
              have hegp : min mpf (maxFee - benv.stat.baseFeePerGas) +
                  benv.stat.baseFeePerGas ≤ maxFee := by omega
              have hmul : tx.gas * (min mpf (maxFee - benv.stat.baseFeePerGas) +
                  benv.stat.baseFeePerGas) ≤ tx.gas * maxFee :=
                Nat.mul_le_mul_left _ hegp
              have hblobmul : calculate_data_fee benv.stat.excessBlobGas tx ≤
                  calculateTotalBlobGas tx * mbf := by
                unfold calculate_data_fee
                exact Nat.mul_le_mul_left _ (by omega)
              omega
  | four cid mpf maxFee recv al auths =>
    simp only [checkTransactionGasFee, htt, checkTransactionDynamicGasFee] at hfee
    split at hfee
    · cases hfee
    · split at hfee
      · cases hfee
      · rename_i hmp hbf
        have hfe := Except.ok.inj hfee
        simp only [Prod.mk.injEq] at hfe
        obtain ⟨rfl, rfl⟩ := hfe
        simp only [checkTransactionBlobData, htt] at hblob
        have hbe := Except.ok.inj hblob
        simp only [Prod.mk.injEq] at hbe
        obtain ⟨rfl, rfl⟩ := hbe
        simp only [Tx.isTypeThree, htt, Bool.false_eq_true, if_false]
        have hegp : min mpf (maxFee - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas ≤ maxFee := by omega
        have hmul : tx.gas * (min mpf (maxFee - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas) ≤ tx.gas * maxFee :=
          Nat.mul_le_mul_left _ hegp
        omega

-- Validation bound: the calldata floor gas cost never exceeds the gas limit.
lemma validateTransaction_floor_le {tx : Tx}
    {intrinsicGas calldataFloorGasCost : Nat}
    (h : validateTransaction tx = .ok ⟨intrinsicGas, calldataFloorGasCost⟩) :
    calldataFloorGasCost ≤ tx.gas := by
  unfold validateTransaction at h
  rcases hic : calculateIntrinsicCost tx with ⟨ig, cdf⟩
  rw [hic] at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i hgas _ _
        have h' := Except.ok.inj h
        simp only [Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        omega

-- One-step wei conservation for `processTransaction`.
lemma processTransaction_sum_le {benv : Benv} {bout bout' : BlockOutput}
    {tx : Tx} {i : Nat} {st : _root_.State}
    (h_run : processTransaction benv bout tx i = .ok ⟨st, bout'⟩) :
    sum st.bal ≤ sum benv.state.bal := by
  unfold processTransaction at h_run
  rcases of_bind_eq_ok h_run with ⟨bout0, hbout0, h_run⟩
  rcases of_bind_eq_ok h_run with ⟨gasInfo, hval, h_run⟩
  rcases gasInfo with ⟨intrinsicGas, calldataFloorGasCost⟩
  rcases of_bind_eq_ok h_run with ⟨chk, hcheck, h_run⟩
  rcases chk with ⟨sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed⟩
  rcases of_bind_eq_ok h_run with ⟨state1, hsub, h_run⟩
  rcases of_bind_eq_ok h_run with ⟨msg, hprep, h_run⟩
  rcases of_bind_eq_ok h_run with ⟨pmout, hpm, h_run⟩
  rcases pmout with ⟨state2, txOutput⟩
  rcases of_bind_eq_ok h_run with ⟨refundCounter, hrefund, h_run⟩
  simp only [Prod.mk.injEq] at h_run
  rcases h_run with ⟨rfl, rfl⟩
  have hsub_some :
      (benv.state.incrNonce sender).subBal sender
        (tx.gas * effectiveGasPrice +
          if tx.isTypeThree = true then
            calculate_data_fee benv.stat.excessBlobGas tx
          else
            0).toB256 = some state1 := by
    generalize hopt : (benv.state.incrNonce sender).subBal sender
        (tx.gas * effectiveGasPrice +
          if tx.isTypeThree = true then
            calculate_data_fee benv.stat.excessBlobGas tx
          else
            0).toB256 = o at hsub ⊢
    cases o with
    | none => simp [Option.toExcept] at hsub
    | some s => simpa [Option.toExcept] using hsub
  -- the up-front debit does not wrap
  have hfee_lt := checkTransaction_fee_lt hcheck
  have hcdf := validateTransaction_floor_le hval
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
  have h6 := toNat_toB256_of_lt hfee_lt
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
Invert its successful do-block as in `processTransaction_inv_solvent`; use
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
    obtain ⟨⟨st, bout''⟩, h1, h2⟩ := of_bind_eq_ok h_run
    exact le_trans (ih h2) (processTransaction_sum_le h1)

/-
(1) Difficulty: ★★★☆☆
(2) Proof plan: induct on `wds`, generalizing the starting state.  For the
head withdrawal, prove that
`(wd.amount * (10 ^ 9).toB256).toNat = wd.amount.toNat * 10 ^ 9`; the product
cannot wrap because a withdrawal amount is 64-bit.  The head/tail decomposition
of `wdsum` and the global bound then gives the exact pre-sum bound required by
`State.Inv.addBal`.  Apply that lemma for the head and feed the resulting sum
identity (or `State.balSum_setBal`) and residual bound to the induction
hypothesis.
-/
lemma processWithdrawalsState_inv_solvent (wa : Adr)
    (st : _root_.State) (wds : List Withdrawal)
    (h_bound : sum st.bal + wdsum wds < 2 ^ 256)
    (h_inv : State.Inv wa st) :
    State.Inv wa (processWithdrawalsState st wds) := by
  sorry

lemma processCheckedSystemTransaction_to_unchecked {benv : Benv} {target : Adr} {data : B8L}
    {st : _root_.State} {out : MsgCallOutput}
    (h : processCheckedSystemTransaction benv target data = .ok ⟨st, out⟩) :
    processUncheckedSystemTransaction benv target data = .ok ⟨st, out⟩ := by
  dsimp [processCheckedSystemTransaction, processUncheckedSystemTransaction] at h ⊢
  split at h
  · exact (Except.noConfusion h)
  · simp only [pure_bind] at h
    rcases of_bind_eq_ok h with ⟨⟨st', out'⟩, h1, h2⟩
    split at h2
    · exact (Except.noConfusion h2)
    · obtain ⟨h3, h4⟩ := Prod.mk.inj (Except.ok.inj h2)
      subst h3; subst h4; exact h1

/-
(1) Difficulty: ★★☆☆☆
(2) Proof plan: invert `processGeneralPurposeRequests`.  Parsing deposits and
updating the request list do not touch state.  Each of the two checked system
transactions reduces, on its successful branch, to the corresponding
unchecked system transaction, so apply
`processUncheckedSystemTransaction_inv_solvent_sum_le` twice.  Thread
`createdAccounts` through `Benv.withState` and compose the two sum
inequalities.
-/
lemma processGeneralPurposeRequests_inv_solvent_sum_le (wa : Adr)
    (benv : Benv) (bout : BlockOutput)
    (st : _root_.State) (bout' : BlockOutput)
    (h_run : processGeneralPurposeRequests benv bout = .ok ⟨st, bout'⟩)
    (h_inv : Benv.InvSolvent wa benv) :
    State.Inv wa st ∧ sum st.bal ≤ sum benv.state.bal := by
  rw [processGeneralPurposeRequests] at h_run
  rcases of_bind_eq_ok h_run with ⟨deposits, h_dep, h_run⟩
  dsimp only at h_run
  split at h_run <;>
    (simp only [pure_bind] at h_run;
     rcases of_bind_eq_ok h_run with ⟨⟨st1, out1⟩, h1, h_run⟩;
     dsimp only at h_run;
     have hu1 := processUncheckedSystemTransaction_inv_solvent_sum_le wa benv
       withdrawalRequestPredeployAddress [] st1 out1
       (processCheckedSystemTransaction_to_unchecked h1) h_inv;
     have h_inv1 : Benv.InvSolvent wa (benv.withState st1) :=
       ⟨hu1.1, by simpa [Benv.withState] using h_inv.ca⟩;
     split at h_run <;>
       (rcases of_bind_eq_ok h_run with ⟨⟨st2, out2⟩, h2, h_run⟩;
        have hu2 := processUncheckedSystemTransaction_inv_solvent_sum_le wa (benv.withState st1)
          consolidationRequestPredeployAddress [] st2 out2
          (processCheckedSystemTransaction_to_unchecked h2) h_inv1;
        split at h_run <;>
          (obtain ⟨h3, h4⟩ := Prod.mk.inj (Except.ok.inj h_run);
           subst h3;
           exact ⟨hu2.1, le_trans (by simpa [Benv.withState] using hu2.2) hu1.2⟩)))

theorem applyBody_inv_solvent (wa : Adr)
    (benv : Benv) (txs : List (B8L ⊕ Tx)) (wds : List Withdrawal)
    (st : _root_.State) (bout : BlockOutput)
    (h_run : applyBody benv txs wds = .ok ⟨st, bout⟩)
    (h_wds : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (h_inv : Benv.InvSolvent wa benv) : State.Inv wa st := by
  rw [applyBody] at h_run
  simp only [cprint, verbose, Bool.false_eq_true, if_false, pure_bind] at h_run
  rcases of_bind_eq_ok h_run with ⟨⟨stBeacon, outBeacon⟩, h_beacon, h_run⟩
  rcases of_bind_eq_ok h_run with ⟨lastHash, h_lastHash, h_run⟩
  rcases of_bind_eq_ok h_run with ⟨⟨stHistory, outHistory⟩, h_history, h_run⟩
  rcases of_bind_eq_ok h_run with ⟨decodedTxs, h_decode, h_run⟩
  rcases of_bind_eq_ok h_run with ⟨⟨benvTxs, boutTxs⟩, h_txs, h_requests⟩
  dsimp only at h_history h_txs h_requests
  have h_beacon_inv :=
    processUncheckedSystemTransaction_inv_solvent_sum_le wa benv
      beaconRootsAddress benv.stat.parentBeaconBlockRoot.toB8L
      stBeacon outBeacon h_beacon h_inv
  have h_benv_beacon : Benv.InvSolvent wa (benv.withState stBeacon) :=
    ⟨h_beacon_inv.1, by simpa [Benv.withState] using h_inv.ca⟩
  have h_history_inv :=
    processUncheckedSystemTransaction_inv_solvent_sum_le wa
      (benv.withState stBeacon) historyStorageAddress lastHash.toB8L
      stHistory outHistory h_history h_benv_beacon
  have h_benv_history :
      Benv.InvSolvent wa ((benv.withState stBeacon).withState stHistory) :=
    ⟨h_history_inv.1, by simpa [Benv.withState] using h_benv_beacon.ca⟩
  have h_txs_inv : Benv.InvSolvent wa benvTxs :=
    applyTransactions_inv_solvent wa decodedTxs.putIndex
      ((benv.withState stBeacon).withState stHistory) benvTxs
      BlockOutput.init boutTxs h_txs h_benv_history
  have h_txs_sum := applyTransactions_sum_le h_txs
  dsimp [processWithdrawals] at h_requests
  have h_txs_bound : sum benvTxs.state.bal + wdsum wds < 2 ^ 256 := by
    have h_history_sum : sum stHistory.bal ≤ sum stBeacon.bal := by
      simpa [Benv.withState] using h_history_inv.2
    have h_txs_sum' : sum benvTxs.state.bal ≤ sum stHistory.bal := by
      simpa [Benv.withState] using h_txs_sum
    omega
  have h_wds_inv :=
    processWithdrawalsState_inv_solvent wa benvTxs.state wds
      h_txs_bound h_txs_inv.state
  have h_benv_wds : Benv.InvSolvent wa
      (benvTxs.withState (processWithdrawalsState benvTxs.state wds)) :=
    ⟨h_wds_inv, by simpa [Benv.withState] using h_txs_inv.ca⟩
  exact (processGeneralPurposeRequests_inv_solvent_sum_le wa
    (benvTxs.withState (processWithdrawalsState benvTxs.state wds))
    (boutTxs.withWithdrawalsTrie
      (processWithdrawalsTrie boutTxs.withdrawalsTrie wds))
    st bout h_requests h_benv_wds).1

theorem stateTransition_inv_solvent (wa : Adr)
    (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransition ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state := by
  -- invert `stateTransition`'s do-block; the state change is `applyBody`, so this
  -- is `applyBody_inv_solvent` (the block-check helpers don't touch state).
  rw [stateTransition] at h_run
  obtain ⟨_, _, h_run⟩ := of_bind_eq_ok h_run
  obtain ⟨_, _, h_run⟩ := of_bind_eq_ok h_run
  dsimp only at h_run
  obtain ⟨⟨st, bout⟩, h_ab, h_run⟩ := of_bind_eq_ok h_run
  dsimp only at h_run
  obtain ⟨_, _, h_run⟩ := of_bind_eq_ok h_run
  rw [← Except.ok.inj h_run]
  exact applyBody_inv_solvent wa (initBenv ch block.header) block.txs block.wds st bout h_ab h_wds
    ⟨h_inv, AdrSet.not_mem_empty⟩

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

-- Chain-level induction corollary : no sequence of valid blocks can break
-- WETH solvency.
theorem chain_inv_solvent (wa : Adr) (ch ch' : BlockChain)
    (h_reach : BlockChain.Reach ch ch')
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state := by
  -- induction on `h_reach`; `refl` is `h_inv`, `step` chains `stateTransition_inv_solvent`
  -- (the `sum + wdsum < 2^256` bound is carried by the `step` constructor).
  induction h_reach with
  | refl => exact h_inv
  | step h_reach' h_bound h_st ih => exact stateTransition_inv_solvent wa _ _ _ h_st h_bound ih

-- Bonus level : preservation through RLP decoding and block hash checks.
theorem addBlockToChain_inv_solvent (wa : Adr)
    (ch ch' : BlockChain) (rlp : B8L)
    (h_run : addBlockToChain ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state := by
  -- invert `addBlockToChain` (rlpToBlock decode + hash check), then one
  -- `stateTransition_inv_solvent` step (h_wds instantiated at the decoded block).
  rw [addBlockToChain] at h_run
  obtain ⟨⟨block, hash⟩, h_rlp, h_run⟩ := of_bind_eq_ok h_run
  dsimp only at h_run
  obtain ⟨_, _, h_run⟩ := of_bind_eq_ok h_run
  obtain ⟨_, _, h_run⟩ := of_bind_eq_ok h_run
  -- outer hash check
  split at h_run
  · exact absurd h_run (by simp)
  · simp only [pure_bind] at h_run
    -- inner rlp check
    split at h_run
    · exact absurd h_run (by simp)
    · -- case on `stateTransition ch block`
      split at h_run
      · exact absurd h_run (by simp [Pure.pure, Except.pure])
      · rename_i chain h_st
        obtain ⟨y, hy, h_run⟩ := of_bind_eq_ok h_run
        obtain ⟨_, _, h_run⟩ := of_bind_eq_ok h_run
        obtain ⟨_, _, h_run⟩ := of_bind_eq_ok h_run
        have hyc : chain = ch' :=
          (Except.ok.inj hy).trans (Sum.inl.inj (Except.ok.inj h_run))
        subst hyc
        exact stateTransition_inv_solvent wa ch _ block h_st (h_wds block hash h_rlp) h_inv
