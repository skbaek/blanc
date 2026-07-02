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

instance : Linst.Hinv Devm.getBal Devm.getBal Linst.ret := by constructor; sorry

instance : Linst.Hinv Devm.getBal Devm.getBal Linst.rev := by
  constructor; intros e s r h
  simp only [Linst.Run, Linst.run] at h
  rcases of_bind_eq_ok h with ⟨v1, h1, h2⟩
  rcases of_bind_eq_ok h2 with ⟨v2, h3, h4⟩
  rcases of_bind_eq_ok h4 with ⟨v3, h5, h6⟩
  contradiction

instance : Linst.Hinv Devm.getStor Devm.getStor Linst.stop := by
  constructor; intros e s r h; injection h with h_eq; subst h_eq; rfl

instance : Linst.Hinv Devm.getStor Devm.getStor Linst.ret := by constructor; sorry

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

lemma of_prepApprove {sevm : Sevm} {s s' : Devm} :
    Line.Run sevm s prepApprove s' →
    ∃ vx x y, ([vx, x, y] <<+ s'.stack) ∧ (vx = 0 ↔ ¬ ValidAdr x) := sorry

lemma sstore_inv_stor_rest {x xs} {sevm : Sevm} {s s' : Devm} :
  ¬ ValidAdr x →
  (x :: xs <<+ s.stack) →
  Ninst.Run sevm s .sstore s' →
  (s.getStor sevm.currentTarget).rest = (s'.getStor sevm.currentTarget).rest := sorry

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

lemma transferFrom_inv_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s transferFrom r)
    (h_sv : s.PreSolvent sevm.currentTarget sevm) :
    r.PostSolvent sevm.currentTarget := sorry

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
