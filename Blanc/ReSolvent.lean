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

def Devm.getStor (devm : Devm) (adr : Adr) : Stor :=
  (devm.getAcct adr).stor


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

lemma chargeGas_getStor_eq {cost devm devm'} (h : chargeGas cost devm = .ok devm') : devm.getStor = devm'.getStor := by
  dsimp [chargeGas] at h
  split at h <;> try contradiction
  cases h; rfl

lemma Devm.push_getStor_eq {x devm devm'} (h : Devm.push x devm = .ok devm') : devm.getStor = devm'.getStor := by
  simp only [Devm.push, bind, Except.bind, Except.assert] at h
  split at h <;> try contradiction
  cases h; rfl

lemma Devm.pop_getStor_eq {devm devm' x} (h : Devm.pop devm = .ok ⟨x, devm'⟩) : devm.getStor = devm'.getStor := by
  dsimp [Devm.pop] at h; split at h <;> try contradiction
  cases h; rfl

lemma pushItem_getStor_eq {x c devm devm'} (h : pushItem x c devm = .ok devm') : devm.getStor = devm'.getStor := by
  dsimp [pushItem] at h
  rcases hc : chargeGas c devm with _ | devm2
  · simp only [hc, bind, Except.bind] at h; contradiction
  · simp only [hc, bind, Except.bind] at h
    rcases hp : Devm.push x devm2 with _ | devm3
    · simp only [hp] at h; contradiction
    · simp only [hp] at h
      injection h with h_eq; subst h_eq
      exact (chargeGas_getStor_eq hc).trans (Devm.push_getStor_eq hp)

class Rinst.Hinv {ξ : Type} (f : Devm → ξ) (o : Rinst) where (inv : Rinst.Inv f o)

instance {ξ : Type} (f : Devm → ξ) (o : Rinst) [Rinst.Hinv f o] :
    Ninst.Hinv f (Ninst.reg o) := ⟨by
  intros e s s' h
  rcases h with ⟨xl, h_filled, pc, run⟩
  cases xl with
  | some _ => cases run
  | none =>
    dsimp [Ninst.Run'] at run
    exact Rinst.Hinv.inv run
⟩

instance {o : Rinst} : Rinst.Hinv Devm.getBal o := ⟨Rinst.inv_bal⟩

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

instance : Ninst.Hinv Devm.getStor (Ninst.reg Rinst.calldataload) := ⟨by
  intros e s s' h
  rcases h with ⟨xl, h_filled, pc, run⟩
  cases xl with
  | some _ => cases run
  | none =>
    dsimp [Ninst.Run', Rinst.run, Rinst.runCore] at run
    rcases hp : Devm.pop s with _ | val
    · rw [hp] at run; dsimp [bind, Except.bind] at run; contradiction
    · rw [hp] at run; dsimp [bind, Except.bind] at run
      rcases val with ⟨x1, s1⟩
      rcases hc : chargeGas gVerylow s1 with _ | s2
      · rw [hc] at run; dsimp [bind, Except.bind] at run; contradiction
      · rw [hc] at run; dsimp [bind, Except.bind] at run
        rcases hpush : Devm.push (B8L.toB256 (List.sliceD e.data x1.toNat 32 0)) s2 with _ | s''
        · rw [hpush] at run; contradiction
        · rw [hpush] at run
          injection run with h_eq; subst h_eq
          exact (Devm.pop_getStor_eq hp).trans <| (chargeGas_getStor_eq hc).trans (Devm.push_getStor_eq hpush)
⟩

instance : Ninst.Hinv Devm.getStor (Ninst.reg Rinst.shr) := ⟨by
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
        rcases hpush : pushItem (x2 >>> x1.toNat) gVerylow s2 with _ | s''
        · rw [hpush] at run; contradiction
        · rw [hpush] at run
          injection run with h_eq; subst h_eq
          exact (Devm.pop_getStor_eq hp1).trans <| (Devm.pop_getStor_eq hp2).trans <| (pushItem_getStor_eq hpush)
⟩

instance : Ninst.Hinv Devm.getStor Ninst.shl := ⟨sorry⟩
instance : Ninst.Hinv Devm.getStor Ninst.mstore := ⟨sorry⟩
instance : Ninst.Hinv Devm.getStor Ninst.sload := ⟨sorry⟩
instance : Ninst.Hinv Devm.getStor Ninst.calldatacopy := ⟨sorry⟩
instance : Ninst.Hinv Devm.getStor Ninst.address := ⟨sorry⟩
instance : Ninst.Hinv Devm.getStor Ninst.balance := ⟨sorry⟩
instance : Ninst.Hinv Devm.getStor Ninst.kec := ⟨sorry⟩

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

lemma approve_inv_solvent {sevm : Sevm} {s r : Devm}
    (run : Func.Run (weth.main :: weth.aux) sevm s approve r)
    (h_sv : s.PreSolvent sevm.currentTarget sevm) :
    r.PostSolvent sevm.currentTarget := sorry

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
