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

def Devm.Solvent (devm : Devm) (a : Adr) (sevm : Sevm) : Prop :=
  (sevm.currentTarget = a → Stor.Solvent (devm.getStor a) sevm.value (devm.getBal a)) ∧
  (sevm.currentTarget ≠ a → Stor.Solvent (devm.getStor a) 0 (devm.getBal a))

def Execution.Solvent (sevm : Sevm) : Execution → Adr → Prop
  | .error _, _ => True
  | .ok devm, adr => devm.Solvent adr sevm

-- Cond : invariant in the main induction for proof of solvency preservation
structure Cond (wa : Adr) (sevm : Sevm) (devm : Devm) : Prop where
  (nof : sum devm.getBal < 2 ^ 256)
  (solvent : devm.Solvent wa sevm)

lemma Precond.state_eq {wa sevm devm devm'}
    (h_pc : Cond wa sevm devm) (h_eq : devm'.state = devm.state) :
    Cond wa sevm devm' := by
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

lemma Linst.inv_nof {sevm devm l devm'} :
    Linst.Run sevm devm l (.ok devm') →
    sum devm.getBal < 2 ^ 256 →
    sum devm'.getBal < 2 ^ 256 := by
  sorry

def Inv0 {ξ} (r : Devm → ξ) (f : Devm → Except (String × Devm) Devm) : Prop :=
    ∀ {pre post}, f pre = .ok post → r pre = r post

def Inv1 {ξ υ} (r : Devm → ξ) (f : Devm → Except (String × Devm) (υ × Devm)) : Prop :=
    ∀ {pre y post}, f pre = .ok ⟨y, post⟩ → r pre = r post

class Hinv0 {ξ} (r : Devm → ξ) (f : Devm → Except (String × Devm) Devm) where
  (inv : Inv0 r f)

class Hinv1 {ξ υ} (r : Devm → ξ)
    (f : Devm → Except (String × Devm) (υ × Devm)) where
  (inv : Inv1 r f)

instance {ca} {cost} : Inv0 (λ devm => devm.getBal ca) (chargeGas cost) := sorry
instance {ca} : Inv1 (λ devm => devm.getBal ca) Devm.popToNat := sorry

lemma Linst.inv_solvent (wa : Adr) :
    ∀ sevm devm l post,
      Linst.Run sevm devm l (.ok post) →
      Cond wa sevm devm →
      Cond wa sevm post := by
  intro sevm devm l exn h_run h_pc
  cases l
  · simp [Linst.Run, Linst.run] at h_run
    rw [← h_run]
    exact h_pc
  · -- ret
    -- TODO: Unfold the `do` block and apply `Precond.state_eq`
    sorry
  · -- rev
    -- TODO: Unfold the `do` block and apply `Precond.state_eq`
    sorry
  · -- dest
    -- TODO: Prove that `dest` preserves `Precond` using `transfer_inv_solvent` logic
    sorry

def Exec.InvDepth (k : Nat) (ca : Adr) (p : Prog) (σ : Sevm → Devm → Prop) : Prop :=
  ForallDeeperAt k ca p (λ _ sevm pre exn _ => σ sevm pre → ifOk (σ sevm) exn)

def Line.Inv {ξ : Type} (f : Devm → ξ) (l : Line) : Prop :=
  ∀ {e s s'}, l.Run e s s' → f s = f s'

lemma Line.of_inv {ξ : Type} {e s s'} (r : Devm → ξ) {l : Line} :
  Line.Inv r l → l.Run e s s' → r s = r s' := λ h => h

lemma Line.inv_solvent {e e' s l s' a}
    (h_bal : Line.Inv Devm.getBal l) (h_stor : Line.Inv Devm.getStor l)
    (h_sv : Devm.Solvent s a e) (h_run : Line.Run e' s l s') : Devm.Solvent s' a e := by
  unfold Devm.Solvent; rw [← h_bal h_run, ← h_stor h_run]; exact h_sv

def Ninst.Inv {ξ : Type} (r : Devm → ξ) (i : Ninst) : Prop :=
  ∀ {e s s'}, Ninst.Run e s i s' → r s = r s'

lemma Line.nil_inv {ξ : Type} {f : Devm → ξ} : Line.Inv f [] := by
  intros e s s' h; cases h; rfl

lemma Line.cons_inv {ξ : Type} {f : Devm → ξ} {i l} :
    Ninst.Inv f i → Line.Inv f l → Line.Inv f (i :: l) := by
  intros h0 h1 e s s'' h2
  rcases Line.of_run_cons h2 with ⟨s', h3, h4⟩
  apply Eq.trans (h0 h3) (h1 h4)

class Ninst.Hinv {ξ : Type} (f : Devm → ξ) (i : Ninst) where (inv : Ninst.Inv f i)

lemma chargeGas_getBal_eq {cost devm devm'} (h : chargeGas cost devm = .ok devm') : devm.getBal = devm'.getBal := by
  dsimp [chargeGas] at h
  split at h <;> try contradiction
  cases h; rfl

lemma Devm.push_getBal_eq {x devm devm'} (h : Devm.push x devm = .ok devm') : devm.getBal = devm'.getBal := by
  simp only [Devm.push, bind, Except.bind, Except.assert] at h
  split at h <;> try contradiction
  cases h; rfl

lemma chargeGas_getStor_eq {cost devm devm'} (h : chargeGas cost devm = .ok devm') : devm.getStor = devm'.getStor := by
  dsimp [chargeGas] at h
  split at h <;> try contradiction
  cases h; rfl

lemma Devm.push_getStor_eq {x devm devm'} (h : Devm.push x devm = .ok devm') : devm.getStor = devm'.getStor := by
  simp only [Devm.push, bind, Except.bind, Except.assert] at h
  split at h <;> try contradiction
  cases h; rfl

lemma Devm.pop_getBal_eq {devm devm' x} (h : Devm.pop devm = .ok ⟨x, devm'⟩) : devm.getBal = devm'.getBal := by
  dsimp [Devm.pop] at h; split at h <;> try contradiction
  cases h; rfl

lemma Devm.pop_getStor_eq {devm devm' x} (h : Devm.pop devm = .ok ⟨x, devm'⟩) : devm.getStor = devm'.getStor := by
  dsimp [Devm.pop] at h; split at h <;> try contradiction
  cases h; rfl

lemma pushItem_getBal_eq {x c devm devm'} (h : pushItem x c devm = .ok devm') : devm.getBal = devm'.getBal := by
  dsimp [pushItem] at h
  rcases hc : chargeGas c devm with _ | devm2
  · simp only [hc, bind, Except.bind] at h; contradiction
  · simp only [hc, bind, Except.bind] at h
    rcases hp : Devm.push x devm2 with _ | devm3
    · simp only [hp] at h; contradiction
    · simp only [hp] at h
      injection h with h_eq; subst h_eq
      exact (chargeGas_getBal_eq hc).trans (Devm.push_getBal_eq hp)

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
        exact (chargeGas_getBal_eq hc).trans (Devm.push_getBal_eq hp)
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

instance : Ninst.Hinv Devm.getBal (Ninst.reg Rinst.calldataload) := ⟨by
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
          exact (Devm.pop_getBal_eq hp).trans <| (chargeGas_getBal_eq hc).trans (Devm.push_getBal_eq hpush)
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

instance : Ninst.Hinv Devm.getBal (Ninst.reg Rinst.shr) := ⟨by
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
          exact (Devm.pop_getBal_eq hp1).trans <| (Devm.pop_getBal_eq hp2).trans <| (pushItem_getBal_eq hpush)
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

open Qq

def Ninst.inv_expr (ξx fx : Lean.Expr) (ix : Q(Ninst)) : Lean.Elab.Tactic.TacticM Lean.Expr := do
  let x ← Lean.Meta.synthInstance <| Lean.mkApp3 q(@Ninst.Hinv) ξx fx ix
  pure <| Lean.mkApp4 q(@Ninst.Hinv.inv) ξx fx ix x

def instInv : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
  let t ← Lean.Elab.Tactic.getMainTarget
  have t' : Q(Prop) := t
  match t' with
  | ~q(@Ninst.Inv $ξx $fx $ix) =>
    let x ← Ninst.inv_expr ξx fx ix
    Lean.Elab.Tactic.closeMainGoal `tacName x
  | _ => dbg_trace "Not a Ninst.Inv goal"

def line_nil_inv : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Expr.apply <|
    Lean.Expr.const (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "Line") "nil_inv") []

def line_cons_inv : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Expr.apply <|
    Lean.Expr.const (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "Line") "cons_inv") []

partial def line_inv : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
  let t : Q(Prop) ← Lean.Elab.Tactic.getMainTarget
  match t with
  | ~q(@Line.Inv $ξx $fx $lx) =>
    let lx' : Q(Line) ← Lean.Meta.whnf lx
    match lx' with
    | ~q([]) => line_nil_inv
    | _ => line_cons_inv; instInv; line_inv
  | _ => dbg_trace "Not a Line.Inv goal"

elab "line_inv" : tactic => line_inv

lemma weth_inv' {sevm : Sevm} {s r}
    (cond : Cond sevm.currentTarget sevm s)
    (ih : Exec.InvDepth sevm.depth sevm.currentTarget weth (Cond sevm.currentTarget)) :
    Func.Run (weth.main :: weth.aux) sevm s (Func.call 0) r →
    Cond sevm.currentTarget sevm r := by

  -- unwrap the initial `call 0` (this part does not exist in original proof in Solvent.lean)
  intro run; cases run
  rename (_ = _) => eq
  rename (Func.Run _ _ _ _ _) => run
  rename (Devm.Burn _ _) => burn
  rename Devm => s₀
  cases eq
  have cond₀ : Cond sevm.currentTarget sevm s₀ :=
    Precond.state_eq cond burn.state.symm
  clear cond burn s
  revert run
  -- this point corresponds to the starting point of weth_inv' in Solvent.lean
  pexec fsig
  have cond₁  : Cond sevm.currentTarget sevm s₁ := by
    refine' ⟨_, _⟩
    · rw [← Line.of_inv Devm.getBal sorry h₁]; exact cond₀.nof
    · apply Line.inv_solvent _ _ cond₀.solvent h₁ <;> line_inv
  clear cond₀
  sorry

theorem weth_inv_solvent (wa : Adr) :
    ∀ sevm pre post,
      Exec 0 sevm pre (.ok post)  →
      (sevm.currentTarget = wa → some sevm.code.toList = Prog.compile weth) →
      Cond wa sevm pre →
      Cond wa sevm post := by
  intro sevm devm exn exc h_code h_pc
  apply lift_inv wa weth (Cond wa) --(Postcond wa)
  · intro sevm pre post run eq; rw [← eq]
    dsimp [Prog.Run] at run
    intro ih cond; apply weth_inv' cond _ run
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
