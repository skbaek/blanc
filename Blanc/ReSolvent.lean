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

def Inv0 {ξ} (r : Devm → ξ) (f : Devm → Except (String × Devm) Devm) : Prop :=
    ∀ {pre post}, f pre = .ok post → r pre = r post

def Inv1 {ξ υ} (r : Devm → ξ) (f : Devm → Except (String × Devm) (υ × Devm)) : Prop :=
    ∀ {pre y post}, f pre = .ok ⟨y, post⟩ → r pre = r post

class Hinv0 {ξ} (r : Devm → ξ) (f : Devm → Except (String × Devm) Devm) where
  (inv : Inv0 r f)

class Hinv1 {ξ υ} (r : Devm → ξ)
    (f : Devm → Except (String × Devm) (υ × Devm)) where
  (inv : Inv1 r f)

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
    sorry
  · -- rev
    sorry
  · -- dest
    sorry

def Exec.InvDepth (k : Nat) (ca : Adr) (p : Prog) (σ : Sevm → Devm → Prop) : Prop :=
  ForallDeeperAt k ca p (λ _ sevm pre exn _ => σ sevm pre → ifOk (σ sevm) exn)

lemma Line.inv_solvent {e e' s l s' a}
    (h_bal : Line.Inv Devm.getBal l) (h_stor : Line.Inv Devm.getStor l)
    (h_sv : Devm.Solvent s a e) (h_run : Line.Run e' s l s') : Devm.Solvent s' a e := by
  unfold Devm.Solvent; rw [← h_bal h_run, ← h_stor h_run]; exact h_sv

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
         Cond e.currentTarget e s ∧
         Exec.InvDepth e.depth e.currentTarget weth (Cond e.currentTarget) )
      ?_ ?_ rfl ?_ wethTree ?_ sevm s₁ r ⟨cond₁, ih⟩ temp ).1
    <;> clear temp cond₁ ih r s₁ sevm
  · sorry
  · sorry
  · sorry
  · sorry






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
