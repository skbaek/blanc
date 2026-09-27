import Blanc.Lift.LockCheckSound

/-!
# The lock checker along a frame: flags, one step, and dominance

Second half of the soundness of `LockCheck.lockCert`
(`Blanc/Lift/LockCheck.lean`).  `Blanc/Lift/LockCheckSound.lean` gives the
meaning of facts and proves the fact rules and the symbol transfer sound; this
module gives the meaning of the flags (`Flags`), proves every rule of the walk
sound for one same-frame edge (`lock_step`, which re-runs `cursor_step`'s case
split so that the synthetic branch taken is the concrete one), and concludes
`LockCheck.dominance`: `LockSpec.Dominance` of `Blanc/LockExclusion.lean` for
the code of any certificate the checker accepts, with its strong form and the
absence of forbidden opcodes as separate theorems.
-/

namespace Blanc.Lift.LockCheck

open Jaune AbstractStackSafety Blanc.LockExclusion

local notation "PP" => Exec.Deriv.ParentPrefix

/-! ## Decoding and the same-frame order -/

theorem ninstAt_inj {code : ByteArray} {pc : Nat} {i j : Ninst}
    (h1 : Ninst.At code pc i) (h2 : Ninst.At code pc j) : i = j := by
  unfold Ninst.At at h1 h2
  rw [h1] at h2
  cases h2
  rfl

/-- A node strictly before the successor of `n` is a prefix of `n`. -/
theorem pp_back {F n n' b : Exec.Deriv} (reach : PP F n)
    (edge : Exec.Deriv.ParentStep n' n) (hb : PP F b) (hbn' : PP b n') (hne : b ≠ n') :
    PP b n := by
  rcases Blanc.Exec.Deriv.ParentPrefix.linear hb reach with h | h
  · exact h
  · rcases (Blanc.Exec.Deriv.ParentStep.parentPrefix_iff edge).mp h with rfl | h'
    · exact .refl _
    · exact (hne (Exec.Deriv.ParentPrefix.antisymm hbn' h')).elim

/-- A same-frame edge out of a node that decodes no frame-spawning instruction
keeps one storage cell of the running account, unless the node is an `SSTORE`
addressed at it. -/
theorem lockAt_edge {n n' : Exec.Deriv} {slot : B256}
    (edge : Exec.Deriv.ParentStep n' n) (hfork : CoveredFork n.sevm.benvStat.fork)
    (noexec : ∀ x, ¬ Xinst.At n.sevm.code n.pc x)
    (notStore : Ninst.At n.sevm.code n.pc (.reg .sstore) → n.devm.stack.head? ≠ some slot) :
    lockAt n.sevm.currentTarget slot n'.devm = lockAt n.sevm.currentTarget slot n.devm := by
  cases edge with
  | cont hstep _ => exact Evm.step_cont_getStor_get hfork hstep (fun _ h => notStore h)
  | doneOk hstep _ _ _ =>
    obtain ⟨x, hx, -, -⟩ := Evm.step_spawn_inv hstep
    exact (noexec x hx).elim
  | runOk hstep _ _ _ _ =>
    obtain ⟨x, hx, -, -⟩ := Evm.step_spawn_inv hstep
    exact (noexec x hx).elim

theorem noexec_of_ninst {code : ByteArray} {pc : Nat} {i : Ninst}
    (hat : Ninst.At code pc i) (hi : ∀ x, i ≠ .exec x) : ∀ x, ¬ Xinst.At code pc x :=
  fun x hx => hi x (ninstAt_inj hat hx)

theorem noexec_of_jinst {code : ByteArray} {pc : Nat} {j : Jinst}
    (hat : Jinst.At code pc j) : ∀ x, ¬ Xinst.At code pc x := fun x hx => by
  unfold Jinst.At at hat; unfold Xinst.At at hx; rw [hat] at hx; cases hx

theorem nostore_of_jinst {code : ByteArray} {pc : Nat} {j : Jinst}
    (hat : Jinst.At code pc j) : ¬ Ninst.At code pc (.reg .sstore) := fun hx => by
  unfold Jinst.At at hat; unfold Ninst.At at hx; rw [hat] at hx; cases hx

/-! ## The meaning of the flags -/

section Flags

variable (sp : Spec) (F : Exec.Deriv)

/-- The flags of `σ` at node `n`, before `n` is visited. -/
structure Flags (σ : LSt) (n : Exec.Deriv) : Prop where
  passed : σ.passed = true → ∃ m, PP F m ∧ PP m n ∧
    lockAt F.sevm.currentTarget sp.slot m.devm ≠ sp.locked
  setNow : σ.setNow = true → lockAt F.sevm.currentTarget sp.slot n.devm = sp.locked
  noMut : σ.noMut = true → ∀ b, PP F b → PP b n → b ≠ n → b.pc ∉ sp.mutBodies

/-- The flags of `σ` at node `n`, once `n` is visited. -/
structure FlagsV (σ : LSt) (n : Exec.Deriv) : Prop where
  passed : σ.passed = true → ∃ m, PP F m ∧ PP m n ∧
    lockAt F.sevm.currentTarget sp.slot m.devm ≠ sp.locked
  setNow : σ.setNow = true → lockAt F.sevm.currentTarget sp.slot n.devm = sp.locked
  noMut : σ.noMut = true → ∀ b, PP F b → PP b n → b.pc ∉ sp.mutBodies

end Flags

section Visit

variable {sp : Spec} {F n : Exec.Deriv} {σ σv : LSt}

/-- Visiting a node: its body-start obligations, and the visited flags. -/
theorem visit_sound (reach : PP F n) (hfl : Flags sp F σ n)
    (hv : visit sp n.pc σ = some σv) :
    FlagsV sp F σv n ∧ σv.kv = σ.kv ∧ σv.facts = σ.facts ∧ σv.passed = σ.passed ∧
      σv.setNow = σ.setNow ∧
      (n.pc ∈ sp.bodies → ∃ m, PP F m ∧ PP m n ∧
        lockAt F.sevm.currentTarget sp.slot m.devm ≠ sp.locked) ∧
      (n.pc ∈ sp.mutBodies → lockAt F.sevm.currentTarget sp.slot n.devm = sp.locked) := by
  unfold visit at hv
  by_cases hmut : sp.mutBodies.contains n.pc = true
  · simp only [hmut, ite_true] at hv
    split at hv
    · rename_i hc
      cases hv
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
        Bool.not_eq_true'] at hc
      refine ⟨⟨hfl.passed, hfl.setNow, fun h => by cases h⟩, rfl, rfl, rfl, rfl,
        fun hb => ?_, fun _ => hfl.setNow hc.2⟩
      rcases hc.1 with hc | hc
      · rw [List.contains_iff_mem.mpr hb] at hc; cases hc
      · exact hfl.passed hc
    · cases hv
  · simp only [hmut, Bool.false_eq_true, ite_false] at hv
    split at hv
    · rename_i hc
      cases hv
      have hm : n.pc ∉ sp.mutBodies := by simpa using hmut
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
      refine ⟨⟨hfl.passed, hfl.setNow, fun h b hb hbn => ?_⟩, rfl, rfl, rfl, rfl,
        fun hb => ?_, fun h => (hm h).elim⟩
      · by_cases he : b = n
        · subst he; exact hm
        · exact hfl.noMut h b hb hbn he
      · rcases hc.1 with hc | hc
        · rw [List.contains_iff_mem.mpr hb] at hc; cases hc
        · exact hfl.passed hc
    · cases hv

/-- Visited flags become the flags of the successor, for a successor state
that keeps `passed` and `noMut` and whose `setNow` is justified at the
successor. -/
theorem flags_succ {n' : Exec.Deriv} {σ' : LSt} (reach : PP F n)
    (edge : Exec.Deriv.ParentStep n' n) (hfl : FlagsV sp F σv n)
    (hp : σ'.passed = true → σv.passed = true ∨ ∃ m, PP F m ∧ PP m n ∧
      lockAt F.sevm.currentTarget sp.slot m.devm ≠ sp.locked)
    (hs : σ'.setNow = true → lockAt F.sevm.currentTarget sp.slot n'.devm = sp.locked)
    (hm : σ'.noMut = true → σv.noMut = true) : Flags sp F σ' n' := by
  have hnn : PP n n' := .step edge (.refl _)
  refine ⟨fun h => ?_, hs, fun h b hb hbn hne => ?_⟩
  · rcases hp h with h | h
    · obtain ⟨m, h1, h2, h3⟩ := hfl.passed h
      exact ⟨m, h1, h2.trans hnn, h3⟩
    · obtain ⟨m, h1, h2, h3⟩ := h
      exact ⟨m, h1, h2.trans hnn, h3⟩
  · exact hfl.noMut (hm h) b hb (pp_back reach edge hb hbn hne)

end Visit

/-! ## One instruction on the lock state -/

section Lstep

variable {sp : Spec} {F n n' : Exec.Deriv}

theorem effSetNow_other {pc : Nat} {i : Ninst} {σ : LSt} (h1 : i ≠ .reg .sstore)
    (h2 : ∀ x, i ≠ .exec x) : effSetNow sp pc i σ = some σ.setNow := by
  unfold effSetNow
  split
  · exact (h1 rfl).elim
  · exact (h1 rfl).elim
  · exact (h2 _ rfl).elim
  · rfl

/-- The `SSTORE` rule and the `setNow` update are sound for one instruction. -/
theorem effSetNow_sound {i : Ninst} {σ : LSt} {S rest : List B256} {b : Bool}
    (reach : PP F n) (edge : Exec.Deriv.ParentStep n' n)
    (hfork : CoveredFork n.sevm.benvStat.fork)
    (hat : Ninst.At n.sevm.code n.pc i) (run : Ninst.Run n.sevm n.devm i n'.devm)
    (hv : Val sp F n σ.kv σ.facts S) (hstack : n.devm.stack = S ++ rest)
    (hs : σ.setNow = true → lockAt F.sevm.currentTarget sp.slot n.devm = sp.locked)
    (he : effSetNow sp n.pc i σ = some b) :
    b = true → lockAt F.sevm.currentTarget sp.slot n'.devm = sp.locked := by
  have hsevm : n.sevm = F.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq reach
  rw [← hsevm] at hs ⊢
  by_cases hsst : i = .reg .sstore
  · subst hsst
    obtain ⟨ρ, hS, hf⟩ := hv
    rcases hkv : σ.kv with _ | ⟨k, _ | ⟨v, kt⟩⟩
    · simp [effSetNow, hkv] at he
    · simp [effSetNow, hkv] at he
    rw [hkv] at hS
    obtain ⟨St, hst⟩ : ∃ St, n.devm.stack = ρ k :: ρ v :: St := by
      cases hS with
      | cons h0 h1 =>
        cases h1 with
        | cons h1 _ => exact ⟨_, by rw [hstack, ← h0, ← h1]; rfl⟩
    have hset := sstore_getStor_set run (x := ρ k) (y := ρ v) (xs := St) ⟨[], by
      simp [Split, hst]⟩
    simp only [effSetNow, hkv] at he
    intro hb
    unfold lockAt
    rw [hset]
    split at he
    · rename_i hex
      cases he
      rw [Stor.get_set_ne _ (excluded_sound hf hex)]
      exact hs hb
    · split at he
      · rename_i hc
        cases he
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        rw [constOf_sound' hf hc.1.1]
        rw [Stor.get_set_self]
        exact constOf_sound' hf (of_decide_eq_true hb)
      · cases he
  · by_cases hex : ∃ x, i = .exec x
    · obtain ⟨x, rfl⟩ := hex
      simp only [effSetNow, Option.some.injEq] at he
      subst he
      intro h; cases h
    · have hex' : ∀ x, i ≠ .exec x := fun x h => hex ⟨x, h⟩
      rw [effSetNow_other hsst hex', Option.some.injEq] at he
      subst he
      intro hb
      rw [lockAt_edge edge hfork (noexec_of_ninst hat hex')
        (fun h => (hsst (ninstAt_inj hat h)).elim)]
      exact hs hb

theorem lstep_nonpush {pc : Nat} {i : Ninst} {σ σ' : LSt}
    (hn : ∀ (bs : Bytes) (fits : bs.length ≤ 32), i ≠ .push bs fits)
    (h : lstep sp pc i σ = some σ') :
    ∃ out kv' b, ninstTransfer i (indexPattern σ.kv.length) = some out ∧
      out.count none ≤ 1 ∧
      out.mapM (fun l => match l with
        | none => some (freshSym σ.kv σ.facts) | some j => σ.kv[j.toNat]?) = some kv' ∧
      effSetNow sp pc i σ = some b ∧
      σ' = ⟨kv', (opFacts sp σ.facts σ.kv i (freshSym σ.kv σ.facts) ++ σ.facts).filter
        (live kv'), σ.passed, b, σ.noMut⟩ := by
  have e : lstep sp pc i σ = (do
      let out ← ninstTransfer i (indexPattern σ.kv.length)
      guard (out.count none ≤ 1)
      let r := freshSym σ.kv σ.facts
      let kv' ← out.mapM (fun l => match l with
        | none => some r
        | some j => σ.kv[j.toNat]?)
      let setNow' ← effSetNow sp pc i σ
      some (⟨kv', (opFacts sp σ.facts σ.kv i r ++ σ.facts).filter (live kv'), σ.passed,
        setNow', σ.noMut⟩ : LSt)) := by
    cases i with
    | push bs fits => exact (hn bs fits rfl).elim
    | _ => rfl
  rw [e] at h
  cases ho : ninstTransfer i (indexPattern σ.kv.length) with
  | none => simp [ho] at h
  | some out =>
    by_cases hc : out.count none ≤ 1
    · cases hm : out.mapM (fun l => match l with
          | none => some (freshSym σ.kv σ.facts) | some j => σ.kv[j.toNat]?) with
      | none => simp [ho, hc, hm] at h
      | some kv' =>
        cases hb : effSetNow sp pc i σ with
        | none => simp [ho, hb] at h
        | some b =>
          simp only [ho, hc, hm, hb, Option.bind_eq_bind, Option.bind_some, guard,
            ite_true, Option.pure_def, Option.some.injEq] at h
          exact ⟨out, kv', b, rfl, hc, hm, rfl, h.symm⟩
    · simp [ho, hc] at h

/-- The instructions with fact rules push their one computed result on top. -/
theorem opFacts_head {fs : List Fact} {kv : List Nat} {i : Ninst} {r : Nat} {p out : Pattern}
    (hne : opFacts sp fs kv i r ≠ []) (hout : ninstTransfer i p = some out) :
    ∃ o, out = none :: o := by
  cases i with
  | reg rr =>
    cases rr
    all_goals first
      | (exfalso; apply hne; simp [opFacts]; done)
      | skip
    all_goals
      simp only [ninstTransfer, liftRegularTransfer, regularTransfer, binaryTransfer,
        unaryTransfer] at hout
      split at hout <;> simp only [Option.some.injEq, reduceCtorEq] at hout
      exact ⟨_, hout.symm⟩
  | _ => exact (hne (by simp [opFacts])).elim

theorem forall₂_update_head {ρ : Nat → B256} {r : Nat} {w : B256} {kv : List Nat}
    {S : List B256} (h : List.Forall₂ (fun s x => Function.update ρ r w s = x) (r :: kv) S) :
    S.head? = some w := by
  cases h with
  | cons h0 _ => simp [← h0]

theorem allHold_append {sp : Spec} {F n : Exec.Deriv} {ρ : Nat → B256} {fs gs : List Fact}
    (h1 : AllHold sp F n ρ fs) (h2 : AllHold sp F n ρ gs) : AllHold sp F n ρ (fs ++ gs) :=
  fun f hf => (List.mem_append.mp hf).elim (h1 f) (h2 f)

theorem allHold_filter {sp : Spec} {F n : Exec.Deriv} {ρ : Nat → B256} {fs : List Fact}
    (p : Fact → Bool) (h : AllHold sp F n ρ fs) : AllHold sp F n ρ (fs.filter p) :=
  fun f hf => h f (List.mem_of_mem_filter hf)

/-- **One non-jump instruction on the lock state is sound.** -/
theorem lstep_sound {i : Ninst} {σ σ' : LSt} {S rest : List B256} {a a' : List AVal}
    {ρt : B256}
    (reach : PP F n) (edge : Exec.Deriv.ParentStep n' n)
    (hfork : CoveredFork n.sevm.benvStat.fork) (hhash : HashAvoid sp.slot F)
    (hat : Ninst.At n.sevm.code n.pc i) (run : Ninst.Run n.sevm n.devm i n'.devm)
    (habs : absNinst i a = some a') (hfr : FrameMatches ρt a S)
    (hv : Val sp F n σ.kv σ.facts S) (hstack : n.devm.stack = S ++ rest)
    (hs : σ.setNow = true → lockAt F.sevm.currentTarget sp.slot n.devm = sp.locked)
    (hl : lstep sp n.pc i σ = some σ') :
    ∃ S', n'.devm.stack = S' ++ rest ∧ Val sp F n' σ'.kv σ'.facts S' ∧
      σ'.passed = σ.passed ∧ σ'.noMut = σ.noMut ∧
      (σ'.setNow = true → lockAt F.sevm.currentTarget sp.slot n'.devm = sp.locked) := by
  have hnn : PP n n' := .step edge (.refl _)
  have hsevm : n.sevm = F.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq reach
  obtain ⟨ρ, hS, hf⟩ := hv
  by_cases hpush : ∃ (bs : Bytes) (fits : bs.length ≤ 32), i = .push bs fits
  · obtain ⟨bs, fits, rfl⟩ := hpush
    simp only [lstep, Option.some.injEq] at hl
    subst hl
    have hr : freshSym σ.kv σ.facts ∉ σ.kv := fun h => Nat.lt_irrefl _ (lt_fresh_kv h)
    have hrf : ∀ f ∈ σ.facts, freshSym σ.kv σ.facts ∉ f.syms := fun f hm h =>
      Nat.lt_irrefl _ (lt_fresh_fact hm h)
    refine ⟨Bytes.toB256 bs :: S, by rw [push_run_stack run, hstack]; rfl, ?_, rfl, rfl, ?_⟩
    · refine ⟨Function.update ρ (freshSym σ.kv σ.facts) (Bytes.toB256 bs),
        .cons (by simp) (forall₂_update_of_not_mem hr hS), ?_⟩
      intro f hm
      rcases List.mem_cons.mp hm with rfl | hm
      · show _ ≤ (Function.update ρ _ _ _).toNat ∧ (Function.update ρ _ _ _).toNat ≤ _
        simp
      · exact Fact.holds_mono hnn (allHold_update hrf hf f hm)
    · intro hb
      rw [← hsevm, lockAt_edge edge hfork (noexec_of_ninst hat (fun _ h => by cases h))
        (fun h => by cases ninstAt_inj hat h)]
      rw [hsevm]
      exact hs hb
  · have hn : ∀ (bs : Bytes) (fits : bs.length ≤ 32), i ≠ .push bs fits :=
      fun bs fits he => hpush ⟨bs, fits, he⟩
    obtain ⟨out, kv', b, hout, hc, hm, hb, rfl⟩ := lstep_nonpush hn hl
    obtain ⟨hlen, -⟩ := absNinst_nonpush_spec hn habs
    have hlenk : σ.kv.length ≤ 1024 := by
      rw [List.Forall₂.length_eq hS, ← List.Forall₂.length_eq hfr]; exact hlen
    have hr : freshSym σ.kv σ.facts ∉ σ.kv := fun h => Nat.lt_irrefl _ (lt_fresh_kv h)
    have hrf : ∀ f ∈ σ.facts, freshSym σ.kv σ.facts ∉ f.syms := fun f hm h =>
      Nat.lt_irrefl _ (lt_fresh_fact hm h)
    obtain ⟨S', w, hst', hS'⟩ := transfer_val hfork hout hlenk hc hm hr hS hstack run
    refine ⟨S', hst', ⟨_, hS', ?_⟩, rfl, rfl,
      effSetNow_sound reach edge hfork hat run ⟨ρ, hS, hf⟩ hstack hs hb⟩
    apply allHold_filter
    apply allHold_append
    · by_cases hne : opFacts sp σ.facts σ.kv i (freshSym σ.kv σ.facts) = []
      · rw [hne]; intro f hf; cases hf
      · obtain ⟨o, rfl⟩ := opFacts_head hne hout
        rw [List.mapM_cons] at hm
        cases ho : o.mapM (fun l => match l with
            | none => some (freshSym σ.kv σ.facts) | some j => σ.kv[j.toNat]?) with
        | none => simp [ho] at hm
        | some kt =>
          simp only [ho, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at hm
          subst hm
          have htop : n'.devm.stack.head? = some w := by
            rw [hst']
            have := forall₂_update_head hS'
            cases S' with
            | nil => simp at this
            | cons x S' => simpa using this
          exact opFacts_sound hf hr hS hstack run reach edge htop (fun hi => by
            subst hi
            exact hhash n n' reach edge hat)
    · exact fun f hm => Fact.holds_mono hnn (allHold_update hrf hf f hm)

end Lstep

/-! ## Branches, joins, calls and returns -/

section Joins

variable {sp : Spec} {F n : Exec.Deriv}

theorem refineFacts_sound {ρ : Nat → B256} {fs : List Fact} {c : Nat} {zero : Bool}
    (hf : AllHold sp F n ρ fs) (hz : zero = true → ρ c = 0) (hnz : zero = false → ρ c ≠ 0) :
    AllHold sp F n ρ (refineFacts fs c zero) := by
  intro f hm0
  obtain ⟨g, hg, hm⟩ := List.mem_flatMap.mp hm0
  clear hm0
  have hgh := hf g hg
  have hlt := B256.toNat_lt
  cases g with
  | gt r s k =>
    simp only at hm
    split at hm
    · subst r
      simp only [Fact.Holds] at hgh
      cases zero
      · simp only [List.mem_singleton, Bool.false_eq_true, ite_false] at hm
        subst hm
        have := hgh.2 (hnz rfl)
        have := hlt (ρ s)
        exact ⟨by omega, by unfold maxW; omega⟩
      · simp only [List.mem_singleton, ite_true] at hm
        subst hm
        exact ⟨Nat.zero_le _, hgh.1 (hz rfl)⟩
    · cases hm
  | isz r s =>
    simp only at hm
    split at hm
    · subst r
      simp only [Fact.Holds] at hgh
      cases zero
      · simp only [List.mem_singleton, Bool.false_eq_true, ite_false] at hm
        subst hm
        have h0 := hgh.2 (hnz rfl)
        show 0 ≤ (ρ s).toNat ∧ (ρ s).toNat ≤ 0
        rw [h0]; exact ⟨Nat.le_refl _, by decide⟩
      · simp only [List.mem_singleton, ite_true] at hm
        subst hm
        have h0 := hgh.1 (hz rfl)
        have := hlt (ρ s)
        have hne : (ρ s).toNat ≠ 0 := fun h => h0 (B256.toNat_inj _ _ (by rw [h]; decide))
        exact ⟨by omega, by unfold maxW; omega⟩
    · cases hm
  | xor r s t =>
    simp only at hm
    split at hm
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
      obtain ⟨rfl, hzf⟩ := hc
      have hne := hgh (hnz hzf)
      have hne' : (ρ s).toNat ≠ (ρ t).toNat := fun h => hne (B256.toNat_inj _ _ h)
      rcases List.mem_append.mp hm with hm | hm
      · split at hm
        · rename_i he
          simp only [List.mem_singleton] at hm; subst hm
          have := entails_sound hf he
          show (ρ s).toNat < (ρ t).toNat
          simp only [Fact.Holds] at this; omega
        · cases hm
      · split at hm
        · rename_i he
          simp only [List.mem_singleton] at hm; subst hm
          have := entails_sound hf he
          show (ρ t).toNat < (ρ s).toNat
          simp only [Fact.Holds] at this; omega
        · cases hm
    · cases hm
  | _ => simp at hm

/-- The facts of a branch state hold on the branch taken. -/
theorem refine_sound {n' : Exec.Deriv} {σ : LSt} {d c : Nat} {kv : List Nat}
    {w0 w1 : B256} {S1 : List B256} {zero : Bool} (hnn : PP n n')
    (hv : Val sp F n (d :: c :: kv) σ.facts (w0 :: w1 :: S1))
    (hz : zero = true → w1 = 0) (hnz : zero = false → w1 ≠ 0) :
    Val sp F n' kv (refine σ c kv zero).facts S1 ∧
      ((refine σ c kv zero).passed = true → σ.passed = true ∨
        ∃ m, PP F m ∧ PP m n ∧ lockAt F.sevm.currentTarget sp.slot m.devm ≠ sp.locked) := by
  obtain ⟨ρ, hS, hf⟩ := hv
  cases hS with
  | cons h0 h1 =>
    cases h1 with
    | cons h1 hS1 =>
      subst h1
      refine ⟨⟨ρ, hS1, ?_⟩, ?_⟩
      · apply allHold_filter
        refine AllHold.mono hnn (allHold_append (refineFacts_sound hf hz hnz) hf)
      · intro hp
        simp only [refine, Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem] at hp
        rcases hp with hp | ⟨hz', hl⟩
        · exact Or.inl hp
        · exact Or.inr (hf _ hl (hz hz'))

theorem forall₂_symMap {ρ : Nat → B256} {g : Nat → Nat} :
    ∀ {A kv : List Nat} {S : List B256}, A.length = kv.length →
      (∀ p ∈ A.zip kv, g p.1 = p.2) → List.Forall₂ (fun s w => ρ s = w) kv S →
      List.Forall₂ (fun s w => (ρ ∘ g) s = w) A S
  | [], [], [], _, _, _ => .nil
  | a :: A, s :: kv, w :: S, hl, hz, .cons h0 hr =>
    .cons (by simp only [Function.comp]; rw [hz (a, s) List.mem_cons_self]; exact h0)
      (forall₂_symMap (by simpa using hl) (fun p hp => hz p (List.mem_cons_of_mem _ hp)) hr)
  | [], _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _ => by simp at hl

/-- An incoming state satisfying an annotation gives the annotation's meaning. -/
theorem compat_sound {σ A : LSt} {S : List B256} (hc : compat σ A = true)
    (hv : Val sp F n σ.kv σ.facts S) (hfl : Flags sp F σ n) :
    Val sp F n A.kv A.facts S ∧ Flags sp F A n := by
  simp only [compat, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨⟨hlen, hzip⟩, hp⟩, hs⟩, hm⟩, hfa⟩ := hc
  obtain ⟨ρ, hS, hf⟩ := hv
  refine ⟨⟨ρ ∘ symMap A.kv σ.kv, forall₂_symMap hlen.symm (fun p hp' => ?_) hS,
    fun f hf' => Fact.holds_rename (entails_sound hf (hfa f hf'))⟩, ?_, ?_, ?_⟩
  · have := hzip p hp'
    simpa using this
  · intro h; rcases hp with hp | hp
    · rw [h] at hp; cases hp
    · exact hfl.passed hp
  · intro h; rcases hs with hs | hs
    · rw [h] at hs; cases hs
    · exact hfl.setNow hs
  · intro h; rcases hm with hm | hm
    · rw [h] at hm; cases hm
    · exact hfl.noMut hm

/-- A resumed continuation: fresh symbols for the returned words above the
saved caller words. -/
theorem resume_val {σ : LSt} {S1 S' : List B256} {rets : Nat}
    (hv : Val sp F n σ.kv σ.facts S1) (hlen : S'.length = rets) :
    Val sp F n (resume σ rets).kv (resume σ rets).facts (S' ++ S1) := by
  obtain ⟨ρ, hS, hf⟩ := hv
  subst hlen
  let fr := freshSym σ.kv σ.facts
  let ρ' : Nat → B256 := fun s => if fr ≤ s then (S'[s - fr]?).getD 0 else ρ s
  have hold : ∀ s, s < fr → ρ' s = ρ s := fun s hs => by
    simp only [ρ']; rw [ite_eq_right_iff.mpr (fun h => by omega)]
  refine ⟨ρ', List.rel_append ?_ ?_, fun f hm => Fact.holds_congr
    (fun s hs => (hold s (lt_fresh_fact hm hs)).symm) (hf f hm)⟩
  · rw [List.forall₂_iff_get]
    refine ⟨by simp, fun i h1 h2 => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range, ρ']
    simp only [fr, Nat.le_add_right, ite_true, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem h2, Option.getD_some]
  · have : ∀ {kv : List Nat} {S : List B256}, (∀ s ∈ kv, s < fr) →
        List.Forall₂ (fun s w => ρ s = w) kv S → List.Forall₂ (fun s w => ρ' s = w) kv S := by
      intro kv S hk h
      induction h with
      | nil => exact .nil
      | cons h0 _ ih =>
        exact .cons (by rw [hold _ (hk _ List.mem_cons_self)]; exact h0)
          (ih (fun s hs => hk s (List.mem_cons_of_mem _ hs)))
    exact this (fun s hs => lt_fresh_kv hs) hS

theorem zip_mem_of_getElem? {α β : Type} :
    ∀ (l1 : List α) (l2 : List β) (k : Nat) (x : α) (y : β),
      l1[k]? = some x → l2[k]? = some y → (x, y) ∈ l1.zip l2
  | [], _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h
  | a :: l1, b :: l2, 0, x, y, h1, h2 => by
    simp at h1 h2; subst h1; subst h2; exact List.mem_cons_self
  | a :: l1, b :: l2, k + 1, x, y, h1, h2 =>
    List.mem_cons_of_mem _ (zip_mem_of_getElem? l1 l2 k x y (by simpa using h1)
      (by simpa using h2))

/-- Every entry tree is accepted from its annotation. -/
theorem lockCert_at {c : Cert} {ann : List LSt} (h : lockCert sp c ann = true) {k : Nat}
    {e : Entry} {g : SFunc} {A : LSt} (he : c.entries[k]? = some e)
    (hg : c.prog[k]? = some g) (hA : ann[k]? = some A) :
    lockNode sp c.entries ann e.pc e.frame A g = true := by
  simp only [lockCert, Bool.and_eq_true, List.all_eq_true] at h
  have hc : c[k]? = some (e, g) := by
    simp only [Cert.entries, Cert.prog, List.getElem?_map] at he hg
    cases hck : c[k]? with
    | none => simp [hck] at he
    | some p => simp [hck] at he hg; rw [← he, ← hg]
  exact h.2 _ (zip_mem_of_getElem? c ann k _ _ hc hA)

end Joins

/-! ## The invariant -/

section Invariant

variable (sp : Spec) (code : ByteArray) (c : Cert) (ann : List LSt) (F : Exec.Deriv)

/-- The pending continuations with their lock data: `ContsOK`'s segments, and
for every live continuation the saved lock state it resumes from, its
acceptance by the walk, the meaning of its words and of its `passed`. -/
inductive LConts (n : Exec.Deriv) : List Cont → List B256 → Prop
  | nil (base : List B256) : LConts n [] base
  | cons {k : Cont} {K : List Cont} {S rest : List B256} :
      FrameMatches (Cont.tagOf K) k.a S →
      RetOK k.a k.m K →
      (k.live = true →
        checkNode code c.entries k.m k.tag.toNat (List.replicate k.rets .unk ++ k.a) k.f = true) →
      (k.live = true → ∃ σk : LSt,
        lockNode sp c.entries ann k.tag.toNat (List.replicate k.rets .unk ++ k.a)
          (resume σk k.rets) k.f = true ∧
        Val sp F n σk.kv σk.facts S ∧
        (σk.passed = true → ∃ m, PP F m ∧ PP m n ∧
          lockAt F.sevm.currentTarget sp.slot m.devm ≠ sp.locked)) →
      LConts n K rest →
      LConts n (k :: K) (S ++ rest)

/-- The node `n` of the frame rooted at `F` sits at the checked cursor `κ`
with the accepted lock state `σ`. -/
structure LockOK (n : Exec.Deriv) (κ : Cursor) (σ : LSt) : Prop where
  reach : PP F n
  code_eq : n.sevm.code = code
  pc_eq : n.pc = κ.pc
  check : checkNode code c.entries κ.m κ.pc κ.a κ.f = true
  retOK : RetOK κ.a κ.m κ.K
  lock : lockNode sp c.entries ann κ.pc κ.a σ κ.f = true
  flags : Flags sp F σ n
  stack : ∃ S rest, n.devm.stack = S ++ rest ∧ FrameMatches (Cont.tagOf κ.K) κ.a S ∧
    Val sp F n σ.kv σ.facts S ∧ LConts sp code c ann F n κ.K rest

end Invariant

section InvariantLemmas

variable {sp : Spec} {code : ByteArray} {c : Cert} {ann : List LSt} {F : Exec.Deriv}

theorem LConts.mono {n n' : Exec.Deriv} (hnn : PP n n') :
    ∀ {K : List Cont} {rest : List B256}, LConts sp code c ann F n K rest →
      LConts sp code c ann F n' K rest
  | _, _, .nil base => .nil base
  | _, _, .cons h1 h2 h3 h4 h5 =>
    .cons h1 h2 h3 (fun hl => by
      obtain ⟨σk, hk1, hk2, hk3⟩ := h4 hl
      refine ⟨σk, hk1, hk2.mono hnn, fun hp => ?_⟩
      obtain ⟨m, a1, a2, a3⟩ := hk3 hp
      exact ⟨m, a1, a2.trans hnn, a3⟩) (LConts.mono hnn h5)

theorem LConts.contsOK {n : Exec.Deriv} :
    ∀ {K : List Cont} {rest : List B256}, LConts sp code c ann F n K rest →
      ContsOK code c.entries K rest
  | _, _, .nil base => .nil base
  | _, _, .cons h1 h2 h3 _ h5 => .cons h1 h2 h3 (LConts.contsOK h5)

theorem LockOK.cursorOK {n : Exec.Deriv} {κ : Cursor} {σ : LSt}
    (ok : LockOK sp code c ann F n κ σ) : CursorOK code c n κ := by
  obtain ⟨S, rest, h1, h2, -, h4⟩ := ok.stack
  exact ⟨ok.code_eq, ok.pc_eq, ok.check, ok.retOK, S, rest, h1, h2, h4.contsOK⟩

/-- The frame's root sits at entry `0` with the initial lock state. -/
theorem lock_start (hc : Cert.check code c = true) (hl : lockCert sp c ann = true)
    (hpc : F.pc = 0) (hcode : F.sevm.code = code) :
    LockOK sp code c ann F F (Cursor.start c) LSt.init := by
  have hcur := cursor_start hc hpc hcode
  cases c with
  | nil => simp [Cert.check] at hc
  | cons p c =>
    rcases p with ⟨e, f⟩
    have hc0 : Cert.check code ((e, f) :: c) = true := hc
    simp [Cert.check] at hc
    have hepc : e.pc = 0 := by simpa using hc.1.1
    have hef : e.frame = [] := by simpa using hc.1.2
    have hA : ann[0]? = some LSt.init := by
      simp only [lockCert, Bool.and_eq_true, beq_iff_eq] at hl; exact hl.1.2
    have hlock := lockCert_at hl (k := 0) (e := e) (g := f) (by simp [Cert.entries])
      (by simp [Cert.prog]) hA
    refine ⟨.refl _, hcur.code_eq, hcur.pc_eq, hcur.check, hcur.retOK, ?_, ?_, ?_⟩
    · simpa [Cursor.start, hepc, hef] using hlock
    · refine ⟨fun h => ?_, fun h => ?_, fun _ b h1 h2 hne => ?_⟩
      · cases h
      · cases h
      · exact (hne (Exec.Deriv.ParentPrefix.antisymm h2 h1)).elim
    · exact ⟨[], F.devm.stack, rfl, .nil, ⟨fun _ => 0, .nil, fun f hf => by
        simp [LSt.init] at hf⟩, .nil _⟩

end InvariantLemmas

end Blanc.Lift.LockCheck
