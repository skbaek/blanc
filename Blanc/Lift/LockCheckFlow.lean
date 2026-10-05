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
      have hm : n.pc ∉ sp.mutBodies := by simpa only [List.contains_eq_mem,
        decide_eq_true_eq] using hmut
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
    · simp only [effSetNow, hkv, reduceCtorEq] at he
    · simp only [effSetNow, hkv, reduceCtorEq] at he
    rw [hkv] at hS
    obtain ⟨St, hst⟩ : ∃ St, n.devm.stack = ρ k :: ρ v :: St := by
      cases hS with
      | cons h0 h1 =>
        cases h1 with
        | cons h1 _ => exact ⟨_, by rw [hstack, ← h0, ← h1]; rfl⟩
    have hset := sstore_getStor_set run (x := ρ k) (y := ρ v) (xs := St) ⟨[], by
      simp only [Split, hst, List.append_nil]⟩
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
  | none => simp only [ho, List.filter_append, Option.bind_eq_bind, Option.bind_none,
    reduceCtorEq] at h
  | some out =>
    by_cases hc : out.count none ≤ 1
    · cases hm : out.mapM (fun l => match l with
          | none => some (freshSym σ.kv σ.facts) | some j => σ.kv[j.toNat]?) with
      | none => simp only [ho, List.filter_append, Option.bind_eq_bind, Option.bind_some, hc,
        guard_true, Option.pure_def, hm, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at h
      | some kv' =>
        cases hb : effSetNow sp pc i σ with
        | none => simp only [ho, hb, List.filter_append, Option.bind_eq_bind, Option.bind_none,
          Option.bind_fun_none, reduceCtorEq] at h
        | some b =>
          simp only [ho, hc, hm, hb, Option.bind_eq_bind, Option.bind_some, guard,
            ite_true, Option.pure_def, Option.some.injEq] at h
          exact ⟨out, kv', b, rfl, hc, hm, rfl, h.symm⟩
    · simp only [ho, List.filter_append, Option.bind_eq_bind, Option.bind_some, hc, guard_false,
      Option.failure_eq_none, Option.bind_none, reduceCtorEq] at h

/-- The instructions with fact rules push their one computed result on top. -/
theorem opFacts_head {fs : List Fact} {kv : List Nat} {i : Ninst} {r : Nat} {p out : Pattern}
    (hne : opFacts sp fs kv i r ≠ []) (hout : ninstTransfer i p = some out) :
    ∃ o, out = none :: o := by
  cases i with
  | reg rr =>
    cases rr
    all_goals first
      | (exfalso; apply hne; simp only [opFacts, List.contains_eq_mem, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.cons_ne_self]; done)
      | skip
    all_goals
      simp only [ninstTransfer, liftRegularTransfer, regularTransfer, binaryTransfer,
        unaryTransfer] at hout
      split at hout <;> simp only [Option.some.injEq, reduceCtorEq] at hout
      exact ⟨_, hout.symm⟩
  | _ => exact (hne (by simp only [opFacts])).elim

theorem forall₂_update_head {ρ : Nat → B256} {r : Nat} {w : B256} {kv : List Nat}
    {S : List B256} (h : List.Forall₂ (fun s x => Function.update ρ r w s = x) (r :: kv) S) :
    S.head? = some w := by
  cases h with
  | cons h0 _ => simp only [← h0, Function.update_self, List.head?_cons]

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
        .cons (by simp only [Function.update_self]) (forall₂_update_of_not_mem hr hS), ?_⟩
      intro f hm
      rcases List.mem_cons.mp hm with rfl | hm
      · show _ ≤ (Function.update ρ _ _ _).toNat ∧ (Function.update ρ _ _ _).toNat ≤ _
        simp only [Function.update_self, Std.le_refl, and_self]
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
        | none => simp only [ho, Option.pure_def, Option.bind_eq_bind, Option.bind_none,
          Option.bind_fun_none, reduceCtorEq] at hm
        | some kt =>
          simp only [ho, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at hm
          subst hm
          have htop : n'.devm.stack.head? = some w := by
            rw [hst']
            have := forall₂_update_head hS'
            cases S' with
            | nil => simp only [List.head?_nil, reduceCtorEq] at this
            | cons x S' => simpa only [List.cons_append, List.head?_cons, Option.some.injEq] using
              this
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
  | _ => simp only [List.not_mem_nil] at hm

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
      (forall₂_symMap (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hl) (fun p hp => hz p (List.mem_cons_of_mem _ hp)) hr)
  | [], _ :: _, _, hl, _, _ => by simp only [List.length_nil, List.length_cons, Nat.right_eq_add,
    Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false] at hl
  | _ :: _, [], _, hl, _, _ => by simp only [List.length_cons, List.length_nil, Nat.add_eq_zero_iff,
    List.length_eq_zero_iff, one_ne_zero, and_false] at hl

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
    simpa only using this
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
    refine ⟨by simp only [List.length_map, List.length_range], fun i h1 h2 => ?_⟩
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
  | [], _, _, _, _, h, _ => by simp only [List.length_nil, not_lt_zero, not_false_eq_true,
    getElem?_neg, reduceCtorEq] at h
  | _ :: _, [], _, _, _, _, h => by simp only [List.length_nil, not_lt_zero, not_false_eq_true,
    getElem?_neg, reduceCtorEq] at h
  | a :: l1, b :: l2, 0, x, y, h1, h2 => by
    simp only [List.length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true,
      getElem?_pos, List.getElem_cons_zero, Option.some.injEq] at h1 h2; subst h1; subst h2; exact List.mem_cons_self
  | a :: l1, b :: l2, k + 1, x, y, h1, h2 =>
    List.mem_cons_of_mem _ (zip_mem_of_getElem? l1 l2 k x y (by simpa only [List.getElem?_cons_succ] using
      h1)
      (by simpa only [List.getElem?_cons_succ] using h2))

/-- Every entry tree is accepted from its annotation. -/
theorem lockCert_at {c : Cert} {ann : List LSt} (h : lockCert sp c ann = true) {k : Nat}
    {e : Entry} {g : SFunc} {A : LSt} (he : c.entries[k]? = some e)
    (hg : c.prog[k]? = some g) (hA : ann[k]? = some A) :
    lockNode sp c.entries ann e.pc e.frame A g = true := by
  simp only [lockCert, Bool.and_eq_true, List.all_eq_true] at h
  have hc : c[k]? = some (e, g) := by
    simp only [Cert.entries, Cert.prog, List.getElem?_map] at he hg
    cases hck : c[k]? with
    | none => simp only [hck, Option.map_none, reduceCtorEq] at he
    | some p => simp only [hck, Option.map_some, Option.some.injEq] at he hg; rw [← he, ← hg]
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
  | nil => simp only [Cert.check, List.all_nil, Bool.and_true, Bool.false_eq_true] at hc
  | cons p c =>
    rcases p with ⟨e, f⟩
    have hc0 : Cert.check code ((e, f) :: c) = true := hc
    simp only [Cert.check, List.beq_nil_eq, List.all_cons, Bool.and_eq_true, beq_iff_eq,
      List.isEmpty_iff, List.all_eq_true, Prod.forall] at hc
    have hepc : e.pc = 0 := by simpa only using hc.1.1
    have hef : e.frame = [] := by simpa only using hc.1.2
    have hA : ann[0]? = some LSt.init := by
      simp only [lockCert, Bool.and_eq_true, beq_iff_eq] at hl; exact hl.1.2
    have hlock := lockCert_at hl (k := 0) (e := e) (g := f) (by simp only [Cert.entries,
      List.map_cons, List.length_cons, List.length_map, lt_add_iff_pos_left, add_pos_iff,
      zero_lt_one, or_true, getElem?_pos, List.getElem_cons_zero])
      (by simp only [Cert.prog, List.map_cons, List.length_cons, List.length_map,
        lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos,
        List.getElem_cons_zero]) hA
    refine ⟨.refl _, hcur.code_eq, hcur.pc_eq, hcur.check, hcur.retOK, ?_, ?_, ?_⟩
    · simpa only [Cursor.start, hepc, hef] using hlock
    · refine ⟨fun h => ?_, fun h => ?_, fun _ b h1 h2 hne => ?_⟩
      · cases h
      · cases h
      · exact (hne (Exec.Deriv.ParentPrefix.antisymm h2 h1)).elim
    · exact ⟨[], F.devm.stack, rfl, .nil, ⟨fun _ => 0, .nil, fun f hf => by
        simp only [LSt.init, List.not_mem_nil] at hf⟩, .nil _⟩

end InvariantLemmas

/-! ## One same-frame edge -/

section Step

variable {sp : Spec} {code : ByteArray} {c : Cert} {ann : List LSt} {F : Exec.Deriv}

theorem jump_flags {n n' : Exec.Deriv} {σv σ' : LSt} {j : Jinst} (reach : PP F n)
    (edge : Exec.Deriv.ParentStep n' n) (hfork : CoveredFork n.sevm.benvStat.fork)
    (hat : Jinst.At n.sevm.code n.pc j) (hfl : FlagsV sp F σv n)
    (hp : σ'.passed = true → σv.passed = true ∨ ∃ m, PP F m ∧ PP m n ∧
      lockAt F.sevm.currentTarget sp.slot m.devm ≠ sp.locked)
    (hs : σ'.setNow = true → σv.setNow = true) (hm : σ'.noMut = true → σv.noMut = true) :
    Flags sp F σ' n' := by
  have hsevm : n.sevm = F.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq reach
  refine flags_succ reach edge hfl hp (fun h => ?_) hm
  rw [← hsevm, lockAt_edge edge hfork (noexec_of_jinst hat)
    (fun h' => (nostore_of_jinst hat h').elim), hsevm]
  exact hfl.setNow (hs h)

theorem val_pop_one {n : Exec.Deriv} {kv : List Nat} {fs : List Fact} {S rest : List B256}
    {d : Nat} {x : B256} {dv dv' : Devm} {av : AVal} {a : List AVal} {ρt : B256}
    (hv : Val sp F n (d :: kv) fs S) (hfr : FrameMatches ρt (av :: a) S)
    (hstack : dv.stack = S ++ rest) (pop : Devm.PopBurn [x] dv dv') :
    AVal.Matches ρt av x ∧ ∃ S1, dv'.stack = S1 ++ rest ∧ FrameMatches ρt a S1 ∧
      Val sp F n kv fs S1 := by
  obtain ⟨ρ, hS, hf⟩ := hv
  cases hfr with
  | @cons _ s0 _ S1 h0 htail =>
    cases hS with
    | cons _ hS1 =>
      have hp := popBurn_one_stack pop
      rw [hstack] at hp
      simp only [List.cons_append, List.cons.injEq] at hp
      obtain ⟨rfl, hs⟩ := hp
      exact ⟨h0, S1, hs.symm, htail, ρ, hS1, hf⟩

theorem frame_pop_two {S rest : List B256} {x y : B256} {dv dv' : Devm} {av bv : AVal}
    {a : List AVal} {ρt : B256} (hfr : FrameMatches ρt (av :: bv :: a) S)
    (hstack : dv.stack = S ++ rest) (pop : Devm.PopBurn [x, y] dv dv') :
    AVal.Matches ρt av x ∧ ∃ S1, S = x :: y :: S1 ∧ dv'.stack = S1 ++ rest ∧
      FrameMatches ρt a S1 := by
  cases hfr with
  | @cons _ s0 _ S0 h0 htail =>
    cases htail with
    | @cons _ s1 _ S1 h1 htail =>
      have hp := popBurn_two_stack pop
      rw [hstack] at hp
      simp only [List.cons_append, List.cons.injEq] at hp
      obtain ⟨rfl, rfl, hs⟩ := hp
      exact ⟨h0, S1, rfl, hs.symm, htail⟩

theorem val_take_drop {n : Exec.Deriv} {kv : List Nat} {fs : List Fact} {sf sr : List B256}
    {len : Nat} (hv : Val sp F n kv fs (sf ++ sr)) (hlen : sf.length = len) :
    Val sp F n (kv.take len) fs sf ∧ Val sp F n (kv.drop len) fs sr := by
  obtain ⟨ρ, hS, hf⟩ := hv
  refine ⟨⟨ρ, ?_, hf⟩, ⟨ρ, ?_, hf⟩⟩
  · have := List.forall₂_take len hS; rwa [List.take_left' hlen] at this
  · have := List.forall₂_drop len hS; rwa [List.drop_left' hlen] at this

/-- **One same-frame edge preserves the lock invariant.**  The case split is
`cursor_step`'s, so the synthetic step taken is the concrete one. -/
theorem lock_step (hc : Cert.check code c = true) (hl : lockCert sp c ann = true)
    (hhash : HashAvoid sp.slot F) {n n' : Exec.Deriv} {κ : Cursor} {σ : LSt}
    (ok : LockOK sp code c ann F n κ σ) (edge : Exec.Deriv.ParentStep n' n)
    (hfork : CoveredFork n.sevm.benvStat.fork) :
    ∃ κ' σ', LockOK sp code c ann F n' κ' σ' := by
  obtain ⟨reach, hcode, hpc, hcheck, hret, hlock, hfl, S, rest, hstack, hframe, hval, hK⟩ := ok
  obtain ⟨f, pc, a, m, K⟩ := κ
  dsimp only at hpc hcheck hret hlock hframe hK
  have hnn : PP n n' := .step edge (.refl _)
  have reach' : PP F n' := reach.trans hnn
  have hsevm : n.sevm = F.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq reach
  have hcode' : n'.sevm.code = code := by rw [Cursor.parentStep_sevm edge]; exact hcode
  have hK' := hK.mono hnn
  cases hvis : visit sp pc σ with
  | none => cases f <;> simp only [lockNode, hvis, Bool.false_eq_true, Option.isSome_none, Bool.false_and] at hlock
  | some σv =>
  obtain ⟨hFV, hkv, hfacts, hpass, hset, -, -⟩ :=
    visit_sound reach hfl (by rw [hpc]; exact hvis)
  have hvalv : Val sp F n σv.kv σv.facts S := by rw [hkv, hfacts]; exact hval
  cases f with
  | pcAt _ _ => simp only [lockNode, Bool.false_eq_true] at hlock
  | next i f =>
    simp only [checkNode, Bool.and_eq_true] at hcheck
    obtain ⟨⟨hbytes, _⟩, hrest⟩ := hcheck
    cases habs : absNinst i a with
    | none => simp only [habs, Bool.false_eq_true] at hrest
    | some a' =>
      simp only [habs] at hrest
      simp only [lockNode, hvis, habs] at hlock
      cases hls : lstep sp pc i σv with
      | none => simp only [hls, Bool.false_eq_true] at hlock
      | some σ' =>
        simp only [hls] at hlock
        have hat : Ninst.At n.sevm.code n.pc i := by
          rw [hcode, hpc]
          exact Ninst.at_of_slice (bytesAt_slice (ninst_bytes_ne_nil i) hbytes)
        obtain ⟨hpc', run⟩ := Cursor.parentStep_ninst edge hat
        obtain ⟨S', hst', hfr'⟩ := Cursor.absNinst_run_stack hfork habs hstack hframe run
        obtain ⟨S'', hst'', hv', hp', hm', hs'⟩ := lstep_sound reach edge hfork hhash hat run
          habs hframe hvalv hstack hFV.setNow (by rw [hpc]; exact hls)
        have hSS : S'' = S' := List.append_cancel_right (hst''.symm.trans hst')
        subst hSS
        refine ⟨⟨f, pc + i.size, a', m, K⟩, σ', reach', hcode', by simp only [hpc', hpc], hrest,
          fun hm => hret (Cursor.ret_mem_of_absNinst habs hm), hlock,
          flags_succ reach edge hFV (fun h => Or.inl (hp' ▸ h)) hs'
            (fun h => hm' ▸ h), S'', rest, hst', hfr', hv', hK'⟩
  | dest f =>
    have h' : byteAt code pc = some (Jinst.toUInt8 .jumpdest) ∧
        checkNode code c.entries m (pc + 1) a f = true := by
      simpa only [checkNode, Bool.and_eq_true, beq_iff_eq] using hcheck
    have hat : Jinst.At n.sevm.code n.pc .jumpdest := by
      rw [hcode, hpc]; exact byteAt_jinst_at h'.1
    obtain ⟨hpc', burn⟩ := of_jumpdest_run (Cursor.parentStep_jinst edge hat)
    simp only [lockNode, hvis] at hlock
    refine ⟨⟨f, pc + 1, a, m, K⟩, σv, reach', hcode', by simp only [hpc', hpc], h'.2, hret, hlock,
      jump_flags reach edge hfork hat hFV (fun h => Or.inl h) id id, S, rest, ?_, hframe,
      hvalv.mono hnn, hK'⟩
    rw [← burn.stack, hstack]
  | branch f g =>
    match a, hcheck, hret, hframe with
    | .const t :: v :: a', hcheck, hret, hframe =>
      have h' : (byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
            (v.jumps? = some true ∨ checkNode code c.entries m (pc + 1) a' f = true)) ∧
          (v.jumps? = some false ∨ checkNode code c.entries m t.toNat a' g = true) := by
        simpa only [checkNode, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] using hcheck
      have hat : Jinst.At n.sevm.code n.pc .jumpi := by
        rw [hcode, hpc]; exact byteAt_jinst_at h'.1.1
      have hret' : RetOK a' m K := fun hm =>
        hret (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))
      rcases hkvv : σv.kv with _ | ⟨d, _ | ⟨cc, kv⟩⟩
      · simp only [lockNode, hvis, hkvv, Bool.false_eq_true] at hlock
      · simp only [lockNode, hvis, hkvv, Bool.false_eq_true] at hlock
      simp only [lockNode, hvis, hkvv, Bool.and_eq_true] at hlock
      rw [hkvv] at hvalv
      rcases of_jumpi_run (Cursor.parentStep_jinst edge hat) with
        ⟨x, hpc', pop⟩ | ⟨x, y, hpc', pop, _, hy⟩
      · have hlive := live_fall (Cursor.pop_two_second hstack hframe pop) h'.1.2
        obtain ⟨_, S1, rfl, hst, hfr⟩ := frame_pop_two hframe hstack pop
        obtain ⟨hv1, hp1⟩ := refine_sound (zero := true) hnn hvalv (fun _ => rfl)
          (fun h => by cases h)
        exact ⟨⟨f, pc + 1, a', m, K⟩, _, reach', hcode', by simp only [hpc', hpc], hlive, hret',
          hlock.1, jump_flags reach edge hfork hat hFV hp1 id id, S1, rest, hst, hfr, hv1, hK'⟩
      · have hlive := live_taken hy (Cursor.pop_two_second hstack hframe pop) h'.2
        obtain ⟨hx, S1, rfl, hst, hfr⟩ := frame_pop_two hframe hstack pop
        have hx : x = t := hx
        subst hx
        obtain ⟨hv1, hp1⟩ := refine_sound (zero := false) hnn hvalv (fun h => by cases h)
          (fun _ => hy)
        exact ⟨⟨g, x.toNat, a', m, K⟩, _, reach', hcode', hpc', hlive, hret',
          hlock.2, jump_flags reach edge hfork hat hFV hp1 id id, S1, rest, hst, hfr, hv1, hK'⟩
    | [], hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | [.const _], hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .ret :: _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .unk :: _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | branchTo f k =>
    match a, hcheck, hret, hframe with
    | .const t :: v :: a', hcheck, hret, hframe =>
      cases hk : c.entries[k]? with
      | none => simp only [checkNode, hk, Bool.false_eq_true] at hcheck
      | some e =>
        have h' : (((byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
              e.pc = t.toNat) ∧ e.rets = m) ∧
              gotoCompat a' e.frame = true) ∧
              (v.jumps? = some true ∨ checkNode code c.entries m (pc + 1) a' f = true) := by
          simpa only [checkNode, hk, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] using hcheck
        have hat : Jinst.At n.sevm.code n.pc .jumpi := by
          rw [hcode, hpc]; exact byteAt_jinst_at h'.1.1.1.1
        have hret' : RetOK a' m K := fun hm =>
          hret (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))
        cases hA : ann[k]? with
        | none =>
          rcases hkvv : σv.kv with _ | ⟨d, _ | ⟨cc, kv⟩⟩ <;>
            simp only [lockNode, hvis, hkvv, hA, Bool.false_eq_true] at hlock
        | some A =>
        rcases hkvv : σv.kv with _ | ⟨d, _ | ⟨cc, kv⟩⟩
        · simp only [lockNode, hvis, hkvv, Bool.false_eq_true] at hlock
        · simp only [lockNode, hvis, hkvv, Bool.false_eq_true] at hlock
        simp only [lockNode, hvis, hkvv, hA, Bool.and_eq_true] at hlock
        rw [hkvv] at hvalv
        rcases of_jumpi_run (Cursor.parentStep_jinst edge hat) with
          ⟨x, hpc', pop⟩ | ⟨x, y, hpc', pop, _, hy⟩
        · have hlive := live_fall (Cursor.pop_two_second hstack hframe pop) h'.2
          obtain ⟨_, S1, rfl, hst, hfr⟩ := frame_pop_two hframe hstack pop
          obtain ⟨hv1, hp1⟩ := refine_sound (zero := true) hnn hvalv (fun _ => rfl)
            (fun h => by cases h)
          exact ⟨⟨f, pc + 1, a', m, K⟩, _, reach', hcode', by simp only [hpc', hpc], hlive, hret',
            hlock.1, jump_flags reach edge hfork hat hFV hp1 id id, S1, rest, hst, hfr, hv1,
            hK'⟩
        · obtain ⟨hx, S1, rfl, hst, hfr⟩ := frame_pop_two hframe hstack pop
          have hx : x = t := hx
          subst hx
          obtain ⟨hv1, hp1⟩ := refine_sound (zero := false) hnn hvalv (fun h => by cases h)
            (fun _ => hy)
          obtain ⟨hvA, hflA⟩ := compat_sound hlock.2 hv1
            (jump_flags reach edge hfork hat hFV hp1 id id)
          obtain ⟨g, hg⟩ := cert_prog_of_entry c k e hk
          refine ⟨⟨g, e.pc, e.frame, e.rets, K⟩, A, reach', hcode', by simp only [hpc',
            h'.1.1.1.2],
            cert_check_at hc k e g hk hg, ?_, lockCert_at hl hk hg hA, hflA, S1, rest, hst,
            frameMatches_gotoCompat h'.1.2 hfr, hvA, hK'⟩
          intro hm
          rw [h'.1.1.2]
          exact hret' (ret_mem_of_gotoCompat h'.1.2 hm)
    | [], hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | [.const _], hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .ret :: _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .unk :: _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | jump k =>
    match a, hcheck, hret, hframe with
    | .const t :: a', hcheck, hret, hframe =>
      cases hk : c.entries[k]? with
      | none => simp only [checkNode, hk, Bool.false_eq_true] at hcheck
      | some e =>
        have h' : (((byteAt code pc = some (Jinst.toUInt8 .jump) ∧
              e.pc = t.toNat) ∧ e.rets = m) ∧
              gotoCompat a' e.frame = true) := by
          simpa only [checkNode, hk, Bool.and_eq_true, beq_iff_eq] using hcheck
        have hat : Jinst.At n.sevm.code n.pc .jump := by
          rw [hcode, hpc]; exact byteAt_jinst_at h'.1.1.1
        cases hA : ann[k]? with
        | none =>
          rcases hkvv : σv.kv with _ | ⟨d, kv⟩ <;> simp only [lockNode, hvis, hkvv, hA,
            Bool.false_eq_true] at hlock
        | some A =>
        rcases hkvv : σv.kv with _ | ⟨d, kv⟩
        · simp only [lockNode, hvis, hkvv, Bool.false_eq_true] at hlock
        simp only [lockNode, hvis, hkvv, hA] at hlock
        rw [hkvv] at hvalv
        obtain ⟨x, hpc', pop, _⟩ := of_jump_run (Cursor.parentStep_jinst edge hat)
        obtain ⟨hx, S1, hst, hfr, hv1⟩ := val_pop_one hvalv hframe hstack pop
        have hx : x = t := hx
        subst hx
        obtain ⟨hvA, hflA⟩ := compat_sound hlock ((hv1.filter _).mono hnn)
          (jump_flags reach edge hfork hat hFV (fun h => Or.inl h) id id)
        obtain ⟨g, hg⟩ := cert_prog_of_entry c k e hk
        refine ⟨⟨g, e.pc, e.frame, e.rets, K⟩, A, reach', hcode', by simp only [hpc',
          h'.1.1.2],
          cert_check_at hc k e g hk hg, ?_, lockCert_at hl hk hg hA, hflA, S1, rest, hst,
          frameMatches_gotoCompat h'.2 hfr, hvA, hK'⟩
        intro hm
        rw [h'.1.2]
        exact hret (List.mem_cons_of_mem _ (ret_mem_of_gotoCompat h'.2 hm))
    | [], hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .ret :: _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .unk :: _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | callNext k f =>
    match a, f, hcheck, hret, hframe with
    | .const t :: a', .dest f0, hcheck, hret, hframe =>
      cases hk : c.entries[k]? with
      | none => simp only [checkNode, hk, Bool.false_eq_true] at hcheck
      | some e =>
        simp only [checkNode, hk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcheck
        obtain ⟨⟨⟨hbyte, hepc⟩, hlen⟩, hmatch⟩ := hcheck
        have hat : Jinst.At n.sevm.code n.pc .jump := by
          rw [hcode, hpc]; exact byteAt_jinst_at hbyte
        cases hA : ann[k]? with
        | none =>
          rcases hkvv : σv.kv with _ | ⟨d, kv⟩ <;> simp only [lockNode, hvis, hkvv, hk, hA,
            Bool.false_eq_true] at hlock
        | some A =>
        rcases hkvv : σv.kv with _ | ⟨d, kv⟩
        · simp only [lockNode, hvis, hkvv, Bool.false_eq_true] at hlock
        simp only [lockNode, hvis, hkvv, hk, hA, Bool.and_eq_true] at hlock
        obtain ⟨hcompat, hcont⟩ := hlock
        rw [hkvv] at hvalv
        obtain ⟨x, hpc', pop, _⟩ := of_jump_run (Cursor.parentStep_jinst edge hat)
        obtain ⟨hx, S0, hst, hfr, hv0⟩ := val_pop_one hvalv hframe hstack pop
        have hx : x = t := hx
        subst hx
        obtain ⟨g, hg⟩ := cert_prog_of_entry c k e hk
        have hentry := cert_check_at hc k e g hk hg
        have hretDrop : RetOK (a'.drop e.frame.length) m K := fun hm =>
          hret (List.mem_cons_of_mem _ (List.mem_of_mem_drop hm))
        have hflp : Flags sp F (popped σv (kv.take e.frame.length)) n' :=
          jump_flags reach edge hfork hat hFV (fun h => Or.inl h) id id
        have split_val : ∀ {sf sr : List B256} {ρt : B256}, S0 = sf ++ sr →
            FrameMatches ρt e.frame sf →
            Val sp F n' A.kv A.facts sf ∧ Flags sp F A n' ∧
              Val sp F n' (kv.drop e.frame.length) (σv.facts.filter
                (live (kv.drop e.frame.length))) sr := by
          intro sf sr ρt hS0 hsf
          rw [hS0] at hv0
          obtain ⟨vt, vd⟩ := val_take_drop hv0 (List.Forall₂.length_eq hsf).symm
          obtain ⟨hvA, hflA⟩ := compat_sound hcompat ((vt.filter _).mono hnn) hflp
          exact ⟨hvA, hflA, (vd.filter _).mono hnn⟩
        cases hi : e.frame.findIdx? (· == .ret) with
        | none =>
          simp only [hi] at hmatch
          obtain ⟨sf, sr, hS0, hsf, hsr⟩ := frameMatches_callCompat hmatch hfr
          obtain ⟨hvA, hflA, -⟩ := split_val hS0 hsf
          let κc : Cont := ⟨.dest f0, 0, a'.drop e.frame.length, m, e.rets, false⟩
          refine ⟨⟨g, e.pc, e.frame, e.rets, κc :: K⟩, A, reach', hcode',
            by simp only [hpc', hepc], hentry, ?_, lockCert_at hl hk hg hA, hflA, sf, sr ++ rest,
            by rw [hst, hS0, List.append_assoc], hsf, hvA,
            .cons hsr hretDrop (fun h => by cases h) (fun h => by cases h) hK'⟩
          intro hm
          exact (ret_not_mem_of_findIdx_none hi _ hm rfl).elim
        | some i =>
          simp only [hi] at hmatch hcont
          cases har : a'[i]? with
          | none => simp only [har, Bool.false_eq_true] at hmatch
          | some av =>
            cases av with
            | ret => simp only [har, Bool.false_eq_true] at hmatch
            | unk => simp only [har, Bool.false_eq_true] at hmatch
            | const r =>
              simp only [har, Bool.and_eq_true] at hmatch hcont
              obtain ⟨hcall, hcontc⟩ := hmatch
              obtain ⟨sf, sr, hS0, hsf, hsr⟩ := frameMatches_callCompat hcall hfr
              obtain ⟨hvA, hflA, hvd⟩ := split_val hS0 hsf
              let κc : Cont := ⟨.dest f0, r, a'.drop e.frame.length, m, e.rets, true⟩
              refine ⟨⟨g, e.pc, e.frame, e.rets, κc :: K⟩, A, reach', hcode',
                by simp only [hpc', hepc], hentry, fun _ => ⟨κc, K, rfl, rfl, rfl⟩,
                lockCert_at hl hk hg hA, hflA, sf, sr ++ rest,
                by rw [hst, hS0, List.append_assoc], hsf, hvA,
                .cons hsr hretDrop (fun _ => by
                  show checkNode code c.entries m r.toNat
                    (List.replicate e.rets .unk ++ a'.drop e.frame.length) (.dest f0) = true
                  simpa only [checkNode, Bool.and_eq_true, beq_iff_eq] using hcontc)
                  (fun _ => ⟨saved σv (kv.drop e.frame.length), hcont, hvd, fun hp => ?_⟩) hK'⟩
              obtain ⟨m0, a1, a2, a3⟩ := hFV.passed hp
              exact ⟨m0, a1, a2.trans hnn, a3⟩
    | [], _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .ret :: _, _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .unk :: _, _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .const _ :: _, .next _ _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .const _ :: _, .branch _ _, hcheck, _, _ => simp only [checkNode,
      Bool.false_eq_true] at hcheck
    | .const _ :: _, .branchTo _ _, hcheck, _, _ => simp only [checkNode,
      Bool.false_eq_true] at hcheck
    | .const _ :: _, .last _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .const _ :: _, .jump _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .const _ :: _, .callNext _ _, hcheck, _, _ => simp only [checkNode,
      Bool.false_eq_true] at hcheck
    | .const _ :: _, .ret, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .const _ :: _, .undefined, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | ret =>
    match a, hcheck, hret, hframe with
    | .ret :: a', hcheck, hret, hframe =>
      have h' : byteAt code pc = some (Jinst.toUInt8 .jump) ∧ a'.length = m := by
        simpa only [checkNode, Bool.and_eq_true, beq_iff_eq] using hcheck
      obtain ⟨k, K', rfl, hlive, hrets⟩ := hret List.mem_cons_self
      cases hK' with
      | @cons _ _ S1 rest1 hS1 hretk hchk hlk hK2 =>
        have hat : Jinst.At n.sevm.code n.pc .jump := by
          rw [hcode, hpc]; exact byteAt_jinst_at h'.1
        obtain ⟨x, hpc', pop, _⟩ := of_jump_run (Cursor.parentStep_jinst edge hat)
        obtain ⟨hx, S', hst, hfr⟩ := Cursor.pop_one_frame hstack hframe pop
        have hx : x = k.tag := hx
        subst hx
        have hlenS : S'.length = k.rets := by
          rw [← List.Forall₂.length_eq hfr, h'.2, hrets]
        obtain ⟨σk, hlk1, hlk2, hlk3⟩ := hlk hlive
        refine ⟨⟨k.f, k.tag.toNat, List.replicate k.rets .unk ++ k.a, k.m, K'⟩,
          resume σk k.rets, reach', hcode', hpc', hchk hlive, ?_, hlk1,
          ⟨fun h => hlk3 h, (fun h => by cases h), (fun h => by cases h)⟩, S' ++ S1, rest1,
          by rw [hst, List.append_assoc], ?_, resume_val hlk2 hlenS, hK2⟩
        · intro hm
          rcases List.mem_append.mp hm with hm | hm
          · simp only [List.mem_replicate, ne_eq, reduceCtorEq, and_false] at hm
          · exact hretk hm
        · rw [← hlenS]
          exact List.rel_append (frameMatches_unk_length S') hS1
    | [], hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .const _ :: _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .unk :: _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | last l =>
    have hbyte : byteAt code pc = some l.toUInt8 := by simpa only [checkNode, beq_iff_eq] using
      hcheck
    have hat : Linst.At n.sevm.code n.pc l := by
      rw [hcode, hpc]; exact byteAt_linst_at hbyte
    exact (Cursor.parentStep_false_of_linst edge hat).elim
  | undefined =>
    have hnone : n.sevm.code.getInst n.pc = none := by
      rw [hcode, hpc]; simpa only [checkNode, Option.isNone_iff_eq_none] using hcheck
    exact (Cursor.parentStep_false_of_none edge hnone).elim

end Step

/-! ## Along the whole frame -/

section Frame

variable {sp : Spec} {code : ByteArray} {c : Cert} {ann : List LSt} {F : Exec.Deriv}

/-- Every node of the same-frame chain of a frame entered at pc `0` of the
certified code carries the lock invariant. -/
theorem lock_of_parentPrefix (hc : Cert.check code c = true) (hl : lockCert sp c ann = true)
    (hpc : F.pc = 0) (hcode : F.sevm.code = code) (hfork : CoveredFork F.sevm.benvStat.fork)
    (hhash : HashAvoid sp.slot F) {n : Exec.Deriv} (hp : PP F n) :
    ∃ κ σ, LockOK sp code c ann F n κ σ := by
  suffices h : ∀ {r t : Exec.Deriv}, PP r t → ∀ κ σ, LockOK sp code c ann F r κ σ →
      ∃ κ' σ', LockOK sp code c ann F t κ' σ' from
    h hp _ _ (lock_start hc hl hpc hcode)
  intro r t hrt
  induction hrt with
  | refl => exact fun κ σ ok => ⟨κ, σ, ok⟩
  | step head _ ih =>
    intro κ σ ok
    obtain ⟨κ1, σ1, ok1⟩ := lock_step hc hl hhash ok head
      (by rw [Blanc.Exec.Deriv.ParentPrefix.sevm_eq ok.reach]; exact hfork)
    exact ih κ1 σ1 ok1

theorem LockOK.visit_some {n : Exec.Deriv} {κ : Cursor} {σ : LSt}
    (ok : LockOK sp code c ann F n κ σ) : ∃ σv, visit sp n.pc σ = some σv := by
  have hl := ok.lock
  rw [ok.pc_eq]
  obtain ⟨f, pc, a, m, K⟩ := κ
  dsimp only at hl ⊢
  cases hv : visit sp pc σ with
  | none => cases f <;> simp only [lockNode, hv, Bool.false_eq_true, Option.isSome_none, Bool.false_and] at hl
  | some σv => exact ⟨σv, rfl⟩

/-- A cursor-placed node that decodes an `SSTORE` sits at an `SSTORE` node of
the certificate. -/
theorem cursor_sstore_node {n : Exec.Deriv} {κ : Cursor} (ok : CursorOK code c n κ)
    (hat : Ninst.At n.sevm.code n.pc (.reg .sstore)) : ∃ g, κ.f = .next (.reg .sstore) g := by
  obtain ⟨hcode, hpc, hcheck, -, -⟩ := ok
  obtain ⟨f, pc, a, m, K⟩ := κ
  dsimp only at hpc hcheck ⊢
  rw [hcode, hpc] at hat
  have hjump : ∀ j : Jinst, byteAt code pc = some j.toUInt8 → False := fun j hb => by
    have hj := byteAt_jinst_at hb
    unfold Jinst.At at hj
    unfold Ninst.At at hat
    rw [hat] at hj
    cases hj
  cases f with
  | pcAt p g =>
    simp only [checkNode, Bool.and_eq_true] at hcheck
    have hi := Ninst.at_of_slice (bytesAt_slice (ninst_bytes_ne_nil (.reg .pc)) hcheck.1.1)
    unfold Ninst.At at hi hat
    rw [hat] at hi
    cases hi
  | next i g =>
    simp only [checkNode, Bool.and_eq_true] at hcheck
    have hi := Ninst.at_of_slice (bytesAt_slice (ninst_bytes_ne_nil i) hcheck.1.1)
    exact ⟨g, by rw [ninstAt_inj hi hat]⟩
  | last l =>
    have hl := byteAt_linst_at (show byteAt code pc = some l.toUInt8 by
      simpa only [checkNode, beq_iff_eq] using hcheck)
    unfold Linst.At at hl
    unfold Ninst.At at hat
    rw [hat] at hl
    cases hl
  | undefined =>
    have hnone : code.getInst pc = none := by
      simpa only [checkNode, Option.isNone_iff_eq_none] using hcheck
    unfold Ninst.At at hat
    rw [hat] at hnone
    cases hnone
  | dest g => exact (hjump _ (by simp only [checkNode, Bool.and_eq_true, beq_iff_eq] at hcheck; exact hcheck.1)).elim
  | branch g h =>
    simp only [checkNode] at hcheck
    split at hcheck
    · exact (hjump _ (by simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hcheck; exact hcheck.1.1)).elim
    · cases hcheck
  | branchTo g k =>
    simp only [checkNode] at hcheck
    split at hcheck
    · exact (hjump _ (by simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hcheck; exact hcheck.1.1.1.1)).elim
    · cases hcheck
  | jump k =>
    simp only [checkNode] at hcheck
    split at hcheck
    · exact (hjump _ (by simp only [Bool.and_eq_true, beq_iff_eq] at hcheck; exact hcheck.1.1.1)).elim
    · cases hcheck
  | callNext k g =>
    simp only [checkNode] at hcheck
    split at hcheck
    · exact (hjump _ (by simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcheck; exact hcheck.1.1.1)).elim
    · cases hcheck
  | ret =>
    simp only [checkNode] at hcheck
    split at hcheck
    · exact (hjump _ (by simp only [Bool.and_eq_true, beq_iff_eq] at hcheck; exact hcheck.1)).elim
    · cases hcheck

/-- At a slot-addressed `SSTORE` the walk had `passed`, and the pc is a
release pc or (before any mutating body start) a set pc. -/
theorem LockOK.sstore_site {n : Exec.Deriv} {κ : Cursor} {σ : LSt}
    (ok : LockOK sp code c ann F n κ σ) (hat : Ninst.At n.sevm.code n.pc (.reg .sstore))
    (hkey : n.devm.stack.head? = some sp.slot) :
    ∃ σv, visit sp n.pc σ = some σv ∧ σv.passed = true ∧
      (n.pc ∈ sp.releasePcs ∨ (σv.noMut = true ∧ n.pc ∈ sp.setPcs)) := by
  obtain ⟨g, hg⟩ := cursor_sstore_node ok.cursorOK hat
  obtain ⟨σv, hvis⟩ := ok.visit_some
  obtain ⟨-, hkv, hfacts, -, -, -, -⟩ := visit_sound ok.reach ok.flags hvis
  obtain ⟨S, rest, hstack, -, hval, -⟩ := ok.stack
  have hl := ok.lock
  rw [hg, ← ok.pc_eq] at hl
  simp only [lockNode, hvis] at hl
  cases hls : lstep sp n.pc (.reg .sstore) σv with
  | none => simp only [hls, reduceCtorEq, imp_self, implies_true, Bool.false_eq_true] at hl
  | some σ' =>
    obtain ⟨-, -, b, -, -, -, hb, -⟩ := lstep_nonpush (fun _ _ h => by cases h) hls
    obtain ⟨ρ, hS, hf⟩ := hval
    rw [← hkv] at hS
    rw [← hfacts] at hf
    rcases hkvv : σv.kv with _ | ⟨k, _ | ⟨v, kt⟩⟩
    · simp only [effSetNow, hkvv, reduceCtorEq] at hb
    · simp only [effSetNow, hkvv, reduceCtorEq] at hb
    rw [hkvv] at hS
    have hk : ρ k = sp.slot := by
      cases hS with
      | cons h0 _ =>
        rw [hstack, ← h0] at hkey
        simpa only [List.cons_append, List.head?_cons, Option.some.injEq] using hkey
    simp only [effSetNow, hkvv] at hb
    split at hb
    · rename_i hex
      exact (excluded_sound hf hex hk).elim
    · split at hb
      · rename_i hc'
        simp only [Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem] at hc'
        exact ⟨σv, hvis, hc'.1.2, hc'.2⟩
      · cases hb

/-- A reached node never executes `SELFDESTRUCT`. -/
theorem LockOK.not_selfdestruct {n : Exec.Deriv} {κ : Cursor} {σ : LSt}
    (ok : LockOK sp code c ann F n κ σ) : ¬ Linst.At n.sevm.code n.pc .selfdestruct := by
  intro hat
  have hl := ok.lock
  have hcheck := ok.check
  have hcode := ok.code_eq
  have hpc := ok.pc_eq
  obtain ⟨f, pc, a, m, K⟩ := κ
  dsimp only at hl hcheck hpc
  rw [hcode, hpc] at hat
  have hjump : ∀ j : Jinst, byteAt code pc = some j.toUInt8 → False := fun j hb => by
    have hj := byteAt_jinst_at hb
    unfold Jinst.At at hj
    unfold Linst.At at hat
    rw [hat] at hj
    cases hj
  cases f with
  | pcAt _ _ => simp only [lockNode, Bool.false_eq_true] at hl
  | last l =>
    have hl' := byteAt_linst_at (show byteAt code pc = some l.toUInt8 by
      simpa only [checkNode, beq_iff_eq] using hcheck)
    unfold Linst.At at hl' hat
    rw [hat] at hl'
    cases hl'
    simp only [lockNode, bne_self_eq_false, Bool.and_false, Bool.false_eq_true] at hl
  | next i g =>
    simp only [checkNode, Bool.and_eq_true] at hcheck
    have hi := Ninst.at_of_slice (bytesAt_slice (ninst_bytes_ne_nil i) hcheck.1.1)
    unfold Ninst.At at hi
    unfold Linst.At at hat
    rw [hat] at hi
    cases hi
  | undefined =>
    have hnone : code.getInst pc = none := by
      simpa only [checkNode, Option.isNone_iff_eq_none] using hcheck
    unfold Linst.At at hat
    rw [hat] at hnone
    cases hnone
  | dest g => exact (hjump _ (by simp only [checkNode, Bool.and_eq_true, beq_iff_eq] at hcheck; exact hcheck.1)).elim
  | branch g h =>
    simp only [checkNode] at hcheck
    split at hcheck
    · exact (hjump _ (by simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hcheck; exact hcheck.1.1)).elim
    · cases hcheck
  | branchTo g k =>
    simp only [checkNode] at hcheck
    split at hcheck
    · exact (hjump _ (by simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hcheck; exact hcheck.1.1.1.1)).elim
    · cases hcheck
  | jump k =>
    simp only [checkNode] at hcheck
    split at hcheck
    · exact (hjump _ (by simp only [Bool.and_eq_true, beq_iff_eq] at hcheck; exact hcheck.1.1.1)).elim
    · cases hcheck
  | callNext k g =>
    simp only [checkNode] at hcheck
    split at hcheck
    · exact (hjump _ (by simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcheck; exact hcheck.1.1.1)).elim
    · cases hcheck
  | ret =>
    simp only [checkNode] at hcheck
    split at hcheck
    · exact (hjump _ (by simp only [Bool.and_eq_true, beq_iff_eq] at hcheck; exact hcheck.1)).elim
    · cases hcheck

end Frame

/-! ## The dominance theorems -/

/-- The lock a checker specification describes, over the certified code. -/
def Spec.lockSpec (sp : Spec) (code : ByteArray) : LockSpec :=
  ⟨code, sp.slot, sp.locked, sp.bodies, sp.mutBodies⟩

section Dominance

variable {sp : Spec} {code : ByteArray} {c : Cert} {ann : List LSt}

/-- **`LockCheck.dominance`.**  For any certificate `c` of `code`
(`Cert.check`) that the lock checker accepts with some annotation
(`lockCert`), the lock `sp` meets `LockSpec.Dominance` over `code`: in every
frame running `code` from pc `0` on a covered fork whose executed hashes avoid
the slot, every body start and every slot-addressed `SSTORE` is preceded in
its frame by a node where the lock cell did not hold `locked`, and every
mutating body start holds `locked` — whatever the frame's outcome. -/
theorem dominance (hc : Cert.check code c = true) (hl : lockCert sp c ann = true) :
    (sp.lockSpec code).Dominance := by
  intro F hpc hfork hcode hhash n hp
  obtain ⟨κ, σ, ok⟩ := lock_of_parentPrefix hc hl hpc hcode hfork hhash hp
  obtain ⟨σv, hvis⟩ := ok.visit_some
  obtain ⟨hFV, -, -, -, -, hbody, hmut⟩ := visit_sound ok.reach ok.flags hvis
  refine ⟨fun h => ?_, hmut⟩
  rcases h with h | ⟨hat, hkey⟩
  · exact hbody h
  · obtain ⟨σv', hvis', hpass, -⟩ := ok.sstore_site hat hkey
    rw [hvis] at hvis'
    cases hvis'
    exact hFV.passed hpass

/-- **Strong form.**  Under the premises of `dominance`, once a frame has
reached a mutating body start, every later (or the same) node that executes a
slot-addressed `SSTORE` sits at a release pc. -/
theorem dominance_strong (hc : Cert.check code c = true) (hl : lockCert sp c ann = true)
    {F : Exec.Deriv} (hpc : F.pc = 0) (hfork : CoveredFork F.sevm.benvStat.fork)
    (hcode : F.sevm.code = code) (hhash : HashAvoid sp.slot F)
    {b n : Exec.Deriv} (hb : PP F b) (hbn : PP b n) (hmb : b.pc ∈ sp.mutBodies)
    (hst : SstoreAt n sp.slot) : n.pc ∈ sp.releasePcs := by
  obtain ⟨κ, σ, ok⟩ := lock_of_parentPrefix hc hl hpc hcode hfork hhash (hb.trans hbn)
  obtain ⟨σv, hvis, -, hpc'⟩ := ok.sstore_site hst.1 hst.2
  obtain ⟨hFV, -⟩ := visit_sound ok.reach ok.flags hvis
  rcases hpc' with h | ⟨hnm, -⟩
  · exact h
  · exact (hFV.noMut hnm b hb hbn hmb).elim

/-- **No forbidden opcode.**  Under the premises of `dominance`, no node of
the frame executes `DELEGATECALL`, `CALLCODE`, `CREATE`, `CREATE2` (the only
frame-spawning instructions are `CALL` and `STATICCALL`) or `SELFDESTRUCT`. -/
theorem no_forbidden (hc : Cert.check code c = true) (hl : lockCert sp c ann = true)
    {F : Exec.Deriv} (hpc : F.pc = 0) (hfork : CoveredFork F.sevm.benvStat.fork)
    (hcode : F.sevm.code = code) (hhash : HashAvoid sp.slot F)
    {n : Exec.Deriv} (hp : PP F n) :
    (∀ x, Ninst.At n.sevm.code n.pc (.exec x) → x = .call ∨ x = .staticcall) ∧
      ¬ Linst.At n.sevm.code n.pc .selfdestruct := by
  obtain ⟨κ, σ, ok⟩ := lock_of_parentPrefix hc hl hpc hcode hfork hhash hp
  exact ⟨fun x hat => ok.cursorOK.exec_call_or_staticcall hat, ok.not_selfdestruct⟩

end Dominance

end Blanc.Lift.LockCheck
