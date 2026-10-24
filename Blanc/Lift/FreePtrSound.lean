import Blanc.Lift.FreePtrSoundStep
import Blanc.Lift.NodeRet

/-!
# Soundness of the free-pointer checker (F3c)

Goal `usdc-neversigner-freepointer-v1`, design `fp-checker.md` §1 point 8, frozen statements
Appendix A §F3 (`FpGood`, `FpObs`, `FpStep` are in `Blanc/Lift/FreePtrSoundStep.lean`):

* `fpRun_sound`: every run of an accepted certificate's entry `0`, under a step relation that
  records the potential, reads a good free pointer at every free-pointer `MLOAD`;
* `lift_sound_fp`: the walk-facing form, from `Cert.check` and a successful frame
  (`lift_sound_in`, `SFunc.RunP.withPot`, then `fpRun_sound`).

The proof is a big-step induction on `SFunc.RunP` (`fp_run`): the checker state describes the
machine (`FpInv`) above an untouched base, steps go through `fstep_sound`, branch arms through
`refineFacts_sound`, gotos and calls through `compat_sound`, and call continuations through
`resume_sound`.  A `callNext` whose callee frame holds no return marker leaves its continuation
unchecked; such a callee never returns (`SFunc.RunP.not_returned_of_noRet`, decision
`ns-node-ret-guard`).  Bytes-free and contract-neutral.
-/

namespace Blanc.Lift.FreePtr

open Jaune AbstractStackSafety Blanc.Lift.SymTransfer

/-! ## The certificate's entries -/

theorem cert_at {c : Cert} {k : Nat} {e : Entry} {g : SFunc} (he : c.entries[k]? = some e)
    (hg : c.prog[k]? = some g) : c[k]? = some (e, g) := by
  simp only [Cert.entries, Cert.prog, List.getElem?_map] at he hg
  cases h : c[k]? with
  | none => rw [h] at he; cases he
  | some p =>
    rw [h] at he hg
    cases he
    cases hg
    rfl

theorem fpCert_at {c : Cert} {ann : List Ann} (hf : fpCert c ann = true) {k : Nat} {e : Entry}
    {g : SFunc} (hk : c[k]? = some (e, g)) :
    ∃ A, ann[k]? = some A ∧ fpNode c.entries ann A.ret e.frame A.entry g = true := by
  simp only [fpCert, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hf
  obtain ⟨⟨hlen, -⟩, hall⟩ := hf
  have hkc : k < c.length := (List.getElem?_eq_some_iff.mp hk).1
  have hka : k < ann.length := hlen ▸ hkc
  refine ⟨ann[k], List.getElem?_eq_getElem hka, ?_⟩
  have hmem : ((e, g), ann[k]) ∈ c.zip ann := by
    rw [List.mem_iff_getElem?]
    refine ⟨k, ?_⟩
    rw [List.getElem?_zip_eq_some]
    exact ⟨hk, List.getElem?_eq_getElem hka⟩
  exact hall _ hmem

/-! ## Inverting the walk's arms -/

section Inv

variable {es : List Entry} {ann : List Ann} {R σ : FSt} {a : List AVal}

theorem fpNode_branch_inv {f g : SFunc} (h : fpNode es ann R a σ (.branch f g) = true) :
    ∃ x y a' x' c kv, a = x :: y :: a' ∧ σ.kv = x' :: c :: kv ∧
      fpNode es ann R a' (refine σ c kv true) f = true ∧
      fpNode es ann R a' (refine σ c kv false) g = true := by
  simp only [fpNode] at h
  split at h
  · simp only [Bool.and_eq_true] at h
    exact ⟨_, _, _, _, _, _, rfl, ‹_›, h.1, h.2⟩
  · cases h

theorem fpNode_branchTo_inv {f : SFunc} {k : Nat}
    (h : fpNode es ann R a σ (.branchTo f k) = true) :
    ∃ x y a' x' c kv e A, a = x :: y :: a' ∧ σ.kv = x' :: c :: kv ∧ es[k]? = some e ∧
      ann[k]? = some A ∧ gotoCompat a' e.frame = true ∧
      fpNode es ann R a' (refine σ c kv true) f = true ∧
      compat (refine σ c kv false) A.entry = true ∧ A.ret = R := by
  simp only [fpNode] at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨_, _, _, _, _, _, _, _, rfl, ‹_›, ‹_›, ‹_›, h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · cases h

theorem fpNode_jump_inv {k : Nat} (h : fpNode es ann R a σ (.jump k) = true) :
    ∃ x a' x' kv e A, a = x :: a' ∧ σ.kv = x' :: kv ∧ es[k]? = some e ∧ ann[k]? = some A ∧
      gotoCompat a' e.frame = true ∧ compat (popped σ kv) A.entry = true ∧ A.ret = R := by
  simp only [fpNode] at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨_, _, _, _, _, _, rfl, ‹_›, ‹_›, ‹_›, h.1.1, h.1.2, h.2⟩
  · cases h

theorem fpNode_ret_inv (h : fpNode es ann R a σ .ret = true) :
    ∃ a' x' kv, a = .ret :: a' ∧ σ.kv = x' :: kv ∧ compat (popped σ kv) R = true := by
  simp only [fpNode] at h
  split at h
  · exact ⟨_, _, _, rfl, ‹_›, h⟩
  · cases h

theorem fpNode_next_inv {n : Ninst} {f : SFunc} (h : fpNode es ann R a σ (.next n f) = true) :
    ∃ a' σ', absNinst n a = some a' ∧ fstep n σ = some σ' ∧ fpNode es ann R a' σ' f = true := by
  simp only [fpNode] at h
  split at h
  · exact ⟨_, _, ‹_›, ‹_›, h⟩
  · cases h

theorem fpNode_callNext_inv {k : Nat} {f : SFunc}
    (h : fpNode es ann R a σ (.callNext k f) = true) :
    ∃ t a' x' kv e A, a = .const t :: a' ∧ σ.kv = x' :: kv ∧ es[k]? = some e ∧
      ann[k]? = some A ∧ compat (popped σ (kv.take e.frame.length)) A.entry = true ∧
      A.ret.kv.length = e.rets ∧
      ∀ i, e.frame.findIdx? (· == .ret) = some i →
        fpNode es ann R (List.replicate e.rets .unk ++ a'.drop e.frame.length)
          (resume σ (kv.drop e.frame.length) A.ret) f = true := by
  simp only [fpNode] at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨_, _, _, _, _, _, rfl, ‹_›, ‹_›, ‹_›, h.1.1, h.1.2, fun i hi => ?_⟩
    have h2 := h.2
    rw [hi] at h2
    simp only at h2
    split at h2
    · exact h2
    · cases h2
  · cases h

end Inv

/-- The free-pointer walk has `checkNode`'s return discipline. -/
theorem fpNode_retClosed {c : Cert} {ann : List Ann} (hf : fpCert c ann = true) :
    RetClosed c.entries c.prog (fun a f => ∃ R σ, fpNode c.entries ann R a σ f = true) where
  entry he hg := by
    obtain ⟨A, -, h⟩ := fpCert_at hf (cert_at he hg)
    exact ⟨_, _, h⟩
  next := by
    rintro a n f ⟨R, σ, h⟩
    obtain ⟨a', σ', ha, -, h⟩ := fpNode_next_inv h
    exact ⟨a', ha, R, σ', h⟩
  dest := by
    rintro a f ⟨R, σ, h⟩
    exact ⟨R, σ, h⟩
  branch := by
    rintro a f g ⟨R, σ, h⟩
    obtain ⟨x, y, a', -, c, kv, rfl, -, h1, h2⟩ := fpNode_branch_inv h
    exact ⟨x, y, a', rfl, ⟨R, _, h1⟩, ⟨R, _, h2⟩⟩
  branchTo := by
    rintro a f k ⟨R, σ, h⟩
    obtain ⟨x, y, a', -, c, kv, e, A, rfl, -, he, -, hg, h1, -⟩ := fpNode_branchTo_inv h
    exact ⟨x, y, a', e, rfl, he, hg, R, _, h1⟩
  jump := by
    rintro a k ⟨R, σ, h⟩
    obtain ⟨x, a', -, kv, e, A, rfl, -, he, -, hg, -⟩ := fpNode_jump_inv h
    exact ⟨x, a', e, rfl, he, hg⟩
  callNext := by
    rintro a k f ⟨R, σ, h⟩
    obtain ⟨t, a', -, kv, e, A, rfl, -, he, -, -, -, hk⟩ := fpNode_callNext_inv h
    exact ⟨_, a', e, rfl, he, fun i hi => ⟨R, _, hk i hi⟩⟩
  ret := by
    rintro a ⟨R, σ, h⟩
    obtain ⟨a', -, -, rfl, -⟩ := fpNode_ret_inv h
    exact ⟨a', rfl⟩
  pcAt := by
    rintro a p f ⟨R, σ, h⟩
    simp only [fpNode] at h
    cases h

/-! ## The invariant across the jump rules -/

theorem gotoCompat_length : ∀ {a e : List AVal}, gotoCompat a e = true → a.length = e.length
  | [], [], _ => rfl
  | x :: a, y :: e, h => by
    cases x <;> cases y <;>
      simp only [gotoCompat, Bool.and_eq_true, Bool.false_eq_true] at h <;>
      first
        | simp only [List.length_cons, gotoCompat_length h]
        | simp only [List.length_cons, gotoCompat_length h.2]
  | [], _ :: _, h => by simp only [gotoCompat, Bool.false_eq_true] at h
  | _ :: _, [], h => by simp only [gotoCompat, Bool.false_eq_true] at h

theorem compat_length {σ A : FSt} (h : compat σ A = true) : σ.kv.length = A.kv.length := by
  unfold compat at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1

/-- An annotation's return-data fact is one the incoming state holds. -/
theorem compat_rds {σ A : FSt} (hc : compat σ A = true) {h : Nat}
    (hm : Fact.rdsLe h ∈ A.facts) : Fact.rdsLe h ∈ σ.facts := by
  unfold compat at hc
  simp only [Bool.and_eq_true, List.all_eq_true] at hc
  have := hc.2 _ hm
  simp only [Fact.rename, entails, List.contains_iff_mem] at this
  exact this

/-- An accepted join carries the invariant to the annotation, under the renamed valuation. -/
theorem FpInv.compat {ν : Nat → B256} {σ A : FSt} {d : Devm} {rest : List B256}
    (hc : compat σ A = true) (inv : FpInv ν σ d rest) : FpInv (ν ∘ symMap A σ) A d rest := by
  obtain ⟨S, hst, hS, hf, hw, hrd⟩ := inv
  obtain ⟨hA, hAf, hfp⟩ := compat_sound hc hS hf
  refine ⟨S, hst, hA, hAf, fun a ha => ?_, fun h hm => hrd h (compat_rds hc hm)⟩
  obtain ⟨s, hs, he⟩ := hfp a ha
  rw [he]
  exact hw s hs

private theorem forall₂_split {ν : Nat → B256} :
    ∀ {ks kv : List Nat} {S : List B256}, List.Forall₂ (fun s w => ν s = w) (ks ++ kv) S →
      ∃ S1 S2, S = S1 ++ S2 ∧ List.Forall₂ (fun s w => ν s = w) ks S1 ∧
        List.Forall₂ (fun s w => ν s = w) kv S2
  | [], _, S, h => ⟨[], S, rfl, .nil, h⟩
  | _ :: _, _, _ :: _, .cons h0 h => by
    obtain ⟨S1, S2, e, h1, h2⟩ := forall₂_split h
    exact ⟨_ :: S1, S2, by rw [e]; rfl, .cons h0 h1, h2⟩

/-- A call continuation starts with no return-data fact: the callee may have changed it. -/
theorem resume_rds {σ R : FSt} {below : List Nat} {h : Nat} :
    Fact.rdsLe h ∉ (resume σ below R).facts := by
  intro hm
  have := (List.mem_filter.mp (closeLive_sub hm)).2
  simp only [Fact.isRds, Bool.not_true, Bool.false_eq_true] at this

/-- Popping words the checker frame names: the popped words are the named ones, and the rest of
the frame names the words above the base. -/
theorem FpInv.pop_raw {ν : Nat → B256} {σ : FSt} {d d' : Devm} {rest : List B256}
    {xs : List B256} {ks kv : List Nat} (hkv : σ.kv = ks ++ kv) (hlen : ks.length = xs.length)
    (pop : Devm.PopBurn xs d d') (inv : FpInv ν σ d rest) :
    List.Forall₂ (fun s w => ν s = w) ks xs ∧ ∃ S2, d'.stack = S2 ++ rest ∧
      List.Forall₂ (fun s w => ν s = w) kv S2 ∧ AllHold ν σ.facts ∧ FpWord ν σ.fp d'.memory ∧
      ∀ h, Fact.rdsLe h ∈ σ.facts → d'.returnData.length ≤ h := by
  obtain ⟨S, hst, hS, hf, hw, hrd⟩ := inv
  rw [hkv] at hS
  obtain ⟨S1, S2, rfl, hS1, hS2⟩ := forall₂_split hS
  have hl1 : S1.length = xs.length := (List.Forall₂.length_eq hS1).symm.trans hlen
  have hps : d.stack = xs ++ d'.stack := pop.stack
  rw [hst, List.append_assoc] at hps
  obtain ⟨rfl, hd'⟩ := List.append_inj hps hl1
  refine ⟨hS1, S2, hd'.symm, hS2, hf, ?_, ?_⟩
  · rw [← pop.memory]
    exact hw
  · rw [← pop.returnData]
    exact hrd

theorem FpInv.pop {ν : Nat → B256} {σ : FSt} {d d' : Devm} {rest : List B256} {x' : Nat}
    {kv : List Nat} {dw : B256} (hkv : σ.kv = x' :: kv) (pop : Devm.PopBurn [dw] d d')
    (inv : FpInv ν σ d rest) : FpInv ν (popped σ kv) d' rest := by
  obtain ⟨-, S2, hst, hS, hf, hw, hrd⟩ := inv.pop_raw (ks := [x']) (by rw [hkv]; rfl) rfl pop
  exact ⟨S2, hst, hS, AllHold.closeLive _ _ hf, hw, fun h hm => hrd h (closeLive_sub hm)⟩

theorem FpWord.shift {ν' μ : Nat → B256} {base : Nat} {x fp : Option Nat} {m : Mem}
    (hx : x = fp.map (base + ·)) (hhigh : ∀ s, ν' (base + s) = μ s) (hw : FpWord μ fp m) :
    FpWord ν' x m := by
  subst hx
  intro s hs
  obtain ⟨s0, hs0, rfl⟩ := Option.map_eq_some_iff.mp hs
  rw [hhigh]
  exact hw s0 hs0

theorem FpInv.burn {ν : Nat → B256} {σ : FSt} {d d' : Devm} {rest : List B256}
    (burn : Devm.Burn d d') (inv : FpInv ν σ d rest) : FpInv ν σ d' rest := by
  obtain ⟨S, hst, hS, hf, hw, hrd⟩ := inv
  refine ⟨S, ?_, hS, hf, ?_, ?_⟩
  · rw [← burn.stack]; exact hst
  · rw [← burn.memory]; exact hw
  · rw [← burn.returnData]; exact hrd

/-- A branch arm: the popped condition word decides what the arm learns. -/
theorem FpInv.refine {ν : Nat → B256} {σ : FSt} {d d' : Devm} {rest : List B256}
    {x c : Nat} {kv : List Nat} {dw w : B256} {zero : Bool} (hkv : σ.kv = x :: c :: kv)
    (pop : Devm.PopBurn [dw, w] d d') (hz : zero = true → w = 0) (hnz : zero = false → w ≠ 0)
    (inv : FpInv ν σ d rest) : FpInv ν (FreePtr.refine σ c kv zero) d' rest := by
  obtain ⟨hk, S2, hst, hS, hf, hw, hrd⟩ := inv.pop_raw (ks := [x, c]) (by rw [hkv]; rfl) rfl pop
  have hc : ν c = w := by
    cases hk with
    | cons _ h => cases h with
      | cons h _ => exact h
  exact ⟨S2, hst, hS, AllHold.closeLive _ _ (refineFacts_sound hf (fun h => hc.trans (hz h))
    (fun h => hc ▸ hnz h)), hw,
    fun h hm => hrd h (rdsLe_mem_refineFacts (closeLive_sub hm))⟩

/-! ## The big-step induction -/

/-- **The recursion.**  A run of a tree the walk accepts, from a machine the walk's state
describes, is a run under `FpStep`; if it returns, the current function's summary `R`
describes the result above the same untouched base. -/
theorem fp_run_noStateGas {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d' ∧ Pot d ∧ Pot d')
    {c : Cert} {ann : List Ann} (hf : fpCert c ann = true)
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none) {d : Devm} {f : SFunc} {o : Outcome}
    (run : SFunc.RunP P c.prog sevm d f o) :
    ∀ {a : List AVal} {σ R : FSt} {ν : Nat → B256} {rest : List B256},
      fpNode c.entries ann R a σ f = true → σ.kv.length ≤ a.length → FpInv ν σ d rest →
      SFunc.RunP (FpStep P) c.prog sevm d f o ∧
        ∀ d'', o = .returned d'' → ∃ μ, FpInv μ R d'' rest := by
  induction run with
  | zero dw pop _ ih =>
    intro a σ R ν rest hn hlen inv
    obtain ⟨x, y, a', x', c', kv, rfl, hkv, h1, -⟩ := fpNode_branch_inv hn
    have hl : kv.length ≤ a'.length := by
      rw [hkv] at hlen; simp only [List.length_cons] at hlen; omega
    obtain ⟨r1, r2⟩ := ih h1 hl (inv.refine hkv pop (fun _ => rfl) (fun h => by cases h))
    exact ⟨.zero dw pop r1, r2⟩
  | succ dw w hw pop _ ih =>
    intro a σ R ν rest hn hlen inv
    obtain ⟨x, y, a', x', c', kv, rfl, hkv, -, h2⟩ := fpNode_branch_inv hn
    have hl : kv.length ≤ a'.length := by
      rw [hkv] at hlen; simp only [List.length_cons] at hlen; omega
    obtain ⟨r1, r2⟩ := ih h2 hl (inv.refine hkv pop (fun h => by cases h) (fun _ => hw))
    exact ⟨.succ dw w hw pop r1, r2⟩
  | toZero dw pop _ ih =>
    intro a σ R ν rest hn hlen inv
    obtain ⟨x, y, a', x', c', kv, e, A, rfl, hkv, -, -, -, h1, -, -⟩ := fpNode_branchTo_inv hn
    have hl : kv.length ≤ a'.length := by
      rw [hkv] at hlen; simp only [List.length_cons] at hlen; omega
    obtain ⟨r1, r2⟩ := ih h1 hl (inv.refine hkv pop (fun _ => rfl) (fun h => by cases h))
    exact ⟨.toZero dw pop r1, r2⟩
  | toSucc dw w hw hk pop _ ih =>
    intro a σ R ν rest hn hlen inv
    obtain ⟨x, y, a', x', c', kv, e, A, rfl, hkv, he, hA, hgo, -, hcA, hR⟩ :=
      fpNode_branchTo_inv hn
    obtain ⟨A', hA', hnode⟩ := fpCert_at hf (cert_at he hk)
    rw [hA] at hA'
    cases hA'
    have hl : A.entry.kv.length ≤ e.frame.length := by
      rw [← compat_length hcA, ← gotoCompat_length hgo]
      rw [hkv] at hlen; simp only [List.length_cons] at hlen
      show kv.length ≤ _
      omega
    obtain ⟨r1, r2⟩ := ih hnode hl
      ((inv.refine hkv pop (fun h => by cases h) (fun _ => hw)).compat hcA)
    rw [hR] at r2
    exact ⟨.toSucc dw w hw hk pop r1, r2⟩
  | last h =>
    intro a σ R ν rest _ _ _
    exact ⟨.last h, fun _ ho => by cases ho⟩
  | next h _ ih =>
    intro a σ R ν rest hn hlen inv
    obtain ⟨a', σ', ha, hs, hn'⟩ := fpNode_next_inv hn
    obtain ⟨hrun, pot, pot'⟩ := hP h
    obtain ⟨hobs, hl, ν', inv'⟩ := fstep_sound_noStateGas hsg hs ha hlen inv hrun pot pot'
    obtain ⟨r1, r2⟩ := ih hn' hl inv'
    exact ⟨.next ⟨h, hobs⟩ r1, r2⟩
  | dest burn _ ih =>
    intro a σ R ν rest hn hlen inv
    obtain ⟨r1, r2⟩ := ih hn hlen (inv.burn burn)
    exact ⟨.dest burn r1, r2⟩
  | jump dw hk pop _ ih =>
    intro a σ R ν rest hn hlen inv
    obtain ⟨x, a', x', kv, e, A, rfl, hkv, he, hA, hgo, hcA, hR⟩ := fpNode_jump_inv hn
    obtain ⟨A', hA', hnode⟩ := fpCert_at hf (cert_at he hk)
    rw [hA] at hA'
    cases hA'
    have hl : A.entry.kv.length ≤ e.frame.length := by
      rw [← compat_length hcA, ← gotoCompat_length hgo]
      rw [hkv] at hlen; simp only [List.length_cons] at hlen
      show kv.length ≤ _
      omega
    obtain ⟨r1, r2⟩ := ih hnode hl ((inv.pop hkv pop).compat hcA)
    rw [hR] at r2
    exact ⟨.jump dw hk pop r1, r2⟩
  | ret dw pop =>
    intro a σ R ν rest hn hlen inv
    obtain ⟨a', x', kv, rfl, hkv, hc⟩ := fpNode_ret_inv hn
    refine ⟨.ret dw pop, fun d'' ho => ?_⟩
    cases ho
    exact ⟨_, (inv.pop hkv pop).compat hc⟩
  | callHalt dw hk pop _ ih =>
    intro a σ R ν rest hn hlen inv
    obtain ⟨t, a', x', kv, e, A, rfl, hkv, he, hA, hcA, -, -⟩ := fpNode_callNext_inv hn
    obtain ⟨A', hA', hnode⟩ := fpCert_at hf (cert_at he hk)
    rw [hA] at hA'
    cases hA'
    obtain ⟨-, S2, hst, hS, hfa, hw, hrd⟩ := inv.pop_raw (ks := [x']) (by rw [hkv]; rfl) rfl pop
    have invC : FpInv ν (popped σ (kv.take e.frame.length)) _
        (S2.drop e.frame.length ++ rest) :=
      ⟨S2.take e.frame.length, by rw [hst, ← List.append_assoc, List.take_append_drop],
        List.forall₂_take _ hS, AllHold.closeLive _ _ hfa, hw,
        fun h hm => hrd h (closeLive_sub hm)⟩
    have hl : A.entry.kv.length ≤ e.frame.length := by
      rw [← compat_length hcA]
      exact List.length_take_le _ _
    obtain ⟨r1, -⟩ := ih hnode hl (invC.compat hcA)
    exact ⟨.callHalt dw hk pop r1, fun _ ho => by cases ho⟩
  | callRet dw hk pop runC _ ihC ihK =>
    intro a σ R ν rest hn hlen inv
    obtain ⟨t, a', x', kv, e, A, rfl, hkv, he, hA, hcA, hrets, hcont⟩ := fpNode_callNext_inv hn
    obtain ⟨A', hA', hnode⟩ := fpCert_at hf (cert_at he hk)
    rw [hA] at hA'
    cases hA'
    obtain ⟨-, S2, hst, hS, hfa, hw, hrd⟩ := inv.pop_raw (ks := [x']) (by rw [hkv]; rfl) rfl pop
    have invC : FpInv ν (popped σ (kv.take e.frame.length)) _
        (S2.drop e.frame.length ++ rest) :=
      ⟨S2.take e.frame.length, by rw [hst, ← List.append_assoc, List.take_append_drop],
        List.forall₂_take _ hS, AllHold.closeLive _ _ hfa, hw,
        fun h hm => hrd h (closeLive_sub hm)⟩
    have hl : A.entry.kv.length ≤ e.frame.length := by
      rw [← compat_length hcA]
      exact List.length_take_le _ _
    obtain ⟨r1, r2⟩ := ihC hnode hl (invC.compat hcA)
    obtain ⟨μ, Sr, hstr, hSr, hfr, hwr, -⟩ := r2 _ rfl
    cases hidx : e.frame.findIdx? (· == .ret) with
    | none => exact (runC.not_returned_of_noRet (fpNode_retClosed hf) he hk hidx).elim
    | some i =>
      obtain ⟨ν', -, hhigh, hkv', hf', hfp'⟩ := resume_sound (σ := σ) (below := kv.drop e.frame.length)
        (fun s hs => by rw [hkv]; exact List.mem_cons_of_mem _ (List.mem_of_mem_drop hs))
        (List.forall₂_drop _ hS) hfa hSr hfr
      have hl' : (resume σ (kv.drop e.frame.length) A.ret).kv.length ≤
          (List.replicate e.rets AVal.unk ++ a'.drop e.frame.length).length := by
        rw [hkv] at hlen
        simp only [resume, List.length_append, List.length_map, List.length_drop,
          List.length_replicate, List.length_cons, hrets] at hlen ⊢
        omega
      obtain ⟨r3, r4⟩ := ihK (hcont i hidx) hl'
        ⟨Sr ++ S2.drop e.frame.length, by rw [hstr, List.append_assoc], hkv', hf',
          FpWord.shift hfp' hhigh hwr, fun _ hm => absurd hm resume_rds⟩
      exact ⟨.callRet dw hk pop r1 r3, r4⟩
  | pcAt _ _ _ _ =>
    intro a σ R ν rest hn _ _
    simp only [fpNode] at hn
    cases hn

/-! ## The frozen statements -/

/-- Covered-fork projection of the actual-rules soundness theorem. -/
theorem fp_run {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d' ∧ Pot d ∧ Pot d')
    {c : Cert} {ann : List Ann} (hf : fpCert c ann = true)
    {sevm : Sevm} (hfork : CoveredFork sevm.benvStat.fork) {d : Devm} {f : SFunc} {o : Outcome}
    (run : SFunc.RunP P c.prog sevm d f o) :
    ∀ {a : List AVal} {σ R : FSt} {ν : Nat → B256} {rest : List B256},
      fpNode c.entries ann R a σ f = true → σ.kv.length ≤ a.length → FpInv ν σ d rest →
      SFunc.RunP (FpStep P) c.prog sevm d f o ∧
        ∀ d'', o = .returned d'' → ∃ μ, FpInv μ R d'' rest :=
  fp_run_noStateGas hP hf hfork.rules_stateGas_none run

/-- **Soundness of the free-pointer checker** (tree level, no bytes): every run of entry `0`
of an accepted certificate, from empty memory, under a step relation that records the
potential, observes a good free pointer at every free-pointer read. -/
theorem fpRun_sound_noStateGas {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d' ∧ Pot d ∧ Pot d')
    {c : Cert} {ann : List Ann} (hf : fpCert c ann = true)
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none) {pre post : Devm}
    (_hmem : pre.memory = Mem.empty) (run : SProg.RunP P c.prog sevm pre post) :
    SProg.RunP (FpStep P) c.prog sevm pre post := by
  -- the empty memory is not needed: the walk starts with no pointer symbol
  obtain ⟨f, hf0, r⟩ := run
  have hc0 : ∃ e, c[0]? = some (e, f) := by
    simp only [Cert.prog, List.getElem?_map] at hf0
    cases h : c[0]? with
    | none => rw [h] at hf0; cases hf0
    | some p =>
      rw [h] at hf0
      cases hf0
      exact ⟨p.1, rfl⟩
  obtain ⟨e, hc0⟩ := hc0
  obtain ⟨A, hA, hnode⟩ := fpCert_at hf hc0
  have hinit : A.entry = FSt.init := by
    simp only [fpCert, Bool.and_eq_true, beq_iff_eq] at hf
    have h := hf.1.2
    rw [hA] at h
    exact Option.some.inj h
  rw [hinit] at hnode
  have inv : FpInv (fun _ => 0) FSt.init pre pre.stack :=
    ⟨[], rfl, .nil, fun _ h => by simp only [FSt.init, List.not_mem_nil] at h, FpWord.none _ _,
      fun _ h => by simp only [FSt.init, List.not_mem_nil] at h⟩
  exact ⟨f, hf0, (fp_run_noStateGas hP hf hsg r hnode (Nat.zero_le _) inv).1⟩

/-- Covered-fork projection of the actual-rules soundness theorem. -/
theorem fpRun_sound {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d' ∧ Pot d ∧ Pot d')
    {c : Cert} {ann : List Ann} (hf : fpCert c ann = true)
    {sevm : Sevm} (hfork : CoveredFork sevm.benvStat.fork) {pre post : Devm}
    (hmem : pre.memory = Mem.empty) (run : SProg.RunP P c.prog sevm pre post) :
    SProg.RunP (FpStep P) c.prog sevm pre post :=
  fpRun_sound_noStateGas hP hf hfork.rules_stateGas_none hmem run

/-- **The walk-facing lifting theorem**: a successful frame of certified bytes, entered fresh
with bounded potential, is a run of the certified program whose steps sit in the derivation,
record the potential, and read only good free pointers. -/
theorem lift_sound_fp_noStateGas {code : ByteArray} {c : Cert} {ann : List Ann}
    (hc : Cert.check code c = true) (hf : fpCert c ann = true)
    {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = code)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hmem : pre.memory = Mem.empty) (hpot : pre.gasMeasure < 2 ^ 256)
    (exc : Exec 0 sevm pre (.ok post)) :
    SProg.RunP (FpStep (PotStep (StepIn ⟨0, sevm, pre, .ok post, exc⟩))) c.prog sevm pre post := by
  obtain ⟨f, hf0, r⟩ := lift_sound_in_noStateGas hc hcode hsg exc
  have pot : Pot pre := by
    unfold Pot
    rw [hmem]
    exact hpot
  obtain ⟨r', -⟩ := SFunc.RunP.withPot (fun h => StepIn.toRun h) hsg r pot
  exact fpRun_sound_noStateGas (fun h => ⟨StepIn.toRun h.1, h.2.1, h.2.2⟩) hf hsg hmem ⟨f, hf0, r'⟩

/-- Covered-fork projection, retaining both original readiness premises. -/
theorem lift_sound_fp {code : ByteArray} {c : Cert} {ann : List Ann}
    (hc : Cert.check code c = true) (hf : fpCert c ann = true)
    {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (hsg : sevm.benvStat.rules.stateGas = none)
    (hmem : pre.memory = Mem.empty) (hpot : pre.gasMeasure < 2 ^ 256)
    (exc : Exec 0 sevm pre (.ok post)) :
    SProg.RunP (FpStep (PotStep (StepIn ⟨0, sevm, pre, .ok post, exc⟩))) c.prog sevm pre post := by
  have _ := hfork
  exact lift_sound_fp_noStateGas hc hf hcode hsg hmem hpot exc

end Blanc.Lift.FreePtr
