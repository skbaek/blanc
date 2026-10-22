import Blanc.Lift.Sound
import Blanc.Lift.Cursor
import Blanc.Lift.ReachWalk
import Blanc.Lift.RetainedTargetCompleteness

/-!
# Node soundness with its same-frame span, for exec-free trees

`node_soundM` (`Blanc/Lift/Sound.lean`) relates a checked derivation node to a synthetic run,
and in the returned case hands back the actual node `exc'` at the return address — but only as a
strictly smaller derivation (`Exec.Deriv.lt`), which may a priori sit inside a child frame.  For a
tree with no external instruction whose referenced entries form an exec-free set
(`SFunc.execFreeIn E`, `ExecFreeSet`), `node_spanM` proves the same claim with the span made
explicit:

* returned: the actual return node is reached from the start along the frame's own chain without
  decoding any `Xinst` (`Exec.Deriv.ExecFreeUntil`), so it has the same direct children
  (`Exec.Deriv.ExecFreeUntil.childFrames_eq`);
* halted: no node of the chain decodes an `Xinst` (`ChainFree`), so the frame has no direct child
  from there on (`Exec.childFrames_eq_nil_of_free`).

`SilentSet.execFreeSet`: a state-silent closed set is exec-free.

The recursion is `node_soundM`'s; every same-frame edge it crosses is read off the derivation's
immediate sub-derivation relation (`prec_parentStep_of_free`) and composed by `SpanOut.back`.
Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune AbstractStackSafety

/-! ## Same-frame spans -/

/-- No node of the same-frame chain from `pk` decodes an `Xinst`. -/
def ChainFree (pk : Exec.Deriv) : Prop :=
  ∀ node, Exec.Deriv.ParentPrefix pk node →
    ∀ x : Xinst, ¬ Ninst.At node.sevm.code node.pc (.exec x)

theorem ChainFree.of_span {pk q : Exec.Deriv} (span : Exec.Deriv.ExecFreeUntil pk q)
    (h : ChainFree q) : ChainFree pk :=
  fun node reached => (span.2 node reached).elim (h node) id

/-- A node at a halting instruction ends its chain, and decodes no `Xinst`. -/
theorem ChainFree.of_linst {pk : Exec.Deriv} {l : Linst}
    (hat : Linst.At pk.sevm.code pk.pc l) : ChainFree pk := by
  intro node reached x hx
  cases reached with
  | refl =>
    unfold Linst.At at hat
    unfold Ninst.At at hx
    rw [hat] at hx
    cases hx
  | step head _ => exact Cursor.parentStep_false_of_linst head hat

/-- A non-`Xinst` instruction decodes no `Xinst`. -/
theorem Ninst.At.not_exec_of_ne {code : ByteArray} {pc : Nat} {n : Ninst}
    (hat : Ninst.At code pc n) (hn : ∀ x, n ≠ .exec x) (x : Xinst) :
    ¬ Ninst.At code pc (.exec x) := by
  intro hx
  unfold Ninst.At at hat hx
  rw [hat] at hx
  cases hx
  exact hn x rfl

/-- An immediate sub-derivation of a node that decodes no `Xinst` is its same-frame
continuation. -/
theorem prec_parentStep_of_free {q p : Exec.Deriv} (h : q ≺ p)
    (free : ∀ x : Xinst, ¬ Ninst.At p.sevm.code p.pc (.exec x)) :
    Exec.Deriv.ParentStep q p := by
  cases h with
  | cont hstep exc => exact .cont hstep exc
  | doneOk hstep henter hr exc => exact .doneOk hstep henter hr exc
  | runOkCont hstep henter excChild hr exc => exact .runOk hstep henter excChild hr exc
  | runErrChild hstep _ _ _ =>
    obtain ⟨x, hx, -, -⟩ := Evm.step_spawn_inv hstep
    exact (free x hx).elim
  | runOkChild hstep _ _ _ _ =>
    obtain ⟨x, hx, -, -⟩ := Evm.step_spawn_inv hstep
    exact (free x hx).elim

/-- One exec-free immediate step is a span. -/
theorem span_of_prec {q p : Exec.Deriv} (h : q ≺ p)
    (free : ∀ x : Xinst, ¬ Ninst.At p.sevm.code p.pc (.exec x)) :
    Exec.Deriv.ExecFreeUntil p q :=
  Exec.Deriv.ExecFreeUntil.ofStep (prec_parentStep_of_free h free) free

/-- A node reached after at least one same-frame edge is strictly smaller. -/
theorem lt_of_prefix_lt {pk next q : Exec.Deriv} (hlt : Exec.Deriv.lt next pk)
    (pp : Exec.Deriv.ParentPrefix next q) : Exec.Deriv.lt q pk := by
  induction pp generalizing pk with
  | refl => exact hlt
  | step head _ ih => exact ih (deriv_lt_trans head.lt hlt)

/-- How a span-tracked node claim ends: halted (`H`) with an exec-free chain, or returned to
`ρ` (`Ret`) at an actual node `Q`-related, reached by an exec-free span. -/
def SpanOut (pk : Exec.Deriv) (sevm : Sevm) (post : Devm) (ρ : B256) (H Ret : Prop)
    (Q : Devm → Prop) : Prop :=
  (H ∧ ChainFree pk) ∨
    (Ret ∧ ∃ (d : Devm) (exc' : Exec ρ.toNat sevm d (.ok post)),
      Exec.Deriv.ExecFreeUntil pk ⟨ρ.toNat, sevm, d, .ok post, exc'⟩ ∧ Q d)

/-- Prefix a span to a claim's outcome. -/
theorem SpanOut.back {pk q : Exec.Deriv} {sevm : Sevm} {post : Devm} {ρ : B256}
    {H H' Ret Ret' : Prop} {Q Q' : Devm → Prop}
    (h : SpanOut q sevm post ρ H Ret Q) (span : Exec.Deriv.ExecFreeUntil pk q)
    (hH : H → H') (hRet : Ret → Ret') (hQ : ∀ d, Q d → Q' d) :
    SpanOut pk sevm post ρ H' Ret' Q' := by
  rcases h with ⟨hh, hfree⟩ | ⟨hr, d, exc', hspan, hq⟩
  · exact .inl ⟨hH hh, ChainFree.of_span span hfree⟩
  · exact .inr ⟨hRet hr, d, exc', span.trans hspan, hQ d hq⟩

/-! ## Exec-free subtrees -/

section ExecFree

variable {E : List Nat}

theorem execFreeIn_branch {f g : SFunc} (h : (SFunc.branch f g).execFreeIn E = true) :
    f.execFreeIn E = true ∧ g.execFreeIn E = true := by
  simp only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs, List.all_append,
    Bool.and_eq_true] at h ⊢
  exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩

theorem execFreeIn_branchTo {f : SFunc} {k : Nat}
    (h : (SFunc.branchTo f k).execFreeIn E = true) : f.execFreeIn E = true ∧ k ∈ E := by
  simp only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs, List.all_cons,
    Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨⟨h.1, h.2.2⟩, h.2.1⟩

theorem execFreeIn_jump {k : Nat} (h : (SFunc.jump k).execFreeIn E = true) : k ∈ E := by
  simpa only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs, List.all_cons, List.all_nil,
    Bool.and_true, Bool.true_and, decide_eq_true_eq] using h

theorem execFreeIn_callNext {f : SFunc} {k : Nat}
    (h : (SFunc.callNext k f).execFreeIn E = true) : f.execFreeIn E = true ∧ k ∈ E := by
  simp only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs, List.all_cons,
    Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨⟨h.1, h.2.2⟩, h.2.1⟩

theorem execFreeIn_dest {f : SFunc} (h : (SFunc.dest f).execFreeIn E = true) :
    f.execFreeIn E = true := by
  simpa only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs] using h

theorem execFreeIn_pcAt {f : SFunc} {p : Nat} (h : (SFunc.pcAt p f).execFreeIn E = true) :
    f.execFreeIn E = true := by
  simpa only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs] using h

theorem execFreeIn_next {n : Ninst} {f : SFunc} (h : (SFunc.next n f).execFreeIn E = true) :
    (∀ x, n ≠ .exec x) ∧ f.execFreeIn E = true := by
  cases n with
  | exec x =>
    simp only [SFunc.execFreeIn, SFunc.execsSatisfy, Bool.false_and,
      Bool.false_eq_true] at h
  | _ =>
    refine ⟨fun x hx => (by cases hx), ?_⟩
    simpa only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs] using h

end ExecFree

/-- A state-silent closed set is exec-free: silence excludes every `Xinst`. -/
theorem SFunc.execsSatisfy_of_silent : ∀ {f : SFunc}, f.silent = true →
    f.execsSatisfy (fun _ => false) = true
  | .branch f g, h => by
    simp only [SFunc.silent, Bool.and_eq_true] at h
    simp only [SFunc.execsSatisfy, execsSatisfy_of_silent h.1, execsSatisfy_of_silent h.2,
      Bool.and_self]
  | .branchTo f _, h => by
    simp only [SFunc.silent] at h
    simpa only [SFunc.execsSatisfy] using execsSatisfy_of_silent h
  | .last _, _ => by simp only [SFunc.execsSatisfy]
  | .next n f, h => by
    simp only [SFunc.silent, Bool.and_eq_true] at h
    cases n with
    | exec x =>
      have h1 := h.1
      simp only [Ninst.stateSilent, Bool.false_eq_true] at h1
    | _ => simpa only [SFunc.execsSatisfy] using execsSatisfy_of_silent h.2
  | .dest f, h => by
    simp only [SFunc.silent] at h
    simpa only [SFunc.execsSatisfy] using execsSatisfy_of_silent h
  | .jump _, _ => by simp only [SFunc.execsSatisfy]
  | .callNext _ f, h => by
    simp only [SFunc.silent] at h
    simpa only [SFunc.execsSatisfy] using execsSatisfy_of_silent h
  | .ret, _ => by simp only [SFunc.execsSatisfy]
  | .pcAt _ f, h => by
    simp only [SFunc.silent] at h
    simpa only [SFunc.execsSatisfy] using execsSatisfy_of_silent h
  | .undefined, _ => by simp only [SFunc.execsSatisfy]

theorem SilentSet.execFreeSet {fs : List SFunc} {S : List Nat} (h : SilentSet fs S = true) :
    ExecFreeSet fs S = true := by
  simp only [SilentSet, ExecFreeSet, List.all_eq_true] at h ⊢
  intro k hk
  have hk' := h k hk
  split at hk'
  · rename_i g hg
    simp only [hg, SFunc.execFreeIn, Bool.and_eq_true] at hk' ⊢
    exact ⟨SFunc.execsSatisfy_of_silent hk'.1, hk'.2⟩
  · rename_i hg
    simp only [hg] at hk' ⊢
    exact hk'

/-! ## The span-strengthened node claim -/

/-- `NodeClaim0` for an exec-free tree, with the span of the frame's chain made explicit. -/
def SpanClaim (code : ByteArray) (c : Cert) (ms : List MemMap) (b : Bool) (E : List Nat)
    (pk : Exec.Deriv) : Prop :=
  ∀ (post : Devm), pk.exn = .ok post → pk.sevm.code = code →
  CoveredFork pk.sevm.benvStat.fork →
  ∀ (m : Nat) (a : List AVal) (f : SFunc) (ρ : B256) (S base : List B256) (μ : MemMap),
    checkNodeM code c.entries ms b m pk.pc a μ f = true → f.execFreeIn E = true →
    pk.devm.stack = S ++ base → FrameMatches ρ a S → MemMatches ρ μ pk.devm.memory →
    SpanOut pk pk.sevm post ρ (SFunc.Run c.prog pk.sevm pk.devm f (.halted post)) (RetIn a μ)
      (fun d => SFunc.Run c.prog pk.sevm pk.devm f (.returned d) ∧
        ∃ S' : List B256, d.stack = S' ++ base ∧ S'.length = m)

theorem node_spanM {code : ByteArray} {c : Cert} {ms : List MemMap} {b : Bool} {E : List Nat}
    (hc : Cert.CheckedM code c ms b) (hE : ExecFreeSet c.prog E = true) :
    ∀ pk : Exec.Deriv, SpanClaim code c ms b E pk := by
  apply Exec.Deriv.strongRec
  intro pk ih post hpost hcode hfork m a f ρ S base μ hcheck hfree hstack hframe hmem
  rcases pk with ⟨pc, sevm, devm, exn, exc⟩
  cases exn with
  | error e => cases hpost
  | ok post =>
    cases hpost
    dsimp only at hcheck hstack hmem hcode hfork ih ⊢
    cases f with
    | branch f g =>
      obtain ⟨hff, hgf⟩ := execFreeIn_branch hfree
      cases a with
      | nil => simp only [checkNodeM, Bool.false_eq_true] at hcheck
      | cons av a0 =>
        cases av with
        | ret => simp only [checkNodeM, Bool.false_eq_true] at hcheck
        | unk => simp only [checkNodeM, Bool.false_eq_true] at hcheck
        | const t =>
          cases a0 with
          | nil => simp only [checkNodeM, Bool.false_eq_true] at hcheck
          | cons av2 a' =>
            have hcheck' :
                (byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
                  (av2.jumps? = some true ∨
                    checkNodeM code c.entries ms b m (pc + 1) a' μ f = true)) ∧
                (av2.jumps? = some false ∨
                  checkNodeM code c.entries ms b m t.toNat a' μ g = true) := by
              simpa only [checkNodeM, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] using hcheck
            have h_at : Jinst.At sevm.code pc .jumpi := by
              apply byteAt_jinst_at
              rw [hcode]
              exact hcheck'.1.1
            obtain ⟨s0, s1, S1, rfl⟩ : ∃ s0 s1 S1, S = s0 :: s1 :: S1 := by
              rcases hframe with _ | ⟨_, _ | ⟨_, _⟩⟩
              exact ⟨_, _, _, rfl⟩
            obtain ⟨hs0, hs1f, htail⟩ : s0 = t ∧ AVal.Matches ρ av2 s1 ∧ FrameMatches ρ a' S1 := by
              rcases hframe with _ | ⟨h0, _ | ⟨h1, ht⟩⟩
              exact ⟨h0, h1, ht⟩
            subst hs0
            have hret : ∀ {a'' : List AVal}, (AVal.ret ∈ a'' → AVal.ret ∈ a') →
                RetIn a'' μ → RetIn (.const s0 :: av2 :: a') μ := fun himp h =>
              RetIn.of_frame (fun hm => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (himp hm))) h
            rcases jumpi_at_exact exc h_at with
                ⟨x, inter, exc', pop, _, prec⟩ | ⟨x, y, inter, exc', pop, _, _, hy, prec⟩
            · have hpop := popBurn_two_stack pop
              rw [hstack] at hpop
              simp only [List.cons_append, List.cons.injEq] at hpop
              obtain ⟨rfl, rfl, hinter⟩ := hpop
              exact (ih ⟨pc + 1, sevm, inter, .ok post, exc'⟩ (Exec.Deriv.lt_of_prec prec) post rfl
                hcode hfork m a' f ρ S1 base μ (live_fall hs1f hcheck'.1.2) hff hinter.symm htail
                (hmem.of_memory_eq pop.memory)).back
                (span_of_prec prec (Blanc.Jinst.At.not_exec h_at))
                (SFunc.RunP.zero s0 pop) (hret id)
                (fun _ q => ⟨SFunc.RunP.zero s0 pop q.1, q.2⟩)
            · have hpop := popBurn_two_stack pop
              rw [hstack] at hpop
              simp only [List.cons_append, List.cons.injEq] at hpop
              obtain ⟨rfl, rfl, hinter⟩ := hpop
              exact (ih ⟨s0.toNat, sevm, inter, .ok post, exc'⟩ (Exec.Deriv.lt_of_prec prec) post
                rfl hcode hfork m a' g ρ S1 base μ (live_taken hy hs1f hcheck'.2) hgf hinter.symm
                htail (hmem.of_memory_eq pop.memory)).back
                (span_of_prec prec (Blanc.Jinst.At.not_exec h_at))
                (SFunc.RunP.succ s0 s1 hy pop) (hret id)
                (fun _ q => ⟨SFunc.RunP.succ s0 s1 hy pop q.1, q.2⟩)
    | branchTo f k =>
      obtain ⟨hff, hkE⟩ := execFreeIn_branchTo hfree
      cases a with
      | nil => simp only [checkNodeM, Bool.false_eq_true] at hcheck
      | cons av a0 =>
        cases av with
        | ret => simp only [checkNodeM, Bool.false_eq_true] at hcheck
        | unk => simp only [checkNodeM, Bool.false_eq_true] at hcheck
        | const t =>
          cases a0 with
          | nil => simp only [checkNodeM, Bool.false_eq_true] at hcheck
          | cons av2 a' =>
            cases hk : c.entries[k]? with
            | none => simp only [checkNodeM, hk, Bool.false_eq_true] at hcheck
            | some e =>
              have hcheck' :
                  (((byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
                    e.pc = t.toNat) ∧ e.rets = m) ∧
                    gotoCompat a' e.frame = true) ∧
                    (av2.jumps? = some true ∨
                      checkNodeM code c.entries ms b m (pc + 1) a' μ f = true) := by
                have h := hcheck
                simp only [checkNodeM, hk, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
                exact ⟨h.1.1, h.2⟩
              have hmc : memCompat μ (ms.getD k []) = true := by
                simp only [checkNodeM, hk, Bool.and_eq_true] at hcheck
                exact hcheck.1.2
              rcases cert_prog_of_entry c k e hk with ⟨g, hg⟩
              have hentry := hc k e g hk hg
              have h_at : Jinst.At sevm.code pc .jumpi := by
                apply byteAt_jinst_at
                rw [hcode]
                exact hcheck'.1.1.1.1
              obtain ⟨s0, s1, S1, rfl⟩ : ∃ s0 s1 S1, S = s0 :: s1 :: S1 := by
                rcases hframe with _ | ⟨_, _ | ⟨_, _⟩⟩
                exact ⟨_, _, _, rfl⟩
              obtain ⟨hs0, hs1f, htail⟩ :
                  s0 = t ∧ AVal.Matches ρ av2 s1 ∧ FrameMatches ρ a' S1 := by
                rcases hframe with _ | ⟨h0, _ | ⟨h1, ht⟩⟩
                exact ⟨h0, h1, ht⟩
              subst hs0
              have hret : ∀ {a'' : List AVal}, (AVal.ret ∈ a'' → AVal.ret ∈ a') →
                  RetIn a'' μ → RetIn (.const s0 :: av2 :: a') μ := fun himp h =>
                RetIn.of_frame
                  (fun hm => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (himp hm))) h
              rcases jumpi_at_exact exc h_at with
                  ⟨x, inter, exc', pop, _, prec⟩ | ⟨x, y, inter, exc', pop, _, _, hy, prec⟩
              · have hpop := popBurn_two_stack pop
                rw [hstack] at hpop
                simp only [List.cons_append, List.cons.injEq] at hpop
                obtain ⟨rfl, rfl, hinter⟩ := hpop
                exact (ih ⟨pc + 1, sevm, inter, .ok post, exc'⟩ (Exec.Deriv.lt_of_prec prec) post
                  rfl hcode hfork m a' f ρ S1 base μ (live_fall hs1f hcheck'.2) hff hinter.symm
                  htail (hmem.of_memory_eq pop.memory)).back
                  (span_of_prec prec (Blanc.Jinst.At.not_exec h_at))
                  (SFunc.RunP.toZero s0 pop) (hret id)
                  (fun _ q => ⟨SFunc.RunP.toZero s0 pop q.1, q.2⟩)
              · have hpop := popBurn_two_stack pop
                rw [hstack] at hpop
                simp only [List.cons_append, List.cons.injEq] at hpop
                obtain ⟨rfl, rfl, hinter⟩ := hpop
                have hentry' : checkNodeM code c.entries ms b e.rets s0.toNat e.frame
                    (ms.getD k []) g = true := by
                  simpa only [List.getD_eq_getElem?_getD, hcheck'.1.1.1.2] using hentry
                have hlen := hcheck'.1.1.2
                exact (ih ⟨s0.toNat, sevm, inter, .ok post, exc'⟩ (Exec.Deriv.lt_of_prec prec)
                  post rfl hcode hfork e.rets e.frame g ρ S1 base (ms.getD k []) hentry'
                  (ExecFreeSet.lookup hE hkE hg) hinter.symm
                  (frameMatches_gotoCompat hcheck'.1.2 htail)
                  ((hmem.of_memory_eq pop.memory).of_memCompat hmc)).back
                  (span_of_prec prec (Blanc.Jinst.At.not_exec h_at))
                  (SFunc.RunP.toSucc s0 s1 hy hg pop)
                  (fun r => hret id (r.imp (ret_mem_of_gotoCompat hcheck'.1.2)
                    (mem_snd_of_memCompat hmc)))
                  (fun _ q => ⟨SFunc.RunP.toSucc s0 s1 hy hg pop q.1, by rw [← hlen]; exact q.2⟩)
    | last l =>
      have hbyte : byteAt code pc = some l.toUInt8 := by
        simpa only [checkNodeM, beq_iff_eq] using hcheck
      have h_at : Linst.At sevm.code pc l := by
        apply byteAt_linst_at
        rw [hcode]
        exact hbyte
      exact .inl ⟨SFunc.RunP.last (Linst.run_of_at exc h_at), ChainFree.of_linst h_at⟩
    | next n f =>
      obtain ⟨hnx, hff⟩ := execFreeIn_next hfree
      have h_at : Ninst.At sevm.code pc n := by
        apply Ninst.at_of_slice
        apply bytesAt_slice (ninst_bytes_ne_nil n)
        rw [hcode]
        cases n <;> simp only [checkNodeM, Bool.and_eq_true] at hcheck <;> exact hcheck.1.1
      have hnfree := Ninst.At.not_exec_of_ne h_at hnx
      rcases Ninst.runIn_of_at exc h_at with ⟨inter, exc', runW, prec⟩
      have run : Ninst.Run sevm devm _ inter := runW.toRun
      have span := span_of_prec prec hnfree
      -- The abstract successor frame `a'`, memory map, and checked child, by instruction shape.
      have step : ∃ (a' : List AVal) (μ' : MemMap) (S' : List B256),
          checkNodeM code c.entries ms b m (pc + n.size) a' μ' f = true ∧
          inter.stack = S' ++ base ∧ FrameMatches ρ a' S' ∧ MemMatches ρ μ' inter.memory ∧
          (RetIn a' μ' → RetIn a μ) := by
        by_cases hpush : ∃ (bs : Bytes) (fits : bs.length ≤ 32), n = .push bs fits
        · obtain ⟨bs, fits, rfl⟩ := hpush
          have hchild : checkNodeM code c.entries ms b m (pc + (Ninst.push bs fits).size)
              (if b then memFold (memTop (.push bs fits) a μ) (.const (Bytes.toB256 bs) :: a)
                else .const (Bytes.toB256 bs) :: a)
              (if b then absMem (.push bs fits) a μ else []) f = true := by
            simp only [checkNodeM, absNinst, Bool.and_eq_true] at hcheck
            exact hcheck.2
          have hstack' : inter.stack = Bytes.toB256 bs :: (S ++ base) := by
            rw [push_run_stack run, hstack]
          obtain ⟨hframe', hmem'⟩ := step_mem_sound b hfork hframe hstack hmem run
            (by rw [hstack']; rfl)
            (show FrameMatches ρ (.const (Bytes.toB256 bs) :: a) (Bytes.toB256 bs :: S) from
              List.Forall₂.cons rfl hframe)
          refine ⟨_, _, _, hchild, hstack', hframe', hmem', fun hret => ?_⟩
          rcases RetIn.of_step b hret with h | h | h
          · exact .inl (by simpa only [List.mem_cons, reduceCtorEq, false_or] using h)
          · exact .inl h
          · exact .inr h
        · have hnpush : ∀ (bs : Bytes) (fits : bs.length ≤ 32), n ≠ .push bs fits :=
            fun bs fits he => hpush ⟨bs, fits, he⟩
          have hrest : (match absNinst n a with
              | some a' => checkNodeM code c.entries ms b m (pc + n.size)
                  (if b then memFold (memTop n a μ) a' else a')
                  (if b then absMem n a μ else []) f
              | none => false) = true := by
            cases n with
            | push bs fits => exact (hnpush bs fits rfl).elim
            | _ => simp only [checkNodeM, Bool.and_eq_true] at hcheck; exact hcheck.2
          cases ha : absNinst n a with
          | none => simp only [ha, Bool.false_eq_true] at hrest
          | some a' =>
            have hchild : checkNodeM code c.entries ms b m (pc + n.size)
                (if b then memFold (memTop n a μ) a' else a')
                (if b then absMem n a μ else []) f = true := by
              simpa only [ha] using hrest
            rcases absNinst_nonpush_spec hnpush ha with ⟨hlen, out, a0, htrans, hread, hfold⟩
            have hinput : Matches ((indexPattern a.length).map (label a ρ) ++ base.map some)
                devm.stack := by
              rw [hstack]
              apply matches_append
              · rw [indexPattern_map_label hlen]
                exact frameMatches_matches hframe
              · exact matches_some_map base
            have hout := ninstTransfer_run hfork hinput
              (ninstTransfer_append (base.map some) (ninstTransfer_map (label a ρ) rfl htrans)) run
            rw [mapM_readBack_label hread] at hout
            rcases matches_split hout with ⟨S', below, hsp, hfirst, hbelow⟩
            have hinter : inter.stack = S' ++ base := by
              simpa only [matches_some_map_eq hbelow] using hsp
            have hframe0 : FrameMatches ρ a' S' := by
              rw [hfold]
              exact frameMatches_foldTop hframe hstack run hinter (matches_to_frame hfirst)
            obtain ⟨hframe', hmem'⟩ := step_mem_sound b hfork hframe hstack hmem run hinter hframe0
            refine ⟨_, _, _, hchild, hinter, hframe', hmem', fun hret => ?_⟩
            rcases RetIn.of_step b hret with h | h | h
            · exact .inl (ret_mem_of_readBack hread (ret_mem_of_foldTop (hfold ▸ h)))
            · exact .inl h
            · exact .inr h
      obtain ⟨a', μ', S', hchild, hinter, hframe', hmem', hretF⟩ := step
      exact (ih ⟨pc + n.size, sevm, inter, .ok post, exc'⟩ (Exec.Deriv.lt_of_prec prec) post rfl
        hcode hfork m a' f ρ S' base μ' hchild hff hinter hframe' hmem').back span
        (SFunc.RunP.next run) hretF (fun _ q => ⟨SFunc.RunP.next run q.1, q.2⟩)
    | dest f =>
      have hcheck' : byteAt code pc = some (Jinst.toUInt8 .jumpdest) ∧
          checkNodeM code c.entries ms b m (pc + 1) a μ f = true := by
        simpa only [checkNodeM, Bool.and_eq_true, beq_iff_eq] using hcheck
      have h_at : Jinst.At sevm.code pc .jumpdest := by
        apply byteAt_jinst_at
        rw [hcode]
        exact hcheck'.1
      rcases jumpdest_at_exact exc h_at with ⟨inter, exc', burn, _, prec⟩
      have hstack' : inter.stack = S ++ base := by
        rw [← burn.stack, hstack]
      exact (ih ⟨pc + 1, sevm, inter, .ok post, exc'⟩ (Exec.Deriv.lt_of_prec prec) post rfl hcode
        hfork m a f ρ S base μ hcheck'.2 (execFreeIn_dest hfree) hstack' hframe
        (hmem.of_memory_eq burn.memory)).back
        (span_of_prec prec (Blanc.Jinst.At.not_exec h_at)) (SFunc.RunP.dest burn) id
        (fun _ q => ⟨SFunc.RunP.dest burn q.1, q.2⟩)
    | jump k =>
      have hkE := execFreeIn_jump hfree
      cases a with
      | nil => simp only [checkNodeM, Bool.false_eq_true] at hcheck
      | cons av a' =>
        cases av with
        | ret => simp only [checkNodeM, Bool.false_eq_true] at hcheck
        | unk => simp only [checkNodeM, Bool.false_eq_true] at hcheck
        | const t =>
          cases hk : c.entries[k]? with
          | none => simp only [checkNodeM, hk, Bool.false_eq_true] at hcheck
          | some e =>
            have hcheck0 :
                ((((byteAt code pc = some (Jinst.toUInt8 .jump) ∧
                  e.pc = t.toNat) ∧ e.rets = m) ∧
                  gotoCompat a' e.frame = true) ∧ memCompat μ (ms.getD k []) = true) := by
              simpa only [checkNodeM, hk, Bool.and_eq_true, beq_iff_eq] using hcheck
            obtain ⟨⟨⟨⟨hbyte, hepc⟩, hrets⟩, hgoto⟩, hmc⟩ := hcheck0
            rcases cert_prog_of_entry c k e hk with ⟨g, hg⟩
            have hentry : checkNodeM code c.entries ms b e.rets t.toNat e.frame
                (ms.getD k []) g = true := by
              simpa only [List.getD_eq_getElem?_getD, hepc] using hc k e g hk hg
            have h_at : Jinst.At sevm.code pc .jump := by
              apply byteAt_jinst_at
              rw [hcode]
              exact hbyte
            obtain ⟨s0, S1, rfl, hs0, htail⟩ :
                ∃ s0 S1, S = s0 :: S1 ∧ s0 = t ∧ FrameMatches ρ a' S1 := by
              rcases hframe with _ | ⟨h0, ht⟩
              exact ⟨_, _, rfl, h0, ht⟩
            subst hs0
            rcases jump_at_exact exc h_at with ⟨x, inter, exc', pop, _, _, prec⟩
            have hpop := popBurn_one_stack pop
            rw [hstack] at hpop
            simp only [List.cons_append, List.cons.injEq] at hpop
            obtain ⟨rfl, hinter⟩ := hpop
            exact (ih ⟨s0.toNat, sevm, inter, .ok post, exc'⟩ (Exec.Deriv.lt_of_prec prec) post
              rfl hcode hfork e.rets e.frame g ρ S1 base (ms.getD k []) hentry
              (ExecFreeSet.lookup hE hkE hg) hinter.symm (frameMatches_gotoCompat hgoto htail)
              ((hmem.of_memory_eq pop.memory).of_memCompat hmc)).back
              (span_of_prec prec (Blanc.Jinst.At.not_exec h_at))
              (SFunc.RunP.jump s0 hg pop)
              (fun r => RetIn.of_frame (fun h => List.mem_cons_of_mem _ h)
                (r.imp (ret_mem_of_gotoCompat hgoto) (mem_snd_of_memCompat hmc)))
              (fun _ q => ⟨SFunc.RunP.jump s0 hg pop q.1, by rw [← hrets]; exact q.2⟩)
    | callNext k f =>
      obtain ⟨hff, hkE⟩ := execFreeIn_callNext hfree
      cases a with
      | nil => simp only [checkNodeM, Bool.false_eq_true] at hcheck
      | cons av a' =>
        cases av with
        | ret => simp only [checkNodeM, Bool.false_eq_true] at hcheck
        | unk => simp only [checkNodeM, Bool.false_eq_true] at hcheck
        | const t =>
          cases f with
          | dest d =>
            cases hk : c.entries[k]? with
            | none => simp only [checkNodeM, hk, Bool.false_eq_true] at hcheck
            | some e =>
              simp only [checkNodeM, hk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
                List.isEmpty_iff] at hcheck
              have hempty : ms.getD k [] = [] := hcheck.1.2
              rcases cert_prog_of_entry c k e hk with ⟨g, hg⟩
              have hgf := ExecFreeSet.lookup hE hkE hg
              have hentry : checkNodeM code c.entries ms b e.rets t.toNat e.frame
                  (ms.getD k []) g = true := by
                simpa only [List.getD_eq_getElem?_getD, hcheck.1.1.1.2] using hc k e g hk hg
              have h_at : Jinst.At sevm.code pc .jump := by
                apply byteAt_jinst_at
                rw [hcode]
                exact hcheck.1.1.1.1
              obtain ⟨s0, S1, rfl, hs0, htail⟩ :
                  ∃ s0 S1, S = s0 :: S1 ∧ s0 = t ∧ FrameMatches ρ a' S1 := by
                rcases hframe with _ | ⟨h0, ht⟩
                exact ⟨_, _, rfl, h0, ht⟩
              subst hs0
              rcases jump_at_exact exc h_at with ⟨x, inter, exc', pop, _, _, prec⟩
              have hpop := popBurn_one_stack pop
              rw [hstack] at hpop
              simp only [List.cons_append, List.cons.injEq] at hpop
              obtain ⟨rfl, hinter⟩ := hpop
              have span0 := span_of_prec prec (Blanc.Jinst.At.not_exec h_at)
              have hmemE : MemMatches 0 (ms.getD k []) inter.memory := by
                rw [hempty]; exact memMatches_nil _ _
              cases hidx : e.frame.findIdx? (· == .ret) with
              | none =>
                have hcall : callCompat 0 a' e.frame = true := by
                  simpa only [hidx] using hcheck.2
                have hret_no : ∀ x, x ∈ e.frame → x ≠ AVal.ret :=
                  ret_not_mem_of_findIdx_none hidx
                rcases frameMatches_callCompat hcall htail with
                  ⟨Sf, Sr, hsplit, hframee, _⟩
                have hstacke : inter.stack = Sf ++ (Sr ++ base) := by
                  rw [← hinter, hsplit, List.append_assoc]
                rcases ih ⟨s0.toNat, sevm, inter, .ok post, exc'⟩ (Exec.Deriv.lt_of_prec prec)
                    post rfl hcode hfork e.rets e.frame g 0 Sf (Sr ++ base) (ms.getD k [])
                    hentry hgf hstacke hframee hmemE with
                  ⟨run, cf⟩ | ⟨hret, _⟩
                · exact .inl ⟨SFunc.RunP.callHalt s0 hg pop run, ChainFree.of_span span0 cf⟩
                · rcases hret with hret | hret
                  · exact (hret_no AVal.ret hret rfl).elim
                  · rw [hempty] at hret
                    simp only [List.map_nil, List.not_mem_nil] at hret
              | some i =>
                cases haidx : a'[i]? with
                | none =>
                  have hbad := hcheck.2
                  simp only [hidx, haidx, Bool.false_eq_true] at hbad
                | some av =>
                  cases av with
                  | ret =>
                    have hbad := hcheck.2
                    simp only [hidx, haidx, Bool.false_eq_true] at hbad
                  | unk =>
                    have hbad := hcheck.2
                    simp only [hidx, haidx, Bool.false_eq_true] at hbad
                  | const r =>
                    have hcall : callCompat r a' e.frame = true ∧
                        byteAt code r.toNat = some (Jinst.toUInt8 .jumpdest) ∧
                        checkNodeM code c.entries ms b m (r.toNat + 1)
                          (List.replicate e.rets .unk ++
                            a'.drop e.frame.length) [] d = true := by
                      simpa only [hidx, haidx, Bool.and_eq_true, beq_iff_eq] using hcheck.2
                    rcases frameMatches_callCompat hcall.1 htail with
                      ⟨Sf, Sr, hsplit, hframee, hframer⟩
                    have hstacke : inter.stack = Sf ++ (Sr ++ base) := by
                      rw [← hinter, hsplit, List.append_assoc]
                    rcases ih ⟨s0.toNat, sevm, inter, .ok post, exc'⟩
                        (Exec.Deriv.lt_of_prec prec) post rfl hcode hfork e.rets e.frame g r Sf
                        (Sr ++ base) (ms.getD k []) hentry hgf hstacke hframee
                        (by rw [hempty]; exact memMatches_nil _ _) with
                      ⟨run, cf⟩ | ⟨_, devm', exc'', hspan, run, Sret, hst, hlen⟩
                    · exact .inl ⟨SFunc.RunP.callHalt s0 hg pop run, ChainFree.of_span span0 cf⟩
                    · have hcont : FrameMatches ρ
                          (List.replicate e.rets .unk ++ a'.drop e.frame.length) (Sret ++ Sr) := by
                        apply matches_to_frame
                        rw [List.map_append]
                        apply matches_append
                        · rw [← hlen]
                          exact frameMatches_matches (frameMatches_unk_length Sret)
                        · exact frameMatches_matches hframer
                      have h_atd : Jinst.At sevm.code r.toNat .jumpdest := by
                        apply byteAt_jinst_at
                        rw [hcode]
                        exact hcall.2.1
                      rcases jumpdest_at_exact exc'' h_atd with ⟨inter2, exc2, burn2, _, prec2⟩
                      have hstackd : inter2.stack = (Sret ++ Sr) ++ base := by
                        rw [← burn2.stack, hst, List.append_assoc]
                      have hlt : Exec.Deriv.lt ⟨r.toNat, sevm, devm', .ok post, exc''⟩
                          ⟨pc, sevm, devm, .ok post, exc⟩ :=
                        lt_of_prefix_lt (Exec.Deriv.lt_of_prec prec) hspan.1
                      exact (ih ⟨r.toNat + 1, sevm, inter2, .ok post, exc2⟩
                        (deriv_lt_trans (Exec.Deriv.lt_of_prec prec2) hlt) post rfl hcode hfork m
                        (List.replicate e.rets .unk ++ a'.drop e.frame.length) d ρ (Sret ++ Sr)
                        base [] hcall.2.2 (execFreeIn_dest hff) hstackd hcont
                        (memMatches_nil _ _)).back
                        ((span0.trans hspan).trans
                          (span_of_prec prec2 (Blanc.Jinst.At.not_exec h_atd)))
                        (fun run' => SFunc.RunP.callRet s0 hg pop run (SFunc.RunP.dest burn2 run'))
                        (fun hret' => by
                          refine .inl (List.mem_cons_of_mem _ ?_)
                          rcases hret' with hret' | hret'
                          · rcases List.mem_append.mp hret' with h | h
                            · simp only [List.mem_replicate, ne_eq, reduceCtorEq,
                                and_false] at h
                            · exact List.mem_of_mem_drop h
                          · simp only [List.map_nil, List.not_mem_nil] at hret')
                        (fun _ q => ⟨SFunc.RunP.callRet s0 hg pop run
                          (SFunc.RunP.dest burn2 q.1), q.2⟩)
          | branch f g => simp only [checkNodeM, Bool.false_eq_true] at hcheck
          | branchTo f k' => simp only [checkNodeM, Bool.false_eq_true] at hcheck
          | last l => simp only [checkNodeM, Bool.false_eq_true] at hcheck
          | next n f => simp only [checkNodeM, Bool.false_eq_true] at hcheck
          | jump k' => simp only [checkNodeM, Bool.false_eq_true] at hcheck
          | callNext k' f => simp only [checkNodeM, Bool.false_eq_true] at hcheck
          | ret => simp only [checkNodeM, Bool.false_eq_true] at hcheck
          | pcAt p' f => simp only [checkNodeM, Bool.false_eq_true] at hcheck
          | undefined => simp only [checkNodeM, Bool.false_eq_true] at hcheck
    | ret =>
      cases a with
      | nil => simp only [checkNodeM, Bool.false_eq_true] at hcheck
      | cons av a' =>
        cases av with
        | const c => simp only [checkNodeM, Bool.false_eq_true] at hcheck
        | unk => simp only [checkNodeM, Bool.false_eq_true] at hcheck
        | ret =>
          have hcheck' : byteAt code pc = some (Jinst.toUInt8 .jump) ∧ a'.length = m := by
            simpa only [checkNodeM, Bool.and_eq_true, beq_iff_eq] using hcheck
          have h_at : Jinst.At sevm.code pc .jump := by
            apply byteAt_jinst_at
            rw [hcode]
            exact hcheck'.1
          obtain ⟨s0, S1, rfl, hs0, htail⟩ :
              ∃ s0 S1, S = s0 :: S1 ∧ s0 = ρ ∧ FrameMatches ρ a' S1 := by
            rcases hframe with _ | ⟨h0, ht⟩
            exact ⟨_, _, rfl, h0, ht⟩
          subst hs0
          rcases jump_at_exact exc h_at with ⟨x, inter, exc', pop, _, _, prec⟩
          have hpop := popBurn_one_stack pop
          rw [hstack] at hpop
          simp only [List.cons_append, List.cons.injEq] at hpop
          obtain ⟨rfl, hinter⟩ := hpop
          exact .inr ⟨by simp only [RetIn, List.mem_cons, true_or, List.mem_map,
              Prod.exists, exists_eq_right], inter, exc',
            span_of_prec prec (Blanc.Jinst.At.not_exec h_at), SFunc.RunP.ret s0 pop, S1,
            hinter.symm, (List.Forall₂.length_eq htail).symm.trans hcheck'.2⟩
    | pcAt p f =>
      have hcheck' :
          (bytesAt code pc (Ninst.toBytes (Ninst.reg .pc)) = true ∧ p = pc) ∧
            checkNodeM code c.entries ms b m (pc + 1) (.const (Nat.toB256 pc) :: a) μ f = true := by
        simpa only [checkNodeM, Bool.and_eq_true, beq_iff_eq] using hcheck
      obtain ⟨⟨hbytes, rfl⟩, hchild⟩ := hcheck'
      have h_at : Ninst.At sevm.code p (Ninst.reg .pc) := by
        apply Ninst.at_of_slice
        apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.reg .pc))
        rw [hcode]
        exact hbytes
      rcases pc_stepRun_of_at exc h_at with ⟨inter, exc', hstepPc, prec⟩
      have runS : Ninst.Run sevm devm (.reg .pc) inter := ⟨.none, trivial, p, hstepPc⟩
      have hstack' : inter.stack = Nat.toB256 p :: (S ++ base) := by
        rw [pc_stepRun_stack hstepPc, hstack]
      exact (ih ⟨p + 1, sevm, inter, .ok post, exc'⟩ (Exec.Deriv.lt_of_prec prec) post rfl hcode
        hfork m (.const (Nat.toB256 p) :: a) f ρ (Nat.toB256 p :: S) base μ hchild
        (execFreeIn_pcAt hfree) hstack' (List.Forall₂.cons rfl hframe)
        (hmem.of_memory_eq (pc_stepRun_memory hstepPc).symm)).back
        (span_of_prec prec (Ninst.At.not_exec_of_ne h_at (fun x hx => by cases hx)))
        (SFunc.RunP.pcAt runS hstepPc)
        (RetIn.of_frame (fun h => by simpa only [List.mem_cons, reduceCtorEq, false_or] using h))
        (fun _ q => ⟨SFunc.RunP.pcAt runS hstepPc q.1, q.2⟩)
    | undefined =>
      have hnone_code : code.getInst pc = none := by
        simpa only [checkNodeM, Option.isNone_iff_eq_none] using hcheck
      have hnone : sevm.code.getInst pc = none := by
        rw [hcode]
        exact hnone_code
      cases Exec.halt_inv exc (Evm.step_invOp (devm := devm) hnone)

/-! ## Corollaries: the direct children across the span -/

/-- **Exec-free node soundness with children.**  At a checked node of an exec-free tree, the
synthetic run either halts — and the frame spawns no direct child from the node on — or returns
to `ρ` at an actual node with the same remaining direct children. -/
theorem node_span_childFrames {code : ByteArray} {c : Cert} {ms : List MemMap} {b : Bool}
    {E : List Nat} (hc : Cert.CheckedM code c ms b) (hE : ExecFreeSet c.prog E = true)
    {pc : Nat} {sevm : Sevm} {d post : Devm} (exc : Exec pc sevm d (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    {m : Nat} {a : List AVal} {f : SFunc} {ρ : B256} {S base : List B256} {μ : MemMap}
    (hcheck : checkNodeM code c.entries ms b m pc a μ f = true) (hfree : f.execFreeIn E = true)
    (hstack : d.stack = S ++ base) (hframe : FrameMatches ρ a S)
    (hmem : MemMatches ρ μ d.memory) :
    (SFunc.Run c.prog sevm d f (.halted post) ∧ Exec.childFrames exc = []) ∨
    (∃ (d' : Devm) (exc' : Exec ρ.toNat sevm d' (.ok post)) (S' : List B256),
      SFunc.Run c.prog sevm d f (.returned d') ∧ Exec.childFrames exc' = Exec.childFrames exc ∧
      Exec.Deriv.ParentPrefix ⟨pc, sevm, d, .ok post, exc⟩ ⟨ρ.toNat, sevm, d', .ok post, exc'⟩ ∧
      d'.stack = S' ++ base ∧ S'.length = m) := by
  rcases node_spanM hc hE ⟨pc, sevm, d, .ok post, exc⟩ post rfl hcode hfork m a f ρ S base μ
      hcheck hfree hstack hframe hmem with
    ⟨run, cf⟩ | ⟨-, d', exc', span, run, S', hst, hlen⟩
  · exact .inl ⟨run, Exec.childFrames_eq_nil_of_free _ cf⟩
  · exact .inr ⟨d', exc', S', run, (Exec.Deriv.ExecFreeUntil.childFrames_eq span).symm, span.1,
      hst, hlen⟩

end Blanc.Lift
