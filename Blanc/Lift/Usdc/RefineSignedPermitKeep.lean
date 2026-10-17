import Blanc.Lift.ReachWalk
import Blanc.Lift.Silent
import Blanc.Lift.ShuffleSkip
import Blanc.Lift.FrameSkip

/-!
# A reach to the first external instruction of a state-keeping region

A node-clause fact (`ImplStepLaw`) is a statement about the machine at an external-instruction
node of a frame's own chain; `reach_of_parentPrefix` (`Blanc/Lift/Cursor.lean`) places that node at
a `Reach` of the certificate.  When the code from some configuration up to the external instruction
writes no state, the node's world state is that configuration's, whatever the stack, the memory and
the number of loop iterations in between.

`SFunc.keepTo xok W Sil E` says a tree runs state-silent instructions, gotos into the entries `W`
(whose trees are of the same kind, `KeepSet`), internal calls of state-silent entries `Sil`
(`SilentSet`) with a continuation of the same kind, internal calls of `W` entries whose
continuation is exec-free in `E` (`ExecFreeSet`), returns, halts, and external instructions `x`
with `xok x` after which it is exec-free in `E`.  `Reach.keepTo`: a reach from such a tree, over
exec-free pending continuations, to an external instruction keeps the world state and stands at an
instruction accepted by `xok`.  Loops cost nothing: the argument is an induction over the reach.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- `n` is an external instruction accepted by `xok`. -/
def _root_.Jaune.Ninst.execOk (xok : Xinst → Bool) : Ninst → Bool
  | .exec x => xok x
  | _ => false

/-- A state-silent tree whose entry references lie in `Sil`. -/
def SFunc.silentIn (Sil : List Nat) (f : SFunc) : Bool := f.silent && f.refs.all (· ∈ Sil)

/-- A state-keeping region up to an accepted external instruction (see the module doc). -/
def SFunc.keepTo (xok : Xinst → Bool) (W Sil E : List Nat) : SFunc → Bool
  | .branch f g => f.keepTo xok W Sil E && g.keepTo xok W Sil E
  | .branchTo f k => decide (k ∈ W) && f.keepTo xok W Sil E
  | .last _ => true
  | .next n f => (n.stateSilent && f.keepTo xok W Sil E) || (n.execOk xok && f.execFreeIn E)
  | .dest f => f.keepTo xok W Sil E
  | .jump k => decide (k ∈ W)
  | .callNext k f =>
      (decide (k ∈ Sil) && f.keepTo xok W Sil E) || (decide (k ∈ W) && f.execFreeIn E)
  | .ret => true
  | .pcAt _ f => f.keepTo xok W Sil E
  | .undefined => true

/-- Every entry of `W` is a state-keeping region. -/
def KeepSet (fs : List SFunc) (xok : Xinst → Bool) (W Sil E : List Nat) : Bool :=
  W.all fun k => match fs[k]? with
    | some g => g.keepTo xok W Sil E
    | none => false

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}

theorem KeepSet.lookup {xok : Xinst → Bool} {W Sil E : List Nat}
    (h : KeepSet fs xok W Sil E = true) {k : Nat} {g : SFunc} (hk : k ∈ W)
    (hg : fs[k]? = some g) : g.keepTo xok W Sil E = true := by
  have h' := (List.all_eq_true.mp h) k hk
  rw [hg] at h'
  exact h'

theorem SilentSet.lookupIn {Sil : List Nat} (h : SilentSet fs Sil = true) {k : Nat} {g : SFunc}
    (hk : k ∈ Sil) (hg : fs[k]? = some g) : g.silentIn Sil = true := by
  have h' := (List.all_eq_true.mp h) k hk
  rw [hg] at h'
  exact h'

/-- The invariant of `Reach.keepTo`: inside the region at the configuration's stack, or inside a
silent callee entered from it. -/
private abbrev KeepInv (xok : Xinst → Bool) (W Sil E : List Nat) (s0 : State) (a : Conf) : Prop :=
  a.d.state = s0 ∧
    ((a.f.keepTo xok W Sil E = true ∧ ∀ s ∈ a.K, s.execFreeIn E = true) ∨
      (a.f.silentIn Sil = true ∧ ∃ L g B, a.K = L ++ g :: B ∧ (∀ s ∈ L, s.silentIn Sil = true) ∧
        g.keepTo xok W Sil E = true ∧ ∀ s ∈ B, s.execFreeIn E = true))

/-- **A reach out of a state-keeping region.**  From a `keepTo` tree over exec-free pending
continuations, a reach to an external instruction keeps the world state, and the instruction is
accepted by `xok`. -/
theorem Reach.keepTo (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {xok : Xinst → Bool}
    {W Sil E : List Nat} (hW : KeepSet fs xok W Sil E = true) (hSil : SilentSet fs Sil = true)
    (hE : ExecFreeSet fs E = true) {d : Devm} {f : SFunc} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, f, K⟩ T) (hT : AtExec T) (hf : f.keepTo xok W Sil E = true)
    (hK : ∀ s ∈ K, s.execFreeIn E = true) :
    T.d.state = d.state ∧ ∃ x f', T.f = .next (.exec x) f' ∧ xok x = true := by
  suffices ∀ {a : Conf}, Reach P fs sevm a T → KeepInv xok W Sil E d.state a →
      T.d.state = d.state ∧ ∃ x f', T.f = .next (.exec x) f' ∧ xok x = true from
    this h ⟨rfl, .inl ⟨hf, hK⟩⟩
  intro a h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      rintro ⟨hs, hA | ⟨hS, -⟩⟩
      · obtain ⟨x, f', hx⟩ := hT
        refine ⟨hs, x, f', hx, ?_⟩
        rw [hx] at hA
        have e := hA.1
        simp only [SFunc.keepTo, Ninst.stateSilent, Bool.false_and, Bool.false_or, Ninst.execOk,
          Bool.and_eq_true] at e
        exact e.1
      · obtain ⟨x, f', hx⟩ := hT
        rw [hx] at hS
        simp only [SFunc.silentIn, SFunc.silent, Ninst.stateSilent, Bool.false_and,
          Bool.false_eq_true] at hS
  | @head a b step rest ih =>
      rintro ⟨hs, hA | ⟨hS, L, g0, B, hKb, hL, hg0, hB⟩⟩
      · obtain ⟨hf, hK⟩ := hA
        cases step with
        | @next d d' n f K hp =>
            simp only [SFunc.keepTo, Bool.or_eq_true, Bool.and_eq_true] at hf
            rcases hf with ⟨hn, hf⟩ | ⟨hn, hf⟩
            · exact ih ⟨(ninst_state_of_stateSilent hn (hP hp)).trans hs, .inl ⟨hf, hK⟩⟩
            · exact (Reach.false_of_execFree hE rest hT hf hK).elim
        | dest burn => exact ih ⟨burn.state.symm.trans hs, .inl ⟨hf, hK⟩⟩
        | zero t pop =>
            simp only [SFunc.keepTo, Bool.and_eq_true] at hf
            exact ih ⟨pop.state.symm.trans hs, .inl ⟨hf.1, hK⟩⟩
        | succ t w hw pop =>
            simp only [SFunc.keepTo, Bool.and_eq_true] at hf
            exact ih ⟨pop.state.symm.trans hs, .inl ⟨hf.2, hK⟩⟩
        | toZero t pop =>
            simp only [SFunc.keepTo, Bool.and_eq_true] at hf
            exact ih ⟨pop.state.symm.trans hs, .inl ⟨hf.2, hK⟩⟩
        | toSucc t w hw hk pop =>
            simp only [SFunc.keepTo, Bool.and_eq_true, decide_eq_true_eq] at hf
            exact ih ⟨pop.state.symm.trans hs, .inl ⟨KeepSet.lookup hW hf.1 hk, hK⟩⟩
        | jump t hk pop =>
            simp only [SFunc.keepTo, decide_eq_true_eq] at hf
            exact ih ⟨pop.state.symm.trans hs, .inl ⟨KeepSet.lookup hW hf hk, hK⟩⟩
        | @call d d' f g k K t hk pop =>
            simp only [SFunc.keepTo, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hf
            rcases hf with ⟨hkS, hf⟩ | ⟨hkW, hf⟩
            · exact ih ⟨pop.state.symm.trans hs, .inr ⟨SilentSet.lookupIn hSil hkS hk, [], f, K, rfl,
                fun _ hm => absurd hm List.not_mem_nil, hf, hK⟩⟩
            · refine ih ⟨pop.state.symm.trans hs, .inl ⟨KeepSet.lookup hW hkW hk, fun s hm => ?_⟩⟩
              rcases List.mem_cons.mp hm with rfl | hm
              · exact hf
              · exact hK s hm
        | ret t pop =>
            exact (Reach.false_of_execFree hE rest hT (hK _ List.mem_cons_self)
              (fun s hm => hK s (List.mem_cons_of_mem _ hm))).elim
        | pcAt hp hr =>
            exact ih ⟨(ninst_state_of_stateSilent (n := .reg .pc) rfl (hP hp)).trans hs,
              .inl ⟨hf, hK⟩⟩
      · cases step with
        | @next d d' n f K hp =>
            simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, Bool.and_eq_true] at hS
            exact ih ⟨(ninst_state_of_stateSilent hS.1.1 (hP hp)).trans hs,
              .inr ⟨by simp only [SFunc.silentIn, hS.1.2, hS.2, Bool.and_self], L, g0, B, hKb, hL,
                hg0, hB⟩⟩
        | dest burn =>
            exact ih ⟨burn.state.symm.trans hs, .inr ⟨by simpa only [SFunc.silentIn, SFunc.silent,
              SFunc.refs] using hS, L, g0, B, hKb, hL, hg0, hB⟩⟩
        | zero t pop =>
            simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_append,
              Bool.and_eq_true] at hS
            exact ih ⟨pop.state.symm.trans hs, .inr ⟨by simp only [SFunc.silentIn, hS.1.1, hS.2.1,
              Bool.and_self], L, g0, B, hKb, hL, hg0, hB⟩⟩
        | succ t w hw pop =>
            simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_append,
              Bool.and_eq_true] at hS
            exact ih ⟨pop.state.symm.trans hs, .inr ⟨by simp only [SFunc.silentIn, hS.1.2, hS.2.2,
              Bool.and_self], L, g0, B, hKb, hL, hg0, hB⟩⟩
        | toZero t pop =>
            simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_cons,
              Bool.and_eq_true] at hS
            exact ih ⟨pop.state.symm.trans hs, .inr ⟨by simp only [SFunc.silentIn, hS.1, hS.2.2,
              Bool.and_self], L, g0, B, hKb, hL, hg0, hB⟩⟩
        | toSucc t w hw hk pop =>
            simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_cons, Bool.and_eq_true,
              decide_eq_true_eq] at hS
            exact ih ⟨pop.state.symm.trans hs, .inr ⟨SilentSet.lookupIn hSil hS.2.1 hk, L, g0, B, hKb, hL,
              hg0, hB⟩⟩
        | jump t hk pop =>
            simp only [SFunc.silentIn, SFunc.refs, List.all_cons, List.all_nil, Bool.and_true,
              Bool.and_eq_true, decide_eq_true_eq] at hS
            exact ih ⟨pop.state.symm.trans hs, .inr ⟨SilentSet.lookupIn hSil hS.2 hk, L, g0, B, hKb, hL,
              hg0, hB⟩⟩
        | @call d d' f g k K t hk pop =>
            simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_cons, Bool.and_eq_true,
              decide_eq_true_eq] at hS
            refine ih ⟨pop.state.symm.trans hs, .inr ⟨SilentSet.lookupIn hSil hS.2.1 hk, f :: L, g0, B,
              congrArg (List.cons f) hKb, fun s hm => ?_, hg0, hB⟩⟩
            rcases List.mem_cons.mp hm with rfl | hm
            · simp only [SFunc.silentIn, hS.1, hS.2.2, Bool.and_self]
            · exact hL s hm
        | @ret d d' f K t pop =>
            cases L with
            | nil =>
                simp only [List.nil_append, List.cons.injEq] at hKb
                obtain ⟨rfl, rfl⟩ := hKb
                exact ih ⟨pop.state.symm.trans hs, .inl ⟨hg0, hB⟩⟩
            | cons s L =>
                simp only [List.cons_append, List.cons.injEq] at hKb
                obtain ⟨rfl, rfl⟩ := hKb
                exact ih ⟨pop.state.symm.trans hs, .inr ⟨hL _ List.mem_cons_self, L, g0, B, rfl,
                  fun s' hm => hL s' (List.mem_cons_of_mem _ hm), hg0, hB⟩⟩
        | pcAt hp hr =>
            exact ih ⟨(ninst_state_of_stateSilent (n := .reg .pc) rfl (hP hp)).trans hs,
              .inr ⟨by simpa only [SFunc.silentIn, SFunc.silent, SFunc.refs] using hS, L, g0, B,
                hKb, hL, hg0, hB⟩⟩

/-! ## Shuffle segments on a reach -/

section ReachShuffle

open AbstractStackSafety

variable {es : List Entry} {Fw : List Nat} {tgt : SFunc} {pB : Nat} {X R : List B256} {T : Conf}
  {K : List SFunc}

/-- What a checked result promises for a reach to an external instruction from `d0`. -/
def ShReachR (fs : List SFunc) (sevm : Sevm) (P : Sevm → Devm → Ninst → Devm → Prop)
    (X R : List B256) (d0 : Devm) (tgt : SFunc) (K : List SFunc) (T : Conf) :
    Option (List SVal) → Prop
  | none => False
  | some π => ∃ d, d.state = d0.state ∧ ∃ Y, d.stack = Y ++ R ∧ Carried X π Y ∧
      Reach P fs sevm ⟨d, tgt, K⟩ T

theorem ShReachR.mono {d0 : Devm} {o o' : Option (List SVal)}
    (h : ShReachR fs sevm P X R d0 tgt K T o) (hle : ShLe o o') :
    ShReachR fs sevm P X R d0 tgt K T o' := by
  match o, o', h, hle with
  | some _, some _, ⟨d, hs, Y, hst, hY, run⟩, hle => exact ⟨d, hs, Y, hst, hY.mono hle, run⟩

theorem ShReachR.state {d0 d1 : Devm} {o : Option (List SVal)}
    (h : ShReachR fs sevm P X R d1 tgt K T o) (hs : d1.state = d0.state) :
    ShReachR fs sevm P X R d0 tgt K T o := by
  match o, h with
  | some _, ⟨d, hd, rest⟩ => exact ⟨d, hd.trans hs, rest⟩

theorem shNinst_not_exec {n : Ninst} {a a' : List SVal} (h : shNinst n a = some a') :
    ∀ x, n ≠ .exec x := by
  rintro x rfl
  simp only [shNinst, Ninst.stateSilent, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    reduceCtorEq] at h

/-- **Soundness of the shuffle checker on a reach** to an external instruction: the reach passes
through the target. -/
theorem rshuffle_sound (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (fork : CoveredFork sevm.benvStat.fork) (hT : AtExec T) :
    ∀ (fuel pc : Nat) (a : List SVal) (f : SFunc) (o : Option (List SVal)) (d : Devm)
      (Y : List B256), shuffle fs es Fw tgt pB fuel pc a f = some o →
      Reach P fs sevm ⟨d, f, K⟩ T → d.stack = Y ++ R → Carried X a Y →
      ShReachR fs sevm P X R d tgt K T o := by
  intro fuel
  induction fuel with
  | zero => intro pc a f o d Y h; simp only [shuffle, reduceCtorEq] at h
  | succ fuel ih =>
    intro pc a f o d Y h run hst hY
    simp only [shuffle] at h
    split at h
    · split at h
      · rename_i hsame
        simp only [Option.some.injEq] at h
        subst h
        rw [SFunc.eq_of_same hsame] at run
        exact ⟨d, rfl, Y, hst, hY, run⟩
      · cases h
    · cases f with
      | next n g =>
        simp only at h
        obtain ⟨a', hn, h'⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨d', hrun, rest⟩ := Reach.next (shNinst_not_exec hn) run hT
        obtain ⟨hs, Y', hst', hY'⟩ := shNinst_run fork hn hst hY (hP hrun)
        exact (ih _ _ _ _ _ _ h' rest hst' hY').state hs
      | dest g =>
        simp only at h
        obtain ⟨d', burn, rest⟩ := Reach.dest run hT
        exact (ih _ _ _ _ _ _ h rest (by rw [← burn.stack, hst]) hY).state burn.state.symm
      | branch g g' =>
        rcases a with _ | ⟨t, _ | ⟨v, a⟩⟩
        · simp only [reduceCtorEq] at h
        · simp only [reduceCtorEq] at h
        · simp only at h
          rcases hY with _ | ⟨_, hY1⟩
          rcases hY1 with _ | ⟨hv, hY'⟩
          rename_i y0 Y0 y1 Y'
          rcases Reach.branch run hT with ⟨dd, d', pop, rest⟩ | ⟨dd, w, d', hw, pop, rest⟩
          · have hp := popBurn_two_stack pop
            rw [hst] at hp
            simp only [List.cons_append, List.cons.injEq] at hp
            obtain ⟨_, rfl, hp⟩ := hp
            obtain ⟨o0, h0, hle⟩ := shBranch_zero h hv
            exact ((ih _ _ _ _ _ _ h0 rest hp.symm hY').mono hle).state pop.state.symm
          · have hp := popBurn_two_stack pop
            rw [hst] at hp
            simp only [List.cons_append, List.cons.injEq] at hp
            obtain ⟨_, rfl, hp⟩ := hp
            obtain ⟨o1, h1, hle⟩ := shBranch_succ h hv hw
            exact ((ih _ _ _ _ _ _ h1 rest hp.symm hY').mono hle).state pop.state.symm
      | branchTo g k =>
        rcases a with _ | ⟨t, _ | ⟨v, a⟩⟩
        · simp only [reduceCtorEq] at h
        · simp only [reduceCtorEq] at h
        · simp only at h
          rcases hY with _ | ⟨_, hY1⟩
          rcases hY1 with _ | ⟨hv, hY'⟩
          rename_i y0 Y0 y1 Y'
          cases hk : fs[k]? with
          | none => simp only [hk, reduceCtorEq] at h
          | some g' =>
            cases he : es[k]? with
            | none => simp only [hk, he, reduceCtorEq] at h
            | some e =>
              simp only [hk, he] at h
              split at h
              · rcases Reach.branchTo run hT with ⟨dd, d', pop, rest⟩ |
                  ⟨dd, w, g'', d', hw, hk', pop, rest⟩
                · have hp := popBurn_two_stack pop
                  rw [hst] at hp
                  simp only [List.cons_append, List.cons.injEq] at hp
                  obtain ⟨_, rfl, hp⟩ := hp
                  obtain ⟨o0, h0, hle⟩ := shBranch_zero h hv
                  exact ((ih _ _ _ _ _ _ h0 rest hp.symm hY').mono hle).state pop.state.symm
                · rw [hk] at hk'
                  cases hk'
                  have hp := popBurn_two_stack pop
                  rw [hst] at hp
                  simp only [List.cons_append, List.cons.injEq] at hp
                  obtain ⟨_, rfl, hp⟩ := hp
                  obtain ⟨o1, h1, hle⟩ := shBranch_succ h hv hw
                  exact ((ih _ _ _ _ _ _ h1 rest hp.symm hY').mono hle).state pop.state.symm
              · cases h
      | jump k =>
        rcases a with _ | ⟨t, a⟩
        · simp only [reduceCtorEq] at h
        · simp only at h
          rcases hY with _ | ⟨_, hY'⟩
          rename_i y0 Y'
          cases hk : fs[k]? with
          | none => simp only [hk, reduceCtorEq] at h
          | some g' =>
            cases he : es[k]? with
            | none => simp only [hk, he, reduceCtorEq] at h
            | some e =>
              simp only [hk, he] at h
              split at h
              · obtain ⟨dd, g'', d', hk', pop, rest⟩ := Reach.jump run hT
                rw [hk] at hk'
                cases hk'
                have hp := popBurn_one_stack pop
                rw [hst] at hp
                simp only [List.cons_append, List.cons.injEq] at hp
                exact (ih _ _ _ _ _ _ h rest hp.2.symm hY').state pop.state.symm
              · cases h
      | last l => exact (Reach.not_last run hT).elim
      | undefined =>
        rcases Relation.ReflTransGen.cases_head run with rfl | ⟨c, step, -⟩
        · obtain ⟨x, f', hx⟩ := hT
          cases hx
        · cases step
      | callNext _ _ => simp only [reduceCtorEq] at h
      | ret => simp only [reduceCtorEq] at h
      | pcAt _ _ => simp only [reduceCtorEq] at h

/-- **The shuffle skip on a reach** to an external instruction. -/
theorem rr_shuffle (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {f : SFunc}
    {pA fuel n : Nat} {π : List SVal} (fork : CoveredFork sevm.benvStat.fork) (hT : AtExec T)
    (hchk : shuffle fs es Fw tgt pB fuel pA (argFrame n) f = some (some π))
    (hX : X.length = n) {b : Devm} {M : Mem} {G : Nat}
    (run : Reach P fs sevm ⟨St b (X ++ R) M G, f, K⟩ T) :
    ∃ b' Y M' G', b'.state = b.state ∧ Carried X π Y ∧
      Reach P fs sevm ⟨St b' (Y ++ R) M' G', tgt, K⟩ T := by
  subst hX
  obtain ⟨d, hs, Y, hst, hY, run'⟩ :=
    rshuffle_sound hP fork hT _ _ _ _ _ _ _ hchk run rfl (carried_argFrame X)
  refine ⟨d, Y, d.memory, d.gasLeft, hs, hY, ?_⟩
  rw [← St.self hst rfl]
  exact run'

end ReachShuffle

/-- **Crossing a silent, exec-free internal call on a reach** to an external instruction: the
callee returns, and the reach continues from a state with the caller's world state and the stack
`Y ++ S.drop e.frame.length`, `Y.length = e.rets`. -/
theorem rr_call_silent (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {code : ByteArray}
    {c : Cert} (hc : Cert.check code c = true) (fork : CoveredFork sevm.benvStat.fork)
    {Sk E : List Nat} (hS : SilentSet c.prog Sk = true) (hE : ExecFreeSet c.prog E = true)
    {k : Nat} (hkS : k ∈ Sk) (hkE : k ∈ E) {e : Entry} {g : SFunc} (he : c.entries[k]? = some e)
    (hg : c.prog[k]? = some g) {b : Devm} {S : List B256} {M : Mem} {G : Nat} {dd ρ : B256}
    {f : SFunc} {K : List SFunc} {T : Conf}
    (hframe : FrameMatches ρ e.frame (S.take e.frame.length)) (hT : AtExec T)
    (run : Reach P c.prog sevm ⟨St b (dd :: S) M G, .callNext k f, K⟩ T) :
    ∃ b' Y M' G', b'.state = b.state ∧ Y.length = e.rets ∧
      Reach P c.prog sevm ⟨St b' (Y ++ S.drop e.frame.length) M' G', f, K⟩ T := by
  obtain ⟨G', D, callee, rest⟩ := rr_callOver hE hg hkE run hT
  have hgS : g.silent = true ∧ g.refs.all (· ∈ Sk) = true := by
    have h := (List.all_eq_true.mp hS) k hkS
    rw [hg] at h
    simpa only [Bool.and_eq_true] using h
  have hstate := SFunc.RunP.state_of_silent hP hS hgS.1 hgS.2 callee
  obtain ⟨Y, hY, hlen⟩ := callee.entry_stack_below hP hc fork he hg
    (List.take_append_drop _ _).symm hframe
  rw [St.stack] at hY
  refine ⟨D, Y, D.memory, D.gasLeft, hstate, hlen, ?_⟩
  rw [← St.self hY rfl]
  exact rest

end Blanc.Lift
