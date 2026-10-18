import Blanc.Lift.ReachChain
import Blanc.Lift.CursorSourceRunReturn
import Blanc.Lift.Silent

/-!
# The first external instruction of a store-free region, and its silent aftermath

A frame whose code, from some point on, writes no storage before its first external instruction and
only state-silent code after it (`SFunc.silent`, closed in a `SilentSet`) keeps its world up to that
instruction and from the instruction's successor to its halt.  Contract-neutral, for the "model"
spawn shape (own steps, one external node, silent after) of code with loops and internal calls before
the call (the WETH9 precedent `Blanc/Lift/Weth9/CommittedSpawn.lean` walks a straight line instead).

* `SFunc.preIn ex Pre S`: a tree of the region before the call — state-silent instructions, gotos into
  `Pre`, external instructions accepted by `ex` followed by a silent tree, and internal calls either into
  silent code (then the region resumes) or into the region (then the continuation is silent);
* `Reach.firstExec`: a reach from such a tree, with silent pending continuations, to an external
  instruction keeps the state and arrives at a region tree;
* `CursorOK.state_post_of_silent`: from a cursor whose tree and continuations are silent, the frame's
  post state is the node's.
-/

namespace Blanc.Lift

open Jaune

/-- A silent tree whose references lie in `S`. -/
def SFunc.silentIn (S : List Nat) (f : SFunc) : Bool := f.silent && f.refs.all (· ∈ S)

/-- A tree of the store-free region before the external instruction. -/
def SFunc.preIn (ex : Xinst → Bool) (Pre S : List Nat) : SFunc → Bool
  | .next (.exec x) g => ex x && g.silentIn S
  | .next n f => n.stateSilent && f.preIn ex Pre S
  | .dest f => f.preIn ex Pre S
  | .branch f g => f.preIn ex Pre S && g.preIn ex Pre S
  | .branchTo f k => decide (k ∈ Pre) && f.preIn ex Pre S
  | .jump k => decide (k ∈ Pre)
  | .callNext k f => (decide (k ∈ S) && f.preIn ex Pre S) || (decide (k ∈ Pre) && f.silentIn S)
  | .last _ => true
  | .ret => true
  | .pcAt _ f => f.preIn ex Pre S
  | .undefined => true

/-- Every entry of `Pre` is a region tree. -/
def PreSet (fs : List SFunc) (ex : Xinst → Bool) (Pre S : List Nat) : Bool :=
  Pre.all fun k => match fs[k]? with
    | some g => g.preIn ex Pre S
    | none => false

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}

theorem SilentSet.lookup {S : List Nat} (hS : SilentSet fs S = true) {k : Nat} {g : SFunc}
    (hk : k ∈ S) (hg : fs[k]? = some g) : g.silentIn S = true := by
  have h := (List.all_eq_true.mp hS) k hk
  rw [hg] at h
  exact h

theorem PreSet.lookup {ex : Xinst → Bool} {Pre S : List Nat} (h : PreSet fs ex Pre S = true) {k : Nat}
    {g : SFunc} (hk : k ∈ Pre) (hg : fs[k]? = some g) : g.preIn ex Pre S = true := by
  have h' := (List.all_eq_true.mp h) k hk
  rw [hg] at h'
  exact h'

theorem SFunc.execFreeIn_of_silentIn {S : List Nat} :
    ∀ {f : SFunc}, f.silentIn S = true → f.execFreeIn S = true := by
  intro f
  induction f with
  | next n f ih =>
      intro h
      simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, Bool.and_eq_true] at h
      have hf := ih (by simp only [SFunc.silentIn, Bool.and_eq_true]; exact ⟨h.1.2, h.2⟩)
      cases n with
      | exec x => simp only [Ninst.stateSilent, Bool.false_eq_true, false_and] at h
      | _ => simpa only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs] using hf
  | branch f g ihf ihg =>
      intro h
      simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_append, Bool.and_eq_true] at h
      have a := ihf (by simp only [SFunc.silentIn, Bool.and_eq_true]; exact ⟨h.1.1, h.2.1⟩)
      have b := ihg (by simp only [SFunc.silentIn, Bool.and_eq_true]; exact ⟨h.1.2, h.2.2⟩)
      simp only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs, List.all_append,
        Bool.and_eq_true] at a b ⊢
      exact ⟨⟨a.1, b.1⟩, a.2, b.2⟩
  | branchTo f k ih =>
      intro h
      simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_cons, Bool.and_eq_true] at h
      have a := ih (by simp only [SFunc.silentIn, Bool.and_eq_true]; exact ⟨h.1, h.2.2⟩)
      simp only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs, List.all_cons,
        Bool.and_eq_true] at a ⊢
      exact ⟨a.1, h.2.1, a.2⟩
  | dest f ih =>
      intro h
      exact ih (by simpa only [SFunc.silentIn, SFunc.silent, SFunc.refs] using h)
  | callNext k f ih =>
      intro h
      simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_cons, Bool.and_eq_true] at h
      have a := ih (by simp only [SFunc.silentIn, Bool.and_eq_true]; exact ⟨h.1, h.2.2⟩)
      simp only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs, List.all_cons,
        Bool.and_eq_true] at a ⊢
      exact ⟨a.1, h.2.1, a.2⟩
  | pcAt p f ih =>
      intro h
      exact ih (by simpa only [SFunc.silentIn, SFunc.silent, SFunc.refs] using h)
  | jump k =>
      intro h
      simpa only [SFunc.silentIn, SFunc.silent, SFunc.refs, SFunc.execFreeIn, SFunc.execsSatisfy,
        Bool.true_and] using h
  | last l => intro _; rfl
  | ret => intro _; rfl
  | undefined => intro _; rfl

theorem ExecFreeSet.of_silentSet {S : List Nat} (hS : SilentSet fs S = true) :
    ExecFreeSet fs S = true := by
  refine List.all_eq_true.mpr fun k hk => ?_
  have h := (List.all_eq_true.mp hS) k hk
  split at h
  · rename_i g hg
    simp only [hg]
    exact SFunc.execFreeIn_of_silentIn h
  · rename_i hg
    simp only [hg]
    exact h

/-- One state-silent instruction keeps the world. -/
theorem state_of_stateSilent (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {d d' : Devm}
    {n : Ninst} (hn : n.stateSilent = true) (h : P sevm d n d') : d'.state = d.state := by
  have run : SFunc.RunP P ([] : List SFunc) sevm d (.next n (.last .stop)) (.halted d') :=
    .next h (.last rfl)
  exact SFunc.RunP.state_of_silent hP (S := []) rfl
    (by simp only [SFunc.silent, hn, Bool.true_and]; rfl) rfl run

/-- **The first external instruction of a store-free region.**  A reach from a region tree (or from
silent code that will return into one), over silent pending continuations, to a configuration about
to run an external instruction keeps the world, and arrives at a region tree over silent
continuations. -/
theorem Reach.firstExec (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {ex : Xinst → Bool}
    {Pre S : List Nat} (hPre : PreSet fs ex Pre S = true) (hS : SilentSet fs S = true) {w : State} :
    ∀ {a T : Conf}, Reach P fs sevm a T → AtExec T → a.d.state = w →
      ((a.f.preIn ex Pre S = true ∧ ∀ s ∈ a.K, s.silentIn S = true) ∨
        (a.f.silentIn S = true ∧ ∃ Fs p Ps, a.K = Fs ++ p :: Ps ∧ (∀ s ∈ Fs, s.silentIn S = true) ∧
          p.preIn ex Pre S = true ∧ ∀ s ∈ Ps, s.silentIn S = true)) →
      T.d.state = w ∧ T.f.preIn ex Pre S = true ∧ ∀ s ∈ T.K, s.silentIn S = true := by
  have hE := ExecFreeSet.of_silentSet hS
  intro a T h hT
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro hw hm
      rcases hm with ⟨hf, hK⟩ | ⟨hf, -⟩
      · exact ⟨hw, hf, hK⟩
      · obtain ⟨x, g, hx⟩ := hT
        rw [hx] at hf
        simp only [SFunc.silentIn, SFunc.silent, Ninst.stateSilent, Bool.false_and,
          Bool.false_eq_true] at hf
  | @head a b step rest ih =>
    intro hw hm
    have quiet : b.f.silentIn S = true → (∀ s ∈ b.K, s.silentIn S = true) → False := fun hf hK =>
      Reach.false_of_execFree hE rest hT (SFunc.execFreeIn_of_silentIn hf)
        (fun s hs => SFunc.execFreeIn_of_silentIn (hK s hs))
    obtain ⟨d, f, K⟩ := a
    dsimp only at hw hm
    rcases hm with ⟨hf, hK⟩ | ⟨hf, Fs, p, Ps, hKs, hFs, hp, hPs⟩
    · -- the region
      cases step with
      | @next _ d' n f' _ hstep =>
          cases n with
          | exec x =>
              simp only [SFunc.preIn, Bool.and_eq_true] at hf
              exact (quiet hf.2 hK).elim
          | _ =>
              simp only [SFunc.preIn, Bool.and_eq_true] at hf
              exact ih (by rw [state_of_stateSilent hP hf.1 hstep]; exact hw) (.inl ⟨hf.2, hK⟩)
      | dest burn => exact ih (burn.state.symm.trans hw) (.inl ⟨hf, hK⟩)
      | zero t pop =>
          simp only [SFunc.preIn, Bool.and_eq_true] at hf
          exact ih (pop.state.symm.trans hw) (.inl ⟨hf.1, hK⟩)
      | succ t w' hw' pop =>
          simp only [SFunc.preIn, Bool.and_eq_true] at hf
          exact ih (pop.state.symm.trans hw) (.inl ⟨hf.2, hK⟩)
      | toZero t pop =>
          simp only [SFunc.preIn, Bool.and_eq_true] at hf
          exact ih (pop.state.symm.trans hw) (.inl ⟨hf.2, hK⟩)
      | toSucc t w' hw' hk pop =>
          simp only [SFunc.preIn, Bool.and_eq_true, decide_eq_true_eq] at hf
          exact ih (pop.state.symm.trans hw) (.inl ⟨PreSet.lookup hPre hf.1 hk, hK⟩)
      | jump t hk pop =>
          simp only [SFunc.preIn, decide_eq_true_eq] at hf
          exact ih (pop.state.symm.trans hw) (.inl ⟨PreSet.lookup hPre hf hk, hK⟩)
      | call t hk pop =>
          simp only [SFunc.preIn, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hf
          rcases hf with ⟨hkS, hf'⟩ | ⟨hkP, hf'⟩
          · exact ih (pop.state.symm.trans hw)
              (.inr ⟨SilentSet.lookup hS hkS hk, [], _, K, rfl, (fun _ h => nomatch h), hf', hK⟩)
          · refine ih (pop.state.symm.trans hw) (.inl ⟨PreSet.lookup hPre hkP hk, fun s hs => ?_⟩)
            rcases List.mem_cons.mp hs with rfl | hs
            · exact hf'
            · exact hK s hs
      | ret t pop =>
          exact (quiet (hK _ List.mem_cons_self) fun s hs => hK s (List.mem_cons_of_mem _ hs)).elim
      | pcAt hstep _ =>
          exact ih (by rw [state_of_stateSilent hP rfl hstep]; exact hw) (.inl ⟨hf, hK⟩)
    · -- silent code that will return into the region
      have keep : ∀ {f' : SFunc}, f'.silentIn S = true →
          (f'.silentIn S = true ∧ ∃ Fs p Ps, K = Fs ++ p :: Ps ∧ (∀ s ∈ Fs, s.silentIn S = true) ∧
            p.preIn ex Pre S = true ∧ ∀ s ∈ Ps, s.silentIn S = true) :=
        fun h => ⟨h, Fs, p, Ps, hKs, hFs, hp, hPs⟩
      cases step with
      | @next _ d' n f' _ hstep =>
          simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, Bool.and_eq_true] at hf
          exact ih (by rw [state_of_stateSilent hP hf.1.1 hstep]; exact hw)
            (.inr (keep (by simp only [SFunc.silentIn, Bool.and_eq_true]; exact ⟨hf.1.2, hf.2⟩)))
      | dest burn =>
          exact ih (burn.state.symm.trans hw)
            (.inr (keep (by simpa only [SFunc.silentIn, SFunc.silent, SFunc.refs] using hf)))
      | zero t pop =>
          simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_append, Bool.and_eq_true] at hf
          exact ih (pop.state.symm.trans hw)
            (.inr (keep (by simp only [SFunc.silentIn, Bool.and_eq_true]; exact ⟨hf.1.1, hf.2.1⟩)))
      | succ t w' hw' pop =>
          simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_append, Bool.and_eq_true] at hf
          exact ih (pop.state.symm.trans hw)
            (.inr (keep (by simp only [SFunc.silentIn, Bool.and_eq_true]; exact ⟨hf.1.2, hf.2.2⟩)))
      | toZero t pop =>
          simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_cons, Bool.and_eq_true] at hf
          exact ih (pop.state.symm.trans hw)
            (.inr (keep (by simp only [SFunc.silentIn, Bool.and_eq_true]; exact ⟨hf.1, hf.2.2⟩)))
      | toSucc t w' hw' hk pop =>
          simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_cons, Bool.and_eq_true,
            decide_eq_true_eq] at hf
          exact ih (pop.state.symm.trans hw) (.inr (keep (SilentSet.lookup hS hf.2.1 hk)))
      | jump t hk pop =>
          simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_cons, List.all_nil,
            Bool.and_true, Bool.true_and, decide_eq_true_eq] at hf
          exact ih (pop.state.symm.trans hw) (.inr (keep (SilentSet.lookup hS hf hk)))
      | @call _ d' f' g k _ t hk pop =>
          simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_cons, Bool.and_eq_true,
            decide_eq_true_eq] at hf
          refine ih (pop.state.symm.trans hw)
            (.inr ⟨SilentSet.lookup hS hf.2.1 hk, f' :: Fs, p, Ps, by rw [hKs]; rfl, fun s hs => ?_, hp, hPs⟩)
          rcases List.mem_cons.mp hs with rfl | hs
          · simp only [SFunc.silentIn, Bool.and_eq_true]; exact ⟨hf.1, hf.2.2⟩
          · exact hFs s hs
      | @ret _ d' f' K' t pop =>
          cases Fs with
          | nil =>
              simp only [List.nil_append, List.cons.injEq] at hKs
              obtain ⟨rfl, rfl⟩ := hKs
              exact ih (pop.state.symm.trans hw) (.inl ⟨hp, hPs⟩)
          | cons s Fs' =>
              simp only [List.cons_append, List.cons.injEq] at hKs
              obtain ⟨rfl, rfl⟩ := hKs
              exact ih (pop.state.symm.trans hw)
                (.inr ⟨hFs _ List.mem_cons_self, Fs', p, Ps, rfl,
                  fun s hs => hFs s (List.mem_cons_of_mem _ hs), hp, hPs⟩)
      | pcAt hstep _ =>
          exact ih (by rw [state_of_stateSilent hP rfl hstep]; exact hw)
            (.inr (keep (by simpa only [SFunc.silentIn, SFunc.silent, SFunc.refs] using hf)))

/-- **The post state of a silent tail.**  From a cursor-placed node of a successful frame whose tree
and pending continuations are silent in a `SilentSet`, the frame's post state is the node's. -/
theorem CursorOK.state_post_of_silent {code : ByteArray} {c : Cert} (checked : Cert.check code c = true)
    {S : List Nat} (hS : SilentSet c.prog S = true) {post : Devm} :
    ∀ (n : Nat) {F : Exec.Deriv} {κ : Cursor}, κ.K.length = n → CursorOK code c F κ →
      F.exn = .ok post → CoveredFork F.sevm.benvStat.fork → κ.f.silentIn S = true →
      (∀ s ∈ κ.K.map Cont.f, s.silentIn S = true) → post.state = F.devm.state := by
  intro n
  induction n with
  | zero =>
      intro F κ hn placed success fork hf hK
      rcases placed.sourceRunReturn checked success fork with halted | ⟨cont, tail, -, -, hKe, -⟩
      · simp only [SFunc.silentIn, Bool.and_eq_true] at hf
        exact SFunc.RunP.state_of_silent StepIn.toRun hS hf.1 hf.2 halted
      · rw [hKe] at hn
        cases hn
  | succ n ih =>
      intro F κ hn placed success fork hf hK
      simp only [SFunc.silentIn, Bool.and_eq_true] at hf
      rcases placed.sourceRunReturn checked success fork with halted |
          ⟨cont, tail, state, run, hKe, -, -, returned, placedC⟩
      · exact SFunc.RunP.state_of_silent StepIn.toRun hS hf.1 hf.2 halted
      · have h1 := SFunc.RunP.state_of_silent StepIn.toRun hS hf.1 hf.2 returned
        rw [hKe] at hn hK
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hn
        simp only [List.map_cons, List.mem_cons, forall_eq_or_imp] at hK
        exact (ih hn placedC rfl fork hK.1 hK.2).trans h1

end Blanc.Lift
