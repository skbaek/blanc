import Blanc.ReachDispatchPrefix

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

/-! Contract-neutral prefixes for the selector dispatcher and its guards. -/

theorem run_prefix_prepend {fs : List Func} {e : Sevm} {s r : Devm}
    {l : Line} {p : Func} {path : Prog.SourcePath}
    (hfree : Line.gasFree l = true) (h : Func.Run fs e s (l +++ p) r) :
    ∃ s' mid, Line.Run e s l s' ∧ Func.Run fs e s' p r ∧
      Func.RunPrefix fs e path s (l +++ p) mid s' p := by
  cases path with
  | mk k steps =>
    rcases Func.RunPrefix.of_run_prepend (k := k) (steps := steps)
        hfree h with ⟨s', hline, hrun, hpre⟩
    exact ⟨s', _, hline, hrun, hpre⟩

theorem run_prefix_branch {fs : List Func} {e : Sevm} {s r : Devm}
    {f g : Func} {path : Prog.SourcePath}
    (h : Func.Run fs e s (.branch f g) r) :
    (∃ s' mid, Devm.PopBurn [0] s s' ∧ Func.Run fs e s' f r ∧
      Func.RunPrefix fs e path s (.branch f g) mid s' f)
    ∨ (∃ w s' s'' mid, w ≠ 0 ∧ Devm.PopBurn [w] s s' ∧ Devm.Burn s' s'' ∧
      Func.Run fs e s'' g r ∧
      Func.RunPrefix fs e path s (.branch f g) mid s'' g) := by
  cases path with
  | mk k steps =>
    rcases Func.RunPrefix.of_run_branch (k := k) (steps := steps) h with
      ⟨s', hpop, hrun, hpre⟩ | ⟨w, s', s'', hne, hpop, hburn, hrun, hpre⟩
    · exact Or.inl ⟨s', _, hpop, hrun, hpre⟩
    · exact Or.inr ⟨w, s', s'', _, hne, hpop, hburn, hrun, hpre⟩

/-- A nonempty `Func.mainWith` run reaches its dispatch tree with the selector
alone on the stack, preserving the entry frame and exposing the gas-free
prefix through the function's source path. -/
theorem dispatch_entry_of_run_mainWith_prefix {fs : List Func}
    {k : Nat} {dt : DispatchTree} {sevm : Sevm} {pre post : Devm}
    {path : Prog.SourcePath}
    (run : Func.Run fs sevm pre (Func.mainWith k dt) post) :
    ∃ entry target, pre.state = entry.state ∧ pre.memory = entry.memory ∧
      pre.logs = entry.logs ∧ pre.output = entry.output ∧
      (Sevm.selector sevm :: [] <<+ entry.stack) ∧
      Func.RunPrefix fs sevm path pre (Func.mainWith k dt) target entry
        (dispatchWith k dt) ∧
      Func.Run fs sevm entry (dispatchWith k dt) post := by
  unfold Func.mainWith at run
  rcases run_prefix_prepend (l := fsig) (path := path)
      (by decide : Line.gasFree fsig = true) run with
    ⟨entry, target, hfsig, hdispatch, hprefix⟩
  have hframe := hfsig
  have hsel : Sevm.selector sevm :: [] <<+ entry.stack :=
    prefix_of_fsig nil_pref hfsig
  exact ⟨entry, target,
    Line.of_inv Devm.state (by line_inv) hframe,
    Line.of_inv Devm.memory (by line_inv) hframe,
    (fsig_logs hframe), (fsig_output hframe), hsel, hprefix, hdispatch⟩

/-! The indexed-fallback dispatcher has the same source walk as `dispatch`,
but its miss arm is a call rather than an inline revert.  Keep its prefix
transport beside the `mainWith` entry lemma so consumers do not have to
reconstruct the balanced-tree walk. -/

theorem dispatchWith_run_prefix_of_sorted :
    ∀ {n : Nat} {xs : List (B256 × Func)} {sig : B256} {f : Func}
      {fs : List Func} {k : Nat} {e : Sevm} {s r : Devm} {ws : Stack}
      {path : Prog.SourcePath},
      DispatchTree.sorted xs = true →
      xs.length ≤ n + 1 →
      (sig, f) ∈ xs →
      sig :: ws <<+ s.stack →
      Func.Run fs e s (dispatchWith k (DispatchTree.build n xs)) r →
      ∃ s' target, ws <<+ s'.stack ∧ s.state = s'.state ∧
        s.memory = s'.memory ∧
        Func.RunPrefix fs e path s (dispatchWith k (DispatchTree.build n xs))
          target s' f ∧
        Func.Run fs e s' f r := by
  intro n
  induction n with
  | zero =>
      intro xs sig f fs k e s r ws path h_sorted h_len h_mem h_pfx h_run
      rcases xs with _ | ⟨⟨w, p⟩, _ | ⟨y, ys⟩⟩
      · cases h_mem
      · have h_eq : (sig, f) = (w, p) := List.mem_singleton.mp h_mem
        injection h_eq with hsig hf
        subst sig
        subst f
        rcases run_prefix_prepend (l := [pushB256 w, eq])
            (path := path)
            (by simp only [Line.gasFree, Ninst.pushB256, Ninst.gasFree,
              Rinst.gasFree, Bool.true_and]) h_run with
          ⟨s₁, mid₁, hline, hbranch, hpre₁⟩
        have h_pfx₁ : (w =? w) :: ws <<+ s₁.stack := by
          generalize_line_prefix
        rw [show (w =? w) = 1 from by simp [B256.eqCheck]] at h_pfx₁
        rcases run_prefix_branch (path := mid₁) hbranch with
          ⟨s₂, mid₂, hpop, hmiss, hpreB⟩ |
          ⟨v, s₂, s₃, mid₃, hne, hpop, hburn, hbody, hpreB⟩
        · exact absurd (popBurn_pref hpop h_pfx₁).1 B256.zero_ne_one
        · rcases popBurn_pref hpop h_pfx₁ with ⟨-, h_pfx₂⟩
          refine ⟨s₃, mid₃, ?_, ?_, ?_,
            (by simpa [DispatchTree.build, dispatchWith, prepend] using
              hpre₁.trans hpreB), hbody⟩
          · rw [← hburn.stack]; exact h_pfx₂
          · exact (Line.of_inv Devm.state (by line_inv) hline).trans
              (hpop.state.trans hburn.state)
          · exact (Line.of_inv Devm.memory (by line_inv) hline).trans
              (hpop.memory.trans hburn.memory)
      · exfalso
        simp only [List.length_cons] at h_len
        omega
  | succ n ih =>
      intro xs sig f fs k e s r ws path h_sorted h_len h_mem h_pfx h_run
      rcases xs with _ | ⟨⟨w, p⟩, _ | ⟨y, ys⟩⟩
      · cases h_mem
      · simpa [DispatchTree.build] using
          (ih (xs := [(w, p)])
            (sig := sig) (f := f) (fs := fs) (k := k) (e := e) (s := s)
            (r := r) (ws := ws) (path := path) (by simpa using h_sorted)
            (by simp) h_mem h_pfx (by simpa [DispatchTree.build] using h_run))
      · simp only [List.length_cons] at h_len
        have h_take_len :
            (((w, p) :: y :: ys).take ((((w, p) :: y :: ys).length + 1) / 2)).length
              ≤ n + 1 := by
          simp only [List.length_take, List.length_cons]; omega
        have h_drop_len :
            (((w, p) :: y :: ys).drop ((((w, p) :: y :: ys).length + 1) / 2)).length
              ≤ n + 1 := by
          simp only [List.length_drop, List.length_cons]; omega
        obtain ⟨z, zs, h_drop⟩ :
            ∃ z zs, ((w, p) :: y :: ys).drop ((((w, p) :: y :: ys).length + 1) / 2)
              = z :: zs := by
          rcases h_d : ((w, p) :: y :: ys).drop ((((w, p) :: y :: ys).length + 1) / 2)
              with _ | ⟨z, zs⟩
          · exfalso
            have h_l := congrArg List.length h_d
            simp only [List.length_drop, List.length_cons, List.length_nil] at h_l
            omega
          · exact ⟨z, zs, rfl⟩
        have h_sorted_split : DispatchTree.sorted
            (((w, p) :: y :: ys).take ((((w, p) :: y :: ys).length + 1) / 2) ++
             ((w, p) :: y :: ys).drop ((((w, p) :: y :: ys).length + 1) / 2)) = true := by
          rw [List.take_append_drop]; exact h_sorted
        have h_sorted_take := DispatchTree.sorted_append_left h_sorted_split
        have h_sorted_drop := DispatchTree.sorted_append_right h_sorted_split
        have h_mem_split : (sig, f) ∈
            ((w, p) :: y :: ys).take ((((w, p) :: y :: ys).length + 1) / 2) ∨
            (sig, f) ∈ ((w, p) :: y :: ys).drop ((((w, p) :: y :: ys).length + 1) / 2) := by
          apply List.mem_append.mp
          rw [List.take_append_drop]
          exact h_mem
        rcases run_prefix_prepend
            (l := [Ninst.dup 0, Ninst.pushB256 (leftmostFsig
              (DispatchTree.build n
                (((w, p) :: y :: ys).drop
                  ((((w, p) :: y :: ys).length + 1) / 2)))), Ninst.gt])
            (path := path)
            (by simp only [Line.gasFree, Ninst.dup, Ninst.pushB256,
              Ninst.gt, Ninst.gasFree, Rinst.gasFree, Bool.true_and]) h_run with
          ⟨s₁, mid₁, hline, hbranch, hpre₁⟩
        have h_pfx₁ :
            (leftmostFsig (DispatchTree.build n
              (((w, p) :: y :: ys).drop ((((w, p) :: y :: ys).length + 1) / 2))) >? sig)
              :: sig :: ws <<+ s₁.stack := by
          generalize_line_prefix
        rw [h_drop, DispatchTree.leftmostFsig_build] at h_pfx₁
        rcases run_prefix_branch (path := mid₁) hbranch with
          ⟨s₂, mid₂, hpop, hright, hpreB⟩ |
          ⟨v, s₂, s₃, mid₃, hne, hpop, hburn, hleft, hpreB⟩
        · rcases popBurn_pref hpop h_pfx₁ with ⟨hflag, h_pfx₂⟩
          have h_le : z.fst ≤ sig := by
            rw [← B256.not_lt]; intro h_lt
            have h_gt : z.fst > sig := h_lt
            rw [B256.gtCheck, if_pos h_gt] at hflag
            exact B256.zero_ne_one hflag
          have h_mem_drop : (sig, f) ∈
              ((w, p) :: y :: ys).drop ((((w, p) :: y :: ys).length + 1) / 2) := by
            rcases h_mem_split with h_in | h_in
            · exfalso
              have h_z : z ∈ ((w, p) :: y :: ys).drop
                  ((((w, p) :: y :: ys).length + 1) / 2) := by
                rw [h_drop]; exact List.mem_cons_self ..
              have h_lt := DispatchTree.fst_lt_of_sorted_append h_sorted_split h_in h_z
              have h1 : sig.toNat < z.fst.toNat := B256.toNat_lt_toNat h_lt
              have h2 : z.fst.toNat ≤ sig.toNat := B256.toNat_le_toNat h_le
              omega
            · exact h_in
          rcases ih h_sorted_drop h_drop_len h_mem_drop h_pfx₂ hright with
            ⟨s', target, hstack, hst, hmm, hpre, hbody⟩
          refine ⟨s', target, hstack, ?_, ?_,
            hpre₁.trans (hpreB.trans hpre), hbody⟩
          · exact (Line.of_inv Devm.state (by line_inv) hline).trans
              (hpop.state.trans hst)
          · exact (Line.of_inv Devm.memory (by line_inv) hline).trans
              (hpop.memory.trans hmm)
        · rcases popBurn_pref hpop h_pfx₁ with ⟨hflag, h_pfx₂⟩
          have h_lt : sig < z.fst := by
            by_contra h_nlt
            rw [B256.gtCheck, if_neg (fun h_gt => h_nlt h_gt)] at hflag
            exact hne hflag
          have h_mem_take : (sig, f) ∈
              ((w, p) :: y :: ys).take ((((w, p) :: y :: ys).length + 1) / 2) := by
            rcases h_mem_split with h_in | h_in
            · exact h_in
            · exfalso
              rw [h_drop] at h_in
              have h_sorted_zzs : DispatchTree.sorted (z :: zs) = true := by
                rw [← h_drop]; exact h_sorted_drop
              have h_le := DispatchTree.fst_le_of_sorted_mem h_sorted_zzs h_in
              have h1 : z.fst.toNat ≤ sig.toNat := B256.toNat_le_toNat h_le
              have h2 : sig.toNat < z.fst.toNat := B256.toNat_lt_toNat h_lt
              omega
          rw [hburn.stack] at h_pfx₂
          rcases ih h_sorted_take h_take_len h_mem_take h_pfx₂ hleft with
            ⟨s', target, hstack, hst, hmm, hpre, hbody⟩
          refine ⟨s', target, hstack, ?_, ?_,
            hpre₁.trans (hpreB.trans hpre), hbody⟩
          · exact (Line.of_inv Devm.state (by line_inv) hline).trans
              (hpop.state.trans (hburn.state.trans hst))
          · exact (Line.of_inv Devm.memory (by line_inv) hline).trans
              (hpop.memory.trans (hburn.memory.trans hmm))

theorem dispatchWith_run_prefix_of_sorted_list {funcs : List (B256 × Func)}
    {sig : B256} {f : Func} {fs : List Func} {k : Nat} {e : Sevm}
    {s r : Devm} {ws : Stack} {path : Prog.SourcePath}
    (h_sorted : DispatchTree.sorted funcs = true)
    (h_mem : (sig, f) ∈ funcs)
    (h_pfx : sig :: ws <<+ s.stack)
    (h_run : Func.Run fs e s (dispatchWith k (DispatchTree.ofSorted funcs)) r) :
    ∃ s' target, ws <<+ s'.stack ∧ s.state = s'.state ∧
      s.memory = s'.memory ∧
      Func.RunPrefix fs e path s (dispatchWith k (DispatchTree.ofSorted funcs))
        target s' f ∧ Func.Run fs e s' f r := by
  simpa only [DispatchTree.ofSorted] using
    (dispatchWith_run_prefix_of_sorted (n := funcs.length)
      (xs := funcs) h_sorted (by omega) h_mem h_pfx h_run)

def exactCalldata (size : B256) (body : Func) : Func :=
  pushB256 size ::: calldatasize ::: eq ::: (body <?> .revert)

/-- Prefix twin of `of_run_exactCalldata`: the same guard inversion exposing
the crossed length-check prefix. -/
theorem of_run_exactCalldata_prefix {fs : List Func} {sevm : Sevm} {s r : Devm}
    {size : B256} {body : Func} {path : Prog.SourcePath}
    (run : Func.Run fs sevm s (exactCalldata size body) r) :
    ∃ mid target, sevm.data.length.toB256 = size ∧
      s.state = mid.state ∧ s.memory = mid.memory ∧
      s.logs = mid.logs ∧ s.output = mid.output ∧
      Func.RunPrefix fs sevm path s (exactCalldata size body) target mid body ∧
      Func.Run fs sevm mid body r := by
  unfold exactCalldata at run
  rcases run_prefix_prepend (l := [pushB256 size, calldatasize, eq])
    (path := path)
    (by simp only [Line.gasFree, Ninst.pushB256, Ninst.gasFree, Rinst.gasFree,
      Bool.true_and] : Line.gasFree [pushB256 size, calldatasize, eq] = true)
    run with
    ⟨s1, mid1, hline, hbranch, hpre1⟩
  have hframe := hline
  rcases Line.of_run_cons hline with ⟨a, hpush, htail⟩
  rcases Line.of_run_cons htail with ⟨b, hsize, htail⟩
  rcases Line.of_run_cons htail with ⟨c, heq, hnil⟩
  cases hnil
  have hp0 : size :: [] <<+ a.stack :=
    prefix_of_push (of_run_pushB256 hpush) nil_pref
  have hp1 : sevm.data.length.toB256 :: size :: [] <<+ b.stack :=
    prefix_of_push (of_run_calldatasize hsize) hp0
  have hp2 : (sevm.data.length.toB256 =? size) :: [] <<+ s1.stack :=
    prefix_of_eq heq hp1
  rcases run_prefix_branch (path := mid1) hbranch with
    ⟨u, midU, hpop, hrev, hpreB⟩
    | ⟨w, u, v, midV, hnz, hpop, hburn, hbody, hpreB⟩
  · exact absurd hrev not_run_revert
  · have hw : w = (sevm.data.length.toB256 =? size) :=
      (popBurn_pref hpop hp2).1
    have hsize' : sevm.data.length.toB256 = size := by
      by_cases h : sevm.data.length.toB256 = size
      · exact h
      · exact absurd (by rw [hw, B256.eqCheck, if_neg h]) hnz
    exact ⟨v, midV, hsize',
      (Line.of_inv Devm.state (by line_inv) hframe).trans
        (hpop.state.trans hburn.state),
      (Line.of_inv Devm.memory (by line_inv) hframe).trans
        (hpop.memory.trans hburn.memory),
      (Line.of_inv Devm.logs (by line_inv) hframe).trans
        (hpop.logs.trans hburn.logs),
      (Line.of_inv Devm.output (by line_inv) hframe).trans
        (hpop.output.trans hburn.output),
      Func.RunPrefix.trans hpre1 hpreB, hbody⟩

theorem run_prefix_nonpayable_logs {fs : List Func}
    {sevm : Sevm} {s r : Devm} {body : Func} {path : Prog.SourcePath}
    (run : Func.Run fs sevm s (nonpayable body) r) :
    ∃ mid target, sevm.value = 0 ∧ s.state = mid.state ∧
      s.memory = mid.memory ∧ s.logs = mid.logs ∧ s.output = mid.output ∧
      Func.RunPrefix fs sevm path s (nonpayable body) target mid body ∧
      Func.Run fs sevm mid body r := by
  unfold nonpayable at run
  rcases run_prefix_prepend (l := [callvalue, iszero]) (path := path)
    (by decide : Line.gasFree [callvalue, iszero] = true) run with
    ⟨s1, mid1, hline, hbranch, hpre1⟩
  rcases Line.of_run_cons hline with ⟨s0, hcv, hline'⟩
  rcases Line.of_run_cons hline' with ⟨s1', hiz, hnil⟩
  cases hnil
  have hpv : [sevm.value] <<+ s0.stack :=
    prefix_of_push (of_run_callvalue hcv) nil_pref
  have hpflag : [sevm.value =? 0] <<+ s1.stack :=
    prefix_of_iszero hiz hpv
  rcases run_prefix_branch (path := mid1) hbranch with
    ⟨s2, mid2, hpop, hrev, hpreB⟩
    | ⟨w, s2, s3, mid3, hnz, hpop, hburn, hbody, hpreB⟩
  · exact absurd hrev not_run_revert
  · have hpop' := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpop'
    rw [hpop'] at hpflag
    have hw : (sevm.value =? 0) = w :=
      pref_head_unique hpflag (pref_append [w] s2.stack)
    have hflag : (sevm.value =? 0) ≠ 0 := by
      rw [hw]
      exact hnz
    have hv : sevm.value = 0 := by
      by_cases hv : sevm.value = 0
      · exact hv
      · simp [B256.eqCheck, hv] at hflag
    exact ⟨s3, mid3, hv,
      (Line.of_inv Devm.state (by line_inv) hline).trans
        (hpop.state.trans hburn.state),
      (Line.of_inv Devm.memory (by line_inv) hline).trans
        (hpop.memory.trans hburn.memory),
      (Line.of_inv Devm.logs (by line_inv) hline).trans
        (hpop.logs.trans hburn.logs),
      (Line.of_inv Devm.output (by line_inv) hline).trans
        (hpop.output.trans hburn.output),
      Func.RunPrefix.trans hpre1 hpreB, hbody⟩

private theorem run_body_of_run_nonpayable_logs_prefix {fs : List Func}
    {sevm : Sevm} {s r : Devm} {body : Func} {path : Prog.SourcePath}
    (run : Func.Run fs sevm s (nonpayable body) r) :
    ∃ mid target, sevm.value = 0 ∧ s.state = mid.state ∧
      s.memory = mid.memory ∧ s.logs = mid.logs ∧ s.output = mid.output ∧
      Func.RunPrefix fs sevm path s (nonpayable body) target mid body ∧
      Func.Run fs sevm mid body r :=
  run_prefix_nonpayable_logs run

/-- A successful run through the nonpayable exact-length guard exposes the
crossed prefix and forces both guard conditions. -/
theorem of_run_nonpayable_exactCalldata_prefix {fs : List Func} {sevm : Sevm}
    {s r : Devm} {size : B256} {body : Func} {path : Prog.SourcePath}
    (run : Func.Run fs sevm s (nonpayable (exactCalldata size body)) r) :
    ∃ mid target, sevm.value = 0 ∧ sevm.data.length.toB256 = size ∧
      s.state = mid.state ∧ s.memory = mid.memory ∧
      s.logs = mid.logs ∧ s.output = mid.output ∧
      Func.RunPrefix fs sevm path s (nonpayable (exactCalldata size body))
        target mid body ∧
      Func.Run fs sevm mid body r := by
  rcases run_body_of_run_nonpayable_logs_prefix (path := path) run with
    ⟨t, midT, hvalue, hst, hmm, hlg, hou, hpreN, hguarded⟩
  rcases of_run_exactCalldata_prefix (path := midT) hguarded with
    ⟨mid, midM, hsize, hst', hmm', hlg', hou', hpreE, hbody⟩
  exact ⟨mid, midM, hvalue, hsize, hst.trans hst', hmm.trans hmm',
    hlg.trans hlg', hou.trans hou', Func.RunPrefix.trans hpreN hpreE, hbody⟩

end Blanc
