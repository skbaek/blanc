import Blanc.Lift.Weth9.Frame
import Blanc.Lift.Weth9.Live
import Blanc.Lift.ReachWalk
import Blanc.Lift.Weth9.RouteCheck

/-!
# The selector dispatch of the deployed WETH9

`hoare_single_call_with_gotos` (`Frame.lean`) abstracts the dispatcher: its predicates are stable under
state equality, so it cannot say *which* wrapper a run entered.  A committed replay needs exactly that, so
this module proves the dispatcher route once at the level of a single comparison and iterates it.

One solc-0.4 comparison is `DUP1; PUSH4 σ; EQ; PUSH2 dest; JUMPI` (a `Link`): it keeps the state and the
selector on the stack, and the goto is taken exactly when the selector is `σ` (`link_walk`).  The eleven
comparisons of the entry-0 tree are `dispatchTree links`, where the trees `t_000d_c0` … `t_00a4_c0` are equal
to it (`tree_000d`).

* RunP form (`weth9_route`): a whole run of the program from a state enters the payable fallback (calldata
  shorter than four bytes, or no selector matches) or the wrapper `k` of a selector `σ` with the calldata
  selector equal to `σ`.
* Reach form (`weth9_reach_route`): a reach to an external instruction can only pass the wrapper of
  `withdraw` (entry 24), whose selector is then the calldata selector; every other wrapper, and the
  fallback, is exec-free (`RouteCheck.lean`).
-/

namespace Blanc.Lift.Weth9

open Jaune Blanc Blanc.Lift

/-! ## One comparison -/

/-- One selector comparison of the dispatcher: the selector bytes, the destination bytes, the entry
jumped to. -/
structure Link where
  σ : Bytes
  dest : Bytes
  hσ : σ.length ≤ 32
  hd : dest.length ≤ 32
  k : Nat

/-- `DUP1; PUSH4 σ; EQ; PUSH2 dest`. -/
def Link.line (l : Link) : List Ninst :=
  [.reg (.dup 0), .push l.σ l.hσ, .reg .eq, .push l.dest l.hd]

theorem Link.line_nonexec (l : Link) : ∀ n ∈ l.line, ∀ x, n ≠ .exec x := by
  intro n hn x h
  simp only [Link.line, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> cases h

/-- **One comparison at line level**: the state is kept and the stack is
`dest :: (σ =? sel) :: sel :: ys`. -/
theorem link_walk {sevm : Sevm} {s s' : Devm} {l : Link} {sel : B256} {ys : Stack}
    (hp : sel :: ys <<+ s.stack) (run : Line.Run sevm s l.line s') :
    (Bytes.toB256 l.dest :: (Bytes.toB256 l.σ =? sel) :: sel :: ys <<+ s'.stack) ∧ Same s s' := by
  unfold Link.line at run
  refine ⟨?_, Line.of_inv Devm.getStor (by line_inv) run,
    Line.of_inv Devm.getBal (by line_inv) run⟩
  obtain ⟨s1, h1, run⟩ := Line.of_run_cons run
  obtain ⟨s2, h2, run⟩ := Line.of_run_cons run
  obtain ⟨s3, h3, run⟩ := Line.of_run_cons run
  obtain ⟨s4, h4, run⟩ := Line.of_run_cons run
  cases run
  have q1 : sel :: sel :: ys <<+ s1.stack := prefix_of_dup_val h1 (by show_nth) hp
  have q2 := prefix_of_push (of_run_push h2) q1
  have q3 := prefix_of_eq h3 q2
  exact prefix_of_push (of_run_push h4) q3

/-! ## The chain of comparisons -/

/-- A cascade of comparisons ending in `f` (the fallback). -/
def dispatchTree : List Link → SFunc → SFunc
  | [], f => f
  | l :: ls, f => chain l.line (.branchTo (dispatchTree ls f) l.k)

/-- The eleven comparisons of the deployed WETH9, in program order:
`name`, `approve`, `totalSupply`, `transferFrom`, `withdraw`, `decimals`, `balanceOf`, `symbol`,
`transfer`, `deposit`, `allowance`. -/
def links : List Link :=
  [⟨[0x06, 0xfd, 0xde, 0x03], [0x00, 0xb9], by decide, by decide, 28⟩,
   ⟨[0x09, 0x5e, 0xa7, 0xb3], [0x01, 0x47], by decide, by decide, 27⟩,
   ⟨[0x18, 0x16, 0x0d, 0xdd], [0x01, 0xa1], by decide, by decide, 26⟩,
   ⟨[0x23, 0xb8, 0x72, 0xdd], [0x01, 0xca], by decide, by decide, 25⟩,
   ⟨[0x2e, 0x1a, 0x7d, 0x4d], [0x02, 0x43], by decide, by decide, 24⟩,
   ⟨[0x31, 0x3c, 0xe5, 0x67], [0x02, 0x66], by decide, by decide, 23⟩,
   ⟨[0x70, 0xa0, 0x82, 0x31], [0x02, 0x95], by decide, by decide, 22⟩,
   ⟨[0x95, 0xd8, 0x9b, 0x41], [0x02, 0xe2], by decide, by decide, 21⟩,
   ⟨[0xa9, 0x05, 0x9c, 0xbb], [0x03, 0x70], by decide, by decide, 20⟩,
   ⟨[0xd0, 0xe3, 0x0d, 0xb0], [0x03, 0xca], by decide, by decide, 19⟩,
   ⟨[0xdd, 0x62, 0xed, 0x3e], [0x03, 0xd4], by decide, by decide, 18⟩]

/-- The constant `2^224` (`PUSH29 0x01 0…0`) of the selector extraction. -/
def pow224 : B256 :=
  Bytes.toB256 [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

/-- `PUSH1 0; CALLDATALOAD; PUSH29 2^224; SWAP1; DIV; PUSH4 0xffffffff; AND`: the selector word. -/
def extractLine : List Ninst :=
  [.push [0x00] (by decide), .reg .calldataload,
   .push [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide),
   .reg (.swap 0), .reg .div, .push [0xff, 0xff, 0xff, 0xff] (by decide), .reg .and]

/-- `PUSH1 0x60; PUSH1 0x40; MSTORE; PUSH1 4; CALLDATASIZE; LT; PUSH2 0x00af`. -/
def preamble : List Ninst :=
  [.push [0x60] (by decide), .push [0x40] (by decide), .reg .mstore, .push [0x04] (by decide),
   .reg .calldatasize, .reg .lt, .push [0x00, 0xaf] (by decide)]

theorem tree_0000 : t_0000_c0 = chain preamble (.branch t_000d_c0 t_00af_c0) := rfl

theorem tree_000d : t_000d_c0 = chain extractLine (dispatchTree links t_00af_c0) := rfl

/-- The payable fallback: `PUSH2 0x00b7; PUSH2 0x0440; JUMP` (a call of entry 1, then `STOP`). -/
theorem tree_00af : t_00af_c0 = .dest (chain [.push [0x00, 0xb7] (by decide),
    .push [0x04, 0x40] (by decide)] (.callNext 1 t_00b7_c0)) := rfl

/-! ## The RunP form -/

section RunPForm

variable {P : Sevm → Devm → Ninst → Devm → Prop}

theorem link_runP (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {fs : List SFunc}
    {sevm : Sevm} (l : Link) {rest : SFunc} {d : Devm} {o : Outcome} {sel : B256} {ys : Stack}
    (hp : sel :: ys <<+ d.stack)
    (run : SFunc.RunP P fs sevm d (chain l.line (.branchTo rest l.k)) o) :
    (sel = Bytes.toB256 l.σ ∧ ∃ (g : SFunc) (d' : Devm), fs[l.k]? = some g ∧ Same d d' ∧
        sel :: ys <<+ d'.stack ∧ SFunc.RunP P fs sevm d' g o) ∨
    (sel ≠ Bytes.toB256 l.σ ∧ ∃ d' : Devm, Same d d' ∧ sel :: ys <<+ d'.stack ∧
        SFunc.RunP P fs sevm d' rest o) := by
  obtain ⟨d1, hl, run⟩ := run_chain_prefixP l.line [] run
  obtain ⟨hp1, s01⟩ := link_walk hp (hl.toRun hP)
  change SFunc.RunP P fs sevm d1 (.branchTo rest l.k) o at run
  cases run with
  | toZero dd pop run =>
    obtain ⟨-, hc, hp2⟩ := prefix_of_popBurn2 hp1 pop
    exact .inr ⟨fun h => ne_of_eqc_eq hc h.symm, _, s01.trans (Same.of_state pop.state), hp2, run⟩
  | toSucc dd w hnz lookup pop run =>
    obtain ⟨-, hc, hp2⟩ := prefix_of_popBurn2 hp1 pop
    subst hc
    exact .inl ⟨(eq_of_eqc_ne hnz).symm, _, _, lookup, s01.trans (Same.of_state pop.state), hp2,
      run⟩

/-- **The comparisons in order**: the run enters the goto of the first link whose selector is the one
on the stack, or, if none matches, the fallback. -/
theorem dispatch_runP (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {fs : List SFunc}
    {sevm : Sevm} :
    ∀ (ls : List Link) {f : SFunc} {d : Devm} {o : Outcome} {sel : B256} {ys : Stack},
      sel :: ys <<+ d.stack → SFunc.RunP P fs sevm d (dispatchTree ls f) o →
      (∃ l ∈ ls, sel = Bytes.toB256 l.σ ∧ ∃ (g : SFunc) (d' : Devm), fs[l.k]? = some g ∧
          Same d d' ∧ sel :: ys <<+ d'.stack ∧ SFunc.RunP P fs sevm d' g o) ∨
      ((∀ l ∈ ls, sel ≠ Bytes.toB256 l.σ) ∧ ∃ d' : Devm, Same d d' ∧ sel :: ys <<+ d'.stack ∧
          SFunc.RunP P fs sevm d' f o) := by
  intro ls
  induction ls with
  | nil =>
    intro f d o sel ys hp run
    exact .inr ⟨fun l hl => absurd hl List.not_mem_nil, d, ⟨rfl, rfl⟩, hp, run⟩
  | cons l ls ih =>
    intro f d o sel ys hp run
    rcases link_runP hP l hp run with ⟨hsel, g, d', hg, hs, hp', run'⟩ | ⟨hne, d', hs, hp', run'⟩
    · exact .inl ⟨l, List.mem_cons_self, hsel, g, d', hg, hs, hp', run'⟩
    · rcases ih hp' run' with ⟨l', hl', hsel, g, d'', hg, hs', hp'', run''⟩ |
          ⟨hne', d'', hs', hp'', run''⟩
      · exact .inl ⟨l', List.mem_cons_of_mem _ hl', hsel, g, d'', hg, hs.trans hs', hp'', run''⟩
      · refine .inr ⟨fun l'' hl'' => ?_, d'', hs.trans hs', hp'', run''⟩
        rcases List.mem_cons.mp hl'' with rfl | hl''
        · exact hne
        · exact hne' l'' hl''

end RunPForm

/-! ## The frame entry: the size test and the selector -/

/-- The machine's own reading of the dispatcher's first test, `CALLDATASIZE < 4`. -/
def shortCall (e : Sevm) : Prop := e.data.length.toB256 < 4

theorem ltc_ne_zero {x y : B256} (h : (x <? y) ≠ 0) : x < y := by
  unfold B256.ltCheck at h
  split at h
  · assumption
  · exact absurd rfl h

theorem ltc_eq_zero {x y : B256} (h : (x <? y) = 0) : ¬ x < y := by
  intro hlt
  unfold B256.ltCheck at h
  simp only [hlt, ↓reduceIte] at h
  exact absurd h (by decide)

/-- The preamble leaves the destination of the fallback and the size test above the stack it found. -/
theorem preamble_walk {sevm : Sevm} {s s' : Devm} {xs : Stack} (hp : xs <<+ s.stack)
    (run : Line.Run sevm s preamble s') :
    Bytes.toB256 [0x00, 0xaf] :: (sevm.data.length.toB256 <? 4) :: xs <<+ s'.stack ∧ Same s s' := by
  unfold preamble at run
  refine ⟨?_, Line.of_inv Devm.getStor (by line_inv) run,
    Line.of_inv Devm.getBal (by line_inv) run⟩
  obtain ⟨s1, h1, run⟩ := Line.of_run_cons run
  obtain ⟨s2, h2, run⟩ := Line.of_run_cons run
  obtain ⟨s3, h3, run⟩ := Line.of_run_cons run
  obtain ⟨s4, h4, run⟩ := Line.of_run_cons run
  obtain ⟨s5, h5, run⟩ := Line.of_run_cons run
  obtain ⟨s6, h6, run⟩ := Line.of_run_cons run
  obtain ⟨s7, h7, run⟩ := Line.of_run_cons run
  cases run
  have q1 := prefix_of_push (of_run_push h1) hp
  have q2 := prefix_of_push (of_run_push h2) q1
  have q3 := prefix_of_mstore h3 q2
  have q4 : (4 : B256) :: xs <<+ s4.stack := by
    have := prefix_of_push (of_run_push h4) q3
    rwa [w04_eq] at this
  have q5 := prefix_of_push (of_run_calldatasize h5) q4
  have q6 := prefix_of_lt h6 q5
  exact prefix_of_push (of_run_push h7) q6

/-- The selector extraction leaves the calldata selector on top of the stack. -/
theorem extract_walk {sevm : Sevm} {s s' : Devm} {xs : Stack} (hp : xs <<+ s.stack)
    (run : Line.Run sevm s extractLine s') :
    Sevm.selector sevm :: xs <<+ s'.stack ∧ Same s s' := by
  unfold extractLine at run
  refine ⟨?_, Line.of_inv Devm.getStor (by line_inv) run,
    Line.of_inv Devm.getBal (by line_inv) run⟩
  obtain ⟨s1, h1, run⟩ := Line.of_run_cons run
  obtain ⟨s2, h2, run⟩ := Line.of_run_cons run
  obtain ⟨s3, h3, run⟩ := Line.of_run_cons run
  obtain ⟨s4, h4, run⟩ := Line.of_run_cons run
  obtain ⟨s5, h5, run⟩ := Line.of_run_cons run
  obtain ⟨s6, h6, run⟩ := Line.of_run_cons run
  obtain ⟨s7, h7, run⟩ := Line.of_run_cons run
  cases run
  have q1 : (0 : B256) :: xs <<+ s1.stack := by
    have := prefix_of_push (of_run_push h1) hp
    rwa [w00_eq] at this
  have q2 := prefix_of_calldataload_val h2 q1
  have q3 : pow224 :: Sevm.dataWord sevm 0 :: xs <<+ s3.stack :=
    prefix_of_push (of_run_push h3) q2
  have q4 : Sevm.dataWord sevm 0 :: pow224 :: xs <<+ s4.stack :=
    Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h4) q3
  have q5 := prefix_of_div h5 q4
  have q6 := prefix_of_push (of_run_push h6) q5
  simp only [List.singleton_append] at q6
  have q7 := prefix_of_and h7 q6
  have hsel : Bytes.toB256 [0xff, 0xff, 0xff, 0xff] &&& (Sevm.dataWord sevm 0 / pow224) =
      Sevm.selector sevm := sel_extract _
  rw [hsel] at q7
  exact q7

section RunPRoute

variable {P : Sevm → Devm → Ninst → Devm → Prop}

/-- **The route of a successful run of the deployed WETH9.**  From any state, a run enters the payable
fallback (calldata shorter than four bytes, or no selector matches), or the wrapper of a link whose
selector is the calldata selector.  Storage and balances are unchanged on the way in. -/
theorem weth9_route (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {sevm : Sevm}
    {pre post : Devm} (hrun : SProg.RunP P prog sevm pre post) :
    ((shortCall sevm ∨ ∀ l ∈ links, Sevm.selector sevm ≠ Bytes.toB256 l.σ) ∧
        ∃ d' : Devm, Same pre d' ∧ SFunc.RunP P prog sevm d' t_00af_c0 (.halted post)) ∨
    ∃ l ∈ links, ¬ shortCall sevm ∧ Sevm.selector sevm = Bytes.toB256 l.σ ∧
      ∃ (g : SFunc) (d' : Devm), prog[l.k]? = some g ∧ Same pre d' ∧
        SFunc.RunP P prog sevm d' g (.halted post) := by
  obtain ⟨f, hf, run⟩ := hrun
  rw [entry0_lookup] at hf
  cases hf
  rw [tree_0000] at run
  obtain ⟨d1, hl, run⟩ := run_chain_prefixP preamble [] run
  obtain ⟨hp1, s01⟩ := preamble_walk nil_pref (hl.toRun hP)
  change SFunc.RunP P prog sevm d1 (.branch t_000d_c0 t_00af_c0) (.halted post) at run
  cases run with
  | zero dd pop run =>
    obtain ⟨-, hc, hp2⟩ := prefix_of_popBurn2 hp1 pop
    have hshort : ¬ shortCall sevm := ltc_eq_zero hc
    rw [tree_000d] at run
    obtain ⟨d2, hl2, run⟩ := run_chain_prefixP extractLine [] run
    obtain ⟨hp3, s23⟩ := extract_walk hp2 (hl2.toRun hP)
    have s03 := s01.trans ((Same.of_state pop.state).trans s23)
    rcases dispatch_runP hP links hp3 run with ⟨l, hl, hsel, g, d', hg, hs, -, run'⟩ |
        ⟨hne, d', hs, -, run'⟩
    · exact .inr ⟨l, hl, hshort, hsel, g, d', hg, s03.trans hs, run'⟩
    · exact .inl ⟨.inr hne, d', s03.trans hs, run'⟩
  | succ dd w hnz pop run =>
    obtain ⟨-, hc, hp2⟩ := prefix_of_popBurn2 hp1 pop
    subst hc
    exact .inl ⟨.inl (ltc_ne_zero hnz), _, s01.trans (Same.of_state pop.state), run⟩

end RunPRoute

/-! ## The Reach form -/

section ReachForm

variable {P : Sevm → Devm → Ninst → Devm → Prop}

/-- A reach through a straight line of non-external instructions to an external-instruction target is a
`LineP` run followed by a reach from what remains. -/
theorem Reach.chain_prefix {fs : List SFunc} {sevm : Sevm} :
    ∀ (xs : List Ninst) {d : Devm} {g : SFunc} {K : List SFunc} {T : Conf},
      (∀ n ∈ xs, ∀ x, n ≠ .exec x) → Reach P fs sevm ⟨d, chain xs g, K⟩ T → AtExec T →
      ∃ d' : Devm, LineP P sevm d xs d' ∧ Reach P fs sevm ⟨d', g, K⟩ T
  | [], d, g, K, T, _, h, _ => ⟨d, .nil, h⟩
  | n :: ns, d, g, K, T, hn, h, hT => by
    obtain ⟨d1, hstep, h1⟩ := Reach.next (hn n List.mem_cons_self) h hT
    obtain ⟨d', hl, h'⟩ := Reach.chain_prefix ns (fun m hm => hn m (List.mem_cons_of_mem _ hm))
      h1 hT
    exact ⟨d', .cons hstep hl, h'⟩

theorem link_reach (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {fs : List SFunc}
    {sevm : Sevm} (l : Link) {rest : SFunc} {d : Devm} {K : List SFunc} {T : Conf} {sel : B256}
    {ys : Stack} (hp : sel :: ys <<+ d.stack)
    (run : Reach P fs sevm ⟨d, chain l.line (.branchTo rest l.k), K⟩ T) (hT : AtExec T) :
    (sel = Bytes.toB256 l.σ ∧ ∃ (g : SFunc) (d' : Devm), fs[l.k]? = some g ∧ Same d d' ∧
        sel :: ys <<+ d'.stack ∧ Reach P fs sevm ⟨d', g, K⟩ T) ∨
    (sel ≠ Bytes.toB256 l.σ ∧ ∃ d' : Devm, Same d d' ∧ sel :: ys <<+ d'.stack ∧
        Reach P fs sevm ⟨d', rest, K⟩ T) := by
  obtain ⟨d1, hl, run⟩ := Reach.chain_prefix l.line l.line_nonexec run hT
  obtain ⟨hp1, s01⟩ := link_walk hp (hl.toRun hP)
  change Reach P fs sevm ⟨d1, .branchTo rest l.k, K⟩ T at run
  rcases Reach.branchTo run hT with ⟨t, d2, pop, run'⟩ | ⟨t, w, g, d2, hw, hk, pop, run'⟩
  · obtain ⟨-, hc, hp2⟩ := prefix_of_popBurn2 hp1 pop
    exact .inr ⟨fun h => ne_of_eqc_eq hc h.symm, _, s01.trans (Same.of_state pop.state), hp2, run'⟩
  · obtain ⟨-, hc, hp2⟩ := prefix_of_popBurn2 hp1 pop
    subst hc
    exact .inl ⟨(eq_of_eqc_ne hw).symm, _, _, hk, s01.trans (Same.of_state pop.state), hp2, run'⟩

theorem dispatch_reach (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {fs : List SFunc}
    {sevm : Sevm} :
    ∀ (ls : List Link) {f : SFunc} {d : Devm} {K : List SFunc} {T : Conf} {sel : B256} {ys : Stack},
      sel :: ys <<+ d.stack → Reach P fs sevm ⟨d, dispatchTree ls f, K⟩ T → AtExec T →
      (∃ l ∈ ls, sel = Bytes.toB256 l.σ ∧ ∃ (g : SFunc) (d' : Devm), fs[l.k]? = some g ∧
          Same d d' ∧ sel :: ys <<+ d'.stack ∧ Reach P fs sevm ⟨d', g, K⟩ T) ∨
      ((∀ l ∈ ls, sel ≠ Bytes.toB256 l.σ) ∧ ∃ d' : Devm, Same d d' ∧ sel :: ys <<+ d'.stack ∧
          Reach P fs sevm ⟨d', f, K⟩ T) := by
  intro ls
  induction ls with
  | nil =>
    intro f d K T sel ys hp run hT
    exact .inr ⟨fun l hl => absurd hl List.not_mem_nil, d, ⟨rfl, rfl⟩, hp, run⟩
  | cons l ls ih =>
    intro f d K T sel ys hp run hT
    rcases link_reach hP l hp run hT with ⟨hsel, g, d', hg, hs, hp', run'⟩ |
        ⟨hne, d', hs, hp', run'⟩
    · exact .inl ⟨l, List.mem_cons_self, hsel, g, d', hg, hs, hp', run'⟩
    · rcases ih hp' run' hT with ⟨l', hl', hsel, g, d'', hg, hs', hp'', run''⟩ |
          ⟨hne', d'', hs', hp'', run''⟩
      · exact .inl ⟨l', List.mem_cons_of_mem _ hl', hsel, g, d'', hg, hs.trans hs', hp'', run''⟩
      · refine .inr ⟨fun l'' hl'' => ?_, d'', hs.trans hs', hp'', run''⟩
        rcases List.mem_cons.mp hl'' with rfl | hl''
        · exact hne
        · exact hne' l'' hl''

theorem preamble_nonexec : ∀ n ∈ preamble, ∀ x, n ≠ .exec x := by
  intro n hn x h
  simp only [preamble, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases h

theorem extractLine_nonexec : ∀ n ∈ extractLine, ∀ x, n ≠ .exec x := by
  intro n hn x h
  simp only [extractLine, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases h

theorem wrapper24_lookup : prog[24]? = some t_0243_c24 := by
  simp [prog, Cert.prog, cert]

/-- **Where an external instruction can be reached.**  A reach from the frame's start to an external
instruction passes only the `withdraw` wrapper (entry 24), and then the calldata selector is
`withdraw`'s and at least four bytes are there.  The rest of the dispatcher — the other wrappers, the
fallback — is exec-free (`RouteCheck.lean`). -/
theorem weth9_reach_route (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {sevm : Sevm}
    {pre : Devm} {T : Conf} (run : Reach P prog sevm ⟨pre, t_0000_c0, []⟩ T) (hT : AtExec T) :
    ¬ shortCall sevm ∧ Sevm.selector sevm = Bytes.toB256 [0x2e, 0x1a, 0x7d, 0x4d] ∧
      ∃ d' : Devm, Same pre d' ∧ Reach P prog sevm ⟨d', t_0243_c24, []⟩ T := by
  rw [tree_0000] at run
  obtain ⟨d1, hl, run⟩ := Reach.chain_prefix preamble preamble_nonexec run hT
  obtain ⟨hp1, s01⟩ := preamble_walk nil_pref (hl.toRun hP)
  change Reach P prog sevm ⟨d1, .branch t_000d_c0 t_00af_c0, []⟩ T at run
  rcases Reach.branch run hT with ⟨t, d2, pop, run⟩ | ⟨t, w, d2, hw, pop, run⟩
  · obtain ⟨-, hc, hp2⟩ := prefix_of_popBurn2 hp1 pop
    have hshort : ¬ shortCall sevm := ltc_eq_zero hc
    rw [tree_000d] at run
    obtain ⟨d3, hl2, run⟩ := Reach.chain_prefix extractLine extractLine_nonexec run hT
    obtain ⟨hp3, s23⟩ := extract_walk hp2 (hl2.toRun hP)
    have s03 := s01.trans ((Same.of_state pop.state).trans s23)
    rcases dispatch_reach hP links hp3 run hT with ⟨l, hl, hsel, g, d', hg, hs, -, run'⟩ |
        ⟨-, d', hs, -, run'⟩
    · simp only [links, List.mem_cons, List.not_mem_nil, or_false] at hl
      have hfree : l.k ≠ 24 → False := by
        intro hk
        have hkE : l.k ∈ execFreeEntries := by
          rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first | exact absurd rfl hk | decide
        exact Reach.false_of_execFree execFreeEntries_set run'
          hT (ExecFreeSet.lookup execFreeEntries_set hkE hg) (by simp)
      by_cases h24 : l.k = 24
      · rw [h24, wrapper24_lookup] at hg
        cases hg
        refine ⟨hshort, ?_, d', s03.trans hs, run'⟩
        rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | exact hsel | exact absurd h24 (by decide)
      · exact (hfree h24).elim
    · exact (Reach.false_of_execFree execFreeEntries_set run' hT fallback_execFree
        (by simp)).elim
  · exact (Reach.false_of_execFree execFreeEntries_set run hT fallback_execFree (by simp)).elim

end ReachForm

end Blanc.Lift.Weth9
