import Blanc.Lift.GasErasureRun
import Blanc.Lift.Weth9.Effects
import Blanc.Lift.Weth9.LiveTransfer

/-!
# WETH9 side of the Uniswap V2 composition: two runs of the deployed WETH9 modulo gas

Two successful frames of the deployed WETH9 code with the same message, from states that differ at
most in `gasLeft`, enter the same selector wrapper in states that again differ at most in `gasLeft`
(`weth9_twin_wrapper`; the dispatcher is gas-free).  The `balanceOf` and `transfer` wrappers, with
every entry they reach, are gas-free (`balanceOf_gasFree`, `transfer_gasFree`), so the two frames end
in states equal modulo gas (`weth9_balanceOf_eqModGas`, `weth9_transfer_eqModGas`).  The frame module
uses this to read the output of an arbitrary successful frame off a constructed gas-exact one.
-/

namespace Blanc.Composition.UniswapV2PairWeth9

open Jaune Blanc Blanc.Lift Blanc.Lift.Weth9

/-- Two runs of a straight gas-free line prefix from states equal modulo gas reach states equal modulo
gas. -/
theorem twin_chain {P Q : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (hQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d') {fs : List SFunc} {sevm : Sevm}
    (hsg : sevm.benvStat.rules.stateGas = none) (xs : List Ninst) (hxs : Line.gasFree xs = true)
    {a b : Devm} {f : SFunc} {o o' : Outcome}
    (r1 : SFunc.RunP P fs sevm a (chain xs f) o) (r2 : SFunc.RunP Q fs sevm b (chain xs f) o')
    (h : Devm.EqModGas a b) :
    ∃ a₁ b₁, LineP P sevm a xs a₁ ∧ Devm.EqModGas a₁ b₁ ∧ SFunc.RunP P fs sevm a₁ f o ∧
      SFunc.RunP Q fs sevm b₁ f o' := by
  have r1' : SFunc.RunP P fs sevm a (chain (xs ++ []) f) o := by rw [List.append_nil]; exact r1
  have r2' : SFunc.RunP Q fs sevm b (chain (xs ++ []) f) o' := by rw [List.append_nil]; exact r2
  obtain ⟨a₁, hl1, r1⟩ := run_chain_prefixP xs [] r1'
  obtain ⟨b₁, hl2, r2⟩ := run_chain_prefixP xs [] r2'
  exact ⟨a₁, b₁, hl1, Line.run_eqModGas hxs (hl1.toRun hP) (hl2.toRun hQ) h hsg, r1, r2⟩

/-- **One comparison, twice.** -/
theorem twin_link {P Q : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (hQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d') {fs : List SFunc} {sevm : Sevm}
    (hsg : sevm.benvStat.rules.stateGas = none) (l : Link) {rest : SFunc} {a b : Devm}
    {o o' : Outcome} {sel : B256} {ys : Stack} (hp : sel :: ys <<+ a.stack)
    (r1 : SFunc.RunP P fs sevm a (chain l.line (.branchTo rest l.k)) o)
    (r2 : SFunc.RunP Q fs sevm b (chain l.line (.branchTo rest l.k)) o')
    (h : Devm.EqModGas a b) :
    (sel = Bytes.toB256 l.σ ∧ ∃ (g : SFunc) (a' b' : Devm), fs[l.k]? = some g ∧
        Devm.EqModGas a' b' ∧ SFunc.RunP P fs sevm a' g o ∧ SFunc.RunP Q fs sevm b' g o') ∨
    (sel ≠ Bytes.toB256 l.σ ∧ ∃ a' b' : Devm, Devm.EqModGas a' b' ∧ sel :: ys <<+ a'.stack ∧
        SFunc.RunP P fs sevm a' rest o ∧ SFunc.RunP Q fs sevm b' rest o') := by
  obtain ⟨a₁, b₁, hl, h1, r1, r2⟩ := twin_chain hP hQ hsg l.line rfl r1 r2 h
  obtain ⟨hp1, -⟩ := link_walk hp (hl.toRun hP)
  cases r1 with
  | toZero d pop r1 =>
    obtain ⟨-, hc, hp2⟩ := prefix_of_popBurn2 hp1 pop
    cases r2 with
    | toZero d' pop' r2 =>
      exact .inr ⟨fun hs => ne_of_eqc_eq hc hs.symm, _, _, (h1.of_popBurnList pop pop' rfl).2, hp2,
        r1, r2⟩
    | toSucc d' w hw lookup' pop' r2 =>
      exact absurd (List.cons.inj (List.cons.inj (h1.of_popBurnList pop pop' rfl).1).2).1.symm hw
  | toSucc d w hw lookup pop r1 =>
    obtain ⟨-, hc, -⟩ := prefix_of_popBurn2 hp1 pop
    subst hc
    cases r2 with
    | toZero d' pop' r2 =>
      exact absurd (List.cons.inj (List.cons.inj (h1.of_popBurnList pop pop' rfl).1).2).1 hw
    | toSucc d' w' hw' lookup' pop' r2 =>
      rw [lookup] at lookup'
      cases lookup'
      exact .inl ⟨(eq_of_eqc_ne hw).symm, _, _, _, lookup, (h1.of_popBurnList pop pop' rfl).2, r1,
        r2⟩

/-- **The comparisons, twice**: both runs enter the same wrapper, or both the fallback, in states equal
modulo gas. -/
theorem twin_dispatch {P Q : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (hQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d') {fs : List SFunc} {sevm : Sevm}
    (hsg : sevm.benvStat.rules.stateGas = none) :
    ∀ (ls : List Link) {f : SFunc} {a b : Devm} {o o' : Outcome} {sel : B256} {ys : Stack},
      sel :: ys <<+ a.stack → SFunc.RunP P fs sevm a (dispatchTree ls f) o →
      SFunc.RunP Q fs sevm b (dispatchTree ls f) o' → Devm.EqModGas a b →
      (∃ l ∈ ls, sel = Bytes.toB256 l.σ ∧ ∃ (g : SFunc) (a' b' : Devm), fs[l.k]? = some g ∧
          Devm.EqModGas a' b' ∧ SFunc.RunP P fs sevm a' g o ∧ SFunc.RunP Q fs sevm b' g o') ∨
      ((∀ l ∈ ls, sel ≠ Bytes.toB256 l.σ) ∧ ∃ a' b' : Devm, Devm.EqModGas a' b' ∧
          SFunc.RunP P fs sevm a' f o ∧ SFunc.RunP Q fs sevm b' f o') := by
  intro ls
  induction ls with
  | nil =>
    intro f a b o o' sel ys _ r1 r2 h
    exact .inr ⟨fun l hl => absurd hl List.not_mem_nil, a, b, h, r1, r2⟩
  | cons l ls ih =>
    intro f a b o o' sel ys hp r1 r2 h
    rcases twin_link hP hQ hsg l hp r1 r2 h with ⟨hsel, g, a', b', hg, h', r1', r2'⟩ |
        ⟨hne, a', b', h', hp', r1', r2'⟩
    · exact .inl ⟨l, List.mem_cons_self, hsel, g, a', b', hg, h', r1', r2'⟩
    · rcases ih hp' r1' r2' h' with ⟨l', hl', hsel, rest⟩ | ⟨hne', rest⟩
      · exact .inl ⟨l', List.mem_cons_of_mem _ hl', hsel, rest⟩
      · refine .inr ⟨fun l'' hl'' => ?_, rest⟩
        rcases List.mem_cons.mp hl'' with rfl | hl''
        · exact hne
        · exact hne' l'' hl''

/-- The eleven comparisons have distinct selectors. -/
theorem links_sel_inj :
    ∀ l ∈ links, ∀ l' ∈ links, Bytes.toB256 l.σ = Bytes.toB256 l'.σ → l.k = l'.k := by
  decide +kernel

/-- **Two frames of the deployed WETH9 with the same message, from states equal modulo gas, enter the
wrapper of the calldata selector's link in states equal modulo gas.** -/
theorem weth9_twin_wrapper {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {sevm : Sevm}
    (hsg : sevm.benvStat.rules.stateGas = none) {a b post post' : Devm}
    (r1 : SProg.RunP P prog sevm a post) (r2 : SProg.Run prog sevm b post')
    (h : Devm.EqModGas a b) (hshort : ¬ shortCall sevm) {l : Link} (hl : l ∈ links)
    (hsel : Sevm.selector sevm = Bytes.toB256 l.σ) :
    ∃ (g : SFunc) (a' b' : Devm), prog[l.k]? = some g ∧ Devm.EqModGas a' b' ∧
      SFunc.RunP P prog sevm a' g (.halted post) ∧ SFunc.Run prog sevm b' g (.halted post') := by
  obtain ⟨f, hf, r1⟩ := r1
  obtain ⟨f', hf', r2⟩ := r2
  rw [entry0_lookup] at hf hf'
  cases hf
  cases hf'
  rw [tree_0000] at r1 r2
  obtain ⟨a₁, b₁, hl1, h1, r1, r2⟩ := twin_chain hP (fun h => h) hsg preamble rfl r1 r2 h
  obtain ⟨hp1, -⟩ := preamble_walk nil_pref (hl1.toRun hP)
  cases r1 with
  | succ d w hw pop r1 =>
    obtain ⟨-, hc, -⟩ := prefix_of_popBurn2 hp1 pop
    subst hc
    exact absurd (ltc_ne_zero hw) hshort
  | zero d pop r1 =>
    obtain ⟨-, -, hp2⟩ := prefix_of_popBurn2 hp1 pop
    cases r2 with
    | succ d' w hw pop' r2 =>
      exact absurd (List.cons.inj (List.cons.inj (h1.of_popBurnList pop pop' rfl).1).2).1.symm hw
    | zero d' pop' r2 =>
      have h2 := (h1.of_popBurnList pop pop' rfl).2
      rw [tree_000d] at r1 r2
      obtain ⟨a₃, b₃, hl3, h3, r1, r2⟩ := twin_chain hP (fun h => h) hsg extractLine rfl r1 r2 h2
      obtain ⟨hp3, -⟩ := extract_walk hp2 (hl3.toRun hP)
      rcases twin_dispatch hP (fun h => h) hsg links hp3 r1 r2 h3 with
          ⟨l', hl', hsel', g, a', b', hg, h', r1', r2'⟩ | ⟨hne, -⟩
      · have hk : l.k = l'.k := links_sel_inj l hl l' hl' (hsel.symm.trans hsel')
        rw [hk]
        exact ⟨g, a', b', hg, h', r1', r2'⟩
      · exact absurd hsel (hne l hl)

/-- The certified cost of `transfer` reads the access set and storage only, not `gasLeft`. -/
theorem transferGas_congr (sevm : Sevm) {a b : Devm} (h : Devm.EqModGas a b) :
    transferGas sevm a = transferGas sevm b := by
  have e0 := h.afterSload sevm (balSlot sevm.caller)
  have e1 := e0.afterSload sevm (balSlot sevm.caller)
  have v1 := e0.getStorVal_congr (t := sevm.currentTarget) (k := balSlot sevm.caller)
  unfold transferGas xferGasSelf xfTailGas
  dsimp only [tT1, tT2, tT3, tV1, tV2, pB1]
  rw [v1]
  have e2 := e1.afterSstore sevm (balSlot sevm.caller)
    ((afterSload sevm b (balSlot sevm.caller)).getStorVal sevm.currentTarget (balSlot sevm.caller) -
      Sevm.dataWord sevm 36)
  have v2 := e2.getStorVal_congr (t := sevm.currentTarget)
    (k := balSlot (Sevm.dataWord sevm 4).toAdr)
  have e3 := e2.afterSload sevm (balSlot (Sevm.dataWord sevm 4).toAdr)
  rw [v2, h.sloadCost_congr, e0.sloadCost_congr, e1.sstoreCost_congr, e2.sloadCost_congr,
    e3.sstoreCost_congr]

/-! ## The `balanceOf` and `transfer` wrappers are gas-free -/

theorem balanceOf_gasFree :
    GasFreeSet prog [6] = true ∧ t_0295_c22.gasFree = true ∧ t_0295_c22.refs.all (· ∈ [6]) = true :=
  by decide +kernel

theorem transfer_gasFree :
    GasFreeSet prog [3, 9] = true ∧ t_0370_c20.gasFree = true ∧
      t_0370_c20.refs.all (· ∈ [3, 9]) = true := by
  decide +kernel

theorem balanceOf_link :
    (⟨[0x70, 0xa0, 0x82, 0x31], [0x02, 0x95], by decide, by decide, 22⟩ : Link) ∈ links := by
  simp only [links, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]

theorem transfer_link :
    (⟨[0xa9, 0x05, 0x9c, 0xbb], [0x03, 0x70], by decide, by decide, 20⟩ : Link) ∈ links := by
  simp only [links, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]

theorem prog_22 : prog[22]? = some t_0295_c22 := by
  simp only [prog, Cert.prog, cert, List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ,
    List.getElem_cons_zero]

theorem prog_20 : prog[20]? = some t_0370_c20 := by
  simp only [prog, Cert.prog, cert, List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ,
    List.getElem_cons_zero]

/-- **Two successful `balanceOf` frames of the deployed WETH9 from states equal modulo gas end in
states equal modulo gas.** -/
theorem weth9_balanceOf_eqModGas {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {sevm : Sevm}
    (hsg : sevm.benvStat.rules.stateGas = none) {a b post post' : Devm}
    (r1 : SProg.RunP P prog sevm a post) (r2 : SProg.Run prog sevm b post')
    (h : Devm.EqModGas a b) (hshort : ¬ shortCall sevm)
    (hsel : Sevm.selector sevm = 0x70a08231) : Devm.EqModGas post post' := by
  obtain ⟨g, a', b', hg, h', r1', r2'⟩ :=
    weth9_twin_wrapper hP hsg r1 r2 h hshort balanceOf_link (hsel.trans (by decide +kernel))
  rw [prog_22] at hg
  cases hg
  obtain ⟨hS, hf, hr⟩ := balanceOf_gasFree
  exact SFunc.RunP.eqModGas hP (fun h => h) hS hsg hf hr r1' r2' h'

/-- **Two successful `transfer` frames of the deployed WETH9 from states equal modulo gas end in
states equal modulo gas.** -/
theorem weth9_transfer_eqModGas {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {sevm : Sevm}
    (hsg : sevm.benvStat.rules.stateGas = none) {a b post post' : Devm}
    (r1 : SProg.RunP P prog sevm a post) (r2 : SProg.Run prog sevm b post')
    (h : Devm.EqModGas a b) (hshort : ¬ shortCall sevm)
    (hsel : Sevm.selector sevm = 0xa9059cbb) : Devm.EqModGas post post' := by
  obtain ⟨g, a', b', hg, h', r1', r2'⟩ :=
    weth9_twin_wrapper hP hsg r1 r2 h hshort transfer_link (hsel.trans (by decide +kernel))
  rw [prog_20] at hg
  cases hg
  obtain ⟨hS, hf, hr⟩ := transfer_gasFree
  exact SFunc.RunP.eqModGas hP (fun h => h) hS hsg hf hr r1' r2' h'

end Blanc.Composition.UniswapV2PairWeth9
