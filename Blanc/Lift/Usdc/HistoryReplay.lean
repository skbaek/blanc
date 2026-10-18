import Blanc.Lift.Usdc.HistoryReplayFrames
import Blanc.Lift.Token.CoreW

/-!
# USDC's `CoreW` facts: the history replay (U6h2)

The facts behind `usdcCore`'s replay, good and shadow fields (design U6c §2 item 7):

* `usdc_opaque_shadowed`: no non-static whole frame at the proxy covers an unshadowed position (a
  library frame's block is shadowed by it; an implementation frame other than `rescueERC20` decodes
  only `DELEGATECALL`s to the library, whose blocks are shadowed);
* `usdc_history_chain`: the settled frames form an observer chain (`ObserverChain.of_local` with
  `usdc_entry_observer` and `usdc_observer_parent`);
* `usdc_history_replayAt`, `usdc_history_replayEnd`: the family ladder's positional law
  (`usdc_configuredHistory_atPos`) and its history law (`usdcLadder`), read through `guardedBook_run`
  (the guard at the checkpoint, `usdc_allowed` from F2) and `ObserverChain.run_eq`;
* `usdc_history_goodStart`, `usdc_history_goodAt`: the footprint invariant at the checkpoint and
  the slot invariant at every settled frame (`usdc_history_frames_of`);
* `usdc_shadow_kind`: a shadowed position holds a non-entry frame at the proxy or a frame below a
  library frame, hence static;
* `usdc_child_unshadowed`: a direct child of a frame elsewhere at an unshadowed position is at an
  unshadowed position (an entry if at the proxy, `usdc_foreign_child_entry`; a library block covering
  it would cover its parent, `enclosure_of_wholeBlocks`).

`UsdcShadowed` is positional (decision `usdc-corew-positional-shadow`), and so is the family
ladder's exclusion (`Exec.NoOpaqueAbove`, decision `usdc-ladder-positional-enclosure`).
* `usdc_decodes`: a non-entry frame at the proxy has its parents at the proxy.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay Blanc.Lift.Token

/-- The shadowed positions of the USDC core (positional: `before` is the list of settled frames
ahead of the position, `f` its frame): a non-entry frame at the proxy (an implementation or library
frame), or a position inside the block of an earlier library frame at the proxy (the
`isValidSignature`/`ecrecover` static calls before a signed writer's effect).  Settled frame values
need not be unique, so enclosure is judged by position, not by value. -/
def UsdcShadowed (P : Adr) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (_tr : ConfiguredHistoryTrace cfg checkpoint future) (before : List Exec.Frame)
    (f : Exec.Frame) : Prop :=
  (f.sevm.currentTarget = P ∧ ¬ IsEntry P f) ∨
    ∃ (b : List Exec.Frame) (A : Exec.Frame) (m n : List Exec.Frame), before = b ++ A :: m ∧
      A.sevm.currentTarget = P ∧ A.sevm.codeAddress = some usdcLib ∧
      Exec.descendantFrames A.run = m ++ f :: n

/-! ## Related messages step the book alike -/

theorem dataWord_congr {a b : Sevm} (h : a.data = b.data) : Sevm.dataWord a = Sevm.dataWord b :=
  funext fun i => by simp only [Sevm.dataWord, h]

theorem decodeCall_congr {a b : Sevm} (hv : a.value = b.value) (hd : a.data = b.data) :
    decodeCall a = decodeCall b := by
  have hw := dataWord_congr hd
  have hsel : Sevm.selector a = Sevm.selector b := by simp only [Sevm.selector, hw]
  have hr : ∀ r ∈ rows, r.read a = r.read b := by
    intro r hr
    simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
    repeat' (rcases hr with rfl | hr)
    all_goals simp only [hw]
  unfold decodeCall
  rw [hv, hd, hsel]
  split
  · rfl
  · cases found : rows.find? (fun r => decide (r.sel = Sevm.selector b)) with
    | none => rfl
    | some r =>
        simp only [hr r (List.mem_of_find?_eq_some found)]

/-- The book steps related messages alike. -/
theorem usdcRelated_step {P : Adr} {a b : Sevm} (h : usdcRelated a b) (l : Ledger) :
    (usdcBookS P).toBook.step l a = (usdcBookS P).toBook.step l b := by
  obtain ⟨hc, hv, hd⟩ := h
  have hsel : Sevm.selector a = Sevm.selector b := by simp only [Sevm.selector, dataWord_congr hd]
  change (usdcBookS P).step l a = (usdcBookS P).step l b
  have hg : adminGetter a = adminGetter b := by unfold adminGetter; rw [hsel]
  simp only [usdcBookS, hc, decodeCall_congr hv hd]
  by_cases g : adminGetter b
  · rw [ite_eq_left (hg ▸ g : adminGetter a), ite_eq_left g]
  · rw [ite_eq_right (fun h => g (hg ▸ h)), ite_eq_right g]

/-! ## The observer chain and the allowed messages -/

section History

variable {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}

/-- The settled frames form an observer chain (U6h, from `usdc_history_settled_owner`,
`proxy_forwards`, `proxy_admin_selectors`, `usdc_history_slots`). -/
theorem usdc_history_chain {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) :
    ObserverChain P (usdcObs P) usdcRelated tr.settledFrames :=
  ObserverChain.of_local _ (usdc_entry_observer tr hist)
    fun b f a split target nonstatic obs notEntry =>
      let ⟨b', e, hb, entry, static, notObs, _⟩ :=
        usdc_observer_parent tr hist b f a split target nonstatic obs notEntry
      ⟨b', e, hb, entry, static, notObs⟩

open Classical in
/-- Every observed message among frames of the history is allowed. -/
theorem usdc_observerAsks_allowed (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) {fs : List Exec.Frame} (sub : ∀ G ∈ fs, G ∈ tr.settledFrames) :
    ∀ e ∈ observerAsks P (usdcObs P) fs, usdcAllowed (adminOf checkpoint.state P) e := by
  intro e he
  unfold observerAsks at he
  obtain ⟨G, hG, rfl⟩ := List.mem_map.mp he
  obtain ⟨hG, h⟩ := List.mem_filter.mp hG
  obtain ⟨target, nonstatic, obs⟩ := of_decide_eq_true h
  exact usdc_allowed tr hist G (sub G hG) target nonstatic obs

/-- The family ladder's replay to a state, read as the book's run over the entry asks. -/
theorem usdc_replay_entryAsks (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) {fs : List Exec.Frame} (sub : ∀ G ∈ fs, G ∈ tr.settledFrames)
    (chain : ObserverChain P (usdcObs P) usdcRelated fs) {w : State} {steps : List Sevm}
    (replay : (usdcCarrier P (historyKeyUniverse P tr K₀) (adminOf checkpoint.state P)).Replay
      ((usdcCarrier P (historyKeyUniverse P tr K₀) (adminOf checkpoint.state P)).ofState
        checkpoint.state) steps
      ((usdcCarrier P (historyKeyUniverse P tr K₀) (adminOf checkpoint.state P)).ofState w))
    (observed : (usdcView P (historyKeyUniverse P tr K₀) (adminOf checkpoint.state P)).obs steps =
      fs.flatMap (usdcView P (historyKeyUniverse P tr K₀) (adminOf checkpoint.state P)).frameObs) :
    (usdcBookS P).toBook.run (ledger (historyKeyUniverse P tr K₀) (checkpoint.state.getStor P))
        (entryAsks P fs) =
      some (ledger (historyKeyUniverse P tr K₀) (w.getStor P)) := by
  have ext := hist.2.2.1.extend hist.2.2.2
  have hsteps : steps = observerAsks P (usdcObs P) fs :=
    observed.trans (observerView_flatMap P (usdcObs P) fs)
  subst hsteps
  obtain ⟨run, -⟩ := guardedBook_run replay ⟨hist.1.slot, rfl, ext.good⟩
    (usdc_observerAsks_allowed tr hist sub)
  exact (chain.run_eq (B := (usdcBookS P).toBook) usdcRelated_step _).trans run

end History

/-! ## The shadow -/

/-- **`shadow_kind`** (U6h). -/
theorem usdc_shadow_kind {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) :
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      tr.settledFrames = before ++ f :: after → UsdcShadowed P tr before f →
        f.sevm.isStatic = true ∨ (f.sevm.currentTarget = P ∧ ¬ IsEntry P f) := by
  intro before f after split shadowed
  rcases shadowed with h | ⟨b, A, m, n, rfl, target, ca, desc⟩
  · exact .inr h
  · left
    have hA : A ∈ tr.settledFrames := by
      rw [split]
      exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
    have encl : A.Encloses f := by
      show f ∈ Exec.descendantFrames A.run
      rw [desc]
      exact List.mem_append_right _ List.mem_cons_self
    have facts := usdc_settled_facts tr hist A hA
    have code : A.sevm.code = Lib.code := by
      rcases facts.kind target with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
      · exact (hist.1.libApart (Option.some.inj (h.symm.trans ca))).elim
      · exact (usdcImpl_ne_lib (Option.some.inj (h.symm.trans ca))).elim
      · exact h
    revert encl
    refine frame_cases_ok (Q := fun A => A.sevm.code = Lib.code →
      CoveredFork A.sevm.benvStat.fork → A.Encloses f → f.sevm.isStatic = true) A facts.pc ?_ code
      facts.fork
    intro sevm pre post run committed code fork encl
    exact (lib_quiet run code fork).2 f encl

/-- A direct child at the proxy of a settled frame elsewhere is an entry: a spawn changing the
target runs the target's own (undelegated, nonempty) code. -/
theorem usdc_foreign_child_entry {P : Adr} {U : Key → Prop} {A₀ : Adr} {G : Exec.Frame}
    (facts : SettledFacts P U A₀ G) {c : Exec.Frame} (member : c ∈ Exec.childFrames G.run)
    (target : c.sevm.currentTarget = P) (apart : G.sevm.currentTarget ≠ P) : IsEntry P c := by
  refine ⟨target, ?_⟩
  revert member apart
  refine frame_cases_ok (Q := fun G => SettledFacts P U A₀ G → c ∈ Exec.childFrames G.run →
    G.sevm.currentTarget ≠ P → c.sevm.codeAddress = some P) G facts.pc ?_ facts
  intro sevm pre post run committed facts member apart
  obtain ⟨N, f, rsm, pc', cevm, chain, step, enter, childEq⟩ :=
    Exec.childFrames_spawnedAt run (.refl _) c member
  obtain ⟨x, hat, spawn, -⟩ := Evm.step_spawn_inv step
  obtain ⟨sevmEq, -, -, -, -, ncodes, -, -⟩ := node_child chain facts.fork facts.codes step enter
  have innerTarget : f.inner.currentTarget = P := by
    rw [← Frame.enter_run_currentTarget enter, ← childEq, target]
  have codeNe : N.devm.getCode P ≠ .empty := fun empty => proxy_nonempty (by
    rw [← ncodes.1, empty]; simp only [ByteArray.toList_empty])
  have hne : N.sevm.currentTarget ≠ f.inner.currentTarget := by
    rw [sevmEq, innerTarget]; exact apart
  have ca := Xinst.step_spawn_codeAddress_eq_currentTarget spawn hne (by rw [innerTarget]; exact codeNe)
    (by rw [innerTarget, ncodes.1]; exact proxy_undelegated)
  rw [childEq, Frame.enter_run_codeAddress enter, ca, innerTarget]

/-- A position inside an earlier frame's block, after a frame `Q` and a run of whole blocks, is
inside `Q`'s position or is `Q`'s block's head. -/
theorem enclosure_of_wholeBlocks {before m b m' n : List Exec.Frame} {Q A c : Exec.Frame}
    (split : before ++ Q :: m = b ++ A :: m') (desc : Exec.descendantFrames A.run = m' ++ c :: n)
    (whole : WholeBlocks m) :
    A = Q ∨ ∃ x, before = b ++ A :: x ∧ Exec.descendantFrames A.run = x ++ Q :: (m ++ c :: n) := by
  rcases List.split_append_cons split with ⟨x, hb, rfl⟩ | ⟨k, -, hk⟩
  · exact .inr ⟨x, hb, by rw [desc]; simp only [List.append_assoc, List.cons_append]⟩
  · cases k with
    | nil =>
      obtain ⟨rfl, -⟩ := List.cons.inj hk
      exact .inl rfl
    | cons y k =>
      obtain ⟨-, hm⟩ := List.cons.inj hk
      have short := whole k A m' hm
      rw [desc, List.length_append, List.length_cons] at short
      omega

/-- **`child_unshadowed`** (U6h, positional). -/
theorem usdc_child_unshadowed {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) :
    ∀ (before : List Exec.Frame) (Q : Exec.Frame) (m : List Exec.Frame) (c : Exec.Frame)
      (after : List Exec.Frame),
      tr.settledFrames = before ++ Q :: (m ++ c :: after) → Q.sevm.currentTarget ≠ P →
        ¬ UsdcShadowed P tr before Q → WholeBlocks m → c ∈ Exec.childFrames Q.run →
          ¬ UsdcShadowed P tr (before ++ Q :: m) c := by
  intro before Q m c after split apart lit whole child shadowed
  rcases shadowed with ⟨target, notEntry⟩ | ⟨b, A, m', n, hsplit, target, ca, desc⟩
  · have hQ : Q ∈ tr.settledFrames := by rw [split]; exact List.mem_append_right _ List.mem_cons_self
    exact notEntry (usdc_foreign_child_entry (usdc_settled_facts tr hist Q hQ) child target apart)
  · rcases enclosure_of_wholeBlocks hsplit desc whole with rfl | ⟨x, hb, descQ⟩
    · exact apart target
    · exact lit (.inr ⟨b, A, x, m ++ c :: n, hb, target, ca, descQ⟩)

/-- **The children of a whole implementation frame are library frames at the proxy**: it decodes
only `DELEGATECALL`s to the library. -/
theorem usdc_impl_children_lib {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) {A : Exec.Frame}
    (facts : SettledFacts P (historyKeyUniverse P tr K₀) (adminOf checkpoint.state P) A)
    (code : A.sevm.code = Impl.code) (target : A.sevm.currentTarget = P)
    (nonstatic : A.sevm.isStatic = false)
    (notRescue : Blanc.Sevm.selector A.sevm ≠ rescueSelector)
    (notAdmin : A.sevm.caller ≠ adminOf A.pre.state P) :
    ∀ c ∈ Exec.childFrames A.run,
      c.sevm.currentTarget = P ∧ c.sevm.codeAddress = some usdcLib := by
  have ext := hist.2.2.1.extend hist.2.2.2
  revert code target nonstatic notRescue notAdmin
  refine frame_cases_ok (Q := fun A => SettledFacts P (historyKeyUniverse P tr K₀)
      (adminOf checkpoint.state P) A → A.sevm.code = Impl.code → A.sevm.currentTarget = P →
    A.sevm.isStatic = false → Blanc.Sevm.selector A.sevm ≠ rescueSelector →
    A.sevm.caller ≠ adminOf A.pre.state P →
    ∀ c ∈ Exec.childFrames A.run,
      c.sevm.currentTarget = P ∧ c.sevm.codeAddress = some usdcLib) A facts.pc ?_ facts
  intro sevm pre post run committed facts code target nonstatic notRescue notAdmin c member
  obtain ⟨-, -, -, nodes⟩ := impl_whole_law ext.inj ext.apart run code target
    ((facts.kind target).impl_codeAddress code) facts.fork nonstatic (facts.keys target)
    (by rw [show pre.state.getCode usdcLib = Lib.code from facts.codes.2.2]; rfl) notAdmin
    facts.slots.2.2.1 notRescue
  obtain ⟨N, f, rsm, pc', cevm, chain, step, enter, childEq⟩ :=
    Exec.childFrames_spawnedAt run (.refl _) c member
  obtain ⟨sevmEq, nfork, -, -, -, ncodes, -, -⟩ := node_child chain facts.fork facts.codes step enter
  obtain ⟨x, hat, spawn, -⟩ := Evm.step_spawn_inv step
  have hx := nodes N chain x hat
  subst hx
  rcases impl_node run code facts.fork chain hat spawn with h | ⟨-, g, rest, stack⟩
  · cases h
  have adr : usdcLib.toB256.toAdr = usdcLib := toAdr_toB256 _
  obtain ⟨ht, hca, -⟩ := Xinst.step_delegatecall_spawn_exact nfork spawn stack
    (by rw [adr, ncodes.2.2]; exact lib_undelegated)
  rw [adr] at hca
  refine ⟨?_, ?_⟩
  · rw [childEq, Frame.enter_run_currentTarget enter, ht, sevmEq]
    exact target
  · rw [childEq, Frame.enter_run_codeAddress enter, hca]

/-- **No opaque frame covers an unshadowed position** (U6h, positional): a whole implementation
frame's block consists of library children's blocks, and a library frame's block is shadowed. -/
theorem usdc_opaque_shadowed {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) :
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      tr.settledFrames = before ++ f :: after → ¬ UsdcShadowed P tr before f →
      Exec.NoOpaqueAbove (CodeFamily.Opaque P usdcWhole) before f := by
  intro before f after split notShadowed b A m n hb desc ⟨target, nonstatic, whole⟩
  have hAs : A ∈ tr.settledFrames := by
    rw [split, hb]
    exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
  have facts := usdc_settled_facts tr hist A hAs
  rcases whole with ⟨code, notRescue⟩ | code
  · have ca := (facts.kind target).impl_codeAddress code
    have notEntry : ¬ IsEntry P A := fun h =>
      hist.1.implApart (Option.some.inj (h.2.symm.trans ca))
    obtain ⟨b0, a0, splitA⟩ := List.append_of_mem hAs
    obtain ⟨b', e, hb', -, -, -, eAdmin, caller⟩ :=
      usdc_observer_parent tr hist b0 A a0 splitA target nonstatic (.inl code) notEntry
    have he : e ∈ tr.settledFrames := by
      rw [splitA, hb']; exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
    have notAdmin : A.sevm.caller ≠ adminOf A.pre.state P := by
      have same : adminOf A.pre.state P = adminOf e.pre.state P :=
        facts.slots.2.1.trans (usdc_settled_facts tr hist e he).slots.2.1.symm
      rw [caller, same]
      exact eAdmin
    have kids := usdc_impl_children_lib tr hist facts code target nonstatic notRescue notAdmin
    rw [Exec.descendantFrames_eq_flatMap] at desc
    obtain ⟨cs₁, c, cs₂, m', n', hcs, hm, hc⟩ := List.flatMap_committed_split desc
    obtain ⟨ct, cca⟩ := kids c (by rw [hcs]; exact List.mem_append_right _ List.mem_cons_self)
    rw [Exec.Frame.committedFrames_self] at hc
    cases m' with
    | nil =>
        obtain ⟨rfl, -⟩ := List.cons.inj hc
        exact notShadowed (.inl ⟨ct, fun entry =>
          hist.1.libApart (Option.some.inj (entry.2.symm.trans cca))⟩)
    | cons y m'' =>
        obtain ⟨rfl, hd⟩ := List.cons.inj hc
        exact notShadowed (.inr ⟨b ++ A :: cs₁.flatMap (fun c => Exec.committedFrames c.run), c,
          m'', n', by rw [hb, hm]; simp only [List.append_assoc, List.cons_append], ct, cca, hd⟩)
  · have ca : A.sevm.codeAddress = some usdcLib := by
      rcases facts.kind target with ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
      · exact (lib_ne_proxy (code.symm.trans h)).elim
      · exact (lib_ne_impl (code.symm.trans h)).elim
      · exact h
    exact notShadowed (.inr ⟨b, A, m, n, hb, target, ca, desc⟩)

/-! ## The replay, good and shadow fields -/

/-- **`replayAt`** (the `usdcCore` field, U6h). -/
theorem usdc_history_replayAt {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) :
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      tr.settledFrames = before ++ f :: after → ¬ UsdcShadowed P tr before f →
      (usdcBookS P).toBook.run (ledger (historyKeyUniverse P tr K₀) (checkpoint.state.getStor P))
          (entryAsks P before) =
        some (ledger (historyKeyUniverse P tr K₀) (f.pre.state.getStor P)) := by
  intro before f after split notShadowed
  have ext := hist.2.2.1.extend hist.2.2.2
  obtain ⟨steps, replay, observed⟩ := usdc_configuredHistory_atPos P (adminOf checkpoint.state P)
    ext.inj ext.apart tr (usdc_history_admitted tr hist.1) hist.1.proxy before f after split
    (usdc_opaque_shadowed tr hist before f after split notShadowed)
  have chain := usdc_history_chain tr hist
  rw [split] at chain
  have entryAt : f.sevm.currentTarget = P → IsEntry P f := fun target => by
    by_contra notEntry
    exact notShadowed (.inl ⟨target, notEntry⟩)
  exact usdc_replay_entryAsks tr hist (fun G hG => by rw [split]; exact List.mem_append_left _ hG)
    (chain.prefix entryAt) replay observed

/-- **`replayEnd`** (U6h). -/
theorem usdc_history_replayEnd {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) :
    (usdcBookS P).toBook.run (ledger (historyKeyUniverse P tr K₀) (checkpoint.state.getStor P))
        (entryAsks P tr.settledFrames) =
      some (ledger (historyKeyUniverse P tr K₀) (future.state.getStor P)) := by
  have ext := hist.2.2.1.extend hist.2.2.2
  obtain ⟨steps, replay, observed⟩ :=
    (usdcLadder P (adminOf checkpoint.state P) ext.inj ext.apart).configuredHistory tr
      (usdc_history_admitted tr hist.1) ⟨hist.1.proxy, trivial, trivial⟩
  exact usdc_replay_entryAsks tr hist (fun _ h => h) (usdc_history_chain tr hist) replay observed

/-- **`goodStart`** (U6h). -/
theorem usdc_history_goodStart {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) :
    (usdcBookS P).toBook.Good (ledger (historyKeyUniverse P tr K₀) (checkpoint.state.getStor P)) :=
  (hist.2.2.1.extend hist.2.2.2).good

/-- **`goodAt`**, shadowed positions included (U6h; `Exec.descendant_getStor_spawnNode` and the
step laws' node clause inside whole frames). -/
theorem usdc_history_goodAt {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) :
    ∀ f ∈ tr.settledFrames,
      (usdcBookS P).toBook.Good (ledger (historyKeyUniverse P tr K₀) (f.pre.state.getStor P)) :=
  fun f hf => (usdc_settled_facts tr hist f hf).slots.2.2.1

/-- **`decodes`**: a non-entry frame at the proxy has its parents at the proxy
(`usdc_foreign_child_entry`). -/
theorem usdc_decodes {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) :
    ∀ g ∈ tr.settledFrames, g.sevm.currentTarget = P → ¬ IsEntry P g →
      ∀ Q ∈ tr.settledFrames, g ∈ Exec.childFrames Q.run → Q.sevm.currentTarget = P := by
  intro g _ target notEntry Q hQ child
  by_contra apart
  exact notEntry (usdc_foreign_child_entry (usdc_settled_facts tr hist Q hQ) child target apart)

/-- Fit check (a `Nonempty`, so it needs no compilation): the U6h facts fill `usdcCore`'s replay,
good, shadow and `decodes` fields.  The two answer fields (the proxy-forwarded `balanceOf` and
`transfer` outputs) are U7b's and enter as hypotheses. -/
example (P : Adr) (K₀ : Key → Prop)
    (balanceAnswer : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
      (tr : ConfiguredHistoryTrace cfg checkpoint future), UsdcHist P K₀ tr →
        ∀ g ∈ tr.settledFrames, IsEntry P g → ∀ {h : Adr},
          (usdcBookS P).toBook.op g.sevm = .balanceOf h → historyKeyUniverse P tr K₀ (.bal h) →
          g.post.output = (Nat.toB256 ((usdcBookS P).toBook.bal
            (ledger (historyKeyUniverse P tr K₀) (g.pre.state.getStor P)) h)).toBytes)
    (transferAnswer : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
      (tr : ConfiguredHistoryTrace cfg checkpoint future), UsdcHist P K₀ tr →
        ∀ g ∈ tr.settledFrames, IsEntry P g → ∀ {dst : Adr} {v : Nat},
          (usdcBookS P).toBook.op g.sevm = .transfer dst v →
          g.post.output = [] ∨ (32 ≤ g.post.output.length ∧
            Bytes.toB256 (g.post.output.sliceD 0 32 0) ≠ 0)) :
    Nonempty (CoreW P (usdcBookS P).toBook) :=
  ⟨{ Hist := fun tr => UsdcHist P K₀ tr
     ledgerOf := fun tr w => ledger (historyKeyUniverse P tr K₀) (w.getStor P)
     Answerable := fun tr h => historyKeyUniverse P tr K₀ (.bal h)
     Shadowed := fun tr before f => UsdcShadowed P tr before f
     shadow_kind := fun tr hist => usdc_shadow_kind tr hist
     child_unshadowed := fun tr hist => usdc_child_unshadowed tr hist
     replayAt := fun tr hist => usdc_history_replayAt tr hist
     replayEnd := fun tr hist => usdc_history_replayEnd tr hist
     goodStart := fun tr hist => usdc_history_goodStart tr hist
     goodAt := fun tr hist => usdc_history_goodAt tr hist
     balanceAnswer := fun tr hist => balanceAnswer tr hist
     transferAnswer := fun tr hist => transferAnswer tr hist
     decodes := fun tr hist => usdc_decodes tr hist }⟩

end Blanc.Lift.Usdc
