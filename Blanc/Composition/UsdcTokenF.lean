import Blanc.Composition.UsdcToken
import Blanc.Lift.Usdc.HistFCore
import Blanc.Lift.Usdc.HistFSlots
import Blanc.Lift.Usdc.HistFFacts

/-!
# USDC's support-free writer-shadowed token core (twin of `UsdcToken.lean`)

`usdcCoreF P K₀ : CoreW P (usdcBookS P).toBook` is the support-free twin of `usdcCore`:
`Hist` is `UsdcHistF P K₀` and every field comes from the `…F` facts.  Each proof below
replays its `UsdcToken.lean` original with `usdc_settled_factsF` / `usdc_entry_codeF` in
place of the `Hist`-based versions; every other lemma used (`usdc_entry_forward`,
`frame_cases_ok`, `proxy_admin_rule`, `proxy_admin_selectors`, `proxy_forwards_ok`,
`usdc_child_stor`, `usdc_foreign_child_entry`'s spawn argument, `impl_children`,
`lib_children`, `lib_quiet`, `enclosure_of_wholeBlocks`, the `impl_*_output` rows) is
support-free already and reused directly.
-/

namespace Blanc.Composition.UsdcToken

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.Usdc

/-- A settled entry frame at the proxy whose caller is the admin word asks neither `balanceOf` nor
`transfer`, support-free (twin of `usdc_entry_notAdmin`). -/
theorem usdc_entry_notAdminF {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) {g : Exec.Frame} (member : g ∈ tr.settledFrames) (entry : IsEntry P g)
    (sel : Blanc.Sevm.selector g.sevm = 0x70a08231 ∨ Blanc.Sevm.selector g.sevm = 0xa9059cbb) :
    g.sevm.caller ≠ adminOf g.pre.state P := by
  intro admin
  have facts := usdc_settled_factsF tr hist g member
  have codeEq := usdc_entry_codeF tr hist member entry
  revert admin codeEq
  refine frame_cases_ok (Q := fun g => IsEntry P g → CoveredFork g.sevm.benvStat.fork →
    (Blanc.Sevm.selector g.sevm = 0x70a08231 ∨ Blanc.Sevm.selector g.sevm = 0xa9059cbb) →
    g.sevm.caller = adminOf g.pre.state P → g.sevm.code = Proxy.code → False) g facts.pc ?_ entry
    facts.fork sel
  intro sevm pre post run _ entry fork sel admin codeEq
  have admin' : sevm.caller = adminOf pre.state sevm.currentTarget := by rw [entry.1]; exact admin
  rcases proxy_admin_selectors run codeEq fork admin' with getter | upgrade
  · rcases getter with h | h <;> rcases sel with s | s <;> rw [s] at h <;> exact absurd h (by decide)
  · rcases sel with s | s <;> rw [s] at upgrade <;> exact absurd upgrade (by decide)

/-- **A settled non-admin entry frame answers with its implementation frame**, support-free
(twin of `usdc_entry_child`). -/
theorem usdc_entry_childF {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) {g : Exec.Frame} (member : g ∈ tr.settledFrames) (entry : IsEntry P g)
    (notAdmin : g.sevm.caller ≠ adminOf g.pre.state P) :
    ∃ c ∈ tr.settledFrames, g.post.output = c.post.output ∧ c.sevm.currentTarget = P ∧
      c.sevm.code = Impl.code ∧ c.sevm.data = g.sevm.data ∧
      c.pre.state.getStor P = g.pre.state.getStor P := by
  have facts := usdc_settled_factsF tr hist g member
  have codeEq := usdc_entry_codeF tr hist member entry
  obtain ⟨before, after, split⟩ := List.append_of_mem member
  obtain ⟨r, hafter⟩ := tr.settledFrames_contig split
  have inDesc : ∀ c ∈ Exec.descendantFrames g.run, c ∈ tr.settledFrames := fun c hc => by
    rw [split, hafter]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ hc))
  revert inDesc codeEq notAdmin
  refine frame_cases_ok (Q := fun g => IsEntry P g → SettledFactsF P (historyKeyUniverse P tr K₀)
    (adminOf checkpoint.state P) g → g.sevm.caller ≠ adminOf g.pre.state P →
    g.sevm.code = Proxy.code → (∀ c ∈ Exec.descendantFrames g.run, c ∈ tr.settledFrames) →
    ∃ c ∈ tr.settledFrames, g.post.output = c.post.output ∧ c.sevm.currentTarget = P ∧
      c.sevm.code = Impl.code ∧ c.sevm.data = g.sevm.data ∧
      c.pre.state.getStor P = g.pre.state.getStor P) g facts.pc ?_ entry facts
  intro sevm pre post run _ entry facts notAdmin codeEq inDesc
  obtain ⟨c, one, desc, ct, -, -, -, cdata, -, ccode⟩ :=
    usdc_entry_forward run codeEq facts.fork entry.1 facts.codes facts.slots.1 notAdmin facts.data
  have notAdmin' : sevm.caller ≠ adminOf pre.state sevm.currentTarget := by rw [entry.1]; exact notAdmin
  obtain ⟨c', member', out, -⟩ := proxy_forwards_ok run codeEq facts.fork
    (by rw [entry.1]; exact facts.slots.1) notAdmin'
    (by rw [show pre.state.getCode usdcImpl = Impl.code from facts.codes.2.1]; exact impl_undelegated)
    (impl_not_precompile facts.fork) post rfl
  rw [one, List.mem_singleton] at member'
  subst member'
  exact ⟨c', inDesc c' (by rw [desc]; exact List.mem_cons_self), out, ct, ccode, cdata,
    usdc_child_stor run codeEq facts.fork facts.codes notAdmin' c' (by rw [one]; exact List.mem_singleton_self _)⟩

/-- A direct child at the proxy of a settled frame elsewhere is an entry, support-free
(twin of `usdc_foreign_child_entry`; the proof reads only `pc`/`fork`/`codes`). -/
theorem usdc_foreign_child_entryF {P : Adr} {U : Key → Prop} {A₀ : Adr} {G : Exec.Frame}
    (facts : SettledFactsF P U A₀ G) {c : Exec.Frame} (member : c ∈ Exec.childFrames G.run)
    (target : c.sevm.currentTarget = P) (apart : G.sevm.currentTarget ≠ P) : IsEntry P c := by
  refine ⟨target, ?_⟩
  revert member apart
  refine frame_cases_ok (Q := fun G => SettledFactsF P U A₀ G → c ∈ Exec.childFrames G.run →
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

/-- **`shadow_kindF`**, support-free (twin of `usdc_shadow_kind`). -/
theorem usdc_shadow_kindF {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) :
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
    have facts := usdc_settled_factsF tr hist A hA
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

/-- **`child_unshadowedF`**, support-free (twin of `usdc_child_unshadowed`). -/
theorem usdc_child_unshadowedF {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) :
    ∀ (before : List Exec.Frame) (Q : Exec.Frame) (m : List Exec.Frame) (c : Exec.Frame)
      (after : List Exec.Frame),
      tr.settledFrames = before ++ Q :: (m ++ c :: after) → Q.sevm.currentTarget ≠ P →
        ¬ UsdcShadowed P tr before Q → WholeBlocks m → c ∈ Exec.childFrames Q.run →
          ¬ UsdcShadowed P tr (before ++ Q :: m) c := by
  intro before Q m c after split apart lit whole child shadowed
  rcases shadowed with ⟨target, notEntry⟩ | ⟨b, A, m', n, hsplit, target, ca, desc⟩
  · have hQ : Q ∈ tr.settledFrames := by rw [split]; exact List.mem_append_right _ List.mem_cons_self
    exact notEntry (usdc_foreign_child_entryF (usdc_settled_factsF tr hist Q hQ) child target apart)
  · rcases enclosure_of_wholeBlocks hsplit desc whole with rfl | ⟨x, hb, descQ⟩
    · exact apart target
    · exact lit (.inr ⟨b, A, x, m ++ c :: n, hb, target, ca, descQ⟩)

/-- **`decodesF`**, support-free (twin of `usdc_decodes`). -/
theorem usdc_decodesF {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) :
    ∀ g ∈ tr.settledFrames, g.sevm.currentTarget = P → ¬ IsEntry P g →
      ∀ Q ∈ tr.settledFrames, g ∈ Exec.childFrames Q.run → Q.sevm.currentTarget = P := by
  intro g _ target notEntry Q hQ child
  by_contra apart
  exact notEntry (usdc_foreign_child_entryF (usdc_settled_factsF tr hist Q hQ) child target apart)

/-- **`balanceAnswerF`**, support-free (twin of `usdc_balanceAnswer`). -/
theorem usdc_balanceAnswerF {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) :
    ∀ g ∈ tr.settledFrames, IsEntry P g → ∀ {h : Adr},
      (usdcBookS P).toBook.op g.sevm = .balanceOf h → historyKeyUniverse P tr K₀ (.bal h) →
      g.post.output = (Nat.toB256 ((usdcBookS P).toBook.bal
        (ledger (historyKeyUniverse P tr K₀) (g.pre.state.getStor P)) h)).toBytes := by
  intro g member entry h hop row
  obtain ⟨sel, hh⟩ := usdcOp_balanceOf hop
  obtain ⟨c, cmem, out, ct, ccode, cdata, cstor⟩ :=
    usdc_entry_childF tr hist member entry (usdc_entry_notAdminF tr hist member entry (.inl sel))
  have cfacts := usdc_settled_factsF tr hist c cmem
  obtain ⟨stackNil, memEmpty⟩ := tr.settledFrames_fresh c cmem
  have hw : Sevm.dataWord c.sevm = Sevm.dataWord g.sevm := dataWord_congr cdata
  have sel' : Blanc.Sevm.selector c.sevm = 0x70a08231 := by
    unfold Blanc.Sevm.selector; rw [hw]; exact sel
  rw [out]
  revert ct ccode stackNil memEmpty sel' cstor hw
  refine frame_cases_ok (Q := fun c => CoveredFork c.sevm.benvStat.fork →
    c.sevm.currentTarget = P → c.sevm.code = Impl.code →
    c.pre.state.getStor P = g.pre.state.getStor P → c.pre.stack = [] → c.pre.memory = Mem.empty →
    Sevm.dataWord c.sevm = Sevm.dataWord g.sevm → Blanc.Sevm.selector c.sevm = 0x70a08231 →
    c.post.output = (Nat.toB256 ((usdcBookS P).toBook.bal
      (ledger (historyKeyUniverse P tr K₀) (g.pre.state.getStor P)) h)).toBytes) c cfacts.pc ?_
    cfacts.fork
  intro sevm pre post run _ fork ct ccode cstor stackNil memEmpty hw sel'
  change post.output = _
  rw [impl_balanceOf_output run ccode fork stackNil memEmpty sel', ct, hw, ← hh]
  change _ = (Nat.toB256 (balanceBits (SlotFootprint.trackedWord Key.slot (historyKeyUniverse P tr K₀)
    (g.pre.state.getStor P) (.bal h)))).toBytes
  rw [SlotFootprint.trackedWord_of_mem row, ← cstor, ← low255_and_toNat, toB256_toNat]
  rfl

/-- **`transferAnswerF`**, support-free (twin of `usdc_transferAnswer`). -/
theorem usdc_transferAnswerF {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) :
    ∀ g ∈ tr.settledFrames, IsEntry P g → ∀ {dst : Adr} {v : Nat},
      (usdcBookS P).toBook.op g.sevm = .transfer dst v →
      g.post.output = [] ∨ (32 ≤ g.post.output.length ∧
        Bytes.toB256 (g.post.output.sliceD 0 32 0) ≠ 0) := by
  intro g member entry dst v hop
  have sel := (usdcOp_transfer hop).1
  obtain ⟨c, cmem, out, -, ccode, cdata, -⟩ :=
    usdc_entry_childF tr hist member entry (usdc_entry_notAdminF tr hist member entry (.inr sel))
  have cfacts := usdc_settled_factsF tr hist c cmem
  obtain ⟨stackNil, memEmpty⟩ := tr.settledFrames_fresh c cmem
  have sel' : Blanc.Sevm.selector c.sevm = 0xa9059cbb := by
    unfold Blanc.Sevm.selector; rw [dataWord_congr cdata]; exact sel
  rw [out]
  revert ccode stackNil memEmpty sel'
  refine frame_cases_ok (Q := fun c => CoveredFork c.sevm.benvStat.fork →
    c.sevm.code = Impl.code → c.pre.stack = [] → c.pre.memory = Mem.empty →
    Blanc.Sevm.selector c.sevm = 0xa9059cbb →
    c.post.output = [] ∨ (32 ≤ c.post.output.length ∧
      Bytes.toB256 (c.post.output.sliceD 0 32 0) ≠ 0)) c cfacts.pc ?_ cfacts.fork
  intro sevm pre post run _ fork ccode stackNil memEmpty sel'
  change post.output = [] ∨ (32 ≤ post.output.length ∧ Bytes.toB256 (post.output.sliceD 0 32 0) ≠ 0)
  rw [impl_transfer_output run ccode fork stackNil memEmpty sel']
  exact Weth9Token.true_word_accepted

/-! ## The instance -/

/-- **USDC is an instance of the writer-shadowed core over its support-free history**
(twin of `usdcCore`). -/
noncomputable def usdcCoreF (P : Adr) (K₀ : Key → Prop) : CoreW P (usdcBookS P).toBook where
  Hist tr := UsdcHistF P K₀ tr
  ledgerOf tr w := ledger (historyKeyUniverse P tr K₀) (w.getStor P)
  Answerable tr h := historyKeyUniverse P tr K₀ (.bal h)
  Shadowed tr before f := UsdcShadowed P tr before f
  shadow_kind tr hist := usdc_shadow_kindF tr hist
  child_unshadowed tr hist := usdc_child_unshadowedF tr hist
  replayAt tr hist := usdc_history_replayAtF tr hist
  replayEnd tr hist := usdc_history_replayEndF tr hist
  goodStart tr hist := usdc_history_goodStartF tr hist
  goodAt tr hist := usdc_history_goodAtF tr hist
  balanceAnswer tr hist := usdc_balanceAnswerF tr hist
  transferAnswer tr hist := usdc_transferAnswerF tr hist
  decodes tr hist := usdc_decodesF tr hist

/-- USDC never forwards a foreign caller into its own entry, support-free
(twin of `usdcSelfCaller`). -/
theorem usdcSelfCallerF (P : Adr) (K₀ : Key → Prop) : SelfCallerW (usdcCoreF P K₀) := by
  refine ⟨fun tr hist G member target _ c child entry => ?_⟩
  have facts := usdc_settled_factsF tr hist G member
  have installed : UsdcInstalled P _ := hist.1
  revert child
  refine frame_cases_ok (Q := fun G => SettledFactsF P (historyKeyUniverse P tr K₀)
    (adminOf _ P) G → G.sevm.currentTarget = P → c ∈ Exec.childFrames G.run → c.sevm.caller = P)
    G facts.pc ?_ facts target
  intro sevm pre post run _ facts target child
  rcases facts.kind target with ⟨-, codeEq⟩ | ⟨-, codeEq⟩ | ⟨-, codeEq⟩
  · by_cases admin : sevm.caller = adminOf pre.state P
    · have admin' : sevm.caller = adminOf pre.state sevm.currentTarget := by rw [target]; exact admin
      rw [← target]
      exact ((proxy_admin_rule run codeEq facts.fork admin').2.1 c child).2
    · obtain ⟨c', one, -, -, cca, -⟩ :=
        usdc_entry_forward run codeEq facts.fork target facts.codes facts.slots.1 admin facts.data
      rw [one, List.mem_singleton] at child
      subst child
      exact (installed.implApart (Option.some.inj (entry.2.symm.trans cca))).elim
  · rcases impl_children run codeEq facts.fork facts.codes.2.2 c child with
      ⟨-, cca, -⟩ | ⟨caller, -⟩
    · exact (installed.libApart (Option.some.inj (entry.2.symm.trans cca))).elim
    · rw [caller, target]
  · rw [((lib_children run codeEq facts.fork).1 c child).2, target]

end Blanc.Composition.UsdcToken
