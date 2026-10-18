import Blanc.Composition.UsdcTokenCore
import Blanc.Composition.Weth9TokenCore
import Blanc.Lift.Usdc.HistoryReplay
import Blanc.Lift.Usdc.ProxyOk
import Blanc.Lift.Token.Abi

/-!
# USDC is an instance of the writer-shadowed token core (C5, U7b)

`usdcCore P K₀ : CoreW P (usdcBookS P).toBook`.  The replay, good, shadow and `decodes` fields are
U6h's (`Blanc/Lift/Usdc/HistoryReplay.lean`).  The two answer fields are here:

* a settled entry frame at the proxy whose caller is the admin word commits only as an admin getter
  or an upgrade (`proxy_admin_selectors`), never as `balanceOf`/`transfer`;
* any other settled entry frame forwards to one implementation frame (`usdc_entry_forward`) and ends
  in its output (`proxy_forwards_ok`); that child is a settled fresh frame whose storage at the proxy
  is its parent's (the proxy writes nothing before its `DELEGATECALL`, `usdc_child_stor`), and it
  answers `balanceOf(h)` with `h`'s balance bits and `transfer` with `1`
  (`impl_balanceOf_output`, `impl_transfer_output`, `UsdcTokenCore.lean`).

`usdcSelfCaller`: the proxy's children are the admin branch's self-calls (caller the proxy) or the
implementation frame (not an entry, `P ≠ usdcImpl`); the implementation's are library frames (not
entries) or calls with the proxy as caller; the library's are static calls with the proxy as caller.
`usdcBook_erc20Abi`: `usdcOp` reads the two selectors first.
-/

namespace Blanc.Composition.UsdcToken

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.Usdc

/-- `Exec.childFrames_spawnedAt`, with the child's pre-state: every direct child of a chain suffix
is the entered frame of a spawning node of the chain, starting in the entered machine's state. -/
theorem childFrames_spawnedAt_pre {root : Exec.Deriv} :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      Exec.Deriv.ParentPrefix root ⟨pc, sevm, pre, out, run⟩ →
      ∀ c ∈ Exec.childFrames run, ∃ (N : Exec.Deriv) (f : Frame) (rsm : Resume) (pc' : Nat)
        (cevm : Evm), Exec.Deriv.ParentPrefix root N ∧
          Evm.step ⟨N.pc, N.sevm, N.devm⟩ = .spawn f rsm pc' ∧ f.enter = .run cevm ∧
          c.pre = cevm.dyna := by
  intro pc sevm pre out run
  induction run with
  | halt _ =>
      intro _ c member
      simp only [Exec.childFrames, List.not_mem_nil] at member
  | cont step next ih =>
      intro chain
      simpa only [Exec.childFrames] using ih (chain.snoc (.cont step next))
  | doneErr _ _ _ =>
      intro _ c member
      simp only [Exec.childFrames, List.not_mem_nil] at member
  | doneOk step enter resume next ih =>
      intro chain
      simpa only [Exec.childFrames] using ih (chain.snoc (.doneOk step enter resume next))
  | runErr _ _ _ _ =>
      intro _ c member
      simp only [Exec.childFrames, List.not_mem_nil] at member
  | runOk step enter child resume next childIh nextIh =>
      intro chain c member
      simp only [Exec.childFrames, List.mem_append] at member
      rcases member with here | later
      · split at here
        · rw [List.mem_singleton] at here
          subst here
          exact ⟨_, _, _, _, _, chain, step, enter, rfl⟩
        · simp only [List.not_mem_nil] at here
      · exact nextIh (chain.snoc (.runOk step enter child resume next)) c later

/-- **The proxy writes nothing before it forwards**: a direct child of a non-admin pc-`0` proxy
frame starts with the frame's storage at the proxy. -/
theorem usdc_child_stor {P : Adr} {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (codeEq : sevm.code = Proxy.code) (fork : CoveredFork sevm.benvStat.fork) (codes : Codes P pre)
    (notAdmin : sevm.caller ≠ adminOf pre.state sevm.currentTarget) :
    ∀ c ∈ Exec.childFrames run, c.pre.state.getStor P = pre.state.getStor P := by
  intro c member
  obtain ⟨N, f, rsm, pc', cevm, chain, step, enter, preEq⟩ :=
    childFrames_spawnedAt_pre run (.refl _) c member
  obtain ⟨x, hat, -, -⟩ := Evm.step_spawn_inv step
  obtain ⟨g, K, ⟨-, hd⟩ | ⟨-, hs, -⟩⟩ := proxy_node run codeEq fork chain hat
  swap
  · exact (notAdmin (by rw [adminOf_eq]; exact hs.1)).elim
  obtain ⟨-, b', w0, S0, M0, G0, rest0, hstate0, -, hdev⟩ := hd
  change N.devm = _ at hdev
  obtain ⟨-, -, -, -, -, -, -, cstor⟩ := node_child chain fork codes step enter
  rw [preEq, cstor, hdev]
  exact congrArg (State.getStor · P) hstate0

/-- A `balanceOf` ask has the `balanceOf` selector and names its holder by the argument word. -/
theorem usdcOp_balanceOf {e : Sevm} {h : Adr} (op : usdcOp e = .balanceOf h) :
    Blanc.Sevm.selector e = 0x70a08231 ∧ h = (Sevm.dataWord e 4).toAdr := by
  unfold usdcOp at op
  by_cases bal : 36 ≤ e.data.length ∧ Blanc.Sevm.selector e = 0x70a08231
  · rw [ite_eq_left bal] at op
    exact ⟨bal.2, (Op.balanceOf.inj op).symm⟩
  · rw [ite_eq_right bal] at op
    by_cases xfer : 68 ≤ e.data.length ∧ Blanc.Sevm.selector e = 0xa9059cbb
    · rw [ite_eq_left xfer] at op
      cases op
    · rw [ite_eq_right xfer] at op
      split at op <;> cases op

/-- A settled entry frame at the proxy whose caller is the admin word asks neither `balanceOf` nor
`transfer`: it commits only as an admin getter or an upgrade. -/
theorem usdc_entry_notAdmin {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) {g : Exec.Frame} (member : g ∈ tr.settledFrames) (entry : IsEntry P g)
    (sel : Blanc.Sevm.selector g.sevm = 0x70a08231 ∨ Blanc.Sevm.selector g.sevm = 0xa9059cbb) :
    g.sevm.caller ≠ adminOf g.pre.state P := by
  intro admin
  have facts := usdc_settled_facts tr hist g member
  have codeEq := usdc_entry_code tr hist member entry
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

/-- **A settled non-admin entry frame answers with its implementation frame**: the frame's one child
is a settled implementation frame at the proxy, fresh, with the entry's message and storage, whose
output the entry frame returns. -/
theorem usdc_entry_child {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) {g : Exec.Frame} (member : g ∈ tr.settledFrames) (entry : IsEntry P g)
    (notAdmin : g.sevm.caller ≠ adminOf g.pre.state P) :
    ∃ c ∈ tr.settledFrames, g.post.output = c.post.output ∧ c.sevm.currentTarget = P ∧
      c.sevm.code = Impl.code ∧ c.sevm.data = g.sevm.data ∧
      c.pre.state.getStor P = g.pre.state.getStor P := by
  have facts := usdc_settled_facts tr hist g member
  have codeEq := usdc_entry_code tr hist member entry
  obtain ⟨before, after, split⟩ := List.append_of_mem member
  obtain ⟨r, hafter⟩ := tr.settledFrames_contig split
  have inDesc : ∀ c ∈ Exec.descendantFrames g.run, c ∈ tr.settledFrames := fun c hc => by
    rw [split, hafter]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ hc))
  revert inDesc codeEq notAdmin
  refine frame_cases_ok (Q := fun g => IsEntry P g → SettledFacts P (historyKeyUniverse P tr K₀)
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

/-- **`balanceAnswer`**: a settled `balanceOf(h)` entry frame at the proxy, static or not, answers
the booked balance of a tracked holder at its entry. -/
theorem usdc_balanceAnswer {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) :
    ∀ g ∈ tr.settledFrames, IsEntry P g → ∀ {h : Adr},
      (usdcBookS P).toBook.op g.sevm = .balanceOf h → historyKeyUniverse P tr K₀ (.bal h) →
      g.post.output = (Nat.toB256 ((usdcBookS P).toBook.bal
        (ledger (historyKeyUniverse P tr K₀) (g.pre.state.getStor P)) h)).toBytes := by
  intro g member entry h hop row
  obtain ⟨sel, hh⟩ := usdcOp_balanceOf hop
  obtain ⟨c, cmem, out, ct, ccode, cdata, cstor⟩ :=
    usdc_entry_child tr hist member entry (usdc_entry_notAdmin tr hist member entry (.inl sel))
  have cfacts := usdc_settled_facts tr hist c cmem
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

/-- **`transferAnswer`**: a settled `transfer` entry frame at the proxy answers `true`. -/
theorem usdc_transferAnswer {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) :
    ∀ g ∈ tr.settledFrames, IsEntry P g → ∀ {dst : Adr} {v : Nat},
      (usdcBookS P).toBook.op g.sevm = .transfer dst v →
      g.post.output = [] ∨ (32 ≤ g.post.output.length ∧
        Bytes.toB256 (g.post.output.sliceD 0 32 0) ≠ 0) := by
  intro g member entry dst v hop
  have sel := (usdcOp_transfer hop).1
  obtain ⟨c, cmem, out, -, ccode, cdata, -⟩ :=
    usdc_entry_child tr hist member entry (usdc_entry_notAdmin tr hist member entry (.inr sel))
  have cfacts := usdc_settled_facts tr hist c cmem
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

/-- **USDC is an instance of the writer-shadowed core** (C5; U7b assembles it from U6). -/
noncomputable def usdcCore (P : Adr) (K₀ : Key → Prop) : CoreW P (usdcBookS P).toBook where
  Hist tr := UsdcHist P K₀ tr
  ledgerOf tr w := ledger (historyKeyUniverse P tr K₀) (w.getStor P)
  Answerable tr h := historyKeyUniverse P tr K₀ (.bal h)
  Shadowed tr before f := UsdcShadowed P tr before f
  shadow_kind tr hist := usdc_shadow_kind tr hist
  child_unshadowed tr hist := usdc_child_unshadowed tr hist
  replayAt tr hist := usdc_history_replayAt tr hist
  replayEnd tr hist := usdc_history_replayEnd tr hist
  goodStart tr hist := usdc_history_goodStart tr hist
  goodAt tr hist := usdc_history_goodAt tr hist
  balanceAnswer tr hist := usdc_balanceAnswer tr hist
  transferAnswer tr hist := usdc_transferAnswer tr hist
  decodes tr hist := usdc_decodes tr hist

/-- USDC never forwards a foreign caller into its own entry (U7b): the proxy's children are
implementation frames (not entries, `usdcImpl ≠ P`), the implementation's are library frames or
`CALL`s with the proxy as caller, the library's are static calls with the proxy as caller. -/
theorem usdcSelfCaller (P : Adr) (K₀ : Key → Prop) : SelfCallerW (usdcCore P K₀) := by
  refine ⟨fun tr hist G member target _ c child entry => ?_⟩
  have facts := usdc_settled_facts tr hist G member
  have installed : UsdcInstalled P _ := hist.1
  revert child
  refine frame_cases_ok (Q := fun G => SettledFacts P (historyKeyUniverse P tr K₀)
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

theorem usdcBook_erc20Abi (P : Adr) : Erc20Abi (usdcBookS P).toBook := by
  refine ⟨fun a long _ sel => ?_, fun a long _ sel => ?_⟩
  · change usdcOp a = _
    unfold usdcOp
    rw [ite_eq_right (fun h => absurd (sel.symm.trans h.2) (by decide)), ite_eq_left ⟨long, sel⟩]
  · change usdcOp a = _
    unfold usdcOp
    rw [ite_eq_left ⟨long, sel⟩]

end Blanc.Composition.UsdcToken
