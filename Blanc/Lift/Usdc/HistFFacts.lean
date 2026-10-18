import Blanc.Lift.Usdc.HistFSlots
import Blanc.Lift.Usdc.HistoryReplayFrames
import Blanc.Lift.Usdc.HistoryFamily
import Blanc.Lift.Usdc.HistoryReplay
import Blanc.Lift.Usdc.HistoryEnd

/-!
# USDC's support-free history facts (twins of U6h2/U9c over `UsdcHistF`)

Twins of the history facts the composition uses, each taking `UsdcHistF`: the settled-frame
facts (`SettledFactsF`, `usdc_settled_factsF`), the observer pairing (`usdc_entry_observerF`,
`usdc_observer_parentF`), the allowed messages (`usdc_allowedF`), the observer chain
(`usdc_history_chainF`), the replay facts (`usdc_history_replayAtF`,
`usdc_history_replayEndF`, `usdc_history_goodStartF`, `usdc_history_goodAtF`), and the end
facts (`usdc_history_end_installedF`, `usdc_history_end_coreF`).

Every proof reuses an existing support-free lemma or reads only `inj`/`apart`/`good` (slots
`.1`/`.2.1`/`.2.2`) of the checkpoint footprint: `usdc_entry_forward`, `frame_cases_ok`,
`impl_whole_law`, `usdc_history_admitted`, `usdcLadder`, `usdc_configuredHistory_atPos`,
`guardedBook_run` and `history_end_codeImage` are reused directly.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay Blanc.Lift.Token

/-! ## Frame facts -/

/-- What a support-free history gives at a settled frame: the twin of `SettledFacts` with the
support-free slot invariant. -/
structure SettledFactsF (P : Adr) (U : Key → Prop) (A₀ : Adr) (G : Exec.Frame) : Prop where
  pc : G.pc = 0
  fork : CoveredFork G.sevm.benvStat.fork
  codes : Codes P G.pre
  slots : SlotInvF U A₀ (G.pre.state.getStor P)
  kind : G.sevm.currentTarget = P → OwnerKind P G.sevm
  keys : G.sevm.currentTarget = P → ∀ k ∈ frameKeys G.sevm, U k
  data : G.sevm.data.length < 2 ^ 256
  gov : IsEntry P G → G.sevm.caller = A₀ →
    Blanc.Sevm.selector G.sevm ∉ [0x3659cfe6, 0x4f1ef286, 0x8f283970]

/-- **The facts at every settled frame** of a `UsdcHistF` history. -/
theorem usdc_settled_factsF {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) :
    ∀ G ∈ tr.settledFrames,
      SettledFactsF P (historyKeyUniverse P tr K₀) (adminOf checkpoint.state P) G := by
  intro G hG
  have installed := hist.1
  have gov := hist.2.1
  have own := tr.settled_ownCode lib_toList_ne_nil (libSem.not_delegation (code := Lib.code) rfl)
    lib_ownSpawns (bytes_eq_of_image installed.lib) G hG
  have q := (usdc_history_frames_ofF impl_signed_law tr hist).1 G hG
  have raw := tr.settled_mem_rawFrames G hG
  have admitted := (tr.frameAdmitted_iff_rawFrames P _).1
    (usdc_history_admitted (K₀ := K₀) tr installed) _ raw
  refine ⟨own.2.1, own.2.2.1, ⟨bytes_eq_of_image (tr.settled_codeImage proxySem P installed.proxy G hG),
    bytes_eq_of_image (tr.settled_codeImage implSem usdcImpl installed.impl G hG),
    bytes_eq_of_image (tr.settled_codeImage libSem usdcLib installed.lib G hG)⟩, q.1, q.2.2,
    fun target => (admitted target).1, tr.calldata_bound _ raw, gov G hG⟩

/-- **The parent of a non-static non-entry implementation child at the proxy**, support-free:
the twin of `usdc_impl_parent`. -/
theorem usdc_impl_parentF {P : Adr} {U : Key → Prop} {A₀ : Adr} {G : Exec.Frame}
    (facts : SettledFactsF P U A₀ G)
    {c : Exec.Frame} (member : c ∈ Exec.childFrames G.run) (target : c.sevm.currentTarget = P)
    (notEntry : c.sevm.codeAddress ≠ some P) (nonstatic : c.sevm.isStatic = false)
    (code : c.sevm.code = Impl.code) :
    G.sevm.currentTarget = P ∧ G.sevm.codeAddress = some P ∧ G.sevm.code = Proxy.code ∧
      G.sevm.caller ≠ adminOf G.pre.state P := by
  revert member
  refine frame_cases_ok (Q := fun G => SettledFactsF P U A₀ G → c ∈ Exec.childFrames G.run →
    G.sevm.currentTarget = P ∧ G.sevm.codeAddress = some P ∧ G.sevm.code = Proxy.code ∧
      G.sevm.caller ≠ adminOf G.pre.state P) G facts.pc ?_ facts
  intro sevm pre post run committed facts member
  obtain ⟨N, f, rsm, pc', cevm, chain, step, enter, childEq⟩ :=
    Exec.childFrames_spawnedAt run (.refl _) c member
  obtain ⟨x, hat, spawn, -⟩ := Evm.step_spawn_inv step
  obtain ⟨sevmEq, nfork, -, -, -, ncodes, -, -⟩ := node_child chain facts.fork facts.codes step enter
  have innerTarget : f.inner.currentTarget = P := by
    rw [← Frame.enter_run_currentTarget enter, ← childEq, target]
  have codeNe : N.devm.getCode P ≠ .empty := fun empty => proxy_nonempty (by
    rw [← ncodes.1, empty]; simp only [ByteArray.toList_empty])
  -- a `CALL`/`STATICCALL` child at the proxy is an entry
  have callEntry : x = .call ∨ x = .staticcall → False := fun kind => notEntry (by
    rw [childEq]; exact (entry_child kind spawn enter ncodes.1 (by rw [← childEq]; exact target)).1)
  by_cases same : sevm.currentTarget = P
  · rcases facts.kind same with ⟨ca, codeEq⟩ | ⟨-, codeEq⟩ | ⟨-, codeEq⟩
    · by_cases admin : sevm.caller = adminOf pre.state P
      · have admin' : sevm.caller = adminOf pre.state sevm.currentTarget := by rw [same]; exact admin
        exact (callEntry (.inl ((proxy_admin_rule run codeEq facts.fork admin').1 N chain x hat))).elim
      · exact ⟨same, ca, codeEq, admin⟩
    · rcases impl_node run codeEq facts.fork chain hat spawn with h | ⟨rfl, g, rest, stack⟩
      · exact (callEntry (.inl h)).elim
      have adr : usdcLib.toB256.toAdr = usdcLib := toAdr_toB256 _
      have nfork' : CoveredFork N.sevm.benvStat.fork := nfork
      obtain ⟨-, -, -, -, -, hK, -⟩ := Xinst.step_delegatecall_spawn_exact nfork' spawn stack
        (by rw [adr, ncodes.2.2]; exact lib_undelegated)
      rw [adr] at hK
      have ccode : c.sevm.code = Lib.code := by
        rw [childEq, Frame.enter_run_code enter, hK]; exact ncodes.2.2
      exact (lib_ne_impl (ccode.symm.trans code)).elim
    · have := ((lib_children run codeEq facts.fork).1 c member).1
      rw [nonstatic] at this
      exact Bool.noConfusion this
  · have hne : N.sevm.currentTarget ≠ f.inner.currentTarget := by
      rw [sevmEq, innerTarget]; exact same
    have ca := Xinst.step_spawn_codeAddress_eq_currentTarget spawn hne (by rw [innerTarget]; exact codeNe)
      (by rw [innerTarget, ncodes.1]; exact proxy_undelegated)
    exact (notEntry (by rw [childEq, Frame.enter_run_codeAddress enter, ca, innerTarget])).elim

/-! ## The observer pairing along the settled frames -/

section HistoryF

variable {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}

/-- The proxy's code at a settled entry frame, support-free. -/
theorem usdc_entry_codeF (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) {G : Exec.Frame} (hG : G ∈ tr.settledFrames) (entry : IsEntry P G) :
    G.sevm.code = Proxy.code :=
  ((usdc_settled_factsF tr hist G hG).kind entry.1).entry_code entry.2 hist.1.implApart
    hist.1.libApart

/-- **An entry frame not observing is followed by its observer**, support-free. -/
theorem usdc_entry_observerF (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) :
    ∀ b f a, tr.settledFrames = b ++ f :: a → IsEntry P f → f.sevm.isStatic = false →
      ¬ usdcObs P f →
      ∃ o a', a = o :: a' ∧ o.sevm.currentTarget = P ∧ o.sevm.isStatic = false ∧ usdcObs P o ∧
        ¬ IsEntry P o ∧ usdcRelated f.sevm o.sevm := by
  intro b f a split entry nonstatic notObs
  have hf : f ∈ tr.settledFrames := by rw [split]; exact List.mem_append_right _ List.mem_cons_self
  have facts := usdc_settled_factsF tr hist f hf
  have codeEq := usdc_entry_codeF tr hist hf entry
  have notAdmin : f.sevm.caller ≠ adminOf f.pre.state P := fun h => notObs (.inr ⟨codeEq, h⟩)
  obtain ⟨r, ha⟩ := tr.settledFrames_contig split
  revert ha
  refine frame_cases_ok (Q := fun f => IsEntry P f → f.sevm.isStatic = false →
    f.sevm.code = Proxy.code → f.sevm.caller ≠ adminOf f.pre.state P → SettledFactsF P
      (historyKeyUniverse P tr K₀) (adminOf checkpoint.state P) f →
    a = Exec.descendantFrames f.run ++ r →
    ∃ o a', a = o :: a' ∧ o.sevm.currentTarget = P ∧ o.sevm.isStatic = false ∧ usdcObs P o ∧
        ¬ IsEntry P o ∧ usdcRelated f.sevm o.sevm) f facts.pc ?_ entry nonstatic codeEq notAdmin
    facts
  intro sevm pre post run committed entry nonstatic codeEq notAdmin facts ha
  obtain ⟨c, -, desc, ct, cca, ccaller, cvalue, cdata, cstatic, ccode⟩ :=
    usdc_entry_forward run codeEq facts.fork entry.1 facts.codes facts.slots.1 notAdmin facts.data
  refine ⟨c, _, by rw [ha]; exact congrArg (· ++ r) desc, ct, cstatic.trans nonstatic, .inl ccode,
    fun h => hist.1.implApart (Option.some.inj (h.2.symm.trans cca)),
    ccaller.symm, cvalue.symm, cdata.symm⟩

/-- **An observer that is no entry follows its entry frame**, support-free. -/
theorem usdc_observer_parentF (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) :
    ∀ b f a, tr.settledFrames = b ++ f :: a → f.sevm.currentTarget = P →
      f.sevm.isStatic = false → usdcObs P f → ¬ IsEntry P f →
      ∃ b' e, b = b' ++ [e] ∧ IsEntry P e ∧ e.sevm.isStatic = false ∧ ¬ usdcObs P e ∧
        e.sevm.caller ≠ adminOf e.pre.state P ∧ f.sevm.caller = e.sevm.caller := by
  intro b f a split target nonstatic obs notEntry
  have hf : f ∈ tr.settledFrames := by rw [split]; exact List.mem_append_right _ List.mem_cons_self
  have ffacts := usdc_settled_factsF tr hist f hf
  have notCA : f.sevm.codeAddress ≠ some P := fun h => notEntry ⟨target, h⟩
  have code : f.sevm.code = Impl.code := by
    rcases obs with h | ⟨h, -⟩
    · exact h
    · rcases ffacts.kind target with ⟨ca, -⟩ | ⟨-, h'⟩ | ⟨-, h'⟩
      · exact (notCA ca).elim
      · exact h'
      · exact (lib_ne_proxy (h'.symm.trans h)).elim
  obtain ⟨b₁, G, b₂, hb, child, len⟩ :=
    tr.settledFrames_parent_of_codeAddress (usdcSpec_preserves_trivial P)
      (c := usdcSpec) ⟨hist.1.proxy, trivial, trivial⟩ b f a split target notCA
  have split' : tr.settledFrames = b₁ ++ G :: (b₂ ++ f :: a) := by
    rw [split, hb, List.append_assoc, List.cons_append]
  have hG : G ∈ tr.settledFrames := by rw [split']; exact List.mem_append_right _ List.mem_cons_self
  have gfacts := usdc_settled_factsF tr hist G hG
  obtain ⟨gt, gca, gcode, gadmin⟩ := usdc_impl_parentF gfacts child
    target notCA nonstatic code
  obtain ⟨r, hr⟩ := tr.settledFrames_contig split'
  subst hb
  revert child len hr
  refine frame_cases_ok (Q := fun G => G.sevm.currentTarget = P → G.sevm.codeAddress = some P →
    G.sevm.code = Proxy.code → G.sevm.caller ≠ adminOf G.pre.state P → SettledFactsF P (historyKeyUniverse P tr K₀)
      (adminOf checkpoint.state P) G →
    f ∈ Exec.childFrames G.run → b₂.length < (Exec.descendantFrames G.run).length →
    b₂ ++ f :: a = Exec.descendantFrames G.run ++ r →
    ∃ b' e, b₁ ++ G :: b₂ = b' ++ [e] ∧ IsEntry P e ∧ e.sevm.isStatic = false ∧ ¬ usdcObs P e ∧
      e.sevm.caller ≠ adminOf e.pre.state P ∧ f.sevm.caller = e.sevm.caller)
    G gfacts.pc ?_ gt gca gcode gadmin gfacts
  intro sevm pre post run committed gt gca gcode gadmin gfacts child len hr
  obtain ⟨c, one, desc, -, -, ccaller, -, -, cstatic, -⟩ :=
    usdc_entry_forward run gcode gfacts.fork gt gfacts.codes gfacts.slots.1 gadmin gfacts.data
  have fc : f = c := by
    rw [one] at child
    exact List.mem_singleton.mp child
  subst fc
  have entry : IsEntry P ⟨0, sevm, pre, .ok post, run, committed⟩ := ⟨gt, gca⟩
  have notObsG : ¬ usdcObs P ⟨0, sevm, pre, .ok post, run, committed⟩ := by
    rintro (h | ⟨-, h⟩)
    · exact proxy_ne_impl (gcode.symm.trans h)
    · exact gadmin h
  cases b₂ with
  | nil =>
      exact ⟨b₁, _, rfl, entry, cstatic.symm.trans nonstatic, notObsG, gadmin, ccaller⟩
  | cons y b₂' =>
      exfalso
      rw [desc, List.cons_append, List.cons_append] at hr
      obtain ⟨-, hr⟩ := List.cons.inj hr
      rw [desc, List.length_cons, List.length_cons] at len
      rcases List.append_eq_append_iff.mp hr with ⟨a', hd, ha'⟩ | ⟨c', hb', -⟩
      · cases a' with
        | nil =>
            rw [List.append_nil] at hd
            rw [hd] at len
            omega
        | cons z a'' =>
            obtain ⟨rfl, -⟩ := List.cons.inj ha'
            exact Exec.Frame.not_mem_own_descendantFrames f
              (by rw [hd]; exact List.mem_append_right _ List.mem_cons_self)
      · rw [hb', List.length_append] at len
        omega

/-- **The observed messages are allowed**, support-free. -/
theorem usdc_allowedF (tr : ConfiguredHistoryTrace cfg checkpoint future) (hist : UsdcHistF P K₀ tr) :
    ∀ G ∈ tr.settledFrames, G.sevm.currentTarget = P → G.sevm.isStatic = false → usdcObs P G →
      usdcAllowed (adminOf checkpoint.state P) G.sevm := by
  intro G hG target nonstatic obs isA₀
  have facts := usdc_settled_factsF tr hist G hG
  rcases obs with code | ⟨code, admin⟩
  · exfalso
    have notEntry : ¬ IsEntry P G := fun h =>
      hist.1.implApart (Option.some.inj (h.2.symm.trans ((facts.kind target).impl_codeAddress code)))
    obtain ⟨b, a, split⟩ := List.append_of_mem hG
    obtain ⟨b', e, hb, -, -, -, eAdmin, caller⟩ :=
      usdc_observer_parentF tr hist b G a split target nonstatic (.inl code) notEntry
    have he : e ∈ tr.settledFrames := by
      rw [split, hb]; exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
    have eAdmin' : adminOf e.pre.state P = adminOf checkpoint.state P :=
      ((usdc_settled_factsF tr hist e he).slots.2.1)
    exact eAdmin (by rw [← caller, eAdmin']; exact isA₀)
  · have ca : G.sevm.codeAddress = some P := by
      rcases facts.kind target with ⟨ca, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
      · exact ca
      · exact (proxy_ne_impl (code.symm.trans h)).elim
      · exact (lib_ne_proxy (h.symm.trans code)).elim
    have notUpgrade := facts.gov ⟨target, ca⟩ isA₀
    revert admin notUpgrade
    refine frame_cases_ok (Q := fun G => G.sevm.code = Proxy.code →
      G.sevm.currentTarget = P → SettledFactsF P (historyKeyUniverse P tr K₀)
        (adminOf checkpoint.state P) G →
      G.sevm.caller = adminOf G.pre.state P →
      Blanc.Sevm.selector G.sevm ∉ [0x3659cfe6, 0x4f1ef286, 0x8f283970] → adminGetter G.sevm)
      G facts.pc ?_ code target facts
    intro sevm pre post run committed code target facts admin notUpgrade
    have admin' : sevm.caller = adminOf pre.state sevm.currentTarget := by rw [target]; exact admin
    rcases proxy_admin_selectors run code facts.fork admin' with getter | upgrade
    · exact getter
    · exact (notUpgrade upgrade).elim

end HistoryF

/-! ## The observer chain and the replay -/

section HistoryF2

variable {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}

/-- The settled frames form an observer chain, support-free. -/
theorem usdc_history_chainF {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) :
    ObserverChain P (usdcObs P) usdcRelated tr.settledFrames :=
  ObserverChain.of_local _ (usdc_entry_observerF tr hist)
    fun b f a split target nonstatic obs notEntry =>
      let ⟨b', e, hb, entry, static, notObs, _⟩ :=
        usdc_observer_parentF tr hist b f a split target nonstatic obs notEntry
      ⟨b', e, hb, entry, static, notObs⟩

open Classical in
/-- Every observed message among frames of the history is allowed, support-free. -/
theorem usdc_observerAsks_allowedF (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) {fs : List Exec.Frame} (sub : ∀ G ∈ fs, G ∈ tr.settledFrames) :
    ∀ e ∈ observerAsks P (usdcObs P) fs, usdcAllowed (adminOf checkpoint.state P) e := by
  intro e he
  unfold observerAsks at he
  obtain ⟨G, hG, rfl⟩ := List.mem_map.mp he
  obtain ⟨hG, h⟩ := List.mem_filter.mp hG
  obtain ⟨target, nonstatic, obs⟩ := of_decide_eq_true h
  exact usdc_allowedF tr hist G (sub G hG) target nonstatic obs

/-- The family ladder's replay to a state, read as the book's run over the entry asks,
support-free: the proof reads only `ext.good`. -/
theorem usdc_replay_entryAsksF (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) {fs : List Exec.Frame} (sub : ∀ G ∈ fs, G ∈ tr.settledFrames)
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
    (usdc_observerAsks_allowedF tr hist sub)
  exact (chain.run_eq (B := (usdcBookS P).toBook) usdcRelated_step _).trans run

/-- **The children of a whole implementation frame are library frames at the proxy**,
support-free: the proof reads only `ext.inj`/`ext.apart` and the good ledger at the frame. -/
theorem usdc_impl_children_libF {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) {A : Exec.Frame}
    (facts : SettledFactsF P (historyKeyUniverse P tr K₀) (adminOf checkpoint.state P) A)
    (code : A.sevm.code = Impl.code) (target : A.sevm.currentTarget = P)
    (nonstatic : A.sevm.isStatic = false)
    (notRescue : Blanc.Sevm.selector A.sevm ≠ rescueSelector)
    (notAdmin : A.sevm.caller ≠ adminOf A.pre.state P) :
    ∀ c ∈ Exec.childFrames A.run,
      c.sevm.currentTarget = P ∧ c.sevm.codeAddress = some usdcLib := by
  have ext := hist.2.2.1.extend hist.2.2.2
  revert code target nonstatic notRescue notAdmin
  refine frame_cases_ok (Q := fun A => SettledFactsF P (historyKeyUniverse P tr K₀)
      (adminOf checkpoint.state P) A → A.sevm.code = Impl.code → A.sevm.currentTarget = P →
    A.sevm.isStatic = false → Blanc.Sevm.selector A.sevm ≠ rescueSelector →
    A.sevm.caller ≠ adminOf A.pre.state P →
    ∀ c ∈ Exec.childFrames A.run,
      c.sevm.currentTarget = P ∧ c.sevm.codeAddress = some usdcLib) A facts.pc ?_ facts
  intro sevm pre post run committed facts code target nonstatic notRescue notAdmin c member
  obtain ⟨-, -, -, nodes⟩ := impl_whole_law ext.inj ext.apart run code target
    ((facts.kind target).impl_codeAddress code) facts.fork nonstatic (facts.keys target)
    (by rw [show pre.state.getCode usdcLib = Lib.code from facts.codes.2.2]; rfl) notAdmin
    facts.slots.2.2 notRescue
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

/-- **No opaque frame covers an unshadowed position**, support-free. -/
theorem usdc_opaque_shadowedF {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) :
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      tr.settledFrames = before ++ f :: after → ¬ UsdcShadowed P tr before f →
      Exec.NoOpaqueAbove (CodeFamily.Opaque P usdcWhole) before f := by
  intro before f after split notShadowed b A m n hb desc ⟨target, nonstatic, whole⟩
  have hAs : A ∈ tr.settledFrames := by
    rw [split, hb]
    exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
  have facts := usdc_settled_factsF tr hist A hAs
  rcases whole with ⟨code, notRescue⟩ | code
  · have ca := (facts.kind target).impl_codeAddress code
    have notEntry : ¬ IsEntry P A := fun h =>
      hist.1.implApart (Option.some.inj (h.2.symm.trans ca))
    obtain ⟨b0, a0, splitA⟩ := List.append_of_mem hAs
    obtain ⟨b', e, hb', -, -, -, eAdmin, caller⟩ :=
      usdc_observer_parentF tr hist b0 A a0 splitA target nonstatic (.inl code) notEntry
    have he : e ∈ tr.settledFrames := by
      rw [splitA, hb']; exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
    have notAdmin : A.sevm.caller ≠ adminOf A.pre.state P := by
      have same : adminOf A.pre.state P = adminOf e.pre.state P :=
        facts.slots.2.1.trans (usdc_settled_factsF tr hist e he).slots.2.1.symm
      rw [caller, same]
      exact eAdmin
    have kids := usdc_impl_children_libF tr hist facts code target nonstatic notRescue notAdmin
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

end HistoryF2

/-! ## The replay, good and end fields -/

section HistoryF3

variable {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}

/-- **`replayAtF`**: the book's run over the entries before an unshadowed position ends in the
ledger at that position's entry. -/
theorem usdc_history_replayAtF {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) :
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      tr.settledFrames = before ++ f :: after → ¬ UsdcShadowed P tr before f →
      (usdcBookS P).toBook.run (ledger (historyKeyUniverse P tr K₀) (checkpoint.state.getStor P))
          (entryAsks P before) =
        some (ledger (historyKeyUniverse P tr K₀) (f.pre.state.getStor P)) := by
  intro before f after split notShadowed
  have ext := hist.2.2.1.extend hist.2.2.2
  obtain ⟨steps, replay, observed⟩ := usdc_configuredHistory_atPos P (adminOf checkpoint.state P)
    ext.inj ext.apart tr (usdc_history_admitted tr hist.1) hist.1.proxy before f after split
    (usdc_opaque_shadowedF tr hist before f after split notShadowed)
  have chain := usdc_history_chainF tr hist
  rw [split] at chain
  have entryAt : f.sevm.currentTarget = P → IsEntry P f := fun target => by
    by_contra notEntry
    exact notShadowed (.inl ⟨target, notEntry⟩)
  exact usdc_replay_entryAsksF tr hist (fun G hG => by rw [split]; exact List.mem_append_left _ hG)
    (chain.prefix entryAt) replay observed

/-- **`replayEndF`**: the book's run over all entries ends in the ledger at the future state. -/
theorem usdc_history_replayEndF {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) :
    (usdcBookS P).toBook.run (ledger (historyKeyUniverse P tr K₀) (checkpoint.state.getStor P))
        (entryAsks P tr.settledFrames) =
      some (ledger (historyKeyUniverse P tr K₀) (future.state.getStor P)) := by
  have ext := hist.2.2.1.extend hist.2.2.2
  obtain ⟨steps, replay, observed⟩ :=
    (usdcLadder P (adminOf checkpoint.state P) ext.inj ext.apart).configuredHistory tr
      (usdc_history_admitted tr hist.1) ⟨hist.1.proxy, trivial, trivial⟩
  exact usdc_replay_entryAsksF tr hist (fun _ h => h) (usdc_history_chainF tr hist) replay observed

/-- **`goodStartF`**: the footprint ledger over the history's universe is good at the
checkpoint. -/
theorem usdc_history_goodStartF {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) :
    (usdcBookS P).toBook.Good (ledger (historyKeyUniverse P tr K₀) (checkpoint.state.getStor P)) :=
  (hist.2.2.1.extend hist.2.2.2).good

/-- **`goodAtF`**: the footprint ledger over the history's universe is good at every settled
frame's entry. -/
theorem usdc_history_goodAtF {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) :
    ∀ f ∈ tr.settledFrames,
      (usdcBookS P).toBook.Good (ledger (historyKeyUniverse P tr K₀) (f.pre.state.getStor P)) :=
  fun f hf => (usdc_settled_factsF tr hist f hf).slots.2.2

/-- **USDC installed at the history's end, the admin word unchanged**, support-free. -/
theorem usdc_history_end_installedF {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) :
    UsdcInstalled P future.state ∧ adminOf future.state P = adminOf checkpoint.state P := by
  obtain ⟨-, slot, admin⟩ := usdc_history_slotsF tr hist
  have inst := hist.1
  exact ⟨⟨history_end_codeImage proxySem P tr inst.proxy,
    history_end_codeImage implSem usdcImpl tr inst.impl,
    history_end_codeImage libSem usdcLib tr inst.lib, slot, inst.implApart, inst.libApart⟩, admin⟩

/-- **USDC at the history's end** (`usdc_history_end_coreF`), support-free: installed, the
admin word unchanged, the history's key universe injective and apart from the fixed slots,
and its ledger good at the end. -/
theorem usdc_history_end_coreF {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) :
    UsdcInstalled P future.state ∧ adminOf future.state P = adminOf checkpoint.state P ∧
      SlotFootprint.Inj Key.slot (historyKeyUniverse P tr K₀) ∧
      SlotFootprint.Apart Key.slot fixedSlots (historyKeyUniverse P tr K₀) ∧
      (ledger (historyKeyUniverse P tr K₀) (future.state.getStor P)).Good := by
  have ext := hist.2.2.1.extend hist.2.2.2
  obtain ⟨inst, admin⟩ := usdc_history_end_installedF tr hist
  exact ⟨inst, admin, ext.inj, ext.apart, (usdc_history_frames_ofF impl_signed_law tr hist).2.2.2⟩

end HistoryF3

end Blanc.Lift.Usdc
