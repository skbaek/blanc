import Blanc.Lift.SettledFramePositions
import Blanc.Lift.Usdc.HistoryFamily
import Blanc.Lift.Usdc.HistoryOwner
import Blanc.ExecutionSettledOwnCode

/-!
# USDC's settled frames: their facts, their parents, the observer pairing (U6h2)

* `usdc_settled_facts`: what a `UsdcHist` history gives at every settled frame (pc `0`, covered
  fork, the three codes, the slot invariant over the history's universe, the code kind at the
  proxy, the frame keys, bounded calldata, F2);
* `usdc_entry_forward`: a non-static admin-free entry frame forwards to exactly one
  implementation frame, which heads its descendants with a related message;
* `usdc_impl_parent`: a non-entry child at the proxy running the implementation was spawned by
  such an entry frame;
* `usdc_entry_observer` and `usdc_observer_parent`: the two local conditions of
  `ObserverChain.of_local` along the settled frames;
* `usdc_allowed`: every observed message is allowed (F2 and `proxy_admin_selectors` for the admin
  word; an implementation frame inherits its entry's non-admin caller).
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay Blanc.Lift.Token

/-! ## Frame facts -/

/-- What the history gives at a settled frame. -/
structure SettledFacts (P : Adr) (U : Key → Prop) (A₀ : Adr) (G : Exec.Frame) : Prop where
  pc : G.pc = 0
  fork : CoveredFork G.sevm.benvStat.fork
  codes : Codes P G.pre
  slots : SlotInv U A₀ (G.pre.state.getStor P)
  kind : G.sevm.currentTarget = P → OwnerKind P G.sevm
  keys : G.sevm.currentTarget = P → ∀ k ∈ frameKeys G.sevm, U k
  data : G.sevm.data.length < 2 ^ 256
  gov : IsEntry P G → G.sevm.caller = A₀ →
    Blanc.Sevm.selector G.sevm ∉ [0x3659cfe6, 0x4f1ef286, 0x8f283970]

/-- The library's frames call out only by `STATICCALL`. -/
theorem lib_ownSpawns : OwnSpawns usdcLib Lib.code := fun pc code _ fork chain hat =>
  .inr (.inl (parentPrefix_exec_staticcall_of_cert Lib.cert_check lib_staticOnly pc code fork chain
    hat))

/-- **The facts at every settled frame** of a `UsdcHist` history. -/
theorem usdc_settled_facts {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) :
    ∀ G ∈ tr.settledFrames,
      SettledFacts P (historyKeyUniverse P tr K₀) (adminOf checkpoint.state P) G := by
  intro G hG
  have installed := hist.1
  have gov := hist.2.1
  have own := tr.settled_ownCode lib_toList_ne_nil (libSem.not_delegation (code := Lib.code) rfl)
    lib_ownSpawns (bytes_eq_of_image installed.lib) G hG
  have q := (usdc_history_frames_of impl_signed_law tr hist).1 G hG
  have raw := tr.settled_mem_rawFrames G hG
  have admitted := (tr.frameAdmitted_iff_rawFrames P _).1
    (usdc_history_admitted (K₀ := K₀) tr installed) _ raw
  refine ⟨own.2.1, own.2.2.1, ⟨bytes_eq_of_image (tr.settled_codeImage proxySem P installed.proxy G hG),
    bytes_eq_of_image (tr.settled_codeImage implSem usdcImpl installed.impl G hG),
    bytes_eq_of_image (tr.settled_codeImage libSem usdcLib installed.lib G hG)⟩, q.1, q.2.2,
    fun target => (admitted target).1, tr.calldata_bound _ raw, gov G hG⟩

/-- A settled frame, as a successful pc-`0` run. -/
theorem frame_cases_ok {Q : Exec.Frame → Prop} (G : Exec.Frame) (pc0 : G.pc = 0)
    (h : ∀ {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
      (committed : Execution.commits (.ok post) = true),
      Q ⟨0, sevm, pre, .ok post, run, committed⟩) : Q G := by
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := G
  dsimp only at pc0
  subst pc0
  cases out with
  | ok post => exact h run committed
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed

theorem usdcImpl_ne_lib : usdcImpl ≠ usdcLib := by decide

/-- An entry frame at the proxy runs the proxy's code. -/
theorem OwnerKind.entry_code {P : Adr} {e : Sevm} (kind : OwnerKind P e) (ca : e.codeAddress = some P)
    (implApart : P ≠ usdcImpl) (libApart : P ≠ usdcLib) : e.code = Proxy.code := by
  rcases kind with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · exact (implApart (Option.some.inj (ca.symm.trans h))).elim
  · exact (libApart (Option.some.inj (ca.symm.trans h))).elim

/-- A frame at the proxy running the implementation's code runs at the implementation's address. -/
theorem OwnerKind.impl_codeAddress {P : Adr} {e : Sevm} (kind : OwnerKind P e)
    (code : e.code = Impl.code) : e.codeAddress = some usdcImpl := by
  rcases kind with ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · exact (proxy_ne_impl (h.symm.trans code)).elim
  · exact h
  · exact (lib_ne_impl (h.symm.trans code)).elim

/-! ## The proxy's forward -/

/-- **A non-static entry frame whose caller is not the admin word forwards once**: its one child is
the implementation frame, heading its descendants, with the entry's caller, value, data and static
flag. -/
theorem usdc_entry_forward {P : Adr} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (codeEq : sevm.code = Proxy.code)
    (fork : CoveredFork sevm.benvStat.fork) (target : sevm.currentTarget = P) (codes : Codes P pre)
    (slot : (pre.state.getStor P).get implSlot = usdcImpl.toB256)
    (notAdmin : sevm.caller ≠ adminOf pre.state P) (dataBound : sevm.data.length < 2 ^ 256) :
    ∃ c, Exec.childFrames run = [c] ∧ Exec.descendantFrames run = c :: Exec.descendantFrames c.run ∧
      c.sevm.currentTarget = P ∧ c.sevm.codeAddress = some usdcImpl ∧ c.sevm.caller = sevm.caller ∧
      c.sevm.value = sevm.value ∧ c.sevm.data = sevm.data ∧ c.sevm.isStatic = sevm.isStatic ∧
      c.sevm.code = Impl.code := by
  subst target
  obtain ⟨-, facts, exists_child⟩ := proxy_forwards run codeEq fork slot notAdmin
    (by rw [show pre.state.getCode usdcImpl = Impl.code from codes.2.1]; exact impl_undelegated)
    (impl_not_precompile fork) dataBound
  rcases Exec.single_child_of_silentAfter run
      (fun N chain x hat N' edge => (proxy_tail run codeEq fork chain hat N' edge).2) with
    none | ⟨c, one, desc⟩
  · obtain ⟨c, member, -⟩ := exists_child post rfl
    rw [none] at member
    exact (List.not_mem_nil member).elim
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := facts c (by rw [one]; exact List.mem_singleton_self c)
    exact ⟨c, one, desc, h1, h2, h3, h4, h5, h6, by rw [h7]; exact codes.2.1⟩

/-! ## The parent of an implementation frame -/

/-- **The parent of a non-static non-entry implementation child at the proxy** is a non-static entry
frame running the proxy, whose caller is not the admin word. -/
theorem usdc_impl_parent {P : Adr} {U : Key → Prop} {A₀ : Adr} {G : Exec.Frame}
    (facts : SettledFacts P U A₀ G)
    {c : Exec.Frame} (member : c ∈ Exec.childFrames G.run) (target : c.sevm.currentTarget = P)
    (notEntry : c.sevm.codeAddress ≠ some P) (nonstatic : c.sevm.isStatic = false)
    (code : c.sevm.code = Impl.code) :
    G.sevm.currentTarget = P ∧ G.sevm.codeAddress = some P ∧ G.sevm.code = Proxy.code ∧
      G.sevm.caller ≠ adminOf G.pre.state P := by
  revert member
  refine frame_cases_ok (Q := fun G => SettledFacts P U A₀ G → c ∈ Exec.childFrames G.run →
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

section History

variable {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}

/-- The proxy's code at a settled entry frame. -/
theorem usdc_entry_code (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) {G : Exec.Frame} (hG : G ∈ tr.settledFrames) (entry : IsEntry P G) :
    G.sevm.code = Proxy.code :=
  ((usdc_settled_facts tr hist G hG).kind entry.1).entry_code entry.2 hist.1.implApart
    hist.1.libApart

/-- **An entry frame not observing is followed by its observer**: a non-static entry frame whose
caller is not the admin word is followed by its implementation frame, carrying a related message. -/
theorem usdc_entry_observer (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) :
    ∀ b f a, tr.settledFrames = b ++ f :: a → IsEntry P f → f.sevm.isStatic = false →
      ¬ usdcObs P f →
      ∃ o a', a = o :: a' ∧ o.sevm.currentTarget = P ∧ o.sevm.isStatic = false ∧ usdcObs P o ∧
        ¬ IsEntry P o ∧ usdcRelated f.sevm o.sevm := by
  intro b f a split entry nonstatic notObs
  have hf : f ∈ tr.settledFrames := by rw [split]; exact List.mem_append_right _ List.mem_cons_self
  have facts := usdc_settled_facts tr hist f hf
  have codeEq := usdc_entry_code tr hist hf entry
  have notAdmin : f.sevm.caller ≠ adminOf f.pre.state P := fun h => notObs (.inr ⟨codeEq, h⟩)
  obtain ⟨r, ha⟩ := tr.settledFrames_contig split
  revert ha
  refine frame_cases_ok (Q := fun f => IsEntry P f → f.sevm.isStatic = false →
    f.sevm.code = Proxy.code → f.sevm.caller ≠ adminOf f.pre.state P → SettledFacts P
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

/-- The preservation of the storage-only proxy specification under the trivial admission. -/
theorem usdcSpec_preserves_trivial (P : Adr) :
    usdcSpec.PreservesAdmitted P (fun _ _ => True) := by
  intro sevm pre post fork run admitted image wf inv
  exact ⟨trivial, trivial⟩

/-- **An observer that is no entry follows its entry frame**: a non-static implementation frame at
the proxy is immediately preceded by the non-static entry frame that forwarded to it, whose caller
is not the admin word and is the implementation frame's. -/
theorem usdc_observer_parent (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) :
    ∀ b f a, tr.settledFrames = b ++ f :: a → f.sevm.currentTarget = P →
      f.sevm.isStatic = false → usdcObs P f → ¬ IsEntry P f →
      ∃ b' e, b = b' ++ [e] ∧ IsEntry P e ∧ e.sevm.isStatic = false ∧ ¬ usdcObs P e ∧
        e.sevm.caller ≠ adminOf e.pre.state P ∧ f.sevm.caller = e.sevm.caller := by
  intro b f a split target nonstatic obs notEntry
  have hf : f ∈ tr.settledFrames := by rw [split]; exact List.mem_append_right _ List.mem_cons_self
  have ffacts := usdc_settled_facts tr hist f hf
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
  have gfacts := usdc_settled_facts tr hist G hG
  obtain ⟨gt, gca, gcode, gadmin⟩ := usdc_impl_parent gfacts child
    target notCA nonstatic code
  obtain ⟨r, hr⟩ := tr.settledFrames_contig split'
  subst hb
  revert child len hr
  refine frame_cases_ok (Q := fun G => G.sevm.currentTarget = P → G.sevm.codeAddress = some P →
    G.sevm.code = Proxy.code → G.sevm.caller ≠ adminOf G.pre.state P → SettledFacts P (historyKeyUniverse P tr K₀)
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

/-- **The observed messages are allowed**: the admin word's observed proxy frames ask getters (F2,
`proxy_admin_selectors`), and an implementation frame's caller is its entry's, never the admin
word. -/
theorem usdc_allowed (tr : ConfiguredHistoryTrace cfg checkpoint future) (hist : UsdcHist P K₀ tr) :
    ∀ G ∈ tr.settledFrames, G.sevm.currentTarget = P → G.sevm.isStatic = false → usdcObs P G →
      usdcAllowed (adminOf checkpoint.state P) G.sevm := by
  intro G hG target nonstatic obs isA₀
  have facts := usdc_settled_facts tr hist G hG
  rcases obs with code | ⟨code, admin⟩
  · exfalso
    have notEntry : ¬ IsEntry P G := fun h =>
      hist.1.implApart (Option.some.inj (h.2.symm.trans ((facts.kind target).impl_codeAddress code)))
    obtain ⟨b, a, split⟩ := List.append_of_mem hG
    obtain ⟨b', e, hb, -, -, -, eAdmin, caller⟩ :=
      usdc_observer_parent tr hist b G a split target nonstatic (.inl code) notEntry
    have he : e ∈ tr.settledFrames := by
      rw [split, hb]; exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
    have eAdmin' : adminOf e.pre.state P = adminOf checkpoint.state P :=
      ((usdc_settled_facts tr hist e he).slots.2.1)
    exact eAdmin (by rw [← caller, eAdmin']; exact isA₀)
  · have ca : G.sevm.codeAddress = some P := by
      rcases facts.kind target with ⟨ca, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
      · exact ca
      · exact (proxy_ne_impl (code.symm.trans h)).elim
      · exact (lib_ne_proxy (h.symm.trans code)).elim
    have notUpgrade := facts.gov ⟨target, ca⟩ isA₀
    revert admin notUpgrade
    refine frame_cases_ok (Q := fun G => G.sevm.code = Proxy.code →
      G.sevm.currentTarget = P → SettledFacts P (historyKeyUniverse P tr K₀)
        (adminOf checkpoint.state P) G →
      G.sevm.caller = adminOf G.pre.state P →
      Blanc.Sevm.selector G.sevm ∉ [0x3659cfe6, 0x4f1ef286, 0x8f283970] → adminGetter G.sevm)
      G facts.pc ?_ code target facts
    intro sevm pre post run committed code target facts admin notUpgrade
    have admin' : sevm.caller = adminOf pre.state sevm.currentTarget := by rw [target]; exact admin
    rcases proxy_admin_selectors run code facts.fork admin' with getter | upgrade
    · exact getter
    · exact (notUpgrade upgrade).elim

end History

end Blanc.Lift.Usdc
