import Blanc.Lift.FrameChain
import Blanc.Lift.WriteSiteRowClass
import Blanc.Lift.WriteSiteMapping
import Blanc.Lift.StaticOnlyFramesIn
import Blanc.ExecutionCellProvenance
import Blanc.ExecutionHistoryCellProvenance
import Blanc.ExecutionInRawNodeOrigin
import Blanc.SlotFootprint
import Blanc.Lift.LinearRuntimeSafety

/-!
# Locality of one holder's balance entry over a mid history

`EntryLocal`: a token's storage moves through its settled frames (`FrameChain`), and each such frame
satisfies `held pre + credit ≤ held post + debit`, where `debit` and `credit` read the frame's message.
With `ownDebit` and `ownCredit` that says a third party's frame never lowers the holder's entry and the
holder's own frame lowers it by at most the amount it names. A rolled-back frame is not settled, so nothing
here ranges over one.

The kit for a certified code:

* `Exec.staticOnly_rawFrameDescendants_isStatic`, `staticOnly_quiet`: below code that executes only
  `STATICCALL`, every entered frame is static, on any lane without state gas;
* `frame_cellInv`: a cell property every write in a committed frame's raw nodes keeps holds at its post;
* `frame_rows_zero`: a holder's tracked rows stay zero across a frame the row table does not name
  (`rawWrite_rowClass`);
* `frame_cell_keep`: a frame under a selector with no mapping site keeps an entry apart from its known sites;
* `CoinKey`, `CoinKeysFresh`: the trace-local hash premise, over the words a coin's settled frames name;
* `rowSep_of_keys`, `slot_ne_of_keys`: the separation facts it gives;
* `PoolAuthorityEmpty`: the holder's allowance is empty at the cut and nothing can fill it;
* `entryLocal_of_frames`: the assembly from a chain and a per-frame law.

Contract-neutral: no address, base or selector of a coin is fixed here but the ERC-20 ABI's in
`ownDebit`/`ownCredit`.
-/

namespace Blanc.Lift

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift.WriteSite

/-! ## Static-only code, on a lane without state gas -/

/-- Every frame a static execution enters is static. -/
theorem Exec.rawFrameRoots_isStatic {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hstatic : sevm.isStatic = true) :
    ∀ root ∈ Exec.rawFrameRoots run, root.sevm.isStatic = true := by
  induction run with
  | halt hstep =>
    intro root member
    simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons, List.not_mem_nil,
      or_false] at member
    subst member
    exact hstatic
  | cont hstep next ih =>
    intro root member
    simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
    rcases member with rfl | member
    · exact hstatic
    · exact ih hstatic root (List.mem_cons_of_mem _ member)
  | doneErr hstep henter hresume =>
    intro root member
    simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons, List.not_mem_nil,
      or_false] at member
    subst member
    exact hstatic
  | doneOk hstep henter hresume next ih =>
    intro root member
    simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
    rcases member with rfl | member
    · exact hstatic
    · exact ih hstatic root (List.mem_cons_of_mem _ member)
  | runErr hstep henter child hresume ih =>
    have hroots := ih (Evm.step_run_isStatic hstep henter hstatic)
    intro root member
    simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
    rcases member with rfl | rfl | member
    · exact hstatic
    · exact hroots _ List.mem_cons_self
    · exact hroots root (List.mem_cons_of_mem _ member)
  | runOk hstep henter child hresume next ihChild ihNext =>
    have hroots := ihChild (Evm.step_run_isStatic hstep henter hstatic)
    have hnext := ihNext hstatic
    intro root member
    simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons, List.mem_append] at member
    rcases member with rfl | rfl | member | member
    · exact hstatic
    · exact hroots _ List.mem_cons_self
    · exact hroots root (List.mem_cons_of_mem _ member)
    · exact hnext root (List.mem_cons_of_mem _ member)

/-- **Below a frame of certified code that executes only `STATICCALL`, every entered frame is
static**, without state gas (the `noStateGas` twin of `Exec.staticOnly_rawFrameDescendants`, minus
its code-address clause). -/
theorem Exec.staticOnly_rawFrameDescendants_isStatic {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true)
    (only : ∀ f ∈ c.prog, f.execsSatisfy Xinst.isStaticcall = true)
    {root : Exec.Deriv} (pc0 : root.pc = 0) (installed : root.sevm.code = code)
    (hsg : root.sevm.benvStat.rules.stateGas = none) :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      Exec.Deriv.ParentPrefix root ⟨pc, sevm, pre, out, run⟩ →
      ∀ D ∈ Exec.rawFrameDescendants run, D.sevm.isStatic = true := by
  intro pc sevm pre out run
  induction run with
  | halt step => simp only [Exec.rawFrameDescendants, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true]
  | cont step next ih =>
    intro chain
    simpa only [Exec.rawFrameDescendants] using ih (chain.snoc (.cont step next))
  | doneErr step enter resume => simp only [Exec.rawFrameDescendants, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true]
  | doneOk step enter resume next ih =>
    intro chain
    simpa only [Exec.rawFrameDescendants] using ih (chain.snoc (.doneOk step enter resume next))
  | runErr step enter child resume ih =>
    intro chain D member
    obtain ⟨x, instruction, spawn, _⟩ := Evm.step_spawn_inv step
    have onlyStatic : x = .staticcall :=
      parentPrefix_exec_staticcall_of_cert_noStateGas checked only pc0 installed hsg chain instruction
    subst x
    have stc := (Frame.enter_run_isStatic enter).trans (Xinst.step_staticcall_spawn_isStatic spawn)
    exact Exec.rawFrameRoots_isStatic child stc D (by
      simpa only [Exec.rawFrameRoots, Exec.rawFrameDescendants] using member)
  | runOk step enter child resume next childIH nextIH =>
    intro chain D member
    obtain ⟨x, instruction, spawn, _⟩ := Evm.step_spawn_inv step
    have onlyStatic : x = .staticcall :=
      parentPrefix_exec_staticcall_of_cert_noStateGas checked only pc0 installed hsg chain instruction
    subst x
    have stc := (Frame.enter_run_isStatic enter).trans (Xinst.step_staticcall_spawn_isStatic spawn)
    simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append] at member
    rcases member with rfl | member | member
    · exact stc
    · exact Exec.rawFrameRoots_isStatic child stc D (List.mem_cons_of_mem _ member)
    · exact nextIH (chain.snoc (.runOk step enter child resume next)) D member

/-- **An allowed frame of static-only code has no observed committed descendant.** -/
theorem staticOnly_quiet {code : ByteArray} {c : Cert} (checked : Cert.check code c = true)
    (only : ∀ f ∈ c.prog, f.execsSatisfy Xinst.isStaticcall = true) (T : Adr) (Obs : Exec.Frame → Prop)
    {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (hcode : sevm.code = code) (hsg : sevm.benvStat.rules.stateGas = none) :
    (Exec.descendantFrames run).flatMap (coinObs T Obs) = [] := by
  have raw := Exec.staticOnly_rawFrameDescendants_isStatic checked only
    (root := ⟨0, sevm, pre, out, run⟩) rfl hcode hsg run (.refl _)
  refine List.flatMap_eq_nil_iff.mpr fun D member => ite_eq_right fun obs => ?_
  have hs := raw _ (Blanc.Exec.mem_rawFrameDescendants_of_mem_descendantFrames run D member)
  change D.sevm.isStatic = true at hs
  rw [obs.2.1] at hs
  cases hs

/-- A successful store in a frame whose descendants are all static is on the frame's own chain. -/
theorem write_onChain {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (static : ∀ D ∈ Exec.rawFrameDescendants run, D.sevm.isStatic = true)
    {m : Exec.Deriv} (member : m ∈ Exec.rawNodes run) {w : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? m = some w) :
    Exec.Deriv.ParentPrefix ⟨pc, sevm, pre, out, run⟩ m := by
  obtain ⟨r, hr, same⟩ := (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix run m).mp member
  simp only [Exec.rawFrameRoots, List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact same
  · exfalso
    have hstatic := static r hr
    obtain ⟨write, hw⟩ := Exec.Deriv.successfulSstore?_sound_raw
      (G := ⟨pc, sevm, pre, out, run⟩) member found
    have hnode : write.occurrence.node = m :=
      (congrArg Exec.StorageWrite.node hw).trans (successfulSstore?_node_owner found).1
    have hs := Exec.Deriv.ParentPrefix.sevm_eq same
    have storeRun : Ninst.Run write.occurrence.node.sevm write.occurrence.node.devm (.reg .sstore)
        write.stepPost := by
      refine ⟨write.occurrence.slot, write.occurrence.filled, write.occurrence.node.pc, ?_⟩
      simpa only [write.instruction_eq, write.stepSuccess] using write.occurrence.stepRun
    have nonstatic := of_run_sstore_not_static storeRun
    rw [hnode, hs, hstatic] at nonstatic
    exact Bool.noConfusion nonstatic

/-- `InstalledRuntimeSafety.of_linearCheck` with the code's emptiness and delegation read off its size. -/
theorem runtimeSafety_of_sizes {C : ByteArray} (kinds : callKindsCheck C = true)
    (terminal : selfdestructFreeCheck C = true) (ne : C.size ≠ 0)
    (notDelegated : C.size ≠ eoaDelegatedCodeLength) : InstalledRuntimeSafety C :=
  InstalledRuntimeSafety.of_linearCheck kinds terminal (fun h => notDelegated h.1)
    (fun h => ne (by
      show C.data.size = 0
      rw [← Array.length_toList, ← ByteArray.toList_eq_toList_data, h, List.length_nil]))

/-! ## A cell across a committed frame -/

/-- **A cell property every write of a committed frame keeps holds at the frame's post.** -/
theorem frame_cellInv (F : Exec.Frame) (hsg : F.sevm.benvStat.rules.stateGas = none) {T : Adr}
    (hne : (F.pre.getCode T).toList ≠ []) (k : B256) {Inv : B256 → Prop}
    (init : Inv ((F.pre.getStor T).get k))
    (step : ∀ m ∈ Exec.rawNodes F.run, ∀ w : Exec.StorageWrite,
      Exec.Deriv.successfulSstore? m = some w → w.owner = T → w.key = k →
      Inv ((m.devm.getStor T).get k) → Inv w.value) :
    Inv ((F.post.getStor T).get k) := by
  have nodes : ∀ n ∈ Exec.rawNodes F.run, Inv ((n.devm.getStor T).get k) := by
    refine List.forall_mem_of_positional fun before n after split ih => ?_
    rcases Exec.rawNodes_cellProv_noStateGas F.run k hsg rfl hne split with
      same | ⟨b₁, b₂, m, w, hb, found, owner, key, value⟩
    · rw [same]
      exact init
    · have inBefore : m ∈ before := by
        rw [hb]
        exact List.mem_append_right _ List.mem_cons_self
      rw [← value]
      exact step m (by rw [split]; exact List.mem_append_left _ inBefore) w found owner key
        (ih m inBefore)
  have hcell : (F.post.getStor T).get k = Exec.StorageWrite.replayCell T k
      ((F.pre.getStor T).get k) (Exec.retainedStorageWrites F.run) :=
    (Exec.storageReplay_committedPost_noStateGas F.run F.committed hsg).2 T hne k
  have prov : CellProv T k ((F.pre.getStor T).get k) (Exec.rawNodes F.run)
      ((F.post.getStor T).get k) :=
    CellProv.of_replayCell hcell.symm fun w hw => by
      simp only [Exec.retainedStorageWrites, List.mem_filterMap] at hw
      obtain ⟨mm, hmem, hss⟩ := hw
      exact ⟨mm, (Exec.retainedNodes_sublist_rawNodes F.run).subset hmem, hss⟩
  rcases prov with same | ⟨b₁, b₂, m, w, hb, found, owner, key, value⟩
  · rw [same]
    exact init
  · have inNodes : m ∈ Exec.rawNodes F.run := by
      rw [hb]
      exact List.mem_append_right _ List.mem_cons_self
    rw [← value]
    exact step m inNodes w found owner key (nodes m inNodes)

/-! ## A certified frame's writes -/

/-- The facts of a committed frame of certified code: entered at pc `0`, without state gas, its
writes on its own chain, at `T`, with code at `T`. -/
structure CertFrame (F : Exec.Frame) (code : ByteArray) (T : Adr) : Prop where
  pc : F.pc = 0
  code : F.sevm.code = code
  stateGas : F.sevm.benvStat.rules.stateGas = none
  target : F.sevm.currentTarget = T
  hasCode : (F.pre.getCode T).toList ≠ []
  /-- Its descendants, committed or not, are static. -/
  static : ∀ D ∈ Exec.rawFrameDescendants F.run, D.sevm.isStatic = true

/-- A node's frame environment is its root's: the chain of a `CertFrame`. -/
theorem CertFrame.chain {F : Exec.Frame} {code : ByteArray} {T : Adr} (h : CertFrame F code T)
    {m : Exec.Deriv} (member : m ∈ Exec.rawNodes F.run) {w : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? m = some w) :
    Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv F) m :=
  write_onChain F.run h.static member found

/-- **A holder's tracked rows stay zero across a frame the row table does not name.** -/
theorem frame_rows_zero {F : Exec.Frame} {code : ByteArray} {T : Adr} (h : CertFrame F code T)
    {c : Cert} {ann : List WAnn} {t : SelTable} {b : B256} {pair : Adr} {Tr : Adr → Prop}
    (hc : Cert.check code c = true) (hw : wsCert c ann = true)
    (hsel : t.selT.known = true) (hok : (wsRoot ann).all (rowSiteOk b t) = true)
    (sep : RowSep b pair.toB256 (AllowKey Tr) (wsRoot ann) (Env.root F.sevm))
    (quiet : ¬ AllowedFrame t pair (Env.root F.sevm))
    (zero : ∀ g, Tr g → (F.pre.getStor T).get (rowSlot b pair.toB256 g.toB256) = 0) :
    ∀ g, Tr g → (F.post.getStor T).get (rowSlot b pair.toB256 g.toB256) = 0 := by
  intro g hg
  refine frame_cellInv F h.stateGas h.hasCode _ (Inv := fun v => v = 0) (zero g hg) ?_
  intro m member w found owner key cur
  have chain := h.chain member found
  have target : m.sevm.currentTarget = T := by
    rw [Exec.Deriv.ParentPrefix.sevm_eq chain]
    exact h.target
  rcases rawWrite_rowClass (b := b) (G := Blanc.Exec.Frame.rootDeriv F) h.pc h.stateGas chain hc hw h.code
      hsel hok sep found ⟨g, hg, key.symm⟩ with allowed | le
  · exact absurd allowed quiet
  · change w.value.toNat ≤ ((m.devm.getStor m.sevm.currentTarget).get w.key).toNat at le
    rw [target, key, cur] at le
    exact B256.eq_zero_of_toNat (Nat.le_zero.mp le)

/-- A good frame of static-only code is a `CertFrame`. -/
theorem CertFrame.of_staticOnly {F : Fork → Prop} {code : ByteArray} {c : Cert} {T : Adr}
    (checked : Cert.check code c = true)
    (only : ∀ f ∈ c.prog, f.execsSatisfy Xinst.isStaticcall = true)
    (hsgF : ∀ {f : Fork}, F f → (Fork.ruleSet f).stateGas = none) {G : Exec.Frame}
    (good : CodeFrame T F code G) (target : G.sevm.currentTarget = T) : CertFrame G code T := by
  obtain ⟨pc, hcode, fork, hasCode⟩ := good
  have hsg : G.sevm.benvStat.rules.stateGas = none := hsgF fork
  obtain ⟨gpc, sevm, pre, out, run, committed⟩ := G
  dsimp only at pc hcode hsg target hasCode
  subst pc
  exact ⟨rfl, hcode, hsg, target, hasCode, Exec.staticOnly_rawFrameDescendants_isStatic checked only
    (root := ⟨0, sevm, pre, out, run⟩) rfl hcode hsg run (.refl _)⟩

/-- **A frame under a selector with no mapping site keeps an entry apart from its known sites.**
`R` lists the selectors of the mapping's sites at base `b` (`hrows`, decided per code); `sep` says the
frame's other known sites miss the cell. -/
theorem frame_cell_keep {F : Exec.Frame} {code : ByteArray} {T : Adr} (h : CertFrame F code T)
    {c : Cert} {ann : List WAnn} {selT : Term} {R : List B256} {b k : B256}
    (hc : Cert.check code c = true) (hw : wsCert c ann = true) (hsel : selT.known = true)
    (hrows : (mappingSites b (wsRoot ann)).all (hasSel selT R) = true)
    (notRow : selT.eval (Env.root F.sevm) ∉ R)
    (sep : ∀ s ∈ wsRoot ann, s.GuardsHold (Env.root F.sevm) → s.slot.known = true →
      mappingKey? b s.slot = none → s.slot.eval (Env.root F.sevm) ≠ k) :
    (F.post.getStor T).get k = (F.pre.getStor T).get k := by
  refine frame_cellInv F h.stateGas h.hasCode k (Inv := fun v => v = (F.pre.getStor T).get k) rfl ?_
  intro m member w found _ key _
  obtain ⟨site, inRoot, guards, -, cases⟩ := successfulSstore_mappingSite b hc hw h.pc h.code h.stateGas
    (h.chain member found) found
  rcases cases with ⟨inMap, -⟩ | ⟨known, none, keyEq⟩
  · exact absurd (hasSel_sound (List.all_eq_true.mp hrows site inMap) hsel guards) notRow
  · exact absurd (keyEq.symm.trans key) (sep site inRoot guards known none)

/-! ## The hash premise -/

/-- A slot a coin's frame names, by its shape. -/
inductive CoinKey : Type
  /-- `keccak256(a ‖ b)`. -/
  | map (b a : B256)
  /-- `keccak256(k ‖ keccak256(o ‖ b))`. -/
  | row (b o k : B256)
  /-- Any other known word. -/
  | raw (x : B256)
  deriving DecidableEq

/-- The storage slot of a key. -/
def CoinKey.slot : CoinKey → B256
  | .map b a => mapSlot a b
  | .row b o k => rowSlot b o k
  | .raw x => x

/-- The key a known term names in `ε`. -/
def termKey (ε : Env) : Term → CoinKey
  | .kecc k (.kecc o (.const b)) => .row b (o.eval ε) (k.eval ε)
  | .kecc k (.const b) => .map b (k.eval ε)
  | t => .raw (t.eval ε)

theorem termKey_slot (ε : Env) (t : Term) : (termKey ε t).slot = t.eval ε := by
  unfold termKey
  split <;> rfl

open Classical in
/-- The keys of a frame's known sites whose guards hold. -/
noncomputable def frameSiteKeys (sites : List Site) (ε : Env) : List CoinKey :=
  sites.filterMap fun s =>
    if s.GuardsHold ε ∧ s.slot.known = true then some (termKey ε s.slot) else none

theorem mem_frameSiteKeys {sites : List Site} {ε : Env} {s : Site} (hs : s ∈ sites)
    (hg : s.GuardsHold ε) (hk : s.slot.known = true) : termKey ε s.slot ∈ frameSiteKeys sites ε := by
  unfold frameSiteKeys
  refine List.mem_filterMap.mpr ⟨s, hs, ?_⟩
  rw [ite_eq_left ⟨hg, hk⟩]

theorem termKey_of_rowOf {ε : Env} {t o k : Term} {b : B256} (h : rowOf b t = some (o, k)) :
    termKey ε t = .row b (o.eval ε) (k.eval ε) := by
  unfold rowOf at h
  split at h
  · split at h
    · rename_i hc
      cases h
      subst hc
      rfl
    · cases h
  · cases h

theorem rowOf_of_termKey {ε : Env} {t : Term} {b o k : B256} (h : termKey ε t = .row b o k) :
    rowOf b t ≠ none := by
  unfold termKey at h
  split at h
  · cases h
    simp only [rowOf, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]
  · cases h
  · cases h

theorem mappingKey_of_termKey {ε : Env} {t : Term} {b a : B256} (h : termKey ε t = .map b a) :
    mappingKey? b t ≠ none := by
  unfold termKey at h
  split at h
  · cases h
  · cases h
    simp only [mappingKey?, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]
  · cases h

/-- The holder's keys: its entry, and its rows for the frames' callers. -/
def heldKeys (balBase allowBase : B256) (h : Adr) (frames : List Exec.Frame) : List CoinKey :=
  .map balBase h.toB256 :: frames.map fun F => .row allowBase h.toB256 F.sevm.caller.toB256

/-- **Hash freshness at a coin**: among the holder's keys and the keys the frames' guarded known sites
name, two with one slot are one key. It speaks only of words these frames compute. No injectivity is
assumed over all words. -/
def CoinKeysFresh (sites : List Site) (balBase allowBase : B256) (h : Adr)
    (frames : List Exec.Frame) : Prop :=
  SlotFootprint.FreshKeys CoinKey.slot [] (fun _ => False)
    (heldKeys balBase allowBase h frames ++
      frames.flatMap fun F => frameSiteKeys sites (Env.root F.sevm))

variable {sites : List Site} {balBase allowBase : B256} {h : Adr} {frames : List Exec.Frame}

/-- The holder's entry key, in the list. -/
theorem CoinKeysFresh.held_mem : CoinKey.map balBase h.toB256 ∈ (heldKeys balBase allowBase h frames ++
      frames.flatMap fun F => frameSiteKeys sites (Env.root F.sevm)) :=
  List.mem_append_left _ List.mem_cons_self

/-- A frame's caller's row of the holder, in the list. -/
theorem CoinKeysFresh.row_mem {F : Exec.Frame} (hF : F ∈ frames) :
    CoinKey.row allowBase h.toB256 F.sevm.caller.toB256 ∈ (heldKeys balBase allowBase h frames ++
      frames.flatMap fun F => frameSiteKeys sites (Env.root F.sevm)) :=
  List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨F, hF, rfl⟩))

/-- A frame's site key, in the list. -/
theorem CoinKeysFresh.site_mem {F : Exec.Frame} (hF : F ∈ frames) {s : Site} (hs : s ∈ sites)
    (hg : s.GuardsHold (Env.root F.sevm)) (hk : s.slot.known = true) :
    termKey (Env.root F.sevm) s.slot ∈ (heldKeys balBase allowBase h frames ++
      frames.flatMap fun F => frameSiteKeys sites (Env.root F.sevm)) :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨F, hF, mem_frameSiteKeys hs hg hk⟩)

/-- The callers of the frames, as tracked spenders. -/
def CallerOf (frames : List Exec.Frame) (g : Adr) : Prop := ∃ F ∈ frames, F.sevm.caller = g

/-- **`RowSep` from the hash premise**, at a frame of the list. -/
theorem rowSep_of_keys (keys : CoinKeysFresh sites balBase allowBase h frames)
    {F : Exec.Frame} (hF : F ∈ frames) :
    RowSep allowBase h.toB256 (AllowKey (CallerOf frames)) sites (Env.root F.sevm) where
  inj := by
    rintro _ _ ⟨g, ⟨G, hG, rfl⟩, rfl⟩ ⟨g', ⟨G', hG', rfl⟩, rfl⟩ eq
    have := keys.2 _ (CoinKeysFresh.row_mem hG) _ (CoinKeysFresh.row_mem hG') eq
    injection this
  row := by
    rintro s hs - hg hk o k hr _ ⟨g, ⟨G, hG, rfl⟩, rfl⟩ eq
    have site := CoinKeysFresh.site_mem (balBase := balBase) (allowBase := allowBase) (h := h) hF hs hg hk
    have same := keys.2 _ site _ (CoinKeysFresh.row_mem hG) (by
      rw [termKey_slot, rowOf_eval hr]
      exact eq)
    rw [termKey_of_rowOf hr] at same
    injection same with _ ho hk'
    exact ⟨ho, hk'⟩
  other := by
    rintro s hs - hg hk hr _ ⟨g, ⟨G, hG, rfl⟩, rfl⟩ eq
    have site := CoinKeysFresh.site_mem (balBase := balBase) (allowBase := allowBase) (h := h) hF hs hg hk
    have same := keys.2 _ site _ (CoinKeysFresh.row_mem hG) (by
      rw [termKey_slot]
      exact eq)
    exact rowOf_of_termKey same hr

/-- **The entry is apart from a frame's known site of another shape.** -/
theorem slot_ne_of_keys (keys : CoinKeysFresh sites balBase allowBase h frames)
    {F : Exec.Frame} (hF : F ∈ frames) {s : Site} (hs : s ∈ sites)
    (hg : s.GuardsHold (Env.root F.sevm)) (hk : s.slot.known = true)
    (none : mappingKey? balBase s.slot = none) :
    s.slot.eval (Env.root F.sevm) ≠ mapSlot h.toB256 balBase := by
  intro eq
  have site := CoinKeysFresh.site_mem (balBase := balBase) (allowBase := allowBase) (h := h) hF hs hg hk
  have same := keys.2 _ site _ (CoinKeysFresh.held_mem (sites := sites) (frames := frames)
    (balBase := balBase) (allowBase := allowBase) (h := h)) (by
      rw [termKey_slot]
      exact eq)
  exact mappingKey_of_termKey same none

/-! ## Locality -/

/-- What the holder's own message says it takes out of its entry. -/
def ownDebit (h : Adr) (e : Sevm) : Nat :=
  if e.caller ≠ h then 0
  else if Blanc.Sevm.selector e = 0xa9059cbb ∧ (Sevm.dataWord e 4).toAdr ≠ h then
    (Sevm.dataWord e 36).toNat
  else if Blanc.Sevm.selector e = 0x23b872dd ∧ (Sevm.dataWord e 4).toAdr = h ∧
      (Sevm.dataWord e 36).toAdr ≠ h then
    (Sevm.dataWord e 68).toNat
  else 0

/-- What the holder's own message says it pulls into its entry. -/
def ownCredit (h : Adr) (e : Sevm) : Nat :=
  if e.caller = h ∧ Blanc.Sevm.selector e = 0x23b872dd ∧ (Sevm.dataWord e 4).toAdr ≠ h ∧
      (Sevm.dataWord e 36).toAdr = h then
    (Sevm.dataWord e 68).toNat
  else 0

/-- **The holder's allowance is empty and stays so**, over the coin's settled frames `frames` from
the words `a`. `rowsAtCut` is a listed state fact: before the holder's code exists, a nonzero row could
come only from `approve` with the holder as caller or from `permit`, and each needs a signature
recovering to the holder's address, so it is grouped with `noSignature` as signature recovery; it can't be
derived without history from the coin's deployment. `noSignature` reads the frame's calldata through
`signedAs`, the coin's one named definition of a message that claims the holder's signature. `ownCalls`
is what the holder sends the coin. -/
structure PoolAuthorityEmpty (signedAs : Adr → Sevm → Prop) (allowSlotOf : Adr → Adr → B256)
    (OwnSel : B256 → Prop) (h : Adr) (a : StorWords) (frames : List Exec.Frame) : Prop where
  rowsAtCut : ∀ g, a (allowSlotOf h g) = 0
  noSignature : ∀ F ∈ frames, ¬ signedAs h F.sevm
  ownCalls : ∀ F ∈ frames, F.sevm.caller = h → OwnSel (Blanc.Sevm.selector F.sevm)

/-- **Locality of `held` at coin `T`** over the settled frames `settled`, from words `a` to `b`. -/
structure EntryLocal (T : Adr) (Obs Good : Exec.Frame → Prop) (held : StorWords → Nat)
    (debit credit : Sevm → Nat) (a b : StorWords) (settled : List Exec.Frame) : Prop where
  /-- The coin's storage moves exactly through these frames, to the end. -/
  chain : FrameChain T Good a (coinFrames T Obs settled) b
  /-- The same, to the entry of any settled frame no earlier non-static `T` frame encloses. -/
  at_ : ∀ {before : List Exec.Frame} {f : Exec.Frame} {after : List Exec.Frame},
    settled = before ++ f :: after →
    Exec.NoOpaqueAbove (fun A => A.sevm.currentTarget = T ∧ A.sevm.isStatic = false) before f →
    FrameChain T Good a (coinFrames T Obs before) (wordsAt T f.pre.state)
  /-- Each frame's effect on the entry, attributed by its message. -/
  law : ∀ F ∈ coinFrames T Obs settled,
    held (wordsAt T F.pre.state) + credit F.sevm ≤ held (wordsAt T F.post.state) + debit F.sevm

namespace EntryLocal

variable {T : Adr} {Obs Good : Exec.Frame → Prop} {held : StorWords → Nat} {a b : StorWords}
  {settled : List Exec.Frame}

/-- A third party's frame does not lower the entry. -/
theorem third_party (L : EntryLocal T Obs Good held (ownDebit h) (ownCredit h) a b settled)
    {F : Exec.Frame} (hF : F ∈ coinFrames T Obs settled) (caller : F.sevm.caller ≠ h) :
    held (wordsAt T F.pre.state) ≤ held (wordsAt T F.post.state) := by
  have := L.law F hF
  have hd : ownDebit h F.sevm = 0 := ite_eq_left caller
  rw [hd] at this
  omega

/-- A frame that lowers the entry is the holder's own `transfer` or `transferFrom` from itself, and
lowers it by at most the amount it names. -/
theorem lowered (L : EntryLocal T Obs Good held (ownDebit h) (ownCredit h) a b settled)
    {F : Exec.Frame} (hF : F ∈ coinFrames T Obs settled)
    (lower : held (wordsAt T F.post.state) < held (wordsAt T F.pre.state)) :
    F.sevm.caller = h ∧ (Blanc.Sevm.selector F.sevm = 0xa9059cbb ∨
        Blanc.Sevm.selector F.sevm = 0x23b872dd ∧ (Sevm.dataWord F.sevm 4).toAdr = h) ∧
      held (wordsAt T F.pre.state) ≤ held (wordsAt T F.post.state) + ownDebit h F.sevm := by
  have law := L.law F hF
  have zero : ownDebit h F.sevm ≠ 0 := fun z => by rw [z] at law; omega
  refine ⟨?_, ?_, by omega⟩
  · by_contra caller
    exact zero (ite_eq_left caller)
  · unfold ownDebit at zero
    split at zero
    · exact absurd rfl zero
    · split at zero
      · rename_i hs
        exact .inl hs.1
      · split at zero
        · rename_i hs
          exact .inr ⟨hs.1, hs.2.1⟩
        · exact absurd rfl zero

/-- Over the whole chain, the entry moves by the frames' amounts. -/
theorem total (L : EntryLocal T Obs Good held debit credit a b settled) :
    held a + ((coinFrames T Obs settled).map fun F => credit F.sevm).sum ≤
      held b + ((coinFrames T Obs settled).map fun F => debit F.sevm).sum :=
  (FrameChain.fold (I := fun _ => True) L.chain
    (fun F hF _ _ => ⟨trivial, L.law F hF⟩) trivial).2

end EntryLocal

/-- **Assembly**: a `SettledChain` of allowed frames and a per-frame law preserving `I` give
`EntryLocal`, with `I` at every frame's entry available to the law. -/
theorem entryLocal_of_frames {T : Adr} {Obs Good : Exec.Frame → Prop} {Allowed : Exec.Frame → Prop}
    {held : StorWords → Nat} {debit credit : Sevm → Nat} {I : StorWords → Prop} {a b : StorWords}
    {settled : List Exec.Frame} (chain : SettledChain T Obs Good Allowed a b settled)
    (allowed : ∀ F ∈ coinFrames T Obs settled, Allowed F) (start : I a)
    (law : ∀ F ∈ coinFrames T Obs settled, Good F → I (wordsAt T F.pre.state) →
      I (wordsAt T F.post.state) ∧
        held (wordsAt T F.pre.state) + credit F.sevm ≤ held (wordsAt T F.post.state) + debit F.sevm) :
    EntryLocal T Obs Good held debit credit a b settled := by
  have whole := chain.1 allowed
  refine ⟨whole, ?_, ?_⟩
  · intro before f after split noOpaque
    refine chain.2 split noOpaque fun F hF => allowed F ?_
    rw [split, coinFrames_append]
    exact List.mem_append_left _ hF
  · intro F hF
    have inv := whole.inv_all (I := I) (fun G hG good h => (law G hG good h).1) start F hF
    exact (law F hF (whole.good F hF) inv).2

end Blanc.Lift
