import Blanc.Lift.ReachKinds
import Blanc.Lift.Usdc.EntryChainProof
import Blanc.Lift.CurveCoins.KeepUsdc
import Blanc.Lift.Usdc.ImplSpawns
import Blanc.Lift.Usdc.LibSpawns

/-!
# The census of `CALL`, per version

Each of the three implementation versions decodes `CALL` only under the `rescueERC20` selector: the trees
outside its path form a closed `CALL`-free region, and the dispatcher reaches that path only on its selector.
So an entry frame on another selector has no observed committed descendant (`entryQuiet`).
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift

/-- `FiatTokenV2_2` off its rescue path delegates only. -/
def onlyDelegate (x : Xinst) : Bool := x == .delegatecall

/-- The dispatcher's comparison that hits `rescueERC20` names its selector. -/
theorem rescue_of_hit {sevm : Sevm} {c : B256} (hc : c = rescueSelector)
    (hit : B256.eqCheck c (Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [224]).toNat) ≠ 0) :
    Blanc.Sevm.selector sevm = rescueSelector := by
  rw [← shr_selector_word, ← hc]
  exact (B256.eq_of_eqCheck_ne_zero hit).symm

/-- The dispatcher's walk to the rescue row: every other arm stands in the `CALL`-free region. -/
macro "censusWalk " h:ident t:ident hx:ident sel:ident hE:term : tactic => `(tactic|
  (repeat (first | rstepN $h $t | rbranchK $h $t $hx $hE)
   exact (($sel (rescue_of_hit (c := Bytes.toB256 [178, 17, 138, 141]) (by decide) (by assumption))).elim)))

/-- The trees of `FiatTokenV2_2` off the rescue path. -/
def v22NoCall : List Nat := (List.range 180).filter (· ∉ [0, 34, 91, 114, 118, 121, 142])

theorem v22NoCall_set : ExecsSet onlyDelegate Impl.cert.prog v22NoCall = true := by decide +kernel

/-- **`FiatTokenV2_2` decodes `CALL` only on `rescueERC20`.** -/
theorem v22_noCall {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (hcode : sevm.code = Impl.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (sel : Blanc.Sevm.selector sevm ≠ rescueSelector) :
    ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → onlyDelegate x = true :=
  execs_of_reach Impl.cert_check rfl rfl run hcode hsg fun T h t x g hx => by
    change Reach _ _ _ ⟨_, Impl.t_0000_c0, []⟩ T at h
    censusWalk h t hx sel v22NoCall_set

/-- The trees of `FiatTokenV2` off the rescue path. -/
def v2NoCall : List Nat := (List.range 151).filter (· ∉ [0, 26, 73, 87, 92, 95, 114])

theorem v2NoCall_set : ExecsSet Xinst.isStaticcall ImplV2.cert.prog v2NoCall = true := by decide +kernel

/-- **`FiatTokenV2` decodes `CALL` only on `rescueERC20`.** -/
theorem v2_noCall {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (hcode : sevm.code = ImplV2.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (sel : Blanc.Sevm.selector sevm ≠ rescueSelector) :
    ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → Xinst.isStaticcall x = true :=
  execs_of_reach ImplV2.cert_check rfl rfl run hcode hsg fun T h t x g hx => by
    change Reach _ _ _ ⟨_, ImplV2.t_0000_c0, []⟩ T at h
    censusWalk h t hx sel v2NoCall_set

/-- The trees of `FiatTokenV2_1` off the rescue path. -/
def v2_1NoCall : List Nat := (List.range 147).filter (· ∉ [0, 22, 70, 85, 90, 93, 107])

theorem v2_1NoCall_set : ExecsSet Xinst.isStaticcall ImplV2_1.cert.prog v2_1NoCall = true := by decide +kernel

/-- **`FiatTokenV2_1` decodes `CALL` only on `rescueERC20`.** -/
theorem v2_1_noCall {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (hcode : sevm.code = ImplV2_1.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (sel : Blanc.Sevm.selector sevm ≠ rescueSelector) :
    ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → Xinst.isStaticcall x = true :=
  execs_of_reach ImplV2_1.cert_check rfl rfl run hcode hsg fun T h t x g hx => by
    change Reach _ _ _ ⟨_, ImplV2_1.t_0000_c0, []⟩ T at h
    censusWalk h t hx sel v2_1NoCall_set

/-! ## Below a version's frame -/

theorem isStaticcall_eq {x : Xinst} (h : Xinst.isStaticcall x = true) : x = .staticcall := by
  cases x <;> first | rfl | cases h

/-- A delegate child of `FiatTokenV2_2` runs the library. -/
theorem impl_delegate_lib {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (codeEq : sevm.code = Impl.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (libCode : pre.state.getCode usdcLib = Lib.code) {N : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N)
    (hat : Ninst.At N.sevm.code N.pc (.exec .delegatecall)) {f : Frame} {rsm : Resume}
    (hx : Xinst.step N.sevm N.devm .delegatecall = .spawn f rsm) :
    f.inner.code = Lib.code := by
  have sevmEq : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix_noStateGas certL_check
    (F := ⟨0, sevm, pre, out, run⟩) rfl codeEq hsg chain
  have frames := Cursor.framesSat_of_reachable certL_framesSat certL_framesSat_head reach
  have hP := ok.framesSat_exec frames hat
  simp only [implP, beq_iff_eq] at hP
  have hw := ok.stack_const hP
  obtain ⟨g, a, rest, hs⟩ := Xinst.step_delegatecall_spawn_stack hx
  rw [hs] at hw
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hw
  subst hw
  have nodeCode : N.devm.getCode usdcLib = Lib.code :=
    ((Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain).2 usdcLib
      (by change (pre.state.getCode usdcLib).toList ≠ []; rw [libCode]; exact lib_toList_ne_nil)).trans libCode
  have adr : usdcLib.toB256.toAdr = usdcLib := toAdr_toB256 _
  obtain ⟨-, -, -, -, -, hK⟩ := step_delegatecall_spawn_shapeH (sevmEq ▸ hsg) hx hs
    (by rw [adr, nodeCode]; exact lib_undelegated)
  rw [adr] at hK
  rw [hK, nodeCode]

/-- **Below a version's frame on another selector than `rescueERC20`, every committed frame is static
or runs the library.** -/
theorem version_below {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (version : CurveCoins.UsdcVersion sevm.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (sel : Blanc.Sevm.selector sevm ≠ rescueSelector)
    (lib : sevm.code = Impl.code → pre.state.getCode usdcLib = Lib.code) :
    ∀ g ∈ Exec.descendantFrames run, g.sevm.isStatic = true ∨ g.sevm.code = Lib.code := by
  have static : (∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → Xinst.isStaticcall x = true) →
      ∀ g ∈ Exec.descendantFrames run, g.sevm.isStatic = true ∨ g.sevm.code = Lib.code := fun h g hg =>
    .inl (Exec.descendantFrames_isStatic_of_staticOnly _
      (fun {N x} chain hat => isStaticcall_eq (h N chain x hat)) run (.refl _) g hg)
  rcases version with hc | hc | hc
  · exact static (v2_noCall run hc hsg sel)
  · exact static (v2_1_noCall run hc hsg sel)
  · refine Exec.descendantFrames_of_spawns (root := ⟨0, sevm, pre, out, run⟩)
      (Q := fun g => g.sevm.isStatic = true ∨ g.sevm.code = Lib.code) ?_ run (.refl _)
      (fun _ h => h) (fun _ h => h)
    intro N f rsm pc' cevm raw child h chain step enter _ _
    obtain ⟨x, hat, spawn, -⟩ := Evm.step_spawn_inv step
    have hx : x = .delegatecall := by
      have := v22_noCall run hc hsg sel N chain x hat
      simpa only [onlyDelegate, beq_iff_eq] using this
    subst hx
    have ccode : cevm.sta.code = Lib.code := by
      rw [Frame.enter_run_code enter]
      exact impl_delegate_lib run hc hsg (lib hc) chain hat spawn
    have sevmEq : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
    have csg : cevm.sta.benvStat.rules.stateGas = none := by
      rw [Blanc.Evm.step_spawn_child_benvStat step enter, sevmEq]
      exact hsg
    obtain ⟨pcZero, -, -⟩ := Blanc.Evm.step_spawn_child step enter
    refine ⟨.inr ccode, fun g hg => .inl ?_⟩
    obtain ⟨cpc, csevm, cdyna⟩ := cevm
    dsimp only at pcZero ccode csg child
    subst pcZero
    exact Exec.descendantFrames_isStatic_of_staticOnly
      (⟨0, csevm, cdyna, raw, child⟩ : Exec.Deriv)
      (fun {M x} ch hatM => by
        obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix_noStateGas Lib.cert_check
          (F := ⟨0, csevm, cdyna, raw, child⟩) rfl ccode csg ch
        exact isStaticcall_eq (ok.execsSatisfy (Cursor.execsSatisfy_of_reachable lib_staticOnly reach) hatM))
      child (.refl _) g hg

/-! ## Below a proxy frame -/

/-- A delegate child of a proxy frame inherits its frame and calldata. -/
theorem proxy_delegate_child {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out) (codeEq : sevm.code = Proxy.code)
    (hsg : sevm.benvStat.rules.stateGas = none) (bal : sevm.benvStat.rules.bal = none)
    (notAdmin : sevm.caller ≠ adminOf pre.state sevm.currentTarget)
    (size : sevm.data.length < 2 ^ 256)
    {N : Exec.Deriv} (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N)
    {x : Xinst} (hat : Ninst.At N.sevm.code N.pc (.exec x))
    {frame : Jaune.Frame} {resume : Resume}
    (spawn : Xinst.step N.sevm N.devm x = .spawn frame resume) :
    x = .delegatecall ∧ frame.inner.currentTarget = sevm.currentTarget ∧
      frame.inner.isStatic = sevm.isStatic ∧ frame.inner.data = sevm.data ∧
      N.devm.state = pre.state ∧
      (getDelegatedCodeAddress (N.devm.getCode (pre.getStorVal sevm.currentTarget implSlot).toAdr) = none →
        frame.inner.code = N.devm.getCode (pre.getStorVal sevm.currentTarget implSlot).toAdr) := by
  have env : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  obtain ⟨f, K, ⟨rfl, delegated⟩ | ⟨rfl, self, -⟩⟩ := Proxy.proxy_nodeH run codeEq hsg bal chain hat
  · obtain ⟨_, b, gas, S, M, G, tail, state, tree, input⟩ := delegated
    change N.devm = _ at input
    have spawn' := spawn
    rw [input] at spawn'
    obtain ⟨target, -, -, static, data⟩ := Xinst.step_delegatecall_spawn_St_noStateGas (env ▸ hsg) spawn'
    refine ⟨rfl, target.trans (congrArg Sevm.currentTarget env), static.trans (congrArg Sevm.isStatic env), ?_,
      by rw [input]; exact state, fun undelegated => ?_⟩
    · rw [data]
      have read : ((M.write 0
          (sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0)).read 0
          sevm.data.length.toB256.toNat).1 =
          sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0 := by
        by_cases empty : sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0 = []
        · have length := congrArg List.length empty
          simp only [List.length_sliceD, List.length_nil] at length
          rw [empty, length]
          rfl
        · simpa only [List.length_sliceD] using Mem.read_write_zero M empty
      have read' := read
      rw [B256.toNat_toB256_of_lt size] at read'
      simp only [show (0 : B256).toNat = 0 from rfl]
      rw [B256.toNat_toB256_of_lt size, read']
      exact Bytes.sliceD_zero_length rfl
    · exact (step_delegatecall_spawn_shapeH (env ▸ hsg) spawn (by rw [input]; rfl) undelegated).2.2.2.2.2
  · exact (notAdmin (by rw [self.1]; rfl)).elim

theorem proxy_ne_v2 : ImplV2.code ≠ Proxy.code := fun h =>
  absurd (congrArg ByteArray.size h) (by decide +kernel)

theorem proxy_ne_v2_1 : ImplV2_1.code ≠ Proxy.code := fun h =>
  absurd (congrArg ByteArray.size h) (by decide +kernel)

theorem version_undelegated {C : ByteArray} (h : CurveCoins.UsdcVersion C) :
    getDelegatedCodeAddress C = none := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

theorem version_ne_proxy {C : ByteArray} (h : CurveCoins.UsdcVersion C) : C ≠ Proxy.code := by
  rcases h with rfl | rfl | rfl
  · exact proxy_ne_v2
  · exact proxy_ne_v2_1
  · exact proxy_ne_impl.symm

/-- **What an entry frame's chain link asks**: the implementation word is certified at its entry, and its calldata
fits a word (`settled_data_bound`). -/
def EntryAllowed (T : Adr) (F : Exec.Frame) : Prop :=
  UsdcCertified F.pre T ∧ F.sevm.data.length < 2 ^ 256

/-- **An allowed entry frame off `rescueERC20` has no observed committed descendant.** -/
theorem entryQuiet {T : Adr} {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (codeEq : sevm.code = Proxy.code) (fork : HistFork sevm.benvStat.fork) (target : sevm.currentTarget = T)
    (notAdmin : sevm.caller ≠ adminOf pre.state T) (sel : Blanc.Sevm.selector sevm ≠ rescueSelector)
    (certified : UsdcCertified pre T) (size : sevm.data.length < 2 ^ 256) :
    (Exec.descendantFrames run).flatMap (coinObs T (EntryObs T)) = [] := by
  have hsg : sevm.benvStat.rules.stateGas = none := fork.stateGas_none
  have bal : sevm.benvStat.rules.bal = none := fork.bal_none
  refine List.flatMap_eq_nil_iff.mpr ?_
  refine Exec.descendantFrames_of_spawns (root := ⟨0, sevm, pre, .ok post, run⟩)
    (Q := fun g => coinObs T (EntryObs T) g = []) ?_ run (.refl _) (fun _ h => h) (fun _ h => h)
  intro N f rsm pc' cevm raw child h chain step enter _ _
  obtain ⟨x, hat, spawn, -⟩ := Evm.step_spawn_inv step
  obtain ⟨rfl, ctarget, cstatic, cdata, cstate, ccode⟩ :=
    proxy_delegate_child run codeEq hsg bal (by rw [target]; exact notAdmin) size chain hat spawn
  have sevmEq : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  have nodeGetCode : ∀ a, N.devm.getCode a = pre.getCode a := fun a => by
    simp only [Devm.getCode, Devm.getAcct, cstate]
  have version : CurveCoins.UsdcVersion (pre.getCode (pre.getStorVal T implSlot).toAdr) := certified.1
  have code : cevm.sta.code = pre.getCode (pre.getStorVal T implSlot).toAdr := by
    rw [Frame.enter_run_code enter, ccode (by rw [target, nodeGetCode]; exact version_undelegated version),
      target, nodeGetCode]
  have childVersion : CurveCoins.UsdcVersion cevm.sta.code := code ▸ version
  obtain ⟨benv, -, hcevm⟩ := Frame.enter_run_inv enter
  obtain ⟨pcZero, childCode, -⟩ := Blanc.Evm.step_spawn_child step enter
  have childData : cevm.sta.data = sevm.data := by rw [hcevm]; exact cdata
  have childSel : Blanc.Sevm.selector cevm.sta = Blanc.Sevm.selector sevm := by
    simp only [Blanc.Sevm.selector, Sevm.dataWord, childData]
  have csg : cevm.sta.benvStat.rules.stateGas = none := by
    rw [Blanc.Evm.step_spawn_child_benvStat step enter, sevmEq]
    exact hsg
  have libClause : cevm.sta.code = Impl.code → cevm.dyna.state.getCode usdcLib = Lib.code := fun hi => by
    have := certified.2.1 (code.symm.trans hi)
    change (cevm.dyna.getCode usdcLib) = _
    rw [childCode, nodeGetCode]
    exact this
  have noObs : ∀ g : Exec.Frame, (g.sevm.isStatic = true ∨ g.sevm.code = Lib.code) →
      coinObs T (EntryObs T) g = [] := fun g hg => ite_eq_right fun obs => by
    rcases hg with s | c
    · rw [s] at obs
      cases obs.2.1
    · exact lib_ne_proxy (c.symm.trans obs.2.2.1)
  refine ⟨ite_eq_right fun obs => version_ne_proxy childVersion obs.2.2.1, fun g hg => ?_⟩
  obtain ⟨cpc, csevm, cdyna⟩ := cevm
  dsimp only at pcZero childVersion childSel csg libClause child
  subst pcZero
  exact noObs g (version_below child childVersion csg (by rw [childSel]; exact sel) libClause g hg)

end Blanc.Lift.Usdc
