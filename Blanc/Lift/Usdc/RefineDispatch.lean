import Blanc.Lift.Usdc.RefineDispatchCheck
import Blanc.Lift.Usdc.RefineShape
import Blanc.Lift.Usdc.Families
import Blanc.Lift.Cursor
import Blanc.Lift.ExactLeaf
import Blanc.Lift.PackedWord
import Jaune.MulDiv

/-!
# USDC refinement, dispatch family (U6g)

Certificate-driven walks over the implementation certificate (`Impl.cert`): the entry preamble
(nonpayable check, short-calldata check, selector extraction), then the dispatcher's comparison tree
evaluated at the selector (`SFunc.selWalk`, `Blanc/Lift/SelectorRoute.lean`), then the facts the
kernel decided about the wrapper entered (`RefineDispatchCheck.lean`).
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.Lift.Token

/-! ## The entry preamble -/

theorem shr_selector (sevm : Sevm) :
    Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Blanc.Sevm.selector sevm := rfl

/-- **The preamble of a cut run.**  The frame has no value, at least four calldata bytes, and the
dispatcher's comparison tree runs with the selector on top of the stack and the base unchanged. -/
theorem impl_preamble_cut {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg}
    (run : SFunc.RunCut implProg sevm [] (St b S M G) Impl.t_0000_c0 r) :
    sevm.value = 0 ∧ B256.ltCheck sevm.data.length.toB256 4 = 0 ∧
      ∃ M' G', SFunc.RunCut implProg sevm [] (St b (Blanc.Sevm.selector sevm :: S) M' G')
        dispTree r := by
  unfold Impl.t_0000_c0 at run
  obtain ⟨d, hd, h⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_mstore hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_callvalue hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_iszero hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branch h with ⟨-, _, h⟩ | ⟨nz, _, h⟩
  · exact (h.false_of_noOk (by decide)).elim
  have value : sevm.value = 0 := eq_of_eqCheck_ne nz
  unfold Impl.t_0010_c0 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_calldatasize hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_lt hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branch h with ⟨long, _, h⟩ | ⟨-, _, h⟩
  · rw [tree_001a] at h
    obtain ⟨d, hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_calldataload hd
    obtain ⟨d, hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_shr hd
    rw [shr_selector] at h
    exact ⟨value, long, _, _, h⟩
  · exact (h.false_of_noOk (by decide)).elim

/-- A reverting arm reaches no external instruction. -/
theorem reach_revert_false {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {d : Devm}
    {f : SFunc} {T : Conf} (hf : f.execFreeIn [] = true) (run : Reach P implProg sevm ⟨d, f, []⟩ T)
    (hT : AtExec T) : False :=
  Reach.false_of_execFree (E := []) rfl run hT hf (fun _ h => absurd h List.not_mem_nil)

/-- **The preamble of a reach** from the frame's start to an external instruction. -/
theorem impl_preamble_reach {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {sevm : Sevm} {b : Devm} {T : Conf}
    (run : Reach P implProg sevm ⟨b, Impl.t_0000_c0, []⟩ T) (hT : AtExec T) :
    ∃ M' G', Reach P implProg sevm ⟨St b (Blanc.Sevm.selector sevm :: b.stack) M' G', dispTree, []⟩ T := by
  rw [St.self (d := b) rfl rfl] at run
  unfold Impl.t_0000_c0 at run
  obtain ⟨d, hd, h⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_push (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_push (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_mstore (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_callvalue (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_iszero (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_push (hP hd)
  rcases rr_branch h hT with ⟨-, _, h⟩ | ⟨-, _, h⟩
  · exact (reach_revert_false (by decide) h hT).elim
  unfold Impl.t_0010_c0 at h
  obtain ⟨_, h⟩ := rr_dest h hT
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_pop (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_push (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_calldatasize (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_lt (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_push (hP hd)
  rcases rr_branch h hT with ⟨-, _, h⟩ | ⟨-, _, h⟩
  · rw [tree_001a] at h
    obtain ⟨d, hd, h⟩ := rr_next h hT
    obtain ⟨_, rfl⟩ := ri_push (hP hd)
    obtain ⟨d, hd, h⟩ := rr_next h hT
    obtain ⟨_, rfl⟩ := ri_calldataload (hP hd)
    obtain ⟨d, hd, h⟩ := rr_next h hT
    obtain ⟨_, rfl⟩ := ri_push (hP hd)
    obtain ⟨d, hd, h⟩ := rr_next h hT
    obtain ⟨_, rfl⟩ := ri_shr (hP hd)
    rw [shr_selector] at h
    exact ⟨_, _, h⟩
  · exact (reach_revert_false (by decide) h hT).elim

/-! ## What a decoded message's selector is -/

theorem decodeCall_some {e : Sevm} {c : Call} (h : decodeCall e = some c) :
    ∃ r ∈ rows, r.sel = Blanc.Sevm.selector e ∧ r.read e = c ∧
      4 + 32 * r.headWords ≤ e.data.length := by
  unfold decodeCall at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i r hr
      split at h
      · rename_i len
        cases h
        have hp := List.find?_some hr
        exact ⟨r, List.mem_of_find?_eq_some hr, of_decide_eq_true hp, rfl, len⟩
      · cases h

/-- The selectors of the calls of this unit. -/
theorem decodeCall_sel {e : Sevm} {c : Call} (h : decodeCall e = some c) :
    (c = .view → Blanc.Sevm.selector e ∈ viewSels) ∧
      (c = .«initialize» → Blanc.Sevm.selector e = 0x3357162b) ∧
      (c = .initializeV2 → Blanc.Sevm.selector e = 0xd608ea64) ∧
      (∀ a, c = .initializeV2_1 a → Blanc.Sevm.selector e = 0x2fc81e09) ∧
      (c = .initializeV2_2 → Blanc.Sevm.selector e = 0x430239b4) := by
  obtain ⟨r, hr, hsel, rfl, -⟩ := decodeCall_some h
  rw [← hsel]
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun a h => ?_, fun h => ?_⟩ <;>
      first | decide | cases h

/-! ## The views -/

/-- A successful implementation frame starts at entry `0` of the certificate, in the cut form. -/
theorem impl_run_cut {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (code : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork) :
    SFunc.RunCut implProg sevm [] (St pre pre.stack pre.memory pre.gasLeft) Impl.t_0000_c0
      (.done (.halted post)) := by
  obtain ⟨f, hf, frun⟩ := lift_sound Impl.cert_check code fork run
  rw [show Impl.cert.prog = implProg from rfl, prog_zero] at hf
  cases hf
  rw [← St.self rfl rfl]
  exact SFunc.Run.cut frun

/-- **A view writes nothing.**  A successful implementation frame whose message decodes to a view
leaves the persistent state as it found it. -/
theorem impl_view_state {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (code : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork)
    (dec : decodeCall sevm = some .view) : post.state = pre.state := by
  obtain ⟨-, -, M, G, drun⟩ := impl_preamble_cut (impl_run_cut run code fork)
  have routes := List.all_eq_true.mp view_routes _ ((decodeCall_sel dec).1 rfl)
  split at routes
  · rename_i p hw
    rcases p with ⟨c, j⟩
    obtain ⟨-, g, G', hg, grun⟩ := SFunc.RunCut.selWalk_inl hw drun
    have hj : j ∈ viewEntries := of_decide_eq_true routes
    have closed := List.all_eq_true.mp view_silent j hj
    rw [hg] at closed
    simp only [Bool.and_eq_true] at closed
    exact SFunc.Run.state_of_silent view_silent closed.1 closed.2 grun.uncut
  · cases routes

/-- **A view calls nothing.**  No node of a successful implementation frame whose message decodes
to a view decodes an external instruction. -/
theorem impl_view_noExec {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (code : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork)
    (dec : decodeCall sevm = some .view) :
    ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x) := by
  intro N hN x hx
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix Impl.cert_check
    (R := ⟨0, sevm, pre, .ok post, run⟩) rfl code fork hN
  obtain ⟨g, hf, -⟩ := ok.tree_of_exec hx
  have hT : AtExec (κ.conf N.devm) := ⟨x, g, hf⟩
  change Reach (StepIn ⟨0, sevm, pre, .ok post, run⟩) implProg sevm ⟨pre, Impl.t_0000_c0, []⟩
    (κ.conf N.devm) at reach
  obtain ⟨M, G, dreach⟩ := impl_preamble_reach StepIn.toRun reach hT
  have routes := List.all_eq_true.mp view_routes _ ((decodeCall_sel dec).1 rfl)
  split at routes
  · rename_i p hw
    rcases p with ⟨c, j⟩
    obtain ⟨-, g, G', hg, greach⟩ := Reach.selWalk_inl StepIn.toRun hw dreach hT
    have hj : j ∈ viewEntries := of_decide_eq_true routes
    exact Reach.false_of_execFree view_execFree greach hT (ExecFreeSet.lookup view_execFree hj hg)
      (fun _ h => absurd h List.not_mem_nil)
  · cases routes

open Classical in
/-- **The whole-frame law of the views** (U6g): a successful implementation frame whose message
decodes to a view commits the book's identity step, keeps the proxy's storage, and spawns nothing. -/
theorem impl_view_law : ImplStepLaw (· = Call.view) := by
  intro P U sevm pre post run code _ _ fork _ _ _ _ _ admin c dec hc
  subst hc
  have stor : post.state.getStor P = pre.state.getStor P := by
    rw [impl_view_state run code fork dec]
  refine ⟨?_, by rw [stor], by rw [stor],
    fun N hN x hx => (impl_view_noExec run code fork dec N hN x hx).elim⟩
  rw [stor]
  change (if sevm.caller = (ledger U (pre.state.getStor P)).admin then
      (if adminGetter sevm then some (ledger U (pre.state.getStor P)) else none)
    else match decodeCall sevm with
      | none => none
      | some c => (ledger U (pre.state.getStor P)).step P sevm.caller c) = _
  have admin' : sevm.caller ≠ (ledger U (pre.state.getStor P)).admin := admin
  rw [ite_eq_right_of_eq_false _ _ (eq_false admin'), dec]
  rfl

/-! ## The initializers at a good ledger -/

/-- **The initializers' law** (U6g): on a pre-state whose ledger is good, no successful
implementation frame decodes to a call of `fam` (the shape of `ImplStepLaw` with the `Good`
premise). -/
def InitRevertLaw (fam : Call → Prop) : Prop :=
  ∀ {P : Adr} {U : Key → Prop} {sevm : Sevm} {pre post : Devm}, Exec 0 sevm pre (.ok post) →
    sevm.code = Impl.code → sevm.currentTarget = P → sevm.codeAddress = some usdcImpl →
    CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
    SlotFootprint.Inj Key.slot U → SlotFootprint.Apart Key.slot fixedSlots U →
    (∀ k ∈ frameKeys sevm, U k) → some (pre.state.getCode usdcLib).toList = libSem.image →
    sevm.caller ≠ adminOf pre.state P → (ledger U (pre.state.getStor P)).Good →
    ∀ c, decodeCall sevm = some c → ¬ fam c

/-- A successful frame routed to an initializer's wrapper runs the initializer's body from a
machine with the frame's starting state. -/
theorem impl_body {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (code : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork) {σ : B256} {j k : Nat}
    {w g : SFunc} (sel : Blanc.Sevm.selector sevm = σ) (route : dispTree.selWalk σ = .inl (σ, j))
    (hw : implProg[j]? = some w) (hc : w.toCall k = true) (hg : implProg[k]? = some g) :
    ∃ d o, d.state = pre.state ∧ SFunc.Run implProg sevm d g o := by
  obtain ⟨-, -, M, G, drun⟩ := impl_preamble_cut (impl_run_cut run code fork)
  rw [sel] at drun
  obtain ⟨-, w', G', hw', wrun⟩ := SFunc.RunCut.selWalk_inl route drun
  rw [hw] at hw'
  cases hw'
  obtain ⟨d, o, hs, grun⟩ := SFunc.RunP.callee_of_toCall id hg hc wrun.uncut
  exact ⟨d, o, hs, grun⟩

theorem and_ff_toNat (x : B256) : (Bytes.toB256 [0xff] &&& x).toNat = x.toNat % 256 := by
  rw [B256.and_comm, show Bytes.toB256 [0xff] = (2 ^ 8 - 1).toB256 from rfl,
    PackedWord.lowMask_toNat x (by decide)]
  rfl

theorem div_160_toNat (x : B256) :
    (x / Bytes.toB256 [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toNat = x.toNat / 2 ^ 160 := by
  rw [B256.toNat_div (by decide)]
  rfl

theorem ne_zero_of_eqCheck_zero {x : B256} (h : B256.eqCheck x 0 = 0) : x ≠ 0 := by
  intro hx
  subst hx
  exact absurd h (by decide)

/-- The packed flag at byte 20 of a word, as the code reads it, is nonzero when the flag is set. -/
theorem flag20_read {v : B256} (h : flag20 v = true) :
    Bytes.toB256 [0xff] &&& (v / Bytes.toB256 [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) ≠ 0 := by
  intro hz
  have hn := congrArg B256.toNat hz
  rw [and_ff_toNat, div_160_toNat] at hn
  exact of_decide_eq_true h hn

/-- The `uint8` at byte 0 of a word, as the code reads it, is `3` when the version is `3`. -/
theorem version_read {v : B256} (h : v.toNat % 256 = 3) {n : B256} (hn : n.toNat ≠ 3) :
    n ≠ Bytes.toB256 [0xff] &&& v := by
  intro he
  rw [he, and_ff_toNat, h] at hn
  exact hn rfl

/-- `require(_initializedVersion == n)` with `n ≠ 3` has no run at version `3`. -/
theorem version_body_false {fs : List SFunc} {sevm : Sevm} {d : Devm} {o : Outcome} {n : UInt8}
    {l1 l2 l3} {dst : Bytes} {l4 : dst.length ≤ 32} {f g : SFunc} (hf : f.noOk = true)
    (hn : (Bytes.toB256 [n]).toNat ≠ 3) (fork : CoveredFork sevm.benvStat.fork)
    (v : ((d.state.getStor sevm.currentTarget).get 18).toNat % 256 = 3)
    (run : SFunc.Run fs sevm d (.dest (.next (.push [0x12] l1) (.next (.reg .sload)
      (.next (.push [0xff] l2) (.next (.reg .and) (.next (.push [n] l3) (.next (.reg .eq)
      (.next (.push dst l4) (.branch f g))))))))) o) : False := by
  have h := SFunc.Run.cut run
  rw [St.self (d := d) rfl rfl] at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_eq hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branch h with ⟨-, _, h⟩ | ⟨nz, -⟩
  · exact h.false_of_noOk hf
  · exact version_read v hn (eq_of_eqCheck_ne nz)

/-- `initialize`'s `require(!initialized)` has no run once the contract is initialized. -/
theorem initialize_body_false {sevm : Sevm} {d : Devm} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (flag : flag20 ((d.state.getStor sevm.currentTarget).get 8) = true)
    (run : SFunc.Run implProg sevm d Impl.t_19e1_c61 o) : False := by
  have h := SFunc.Run.cut run
  rw [St.self (d := d) rfl rfl] at h
  unfold Impl.t_19e1_c61 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_div hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_iszero hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branch h with ⟨-, _, h⟩ | ⟨nz, -⟩
  · exact h.false_of_noOk (by decide)
  · exact flag20_read flag (eq_of_eqCheck_ne nz)

/-- `initializeV2`'s `require(initialized && _initializedVersion == 0)` has no run at version `3`
of an initialized contract. -/
theorem initializeV2_body_false {sevm : Sevm} {d : Devm} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (flag : flag20 ((d.state.getStor sevm.currentTarget).get 8) = true)
    (v : ((d.state.getStor sevm.currentTarget).get 18).toNat % 256 = 3)
    (run : SFunc.Run implProg sevm d Impl.t_3744_c25 o) : False := by
  have h := SFunc.Run.cut run
  rw [St.self (d := d) rfl rfl] at h
  unfold Impl.t_3744_c25 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_div hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_iszero hd
  obtain ⟨d', hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branchTo List.not_mem_nil init_lookups.2.2.2.2.2.2.2.2 h with ⟨z, _, h⟩ | ⟨nz, -⟩
  · unfold Impl.t_3769_c25 at h
    obtain ⟨d', hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_pop hd
    obtain ⟨d', hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d', hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_sload fork hd
    obtain ⟨d', hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d', hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_and hd
    obtain ⟨d', hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_iszero hd
    unfold Impl.t_3771_c5 at h
    obtain ⟨_, h⟩ := ric_dest h
    obtain ⟨d', hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_push hd
    rcases ric_branch h with ⟨-, _, h⟩ | ⟨nz, -⟩
    · exact h.false_of_noOk (by decide)
    · have e := (eq_of_eqCheck_ne nz).symm
      simp only [Devm.getStorVal, Devm.getAcct, NodeWalk.afterSload_state] at e
      exact version_read v (n := 0) (by decide) e
  · exact flag20_read flag (eq_of_eqCheck_ne nz)

/-- **`initialize` and `initializeV2_2` revert at a good ledger** (U6g; the model reverts them,
decision usdc-u5a-initialize-revert). -/
theorem impl_initRevert : InitRevertLaw famInitRevert := by
  intro P U sevm pre post run code target _ fork _ _ _ _ _ _ good c dec hc
  have version : ((pre.state.getStor P).get 18).toNat % 256 = 3 := good.version
  have flag : flag20 ((pre.state.getStor P).get 8) = true := good.initialized
  cases c <;> try exact (show False from hc).elim
  · obtain ⟨d, o, hs, grun⟩ := impl_body run code fork ((decodeCall_sel dec).2.1 rfl)
      route_initialize init_lookups.1 init_toCall.1 init_lookups.2.1
    exact initialize_body_false fork (by rw [hs, target]; exact flag) grun
  · obtain ⟨d, o, hs, grun⟩ := impl_body run code fork ((decodeCall_sel dec).2.2.2.2 rfl)
      route_initializeV2_2 init_lookups.2.2.2.2.2.2.1 init_toCall.2.2.2 init_lookups.2.2.2.2.2.2.2.1
    exact version_body_false (by decide) (by decide) fork (by rw [hs, target]; exact version) grun

/-- **`initializeV2` and `initializeV2_1` revert at a good ledger** (U6g): their guards
(`initialized ∧ version = 0`, `version = 1`) fail at version `3`. -/
theorem impl_initV2Revert :
    InitRevertLaw (fun c => c = .initializeV2 ∨ ∃ a, c = .initializeV2_1 a) := by
  intro P U sevm pre post run code target _ fork _ _ _ _ _ _ good c dec hc
  have version : ((pre.state.getStor P).get 18).toNat % 256 = 3 := good.version
  have flag : flag20 ((pre.state.getStor P).get 8) = true := good.initialized
  rcases hc with rfl | ⟨a, rfl⟩
  · obtain ⟨d, o, hs, grun⟩ := impl_body run code fork ((decodeCall_sel dec).2.2.1 rfl)
      route_initializeV2 init_lookups.2.2.1 init_toCall.2.1 init_lookups.2.2.2.1
    exact initializeV2_body_false fork (by rw [hs, target]; exact flag)
      (by rw [hs, target]; exact version) grun
  · obtain ⟨d, o, hs, grun⟩ := impl_body run code fork ((decodeCall_sel dec).2.2.2.1 a rfl)
      route_initializeV2_1 init_lookups.2.2.2.2.1 init_toCall.2.2.1 init_lookups.2.2.2.2.2.1
    exact version_body_false (by decide) (by decide) fork (by rw [hs, target]; exact version) grun

/-! ## Every successful frame decodes -/

theorem rows_headWords : ∀ r ∈ rows, r.headWords ≤ 9 := by decide

/-- **A successful implementation frame's message decodes**: it carries no value, its selector is
one of the dispatcher's 55, and its calldata holds that row's static head. -/
theorem impl_decodes {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (code : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork) :
    ∃ c, decodeCall sevm = some c := by
  obtain ⟨value, long, M, G, drun⟩ := impl_preamble_cut (impl_run_cut run code fork)
  rcases hw : dispTree.selWalk (Blanc.Sevm.selector sevm) with ⟨c, j⟩ | t
  · obtain ⟨hσ, g, G', hg, grun⟩ := SFunc.RunCut.selWalk_inl hw drun
    have table := List.all_eq_true.mp decode_table _ (SFunc.selWalk_mem_pairs hw)
    split at table
    · rename_i r hr
      have found : rows.find? (fun r => decide (r.sel = Blanc.Sevm.selector sevm)) = some r := by
        rw [hσ]
        exact hr
      refine ⟨_, decodeCall_of_find value found (calldata_head_fits long ?_ ?_)⟩
      · simp only [headOk, Bool.or_eq_true, beq_iff_eq] at table
        rcases table with h0 | hh
        · exact .inl h0
        · rw [hg] at hh
          exact .inr (SFunc.RunCut.headWord (of_decide_eq_true hh) grun)
      · have := rows_headWords r (List.mem_of_find?_eq_some hr)
        omega
    · cases table
  · obtain ⟨G', trun⟩ := SFunc.RunCut.selWalk_inr hw drun
    have leaf := List.all_eq_true.mp leaves_revert.1 _ (SFunc.selWalk_mem_leaves hw)
    simp only [Bool.and_eq_true] at leaf
    exact (SFunc.RunP.not_halted leaves_revert.2 leaf.1 leaf.2 trun.uncut rfl).elim

end Blanc.Lift.Usdc
