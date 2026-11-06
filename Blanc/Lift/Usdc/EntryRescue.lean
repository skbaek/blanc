import Blanc.Lift.Usdc.HistorySlotsRescue
import Blanc.Lift.Usdc.ImplV2.Check
import Blanc.Lift.Usdc.ImplV2_1.Check
import Blanc.Lift.Usdc.EntryChainProof

/-!
# `rescueERC20` of FiatTokenV2 and V2_1: one `CALL`, silent around it

The stop check of M3, for the two older versions: from the dispatcher's entry under the `rescueERC20` selector, the
first external instruction of a frame is a `CALL`, its state is the frame's, and everything after it is silent
(`PreSet`, `SilentSet`, decided; `reach_rescue`, walked; `Impl.reach_rescue` is V2_2's). `version_rescue_nodes` and
`version_rescue_end` say so for all three, on historical forks.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift

/-- The dispatcher's comparison ladder under `rescueERC20`'s selector, to its hit. -/
macro "rescueLadder " hP:ident run:ident hT:ident : tactic => `(tactic|
  repeat (first
    | (obtain ⟨_, $run:ident⟩ := rr_dest $run $hT)
    | (obtain ⟨_, $run:ident⟩ := rr_cmp_gt $hP $run $hT; rw [ite_eq_left (by decide)] at $run:ident)
    | (obtain ⟨_, $run:ident⟩ := rr_cmp_gt $hP $run $hT; rw [ite_eq_right (by decide)] at $run:ident)
    | (obtain ⟨_, $run:ident⟩ := rr_cmp_eq $hP rfl $run $hT; rw [ite_eq_left (by decide)] at $run:ident)))

set_option hygiene false in
/-- The opening of the dispatcher, common to the versions: to the selector on the stack. -/
macro "rescueOpening " hP:ident run:ident hT:ident hw:ident : tactic => `(tactic| (
  obtain ⟨_, s, $run:ident⟩ := rr_next $run $hT; obtain ⟨_, rfl⟩ := ri_push ($hP s)
  obtain ⟨_, s, $run:ident⟩ := rr_next $run $hT; obtain ⟨_, rfl⟩ := ri_push ($hP s)
  obtain ⟨_, s, $run:ident⟩ := rr_next $run $hT; obtain ⟨_, rfl⟩ := ri_mstore ($hP s)
  obtain ⟨_, s, $run:ident⟩ := rr_next $run $hT; obtain ⟨_, rfl⟩ := ri_callvalue ($hP s)
  obtain ⟨_, s, $run:ident⟩ := rr_next $run $hT; obtain ⟨_, rfl⟩ := ri_dup rfl ($hP s)
  obtain ⟨_, s, $run:ident⟩ := rr_next $run $hT; obtain ⟨_, rfl⟩ := ri_iszero ($hP s)
  obtain ⟨_, s, $run:ident⟩ := rr_next $run $hT; obtain ⟨_, rfl⟩ := ri_push ($hP s)
  rcases rr_branch $run $hT with ⟨-, _, $run:ident⟩ | ⟨-, _, $run:ident⟩
  · exact (Reach.false_of_execFree (E := []) (by decide) $run $hT (by decide) (fun _ h => by cases h)).elim
  obtain ⟨_, $run:ident⟩ := rr_dest $run $hT
  obtain ⟨_, s, $run:ident⟩ := rr_next $run $hT; obtain ⟨_, rfl⟩ := ri_pop ($hP s)
  obtain ⟨_, s, $run:ident⟩ := rr_next $run $hT; obtain ⟨_, rfl⟩ := ri_push ($hP s)
  obtain ⟨_, s, $run:ident⟩ := rr_next $run $hT; obtain ⟨_, rfl⟩ := ri_calldatasize ($hP s)
  obtain ⟨_, s, $run:ident⟩ := rr_next $run $hT; obtain ⟨_, rfl⟩ := ri_lt ($hP s)
  obtain ⟨_, s, $run:ident⟩ := rr_next $run $hT; obtain ⟨_, rfl⟩ := ri_push ($hP s)
  rcases rr_branch $run $hT with ⟨-, _, $run:ident⟩ | ⟨-, _, $run:ident⟩
  swap; · exact (Reach.false_of_execFree (E := []) (by decide) $run $hT (by decide) (fun _ h => by cases h)).elim
  obtain ⟨_, s, $run:ident⟩ := rr_next $run $hT; obtain ⟨_, rfl⟩ := ri_push ($hP s)
  obtain ⟨_, s, $run:ident⟩ := rr_next $run $hT; obtain ⟨_, rfl⟩ := ri_calldataload ($hP s)
  obtain ⟨_, s, $run:ident⟩ := rr_next $run $hT; obtain ⟨_, rfl⟩ := ri_push ($hP s)
  obtain ⟨_, s, $run:ident⟩ := rr_next $run $hT; obtain ⟨_, rfl⟩ := ri_shr ($hP s)
  rw [$hw:ident] at $run:ident))


set_option hygiene false in
/-- **`rescueERC20` without its call keeps the storage**, by the dispatcher's walk and the decided region. -/
macro "rescueEndWalk" : tactic => `(tactic| (
  let R : Exec.Deriv := ⟨0, sevm, pre, .ok post, run⟩
  have noDesc : Exec.rawFrameDescendants R.exc = [] := Exec.rawFrameDescendants_eq_nil_of_noExec run none
  have hX : ∀ {d : Devm} {x : Xinst} {d' : Devm}, StepIn R sevm d (.exec x) d' →
      State.Protected d.state P → d'.state.getStor P = d.state.getStor P :=
    fun h hp => stepIn_exec_stor noDesc h hp
  have hw := rescue_word hsel
  have placed := cursor_start cert_check (F := R) rfl codeEq
  rcases placed.sourceRunReturnH cert_check rfl hsg with halted | ⟨c, tail, -, -, hK, -⟩
  swap
  · cases hK
  have sound : ∀ {s d n d'}, StepIn R s d n d' → Ninst.Run s d n d' := StepIn.toRun
  change SFunc.RunP (StepIn R) cert.prog sevm pre t_0000_c0 (.halted post) at halted
  rw [St.self' pre] at halted
  have run := SFunc.runP_iff_runCutP_nil.mp halted
  clear halted placed
  unfold t_0000_c0 at run
  winv 7 using sound
  rcases ric_branchP run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_0010_c0 at run
  obtain ⟨_, run⟩ := ric_destP run
  winv 5 using sound
  rcases ric_branchP run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap; · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_001a_c0 at run
  winv 4 using sound
  rw [hw] at run
  repeat (first
    | (obtain ⟨_, run⟩ := ric_destP run)
    | (obtain ⟨_, run⟩ := ric_cmp_gtP sound run; rw [ite_eq_left (by decide)] at run)
    | (obtain ⟨_, run⟩ := ric_cmp_gtP sound run; rw [ite_eq_right (by decide)] at run)
    | (obtain ⟨_, run⟩ := ric_cmp_eqP sound (List.not_mem_nil) rfl run; rw [ite_eq_left (by decide)] at run))
  obtain ⟨_, run⟩ := ric_cmp_eqP sound (List.not_mem_nil) rfl run
  rw [ite_eq_right (by decide)] at run
  exact SFunc.RunP.stor_of_preIn sound rescuePre_ok rescueSilent_ok hX
    (SFunc.runP_iff_runCutP_nil.mpr run) (by decide +kernel) prot))

theorem rescue_word {sevm : Sevm} (hsel : Blanc.Sevm.selector sevm = 0xb2118a8d) :
    Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Bytes.toB256 [0xb2, 0x11, 0x8a, 0x8d] := by
  rw [show Bytes.toB256 [0x00] = 0 from by decide, show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]
  exact hsel.trans (by decide)

namespace ImplV2

def rescuePre : List Nat := [26, 73, 87, 92, 95, 114, 4, 94, 96, 7, 97, 98]
def rescueSilent : List Nat := [4, 94, 96, 7, 97, 98]

theorem rescuePre_ok : PreSet cert.prog Impl.rescueEx rescuePre rescueSilent = true := by decide +kernel
theorem rescueSilent_ok : SilentSet cert.prog rescueSilent = true := by decide +kernel

theorem rescueWrapper_pre : t_0b07_c114.preIn Impl.rescueEx rescuePre rescueSilent = true := by decide +kernel

theorem reach_rescue {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {T : Conf}
    (hsel : Blanc.Sevm.selector sevm = 0xb2118a8d)
    (run : Reach P cert.prog sevm ⟨St b S M G, t_0000_c0, []⟩ T) (hT : AtExec T) :
    T.d.state = b.state ∧ T.f.preIn Impl.rescueEx rescuePre rescueSilent = true ∧
      ∀ s ∈ T.K, s.silentIn rescueSilent = true := by
  have hw := rescue_word hsel
  unfold t_0000_c0 at run
  rescueOpening hP run hT hw
  rescueLadder hP run hT
  obtain ⟨_, run⟩ := rr_cmp_eq hP rfl run hT
  rw [ite_eq_right (by decide)] at run
  exact Reach.firstExec hP rescuePre_ok rescueSilent_ok run hT rfl
    (.inl ⟨rescueWrapper_pre, fun _ h => nomatch h⟩)


theorem rescue_end {P : Adr} {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (codeEq : sevm.code = code) (hsg : sevm.benvStat.rules.stateGas = none)
    (hsel : Blanc.Sevm.selector sevm = 0xb2118a8d) (prot : State.Protected pre.state P)
    (none : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)) :
    post.state.getStor P = pre.state.getStor P := by
  rescueEndWalk

end ImplV2

namespace ImplV2_1

def rescuePre : List Nat := [22, 70, 85, 90, 93, 107, 4, 92, 94, 8, 95, 96]
def rescueSilent : List Nat := [4, 92, 94, 8, 95, 96]

theorem rescuePre_ok : PreSet cert.prog Impl.rescueEx rescuePre rescueSilent = true := by decide +kernel
theorem rescueSilent_ok : SilentSet cert.prog rescueSilent = true := by decide +kernel

theorem rescueWrapper_pre : t_0ab8_c107.preIn Impl.rescueEx rescuePre rescueSilent = true := by decide +kernel

theorem reach_rescue {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {T : Conf}
    (hsel : Blanc.Sevm.selector sevm = 0xb2118a8d)
    (run : Reach P cert.prog sevm ⟨St b S M G, t_0000_c0, []⟩ T) (hT : AtExec T) :
    T.d.state = b.state ∧ T.f.preIn Impl.rescueEx rescuePre rescueSilent = true ∧
      ∀ s ∈ T.K, s.silentIn rescueSilent = true := by
  have hw := rescue_word hsel
  unfold t_0000_c0 at run
  rescueOpening hP run hT hw
  rescueLadder hP run hT
  obtain ⟨_, run⟩ := rr_cmp_eq hP rfl run hT
  rw [ite_eq_right (by decide)] at run
  exact Reach.firstExec hP rescuePre_ok rescueSilent_ok run hT rfl
    (.inl ⟨rescueWrapper_pre, fun _ h => nomatch h⟩)


theorem rescue_end {P : Adr} {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (codeEq : sevm.code = code) (hsg : sevm.benvStat.rules.stateGas = none)
    (hsel : Blanc.Sevm.selector sevm = 0xb2118a8d) (prot : State.Protected pre.state P)
    (none : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)) :
    post.state.getStor P = pre.state.getStor P := by
  rescueEndWalk

end ImplV2_1

namespace Impl

theorem rescue_end {P : Adr} {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (codeEq : sevm.code = code) (hsg : sevm.benvStat.rules.stateGas = none)
    (hsel : Blanc.Sevm.selector sevm = 0xb2118a8d) (prot : State.Protected pre.state P)
    (none : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)) :
    post.state.getStor P = pre.state.getStor P := by
  rescueEndWalk

end Impl

/-! ## What a version's frame on `rescueERC20` does -/

/-- From a region reach: the instruction is accepted, the state is the frame's, and after it the frame is silent. -/
theorem region_after {code : ByteArray} {c : Cert} {f0 : SFunc} (checked : Cert.check code c = true)
    (hf0 : (Cursor.start c).f = f0) (hK0 : (Cursor.start c).K = []) {ex : Xinst → Bool} {Pre S : List Nat}
    (hS : SilentSet c.prog S = true) {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hsg : sevm.benvStat.rules.stateGas = none)
    (hr : ∀ T, Reach (StepIn ⟨0, sevm, pre, .ok post, run⟩) c.prog sevm
      ⟨St pre pre.stack pre.memory pre.gasLeft, f0, []⟩ T → AtExec T →
      T.d.state = pre.state ∧ T.f.preIn ex Pre S = true ∧ ∀ s ∈ T.K, s.silentIn S = true)
    {N : Exec.Deriv} (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N) {x : Xinst}
    (hat : Ninst.At N.sevm.code N.pc (.exec x)) :
    ex x = true ∧ N.devm.state = pre.state ∧ ∀ N', Exec.Deriv.ParentStep N' N →
      post.state = N'.devm.state ∧
        ∀ M, Exec.Deriv.ParentPrefix N' M → ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y) := by
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix_noStateGas checked rfl hcode hsg chain
  obtain ⟨g, hf, -⟩ := ok.tree_of_exec hat
  have reach' : Reach (StepIn ⟨0, sevm, pre, .ok post, run⟩) c.prog sevm
      ⟨St pre pre.stack pre.memory pre.gasLeft, f0, []⟩ (κ.conf N.devm) := by
    rw [← St.self rfl rfl]
    have e : (Cursor.start c).conf pre = ⟨pre, f0, []⟩ := by
      simp only [Cursor.conf, hf0, hK0, List.map_nil]
    rw [← e]
    exact reach
  obtain ⟨state, region, hK⟩ := hr _ reach' ⟨x, g, hf⟩
  have region' : κ.f.preIn ex Pre S = true := region
  rw [hf] at region'
  simp only [SFunc.preIn, Bool.and_eq_true] at region'
  refine ⟨region'.1, state, fun N' edge => ?_⟩
  have hsevmN : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  have hsgN : N.sevm.benvStat.rules.stateGas = none := by rw [hsevmN]; exact hsg
  obtain ⟨κ₁, hs, -, ok₁⟩ := cursor_stepS_noStateGas checked ok edge hsgN
  obtain ⟨f, pc, a, m, K⟩ := κ
  dsimp only at hf hK
  subst hf
  cases hs with
  | next habs =>
    have hchain := chain.snoc edge
    have hsevmN' : N'.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq hchain
    have hsgN' : N'.sevm.benvStat.rules.stateGas = none := by rw [hsevmN']; exact hsg
    have success' : N'.exn = .ok post := Exec.Deriv.ParentPrefix.exn_eq hchain
    exact ⟨CursorOK.state_post_of_silentH checked hS _ rfl ok₁ success' hsgN' region'.2 hK,
      fun M hM y => noExec_after_of_cursorH checked hchain hM hsg ok₁ (ExecFreeSet.of_silentSet hS)
        (SFunc.execFreeIn_of_silentIn region'.2) (fun s hs => SFunc.execFreeIn_of_silentIn (hK s hs)) y⟩

/-- **A version's frame on `rescueERC20`**: its only external instruction is one `CALL`, reached with the frame's
state, and it is silent after. -/
theorem version_rescue_nodes {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (version : CurveCoins.UsdcVersion sevm.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (hsel : Blanc.Sevm.selector sevm = rescueSelector)
    {N : Exec.Deriv} (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N) {x : Xinst}
    (hat : Ninst.At N.sevm.code N.pc (.exec x)) :
    x = .call ∧ N.devm.state = pre.state ∧ ∀ N', Exec.Deriv.ParentStep N' N →
      post.state = N'.devm.state ∧
        ∀ M, Exec.Deriv.ParentPrefix N' M → ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y) := by
  have result : Impl.rescueEx x = true ∧ N.devm.state = pre.state ∧ ∀ N', Exec.Deriv.ParentStep N' N →
      post.state = N'.devm.state ∧
        ∀ M, Exec.Deriv.ParentPrefix N' M → ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y) := by
    rcases version with hc | hc | hc
    · exact region_after ImplV2.cert_check (f0 := ImplV2.t_0000_c0) rfl rfl ImplV2.rescueSilent_ok run hc hsg
        (fun T h t => ImplV2.reach_rescue StepIn.toRun hsel h t) chain hat
    · exact region_after ImplV2_1.cert_check (f0 := ImplV2_1.t_0000_c0) rfl rfl ImplV2_1.rescueSilent_ok run hc hsg
        (fun T h t => ImplV2_1.reach_rescue StepIn.toRun hsel h t) chain hat
    · exact region_after Impl.cert_check (f0 := Impl.t_0000_c0) rfl rfl Impl.rescueSilent_ok run hc hsg
        (fun T h t => Impl.reach_rescue StepIn.toRun hsel h t) chain hat
  exact ⟨by simpa only [Impl.rescueEx, beq_iff_eq] using result.1, result.2⟩

/-- A version's frame on `rescueERC20` that decodes no external instruction keeps the storage. -/
theorem version_rescue_end {P : Adr} {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (version : CurveCoins.UsdcVersion sevm.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (hsel : Blanc.Sevm.selector sevm = rescueSelector) (prot : State.Protected pre.state P)
    (none : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)) :
    post.state.getStor P = pre.state.getStor P := by
  rcases version with hc | hc | hc
  · exact ImplV2.rescue_end run hc hsg hsel prot none
  · exact ImplV2_1.rescue_end run hc hsg hsel prot none
  · exact Impl.rescue_end run hc hsg hsel prot none

end Blanc.Lift.Usdc
