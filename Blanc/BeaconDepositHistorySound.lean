import Blanc.BeaconDepositSuccessSource
import Blanc.BeaconDepositHistory
import Blanc.StaticStorage

/-!
# Beacon deposit open-frame runtime soundness

The source-level kernel for the baseline-relative history specification.  The
three read-only dispatcher targets preserve storage outright; the deposit
target is handled through the successful source path and the admitted native
SHA-256 boundary.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

private theorem historyCore_of_inv
    {baseline : List B256} {f : Func}
    (silent : Func.Inv Devm.getStor Devm.getStor f) :
    Func.Core (runtime.main :: aux) (HistoryExtends baseline) f := by
  intro sevm s r run history
  rw [← congrFun (Func.of_inv Devm.getStor Devm.getStor silent run)
    sevm.currentTarget]
  exact history

private theorem supportsInterface_historyCore {baseline : List B256} :
    Func.Core (runtime.main :: aux) (HistoryExtends baseline)
      (nonpayableEndpoint supportsInterfaceEndpoint) := by
  apply historyCore_of_inv
  unfold nonpayableEndpoint supportsInterfaceEndpoint
  func_inv

private theorem getDepositCount_historyCore {baseline : List B256} :
    Func.Core (runtime.main :: aux) (HistoryExtends baseline)
      (nonpayableEndpoint getDepositCountEndpoint) := by
  apply historyCore_of_inv
  unfold nonpayableEndpoint getDepositCountEndpoint storeLe64At
  func_inv

private def RootSilentSlot (k : Nat) : Prop :=
  k = emptyRevertSlot ∨ k = bubbleRevertSlot ∨
    k = rootLoopSlot ∨ k = rootContinuationSlot

private theorem silentIn_emptyRevert :
    Func.SilentIn Devm.storageView RootSilentSlot Func.revert := by
  unfold Func.revert
  silent_structure

private theorem silentIn_bubbleRevert :
    Func.SilentIn Devm.storageView RootSilentSlot Func.revertReturnData := by
  unfold Func.revertReturnData
  silent_structure

private theorem silentIn_rootContinuation :
    Func.SilentIn Devm.storageView RootSilentSlot rootContinuation := by
  unfold rootContinuation loadWord mstoreAt
  silent_structure with
    (change RootSilentSlot rootLoopSlot
     simp only [RootSilentSlot, rootLoopSlot, emptyRevertSlot, OfNat.ofNat_ne_one, bubbleRevertSlot,
       Nat.reduceEqDiff, true_or, or_true])

/-- The root loop's SHA-256 crossing is a `STATICCALL`, whose storage
silence is a covered-fork fact, so the loop is silent in each covered
context rather than universally. -/
private theorem silentAt_rootLoop {sevm : Sevm}
    (hfork : CoveredFork sevm.benvStat.fork) :
    Func.SilentAt Devm.storageView sevm RootSilentSlot rootLoop := by
  unfold rootLoop rootLiveStep rootDeadStep rootFinish sha64 loadWord
    mstoreAt storeLe64At returnDataShorterThan returnMemoryRange pushList
  silent_structure with
    first
    | exact fun run => Ninst.staticcall_inv_getStor hfork run
    | (change RootSilentSlot emptyRevertSlot
       simp only [RootSilentSlot, emptyRevertSlot, bubbleRevertSlot, OfNat.one_ne_ofNat,
         rootLoopSlot, rootContinuationSlot, or_self, or_false])
    | (change RootSilentSlot bubbleRevertSlot
       simp only [RootSilentSlot, bubbleRevertSlot, emptyRevertSlot, OfNat.ofNat_ne_one,
         rootLoopSlot, Nat.reduceEqDiff, rootContinuationSlot, or_self, or_false, or_true])
    | (change RootSilentSlot rootContinuationSlot
       simp only [RootSilentSlot, rootContinuationSlot, emptyRevertSlot, OfNat.ofNat_ne_one,
         bubbleRevertSlot, Nat.reduceEqDiff, rootLoopSlot, Nat.succ_ne_self, or_true])

private theorem silentIn_getDepositRoot :
  Func.SilentIn Devm.storageView RootSilentSlot
      (nonpayableEndpoint getDepositRootEndpoint) := by
  unfold nonpayableEndpoint getDepositRootEndpoint mstoreAt Func.revert
  silent_structure with
    first
    | (change RootSilentSlot rootLoopSlot
       simp only [RootSilentSlot, rootLoopSlot, emptyRevertSlot, OfNat.ofNat_ne_one,
         bubbleRevertSlot, Nat.reduceEqDiff, rootContinuationSlot, or_false, or_true])

private theorem rootSilentSlot_closed {sevm : Sevm}
    (hfork : CoveredFork sevm.benvStat.fork) :
    ∀ k g, RootSilentSlot k → (runtime.main :: aux)[k]? = some g →
      Func.SilentAt Devm.storageView sevm RootSilentSlot g := by
  intro k g allowed lookup
  rcases allowed with h | h | h | h
  · subst k
    obtain rfl : Func.revert = g := Option.some.inj
      ((show (runtime.main :: aux)[emptyRevertSlot]? = some Func.revert from rfl).symm.trans
        lookup)
    exact silentIn_emptyRevert.toSilentAt
  · subst k
    obtain rfl : Func.revertReturnData = g := Option.some.inj
      ((show (runtime.main :: aux)[bubbleRevertSlot]? =
          some Func.revertReturnData from rfl).symm.trans lookup)
    exact silentIn_bubbleRevert.toSilentAt
  · subst k
    obtain rfl : rootLoop = g := Option.some.inj
      ((show (runtime.main :: aux)[rootLoopSlot]? = some rootLoop from rfl).symm.trans
        lookup)
    exact silentAt_rootLoop hfork
  · subst k
    obtain rfl : rootContinuation = g := Option.some.inj
      ((show (runtime.main :: aux)[rootContinuationSlot]? =
          some rootContinuation from rfl).symm.trans lookup)
    exact silentIn_rootContinuation.toSilentAt

private def HistoryTargetSound
    (baseline : List B256) (ca : Adr) (f : Func) : Prop :=
  ∀ {sevm : Sevm} {s r : Devm},
    sevm.currentTarget = ca →
    (historySpec baseline).Pre ca sevm s →
    Mem.Wf s.memory →
    NativeShaEntry sevm s →
    s.memory = Mem.empty →
    Func.Run (runtime.main :: aux) sevm s f r →
    (historySpec baseline).Post ca sevm r

private theorem historyTarget_of_core
    {baseline : List B256} {ca : Adr} {f : Func}
    (core : Func.Core (runtime.main :: aux) (HistoryExtends baseline) f) :
    HistoryTargetSound baseline ca f := by
  intro sevm s r target pre _wf _native _memory run
  subst ca
  refine ⟨trivial, ?_⟩
  exact core run (pre.inv.1 rfl)

private theorem supportsInterface_historyTarget
    {baseline : List B256} {ca : Adr} :
    HistoryTargetSound baseline ca
      (nonpayableEndpoint supportsInterfaceEndpoint) := by
  exact historyTarget_of_core supportsInterface_historyCore

private theorem getDepositCount_historyTarget
    {baseline : List B256} {ca : Adr} :
    HistoryTargetSound baseline ca
      (nonpayableEndpoint getDepositCountEndpoint) := by
  exact historyTarget_of_core getDepositCount_historyCore

private theorem getDepositRoot_historyTarget
    {baseline : List B256} {ca : Adr} :
    HistoryTargetSound baseline ca
      (nonpayableEndpoint getDepositRootEndpoint) := by
  intro sevm s r target pre _wf native _memory run
  have storageView := Func.observe_eq_of_run_silentAt
    (rootSilentSlot_closed native.covered) run silentIn_getDepositRoot.toSilentAt
  subst ca
  refine ⟨trivial, ?_⟩
  exact (pre.inv.1 rfl).of_get_eq (fun key =>
    congrFun (congrFun storageView sevm.currentTarget) key)

private theorem deposit_historyTarget
    {baseline : List B256} {ca : Adr} :
    HistoryTargetSound baseline ca depositEndpoint := by
  intro sevm s r target pre _wf native memory run
  subst ca
  refine ⟨trivial, ?_⟩
  exact depositEndpoint_history_success_of_run native memory
    (pre.inv.1 rfl) run

private theorem of_run_branch_revert_fallback
    {fs : List Func} {sevm : Sevm} {s r : Devm} {body : Func}
    (run : Func.Run fs sevm s (body <?> Func.revert) r) :
    ∃ w s', Devm.PopBurn [w] s s' ∧ Func.Run fs sevm s' body r := by
  rcases of_run_branch run with
    ⟨s', _pop, revertRun⟩ |
      ⟨w, _s', s'', _nonzero, pop, burn, bodyRun⟩
  · exact absurd revertRun not_run_revert
  · exact ⟨w, s'', Devm.popBurn_of_popBurn_of_pop pop burn, bodyRun⟩

private def HistoryDispatchState
    (baseline : List B256) (ca : Adr) (sevm : Sevm) (s : Devm) : Prop :=
  sevm.currentTarget = ca ∧
    (historySpec baseline).Pre ca sevm s ∧
    Mem.Wf s.memory ∧
    NativeShaEntry sevm s ∧
    s.memory = Mem.empty

private theorem HistoryDispatchState.of_line
    {baseline : List B256} {ca : Adr} {sevm : Sevm}
    {s s' : Devm} {line : Line}
    (state : HistoryDispatchState baseline ca sevm s)
    (lineRun : Line.Run sevm s line s')
    (code : Line.Inv Devm.getCode line)
    (balance : Line.Inv Devm.getBal line)
    (storage : Line.Inv Devm.getStor line)
    (memory : Line.Inv Devm.memory line) :
    HistoryDispatchState baseline ca sevm s' := by
  rcases state with ⟨target, pre, wf, native, empty⟩
  have codeEq := Line.of_inv Devm.getCode code lineRun
  have memoryEq := Line.of_inv Devm.memory memory lineRun
  have pre' : (historySpec baseline).Pre ca sevm s' :=
    pre.of_eqs
      (congrFun codeEq.symm ca)
      (Line.of_inv Devm.getBal balance lineRun).symm
      (congrFun (Line.of_inv Devm.getStor storage lineRun).symm ca)
  have wf' : Mem.Wf s'.memory := by
    rw [← memoryEq]
    exact wf
  have native' : NativeShaEntry sevm s' := by
    refine ⟨?_, native.precompile, native.covered⟩
    rw [← congrFun codeEq 2]
    exact native.nondelegated
  exact ⟨target, pre', wf', native', memoryEq.symm.trans empty⟩

private theorem HistoryDispatchState.of_popBurn
    {baseline : List B256} {ca : Adr} {sevm : Sevm}
    {s s' : Devm} {popped : Stack}
    (state : HistoryDispatchState baseline ca sevm s)
    (pop : Devm.PopBurn popped s s') :
    HistoryDispatchState baseline ca sevm s' := by
  rcases state with ⟨target, pre, wf, native, empty⟩
  have codeEq : Devm.getCode s = Devm.getCode s' := by
    funext a
    exact getCode_eq_of_state_eq pop.state a
  have native' : NativeShaEntry sevm s' := by
    refine ⟨?_, native.precompile, native.covered⟩
    rw [← congrFun codeEq 2]
    exact native.nondelegated
  have wf' : Mem.Wf s'.memory := by
    rw [← pop.memory]
    exact wf
  exact ⟨target, pre.state_eq pop.state.symm, wf', native',
    pop.memory.symm.trans empty⟩

private theorem HistoryDispatchState.of_burn
    {baseline : List B256} {ca : Adr} {sevm : Sevm}
    {s s' : Devm}
    (state : HistoryDispatchState baseline ca sevm s)
    (burn : Devm.Burn s s') :
    HistoryDispatchState baseline ca sevm s' := by
  rcases state with ⟨target, pre, wf, native, empty⟩
  have codeEq : Devm.getCode s = Devm.getCode s' := by
    funext a
    exact getCode_eq_of_state_eq burn.state a
  have native' : NativeShaEntry sevm s' := by
    refine ⟨?_, native.precompile, native.covered⟩
    rw [← congrFun codeEq 2]
    exact native.nondelegated
  have wf' : Mem.Wf s'.memory := by
    rw [← burn.memory]
    exact wf
  exact ⟨target, pre.state_eq burn.state.symm, wf', native',
    burn.memory.symm.trans empty⟩

private theorem HistoryDispatchState.of_line_popBurn
    {baseline : List B256} {ca : Adr} {sevm : Sevm}
    {s s' s'' : Devm} {line : Line} {popped : Stack}
    (state : HistoryDispatchState baseline ca sevm s)
    (lineRun : Line.Run sevm s line s')
    (pop : Devm.PopBurn popped s' s'')
    (code : Line.Inv Devm.getCode line)
    (balance : Line.Inv Devm.getBal line)
    (storage : Line.Inv Devm.getStor line)
    (memory : Line.Inv Devm.memory line) :
    HistoryDispatchState baseline ca sevm s'' := by
  exact (state.of_line lineRun code balance storage memory).of_popBurn pop

/-- Source soundness for the exact Beacon dispatcher, reduced to the four
endpoint bodies.  The carried selector state retains the native SHA boundary
and fresh memory while allowing the dispatcher to manipulate its stack. -/
private theorem historySpec_sound_of_targets
    {baseline : List B256} {ca : Adr}
    (h_all : ∀ p ∈ funcs, HistoryTargetSound baseline ca p.2) :
    (historySpec baseline).SoundAdmitted ca HistoryEntry := by
  intro sevm pre post _hfork execution run h_ca admitted _ih h_wf h_pre
  have entry : HistoryEntry sevm pre :=
    Exec.HistoryAdmitted.root admitted h_ca
  have statePre : HistoryDispatchState baseline ca sevm pre :=
    ⟨h_ca, h_pre, h_wf, entry.1, entry.2.2⟩
  dsimp only [Prog.Run] at run
  cases run
  rename (_ = _) => h_eq
  rename (Func.Run _ _ _ _ _) => run
  rename (Devm.Burn _ _) => burn
  rename Devm => s₀
  cases h_eq
  have state₀ : HistoryDispatchState baseline ca sevm s₀ :=
    statePre.of_burn burn
  clear statePre entry admitted h_pre h_wf burn pre execution
  refine run_prepend_elim _ [calldatasize] ?_ run
  intro s₁ h₁ run₁
  have state₁ : HistoryDispatchState baseline ca sevm s₁ :=
    state₀.of_line h₁ (by line_inv) (by line_inv) (by line_inv) (by line_inv)
  clear state₀ h₁ run s₀
  obtain ⟨_w, s₂, pop₂, run₂⟩ := of_run_branch_revert_fallback run₁
  have state₂ : HistoryDispatchState baseline ca sevm s₂ :=
    state₁.of_popBurn pop₂
  clear state₁ pop₂ run₁ s₁
  refine run_prepend_elim _ fsig ?_ run₂
  intro s₃ h₃ run₃
  have state₃ : HistoryDispatchState baseline ca sevm s₃ :=
    state₂.of_line h₃ (by line_inv) (by line_inv) (by line_inv) (by line_inv)
  clear state₂ h₃ run₂ s₂
  refine dispatch_inv
    (HistoryDispatchState baseline ca)
    (fun e d => (historySpec baseline).Post ca e d) ?_ ?_ tree ?_
      sevm s₃ post state₃ run₃
  · intro e s x w s' s'' state lineRun pop
    exact state.of_line_popBurn lineRun pop
      (by line_inv) (by line_inv) (by line_inv) (by line_inv)
  · intro e s x w s' s'' state lineRun pop
    exact state.of_line_popBurn lineRun pop
      (by line_inv) (by line_inv) (by line_inv) (by line_inv)
  · intro e s r wf member state targetRun
    exact h_all wf (by
      change DispatchTree.mem tree wf at member
      simpa only [funcs, List.mem_cons, List.not_mem_nil, or_false, tree, DispatchTree.mem] using
        member)
      state.1 state.2.1 state.2.2.1 state.2.2.2.1 state.2.2.2.2 targetRun

/-- The actual four-selector Beacon runtime satisfies its baseline-relative
history specification under trace-local native-SHA and fresh-entry admission. -/
theorem historySpec_sound (baseline : List B256) (ca : Adr) :
    (historySpec baseline).SoundAdmitted ca HistoryEntry := by
  apply historySpec_sound_of_targets
  intro p member
  simp only [funcs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact supportsInterface_historyTarget
  · exact deposit_historyTarget
  · exact getDepositCount_historyTarget
  · exact getDepositRoot_historyTarget

/-- Public open-frame theorem for the exact compiled Beacon dispatcher. -/
theorem historySpec_preserves (baseline : List B256) (ca : Adr) :
    HistoryPreserves baseline ca := by
  exact ContractSpec.preserves_inv_admitted
    (historySpec baseline) ca HistoryEntry (historySpec_sound baseline ca)

end Blanc.BeaconDeposit
