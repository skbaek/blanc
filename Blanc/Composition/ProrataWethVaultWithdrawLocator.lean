import Blanc.Composition.ProrataWethVaultEnvironment
import Blanc.Composition.ProrataWethVaultWithdrawPayout
import Blanc.FuncMainPrefix
import Blanc.ExecutionPathLocator
import Blanc.CallSpawnExact
import Blanc.PrefixTransport
import Blanc.ExecutionTraceFrames
import Blanc.MessageExecutionInversion

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Composition.ProrataWethVault

/-- The suffix beginning at WETH's value-bearing withdrawal `CALL`. -/
def wethWithdrawCallSuffix : Func :=
  call ::: (logWithdraw <?> Func.revert)

private theorem withdrawLoadCheck_prefix {sevm : Sevm} {s s' : Devm}
    (h : Line.Run sevm s Blanc.withdrawLoadCheck s') :
    Devm.getStor s = Devm.getStor s' ∧
      ∃ less balance,
        ([less, Devm.getStorVal s' sevm.currentTarget sevm.caller.toB256,
            Sevm.argWord sevm 0, Sevm.argWord sevm 0] <<+ s'.stack) ∧
          balance = Devm.getStorVal s' sevm.currentTarget sevm.caller.toB256 ∧
          less = balance <? Sevm.argWord sevm 0 := by
  refine ⟨by invariance, ?_⟩
  revert h
  simp only [Blanc.withdrawLoadCheck]
  line_execute_with (arg 0)
  have hp1 : Sevm.argWord sevm 0 :: [] <<+ s₁.stack :=
    prefix_of_arg nil_pref h₁
  clear h₁
  line_execute 2
  have hp2 : [sevm.caller.toB256, Sevm.argWord sevm 0, Sevm.argWord sevm 0] <<+
      s₂.stack := by
    generalize_line_prefix
  clear hp1 h₂
  line_execute 1
  rcases prefix_of_sload (of_run_singleton h₃) hp2 with
    ⟨balance, hp3, hbalance⟩
  have storage23 : Devm.getStor s₂ = Devm.getStor s₃ :=
    Line.of_inv Devm.getStor (by line_inv) h₃
  clear h₃
  intro h₄
  have hp4 : [balance <? Sevm.argWord sevm 0, balance, Sevm.argWord sevm 0,
      Sevm.argWord sevm 0] <<+ s'.stack := by
    generalize_line_prefix
  have storage34 : Devm.getStor s₃ = Devm.getStor s' :=
    Line.of_inv Devm.getStor (by line_inv) h₄
  have balanceEq : balance =
      Devm.getStorVal s' sevm.currentTarget sevm.caller.toB256 := by
    rw [hbalance]
    show (Devm.getStor s₂ _).get _ = (Devm.getStor s' _).get _
    rw [storage23, storage34]
  refine ⟨balance <? Sevm.argWord sevm 0, balance, ?_, balanceEq, rfl⟩
  · rw [← balanceEq]
    exact hp4

/-- The gas-free part of `sendToCaller` immediately before its `CALL`. -/
def wethWithdrawCallOperands : Line :=
  pushList [0, 0, 0, 0] ++ [swap 3, caller, pushB256 0]

private theorem wethWithdrawCallOperands_prefix {sevm : Sevm} {s sf : Devm}
    {wad : B256} (hp : [wad] <<+ s.stack)
    : Line.Run sevm s wethWithdrawCallOperands sf →
      [0, sevm.caller.toB256, wad, 0, 0, 0, 0] <<+ sf.stack ∧
        s.memory = sf.memory ∧ s.getCode = sf.getCode := by
  line_execute 7
  have stack : [0, sevm.caller.toB256, wad, 0, 0, 0, 0] <<+ s₁.stack := by
    generalize_line_prefix
  intro htail
  cases htail
  exact ⟨stack, Line.of_inv Devm.memory (by line_inv) h₁,
    Line.of_inv Devm.getCode (by line_inv) h₁⟩

/-- The loose gas-free source prefix through WETH's withdrawal `CALL`. -/
theorem weth_withdraw_callHead_prefix {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post))
    (hcode : some sevm.code.toList = Blanc.weth.compile)
    (htarget : sevm.currentTarget = wethAccount)
    (hdirect : sevm.codeAddress = some wethAccount)
    (hcaller : sevm.caller ≠ wethAccount)
    (hsel : Sevm.selector sevm = selector "withdraw" [.uint256])
    (hpre : wethSpec.Pre wethAccount sevm pre)
    (hfresh : Exec.FreshEntry sevm pre) :
    ∃ (entry t : Devm) (target : Prog.SourcePath),
      Devm.Burn pre entry ∧
      Devm.getCode t = Devm.getCode pre ∧
      (0 :: sevm.caller.toB256 :: Sevm.argWord sevm 0 :: 0 :: 0 :: 0 :: 0 ::
        [] <<+ t.stack) ∧
      Devm.getStor t sevm.currentTarget =
        (Devm.getStor pre sevm.currentTarget).set sevm.caller.toB256
          (Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 -
            Sevm.argWord sevm 0) ∧
      Mem.Wf t.memory ∧
      (∀ account, sevm.currentTarget ≠ account →
        Devm.getStor t account = Devm.getStor pre account) ∧
      Devm.getBal t = Devm.getBal pre ∧
      (wethSpec.Pre sevm.currentTarget sevm pre →
        Stor.Solvent (Devm.getStor t sevm.currentTarget) 0
          (Devm.getBal t sevm.currentTarget - Sevm.argWord sevm 0)) ∧
      Func.RunPrefix (weth.main :: weth.aux) sevm ⟨0, []⟩ entry weth.main
        target t wethWithdrawCallSuffix ∧
      Func.Run (weth.main :: weth.aux) sevm t wethWithdrawCallSuffix post := by
  have hrun : Prog.Run sevm pre Blanc.weth post :=
    correct sevm pre Blanc.weth post run hcode
  dsimp only [Prog.Run] at hrun
  cases hrun
  rename (_ = _) => heq
  rename (Func.Run _ _ _ _ _) => sourceRun
  rename (Devm.Burn _ _) => burn
  rename Devm => entry
  cases heq
  rcases dispatch_entry_of_run_mainWith_prefix (path := ⟨0, []⟩) sourceRun with
    ⟨s2, path2, hst2, hmm2, -, -, hpfx, hpre2, hdispatch⟩
  rw [hsel] at hpfx
  have hmem : (selector "withdraw" [.uint256], nonpayable Blanc.withdraw) ∈
      Blanc.wethFuncs := by
    simp [Blanc.wethFuncs]
  rcases dispatchWith_run_prefix_of_sorted_list (path := path2)
      Blanc.wethFuncs_sorted hmem
      hpfx hdispatch with
    ⟨s3, path3, -, hst3, hmm3, hpre3, hwrapped⟩
  rcases run_prefix_nonpayable_logs (path := path3) hwrapped with
    ⟨s4, path4, -, hst4, hmm4, -, -, hpre4, hbody⟩
  simp only [Blanc.withdraw] at hbody
  rcases run_prefix_prepend (l := Blanc.withdrawLoadCheck) (path := path4)
      (by decide) hbody with
    ⟨g1, pathG1, guard, branch, hpre5⟩
  have hgood : ∃ g2 pathG2,
      Devm.PopBurn [0] g1 g2 ∧
      Func.Run (weth.main :: weth.aux) sevm g2
        (sub ::: caller ::: sstore ::: sendToCaller +++ Func.revert.branch logWithdraw) post ∧
      Func.RunPrefix (weth.main :: weth.aux) sevm pathG1 g1
        ((sub ::: caller ::: sstore ::: sendToCaller +++ Func.revert.branch logWithdraw).branch Func.revert)
        pathG2 g2 (sub ::: caller ::: sstore ::: sendToCaller +++ Func.revert.branch logWithdraw) := by
    rcases run_prefix_branch (path := pathG1) branch with
      ⟨g2, pathG2, pop, bodyRun, hpre6⟩ | ⟨less, g2, g3, pathG2, lessNe, pop,
        burnLess, revertRun, hpre6⟩
    · exact ⟨g2, pathG2, pop, bodyRun, hpre6⟩
    · exact absurd revertRun not_run_revert
  rcases hgood with ⟨g2, pathG2, pop, bodyRun, hpre6⟩
  have guardFacts := withdrawLoadCheck_prefix guard
  rcases guardFacts with ⟨guardStorage, less, balance, guardStack, balanceEq, lessEq⟩
  have hp2 : [Devm.getStorVal g1 sevm.currentTarget sevm.caller.toB256,
      Sevm.argWord sevm 0, Sevm.argWord sevm 0] <<+ g2.stack := by
    exact (popBurn_pref pop guardStack).2
  rcases run_prefix_prepend (l := [sub, caller, sstore]) (path := pathG2)
      (by decide) bodyRun with
    ⟨g5, pathG5, debit, sendRun, hpre7⟩
  rcases Line.of_run_cons debit with ⟨g4, subRun, debit⟩
  rcases Line.of_run_cons debit with ⟨g5pre, callerRun, debit⟩
  rcases Line.of_run_cons debit with ⟨g5', storeRun, hnil⟩
  cases hnil
  have hp4 : [sevm.caller.toB256,
      Devm.getStorVal g1 sevm.currentTarget sevm.caller.toB256 -
        Sevm.argWord sevm 0, Sevm.argWord sevm 0] <<+ g5pre.stack := by
    exact prefix_of_push (of_run_caller callerRun)
      (prefix_of_sub subRun hp2)
  have stored := sstore_getStor_set storeRun hp4
  rcases run_prefix_prepend (l := wethWithdrawCallOperands) (path := pathG5)
      (by decide) sendRun with
    ⟨t, pathT, sendLine, callRun, hpre8⟩
  obtain ⟨stack, memory, code⟩ := wethWithdrawCallOperands_prefix
    (prefix_of_sstore storeRun hp4) sendLine
  have storage : Devm.getStor g5 = Devm.getStor t :=
    Line.of_inv Devm.getStor (by line_inv) sendLine
  have popStorage : Devm.getStor g1 = Devm.getStor g2 :=
    funext (fun a => (Devm.PopBurn.getStor pop a).symm)
  have hstorG1 : Devm.getStor g1 sevm.currentTarget =
      Devm.getStor pre sevm.currentTarget := by
    have stateEq : pre.state = s4.state :=
      burn.state.trans (hst2.trans (hst3.trans hst4))
    have rootStorage : Devm.getStor s4 = Devm.getStor pre :=
      funext (getStor_eq_of_state_eq stateEq.symm)
    have rootStorageAt := congrFun rootStorage sevm.currentTarget
    exact (congrFun guardStorage.symm sevm.currentTarget).trans rootStorageAt
  have prefixStorage : Devm.getStor g2 = Devm.getStor g5pre := by
    exact Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons subRun (Line.Run.cons callerRun Line.Run.nil))
  have hstored : Devm.getStor t sevm.currentTarget =
      (Devm.getStor pre sevm.currentTarget).set sevm.caller.toB256
        (Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 -
          Sevm.argWord sevm 0) := by
    have hstorG1all : Devm.getStor g1 = Devm.getStor pre := by
      exact guardStorage.symm.trans
        (funext (getStor_eq_of_state_eq (burn.state.trans
          (hst2.trans (hst3.trans hst4))).symm))
    have preBeforeStore : Devm.getStor g5pre = Devm.getStor pre :=
      prefixStorage.symm.trans
        (popStorage.symm.trans hstorG1all)
    have callerValue :
        Devm.getStorVal g1 sevm.currentTarget sevm.caller.toB256 =
          Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 := by
      exact congrArg (fun st => st.get sevm.caller.toB256) hstorG1
    rw [← storage, stored, preBeforeStore, callerValue]
  have hmemt : Mem.Wf t.memory := by
    have stateEq : pre.state = s4.state :=
      burn.state.trans (hst2.trans (hst3.trans hst4))
    have memS4 : s4.memory = Mem.empty := by
      rw [← hmm4, ← hmm3, ← hmm2, ← burn.memory, hfresh.2]
    have memG1 : s4.memory = g1.memory :=
      Line.of_inv Devm.memory (by line_inv) guard
    have memG2 : g1.memory = g2.memory := pop.memory
    have memG5 : g2.memory = g5pre.memory :=
      Line.of_inv Devm.memory (by line_inv)
        (Line.Run.cons subRun (Line.Run.cons callerRun Line.Run.nil))
    have memStore : g5pre.memory = g5.memory :=
      Line.of_inv Devm.memory (by line_inv) (Line.Run.cons storeRun Line.Run.nil)
    have memT : g5.memory = t.memory := memory
    rw [← memT, ← memStore, ← memG5, ← memG2, ← memG1, memS4]
    exact Mem.wf_empty
  have hbalT : Devm.getBal t = Devm.getBal pre := by
    have stateEq : pre.state = s4.state :=
      burn.state.trans (hst2.trans (hst3.trans hst4))
    have guardBal : Devm.getBal pre = Devm.getBal g2 := by
      exact (funext (getBal_eq_of_state_eq stateEq)).trans
        ((Line.of_inv Devm.getBal (by line_inv) guard).trans
          (funext (getBal_eq_of_state_eq pop.state)))
    have debitBal : Devm.getBal g2 = Devm.getBal g5 :=
      Line.of_inv Devm.getBal (by line_inv)
        (Line.Run.cons subRun (Line.Run.cons callerRun
          (Line.Run.cons storeRun Line.Run.nil)))
    have sendBal : Devm.getBal g5 = Devm.getBal t :=
      Line.of_inv Devm.getBal (by line_inv) sendLine
    exact (guardBal.trans (debitBal.trans sendBal)).symm
  have hforeignT : ∀ account, sevm.currentTarget ≠ account →
      Devm.getStor t account = Devm.getStor pre account := by
    intro account different
    have stateEq : pre.state = s4.state :=
      burn.state.trans (hst2.trans (hst3.trans hst4))
    obtain ⟨pc, registerRun⟩ := of_run_reg storeRun
    have prefixStorage : Devm.getStor g2 = Devm.getStor g5pre := by
      exact Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons subRun (Line.Run.cons callerRun Line.Run.nil))
    rw [← congrFun storage account,
      sstore_preserves_getStor_ne registerRun different,
      ← congrFun prefixStorage account,
      ← congrFun popStorage account,
      ← congrFun guardStorage account,
      ← congrFun (funext (getStor_eq_of_state_eq stateEq)) account]
  have hsolvent : wethSpec.Pre sevm.currentTarget sevm pre →
      Stor.Solvent (Devm.getStor t sevm.currentTarget) 0
        (Devm.getBal t sevm.currentTarget - Sevm.argWord sevm 0) := by
    intro precondition
    have lessZero : (0 : B256) = less := (popBurn_pref pop guardStack).1
    have lessZero' : (0 : B256) = balance <? Sevm.argWord sevm 0 := by
      rw [← lessEq]
      exact lessZero
    have covered : Sevm.argWord sevm 0 ≤ balance := by
      rw [← B256.not_lt]
      intro hlt
      have one : (balance <? Sevm.argWord sevm 0) = 1 := by
        simp [B256.ltCheck, hlt]
      exact B256.zero_ne_one (lessZero'.trans one)
    have debitRun : Line.Run sevm g2
        [Blanc.Ninst.sub, Blanc.Ninst.caller, Blanc.Ninst.sstore] g5 :=
      Line.Run.cons subRun (Line.Run.cons callerRun
        (Line.Run.cons storeRun Line.Run.nil))
    have stateEq : pre.state = s4.state :=
      burn.state.trans (hst2.trans (hst3.trans hst4))
    have guardBal : Devm.getBal pre = Devm.getBal g2 := by
      exact (funext (getBal_eq_of_state_eq stateEq)).trans
        ((Line.of_inv Devm.getBal (by line_inv) guard).trans
          (funext (getBal_eq_of_state_eq pop.state)))
    have guardCode : Devm.getCode pre = Devm.getCode g2 := by
      exact (funext (getCode_eq_of_state_eq stateEq)).trans
        ((Line.of_inv Devm.getCode (by line_inv) guard).trans
          (funext (getCode_eq_of_state_eq pop.state)))
    have atGuard : Precond sevm.currentTarget sevm g2 :=
      precond_of_precond (wethSpec_pre_iff.mp precondition) guardBal
        (popStorage.symm.trans
          (guardStorage.symm.trans
            (funext (getStor_eq_of_state_eq stateEq.symm)))).symm
        guardCode
    have rowAtGuard :
        Devm.getStorVal g1 sevm.currentTarget sevm.caller.toB256 =
          Devm.getStorVal g2 sevm.currentTarget sevm.caller.toB256 := by
      show (Devm.getStor g1 _).get _ = (Devm.getStor g2 _).get _
      rw [popStorage]
    have coveredG1 : Sevm.argWord sevm 0 ≤
        Devm.getStorVal g1 sevm.currentTarget sevm.caller.toB256 := by
      rw [← balanceEq]
      exact covered
    obtain ⟨-, hsv⟩ := solvent_of_withdraw_update_bal atGuard hp2
      rowAtGuard coveredG1 debitRun
    have debitBal : Devm.getBal g2 = Devm.getBal g5 :=
      Line.of_inv Devm.getBal (by line_inv) debitRun
    have sendBal : Devm.getBal g5 = Devm.getBal t :=
      Line.of_inv Devm.getBal (by line_inv) sendLine
    rw [← congrFun storage sevm.currentTarget,
      ← congrFun sendBal sevm.currentTarget]
    exact solvent_of_same_stor hsv rfl rfl
  have stateEq : pre.state = s4.state :=
    burn.state.trans (hst2.trans (hst3.trans hst4))
  have codeS4G1 : Devm.getCode s4 = Devm.getCode g1 :=
    Line.of_inv Devm.getCode (by line_inv) guard
  have codeG1G2 : Devm.getCode g1 = Devm.getCode g2 := by
    funext a
    exact getCode_eq_of_state_eq pop.state a
  have codeG2G5 : Devm.getCode g2 = Devm.getCode g5 :=
    Line.of_inv Devm.getCode (by line_inv)
      (Line.Run.cons subRun (Line.Run.cons callerRun
        (Line.Run.cons storeRun Line.Run.nil)))
  have codePre : Devm.getCode pre = Devm.getCode g5 :=
    (congrArg State.getCode stateEq).trans
      (codeS4G1.trans (codeG1G2.trans codeG2G5))
  have hmain : Func.RunPrefix (weth.main :: weth.aux) sevm
      ⟨0, []⟩ entry weth.main pathT t wethWithdrawCallSuffix :=
    hpre2.trans (hpre3.trans (hpre4.trans
      (hpre5.trans (hpre6.trans (hpre7.trans hpre8)))))
  exact ⟨entry, t, pathT, burn,
    code.symm.trans codePre.symm,
    stack, hstored, hmemt, hforeignT, hbalT, hsolvent, hmain, callRun⟩

/-- The actual WETH `withdraw` execution contains the value-bearing `CALL`
node reached by the loose source prefix.  Its gas operand is the pushed
literal zero, so no gas-sensitive crossing is needed. -/
theorem weth_withdraw_callNode_identity_of_exec {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post))
    (hcode : some sevm.code.toList = Blanc.weth.compile)
    (htarget : sevm.currentTarget = wethAccount)
    (hdirect : sevm.codeAddress = some wethAccount)
    (hcaller : sevm.caller ≠ wethAccount)
    (hsel : Sevm.selector sevm = selector "withdraw" [.uint256])
    (hpre : wethSpec.Pre wethAccount sevm pre)
    (hfresh : Exec.FreshEntry sevm pre) :
    ∃ (node : Exec.NinstOccurrence ⟨0, sevm, pre, .ok post, run⟩),
      node.instruction = call ∧
      Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ node.node ∧
      (0 :: sevm.caller.toB256 :: Sevm.argWord sevm 0 :: 0 :: 0 :: 0 :: 0 ::
        [] <<+ node.node.devm.stack) ∧
      Mem.Wf node.node.devm.memory ∧
      ∃ callPost, node.stepResult = .ok callPost := by
  rcases weth_withdraw_callHead_prefix run hcode htarget hdirect hcaller hsel hpre hfresh with
    ⟨entry, t, target, burn, hcodeT, hstackT, hstorT, hwfT,
      hforeignT, hbalT, hsolvent, hprefix, callRun⟩
  have compiled : some sevm.code.toList = Blanc.weth.compile := hcode
  rcases Exec.Deriv.SourceCursor.mainForward
      (root := ⟨0, sevm, pre, .ok post, run⟩) (program := Blanc.weth)
      rfl compiled rfl with
    ⟨mainCursor, mainReached, actualBurn⟩
  have seed : Devm.EqModGas entry mainCursor.pre :=
    (Devm.EqModGas.refl pre).of_burn burn actualBurn
  rcases mainCursor.ofRunPrefix compiled rfl hprefix seed with
    ⟨callHead, agree, callReached⟩
  unfold wethWithdrawCallSuffix at callHead
  rcases callHead.nextForward rfl with ⟨callCursor, callEdge, callRun⟩
  rcases callRun with ⟨slot, filled, anyPc, stepRun⟩
  have stepRun' := Ninst.stepRun_pc_irrel (n := call) rfl
    (pc' := callHead.pc) stepRun
  have sameFrame : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩
      callHead.node :=
    mainReached.trans callReached
  have reached : callHead.node ∈ Exec.rawNodes run :=
    (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix run _).mpr
      ⟨_, Exec.mem_rawFrameRoots_self run, sameFrame⟩
  have hmem : Mem.Wf callHead.pre.memory := by
    rw [← agree.memory]
    exact hwfT
  have decoded : Ninst.At callHead.node.sevm.code callHead.node.pc call := by
    simpa only [Exec.Deriv.SourceCursor.node] using callHead.ninstAt
  have stepRunNode : Ninst.StepRun callHead.node.pc callHead.node.sevm
      callHead.node.devm call slot (.ok callCursor.pre) := by
    simpa only [Exec.Deriv.SourceCursor.node] using stepRun'
  have hstack : [0, sevm.caller.toB256, Sevm.argWord sevm 0,
      0, 0, 0, 0] <<+ callHead.pre.stack := by
    rw [← agree.stack]
    exact hstackT
  refine ⟨⟨callHead.node, call, slot, .ok callCursor.pre,
    reached, decoded, filled, stepRunNode⟩, rfl, sameFrame, ?_, hmem,
    callCursor.pre, rfl⟩
  change [0, sevm.caller.toB256, Sevm.argWord sevm 0, 0, 0, 0, 0] <<+
    callHead.pre.stack
  rw [← agree.stack]
  exact hstackT

private theorem weth_withdraw_callNode_facts {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post))
    (hcode : some sevm.code.toList = Blanc.weth.compile)
    (htarget : sevm.currentTarget = wethAccount)
    (hdirect : sevm.codeAddress = some wethAccount)
    (hcaller : sevm.caller ≠ wethAccount)
    (hsel : Sevm.selector sevm = selector "withdraw" [.uint256])
    (hpre : wethSpec.Pre wethAccount sevm pre)
    (hfresh : Exec.FreshEntry sevm pre) :
    ∃ (node : Exec.NinstOccurrence ⟨0, sevm, pre, .ok post, run⟩),
      node.instruction = call ∧
      Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ node.node ∧
      (0 :: sevm.caller.toB256 :: Sevm.argWord sevm 0 :: 0 :: 0 :: 0 :: 0 ::
        [] <<+ node.node.devm.stack) ∧
      Mem.Wf node.node.devm.memory ∧
      Devm.getStor node.node.devm sevm.currentTarget =
        (Devm.getStor pre sevm.currentTarget).set sevm.caller.toB256
          (Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 -
            Sevm.argWord sevm 0) ∧
      (∀ account, sevm.currentTarget ≠ account →
        Devm.getStor node.node.devm account = Devm.getStor pre account) ∧
      Devm.getBal node.node.devm = Devm.getBal pre ∧
      Devm.getCode node.node.devm = Devm.getCode pre ∧
      (wethSpec.Pre sevm.currentTarget sevm pre →
        Stor.Solvent (Devm.getStor node.node.devm sevm.currentTarget) 0
          (Devm.getBal node.node.devm sevm.currentTarget - Sevm.argWord sevm 0)) ∧
      ∃ callPost guardPost,
        node.stepResult = .ok callPost ∧
        Devm.PopBurn [1] callPost guardPost ∧
        Devm.getStor post = Devm.getStor callPost ∧
        (∃ (parent child : Devm) (xl : Xlot) (delegated : Bool) (nextAddress : Adr)
          (code : ByteArray) (avail pc : Nat),
          Ninst.StepRun pc sevm node.node.devm Ninst.call xl (.ok callPost) ∧
          0 < sevm.depth ∧
          node.node.devm.stack = 0 :: sevm.caller.toB256 :: Sevm.argWord sevm 0 ::
            0 :: 0 :: 0 :: 0 :: parent.stack ∧
          parent.state = node.node.devm.state ∧
          parent.memory = node.node.devm.memory.extends [(0, 0), (0, 0)] ∧
          parent.logs = node.node.devm.logs ∧ parent.output = node.node.devm.output ∧
          ((getDelegatedCodeAddress (node.node.devm.getCode sevm.caller.toB256.toAdr) = none ∧
              nextAddress = sevm.caller.toB256.toAdr ∧
              code = node.node.devm.getCode sevm.caller.toB256.toAdr ∧ delegated = false) ∨
            (∃ d, getDelegatedCodeAddress
                (node.node.devm.getCode sevm.caller.toB256.toAdr) = some d ∧
              nextAddress = d ∧ code = node.node.devm.getCode d ∧ delegated = true)) ∧
          Xlot.Filled xl ∧
          ProcessMessage
            (callMsg sevm parent
              (min (0 : Nat) (except64th avail) +
                (if (Sevm.argWord sevm 0).toNat = 0 then 0 else gCallStipend))
              (Sevm.argWord sevm 0) sevm.currentTarget sevm.caller.toB256.toAdr
              nextAddress true false
              ((node.node.devm.memory.read 0 0).1) code delegated)
            xl (.ok child) ∧
          child.error.isSome = false ∧
          (Resume.call parent 0 0).run (.ok child) = .ok callPost ∧
          callPost.state = child.state ∧
          callPost.returnData = child.output ∧
          callPost.memory = parent.memory.write 0 (child.output.take 0) ∧
          callPost.stack = (1 : B256) :: parent.stack) := by
  rcases weth_withdraw_callHead_prefix run hcode htarget hdirect hcaller hsel hpre hfresh with
    ⟨entry, t, target, burn, hcodeT, hstackT, hstorT, hwfT,
      hforeignT, hbalT, hsolventT, hprefix, suffixRun⟩
  have compiled : some sevm.code.toList = Blanc.weth.compile := hcode
  rcases Exec.Deriv.SourceCursor.mainForward
      (root := ⟨0, sevm, pre, .ok post, run⟩) (program := Blanc.weth)
      rfl compiled rfl with
    ⟨mainCursor, mainReached, actualBurn⟩
  have seed : Devm.EqModGas entry mainCursor.pre :=
    (Devm.EqModGas.refl pre).of_burn burn actualBurn
  rcases mainCursor.ofRunPrefix compiled rfl hprefix seed with
    ⟨callHead, agree, callReached⟩
  unfold wethWithdrawCallSuffix at callHead
  rcases callHead.nextForward rfl with ⟨callCursor, callEdge, callRun⟩
  have callRun' := callRun
  rcases callRun with ⟨slot, filled, anyPc, stepRun⟩
  have stepRun' := Ninst.stepRun_pc_irrel (n := call) rfl
    (pc' := callHead.pc) stepRun
  have sameFrame : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩
      callHead.node := mainReached.trans callReached
  have reached : callHead.node ∈ Exec.rawNodes run :=
    (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix run _).mpr
      ⟨_, Exec.mem_rawFrameRoots_self run, sameFrame⟩
  have hmem : Mem.Wf callHead.pre.memory := by
    rw [← agree.memory]
    exact hwfT
  have decoded : Ninst.At callHead.node.sevm.code callHead.node.pc call := by
    simpa only [Exec.Deriv.SourceCursor.node] using callHead.ninstAt
  have stepRunNode : Ninst.StepRun callHead.node.pc callHead.node.sevm
      callHead.node.devm call slot (.ok callCursor.pre) := by
    simpa only [Exec.Deriv.SourceCursor.node] using stepRun'
  have hstack : [0, sevm.caller.toB256, Sevm.argWord sevm 0,
      0, 0, 0, 0] <<+ callHead.pre.stack := by
    rw [← agree.stack]
    exact hstackT
  have restRun : Func.Run (weth.main :: weth.aux) sevm callCursor.pre
      (logWithdraw <?> Func.revert) post :=
    correct_core Blanc.weth.main Blanc.weth.aux callCursor.node _ compiled
      callCursor.codeSlice
  rcases of_run_branch restRun with
    ⟨_, _, hrev⟩ | ⟨w, guardPost, returnPre, hw, hpop, hburn, logRun⟩
  · exact (not_run_revert hrev).elim
  rcases of_run_call_val_with_depth_frame (xs := []) hstack callRun' with
    hfailed | hentered
  · exact (hw (popBurn_pref hpop hfailed.1).1).elim
  rcases hentered with
    ⟨parent, child, xl, delegated, nextAddress, childCode, avail, pc, hstep,
      hdepth, hstackEq, hparentState, hparentMemory, hparentLogs,
      hparentOutput, hdelegated, hfilled, hmessage, hclean, hresume,
      hpostState, hpostReturnData, hpostMemory, hpostStack⟩
  have hpop1 : Devm.PopBurn [1] callCursor.pre guardPost := by
    have hpostPrefix : (1 : B256) :: [] <<+ callCursor.pre.stack := by
      rw [hpostStack]
      exact pref_cons nil_pref
    have hwone : w = 1 := (popBurn_pref hpop hpostPrefix).1
    subst w
    exact hpop
  have tailStorage : Devm.getStor callCursor.pre = Devm.getStor post := by
    exact (funext (fun a => (Devm.PopBurn.getStor hpop1 a).symm)).trans
      ((funext (fun a => (Devm.Burn.getStor hburn a).symm)).trans
        (Func.of_inv Devm.getStor Devm.getStor (by
          unfold Blanc.logWithdraw
          func_inv) logRun))
  have hstor : Devm.getStor callHead.pre sevm.currentTarget =
      (Devm.getStor pre sevm.currentTarget).set sevm.caller.toB256
        (Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 -
          Sevm.argWord sevm 0) := by
    exact (getStor_eq_of_state_eq agree.state.symm sevm.currentTarget).trans hstorT
  have hforeign : ∀ account, sevm.currentTarget ≠ account →
      Devm.getStor callHead.pre account = Devm.getStor pre account := by
    intro account different
    exact (getStor_eq_of_state_eq agree.state.symm account).trans
      (hforeignT account different)
  have hbal : Devm.getBal callHead.pre = Devm.getBal pre :=
    (funext (getBal_eq_of_state_eq agree.state.symm)).trans hbalT
  have hcodeNode : Devm.getCode callHead.pre = Devm.getCode pre := by
    exact (congrArg State.getCode agree.state.symm).trans hcodeT
  have hsolvent : wethSpec.Pre sevm.currentTarget sevm pre →
      Stor.Solvent (Devm.getStor callHead.pre sevm.currentTarget) 0
        (Devm.getBal callHead.pre sevm.currentTarget - Sevm.argWord sevm 0) := by
    intro precondition
    apply solvent_of_same_stor (hsolventT precondition)
    · exact (getStor_eq_of_state_eq agree.state.symm sevm.currentTarget).symm
    · exact congrArg (fun b => b - Sevm.argWord sevm 0)
        (getBal_eq_of_state_eq agree.state.symm sevm.currentTarget).symm
  refine ⟨⟨callHead.node, call, slot, .ok callCursor.pre, reached,
    decoded, filled, stepRunNode⟩, rfl, sameFrame, hstack, hmem, hstor,
    hforeign, hbal, hcodeNode, hsolvent, ?_⟩
  refine ⟨callCursor.pre, guardPost, rfl, hpop1, tailStorage.symm, ?_⟩
  exact ⟨parent, child, xl, delegated, nextAddress, childCode, avail, pc,
    hstep, hdepth, hstackEq, hparentState, hparentMemory, hparentLogs,
    hparentOutput, hdelegated, hfilled, hmessage, hclean, hresume,
    hpostState, hpostReturnData, hpostMemory, hpostStack⟩

private theorem retainedRawFrames_eq
    {slot1 slot2 : Xlot}
    {retained1 : ExecutionTrace.RetainedXlot slot1}
    {retained2 : ExecutionTrace.RetainedXlot slot2}
    (slotEq : slot1 = slot2) (retainedEq : HEq retained1 retained2) :
    retained1.rawFrames = retained2.rawFrames := by
  cases slotEq
  exact congrArg (fun retained => retained.rawFrames) (eq_of_heq retainedEq)

private theorem call_settle_clean_transport
    {left right : Msg} {pc : Nat} {sevm : Sevm} {pre child : Devm}
    {raw : Execution}
    (process : ProcessMessage left
      (.some ⟨⟨pc, sevm, pre⟩, raw⟩) (.ok child))
    (clean : child.error.isSome = false) :
    (Frame.ofCall right).settle raw = .ok child := by
  rcases MessageExecution.processMessage_clean_rawPost process clean with
    ⟨rawPost, rawEq, rawClean, stateEq, outputEq⟩
  cases rawEq
  have settled := (RunFrame.some_inv process).2
  have settled' : (Except.ok child : Execution) = Except.ok rawPost := by
    simpa [Frame.ofCall, Frame.settle, Frame.settleMsg,
      executeCode.handleError, processMessage.settle, rawClean] using settled
  have childEq : child = rawPost := Except.ok.inj settled'
  rw [childEq]
  simp [Frame.ofCall, Frame.settle, Frame.settleMsg,
    executeCode.handleError, processMessage.settle, rawClean]

private theorem retained_rawFrames_of_slot
    {xl : Xlot} {retained : ExecutionTrace.RetainedXlot xl}
    {frame : Exec.Frame}
    (slotEq : xl = .some
      ⟨⟨frame.pc, frame.sevm, frame.pre⟩, frame.out⟩) :
    retained.rawFrames = Exec.rawFrameRoots frame.rootDeriv.exc := by
  cases retained with
  | none => cases slotEq
  | @some pc0 sevm0 pre0 out0 childRun =>
      cases slotEq
      exact congrArg Exec.rawFrameRoots (Exec.unique childRun frame.run)

private theorem rawChild_of_spawn
    {nodePc : Nat} {nodeSevm : Sevm} {nodePre : Devm} {nodeOut : Execution}
    (node : Exec nodePc nodeSevm nodePre nodeOut)
    {msg : Msg} {rsm : Resume} {nextPc : Nat}
    {cevm : Evm} {raw : Execution} {child post : Devm}
    (spawn : Evm.step ⟨nodePc, nodeSevm, nodePre⟩ =
      .spawn (Frame.ofCall msg) rsm nextPc)
    (process : ProcessMessage msg (.some ⟨cevm, raw⟩) (.ok child))
    (resumed : rsm.run (.ok child) = .ok post)
    (childRun : Exec cevm.pc cevm.sta cevm.dyna raw) :
    ∃ childRoot : Exec.Deriv,
      childRoot ∈ Exec.rawFrameDescendants node ∧
      Exec.rawFrameRoots childRun = Exec.rawFrameRoots childRoot.exc := by
  obtain ⟨entered, settledEq⟩ := RunFrame.some_inv process
  have resumeRaw : rsm.run ((Frame.ofCall msg).settle raw) = .ok post := by
    rw [← settledEq]
    exact resumed
  obtain ⟨next, nodeEq⟩ :=
    Exec.exists_next_of_run_spawn node spawn entered childRun resumeRaw
  let childRoot : Exec.Deriv := ⟨cevm.pc, cevm.sta, cevm.dyna, raw, childRun⟩
  refine ⟨childRoot, ?_, ?_⟩
  · rw [nodeEq]
    simp [childRoot, Exec.rawFrameDescendants]
  · rfl

theorem wethWithdrawAcceptedPayoutAt_body {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (hcode : some sevm.code.toList = Blanc.weth.compile)
    (htarget : sevm.currentTarget = wethAccount) (hdirect : sevm.codeAddress = some wethAccount)
    (hcaller : sevm.caller ≠ wethAccount) (hsel : Sevm.selector sevm = selector "withdraw" [.uint256])
    (hpre : wethSpec.Pre wethAccount sevm pre) (hfresh : Exec.FreshEntry sevm pre) :
        ∃ split : WethWithdrawSplit sevm pre post,
          ∀ d ∈ split.payout.trace.rawFrames, d ∈ Exec.rawFrameRoots run := by
  rcases weth_withdraw_callNode_facts run hcode htarget hdirect hcaller hsel hpre hfresh with
    ⟨node, isCall, sameFrame, nodeStack, nodeMem, written, foreignKept, callBal,
      callCode, solvent, ⟨callPost, guardPost, stepEq, successPop, after, callFacts⟩⟩
  rcases callFacts with
    ⟨parent, child, xl, delegated, nextAddress, code, avail, pc, hstep,
      hdepth, hstackEq, hparentState, hparentMemory, hparentLogs, hparentOutput,
      hdelegation, hfilled, hmessage, hclean, hresume, hpostState,
      hpostReturnData, hpostMemory, hpostStack⟩
  obtain ⟨retained⟩ := ExecutionTrace.exists_retainedXlot_of_filled hfilled
  let facts : WethWithdrawCallFacts sevm node.node.devm callPost :=
    { xl := xl
      retained := retained
      parent := parent
      child := child
      delegated := delegated
      nextAddress := nextAddress
      code := code
      avail := avail
      pc := pc
      step := hstep
      positive := hdepth
      stack := hstackEq
      parentState := hparentState
      parentMemory := hparentMemory
      parentLogs := hparentLogs
      parentOutput := hparentOutput
      delegation := hdelegation
      filled := hfilled
      processed := hmessage
      clean := hclean
      resume := hresume
      postState := hpostState
      postReturnData := hpostReturnData
      postMemory := hpostMemory
      postStack := hpostStack }
  obtain ⟨split, splitPre, splitPost, traceSlot, traceRetained, traceRun, traceEq⟩ :=
    WethWithdrawSplit.ofCallFacts_pinned htarget hcaller hpre written foreignKept
      facts callBal callCode solvent after
  have retainedFramesEq := retainedRawFrames_eq traceSlot traceRetained
  have rawEq : split.payout.trace.rawFrames = facts.retained.rawFrames := by
    simp only [ExecutionTrace.ProcessMessageTrace.rawFrames]
    exact retainedFramesEq
  refine ⟨split, ?_⟩
  intro d hd
  rw [rawEq] at hd
  cases retained with
  | none =>
      simp [facts, ExecutionTrace.RetainedXlot.rawFrames] at hd
  | some childRun =>
      have sevmEq : node.node.sevm = sevm := sameFrame.sevm_eq
      have acceptedStep' := Ninst.stepRun_pc_irrel (n := call) rfl
        (pc' := node.node.pc) hstep
      have nodeRun := node.stepRun
      rw [isCall, sevmEq] at nodeRun
      obtain ⟨xlEq, outEq⟩ := Step.Run.unique_of_filled hfilled node.filled
        acceptedStep' nodeRun
      have slotEq : node.slot = facts.xl := xlEq.symm
      have evmStep := Evm.step_next (devm := node.node.devm) node.decoded
      rw [isCall, sevmEq] at evmStep
      unfold Ninst.StepRun at nodeRun
      rcases stepEq' : Ninst.step
          ⟨node.node.pc, sevm, node.node.devm⟩ call with
        out | ⟨nextPc, next⟩ | ⟨f, rsm, nextPc⟩ <;> rw [stepEq'] at nodeRun
      · rw [slotEq] at nodeRun
        cases nodeRun.1
      · rw [slotEq] at nodeRun
        cases nodeRun.1
      rcases Ninst.step_call_spawn_exact stepEq' hstackEq with
        ⟨spawnParent, spawnDelegated, spawnAddress, spawnCode, spawnAvail,
          spawnDepth, spawnStack, spawnState, spawnMemory, spawnDelegation,
          frameEq, resumeEq⟩
      rcases nodeRun with ⟨r, frameRun, resultEq⟩
      rw [slotEq] at frameRun
      obtain ⟨msg, frameMsg⟩ : ∃ msg, f = Frame.ofCall msg := ⟨_, frameEq⟩
      subst frameMsg
      have entered := (RunFrame.some_inv frameRun).1
      have frameRun0 := frameRun
      unfold RunFrame at frameRun0
      rw [entered] at frameRun0
      rcases frameRun0 with ⟨raw, slotRaw, settledEq⟩
      cases slotRaw
      have settled := call_settle_clean_transport (right := msg) hmessage hclean
      rw [settled] at settledEq
      subst settledEq
      have process : ProcessMessage msg facts.xl (.ok child) := by
        exact frameRun
      have spawn : Evm.step
          ⟨node.node.pc, node.node.sevm, node.node.devm⟩ =
            .spawn (Frame.ofCall msg) rsm nextPc := by
        rw [sevmEq, evmStep, stepEq']
      have resumed : rsm.run (.ok child) = .ok callPost := by
        rw [← resultEq, stepEq]
      by_cases postClean : post.error = none
      · have rootCommitted : Execution.commits (.ok post) = true := by
          simp [Execution.commits, postClean]
        rcases Exec.NinstOccurrence.exists_root_call_child run rootCommitted node
            sameFrame slotEq spawn process hclean resumed with
          ⟨located, member, entering, parentEq, occurrenceEq, pathEq, locatedSlot⟩
        have frameMember : located.frame ∈ Exec.committedFrames run := by
          rw [← Exec.committedFramePaths_map_frame run]
          exact List.mem_map_of_mem member
        have rootRaw :=
          Exec.mem_rawFrameRoots_of_mem_committedFrames run located.frame frameMember
        have retainedSlot : facts.xl = .some
            ⟨⟨located.frame.pc, located.frame.sevm, located.frame.pre⟩,
              located.frame.out⟩ := slotEq.symm.trans locatedSlot
        have retainedRaw := retained_rawFrames_of_slot
          (retained := facts.retained) retainedSlot
        rw [retainedRaw] at hd
        exact Exec.rawFrameRoots_trans rootRaw hd
      · obtain ⟨childRoot, childMember, retainedRoot⟩ :=
          rawChild_of_spawn node.node.exc spawn process resumed childRun
        have childDesc : childRoot ∈ Exec.rawFrameDescendants run :=
          Exec.mem_rawFrameDescendants_of_parentPrefix sameFrame childMember
        have childRaw : childRoot ∈ Exec.rawFrameRoots run := by
          simp only [Exec.rawFrameRoots, List.mem_cons]
          exact Or.inr childDesc
        change d ∈ childRun.rawFrameRoots at hd
        rw [retainedRoot] at hd
        exact Exec.rawFrameRoots_trans childRaw hd

end Composition.ProrataWethVault

end Blanc
