import Blanc.Lift.Weth9.CommittedSpawn
import Blanc.ExecutionTraceFrames

/-! Raw-entry projection of a genuinely successful WETH9 deposit. -/

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- A successful deposit cannot spawn a child: WETH9's only external node is withdrawal. -/
theorem deposit_rawFrameDescendants {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (installed : sevm.code = code)
    (fork : CoveredFork sevm.benvStat.fork)
    (deposit : decodeCall sevm = some (.deposit sevm.caller sevm.value)) :
    Exec.rawFrameDescendants run = [] := by
  apply Exec.rawFrameDescendants_eq_nil_of_noExec run
  intro node hprefix x atExec
  have withdraw := (weth9_exec_node run installed fork hprefix ⟨x, atExec⟩).1
  rw [deposit] at withdraw
  cases withdraw

/-- The retained raw trace of a successful deposit consists of its actual entered root. -/
theorem deposit_message_rawFrames {msg : Msg}
    {out : Except (EvmError × Jaune.State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) {cevm : Evm}
    (enter : (Frame.ofCall msg).enter = .run cevm) {post : Devm}
    (execution : exec cevm = .ok post) (pcZero : cevm.pc = 0)
    (installed : cevm.sta.code = code) (fork : CoveredFork cevm.sta.benvStat.fork)
    (deposit : decodeCall cevm.sta = some (.deposit cevm.sta.caller cevm.sta.value)) :
    ∃ root, trace.rawFrames = [root] ∧ root.sevm = cevm.sta := by
  rcases trace with ⟨slot, retained, run⟩
  have hrun := run
  unfold ProcessMessage RunFrame at hrun
  rw [enter] at hrun
  obtain ⟨raw, slotEq, -⟩ := hrun
  subst slotEq
  rcases cevm with ⟨pc, sevm, pre⟩
  cases retained with
  | some exn =>
    have rawEq : raw = .ok post := by
      have h := (exec_iff_exec_eq pc sevm pre raw).mp ⟨exn⟩
      rw [← h]
      exact execution
    subst rawEq
    dsimp only at pcZero installed fork deposit
    subst pcZero
    have descendants := deposit_rawFrameDescendants exn installed fork deposit
    exact ⟨⟨0, sevm, pre, .ok post, exn⟩,
      by simp only [ProcessMessageTrace.rawFrames, RetainedXlot.rawFrames,
        Exec.rawFrameRoots, descendants], rfl⟩

/-- The nondelegating settled call wrapper retains the same single deposit root. -/
theorem deposit_call_rawFrames {msg : Msg} {state : Jaune.State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (target : msg.target.isNone = false)
    (auths : msg.tenv.stat.auths.isEmpty = true)
    (nodeleg : getDelegatedCodeAddress msg.code = none) {cevm : Evm}
    (enter : (Frame.ofCall msg).enter = .run cevm) {post : Devm}
    (execution : exec cevm = .ok post) (pcZero : cevm.pc = 0)
    (installed : cevm.sta.code = code) (fork : CoveredFork cevm.sta.benvStat.fork)
    (deposit : decodeCall cevm.sta = some (.deposit cevm.sta.caller cevm.sta.value)) :
    ∃ root, trace.rawFrames = [root] ∧ root.sevm = cevm.sta := by
  cases trace with
  | createCollision htarget => simp only [target, Bool.false_eq_true] at htarget
  | createRun htarget => simp only [target, Bool.false_eq_true] at htarget
  | callRun htarget delegated refund hdelegation execMsg execMsgEq evm core coreTrace result =>
    have delegatedEq : delegated = msg := by
      unfold messageCallDelegation at hdelegation
      simp only [auths, ↓reduceIte] at hdelegation
      exact (Prod.mk.inj (Except.ok.inj hdelegation)).1.symm
    subst delegated
    have execEq : execMsg = msg := by
      rw [execMsgEq]
      simp only [messageCallExecutionMessage, nodeleg]
    subst execEq
    exact deposit_message_rawFrames coreTrace enter execution pcZero installed fork deposit

end Blanc.Lift.Weth9.ClosedInstance
