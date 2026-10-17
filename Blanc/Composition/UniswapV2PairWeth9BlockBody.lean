import Blanc.Composition.UniswapV2PairWeth9BlockData
import Blanc.Lift.Weth9.ClosedDeployment
import Blanc.ExecutionTraceSettledOrigin
import Blanc.ExecutionTraceSystemCode
import Blanc.DeploymentMessage

/-!
# The closed instance's block body

`swap_body_of_transactions`: the block body runs when its two transactions run in sequence and the
four system addresses hold the STOP fixture before and after them; the system messages change no
state.  Two trace facts the history assembly uses: a two-transaction fold's traces are those of
its two transactions (`fold_two`), and a STOP system message enters no frame but its own
(`stop_frames`).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.BlockForward Blanc.ExecutionTrace
open Blanc.Lift.Weth9.ClosedInstance (input input_lastHash checkpointHeader systemCode
  systemCode_compile SystemCodes systemAddresses)

/-- **The block body from its two transactions.** -/
theorem swap_body_of_transactions {st s1 s2 : Jaune.State} {bout1 bout2 : BlockOutput}
    (beforeCodes : SystemCodes st) (afterCodes : SystemCodes s2)
    (run1 : processTransaction (input st) BlockOutput.init signedTx1 0 = .ok (s1, bout1))
    (run2 : processTransaction ((input st).withState s1) bout1 signedTx2 1 = .ok (s2, bout2))
    (requests : parseDepositRequests bout2 = .ok []) :
    applyBody (input st) swapTxs [] = .ok (s2, requestsOutput bout2 [] []) := by
  have codeBefore (a : Adr) (ha : a ∈ systemAddresses) :
      some ((input st).state.getCode a).toList = Prog.compile deploymentSystemProgram := by
    change some (st.getCode a).toList = _
    rw [beforeCodes a ha]
    exact systemCode_compile
  have codeAfter (a : Adr) (ha : a ∈ systemAddresses) :
      some (((input st).withState s2).state.getCode a).toList =
        Prog.compile deploymentSystemProgram := by
    change some (s2.getCode a).toList = _
    rw [afterCodes a ha]
    exact systemCode_compile
  obtain ⟨outBeacon, beacon, -⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
    (input st) beaconRootsAddress (input st).stat.parentBeaconBlockRoot.toBytes
    (codeBefore _ (by decide +kernel))
    (by change ¬ Fork.bpo2.ruleSet.isPrecomp beaconRootsAddress; decide +kernel) CoveredFork.bpo2
  obtain ⟨outHistory, history, -⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
    (input st) historyStorageAddress (checkpointHeader st).hash.toBytes
    (codeBefore _ (by decide +kernel))
    (by change ¬ Fork.bpo2.ruleSet.isPrecomp historyStorageAddress; decide +kernel)
    CoveredFork.bpo2
  obtain ⟨outW, runW, _, _, _, _, returnW⟩ := processCheckedSystemTransaction_deploymentSystemProgram
    ((input st).withState s2) withdrawalRequestPredeployAddress []
    (codeAfter _ (by decide +kernel))
    (by change ¬ Fork.bpo2.ruleSet.isPrecomp withdrawalRequestPredeployAddress; decide +kernel)
    CoveredFork.bpo2
  obtain ⟨outC, runC, _, _, _, _, returnC⟩ := processCheckedSystemTransaction_deploymentSystemProgram
    ((input st).withState s2) consolidationRequestPredeployAddress []
    (codeAfter _ (by decide +kernel))
    (by change ¬ Fork.bpo2.ruleSet.isPrecomp consolidationRequestPredeployAddress; decide +kernel)
    CoveredFork.bpo2
  have fold : applyTransactions [signedTx1, signedTx2].putIndex (input st) BlockOutput.init =
      .ok ((input st).withState s2, bout2) := by
    change applyTransactions [(0, signedTx1), (1, signedTx2)] (input st) BlockOutput.init = _
    simp only [applyTransactions, run1, run2, bind, Except.bind]
    rfl
  have same : (input st).withState (input st).state = input st := rfl
  have samePost : ((input st).withState s2).withState ((input st).withState s2).state =
      (input st).withState s2 := rfl
  have body := applyBody_forward (txs := swapTxs) (stHistory := (input st).state)
    CoveredFork.bpo2 beacon (input_lastHash st)
    (by rw [same]; exact history) (txList := [signedTx1, signedTx2]) rfl
    (by rw [same, same]; exact fold) requests runW (by rw [samePost]; exact runC)
  rw [returnW, returnC] at body
  exact body

/-- **A two-transaction fold is its two transactions**: from a fold over `[(0, T1), (1, T2)]` whose
start environment is `B0` and whose two transactions run in sequence, its retained traces are
those of two transaction traces of exactly those runs, and it ends in the second's state. -/
theorem fold_two {txs : List (Nat × Tx)} {B B0 finalB : Benv} {finalBout : BlockOutput}
    (t : ApplyTransactionsTrace txs B BlockOutput.init finalB finalBout) (hB : B = B0)
    {T1 T2 : Tx} {s1 s2 : Jaune.State} {bout1 bout2 : BlockOutput}
    (htxs : txs = [(0, T1), (1, T2)])
    (run1 : processTransaction B0 BlockOutput.init T1 0 = .ok (s1, bout1))
    (run2 : processTransaction (B0.withState s1) bout1 T2 1 = .ok (s2, bout2)) :
    ∃ (t1 : TransactionTrace B0 BlockOutput.init T1 0 s1 bout1)
      (t2 : TransactionTrace (B0.withState s1) bout1 T2 1 s2 bout2),
      t.rawFrames = t1.rawFrames ++ t2.rawFrames ∧
      t.settledFrames = t1.settledFrames ++ t2.settledFrames ∧ finalB.state = s2 := by
  subst hB htxs
  cases t with
  | cons head tail =>
    have e1 := head.result.symm.trans run1
    simp only [Except.ok.injEq, Prod.mk.injEq] at e1
    obtain ⟨rfl, rfl⟩ := e1
    cases tail with
    | cons head2 tail2 =>
      have e2 := head2.result.symm.trans run2
      simp only [Except.ok.injEq, Prod.mk.injEq] at e2
      obtain ⟨rfl, rfl⟩ := e2
      cases tail2 with
      | nil =>
        exact ⟨head, head2,
          by simp only [ApplyTransactionsTrace.rawFrames, List.append_nil],
          by simp only [ApplyTransactionsTrace.settledFrames, List.append_nil], rfl⟩

/-- **A STOP system message enters no frame but its own**, raw or settled. -/
theorem stop_frames {benv : Benv} {target : Adr} {data : Bytes} {state : Jaune.State}
    {out : MsgCallOutput} (trace : SystemMessageTrace benv target data state out)
    (code : benv.state.getCode target = systemCode) :
    (∀ root ∈ trace.rawFrames, root.sevm.currentTarget = target) ∧
      (∀ f ∈ trace.settledFrames, f.sevm.currentTarget = target) := by
  have raw := trace.rawFrames_target_of_code
    (by rw [code]; exact spawnFreeReach_of_check (by decide +kernel))
    (by rw [code]; decide +kernel)
  exact ⟨raw, fun f member => raw _ (trace.mem_rawFrames_of_mem_settledFrames f member)⟩

end Blanc.Composition.UniswapV2PairWeth9Instance
