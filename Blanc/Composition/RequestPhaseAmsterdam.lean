import Blanc.Composition.RequestPhaseAmsterdamBase
import Blanc.Composition.DepositParse

namespace Blanc.Composition.RequestPhaseAmsterdam

open Jaune
open Blanc (Root TransactionsRoots)
open Blanc.Lift
open Blanc.Lift.RequestSystem
open Blanc.ExecutionTrace (optionalRequestEntry append_optionalRequestEntry)

/-- **The block's request pass under Amsterdam, given that deposit-log parsing succeeded.** Jaune's
`processGeneralPurposeRequestsAt` is `parseDepositRequests` over the block's receipts, then the fold. Given it, and
the fork and the four code installations, with no storage, gas or queue premise, each of the four checked calls returns
at the state the previous one left, and the pass returns the last state. The request list extends the incoming one by
the deposit entry when the parsed bytes are non-empty, ahead of everything the fold appends, then by the type-prefixed
non-empty outputs in rule order. Nothing else in the block output changes but the access list. -/
theorem request_pass_of_parsed {benv : Benv} {bout : BlockOutput} {depositRequests : Bytes}
    (hfork : benv.stat.fork = .amsterdam)
    (h7002 : benv.state.getCode withdrawalRequestPredeployAddress = withdrawalRequestCode)
    (h7251 : benv.state.getCode consolidationRequestPredeployAddress = consolidationRequestCode)
    (hdeposit : benv.state.getCode BuilderRequest.Deposit.Creation.address = BuilderRequest.Deposit.code)
    (hexit : benv.state.getCode BuilderRequest.Exit.Creation.address = BuilderRequest.Exit.code)
    (parsed : parseDepositRequests bout = .ok depositRequests) (idx : Nat) :
    let σ1 := afterWithdrawals benv.state
    let σ2 := afterConsolidations σ1
    let σ3 := afterDeposits σ2
    let σ4 := afterExits σ3
    ∃ (out1 out2 out3 out4 : MsgCallOutput) (bal' : BalBuilder),
      processCheckedSystemTransaction benv withdrawalRequestPredeployAddress [] = .ok (σ1, out1) ∧
      processCheckedSystemTransaction (benv.withState σ1) consolidationRequestPredeployAddress [] =
        .ok (σ2, out2) ∧
      processCheckedSystemTransaction (benv.withState σ2) BuilderRequest.Deposit.Creation.address [] =
        .ok (σ3, out3) ∧
      processCheckedSystemTransaction (benv.withState σ3) BuilderRequest.Exit.Creation.address [] =
        .ok (σ4, out4) ∧
      processGeneralPurposeRequestsAt idx benv bout =
        .ok (σ4, { bout with
          requests := bout.requests ++ optionalRequestEntry 0 depositRequests ++
            optionalRequestEntry 1 out1.returnData ++ optionalRequestEntry 2 out2.returnData ++
            optionalRequestEntry 3 out3.returnData ++ optionalRequestEntry 4 out4.returnData
          bal := bal' }) := by
  intro σ1 σ2 σ3 σ4
  obtain ⟨out1, out2, out3, out4, bal', c1, c2, c3, c4, run, hrules⟩ := request_phase hfork h7002 h7251
    hdeposit hexit idx (bout.requests ++ optionalRequestEntry 0 depositRequests) bout.bal
  refine ⟨out1, out2, out3, out4, bal', c1, c2, c3, c4, ?_⟩
  unfold processGeneralPurposeRequestsAt
  rw [parsed]
  simp only [bind, Except.bind, depositRequestType, append_optionalRequestEntry, hrules]
  rw [run]

/-- **The block's request pass under Amsterdam, without assuming deposit-log parsing.**
Given the block's Amsterdam transaction stage (`TransactionsRoots` over `txs.putIndex` from empty
block output with the deposit contract code installed), followed by withdrawals (`withdrawalsPass`),
deposit-log parsing succeeds unconditionally via `Blanc.Composition.DepositParse.parse_succeeds_amsterdam`,
and the four checked system-contract calls return in rule order. -/
theorem request_pass {benv0 final benv : Benv} {txs : List Tx} {bal0 : BalBuilder}
    {out0 : BlockOutput} {senders : List (Adr × Tx)} {roots : List Root}
    (wds : List Withdrawal)
    (hfork0 : benv0.stat.fork = .amsterdam)
    (hbeacon : benv0.state.getCode depositContractAddress = BeaconDeposit.code)
    (transactions : TransactionsRoots txs.putIndex benv0 { BlockOutput.init with bal := bal0 }
      final out0 senders roots)
    (hfork : benv.stat.fork = .amsterdam)
    (h7002 : benv.state.getCode withdrawalRequestPredeployAddress = withdrawalRequestCode)
    (h7251 : benv.state.getCode consolidationRequestPredeployAddress = consolidationRequestCode)
    (hdeposit : benv.state.getCode BuilderRequest.Deposit.Creation.address = BuilderRequest.Deposit.code)
    (hexit : benv.state.getCode BuilderRequest.Exit.Creation.address = BuilderRequest.Exit.code)
    (idx : Nat) :
    let bout := (withdrawalsPass benv0.stat.rules final out0 wds).2
    let depositRequests := ((roots.flatMap (Root.keptAt depositContractAddress)).flatMap
      Blanc.Corpus.Freeze.Deposit.frameRecords).flatten
    let σ1 := afterWithdrawals benv.state
    let σ2 := afterConsolidations σ1
    let σ3 := afterDeposits σ2
    let σ4 := afterExits σ3
    ∃ (out1 out2 out3 out4 : MsgCallOutput) (bal' : BalBuilder),
      processCheckedSystemTransaction benv withdrawalRequestPredeployAddress [] = .ok (σ1, out1) ∧
      processCheckedSystemTransaction (benv.withState σ1) consolidationRequestPredeployAddress [] =
        .ok (σ2, out2) ∧
      processCheckedSystemTransaction (benv.withState σ2) BuilderRequest.Deposit.Creation.address [] =
        .ok (σ3, out3) ∧
      processCheckedSystemTransaction (benv.withState σ3) BuilderRequest.Exit.Creation.address [] =
        .ok (σ4, out4) ∧
      processGeneralPurposeRequestsAt idx benv bout =
        .ok (σ4, { bout with
          requests := bout.requests ++ optionalRequestEntry 0 depositRequests ++
            optionalRequestEntry 1 out1.returnData ++ optionalRequestEntry 2 out2.returnData ++
            optionalRequestEntry 3 out3.returnData ++ optionalRequestEntry 4 out4.returnData
          bal := bal' }) := by
  have parsed := Blanc.Composition.DepositParse.parse_succeeds_amsterdam
    benv0 txs bal0 final out0 senders roots wds hfork0 hbeacon transactions
  exact request_pass_of_parsed hfork h7002 h7251 hdeposit hexit parsed idx

/-- All four contracts can be installed together in any `State`, so the four installation premises of
`request_phase` are satisfiable. This is about a `State` only: no `Benv` with `stat.fork = .amsterdam` is
constructed here. A `Benv.withState` takes the installed state into any environment and leaves its `stat`
alone, but that step is not a theorem in this file. -/
theorem installations_satisfiable (σ : State) :
    ∃ σ' : State, σ'.getCode withdrawalRequestPredeployAddress = withdrawalRequestCode ∧
      σ'.getCode consolidationRequestPredeployAddress = consolidationRequestCode ∧
      σ'.getCode BuilderRequest.Deposit.Creation.address = BuilderRequest.Deposit.code ∧
      σ'.getCode BuilderRequest.Exit.Creation.address = BuilderRequest.Exit.code := by
  let install (w : State) (a : Adr) (c : ByteArray) : State := w.setPresent a { w.get a with code := c }
  have self : ∀ w a c, (install w a c).getCode a = c := fun w a c => by
    show ((w.setPresent a _).get a).code = c
    rw [State.get_setPresent_self]
  have other : ∀ w a c x, a ≠ x → (install w a c).getCode x = w.getCode x := fun w a c x h => by
    show ((w.setPresent a _).get x).code = _
    rw [State.get_setPresent_ne _ h]
    rfl
  refine ⟨install (install (install (install σ withdrawalRequestPredeployAddress withdrawalRequestCode)
    consolidationRequestPredeployAddress consolidationRequestCode)
    BuilderRequest.Deposit.Creation.address BuilderRequest.Deposit.code)
    BuilderRequest.Exit.Creation.address BuilderRequest.Exit.code, ?_, ?_, ?_, ?_⟩
  · rw [other _ _ _ _ (by decide), other _ _ _ _ (by decide), other _ _ _ _ (by decide), self]
  · rw [other _ _ _ _ (by decide), other _ _ _ _ (by decide), self]
  · rw [other _ _ _ _ (by decide), self]
  · rw [self]

end Blanc.Composition.RequestPhaseAmsterdam
