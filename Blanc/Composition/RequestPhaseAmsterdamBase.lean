import Blanc.Lift.WithdrawalRequest.AmsterdamSystem
import Blanc.Lift.SystemExecution.ConsolidationRequest.AmsterdamSystem
import Blanc.Lift.BuilderRequest.Deposit.SystemCall
import Blanc.Lift.BuilderRequest.Exit.SystemCall
import Blanc.Lift.RequestSystem.Output
import Blanc.RequestsOutput

/-!
# The Amsterdam request-contract fold over all four contracts

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

`request_phase` says: under Amsterdam, with the canonical EIP-7002, EIP-7251, EIP-8282 deposit and EIP-8282
exit runtimes installed, and any storage in all of them, the fold over `amsterdamRules.requests` cannot fail.
Its state is the fourth call's, and its bytes extend the incoming list by each call's return data, prefixed
with the contract's type byte, in rule order, leaving out each empty return.

Each call's `.ok` is stated at the state the previous call left, so nothing here assumes the calls commute.
A call changes only its own slots (`sysState`), so every later call still sees its code
(`sysState_getCode`). This is a statement about Jaune's semantics. It says nothing about what the queues
hold or what a block's transactions did, and nothing about the receipt-derived deposit requests, which
Jaune appends ahead of this fold.
-/

namespace Blanc.Composition.RequestPhaseAmsterdam

open Jaune
open Blanc.Lift
open Blanc.Lift.RequestSystem
open Blanc.ExecutionTrace (optionalRequestEntry append_optionalRequestEntry)

/-- The EIP-7002 call's post state. -/
abbrev afterWithdrawals (σ : State) : State :=
  sysState WithdrawalRequest.Amsterdam.sysShape σ withdrawalRequestPredeployAddress

/-- The EIP-7251 call's post state. -/
abbrev afterConsolidations (σ : State) : State :=
  sysState SystemExecution.ConsolidationRequest.Amsterdam.sysShape σ consolidationRequestPredeployAddress

/-- The EIP-8282 deposit call's post state. -/
abbrev afterDeposits (σ : State) : State :=
  sysState BuilderRequest.Deposit.sysShape σ BuilderRequest.Deposit.Creation.address

/-- The EIP-8282 exit call's post state. -/
abbrev afterExits (σ : State) : State :=
  sysState BuilderRequest.Exit.sysShape σ BuilderRequest.Exit.Creation.address

/-- The rule list, as the four contracts. -/
theorem requests_eq : amsterdamRules.requests =
    [(1, withdrawalRequestPredeployAddress), (2, consolidationRequestPredeployAddress),
      (3, BuilderRequest.Deposit.Creation.address), (4, BuilderRequest.Exit.Creation.address)] := rfl

/-- The EIP-7251 call at any state holding its code. -/
theorem call7251 {benv : Benv} (hfork : benv.stat.fork = .amsterdam) (σ : State)
    (h : σ.getCode consolidationRequestPredeployAddress = consolidationRequestCode) :
    ∃ out, processCheckedSystemTransaction (benv.withState σ) consolidationRequestPredeployAddress [] =
      .ok (afterConsolidations σ, out) :=
  let ⟨out, c, _⟩ := SystemExecution.ConsolidationRequest.Amsterdam.system_call_ok
    (benv := benv.withState σ) hfork h
  ⟨out, c⟩

/-- The EIP-8282 deposit call at any state holding its code. -/
theorem callDeposit {benv : Benv} (hfork : benv.stat.fork = .amsterdam) (σ : State)
    (h : σ.getCode BuilderRequest.Deposit.Creation.address = BuilderRequest.Deposit.code) :
    ∃ out, processCheckedSystemTransaction (benv.withState σ) BuilderRequest.Deposit.Creation.address [] =
      .ok (afterDeposits σ, out) :=
  let ⟨out, c, _⟩ := BuilderRequest.Deposit.system_call_state (benv := benv.withState σ) hfork h
  ⟨out, c⟩

/-- The EIP-8282 exit call at any state holding its code. -/
theorem callExit {benv : Benv} (hfork : benv.stat.fork = .amsterdam) (σ : State)
    (h : σ.getCode BuilderRequest.Exit.Creation.address = BuilderRequest.Exit.code) :
    ∃ out, processCheckedSystemTransaction (benv.withState σ) BuilderRequest.Exit.Creation.address [] =
      .ok (afterExits σ, out) :=
  let ⟨out, c, _⟩ := BuilderRequest.Exit.system_call_state (benv := benv.withState σ) hfork h
  ⟨out, c⟩

/-- Four returning calls, each at the state the last left, are the fold's run. -/
theorem fold_of_calls {benv : Benv} {σ1 σ2 σ3 σ4 : State} {out1 out2 out3 out4 : MsgCallOutput}
    (idx : Nat) (acc : List Bytes) (bal : BalBuilder)
    (c1 : processCheckedSystemTransaction benv withdrawalRequestPredeployAddress [] = .ok (σ1, out1))
    (c2 : processCheckedSystemTransaction (benv.withState σ1) consolidationRequestPredeployAddress [] =
      .ok (σ2, out2))
    (c3 : processCheckedSystemTransaction (benv.withState σ2) BuilderRequest.Deposit.Creation.address [] =
      .ok (σ3, out3))
    (c4 : processCheckedSystemTransaction (benv.withState σ3) BuilderRequest.Exit.Creation.address [] =
      .ok (σ4, out4)) :
    ∃ bal', runRequestContracts idx amsterdamRules.requests benv acc bal =
      .ok (σ4, acc ++ optionalRequestEntry 1 out1.returnData ++
        optionalRequestEntry 2 out2.returnData ++ optionalRequestEntry 3 out3.returnData ++
        optionalRequestEntry 4 out4.returnData, bal') := by
  have w : ∀ a b, (benv.withState a).withState b = benv.withState b := fun _ _ => rfl
  rw [requests_eq, runRequestContracts_step c1, runRequestContracts_step c2, w,
    runRequestContracts_step c3, w, runRequestContracts_step c4, w, runRequestContracts]
  simp only [append_optionalRequestEntry]
  exact ⟨_, rfl⟩

/-- **The Amsterdam request-contract fold succeeds, from any storage.** The fold is `runRequestContracts`
over the rule list a block uses (the last conjunct ties `benv.stat.rules.requests` to
`amsterdamRules.requests`). It is the four system calls of Jaune's `processGeneralPurposeRequests`, and not
all of that function: `processGeneralPurposeRequests` first runs `parseDepositRequests` on the block's
receipts, and that step fails on a malformed deposit log. Nothing here says it succeeds. The only premises
are the fork and the four code installations: no storage, gas or queue premise. Each of the four checked
system calls returns, at the state the previous one left, and the fold returns the last state, with the
incoming list extended by the type-prefixed non-empty outputs in rule order. -/
theorem request_phase {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (h7002 : benv.state.getCode withdrawalRequestPredeployAddress = withdrawalRequestCode)
    (h7251 : benv.state.getCode consolidationRequestPredeployAddress = consolidationRequestCode)
    (hdeposit : benv.state.getCode BuilderRequest.Deposit.Creation.address = BuilderRequest.Deposit.code)
    (hexit : benv.state.getCode BuilderRequest.Exit.Creation.address = BuilderRequest.Exit.code)
    (idx : Nat) (acc : List Bytes) (bal : BalBuilder) :
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
      runRequestContracts idx amsterdamRules.requests benv acc bal =
        .ok (σ4, acc ++ optionalRequestEntry 1 out1.returnData ++
          optionalRequestEntry 2 out2.returnData ++ optionalRequestEntry 3 out3.returnData ++
          optionalRequestEntry 4 out4.returnData, bal') ∧
      benv.stat.rules.requests = amsterdamRules.requests := by
  intro σ1 σ2 σ3 σ4
  have k1 : ∀ x, σ1.getCode x = benv.state.getCode x := sysState_getCode _ _ _
  have k2 : ∀ x, σ2.getCode x = σ1.getCode x := sysState_getCode _ _ _
  have k3 : ∀ x, σ3.getCode x = σ2.getCode x := sysState_getCode _ _ _
  have i2 : σ1.getCode consolidationRequestPredeployAddress = consolidationRequestCode := by
    rw [k1, h7251]
  have i3 : σ2.getCode BuilderRequest.Deposit.Creation.address = BuilderRequest.Deposit.code := by
    rw [k2, k1, hdeposit]
  have i4 : σ3.getCode BuilderRequest.Exit.Creation.address = BuilderRequest.Exit.code := by
    rw [k3, k2, k1, hexit]
  obtain ⟨out1, c1, -⟩ := WithdrawalRequest.Amsterdam.system_call_ok hfork h7002
  obtain ⟨out2, c2⟩ := call7251 hfork σ1 i2
  obtain ⟨out3, c3⟩ := callDeposit hfork σ2 i3
  obtain ⟨out4, c4⟩ := callExit hfork σ3 i4
  obtain ⟨bal', run⟩ := fold_of_calls idx acc bal c1 c2 c3 c4
  exact ⟨out1, out2, out3, out4, bal', c1, c2, c3, c4, run, by rw [amsterdam_rules hfork]⟩

end Blanc.Composition.RequestPhaseAmsterdam
