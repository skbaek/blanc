import Blanc.Composition.RequestPhaseAmsterdamBase
import Blanc.Lift.RequestSystem.Effects

/-!
# The four request contracts under Amsterdam: non-interference and order independence

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

`call_keeps_other_accounts` says each of the four checked system calls leaves every other account exactly as it
was. `fold_order_independent` runs `runRequestContracts` over any reordering of the rule list: it still
returns, and every account ends the same, whatever the storage.

The order claim is about the state only. Two facts bound it. A `State` is a `TreeMap`, whose internal tree can
depend on insertion order, so "the same state" here is agreement at every address, `σ[x]? = σ'[x]?`, which is
everything a lookup can see. And the request bytes do depend on the order: `amsterdamRules.requests` fixes that
order, and `requestsHash` commits to it, so a reordered fold is not a block's fold. Nor is anything claimed
about the `BalBuilder`, or about other activity on a chain: these are statements about the four calls alone.
-/

namespace Blanc.Composition.RequestPhaseAmsterdam

open Jaune
open Blanc.Lift
open Blanc.Lift.RequestSystem

/-- The four contracts' canonical code, in a state. -/
structure Installed (σ : State) : Prop where
  withdrawals : σ.getCode withdrawalRequestPredeployAddress = withdrawalRequestCode
  consolidations : σ.getCode consolidationRequestPredeployAddress = consolidationRequestCode
  deposits : σ.getCode BuilderRequest.Deposit.Creation.address = BuilderRequest.Deposit.code
  exits : σ.getCode BuilderRequest.Exit.Creation.address = BuilderRequest.Exit.code

/-- A system call moves no contract's code. -/
theorem Installed.after {σ : State} (h : Installed σ) (p : SysShape) (a : Adr) :
    Installed (sysState p σ a) where
  withdrawals := (sysState_getCode p σ a _).trans h.withdrawals
  consolidations := (sysState_getCode p σ a _).trans h.consolidations
  deposits := (sysState_getCode p σ a _).trans h.deposits
  exits := (sysState_getCode p σ a _).trans h.exits

/-- Each contract's shape, by address. -/
def shapeOf (a : Adr) : SysShape :=
  if a = withdrawalRequestPredeployAddress then WithdrawalRequest.Amsterdam.sysShape
  else if a = consolidationRequestPredeployAddress then
    SystemExecution.ConsolidationRequest.Amsterdam.sysShape
  else if a = BuilderRequest.Deposit.Creation.address then BuilderRequest.Deposit.sysShape
  else BuilderRequest.Exit.sysShape

/-- Each of the four contracts' checked system call, with its exact post state, at any state holding the four
codes. -/
theorem call_sysState {benv : Benv} (hfork : benv.stat.fork = .amsterdam) (hi : Installed benv.state)
    {e : UInt8 × Adr} (he : e ∈ amsterdamRules.requests) :
    ∃ out, processCheckedSystemTransaction benv e.2 [] =
      .ok (RequestSystem.sysState (shapeOf e.2) benv.state e.2, out) := by
  rw [requests_eq] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · obtain ⟨out, c, -⟩ := WithdrawalRequest.Amsterdam.system_call_ok hfork hi.withdrawals
    exact ⟨out, c⟩
  · exact call7251 (benv := benv) hfork benv.state hi.consolidations
  · exact callDeposit (benv := benv) hfork benv.state hi.deposits
  · exact callExit (benv := benv) hfork benv.state hi.exits

/-- **Non-interference.** Under Amsterdam, with the four canonical codes installed and any storage, each of the
four contracts' checked system calls returns, and changes no other account: each other address reads exactly as
before, present or absent, so in particular its storage is unchanged. -/
theorem call_keeps_other_accounts {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (hi : Installed benv.state) {e : UInt8 × Adr} (he : e ∈ amsterdamRules.requests) :
    ∃ post out, processCheckedSystemTransaction benv e.2 [] = .ok (post, out) ∧
      ∀ x, e.2 ≠ x → post[x]? = benv.state[x]? ∧ post.getStor x = benv.state.getStor x := by
  obtain ⟨out, c⟩ := call_sysState hfork hi he
  exact ⟨_, out, c, fun _ h => ⟨sysState_getElem_ne _ _ h, sysState_getStor_other _ _ h⟩⟩

/-- The four targets are distinct. -/
theorem requests_nodup : (amsterdamRules.requests.map Prod.snd).Nodup := by
  rw [requests_eq]
  decide

/-- **Order independence.** Under Amsterdam, with the four canonical codes installed and any storage, the fold
over any reordering of the rule list returns, and ends with every account exactly as the rule order leaves it.
This is about the post state only: the request bytes follow the order, so a reordered fold yields different
bytes, and the rule list's order is the one a block uses. -/
theorem fold_order_independent {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (hi : Installed benv.state) {l : List (UInt8 × Adr)} (hl : l.Perm amsterdamRules.requests) (idx : Nat)
    (acc : List Bytes) (bal : BalBuilder) :
    ∃ σ acc' bal' τ acc'' bal'', runRequestContracts idx l benv acc bal = .ok (σ, acc', bal') ∧
      runRequestContracts idx amsterdamRules.requests benv acc bal = .ok (τ, acc'', bal'') ∧
      ∀ x : Adr, σ[x]? = τ[x]? := by
  have hcall : ∀ (w : Benv), w.stat.fork = .amsterdam → Installed w.state → ∀ e ∈ amsterdamRules.requests,
      ∃ out, processCheckedSystemTransaction w e.2 [] =
        .ok (RequestSystem.sysState (shapeOf e.2) w.state e.2, out) :=
    fun _ f i _ he => call_sysState f i he
  have hinv : ∀ (w : State) (a : Adr), Installed w →
      Installed (RequestSystem.sysState (shapeOf a) w a) := fun _ _ i => i.after _ _
  obtain ⟨a1, b1, r1⟩ := run_sysFold shapeOf Installed hinv hcall (fun _ h => hl.subset h) hfork hi idx acc bal
  obtain ⟨a2, b2, r2⟩ := run_sysFold shapeOf Installed hinv hcall (l := amsterdamRules.requests) (fun _ h => h)
    hfork hi idx acc bal
  refine ⟨_, a1, b1, _, a2, b2, r1, r2, fun x => ?_⟩
  have hp := hl.map Prod.snd
  rw [sysFold_getElem shapeOf (hp.nodup_iff.mpr requests_nodup), sysFold_getElem shapeOf requests_nodup]
  by_cases hx : x ∈ amsterdamRules.requests.map Prod.snd
  · rw [ite_eq_left hx, ite_eq_left (hp.mem_iff.mpr hx)]
  · rw [ite_eq_right hx, ite_eq_right (fun c => hx (hp.mem_iff.mp c))]

/-- **A real reversal.** The order claim is not an empty one: the reversed list is a reordering, and it is a
different list from the rule list. -/
theorem reverse_is_reordering :
    amsterdamRules.requests.reverse.Perm amsterdamRules.requests ∧
      amsterdamRules.requests.reverse ≠ amsterdamRules.requests := by
  refine ⟨List.reverse_perm _, ?_⟩
  rw [requests_eq]
  decide

end Blanc.Composition.RequestPhaseAmsterdam
