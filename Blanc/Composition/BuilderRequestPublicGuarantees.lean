import Blanc.Composition.BuilderRequestPublicObservers
import Blanc.Lift.BuilderRequest.Deposit.Delivery
import Blanc.Lift.BuilderRequest.Exit.Delivery
import Blanc.Composition.RequestPhaseAmsterdam

/-!
# Builder request contracts: public guarantees

Featured headlines 1-6 of §17. History form leads where it exists; the form of
each headline is named in its docstring. The gas bound of O7 lives in the unit
layer (`SystemCallOk` shape); the headline states success. Proofs are thin
wrappers over the existing unit theorems; every bridge that is not yet written
is a `sorry` with a `-- DRAFT:` note naming the lemma it needs.
-/

namespace Blanc.Composition.BuilderRequestPublic

open Jaune Blanc Blanc.Lift.BuilderRequest

/-- A history over the kept forks from a start whose builder codes are installed. -/
structure CodesKept {cfg : ChainConfig} (start : BlockChain)
    (blocks : List KeptBlock) (stop : BlockChain) : Prop where
  /-- The blocks link the start to the stop. -/
  linked : Blanc.KeptHistory cfg start blocks stop
  /-- The deposit contract runs its code at the start. -/
  deposit : runsBuilderCode start.state depositAddr Deposit.code
  /-- The exit contract runs its code at the start. -/
  exit : runsBuilderCode start.state exitAddr Exit.code

/-- The four request contracts' code at a call's environment. -/
structure FoldInstalled (benv : Benv) : Prop where
  /-- EIP-7002's code is installed. -/
  w7002 : benv.state.getCode withdrawalRequestPredeployAddress =
    Blanc.withdrawalRequestCode
  /-- EIP-7251's code is installed. -/
  w7251 : benv.state.getCode consolidationRequestPredeployAddress =
    Blanc.consolidationRequestCode
  /-- The deposit code is installed. -/
  dep : runsBuilderCode benv.state depositAddr Deposit.code
  /-- The exit code is installed. -/
  ext : runsBuilderCode benv.state exitAddr Exit.code

/-- **Guarantee 1, history form: the builder system calls cannot halt the chain.**
At the end of every kept history that started with both builder codes installed,
each builder's checked system call with empty calldata succeeds. -/
def chain_cannot_halt : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock},
    CodesKept start blocks stop → ∀ benv : Benv,
      benv.state = stop.state → benv.stat.fork = .amsterdam →
      (∃ post out, callIsOk benv depositAddr [] post out) ∧
      (∃ post out, callIsOk benv exitAddr [] post out)

/-- **Guarantee 1, per-call form: each builder call succeeds from any storage.**
Under Amsterdam with the code installed, the checked system call with empty
calldata succeeds whatever the storage holds. -/
def system_call_succeeds : Prop :=
  ∀ (benv : Benv), benv.stat.fork = .amsterdam →
    runsBuilderCode benv.state depositAddr Deposit.code →
    runsBuilderCode benv.state exitAddr Exit.code →
    (∃ post out, callIsOk benv depositAddr [] post out) ∧
    (∃ post out, callIsOk benv exitAddr [] post out)

/-- **Guarantee 2, history form: the next request pass cannot fail.** At the end
of every kept history that started with all four codes installed, the next
block's request pass over `amsterdamRules.requests` succeeds. -/
-- DRAFT: `runRequestContracts`, `BalBuilder` and `amsterdamRules` are read from
-- `Blanc/Composition/RequestPhaseAmsterdam.lean`; their homes (Jaune-level) are
-- confirmed at compile time.
def next_pass_cannot_fail : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock},
    CodesKept start blocks stop → FourCodes start →
    ∀ (benv : Benv) (idx : Nat) (acc : List Bytes) (bal : BalBuilder),
      benv.state = stop.state → benv.stat.fork = .amsterdam →
      benv.stat.rules.requests = amsterdamRules.requests →
      ∃ r, runRequestContracts idx amsterdamRules.requests benv acc bal = .ok r

/-- **Guarantee 2, per-call form: the four-contract request fold.** Under
Amsterdam with all four codes installed, the fold over `amsterdamRules.requests`
succeeds and its bytes are the type-prefixed outputs in rule order. -/
def request_fold_succeeds : Prop :=
  ∀ (benv : Benv) (idx : Nat) (acc : List Bytes) (bal : BalBuilder),
    benv.stat.fork = .amsterdam → FoldInstalled benv →
    benv.stat.rules.requests = amsterdamRules.requests →
    ∃ r, runRequestContracts idx amsterdamRules.requests benv acc bal = .ok r

/-- **Guarantee 3, history form: exact delivery.** Over every kept history from
deployed storage with no system-caller, authority or created-address frames,
each contract's request bytes are a prefix of its submitted records' bytes, and
the end storage holds exactly the rest, in order. -/
def history_delivers_exactly : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock},
    CodesKept start blocks stop → DeployedStart start → HistoryClean blocks →
    depositRequests blocks <+: ((depositSubmitted blocks).map Deposit.contract.out).flatten ∧
    exitRequests blocks <+: ((exitSubmitted blocks).map Exit.contract.out).flatten ∧
    storedQueueLen stop.state depositAddr = (depositSubmitted blocks).length - (depositRequests blocks).length / 184 ∧
    storedQueueLen stop.state exitAddr = (exitSubmitted blocks).length - (exitRequests blocks).length / 68

/-- No kept system-caller frame carries request data: the latch arm is
unreachable from the request phase. -/
def noLatchData (blocks : List KeptBlock) : Prop :=
  (∀ f ∈ keptAt blocks depositAddr, f.sevm.caller = systemAddress → f.sevm.data = []) ∧
  (∀ f ∈ keptAt blocks exitAddr, f.sevm.caller = systemAddress → f.sevm.data = [])

/-- **Guarantee 3, list form: exact delivery over kept frames.** The same
equations over kept-frame lists with direct per-frame premises (no system-caller
frames carrying request data), without the history linkage. -/
def sequence_delivers_exactly : Prop :=
  ∀ {start stop : BlockChain} {blocks : List KeptBlock},
    DeployedStart start → HistoryClean blocks → noLatchData blocks →
    depositRequests blocks <+: ((depositSubmitted blocks).map Deposit.contract.out).flatten ∧
    exitRequests blocks <+: ((exitSubmitted blocks).map Exit.contract.out).flatten ∧
    storedQueueLen stop.state depositAddr = (depositSubmitted blocks).length - (depositRequests blocks).length / 184 ∧
    storedQueueLen stop.state exitAddr = (exitSubmitted blocks).length - (exitRequests blocks).length / 68

/-- **Guarantee 4, list form: activation and pre-fork migration.** From deployed
storage, the end load never exceeds the submissions, and each contract's
delivered bytes fit its per-call cap times its system calls (64 for deposits,
16 for exits). The latch arm is unreachable: system frames carry empty data. -/
def activation_migrates : Prop :=
  ∀ {start stop : BlockChain} {blocks : List KeptBlock},
    DeployedStart start → HistoryClean blocks → noLatchData blocks →
    storedLoad stop.state depositAddr ≤ (depositSubmitted blocks).length ∧
    (depositRequests blocks).length ≤ 184 * (64 * sysCallCount blocks depositAddr) ∧
    (exitRequests blocks).length ≤ 68 * (16 * sysCallCount blocks exitAddr)

/-- **Guarantee 4, history form: activation at a history's end.** If the exit
contract is still inhibited at the end, the first empty-calldata system call
from there unlocks it; the deposit load never exceeds the submissions. -/
def history_activates : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock},
    CodesKept start blocks stop → DeployedStart start → HistoryClean blocks →
    storedLoad stop.state depositAddr ≤ (depositSubmitted blocks).length ∧
    (inhibited stop.state exitAddr → ∀ (benv : Benv) (post : State) (out : MsgCallOutput),
      benv.state = stop.state → benv.stat.fork = .amsterdam →
      callIsOk benv exitAddr [] post out → ¬ inhibited post exitAddr)

/-- **Guarantee 5, frame form: every accepted deposit is stake funded.** Every
kept 184-byte frame at the deposit contract carries at least 1 ETH of value,
with no cap on the fee it may quote. -/
def stake_funded : Prop :=
  ∀ {blocks : List KeptBlock} {f : Exec.Frame}, f ∈ keptAt blocks depositAddr →
    f.sevm.data.length = 184 → oneEth ≤ f.sevm.value.toNat

/-- A valid direct deposit pays the quote at its storage, succeeds, and moves
the full value: the per-contract half of direct use. -/
def depositDirectUse : Prop :=
  ∀ {benv : Benv} {bout : BlockOutput} {tx : Tx} {E : Adr} {chainId : UInt64}
    {prio maxFee i f index : Nat}
    (d : Blanc.Lift.DirectTx benv bout tx E depositAddr chainId prio maxFee i f),
    tx.data.length = 184 → (benv.state.getStor depositAddr).get 0 ≠ B256.max →
    fakeExp 1 (storedExcess benv.state depositAddr +
      (storedCount benv.state depositAddr - 8)) 17 ≤ tx.value.toNat →
    ∃ final bout', processTransaction benv bout tx index = .ok (final, bout') ∧
      (final.get depositAddr).bal.toNat = (benv.state.get depositAddr).bal.toNat + tx.value.toNat

/-- A valid direct exit pays the quote at its storage, succeeds, and moves
the full value: the per-contract half of direct use. -/
def exitDirectUse : Prop :=
  ∀ {benv : Benv} {bout : BlockOutput} {tx : Tx} {E : Adr} {chainId : UInt64}
    {prio maxFee i f index : Nat}
    (d : Blanc.Lift.DirectTx benv bout tx E exitAddr chainId prio maxFee i f),
    tx.data.length = 48 → (benv.state.getStor exitAddr).get 0 ≠ B256.max →
    fakeExp 1 (storedExcess benv.state exitAddr +
      (storedCount benv.state exitAddr - 2)) 17 ≤ tx.value.toNat →
    ∃ final bout', processTransaction benv bout tx index = .ok (final, bout') ∧
      (final.get exitAddr).bal.toNat = (benv.state.get exitAddr).bal.toNat + tx.value.toNat

/-- **Guarantee 6, transaction form: direct use under Amsterdam.** A valid
direct transaction to either contract, paying the quote read at its storage and
enough gas, succeeds and moves the full value to the contract. -/
def direct_use_succeeds : Prop := depositDirectUse ∧ exitDirectUse

/-! ## Bridges: each guarantee from its unit theorem -/

/-- History-form success of the deposit system call, from its unit law. -/
theorem chain_cannot_halt_deposit : chain_cannot_halt := by
  -- DRAFT: `codes_persist` (Accepts.lean) keeps the code to `stop`, then the
  -- deposit `system_law` (Deposit/Delivery.lean) gives success from any storage.
  sorry

/-- History-form success of the exit system call, from its unit law. -/
theorem chain_cannot_halt_exit : chain_cannot_halt := by
  -- DRAFT: as above with the exit `system_law` (Exit/Delivery.lean).
  sorry

/-- The next pass cannot fail, from code persistence and the fold. -/
theorem next_pass_bridge : next_pass_cannot_fail := by
  -- DRAFT: `next_pass_succeeds` (Accepts.lean) applied to `codes_persist`;
  -- the EIP-7002/7251 pair stays a premise there as in `FourCodes` here.
  sorry

/-- The fold succeeds from any installed storage, from the request phase. -/
theorem fold_bridge : request_fold_succeeds := by
  -- DRAFT: `request_phase` (RequestPhaseAmsterdam.lean) with the four
  -- installation premises; any-storage totality for EIP-7002/7251 is O9's.
  sorry

/-- Exact delivery over a history, from the chain correspondence. -/
theorem history_delivers_bridge : history_delivers_exactly := by
  -- DRAFT: `history_delivery` (ChainLink.lean) for each contract's `Linked`,
  -- via `history_chain`; needs the `Placed`/`Linked` instances (Deposit and
  -- Exit ChainLink files) and the deployed-storage `Represents`.
  sorry

/-- Activation bounds, from the replay and drain lemmas. -/
theorem activation_bridge : activation_migrates := by
  -- DRAFT: per-call caps from `replay_calls_excess`/`drained_length`
  -- (Delivery.lean, Flood.lean); the load bound from `Chain.delivered`.
  sorry

/-- Activation at a history's end, from the system law and the unlock case. -/
theorem history_activates_bridge : history_activates := by
  -- DRAFT: deposit part as `activation_bridge` via `history_chain`; exit part
  -- from the exit `system_law` with `excessNext_inhibitor` at slot 0.
  sorry

/-- Stake funding of a kept deposit frame, from the submission law. -/
theorem stake_funded_bridge : stake_funded := by
  -- DRAFT: `Frame.ofKept` (ChainLink.lean) turns the kept frame into a delivery
  -- `Frame`; the deposit `Contract.paid` field gives value covering the fee,
  -- and the submission law gives the 1 ETH floor and 184-byte shape.
  sorry

/-- Direct use, from the transaction theorem. -/
theorem direct_use_bridge : direct_use_succeeds := by
  -- DRAFT: `transaction_ok` (Transaction.lean) for each contract's
  -- `Submissions` instance; the quote premise here is its `admit` at the
  -- natural fee, and the balance equation is its value-move conclusion.
  sorry

end Blanc.Composition.BuilderRequestPublic
