import Blanc.Composition.BuilderRequestPublicObservers
import Blanc.Composition.BuilderRequestCodesKept
import Blanc.Lift.BuilderRequest.Deposit.Delivery
import Blanc.Lift.BuilderRequest.Exit.Delivery
import Blanc.Lift.BuilderRequest.Deposit.ChainLink
import Blanc.Lift.BuilderRequest.Exit.ChainLink
import Blanc.Lift.BuilderRequest.Deposit.FeeDomain
import Blanc.Lift.BuilderRequest.Exit.FeeDomain
import Blanc.Lift.BuilderRequest.FeeDomain
import Blanc.Lift.BuilderRequest.Message
import Blanc.Lift.BuilderRequest.Surplus
import Blanc.Lift.BuilderRequest.ValueKept
import Blanc.Composition.RequestPhaseAmsterdamBase
import Blanc.RequestFeeWordBound

/-!
# Builder request contracts: public guarantees

Featured headlines 1-6 of §17, and O37's value guarantee, which joins them
unnumbered (featured findings 7-8 are in `BuilderRequestPublicFindings`).
History form leads where it exists; the form of each headline is named in its
docstring. The gas bound of O7 lives in the unit layer (`SystemCallOk` shape);
the headline states success. Proofs are thin wrappers over the existing unit
theorems; every bridge is proved.
-/

namespace Blanc.Composition.BuilderRequestPublic

open Jaune Blanc Blanc.Lift.BuilderRequest

/-- A history over the kept forks from a start whose builder codes are installed. -/
structure CodesKept (cfg : ChainConfig) (start : BlockChain)
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
    CodesKept cfg start blocks stop → ∀ benv : Benv,
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
block's request pass over `amsterdamRules.requests` succeeds.
`runRequestContracts`, `BalBuilder` and `amsterdamRules` are read from
`Blanc/Composition/RequestPhaseAmsterdam.lean`. -/
def next_pass_cannot_fail : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock},
    CodesKept cfg start blocks stop →
      BuilderRequestCodesKept.CodesAt start.state →
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
each contract's request bytes are a prefix of its submitted records' bytes, in
order. The end-storage remainder is a unit-layer equation, not restated here. -/
def history_delivers_exactly : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock},
    CodesKept cfg start blocks stop → DeployedStart start → HistoryClean blocks →
    SystemCodeAbsent start → feesPaidAt blocks depositAddr ≤ 2 ^ 256 →
    (exitSubmitted blocks).length ≤ 2 ^ 64 →
    depositRequests blocks <+: (depositSubmitted blocks).flatMap Deposit.contract.out ∧
    exitRequests blocks <+: (exitSubmitted blocks).flatMap Exit.contract.out

/-- No kept system-caller frame carries request data: the latch arm is
unreachable from the request phase. Per-list premise vocabulary for the latch
story; the proved headlines go through the history form. -/
def noLatchData (blocks : List KeptBlock) : Prop :=
  (∀ f ∈ keptAt blocks depositAddr, f.sevm.caller = systemAddress → f.sevm.data = []) ∧
  (∀ f ∈ keptAt blocks exitAddr, f.sevm.caller = systemAddress → f.sevm.data = [])

/-- **Guarantee 4, history form: activation and pre-fork migration.** At the end
of every kept history from deployed storage, each contract's load never exceeds
its submissions. Per-call byte caps live in the unit layer, not restated here. -/
def activation_migrates : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock},
    CodesKept cfg start blocks stop → DeployedStart start → HistoryClean blocks →
    SystemCodeAbsent start → feesPaidAt blocks depositAddr ≤ 2 ^ 256 →
    (exitSubmitted blocks).length ≤ 2 ^ 64 → keptAt blocks exitAddr ≠ [] →
    storedLoad stop.state depositAddr ≤ (depositSubmitted blocks).length ∧
    storedLoad stop.state exitAddr ≤ (exitSubmitted blocks).length

/-- **Guarantee 4, history form: activation at a history's end.** If the exit
contract is still inhibited at the end, the first empty-calldata system call
from there unlocks it; the deposit load never exceeds the submissions. -/
def history_activates : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock},
    CodesKept cfg start blocks stop → DeployedStart start → HistoryClean blocks →
    SystemCodeAbsent start → feesPaidAt blocks depositAddr ≤ 2 ^ 256 →
    storedLoad stop.state depositAddr ≤ (depositSubmitted blocks).length ∧
    (inhibited stop.state exitAddr → ∀ (benv : Benv) (post : State) (out : MsgCallOutput),
      benv.state = stop.state → benv.stat.fork = .amsterdam →
      callIsOk benv exitAddr [] post out → ¬ inhibited post exitAddr)

/-- **Guarantee 5, history form: every accepted deposit is stake funded.** Over
every kept history from deployed storage, every kept 184-byte frame at the
deposit contract carries at least 1 ETH of value, with no cap on the fee. -/
def stake_funded : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    {f : Exec.Frame},
    CodesKept cfg start blocks stop → DeployedStart start → HistoryClean blocks →
    SystemCodeAbsent start → feesPaidAt blocks depositAddr ≤ 2 ^ 256 →
    f ∈ keptAt blocks depositAddr → f.sevm.data.length = 184 →
    oneEth ≤ f.sevm.value.toNat

/-- A valid direct deposit pays the quote at its storage, succeeds, and moves
the full value: the per-contract half of direct use, on the fee's domain. -/
def depositDirectUse : Prop :=
  ∀ {benv : Benv} {bout : BlockOutput} {tx : Tx} {E : Adr} {chainId : UInt64}
    {prio maxFee i f index : Nat}
    (_d : Blanc.Lift.DirectTx benv bout tx E depositAddr chainId prio maxFee i f),
    runsBuilderCode benv.state depositAddr Deposit.code →
    ¬ amsterdamRules.isPrecomp depositAddr → depositAddr ∉ benv.createdAccounts →
    E ≠ systemAddress → tx.data.length = 184 →
    i + 147683 + 783360 + 2300 < tx.gas →
    (benv.state.getStor depositAddr).get 0 ≠ B256.max →
    (storageExcess 8 (benv.state.getStor depositAddr)).toNat ≤ 2892 →
    Deposit.Admits tx.data tx.value.toB256
      (fakeExp 1 (storageExcess 8 (benv.state.getStor depositAddr)).toNat 17).toB256 →
    ((benv.state.getStor depositAddr).get 3).toNat < 2 ^ 253 →
    benv.stat.coinbase ≠ depositAddr →
    ∃ final bout', processTransaction benv bout tx index = .ok (final, bout') ∧
      (final.get depositAddr).bal = (benv.state.get depositAddr).bal + tx.value.toB256

/-- A valid direct exit pays the quote at its storage, succeeds, and moves
the full value: the per-contract half of direct use, on the fee's domain. -/
def exitDirectUse : Prop :=
  ∀ {benv : Benv} {bout : BlockOutput} {tx : Tx} {E : Adr} {chainId : UInt64}
    {prio maxFee i f index : Nat}
    (_d : Blanc.Lift.DirectTx benv bout tx E exitAddr chainId prio maxFee i f),
    runsBuilderCode benv.state exitAddr Exit.code →
    ¬ amsterdamRules.isPrecomp exitAddr → exitAddr ∉ benv.createdAccounts →
    E ≠ systemAddress → tx.data.length = 48 →
    i + 110330 + 489600 + 2300 < tx.gas →
    (benv.state.getStor exitAddr).get 0 ≠ B256.max →
    (storageExcess 2 (benv.state.getStor exitAddr)).toNat ≤ 2892 →
    Exit.Admits tx.data tx.value.toB256
      (fakeExp 1 (storageExcess 2 (benv.state.getStor exitAddr)).toNat 17).toB256 →
    ((benv.state.getStor exitAddr).get 3).toNat < 2 ^ 253 →
    benv.stat.coinbase ≠ exitAddr →
    ∃ final bout', processTransaction benv bout tx index = .ok (final, bout') ∧
      (final.get exitAddr).bal = (benv.state.get exitAddr).bal + tx.value.toB256

/-- **Guarantee 6, transaction form: direct use under Amsterdam.** A valid
direct transaction to either contract, paying the quote read at its storage and
enough gas, succeeds and moves the full value to the contract. -/
def direct_use_succeeds : Prop := depositDirectUse ∧ exitDirectUse

/-- **Value guarantee (O37), history form: the builder contracts' value never falls.**
Over every kept history that started with both builder codes installed, each
builder's balance at the end is at least its balance at the start plus every
value its kept frames carried (`feesPaidAt`: each deposit plus its fee), so it
never falls. At least, never equality: tips and withdrawals can only add. Beyond
the start, the contract sends no transaction, and two virtual certainties no
pinned read answers today: every root message opens on a world whose balances
sum below `2 ^ 256`, and no tip or withdrawal credit to the contract wraps. -/
def value_kept : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock},
    CodesKept cfg start blocks stop → HistoryRootsFit blocks →
    ∀ a ∈ [depositAddr, exitAddr],
      ChainLink.History.NoSender a blocks → HistoryCreditsFit a blocks →
      ((start.state.get a).bal).toNat + feesPaidAt blocks a ≤ ((stop.state.get a).bal).toNat

/-! ## Bridges: each guarantee from its unit theorem -/

/-- History-form success of both builder calls, from the unit totality laws. -/
theorem chain_cannot_halt_bridge : chain_cannot_halt := by
  intro cfg start stop blocks hcodes benv hstate hfork
  have hdep : start.state.getCode depositAddr = Deposit.code := hcodes.deposit
  have hex : start.state.getCode exitAddr = Exit.code := hcodes.exit
  have nedep : (start.state.getCode depositAddr).toList ≠ [] := by
    rw [hdep]
    decide +kernel
  have nddep : ¬ isValidDelegation (start.state.getCode depositAddr) := by
    rw [hdep]
    decide +kernel
  have neex : (start.state.getCode exitAddr).toList ≠ [] := by
    rw [hex]
    decide +kernel
  have ndex : ¬ isValidDelegation (start.state.getCode exitAddr) := by
    rw [hex]
    decide +kernel
  obtain ⟨-, cdep⟩ := hcodes.linked.chain nedep nddep
  obtain ⟨-, cex⟩ := hcodes.linked.chain neex ndex
  have hinstD : benv.state.getCode depositAddr = Deposit.code := by
    rw [hstate, cdep]
    exact hdep
  have hinstE : benv.state.getCode exitAddr = Exit.code := by
    rw [hstate, cex]
    exact hex
  obtain ⟨postD, outD, hrunD, -⟩ := Deposit.system_call_ok hfork hinstD
  obtain ⟨postE, outE, hrunE, -⟩ := Exit.system_call_ok hfork hinstE
  exact ⟨⟨postD, outD, hrunD⟩, ⟨postE, outE, hrunE⟩⟩

/-- The next pass cannot fail, from code persistence and the fold. -/
theorem next_pass_bridge : next_pass_cannot_fail := by
  intro cfg start stop blocks hcodes hfour benv idx acc bal hstate hfork hrules
  obtain ⟨o1, o2, o3, o4, bal', c1, c2, c3, c4, run, -⟩ :=
    BuilderRequestCodesKept.next_pass_succeeds hcodes.linked hfour hstate hfork
      idx acc bal
  exact ⟨_, run⟩

/-- The fold succeeds from any installed storage, from the request phase. -/
theorem fold_bridge : request_fold_succeeds := by
  intro benv idx acc bal hfork hfold hrules
  obtain ⟨o1, o2, o3, o4, bal', c1, c2, c3, c4, run, -⟩ :=
    RequestPhaseAmsterdam.request_phase hfork hfold.w7002 hfold.w7251 hfold.dep
      hfold.ext idx acc bal
  exact ⟨_, run⟩

/-- Exact delivery over a history, from the chain correspondence. -/
theorem history_delivers_bridge : history_delivers_exactly := by
  intro cfg start stop blocks hcodes hdep hclean hsys hbudD hbudE
  have hD := Deposit.history_delivers hcodes.linked hcodes.deposit hdep.depStor
    hsys.code hclean.senders hclean.authorities hclean.creates hbudD
  have hE := Exit.history_delivers hcodes.linked hcodes.exit hdep.exitStor
    hsys.code hclean.senders hclean.authorities hclean.creates hbudE
  exact ⟨hD, hE⟩

/-- Activation bounds, from the excess replay over a history. -/
theorem activation_bridge : activation_migrates := by
  intro cfg start stop blocks hcodes hdep hclean hsys hbudD hfewE hkeptE
  have hD := Deposit.history_excess_bound hcodes.linked hcodes.deposit
    hdep.depStor hsys.code hclean.senders hclean.authorities hclean.creates hbudD
  have hE := Exit.history_excess_bound hcodes.linked hcodes.exit hdep.exitStor
    hsys.code hclean.senders hclean.authorities hclean.creates hfewE hkeptE
  exact ⟨hD, hE⟩

/-- Activation at a history's end, from the system law and the unlock case. -/
theorem history_activates_bridge : history_activates := by
  intro cfg start stop blocks hcodes hdep hclean hsys hbudD
  have hD := Deposit.history_excess_bound hcodes.linked hcodes.deposit
    hdep.depStor hsys.code hclean.senders hclean.authorities hclean.creates hbudD
  refine ⟨hD, ?_⟩
  intro hinh benv post out hstate hfork hrun
  have hex : start.state.getCode exitAddr = Exit.code := hcodes.exit
  have neex : (start.state.getCode exitAddr).toList ≠ [] := by
    rw [hex]
    decide +kernel
  have ndex : ¬ isValidDelegation (start.state.getCode exitAddr) := by
    rw [hex]
    decide +kernel
  obtain ⟨-, cex⟩ := hcodes.linked.chain neex ndex
  have hinst : benv.state.getCode exitAddr = Exit.code := by
    rw [hstate, cex]
    exact hex
  obtain ⟨hpost, -⟩ := Exit.system_law hfork hinst hrun
  have hn : Exit.sysShape.next = excessNext Exit.sysShape.target.word :=
    Exit.contract.next_eq
  have hinh0 : (benv.state.getStor exitAddr).get 0 = B256.max := by
    rw [hstate]
    exact hinh
  have h0 : (post.getStor exitAddr).get 0 = 0 := by
    rw [hpost, Blanc.Lift.RequestSystem.sysState_get_zero, hn, hinh0]
    exact excessNext_inhibitor _ _
  intro hcon
  have hcon0 : (post.getStor exitAddr).get 0 = B256.max := hcon
  rw [h0] at hcon0
  exact absurd hcon0 (by decide)

/-- Stake funding of a kept deposit frame, from the submission law. -/
theorem stake_funded_bridge : stake_funded := by
  intro cfg start stop blocks f hcodes hdep hclean hsys hbud hmem hlen
  obtain ⟨frames, chain, corr, -⟩ := Deposit.history_chain hcodes.linked
    hcodes.deposit hdep.depStor hsys.code hclean.senders hclean.authorities
    hclean.creates
  obtain ⟨xs, ys, hsplit0⟩ := List.mem_iff_append.mp hmem
  have hsplit : ChainLink.History.kept Deposit.contract.address blocks =
      xs ++ f :: ys := hsplit0
  have hcorr : ChainLink.Corresponds Deposit.contract frames (xs ++ f :: ys) := by
    rw [← hsplit]
    exact corr
  obtain ⟨gs, g, hs, rfl, left, m, -⟩ := hcorr.split
  have hlen' : f.sevm.data.length = Deposit.contract.payload := hlen
  have hkev : ChainLink.keptEvent Deposit.contract f =
      .submission (Deposit.contract.recordOf f.sevm hlen') :=
    ChainLink.keptEvent_of_length hlen'
  cases hg : g with
  | submission sevm pre post l i o rules tgt caller law =>
    have hval : sevm.value.toNat ≤ f.sevm.value.toNat := by
      have h := m.value
      rw [hg] at h
      exact h
    have hcr := law.admitted.credited
    have hco := law.admitted.covered
    unfold oneEth
    omega
  | feeRead sevm pre post l i o rules tgt caller law =>
    have h1 := m.event
    rw [hg, hkev] at h1
    change Delivery.Event.feeRead = .submission _ at h1
    cases h1
  | system benv data post out fork installed length run =>
    have h1 := m.event
    rw [hg, hkev] at h1
    change Delivery.Event.system _ = .submission _ at h1
    cases h1

/-- Direct use, from the quoted-domain transaction theorems. -/
theorem direct_use_bridge : direct_use_succeeds := by
  constructor
  · intro benv bout tx E chainId prio maxFee i f index d hinst hpre hnew hcaller
      hlen hgas hoff he hadmit hnoalias hcb
    obtain ⟨entry, hentry, X, used, hX, hu, hrest⟩ :=
      Deposit.transaction_ok_quoted (index := index) d hinst hpre hnew hcaller
        hlen hgas hoff he hadmit hnoalias
    obtain ⟨n, out, hn, hrun, hq, hq'⟩ :=
      RequestFeeWord.fee_run
        (e := storageExcess 8 (benv.state.getStor depositAddr)) he
    have hqnat : (out / (17 : B256)).toNat ≤ (tx.value.toB256).toNat := by
      rw [hq']
      obtain ⟨hcr, hco⟩ := hadmit
      omega
    have hval : tx.value.toB256 ≠ 0 := by
      intro h0
      rw [hq, h0] at hqnat
      have hz : (0 : B256).toNat = 0 := rfl
      rw [hz] at hqnat
      have hpos := RequestFeeWord.fakeExp_pos
        (storageExcess 8 (benv.state.getStor depositAddr)).toNat
      omega
    have hbn := Deposit.submissions.regularBound_le hn
    rw [Deposit.regularBound_462] at hbn
    have hbs : Deposit.submissions.stateBound = 783360 := Deposit.stateBound_eq
    have hg2300 : gCallStipend = 2300 := rfl
    have hgas' : i + Deposit.submissions.regularBound n +
        Deposit.submissions.stateBound + gCallStipend < tx.gas := by omega
    obtain ⟨entryB, st, bout', hproc, hbal, -⟩ :=
      Submissions.transaction_balance (c := Deposit.submissions) (n := n)
        (out := out) d hinst hpre hnew hcaller hval hlen hgas' hoff hrun
        (by rw [hq']; exact hadmit) hnoalias hcb
    exact ⟨_, _, hproc, hbal⟩
  · intro benv bout tx E chainId prio maxFee i f index d hinst hpre hnew hcaller
      hlen hgas hoff he hadmit hnoalias hcb
    obtain ⟨entry, hentry, X, used, hX, hu, hrest⟩ :=
      Exit.transaction_ok_quoted (index := index) d hinst hpre hnew hcaller hlen
        hgas hoff he hadmit hnoalias
    obtain ⟨n, out, hn, hrun, hq, hq'⟩ :=
      RequestFeeWord.fee_run
        (e := storageExcess 2 (benv.state.getStor exitAddr)) he
    have hqnat : (out / (17 : B256)).toNat ≤ (tx.value.toB256).toNat := by
      rw [hq']
      exact hadmit
    have hval : tx.value.toB256 ≠ 0 := by
      intro h0
      rw [hq, h0] at hqnat
      have hz : (0 : B256).toNat = 0 := rfl
      rw [hz] at hqnat
      have hpos := RequestFeeWord.fakeExp_pos
        (storageExcess 2 (benv.state.getStor exitAddr)).toNat
      omega
    have hbn := Exit.submissions.regularBound_le hn
    rw [Exit.regularBound_462] at hbn
    have hbs : Exit.submissions.stateBound = 489600 := Exit.stateBound_eq
    have hg2300 : gCallStipend = 2300 := rfl
    have hgas' : i + Exit.submissions.regularBound n + Exit.submissions.stateBound +
        gCallStipend < tx.gas := by omega
    obtain ⟨entryB, st, bout', hproc, hbal, -⟩ :=
      Submissions.transaction_balance (c := Exit.submissions) (n := n) (out := out)
        d hinst hpre hnew hcaller hval hlen hgas' hoff hrun
        (by rw [hq']; exact hadmit) hnoalias hcb
    exact ⟨_, _, hproc, hbal⟩

/-- The builders' kept value over a history, from the O37 instances. -/
theorem value_kept_bridge : value_kept := by
  intro cfg start stop blocks h fits a ha senders credits
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact (Deposit.history_value h.linked h.deposit senders fits credits).2
  · exact (Exit.history_value h.linked h.exit senders fits credits).2

end Blanc.Composition.BuilderRequestPublic
