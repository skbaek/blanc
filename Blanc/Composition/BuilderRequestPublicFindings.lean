import Blanc.Composition.BuilderRequestPublicObservers
import Blanc.Composition.BuilderRequestPublicGuarantees
import Blanc.Lift.BuilderRequest.Deposit.Delivery
import Blanc.Lift.BuilderRequest.Exit.Delivery
import Blanc.Lift.BuilderRequest.Deposit.ChainLink
import Blanc.Lift.BuilderRequest.Exit.ChainLink
import Blanc.Lift.BuilderRequest.Deposit.Latch
import Blanc.Lift.BuilderRequest.Exit.Latch
import Blanc.Lift.BuilderRequest.Balances
import Blanc.Lift.BuilderRequest.Progress
import Blanc.Lift.BuilderRequest.Accepts

/-!
# Builder request contracts: public findings

Featured findings 7-8 and the bounds-and-context headlines of §17-§19 that are
frame or list statements: the reversible kill switch, the exit's caller
authentication, the locked surplus, what the contracts accept, fee reads as
used, and the contract-interaction facts. History form leads where it exists;
each headline names its form. Fee reads succeed under `STATICCALL` too (the
unit fee-read walks take no staticness premise); a submission under `STATICCALL`
fails at its first store, which the unit layer states and this layer does not
repeat. Every bridge is proved; the one deleted draft statement
(`history_never_latches`) is reported to the master, not restated here.
-/

namespace Blanc.Composition.BuilderRequestPublic

open Jaune Blanc Blanc.Lift Blanc.Lift.BuilderRequest

/-- One contract's latch cycle: a nonempty-data system call drains yet keeps the
inhibitor, and the next empty call clears it. -/
def latchCycle (a : Adr) (code : ByteArray) : Prop :=
  ∀ (benv : Benv) (data : Bytes) (post : State) (out : MsgCallOutput),
    benv.stat.fork = .amsterdam → runsBuilderCode benv.state a code →
    data ≠ [] → data.length < 2 ^ 256 →
    callIsOk benv a data post out → (post.getStor a).get 0 = B256.max ∧
    ∀ (post2 : State) (out2 : MsgCallOutput),
      callIsOk (benv.withState post) a [] post2 out2 →
      (post2.getStor a).get 0 = 0

/-- **Finding 7, list form: the kill switch is reversible.** A system call with
nonempty calldata drains as with empty calldata and leaves slot 0 at the
inhibitor; the next empty-calldata call moves it to 0, against the EIP text's
"permanently". -/
def kill_switch_reversible : Prop :=
  latchCycle depositAddr Deposit.code ∧ latchCycle exitAddr Exit.code

/-- One contract's unlock: an inhibited empty system call clears excess and
count. -/
def unlockClears (a : Adr) (code : ByteArray) : Prop :=
  ∀ (benv : Benv) (post : State) (out : MsgCallOutput),
    benv.stat.fork = .amsterdam → runsBuilderCode benv.state a code →
    (benv.state.getStor a).get 0 = B256.max →
    callIsOk benv a [] post out →
    (post.getStor a).get 0 = 0 ∧ (post.getStor a).get 1 = 0

/-- **Unlock finding, list form: the unlock resets the fee to 1 wei.** After an
inhibited system call the cleared storage quotes 1 wei whatever the backlog was. -/
def unlock_resets_fee : Prop :=
  unlockClears depositAddr Deposit.code ∧ unlockClears exitAddr Exit.code ∧
  fakeExp 1 0 17 = 1

/-- **Exit authentication, history form: a delivered exit's source is its
submitter.** Every exit record a kept history's frames submitted records exactly
the caller of the frame that submitted it, with the frame's calldata as its key.
Per-frame content: no history premise is needed, so none is stated. -/
def history_exit_source_is_caller : Prop :=
  ∀ {blocks : List KeptBlock} {f : Exec.Frame} {r : Exit.Record},
    f ∈ keptAt blocks exitAddr → ChainLink.submittedBy Exit.contract f = some r →
    r.source = f.sevm.caller ∧ r.pubkey = f.sevm.data

/-- **Exit authentication, list form.** Over a bare kept-frame list, each mapped
exit record's source is the caller of the frame that submitted it. -/
def sequence_exit_source_is_caller : Prop :=
  ∀ {fs : List Exec.Frame} {f : Exec.Frame} {r : Exit.Record},
    f ∈ fs → ChainLink.submittedBy Exit.contract f = some r →
    r.source = f.sevm.caller ∧ r.pubkey = f.sevm.data

/-- The deposit contract accepts a passing 184-byte payload, under Amsterdam. -/
def depositSubmitAccepts : Prop :=
  ∀ {sevm : Sevm} {b : Devm} {M : Mem} {G n : Nat} {out : B256},
    sevm.code = Deposit.code → sevm.benvStat.fork = .amsterdam →
    sevm.caller ≠ systemAddress → sevm.data.length = 184 → sevm.isStatic = false →
    gCallStipend < G → b.getStorVal sevm.currentTarget 0 ≠ B256.max →
    WordFakeExponential.Run (Blanc.Lift.BuilderRequest.storedExcess 8 sevm b) 17 1 17 0 n out → Deposit.Admitted sevm (out / (17 : B256)) →
    Nonempty (Exec 0 sevm (St b [] M (G + Deposit.submissionGasA sevm b M n))
      (.ok (Deposit.submissionPostA sevm (Deposit.feeBaseA sevm b) M
        (G + Deposit.submissionRepayA sevm b M))))

/-- The deposit contract reverts a rejected 184-byte payload, under Amsterdam. -/
def depositSubmitRejects : Prop :=
  ∀ {s : Sevm} {b : Devm} {n : Nat} {out : B256},
    s.code = Deposit.code → s.benvStat.fork = .amsterdam →
    s.caller ≠ systemAddress → s.data.length = 184 →
    b.getStorVal s.currentTarget 0 ≠ B256.max →
    WordFakeExponential.Run (Blanc.Lift.BuilderRequest.storedExcess 8 s b) 17 1 17 0 n out →
    ¬ Deposit.Admits s.data s.value (out / (17 : B256)) → FrameReverts s b (revertBound n)

/-- The exit contract accepts a funded 48-byte payload, under Amsterdam. -/
def exitSubmitAccepts : Prop :=
  ∀ {sevm : Sevm} {b : Devm} {M : Mem} {G n : Nat} {out : B256},
    sevm.code = Exit.code → sevm.benvStat.fork = .amsterdam →
    sevm.caller ≠ systemAddress → sevm.data.length = 48 → sevm.isStatic = false →
    gCallStipend < G → b.getStorVal sevm.currentTarget 0 ≠ B256.max →
    WordFakeExponential.Run (Blanc.Lift.BuilderRequest.storedExcess 2 sevm b) 17 1 17 0 n out → (out / (17 : B256)).toNat ≤ sevm.value.toNat →
    Nonempty (Exec 0 sevm (St b [] M (G + Exit.submissionGasA sevm b M n))
      (.ok (Exit.submissionPostA sevm (Exit.feeBaseA sevm b) M
        (G + Exit.submissionRepayA sevm b M))))

/-- The exit contract reverts an underfunded 48-byte payload, under Amsterdam. -/
def exitSubmitRejects : Prop :=
  ∀ {s : Sevm} {b : Devm} {n : Nat} {out : B256},
    s.code = Exit.code → s.benvStat.fork = .amsterdam →
    s.caller ≠ systemAddress → s.data.length = 48 →
    b.getStorVal s.currentTarget 0 ≠ B256.max →
    WordFakeExponential.Run (Blanc.Lift.BuilderRequest.storedExcess 2 s b) 17 1 17 0 n out →
    ¬ Exit.Admits s.data s.value (out / (17 : B256)) → FrameReverts s b (revertBound n)

/-- A plain value transfer reverts at a contract: empty calldata with nonzero
value is a paid fee read. -/
def transferRevertsAt (code : ByteArray) (target : B256) : Prop :=
  ∀ {s : Sevm} {b : Devm} {n : Nat} {out : B256}, s.code = code →
    s.benvStat.fork = .amsterdam → s.caller ≠ systemAddress →
    b.getStorVal s.currentTarget 0 ≠ B256.max →
    WordFakeExponential.Run (Blanc.Lift.BuilderRequest.storedExcess target s b) 17 1 17 0 n out →
    s.data = [] → s.value ≠ 0 → FrameReverts s b (revertBound n)

/-- A plain value transfer reverts at either contract, under Amsterdam. -/
def transfersRevert : Prop :=
  transferRevertsAt Deposit.code 8 ∧ transferRevertsAt Exit.code 2

/-- **What the contracts accept, frame form.** Any 184-byte deposit payload
passing the amount and value guards is accepted whatever its pubkey, credentials
and signature; any caller can queue an exit for any pubkey paying the fee; a
plain value transfer reverts. -/
def accepts_plainly : Prop :=
  depositSubmitAccepts ∧ depositSubmitRejects ∧ exitSubmitAccepts ∧ exitSubmitRejects ∧ transfersRevert

/-- One contract's fee read: off the inhibitor, empty calldata and zero value
run a successful frame returning exactly the 32-byte quote, changing no
storage, balance or logs. -/
def feeReadWorks (_a : Adr) (code : ByteArray) (target : B256) : Prop :=
  ∀ {sevm : Sevm} {b : Devm} {M : Mem} {G n : Nat} {out : B256},
    sevm.code = code → sevm.benvStat.fork = .amsterdam →
    M.size % 32 = 0 → Mem.Wf M → sevm.caller ≠ systemAddress →
    sevm.data = [] → sevm.value = 0 →
    b.getStorVal sevm.currentTarget 0 ≠ B256.max →
    WordFakeExponential.Run (Blanc.Lift.BuilderRequest.storedExcess target sevm b) 17 1 17 0 n out →
    ∃ post, Nonempty (Exec 0 sevm
        (St b [] M (G + UserPath.feeReadGasOn (amsterdamSteps sevm) b M n))
        (.ok post)) ∧
      post.output = (out / (17 : B256)).toBytes ∧
      (∀ x : Adr, post.getStor x = b.getStor x) ∧
      (∀ x : Adr, post.getBal x = b.getBal x) ∧ post.logs = b.logs

/-- **Fee reads as used, frame form.** Off the inhibitor with zero value and
empty calldata, a frame returns exactly the 32-byte quote and changes no
storage and no logs. -/
def fee_reads_as_used : Prop :=
  feeReadWorks depositAddr Deposit.code 8 ∧ feeReadWorks exitAddr Exit.code 2

/-- **Quote against charge, kept-frame form.** Over a kept history from deployed
storage, a kept submission frame's value covers the natural fee of the storage
it found, on either contract, with at most 2892 submissions before it. The
later-quote dynamics live in the unit layer. -/
def quote_against_charge : Prop :=
  (∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    {xs ys : List Exec.Frame} {f : Exec.Frame},
    CodesKept cfg start blocks stop → DeployedStart start → HistoryClean blocks →
    SystemCodeAbsent start → keptAt blocks depositAddr = xs ++ f :: ys →
    (xs.filterMap (ChainLink.submittedBy Deposit.contract)).length ≤ 2892 →
    f.sevm.data.length = 184 →
    ChainLink.naturalFee Deposit.contract f ≤ f.sevm.value.toNat) ∧
  (∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    {xs ys : List Exec.Frame} {f : Exec.Frame},
    CodesKept cfg start blocks stop → DeployedStart start → HistoryClean blocks →
    SystemCodeAbsent start → keptAt blocks exitAddr = xs ++ f :: ys →
    (xs.filterMap (ChainLink.submittedBy Exit.contract)).length ≤ 2892 →
    f.sevm.data.length = 48 →
    ChainLink.naturalFee Exit.contract f ≤ f.sevm.value.toNat)

/-- **Output lengths, per-call form.** Each builder's system call returns
`returnData` whose length is a multiple of the record size, at most cap records,
with no representation premise. -/
def output_lengths_capped : Prop :=
  (∀ (benv : Benv) (data : Bytes) (post : State) (out : MsgCallOutput),
    benv.stat.fork = .amsterdam → runsBuilderCode benv.state depositAddr Deposit.code →
    callIsOk benv depositAddr data post out →
    out.returnData.length % 184 = 0 ∧ out.returnData.length ≤ 64 * 184) ∧
  (∀ (benv : Benv) (data : Bytes) (post : State) (out : MsgCallOutput),
    benv.stat.fork = .amsterdam → runsBuilderCode benv.state exitAddr Exit.code →
    callIsOk benv exitAddr data post out →
    out.returnData.length % 68 = 0 ∧ out.returnData.length ≤ 16 * 68)

/-- One contract's surplus: a checked system call moves no balance. -/
def callKeepsBalances (a : Adr) (code : ByteArray) : Prop :=
  ∀ (benv : Benv) (data : Bytes) (post : State) (out : MsgCallOutput),
    benv.stat.fork = .amsterdam → runsBuilderCode benv.state a code →
    data.length < 2 ^ 256 → callIsOk benv a data post out →
    ∀ x : Adr, (post.get x).bal = (benv.state.get x).bal

/-- **Locked surplus, per-call form: the bytes keep what they are paid.** A
checked system call changes no account's balance. With direct use, a submission
raises the contract's balance by exactly the full value it carried. -/
def surplus_locked : Prop :=
  callKeepsBalances depositAddr Deposit.code ∧ callKeepsBalances exitAddr Exit.code

/-- One contract's system call leaves another account's storage untouched. -/
def callLocalTo (a other : Adr) (code : ByteArray) : Prop :=
  ∀ (benv : Benv) (data : Bytes) (post : State) (out : MsgCallOutput),
    benv.stat.fork = .amsterdam → runsBuilderCode benv.state a code →
    callIsOk benv a data post out → post.getStor other = benv.state.getStor other

/-- One contract's system call leaves every code untouched. -/
def callKeepsCode (a : Adr) (code : ByteArray) : Prop :=
  ∀ (benv : Benv) (data : Bytes) (post : State) (out : MsgCallOutput),
    benv.stat.fork = .amsterdam → runsBuilderCode benv.state a code →
    callIsOk benv a data post out → ∀ x : Adr, post.getCode x = benv.state.getCode x

/-- **Non-interference, per-call form.** A builder's system call changes no
storage but its own contract's, and leaves every code untouched. The fold's
order-independence is proved at the unit layer, not stated here. -/
def calls_do_not_interfere : Prop :=
  callLocalTo depositAddr exitAddr Deposit.code ∧ callLocalTo exitAddr depositAddr Exit.code ∧
  callKeepsCode depositAddr Deposit.code ∧ callKeepsCode exitAddr Exit.code

/-! ## Bridges -/

/-- The latch cycle, from the latch specification. -/
theorem kill_switch_bridge : kill_switch_reversible := by
  constructor
  · intro benv data post out hfork hinst hne hlen hrun
    obtain ⟨out0, out0', h1, hmax, h2, hgas, h0⟩ :=
      Deposit.latch_cycle hfork hinst hne hlen
    have hrunE : processCheckedSystemTransaction benv Deposit.Creation.address
        data = .ok (post, out) := hrun
    rw [hrunE, Except.ok.injEq, Prod.mk.injEq] at h1
    obtain ⟨hpost, -⟩ := h1
    rw [hpost]
    refine ⟨hmax, ?_⟩
    intro post2 out2 hrun2
    have hrun2E : processCheckedSystemTransaction
        (benv.withState (latchState Deposit.sysShape benv.state
          Deposit.Creation.address)) Deposit.Creation.address [] =
        .ok (post2, out2) := hrun2
    rw [hrun2E, Except.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨hpost2, -⟩ := h2
    rw [hpost2]
    exact h0
  · intro benv data post out hfork hinst hne hlen hrun
    obtain ⟨out0, out0', h1, hmax, h2, hgas, h0⟩ :=
      Exit.latch_cycle hfork hinst hne hlen
    have hrunE : processCheckedSystemTransaction benv Exit.Creation.address
        data = .ok (post, out) := hrun
    rw [hrunE, Except.ok.injEq, Prod.mk.injEq] at h1
    obtain ⟨hpost, -⟩ := h1
    rw [hpost]
    refine ⟨hmax, ?_⟩
    intro post2 out2 hrun2
    have hrun2E : processCheckedSystemTransaction
        (benv.withState (latchState Exit.sysShape benv.state
          Exit.Creation.address)) Exit.Creation.address [] =
        .ok (post2, out2) := hrun2
    rw [hrun2E, Except.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨hpost2, -⟩ := h2
    rw [hpost2]
    exact h0

/-- The unlock quote, from the cleared-storage reading. -/
theorem unlock_fee_bridge : unlock_resets_fee := by
  refine ⟨?_, ?_, ?_⟩
  · intro benv post out hfork hinst hinh hrun
    exact deposit_unlock_clears hfork hinst hinh hrun
  · intro benv post out hfork hinst hinh hrun
    exact exit_unlock_clears hfork hinst hinh hrun
  · exact FakeExponential.value_zero_numerator 1 17 (by decide)

/-- Exit source authentication, from the record projection. -/
theorem exit_source_bridge : sequence_exit_source_is_caller := by
  intro fs f r hmem hsub
  unfold ChainLink.submittedBy at hsub
  split at hsub
  · next h =>
    obtain rfl := Option.some_inj.mp hsub
    exact ⟨rfl, rfl⟩
  · next h => cases hsub

/-- Exit source authentication over a history's kept frames. -/
theorem history_exit_source_bridge : history_exit_source_is_caller := by
  intro blocks f r hmem hsub
  exact exit_source_bridge hmem hsub

/-- The surplus is locked, from the system-call balance law. -/
theorem surplus_bridge : surplus_locked := by
  constructor
  · intro benv data post out hfork hinst hlen hrun x
    obtain ⟨hd, -⟩ := system_calls_keep_balances hfork hlen
    obtain ⟨post', out', hrun', hbal⟩ := hd hinst
    have hrunE : processCheckedSystemTransaction benv depositAddr data =
        .ok (post, out) := hrun
    rw [hrunE, Except.ok.injEq, Prod.mk.injEq] at hrun'
    obtain ⟨rfl, rfl⟩ := hrun'
    exact hbal x
  · intro benv data post out hfork hinst hlen hrun x
    obtain ⟨-, hd⟩ := system_calls_keep_balances hfork hlen
    obtain ⟨post', out', hrun', hbal⟩ := hd hinst
    have hrunE : processCheckedSystemTransaction benv exitAddr data =
        .ok (post, out) := hrun
    rw [hrunE, Except.ok.injEq, Prod.mk.injEq] at hrun'
    obtain ⟨rfl, rfl⟩ := hrun'
    exact hbal x

/-- What the contracts accept, from the submission and revert laws. -/
theorem accepts_bridge : accepts_plainly := by
  exact ⟨deposit_accepts, deposit_rejects,
    exit_accepts, exit_rejects,
    ⟨deposit_transfer_reverts, exit_transfer_reverts⟩⟩

/-- Fee reads as used, from the fee-read walks. -/
theorem feeread_bridge : fee_reads_as_used := by
  exact ⟨progress_feeread_amsterdam, progress_feeread_amsterdam_exit⟩

/-- Quote against charge, from the kept submission payments over a history. -/
theorem quote_bridge : quote_against_charge := by
  constructor
  · intro cfg start stop blocks xs ys f hcodes hdep hclean hsys hsplit hfew hlen
    have h := Deposit.history_submission_pays hcodes.linked hcodes.deposit
      hdep.depStor hsys.code hclean.senders hclean.authorities hclean.creates
      hsplit hfew hlen
    show fakeExp 1 (ChainLink.excessAt depositAddr f +
      (ChainLink.countAt depositAddr f - Deposit.contract.target.toNat)) 17 ≤
      f.sevm.value.toNat
    rw [Deposit.target_toNat]
    exact h
  · intro cfg start stop blocks xs ys f hcodes hdep hclean hsys hsplit hfew hlen
    have h := Exit.history_submission_pays hcodes.linked hcodes.exit
      hdep.exitStor hsys.code hclean.senders hclean.authorities hclean.creates
      hsplit hfew hlen
    show fakeExp 1 (ChainLink.excessAt exitAddr f +
      (ChainLink.countAt exitAddr f - Exit.contract.target.toNat)) 17 ≤
      f.sevm.value.toNat
    rw [Exit.target_toNat]
    exact h

end Blanc.Composition.BuilderRequestPublic
