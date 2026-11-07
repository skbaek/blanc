import Blanc.Lift.BuilderRequest.TransactionWitness
import Blanc.Lift.BuilderRequest.Deposit.FeeDomain
import Blanc.Lift.BuilderRequest.Exit.FeeDomain
import Blanc.Lift.BuilderRequest.Deposit.Properties
import Blanc.Lift.BuilderRequest.Exit.Properties
import Blanc.Lift.BuilderRequest.Exit.DeliveryWitness

/-!
# The fee-domain statements have closed models

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

The closed transactions of `TransactionWitness` meet every premise of the concrete-gas corollaries, and two more signed transactions, zero value and empty
calldata, meet every premise of the fee reads. The sender's key is the published test key 1.
-/

namespace Blanc.Lift.BuilderRequest.FeeDomainWitness

open Jaune
open TransactionWitness
open Delivery (Event)

/-- A signed fee read of the deposit contract: zero value, empty calldata. -/
def depositReadTx : Tx :=
  { nonce := 1, gas := 1000000, value := 0, data := [], v := 0
    r := (0xf01d6b9018ab421dd410404cb869072065522bf85734008f105cf385a023a80f : B256).toBytes
    s := (0x5248226eaccae0e756c0edbe9798c5d6740d9ed6bc750e65562a98ea80415d30 : B256).toBytes
    type := .two 1 1 8 (some Deposit.Creation.address) [] }

/-- A signed fee read of the exit contract: zero value, empty calldata. -/
def exitReadTx : Tx :=
  { nonce := 1, gas := 1000000, value := 0, data := [], v := 1
    r := (0xf01d6b9018ab421dd410404cb869072065522bf85734008f105cf385a023a80f : B256).toBytes
    s := (0x3df05a787ce0602d15cd97d099c0e40f7b607321b3130944d5506d8a7d1913de : B256).toBytes
    type := .two 1 1 8 (some Exit.Creation.address) [] }

theorem depositReadTx_recovers : recoverSender 1 depositReadTx = .ok sender := by
  have h : depositReadTx.signingHash = some (0x375e296563fd4a1bae6713d6e17aa2a986ec076555050911c006ed5fa8ff4902 : B256) := by
    simp only [Tx.signingHash, depositReadTx, BLT.toBytes_eq_toBytesS, Nat.toBytes_eq_toBytesS]
    decide +kernel
  rw [recoverSender, h]
  decide +kernel

theorem exitReadTx_recovers : recoverSender 1 exitReadTx = .ok sender := by
  have h : exitReadTx.signingHash = some (0xeb5d50adc7529c02932da9f9ae4cb64567d00a4a43f19f13d724efdd258c8576 : B256) := by
    simp only [Tx.signingHash, exitReadTx, BLT.toBytes_eq_toBytesS, Nat.toBytes_eq_toBytesS]
    decide +kernel
  rw [recoverSender, h]
  decide +kernel

theorem depositRead_direct : DirectTx (preBenv Deposit.Creation.address Deposit.code) preBout depositReadTx sender
    Deposit.Creation.address 1 1 8 15000 15000 where
  fork := rfl
  type := rfl
  chain := rfl
  prioLe := by decide
  baseLe := by decide
  cost := by decide +kernel
  intrinsic := by decide
  floor := by decide
  budget := by decide
  room := by decide
  stateRoom := by decide
  recover := depositReadTx_recovers
  nonce := by decide +kernel
  nonceMax := by decide +kernel
  noCode := by decide +kernel
  funds := by decide +kernel

theorem exitRead_direct : DirectTx (preBenv Exit.Creation.address Exit.code) preBout exitReadTx sender
    Exit.Creation.address 1 1 8 15000 15000 where
  fork := rfl
  type := rfl
  chain := rfl
  prioLe := by decide
  baseLe := by decide
  cost := by decide +kernel
  intrinsic := by decide
  floor := by decide
  budget := by decide
  room := by decide
  stateRoom := by decide
  recover := exitReadTx_recovers
  nonce := by decide +kernel
  nonceMax := by decide +kernel
  noCode := by decide +kernel
  funds := by decide +kernel

/-- At excess 0 the natural fee is 1 wei. -/
theorem fakeExp_zero : fakeExp 1 0 17 = 1 := by
  have h : FakeExponentialEval.runFuel 512 0 17 1 17 = some (1, 17) := by decide +kernel
  have out := (FakeExponentialEval.run_of_runFuel h).output_eq
  show fakeExpAux 0 17 1 17 / 17 = _
  rw [← out]

theorem excess_empty (t : B256) : (storageExcess t Stor.empty).toNat = 0 := by
  have h0 : (Stor.empty.get 0).toNat = 0 := rfl
  have h1 : (Stor.empty.get 1).toNat = 0 := rfl
  rw [storageExcess, targetExcess_toNat, h0, h1, Nat.zero_sub, Nat.add_zero, Nat.zero_mod]

/-- **The concrete-gas submission has a model at the deposit contract**: `deposit_direct` meets `transaction_ok_quoted`'s premises. -/
theorem deposit_quoted_model :
    ∃ entry : Benv, ∃ X used, X ≤ 147683 + 783360 ∧ used ≤ 783360 ∧
      Deposit.submissions.TxApplied (preBenv Deposit.Creation.address Deposit.code) preBout depositTx 0 sender
        Deposit.Creation.address (twoPrice (preBenv Deposit.Creation.address Deposit.code).stat.baseFeePerGas 1 8) 23944 32776 entry X used := by
  obtain ⟨entry, -, h⟩ := Deposit.transaction_ok_quoted (index := 0) deposit_direct
    (by decide +kernel) (by decide +kernel) Std.HashSet.not_mem_emptyWithCapacity (by decide +kernel) rfl (by decide)
    (by rw [deposit_stor]; decide +kernel) (by rw [deposit_stor, excess_empty]; decide)
    (by
      rw [deposit_stor, excess_empty, fakeExp_zero]
      exact ⟨by decide +kernel, by decide +kernel⟩)
    (by rw [deposit_stor]; decide +kernel)
  exact ⟨entry, h⟩

/-- **The concrete-gas submission has a model at the exit contract**: `exit_direct` meets `transaction_ok_quoted`'s premises. -/
theorem exit_quoted_model :
    ∃ entry : Benv, ∃ X used, X ≤ 110330 + 489600 ∧ used ≤ 489600 ∧
      Exit.submissions.TxApplied (preBenv Exit.Creation.address Exit.code) preBout exitTx 0 sender
        Exit.Creation.address (twoPrice (preBenv Exit.Creation.address Exit.code).stat.baseFeePerGas 1 8) 21768 24072 entry X used := by
  obtain ⟨entry, -, h⟩ := Exit.transaction_ok_quoted (index := 0) exit_direct
    (by decide +kernel) (by decide +kernel) Std.HashSet.not_mem_emptyWithCapacity (by decide +kernel) rfl (by decide)
    (by rw [exit_stor]; decide +kernel) (by rw [exit_stor, excess_empty]; decide)
    (by
      rw [exit_stor, excess_empty, fakeExp_zero]
      show (Nat.toB256 1).toNat ≤ (Nat.toB256 1).toNat
      exact Nat.le_refl _)
    (by rw [exit_stor]; decide +kernel)
  exact ⟨entry, h⟩

/-- **The transaction fee read has a model at the deposit contract**: its quote on empty storage is 1 wei, 32 bytes, and no log. -/
theorem deposit_feeRead_model :
    ∃ (X : Nat) (o : MsgCallOutput), X ≤ 44616 ∧ o.returnData = (1 : B256).toBytes ∧ o.logs = [] ∧ o.error = none ∧
      FeeReadTx (preBenv Deposit.Creation.address Deposit.code) preBout depositReadTx 0 sender
        (twoPrice (preBenv Deposit.Creation.address Deposit.code).stat.baseFeePerGas 1 8) 15000 15000 X := by
  obtain ⟨X, o, hX, -, ho, -, htx, -⟩ := Deposit.transaction_feeRead (index := 0) depositRead_direct
    (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) (by decide)
    (by rw [deposit_stor]; decide +kernel) (by rw [deposit_stor, excess_empty]; decide)
  refine ⟨X, o, hX, ho.returnData.trans ?_, ho.logs, ho.error, htx⟩
  rw [deposit_stor, excess_empty, fakeExp_zero]
  rfl

/-- **The transaction fee read has a model at the exit contract.** On empty storage, off the inhibitor. -/
theorem exit_feeRead_model :
    ∃ (X : Nat) (o : MsgCallOutput), X ≤ 44616 ∧ o.returnData = (1 : B256).toBytes ∧ o.logs = [] ∧ o.error = none ∧
      FeeReadTx (preBenv Exit.Creation.address Exit.code) preBout exitReadTx 0 sender
        (twoPrice (preBenv Exit.Creation.address Exit.code).stat.baseFeePerGas 1 8) 15000 15000 X := by
  obtain ⟨X, o, hX, -, ho, -, htx, -⟩ := Exit.transaction_feeRead (index := 0) exitRead_direct
    (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) (by decide)
    (by rw [exit_stor]; decide +kernel) (by rw [exit_stor, excess_empty]; decide)
  refine ⟨X, o, hX, ho.returnData.trans ?_, ho.logs, ho.error, htx⟩
  rw [exit_stor, excess_empty, fakeExp_zero]
  rfl

/-! ## Surplus -/

/-- A signed deposit of all-ones calldata paying 1 ETH above the credit and the fee. -/
def depositSurplusTx : Tx :=
  { nonce := 1, gas := 1000000, value := goodValue + 10 ^ 18, data := List.replicate 184 0xff, v := 0
    r := (0xf01d6b9018ab421dd410404cb869072065522bf85734008f105cf385a023a80f : B256).toBytes
    s := (0x3fbefc1d0fdb21f3ca255861795924078ffdd543efff731b85cee1ad19ba2cf8 : B256).toBytes
    type := .two 1 1 8 (some Deposit.Creation.address) [] }

theorem depositSurplusTx_recovers : recoverSender 1 depositSurplusTx = .ok sender := by
  have h : depositSurplusTx.signingHash = some (0x0f16fefe492c78b3290ccb3e8bfc78ed559401d2c8b2e2ea76280d85b8aba47c : B256) := by
    simp only [Tx.signingHash, depositSurplusTx, BLT.toBytes_eq_toBytesS, Nat.toBytes_eq_toBytesS]
    decide +kernel
  rw [recoverSender, h]
  decide +kernel

theorem depositSurplus_direct : DirectTx (preBenv Deposit.Creation.address Deposit.code) preBout depositSurplusTx sender
    Deposit.Creation.address 1 1 8 23944 32776 where
  fork := rfl
  type := rfl
  chain := rfl
  prioLe := by decide
  baseLe := by decide
  cost := by decide +kernel
  intrinsic := by decide
  floor := by decide
  budget := by decide
  room := by decide
  stateRoom := by decide
  recover := depositSurplusTx_recovers
  nonce := by decide +kernel
  nonceMax := by decide +kernel
  noCode := by decide +kernel
  funds := by decide +kernel

/-- **`surplus_locked` has a model with real surplus.** A closed deposit paying 1 ETH above the credit and the fee succeeds, and the contract's balance rises by the whole value. -/
theorem deposit_surplus_model :
    ∃ (st : State) (bout' : BlockOutput),
      processTransaction (preBenv Deposit.Creation.address Deposit.code) preBout depositSurplusTx 0 = .ok (st, bout') ∧
      (st.get Deposit.Creation.address).bal = (goodValue + 10 ^ 18 : Nat).toB256 := by
  obtain ⟨_, st, bout', -, hproc, hbal, -⟩ := Deposit.surplus_locked (index := 0) (n := 1) (out := 17) depositSurplus_direct
    (by decide +kernel) (by decide +kernel) Std.HashSet.not_mem_emptyWithCapacity (by decide +kernel) (by decide +kernel) rfl
    (by decide)
    (by rw [deposit_stor]; decide +kernel)
    (by
      rw [deposit_stor]
      have hz : storageExcess 8 Stor.empty = 0 := by decide +kernel
      show WordFakeExponential.Run (storageExcess 8 Stor.empty) 17 1 17 0 1 17
      rw [hz]
      exact quote_zero_excess)
    ⟨by decide +kernel, by decide +kernel⟩
    (by rw [deposit_stor]; decide +kernel)
    (by decide +kernel)
  refine ⟨st, bout', hproc, hbal.trans ?_⟩
  decide +kernel

/-! ## A batcher, and the flood's budget -/

/-- A frame by this record's source paying 1 wei, under Amsterdam. -/
def cheapSevm (r : Exit.Record) : Sevm := { Exit.recordSevm r with value := 1 }

/-- The storage after the unlocking call, on a machine holding it. -/
theorem unlocked_represents : ∃ (f0 : Exit.Frame), f0.before = Exit.deployedStorage ∧ f0.event = .system false ∧
    Delivery.Holds Exit.contract f0.after (Delivery.step 16 2 Exit.deployedQueue (.system false)) := by
  obtain ⟨f0, hb0, he0⟩ := Exit.exists_system Exit.deployedStorage
  have rep0 : Delivery.Holds Exit.contract f0.before Exit.deployedQueue := by
    rw [hb0]
    exact Exit.deployed_represents
  have h := (f0.step_holds rep0 (by rw [he0]; decide) (by rw [he0]; decide)).1
  rw [he0] at h
  exact ⟨f0, hb0, he0, h⟩

/-- **`batcher_witness`'s premises can all be met together**: two callers, the same contract, a represented queue just after the unlocking call. -/
theorem batcher_model (r1 r2 : Exit.Record) (h1 : r1.source ≠ systemAddress) (h2 : r2.source ≠ systemAddress) (s : Stor)
    (rep : Delivery.Holds Exit.contract s (Delivery.step 16 2 Exit.deployedQueue (.system false))) :
    ∃ post1 post2,
      Nonempty (Exec 0 (cheapSevm r1) (St (Delivery.holdingDevm Exit.Creation.address Exit.code s) [] .empty
        (2301 + Exit.submissionGasA (cheapSevm r1) (Delivery.holdingDevm Exit.Creation.address Exit.code s) .empty 1)) (.ok post1)) ∧
      Nonempty (Exec 0 (cheapSevm r2) (St post1 [] .empty (2301 + Exit.submissionGasA (cheapSevm r2) post1 .empty 1)) (.ok post2)) ∧
      (Delivery.submit (Delivery.submit (Delivery.step 16 2 Exit.deployedQueue (.system false)) r1) r2).queue = [r1, r2] := by
  have hx : (Delivery.step 16 2 Exit.deployedQueue (.system false)).excess = 0 :=
    (drained_excess_cases 16 2 Exit.deployedQueue).1 rfl
  have hc : (Delivery.step 16 2 Exit.deployedQueue (.system false)).count = 0 := Delivery.drainedState_count _ _ _
  have rep' : Represents 3 Exit.Record.word
      (fun key => ((Delivery.holdingDevm Exit.Creation.address Exit.code s).getStor (cheapSevm r1).currentTarget).get key)
      (Delivery.step 16 2 Exit.deployedQueue (.system false)) := by
    have hs : (Delivery.holdingDevm Exit.Creation.address Exit.code s).getStor (cheapSevm r1).currentTarget = s :=
      Delivery.holding_getStor _ _ s
    rw [hs]
    exact rep
  obtain ⟨post1, post2, e1, e2, -, hq, -⟩ := Exit.batcher_witness (s1 := cheapSevm r1) (s2 := cheapSevm r2) (G1 := 2301) (G2 := 2301)
    rfl rfl rfl rfl rfl h1 h2 r1.pubkey_length r2.pubkey_length rfl rfl
    (by show 1 ≤ (1 : B256).toNat; decide) (by show 1 ≤ (1 : B256).toNat; decide) (by decide) (by decide) rep' hx hc
    (by decide)
  exact ⟨post1, post2, e1, e2, hq.trans rfl⟩

/-- **`submissions_le_paid`'s budget can be met by a frame that submits**: from the deployed storage, the unlocking call, then one submission paying 1 wei. -/
theorem flood_model (r : Exit.Record) (hr : r.source ≠ systemAddress) :
    ∃ (frames : List Exit.Frame) (t : Stor), Delivery.Chain Exit.deployedStorage frames t ∧
      Delivery.submissions frames = [r] ∧ Exit.paid frames = 1 := by
  obtain ⟨f0, hb0, he0, rep⟩ := unlocked_represents
  have hx : (Delivery.step 16 2 Exit.deployedQueue (.system false)).excess = 0 :=
    (drained_excess_cases 16 2 Exit.deployedQueue).1 rfl
  have hc : (Delivery.step 16 2 Exit.deployedQueue (.system false)).count = 0 := Delivery.drainedState_count _ _ _
  have s0 : f0.after.get 0 = 0 := by
    have h : f0.after.get 0 = _ := rep.excess
    rw [hx] at h
    exact h
  have s1 : f0.after.get 1 = 0 := by
    have h : f0.after.get 1 = _ := rep.count
    rw [hc] at h
    exact h
  have hb := Delivery.holdingDevm_getStorVal Exit.Creation.address Exit.code f0.after
  have hx0 : storedExcess 2 (cheapSevm r) (Delivery.holdingDevm Exit.Creation.address Exit.code f0.after) = 0 := by
    show targetExcess 2 ((Delivery.holdingDevm Exit.Creation.address Exit.code f0.after).getStorVal Exit.Creation.address 0)
      ((Delivery.holdingDevm Exit.Creation.address Exit.code f0.after).getStorVal Exit.Creation.address 1) = 0
    rw [hb, hb, s0, s1]
    decide
  have hfork : (cheapSevm r).benvStat.fork = .amsterdam := rfl
  obtain ⟨exec⟩ := Exit.exec_submission_amsterdam (b := Delivery.holdingDevm Exit.Creation.address Exit.code f0.after) (M := .empty)
    (G := gCallStipend + 1) (sevm := cheapSevm r) (finalOutput := 17) rfl hfork hr r.pubkey_length rfl (by omega)
    (by
      show (Delivery.holdingDevm Exit.Creation.address Exit.code f0.after).getStorVal Exit.Creation.address 0 ≠ _
      rw [hb, s0]
      decide)
    (by rw [hx0]; exact quote_zero_excess)
    (by show ((17 : B256) / (17 : B256)).toNat ≤ (1 : B256).toNat; decide)
  have frame := Exit.exec_user_frame_amsterdam (sevm := cheapSevm r)
    (pre := St (Delivery.holdingDevm Exit.Creation.address Exit.code f0.after) [] .empty _) rfl hfork rfl rfl Mem.wf_empty
    (by show r.pubkey.length < _; rw [r.pubkey_length]; decide) hr exec
  cases frame with
  | submission i' o' law =>
    have hv0 : f0.value = 0 := by
      cases f0 with
      | submission sevm pre post l i o rules target caller law => cases he0
      | feeRead sevm pre post l i o rules target caller law => cases he0
      | system benv data post out fork installed length run => rfl
    refine ⟨[f0, .submission (cheapSevm r) _ _ _ i' o' (.amsterdam hfork) rfl hr law], _,
      .cons hb0 (.cons (Delivery.holding_getStor _ _ _) (.nil _)), ?_, ?_⟩
    · show Delivery.submitted [f0.event, Event.submission (Exit.recordOf (cheapSevm r) law.length)] = _
      rw [he0]
      rfl
    · show Delivery.paidBy _ = 1
      rw [Delivery.paidBy_cons, Delivery.paidBy_cons, hv0]
      show 0 + ((1 : B256).toNat + 0) = 1
      decide
  | feeRead i' o' empty law =>
    have := r.pubkey_length
    rw [show r.pubkey = [] from empty] at this
    cases this

end Blanc.Lift.BuilderRequest.FeeDomainWitness
