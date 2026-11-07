import Blanc.Lift.BuilderRequest.FeeDomain

/-!
# Fee reads as they are used, under Amsterdam

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

A zero-value, empty-calldata message or direct transaction to a builder contract with slot 0 off the inhibitor returns exactly the
32-byte quote and leaves the contract as it was. `message_feeRead` is the top-level path, `transaction_feeRead` is
`processTransaction`, and each `_quoted` form takes the quoted excess at most 2892 in place of the loop's run. Message level does not
mention `isStatic`, so it holds of a static message too. A `STATICCALL` from another contract reaches the code as a frame, not through
`processMessageCall`: that case is the frame-level statements in `Deposit/Static` and `Exit/Static`.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune ExecutionTrace

/-- A fee read's bound on what it takes from `gasLeft`: dispatch, the fee path with `n` iterations of its loop and its two `SLOAD`s, and
the getter on empty memory. Regular gas; a fee read charges no state gas. -/
def feeReadBound (n : Nat) : Nat := 222 + 87 * n + 2 * gasColdSload

/-- **A fee read's bound on the domain.** -/
theorem feeReadBound_462 : feeReadBound 462 = 44616 := rfl

theorem feeReadBound_le {n : Nat} (hn : n ≤ 462) : feeReadBound n ≤ feeReadBound 462 := by
  unfold feeReadBound
  omega

/-- The charge of a fee read on empty memory, within `feeReadBound`. -/
theorem feeReadGas_le (s : Sevm) (b : Devm) (n : Nat) :
    UserPath.feeReadGasOn (amsterdamSteps s) b .empty n ≤ feeReadBound n := by
  have a1 := sloadCost_le s b 0
  have a2 := sloadCost_le s ((amsterdamSteps s).afterRead b 0) 1
  unfold UserPath.feeReadGasOn StorageSteps.feePathGas feeReadBound
  rw [RequestFee.feeGetterGas_empty, RequestFee.feeLoopGas_eq, feePathFixedGas, RequestSystem.dispatchGas]
  omega

/-- A zero-value message's frame starts with no log: there is no transfer log. -/
theorem initDevm_logs_zero {M : Msg} (hfork : M.benv.stat.fork = .amsterdam) (zero : M.value = 0) :
    (initDevm M).logs = [] := by
  have hsg := amsterdam_stateGas hfork
  show (match M.benv.stat.rules.stateGas with
    | none => []
    | some _ => if M.shouldTransferValue then (Devm.emitTransferLog _ _ _ _).logs else []) = _
  rw [hsg]
  by_cases h : M.shouldTransferValue = true
  · simp only [h, ↓reduceIte, Devm.emitTransferLog, zero, or_true]
    rfl
  · simp only [h, Bool.false_eq_true, ↓reduceIte]

theorem afterSloadA_deleted (s : Sevm) (d : Devm) (key : B256) :
    (afterSloadA s d key).accountsToDelete = d.accountsToDelete := by
  unfold afterSloadA Devm.balReadStorage afterSload
  split <;> split <;> rfl

variable {M : Msg} {G n : Nat} {out : B256} (k : UserPath)

/-- The frame of a zero-value message at the code. -/
local notation "S" => userSevm M k.code M.benv

/-- Its entry machine. -/
local notation "F" => userEntry M M.benv

/-- What a clean fee-read frame's message gives: the world as it was, the quote, no log, no refund, the state-gas meter untouched. -/
structure FeeReadOutput (M : Msg) (o : MsgCallOutput) (quote : B256) (G : Nat) : Prop where
  /-- No error. -/
  error : o.error = none
  /-- The return bytes are exactly the quote's word. -/
  returnData : o.returnData = quote.toBytes
  /-- No log: nothing is transferred and the frame emits none. -/
  logs : o.logs = []
  /-- What is left of the regular gas. -/
  gasLeft : o.gasLeft = G
  /-- No refund. -/
  refund : o.refundCounter = 0
  /-- The reservoir stands at its grant. -/
  stateGasLeft : o.stateGasLeft = M.stateGasGrant
  /-- No state gas used. -/
  stateGasUsed : o.stateGasUsed = 0
  /-- Nothing to delete. -/
  deleted : o.accountsToDelete.toList = []

/-- **A fee read through `processMessageCall`, under Amsterdam.** A message at a non-system caller, with no authorizations, to the code,
zero value and empty calldata, slot 0 off the inhibitor: it returns the pre-call state and exactly the quotient the recurrence computes, as
one word, leaving `G` of `G + feeReadGasOn`. -/
theorem message_feeRead (hnonempty : k.code.isEmpty = false) (hdel : getDelegatedCodeAddress k.code = none)
    (hfork : M.benv.stat.fork = .amsterdam) (hauth : M.tenv.stat.auths.isEmpty = true)
    (htarget : M.target.isNone = false) (installed : M.benv.state.getCode M.currentTarget = k.code)
    (hprecomp : ¬ amsterdamRules.isPrecomp M.currentTarget) (inherited : M.inheritedDeletions.toList = [])
    (caller : M.caller ≠ systemAddress) (empty : M.data = []) (zero : M.value = 0)
    (hgas : M.gas = G + UserPath.feeReadGasOn (amsterdamSteps S) F .empty n)
    (off : (M.benv.state.getStor M.currentTarget).get 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storageExcess k.target (M.benv.state.getStor M.currentTarget)) 17 1 17 0 n out) :
    ∃ o, processMessageCall M = .ok (M.benv.state, o) ∧ FeeReadOutput M o (out / (17 : B256)) G := by
  have hentry : M.benvAfterTransfer = .ok M.benv := Msg.benvAfterTransfer_of_value_zero zero
  have hsfork : (S).benvStat.fork = .amsterdam := hfork
  have v := amsterdamSteps_valid hsfork
  have read : ∀ key, (F).getStorVal M.currentTarget key = (M.benv.state.getStor M.currentTarget).get key := fun _ => rfl
  have hrun := UserPath.exec_fee_read_exact (k := k) (b := F) (M := .empty) (G := G) (iterations := n) (finalOutput := out)
    v rfl rfl caller empty zero (by
      show (F).getStorVal M.currentTarget 0 ≠ _
      rw [read]
      exact off) (by
      show WordFakeExponential.Run (targetExcess k.target ((F).getStorVal M.currentTarget 0)
        ((F).getStorVal M.currentTarget 1)) 17 1 17 0 n out
      rw [read, read]
      exact wordRun)
  have hSt : St (F) [] .empty (G + UserPath.feeReadGasOn (amsterdamSteps S) F .empty n) = F := by
    rw [← hgas]
    exact (St.self rfl rfl).symm
  rw [hSt] at hrun
  have hexec := (exec_iff_exec_eq _ _ _ _).mp hrun
  have herr : (systemCallBase M).error = none := systemCallBase_error M
  have hrefund : (systemCallBase M).refundCounter = 0 := systemCallBase_refundCounter M
  generalize hbase : (amsterdamSteps S).feeBase F = base at hexec
  have hb0 : base.error = none := by
    rw [← hbase]
    show (afterSloadA S (afterSloadA S F 0) 1).error = none
    rw [afterSloadA_error, afterSloadA_error]
    exact herr
  have hb1 : base.refundCounter = 0 := by
    rw [← hbase]
    show (afterSloadA S (afterSloadA S F 0) 1).refundCounter = 0
    rw [afterSloadA_refundCounter, afterSloadA_refundCounter]
    exact hrefund
  have hb2 : base.stateGas = (F).stateGas := by
    rw [← hbase]
    exact UserPath.feeBase_stateGas S F
  have hb3 : base.logs = (F).logs := by
    rw [← hbase]
    exact v.logs_feeBase F
  have hb4 : base.state = (F).state := by
    rw [← hbase]
    exact v.state_feeBase F
  have facts := RequestFee.feeGetterPost_facts base .empty (out / (17 : B256)) G Mem.wf_empty rfl
  obtain ⟨f1, f2, f3, -, -, f6, f7⟩ := facts
  generalize hpost : RequestFee.feeGetterPost base .empty (out / (17 : B256)) G = post at *
  have hpe : post.error = none := by
    show post.meta.error = none
    rw [f3]
    exact hb0
  have hpr : post.refundCounter = 0 := by
    show post.meta.refundCounter = 0
    rw [f3]
    exact hb1
  have hcall := processMessageCall_ok (code := k.code) (post := post) hfork hauth htarget installed hnonempty hdel hprecomp hentry
    hexec hpe (by rw [hpr])
  have hstate : post.state = M.benv.state := by
    show post.world.state = _
    rw [f2]
    exact hb4
  rw [hstate] at hcall
  have hlogs : post.logs = [] := by
    show post.meta.logs = []
    rw [f3]
    show base.logs = []
    rw [hb3]
    show (systemCallBase M).logs = []
    have h0 : (systemCallBase M).logs = (initDevm M).logs := by
      unfold systemCallBase Devm.balReadAccount
      dsimp only
      by_cases h : M.benv.stat.rules.bal.isSome = true <;> simp only [h, ↓reduceIte] <;> rfl
    rw [h0, initDevm_logs_zero hfork zero]
  have hmeter : post.stateGas = (F).stateGas := f7.trans hb2
  refine ⟨_, hcall, rfl, f1, hlogs, f6, ?_, ?_, ?_, ?_⟩
  · show ((post.refundCounter.toNat : Nat) : Int) = 0
    rw [hpr]
    rfl
  · show post.stateGasLeft = M.stateGasGrant
    show post.stateGas.left = _
    rw [hmeter]
    rfl
  · show Int.ofNat M.stateGasGrant - Int.ofNat post.stateGas.left + Int.ofNat post.stateGas.spilled +
      Int.ofNat post.stateGas.committedSpill = 0
    rw [hmeter]
    show Int.ofNat M.stateGasGrant - Int.ofNat M.stateGasGrant + Int.ofNat 0 + Int.ofNat 0 = 0
    simp only [Int.ofNat_eq_natCast, Int.natCast_zero, Int.add_zero, Int.sub_self]
  · show post.accountsToDelete.toList = []
    show post.meta.accountsToDelete.toList = []
    rw [f3]
    show base.accountsToDelete.toList = []
    rw [← hbase]
    show (afterSloadA S (afterSloadA S F 0) 1).accountsToDelete.toList = []
    rw [afterSloadA_deleted, afterSloadA_deleted]
    show (systemCallBase M).accountsToDelete.toList = []
    unfold systemCallBase Devm.balReadAccount
    dsimp only
    by_cases h : M.benv.stat.rules.bal.isSome = true <;> simp only [h, ↓reduceIte] <;> exact inherited

/-- **A fee read through `processMessageCall`, on the fee's domain.** With the quoted excess at most 2892, the loop's run goes: the call
returns exactly `fake_exponential(1, excess, 17)` as one word, 32 bytes, and leaves the state as it was, for a charge `X` of at most 44,616
regular gas, state gas none. -/
theorem message_feeRead_quoted (hnonempty : k.code.isEmpty = false) (hdel : getDelegatedCodeAddress k.code = none)
    (hfork : M.benv.stat.fork = .amsterdam) (hauth : M.tenv.stat.auths.isEmpty = true)
    (htarget : M.target.isNone = false) (installed : M.benv.state.getCode M.currentTarget = k.code)
    (hprecomp : ¬ amsterdamRules.isPrecomp M.currentTarget) (inherited : M.inheritedDeletions.toList = [])
    (caller : M.caller ≠ systemAddress) (empty : M.data = []) (zero : M.value = 0) (hgas : 44616 ≤ M.gas)
    (off : (M.benv.state.getStor M.currentTarget).get 0 ≠ B256.max)
    (he : (storageExcess k.target (M.benv.state.getStor M.currentTarget)).toNat ≤ 2892) :
    ∃ X o, X ≤ 44616 ∧ processMessageCall M = .ok (M.benv.state, o) ∧
      FeeReadOutput M o (fakeExp 1 (storageExcess k.target (M.benv.state.getStor M.currentTarget)).toNat 17).toB256 (M.gas - X) ∧
      o.returnData.length = 32 := by
  obtain ⟨n, out, hn, run, -, hq⟩ := RequestFeeWord.fee_run he
  have hX := feeReadGas_le S F n
  have hb := feeReadBound_le hn
  rw [feeReadBound_462] at hb
  obtain ⟨o, hcall, ho⟩ := message_feeRead k (G := M.gas - UserPath.feeReadGasOn (amsterdamSteps S) F .empty n) hnonempty hdel hfork hauth
    htarget installed hprecomp inherited caller empty zero (by omega) off run
  rw [hq] at ho
  refine ⟨_, o, by omega, hcall, ho, ?_⟩
  rw [ho.returnData]
  exact B256.length_toBytes _

section Transaction

variable {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {E t : Adr} {chainId : UInt64} {prio maxFee i f : Nat}

/-- What a direct fee read's transaction leaves, at frame charge `X`: the debited state with the refund and fee credited, gas used, a
receipt with no error and no log, nothing added to the block's logs or state gas. The message's output `o` carries the quote. -/
def FeeReadTx (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat) (E : Adr) (price i f X : Nat) : Prop :=
  let settlement := settleTransactionGas benv.stat.rules tx.gas f (tx.gas - i - X) 0 0 (0 : Int)
  let debited := txDebit benv.state E (tx.gas * price)
  let final := txFinal debited E benv.stat.coinbase (settlement.gasLeft * price)
    (settlement.gasUsed * (price - benv.stat.baseFeePerGas))
  settlement.gasUsed = max (i + X) f ∧ settlement.stateGasUsed = 0 ∧
    ∃ bout', processTransaction benv bout tx index = .ok (final, bout') ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed + settlement.gasUsed ∧
      bout'.blockGasUsed = bout.blockGasUsed + settlement.executionGasUsed ∧
      bout'.blockStateGasUsed = bout.blockStateGasUsed ∧
      bout'.blockLogs = bout.blockLogs ∧
      bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
        some (makeReceipt tx none bout'.cumulativeGasUsed [])

/-- The message a direct transaction prepares. -/
local notation "TM" => txMsg benv tx index E t (twoPrice benv.stat.baseFeePerGas prio maxFee) i

/-- **A direct fee read through `processTransaction`, on the fee's domain.** A valid type-2 transaction (`DirectTx`) to the code, zero value
and empty calldata, slot 0 off the inhibitor, the quoted excess at most 2892, gas covering the intrinsic cost and 44,616. The transaction's
message returns exactly `fake_exponential(1, excess, 17)` as one 32-byte word, on the debited state, with no log; a transaction's receipt has no
place for return bytes, so a caller reads this through `eth_call`, not the receipt. The frame's charge `X` is at most 44,616 regular gas. The
contract's account is as it was, unless it is the coinbase. -/
theorem transaction_feeRead (hnonempty : k.code.isEmpty = false) (hdel : getDelegatedCodeAddress k.code = none)
    (d : DirectTx benv bout tx E t chainId prio maxFee i f) (installed : benv.state.getCode t = k.code)
    (hprecomp : ¬ amsterdamRules.isPrecomp t) (caller : E ≠ systemAddress) (empty : tx.data = [])
    (zero : tx.value.toB256 = 0) (hgas : i + 44616 ≤ tx.gas) (off : (benv.state.getStor t).get 0 ≠ B256.max)
    (he : (storageExcess k.target (benv.state.getStor t)).toNat ≤ 2892) :
    ∃ X o, X ≤ 44616 ∧ processMessageCall TM = .ok ((TM).benv.state, o) ∧
      FeeReadOutput TM o (fakeExp 1 (storageExcess k.target (benv.state.getStor t)).toNat 17).toB256 (tx.gas - i - X) ∧
      o.returnData.length = 32 ∧
      FeeReadTx benv bout tx index E (twoPrice benv.stat.baseFeePerGas prio maxFee) i f X ∧
      (benv.stat.coinbase ≠ t → ∀ final bout', processTransaction benv bout tx index = .ok (final, bout') →
        final.get t = benv.state.get t) := by
  have hne : E ≠ t := by
    intro h
    subst h
    have hc : (benv.state.get E).code = k.code := installed
    have hn := d.noCode
    rw [hc, hnonempty] at hn
    cases hn
  have hget := txDebit_get_ne (σ := benv.state) (fee := tx.gas * twoPrice benv.stat.baseFeePerGas prio maxFee) hne
  have hstor : (TM).benv.state.getStor t = benv.state.getStor t := congrArg Acct.stor hget
  obtain ⟨X, o, hX, hcall, ho, hlen⟩ := message_feeRead_quoted k (M := TM) hnonempty hdel d.fork
    (by
      show (tx.auths).isEmpty = true
      unfold Tx.auths
      rw [d.type]
      rfl)
    rfl
    (by
      show ((txDebit benv.state E (tx.gas * twoPrice benv.stat.baseFeePerGas prio maxFee)).get t).code = _
      rw [hget]
      exact installed)
    hprecomp Std.HashSet.toList_emptyWithCapacity caller empty zero (by show 44616 ≤ tx.gas - i; omega)
    (by
      show ((TM).benv.state.getStor t).get 0 ≠ _
      rw [hstor]
      exact off)
    (by
      show (storageExcess k.target ((TM).benv.state.getStor t)).toNat ≤ _
      rw [hstor]
      exact he)
  have hsame : storageExcess k.target ((TM).benv.state.getStor (TM).currentTarget) = storageExcess k.target (benv.state.getStor t) := by
    show storageExcess k.target ((TM).benv.state.getStor t) = _
    rw [hstor]
  rw [hsame] at ho
  obtain ⟨hvs, hvalid, hchecked, halloc, hdebit, hprep⟩ := d.stages (t := t) index
  have hrefund : Int.toNat? o.refundCounter = some 0 := by rw [ho.refund]; rfl
  have stage := processTransaction_amsterdam_of_stages d.fork hvs hvalid hchecked halloc hdebit hprep hcall hrefund ho.deleted
  dsimp only at stage
  have hgrant : (TM).stateGasGrant = 0 := rfl
  have hleft : o.gasLeft = tx.gas - i - X := ho.gasLeft
  have hsl : o.stateGasLeft = 0 := ho.stateGasLeft.trans hgrant
  rw [hleft, hsl, ho.stateGasUsed] at stage
  obtain ⟨bout', hproc, hcum, hblock, hstateCtr, hblockLogs, -, hreceipt, -⟩ := stage
  have hrules : benv.stat.rules = amsterdamRules := amsterdam_rules d.fork
  have hused : (settleTransactionGas benv.stat.rules tx.gas f (tx.gas - i - X) 0 0 (0 : Int)).gasUsed = max (i + X) f := by
    rw [hrules]
    show max (tx.gas - (tx.gas - i - X) - 0 - min ((tx.gas - (tx.gas - i - X) - 0) / 5) 0) f = _
    rw [show tx.gas - (tx.gas - i - X) - 0 = i + X by omega, Nat.min_zero, Nat.sub_zero]
  have hsu : (settleTransactionGas benv.stat.rules tx.gas f (tx.gas - i - X) 0 0 (0 : Int)).stateGasUsed = 0 := by
    rw [hrules]
    rfl
  refine ⟨X, o, hX, hcall, ho, hlen, ⟨hused, hsu, bout', hproc, hcum, hblock, ?_, ?_, ?_⟩, ?_⟩
  · rw [hstateCtr, hsu, Nat.add_zero]
  · rw [hblockLogs, ho.logs, List.append_nil]
  · rw [hreceipt, ho.error, ho.logs]
  · intro hcb final' bout'' hp
    have heq := Except.ok.inj (hp.symm.trans hproc)
    obtain ⟨rfl, -⟩ := Prod.mk.inj heq
    rw [txFinal, State.addBal, State.setBal, State.setAccount_get_ne _ hcb, State.addBal, State.setBal,
      State.setAccount_get_ne _ hne]
    exact hget

end Transaction

/-! ## The quote in naturals -/

variable {sevm : Sevm} {l : StorageSteps sevm} {pre post : Devm} {target : B256} {iterations : Nat} {finalOutput : B256}

/-- The quoted excess in naturals, with no wrap in the sum. -/
theorem storedExcess_toNat (hsum : (pre.getStorVal sevm.currentTarget 0).toNat +
      ((pre.getStorVal sevm.currentTarget 1).toNat - target.toNat) < 2 ^ 256) :
    (storedExcess target sevm pre).toNat = (pre.getStorVal sevm.currentTarget 0).toNat +
      ((pre.getStorVal sevm.currentTarget 1).toNat - target.toNat) := by
  rw [storedExcess, targetExcess_toNat]
  exact Nat.mod_eq_of_lt hsum

/-- **The quoted fee in naturals, with both conditions shown.** `FeeReadOn.fee_eq_iff` for a word: with no wrap in
`slot0 + (count - target)`, and that natural at most 2892, the quote is `fake_exponential(1, slot0 + (count - target), 17)`. The second condition
implies the first; both appear so a reader sees that the word excess is the natural one. -/
theorem UserPath.FeeReadOn.fee_eq_natural (read : UserPath.FeeReadOn l target pre post iterations finalOutput)
    (hsum : (pre.getStorVal sevm.currentTarget 0).toNat +
      ((pre.getStorVal sevm.currentTarget 1).toNat - target.toNat) < 2 ^ 256)
    (he : (pre.getStorVal sevm.currentTarget 0).toNat +
      ((pre.getStorVal sevm.currentTarget 1).toNat - target.toNat) ≤ 2892) :
    (finalOutput / (17 : B256)).toNat = fakeExp 1 ((pre.getStorVal sevm.currentTarget 0).toNat +
      ((pre.getStorVal sevm.currentTarget 1).toNat - target.toNat)) 17 := by
  have hx := storedExcess_toNat (target := target) hsum
  have hrun := read.quote
  have heq : storedExcess target sevm pre = ((storedExcess target sevm pre).toNat).toB256 := (toB256_toNat _).symm
  rw [heq, hx] at hrun
  exact RequestFeeWord.word_fee_eq_natural he hrun

end Blanc.Lift.BuilderRequest
