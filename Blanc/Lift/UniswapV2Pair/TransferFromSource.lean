import Blanc.Lift.UniswapV2Pair.TransferFromEntries
import Blanc.Lift.UniswapV2Pair.TransferSource
import Blanc.Lift.CalldataGuards

/-! Finite allowance and sequential balance representation for the existing transferFrom handler. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def transferFromTouched (owner spender recipient : Adr) : List WriterKey :=
  [.allowance owner spender, .balance owner, .balance recipient]

def transferFromAllowanceState (st : State) (owner spender : Adr) (amount : B256) : State :=
  if st.allowance owner spender = B256.max then st else
    approveSourceState st owner spender (st.allowance owner spender - amount)

def transferFromSourceState (st : State) (owner spender recipient : Adr) (amount : B256) : State :=
  transferSourceState (transferFromAllowanceState st owner spender amount) owner recipient amount

/-- The finite allowance write reuses the accepted selected-store theorem on the one extended universe. -/
theorem WriterRep.transferFrom_allowance_store {K : WriterKey → Prop} {s : Stor} {st : State}
    {owner spender recipient : Adr} {amount : B256} (rep : WriterRep K s st)
    (fresh : WriterFreshKeys K (transferFromTouched owner spender recipient)) :
    WriterRep (WriterExtend K (transferFromTouched owner spender recipient))
      (s.set (WriterKey.slot (.allowance owner spender)) (st.allowance owner spender - amount))
      (approveSourceState st owner spender (st.allowance owner spender - amount)) := by
  have extended := rep.extend fresh
  have touched : ∀ k ∈ approveTouched owner spender,
      WriterExtend K (transferFromTouched owner spender recipient) k := by
    intro k hk
    simp only [approveTouched, List.mem_singleton] at hk
    subst k
    exact .inr (List.mem_cons.mpr (.inl rfl))
  have selectedFresh : WriterFreshKeys (WriterExtend K (transferFromTouched owner spender recipient))
      (approveTouched owner spender) :=
    Blanc.SlotFootprint.FreshKeys.of_universe extended.inj extended.apart (fun _ h => h) touched
  have stored := extended.approve_store (amount := st.allowance owner spender - amount) selectedFresh
  have keys : WriterExtend (WriterExtend K (transferFromTouched owner spender recipient))
      (approveTouched owner spender) = WriterExtend K (transferFromTouched owner spender recipient) := by
    funext k
    apply propext
    constructor
    · rintro (old | new)
      · exact old
      · exact touched k new
    · intro old
      exact .inl old
  rw [keys] at stored
  exact stored

theorem transferFrom_allowance_reads {K : WriterKey → Prop} {st : State} {sevm : Sevm} {b : Devm}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm))) :
    transferFromAllowanceWord sevm b (transferFromOwner sevm) = st.allowance (transferFromOwner sevm) sevm.caller ∧
    transferFromAllowanceWord sevm (transferFromFirst sevm b) (transferFromOwner sevm) =
      st.allowance (transferFromOwner sevm) sevm.caller := by
  have extended := rep.extend fresh
  have member : WriterExtend K
      (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm))
      (.allowance (transferFromOwner sevm) sevm.caller) := .inr (List.mem_cons.mpr (.inl rfl))
  have read := extended.selected (.allowance (transferFromOwner sevm) sevm.caller) member
  refine ⟨read, ?_⟩
  unfold transferFromAllowanceWord transferFromFirst transferFromFirstBase
  change ((afterSload sevm b (transferFromAllowanceSlot (transferFromOwner sevm) sevm.caller)).getStor
    sevm.currentTarget).get (transferFromAllowanceSlot (transferFromOwner sevm) sevm.caller) = _
  rw [afterSload_getStor]
  exact read

theorem WriterRep.transferFrom_balance_base {K : WriterKey → Prop} {st : State} {sevm : Sevm} {b : Devm}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm))) :
    WriterRep (WriterExtend K (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm)))
      ((transferFromBalanceBase sevm b).getStor sevm.currentTarget)
      (transferFromAllowanceState st (transferFromOwner sevm) sevm.caller (transferFromAmount sevm)) := by
  have reads := transferFrom_allowance_reads rep fresh
  unfold transferFromBalanceBase transferFromAllowanceState
  by_cases maximal : transferFromMaximal sevm b
  · have same : st.allowance (transferFromOwner sevm) sevm.caller = B256.max := by
      rw [← reads.1]
      exact maximal
    rw [ite_eq_left maximal, ite_eq_left same]
    unfold transferFromFirst transferFromFirstBase
    rw [afterSload_getStor]
    exact rep.extend fresh
  · have different : st.allowance (transferFromOwner sevm) sevm.caller ≠ B256.max := by
      rw [← reads.1]
      exact maximal
    rw [ite_eq_right maximal, ite_eq_right different]
    unfold transferFromStored transferFromStoreBase transferFromSecond transferFromSecondBase transferFromFirst transferFromFirstBase
    rw [afterSstore_getStor_self, afterSload_getStor, afterSload_getStor]
    unfold transferFromReduced
    rw [reads.2]
    exact rep.transferFrom_allowance_store fresh

theorem transferFromAllowanceState_balance (st : State) (owner spender : Adr) (amount : B256) :
    (transferFromAllowanceState st owner spender amount).balanceOf = st.balanceOf := by
  unfold transferFromAllowanceState
  split <;> rfl

theorem transferFrom_balance_reads {K : WriterKey → Prop} {st : State} {sevm : Sevm} {b : Devm}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm))) :
    transferSourceWord sevm (transferFromBalanceBase sevm b) (transferFromOwner sevm) =
      st.balanceOf (transferFromOwner sevm) ∧
    transferFromCreditWord sevm b = Blanc.ledgerDebit st.balanceOf (transferFromOwner sevm)
      (transferFromAmount sevm) (transferFromRecipient sevm) := by
  have base := rep.transferFrom_balance_base fresh
  have ownerKey : WriterExtend K
      (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm))
      (.balance (transferFromOwner sevm)) := .inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl))))
  have recipientKey : WriterExtend K
      (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm))
      (.balance (transferFromRecipient sevm)) :=
    .inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl)))))
  have source : transferSourceWord sevm (transferFromBalanceBase sevm b) (transferFromOwner sevm) =
      st.balanceOf (transferFromOwner sevm) := by
    have selected := base.selected (.balance (transferFromOwner sevm)) ownerKey
    change _ = (transferFromAllowanceState st (transferFromOwner sevm) sevm.caller (transferFromAmount sevm)).balanceOf _ at selected
    rwa [transferFromAllowanceState_balance] at selected
  refine ⟨source, ?_⟩
  change ((transferDebitBase sevm (transferFromLoaded sevm b) (transferFromOwner sevm)
    (transferFromDebitWord sevm b)).getStor sevm.currentTarget).get
    (transferBalanceSlot (transferFromRecipient sevm)) = _
  rw [transferDebitBase, afterSstore_getStor_self, transferFromLoaded, afterSload_getStor]
  unfold transferFromDebitWord
  rw [source]
  have selected := (base.balance_store (value := st.balanceOf (transferFromOwner sevm) - transferFromAmount sevm)
    ownerKey).selected (.balance (transferFromRecipient sevm)) recipientKey
  dsimp only [WriterKey.value, balanceSourceState] at selected
  rw [transferFromAllowanceState_balance] at selected
  exact selected

theorem transferFromBalanceBase_facts (sevm : Sevm) (b : Devm) :
    (transferFromBalanceBase sevm b).logs = b.logs ∧
    (∀ a, a ≠ sevm.currentTarget → (transferFromBalanceBase sevm b).getStor a = b.getStor a) := by
  unfold transferFromBalanceBase
  split
  · simp only [transferFromFirst, transferFromFirstBase, afterSload_logs, afterSload_getStor]
    exact ⟨True.intro, fun _ _ => True.intro⟩
  · simp only [transferFromStored, transferFromStoreBase, transferFromSecond,
      transferFromSecondBase, transferFromFirst, transferFromFirstBase, afterSstore_logs,
      afterSload_logs]
    refine ⟨True.intro, ?_⟩
    intro a different
    rw [afterSstore_getStor_ne _ _ _ _ _ different.symm, afterSload_getStor, afterSload_getStor]

/-- Physical facts retain the allowance branch's exact metadata base and sequential balance stores. -/
theorem transferFromPublicPost_facts {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} (mem : PtrMem 128 96 M) :
    (transferFromPublicPost sevm b R M G).output = encodeWords [1] ∧
    (transferFromPublicPost sevm b R M G).logs = b.logs ++
      [transferRawLog sevm.currentTarget (transferFromOwner sevm) (transferFromRecipient sevm) (transferFromAmount sevm)] ∧
    (transferFromPublicPost sevm b R M G).getStor sevm.currentTarget =
      (((transferFromBalanceBase sevm b).getStor sevm.currentTarget).set
        (transferBalanceSlot (transferFromOwner sevm)) (transferFromDebitWord sevm b)).set
        (transferBalanceSlot (transferFromRecipient sevm)) (transferFromCreditWord sevm b + transferFromAmount sevm) ∧
    (∀ a, a ≠ sevm.currentTarget → (transferFromPublicPost sevm b R M G).getStor a = b.getStor a) ∧
    (transferFromPublicPost sevm b R M G).gasLeft = G := by
  unfold transferFromPublicPost
  have memory := transferFromRawMemory_ptr (sevm := sevm) (b := b) mem
  have facts := getterWordPost_facts
    (b := transferCoreBase sevm (transferFromBalanceBase sevm b) (transferFromOwner sevm)
      (transferFromRecipient sevm) (transferFromAmount sevm))
    (R := R) (v := 1) (G := G) memory.wf
  have base := transferFromBalanceBase_facts sevm b
  refine ⟨?_, ?_, ?_, ?_, facts.2.2.2⟩
  · simpa only [encodeWords, List.flatMap_cons, List.flatMap_nil, List.append_nil] using facts.1
  · have creditLogs (base : Devm) (owner recipient : Adr) (amount credited : B256) :
        (transferCreditBase sevm base owner recipient amount credited).logs = base.logs ++
          [transferRawLog sevm.currentTarget owner recipient amount] := by
      change (afterSstore sevm base (transferBalanceSlot recipient) credited).logs ++
        [transferRawLog sevm.currentTarget owner recipient amount] = _
      rw [afterSstore_logs]
    rw [facts.2.2.1]
    simp only [transferCoreBase, creditLogs, afterSload_logs, transferDebitBase, afterSstore_logs, base.1]
  · rw [facts.2.1 sevm.currentTarget]
    simp only [transferCoreBase, transferCreditBase, Devm.addLog_getStor,
      afterSstore_getStor_self, afterSload_getStor, transferDebitBase]
    rfl
  · intro a different
    rw [facts.2.1 a]
    simp only [transferCoreBase, transferCreditBase, Devm.addLog_getStor,
      afterSstore_getStor_ne _ _ _ _ _ different.symm, afterSload_getStor, transferDebitBase]
    exact base.2 a different

/-- All touched rows share one finite universe; no global raw map agreement is assumed. -/
theorem WriterRep.transferFrom_public_post {K : WriterKey → Prop} {st : State}
    {sevm : Sevm} {b : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm))) :
    WriterRep (WriterExtend K (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm)))
      ((transferFromPublicPost sevm b [0x23b872dd] getterInitMemory G).getStor sevm.currentTarget)
      (transferFromSourceState st (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm) (transferFromAmount sevm)) := by
  have base := rep.transferFrom_balance_base fresh
  have reads := transferFrom_balance_reads rep fresh
  have ownerKey : WriterExtend K
      (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm))
      (.balance (transferFromOwner sevm)) := .inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl))))
  have recipientKey : WriterExtend K
      (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm))
      (.balance (transferFromRecipient sevm)) :=
    .inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl)))))
  have facts := transferFromPublicPost_facts (sevm := sevm) (b := b)
    (R := [0x23b872dd]) (G := G) getterInitMemory_ptr
  rw [facts.2.2.1]
  unfold transferFromDebitWord
  rw [reads.1, reads.2]
  have debited := base.balance_store
    (value := st.balanceOf (transferFromOwner sevm) - transferFromAmount sevm) ownerKey
  have credited := debited.balance_store
    (value := Blanc.ledgerDebit st.balanceOf (transferFromOwner sevm) (transferFromAmount sevm)
      (transferFromRecipient sevm) + transferFromAmount sevm) recipientKey
  dsimp only [transferFromSourceState, transferSourceState, balanceSourceState] at credited ⊢
  rw [transferFromAllowanceState_balance] at credited ⊢
  exact credited

def transferFromDecodedEntry (sevm : Sevm) : Entry :=
  .transferFrom (transferFromOwner sevm) (transferFromRecipient sevm) (transferFromAmount sevm)

def transferFromSourceFrame (current : Checkpoint) (ctx : Context)
    (owner recipient : Adr) (amount : B256) : Frame :=
  (Frame.enter current ctx (.transferFrom owner recipient amount)).withEvents
    (transferFromSourceState current.state owner ctx.sender recipient amount)
    [.transfer owner recipient amount]

def transferFromSourceDone (current : Checkpoint) (ctx : Context)
    (owner recipient : Adr) (amount : B256) : RunResult :=
  { status := .success (encodeWords [1]),
    frame := transferFromSourceFrame current ctx owner recipient amount,
    remaining := .done, childReturns := [] }

theorem transferFromLP_accept {st : State} {ctx : Context} {owner recipient : Adr} {amount : B256}
    (allowed : st.allowance owner ctx.sender = B256.max ∨ amount ≤ st.allowance owner ctx.sender)
    (nonstatic : ctx.isStatic = false) (cover : amount ≤ st.balanceOf owner)
    (nowrap : (Blanc.ledgerDebit st.balanceOf owner amount recipient).toNat + amount.toNat < 2 ^ 256) :
    st.transferFromLP ctx owner recipient amount =
      .ok (transferFromSourceState st owner ctx.sender recipient amount, [.transfer owner recipient amount]) := by
  unfold State.transferFromLP transferFromSourceState transferFromAllowanceState
  by_cases maximal : st.allowance owner ctx.sender = B256.max
  · rw [ite_eq_left maximal, ite_eq_left maximal]
    exact transferLP_accept nonstatic cover nowrap
  · have finiteCover := allowed.resolve_left maximal
    rw [ite_eq_right maximal, ite_eq_right maximal, ite_eq_left finiteCover, nonstatic]
    exact transferLP_accept nonstatic cover nowrap

theorem transferFrom_startImmediate_done {current : Checkpoint} {ctx : Context}
    {owner recipient : Adr} {amount : B256}
    (value : ctx.value = 0)
    (allowed : current.state.allowance owner ctx.sender = B256.max ∨ amount ≤ current.state.allowance owner ctx.sender)
    (nonstatic : ctx.isStatic = false) (cover : amount ≤ current.state.balanceOf owner)
    (nowrap : (Blanc.ledgerDebit current.state.balanceOf owner amount recipient).toNat + amount.toNat < 2 ^ 256) :
    startImmediate current ctx (.transferFrom owner recipient amount) =
      some (.finished (transferFromSourceFrame current ctx owner recipient amount) (encodeWords [1])) := by
  simp only [startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad value), getterResult,
    transferFromLP_accept allowed nonstatic cover nowrap, Frame.finishLP]
  rfl

theorem transferFrom_drive_done {current : Checkpoint} {ctx : Context}
    {owner recipient : Adr} {amount : B256}
    (value : ctx.value = 0)
    (allowed : current.state.allowance owner ctx.sender = B256.max ∨ amount ≤ current.state.allowance owner ctx.sender)
    (nonstatic : ctx.isStatic = false) (cover : amount ≤ current.state.balanceOf owner)
    (nowrap : (Blanc.ledgerDebit current.state.balanceOf owner amount recipient).toNat + amount.toNat < 2 ^ 256) :
    drive 2 (startTyped current ctx (.transferFrom owner recipient amount)) .done =
      transferFromSourceDone current ctx owner recipient amount := by
  rw [startTyped, transferFrom_startImmediate_done value allowed nonstatic cover nowrap]
  rfl

theorem transferFrom_startImmediate_inv {current : Checkpoint} {ctx : Context}
    {owner recipient : Adr} {amount : B256} {sourceFrame : Frame} {returndata : Bytes}
    (accepted : startImmediate current ctx (.transferFrom owner recipient amount) =
      some (.finished sourceFrame returndata)) :
    ctx.value = 0 ∧
    (current.state.allowance owner ctx.sender = B256.max ∨ amount ≤ current.state.allowance owner ctx.sender) ∧
    ctx.isStatic = false ∧ amount ≤ current.state.balanceOf owner ∧
    (Blanc.ledgerDebit current.state.balanceOf owner amount recipient).toNat + amount.toNat < 2 ^ 256 ∧
    sourceFrame = transferFromSourceFrame current ctx owner recipient amount ∧ returndata = encodeWords [1] := by
  have value : ctx.value = 0 := by
    by_contra paid
    simp only [startImmediate, ite_eq_left paid, Frame.fail, Option.some.injEq] at accepted
    cases accepted
  have allowed : current.state.allowance owner ctx.sender = B256.max ∨
      amount ≤ current.state.allowance owner ctx.sender := by
    by_contra denied
    have finite : current.state.allowance owner ctx.sender ≠ B256.max := fun eq => denied (.inl eq)
    have uncovered : ¬ amount ≤ current.state.allowance owner ctx.sender := fun cover => denied (.inr cover)
    simp only [startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad value), getterResult,
      State.transferFromLP, ite_eq_right finite, ite_eq_right uncovered, Frame.finishLP,
      Frame.fail, Option.some.injEq] at accepted
    cases accepted
  have nonstatic : ctx.isStatic = false := by
    cases static : ctx.isStatic with
    | false => rfl
    | true =>
      by_cases maximal : current.state.allowance owner ctx.sender = B256.max
      · by_cases cover : amount ≤ current.state.balanceOf owner
        · simp only [startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad value), getterResult,
            State.transferFromLP, ite_eq_left maximal, State.transferLP, ite_eq_left cover,
            static, ite_true, Frame.finishLP, Frame.fail, Option.some.injEq] at accepted
          cases accepted
        · simp only [startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad value), getterResult,
            State.transferFromLP, ite_eq_left maximal, State.transferLP, ite_eq_right cover,
            Frame.finishLP, Frame.fail, Option.some.injEq] at accepted
          cases accepted
      · have cover := allowed.resolve_left maximal
        simp only [startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad value), getterResult,
          State.transferFromLP, ite_eq_right maximal, ite_eq_left cover, static,
          ite_true, Frame.finishLP, Frame.fail, Option.some.injEq] at accepted
        cases accepted
  have cover : amount ≤ current.state.balanceOf owner := by
    by_contra uncovered
    by_cases maximal : current.state.allowance owner ctx.sender = B256.max
    · simp only [startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad value), getterResult,
        State.transferFromLP, ite_eq_left maximal, State.transferLP, ite_eq_right uncovered,
        Frame.finishLP, Frame.fail, Option.some.injEq] at accepted
      cases accepted
    · have finiteCover := allowed.resolve_left maximal
      simp only [startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad value), getterResult,
        State.transferFromLP, ite_eq_right maximal, ite_eq_left finiteCover, nonstatic,
        State.transferLP, ite_eq_right uncovered, Frame.finishLP, Frame.fail, Option.some.injEq] at accepted
      cases accepted
  have nowrap : (Blanc.ledgerDebit current.state.balanceOf owner amount recipient).toNat + amount.toNat < 2 ^ 256 := by
    by_contra wrapped
    by_cases maximal : current.state.allowance owner ctx.sender = B256.max
    · simp only [startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad value), getterResult,
        State.transferFromLP, ite_eq_left maximal, State.transferLP, ite_eq_left cover,
        nonstatic, ite_eq_right wrapped, Frame.finishLP, Frame.fail, Option.some.injEq] at accepted
      cases accepted
    · have finiteCover := allowed.resolve_left maximal
      simp only [startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad value), getterResult,
        State.transferFromLP, ite_eq_right maximal, ite_eq_left finiteCover, nonstatic,
        State.transferLP, ite_eq_left cover, ite_eq_right wrapped, Frame.finishLP,
        Frame.fail, Option.some.injEq] at accepted
      cases accepted
  rw [transferFrom_startImmediate_done value allowed nonstatic cover nowrap] at accepted
  have fields := SegmentResult.finished.inj (Option.some.inj accepted)
  exact ⟨value, allowed, nonstatic, cover, nowrap, fields.1.symm, fields.2.symm⟩

theorem WriterRep.transferFrom_public_fixed {K : WriterKey → Prop} {st : State}
    {sevm : Sevm} {b : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm))) :
    ∀ n, n ∈ writerFixedSlots →
      ((transferFromPublicPost sevm b [0x23b872dd] getterInitMemory G).getStor sevm.currentTarget).get n =
        (b.getStor sevm.currentTarget).get n := by
  have extended := rep.extend fresh
  have allowanceKey : WriterExtend K
      (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm))
      (.allowance (transferFromOwner sevm) sevm.caller) := .inr (List.mem_cons.mpr (.inl rfl))
  have ownerKey : WriterExtend K
      (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm))
      (.balance (transferFromOwner sevm)) := .inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl))))
  have recipientKey : WriterExtend K
      (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm))
      (.balance (transferFromRecipient sevm)) :=
    .inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl)))))
  have allowanceOff := extended.apart (.allowance (transferFromOwner sevm) sevm.caller) allowanceKey
  have ownerOff := extended.apart (.balance (transferFromOwner sevm)) ownerKey
  have recipientOff := extended.apart (.balance (transferFromRecipient sevm)) recipientKey
  change transferFromAllowanceSlot (transferFromOwner sevm) sevm.caller ∉ writerFixedSlots at allowanceOff
  change transferBalanceSlot (transferFromOwner sevm) ∉ writerFixedSlots at ownerOff
  change transferBalanceSlot (transferFromRecipient sevm) ∉ writerFixedSlots at recipientOff
  have facts := transferFromPublicPost_facts (sevm := sevm) (b := b)
    (R := [0x23b872dd]) (G := G) getterInitMemory_ptr
  intro n fixed
  rw [facts.2.2.1]
  rw [Stor.get_set_ne _ (k := transferBalanceSlot (transferFromRecipient sevm)) (a := n)
    (fun eq => recipientOff (eq.symm ▸ fixed)),
    Stor.get_set_ne _ (k := transferBalanceSlot (transferFromOwner sevm)) (a := n)
    (fun eq => ownerOff (eq.symm ▸ fixed))]
  unfold transferFromBalanceBase
  split
  · rw [transferFromFirst, transferFromFirstBase, afterSload_getStor]
  · rw [transferFromStored, transferFromStoreBase, afterSstore_getStor_self,
      transferFromSecond, transferFromSecondBase, afterSload_getStor,
      transferFromFirst, transferFromFirstBase, afterSload_getStor]
    exact Stor.get_set_ne _ (k := transferFromAllowanceSlot (transferFromOwner sevm) sevm.caller)
      (a := n) (fun eq => allowanceOff (eq.symm ▸ fixed)) _

theorem transferFromAllowanceState_zero (st : State) (owner spender : Adr) :
    transferFromAllowanceState st owner spender 0 = st := by
  unfold transferFromAllowanceState
  split
  · rfl
  · rw [B256.sub_zero]
    have unchanged : Function.update st.allowance owner
        (Function.update (st.allowance owner) spender (st.allowance owner spender)) = st.allowance := by
      funext o p
      by_cases sameOwner : o = owner
      · subst o
        rw [Function.update_self]
        by_cases sameSpender : p = spender
        · subst p
          rw [Function.update_self]
        · rw [Function.update_of_ne sameSpender]
      · rw [Function.update_of_ne sameOwner]
    unfold approveSourceState
    rw [unchanged]

theorem transferFromSourceFrame_prefix (current : Checkpoint) (ctx : Context)
    (owner recipient : Adr) (amount : B256) :
    (transferFromSourceFrame current ctx owner recipient amount).context = ctx ∧
    (transferFromSourceFrame current ctx owner recipient amount).checkpoint = current ∧
    (transferFromSourceFrame current ctx owner recipient amount).current.logs = current.logs ++
      [.owned (writerEntryOrigin ctx) (.transfer owner recipient amount)] ∧
    (transferFromSourceFrame current ctx owner recipient amount).current.updates = current.updates ∧
    (transferFromSourceFrame current ctx owner recipient amount).segment = 0 ∧
    (transferFromSourceFrame current ctx owner recipient amount).afterCall = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The finite source result keeps physical metadata exact and source provenance explicit. -/
structure TransferFromSourceResult (K : WriterKey → Prop) (current : Checkpoint)
    (invocation : List Nat) (sevm : Sevm) (b post : Devm) (residual : Nat) : Prop where
  rawPost : post = transferFromPublicPost sevm b [0x23b872dd] getterInitMemory residual
  representation : WriterRep
    (WriterExtend K (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm)))
    (post.getStor sevm.currentTarget)
    (transferFromSourceState current.state (transferFromOwner sevm) sevm.caller
      (transferFromRecipient sevm) (transferFromAmount sevm))
  accepted : startImmediate current (writerContext sevm invocation) (transferFromDecodedEntry sevm) =
    some (.finished (transferFromSourceFrame current (writerContext sevm invocation)
      (transferFromOwner sevm) (transferFromRecipient sevm) (transferFromAmount sevm)) (encodeWords [1]))
  done : drive 2 (startTyped current (writerContext sevm invocation) (transferFromDecodedEntry sevm)) .done =
    transferFromSourceDone current (writerContext sevm invocation)
      (transferFromOwner sevm) (transferFromRecipient sevm) (transferFromAmount sevm)
  context : (transferFromSourceFrame current (writerContext sevm invocation)
    (transferFromOwner sevm) (transferFromRecipient sevm) (transferFromAmount sevm)).context = writerContext sevm invocation
  checkpoint : (transferFromSourceFrame current (writerContext sevm invocation)
    (transferFromOwner sevm) (transferFromRecipient sevm) (transferFromAmount sevm)).checkpoint = current
  sourceLogs : (transferFromSourceFrame current (writerContext sevm invocation)
    (transferFromOwner sevm) (transferFromRecipient sevm) (transferFromAmount sevm)).current.logs = current.logs ++
      [.owned (writerEntryOrigin (writerContext sevm invocation))
        (.transfer (transferFromOwner sevm) (transferFromRecipient sevm) (transferFromAmount sevm))]
  updates : (transferFromSourceFrame current (writerContext sevm invocation)
    (transferFromOwner sevm) (transferFromRecipient sevm) (transferFromAmount sevm)).current.updates = current.updates
  sourceState : (transferFromSourceFrame current (writerContext sevm invocation)
    (transferFromOwner sevm) (transferFromRecipient sevm) (transferFromAmount sevm)).current.state =
      transferFromSourceState current.state (transferFromOwner sevm) sevm.caller
        (transferFromRecipient sevm) (transferFromAmount sevm)
  segment : (transferFromSourceFrame current (writerContext sevm invocation)
    (transferFromOwner sevm) (transferFromRecipient sevm) (transferFromAmount sevm)).segment = 0
  afterCall : (transferFromSourceFrame current (writerContext sevm invocation)
    (transferFromOwner sevm) (transferFromRecipient sevm) (transferFromAmount sevm)).afterCall = none
  output : post.output = encodeWords [1]
  logs : post.logs = b.logs ++ [transferRawLog sevm.currentTarget (transferFromOwner sevm)
    (transferFromRecipient sevm) (transferFromAmount sevm)]
  storage : post.getStor sevm.currentTarget =
    (((transferFromBalanceBase sevm b).getStor sevm.currentTarget).set
      (transferBalanceSlot (transferFromOwner sevm)) (transferFromDebitWord sevm b)).set
      (transferBalanceSlot (transferFromRecipient sevm)) (transferFromCreditWord sevm b + transferFromAmount sevm)
  foreign : ∀ a, a ≠ sevm.currentTarget → post.getStor a = b.getStor a
  gas : post.gasLeft = residual
  fixed : ∀ n, n ∈ writerFixedSlots → (post.getStor sevm.currentTarget).get n =
    (b.getStor sevm.currentTarget).get n
  movement : Blanc.Transfer current.state.balanceOf (transferFromOwner sevm) (transferFromAmount sevm)
    (transferFromRecipient sevm)
    (transferFromSourceState current.state (transferFromOwner sevm) sevm.caller
      (transferFromRecipient sevm) (transferFromAmount sevm)).balanceOf
  self : transferFromRecipient sevm = transferFromOwner sevm →
    transferFromSourceState current.state (transferFromOwner sevm) sevm.caller
      (transferFromRecipient sevm) (transferFromAmount sevm) =
      transferFromAllowanceState current.state (transferFromOwner sevm) sevm.caller (transferFromAmount sevm)
  zero : transferFromAmount sevm = 0 →
    transferFromSourceState current.state (transferFromOwner sevm) sevm.caller
      (transferFromRecipient sevm) (transferFromAmount sevm) = current.state

theorem transferFrom_public_source_result {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : WriterFreshKeys K (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm)))
    (value : sevm.value = 0) (allowed : transferFromAllowanceSafe sevm b)
    (nonstatic : sevm.isStatic = false)
    (cover : transferFromAmount sevm ≤ transferSourceWord sevm (transferFromBalanceBase sevm b) (transferFromOwner sevm))
    (nowrap : transferFromCreditSafe sevm b) :
    TransferFromSourceResult K current invocation sevm b
      (transferFromPublicPost sevm b [0x23b872dd] getterInitMemory G) G := by
  have allowances := transferFrom_allowance_reads rep fresh
  have balances := transferFrom_balance_reads rep fresh
  have sourceAllowed : current.state.allowance (transferFromOwner sevm) sevm.caller = B256.max ∨
      transferFromAmount sevm ≤ current.state.allowance (transferFromOwner sevm) sevm.caller := by
    rcases allowed with maximal | finiteCover
    · exact .inl (allowances.1.symm.trans maximal)
    · exact .inr (allowances.2 ▸ finiteCover)
  have covered : transferFromAmount sevm ≤ current.state.balanceOf (transferFromOwner sevm) := by
    rwa [balances.1] at cover
  have safe : (Blanc.ledgerDebit current.state.balanceOf (transferFromOwner sevm) (transferFromAmount sevm)
      (transferFromRecipient sevm)).toNat + (transferFromAmount sevm).toNat < 2 ^ 256 := by
    unfold transferFromCreditSafe at nowrap
    rwa [balances.2] at nowrap
  have sourceFacts := transferFromSourceFrame_prefix current (writerContext sevm invocation)
    (transferFromOwner sevm) (transferFromRecipient sevm) (transferFromAmount sevm)
  have facts := transferFromPublicPost_facts (sevm := sevm) (b := b)
    (R := [0x23b872dd]) (G := G) getterInitMemory_ptr
  refine {
    rawPost := rfl
    representation := rep.transferFrom_public_post fresh
    accepted := transferFrom_startImmediate_done value sourceAllowed nonstatic covered safe
    done := transferFrom_drive_done value sourceAllowed nonstatic covered safe
    context := sourceFacts.1
    checkpoint := sourceFacts.2.1
    sourceLogs := sourceFacts.2.2.1
    updates := sourceFacts.2.2.2.1
    sourceState := rfl
    segment := sourceFacts.2.2.2.2.1
    afterCall := sourceFacts.2.2.2.2.2
    output := facts.1
    logs := facts.2.1
    storage := facts.2.2.1
    foreign := facts.2.2.2.1
    gas := facts.2.2.2.2
    fixed := rep.transferFrom_public_fixed fresh
    movement := ?_
    self := ?_
    zero := ?_ }
  · dsimp only [transferFromSourceState, transferSourceState]
    rw [transferFromAllowanceState_balance]
    exact Blanc.ledgerDebit_credit_transfer covered
  · intro same
    unfold transferFromSourceState
    rw [same]
    exact transferSourceState_self _ _ _
  · intro zero
    unfold transferFromSourceState
    rw [zero, transferFromAllowanceState_zero]
    exact transferSourceState_zero _ _ _

/-- Actual raw pc-zero success derives source acceptance; no desired endpoint is a premise. -/
theorem transferFrom_bytecode_refines_source {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : WriterFreshKeys K (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm)))
    (representable : sevm.data.length < 2 ^ 256)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x23b872dd)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ 100 ≤ sevm.data.length ∧ sevm.isStatic = false ∧
      ∃ residual, TransferFromSourceResult K current invocation sevm b post residual := by
  obtain ⟨value, size, guard, allowed, cover, nonstatic, nowrap, residual, eq⟩ :=
    transferFrom_bytecode_refines_raw codeEq fork selector run
  refine ⟨value, (Blanc.Lift.word_calldata_guards_iff (n := 96) representable (by decide)).mp ⟨size, guard⟩,
    nonstatic, residual, ?_⟩
  rw [eq]
  exact transferFrom_public_source_result rep fresh value allowed nonstatic cover nowrap

/-- Existing handler acceptance constructs exact bytecode gas with every incoming store sentry. -/
theorem transferFrom_source_bytecode_exact {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b : Devm} {G : Nat}
    {sourceFrame : Frame} {returndata : Bytes}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : WriterFreshKeys K (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm)))
    (representable : sevm.data.length < 2 ^ 256) (length : 100 ≤ sevm.data.length)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x23b872dd)
    (allowanceSentry : ¬ transferFromMaximal sevm b →
      gCallStipend < G + transferFromAllowanceCharge sevm b + transferFromSourceCharge sevm b +
        transferFromDebitCharge sevm b + transferFromRecipientCharge sevm b + transferFromCreditCharge sevm b + 2431)
    (debitSentry : gCallStipend < G + transferFromDebitCharge sevm b +
      transferFromRecipientCharge sevm b + transferFromCreditCharge sevm b + 2154)
    (creditSentry : gCallStipend < G + transferFromCreditCharge sevm b + 1914)
    (accepted : startImmediate current (writerContext sevm invocation) (transferFromDecodedEntry sevm) =
      some (.finished sourceFrame returndata)) :
    SProg.RunExact cert.prog sevm (St b [] Mem.empty (G + transferFromPublicGas sevm b))
      (transferFromPublicPost sevm b [0x23b872dd] getterInitMemory G) ∧
    Nonempty (Exec 0 sevm (St b [] Mem.empty (G + transferFromPublicGas sevm b))
      (.ok (transferFromPublicPost sevm b [0x23b872dd] getterInitMemory G))) ∧
    sourceFrame = transferFromSourceFrame current (writerContext sevm invocation)
      (transferFromOwner sevm) (transferFromRecipient sevm) (transferFromAmount sevm) ∧
    returndata = encodeWords [1] ∧
    TransferFromSourceResult K current invocation sevm b
      (transferFromPublicPost sevm b [0x23b872dd] getterInitMemory G) G := by
  obtain ⟨value, sourceAllowed, nonstatic, covered, safe, frameEq, dataEq⟩ := transferFrom_startImmediate_inv accepted
  obtain ⟨size, guard⟩ := (Blanc.Lift.word_calldata_guards_iff (n := 96) representable (by decide)).mpr length
  have allowances := transferFrom_allowance_reads rep fresh
  have balances := transferFrom_balance_reads rep fresh
  have allowed : transferFromAllowanceSafe sevm b := by
    rcases sourceAllowed with maximal | finiteCover
    · exact .inl (allowances.1.trans maximal)
    · exact .inr (allowances.2.symm ▸ finiteCover)
  have cover : transferFromAmount sevm ≤ transferSourceWord sevm (transferFromBalanceBase sevm b) (transferFromOwner sevm) := by
    rw [balances.1]
    exact covered
  have nowrap : transferFromCreditSafe sevm b := by
    unfold transferFromCreditSafe
    rw [balances.2]
    exact safe
  exact ⟨transferFrom_pc0_exact fork value size selector guard allowed allowanceSentry debitSentry creditSentry nonstatic cover nowrap,
    transferFrom_bytecode_live_raw codeEq fork value size selector guard allowed allowanceSentry debitSentry creditSentry nonstatic cover nowrap,
    frameEq, dataEq, transferFrom_public_source_result rep fresh value allowed nonstatic cover nowrap⟩

/-- Successful raw pc0 execution derives exact consumption for the typed transferFrom entry. -/
theorem transferFrom_bytecode_exact_consumes {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : WriterFreshKeys K (transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm)))
    (representable : sevm.data.length < 2 ^ 256)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x23b872dd)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ 100 ≤ sevm.data.length ∧ sevm.isStatic = false ∧
      ∃ residual, TransferFromSourceResult K current invocation sevm b post residual ∧
        ExactConsumes (startTyped current (writerContext sevm invocation) (transferFromDecodedEntry sevm)) .done
          { status := .success post.output,
            frame := transferFromSourceFrame current (writerContext sevm invocation)
              (transferFromOwner sevm) (transferFromRecipient sevm) (transferFromAmount sevm),
            remaining := .done, childReturns := [] } := by
  obtain ⟨value, size, nonstatic, residual, result⟩ :=
    transferFrom_bytecode_refines_source rep fresh representable codeEq fork selector run
  have typed : startTyped current (writerContext sevm invocation) (transferFromDecodedEntry sevm) =
      .finished (transferFromSourceFrame current (writerContext sevm invocation)
        (transferFromOwner sevm) (transferFromRecipient sevm) (transferFromAmount sevm)) post.output := by
    unfold startTyped
    rw [result.accepted]
    dsimp only []
    rw [← result.output]
  refine ⟨value, size, nonstatic, residual, result, ?_⟩
  rw [typed]
  exact ExactConsumes.finished (transferFromSourceFrame current (writerContext sevm invocation)
    (transferFromOwner sevm) (transferFromRecipient sevm) (transferFromAmount sevm)) post.output

end Blanc.Lift.UniswapV2Pair
