-- Exact functional observations for successful WETH10 flash loans.

import Blanc.Weth10Functional
import Blanc.Weth10StateFunctional
import Blanc.Weth10StateSound
import Blanc.Ladder

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Weth10

/-! ## Public selector route -/

/-- The public selector word for `flashLoan(address,address,uint256,bytes)`.
It remains unreduced: proofs use positional membership and never reduce Keccak. -/
def flashLoanSelector : B256 :=
  selector "flashLoan" [.address, .address, .uint256, .dynBytes]

/-- `flashLoan` is the eleventh deployed WETH10 selector. -/
lemma flashLoan_mem_weth10Funcs (dp : DeployParams) :
    (flashLoanSelector, nonpayable flashLoan) ∈ weth10Funcs dp := by
  simp only [weth10Funcs, flashLoanSelector]
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))))))))

/-! ## Canonical callback image -/

/-- `storeFlashCallbackHead`, with each of its six complete-word writes. -/
lemma of_storeFlashCallbackHead_val {e : Sevm} {s s' : Devm} {x xs}
    (hp : x :: xs <<+ s.stack)
    (h : Line.Run e s storeFlashCallbackHead s') :
    (xs <<+ s'.stack) ∧
      s'.memory =
        ((((((s.memory.write 0 onFlashLoanSelector.toBytes).write
          32 e.caller.toB256.toBytes).write
          64 e.currentTarget.toB256.toBytes).write
          96 x.toBytes).write
          128 (0 : B256).toBytes).write
          160 (0xa0 : B256).toBytes) := by
  simp only [storeFlashCallbackHead] at h
  rcases Line.of_run_cons h with ⟨t1, q1, h⟩
  have hb1 := of_run_pushB256 q1
  have hp1 : onFlashLoanSelector :: x :: xs <<+ t1.stack :=
    prefix_of_push hb1 hp
  rcases of_run_append (mstoreAt 0) h with ⟨t2, q2, h⟩
  rcases of_run_mstoreAt_val q2 hp1 with ⟨hp2, hm2⟩
  have e2 : t2.memory = s.memory.write 0 onFlashLoanSelector.toBytes := by
    rw [hm2, ← hb1.memory]
    rfl
  rcases Line.of_run_cons h with ⟨t3, q3, h⟩
  have hb3 := of_run_caller q3
  have hp3 : e.caller.toB256 :: x :: xs <<+ t3.stack :=
    prefix_of_push hb3 hp2
  rcases of_run_append (mstoreAt 1) h with ⟨t4, q4, h⟩
  rcases of_run_mstoreAt_val q4 hp3 with ⟨hp4, hm4⟩
  have e4 : t4.memory =
      (s.memory.write 0 onFlashLoanSelector.toBytes).write
        32 e.caller.toB256.toBytes := by
    rw [hm4, ← hb3.memory, e2]
    rfl
  rcases Line.of_run_cons h with ⟨t5, q5, h⟩
  have hb5 := of_run_address q5
  have hp5 : e.currentTarget.toB256 :: x :: xs <<+ t5.stack :=
    prefix_of_push hb5 hp4
  rcases of_run_append (mstoreAt 2) h with ⟨t6, q6, h⟩
  rcases of_run_mstoreAt_val q6 hp5 with ⟨hp6, hm6⟩
  have e6 : t6.memory =
      ((s.memory.write 0 onFlashLoanSelector.toBytes).write
        32 e.caller.toB256.toBytes).write
        64 e.currentTarget.toB256.toBytes := by
    rw [hm6, ← hb5.memory, e4]
    rfl
  rcases of_run_append (mstoreAt 3) h with ⟨t7, q7, h⟩
  rcases of_run_mstoreAt_val q7 hp6 with ⟨hp7, hm7⟩
  have e7 : t7.memory =
      (((s.memory.write 0 onFlashLoanSelector.toBytes).write
        32 e.caller.toB256.toBytes).write
        64 e.currentTarget.toB256.toBytes).write 96 x.toBytes := by
    rw [hm7, e6]
    rfl
  rcases Line.of_run_cons h with ⟨t8, q8, h⟩
  have hb8 := of_run_pushB256 q8
  have hp8 : (0 : B256) :: xs <<+ t8.stack :=
    prefix_of_push hb8 hp7
  rcases of_run_append (mstoreAt 4) h with ⟨t9, q9, h⟩
  rcases of_run_mstoreAt_val q9 hp8 with ⟨hp9, hm9⟩
  have e9 : t9.memory =
      ((((s.memory.write 0 onFlashLoanSelector.toBytes).write
        32 e.caller.toB256.toBytes).write
        64 e.currentTarget.toB256.toBytes).write
        96 x.toBytes).write 128 (0 : B256).toBytes := by
    rw [hm9, ← hb8.memory, e7]
    rfl
  rcases Line.of_run_cons h with ⟨t10, q10, h⟩
  have hb10 := of_run_pushB256 q10
  have hp10 : (0xa0 : B256) :: xs <<+ t10.stack :=
    prefix_of_push hb10 hp9
  rcases of_run_mstoreAt_val h hp10 with ⟨hp11, hm11⟩
  exact ⟨hp11, by rw [hm11, ← hb10.memory, e9]; rfl⟩

/-- The callback-size line computes `0xc4 + ceil32(data.length)` as a word. -/
lemma of_flashCallbackArgsSize_val {e : Sevm} {s s' : Devm} {x xs}
    (hp : x :: xs <<+ s.stack)
    (h : Line.Run e s flashCallbackArgsSize s') :
    (0xc4 + ((~~~ (31 : B256)) &&& (31 + x))) :: xs <<+ s'.stack := by
  simp only [flashCallbackArgsSize] at h
  rcases Line.of_run_cons h with ⟨u1, q1, h⟩
  have hp1 : (31 : B256) :: x :: xs <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp
  rcases Line.of_run_cons h with ⟨u2, q2, h⟩
  have hp2 := prefix_of_add q2 hp1
  rcases Line.of_run_cons h with ⟨u3, q3, h⟩
  have hp3 : (31 : B256) :: (31 + x) :: xs <<+ u3.stack :=
    prefix_of_push (of_run_pushB256 q3) hp2
  rcases Line.of_run_cons h with ⟨u4, q4, h⟩
  have hp4 := prefix_of_not q4 hp3
  rcases Line.of_run_cons h with ⟨u5, q5, h⟩
  have hp5 := prefix_of_and q5 hp4
  rcases Line.of_run_cons h with ⟨u6, q6, h⟩
  have hp6 : (0xc4 : B256) :: ((~~~ (31 : B256)) &&& (31 + x)) :: xs <<+
      u6.stack := prefix_of_push (of_run_pushB256 q6) hp5
  rcases Line.of_run_cons h with ⟨u7, q7, hnil⟩
  cases hnil
  exact prefix_of_add q7 hp6

/-- The computed callback-size word denotes the canonical encoding length. -/
lemma toNat_flashCallbackArgsSize {len : Nat}
    (h : 196 + ceil32 len < 2 ^ 256) :
    ((0xc4 : B256) + ((~~~ (31 : B256)) &&& (31 + Nat.toB256 len))).toNat
      = 196 + ceil32 len := by
  have hlen : 31 + len < 2 ^ 256 := by
    have := Nat.le_ceil32 len
    omega
  rw [B256.toNat_add, B256.toNat_ceil32 hlen,
    show B256.toNat 0xc4 = 196 from rfl, Nat.lo_eq_of_lt h]

/-- The callback write chain over a fresh frame image, byte for byte. -/
lemma flashCallbackImage_nil (sel cal slf amt lenw : B256)
    (payload : Bytes) :
    Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
        (Bytes.writeAt [] 0 amt.toBytes) 0 sel.toBytes) 32 cal.toBytes)
        64 slf.toBytes) 96 amt.toBytes) 128 (0 : B256).toBytes)
        160 (0xa0 : B256).toBytes) 192 lenw.toBytes) 224 payload
      = sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes ++
        (0 : B256).toBytes ++ (0xa0 : B256).toBytes ++ lenw.toBytes ++
        payload := by
  have hlen : ∀ x : B256, (B256.toBytes x).length = 32 :=
    B256.length_toBytes
  have e0 : Bytes.writeAt ([] : Bytes) 0 amt.toBytes = amt.toBytes :=
    Bytes.writeAt_zero_of_le (by simp)
  have e1 : Bytes.writeAt amt.toBytes 0 sel.toBytes = sel.toBytes :=
    Bytes.writeAt_zero_of_le (by rw [hlen, hlen])
  have e2 : Bytes.writeAt sel.toBytes 32 cal.toBytes =
      sel.toBytes ++ cal.toBytes :=
    Bytes.writeAt_of_length_eq (hlen sel)
  have e3 : Bytes.writeAt (sel.toBytes ++ cal.toBytes) 64 slf.toBytes =
      sel.toBytes ++ cal.toBytes ++ slf.toBytes :=
    Bytes.writeAt_of_length_eq (by simp [hlen])
  have e4 : Bytes.writeAt
      (sel.toBytes ++ cal.toBytes ++ slf.toBytes) 96 amt.toBytes =
      sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes :=
    Bytes.writeAt_of_length_eq (by simp [hlen])
  have e5 : Bytes.writeAt
      (sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes)
      128 (0 : B256).toBytes =
      sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes ++
        (0 : B256).toBytes :=
    Bytes.writeAt_of_length_eq (by simp [hlen])
  have e6 : Bytes.writeAt
      (sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes ++
        (0 : B256).toBytes) 160 (0xa0 : B256).toBytes =
      sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes ++
        (0 : B256).toBytes ++ (0xa0 : B256).toBytes :=
    Bytes.writeAt_of_length_eq (by simp [hlen])
  have e7 : Bytes.writeAt
      (sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes ++
        (0 : B256).toBytes ++ (0xa0 : B256).toBytes)
      192 lenw.toBytes =
      sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes ++
        (0 : B256).toBytes ++ (0xa0 : B256).toBytes ++ lenw.toBytes :=
    Bytes.writeAt_of_length_eq (by simp [hlen])
  have e8 : Bytes.writeAt
      (sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes ++
        (0 : B256).toBytes ++ (0xa0 : B256).toBytes ++ lenw.toBytes)
      224 payload =
      sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes ++
        (0 : B256).toBytes ++ (0xa0 : B256).toBytes ++ lenw.toBytes ++
        payload :=
    Bytes.writeAt_of_length_eq (by simp [hlen])
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8]

/-- The call window is the canonical ERC-3156 callback encoding, including
derived zero padding after the dynamic payload. -/
lemma flashCallbackWindow (sel cal slf amt : B256) (payload : Bytes) :
    (sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes ++
      (0 : B256).toBytes ++ (0xa0 : B256).toBytes ++
      (Nat.toB256 payload.length).toBytes ++ payload).sliceD
        28 (196 + ceil32 payload.length) 0 =
      abiCallWithTail sel [cal, slf, amt, 0] payload := by
  have hlen : ∀ x : B256, (B256.toBytes x).length = 32 :=
    B256.length_toBytes
  have hce : payload.length ≤ ceil32 payload.length := Nat.le_ceil32 _
  have himg :
      (sel.toBytes ++ cal.toBytes ++ slf.toBytes ++ amt.toBytes ++
        (0 : B256).toBytes ++ (0xa0 : B256).toBytes ++
        (Nat.toB256 payload.length).toBytes ++ payload) =
      sel.toBytes ++ (cal.toBytes ++ slf.toBytes ++ amt.toBytes ++
        (0 : B256).toBytes ++ (0xa0 : B256).toBytes ++
        (Nat.toB256 payload.length).toBytes ++ payload) := by
    simp [List.append_assoc]
  unfold List.sliceD
  rw [himg, List.drop_append_of_le_length (by rw [hlen]; omega)]
  rw [List.takeD_of_length_le]
  · simp only [abiCallWithTail, abiBytesTail, abiSelectorBytes, List.map,
      List.flatten, List.length_cons, List.length_nil, List.append_assoc,
      List.length_append, hlen, List.length_drop]
    rw [show 196 + ceil32 payload.length -
        (32 - 28 + (32 + (32 + (32 + (32 + (32 +
          (32 + payload.length))))))) =
        ceil32 payload.length - payload.length from by omega]
    norm_num
    rfl
  · simp only [List.length_append, List.length_drop, hlen]
    omega

/-! ## Callback boundary -/

/-- The successful borrower boundary before imposing any ABI-canonicality
assumption on the dynamic tail.  `inputSize` is the runtime word produced by
`flashCallbackArgsSize`; `callbackInput` is the byte string actually read from
memory with its modular `toNat` length. -/
def RawFlashCallbackBoundary (sevm : Sevm) (self receiver : Adr)
    (amount inputSize : B256) (callbackInput : Bytes)
    (pre mid : Devm) : Prop :=
  ∃ (parent child : Devm) (xl : Xlot) (delegated : Bool)
    (na : Adr) (code : ByteArray) (gasWord : B256) (avail : Nat),
    0 < sevm.depth ∧
    pre.stack =
      gasWord :: receiver.toB256 :: (0 : B256) :: callbackArgsOffset ::
        inputSize :: (0 : B256) :: (0 : B256) :: parent.stack ∧
    [amount, receiver.toB256] <<+ parent.stack ∧
    parent.state = pre.state ∧
    parent.memory = pre.memory.extends
      [(callbackArgsOffset.toNat, inputSize.toNat), (0, 0)] ∧
    parent.logs = pre.logs ∧
    parent.output = pre.output ∧
    ((getDelegatedCodeAddress (pre.getCode receiver) = none ∧
        na = receiver ∧ code = pre.getCode receiver ∧ delegated = false) ∨
      (∃ target,
        getDelegatedCodeAddress (pre.getCode receiver) = some target ∧
        na = target ∧ code = pre.getCode target ∧ delegated = true)) ∧
    Xlot.Filled xl ∧
    ProcessMessage
      (callMsg sevm parent (min gasWord.toNat (except64th avail)) 0
        self receiver na true false callbackInput code delegated)
      xl (.ok child) ∧
    child.error.isSome = false ∧
    32 ≤ child.output.length ∧
    Bytes.toB256 (child.output.sliceD 0 32 0) = CALLBACK_SUCCESS ∧
    (Resume.call parent 0 0).run (.ok child) = .ok mid ∧
    mid.state = child.state ∧
    mid.returnData = child.output ∧
    mid.stack = (1 : B256) :: parent.stack ∧
    mid.logs = pre.logs ++ child.logs ∧
    mid.output = pre.output

/-- `RawFlashCallbackBoundary` with the exact parent instruction step that
spawned the borrower slot. -/
def RawFlashCallbackStepBoundary (sevm : Sevm) (self receiver : Adr)
    (amount inputSize : B256) (callbackInput : Bytes)
    (pre mid : Devm) : Prop :=
  ∃ (parent child : Devm) (xl : Xlot) (delegated : Bool)
    (na : Adr) (code : ByteArray) (gasWord : B256) (avail pc : Nat),
    Ninst.StepRun pc sevm pre call xl (.ok mid) ∧
    0 < sevm.depth ∧
    pre.stack =
      gasWord :: receiver.toB256 :: (0 : B256) :: callbackArgsOffset ::
        inputSize :: (0 : B256) :: (0 : B256) :: parent.stack ∧
    [amount, receiver.toB256] <<+ parent.stack ∧
    parent.state = pre.state ∧
    parent.memory = pre.memory.extends
      [(callbackArgsOffset.toNat, inputSize.toNat), (0, 0)] ∧
    parent.logs = pre.logs ∧
    parent.output = pre.output ∧
    ((getDelegatedCodeAddress (pre.getCode receiver) = none ∧
        na = receiver ∧ code = pre.getCode receiver ∧ delegated = false) ∨
      (∃ target,
        getDelegatedCodeAddress (pre.getCode receiver) = some target ∧
        na = target ∧ code = pre.getCode target ∧ delegated = true)) ∧
    Xlot.Filled xl ∧
    ProcessMessage
      (callMsg sevm parent (min gasWord.toNat (except64th avail)) 0
        self receiver na true false callbackInput code delegated)
      xl (.ok child) ∧
    child.error.isSome = false ∧
    32 ≤ child.output.length ∧
    Bytes.toB256 (child.output.sliceD 0 32 0) = CALLBACK_SUCCESS ∧
    (Resume.call parent 0 0).run (.ok child) = .ok mid ∧
    mid.state = child.state ∧
    mid.returnData = child.output ∧
    mid.stack = (1 : B256) :: parent.stack ∧
    mid.logs = pre.logs ++ child.logs ∧
    mid.output = pre.output

/-- Compatibility projection that forgets only the parent instruction step. -/
theorem RawFlashCallbackStepBoundary.toRaw
    {sevm : Sevm} {self receiver : Adr} {amount inputSize : B256}
    {callbackInput : Bytes} {pre mid : Devm}
    (h : RawFlashCallbackStepBoundary sevm self receiver amount inputSize
      callbackInput pre mid) :
    RawFlashCallbackBoundary sevm self receiver amount inputSize
      callbackInput pre mid := by
  rcases h with
    ⟨parent, child, xl, delegated, na, code, gasWord, avail, pc, _hstep,
      hdepth, hstack, hpref, hstate, hmemory, hlogs, houtput,
      hdelegation, hfilled, hprocess, hclean, hlength, hmagic, hresume,
      hmidState, hreturndata, hmidStack, hmidLogs, hmidOutput⟩
  exact ⟨parent, child, xl, delegated, na, code, gasWord, avail, hdepth,
    hstack, hpref, hstate, hmemory, hlogs, houtput, hdelegation, hfilled,
    hprocess, hclean, hlength, hmagic, hresume, hmidState, hreturndata,
    hmidStack, hmidLogs, hmidOutput⟩

/-- The raw callback boundary contributes the successful child's exact log
segment to the enclosing frame. -/
lemma RawFlashCallbackBoundary.exists_log_segment
    {sevm : Sevm} {self receiver : Adr} {amount inputSize : B256}
    {callbackInput : Bytes} {pre mid : Devm}
    (h : RawFlashCallbackBoundary sevm self receiver amount inputSize
      callbackInput pre mid) :
    ∃ callbackLogs : List Log, mid.logs = pre.logs ++ callbackLogs := by
  rcases h with ⟨parent, child, xl, delegated, na, code, gasWord, avail,
    hdepth, hstack, hpref, hstate, hmemory, hparentLogs, hparentOutput,
    hdelegation, hfilled, hprocess, hclean, hlength, hmagic, hresume,
    hmidState, hreturndata, hmidStack, hmidLogs, hmidOutput⟩
  exact ⟨child.logs, hmidLogs⟩

/-- The exact successful suffix of `flashLoan` beginning at its borrower
`CALL`.  It is named locally so the functional layer remains independent of
the state-soundness proof's internal factoring. -/
def flashLoanSuccessTail : Func :=
  call ::: iszero :::
  (.call bubbleRevertSlot) <?>
  (returnDataShorterThan 32 +++
    Func.revert <?>
    (checkReturnDataHead CALLBACK_SUCCESS 0 +++ iszero :::
      (.call flashFailedErrorSlot) <?>
      (pop ::: pop ::: .call flashSettleSlot)))

/-- A clean callback frame entered with the canonical ERC-3156 calldata,
returned WETH10's locked magic word, and contributed exactly its own log
segment between the outer mint and repayment logs. -/
def FlashCallbackBoundary (sevm : Sevm) (self receiver : Adr)
    (amount : B256) (data : Bytes) (pre mid : Devm) : Prop :=
  ∃ (parent child : Devm) (xl : Xlot) (delegated : Bool)
    (na : Adr) (code : ByteArray) (gasWord : B256) (avail : Nat),
    0 < sevm.depth ∧
    pre.stack =
      gasWord :: receiver.toB256 :: (0 : B256) :: callbackArgsOffset ::
        Nat.toB256 (196 + ceil32 data.length) :: (0 : B256) ::
        (0 : B256) :: parent.stack ∧
    parent.state = pre.state ∧
    parent.memory = pre.memory.extends
      [(callbackArgsOffset.toNat, 196 + ceil32 data.length), (0, 0)] ∧
    parent.logs = pre.logs ∧
    parent.output = pre.output ∧
    ((getDelegatedCodeAddress (pre.getCode receiver) = none ∧
        na = receiver ∧ code = pre.getCode receiver ∧ delegated = false) ∨
      (∃ target,
        getDelegatedCodeAddress (pre.getCode receiver) = some target ∧
        na = target ∧ code = pre.getCode target ∧ delegated = true)) ∧
    Xlot.Filled xl ∧
    ProcessMessage
      (callMsg sevm parent (min gasWord.toNat (except64th avail)) 0
        self receiver na true false
        (abiCallWithTail onFlashLoanSelector
          [sevm.caller.toB256, self.toB256, amount, 0] data)
        code delegated)
      xl (.ok child) ∧
    child.error.isSome = false ∧
    32 ≤ child.output.length ∧
    Bytes.toB256 (child.output.sliceD 0 32 0) = CALLBACK_SUCCESS ∧
    (Resume.call parent 0 0).run (.ok child) = .ok mid ∧
    mid.state = child.state ∧
    mid.returnData = child.output ∧
    mid.stack = (1 : B256) :: parent.stack ∧
    mid.logs = pre.logs ++ child.logs ∧
    mid.output = pre.output

/-- The callback boundary contributes an otherwise unrestricted child-log
segment to the enclosing WETH10 frame. -/
lemma FlashCallbackBoundary.exists_log_segment
    {sevm : Sevm} {self receiver : Adr} {amount : B256} {data : Bytes}
    {pre mid : Devm}
    (h : FlashCallbackBoundary sevm self receiver amount data pre mid) :
    ∃ callbackLogs : List Log, mid.logs = pre.logs ++ callbackLogs := by
  unfold FlashCallbackBoundary at h
  aesop

/-- Bubbling returndata always terminates by `REVERT`, hence cannot be the
selected arm of a successful flash-loan suffix. -/
private theorem not_run_bubbleRevertFunctional
    {fs : List Func} {e : Sevm} {s r : Devm} :
    ¬ Func.Run fs e s bubbleRevert r := by
  intro run
  simp only [bubbleRevert, Func.revertReturnData] at run
  rcases of_run_next run with ⟨s1, h1, run1⟩
  rcases of_run_next run1 with ⟨s2, h2, run2⟩
  rcases of_run_next run2 with ⟨s3, h3, run3⟩
  rcases of_run_next run3 with ⟨s4, h4, run4⟩
  rcases of_run_next run4 with ⟨s5, h5, run5⟩
  rcases of_run_next run5 with ⟨s6, h6, run6⟩
  cases run6 with
  | last hrun =>
    simp only [Linst.Run, Linst.run] at hrun
    rcases Except.bind_eq_ok hrun with ⟨v1, h1, h2⟩
    rcases Except.bind_eq_ok h2 with ⟨v2, h3, h4⟩
    rcases Except.bind_eq_ok h4 with ⟨v3, h5, h6⟩
    contradiction

/-- A successful conditional whose nonzero arm calls an exact reverting
`revertWith` body necessarily follows the zero continuation. -/
private theorem of_run_branch_call_revertWithFunctional
    {fs : List Func} {e : Sevm} {s r : Devm} {k : Nat}
    {payload : String} {next : Func}
    (hget : fs[k]? = some (Func.revertWith payload))
    (run : Func.Run fs e s ((.call k) <?> next) r) :
    ∃ s', Devm.PopBurn [0] s s' ∧ Func.Run fs e s' next r := by
  rcases of_run_branch run with
    ⟨s', hpop, hnext⟩ |
    ⟨w, s', s'', hnz, hpop, hburn, hcall⟩
  · exact ⟨s', hpop, hnext⟩
  · rcases of_run_call hcall with
      ⟨f, s3, hlookup, hcallBurn, hrev⟩
    have hf : f = Func.revertWith payload := by
      rw [hget] at hlookup
      exact Option.some.inj hlookup.symm
    subst f
    exact absurd hrev Func.not_run_revertWith

/-- The analogous continuation rule for the byte-for-byte bubbling helper. -/
private theorem of_run_branch_call_bubbleFunctional
    {fs : List Func} {e : Sevm} {s r : Devm} {k : Nat} {next : Func}
    (hget : fs[k]? = some bubbleRevert)
    (run : Func.Run fs e s ((.call k) <?> next) r) :
    ∃ s', Devm.PopBurn [0] s s' ∧ Func.Run fs e s' next r := by
  rcases of_run_branch run with
    ⟨s', hpop, hnext⟩ |
    ⟨w, s', s'', hnz, hpop, hburn, hcall⟩
  · exact ⟨s', hpop, hnext⟩
  · rcases of_run_call hcall with
      ⟨f, s3, hlookup, hcallBurn, hbubble⟩
    have hf : f = bubbleRevert := by
      rw [hget] at hlookup
      exact Option.some.inj hlookup.symm
    subst f
    exact absurd hbubble not_run_bubbleRevertFunctional

/-- `RETURNDATACOPY` changes only the stack, gas, and memory. -/
private theorem of_run_returndatacopy_frame
    {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s returndatacopy s') :
    s.logs = s'.logs ∧ s.output = s'.output ∧ s.state = s'.state := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s1⟩, h1, run1⟩
  rcases Except.bind_eq_ok run1 with ⟨⟨di, s2⟩, h2, run2⟩
  rcases Except.bind_eq_ok run2 with ⟨⟨sz, s3⟩, h3, run3⟩
  rcases Except.bind_eq_ok run3 with ⟨s4, h4, h5⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x1, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨x2, p2⟩
  rcases Devm.pop_of_popToNat h3 with ⟨x3, p3⟩
  have hb := Devm.burn_of_chargeGas h4
  split at h5
  · cases h5
  · injection h5 with eq
    rw [← eq]
    exact ⟨(((p1.logs.trans p2.logs).trans p3.logs).trans hb.logs),
      (((p1.output.trans p2.output).trans p3.output).trans hb.output),
      (((p1.state.trans p2.state).trans p3.state).trans hb.state)⟩

/-- `MLOAD` changes only the stack, gas, and memory. -/
private theorem of_run_mload_frame
    {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s mload s') :
    s.logs = s'.logs ∧ s.output = s'.output ∧ s.state = s'.state := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨si, s1⟩, h1, run1⟩
  rcases Except.bind_eq_ok run1 with ⟨s2, h2, run2⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  have hb := Devm.burn_of_chargeGas h2
  have hp := Devm.push_of_push run2
  have hl : s2.logs = (s2.memRead si 32).2.logs := rfl
  have ho : s2.output = (s2.memRead si 32).2.output := rfl
  have hs : s2.state = (s2.memRead si 32).2.state := rfl
  exact ⟨((p1.logs.trans hb.logs).trans hl).trans hp.logs,
    ((p1.output.trans hb.output).trans ho).trans hp.output,
    ((p1.state.trans hb.state).trans hs).trans hp.state⟩

/-- The returndata-length comparison is log- and output-silent. -/
private theorem of_returnDataShorterThan_frame
    {e : Sevm} {s s' : Devm} {n : B256}
    (h : Line.Run e s (returnDataShorterThan n) s') :
    s.logs = s'.logs ∧ s.output = s'.output ∧ s.state = s'.state := by
  simp only [returnDataShorterThan] at h
  rcases Line.of_run_cons h with ⟨u1, q1, h⟩
  have hb1 := of_run_pushB256 q1
  rcases Line.of_run_cons h with ⟨u2, q2, h⟩
  have hb2 := of_run_returndatasize_val q2
  rcases Line.of_run_cons h with ⟨u3, q3, hnil⟩
  cases hnil
  obtain ⟨a, b, hdb⟩ :
      ∃ a b, Devm.DiffBurn [a, b] [B256.ltCheck a b] u2 s' := by
    rcases of_run_reg q3 with ⟨pc, run⟩
    simp only [Rinst.run, Rinst.runCore] at run
    exact Devm.diffBurn_of_applyBinary run
  exact ⟨(hb1.logs.trans hb2.logs).trans hdb.logs,
    (hb1.output.trans hb2.output).trans hdb.output,
    (hb1.state.trans hb2.state).trans hdb.state⟩

/-- The returndata-head copy and comparison preserve logs and outer output. -/
private theorem of_checkReturnDataHead_frame
    {e : Sevm} {s s' : Devm} {w m : B256}
    (h : Line.Run e s (checkReturnDataHead w m) s') :
    s.logs = s'.logs ∧ s.output = s'.output ∧ s.state = s'.state := by
  simp only [checkReturnDataHead, pushList, List.map] at h
  rcases Line.of_run_cons h with ⟨u1, q1, h⟩
  have hb1 := of_run_pushB256 q1
  rcases Line.of_run_cons h with ⟨u2, q2, h⟩
  have hb2 := of_run_pushB256 q2
  rcases Line.of_run_cons h with ⟨u3, q3, h⟩
  have hb3 := of_run_pushB256 q3
  rcases Line.of_run_cons h with ⟨u4, q4, h⟩
  have hf4 := of_run_returndatacopy_frame q4
  rcases Line.of_run_cons h with ⟨u5, q5, h⟩
  have hb5 := of_run_pushB256 q5
  rcases Line.of_run_cons h with ⟨u6, q6, h⟩
  have hf6 := of_run_mload_frame q6
  rcases Line.of_run_cons h with ⟨u7, q7, h⟩
  have hb7 := of_run_pushB256 q7
  rcases Line.of_run_cons h with ⟨u8, q8, hnil⟩
  cases hnil
  obtain ⟨a, b, hdb⟩ :
      ∃ a b, Devm.DiffBurn [a, b] [B256.eqCheck a b] u7 s' := by
    rcases of_run_reg q8 with ⟨pc, run⟩
    simp only [Rinst.run, Rinst.runCore] at run
    exact Devm.diffBurn_of_applyBinary run
  exact ⟨((((((hb1.logs.trans hb2.logs).trans hb3.logs).trans hf4.1).trans
      hb5.logs).trans hf6.1).trans hb7.logs).trans hdb.logs,
    ((((((hb1.output.trans hb2.output).trans hb3.output).trans hf4.2.1).trans
      hb5.output).trans hf6.2.1).trans hb7.output).trans hdb.output,
    ((((((hb1.state.trans hb2.state).trans hb3.state).trans hf4.2.2).trans
      hb5.state).trans hf6.2.2).trans hb7.state).trans hdb.state⟩

/-- A successful callback suffix opens the exact child frame for the modular
runtime size and actual memory bytes, accepts its magic word, and reaches the
unique repayment continuation.  No calldata-canonicality or no-wrap size
assumption is used. -/
theorem of_rawFlashLoanSuccessTail_step
    (dp : DeployParams)
    {sevm : Sevm} {sc r : Devm} {amount : B256}
    {receiver : Adr} {inputSize : B256} {callbackInput : Bytes}
    {gasWord : B256} {img : Bytes}
    (h_stack :
      gasWord :: receiver.toB256 :: (0 : B256) :: callbackArgsOffset ::
      inputSize :: (0 : B256) :: (0 : B256) ::
      [amount, receiver.toB256] <<+ sc.stack)
    (h_wf : Mem.Wf sc.memory)
    (h_reads : Mem.Reads sc.memory img)
    (h_win :
      img.sliceD callbackArgsOffset.toNat inputSize.toNat 0 =
        callbackInput)
    (h_run :
      Func.Run ((weth10 dp).main :: weth10Aux) sevm sc
        flashLoanSuccessTail r) :
    ∃ mid settle,
      RawFlashCallbackStepBoundary sevm sevm.currentTarget receiver
        amount inputSize callbackInput sc mid ∧
      Devm.getStor mid = Devm.getStor settle ∧
      Devm.getBal mid = Devm.getBal settle ∧
      Devm.getCode mid = Devm.getCode settle ∧
      settle.logs = mid.logs ∧
      settle.output = mid.output ∧
      Mem.Wf settle.memory ∧
      (∃ settleImg, Mem.Reads settle.memory settleImg) ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm settle
        flashSettle r := by
  simp only [flashLoanSuccessTail] at h_run
  rcases of_run_next h_run with ⟨mid, r_call, h_run⟩
  rcases of_run_call_val_with_depth_frame h_stack r_call with h_fail | h_ok
  · exfalso
    rcases of_run_next h_run with ⟨s1, r_iz, h_run⟩
    have hp1 := prefix_of_iszero r_iz h_fail.1
    have h_bubble_lookup :
        ((weth10 dp).main :: weth10Aux)[bubbleRevertSlot]? =
          some bubbleRevert := by
      simp [weth10, weth10Aux, bubbleRevertSlot]
    rcases of_run_branch_call_bubbleFunctional h_bubble_lookup h_run with
      ⟨s2, hpb2, -⟩
    have hps2 := hpb2.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hps2
    rw [hps2] at hp1
    have h01 : ((0 : B256) =? 0) = 0 :=
      pref_head_unique hp1 (pref_append [(0 : B256)] s2.stack)
    rw [show ((0 : B256) =? 0) = 1 from by simp [B256.eqCheck]] at h01
    exact B256.zero_ne_one h01.symm
  · rcases h_ok with
      ⟨parent, child, xl, delegated, na, code, avail, pc, hstep,
        hdepth, hstk_eq, hst_par, hmem_par, hlogs_par, houtput_par,
        h_del, h_fill, run_pm, hclean, h_resume, h_mid_state, h_mid_rd,
        h_mid_mem, h_mid_stack⟩
    rw [toAdr_toB256] at h_del run_pm
    have h_cd : (sc.memory.read callbackArgsOffset.toNat
        inputSize.toNat).1 = callbackInput := by
      rw [Mem.Reads.read h_reads, h_win]
    rw [h_cd] at run_pm
    have hp_par : [amount, receiver.toB256] <<+ parent.stack := by
      rw [hstk_eq] at h_stack
      exact cons_pref_cons_inv (cons_pref_cons_inv (cons_pref_cons_inv
        (cons_pref_cons_inv (cons_pref_cons_inv (cons_pref_cons_inv
          (cons_pref_cons_inv h_stack))))))
    have h_mid_mem' : mid.memory = parent.memory := by
      simpa only [show (0 : B256).toNat = 0 from rfl, List.take_zero,
        Mem.write] using h_mid_mem
    have h_wf_mid : Mem.Wf mid.memory := by
      rw [h_mid_mem', hmem_par]
      exact Mem.Wf.extends _ h_wf
    have h_rd_mid : Mem.Reads mid.memory img := by
      rw [h_mid_mem', hmem_par]
      exact Mem.Reads.extends _ h_reads
    have hcleanNot : ¬ child.error.isSome = true := by
      rw [hclean]
      decide
    have h_mid_logs : mid.logs = sc.logs ++ child.logs := by
      rw [Resume.call_logs h_resume, if_neg hcleanNot, hlogs_par]
    have h_mid_output : mid.output = sc.output := by
      rw [Resume.call_output h_resume, houtput_par]
    rcases of_run_next h_run with ⟨s1, r_iz, h_run⟩
    have hp_mid : (1 : B256) :: [amount, receiver.toB256] <<+ mid.stack := by
      rw [h_mid_stack]
      exact pref_cons hp_par
    have hp1 := prefix_of_iszero r_iz hp_mid
    obtain ⟨w1, hdb1⟩ : ∃ w, Devm.DiffBurn [w] [w =? 0] mid s1 := by
      rcases of_run_reg r_iz with ⟨pc, run⟩
      simp only [Rinst.run, Rinst.runCore] at run
      exact Devm.diffBurn_of_applyUnary run
    have h_bubble_lookup :
        ((weth10 dp).main :: weth10Aux)[bubbleRevertSlot]? =
          some bubbleRevert := by
      simp [weth10, weth10Aux, bubbleRevertSlot]
    rcases of_run_branch_call_bubbleFunctional h_bubble_lookup h_run with
      ⟨s2, hpb2, h_run⟩
    have hps2 := hpb2.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hps2
    rw [hps2] at hp1
    rw [show ((1 : B256) =? 0) = 0 from by
      rw [B256.eqCheck, if_neg (fun h => B256.zero_ne_one h.symm)]] at hp1
    have hp2 : [amount, receiver.toB256] <<+ s2.stack :=
      cons_pref_cons_inv hp1
    rcases of_run_prepend (returnDataShorterThan 32) _ h_run with
      ⟨s3, h_rst, h_run⟩
    rcases of_returnDataShorterThan_val hp2 h_rst with ⟨hp3, hm3, hrd3⟩
    rcases of_run_branch_revert h_run with ⟨s4, hpb4, h_run⟩
    have hps4 := hpb4.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hps4
    rw [hps4] at hp3
    rw [pref_head_unique hp3 (pref_append [(0 : B256)] s4.stack)] at hp3
    have hp4 : [amount, receiver.toB256] <<+ s4.stack :=
      cons_pref_cons_inv hp3
    have h_mem_s4 : s4.memory = mid.memory :=
      (hpb4.memory.symm.trans hm3).trans
        (hpb2.memory.symm.trans hdb1.memory.symm)
    have h_rd_s4 : s4.returnData = mid.returnData :=
      (hpb4.returnData.symm.trans hrd3).trans
        (hpb2.returnData.symm.trans hdb1.returnData.symm)
    have h_wf4 : Mem.Wf s4.memory := by
      rw [h_mem_s4]
      exact h_wf_mid
    have h_rd4 : Mem.Reads s4.memory img := by
      rw [h_mem_s4]
      exact h_rd_mid
    rcases of_run_prepend (checkReturnDataHead CALLBACK_SUCCESS 0) _ h_run with
      ⟨s5, h_crh, h_run⟩
    rcases of_checkReturnDataHead_val hp4 h_wf4 h_rd4 h_crh with
      ⟨hp5, hlen4, h_wf5, h_rd5, hrd5⟩
    rcases of_run_next h_run with ⟨s6, r_iz2, h_run⟩
    have hp6 := prefix_of_iszero r_iz2 hp5
    obtain ⟨w2, hdb6⟩ : ∃ w, Devm.DiffBurn [w] [w =? 0] s5 s6 := by
      rcases of_run_reg r_iz2 with ⟨pc, run⟩
      simp only [Rinst.run, Rinst.runCore] at run
      exact Devm.diffBurn_of_applyUnary run
    have h_failed_lookup :
        ((weth10 dp).main :: weth10Aux)[flashFailedErrorSlot]? =
          some (Func.revertWith "WETH: flash loan failed") := by
      simp [weth10, weth10Aux, flashFailedErrorSlot, flashFailedError]
    rcases of_run_branch_call_revertWithFunctional h_failed_lookup h_run with
      ⟨s7, hpb7, h_run⟩
    have hps7 := hpb7.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hps7
    rw [hps7] at hp6
    have h_flag2 : ((CALLBACK_SUCCESS
        =? Bytes.toB256 (s4.returnData.sliceD 0 32 0)) =? 0) = 0 :=
      pref_head_unique hp6 (pref_append [(0 : B256)] s7.stack)
    have h_magic : Bytes.toB256 (s4.returnData.sliceD 0 32 0) =
        CALLBACK_SUCCESS := by
      by_contra hne
      have h0 : (CALLBACK_SUCCESS =?
          Bytes.toB256 (s4.returnData.sliceD 0 32 0)) = 0 := by
        simp only [B256.eqCheck]
        exact if_neg (fun h => hne h.symm)
      rw [h0, show ((0 : B256) =? 0) = 1 from by
        simp [B256.eqCheck]] at h_flag2
      exact B256.zero_ne_one h_flag2.symm
    rw [h_flag2] at hp6
    have hlen : 32 ≤ child.output.length := by
      rw [← h_mid_rd, ← h_rd_s4]
      exact hlen4
    have hmagicChild :
        Bytes.toB256 (child.output.sliceD 0 32 0) = CALLBACK_SUCCESS := by
      rw [← h_mid_rd, ← h_rd_s4]
      exact h_magic
    rcases of_run_next h_run with ⟨s8, hpop1, h_run⟩
    rcases of_run_next h_run with ⟨s9, hpop2, hcallSettle⟩
    obtain ⟨popped1, hpb8⟩ := of_run_pop hpop1
    obtain ⟨popped2, hpb9⟩ := of_run_pop hpop2
    rcases of_run_call hcallSettle with
      ⟨f, settle, hget, hburnSettle, hsettle⟩
    have h_settle_lookup :
        ((weth10 dp).main :: weth10Aux)[flashSettleSlot]? =
          some flashSettle := by
      simp [weth10, weth10Aux, flashSettleSlot]
    have hf : f = flashSettle := by
      rw [h_settle_lookup] at hget
      exact Option.some.inj hget.symm
    subst f
    have hrstFrame := of_returnDataShorterThan_frame h_rst
    have hcrhFrame := of_checkReturnDataHead_frame h_crh
    have hstate : mid.state = settle.state :=
      hdb1.state.trans (hpb2.state.trans
        (hrstFrame.2.2.trans
          (hpb4.state.trans
            (hcrhFrame.2.2.trans
              (hdb6.state.trans (hpb7.state.trans
                (hpb8.state.trans (hpb9.state.trans hburnSettle.state))))))))
    have hstor : Devm.getStor mid = Devm.getStor settle :=
      funext (getStor_eq_of_state_eq hstate)
    have hbal : Devm.getBal mid = Devm.getBal settle :=
      funext (getBal_eq_of_state_eq hstate)
    have hcode : Devm.getCode mid = Devm.getCode settle :=
      funext (getCode_eq_of_state_eq hstate)
    have hlogs : mid.logs = settle.logs :=
      hdb1.logs.trans (hpb2.logs.trans (hrstFrame.1.trans
        (hpb4.logs.trans (hcrhFrame.1.trans (hdb6.logs.trans
          (hpb7.logs.trans
            (hpb8.logs.trans (hpb9.logs.trans hburnSettle.logs))))))))
    have houtput : mid.output = settle.output :=
      hdb1.output.trans (hpb2.output.trans (hrstFrame.2.1.trans
        (hpb4.output.trans (hcrhFrame.2.1.trans (hdb6.output.trans
          (hpb7.output.trans
            (hpb8.output.trans (hpb9.output.trans hburnSettle.output))))))))
    have hmemory : s5.memory = settle.memory :=
      hdb6.memory.trans (hpb7.memory.trans
        (hpb8.memory.trans (hpb9.memory.trans hburnSettle.memory)))
    have hwfSettle : Mem.Wf settle.memory := by
      rw [← hmemory]
      exact h_wf5
    have hreadsSettle : ∃ settleImg, Mem.Reads settle.memory settleImg := by
      rw [← hmemory]
      exact ⟨_, h_rd5⟩
    refine ⟨mid, settle, ?_, hstor, hbal, hcode, hlogs.symm,
      houtput.symm, hwfSettle, hreadsSettle, hsettle⟩
    refine ⟨parent, child, xl, delegated, na, code, gasWord, avail, pc,
      hstep, hdepth, hstk_eq, hp_par, hst_par, ?_, hlogs_par, houtput_par, h_del, h_fill,
      ?_, hclean, hlen, hmagicChild, h_resume, h_mid_state, h_mid_rd,
      h_mid_stack, h_mid_logs, h_mid_output⟩
    · simpa only [show (0 : B256).toNat = 0 from rfl] using hmem_par
    · simpa only [show (0 : B256).toNat = 0 from rfl, if_true,
        Nat.add_zero] using run_pm

/-- Compatibility projection of `of_rawFlashLoanSuccessTail_step`. -/
theorem of_rawFlashLoanSuccessTail
    (dp : DeployParams)
    {sevm : Sevm} {sc r : Devm} {amount : B256}
    {receiver : Adr} {inputSize : B256} {callbackInput : Bytes}
    {gasWord : B256} {img : Bytes}
    (h_stack :
      gasWord :: receiver.toB256 :: (0 : B256) :: callbackArgsOffset ::
      inputSize :: (0 : B256) :: (0 : B256) ::
      [amount, receiver.toB256] <<+ sc.stack)
    (h_wf : Mem.Wf sc.memory)
    (h_reads : Mem.Reads sc.memory img)
    (h_win :
      img.sliceD callbackArgsOffset.toNat inputSize.toNat 0 =
        callbackInput)
    (h_run :
      Func.Run ((weth10 dp).main :: weth10Aux) sevm sc
        flashLoanSuccessTail r) :
    ∃ mid settle,
      RawFlashCallbackBoundary sevm sevm.currentTarget receiver
        amount inputSize callbackInput sc mid ∧
      Devm.getStor mid = Devm.getStor settle ∧
      Devm.getBal mid = Devm.getBal settle ∧
      Devm.getCode mid = Devm.getCode settle ∧
      settle.logs = mid.logs ∧
      settle.output = mid.output ∧
      Mem.Wf settle.memory ∧
      (∃ settleImg, Mem.Reads settle.memory settleImg) ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm settle
        flashSettle r := by
  rcases of_rawFlashLoanSuccessTail_step dp h_stack h_wf h_reads h_win
      h_run with
    ⟨mid, settle, hcallback, hstor, hbal, hcode, hlogs, houtput,
      hwf, hreads', hsettle⟩
  exact ⟨mid, settle, hcallback.toRaw, hstor, hbal, hcode, hlogs,
    houtput, hwf, hreads', hsettle⟩

/-- Canonical ERC-3156 compatibility projection of
`of_rawFlashLoanSuccessTail`. -/
theorem of_flashLoanSuccessTail
    (dp : DeployParams)
    {sevm : Sevm} {sc r : Devm} {amount : B256}
    {receiver : Adr} {data : Bytes} {gasWord : B256} {img : Bytes}
    (h_stack :
      gasWord :: receiver.toB256 :: (0 : B256) :: callbackArgsOffset ::
      Nat.toB256 (196 + ceil32 data.length) :: (0 : B256) :: (0 : B256) ::
      [amount, receiver.toB256] <<+ sc.stack)
    (h_wf : Mem.Wf sc.memory)
    (h_reads : Mem.Reads sc.memory img)
    (h_win :
      img.sliceD callbackArgsOffset.toNat
        (196 + ceil32 data.length) 0 =
      abiCallWithTail onFlashLoanSelector
        [sevm.caller.toB256, sevm.currentTarget.toB256, amount, 0] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_run :
      Func.Run ((weth10 dp).main :: weth10Aux) sevm sc
        flashLoanSuccessTail r) :
    ∃ mid settle,
      FlashCallbackBoundary sevm sevm.currentTarget receiver
        amount data sc mid ∧
      Devm.getStor mid = Devm.getStor settle ∧
      Devm.getBal mid = Devm.getBal settle ∧
      Devm.getCode mid = Devm.getCode settle ∧
      settle.logs = mid.logs ∧
      settle.output = mid.output ∧
      Mem.Wf settle.memory ∧
      (∃ settleImg, Mem.Reads settle.memory settleImg) ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm settle
        flashSettle r := by
  have h_win' :
      img.sliceD callbackArgsOffset.toNat
          (Nat.toB256 (196 + ceil32 data.length)).toNat 0 =
        abiCallWithTail onFlashLoanSelector
          [sevm.caller.toB256, sevm.currentTarget.toB256, amount, 0] data := by
    rw [B256.toNat_toB256_of_lt h_size]
    exact h_win
  obtain ⟨mid, settle, hraw, hstor, hbal, hcode, hlogs, houtput,
      hwf, hreads, hsettle⟩ :=
    of_rawFlashLoanSuccessTail dp h_stack h_wf h_reads h_win' h_run
  refine ⟨mid, settle, ?_, hstor, hbal, hcode, hlogs, houtput,
    hwf, hreads, hsettle⟩
  unfold RawFlashCallbackBoundary at hraw
  unfold FlashCallbackBoundary
  rcases hraw with ⟨parent, child, xl, delegated, na, code, gasWord', avail,
    hdepth, hstack, -, hstate, hmemory, hlogs', houtput', hdelegated,
    hfilled, hprocess, hclean, hlength, hmagic, hresume, hmidState,
    hreturndata, hmidStack, hmidLogs, hmidOutput⟩
  refine ⟨parent, child, xl, delegated, na, code, gasWord', avail,
    hdepth, hstack, hstate, ?_, hlogs', houtput', hdelegated, hfilled,
    hprocess, hclean, hlength, hmagic, hresume, hmidState,
    hreturndata, hmidStack, hmidLogs, hmidOutput⟩
  simpa only [B256.toNat_toB256_of_lt h_size] using hmemory

/-! ## Exact repayment frame -/

/-- The tagged allowance cell charged by flash repayment: normalized receiver
as owner and this WETH10 deployment as spender. -/
def flashAllowanceRuntimeKey (e : Sevm) : B256 :=
  allowanceTagWord |||
    (allowancePayloadMask &&& Bytes.keccak
      ((normalizedAddressArg e 0).toBytes ++
        e.currentTarget.toB256.toBytes))

/-- The final flash burn leaves the tagged repayment-allowance cell exactly
as settlement wrote it. -/
theorem flashBurn_storage_at_allowanceKey
    (dp : DeployParams) {e : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s flashBurn r) :
    (Devm.getStor r e.currentTarget).get (flashAllowanceRuntimeKey e) =
      (Devm.getStor s e.currentTarget).get
        (flashAllowanceRuntimeKey e) := by
  apply flashBurn_storage_get_of_not_valid dp
    (flashAllowanceRuntimeKey e)
  · simpa only [flashAllowanceRuntimeKey] using
      runtimeAllowanceKey_not_valid
        (Bytes.keccak
          ((normalizedAddressArg e 0).toBytes ++
            e.currentTarget.toB256.toBytes))
  · simpa only [flashAllowanceRuntimeKey] using
      runtimeAllowanceKey_ne_flash
        (Bytes.keccak
          ((normalizedAddressArg e 0).toBytes ++
            e.currentTarget.toB256.toBytes))
  · exact run

/-- The finite-allowance arm's exact `Approval` entry.  The runtime deliberately
keeps the raw ABI receiver word as the indexed topic, while the storage key
uses its normalized address image. -/
def flashApprovalLog (e : Sevm) (reduced : B256) : Log :=
  ⟨e.currentTarget,
    [approvalEvent, Sevm.argWord e 0, e.currentTarget.toB256],
    reduced.toBytes⟩

/-- The exact burn-side `Transfer(receiver, 0, amount)` entry. -/
def flashBurnTransferLog (e : Sevm) : Log :=
  ⟨e.currentTarget,
    [transferEvent, normalizedAddressArg e 0, 0],
    (Sevm.argWord e 2).toBytes⟩

/-- The exact outer mint entry emitted before control passes to the borrower.
The recipient is the runtime-normalized address, never the unmasked ABI word. -/
def flashMintTransferLog (e : Sevm) (recipient : Adr) : Log :=
  ⟨e.currentTarget,
    [transferEvent, 0, recipient.toB256],
    (Sevm.argWord e 2).toBytes⟩

/-- Exact observable fork of the post-callback allowance phase.  Infinite
allowance is retained without a write or `Approval`; finite allowance is
reduced by the loan amount and emits the corresponding entry. -/
def FlashAllowanceOutcome (e : Sevm) (pre burn : Devm) : Prop :=
  (((Devm.getStor pre e.currentTarget).get (flashAllowanceRuntimeKey e) =
        B256.max ∧
      Devm.getStor burn e.currentTarget =
        Devm.getStor pre e.currentTarget ∧
      burn.logs = pre.logs) ∨
    (∃ allowance : B256,
      allowance ≠ B256.max ∧
      Sevm.argWord e 2 ≤ allowance ∧
      (Devm.getStor pre e.currentTarget).get
          (flashAllowanceRuntimeKey e) = allowance ∧
      Devm.getStor burn e.currentTarget =
        (Devm.getStor pre e.currentTarget).set
          (flashAllowanceRuntimeKey e)
          (allowance - Sevm.argWord e 2) ∧
      burn.logs = pre.logs ++
        [flashApprovalLog e (allowance - Sevm.argWord e 2)])) ∧
  burn.output = pre.output ∧
  Devm.getBal burn = Devm.getBal pre ∧
  Devm.getCode burn = Devm.getCode pre

/-- Compose the callback's arbitrary log segment with the allowance fork and
the final burn entry. -/
private lemma repayment_log_fork
    {e : Sevm} {pre sc mid settle burn post : Devm}
    {recipient : Adr} {callbackLogs : List Log} {amount : B256}
    (h_amount : Sevm.argWord e 2 = amount)
    (h_mint : sc.logs = pre.logs ++ [flashMintTransferLog e recipient])
    (h_callback : mid.logs = sc.logs ++ callbackLogs)
    (h_settle : settle.logs = mid.logs)
    (h_allow : FlashAllowanceOutcome e settle burn)
    (h_burn : post.logs = burn.logs ++ [flashBurnTransferLog e]) :
    (((Devm.getStor settle e.currentTarget).get
          (flashAllowanceRuntimeKey e) = B256.max ∧
        post.logs = pre.logs ++ [flashMintTransferLog e recipient] ++
          callbackLogs ++ [flashBurnTransferLog e]) ∨
      (∃ allowance : B256,
        allowance ≠ B256.max ∧
        amount ≤ allowance ∧
        (Devm.getStor settle e.currentTarget).get
          (flashAllowanceRuntimeKey e) = allowance ∧
        post.logs = pre.logs ++ [flashMintTransferLog e recipient] ++
          callbackLogs ++
            [flashApprovalLog e (allowance - amount),
              flashBurnTransferLog e])) := by
  unfold FlashAllowanceOutcome at h_allow
  rcases h_allow.1 with h_max | h_finite
  · left
    refine ⟨h_max.1, ?_⟩
    rw [h_burn, h_max.2.2, h_settle, h_callback, h_mint]
  · rcases h_finite with
      ⟨allowance, h_ne, h_le, h_read, h_write, h_logs⟩
    right
    refine ⟨allowance, h_ne, ?_, h_read, ?_⟩
    · simpa only [h_amount] using h_le
    · rw [h_burn, h_logs, h_settle, h_callback, h_mint, h_amount]
      simp only [List.append_assoc, List.singleton_append]

/-- The repayment prefix computes the exact tagged receiver/self allowance
key while retaining a well-formed readable memory image for the event and
return proofs that follow. -/
private lemma of_flashSettleKeyPrefix
    {e : Sevm} {s r : Devm} {img : Bytes}
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Line.Run e s
      (addressArg 0 ++ mstoreAt 0 ++ [address] ++ mstoreAt 1 ++
        allowanceKeyFromMemory) r) :
    flashAllowanceRuntimeKey e :: [] <<+ r.stack ∧
      Mem.Wf r.memory ∧
      ∃ out, Mem.Reads r.memory out := by
  rcases of_run_append (addressArg 0) run with
    ⟨s1, howner, run1⟩
  have hp1 : normalizedAddressArg e 0 :: [] <<+ s1.stack := by
    simpa only [normalizedAddressArg] using
      prefix_of_addressArg nil_pref howner
  rcases of_run_append (mstoreAt 0) run1 with
    ⟨s2, hstoreOwner, run2⟩
  rcases of_run_mstoreAt_val hstoreOwner hp1 with
    ⟨hp2, hm2⟩
  have hm2' : s2.memory =
      s1.memory.write 0 (normalizedAddressArg e 0).toBytes := by
    simpa only [show (0 * 32 : B256).toNat = 0 by decide +kernel]
      using hm2
  have hmOwner : s.memory = s1.memory :=
    Line.of_inv Devm.memory (by
      unfold addressArg normalizeAddress
      line_inv) howner
  rcases Line.of_run_cons run2 with
    ⟨s3, haddress, run3⟩
  have hb3 := of_run_address haddress
  have hp3 : e.currentTarget.toB256 :: [] <<+ s3.stack :=
    prefix_of_push hb3 hp2
  rcases of_run_append (mstoreAt 1) run3 with
    ⟨s4, hstoreSelf, hkey⟩
  rcases of_run_mstoreAt_val hstoreSelf hp3 with
    ⟨hp4, hm4⟩
  have hm4' : s4.memory =
      s3.memory.write 32 e.currentTarget.toB256.toBytes := by
    simpa only [show (1 * 32 : B256).toNat = 32 by decide +kernel]
      using hm4
  let img1 := Bytes.writeAt img 0 (normalizedAddressArg e 0).toBytes
  let img2 := Bytes.writeAt img1 32 e.currentTarget.toB256.toBytes
  have hwf4 : Mem.Wf s4.memory := by
    rw [hm4', ← hb3.memory, hm2', ← hmOwner]
    exact (h_wf.write 0 (normalizedAddressArg e 0).toBytes).write
      32 e.currentTarget.toB256.toBytes
  have hr4 : Mem.Reads s4.memory img2 := by
    rw [hm4', ← hb3.memory, hm2', ← hmOwner]
    exact Mem.Reads.write
      (h_wf.write 0 (normalizedAddressArg e 0).toBytes)
      (Mem.Reads.write h_wf h_reads 0
        (normalizedAddressArg e 0).toBytes)
      32 e.currentTarget.toB256.toBytes
  rcases prefix_of_allowanceKeyFromMemory_image hp4 hwf4 hr4 hkey with
    ⟨hp5, hwf5, hr5⟩
  have himg : img2.sliceD 0 64 0 =
      (normalizedAddressArg e 0).toBytes ++
        e.currentTarget.toB256.toBytes := by
    dsimp only [img2, img1]
    apply slice_two_words
    exact B256.length_toBytes _
  rw [himg] at hp5
  change flashAllowanceRuntimeKey e :: [] <<+ r.stack at hp5
  exact ⟨hp5, hwf5, ⟨img2, hr5⟩⟩

/-- Exact finite-allowance event fragment: retain no stack values, append the
one canonical `Approval`, and retain a readable frame image. -/
private lemma of_emitFlashApproval_effect
    {e : Sevm} {s r : Devm} {reduced : B256} {img : Bytes}
    (hp : reduced :: [] <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Line.Run e s emitFlashApproval r) :
    [] <<+ r.stack ∧
      r.logs = s.logs ++ [flashApprovalLog e reduced] ∧
      r.output = s.output ∧
      Mem.Wf r.memory ∧
      ∃ out, Mem.Reads r.memory out := by
  simp only [emitFlashApproval] at run
  rcases Line.of_run_cons run with ⟨s1, hdup, run1⟩
  have hp1 : reduced :: reduced :: [] <<+ s1.stack :=
    prefix_of_dup_val hdup (by show_nth) hp
  rcases of_run_append (mstoreAt 0) run1 with
    ⟨s2, hstore, run2⟩
  rcases of_run_mstoreAt_val hstore hp1 with ⟨hp2, hm2⟩
  have hm2' : s2.memory = s1.memory.write 0 reduced.toBytes := by
    simpa only [show (0 * 32 : B256).toNat = 0 by decide +kernel]
      using hm2
  have hm01 : s.memory = s1.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hdup
  let img1 := Bytes.writeAt img 0 reduced.toBytes
  have hwf2 : Mem.Wf s2.memory := by
    rw [hm2', ← hm01]
    exact h_wf.write 0 reduced.toBytes
  have hr2 : Mem.Reads s2.memory img1 := by
    rw [hm2', ← hm01]
    exact Mem.Reads.write h_wf h_reads 0 reduced.toBytes
  rcases Line.of_run_cons run2 with ⟨s3, haddress, run3⟩
  have hb3 := of_run_address haddress
  have hp3 : e.currentTarget.toB256 :: reduced :: [] <<+ s3.stack :=
    prefix_of_push hb3 hp2
  rcases of_run_append (arg 0) run3 with ⟨s4, harg0, run4⟩
  have hp4 : Sevm.argWord e 0 :: e.currentTarget.toB256 ::
      reduced :: [] <<+ s4.stack := prefix_of_arg hp3 harg0
  rcases Line.of_run_cons run4 with ⟨s5, hevent, run5⟩
  have hb5 := of_run_pushB256 hevent
  have hp5 : approvalEvent :: Sevm.argWord e 0 ::
      e.currentTarget.toB256 :: reduced :: [] <<+ s5.stack :=
    prefix_of_push hb5 hp4
  rcases of_run_append (logWith 2 0 1) run5 with
    ⟨s6, hlog, run6⟩
  rcases of_logWith201_val hp5 hlog with ⟨hp6, hlogs6⟩
  have hm25 : s2.memory = s5.memory := by
    calc
      s2.memory = s3.memory := hb3.memory
      _ = s4.memory := Line.of_inv Devm.memory (by
        unfold arg cdl
        line_inv) harg0
      _ = s5.memory := hb5.memory
  have hr5 : Mem.Reads s5.memory img1 := by
    rw [← hm25]
    exact hr2
  have hdata : (s5.memory.read 0 32).1 = reduced.toBytes := by
    rw [Mem.Reads.read hr5 0 32,
      show 32 = reduced.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt]
  rcases Line.of_run_cons run6 with ⟨s7, hpop, hnil⟩
  cases hnil
  have hp7 := prefix_of_pop (of_run_pop hpop) hp6
  have hlogs05 : s.logs = s5.logs := by
    calc
      s.logs = s1.logs := Ninst.Hinv.inv (f := Devm.logs) hdup
      _ = s2.logs := Line.of_inv Devm.logs (by
        unfold mstoreAt
        line_inv) hstore
      _ = s3.logs := hb3.logs
      _ = s4.logs := Line.of_inv Devm.logs (by
        unfold arg cdl
        line_inv) harg0
      _ = s5.logs := hb5.logs
  have hmem6 : s6.memory = s5.memory.extend 0 32 :=
    of_logWith201_mem hp5 hlog
  have hwf6 : Mem.Wf s6.memory := by
    rw [hmem6]
    exact Mem.Wf.extend (hm25 ▸ hwf2) 0 32
  have hr6 : Mem.Reads s6.memory img1 := by
    rw [hmem6]
    exact Mem.Reads.extend hr5 0 32
  have hmem67 : s6.memory = r.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hpop
  have hlogs67 : s6.logs = r.logs :=
    Ninst.Hinv.inv (f := Devm.logs) hpop
  refine ⟨hp7, ?_, ?_, ?_, ?_⟩
  · rw [← hlogs67, hlogs6, hdata, ← hlogs05]
    rfl
  · calc
      r.output = s6.output :=
        (Ninst.Hinv.inv (f := Devm.output) hpop).symm
      _ = s5.output :=
        (Line.of_inv Devm.output (by
          unfold logWith
          line_inv) hlog).symm
      _ = s4.output := hb5.output.symm
      _ = s3.output :=
        (Line.of_inv Devm.output (by
          unfold arg cdl
          line_inv) harg0).symm
      _ = s2.output := hb3.output.symm
      _ = s1.output :=
        (Line.of_inv Devm.output (by
          unfold mstoreAt
          line_inv) hstore).symm
      _ = s.output :=
        (Ninst.Hinv.inv (f := Devm.output) hdup).symm
  · rw [← hmem67]
    exact hwf6
  · rw [← hmem67]
    exact ⟨img1, hr6⟩

/-- `SUB` is silent for the parent frame's log and output fields. -/
private lemma of_run_sub_logOutput
    {e : Sevm} {s r : Devm} (run : Ninst.Run e s sub r) :
    s.logs = r.logs ∧ s.output = r.output := by
  rcases of_run_reg run with ⟨pc, hrun⟩
  simp only [Rinst.run, Rinst.runCore] at hrun
  obtain ⟨a, b, hdb⟩ := Devm.diffBurn_of_applyBinary hrun
  exact ⟨hdb.logs, hdb.output⟩

/-- Exact post-callback allowance fork and the unique shared burn
continuation.  This theorem stops at `flashBurn`, so the callback's arbitrary
reentrant log segment is already fixed and only the optional outer
`Approval` remains to be accounted for. -/
theorem of_flashSettle_allowance
    (dp : DeployParams) {e : Sevm} {s r : Devm} {img : Bytes}
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      flashSettle r) :
    ∃ burn,
      Func.Run ((weth10 dp).main :: weth10Aux) e burn flashBurn r ∧
      FlashAllowanceOutcome e s burn ∧
      Mem.Wf burn.memory ∧
      (∃ out, Mem.Reads burn.memory out) := by
  simp only [flashSettle] at run
  let keyLine : Line :=
    addressArg 0 ++ mstoreAt 0 ++ [address] ++ mstoreAt 1 ++
      allowanceKeyFromMemory
  rcases of_run_prepend keyLine _ run with
    ⟨sk, hkeyLine, run1⟩
  obtain ⟨hpKey, hwfKey, out, hreadsKey⟩ :=
    of_flashSettleKeyPrefix h_wf h_reads (by
      simpa only [keyLine] using hkeyLine)
  have hstor_s_sk : Devm.getStor s = Devm.getStor sk :=
    Line.of_inv Devm.getStor (by
      unfold keyLine addressArg normalizeAddress mstoreAt
        allowanceKeyFromMemory arg cdl pushList
      line_inv) hkeyLine
  have hbal_s_sk : Devm.getBal s = Devm.getBal sk :=
    Line.of_inv Devm.getBal (by
      unfold keyLine addressArg normalizeAddress mstoreAt
        allowanceKeyFromMemory arg cdl pushList
      line_inv) hkeyLine
  have hcode_s_sk : Devm.getCode s = Devm.getCode sk :=
    Line.of_inv Devm.getCode (by
      unfold keyLine addressArg normalizeAddress mstoreAt
        allowanceKeyFromMemory arg cdl pushList
      line_inv) hkeyLine
  have hlogs_s_sk : s.logs = sk.logs :=
    Line.of_inv Devm.logs (by
      unfold keyLine addressArg normalizeAddress mstoreAt
        allowanceKeyFromMemory arg cdl pushList
      line_inv) hkeyLine
  have houtput_s_sk : s.output = sk.output :=
    Line.of_inv Devm.output (by
      unfold keyLine addressArg normalizeAddress mstoreAt
        allowanceKeyFromMemory arg cdl pushList
      line_inv) hkeyLine

  let inspectLine : Line := [dup 0, sload, dup 0] ++ isMax
  rcases of_run_prepend inspectLine _ run1 with
    ⟨sl, hinspect, runBranch⟩
  have hmem_sk_sl : sk.memory = sl.memory :=
    Line.of_inv Devm.memory (by
      unfold inspectLine isMax
      line_inv) hinspect
  have hstor_sk_sl : Devm.getStor sk = Devm.getStor sl :=
    Line.of_inv Devm.getStor (by
      unfold inspectLine isMax
      line_inv) hinspect
  have hbal_sk_sl : Devm.getBal sk = Devm.getBal sl :=
    Line.of_inv Devm.getBal (by
      unfold inspectLine isMax
      line_inv) hinspect
  have hcode_sk_sl : Devm.getCode sk = Devm.getCode sl :=
    Line.of_inv Devm.getCode (by
      unfold inspectLine isMax
      line_inv) hinspect
  have hlogs_sk_sl : sk.logs = sl.logs :=
    Line.of_inv Devm.logs (by
      unfold inspectLine isMax
      line_inv) hinspect
  have houtput_sk_sl : sk.output = sl.output :=
    Line.of_inv Devm.output (by
      unfold inspectLine isMax
      line_inv) hinspect
  unfold inspectLine at hinspect
  rcases Line.of_run_cons hinspect with
    ⟨si1, hdupKey, hinspect1⟩
  have hpI1 : flashAllowanceRuntimeKey e ::
      flashAllowanceRuntimeKey e :: [] <<+ si1.stack :=
    prefix_of_dup_val hdupKey (by show_nth) hpKey
  rcases Line.of_run_cons hinspect1 with
    ⟨si2, hload, hinspect2⟩
  rcases prefix_of_sload hload hpI1 with
    ⟨allowance, hpI2, hallowanceRead⟩
  have hallowance :
      (Devm.getStor s e.currentTarget).get
          (flashAllowanceRuntimeKey e) = allowance := by
    symm
    rw [hallowanceRead]
    change (Devm.getStor si1 e.currentTarget).get
      (flashAllowanceRuntimeKey e) = _
    rw [← congrFun (Ninst.Hinv.inv (f := Devm.getStor) hdupKey)
      e.currentTarget, ← congrFun hstor_s_sk e.currentTarget]
  rcases Line.of_run_cons hinspect2 with
    ⟨si3, hdupAllowance, hinspect3⟩
  have hpI3 : allowance :: allowance :: flashAllowanceRuntimeKey e ::
      [] <<+ si3.stack :=
    prefix_of_dup_val hdupAllowance (by show_nth) hpI2
  rcases Line.of_run_cons hinspect3 with
    ⟨si4, hnot, hinspect4⟩
  have hpI4 : (~~~ allowance) :: allowance ::
      flashAllowanceRuntimeKey e :: [] <<+ si4.stack :=
    prefix_of_not hnot hpI3
  rcases Line.of_run_cons hinspect4 with
    ⟨si5, hiszero, hnilInspect⟩
  cases hnilInspect
  have hpLoad : ((~~~ allowance) =? 0) :: allowance ::
      flashAllowanceRuntimeKey e :: [] <<+ sl.stack :=
    prefix_of_iszero hiszero hpI4
  have hstor_s_sl := hstor_s_sk.trans hstor_sk_sl
  have hbal_s_sl := hbal_s_sk.trans hbal_sk_sl
  have hcode_s_sl := hcode_s_sk.trans hcode_sk_sl
  have hlogs_s_sl := hlogs_s_sk.trans hlogs_sk_sl
  have houtput_s_sl := houtput_s_sk.trans houtput_sk_sl
  have hwfSl : Mem.Wf sl.memory := by
    rw [← hmem_sk_sl]
    exact hwfKey
  have hreadsSl : Mem.Reads sl.memory out := by
    rw [← hmem_sk_sl]
    exact hreadsKey
  have h_burn_lookup :
      ((weth10 dp).main :: weth10Aux)[flashBurnSlot]? = some flashBurn := by
    simp [weth10, weth10Aux, flashBurnSlot]

  rcases of_run_branch runBranch with
      ⟨sf, hfinitePop, hfinite⟩ |
      ⟨wmax, sm1, sm2, hnzmax, hmaxPop, hmaxBurn, hmax⟩
  · have hfiniteStack := hfinitePop.stack
    simp only [Stack.Pop, Split, List.nil_append,
      List.cons_append] at hfiniteStack
    rw [hfiniteStack] at hpLoad
    have hmaxFlag : ((~~~ allowance) =? 0) = 0 :=
      pref_head_unique hpLoad (pref_append [0] sf.stack)
    have hneMax : allowance ≠ B256.max := by
      intro hmaxAllowance
      rw [hmaxAllowance, B256.not_max,
        show ((0 : B256) =? 0) = 1 from by simp [B256.eqCheck]]
        at hmaxFlag
      exact B256.zero_ne_one hmaxFlag.symm
    rw [hmaxFlag] at hpLoad
    have hpFinite : allowance :: flashAllowanceRuntimeKey e ::
        [] <<+ sf.stack := cons_pref_cons_inv hpLoad
    have hstor_s_sf := hstor_s_sl.trans (PopBurn.Inv.inv hfinitePop)
    have hbal_s_sf := hbal_s_sl.trans (PopBurn.Inv.inv hfinitePop)
    have hcode_s_sf := hcode_s_sl.trans (funext (fun a =>
      getCode_eq_of_state_eq hfinitePop.state a))
    have hlogs_s_sf := hlogs_s_sl.trans hfinitePop.logs
    have houtput_s_sf := houtput_s_sl.trans hfinitePop.output
    let guardLine : Line := arg 2 ++ [swap 0] ++ balanceTooSmall
    rcases of_run_prepend guardLine _ hfinite with
      ⟨sg, hguardLine, runGuard⟩
    have hpGuard :
        (allowance <? Sevm.argWord e 2) :: allowance ::
          Sevm.argWord e 2 :: flashAllowanceRuntimeKey e ::
          [] <<+ sg.stack := by
      unfold guardLine at hguardLine
      rcases of_run_append (arg 2) hguardLine with
        ⟨sa, hamount, hguard1⟩
      have hpA : Sevm.argWord e 2 :: allowance ::
          flashAllowanceRuntimeKey e :: [] <<+ sa.stack :=
        prefix_of_arg hpFinite hamount
      rcases Line.of_run_cons hguard1 with
        ⟨ss, hswap, htooSmall⟩
      have hswapCore : Stack.Swap (0 : Fin 16).val
          [Sevm.argWord e 2, allowance, flashAllowanceRuntimeKey e]
          [allowance, Sevm.argWord e 2, flashAllowanceRuntimeKey e] :=
        Stack.swapCore_zero
      have hpS : allowance :: Sevm.argWord e 2 ::
          flashAllowanceRuntimeKey e :: [] <<+ ss.stack :=
        Stack.prefix_of_swap hswapCore (of_run_swap hswap) hpA
      exact prefix_of_balanceTooSmall hpS htooSmall
    have h_allowance_lookup :
        ((weth10 dp).main :: weth10Aux)[allowanceErrorSlot]? =
          some (Func.revertWith "WETH: request exceeds allowance") := by
      simp [weth10, weth10Aux, allowanceErrorSlot, allowanceError]
    rcases of_run_branch_call_revertWithFunctional h_allowance_lookup
        runGuard with ⟨sb, hguardPop, runMutate⟩
    have hguardStack := hguardPop.stack
    simp only [Stack.Pop, Split, List.nil_append,
      List.cons_append] at hguardStack
    rw [hguardStack] at hpGuard
    have hguardFlag : (allowance <? Sevm.argWord e 2) = 0 :=
      pref_head_unique hpGuard (pref_append [0] sb.stack)
    have hcover : Sevm.argWord e 2 ≤ allowance := by
      rw [← B256.not_lt]
      intro hlt
      rw [B256.ltCheck, if_pos hlt] at hguardFlag
      exact B256.zero_ne_one hguardFlag.symm
    rw [hguardFlag] at hpGuard
    have hpBeforeMutate : allowance :: Sevm.argWord e 2 ::
        flashAllowanceRuntimeKey e :: [] <<+ sb.stack :=
      cons_pref_cons_inv hpGuard
    let mutateLine : Line :=
      [sub, dup 0, swap 1, sstore] ++ emitFlashApproval
    rcases of_run_prepend mutateLine _ runMutate with
      ⟨scall, hmutate, hcallRun⟩
    unfold mutateLine at hmutate
    rcases Line.of_run_cons hmutate with
      ⟨ms1, hsub, hmutate1⟩
    have hpSub : (allowance - Sevm.argWord e 2) ::
        flashAllowanceRuntimeKey e :: [] <<+ ms1.stack :=
      prefix_of_sub hsub hpBeforeMutate
    rcases Line.of_run_cons hmutate1 with
      ⟨ms2, hdup, hmutate2⟩
    have hpDup : (allowance - Sevm.argWord e 2) ::
        (allowance - Sevm.argWord e 2) ::
        flashAllowanceRuntimeKey e :: [] <<+ ms2.stack :=
      prefix_of_dup_val hdup (by show_nth) hpSub
    rcases Line.of_run_cons hmutate2 with
      ⟨ms3, hswap, hmutate3⟩
    have hswapCore : Stack.Swap (1 : Fin 16).val
        [(allowance - Sevm.argWord e 2),
          (allowance - Sevm.argWord e 2), flashAllowanceRuntimeKey e]
        [flashAllowanceRuntimeKey e,
          (allowance - Sevm.argWord e 2),
          (allowance - Sevm.argWord e 2)] :=
      Stack.swapCore_succ Stack.swapCore_zero
    have hpStore : flashAllowanceRuntimeKey e ::
        (allowance - Sevm.argWord e 2) ::
        (allowance - Sevm.argWord e 2) :: [] <<+ ms3.stack :=
      Stack.prefix_of_swap hswapCore (of_run_swap hswap) hpDup
    rcases Line.of_run_cons hmutate3 with
      ⟨ms4, hstore, happroval⟩
    have hset : Devm.getStor ms4 e.currentTarget =
        (Devm.getStor ms3 e.currentTarget).set
          (flashAllowanceRuntimeKey e)
          (allowance - Sevm.argWord e 2) :=
      sstore_getStor_set hstore hpStore
    let storeRun : Line.Run e sb [sub, dup 0, swap 1, sstore] ms4 :=
      Line.Run.cons hsub (Line.Run.cons hdup
        (Line.Run.cons hswap (Line.Run.cons hstore Line.Run.nil)))
    have hstor_s_ms3 : Devm.getStor s = Devm.getStor ms3 :=
      hstor_s_sf.trans
        ((Line.of_inv Devm.getStor (by
          unfold guardLine
          line_inv) hguardLine).trans
          ((PopBurn.Inv.inv hguardPop).trans
            ((Line.of_inv Devm.getStor (by line_inv)
              (Line.Run.cons hsub Line.Run.nil)).trans
              ((Line.of_inv Devm.getStor (by line_inv)
                (Line.Run.cons hdup Line.Run.nil)).trans
                (Line.of_inv Devm.getStor (by line_inv)
                  (Line.Run.cons hswap Line.Run.nil))))))
    have hlogs_s_ms4 : s.logs = ms4.logs :=
      hlogs_s_sf.trans
        ((Line.of_inv Devm.logs (by
          unfold guardLine
          line_inv) hguardLine).trans
          (hguardPop.logs.trans
            ((of_run_sub_logOutput hsub).1.trans
              ((Ninst.Hinv.inv (f := Devm.logs) hdup).trans
                ((Ninst.Hinv.inv (f := Devm.logs) hswap).trans
                  (Ninst.Hinv.inv (f := Devm.logs) hstore))))))
    have houtput_s_ms4 : s.output = ms4.output :=
      houtput_s_sf.trans
        ((Line.of_inv Devm.output (by
          unfold guardLine
          line_inv) hguardLine).trans
          (hguardPop.output.trans
            ((of_run_sub_logOutput hsub).2.trans
              ((Ninst.Hinv.inv (f := Devm.output) hdup).trans
                ((Ninst.Hinv.inv (f := Devm.output) hswap).trans
                  (Ninst.Hinv.inv (f := Devm.output) hstore))))))
    have hbal_s_ms4 : Devm.getBal s = Devm.getBal ms4 :=
      hbal_s_sf.trans
        ((Line.of_inv Devm.getBal (by
          unfold guardLine
          line_inv) hguardLine).trans
          ((PopBurn.Inv.inv hguardPop).trans
            (Line.of_inv Devm.getBal (by line_inv) storeRun)))
    have hcode_s_ms4 : Devm.getCode s = Devm.getCode ms4 :=
      hcode_s_sf.trans
        ((Line.of_inv Devm.getCode (by
          unfold guardLine
          line_inv) hguardLine).trans
          ((funext (fun a => getCode_eq_of_state_eq hguardPop.state a)).trans
            (Line.of_inv Devm.getCode (by line_inv) storeRun)))
    have hmem_sk_ms4 : sk.memory = ms4.memory :=
      hmem_sk_sl.trans
        (hfinitePop.memory.trans
          ((Line.of_inv Devm.memory (by
            unfold guardLine
            line_inv) hguardLine).trans
            (hguardPop.memory.trans
              (Line.of_inv Devm.memory (by line_inv) storeRun))))
    have hwf4 : Mem.Wf ms4.memory := by
      rw [← hmem_sk_ms4]
      exact hwfKey
    have hreads4 : Mem.Reads ms4.memory out := by
      rw [← hmem_sk_ms4]
      exact hreadsKey
    obtain ⟨hpAfterApproval, happrovalLogs, happrovalOutput,
        hwfCall, outCall, hreadsCall⟩ :=
      of_emitFlashApproval_effect
        (reduced := allowance - Sevm.argWord e 2)
        (img := out) (by
          exact prefix_of_sstore hstore hpStore)
        hwf4 hreads4 happroval
    rcases of_run_call hcallRun with
      ⟨f, burn, hget, hcallBurn, hcore⟩
    have hf : f = flashBurn := by
      rw [h_burn_lookup] at hget
      exact Option.some.inj hget.symm
    subst f
    have hstorApproval : Devm.getStor ms4 = Devm.getStor scall :=
      Line.of_inv Devm.getStor (by
        unfold emitFlashApproval mstoreAt arg cdl logWith
        line_inv) happroval
    have hstorCall : Devm.getStor scall = Devm.getStor burn :=
      Burn.Inv.inv hcallBurn
    have hstorBurn : Devm.getStor burn e.currentTarget =
        (Devm.getStor s e.currentTarget).set
          (flashAllowanceRuntimeKey e)
          (allowance - Sevm.argWord e 2) := by
      rw [← congrFun hstorCall e.currentTarget,
        ← congrFun hstorApproval e.currentTarget, hset,
        ← congrFun hstor_s_ms3 e.currentTarget]
    have hlogsBurn : burn.logs = s.logs ++
        [flashApprovalLog e (allowance - Sevm.argWord e 2)] := by
      rw [← hcallBurn.logs, happrovalLogs, ← hlogs_s_ms4]
    have houtputBurn : burn.output = s.output := by
      exact hcallBurn.output.symm.trans
        (happrovalOutput.trans houtput_s_ms4.symm)
    have hbalBurn : Devm.getBal burn = Devm.getBal s := by
      exact (hbal_s_ms4.trans
        ((Line.of_inv Devm.getBal (by
          unfold emitFlashApproval mstoreAt arg cdl logWith
          line_inv) happroval).trans
          (Burn.Inv.inv hcallBurn))).symm
    have hcodeBurn : Devm.getCode burn = Devm.getCode s := by
      exact (hcode_s_ms4.trans
        ((Line.of_inv Devm.getCode (by
          unfold emitFlashApproval mstoreAt arg cdl logWith
          line_inv) happroval).trans
          (funext (fun a =>
            getCode_eq_of_state_eq hcallBurn.state a)))).symm
    refine ⟨burn, hcore, ?_, ?_, ?_⟩
    · unfold FlashAllowanceOutcome
      exact ⟨Or.inr ⟨allowance, hneMax, hcover, hallowance,
        hstorBurn, hlogsBurn⟩, houtputBurn, hbalBurn, hcodeBurn⟩
    · rw [← hcallBurn.memory]
      exact hwfCall
    · rw [← hcallBurn.memory]
      exact ⟨outCall, hreadsCall⟩
  · have hmaxStack := hmaxPop.stack
    simp only [Stack.Pop, Split, List.nil_append,
      List.cons_append] at hmaxStack
    rw [hmaxStack] at hpLoad
    have hflagEq : ((~~~ allowance) =? 0) = wmax :=
      pref_head_unique hpLoad (pref_append [wmax] sm1.stack)
    have hallowanceMax : allowance = B256.max := by
      apply B256.eq_max_of_not_eq_zero
      by_contra hnotZero
      rw [B256.eqCheck, if_neg hnotZero] at hflagEq
      exact hnzmax hflagEq.symm
    rw [hflagEq] at hpLoad
    have hpMax : allowance :: flashAllowanceRuntimeKey e ::
        [] <<+ sm1.stack := cons_pref_cons_inv hpLoad
    have hpMax2 : allowance :: flashAllowanceRuntimeKey e ::
        [] <<+ sm2.stack := by
      rcases hpMax with ⟨tail, htail⟩
      exact ⟨tail, by rw [← hmaxBurn.stack]; exact htail⟩
    rcases of_run_next hmax with ⟨sm3, hpop1, hmax1⟩
    have hpMax3 : flashAllowanceRuntimeKey e :: [] <<+ sm3.stack :=
      prefix_of_pop (of_run_pop hpop1) hpMax2
    rcases of_run_next hmax1 with ⟨sm4, hpop2, hcallRun⟩
    have hpMax4 : [] <<+ sm4.stack :=
      prefix_of_pop (of_run_pop hpop2) hpMax3
    rcases of_run_call hcallRun with
      ⟨f, burn, hget, hcallBurn, hcore⟩
    have hf : f = flashBurn := by
      rw [h_burn_lookup] at hget
      exact Option.some.inj hget.symm
    subst f
    let hpops : Line.Run e sm2 [pop, pop] sm4 :=
      Line.Run.cons hpop1 (Line.Run.cons hpop2 Line.Run.nil)
    have hstor_s_burn : Devm.getStor s = Devm.getStor burn :=
      hstor_s_sl.trans
        ((PopBurn.Inv.inv hmaxPop).trans
          ((Burn.Inv.inv hmaxBurn).trans
            ((Line.of_inv Devm.getStor (by line_inv) hpops).trans
              (Burn.Inv.inv hcallBurn))))
    have hbal_s_burn : Devm.getBal s = Devm.getBal burn :=
      hbal_s_sl.trans
        ((PopBurn.Inv.inv hmaxPop).trans
          ((Burn.Inv.inv hmaxBurn).trans
            ((Line.of_inv Devm.getBal (by line_inv) hpops).trans
              (Burn.Inv.inv hcallBurn))))
    have hcode_s_burn : Devm.getCode s = Devm.getCode burn :=
      hcode_s_sl.trans
        ((funext (fun a => getCode_eq_of_state_eq hmaxPop.state a)).trans
          ((funext (fun a => getCode_eq_of_state_eq hmaxBurn.state a)).trans
            ((Line.of_inv Devm.getCode (by line_inv) hpops).trans
              (funext (fun a =>
                getCode_eq_of_state_eq hcallBurn.state a)))))
    have hlogs_s_burn : s.logs = burn.logs :=
      hlogs_s_sl.trans
        (hmaxPop.logs.trans
          (hmaxBurn.logs.trans
            ((Line.of_inv Devm.logs (by line_inv) hpops).trans
              hcallBurn.logs)))
    have houtput_s_burn : s.output = burn.output :=
      houtput_s_sl.trans
        (hmaxPop.output.trans
          (hmaxBurn.output.trans
            ((Line.of_inv Devm.output (by line_inv) hpops).trans
              hcallBurn.output)))
    have hmem_sk_burn : sk.memory = burn.memory :=
      hmem_sk_sl.trans
        (hmaxPop.memory.trans
          (hmaxBurn.memory.trans
            ((Line.of_inv Devm.memory (by line_inv) hpops).trans
              hcallBurn.memory)))
    refine ⟨burn, hcore, ?_, ?_, ?_⟩
    · unfold FlashAllowanceOutcome
      exact ⟨Or.inl ⟨hallowance.trans hallowanceMax,
        congrFun hstor_s_burn e.currentTarget |>.symm,
        hlogs_s_burn.symm⟩,
        houtput_s_burn.symm, hbal_s_burn.symm, hcode_s_burn.symm⟩
    · rw [← hmem_sk_burn]
      exact hwfKey
    · rw [← hmem_sk_burn]
      exact ⟨out, hreadsKey⟩

/-- The burn event fragment emits exactly
`Transfer(normalized receiver, 0, amount)` and is otherwise frame-silent. -/
private lemma of_flashBurnEvent_effect
    {e : Sevm} {s r : Devm} {img : Bytes}
    (hp : [] <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Line.Run e s
      (addressArg 0 ++ arg 2 ++ [pushB256 0] ++ emitTransfer ++
        [pop, pop]) r) :
    [] <<+ r.stack ∧
      r.logs = s.logs ++ [flashBurnTransferLog e] ∧
      r.output = s.output ∧
      Mem.Wf r.memory ∧
      ∃ out, Mem.Reads r.memory out := by
  rcases of_run_append (addressArg 0) run with
    ⟨s1, howner, run1⟩
  have hp1 : normalizedAddressArg e 0 :: [] <<+ s1.stack := by
    simpa only [normalizedAddressArg] using
      prefix_of_addressArg hp howner
  rcases of_run_append (arg 2) run1 with
    ⟨s2, hamount, run2⟩
  have hp2 : Sevm.argWord e 2 :: normalizedAddressArg e 0 ::
      [] <<+ s2.stack := prefix_of_arg hp1 hamount
  rcases Line.of_run_cons run2 with ⟨s3, hzero, run3⟩
  have hb3 := of_run_pushB256 hzero
  have hp3 : (0 : B256) :: Sevm.argWord e 2 ::
      normalizedAddressArg e 0 :: [] <<+ s3.stack :=
    prefix_of_push hb3 hp2
  rcases of_run_append emitTransfer run3 with
    ⟨s4, hemit, run4⟩
  simp only [emitTransfer, Blanc.transferFromLog] at hemit
  rcases Line.of_run_cons hemit with
    ⟨u1, hdupOwner, hemit1⟩
  have hpU1 : normalizedAddressArg e 0 :: (0 : B256) ::
      Sevm.argWord e 2 :: normalizedAddressArg e 0 :: [] <<+ u1.stack :=
    prefix_of_dup_val hdupOwner (by show_nth) hp3
  rcases Line.of_run_cons hemit1 with
    ⟨u2, hevent, hemit2⟩
  have hbEvent := of_run_pushB256 hevent
  have hpU2 : transferEvent :: normalizedAddressArg e 0 ::
      (0 : B256) :: Sevm.argWord e 2 ::
      normalizedAddressArg e 0 :: [] <<+ u2.stack :=
    prefix_of_push hbEvent hpU1
  rcases Line.of_run_cons hemit2 with
    ⟨u3, hdupAmount, hemit3⟩
  have hpU3 : Sevm.argWord e 2 :: transferEvent ::
      normalizedAddressArg e 0 :: (0 : B256) ::
      Sevm.argWord e 2 :: normalizedAddressArg e 0 :: [] <<+ u3.stack :=
    prefix_of_dup_val hdupAmount (by show_nth) hpU2
  rcases of_run_append (mstoreAt 0) hemit3 with
    ⟨u4, hstore, hlog⟩
  rcases of_run_mstoreAt_val hstore hpU3 with ⟨hpU4, hm4⟩
  have hm4' : u4.memory =
      u3.memory.write 0 (Sevm.argWord e 2).toBytes := by
    simpa only [show (0 * 32 : B256).toNat = 0 by decide +kernel]
      using hm4
  rcases of_logWith201_val hpU4 hlog with
    ⟨hpAfterLog, hlogs4⟩
  have hmem_s_u3 : s.memory = u3.memory := by
    calc
      s.memory = s1.memory := Line.of_inv Devm.memory (by
        unfold addressArg normalizeAddress
        line_inv) howner
      _ = s2.memory := Line.of_inv Devm.memory (by
        unfold arg cdl
        line_inv) hamount
      _ = s3.memory := hb3.memory
      _ = u1.memory := Ninst.Hinv.inv (f := Devm.memory) hdupOwner
      _ = u2.memory := hbEvent.memory
      _ = u3.memory := Ninst.Hinv.inv (f := Devm.memory) hdupAmount
  let img1 := Bytes.writeAt img 0 (Sevm.argWord e 2).toBytes
  have hwf4 : Mem.Wf u4.memory := by
    rw [hm4', ← hmem_s_u3]
    exact h_wf.write 0 (Sevm.argWord e 2).toBytes
  have hreads4 : Mem.Reads u4.memory img1 := by
    rw [hm4', ← hmem_s_u3]
    exact Mem.Reads.write h_wf h_reads 0 (Sevm.argWord e 2).toBytes
  have hdata : (u4.memory.read 0 32).1 =
      (Sevm.argWord e 2).toBytes := by
    rw [Mem.Reads.read hreads4 0 32,
      show 32 = (Sevm.argWord e 2).toBytes.length by
        rw [B256.length_toBytes],
      Bytes.sliceD_writeAt]
  have hlogs_s_u4 : s.logs = u4.logs := by
    calc
      s.logs = s1.logs := Line.of_inv Devm.logs (by
        unfold addressArg normalizeAddress
        line_inv) howner
      _ = s2.logs := Line.of_inv Devm.logs (by
        unfold arg cdl
        line_inv) hamount
      _ = s3.logs := hb3.logs
      _ = u1.logs := Ninst.Hinv.inv (f := Devm.logs) hdupOwner
      _ = u2.logs := hbEvent.logs
      _ = u3.logs := Ninst.Hinv.inv (f := Devm.logs) hdupAmount
      _ = u4.logs := Line.of_inv Devm.logs (by
        unfold mstoreAt
        line_inv) hstore
  have hmemAfterLog : s4.memory = u4.memory.extend 0 32 :=
    of_logWith201_mem hpU4 hlog
  have hwfLog : Mem.Wf s4.memory := by
    rw [hmemAfterLog]
    exact hwf4.extend 0 32
  have hreadsLog : Mem.Reads s4.memory img1 := by
    rw [hmemAfterLog]
    exact hreads4.extend 0 32
  rcases Line.of_run_cons run4 with ⟨p1, hpop1, run5⟩
  have hpP1 := prefix_of_pop (of_run_pop hpop1) hpAfterLog
  rcases Line.of_run_cons run5 with ⟨p2, hpop2, hnil⟩
  cases hnil
  have hpP2 := prefix_of_pop (of_run_pop hpop2) hpP1
  have hmem4r : s4.memory = r.memory :=
    (Ninst.Hinv.inv (f := Devm.memory) hpop1).trans
      (Ninst.Hinv.inv (f := Devm.memory) hpop2)
  have hlogs4r : s4.logs = r.logs :=
    (Ninst.Hinv.inv (f := Devm.logs) hpop1).trans
      (Ninst.Hinv.inv (f := Devm.logs) hpop2)
  refine ⟨hpP2, ?_, ?_, ?_, ?_⟩
  · rw [← hlogs4r, hlogs4, hdata, ← hlogs_s_u4]
    rfl
  · calc
      r.output = s4.output :=
        ((Ninst.Hinv.inv (f := Devm.output) hpop1).trans
          (Ninst.Hinv.inv (f := Devm.output) hpop2)).symm
      _ = u4.output :=
        (Line.of_inv Devm.output (by
          unfold logWith
          line_inv) hlog).symm
      _ = u3.output :=
        (Line.of_inv Devm.output (by
          unfold mstoreAt
          line_inv) hstore).symm
      _ = u2.output :=
        (Ninst.Hinv.inv (f := Devm.output) hdupAmount).symm
      _ = u1.output := hbEvent.output.symm
      _ = s3.output :=
        (Ninst.Hinv.inv (f := Devm.output) hdupOwner).symm
      _ = s2.output := hb3.output.symm
      _ = s1.output :=
        (Line.of_inv Devm.output (by
          unfold arg cdl
          line_inv) hamount).symm
      _ = s.output :=
        (Line.of_inv Devm.output (by
          unfold addressArg normalizeAddress
          line_inv) howner).symm
  · rw [← hmem4r]
    exact hwfLog
  · rw [← hmem4r]
    exact ⟨img1, hreadsLog⟩

/-- Exact successful burn continuation: the normalized receiver is debited,
the temporary flash counter is reduced by the same amount, exactly one burn
`Transfer` is appended, and the body returns canonical ABI `true`. -/
theorem flashBurn_effect
    (dp : DeployParams) {e : Sevm} {s r : Devm} {img : Bytes}
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s flashBurn r) :
    Decrease (normalizedAddressArg e 0).toAdr (Sevm.argWord e 2)
        (Stor.rest (Devm.getStor s e.currentTarget))
        (Stor.rest (Devm.getStor r e.currentTarget)) ∧
      Sevm.argWord e 2 ≤
        Stor.rest (Devm.getStor s e.currentTarget)
          (normalizedAddressArg e 0).toAdr ∧
      (Devm.getStor r e.currentTarget).get flashMintedSlot =
        (Devm.getStor s e.currentTarget).get flashMintedSlot -
          Sevm.argWord e 2 ∧
      r.logs = s.logs ++ [flashBurnTransferLog e] ∧
      AbiReturnsTrue r ∧
      Devm.getBal r = Devm.getBal s ∧
      Devm.getCode r = Devm.getCode s := by
  obtain ⟨hdecrease, hcover, hflash, hbal⟩ :=
    flashBurn_storage_at_receiver dp run
  simp only [flashBurn] at run
  rcases of_run_prepend (loadArgBalanceAmount 0 2) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadArgBalanceAmount 0 2 nil_pref hload with
    ⟨balance, ownerWord, hownerWord, hbalance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 : (balance <? Sevm.argWord e 2) :: balance ::
      Sevm.argWord e 2 :: ownerWord :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  have h_burn_lookup :
      ((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]? =
        some (Func.revertWith "WETH: burn amount exceeds balance") := by
    simp [weth10, weth10Aux, burnBalanceErrorSlot, burnBalanceError]
  rcases of_run_branch_call_revertWithFunctional h_burn_lookup run2 with
    ⟨s3, hguardPop, run3⟩
  have hguardStack := hguardPop.stack
  simp only [Stack.Pop, Split, List.nil_append,
    List.cons_append] at hguardStack
  rw [hguardStack] at hp2
  have hflag : (balance <? Sevm.argWord e 2) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  rw [hflag] at hp2
  have hp3 : balance :: Sevm.argWord e 2 :: ownerWord ::
      [] <<+ s3.stack := cons_pref_cons_inv hp2
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  unfold debitLoadedBalance at hdebit
  rcases Line.of_run_cons hdebit with ⟨d1, hsub, hdebit1⟩
  have hpD1 : (balance - Sevm.argWord e 2) :: ownerWord ::
      [] <<+ d1.stack := prefix_of_sub hsub hp3
  rcases Line.of_run_cons hdebit1 with ⟨d2, hswap, hdebit2⟩
  have hswapCore : Stack.Swap (0 : Fin 16).val
      [balance - Sevm.argWord e 2, ownerWord]
      [ownerWord, balance - Sevm.argWord e 2] := Stack.swapCore_zero
  have hpD2 : ownerWord :: (balance - Sevm.argWord e 2) ::
      [] <<+ d2.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hpD1
  rcases Line.of_run_cons hdebit2 with
    ⟨d3, hstoreDebit, hnilDebit⟩
  cases hnilDebit
  have hp4 : [] <<+ s4.stack :=
    prefix_of_sstore hstoreDebit hpD2
  have hmem_s_s4 : s.memory = s4.memory :=
    (Line.of_inv Devm.memory (by line_inv) hload).trans
      ((Line.of_inv Devm.memory (by line_inv) hguard).trans
        (hguardPop.memory.trans
          (Line.of_inv Devm.memory (by line_inv) hdebit)))
  have hwf4 : Mem.Wf s4.memory := by
    rw [← hmem_s_s4]
    exact h_wf
  have hreads4 : Mem.Reads s4.memory img := by
    rw [← hmem_s_s4]
    exact h_reads
  have hlogs_s_s4 : s.logs = s4.logs :=
    (Line.of_inv Devm.logs (by line_inv) hload).trans
      ((Line.of_inv Devm.logs (by line_inv) hguard).trans
        (hguardPop.logs.trans
          ((of_run_sub_logOutput hsub).1.trans
            ((Ninst.Hinv.inv (f := Devm.logs) hswap).trans
              (Ninst.Hinv.inv (f := Devm.logs) hstoreDebit)))))
  let eventLine : Line :=
    addressArg 0 ++ arg 2 ++ [pushB256 0] ++ emitTransfer ++ [pop, pop]
  rcases of_run_prepend eventLine _ run4 with
    ⟨s5, hevent, run5⟩
  obtain ⟨hp5, hlogsEvent, houtputEvent, hwf5, out5, hreads5⟩ :=
    of_flashBurnEvent_effect hp4 hwf4 hreads4 (by
      simpa only [eventLine] using hevent)
  let tailLine : Line :=
    pushFlashMintedSlot ++ [sload] ++ arg 2 ++ [swap 0, sub] ++
      pushFlashMintedSlot ++ [sstore]
  rcases of_run_prepend tailLine _ run5 with
    ⟨s12, htail, hreturn⟩
  unfold tailLine at htail
  rcases of_run_append pushFlashMintedSlot htail with
    ⟨t1, hpushFlash1, htail1⟩
  have hpT1 : flashMintedSlot :: [] <<+ t1.stack :=
    prefix_of_pushFlashMintedSlot hp5 hpushFlash1
  rcases Line.of_run_cons htail1 with
    ⟨t2, hloadFlash, htail2⟩
  rcases prefix_of_sload hloadFlash hpT1 with
    ⟨flash, hpT2, hflashRead⟩
  rcases of_run_append (arg 2) htail2 with
    ⟨t3, harg2, htail3⟩
  have hpT3 : Sevm.argWord e 2 :: flash :: [] <<+ t3.stack :=
    prefix_of_arg hpT2 harg2
  rcases Line.of_run_cons htail3 with
    ⟨t4, hswapFlash, htail4⟩
  have hswapFlashCore : Stack.Swap (0 : Fin 16).val
      [Sevm.argWord e 2, flash] [flash, Sevm.argWord e 2] :=
    Stack.swapCore_zero
  have hpT4 : flash :: Sevm.argWord e 2 :: [] <<+ t4.stack :=
    Stack.prefix_of_swap hswapFlashCore
      (of_run_swap hswapFlash) hpT3
  rcases Line.of_run_cons htail4 with
    ⟨t5, hsubFlash, htail5⟩
  have hpT5 : (flash - Sevm.argWord e 2) :: [] <<+ t5.stack :=
    prefix_of_sub hsubFlash hpT4
  rcases of_run_append pushFlashMintedSlot htail5 with
    ⟨t6, hpushFlash2, htail6⟩
  have hpT6 : flashMintedSlot ::
      (flash - Sevm.argWord e 2) :: [] <<+ t6.stack :=
    prefix_of_pushFlashMintedSlot hpT5 hpushFlash2
  rcases Line.of_run_cons htail6 with
    ⟨t7, hstoreFlash, hnilTail⟩
  cases hnilTail
  have hp12 : [] <<+ s12.stack :=
    prefix_of_sstore hstoreFlash hpT6
  have hmem_s5_s12 : s5.memory = s12.memory :=
    Line.of_inv Devm.memory (by
      unfold pushFlashMintedSlot arg cdl
      line_inv) htail
  have hwf12 : Mem.Wf s12.memory := by
    rw [← hmem_s5_s12]
    exact hwf5
  have hreads12 : Mem.Reads s12.memory out5 := by
    rw [← hmem_s5_s12]
    exact hreads5
  obtain ⟨htrue, hcodeReturn⟩ :=
    of_returnTrue_shared hp12 hwf12 hreads12 hreturn
  have hlogs_s5_s12 : s5.logs = s12.logs :=
    (Line.of_inv Devm.logs (by line_inv) hpushFlash1).trans
      ((Ninst.Hinv.inv (f := Devm.logs) hloadFlash).trans
        ((Line.of_inv Devm.logs (by
          unfold arg cdl
          line_inv) harg2).trans
          ((Ninst.Hinv.inv (f := Devm.logs) hswapFlash).trans
            ((of_run_sub_logOutput hsubFlash).1.trans
              ((Line.of_inv Devm.logs (by line_inv) hpushFlash2).trans
                (Ninst.Hinv.inv (f := Devm.logs) hstoreFlash))))))
  change Func.Run ((weth10 dp).main :: weth10Aux) e s12 returnTrue r at hreturn
  have hlogs_s12_r : s12.logs = r.logs :=
    Func.of_inv Devm.logs Devm.logs (by
      unfold returnTrue pushList
      func_inv) hreturn
  have hlogs : r.logs = s.logs ++ [flashBurnTransferLog e] := by
    rw [← hlogs_s12_r, ← hlogs_s5_s12, hlogsEvent, ← hlogs_s_s4]
  have hcode_s_s3 : Devm.getCode s = Devm.getCode s3 :=
    (Line.of_inv Devm.getCode (by line_inv) hload).trans
      ((Line.of_inv Devm.getCode (by line_inv) hguard).trans
        (funext (fun a => getCode_eq_of_state_eq hguardPop.state a)))
  have hcode_s3_s4 : Devm.getCode s3 = Devm.getCode s4 :=
    Line.of_inv Devm.getCode (by line_inv) hdebit
  have hcode_s4_s5 : Devm.getCode s4 = Devm.getCode s5 :=
    Line.of_inv Devm.getCode (by
      unfold eventLine addressArg normalizeAddress arg cdl emitTransfer
        Blanc.transferFromLog mstoreAt logWith
      line_inv) hevent
  have hcode_s5_s12 : Devm.getCode s5 = Devm.getCode s12 :=
    Line.of_inv Devm.getCode (by
      unfold pushFlashMintedSlot arg cdl
      line_inv) htail
  have hcode : Devm.getCode r = Devm.getCode s :=
    (hcode_s_s3.trans (hcode_s3_s4.trans
      (hcode_s4_s5.trans (hcode_s5_s12.trans hcodeReturn)))).symm
  refine ⟨?_, ?_, hflash, hlogs, htrue, hbal.symm, hcode⟩
  · simpa only [normalizedAddressArg] using hdecrease
  · simpa only [normalizedAddressArg] using hcover

/-! ## End-to-end successful flash-loan observation -/

/-- The callback input-size word computed by the deployed program.  Addition
and alignment are deliberately left in `B256`, so this definition also covers
wrapped dynamic-tail lengths. -/
def flashCallbackRuntimeSize (e : Sevm) : B256 :=
  0xc4 + ((~~~ (31 : B256)) &&& (31 + Sevm.tailLen e 3))

/-- The exact callback-memory image produced from a readable source image.
Unlike `abiCallWithTail`, this retains the raw dynamic length word, the raw
tail bytes available to the machine, and all overwrite behavior. -/
def flashCallbackRuntimeImage (e : Sevm) (source : Bytes) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt
          (Bytes.writeAt
            (Bytes.writeAt
              (Bytes.writeAt
                (Bytes.writeAt
                  (Bytes.writeAt source 0 (Sevm.argWord e 2).toBytes)
                  0 onFlashLoanSelector.toBytes)
                32 e.caller.toB256.toBytes)
              64 e.currentTarget.toB256.toBytes)
            96 (Sevm.argWord e 2).toBytes)
          128 (0 : B256).toBytes)
        160 (0xa0 : B256).toBytes)
      192 (Sevm.tailLen e 3).toBytes)
    224 (Sevm.tailBytes e 3)

/-- The byte string actually offered to the callback when the public frame
starts with fresh memory.  Its length is the `toNat` interpretation of the
modular runtime size, not an assumed canonical ABI length. -/
def flashCallbackRuntimeInput (e : Sevm) : Bytes :=
  (flashCallbackRuntimeImage e []).sliceD callbackArgsOffset.toNat
    (flashCallbackRuntimeSize e).toNat 0

/-- Execution-level bridge from the raw borrower `CALL` to the repayment
entry.  This is the exact projection supplied by `of_run_flashLoanFromCall`:
the callback result and settlement entry agree on storage and balances. -/
def RawFlashSettlementContinuation (dp : DeployParams) (e : Sevm)
    (sc post : Devm) : Prop :=
  ∃ callbackPost settle,
    Ninst.Run e sc call callbackPost ∧
    Func.Run ((weth10 dp).main :: weth10Aux) e settle flashSettle post ∧
    Devm.getStor callbackPost = Devm.getStor settle ∧
    Devm.getBal callbackPost = Devm.getBal settle

/-- Successful raw `flashLoan` effect.  The three named words are exactly the
machine's receiver, token, and principal arguments.  The callback boundary
retains the modular input size and exact memory bytes, while the state clauses
retain the matching credit/debit, allowance fork, logs, and restored flash
counter. -/
def RawFlashLoanSuccessEffect (dp : DeployParams) (e : Sevm)
    (pre post : Devm)
    (receiver token amount : B256) : Prop :=
  Sevm.argWord e 0 = receiver ∧
  Sevm.argWord e 1 = token ∧
  Sevm.argWord e 2 = amount ∧
  token = e.currentTarget.toB256 ∧
  ∃ (recipient : Adr) (sc mid settle burn : Devm)
      (callbackLogs : List Log) (base : B256),
    recipient.toB256 = ((~~~ addressMask) &&& receiver) ∧
    base = (Devm.getStor pre e.currentTarget).get flashMintedSlot ∧
    amount ≤ maxUint112 ∧
    base + amount ≤ maxUint112 ∧
    Increase recipient amount
      (Stor.rest (Devm.getStor pre e.currentTarget))
      (Stor.rest (Devm.getStor sc e.currentTarget)) ∧
    (Devm.getStor sc e.currentTarget).get flashMintedSlot =
      base + amount ∧
    Devm.getCode pre = Devm.getCode sc ∧
    Devm.getBal pre = Devm.getBal sc ∧
    (sc.memory.read callbackArgsOffset.toNat
        (flashCallbackRuntimeSize e).toNat).1 =
      flashCallbackRuntimeInput e ∧
    sc.logs = pre.logs ++ [flashMintTransferLog e recipient] ∧
    sc.output = pre.output ∧
    RawFlashSettlementContinuation dp e sc post ∧
    RawFlashCallbackBoundary e e.currentTarget recipient amount
      (flashCallbackRuntimeSize e) (flashCallbackRuntimeInput e) sc mid ∧
    mid.logs = sc.logs ++ callbackLogs ∧
    Devm.getStor mid = Devm.getStor settle ∧
    Devm.getBal mid = Devm.getBal settle ∧
    Devm.getCode mid = Devm.getCode settle ∧
    settle.logs = mid.logs ∧
    settle.output = mid.output ∧
    Func.Run ((weth10 dp).main :: weth10Aux) e settle
      flashSettle post ∧
    Func.Run ((weth10 dp).main :: weth10Aux) e burn
      flashBurn post ∧
    FlashAllowanceOutcome e settle burn ∧
    Decrease recipient amount
      (Stor.rest (Devm.getStor burn e.currentTarget))
      (Stor.rest (Devm.getStor post e.currentTarget)) ∧
    amount ≤ Stor.rest (Devm.getStor burn e.currentTarget) recipient ∧
    (Devm.getStor post e.currentTarget).get flashMintedSlot = base ∧
    (((Devm.getStor settle e.currentTarget).get
          (flashAllowanceRuntimeKey e) = B256.max ∧
        post.logs = pre.logs ++ [flashMintTransferLog e recipient] ++
          callbackLogs ++ [flashBurnTransferLog e]) ∨
      (∃ allowance : B256,
        allowance ≠ B256.max ∧
        amount ≤ allowance ∧
        (Devm.getStor settle e.currentTarget).get
          (flashAllowanceRuntimeKey e) = allowance ∧
        post.logs = pre.logs ++ [flashMintTransferLog e recipient] ++
          callbackLogs ++
            [flashApprovalLog e (allowance - amount),
              flashBurnTransferLog e])) ∧
    AbiReturnsTrue post ∧
    Devm.getBal post = Devm.getBal mid ∧
    Devm.getCode post = Devm.getCode mid

/-- Exact partial-correctness observation for one successful WETH10
`flashLoan` body.  It exposes the temporary mint at callback entry, the
canonical child frame and arbitrary child-log segment, the two repayment
allowance arms, the receiver burn, the restored flash counter, and the
canonical ABI-true result. -/
def FlashLoanSuccessEffect (e : Sevm) (pre post : Devm)
    (receiver token amount : B256) (data : Bytes) : Prop :=
  Sevm.argWord e 0 = receiver ∧
  Sevm.argWord e 1 = token ∧
  Sevm.argWord e 2 = amount ∧
  Sevm.tailLen e 3 = Nat.toB256 data.length ∧
  Sevm.tailBytes e 3 = data ∧
  token = e.currentTarget.toB256 ∧
  ∃ (recipient : Adr) (sc mid settle burn : Devm)
      (callbackLogs : List Log) (base : B256),
    recipient.toB256 = normalizedAddressArg e 0 ∧
    base = (Devm.getStor pre e.currentTarget).get flashMintedSlot ∧
    amount ≤ maxUint112 ∧
    base + amount ≤ maxUint112 ∧
    Increase recipient amount
      (Stor.rest (Devm.getStor pre e.currentTarget))
      (Stor.rest (Devm.getStor sc e.currentTarget)) ∧
    (Devm.getStor sc e.currentTarget).get flashMintedSlot =
      base + amount ∧
    Devm.getCode pre = Devm.getCode sc ∧
    Devm.getBal pre = Devm.getBal sc ∧
    (sc.memory.read callbackArgsOffset.toNat
        (196 + ceil32 data.length)).1 =
      abiCallWithTail onFlashLoanSelector
        [e.caller.toB256, e.currentTarget.toB256, amount, 0] data ∧
    sc.logs = pre.logs ++ [flashMintTransferLog e recipient] ∧
    sc.output = pre.output ∧
    FlashCallbackBoundary e e.currentTarget recipient amount data sc mid ∧
    mid.logs = sc.logs ++ callbackLogs ∧
    Devm.getStor mid = Devm.getStor settle ∧
    Devm.getBal mid = Devm.getBal settle ∧
    Devm.getCode mid = Devm.getCode settle ∧
    settle.logs = mid.logs ∧
    settle.output = mid.output ∧
    FlashAllowanceOutcome e settle burn ∧
    Decrease recipient amount
      (Stor.rest (Devm.getStor burn e.currentTarget))
      (Stor.rest (Devm.getStor post e.currentTarget)) ∧
    amount ≤ Stor.rest (Devm.getStor burn e.currentTarget) recipient ∧
    (Devm.getStor post e.currentTarget).get flashMintedSlot = base ∧
    (((Devm.getStor settle e.currentTarget).get
          (flashAllowanceRuntimeKey e) = B256.max ∧
        post.logs = pre.logs ++ [flashMintTransferLog e recipient] ++
          callbackLogs ++ [flashBurnTransferLog e]) ∨
      (∃ allowance : B256,
        allowance ≠ B256.max ∧
        amount ≤ allowance ∧
        (Devm.getStor settle e.currentTarget).get
          (flashAllowanceRuntimeKey e) = allowance ∧
        post.logs = pre.logs ++ [flashMintTransferLog e recipient] ++
          callbackLogs ++
            [flashApprovalLog e (allowance - amount),
              flashBurnTransferLog e])) ∧
    AbiReturnsTrue post ∧
    Devm.getBal post = Devm.getBal mid ∧
    Devm.getCode post = Devm.getCode mid

/-- A successful `flashLoan` body has a complete raw effect without assuming
that its calldata tail is canonically encoded or that the callback-size
arithmetic does not wrap. -/
theorem flashLoan_rawSuccessEffect
    (dp : DeployParams) {e : Sevm} {pre post : Devm}
    (h_wf : Mem.Wf pre.memory)
    (h_fresh : Mem.Reads pre.memory [])
    (h_code : some (pre.getCode e.currentTarget).toList =
      Prog.compile (weth10 dp))
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e pre
      flashLoan post) :
    RawFlashLoanSuccessEffect dp e pre post
      (Sevm.argWord e 0) (Sevm.argWord e 1) (Sevm.argWord e 2) := by
  obtain ⟨recipient, sc, g, inputSize, base,
      hbase, hrecipient, htoken, hamount, htotal, hinc, hflash,
      hcodeSc, hbalSc, hinputSize, hstack, hmemory, hmintLogs,
      hsetupOutput, htail⟩ := of_flashLoan_toCall_frame dp run
  have hinputSize' : inputSize = flashCallbackRuntimeSize e := by
    simpa only [flashCallbackRuntimeSize] using hinputSize
  have hstack' := hstack
  rw [hinputSize'] at hstack'
  obtain ⟨hwfSc, hreadsSc⟩ := hmemory [] h_wf h_fresh
  have hreadsRuntime :
      Mem.Reads sc.memory (flashCallbackRuntimeImage e []) := by
    simpa only [flashCallbackRuntimeImage] using hreadsSc
  have hwindow :
      (sc.memory.read callbackArgsOffset.toNat
          (flashCallbackRuntimeSize e).toNat).1 =
        flashCallbackRuntimeInput e := by
    rw [Mem.Reads.read hreadsRuntime]
    rfl
  have htail' : Func.Run ((weth10 dp).main :: weth10Aux) e sc
      flashLoanSuccessTail post := by
    simpa only [flashLoanSuccessTail, flashLoanFromCall] using htail
  have hcontinuation : RawFlashSettlementContinuation dp e sc post := by
    unfold RawFlashSettlementContinuation
    exact of_run_flashLoanFromCall dp htail
  obtain ⟨mid, settle, hcallback, hstorMid, hbalMid, hcodeMid,
      hsettleLogs, hsettleOutput, hwfSettle, hreadsSettleEx,
      hsettle⟩ :=
    of_rawFlashLoanSuccessTail dp hstack' hwfSc hreadsRuntime
      (by rfl) htail'
  obtain ⟨settleImg, hreadsSettle⟩ := hreadsSettleEx
  obtain ⟨callbackLogs, hcallbackLogs⟩ :=
    RawFlashCallbackBoundary.exists_log_segment hcallback
  obtain ⟨burn, hburn, hallowance, hwfBurn, burnImg, hreadsBurn⟩ :=
    of_flashSettle_allowance dp hwfSettle hreadsSettle hsettle
  obtain ⟨hdecrease, hcover, hflashBurn, hburnLogs, htrue,
      hbalBurn, hcodeBurn⟩ :=
    flashBurn_effect dp hwfBurn hreadsBurn hburn
  have hrecipient' :
      recipient.toB256 = normalizedAddressArg e 0 := by
    simpa only [normalizedAddressArg] using hrecipient
  have hrecipientAdr : (normalizedAddressArg e 0).toAdr = recipient := by
    rw [← hrecipient', toAdr_toB256]
  have hdecrease' : Decrease recipient (Sevm.argWord e 2)
      (Stor.rest (Devm.getStor burn e.currentTarget))
      (Stor.rest (Devm.getStor post e.currentTarget)) := by
    simpa only [hrecipientAdr] using hdecrease
  have hcover' : Sevm.argWord e 2 ≤
      Stor.rest (Devm.getStor burn e.currentTarget) recipient := by
    simpa only [hrecipientAdr] using hcover
  have hmintLogs' :
      sc.logs = pre.logs ++ [flashMintTransferLog e recipient] := by
    simpa only [flashMintTransferLog] using hmintLogs
  have hlogFork := repayment_log_fork (amount := Sevm.argWord e 2)
    rfl hmintLogs' hcallbackLogs hsettleLogs hallowance hburnLogs
  have hexact := flashLoan_exactRelFuncSound dp e.currentTarget
    rfl h_code (flashExactDepth dp e.currentTarget e.depth) run
  have hcounter :
      (Devm.getStor post e.currentTarget).get flashMintedSlot = base := by
    unfold FlashExactRel at hexact
    exact hexact.trans hbase.symm
  have hbalFinal : Devm.getBal post = Devm.getBal mid :=
    hbalBurn.trans (hallowance.2.2.1.trans hbalMid.symm)
  have hcodeFinal : Devm.getCode post = Devm.getCode mid :=
    hcodeBurn.trans (hallowance.2.2.2.trans hcodeMid.symm)
  refine ⟨rfl, rfl, rfl, htoken,
    recipient, sc, mid, settle, burn, callbackLogs, base,
    hrecipient, hbase, hamount, htotal, hinc, hflash, hcodeSc,
    hbalSc, hwindow, hmintLogs', hsetupOutput, hcontinuation, hcallback,
    hcallbackLogs, hstorMid, hbalMid, hcodeMid, hsettleLogs,
    hsettleOutput, hsettle, hburn, hallowance, hdecrease', hcover', hcounter,
    hlogFork, htrue, hbalFinal, hcodeFinal⟩

/-- A successful selected `flashLoan` body has the exact callback, repayment,
counter-restoration, return, and log effect described above. -/
theorem flashLoan_successEffect
    (dp : DeployParams) {e : Sevm} {pre post : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_dec : Sevm.DecodesCallWithTail e flashLoanSelector
      [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf pre.memory)
    (h_fresh : Mem.Reads pre.memory [])
    (h_code : some (pre.getCode e.currentTarget).toList =
      Prog.compile (weth10 dp))
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e pre
      flashLoan post) :
    FlashLoanSuccessEffect e pre post receiver token amount data := by
  have h_data_len : data.length < 2 ^ 256 := by
    have hceil := Nat.le_ceil32 data.length
    omega
  have h0 : Sevm.argWord e 0 = receiver :=
    argWord_zero_of_decodes h_dec
  have h1 : Sevm.argWord e 1 = token :=
    argWord_one_of_decodes h_dec
  have h2 : Sevm.argWord e 2 = amount :=
    argWord_two_of_decodes h_dec
  have htl : Sevm.tailLen e 3 = Nat.toB256 data.length :=
    tailLen_three_of_decodes h_dec
  have htb : Sevm.tailBytes e 3 = data :=
    tailBytes_three_of_decodes h_data_len h_dec
  have hsizeWord :
      (0xc4 : B256) +
          ((~~~ (31 : B256)) &&& (31 + Nat.toB256 data.length)) =
        Nat.toB256 (196 + ceil32 data.length) := by
    rw [← toB256_toNat ((0xc4 : B256) + _),
      toNat_flashCallbackArgsSize h_size]
  obtain ⟨recipient, sc, g, inputSize, base,
      hbase, hrecipient, htoken, hamount, htotal, hinc, hflash,
      hcodeSc, hbalSc, hinputSize, hstack, hmemory, hmintLogs,
      hsetupOutput, htail⟩ := of_flashLoan_toCall_frame dp run
  have htokenNamed : token = e.currentTarget.toB256 :=
    h1.symm.trans htoken
  have hrecipient' : recipient.toB256 = normalizedAddressArg e 0 := by
    simpa only [normalizedAddressArg] using hrecipient
  have hamount' : amount ≤ maxUint112 := by
    simpa only [h2] using hamount
  have htotal' : base + amount ≤ maxUint112 := by
    simpa only [h2] using htotal
  have hinc' : Increase recipient amount
      (Stor.rest (Devm.getStor pre e.currentTarget))
      (Stor.rest (Devm.getStor sc e.currentTarget)) := by
    simpa only [h2] using hinc
  have hflash' :
      (Devm.getStor sc e.currentTarget).get flashMintedSlot =
        base + amount := by
    simpa only [h2] using hflash
  have hstack' := hstack
  rw [hinputSize, htl, hsizeWord, h2] at hstack'
  obtain ⟨hwfSc, hreadsSc⟩ := hmemory [] h_wf h_fresh
  rw [h2, htl, htb, flashCallbackImage_nil] at hreadsSc
  have hwin :
      (onFlashLoanSelector.toBytes ++ e.caller.toB256.toBytes ++
        e.currentTarget.toB256.toBytes ++ amount.toBytes ++
        (0 : B256).toBytes ++ (0xa0 : B256).toBytes ++
        (Nat.toB256 data.length).toBytes ++ data).sliceD
          callbackArgsOffset.toNat (196 + ceil32 data.length) 0 =
        abiCallWithTail onFlashLoanSelector
          [e.caller.toB256, e.currentTarget.toB256, amount, 0] data := by
    rw [show callbackArgsOffset.toNat = 28 from rfl]
    exact flashCallbackWindow onFlashLoanSelector e.caller.toB256
      e.currentTarget.toB256 amount data
  have hwindow :
      (sc.memory.read callbackArgsOffset.toNat
          (196 + ceil32 data.length)).1 =
        abiCallWithTail onFlashLoanSelector
          [e.caller.toB256, e.currentTarget.toB256, amount, 0] data := by
    rw [Mem.Reads.read hreadsSc]
    exact hwin
  have htail' : Func.Run ((weth10 dp).main :: weth10Aux) e sc
      flashLoanSuccessTail post := by
    simpa only [flashLoanSuccessTail, flashLoanFromCall] using htail
  obtain ⟨mid, settle, hcallback, hstorMid, hbalMid, hcodeMid,
      hsettleLogs, hsettleOutput, hwfSettle, hreadsSettleEx,
      hsettle⟩ :=
    of_flashLoanSuccessTail dp hstack' hwfSc hreadsSc hwin h_size htail'
  obtain ⟨settleImg, hreadsSettle⟩ := hreadsSettleEx
  obtain ⟨callbackLogs, hcallbackLogs⟩ :=
    FlashCallbackBoundary.exists_log_segment hcallback
  obtain ⟨burn, hburn, hallowance, hwfBurn, burnImg, hreadsBurn⟩ :=
    of_flashSettle_allowance dp hwfSettle hreadsSettle hsettle
  obtain ⟨hdecrease, hcover, hflashBurn, hburnLogs, htrue,
      hbalBurn, hcodeBurn⟩ :=
    flashBurn_effect dp hwfBurn hreadsBurn hburn
  have hrecipientAdr : (normalizedAddressArg e 0).toAdr = recipient := by
    rw [← hrecipient', toAdr_toB256]
  have hdecrease' : Decrease recipient amount
      (Stor.rest (Devm.getStor burn e.currentTarget))
      (Stor.rest (Devm.getStor post e.currentTarget)) := by
    simpa only [hrecipientAdr, h2] using hdecrease
  have hcover' : amount ≤
      Stor.rest (Devm.getStor burn e.currentTarget) recipient := by
    simpa only [hrecipientAdr, h2] using hcover
  have hmintLogs' :
      sc.logs = pre.logs ++ [flashMintTransferLog e recipient] := by
    simpa only [flashMintTransferLog] using hmintLogs
  have hlogFork := repayment_log_fork h2 hmintLogs'
    hcallbackLogs hsettleLogs hallowance hburnLogs
  have hexact := flashLoan_exactRelFuncSound dp e.currentTarget
    rfl h_code (flashExactDepth dp e.currentTarget e.depth) run
  have hcounter :
      (Devm.getStor post e.currentTarget).get flashMintedSlot = base := by
    unfold FlashExactRel at hexact
    exact hexact.trans hbase.symm
  have hbalFinal : Devm.getBal post = Devm.getBal mid :=
    hbalBurn.trans (hallowance.2.2.1.trans hbalMid.symm)
  have hcodeFinal : Devm.getCode post = Devm.getCode mid :=
    hcodeBurn.trans (hallowance.2.2.2.trans hcodeMid.symm)
  refine ⟨h0, h1, h2, htl, htb, htokenNamed,
    recipient, sc, mid, settle, burn, callbackLogs, base,
    hrecipient', hbase, hamount', htotal', hinc', hflash', hcodeSc,
    hbalSc, hwindow, hmintLogs', hsetupOutput, hcallback,
    hcallbackLogs, hstorMid, hbalMid, hcodeMid, hsettleLogs,
    hsettleOutput, hallowance, hdecrease', hcover', hcounter,
    hlogFork, htrue, hbalFinal, hcodeFinal⟩

/-- Compiled public-selector form of `flashLoan_rawSuccessEffect`.  It imposes
no decoded-tail witness and no callback-size no-wrap premise. -/
theorem weth10_flashLoan_rawSuccessEffect
    (dp : DeployParams) {e : Sevm} {pre post : Devm}
    (h_code : some e.code.toList = Prog.compile (weth10 dp))
    (h_state_code : pre.getCode e.currentTarget = e.code)
    (h_sel : Sevm.selector e = flashLoanSelector)
    (h_nonempty : e.data.length.toB256 ≠ 0)
    (h_wf : Mem.Wf pre.memory)
    (h_fresh : Mem.Reads pre.memory [])
    (exc : Exec 0 e pre (.ok post)) :
    e.value = 0 ∧
      RawFlashLoanSuccessEffect dp e pre post
        (Sevm.argWord e 0) (Sevm.argWord e 1) (Sevm.argWord e 2) := by
  rcases exec_enters_weth10Nonpayable_logs exc h_code h_sel h_nonempty
      (flashLoan_mem_weth10Funcs dp) with
    ⟨bodyPre, hvalue, hstor, hbal, hcodeFrame, hmemory,
      hlogs, houtput, hbody⟩
  have hbodyCode : some (bodyPre.getCode e.currentTarget).toList =
      Prog.compile (weth10 dp) := by
    rw [hcodeFrame, h_state_code]
    exact h_code
  have hwfBody : Mem.Wf bodyPre.memory := by
    rw [hmemory]
    exact h_wf
  have hfreshBody : Mem.Reads bodyPre.memory [] := by
    rw [hmemory]
    exact h_fresh
  have heffect := flashLoan_rawSuccessEffect dp hwfBody hfreshBody
    hbodyCode hbody
  refine ⟨hvalue, ?_⟩
  unfold RawFlashLoanSuccessEffect at heffect ⊢
  simpa only [hstor, hbal, hcodeFrame, hlogs, houtput] using heffect

/-- Compiled public-selector form of `flashLoan_successEffect`.  The
state-code equality is the direct-call linkage needed to identify any nested
call back into the same WETH10 deployment. -/
theorem weth10_flashLoan_successEffect
    (dp : DeployParams) {e : Sevm} {pre post : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_code : some e.code.toList = Prog.compile (weth10 dp))
    (h_state_code : pre.getCode e.currentTarget = e.code)
    (h_sel : Sevm.selector e = flashLoanSelector)
    (h_nonempty : e.data.length.toB256 ≠ 0)
    (h_dec : Sevm.DecodesCallWithTail e flashLoanSelector
      [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_wf : Mem.Wf pre.memory)
    (h_fresh : Mem.Reads pre.memory [])
    (exc : Exec 0 e pre (.ok post)) :
    e.value = 0 ∧
      FlashLoanSuccessEffect e pre post receiver token amount data := by
  rcases exec_enters_weth10Nonpayable_logs exc h_code h_sel h_nonempty
      (flashLoan_mem_weth10Funcs dp) with
    ⟨bodyPre, hvalue, hstor, hbal, hcodeFrame, hmemory,
      hlogs, houtput, hbody⟩
  have hbodyCode : some (bodyPre.getCode e.currentTarget).toList =
      Prog.compile (weth10 dp) := by
    rw [hcodeFrame, h_state_code]
    exact h_code
  have hwfBody : Mem.Wf bodyPre.memory := by
    rw [hmemory]
    exact h_wf
  have hfreshBody : Mem.Reads bodyPre.memory [] := by
    rw [hmemory]
    exact h_fresh
  have heffect := flashLoan_successEffect dp h_dec h_size
    hwfBody hfreshBody hbodyCode hbody
  refine ⟨hvalue, ?_⟩
  unfold FlashLoanSuccessEffect at heffect ⊢
  simpa only [hstor, hbal, hcodeFrame, hlogs, houtput] using heffect

end Weth10

end Blanc
