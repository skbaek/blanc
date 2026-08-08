-- Exact state, event, and return observations for WETH10's ordinary mutators.

import Blanc.Weth10Functional

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Weth10

/-! ## Exact calldata and allowance-key images -/

/-- The tagged allowance key computed by `approve` from the exact caller word
and the first raw ABI argument word copied from calldata. -/
def approveRuntimeKey (e : Sevm) : B256 :=
  allowanceTagWord |||
    (allowancePayloadMask &&&
      Bytes.keccak
        (e.caller.toB256.toBytes ++ e.data.sliceD 4 32 0))

/-- Exact memory effect of `argCopy 1 0 1`, the spender-word copy used by
`approvePrefix`. -/
lemma of_run_argCopy101 {e : Sevm} {s s' : Devm} {xs : Stack}
    (hp : xs <<+ s.stack)
    (run : Line.Run e s (argCopy 1 0 1) s') :
    xs <<+ s'.stack ∧
      s'.memory = s.memory.write 32 (e.data.sliceD 4 32 0) := by
  simp only [argCopy, cdc] at run
  rcases Line.of_run_cons run with ⟨u1, q1, run1⟩
  have hp1 : (32 : B256) :: xs <<+ u1.stack := by
    have hword : (1 * 32 : B256) = 32 := by decide +kernel
    rw [hword] at q1
    exact prefix_of_push (of_run_pushB256 q1) hp
  rcases Line.of_run_cons run1 with ⟨u2, q2, run2⟩
  have hp2 : (4 : B256) :: 32 :: xs <<+ u2.stack := by
    have hword : (0 * 32 + 4 : B256) = 4 := by decide +kernel
    rw [hword] at q2
    exact prefix_of_push (of_run_pushB256 q2) hp1
  rcases Line.of_run_cons run2 with ⟨u3, q3, run3⟩
  have hp3 : (32 : B256) :: 4 :: 32 :: xs <<+ u3.stack := by
    have hword : (1 * 32 : B256) = 32 := by decide +kernel
    rw [hword] at q3
    exact prefix_of_push (of_run_pushB256 q3) hp2
  rcases Line.of_run_cons run3 with ⟨u4, q4, hnil⟩
  cases hnil
  rcases prefix_of_calldatacopy_val q4 hp3 with ⟨hp4, hm4⟩
  refine ⟨hp4, ?_⟩
  rw [hm4,
    ← (Ninst.Hinv.inv (f := Devm.memory) q3),
    ← (Ninst.Hinv.inv (f := Devm.memory) q2),
    ← (Ninst.Hinv.inv (f := Devm.memory) q1)]
  rfl

/-- Exact memory effect of `argCopy 0 1 1`, the value-word copy used by the
canonical `Approval` and `Transfer` log fragments. -/
lemma of_run_argCopy011 {e : Sevm} {s s' : Devm} {xs : Stack}
    (hp : xs <<+ s.stack)
    (run : Line.Run e s (argCopy 0 1 1) s') :
    xs <<+ s'.stack ∧
      s'.memory = s.memory.write 0 (e.data.sliceD 36 32 0) := by
  simp only [argCopy, cdc] at run
  rcases Line.of_run_cons run with ⟨u1, q1, run1⟩
  have hp1 : (32 : B256) :: xs <<+ u1.stack := by
    have hword : (1 * 32 : B256) = 32 := by decide +kernel
    rw [hword] at q1
    exact prefix_of_push (of_run_pushB256 q1) hp
  rcases Line.of_run_cons run1 with ⟨u2, q2, run2⟩
  have hp2 : (36 : B256) :: 32 :: xs <<+ u2.stack := by
    have hword : (1 * 32 + 4 : B256) = 36 := by decide +kernel
    rw [hword] at q2
    exact prefix_of_push (of_run_pushB256 q2) hp1
  rcases Line.of_run_cons run2 with ⟨u3, q3, run3⟩
  have hp3 : (0 : B256) :: 36 :: 32 :: xs <<+ u3.stack := by
    have hword : (0 * 32 : B256) = 0 := by decide +kernel
    rw [hword] at q3
    exact prefix_of_push (of_run_pushB256 q3) hp2
  rcases Line.of_run_cons run3 with ⟨u4, q4, hnil⟩
  cases hnil
  rcases prefix_of_calldatacopy_val q4 hp3 with ⟨hp4, hm4⟩
  refine ⟨hp4, ?_⟩
  rw [hm4,
    ← (Ninst.Hinv.inv (f := Devm.memory) q3),
    ← (Ninst.Hinv.inv (f := Devm.memory) q2),
    ← (Ninst.Hinv.inv (f := Devm.memory) q1)]
  rfl

/-- Reading the two words after the caller and spender writes yields exactly
their concatenated 64-byte ABI image. -/
lemma slice_two_words (img : Bytes) (a : B256) (b : Bytes)
    (hb : b.length = 32) :
    (Bytes.writeAt (Bytes.writeAt img 0 a.toBytes) 32 b).sliceD 0 64 0 =
      a.toBytes ++ b := by
  have ha : a.toBytes.length = 32 := B256.length_toBytes a
  have e1 : Bytes.writeAt img 0 a.toBytes =
      a.toBytes ++ img.drop 32 := by
    rw [Bytes.writeAt, ha, show List.takeD 0 img 0 = [] from rfl,
      List.nil_append, Nat.zero_add]
  have e2 : Bytes.writeAt (a.toBytes ++ img.drop 32) 32 b =
      a.toBytes ++ (b ++ (img.drop 32).drop 32) := by
    rw [Bytes.writeAt, hb, List.takeD_eq_take _ (by simp [ha]),
      List.take_left' ha,
      show 32 + 32 = a.toBytes.length + 32 from by rw [ha],
      List.drop_append, List.append_assoc]
    simp [ha]
  rw [e1, e2]
  unfold List.sliceD
  rw [List.drop_zero,
    List.takeD_eq_take _ (by simp [ha, hb]; omega)]
  rw [show a.toBytes ++ (b ++ List.drop 32 (List.drop 32 img)) =
      (a.toBytes ++ b) ++ List.drop 32 (List.drop 32 img) by
        simp [List.append_assoc],
    List.take_left' (by simp [ha, hb])]

/-- Value-carrying allowance-key computation for an exact readable memory
image. -/
lemma prefix_of_allowanceKeyFromMemory_image
    {e : Sevm} {xs : Stack} {s s' : Devm} {img : Bytes}
    (hp : xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Line.Run e s allowanceKeyFromMemory s') :
    (allowanceTagWord |||
      (allowancePayloadMask &&& Bytes.keccak (img.sliceD 0 64 0))) ::
        xs <<+ s'.stack ∧
      Mem.Wf s'.memory ∧ Mem.Reads s'.memory img := by
  unfold allowanceKeyFromMemory pushList at run
  simp only [List.map] at run
  rcases Line.of_run_cons run with ⟨s1, hpush64, run1⟩
  have hb64 := of_run_pushB256 hpush64
  have hp1 : (64 : B256) :: xs <<+ s1.stack :=
    prefix_of_push hb64 hp
  have hr1 : Mem.Reads s1.memory img := by
    rw [← hb64.memory]
    exact h_reads
  rcases Line.of_run_cons run1 with ⟨s2, hpush0, run2⟩
  have hb0 := of_run_pushB256 hpush0
  have hp2 : (0 : B256) :: 64 :: xs <<+ s2.stack :=
    prefix_of_push hb0 hp1
  have hr2 : Mem.Reads s2.memory img := by
    rw [← hb0.memory]
    exact hr1
  have hm2 : s.memory = s2.memory := hb64.memory.trans hb0.memory
  rcases Line.of_run_cons run2 with ⟨s3, hkec, run3⟩
  rcases prefix_of_kec_val hkec hp2 with ⟨hp3, hm3⟩
  change (s2.memory.read 0 64).1.keccak :: xs <<+ s3.stack at hp3
  rw [Mem.Reads.read hr2 0 64] at hp3
  rcases Line.of_run_cons run3 with ⟨s4, hpushMask, run4⟩
  have hp4 :
      allowancePayloadMask :: Bytes.keccak (img.sliceD 0 64 0) :: xs <<+
        s4.stack :=
    prefix_of_push (of_run_pushB256 hpushMask) hp3
  rcases Line.of_run_cons run4 with ⟨s5, hand, run5⟩
  have hp5 :
      (allowancePayloadMask &&& Bytes.keccak (img.sliceD 0 64 0)) :: xs <<+
        s5.stack :=
    prefix_of_and hand hp4
  rcases Line.of_run_cons run5 with ⟨s6, hpushTag, run6⟩
  have hp6 :
      allowanceTagWord ::
        (allowancePayloadMask &&& Bytes.keccak (img.sliceD 0 64 0)) :: xs <<+
          s6.stack :=
    prefix_of_push (of_run_pushB256 hpushTag) hp5
  rcases Line.of_run_cons run6 with ⟨s7, hor, hnil⟩
  cases hnil
  have hp7 := prefix_of_or hor hp6
  have hmTail : s3.memory = s'.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons hpushMask
        (Line.Run.cons hand
          (Line.Run.cons hpushTag (Line.Run.cons hor Line.Run.nil))))
  refine ⟨hp7, ?_, ?_⟩
  · rw [← hmTail, hm3, ← hm2]
    exact h_wf.extend _ _
  · rw [← hmTail, hm3, ← hm2]
    exact Mem.Reads.extend h_reads _ _

/-! ## Approve -/

/-- The exact canonical `Approval` entry emitted by the raw `approve` body.
The spender topic and data word deliberately name the machine's ABI reads, so
the theorem below remains true before specializing to canonical calldata. -/
def approveApprovalLog (e : Sevm) : Log :=
  ⟨e.currentTarget,
    [approvalEvent, e.caller.toB256, Sevm.argWord e 0],
    e.data.sliceD 36 32 0⟩

/-- A successful selected `approve` body performs its one tagged allowance
write, appends exactly one `Approval` log, and returns canonical ABI `true`.
The theorem also records that no ETH balance or account code changes. -/
theorem approve_effect
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    {xs : Stack} {img : Bytes}
    (hp : xs <<+ s.stack)
    (hwf : Mem.Wf s.memory)
    (hr : Mem.Reads s.memory img)
    (run : Func.Run fs sevm s approve r) :
    Devm.getStor r sevm.currentTarget =
        (Devm.getStor s sevm.currentTarget).set
          (approveRuntimeKey sevm) (Sevm.argWord sevm 1) ∧
      r.logs = s.logs ++ [approveApprovalLog sevm] ∧
      AbiReturnsTrue r ∧
      Devm.getBal r = Devm.getBal s ∧
      Devm.getCode r = Devm.getCode s := by
  simp only [approve] at run
  rcases of_run_prepend approvePrefix _ run with
    ⟨t, hprefix, hreturn⟩
  have hbalPrefix : Devm.getBal s = Devm.getBal t :=
    Line.of_inv Devm.getBal (by
      unfold approvePrefix allowanceKeyFromMemory Blanc.logApprove argCopy cdc pushList
      line_inv) hprefix
  have hcodePrefix : Devm.getCode s = Devm.getCode t :=
    Line.of_inv Devm.getCode (by
      unfold approvePrefix allowanceKeyFromMemory Blanc.logApprove argCopy cdc pushList
      line_inv) hprefix
  have hstorReturn : Devm.getStor t = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by
      unfold returnTrue pushList
      func_inv) hreturn
  have hbalReturn : Devm.getBal t = Devm.getBal r :=
    Func.of_inv Devm.getBal Devm.getBal (by
      unfold returnTrue pushList
      func_inv) hreturn
  have hlogsReturn : t.logs = r.logs :=
    Func.of_inv Devm.logs Devm.logs (by
      unfold returnTrue pushList
      func_inv) hreturn

  unfold approvePrefix at hprefix
  rcases Line.of_run_cons hprefix with ⟨s1, hcaller, hprefix⟩
  have hp1 : sevm.caller.toB256 :: xs <<+ s1.stack :=
    prefix_of_push (of_run_caller hcaller) hp
  have hm1 : s.memory = s1.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hcaller
  have hwf1 : Mem.Wf s1.memory := hm1 ▸ hwf
  have hr1 : Mem.Reads s1.memory img := hm1 ▸ hr

  rcases of_run_append (mstoreAt 0) hprefix with
    ⟨s2, hmstore0, hprefix⟩
  rcases of_run_mstoreAt_val hmstore0 hp1 with ⟨hp2, hm2⟩
  rw [show (((0 : B256) * 32).toNat) = 0 from rfl] at hm2
  let img1 := Bytes.writeAt img 0 sevm.caller.toB256.toBytes
  have hwf2 : Mem.Wf s2.memory := by
    rw [hm2]
    exact hwf1.write _ _
  have hr2 : Mem.Reads s2.memory img1 := by
    rw [hm2]
    exact Mem.Reads.write hwf1 hr1 0 _

  rcases of_run_append (argCopy 1 0 1) hprefix with
    ⟨s3, hcopySpender, hprefix⟩
  rcases of_run_argCopy101 hp2 hcopySpender with ⟨hp3, hm3⟩
  let spenderBytes := sevm.data.sliceD 4 32 0
  let img2 := Bytes.writeAt img1 32 spenderBytes
  have hwf3 : Mem.Wf s3.memory := by
    rw [hm3]
    exact hwf2.write _ _
  have hr3 : Mem.Reads s3.memory img2 := by
    rw [hm3]
    exact Mem.Reads.write hwf2 hr2 32 _

  rcases of_run_append allowanceKeyFromMemory hprefix with
    ⟨s4, hkey, hprefix⟩
  rcases prefix_of_allowanceKeyFromMemory_image hp3 hwf3 hr3 hkey with
    ⟨hp4raw, hwf4, hr4⟩
  have hspenderLen : spenderBytes.length = 32 := by
    unfold spenderBytes List.sliceD
    rw [List.takeD_length]
  have himg2 :
      img2.sliceD 0 64 0 =
        sevm.caller.toB256.toBytes ++ spenderBytes := by
    exact slice_two_words img sevm.caller.toB256 spenderBytes hspenderLen
  have hp4 : approveRuntimeKey sevm :: xs <<+ s4.stack := by
    rw [himg2] at hp4raw
    simpa only [approveRuntimeKey, img1, spenderBytes] using hp4raw

  rcases of_run_append (arg 1) hprefix with
    ⟨s5, hargValue, hprefix⟩
  have hp5 : Sevm.argWord sevm 1 :: approveRuntimeKey sevm :: xs <<+
      s5.stack := prefix_of_arg hp4 hargValue
  rcases Line.of_run_cons hprefix with ⟨s6, hswap, hprefix⟩
  have hswapCore : Stack.Swap (0 : Fin 16).val
      (Sevm.argWord sevm 1 :: approveRuntimeKey sevm :: xs)
      (approveRuntimeKey sevm :: Sevm.argWord sevm 1 :: xs) :=
    Stack.swapCore_zero
  have hp6 : approveRuntimeKey sevm :: Sevm.argWord sevm 1 :: xs <<+
      s6.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp5
  rcases Line.of_run_cons hprefix with ⟨s7, hstore, hlogApprove⟩
  have hp7 : xs <<+ s7.stack := prefix_of_sstore hstore hp6
  have hset :
      Devm.getStor s7 sevm.currentTarget =
        (Devm.getStor s6 sevm.currentTarget).set
          (approveRuntimeKey sevm) (Sevm.argWord sevm 1) :=
    sstore_getStor_set hstore hp6
  have hstorBefore : Devm.getStor s = Devm.getStor s6 := by
    calc
      Devm.getStor s = Devm.getStor s1 :=
        Ninst.Hinv.inv (f := Devm.getStor) hcaller
      _ = Devm.getStor s2 :=
        Line.of_inv Devm.getStor (by line_inv) hmstore0
      _ = Devm.getStor s3 :=
        Line.of_inv Devm.getStor (by
          unfold argCopy cdc
          line_inv) hcopySpender
      _ = Devm.getStor s4 :=
        Line.of_inv Devm.getStor (by
          unfold allowanceKeyFromMemory pushList
          line_inv) hkey
      _ = Devm.getStor s5 :=
        Line.of_inv Devm.getStor (by line_inv) hargValue
      _ = Devm.getStor s6 :=
        Ninst.Hinv.inv (f := Devm.getStor) hswap
  have hmem4to7 : s4.memory = s7.memory := by
    calc
      s4.memory = s5.memory :=
        Line.of_inv Devm.memory (by line_inv) hargValue
      _ = s6.memory := Ninst.Hinv.inv (f := Devm.memory) hswap
      _ = s7.memory := Ninst.Hinv.inv (f := Devm.memory) hstore
  have hwf7 : Mem.Wf s7.memory := hmem4to7 ▸ hwf4
  have hr7 : Mem.Reads s7.memory img2 := hmem4to7 ▸ hr4
  have hstorLog : Devm.getStor s7 = Devm.getStor t :=
    Line.of_inv Devm.getStor (by
      unfold Blanc.logApprove argCopy cdc
      line_inv) hlogApprove

  unfold Blanc.logApprove at hlogApprove
  rcases of_run_append (argCopy 0 1 1) hlogApprove with
    ⟨s8, hcopyValue, hlogApprove⟩
  rcases of_run_argCopy011 hp7 hcopyValue with ⟨hp8, hm8⟩
  let valueBytes := sevm.data.sliceD 36 32 0
  let img3 := Bytes.writeAt img2 0 valueBytes
  have hwf8 : Mem.Wf s8.memory := by
    rw [hm8]
    exact hwf7.write _ _
  have hr8 : Mem.Reads s8.memory img3 := by
    rw [hm8]
    exact Mem.Reads.write hwf7 hr7 0 _

  rcases of_run_append (arg 0) hlogApprove with
    ⟨s9, hargSpender, hlogApprove⟩
  have hp9 : Sevm.argWord sevm 0 :: xs <<+ s9.stack :=
    prefix_of_arg hp8 hargSpender
  rcases Line.of_run_cons hlogApprove with
    ⟨s10, hcallerTopic, hlogApprove⟩
  have hp10 : sevm.caller.toB256 :: Sevm.argWord sevm 0 :: xs <<+
      s10.stack :=
    prefix_of_push (of_run_caller hcallerTopic) hp9
  rcases Line.of_run_cons hlogApprove with
    ⟨s11, hevent, hlogWith⟩
  have hp11 : approvalEvent :: sevm.caller.toB256 ::
      Sevm.argWord sevm 0 :: xs <<+ s11.stack :=
    prefix_of_push (of_run_pushB256 hevent) hp10
  have hmem8to11 : s8.memory = s11.memory := by
    calc
      s8.memory = s9.memory :=
        Line.of_inv Devm.memory (by line_inv) hargSpender
      _ = s10.memory := Ninst.Hinv.inv (f := Devm.memory) hcallerTopic
      _ = s11.memory := Ninst.Hinv.inv (f := Devm.memory) hevent
  have hread : (s11.memory.read 0 32).1 = valueBytes := by
    rw [Mem.Reads.read (hmem8to11 ▸ hr8) 0 32,
      show 32 = valueBytes.length by
        unfold valueBytes List.sliceD
        rw [List.takeD_length],
      Bytes.sliceD_writeAt]
  rcases of_logWith201_val hp11 hlogWith with ⟨hp12, hlogs⟩
  have hlogMem := of_logWith201_mem hp11 hlogWith
  have hwft : Mem.Wf t.memory := by
    rw [hlogMem, ← hmem8to11]
    exact hwf8.extend _ _
  have hrt : Mem.Reads t.memory img3 := by
    rw [hlogMem, ← hmem8to11]
    exact Mem.Reads.extend hr8 _ _
  rw [hread] at hlogs
  have hlogsBefore : s.logs = s11.logs := by
    calc
      s.logs = s1.logs := (of_run_caller hcaller).logs
      _ = s2.logs := Line.of_inv Devm.logs (by line_inv) hmstore0
      _ = s3.logs := Line.of_inv Devm.logs (by
        unfold argCopy cdc
        line_inv) hcopySpender
      _ = s4.logs := Line.of_inv Devm.logs (by
        unfold allowanceKeyFromMemory pushList
        line_inv) hkey
      _ = s5.logs := Line.of_inv Devm.logs (by line_inv) hargValue
      _ = s6.logs := Ninst.Hinv.inv (f := Devm.logs) hswap
      _ = s7.logs := Ninst.Hinv.inv (f := Devm.logs) hstore
      _ = s8.logs := Line.of_inv Devm.logs (by
        unfold argCopy cdc
        line_inv) hcopyValue
      _ = s9.logs := Line.of_inv Devm.logs (by line_inv) hargSpender
      _ = s10.logs := (of_run_caller hcallerTopic).logs
      _ = s11.logs := Ninst.Hinv.inv (f := Devm.logs) hevent
  rcases of_returnTrue_shared hp12 hwft hrt hreturn with
    ⟨htrue, hcodeReturn⟩
  refine ⟨?_, ?_, htrue, ?_, ?_⟩
  · rw [← congrFun hstorReturn sevm.currentTarget,
      ← congrFun hstorLog sevm.currentTarget,
      hset, ← congrFun hstorBefore sevm.currentTarget]
  · calc
      r.logs = t.logs := hlogsReturn.symm
      _ = s11.logs ++ [approveApprovalLog sevm] := by
        simpa only [approveApprovalLog, valueBytes] using hlogs
      _ = s.logs ++ [approveApprovalLog sevm] := by
        rw [hlogsBefore]
  · exact hbalReturn.symm.trans hbalPrefix.symm
  · exact hcodeReturn.symm.trans hcodePrefix.symm

/-- Compiled public `approve`: recognized nonpayable entry, exact allowance
write and event, canonical `true`, and no ETH-balance or code effect. -/
theorem approve_exec_effect (dp : DeployParams)
    {sevm : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = selector "approve" [.address, .uint256])
    (h_nonempty : sevm.data.length.toB256 ≠ 0) :
    sevm.value = 0 ∧
      Devm.getStor post sevm.currentTarget =
        (Devm.getStor pre sevm.currentTarget).set
          (approveRuntimeKey sevm) (Sevm.argWord sevm 1) ∧
      post.logs = pre.logs ++ [approveApprovalLog sevm] ∧
      AbiReturnsTrue post ∧
      Devm.getBal post = Devm.getBal pre ∧
      Devm.getCode post = Devm.getCode pre := by
  have h_mem :
      (selector "approve" [.address, .uint256], nonpayable approve) ∈
        weth10Funcs dp := by
    simp [weth10Funcs]
  rcases exec_enters_weth10Nonpayable_logs
      exc h_code h_sel h_nonempty h_mem with
    ⟨mid, hvalue, hstor0, hbal0, hcode0, hmemory, hlogs0, _, hbody⟩
  have hwfMid : Mem.Wf mid.memory := by
    rw [hmemory]
    exact h_wf
  have hreadsMid : Mem.Reads mid.memory img := by
    rw [hmemory]
    exact h_reads
  rcases approve_effect nil_pref hwfMid hreadsMid hbody with
    ⟨hstor, hlogs, htrue, hbal, hcode⟩
  refine ⟨hvalue, ?_, ?_, htrue, ?_, ?_⟩
  · rw [hstor, congrFun hstor0 sevm.currentTarget]
  · rw [hlogs, hlogs0]
  · exact hbal.trans hbal0
  · exact hcode.trans hcode0

/-! ## Payable mint paths -/

/-- The exact low-160-bit word used by WETH10 whenever an ABI address argument
becomes a balance key or indexed event topic. -/
def normalizedAddressArg (e : Sevm) (k : B256) : B256 :=
  (~~~ addressMask) &&& Sevm.argWord e k

private lemma prefix_of_addressArg_effect {e : Sevm} {k : B256} {xs : Stack}
    {s s' : Devm} (hp : xs <<+ s.stack)
    (run : Line.Run e s (addressArg k) s') :
    normalizedAddressArg e k :: xs <<+ s'.stack := by
  unfold addressArg normalizeAddress at run
  unfold normalizedAddressArg
  rcases of_run_append (arg k) run with ⟨s1, harg, run1⟩
  have hp1 : Sevm.argWord e k :: xs <<+ s1.stack :=
    prefix_of_arg hp harg
  rcases of_run_append pushAddressMask run1 with ⟨s2, hmask, run2⟩
  have hp2 : addressMask :: Sevm.argWord e k :: xs <<+ s2.stack :=
    of_push_addressMask hp1 hmask
  rcases Line.of_run_cons run2 with ⟨s3, hnot, run3⟩
  have hp3 : (~~~ addressMask) :: Sevm.argWord e k :: xs <<+ s3.stack :=
    prefix_of_not hnot hp2
  rcases Line.of_run_cons run3 with ⟨s4, hand, hnil⟩
  cases hnil
  exact prefix_of_and hand hp3

/-- The exact ERC-20 `Transfer(0, caller, value)` entry emitted by `deposit`
and by the empty-calldata receive path. -/
def mintCallerTransferLog (e : Sevm) : Log :=
  ⟨e.currentTarget, [transferEvent, 0, e.caller.toB256], e.value.toBytes⟩

/-- The exact `Transfer(0, recipient, value)` entry emitted by `mintToPrefix`.
The recipient is the same normalized low-160-bit word used as the balance key. -/
def mintToTransferLog (e : Sevm) : Log :=
  ⟨e.currentTarget, [transferEvent, 0, normalizedAddressArg e 0],
    e.value.toBytes⟩

private lemma sload_logs {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s sload s') : s.logs = s'.logs := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨key, s1⟩, h1, run1⟩
  refine (Devm.pop_of_pop h1).logs.trans ?_
  suffices H : ∀ (d : Devm) (c : Nat), s1.logs = d.logs →
      (chargeGas c d >>=
        fun y => Devm.push (Devm.getStorVal y e.currentTarget key) y) =
          .ok s' →
      s1.logs = s'.logs by
    split at run1
    · exact H s1 gasWarmAccess rfl run1
    · exact H (addAccessedStorageKey s1 e.currentTarget key)
        gasColdSload rfl run1
  intro d c hlogs run'
  rcases Except.bind_eq_ok run' with ⟨s2, h2, run2⟩
  exact (hlogs.trans (Devm.burn_of_chargeGas h2).logs).trans
    (Devm.push_of_push run2).logs

private lemma sload_output {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s sload s') : s.output = s'.output := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨key, s1⟩, h1, run1⟩
  refine (Devm.pop_of_pop h1).output.trans ?_
  suffices H : ∀ (d : Devm) (c : Nat), s1.output = d.output →
      (chargeGas c d >>=
        fun y => Devm.push (Devm.getStorVal y e.currentTarget key) y) =
          .ok s' →
      s1.output = s'.output by
    split at run1
    · exact H s1 gasWarmAccess rfl run1
    · exact H (addAccessedStorageKey s1 e.currentTarget key)
        gasColdSload rfl run1
  intro d c houtput run'
  rcases Except.bind_eq_ok run' with ⟨s2, h2, run2⟩
  exact (houtput.trans (Devm.burn_of_chargeGas h2).output).trans
    (Devm.push_of_push run2).output

private lemma add_logs {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s add s') : s.logs = s'.logs := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.logs

private lemma add_output {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s add s') : s.output = s'.output := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.output

/-- Exact selected-body effect of the shared `depositTo` mint prefix: one
normalized balance-key update, one mint log, and no balance, code, or outer
return-data mutation. -/
theorem mintToPrefix_effect
    {sevm : Sevm} {s r : Devm} {img : Bytes}
    (hwf : Mem.Wf s.memory)
    (hr : Mem.Reads s.memory img)
    (run : Line.Run sevm s mintToPrefix r) :
    Devm.getStor r sevm.currentTarget =
        (Devm.getStor s sevm.currentTarget).set
          (normalizedAddressArg sevm 0)
          (sevm.value +
            (Devm.getStor s sevm.currentTarget).get
              (normalizedAddressArg sevm 0)) ∧
      r.logs = s.logs ++ [mintToTransferLog sevm] ∧
      Devm.getBal r = Devm.getBal s ∧
      Devm.getCode r = Devm.getCode s ∧
      r.output = s.output := by
  unfold mintToPrefix at run
  rcases of_run_append (addressArg 0) run with ⟨s1, harg1, run1⟩
  let key := normalizedAddressArg sevm 0
  have hp1 : key :: [] <<+ s1.stack :=
    prefix_of_addressArg_effect nil_pref harg1
  rcases Line.of_run_cons run1 with ⟨s2, hload, run2⟩
  rcases prefix_of_sload hload hp1 with ⟨toBal, hp2, htoBal⟩
  rcases Line.of_run_cons run2 with ⟨s3, hvalue1, run3⟩
  have hp3 : sevm.value :: toBal :: [] <<+ s3.stack :=
    prefix_of_push (of_run_callvalue hvalue1) hp2
  rcases Line.of_run_cons run3 with ⟨s4, hadd, run4⟩
  have hp4 : (sevm.value + toBal) :: [] <<+ s4.stack :=
    prefix_of_add hadd hp3
  rcases of_run_append (addressArg 0) run4 with ⟨s5, harg2, run5⟩
  have hp5 : key :: (sevm.value + toBal) :: [] <<+ s5.stack :=
    prefix_of_addressArg_effect hp4 harg2
  rcases Line.of_run_cons run5 with ⟨s6, hstore, run6⟩
  have hset :
      Devm.getStor s6 sevm.currentTarget =
        (Devm.getStor s5 sevm.currentTarget).set key
          (sevm.value + toBal) :=
    sstore_getStor_set hstore hp5
  rcases Line.of_run_cons run6 with ⟨s7, hvalue2, run7⟩
  have hp7 : sevm.value :: [] <<+ s7.stack :=
    prefix_of_push (of_run_callvalue hvalue2) nil_pref
  rcases of_run_append (mstoreAt 0) run7 with ⟨s8, hmstore, run8⟩
  rcases of_run_mstoreAt_val hmstore hp7 with ⟨hp8, hm8⟩
  rcases of_run_append (addressArg 0) run8 with ⟨s9, harg3, run9⟩
  have hp9 : key :: [] <<+ s9.stack :=
    prefix_of_addressArg_effect hp8 harg3
  rcases Line.of_run_cons run9 with ⟨s10, hzero, run10⟩
  have hp10 : (0 : B256) :: key :: [] <<+ s10.stack :=
    prefix_of_push (of_run_pushB256 hzero) hp9
  rcases Line.of_run_cons run10 with ⟨s11, hevent, hlog⟩
  have hp11 : transferEvent :: (0 : B256) :: key :: [] <<+ s11.stack :=
    prefix_of_push (of_run_pushB256 hevent) hp10

  have hs1 : Devm.getStor s = Devm.getStor s1 :=
    Line.of_inv Devm.getStor (by
      unfold addressArg normalizeAddress pushAddressMask
      line_inv) harg1
  have hs2 : Devm.getStor s1 = Devm.getStor s2 :=
    Ninst.Hinv.inv (f := Devm.getStor) hload
  have hs3 : Devm.getStor s2 = Devm.getStor s3 :=
    Ninst.Hinv.inv (f := Devm.getStor) hvalue1
  have hs4 : Devm.getStor s3 = Devm.getStor s4 :=
    Ninst.Hinv.inv (f := Devm.getStor) hadd
  have hs5 : Devm.getStor s4 = Devm.getStor s5 :=
    Line.of_inv Devm.getStor (by
      unfold addressArg normalizeAddress pushAddressMask
      line_inv) harg2
  have hsBefore : Devm.getStor s = Devm.getStor s5 := by
    rw [hs1, hs2, hs3, hs4, hs5]
  have hsAfter : Devm.getStor s6 = Devm.getStor r :=
    Line.of_inv Devm.getStor (by
      unfold mstoreAt addressArg normalizeAddress pushAddressMask logWith
      line_inv) run6
  have htoBal' :
      toBal = (Devm.getStor s5 sevm.currentTarget).get key := by
    rw [htoBal]
    show (Devm.getStor s1 sevm.currentTarget).get key = _
    rw [hs2, hs3, hs4, hs5]

  have hmemTo7 : s.memory = s7.memory := by
    calc
      s.memory = s1.memory := Line.of_inv Devm.memory (by
        unfold addressArg normalizeAddress pushAddressMask
        line_inv) harg1
      _ = s2.memory := Ninst.Hinv.inv (f := Devm.memory) hload
      _ = s3.memory := Ninst.Hinv.inv (f := Devm.memory) hvalue1
      _ = s4.memory := Ninst.Hinv.inv (f := Devm.memory) hadd
      _ = s5.memory := Line.of_inv Devm.memory (by
        unfold addressArg normalizeAddress pushAddressMask
        line_inv) harg2
      _ = s6.memory := Ninst.Hinv.inv (f := Devm.memory) hstore
      _ = s7.memory := Ninst.Hinv.inv (f := Devm.memory) hvalue2
  let img1 := Bytes.writeAt img 0 sevm.value.toBytes
  have hwf8 : Mem.Wf s8.memory := by
    rw [hm8, ← hmemTo7]
    exact hwf.write _ _
  have hr8 : Mem.Reads s8.memory img1 := by
    rw [hm8, ← hmemTo7]
    exact Mem.Reads.write hwf hr 0 _
  have hmem8to11 : s8.memory = s11.memory := by
    calc
      s8.memory = s9.memory := Line.of_inv Devm.memory (by
        unfold addressArg normalizeAddress pushAddressMask
        line_inv) harg3
      _ = s10.memory := Ninst.Hinv.inv (f := Devm.memory) hzero
      _ = s11.memory := Ninst.Hinv.inv (f := Devm.memory) hevent
  have hread : (s11.memory.read 0 32).1 = sevm.value.toBytes := by
    rw [Mem.Reads.read (hmem8to11 ▸ hr8) 0 32,
      show 32 = sevm.value.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt]
  rcases of_logWith201_val hp11 hlog with ⟨_, hlogs⟩
  have hlogsBefore : s.logs = s11.logs := by
    calc
      s.logs = s1.logs := Line.of_inv Devm.logs (by
        unfold addressArg normalizeAddress pushAddressMask
        line_inv) harg1
      _ = s2.logs := sload_logs hload
      _ = s3.logs := (of_run_callvalue hvalue1).logs
      _ = s4.logs := add_logs hadd
      _ = s5.logs := Line.of_inv Devm.logs (by
        unfold addressArg normalizeAddress pushAddressMask
        line_inv) harg2
      _ = s6.logs := Ninst.Hinv.inv (f := Devm.logs) hstore
      _ = s7.logs := (of_run_callvalue hvalue2).logs
      _ = s8.logs := Line.of_inv Devm.logs (by
        unfold mstoreAt
        line_inv) hmstore
      _ = s9.logs := Line.of_inv Devm.logs (by
        unfold addressArg normalizeAddress pushAddressMask
        line_inv) harg3
      _ = s10.logs := (of_run_pushB256 hzero).logs
      _ = s11.logs := (of_run_pushB256 hevent).logs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← congrFun hsAfter sevm.currentTarget, hset,
      ← congrFun hsBefore sevm.currentTarget, htoBal']
    simp only [key]
    rw [← congrFun hsBefore sevm.currentTarget]
  · rw [hread] at hlogs
    simpa only [mintToTransferLog, key] using hlogs.trans (by
      rw [← hlogsBefore])
  · symm
    exact Line.of_inv Devm.getBal (by
      unfold addressArg normalizeAddress pushAddressMask mstoreAt logWith
      line_inv) run
  · symm
    exact Line.of_inv Devm.getCode (by
      unfold addressArg normalizeAddress pushAddressMask mstoreAt logWith
      line_inv) run
  · symm
    calc
      s.output = s1.output := Line.of_inv Devm.output (by
        unfold addressArg normalizeAddress pushAddressMask
        line_inv) harg1
      _ = s2.output := sload_output hload
      _ = s3.output := (of_run_callvalue hvalue1).output
      _ = s4.output := add_output hadd
      _ = s5.output := Line.of_inv Devm.output (by
        unfold addressArg normalizeAddress pushAddressMask
        line_inv) harg2
      _ = s6.output := Ninst.Hinv.inv (f := Devm.output) hstore
      _ = s7.output := (of_run_callvalue hvalue2).output
      _ = s8.output := Line.of_inv Devm.output (by
        unfold mstoreAt
        line_inv) hmstore
      _ = s9.output := Line.of_inv Devm.output (by
        unfold addressArg normalizeAddress pushAddressMask
        line_inv) harg3
      _ = s10.output := (of_run_pushB256 hzero).output
      _ = s11.output := (of_run_pushB256 hevent).output
      _ = r.output := Line.of_inv Devm.output (by
        unfold logWith
        line_inv) hlog

/-- Successful selected `depositTo`: exact normalized balance update, event,
and frame-local return behavior. -/
theorem depositTo_effect
    {fs : List Func} {sevm : Sevm} {s r : Devm} {img : Bytes}
    (hwf : Mem.Wf s.memory)
    (hr : Mem.Reads s.memory img)
    (run : Func.Run fs sevm s depositTo r) :
    Devm.getStor r sevm.currentTarget =
        (Devm.getStor s sevm.currentTarget).set
          (normalizedAddressArg sevm 0)
          (sevm.value +
            (Devm.getStor s sevm.currentTarget).get
              (normalizedAddressArg sevm 0)) ∧
      r.logs = s.logs ++ [mintToTransferLog sevm] ∧
      Devm.getBal r = Devm.getBal s ∧
      Devm.getCode r = Devm.getCode s ∧
      r.output = s.output := by
  simp only [depositTo] at run
  rcases of_run_prepend mintToPrefix Func.stop run with
    ⟨mid, hprefix, hstop⟩
  have hr_eq : r = mid := by
    cases hstop with
    | last h =>
      simp only [Linst.Run, Linst.run] at h
      exact (Except.ok.inj h).symm
  subst r
  exact mintToPrefix_effect hwf hr hprefix

/-- Compiled public `depositTo(address)`: the payable entry preserves the
exact normalized-key credit, mint event, balance/code, and outer output. -/
theorem depositTo_exec_effect (dp : DeployParams)
    {sevm : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = selector "depositTo" [.address])
    (h_nonempty : sevm.data.length.toB256 ≠ 0) :
    Devm.getStor post sevm.currentTarget =
        (Devm.getStor pre sevm.currentTarget).set
          (normalizedAddressArg sevm 0)
          (sevm.value +
            (Devm.getStor pre sevm.currentTarget).get
              (normalizedAddressArg sevm 0)) ∧
      post.logs = pre.logs ++ [mintToTransferLog sevm] ∧
      Devm.getBal post = Devm.getBal pre ∧
      Devm.getCode post = Devm.getCode pre ∧
      post.output = pre.output := by
  have h_mem : (selector "depositTo" [.address], depositTo) ∈ weth10Funcs dp := by
    simp [weth10Funcs]
  rcases exec_enters_weth10Selector_logs
      exc h_code h_sel h_nonempty h_mem with
    ⟨mid, hstor0, hbal0, hcode0, hmemory, hlogs0, houtput0, hbody⟩
  have hwfMid : Mem.Wf mid.memory := by
    rw [hmemory]
    exact h_wf
  have hreadsMid : Mem.Reads mid.memory img := by
    rw [hmemory]
    exact h_reads
  rcases depositTo_effect hwfMid hreadsMid hbody with
    ⟨hstor, hlogs, hbal, hcode, houtput⟩
  refine ⟨?_, ?_, hbal.trans hbal0, hcode.trans hcode0,
    houtput.trans houtput0⟩
  · rw [hstor, ← congrFun hstor0 sevm.currentTarget]
  · rw [hlogs, hlogs0]

/-- A successful `mintCaller` body credits exactly the caller by the frame
value, leaves the disjoint flash counter unchanged, and appends exactly the
canonical mint `Transfer` log.  `receiveEther` and `deposit` are both
definitionally this body; public entry corollaries specialize it below. -/
theorem mintCaller_effect
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    {img : Bytes}
    (hwf : Mem.Wf s.memory)
    (hr : Mem.Reads s.memory img)
    (run : Func.Run fs sevm s mintCaller r) :
    Increase sevm.caller sevm.value
        (Stor.rest (Devm.getStor s sevm.currentTarget))
        (Stor.rest (Devm.getStor r sevm.currentTarget)) ∧
      (Devm.getStor r sevm.currentTarget).get flashMintedSlot =
        (Devm.getStor s sevm.currentTarget).get flashMintedSlot ∧
      r.logs = s.logs ++ [mintCallerTransferLog sevm] ∧
      Devm.getBal r = Devm.getBal s ∧
      Devm.getCode r = Devm.getCode s ∧
      r.output = s.output := by
  have hstorage := mintCaller_storage run
  unfold mintCaller at run
  rcases of_run_next run with ⟨s1, hcaller1, run1⟩
  rcases of_run_next run1 with ⟨s2, hload, run2⟩
  rcases of_run_next run2 with ⟨s3, hvalue1, run3⟩
  rcases of_run_next run3 with ⟨s4, hadd, run4⟩
  rcases of_run_next run4 with ⟨s5, hcaller2, run5⟩
  rcases of_run_next run5 with ⟨s6, hstore, run6⟩
  rcases of_run_next run6 with ⟨s7, hvalue2, run7⟩
  rcases of_run_prepend (mstoreAt 0) _ run7 with
    ⟨s8, hmstore, run8⟩
  rcases of_run_next run8 with ⟨s9, hcaller3, run9⟩
  rcases of_run_next run9 with ⟨s10, hzero, run10⟩
  rcases of_run_next run10 with ⟨s11, hevent, run11⟩
  rcases of_run_prepend (logWith 2 0 1) _ run11 with
    ⟨s12, hlog, hstop⟩
  have hp7 : sevm.value :: [] <<+ s7.stack :=
    prefix_of_push (of_run_callvalue hvalue2) nil_pref
  rcases of_run_mstoreAt_val hmstore hp7 with ⟨hp8, hm8⟩
  have hp9 : sevm.caller.toB256 :: [] <<+ s9.stack :=
    prefix_of_push (of_run_caller hcaller3) hp8
  have hp10 : (0 : B256) :: sevm.caller.toB256 :: [] <<+ s10.stack :=
    prefix_of_push (of_run_pushB256 hzero) hp9
  have hp11 : transferEvent :: (0 : B256) :: sevm.caller.toB256 :: [] <<+
      s11.stack :=
    prefix_of_push (of_run_pushB256 hevent) hp10
  rcases of_logWith201_val hp11 hlog with ⟨_, hlogs⟩
  have hmemTo7 : s.memory = s7.memory := by
    calc
      s.memory = s1.memory := (of_run_caller hcaller1).memory
      _ = s2.memory := Ninst.Hinv.inv (f := Devm.memory) hload
      _ = s3.memory := (of_run_callvalue hvalue1).memory
      _ = s4.memory := Ninst.Hinv.inv (f := Devm.memory) hadd
      _ = s5.memory := (of_run_caller hcaller2).memory
      _ = s6.memory := Ninst.Hinv.inv (f := Devm.memory) hstore
      _ = s7.memory := (of_run_callvalue hvalue2).memory
  let img1 := Bytes.writeAt img 0 sevm.value.toBytes
  have hwf8 : Mem.Wf s8.memory := by
    rw [hm8, ← hmemTo7]
    exact hwf.write _ _
  have hr8 : Mem.Reads s8.memory img1 := by
    rw [hm8, ← hmemTo7]
    exact Mem.Reads.write hwf hr 0 _
  have hmem8to11 : s8.memory = s11.memory := by
    calc
      s8.memory = s9.memory := (of_run_caller hcaller3).memory
      _ = s10.memory := (of_run_pushB256 hzero).memory
      _ = s11.memory := (of_run_pushB256 hevent).memory
  have hread : (s11.memory.read 0 32).1 = sevm.value.toBytes := by
    rw [Mem.Reads.read (hmem8to11 ▸ hr8) 0 32,
      show 32 = sevm.value.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt]
  rw [hread] at hlogs
  have hlogsBefore : s.logs = s11.logs := by
    calc
      s.logs = s1.logs := (of_run_caller hcaller1).logs
      _ = s2.logs := sload_logs hload
      _ = s3.logs := (of_run_callvalue hvalue1).logs
      _ = s4.logs := add_logs hadd
      _ = s5.logs := (of_run_caller hcaller2).logs
      _ = s6.logs := Ninst.Hinv.inv (f := Devm.logs) hstore
      _ = s7.logs := (of_run_callvalue hvalue2).logs
      _ = s8.logs := Line.of_inv Devm.logs (by
        unfold mstoreAt
        line_inv) hmstore
      _ = s9.logs := (of_run_caller hcaller3).logs
      _ = s10.logs := (of_run_pushB256 hzero).logs
      _ = s11.logs := (of_run_pushB256 hevent).logs
  have hstopEq : r = s12 := by
    cases hstop with
    | last h =>
        simp only [Linst.Run, Linst.run] at h
        exact (Except.ok.inj h).symm
  refine ⟨hstorage.1, hstorage.2, ?_, ?_, ?_, ?_⟩
  · rw [hstopEq, hlogs, ← hlogsBefore]
    rfl
  · rw [hstopEq]
    symm
    calc
      Devm.getBal s = Devm.getBal s1 :=
        Ninst.Hinv.inv (f := Devm.getBal) hcaller1
      _ = Devm.getBal s2 := Ninst.Hinv.inv (f := Devm.getBal) hload
      _ = Devm.getBal s3 := Ninst.Hinv.inv (f := Devm.getBal) hvalue1
      _ = Devm.getBal s4 := Ninst.Hinv.inv (f := Devm.getBal) hadd
      _ = Devm.getBal s5 := Ninst.Hinv.inv (f := Devm.getBal) hcaller2
      _ = Devm.getBal s6 := Ninst.Hinv.inv (f := Devm.getBal) hstore
      _ = Devm.getBal s7 := Ninst.Hinv.inv (f := Devm.getBal) hvalue2
      _ = Devm.getBal s8 := Line.of_inv Devm.getBal (by
        unfold mstoreAt
        line_inv) hmstore
      _ = Devm.getBal s9 := Ninst.Hinv.inv (f := Devm.getBal) hcaller3
      _ = Devm.getBal s10 := Ninst.Hinv.inv (f := Devm.getBal) hzero
      _ = Devm.getBal s11 := Ninst.Hinv.inv (f := Devm.getBal) hevent
      _ = Devm.getBal s12 := Line.of_inv Devm.getBal (by
        unfold logWith
        line_inv) hlog
  · rw [hstopEq]
    symm
    calc
      Devm.getCode s = Devm.getCode s1 :=
        Ninst.Hinv.inv (f := Devm.getCode) hcaller1
      _ = Devm.getCode s2 := Ninst.Hinv.inv (f := Devm.getCode) hload
      _ = Devm.getCode s3 := Ninst.Hinv.inv (f := Devm.getCode) hvalue1
      _ = Devm.getCode s4 := Ninst.Hinv.inv (f := Devm.getCode) hadd
      _ = Devm.getCode s5 := Ninst.Hinv.inv (f := Devm.getCode) hcaller2
      _ = Devm.getCode s6 := Ninst.Hinv.inv (f := Devm.getCode) hstore
      _ = Devm.getCode s7 := Ninst.Hinv.inv (f := Devm.getCode) hvalue2
      _ = Devm.getCode s8 := Line.of_inv Devm.getCode (by
        unfold mstoreAt
        line_inv) hmstore
      _ = Devm.getCode s9 := Ninst.Hinv.inv (f := Devm.getCode) hcaller3
      _ = Devm.getCode s10 := Ninst.Hinv.inv (f := Devm.getCode) hzero
      _ = Devm.getCode s11 := Ninst.Hinv.inv (f := Devm.getCode) hevent
      _ = Devm.getCode s12 := Line.of_inv Devm.getCode (by
        unfold logWith
        line_inv) hlog
  · rw [hstopEq]
    symm
    calc
      s.output = s1.output := (of_run_caller hcaller1).output
      _ = s2.output := sload_output hload
      _ = s3.output := (of_run_callvalue hvalue1).output
      _ = s4.output := add_output hadd
      _ = s5.output := (of_run_caller hcaller2).output
      _ = s6.output := Ninst.Hinv.inv (f := Devm.output) hstore
      _ = s7.output := (of_run_callvalue hvalue2).output
      _ = s8.output := Line.of_inv Devm.output (by
        unfold mstoreAt
        line_inv) hmstore
      _ = s9.output := (of_run_caller hcaller3).output
      _ = s10.output := (of_run_pushB256 hzero).output
      _ = s11.output := (of_run_pushB256 hevent).output
      _ = s12.output := Line.of_inv Devm.output (by
        unfold logWith
        line_inv) hlog

/-- Compiled public `deposit()`: exact caller credit, unchanged flash counter,
one canonical mint `Transfer` log, and no ETH-balance or code mutation inside
the WETH10 frame. -/
theorem deposit_exec_effect (dp : DeployParams)
    {sevm : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = selector "deposit" [])
    (h_nonempty : sevm.data.length.toB256 ≠ 0) :
    Increase sevm.caller sevm.value
        (Stor.rest (Devm.getStor pre sevm.currentTarget))
        (Stor.rest (Devm.getStor post sevm.currentTarget)) ∧
      (Devm.getStor post sevm.currentTarget).get flashMintedSlot =
        (Devm.getStor pre sevm.currentTarget).get flashMintedSlot ∧
      post.logs = pre.logs ++ [mintCallerTransferLog sevm] ∧
      Devm.getBal post = Devm.getBal pre ∧
      Devm.getCode post = Devm.getCode pre ∧
      post.output = pre.output := by
  have h_mem : (selector "deposit" [], deposit) ∈ weth10Funcs dp := by
    simp [weth10Funcs]
  rcases exec_enters_weth10Selector_logs
      exc h_code h_sel h_nonempty h_mem with
    ⟨mid, hstor0, hbal0, hcode0, hmemory, hlogs0, houtput0, hbody⟩
  have hwfMid : Mem.Wf mid.memory := by
    rw [hmemory]
    exact h_wf
  have hreadsMid : Mem.Reads mid.memory img := by
    rw [hmemory]
    exact h_reads
  have hmint : Func.Run ((weth10 dp).main :: weth10Aux)
      sevm mid mintCaller post := by
    simpa only [deposit] using hbody
  rcases mintCaller_effect hwfMid hreadsMid hmint with
    ⟨hinc, hflash, hlogs, hbal, hcode, houtput⟩
  have hstorAt := congrFun hstor0 sevm.currentTarget
  rw [hstorAt] at hinc hflash
  refine ⟨hinc, hflash, ?_, hbal.trans hbal0, hcode.trans hcode0,
    houtput.trans houtput0⟩
  rw [hlogs, hlogs0]

/-- Compiled payable receive: empty calldata credits exactly the caller,
preserves the flash counter, and emits the same canonical mint `Transfer`
entry as `deposit()`. -/
theorem receive_exec_effect (dp : DeployParams)
    {sevm : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_empty : sevm.data.length.toB256 = 0) :
    Increase sevm.caller sevm.value
        (Stor.rest (Devm.getStor pre sevm.currentTarget))
        (Stor.rest (Devm.getStor post sevm.currentTarget)) ∧
      (Devm.getStor post sevm.currentTarget).get flashMintedSlot =
        (Devm.getStor pre sevm.currentTarget).get flashMintedSlot ∧
      post.logs = pre.logs ++ [mintCallerTransferLog sevm] ∧
      Devm.getBal post = Devm.getBal pre ∧
      Devm.getCode post = Devm.getCode pre ∧
      post.output = pre.output := by
  rcases exec_enters_weth10Receive_logs exc h_code h_empty with
    ⟨mid, hstor0, hbal0, hcode0, hmemory, hlogs0, houtput0, hbody⟩
  have hwfMid : Mem.Wf mid.memory := by
    rw [hmemory]
    exact h_wf
  have hreadsMid : Mem.Reads mid.memory img := by
    rw [hmemory]
    exact h_reads
  have hmint : Func.Run ((weth10 dp).main :: weth10Aux)
      sevm mid mintCaller post := by
    simpa only [receiveEther] using hbody
  rcases mintCaller_effect hwfMid hreadsMid hmint with
    ⟨hinc, hflash, hlogs, hbal, hcode, houtput⟩
  have hstorAt := congrFun hstor0 sevm.currentTarget
  rw [hstorAt] at hinc hflash
  refine ⟨hinc, hflash, ?_, hbal.trans hbal0, hcode.trans hcode0,
    houtput.trans houtput0⟩
  rw [hlogs, hlogs0]

end Weth10

end Blanc
