-- Exact public effects for WETH10 transfers and withdrawals.

import Blanc.Weth10StateFunctional
import Blanc.Weth10StateSound
import Blanc.Weth10Errors

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Weth10

/-! ## Shared observable vocabulary -/

/-- Canonical ERC-20 `Transfer` entry emitted by WETH10's ordinary movement
and burn paths.  Address words are stated exactly as the runtime puts them on
the topic stack. -/
def ordinaryTransferLog (e : Sevm) (src dst amount : B256) : Log :=
  ⟨e.currentTarget, [transferEvent, src, dst], amount.toBytes⟩

/-- Canonical finite-spend `Approval` entry.  The owner topic intentionally
retains the raw ABI word used by the deployed allowance-key path. -/
def allowanceSpendLog (e : Sevm) (reduced : B256) : Log :=
  ⟨e.currentTarget,
    [approvalEvent, Sevm.argWord e 0, e.caller.toB256],
    reduced.toBytes⟩

def ordinaryApprovalLog (e : Sevm) (owner spender value : B256) : Log :=
  ⟨e.currentTarget, [approvalEvent, owner, spender], value.toBytes⟩

/-- Exact tagged key for `allowance[raw owner word][caller]`.  This path
intentionally uses the raw owner word, matching deployed compatibility. -/
def callerAllowanceRuntimeKey (e : Sevm) : B256 :=
  allowanceTagWord |||
    (allowancePayloadMask &&& Bytes.keccak
      ((Sevm.argWord e 0).toBytes ++ e.caller.toB256.toBytes))

/-- Exact self/max/finite allowance fork before delegated movement reaches its
core.  Self and max paths are silent; the finite path subtracts exactly once
at the tagged runtime key and appends exactly one `Approval`. -/
def CallerAllowanceOutcome (e : Sevm) (pre corePre : Devm)
    (amountArg : B256) : Prop :=
  ((Sevm.argWord e 0 = e.caller.toB256 ∧
      Devm.getStor corePre e.currentTarget =
        Devm.getStor pre e.currentTarget ∧
      corePre.logs = pre.logs) ∨
    (Sevm.argWord e 0 ≠ e.caller.toB256 ∧
      (((Devm.getStor pre e.currentTarget).get
            (callerAllowanceRuntimeKey e) = B256.max ∧
          Devm.getStor corePre e.currentTarget =
            Devm.getStor pre e.currentTarget ∧
          corePre.logs = pre.logs) ∨
        (∃ allowance : B256,
          allowance ≠ B256.max ∧
          Sevm.argWord e amountArg ≤ allowance ∧
          (Devm.getStor pre e.currentTarget).get
              (callerAllowanceRuntimeKey e) = allowance ∧
          Devm.getStor corePre e.currentTarget =
            (Devm.getStor pre e.currentTarget).set
              (callerAllowanceRuntimeKey e)
              (allowance - Sevm.argWord e amountArg) ∧
          corePre.logs = pre.logs ++
            [allowanceSpendLog e
              (allowance - Sevm.argWord e amountArg)])))) ∧
  corePre.output = pre.output ∧
  Devm.getBal corePre = Devm.getBal pre ∧
  Devm.getCode corePre = Devm.getCode pre

theorem of_callerAllowanceKeyPrefix
    {e : Sevm} {s r : Devm} {img : Bytes}
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Line.Run e s
      (arg 0 ++ mstoreAt 0 ++ [caller] ++ mstoreAt 1 ++
        allowanceKeyFromMemory) r) :
    callerAllowanceRuntimeKey e :: [] <<+ r.stack ∧
      Mem.Wf r.memory ∧ ∃ out, Mem.Reads r.memory out := by
  rcases of_run_append (arg 0) run with ⟨s1, howner, run1⟩
  have hp1 : Sevm.argWord e 0 :: [] <<+ s1.stack :=
    prefix_of_arg nil_pref howner
  rcases of_run_append (mstoreAt 0) run1 with
    ⟨s2, hstoreOwner, run2⟩
  rcases of_run_mstoreAt_val hstoreOwner hp1 with ⟨hp2, hm2⟩
  have hm2' : s2.memory =
      s1.memory.write 0 (Sevm.argWord e 0).toBytes := by
    simpa only [show (0 * 32 : B256).toNat = 0 by decide +kernel]
      using hm2
  have hmOwner : s.memory = s1.memory :=
    Line.of_inv Devm.memory (by unfold arg cdl; line_inv) howner
  rcases Line.of_run_cons run2 with ⟨s3, hcaller, run3⟩
  have hb3 := of_run_caller hcaller
  have hp3 : e.caller.toB256 :: [] <<+ s3.stack :=
    prefix_of_push hb3 hp2
  rcases of_run_append (mstoreAt 1) run3 with
    ⟨s4, hstoreCaller, hkey⟩
  rcases of_run_mstoreAt_val hstoreCaller hp3 with ⟨hp4, hm4⟩
  have hm4' : s4.memory =
      s3.memory.write 32 e.caller.toB256.toBytes := by
    simpa only [show (1 * 32 : B256).toNat = 32 by decide +kernel]
      using hm4
  let img1 := Bytes.writeAt img 0 (Sevm.argWord e 0).toBytes
  let img2 := Bytes.writeAt img1 32 e.caller.toB256.toBytes
  have hwf4 : Mem.Wf s4.memory := by
    rw [hm4', ← hb3.memory, hm2', ← hmOwner]
    exact (h_wf.write 0 (Sevm.argWord e 0).toBytes).write
      32 e.caller.toB256.toBytes
  have hr4 : Mem.Reads s4.memory img2 := by
    rw [hm4', ← hb3.memory, hm2', ← hmOwner]
    exact Mem.Reads.write
      (h_wf.write 0 (Sevm.argWord e 0).toBytes)
      (Mem.Reads.write h_wf h_reads 0 (Sevm.argWord e 0).toBytes)
      32 e.caller.toB256.toBytes
  rcases prefix_of_allowanceKeyFromMemory_image hp4 hwf4 hr4 hkey with
    ⟨hp5, hwf5, hr5⟩
  have himg : img2.sliceD 0 64 0 =
      (Sevm.argWord e 0).toBytes ++ e.caller.toB256.toBytes := by
    dsimp only [img2, img1]
    apply slice_two_words
    exact B256.length_toBytes _
  rw [himg] at hp5
  change callerAllowanceRuntimeKey e :: [] <<+ r.stack at hp5
  exact ⟨hp5, hwf5, ⟨img2, hr5⟩⟩

private lemma sub_logs {e : Sevm} {s r : Devm}
    (run : Ninst.Run e s sub r) : s.logs = r.logs := by
  rcases of_run_reg run with ⟨pc, hrun⟩
  simp only [Rinst.run, Rinst.runCore] at hrun
  exact (Devm.diffBurn_of_applyBinary hrun).choose_spec.choose_spec.logs

private lemma sub_output {e : Sevm} {s r : Devm}
    (run : Ninst.Run e s sub r) : s.output = r.output := by
  rcases of_run_reg run with ⟨pc, hrun⟩
  simp only [Rinst.run, Rinst.runCore] at hrun
  exact (Devm.diffBurn_of_applyBinary hrun).choose_spec.choose_spec.output

private lemma sload_logs {e : Sevm} {s r : Devm}
    (run : Ninst.Run e s sload r) : s.logs = r.logs := by
  rcases of_run_reg run with ⟨pc, hrun⟩
  simp only [Rinst.run, Rinst.runCore] at hrun
  rcases Except.bind_eq_ok hrun with ⟨⟨key, s1⟩, hpop, htail⟩
  refine (Devm.pop_of_pop hpop).logs.trans ?_
  suffices H : ∀ (d : Devm) (c : Nat), s1.logs = d.logs →
      (chargeGas c d >>=
        fun y => Devm.push (Devm.getStorVal y e.currentTarget key) y) =
          .ok r → s1.logs = r.logs by
    split at htail
    · exact H s1 gasWarmAccess rfl htail
    · exact H (addAccessedStorageKey s1 e.currentTarget key)
        gasColdSload rfl htail
  intro d c hlogs hrun'
  rcases Except.bind_eq_ok hrun' with ⟨s2, hcharge, hpush⟩
  exact (hlogs.trans (Devm.burn_of_chargeGas hcharge).logs).trans
    (Devm.push_of_push hpush).logs

private lemma sload_output {e : Sevm} {s r : Devm}
    (run : Ninst.Run e s sload r) : s.output = r.output := by
  rcases of_run_reg run with ⟨pc, hrun⟩
  simp only [Rinst.run, Rinst.runCore] at hrun
  rcases Except.bind_eq_ok hrun with ⟨⟨key, s1⟩, hpop, htail⟩
  refine (Devm.pop_of_pop hpop).output.trans ?_
  suffices H : ∀ (d : Devm) (c : Nat), s1.output = d.output →
      (chargeGas c d >>=
        fun y => Devm.push (Devm.getStorVal y e.currentTarget key) y) =
          .ok r → s1.output = r.output by
    split at htail
    · exact H s1 gasWarmAccess rfl htail
    · exact H (addAccessedStorageKey s1 e.currentTarget key)
        gasColdSload rfl htail
  intro d c houtput hrun'
  rcases Except.bind_eq_ok hrun' with ⟨s2, hcharge, hpush⟩
  exact (houtput.trans (Devm.burn_of_chargeGas hcharge).output).trans
    (Devm.push_of_push hpush).output

private lemma debitLoadedBalance_logOutput
    {e : Sevm} {s r : Devm}
    (run : Line.Run e s debitLoadedBalance r) :
    s.logs = r.logs ∧ s.output = r.output := by
  unfold debitLoadedBalance at run
  rcases Line.of_run_cons run with ⟨s1, hsub, run1⟩
  rcases Line.of_run_cons run1 with ⟨s2, hswap, run2⟩
  rcases Line.of_run_cons run2 with ⟨s3, hstore, hnil⟩
  cases hnil
  exact ⟨(sub_logs hsub).trans
      ((Ninst.Hinv.inv (f := Devm.logs) hswap).trans
        (Ninst.Hinv.inv (f := Devm.logs) hstore)),
    (sub_output hsub).trans
      ((Ninst.Hinv.inv (f := Devm.output) hswap).trans
        (Ninst.Hinv.inv (f := Devm.output) hstore))⟩

/-- `returnTrue` has a self-window proof independent of the incoming memory
image: the full returned word is written at offset zero immediately before it
is read. -/
theorem of_returnTrue_exact {fs : List Func} {e : Sevm} {s r : Devm}
    {xs : Stack}
    (hp : xs <<+ s.stack)
    (run : Func.Run fs e s returnTrue r) :
    AbiReturnsTrue r ∧ Devm.getCode s = Devm.getCode r := by
  simp only [returnTrue] at run
  rcases of_run_next run with ⟨s1, htrue, run1⟩
  have hp1 : (1 : B256) :: xs <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 htrue) hp
  rcases of_run_prepend (mstoreAt 0) _ run1 with
    ⟨s2, hstore, run2⟩
  rcases of_run_mstoreAt_val hstore hp1 with ⟨hp2, hm2⟩
  rcases of_run_prepend (pushList [32, 0]) _ run2 with
    ⟨s3, hwindow, hret⟩
  rcases Line.of_run_cons hwindow with ⟨u1, hsize, hwindow1⟩
  rcases Line.of_run_cons hwindow1 with ⟨u2, hoffset, hnil⟩
  cases hnil
  have hpSize : (32 : B256) :: xs <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 hsize) hp2
  have hpWindow : (0 : B256) :: (32 : B256) :: xs <<+ s3.stack :=
    prefix_of_push (of_run_pushB256 hoffset) hpSize
  have hm3 : s2.memory = s3.memory :=
    Line.of_inv Devm.memory (by line_inv) hwindow
  have hcode : Devm.getCode s = Devm.getCode s3 :=
    ((Ninst.Hinv.inv (f := Devm.getCode) htrue).trans
      (Line.of_inv Devm.getCode (by line_inv) hstore)).trans
      (Line.of_inv Devm.getCode (by line_inv) hwindow)
  refine ⟨?_, hcode.trans (of_run_return_val hpWindow hret).2⟩
  show Devm.output r = _
  rw [(of_run_return_val hpWindow hret).1,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    ← hm3, hm2,
    show (0 * 32 : B256).toNat = 0 by decide +kernel,
    show 32 = (1 : B256).toBytes.length by
      rw [B256.length_toBytes],
    Mem.read_write_zero]
  intro hempty
  have hlen := B256.length_toBytes (1 : B256)
  rw [hempty] at hlen
  simp at hlen

/-- Observable strengthening of the caller-value sender: in addition to the
seven CALL operands, all parent-frame fields changed only by the CALL itself
are exposed at the call boundary. -/
theorem of_sendValueToCaller_frame
    {e : Sevm} {s r : Devm} {value : B256} {xs : Stack}
    (hp : value :: xs <<+ s.stack)
    (run : Line.Run e s sendValueToCaller r) :
    ∃ sc g,
      (g :: e.caller.toB256 :: value :: 0 :: 0 :: 0 :: 0 :: xs) <<+
        sc.stack ∧
      Ninst.Run e sc call r ∧
      Devm.getStor s = Devm.getStor sc ∧
      Devm.getBal s = Devm.getBal sc ∧
      Devm.getCode s = Devm.getCode sc ∧
      s.logs = sc.logs ∧ s.output = sc.output ∧ s.memory = sc.memory := by
  unfold sendValueToCaller at run
  let pre : Line := pushList [0, 0, 0, 0] ++ [swap 3, caller, gas]
  rcases of_run_append pre run with ⟨sc, hpre, hrest⟩
  rcases Line.of_run_cons hrest with ⟨r', hcall, hnil⟩
  cases hnil
  unfold pre pushList at hpre
  simp only [List.map] at hpre
  rcases Line.of_run_cons hpre with ⟨s1, hpush1, hpre1⟩
  have hp1 : (0 : B256) :: value :: xs <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 hpush1) hp
  rcases Line.of_run_cons hpre1 with ⟨s2, hpush2, hpre2⟩
  have hp2 : (0 : B256) :: 0 :: value :: xs <<+ s2.stack :=
    prefix_of_push (of_run_pushB256 hpush2) hp1
  rcases Line.of_run_cons hpre2 with ⟨s3, hpush3, hpre3⟩
  have hp3 : (0 : B256) :: 0 :: 0 :: value :: xs <<+ s3.stack :=
    prefix_of_push (of_run_pushB256 hpush3) hp2
  rcases Line.of_run_cons hpre3 with ⟨s4, hpush4, hpre4⟩
  have hp4 : (0 : B256) :: 0 :: 0 :: 0 :: value :: xs <<+ s4.stack :=
    prefix_of_push (of_run_pushB256 hpush4) hp3
  rcases Line.of_run_cons hpre4 with ⟨s5, hswap, hpre5⟩
  have hswapCore : Stack.Swap (3 : Fin 16).val
      ((0 : B256) :: 0 :: 0 :: 0 :: value :: xs)
      (value :: 0 :: 0 :: 0 :: 0 :: xs) :=
    Stack.swapCore_succ (Stack.swapCore_succ
      (Stack.swapCore_succ Stack.swapCore_zero))
  have hp5 : value :: 0 :: 0 :: 0 :: 0 :: xs <<+ s5.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp4
  rcases Line.of_run_cons hpre5 with ⟨s6, hcaller, hpre6⟩
  have hp6 : e.caller.toB256 :: value :: 0 :: 0 :: 0 :: 0 :: xs <<+
      s6.stack := prefix_of_push (of_run_caller hcaller) hp5
  rcases Line.of_run_cons hpre6 with ⟨s7, hgas, hnil7⟩
  cases hnil7
  rcases of_run_gas hgas with ⟨g, hpushGas⟩
  refine ⟨sc, g, prefix_of_push hpushGas hp6, hcall,
    Line.of_inv Devm.getStor (by line_inv) hpre,
    Line.of_inv Devm.getBal (by line_inv) hpre,
    Line.of_inv Devm.getCode (by line_inv) hpre,
    Line.of_inv Devm.logs (by line_inv) hpre,
    Line.of_inv Devm.output (by line_inv) hpre,
    Line.of_inv Devm.memory (by line_inv) hpre⟩

/-- Observable strengthening of the address-argument value sender.  The raw
ABI word is retained on the CALL stack; EVM address truncation happens only
inside CALL processing. -/
theorem of_sendValueToArg_frame (k : B256)
    {e : Sevm} {s r : Devm} {value : B256} {xs : Stack}
    (hp : value :: xs <<+ s.stack)
    (run : Line.Run e s (sendValueToArg k) r) :
    ∃ sc g,
      (g :: Sevm.argWord e k :: value :: 0 :: 0 :: 0 :: 0 :: xs) <<+
        sc.stack ∧
      Ninst.Run e sc call r ∧
      Devm.getStor s = Devm.getStor sc ∧
      Devm.getBal s = Devm.getBal sc ∧
      Devm.getCode s = Devm.getCode sc ∧
      s.logs = sc.logs ∧ s.output = sc.output ∧ s.memory = sc.memory := by
  unfold sendValueToArg at run
  let pre : Line := pushList [0, 0, 0, 0] ++ [swap 3] ++ arg k ++ [gas]
  rcases of_run_append pre run with ⟨sc, hpre, hrest⟩
  rcases Line.of_run_cons hrest with ⟨r', hcall, hnil⟩
  cases hnil
  unfold pre pushList at hpre
  simp only [List.map] at hpre
  rcases Line.of_run_cons hpre with ⟨s1, hpush1, hpre1⟩
  have hp1 : (0 : B256) :: value :: xs <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 hpush1) hp
  rcases Line.of_run_cons hpre1 with ⟨s2, hpush2, hpre2⟩
  have hp2 : (0 : B256) :: 0 :: value :: xs <<+ s2.stack :=
    prefix_of_push (of_run_pushB256 hpush2) hp1
  rcases Line.of_run_cons hpre2 with ⟨s3, hpush3, hpre3⟩
  have hp3 : (0 : B256) :: 0 :: 0 :: value :: xs <<+ s3.stack :=
    prefix_of_push (of_run_pushB256 hpush3) hp2
  rcases Line.of_run_cons hpre3 with ⟨s4, hpush4, hpre4⟩
  have hp4 : (0 : B256) :: 0 :: 0 :: 0 :: value :: xs <<+ s4.stack :=
    prefix_of_push (of_run_pushB256 hpush4) hp3
  rcases Line.of_run_cons hpre4 with ⟨s5, hswap, hpre5⟩
  have hswapCore : Stack.Swap (3 : Fin 16).val
      ((0 : B256) :: 0 :: 0 :: 0 :: value :: xs)
      (value :: 0 :: 0 :: 0 :: 0 :: xs) :=
    Stack.swapCore_succ (Stack.swapCore_succ
      (Stack.swapCore_succ Stack.swapCore_zero))
  have hp5 : value :: 0 :: 0 :: 0 :: 0 :: xs <<+ s5.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp4
  rcases of_run_append (arg k) hpre5 with ⟨s6, harg, hpre6⟩
  have hp6 : Sevm.argWord e k :: value :: 0 :: 0 :: 0 :: 0 :: xs <<+
      s6.stack := prefix_of_arg hp5 harg
  rcases Line.of_run_cons hpre6 with ⟨s7, hgas, hnil7⟩
  cases hnil7
  rcases of_run_gas hgas with ⟨g, hpushGas⟩
  refine ⟨sc, g, prefix_of_push hpushGas hp6, hcall,
    Line.of_inv Devm.getStor (by line_inv) hpre,
    Line.of_inv Devm.getBal (by line_inv) hpre,
    Line.of_inv Devm.getCode (by line_inv) hpre,
    Line.of_inv Devm.logs (by line_inv) hpre,
    Line.of_inv Devm.output (by line_inv) hpre,
    Line.of_inv Devm.memory (by line_inv) hpre⟩

/-- Exact `emitTransfer` effect retaining the concrete post-log memory image.
This strengthening lets a following callback reuse the word written for the
event data without replaying the LOG walk. -/
theorem emitTransfer_effect_frame
    {e : Sevm} {s r : Devm} {src dst amount : B256}
    {xs : Stack} {img : Bytes}
    (hp : dst :: amount :: src :: xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Line.Run e s emitTransfer r) :
    amount :: src :: xs <<+ r.stack ∧
      r.logs = s.logs ++ [ordinaryTransferLog e src dst amount] ∧
      Devm.getStor r = Devm.getStor s ∧
      Devm.getBal r = Devm.getBal s ∧
      Devm.getCode r = Devm.getCode s ∧
      r.output = s.output ∧
      Mem.Wf r.memory ∧
      Mem.Reads r.memory (Bytes.writeAt img 0 amount.toBytes) := by
  simp only [emitTransfer, Blanc.transferFromLog] at run
  rcases Line.of_run_cons run with ⟨s1, hdupSrc, run1⟩
  have hp1 : src :: dst :: amount :: src :: xs <<+ s1.stack :=
    prefix_of_dup_val hdupSrc (by show_nth) hp
  rcases Line.of_run_cons run1 with ⟨s2, hevent, run2⟩
  have hbevent := of_run_pushB256 hevent
  have hp2 : transferEvent :: src :: dst :: amount :: src :: xs <<+
      s2.stack := prefix_of_push hbevent hp1
  rcases Line.of_run_cons run2 with ⟨s3, hdupAmount, run3⟩
  have hp3 : amount :: transferEvent :: src :: dst :: amount :: src :: xs <<+
      s3.stack := prefix_of_dup_val hdupAmount (by show_nth) hp2
  rcases of_run_append (mstoreAt 0) run3 with
    ⟨s4, hstore, hlog⟩
  rcases of_run_mstoreAt_val hstore hp3 with ⟨hp4, hm4⟩
  have hm4' : s4.memory = s3.memory.write 0 amount.toBytes := by
    simpa only [show (0 * 32 : B256).toNat = 0 by decide +kernel]
      using hm4
  rcases of_logWith201_val hp4 hlog with ⟨hp5, hlogs⟩
  have hlogMem := of_logWith201_mem hp4 hlog
  have hmem_s_s3 : s.memory = s3.memory := by
    calc
      s.memory = s1.memory := Ninst.Hinv.inv (f := Devm.memory) hdupSrc
      _ = s2.memory := hbevent.memory
      _ = s3.memory := Ninst.Hinv.inv (f := Devm.memory) hdupAmount
  let img1 := Bytes.writeAt img 0 amount.toBytes
  have hwf4 : Mem.Wf s4.memory := by
    rw [hm4', ← hmem_s_s3]
    exact h_wf.write 0 amount.toBytes
  have hreads4 : Mem.Reads s4.memory img1 := by
    rw [hm4', ← hmem_s_s3]
    exact Mem.Reads.write h_wf h_reads 0 amount.toBytes
  have hdata : (s4.memory.read 0 32).1 = amount.toBytes := by
    rw [Mem.Reads.read hreads4 0 32,
      show 32 = amount.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt]
  have hlogs_s_s4 : s.logs = s4.logs := by
    calc
      s.logs = s1.logs := Ninst.Hinv.inv (f := Devm.logs) hdupSrc
      _ = s2.logs := hbevent.logs
      _ = s3.logs := Ninst.Hinv.inv (f := Devm.logs) hdupAmount
      _ = s4.logs := Line.of_inv Devm.logs (by
        unfold mstoreAt
        line_inv) hstore
  have hwfR : Mem.Wf r.memory := by
    rw [hlogMem]
    exact hwf4.extend 0 32
  have hreadsR : Mem.Reads r.memory img1 := by
    rw [hlogMem]
    exact Mem.Reads.extend hreads4 0 32
  refine ⟨hp5, ?_, ?_, ?_, ?_, ?_, hwfR, hreadsR⟩
  · rw [hlogs, hdata, ← hlogs_s_s4]
    rfl
  · exact (Line.of_inv Devm.getStor (by line_inv) run).symm
  · exact (Line.of_inv Devm.getBal (by line_inv) run).symm
  · exact (Line.of_inv Devm.getCode (by line_inv) run).symm
  · exact (Line.of_inv Devm.output (by line_inv) run).symm

/-- Compatibility projection of `emitTransfer_effect_frame`. -/
theorem emitTransfer_effect
    {e : Sevm} {s r : Devm} {src dst amount : B256}
    {xs : Stack} {img : Bytes}
    (hp : dst :: amount :: src :: xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Line.Run e s emitTransfer r) :
    amount :: src :: xs <<+ r.stack ∧
      r.logs = s.logs ++ [ordinaryTransferLog e src dst amount] ∧
      Devm.getStor r = Devm.getStor s ∧
      Devm.getBal r = Devm.getBal s ∧
      Devm.getCode r = Devm.getCode s ∧
      r.output = s.output ∧
      Mem.Wf r.memory ∧ ∃ out, Mem.Reads r.memory out := by
  rcases emitTransfer_effect_frame hp h_wf h_reads run with
    ⟨hp', hlogs, hstor, hbal, hcode, houtput, hwf, hreads'⟩
  exact ⟨hp', hlogs, hstor, hbal, hcode, houtput,
    hwf, _, hreads'⟩

/-- Exact `emitApproval` effect for arbitrary owner/spender/value words. -/
theorem emitApproval_effect
    {e : Sevm} {s r : Devm} {owner spender value : B256}
    {xs : Stack} {img : Bytes}
    (hp : spender :: value :: owner :: xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Line.Run e s emitApproval r) :
    value :: owner :: xs <<+ r.stack ∧
      r.logs = s.logs ++ [ordinaryApprovalLog e owner spender value] ∧
      Devm.getStor r = Devm.getStor s ∧
      Devm.getBal r = Devm.getBal s ∧
      Devm.getCode r = Devm.getCode s ∧
      r.output = s.output ∧
      Mem.Wf r.memory ∧ ∃ out, Mem.Reads r.memory out := by
  simp only [emitApproval] at run
  rcases Line.of_run_cons run with ⟨s1, hdupOwner, run1⟩
  have hp1 : owner :: spender :: value :: owner :: xs <<+ s1.stack :=
    prefix_of_dup_val hdupOwner (by show_nth) hp
  rcases Line.of_run_cons run1 with ⟨s2, hevent, run2⟩
  have hbevent := of_run_pushB256 hevent
  have hp2 : approvalEvent :: owner :: spender :: value :: owner :: xs <<+
      s2.stack := prefix_of_push hbevent hp1
  rcases Line.of_run_cons run2 with ⟨s3, hdupValue, run3⟩
  have hp3 : value :: approvalEvent :: owner :: spender :: value :: owner ::
      xs <<+ s3.stack := prefix_of_dup_val hdupValue (by show_nth) hp2
  rcases of_run_append (mstoreAt 0) run3 with
    ⟨s4, hstore, hlog⟩
  rcases of_run_mstoreAt_val hstore hp3 with ⟨hp4, hm4⟩
  have hm4' : s4.memory = s3.memory.write 0 value.toBytes := by
    simpa only [show (0 * 32 : B256).toNat = 0 by decide +kernel]
      using hm4
  rcases of_logWith201_val hp4 hlog with ⟨hp5, hlogs⟩
  have hlogMem := of_logWith201_mem hp4 hlog
  have hmem_s_s3 : s.memory = s3.memory := by
    calc
      s.memory = s1.memory := Ninst.Hinv.inv (f := Devm.memory) hdupOwner
      _ = s2.memory := hbevent.memory
      _ = s3.memory := Ninst.Hinv.inv (f := Devm.memory) hdupValue
  let img1 := Bytes.writeAt img 0 value.toBytes
  have hwf4 : Mem.Wf s4.memory := by
    rw [hm4', ← hmem_s_s3]
    exact h_wf.write 0 value.toBytes
  have hreads4 : Mem.Reads s4.memory img1 := by
    rw [hm4', ← hmem_s_s3]
    exact Mem.Reads.write h_wf h_reads 0 value.toBytes
  have hdata : (s4.memory.read 0 32).1 = value.toBytes := by
    rw [Mem.Reads.read hreads4 0 32,
      show 32 = value.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt]
  have hlogs_s_s4 : s.logs = s4.logs := by
    calc
      s.logs = s1.logs := Ninst.Hinv.inv (f := Devm.logs) hdupOwner
      _ = s2.logs := hbevent.logs
      _ = s3.logs := Ninst.Hinv.inv (f := Devm.logs) hdupValue
      _ = s4.logs := Line.of_inv Devm.logs (by
        unfold mstoreAt
        line_inv) hstore
  have hwfR : Mem.Wf r.memory := by
    rw [hlogMem]
    exact hwf4.extend 0 32
  have hreadsR : Mem.Reads r.memory img1 := by
    rw [hlogMem]
    exact Mem.Reads.extend hreads4 0 32
  refine ⟨hp5, ?_, ?_, ?_, ?_, ?_, hwfR, ⟨img1, hreadsR⟩⟩
  · rw [hlogs, hdata, ← hlogs_s_s4]
    rfl
  · exact (Line.of_inv Devm.getStor (by line_inv) run).symm
  · exact (Line.of_inv Devm.getBal (by line_inv) run).symm
  · exact (Line.of_inv Devm.getCode (by line_inv) run).symm
  · exact (Line.of_inv Devm.output (by line_inv) run).symm

private theorem allowanceApprovalTail_effect
    {e : Sevm} {s r : Devm} {reduced : B256} {img : Bytes}
    (hp : reduced :: [] <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Line.Run e s
      (arg 0 ++ [swap 0, caller] ++ emitApproval ++ [pop, pop]) r) :
    [] <<+ r.stack ∧
      r.logs = s.logs ++ [allowanceSpendLog e reduced] ∧
      Devm.getStor r = Devm.getStor s ∧
      Devm.getBal r = Devm.getBal s ∧
      Devm.getCode r = Devm.getCode s ∧
      r.output = s.output ∧
      Mem.Wf r.memory ∧ ∃ out, Mem.Reads r.memory out := by
  rcases of_run_append (arg 0) run with ⟨s1, howner, run1⟩
  have hp1 : Sevm.argWord e 0 :: reduced :: [] <<+ s1.stack :=
    prefix_of_arg hp howner
  rcases Line.of_run_cons run1 with ⟨s2, hswap, run2⟩
  have hswapCore : Stack.Swap (0 : Fin 16).val
      [Sevm.argWord e 0, reduced] [reduced, Sevm.argWord e 0] :=
    Stack.swapCore_zero
  have hp2 : reduced :: Sevm.argWord e 0 :: [] <<+ s2.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp1
  rcases Line.of_run_cons run2 with ⟨s3, hcaller, run3⟩
  have hp3 : e.caller.toB256 :: reduced :: Sevm.argWord e 0 :: [] <<+
      s3.stack := prefix_of_push (of_run_caller hcaller) hp2
  rcases of_run_append emitApproval run3 with ⟨s4, hemit, run4⟩
  have hmem_s_s3 : s.memory = s3.memory :=
    (Line.of_inv Devm.memory (by line_inv) howner).trans
      ((Ninst.Hinv.inv (f := Devm.memory) hswap).trans
        (of_run_caller hcaller).memory)
  have hwf3 : Mem.Wf s3.memory := by
    rw [← hmem_s_s3]
    exact h_wf
  have hreads3 : Mem.Reads s3.memory img := by
    rw [← hmem_s_s3]
    exact h_reads
  obtain ⟨hp4, hlogs4, _, _, _, _, hwf4, out, hreads4⟩ :=
    emitApproval_effect hp3 hwf3 hreads3 hemit
  rcases Line.of_run_cons run4 with ⟨s5, hpop1, run5⟩
  have hp5 := prefix_of_pop (of_run_pop hpop1) hp4
  rcases Line.of_run_cons run5 with ⟨s6, hpop2, hnil⟩
  cases hnil
  have hp6 := prefix_of_pop (of_run_pop hpop2) hp5
  have hlogs_s_s3 : s.logs = s3.logs :=
    (Line.of_inv Devm.logs (by line_inv) howner).trans
      ((Ninst.Hinv.inv (f := Devm.logs) hswap).trans
        (of_run_caller hcaller).logs)
  have hlogs_s4_r : s4.logs = r.logs :=
    (Ninst.Hinv.inv (f := Devm.logs) hpop1).trans
      (Ninst.Hinv.inv (f := Devm.logs) hpop2)
  have hmem_s4_r : s4.memory = r.memory :=
    (Ninst.Hinv.inv (f := Devm.memory) hpop1).trans
      (Ninst.Hinv.inv (f := Devm.memory) hpop2)
  refine ⟨hp6, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hlogs_s4_r, hlogs4, ← hlogs_s_s3]
    rfl
  · exact (Line.of_inv Devm.getStor (by line_inv) run).symm
  · exact (Line.of_inv Devm.getBal (by line_inv) run).symm
  · exact (Line.of_inv Devm.getCode (by line_inv) run).symm
  · exact (Line.of_inv Devm.output (by line_inv) run).symm
  · rw [← hmem_s4_r]
    exact hwf4
  · rw [← hmem_s4_r]
    exact ⟨out, hreads4⟩

/-- Exact shared burn-event tail retaining the concrete event-word memory
image for a following zero-length value CALL or typed callback. -/
theorem burnEventTail_effect_frame
    {e : Sevm} {s r : Devm} {owner amountArg : B256}
    {xs : Stack} {img : Bytes}
    (hp : owner :: xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Line.Run e s
      (arg amountArg ++ [pushB256 0] ++ emitTransfer ++ [swap 0, pop]) r) :
    Sevm.argWord e amountArg :: xs <<+ r.stack ∧
      r.logs = s.logs ++
        [ordinaryTransferLog e owner 0 (Sevm.argWord e amountArg)] ∧
      Devm.getStor r = Devm.getStor s ∧
      Devm.getBal r = Devm.getBal s ∧
      Devm.getCode r = Devm.getCode s ∧
      r.output = s.output ∧
      Mem.Wf r.memory ∧
      Mem.Reads r.memory
        (Bytes.writeAt img 0 (Sevm.argWord e amountArg).toBytes) := by
  rcases of_run_append (arg amountArg) run with
    ⟨s1, harg, run1⟩
  have hp1 : Sevm.argWord e amountArg :: owner :: xs <<+ s1.stack :=
    prefix_of_arg hp harg
  rcases Line.of_run_cons run1 with ⟨s2, hzero, run2⟩
  have hp2 : (0 : B256) :: Sevm.argWord e amountArg :: owner :: xs <<+
      s2.stack := prefix_of_push (of_run_pushB256 hzero) hp1
  rcases of_run_append emitTransfer run2 with
    ⟨s3, hemit, run3⟩
  have hmem_s_s2 : s.memory = s2.memory :=
    (Line.of_inv Devm.memory (by line_inv) harg).trans
      (Ninst.Hinv.inv (f := Devm.memory) hzero)
  have hwf2 : Mem.Wf s2.memory := by
    rw [← hmem_s_s2]
    exact h_wf
  have hreads2 : Mem.Reads s2.memory img := by
    rw [← hmem_s_s2]
    exact h_reads
  obtain ⟨hp3, hlogs3, _, _, _, _, hwf3, hreads3⟩ :=
    emitTransfer_effect_frame hp2 hwf2 hreads2 hemit
  rcases Line.of_run_cons run3 with ⟨s4, hswap, run4⟩
  have hswapCore : Stack.Swap (0 : Fin 16).val
      (Sevm.argWord e amountArg :: owner :: xs)
      (owner :: Sevm.argWord e amountArg :: xs) :=
    Stack.swapCore_zero
  have hp4 : owner :: Sevm.argWord e amountArg :: xs <<+ s4.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp3
  rcases Line.of_run_cons run4 with ⟨s5, hpop, hnil⟩
  cases hnil
  have hp5 : Sevm.argWord e amountArg :: xs <<+ r.stack :=
    prefix_of_pop (of_run_pop hpop) hp4
  have hlogs_s_s2 : s.logs = s2.logs :=
    (Line.of_inv Devm.logs (by line_inv) harg).trans
      (Ninst.Hinv.inv (f := Devm.logs) hzero)
  have hlogs_s3_r : s3.logs = r.logs :=
    (Ninst.Hinv.inv (f := Devm.logs) hswap).trans
      (Ninst.Hinv.inv (f := Devm.logs) hpop)
  have hmem_s3_r : s3.memory = r.memory :=
    (Ninst.Hinv.inv (f := Devm.memory) hswap).trans
      (Ninst.Hinv.inv (f := Devm.memory) hpop)
  refine ⟨hp5, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hlogs_s3_r, hlogs3, ← hlogs_s_s2]
  · exact (Line.of_inv Devm.getStor (by line_inv) run).symm
  · exact (Line.of_inv Devm.getBal (by line_inv) run).symm
  · exact (Line.of_inv Devm.getCode (by line_inv) run).symm
  · exact (Line.of_inv Devm.output (by line_inv) run).symm
  · rw [← hmem_s3_r]
    exact hwf3
  · rw [← hmem_s3_r]
    exact hreads3

/-- Compatibility projection of `burnEventTail_effect_frame`. -/
theorem burnEventTail_effect
    {e : Sevm} {s r : Devm} {owner amountArg : B256}
    {xs : Stack} {img : Bytes}
    (hp : owner :: xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Line.Run e s
      (arg amountArg ++ [pushB256 0] ++ emitTransfer ++ [swap 0, pop]) r) :
    Sevm.argWord e amountArg :: xs <<+ r.stack ∧
      r.logs = s.logs ++
        [ordinaryTransferLog e owner 0 (Sevm.argWord e amountArg)] ∧
      Devm.getStor r = Devm.getStor s ∧
      Devm.getBal r = Devm.getBal s ∧
      Devm.getCode r = Devm.getCode s ∧
      r.output = s.output ∧
      Mem.Wf r.memory ∧ ∃ out, Mem.Reads r.memory out := by
  rcases burnEventTail_effect_frame hp h_wf h_reads run with
    ⟨hp', hlogs, hstor, hbal, hcode, houtput, hwf, hreads'⟩
  exact ⟨hp', hlogs, hstor, hbal, hcode, houtput,
    hwf, _, hreads'⟩

/-- A value CALL whose returned success word passed WETH10's `iszero`/error
guard.  The raw target word is intentionally retained. -/
def AcceptedValueCall (e : Sevm) (target value : B256)
    (callPre guardPost : Devm) : Prop :=
  ∃ (g : B256) (callPost testPost : Devm),
    (g :: target :: value :: 0 :: 0 :: 0 :: 0 :: []) <<+
      callPre.stack ∧
    Ninst.Run e callPre call callPost ∧
    Ninst.Run e callPost iszero testPost ∧
    Devm.PopBurn [0] testPost guardPost

/-- Exact pre-call token burn and outer event, followed by an accepted
zero-length value CALL.  Any child/reentrant state and log effects live
between `callPre` and `guardPost` in `AcceptedValueCall`. -/
def BurnCallPrefix (e : Sevm) (pre callPre guardPost : Devm)
    (owner : Adr) (amount target : B256) : Prop :=
  Decrease owner amount
      (Stor.rest (Devm.getStor pre e.currentTarget))
      (Stor.rest (Devm.getStor callPre e.currentTarget)) ∧
  amount ≤ Stor.rest (Devm.getStor pre e.currentTarget) owner ∧
  (Devm.getStor callPre e.currentTarget).get flashMintedSlot =
      (Devm.getStor pre e.currentTarget).get flashMintedSlot ∧
  callPre.logs = pre.logs ++
      [ordinaryTransferLog e owner.toB256 0 amount] ∧
  Devm.getBal callPre = Devm.getBal pre ∧
  Devm.getCode callPre = Devm.getCode pre ∧
  callPre.output = pre.output ∧
  AcceptedValueCall e target amount callPre guardPost

/-! ## Direct storage-transfer branch -/

/-- Exact call-free transfer prefix for an arbitrary continuation.  The
concrete event-word memory image is retained for a following typed callback. -/
theorem transferNonzeroThen_callbackPrefix_effect (dp : DeployParams)
    {next : Func} {e : Sevm} {s r : Devm} {img : Bytes}
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      (transferNonzeroThen next) r) :
    ∃ (recipient : Adr) (callbackPre : Devm),
      recipient.toB256 = normalizedAddressArg e 0 ∧
      Transfer (Stor.rest (Devm.getStor s e.currentTarget))
        e.caller (Sevm.argWord e 1) recipient
        (Stor.rest (Devm.getStor callbackPre e.currentTarget)) ∧
      (Devm.getStor callbackPre e.currentTarget).get flashMintedSlot =
        (Devm.getStor s e.currentTarget).get flashMintedSlot ∧
      callbackPre.logs = s.logs ++
        [ordinaryTransferLog e e.caller.toB256
          (normalizedAddressArg e 0) (Sevm.argWord e 1)] ∧
      Devm.getBal callbackPre = Devm.getBal s ∧
      Devm.getCode callbackPre = Devm.getCode s ∧
      callbackPre.output = s.output ∧
      Mem.Wf callbackPre.memory ∧
      Mem.Reads callbackPre.memory
        (Bytes.writeAt img 0 (Sevm.argWord e 1).toBytes) ∧
      Func.Run ((weth10 dp).main :: weth10Aux) e callbackPre next r := by
  simp only [transferNonzeroThen] at run
  rcases of_run_prepend (loadCallerBalanceAmount 1) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadCallerBalanceAmount nil_pref hload with
    ⟨balance, hbalance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 : (balance <? Sevm.argWord e 1) :: balance ::
      Sevm.argWord e 1 :: e.caller.toB256 :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  rcases of_run_branch_call_revertWith
      (transferBalanceError_lookup dp) run2 with
    ⟨s3, hguardPop, run3⟩
  have hguardStack := hguardPop.stack
  simp only [Stack.Pop, Split, List.nil_append,
    List.cons_append] at hguardStack
  rw [hguardStack] at hp2
  have hflag : (balance <? Sevm.argWord e 1) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  have hcover : Sevm.argWord e 1 ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at hflag
    exact B256.zero_ne_one hflag.symm
  rw [hflag] at hp2
  have hp3 : balance :: Sevm.argWord e 1 :: e.caller.toB256 ::
      [] <<+ s3.stack := cons_pref_cons_inv hp2
  have hstor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
    (Line.of_inv Devm.getStor (by line_inv) hload).trans
      ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
        (PopBurn.Inv.inv hguardPop))
  have hbalance3 : balance =
      (Devm.getStor s3 e.currentTarget).get e.caller.toB256 := by
    rw [hbalance, congrFun hstor_s_s3 e.currentTarget]
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  obtain ⟨hdecrease, hcovered, hflashDebit⟩ :=
    debitLoadedBalance_storage (validAdr_toB256 e.caller)
      hbalance3 hcover hp3 hdebit
  let creditLine : Line :=
    addressArg 0 ++ [dup 0, sload] ++ arg 1 ++ [add, swap 0, sstore]
  rcases of_run_prepend creditLine _ run4 with
    ⟨s5, hcredit, run5⟩
  obtain ⟨recipient, hrecipient, hincrease, hflashCredit⟩ :=
    creditAddressArg_storage_at 0 1 (by
      simpa only [creditLine] using hcredit)
  have htransfer : Transfer
      (Stor.rest (Devm.getStor s3 e.currentTarget)) e.caller
      (Sevm.argWord e 1) recipient
      (Stor.rest (Devm.getStor s5 e.currentTarget)) :=
    ⟨by simpa only [toAdr_toB256] using hcovered,
      Stor.rest (Devm.getStor s4 e.currentTarget),
      by simpa only [toAdr_toB256] using hdecrease, hincrease⟩
  let eventPrep : Line := [caller] ++ arg 1 ++ addressArg 0
  rcases of_run_prepend eventPrep _ run5 with
    ⟨se, hprep, runEvent⟩
  unfold eventPrep at hprep
  rcases Line.of_run_cons hprep with ⟨p1, hcaller, hprep1⟩
  have hpP1 : e.caller.toB256 :: [] <<+ p1.stack :=
    prefix_of_push (of_run_caller hcaller) nil_pref
  rcases of_run_append (arg 1) hprep1 with ⟨p2, harg, haddress⟩
  have hpP2 : Sevm.argWord e 1 :: e.caller.toB256 :: [] <<+
      p2.stack := prefix_of_arg hpP1 harg
  have hpEvent : normalizedAddressArg e 0 :: Sevm.argWord e 1 ::
      e.caller.toB256 :: [] <<+ se.stack := by
    simpa only [normalizedAddressArg] using
      prefix_of_addressArg hpP2 haddress
  rcases of_run_prepend emitTransfer _ runEvent with
    ⟨callbackPre, hemit, hnext⟩
  have hmem_s_se : s.memory = se.memory := by
    calc
      s.memory = s1.memory := Line.of_inv Devm.memory (by line_inv) hload
      _ = s2.memory := Line.of_inv Devm.memory (by line_inv) hguard
      _ = s3.memory := hguardPop.memory
      _ = s4.memory := Line.of_inv Devm.memory (by line_inv) hdebit
      _ = s5.memory := Line.of_inv Devm.memory (by line_inv) hcredit
      _ = se.memory := Line.of_inv Devm.memory (by line_inv) hprep
  have hwfEvent : Mem.Wf se.memory := by
    rw [← hmem_s_se]
    exact h_wf
  have hreadsEvent : Mem.Reads se.memory img := by
    rw [← hmem_s_se]
    exact h_reads
  obtain ⟨hpNext, hemitLogs, hemitStor, hemitBal, hemitCode,
      hemitOutput, hwfNext, hreadsNext⟩ :=
    emitTransfer_effect_frame hpEvent hwfEvent hreadsEvent hemit
  have hstor_s5_callback : Devm.getStor s5 = Devm.getStor callbackPre :=
    (Line.of_inv Devm.getStor (by line_inv) hprep).trans
      hemitStor.symm
  have hlogs_s_se : s.logs = se.logs := by
    calc
      s.logs = s1.logs := Line.of_inv Devm.logs (by line_inv) hload
      _ = s2.logs := Line.of_inv Devm.logs (by line_inv) hguard
      _ = s3.logs := hguardPop.logs
      _ = s4.logs := by
        unfold debitLoadedBalance at hdebit
        rcases Line.of_run_cons hdebit with ⟨d1, hsub, hdebit1⟩
        rcases Line.of_run_cons hdebit1 with ⟨d2, hswap, hdebit2⟩
        rcases Line.of_run_cons hdebit2 with ⟨d3, hstore, hnil⟩
        cases hnil
        exact (sub_logs hsub).trans
          ((Ninst.Hinv.inv (f := Devm.logs) hswap).trans
            (Ninst.Hinv.inv (f := Devm.logs) hstore))
      _ = s5.logs := Line.of_inv Devm.logs (by line_inv) hcredit
      _ = se.logs := Line.of_inv Devm.logs (by line_inv) hprep
  have hbal_s_callback : Devm.getBal s = Devm.getBal callbackPre := by
    calc
      Devm.getBal s = Devm.getBal s1 :=
        Line.of_inv Devm.getBal (by line_inv) hload
      _ = Devm.getBal s2 := Line.of_inv Devm.getBal (by line_inv) hguard
      _ = Devm.getBal s3 := PopBurn.Inv.inv hguardPop
      _ = Devm.getBal s4 := Line.of_inv Devm.getBal (by line_inv) hdebit
      _ = Devm.getBal s5 := Line.of_inv Devm.getBal (by line_inv) hcredit
      _ = Devm.getBal se := Line.of_inv Devm.getBal (by line_inv) hprep
      _ = Devm.getBal callbackPre := hemitBal.symm
  have hcode_s_callback : Devm.getCode s = Devm.getCode callbackPre := by
    calc
      Devm.getCode s = Devm.getCode s1 :=
        Line.of_inv Devm.getCode (by line_inv) hload
      _ = Devm.getCode s2 := Line.of_inv Devm.getCode (by line_inv) hguard
      _ = Devm.getCode s3 := funext (fun a =>
        getCode_eq_of_state_eq hguardPop.state a)
      _ = Devm.getCode s4 := Line.of_inv Devm.getCode (by line_inv) hdebit
      _ = Devm.getCode s5 := Line.of_inv Devm.getCode (by line_inv) hcredit
      _ = Devm.getCode se := Line.of_inv Devm.getCode (by line_inv) hprep
      _ = Devm.getCode callbackPre := hemitCode.symm
  have houtput_s_callback : s.output = callbackPre.output := by
    calc
      s.output = s1.output := Line.of_inv Devm.output (by line_inv) hload
      _ = s2.output := Line.of_inv Devm.output (by line_inv) hguard
      _ = s3.output := hguardPop.output
      _ = s4.output := (debitLoadedBalance_logOutput hdebit).2
      _ = s5.output := Line.of_inv Devm.output (by line_inv) hcredit
      _ = se.output := Line.of_inv Devm.output (by line_inv) hprep
      _ = callbackPre.output := hemitOutput.symm
  refine ⟨recipient, callbackPre, ?_, ?_, ?_, ?_,
    hbal_s_callback.symm, hcode_s_callback.symm,
    houtput_s_callback.symm, hwfNext, hreadsNext, hnext⟩
  · simpa only [normalizedAddressArg] using hrecipient
  · simpa only [← congrFun hstor_s_s3 e.currentTarget,
      congrFun hstor_s5_callback e.currentTarget] using htransfer
  · rw [← congrFun hstor_s5_callback e.currentTarget,
      hflashCredit, hflashDebit,
      ← congrFun hstor_s_s3 e.currentTarget]
  · rw [hemitLogs, ← hlogs_s_se]

/-- Exact selected-body effect of the call-free, raw-nonzero recipient arm.
The storage recipient and indexed destination are the same normalized
low-160-bit address word. -/
theorem transferNonzero_effect (dp : DeployParams)
    {e : Sevm} {s r : Devm} {img : Bytes}
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      (transferNonzeroThen returnTrue) r) :
    ∃ recipient : Adr,
      recipient.toB256 = normalizedAddressArg e 0 ∧
      Transfer (Stor.rest (Devm.getStor s e.currentTarget))
        e.caller (Sevm.argWord e 1) recipient
        (Stor.rest (Devm.getStor r e.currentTarget)) ∧
      (Devm.getStor r e.currentTarget).get flashMintedSlot =
        (Devm.getStor s e.currentTarget).get flashMintedSlot ∧
      r.logs = s.logs ++
        [ordinaryTransferLog e e.caller.toB256
          (normalizedAddressArg e 0) (Sevm.argWord e 1)] ∧
      AbiReturnsTrue r ∧
      Devm.getBal r = Devm.getBal s ∧
      Devm.getCode r = Devm.getCode s := by
  rcases transferNonzeroThen_callbackPrefix_effect dp h_wf h_reads run with
    ⟨recipient, callbackPre, hrecipient, htransfer, hflash,
      hlogs, hbal, hcode, houtput, hwf, hreads', hreturn⟩
  obtain ⟨htrue, hreturnCode⟩ := of_returnTrue_exact nil_pref hreturn
  have hreturnStor : Devm.getStor callbackPre = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hreturn
  have hreturnBal : Devm.getBal callbackPre = Devm.getBal r :=
    Func.of_inv Devm.getBal Devm.getBal (by func_inv) hreturn
  have hreturnLogs : callbackPre.logs = r.logs :=
    Func.of_inv Devm.logs Devm.logs (by func_inv) hreturn
  refine ⟨recipient, hrecipient, ?_, ?_, ?_, htrue,
    hreturnBal.symm.trans hbal, hreturnCode.symm.trans hcode⟩
  · simpa only [← congrFun hreturnStor e.currentTarget] using htransfer
  · rw [← congrFun hreturnStor e.currentTarget]
    exact hflash
  · rw [← hreturnLogs]
    exact hlogs

/-! ## Burn/value-call paths -/

/-- Shared exact caller-burn prefix.  It stops after the accepted CALL guard
and retains the actual continuation run, so callers can choose either
canonical ABI `true` or `STOP` without rewalking the value transfer. -/
theorem of_callerBurnThen_callback_effect
    (dp : DeployParams) (amountArg : B256) (send : Line)
    (target : B256) (sendErrorSlot : Nat) (sendError : String)
    {next : Func} {e : Sevm} {s r : Devm} {img : Bytes}
    (h_send : ∀ {s0 r0 : Devm} {value : B256} {xs : Stack},
      value :: xs <<+ s0.stack → Line.Run e s0 send r0 →
      ∃ sc g,
        (g :: target :: value :: 0 :: 0 :: 0 :: 0 :: xs) <<+
          sc.stack ∧
        Ninst.Run e sc call r0 ∧
        Devm.getStor s0 = Devm.getStor sc ∧
        Devm.getBal s0 = Devm.getBal sc ∧
        Devm.getCode s0 = Devm.getCode sc ∧
        s0.logs = sc.logs ∧ s0.output = sc.output ∧
        s0.memory = sc.memory)
    (h_error_lookup :
      ((weth10 dp).main :: weth10Aux)[sendErrorSlot]? =
        some (Func.revertWith sendError))
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      (loadCallerBalanceAmount amountArg +++ balanceTooSmall +++
        (.call burnBalanceErrorSlot) <?>
        (debitLoadedBalance +++
          caller ::: arg amountArg +++ pushB256 0 ::: emitTransfer +++
          swap 0 ::: pop :::
          send +++ iszero :::
          (.call sendErrorSlot) <?> next)) r) :
    ∃ callPre guardPost,
      BurnCallPrefix e s callPre guardPost e.caller
        (Sevm.argWord e amountArg) target ∧
      Mem.Wf guardPost.memory ∧
      Mem.Reads guardPost.memory
        (Bytes.writeAt img 0 (Sevm.argWord e amountArg).toBytes) ∧
      Func.Run ((weth10 dp).main :: weth10Aux) e guardPost next r := by
  rcases of_run_prepend (loadCallerBalanceAmount amountArg) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadCallerBalanceAmount nil_pref hload with
    ⟨balance, hbalance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 : (balance <? Sevm.argWord e amountArg) :: balance ::
      Sevm.argWord e amountArg :: e.caller.toB256 :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  rcases of_run_branch_call_revertWith (burnBalanceError_lookup dp) run2 with
    ⟨s3, hguardPop, run3⟩
  have hguardStack := hguardPop.stack
  simp only [Stack.Pop, Split, List.nil_append,
    List.cons_append] at hguardStack
  rw [hguardStack] at hp2
  have hflag : (balance <? Sevm.argWord e amountArg) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  have hcover : Sevm.argWord e amountArg ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at hflag
    exact B256.zero_ne_one hflag.symm
  rw [hflag] at hp2
  have hp3 : balance :: Sevm.argWord e amountArg ::
      e.caller.toB256 :: [] <<+ s3.stack := cons_pref_cons_inv hp2
  have hstor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
    (Line.of_inv Devm.getStor (by line_inv) hload).trans
      ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
        (PopBurn.Inv.inv hguardPop))
  have hbalance3 : balance =
      (Devm.getStor s3 e.currentTarget).get e.caller.toB256 := by
    rw [hbalance, congrFun hstor_s_s3 e.currentTarget]
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  obtain ⟨hdecrease, hcovered, hflashDebit⟩ :=
    debitLoadedBalance_storage (validAdr_toB256 e.caller)
      hbalance3 hcover hp3 hdebit
  rcases of_run_prepend [caller] _ run4 with
    ⟨so, howner, runEvent⟩
  rcases Line.of_run_cons howner with ⟨so', hcaller, hnilOwner⟩
  cases hnilOwner
  have hpOwner : e.caller.toB256 :: [] <<+ so.stack :=
    prefix_of_push (of_run_caller hcaller) nil_pref
  let eventTail : Line :=
    arg amountArg ++ [pushB256 0] ++ emitTransfer ++ [swap 0, pop]
  rcases of_run_prepend eventTail _ runEvent with
    ⟨s5, hevent, run5⟩
  have hmem_s_so : s.memory = so.memory := by
    calc
      s.memory = s1.memory := Line.of_inv Devm.memory (by line_inv) hload
      _ = s2.memory := Line.of_inv Devm.memory (by line_inv) hguard
      _ = s3.memory := hguardPop.memory
      _ = s4.memory := Line.of_inv Devm.memory (by line_inv) hdebit
      _ = so.memory := Line.of_inv Devm.memory (by line_inv) howner
  have hwfOwner : Mem.Wf so.memory := by
    rw [← hmem_s_so]
    exact h_wf
  have hreadsOwner : Mem.Reads so.memory img := by
    rw [← hmem_s_so]
    exact h_reads
  obtain ⟨hp5, heventLogs, heventStor, heventBal, heventCode,
      heventOutput, hwf5, hreads5⟩ :=
    burnEventTail_effect_frame hpOwner hwfOwner hreadsOwner (by
      simpa only [eventTail] using hevent)
  rcases of_run_prepend send _ run5 with ⟨s6, hsend, run6⟩
  obtain ⟨callPre, g, hpCall, hcall, hsendStor, hsendBal,
      hsendCode, hsendLogs, hsendOutput, hsendMemory⟩ :=
    h_send hp5 hsend
  rcases of_run_next run6 with ⟨testPost, hiszero, run7⟩
  rcases of_run_branch_call_revertWith h_error_lookup run7 with
    ⟨guardPost, hcallPop, hnext⟩
  rcases of_run_call_val_with_depth_frame hpCall hcall with
      hcallFailed | hcallSuccess
  · exfalso
    have hpTest := prefix_of_iszero hiszero hcallFailed.1
    have hguardStack := hcallPop.stack
    simp only [Stack.Pop, Split, List.nil_append,
      List.cons_append] at hguardStack
    rw [hguardStack] at hpTest
    have h01 : ((0 : B256) =? 0) = 0 :=
      pref_head_unique hpTest (pref_append [(0 : B256)] guardPost.stack)
    rw [show ((0 : B256) =? 0) = 1 from by
      simp [B256.eqCheck]] at h01
    exact B256.zero_ne_one h01.symm
  rcases hcallSuccess with
    ⟨parent, child, xl, delegated, _na, code, avail, _pc, _hstep,
      hdepth, hstackEq, hparentState, hparentMemory,
      hparentLogs, hparentOutput, hdelegated, hfilled,
      hmessage, hclean, hresume, hpostState, hpostReturnData,
      hpostMemory, hpostStack⟩
  have hwfCallPre : Mem.Wf callPre.memory := by
    rw [← hsendMemory]
    exact hwf5
  have hreadsCallPre : Mem.Reads callPre.memory
      (Bytes.writeAt img 0 (Sevm.argWord e amountArg).toBytes) := by
    rw [← hsendMemory]
    exact hreads5
  have hpostMemory' : s6.memory = parent.memory := by
    simpa only [show (0 : B256).toNat = 0 from rfl, List.take_zero,
      Mem.write] using hpostMemory
  have hwf6 : Mem.Wf s6.memory := by
    rw [hpostMemory', hparentMemory]
    exact Mem.Wf.extends _ hwfCallPre
  have hreads6 : Mem.Reads s6.memory
      (Bytes.writeAt img 0 (Sevm.argWord e amountArg).toBytes) := by
    rw [hpostMemory', hparentMemory]
    exact Mem.Reads.extends _ hreadsCallPre
  have hmem6Guard : s6.memory = guardPost.memory :=
    (Ninst.Hinv.inv (f := Devm.memory) hiszero).trans hcallPop.memory
  have hwfGuard : Mem.Wf guardPost.memory := by
    rw [← hmem6Guard]
    exact hwf6
  have hreadsGuard : Mem.Reads guardPost.memory
      (Bytes.writeAt img 0 (Sevm.argWord e amountArg).toBytes) := by
    rw [← hmem6Guard]
    exact hreads6
  have hstor_s4_callPre : Devm.getStor s4 = Devm.getStor callPre :=
    (Line.of_inv Devm.getStor (by line_inv) howner).trans
      (heventStor.symm.trans hsendStor)
  have hlogs_s_s4 : s.logs = s4.logs :=
    (Line.of_inv Devm.logs (by line_inv) hload).trans
      ((Line.of_inv Devm.logs (by line_inv) hguard).trans
        (hguardPop.logs.trans (debitLoadedBalance_logOutput hdebit).1))
  have houtput_s_s4 : s.output = s4.output :=
    (Line.of_inv Devm.output (by line_inv) hload).trans
      ((Line.of_inv Devm.output (by line_inv) hguard).trans
        (hguardPop.output.trans (debitLoadedBalance_logOutput hdebit).2))
  have hownerLogs : s4.logs = so.logs :=
    Line.of_inv Devm.logs (by line_inv) howner
  have hownerOutput : s4.output = so.output :=
    Line.of_inv Devm.output (by line_inv) howner
  have hbal_s_callPre : Devm.getBal s = Devm.getBal callPre :=
    (Line.of_inv Devm.getBal (by line_inv) hload).trans
      ((Line.of_inv Devm.getBal (by line_inv) hguard).trans
        ((PopBurn.Inv.inv hguardPop).trans
          ((Line.of_inv Devm.getBal (by line_inv) hdebit).trans
            ((Line.of_inv Devm.getBal (by line_inv) howner).trans
              (heventBal.symm.trans hsendBal)))))
  have hcode_s_callPre : Devm.getCode s = Devm.getCode callPre :=
    (Line.of_inv Devm.getCode (by line_inv) hload).trans
      ((Line.of_inv Devm.getCode (by line_inv) hguard).trans
        ((funext (fun a => getCode_eq_of_state_eq hguardPop.state a)).trans
          ((Line.of_inv Devm.getCode (by line_inv) hdebit).trans
            ((Line.of_inv Devm.getCode (by line_inv) howner).trans
              (heventCode.symm.trans hsendCode)))))
  refine ⟨callPre, guardPost, ?_, hwfGuard, hreadsGuard, hnext⟩
  unfold BurnCallPrefix AcceptedValueCall
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
    g, s6, testPost, hpCall, hcall, hiszero, hcallPop⟩
  · simpa only [toAdr_toB256, ← congrFun hstor_s_s3 e.currentTarget,
      congrFun hstor_s4_callPre e.currentTarget] using hdecrease
  · simpa only [toAdr_toB256, ← congrFun hstor_s_s3 e.currentTarget]
      using hcovered
  · rw [← congrFun hstor_s4_callPre e.currentTarget,
      hflashDebit, ← congrFun hstor_s_s3 e.currentTarget]
  · rw [← hsendLogs, heventLogs, ← hownerLogs, ← hlogs_s_s4]
  · exact hbal_s_callPre.symm
  · exact hcode_s_callPre.symm
  · exact hsendOutput.symm.trans
      (heventOutput.trans (hownerOutput.symm.trans houtput_s_s4.symm))

/-- Compatibility projection of `of_callerBurnThen_callback_effect`. -/
theorem of_callerBurnThen_effect
    (dp : DeployParams) (amountArg : B256) (send : Line)
    (target : B256) (sendErrorSlot : Nat) (sendError : String)
    {next : Func} {e : Sevm} {s r : Devm} {img : Bytes}
    (h_send : ∀ {s0 r0 : Devm} {value : B256} {xs : Stack},
      value :: xs <<+ s0.stack → Line.Run e s0 send r0 →
      ∃ sc g,
        (g :: target :: value :: 0 :: 0 :: 0 :: 0 :: xs) <<+
          sc.stack ∧
        Ninst.Run e sc call r0 ∧
        Devm.getStor s0 = Devm.getStor sc ∧
        Devm.getBal s0 = Devm.getBal sc ∧
        Devm.getCode s0 = Devm.getCode sc ∧
        s0.logs = sc.logs ∧ s0.output = sc.output ∧
        s0.memory = sc.memory)
    (h_error_lookup :
      ((weth10 dp).main :: weth10Aux)[sendErrorSlot]? =
        some (Func.revertWith sendError))
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      (loadCallerBalanceAmount amountArg +++ balanceTooSmall +++
        (.call burnBalanceErrorSlot) <?>
        (debitLoadedBalance +++
          caller ::: arg amountArg +++ pushB256 0 ::: emitTransfer +++
          swap 0 ::: pop :::
          send +++ iszero :::
          (.call sendErrorSlot) <?> next)) r) :
    ∃ callPre guardPost,
      BurnCallPrefix e s callPre guardPost e.caller
        (Sevm.argWord e amountArg) target ∧
      Func.Run ((weth10 dp).main :: weth10Aux) e guardPost next r := by
  rcases of_callerBurnThen_callback_effect dp amountArg send target
      sendErrorSlot sendError h_send h_error_lookup h_wf h_reads run with
    ⟨callPre, guardPost, hprefix, -, -, hnext⟩
  exact ⟨callPre, guardPost, hprefix, hnext⟩

/-- A burn/value-call path whose successful guard falls through to canonical
ABI `true`.  State and logs after the call are arbitrary (and may include
reentrancy), but the return wrapper changes none of them. -/
def BurnReturnTrueEffect (e : Sevm) (pre post : Devm)
    (owner : Adr) (amount target : B256) : Prop :=
  ∃ callPre guardPost,
    BurnCallPrefix e pre callPre guardPost owner amount target ∧
    Devm.getStor guardPost = Devm.getStor post ∧
    Devm.getBal guardPost = Devm.getBal post ∧
    Devm.getCode guardPost = Devm.getCode post ∧
    guardPost.logs = post.logs ∧
    AbiReturnsTrue post

/-- A burn/value-call path whose successful guard falls through to `STOP`.
The guard state is therefore the public body result exactly. -/
def BurnStopEffect (e : Sevm) (pre post : Devm)
    (owner : Adr) (amount target : B256) : Prop :=
  ∃ callPre,
    BurnCallPrefix e pre callPre post owner amount target

theorem BurnCallPrefix.of_entry_eq
    {e : Sevm} {pre pre' callPre guardPost : Devm}
    {owner : Adr} {amount target : B256}
    (hstor : Devm.getStor pre' = Devm.getStor pre)
    (hbal : Devm.getBal pre' = Devm.getBal pre)
    (hcode : Devm.getCode pre' = Devm.getCode pre)
    (hlogs : pre'.logs = pre.logs)
    (houtput : pre'.output = pre.output)
    (h : BurnCallPrefix e pre callPre guardPost owner amount target) :
    BurnCallPrefix e pre' callPre guardPost owner amount target := by
  unfold BurnCallPrefix at h ⊢
  simpa only [hstor, hbal, hcode, hlogs, houtput] using h

theorem BurnReturnTrueEffect.of_entry_eq
    {e : Sevm} {pre pre' post : Devm}
    {owner : Adr} {amount target : B256}
    (hstor : Devm.getStor pre' = Devm.getStor pre)
    (hbal : Devm.getBal pre' = Devm.getBal pre)
    (hcode : Devm.getCode pre' = Devm.getCode pre)
    (hlogs : pre'.logs = pre.logs)
    (houtput : pre'.output = pre.output)
    (h : BurnReturnTrueEffect e pre post owner amount target) :
    BurnReturnTrueEffect e pre' post owner amount target := by
  rcases h with ⟨callPre, guardPost, hprefix, hrest⟩
  exact ⟨callPre, guardPost,
    hprefix.of_entry_eq hstor hbal hcode hlogs houtput, hrest⟩

theorem BurnStopEffect.of_entry_eq
    {e : Sevm} {pre pre' post : Devm}
    {owner : Adr} {amount target : B256}
    (hstor : Devm.getStor pre' = Devm.getStor pre)
    (hbal : Devm.getBal pre' = Devm.getBal pre)
    (hcode : Devm.getCode pre' = Devm.getCode pre)
    (hlogs : pre'.logs = pre.logs)
    (houtput : pre'.output = pre.output)
    (h : BurnStopEffect e pre post owner amount target) :
    BurnStopEffect e pre' post owner amount target := by
  rcases h with ⟨callPre, hprefix⟩
  exact ⟨callPre,
    hprefix.of_entry_eq hstor hbal hcode hlogs houtput⟩

/-- Exact selected zero-recipient transfer arm, including the outer burn log,
raw caller target, accepted value CALL, arbitrary child/reentrant effects, and
canonical ABI-true wrapper. -/
theorem transferZero_effect (dp : DeployParams)
    {e : Sevm} {s r : Devm} {img : Bytes}
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      (transferZeroThen returnTrue) r) :
    BurnReturnTrueEffect e s r e.caller (Sevm.argWord e 1)
      e.caller.toB256 := by
  obtain ⟨callPre, guardPost, hprefix, hreturn⟩ :=
    of_callerBurnThen_effect dp 1 sendValueToCaller e.caller.toB256
      ethTransferErrorSlot "WETH: ETH transfer failed"
      (by
        intro s0 r0 value xs hp hsend
        exact of_sendValueToCaller_frame hp hsend)
      (ethTransferError_lookup dp) h_wf h_reads
      (by simpa only [transferZeroThen] using run)
  obtain ⟨htrue, hcode⟩ := of_returnTrue_exact nil_pref hreturn
  unfold BurnReturnTrueEffect
  exact ⟨callPre, guardPost, hprefix,
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hreturn,
    Func.of_inv Devm.getBal Devm.getBal (by func_inv) hreturn,
    hcode,
    Func.of_inv Devm.logs Devm.logs (by func_inv) hreturn,
    htrue⟩

/-- Exact selected `withdraw(uint256)` effect. -/
theorem withdraw_effect (dp : DeployParams)
    {e : Sevm} {s r : Devm} {img : Bytes}
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s withdraw r) :
    BurnStopEffect e s r e.caller (Sevm.argWord e 0)
      e.caller.toB256 := by
  obtain ⟨callPre, guardPost, hprefix, hstop⟩ :=
    of_callerBurnThen_effect dp 0 sendValueToCaller e.caller.toB256
      ethTransferErrorSlot "WETH: ETH transfer failed"
      (by
        intro s0 r0 value xs hp hsend
        exact of_sendValueToCaller_frame hp hsend)
      (ethTransferError_lookup dp) h_wf h_reads
      (by simpa only [withdraw] using run)
  have hr : r = guardPost := by
    cases hstop with
    | last h =>
      simp only [Linst.Run, Linst.run] at h
      exact (Except.ok.inj h).symm
  subst r
  exact ⟨callPre, hprefix⟩

/-- Exact selected `withdrawTo(address,uint256)` effect.  The raw ABI target
word is passed intact to CALL and is truncated only by EVM call semantics. -/
theorem withdrawTo_effect (dp : DeployParams)
    {e : Sevm} {s r : Devm} {img : Bytes}
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s withdrawTo r) :
    BurnStopEffect e s r e.caller (Sevm.argWord e 1)
      (Sevm.argWord e 0) := by
  obtain ⟨callPre, guardPost, hprefix, hstop⟩ :=
    of_callerBurnThen_effect dp 1 (sendValueToArg 0)
      (Sevm.argWord e 0) ethTransferErrorSlot
      "WETH: ETH transfer failed"
      (by
        intro s0 r0 value xs hp hsend
        exact of_sendValueToArg_frame 0 hp hsend)
      (ethTransferError_lookup dp) h_wf h_reads
      (by simpa only [withdrawTo] using run)
  have hr : r = guardPost := by
    cases hstop with
    | last h =>
      simp only [Linst.Run, Linst.run] at h
      exact (Except.ok.inj h).symm
  subst r
  exact ⟨callPre, hprefix⟩

/-- Exact successful transfer prefix for an arbitrary continuation.  Both the
zero-recipient value-CALL arm and the nonzero storage-transfer arm expose the
concrete event-word memory image at the continuation boundary. -/
theorem transferThen_callbackPrefix_effect (dp : DeployParams)
    {next : Func} {e : Sevm} {pre post : Devm}
    (h_wf : Mem.Wf pre.memory)
    (h_fresh : Mem.Reads pre.memory [])
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e pre
      (transferThen next) post) :
    (Sevm.argWord e 0 = 0 ∧
      ∃ callPre callbackPre img,
        BurnCallPrefix e pre callPre callbackPre e.caller
          (Sevm.argWord e 1) e.caller.toB256 ∧
        img.length ≤ 160 ∧
        Mem.Wf callbackPre.memory ∧
        Mem.Reads callbackPre.memory img ∧
        Func.Run ((weth10 dp).main :: weth10Aux) e callbackPre next post) ∨
    (Sevm.argWord e 0 ≠ 0 ∧
      ∃ recipient callbackPre img,
        recipient.toB256 = normalizedAddressArg e 0 ∧
        Transfer (Stor.rest (Devm.getStor pre e.currentTarget))
          e.caller (Sevm.argWord e 1) recipient
          (Stor.rest (Devm.getStor callbackPre e.currentTarget)) ∧
        (Devm.getStor callbackPre e.currentTarget).get flashMintedSlot =
          (Devm.getStor pre e.currentTarget).get flashMintedSlot ∧
        callbackPre.logs = pre.logs ++
          [ordinaryTransferLog e e.caller.toB256
            (normalizedAddressArg e 0) (Sevm.argWord e 1)] ∧
        Devm.getBal callbackPre = Devm.getBal pre ∧
        Devm.getCode callbackPre = Devm.getCode pre ∧
        callbackPre.output = pre.output ∧
        img.length ≤ 160 ∧
        Mem.Wf callbackPre.memory ∧
        Mem.Reads callbackPre.memory img ∧
        Func.Run ((weth10 dp).main :: weth10Aux) e callbackPre next post) := by
  simp only [transferThen] at run
  rcases of_run_prepend (arg 0) _ run with ⟨s1, harg, run1⟩
  have hp1 : Sevm.argWord e 0 :: [] <<+ s1.stack :=
    prefix_of_arg nil_pref harg
  rcases of_run_next run1 with ⟨s2, hiszero, run2⟩
  have hp2 : (Sevm.argWord e 0 =? 0) :: [] <<+ s2.stack :=
    prefix_of_iszero hiszero hp1
  rcases of_run_branch run2 with
      ⟨s3, hpop, hnonzero⟩ |
      ⟨w, s3, s4, hnz, hpop, hburn, hzero⟩
  · have hpopStack := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append,
      List.cons_append] at hpopStack
    rw [hpopStack] at hp2
    have hflag : (Sevm.argWord e 0 =? 0) = 0 :=
      pref_head_unique hp2 (pref_append [0] s3.stack)
    have hargNonzero : Sevm.argWord e 0 ≠ 0 := by
      intro hz
      rw [hz, B256.eqCheck, if_pos rfl] at hflag
      exact B256.zero_ne_one hflag.symm
    have hstor_pre_s3 : Devm.getStor pre = Devm.getStor s3 :=
      (Line.of_inv Devm.getStor (by line_inv) harg).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
          (PopBurn.Inv.inv hpop))
    have hbal_pre_s3 : Devm.getBal pre = Devm.getBal s3 :=
      (Line.of_inv Devm.getBal (by line_inv) harg).trans
        ((Line.of_inv Devm.getBal (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
          (PopBurn.Inv.inv hpop))
    have hcode_pre_s3 : Devm.getCode pre = Devm.getCode s3 :=
      (Line.of_inv Devm.getCode (by line_inv) harg).trans
        ((Line.of_inv Devm.getCode (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
          (funext (fun a => getCode_eq_of_state_eq hpop.state a)))
    have hlogs_pre_s3 : pre.logs = s3.logs :=
      (Line.of_inv Devm.logs (by line_inv) harg).trans
        ((Ninst.Hinv.inv (f := Devm.logs) hiszero).trans hpop.logs)
    have houtput_pre_s3 : pre.output = s3.output :=
      (Line.of_inv Devm.output (by line_inv) harg).trans
        ((Ninst.Hinv.inv (f := Devm.output) hiszero).trans hpop.output)
    have hmemory_pre_s3 : pre.memory = s3.memory :=
      (Line.of_inv Devm.memory (by line_inv) harg).trans
        ((Ninst.Hinv.inv (f := Devm.memory) hiszero).trans hpop.memory)
    have hwf3 : Mem.Wf s3.memory := by
      rw [← hmemory_pre_s3]
      exact h_wf
    have hreads3 : Mem.Reads s3.memory [] := by
      rw [← hmemory_pre_s3]
      exact h_fresh
    obtain ⟨recipient, callbackPre, hrecipient, htransfer, hflash,
        hlogs, hbal, hcode, houtput, hwfCallback, hreadsCallback,
        hnext⟩ :=
      transferNonzeroThen_callbackPrefix_effect dp hwf3 hreads3 hnonzero
    have hwrite : Bytes.writeAt [] 0 (Sevm.argWord e 1).toBytes =
        (Sevm.argWord e 1).toBytes :=
      Bytes.writeAt_zero_of_le (Nat.zero_le _)
    rw [hwrite] at hreadsCallback
    right
    refine ⟨hargNonzero, recipient, callbackPre,
      (Sevm.argWord e 1).toBytes, hrecipient, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, hwfCallback, hreadsCallback, hnext⟩
    · simpa only [congrFun hstor_pre_s3 e.currentTarget] using htransfer
    · rw [hflash, ← congrFun hstor_pre_s3 e.currentTarget]
    · rw [hlogs, ← hlogs_pre_s3]
    · exact hbal.trans hbal_pre_s3.symm
    · exact hcode.trans hcode_pre_s3.symm
    · exact houtput.trans houtput_pre_s3.symm
    · rw [B256.length_toBytes]
      omega
  · have hpopStack := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append,
      List.cons_append] at hpopStack
    rw [hpopStack] at hp2
    have hflag : (Sevm.argWord e 0 =? 0) = w :=
      pref_head_unique hp2 (pref_append [w] s3.stack)
    have hargZero : Sevm.argWord e 0 = 0 := by
      by_contra hne
      rw [B256.eqCheck, if_neg hne] at hflag
      exact hnz hflag.symm
    have hstor_pre_s4 : Devm.getStor pre = Devm.getStor s4 :=
      (Line.of_inv Devm.getStor (by line_inv) harg).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
          ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn)))
    have hbal_pre_s4 : Devm.getBal pre = Devm.getBal s4 :=
      (Line.of_inv Devm.getBal (by line_inv) harg).trans
        ((Line.of_inv Devm.getBal (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
          ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn)))
    have hcode_pre_s4 : Devm.getCode pre = Devm.getCode s4 :=
      (Line.of_inv Devm.getCode (by line_inv) harg).trans
        ((Line.of_inv Devm.getCode (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
          ((funext (fun a => getCode_eq_of_state_eq hpop.state a)).trans
            (funext (fun a => getCode_eq_of_state_eq hburn.state a))))
    have hlogs_pre_s4 : pre.logs = s4.logs :=
      (Line.of_inv Devm.logs (by line_inv) harg).trans
        ((Ninst.Hinv.inv (f := Devm.logs) hiszero).trans
          (hpop.logs.trans hburn.logs))
    have houtput_pre_s4 : pre.output = s4.output :=
      (Line.of_inv Devm.output (by line_inv) harg).trans
        ((Ninst.Hinv.inv (f := Devm.output) hiszero).trans
          (hpop.output.trans hburn.output))
    have hmemory_pre_s4 : pre.memory = s4.memory :=
      (Line.of_inv Devm.memory (by line_inv) harg).trans
        ((Ninst.Hinv.inv (f := Devm.memory) hiszero).trans
          (hpop.memory.trans hburn.memory))
    have hwf4 : Mem.Wf s4.memory := by
      rw [← hmemory_pre_s4]
      exact h_wf
    have hreads4 : Mem.Reads s4.memory [] := by
      rw [← hmemory_pre_s4]
      exact h_fresh
    obtain ⟨callPre, callbackPre, hprefix, hwfCallback,
        hreadsCallback, hnext⟩ :=
      of_callerBurnThen_callback_effect dp 1 sendValueToCaller
        e.caller.toB256 ethTransferErrorSlot
        "WETH: ETH transfer failed"
        (by
          intro s0 r0 value xs hp hsend
          exact of_sendValueToCaller_frame hp hsend)
        (ethTransferError_lookup dp) hwf4 hreads4
        (by simpa only [transferZeroThen] using hzero)
    have hwrite : Bytes.writeAt [] 0 (Sevm.argWord e 1).toBytes =
        (Sevm.argWord e 1).toBytes :=
      Bytes.writeAt_zero_of_le (Nat.zero_le _)
    rw [hwrite] at hreadsCallback
    left
    refine ⟨hargZero, callPre, callbackPre,
      (Sevm.argWord e 1).toBytes, ?_, ?_, hwfCallback,
      hreadsCallback, hnext⟩
    · exact hprefix.of_entry_eq hstor_pre_s4 hbal_pre_s4 hcode_pre_s4
        hlogs_pre_s4 houtput_pre_s4
    · rw [B256.length_toBytes]
      omega

/-! ## Public transfer branch classification -/

/-- Exact successful `transfer(address,uint256)` body.  The branch is chosen
by the raw ABI word, while the nonzero branch's storage key and event topic use
the normalized low-160-bit word. -/
def TransferSuccessEffect (e : Sevm) (pre post : Devm) : Prop :=
  (Sevm.argWord e 0 = 0 ∧
    BurnReturnTrueEffect e pre post e.caller (Sevm.argWord e 1)
      e.caller.toB256) ∨
  (Sevm.argWord e 0 ≠ 0 ∧
    ∃ recipient : Adr,
      recipient.toB256 = normalizedAddressArg e 0 ∧
      Transfer (Stor.rest (Devm.getStor pre e.currentTarget))
        e.caller (Sevm.argWord e 1) recipient
        (Stor.rest (Devm.getStor post e.currentTarget)) ∧
      (Devm.getStor post e.currentTarget).get flashMintedSlot =
        (Devm.getStor pre e.currentTarget).get flashMintedSlot ∧
      post.logs = pre.logs ++
        [ordinaryTransferLog e e.caller.toB256
          (normalizedAddressArg e 0) (Sevm.argWord e 1)] ∧
      AbiReturnsTrue post ∧
      Devm.getBal post = Devm.getBal pre ∧
      Devm.getCode post = Devm.getCode pre)

theorem transfer_successEffect (dp : DeployParams)
    {e : Sevm} {s r : Devm} {img : Bytes}
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s transfer r) :
    TransferSuccessEffect e s r := by
  simp only [transfer, transferThen] at run
  rcases of_run_prepend (arg 0) _ run with ⟨s1, harg, run1⟩
  have hp1 : Sevm.argWord e 0 :: [] <<+ s1.stack :=
    prefix_of_arg nil_pref harg
  rcases of_run_next run1 with ⟨s2, hiszero, run2⟩
  have hp2 : (Sevm.argWord e 0 =? 0) :: [] <<+ s2.stack :=
    prefix_of_iszero hiszero hp1
  rcases of_run_branch run2 with
      ⟨s3, hpop, hnonzero⟩ |
      ⟨w, s3, s4, hnz, hpop, hburn, hzero⟩
  · have hpopStack := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append,
      List.cons_append] at hpopStack
    rw [hpopStack] at hp2
    have hflag : (Sevm.argWord e 0 =? 0) = 0 :=
      pref_head_unique hp2 (pref_append [0] s3.stack)
    have hargNonzero : Sevm.argWord e 0 ≠ 0 := by
      intro hz
      rw [hz, B256.eqCheck, if_pos rfl] at hflag
      exact B256.zero_ne_one hflag.symm
    have hstor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
      (Line.of_inv Devm.getStor (by line_inv) harg).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
          (PopBurn.Inv.inv hpop))
    have hbal_s_s3 : Devm.getBal s = Devm.getBal s3 :=
      (Line.of_inv Devm.getBal (by line_inv) harg).trans
        ((Line.of_inv Devm.getBal (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
          (PopBurn.Inv.inv hpop))
    have hcode_s_s3 : Devm.getCode s = Devm.getCode s3 :=
      (Line.of_inv Devm.getCode (by line_inv) harg).trans
        ((Line.of_inv Devm.getCode (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
          (funext (fun a => getCode_eq_of_state_eq hpop.state a)))
    have hlogs_s_s3 : s.logs = s3.logs :=
      (Line.of_inv Devm.logs (by line_inv) harg).trans
        ((Ninst.Hinv.inv (f := Devm.logs) hiszero).trans hpop.logs)
    have hmemory_s_s3 : s.memory = s3.memory :=
      (Line.of_inv Devm.memory (by line_inv) harg).trans
        ((Ninst.Hinv.inv (f := Devm.memory) hiszero).trans hpop.memory)
    have hwf3 : Mem.Wf s3.memory := by
      rw [← hmemory_s_s3]
      exact h_wf
    have hreads3 : Mem.Reads s3.memory img := by
      rw [← hmemory_s_s3]
      exact h_reads
    obtain ⟨recipient, hrecipient, htransfer, hflash, hlogs,
        htrue, hbal, hcode⟩ :=
      transferNonzero_effect dp hwf3 hreads3 hnonzero
    right
    refine ⟨hargNonzero, recipient, hrecipient, ?_, ?_, ?_,
      htrue, ?_, ?_⟩
    · simpa only [congrFun hstor_s_s3 e.currentTarget] using htransfer
    · rw [hflash, ← congrFun hstor_s_s3 e.currentTarget]
    · rw [hlogs, ← hlogs_s_s3]
    · exact hbal.trans hbal_s_s3.symm
    · exact hcode.trans hcode_s_s3.symm
  · have hpopStack := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append,
      List.cons_append] at hpopStack
    rw [hpopStack] at hp2
    have hflag : (Sevm.argWord e 0 =? 0) = w :=
      pref_head_unique hp2 (pref_append [w] s3.stack)
    have hargZero : Sevm.argWord e 0 = 0 := by
      by_contra hne
      rw [B256.eqCheck, if_neg hne] at hflag
      exact hnz hflag.symm
    have hstor_s_s4 : Devm.getStor s = Devm.getStor s4 :=
      (Line.of_inv Devm.getStor (by line_inv) harg).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
          ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn)))
    have hbal_s_s4 : Devm.getBal s = Devm.getBal s4 :=
      (Line.of_inv Devm.getBal (by line_inv) harg).trans
        ((Line.of_inv Devm.getBal (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
          ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn)))
    have hcode_s_s4 : Devm.getCode s = Devm.getCode s4 :=
      (Line.of_inv Devm.getCode (by line_inv) harg).trans
        ((Line.of_inv Devm.getCode (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
          ((funext (fun a => getCode_eq_of_state_eq hpop.state a)).trans
            (funext (fun a => getCode_eq_of_state_eq hburn.state a))))
    have hlogs_s_s4 : s.logs = s4.logs :=
      (Line.of_inv Devm.logs (by line_inv) harg).trans
        ((Ninst.Hinv.inv (f := Devm.logs) hiszero).trans
          (hpop.logs.trans hburn.logs))
    have houtput_s_s4 : s.output = s4.output :=
      (Line.of_inv Devm.output (by line_inv) harg).trans
        ((Ninst.Hinv.inv (f := Devm.output) hiszero).trans
          (hpop.output.trans hburn.output))
    have hmemory_s_s4 : s.memory = s4.memory :=
      (Line.of_inv Devm.memory (by line_inv) harg).trans
        ((Ninst.Hinv.inv (f := Devm.memory) hiszero).trans
          (hpop.memory.trans hburn.memory))
    have hwf4 : Mem.Wf s4.memory := by
      rw [← hmemory_s_s4]
      exact h_wf
    have hreads4 : Mem.Reads s4.memory img := by
      rw [← hmemory_s_s4]
      exact h_reads
    have heffect := transferZero_effect dp hwf4 hreads4 hzero
    left
    exact ⟨hargZero,
      heffect.of_entry_eq hstor_s_s4 hbal_s_s4 hcode_s_s4
        hlogs_s_s4 houtput_s_s4⟩

theorem TransferSuccessEffect.of_entry_eq
    {e : Sevm} {pre pre' post : Devm}
    (hstor : Devm.getStor pre' = Devm.getStor pre)
    (hbal : Devm.getBal pre' = Devm.getBal pre)
    (hcode : Devm.getCode pre' = Devm.getCode pre)
    (hlogs : pre'.logs = pre.logs)
    (houtput : pre'.output = pre.output)
    (h : TransferSuccessEffect e pre post) :
    TransferSuccessEffect e pre' post := by
  rcases h with hzero | hnonzero
  · exact Or.inl ⟨hzero.1,
      hzero.2.of_entry_eq hstor hbal hcode hlogs houtput⟩
  · rcases hnonzero with
      ⟨hraw, recipient, hrecipient, htransfer, hflash,
        hpostLogs, htrue, hpostBal, hpostCode⟩
    right
    refine ⟨hraw, recipient, hrecipient, ?_, ?_, ?_, htrue, ?_, ?_⟩
    · simpa only [congrFun hstor e.currentTarget] using htransfer
    · rw [hflash, ← congrFun hstor e.currentTarget]
    · rw [hpostLogs, ← hlogs]
    · exact hpostBal.trans hbal.symm
    · exact hpostCode.trans hcode.symm

/-! ## Compiled public entry points -/

/-- Compiled public `transfer(address,uint256)`: raw-word branch split,
normalized storage/event behavior in the nonzero branch, and exact accepted
value-call behavior in the zero branch. -/
theorem weth10_transfer_successEffect (dp : DeployParams)
    {e : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 e pre (.ok post))
    (h_code : some e.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector e =
      selector "transfer" [.address, .uint256])
    (h_nonempty : e.data.length.toB256 ≠ 0) :
    e.value = 0 ∧ TransferSuccessEffect e pre post := by
  have h_mem :
      (selector "transfer" [.address, .uint256], nonpayable transfer) ∈
        weth10Funcs dp := by
    simp [weth10Funcs]
  rcases exec_enters_weth10Nonpayable_logs
      exc h_code h_sel h_nonempty h_mem with
    ⟨mid, hvalue, hstor, hbal, hcode, hmemory,
      hlogs, houtput, hbody⟩
  have hwfMid : Mem.Wf mid.memory := by
    rw [hmemory]
    exact h_wf
  have hreadsMid : Mem.Reads mid.memory img := by
    rw [hmemory]
    exact h_reads
  have heffect := transfer_successEffect dp hwfMid hreadsMid hbody
  exact ⟨hvalue, heffect.of_entry_eq hstor.symm hbal.symm
    hcode.symm hlogs.symm houtput.symm⟩

/-- Compiled public `withdraw(uint256)`: exact caller burn/event, accepted
value CALL back to the caller, and `STOP` result. -/
theorem weth10_withdraw_successEffect (dp : DeployParams)
    {e : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 e pre (.ok post))
    (h_code : some e.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector e = selector "withdraw" [.uint256])
    (h_nonempty : e.data.length.toB256 ≠ 0) :
    e.value = 0 ∧
      BurnStopEffect e pre post e.caller (Sevm.argWord e 0)
        e.caller.toB256 := by
  have h_mem :
      (selector "withdraw" [.uint256], nonpayable withdraw) ∈
        weth10Funcs dp := by
    simp [weth10Funcs]
  rcases exec_enters_weth10Nonpayable_logs
      exc h_code h_sel h_nonempty h_mem with
    ⟨mid, hvalue, hstor, hbal, hcode, hmemory,
      hlogs, houtput, hbody⟩
  have hwfMid : Mem.Wf mid.memory := by
    rw [hmemory]
    exact h_wf
  have hreadsMid : Mem.Reads mid.memory img := by
    rw [hmemory]
    exact h_reads
  have heffect := withdraw_effect dp hwfMid hreadsMid hbody
  exact ⟨hvalue, heffect.of_entry_eq hstor.symm hbal.symm
    hcode.symm hlogs.symm houtput.symm⟩

/-- Compiled public `withdrawTo(address,uint256)`: exact caller burn/event,
raw CALL target, accepted value transfer, and `STOP` result. -/
theorem weth10_withdrawTo_successEffect (dp : DeployParams)
    {e : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 e pre (.ok post))
    (h_code : some e.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector e =
      selector "withdrawTo" [.address, .uint256])
    (h_nonempty : e.data.length.toB256 ≠ 0) :
    e.value = 0 ∧
      BurnStopEffect e pre post e.caller (Sevm.argWord e 1)
        (Sevm.argWord e 0) := by
  have h_mem :
      (selector "withdrawTo" [.address, .uint256],
        nonpayable withdrawTo) ∈ weth10Funcs dp := by
    simp [weth10Funcs]
  rcases exec_enters_weth10Nonpayable_logs
      exc h_code h_sel h_nonempty h_mem with
    ⟨mid, hvalue, hstor, hbal, hcode, hmemory,
      hlogs, houtput, hbody⟩
  have hwfMid : Mem.Wf mid.memory := by
    rw [hmemory]
    exact h_wf
  have hreadsMid : Mem.Reads mid.memory img := by
    rw [hmemory]
    exact h_reads
  have heffect := withdrawTo_effect dp hwfMid hreadsMid hbody
  exact ⟨hvalue, heffect.of_entry_eq hstor.symm hbal.symm
    hcode.symm hlogs.symm houtput.symm⟩

/-! ## Delegated normalized-source burn paths -/

/-- Shared exact normalized-owner burn prefix used by `transferFrom`'s raw
zero-recipient arm and by `withdrawFrom`. -/
theorem of_argBurnThen_effect
    (dp : DeployParams) (ownerArg amountArg : B256) (send : Line)
    (target : B256) (sendErrorSlot : Nat) (sendError : String)
    {next : Func} {e : Sevm} {s r : Devm} {img : Bytes}
    (h_send : ∀ {s0 r0 : Devm} {value : B256} {xs : Stack},
      value :: xs <<+ s0.stack → Line.Run e s0 send r0 →
      ∃ sc g,
        (g :: target :: value :: 0 :: 0 :: 0 :: 0 :: xs) <<+
          sc.stack ∧
        Ninst.Run e sc call r0 ∧
        Devm.getStor s0 = Devm.getStor sc ∧
        Devm.getBal s0 = Devm.getBal sc ∧
        Devm.getCode s0 = Devm.getCode sc ∧
        s0.logs = sc.logs ∧ s0.output = sc.output ∧
        s0.memory = sc.memory)
    (h_error_lookup :
      ((weth10 dp).main :: weth10Aux)[sendErrorSlot]? =
        some (Func.revertWith sendError))
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      (loadArgBalanceAmount ownerArg amountArg +++ balanceTooSmall +++
        (.call burnBalanceErrorSlot) <?>
        (debitLoadedBalance +++
          addressArg ownerArg +++ arg amountArg +++ pushB256 0 :::
          emitTransfer +++ swap 0 ::: pop :::
          send +++ iszero :::
          (.call sendErrorSlot) <?> next)) r) :
    ∃ callPre guardPost,
      BurnCallPrefix e s callPre guardPost
        (normalizedAddressArg e ownerArg).toAdr
        (Sevm.argWord e amountArg) target ∧
      Func.Run ((weth10 dp).main :: weth10Aux) e guardPost next r := by
  rcases of_run_prepend (loadArgBalanceAmount ownerArg amountArg) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadArgBalanceAmount ownerArg amountArg nil_pref hload with
    ⟨balance, owner, howner, hbalance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 : (balance <? Sevm.argWord e amountArg) :: balance ::
      Sevm.argWord e amountArg :: owner :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  rcases of_run_branch_call_revertWith (burnBalanceError_lookup dp) run2 with
    ⟨s3, hguardPop, run3⟩
  have hguardStack := hguardPop.stack
  simp only [Stack.Pop, Split, List.nil_append,
    List.cons_append] at hguardStack
  rw [hguardStack] at hp2
  have hflag : (balance <? Sevm.argWord e amountArg) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  have hcover : Sevm.argWord e amountArg ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at hflag
    exact B256.zero_ne_one hflag.symm
  rw [hflag] at hp2
  have hp3 : balance :: Sevm.argWord e amountArg :: owner ::
      [] <<+ s3.stack := cons_pref_cons_inv hp2
  have hstor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
    (Line.of_inv Devm.getStor (by line_inv) hload).trans
      ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
        (PopBurn.Inv.inv hguardPop))
  have hbalance3 : balance =
      (Devm.getStor s3 e.currentTarget).get owner := by
    rw [hbalance, congrFun hstor_s_s3 e.currentTarget]
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  obtain ⟨hdecrease, hcovered, hflashDebit⟩ :=
    debitLoadedBalance_storage (by
      rw [howner]
      exact normalizedAddress_valid (Sevm.argWord e ownerArg))
      hbalance3 hcover hp3 hdebit
  rcases of_run_prepend (addressArg ownerArg) _ run4 with
    ⟨so, hownerLine, runEvent⟩
  have hpOwner : normalizedAddressArg e ownerArg :: [] <<+ so.stack := by
    simpa only [normalizedAddressArg] using
      prefix_of_addressArg nil_pref hownerLine
  let eventTail : Line :=
    arg amountArg ++ [pushB256 0] ++ emitTransfer ++ [swap 0, pop]
  rcases of_run_prepend eventTail _ runEvent with
    ⟨s5, hevent, run5⟩
  have hmem_s_so : s.memory = so.memory := by
    calc
      s.memory = s1.memory := Line.of_inv Devm.memory (by line_inv) hload
      _ = s2.memory := Line.of_inv Devm.memory (by line_inv) hguard
      _ = s3.memory := hguardPop.memory
      _ = s4.memory := Line.of_inv Devm.memory (by line_inv) hdebit
      _ = so.memory := Line.of_inv Devm.memory (by line_inv) hownerLine
  have hwfOwner : Mem.Wf so.memory := by
    rw [← hmem_s_so]
    exact h_wf
  have hreadsOwner : Mem.Reads so.memory img := by
    rw [← hmem_s_so]
    exact h_reads
  obtain ⟨hp5, heventLogs, heventStor, heventBal, heventCode,
      heventOutput, _, out, hreads5⟩ :=
    burnEventTail_effect hpOwner hwfOwner hreadsOwner (by
      simpa only [eventTail] using hevent)
  rcases of_run_prepend send _ run5 with ⟨s6, hsend, run6⟩
  obtain ⟨callPre, g, hpCall, hcall, hsendStor, hsendBal,
      hsendCode, hsendLogs, hsendOutput, hsendMemory⟩ :=
    h_send hp5 hsend
  rcases of_run_next run6 with ⟨testPost, hiszero, run7⟩
  rcases of_run_branch_call_revertWith h_error_lookup run7 with
    ⟨guardPost, hcallPop, hnext⟩
  have hstor_s4_callPre : Devm.getStor s4 = Devm.getStor callPre :=
    (Line.of_inv Devm.getStor (by line_inv) hownerLine).trans
      (heventStor.symm.trans hsendStor)
  have hlogs_s_s4 : s.logs = s4.logs :=
    (Line.of_inv Devm.logs (by line_inv) hload).trans
      ((Line.of_inv Devm.logs (by line_inv) hguard).trans
        (hguardPop.logs.trans (debitLoadedBalance_logOutput hdebit).1))
  have houtput_s_s4 : s.output = s4.output :=
    (Line.of_inv Devm.output (by line_inv) hload).trans
      ((Line.of_inv Devm.output (by line_inv) hguard).trans
        (hguardPop.output.trans (debitLoadedBalance_logOutput hdebit).2))
  have hownerLogs : s4.logs = so.logs :=
    Line.of_inv Devm.logs (by line_inv) hownerLine
  have hownerOutput : s4.output = so.output :=
    Line.of_inv Devm.output (by line_inv) hownerLine
  have hbal_s_callPre : Devm.getBal s = Devm.getBal callPre :=
    (Line.of_inv Devm.getBal (by line_inv) hload).trans
      ((Line.of_inv Devm.getBal (by line_inv) hguard).trans
        ((PopBurn.Inv.inv hguardPop).trans
          ((Line.of_inv Devm.getBal (by line_inv) hdebit).trans
            ((Line.of_inv Devm.getBal (by line_inv) hownerLine).trans
              (heventBal.symm.trans hsendBal)))))
  have hcode_s_callPre : Devm.getCode s = Devm.getCode callPre :=
    (Line.of_inv Devm.getCode (by line_inv) hload).trans
      ((Line.of_inv Devm.getCode (by line_inv) hguard).trans
        ((funext (fun a => getCode_eq_of_state_eq hguardPop.state a)).trans
          ((Line.of_inv Devm.getCode (by line_inv) hdebit).trans
            ((Line.of_inv Devm.getCode (by line_inv) hownerLine).trans
              (heventCode.symm.trans hsendCode)))))
  have hvalid : ValidAdr (normalizedAddressArg e ownerArg) := by
    unfold normalizedAddressArg
    exact normalizedAddress_valid (Sevm.argWord e ownerArg)
  refine ⟨callPre, guardPost, ?_, hnext⟩
  unfold BurnCallPrefix AcceptedValueCall
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
    g, s6, testPost, hpCall, hcall, hiszero, hcallPop⟩
  · simpa only [normalizedAddressArg, howner,
      ← congrFun hstor_s_s3 e.currentTarget,
      congrFun hstor_s4_callPre e.currentTarget] using hdecrease
  · simpa only [normalizedAddressArg, howner,
      ← congrFun hstor_s_s3 e.currentTarget] using hcovered
  · rw [← congrFun hstor_s4_callPre e.currentTarget,
      hflashDebit, ← congrFun hstor_s_s3 e.currentTarget]
  · rw [toB256_toAdr hvalid, ← hsendLogs, heventLogs,
      ← hownerLogs, ← hlogs_s_s4]
  · exact hbal_s_callPre.symm
  · exact hcode_s_callPre.symm
  · exact hsendOutput.symm.trans
      (heventOutput.trans (hownerOutput.symm.trans houtput_s_s4.symm))

theorem transferFromZero_effect (dp : DeployParams)
    {e : Sevm} {s r : Devm} {img : Bytes}
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      transferFromZero r) :
    BurnReturnTrueEffect e s r (normalizedAddressArg e 0).toAdr
      (Sevm.argWord e 2) e.caller.toB256 := by
  obtain ⟨callPre, guardPost, hprefix, hreturn⟩ :=
    of_argBurnThen_effect dp 0 2 sendValueToCaller e.caller.toB256
      ethTransferErrorSlot "WETH: ETH transfer failed"
      (by
        intro s0 r0 value xs hp hsend
        exact of_sendValueToCaller_frame hp hsend)
      (ethTransferError_lookup dp) h_wf h_reads
      (by simpa only [transferFromZero] using run)
  obtain ⟨htrue, hcode⟩ := of_returnTrue_exact nil_pref hreturn
  exact ⟨callPre, guardPost, hprefix,
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hreturn,
    Func.of_inv Devm.getBal Devm.getBal (by func_inv) hreturn,
    hcode,
    Func.of_inv Devm.logs Devm.logs (by func_inv) hreturn,
    htrue⟩

theorem withdrawFromCore_effect (dp : DeployParams)
    {e : Sevm} {s r : Devm} {img : Bytes}
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      withdrawFromCore r) :
    BurnStopEffect e s r (normalizedAddressArg e 0).toAdr
      (Sevm.argWord e 2) (Sevm.argWord e 1) := by
  obtain ⟨callPre, guardPost, hprefix, hstop⟩ :=
    of_argBurnThen_effect dp 0 2 (sendValueToArg 1)
      (Sevm.argWord e 1) etherTransferErrorSlot
      "WETH: Ether transfer failed"
      (by
        intro s0 r0 value xs hp hsend
        exact of_sendValueToArg_frame 1 hp hsend)
      (etherTransferError_lookup dp) h_wf h_reads
      (by simpa only [withdrawFromCore] using run)
  have hr : r = guardPost := by
    cases hstop with
    | last h =>
      simp only [Linst.Run, Linst.run] at h
      exact (Except.ok.inj h).symm
  subst r
  exact ⟨callPre, hprefix⟩

/-- Exact selected nonzero-recipient `transferFrom` core.  Both source and
destination balance keys/event topics use normalized ABI address words. -/
theorem transferFromNonzero_effect (dp : DeployParams)
    {e : Sevm} {s r : Devm} {img : Bytes}
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      transferFromNonzero r) :
    ∃ recipient : Adr,
      recipient.toB256 = normalizedAddressArg e 1 ∧
      Transfer (Stor.rest (Devm.getStor s e.currentTarget))
        (normalizedAddressArg e 0).toAdr (Sevm.argWord e 2) recipient
        (Stor.rest (Devm.getStor r e.currentTarget)) ∧
      (Devm.getStor r e.currentTarget).get flashMintedSlot =
        (Devm.getStor s e.currentTarget).get flashMintedSlot ∧
      r.logs = s.logs ++
        [ordinaryTransferLog e (normalizedAddressArg e 0)
          (normalizedAddressArg e 1) (Sevm.argWord e 2)] ∧
      AbiReturnsTrue r ∧
      Devm.getBal r = Devm.getBal s ∧
      Devm.getCode r = Devm.getCode s := by
  simp only [transferFromNonzero] at run
  rcases of_run_prepend (loadArgBalanceAmount 0 2) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadArgBalanceAmount 0 2 nil_pref hload with
    ⟨balance, owner, howner, hbalance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 : (balance <? Sevm.argWord e 2) :: balance ::
      Sevm.argWord e 2 :: owner :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  rcases of_run_branch_call_revertWith
      (transferBalanceError_lookup dp) run2 with
    ⟨s3, hguardPop, run3⟩
  have hguardStack := hguardPop.stack
  simp only [Stack.Pop, Split, List.nil_append,
    List.cons_append] at hguardStack
  rw [hguardStack] at hp2
  have hflag : (balance <? Sevm.argWord e 2) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  have hcover : Sevm.argWord e 2 ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at hflag
    exact B256.zero_ne_one hflag.symm
  rw [hflag] at hp2
  have hp3 : balance :: Sevm.argWord e 2 :: owner ::
      [] <<+ s3.stack := cons_pref_cons_inv hp2
  have hstor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
    (Line.of_inv Devm.getStor (by line_inv) hload).trans
      ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
        (PopBurn.Inv.inv hguardPop))
  have hbalance3 : balance =
      (Devm.getStor s3 e.currentTarget).get owner := by
    rw [hbalance, congrFun hstor_s_s3 e.currentTarget]
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  obtain ⟨hdecrease, hcovered, hflashDebit⟩ :=
    debitLoadedBalance_storage (by
      rw [howner]
      exact normalizedAddress_valid (Sevm.argWord e 0))
      hbalance3 hcover hp3 hdebit
  let creditLine : Line :=
    addressArg 1 ++ [dup 0, sload] ++ arg 2 ++ [add, swap 0, sstore]
  rcases of_run_prepend creditLine _ run4 with
    ⟨s5, hcredit, run5⟩
  obtain ⟨recipient, hrecipient, hincrease, hflashCredit⟩ :=
    creditAddressArg_storage_at 1 2 (by
      simpa only [creditLine] using hcredit)
  have htransfer : Transfer
      (Stor.rest (Devm.getStor s3 e.currentTarget))
      (normalizedAddressArg e 0).toAdr (Sevm.argWord e 2) recipient
      (Stor.rest (Devm.getStor s5 e.currentTarget)) :=
    ⟨by simpa only [normalizedAddressArg, howner] using hcovered,
      Stor.rest (Devm.getStor s4 e.currentTarget),
      by simpa only [normalizedAddressArg, howner] using hdecrease,
      hincrease⟩
  let eventPrep : Line := addressArg 0 ++ arg 2 ++ addressArg 1
  rcases of_run_prepend eventPrep _ run5 with
    ⟨se, hprep, runEvent⟩
  unfold eventPrep at hprep
  rcases of_run_append (addressArg 0) hprep with
    ⟨p1, hsource, hprep1⟩
  have hpP1 : normalizedAddressArg e 0 :: [] <<+ p1.stack := by
    simpa only [normalizedAddressArg] using
      prefix_of_addressArg nil_pref hsource
  rcases of_run_append (arg 2) hprep1 with ⟨p2, harg, hdest⟩
  have hpP2 : Sevm.argWord e 2 :: normalizedAddressArg e 0 :: [] <<+
      p2.stack := prefix_of_arg hpP1 harg
  have hpEvent : normalizedAddressArg e 1 :: Sevm.argWord e 2 ::
      normalizedAddressArg e 0 :: [] <<+ se.stack := by
    simpa only [normalizedAddressArg] using
      prefix_of_addressArg hpP2 hdest
  rcases of_run_prepend emitTransfer _ runEvent with
    ⟨sr, hemit, hreturn⟩
  have hmem_s_se : s.memory = se.memory := by
    calc
      s.memory = s1.memory := Line.of_inv Devm.memory (by line_inv) hload
      _ = s2.memory := Line.of_inv Devm.memory (by line_inv) hguard
      _ = s3.memory := hguardPop.memory
      _ = s4.memory := Line.of_inv Devm.memory (by line_inv) hdebit
      _ = s5.memory := Line.of_inv Devm.memory (by line_inv) hcredit
      _ = se.memory := Line.of_inv Devm.memory (by line_inv) hprep
  have hwfEvent : Mem.Wf se.memory := by
    rw [← hmem_s_se]
    exact h_wf
  have hreadsEvent : Mem.Reads se.memory img := by
    rw [← hmem_s_se]
    exact h_reads
  obtain ⟨hpReturn, hemitLogs, _, _, _, _, hwfReturn,
      out, hreadsReturn⟩ :=
    emitTransfer_effect hpEvent hwfEvent hreadsEvent hemit
  obtain ⟨htrue, hreturnCode⟩ :=
    of_returnTrue_shared hpReturn hwfReturn hreadsReturn hreturn
  have hstor_s5_r : Devm.getStor s5 = Devm.getStor r :=
    (Line.of_inv Devm.getStor (by line_inv) hprep).trans
      ((Line.of_inv Devm.getStor (by line_inv) hemit).trans
        (Func.of_inv Devm.getStor Devm.getStor (by func_inv) hreturn))
  have hlogs_s_se : s.logs = se.logs := by
    calc
      s.logs = s1.logs := Line.of_inv Devm.logs (by line_inv) hload
      _ = s2.logs := Line.of_inv Devm.logs (by line_inv) hguard
      _ = s3.logs := hguardPop.logs
      _ = s4.logs := (debitLoadedBalance_logOutput hdebit).1
      _ = s5.logs := Line.of_inv Devm.logs (by line_inv) hcredit
      _ = se.logs := Line.of_inv Devm.logs (by line_inv) hprep
  have hlogs_sr : sr.logs = r.logs :=
    Func.of_inv Devm.logs Devm.logs (by func_inv) hreturn
  have hbal_s_r : Devm.getBal s = Devm.getBal r := by
    calc
      Devm.getBal s = Devm.getBal s1 :=
        Line.of_inv Devm.getBal (by line_inv) hload
      _ = Devm.getBal s2 := Line.of_inv Devm.getBal (by line_inv) hguard
      _ = Devm.getBal s3 := PopBurn.Inv.inv hguardPop
      _ = Devm.getBal s4 := Line.of_inv Devm.getBal (by line_inv) hdebit
      _ = Devm.getBal s5 := Line.of_inv Devm.getBal (by line_inv) hcredit
      _ = Devm.getBal se := Line.of_inv Devm.getBal (by line_inv) hprep
      _ = Devm.getBal sr := Line.of_inv Devm.getBal (by line_inv) hemit
      _ = Devm.getBal r :=
        Func.of_inv Devm.getBal Devm.getBal (by func_inv) hreturn
  have hcode_s_r : Devm.getCode s = Devm.getCode r := by
    calc
      Devm.getCode s = Devm.getCode s1 :=
        Line.of_inv Devm.getCode (by line_inv) hload
      _ = Devm.getCode s2 := Line.of_inv Devm.getCode (by line_inv) hguard
      _ = Devm.getCode s3 := funext (fun a =>
        getCode_eq_of_state_eq hguardPop.state a)
      _ = Devm.getCode s4 := Line.of_inv Devm.getCode (by line_inv) hdebit
      _ = Devm.getCode s5 := Line.of_inv Devm.getCode (by line_inv) hcredit
      _ = Devm.getCode se := Line.of_inv Devm.getCode (by line_inv) hprep
      _ = Devm.getCode sr := Line.of_inv Devm.getCode (by line_inv) hemit
      _ = Devm.getCode r := hreturnCode
  refine ⟨recipient, ?_, ?_, ?_, ?_, htrue,
    hbal_s_r.symm, hcode_s_r.symm⟩
  · simpa only [normalizedAddressArg] using hrecipient
  · simpa only [← congrFun hstor_s_s3 e.currentTarget,
      congrFun hstor_s5_r e.currentTarget] using htransfer
  · rw [← congrFun hstor_s5_r e.currentTarget,
      hflashCredit, hflashDebit,
      ← congrFun hstor_s_s3 e.currentTarget]
  · rw [← hlogs_sr, hemitLogs, ← hlogs_s_se]

/-- Exact `transferFrom` core fork.  The raw recipient word selects burn vs
storage transfer; normalized words are used only once an address becomes a
balance key or indexed `Transfer` topic. -/
def TransferFromCoreSuccessEffect (e : Sevm) (pre post : Devm) : Prop :=
  (Sevm.argWord e 1 = 0 ∧
    BurnReturnTrueEffect e pre post (normalizedAddressArg e 0).toAdr
      (Sevm.argWord e 2) e.caller.toB256) ∨
  (Sevm.argWord e 1 ≠ 0 ∧
    ∃ recipient : Adr,
      recipient.toB256 = normalizedAddressArg e 1 ∧
      Transfer (Stor.rest (Devm.getStor pre e.currentTarget))
        (normalizedAddressArg e 0).toAdr (Sevm.argWord e 2) recipient
        (Stor.rest (Devm.getStor post e.currentTarget)) ∧
      (Devm.getStor post e.currentTarget).get flashMintedSlot =
        (Devm.getStor pre e.currentTarget).get flashMintedSlot ∧
      post.logs = pre.logs ++
        [ordinaryTransferLog e (normalizedAddressArg e 0)
          (normalizedAddressArg e 1) (Sevm.argWord e 2)] ∧
      AbiReturnsTrue post ∧
      Devm.getBal post = Devm.getBal pre ∧
      Devm.getCode post = Devm.getCode pre)

theorem transferFromCore_successEffect (dp : DeployParams)
    {e : Sevm} {s r : Devm} {img : Bytes}
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      transferFromCore r) :
    TransferFromCoreSuccessEffect e s r := by
  simp only [transferFromCore] at run
  rcases of_run_prepend (arg 1) _ run with ⟨s1, harg, run1⟩
  have hp1 : Sevm.argWord e 1 :: [] <<+ s1.stack :=
    prefix_of_arg nil_pref harg
  rcases of_run_next run1 with ⟨s2, hiszero, run2⟩
  have hp2 : (Sevm.argWord e 1 =? 0) :: [] <<+ s2.stack :=
    prefix_of_iszero hiszero hp1
  rcases of_run_branch run2 with
      ⟨s3, hpop, hnonzero⟩ |
      ⟨w, s3, s4, hnz, hpop, hburn, hzero⟩
  · have hpopStack := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append,
      List.cons_append] at hpopStack
    rw [hpopStack] at hp2
    have hflag : (Sevm.argWord e 1 =? 0) = 0 :=
      pref_head_unique hp2 (pref_append [0] s3.stack)
    have hargNonzero : Sevm.argWord e 1 ≠ 0 := by
      intro hz
      rw [hz, B256.eqCheck, if_pos rfl] at hflag
      exact B256.zero_ne_one hflag.symm
    have hstor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
      (Line.of_inv Devm.getStor (by line_inv) harg).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
          (PopBurn.Inv.inv hpop))
    have hbal_s_s3 : Devm.getBal s = Devm.getBal s3 :=
      (Line.of_inv Devm.getBal (by line_inv) harg).trans
        ((Line.of_inv Devm.getBal (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
          (PopBurn.Inv.inv hpop))
    have hcode_s_s3 : Devm.getCode s = Devm.getCode s3 :=
      (Line.of_inv Devm.getCode (by line_inv) harg).trans
        ((Line.of_inv Devm.getCode (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
          (funext (fun a => getCode_eq_of_state_eq hpop.state a)))
    have hlogs_s_s3 : s.logs = s3.logs :=
      (Line.of_inv Devm.logs (by line_inv) harg).trans
        ((Ninst.Hinv.inv (f := Devm.logs) hiszero).trans hpop.logs)
    have hmemory_s_s3 : s.memory = s3.memory :=
      (Line.of_inv Devm.memory (by line_inv) harg).trans
        ((Ninst.Hinv.inv (f := Devm.memory) hiszero).trans hpop.memory)
    have hwf3 : Mem.Wf s3.memory := by
      rw [← hmemory_s_s3]
      exact h_wf
    have hreads3 : Mem.Reads s3.memory img := by
      rw [← hmemory_s_s3]
      exact h_reads
    obtain ⟨recipient, hrecipient, htransfer, hflash, hlogs,
        htrue, hbal, hcode⟩ :=
      transferFromNonzero_effect dp hwf3 hreads3 hnonzero
    right
    refine ⟨hargNonzero, recipient, hrecipient, ?_, ?_, ?_,
      htrue, ?_, ?_⟩
    · simpa only [congrFun hstor_s_s3 e.currentTarget] using htransfer
    · rw [hflash, ← congrFun hstor_s_s3 e.currentTarget]
    · rw [hlogs, ← hlogs_s_s3]
    · exact hbal.trans hbal_s_s3.symm
    · exact hcode.trans hcode_s_s3.symm
  · have hpopStack := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append,
      List.cons_append] at hpopStack
    rw [hpopStack] at hp2
    have hflag : (Sevm.argWord e 1 =? 0) = w :=
      pref_head_unique hp2 (pref_append [w] s3.stack)
    have hargZero : Sevm.argWord e 1 = 0 := by
      by_contra hne
      rw [B256.eqCheck, if_neg hne] at hflag
      exact hnz hflag.symm
    have hstor_s_s4 : Devm.getStor s = Devm.getStor s4 :=
      (Line.of_inv Devm.getStor (by line_inv) harg).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
          ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn)))
    have hbal_s_s4 : Devm.getBal s = Devm.getBal s4 :=
      (Line.of_inv Devm.getBal (by line_inv) harg).trans
        ((Line.of_inv Devm.getBal (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
          ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn)))
    have hcode_s_s4 : Devm.getCode s = Devm.getCode s4 :=
      (Line.of_inv Devm.getCode (by line_inv) harg).trans
        ((Line.of_inv Devm.getCode (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
          ((funext (fun a => getCode_eq_of_state_eq hpop.state a)).trans
            (funext (fun a => getCode_eq_of_state_eq hburn.state a))))
    have hlogs_s_s4 : s.logs = s4.logs :=
      (Line.of_inv Devm.logs (by line_inv) harg).trans
        ((Ninst.Hinv.inv (f := Devm.logs) hiszero).trans
          (hpop.logs.trans hburn.logs))
    have houtput_s_s4 : s.output = s4.output :=
      (Line.of_inv Devm.output (by line_inv) harg).trans
        ((Ninst.Hinv.inv (f := Devm.output) hiszero).trans
          (hpop.output.trans hburn.output))
    have hmemory_s_s4 : s.memory = s4.memory :=
      (Line.of_inv Devm.memory (by line_inv) harg).trans
        ((Ninst.Hinv.inv (f := Devm.memory) hiszero).trans
          (hpop.memory.trans hburn.memory))
    have hwf4 : Mem.Wf s4.memory := by
      rw [← hmemory_s_s4]
      exact h_wf
    have hreads4 : Mem.Reads s4.memory img := by
      rw [← hmemory_s_s4]
      exact h_reads
    have heffect := transferFromZero_effect dp hwf4 hreads4 hzero
    left
    exact ⟨hargZero,
      heffect.of_entry_eq hstor_s_s4 hbal_s_s4 hcode_s_s4
        hlogs_s_s4 houtput_s_s4⟩

/-! ## Exact delegated allowance fork -/

theorem of_spendCallerAllowanceThen_effect
    (dp : DeployParams) (amountArg : B256) (nextSlot : Nat)
    (core : Func)
    (hnext : ((weth10 dp).main :: weth10Aux)[nextSlot]? = some core)
    {e : Sevm} {s r : Devm} {img : Bytes}
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      (spendCallerAllowanceThen amountArg nextSlot) r) :
    ∃ corePre,
      Func.Run ((weth10 dp).main :: weth10Aux) e corePre core r ∧
      CallerAllowanceOutcome e s corePre amountArg ∧
      Mem.Wf corePre.memory ∧
      (∃ out, Mem.Reads corePre.memory out) := by
  unfold spendCallerAllowanceThen at run
  let ownerEqLine : Line := arg 0 ++ [caller, eq]
  rcases of_run_prepend ownerEqLine _ run with
    ⟨s1, hownerEq, run1⟩
  have hp1 : (e.caller.toB256 =? Sevm.argWord e 0) :: [] <<+
      s1.stack := by
    unfold ownerEqLine at hownerEq
    rcases of_run_append (arg 0) hownerEq with
      ⟨p1, harg, hownerEq1⟩
    have hpArg : Sevm.argWord e 0 :: [] <<+ p1.stack :=
      prefix_of_arg nil_pref harg
    rcases Line.of_run_cons hownerEq1 with
      ⟨p2, hcaller, hownerEq2⟩
    have hpCaller : e.caller.toB256 :: Sevm.argWord e 0 :: [] <<+
        p2.stack := prefix_of_push (of_run_caller hcaller) hpArg
    rcases Line.of_run_cons hownerEq2 with ⟨p3, heq, hnil⟩
    cases hnil
    exact prefix_of_eq heq hpCaller
  have hstor_s_s1 : Devm.getStor s = Devm.getStor s1 :=
    Line.of_inv Devm.getStor (by unfold ownerEqLine; line_inv) hownerEq
  have hbal_s_s1 : Devm.getBal s = Devm.getBal s1 :=
    Line.of_inv Devm.getBal (by unfold ownerEqLine; line_inv) hownerEq
  have hcode_s_s1 : Devm.getCode s = Devm.getCode s1 :=
    Line.of_inv Devm.getCode (by unfold ownerEqLine; line_inv) hownerEq
  have hlogs_s_s1 : s.logs = s1.logs :=
    Line.of_inv Devm.logs (by unfold ownerEqLine; line_inv) hownerEq
  have houtput_s_s1 : s.output = s1.output :=
    Line.of_inv Devm.output (by unfold ownerEqLine; line_inv) hownerEq
  have hmemory_s_s1 : s.memory = s1.memory :=
    Line.of_inv Devm.memory (by unfold ownerEqLine; line_inv) hownerEq
  rcases of_run_branch run1 with
      ⟨s2, houterPop, hnonself⟩ |
      ⟨wself, s2, s3, hnzself, houterPop, houterBurn, hself⟩
  · have houterStack := houterPop.stack
    simp only [Stack.Pop, Split, List.nil_append,
      List.cons_append] at houterStack
    rw [houterStack] at hp1
    have hselfFlag : (e.caller.toB256 =? Sevm.argWord e 0) = 0 :=
      pref_head_unique hp1 (pref_append [0] s2.stack)
    have hnonselfWord : Sevm.argWord e 0 ≠ e.caller.toB256 := by
      intro heq
      rw [heq, B256.eqCheck, if_pos rfl] at hselfFlag
      exact B256.zero_ne_one hselfFlag.symm
    let keyLine : Line :=
      arg 0 ++ mstoreAt 0 ++ [caller] ++ mstoreAt 1 ++
        allowanceKeyFromMemory
    rcases of_run_prepend keyLine _ hnonself with
      ⟨sk, hkeyLine, runKey⟩
    have hwf2 : Mem.Wf s2.memory := by
      rw [← houterPop.memory, ← hmemory_s_s1]
      exact h_wf
    have hreads2 : Mem.Reads s2.memory img := by
      rw [← houterPop.memory, ← hmemory_s_s1]
      exact h_reads
    obtain ⟨hpKey, hwfKey, out, hreadsKey⟩ :=
      of_callerAllowanceKeyPrefix hwf2 hreads2 (by
        simpa only [keyLine] using hkeyLine)
    have hstor_s_sk : Devm.getStor s = Devm.getStor sk :=
      hstor_s_s1.trans ((PopBurn.Inv.inv houterPop).trans
        (Line.of_inv Devm.getStor (by line_inv) hkeyLine))
    have hbal_s_sk : Devm.getBal s = Devm.getBal sk :=
      hbal_s_s1.trans ((PopBurn.Inv.inv houterPop).trans
        (Line.of_inv Devm.getBal (by line_inv) hkeyLine))
    have hcode_s_sk : Devm.getCode s = Devm.getCode sk :=
      hcode_s_s1.trans
        ((funext (fun a => getCode_eq_of_state_eq houterPop.state a)).trans
          (Line.of_inv Devm.getCode (by line_inv) hkeyLine))
    have hlogs_s_sk : s.logs = sk.logs :=
      hlogs_s_s1.trans (houterPop.logs.trans
        (Line.of_inv Devm.logs (by line_inv) hkeyLine))
    have houtput_s_sk : s.output = sk.output :=
      houtput_s_s1.trans (houterPop.output.trans
        (Line.of_inv Devm.output (by line_inv) hkeyLine))
    let inspectLine : Line := [dup 0, sload, dup 0] ++ isMax
    rcases of_run_prepend inspectLine _ runKey with
      ⟨sl, hinspect, runBranch⟩
    unfold inspectLine at hinspect
    rcases Line.of_run_cons hinspect with
      ⟨si1, hdupKey, hinspect1⟩
    have hpI1 : callerAllowanceRuntimeKey e ::
        callerAllowanceRuntimeKey e :: [] <<+ si1.stack :=
      prefix_of_dup_val hdupKey (by show_nth) hpKey
    rcases Line.of_run_cons hinspect1 with
      ⟨si2, hload, hinspect2⟩
    rcases prefix_of_sload hload hpI1 with
      ⟨allowance, hpI2, hallowanceRead⟩
    rcases Line.of_run_cons hinspect2 with
      ⟨si3, hdupAllowance, hinspect3⟩
    have hpI3 : allowance :: allowance :: callerAllowanceRuntimeKey e ::
        [] <<+ si3.stack :=
      prefix_of_dup_val hdupAllowance (by show_nth) hpI2
    rcases Line.of_run_cons hinspect3 with
      ⟨si4, hnot, hinspect4⟩
    have hpI4 : (~~~ allowance) :: allowance ::
        callerAllowanceRuntimeKey e :: [] <<+ si4.stack :=
      prefix_of_not hnot hpI3
    rcases Line.of_run_cons hinspect4 with
      ⟨si5, hiszeroMax, hnilInspect⟩
    cases hnilInspect
    have hpLoad : ((~~~ allowance) =? 0) :: allowance ::
        callerAllowanceRuntimeKey e :: [] <<+ sl.stack :=
      prefix_of_iszero hiszeroMax hpI4
    have hstor_sk_sl : Devm.getStor sk = Devm.getStor sl :=
      Line.of_inv Devm.getStor (by line_inv) hinspect
    have hbal_sk_sl : Devm.getBal sk = Devm.getBal sl :=
      Line.of_inv Devm.getBal (by line_inv) hinspect
    have hcode_sk_sl : Devm.getCode sk = Devm.getCode sl :=
      Line.of_inv Devm.getCode (by line_inv) hinspect
    have hlogs_sk_sl : sk.logs = sl.logs :=
      (Ninst.Hinv.inv (f := Devm.logs) hdupKey).trans
        ((sload_logs hload).trans
          ((Ninst.Hinv.inv (f := Devm.logs) hdupAllowance).trans
            ((Ninst.Hinv.inv (f := Devm.logs) hnot).trans
              (Ninst.Hinv.inv (f := Devm.logs) hiszeroMax))))
    have houtput_sk_sl : sk.output = sl.output :=
      (Ninst.Hinv.inv (f := Devm.output) hdupKey).trans
        ((sload_output hload).trans
          ((Ninst.Hinv.inv (f := Devm.output) hdupAllowance).trans
            ((Ninst.Hinv.inv (f := Devm.output) hnot).trans
              (Ninst.Hinv.inv (f := Devm.output) hiszeroMax))))
    have hmemory_sk_sl : sk.memory = sl.memory :=
      Line.of_inv Devm.memory (by line_inv) hinspect
    have hwfSl : Mem.Wf sl.memory := by
      rw [← hmemory_sk_sl]
      exact hwfKey
    have hreadsSl : Mem.Reads sl.memory out := by
      rw [← hmemory_sk_sl]
      exact hreadsKey
    have hallowance :
        (Devm.getStor s e.currentTarget).get
            (callerAllowanceRuntimeKey e) = allowance := by
      symm
      rw [hallowanceRead]
      change (Devm.getStor si1 e.currentTarget).get
        (callerAllowanceRuntimeKey e) = _
      rw [← congrFun (Ninst.Hinv.inv (f := Devm.getStor) hdupKey)
        e.currentTarget, ← congrFun hstor_s_sk e.currentTarget]
    have hstor_s_sl := hstor_s_sk.trans hstor_sk_sl
    have hbal_s_sl := hbal_s_sk.trans hbal_sk_sl
    have hcode_s_sl := hcode_s_sk.trans hcode_sk_sl
    have hlogs_s_sl := hlogs_s_sk.trans hlogs_sk_sl
    have houtput_s_sl := houtput_s_sk.trans houtput_sk_sl
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
      have hpFinite : allowance :: callerAllowanceRuntimeKey e ::
          [] <<+ sf.stack := cons_pref_cons_inv hpLoad
      let guardLine : Line := arg amountArg ++ [swap 0] ++ balanceTooSmall
      rcases of_run_prepend guardLine _ hfinite with
        ⟨sg, hguardLine, runGuard⟩
      have hpGuard :
          (allowance <? Sevm.argWord e amountArg) :: allowance ::
            Sevm.argWord e amountArg :: callerAllowanceRuntimeKey e ::
            [] <<+ sg.stack := by
        unfold guardLine at hguardLine
        rcases of_run_append (arg amountArg) hguardLine with
          ⟨sa, hamount, hguard1⟩
        have hpA : Sevm.argWord e amountArg :: allowance ::
            callerAllowanceRuntimeKey e :: [] <<+ sa.stack :=
          prefix_of_arg hpFinite hamount
        rcases Line.of_run_cons hguard1 with
          ⟨ss, hswap, htooSmall⟩
        have hswapCore : Stack.Swap (0 : Fin 16).val
            [Sevm.argWord e amountArg, allowance,
              callerAllowanceRuntimeKey e]
            [allowance, Sevm.argWord e amountArg,
              callerAllowanceRuntimeKey e] := Stack.swapCore_zero
        have hpS : allowance :: Sevm.argWord e amountArg ::
            callerAllowanceRuntimeKey e :: [] <<+ ss.stack :=
          Stack.prefix_of_swap hswapCore (of_run_swap hswap) hpA
        exact prefix_of_balanceTooSmall hpS htooSmall
      rcases of_run_branch_call_revertWith (allowanceError_lookup dp)
          runGuard with ⟨sb, hguardPop, runMutate⟩
      have hguardStack := hguardPop.stack
      simp only [Stack.Pop, Split, List.nil_append,
        List.cons_append] at hguardStack
      rw [hguardStack] at hpGuard
      have hguardFlag : (allowance <? Sevm.argWord e amountArg) = 0 :=
        pref_head_unique hpGuard (pref_append [0] sb.stack)
      have hcover : Sevm.argWord e amountArg ≤ allowance := by
        rw [← B256.not_lt]
        intro hlt
        rw [B256.ltCheck, if_pos hlt] at hguardFlag
        exact B256.zero_ne_one hguardFlag.symm
      rw [hguardFlag] at hpGuard
      have hpBeforeMutate : allowance :: Sevm.argWord e amountArg ::
          callerAllowanceRuntimeKey e :: [] <<+ sb.stack :=
        cons_pref_cons_inv hpGuard
      let storeLine : Line := [sub, dup 0, swap 1, sstore]
      rcases of_run_prepend storeLine _ runMutate with
        ⟨ms4, hstoreLine, runApproval⟩
      unfold storeLine at hstoreLine
      rcases Line.of_run_cons hstoreLine with
        ⟨ms1, hsub, hstore1⟩
      have hpSub : (allowance - Sevm.argWord e amountArg) ::
          callerAllowanceRuntimeKey e :: [] <<+ ms1.stack :=
        prefix_of_sub hsub hpBeforeMutate
      rcases Line.of_run_cons hstore1 with ⟨ms2, hdup, hstore2⟩
      have hpDup : (allowance - Sevm.argWord e amountArg) ::
          (allowance - Sevm.argWord e amountArg) ::
          callerAllowanceRuntimeKey e :: [] <<+ ms2.stack :=
        prefix_of_dup_val hdup (by show_nth) hpSub
      rcases Line.of_run_cons hstore2 with ⟨ms3, hswap, hstore3⟩
      have hswapCore : Stack.Swap (1 : Fin 16).val
          [(allowance - Sevm.argWord e amountArg),
            (allowance - Sevm.argWord e amountArg),
            callerAllowanceRuntimeKey e]
          [callerAllowanceRuntimeKey e,
            (allowance - Sevm.argWord e amountArg),
            (allowance - Sevm.argWord e amountArg)] :=
        Stack.swapCore_succ Stack.swapCore_zero
      have hpStore : callerAllowanceRuntimeKey e ::
          (allowance - Sevm.argWord e amountArg) ::
          (allowance - Sevm.argWord e amountArg) :: [] <<+ ms3.stack :=
        Stack.prefix_of_swap hswapCore (of_run_swap hswap) hpDup
      rcases Line.of_run_cons hstore3 with
        ⟨ms4', hstore, hnilStore⟩
      cases hnilStore
      have hset : Devm.getStor ms4 e.currentTarget =
          (Devm.getStor ms3 e.currentTarget).set
            (callerAllowanceRuntimeKey e)
            (allowance - Sevm.argWord e amountArg) :=
        sstore_getStor_set hstore hpStore
      let approvalTail : Line :=
        arg 0 ++ [swap 0, caller] ++ emitApproval ++ [pop, pop]
      rcases of_run_prepend approvalTail _ runApproval with
        ⟨scall, happroval, hcallRun⟩
      have hpAfterStore : (allowance - Sevm.argWord e amountArg) ::
          [] <<+ ms4.stack := prefix_of_sstore hstore hpStore
      have hmem_sl_ms4 : sl.memory = ms4.memory :=
        hfinitePop.memory.trans
          ((Line.of_inv Devm.memory (by unfold guardLine; line_inv)
            hguardLine).trans
            (hguardPop.memory.trans
              (Line.of_inv Devm.memory (by line_inv) hstoreLine)))
      have hwf4 : Mem.Wf ms4.memory := by
        rw [← hmem_sl_ms4]
        exact hwfSl
      have hreads4 : Mem.Reads ms4.memory out := by
        rw [← hmem_sl_ms4]
        exact hreadsSl
      obtain ⟨hpApproval, happrovalLogs, happrovalStor,
          happrovalBal, happrovalCode, happrovalOutput,
          hwfCall, outCall, hreadsCall⟩ :=
        allowanceApprovalTail_effect hpAfterStore hwf4 hreads4 (by
          simpa only [approvalTail] using happroval)
      rcases of_run_call hcallRun with
        ⟨f, corePre, hget, hcallBurn, hcore⟩
      have hf : f = core := by
        rw [hnext] at hget
        exact Option.some.inj hget.symm
      subst f
      have hstor_s_ms3 : Devm.getStor s = Devm.getStor ms3 :=
        hstor_s_sl.trans
          ((PopBurn.Inv.inv hfinitePop).trans
            ((Line.of_inv Devm.getStor (by unfold guardLine; line_inv)
              hguardLine).trans
              ((PopBurn.Inv.inv hguardPop).trans
                ((Line.of_inv Devm.getStor (by line_inv)
                  (Line.Run.cons hsub Line.Run.nil)).trans
                  ((Line.of_inv Devm.getStor (by line_inv)
                    (Line.Run.cons hdup Line.Run.nil)).trans
                    (Line.of_inv Devm.getStor (by line_inv)
                      (Line.Run.cons hswap Line.Run.nil)))))))
      have hstorCore : Devm.getStor corePre e.currentTarget =
          (Devm.getStor s e.currentTarget).set
            (callerAllowanceRuntimeKey e)
            (allowance - Sevm.argWord e amountArg) := by
        have hstor_scall_core :
            Devm.getStor scall = Devm.getStor corePre :=
          Burn.Inv.inv hcallBurn
        rw [← congrFun hstor_scall_core e.currentTarget,
          congrFun happrovalStor e.currentTarget, hset,
          ← congrFun hstor_s_ms3 e.currentTarget]
      have hlogs_s_ms4 : s.logs = ms4.logs :=
        hlogs_s_sl.trans
          (hfinitePop.logs.trans
            ((Line.of_inv Devm.logs (by unfold guardLine; line_inv)
              hguardLine).trans
              (hguardPop.logs.trans
                ((sub_logs hsub).trans
                  ((Ninst.Hinv.inv (f := Devm.logs) hdup).trans
                    ((Ninst.Hinv.inv (f := Devm.logs) hswap).trans
                      (Ninst.Hinv.inv (f := Devm.logs) hstore)))))))
      have houtput_s_ms4 : s.output = ms4.output :=
        houtput_s_sl.trans
          (hfinitePop.output.trans
            ((Line.of_inv Devm.output (by unfold guardLine; line_inv)
              hguardLine).trans
              (hguardPop.output.trans
                ((sub_output hsub).trans
                  ((Ninst.Hinv.inv (f := Devm.output) hdup).trans
                    ((Ninst.Hinv.inv (f := Devm.output) hswap).trans
                      (Ninst.Hinv.inv (f := Devm.output) hstore)))))))
      have hbal_s_core : Devm.getBal s = Devm.getBal corePre :=
        hbal_s_sl.trans
          ((PopBurn.Inv.inv hfinitePop).trans
            ((Line.of_inv Devm.getBal (by unfold guardLine; line_inv)
              hguardLine).trans
              ((PopBurn.Inv.inv hguardPop).trans
                ((Line.of_inv Devm.getBal (by line_inv) hstoreLine).trans
                  (happrovalBal.symm.trans (Burn.Inv.inv hcallBurn))))))
      have hcode_s_core : Devm.getCode s = Devm.getCode corePre :=
        hcode_s_sl.trans
          ((funext (fun a => getCode_eq_of_state_eq hfinitePop.state a)).trans
            ((Line.of_inv Devm.getCode (by unfold guardLine; line_inv)
              hguardLine).trans
              ((funext (fun a => getCode_eq_of_state_eq hguardPop.state a)).trans
                ((Line.of_inv Devm.getCode (by line_inv) hstoreLine).trans
                  (happrovalCode.symm.trans
                    (funext (fun a =>
                      getCode_eq_of_state_eq hcallBurn.state a)))))))
      have hlogsCore : corePre.logs = s.logs ++
          [allowanceSpendLog e
            (allowance - Sevm.argWord e amountArg)] := by
        rw [← hcallBurn.logs, happrovalLogs, ← hlogs_s_ms4]
      have houtputCore : corePre.output = s.output :=
        hcallBurn.output.symm.trans
          (happrovalOutput.trans houtput_s_ms4.symm)
      have hwfCore : Mem.Wf corePre.memory := by
        rw [← hcallBurn.memory]
        exact hwfCall
      have hreadsCore : Mem.Reads corePre.memory outCall := by
        rw [← hcallBurn.memory]
        exact hreadsCall
      refine ⟨corePre, hcore, ?_, hwfCore, ⟨outCall, hreadsCore⟩⟩
      unfold CallerAllowanceOutcome
      refine ⟨Or.inr ⟨hnonselfWord, Or.inr
        ⟨allowance, hneMax, hcover, hallowance, hstorCore,
          hlogsCore⟩⟩, houtputCore, hbal_s_core.symm,
        hcode_s_core.symm⟩
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
      rcases of_run_next hmax with ⟨sm3, hpop1, hmax1⟩
      rcases of_run_next hmax1 with ⟨sm4, hpop2, hcallRun⟩
      rcases of_run_call hcallRun with
        ⟨f, corePre, hget, hcallBurn, hcore⟩
      have hf : f = core := by
        rw [hnext] at hget
        exact Option.some.inj hget.symm
      subst f
      let hpops : Line.Run e sm2 [pop, pop] sm4 :=
        Line.Run.cons hpop1 (Line.Run.cons hpop2 Line.Run.nil)
      have hstor_s_core : Devm.getStor s = Devm.getStor corePre :=
        hstor_s_sl.trans
          ((PopBurn.Inv.inv hmaxPop).trans
            ((Burn.Inv.inv hmaxBurn).trans
              ((Line.of_inv Devm.getStor (by line_inv) hpops).trans
                (Burn.Inv.inv hcallBurn))))
      have hbal_s_core : Devm.getBal s = Devm.getBal corePre :=
        hbal_s_sl.trans
          ((PopBurn.Inv.inv hmaxPop).trans
            ((Burn.Inv.inv hmaxBurn).trans
              ((Line.of_inv Devm.getBal (by line_inv) hpops).trans
                (Burn.Inv.inv hcallBurn))))
      have hcode_s_core : Devm.getCode s = Devm.getCode corePre :=
        hcode_s_sl.trans
          ((funext (fun a => getCode_eq_of_state_eq hmaxPop.state a)).trans
            ((funext (fun a => getCode_eq_of_state_eq hmaxBurn.state a)).trans
              ((Line.of_inv Devm.getCode (by line_inv) hpops).trans
                (funext (fun a =>
                  getCode_eq_of_state_eq hcallBurn.state a)))))
      have hlogs_s_core : s.logs = corePre.logs :=
        hlogs_s_sl.trans
          (hmaxPop.logs.trans (hmaxBurn.logs.trans
            ((Line.of_inv Devm.logs (by line_inv) hpops).trans
              hcallBurn.logs)))
      have houtput_s_core : s.output = corePre.output :=
        houtput_s_sl.trans
          (hmaxPop.output.trans (hmaxBurn.output.trans
            ((Line.of_inv Devm.output (by line_inv) hpops).trans
              hcallBurn.output)))
      have hmemory_sk_core : sk.memory = corePre.memory :=
        hmemory_sk_sl.trans
          (hmaxPop.memory.trans (hmaxBurn.memory.trans
            ((Line.of_inv Devm.memory (by line_inv) hpops).trans
              hcallBurn.memory)))
      refine ⟨corePre, hcore, ?_, ?_, ?_⟩
      · unfold CallerAllowanceOutcome
        exact ⟨Or.inr ⟨hnonselfWord, Or.inl
          ⟨hallowance.trans hallowanceMax,
            congrFun hstor_s_core e.currentTarget |>.symm,
            hlogs_s_core.symm⟩⟩,
          houtput_s_core.symm, hbal_s_core.symm, hcode_s_core.symm⟩
      · rw [← hmemory_sk_core]
        exact hwfKey
      · rw [← hmemory_sk_core]
        exact ⟨out, hreadsKey⟩
  · have houterStack := houterPop.stack
    simp only [Stack.Pop, Split, List.nil_append,
      List.cons_append] at houterStack
    rw [houterStack] at hp1
    have hflagEq : (e.caller.toB256 =? Sevm.argWord e 0) = wself :=
      pref_head_unique hp1 (pref_append [wself] s2.stack)
    have hselfWord : Sevm.argWord e 0 = e.caller.toB256 := by
      apply Eq.symm
      by_contra hne
      rw [B256.eqCheck, if_neg hne] at hflagEq
      exact hnzself hflagEq.symm
    rcases of_run_call hself with
      ⟨f, corePre, hget, hcallBurn, hcore⟩
    have hf : f = core := by
      rw [hnext] at hget
      exact Option.some.inj hget.symm
    subst f
    have hstor_s_core : Devm.getStor s = Devm.getStor corePre :=
      hstor_s_s1.trans
        ((PopBurn.Inv.inv houterPop).trans
          ((Burn.Inv.inv houterBurn).trans (Burn.Inv.inv hcallBurn)))
    have hbal_s_core : Devm.getBal s = Devm.getBal corePre :=
      hbal_s_s1.trans
        ((PopBurn.Inv.inv houterPop).trans
          ((Burn.Inv.inv houterBurn).trans (Burn.Inv.inv hcallBurn)))
    have hcode_s_core : Devm.getCode s = Devm.getCode corePre :=
      hcode_s_s1.trans
        ((funext (fun a => getCode_eq_of_state_eq houterPop.state a)).trans
          ((funext (fun a => getCode_eq_of_state_eq houterBurn.state a)).trans
            (funext (fun a =>
              getCode_eq_of_state_eq hcallBurn.state a))))
    have hlogs_s_core : s.logs = corePre.logs :=
      hlogs_s_s1.trans
        (houterPop.logs.trans (houterBurn.logs.trans hcallBurn.logs))
    have houtput_s_core : s.output = corePre.output :=
      houtput_s_s1.trans
        (houterPop.output.trans (houterBurn.output.trans hcallBurn.output))
    have hmemory_s_core : s.memory = corePre.memory :=
      hmemory_s_s1.trans
        (houterPop.memory.trans (houterBurn.memory.trans hcallBurn.memory))
    refine ⟨corePre, hcore, ?_, ?_, ?_⟩
    · unfold CallerAllowanceOutcome
      exact ⟨Or.inl ⟨hselfWord,
        congrFun hstor_s_core e.currentTarget |>.symm,
        hlogs_s_core.symm⟩,
        houtput_s_core.symm, hbal_s_core.symm, hcode_s_core.symm⟩
    · rw [← hmemory_s_core]
      exact h_wf
    · rw [← hmemory_s_core]
      exact ⟨img, h_reads⟩

def TransferFromSuccessEffect (e : Sevm) (pre post : Devm) : Prop :=
  ∃ corePre,
    CallerAllowanceOutcome e pre corePre 2 ∧
    TransferFromCoreSuccessEffect e corePre post

def WithdrawFromSuccessEffect (e : Sevm) (pre post : Devm) : Prop :=
  ∃ corePre,
    CallerAllowanceOutcome e pre corePre 2 ∧
    BurnStopEffect e corePre post (normalizedAddressArg e 0).toAdr
      (Sevm.argWord e 2) (Sevm.argWord e 1)

theorem transferFrom_successEffect (dp : DeployParams)
    {e : Sevm} {s r : Devm} {img : Bytes}
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      transferFrom r) :
    TransferFromSuccessEffect e s r := by
  have hlookup :
      ((weth10 dp).main :: weth10Aux)[transferFromCoreSlot]? =
        some transferFromCore := by
    simp [weth10, weth10Aux, transferFromCoreSlot]
  obtain ⟨corePre, hcore, hallowance, hwfCore,
      out, hreadsCore⟩ :=
    of_spendCallerAllowanceThen_effect dp 2 transferFromCoreSlot
      transferFromCore hlookup h_wf h_reads (by
        simpa only [transferFrom] using run)
  exact ⟨corePre, hallowance,
    transferFromCore_successEffect dp hwfCore hreadsCore hcore⟩

theorem withdrawFrom_successEffect (dp : DeployParams)
    {e : Sevm} {s r : Devm} {img : Bytes}
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      withdrawFrom r) :
    WithdrawFromSuccessEffect e s r := by
  have hlookup :
      ((weth10 dp).main :: weth10Aux)[withdrawFromCoreSlot]? =
        some withdrawFromCore := by
    simp [weth10, weth10Aux, withdrawFromCoreSlot]
  obtain ⟨corePre, hcore, hallowance, hwfCore,
      out, hreadsCore⟩ :=
    of_spendCallerAllowanceThen_effect dp 2 withdrawFromCoreSlot
      withdrawFromCore hlookup h_wf h_reads (by
        simpa only [withdrawFrom] using run)
  exact ⟨corePre, hallowance,
    withdrawFromCore_effect dp hwfCore hreadsCore hcore⟩

theorem CallerAllowanceOutcome.of_entry_eq
    {e : Sevm} {pre pre' corePre : Devm} {amountArg : B256}
    (hstor : Devm.getStor pre' = Devm.getStor pre)
    (hbal : Devm.getBal pre' = Devm.getBal pre)
    (hcode : Devm.getCode pre' = Devm.getCode pre)
    (hlogs : pre'.logs = pre.logs)
    (houtput : pre'.output = pre.output)
    (h : CallerAllowanceOutcome e pre corePre amountArg) :
    CallerAllowanceOutcome e pre' corePre amountArg := by
  unfold CallerAllowanceOutcome at h ⊢
  simpa only [congrFun hstor e.currentTarget, hbal, hcode,
    hlogs, houtput] using h

theorem TransferFromSuccessEffect.of_entry_eq
    {e : Sevm} {pre pre' post : Devm}
    (hstor : Devm.getStor pre' = Devm.getStor pre)
    (hbal : Devm.getBal pre' = Devm.getBal pre)
    (hcode : Devm.getCode pre' = Devm.getCode pre)
    (hlogs : pre'.logs = pre.logs)
    (houtput : pre'.output = pre.output)
    (h : TransferFromSuccessEffect e pre post) :
    TransferFromSuccessEffect e pre' post := by
  rcases h with ⟨corePre, hallowance, hcore⟩
  exact ⟨corePre,
    hallowance.of_entry_eq hstor hbal hcode hlogs houtput, hcore⟩

theorem WithdrawFromSuccessEffect.of_entry_eq
    {e : Sevm} {pre pre' post : Devm}
    (hstor : Devm.getStor pre' = Devm.getStor pre)
    (hbal : Devm.getBal pre' = Devm.getBal pre)
    (hcode : Devm.getCode pre' = Devm.getCode pre)
    (hlogs : pre'.logs = pre.logs)
    (houtput : pre'.output = pre.output)
    (h : WithdrawFromSuccessEffect e pre post) :
    WithdrawFromSuccessEffect e pre' post := by
  rcases h with ⟨corePre, hallowance, hcore⟩
  exact ⟨corePre,
    hallowance.of_entry_eq hstor hbal hcode hlogs houtput, hcore⟩

/-- Compiled public `transferFrom(address,address,uint256)`: exact self/max/
finite allowance fork followed by the raw-recipient burn/storage-transfer fork. -/
theorem weth10_transferFrom_successEffect (dp : DeployParams)
    {e : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 e pre (.ok post))
    (h_code : some e.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector e =
      selector "transferFrom" [.address, .address, .uint256])
    (h_nonempty : e.data.length.toB256 ≠ 0) :
    e.value = 0 ∧ TransferFromSuccessEffect e pre post := by
  have h_mem :
      (selector "transferFrom" [.address, .address, .uint256],
        nonpayable transferFrom) ∈ weth10Funcs dp := by
    simp [weth10Funcs]
  rcases exec_enters_weth10Nonpayable_logs
      exc h_code h_sel h_nonempty h_mem with
    ⟨mid, hvalue, hstor, hbal, hcode, hmemory,
      hlogs, houtput, hbody⟩
  have hwfMid : Mem.Wf mid.memory := by
    rw [hmemory]
    exact h_wf
  have hreadsMid : Mem.Reads mid.memory img := by
    rw [hmemory]
    exact h_reads
  have heffect := transferFrom_successEffect dp hwfMid hreadsMid hbody
  exact ⟨hvalue, heffect.of_entry_eq hstor.symm hbal.symm
    hcode.symm hlogs.symm houtput.symm⟩

/-- Compiled public `withdrawFrom(address,address,uint256)`: exact self/max/
finite allowance fork, normalized source burn, raw CALL target, and `STOP`. -/
theorem weth10_withdrawFrom_successEffect (dp : DeployParams)
    {e : Sevm} {pre post : Devm} {img : Bytes}
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 e pre (.ok post))
    (h_code : some e.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector e =
      selector "withdrawFrom" [.address, .address, .uint256])
    (h_nonempty : e.data.length.toB256 ≠ 0) :
    e.value = 0 ∧ WithdrawFromSuccessEffect e pre post := by
  have h_mem :
      (selector "withdrawFrom" [.address, .address, .uint256],
        nonpayable withdrawFrom) ∈ weth10Funcs dp := by
    simp [weth10Funcs]
  rcases exec_enters_weth10Nonpayable_logs
      exc h_code h_sel h_nonempty h_mem with
    ⟨mid, hvalue, hstor, hbal, hcode, hmemory,
      hlogs, houtput, hbody⟩
  have hwfMid : Mem.Wf mid.memory := by
    rw [hmemory]
    exact h_wf
  have hreadsMid : Mem.Reads mid.memory img := by
    rw [hmemory]
    exact h_reads
  have heffect := withdrawFrom_successEffect dp hwfMid hreadsMid hbody
  exact ⟨hvalue, heffect.of_entry_eq hstor.symm hbal.symm
    hcode.symm hlogs.symm houtput.symm⟩

/-! ## Failure-order audit links -/

theorem transfer_effect_failureOrder :
    lockedGuardChain (transferZeroThen returnTrue) =
        [burnBalanceErrorSlot, ethTransferErrorSlot] ++
          lockedGuardChain returnTrue ∧
    lockedGuardChain (transferNonzeroThen returnTrue) =
        [transferBalanceErrorSlot] ++ lockedGuardChain returnTrue :=
  transfer_lockedGuardOrder returnTrue

theorem transferFrom_effect_failureOrder :
    lockedGuardChain transferFromZero =
        [burnBalanceErrorSlot, ethTransferErrorSlot] ∧
    lockedGuardChain transferFromNonzero = [transferBalanceErrorSlot] :=
  transferFromCore_lockedGuardOrder

theorem withdrawal_effect_failureOrder :
    lockedGuardChain withdraw =
        [burnBalanceErrorSlot, ethTransferErrorSlot] ∧
    lockedGuardChain withdrawTo =
        [burnBalanceErrorSlot, ethTransferErrorSlot] ∧
    lockedGuardChain withdrawFromCore =
        [burnBalanceErrorSlot, etherTransferErrorSlot] :=
  withdraw_lockedGuardOrder

theorem delegatedAllowance_effect_precedence (nextSlot : Nat) :
    ∃ finite,
      spendCallerAllowanceThen 2 nextSlot =
        (arg 0 +++ caller ::: eq :::
          (.call nextSlot) <?>
          (arg 0 +++ mstoreAt 0 +++ caller ::: mstoreAt 1 +++
            allowanceKeyFromMemory +++ dup 0 ::: sload ::: dup 0 ::: isMax +++
            (pop ::: pop ::: .call nextSlot) <?> finite)) ∧
      finite =
        (arg 2 +++ swap 0 ::: balanceTooSmall +++
          (.call allowanceErrorSlot) <?>
          (sub ::: dup 0 ::: swap 1 ::: sstore :::
            arg 0 +++ swap 0 ::: caller ::: emitApproval +++
            pop ::: pop ::: .call nextSlot)) :=
  spendCallerAllowanceThen_finitePrecedence 2 nextSlot

end Weth10

end Blanc
