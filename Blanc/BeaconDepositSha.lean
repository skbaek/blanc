import Blanc.BeaconDeposit
import Blanc.ForwardSha256
import Blanc.StaticPrecompileMessage

/-!
# Beacon deposit SHA-256 wrapper carrier

The executable contract's `sha64` helper performs one warm call to the SHA-256
precompile and then checks both the status word and the returned byte count.
This module exposes the successful path with exact gas and the digest, storage,
log, output, and error facts needed by its continuations.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- Exact successful cost of the contract's `sha64` wrapper.

The fixed suffix costs 223 gas: `GAS` costs 2, the warm SHA-256 crossing 184,
`ISZERO` 3, the two untaken-branch frames 13 each, and the returndata-length
guard 8.  The remaining cost is the five argument pushes.
-/
def sha64SuccessCost (inputWord outputWord : B256) : Nat :=
  pushCost ((32 : B256).toBytes.sig) +
  pushCost ((outputWord * 32).toBytes.sig) +
  pushCost ((64 : B256).toBytes.sig) +
  pushCost ((inputWord * 32).toBytes.sig) +
  pushCost ((2 : B256).toBytes.sig) + 223

private theorem sha64_success_suffix_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {K : Nat}
    {stack : List B256} {success : Func} {ex : Execution}
    (h_ge : (Nat.toB256 base.returnData.length <? (32 : B256)) = 0)
    (h_tail : Func.RunCompiledTo fs sevm
      (base.setMach ⟨stack, base.memory, K⟩) success ex)
    (h_room : stack.length < 1019) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨1 :: stack, base.memory, K + 37⟩)
      (iszero :::
        (.call bubbleRevertSlot) <?>
        (returnDataShorterThan 32 +++
          ((.call emptyRevertSlot) <?> success))) ex := by
  func_run (6) [0, 0]
  all_goals try {
    simp only [Devm.stack_setMach, List.length_cons] at *
    omega }
  all_goals try omega
  simpa only [Devm.memory_setMach, Nat.add_sub_cancel] using h_tail

/-- Run the argument prefix, warm SHA-256 call, and successful decoder guards
with an exact selected memory-expansion charge.

The returned `callPost` is the state immediately after `STATICCALL`; the last
field turns any exact-gas continuation from the post-guard state into a run of
the complete `sha64` wrapper.  Keeping the call state visible lets downstream
fold proofs consume the digest and preservation facts without re-opening the
precompile semantics.
-/
theorem sha64_success_prefix_runCompiledTo_ext
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {inputWord outputWord : B256} {stack : List B256}
    {success : Func} {K ext : Nat}
    (hext : base.extCost
      [⟨(inputWord * 32).toNat, 64⟩,
        ⟨(outputWord * 32).toNat, 32⟩] = ext)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : K + 221 + ext < 2 ^ 256)
    (hroom : stack.length < 1019) :
    ∃ callPost,
      callPost.stack = 1 :: stack ∧
      callPost.memory = (base.memory.extends
        [⟨(inputWord * 32).toNat, 64⟩,
          ⟨(outputWord * 32).toNat, 32⟩]).write
        (outputWord * 32).toNat
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes ∧
      callPost.gasLeft = K + 37 ∧
      callPost.returnData =
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes ∧
      (∀ a, Devm.getStor callPost a = Devm.getStor base a) ∧
      (∀ a, callPost.getCode a = base.getCode a) ∧
      callPost.accessedAddresses = base.accessedAddresses ∧
      callPost.accessedStorageKeys = base.accessedStorageKeys ∧
      callPost.logs = base.logs ∧
      callPost.output = base.output ∧
      callPost.error = base.error ∧
      (∃ stmid,
        base.state.subBal sevm.currentTarget 0 = some stmid ∧
        callPost.state = stmid.addBal 2 0) ∧
      ∀ {ex : Execution},
        Func.RunCompiledTo fs sevm
          (callPost.setMach ⟨stack, callPost.memory, K⟩) success ex →
        Func.RunCompiledTo fs sevm
          (base.setMach
            ⟨stack, base.memory,
              K + sha64SuccessCost inputWord outputWord + ext⟩)
          (sha64 inputWord outputWord success) ex := by
  let callPre := base.setMach
    ⟨Nat.toB256 (K + 221 + ext) :: (2 : B256) ::
      (inputWord * 32) :: (64 : B256) ::
      (outputWord * 32) :: (32 : B256) :: stack,
      base.memory, K + 221 + ext⟩
  obtain ⟨callPost, hstat, hstack, hmemory, hgas, hreturn,
      hstorage, hcode, haddresses, hkeys,
      hlogs, houtput, herror, stmid, hsub, hstate⟩ :=
    Ninst.runCompiled_staticcall_sha256_64_warm_ext
      (sevm := sevm) (devm := callPre)
      (iiw := inputWord * 32) (oiw := outputWord * 32)
      (s := stack) (G := K + 221 + ext) (ext := ext)
      (by simp only [callPre, Devm.stack_setMach])
      (by simp only [callPre, Devm.gasLeft_setMach])
      (by
        simpa only [callPre, Devm.extCost, Devm.memory_setMach] using hext)
      (by simpa only [callPre, Devm.getCode_setMach] using hnodeleg)
      (by
        change (2 : Adr) ∈ base.accessedAddresses
        exact hwarm)
      hpre hdepth (by omega) hbound (by omega)
  have hgas' : callPost.gasLeft = K + 37 := by omega
  have hmemory' :
      callPost.memory = (base.memory.extends
        [⟨(inputWord * 32).toNat, 64⟩,
          ⟨(outputWord * 32).toNat, 32⟩]).write
        (outputWord * 32).toNat
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes := by
    simpa only [callPre, Devm.memory_setMach] using hmemory
  have hreturn' :
      callPost.returnData =
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes := by
    simpa only [callPre, Devm.memory_setMach] using hreturn
  have hstorage' : ∀ a,
      Devm.getStor callPost a = Devm.getStor base a := by
    intro a
    calc
      Devm.getStor callPost a = Devm.getStor callPre a := hstorage a
      _ = Devm.getStor base a := by rfl
  have hcode' : ∀ a, callPost.getCode a = base.getCode a := by
    intro a
    calc
      callPost.getCode a = callPre.getCode a := hcode a
      _ = base.getCode a := by rfl
  have haddresses' :
      callPost.accessedAddresses = base.accessedAddresses := by
    calc
      callPost.accessedAddresses = callPre.accessedAddresses := haddresses
      _ = base.accessedAddresses := by rfl
  have hkeys' :
      callPost.accessedStorageKeys = base.accessedStorageKeys := by
    calc
      callPost.accessedStorageKeys = callPre.accessedStorageKeys := hkeys
      _ = base.accessedStorageKeys := by rfl
  have hlogs' : callPost.logs = base.logs := by
    calc
      callPost.logs = callPre.logs := hlogs
      _ = base.logs := by rfl
  have houtput' : callPost.output = base.output := by
    calc
      callPost.output = callPre.output := houtput
      _ = base.output := by rfl
  have herror' : callPost.error = base.error := by
    calc
      callPost.error = callPre.error := herror
      _ = base.error := by rfl
  have hsub' : base.state.subBal sevm.currentTarget 0 = some stmid := by
    change base.state.subBal sevm.currentTarget 0 = some stmid at hsub
    exact hsub
  refine ⟨callPost, hstack, hmemory', hgas', hreturn',
    hstorage', hcode', haddresses', hkeys',
    hlogs', houtput', herror', ⟨stmid, hsub', hstate⟩, ?_⟩
  intro ex htail
  have hge :
      (Nat.toB256 callPost.returnData.length <? (32 : B256)) = 0 := by
    rw [hreturn', B256.length_toBytes]
    decide +kernel
  have hsuffix : Func.RunCompiledTo fs sevm
      (callPost.setMach ⟨1 :: stack, callPost.memory, K + 37⟩)
      (iszero :::
        (.call bubbleRevertSlot) <?>
        (returnDataShorterThan 32 +++
          ((.call emptyRevertSlot) <?> success))) ex :=
    sha64_success_suffix_runCompiledTo hge htail hroom
  let c32 := pushCost ((32 : B256).toBytes.sig)
  let cout := pushCost ((outputWord * 32).toBytes.sig)
  let c64 := pushCost ((64 : B256).toBytes.sig)
  let cin := pushCost ((inputWord * 32).toBytes.sig)
  let c2 := pushCost ((2 : B256).toBytes.sig)
  simp only [sha64, pushList, List.map, prepend]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (sevm := sevm)
      (devm := base.setMach
        ⟨stack, base.memory,
          K + sha64SuccessCost inputWord outputWord + ext⟩)
      (w := (32 : B256)) (c := c32)
      (G := K + (cout + c64 + cin + c2 + 223) + ext)
      (by rfl)
      (by
        simp only [Devm.gasLeft_setMach, sha64SuccessCost,
          c32, cout, c64, cin, c2]
        omega)
      (by simp only [Devm.stack_setMach]; omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := outputWord * 32) (c := cout)
      (G := K + (c64 + cin + c2 + 223) + ext)
      (by rfl)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by
        simp only [Devm.stack_setMach, List.length_cons]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := (64 : B256)) (c := c64)
      (G := K + (cin + c2 + 223) + ext)
      (by rfl)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by
        simp only [Devm.stack_setMach, List.length_cons]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := inputWord * 32) (c := cin)
      (G := K + (c2 + 223) + ext)
      (by rfl)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by
        simp only [Devm.stack_setMach, List.length_cons]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := (2 : B256)) (c := c2)
      (G := K + 223 + ext)
      (by rfl)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by
        simp only [Devm.stack_setMach, List.length_cons]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_gas
      (G := K + 221 + ext)
      (by simp only [Devm.gasLeft_setMach, gBase]; omega)
      (by
        simp only [Devm.stack_setMach, List.length_cons]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next ?_ hsuffix
  have hpost :
      callPost.setMach
        ⟨1 :: stack, callPost.memory, K + 37⟩ = callPost := by
    apply Devm.ext
    · apply Mach.ext
      · exact hstack.symm
      · rfl
      · exact hgas'.symm
    · rfl
    · rfl
  rw [hpost]
  simpa only [callPre, Devm.stack_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach] using hstat

/-- Covered-memory compatibility form of
`sha64_success_prefix_runCompiledTo_ext`. -/
theorem sha64_success_prefix_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {inputWord outputWord : B256} {stack : List B256}
    {success : Func} {K : Nat}
    (hcovered : memExtsSize base.memory.size
      [⟨(inputWord * 32).toNat, 64⟩,
        ⟨(outputWord * 32).toNat, 32⟩] = base.memory.size)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : K + 221 < 2 ^ 256)
    (hroom : stack.length < 1019) :
    ∃ callPost,
      callPost.stack = 1 :: stack ∧
      callPost.memory = base.memory.write (outputWord * 32).toNat
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes ∧
      callPost.gasLeft = K + 37 ∧
      callPost.returnData =
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes ∧
      (∀ a, Devm.getStor callPost a = Devm.getStor base a) ∧
      (∀ a, callPost.getCode a = base.getCode a) ∧
      callPost.accessedAddresses = base.accessedAddresses ∧
      callPost.accessedStorageKeys = base.accessedStorageKeys ∧
      callPost.logs = base.logs ∧
      callPost.output = base.output ∧
      callPost.error = base.error ∧
      (∃ stmid,
        base.state.subBal sevm.currentTarget 0 = some stmid ∧
        callPost.state = stmid.addBal 2 0) ∧
      ∀ {ex : Execution},
        Func.RunCompiledTo fs sevm
          (callPost.setMach ⟨stack, callPost.memory, K⟩) success ex →
        Func.RunCompiledTo fs sevm
          (base.setMach
            ⟨stack, base.memory,
              K + sha64SuccessCost inputWord outputWord⟩)
          (sha64 inputWord outputWord success) ex := by
  have hext : base.extCost
      [⟨(inputWord * 32).toNat, 64⟩,
        ⟨(outputWord * 32).toNat, 32⟩] = 0 := by
    simp only [Devm.extCost, hcovered]
    omega
  simpa only [Nat.add_zero, Mem.extends_covered hcovered] using
    (sha64_success_prefix_runCompiledTo_ext
      (ext := 0) hext hnodeleg hwarm hpre hdepth (by simpa using hbound) hroom)

/-! ## Source-level successful-run inversion -/

/-- Invert a successful source-level `sha64` walk.  The actual `STATICCALL`
must have entered the native address-2 precompile: its failure arm bubbles and
its short-output arm reverts, so neither can occur in a successful walk.  The
returned continuation state carries the exact digest write while preserving
storage and code. -/
theorem sha64_success_of_run
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    {inputWord outputWord : B256} {xs : Stack} {success : Func}
    (hbubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (hrev : fs[emptyRevertSlot]? = some Func.revert)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hnodeleg : getDelegatedCodeAddress (s.getCode 2) = none)
    (hp : xs <<+ s.stack)
    (run : Func.Run fs sevm s (sha64 inputWord outputWord success) r) :
    ∃ q,
      xs <<+ q.stack ∧
      Func.Run fs sevm q success r ∧
      q.memory =
        (s.memory.extends
          [⟨(inputWord * 32).toNat, 64⟩,
            ⟨(outputWord * 32).toNat, 32⟩]).write
          (outputWord * 32).toNat
          (Bytes.sha256 (s.memory.read (inputWord * 32).toNat 64).1).toBytes ∧
      q.returnData =
        (Bytes.sha256 (s.memory.read (inputWord * 32).toNat 64).1).toBytes ∧
      Devm.getStor q = Devm.getStor s ∧
      Devm.getCode q = Devm.getCode s := by
  unfold sha64 at run
  rcases of_run_prepend
      (pushList [32, outputWord * 32, 64, inputWord * 32, 2]) _ run with
    ⟨p, hpushLine, run⟩
  have hpushFrameStor : Devm.getStor s = Devm.getStor p :=
    Line.of_inv Devm.getStor (by unfold pushList; line_inv) hpushLine
  have hpushFrameCode : Devm.getCode s = Devm.getCode p :=
    Line.of_inv Devm.getCode (by unfold pushList; line_inv) hpushLine
  have hpushFrameMem : s.memory = p.memory :=
    Line.of_inv Devm.memory (by unfold pushList; line_inv) hpushLine
  have hpl := hpushLine
  simp only [pushList, List.map] at hpl
  rcases Line.of_run_cons hpl with ⟨p1, q1, hpl⟩
  have hp1 := prefix_of_push (of_run_pushB256 q1) hp
  rcases Line.of_run_cons hpl with ⟨p2, q2, hpl⟩
  have hp2 := prefix_of_push (of_run_pushB256 q2) hp1
  rcases Line.of_run_cons hpl with ⟨p3, q3, hpl⟩
  have hp3 := prefix_of_push (of_run_pushB256 q3) hp2
  rcases Line.of_run_cons hpl with ⟨p4, q4, hpl⟩
  have hp4 := prefix_of_push (of_run_pushB256 q4) hp3
  rcases Line.of_run_cons hpl with ⟨p5, q5, hnil⟩
  cases hnil
  have hp5 := prefix_of_push (of_run_pushB256 q5) hp4
  rcases of_run_next run with ⟨callPre, qgas, run⟩
  rcases of_run_gas qgas with ⟨g, hgas⟩
  have hpCall :
      g :: (2 : B256) :: inputWord * 32 :: (64 : B256) ::
        outputWord * 32 :: (32 : B256) :: xs <<+ callPre.stack :=
    prefix_of_push hgas hp5
  have hstorCall : Devm.getStor callPre = Devm.getStor s := by
    exact ((hpushFrameStor.trans
      (Ninst.Hinv.inv (f := Devm.getStor) qgas))).symm
  have hcodeCall : Devm.getCode callPre = Devm.getCode s := by
    exact ((hpushFrameCode.trans
      (Ninst.Hinv.inv (f := Devm.getCode) qgas))).symm
  have hmemCall : callPre.memory = s.memory := by
    exact ((hpushFrameMem.trans
      (Ninst.Hinv.inv (f := Devm.memory) qgas))).symm
  have hnodelegCall :
      getDelegatedCodeAddress (callPre.getCode 2) = none := by
    rw [congrFun hcodeCall 2]
    exact hnodeleg
  rcases of_run_next run with ⟨callPost, qstat, run⟩
  rcases of_run_staticcall_val_with_depth_cause hpCall qstat with
      hfail | hsuccess
  · rcases hfail with ⟨hpPost, hworld, out, hret, hmem, hcause⟩
    rcases of_run_next run with ⟨afterIszero, qiszero, run⟩
    have hpFlag := prefix_of_iszero qiszero hpPost
    rcases of_run_branch_call_revertReturnData hbubble run with
      ⟨afterBranch, hpop, hcontinue⟩
    have hpopStack := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
    rw [hpopStack] at hpFlag
    have hbad : (((0 : B256) =? 0) : B256) = 0 :=
      pref_head_unique hpFlag (pref_append [(0 : B256)] afterBranch.stack)
    rw [show (((0 : B256) =? 0) : B256) = 1 by simp [B256.eqCheck]] at hbad
    exact False.elim (B256.zero_ne_one hbad.symm)
  · rcases hsuccess with
      ⟨parent, child, xl, dp, na, code, avail,
        hdepth, hstack, hstate, hmemory, hparentLogs, hparentOutput,
        hdel, hfill, hpm, hclean, hresume, hpostState, hpostRet,
        hpostMemory, hpostStack⟩
    rcases hdel with
      ⟨hnd, hna, hcode, hdp⟩ | ⟨d, hsome, hna, hcode, hdp⟩
    · subst na
      subst dp
      have hlen :
          (callPre.memory.read (inputWord * 32).toNat 64).1.length = 64 := by
        change
          (callPre.memory.data.sliceD (inputWord * 32).toNat 64 0).length = 64
        rw [Array.sliceD_eq_map, List.length_map, List.length_range]
      have hframe := frame_of_processMessage_sha256_64_clean
        hpre hlen hpm hclean
      have hchildStor := hframe.1
      have hchildOut := hframe.2
      have hchildCode := code_of_processMessage_staticPrecomp hpre hpm
      have hpParent : xs <<+ parent.stack := by
        rw [hstack] at hpCall
        exact cons_pref_cons_inv (cons_pref_cons_inv (cons_pref_cons_inv
          (cons_pref_cons_inv (cons_pref_cons_inv
            (cons_pref_cons_inv hpCall)))))
      have hpPost : (1 : B256) :: xs <<+ callPost.stack := by
        rw [hpostStack]
        exact pref_cons hpParent
      have hstorPost : Devm.getStor callPost = Devm.getStor s := by
        funext a
        calc
          Devm.getStor callPost a = Devm.getStor child a :=
            getStor_eq_of_state_eq hpostState a
          _ = Devm.getStor parent a := hchildStor a
          _ = Devm.getStor callPre a := getStor_eq_of_state_eq hstate a
          _ = Devm.getStor s a := congrFun hstorCall a
      have hcodePost : Devm.getCode callPost = Devm.getCode s := by
        funext a
        calc
          Devm.getCode callPost a = Devm.getCode child a :=
            getCode_eq_of_state_eq hpostState a
          _ = Devm.getCode parent a := hchildCode a
          _ = Devm.getCode callPre a := getCode_eq_of_state_eq hstate a
          _ = Devm.getCode s a := congrFun hcodeCall a
      have hretPost : callPost.returnData =
          (Bytes.sha256
            (s.memory.read (inputWord * 32).toNat 64).1).toBytes := by
        rw [hpostRet, hchildOut, hmemCall]
      have hmemPost : callPost.memory =
          (s.memory.extends
            [⟨(inputWord * 32).toNat, 64⟩,
              ⟨(outputWord * 32).toNat, 32⟩]).write
            (outputWord * 32).toNat
            (Bytes.sha256
              (s.memory.read (inputWord * 32).toNat 64).1).toBytes := by
        rw [hpostMemory, hmemory, hchildOut, hmemCall]
        simp only [show ((64 : B256).toNat) = 64 by decide +kernel,
          show ((32 : B256).toNat) = 32 by decide +kernel]
        rw [List.take_of_length_le]
        rw [B256.length_toBytes]
      rcases of_run_next run with ⟨afterIszero, qiszero, run⟩
      have hpFlag := prefix_of_iszero qiszero hpPost
      obtain ⟨iszeroWord, hdbIszero⟩ :
          ∃ w, Devm.DiffBurn [w] [w =? 0] callPost afterIszero := by
        rcases of_run_reg qiszero with ⟨pc, hreg⟩
        simp only [Rinst.run, Rinst.runCore] at hreg
        exact Devm.diffBurn_of_applyUnary hreg
      rcases of_run_branch_call_revertReturnData hbubble run with
        ⟨afterBranch, hpop, run⟩
      have hpopStack := hpop.stack
      simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
      rw [hpopStack] at hpFlag
      have hflag : (((1 : B256) =? 0) : B256) = 0 :=
        pref_head_unique hpFlag (pref_append [(0 : B256)] afterBranch.stack)
      rw [hflag] at hpFlag
      have hpBranch : xs <<+ afterBranch.stack := cons_pref_cons_inv hpFlag
      have hstorBranch : Devm.getStor afterBranch = Devm.getStor s := by
        rw [← hstorPost]
        funext a
        exact (getStor_eq_of_state_eq
          (hdbIszero.state.trans hpop.state) a).symm
      have hcodeBranch : Devm.getCode afterBranch = Devm.getCode s := by
        rw [← hcodePost]
        funext a
        exact (getCode_eq_of_state_eq
          (hdbIszero.state.trans hpop.state) a).symm
      have hmemBranch : afterBranch.memory = callPost.memory :=
        ((Ninst.Hinv.inv (f := Devm.memory) qiszero).trans hpop.memory).symm
      have hretBranch : afterBranch.returnData = callPost.returnData :=
        (hdbIszero.returnData.trans hpop.returnData).symm
      rcases of_run_prepend (returnDataShorterThan 32) _ run with
        ⟨afterShort, hshort, run⟩
      rcases of_returnDataShorterThan_val hpBranch hshort with
        ⟨hpShort, hmemShort, hretShort⟩
      rcases of_run_branch_call_revert hrev run with
        ⟨q, hpopShort, hsuccess⟩
      have hpopShortStack := hpopShort.stack
      simp only [Stack.Pop, Split, List.nil_append,
        List.cons_append] at hpopShortStack
      rw [hpopShortStack] at hpShort
      have hshortFlag :
          (afterBranch.returnData.length.toB256 <? (32 : B256)) = 0 :=
        pref_head_unique hpShort (pref_append [(0 : B256)] q.stack)
      have hshortZero :
          (afterBranch.returnData.length.toB256 <? (32 : B256)) = 0 := by
        rw [hretBranch, hretPost, B256.length_toBytes]
        decide +kernel
      rw [hshortZero] at hpShort
      have hpQ : xs <<+ q.stack := cons_pref_cons_inv hpShort
      refine ⟨q, hpQ, hsuccess, ?_, ?_, ?_, ?_⟩
      · rw [← hmemPost]
        exact hpopShort.memory.symm.trans
          (hmemShort.trans hmemBranch)
      · rw [← hretPost]
        exact hpopShort.returnData.symm.trans
          (hretShort.trans hretBranch)
      · rw [← hstorBranch]
        funext a
        exact (getStor_eq_of_state_eq hpopShort.state a).symm.trans
          (congrFun (Line.of_inv Devm.getStor (by
            unfold returnDataShorterThan
            line_inv) hshort) a).symm
      · rw [← hcodeBranch]
        funext a
        exact (getCode_eq_of_state_eq hpopShort.state a).symm.trans
          (congrFun (Line.of_inv Devm.getCode (by
            unfold returnDataShorterThan
            line_inv) hshort) a).symm
    · change getDelegatedCodeAddress (callPre.getCode 2) = some d at hsome
      rw [hnodelegCall] at hsome
      cases hsome

/-! ## Contract-site cost specializations -/

@[simp] theorem sha64SuccessCost_zero_node :
    sha64SuccessCost 0 nodeWord = 237 := by
  decide +kernel

@[simp] theorem sha64SuccessCost_zero_intermediate :
    sha64SuccessCost 0 intermediateWord = 237 := by
  decide +kernel

@[simp] theorem sha64SuccessCost_zero_secondIntermediate :
    sha64SuccessCost 0 secondIntermediateWord = 237 := by
  decide +kernel

@[simp] theorem sha64SuccessCost_six_node :
    sha64SuccessCost 6 nodeWord = 238 := by
  decide +kernel

@[simp] theorem sha64SuccessCost_thirteen_intermediate :
    sha64SuccessCost 13 intermediateWord = 238 := by
  decide +kernel

end Blanc.BeaconDeposit
