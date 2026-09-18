-- DripDeploy.lean : no-argument DRIP constructor and creation artifact.

import Blanc.CreationArtifact
import Blanc.DeploymentCompiled
import Blanc.DeploymentMessage
import Blanc.DripCode
import Blanc.ExecutionHistory
import Blanc.ForwardCall
import Blanc.Ladder
import Blanc.MessageExecution

/-!
# DRIP deployment source

The nonpayable constructor accepts no appended argument bytes, initializes
`chi` before `rho`, and returns the exact compiler-generated DRIP runtime.
Full-width creation coordinates make the provisional and final compiler passes
shape-identical without truncating a future artifact that outgrows PUSH2.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace Drip

/-- Full-width creation coordinates keep both compiler passes shape-identical. -/
def pushCreationCoordinate (value : Nat) : Ninst :=
  Ninst.push (Nat.toB256 value).toBytes (by rw [B256.length_toBytes])

/-- Strict no-argument body: initialize the two scalar words in frozen order,
copy the appended runtime, and return precisely that memory window. -/
def constructorBody
    (runtimeOffset argsOffset runtimeLength : Nat) : Func :=
  pushCreationCoordinate argsOffset ::: codesize ::: eq :::
  ((pushB256 scale ::: pushB256 chiSlot ::: sstore :::
      timestamp ::: pushB256 rhoSlot ::: sstore :::
      pushCreationCoordinate runtimeLength :::
      pushCreationCoordinate runtimeOffset :::
      pushB256 0 ::: codecopy :::
      pushCreationCoordinate runtimeLength :::
      pushB256 0 ::: Func.return_) <?>
    Func.revert)

/-- Layout-parametric constructor used for the provisional and final passes. -/
def constructorProgramAt
    (runtimeOffset argsOffset runtimeLength : Nat) : Prog :=
  { main := nonpayable
      (constructorBody runtimeOffset argsOffset runtimeLength)
    aux := [] }

private def provisionalConstructorPrefix : Bytes :=
  (Prog.compile (constructorProgramAt 0 0 code.length)).getD []

/-- Compiler-derived byte offset of the appended runtime. -/
def constructorRuntimeOffset : Nat :=
  provisionalConstructorPrefix.length

/-- Exact constructor source closed over the compiler-derived layout. -/
def constructorProgram : Prog :=
  CreationArtifact.finalizedConstructorProgram constructorProgramAt
    provisionalConstructorPrefix code

/-- Exact compiled constructor prefix. -/
def constructorInitPrefix : Bytes :=
  (Prog.compile constructorProgram).getD []

/-- Exact DRIP creation bytes: compiled prefix followed by the runtime literal. -/
def creationCode : Bytes :=
  constructorInitPrefix ++ code

def constructorCreationCode : Bytes := creationCode

def creationCodeSize : Nat := creationCode.length

def eip3860InitcodeLimit : Nat := pragueCodeLimits.maxInitCodeSize

def creationCodeHeadroom : Nat := eip3860InitcodeLimit - creationCodeSize

theorem constructorProgram_eq :
    constructorProgram =
      constructorProgramAt constructorRuntimeOffset
        (constructorRuntimeOffset + code.length) code.length := by
  simp only [constructorProgram,
    CreationArtifact.finalizedConstructorProgram, constructorRuntimeOffset]

theorem constructorProgram_compiles :
    Prog.compiles constructorProgram = true := by
  decide +kernel

theorem constructorInitPrefix_compile :
    Prog.compile constructorProgram = some constructorInitPrefix := by
  unfold constructorInitPrefix
  exact Prog.compile_eq_some_getD_of_compiles _ constructorProgram_compiles

/-- Fixed-width layout operands make the second-pass prefix a true fixed point. -/
theorem constructorInitPrefix_length_eq_runtimeOffset :
    constructorInitPrefix.length = constructorRuntimeOffset := by
  decide +kernel

theorem constructorRuntimeOffset_exact : constructorRuntimeOffset = 239 := by
  decide +kernel

theorem creationCode_eq_prefix_append_runtime :
    creationCode = constructorInitPrefix ++ code := by
  rfl

theorem constructorCreationCode_eq_creationCode :
    constructorCreationCode = creationCode := by
  rfl

theorem creationCode_drop_prefix :
    creationCode.drop constructorInitPrefix.length = code := by
  simp [creationCode]

theorem creationCode_drop_runtimeOffset :
    creationCode.drop constructorRuntimeOffset = code := by
  rw [← constructorInitPrefix_length_eq_runtimeOffset]
  exact creationCode_drop_prefix

/-- The constructor's CODECOPY window is exactly the appended runtime. -/
theorem creationCode_slice_runtime :
    creationCode.sliceD constructorRuntimeOffset codeSize 0 = code := by
  rw [← constructorInitPrefix_length_eq_runtimeOffset]
  unfold creationCode List.sliceD
  rw [List.drop_length_append' rfl]
  change List.takeD code.length code 0 = code
  rw [List.takeD_eq_take _ (by simp)]
  exact List.take_length

theorem eip3860InitcodeLimit_exact : eip3860InitcodeLimit = 49152 := by
  rfl

theorem creationCodeSize_exact : creationCodeSize = 2001 := by
  decide +kernel

theorem creationCode_eip3860 :
    creationCodeSize <= eip3860InitcodeLimit := by
  rw [creationCodeSize_exact, eip3860InitcodeLimit_exact]
  decide

theorem creationCodeHeadroom_exact : creationCodeHeadroom = 47151 := by
  unfold creationCodeHeadroom
  rw [eip3860InitcodeLimit_exact, creationCodeSize_exact]

/-! ## F4a: constructor source run

A successful source-level run of `constructorProgram.main` against the exact
creation code crosses the no-argument guard, initializes the two scalar words
in frozen order, copies the appended runtime, and returns exactly that
window.  `aux = []` and the body performs no `.call`, so no `AuxLookup`
is needed. -/

private theorem of_run_pushCreationCoordinate {e : Sevm} {s s' : Devm} {v : Nat}
    (h : Ninst.Run e s (pushCreationCoordinate v) s') :
    Devm.PushBurn [Nat.toB256 v] s s' := by
  unfold pushCreationCoordinate at h
  have h' := of_run_push h
  rwa [B256.toB256_toBytes] at h'

private theorem pushBurn_of_run_timestamp {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s Ninst.timestamp s') :
    Devm.PushBurn [e.benvStat.time] s s' := by
  change Ninst.Run e s (.reg .timestamp) s' at h
  rcases of_run_reg h with ⟨pc, hrun⟩
  simp only [Rinst.run, Rinst.runCore] at hrun
  exact Devm.pushBurn_of_pushItem hrun

private theorem getStor_of_state {s t : Devm} (h : s.state = t.state) :
    Devm.getStor s = Devm.getStor t := by
  funext a
  unfold Devm.getStor Devm.getAcct
  rw [h]

/-- Nonpayable peel retaining the stack tail for the constructor walk. -/
private theorem run_body_of_run_nonpayable_stack {fs : List Func} {sevm : Sevm}
    {s r : Devm} {body : Func} {tail : Stack}
    (hp : tail <<+ s.stack)
    (run : Func.Run fs sevm s (nonpayable body) r) :
    ∃ mid, sevm.value = 0 ∧ s.state = mid.state ∧ s.memory = mid.memory ∧
      tail <<+ mid.stack ∧ Func.Run fs sevm mid body r := by
  unfold nonpayable at run
  refine run_prepend_elim _ [callvalue, iszero] ?_ run
  intro s1 hline hbranch
  rcases Line.of_run_cons hline with ⟨s0, hcv, hline'⟩
  rcases Line.of_run_cons hline' with ⟨s1', hiz, hnil⟩
  cases hnil
  have hpv : sevm.value :: tail <<+ s0.stack :=
    prefix_of_push (of_run_callvalue hcv) hp
  have hpflag : (sevm.value =? 0) :: tail <<+ s1.stack :=
    prefix_of_iszero hiz hpv
  rcases of_run_branch hbranch with
    ⟨s2, hpop, hrev⟩ | ⟨w, s2, s3, hnz, hpop, hburn, hbody⟩
  · exact absurd hrev not_run_revert
  · obtain ⟨hw, htail2⟩ := popBurn_pref hpop hpflag
    have hflag : (sevm.value =? 0) ≠ 0 := by
      rw [← hw]
      exact hnz
    have hv : sevm.value = 0 := by
      by_cases hv : sevm.value = 0
      · exact hv
      · simp [B256.eqCheck, hv] at hflag
    have htail3 : tail <<+ s3.stack := by
      rw [← hburn.stack]
      exact htail2
    refine ⟨s3, hv, ?_, ?_, htail3, hbody⟩
    · exact (Line.of_inv Devm.state (by line_inv) hline).trans
        (hpop.state.trans hburn.state)
    · exact (Line.of_inv Devm.memory (by line_inv) hline).trans
        (hpop.memory.trans hburn.memory)

theorem of_run_constructorProgram_main {fs : List Func} {sevm : Sevm} {s r : Devm}
    {tail : Stack} {image : Bytes}
    (hp : tail <<+ s.stack)
    (hwf : Mem.Wf s.memory)
    (hreads : Mem.Reads s.memory image)
    (hcode : sevm.code.toList = creationCode)
    (run : Func.Run fs sevm s constructorProgram.main r) :
    sevm.value = 0 ∧
      Devm.getStor r sevm.currentTarget =
        ((Devm.getStor s sevm.currentTarget).set chiSlot scale).set rhoSlot
          sevm.benvStat.time ∧
      Devm.output r = code := by
  have hlen : code.length = 1762 := codeSize_exact
  have hsize : sevm.code.size = 2001 := by
    rw [ByteArray.size_eq_length_toList, hcode]
    exact creationCodeSize_exact
  have hRO239 : (Nat.toB256 239).toNat = 239 :=
    B256.toNat_toB256_of_lt (by decide)
  have hRL1762 : (Nat.toB256 1762).toNat = 1762 :=
    B256.toNat_toB256_of_lt (by decide)
  have hslice : sevm.code.sliceD (Nat.toB256 239).toNat (Nat.toB256 1762).toNat
      (Linst.toUInt8 .stop) = code := by
    rw [hRO239, hRL1762, ByteArray.sliceD_eq, hcode]
    have hstop : Linst.toUInt8 .stop = 0 := rfl
    rw [hstop, ← constructorRuntimeOffset_exact, ← codeSize_exact]
    exact creationCode_slice_runtime
  rw [constructorProgram_eq] at run
  simp only [constructorProgramAt] at run
  obtain ⟨mid, hv, hstate0, hmem0, hpmid, hbody⟩ :=
    run_body_of_run_nonpayable_stack hp run
  rw [constructorRuntimeOffset_exact, hlen] at hbody
  have hAO : (239 : Nat) + 1762 = 2001 := by decide
  rw [hAO] at hbody
  unfold constructorBody at hbody
  rcases of_run_next hbody with ⟨a1, hpushA, hbody⟩
  have hpA : Nat.toB256 2001 :: tail <<+ a1.stack :=
    prefix_of_push (of_run_pushCreationCoordinate hpushA) hpmid
  rcases of_run_next hbody with ⟨a2, hcodesize, hbody⟩
  have hpC : sevm.code.size.toB256 :: Nat.toB256 2001 :: tail <<+ a2.stack :=
    prefix_of_push (of_run_codesize hcodesize) hpA
  rcases of_run_next hbody with ⟨a3, heq, hbody⟩
  have hpF : (sevm.code.size.toB256 =? Nat.toB256 2001) :: tail <<+ a3.stack :=
    prefix_of_eq heq hpC
  rw [hsize] at hpF
  have hflag1 : (Nat.toB256 2001 =? Nat.toB256 2001) = 1 := by
    simp [B256.eqCheck]
  rw [hflag1] at hpF
  rcases of_run_branch hbody with
    ⟨_, _, hrev⟩ | ⟨_, b1, b2, _, hpop, hburn, hbody⟩
  · exact absurd hrev not_run_revert
  · obtain ⟨_, hpb1⟩ := popBurn_pref hpop hpF
    have hpb2 : tail <<+ b2.stack := by
      rw [← hburn.stack]
      exact hpb1
    rcases of_run_next hbody with ⟨c1, hpushS, hbody⟩
    have hpS : scale :: tail <<+ c1.stack :=
      prefix_of_push (of_run_pushB256 hpushS) hpb2
    rcases of_run_next hbody with ⟨c2, hpushC, hbody⟩
    have hpChi : chiSlot :: scale :: tail <<+ c2.stack :=
      prefix_of_push (of_run_pushB256 hpushC) hpS
    rcases of_run_next hbody with ⟨d1, hstore1, hbody⟩
    have hst_c2 : s.state = c2.state := by
      refine hstate0.trans ?_
      refine (of_run_pushCreationCoordinate hpushA).state.trans ?_
      refine (of_run_codesize hcodesize).state.trans ?_
      refine (Ninst.Hinv.inv (f := Devm.state) heq).trans ?_
      refine hpop.state.trans ?_
      refine hburn.state.trans ?_
      exact (of_run_pushB256 hpushS).state.trans
        (of_run_pushB256 hpushC).state
    have hstor1 : Devm.getStor d1 sevm.currentTarget =
        (Devm.getStor s sevm.currentTarget).set chiSlot scale := by
      rw [sstore_getStor_set hstore1 hpChi,
        ← congrFun (getStor_of_state hst_c2) sevm.currentTarget]
    have hpD1 : tail <<+ d1.stack := prefix_of_sstore hstore1 hpChi
    have hmem_d1 : s.memory = d1.memory := by
      refine hmem0.trans ?_
      refine (of_run_pushCreationCoordinate hpushA).memory.trans ?_
      refine (of_run_codesize hcodesize).memory.trans ?_
      refine (Ninst.Hinv.inv (f := Devm.memory) heq).trans ?_
      refine hpop.memory.trans ?_
      refine hburn.memory.trans ?_
      refine (of_run_pushB256 hpushS).memory.trans ?_
      refine (of_run_pushB256 hpushC).memory.trans ?_
      exact Ninst.Hinv.inv (f := Devm.memory) hstore1
    rcases of_run_next hbody with ⟨d2, hts, hbody⟩
    have hpT : sevm.benvStat.time :: tail <<+ d2.stack :=
      prefix_of_push (pushBurn_of_run_timestamp hts) hpD1
    rcases of_run_next hbody with ⟨d3, hpushR, hbody⟩
    have hpR : rhoSlot :: sevm.benvStat.time :: tail <<+ d3.stack :=
      prefix_of_push (of_run_pushB256 hpushR) hpT
    rcases of_run_next hbody with ⟨e1, hstore2, hbody⟩
    have hst_d3 : d1.state = d3.state :=
      (pushBurn_of_run_timestamp hts).state.trans
        (of_run_pushB256 hpushR).state
    have hstor2 : Devm.getStor e1 sevm.currentTarget =
        ((Devm.getStor s sevm.currentTarget).set chiSlot scale).set rhoSlot
          sevm.benvStat.time := by
      rw [sstore_getStor_set hstore2 hpR,
        ← congrFun (getStor_of_state hst_d3) sevm.currentTarget, hstor1]
    have hpE1 : tail <<+ e1.stack := prefix_of_sstore hstore2 hpR
    rcases of_run_next hbody with ⟨e2, hpushRL1, hbody⟩
    have hpE2 : Nat.toB256 1762 :: tail <<+ e2.stack :=
      prefix_of_push (of_run_pushCreationCoordinate hpushRL1) hpE1
    rcases of_run_next hbody with ⟨e3, hpushRO, hbody⟩
    have hpE3 : Nat.toB256 239 :: Nat.toB256 1762 :: tail <<+ e3.stack :=
      prefix_of_push (of_run_pushCreationCoordinate hpushRO) hpE2
    rcases of_run_next hbody with ⟨e4, hpush01, hbody⟩
    have hpE4 : (0 : B256) :: Nat.toB256 239 :: Nat.toB256 1762 :: tail
        <<+ e4.stack :=
      prefix_of_push (of_run_pushB256 hpush01) hpE3
    rcases of_run_next hbody with ⟨f1, hcc, hbody⟩
    have hmem_e4 : s.memory = e4.memory := by
      refine hmem_d1.trans ?_
      refine (pushBurn_of_run_timestamp hts).memory.trans ?_
      refine (of_run_pushB256 hpushR).memory.trans ?_
      refine (Ninst.Hinv.inv (f := Devm.memory) hstore2).trans ?_
      refine (of_run_pushCreationCoordinate hpushRL1).memory.trans ?_
      refine (of_run_pushCreationCoordinate hpushRO).memory.trans ?_
      exact (of_run_pushB256 hpush01).memory
    have hwf_e4 : Mem.Wf e4.memory := by
      rw [← hmem_e4]
      exact hwf
    have hreads_e4 : Mem.Reads e4.memory image := by
      rw [← hmem_e4]
      exact hreads
    obtain ⟨hpf1, _, hreads_f1, hst_f1, _⟩ :=
      of_run_codecopy_image hpE4 hwf_e4 hreads_e4 hcc
    rcases of_run_next hbody with ⟨f2, hpushRL2, hbody⟩
    have hpF2 : Nat.toB256 1762 :: tail <<+ f2.stack :=
      prefix_of_push (of_run_pushCreationCoordinate hpushRL2) hpf1
    rcases of_run_next hbody with ⟨f3, hpush02, hret⟩
    have hpF3 : (0 : B256) :: Nat.toB256 1762 :: tail <<+ f3.stack :=
      prefix_of_push (of_run_pushB256 hpush02) hpF2
    have hout : Devm.output r = code := by
      have hretout := (of_run_return_val hpF3 hret).1
      rw [B256.toNat_zero, hRL1762] at hretout
      have hmem_f3 : f1.memory = f3.memory :=
        (of_run_pushCreationCoordinate hpushRL2).memory.trans
          (of_run_pushB256 hpush02).memory
      rw [← hmem_f3, Mem.Reads.read hreads_f1 0 1762] at hretout
      rw [B256.toNat_zero, hslice] at hretout
      rw [← hlen, Bytes.sliceD_writeAt] at hretout
      exact hretout
    have hg : Devm.getStor r sevm.currentTarget =
        ((Devm.getStor s sevm.currentTarget).set chiSlot scale).set rhoSlot
          sevm.benvStat.time := by
      have he4 : Devm.getStor e1 = Devm.getStor e4 :=
        getStor_of_state (((of_run_pushCreationCoordinate hpushRL1).state.trans
          (of_run_pushCreationCoordinate hpushRO).state).trans
          (of_run_pushB256 hpush01).state)
      have hf3 : Devm.getStor f1 = Devm.getStor f3 :=
        getStor_of_state ((of_run_pushCreationCoordinate hpushRL2).state.trans
          (of_run_pushB256 hpush02).state)
      have hr : Devm.getStor f3 = Devm.getStor r :=
        Func.of_inv Devm.getStor Devm.getStor (by func_inv) hret
      rw [← congrFun hr sevm.currentTarget,
        ← congrFun hf3 sevm.currentTarget,
        ← congrFun (getStor_of_state hst_f1) sevm.currentTarget,
        ← congrFun he4 sevm.currentTarget, hstor2]
    exact ⟨hv, hg, hout⟩

/-! ## F4b: constructor execution

The compiled constructor prefix executes gas-exactly against the creation
image. G1 already owns the compiler-output bridge
(`constructorInitPrefix_compile` + `creationCode_eq_prefix_append_runtime`);
below are the slice and return-window facts the walk's memory steps need,
then the walk itself with its `Exec`/message bridge and installed-post
certificate. -/

theorem constructorCode_slice_exact {sevm : Sevm}
    (hcode : sevm.code.toList = creationCode) :
    sevm.code.sliceD 239 1762 (Linst.toUInt8 .stop) = code := by
  have hstop : Linst.toUInt8 .stop = 0 := rfl
  rw [hstop, ByteArray.sliceD_eq, hcode, ← constructorRuntimeOffset_exact,
    ← codeSize_exact]
  exact creationCode_slice_runtime

theorem constructorReturnImage_read :
    ((Mem.empty.write 0 code).read 0 1762).1 = code := by
  have hreadsM : Mem.Reads (Mem.empty.write 0 code) (Bytes.writeAt [] 0 code) :=
    Mem.Reads.write Mem.wf_empty Mem.reads_empty 0 code
  have hread := Mem.Reads.read hreadsM 0 1762
  have hlen : code.length = 1762 := codeSize_exact
  rw [← hlen] at hread ⊢
  rw [Bytes.sliceD_writeAt] at hread
  exact hread

/-! ## Balance threading

`getBal` preservation through the walk's transitions, the two `B256`
zero-lemmas, the value-zero entry-transfer balance-map equality, and the
`addBal`-at-another-address projection for final settlement. All eight are
generic-shaped (S9 hoist candidates); they live here only because the packet
owns no shared path. -/

private theorem getBal_setMach_eq {d : Devm} {m : Mach} {a : Adr} :
    (d.setMach m).getBal a = d.getBal a := rfl

private theorem getBal_addAccessed_eq {d : Devm} {a : Adr} {k : B256} {b : Adr} :
    (addAccessedStorageKey d a k).getBal b = d.getBal b := rfl

private theorem getBal_withRefundCounter_eq {d : Devm} {n : Int} {b : Adr} :
    (d.withRefundCounter n).getBal b = d.getBal b := rfl

private theorem getBal_setStorVal_eq {d : Devm} {a : Adr} {k v : B256} {b : Adr} :
    (d.setStorVal a k v).getBal b = d.getBal b := by
  show ((d.state.setStorVal a k v).get b).bal = (d.state.get b).bal
  unfold State.setStorVal
  by_cases h : a = b
  · subst h
    rw [State.get_set_self]
  · rw [State.get_set_ne _ h]

private theorem b256_sub_zero (x : B256) : x - 0 = x := by
  rcases x with ⟨xh, xl⟩
  have hborrow : ¬ xl < (0 : B128) := by
    intro hlt
    rcases hlt with hlt | ⟨_, hlt⟩
    · exact UInt64.not_lt_zero hlt
    · exact UInt64.not_lt_zero hlt
  show ((xh - (0 : B128)) -
      (if xl < (0 : B128) then (1 : B128) else 0),
    xl - (0 : B128)) = (xh, xl)
  simp only [if_neg hborrow, B128.sub_zero]

private theorem b256_add_zero (x : B256) : x + 0 = x := by
  apply B256.toNat_inj
  rw [B256.toNat_add, show (0 : B256).toNat = 0 from rfl, Nat.add_zero]
  exact Nat.lo_eq_of_lt (B256.toNat_lt x)

/-- A zero-value message entry preserves the complete balance map, including
the self-call case where caller and callee coincide. -/
private theorem benvAfterTransfer_bal_of_value_zero {msg : Msg} {post : Benv}
    (hzero : msg.value = 0)
    (hrun : msg.benvAfterTransfer = .ok post) :
    post.state.bal = msg.benv.state.bal := by
  by_cases hstv : msg.shouldTransferValue = true
  · obtain ⟨debit, hsub, rfl⟩ := of_benvAfterTransfer hstv hrun
    rw [hzero] at hsub ⊢
    have hdebit : debit.bal = msg.benv.state.bal := by
      obtain ⟨_, hdebitEq⟩ := State.of_subBal hsub
      rw [hdebitEq]
      funext a
      show ((msg.benv.state.setBal msg.caller _).get a).bal = _
      by_cases hcaller : msg.caller = a
      · subst hcaller
        rw [State.setBal_get_self]
        exact b256_sub_zero _
      · simp only [State.setBal_get_ne hcaller, State.bal]
    have hadd : ((msg.benv.withState debit).addBal
        msg.currentTarget 0).state.bal = debit.bal := by
      have e : ((msg.benv.withState debit).addBal
          msg.currentTarget 0).state =
          debit.addBal msg.currentTarget 0 := rfl
      rw [e]
      funext a
      show ((debit.addBal msg.currentTarget 0).get a).bal = _
      unfold State.addBal
      by_cases htarget : msg.currentTarget = a
      · subst htarget
        rw [State.setBal_get_self]
        exact b256_add_zero _
      · simp only [State.setBal_get_ne htarget, State.bal]
    exact hadd.trans hdebit
  · have h := of_benvAfterTransfer_no hstv hrun
    subst post
    rfl

private theorem addBal_bal_ne {st : State} {a b : Adr} {v : B256} (h : a ≠ b) :
    (st.addBal a v).bal b = st.bal b := by
  show ((st.setBal a (st.bal a + v)).get b).bal = (st.get b).bal
  rw [State.setBal_get_ne h]

theorem constructorProgram_runCompiled {sevm : Sevm} {pre : Devm} {G : Nat}
    (hcode : sevm.code.toList = creationCode)
    (hvalue : sevm.value = 0)
    (hstatic : sevm.isStatic = false)
    (htime : sevm.benvStat.time ≠ 0)
    (hstack : pre.stack = [])
    (hmem : pre.memory = Mem.empty)
    (hgas : pre.gasLeft = G + 44611)
    (hlogs : pre.logs = [])
    (hrefund : pre.refundCounter = 0)
    (herror : pre.error = .none)
    (horigChi : getOrigStorVal sevm sevm.currentTarget chiSlot = 0)
    (horigRho : getOrigStorVal sevm sevm.currentTarget rhoSlot = 0)
    (hcurChi : pre.getStorVal sevm.currentTarget chiSlot = 0)
    (hcurRho : pre.getStorVal sevm.currentTarget rhoSlot = 0)
    (hcurAll : ∀ k, pre.getStorVal sevm.currentTarget k = 0)
    (hcoldChi : ⟨sevm.currentTarget, chiSlot⟩ ∉ pre.accessedStorageKeys)
    (hcoldRho : ⟨sevm.currentTarget, rhoSlot⟩ ∉ pre.accessedStorageKeys) :
    ∃ post, Prog.RunCompiled sevm pre constructorProgram post ∧
      post.output = code ∧
      post.error = .none ∧
      post.logs = [] ∧
      Devm.getStorVal post sevm.currentTarget chiSlot = scale ∧
      Devm.getStorVal post sevm.currentTarget rhoSlot = sevm.benvStat.time ∧
      post.gasLeft = G ∧ post.refundCounter = 0 ∧
      post.accountsToDelete = pre.accountsToDelete ∧
      (∀ k, k ≠ chiSlot → k ≠ rhoSlot → Devm.getStorVal post sevm.currentTarget k = 0) ∧
      post.getBal sevm.currentTarget = pre.getBal sevm.currentTarget ∧
      post.state = (pre.state.setStorVal sevm.currentTarget chiSlot scale).setStorVal
        sevm.currentTarget rhoSlot sevm.benvStat.time := by
  have hlen : code.length = 1762 := codeSize_exact
  have hsize : sevm.code.size = 2001 := by
    rw [ByteArray.size_eq_length_toList, hcode]
    exact creationCodeSize_exact
  have hAO : (239 : Nat) + 1762 = 2001 := by decide
  have hRO239 : (Nat.toB256 239).toNat = 239 :=
    B256.toNat_toB256_of_lt (by decide)
  have hRL1762 : (Nat.toB256 1762).toNat = 1762 :=
    B256.toNat_toB256_of_lt (by decide)
  have hChiNeRho : chiSlot ≠ rhoSlot := by decide
  have hScaleNe0 : (0 : B256) ≠ scale := by decide
  have htime0 : (0 : B256) ≠ sevm.benvStat.time := Ne.symm htime
  have hne : (1 : B256) ≠ 0 := by decide
  have hvcS : sstoreValueCost 0 0 scale = gasStorageSet := by
    simp [sstoreValueCost, hScaleNe0]
  have hvcT : sstoreValueCost 0 0 sevm.benvStat.time = gasStorageSet := by
    simp [sstoreValueCost, htime0]
  have hrcS : sstoreNewRefundCounter scale 0 0 0 = 0 := by decide
  have hrcT : sstoreNewRefundCounter sevm.benvStat.time 0 0 0 = 0 := by
    simp [sstoreNewRefundCounter, htime0]
  let fs := constructorProgram.main :: constructorProgram.aux
  let F0 : Func := Func.return_
  let F1 : Func := pushB256 0 ::: F0
  let F2 : Func := pushCreationCoordinate 1762 ::: F1
  let F3 : Func := codecopy ::: F2
  let F4 : Func := pushB256 0 ::: F3
  let F5 : Func := pushCreationCoordinate 239 ::: F4
  let F6 : Func := pushCreationCoordinate 1762 ::: F5
  let F7 : Func := sstore ::: F6
  let F8 : Func := pushB256 rhoSlot ::: F7
  let F9 : Func := timestamp ::: F8
  let F10 : Func := sstore ::: F9
  let F11 : Func := pushB256 chiSlot ::: F10
  let F12 : Func := pushB256 scale ::: F11
  let G1 : Func := (F12 <?> Func.revert)
  let E0 : Func := eq ::: G1
  let E1 : Func := codesize ::: E0
  let BODY : Func := pushCreationCoordinate 2001 ::: E1
  let G0 : Func := (BODY <?> Func.revert)
  let N0 : Func := iszero ::: G0
  let MAIN : Func := callvalue ::: N0
  let mid := pre.setMach ⟨[], Mem.empty, G + 44610⟩
  let s1 := mid.setMach ⟨[sevm.value], Mem.empty, G + 44608⟩
  let s2 := s1.setMach ⟨[(1 : B256)], Mem.empty, G + 44605⟩
  let s3 := s2.setMach ⟨[], Mem.empty, G + 44591⟩
  let s4 := s3.setMach ⟨[Nat.toB256 2001], Mem.empty, G + 44588⟩
  let s5 := s4.setMach ⟨[sevm.code.size.toB256, Nat.toB256 2001], Mem.empty, G + 44586⟩
  let s6 := s5.setMach ⟨[(1 : B256)], Mem.empty, G + 44583⟩
  let s7 := s6.setMach ⟨[], Mem.empty, G + 44569⟩
  let s8 := s7.setMach ⟨[scale], Mem.empty, G + 44566⟩
  let s9 := s8.setMach ⟨[chiSlot, scale], Mem.empty, G + 44563⟩
  let s10 := ((((addAccessedStorageKey s9 sevm.currentTarget chiSlot).withRefundCounter 0).setStorVal sevm.currentTarget chiSlot scale).setMach ⟨[], Mem.empty, G + 22463⟩)
  let s11 := s10.setMach ⟨[sevm.benvStat.time], Mem.empty, G + 22461⟩
  let s12 := s11.setMach ⟨[rhoSlot, sevm.benvStat.time], Mem.empty, G + 22458⟩
  let s13 := ((((addAccessedStorageKey s12 sevm.currentTarget rhoSlot).withRefundCounter 0).setStorVal sevm.currentTarget rhoSlot sevm.benvStat.time).setMach ⟨[], Mem.empty, G + 358⟩)
  let s14 := s13.setMach ⟨[Nat.toB256 1762], Mem.empty, G + 355⟩
  let s15 := s14.setMach ⟨[Nat.toB256 239, Nat.toB256 1762], Mem.empty, G + 352⟩
  let s16 := s15.setMach ⟨[(0 : B256), Nat.toB256 239, Nat.toB256 1762], Mem.empty, G + 350⟩
  let s17 := s16.setMach ⟨[], Mem.empty.write 0 code, G + 5⟩
  let s18 := s17.setMach ⟨[Nat.toB256 1762], Mem.empty.write 0 code, G + 2⟩
  let s19 := s18.setMach ⟨[(0 : B256), Nat.toB256 1762], Mem.empty.write 0 code, G⟩
  let dRet := s19.setMach ⟨[], Mem.empty.write 0 code, G⟩
  let postW := (dRet.withMemory (Mem.empty.write 0 code)).withOutput code
  have hentry : Devm.BurnBy gJumpdest pre mid := by
    simpa only [mid, hstack, hmem] using
      Devm.burnBy_setMach_gas (devm := pre) (cost := gJumpdest) (G := G + 44610) (by simp only [hgas, gJumpdest])
  have h1 : Ninst.RunCompiled sevm mid callvalue s1 := by
    simpa only [s1, mid, Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushItem (sevm := sevm) (devm := mid) (r := .callvalue) (x := sevm.value) (cost := gBase) (G := G + 44608) (by rintro ⟨⟩) rfl (by simp only [mid, Devm.gasLeft_setMach, gBase]) (by simp only [mid, Devm.stack_setMach, List.length_nil]; omega))
  have h2 : Ninst.RunCompiled sevm s1 iszero s2 := by
    simpa only [s2, s1, Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_unary (sevm := sevm) (devm := s1) (r := .iszero) (cost := gVerylow) (G := G + 44605) (x := sevm.value) (v := 1) (s := []) (by rintro ⟨⟩) rfl (by simp only [s1, Devm.stack_setMach]) (by show B256.eqCheck sevm.value 0 = 1; rw [hvalue]; simp [B256.eqCheck]) (by simp only [s1, Devm.gasLeft_setMach, gVerylow]) (by simp only [List.length_nil]; omega))
  have hpop1 : Devm.PopBurnBy [(1 : B256)] (gVerylow + gHigh + gJumpdest) s2 s3 := by
    simpa only [s3, s2, Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using
      Devm.popBurnBy_setMach (devm := s2) (x := 1) (s := []) (cost := gVerylow + gHigh + gJumpdest) (G := G + 44591) (by simp only [s2, Devm.stack_setMach]) (by simp only [s2, Devm.gasLeft_setMach, gVerylow, gHigh, gJumpdest])
  have hroom2 : s2.stack.length < 1024 := by
    simp only [s2, Devm.stack_setMach, List.length_cons, List.length_nil]; omega
  have h4 : Ninst.RunCompiled sevm s3 (pushCreationCoordinate 2001) s4 := by
    simpa only [s4, s3, pushCreationCoordinate, Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushB256Full (sevm := sevm) (devm := s3) (w := Nat.toB256 2001) (G := G + 44588) (by simp only [s3, Devm.gasLeft_setMach, gVerylow]) (by simp only [s3, Devm.stack_setMach, List.length_nil]; omega))
  have h5 : Ninst.RunCompiled sevm s4 codesize s5 := by
    simpa only [s5, s4, Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushItem (sevm := sevm) (devm := s4) (r := .codesize) (x := sevm.code.size.toB256) (cost := gBase) (G := G + 44586) (by rintro ⟨⟩) rfl (by simp only [s4, Devm.gasLeft_setMach, gBase]) (by simp only [s4, Devm.stack_setMach, List.length_cons, List.length_nil]; omega))
  have h6 : Ninst.RunCompiled sevm s5 eq s6 := by
    simpa only [s6, s5, Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_binary (sevm := sevm) (devm := s5) (r := .eq) (cost := gVerylow) (G := G + 44583) (x := sevm.code.size.toB256) (y := Nat.toB256 2001) (v := 1) (s := []) (by rintro ⟨⟩) rfl (by simp only [s5, Devm.stack_setMach]) (by show B256.eqCheck sevm.code.size.toB256 (Nat.toB256 2001) = 1; rw [hsize]; simp [B256.eqCheck]) (by simp only [s5, Devm.gasLeft_setMach, gVerylow]) (by simp only [List.length_nil]; omega))
  have hpop2 : Devm.PopBurnBy [(1 : B256)] (gVerylow + gHigh + gJumpdest) s6 s7 := by
    simpa only [s7, s6, Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using
      Devm.popBurnBy_setMach (devm := s6) (x := 1) (s := []) (cost := gVerylow + gHigh + gJumpdest) (G := G + 44569) (by simp only [s6, Devm.stack_setMach]) (by simp only [s6, Devm.gasLeft_setMach, gVerylow, gHigh, gJumpdest])
  have hroom6 : s6.stack.length < 1024 := by
    simp only [s6, Devm.stack_setMach, List.length_cons, List.length_nil]; omega
  have h8 : Ninst.RunCompiled sevm s7 (pushB256 scale) s8 := by
    simpa only [s8, s7, Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushB256 (sevm := sevm) (devm := s7) (w := scale) (c := gVerylow) (G := G + 44566) (by decide) (by simp only [s7, Devm.gasLeft_setMach, gVerylow]) (by simp only [s7, Devm.stack_setMach, List.length_nil]; omega))
  have h9 : Ninst.RunCompiled sevm s8 (pushB256 chiSlot) s9 := by
    simpa only [s9, s8, Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushB256 (sevm := sevm) (devm := s8) (w := chiSlot) (c := gVerylow) (G := G + 44563) (by decide) (by simp only [s8, Devm.gasLeft_setMach, gVerylow]) (by simp only [s8, Devm.stack_setMach, List.length_cons, List.length_nil]; omega))
  have hc9 : s9.getStorVal sevm.currentTarget chiSlot = 0 := by
    simpa only [s9, s8, s7, s6, s5, s4, s3, s2, s1, mid, Devm.getStorVal_setMach] using hcurChi
  have hrefund9 : s9.refundCounter = 0 := by
    simpa only [s9, s8, s7, s6, s5, s4, s3, s2, s1, mid, Devm.setMach_refundCounter] using hrefund
  have haccess9 : s9.accessedStorageKeys = pre.accessedStorageKeys := by
    simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, mid, Devm.setMach_accessedStorageKeys]
  have h10 : Ninst.RunCompiled sevm s9 sstore s10 := by
    apply Ninst.runCompiled_sstore_cold (c := gasColdSload + gasStorageSet) (G := G + 22463) (rc := 0)
    · rfl
    · rw [haccess9]; exact hcoldChi
    · simp only [s9, Devm.gasLeft_setMach, gCallStipend]; omega
    · exact hstatic
    · simp only [horigChi, hc9, hvcS]
    · simp only [horigChi, hc9, hrefund9, hrcS]
    · simp only [s9, Devm.gasLeft_setMach, gasColdSload, gasStorageSet]
  have h11 : Ninst.RunCompiled sevm s10 timestamp s11 := by
    simpa only [s11, s10, Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushItem (sevm := sevm) (devm := s10) (r := .timestamp) (x := sevm.benvStat.time) (cost := gBase) (G := G + 22461) (by rintro ⟨⟩) rfl (by simp only [s10, Devm.gasLeft_setMach, gBase]) (by simp only [s10, Devm.stack_setMach, List.length_nil]; omega))
  have h12 : Ninst.RunCompiled sevm s11 (pushB256 rhoSlot) s12 := by
    simpa only [s12, s11, Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushB256 (sevm := sevm) (devm := s11) (w := rhoSlot) (c := gVerylow) (G := G + 22458) (by decide) (by simp only [s11, Devm.gasLeft_setMach, gVerylow]) (by simp only [s11, Devm.stack_setMach, List.length_cons, List.length_nil]; omega))
  have hcur9Rho : s9.getStorVal sevm.currentTarget rhoSlot = 0 := by
    simpa only [s9, s8, s7, s6, s5, s4, s3, s2, s1, mid, Devm.getStorVal_setMach] using hcurRho
  have hcur12 : s12.getStorVal sevm.currentTarget rhoSlot = 0 := by
    have h10w : ((((addAccessedStorageKey s9 sevm.currentTarget chiSlot).withRefundCounter 0).setStorVal sevm.currentTarget chiSlot scale)).getStorVal sevm.currentTarget rhoSlot = s9.getStorVal sevm.currentTarget rhoSlot := by
      show (Devm.getStor (((addAccessedStorageKey s9 sevm.currentTarget chiSlot).withRefundCounter 0).setStorVal sevm.currentTarget chiSlot scale) sevm.currentTarget).get rhoSlot = (Devm.getStor s9 sevm.currentTarget).get rhoSlot
      rw [setStorVal_getStor_self, Stor.get_set_ne _ hChiNeRho, Devm.withRefundCounter_getStor, addAccessedStorageKey_getStor]
    simpa only [s12, s11, s10, Devm.getStorVal_setMach, h10w] using hcur9Rho
  have hrefund12 : s12.refundCounter = 0 := rfl
  have haccess12 : ⟨sevm.currentTarget, rhoSlot⟩ ∉ s12.accessedStorageKeys := by
    have h10acc : s10.accessedStorageKeys = Std.HashSet.insert pre.accessedStorageKeys ⟨sevm.currentTarget, chiSlot⟩ := by rfl
    have h1210 : s12.accessedStorageKeys = s10.accessedStorageKeys := by rfl
    rw [h1210, h10acc]
    intro hmem
    rcases Std.HashSet.mem_insert.mp hmem with he | hx
    · exact hChiNeRho (congrArg Prod.snd (eq_of_beq he))
    · exact hcoldRho hx
  have h13 : Ninst.RunCompiled sevm s12 sstore s13 := by
    apply Ninst.runCompiled_sstore_cold (c := gasColdSload + gasStorageSet) (G := G + 358) (rc := 0)
    · rfl
    · exact haccess12
    · simp only [s12, Devm.gasLeft_setMach, gCallStipend]; omega
    · exact hstatic
    · simp only [horigRho, hcur12, hvcT]
    · simp only [horigRho, hcur12, hrefund12, hrcT]
    · simp only [s12, Devm.gasLeft_setMach, gasColdSload, gasStorageSet]
  have h14 : Ninst.RunCompiled sevm s13 (pushCreationCoordinate 1762) s14 := by
    simpa only [s14, s13, pushCreationCoordinate, Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushB256Full (sevm := sevm) (devm := s13) (w := Nat.toB256 1762) (G := G + 355) (by simp only [s13, Devm.gasLeft_setMach, gVerylow]) (by simp only [s13, Devm.stack_setMach, List.length_nil]; omega))
  have h15 : Ninst.RunCompiled sevm s14 (pushCreationCoordinate 239) s15 := by
    simpa only [s15, s14, pushCreationCoordinate, Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushB256Full (sevm := sevm) (devm := s14) (w := Nat.toB256 239) (G := G + 352) (by simp only [s14, Devm.gasLeft_setMach, gVerylow]) (by simp only [s14, Devm.stack_setMach, List.length_cons, List.length_nil]; omega))
  have h16 : Ninst.RunCompiled sevm s15 (pushB256 0) s16 := by
    simpa only [s16, s15, Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushB256 (sevm := sevm) (devm := s15) (w := 0) (c := gBase) (G := G + 350) (by decide) (by simp only [s15, Devm.gasLeft_setMach, gBase]) (by simp only [s15, Devm.stack_setMach, List.length_cons, List.length_nil]; omega))
  have hext16 : s16.extCost [⟨0, 1762⟩] = 174 :=
    Devm.extCost_of_size (N := Mem.empty) (n := 0) (i := 0) (sz := 1762) (e := 174) (by rfl) (by decide)
  have h17 : Ninst.RunCompiled sevm s16 codecopy s17 := by
    apply Ninst.runCompiled_codecopy_of (c := 345) (G := G + 5) (M := Mem.empty.write 0 code)
    · rfl
    · simp only [B256.toNat_zero, hRL1762, hext16]; decide
    · simp only [s16, Devm.memory_setMach, B256.toNat_zero, hRO239, hRL1762, constructorCode_slice_exact hcode]
    · simp only [s16, Devm.gasLeft_setMach]
  have h18 : Ninst.RunCompiled sevm s17 (pushCreationCoordinate 1762) s18 := by
    simpa only [s18, s17, pushCreationCoordinate, Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushB256Full (sevm := sevm) (devm := s17) (w := Nat.toB256 1762) (G := G + 2) (by simp only [s17, Devm.gasLeft_setMach, gVerylow]) (by simp only [s17, Devm.stack_setMach, List.length_nil]; omega))
  have h19 : Ninst.RunCompiled sevm s18 (pushB256 0) s19 := by
    simpa only [s19, s18, Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushB256 (sevm := sevm) (devm := s18) (w := 0) (c := gBase) (G := G) (by decide) (by simp only [s18, Devm.gasLeft_setMach, gBase]) (by simp only [s18, Devm.stack_setMach, List.length_cons, List.length_nil]; omega))
  have hMsize32 : (Mem.empty.write 0 code).size % 32 = 0 := by
    rw [Mem.size_write_of_size (by rfl : Mem.empty.size = 0) (by decide : 0 % 32 = 0) codeSize_exact]
    decide
  have hMcov : 0 + 1762 ≤ (Mem.empty.write 0 code).size := by
    rw [Mem.size_write_of_size (by rfl : Mem.empty.size = 0) (by decide : 0 % 32 = 0) codeSize_exact]
    decide
  have hext19 : s19.extCost [⟨0, 1762⟩] = 0 :=
    Devm.extCost_zero_of_le hMsize32 hMcov
  have h_read : (s19.setMach ⟨[], s19.memory, G⟩).memRead (0 : B256).toNat (Nat.toB256 1762).toNat = ⟨code, dRet.withMemory (Mem.empty.write 0 code)⟩ := by
    have hmem19 : s19.memory = Mem.empty.write 0 code := by simp only [s19, Devm.memory_setMach]
    simp only [B256.toNat_zero, hRL1762, hmem19, Devm.memRead, Devm.memory_setMach, dRet,
      constructorReturnImage_read, Mem.read_snd_eq_self (memExtSize_of_le hMsize32 hMcov)]
  have hT0 : Func.RunCompiled fs sevm s19 F0 postW :=
    Func.runCompiled_return (i := (0 : B256)) (sz := Nat.toB256 1762) (s := []) (out := code) (d' := dRet.withMemory (Mem.empty.write 0 code)) (G := G) rfl (by simp only [B256.toNat_zero, hRL1762, hext19, s19, Devm.gasLeft_setMach]; omega) h_read
  have hT1 : Func.RunCompiled fs sevm s18 F1 postW := .next h19 hT0
  have hT2 : Func.RunCompiled fs sevm s17 F2 postW := .next h18 hT1
  have hT3 : Func.RunCompiled fs sevm s16 F3 postW := .next h17 hT2
  have hT4 : Func.RunCompiled fs sevm s15 F4 postW := .next h16 hT3
  have hT5 : Func.RunCompiled fs sevm s14 F5 postW := .next h15 hT4
  have hT6 : Func.RunCompiled fs sevm s13 F6 postW := .next h14 hT5
  have hT7 : Func.RunCompiled fs sevm s12 F7 postW := .next h13 hT6
  have hT8 : Func.RunCompiled fs sevm s11 F8 postW := .next h12 hT7
  have hT9 : Func.RunCompiled fs sevm s10 F9 postW := .next h11 hT8
  have hT10 : Func.RunCompiled fs sevm s9 F10 postW := .next h10 hT9
  have hT11 : Func.RunCompiled fs sevm s8 F11 postW := .next h9 hT10
  have hT12 : Func.RunCompiled fs sevm s7 F12 postW := .next h8 hT11
  have hG1 : Func.RunCompiled fs sevm s6 G1 postW := .succ hne hroom6 hpop2 hT12
  have hE0 : Func.RunCompiled fs sevm s5 E0 postW := .next h6 hG1
  have hE1 : Func.RunCompiled fs sevm s4 E1 postW := .next h5 hE0
  have hBODY : Func.RunCompiled fs sevm s3 BODY postW := .next h4 hE1
  have hG0 : Func.RunCompiled fs sevm s2 G0 postW := .succ hne hroom2 hpop1 hBODY
  have hN0 : Func.RunCompiled fs sevm s1 N0 postW := .next h2 hG0
  have hMAIN : Func.RunCompiled fs sevm mid MAIN postW := .next h1 hN0
  have hFunc : Func.RunCompiled (constructorProgram.main :: constructorProgram.aux) sevm mid constructorProgram.main postW := by
    simp only [fs] at hMAIN
    rw [constructorProgram_eq] at hMAIN ⊢
    simp only [constructorProgramAt, nonpayable, constructorBody, constructorRuntimeOffset_exact, hlen, hAO] at hMAIN ⊢
    exact hMAIN
  have hProg : Prog.RunCompiled sevm pre constructorProgram postW := ⟨mid, hentry, hFunc⟩
  have hRun : Func.Run (constructorProgram.main :: constructorProgram.aux) sevm mid constructorProgram.main postW :=
    Func.Run.of_runCompiled hFunc
  have hnil : ([] : Stack) <<+ mid.stack := nil_pref
  have hwfMid : Mem.Wf mid.memory := by simp only [mid, Devm.memory_setMach]; exact Mem.wf_empty
  have hreadsMid : Mem.Reads mid.memory [] := by simp only [mid, Devm.memory_setMach]; exact Mem.reads_empty
  obtain ⟨-, hstorW, houtW⟩ := of_run_constructorProgram_main hnil hwfMid hreadsMid hcode hRun
  have hrowChi : Devm.getStorVal postW sevm.currentTarget chiSlot = scale := by
    show (Devm.getStor postW sevm.currentTarget).get chiSlot = scale
    rw [hstorW, Stor.get_set_ne _ (Ne.symm hChiNeRho), Stor.get_set_self]
  have hrowRho : Devm.getStorVal postW sevm.currentTarget rhoSlot = sevm.benvStat.time := by
    show (Devm.getStor postW sevm.currentTarget).get rhoSlot = sevm.benvStat.time
    rw [hstorW, Stor.get_set_self]
  have hpieW : ∀ k, k ≠ chiSlot → k ≠ rhoSlot → Devm.getStorVal postW sevm.currentTarget k = 0 := by
    intro k hkc hkr
    show (Devm.getStor postW sevm.currentTarget).get k = 0
    rw [hstorW, Stor.get_set_ne _ (Ne.symm hkr), Stor.get_set_ne _ (Ne.symm hkc)]
    show (Devm.getStor pre sevm.currentTarget).get k = 0
    exact hcurAll k
  have hgasW : postW.gasLeft = G := rfl
  have hrefundW : postW.refundCounter = 0 := rfl
  have hdeleteW : postW.accountsToDelete = pre.accountsToDelete := rfl
  have herrW : postW.error = .none := by
    simp only [postW, dRet, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, mid]
    exact herror
  have hlogsW : postW.logs = [] := by
    simp only [postW, dRet, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, mid]
    exact hlogs
  have hbalW : postW.getBal sevm.currentTarget = pre.getBal sevm.currentTarget := by
    show dRet.getBal sevm.currentTarget = pre.getBal sevm.currentTarget
    simp only [dRet, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10,
      s9, s8, s7, s6, s5, s4, s3, s2, s1, mid,
      getBal_setMach_eq, getBal_setStorVal_eq, getBal_withRefundCounter_eq,
      getBal_addAccessed_eq]
  have hstateW : postW.state =
      (pre.state.setStorVal sevm.currentTarget chiSlot scale).setStorVal
        sevm.currentTarget rhoSlot sevm.benvStat.time := by rfl
  exact ⟨postW, hProg, houtW, herrW, hlogsW, hrowChi, hrowRho, hgasW, hrefundW,
    hdeleteW, hpieW, hbalW, hstateW⟩

theorem constructorExec_of_walk {sevm : Sevm} {pre : Devm} {G : Nat}
    (hcode : sevm.code.toList = creationCode)
    (hvalue : sevm.value = 0)
    (hstatic : sevm.isStatic = false)
    (htime : sevm.benvStat.time ≠ 0)
    (hstack : pre.stack = [])
    (hmem : pre.memory = Mem.empty)
    (hgas : pre.gasLeft = G + 44611)
    (hlogs : pre.logs = [])
    (hrefund : pre.refundCounter = 0)
    (herror : pre.error = .none)
    (horigChi : getOrigStorVal sevm sevm.currentTarget chiSlot = 0)
    (horigRho : getOrigStorVal sevm sevm.currentTarget rhoSlot = 0)
    (hcurChi : pre.getStorVal sevm.currentTarget chiSlot = 0)
    (hcurRho : pre.getStorVal sevm.currentTarget rhoSlot = 0)
    (hcurAll : ∀ k, pre.getStorVal sevm.currentTarget k = 0)
    (hcoldChi : ⟨sevm.currentTarget, chiSlot⟩ ∉ pre.accessedStorageKeys)
    (hcoldRho : ⟨sevm.currentTarget, rhoSlot⟩ ∉ pre.accessedStorageKeys) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧
      post.output = code ∧
      post.error = .none ∧
      post.logs = [] ∧
      Devm.getStorVal post sevm.currentTarget chiSlot = scale ∧
      Devm.getStorVal post sevm.currentTarget rhoSlot = sevm.benvStat.time ∧
      post.gasLeft = G ∧ post.refundCounter = 0 ∧
      post.accountsToDelete = pre.accountsToDelete ∧
      (∀ k, k ≠ chiSlot → k ≠ rhoSlot → Devm.getStorVal post sevm.currentTarget k = 0) ∧
      post.getBal sevm.currentTarget = pre.getBal sevm.currentTarget ∧
      post.state = (pre.state.setStorVal sevm.currentTarget chiSlot scale).setStorVal
        sevm.currentTarget rhoSlot sevm.benvStat.time := by
  obtain ⟨postW, hProg, houtW, herrW, hlogsW, hrowChi, hrowRho, hgasW, hrefundW, hdeleteW, hpieW, hbalW, hstateW⟩ :=
    constructorProgram_runCompiled hcode hvalue hstatic htime hstack hmem hgas
      hlogs hrefund herror horigChi horigRho hcurChi hcurRho hcurAll hcoldChi hcoldRho
  have h_compile : some constructorInitPrefix = constructorProgram.compile :=
    constructorInitPrefix_compile.symm
  have h_code : sevm.code.toList = constructorInitPrefix ++ code := by
    rw [hcode, creationCode_eq_prefix_append_runtime]
  have hexec := Prog.exec_of_runCompiled_appended hProg h_compile h_code
  exact ⟨postW, hexec, houtW, herrW, hlogsW, hrowChi, hrowRho, hgasW, hrefundW, hdeleteW, hpieW, hbalW, hstateW⟩

/-- The constructor's exact two world-state writes. -/
def constructorStoredState (state : State) (ca : Adr) (time : B256) : State :=
  (state.setStorVal ca chiSlot scale).setStorVal ca rhoSlot time

/-- The constructor writes followed by runtime installation. -/
def constructorInstalledState (state : State) (ca : Adr) (time : B256) : State :=
  (constructorStoredState state ca time).setCode ca ⟨⟨code⟩⟩

structure DripInitCheckpoint (msg : Msg) (initPost : Devm) : Prop where
  state : ∃ entry : Benv,
    (processCreateMessage.msg msg).benvAfterTransfer = .ok entry ∧
    initPost.state = constructorStoredState entry.state msg.currentTarget msg.benv.stat.time
  process : processMessage (processCreateMessage.msg msg) = .ok initPost
  output : initPost.output = code
  chi : Devm.getStorVal initPost msg.currentTarget chiSlot = scale
  rho : Devm.getStorVal initPost msg.currentTarget rhoSlot = msg.benv.stat.time
  logs : initPost.logs = []
  error : initPost.error = .none
  refundCounter : initPost.refundCounter = 0
  accountsToDelete : initPost.accountsToDelete = .emptyWithCapacity
  gas : initPost.gasLeft = msg.gas - 44611
  pie : ∀ k, k ≠ chiSlot → k ≠ rhoSlot → Devm.getStorVal initPost msg.currentTarget k = 0
  bal : initPost.getBal msg.currentTarget = 0

theorem processMessage_drip_checkpoint
    (msg : Msg)
    (h_value : msg.value = 0)
    (h_codeAddress : msg.codeAddress = .none)
    (h_code : msg.code.toList = creationCode)
    (h_gas : 44611 ≤ msg.gas)
    (h_static : msg.isStatic = false)
    (h_time : msg.benv.stat.time ≠ 0)
    (h_origChi : getOrigStorVal (initSevm (processCreateMessage.msg msg)) msg.currentTarget chiSlot = 0)
    (h_origRho : getOrigStorVal (initSevm (processCreateMessage.msg msg)) msg.currentTarget rhoSlot = 0)
    (h_coldChi : ⟨msg.currentTarget, chiSlot⟩ ∉ msg.accessedStorageKeys)
    (h_coldRho : ⟨msg.currentTarget, rhoSlot⟩ ∉ msg.accessedStorageKeys)
    (h_bal : msg.benv.state.bal msg.currentTarget = 0) :
    ∃ initPost, DripInitCheckpoint msg initPost := by
  let prepared := processCreateMessage.msg msg
  obtain ⟨benv, h_transfer⟩ :=
    benvAfterTransfer_exists_zero (msg := prepared) h_value
  let seeded := prepared.withBenv benv
  have h_stat : benv.stat = msg.benv.stat := by
    calc
      benv.stat = prepared.benv.stat := benvAfterTransfer_stat h_transfer
      _ = msg.benv.stat := by rfl
  have h_seed_code : (initSevm seeded).code.toList = creationCode := h_code
  have h_seed_value : (initSevm seeded).value = 0 := h_value
  have h_seed_static : (initSevm seeded).isStatic = false := h_static
  have h_seed_time : (initSevm seeded).benvStat.time ≠ 0 := by
    have heq : (initSevm seeded).benvStat = msg.benv.stat := h_stat
    rw [heq]
    exact h_time
  have h_seed_stack : (initDevm seeded).stack = [] := rfl
  have h_seed_mem : (initDevm seeded).memory = Mem.empty := rfl
  have h_seed_gas_msg : seeded.gas = msg.gas := rfl
  have h_seed_gas : (initDevm seeded).gasLeft = (msg.gas - 44611) + 44611 := by
    show seeded.gas = (msg.gas - 44611) + 44611
    rw [h_seed_gas_msg]
    omega
  have h_seed_logs : (initDevm seeded).logs = [] := rfl
  have h_seed_refund : (initDevm seeded).refundCounter = 0 := rfl
  have h_seed_error : (initDevm seeded).error = .none := rfl
  have h_beq : (initSevm seeded).benvStat = (initSevm prepared).benvStat :=
    benvAfterTransfer_stat h_transfer
  have h_orch : getOrigStorVal (initSevm seeded) msg.currentTarget chiSlot = 0 := by
    simpa only [getOrigStorVal, getOrigAcct, h_beq] using h_origChi
  have h_orr : getOrigStorVal (initSevm seeded) msg.currentTarget rhoSlot = 0 := by
    simpa only [getOrigStorVal, getOrigAcct, h_beq] using h_origRho
  have h_benv_stor : benv.state.getStor msg.currentTarget = Stor.empty := by
    have h := congrFun (benvAfterTransfer_getStor_eq (msg := prepared) h_transfer) msg.currentTarget
    rw [h]
    exact processCreateMessage_msg_getStor_currentTarget msg
  have h_curchi : (initDevm seeded).getStorVal msg.currentTarget chiSlot = 0 := by
    show (benv.state.getStor msg.currentTarget).get chiSlot = 0
    rw [h_benv_stor]
    rfl
  have h_currho : (initDevm seeded).getStorVal msg.currentTarget rhoSlot = 0 := by
    show (benv.state.getStor msg.currentTarget).get rhoSlot = 0
    rw [h_benv_stor]
    rfl
  have h_curall : ∀ k, (initDevm seeded).getStorVal msg.currentTarget k = 0 := by
    intro k
    show (benv.state.getStor msg.currentTarget).get k = 0
    rw [h_benv_stor]
    rfl
  have h_cchi : ⟨(initSevm seeded).currentTarget, chiSlot⟩ ∉ (initDevm seeded).accessedStorageKeys := h_coldChi
  have h_crho : ⟨(initSevm seeded).currentTarget, rhoSlot⟩ ∉ (initDevm seeded).accessedStorageKeys := h_coldRho
  obtain ⟨initPost, hexecW, houtW, herrW, hlogsW, hchiW, hrhoW, hgasW, hrefundW, hdeleteW, hpieW, hbalW, hstateW⟩ :=
    constructorExec_of_walk (sevm := initSevm seeded) (pre := initDevm seeded)
      (G := msg.gas - 44611) h_seed_code h_seed_value h_seed_static h_seed_time
      h_seed_stack h_seed_mem h_seed_gas h_seed_logs h_seed_refund h_seed_error
      h_orch h_orr h_curchi h_currho h_curall h_cchi h_crho
  have hexec : exec (initEvm seeded) = .ok initPost := hexecW
  have h_seed_ca : seeded.codeAddress = .none := h_codeAddress
  have h_pm : processMessage prepared = .ok initPost :=
    processMessage_ok_of_exec h_transfer h_seed_ca hexec herrW
  have h_rho : Devm.getStorVal initPost msg.currentTarget rhoSlot = msg.benv.stat.time := by
    have heq : (initSevm seeded).benvStat.time = msg.benv.stat.time :=
      congrArg BenvStat.time h_stat
    rw [← heq]
    exact hrhoW
  have h_delete : initPost.accountsToDelete = .emptyWithCapacity := by
    rw [hdeleteW]
    rfl
  have h_initBal : (initDevm seeded).getBal msg.currentTarget = 0 := by
    have h1 : (initDevm seeded).getBal msg.currentTarget =
        benv.state.bal msg.currentTarget := rfl
    have h2 : benv.state.bal msg.currentTarget =
        prepared.benv.state.bal msg.currentTarget :=
      congrFun (benvAfterTransfer_bal_of_value_zero (msg := prepared)
        h_value h_transfer) _
    have h3 : prepared.benv.state.bal msg.currentTarget =
        msg.benv.state.bal msg.currentTarget :=
      congrFun (processCreateMessage_msg_bal_eq msg) _
    rw [h1, h2, h3]
    exact h_bal
  have h_balPost : initPost.getBal msg.currentTarget = 0 := by
    show initPost.getBal (initSevm seeded).currentTarget = 0
    rw [hbalW]
    show (initDevm seeded).getBal msg.currentTarget = 0
    exact h_initBal
  exact ⟨initPost,
    { state := ⟨benv, h_transfer, by
        change initPost.state = constructorStoredState benv.state msg.currentTarget benv.stat.time at hstateW
        rw [h_stat] at hstateW
        exact hstateW⟩
      process := h_pm
      output := houtW
      chi := hchiW
      rho := h_rho
      logs := hlogsW
      error := herrW
      refundCounter := hrefundW
      accountsToDelete := h_delete
      gas := hgasW
      pie := hpieW
      bal := h_balPost }⟩

private theorem code_cons : ∃ tail, code = 0x5b :: tail := ⟨_, rfl⟩

private theorem setMach_output_eq (d : Devm) (m : Mach) :
    (d.setMach m).output = d.output := rfl

private theorem setMach_state_eq (d : Devm) (m : Mach) :
    (d.setMach m).state = d.state := rfl

private theorem setMach_logs_eq (d : Devm) (m : Mach) :
    (d.setMach m).logs = d.logs := rfl

private theorem setMach_error_eq (d : Devm) (m : Mach) :
    (d.setMach m).error = d.error := rfl

private theorem setMach_refundCounter_eq (d : Devm) (m : Mach) :
    (d.setMach m).refundCounter = d.refundCounter := rfl

private theorem setMach_accountsToDelete_eq (d : Devm) (m : Mach) :
    (d.setMach m).accountsToDelete = d.accountsToDelete := rfl

private theorem setMach_gasLeft_eq (d : Devm) (m : Mach) :
    (d.setMach m).gasLeft = m.gasLeft := rfl



private theorem chargeCodeGas_drip_output
    {rules : ForkRules} {d : Devm}
    (h_output : d.output = code)
    (h_gas : 352400 ≤ d.gasLeft)
    (h_max : 1762 ≤ rules.code.maxCodeSize) :
    processCreateMessage.chargeCodeGas rules d =
      .ok (d.setMach ⟨d.stack, d.memory, d.gasLeft - 352400⟩) := by
  obtain ⟨tail, hcons⟩ := code_cons
  have hlen : code.length = 1762 := codeSize_exact
  unfold processCreateMessage.chargeCodeGas
  rw [h_output, hcons]
  rw [hcons] at hlen
  simp only [List.length_cons] at hlen
  simp only [List.length_cons, hlen, gasCodeDeposit]
  rw [chargeGas_eq_ok h_gas]
  change ((if rules.code.maxCodeSize < 1762 then
      Except.error ⟨.halt (.outOfGas .none), _⟩
    else Except.ok _) : Execution) = Except.ok _
  rw [if_neg (by omega)]

structure DripCodeGasCheckpoint (rules : ForkRules) (d : Devm) (charged : Devm) : Prop where
  charge : processCreateMessage.chargeCodeGas rules d = .ok charged
  output : charged.output = code
  state : charged.state = d.state
  logs : charged.logs = d.logs
  error : charged.error = d.error
  refundCounter : charged.refundCounter = d.refundCounter
  accountsToDelete : charged.accountsToDelete = d.accountsToDelete
  gas : charged.gasLeft = d.gasLeft - 352400

theorem chargeCodeGas_drip_checkpoint
    {rules : ForkRules} {d : Devm}
    (h_output : d.output = code)
    (h_gas : 352400 ≤ d.gasLeft)
    (h_max : 1762 ≤ rules.code.maxCodeSize) :
    ∃ charged, DripCodeGasCheckpoint rules d charged := by
  let m : Mach := ⟨d.stack, d.memory, d.gasLeft - 352400⟩
  have hm : processCreateMessage.chargeCodeGas rules d = .ok (d.setMach m) := by
    simpa only [m] using chargeCodeGas_drip_output h_output h_gas h_max
  obtain ⟨charged, hc⟩ : ∃ charged, processCreateMessage.chargeCodeGas rules d = .ok charged := ⟨d.setMach m, hm⟩
  have heq : charged = d.setMach m := Except.ok.inj (hc.symm.trans hm)
  have hout : charged.output = d.output := by
    rw [heq]
    exact setMach_output_eq d m
  have hst : charged.state = d.state := by
    rw [heq]
    exact setMach_state_eq d m
  have hlogs : charged.logs = d.logs := by
    rw [heq]
    exact setMach_logs_eq d m
  have herr : charged.error = d.error := by
    rw [heq]
    exact setMach_error_eq d m
  have href : charged.refundCounter = d.refundCounter := by
    rw [heq]
    exact setMach_refundCounter_eq d m
  have hdel : charged.accountsToDelete = d.accountsToDelete := by
    rw [heq]
    exact setMach_accountsToDelete_eq d m
  have hgas : charged.gasLeft = d.gasLeft - 352400 := by
    have hmg : charged.gasLeft = m.gasLeft := by
      rw [heq]
      exact setMach_gasLeft_eq d m
    exact hmg.trans (by rfl)
  exact ⟨charged, hc, hout.trans h_output, hst, hlogs, herr, href, hdel, hgas⟩

structure DripChargeCheckpoint (msg : Msg) (charged : Devm) : Prop where
  state : ∃ entry : Benv,
    (processCreateMessage.msg msg).benvAfterTransfer = .ok entry ∧
    charged.state = constructorStoredState entry.state msg.currentTarget msg.benv.stat.time
  process :
    processCreateMessage msg =
      .ok (charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩)
  output : charged.output = code
  chi : Devm.getStorVal charged msg.currentTarget chiSlot = scale
  rho : Devm.getStorVal charged msg.currentTarget rhoSlot = msg.benv.stat.time
  logs : charged.logs = []
  error : charged.error = .none
  refundCounter : charged.refundCounter = 0
  accountsToDelete : charged.accountsToDelete = .emptyWithCapacity
  gas : charged.gasLeft = msg.gas - 44611 - 352400
  pie : ∀ k, k ≠ chiSlot → k ≠ rhoSlot → Devm.getStorVal charged msg.currentTarget k = 0
  bal : charged.getBal msg.currentTarget = 0

theorem processCreateMessage_drip_charge_checkpoint
    (msg : Msg) {initPost : Devm}
    (init : DripInitCheckpoint msg initPost)
    (h_gas : 44611 + 352400 ≤ msg.gas)
    (h_max : 1762 ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ charged, DripChargeCheckpoint msg charged := by
  have h_deposit : 352400 ≤ initPost.gasLeft := by
    rw [init.gas]
    omega
  obtain ⟨charged, checkpoint⟩ :=
    chargeCodeGas_drip_checkpoint (rules := msg.benv.stat.rules) (d := initPost)
      init.output h_deposit h_max
  have h_chi : Devm.getStorVal charged msg.currentTarget chiSlot = scale := by
    show (charged.state.getStor msg.currentTarget).get chiSlot = scale
    rw [checkpoint.state]
    exact init.chi
  have h_rho : Devm.getStorVal charged msg.currentTarget rhoSlot = msg.benv.stat.time := by
    show (charged.state.getStor msg.currentTarget).get rhoSlot = msg.benv.stat.time
    rw [checkpoint.state]
    exact init.rho
  have h_pie : ∀ k, k ≠ chiSlot → k ≠ rhoSlot → Devm.getStorVal charged msg.currentTarget k = 0 := by
    intro k hkc hkr
    show (charged.state.getStor msg.currentTarget).get k = 0
    rw [checkpoint.state]
    exact init.pie k hkc hkr
  have h_gas_charged : charged.gasLeft = msg.gas - 44611 - 352400 := by
    rw [checkpoint.gas, init.gas]
  have h_bal : charged.getBal msg.currentTarget = 0 := by
    have h : (charged.state.get msg.currentTarget).bal =
        (initPost.state.get msg.currentTarget).bal := by
      rw [checkpoint.state]
    show (charged.state.get msg.currentTarget).bal = 0
    rw [h]
    exact init.bal
  exact ⟨charged,
    { state := by
        obtain ⟨entry, hentry, hstate⟩ := init.state
        exact ⟨entry, hentry, checkpoint.state.trans hstate⟩
      process :=
        processCreateMessage_ok_of_processMessage_and_charge msg
          init.process init.error checkpoint.charge
      output := checkpoint.output
      chi := h_chi
      rho := h_rho
      logs := checkpoint.logs.trans init.logs
      error := checkpoint.error.trans init.error
      refundCounter := checkpoint.refundCounter.trans init.refundCounter
      accountsToDelete := checkpoint.accountsToDelete.trans init.accountsToDelete
      gas := h_gas_charged
      pie := h_pie
      bal := h_bal }⟩

private theorem dripInstalledPost_certificate
    (msg : Msg) {charged : Devm}
    (h_process :
      processCreateMessage msg =
        .ok (charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩))
    (h_output : charged.output = code)
    (h_chi : Devm.getStorVal charged msg.currentTarget chiSlot = scale)
    (h_rho : Devm.getStorVal charged msg.currentTarget rhoSlot = msg.benv.stat.time)
    (h_pie : ∀ k, k ≠ chiSlot → k ≠ rhoSlot → Devm.getStorVal charged msg.currentTarget k = 0)
    (h_logs : charged.logs = [])
    (h_error : charged.error = .none)
    (h_refund : charged.refundCounter = 0)
    (h_delete : charged.accountsToDelete = .emptyWithCapacity)
    (h_gas : charged.gasLeft = msg.gas - 44611 - 352400)
    (h_bal : charged.getBal msg.currentTarget = 0) :
    ∃ post,
      processCreateMessage msg = .ok post ∧
      post.getCode msg.currentTarget = ⟨⟨code⟩⟩ ∧
      Devm.getStorVal post msg.currentTarget chiSlot = scale ∧
      Devm.getStorVal post msg.currentTarget rhoSlot = msg.benv.stat.time ∧
      (∀ k, k ≠ chiSlot → k ≠ rhoSlot → Devm.getStorVal post msg.currentTarget k = 0) ∧
      post.logs = [] ∧
      post.output = code ∧
      post.gasLeft = msg.gas - 44611 - 352400 ∧
      post.error = .none ∧
      post.refundCounter = 0 ∧
      post.accountsToDelete = .emptyWithCapacity ∧
      post.getBal msg.currentTarget = 0 := by
  refine ⟨charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩,
    h_process, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Devm.getCode Devm.getAcct
    rw [Devm.setCode_state]
    unfold State.setCode
    rw [State.get_set_self]
    simp only [h_output]
  · change ((charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩).state.getStor
        msg.currentTarget).get chiSlot = scale
    rw [Devm.setCode_state]
    change (((charged.state.setCode msg.currentTarget
        ⟨⟨charged.output⟩⟩).get msg.currentTarget).stor).get chiSlot = scale
    rw [State.setCode_get_stor]
    exact h_chi
  · change ((charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩).state.getStor
        msg.currentTarget).get rhoSlot = msg.benv.stat.time
    rw [Devm.setCode_state]
    change (((charged.state.setCode msg.currentTarget
        ⟨⟨charged.output⟩⟩).get msg.currentTarget).stor).get rhoSlot = msg.benv.stat.time
    rw [State.setCode_get_stor]
    exact h_rho
  · intro k hkc hkr
    change ((charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩).state.getStor
        msg.currentTarget).get k = 0
    rw [Devm.setCode_state]
    change (((charged.state.setCode msg.currentTarget
        ⟨⟨charged.output⟩⟩).get msg.currentTarget).stor).get k = 0
    rw [State.setCode_get_stor]
    exact h_pie k hkc hkr
  · exact h_logs
  · exact h_output
  · exact h_gas
  · exact h_error
  · exact h_refund
  · exact h_delete
  · show ((charged.state.setCode msg.currentTarget
        ⟨⟨charged.output⟩⟩).get msg.currentTarget).bal = 0
    rw [State.setCode_get_bal]
    exact h_bal

theorem processCreateMessage_drip_success
    (msg : Msg)
    (h_value : msg.value = 0)
    (h_codeAddress : msg.codeAddress = .none)
    (h_code : msg.code.toList = creationCode)
    (h_gas : 44611 + 352400 ≤ msg.gas)
    (h_static : msg.isStatic = false)
    (h_time : msg.benv.stat.time ≠ 0)
    (h_origChi : getOrigStorVal (initSevm (processCreateMessage.msg msg)) msg.currentTarget chiSlot = 0)
    (h_origRho : getOrigStorVal (initSevm (processCreateMessage.msg msg)) msg.currentTarget rhoSlot = 0)
    (h_coldChi : ⟨msg.currentTarget, chiSlot⟩ ∉ msg.accessedStorageKeys)
    (h_coldRho : ⟨msg.currentTarget, rhoSlot⟩ ∉ msg.accessedStorageKeys)
    (h_max : 1762 ≤ msg.benv.stat.rules.code.maxCodeSize)
    (h_bal : msg.benv.state.bal msg.currentTarget = 0) :
    ∃ post,
      processCreateMessage msg = .ok post ∧
      post.getCode msg.currentTarget = ⟨⟨code⟩⟩ ∧
      Devm.getStorVal post msg.currentTarget chiSlot = scale ∧
      Devm.getStorVal post msg.currentTarget rhoSlot = msg.benv.stat.time ∧
      (∀ k, k ≠ chiSlot → k ≠ rhoSlot → Devm.getStorVal post msg.currentTarget k = 0) ∧
      post.logs = [] ∧
      post.output = code ∧
      post.gasLeft = msg.gas - 44611 - 352400 ∧
      post.error = .none ∧
      post.refundCounter = 0 ∧
      post.accountsToDelete = .emptyWithCapacity ∧
      post.getBal msg.currentTarget = 0 ∧
      (∃ entry : Benv,
        (processCreateMessage.msg msg).benvAfterTransfer = .ok entry ∧
        post.state = constructorInstalledState entry.state msg.currentTarget msg.benv.stat.time) := by
  obtain ⟨initPost, init⟩ :=
    processMessage_drip_checkpoint msg h_value h_codeAddress h_code
      (by omega) h_static h_time h_origChi h_origRho h_coldChi h_coldRho h_bal
  obtain ⟨chargedPost, charged⟩ :=
    processCreateMessage_drip_charge_checkpoint msg init h_gas h_max
  obtain ⟨post, hrun, hcode, hchi, hrho, hpie, hlogs, houtput, hgas,
      herror, hrefund, hdelete, hbal⟩ :=
    dripInstalledPost_certificate msg charged.process charged.output
      charged.chi charged.rho charged.pie charged.logs charged.error charged.refundCounter
      charged.accountsToDelete charged.gas charged.bal
  have hpost : post = chargedPost.setCode msg.currentTarget ⟨⟨chargedPost.output⟩⟩ :=
    Except.ok.inj (hrun.symm.trans charged.process)
  obtain ⟨entry, hentry, hstate⟩ := charged.state
  refine ⟨post, hrun, hcode, hchi, hrho, hpie, hlogs, houtput, hgas,
    herror, hrefund, hdelete, hbal, entry, hentry, ?_⟩
  rw [hpost, Devm.setCode_state, hstate, charged.output]
  rfl

/-! ## F4c: schedule-parametric deployment root

Mirror of the `Weth10DeploymentRoot` pipeline over `cfg : ChainConfig`,
consuming `processCreateMessage_drip_success` and the shared
`DeploymentMessage` defs directly (no contract-local aliases). The creation
transaction and receipt are included per SF §2. Beyond the WETH10 envelope
shape, DRIP needs three honest well-formedness fields: `timestamp_ne_zero`
(the TIMESTAMP-reading constructor needs nonzero time for its gas-exact
cold-store accounting), `coinbase_ne_target` and `target_zeroBalance` (the
zero-balance projection needs both; the fixture generator chooses a fresh
destination per SF §2). There are no `Stable`/backing/flash carriers at G2,
so the suffix carries no preservation rungs and the root projects
installed/chi/rho/pie/balance/logs/receipt facts plus `ReachUsing` refl;
reachable-state projections are G6 scope. -/

/-- Closed successful-path accounting inside a direct DRIP creation message:
constructor execution plus runtime code deposit. -/
def dripCreateMessageGasAccounting : Nat :=
  44611 + 352400

theorem dripCreateMessageGasAccounting_eq :
    dripCreateMessageGasAccounting = 44611 + 352400 := rfl

/-- The canonical transaction budget crosses both EIP-7623's calldata floor
and the constructor's independently proved execution/deposit accounting. -/
def deploymentTransactionGasBound (tx : Tx) : Nat :=
  max (deploymentCalldataFloorGas tx)
    (deploymentIntrinsicGas tx + dripCreateMessageGasAccounting)

/-- Valid configured base state and collision-free target facts. The four
system-address fields describe only pre-state code; no system-call result or
post-state is admitted here. `target_zeroBalance` is consumed by the Balance
projection; there is no founded-sum premise at G2 (sums arrive with R2/G4). -/
structure CanonicalDeploymentBase
    (cfg : ChainConfig) (rules : ForkRules)
    (base : BlockChain) (sender ca : Adr) : Prop where
  configValid : cfg.Valid
  chainId_eq : cfg.chainId = base.chainId
  validContext : base.ValidContext
  target_eq : ca = computeContractAddress sender (base.state.getNonce sender)
  target_ne_zero : ca ≠ 0
  target_not_precompile : ∀ {timestamp selected},
    cfg.rulesAt timestamp = .ok selected → ¬ selected.isPrecomp ca
  beacon_not_precompile : ¬ rules.isPrecomp beaconRootsAddress
  history_not_precompile : ¬ rules.isPrecomp historyStorageAddress
  withdrawalRequest_not_precompile :
    ¬ rules.isPrecomp withdrawalRequestPredeployAddress
  consolidationRequest_not_precompile :
    ¬ rules.isPrecomp consolidationRequestPredeployAddress
  sender_ne_target : sender ≠ ca
  withdrawalRequest_ne_target : withdrawalRequestPredeployAddress ≠ ca
  consolidationRequest_ne_target : consolidationRequestPredeployAddress ≠ ca
  target_noCodeOrNonce : accountHasCodeOrNonce base.state ca = false
  target_noStorage : accountHasStorage base.state ca = false
  target_zeroBalance : base.state.bal ca = 0
  lastBlockHash : ∃ lastHash,
    List.getLast? (getLast256BlockHashes base) = some lastHash
  beaconCode :
    some (base.state.getCode beaconRootsAddress).toList =
      Prog.compile deploymentSystemProgram
  historyCode :
    some (base.state.getCode historyStorageAddress).toList =
      Prog.compile deploymentSystemProgram
  withdrawalRequestCode :
    some (base.state.getCode withdrawalRequestPredeployAddress).toList =
      Prog.compile deploymentSystemProgram
  consolidationRequestCode :
    some (base.state.getCode consolidationRequestPredeployAddress).toList =
      Prog.compile deploymentSystemProgram

/-- A strict configured block and type-2 creation transaction profile. The
`CanonicalBlock` parameter itself retains the original bytes, strict
`rlpToBlock` equation, and exact re-encoding equation. Every field below is
available before execution. -/
structure CanonicalDripDeploymentBlock
    (cfg : ChainConfig) (rules : ForkRules)
    (base : BlockChain) (cb : CanonicalBlock)
    (deploymentTxBytes : Bytes) (deploymentTx : Tx)
    (sender ca : Adr) : Prop where
  txs_eq : cb.block.txs = [.inl deploymentTxBytes]
  decode_eq : decodeTx (.inl deploymentTxBytes) = .ok deploymentTx
  ommers_eq : cb.block.ommers = []
  withdrawals_eq : cb.block.wds = []
  rulesAt : cfg.rulesAt cb.block.header.timestamp = .ok rules
  type_eq : ∃ maxPriorityFee maxFee,
    deploymentTx.type = .two cfg.chainId maxPriorityFee maxFee none []
  value_eq : deploymentTx.value = 0
  data_eq : deploymentTx.data = creationCode
  nonce_eq : deploymentTx.nonce = base.state.getNonce sender
  nonce_not_max : deploymentTx.nonce ≠ UInt64.max
  recoveredSender : recoverSender cfg.chainId deploymentTx = .ok sender
  validated : validateTransaction rules deploymentTx =
    .ok (calculateIntrinsicCost deploymentTx)
  checked :
    let benv := initBenv rules base cb.block.header
    checkTransaction benv.beginTransaction
      (deploymentTxPreludeBout .init deploymentTx 0) deploymentTx =
      .ok (sender, deploymentEffectiveGasPrice benv deploymentTx, [], 0)
  base_fee_le_effective :
    cb.block.header.baseFeePerGas ≤
      deploymentEffectiveGasPrice
        (initBenv rules base cb.block.header) deploymentTx
  upfront_funded :
    deploymentTx.gas *
        deploymentEffectiveGasPrice
          (initBenv rules base cb.block.header) deploymentTx ≤
      (base.state.bal sender).toNat
  gas_bound : deploymentTransactionGasBound deploymentTx ≤ deploymentTx.gas
  runtime_code_fits : 1762 ≤ rules.code.maxCodeSize
  block_gas_room :
    deploymentTx.gas ≤ cb.block.header.gasLimit
  timestamp_ne_zero : cb.block.header.timestamp.toB256 ≠ 0
  coinbase_ne_target : cb.block.header.coinbase ≠ ca
  target_eq : ca = computeContractAddress sender deploymentTx.nonce

/-! ## Proof-produced pipeline contexts -/

/-- The mandatory beacon-roots and history-storage calls recovered from the
real block prefix. Conclusion evidence, never input data. Field order follows
the DRIP proof narrative (beacon pair, history pair, boundary equations). -/
structure DeploymentSystemPrefix
    (rules : ForkRules)
    (base : BlockChain) (block : Block) (txInput : Benv) : Type where
  outBeacon : MsgCallOutput
  stBeacon : State
  lastHash : B256
  outHistory : MsgCallOutput
  stHistory : State
  beaconRun :
    processUncheckedSystemTransaction
      (initBenv rules base block.header)
      beaconRootsAddress block.header.parentBeaconBlockRoot.toBytes =
      .ok (stBeacon, outBeacon)
  lastHashEq :
    List.getLast?
      ((initBenv rules base block.header).withState stBeacon).stat.blockHashes =
        some lastHash
  historyRun :
      processUncheckedSystemTransaction
      ((initBenv rules base block.header).withState stBeacon)
      historyStorageAddress lastHash.toBytes = .ok (stHistory, outHistory)
  txInput_eq :
    txInput =
      ((initBenv rules base block.header).withState stBeacon).withState
        stHistory
  environment_eq : txInput = initBenv rules base block.header
  state_eq : txInput.state = base.state
  createdAccounts_eq : txInput.createdAccounts = .emptyWithCapacity

/-- Reconstruct the mandatory beacon-roots and history-storage prefix from the
canonical pre-state; neither call is smuggled into the input record. -/
theorem canonicalDeploymentSystemPrefix
    (cfg : ChainConfig) (rules : ForkRules)
    (base : BlockChain) (cb : CanonicalBlock)
    (sender ca : Adr)
    (hbase : CanonicalDeploymentBase cfg rules base sender ca) :
    Nonempty (Σ txInput, DeploymentSystemPrefix rules base cb.block txInput) := by
  classical
  have hbeaconRun := processUncheckedSystemTransaction_deploymentSystemProgram
    (initBenv rules base cb.block.header)
    beaconRootsAddress cb.block.header.parentBeaconBlockRoot.toBytes
    (by simpa [initBenv] using hbase.beaconCode)
    hbase.beacon_not_precompile
  obtain ⟨outBeacon, hbeaconEq, _, _, _, _, _⟩ := hbeaconRun
  obtain ⟨lastHash, hlast⟩ := hbase.lastBlockHash
  have hhistoryRun := processUncheckedSystemTransaction_deploymentSystemProgram
    ((initBenv rules base cb.block.header).withState base.state)
    historyStorageAddress lastHash.toBytes
    (by simpa [initBenv, Benv.withState] using hbase.historyCode)
    hbase.history_not_precompile
  obtain ⟨outHistory, hhistoryEq, _, _, _, _, _⟩ := hhistoryRun
  refine ⟨⟨_, {
    outBeacon := outBeacon
    stBeacon := base.state
    lastHash := lastHash
    outHistory := outHistory
    stHistory := base.state
    beaconRun := hbeaconEq
    lastHashEq := by
      simpa [initBenv, initBenvStat, Benv.withState] using hlast
    historyRun := by
      simpa [Benv.withState] using hhistoryEq
    txInput_eq := rfl
    environment_eq := rfl
    state_eq := rfl
    createdAccounts_eq := rfl }⟩⟩

/-- The transaction contexts are kept distinct: recovered prefix input,
`beginTransaction`, nonce/fee-updated state, and the actual prepared message.
Collision freedom is stated at exactly `msg.benv.state`. The DRIP extras
(`msg_isStatic_eq`, cold keys, `msg_time_ne_zero`, orig-storage, `msg_balZero`)
are exactly the premises `processCreateMessage_drip_success` needs beyond the
WETH10 shape. -/
structure PreparedDeploymentContext
    (cfg : ChainConfig) (rules : ForkRules)
    (base : BlockChain) (cb : CanonicalBlock)
    (deploymentTx : Tx) (sender ca : Adr) : Type where
  txInput : Benv
  begun : Benv
  debit : State
  tenv : Tenv
  msg : Msg
  systemPrefix : DeploymentSystemPrefix rules base cb.block txInput
  begun_eq : begun = txInput.beginTransaction
  debit_eq :
    (begun.state.incrNonce sender).subBal sender
      (deploymentTx.gas *
        deploymentEffectiveGasPrice txInput deploymentTx).toB256 = some debit
  tenv_eq : tenv = deploymentTenv txInput deploymentTx sender 0
  prepare_eq : prepareMessage {begun with state := debit} tenv deploymentTx =
    .ok msg
  msg_benv_eq : msg.benv = {begun with state := debit}
  msg_caller_eq : msg.caller = sender
  msg_target_eq : msg.target = none
  msg_gas_eq : msg.gas = deploymentTx.gas - deploymentIntrinsicGas deploymentTx
  msg_value_eq : msg.value = 0
  msg_data_eq : msg.data = []
  msg_code_eq : msg.code.toList = creationCode
  msg_codeAddress_eq : msg.codeAddress = none
  msg_isStatic_eq : msg.isStatic = false
  msg_shouldTransferValue_eq : msg.shouldTransferValue = true
  msg_auths_eq : msg.tenv.stat.auths = []
  msg_rules_eq : msg.benv.stat.rules = rules
  msg_chainId_eq : msg.benv.stat.chainId = cfg.chainId
  msg_coldChi : ⟨msg.currentTarget, chiSlot⟩ ∉ msg.accessedStorageKeys
  msg_coldRho : ⟨msg.currentTarget, rhoSlot⟩ ∉ msg.accessedStorageKeys
  msg_time_ne_zero : msg.benv.stat.time ≠ 0
  msg_time_eq : msg.benv.stat.time = cb.block.header.timestamp.toB256
  msg_origChi : getOrigStorVal (initSevm (processCreateMessage.msg msg))
    msg.currentTarget chiSlot = 0
  msg_origRho : getOrigStorVal (initSevm (processCreateMessage.msg msg))
    msg.currentTarget rhoSlot = 0
  msg_balZero : msg.benv.state.bal msg.currentTarget = 0
  target_eq : msg.currentTarget = ca
  noCodeOrNonce : accountHasCodeOrNonce msg.benv.state ca = false
  noStorage : accountHasStorage msg.benv.state ca = false

/-- Produce the real transaction input, transaction-local origin boundary,
upfront nonce/fee debit, and the message returned by `prepareMessage`.
Collision freedom is derived at that message's own state. -/
theorem prepareCanonicalDeploymentContext
    (cfg : ChainConfig) (rules : ForkRules)
    (base : BlockChain) (cb : CanonicalBlock)
    (deploymentTx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase cfg rules base sender ca)
    (henv : CanonicalDripDeploymentBlock cfg rules base cb
      deploymentTxBytes deploymentTx sender ca) :
    Nonempty
      (PreparedDeploymentContext cfg rules base cb deploymentTx sender ca) := by
  obtain ⟨⟨txInput, hprefix⟩⟩ :=
    canonicalDeploymentSystemPrefix cfg rules base cb sender ca hbase
  let begun := txInput.beginTransaction
  let fee := deploymentTx.gas *
    deploymentEffectiveGasPrice txInput deploymentTx
  have hbegun_state : begun.state = base.state := by
    simpa [begun, Benv.beginTransaction] using hprefix.state_eq
  have hprice : deploymentEffectiveGasPrice txInput deploymentTx =
      deploymentEffectiveGasPrice
        (initBenv rules base cb.block.header) deploymentTx := by
    rw [hprefix.txInput_eq]
    rfl
  have hfee_le : fee ≤ (begun.state.bal sender).toNat := by
    rw [hbegun_state]
    simpa [fee, hprice] using henv.upfront_funded
  have hfee_lt : fee < 2 ^ 256 :=
    hfee_le.trans_lt (B256.toNat_lt _)
  have hfeeEncoded : fee.toB256.toNat = fee :=
    B256.toNat_toB256_of_lt hfee_lt
  have hnotlt : ¬ (begun.state.incrNonce sender).bal sender <
      fee.toB256 := by
    rw [B256.lt_iff_toNat_lt_toNat, hfeeEncoded]
    change ¬ ((begun.state.incrNonce sender).get sender).bal.toNat < fee
    rw [State.incrNonce_get_bal]
    exact not_lt_of_ge hfee_le
  let debit := (begun.state.incrNonce sender).setBal sender
    ((begun.state.incrNonce sender).bal sender - fee.toB256)
  have hdebit :
      (begun.state.incrNonce sender).subBal sender fee.toB256 =
        some debit := by
    unfold State.subBal
    rw [if_neg hnotlt]
  let tenv := deploymentTenv txInput deploymentTx sender 0
  let currentTarget :=
    computeContractAddress tenv.stat.origin
      (debit.getNonce tenv.stat.origin - 1)
  let msgBenv : Benv := {begun with state := debit}
  let msg : Msg :=
    { benv := msgBenv
      tenv := tenv
      caller := tenv.stat.origin
      target := deploymentTx.type.receiver?
      gas := tenv.stat.gas
      value := deploymentTx.value.toB256
      data := []
      code := .mk (.mk deploymentTx.data)
      depth := 1024
      currentTarget := currentTarget
      codeAddress := none
      shouldTransferValue := true
      isStatic := false
      accessedAddresses := tenv.stat.accessListAddresses.insertMany
        (msgBenv.stat.rules.precompiles ++ [tenv.stat.origin, currentTarget])
      accessedStorageKeys := tenv.stat.accessListStorageKeys
      disablePrecompiles := false }
  obtain ⟨maxPriorityFee, maxFee, htype⟩ := henv.type_eq
  have hreceiver : deploymentTx.type.receiver? = none := by
    rw [htype]
    rfl
  have hprepare : prepareMessage msgBenv tenv deploymentTx = .ok msg := by
    unfold prepareMessage
    rw [hreceiver]
    simp [msg, msgBenv, currentTarget, hreceiver]
  have hdebit_nonce :
      debit.getNonce sender = base.state.getNonce sender + 1 := by
    dsimp only [debit]
    change (((begun.state.incrNonce sender).setBal sender _).get sender).nonce =
      base.state.getNonce sender + 1
    rw [State.setBal_get_self]
    change ((begun.state.incrNonce sender).get sender).nonce =
      base.state.getNonce sender + 1
    unfold State.incrNonce
    rw [State.get_set_self]
    change begun.state.getNonce sender + 1 = base.state.getNonce sender + 1
    rw [hbegun_state]
  have htarget : msg.currentTarget = ca := by
    dsimp only [msg, currentTarget]
    change computeContractAddress sender (debit.getNonce sender - 1) = ca
    rw [hdebit_nonce]
    simp
    exact hbase.target_eq.symm
  have htx_chain : txInput.stat.chainId = base.chainId := by
    rw [hprefix.txInput_eq]
    rfl
  have htx_rules : txInput.stat.rules = rules := by
    rw [hprefix.txInput_eq]
    rfl
  have hmsg_chain : msg.benv.stat.chainId = cfg.chainId := by
    dsimp only [msg, msgBenv, begun]
    simpa [Benv.beginTransaction] using
      htx_chain.trans hbase.chainId_eq.symm
  have hmsg_rules : msg.benv.stat.rules = rules := by
    dsimp only [msg, msgBenv, begun]
    simpa [Benv.beginTransaction] using htx_rules
  have hdebit_ca : debit.get ca = base.state.get ca := by
    dsimp only [debit]
    rw [State.setBal_get_ne hbase.sender_ne_target]
    unfold State.incrNonce
    rw [State.get_set_ne _ hbase.sender_ne_target]
    rw [hbegun_state]
  have hnocode : accountHasCodeOrNonce msg.benv.state ca = false := by
    dsimp only [msg, msgBenv]
    have hpre := hbase.target_noCodeOrNonce
    unfold accountHasCodeOrNonce at hpre ⊢
    simpa [State.getNonce, State.getCode, hdebit_ca] using hpre
  have hnostor : accountHasStorage msg.benv.state ca = false := by
    dsimp only [msg, msgBenv]
    have hpre := hbase.target_noStorage
    unfold accountHasStorage at hpre ⊢
    simpa [State.getStor, hdebit_ca] using hpre
  have hempty : base.state.getStor ca = Stor.empty := by
    have hisEmpty : (base.state.getStor ca).isEmpty = true := by
      have hpre := hbase.target_noStorage
      unfold accountHasStorage at hpre
      simpa using hpre
    exact Std.TreeMap.eq_empty_of_isEmpty hisEmpty
  have horig_state : (processCreateMessage.msg msg).benv.stat.origState =
      base.state := by
    have e1 : (processCreateMessage.msg msg).benv.stat = msg.benv.stat := rfl
    have e2 : msg.benv.stat = begun.stat := rfl
    have e3 : begun.stat.origState = txInput.state := rfl
    rw [e1, e2, e3, hprefix.state_eq]
  have horig_empty : ((processCreateMessage.msg msg).benv.stat.origState.get
      msg.currentTarget).stor = Stor.empty := by
    rw [horig_state, htarget]
    exact hempty
  have horigChi : getOrigStorVal (initSevm (processCreateMessage.msg msg))
      msg.currentTarget chiSlot = 0 := by
    show ((processCreateMessage.msg msg).benv.stat.origState.get
      msg.currentTarget).stor.get chiSlot = 0
    rw [horig_empty]
    rfl
  have horigRho : getOrigStorVal (initSevm (processCreateMessage.msg msg))
      msg.currentTarget rhoSlot = 0 := by
    show ((processCreateMessage.msg msg).benv.stat.origState.get
      msg.currentTarget).stor.get rhoSlot = 0
    rw [horig_empty]
    rfl
  have htime : msg.benv.stat.time = cb.block.header.timestamp.toB256 := by
    have e1 : msg.benv.stat = begun.stat := rfl
    have e2 : begun.stat.time = txInput.stat.time := by
      simp only [begun, Benv.beginTransaction]
    have e3 : txInput.stat.time = cb.block.header.timestamp.toB256 := by
      rw [hprefix.environment_eq]
      rfl
    rw [e1, e2, e3]
  have hcoldKeys : msg.accessedStorageKeys = tenv.stat.accessListStorageKeys :=
    rfl
  have hcoldEmpty : tenv.stat.accessListStorageKeys = .ofList [] := rfl
  have hcoldChi : ⟨msg.currentTarget, chiSlot⟩ ∉ msg.accessedStorageKeys := by
    rw [hcoldKeys, hcoldEmpty, Std.HashSet.mem_ofList]
    simp
  have hcoldRho : ⟨msg.currentTarget, rhoSlot⟩ ∉ msg.accessedStorageKeys := by
    rw [hcoldKeys, hcoldEmpty, Std.HashSet.mem_ofList]
    simp
  have hbalZero : msg.benv.state.bal msg.currentTarget = 0 := by
    have e : msg.benv.state = debit := rfl
    rw [e, htarget]
    show (debit.get ca).bal = 0
    rw [hdebit_ca]
    exact hbase.target_zeroBalance
  exact ⟨{
    txInput := txInput
    begun := begun
    debit := debit
    tenv := tenv
    msg := msg
    systemPrefix := hprefix
    begun_eq := rfl
    debit_eq := by simpa [fee] using hdebit
    tenv_eq := rfl
    prepare_eq := hprepare
    msg_benv_eq := rfl
    msg_caller_eq := rfl
    msg_target_eq := by simpa [msg] using hreceiver
    msg_gas_eq := rfl
    msg_value_eq := by
      rw [show msg.value = deploymentTx.value.toB256 from rfl,
        henv.value_eq]
      decide
    msg_data_eq := rfl
    msg_code_eq := by
      rw [show msg.code = .mk (.mk deploymentTx.data) from rfl,
        henv.data_eq, ByteArray.toList_eq_toList_data]
    msg_codeAddress_eq := rfl
    msg_isStatic_eq := rfl
    msg_shouldTransferValue_eq := rfl
    msg_auths_eq := rfl
    msg_rules_eq := hmsg_rules
    msg_chainId_eq := hmsg_chain
    msg_coldChi := hcoldChi
    msg_coldRho := hcoldRho
    msg_time_ne_zero := by rw [htime]; exact henv.timestamp_ne_zero
    msg_time_eq := htime
    msg_origChi := horigChi
    msg_origRho := horigRho
    msg_balZero := hbalZero
    target_eq := htarget
    noCodeOrNonce := hnocode
    noStorage := hnostor
  }⟩

structure CanonicalDeploymentMessageResult
    (cfg : ChainConfig) (rules : ForkRules) (ca : Adr)
    (ctx : PreparedDeploymentContext cfg rules base cb deploymentTx sender ca)
    (post : State) (out : MsgCallOutput) : Prop where
  run : processMessageCall ctx.msg = .ok (post, out)
  state : ∃ entry : Benv,
    (processCreateMessage.msg ctx.msg).benvAfterTransfer = .ok entry ∧
    post = constructorInstalledState entry.state ca ctx.msg.benv.stat.time
  installed : post.getCode ca = ⟨⟨code⟩⟩
  chi : (post.getStor ca).get chiSlot = scale
  rho : (post.getStor ca).get rhoSlot = ctx.msg.benv.stat.time
  pie : ∀ k, k ≠ chiSlot → k ≠ rhoSlot → (post.getStor ca).get k = 0
  bal : post.bal ca = 0
  logs : out.logs = []
  returnData : out.returnData = code
  gasLeft : out.gasLeft = ctx.msg.gas - 44611 - 352400
  error : out.error = none
  refundCounter : out.refundCounter = 0
  accountsToDelete : out.accountsToDelete = .emptyWithCapacity
  withdrawalRequestCode :
    some (post.getCode withdrawalRequestPredeployAddress).toList =
      Prog.compile deploymentSystemProgram
  consolidationRequestCode :
    some (post.getCode consolidationRequestPredeployAddress).toList =
      Prog.compile deploymentSystemProgram

/-- The prepared creation message takes the direct-create arm, passes the
collision checks at its own state, executes the real DRIP constructor, and
packages the exact successful message-call output. -/
theorem canonicalDeploymentMessage_succeeds
    (cfg : ChainConfig) (rules : ForkRules)
    (base : BlockChain) (cb : CanonicalBlock)
    (deploymentTx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase cfg rules base sender ca)
    (henv : CanonicalDripDeploymentBlock cfg rules base cb
      deploymentTxBytes deploymentTx sender ca)
    (ctx : PreparedDeploymentContext cfg rules base cb deploymentTx sender ca) :
    ∃ post out, CanonicalDeploymentMessageResult cfg rules ca ctx post out := by
  have htotal : deploymentIntrinsicGas deploymentTx +
      dripCreateMessageGasAccounting ≤ deploymentTx.gas :=
    (le_max_right _ _).trans henv.gas_bound
  have hgas : 44611 + 352400 ≤ ctx.msg.gas := by
    rw [dripCreateMessageGasAccounting_eq] at htotal
    rw [ctx.msg_gas_eq]
    omega
  have hmax : 1762 ≤ ctx.msg.benv.stat.rules.code.maxCodeSize := by
    rw [ctx.msg_rules_eq]
    exact henv.runtime_code_fits
  obtain ⟨post, hcreate, hinstalled, hchi, hrho, hpie, hlogs, houtput,
      hgasLeft, herr, hrefund, hdelete, hbalPost, hstatePost⟩ :=
    processCreateMessage_drip_success ctx.msg ctx.msg_value_eq
      ctx.msg_codeAddress_eq ctx.msg_code_eq hgas ctx.msg_isStatic_eq
      ctx.msg_time_ne_zero ctx.msg_origChi ctx.msg_origRho
      ctx.msg_coldChi ctx.msg_coldRho hmax ctx.msg_balZero
  have htoNat : Int.toNat? post.refundCounter = some 0 := by
    rw [hrefund]
    rfl
  have hrun : processMessageCall ctx.msg =
      .ok (post.state, directCreateMessageOutputOf post) := by
    unfold processMessageCall
    rw [show ctx.msg.target.isNone = true by
      rw [ctx.msg_target_eq]
      rfl]
    unfold processMessageCall.create
    simp only [if_true]
    rw [ctx.target_eq]
    simp [ctx.noCodeOrNonce, ctx.noStorage, Except.bimap, hcreate, herr,
      htoNat, directCreateMessageOutputOf]
    rfl
  rcases of_processCreateMessage ctx.msg (.ok post) hcreate with
    ⟨xl, hfilled, hcreateRel⟩
  have hcodeRelation : Xlot.Rel Devm.CodePreserve xl :=
    Xlot.rel_of_filled codePreserve_refl_trans.1
      codePreserve_refl_trans.2 Ninst.codePreserve_effectRec
      Jinst.codePreserve_effect Linst.codePreserve_effect hfilled
  have hcreateCode := ProcessCreateMessage.codePreserve
    (Xlot.invGetCode_of_rel hcodeRelation) hcreateRel
  have hinputCode (a : Adr) :
      ctx.msg.benv.state.getCode a = base.state.getCode a := by
    rw [ctx.msg_benv_eq]
    have hsub := State.subBal_getCode ctx.debit_eq (a := a)
    rw [hsub]
    unfold State.getCode
    rw [State.incrNonce_get_code]
    change ctx.begun.state.getCode a = base.state.getCode a
    rw [ctx.begun_eq]
    change ctx.txInput.state.getCode a = base.state.getCode a
    rw [ctx.systemPrefix.state_eq]
  have hpreservedCode (a : Adr) (hne : a ≠ ca)
      (hbaseCode : some (base.state.getCode a).toList =
        Prog.compile deploymentSystemProgram) :
      post.state.getCode a = base.state.getCode a := by
    have hnonempty : (ctx.msg.benv.state.getCode a).toList ≠ [] := by
      rw [hinputCode]
      intro hempty
      apply Prog.compile_ne_nil (p := deploymentSystemProgram)
      rw [← hbaseCode, hempty]
    have hne' : a ≠ ctx.msg.currentTarget := by
      simpa [ctx.target_eq] using hne
    have hc := hcreateCode a hne' hnonempty
    change post.state.getCode a = ctx.msg.benv.state.getCode a at hc
    rw [hinputCode] at hc
    exact hc
  have hwithdrawalCode :
      some (post.state.getCode withdrawalRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram := by
    rw [hpreservedCode withdrawalRequestPredeployAddress
      hbase.withdrawalRequest_ne_target hbase.withdrawalRequestCode]
    exact hbase.withdrawalRequestCode
  have hconsolidationCode :
      some (post.state.getCode consolidationRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram := by
    rw [hpreservedCode consolidationRequestPredeployAddress
      hbase.consolidationRequest_ne_target hbase.consolidationRequestCode]
    exact hbase.consolidationRequestCode
  refine ⟨post.state, directCreateMessageOutputOf post, hrun, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hwithdrawalCode, hconsolidationCode⟩
  · simpa only [ctx.target_eq] using hstatePost
  · rw [← ctx.target_eq]
    exact hinstalled
  · rw [← ctx.target_eq]
    exact hchi
  · conv_lhs => rw [← ctx.target_eq]
    exact hrho
  · intro k hkc hkr
    rw [← ctx.target_eq]
    exact hpie k hkc hkr
  · rw [← ctx.target_eq]
    exact hbalPost
  · show post.logs = []
    exact hlogs
  · show post.output = code
    exact houtput
  · show post.gasLeft = ctx.msg.gas - 44611 - 352400
    exact hgasLeft
  · show post.error = none
    exact herr
  · rfl
  · show post.accountsToDelete = .emptyWithCapacity
    exact hdelete

structure CanonicalDeploymentTransactionResult
    (cfg : ChainConfig) (rules : ForkRules) (ca : Adr)
    (ctx : PreparedDeploymentContext cfg rules base cb deploymentTx sender ca)
    (post : State) (bout : BlockOutput) : Prop where
  run : processTransaction ctx.txInput .init deploymentTx 0 = .ok (post, bout)
  state : ∃ entry : Benv,
    (processCreateMessage.msg ctx.msg).benvAfterTransfer = .ok entry ∧
    post = deploymentFinalState ctx.txInput deploymentTx sender
      (constructorInstalledState entry.state ca ctx.msg.benv.stat.time)
      (deploymentTransactionGasBound deploymentTx)
  blockGasUsed : bout.blockGasUsed = deploymentTransactionGasBound deploymentTx
  blobGasUsed : bout.blobGasUsed = 0
  installed : post.getCode ca = ⟨⟨code⟩⟩
  chi : (post.getStor ca).get chiSlot = scale
  rho : (post.getStor ca).get rhoSlot = ctx.msg.benv.stat.time
  pie : ∀ k, k ≠ chiSlot → k ≠ rhoSlot → (post.getStor ca).get k = 0
  bal : post.bal ca = 0
  blockLogs : bout.blockLogs = []
  requests : bout.requests = []
  depositRequests : parseDepositRequests bout = .ok []
  withdrawalRequestCode :
    some (post.getCode withdrawalRequestPredeployAddress).toList =
      Prog.compile deploymentSystemProgram
  consolidationRequestCode :
    some (post.getCode consolidationRequestPredeployAddress).toList =
      Prog.compile deploymentSystemProgram
  receiptSucceeded :
    (Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0)).map
      (fun entry => entry.2.succeeded) = some true

/-- The message theorem is threaded through the linearized real transaction
pipeline, including validation, checking, upfront debit, refund/tip settlement,
receipt insertion, and the final DRIP post-state. -/
theorem canonicalDeploymentTransaction_succeeds
    (cfg : ChainConfig) (rules : ForkRules)
    (base : BlockChain) (cb : CanonicalBlock)
    (deploymentTx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase cfg rules base sender ca)
    (henv : CanonicalDripDeploymentBlock cfg rules base cb
      deploymentTxBytes deploymentTx sender ca)
    (ctx : PreparedDeploymentContext cfg rules base cb deploymentTx sender ca) :
    ∃ post bout,
      CanonicalDeploymentTransactionResult cfg rules ca ctx post bout := by
  obtain ⟨messagePost, messageOut, hmessage⟩ :=
    canonicalDeploymentMessage_succeeds cfg rules base cb deploymentTx sender
      ca hbase henv ctx
  let usedGas := deploymentUsedGasFromMessage deploymentTx messageOut
  let post := deploymentFinalState ctx.txInput deploymentTx sender
    messagePost usedGas
  let bout := deploymentFinalBout .init deploymentTx 0 messageOut usedGas
  have hrefund : Int.toNat? messageOut.refundCounter =
      some messageOut.refundCounter.toNat := by
    rw [hmessage.refundCounter]
    exact Int.mem_toNat?.mpr rfl
  have hdelete : messageOut.accountsToDelete.toList = [] := by
    apply List.isEmpty_iff.mp
    rw [Std.HashSet.isEmpty_toList, hmessage.accountsToDelete]
    rfl
  obtain ⟨maxPriorityFee, maxFee, htype⟩ := henv.type_eq
  have hrules : ctx.txInput.beginTransaction.stat.rules = rules := by
    rw [ctx.systemPrefix.environment_eq]
    rfl
  have hprice : deploymentEffectiveGasPrice
      (initBenv rules base cb.block.header) deploymentTx =
      deploymentEffectiveGasPrice ctx.txInput deploymentTx := by
    rw [ctx.systemPrefix.environment_eq]
  have hchecked :
      checkTransaction ctx.txInput.beginTransaction
          (deploymentTxPreludeBout .init deploymentTx 0) deploymentTx =
        .ok (sender, deploymentEffectiveGasPrice ctx.txInput deploymentTx,
          [], 0) := by
    simpa [ctx.systemPrefix.environment_eq, hprice] using henv.checked
  have hdebit := ctx.debit_eq
  rw [ctx.begun_eq] at hdebit
  simp only [Benv.beginTransaction] at hdebit
  have hprepare := ctx.prepare_eq
  rw [ctx.begun_eq, ctx.tenv_eq] at hprepare
  have hrun : processTransaction ctx.txInput .init deploymentTx 0 =
      .ok (post, bout) := by
    unfold processTransaction
    simp only [bind, Except.bind]
    rw [hrules, henv.validated]
    simp only [Except.mapError]
    simp only [deploymentTxPreludeBout,
      ExecutionTrace.transactionPreludeBout] at hchecked
    rw [hchecked]
    simp only [Tx.isTypeThree, Tx.accessList, TxType.accessList, Tx.auths,
      htype, Bool.false_eq_true, if_false, Nat.add_zero,
      Benv.beginTransaction]
    rw [hdebit]
    simp only [Option.toExcept]
    simp only [deploymentTenv, deploymentIntrinsicGas,
      Benv.beginTransaction] at hprepare
    simp only [List.map_nil, List.flatten_nil]
    simp only [deploymentEffectiveGasPrice] at hprepare ⊢
    rw [hprepare]
    simp only [hmessage.run]
    rw [hrefund]
    simp only [hdelete, List.foldl_nil]
    rfl
  have hcode : post.getCode ca = ⟨⟨code⟩⟩ := by
    dsimp only [post, deploymentFinalState]
    rw [State.addBal_getCode, State.addBal_getCode]
    exact hmessage.installed
  have hstor_eq : post.getStor ca = messagePost.getStor ca := by
    dsimp only [post, deploymentFinalState]
    unfold State.addBal
    unfold State.getStor
    rw [State.setBal_get_stor, State.setBal_get_stor]
  have hchi : (post.getStor ca).get chiSlot = scale := by
    rw [hstor_eq]
    exact hmessage.chi
  have hrho : (post.getStor ca).get rhoSlot = ctx.msg.benv.stat.time := by
    rw [hstor_eq]
    exact hmessage.rho
  have hpie : ∀ k, k ≠ chiSlot → k ≠ rhoSlot → (post.getStor ca).get k = 0 := by
    intro k hkc hkr
    rw [hstor_eq]
    exact hmessage.pie k hkc hkr
  have hcoinbase : ctx.txInput.stat.coinbase = cb.block.header.coinbase := by
    rw [ctx.systemPrefix.environment_eq]
    rfl
  have hbal : post.bal ca = 0 := by
    have hne1 : sender ≠ ca := hbase.sender_ne_target
    have hne2 : ctx.txInput.stat.coinbase ≠ ca := by
      rw [hcoinbase]
      exact henv.coinbase_ne_target
    dsimp only [post, deploymentFinalState]
    rw [addBal_bal_ne hne2, addBal_bal_ne hne1]
    exact hmessage.bal
  have hblockLogs : bout.blockLogs = [] := by
    dsimp only [bout, deploymentFinalBout]
    simp [deploymentTxPreludeBout,
      ExecutionTrace.transactionPreludeBout,
      hmessage.logs, BlockOutput.init]
  have hrequests : bout.requests = [] := by
    dsimp only [bout, deploymentFinalBout]
    simp [deploymentTxPreludeBout,
      ExecutionTrace.transactionPreludeBout,
      BlockOutput.init]
  have hwithdrawalCode :
      some (post.getCode withdrawalRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram := by
    dsimp only [post, deploymentFinalState]
    rw [State.addBal_getCode, State.addBal_getCode]
    exact hmessage.withdrawalRequestCode
  have hconsolidationCode :
      some (post.getCode consolidationRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram := by
    dsimp only [post, deploymentFinalState]
    rw [State.addBal_getCode, State.addBal_getCode]
    exact hmessage.consolidationRequestCode
  have hentry :
      Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0) =
        some (makeReceipt deploymentTx messageOut.error
          ((BlockOutput.init : BlockOutput).blockGasUsed + usedGas)
          messageOut.logs) := by
    dsimp only [bout, deploymentFinalBout]
    simp only [deploymentTxPreludeBout]
    change
      (((BlockOutput.init : BlockOutput).receiptsTrie.insert
        (deploymentReceiptKey 0)
        (makeReceipt deploymentTx messageOut.error
          ((BlockOutput.init : BlockOutput).blockGasUsed + usedGas)
          messageOut.logs))[deploymentReceiptKey 0]?) = _
    rw [Std.TreeMap.getElem?_insert_self]
  have hdeposit : parseDepositRequests bout = .ok [] := by
    unfold parseDepositRequests
    have hkeys : bout.receiptKeys = [deploymentReceiptKey 0] := by
      dsimp only [bout, deploymentFinalBout]
      simp [deploymentTxPreludeBout,
        ExecutionTrace.transactionPreludeBout, deploymentReceiptKey,
        BlockOutput.init]
    rw [hkeys]
    have hentry' := hentry
    change bout.receiptsTrie[deploymentReceiptKey 0]? = _ at hentry'
    simp
    rw [hentry']
    unfold makeReceipt
    rw [htype, hmessage.logs]
    rfl
  have hreceipt :
      (Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0)).map
        (fun entry => entry.2.succeeded) = some true := by
    rw [hentry]
    simp [makeReceipt, hmessage.error]
  have htotal : deploymentIntrinsicGas deploymentTx +
      dripCreateMessageGasAccounting ≤ deploymentTx.gas :=
    (le_max_right _ _).trans henv.gas_bound
  have hused : usedGas = deploymentTransactionGasBound deploymentTx := by
    dsimp only [usedGas, deploymentUsedGasFromMessage]
    rw [hmessage.gasLeft, ctx.msg_gas_eq, hmessage.refundCounter]
    simp only [Int.toNat_zero, Nat.min_zero, Nat.sub_zero]
    have hcharge : deploymentTx.gas -
        (deploymentTx.gas - deploymentIntrinsicGas deploymentTx - 44611 - 352400) =
        deploymentIntrinsicGas deploymentTx + dripCreateMessageGasAccounting := by
      simp only [dripCreateMessageGasAccounting] at htotal ⊢
      omega
    rw [hcharge]
    exact Nat.max_comm _ _
  have hblockGas : bout.blockGasUsed = deploymentTransactionGasBound deploymentTx := by
    change 0 + usedGas = _
    simpa only [Nat.zero_add] using hused
  have hblobGas : bout.blobGasUsed = 0 := rfl
  have hstate : ∃ entry : Benv,
      (processCreateMessage.msg ctx.msg).benvAfterTransfer = .ok entry ∧
      post = deploymentFinalState ctx.txInput deploymentTx sender
        (constructorInstalledState entry.state ca ctx.msg.benv.stat.time)
        (deploymentTransactionGasBound deploymentTx) := by
    obtain ⟨entry, hentry, hstate⟩ := hmessage.state
    refine ⟨entry, hentry, ?_⟩
    dsimp only [post]
    rw [hstate, hused]
  exact ⟨post, bout, hrun, hstate, hblockGas, hblobGas, hcode, hchi, hrho, hpie, hbal,
    hblockLogs, hrequests, hdeposit, hwithdrawalCode, hconsolidationCode, hreceipt⟩

/-! ## Exact post-transaction request suffix -/

/-- Conclusion evidence for the selected rules' two checked request-system
calls. Both calls execute the installed nonempty system program, return no
request bytes, and leave the constructor post-state and block output
unchanged. No preservation rungs: DRIP has no `ContractSpec` at G2. -/
structure CanonicalDeploymentSuffixResult
    (cfg : ChainConfig) (rules : ForkRules) (ca : Adr)
    (ctx : PreparedDeploymentContext cfg rules base cb deploymentTx sender ca)
    (post : State) (bout : BlockOutput) : Type where
  withdrawalOut : MsgCallOutput
  consolidationOut : MsgCallOutput
  withdrawalRun :
    processCheckedSystemTransaction (ctx.txInput.withState post)
      withdrawalRequestPredeployAddress [] = .ok (post, withdrawalOut)
  withdrawalReturnData : withdrawalOut.returnData = []
  consolidationRun :
    processCheckedSystemTransaction
      ((ctx.txInput.withState post).withState post)
      consolidationRequestPredeployAddress [] = .ok (post, consolidationOut)
  consolidationReturnData : consolidationOut.returnData = []
  run : processGeneralPurposeRequests (ctx.txInput.withState post) bout =
    .ok (post, bout)

/-- Execute the exact request suffix over the transaction result. -/
theorem canonicalDeploymentSuffix_succeeds
    (cfg : ChainConfig) (rules : ForkRules)
    (base : BlockChain) (cb : CanonicalBlock)
    (deploymentTx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase cfg rules base sender ca)
    (ctx : PreparedDeploymentContext cfg rules base cb deploymentTx sender ca)
    (post : State) (bout : BlockOutput)
    (htx : CanonicalDeploymentTransactionResult cfg rules ca ctx post bout) :
    Nonempty (CanonicalDeploymentSuffixResult cfg rules ca ctx post bout) := by
  obtain ⟨withdrawalOut, hwithdrawal, _, _, _, _,
      hwithdrawalReturn⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      (ctx.txInput.withState post) withdrawalRequestPredeployAddress []
      (by simpa [Benv.withState] using htx.withdrawalRequestCode)
      (by
        rw [ctx.systemPrefix.environment_eq]
        exact hbase.withdrawalRequest_not_precompile)
  obtain ⟨consolidationOut, hconsolidation, _, _, _, _,
      hconsolidationReturn⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      ((ctx.txInput.withState post).withState post)
      consolidationRequestPredeployAddress []
      (by simpa [Benv.withState] using htx.consolidationRequestCode)
      (by
        rw [ctx.systemPrefix.environment_eq]
        exact hbase.consolidationRequest_not_precompile)
  have hrun : processGeneralPurposeRequests
      (ctx.txInput.withState post) bout = .ok (post, bout) := by
    unfold processGeneralPurposeRequests
    rw [htx.depositRequests]
    simp only [List.length_nil, Nat.lt_irrefl, if_false, bind, Except.bind]
    rw [hwithdrawal]
    simp only [hwithdrawalReturn, List.length_nil, Nat.lt_irrefl, if_false]
    change (do
      let ⟨state, consolidationOutput⟩ ←
        processCheckedSystemTransaction
          ((ctx.txInput.withState post).withState post)
          consolidationRequestPredeployAddress []
      if consolidationOutput.returnData.length > 0 then
        .ok (state, {bout with requests := bout.requests ++
          [consolidationRequestType ++ consolidationOutput.returnData]})
      else .ok (state, {bout with requests := bout.requests})) =
        .ok (post, bout)
    simp only [hconsolidation, bind, Except.bind, hconsolidationReturn,
      List.length_nil, Nat.lt_irrefl, if_false]
    rfl
  exact ⟨⟨withdrawalOut, consolidationOut, hwithdrawal,
    hwithdrawalReturn, hconsolidation, hconsolidationReturn, hrun⟩⟩

/-- Compose the recovered prefix, singleton decoded transaction, empty
withdrawal stage, and exact request suffix into Jaune's real block body. -/
theorem canonicalDeploymentApplyBody_succeeds
    (cfg : ChainConfig) (rules : ForkRules)
    (base : BlockChain) (cb : CanonicalBlock)
    (deploymentTxBytes : Bytes) (deploymentTx : Tx) (sender ca : Adr)
    (henv : CanonicalDripDeploymentBlock cfg rules base cb
      deploymentTxBytes deploymentTx sender ca)
    (ctx : PreparedDeploymentContext cfg rules base cb deploymentTx sender ca)
    (post : State) (bout : BlockOutput)
    (htx : CanonicalDeploymentTransactionResult cfg rules ca ctx post bout)
    (hsuffix : CanonicalDeploymentSuffixResult cfg rules ca ctx post bout) :
    applyBody (initBenv rules base cb.block.header)
      cb.block.txs cb.block.wds = .ok (post, bout) := by
  unfold applyBody
  have hbeacon := ctx.systemPrefix.beaconRun
  change processUncheckedSystemTransaction
    (initBenv rules base cb.block.header)
    beaconRootsAddress
    (initBenv rules base cb.block.header).stat.parentBeaconBlockRoot.toBytes =
      .ok (ctx.systemPrefix.stBeacon, ctx.systemPrefix.outBeacon) at hbeacon
  rw [hbeacon]
  simp only [Except.mapError, bind, Except.bind]
  rw [ctx.systemPrefix.lastHashEq]
  simp only [Option.toExcept]
  rw [ctx.systemPrefix.historyRun]
  rw [henv.txs_eq]
  simp only [List.mapM_cons, List.mapM_nil, henv.decode_eq, bind,
    Except.bind, List.putIndex]
  rw [← ctx.systemPrefix.txInput_eq]
  change (do
    let ⟨benvTxs, boutTxs⟩ ←
      applyTransactions [(0, deploymentTx)] ctx.txInput .init
    let ⟨stWds, boutWds⟩ :=
      processWithdrawals benvTxs boutTxs cb.block.wds
    processGeneralPurposeRequests (benvTxs.withState stWds) boutWds) =
      .ok (post, bout)
  simp only [applyTransactions, htx.run, bind, Except.bind]
  rw [henv.withdrawals_eq]
  change processGeneralPurposeRequests (ctx.txInput.withState post) bout =
    .ok (post, bout)
  exact hsuffix.run

/-! ## Deployment-root adapter -/

/-- The DRIP deployment root. Time-free state facts (`installed`, `chi`,
`pie`, `bal`) are top-level; the time-valued `rho`, log, and receipt facts live in
the `execution` transaction result (with `msg_time_eq` linking message time
to the deployment block timestamp), following the WETH10 scoping pattern. -/
structure DeploymentRoot
    (cfg : ChainConfig) (base deployed : BlockChain) (ca : Adr) : Prop where
  execution : ∃ (rules : ForkRules) (cb : CanonicalBlock)
      (deploymentTxBytes : Bytes)
      (deploymentTx : Tx) (sender : Adr)
      (ctx : PreparedDeploymentContext cfg rules base cb deploymentTx sender ca)
      (post : State) (bout : BlockOutput),
    CanonicalDeploymentBase cfg rules base sender ca ∧
    CanonicalDripDeploymentBlock cfg rules base cb deploymentTxBytes
      deploymentTx sender ca ∧
    CanonicalDeploymentTransactionResult cfg rules ca ctx post bout ∧
    Nonempty (CanonicalDeploymentSuffixResult cfg rules ca ctx post bout) ∧
    stateTransitionUsing cfg
        base cb.block = .ok deployed ∧
    applyBody (initBenv rules base cb.block.header)
        cb.block.txs cb.block.wds = .ok (post, bout) ∧
    post = deployed.state ∧
    (Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0)).map
        (fun entry => entry.2.succeeded) = some true
  configValid : cfg.Valid
  target_ne_zero : ca ≠ 0
  target_not_precompile : ∀ {timestamp rules},
    cfg.rulesAt timestamp = .ok rules → ¬ rules.isPrecomp ca
  installed : deployed.state.getCode ca = ⟨⟨code⟩⟩
  chi : (deployed.state.getStor ca).get chiSlot = scale
  pie : ∀ k, k ≠ chiSlot → k ≠ rhoSlot → (deployed.state.getStor ca).get k = 0
  bal : deployed.state.bal ca = 0
  deployed_validContext : deployed.ValidContext
  deployed_chainId : cfg.chainId = deployed.chainId

/-- A successful configured step over the strict canonical
envelope establishes the deployment root; all execution contexts and receipt
facts are constructed in this proof rather than admitted by the envelope. -/
theorem canonicalDeploymentStep_establishes_root
    (cfg : ChainConfig) (rules : ForkRules) (base deployed : BlockChain)
    (cb : CanonicalBlock) (deploymentTxBytes : Bytes)
    (deploymentTx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase cfg rules base sender ca)
    (henv : CanonicalDripDeploymentBlock cfg rules base cb
      deploymentTxBytes deploymentTx sender ca)
    (hstep : stateTransitionUsing cfg
      base cb.block = .ok deployed) :
    DeploymentRoot cfg base deployed ca := by
  obtain ⟨ctx⟩ :=
    prepareCanonicalDeploymentContext cfg rules base cb deploymentTx sender ca
      hbase henv
  obtain ⟨post, bout, htx⟩ :=
    canonicalDeploymentTransaction_succeeds cfg rules base cb deploymentTx
      sender ca hbase henv ctx
  obtain ⟨suffix⟩ :=
    canonicalDeploymentSuffix_succeeds cfg rules base cb deploymentTx sender ca
      hbase ctx post bout htx
  have happly : applyBody (initBenv rules base cb.block.header)
      cb.block.txs cb.block.wds = .ok (post, bout) :=
    canonicalDeploymentApplyBody_succeeds cfg rules base cb deploymentTxBytes
      deploymentTx sender ca henv ctx post bout htx suffix
  have hwith : stateTransitionWith rules base cb.block = .ok deployed := by
    have h := hstep
    rw [stateTransitionUsing_eq_of_chainId_eq
      (cfg := cfg) (ch := base) hbase.chainId_eq] at h
    rw [henv.rulesAt] at h
    simpa [Except.mapError, Bind.bind, Except.bind] using h
  have hstate : post = deployed.state := by
    have hinvert := hwith
    rw [stateTransitionWith_eq_ok_iff, stateTransitionE] at hinvert
    obtain ⟨_, _, hinvert⟩ := Except.bind_eq_ok hinvert
    obtain ⟨_, _, hinvert⟩ := Except.bind_eq_ok hinvert
    dsimp only at hinvert
    obtain ⟨⟨st, bout'⟩, hab, hinvert⟩ := Except.bind_eq_ok hinvert
    rw [happly] at hab
    obtain ⟨hst, hbout⟩ := Prod.mk.inj (Except.ok.inj hab)
    subst st
    subst bout'
    dsimp only at hinvert
    obtain ⟨_, _, hinvert⟩ := Except.bind_eq_ok hinvert
    rw [← Except.ok.inj hinvert]
  let checkedBase := CheckedBlockChain.ofValidContext hbase.validContext
  have hwithChecked :
      stateTransitionWith rules checkedBase.val cb.block = .ok deployed := by
    change stateTransitionWith rules base cb.block = .ok deployed
    exact hwith
  have hcontext := BlockChain.validContext_of_transition
    (cc := checkedBase) (cb := cb) hwithChecked
  have hvalid : deployed.ValidContext := by
    let checkedDeployed := CheckedBlockChain.ofEvidence deployed cb.block
      hcontext.1 hcontext.2.1 hcontext.2.2.1 hcontext.2.2.2
    exact checkedDeployed.validContext
  have hchain : cfg.chainId = deployed.chainId :=
    hbase.chainId_eq.trans (stateTransitionWith_preserves_chainId hwith).symm
  refine ⟨?_, hbase.configValid, hbase.target_ne_zero,
    hbase.target_not_precompile,
    ?_, ?_, ?_, ?_, hvalid, hchain⟩
  · exact ⟨rules, cb, deploymentTxBytes, deploymentTx, sender, ctx, post, bout,
      hbase, henv, htx, ⟨suffix⟩, hstep, happly, hstate,
      htx.receiptSucceeded⟩
  · rw [← hstate]
    exact htx.installed
  · rw [← hstate]
    exact htx.chi
  · rw [← hstate]
    exact htx.pie
  · rw [← hstate]
    exact htx.bal

theorem DeploymentRoot.reflReach
    (hroot : DeploymentRoot cfg base deployed ca) :
    BlockChain.ReachUsing cfg deployed deployed := by
  exact .refl deployed hroot.configValid hroot.deployed_validContext
    hroot.deployed_chainId

end Drip
end Blanc
