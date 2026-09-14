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
      (∀ k, k ≠ chiSlot → k ≠ rhoSlot → Devm.getStorVal post sevm.currentTarget k = 0) := by
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
  exact ⟨postW, hProg, houtW, herrW, hlogsW, hrowChi, hrowRho, hgasW, hrefundW, hdeleteW, hpieW⟩

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
      (∀ k, k ≠ chiSlot → k ≠ rhoSlot → Devm.getStorVal post sevm.currentTarget k = 0) := by
  obtain ⟨postW, hProg, houtW, herrW, hlogsW, hrowChi, hrowRho, hgasW, hrefundW, hdeleteW, hpieW⟩ :=
    constructorProgram_runCompiled hcode hvalue hstatic htime hstack hmem hgas
      hlogs hrefund herror horigChi horigRho hcurChi hcurRho hcurAll hcoldChi hcoldRho
  have h_compile : some constructorInitPrefix = constructorProgram.compile :=
    constructorInitPrefix_compile.symm
  have h_code : sevm.code.toList = constructorInitPrefix ++ code := by
    rw [hcode, creationCode_eq_prefix_append_runtime]
  have hexec := Prog.exec_of_runCompiled_appended hProg h_compile h_code
  exact ⟨postW, hexec, houtW, herrW, hlogsW, hrowChi, hrowRho, hgasW, hrefundW, hdeleteW, hpieW⟩

structure DripInitCheckpoint (msg : Msg) (initPost : Devm) : Prop where
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
    (h_coldRho : ⟨msg.currentTarget, rhoSlot⟩ ∉ msg.accessedStorageKeys) :
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
  obtain ⟨initPost, hexecW, houtW, herrW, hlogsW, hchiW, hrhoW, hgasW, hrefundW, hdeleteW, hpieW⟩ :=
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
  exact ⟨initPost,
    { process := h_pm
      output := houtW
      chi := hchiW
      rho := h_rho
      logs := hlogsW
      error := herrW
      refundCounter := hrefundW
      accountsToDelete := h_delete
      gas := hgasW
      pie := hpieW }⟩

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
  exact ⟨charged,
    { process :=
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
      pie := h_pie }⟩

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
    (h_gas : charged.gasLeft = msg.gas - 44611 - 352400) :
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
      post.accountsToDelete = .emptyWithCapacity := by
  refine ⟨charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩,
    h_process, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    (h_max : 1762 ≤ msg.benv.stat.rules.code.maxCodeSize) :
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
      post.accountsToDelete = .emptyWithCapacity := by
  obtain ⟨initPost, init⟩ :=
    processMessage_drip_checkpoint msg h_value h_codeAddress h_code
      (by omega) h_static h_time h_origChi h_origRho h_coldChi h_coldRho
  obtain ⟨chargedPost, charged⟩ :=
    processCreateMessage_drip_charge_checkpoint msg init h_gas h_max
  exact dripInstalledPost_certificate msg charged.process charged.output
    charged.chi charged.rho charged.pie charged.logs charged.error charged.refundCounter
    charged.accountsToDelete charged.gas

end Drip
end Blanc
