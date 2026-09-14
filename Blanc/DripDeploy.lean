-- DripDeploy.lean : no-argument DRIP constructor and creation artifact.

import Blanc.CreationArtifact
import Blanc.DeploymentCompiled
import Blanc.DeploymentMessage
import Blanc.DripCode
import Blanc.ExecutionHistory
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

theorem of_run_constructorProgram_main {sevm : Sevm} {s r : Devm}
    {tail : Stack} {image : Bytes}
    (hp : tail <<+ s.stack)
    (hwf : Mem.Wf s.memory)
    (hreads : Mem.Reads s.memory image)
    (hcode : sevm.code.toList = creationCode)
    (run : Func.Run [] sevm s constructorProgram.main r) :
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

end Drip
end Blanc
