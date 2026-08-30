import Blanc.ProxyPairOssifiableConstructorSetup

/-!
# OssifiableProxy whole-constructor execution boundary

This module connects the complete compiled creation program to the strict
decoder and setup carriers.  It stays at raw program altitude: CREATE-message
entry, code charging, installation, and failed-create rollback belong to the
deployment-message layer above it.
-/

namespace Blanc.ProxyPair

open Jaune
open Jaune.Ninst Blanc.Ninst
open scoped LogOutputHinv

/-- Peel the complete constructor's leading value guard on a successful walk,
then classify and prepare its strict decoder route.  The resulting carrier
retains the exact implementation/admin/setup values and the execution-derived
decoder memory image. -/
theorem ossifiableConstructorProgram_prepare_of_ok
    {runtimeOffset runtimeLength : Nat}
    {sevm : Sevm} {entry post : Devm} {tail : Stack} {image : Bytes}
    (hp : tail <<+ entry.stack)
    (hwf : Mem.Wf entry.memory)
    (hreads : Mem.Reads entry.memory image)
    (hcoordinate : runtimeOffset + runtimeLength + 96 < 2 ^ 256)
    (hcodeSize : sevm.code.size < 2 ^ 256)
    (run : Prog.RunCompiledTo sevm entry
      (ossifiableConstructorProgram runtimeOffset
        (runtimeOffset + runtimeLength) runtimeLength) (.ok post)) :
    ∃ decodePre implementation requestedAdmin setupData bodyPre,
      entry.state = decodePre.state ∧
      entry.logs = decodePre.logs ∧
      entry.memory = decodePre.memory ∧
      OssifiableConstructorPreparedSuccess runtimeOffset runtimeLength
        (runtimeOffset + runtimeLength) sevm decodePre post tail image
        implementation requestedAdmin setupData bodyPre := by
  rcases run with ⟨mainPre, mainBurn, mainRun⟩
  have pMain : tail <<+ mainPre.stack := by
    rw [← mainBurn.stack]
    exact hp
  have wfMain : Mem.Wf mainPre.memory := by
    rw [← mainBurn.memory]
    exact hwf
  have readsMain : Mem.Reads mainPre.memory image := by
    rw [← mainBurn.memory]
    exact hreads
  change Func.RunCompiledTo
    (ossifiableConstructorFunctions runtimeOffset runtimeLength)
    sevm mainPre
      (ossifiableConstructorProgram runtimeOffset
        (runtimeOffset + runtimeLength) runtimeLength).main
      (.ok post) at mainRun
  have valueZero : sevm.value = 0 := by
    by_contra valueNonzero
    rcases ossifiableConstructorProgram_value_rejected valueNonzero pMain
        mainRun with
      ⟨_, impossible, _⟩
    cases impossible
  rw [ossifiableConstructorProgram_main_shape] at mainRun
  obtain ⟨valuePost, qvalue, mainRun⟩ :=
    runCompiledTo_next_inv mainRun
  obtain ⟨testPre, qzero, branchRun⟩ :=
    runCompiledTo_next_inv mainRun
  have valueRun := Ninst.Run.of_runCompiled qvalue
  have zeroRun := Ninst.Run.of_runCompiled qzero
  have pValue := prefix_of_push (of_run_callvalue valueRun) pMain
  have pTest := prefix_of_iszero zeroRun pValue
  have pOne : (1 : B256) :: tail <<+ testPre.stack := by
    simpa [valueZero, B256.eqCheck] using pTest
  obtain ⟨decodePre, _, _, branchPop, decodeRun, pDecode⟩ :=
    Func.RunCompiledTo.succ_branch_of_prefix
      (by decide : (1 : B256) ≠ 0) pOne branchRun
  have entryToDecodeMemory : entry.memory = decodePre.memory :=
    mainBurn.memory.trans
      ((Ninst.Hinv.inv (f := Devm.memory) valueRun).trans
        ((Ninst.Hinv.inv (f := Devm.memory) zeroRun).trans
          branchPop.memory))
  have entryToDecodeState : entry.state = decodePre.state :=
    mainBurn.state.trans
      ((Ninst.Hinv.inv (f := Devm.state) valueRun).trans
        ((Ninst.Hinv.inv (f := Devm.state) zeroRun).trans
          branchPop.state))
  have entryToDecodeLogs : entry.logs = decodePre.logs :=
    mainBurn.logs.trans
      ((of_run_callvalue valueRun).logs.trans
        ((Ninst.Hinv.inv (f := Devm.logs) zeroRun).trans
          branchPop.logs))
  have wfDecode : Mem.Wf decodePre.memory := by
    rw [← entryToDecodeMemory]
    exact hwf
  have readsDecode : Mem.Reads decodePre.memory image := by
    rw [← entryToDecodeMemory]
    exact hreads
  have route := ossifiableConstructorDecode_route pDecode wfDecode readsDecode
    hcoordinate hcodeSize decodeRun
  rcases route.prepare_of_ok with
    ⟨implementation, requestedAdmin, setupData, bodyPre, prepared⟩
  exact ⟨decodePre, implementation, requestedAdmin, setupData, bodyPre,
    entryToDecodeState, entryToDecodeLogs, entryToDecodeMemory, prepared⟩

/-- Program-level form of the leading nonpayable failure.  The exact empty
REVERT is derived before decoding and before any constructor storage or log
effect. -/
theorem ossifiableConstructorProgram_value_rejected_of_prog
    {runtimeOffset runtimeLength : Nat}
    {sevm : Sevm} {entry : Devm} {tail : Stack} {out : Execution}
    (valueNonzero : sevm.value ≠ 0)
    (hp : tail <<+ entry.stack)
    (run : Prog.RunCompiledTo sevm entry
      (ossifiableConstructorProgram runtimeOffset
        (runtimeOffset + runtimeLength) runtimeLength) out) :
    ∃ post, out = .error (.revert, post) ∧ post.output = [] := by
  rcases run with ⟨mainPre, mainBurn, mainRun⟩
  have pMain : tail <<+ mainPre.stack := by
    rw [← mainBurn.stack]
    exact hp
  change Func.RunCompiledTo
    (ossifiableConstructorFunctions runtimeOffset runtimeLength)
    sevm mainPre
      (ossifiableConstructorProgram runtimeOffset
        (runtimeOffset + runtimeLength) runtimeLength).main out at mainRun
  exact ossifiableConstructorProgram_value_rejected valueNonzero pMain mainRun

end Blanc.ProxyPair
