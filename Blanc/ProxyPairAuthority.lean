import Blanc.ProxyPairExecution
import Blanc.CycleWriteFree

/-!
# Proxy-pair write authority

The selector-free proxy has no source `SSTORE`.  The concrete success and
revert executions therefore attribute every reached successful persistent
write to the installed guarded implementation.
-/

namespace Blanc.ProxyPair

open Jaune

theorem proxy_entrySstoreFree :
    proxyProg.entrySstoreFree proxyProg.main [] = true := by
  decide

/-- Biting control: the same checker rejects the implementation entry that
contains the fixture's successful `SSTORE`. -/
theorem implGuarded_entrySstoreFree_rejected :
    implGuardedProg.entrySstoreFree implGuardedProg.main [] = false := by
  decide

private theorem successfulSstore_sourceSite_of_proxyRootCases
    {globalRoot : Exec.Deriv}
    (proxyInvocation :
      globalRoot.exactInvocation proxyProg proxyAdr proxyAdr)
    (rootCases : ∀ frameRoot ∈ Exec.rawFrameRoots globalRoot.exc,
      frameRoot = globalRoot ∨
        frameRoot.exactInvocation implGuardedProg proxyAdr implAdr)
    (write : Exec.SuccessfulSstoreOccurrence globalRoot) :
    ∃ site : Prog.SourceSite,
      site ∈ implGuardedProg.sourceSites ∧
      site.pc = write.occurrence.node.pc ∧
      site.instruction = .reg .sstore := by
  obtain ⟨frameRoot, selected, sameFrame⟩ :=
    write.occurrence.exists_rawFrameRoot_parentPrefix
  rcases rootCases frameRoot selected with rootEq | implementationInvocation
  · subst frameRoot
    have storeAt : Ninst.At write.occurrence.node.sevm.code
        write.occurrence.node.pc (.reg .sstore) := by
      rw [← write.instruction_eq]
      exact write.occurrence.decoded
    exact (globalRoot.noSstore_of_exactMain_entrySstoreFree
      proxyInvocation [] proxy_entrySstoreFree sameFrame storeAt).elim
  · exact write.occurrence.sourceSite_of_rawFrameRoot
      write.instruction_eq selected implementationInvocation sameFrame

theorem proxyProg_success_successfulSstore_sourceSite :
    ∃ (final : Devm) (outer : Exec 0 (initSevm proxyMsgSuccess)
        (initDevm proxyMsgSuccess) (.ok final)),
      exec ⟨0, initSevm proxyMsgSuccess, initDevm proxyMsgSuccess⟩ =
        .ok final ∧
      ∀ write : Exec.SuccessfulSstoreOccurrence
          (⟨0, initSevm proxyMsgSuccess, initDevm proxyMsgSuccess,
            .ok final, outer⟩ : Exec.Deriv),
        ∃ site : Prog.SourceSite,
          site ∈ implGuardedProg.sourceSites ∧
          site.pc = write.occurrence.node.pc ∧
          site.instruction = .reg .sstore := by
  obtain ⟨final, outer, _hprog, hexec, rootCases, _hout, _hgas,
      _hstate, _htra, _hlogs⟩ := proxyProg_success_runCompiledTo
  let globalRoot : Exec.Deriv :=
    ⟨0, initSevm proxyMsgSuccess, initDevm proxyMsgSuccess,
      .ok final, outer⟩
  have proxyInvocation :
      globalRoot.exactInvocation proxyProg proxyAdr proxyAdr := by
    refine ⟨rfl, rfl, rfl, ?_⟩
    rw [show (initSevm proxyMsgSuccess).code = proxyCode by rfl]
    rw [show proxyCode.toList = proxyBytes by
      simp [proxyCode, proxyBytes, ByteArray.toList_eq_toList_data]]
    exact proxyProg_compile
  have globalRootCases :
      ∀ frameRoot ∈ Exec.rawFrameRoots globalRoot.exc,
        frameRoot = globalRoot ∨
          frameRoot.exactInvocation implGuardedProg proxyAdr implAdr := by
    simpa [globalRoot] using rootCases
  refine ⟨final, outer, hexec, ?_⟩
  intro write
  exact successfulSstore_sourceSite_of_proxyRootCases
    proxyInvocation globalRootCases write

theorem proxyProg_revert_successfulSstore_sourceSite :
    ∃ (final : Devm) (outer : Exec 0 (initSevm proxyMsgRevert)
        (initDevm proxyMsgRevert) (.error (.revert, final))),
      exec ⟨0, initSevm proxyMsgRevert, initDevm proxyMsgRevert⟩ =
        .error (.revert, final) ∧
      ∀ write : Exec.SuccessfulSstoreOccurrence
          (⟨0, initSevm proxyMsgRevert, initDevm proxyMsgRevert,
            .error (.revert, final), outer⟩ : Exec.Deriv),
        ∃ site : Prog.SourceSite,
          site ∈ implGuardedProg.sourceSites ∧
          site.pc = write.occurrence.node.pc ∧
          site.instruction = .reg .sstore := by
  obtain ⟨final, outer, _hprog, hexec, rootCases, _hout, _hgas,
      _hstate, _htra, _hlogs⟩ := proxyProg_revert_runCompiledTo
  let globalRoot : Exec.Deriv :=
    ⟨0, initSevm proxyMsgRevert, initDevm proxyMsgRevert,
      .error (.revert, final), outer⟩
  have proxyInvocation :
      globalRoot.exactInvocation proxyProg proxyAdr proxyAdr := by
    refine ⟨rfl, rfl, rfl, ?_⟩
    rw [show (initSevm proxyMsgRevert).code = proxyCode by rfl]
    rw [show proxyCode.toList = proxyBytes by
      simp [proxyCode, proxyBytes, ByteArray.toList_eq_toList_data]]
    exact proxyProg_compile
  have globalRootCases :
      ∀ frameRoot ∈ Exec.rawFrameRoots globalRoot.exc,
        frameRoot = globalRoot ∨
          frameRoot.exactInvocation implGuardedProg proxyAdr implAdr := by
    simpa [globalRoot] using rootCases
  refine ⟨final, outer, hexec, ?_⟩
  intro write
  exact successfulSstore_sourceSite_of_proxyRootCases
    proxyInvocation globalRootCases write

end Blanc.ProxyPair
