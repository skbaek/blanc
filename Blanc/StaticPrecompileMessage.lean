import Blanc.ForwardSha256
import Blanc.Ladder

/-!
# Inversion facts for retained static-precompile messages

These facts start from an actual `ProcessMessage` witness rather than a
forward-constructed call.  They separate the contract-neutral storage frame
of any enabled static precompile from the fixed-width SHA-256 output used by
compiled callers.
-/

namespace Blanc

open Jaune

/-- A synchronous precompile child of a zero-value static call leaves every
account's storage where the parent had it.  The enabled-precompile premise is
load-bearing: without it an EIP-7702 delegation designator may route the same
address to ordinary write-capable code. -/
theorem stor_of_processMessage_staticPrecomp
    {sevm : Sevm} {parent child : Devm} {gas : Nat} {calldata : Bytes}
    {code : ByteArray} {xl : Xlot} {target : Adr}
    (hpre : decide (sevm.benvStat.rules.isPrecomp target) = true)
    (hpm : ProcessMessage
      (callMsg sevm parent gas 0 sevm.currentTarget target target true true
        calldata code false) xl (.ok child)) :
    ∀ a, Devm.getStor child a = Devm.getStor parent a := by
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp hpm
  unfold FrameBody at hbody
  rcases hbt :
      (callMsg sevm parent gas 0 sevm.currentTarget target target true true
        calldata code false).benvAfterTransfer with e | benv <;>
    rw [hbt] at hbody
  · rw [hbody.2] at hset
    unfold processMessage.settle at hset
    cases hset
  · obtain ⟨st_mid, hsub, hbenv⟩ := of_benvAfterTransfer rfl hbt
    subst benv
    have hca :
        ((callMsg sevm parent gas 0 sevm.currentTarget target target true true
            calldata code false).withBenv
          (((callMsg sevm parent gas 0 sevm.currentTarget target target true
              true calldata code false).benv.withState st_mid).addBal
            target 0)).codeAddress = some target := rfl
    rcases of_executeCode_someCode hca hbody with hpc | hinterp
    · rcases r0 with x | evm'
      · rw [processMessage.settle_error] at hset
        cases hset
      · unfold processMessage.settle at hset
        dsimp only [bind, Except.bind] at hset
        by_cases herr : evm'.error.isSome = true
        · rw [if_pos herr] at hset
          intro a
          rw [Except.ok.inj hset]
          rfl
        · rw [if_neg herr] at hset
          have heq : child = evm' := Except.ok.inj hset
          subst heq
          have hstate := state_of_executePrecomp_ok hpc.2.2 herr
          intro a
          change (child.state.get a).stor = (parent.state.get a).stor
          rw [hstate]
          exact (of_state_transfer_fields hsub).1 a
    · exact False.elim (hinterp.1 (by exact hpre))

/-- A synchronous enabled static precompile also preserves every account's
code.  This is the code-field companion of
`stor_of_processMessage_staticPrecomp`; callers need it to transport a
non-delegation fact across a sequence of precompile calls. -/
theorem code_of_processMessage_staticPrecomp
    {sevm : Sevm} {parent child : Devm} {gas : Nat} {calldata : Bytes}
    {code : ByteArray} {xl : Xlot} {target : Adr}
    (hpre : decide (sevm.benvStat.rules.isPrecomp target) = true)
    (hpm : ProcessMessage
      (callMsg sevm parent gas 0 sevm.currentTarget target target true true
        calldata code false) xl (.ok child)) :
    ∀ a, child.getCode a = parent.getCode a := by
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp hpm
  unfold FrameBody at hbody
  rcases hbt :
      (callMsg sevm parent gas 0 sevm.currentTarget target target true true
        calldata code false).benvAfterTransfer with e | benv <;>
    rw [hbt] at hbody
  · rw [hbody.2] at hset
    unfold processMessage.settle at hset
    cases hset
  · obtain ⟨st_mid, hsub, hbenv⟩ := of_benvAfterTransfer rfl hbt
    subst benv
    have hca :
        ((callMsg sevm parent gas 0 sevm.currentTarget target target true true
            calldata code false).withBenv
          (((callMsg sevm parent gas 0 sevm.currentTarget target target true
              true calldata code false).benv.withState st_mid).addBal
            target 0)).codeAddress = some target := rfl
    rcases of_executeCode_someCode hca hbody with hpc | hinterp
    · rcases r0 with x | evm'
      · rw [processMessage.settle_error] at hset
        cases hset
      · unfold processMessage.settle at hset
        dsimp only [bind, Except.bind] at hset
        by_cases herr : evm'.error.isSome = true
        · rw [if_pos herr] at hset
          intro a
          rw [Except.ok.inj hset]
          rfl
        · rw [if_neg herr] at hset
          have heq : child = evm' := Except.ok.inj hset
          subst heq
          have hstate := state_of_executePrecomp_ok hpc.2.2 herr
          intro a
          change (child.state.get a).code = (parent.state.get a).code
          rw [hstate]
          exact (of_state_transfer_fields hsub).2.1 a
    · exact False.elim (hinterp.1 (by exact hpre))

/-- A clean 64-byte SHA-256 child necessarily paid the fixed precompile
charge.  An underfunded precompile exceptional-halts, so it cannot satisfy the
clean-child premise. -/
theorem gasSha25664_le_of_processMessage_clean
    {sevm : Sevm} {parent child : Devm} {gas : Nat} {calldata : Bytes}
    {code : ByteArray} {xl : Xlot}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hlen : calldata.length = 64)
    (hpm : ProcessMessage
      (callMsg sevm parent gas 0 sevm.currentTarget 2 2 true true
        calldata code false) xl (.ok child))
    (hclean : child.error.isSome = false) :
    84 ≤ gas := by
  by_contra hgas
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp hpm
  unfold FrameBody at hbody
  rcases hbt :
      (callMsg sevm parent gas 0 sevm.currentTarget 2 2 true true
        calldata code false).benvAfterTransfer with e | benv <;>
    rw [hbt] at hbody
  · rw [hbody.2] at hset
    unfold processMessage.settle at hset
    cases hset
  · have hca :
        ((callMsg sevm parent gas 0 sevm.currentTarget 2 2 true true
          calldata code false).withBenv benv).codeAddress = some 2 := rfl
    rcases of_executeCode_someCode hca hbody with hpc | hinterp
    · have hexec := hpc.2.2
      rw [show executePrecomp
          (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 2 2 true true
            calldata code false).withBenv benv)) 2 =
          applyPrecompResult
            (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 2 2 true
              true calldata code false).withBenv benv))
            (executeSha256
              (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 2 2 true
                true calldata code false).withBenv benv))) from rfl] at hexec
      have hlen' :
          (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 2 2 true true
            calldata code false).withBenv benv)).sta.data.length = 64 := by
        change calldata.length = 64
        exact hlen
      unfold executeSha256 PrecompResult.chargeGas at hexec
      simp only [hlen'] at hexec
      rw [if_neg (by
        show ¬(60 + 12 * ceilDiv 64 32) ≤
          (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 2 2 true true
            calldata code false).withBenv benv)).dyna.gasLeft
        change ¬84 ≤ gas
        exact hgas)] at hexec
      simp only [applyPrecompResult, executeCode.handleError] at hexec
      rw [← hexec] at hset
      unfold processMessage.settle at hset
      simp only [bind, Except.bind, Option.isSome] at hset
      injection hset with hchild
      subst child
      change true = false at hclean
      contradiction
    · exact False.elim (hinterp.1 (by
        obtain ⟨st_mid, hsub, hbenv⟩ := of_benvAfterTransfer rfl hbt
        subst benv
        exact hpre))

/-- A clean enabled address-2 child on exactly 64 bytes returns the canonical
SHA-256 digest. -/
theorem output_of_processMessage_sha256_64_clean
    {sevm : Sevm} {parent child : Devm} {gas : Nat} {calldata : Bytes}
    {code : ByteArray} {xl : Xlot}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hlen : calldata.length = 64)
    (hpm : ProcessMessage
      (callMsg sevm parent gas 0 sevm.currentTarget 2 2 true true
        calldata code false) xl (.ok child))
    (hclean : child.error.isSome = false) :
    child.output = (Bytes.sha256 calldata).toBytes := by
  have hgas : 84 ≤ gas :=
    gasSha25664_le_of_processMessage_clean hpre hlen hpm hclean
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp hpm
  unfold FrameBody at hbody
  rcases hbt :
      (callMsg sevm parent gas 0 sevm.currentTarget 2 2 true true
        calldata code false).benvAfterTransfer with e | benv <;>
    rw [hbt] at hbody
  · rw [hbody.2] at hset
    unfold processMessage.settle at hset
    cases hset
  · have hca :
        ((callMsg sevm parent gas 0 sevm.currentTarget 2 2 true true
          calldata code false).withBenv benv).codeAddress = some 2 := rfl
    rcases of_executeCode_someCode hca hbody with hpc | hinterp
    · have hexec := hpc.2.2
      rw [executePrecomp_two_of_length_64 (by
        change calldata.length = 64
        exact hlen) (by
        change 84 ≤ gas
        exact hgas)] at hexec
      simp only [applyPrecompResult, executeCode.handleError] at hexec
      rw [← hexec] at hset
      unfold processMessage.settle at hset
      simp only [bind, Except.bind, Option.isSome] at hset
      injection hset with hchild
      subst child
      rfl
    · exact False.elim (hinterp.1 (by
        obtain ⟨st_mid, hsub, hbenv⟩ := of_benvAfterTransfer rfl hbt
        subst benv
        exact hpre))

/-- Storage and output image of a clean fixed-width SHA-256 static child. -/
theorem frame_of_processMessage_sha256_64_clean
    {sevm : Sevm} {parent child : Devm} {gas : Nat} {calldata : Bytes}
    {code : ByteArray} {xl : Xlot}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hlen : calldata.length = 64)
    (hpm : ProcessMessage
      (callMsg sevm parent gas 0 sevm.currentTarget 2 2 true true
        calldata code false) xl (.ok child))
    (hclean : child.error.isSome = false) :
    (∀ a, Devm.getStor child a = Devm.getStor parent a) ∧
      child.output = (Bytes.sha256 calldata).toBytes := by
  exact ⟨stor_of_processMessage_staticPrecomp hpre hpm,
    output_of_processMessage_sha256_64_clean hpre hlen hpm hclean⟩

end Blanc
