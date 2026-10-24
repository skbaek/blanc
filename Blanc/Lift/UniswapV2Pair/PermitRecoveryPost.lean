import Blanc.Lift.UniswapV2Pair.PermitRecoverySettlement
import Blanc.Lift.CursorSourceRunReturn

namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem PermitCallOccurrenceH.reply_memory {root : Exec.Deriv} {b : Devm}
    (actual : PermitCallOccurrenceH root b) :
    actual.call.returned.devm.memory =
      permitReplyMemory (permitPublicCallMemoryH root.sevm b) actual.out := by
  simpa only [permitReplyMemory,
    show (482 : B256).toNat = 482 from rfl, show (128 : B256).toNat = 128 from rfl,
    show (450 : B256).toNat = 450 from rfl, show (32 : B256).toNat = 32 from rfl]
    using actual.post.memory

theorem PermitCallOccurrenceH.recovered_image {root : Exec.Deriv} {b : Devm}
    (actual : PermitCallOccurrenceH root b) :
    Bytes.toB256 (actual.call.returned.devm.memory.read 450 32).1 =
      permitRecoveredWord actual.out := by
  rw [actual.reply_memory]
  exact (permitCallMemory_factsH (sevm := root.sevm) (b := b)
    getterInitMemory_ptr (Mem.reads_data getterInitMemory) (permitOwner root.sevm)
    (permitSpender root.sevm) (permitValue root.sevm) (permitDeadline root.sevm)
    (permitV root.sevm) (permitR root.sevm) (permitS root.sevm)).2.2 actual.out

theorem PermitCallOccurrenceH.suffix_inverse {root : Exec.Deriv} {b post : Devm}
    (actual : PermitCallOccurrenceH root b) (success : root.exn = .ok post)
    (stateGas : root.sevm.benvStat.rules.stateGas = none)
    (bal : root.sevm.benvStat.rules.bal = none) {o : Outcome}
    (run : SFunc.Run cert.prog root.sevm actual.call.returned.devm permitRecoveryTail o) :
    (permitRecoveredWord actual.out).toAdr ≠ 0 ∧
      (permitRecoveredWord actual.out).toAdr = permitOwner root.sevm ∧
      root.sevm.isStatic = false ∧
      ∃ gas, o = .returned (St
        (approveCoreBaseH root.sevm actual.call.returned.devm (permitOwner root.sevm)
          (permitSpender root.sevm) (permitValue root.sevm)) [0xd505accf]
        (permitFinalMemory (permitReplyMemory (permitPublicCallMemoryH root.sevm b) actual.out)
          (permitOwner root.sevm) (permitSpender root.sevm) (permitValue root.sevm)) gas) := by
  have one := actual.flag_one success stateGas bal
  have shape := St.self (one ▸ actual.post.stack) actual.reply_memory
  rw [shape] at run
  have h := run.cut
  unfold permitRecoveryTail at h
  obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_iszero hd
  obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_iszero hd
  obtain ⟨d', hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branch h with ⟨_, _, bad⟩ | ⟨accepted, _, h⟩
  · exact (bad.false_of_noOk (by decide)).elim
  · rw [show B256.eqCheck (1 : B256) 0 = 0 from by decide] at h
    have facts := permitCallMemory_factsH (sevm := root.sevm) (b := b)
      getterInitMemory_ptr (Mem.reads_data getterInitMemory) (permitOwner root.sevm)
      (permitSpender root.sevm) (permitValue root.sevm) (permitDeadline root.sevm)
      (permitV root.sevm) (permitR root.sevm) (permitS root.sevm)
    obtain ⟨recovered, signer, nonstatic, gas, image⟩ := permitSigner_invH stateGas bal
      (permitReplyMemory_ptr facts.1 actual.out) (SFunc.runP_iff_runCutP_nil.mpr h)
    rw [facts.2.2 actual.out] at recovered signer
    exact ⟨recovered, signer, nonstatic, gas, image⟩


theorem PermitCallOccurrenceH.post_image {root : Exec.Deriv} {b post : Devm}
    (actual : PermitCallOccurrenceH root b) (success : root.exn = .ok post)
    (stateGas : root.sevm.benvStat.rules.stateGas = none)
    (bal : root.sevm.benvStat.rules.bal = none) :
    (permitRecoveredWord actual.out).toAdr ≠ 0 ∧
      (permitRecoveredWord actual.out).toAdr = permitOwner root.sevm ∧
      root.sevm.isStatic = false ∧
      post = permitPublicPostH root.sevm b actual.call.returned.devm actual.out
        0xd505accf post.gasLeft := by
  have returnedFork : actual.call.returned.sevm.benvStat.rules.stateGas = none ∧
      actual.call.returned.sevm.benvStat.rules.bal = none :=
    ⟨actual.returnedSevm ▸ stateGas, actual.returnedSevm ▸ bal⟩
  rcases actual.placed.sourceRunReturnH cert_check (actual.returnedExn.trans success)
      returnedFork.1 with halted | returned
  · have plain : SFunc.Run cert.prog root.sevm actual.call.returned.devm
        permitRecoveryTail (.halted post) := by
      simpa only [actual.returnedSevm, actual.tree] using halted.mono StepIn.toRun
    obtain ⟨_, _, _, gas, impossible⟩ := actual.suffix_inverse success stateGas bal plain
    cases impossible
  · obtain ⟨k, K, d, run, sameK, _, _, body, placed⟩ := returned
    have plain : SFunc.Run cert.prog root.sevm actual.call.returned.devm
        permitRecoveryTail (.returned d) := by
      simpa only [actual.returnedSevm, actual.tree] using body.mono StepIn.toRun
    obtain ⟨recovered, signer, nonstatic, gas, image⟩ :=
      actual.suffix_inverse success stateGas bal plain
    have state := Outcome.returned.inj image
    have continuations := actual.continuations
    rw [sameK, List.map_cons] at continuations
    have pair := List.cons.inj continuations
    have tail : K = [] := List.eq_nil_of_map_eq_nil pair.2
    rcases placed.sourceRunReturnH cert_check rfl returnedFork.1 with halted | another
    · have caller : SFunc.Run cert.prog root.sevm d t_0257_c76 (.halted post) := by
        simpa only [actual.returnedSevm, pair.1] using halted.mono StepIn.toRun
      rw [state] at caller
      have h := caller.cut
      unfold t_0257_c76 at h
      obtain ⟨residual, h⟩ := ric_dest h
      cases h with
      | last stop =>
        have result : post = permitPublicPostH root.sevm b actual.call.returned.devm
            actual.out 0xd505accf residual := (Except.ok.inj stop).symm
        have remaining : post.gasLeft = residual := congrArg Devm.gasLeft result
        exact ⟨recovered, signer, nonstatic, remaining ▸ result⟩
    · obtain ⟨next, rest, state, exc, impossible, _⟩ := another
      change K = next :: rest at impossible
      rw [tail] at impossible
      cases impossible


end Blanc.Lift.UniswapV2Pair
