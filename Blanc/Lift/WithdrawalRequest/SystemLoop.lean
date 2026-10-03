import Blanc.Lift.WithdrawalRequest.SystemBody
import Blanc.Lift.ExactWalkCutOps

/-! The bounded certified queue loop, ending before bookkeeping at 0x183.
The Nat index selects the actual word body; base, memory and selected charges
are threaded in execution order. No queue representation premise is used. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

/-- JUMPDEST, two DUP2s, EQ, PUSH2 and JUMPI. -/
def systemLoopHeaderGas : Nat := gJumpdest + 4 * gVerylow + gHigh

theorem systemLoopHeaderGas_eq : systemLoopHeaderGas = 23 := rfl

/-- Both certified headers and their bookkeeping continuations are identical. -/
theorem systemLoop_tree_eq : t_00e1_c1 = t_00e1_c6 := rfl

theorem systemLoop_post_tree_eq : t_0183_c1 = t_0183_c6 := rfl

/-- The three selected reads and eleven expansion-inclusive store charges.
Each charge uses its actual incoming warmed base or intermediate memory. -/
def systemLoopBodyCharges (sevm : Sevm) (base : Devm) (head index : B256)
    (memory : Mem) : Nat :=
  sloadCost sevm base (systemBodyKey head index) +
  sloadCost sevm (systemBodyBase1 sevm base head index) (1 + systemBodyKey head index) +
  sloadCost sevm (systemBodyBase2 sevm base head index) (2 + systemBodyKey head index) +
  systemRecordWordCharge index (systemBodyCaller sevm base head index)
    (systemBodyPubkey sevm base head index) (systemBodyPacked sevm base head index) memory 0 +
  systemRecordWordCharge index (systemBodyCaller sevm base head index)
    (systemBodyPubkey sevm base head index) (systemBodyPacked sevm base head index) memory 1 +
  systemRecordWordCharge index (systemBodyCaller sevm base head index)
    (systemBodyPubkey sevm base head index) (systemBodyPacked sevm base head index) memory 2 +
  systemRecordAmountCharge index (systemBodyPacked sevm base head index)
    (systemBodyWordMemory sevm base head index memory) 0 +
  systemRecordAmountCharge index (systemBodyPacked sevm base head index)
    (systemBodyWordMemory sevm base head index memory) 1 +
  systemRecordAmountCharge index (systemBodyPacked sevm base head index)
    (systemBodyWordMemory sevm base head index memory) 2 +
  systemRecordAmountCharge index (systemBodyPacked sevm base head index)
    (systemBodyWordMemory sevm base head index memory) 3 +
  systemRecordAmountCharge index (systemBodyPacked sevm base head index)
    (systemBodyWordMemory sevm base head index memory) 4 +
  systemRecordAmountCharge index (systemBodyPacked sevm base head index)
    (systemBodyWordMemory sevm base head index memory) 5 +
  systemRecordAmountCharge index (systemBodyPacked sevm base head index)
    (systemBodyWordMemory sevm base head index memory) 6 +
  systemRecordAmountCharge index (systemBodyPacked sevm base head index)
    (systemBodyWordMemory sevm base head index memory) 7

private theorem systemLoop_bodyGas (sevm : Sevm) (base : Devm) (head index : B256)
    (memory : Mem) :
    systemBodyGas sevm base head index memory =
      255 + systemLoopBodyCharges sevm base head index memory := by
  unfold systemBodyGas systemBodyAmountGas systemLoopBodyCharges
  simp only [gVerylow, gLow, gMid]
  omega

/-- Only the state and selected-charge sum consumed at the loop boundary. -/
structure SystemLoopPost where
  base : Devm
  memory : Mem
  charges : Nat

/-- One aggregate over the actual sequence of certified body effects. -/
def systemLoopFold (sevm : Sevm) (head : B256) (index : Nat) :
    Nat → Devm → Mem → SystemLoopPost
  | 0, base, memory => ⟨base, memory, 0⟩
  | n + 1, base, memory =>
    let post := systemLoopFold sevm head (index + 1) n
      (systemBodyBase sevm base head index.toB256)
      (systemBodyMemory sevm base head index.toB256 memory)
    ⟨post.base, post.memory,
      systemLoopBodyCharges sevm base head index.toB256 memory + post.charges⟩

/-- Affine fixed instructions plus the sum of the actual selected charges.
The eleven store base charges remain in `charges`; no allocation telescoping
or final closed E6 formula is asserted here. -/
def systemLoopGas (iterations : Nat) (post : SystemLoopPost) : Nat :=
  278 * iterations + systemLoopHeaderGas + post.charges

private theorem systemLoop_header_inv {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {index count head tail : B256} {out : Outcome}
    (run : SFunc.Run prog sevm (St base [index, count, head, tail] memory gas) t_00e1_c1 out) :
    ∃ gas', SFunc.Run prog sevm (St base [index, count, head, tail] memory gas')
      (if index = count then t_0183_c1 else t_00e9_c1) out := by
  obtain ⟨_, run⟩ := ric_dest run.cut
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (w := count) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (w := index) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_eq step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  by_cases same : index = count
  · simp only [B256.eqCheck, ite_eq_left same] at run
    rcases ric_branch run with ⟨flag, _, run⟩ | ⟨_, gas', run⟩
    · exact False.elim ((by decide : (1 : B256) ≠ 0) flag)
    · exact ⟨gas', (ite_eq_left same) ▸ run.uncut⟩
  · simp only [B256.eqCheck, ite_eq_right same] at run
    rcases ric_branch run with ⟨_, gas', run⟩ | ⟨flag, _, run⟩
    · exact ⟨gas', (ite_eq_right same) ▸ run.uncut⟩
    · exact False.elim (flag rfl)

private theorem systemLoop_header_exact {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {index count head tail : B256} {out : Outcome}
    (next : SFunc.RunExact prog sevm (St base [index, count, head, tail] memory gas)
      (if index = count then t_0183_c1 else t_00e9_c1) out) :
    SFunc.RunExact prog sevm
      (St base [index, count, head, tail] memory (gas + systemLoopHeaderGas)) t_00e1_c1 out := by
  rw [systemLoopHeaderGas_eq]
  have gasEq : gas + 23 = gas + 10 + 3 + 3 + 3 + 3 + 1 := by omega
  rw [gasEq]
  unfold t_00e1_c1
  refine rx_dest ?_
  refine rx_dup2 (by change 4 < 1024; decide) ?_
  refine rx_dup2 (by change 5 < 1024; decide) ?_
  refine rx_eq rfl (by change 4 < 1024; decide) ?_
  refine rx_push rfl (by change 5 < 1024; decide) ?_
  by_cases same : index = count
  · simp only [B256.eqCheck, ite_eq_left same] at next ⊢
    exact rx_branch_succ (by decide : (1 : B256) ≠ 0) next
  · simp only [B256.eqCheck, ite_eq_right same] at next ⊢
    exact rx_branch_zero next

/-- Any successful bounded loop reaches the bookkeeping tree with the exact
sequential body effects. `index + remaining` is the actual word count. -/
theorem systemLoop_inv_from {sevm : Sevm} {head tail count : B256}
    (fork : CoveredFork sevm.benvStat.fork) (cap : count.toNat ≤ 16)
    (remaining : Nat) {index : Nat} {base : Devm} {memory : Mem} {gas : Nat} {out : Outcome}
    (bound : index + remaining = count.toNat)
    (run : SFunc.Run prog sevm
      (St base [index.toB256, count, head, tail] memory gas) t_00e1_c1 out) :
    ∃ gas', SFunc.Run prog sevm
      (St (systemLoopFold sevm head index remaining base memory).base [count, count, head, tail]
        (systemLoopFold sevm head index remaining base memory).memory gas') t_0183_c1 out := by
  induction remaining generalizing index base memory gas with
  | zero =>
    have same : index.toB256 = count := by
      rw [show index = count.toNat by omega, toB256_toNat]
    obtain ⟨gas', next⟩ := systemLoop_header_inv run
    simp only [ite_eq_left same] at next
    simp only [systemLoopFold]
    rw [same] at next
    exact ⟨gas', next⟩
  | succ remaining ih =>
    have width : (16 : Nat) < 2 ^ 256 := by decide
    have different : index.toB256 ≠ count := by
      intro eq
      have eqNat := congrArg B256.toNat eq
      rw [B256.toNat_toB256_of_lt (by omega)] at eqNat
      omega
    obtain ⟨_, next⟩ := systemLoop_header_inv run
    simp only [ite_eq_right different] at next
    obtain ⟨_, next⟩ := systemBody_inv fork next
    have increment := one_add_toB256 (h := index) (by omega)
    rw [show Bytes.toB256 [0x01] = (1 : B256) by decide] at increment
    rw [increment, ← systemLoop_tree_eq] at next
    simp only [systemLoopFold]
    exact ih (index := index + 1) (by omega) next

/-- Exact bookkeeping continuations transport through every bounded body and
header. The gas is affine fixed instructions plus the selected-charge sum. -/
theorem systemLoop_exact_from {sevm : Sevm} {head tail count : B256}
    (fork : CoveredFork sevm.benvStat.fork) (cap : count.toNat ≤ 16)
    (remaining : Nat) {index : Nat} {base : Devm} {memory : Mem} {gas : Nat} {out : Outcome}
    (bound : index + remaining = count.toNat)
    (next : SFunc.RunExact prog sevm
      (St (systemLoopFold sevm head index remaining base memory).base [count, count, head, tail]
        (systemLoopFold sevm head index remaining base memory).memory gas) t_0183_c1 out) :
    SFunc.RunExact prog sevm (St base [index.toB256, count, head, tail] memory
      (gas + systemLoopGas remaining (systemLoopFold sevm head index remaining base memory)))
      t_00e1_c1 out := by
  induction remaining generalizing index base memory with
  | zero =>
    have same : index.toB256 = count := by
      rw [show index = count.toNat by omega, toB256_toNat]
    simp only [systemLoopFold] at next
    simp only [systemLoopFold, systemLoopGas, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    apply systemLoop_header_exact
    rw [ite_eq_left same, same]
    exact next
  | succ remaining ih =>
    have width : (16 : Nat) < 2 ^ 256 := by decide
    have different : index.toB256 ≠ count := by
      intro eq
      have eqNat := congrArg B256.toNat eq
      rw [B256.toNat_toB256_of_lt (by omega)] at eqNat
      omega
    simp only [systemLoopFold] at next
    have suffix := ih (index := index + 1) (by omega) next
    rw [systemLoop_tree_eq, ← one_add_toB256 (by omega)] at suffix
    have body := systemBody_exact fork suffix
    have header := systemLoop_header_exact
      (index := index.toB256) (count := count) (head := head) (tail := tail)
      (by simpa only [ite_eq_right different] using body)
    have gasEq : gas + systemLoopGas (remaining + 1)
        (systemLoopFold sevm head index (remaining + 1) base memory) =
        gas + systemLoopGas remaining
          (systemLoopFold sevm head (index + 1) remaining
            (systemBodyBase sevm base head index.toB256)
            (systemBodyMemory sevm base head index.toB256 memory)) +
          systemBodyGas sevm base head index.toB256 memory + systemLoopHeaderGas := by
      simp only [systemLoopGas, systemLoopFold, systemLoopHeaderGas_eq]
      rw [systemLoop_bodyGas]
      omega
    rw [gasEq]
    exact header

/-- The zero-index loop's exact poststate, including the two setup loads. -/
def systemQueuePost (sevm : Sevm) (base : Devm) (memory : Mem) : SystemLoopPost :=
  systemLoopFold sevm (systemHead sevm base) 0 (systemCount sevm base).toNat
    (systemSetupBase sevm base) memory

/-- The exact setup and bounded-loop cost, before any bookkeeping instruction. -/
def systemQueueGas (sevm : Sevm) (base : Devm) (memory : Mem) : Nat :=
  systemLoopGas (systemCount sevm base).toNat (systemQueuePost sevm base memory) +
    systemSetupGas sevm base

/-- A successful system setup and loop reach the canonical bookkeeping clone.
The final stack contains the count twice, followed by the original head/tail. -/
theorem systemQueue_inv {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat} {out : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm (St base [] memory gas) t_00cb_c0 out) :
    ∃ gas', SFunc.Run prog sevm
      (St (systemQueuePost sevm base memory).base
        [systemCount sevm base, systemCount sevm base, systemHead sevm base, systemTail sevm base]
        (systemQueuePost sevm base memory).memory gas') t_0183_c6 out := by
  obtain ⟨_, loop⟩ := systemSetup_inv fork run
  have post := systemLoop_inv_from fork (systemCount_le sevm base)
    (systemCount sevm base).toNat (index := 0) (by omega) loop
  rw [systemLoop_post_tree_eq] at post
  exact post

/-- An arbitrary-outcome bookkeeping continuation constructs the exact setup
and bounded loop, with no representation or reachable-state premise. -/
theorem systemQueue_exact {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat} {out : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (next : SFunc.RunExact prog sevm
      (St (systemQueuePost sevm base memory).base
        [systemCount sevm base, systemCount sevm base, systemHead sevm base, systemTail sevm base]
        (systemQueuePost sevm base memory).memory gas) t_0183_c6 out) :
    SFunc.RunExact prog sevm (St base [] memory (gas + systemQueueGas sevm base memory))
      t_00cb_c0 out := by
  rw [← systemLoop_post_tree_eq] at next
  have loop := systemLoop_exact_from fork (systemCount_le sevm base)
    (systemCount sevm base).toNat (index := 0) (by omega) next
  have setup := systemSetup_exact fork loop
  simpa only [systemQueueGas, systemQueuePost, Nat.add_assoc] using setup

/-- Every successful canonical-code system frame reaches the exact word-state
bookkeeping boundary. No per-frame queue ENTRY predicate is assumed. -/
theorem exec_system_loop {sevm : Sevm} {pre post : Devm}
    (code : sevm.code = Blanc.withdrawalRequestCode)
    (fork : CoveredFork sevm.benvStat.fork) (stack : pre.stack = [])
    (caller : sevm.caller = systemAddress) (exec : Exec 0 sevm pre (.ok post)) :
    ∃ gas, SFunc.Run prog sevm
      (St (systemQueuePost sevm pre pre.memory).base
        [systemCount sevm pre, systemCount sevm pre, systemHead sevm pre, systemTail sevm pre]
        (systemQueuePost sevm pre pre.memory).memory gas) t_0183_c6 (.halted post) := by
  obtain ⟨_, run⟩ := exec_dispatch code fork stack exec
  simp only [dispatchTail, ite_eq_left caller] at run
  exact systemQueue_inv fork run

/-- The exact caller prefix, setup and loop all consume the same continuation. -/
theorem system_loop_exact {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat} {out : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (caller : sevm.caller = systemAddress)
    (next : SFunc.RunExact prog sevm
      (St (systemQueuePost sevm base memory).base
        [systemCount sevm base, systemCount sevm base, systemHead sevm base, systemTail sevm base]
        (systemQueuePost sevm base memory).memory gas) t_0183_c6 out) :
    SFunc.RunExact prog sevm
      (St base [] memory (gas + systemQueueGas sevm base memory + dispatchGas)) t_0000_c0 out := by
  have setup := systemQueue_exact fork next
  apply dispatch_exact
  simpa only [dispatchTail, ite_eq_left caller] using setup

end Blanc.Lift.WithdrawalRequest
