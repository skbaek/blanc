import Blanc.Lift.WithdrawalRequest.UserFeeDispatch
import Blanc.Lift.Deploy

/-!
The actual word-fee getter return. Memory and RETURN state are named to keep
symbolic byte arrays opaque during the walk. Fragment alignment is explicit;
the full canonical specialization starts with fresh memory and constructs its
exit without a continuation premise.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

def feeGetterMemory (M : Mem) (fee : B256) : Mem := M.write 0 fee.toBytes

def feeGetterPost (b : Devm) (M : Mem) (fee : B256) (G : Nat) : Devm :=
  returnPost (St b [0, 32] (feeGetterMemory M fee) G) 0 32 []

/-- PUSH0, MSTORE's fixed charge, PUSH1, PUSH0; RETURN costs only expansion. -/
def feeGetterFixedGas : Nat := 2 * gBase + 2 * gVerylow

def feeGetterGas (M : Mem) : Nat :=
  feeGetterFixedGas +
    (calculateMemoryGasCost (memExtSize M.size 0 32) - calculateMemoryGasCost M.size)

theorem feeGetterFixedGas_eq : feeGetterFixedGas = 10 := rfl
theorem feeGetterGas_empty : feeGetterGas Mem.empty = 13 := rfl

private theorem getter_memory_size {M : Mem} {fee : B256} (aligned : M.size % 32 = 0) :
    (feeGetterMemory M fee).size = max M.size 32 := by
  exact Mem.size_write_word_aligned aligned (by decide)

private theorem getter_memory_alignment {M : Mem} {fee : B256} (aligned : M.size % 32 = 0) :
    (feeGetterMemory M fee).size % 32 = 0 := by
  rw [getter_memory_size aligned]
  by_cases h : M.size ≤ 32
  · rw [Nat.max_eq_right h]
  · rw [Nat.max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge h))]
    exact aligned

private theorem getter_return_free {b : Devm} {M : Mem} {fee : B256} {G : Nat}
    (aligned : M.size % 32 = 0) :
    (St b [0, 32] (feeGetterMemory M fee) G).extCost [⟨0, 32⟩] = 0 := by
  apply Devm.extCost_zero_of_le (getter_memory_alignment aligned)
  rw [getter_memory_size aligned]
  exact Nat.le_max_right _ _

/-- A successful getter leaves exactly the named RETURN state, including its error field. -/
theorem fee_getter_inv {sevm : Sevm} {b post : Devm} {M : Mem} {fee : B256} {G : Nat}
    (aligned : M.size % 32 = 0)
    (run : SFunc.Run prog sevm (St b [fee] M G) t_0082_c0 (.halted post)) :
    ∃ G', post = feeGetterPost b M fee G' := by
  cases run with
  | next hp run =>
    obtain ⟨_, rfl⟩ := ri_push hp
    change SFunc.Run _ _ (St b [0, fee] M _) _ _ at run
    cases run with
    | next hm run =>
      obtain ⟨_, rfl⟩ := ri_mstore hm
      change SFunc.Run _ _ (St b [] (feeGetterMemory M fee) _) _ _ at run
      cases run with
      | next hp run =>
        obtain ⟨_, rfl⟩ := ri_push hp
        change SFunc.Run _ _ (St b [32] (feeGetterMemory M fee) _) _ _ at run
        cases run with
        | next hp run =>
          obtain ⟨gas, rfl⟩ := ri_push hp
          change SFunc.Run _ _ (St b [0, 32] (feeGetterMemory M fee) gas) _ _ at run
          cases run with
          | last actual =>
            have expected : SFunc.RunExact prog sevm
                (St b [0, 32] (feeGetterMemory M fee) gas) (.last .return_)
                (.halted (feeGetterPost b M fee gas)) :=
              rx_return_any rfl (getter_return_free aligned)
            cases expected with
            | last expected =>
              exact ⟨_, Except.ok.inj (actual.symm.trans expected)⟩

/-- Construct the actual return outcome at exactly the getter charge. -/
theorem fee_getter_exact {sevm : Sevm} {b : Devm} {M : Mem} {fee : B256} {G : Nat}
    (aligned : M.size % 32 = 0) :
    SFunc.RunExact prog sevm (St b [fee] M (G + feeGetterGas M)) t_0082_c0
      (.halted (feeGetterPost b M fee G)) := by
  let expansion := calculateMemoryGasCost (memExtSize M.size 0 32) - calculateMemoryGasCost M.size
  have hgas : G + feeGetterGas M = G + 2 + 3 + (3 + expansion) + 2 := by
    simp only [feeGetterGas, feeGetterFixedGas_eq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    congr 1
    simp only [expansion, ← Nat.add_assoc]
  rw [hgas]
  unfold t_0082_c0
  refine rx_push0 (by change 1 < 1024; decide) ?_
  refine rx_mstore (c := 3 + expansion) ?_ rfl ?_
  · rw [St.extCost_eq rfl]
    rfl
  · refine rx_push (w := (32 : B256)) rfl (by decide) ?_
    refine rx_push0 (by change 1 < 1024; decide) ?_
    exact rx_return_any rfl (getter_return_free aligned)

/-- The named return writes the full word and preserves every non-machine base field. -/
theorem feeGetterPost_facts (b : Devm) (M : Mem) (fee : B256) (G : Nat)
    (wf : Mem.Wf M) (aligned : M.size % 32 = 0) :
    (feeGetterPost b M fee G).output = fee.toBytes ∧
    (feeGetterPost b M fee G).world = b.world ∧
    (feeGetterPost b M fee G).meta = {b.meta with output := fee.toBytes} ∧
    (feeGetterPost b M fee G).stack = [] ∧
    (feeGetterPost b M fee G).memory = feeGetterMemory M fee ∧
    (feeGetterPost b M fee G).gasLeft = G ∧
    (feeGetterPost b M fee G).stateGas = b.stateGas := by
  have covered : ((feeGetterMemory M fee).read 0 32).2 = feeGetterMemory M fee := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le (getter_memory_alignment aligned)
    rw [getter_memory_size aligned]
    exact Nat.le_max_right _ _
  refine ⟨?_, rfl, ?_, rfl, ?_, rfl, rfl⟩
  · exact Mem.read_write_word_of_wf wf 0 fee
  · change {b.meta with output := ((M.write 0 fee.toBytes).read 0 32).1} = _
    rw [Mem.read_write_word_of_wf wf]
  · exact covered

/-- Full raw getter execution charge, excluding any call-frame settlement charge. -/
def userFeeGetterGas (sevm : Sevm) (b : Devm) (M : Mem) (iterations : Nat) : Nat :=
  feeGetterGas M + 75 + feeLoopGas iterations + userSetupGas sevm b + dispatchGas

theorem userFeeGetterGas_eq (sevm : Sevm) (b : Devm) (M : Mem) (iterations : Nat) :
    userFeeGetterGas sevm b M iterations =
      177 + 87 * iterations + sloadCost sevm b 0 +
        (calculateMemoryGasCost (memExtSize M.size 0 32) - calculateMemoryGasCost M.size) := by
  calc
    _ = (10 + 75 + 25 + 46 + 21) + (87 * iterations + sloadCost sevm b 0 +
        (calculateMemoryGasCost (memExtSize M.size 0 32) - calculateMemoryGasCost M.size)) := by
      simp only [userFeeGetterGas, feeGetterGas, feeGetterFixedGas_eq, feeLoopGas_eq,
        userSetupGas, userSetupFixedGas_eq, dispatchGas_eq,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    _ = _ := by simp only [← Nat.add_assoc]

theorem userFeeGetterGas_empty (sevm : Sevm) (b : Devm) (iterations : Nat) :
    userFeeGetterGas sevm b Mem.empty iterations = 180 + 87 * iterations + sloadCost sevm b 0 := by
  calc
    _ = (13 + 75 + 25 + 46 + 21) + (87 * iterations + sloadCost sevm b 0) := by
      simp only [userFeeGetterGas, feeGetterGas_empty, feeLoopGas_eq,
        userSetupGas, userSetupFixedGas_eq, dispatchGas_eq,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    _ = _ := by simp only [← Nat.add_assoc]

/-- Successful canonical empty-calldata execution returns the actual finite word fee. -/
theorem exec_fee_getter {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = Blanc.withdrawalRequestCode) (hfork : CoveredFork sevm.benvStat.fork)
    (hstack : pre.stack = []) (aligned : pre.memory.size % 32 = 0)
    (wf : Mem.Wf pre.memory)
    (user : sevm.caller ≠ systemAddress) (empty : sevm.data = [])
    (exec : Exec 0 sevm pre (.ok post)) :
    sevm.value = 0 ∧ pre.getStorVal sevm.currentTarget 0 ≠ B256.max ∧
    ∃ iterations finalOutput,
      WordFakeExponential.Run (pre.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations finalOutput ∧
      ∃ G, post = feeGetterPost (afterSload sevm pre 0) pre.memory (finalOutput / (17 : B256)) G ∧
        post.output = (finalOutput / (17 : B256)).toBytes := by
  obtain ⟨active, iterations, finalOutput, wordRun, accepted⟩ :=
    exec_user_fee_dispatch hcode hfork hstack user exec
  rcases accepted with ⟨hlen, _, _⟩ | ⟨_, zero, _, run⟩
  · simp only [empty, List.length_nil] at hlen
    exact False.elim ((by decide : (0 : B256) ≠ 56) hlen)
  · obtain ⟨G, postEq⟩ := fee_getter_inv aligned run
    exact ⟨zero, active, iterations, finalOutput, wordRun, G, postEq,
      postEq ▸ (feeGetterPost_facts _ _ _ _ wf aligned).1⟩

/-- Construct a complete raw canonical getter Exec with an actual RETURN outcome. -/
theorem exec_fee_getter_exact {sevm : Sevm} {b : Devm} {M : Mem} {G iterations : Nat}
    {finalOutput : B256}
    (hcode : sevm.code = Blanc.withdrawalRequestCode) (hfork : CoveredFork sevm.benvStat.fork)
    (aligned : M.size % 32 = 0) (user : sevm.caller ≠ systemAddress)
    (empty : sevm.data = []) (zero : sevm.value = 0)
    (active : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (b.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations finalOutput) :
    Nonempty (Exec 0 sevm (St b [] M (G + userFeeGetterGas sevm b M iterations))
      (.ok (feeGetterPost (afterSload sevm b 0) M (finalOutput / (17 : B256)) G))) := by
  have hlen : sevm.data.length.toB256 = 0 := by rw [empty]; rfl
  have branchGas : userFeeDispatchGas sevm = 75 := by
    rw [userFeeDispatchGas_eq, hlen]
    rfl
  have tail := user_fee_prefix_exact hfork active wordRun
    (.inr ⟨hlen, zero, fee_getter_exact (b := afterSload sevm b 0)
      (fee := finalOutput / (17 : B256)) (G := G) aligned⟩)
  rw [branchGas] at tail
  have hgas : G + userFeeGetterGas sevm b M iterations =
      (G + feeGetterGas M + 75 + feeLoopGas iterations + userSetupGas sevm b) + dispatchGas := by
    simp only [userFeeGetterGas, Nat.add_assoc]
  rw [hgas]
  exact exec_of_dispatch hcode hfork (by
    simpa only [dispatchTail, ite_eq_right user] using tail)

/-- Fresh-memory specialization has the proved closed execution charge. -/
theorem exec_fee_getter_fresh {sevm : Sevm} {b : Devm} {G iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = Blanc.withdrawalRequestCode) (hfork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) (empty : sevm.data = []) (zero : sevm.value = 0)
    (active : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (b.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations finalOutput) :
    Nonempty (Exec 0 sevm (St b [] Mem.empty (G + (180 + 87 * iterations + sloadCost sevm b 0)))
      (.ok (feeGetterPost (afterSload sevm b 0) Mem.empty (finalOutput / (17 : B256)) G))) := by
  rw [← userFeeGetterGas_empty]
  exact exec_fee_getter_exact hcode hfork (by decide) user empty zero active wordRun

end Blanc.Lift.WithdrawalRequest
