import Blanc.Lift.Deploy
import Blanc.Lift.RequestFee.Window

/-!
# The request contracts' fee getter

After the fee quotient is computed, a request contract's getter path requires empty calldata and
zero value, then writes the quotient at memory offset zero and returns it. The two guards differ
between contracts only in the pushed revert target and its tree, so those are parameters of
`guardTree`; the return tree `returnTree` has none.

Memory and `RETURN` state are named to keep symbolic byte arrays opaque during the walk. Exact
walks take `PUSH0`'s activation as a hypothesis and assume no other fork fact.
-/

namespace Blanc.Lift.RequestFee

open Jaune

/-- CALLDATASIZE must be zero and CALLVALUE must be zero, else the revert tree. -/
def guardTree (dest : PushWord) (accept revert : SFunc) : SFunc :=
  (.next (.reg .calldatasize) (.next (.push (dest.head :: dest.tail) dest.le)
  (.branch (.next (.reg .callvalue) (.next (.push (dest.head :: dest.tail) dest.le)
  (.branch accept revert))) revert)))

/-- `PUSH0; MSTORE; PUSH1 32; PUSH0; RETURN`. -/
def returnTree : SFunc :=
  (.next (.push [] (by decide)) (.next (.reg .mstore) (.next (.push [0x20] (by decide))
  (.next (.push [] (by decide)) (.last .return_)))))

/-- CALLDATASIZE/PUSH/JUMPI followed by CALLVALUE/PUSH/JUMPI. -/
def getterGuardGas : Nat := 2 * (gBase + gVerylow + gHigh)

theorem getterGuardGas_eq : getterGuardGas = 30 := rfl

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

section Walks

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {fee : B256}

/-- Success passes both guards. -/
theorem guard_inv {dest : PushWord} {accept revert : SFunc}
    {o : Outcome} (noOk : revert.noOk = true)
    (run : SFunc.Run fs sevm (St b [fee] M G) (guardTree dest accept revert) o) :
    sevm.data.length.toB256 = 0 ∧ sevm.value = 0 ∧
      ∃ G', SFunc.Run fs sevm (St b [fee] M G') accept o := by
  have run := run.cut
  unfold guardTree at run
  winv 2
  rcases ric_branch run with ⟨empty, _, run⟩ | ⟨_, _, run⟩
  · obtain ⟨_, h, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_callvalue h
    winv 1
    rcases ric_branch run with ⟨zero, G', run⟩ | ⟨_, _, run⟩
    · exact ⟨empty, zero, G', run.uncut⟩
    · exact False.elim (run.false_of_noOk noOk)
  · exact False.elim (run.false_of_noOk noOk)

/-- Both guards, forward, at their exact charge of 30. -/
theorem guard_exact {dest : PushWord} {accept revert : SFunc}
    {o : Outcome} (empty : sevm.data.length.toB256 = 0) (zero : sevm.value = 0)
    (tail : SFunc.RunExact fs sevm (St b [fee] M G) accept o) :
    SFunc.RunExact fs sevm (St b [fee] M (G + 30)) (guardTree dest accept revert) o := by
  have hgas : G + 30 = G + 10 + 3 + 2 + 10 + 3 + 2 := by
    simp only [Nat.add_assoc]
  rw [hgas]
  unfold guardTree
  refine rx_calldatasize (by change 1 < 1024; decide) ?_
  rw [empty]
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_branch_zero ?_
  refine rx_callvalue (by change 1 < 1024; decide) ?_
  rw [zero]
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  exact rx_branch_zero tail

/-- A successful getter leaves exactly the named RETURN state, including its error field. -/
theorem return_inv {post : Devm} (aligned : M.size % 32 = 0)
    (run : SFunc.Run fs sevm (St b [fee] M G) returnTree (.halted post)) :
    ∃ G', post = feeGetterPost b M fee G' := by
  unfold returnTree at run
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
            have expected : SFunc.RunExact fs sevm
                (St b [0, 32] (feeGetterMemory M fee) gas) (.last .return_)
                (.halted (feeGetterPost b M fee gas)) :=
              rx_return_any rfl (getter_return_free aligned)
            cases expected with
            | last expected =>
              exact ⟨_, Except.ok.inj (actual.symm.trans expected)⟩

/-- Construct the actual return outcome at exactly the getter charge. -/
theorem return_exact (h_push0 : sevm.benvStat.rules.op.push0 = true)
    (aligned : M.size % 32 = 0) :
    SFunc.RunExact fs sevm (St b [fee] M (G + feeGetterGas M)) returnTree
      (.halted (feeGetterPost b M fee G)) := by
  let expansion := calculateMemoryGasCost (memExtSize M.size 0 32) - calculateMemoryGasCost M.size
  have hgas : G + feeGetterGas M = G + 2 + 3 + (3 + expansion) + 2 := by
    simp only [feeGetterGas, feeGetterFixedGas_eq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    congr 1
    simp only [expansion, ← Nat.add_assoc]
  rw [hgas]
  unfold returnTree
  refine rx_push0 (h_push0 := h_push0) (by change 1 < 1024; decide) ?_
  refine rx_mstore (c := 3 + expansion) ?_ rfl ?_
  · rw [St.extCost_eq rfl]
    rfl
  · refine rx_push (w := (32 : B256)) rfl (by decide) ?_
    refine rx_push0 (h_push0 := h_push0) (by change 1 < 1024; decide) ?_
    exact rx_return_any rfl (getter_return_free aligned)

end Walks

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

end Blanc.Lift.RequestFee
