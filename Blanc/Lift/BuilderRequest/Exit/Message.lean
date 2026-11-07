import Blanc.Lift.BuilderRequest.Exit.SubmissionAmsterdam
import Blanc.Lift.BuilderRequest.Message

/-!
# The exit contract's direct messages under Amsterdam

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

`submissions` is what the top-level path needs of an exit submission. Direct calls only: no nested frames, no
history.
-/

namespace Blanc.Lift.BuilderRequest.Exit

open Jaune

/-- The world after a submission over `σ`, at the account level, in the bytes' write order. -/
def submittedState (sevm : Sevm) (σ : State) : State :=
  let a := sevm.currentTarget
  let tail := (σ.getStor a).get 3
  let key := submissionKey tail
  (((((σ.setStorVal a 1 (1 + (σ.getStor a).get 1)).setStorVal a key sevm.caller.toB256).setStorVal a (1 + key)
    (Sevm.dataWord sevm 0)).setStorVal a (1 + (1 + key)) (Sevm.dataWord sevm 32)).setStorVal a 3 (1 + tail))

/-- The slots a submission writes, in order, at tail word `tail`. -/
def bodyKeys (tail : B256) : List B256 :=
  let k := submissionKey tail
  [1, k, 1 + k, 1 + (1 + k), 3]

/-- What the guard accepts: value covering the quoted fee. -/
def Admits (_data : Bytes) (value fee : B256) : Prop := fee.toNat ≤ value.toNat

theorem bodyKeys_nodup (t : B256) (h : t.toNat < 2 ^ 253) : (bodyKeys t).Nodup := by
  have hk : (submissionKey t).toNat = 4 + 3 * t.toNat := by
    have h3 : (3 * t).toNat = 3 * t.toNat := by
      rw [B256.toNat_mul, show (3 : B256).toNat = 3 by decide, Nat.lo]
      exact Nat.mod_eq_of_lt (by omega)
    rw [submissionKey, B256.toNat_add_eq_of_nof _ _ (by unfold B256.Nof; rw [h3, show (4 : B256).toNat = 4 by decide]; omega),
      h3, show (4 : B256).toNat = 4 by decide]
  have one : ∀ {x : B256} {m : Nat}, x.toNat = m → m + 1 < 2 ^ 256 → (1 + x).toNat = m + 1 := by
    intro x m hx hm
    rw [B256.toNat_add_eq_of_nof _ _ (by unfold B256.Nof; rw [hx, show (1 : B256).toNat = 1 by decide]; omega), hx,
      show (1 : B256).toNat = 1 by decide, Nat.add_comm]
  have k1 := one hk (by omega)
  have k2 := one k1 (by omega)
  refine List.Nodup.of_map B256.toNat ?_
  simp only [bodyKeys, List.map_cons, List.map_nil, hk, k1, k2,
    show (1 : B256).toNat = 1 by decide, show (3 : B256).toNat = 3 by decide, List.nodup_cons,
    List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil, and_true]
  omega

variable {s : Sevm} {b : Devm} {M : Mem} {G grant used : Nat}

/-- A submission on untouched slots keeps the frame `Fresh` and repays nothing. -/
theorem post_fresh (hfork : s.benvStat.fork = .amsterdam)
    (r : Fresh s b (bodyKeys (b.getStorVal s.currentTarget 3)) grant used 5)
    (nd : (bodyKeys (b.getStorVal s.currentTarget 3)).Nodup) :
    (∃ used', Fresh s (submissionPostA s (feeBaseA s b) M G) [] grant used' 5) ∧
      submissionRepayA s b M = 0 := by
  have ht : (amsterdamSteps s).tailWord (feeBaseA s b) = b.getStorVal s.currentTarget 3 :=
    ((amsterdamSteps_valid hfork).tailWord_eq _).trans ((amsterdamSteps_valid hfork).read_feeBase 3 _ b)
  have r0 : Fresh s (feeBaseA s b) (bodyKeys (b.getStorVal s.currentTarget 3)) grant used 5 := (r.sload 0).sload 1
  obtain ⟨⟨_, r1⟩, n1, rp1⟩ := (r0.sload 1).step nd (1 + countWord s (feeBaseA s b))
  obtain ⟨⟨_, r2⟩, n2, rp2⟩ := (r1.sload 3).step n1 s.caller.toB256
  obtain ⟨⟨_, r3⟩, n3, rp3⟩ := r2.step n2 (Sevm.dataWord s 0)
  obtain ⟨⟨_, r4⟩, n4, rp4⟩ := r3.step n3 (Sevm.dataWord s 32)
  obtain ⟨⟨_, r5⟩, -, rp5⟩ := (r4.addLog (submissionLog s M)).step n4 (1 + b.getStorVal s.currentTarget 3)
  have add0 : ∀ {a b : Nat}, a = 0 → b = 0 → a + b = 0 := fun ha hb => by rw [ha, hb]
  refine ⟨?_, ?_⟩
  · unfold submissionPostA Steps.submissionPost Steps.submissionBase Steps.logged Steps.recordsWritten
    rw [ht]
    exact ⟨_, r5.st _ _ _⟩
  · unfold submissionRepayA Steps.bodyRepay Steps.logged Steps.recordsWritten
    simp only [ht]
    exact add0 (add0 (add0 (add0 rp1 rp2) rp3) rp4) rp5

/-- The memory an exit submission's fixed steps pay for, from empty memory: `MSTORE` at 0, `CALLDATACOPY` at 20,
`LOG0` of 68 bytes. -/
theorem memory_gas (s : Sevm) :
    sourceGas .empty + copyGas (Mem.empty.write 0 (sourceWord s).toBytes) + log0Gas (copyMemory s .empty) 68 =
      6 + 15 + 919 := by
  have hword : (Mem.empty.write 0 (sourceWord s).toBytes).size = 32 := by
    rw [Mem.size_write_of_length (len := 32) (B256.length_toBytes _) (by decide)]
    rfl
  have hlen : (s.data.sliceD 0 48 0).length = 48 := List.length_sliceD _ _ _ _
  have hsize : (copyMemory s .empty).size = 96 := by
    rw [copyMemory, Mem.size_write_of_length hlen (by decide), hword]
    rfl
  unfold copyGas log0Gas
  rw [hword, hsize]
  rfl

theorem gas_le (s : Sevm) (b : Devm) (n : Nat) :
    submissionGasA s b .empty n ≤ 1236 + 87 * n + 4 * gasColdSload +
      5 * (gasColdSload + amsterdamStateGasRules.storageWrite) + 5 * amsterdamStateGasRules.storageSet := by
  have W := writeCharge_le s
  have L := sloadCost_le s
  have R : ∀ d K, Steps.recordWritesGas (amsterdamSteps s) d K ≤
      3 * ((gasColdSload + amsterdamStateGasRules.storageWrite) + amsterdamStateGasRules.storageSet) :=
    fun d K => (Nat.add_le_add (Nat.add_le_add (W _ _ _) (W _ _ _)) (W _ _ _)).trans (by omega)
  have CL := memory_gas s
  unfold submissionGasA submissionGasOn Steps.bodyGas StorageSteps.feePathGas
  rw [RequestFee.feeLoopGas_eq, feePathFixedGas, RequestSystem.dispatchGas]
  have a1 := L b 0
  have a2 := L ((amsterdamSteps s).afterRead b 0) 1
  have a3 := L ((amsterdamSteps s).feeBase b) 1
  have a4 := L ((amsterdamSteps s).countStore ((amsterdamSteps s).feeBase b)) 3
  have w1 := W ((amsterdamSteps s).afterRead ((amsterdamSteps s).feeBase b) 1)
    1 (1 + countWord s ((amsterdamSteps s).feeBase b))
  have w2 := W (Steps.logged (amsterdamSteps s) ((amsterdamSteps s).feeBase b) .empty) 3
    (1 + (amsterdamSteps s).tailWord ((amsterdamSteps s).feeBase b))
  have w3 := R ((amsterdamSteps s).tailRead ((amsterdamSteps s).feeBase b))
    (submissionKey ((amsterdamSteps s).tailWord ((amsterdamSteps s).feeBase b)))
  omega

/-- What the top-level path needs of an exit submission. -/
def submissions : Submissions where
  toUserFrames := frames
  nonempty := by decide +kernel
  undelegated := by decide +kernel
  len := 48
  target := 2
  stores := 5
  loads := 4
  fixed := 1236
  Admit := Admits
  Post := fun s b M G => submissionPostA s (feeBaseA s b) M G
  Gas := submissionGasA
  Repay := submissionRepayA
  log := fun s => ⟨s.currentTarget, [], s.caller.toBytes ++ s.data⟩
  world := submittedState
  keys := bodyKeys
  exec := fun hcode hfork caller hlen dynamic slack off wordRun admit =>
    exec_submission_amsterdam hcode hfork caller hlen dynamic slack off wordRun admit
  fresh := fun hfork r nd => post_fresh hfork r nd
  keys_length := fun _ => rfl
  nodup := bodyKeys_nodup
  gasLeft := rfl
  state := fun hfork => submissionBase_state (amsterdamSteps_valid hfork)
  logs := fun hfork hlen => (submissionPostA_effects hfork hlen Mem.wf_empty _).logs
  gas_le := gas_le

end Blanc.Lift.BuilderRequest.Exit
