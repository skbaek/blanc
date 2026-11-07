import Blanc.Lift.BuilderRequest.Deposit.SubmissionAmsterdam
import Blanc.Lift.BuilderRequest.Message

/-!
# The deposit contract's direct messages under Amsterdam

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

`submissions` is what the top-level path needs of a deposit submission. Direct calls only: no nested frames, no
history.
-/

namespace Blanc.Lift.BuilderRequest.Deposit

open Jaune

local notation "A" => amsterdamStateGasRules

/-- The world after a submission over `σ`, at the account level, in the bytes' write order. -/
def submittedState (sevm : Sevm) (σ : State) : State :=
  let a := sevm.currentTarget
  let tail := (σ.getStor a).get 3
  let key := submissionKey tail
  ((((((((σ.setStorVal a 1 (1 + (σ.getStor a).get 1)).setStorVal a key
    (Sevm.dataWord sevm 0)).setStorVal a (1 + key) (Sevm.dataWord sevm 32)).setStorVal a (1 + (1 + key))
    (Sevm.dataWord sevm 64)).setStorVal a (1 + (1 + (1 + key))) (Sevm.dataWord sevm 96)).setStorVal a
    (1 + (1 + (1 + (1 + key)))) (Sevm.dataWord sevm 128)).setStorVal a
    (1 + (1 + (1 + (1 + (1 + key))))) (Sevm.dataWord sevm 160)).setStorVal a 3 (1 + tail))

/-- The slots a submission writes, in order, at tail word `tail`. -/
def bodyKeys (tail : B256) : List B256 :=
  let k := submissionKey tail
  [1, k, 1 + k, 1 + (1 + k), 1 + (1 + (1 + k)), 1 + (1 + (1 + (1 + k))), 1 + (1 + (1 + (1 + (1 + k)))), 3]

/-- The wei a submission's calldata credits. -/
def creditOf (data : Bytes) : Nat := (amountMask &&& Bytes.toB256 (data.sliceD 56 32 0)).toNat * 10 ^ 9

/-- What the guards accept, from the calldata, the value and the quoted fee: at least 1 ETH credited, and value
covering the credit plus the fee. -/
def Admits (data : Bytes) (value fee : B256) : Prop :=
  10 ^ 18 ≤ creditOf data ∧ creditOf data + fee.toNat ≤ value.toNat

theorem creditedWei_eq (sevm : Sevm) : creditedWei sevm = creditOf sevm.data := rfl

theorem bodyKeys_nodup (t : B256) (h : t.toNat < 2 ^ 253) : (bodyKeys t).Nodup := by
  have hk : (submissionKey t).toNat = 4 + 6 * t.toNat := by
    have h6 : (6 * t).toNat = 6 * t.toNat := by
      rw [B256.toNat_mul, show (6 : B256).toNat = 6 by decide, Nat.lo]
      exact Nat.mod_eq_of_lt (by omega)
    rw [submissionKey, B256.toNat_add_eq_of_nof _ _ (by unfold B256.Nof; rw [h6, show (4 : B256).toNat = 4 by decide]; omega),
      h6, show (4 : B256).toNat = 4 by decide]
  have one : ∀ {x : B256} {m : Nat}, x.toNat = m → m + 1 < 2 ^ 256 → (1 + x).toNat = m + 1 := by
    intro x m hx hm
    rw [B256.toNat_add_eq_of_nof _ _ (by unfold B256.Nof; rw [hx, show (1 : B256).toNat = 1 by decide]; omega), hx,
      show (1 : B256).toNat = 1 by decide, Nat.add_comm]
  have k1 := one hk (by omega)
  have k2 := one k1 (by omega)
  have k3 := one k2 (by omega)
  have k4 := one k3 (by omega)
  have k5 := one k4 (by omega)
  refine List.Nodup.of_map B256.toNat ?_
  simp only [bodyKeys, List.map_cons, List.map_nil, hk, k1, k2, k3, k4, k5,
    show (1 : B256).toNat = 1 by decide, show (3 : B256).toNat = 3 by decide, List.nodup_cons,
    List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil, and_true]
  omega

variable {s : Sevm} {b : Devm} {M : Mem} {G grant used : Nat}

/-- The six record stores on untouched slots keep the frame `Fresh` and repay nothing. -/
theorem records_fresh {d : Devm} {K : B256} {ks : List B256}
    (r : Fresh s d (K :: (1 + K) :: (1 + (1 + K)) :: (1 + (1 + (1 + K))) :: (1 + (1 + (1 + (1 + K)))) ::
      (1 + (1 + (1 + (1 + (1 + K))))) :: ks) grant used 8)
    (nd : (K :: (1 + K) :: (1 + (1 + K)) :: (1 + (1 + (1 + K))) :: (1 + (1 + (1 + (1 + K)))) ::
      (1 + (1 + (1 + (1 + (1 + K))))) :: ks).Nodup) :
    (∃ u, Fresh s (Steps.recordStore (amsterdamSteps s) d K) ks grant u 8) ∧ ks.Nodup ∧
      Steps.recordWritesRepay (amsterdamSteps s) d K = 0 := by
  obtain ⟨⟨_, r⟩, nd, rp0⟩ := r.step nd (Sevm.dataWord s 0)
  obtain ⟨⟨_, r⟩, nd, rp1⟩ := r.step nd (Sevm.dataWord s 32)
  obtain ⟨⟨_, r⟩, nd, rp2⟩ := r.step nd (Sevm.dataWord s 64)
  obtain ⟨⟨_, r⟩, nd, rp3⟩ := r.step nd (Sevm.dataWord s 96)
  obtain ⟨⟨_, r⟩, nd, rp4⟩ := r.step nd (Sevm.dataWord s 128)
  obtain ⟨⟨_, r⟩, nd, rp5⟩ := r.step nd (Sevm.dataWord s 160)
  refine ⟨⟨_, r⟩, nd, ?_⟩
  have add0 : ∀ {a b : Nat}, a = 0 → b = 0 → a + b = 0 := fun ha hb => by rw [ha, hb]
  exact add0 (add0 (add0 (add0 (add0 rp0 rp1) rp2) rp3) rp4) rp5

/-- A submission on untouched slots keeps the frame `Fresh` and repays nothing. -/
theorem post_fresh (hfork : s.benvStat.fork = .amsterdam)
    (r : Fresh s b (bodyKeys (b.getStorVal s.currentTarget 3)) grant used 8)
    (nd : (bodyKeys (b.getStorVal s.currentTarget 3)).Nodup) :
    (∃ used', Fresh s (submissionPostA s (feeBaseA s b) M G) [] grant used' 8) ∧
      submissionRepayA s b M = 0 := by
  have ht : (amsterdamSteps s).tailWord (feeBaseA s b) = b.getStorVal s.currentTarget 3 :=
    ((amsterdamSteps_valid hfork).tailWord_eq _).trans ((amsterdamSteps_valid hfork).read_feeBase 3 _ b)
  have r0 : Fresh s (feeBaseA s b) (bodyKeys (b.getStorVal s.currentTarget 3)) grant used 8 := (r.sload 0).sload 1
  obtain ⟨⟨_, r1⟩, n1, rp1⟩ := (r0.sload 1).step nd (1 + countWord s (feeBaseA s b))
  obtain ⟨⟨_, r2⟩, n2, rp2⟩ := records_fresh (r1.sload 3) n1
  obtain ⟨⟨_, r3⟩, -, rp3⟩ := (r2.addLog (submissionLog s M)).step n2 (1 + b.getStorVal s.currentTarget 3)
  have add0 : ∀ {a b : Nat}, a = 0 → b = 0 → a + b = 0 := fun ha hb => by rw [ha, hb]
  refine ⟨?_, ?_⟩
  · unfold submissionPostA Steps.submissionPost Steps.submissionBase Steps.logged Steps.recordsWritten
    rw [ht]
    exact ⟨_, r3.st _ _ _⟩
  · unfold submissionRepayA Steps.bodyRepay Steps.logged Steps.recordsWritten
    rw [ht]
    exact add0 (add0 rp1 rp2) rp3

/-- `CALLDATACOPY` of the payload into empty memory, and its `LOG0`, in gas. -/
theorem copyLog_gas (s : Sevm) : copyGas .empty + logGas (sevm := s) .empty = 39 + 1847 := by
  have hlen : (s.data.sliceD 0 184 0).length = 184 := List.length_sliceD _ _ _ _
  have hsize : (copyMemory s .empty).size = 192 := by
    rw [copyMemory, Mem.size_write_of_length hlen (by decide)]
    rfl
  unfold logGas log0Gas
  rw [hsize]
  rfl

theorem gas_le (s : Sevm) (b : Devm) (n : Nat) :
    submissionGasA s b .empty n ≤ 2289 + 87 * n + 4 * gasColdSload +
      8 * (gasColdSload + amsterdamStateGasRules.storageWrite) + 8 * amsterdamStateGasRules.storageSet := by
  have W := writeCharge_le s
  have L := sloadCost_le s
  have R : ∀ d K, Steps.recordWritesGas (amsterdamSteps s) d K ≤
      6 * ((gasColdSload + amsterdamStateGasRules.storageWrite) + amsterdamStateGasRules.storageSet) :=
    fun d K => (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (W _ _ _) (W _ _ _)) (W _ _ _)) (W _ _ _)) (W _ _ _)) (W _ _ _)).trans (by omega)
  have CL := copyLog_gas s
  unfold submissionGasA submissionGasOn Steps.bodyGas StorageSteps.feePathGas
  rw [RequestFee.feeLoopGas_eq, feePathFixedGas, RequestSystem.dispatchGas]
  have a1 := L b 0
  have a2 := L ((amsterdamSteps s).afterRead b 0) 1
  have a3 := L ((amsterdamSteps s).feeBase b) 1
  have a4 := L ((amsterdamSteps s).countStore ((amsterdamSteps s).feeBase b)) 3
  have w1 := W ((amsterdamSteps s).afterRead ((amsterdamSteps s).feeBase b) 1) 1
    (1 + countWord s ((amsterdamSteps s).feeBase b))
  have w2 := W (Steps.logged (amsterdamSteps s) ((amsterdamSteps s).feeBase b) .empty) 3
    (1 + (amsterdamSteps s).tailWord ((amsterdamSteps s).feeBase b))
  have w3 := R ((amsterdamSteps s).tailRead ((amsterdamSteps s).feeBase b))
    (submissionKey ((amsterdamSteps s).tailWord ((amsterdamSteps s).feeBase b)))
  omega

/-- What the top-level path needs of a deposit submission. -/
def submissions : Submissions where
  toUserFrames := frames
  nonempty := by decide +kernel
  undelegated := by decide +kernel
  len := 184
  target := 8
  stores := 8
  loads := 4
  fixed := 2289
  Admit := Admits
  Post := fun s b M G => submissionPostA s (feeBaseA s b) M G
  Gas := submissionGasA
  Repay := submissionRepayA
  log := fun s => ⟨s.currentTarget, [], s.data⟩
  world := submittedState
  keys := bodyKeys
  exec := fun hcode hfork caller hlen dynamic slack off wordRun admit =>
    exec_submission_exact_amsterdam hcode hfork caller hlen dynamic slack off wordRun ⟨admit.1, admit.2⟩
  fresh := fun hfork r nd => post_fresh hfork r nd
  keys_length := fun _ => rfl
  nodup := bodyKeys_nodup
  gasLeft := rfl
  state := fun hfork => submissionBase_state (amsterdamSteps_valid hfork)
  logs := fun hfork hlen => (submissionPostA_effects hfork hlen Mem.wf_empty _).logs
  gas_le := gas_le

end Blanc.Lift.BuilderRequest.Deposit
