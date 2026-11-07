import Blanc.Lift.BuilderRequest.AmsterdamMsgProbeFrame

/-!
# Probe: a successful deposit call through the top-level message path, under Amsterdam

Disposable (goal `blanc-eip8282-builder-requests-v1`, O16).
-/

namespace Blanc.Lift.BuilderRequest.Deposit

open Jaune
open Blanc.Lift.BuilderRequest.AmsterdamMsgProbe

local notation "A" => amsterdamStateGasRules

/-! ## The world a submission leaves -/

/-- The world after a submission over `σ`, stated at the account level. -/
def submittedState (sevm : Sevm) (σ : State) : State :=
  let ct := sevm.currentTarget
  let c := (σ.getStor ct).get 1
  let t := (σ.getStor ct).get 3
  let key := submissionKey t
  (((((((σ.setStorVal ct 1 (1 + c)).setStorVal ct key (Sevm.dataWord sevm 0)).setStorVal ct (1 + key)
    (Sevm.dataWord sevm 32)).setStorVal ct (1 + (1 + key)) (Sevm.dataWord sevm 64)).setStorVal ct
    (1 + (1 + (1 + key))) (Sevm.dataWord sevm 96)).setStorVal ct (1 + (1 + (1 + (1 + key))))
    (Sevm.dataWord sevm 128)).setStorVal ct (1 + (1 + (1 + (1 + (1 + key)))))
    (Sevm.dataWord sevm 160)).setStorVal ct 3 (1 + t)

variable {sevm : Sevm} {b : Devm} {M : Mem}

theorem tailWordA_eq (sevm : Sevm) (b : Devm) :
    tailWordA sevm b = b.getStorVal sevm.currentTarget 3 := by
  unfold tailWordA countStoreA Devm.getStorVal Devm.getAcct
  rw [afterSstoreA_state, afterSloadA_state]
  show ((b.state.setStorVal sevm.currentTarget 1 _).getStor sevm.currentTarget).get 3 =
    (b.state.getStor sevm.currentTarget).get 3
  rw [State.getStor_setStorVal_self, Stor.get_set_ne _ (by decide : (1 : B256) ≠ 3)]

theorem submissionBaseA_state (sevm : Sevm) (b : Devm) (M : Mem) :
    (submissionBaseA sevm (feeBaseA sevm b) M).state = submittedState sevm b.state := by
  have s0 : (feeBaseA sevm b).state = b.state := by
    unfold feeBaseA
    rw [afterSloadA_state, afterSloadA_state]
  have hc : countWord sevm (feeBaseA sevm b) = (b.state.getStor sevm.currentTarget).get 1 := by
    unfold countWord Devm.getStorVal Devm.getAcct
    rw [s0]
    rfl
  have ht : tailWordA sevm (feeBaseA sevm b) = (b.state.getStor sevm.currentTarget).get 3 := by
    rw [tailWordA_eq]
    unfold Devm.getStorVal Devm.getAcct
    rw [s0]
    rfl
  unfold submissionBaseA loggedA recordsWrittenA recordStoreA wordStoreA tailReadA countStoreA
  rw [hc, ht]
  have hlog : ∀ (d : Devm) (l : Log), (Devm.addLog d l).state = d.state := fun _ _ => rfl
  simp only [afterSstoreA_state, afterSloadA_state, hlog, s0]
  rfl

theorem submittedState_getStor (sevm : Sevm) (σ : State) :
    (submittedState sevm σ).getStor sevm.currentTarget =
      submittedStorage sevm (σ.getStor sevm.currentTarget) := by
  simp only [submittedState, State.getStor_setStorVal_self, submittedStorage]

theorem submittedState_get_ne (sevm : Sevm) (σ : State) {a : Adr} (h : sevm.currentTarget ≠ a) :
    (submittedState sevm σ).get a = σ.get a := by
  simp only [submittedState, State.get_setStorVal_ne _ _ _ h]

theorem setStorVal_get_self_fields (w : State) (t : Adr) (k v : B256) :
    ((w.setStorVal t k v).get t).bal = (w.get t).bal ∧
      ((w.setStorVal t k v).get t).code = (w.get t).code := by
  rw [State.get_setStorVal_self]
  exact ⟨rfl, rfl⟩

theorem submittedState_bal (sevm : Sevm) (σ : State) :
    ((submittedState sevm σ).get sevm.currentTarget).bal = (σ.get sevm.currentTarget).bal := by
  simp only [submittedState, (setStorVal_get_self_fields _ _ _ _).1]

/-! ## Logs, meter, and the prefix `Ready` carries -/

theorem balReadAccount_logs (r : ForkRules) (a : Adr) (d : Devm) :
    (d.balReadAccount r a).logs = d.logs := by
  unfold Devm.balReadAccount
  split <;> rfl

theorem balReadStorage_logs (r : ForkRules) (a : Adr) (k : B256) (d : Devm) :
    (d.balReadStorage r a k).logs = d.logs := by
  unfold Devm.balReadStorage
  split <;> rfl

theorem afterSstoreA_logs (sevm : Sevm) (d : Devm) (k v : B256) :
    (afterSstoreA A sevm d k v).logs = d.logs := by
  unfold afterSstoreA
  dsimp only
  show (Devm.balReadAccount _ _ _).logs = _
  rw [balReadAccount_logs]
  show (Devm.balReadStorage _ _ _ _).logs = _
  rw [balReadStorage_logs]
  split <;> rfl

theorem afterSloadA_logs (sevm : Sevm) (d : Devm) (k : B256) :
    (afterSloadA sevm d k).logs = d.logs := by
  unfold afterSloadA
  rw [balReadStorage_logs, afterSload_logs]

theorem submissionPostA_logs (sevm : Sevm) (b : Devm) (M : Mem) (G : Nat) :
    (submissionPostA sevm (feeBaseA sevm b) M G).logs = b.logs ++ [submissionLog sevm M] := by
  show (submissionBaseA sevm (feeBaseA sevm b) M).logs = _
  unfold submissionBaseA loggedA recordsWrittenA recordStoreA wordStoreA tailReadA countStoreA feeBaseA
  simp only [afterSstoreA_logs, Devm.addLog_logs, afterSloadA_logs]

local notation "SS" => amsterdamStateGasRules.storageSet

theorem meter_step {d : Devm} {k v : B256} {X j : Nat}
    (h : d.stateGas.spilled = 0 ∧ X + (j + 1) * SS ≤ d.stateGas.left) :
    (afterSstoreA A sevm d k v).stateGas.spilled = 0 ∧
      X + j * SS ≤ (afterSstoreA A sevm d k v).stateGas.left :=
  afterSstoreA_meter A h.1 (by
    have := h.2
    rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc] at this
    exact this)

theorem meter_records {d : Devm} {K : B256} {X j : Nat}
    (h : d.stateGas.spilled = 0 ∧ X + (j + 6) * SS ≤ d.stateGas.left) :
    (recordStoreA sevm d K).stateGas.spilled = 0 ∧ X + j * SS ≤ (recordStoreA sevm d K).stateGas.left :=
  meter_step (meter_step (meter_step (meter_step (meter_step (meter_step h)))))

theorem ready_records {d : Devm} {K : B256} {rest : List B256}
    (r : Ready sevm d (K :: (1 + K) :: (1 + (1 + K)) :: (1 + (1 + (1 + K))) ::
      (1 + (1 + (1 + (1 + K)))) :: (1 + (1 + (1 + (1 + (1 + K))))) :: rest))
    (nodup : (K :: (1 + K) :: (1 + (1 + K)) :: (1 + (1 + (1 + K))) ::
      (1 + (1 + (1 + (1 + K)))) :: (1 + (1 + (1 + (1 + (1 + K))))) :: rest).Nodup) :
    Ready sevm (recordStoreA sevm d K) rest := by
  have n1 := List.nodup_cons.mp nodup
  have n2 := List.nodup_cons.mp n1.2
  have n3 := List.nodup_cons.mp n2.2
  have n4 := List.nodup_cons.mp n3.2
  have n5 := List.nodup_cons.mp n4.2
  have n6 := List.nodup_cons.mp n5.2
  exact Ready.sstore (Ready.sstore (Ready.sstore (Ready.sstore (Ready.sstore (Ready.sstore r n1.1 _)
    n2.1 _) n3.1 _) n4.1 _) n5.1 _) n6.1 _

/-- What `Ready` and the meter give at the end: no error, nonnegative refund, no spill, at most eight
`storageSet`s drawn from the reservoir. -/
theorem submissionBaseA_ready {X : Nat} (b : Devm) (M : Mem)
    (r : Ready sevm b (bodyKeys (submissionKey (tailWordA sevm b))))
    (nodup : (bodyKeys (submissionKey (tailWordA sevm b))).Nodup)
    (hX : X + 8 * SS ≤ b.stateGas.left) :
    (submissionBaseA sevm b M).error = none ∧ 0 ≤ (submissionBaseA sevm b M).refundCounter ∧
      (submissionBaseA sevm b M).stateGas.spilled = 0 ∧ X ≤ (submissionBaseA sevm b M).stateGas.left := by
  have n0 := List.nodup_cons.mp nodup
  have rc := Ready.sstore (r.sload 1) n0.1 (1 + countWord sevm b)
  have rt : Ready sevm (tailReadA sevm b) _ := rc.sload 3
  have rw' : Ready sevm (recordsWrittenA sevm b) [3] := ready_records rt n0.2
  have re := Ready.sstore (Ready.addLog (submissionLog sevm M) rw') (List.not_mem_nil)
    (1 + tailWordA sevm b)
  have m1 : (countStoreA sevm b).stateGas.spilled = 0 ∧
      X + (1 + 6) * SS ≤ (countStoreA sevm b).stateGas.left :=
    meter_step (j := 1 + 6) ⟨by rw [afterSloadA_stateGas]; exact r.spill, by
      rw [afterSloadA_stateGas]
      exact hX⟩
  have m2 : (recordsWrittenA sevm b).stateGas.spilled = 0 ∧
      X + 1 * SS ≤ (recordsWrittenA sevm b).stateGas.left :=
    meter_records (j := 1) ⟨by unfold tailReadA; rw [afterSloadA_stateGas]; exact m1.1, by
      unfold tailReadA; rw [afterSloadA_stateGas]; exact m1.2⟩
  have m3 := meter_step (sevm := sevm) (d := loggedA sevm b M) (k := 3) (v := 1 + tailWordA sevm b)
    (X := X) (j := 0) ⟨m2.1, by
      have := m2.2
      exact this⟩
  refine ⟨re.error, re.refund, m3.1, ?_⟩
  have := m3.2
  simp only [Nat.zero_mul, Nat.add_zero] at this
  exact this

/-! ## The entry machine -/

theorem userEntry_ready {M : Msg} {benv : Benv} {code' : ByteArray} {X : Nat}
    (reserve : X + 8 * SS ≤ M.stateGasGrant) (keys : List B256) (hlen : keys.length = 8)
    (hclean : ∀ k ∈ keys, SlotClean (userSevm M code' benv) (userEntry M benv) k) :
    Ready (userSevm M code' benv) (userEntry M benv) keys where
  error := by
    show (userBase M).error = none
    unfold userBase
    simp only [balReadAccount_error]
    rfl
  refund := by
    show 0 ≤ (userBase M).refundCounter
    unfold userBase
    simp only [Devm.balReadAccount_refundCounter]
    exact Int.le_refl 0
  spill := rfl
  reservoir := by
    rw [hlen]
    show 8 * SS ≤ M.stateGasGrant
    omega
  clean := hclean

theorem code_undelegated : getDelegatedCodeAddress code = none := by decide +kernel

theorem Ready.feeBaseA {sevm : Sevm} {d : Devm} {ks : List B256} (r : Ready sevm d ks) :
    Ready sevm (Deposit.feeBaseA sevm d) ks := (r.sload 0).sload 1

/-- **A successful deposit call under Amsterdam, through the top-level message path.** The value moved
before the frame (`entry`); the frame reads the state after that; the transfer log `initDevm` seeded
stays ahead of the frame's `LOG0`; state gas drew at most eight `storageSet`s from the reservoir with no
spill. -/
theorem deposit_call_ok {M' : Msg} {benv : Benv} {G iterations X : Nat} {finalOutput : B256}
    (hfork : M'.benv.stat.fork = .amsterdam)
    (hauth : M'.tenv.stat.auths.isEmpty = true) (htarget : M'.target.isNone = false)
    (installed : M'.benv.state.getCode M'.currentTarget = code)
    (hnew : (M'.value != 0 && decide (M'.benv.state.get M'.currentTarget).Empty) = false)
    (hprecomp : ¬ amsterdamRules.isPrecomp M'.currentTarget)
    (entry : M'.benvAfterTransfer = .ok benv) (hstat : benv.stat = M'.benv.stat)
    (caller : M'.caller ≠ systemAddress) (hlen : M'.data.length = 184)
    (dynamic : M'.isStatic = false) (slack : gCallStipend < G)
    (hgas : M'.gas = G + submissionGasA (userSevm M' code benv) (userEntry M' benv) .empty iterations)
    (off : (userEntry M' benv).getStorVal M'.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run
      (storedExcess 8 (userSevm M' code benv) (userEntry M' benv)) 17 1 17 0 iterations finalOutput)
    (admitted : Admitted (userSevm M' code benv) (finalOutput / (17 : B256)))
    (reserve : X + 8 * SS ≤ M'.stateGasGrant)
    (hclean : ∀ k, SlotClean (userSevm M' code benv) (userEntry M' benv) k)
    (nodup : (bodyKeys (submissionKey (tailWordA (userSevm M' code benv)
      (Deposit.feeBaseA (userSevm M' code benv) (userEntry M' benv))))).Nodup) :
    let s := userSevm M' code benv
    let e := userEntry M' benv
    let post := submissionPostA s (Deposit.feeBaseA s e) .empty G
    processMessageCall M' = .ok (post.state, systemCallOutputA M' post) ∧
      post.state = submittedState s benv.state ∧
      post.logs = (initDevm M').logs ++ [⟨M'.currentTarget, [], M'.data⟩] ∧
      post.gasLeft = G ∧ post.stateGas.spilled = 0 ∧ X ≤ post.stateGas.left := by
  intro s e post
  have hsfork : s.benvStat.fork = .amsterdam := by
    show benv.stat.fork = _
    rw [hstat]
    exact hfork
  have r0 : Ready s e (bodyKeys (submissionKey (tailWordA s (Deposit.feeBaseA s e)))) :=
    userEntry_ready reserve _ rfl fun k _ => hclean k
  have r := Ready.feeBaseA r0
  have hrun := exec_submission_exactA (M := .empty) (sevm := s) (b := e) (G := G) (iterations := iterations)
    (finalOutput := finalOutput) rfl hsfork caller hlen dynamic slack off wordRun admitted r nodup
  have hSt : St e [] .empty (G + submissionGasA s e .empty iterations) = e := by
    rw [← hgas]
    exact St.self rfl rfl
  rw [hSt] at hrun
  have hexec := (exec_iff_exec_eq _ _ _ _).mp hrun
  have hX : X + 8 * SS ≤ (Deposit.feeBaseA s e).stateGas.left := by
    show X + 8 * SS ≤ _
    unfold Deposit.feeBaseA
    rw [afterSloadA_stateGas, afterSloadA_stateGas]
    exact reserve
  obtain ⟨herr, hrefund, hspill, hleft⟩ := submissionBaseA_ready (sevm := s) (M := .empty)
    (Deposit.feeBaseA s e) r nodup hX
  have hstate : post.state = submittedState s benv.state :=
    submissionBaseA_state s e .empty
  refine ⟨processMessageCall_ok hfork hauth htarget installed code_undelegated hnew hprecomp entry
      hstat hexec herr hrefund, hstate, ?_, rfl, hspill, hleft⟩
  have hlog := submissionPostA_logs s e .empty G
  have hlg : submissionLog s Mem.empty = ⟨M'.currentTarget, [], M'.data⟩ :=
    submissionLog_eq hlen (Mem.wf_empty)
  rw [hlg] at hlog
  refine hlog.trans ?_
  have : e.logs = (initDevm M').logs := by
    show (userBase M').logs = _
    unfold userBase
    simp only [balReadAccount_logs]
  rw [this]

/-- Under Amsterdam a value-moving call's entry log is the EIP-7708 transfer log. -/
theorem initDevm_logs_transfer {M' : Msg} (hfork : M'.benv.stat.fork = .amsterdam)
    (transfer : M'.shouldTransferValue = true) (distinct : M'.caller ≠ M'.currentTarget)
    (nonzero : M'.value ≠ 0) :
    (initDevm M').logs = [transferLog M'.caller M'.currentTarget M'.value] := by
  have hsg := Blanc.amsterdam_stateGas hfork
  show (match M'.benv.stat.rules.stateGas with
    | none => []
    | some _ => if M'.shouldTransferValue then (Devm.emitTransferLog _ _ _ _).logs else []) = _
  rw [hsg]
  simp only [transfer, ↓reduceIte, Devm.emitTransferLog, distinct, nonzero, or_self]
  rfl

end Blanc.Lift.BuilderRequest.Deposit
