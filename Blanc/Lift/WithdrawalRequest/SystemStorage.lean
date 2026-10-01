import Blanc.Lift.WithdrawalRequest.SystemBookkeeping
import Blanc.Lift.WithdrawalRequest.SystemOutput
import Blanc.Lift.ExactWalkSolc

/-! Conditional correspondence of the actual system frame with the queue model. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune
open Blanc.WithdrawalRequest

theorem systemAdvancedHead_represented (sevm : Sevm) (base : Devm)
    (state : WithdrawalRequest.State)
    (rep : RepresentsStorage (base.getStorVal sevm.currentTarget) state) :
    systemAdvancedHead (systemHead sevm base) (systemCount sevm base) =
      (state.head + min 16 state.queue.length).toB256 := by
  have coherent := rep.coherent
  change state.head + state.queue.length = state.tail at coherent
  have cap := Nat.min_le_right 16 state.queue.length
  have tailBound := rep.bounds.tail_lt
  rw [systemAdvancedHead, systemHead_represented sevm base state rep,
    ← toB256_toNat (systemCount sevm base), systemCount_represented sevm base state rep,
    toB256_add_toB256 (by omega : state.head + min 16 state.queue.length < 2 ^ 256)]

theorem systemPointers_drained_iff (sevm : Sevm) (base : Devm)
    (state : WithdrawalRequest.State)
    (rep : RepresentsStorage (base.getStorVal sevm.currentTarget) state) :
    systemAdvancedHead (systemHead sevm base) (systemCount sevm base) =
      systemTail sevm base ↔ state.queue.length ≤ 16 := by
  have coherent := rep.coherent
  change state.head + state.queue.length = state.tail at coherent
  have cap := Nat.min_le_right 16 state.queue.length
  have advancedBound : state.head + min 16 state.queue.length < 2 ^ 256 := by
    have tailBound := rep.bounds.tail_lt
    omega
  rw [systemAdvancedHead_represented sevm base state rep,
    systemTail_represented sevm base state rep]
  constructor
  · intro eq
    have numeric := congrArg B256.toNat eq
    rw [B256.toNat_toB256_of_lt advancedBound,
      B256.toNat_toB256_of_lt rep.bounds.tail_lt] at numeric
    omega
  · intro drained
    congr 1
    omega

theorem systemLoopFold_logs (sevm : Sevm) (head : B256) (index remaining : Nat)
    (base : Devm) (memory : Mem) :
    (systemLoopFold sevm head index remaining base memory).base.logs = base.logs := by
  induction remaining generalizing index base memory with
  | zero => rfl
  | succ remaining ih =>
    simp only [systemLoopFold]
    rw [ih]
    simp only [systemBodyBase, systemBodyBase2, systemBodyBase1, afterSload_logs]

theorem systemQueuePost_logs (sevm : Sevm) (base : Devm) (memory : Mem) :
    (systemQueuePost sevm base memory).base.logs = base.logs := by
  rw [systemQueuePost, systemLoopFold_logs]
  simp only [systemSetupBase, afterSload_logs]

theorem systemFramePointers_storage (sevm : Sevm) (base : Devm) (memory : Mem)
    (state : WithdrawalRequest.State)
    (rep : RepresentsStorage (base.getStorVal sevm.currentTarget) state) :
    (systemFramePointers sevm base memory).getStor sevm.currentTarget =
      if state.queue.length ≤ 16 then
        ((base.getStor sevm.currentTarget).set 2 0).set 3 0
      else (base.getStor sevm.currentTarget).set 2
        (state.head + min 16 state.queue.length).toB256 := by
  unfold systemFramePointers systemPointerBase
  simp only [systemPointers_drained_iff sevm base state rep]
  rw [systemAdvancedHead_represented sevm base state rep]
  split
  · rw [afterSstore_getStor_self, afterSstore_getStor_self, systemQueuePost_storage]
  · rw [afterSstore_getStor_self, systemQueuePost_storage]

theorem systemFramePointers_metadata (sevm : Sevm) (base : Devm) (memory : Mem)
    (state : WithdrawalRequest.State)
    (rep : RepresentsStorage (base.getStorVal sevm.currentTarget) state) :
    (systemFramePointers sevm base memory).getStorVal sevm.currentTarget 0 = state.excess.toB256 ∧
    (systemFramePointers sevm base memory).getStorVal sevm.currentTarget 1 = state.count.toB256 ∧
    (systemFramePointers sevm base memory).getStorVal sevm.currentTarget 2 =
      (WithdrawalRequest.system state).head.toB256 ∧
    (systemFramePointers sevm base memory).getStorVal sevm.currentTarget 3 =
      (WithdrawalRequest.system state).tail.toB256 := by
  simp only [getStorVal_eq_getStor]
  rw [systemFramePointers_storage sevm base memory state rep]
  by_cases drained : state.queue.length ≤ 16
  · have pointers := system_drained_pointers state drained
    rw [pointers.1, pointers.2]
    simp only [ite_eq_left drained, Stor.get_set_self,
      Stor.get_set_ne _ (by decide : (3 : B256) ≠ 0),
      Stor.get_set_ne _ (by decide : (2 : B256) ≠ 0),
      Stor.get_set_ne _ (by decide : (3 : B256) ≠ 1),
      Stor.get_set_ne _ (by decide : (2 : B256) ≠ 1),
      Stor.get_set_ne _ (by decide : (3 : B256) ≠ 2)]
    exact ⟨rep.excess, rep.count, rfl, rfl⟩
  · have pointers := system_live_pointers state drained
    rw [pointers.1, pointers.2, emitted_length]
    simp only [ite_eq_right drained, maxPerBlock, Stor.get_set_self,
      Stor.get_set_ne _ (by decide : (2 : B256) ≠ 0),
      Stor.get_set_ne _ (by decide : (2 : B256) ≠ 1),
      Stor.get_set_ne _ (by decide : (2 : B256) ≠ 3)]
    exact ⟨rep.excess, rep.count, True.intro, rep.tail⟩

theorem systemEffectiveExcess_represented (sevm : Sevm) (base : Devm) (memory : Mem)
    (state : WithdrawalRequest.State)
    (rep : RepresentsStorage (base.getStorVal sevm.currentTarget) state) :
    systemEffectiveExcess sevm (systemFramePointers sevm base memory) =
      (effectiveExcess state).toB256 := by
  have old := (systemFramePointers_metadata sevm base memory state rep).1
  have inhibitor : state.excess.toB256 = B256.max ↔ state.excess = excessInhibitor := by
    constructor
    · intro eq
      have numeric := congrArg B256.toNat eq
      rw [B256.toNat_toB256_of_lt rep.bounds.excess_lt] at numeric
      exact numeric
    · intro eq
      rw [eq]
      rfl
  simp only [systemEffectiveExcess, systemOldExcess, old, inhibitor, effectiveExcess]
  split <;> rfl

theorem systemPendingCount_represented (sevm : Sevm) (base : Devm) (memory : Mem)
    (state : WithdrawalRequest.State)
    (rep : RepresentsStorage (base.getStorVal sevm.currentTarget) state) :
    systemPendingCount sevm (systemFramePointers sevm base memory) = state.count.toB256 := by
  rw [systemPendingCount, systemExcessRead, getStorVal_afterSload]
  exact (systemFramePointers_metadata sevm base memory state rep).2.1

theorem systemNewExcess_represented (sevm : Sevm) (base : Devm) (memory : Mem)
    (state : WithdrawalRequest.State)
    (rep : RepresentsStorage (base.getStorVal sevm.currentTarget) state)
    (sumBound : effectiveExcess state + state.count < 2 ^ 256) :
    systemNewExcess sevm (systemFramePointers sevm base memory) =
      (WithdrawalRequest.system state).excess.toB256 := by
  have excessNat : (WithdrawalRequest.system state).excess =
      effectiveExcess state + state.count - 2 := by
    simp only [WithdrawalRequest.system, targetPerBlock]
  have sum : systemExcessSum sevm (systemFramePointers sevm base memory) =
      (effectiveExcess state + state.count).toB256 := by
    rw [systemExcessSum, systemPendingCount_represented sevm base memory state rep,
      systemEffectiveExcess_represented sevm base memory state rep,
      toB256_add_toB256 (by
        simpa only [Nat.add_comm state.count] using sumBound),
      Nat.add_comm state.count]
  have sumNat := B256.toNat_toB256_of_lt sumBound
  have branch : (2 : B256) < (effectiveExcess state + state.count).toB256 ↔
      2 < effectiveExcess state + state.count := by
    rw [B256.lt_iff_toNat_lt_toNat, sumNat]
    rfl
  simp only [systemNewExcess, sum, branch, excessNat]
  by_cases positive : 2 < effectiveExcess state + state.count
  · rw [ite_eq_left positive]
    exact toB256_sub_toB256 (a := effectiveExcess state + state.count) (b := 2)
      (Nat.le_of_lt positive) sumBound
  · rw [ite_eq_right positive, Nat.sub_eq_zero_of_le (Nat.le_of_not_lt positive)]
    rfl

theorem system_storageBounds (state : WithdrawalRequest.State) (coherent : Coherent state)
    (bounds : StorageBounds state)
    (sumBound : effectiveExcess state + state.count < 2 ^ 256) :
    StorageBounds (WithdrawalRequest.system state) := by
  have oldCoherent := coherent
  change state.head + state.queue.length = state.tail at oldCoherent
  have tailBound := bounds.tail_lt
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [system_excess]
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) sumBound
  · rw [system_count]
    decide
  · by_cases drained : state.queue.length ≤ maxPerBlock
    · rw [(system_drained_pointers state drained).1]
      decide
    · rw [(system_live_pointers state drained).1, emitted_length]
      have cap := Nat.min_le_right maxPerBlock state.queue.length
      omega
  · by_cases drained : state.queue.length ≤ maxPerBlock
    · rw [(system_drained_pointers state drained).2]
      decide
    · rw [(system_live_pointers state drained).2]
      exact tailBound
  · intro i hi
    rw [system_queue, List.length_drop] at hi
    by_cases drained : state.queue.length ≤ maxPerBlock
    · omega
    · have live : i + 16 < state.queue.length := by
        change i < state.queue.length - 16 at hi
        omega
      have oldBound := bounds.liveSlot_lt (i + 16) live
      rw [(system_live_pointers state drained).1, emitted_length,
        Nat.min_eq_left (Nat.le_of_not_ge drained)]
      change queueBase (state.head + 16 + i) + 2 < 2 ^ 256
      rw [show state.head + 16 + i = state.head + (i + 16) by omega]
      exact oldBound

theorem systemFramePost_storage (sevm : Sevm) (base : Devm) (memory : Mem) (gas : Nat) :
    (systemFramePost sevm base memory gas).getStor sevm.currentTarget =
      (((systemFramePointers sevm base memory).getStor sevm.currentTarget).set 0
        (systemNewExcess sevm (systemFramePointers sevm base memory))).set 1 0 := by
  rw [systemFramePost, systemBookkeepingPost,
    (returnPost_facts _ _ _ _).2.2.1 sevm.currentTarget, St_getStor]
  simp only [systemBookkeepingBase, systemExcessStore, systemCountRead, systemExcessRead,
    afterSstore_getStor_self, afterSload_getStor]

theorem systemFramePost_metadata (sevm : Sevm) (base : Devm) (memory : Mem) (gas : Nat)
    (state : WithdrawalRequest.State)
    (rep : RepresentsStorage (base.getStorVal sevm.currentTarget) state)
    (sumBound : effectiveExcess state + state.count < 2 ^ 256) :
    (systemFramePost sevm base memory gas).getStorVal sevm.currentTarget 0 =
      (WithdrawalRequest.system state).excess.toB256 ∧
    (systemFramePost sevm base memory gas).getStorVal sevm.currentTarget 1 =
      (WithdrawalRequest.system state).count.toB256 ∧
    (systemFramePost sevm base memory gas).getStorVal sevm.currentTarget 2 =
      (WithdrawalRequest.system state).head.toB256 ∧
    (systemFramePost sevm base memory gas).getStorVal sevm.currentTarget 3 =
      (WithdrawalRequest.system state).tail.toB256 := by
  simp only [getStorVal_eq_getStor]
  rw [systemFramePost_storage, systemNewExcess_represented sevm base memory state rep sumBound]
  simp only [Stor.get_set_self, Stor.get_set_ne _ (by decide : (1 : B256) ≠ 0),
    Stor.get_set_ne _ (by decide : (1 : B256) ≠ 2),
    Stor.get_set_ne _ (by decide : (0 : B256) ≠ 2),
    Stor.get_set_ne _ (by decide : (1 : B256) ≠ 3),
    Stor.get_set_ne _ (by decide : (0 : B256) ≠ 3), system_count]
  exact ⟨True.intro, rfl, (systemFramePointers_metadata sevm base memory state rep).2.2⟩

theorem systemFramePost_live (sevm : Sevm) (base : Devm) (memory : Mem) (gas : Nat)
    (state : WithdrawalRequest.State)
    (rep : RepresentsStorage (base.getStorVal sevm.currentTarget) state)
    (i : Nat) (hi : i < (WithdrawalRequest.system state).queue.length) :
    (systemFramePost sevm base memory gas).getStorVal sevm.currentTarget
      (queueSlot ((WithdrawalRequest.system state).head + i) 0) =
        callerWord (WithdrawalRequest.system state).queue[i] ∧
    (systemFramePost sevm base memory gas).getStorVal sevm.currentTarget
      (queueSlot ((WithdrawalRequest.system state).head + i) 1) =
        pubkeyWord (WithdrawalRequest.system state).queue[i] ∧
    (systemFramePost sevm base memory gas).getStorVal sevm.currentTarget
      (queueSlot ((WithdrawalRequest.system state).head + i) 2) =
        pubkeyAmountWord (WithdrawalRequest.system state).queue[i] := by
  have remaining := hi
  rw [system_queue, List.length_drop] at remaining
  change i < state.queue.length - 16 at remaining
  have notDrained : ¬ state.queue.length ≤ 16 := by omega
  have oldIndex : i + 16 < state.queue.length := by omega
  have headEq : (WithdrawalRequest.system state).head + i = state.head + (i + 16) := by
    rw [(system_live_pointers state notDrained).1, emitted_length,
      Nat.min_eq_left (by change 16 ≤ state.queue.length; omega)]
    change state.head + 16 + i = _
    omega
  have entryEq : (WithdrawalRequest.system state).queue[i] = state.queue[i + 16] := by
    simp only [system_queue, maxPerBlock, List.getElem_drop]
    simp only [Nat.add_comm 16 i]
  have preserved : ∀ offset : Nat, offset ≤ 2 →
      (systemFramePost sevm base memory gas).getStorVal sevm.currentTarget
        (queueSlot ((WithdrawalRequest.system state).head + i) offset) =
      base.getStorVal sevm.currentTarget (queueSlot (state.head + (i + 16)) offset) := by
    intro offset offsetBound
    rw [headEq]
    have bound := rep.bounds.liveSlot_lt (i + 16) oldIndex
    have keyNat : (queueSlot (state.head + (i + 16)) offset).toNat =
        queueBase (state.head + (i + 16)) + offset := by
      rw [queueSlot, B256.toNat_toB256_of_lt (by omega)]
    have noMetadata : ∀ n : Nat, n ≤ 3 → n.toB256 ≠
        queueSlot (state.head + (i + 16)) offset := by
      intro n hn eq
      have numeric := congrArg B256.toNat eq
      rw [B256.toNat_toB256_of_lt (by omega : n < 2 ^ 256), keyNat] at numeric
      unfold queueBase at numeric
      omega
    have key0 : (0 : B256) ≠ queueSlot (state.head + (i + 16)) offset :=
      noMetadata 0 (by decide)
    have key1 : (1 : B256) ≠ queueSlot (state.head + (i + 16)) offset :=
      noMetadata 1 (by decide)
    have key2 : (2 : B256) ≠ queueSlot (state.head + (i + 16)) offset :=
      noMetadata 2 (by decide)
    rw [getStorVal_eq_getStor, systemFramePost_storage,
      Stor.get_set_ne _ key1, Stor.get_set_ne _ key0,
      systemFramePointers_storage sevm base memory state rep, ite_eq_right notDrained,
      Stor.get_set_ne _ key2]
    rfl
  rw [preserved 0 (by decide), preserved 1 (by decide), preserved 2 (by decide), entryEq]
  exact rep.live (i + 16) oldIndex

theorem systemFramePost_represents (sevm : Sevm) (base : Devm) (memory : Mem) (gas : Nat)
    (state : WithdrawalRequest.State)
    (rep : RepresentsStorage (base.getStorVal sevm.currentTarget) state)
    (sumBound : effectiveExcess state + state.count < 2 ^ 256) :
    RepresentsStorage ((systemFramePost sevm base memory gas).getStorVal sevm.currentTarget)
      (WithdrawalRequest.system state) := by
  obtain ⟨excess, count, head, tail⟩ :=
    systemFramePost_metadata sevm base memory gas state rep sumBound
  exact ⟨system_coherent rep.coherent, system_storageBounds state rep.coherent rep.bounds sumBound,
    excess, count, head, tail, systemFramePost_live sevm base memory gas state rep⟩

theorem systemFramePost_output_represented (sevm : Sevm) (base : Devm) (memory : Mem)
    (gas : Nat) (state : WithdrawalRequest.State)
    (rep : RepresentsStorage (base.getStorVal sevm.currentTarget) state)
    {image : Bytes} (wf : Mem.Wf memory) (reads : Mem.Reads memory image) :
    (systemFramePost sevm base memory gas).output = systemOutput state := by
  rw [systemFramePost_output, systemCount_represented sevm base state rep]
  exact systemQueuePost_read sevm base state rep wf reads

theorem exec_system_represented {sevm : Sevm} {pre post : Devm}
    (state : WithdrawalRequest.State)
    (code : sevm.code = Blanc.withdrawalRequestCode)
    (fork : CoveredFork sevm.benvStat.fork) (stack : pre.stack = [])
    (caller : sevm.caller = systemAddress) (exec : Exec 0 sevm pre (.ok post))
    (rep : RepresentsStorage (pre.getStorVal sevm.currentTarget) state)
    (sumBound : effectiveExcess state + state.count < 2 ^ 256)
    {image : Bytes} (wf : Mem.Wf pre.memory) (reads : Mem.Reads pre.memory image) :
    RepresentsStorage (post.getStorVal sevm.currentTarget) (WithdrawalRequest.system state) ∧
      post.output = systemOutput state := by
  obtain ⟨_, gas, rfl⟩ := exec_system_frame code fork stack caller exec
  exact ⟨systemFramePost_represents sevm pre pre.memory gas state rep sumBound,
    systemFramePost_output_represented sevm pre pre.memory gas state rep wf reads⟩

theorem systemLoopFold_error (sevm : Sevm) (head : B256) (index remaining : Nat)
    (base : Devm) (memory : Mem) :
    (systemLoopFold sevm head index remaining base memory).base.error = base.error := by
  induction remaining generalizing index base memory with
  | zero => rfl
  | succ remaining ih =>
    simp only [systemLoopFold]
    rw [ih]
    simp only [systemBodyBase, systemBodyBase2, systemBodyBase1, afterSload_error]

theorem systemLoopFold_balance (sevm : Sevm) (head : B256) (index remaining : Nat)
    (base : Devm) (memory : Mem) (address : Adr) :
    (systemLoopFold sevm head index remaining base memory).base.getBal address =
      base.getBal address := by
  induction remaining generalizing index base memory with
  | zero => rfl
  | succ remaining ih =>
    simp only [systemLoopFold]
    rw [ih]
    simp only [systemBodyBase, systemBodyBase2, systemBodyBase1,
      Devm.getBal, afterSload_getAcct]

theorem systemFramePost_other_storage (sevm : Sevm) (base : Devm) (memory : Mem) (gas : Nat)
    (address : Adr) (other : sevm.currentTarget ≠ address) :
    (systemFramePost sevm base memory gas).getStor address = base.getStor address := by
  rw [systemFramePost, systemBookkeepingPost,
    (returnPost_facts _ _ _ _).2.2.1 address, St_getStor]
  simp only [systemBookkeepingBase, systemExcessStore, systemCountRead, systemExcessRead,
    afterSstore_getStor_ne _ _ _ _ _ other, afterSload_getStor]
  unfold systemFramePointers systemPointerBase
  split
  · rw [afterSstore_getStor_ne _ _ _ _ _ other, afterSstore_getStor_ne _ _ _ _ _ other,
      systemQueuePost_storage]
  · rw [afterSstore_getStor_ne _ _ _ _ _ other, systemQueuePost_storage]

theorem systemFramePost_logs (sevm : Sevm) (base : Devm) (memory : Mem) (gas : Nat) :
    (systemFramePost sevm base memory gas).logs = base.logs := by
  simp only [systemFramePost, systemBookkeepingPost, returnPost, Devm.withOutput_logs,
    Devm.memRead_logs, Devm.setMach_logs, St]
  simp only [systemBookkeepingBase, systemExcessStore, systemCountRead, systemExcessRead,
    afterSstore_logs, afterSload_logs]
  unfold systemFramePointers systemPointerBase
  split
  · rw [afterSstore_logs, afterSstore_logs, systemQueuePost_logs]
  · rw [afterSstore_logs, systemQueuePost_logs]

theorem systemFramePost_error (sevm : Sevm) (base : Devm) (memory : Mem) (gas : Nat) :
    (systemFramePost sevm base memory gas).error = base.error := by
  rw [systemFramePost, systemBookkeepingPost, (returnPost_facts _ _ _ _).2.1]
  simp only [St, Devm.setMach_error, systemBookkeepingBase, systemExcessStore,
    systemCountRead, systemExcessRead, afterSstore_error, afterSload_error]
  unfold systemFramePointers systemPointerBase
  split
  all_goals simp only [afterSstore_error]
  all_goals
    rw [systemQueuePost, systemLoopFold_error]
    simp only [systemSetupBase, afterSload_error]

theorem systemFramePost_balance (sevm : Sevm) (base : Devm) (memory : Mem) (gas : Nat)
    (address : Adr) :
    (systemFramePost sevm base memory gas).getBal address = base.getBal address := by
  simp only [systemFramePost, systemBookkeepingPost, returnPost, Devm.getBal, Devm.getAcct,
    Devm.withOutput_state, Devm.memRead_state, Devm.setMach_state, St]
  change (systemBookkeepingBase sevm (systemFramePointers sevm base memory)).getBal address = _
  simp only [systemBookkeepingBase, systemExcessStore, systemCountRead, systemExcessRead,
    afterSstore_getBal]
  simp only [Devm.getBal, afterSload_getAcct]
  change (systemFramePointers sevm base memory).getBal address = base.getBal address
  unfold systemFramePointers systemPointerBase
  split
  all_goals simp only [afterSstore_getBal]
  all_goals
    rw [systemQueuePost, systemLoopFold_balance]
    simp only [systemSetupBase, Devm.getBal, afterSload_getAcct]

end Blanc.Lift.WithdrawalRequest
