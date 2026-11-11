import Blanc.Lift.BeaconDeposit.LogCodec
import Blanc.Lift.LogSilent
import Blanc.Lift.BeaconDeposit.Lift
import Blanc.Lift.BeaconDeposit.SafeViews
import Blanc.Lift.BeaconDeposit.SafeDispatch
import Blanc.Lift.BeaconDeposit.SafeDecoder
import Blanc.Lift.BeaconDeposit.SafeGuards
import Blanc.Lift.BeaconDeposit.SafeEvent

/-! # The original successful deposit runtime emits only well-shaped deposit events -/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-- The actual continuation immediately after the runtime's unique LOG instruction. -/
private def eventTail : SFunc :=
  match t_071c_c4 with
  | .dest (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ tail))))))))))))))))))))))) => tail
  | _ => .undefined

/-- Closed entries reachable after the event has been appended. -/
private def postEventSet : List Nat := [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

private theorem postEventSet_logSilent : LogSilentSet prog postEventSet = true := by
  decide +kernel

private theorem eventTail_logSilent : eventTail.logSilent = true ∧
    eventTail.refs.all (· ∈ postEventSet) = true := by
  decide +kernel

/-- Invert the runtime's LOG prefix without asking how its later hash/storage work behaves. -/
private theorem event_tail_run {sevm : Sevm} {b : Devm}
    {sel rt sP wP pP a : B256} {G : Nat} {M : Mem} {data : Bytes} {out : Outcome}
    (hlen : data.length = 576)
    (hM : BodyMem M 832 0x100
      [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat), (0x100, data)])
    (run : SFunc.Run prog sevm
      (St b [8, 0x340, 0x180, 0x160, 0x140, 0x120, 0x100, 0x100, 0xc0, 96, sP, 0x80, 32, wP,
        48, pP, BeaconDeposit.depositEventTopic, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8,
        sel] M G) t_071c_c4 out) :
    ∃ (stack : List B256) (gas : Nat), SFunc.Run prog sevm
      (St (b.addLog ⟨sevm.currentTarget, [BeaconDeposit.depositEventTopic], data⟩) stack M gas)
      eventTail out := by
  obtain ⟨hwf, hs, img, hr, hfp, hf⟩ := hM
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have hdata : img.sliceD 256 576 0 = data := by
    have h := hf (0x100, data) (by simp only [List.mem_cons, Prod.mk.injEq, Nat.reduceEqDiff,
      false_and, List.not_mem_nil, or_false, or_true])
    rwa [hlen] at h
  have run := run.cut
  unfold t_071c_c4 at run
  winv 3
  iterate 14
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_pop s1
  winv 2
  rw [h40, read_word hr 64 hfp, read_covered hs (by norm_num only) (by norm_num only)] at run
  winv 5
  have e256 : (256 : B256).toNat = 256 := by decide
  have e576 : ((832 : B256) - 256).toNat = 576 := by decide
  have hfst : (M.read 256 576).1 = data := by rw [hr.read, hdata]
  have hsnd : (M.read 256 576).2 = M :=
    Mem.read_snd_eq_self (by rw [hs]; exact memExtSize_of_le (by norm_num only) (by norm_num only))
  rw [e256, e576, hfst, hsnd] at run
  exact ⟨_, _, run.uncut⟩

private theorem event_logs {sevm : Sevm} {b : Devm}
    {sel rt sP wP pP a : B256} {G : Nat} {M : Mem} {data : Bytes} {out : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (hlen : data.length = 576)
    (hM : BodyMem M 832 0x100
      [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat), (0x100, data)])
    (run : SFunc.Run prog sevm
      (St b [8, 0x340, 0x180, 0x160, 0x140, 0x120, 0x100, 0x100, 0xc0, 96, sP, 0x80, 32, wP,
        48, pP, BeaconDeposit.depositEventTopic, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8,
        sel] M G) t_071c_c4 out) :
    (Outcome.devm out).logs =
      b.logs ++ [⟨sevm.currentTarget, [BeaconDeposit.depositEventTopic], data⟩] := by
  obtain ⟨stack, gas, tail⟩ := event_tail_run hlen hM run
  exact tail.logs_of_logSilent postEventSet_logSilent fork
    eventTail_logSilent.1 eventTail_logSilent.2

/-- The deposit wrapper appends one well-shaped event on its original successful run. -/
private theorem deposit_wrapper_logs {sevm : Sevm} {pre post : Devm} {sel : B256} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (hcd : sevm.data.length < 2 ^ 256)
    (run : SFunc.Run prog sevm (St pre [sel] mem0 G) t_00a4_c32 (.halted post)) :
    ∃ ev : BeaconDeposit.DepositEvent,
      post.logs = pre.logs ++ [BeaconDeposit.depositEventLog sevm.currentTarget ev] ∧
      ev.pubkey.length = 48 ∧ ev.withdrawal_credentials.length = 32 ∧
      ev.amount.length = 8 ∧ ev.signature.length = 96 ∧ ev.index.length = 8 := by
  obtain ⟨decodable, gas, returned, body, _, logs⟩ := safe_decoder hcd run
  obtain ⟨_, _, _, _, _, _, b1, m1, gas1, kept1, mem1, body1⟩ :=
    safe_guards (sel := sel) hcd fork body
  obtain ⟨b2, m2, gas2, kept2, mem2, body2⟩ := safe_event mem1 body1
  let ev := bodyEvent sevm (argPtr sevm 0) (argPtr sevm 1) (argPtr sevm 2)
    (gweiAmount sevm) (pre.getStorVal sevm.currentTarget solCountSlot)
  have lengths : ev.pubkey.length = 48 ∧ ev.withdrawal_credentials.length = 32 ∧
      ev.amount.length = 8 ∧ ev.signature.length = 96 ∧ ev.index.length = 8 := by
    simp only [ev, bodyEvent, List.length_sliceD, BeaconDeposit.le64, List.length_cons,
      List.length_nil, Nat.reduceAdd, and_self, eq_self]
  have hlen := BeaconDeposit.abiDepositEvent_length ev lengths.1 lengths.2.1
    lengths.2.2.1 lengths.2.2.2.1 lengths.2.2.2.2
  have eventLogs := event_logs fork hlen mem2 body2
  simp only [Outcome.devm] at eventLogs
  refine ⟨ev, ?_, lengths⟩
  rw [logs, eventLogs, kept2.logs, kept1.logs, afterSload_logs]
  rfl

/-- Every original successful fresh execution appends no log or exactly one well-shaped event. -/
theorem successful_logs {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256) (hstack : pre.stack = [])
    (hmem : pre.memory = Mem.empty) (executed : Exec 0 sevm pre (.ok post)) :
    post.logs = pre.logs ∨ ∃ ev : BeaconDeposit.DepositEvent,
      post.logs = pre.logs ++ [BeaconDeposit.depositEventLog sevm.currentTarget ev] ∧
      ev.pubkey.length = 48 ∧ ev.withdrawal_credentials.length = 32 ∧
      ev.amount.length = 8 ∧ ev.signature.length = 96 ∧ ev.index.length = 8 := by
  obtain ⟨f, found, run⟩ := lift_sound cert_check hcode fork executed
  have root : prog[0]? = some t_0000_c0 := rfl
  rw [root] at found
  cases found
  rw [St.self hstack hmem] at run
  obtain ⟨k, gas, wrapper, member, isDeposit, found, run⟩ := safe_dispatch run
  by_cases selected : k = 32
  · subst k
    have here : wrapper = t_00a4_c32 := by
      have at32 : prog[32]? = some t_00a4_c32 := rfl
      rw [at32] at found
      exact (Option.some.inj found).symm
    subst wrapper
    exact Or.inr (deposit_wrapper_logs fork hcd run)
  · left
    have inViews : k ∈ viewSet := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      simp only [viewSet, List.mem_cons, List.not_mem_nil, or_false]
      omega
    have checked := (List.all_eq_true.mp viewSet_quiet) k inViews
    rw [found] at checked
    simp only [Bool.and_eq_true] at checked
    exact (run.world_of_quietH viewSet_quiet fork.rules_stateGas_none checked.1 checked.2).2

/-- Every newly appended log is the exact accepted event image, with a 192-byte request record. -/
theorem successful_log_shape {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256) (hstack : pre.stack = [])
    (hmem : pre.memory = Mem.empty) (executed : Exec 0 sevm pre (.ok post)) :
    ∀ log ∈ post.logs.drop pre.logs.length, ∃ ev : BeaconDeposit.DepositEvent,
      log = BeaconDeposit.depositEventLog sevm.currentTarget ev ∧
      extractDepositData log.data =
        .ok (ev.pubkey ++ ev.withdrawal_credentials ++ ev.amount ++ ev.signature ++ ev.index) ∧
      (ev.pubkey ++ ev.withdrawal_credentials ++ ev.amount ++ ev.signature ++ ev.index).length =
        192 := by
  intro log member
  rcases successful_logs hcode fork hcd hstack hmem executed with empty | ⟨ev, logs, lengths⟩
  · rw [empty, List.drop_length] at member
    exact False.elim (List.not_mem_nil member)
  · rw [logs, List.drop_length_append' rfl, List.mem_singleton] at member
    subst log
    refine ⟨ev, rfl, ?_, ?_⟩
    · exact extractDepositData_abiDepositEvent ev lengths.1 lengths.2.1 lengths.2.2.1
        lengths.2.2.2.1 lengths.2.2.2.2
    · exact depositRecord_length ev lengths.1 lengths.2.1 lengths.2.2.1
        lengths.2.2.2.1 lengths.2.2.2.2

end Blanc.Lift.BeaconDeposit
