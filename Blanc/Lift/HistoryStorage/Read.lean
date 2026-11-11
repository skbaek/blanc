import Blanc.Lift.SystemExecution.HistoryStorage.SystemWalk
import Blanc.Lift.RequestFee.Plain
import Blanc.Lift.WalkKit
import Blanc.Lift.ExactWalkSolc

/-! # The exact EIP-2935 read path -/

namespace Blanc.Lift.HistoryStorage

open Jaune Blanc.Lift
open SystemExecution.HistoryStorage

def readPost (sevm : Sevm) (b : Devm) (q : B256) (G : Nat) : Devm :=
  let w := b.getStorVal sevm.currentTarget (q % 8191)
  chargedRetPost (afterSload sevm b (q % 8191)) [] (Mem.empty.write 0 w.toBytes) G 0 32

theorem read_tail_run {fs : List SFunc} {sevm : Sevm} {b : Devm} {q : B256} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork) :
    SFunc.RunExact fs sevm (St b [q] .empty (G + sloadCost sevm b (q % 8191) + 24))
      t_0036_c0 (.halted (readPost sevm b q G)) := by
  unfold t_0036_c0
  wrun! 3
  rw [show G + sloadCost sevm b (q % 8191) + 13 =
    (G + 13) + sloadCost sevm b (q % 8191) by omega]
  refine rx_sload_sel fork.shanghaiOnwards (by decide) ?_
  refine rx_push0 fork.rules_push0 (by wroom) ?_
  refine rx_mstore (c := 6) ?_ rfl ?_
  · rw [St.extCost_eq rfl]
    rfl
  wrun! 1
  refine rx_push0 fork.rules_push0 (by wroom) ?_
  unfold readPost chargedRetPost
  refine rx_return ?_ ?_
  · rw [St.extCost_eq (n := 32) (by rw [Mem.size_write_word_at]; rfl)]
    rfl
  · rfl

theorem read_arm_run {fs : List SFunc} {sevm : Sevm} {b : Devm} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (length : sevm.data.length = 32)
    (upper : (Sevm.dataWord sevm 0).toNat ≤ (sevm.benvStat.number.toB256 - 1).toNat)
    (lower : (sevm.benvStat.number.toB256 - Sevm.dataWord sevm 0).toNat ≤ 8191) :
    SFunc.RunExact fs sevm
      (St b [] .empty (G + sloadCost sevm b (Sevm.dataWord sevm 0 % 8191) + 104))
      t_001a_c0 (.halted (readPost sevm b (Sevm.dataWord sevm 0) G)) := by
  unfold t_001a_c0
  wrun! 2
  refine rx_sub' (v := 0) (by rw [length]; exact B256.sub_self _) (by wroom) ?_
  wrun! 1
  refine rx_branch_zero ?_
  unfold t_0021_c0
  refine rx_push0 fork.rules_push0 (by wroom) ?_
  wrun! 5
  refine rx_gt (v := 0) (B256.gtCheck_eq_zero_of_toNat_le upper) (by wroom) ?_
  wrun! 1
  refine rx_branch_zero ?_
  unfold t_002c_c0
  wrun! 4
  refine rx_gt (v := 0) (B256.gtCheck_eq_zero_of_toNat_le lower) (by wroom) ?_
  wrun! 1
  exact rx_branch_zero (read_tail_run fork)

theorem readPost_facts (sevm : Sevm) (b : Devm) (q : B256) (G : Nat) :
    (readPost sevm b q G).gasLeft = G ∧
    (readPost sevm b q G).output = (b.getStorVal sevm.currentTarget (q % 8191)).toBytes ∧
    (readPost sevm b q G).state = b.state := by
  refine ⟨rfl, ?_, ?_⟩
  · change ((Mem.empty.write 0 (b.getStorVal sevm.currentTarget (q % 8191)).toBytes).read 0 32).1 = _
    have h := Mem.read_write_zero Mem.empty
      (ys := (b.getStorVal sevm.currentTarget (q % 8191)).toBytes)
      (List.ne_nil_of_length_pos (by rw [B256.length_toBytes]; decide))
    rwa [B256.length_toBytes] at h
  · change (afterSload sevm b (q % 8191)).state = b.state
    exact RequestFee.afterSload_state _ _ _

theorem read_exec {sevm : Sevm} {pre : Devm}
    (code : sevm.code = historyStorageCode) (fork : CoveredFork sevm.benvStat.fork)
    (caller : sevm.caller ≠ systemAddress) (length : sevm.data.length = 32)
    (stack : pre.stack = []) (memory : pre.memory = .empty)
    (upper : (Sevm.dataWord sevm 0).toNat ≤ (sevm.benvStat.number.toB256 - 1).toNat)
    (lower : (sevm.benvStat.number.toB256 - Sevm.dataWord sevm 0).toNat ≤ 8191)
    (gas : sloadCost sevm pre (Sevm.dataWord sevm 0 % 8191) + 125 ≤ pre.gasLeft) :
    ∃ post, Nonempty (Exec 0 sevm pre (.ok post)) ∧
      post.gasLeft = pre.gasLeft - (sloadCost sevm pre (Sevm.dataWord sevm 0 % 8191) + 125) ∧
      post.output = (pre.getStorVal sevm.currentTarget (Sevm.dataWord sevm 0 % 8191)).toBytes ∧
      post.state = pre.state := by
  let G := pre.gasLeft - (sloadCost sevm pre (Sevm.dataWord sevm 0 % 8191) + 125)
  have run := read_arm_run (fs := cert.prog) (b := pre) (G := G) fork length upper lower
  have exec := RequestFee.exec_of_dispatch_user cert_check jumps_ok
    (progNoExec_of_all (by decide)) (dest := ⟨0x46, [], by decide⟩)
    (by rfl) code caller run
  have seed : St pre [] .empty
      (G + sloadCost sevm pre (Sevm.dataWord sevm 0 % 8191) + 104 + RequestSystem.dispatchGas) = pre := by
    apply pre_eq_St stack memory
    dsimp only [G, RequestSystem.dispatchGas]
    omega
  rw [seed] at exec
  exact ⟨_, exec, readPost_facts sevm pre (Sevm.dataWord sevm 0) G⟩

end Blanc.Lift.HistoryStorage
