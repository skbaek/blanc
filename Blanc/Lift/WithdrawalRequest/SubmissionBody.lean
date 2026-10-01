import Blanc.Lift.WithdrawalRequest.SubmissionState

/-! Actual sequential submission walk, without queue-key disjointness. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

def submissionWordsTree : SFunc :=
  match t_008f_c0 with
  | (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ f)))))) => f
  | _ => .undefined

def submissionMemoryTree : SFunc :=
  match submissionWordsTree with
  | (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ f)))))))))))))))))))))) => f
  | _ => .undefined

private theorem submissionCount_split : t_008f_c0 =
    .next (.push [1] (by decide)) (.next (.reg .sload)
    (.next (.push [1] (by decide)) (.next (.reg .add)
    (.next (.push [1] (by decide)) (.next (.reg .sstore) submissionWordsTree))))) := rfl

private theorem submissionCount_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {out : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm (St b [] M G) t_008f_c0 out) :
    sevm.isStatic = false ∧ ∃ G', SFunc.Run prog sevm
      (St (submissionCountStore sevm b) [] M G') submissionWordsTree out := by
  have run := run.cut
  rw [submissionCount_split] at run
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := submissionCount sevm b) rfl (ri_sload fork h)
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_add h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨_, h, run⟩ := ric_next run
  have dynamic := ri_sstore_nonstatic fork h
  obtain ⟨_, rfl⟩ := ri_sstore fork h
  exact ⟨dynamic, _, run.uncut⟩

private theorem submissionCount_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {out : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G)
    (tail : SFunc.RunExact prog sevm
      (St (submissionCountStore sevm b) [] M G) submissionWordsTree out) :
    SFunc.RunExact prog sevm (St b [] M (G + submissionCountGas sevm b)) t_008f_c0 out := by
  have gasEq : G + submissionCountGas sevm b =
      G + sstoreCost sevm (submissionCountRead sevm b) 1 (1 + submissionCount sevm b)
      + 3 + 3 + 3 + sloadCost sevm b 1 + 3 := by
    simp only [submissionCountGas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [← Nat.add_assoc 3 3, ← Nat.add_assoc 6 3, ← Nat.add_assoc 9 3]
  rw [gasEq, submissionCount_split]
  apply rx_push rfl (by change 0 < 1024; decide)
  apply rx_sload_sel fork (by change 0 < 1024; decide)
  apply rx_push rfl (by change 1 < 1024; decide)
  apply rx_add' (v := 1 + submissionCount sevm b) rfl (by change 0 < 1024; decide)
  apply rx_push rfl (by change 1 < 1024; decide)
  apply rx_sstore fork (Nat.lt_of_lt_of_le slack (Nat.le_add_right _ _)) dynamic
  exact tail

private theorem submissionWords_split : submissionWordsTree =
  (.next (.push [3] (by decide)) (.next (.reg .sload) (.next (.reg (.dup 0)) (.next (.push [3] (by decide)) (.next (.reg .mul) (.next (.push [4] (by decide)) (.next (.reg .add) (.next (.reg .caller) (.next (.reg (.dup 1)) (.next (.reg .sstore) (.next (.push [1] (by decide)) (.next (.reg .add) (.next (.push [] (by decide)) (.next (.reg .calldataload) (.next (.reg (.dup 1)) (.next (.reg .sstore) (.next (.push [1] (by decide)) (.next (.reg .add) (.next (.push [32] (by decide)) (.next (.reg .calldataload) (.next (.reg (.swap 0)) (.next (.reg .sstore) submissionMemoryTree)))))))))))))))))))))) := rfl

private theorem submissionWords_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {out : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm (St (submissionCountStore sevm b) [] M G)
      submissionWordsTree out) :
    ∃ G', SFunc.Run prog sevm
      (St (submissionWordsStore sevm b) [submissionTail sevm b] M G') submissionMemoryTree out := by
  have run := run.cut
  rw [submissionWords_split] at run
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := submissionTail sevm b) rfl (ri_sload fork h)
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_mul h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := submissionKey sevm b) rfl (ri_add h)
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_caller h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sstore fork h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_add h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_calldataload h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sstore fork h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_add h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_calldataload h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap rfl h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sstore fork h
  exact ⟨_, run.uncut⟩

private theorem submissionWords_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {out : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G)
    (tail : SFunc.RunExact prog sevm
      (St (submissionWordsStore sevm b) [submissionTail sevm b] M G) submissionMemoryTree out) :
    SFunc.RunExact prog sevm (St (submissionCountStore sevm b) [] M
      (G + submissionWordsGas sevm b)) submissionWordsTree out := by
  let R := sloadCost sevm (submissionCountStore sevm b) 3
  let C0 := sstoreCost sevm (submissionTailRead sevm b) (submissionKey sevm b) sevm.caller.toB256
  let C1 := sstoreCost sevm (submissionCallerStore sevm b) (1 + submissionKey sevm b)
    (Sevm.dataWord sevm 0)
  let C2 := sstoreCost sevm (submissionWord1Store sevm b) (1 + (1 + submissionKey sevm b))
    (Sevm.dataWord sevm 32)
  have gasEq : G + submissionWordsGas sevm b =
      G + C2 + 3 + 3 + 3 + 3 + 3 + C1 + 3 + 3 + 2 + 3 + 3
      + C0 + 3 + 2 + 3 + 3 + 5 + 3 + 3 + R + 3 := by
    calc
      _ = G + (54 + (R + (C0 + (C1 + C2)))) := by
        simp only [submissionWordsGas, Nat.add_assoc]
        rfl
      _ = G + ((3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 3 + 3 + 2 + 3 + 3 + 5 + 3 + 3 + 3)
        + (R + (C0 + (C1 + C2)))) := rfl
      _ = _ := by simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [gasEq, submissionWords_split]
  apply rx_push rfl (by change 0 < 1024; decide)
  apply rx_sload_sel fork (by change 0 < 1024; decide)
  apply rx_dup1 (by change 1 < 1024; decide)
  apply rx_push rfl (by change 2 < 1024; decide)
  apply rx_mul (v := 3 * submissionTail sevm b) rfl (by change 1 < 1024; decide)
  apply rx_push rfl (by change 2 < 1024; decide)
  apply rx_add' (v := submissionKey sevm b) rfl (by change 1 < 1024; decide)
  apply rx_caller (by change 2 < 1024; decide)
  apply rx_dup2 (by change 3 < 1024; decide)
  apply rx_sstore fork (Nat.lt_of_lt_of_le slack (by simp only [Nat.add_assoc]; exact Nat.le_add_right _ _)) dynamic
  apply rx_push rfl (by change 2 < 1024; decide)
  apply rx_add' (v := 1 + submissionKey sevm b) rfl (by change 1 < 1024; decide)
  apply rx_push0 (by change 2 < 1024; decide)
  apply rx_calldataload (by change 2 < 1024; decide)
  apply rx_dup2 (by change 3 < 1024; decide)
  apply rx_sstore fork (Nat.lt_of_lt_of_le slack (by simp only [Nat.add_assoc]; exact Nat.le_add_right _ _)) dynamic
  apply rx_push rfl (by change 2 < 1024; decide)
  apply rx_add' (v := 1 + (1 + submissionKey sevm b)) rfl (by change 1 < 1024; decide)
  apply rx_push rfl (by change 2 < 1024; decide)
  apply rx_calldataload (by change 2 < 1024; decide)
  apply rx_swap1
  apply rx_sstore fork (Nat.lt_of_lt_of_le slack (Nat.le_add_right _ _)) dynamic
  exact tail

def submissionLogTree : SFunc :=
  match submissionMemoryTree with
  | (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ f))))))))))) => f
  | _ => .undefined

private theorem submissionMemory_split : submissionMemoryTree =
  (.next (.reg .caller) (.next (.push [96] (by decide)) (.next (.reg .shl) (.next (.push [] (by decide)) (.next (.reg .mstore) (.next (.push [56] (by decide)) (.next (.push [] (by decide)) (.next (.push [20] (by decide)) (.next (.reg .calldatacopy) (.next (.push [76] (by decide)) (.next (.push [] (by decide)) submissionLogTree))))))))))) := rfl

private theorem submissionMemory_inv {sevm : Sevm} {base : Devm} {M : Mem} {G : Nat}
    {tail : B256} {out : Outcome}
    (run : SFunc.Run prog sevm (St base [tail] M G) submissionMemoryTree out) :
    ∃ G', SFunc.Run prog sevm (St base [0, 76, tail] (submissionCopyMemory sevm M) G')
      submissionLogTree out := by
  have run := run.cut
  rw [submissionMemory_split] at run
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_caller h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := sevm.caller.toB256 <<< 96) rfl (ri_shl h)
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_mstore h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_calldatacopy h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  exact ⟨_, run.uncut⟩

private theorem submissionLog_split : submissionLogTree =
    .next (.reg (.log 0)) (.next (.push [1] (by decide)) (.next (.reg .add)
      (.next (.push [3] (by decide)) (.next (.reg .sstore) (.last .stop))))) := rfl

private theorem submissionLog_inv {sevm : Sevm} {base : Devm} {M : Mem} {G : Nat}
    {tail : B256} {out : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm
      (St base [0, 76, tail] (submissionCopyMemory sevm M) G) submissionLogTree out) :
    ∃ G', out = .halted (St (afterSstore sevm (base.addLog (submissionLog sevm M))
      3 (1 + tail)) [] (submissionMemory sevm M) G') := by
  have run := run.cut
  rw [submissionLog_split] at run
  obtain ⟨d, h, run⟩ := ric_next run
  rcases of_run_reg h with ⟨pc, raw⟩
  simp only [Rinst.run, Rinst.runCore] at raw
  rw [show (St base [0, 76, tail] (submissionCopyMemory sevm M) G).popToNat =
    .ok (0, St base [76, tail] (submissionCopyMemory sevm M) G) from rfl] at raw
  simp only [Except.bind_ok] at raw
  rw [show (St base [76, tail] (submissionCopyMemory sevm M) G).popToNat =
    .ok (76, St base [tail] (submissionCopyMemory sevm M) G) from rfl] at raw
  simp only [Except.bind_ok] at raw
  rw [show (St base [tail] (submissionCopyMemory sevm M) G).popN ((0 : Fin 5) : Nat) =
    .ok ([], St base [tail] (submissionCopyMemory sevm M) G) from rfl] at raw
  simp only [Except.bind_ok] at raw
  rcases Except.bind_eq_ok raw with ⟨s1, hcharge, rest⟩
  rcases Except.bind_eq_ok rest with ⟨_, -, last⟩
  cases last
  have eqGas := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas hcharge)
  have eqSt : s1 = St base [tail] (submissionCopyMemory sevm M) s1.gasLeft := eqGas
  rw [eqSt] at run
  simp only [St.memRead_fst, St.memRead_snd] at run
  change SFunc.RunCut _ _ _ (St (base.addLog (submissionLog sevm M)) [tail]
    (submissionMemory sevm M) s1.gasLeft) _ _ at run
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_add h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sstore fork h
  cases run with
  | last terminal =>
    change Except.ok _ = Except.ok _ at terminal
    cases terminal
    exact ⟨_, rfl⟩

private theorem submissionLog_exact {sevm : Sevm} {base : Devm} {M : Mem} {G : Nat}
    {tail : B256} (fork : CoveredFork sevm.benvStat.fork)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G) :
    SFunc.RunExact prog sevm
      (St base [0, 76, tail] (submissionCopyMemory sevm M)
        (G + sstoreCost sevm (base.addLog (submissionLog sevm M)) 3 (1 + tail)
          + 9 + submissionLogGas sevm M)) submissionLogTree
      (.halted (St (afterSstore sevm (base.addLog (submissionLog sevm M)) 3 (1 + tail))
        [] (submissionMemory sevm M) G)) := by
  have logged : Ninst.RunCompiled sevm
      (St base [0, 76, tail] (submissionCopyMemory sevm M)
        (G + sstoreCost sevm (base.addLog (submissionLog sevm M)) 3 (1 + tail)
          + 9 + submissionLogGas sevm M)) (.reg (.log 0))
      (St (base.addLog (submissionLog sevm M)) [tail] (submissionMemory sevm M)
        (G + sstoreCost sevm (base.addLog (submissionLog sevm M)) 3 (1 + tail) + 9)) :=
    Ninst.runCompiled_log_of (n := 0) (i := 0) (sz := 76) (topics := []) (s := [tail])
      rfl rfl dynamic (Devm.extCost_add_of_size rfl rfl) rfl rfl rfl
  rw [submissionLog_split]
  refine .next logged ?_
  apply rx_push rfl (by change 1 < 1024; decide)
  apply rx_add' (v := 1 + tail) rfl (by change 0 < 1024; decide)
  apply rx_push rfl (by change 1 < 1024; decide)
  apply rx_sstore fork (Nat.lt_of_lt_of_le slack (Nat.le_add_right _ _)) dynamic
  exact .last rfl

private theorem submissionMemory_exact {sevm : Sevm} {base : Devm} {M : Mem} {G : Nat}
    {tail : B256} {out : Outcome}
    (next : SFunc.RunExact prog sevm
      (St base [0, 76, tail] (submissionCopyMemory sevm M) G) submissionLogTree out) :
    SFunc.RunExact prog sevm (St base [tail] M
      (G + 23 + submissionMstoreGas M + submissionCopyGas sevm M)) submissionMemoryTree out := by
  have gasEq : G + 23 + submissionMstoreGas M + submissionCopyGas sevm M =
      G + 2 + 3 + submissionCopyGas sevm M + 3 + 2 + 3 + submissionMstoreGas M + 2 + 3 + 3 + 2 := by
    calc
      _ = G + (23 + (submissionMstoreGas M + submissionCopyGas sevm M)) := by
        simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = G + ((2 + 3 + 3 + 2 + 3 + 2 + 3 + 3 + 2) +
        (submissionMstoreGas M + submissionCopyGas sevm M)) := rfl
      _ = _ := by simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [gasEq, submissionMemory_split]
  apply rx_caller (by change 1 < 1024; decide)
  apply rx_push rfl (by change 2 < 1024; decide)
  apply rx_shl (v := sevm.caller.toB256 <<< 96) rfl (by change 1 < 1024; decide)
  apply rx_push0 (by change 2 < 1024; decide)
  apply rx_mstore (Devm.extCost_add_of_size rfl rfl) rfl
  apply rx_push rfl (by change 1 < 1024; decide)
  apply rx_push0 (by change 2 < 1024; decide)
  apply rx_push rfl (by change 3 < 1024; decide)
  apply rx_calldatacopy (Devm.extCost_add_of_size rfl rfl) rfl
  apply rx_push rfl (by change 1 < 1024; decide)
  apply rx_push0 (by change 2 < 1024; decide)
  exact next

/-- Successful body execution has the entire sequential raw state and actual STOP outcome. -/
theorem submissionBody_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {out : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm (St b [] M G) t_008f_c0 out) :
    sevm.isStatic = false ∧ ∃ G', out = .halted (submissionPost sevm b M G') := by
  obtain ⟨dynamic, _, run⟩ := submissionCount_inv fork run
  obtain ⟨_, run⟩ := submissionWords_inv fork run
  obtain ⟨_, run⟩ := submissionMemory_inv run
  exact ⟨dynamic, submissionLog_inv fork run⟩

/-- Sufficient residual slack derives every sentry; consumed gas is the exact selected cost. -/
theorem submissionBody_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G) :
    SFunc.RunExact prog sevm (St b [] M (G + submissionBodyGas sevm b M)) t_008f_c0
      (.halted (submissionPost sevm b M G)) := by
  have logged := submissionLog_exact (base := submissionWordsStore sevm b)
    (M := M) (tail := submissionTail sevm b) fork dynamic slack
  have suffix := submissionMemory_exact logged
  have suffixGasEq : G + submissionSuffixGas sevm b M =
      G + sstoreCost sevm (submissionLogged sevm b M) 3 (1 + submissionTail sevm b)
      + 9 + submissionLogGas sevm M + 23 + submissionMstoreGas M + submissionCopyGas sevm M := by
    calc
      _ = G + (32 + (submissionMstoreGas M + (submissionCopyGas sevm M +
        (submissionLogGas sevm M + sstoreCost sevm (submissionLogged sevm b M) 3 (1 + submissionTail sevm b))))) := by
        simp only [submissionSuffixGas, Nat.add_assoc]
      _ = G + ((9 + 23) + (submissionMstoreGas M + (submissionCopyGas sevm M +
        (submissionLogGas sevm M + sstoreCost sevm (submissionLogged sevm b M) 3 (1 + submissionTail sevm b))))) := rfl
      _ = _ := by simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  change SFunc.RunExact prog sevm _ submissionMemoryTree
    (.halted (submissionPost sevm b M G)) at suffix
  unfold submissionLogged at suffixGasEq
  rw [← suffixGasEq] at suffix
  have words := submissionWords_exact fork dynamic
    (Nat.lt_of_lt_of_le slack (Nat.le_add_right _ _)) suffix
  have counted := submissionCount_exact fork dynamic
    (Nat.lt_of_lt_of_le slack (by simp only [Nat.add_assoc]; exact Nat.le_add_right _ _)) words
  have gasEq : G + submissionBodyGas sevm b M =
      G + submissionSuffixGas sevm b M + submissionWordsGas sevm b + submissionCountGas sevm b := by
    simp only [submissionBodyGas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [gasEq]
  exact counted

def userSubmissionGas (sevm : Sevm) (b : Devm) (M : Mem) (iterations : Nat) : Nat :=
  submissionBodyGas sevm (afterSload sevm b 0) M + 64 +
    feeLoopGas iterations + userSetupGas sevm b + dispatchGas

/-- A literal 56-byte canonical successful submission has the actual sequential effects. -/
theorem exec_submission {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = Blanc.withdrawalRequestCode) (fork : CoveredFork sevm.benvStat.fork)
    (hstack : pre.stack = []) (user : sevm.caller ≠ systemAddress)
    (hlen : sevm.data.length = 56) (exec : Exec 0 sevm pre (.ok post)) :
    sevm.isStatic = false ∧ pre.getStorVal sevm.currentTarget 0 ≠ B256.max ∧
    ∃ iterations finalOutput,
      WordFakeExponential.Run (pre.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations finalOutput ∧
      (finalOutput / (17 : B256)).toNat ≤ sevm.value.toNat ∧
      ∃ G, post = submissionPost sevm (afterSload sevm pre 0) pre.memory G := by
  have hword : sevm.data.length.toB256 = 56 := by rw [hlen]; rfl
  obtain ⟨active, iterations, finalOutput, wordRun, accepted⟩ :=
    exec_user_fee_dispatch hcode fork hstack user exec
  rcases accepted with ⟨_, paid, _, run⟩ | ⟨empty, _, _⟩
  · obtain ⟨dynamic, G, postEq⟩ := submissionBody_inv fork run
    exact ⟨dynamic, active, iterations, finalOutput, wordRun, paid,
      G, Outcome.halted.inj postEq⟩
  · rw [hword] at empty
    exact False.elim ((by decide : (56 : B256) ≠ 0) empty)

/-- Construct canonical STOP with every store sentry, exact selected gas and literal payload length. -/
theorem exec_submission_exact {sevm : Sevm} {b : Devm} {M : Mem} {G iterations : Nat}
    {finalOutput : B256}
    (hcode : sevm.code = Blanc.withdrawalRequestCode) (fork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) (hlen : sevm.data.length = 56)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G)
    (active : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (b.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations finalOutput)
    (paid : (finalOutput / (17 : B256)).toNat ≤ sevm.value.toNat) :
    Nonempty (Exec 0 sevm (St b [] M (G + userSubmissionGas sevm b M iterations))
      (.ok (submissionPost sevm (afterSload sevm b 0) M G))) := by
  have hword : sevm.data.length.toB256 = 56 := by rw [hlen]; rfl
  have branchGas : userFeeDispatchGas sevm = 64 := by
    rw [userFeeDispatchGas_eq, ite_eq_left hword]
  have body := submissionBody_exact (b := afterSload sevm b 0) (M := M) fork dynamic slack
  have acceptedWalk := user_fee_prefix_exact fork active wordRun (.inl ⟨hword, paid, body⟩)
  rw [branchGas] at acceptedWalk
  have gasEq : G + userSubmissionGas sevm b M iterations =
      (G + submissionBodyGas sevm (afterSload sevm b 0) M + 64 +
        feeLoopGas iterations + userSetupGas sevm b) + dispatchGas := by
    simp only [userSubmissionGas, Nat.add_assoc]
  rw [gasEq]
  exact exec_of_dispatch hcode fork (by
    simpa only [dispatchTail, ite_eq_right user] using acceptedWalk)

end Blanc.Lift.WithdrawalRequest
