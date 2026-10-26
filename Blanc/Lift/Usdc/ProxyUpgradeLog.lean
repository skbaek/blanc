import Blanc.ExecutionModelAccounting
import Blanc.Lift.Usdc.ProxySstoreH
import Blanc.Lift.HistCursorCuts
import Blanc.Lift.CommittedLogs

/-! A retained implementation write in a successful proxy frame emits `Upgraded`.
The proof follows the checked internal continuation of the same original frame.
It specifies the address and topic; the data payload remains existential. -/

namespace Blanc.Lift.Usdc.Proxy

open Jaune Blanc Blanc.Lift

/-- `keccak256("Upgraded(address)")`, as embedded in the checked proxy runtime. -/
def upgradedTopic : B256 := Bytes.toB256 [0xbc, 0x7c, 0xd7, 0x5a, 0x20, 0xee, 0x27, 0xfd, 0x9a, 0xde, 0xba, 0xb3, 0x20, 0x41, 0xf7, 0x55, 0x21, 0x4d, 0xbc, 0x6b, 0xff, 0xa9, 0x0c, 0xc0, 0x22, 0x5b, 0x39, 0xda, 0x2e, 0x5c, 0x2d, 0x3b]

private def upgradeLogLine : List Ninst :=
  [.push [0xbc, 0x7c, 0xd7, 0x5a, 0x20, 0xee, 0x27, 0xfd, 0x9a, 0xde, 0xba, 0xb3, 0x20, 0x41, 0xf7, 0x55, 0x21, 0x4d, 0xbc, 0x6b, 0xff, 0xa9, 0x0c, 0xc0, 0x22, 0x5b, 0x39, 0xda, 0x2e, 0x5c, 0x2d, 0x3b] (by decide),
    .reg (.dup 1),
    .push [0x40] (by decide),
    .reg .mload,
    .reg (.dup 0),
    .reg (.dup 2),
    .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
    .reg .and,
    .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
    .reg .and,
    .reg (.dup 1),
    .reg .mstore,
    .push [0x20] (by decide),
    .reg .add,
    .reg (.swap 1),
    .reg .pop,
    .reg .pop,
    .push [0x40] (by decide),
    .reg .mload,
    .reg (.dup 0),
    .reg (.swap 1),
    .reg .sub,
    .reg (.swap 0)]

private theorem upgradeLogLine_inverse {sevm : Sevm} {b : Devm}
    {x : B256} {S : List B256} {M : Mem} {G : Nat} {d : Devm}
    (run : Line.Run sevm (St b (x :: S) M G) upgradeLogLine d) :
    ∃ i sz M' G', d = St b (i :: sz :: upgradedTopic :: x :: S) M' G' := by
  unfold upgradeLogLine at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sub step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl step
  cases run
  exact ⟨_, _, _, _, rfl⟩

/-- A successful same-frame suffix beginning at the classified implementation
write emits the literal `Upgraded` topic and retains it through its endpoint. -/
theorem upgradeStoreConf_emitsUpgraded {N : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code cert N κ) {x : B256}
    (geometry : UpgradeStoreConf x (κ.conf N.devm)) {post : Devm}
    (success : N.exn = .ok post) (committed : Execution.commits N.exn = true)
    (hsg : N.sevm.benvStat.rules.stateGas = none)
    (bal : N.sevm.benvStat.rules.bal = none) :
    ∃ entry ∈ post.logs,
      entry.address = N.sevm.currentTarget ∧ entry.topics = [upgradedTopic] := by
  obtain ⟨a, b, r, y, S, K, stack, tree, cont⟩ := geometry
  let cut : CursorStateAt code cert N
      (.next (.reg .sstore) (.next (.reg .pop) (.next (.reg .pop) .ret)))
      N.devm (implSlot :: x :: a :: b :: r :: y :: S) N.devm.memory
      (t_06e2_c9 :: K) :=
    ⟨N, κ, .refl N, rfl, rfl, ok, tree,
      ⟨N.devm.gasLeft, by rw [← stack]; exact (St.self' N.devm).symm⟩, cont⟩
  obtain ⟨stored⟩ := cut.lineH cert_check success hsg
    [.reg .sstore, .reg .pop, .reg .pop] rfl
    (by intro n hn z; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl <;> intro h <;> cases h)
    (by
      intro G d run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_sstoreH hsg bal step
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_pop step
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_pop step
      cases run
      exact ⟨_, rfl⟩)
  obtain ⟨returned⟩ := stored.retH cert_check success hsg
  obtain ⟨ready⟩ := returned.destH cert_check success hsg
  obtain ⟨L, cursorL, path, _, sameSevm, sameExn, placed, logTree, line, _, _⟩ :=
    cursor_nexts_line_cont_free_forwardH cert_check ready.placed upgradeLogLine
      (.next (.reg (.log 1)) (.next (.reg .pop) .ret))
      ready.tree (ready.exn_eq.trans success) (by rw [ready.sevm_eq]; exact hsg)
  obtain ⟨G, readyState⟩ := ready.state
  rw [ready.sevm_eq, readyState] at line
  obtain ⟨i, sz, M, G', logState⟩ := upgradeLogLine_inverse line
  have env : L.sevm = N.sevm := sameSevm.trans ready.sevm_eq
  have outcome : L.exn = .ok post := sameExn.trans (ready.exn_eq.trans success)
  obtain ⟨A, _, edge, _, primitive, _, _, _⟩ :=
    cursor_next_forwardH cert_check placed logTree outcome (env ▸ hsg)
  have logRun := primitive.toRun
  rw [env, logState] at logRun
  obtain ⟨_, afterLog⟩ := ri_log1 logRun
  have afterEnv : A.sevm = N.sevm := (Cursor.parentStep_sevm edge).trans env
  have afterOutcome : A.exn = .ok post :=
    (show A.exn = L.exn by cases edge <;> rfl).trans outcome
  have committedA : Execution.commits A.exn = true := by
    rw [afterOutcome, ← success]; exact committed
  have finalPost : Execution.committedPost A.exn committedA = post := by
    generalize hout : A.exn = out at committedA ⊢
    have equal := hout.symm.trans afterOutcome
    cases equal
    rfl
  have logs := Exec.committed_logs_noStateGas A.exc committedA (afterEnv ▸ hsg) rfl rfl
  rw [finalPost] at logs
  have appended := congrArg Devm.logs afterLog
  refine ⟨⟨N.sevm.currentTarget, [upgradedTopic], (M.read i.toNat sz.toNat).1⟩, ?_, rfl, rfl⟩
  rw [logs]
  apply List.mem_append_left
  rw [appended]
  change _ ∈ (afterSstoreH N.sevm N.devm implSlot x).logs ++ [_]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Every implementation-slot `SSTORE` reached by a committing pc-0 frame
of the checked proxy runtime entails a retained `Upgraded` log in that frame.
The prefix belongs to this same frame; no claim is made about reverted writes. -/
theorem proxy_implSstore_emitsUpgraded {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out) (committed : Execution.commits out = true)
    (codeEq : sevm.code = Proxy.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none) {N : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N)
    (hat : Ninst.At N.sevm.code N.pc (.reg .sstore))
    (slot : ∃ v rest, N.devm.stack = implSlot :: v :: rest) :
    ∃ entry ∈ (Execution.committedPost out committed).logs,
      entry.address = sevm.currentTarget ∧ entry.topics = [upgradedTopic] := by
  obtain ⟨κ, ok, classified⟩ := proxy_sstoreCursorH run codeEq hsg bal chain hat
  rcases classified with ⟨rest, admin⟩ | ⟨rest, stack, selector, caller, geometry⟩
  · obtain ⟨v, tail, impl⟩ := slot
    have unequal : adminSlot ≠ implSlot := by decide
    exact (unequal (List.cons.inj (admin.symm.trans impl)).1).elim
  · have env : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
    have outcome : N.exn = out := Blanc.Exec.Deriv.ParentPrefix.exn_eq chain
    have retained : Execution.commits N.exn = true := by rw [outcome]; exact committed
    cases out with
    | error err => simp only [Execution.commits, Bool.false_eq_true] at committed
    | ok post =>
      obtain ⟨entry, present, address, topics⟩ :=
        upgradeStoreConf_emitsUpgraded ok geometry outcome retained
          (env ▸ hsg) (env ▸ bal)
      exact ⟨entry, present, by rw [← env]; exact address, topics⟩

end Blanc.Lift.Usdc.Proxy
