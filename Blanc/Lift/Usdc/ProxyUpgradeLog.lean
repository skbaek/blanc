import Blanc.ExecutionModelAccounting
import Blanc.Lift.Usdc.ProxySstoreH
import Blanc.Lift.HistCursorCuts
import Blanc.Lift.CommittedLogs
import Blanc.Lift.PtrWordMemory

/-! A retained implementation write in a successful proxy frame emits `Upgraded`.
The proof follows the checked internal continuation of the same original frame.
The exact-data theorem links the emitted payload to the implementation word stored
by that same instruction; the older address/topic APIs remain projections. -/

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

/-- The two masks applied by the checked event encoder. -/
private def upgradeLogWord (x : B256) : B256 :=
  let mask : B256 := 0xffffffffffffffffffffffffffffffffffffffff
  mask &&& (mask &&& x)

/-- Actual memory after staging the event word, before reloading the free pointer. -/
private def upgradeLogMemory (M : Mem) (x : B256) : Mem :=
  (M.read 64 32).2.write (M.read 64 32).1.toB256.toNat (upgradeLogWord x).toBytes

private theorem upgradeLogLine_exact {sevm : Sevm} {b : Devm}
    {x : B256} {S : List B256} {M : Mem} {G : Nat} {d : Devm}
    (run : Line.Run sevm (St b (x :: S) M G) upgradeLogLine d) :
    let p := (M.read 64 32).1.toB256
    let written := upgradeLogMemory M x
    let i := (written.read 64 32).1.toB256
    ∃ G', d = St b (i :: (32 + p - i) :: upgradedTopic :: x :: S)
      (written.read 64 32).2 G' := by
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
  exact ⟨_, rfl⟩

/-- With the actual free-pointer word kept disjoint from the event store,
    the checked encoder stages exactly one masked address word. -/
private theorem upgradeLogLine_payload {sevm : Sevm} {b : Devm}
    {x p : B256} {S : List B256} {M : Mem} {G : Nat} {d : Devm}
    (pointer : PtrWord p M) (far : 96 ≤ p.toNat)
    (run : Line.Run sevm (St b (x :: S) M G) upgradeLogLine d) :
    ∃ M' G', d = St b (p :: 32 :: upgradedTopic :: x :: S) M' G' ∧
      (M'.read p.toNat 32).1 = (upgradeLogWord x).toBytes := by
  have kept := (pointer.extend 64 32).write p.toNat (upgradeLogWord x).toBytes far
  have reloaded : ((upgradeLogMemory M x).read 64 32).1.toB256 = p := by
    simpa only [upgradeLogMemory, pointer.2] using kept.2
  have size : (32 : B256) + p - p = 32 := by
    apply B256.toNat_inj
    rw [B256.toNat_sub, B256.toNat_add]
    have bound := B256.toNat_lt p
    change (2 ^ 256 + (32 + p.toNat) % 2 ^ 256 - p.toNat) % 2 ^ 256 = 32
    omega
  obtain ⟨G', state⟩ := upgradeLogLine_exact run
  rw [pointer.2, reloaded, size] at state
  refine ⟨_, G', state, ?_⟩
  rw [memRead_extend_fst]
  unfold upgradeLogMemory
  rw [pointer.2, Mem.read_write_word_of_wf (pointer.extend 64 32).1]

private theorem upgradeLogLine_inverse {sevm : Sevm} {b : Devm}
    {x : B256} {S : List B256} {M : Mem} {G : Nat} {d : Devm}
    (run : Line.Run sevm (St b (x :: S) M G) upgradeLogLine d) :
    ∃ i sz M' G', d = St b (i :: sz :: upgradedTopic :: x :: S) M' G' := by
  obtain ⟨G', state⟩ := upgradeLogLine_exact run
  exact ⟨_, _, _, G', state⟩

/-- A successful same-frame suffix beginning at the classified implementation
write emits the literal `Upgraded` topic and retains it through its endpoint. -/
private theorem upgradeStoreConf_emitsUpgraded_encoded {N : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code cert N κ) {x : B256}
    (geometry : UpgradeStoreConf x (κ.conf N.devm)) {post : Devm}
    (success : N.exn = .ok post) (committed : Execution.commits N.exn = true)
    (hsg : N.sevm.benvStat.rules.stateGas = none)
    (bal : N.sevm.benvStat.rules.bal = none) :
    ∃ y entry, entry ∈ post.logs ∧
      entry.address = N.sevm.currentTarget ∧ entry.topics = [upgradedTopic] ∧
      (∃ a b r S, N.devm.stack = implSlot :: x :: a :: b :: r :: y :: S) ∧
      (∀ p, PtrWord p N.devm.memory → 96 ≤ p.toNat →
        entry.data = (upgradeLogWord y).toBytes) := by
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
  refine ⟨y, ⟨N.sevm.currentTarget, [upgradedTopic], (M.read i.toNat sz.toNat).1⟩,
    ?_, rfl, rfl, ⟨a, b, r, S, stack⟩, ?_⟩
  · rw [logs]
    apply List.mem_append_left
    rw [appended]
    change _ ∈ (afterSstoreH N.sevm N.devm implSlot x).logs ++ [_]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · intro p pointer far
    obtain ⟨M', G'', payloadState, payload⟩ := upgradeLogLine_payload pointer far line
    have states := logState.symm.trans payloadState
    have stackEq := congrArg Devm.stack states
    simp only [St.stack, List.cons.injEq] at stackEq
    have memories : M = M' := congrArg Devm.memory states
    change (M.read i.toNat sz.toNat).1 = _
    rw [stackEq.1, stackEq.2.1, memories]
    exact payload

/-- Compatibility projection retaining the address/topic-only API. -/
theorem upgradeStoreConf_emitsUpgraded {N : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code cert N κ) {x : B256}
    (geometry : UpgradeStoreConf x (κ.conf N.devm)) {post : Devm}
    (success : N.exn = .ok post) (committed : Execution.commits N.exn = true)
    (hsg : N.sevm.benvStat.rules.stateGas = none)
    (bal : N.sevm.benvStat.rules.bal = none) :
    ∃ entry ∈ post.logs,
      entry.address = N.sevm.currentTarget ∧ entry.topics = [upgradedTopic] := by
  obtain ⟨_, entry, present, address, topics, _, _⟩ :=
    upgradeStoreConf_emitsUpgraded_encoded ok geometry success committed hsg bal
  exact ⟨entry, present, address, topics⟩

/-- The exact implementation-write geometry links the retained event's payload
    to the word stored by this instruction. -/
theorem upgradeStoreConf_emitsUpgraded_data {N : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code cert N κ) {x p : B256}
    (geometry : UpgradeStoreDataConf x N.devm.memory (κ.conf N.devm))
    (pointer : PtrWord p N.devm.memory) (far : 96 ≤ p.toNat)
    (masked : (0xffffffffffffffffffffffffffffffffffffffff : B256) &&& x = x)
    {post : Devm} (success : N.exn = .ok post)
    (committed : Execution.commits N.exn = true)
    (hsg : N.sevm.benvStat.rules.stateGas = none)
    (bal : N.sevm.benvStat.rules.bal = none) :
    ∃ entry ∈ post.logs, entry.address = N.sevm.currentTarget ∧
      entry.topics = [upgradedTopic] ∧ entry.data = x.toBytes := by
  obtain ⟨y, entry, present, address, topics, stack, payload⟩ :=
    upgradeStoreConf_emitsUpgraded_encoded ok geometry.forget success committed hsg bal
  obtain ⟨a, b, r, S, stack⟩ := stack
  obtain ⟨a', b', r', S', K, exactStack, _, _, _⟩ := geometry
  have same := stack.symm.trans exactStack
  simp only [List.cons.injEq] at same
  have aligned : y = x := same.2.2.2.2.2.1
  refine ⟨entry, present, address, topics, ?_⟩
  rw [payload p pointer far, aligned]
  simp only [upgradeLogWord, masked]

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

/-- An actual pc-0 proxy prefix with well-formed entry memory emits the
    precise implementation word written by the selected `SSTORE`. -/
theorem proxy_implSstore_emitsUpgraded_data {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out) (committed : Execution.commits out = true)
    (codeEq : sevm.code = Proxy.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none) (wf : Mem.Wf pre.memory) {N : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N)
    (hat : Ninst.At N.sevm.code N.pc (.reg .sstore)) {v : B256} {rest : List B256}
    (slot : N.devm.stack = implSlot :: v :: rest) :
    ∃ entry ∈ (Execution.committedPost out committed).logs,
      entry.address = sevm.currentTarget ∧ entry.topics = [upgradedTopic] ∧
      entry.data = v.toBytes := by
  obtain ⟨κ, ok, _, exactData⟩ :=
    proxy_sstoreCursorH_with_data run codeEq hsg bal chain hat
  have geometry := (exactData (v :: rest) slot).2
  obtain ⟨a, b, r, S, K, stack, tree, cont, memory⟩ := geometry
  have value : upgradeArg sevm = v := (List.cons.inj (List.cons.inj (stack.symm.trans slot)).2).1
  have ownGeometry : UpgradeStoreDataConf (upgradeArg sevm) N.devm.memory (κ.conf N.devm) :=
    ⟨a, b, r, S, K, stack, tree, cont, rfl⟩
  have pointer : PtrWord 128 N.devm.memory := by
    rw [memory]
    refine ⟨wf.write _ _, ?_⟩
    rw [Mem.read_write_word_of_wf wf, B256.toB256_toBytes]
  have masked : (0xffffffffffffffffffffffffffffffffffffffff : B256) &&& upgradeArg sevm =
      upgradeArg sevm := by
    change (0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
      (0xffffffffffffffffffffffffffffffffffffffff &&& Sevm.dataWord sevm 4) =
      0xffffffffffffffffffffffffffffffffffffffff &&& Sevm.dataWord sevm 4
    rw [B256.and_comm 0xffffffffffffffffffffffffffffffffffffffff
      (0xffffffffffffffffffffffffffffffffffffffff &&& Sevm.dataWord sevm 4),
      B256.and_comm 0xffffffffffffffffffffffffffffffffffffffff (Sevm.dataWord sevm 4),
      B256.and_idem_right]
  have env : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  have outcome : N.exn = out := Blanc.Exec.Deriv.ParentPrefix.exn_eq chain
  have retained : Execution.commits N.exn = true := by rw [outcome]; exact committed
  cases out with
  | error err => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    obtain ⟨entry, present, address, topics, payload⟩ :=
      upgradeStoreConf_emitsUpgraded_data ok ownGeometry pointer (by decide) masked
        outcome retained (env ▸ hsg) (env ▸ bal)
    exact ⟨entry, present, by rw [← env]; exact address, topics, value ▸ payload⟩

end Blanc.Lift.Usdc.Proxy
