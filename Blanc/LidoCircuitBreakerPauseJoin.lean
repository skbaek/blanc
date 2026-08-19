import Blanc.LidoCircuitBreakerPauseWorldRun
import Blanc.LidoCircuitBreakerPauseOkRoute
import Blanc.LidoCircuitBreakerPauseSuffix

/-!
# The pause join: expiry writes meet attainable rows 18 and 19

The walk side (`Blanc/LidoCircuitBreakerPauseWorldRun.lean`) runs the two
pause witness worlds end to end; the route side
(`Blanc/LidoCircuitBreakerPauseOkRoute.lean`) routes a successful pause walk
to either expiry `SSTORE` under twenty-two premises.  This module discharges
those premises at the two worlds and joins the halves:

* the **responder-crossing preservation** lemmas, which settle the routes'
  `hcall`/`hstat` continuations against an *arbitrary* derivation's crossing
  of the two external calls — at any gas, without pinning the child's budget;
* the **route-final discharges** at both worlds, entered from the full
  `Devm.BurnBy` fact the frame tail hands the route;
* the two `decide +kernel` **index pins** binding the routed paths to
  inventory indices 18 and 19;
* the **J1/J2 witnesses** `attainable_pauseLastTargetExpiry_pauseExpiry` and
  `attainable_pauseRetainedTargetExpiry_pauseExpiry`;
* the **J3 join theorems**, which tie the same walks' suffix writes — through
  `pauseSuccess_expiryWrite_dichotomy`, load-bearing by construction — to the
  attained rows.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune
open Jaune.Ninst Blanc.Ninst

/-! ## Zero-value seam projections

The crossings leave the parent's state as a zero-value `subBal`/`addBal`
chain (success leg) or restore it outright (error leg); either way every
account's storage and code are untouched.  The Kit proves the storage half
privately for its own two-hop seam; the join needs the one-hop forms, and the
code forms, so they are re-minted here. -/

private theorem joinState_setBal_acct (st : State) (adr : Adr) (val : B256)
    (a : Adr) : ((st.setBal adr val).get a).stor = (st.get a).stor ∧
      ((st.setBal adr val).get a).code = (st.get a).code := by
  unfold State.setBal
  by_cases h : adr = a
  · subst h
    rw [State.get_set_self]
    exact ⟨rfl, rfl⟩
  · rw [State.get_set_ne st h _]
    exact ⟨rfl, rfl⟩

private theorem joinState_addBal_acct (st : State) (adr : Adr) (val : B256)
    (a : Adr) : ((st.addBal adr val).get a).stor = (st.get a).stor ∧
      ((st.addBal adr val).get a).code = (st.get a).code := by
  unfold State.addBal
  exact joinState_setBal_acct st adr _ a

private theorem joinState_subBal_acct {st st' : State} {adr : Adr}
    {val : B256} (h : st.subBal adr val = some st') (a : Adr) :
    (st'.get a).stor = (st.get a).stor ∧
      (st'.get a).code = (st.get a).code := by
  unfold State.subBal at h
  split at h
  · contradiction
  · injection h with h2
    subst h2
    exact joinState_setBal_acct st adr _ a

/-! ## Window survival across the resume's memory shape

Both resume legs leave the parent's memory as
`(preC.memory.extends spans).write oi bytes` with `bytes.length ≤ os`; a
window that misses the written span survives, and an `extends` never moves
data at all. -/

theorem MemWordAt.acrossMemExtends {a b : Devm} {offset : Nat} {w : B256}
    {pairs : List (Nat × Nat)}
    (h : b.memory = a.memory.extends pairs)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  obtain ⟨hwf, img, hreads, hslice⟩ := window
  refine ⟨?_, img, ?_, hslice⟩
  · rw [h]
    exact hwf.extends pairs
  · rw [h]
    exact hreads.extends pairs

/-- The resume's whole memory shape at once: an `extends` never moves data,
and a write that stops short of the window leaves it alone. -/
theorem MemWordAt.acrossExtendsWrite {a b : Devm} {offset : Nat} {w : B256}
    {pairs : List (Nat × Nat)} {ys : Bytes} {n : Nat}
    (h : b.memory = (a.memory.extends pairs).write n ys)
    (miss : offset + 32 ≤ n ∨ n + ys.length ≤ offset)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  obtain ⟨hwf, img, hreads, hslice⟩ := window
  have hwf' : Mem.Wf (a.memory.extends pairs) := hwf.extends pairs
  have hreads' : Mem.Reads (a.memory.extends pairs) img := hreads.extends pairs
  refine ⟨by rw [h]; exact hwf'.write n ys, Bytes.writeAt img n ys,
    by rw [h]; exact Mem.Reads.write hwf' hreads' n ys, ?_⟩
  rcases miss with late | early
  · rw [Bytes.sliceD_writeAt_before img ys offset 32 n late]
    exact hslice
  · rw [Bytes.sliceD_writeAt_after img ys offset 32 n early]
    exact hslice

theorem MemWordAt.writeMissBytes {a b : Devm} {offset : Nat} {w : B256}
    {ys : Bytes} {n : Nat}
    (h : b.memory = a.memory.write n ys)
    (miss : offset + 32 ≤ n ∨ n + ys.length ≤ offset)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  obtain ⟨hwf, img, hreads, hslice⟩ := window
  refine ⟨by rw [h]; exact hwf.write n ys, Bytes.writeAt img n ys,
    by rw [h]; exact Mem.Reads.write hwf hreads n ys, ?_⟩
  rcases miss with late | early
  · rw [Bytes.sliceD_writeAt_before img ys offset 32 n late]
    exact hslice
  · rw [Bytes.sliceD_writeAt_after img ys offset 32 n early]
    exact hslice

/-! ## Out-of-gas step outcomes

The crossing inversion below must account for every gas level a derivation
can carry, so the failing arms of the step functions are named here: the
forward library only ever evaluates them on success. -/

/-- `chargeGas`, evaluated forward on the failing arm. -/
private lemma chargeGas_eq_error {cost : Nat} {devm : Devm}
    (h : devm.gasLeft < cost) :
    chargeGas cost devm = .error ⟨.halt (.outOfGas .none), devm⟩ := by
  rw [chargeGas_def]
  have hs : safeSub devm.gasLeft cost = none := by
    unfold safeSub
    rw [if_neg (by omega)]
  rw [hs]

/-- A `JUMPDEST` without the gas for its own charge halts out of gas. -/
private lemma step_jumpdest_fail {pc : Nat} {sevm : Sevm} {devm : Devm}
    (h_at : Jinst.At sevm.code pc .jumpdest)
    (h_gas : devm.gasLeft < gJumpdest) :
    Evm.step ⟨pc, sevm, devm⟩ =
      .halt (.error ⟨.halt (.outOfGas .none), devm⟩) := by
  rw [Evm.step_jump h_at]
  have hrun : Jinst.run ⟨pc, sevm, devm⟩ .jumpdest =
      .error ⟨.halt (.outOfGas .none), devm⟩ := by
    show Jinst.runCore pc devm sevm .jumpdest = _
    unfold Jinst.runCore
    rw [chargeGas_eq_error h_gas]
    rfl
  rw [hrun]
  rfl

/-- A `JUMPDEST` with the gas for its charge continues to the next byte. -/
private lemma step_jumpdest_cont {pc : Nat} {sevm : Sevm} {devm : Devm}
    (h_at : Jinst.At sevm.code pc .jumpdest)
    (h_gas : gJumpdest ≤ devm.gasLeft) :
    Evm.step ⟨pc, sevm, devm⟩ = .cont (pc + 1)
      (devm.setMach ⟨devm.stack, devm.memory, devm.gasLeft - gJumpdest⟩) := by
  rw [Evm.step_jump h_at]
  have hrun : Jinst.run ⟨pc, sevm, devm⟩ .jumpdest = .ok ⟨pc + 1,
      devm.setMach ⟨devm.stack, devm.memory, devm.gasLeft - gJumpdest⟩⟩ := by
    show Jinst.runCore pc devm sevm .jumpdest = _
    unfold Jinst.runCore
    rw [chargeGas_eq_ok h_gas]
    rfl
  rw [hrun]
  rfl

/-- A `PUSH` — of either cost class — without the gas for its charge halts
out of gas. -/
private lemma step_push_fail {pc : Nat} {sevm : Sevm} {devm : Devm}
    {xs : Bytes} {le : xs.length ≤ 32}
    (h_at : Ninst.At sevm.code pc (.push xs le))
    (h_gas : devm.gasLeft < if xs = [] then gBase else gVerylow) :
    Evm.step ⟨pc, sevm, devm⟩ =
      .halt (.error ⟨.halt (.outOfGas .none), devm⟩) := by
  rw [Evm.step_next h_at, Ninst.step_push, chargeGas_eq_error h_gas]
  rfl

/-- A `PUSH0` with the gas for its charge continues with a zero pushed. -/
private lemma step_push0_cont {pc : Nat} {sevm : Sevm} {devm : Devm}
    {le : ([] : Bytes).length ≤ 32}
    (h_at : Ninst.At sevm.code pc (.push [] le))
    (h_gas : gBase ≤ devm.gasLeft) (h_room : devm.stack.length < 1024) :
    Evm.step ⟨pc, sevm, devm⟩ = .cont (pc + 1)
      (devm.setMach ⟨0 :: devm.stack, devm.memory,
        devm.gasLeft - gBase⟩) := by
  rw [Evm.step_next h_at, Ninst.step_push]
  rw [show (if ([] : Bytes) = [] then gBase else gVerylow) = gBase from rfl]
  rw [chargeGas_eq_ok h_gas]
  simp only [bind, Except.bind]
  rw [Devm.push_eq_ok (devm := devm.setMach
    ⟨devm.stack, devm.memory, devm.gasLeft - gBase⟩) h_room]
  rfl

/-- An `MSTORE` at offset zero over empty memory, without the gas for its
`gVerylow + 3` word-extension charge, halts out of gas. -/
private lemma step_mstore_fail {pc : Nat} {sevm : Sevm} {devm : Devm}
    {v : B256} {s : List B256}
    (h_at : Ninst.At sevm.code pc (.reg .mstore))
    (h_stk : devm.stack = 0 :: v :: s) (h_mem : devm.memory = Mem.empty)
    (h_gas : devm.gasLeft < gVerylow + 3) :
    ∃ d : Devm, Evm.step ⟨pc, sevm, devm⟩ =
      .halt (.error ⟨.halt (.outOfGas .none), d⟩) := by
  rw [Evm.step_next h_at, Ninst.step_reg]
  show ∃ d, Step.ofExecution _ (Rinst.runCore pc devm sevm .mstore) = _
  unfold Rinst.runCore
  rw [Devm.popToNat_eq_ok (devm := devm) h_stk]
  simp only [bind, Except.bind]
  rw [Devm.pop_eq_ok (devm := devm.setMach ⟨v :: s, devm.memory, devm.gasLeft⟩)
    rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  have hext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨(0 : B256).toNat, 32⟩] = 3 := by
    rw [show ((0 : B256).toNat) = 0 from rfl]
    show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost [⟨0, 32⟩] = 3
    have hm : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).memory =
        Mem.empty := h_mem
    exact hm ▸ Devm.extCost_empty_word
  rw [hext, chargeGas_eq_error (by
    show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).gasLeft < _
    rw [Devm.gasLeft_setMach]
    omega)]
  exact ⟨_, rfl⟩

/-- An `MSTORE` at offset zero over empty memory, with the gas for its
charge: the projections the following steps read. -/
private lemma step_mstore_cont {pc : Nat} {sevm : Sevm} {devm : Devm}
    {v : B256} {s : List B256}
    (h_at : Ninst.At sevm.code pc (.reg .mstore))
    (h_stk : devm.stack = 0 :: v :: s) (h_mem : devm.memory = Mem.empty)
    (h_gas : gVerylow + 3 ≤ devm.gasLeft) :
    ∃ d : Devm, Evm.step ⟨pc, sevm, devm⟩ = .cont (pc + 1) d ∧
      d.stack = s ∧ d.gasLeft = devm.gasLeft - (gVerylow + 3) := by
  rw [Evm.step_next h_at, Ninst.step_reg]
  have hstep : Step.ofExecution (pc + 1)
      (Rinst.runCore pc devm sevm .mstore) = .cont (pc + 1)
        ((devm.setMach
          ⟨s, devm.memory, devm.gasLeft - (gVerylow + 3)⟩).memWrite
            (0 : B256).toNat v.toBytes) := by
    unfold Rinst.runCore
    rw [Devm.popToNat_eq_ok (devm := devm) h_stk]
    simp only [bind, Except.bind]
    rw [Devm.pop_eq_ok
      (devm := devm.setMach ⟨v :: s, devm.memory, devm.gasLeft⟩) rfl]
    simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
    have hext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
        [⟨(0 : B256).toNat, 32⟩] = 3 := by
      rw [show ((0 : B256).toNat) = 0 from rfl]
      show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost [⟨0, 32⟩] = 3
      have hm : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).memory =
          Mem.empty := h_mem
      exact hm ▸ Devm.extCost_empty_word
    rw [hext, chargeGas_eq_ok (by
      show gVerylow + 3 ≤
        (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).gasLeft
      rw [Devm.gasLeft_setMach]
      omega)]
    rfl
  exact ⟨_, hstep, rfl, rfl⟩

set_option maxRecDepth 8192 in
/-- The responder cannot settle on a budget below its exact charge: a message
installing `calleeCode` with gas under `17` executes to a raw `.error` — it
halts out of gas at whichever of its six charged instructions the budget dies
on.  This is the fact that closes the arbitrary-gas leg of the crossing
inversion: `callee_exec` pins every budget of at least `17`, and this lemma
refutes a clean settle on every budget below. -/
private theorem callee_exec_low_gas {m : Msg}
    (hcode : m.code = calleeCode) (hgas : m.gas < 17) :
    ∃ (e : EvmError) (d : Devm), exec (initEvm m) = .error ⟨e, d⟩ := by
  have hc : (initSevm m).code = calleeCode := hcode
  have hbytes : calleeCode.toList = calleeBytes := by
    simp [calleeCode, ByteArray.toList_eq_toList_data]
  have at0 : Jinst.At (initSevm m).code 0 .jumpdest := by
    rw [hc]
    exact Jinst.at_of_slice (xs := []) ⟨1, by rw [hbytes]; decide⟩
  have at1 : Ninst.At (initSevm m).code 1 (.push [1] (by decide)) := by
    rw [hc]
    exact Ninst.at_of_slice ⟨2, by rw [hbytes]; decide⟩
  have at3 : Ninst.At (initSevm m).code 3 (.push [] (by decide)) := by
    rw [hc]
    exact Ninst.at_of_slice ⟨1, by rw [hbytes]; decide⟩
  have at4 : Ninst.At (initSevm m).code 4 (.reg .mstore) := by
    rw [hc]
    exact Ninst.at_of_slice ⟨1, by rw [hbytes]; decide⟩
  have at5 : Ninst.At (initSevm m).code 5 (.push [32] (by decide)) := by
    rw [hc]
    exact Ninst.at_of_slice ⟨2, by rw [hbytes]; decide⟩
  have at7 : Ninst.At (initSevm m).code 7 (.push [] (by decide)) := by
    rw [hc]
    exact Ninst.at_of_slice ⟨1, by rw [hbytes]; decide⟩
  have hinit : initEvm m = ⟨0, initSevm m, initDevm m⟩ := rfl
  rw [hinit]
  rcases Nat.lt_or_ge m.gas 1 with h1 | h1
  · refine ⟨_, _, (exec_iff_exec_eq _ _ _ _).mp
      ⟨Exec.halt (step_jumpdest_fail (devm := initDevm m) at0 ?_)⟩⟩
    show m.gas < gJumpdest
    show m.gas < 1
    omega
  have s0 : Evm.step ⟨0, initSevm m, initDevm m⟩ = .cont 1
      ((initDevm m).setMach ⟨[], Mem.empty, m.gas - 1⟩) :=
    step_jumpdest_cont (devm := initDevm m) at0 (show (1 : Nat) ≤ m.gas from h1)
  rcases Nat.lt_or_ge m.gas 4 with h2 | h2
  · refine ⟨_, _, (exec_iff_exec_eq _ _ _ _).mp
      ⟨Exec.cont s0 (Exec.halt (step_push_fail
        (devm := (initDevm m).setMach ⟨[], Mem.empty, m.gas - 1⟩) at1 ?_))⟩⟩
    rw [if_neg (by decide)]
    show m.gas - 1 < 3
    omega
  have s1 : Evm.step ⟨1, initSevm m,
      (initDevm m).setMach ⟨[], Mem.empty, m.gas - 1⟩⟩ = .cont 3
      ((initDevm m).setMach
        ⟨[Bytes.toB256 [1]], Mem.empty, m.gas - 1 - 3⟩) :=
    Evm.push_cont (by decide) at1 (show (3 : Nat) ≤ m.gas - 1 by omega)
      (show (0 : Nat) < 1024 by decide)
  rcases Nat.lt_or_ge m.gas 6 with h3 | h3
  · refine ⟨_, _, (exec_iff_exec_eq _ _ _ _).mp
      ⟨Exec.cont s0 (Exec.cont s1 (Exec.halt (step_push_fail
        (devm := (initDevm m).setMach
          ⟨[Bytes.toB256 [1]], Mem.empty, m.gas - 1 - 3⟩) at3 ?_)))⟩⟩
    rw [if_pos rfl]
    show m.gas - 1 - 3 < 2
    omega
  have s2 : Evm.step ⟨3, initSevm m, (initDevm m).setMach
      ⟨[Bytes.toB256 [1]], Mem.empty, m.gas - 1 - 3⟩⟩ = .cont 4
      ((initDevm m).setMach
        ⟨0 :: Bytes.toB256 [1] :: [], Mem.empty, m.gas - 1 - 3 - 2⟩) :=
    step_push0_cont (le := by decide) at3
      (show (2 : Nat) ≤ m.gas - 1 - 3 by omega)
      (show (1 : Nat) < 1024 by decide)
  rcases Nat.lt_or_ge m.gas 12 with h4 | h4
  · obtain ⟨d, hfail⟩ := step_mstore_fail
      (devm := (initDevm m).setMach
        ⟨0 :: Bytes.toB256 [1] :: [], Mem.empty, m.gas - 1 - 3 - 2⟩)
      at4 rfl rfl (show m.gas - 1 - 3 - 2 < 3 + 3 by omega)
    exact ⟨_, _, (exec_iff_exec_eq _ _ _ _).mp
      ⟨Exec.cont s0 (Exec.cont s1 (Exec.cont s2 (Exec.halt hfail)))⟩⟩
  obtain ⟨d4, s3, hstk4, hg4'⟩ := step_mstore_cont
    (devm := (initDevm m).setMach
      ⟨0 :: Bytes.toB256 [1] :: [], Mem.empty, m.gas - 1 - 3 - 2⟩)
    at4 rfl rfl (show 3 + 3 ≤ m.gas - 1 - 3 - 2 by omega)
  have hg4 : d4.gasLeft = m.gas - 12 := by
    rw [hg4']
    show m.gas - 1 - 3 - 2 - (3 + 3) = m.gas - 12
    omega
  rcases Nat.lt_or_ge m.gas 15 with h5 | h5
  · refine ⟨_, _, (exec_iff_exec_eq _ _ _ _).mp
      ⟨Exec.cont s0 (Exec.cont s1 (Exec.cont s2 (Exec.cont
        (by exact s3) (Exec.halt (step_push_fail (devm := d4) at5 ?_)))))⟩⟩
    rw [if_neg (by decide), hg4]
    show m.gas - 12 < 3
    omega
  have s4 : Evm.step ⟨5, initSevm m, d4⟩ = .cont 7
      (d4.setMach
        ⟨Bytes.toB256 [32] :: d4.stack, d4.memory, d4.gasLeft - 3⟩) :=
    Evm.push_cont (by decide) at5 (show (3 : Nat) ≤ d4.gasLeft by omega)
      (by rw [hstk4]; decide)
  refine ⟨_, _, (exec_iff_exec_eq _ _ _ _).mp
    ⟨Exec.cont s0 (Exec.cont s1 (Exec.cont s2 (Exec.cont (by exact s3)
      (Exec.cont s4 (Exec.halt (step_push_fail
        (devm := d4.setMach ⟨Bytes.toB256 [32] :: d4.stack, d4.memory,
          d4.gasLeft - 3⟩) at7 ?_))))))⟩⟩
  rw [if_pos rfl]
  show d4.gasLeft - 3 < 2
  omega

/-! ## The settle, read backwards

The crossings hand the join an *equation* — the resume of the settle of the
child's execution is `.ok postC` — and the join reads the settle's anatomy
off it.  Three facts cover every leg: a fatal settle contradicts the
equation, a settled-with-error child carries the rolled-back entry state, and
a clean child is the raw execution itself. -/

/-- A settle that lands `.ok` with the error flag set rolled the state back:
the child's world is the message's own entry state. -/
private lemma settle_err_state {msg : Msg} {raw : Execution} {child : Devm}
    (hsettle : (Frame.ofCall msg).settle raw = .ok child)
    (hce : child.error.isSome = true) :
    child.state = msg.benv.state := by
  rcases hhe : executeCode.handleError raw with e | evm
  · rw [show (Frame.ofCall msg).settle raw
        = processMessage.settle msg (executeCode.handleError raw) from rfl,
      hhe] at hsettle
    cases hsettle
  · rw [show (Frame.ofCall msg).settle raw
        = processMessage.settle msg (executeCode.handleError raw) from rfl,
      hhe] at hsettle
    unfold processMessage.settle at hsettle
    simp only [bind, Except.bind] at hsettle
    by_cases he : evm.error.isSome
    · rw [if_pos he] at hsettle
      cases hsettle
      rfl
    · rw [if_neg he] at hsettle
      cases hsettle
      exact absurd hce he

/-- A settle that lands `.ok` with the error flag clear did not intervene:
the raw execution already was that clean state. -/
private lemma settle_ok_clean {msg : Msg} {raw : Execution} {child : Devm}
    (hsettle : (Frame.ofCall msg).settle raw = .ok child)
    (hce : child.error.isSome = false) :
    raw = .ok child := by
  have hsettle' : processMessage.settle msg (executeCode.handleError raw)
      = .ok child := hsettle
  rcases raw with ⟨e, d⟩ | out
  · exfalso
    rcases e with reason | _ | reason | reason
    · unfold executeCode.handleError processMessage.settle at hsettle'
      simp only [bind, Except.bind] at hsettle'
      rw [if_pos (by rfl)] at hsettle'
      cases hsettle'
      exact Bool.noConfusion (show (true : Bool) = false from hce)
    · unfold executeCode.handleError processMessage.settle at hsettle'
      simp only [bind, Except.bind] at hsettle'
      rw [if_pos (by rfl)] at hsettle'
      cases hsettle'
      exact Bool.noConfusion (show (true : Bool) = false from hce)
    · unfold executeCode.handleError processMessage.settle at hsettle'
      simp only [bind, Except.bind] at hsettle'
      cases hsettle'
    · unfold executeCode.handleError processMessage.settle at hsettle'
      simp only [bind, Except.bind] at hsettle'
      cases hsettle'
  · unfold executeCode.handleError processMessage.settle at hsettle'
    simp only [bind, Except.bind] at hsettle'
    by_cases he : out.error.isSome
    · exfalso
      rw [if_pos he] at hsettle'
      cases hsettle'
      have hnone : out.error.isSome = false := hce
      rw [he] at hnone
      cases hnone
    · rw [if_neg he] at hsettle'
      cases hsettle'
      rfl

/-- A resume against a full parent stack cannot land `.ok`: both flag pushes
overflow. -/
private lemma resume_call_overflow {parent child : Devm} {oi os : Nat}
    (h_room : ¬ parent.stack.length < 1024) :
    ∃ e : EvmError × Devm,
      Resume.run (.call parent oi os) (.ok child) = .error e := by
  show (∃ e, (do
    let c ← liftToExecution parent (.ok child)
    let actualOutput := c.output.take os
    if c.error.isSome then
      let evm2 ← (incorporateChildOnError parent c c.output).push 0
      Except.ok (evm2.memWrite oi actualOutput)
    else
      let evm2 ← (incorporateChildOnSuccess parent c c.output).push 1
      Except.ok (evm2.memWrite oi actualOutput)) = .error e)
  show (∃ e, (if child.error.isSome then
      (incorporateChildOnError parent child child.output).push 0 >>= fun e2 =>
        Except.ok (e2.memWrite oi (child.output.take os))
    else
      (incorporateChildOnSuccess parent child child.output).push 1 >>=
        fun e2 =>
        Except.ok (e2.memWrite oi (child.output.take os))) = .error e)
  by_cases hce : child.error.isSome
  · rw [if_pos hce]
    have hpush : Devm.push 0 (incorporateChildOnError parent child
        child.output) = .error ⟨.halt (.stackOverflow .none),
          incorporateChildOnError parent child child.output⟩ := by
      rw [Devm.push_def]
      simp only [Except.assert, bind, Except.bind]
      rw [if_neg (by show ¬ parent.stack.length < 1024; exact h_room)]
    exact ⟨_, by rw [hpush]; rfl⟩
  · rw [if_neg hce]
    have hpush : Devm.push 1 (incorporateChildOnSuccess parent child
        child.output) = .error ⟨.halt (.stackOverflow .none),
          incorporateChildOnSuccess parent child child.output⟩ := by
      rw [Devm.push_def]
      simp only [Except.assert, bind, Except.bind]
      rw [if_neg (by show ¬ parent.stack.length < 1024; exact h_room)]
    exact ⟨_, by rw [hpush]; rfl⟩

/-- The `.call` arm at `value = 0` on a frame that cannot pay the call's own
charge: `chargeGas` fails and the step is an out-of-gas halt.  The failing
sibling of `Xinst.step_call_zero_value`. -/
private lemma step_call_zero_value_outOfGas {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: 0 :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : d1.gasLeft < mcc + ext) :
    Xinst.step sevm devm .call =
      .done (.error ⟨.halt (.outOfGas .none), d1⟩) := by
  subst h_ext; subst h_acc
  show XStep.ofExcept (do
    let ⟨gas, d⟩ ← devm.pop
    let ⟨callee, d⟩ ← d.popToAdr
    let ⟨value, d⟩ ← d.pop
    let ⟨inputIndex, d⟩ ← d.popToNat
    let ⟨inputSize, d⟩ ← d.popToNat
    let ⟨outputIndex, d⟩ ← d.popToNat
    let ⟨outputSize, d⟩ ← d.popToNat
    let extendCost :=
      d.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    let preAccessCost := accessCost callee d.accessedAddresses
    let d := addAccessedAddress d callee
    let ⟨disablePrecompiles, _, code, delegatedAccessGasCost, d⟩ :=
      accessDelegation d callee
    let accessCost := preAccessCost + delegatedAccessGasCost
    let createCost :=
      if (¬ (d.getAcct callee).Empty) ∨ value = 0 then 0 else gNewAccount
    let transferCost := if value = 0 then 0 else gasCallValue
    let ⟨msgCallCost, msgCallStipend⟩ :=
      calculateMsgCallGas value.toNat gas.toNat d.gasLeft extendCost
        (accessCost + createCost + transferCost)
    let d ← chargeGas (msgCallCost + extendCost) d
    Except.assert (!sevm.isStatic ∨ value = 0)
      ⟨.halt (.writeInStaticContext .none), d⟩
    let d := d.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    let senderBal := (d.getAcct sevm.currentTarget).bal
    if senderBal < value then
      let d ← d.push 0
      return .done
        (.ok ((d.withReturnData []).withGasLeft (d.gasLeft + msgCallStipend)))
    else
      return genericCall.step
        sevm d msgCallStipend value sevm.currentTarget callee callee
        true false inputIndex inputSize outputIndex outputSize
        code disablePrecompiles) = _
  rw [Devm.pop_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.popToAdr_eq_ok
    (devm := devm.setMach ⟨cw :: 0 :: iiw :: isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Devm.pop_eq_ok
    (devm := devm.setMach ⟨0 :: iiw :: isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨iiw :: isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨oiw :: osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  simp only [if_pos (Or.inr trivial), if_pos trivial, Nat.add_zero,
    show ((0 : B256).toNat) = 0 from rfl]
  simp only [h_del, h_split]
  rw [chargeGas_eq_error (devm := d1) h_gas]
  rfl

/-- The `.statcall` arm on a frame that cannot pay the call's own charge. -/
private lemma step_statcall_outOfGas {sevm : Sevm} {devm : Devm}
    {gw tw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: tw :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        tw.toAdr) tw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost tw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : d1.gasLeft < mcc + ext) :
    Xinst.step sevm devm .statcall =
      .done (.error ⟨.halt (.outOfGas .none), d1⟩) := by
  subst h_ext; subst h_acc
  show XStep.ofExcept (do
    let ⟨gas, d⟩ ← devm.pop
    let ⟨target, d⟩ ← d.popToAdr
    let ⟨inputIndex, d⟩ ← d.popToNat
    let ⟨inputSize, d⟩ ← d.popToNat
    let ⟨outputIndex, d⟩ ← d.popToNat
    let ⟨outputSize, d⟩ ← d.popToNat
    let extendCost :=
      d.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    let preAccessCost := accessCost target d.accessedAddresses
    let d := addAccessedAddress d target
    let ⟨disablePrecompiles, _, code, delegatedAccessGasCost, d⟩ :=
      accessDelegation d target
    let accessCost := preAccessCost + delegatedAccessGasCost
    let ⟨msgCallCost, msgCallStipend⟩ :=
      calculateMsgCallGas 0 gas.toNat d.gasLeft extendCost accessCost
    let d ← chargeGas (msgCallCost + extendCost) d
    let d :=
      d.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    return genericCall.step
      sevm d msgCallStipend 0 sevm.currentTarget target target true true
      inputIndex inputSize outputIndex outputSize code
      disablePrecompiles) = _
  rw [Devm.pop_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.popToAdr_eq_ok
    (devm := devm.setMach ⟨tw :: iiw :: isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨iiw :: isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨oiw :: osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  simp only [h_del, h_split]
  rw [chargeGas_eq_error (devm := d1) h_gas]
  rfl

/-! ## The crossing tail, shared by `CALL` and `STATICCALL`

Once a crossing's spawn is exposed, everything left depends only on the
spawned message — and the two spawn shapes build the same `callMsg` up to the
static flag.  The tail consumes the frame relation and the resume equation an
arbitrary derivation carries and returns the three effects the route finals
need, **without pinning the child's gas**: a clean settle is pinned by
`callee_exec` when the forwarded budget covers the responder's charge of `17`
and refuted by `callee_exec_low_gas` when it does not, and every other leg
restores the parent's state outright. -/

private lemma responder_crossing_tail {sevm : Sevm} {p : Devm} {mcs : Nat}
    {callee : Adr} {data : Bytes} {dp isStat : Bool} {oi os : Nat}
    {postC : Devm} {xl : Xlot}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h_nonprecompile : sevm.benvStat.rules.isPrecomp callee = false)
    (hfill : Xlot.Filled xl)
    (hframe : RunFrame (Frame.ofCall (callMsg sevm p mcs 0 sevm.currentTarget
      callee callee true isStat data calleeCode dp)) xl r)
    (hres : (.ok postC : Execution) = Resume.run (.call p oi os) r) :
    (∃ ys : Bytes, ys.length ≤ os ∧
      postC.memory = p.memory.write oi ys) ∧
    (∀ (a : Adr) (key : B256),
      Devm.getStorVal postC a key = Devm.getStorVal p a key) ∧
    (∀ a : Adr, Devm.getCode postC a = Devm.getCode p a) := by
  set msg : Msg := callMsg sevm p mcs 0 sevm.currentTarget
    callee callee true isStat data calleeCode dp with hmsg
  have h_afford : ¬ msg.benv.state.bal msg.caller < msg.value := by
    show ¬ (p.getAcct sevm.currentTarget).bal < 0
    rw [B256.lt_iff_toNat_lt_toNat]
    exact Nat.not_lt.mpr (Nat.zero_le _)
  obtain ⟨stmid, hsub, hbt⟩ :=
    Msg.benvAfterTransfer_of_affordable msg rfl h_afford
  have henter : (Frame.ofCall msg).enter =
      .run (initEvm (msg.withBenv
        ((msg.benv.withState stmid).addBal msg.currentTarget msg.value))) := by
    apply Frame.enter_run_of_nonprecompile hbt
    · rfl
    · exact h_nonprecompile
  simp only [RunFrame, henter] at hframe
  obtain ⟨raw, hxl, hr⟩ := hframe
  subst hxl
  subst hr
  have hexecraw : exec (initEvm (msg.withBenv
      ((msg.benv.withState stmid).addBal msg.currentTarget msg.value)))
      = raw :=
    (exec_iff_exec_eq _ _ _ _).mp hfill
  -- every account's storage and code across the zero-value seam
  have hseam : ∀ a : Adr,
      ((((msg.benv.withState stmid).addBal msg.currentTarget
        msg.value).state.get a).stor = (p.state.get a).stor) ∧
      ((((msg.benv.withState stmid).addBal msg.currentTarget
        msg.value).state.get a).code = (p.state.get a).code) := by
    intro a
    have h2 := joinState_addBal_acct stmid msg.currentTarget msg.value a
    have h1 := joinState_subBal_acct hsub a
    exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩
  rcases hsettle : (Frame.ofCall msg).settle raw with e | child2
  · rw [hsettle, Resume.run_call_fatal] at hres
    cases hres
  by_cases hroom : p.stack.length < 1024
  case neg =>
    obtain ⟨ed, hoverflow⟩ :=
      resume_call_overflow (child := child2) (oi := oi) (os := os) hroom
    rw [hsettle, hoverflow] at hres
    cases hres
  case pos =>
  by_cases hce : child2.error.isSome
  · -- the rolled-back leg: the child's world is the message's entry state
    rw [hsettle, Resume.run_call_err hce hroom] at hres
    have hpost : postC = ((incorporateChildOnError p child2
        child2.output).setMach ⟨0 :: p.stack, p.memory,
          p.gasLeft + child2.gasLeft⟩).memWrite oi
            (child2.output.take os) :=
      Except.ok.inj hres
    have hstate : child2.state = msg.benv.state := settle_err_state hsettle hce
    subst hpost
    refine ⟨⟨child2.output.take os, List.length_take_le _ _, rfl⟩, ?_, ?_⟩
    · intro a key
      show ((child2.state.get a).stor).get key = ((p.state.get a).stor).get key
      rw [hstate]
      rfl
    · intro a
      show (child2.state.get a).code = (p.state.get a).code
      rw [hstate]
      rfl
  · -- the clean leg: the responder's own execution, at either budget class
    have hce' : child2.error.isSome = false := by
      revert hce
      cases child2.error.isSome <;> simp
    rw [hsettle, Resume.run_call_ok hce' hroom] at hres
    have hpost : postC = ((incorporateChildOnSuccess p child2
        child2.output).setMach ⟨1 :: p.stack, p.memory,
          p.gasLeft + child2.gasLeft⟩).memWrite oi
            (child2.output.take os) :=
      Except.ok.inj hres
    have hraw : raw = .ok child2 := settle_ok_clean hsettle hce'
    rcases Nat.lt_or_ge mcs 17 with hlow | hhigh
    · -- refuted: the responder cannot settle clean under its charge
      exfalso
      obtain ⟨e', d', herr⟩ := callee_exec_low_gas
        (m := msg.withBenv
          ((msg.benv.withState stmid).addBal msg.currentTarget msg.value))
        rfl hlow
      rw [herr, hraw] at hexecraw
      cases hexecraw
    · obtain ⟨out, hexec, _herr, _hout, _hgas, hworld, _⟩ :=
        callee_exec (msg.withBenv
          ((msg.benv.withState stmid).addBal msg.currentTarget msg.value))
          (mcs - 17) rfl (by show mcs = mcs - 17 + 17; omega)
      rw [hexec, hraw] at hexecraw
      have hchild : child2 = out := (Except.ok.inj hexecraw).symm
      have hstate : child2.state =
          ((msg.benv.withState stmid).addBal msg.currentTarget
            msg.value).state := by
        rw [hchild]
        exact congrArg World.state hworld
      subst hpost
      refine ⟨⟨child2.output.take os, List.length_take_le _ _, rfl⟩, ?_, ?_⟩
      · intro a key
        show ((child2.state.get a).stor).get key =
          ((p.state.get a).stor).get key
        rw [hstate, (hseam a).1]
      · intro a
        show (child2.state.get a).code = (p.state.get a).code
        rw [hstate, (hseam a).2]

/-- A compiled-step hypothesis, opened at the `Xinst.step` layer: the slot and
its `Filled` witness survive, and the step relation is exposed for rewriting
by a step equation. -/
private lemma runCompiled_exec_okStep {sevm : Sevm} {devm postC : Devm}
    {x : Xinst} (h : Ninst.RunCompiled sevm devm (.exec x) postC) :
    ∃ xl, Xlot.Filled xl ∧
      XStep.Run (Xinst.step sevm devm x) xl (.ok postC) := by
  obtain ⟨xl, hfill, hrun⟩ := h
  refine ⟨xl, hfill, ?_⟩
  have h0 := hrun 0
  rwa [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at h0

/-! ## The two responder-crossing preservation theorems

The analysis-mode duals of the world module's construction-mode crossings:
given an **arbitrary** derivation's `Ninst.RunCompiled` crossing of a
`CALL`/`STATICCALL` aimed at the responder, at any gas, the parent's memory
moves only by the resume's own window write, and every account's storage and
code survive. -/

theorem responder_call_effects {sevm : Sevm} {preC postC : Devm}
    {gw tw iiw isw oiw osw : B256} {rest : List B256}
    (h_stk : preC.stack = gw :: tw :: 0 :: iiw :: isw :: oiw :: osw :: rest)
    (h_code : CodeAt preC tw.toAdr calleeCode)
    (h_depth : sevm.depth ≠ 0)
    (h_nonprecompile : sevm.benvStat.rules.isPrecomp tw.toAdr = false)
    (run : Ninst.RunCompiled sevm preC (.exec .call) postC) :
    (∃ ys : Bytes, ys.length ≤ osw.toNat ∧
      postC.memory = (preC.memory.extends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).write
          oiw.toNat ys) ∧
    (∀ (a : Adr) (key : B256),
      Devm.getStorVal postC a key = Devm.getStorVal preC a key) ∧
    (∀ a : Adr, Devm.getCode postC a = Devm.getCode preC a) := by
  have hcc : (addAccessedAddress
      (preC.setMach ⟨rest, preC.memory, preC.gasLeft⟩)
        tw.toAdr).state.getCode tw.toAdr = calleeCode := h_code
  have h_del := accessDelegation_of_none
    (devm := addAccessedAddress
      (preC.setMach ⟨rest, preC.memory, preC.gasLeft⟩) tw.toAdr)
    (a := tw.toAdr) (by rw [hcc]; exact calleeCode_notDelegation)
  rw [hcc] at h_del
  rcases hsplit : calculateMsgCallGas 0 gw.toNat
    (addAccessedAddress (preC.setMach ⟨rest, preC.memory, preC.gasLeft⟩)
      tw.toAdr).gasLeft
    ((preC.setMach ⟨rest, preC.memory, preC.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩])
    (accessCost tw.toAdr
      (preC.setMach
        ⟨rest, preC.memory, preC.gasLeft⟩).accessedAddresses + 0)
    with ⟨mcc, mcs⟩
  obtain ⟨xl, hfill, hx⟩ := runCompiled_exec_okStep run
  by_cases hga : mcc +
      (preC.setMach ⟨rest, preC.memory, preC.gasLeft⟩).extCost
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] ≤
      (addAccessedAddress (preC.setMach ⟨rest, preC.memory, preC.gasLeft⟩)
        tw.toAdr).gasLeft
  case neg =>
    rw [step_call_zero_value_outOfGas h_stk rfl h_del rfl hsplit
      (by omega)] at hx
    obtain ⟨-, hcontra⟩ := hx
    cases hcontra
  case pos =>
    rw [Xinst.step_call_zero_value_spawn h_stk rfl h_del rfl hsplit hga
      h_depth] at hx
    obtain ⟨r, hframe, hres⟩ := hx
    obtain ⟨hmem, hstor, hcode'⟩ :=
      responder_crossing_tail h_nonprecompile hfill hframe hres
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨ys, hlen, heq⟩ := hmem
      exact ⟨ys, hlen, heq⟩
    · intro a key
      exact hstor a key
    · intro a
      exact hcode' a

theorem responder_statcall_effects {sevm : Sevm} {preC postC : Devm}
    {gw tw iiw isw oiw osw : B256} {rest : List B256}
    (h_stk : preC.stack = gw :: tw :: iiw :: isw :: oiw :: osw :: rest)
    (h_code : CodeAt preC tw.toAdr calleeCode)
    (h_depth : sevm.depth ≠ 0)
    (h_nonprecompile : sevm.benvStat.rules.isPrecomp tw.toAdr = false)
    (run : Ninst.RunCompiled sevm preC (.exec .statcall) postC) :
    (∃ ys : Bytes, ys.length ≤ osw.toNat ∧
      postC.memory = (preC.memory.extends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).write
          oiw.toNat ys) ∧
    (∀ (a : Adr) (key : B256),
      Devm.getStorVal postC a key = Devm.getStorVal preC a key) ∧
    (∀ a : Adr, Devm.getCode postC a = Devm.getCode preC a) := by
  have hcc : (addAccessedAddress
      (preC.setMach ⟨rest, preC.memory, preC.gasLeft⟩)
        tw.toAdr).state.getCode tw.toAdr = calleeCode := h_code
  have h_del := accessDelegation_of_none
    (devm := addAccessedAddress
      (preC.setMach ⟨rest, preC.memory, preC.gasLeft⟩) tw.toAdr)
    (a := tw.toAdr) (by rw [hcc]; exact calleeCode_notDelegation)
  rw [hcc] at h_del
  rcases hsplit : calculateMsgCallGas 0 gw.toNat
    (addAccessedAddress (preC.setMach ⟨rest, preC.memory, preC.gasLeft⟩)
      tw.toAdr).gasLeft
    ((preC.setMach ⟨rest, preC.memory, preC.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩])
    (accessCost tw.toAdr
      (preC.setMach
        ⟨rest, preC.memory, preC.gasLeft⟩).accessedAddresses + 0)
    with ⟨mcc, mcs⟩
  obtain ⟨xl, hfill, hx⟩ := runCompiled_exec_okStep run
  by_cases hga : mcc +
      (preC.setMach ⟨rest, preC.memory, preC.gasLeft⟩).extCost
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] ≤
      (addAccessedAddress (preC.setMach ⟨rest, preC.memory, preC.gasLeft⟩)
        tw.toAdr).gasLeft
  case neg =>
    rw [step_statcall_outOfGas h_stk rfl h_del rfl hsplit (by omega)] at hx
    obtain ⟨-, hcontra⟩ := hx
    cases hcontra
  case pos =>
    rw [Xinst.step_statcall_spawn h_stk rfl h_del rfl hsplit hga
      h_depth] at hx
    obtain ⟨r, hframe, hres⟩ := hx
    obtain ⟨hmem, hstor, hcode'⟩ :=
      responder_crossing_tail h_nonprecompile hfill hframe hres
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨ys, hlen, heq⟩ := hmem
      exact ⟨ys, hlen, heq⟩
    · intro a key
      exact hstor a key
    · intro a
      exact hcode' a

/-- The route finals' `hcall` premise, discharged for any frame whose depth
is nonzero and whose fork rules do not treat the callee as a precompile. -/
theorem responder_hcall {sevm : Sevm} {target : B256}
    (h_depth : sevm.depth ≠ 0)
    (h_np : sevm.benvStat.rules.isPrecomp target.toAdr = false) :
    ∀ (preC postC : Devm) (gw : B256) (rest : Stack),
      preC.stack = gw :: target :: 0 :: 284 :: 36 :: 0 :: 0 :: rest →
      MemWordAt preC (targetWord * 32).toNat target →
      CodeAt preC target.toAdr calleeCode →
      Ninst.RunCompiled sevm preC Ninst.call postC →
      MemWordAt postC (targetWord * 32).toNat target ∧
        CodeAt postC target.toAdr calleeCode ∧
        Devm.getStorVal postC sevm.currentTarget
            (countSlot sevm.caller.toB256) =
          Devm.getStorVal preC sevm.currentTarget
            (countSlot sevm.caller.toB256) := by
  intro preC postC gw rest hstk window codeAt run
  obtain ⟨⟨ys, hlen, hmem⟩, hstor, hcode⟩ :=
    responder_call_effects hstk codeAt h_depth h_np run
  refine ⟨?_, ?_, hstor _ _⟩
  · refine MemWordAt.acrossExtendsWrite hmem (Or.inr ?_) window
    have h0 : ((0 : B256)).toNat = 0 := rfl
    rw [h0] at hlen ⊢
    omega
  · show Devm.getCode postC target.toAdr = calleeCode
    rw [hcode target.toAdr]
    exact codeAt

/-- The route finals' `hstat` premise, discharged the same way: the
`STATICCALL`'s 32-byte return window lands at offset zero, clear of the
staged target at `targetWord * 32`. -/
theorem responder_hstat {sevm : Sevm} {target : B256}
    (h_depth : sevm.depth ≠ 0)
    (h_np : sevm.benvStat.rules.isPrecomp target.toAdr = false) :
    ∀ (preC postC : Devm) (gw : B256) (rest : Stack),
      preC.stack = gw :: target :: 284 :: 4 :: 0 :: 32 :: rest →
      MemWordAt preC (targetWord * 32).toNat target →
      CodeAt preC target.toAdr calleeCode →
      Ninst.RunCompiled sevm preC Ninst.statcall postC →
      MemWordAt postC (targetWord * 32).toNat target ∧
        CodeAt postC target.toAdr calleeCode ∧
        Devm.getStorVal postC sevm.currentTarget
            (countSlot sevm.caller.toB256) =
          Devm.getStorVal preC sevm.currentTarget
            (countSlot sevm.caller.toB256) := by
  intro preC postC gw rest hstk window codeAt run
  obtain ⟨⟨ys, hlen, hmem⟩, hstor, hcode⟩ :=
    responder_statcall_effects hstk codeAt h_depth h_np run
  refine ⟨?_, ?_, hstor _ _⟩
  · refine MemWordAt.acrossExtendsWrite hmem (Or.inr ?_) window
    have h0 : ((0 : B256)).toNat = 0 := rfl
    have h32 : ((32 : B256)).toNat = 32 := rfl
    rw [h32] at hlen
    rw [h0]
    have hwin : 32 ≤ (targetWord * 32).toNat := by decide
    omega
  · show Devm.getCode postC target.toAdr = calleeCode
    rw [hcode target.toAdr]
    exact codeAt

/-! ## The removal span's five writes, keyed

`hRemoveCount` hands the join an arbitrary crossing of
`removeClearTargetIndexPrefix` plus its closing `SSTORE`, with the three
storage cells the span's key computations read pinned at entry.  Naming those
cells names all five write keys — `arrayEntrySlot idx0`, `indexSlot last0`,
`arrayEntrySlot len0`, `arrayLengthSlot` and `indexSlot target` — and five
disequalities against the caller's count slot close the thread. -/

/-- One image-extension step: a `loadWord` only extends memory. -/
private theorem memImage_extend {a b : Devm} {img : Bytes} {i n : Nat}
    (h : b.memory = a.memory.extend i n) (image : MemImage a img) :
    MemImage b img :=
  ⟨by rw [h]; exact image.1.extend i n, by rw [h]; exact image.2.extend i n⟩

set_option maxRecDepth 8192 in
/-- The caller's count cell across `removeTarget`'s whole span, at any state
whose Registry cells are pinned: every one of the five `SSTORE` keys is named
by the entry cells, and each misses the count slot by hypothesis. -/
theorem removeSpan_countPreserved {sevm : Sevm} {a b postW : Devm}
    {target idx0 len0 last0 : B256}
    (hne1 : arrayEntrySlot idx0 ≠ countSlot sevm.caller.toB256)
    (hne2 : indexSlot last0 ≠ countSlot sevm.caller.toB256)
    (hne3 : arrayEntrySlot len0 ≠ countSlot sevm.caller.toB256)
    (hne4 : arrayLengthSlot ≠ countSlot sevm.caller.toB256)
    (hne5 : indexSlot target ≠ countSlot sevm.caller.toB256)
    (windowT : MemWordAt a (targetWord * 32).toNat target)
    (hidx : Devm.getStorVal a sevm.currentTarget (indexSlot target) = idx0)
    (hlen : Devm.getStorVal a sevm.currentTarget arrayLengthSlot = len0)
    (hlast : Devm.getStorVal a sevm.currentTarget (arrayEntrySlot len0)
      = last0)
    (run : Line.Run sevm a removeClearTargetIndexPrefix b)
    (post : Ninst.RunCompiled sevm b Ninst.sstore postW) :
    Devm.getStorVal postW sevm.currentTarget
        (countSlot sevm.caller.toB256) =
      Devm.getStorVal a sevm.currentTarget
        (countSlot sevm.caller.toB256) := by
  have cellOf : ∀ {x y : Devm}, Devm.getStor x = Devm.getStor y →
      ∀ k : B256, Devm.getStorVal x sevm.currentTarget k =
        Devm.getStorVal y sevm.currentTarget k :=
    fun heq k => congrArg (fun f : Adr → Stor =>
      (f sevm.currentTarget).get k) heq
  unfold removeClearTargetIndexPrefix at run
  rcases of_run_append removeArrayLengthPrefix run with ⟨sD, rD, run⟩
  unfold removeArrayLengthPrefix at rD
  rcases of_run_append removeClearTailPrefix rD with ⟨sC, rC, rD⟩
  unfold removeClearTailPrefix at rC
  rcases of_run_append removeMovedIndexPrefix rC with ⟨sB, rB, rC⟩
  unfold removeMovedIndexPrefix at rB
  rcases of_run_append removeArrayHolePrefix rB with ⟨sA, rA, rB⟩
  -- the hole prefix: three cells staged to memory, the hole key built
  unfold removeArrayHolePrefix targetIndexKey at rA
  rcases of_run_append (loadWord targetWord ++ tagTop indexRegion) rA
    with ⟨a1, q1, rA⟩
  rcases of_run_append [Ninst.sload] rA with ⟨a2, q2, rA⟩
  rcases of_run_append (mstoreAt removedIndexWord) rA with ⟨a3, q3, rA⟩
  rcases of_run_append [Ninst.pushB256 arrayLengthSlot, Ninst.sload] rA
    with ⟨a4, q4, rA⟩
  rcases of_run_append (mstoreAt arrayLengthWord) rA with ⟨a5, q5, rA⟩
  rcases of_run_append (loadWord arrayLengthWord) rA with ⟨a6, q6, rA⟩
  rcases of_run_append (tagTop arrayRegion) rA with ⟨a7, q7, rA⟩
  rcases of_run_append [Ninst.sload] rA with ⟨a8, q8, rA⟩
  rcases of_run_append (mstoreAt lastTargetWord) rA with ⟨a9, q9, rA⟩
  rcases of_run_append (loadWord lastTargetWord) rA with ⟨a10, q10, rA⟩
  rcases of_run_append (loadWord removedIndexWord) rA with ⟨a11, q11, rA⟩
  -- the target-index key on the stack
  have p1 : indexSlot target :: [] <<+ a1.stack := by
    rcases of_run_append (loadWord targetWord) q1 with ⟨u1, l1, t1⟩
    have pu := prefix_of_loadWord_window windowT nil_pref l1
    unfold tagTop at t1
    rcases Line.of_run_cons t1 with ⟨u2, o1, t1⟩
    rcases Line.of_run_cons t1 with ⟨u3, o2, hnil⟩
    cases hnil
    exact prefix_of_or o2 (prefix_of_push (of_run_pushB256 o1) pu)
  have windowT1 := windowT.acrossLoadTag q1
  have hstor1 : Devm.getStor a1 = Devm.getStor a :=
    (Line.of_inv Devm.getStor
      (by unfold loadWord tagTop; line_inv) q1).symm
  -- the reverse-index read: `idx0`
  rcases Line.of_run_cons q2 with ⟨_v, o2s, hnil2⟩
  cases hnil2
  obtain ⟨v1, p2, hv1⟩ := prefix_of_sload o2s p1
  have hv1' : v1 = idx0 := by
    rw [hv1, cellOf hstor1 (indexSlot target)]
    exact hidx
  have windowT2 := windowT1.acrossNinst o2s
  have hstor2 : Devm.getStor a2 = Devm.getStor a :=
    ((Ninst.Hinv.inv (f := Devm.getStor) o2s).symm).trans hstor1
  -- staged at `removedIndexWord`
  obtain ⟨p3, hm3⟩ := of_run_mstoreAt_val q3 p2
  obtain ⟨img2, image2⟩ := windowT2.memImage
  have windowRem3 : MemWordAt a3 (removedIndexWord * 32).toNat v1 :=
    MemWordAt.of_write image2 hm3
  have windowT3 := windowT2.writeMiss hm3 (by decide)
  have hstor3 : Devm.getStor a3 = Devm.getStor a :=
    ((Line.of_inv Devm.getStor (by unfold mstoreAt; line_inv) q3).symm).trans
      hstor2
  -- the length read: `len0`
  rcases Line.of_run_cons q4 with ⟨b4, o4p, q4'⟩
  rcases Line.of_run_cons q4' with ⟨b4', o4s, hnil4⟩
  cases hnil4
  have p4p := prefix_of_push (of_run_pushB256 o4p) nil_pref
  obtain ⟨v2, p4, hv2⟩ := prefix_of_sload o4s p4p
  have hv2' : v2 = len0 := by
    rw [hv2,
      cellOf (((Ninst.Hinv.inv (f := Devm.getStor) o4p).symm).trans hstor3)
        arrayLengthSlot]
    exact hlen
  have windowT4 := (windowT3.acrossNinst o4p).acrossNinst o4s
  have windowRem4 := (windowRem3.acrossNinst o4p).acrossNinst o4s
  have hstor4 : Devm.getStor a4 = Devm.getStor a :=
    ((Ninst.Hinv.inv (f := Devm.getStor) o4s).symm).trans
      (((Ninst.Hinv.inv (f := Devm.getStor) o4p).symm).trans hstor3)
  -- staged at `arrayLengthWord`
  obtain ⟨p5, hm5⟩ := of_run_mstoreAt_val q5 p4
  obtain ⟨img4, image4⟩ := windowT4.memImage
  have windowLen5 : MemWordAt a5 (arrayLengthWord * 32).toNat v2 :=
    MemWordAt.of_write image4 hm5
  have windowT5 := windowT4.writeMiss hm5 (by decide)
  have windowRem5 := windowRem4.writeMiss hm5 (by decide)
  have hstor5 : Devm.getStor a5 = Devm.getStor a :=
    ((Line.of_inv Devm.getStor (by unfold mstoreAt; line_inv) q5).symm).trans
      hstor4
  -- the last-entry key and read: `last0`
  have p6 := prefix_of_loadWord_window windowLen5 nil_pref q6
  have windowT6 := windowT5.acrossLoadWord q6
  have windowRem6 := windowRem5.acrossLoadWord q6
  have windowLen6 := windowLen5.acrossLoadWord q6
  have hstor6 : Devm.getStor a6 = Devm.getStor a :=
    ((Line.of_inv Devm.getStor (by unfold loadWord; line_inv) q6).symm).trans
      hstor5
  unfold tagTop at q7
  rcases Line.of_run_cons q7 with ⟨c7, o7p, q7'⟩
  rcases Line.of_run_cons q7' with ⟨c7', o7o, hnil7⟩
  cases hnil7
  have p7 : (regionWord arrayRegion ||| v2) :: [] <<+ a7.stack :=
    prefix_of_or o7o (prefix_of_push (of_run_pushB256 o7p) p6)
  have windowT7 := (windowT6.acrossNinst o7p).acrossNinst o7o
  have windowRem7 := (windowRem6.acrossNinst o7p).acrossNinst o7o
  have windowLen7 := (windowLen6.acrossNinst o7p).acrossNinst o7o
  have hstor7 : Devm.getStor a7 = Devm.getStor a :=
    ((Ninst.Hinv.inv (f := Devm.getStor) o7o).symm).trans
      (((Ninst.Hinv.inv (f := Devm.getStor) o7p).symm).trans hstor6)
  rcases Line.of_run_cons q8 with ⟨_v8, o8s, hnil8⟩
  cases hnil8
  obtain ⟨v3, p8, hv3⟩ := prefix_of_sload o8s p7
  have hv3' : v3 = last0 := by
    rw [hv3,
      show (regionWord arrayRegion ||| v2) = arrayEntrySlot v2 from rfl,
      hv2', cellOf hstor7 (arrayEntrySlot len0)]
    exact hlast
  have windowT8 := windowT7.acrossNinst o8s
  have windowRem8 := windowRem7.acrossNinst o8s
  have windowLen8 := windowLen7.acrossNinst o8s
  have hstor8 : Devm.getStor a8 = Devm.getStor a :=
    ((Ninst.Hinv.inv (f := Devm.getStor) o8s).symm).trans hstor7
  -- staged at `lastTargetWord`
  obtain ⟨p9, hm9⟩ := of_run_mstoreAt_val q9 p8
  obtain ⟨img8, image8⟩ := windowT8.memImage
  have windowLast9 : MemWordAt a9 (lastTargetWord * 32).toNat v3 :=
    MemWordAt.of_write image8 hm9
  have windowT9 := windowT8.writeMiss hm9 (by decide)
  have windowRem9 := windowRem8.writeMiss hm9 (by decide)
  have windowLen9 := windowLen8.writeMiss hm9 (by decide)
  have hstor9 : Devm.getStor a9 = Devm.getStor a :=
    ((Line.of_inv Devm.getStor (by unfold mstoreAt; line_inv) q9).symm).trans
      hstor8
  -- the hole write's operands
  have p10 := prefix_of_loadWord_window windowLast9 nil_pref q10
  have windowT10 := windowT9.acrossLoadWord q10
  have windowRem10 := windowRem9.acrossLoadWord q10
  have windowLen10 := windowLen9.acrossLoadWord q10
  have windowLast10 := windowLast9.acrossLoadWord q10
  have p11 := prefix_of_loadWord_window windowRem10 p10 q11
  have windowT11 := windowT10.acrossLoadWord q11
  have windowRem11 := windowRem10.acrossLoadWord q11
  have windowLen11 := windowLen10.acrossLoadWord q11
  have windowLast11 := windowLast10.acrossLoadWord q11
  have hstor11 : Devm.getStor a11 = Devm.getStor a :=
    ((Line.of_inv Devm.getStor (by unfold loadWord; line_inv) q11).symm).trans
      (((Line.of_inv Devm.getStor (by unfold loadWord; line_inv)
        q10).symm).trans hstor9)
  unfold tagTop at rA
  rcases Line.of_run_cons rA with ⟨e1, oAp, rA'⟩
  rcases Line.of_run_cons rA' with ⟨e1', oAo, hnilA⟩
  cases hnilA
  have pHole : (regionWord arrayRegion ||| v1) :: v3 :: [] <<+ sA.stack :=
    prefix_of_or oAo (prefix_of_push (of_run_pushB256 oAp) p11)
  have windowTA := (windowT11.acrossNinst oAp).acrossNinst oAo
  have windowRemA := (windowRem11.acrossNinst oAp).acrossNinst oAo
  have windowLenA := (windowLen11.acrossNinst oAp).acrossNinst oAo
  have windowLastA := (windowLast11.acrossNinst oAp).acrossNinst oAo
  have hstorA : Devm.getStor sA = Devm.getStor a :=
    ((Ninst.Hinv.inv (f := Devm.getStor) oAo).symm).trans
      (((Ninst.Hinv.inv (f := Devm.getStor) oAp).symm).trans hstor11)
  -- write 1: the array hole
  rcases of_run_append [Ninst.sstore] rB with ⟨b1, w1, rB⟩
  rcases Line.of_run_cons w1 with ⟨_b1', w1s, hnilB1⟩
  cases hnilB1
  have hset1 := sstore_getStor_set w1s pHole
  have pB1 := prefix_of_sstore w1s pHole
  have kB1 : Devm.getStorVal b1 sevm.currentTarget
      (countSlot sevm.caller.toB256) =
      Devm.getStorVal a sevm.currentTarget
        (countSlot sevm.caller.toB256) := by
    show (Devm.getStor b1 sevm.currentTarget).get _ = _
    rw [hset1, Stor.get_set_ne _ (by
      show (regionWord arrayRegion ||| v1) ≠ countSlot sevm.caller.toB256
      rw [show (regionWord arrayRegion ||| v1) = arrayEntrySlot v1 from rfl,
        hv1']
      exact hne1)]
    exact cellOf hstorA _
  have windowRemB1 := windowRemA.acrossNinst w1s
  have windowLenB1 := windowLenA.acrossNinst w1s
  have windowLastB1 := windowLastA.acrossNinst w1s
  have windowTB1 := windowTA.acrossNinst w1s
  -- write 2: the moved index
  rcases of_run_append (loadWord removedIndexWord) rB with ⟨b2, w2, rB⟩
  have pB2 := prefix_of_loadWord_window windowRemB1 nil_pref w2
  have windowLastB2 := windowLastB1.acrossLoadWord w2
  have windowLenB2 := windowLenB1.acrossLoadWord w2
  have windowTB2 := windowTB1.acrossLoadWord w2
  have kB2 : Devm.getStorVal b2 sevm.currentTarget
      (countSlot sevm.caller.toB256) =
      Devm.getStorVal a sevm.currentTarget
        (countSlot sevm.caller.toB256) :=
    (cellOf (Line.of_inv Devm.getStor (by unfold loadWord; line_inv)
      w2).symm _).trans kB1
  unfold lastTargetIndexKey at rB
  rcases of_run_append (loadWord lastTargetWord) rB with ⟨b3, w3, rB⟩
  have pB3 := prefix_of_loadWord_window windowLastB2 pB2 w3
  have windowLenB3 := windowLenB2.acrossLoadWord w3
  have windowTB3 := windowTB2.acrossLoadWord w3
  have kB3 : Devm.getStorVal b3 sevm.currentTarget
      (countSlot sevm.caller.toB256) =
      Devm.getStorVal a sevm.currentTarget
        (countSlot sevm.caller.toB256) :=
    (cellOf (Line.of_inv Devm.getStor (by unfold loadWord; line_inv)
      w3).symm _).trans kB2
  unfold tagTop at rB
  rcases Line.of_run_cons rB with ⟨b5, wBp, rB'⟩
  rcases Line.of_run_cons rB' with ⟨b5', wBo, hnilB⟩
  cases hnilB
  have pMoved : (regionWord indexRegion ||| v3) :: v1 :: [] <<+ sB.stack :=
    prefix_of_or wBo (prefix_of_push (of_run_pushB256 wBp) pB3)
  have windowLenB := (windowLenB3.acrossNinst wBp).acrossNinst wBo
  have windowTB := (windowTB3.acrossNinst wBp).acrossNinst wBo
  have kB : Devm.getStorVal sB sevm.currentTarget
      (countSlot sevm.caller.toB256) =
      Devm.getStorVal a sevm.currentTarget
        (countSlot sevm.caller.toB256) :=
    (cellOf ((Ninst.Hinv.inv (f := Devm.getStor) wBo).symm) _).trans
      ((cellOf ((Ninst.Hinv.inv (f := Devm.getStor) wBp).symm) _).trans kB3)
  rcases of_run_append [Ninst.sstore, Ninst.pushB256 0] rC with ⟨c1, wc, rC⟩
  rcases Line.of_run_cons wc with ⟨c1a, wc1, wc'⟩
  rcases Line.of_run_cons wc' with ⟨c1b, wc2, hnilC1⟩
  cases hnilC1
  have hset2 := sstore_getStor_set wc1 pMoved
  have pC0 := prefix_of_sstore wc1 pMoved
  have pC1 : (0 : B256) :: [] <<+ c1.stack :=
    prefix_of_push (of_run_pushB256 wc2) pC0
  have kC1 : Devm.getStorVal c1 sevm.currentTarget
      (countSlot sevm.caller.toB256) =
      Devm.getStorVal a sevm.currentTarget
        (countSlot sevm.caller.toB256) := by
    refine (cellOf ((Ninst.Hinv.inv (f := Devm.getStor) wc2).symm) _).trans ?_
    show (Devm.getStor c1a sevm.currentTarget).get _ = _
    rw [hset2, Stor.get_set_ne _ (by
      show (regionWord indexRegion ||| v3) ≠ countSlot sevm.caller.toB256
      rw [show (regionWord indexRegion ||| v3) = indexSlot v3 from rfl, hv3']
      exact hne2)]
    exact kB
  have windowLenC1 := (windowLenB.acrossNinst wc1).acrossNinst wc2
  have windowTC1 := (windowTB.acrossNinst wc1).acrossNinst wc2
  -- write 3: the cleared tail
  rcases of_run_append (loadWord arrayLengthWord) rC with ⟨c2, wc3, rC⟩
  have pC2 := prefix_of_loadWord_window windowLenC1 pC1 wc3
  have windowLenC2 := windowLenC1.acrossLoadWord wc3
  have windowTC2 := windowTC1.acrossLoadWord wc3
  have kC2 : Devm.getStorVal c2 sevm.currentTarget
      (countSlot sevm.caller.toB256) =
      Devm.getStorVal a sevm.currentTarget
        (countSlot sevm.caller.toB256) :=
    (cellOf (Line.of_inv Devm.getStor (by unfold loadWord; line_inv)
      wc3).symm _).trans kC1
  unfold tagTop at rC
  rcases Line.of_run_cons rC with ⟨c3, wCp, rC'⟩
  rcases Line.of_run_cons rC' with ⟨c3', wCo, hnilC⟩
  cases hnilC
  have pTail : (regionWord arrayRegion ||| v2) :: 0 :: [] <<+ sC.stack :=
    prefix_of_or wCo (prefix_of_push (of_run_pushB256 wCp) pC2)
  have windowLenC := (windowLenC2.acrossNinst wCp).acrossNinst wCo
  have windowTC := (windowTC2.acrossNinst wCp).acrossNinst wCo
  have kC : Devm.getStorVal sC sevm.currentTarget
      (countSlot sevm.caller.toB256) =
      Devm.getStorVal a sevm.currentTarget
        (countSlot sevm.caller.toB256) :=
    (cellOf ((Ninst.Hinv.inv (f := Devm.getStor) wCo).symm) _).trans
      ((cellOf ((Ninst.Hinv.inv (f := Devm.getStor) wCp).symm) _).trans kC2)
  -- write 4: the restored length
  rcases of_run_append [Ninst.sstore] rD with ⟨d1, wd, rD⟩
  rcases Line.of_run_cons wd with ⟨d1', wd1, hnilD1⟩
  cases hnilD1
  have hset3 := sstore_getStor_set wd1 pTail
  have pD0 := prefix_of_sstore wd1 pTail
  have kD1 : Devm.getStorVal d1 sevm.currentTarget
      (countSlot sevm.caller.toB256) =
      Devm.getStorVal a sevm.currentTarget
        (countSlot sevm.caller.toB256) := by
    show (Devm.getStor d1 sevm.currentTarget).get _ = _
    rw [hset3, Stor.get_set_ne _ (by
      show (regionWord arrayRegion ||| v2) ≠ countSlot sevm.caller.toB256
      rw [show (regionWord arrayRegion ||| v2) = arrayEntrySlot v2 from rfl,
        hv2']
      exact hne3)]
    exact kC
  have windowLenD1 := windowLenC.acrossNinst wd1
  have windowTD1 := windowTC.acrossNinst wd1
  rcases of_run_append (loadWord arrayLengthWord) rD with ⟨d2, wd2, rD⟩
  have pD2 := prefix_of_loadWord_window windowLenD1 pD0 wd2
  have windowTD2 := windowTD1.acrossLoadWord wd2
  have kD2 : Devm.getStorVal d2 sevm.currentTarget
      (countSlot sevm.caller.toB256) =
      Devm.getStorVal a sevm.currentTarget
        (countSlot sevm.caller.toB256) :=
    (cellOf (Line.of_inv Devm.getStor (by unfold loadWord; line_inv)
      wd2).symm _).trans kD1
  rcases Line.of_run_cons rD with ⟨d3, wd3, rD'⟩
  rcases Line.of_run_cons rD' with ⟨d4, wd4, rD''⟩
  rcases Line.of_run_cons rD'' with ⟨d5, wd5, rD'''⟩
  rcases Line.of_run_cons rD''' with ⟨d6, wd6, hnilD⟩
  cases hnilD
  have pD3 := prefix_of_push (of_run_pushB256 wd3) pD2
  have hswap : Stack.Swap (0 : Fin 16).val
      ((1 : B256) :: v2 :: []) (v2 :: (1 : B256) :: []) := Stack.swapCore_zero
  have pD4 := Stack.prefix_of_swap hswap (of_run_swap wd4) pD3
  have pD5 := prefix_of_sub wd5 pD4
  have pD6 := prefix_of_push (of_run_pushB256 wd6) pD5
  have windowTD := (((windowTD2.acrossNinst wd3).acrossNinst
    wd4).acrossNinst wd5).acrossNinst wd6
  have kD : Devm.getStorVal sD sevm.currentTarget
      (countSlot sevm.caller.toB256) =
      Devm.getStorVal a sevm.currentTarget
        (countSlot sevm.caller.toB256) :=
    (cellOf ((Ninst.Hinv.inv (f := Devm.getStor) wd6).symm) _).trans
      ((cellOf ((Ninst.Hinv.inv (f := Devm.getStor) wd5).symm) _).trans
        ((cellOf ((Ninst.Hinv.inv (f := Devm.getStor) wd4).symm) _).trans
          ((cellOf ((Ninst.Hinv.inv (f := Devm.getStor) wd3).symm) _).trans
            kD2)))
  -- write 5's operands: the cleared target index
  rcases of_run_append [Ninst.sstore, Ninst.pushB256 0] run with ⟨e2, we, run⟩
  rcases Line.of_run_cons we with ⟨e2a, we1, we'⟩
  rcases Line.of_run_cons we' with ⟨e2b, we2, hnilE1⟩
  cases hnilE1
  have hset4 := sstore_getStor_set we1 pD6
  have pE0 := prefix_of_sstore we1 pD6
  have pE1 : (0 : B256) :: [] <<+ e2.stack :=
    prefix_of_push (of_run_pushB256 we2) pE0
  have kE1 : Devm.getStorVal e2 sevm.currentTarget
      (countSlot sevm.caller.toB256) =
      Devm.getStorVal a sevm.currentTarget
        (countSlot sevm.caller.toB256) := by
    refine (cellOf ((Ninst.Hinv.inv (f := Devm.getStor) we2).symm) _).trans ?_
    show (Devm.getStor e2a sevm.currentTarget).get _ = _
    rw [hset4, Stor.get_set_ne _ hne4]
    exact kD
  have windowTE1 := (windowTD.acrossNinst we1).acrossNinst we2
  unfold targetIndexKey at run
  rcases of_run_append (loadWord targetWord) run with ⟨e3, we3, run⟩
  have pE3 := prefix_of_loadWord_window windowTE1 pE1 we3
  have kE3 : Devm.getStorVal e3 sevm.currentTarget
      (countSlot sevm.caller.toB256) =
      Devm.getStorVal a sevm.currentTarget
        (countSlot sevm.caller.toB256) :=
    (cellOf (Line.of_inv Devm.getStor (by unfold loadWord; line_inv)
      we3).symm _).trans kE1
  unfold tagTop at run
  rcases Line.of_run_cons run with ⟨e4, weP, run'⟩
  rcases Line.of_run_cons run' with ⟨e4', weO, hnilE⟩
  cases hnilE
  have pFinal : (regionWord indexRegion ||| target) :: 0 :: [] <<+ b.stack :=
    prefix_of_or weO (prefix_of_push (of_run_pushB256 weP) pE3)
  have kFinal : Devm.getStorVal b sevm.currentTarget
      (countSlot sevm.caller.toB256) =
      Devm.getStorVal a sevm.currentTarget
        (countSlot sevm.caller.toB256) :=
    (cellOf ((Ninst.Hinv.inv (f := Devm.getStor) weO).symm) _).trans
      ((cellOf ((Ninst.Hinv.inv (f := Devm.getStor) weP).symm) _).trans kE3)
  -- the closing store
  have hset5 := sstore_getStor_set (Ninst.Run.of_runCompiled post) pFinal
  show (Devm.getStor postW sevm.currentTarget).get _ = _
  rw [hset5, Stor.get_set_ne _ (by
    show (regionWord indexRegion ||| target) ≠ countSlot sevm.caller.toB256
    rw [show (regionWord indexRegion ||| target) = indexSlot target from rfl]
    exact hne5)]
  exact kFinal

/-! ## The index pins

The `:330-337` template of `Blanc/LidoCircuitBreakerPauseAttainment.lean`,
instantiated at the two expiry paths: one kernel evaluation per row pins the
routed path to its inventory index. -/

set_option maxRecDepth 20000 in
/-- Only inventory index `19` — `.pauseLastTargetExpiry` — nominates the
count-zero arm's expiry path. -/
theorem pauseLastExpiry_index_pin :
    ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some pauseLastExpiryPath) →
        index = RuntimePersistentWrite.pauseLastTargetExpiry.index := by
  decide +kernel

set_option maxRecDepth 20000 in
/-- Only inventory index `18` — `.pauseRetainedTargetExpiry` — nominates the
checked arm's expiry path. -/
theorem pauseRetainedExpiry_index_pin :
    ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some pauseRetainedExpiryPath) →
        index = RuntimePersistentWrite.pauseRetainedTargetExpiry.index := by
  decide +kernel

/-! ## J1: row 19 attained with the `.pauseExpiry` role -/

/-- The world's `toAdr` round trip at the staged target. -/
private theorem pauseWorld_callee_toAdr :
    (pauseWorldCallee.toB256).toAdr = pauseWorldCallee := by decide

set_option maxRecDepth 4096 in
/-- **J1.**  The `.pauseLastTargetExpiry` row — inventory index 19, the
count-zero arm's expiry `SSTORE` — is attained with the `.pauseExpiry` role,
at the row-19 pause witness world. -/
theorem attainable_pauseLastTargetExpiry_pauseExpiry :
    Attainable officialParams .pauseLastTargetExpiry .pauseExpiry := by
  refine attainable_of_entryRoute_frame_burn (ca := configWorldOwner)
    (pauseWorld_currentTarget _ _) (pauseWorld_codeAddress _ _)
    (fun found pathEq =>
      RuntimePersistentWrite.eq_of_path pauseLastExpiry_index_pin found
        pathEq)
    (by decide) pauseLastWorld_run
    (fun devm post hburn hwalk => ?_)
  have cellDevm : ∀ k : B256,
      Devm.getStorVal devm configWorldOwner k = pauseLastWorldStor.get k := by
    intro k
    rw [show Devm.getStorVal devm configWorldOwner k
          = Devm.getStorVal pauseLastPre configWorldOwner k from
        congrArg (fun w : State =>
          (w.get configWorldOwner).stor.get k) hburn.state.symm]
    exact pauseWorld_getStorVal _ _
  refine runtimeMain_routeTo_pauseLastExpiry (img := [])
    (target := pauseWorldCallee.toB256) (code := calleeCode)
    (countAfter := 0) (idx0 := 1) (len0 := 1)
    (last0 := pauseWorldCallee.toB256) hwalk
    (MemImage.of_memory_eq hburn.memory.symm ⟨Mem.wf_empty, Mem.reads_empty⟩)
    (pauseWorld_selector _ _) (pauseWorld_argTarget _ _)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- hcode
    rw [pauseWorld_callee_toAdr]
    exact (show CodeAt pauseLastPre pauseWorldCallee calleeCode from
      pauseWorld_calleeCodeAt _ _).ofState hburn.state
  · -- assigned
    show Devm.getStorVal devm configWorldOwner
      (assignmentSlot pauseWorldCallee.toB256) ≠ 0
    rw [cellDevm, pauseLastStor_assignment]
    decide
  · -- hprev
    show Devm.getStorVal devm configWorldOwner
        (assignmentSlot pauseWorldCallee.toB256)
      = pauseLastSevm.caller.toB256
    rw [cellDevm, pauseLastStor_assignment]
    exact (pauseWorld_callerWord pauseLastWorldStor pauseLastWorldGas).symm
  · -- hidx0
    show Devm.getStorVal devm configWorldOwner
      (indexSlot pauseWorldCallee.toB256) = 1
    rw [cellDevm, pauseLastStor_index]
  · -- hlen0
    show Devm.getStorVal devm configWorldOwner arrayLengthSlot = 1
    rw [cellDevm, pauseLastStor_length]
  · -- hlast0
    show Devm.getStorVal devm configWorldOwner (arrayEntrySlot 1)
      = pauseWorldCallee.toB256
    rw [cellDevm, pauseLastStor_entry]
  · -- hneAC
    rw [pauseWorld_callerWord]
    exact pauseWorld_assignCallee_ne_count
  · -- hneAI
    exact pauseWorld_assignCallee_ne_indexCallee
  · -- hneAL
    exact pauseWorld_length_ne_assignCallee.symm
  · -- hneAE
    exact pauseWorld_entryOne_ne_assignCallee.symm
  · -- hneCI
    rw [pauseWorld_callerWord]
    exact pauseWorld_indexCallee_ne_count.symm
  · -- hneCL
    rw [pauseWorld_callerWord]
    exact pauseWorld_length_ne_count.symm
  · -- hneCE
    rw [pauseWorld_callerWord]
    exact pauseWorld_entryOne_ne_count.symm
  · -- hcount
    show Devm.getStorVal devm configWorldOwner
      (countSlot pauseLastSevm.caller.toB256) - 1 = 0
    rw [show pauseLastSevm.caller.toB256 = pauseWorldPauser from
        pauseWorld_callerWord pauseLastWorldStor pauseLastWorldGas,
      cellDevm, pauseLastStor_count]
    decide
  · -- hzero
    rfl
  · -- hRemoveCount
    intro a b postW wT hidxa hlena hlasta lrun srun
    refine removeSpan_countPreserved ?_ ?_ ?_ ?_ ?_ wT hidxa hlena hlasta
      lrun srun
    · rw [pauseWorld_callerWord]
      exact pauseWorld_entryOne_ne_count
    · rw [pauseWorld_callerWord]
      exact pauseWorld_indexCallee_ne_count
    · rw [pauseWorld_callerWord]
      exact pauseWorld_entryOne_ne_count
    · rw [pauseWorld_callerWord]
      exact pauseWorld_length_ne_count
    · rw [pauseWorld_callerWord]
      exact pauseWorld_indexCallee_ne_count
  · -- hcall
    exact responder_hcall (show (1024 : Nat) ≠ 0 by decide) (by decide)
  · -- hstat
    exact responder_hstat (show (1024 : Nat) ≠ 0 by decide) (by decide)

/-! ## J2: row 18 attained with the `.pauseExpiry` role -/

set_option maxRecDepth 4096 in
/-- **J2.**  The `.pauseRetainedTargetExpiry` row — inventory index 18, the
checked arm's expiry `SSTORE` — is attained with the `.pauseExpiry` role, at
the row-18 pause witness world. -/
theorem attainable_pauseRetainedTargetExpiry_pauseExpiry :
    Attainable officialParams .pauseRetainedTargetExpiry .pauseExpiry := by
  refine attainable_of_entryRoute_frame_burn (ca := configWorldOwner)
    (pauseWorld_currentTarget _ _) (pauseWorld_codeAddress _ _)
    (fun found pathEq =>
      RuntimePersistentWrite.eq_of_path pauseRetainedExpiry_index_pin found
        pathEq)
    (by decide) pauseRetainedWorld_run
    (fun devm post hburn hwalk => ?_)
  have cellDevm : ∀ k : B256,
      Devm.getStorVal devm configWorldOwner k =
        pauseRetainedWorldStor.get k := by
    intro k
    rw [show Devm.getStorVal devm configWorldOwner k
          = Devm.getStorVal pauseRetainedPre configWorldOwner k from
        congrArg (fun w : State =>
          (w.get configWorldOwner).stor.get k) hburn.state.symm]
    exact pauseWorld_getStorVal _ _
  refine runtimeMain_routeTo_pauseRetainedExpiry (img := [])
    (target := pauseWorldCallee.toB256) (code := calleeCode)
    (countAfter := 1) (idx0 := 1) (len0 := 2)
    (last0 := pauseWorldT2) hwalk
    (MemImage.of_memory_eq hburn.memory.symm ⟨Mem.wf_empty, Mem.reads_empty⟩)
    (pauseWorld_selector _ _) (pauseWorld_argTarget _ _)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- hcode
    rw [pauseWorld_callee_toAdr]
    exact (show CodeAt pauseRetainedPre pauseWorldCallee calleeCode from
      pauseWorld_calleeCodeAt _ _).ofState hburn.state
  · -- assigned
    show Devm.getStorVal devm configWorldOwner
      (assignmentSlot pauseWorldCallee.toB256) ≠ 0
    rw [cellDevm, pauseRetainedStor_assignment]
    decide
  · -- hprev
    show Devm.getStorVal devm configWorldOwner
        (assignmentSlot pauseWorldCallee.toB256)
      = pauseRetainedSevm.caller.toB256
    rw [cellDevm, pauseRetainedStor_assignment]
    exact (pauseWorld_callerWord pauseRetainedWorldStor
      pauseRetainedWorldGas).symm
  · -- hidx0
    show Devm.getStorVal devm configWorldOwner
      (indexSlot pauseWorldCallee.toB256) = 1
    rw [cellDevm, pauseRetainedStor_index]
  · -- hlen0
    show Devm.getStorVal devm configWorldOwner arrayLengthSlot = 2
    rw [cellDevm, pauseRetainedStor_length]
  · -- hlast0
    show Devm.getStorVal devm configWorldOwner (arrayEntrySlot 2)
      = pauseWorldT2
    rw [cellDevm, pauseRetainedStor_entryTwo]
  · -- hneAC
    rw [pauseWorld_callerWord]
    exact pauseWorld_assignCallee_ne_count
  · -- hneAI
    exact pauseWorld_assignCallee_ne_indexCallee
  · -- hneAL
    exact pauseWorld_length_ne_assignCallee.symm
  · -- hneAE
    exact pauseWorld_entryTwo_ne_assignCallee.symm
  · -- hneCI
    rw [pauseWorld_callerWord]
    exact pauseWorld_indexCallee_ne_count.symm
  · -- hneCL
    rw [pauseWorld_callerWord]
    exact pauseWorld_length_ne_count.symm
  · -- hneCE
    rw [pauseWorld_callerWord]
    exact pauseWorld_entryTwo_ne_count.symm
  · -- hcount
    show Devm.getStorVal devm configWorldOwner
      (countSlot pauseRetainedSevm.caller.toB256) - 1 = 1
    rw [show pauseRetainedSevm.caller.toB256 = pauseWorldPauser from
        pauseWorld_callerWord pauseRetainedWorldStor pauseRetainedWorldGas,
      cellDevm, pauseRetainedStor_count]
    decide
  · -- hnz
    decide
  · -- hRemoveCount
    intro a b postW wT hidxa hlena hlasta lrun srun
    refine removeSpan_countPreserved ?_ ?_ ?_ ?_ ?_ wT hidxa hlena hlasta
      lrun srun
    · rw [pauseWorld_callerWord]
      exact pauseWorld_entryOne_ne_count
    · rw [pauseWorld_callerWord]
      exact pauseWorld_indexT2_ne_count
    · rw [pauseWorld_callerWord]
      exact pauseWorld_entryTwo_ne_count
    · rw [pauseWorld_callerWord]
      exact pauseWorld_length_ne_count
    · rw [pauseWorld_callerWord]
      exact pauseWorld_indexCallee_ne_count
  · -- hcall
    exact responder_hcall (show (1024 : Nat) ≠ 0 by decide) (by decide)
  · -- hstat
    exact responder_hstat (show (1024 : Nat) ≠ 0 by decide) (by decide)

/-! ## J3: the joins -/

/-- **J3, row 19.**  The row-19 pause walk's own `pauseSuccess` boundary
carries an expiry `SSTORE` whose stored word obeys the zero-count value law,
and the row it reaches is attained: the first two conjuncts come from
`pauseSuccess_expiryWrite_dichotomy` applied to
`pauseLastWorld_successBoundary` with the right disjunct excluded — the
boundary count is `0`, and the dichotomy's panic arm requires it nonzero —
and the third is the J1 witness.

Honesty register (J4): the walk's outcome is `.ok` (`pauseLastWorld_run`);
the entry world is Registry-well-formed by *projection* —
`pauseLastStor_witness` exhibits `RegistryWitness` for the singleton
`[(0x77, 9)]` — with **no** claim that the world is reachable from any
genesis or deployment; the callee at `0x77` is the neutral responder
`calleeCode`, which accepts `pauseFor(uint256)` by returning success and
answers `isPaused()` with the canonical 32-byte `1`, and does nothing else. -/
theorem pauseLastWorld_join :
    ∃ (mid : Devm) (out : Execution) (value : B256),
      Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        pauseLastSevm mid pauseSuccess out ∧
      PauseExpiryWrite pauseLastSevm mid configWorldOwner value ∧
      PauseExpiryValue pauseLastSevm.benvStat.time pauseWorldInterval 0
        value ∧
      Attainable officialParams .pauseLastTargetExpiry .pauseExpiry := by
  obtain ⟨mid, out, hboundary, hcount, hinterval, howner⟩ :=
    pauseLastWorld_successBoundary
  rcases pauseSuccess_expiryWrite_dichotomy howner hcount hinterval
      hboundary with ⟨value, hwrite, hvalue⟩ | ⟨hnz, -, -⟩
  · exact ⟨mid, out, value, hboundary, hwrite, hvalue,
      attainable_pauseLastTargetExpiry_pauseExpiry⟩
  · exact absurd rfl hnz

/-- **J3, row 18.**  The row-18 walk's `pauseSuccess` boundary carries an
expiry `SSTORE` obeying the count-one value law — the dichotomy's panic arm
is excluded because `timestamp + interval` does not wrap at this world
(`B256.Nof 10 2592000` holds outright) — and the reached row is attained by
the J2 witness.

Honesty register (J4): outcome `.ok` (`pauseRetainedWorld_run`); the entry
world is Registry-well-formed by projection — `pauseRetainedStor_witness`
exhibits `RegistryWitness` for `[(0x77, 9), (0x88, 9)]` — with no
genesis-reachability claim; the callee at `0x77` is the same neutral
responder, and `0x88` is codeless and never called. -/
theorem pauseRetainedWorld_join :
    ∃ (mid : Devm) (out : Execution) (value : B256),
      Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        pauseRetainedSevm mid pauseSuccess out ∧
      PauseExpiryWrite pauseRetainedSevm mid configWorldOwner value ∧
      PauseExpiryValue pauseRetainedSevm.benvStat.time pauseWorldInterval 1
        value ∧
      Attainable officialParams .pauseRetainedTargetExpiry .pauseExpiry := by
  obtain ⟨mid, out, hboundary, hcount, hinterval, howner⟩ :=
    pauseRetainedWorld_successBoundary
  rcases pauseSuccess_expiryWrite_dichotomy howner hcount hinterval
      hboundary with ⟨value, hwrite, hvalue⟩ | ⟨-, hwrap, -⟩
  · exact ⟨mid, out, value, hboundary, hwrite, hvalue,
      attainable_pauseRetainedTargetExpiry_pauseExpiry⟩
  · refine absurd (show B256.Nof pauseRetainedSevm.benvStat.time
      pauseWorldInterval from ?_) hwrap
    show pauseWorldTime.toNat + pauseWorldInterval.toNat < 2 ^ 256
    norm_num [show pauseWorldTime.toNat = 10 from by decide,
      show pauseWorldInterval.toNat = 2592000 from by decide]

end Blanc.LidoCircuitBreaker
