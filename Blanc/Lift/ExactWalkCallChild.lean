import Blanc.Lift.ExactWalk
import Blanc.Lift.ExactWalkCut
import Blanc.ForwardCall

/-!
# Gas-exact walk step: a value-bearing `CALL` into a callee whose child run is known

`Ninst.runCompiled_call_nonzero` leaves the child as the total term `exec cevm`.
This module specializes it to the case a walk actually has in hand: the child's
message is the one the parent built, debited of the value, and its execution is
known to halt cleanly (`exec … = .ok cpost`, `cpost.error = none`, typically
from the callee's own exact walk).  The parent then resumes in `callChildPost`:
the child's world adopted, its gas returned, its logs and warm sets merged, the
success flag pushed and its output copied into the output window.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- The message a nonzero-value `CALL` enters with once the value has moved:
the spawned message over the caller's debited world `stmid`, credited at the
callee. -/
def callChildMsg (sevm : Sevm) (p : Devm) (mcs : Nat) (value : B256) (callee dadr : Adr)
    (ii is : Nat) (code : ByteArray) (dp : Bool) (stmid : State) : Msg :=
  (valueCallSpawnMsg sevm p mcs value callee dadr ii is code dp).withBenv
    (((valueCallSpawnMsg sevm p mcs value callee dadr ii is code dp).benv.withState stmid).addBal
      callee value)

/-- The parent state a `CALL` resumes in after its child halted cleanly. -/
def callChildPost (p cpost : Devm) (oi os : Nat) : Devm :=
  ((incorporateChildOnSuccess p cpost cpost.output).setMach
    ⟨1 :: p.stack, p.memory, p.gasLeft + cpost.gasLeft,
      (incorporateChildOnSuccess p cpost cpost.output).stateGas⟩).memWrite oi
    (cpost.output.take os)

/-- An affordable nonzero-value `CALL` to a non-precompile callee whose entered
child halts cleanly resumes in `callChildPost`.  The child's derivation is the
premise `h_exec`, stated at exactly the message the parent builds. -/
lemma Ninst.runCompiled_call_nonzero_child {sevm : Sevm} {devm : Devm}
    {gw cw vw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc create mcc mcs : Nat} {stmid : State} {cpost : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_stk : devm.stack = gw :: cw :: vw :: iiw :: isw :: oiw :: osw :: s)
    (h_value : vw ≠ 0)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩).accessedAddresses
        + dgc = acc)
    (h_create :
      (if ¬ (d1.getAcct cw.toAdr).Empty then 0 else gNewAccount) = create)
    (h_split :
      calculateMsgCallGas vw.toNat gw.toNat d1.gasLeft ext
        (acc + create + gasCallValue) = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft)
    (h_dynamic : sevm.isStatic = false)
    (h_sender : ¬ (d1.getAcct sevm.currentTarget).bal < vw)
    (h_depth : sevm.depth ≠ 0)
    (h_nonprecompile : sevm.benvStat.rules.isPrecomp dadr = false)
    (h_room : s.length < 1024)
    (h_sub : d1.state.subBal sevm.currentTarget vw = some stmid)
    (h_exec : exec (initEvm (callChildMsg sevm
      (callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat)
      mcs vw cw.toAdr dadr iiw.toNat isw.toNat code dp stmid)) = .ok cpost)
    (h_error : cpost.error = none) :
    Ninst.RunCompiled sevm devm (.exec .call)
      (callChildPost (callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat)
        cpost oiw.toNat osw.toNat) := by
  let p := callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat
  let msg := valueCallSpawnMsg sevm p mcs vw cw.toAdr dadr iiw.toNat isw.toNat code dp
  have h_afford : ¬ msg.benv.state.bal msg.caller < msg.value := by
    change ¬ (d1.getAcct sevm.currentTarget).bal < vw
    exact h_sender
  obtain ⟨stmid', hsub', hbt⟩ := Msg.benvAfterTransfer_of_affordable msg rfl h_afford
  have hstmid : stmid' = stmid := by
    have h := hsub'
    change d1.state.subBal sevm.currentTarget vw = some stmid' at h
    exact Option.some.inj (h.symm.trans h_sub)
  subst hstmid
  let benv' := (msg.benv.withState stmid').addBal msg.currentTarget msg.value
  let child := initEvm (msg.withBenv benv')
  have henter : (Frame.ofCall msg).enter = .run child := by
    apply Frame.enter_run_of_nonprecompile hbt
    · rfl
    · change sevm.benvStat.rules.isPrecomp dadr = false
      exact h_nonprecompile
  have hexec : exec child = .ok cpost := h_exec
  have hsettle : (Frame.ofCall msg).settle (exec child) = .ok cpost := by
    rw [hexec, Frame.settle_eq_settleMsg_handleErrorWith, executeCode.handleErrorWith_ok]
    simp only [Frame.ofCall, Frame.settleMsg, processMessage.settle, h_error,
      Option.isSome_none, Bool.false_eq_true, ite_false, bind, Except.bind]
  have hdi := accessDelegation_inv h_del
  have hpstack : p.stack.length < 1024 := by
    change d1.stack.length < 1024
    rw [hdi.1]
    exact h_room
  have hres : Resume.run (.call p oiw.toNat osw.toNat)
      ((Frame.ofCall msg).settle (exec child)) =
        .ok (callChildPost p cpost oiw.toNat osw.toNat) := by
    rw [hsettle, Resume.run_call_ok (by rw [h_error]; rfl) hpstack]
    rfl
  exact Ninst.runCompiled_call_nonzero hfork h_stk h_value h_ext h_del h_acc h_create
    h_split h_gas h_dynamic h_sender h_depth henter hres

/-- The resumed parent's machine and world when the child returned no output:
the memory is the parent's own (already extended), and everything the child
settled is adopted. -/
theorem callChildPost_facts (p cpost : Devm) (oi os : Nat) (hout : cpost.output = []) :
    (callChildPost p cpost oi os).stack = 1 :: p.stack ∧
    (callChildPost p cpost oi os).memory = p.memory ∧
    (callChildPost p cpost oi os).gasLeft = p.gasLeft + cpost.gasLeft ∧
    (callChildPost p cpost oi os).state = cpost.state ∧
    (callChildPost p cpost oi os).transientStorage = cpost.transientStorage ∧
    (callChildPost p cpost oi os).logs = p.logs ++ cpost.logs ∧
    (callChildPost p cpost oi os).refundCounter = p.refundCounter + cpost.refundCounter ∧
    (callChildPost p cpost oi os).error = p.error ∧
    (callChildPost p cpost oi os).output = p.output ∧
    (callChildPost p cpost oi os).returnData = [] ∧
    (callChildPost p cpost oi os).accountsToDelete =
      p.accountsToDelete.union cpost.accountsToDelete ∧
    (callChildPost p cpost oi os).accessedAddresses =
      p.accessedAddresses.union cpost.accessedAddresses ∧
    (callChildPost p cpost oi os).accessedStorageKeys =
      p.accessedStorageKeys.union cpost.accessedStorageKeys ∧
    (callChildPost p cpost oi os).createdAccounts = cpost.createdAccounts := by
  unfold callChildPost
  rw [hout, List.take_nil, Devm.memWrite_nil]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- With the whole remaining gas asked for (the `GAS; CALL` idiom), a value-bearing `CALL`
forwards all but one 64th of what is left after its fixed charge, plus the stipend. -/
theorem calculateMsgCallGas_all {value gas gl extra : Nat} (hv : value ≠ 0) (hg : gl ≤ gas)
    (he : extra ≤ gl) :
    calculateMsgCallGas value gas gl 0 extra =
      ⟨except64th (gl - extra) + extra, except64th (gl - extra) + gCallStipend⟩ := by
  have hmin : min gas (except64th (gl - 0 - extra)) = except64th (gl - extra) := by
    have hle : except64th (gl - extra) ≤ gas := by
      unfold except64th
      omega
    rw [Nat.sub_zero]
    exact Nat.min_eq_right hle
  unfold calculateMsgCallGas
  simp only [hv, ite_false, show ¬ gl < extra + 0 by omega, hmin]

/-! ## Cut-run steps for loops around a call -/

section CutSteps

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {f : SFunc} {r : Seg}
  {S : List B256} {M : Mem} {G : Nat}

/-- `PUSH0` inside a cut run. -/
theorem rxc_push0 {le : ([] : Bytes).length ≤ 32} (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (0 :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b S M (G + 2)) (.next (.push [] le) f) r :=
  .next (Ninst.runCompiled_pushBytes (devm := St b S M (G + 2)) (c := gBase) (G := G)
    rfl rfl hroom) k

/-- `CALLDATALOAD` inside a cut run. -/
theorem rxc_calldataload {x : B256} (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (Sevm.dataWord sevm x :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (x :: S) M (G + 3)) (.next (.reg .calldataload) f) r :=
  .next (Ninst.runCompiled_calldataload (devm := St b (x :: S) M (G + 3)) (G := G) rfl rfl rfl
    hroom) k

end CutSteps

end Blanc.Lift
