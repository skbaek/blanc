import Blanc.Lift.SystemDrainer.Jumps
import Blanc.Lift.ExactWalkCallChild
import Blanc.Lift.CreationOps
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.WithdrawalRequest.SystemProtocol
import Blanc.Lift.WithdrawalRequest.SystemFrameEffects
import Blanc.StorageOnlySpec

/-!
# E5(ii): a frame whose caller is SYSTEM_ADDRESS drains the queue mid-block

The FIFO headline excludes code at SYSTEM_ADDRESS (`systemEmpty`).  Without it, a
contract installed there can `CALL` the withdrawal predeploy from inside a user
transaction; the predeploy selects its system path on `CALLER == SYSTEM_ADDRESS`
and dequeues.  This module walks such a contract (`Blanc/Lift/SystemDrainer`,
`PUSH0 ×5; PUSH20 predeploy; GAS; CALL; STOP`): its run succeeds and leaves the
predeploy storage representing `system σ`.
-/

namespace Blanc.Lift.WithdrawalRequest.SystemDrain

open Jaune Blanc.Lift Blanc.Lift.WithdrawalRequest

/-- The predeploy address the drainer pushes. -/
theorem drainer_callee :
    (Bytes.toB256 [0x00, 0x00, 0x09, 0x61, 0xef, 0x48, 0x0e, 0xb5, 0x5e, 0x80, 0xd1, 0x9a,
      0xd8, 0x35, 0x79, 0xa6, 0x4c, 0x00, 0x70, 0x02]).toAdr = withdrawalRequestPredeployAddress :=
  rfl

/-- Word constants of the drainer's call, each decided once. -/
private theorem drain_consts :
    (0 : B256).toNat = 0 ∧ memExtsSize 0 [(0, 0), (0, 0)] = 0 := ⟨rfl, by decide⟩

/-- **The drainer's `CALL`.**  From SYSTEM_ADDRESS, a zero-value call with empty windows and
all remaining gas into the installed predeploy runs its system path: the parent resumes with
success pushed and the predeploy storage representing `system σ`. -/
theorem drain_call {sevm : Sevm} {base : Devm} {Gc : Nat} {cw : B256}
    {σ : Blanc.WithdrawalRequest.State}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hsys : sevm.currentTarget = systemAddress)
    (hcw : cw.toAdr = withdrawalRequestPredeployAddress)
    (hcode : base.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (hrep : Blanc.WithdrawalRequest.RepresentsStorage
      (base.getStor withdrawalRequestPredeployAddress).get σ)
    (hsum : Blanc.WithdrawalRequest.effectiveExcess σ + σ.count < 2 ^ 256)
    (horig : ∀ key, getOrigStorVal sevm withdrawalRequestPredeployAddress key =
      (base.getStor withdrawalRequestPredeployAddress).get key)
    (hGlt : Gc < 2 ^ 256) (hG : 427202 ≤ Gc) :
    ∃ post G',
      Ninst.RunCompiled sevm (St base [Nat.toB256 Gc, cw, 0, 0, 0, 0, 0] Mem.empty Gc)
        (.exec .call) (St post [1] Mem.empty G') ∧
      Blanc.WithdrawalRequest.RepresentsStorage
        (post.getStor withdrawalRequestPredeployAddress).get (Blanc.WithdrawalRequest.system σ) ∧
      post.error = base.error ∧
      (∀ a, post.getCode a = base.getCode a) ∧
      (∀ a, a ≠ withdrawalRequestPredeployAddress → post.getStor a = base.getStor a) ∧
      post.logs = base.logs ∧
      post.accountsToDelete.isEmpty = base.accountsToDelete.isEmpty ∧
      base.refundCounter ≤ post.refundCounter := by
  have hd1code : (addAccessedAddress (St base [] Mem.empty Gc) cw.toAdr).state.getCode cw.toAdr =
      Blanc.withdrawalRequestCode := by
    rw [hcw]
    exact hcode
  have hdel : accessDelegation (addAccessedAddress (St base [] Mem.empty Gc) cw.toAdr) cw.toAdr =
      ⟨false, cw.toAdr, Blanc.withdrawalRequestCode, 0,
        addAccessedAddress (St base [] Mem.empty Gc) cw.toAdr⟩ := by
    unfold accessDelegation
    simp only [hd1code, withdrawalRequestCode_nondelegated]
  have hacc : accessCost cw.toAdr base.accessedAddresses ≤ 2600 := by
    unfold accessCost
    split <;> decide
  have hext : (St base [] Mem.empty Gc).extCost [⟨(0 : B256).toNat, (0 : B256).toNat⟩,
      ⟨(0 : B256).toNat, (0 : B256).toNat⟩] = 0 := by
    simp only [Devm.extCost, St, Devm.memory_setMach, drain_consts.1]
    rfl
  have hgw : (Nat.toB256 Gc).toNat = Gc := B256.toNat_toB256_of_lt hGlt
  have hsplit : calculateMsgCallGas 0 (Nat.toB256 Gc).toNat Gc 0
      (accessCost cw.toAdr base.accessedAddresses + 0) =
      ⟨except64th (Gc - (accessCost cw.toAdr base.accessedAddresses + 0)) +
        (accessCost cw.toAdr base.accessedAddresses + 0),
       except64th (Gc - (accessCost cw.toAdr base.accessedAddresses + 0))⟩ := by
    have hmin : min (Nat.toB256 Gc).toNat
        (except64th (Gc - 0 - (accessCost cw.toAdr base.accessedAddresses + 0))) =
        except64th (Gc - (accessCost cw.toAdr base.accessedAddresses + 0)) := by
      rw [hgw, Nat.sub_zero]
      apply Nat.min_eq_right
      unfold except64th
      omega
    generalize ha : accessCost cw.toAdr base.accessedAddresses + 0 = a at hmin ⊢
    unfold calculateMsgCallGas
    simp only [↓reduceIte, hmin, Nat.add_zero, show ¬ Gc < a by omega]
  have hsub : (addAccessedAddress (St base [] Mem.empty Gc) cw.toAdr).state.subBal
      sevm.currentTarget 0 =
      some (base.state.setBal sevm.currentTarget (base.state.bal sevm.currentTarget - 0)) := by
    have hnl : ¬ base.state.bal sevm.currentTarget < 0 := by
      rw [B256.not_lt]
      exact B256.zero_le _
    change base.state.subBal sevm.currentTarget 0 = _
    unfold State.subBal
    simp only [hnl, ite_false]
  generalize hstmid : base.state.setBal sevm.currentTarget
    (base.state.bal sevm.currentTarget - 0) = stmid at hsub
  generalize hfwd : except64th (Gc - (accessCost cw.toAdr base.accessedAddresses + 0)) = fwd
    at hsplit
  have hfwdge : 212301 ≤ fwd := by
    rw [← hfwd]
    unfold except64th
    omega
  generalize hmsg : callChildMsg sevm
    (callSpawnParent (addAccessedAddress (St base [] Mem.empty Gc) cw.toAdr)
      (fwd + (accessCost cw.toAdr base.accessedAddresses + 0) + 0)
      (0 : B256).toNat (0 : B256).toNat (0 : B256).toNat (0 : B256).toNat)
    fwd 0 cw.toAdr cw.toAdr (0 : B256).toNat (0 : B256).toNat
    Blanc.withdrawalRequestCode false stmid = msg
  have mfork : CoveredFork (initSevm msg).benvStat.fork := by rw [← hmsg]; exact hfork
  have mcode : (initSevm msg).code = Blanc.withdrawalRequestCode := by rw [← hmsg]; rfl
  have mcaller : (initSevm msg).caller = systemAddress := by rw [← hmsg]; exact hsys
  have mtarget : (initSevm msg).currentTarget = withdrawalRequestPredeployAddress := by
    rw [← hmsg]; exact hcw
  have mstatic : (initSevm msg).isStatic = false := by
    rw [← hmsg]
    show (false || sevm.isStatic) = false
    rw [hstatic]; rfl
  have mgas : msg.gas = fwd := by rw [← hmsg]; rfl
  have mstor : (initDevm msg).getStor withdrawalRequestPredeployAddress =
      base.getStor withdrawalRequestPredeployAddress := by
    rw [← hmsg]
    exact getStor_subBal_addBal hsub
  have mcodeP : (initDevm msg).getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode := by
    rw [← hmsg]
    change (stmid.addBal cw.toAdr 0).getCode withdrawalRequestPredeployAddress = _
    rw [State.addBal_getCode, ← hstmid, State.setBal_getCode]
    exact hcode
  have mrep : Blanc.WithdrawalRequest.RepresentsStorage
      ((initDevm msg).getStorVal (initSevm msg).currentTarget) σ := by
    change Blanc.WithdrawalRequest.RepresentsStorage
      ((initDevm msg).getStor (initSevm msg).currentTarget).get σ
    rw [mtarget, mstor]
    exact hrep
  have hbound := systemFrameGas_le (initSevm msg) (initDevm msg) Mem.empty rfl
  generalize hcg : systemFrameGas (initSevm msg) (initDevm msg) Mem.empty = cg at hbound
  have frame := exec_system_frame_exact (sevm := initSevm msg) (base := initDevm msg)
    (memory := Mem.empty) (gas := fwd - cg) mcode mfork mcaller mstatic
    (by simp only [gCallStipend]; omega)
  rw [hcg, show fwd - cg + cg = (initDevm msg).gasLeft by rw [initDevm_gasLeft, mgas]; omega,
    ← St.self (d := initDevm msg) (S := []) (M := Mem.empty) rfl rfl] at frame
  have hexec := (exec_iff_exec_eq 0 (initSevm msg) (initDevm msg) _).mp frame
  have herror : (systemFramePost (initSevm msg) (initDevm msg) Mem.empty (fwd - cg)).error =
      none := by
    rw [systemFramePost_error]
    rfl
  have hprec : sevm.benvStat.rules.isPrecomp cw.toAdr = false := by
    have h := withdrawalRequest_not_precompile hfork
    rw [hcw]
    exact propext (iff_of_false h (by decide))
  have run := Ninst.runCompiled_call_zero_child
    (devm := St base [Nat.toB256 Gc, cw, 0, 0, 0, 0, 0] Mem.empty Gc)
    (gw := Nat.toB256 Gc) (cw := cw) (iiw := 0) (isw := 0) (oiw := 0) (osw := 0)
    (s := []) (dp := false) (dadr := cw.toAdr) (code := Blanc.withdrawalRequestCode) (dgc := 0)
    (d1 := addAccessedAddress (St base [] Mem.empty Gc) cw.toAdr) (ext := 0)
    (acc := accessCost cw.toAdr base.accessedAddresses + 0)
    (mcc := fwd + (accessCost cw.toAdr base.accessedAddresses + 0)) (mcs := fwd)
    (stmid := stmid)
    (cpost := systemFramePost (initSevm msg) (initDevm msg) Mem.empty (fwd - cg))
    hfork rfl hext hdel rfl hsplit ?hgas hdepth hprec (by decide) hsub ?hexec herror
  case hgas =>
    have : fwd ≤ Gc - (accessCost cw.toAdr base.accessedAddresses + 0) := by
      rw [← hfwd]; unfold except64th; omega
    have hle : accessCost cw.toAdr base.accessedAddresses + 0 ≤ Gc := by omega
    change fwd + (accessCost cw.toAdr base.accessedAddresses + 0) + 0 ≤ Gc
    rw [Nat.add_zero]
    exact (Nat.le_sub_iff_add_le hle).mp this
  case hexec =>
    subst hmsg
    exact hexec
  have pmem : (callSpawnParent (addAccessedAddress (St base [] Mem.empty Gc) cw.toAdr)
      (fwd + (accessCost cw.toAdr base.accessedAddresses + 0) + 0)
      (0 : B256).toNat (0 : B256).toNat (0 : B256).toNat (0 : B256).toNat).memory = Mem.empty := by
    change Mem.empty.extends [((0 : B256).toNat, (0 : B256).toNat),
      ((0 : B256).toNat, (0 : B256).toNat)] = Mem.empty
    simp only [Mem.extends, drain_consts.1]
    rfl
  have pfacts := callChildPost_facts_zero (callSpawnParent
      (addAccessedAddress (St base [] Mem.empty Gc) cw.toAdr)
      (fwd + (accessCost cw.toAdr base.accessedAddresses + 0) + 0)
      (0 : B256).toNat (0 : B256).toNat (0 : B256).toNat (0 : B256).toNat)
    (systemFramePost (initSevm msg) (initDevm msg) Mem.empty (fwd - cg)) (0 : B256).toNat
    (0 : B256).toNat drain_consts.1
  have hrep' := systemFramePost_represents (initSevm msg) (initDevm msg) Mem.empty (fwd - cg)
    σ mrep hsum
  generalize hpost : callChildPost (callSpawnParent
      (addAccessedAddress (St base [] Mem.empty Gc) cw.toAdr)
      (fwd + (accessCost cw.toAdr base.accessedAddresses + 0) + 0)
      (0 : B256).toNat (0 : B256).toNat (0 : B256).toNat (0 : B256).toNat)
    (systemFramePost (initSevm msg) (initDevm msg) Mem.empty (fwd - cg)) (0 : B256).toNat
    (0 : B256).toNat = post at run pfacts
  obtain ⟨pstack, pmem', -, pstate, perr⟩ := pfacts
  rw [pmem] at pmem'
  have pstack' : post.stack = [1] := pstack
  have hSt := St.self pstack' pmem'
  have hchild : (callChildPost (callSpawnParent
      (addAccessedAddress (St base [] Mem.empty Gc) cw.toAdr)
      (fwd + (accessCost cw.toAdr base.accessedAddresses + 0) + 0)
      (0 : B256).toNat (0 : B256).toNat (0 : B256).toNat (0 : B256).toNat)
    (systemFramePost (initSevm msg) (initDevm msg) Mem.empty (fwd - cg)) (0 : B256).toNat
    (0 : B256).toNat) = post := hpost
  rw [drain_consts.1] at hchild
  unfold callChildPost at hchild
  rw [List.take_zero, Devm.memWrite_nil] at hchild
  have mstorAll : ∀ a, (initDevm msg).getStor a = base.getStor a := by
    intro a
    rw [← hmsg]
    exact getStor_subBal_addBal hsub
  have mcodeAll : ∀ a, (initDevm msg).getCode a = base.getCode a := by
    intro a
    rw [← hmsg]
    change (stmid.addBal cw.toAdr 0).getCode a = _
    rw [State.addBal_getCode, ← hstmid, State.setBal_getCode]
    rfl
  have mlogs : (initDevm msg).logs = [] := by
    change (match (initSevm msg).benvStat.rules.stateGas with
      | none => []
      | some _ => _) = []
    rw [CoveredFork.rules_stateGas_none mfork]
  have morig : ∀ key, getOrigStorVal (initSevm msg) (initSevm msg).currentTarget key =
      (initDevm msg).getStorVal (initSevm msg).currentTarget key := by
    intro key
    rw [mtarget]
    change _ = ((initDevm msg).getStor withdrawalRequestPredeployAddress).get key
    rw [mstor, ← horig key, ← hmsg]
    rfl
  have hrefund := systemFramePost_refund_ge (initSevm msg) (initDevm msg) Mem.empty (fwd - cg)
    morig
  have hld := systemFramePost_logs_deletions (initSevm msg) (initDevm msg) Mem.empty (fwd - cg)
  refine ⟨post, post.gasLeft, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hSt]
    exact run
  · change Blanc.WithdrawalRequest.RepresentsStorage (post.state.get _).stor.get _
    rw [pstate]
    rw [mtarget] at hrep'
    exact hrep'
  · rw [perr, callSpawnParent_error]
    rfl
  · intro a
    rw [Devm.getCode_state, pstate, ← Devm.getCode_state, systemFramePost_getCode, mcodeAll]
  · intro a ha
    change (post.state.get a).stor = _
    rw [pstate]
    change Devm.getStor _ a = _
    rw [systemFramePost_other_storage _ _ _ _ a (by rw [mtarget]; exact Ne.symm ha), mstorAll]
  · rw [← hchild]
    change base.logs ++ _ = base.logs
    rw [hld.1, mlogs, List.append_nil]
  · rw [← hchild]
    change (base.accountsToDelete.union _).isEmpty = _
    rw [hld.2]
    exact adrSet_union_isEmpty _ _ (Std.HashSet.isEmpty_emptyWithCapacity)
  · rw [← hchild]
    change base.refundCounter ≤ base.refundCounter + _
    have h0 : (initDevm msg).refundCounter = 0 := rfl
    rw [h0] at hrefund
    omega

/-- **A user-transaction frame at SYSTEM_ADDRESS drains the queue.**  A message running the
drainer code at SYSTEM_ADDRESS (dynamic, not outermost), into a world where the predeploy is
installed with storage representing `σ` (excess plus count below `2^256`), with enough gas,
executes without error and leaves the predeploy storage representing `system σ`: the
system-path dequeue of up to 16 entries and the count reset, though no system call ran. -/
theorem drain_exec {msg : Msg} {σ : Blanc.WithdrawalRequest.State}
    (hfork : CoveredFork msg.benv.stat.fork)
    (hcode : msg.code = Blanc.Lift.SystemDrainer.code)
    (hsys : msg.currentTarget = systemAddress) (hstatic : msg.isStatic = false)
    (hdepth : msg.depth ≠ 0)
    (hinstalled : msg.benv.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode)
    (hrep : Blanc.WithdrawalRequest.RepresentsStorage
      (msg.benv.state.getStor withdrawalRequestPredeployAddress).get σ)
    (hsum : Blanc.WithdrawalRequest.effectiveExcess σ + σ.count < 2 ^ 256)
    (horig : ∀ key, (msg.benv.stat.origState.getStor withdrawalRequestPredeployAddress).get key =
      (msg.benv.state.getStor withdrawalRequestPredeployAddress).get key)
    (hgas : 427217 ≤ msg.gas) (hlt : msg.gas < 2 ^ 256) :
    ∃ post, exec (initEvm msg) = .ok post ∧ post.error = none ∧
      Blanc.WithdrawalRequest.RepresentsStorage
        (post.getStor withdrawalRequestPredeployAddress).get
        (Blanc.WithdrawalRequest.system σ) ∧
      (∀ a, post.getCode a = msg.benv.state.getCode a) ∧
      (∀ a, a ≠ withdrawalRequestPredeployAddress → post.getStor a = msg.benv.state.getStor a) ∧
      post.logs = [] ∧ post.accountsToDelete.isEmpty = true ∧ 0 ≤ post.refundCounter := by
  obtain ⟨G0, hG0⟩ : ∃ G0, G0 + 15 = (initDevm msg).gasLeft :=
    ⟨msg.gas - 15, by rw [initDevm_gasLeft]; omega⟩
  have hpre := pre_eq_St (pre := initDevm msg) rfl rfl hG0
  obtain ⟨post, G', run, rep, err, pcode, pstor, plogs, pdel, prefund⟩ :=
    drain_call (sevm := initSevm msg) (base := initDevm msg)
    (Gc := G0) (σ := σ) hfork hstatic hdepth hsys drainer_callee hinstalled hrep hsum horig
    (by rw [initDevm_gasLeft] at hG0; omega) (by rw [initDevm_gasLeft] at hG0; omega)
  have hrun : SFunc.RunExact Blanc.Lift.SystemDrainer.cert.prog (initSevm msg)
      (St (initDevm msg) [] Mem.empty (G0 + 15)) Blanc.Lift.SystemDrainer.t_0000_c0
      (.halted (St post [1] Mem.empty G')) := by
    unfold Blanc.Lift.SystemDrainer.t_0000_c0
    refine rx_push0 (by decide) ?_
    refine rx_push0 (by decide) ?_
    refine rx_push0 (by decide) ?_
    refine rx_push0 (by decide) ?_
    refine rx_push0 (by decide) ?_
    refine rx_push rfl (by decide) ?_
    refine rx_gas (by decide) ?_
    exact .next run (.last rfl)
  rw [hpre] at hrun
  obtain ⟨exn⟩ := lift_exact Blanc.Lift.SystemDrainer.cert_check Blanc.Lift.SystemDrainer.jumps_ok
    hcode hfork ⟨Blanc.Lift.SystemDrainer.t_0000_c0, rfl, hrun⟩
  refine ⟨St post [1] Mem.empty G', (exec_iff_exec_eq 0 (initSevm msg) (initDevm msg) _).mp ⟨exn⟩,
    ?_, rep, pcode, pstor, ?_, ?_, ?_⟩
  · change post.error = none
    rw [err]
    rfl
  · change post.logs = []
    rw [plogs]
    have hsg : (initSevm msg).benvStat.rules.stateGas = none :=
      CoveredFork.rules_stateGas_none hfork
    change (match (initSevm msg).benvStat.rules.stateGas with
      | none => []
      | some _ => _) = []
    rw [hsg]
  · change post.accountsToDelete.isEmpty = true
    rw [pdel]
    exact Std.HashSet.isEmpty_emptyWithCapacity
  · change 0 ≤ post.refundCounter
    exact prefund

end Blanc.Lift.WithdrawalRequest.SystemDrain
