import Blanc.Lift.PackedShaSize
import Blanc.Lift.HistCreate
import Blanc.Lift.CreateSettlementMeta

/-! Constructive exact SHA-256 steps for the flat, undelegated Muir Glacier schedule.
The hash remains symbolic and the actual historical call costs 700 + 84 gas. -/

namespace Blanc.Lift

open Jaune

private theorem shaResume_facts (p c : Devm) (oi : Nat) :
    let post := (((incorporateChildOnSuccess p c c.output).setMach
      ⟨1 :: p.stack, p.memory, p.gasLeft + c.gasLeft, p.stateGas⟩).memWrite
      oi (c.output.take 32))
    post.stack = 1 :: p.stack ∧
    post.memory = p.memory.write oi (c.output.take 32) ∧
    post.gasLeft = p.gasLeft + c.gasLeft ∧
    post.state = c.state ∧
    post.accessedAddresses = p.accessedAddresses.union c.accessedAddresses ∧
    post.accessedStorageKeys = p.accessedStorageKeys.union c.accessedStorageKeys ∧
    post.logs = p.logs ++ c.logs ∧ post.refundCounter = p.refundCounter + c.refundCounter ∧
    post.output = p.output ∧ post.error = p.error ∧ post.returnData = c.output ∧
    post.createdAccounts = c.createdAccounts := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem shaResume_run (p c : Devm) (oi : Nat)
    (hc : c.error = none) (hr : p.stack.length < 1024) :
    Resume.run (.call p oi 32) (.ok c) = .ok
      (((incorporateChildOnSuccess p c c.output).setMach
        ⟨1 :: p.stack, p.memory, p.gasLeft + c.gasLeft, p.stateGas⟩).memWrite
        oi (c.output.take 32)) := by
  rw [Resume.run_call_ok (by rw [hc]; rfl) hr]
  rfl

private theorem shaInit_logs (msg : Msg) (hsg : msg.benv.stat.rules.stateGas = none) :
    (initDevm msg).logs = [] := by
  simp only [initDevm, hsg]
  rfl

private theorem shaRaw_logs (d : Devm) (G : Nat) (out : Bytes) :
    ((d.withGasLeft G).withOutput out).logs = d.logs := rfl

/-- An exact two-word SHA call under real Muir Glacier rules. -/
theorem staticcall_sha_stepMuir {sevm : Sevm} {b : Devm} {iiw oiw : B256} {S : List B256}
    {M : Mem} {G : Nat}
    (hmuir : sevm.benvStat.rules = muirGlacierRules)
    (hcov : memExtsSize M.size [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩] = M.size)
    (hdepth : sevm.depth ≠ 0) (hbound : G + 784 < 2 ^ 256)
    (hroom : S.length < 1024) (hG : 1 ≤ G) :
    ∃ b', ShaCallPostDelete b b' (Bytes.sha256 (M.read iiw.toNat 64).1).toBytes ∧
      Ninst.RunCompiled sevm
        (St b (Nat.toB256 (G + 784) :: 2 :: iiw :: 64 :: oiw :: 32 :: S) M (G + 784))
        (.exec .staticcall)
        (St b' (1 :: S) (M.write oiw.toNat (Bytes.sha256 (M.read iiw.toNat 64).1).toBytes) G) := by
  let X := G + 784
  let mcs := except64th (X - 700)
  let mcc := mcs + 700
  let base := St b S M X
  let p := callSpawnParent base mcc iiw.toNat 64 oiw.toNat 32
  let msg := staticcallSpawnMsg sevm p mcs 2 2 iiw.toNat 64 (b.getCode 2) false
  let cev := initEvm msg
  let raw := (cev.dyna.withGasLeft (mcs - 84)).withOutput
    (Bytes.sha256 cev.sta.data).toBytes
  let child := raw.recordTouch sevm.benvStat.rules true 2
  let post := (((incorporateChildOnSuccess p child child.output).setMach
    ⟨1 :: p.stack, p.memory, p.gasLeft + child.gasLeft, p.stateGas⟩).memWrite
    oiw.toNat (child.output.take 32))
  have hsplit : calculateMsgCallGas 0 (Nat.toB256 X).toNat X 0 700 = (mcc, mcs) := by
    rw [toNat_toB256' hbound]
    unfold calculateMsgCallGas
    rw [ite_eq_right (by omega)]
    simp only [Nat.sub_zero, ↓reduceIte, Nat.add_zero]
    rw [Nat.min_eq_right (by unfold except64th; omega)]
  have hcross : mcc ≤ X := by dsimp only [mcc, mcs, X]; unfold except64th; omega
  have hfund : 84 ≤ mcs := by dsimp only [mcs, X]; unfold except64th; omega
  have hgas : X - mcc + (mcs - 84) = G := by dsimp only [mcc, X]; omega
  have hext : base.extCost [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩] = 0 :=
    Devm.extCost_covered hcov
  have hpMem : p.memory = M := by
    change M.extends [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩] = M
    exact Mem.extends_covered hcov
  have hstep : Xinst.step sevm
      (St b (Nat.toB256 X :: 2 :: iiw :: 64 :: oiw :: 32 :: S) M X) .staticcall =
        .spawn (Frame.ofCall msg) (.call p oiw.toNat 32) := by
    have hsg : muirGlacierRules.stateGas = none := rfl
    have hacc : muirGlacierRules.access = .flat istanbulAccessGas := rfl
    have hdel : muirGlacierRules.delegationEnabled = false := rfl
    simp only [Xinst.step, hmuir, hsg, hacc]
    rw [show (St b (Nat.toB256 X :: 2 :: iiw :: 64 :: oiw :: 32 :: S) M X).pop =
      .ok (Nat.toB256 X, St b (2 :: iiw :: 64 :: oiw :: 32 :: S) M X) from rfl]
    simp only [Except.bind_ok]
    rw [show (St b (2 :: iiw :: 64 :: oiw :: 32 :: S) M X).popToAdr =
      .ok ((2 : Adr), St b (iiw :: 64 :: oiw :: 32 :: S) M X) from rfl]
    simp only [Except.bind_ok]
    rw [show (St b (iiw :: 64 :: oiw :: 32 :: S) M X).popToNat =
      .ok (iiw.toNat, St b (64 :: oiw :: 32 :: S) M X) from rfl]
    simp only [Except.bind_ok]
    rw [show (St b (64 :: oiw :: 32 :: S) M X).popToNat =
      .ok (64, St b (oiw :: 32 :: S) M X) from rfl]
    simp only [Except.bind_ok]
    rw [show (St b (oiw :: 32 :: S) M X).popToNat =
      .ok (oiw.toNat, St b (32 :: S) M X) from rfl]
    simp only [Except.bind_ok]
    rw [show (St b (32 :: S) M X).popToNat = .ok (32, base) from rfl]
    simp only [Except.bind_ok, ForkRules.accessDelegation_disabled hdel,
      hext, show istanbulAccessGas.call = 700 from rfl, Nat.add_zero]
    rw [show base.gasLeft = X from rfl, hsplit]
    rw [chargeGas_eq_ok hcross]
    simp only [Except.bind_ok]
    rw [genericCall.step_spawn hdepth]
    rfl
  have hbt : msg.benvAfterTransfer = .ok msg.benv := Msg.benvAfterTransfer_of_value_zero rfl
  have hpre : (!((msg.withBenv msg.benv).disablePrecompiles) &&
      decide ((msg.withBenv msg.benv).benv.stat.rules.isPrecomp 2)) = true := by
    change decide (sevm.benvStat.rules.isPrecomp 2) = true
    rw [hmuir]; rfl
  have hlen : (initEvm (msg.withBenv msg.benv)).sta.data.length = 64 := by
    change (p.memory.data.sliceD iiw.toNat 64 0).length = 64
    rw [Array.sliceD_eq_map, List.length_map, List.length_range]
  have henterRaw := Frame.enter_sha256_of_length_64 (f := Frame.ofCall msg)
    hbt (by rfl) hpre hlen hfund
  have hsettle : (Frame.ofCall msg).settle (.ok raw) = .ok child := by
    rw [Frame.settle_eq_settleMsg_handleErrorWith, executeCode.handleErrorWith_ok]
    simp only [Frame.settleMsg, Frame.ofCall, Bool.false_eq_true, ↓reduceIte,
      processMessage.settle, Except.bind_ok, show raw.error = none from rfl, Option.isSome_none]
    rfl
  have henter : (Frame.ofCall msg).enter = .done (.ok child) := by
    change (Frame.ofCall msg).enter = .done ((Frame.ofCall msg).settle (.ok raw)) at henterRaw
    rwa [hsettle] at henterRaw
  have hres : Resume.run (.call p oiw.toNat 32) (.ok child) = .ok post :=
    shaResume_run p child _ (by rw [Devm.recordTouch_error]; rfl) (by exact hroom)
  have hrun := Ninst.runCompiled_exec_doneFrame hstep henter hres
  obtain ⟨hst, hmem0, hgas0, hstate, haddr0, hkeys0, hlogs0, hrefund0,
    hout0, herr0, hrd0, hcreated0⟩ := shaResume_facts p child oiw.toNat
  have houtput : child.output = (Bytes.sha256 (M.read iiw.toNat 64).1).toBytes := by
    rw [Devm.recordTouch_output]
    change (Bytes.sha256 (p.memory.data.sliceD iiw.toNat 64 0)).toBytes = _
    rw [hpMem]; rfl
  have htake : child.output.take 32 = child.output := by
    rw [houtput, ← B256.length_toBytes (Bytes.sha256 (M.read iiw.toNat 64).1), List.take_length]
  have hmem : post.memory = M.write oiw.toNat (Bytes.sha256 (M.read iiw.toNat 64).1).toBytes := by
    rw [hmem0]
    rw [htake, houtput, hpMem]
  have hpostGas : post.gasLeft = G := by
    rw [hgas0]
    have hcGas : child.gasLeft = mcs - 84 := rfl
    rw [hcGas, show p.gasLeft = X - mcc from rfl]
    exact hgas
  have haddr : post.accessedAddresses = b.accessedAddresses := by
    rw [haddr0]
    have hc : child.accessedAddresses = raw.accessedAddresses := rfl
    have hr : raw.accessedAddresses = p.accessedAddresses := rfl
    rw [hc, hr, hashSet_union_self]
    rfl
  have hkeys : post.accessedStorageKeys = b.accessedStorageKeys := by
    rw [hkeys0]
    have hc : child.accessedStorageKeys = raw.accessedStorageKeys := rfl
    have hr : raw.accessedStorageKeys = p.accessedStorageKeys := rfl
    rw [hc, hr, hashSet_union_self]
    rfl
  have hstor : ∀ a, Devm.getStor post a = Devm.getStor b a := by
    intro a
    change (post.state.get a).stor = _
    rw [hstate]
    rw [Devm.recordTouch_state]; rfl
  have hcode : ∀ a, post.getCode a = b.getCode a := by
    intro a
    change post.state.getCode a = _
    rw [hstate]
    rw [Devm.recordTouch_state]; rfl
  have hlogs : post.logs = b.logs := by
    rw [hlogs0]
    have hc : child.logs = raw.logs := rfl
    have hr : raw.logs = [] := by
      rw [shaRaw_logs]
      change (initDevm msg).logs = []
      exact shaInit_logs msg (by change sevm.benvStat.rules.stateGas = none; rw [hmuir]; rfl)
    rw [hc, hr, List.append_nil]
    rfl
  have hrefund : post.refundCounter = b.refundCounter := by
    rw [hrefund0]
    have hc : child.refundCounter = 0 := rfl
    rw [hc, Int.add_zero]
    rfl
  have hworld : ShaCallPost b post (Bytes.sha256 (M.read iiw.toNat 64).1).toBytes :=
    ⟨hstor, hcode, haddr, hkeys, hlogs, hout0, herr0,
      hrd0.trans houtput, hcreated0, hrefund⟩
  have hdelete : post.accountsToDelete = b.accountsToDelete := by
    have hpost : post.accountsToDelete = p.accountsToDelete.union child.accountsToDelete :=
      shaResume_accountsToDelete p child oiw.toNat
    have hchild : child.accountsToDelete = p.accountsToDelete := by
      rw [recordTouch_accountsToDelete]
      change (if sevm.benvStat.rules.settle.selfdestructRefund = 0 then
        .emptyWithCapacity else p.accountsToDelete) = p.accountsToDelete
      rw [hmuir]
      rfl
    rw [hpost, hchild, hashSet_union_self]
    rfl
  refine ⟨post, ⟨hworld, hdelete⟩, ?_⟩
  have hp := St.self (d := post) (hst.trans (by rw [show p.stack = S from rfl])) hmem
  rw [hpostGas] at hp
  rw [← hp]
  exact hrun

section HistoricalSite
variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm}
  {R : List B256} {M : Mem} {G : Nat} {e0 e1 r0 r1 : UInt8} {k : Nat} {X T : SFunc}
  {c0 c1 v0 v1 : UInt8} {fail1 fail2 : SFunc}

/-- Copy/merge/SHA site at its real Muir Glacier cost, retaining the symbolic digest. -/
theorem copy_shaNMuir_gen {img : Bytes} {n s d : Nat} {w1 w2 x1 x3 x4 : B256} {X : SFunc}
    (hk : fs[k]? = some (mcpyTreeN e0 e1 r0 r1 k
      (mergeTreeN (shaCallTree c0 c1 v0 v1 fail1 fail2 T))))
    (hkC : k ∉ C)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = n) (hn : n % 32 = 0)
    (hdn : d ≤ n) (hsd : s + 64 = d) (hd32 : d % 32 = 0) (hd96 : 96 ≤ s)
    (hdb : d + 1000 < 2 ^ 256) (hfp : img.sliceD 64 32 0 = (Nat.toB256 d).toBytes)
    (hw1 : img.sliceD s 32 0 = w1.toBytes) (hw2 : img.sliceD (s + 32) 32 0 = w2.toBytes)
    (hR : R.length < 900)
    (hmuir : sevm.benvStat.rules = muirGlacierRules) (hdepth : sevm.depth ≠ 0)
    (hG : G + 846 < 2 ^ 256) :
    ∃ b' M', ShaCallPostDelete b b' (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' (shaImg img d w1 w2) ∧ M'.size = max n (d + 96) ∧
      ∀ r, SFunc.RunExactCut fs sevm C (St b' (Nat.toB256 32 :: Nat.toB256 d :: R) M' G) T r →
      SFunc.RunExactCut fs sevm C
        (St b (Nat.toB256 s :: Nat.toB256 d :: Nat.toB256 64 :: Nat.toB256 64 :: x1 ::
          Nat.toB256 d :: x3 :: x4 :: 2 :: R) M
          (G + (1207 + (calculateMemoryGasCost (max n (d + 96)) - calculateMemoryGasCost n))))
        (mcpyTreeN e0 e1 r0 r1 k X) r := by
  set n1 := max n (d + 32) with hn1
  set n2 := max n (d + 64) with hn2
  set n3 := max n (d + 96) with hn3
  have m3 := calculateMemoryGasCost_mono (show n ≤ n1 by omega)
  have m4 := calculateMemoryGasCost_mono (show n1 ≤ n2 by omega)
  have m5 := calculateMemoryGasCost_mono (show n2 ≤ n3 by omega)
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have hw1' : (M.read s 32).1 = w1.toBytes := by rw [hr.read, hw1]
  set M5 := M.write d (M.read s 32).1 with hM5
  have hwf5 : Mem.Wf M5 := hwf.write _ _
  have hr5 : Mem.Reads M5 (Bytes.writeAt img d w1.toBytes) := by
    rw [hM5, hw1']; exact hr.write hwf _ _
  have hs5 : M5.size = n1 := by
    rw [hM5, hw1', Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hw2' : (M5.read (s + 32) 32).1 = w2.toBytes := by
    rw [hr5.read, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hw2]
  set M6 := M5.write (d + 32) (M5.read (s + 32) 32).1 with hM6
  have hwf6 : Mem.Wf M6 := hwf5.write _ _
  have hr6 : Mem.Reads M6 (copyImg2 img d w1 w2) := by
    rw [hM6, hw2']; exact hr5.write hwf5 _ _
  have hs6 : M6.size = n2 := by
    rw [hM6, hw2', Mem.size_write_word_aligned (by omega) (by omega)]; omega
  set M7 := (M6.read (d + 64) 32).2.write (d + 64) (M6.read (d + 64) 32).1 with hM7
  have hs6' : (M6.read (d + 64) 32).2.size = n3 := by
    rw [read_ext_size hs6 (by omega) (by omega)]; omega
  have hwf7 : Mem.Wf M7 := (hwf6.extend _ _).write _ _
  have hr7 : Mem.Reads M7 (copyImg2 img d w1 w2) := by
    rw [hM7, hr6.read]
    exact Mem.Reads.write_self (hwf6.extend _ _) (hr6.extend _ _) _
  have hs7 : M7.size = n3 := by
    rw [hM7, ← toBytes_read, Mem.size_write_word_aligned (by omega) (by omega), hs6']; omega
  have hin : (M7.read d 64).1 = w1.toBytes ++ w2.toBytes := by
    rw [hr7.read, copyImg2_input]
  have hF : (Nat.toB256 d).toNat = d := toNat_toB256' (by omega)
  obtain ⟨b', hpost, hstep⟩ := staticcall_sha_stepMuir (sevm := sevm) (b := b)
    (iiw := Nat.toB256 d) (oiw := Nat.toB256 d) (S := Nat.toB256 (d + 64) :: 2 :: R)
    (M := M7) (G := G + 62)
    hmuir (by rw [hF, hs7]; exact memExtsSize_two_covered (by omega) (by omega) (by omega))
    hdepth (by omega) (by simp only [List.length_cons]; omega) (by omega)
  rw [hF, hin] at hpost hstep
  set M8 := M7.write d (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes with hM8
  have hwf8 : Mem.Wf M8 := hwf7.write _ _
  have hr8 : Mem.Reads M8 (shaImg img d w1 w2) := hr7.write hwf7 d _
  have hs8 : M8.size = n3 := by
    rw [hM8, Mem.size_write_word_aligned (by omega) (by omega), hs7]; omega
  have hw7 : (copyImg2 img d w1 w2).sliceD 64 32 0 = (Nat.toB256 d).toBytes := by
    rw [copyImg2_word64 (by omega), hfp]
  have hw8 : (shaImg img d w1 w2).sliceD 64 32 0 = (Nat.toB256 d).toBytes := by
    rw [shaImg_out (by omega), hfp]
  have hrd : b'.returnData.length.toB256 = Nat.toB256 32 := by
    rw [hpost.returnData, B256.length_toBytes]
  refine ⟨b', M8, hpost, hwf8, hr8, hs8, fun r kont => ?_⟩
  rw [show G + (1207 + (calculateMemoryGasCost n3 - calculateMemoryGasCost n)) =
    G + 62 + 784 + 50
      + (121 + (3 + (calculateMemoryGasCost n3 - calculateMemoryGasCost n2))) + 23
      + (79 + (3 + (calculateMemoryGasCost n2 - calculateMemoryGasCost n1)))
      + (79 + (3 + (calculateMemoryGasCost n1 - calculateMemoryGasCost n))) by omega]
  -- the copy: two passes and the exit test
  refine mcpyN_iter (s := s) (d := d) (l := 64) (n := n) (n' := n1)
    (by omega) (by omega) hs (by omega) hn (by omega) (by omega) (by omega) (by omega)
    (by simp only [List.length_cons]; omega) hk hkC ?_
  refine mcpyN_iter (s := s + 32) (d := d + 32) (l := 32) (n := n1) (n' := n2)
    (by omega) (by omega) hs5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp only [List.length_cons]; omega) hk hkC ?_
  refine mcpyN_exit (s := s + 64) (d := d + 64) (l := 0) (by omega) (by simp only [List.length_cons]; omega) ?_
  refine mergeN0 (s := s + 64) (d := d + 64) (n := n2) (n' := n3) hs6 (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by simp only [List.length_cons]; omega) ?_
  -- the call
  unfold shaCallTree
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 d) ?_
    (by rw [h40]; exact read_word hr7 64 hw7) ?_ (by simp only [List.length_cons]; omega) ?_
  · rw [h40]; exact charge_covered hs7 (by omega) (by omega)
  · rw [h40]; exact read_covered hs7 (by omega) (by omega)
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_swap (n := 3) rfl ?_
  refine rxc_add' (add_toB256' (c := d + 64) (by omega) (by omega)) (by simp only [List.set_cons_zero, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rxc_swap (n := 4) rfl ?_
  refine rxc_pop ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_dup (n := 0) rfl (by simp only [List.set_cons_zero, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp only [List.set_cons_zero, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rxc_sub' (sub_toB256' (c := 64) (by omega) (by omega) (by omega)) (by simp only [List.set_cons_zero, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.set_cons_zero, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rxc_dup (n := 5) rfl (by simp only [List.set_cons_zero, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rxc_gas (by simp only [List.set_cons_zero, List.set_cons_succ, List.length_cons]; omega) ?_
  refine .next hstep ?_
  refine rxc_iszero (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_branch_succ (by decide) ?_
  refine rxc_dest ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_push rfl (by omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 d) ?_
    (by rw [h40]; exact read_word hr8 64 hw8) ?_ (by omega) ?_
  · rw [h40]; exact charge_covered hs8 (by omega) (by omega)
  · rw [h40]; exact read_covered hs8 (by omega) (by omega)
  refine rxc_returndatasize (by simp only [List.length_cons]; omega) ?_
  rw [hrd]
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_lt (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rxc_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_branch_succ (by decide) ?_
  exact kont


/-- **Copy, merge and call**: from the copy loop's head with two words `w1`, `w2` at `s` and
`s + 0x20` to be copied to the free pointer `d = s + 0x40`, the two passes (the first inlined,
the second through entry `k`), the exit test, the merge, and the precompile call over the
copied 64 bytes with its checks: `copy_shaNMuir_gen` when memory ends by `d + 0x20`.  1207 gas and
the expansion to `d + 0x60`.  The stack under the
copy's operands carries the length `0x40`, three words the tail discards around the free pointer `d`, and the
precompile's address.  The successor world is `ShaCallPost`-related, and the continuation `T` starts with
the returned size and `d` on the stack. -/
theorem copy_shaNMuir {img : Bytes} {n s d : Nat} {w1 w2 x1 x3 x4 : B256}
    (hk : fs[k]? = some (mcpyTreeN e0 e1 r0 r1 k
      (mergeTreeN (shaCallTree c0 c1 v0 v1 fail1 fail2 T))))
    (hkC : k ∉ C)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = n) (hn : n % 32 = 0)
    (hdn : d ≤ n) (hnd : n ≤ d + 32) (hsd : s + 64 = d) (hd32 : d % 32 = 0) (hd96 : 96 ≤ s)
    (hdb : d + 1000 < 2 ^ 256) (hfp : img.sliceD 64 32 0 = (Nat.toB256 d).toBytes)
    (hw1 : img.sliceD s 32 0 = w1.toBytes) (hw2 : img.sliceD (s + 32) 32 0 = w2.toBytes)
    (hR : R.length < 900)
    (hmuir : sevm.benvStat.rules = muirGlacierRules) (hdepth : sevm.depth ≠ 0)
    (hG : G + 846 < 2 ^ 256) :
    ∃ b' M' img', ShaCallPostDelete b b' (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' img' ∧ M'.size = d + 96 ∧
      img'.sliceD 64 32 0 = (Nat.toB256 d).toBytes ∧
      img'.sliceD d 32 0 = (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes ∧
      ∀ r, SFunc.RunExactCut fs sevm C (St b' (Nat.toB256 32 :: Nat.toB256 d :: R) M' G) T r →
      SFunc.RunExactCut fs sevm C
        (St b (Nat.toB256 s :: Nat.toB256 d :: Nat.toB256 64 :: Nat.toB256 64 :: x1 ::
          Nat.toB256 d :: x3 :: x4 :: 2 :: R) M
          (G + (1207 + (calculateMemoryGasCost (d + 96) - calculateMemoryGasCost n))))
        (mcpyTreeN e0 e1 r0 r1 k (mergeTreeN (shaCallTree c0 c1 v0 v1 fail1 fail2 T))) r := by
  obtain ⟨b', M', hpost, hwf', hr', hs', hrun⟩ := copy_shaNMuir_gen (X := mergeTreeN
    (shaCallTree c0 c1 v0 v1 fail1 fail2 T)) (x1 := x1) (x3 := x3) (x4 := x4) (R := R) (G := G)
    hk hkC hwf hr hs hn hdn hsd hd32 hd96 hdb hfp hw1 hw2 hR hmuir hdepth hG
  have hmax : max n (d + 96) = d + 96 := by omega
  refine ⟨b', M', shaImg img d w1 w2, hpost, hwf', hr', by rw [hs', hmax],
    (shaImg_out (d := d) (start := 64) (len := 32) (by omega)).trans hfp, shaImg_digest, fun r kont => ?_⟩
  have hc := hrun r kont
  rwa [hmax] at hc

/-- **`sha256(abi.encodePacked(a, b))`** with `b` on top of `a` (and the precompile's address
`2` below them), the free pointer at `f` (word-aligned, past the scratch words) and memory of
size `n ≤ f + 0x60`: the packing, then `copy_shaNMuir` from `f + 0x20` to `f + 0x60`.  1336 gas and
the expansion to `f + 0xc0`. -/
theorem packed_sha_pairNMuir {img : Bytes} {n f : Nat} {a bw : B256}
    (hk : fs[k]? = some (mcpyTreeN e0 e1 r0 r1 k
      (mergeTreeN (shaCallTree c0 c1 v0 v1 fail1 fail2 T))))
    (hkC : k ∉ C)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = n) (hn : n % 32 = 0)
    (h96 : 96 ≤ n) (hnf : n ≤ f + 96) (hf32 : f % 32 = 0) (hf96 : 96 ≤ f)
    (hfb : f + 2000 < 2 ^ 256) (hfp : img.sliceD 64 32 0 = (Nat.toB256 f).toBytes)
    (hR : R.length < 900)
    (hmuir : sevm.benvStat.rules = muirGlacierRules) (hdepth : sevm.depth ≠ 0)
    (hG : G + 846 < 2 ^ 256) :
    ∃ b' M' img', ShaCallPostDelete b b' (hashPairBytes a bw) ∧ Mem.Wf M' ∧
      Mem.Reads M' img' ∧ M'.size = f + 192 ∧
      img'.sliceD 64 32 0 = (Nat.toB256 (f + 96)).toBytes ∧
      img'.sliceD (f + 96) 32 0 = (Bytes.sha256 (a.toBytes ++ bw.toBytes)).toBytes ∧
      ∀ r, SFunc.RunExactCut fs sevm C
        (St b' (Nat.toB256 32 :: Nat.toB256 (f + 96) :: R) M' G) T r →
      SFunc.RunExactCut fs sevm C
        (St b (bw :: a :: 2 :: R) M
          (G + (1336 + (calculateMemoryGasCost (f + 192) - calculateMemoryGasCost n))))
        (pack2Tree (mcpyTreeN e0 e1 r0 r1 k (mergeTreeN (shaCallTree c0 c1 v0 v1 fail1 fail2 T))))
        r := by
  set s1 := max n (f + 64) with hs1_def
  have m1 := calculateMemoryGasCost_mono (show n ≤ s1 by omega)
  have m2 := calculateMemoryGasCost_mono (show s1 ≤ f + 96 by omega)
  have m3 := calculateMemoryGasCost_mono (show f + 96 ≤ f + 192 by omega)
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  set M1 := M.write (f + 32) a.toBytes with hM1
  set M2 := M1.write (f + 64) bw.toBytes with hM2
  set M3 := M2.write f (Nat.toB256 64).toBytes with hM3
  set M4 := M3.write 64 (Nat.toB256 (f + 96)).toBytes with hM4
  have hs1 : M1.size = s1 := by
    rw [hM1, Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hs2 : M2.size = f + 96 := by
    rw [hM2, Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hs3 : M3.size = f + 96 := by
    rw [hM3, Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hs4 : M4.size = f + 96 := by
    rw [hM4, Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hwf1 : Mem.Wf M1 := hwf.write _ _
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hwf3 : Mem.Wf M3 := hwf2.write _ _
  have hwf4 : Mem.Wf M4 := hwf3.write _ _
  have hr1 := hr.write hwf (f + 32) a.toBytes
  have hr2 := hr1.write hwf1 (f + 64) bw.toBytes
  have hr3 := hr2.write hwf2 f (Nat.toB256 64).toBytes
  have hr4 : Mem.Reads M4 (packImg img f a bw) := hr3.write hwf3 64 _
  have hfp2 : (Bytes.writeAt (Bytes.writeAt img (f + 32) a.toBytes) (f + 64)
      bw.toBytes).sliceD 64 32 0 = (Nat.toB256 f).toBytes := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hfp]
  obtain ⟨b', M', img', hpost, hwf', hr', hs', hw', hh', hrun⟩ :=
    copy_shaNMuir (fs := fs) (sevm := sevm) (C := C) (b := b) (R := R) (M := M4) (G := G)
      (T := T) (fail1 := fail1) (fail2 := fail2) (n := f + 96) (s := f + 32) (d := f + 96)
      (x1 := Nat.toB256 (f + 32)) (x3 := Nat.toB256 (f + 96))
      (x4 := Nat.toB256 f)
      hk hkC hwf4 hr4 hs4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (packImg_word64 hf96) (packImg_a hf96) (packImg_b hf96) hR hmuir hdepth hG
  refine ⟨b', M', img', hpost, hwf', hr', by omega, hw', hh', fun r kont => ?_⟩
  have hc := hrun r kont
  rw [show G + (1336 + (calculateMemoryGasCost (f + 192) - calculateMemoryGasCost n)) =
    G + (1207 + (calculateMemoryGasCost (f + 96 + 96) - calculateMemoryGasCost (f + 96))) + 90
      + (3 + (calculateMemoryGasCost (f + 96) - calculateMemoryGasCost s1)) + 12
      + (3 + (calculateMemoryGasCost s1 - calculateMemoryGasCost n)) + 21 by
    rw [show f + 96 + 96 = f + 192 by omega]; omega]
  unfold pack2Tree
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 f) ?_ (by rw [h40]; exact read_word hr 64 hfp) ?_
    (by simp only [List.length_cons]; omega) ?_
  · rw [h40]; exact charge_covered hs hn (by omega)
  · rw [h40]; exact read_covered hs hn (by omega)
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_add' (push20_add (a := f) (by omega)) (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_mstore (M' := M1) ?_ (by rw [toNat_toB256' (by omega)]) ?_
  · rw [toNat_toB256' (by omega), charge_word hs hn (by omega)]
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_add' (push20_add' (a := f + 32) (c := f + 64) rfl (by omega)) (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_mstore (M' := M2) ?_ (by rw [toNat_toB256' (by omega)]) ?_
  · rw [toNat_toB256' (by omega), charge_word hs1 (by omega) (by omega),
      show max s1 (f + 64 + 32) = f + 96 by omega]
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_add' (push20_add' (a := f + 64) (c := f + 96) rfl (by omega)) (by simp only [List.length_cons]; omega) ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_push rfl (by simp only [List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 f) ?_
    (by rw [h40]; exact read_word hr2 64 hfp2) ?_ (by simp only [List.set_cons_zero, List.length_cons]; omega) ?_
  · rw [h40]; exact charge_covered hs2 (by omega) (by omega)
  · rw [h40]; exact read_covered hs2 (by omega) (by omega)
  refine rxc_push rfl (by simp only [List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp only [List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_sub' (sub_toB256' (c := 96) (by omega) (by omega) (by omega)) (by simp only [List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_sub' (v := Nat.toB256 64) (by decide) (by simp only [List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_mstore (c := 3) (M' := M3) ?_ (by rw [toNat_toB256' (by omega)]) ?_
  · rw [toNat_toB256' (by omega)]; exact charge_covered hs2 (by omega) (by omega)
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_push rfl (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  refine rxc_mstore (c := 3) (M' := M4) ?_ (by rw [h40]) ?_
  · rw [h40]; exact charge_covered hs3 (by omega) (by omega)
  refine rxc_push rfl (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 (f + 96)) ?_
    (by rw [h40]; exact read_word hr4 64 (packImg_word64 hf96)) ?_ (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  · rw [h40]; exact charge_covered hs4 (by omega) (by omega)
  · rw [h40]; exact read_covered hs4 (by omega) (by omega)
  refine rxc_dup (n := 0) rfl (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 64) ?_
    (by rw [toNat_toB256' (by omega)]; exact read_word hr4 f (packImg_len hf96)) ?_
    (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  · rw [toNat_toB256' (by omega)]; exact charge_covered hs4 (by omega) (by omega)
  · rw [toNat_toB256' (by omega)]; exact read_covered hs4 (by omega) (by omega)
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_push rfl (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  refine rxc_add' (push20_add (a := f) (by omega)) (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_dup (n := 0) rfl (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp only [List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  exact hc

end HistoricalSite

end Blanc.Lift
