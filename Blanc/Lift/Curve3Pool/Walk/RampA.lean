import Blanc.Lift.HistIdentityCall
import Blanc.Lift.Curve3Pool.Walk.RampKit
import Blanc.Lift.WordWindowMemory
import Blanc.Lift.Curve3Pool.Walk.AutoStep

/-!
# `ramp_A(_future_A, _future_time)` on the derivation, with `_A` bridged

The body (`0x4777`): the non-payable guard, `assert msg.sender == self.owner`, the checked
`initial_A_time + MIN_RAMP_TIME ≤ block.timestamp` and `block.timestamp + MIN_RAMP_TIME ≤
_future_time`, `_A()` (inline save of `0x140`), `0 < _future_A < MAX_A`, the change bound (the
checked `_initial_A * MAX_A_CHANGE` or `_future_A * MAX_A_CHANGE`), the four ramp slots written,
and `RampA(_initial_A, _future_A, block.timestamp, _future_time)` logged from `0x1a0`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The decoded arguments `_future_A`, `_future_time`. -/
abbrev rampFA (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [4])
abbrev rampFT (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [0x24])

/-- `MIN_RAMP_TIME`, as pushed. -/
abbrev rampMin : B256 := Bytes.toB256 [0x01, 0x51, 0x80]

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {s : State}

-- SEGMENT: rampAPre
/-- **`ramp_A` up to the bound checks**: the guards and `_A`. -/
theorem xa_rampA_pre (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (h : XAt sevm post 0x4777 (St b [] (vdMem sevm) G) L) :
    sevm.value = 0 ∧ sevm.caller.toB256 = (b.getStor sevm.currentTarget).get ownerSlot ∧
      ((b.getStor sevm.currentTarget).get initialATimeSlot).toNat + rampMin.toNat < 2 ^ 256 ∧
      ¬ sevm.benvStat.time < (b.getStor sevm.currentTarget).get initialATimeSlot + rampMin ∧
      sevm.benvStat.time.toNat + rampMin.toNat < 2 ^ 256 ∧
      ¬ rampFT sevm < sevm.benvStat.time + rampMin ∧
      ∃ (A : B256) (b2 : Devm) (M : Mem) (G2 : Nat), SloadsOnlyH sevm b b2 ∧
        aChk s sevm.benvStat.time.toNat = some A.toNat ∧
        XAt sevm post 0x47ff (St b2 [] M G2) L ∧ VW M [(0x140, A)] := by
  have hV : VW (vdMem sevm) [] := ⟨Words.nil _, vyMem_wf Mem.wf_empty _,
    by rw [vyMem_empty_size]⟩
  xa 3
  xji 0x477d 0x4781 hw
  · xdead  -- 477c JUMPI
  have hval : sevm.value = 0 := B256.eq_of_eqCheck_ne_zero hw
  clear hw
  xa 2
  xw 0x4785 (.reg .sload) ri_sloadF  -- 4784 SLOAD
  xa 3
  xji 0x478b 0x478f hw
  · xdead  -- 478a JUMPI
  have hown := B256.eq_of_eqCheck_ne_zero hw
  clear hw
  xa 2
  xw 0x4793 (.reg .sload) ri_sloadF  -- 4792 SLOAD
  xa 8
  xji 0x47a1 0x47a5 hw
  · xdead  -- 47a0 JUMPI
  have hn0 := (B256.nof_iff_not_add_lt _ _).mpr
    (B256.not_lt_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw))
  clear hw
  xa 12
  xji 0x47b4 0x47b8 hw
  · xdead  -- 47b3 JUMPI
  have ht0 := B256.not_lt_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xa 10
  xji 0x47c8 0x47cc hw
  · xdead  -- 47c7 JUMPI
  have hn1 := (B256.nof_iff_not_add_lt _ _).mpr
    (B256.not_lt_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw))
  clear hw
  xa 13
  xji 0x47dd 0x47e1 hw
  · xdead  -- 47dc JUMPI
  have ht1 := B256.not_lt_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xa 2
  xlu 0x47e6  -- 47e5 MLOAD
  xs 0x47e8 (.push [0x06] (by decide)) ri_push  -- 47e6 PUSH1 0x06
  cvpc 0x47e9  -- 47e8 PC
  xa 2
  xjmp 0xa9  -- 47ed JUMP
  have ha1 : Abstracts ((afterSloadH sevm (afterSloadH sevm b (Bytes.toB256 [4]))
      (Bytes.toB256 [8])).getStor sevm.currentTarget) s := by
    rw [afterSloadH_getStor, afterSloadH_getStor]; exact ha
  obtain ⟨A, b2, M, _, hb2, h, hA, hV1⟩ := xa_vAV hc hcode hfork ha1 hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xa 2
  xsw 0x47f3 0x180  -- 47f2 MSTORE
  xs 0x47f6 (.push [0x01, 0x40] (by decide)) ri_push  -- 47f3 PUSH2 0x0140
  xsw 0x47f7 0x140  -- 47f6 MSTORE
  xs 0x47fa (.push [0x01, 0x80] (by decide)) ri_push  -- 47f7 PUSH2 0x0180
  xl 0x47fb 0x180  -- 47fa MLOAD
  xs 0x47fe (.push [0x01, 0x40] (by decide)) ri_push  -- 47fb PUSH2 0x0140
  xsw 0x47ff 0x140  -- 47fe MSTORE
  simp only [getStorVal_eq, afterSloadH_getStor] at hown hn0 ht0
  refine ⟨hval, by rw [hown]; rfl, hn0, ht0, hn1, ht1, A, b2, _, _,
    (((SloadsOnlyH.refl).sload _).sload _).trans hb2, hA, h, hV.sub ?_⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
  exact .inl hx

-- SEGMENT: rampAOr
/-- **The change bound's second disjunct** (from `0x485e`, the first disjunct's flag `c` on the
stack): the assertion passes when `c ≠ 0` or `_future_A < _initial_A` with the checked
`_future_A * MAX_A_CHANGE ≥ _initial_A`. -/
theorem xa_rampA_or {b2 : Devm} {M : Mem} {A c : B256}
    (hcode : sevm.code = code) (hV : VW M [(0x140, A)])
    (h : XAt sevm post 0x485e (St b2 [c] M G) L) :
    (c ≠ 0 ∨ ((rampFA sevm).toNat < A.toNat ∧ B256.Nofm (rampFA sevm) (Bytes.toB256 [10]) ∧
      ¬ rampFA sevm * Bytes.toB256 [10] < A)) ∧ ∃ G2, XAt sevm post 0x48b0 (St b2 [] M G2) L := by
  xa 3
  xji 0x4864 0x486a hw
  · xs 0x4866 (.push [0x01] (by decide)) ri_push  -- 4864 PUSH1 0x01
    xs 0x4869 (.push [0x48, 0xa6] (by decide)) ri_push  -- 4866 PUSH2 0x48a6
    xjmp 0x48a6  -- 4869 JUMP
    xa 3
    xji 0x48ac 0x48b0 hw2
    · exact absurd hw2 (by decide)
    · exact ⟨.inl (ne_of_eqCheck_eq_zero hw), _, h⟩
  clear hw
  xa 2
  xl 0x486f 0x140  -- 486e MLOAD
  xa 5
  xji 0x4878 0x48a2 hw
  · have hlt := ltCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
    clear hw
    xs 0x487b (.push [0x01, 0x40] (by decide)) ri_push  -- 4878 PUSH2 0x0140
    xl 0x487c 0x140  -- 487b MLOAD
    xa 15
    xji 0x4890 0x4894 hw
    · xdead  -- 488f JUMPI
    have hm := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
    clear hw
    xa 11
    xjmp 0x48a5  -- 48a1 JUMP
    xa 4
    xji 0x48ac 0x48b0 hw
    · xdead  -- 48ab JUMPI
    exact ⟨.inr ⟨hlt, hm, B256.not_lt_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)⟩, _, h⟩
  · xjd 0x48a3  -- 48a2 JUMPDEST
    xa 5
    xji 0x48ac 0x48b0 hw2
    · xdead  -- 48ab JUMPI
    · exact absurd rfl hw2

-- SEGMENT: rampACheck
/-- **The bound checks** (`0x47ff` to `0x48b0`): `0 < _future_A < MAX_A` and the change bound. -/
theorem xa_rampA_check {b2 : Devm} {M : Mem} {A : B256}
    (hcode : sevm.code = code) (hV : VW M [(0x140, A)])
    (h : XAt sevm post 0x47ff (St b2 [] M G) L) :
    0 < (rampFA sevm).toNat ∧ (rampFA sevm).toNat < maxA ∧
      ((A.toNat ≤ (rampFA sevm).toNat ∧ (rampFA sevm).toNat ≤ A.toNat * maxAChange) ∨
        ((rampFA sevm).toNat < A.toNat ∧ A.toNat ≤ (rampFA sevm).toNat * maxAChange)) ∧
      ∃ G2, XAt sevm post 0x48b0 (St b2 [] M G2) L := by
  have h10 : (Bytes.toB256 [10]).toNat = maxAChange := by decide
  xa 6
  xji 0x480a 0x4816 hw
  swap
  · xjd 0x4817  -- 4816 JUMPDEST
    xa 3
    xji 0x481e 0x4822 hw2
    · xdead  -- 481d JUMPI
    · exact absurd rfl hw2
  have hpos := hw
  clear hw
  xa 5
  xjmp 0x4819  -- 4815 JUMP
  xa 2
  xji 0x481e 0x4822 hw
  · xdead  -- 481d JUMPI
  have hmax := ltCheck_ne_zero hw
  clear hw
  xa 2
  xl 0x4827 0x140  -- 4826 MLOAD
  xa 6
  xji 0x4831 0x485b hw
  · have hge := hw
    clear hw
    xs 0x4834 (.push [0x01, 0x40] (by decide)) ri_push  -- 4831 PUSH2 0x0140
    xl 0x4835 0x140  -- 4834 MLOAD
    xa 13
    xji 0x4846 0x484a hw
    · xdead  -- 4845 JUMPI
    have hm := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
    clear hw
    xa 13
    xjmp 0x485e  -- 485a JUMP
    obtain ⟨hor, _, h⟩ := xa_rampA_or hcode hV h
    refine ⟨toNat_lt_of_iszero_gt_eq_zero hpos, hmax, ?_, _, h⟩
    rcases hor with hor | ⟨hl, hm', hn⟩
    · refine .inl ⟨?_, ?_⟩
      · have e := B256.not_lt_of_ltCheck_eq_zero (eq_zero_of_iszero2_eq_zero hge)
        rw [B256.lt_iff_toNat_lt_toNat] at e
        exact Nat.le_of_not_lt e
      · have e := toNat_le_of_iszero_gt_ne_zero hor
        rwa [B256.toNat_mul_eq_of_nofm hm, h10] at e
    · rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_mul_eq_of_nofm hm', h10] at hn
      exact .inr ⟨hl, Nat.le_of_not_lt hn⟩
  · have hlt := hw
    clear hw
    xa 2
    obtain ⟨hor, _, h⟩ := xa_rampA_or hcode hV h
    refine ⟨toNat_lt_of_iszero_gt_eq_zero hpos, hmax, ?_, _, h⟩
    rcases hor with hor | ⟨hl, hm', hn⟩
    · exact absurd rfl hor
    · rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_mul_eq_of_nofm hm', h10] at hn
      exact .inr ⟨hl, Nat.le_of_not_lt hn⟩

/-- The `RampA` topic as pushed. -/
theorem rampA_topic : Bytes.toB256 [0xa2, 0xb7, 0x1e, 0xc6, 0xdf, 0x94, 0x93, 0x00, 0xb5, 0x9a,
    0xab, 0x36, 0xb5, 0x5e, 0x18, 0x96, 0x97, 0xb7, 0x50, 0x11, 0x9d, 0xd3, 0x49, 0xfc, 0xfa, 0x8c,
    0x0f, 0x77, 0x9e, 0x83, 0xc2, 0x54] = topicRampA := by decide

-- SEGMENT: rampATail
/-- **The writes and the log** (`0x48b0` to the `STOP`). -/
theorem xa_rampA_tail {b2 : Devm} {M : Mem} {A : B256}
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    (hV : VW M [(0x140, A)]) (h : XAt sevm post 0x48b0 (St b2 [] M G) L) :
    L = [] ∧
      (∀ x, (post.getStor sevm.currentTarget).get x =
        (((((b2.getStor sevm.currentTarget).set initialASlot A).set futureASlot (rampFA sevm)).set
          initialATimeSlot sevm.benvStat.time).set futureATimeSlot (rampFT sevm)).get x) ∧
      post.logs = b2.logs ++ [⟨sevm.currentTarget, [topicRampA], A.toBytes ++
        (rampFA sevm).toBytes ++ sevm.benvStat.time.toBytes ++ (rampFT sevm).toBytes⟩] ∧
      post.output = b2.output := by
  xa 2
  xl 0x48b5 0x140  -- 48b4 MLOAD
  xs 0x48b7 (.push [0x06] (by decide)) ri_push  -- 48b5 PUSH1 0x06
  xw 0x48b8 (.reg .sstore) ri_sstoreF  -- 48b7 SSTORE
  xa 3
  xw 0x48be (.reg .sstore) ri_sstoreF  -- 48bd SSTORE
  xa 2
  xw 0x48c2 (.reg .sstore) ri_sstoreF  -- 48c1 SSTORE
  xa 3
  xw 0x48c8 (.reg .sstore) ri_sstoreF  -- 48c7 SSTORE
  xs 0x48cb (.push [0x01, 0x40] (by decide)) ri_push  -- 48c8 PUSH2 0x0140
  xl 0x48cc 0x140  -- 48cb MLOAD
  xs 0x48cf (.push [0x01, 0xa0] (by decide)) ri_push  -- 48cc PUSH2 0x01a0
  have hlogwf := hV.wf
  xsw 0x48d0 0x1a0  -- 48cf MSTORE
  xa 3
  xsw 0x48d7 0x1c0  -- 48d6 MSTORE
  xa 2
  xsw 0x48dc 0x1e0  -- 48db MSTORE
  xa 3
  xsw 0x48e3 0x200  -- 48e2 MSTORE
  xa 3
  have hdata := Mem.read_four_word_writes hlogwf 0x1a0 A (rampFA sevm) sevm.benvStat.time
    (rampFT sevm)
  replace h := xa_nextAt (n := .reg (.log 1)) (pc' := 0x490a) (atN hcode (by kernel_rfl))
    (by nofun) (by rfl) h
  obtain ⟨_, s, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_log1 s
  clear s
  obtain ⟨hrun, hL⟩ := xa_halt (l := .stop) (atL hcode (by kernel_rfl)) h
  have hp := (Except.ok.inj hrun).symm
  subst hp hL
  refine ⟨rfl, fun x => ?_, ?_, ?_⟩
  · simp only [St]
    rw [← getStorVal_eq, Devm.getStorVal_setMach, getStorVal_eq, getStor_addLog,
      afterSstoreH_getStor_self, afterSstoreH_getStor_self, afterSstoreH_getStor_self,
      afterSstoreH_getStor_self, slot_06, slot_07, slot_08, slot_09]
  · simp only [St, Devm.setMach_logs]
    rw [Devm.addLog_logs, afterSstoreH_logs, afterSstoreH_logs, afterSstoreH_logs, afterSstoreH_logs,
      rampA_topic, show (Bytes.toB256 [1, 160]).toNat = 0x1a0 from rfl,
      show (Bytes.toB256 [128]).toNat = 128 from rfl]
    exact congrArg (fun z => b2.logs ++ [⟨sevm.currentTarget, [topicRampA], z⟩]) hdata
  · simp only [St, Devm.setMach_output]
    rw [Devm.addLog_output, afterSstoreH_output, afterSstoreH_output, afterSstoreH_output,
      afterSstoreH_output]

/-- **`ramp_A`'s raw effect**, given the certificate's checkedness. -/
theorem rampA_raw_of (hc : Cert.CheckedM code cert mems true) {pre : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRampA)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨_, hx⟩ := xa_vd_rampA hcode hlen hcd hsel hx
  obtain ⟨hval, hown, hn0, ht0, hn1, ht1, A, b2, M, G2, hb2, hA, hx, hV⟩ :=
    xa_rampA_pre hc hcode hfork hck.abs hx
  obtain ⟨hpos, hmax, hbd, _, hx⟩ := xa_rampA_check hcode hV hx
  obtain ⟨hL, hstor, hlogs, hout⟩ := xa_rampA_tail hcode hfork hV hx
  have hdec : decodeCall sevm = .rampA (rampFA sevm).toNat (rampFT sevm).toNat :=
    decodeCall_at (k := 11) rfl hsel hlen
  have hmin : rampMin.toNat = minRampTime := by decide
  have hown' : (quietEnv sevm).caller = s.owner := by
    show sevm.caller.toB256.toNat = _
    rw [hown, hck.abs.owner]
  have ht : (quietEnv sevm).time = sevm.benvStat.time.toNat := rfl
  have hiat : ((pre.getStor sevm.currentTarget).get initialATimeSlot).toNat = s.initialATime :=
    hck.abs.initialATime
  rw [B256.lt_iff_toNat_lt_toNat] at ht0 ht1
  have hst : rampA s (quietEnv sevm) (rampFA sevm).toNat (rampFT sevm).toNat =
      some ⟨{ s with initialA := A.toNat, futureA := (rampFA sevm).toNat,
                     initialATime := sevm.benvStat.time.toNat,
                     futureATime := (rampFT sevm).toNat }, none,
        [.rampA A.toNat (rampFA sevm).toNat sevm.benvStat.time.toNat (rampFT sevm).toNat], []⟩ := by
    unfold rampA
    simp only [Option.bind_eq_bind]
    rw [req, ite_eq_left hown', Option.bind_some, ← hiat, ← hmin, chkAdd_toNat_of_lt hn0,
      Option.bind_some, req, ite_eq_left (show (quietEnv sevm).time ≥ _ from Nat.le_of_not_lt ht0), Option.bind_some, ht,
      chkAdd_toNat_of_lt hn1, Option.bind_some, req, ite_eq_left (Nat.le_of_not_lt ht1),
      Option.bind_some, hA, Option.bind_some, req, ite_eq_left ⟨hpos, hmax⟩, Option.bind_some, req,
      ite_eq_left hbd, Option.bind_some]
  have hstep : step s (quietEnv sevm) (decodeCall sevm) =
      rampA s (quietEnv sevm) (rampFA sevm).toNat (rampFT sevm).toNat := by
    rw [hdec]
    show (if (quietEnv sevm).value = 0 then rampA s (quietEnv sevm) _ _ else none) = _
    rw [show (quietEnv sevm).value = 0 by show sevm.value.toNat = 0; rw [hval]; rfl,
      ite_eq_left rfl]
  rw [hst] at hstep
  refine ⟨quietEnv sevm, _, hstep, ?_⟩
  · refine rawEffect_noChild hL (ramp_storEffect (by rw [hdec]; rfl)
      (fun x => by rw [hstor, hb2.getStor]; rfl) rfl rfl rfl rfl) ?_
      (by rw [hout, hb2.output]; rfl) ?_
    · rw [hlogs, hb2.logs]
      simp only [List.map_cons, List.map_nil, eventLog, word, toB256_toNat]
    · rfl

end

end Blanc.Lift.Curve3Pool
