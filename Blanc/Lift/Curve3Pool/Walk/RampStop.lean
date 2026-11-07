import Blanc.Lift.HistIdentityCall
import Blanc.Lift.Curve3Pool.Walk.RampKit
import Blanc.Lift.Curve3Pool.Walk.AutoStep

/-!
# `stop_ramp_A()` on the derivation, with `_A` bridged

The body (`0x491a`): the non-payable guard, `assert msg.sender == self.owner`, `_A()` (inline
save of `0x140`), the four ramp slots written (`initial_A = future_A = A`,
`initial_A_time = future_A_time = block.timestamp`), and `StopRampA(A, block.timestamp)` logged
from `0x1a0`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The `StopRampA` topic as pushed. -/
theorem stopRamp_topic : Bytes.toB256 [0x46, 0xe2, 0x2f, 0xb3, 0x70, 0x9a, 0xd2, 0x89, 0xf6, 0x2c,
    0xe6, 0x3d, 0x46, 0x92, 0x48, 0x53, 0x6d, 0xbc, 0x78, 0xd8, 0x2b, 0x84, 0xa3, 0xd7, 0xe7, 0x4a,
    0xd6, 0x06, 0xdc, 0x20, 0x19, 0x38] = topicStopRampA := by decide

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {s : State}

-- SEGMENT: stopRampFrame
/-- **The `stop_ramp_A()` frame.** -/
theorem xa_stopRamp (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selStopRampA) (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    sevm.value = 0 ∧ L = [] ∧
      sevm.caller.toB256 = (b.getStor sevm.currentTarget).get ownerSlot ∧
      ∃ A : B256, aChk s sevm.benvStat.time.toNat = some A.toNat ∧
        (∀ x, (post.getStor sevm.currentTarget).get x =
          (((((b.getStor sevm.currentTarget).set initialASlot A).set futureASlot A).set
            initialATimeSlot sevm.benvStat.time).set futureATimeSlot sevm.benvStat.time).get x) ∧
        post.logs = b.logs ++ [⟨sevm.currentTarget, [topicStopRampA],
          A.toBytes ++ sevm.benvStat.time.toBytes⟩] ∧
        post.output = b.output := by
  obtain ⟨_, h⟩ := xa_vd_stopRampA hcode hlen hcd hsel h
  have hV : VW (vdMem sevm) [] := ⟨Words.nil _, vyMem_wf Mem.wf_empty _,
    by rw [vyMem_empty_size]⟩
  xa 3
  xji 0x4920 0x4924 hw
  · xdead
  have hval : sevm.value = 0 := B256.eq_of_eqCheck_ne_zero hw
  clear hw
  xa 2
  xw 0x4928 (.reg .sload) ri_sloadF  -- 4927 SLOAD
  xa 3
  xji 0x492e 0x4932 hw
  · xdead
  have hown := B256.eq_of_eqCheck_ne_zero hw
  clear hw
  xa 2
  xlu 0x4937  -- 4936 MLOAD
  xs 0x4939 (.push [0x06] (by decide)) ri_push  -- 4937 PUSH1 0x06
  cvpc 0x493a  -- 4939 PC
  xa 2
  xjmp 0xa9  -- 493e JUMP
  have ha1 : Abstracts ((afterSloadH sevm b (Bytes.toB256 [4])).getStor sevm.currentTarget) s := by
    rw [afterSloadH_getStor]; exact ha
  obtain ⟨A, b2, M, _, hb2, h, hA, hV1⟩ := xa_vAV hc hcode hfork ha1 hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xa 2
  xsw 0x4944 0x180  -- 4943 MSTORE
  xs 0x4947 (.push [0x01, 0x40] (by decide)) ri_push  -- 4944 PUSH2 0x0140
  xsw 0x4948 0x140  -- 4947 MSTORE
  xs 0x494b (.push [0x01, 0x80] (by decide)) ri_push  -- 4948 PUSH2 0x0180
  xl 0x494c 0x180  -- 494b MLOAD
  xs 0x494f (.push [0x01, 0x40] (by decide)) ri_push  -- 494c PUSH2 0x0140
  xsw 0x4950 0x140  -- 494f MSTORE
  xs 0x4953 (.push [0x01, 0x40] (by decide)) ri_push  -- 4950 PUSH2 0x0140
  xl 0x4954 0x140  -- 4953 MLOAD
  xs 0x4956 (.push [0x06] (by decide)) ri_push  -- 4954 PUSH1 0x06
  xw 0x4957 (.reg .sstore) ri_sstoreF  -- 4956 SSTORE
  xs 0x495a (.push [0x01, 0x40] (by decide)) ri_push  -- 4957 PUSH2 0x0140
  xl 0x495b 0x140  -- 495a MLOAD
  xs 0x495d (.push [0x07] (by decide)) ri_push  -- 495b PUSH1 0x07
  xw 0x495e (.reg .sstore) ri_sstoreF  -- 495d SSTORE
  xa 2
  xw 0x4962 (.reg .sstore) ri_sstoreF  -- 4961 SSTORE
  xa 2
  xw 0x4966 (.reg .sstore) ri_sstoreF  -- 4965 SSTORE
  xs 0x4969 (.push [0x01, 0x40] (by decide)) ri_push  -- 4966 PUSH2 0x0140
  xl 0x496a 0x140  -- 4969 MLOAD
  xs 0x496d (.push [0x01, 0xa0] (by decide)) ri_push  -- 496a PUSH2 0x01a0
  have hlogwf := hV.wf
  xsw 0x496e 0x1a0  -- 496d MSTORE
  xa 2
  xsw 0x4973 0x1c0  -- 4972 MSTORE
  xa 3
  have hdata := Mem.read_two_word_writes_wf' hlogwf (s := 0x1a0) (t := 0x1c0)
    (by decide) A sevm.benvStat.time
  replace h := xa_nextAt (n := .reg (.log 1)) (pc' := 0x499a) (atN hcode (by kernel_rfl))
    (by nofun) (by rfl) h
  obtain ⟨_, s, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_log1 s
  clear s
  obtain ⟨hrun, hL⟩ := xa_halt (l := .stop) (atL hcode (by kernel_rfl)) h
  have hp := (Except.ok.inj hrun).symm
  subst hp hL
  refine ⟨hval, rfl, ?_, A, hA, fun x => ?_, ?_, ?_⟩
  · rw [hown, getStorVal_eq, show Bytes.toB256 [4] = ownerSlot by decide]
  · simp only [St]
    rw [← getStorVal_eq, Devm.getStorVal_setMach, getStorVal_eq, getStor_addLog, afterSstoreH_getStor_self, afterSstoreH_getStor_self, afterSstoreH_getStor_self,
      afterSstoreH_getStor_self, hb2.getStor, afterSloadH_getStor, slot_06, slot_07, slot_08, slot_09]
  · simp only [St, Devm.setMach_logs]
    rw [Devm.addLog_logs, afterSstoreH_logs, afterSstoreH_logs, afterSstoreH_logs, afterSstoreH_logs, hb2.logs,
      afterSloadH_logs, stopRamp_topic, show (Bytes.toB256 [1, 160]).toNat = 416 from rfl,
      show (Bytes.toB256 [64]).toNat = 64 from rfl, hdata]
  · simp only [St, Devm.setMach_output]
    rw [Devm.addLog_output, afterSstoreH_output, afterSstoreH_output, afterSstoreH_output, afterSstoreH_output,
      hb2.output, afterSloadH_output]

/-- The model's `stop_ramp_A` when the caller is the owner. -/
theorem stopRampA_eq {s : State} {e : Env} {a : Nat} (hown : e.caller = s.owner)
    (hA : aChk s e.time = some a) :
    stopRampA s e = some ⟨{ s with initialA := a, futureA := a, initialATime := e.time, futureATime := e.time }, none, [.stopRampA a e.time], []⟩ := by
  simp only [stopRampA, req, hown, hA, ↓reduceIte, Option.bind_eq_bind, Option.bind_some]

/-- **`stop_ramp_A()`'s raw effect**, given the certificate's checkedness. -/
theorem stopRampA_raw_of (hc : Cert.CheckedM code cert mems true) {pre : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selStopRampA)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨hval, hL, hown, A, hA, hstor, hlogs, hout⟩ :=
    xa_stopRamp hc hcode hfork hlen hcd hsel hck.abs hx
  have hdec : decodeCall sevm = .stopRampA := decodeCall_at (k := 12) rfl hsel hlen
  have hown' : (quietEnv sevm).caller = s.owner := by
    show sevm.caller.toB256.toNat = _
    rw [hown, hck.abs.owner]
  have hst := stopRampA_eq (e := quietEnv sevm) hown' hA
  refine ⟨quietEnv sevm, ⟨{ s with initialA := A.toNat, futureA := A.toNat, initialATime := sevm.benvStat.time.toNat, futureATime := sevm.benvStat.time.toNat },
    none, [.stopRampA A.toNat sevm.benvStat.time.toNat], []⟩, ?_, ?_⟩
  · rw [hdec]
    show (if (quietEnv sevm).value = 0 then stopRampA s (quietEnv sevm) else none) = _
    rw [show (quietEnv sevm).value = 0 by show sevm.value.toNat = 0; rw [hval]; rfl,
      ite_eq_left rfl, hst]
    rfl
  · refine rawEffect_noChild hL (ramp_storEffect (by rw [hdec]; rfl) hstor rfl rfl rfl rfl) ?_
      hout rfl
    rw [hlogs]
    simp only [List.map_cons, List.map_nil, eventLog, word, toB256_toNat]

end

end Blanc.Lift.Curve3Pool
