import Blanc.Lift.CurveCoins.UsdtLocality
import Blanc.Lift.CurveCoins.ApprovalLog

/-!
# USDT: `Approval` from `approve`, and the logs of the owner's powers

Laws a reader's `eth_getLogs` check rests on, per frame of the certified code:

* `frame_rows_raised_logs`: a frame, not deprecated, that raises a tracked allowance row from empty logs `Approval`;
* `confiscates_logs`, `confiscates_listed`: `destroyBlackFunds` on `h` logs `DestroyedBlackFunds(h, _)` and finds `h` listed;
* `deprecate_logs`, `addBlackList_logs`: those powers log;
* `frame_flag_keep`: only `deprecate` writes slot 10.

The three owner events are `LOG1` with the address in data, not a topic, so a reader filters by topic and reads the data.
`Mem.Wf F.pre.memory` is the same premise as `frame_balanceOf_answer`'s: an entered frame's memory is empty.
-/

namespace Blanc.Lift.CurveCoins.Usdt

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdt Blanc.Lift.WriteSite Blanc.ExecutionTrace

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- `Approval`, after `approve`'s `require`. -/
theorem approve_tail_log {c n v sp ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (h : SFunc.RunCut cert.prog sevm [] (St b (c :: n :: v :: sp :: ret :: S) M G) t_20b4_c9 (Seg.done o)) :
    ∃ (b₀ : Devm) (data : Bytes) (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b₀ ⟨sevm.currentTarget, [approvalTopic, sevm.caller.toB256, sp.toAdr.toB256], data⟩)
        S M' G') := by
  repeat ustep h
  ibranch h c1
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  simp only [ff20_and_word, toAdr_toB256] at e
  rw [approvalTopic_bytes] at e
  exact ⟨_, _, _, _, Seg.done.inj e⟩

/-- **Entry 54, `StandardToken.approve`.** -/
theorem e54_log {v sp ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (v :: sp :: ret :: S) M G) t_200e_c54 o) :
    ∃ (b₀ : Devm) (data : Bytes) (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b₀ ⟨sevm.currentTarget, [approvalTopic, sevm.caller.toB256, sp.toAdr.toB256], data⟩)
        S M' G') := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ubranchTo h c2
  · iterate 40 ustep h
    exact approve_tail_log fork h
  · exact approve_tail_log fork h

/-- **Entry 19, `TetherToken.approve`, not deprecated.** -/
theorem e19_log {v sp ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (hdep : flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (run : SFunc.Run cert.prog sevm (St b (v :: sp :: ret :: S) M G) t_0b73_c19 o) :
    ∃ (b₀ : Devm) (data : Bytes) (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b₀ ⟨sevm.currentTarget, [approvalTopic, sevm.caller.toB256, sp.toAdr.toB256], data⟩)
        S M' G') := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  useg h
  rw [lit10] at h
  have h' := ric_branch h
  clear h
  rcases h' with ⟨c3, _, h⟩ | ⟨c3, _, h⟩
  · exfalso
    rw [show (Bytes.toB256 [255] &&& (Devm.getStor b sevm.currentTarget).get 10 /
      B256.bexp (Bytes.toB256 [1, 0]) (Bytes.toB256 [20])) = 0 from hdep] at c3
    exact absurd c3 (by decide)
  repeat ustep h
  obtain ⟨_, ⟨_, hc, h⟩ | ⟨_, hc, -⟩⟩ := ric_call (k := 54) (g := t_200e_c54) rfl h
  on_goal 2 => obtain ⟨_, _, _, _, e⟩ := e54_log fork hc; cases e
  obtain ⟨b₀, data, M', G', e⟩ := e54_log fork hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨_, _, _, _, Seg.done.inj e⟩

/-- **A committed `approve`, not deprecated, logs `Approval` with its caller.** -/
theorem frame_approve_logs {post : Devm} (fork : HistFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (hdep : flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    ∃ l ∈ post.logs, l.address = sevm.currentTarget ∧
      l.topics.take 2 = [approvalTopic, sevm.caller.toB256] := by
  have h := run.cut
  clear run
  iterate 7 ustep h
  ibranch h c0
  iterate 7 ustep h
  rw [legacy_selector_word, sel] at h
  repeat udisp h
  repeat ustep h
  ibranch h c1
  repeat ustep h
  obtain ⟨_, ⟨_, hc, h⟩ | ⟨_, hc, -⟩⟩ := ric_call (k := 19) (g := t_0b73_c19) rfl h
  on_goal 2 => obtain ⟨_, _, _, _, e⟩ := e19_log fork hdep hc; cases e
  obtain ⟨b₀, data, M', G', e⟩ := e19_log fork hdep hc
  cases e
  clear hc
  repeat ustep h
  cases ric_stop h
  exact ⟨_, List.mem_append_right _ List.mem_cons_self, rfl, by
    simp only [List.take_succ_cons, List.take_zero]⟩

/-- The tail of `addBlackList` and `deprecate` from the event topic: a `LOG1` of one address word at the free
pointer. -/
def logTail (tp : List UInt8) (htp : tp.length ≤ 32) : SFunc :=
  [.push tp htp, .reg (.dup 1), .push [0x40] (by decide), .reg .mload, .reg (.dup 0), .reg (.dup 2),
    .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff] (by decide), .reg .and,
    .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff] (by decide), .reg .and,
    .reg (.dup 1), .reg .mstore, .push [0x20] (by decide), .reg .add, .reg (.swap 1), .reg .pop, .reg .pop,
    .push [0x40] (by decide), .reg .mload, .reg (.dup 0), .reg (.swap 1), .reg .sub, .reg (.swap 0), .reg (.log 1),
    .reg .pop].foldr SFunc.next .ret

theorem logTail_log {tp : List UInt8} {htp} {a ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (wf : Mem.Wf M) (fp : (M.read 64 32).1 = (Bytes.toB256 [96]).toBytes)
    (h : SFunc.RunCut cert.prog sevm [] (St b (a :: ret :: S) M G) (logTail tp htp) (Seg.done o)) :
    ∃ (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b ⟨sevm.currentTarget, [Bytes.toB256 tp], a.toAdr.toB256.toBytes⟩) S M' G') := by
  unfold logTail at h
  simp only [List.foldr_cons, List.foldr_nil] at h
  have w96 : (Bytes.toB256 [96]).toBytes.toB256 = Bytes.toB256 [96] := by decide +kernel
  have l96 : (Bytes.toB256 [96]).toNat = 96 := by decide +kernel
  have l64 : (Bytes.toB256 [64]).toNat = 64 := by decide +kernel
  iterate 4 ustep h
  have r1 : (M.read (Bytes.toB256 [64]).toNat 32).1 = (Bytes.toB256 [96]).toBytes := by rw [l64]; exact fp
  rw [r1, w96] at h
  iterate 13 ustep h
  have wN : Mem.Wf (M.read (Bytes.toB256 [64]).toNat 32).2 := by uwf
  simp only [ff20_and_word, toAdr_toB256] at h
  rw [l96] at h
  have r2 : (((M.read (Bytes.toB256 [64]).toNat 32).2.write 96 a.toAdr.toB256.toBytes).read
      (Bytes.toB256 [64]).toNat 32).1 = (Bytes.toB256 [96]).toBytes := by
    rw [Mem.read_write_word_disjoint wN 96 _ (.inr (by decide +kernel)), memRead_snd_fst, r1]
  iterate 2 ustep h
  rw [r2, w96] at h
  iterate 4 ustep h
  have h' := ric_next h
  clear h
  obtain ⟨_, hd, h⟩ := h'
  obtain ⟨G', e⟩ := ri_log1 hd
  subst e
  clear hd
  iterate 1 ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  rw [memRead_snd_fst, l96,
    show (Bytes.toB256 [32] + Bytes.toB256 [96] - Bytes.toB256 [96]).toNat = 32 by decide +kernel,
    Mem.read_write_word_of_wf wN 96 _] at e
  exact ⟨_, _, Seg.done.inj e⟩

/-- The `AddedBlackList(address)` topic. -/
def addedTopic : B256 := 0x42e160154868087d6bfdc0ca23d96a1c1cfa32f1b72ba9ba27b69b98a0d819dc

/-- The scratch hash leaves the free pointer where it was. -/
theorem scratch_fp {x y : B256} (wf : Mem.Wf M) (fp : (M.read 64 32).1 = (Bytes.toB256 [96]).toBytes)
    (a n : Nat) : (((((M.write (Bytes.toB256 [0]).toNat x.toBytes).write (Bytes.toB256 [32] + Bytes.toB256 [0]).toNat
      y.toBytes).read a n).2).read 64 32).1 = (Bytes.toB256 [96]).toBytes := by
  rw [memRead_snd_fst, Mem.read_write_word_disjoint (wf.write _ _) _ _ (.inl (by decide +kernel)),
    Mem.read_write_word_disjoint wf _ _ (.inl (by decide +kernel))]
  exact fp

/-- **Entry 21, `addBlackList(a)`.** -/
theorem e21_log {a ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (fp : (M.read 64 32).1 = (Bytes.toB256 [96]).toBytes)
    (run : SFunc.Run cert.prog sevm (St b (a :: ret :: S) M G) t_0cd4_c21 o) :
    ∃ (b₀ : Devm) (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b₀ ⟨sevm.currentTarget, [addedTopic], a.toAdr.toB256.toBytes⟩) S M' G') := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  iterate 39 ustep h
  have l := logTail_log (tp := [0x42, 0xe1, 0x60, 0x15, 0x48, 0x68, 0x08, 0x7d, 0x6b, 0xfd, 0xc0, 0xca, 0x23, 0xd9, 0x6a,
    0x1c, 0x1c, 0xfa, 0x32, 0xf1, 0xb7, 0x2b, 0xa9, 0xba, 0x27, 0xb6, 0x9b, 0x98, 0xa0, 0xd8, 0x19, 0xdc])
    (htp := by decide) fork (by uwf) (by
      exact scratch_fp wf fp _ _) h
  obtain ⟨M', G', e⟩ := l
  rw [show Bytes.toB256 [0x42, 0xe1, 0x60, 0x15, 0x48, 0x68, 0x08, 0x7d, 0x6b, 0xfd, 0xc0, 0xca, 0x23, 0xd9, 0x6a,
    0x1c, 0x1c, 0xfa, 0x32, 0xf1, 0xb7, 0x2b, 0xa9, 0xba, 0x27, 0xb6, 0x9b, 0x98, 0xa0, 0xd8, 0x19, 0xdc] = addedTopic
    by decide] at e
  exact ⟨_, _, _, e⟩

/-- The `Deprecate(address)` topic. -/
def deprecateTopic : B256 := 0xcc358699805e9a8b7f77b522628c7cb9abd07d9efb86b6fb616af1609036a99e

/-- **Entry 18, `deprecate(a)`.** -/
theorem e18_log {a ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (fp : (M.read 64 32).1 = (Bytes.toB256 [96]).toBytes)
    (run : SFunc.Run cert.prog sevm (St b (a :: ret :: S) M G) t_0a56_c18 o) :
    ∃ (b₀ : Devm) (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b₀ ⟨sevm.currentTarget, [deprecateTopic], a.toAdr.toB256.toBytes⟩) S M' G') := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  iterate 43 ustep h
  have l := logTail_log (tp := [0xcc, 0x35, 0x86, 0x99, 0x80, 0x5e, 0x9a, 0x8b, 0x7f, 0x77, 0xb5, 0x22, 0x62, 0x8c, 0x7c,
    0xb9, 0xab, 0xd0, 0x7d, 0x9e, 0xfb, 0x86, 0xb6, 0xfb, 0x61, 0x6a, 0xf1, 0x60, 0x90, 0x36, 0xa9, 0x9e])
    (htp := by decide) fork wf fp h
  obtain ⟨M', G', e⟩ := l
  rw [show Bytes.toB256 [0xcc, 0x35, 0x86, 0x99, 0x80, 0x5e, 0x9a, 0x8b, 0x7f, 0x77, 0xb5, 0x22, 0x62, 0x8c, 0x7c,
    0xb9, 0xab, 0xd0, 0x7d, 0x9e, 0xfb, 0x86, 0xb6, 0xfb, 0x61, 0x6a, 0xf1, 0x60, 0x90, 0x36, 0xa9, 0x9e] = deprecateTopic
    by decide] at e
  exact ⟨_, _, _, e⟩

/-- The `DestroyedBlackFunds(address,uint256)` topic. -/
def destroyedTopic : B256 := 0x61e6e66b0d6339b2980aecc6ccc0039736791f0ccde9ed512e789a7fbdd698c6

/-- The tail of `destroyBlackFunds` from the event topic. -/
def destroyTail (tp : List UInt8) (htp : tp.length ≤ 32) : SFunc :=
  [.push tp htp, .reg (.dup 2), .reg (.dup 2), .push [0x40] (by decide), .reg .mload, .reg (.dup 0), .reg (.dup 3),
    .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff] (by decide), .reg .and,
    .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff] (by decide), .reg .and,
    .reg (.dup 1), .reg .mstore, .push [0x20] (by decide), .reg .add, .reg (.dup 2), .reg (.dup 1), .reg .mstore,
    .push [0x20] (by decide), .reg .add, .reg (.swap 2), .reg .pop, .reg .pop, .reg .pop,
    .push [0x40] (by decide), .reg .mload, .reg (.dup 0), .reg (.swap 1), .reg .sub, .reg (.swap 0), .reg (.log 1),
    .reg .pop, .reg .pop].foldr SFunc.next .ret

theorem destroyTail_log {tp : List UInt8} {htp} {v a ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (wf : Mem.Wf M) (fp : (M.read 64 32).1 = (Bytes.toB256 [96]).toBytes)
    (h : SFunc.RunCut cert.prog sevm [] (St b (v :: a :: ret :: S) M G) (destroyTail tp htp) (Seg.done o)) :
    ∃ (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b ⟨sevm.currentTarget, [Bytes.toB256 tp], a.toAdr.toB256.toBytes ++ v.toBytes⟩) S M' G') := by
  unfold destroyTail at h
  simp only [List.foldr_cons, List.foldr_nil] at h
  have w96 : (Bytes.toB256 [96]).toBytes.toB256 = Bytes.toB256 [96] := by decide +kernel
  have l96 : (Bytes.toB256 [96]).toNat = 96 := by decide +kernel
  have l64 : (Bytes.toB256 [64]).toNat = 64 := by decide +kernel
  iterate 5 ustep h
  have r1 : (M.read (Bytes.toB256 [64]).toNat 32).1 = (Bytes.toB256 [96]).toBytes := by rw [l64]; exact fp
  rw [r1, w96] at h
  iterate 8 ustep h
  have wN : Mem.Wf (M.read (Bytes.toB256 [64]).toNat 32).2 := by uwf
  simp only [ff20_and_word, toAdr_toB256] at h
  rw [l96] at h
  iterate 2 ustep h
  iterate 3 ustep h
  have l128 : (Bytes.toB256 [32] + Bytes.toB256 [96]).toNat = 96 + 32 := by decide +kernel
  rw [l128] at h
  have wA : Mem.Wf ((M.read (Bytes.toB256 [64]).toNat 32).2.write 96 a.toAdr.toB256.toBytes) := wN.write _ _
  have r2 : ((((M.read (Bytes.toB256 [64]).toNat 32).2.write 96 a.toAdr.toB256.toBytes).write (96 + 32) v.toBytes).read
      (Bytes.toB256 [64]).toNat 32).1 = (Bytes.toB256 [96]).toBytes := by
    rw [Mem.read_write_word_disjoint wA _ _ (.inr (by decide +kernel)),
      Mem.read_write_word_disjoint wN 96 _ (.inr (by decide +kernel)), memRead_snd_fst, r1]
  iterate 8 ustep h
  rw [r2, w96] at h
  iterate 4 ustep h
  have h' := ric_next h
  clear h
  obtain ⟨_, hd, h⟩ := h'
  obtain ⟨G', e⟩ := ri_log1 hd
  subst e
  clear hd
  iterate 2 ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  rw [memRead_snd_fst, l96,
    show (Bytes.toB256 [32] + (Bytes.toB256 [32] + Bytes.toB256 [96]) - Bytes.toB256 [96]).toNat = 64 by decide +kernel,
    Mem.read_two_word_writes_at_raw] at e
  exact ⟨_, _, Seg.done.inj e⟩

/-- **Entry 49, `destroyBlackFunds(a)`, not deprecated.** It requires `a` listed and logs. -/
theorem e49_log {a ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (fp : (M.read 64 32).1 = (Bytes.toB256 [96]).toBytes)
    (hdep : flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (run : SFunc.Run cert.prog sevm (St b (a :: ret :: S) M G) t_1e8a_c49 o) :
    listedByte (Devm.getStor b sevm.currentTarget) a.toAdr ≠ 0 ∧
    ∃ (b₀ : Devm) (v : B256) (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b₀ ⟨sevm.currentTarget, [destroyedTopic], a.toAdr.toB256.toBytes ++ v.toBytes⟩) S M' G') := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ibranch h c2
  have listed : listedByte (Devm.getStor b sevm.currentTarget) a.toAdr ≠ 0 := by
    intro zero
    unorm c2
    have l6 : Bytes.toB256 [6] = 6 := by decide
    rw [l6] at c2
    rw [show (Bytes.toB256 [255] &&& (Devm.getStor b sevm.currentTarget).get (mapSlot a.toAdr.toB256 6)) = 0 from zero] at c2
    exact c2 (by decide)
  refine ⟨listed, ?_⟩
  clear listed c1 c2
  repeat ustep h
  ucall h hc 33 t_1239_c33
  obtain ⟨B, MB, GB, e, sB, wB, rB⟩ := e33_out fork (by uwf) (by simp only [afterSloadH_getStor]; exact hdep) hc
  cases e
  clear hc
  have fpB : (MB.read 64 32).1 = (Bytes.toB256 [96]).toBytes := by
    rw [rB]
    exact scratch_fp wf fp _ _
  clear rB sB
  iterate 40 ustep h
  have l := destroyTail_log (tp := [0x61, 0xe6, 0xe6, 0x6b, 0x0d, 0x63, 0x39, 0xb2, 0x98, 0x0a, 0xec, 0xc6, 0xcc, 0xc0, 0x03,
    0x97, 0x36, 0x79, 0x1f, 0x0c, 0xcd, 0xe9, 0xed, 0x51, 0x2e, 0x78, 0x9a, 0x7f, 0xbd, 0xd6, 0x98, 0xc6])
    (htp := by decide) fork (by uwf) (scratch_fp wB fpB _ _) h
  obtain ⟨M', G', e⟩ := l
  rw [show Bytes.toB256 [0x61, 0xe6, 0xe6, 0x6b, 0x0d, 0x63, 0x39, 0xb2, 0x98, 0x0a, 0xec, 0xc6, 0xcc, 0xc0, 0x03,
    0x97, 0x36, 0x79, 0x1f, 0x0c, 0xcd, 0xe9, 0xed, 0x51, 0x2e, 0x78, 0x9a, 0x7f, 0xbd, 0xd6, 0x98, 0xc6] = destroyedTopic
    by decide] at e
  exact ⟨_, _, _, _, e⟩

theorem prologue_fp (wf : Mem.Wf M) :
    ((M.write (Bytes.toB256 [64]).toNat (Bytes.toB256 [96]).toBytes).read 64 32).1 = (Bytes.toB256 [96]).toBytes := by
  rw [show (Bytes.toB256 [64]).toNat = 64 by decide +kernel]
  exact Mem.read_write_word_of_wf wf 64 _

/-- **A committed `deprecate(a)` logs `Deprecate(a)`.** -/
theorem frame_deprecate_logs {post : Devm} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (sel : Blanc.Sevm.selector sevm = 0x0753c30c)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    (⟨sevm.currentTarget, [deprecateTopic], (Sevm.dataWord sevm 4).toAdr.toB256.toBytes⟩ : Log) ∈ post.logs := by
  have h := run.cut
  clear run
  iterate 7 ustep h
  ibranch h c0
  iterate 7 ustep h
  rw [legacy_selector_word, sel] at h
  repeat udisp h
  repeat ustep h
  ibranch h c1
  repeat ustep h
  obtain ⟨_, ⟨_, hc, h⟩ | ⟨_, hc, -⟩⟩ := ric_call (k := 18) (g := t_0a56_c18) rfl h
  on_goal 2 => obtain ⟨_, _, _, e⟩ := e18_log fork (by uwf) (prologue_fp wf) hc; cases e
  obtain ⟨b₀, M', G', e⟩ := e18_log fork (by uwf) (prologue_fp wf) hc
  cases e
  clear hc
  repeat ustep h
  cases ric_stop h
  simp only [ff20_and_word, toAdr_toB256, lit4]
  exact List.mem_append_right _ List.mem_cons_self

/-- **A committed `addBlackList(a)` logs `AddedBlackList(a)`.** -/
theorem frame_addBlackList_logs {post : Devm} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (sel : Blanc.Sevm.selector sevm = 0x0ecb93c0)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    (⟨sevm.currentTarget, [addedTopic], (Sevm.dataWord sevm 4).toAdr.toB256.toBytes⟩ : Log) ∈ post.logs := by
  have h := run.cut
  clear run
  iterate 7 ustep h
  ibranch h c0
  iterate 7 ustep h
  rw [legacy_selector_word, sel] at h
  repeat udisp h
  repeat ustep h
  ibranch h c1
  repeat ustep h
  obtain ⟨_, ⟨_, hc, h⟩ | ⟨_, hc, -⟩⟩ := ric_call (k := 21) (g := t_0cd4_c21) rfl h
  on_goal 2 => obtain ⟨_, _, _, e⟩ := e21_log fork (by uwf) (prologue_fp wf) hc; cases e
  obtain ⟨b₀, M', G', e⟩ := e21_log fork (by uwf) (prologue_fp wf) hc
  cases e
  clear hc
  repeat ustep h
  cases ric_stop h
  simp only [ff20_and_word, toAdr_toB256, lit4]
  exact List.mem_append_right _ List.mem_cons_self

/-- **A committed `destroyBlackFunds(a)`, not deprecated, requires `a` listed and logs `DestroyedBlackFunds(a, _)`.** -/
theorem frame_destroy_logs {post : Devm} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (sel : Blanc.Sevm.selector sevm = 0xf3bdc228)
    (hdep : flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    listedByte (Devm.getStor b sevm.currentTarget) (Sevm.dataWord sevm 4).toAdr ≠ 0 ∧
      ∃ v : B256, (⟨sevm.currentTarget, [destroyedTopic],
        (Sevm.dataWord sevm 4).toAdr.toB256.toBytes ++ v.toBytes⟩ : Log) ∈ post.logs := by
  have h := run.cut
  clear run
  iterate 7 ustep h
  ibranch h c0
  iterate 7 ustep h
  rw [legacy_selector_word, sel] at h
  repeat udisp h
  repeat ustep h
  ibranch h c1
  repeat ustep h
  obtain ⟨_, ⟨_, hc, h⟩ | ⟨_, hc, -⟩⟩ := ric_call (k := 49) (g := t_1e8a_c49) rfl h
  on_goal 2 => obtain ⟨_, _, _, _, _, e⟩ := e49_log fork (by uwf) (prologue_fp wf) hdep hc; cases e
  obtain ⟨listed, b₀, v, M', G', e⟩ := e49_log fork (by uwf) (prologue_fp wf) hdep hc
  cases e
  clear hc
  repeat ustep h
  cases ric_stop h
  simp only [ff20_and_word, toAdr_toB256, lit4] at listed ⊢
  exact ⟨listed, v, List.mem_append_right _ List.mem_cons_self⟩

/-! ## The frames a reader's check speaks of -/

variable {T h : Adr} {frames : List Exec.Frame}

/-- **`noConfiscation` from the logs**: a committed frame that confiscates `h`'s entry, not deprecated, logs
`DestroyedBlackFunds` with `h` as the first data word. USDT's log has the address in data, not a topic. -/
theorem confiscates_logs {F : Exec.Frame} (good : CodeFrame T HistFork code F) (target : F.sevm.currentTarget = T)
    (live : NotDeprecated T F) (wf : Mem.Wf F.pre.memory) (named : Confiscates h F.sevm) :
    ∃ l ∈ F.post.logs, l.address = T ∧ l.topics = [destroyedTopic] ∧ l.data.take 32 = h.toB256.toBytes := by
  have hdep : flag20 ((Devm.getStor (St F.pre F.pre.stack F.pre.memory F.pre.gasLeft) F.sevm.currentTarget).get 10) = 0 := by
    simp only [St_getStor, target]
    exact live
  obtain ⟨-, v, mem⟩ := frame_destroy_logs good.2.2.1 wf named.1 hdep (codeFrame_run good)
  refine ⟨_, mem, target, rfl, ?_⟩
  simp only [named.2]
  exact List.take_left' (B256.length_toBytes _)

/-- **A committed `destroyBlackFunds` on `h`, not deprecated, finds `h` listed at its entry.** -/
theorem confiscates_listed {F : Exec.Frame} (good : CodeFrame T HistFork code F) (target : F.sevm.currentTarget = T)
    (live : NotDeprecated T F) (wf : Mem.Wf F.pre.memory) (named : Confiscates h F.sevm) :
    listedByte (Devm.getStor F.pre T) h ≠ 0 := by
  have hdep : flag20 ((Devm.getStor (St F.pre F.pre.stack F.pre.memory F.pre.gasLeft) F.sevm.currentTarget).get 10) = 0 := by
    simp only [St_getStor, target]
    exact live
  have := (frame_destroy_logs good.2.2.1 wf named.1 hdep (codeFrame_run good)).1
  simpa only [St_getStor, target, named.2] using this

/-- **A committed `deprecate` logs `Deprecate`, at `T`.** -/
theorem deprecate_logs {F : Exec.Frame} (good : CodeFrame T HistFork code F) (target : F.sevm.currentTarget = T)
    (wf : Mem.Wf F.pre.memory) (sel : Blanc.Sevm.selector F.sevm = 0x0753c30c) :
    ∃ l ∈ F.post.logs, l.address = T ∧ l.topics = [deprecateTopic] :=
  ⟨_, frame_deprecate_logs good.2.2.1 wf sel (codeFrame_run good), target, rfl⟩

/-- **A committed `addBlackList(a)` logs `AddedBlackList` with `a` as data, at `T`.** -/
theorem addBlackList_logs {F : Exec.Frame} (good : CodeFrame T HistFork code F) (target : F.sevm.currentTarget = T)
    (wf : Mem.Wf F.pre.memory) (sel : Blanc.Sevm.selector F.sevm = 0x0ecb93c0) (named : (Sevm.dataWord F.sevm 4).toAdr = h) :
    ∃ l ∈ F.post.logs, l.address = T ∧ l.topics = [addedTopic] ∧ l.data = h.toB256.toBytes :=
  ⟨_, frame_addBlackList_logs good.2.2.1 wf sel (codeFrame_run good), target, rfl, by simp only [named]⟩

/-- **A committed `approve` by the holder, not deprecated, logs `Approval` with the holder, at `T`.** -/
theorem approve_logs {F : Exec.Frame} (good : CodeFrame T HistFork code F) (target : F.sevm.currentTarget = T)
    (live : NotDeprecated T F) (sel : Blanc.Sevm.selector F.sevm = 0x095ea7b3) (hc : F.sevm.caller = h) :
    FrameLogsApproval T h F := by
  have hdep : flag20 ((Devm.getStor (St F.pre F.pre.stack F.pre.memory F.pre.gasLeft) F.sevm.currentTarget).get 10) = 0 := by
    simp only [St_getStor, target]
    exact live
  obtain ⟨l, mem, addr, topics⟩ := frame_approve_logs good.2.2.1 sel hdep (codeFrame_run good)
  exact ⟨l, mem, addr.trans target, by rw [topics, hc]⟩

/-- **A committed frame, not deprecated, that raises one of the holder's tracked rows from empty logs `Approval`
with the holder as owner.** `rowTable_ok` certifies `approve` as the only selector the table leaves open; the four
`top` selectors go through their frame laws. -/
theorem frame_rows_raised_logs {F : Exec.Frame} (hF : F ∈ frames) (good : CodeFrame T HistFork code F)
    (target : F.sevm.currentTarget = T) (live : NotDeprecated T F) (keys : UsdtKeysFresh h frames)
    (rows : RowsEmpty h frames (wordsAt T F.pre.state)) (raised : ¬ RowsEmpty h frames (wordsAt T F.post.state)) :
    FrameLogsApproval T h F := by
  refine Classical.byContradiction fun noLog => raised ?_
  have run := codeFrame_run good
  have fork : HistFork F.sevm.benvStat.fork := good.2.2.1
  have C := certFrame good target live
  have hdep : flag20 ((Devm.getStor (St F.pre F.pre.stack F.pre.memory F.pre.gasLeft) F.sevm.currentTarget).get 10) = 0 := by
    simp only [St_getStor, target]
    exact live
  change ∀ g, CallerOf frames g → (Devm.getStor F.post T).get (allowSlot h g) = 0
  change ∀ g, CallerOf frames g → (Devm.getStor F.pre T).get (allowSlot h g) = 0 at rows
  by_cases s1 : Blanc.Sevm.selector F.sevm = 0xa9059cbb
  · obtain ⟨-, -, ok, st⟩ := frame_transfer fork s1 hdep run
    simp only [St_getStor, target] at ok st
    exact (transfer_law hF keys target (transferKeys hF s1) rfl ok st s1 rows).1
  by_cases s2 : Blanc.Sevm.selector F.sevm = 0x23b872dd
  · obtain ⟨-, -, allow, ok, st⟩ := frame_transferFrom fork s2 hdep run
    simp only [St_getStor, target] at allow ok st
    exact (from_law hF keys target (fromKeys hF s2) rfl allow ok st rows).1
  have ownerRow : ∀ g, CallerOf frames g → balSlot (ownerOf (Devm.getStor F.pre T)) ≠ allowSlot h g := by
    rintro g ⟨G, hG, hg⟩
    have ko : CoinKey.map 2 (ownerOf (Devm.getStor F.pre T)).toB256 ∈ KeyList h frames := by
      have m := owner_mem (h := h) hF
      unfold ownerKey at m
      rwa [target] at m
    exact bal_ne_row keys hG hg ko
  by_cases s3 : Blanc.Sevm.selector F.sevm = 0xcc872b66
  · obtain ⟨-, st⟩ := frame_issue fork s3 run
    simp only [target] at st
    rw [st]
    rintro g ⟨G', hG, hg⟩
    rw [issueStor_get_ne (one_ne_row keys hG hg) (ownerRow g ⟨G', hG, hg⟩)]
    exact rows g ⟨G', hG, hg⟩
  by_cases s4 : Blanc.Sevm.selector F.sevm = 0xdb006a75
  · obtain ⟨-, st⟩ := frame_redeem fork s4 run
    simp only [target] at st
    rw [st]
    rintro g ⟨G', hG, hg⟩
    rw [redeemStor_get_ne (one_ne_row keys hG hg) (ownerRow g ⟨G', hG, hg⟩)]
    exact rows g ⟨G', hG, hg⟩
  have notTop : selTerm.eval (Env.root F.sevm) ∉ topSelectors := by
    rw [selTerm_eval]
    simp only [topSelectors, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨s1, s2, s3, s4⟩
  refine frame_rows_zero C cert_check usdt_wsCert (t := rowTable) (b := 5) rfl rowTable_ok
    (rowSep_of_keys keys.coin hF) ?_ rows
  rintro (⟨sel, caller⟩ | ⟨sel, -⟩ | sel)
  · have hsel : Blanc.Sevm.selector F.sevm = 0x095ea7b3 := by
      have := List.mem_singleton.mp sel
      rwa [show rowTable.selT = selTerm from rfl, selTerm_eval] at this
    have hc : F.sevm.caller = h := by
      have e : (Env.root F.sevm).caller = F.sevm.caller.toB256 := rfl
      rw [e, toAdr_toB256] at caller
      exact caller
    exact noLog (approve_logs good target live hsel hc)
  · exact absurd sel List.not_mem_nil
  · exact notTop sel

/-! ## `deprecated`: only `deprecate` writes slot 10 -/

/-- The certificate's sites at slot 10 are `deprecate`'s. -/
theorem flagSites_ok :
    (wsRoot UsdtWs.implWsAnn).all (fun s => s.slot != .const 10 || hasSel selTerm [0x0753c30c] s) = true := by
  decide +kernel

/-- **A frame, not deprecated, on any other selector than `deprecate` keeps slot 10.** `apart` is hash freshness: no
other site's key is 10. With `deprecate_logs` and the receipt link, no `Deprecate` log from a state with the flag clear
keeps it clear across every frame. -/
theorem frame_flag_keep {F : Exec.Frame} (good : CodeFrame T HistFork code F) (target : F.sevm.currentTarget = T)
    (live : NotDeprecated T F)
    (apart : ∀ s ∈ wsRoot UsdtWs.implWsAnn, s.slot.Den (Env.root F.sevm) 10 → s.slot = .const 10)
    (other : Blanc.Sevm.selector F.sevm ≠ 0x0753c30c) :
    (F.post.getStor T).get 10 = (F.pre.getStor T).get 10 := by
  have C := certFrame good target live
  refine frame_cellInv F C.stateGas C.hasCode _ (Inv := fun v => v = (F.pre.getStor T).get 10) rfl ?_
  intro m member w found _ key _
  obtain ⟨site, inRoot, den, guards, -⟩ := successfulSstore_site cert_check usdt_wsCert C.pc C.code C.stateGas
    (C.chain member found) found
  rw [key] at den
  have constant := apart site inRoot den
  have row := List.all_eq_true.mp flagSites_ok site inRoot
  simp only [constant, bne_self_eq_false, Bool.false_or] at row
  have hsel := hasSel_sound row rfl guards
  rw [selTerm_eval] at hsel
  exact absurd (List.mem_singleton.mp hsel) other

end Blanc.Lift.CurveCoins.Usdt
