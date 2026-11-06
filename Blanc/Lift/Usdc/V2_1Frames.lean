import Blanc.Lift.Usdc.ImplV2_1.Check
import Blanc.Lift.InvWalkLegacy

/-!
# FiatTokenV2_1: the frames of `transfer`, `transferFrom` and `balanceOf`, inverted
-/

namespace Blanc.Lift.Usdc.ImplV2_1

open Jaune Blanc Blanc.Lift

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- The internal callees of the family: none halts the frame. -/
def familyCallees : List Nat := [6, 30, 39, 58, 73, 75, 76, 86, 91]

theorem familyCallees_noHalt : NoHaltSet cert.prog familyCallees = true := by decide +kernel

/-- Enter callee entry `k` (tree `T`) of `familyCallees` from a cut run `h`. -/
macro "ucall " h:ident hc:ident k:num T:term : tactic => `(tactic|
  (have h' := ric_callR (k := $k) (g := $T) rfl
    (fun hh => SFunc.RunP.not_halted_entry familyCallees_noHalt
      (by decide : $k ∈ familyCallees) rfl hh rfl) $h
   clear $h
   obtain ⟨_, _, $hc:ident, $h:ident⟩ := h'))

/-- **Entry 75, SafeMath `add`**. -/
theorem e75_inv {x y ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: ret :: S) M G) t_3e26_c75 o) :
    x.toNat + y.toNat < 2 ^ 256 ∧ ∃ G', o = .returned (St b ((x + y) :: S) M G') := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  cases e
  exact ⟨(add_nof_of_ltCheck (eq_zero_of_iszero_ne_zero c)).1, _, rfl⟩

/-- The error-message copy loop of SafeMath's messaged `sub` only reverts. -/
theorem revertCopy_noExit : NoExitSet cert.prog [6, 91] = true := by decide +kernel

/-- **Entry 86, SafeMath `sub` with a message**. -/
theorem e86_inv {m x y ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (m :: x :: y :: ret :: S) M G) t_4576_c86 o) :
    x.toNat ≤ y.toNat ∧ ∃ G', o = .returned (St b ((y - x) :: S) M G') := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c
  · exact (SFunc.RunP.false_of_noExit revertCopy_noExit (by decide) (by decide) h.uncut).elim
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  cases e
  exact ⟨toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero c), _, rfl⟩

/-- **Entry 76, SafeMath `sub`**. -/
theorem e76_inv {x y ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: ret :: S) M G) t_3d4c_c76 o) :
    x.toNat ≤ y.toNat ∧ ∃ M' G', o = .returned (St b ((y - x) :: S) M' G') ∧ Mem.Wf M' := by
  have h := run.cut
  clear run
  repeat ustep h
  ucall h hc 86 t_4576_c86
  obtain ⟨c, G1, e⟩ := e86_inv fork hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  cases e
  exact ⟨c, _, _, rfl, by uwf⟩

/-! ## The ledger -/

/-- A balance entry (`balances`, slot 9). -/
def balSlot (a : Adr) : B256 := mapSlot a.toB256 9

/-- `transfer`'s move. -/
def moveStor (σ : Stor) (src dst : Adr) (v : B256) : Stor :=
  (σ.set (balSlot src) (σ.get (balSlot src) - v)).set (balSlot dst)
    (v + (σ.set (balSlot src) (σ.get (balSlot src) - v)).get (balSlot dst))

theorem lit9 : Bytes.toB256 [9] = 9 := by decide

/-- The word normal form of a walk's stack and facts. -/
macro "unorm " h:ident : tactic => `(tactic|
  (simp (config := { failIfUnchanged := false }) only [keccak_scratch, ff20_and_word, word_ff20,
     toAdr_toB256, getStorVal_afterSload, lit9, afterSstore_getStor_self,
     AccumulatedWalk.getStorVal_afterSstore_self, afterSload_getStor, gsv] at $h:ident))

/-- **Entry 73, `_transfer(owner, recipient, amount)`**. -/
theorem e73_inv {v t r ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm (St b (v :: t :: r :: ret :: S) M G) t_3b21_c73 o) :
    v.toNat ≤ ((Devm.getStor b sevm.currentTarget).get (balSlot r.toAdr)).toNat ∧
      v.toNat + (((Devm.getStor b sevm.currentTarget).set (balSlot r.toAdr)
        ((Devm.getStor b sevm.currentTarget).get (balSlot r.toAdr) - v)).get
          (balSlot t.toAdr)).toNat < 2 ^ 256 ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧ Mem.Wf M' ∧
        Devm.getStor b' sevm.currentTarget =
          moveStor (Devm.getStor b sevm.currentTarget) r.toAdr t.toAdr v := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ibranch h c2
  repeat ustep h
  ibranch h c3
  clear c1 c2
  unorm h
  unorm c3
  umemw h wf
  repeat ustep h
  unorm h
  umemw h wf
  ucall h hc 76 t_3d4c_c76
  obtain ⟨c4, M1, G1, e, wf1⟩ := e76_inv fork wf hc
  cases e
  clear hc wf
  unorm c4
  iterate 26 ustep h
  simp only [keccak_rehash wf1, keccak_scratch, ff20_and_word, word_ff20, toAdr_toB256,
    getStorVal_afterSload, lit9, afterSstore_getStor_self,
    AccumulatedWalk.getStorVal_afterSstore_self, afterSload_getStor, gsv] at h
  umemw h wf1
  repeat ustep h
  unorm h
  umemw h wf1
  ucall h hc 75 t_3e26_c75
  obtain ⟨c5, G2, e⟩ := e75_inv fork hc
  cases e
  clear hc
  unorm c5
  repeat ustep h
  unorm h
  umemw h wf1
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  refine ⟨toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero c3), c5, _, _, _,
    Seg.done.inj e, ?_, ?_⟩
  · uwf
  · simp only [Devm.addLog_getStor, afterSstore_getStor_self, afterSload_getStor, keccak_scratch,
      ff20_and_word, word_ff20, toAdr_toB256, lit9, gsv]
    rfl

/-- `paused`, the byte at offset 20 of slot 1. -/
def pausedByte (σ : Stor) : B256 :=
  Bytes.toB256 [255] &&& σ.get 1 / Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- `blacklisted[a]`, the low byte of the entry at slot 3. -/
def listedByte (σ : Stor) (a : Adr) : B256 := Bytes.toB256 [255] &&& σ.get (mapSlot a.toB256 3)

theorem lit1 : Bytes.toB256 [1] = 1 := by decide
theorem lit3 : Bytes.toB256 [3] = 3 := by decide

/-- **Entry 30, `transfer(to, value)`**. -/
theorem e30_inv {v t ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm (St b (v :: t :: ret :: S) M G) t_2b65_c30 o) :
    pausedByte (Devm.getStor b sevm.currentTarget) = 0 ∧
      listedByte (Devm.getStor b sevm.currentTarget) sevm.caller = 0 ∧
      listedByte (Devm.getStor b sevm.currentTarget) t.toAdr = 0 ∧
      v.toNat ≤ ((Devm.getStor b sevm.currentTarget).get (balSlot sevm.caller)).toNat ∧
      v.toNat + (((Devm.getStor b sevm.currentTarget).set (balSlot sevm.caller)
        ((Devm.getStor b sevm.currentTarget).get (balSlot sevm.caller) - v)).get
          (balSlot t.toAdr)).toNat < 2 ^ 256 ∧
      ∃ b' M' G', o = .returned (St b' (Bytes.toB256 [1] :: S) M' G') ∧ Mem.Wf M' ∧
        Devm.getStor b' sevm.currentTarget =
          moveStor (Devm.getStor b sevm.currentTarget) sevm.caller t.toAdr v := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  repeat ustep h
  unorm h
  ibranch h c2
  repeat ustep h
  unorm h
  ibranch h c3
  repeat ustep h
  ucall h hc 73 t_3b21_c73
  obtain ⟨d1, d2, B, MB, GB, e, wfb, sB⟩ := e73_inv fork (by uwf) hc
  cases e
  clear hc
  simp only [toAdr_toB256, afterSload_getStor] at d1 d2 sB
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  unorm c1
  unorm c2
  unorm c3
  simp only [lit1, lit3] at c1 c2 c3
  refine ⟨eq_zero_of_iszero_ne_zero c1, eq_zero_of_iszero_ne_zero c2, eq_zero_of_iszero_ne_zero c3,
    d1, d2, _, _, _, Seg.done.inj e, wfb, sB⟩

/-- An allowance entry (`allowed`, slot 10). -/
def allowSlot (o s : Adr) : B256 := mapSlot s.toB256 (mapSlot o.toB256 10)

theorem lit10 : Bytes.toB256 [10] = 10 := by decide

/-- `transferFrom`'s storage: the move, then the allowance read after it lowered. -/
def fromStor (σ : Stor) (r s t : Adr) (v : B256) : Stor :=
  (moveStor σ r t v).set (allowSlot r s) ((moveStor σ r t v).get (allowSlot r s) - v)

/-- **Tree `0x1375` of entry 58, the allowance write.** -/
theorem e58_tail {v t r ret p q w x : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (wf : Mem.Wf M)
    (h : SFunc.RunCut cert.prog sevm []
      (St b (p :: q :: w :: x :: v :: t :: r :: ret :: S) M G) t_1375_c58 (Seg.done o)) :
    v.toNat ≤ ((Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sevm.caller)).toNat ∧
      ∃ b' M' G', o = .returned (St b' (Bytes.toB256 [1] :: S) M' G') ∧
        Devm.getStor b' sevm.currentTarget =
          (Devm.getStor b sevm.currentTarget).set (allowSlot r.toAdr sevm.caller)
            ((Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sevm.caller) - v) := by
  repeat ustep h
  simp only [keccak_scratch, ff20_and_word, word_ff20, toAdr_toB256, lit10,
    getStorVal_afterSload, gsv, afterSload_getStor] at h
  umemw h wf
  ucall h hc 76 t_3d4c_c76
  obtain ⟨c1, M1, G1, e, wf1⟩ := e76_inv fork wf hc
  cases e
  clear hc wf
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
  clear e
  refine ⟨?_, B, MB, GB, eo, ?_⟩
  · simp (config := { failIfUnchanged := false }) only [afterSload_getStor] at c1
    exact c1
  · rw [sB]
    simp only [afterSstore_getStor_self, afterSload_getStor, keccak_scratch, ff20_and_word, word_ff20,
      toAdr_toB256, lit10, gsv]
    rfl

/-- **Entry 58, `transferFrom(from, to, value)`**. -/
theorem e58_inv {v t r ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm (St b (v :: t :: r :: ret :: S) M G) t_10e9_c58 o) :
    pausedByte (Devm.getStor b sevm.currentTarget) = 0 ∧
      listedByte (Devm.getStor b sevm.currentTarget) sevm.caller = 0 ∧
      listedByte (Devm.getStor b sevm.currentTarget) r.toAdr = 0 ∧
      listedByte (Devm.getStor b sevm.currentTarget) t.toAdr = 0 ∧
      v.toNat ≤ ((Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sevm.caller)).toNat ∧
      v.toNat ≤ ((Devm.getStor b sevm.currentTarget).get (balSlot r.toAdr)).toNat ∧
      v.toNat + (((Devm.getStor b sevm.currentTarget).set (balSlot r.toAdr)
        ((Devm.getStor b sevm.currentTarget).get (balSlot r.toAdr) - v)).get
          (balSlot t.toAdr)).toNat < 2 ^ 256 ∧
      ∃ b' M' G', o = .returned (St b' (Bytes.toB256 [1] :: S) M' G') ∧
        Devm.getStor b' sevm.currentTarget =
          fromStor (Devm.getStor b sevm.currentTarget) r.toAdr sevm.caller t.toAdr v := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  repeat ustep h
  unorm h
  ibranch h c2
  repeat ustep h
  unorm h
  ibranch h c3
  repeat ustep h
  unorm h
  ibranch h c4
  repeat ustep h
  unorm h
  ibranch h c5
  unorm h
  umemw h wf
  repeat ustep h
  ucall h hc 73 t_3b21_c73
  obtain ⟨d1, d2, B, MB, GB, e, wfb, sB⟩ := e73_inv fork (by uwf) hc
  cases e
  clear hc wf
  simp (config := { failIfUnchanged := false }) only [afterSload_getStor] at d1 d2 sB
  obtain ⟨g1, B', M', G', eo, sB'⟩ := e58_tail fork wfb h
  clear h
  unorm c1
  unorm c2
  unorm c3
  unorm c4
  unorm c5
  simp only [lit1, lit3, lit10] at c1 c2 c3 c4
  refine ⟨eq_zero_of_iszero_ne_zero c1, eq_zero_of_iszero_ne_zero c2, eq_zero_of_iszero_ne_zero c3,
    eq_zero_of_iszero_ne_zero c4, toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero c5),
    d1, d2, B', M', G', eo, ?_⟩
  rw [sB', sB]
  rfl

theorem lit4 : Bytes.toB256 [4] = 4 := by decide
theorem lit36 : Bytes.toB256 [32] + Bytes.toB256 [4] = 36 := by decide

/-- The prologue through the selector, a macro over the cut run `h`. -/
macro "uhead " h:ident sel:ident : tactic => `(tactic|
  (iterate 7 ustep $h
   ibranch $h c0
   iterate 6 ustep $h
   ibranch $h c0'
   iterate 4 ustep $h
   rw [shr_selector_word, $sel:ident] at $h:ident
   repeat udisp $h))

/-- **The `transfer(to, v)` frame of FiatTokenV2_1.** -/
theorem frame_transfer {post : Devm} (fork : CoveredFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (sel : Blanc.Sevm.selector sevm = 0xa9059cbb)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    pausedByte (Devm.getStor b sevm.currentTarget) = 0 ∧
      listedByte (Devm.getStor b sevm.currentTarget) sevm.caller = 0 ∧
      listedByte (Devm.getStor b sevm.currentTarget) (Sevm.dataWord sevm 4).toAdr = 0 ∧
      (Sevm.dataWord sevm 36).toNat ≤ ((Devm.getStor b sevm.currentTarget).get (balSlot sevm.caller)).toNat ∧
      (Sevm.dataWord sevm 36).toNat + (((Devm.getStor b sevm.currentTarget).set (balSlot sevm.caller)
        ((Devm.getStor b sevm.currentTarget).get (balSlot sevm.caller) - Sevm.dataWord sevm 36)).get
          (balSlot (Sevm.dataWord sevm 4).toAdr)).toNat < 2 ^ 256 ∧
      Devm.getStor post sevm.currentTarget =
        moveStor (Devm.getStor b sevm.currentTarget) sevm.caller (Sevm.dataWord sevm 4).toAdr
          (Sevm.dataWord sevm 36) := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ucall h hc 30 t_2b65_c30
  obtain ⟨d1, d2, d3, d4, d5, B, MB, GB, e, wfb, sB⟩ := e30_inv fork (by uwf) hc
  cases e
  clear hc
  repeat ustep h
  have sp := ric_return_getStor h
  clear h
  simp only [lit36] at d3 d4 d5 sB
  simp only [ff20_and_word, word_ff20, toAdr_toB256, lit4] at d3 d4 d5 sB
  exact ⟨d1, d2, d3, d4, d5, by rw [sp, sB]⟩

/-- **The `transferFrom(from, to, v)` frame of FiatTokenV2_1.** -/
theorem frame_transferFrom {post : Devm} (fork : CoveredFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (sel : Blanc.Sevm.selector sevm = 0x23b872dd)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    pausedByte (Devm.getStor b sevm.currentTarget) = 0 ∧
      listedByte (Devm.getStor b sevm.currentTarget) sevm.caller = 0 ∧
      listedByte (Devm.getStor b sevm.currentTarget) (Sevm.dataWord sevm 4).toAdr = 0 ∧
      listedByte (Devm.getStor b sevm.currentTarget) (Sevm.dataWord sevm 36).toAdr = 0 ∧
      (Sevm.dataWord sevm 68).toNat ≤
        ((Devm.getStor b sevm.currentTarget).get (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller)).toNat ∧
      (Sevm.dataWord sevm 68).toNat ≤
        ((Devm.getStor b sevm.currentTarget).get (balSlot (Sevm.dataWord sevm 4).toAdr)).toNat ∧
      (Sevm.dataWord sevm 68).toNat + (((Devm.getStor b sevm.currentTarget).set
        (balSlot (Sevm.dataWord sevm 4).toAdr)
        ((Devm.getStor b sevm.currentTarget).get (balSlot (Sevm.dataWord sevm 4).toAdr) -
          Sevm.dataWord sevm 68)).get (balSlot (Sevm.dataWord sevm 36).toAdr)).toNat < 2 ^ 256 ∧
      Devm.getStor post sevm.currentTarget =
        fromStor (Devm.getStor b sevm.currentTarget) (Sevm.dataWord sevm 4).toAdr sevm.caller
          (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68) := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ucall h hc 58 t_10e9_c58
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, B, MB, GB, e, sB⟩ := e58_inv fork (by uwf) hc
  cases e
  clear hc
  repeat ustep h
  have sp := ric_return_getStor h
  clear h
  simp only [show (Bytes.toB256 [64] + Bytes.toB256 [4]) = 68 by decide, lit36,
    show Bytes.toB256 [32] + 36 = 68 by decide] at d3 d4 d5 d6 d7 sB
  simp only [ff20_and_word, word_ff20, toAdr_toB256, lit4] at d3 d4 d5 d6 d7 sB
  simp only [show (4 : B256) + Bytes.toB256 [32] = 36 by decide] at d3 d4 d5 d6 d7 sB
  exact ⟨d1, d2, d3, d4, d5, d6, d7, by rw [sp, sB]⟩

/-- **The `balanceOf(a)` frame of FiatTokenV2_1** keeps the storage. -/
theorem frame_balanceOf {post : Devm} (fork : CoveredFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0x70a08231)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    Devm.getStor post = Devm.getStor b := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ucall h hc 39 t_2798_c39
  have h2 := hc.cut
  clear hc
  repeat ustep h2
  obtain ⟨_, e⟩ := ric_ret h2
  clear h2
  cases e
  repeat ustep h
  rw [ric_return_getStor h]
  exact funext fun x => afterSload_getStor _ _ _ x

end Blanc.Lift.Usdc.ImplV2_1
