import Blanc.Lift.InvWalkLegacy
import Blanc.Lift.Dai.Check

/-!
# DAI: the frames of `transfer`, `transferFrom` and `balanceOf`, inverted

A successful `transfer` or `transferFrom` frame moves `v` from its source to its recipient with no
fee, after lowering a limited allowance when the spender is not the source.  `balanceOf` writes
nothing.
-/

namespace Blanc.Lift.Dai

open Jaune Blanc Blanc.Lift

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- The internal callees of `transfer`, `transferFrom` and `balanceOf`: none halts the frame. -/
def familyCallees : List Nat := [4, 5, 10, 29, 34, 36, 37]

theorem familyCallees_noHalt : NoHaltSet cert.prog familyCallees = true := by decide +kernel

/-- Enter callee entry `k` (tree `T`) of `familyCallees` from a cut run `h`. -/
macro "ucall " h:ident hc:ident k:num T:term : tactic => `(tactic|
  (have h' := ric_callR (k := $k) (g := $T) rfl
    (fun hh => SFunc.RunP.not_halted_entry familyCallees_noHalt
      (by decide : $k ∈ familyCallees) rfl hh rfl) $h
   clear $h
   obtain ⟨_, _, $hc:ident, $h:ident⟩ := h'))

/-- **Entry 36, `sub(x, y)`**: the result does not exceed `x`. -/
theorem e36_inv {y x ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (y :: x :: ret :: S) M G) t_1e77_c36 o) :
    ∃ G', o = .returned (St b ((x - y) :: S) M G') := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  cases e
  exact ⟨_, rfl⟩

/-- **Entry 37, `add(x, y)`**: no wrap. -/
theorem e37_inv {y x ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (y :: x :: ret :: S) M G) t_1e91_c37 o) :
    y.toNat + x.toNat < 2 ^ 256 ∧ ∃ G', o = .returned (St b ((x + y) :: S) M G') := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  cases e
  rw [B256.add_comm] at c
  exact ⟨(add_nof_of_ltCheck (eq_zero_of_iszero_ne_zero c)).1, _, by rw [B256.add_comm]⟩

/-! ## The ledger -/

/-- A balance entry (`balanceOf`, slot 2). -/
def balSlot (a : Adr) : B256 := mapSlot a.toB256 2

/-- An allowance entry (`allowance`, slot 3). -/
def allowSlot (o s : Adr) : B256 := mapSlot s.toB256 (mapSlot o.toB256 3)

/-- The allowance's "unlimited" sentinel, `uint(-1)`. -/
def maxUint : B256 := Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
  255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

/-- The move of `v` from `src` to `dst`. -/
def moveStor (σ : Stor) (src dst : Adr) (v : B256) : Stor :=
  (σ.set (balSlot src) (σ.get (balSlot src) - v)).set (balSlot dst)
    ((σ.set (balSlot src) (σ.get (balSlot src) - v)).get (balSlot dst) + v)

/-- The allowance step: a spender other than the source, with a limited allowance, spends `v`. -/
def spendStor (σ : Stor) (src s : Adr) (v : B256) : Stor :=
  if src ≠ s ∧ σ.get (allowSlot src s) ≠ maxUint then
    σ.set (allowSlot src s) (σ.get (allowSlot src s) - v)
  else σ

theorem lit2 : Bytes.toB256 [2] = 2 := by decide
theorem lit3 : Bytes.toB256 [3] = 3 := by decide

/-- The word normal form of a DAI walk's stack and facts. -/
macro "unorm " h:ident : tactic => `(tactic|
  (simp (config := { failIfUnchanged := false }) only [keccak_u, ff20_and_word, word_ff20,
     toAdr_toB256, getStorVal_afterSload, lit2, lit3, afterSstore_getStor_self,
     AccumulatedWalk.getStorVal_afterSstore_self, afterSload_getStor, gsv] at $h:ident
   simp (config := { failIfUnchanged := false }) only [lit0] at $h:ident))

/-- `unorm` and `umem`, across a segment. -/
macro "useg " h:ident : tactic => `(tactic|
  (repeat ustep $h
   unorm $h
   umem $h))

/-- **Tree `0x0db2` of entry 5, the move**. -/
theorem e5_inv {p v t r ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (h : SFunc.RunCut cert.prog sevm []
      (St b (p :: v :: t :: r :: ret :: S) M G) t_0db2_c5 (Seg.done o)) :
    v.toNat + (((Devm.getStor b sevm.currentTarget).set (balSlot r.toAdr)
        ((Devm.getStor b sevm.currentTarget).get (balSlot r.toAdr) - v)).get (balSlot t.toAdr)).toNat <
      2 ^ 256 ∧
      ∃ b' M' G', o = .returned (St b' (Bytes.toB256 [1] :: S) M' G') ∧
        Devm.getStor b' sevm.currentTarget =
          moveStor (Devm.getStor b sevm.currentTarget) r.toAdr t.toAdr v := by
  useg h
  ucall h hc 36 t_1e77_c36
  obtain ⟨G1, e⟩ := e36_inv fork hc
  cases e
  clear hc
  useg h
  ucall h hc 37 t_1e91_c37
  obtain ⟨c2, G2, e⟩ := e37_inv fork hc
  cases e
  clear hc
  unorm c2
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
  clear e
  refine ⟨c2, B, MB, GB, eo, ?_⟩
  rw [sB]
  simp only [Devm.addLog_getStor, afterSstore_getStor_self, afterSload_getStor, keccak_u,
    ff20_and_word, toAdr_toB256, lit2]
  rfl

/-- **Entry 34, `transferFrom(src, dst, wad)`**. -/
theorem e34_inv {v t r ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (v :: t :: r :: ret :: S) M G) t_0a25_c34 o) :
    v.toNat ≤ ((Devm.getStor b sevm.currentTarget).get (balSlot r.toAdr)).toNat ∧
      (r.toAdr ≠ sevm.caller →
        (Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sevm.caller) ≠ maxUint →
        v.toNat ≤ ((Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sevm.caller)).toNat) ∧
      v.toNat + (((spendStor (Devm.getStor b sevm.currentTarget) r.toAdr sevm.caller v).set
        (balSlot r.toAdr) ((spendStor (Devm.getStor b sevm.currentTarget) r.toAdr sevm.caller v).get
          (balSlot r.toAdr) - v)).get (balSlot t.toAdr)).toNat < 2 ^ 256 ∧
      ∃ b' M' G', o = .returned (St b' (Bytes.toB256 [1] :: S) M' G') ∧
        Devm.getStor b' sevm.currentTarget =
          moveStor (spendStor (Devm.getStor b sevm.currentTarget) r.toAdr sevm.caller v)
            r.toAdr t.toAdr v := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  unorm c1
  have hle : v.toNat ≤ ((Devm.getStor b sevm.currentTarget).get (balSlot r.toAdr)).toNat :=
    toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero c1)
  clear c1
  useg h
  repeat ustep h
  unorm h
  ubranchTo h c2
  · repeat ustep h
    unorm h
    umem h
    ubranchTo h c3
    · repeat ustep h
      ibranch h c4
      useg h
      ucall h hc 36 t_1e77_c36
      obtain ⟨G1, e⟩ := e36_inv fork hc
      cases e
      clear hc
      iterate 40 ustep h
      unorm h
      have e5 := e5_inv fork h
      clear h
      simp only [afterSstore_getStor_self, afterSload_getStor] at e5
      unorm c4
      have hne : r.toAdr ≠ sevm.caller := fun e => ne_of_iszero3 c2 (congrArg Adr.toB256 e)
      have hnm : (Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sevm.caller) ≠ maxUint :=
        ne_of_iszero3 c3
      have hs : spendStor (Devm.getStor b sevm.currentTarget) r.toAdr sevm.caller v =
          (Devm.getStor b sevm.currentTarget).set (allowSlot r.toAdr sevm.caller)
            ((Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sevm.caller) - v) := by
        unfold spendStor
        rw [if_pos ⟨hne, hnm⟩]
      rw [hs]
      exact ⟨hle, fun _ _ => toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero c4), e5⟩
    · have e5 := e5_inv fork h
      clear h
      simp only [afterSload_getStor] at e5
      have hm : (Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sevm.caller) = maxUint :=
        eq_of_iszero3 c3
      have hs : spendStor (Devm.getStor b sevm.currentTarget) r.toAdr sevm.caller v =
          Devm.getStor b sevm.currentTarget := by
        unfold spendStor
        rw [if_neg (fun hh => hh.2 hm)]
      rw [hs]
      exact ⟨hle, fun _ hnm => absurd hm hnm, e5⟩
  · repeat ustep h
    ubranchTo h c3
    · exact absurd c3 c2
    · have e5 := e5_inv fork h
      clear h
      simp only [afterSload_getStor] at e5
      have hre : r.toAdr = sevm.caller := by
        have := eq_of_iszero3 c2
        simpa only [toAdr_toB256] using congrArg B256.toAdr this
      have hs : spendStor (Devm.getStor b sevm.currentTarget) r.toAdr sevm.caller v =
          Devm.getStor b sevm.currentTarget := by
        unfold spendStor
        rw [if_neg (fun hh => hh.1 hre)]
      rw [hs]
      exact ⟨hle, fun hne => absurd hre hne, e5⟩

/-- **Entry 10, `transfer(dst, wad)`**: `transferFrom(msg.sender, dst, wad)`. -/
theorem e10_inv {v t ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (v :: t :: ret :: S) M G) t_1df4_c10 o) :
    v.toNat ≤ ((Devm.getStor b sevm.currentTarget).get (balSlot sevm.caller)).toNat ∧
      v.toNat + (((Devm.getStor b sevm.currentTarget).set (balSlot sevm.caller)
        ((Devm.getStor b sevm.currentTarget).get (balSlot sevm.caller) - v)).get
          (balSlot t.toAdr)).toNat < 2 ^ 256 ∧
      ∃ b' M' G', o = .returned (St b' (Bytes.toB256 [1] :: S) M' G') ∧
        Devm.getStor b' sevm.currentTarget =
          moveStor (Devm.getStor b sevm.currentTarget) sevm.caller t.toAdr v := by
  have h := run.cut
  clear run
  repeat ustep h
  ucall h hc 34 t_0a25_c34
  obtain ⟨d1, -, d2, B, MB, GB, e, sB⟩ := e34_inv fork hc
  cases e
  clear hc
  have hs : spendStor (Devm.getStor b sevm.currentTarget) sevm.caller sevm.caller v =
      Devm.getStor b sevm.currentTarget := by
    unfold spendStor
    rw [if_neg (fun hh => hh.1 rfl)]
  simp only [toAdr_toB256, hs] at d1 d2 sB
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B', MB', GB', eo, sB'⟩ := ret_named e
  exact ⟨d1, d2, B', MB', GB', eo, by rw [sB', sB]⟩

/-- The prologue through the selector, a macro over the cut run `h`. -/
macro "uhead " h:ident sel:ident : tactic => `(tactic|
  (iterate 7 ustep $h
   ibranch $h c0
   iterate 6 ustep $h
   ibranch $h c0'
   iterate 4 ustep $h
   rw [shr_selector_word, $sel:ident] at $h:ident
   repeat udisp $h))

theorem lit4 : Bytes.toB256 [4] = 4 := by decide
theorem lit36 : Bytes.toB256 [32] + Bytes.toB256 [4] = 36 := by decide

/-- **The `transfer(to, v)` frame of DAI.** -/
theorem frame_transfer {post : Devm} (fork : CoveredFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0xa9059cbb)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    (Sevm.dataWord sevm 36).toNat ≤
        ((Devm.getStor b sevm.currentTarget).get (balSlot sevm.caller)).toNat ∧
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
  ucall h hc 10 t_1df4_c10
  obtain ⟨d1, d2, B, MB, GB, e, sB⟩ := e10_inv fork hc
  cases e
  clear hc
  repeat ustep h
  have sp := ric_return_getStor h
  clear h
  simp only [lit36] at d1 d2 sB
  simp only [ff20_and_word, toAdr_toB256, lit4] at d1 d2 sB
  exact ⟨d1, d2, by rw [sp, sB]⟩

/-- **The `transferFrom(r, to, v)` frame of DAI.** -/
theorem frame_transferFrom {post : Devm} (fork : CoveredFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0x23b872dd)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    (Sevm.dataWord sevm 68).toNat ≤
        ((Devm.getStor b sevm.currentTarget).get (balSlot (Sevm.dataWord sevm 4).toAdr)).toNat ∧
      ((Sevm.dataWord sevm 4).toAdr ≠ sevm.caller →
        (Devm.getStor b sevm.currentTarget).get (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller) ≠ maxUint →
        (Sevm.dataWord sevm 68).toNat ≤
          ((Devm.getStor b sevm.currentTarget).get (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller)).toNat) ∧
      (Sevm.dataWord sevm 68).toNat + (((spendStor (Devm.getStor b sevm.currentTarget)
          (Sevm.dataWord sevm 4).toAdr sevm.caller (Sevm.dataWord sevm 68)).set
        (balSlot (Sevm.dataWord sevm 4).toAdr)
        ((spendStor (Devm.getStor b sevm.currentTarget) (Sevm.dataWord sevm 4).toAdr sevm.caller
          (Sevm.dataWord sevm 68)).get (balSlot (Sevm.dataWord sevm 4).toAdr) - Sevm.dataWord sevm 68)).get
          (balSlot (Sevm.dataWord sevm 36).toAdr)).toNat < 2 ^ 256 ∧
      Devm.getStor post sevm.currentTarget =
        moveStor (spendStor (Devm.getStor b sevm.currentTarget) (Sevm.dataWord sevm 4).toAdr sevm.caller
          (Sevm.dataWord sevm 68)) (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr
          (Sevm.dataWord sevm 68) := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ucall h hc 34 t_0a25_c34
  obtain ⟨d1, d0, d2, B, MB, GB, e, sB⟩ := e34_inv fork hc
  cases e
  clear hc
  repeat ustep h
  have sp := ric_return_getStor h
  clear h
  simp only [lit36, show Bytes.toB256 [32] + 36 = 68 by decide] at d0 d1 d2 sB
  simp only [ff20_and_word, toAdr_toB256, lit4] at d0 d1 d2 sB
  exact ⟨d1, d0, d2, by rw [sp, sB]⟩

/-- **The `balanceOf(a)` frame of DAI** keeps the storage. -/
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
  ucall h hc 29 t_128f_c29
  have h2 := hc.cut
  clear hc
  repeat ustep h2
  obtain ⟨_, e⟩ := ric_ret h2
  clear h2
  cases e
  repeat ustep h
  rw [ric_return_getStor h]
  exact funext fun x => afterSload_getStor _ _ _ x

/-! ## Credits: a move lowers only its source -/

/-- **A move does not lower any slot but its source's entry.** -/
theorem moveStor_ge {σ : Stor} {src dst : Adr} {v k : B256}
    (hnof : v.toNat + ((σ.set (balSlot src) (σ.get (balSlot src) - v)).get (balSlot dst)).toNat < 2 ^ 256)
    (hk : k ≠ balSlot src) :
    (σ.get k).toNat ≤ ((moveStor σ src dst v).get k).toNat := by
  unfold moveStor
  by_cases hkd : k = balSlot dst
  · subst hkd
    rw [Stor.get_set_self, Stor.get_set_ne _ (Ne.symm hk)] at *
    have hn : (σ.get (balSlot dst)).toNat + v.toNat < 2 ^ 256 := by omega
    rw [B256.toNat_add_eq_of_nof _ _ hn]
    omega
  · rw [Stor.get_set_ne _ (Ne.symm hkd), Stor.get_set_ne _ (Ne.symm hk)]

end Blanc.Lift.Dai
