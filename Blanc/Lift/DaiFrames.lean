import Blanc.Lift.InvWalkLegacy
import Blanc.Lift.Dai.Check

/-!
# DAI: the frames that touch a balance entry, inverted, over every historical fork

A successful `transfer`, `transferFrom`, `push`, `pull` or `move` frame moves `v` from its source to its
recipient with no fee, after lowering a limited allowance when the spender is not the source
(`FromLaw`).  `mint` credits and `burn` debits an entry and the supply word; `mint`'s ward check is not
stated.  `balanceOf` writes nothing.
-/

namespace Blanc.Lift.Dai

open Jaune Blanc Blanc.Lift

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- The internal callees of `transfer`, `transferFrom` and `balanceOf`: none halts the frame. -/
def familyCallees : List Nat := [4, 5, 8, 9, 10, 11, 12, 15, 22, 25, 29, 34, 36, 37]

theorem familyCallees_noHalt : NoHaltSet cert.prog familyCallees = true := by decide +kernel

/-- Enter callee entry `k` (tree `T`) of `familyCallees` from a cut run `h`. -/
macro "ucall " h:ident hc:ident k:num T:term : tactic => `(tactic|
  (have h' := ric_callR (k := $k) (g := $T) rfl
    (fun hh => SFunc.RunP.not_halted_entry familyCallees_noHalt
      (by decide : $k ∈ familyCallees) rfl hh rfl) $h
   clear $h
   obtain ⟨_, _, $hc:ident, $h:ident⟩ := h'))

/-- **Entry 36, `sub(x, y)`**: the result does not exceed `x`. -/
theorem e36_inv {y x ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
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
theorem e37_inv {y x ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
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
     toAdr_toB256, getStorVal_afterSloadH, lit2, lit3, afterSstoreH_getStor_self,
     afterSloadH_getStor, gsv] at $h:ident
   simp (config := { failIfUnchanged := false }) only [lit0] at $h:ident))

/-- `unorm` and `umem`, across a segment. -/
macro "useg " h:ident : tactic => `(tactic|
  (repeat ustep $h
   unorm $h
   umem $h))

/-- **Tree `0x0db2` of entry 5, the move**. -/
theorem e5_inv {p v t r ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
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
  simp only [Devm.addLog_getStor, afterSstoreH_getStor_self, afterSloadH_getStor, keccak_u,
    ff20_and_word, toAdr_toB256, lit2]
  rfl

/-- **Entry 34, `transferFrom(src, dst, wad)`**. -/
theorem e34_inv {v t r ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
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
      simp only [afterSstoreH_getStor_self, afterSloadH_getStor] at e5
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
      simp only [afterSloadH_getStor] at e5
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
      simp only [afterSloadH_getStor] at e5
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
theorem e10_inv {v t ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
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
theorem frame_transfer {post : Devm} (fork : HistFork sevm.benvStat.fork)
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
theorem frame_transferFrom {post : Devm} (fork : HistFork sevm.benvStat.fork)
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
theorem frame_balanceOf {post : Devm} (fork : HistFork sevm.benvStat.fork)
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
  exact funext fun x => afterSloadH_getStor _ _ _ x

/-- **What a move through `transferFrom` does**: the source covers it, a limited allowance covers it
for a spender other than the source, the recipient does not wrap, and the storage moves. -/
structure FromLaw (σ σ' : Stor) (src spender dst : Adr) (v : B256) : Prop where
  covered : v.toNat ≤ (σ.get (balSlot src)).toNat
  allowed : src ≠ spender → σ.get (allowSlot src spender) ≠ maxUint →
    v.toNat ≤ (σ.get (allowSlot src spender)).toNat
  fits : v.toNat + (((spendStor σ src spender v).set (balSlot src)
    ((spendStor σ src spender v).get (balSlot src) - v)).get (balSlot dst)).toNat < 2 ^ 256
  stor : σ' = moveStor (spendStor σ src spender v) src dst v

/-- **Entry 11, `push(usr, wad)`**: `transferFrom(msg.sender, usr, wad)`. -/
theorem e11_inv {v t ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (v :: t :: ret :: S) M G) t_1e09_c11 o) :
    ∃ b' M' G', o = .returned (St b' S M' G') ∧
      FromLaw (Devm.getStor b sevm.currentTarget) (Devm.getStor b' sevm.currentTarget)
        sevm.caller sevm.caller t.toAdr v := by
  have h := run.cut
  clear run
  repeat ustep h
  ucall h hc 34 t_0a25_c34
  obtain ⟨d1, d0, d2, B, MB, GB, e, sB⟩ := e34_inv fork hc
  cases e
  clear hc
  simp only [toAdr_toB256] at d0 d1 d2 sB
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B', MB', GB', eo, sB'⟩ := ret_named e
  exact ⟨B', MB', GB', eo, d1, d0, d2, by rw [sB', sB]⟩

/-- **Entry 12, `move(src, dst, wad)`**: `transferFrom(src, dst, wad)`. -/
theorem e12_inv {v t r ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (v :: t :: r :: ret :: S) M G) t_1e19_c12 o) :
    ∃ b' M' G', o = .returned (St b' S M' G') ∧
      FromLaw (Devm.getStor b sevm.currentTarget) (Devm.getStor b' sevm.currentTarget)
        r.toAdr sevm.caller t.toAdr v := by
  have h := run.cut
  clear run
  repeat ustep h
  ucall h hc 34 t_0a25_c34
  obtain ⟨d1, d0, d2, B, MB, GB, e, sB⟩ := e34_inv fork hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B', MB', GB', eo, sB'⟩ := ret_named e
  exact ⟨B', MB', GB', eo, d1, d0, d2, by rw [sB', sB]⟩

/-- **Entry 15, `pull(usr, wad)`**: `transferFrom(usr, msg.sender, wad)`. -/
theorem e15_inv {v r ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (v :: r :: ret :: S) M G) t_1e67_c15 o) :
    ∃ b' M' G', o = .returned (St b' S M' G') ∧
      FromLaw (Devm.getStor b sevm.currentTarget) (Devm.getStor b' sevm.currentTarget)
        r.toAdr sevm.caller sevm.caller v := by
  have h := run.cut
  clear run
  repeat ustep h
  ucall h hc 34 t_0a25_c34
  obtain ⟨d1, d0, d2, B, MB, GB, e, sB⟩ := e34_inv fork hc
  cases e
  clear hc
  simp only [toAdr_toB256] at d0 d1 d2 sB
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B', MB', GB', eo, sB'⟩ := ret_named e
  exact ⟨B', MB', GB', eo, d1, d0, d2, by rw [sB', sB]⟩

/-- The burn of `v` from `u`: its entry and the supply word (slot 1) fall. -/
def burnStor (σ : Stor) (u : Adr) (v : B256) : Stor :=
  (σ.set (balSlot u) (σ.get (balSlot u) - v)).set 1 ((σ.set (balSlot u) (σ.get (balSlot u) - v)).get 1 - v)

/-- The mint of `v` to `u`: its entry and the supply word rise. -/
def mintStor (σ : Stor) (u : Adr) (v : B256) : Stor :=
  (σ.set (balSlot u) (σ.get (balSlot u) + v)).set 1 ((σ.set (balSlot u) (σ.get (balSlot u) + v)).get 1 + v)

theorem lit1 : Bytes.toB256 [1] = 1 := by decide

/-- **Tree `0x1cec` of entry 9, `burn`'s debit.** -/
theorem e9_inv {v u ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (h : SFunc.RunCut cert.prog sevm [] (St b (v :: u :: ret :: S) M G) t_1cec_c9 (Seg.done o)) :
    ∃ b' M' G', o = .returned (St b' S M' G') ∧
      Devm.getStor b' sevm.currentTarget = burnStor (Devm.getStor b sevm.currentTarget) u.toAdr v := by
  useg h
  ucall h hc 36 t_1e77_c36
  obtain ⟨G1, e⟩ := e36_inv fork hc
  cases e
  clear hc
  useg h
  ucall h hc 36 t_1e77_c36
  obtain ⟨G2, e⟩ := e36_inv fork hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
  clear e
  refine ⟨B, MB, GB, eo, ?_⟩
  rw [sB]
  simp only [Devm.addLog_getStor, afterSstoreH_getStor_self, afterSloadH_getStor, keccak_u,
    ff20_and_word, toAdr_toB256, lit2, lit1, gsv]
  rfl

/-- **Entry 22, `burn(usr, wad)`.** -/
theorem e22_inv {v u ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (v :: u :: ret :: S) M G) t_1961_c22 o) :
    v.toNat ≤ ((Devm.getStor b sevm.currentTarget).get (balSlot u.toAdr)).toNat ∧
      (u.toAdr ≠ sevm.caller →
        (Devm.getStor b sevm.currentTarget).get (allowSlot u.toAdr sevm.caller) ≠ maxUint →
        v.toNat ≤ ((Devm.getStor b sevm.currentTarget).get (allowSlot u.toAdr sevm.caller)).toNat) ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧
        Devm.getStor b' sevm.currentTarget =
          burnStor (spendStor (Devm.getStor b sevm.currentTarget) u.toAdr sevm.caller v) u.toAdr v := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  unorm c1
  have hle : v.toNat ≤ ((Devm.getStor b sevm.currentTarget).get (balSlot u.toAdr)).toNat :=
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
      have e9 := e9_inv fork h
      clear h
      simp only [afterSstoreH_getStor_self, afterSloadH_getStor] at e9
      unorm c4
      have hne : u.toAdr ≠ sevm.caller := fun e => ne_of_iszero3 c2 (congrArg Adr.toB256 e)
      have hnm : (Devm.getStor b sevm.currentTarget).get (allowSlot u.toAdr sevm.caller) ≠ maxUint :=
        ne_of_iszero3 c3
      have hs : spendStor (Devm.getStor b sevm.currentTarget) u.toAdr sevm.caller v =
          (Devm.getStor b sevm.currentTarget).set (allowSlot u.toAdr sevm.caller)
            ((Devm.getStor b sevm.currentTarget).get (allowSlot u.toAdr sevm.caller) - v) := by
        unfold spendStor
        rw [ite_eq_left ⟨hne, hnm⟩]
      rw [hs]
      exact ⟨hle, fun _ _ => toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero c4), e9⟩
    · have e9 := e9_inv fork h
      clear h
      simp only [afterSloadH_getStor] at e9
      have hm : (Devm.getStor b sevm.currentTarget).get (allowSlot u.toAdr sevm.caller) = maxUint :=
        eq_of_iszero3 c3
      have hs : spendStor (Devm.getStor b sevm.currentTarget) u.toAdr sevm.caller v =
          Devm.getStor b sevm.currentTarget := by
        unfold spendStor
        rw [ite_eq_right (fun hh => hh.2 hm)]
      rw [hs]
      exact ⟨hle, fun _ hnm => absurd hm hnm, e9⟩
  · repeat ustep h
    ubranchTo h c3
    · exact absurd c3 c2
    · have e9 := e9_inv fork h
      clear h
      simp only [afterSloadH_getStor] at e9
      have hre : u.toAdr = sevm.caller := by
        have := eq_of_iszero3 c2
        simpa only [toAdr_toB256] using congrArg B256.toAdr this
      have hs : spendStor (Devm.getStor b sevm.currentTarget) u.toAdr sevm.caller v =
          Devm.getStor b sevm.currentTarget := by
        unfold spendStor
        rw [ite_eq_right (fun hh => hh.1 hre)]
      rw [hs]
      exact ⟨hle, fun hne => absurd hre hne, e9⟩

/-- **Entry 25, `mint(usr, wad)`.** The ward check is not stated; a credit is all this says. -/
theorem e25_inv {v u ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (v :: u :: ret :: S) M G) t_0f6c_c25 o) :
    v.toNat + ((Devm.getStor b sevm.currentTarget).get (balSlot u.toAdr)).toNat < 2 ^ 256 ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧
        Devm.getStor b' sevm.currentTarget =
          mintStor (Devm.getStor b sevm.currentTarget) u.toAdr v := by
  have h := run.cut
  clear run
  useg h
  ibranch h c1
  useg h
  ucall h hc 37 t_1e91_c37
  obtain ⟨c2, G2, e⟩ := e37_inv fork hc
  cases e
  clear hc
  unorm c2
  useg h
  ucall h hc 37 t_1e91_c37
  obtain ⟨-, G3, e⟩ := e37_inv fork hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
  clear e
  refine ⟨c2, B, MB, GB, eo, ?_⟩
  rw [sB]
  simp only [Devm.addLog_getStor, afterSstoreH_getStor_self, afterSloadH_getStor, keccak_u,
    ff20_and_word, toAdr_toB256, lit2, lit1, gsv]
  rfl

theorem lit68 : Bytes.toB256 [32] + 36 = 68 := by decide

theorem lit36' : Bytes.toB256 [32] + 4 = 36 := by decide

/-- **The `push(usr, wad)` frame of DAI.** -/
theorem frame_push {post : Devm} (fork : HistFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0xb753a98c)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    FromLaw (Devm.getStor b sevm.currentTarget) (Devm.getStor post sevm.currentTarget)
      sevm.caller sevm.caller (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36) := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ucall h hc 11 t_1e09_c11
  obtain ⟨B, MB, GB, e, law⟩ := e11_inv fork hc
  cases e
  clear hc
  repeat ustep h
  have sp := ric_stop_keeps h
  clear h
  simp only [lit36, lit36', ff20_and_word, toAdr_toB256, lit4] at law
  rw [sp]
  exact law

/-- **The `pull(usr, wad)` frame of DAI.** -/
theorem frame_pull {post : Devm} (fork : HistFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0xf2d5d56b)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    FromLaw (Devm.getStor b sevm.currentTarget) (Devm.getStor post sevm.currentTarget)
      (Sevm.dataWord sevm 4).toAdr sevm.caller sevm.caller (Sevm.dataWord sevm 36) := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ucall h hc 15 t_1e67_c15
  obtain ⟨B, MB, GB, e, law⟩ := e15_inv fork hc
  cases e
  clear hc
  repeat ustep h
  have sp := ric_stop_keeps h
  clear h
  simp only [lit36, lit36', ff20_and_word, toAdr_toB256, lit4] at law
  rw [sp]
  exact law

/-- **The `move(src, dst, wad)` frame of DAI.** -/
theorem frame_move {post : Devm} (fork : HistFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0xbb35783b)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    FromLaw (Devm.getStor b sevm.currentTarget) (Devm.getStor post sevm.currentTarget)
      (Sevm.dataWord sevm 4).toAdr sevm.caller (Sevm.dataWord sevm 36).toAdr
      (Sevm.dataWord sevm 68) := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ucall h hc 12 t_1e19_c12
  obtain ⟨B, MB, GB, e, law⟩ := e12_inv fork hc
  cases e
  clear hc
  repeat ustep h
  have sp := ric_stop_keeps h
  clear h
  simp only [lit36, lit36', lit68, ff20_and_word, toAdr_toB256, lit4] at law
  rw [sp]
  exact law

/-- **The `burn(usr, wad)` frame of DAI.** -/
theorem frame_burn {post : Devm} (fork : HistFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0x9dc29fac)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    (Sevm.dataWord sevm 36).toNat ≤
        ((Devm.getStor b sevm.currentTarget).get (balSlot (Sevm.dataWord sevm 4).toAdr)).toNat ∧
      ((Sevm.dataWord sevm 4).toAdr ≠ sevm.caller →
        (Devm.getStor b sevm.currentTarget).get (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller) ≠
          maxUint →
        (Sevm.dataWord sevm 36).toNat ≤
          ((Devm.getStor b sevm.currentTarget).get
            (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller)).toNat) ∧
      Devm.getStor post sevm.currentTarget =
        burnStor (spendStor (Devm.getStor b sevm.currentTarget) (Sevm.dataWord sevm 4).toAdr sevm.caller
          (Sevm.dataWord sevm 36)) (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36) := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ucall h hc 22 t_1961_c22
  obtain ⟨d1, d0, B, MB, GB, e, sB⟩ := e22_inv fork hc
  cases e
  clear hc
  repeat ustep h
  have sp := ric_stop_keeps h
  clear h
  simp only [lit36, lit36', ff20_and_word, toAdr_toB256, lit4] at d0 d1 sB
  exact ⟨d1, d0, by rw [sp, sB]⟩

/-- **The `mint(usr, wad)` frame of DAI.** -/
theorem frame_mint {post : Devm} (fork : HistFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0x40c10f19)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    (Sevm.dataWord sevm 36).toNat +
        ((Devm.getStor b sevm.currentTarget).get (balSlot (Sevm.dataWord sevm 4).toAdr)).toNat < 2 ^ 256 ∧
      Devm.getStor post sevm.currentTarget =
        mintStor (Devm.getStor b sevm.currentTarget) (Sevm.dataWord sevm 4).toAdr
          (Sevm.dataWord sevm 36) := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ucall h hc 25 t_0f6c_c25
  obtain ⟨d1, B, MB, GB, e, sB⟩ := e25_inv fork hc
  cases e
  clear hc
  repeat ustep h
  have sp := ric_stop_keeps h
  clear h
  simp only [lit36, lit36', ff20_and_word, toAdr_toB256, lit4] at d1 sB
  exact ⟨d1, by rw [sp, sB]⟩

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
