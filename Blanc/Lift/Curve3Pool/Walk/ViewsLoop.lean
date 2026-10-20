import Blanc.Lift.FrameWalkKit
import Blanc.Lift.VyperFrameLoop
import Blanc.Lift.VyperCallee

/-!
# Vyper's frame save and restore loops on the actual derivation

Around an internal call Vyper saves the caller's frame `[lo, e)` on the stack with a counter
loop (`frameSaveIter`'s instructions) and restores it with another (`frameRestoreIter`'s). On
the actual derivation (`XAt`) the loops run iteration by iteration:

* `SaveAt cd H t`/`RestoreAt cd H t`: the loop's instructions at head `H` (template `t`, as in
  `Blanc/Lift/VyperFrameLoop.lean`), and its exit `JUMPDEST`;
* `xa_saveIter`/`xa_restoreIter`: one iteration;
* `xa_frameSave`: the whole save loop pushes `frameWords M lo n` (lowest deepest) and leaves
  `saveMem` (the counter rewritten);
* `xa_frameRestore`: the whole restore loop writes the stack words back (`restoreMem`).

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- The save loop's instructions at head `H`, its back edge to `H` and its exit `JUMPDEST`. -/
structure SaveAt (cd : ByteArray) (H : Nat) (t : FrameLoopTpl) : Prop where
  i0 : Jinst.At cd H .jumpdest
  i1 : Ninst.At cd (H + 1) (.push [t.c0, t.c1] (frameLoop_len2 t.c0 t.c1))
  i2 : Ninst.At cd (H + 4) (.reg .mload)
  i3 : Ninst.At cd (H + 5) (.reg .mload)
  i4 : Ninst.At cd (H + 6) (.push [0x20] (by decide))
  i5 : Ninst.At cd (H + 8) (.push [t.c0, t.c1] (frameLoop_len2 t.c0 t.c1))
  i6 : Ninst.At cd (H + 11) (.reg .mload)
  i7 : Ninst.At cd (H + 12) (.reg .add)
  i8 : Ninst.At cd (H + 13) (.push [t.c0, t.c1] (frameLoop_len2 t.c0 t.c1))
  i9 : Ninst.At cd (H + 16) (.reg .mstore)
  i10 : Ninst.At cd (H + 17) (.push [t.e0, t.e1] (frameLoop_len2 t.e0 t.e1))
  i11 : Ninst.At cd (H + 20) (.push [t.c0, t.c1] (frameLoop_len2 t.c0 t.c1))
  i12 : Ninst.At cd (H + 23) (.reg .mload)
  i13 : Ninst.At cd (H + 24) (.reg .lt)
  i14 : Ninst.At cd (H + 25) (.reg .iszero)
  i15 : Ninst.At cd (H + 26) (.push [t.x0, t.x1] (frameLoop_len2 t.x0 t.x1))
  i16 : Jinst.At cd (H + 29) .jumpi
  i17 : Ninst.At cd (H + 30) (.push [t.h0, t.h1] (frameLoop_len2 t.h0 t.h1))
  i18 : Jinst.At cd (H + 33) .jump
  ix : Jinst.At cd (Bytes.toB256 [t.x0, t.x1]).toNat .jumpdest
  hh : (Bytes.toB256 [t.h0, t.h1]).toNat = H

/-- The restore loop's instructions at head `H` (bound `t.e` the frame's start), its back edge
to `H` and its exit `JUMPDEST`. -/
structure RestoreAt (cd : ByteArray) (H : Nat) (t : FrameLoopTpl) : Prop where
  i0 : Jinst.At cd H .jumpdest
  i1 : Ninst.At cd (H + 1) (.push [t.c0, t.c1] (frameLoop_len2 t.c0 t.c1))
  i2 : Ninst.At cd (H + 4) (.reg .mload)
  i3 : Ninst.At cd (H + 5) (.reg .mstore)
  i4 : Ninst.At cd (H + 6) (.push [0x20] (by decide))
  i5 : Ninst.At cd (H + 8) (.push [t.c0, t.c1] (frameLoop_len2 t.c0 t.c1))
  i6 : Ninst.At cd (H + 11) (.reg .mload)
  i7 : Ninst.At cd (H + 12) (.reg .sub)
  i8 : Ninst.At cd (H + 13) (.push [t.c0, t.c1] (frameLoop_len2 t.c0 t.c1))
  i9 : Ninst.At cd (H + 16) (.reg .mstore)
  i10 : Ninst.At cd (H + 17) (.push [t.e0, t.e1] (frameLoop_len2 t.e0 t.e1))
  i11 : Ninst.At cd (H + 20) (.push [t.c0, t.c1] (frameLoop_len2 t.c0 t.c1))
  i12 : Ninst.At cd (H + 23) (.reg .mload)
  i13 : Ninst.At cd (H + 24) (.reg .lt)
  i14 : Ninst.At cd (H + 25) (.reg .iszero)
  i15 : Ninst.At cd (H + 26) (.reg .iszero)
  i16 : Ninst.At cd (H + 27) (.push [t.x0, t.x1] (frameLoop_len2 t.x0 t.x1))
  i17 : Jinst.At cd (H + 30) .jumpi
  i18 : Ninst.At cd (H + 31) (.push [t.h0, t.h1] (frameLoop_len2 t.h0 t.h1))
  i19 : Jinst.At cd (H + 34) .jump
  ix : Jinst.At cd (Bytes.toB256 [t.x0, t.x1]).toNat .jumpdest
  hh : (Bytes.toB256 [t.h0, t.h1]).toNat = H

/-- The exit tag. -/
abbrev FrameLoopTpl.x (t : FrameLoopTpl) : Nat := (Bytes.toB256 [t.x0, t.x1]).toNat

set_option hygiene false in
/-- One non-spawning instruction from an `At` fact `hat`, inverted by `ri`. -/
local macro "ys " hat:term:max ri:term:max : tactic => `(tactic| (
  replace h := xa_next $hat (by nofun) h
  obtain ⟨_, s, h⟩ := h
  obtain ⟨_, rfl⟩ := $ri s
  clear s))

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {S : List B256} {M : Mem}
  {G H : Nat} {t : FrameLoopTpl}

/-- **One save iteration** on the actual derivation: the word at the counter's value `p` is
pushed, the counter becomes `p + 32`, and the walk is back at the head while `p + 32 < e`, else
past the exit `JUMPDEST`. -/
theorem xa_saveIter (hat : SaveAt sevm.code H t) {p : Nat}
    (hsz : M.size % 32 = 0) (hcs : t.c + 32 ≤ M.size)
    (hps : p + 32 ≤ M.size) (hp : p + 32 < 2 ^ 256)
    (hctr : memWord M t.c = Nat.toB256 p)
    (h : XAt sevm post H (St b S M G) L) :
    ∃ G', (p + 32 < t.e ∧ XAt sevm post H (St b (memWord M p :: S)
        (M.write t.c (Nat.toB256 (p + 32)).toBytes) G') L) ∨
      (¬ p + 32 < t.e ∧ XAt sevm post (t.x + 1) (St b (memWord M p :: S)
        (M.write t.c (Nat.toB256 (p + 32)).toBytes) G') L) := by
  have hR : ∀ o, o + 32 ≤ M.size → (M.read o 32).2 = M := fun o ho => read_covered rfl hsz ho
  have hpn : (Nat.toB256 p).toNat = p := B256.toNat_toB256_of_lt (by omega)
  have hctr' : Bytes.toB256 (M.read (Bytes.toB256 [t.c0, t.c1]).toNat 32).1 = Nat.toB256 p := hctr
  have hM1 := Mem.size_write_word_of_add_le (v := Nat.toB256 (p + 32)) hcs
  have hc : t.c = (Bytes.toB256 [t.c0, t.c1]).toNat := rfl
  obtain ⟨_, h⟩ := xa_jumpdest_St hat.i0 h
  ys hat.i1 ri_push
  ys hat.i2 ri_mload
  rw [← hc, hR _ hcs, hc, hctr'] at h
  ys hat.i3 ri_mload
  rw [hpn, hR _ hps] at h
  ys hat.i4 ri_push
  ys hat.i5 ri_push
  ys hat.i6 ri_mload
  rw [← hc, hR _ hcs, hc, hctr'] at h
  ys hat.i7 ri_add
  rw [toB256_add_0x20 hp] at h
  ys hat.i8 ri_push
  ys hat.i9 ri_mstore
  ys hat.i10 ri_push
  ys hat.i11 ri_push
  ys hat.i12 ri_mload
  have hw : Bytes.toB256 ((M.write t.c (Nat.toB256 (p + 32)).toBytes).read t.c 32).1 =
      Nat.toB256 (p + 32) := (Mem.memWord_write_word M _ _).1
  rw [← hc, read_covered rfl (by rw [hM1]; exact hsz) (by rw [hM1]; exact hcs), hw] at h
  ys hat.i13 ri_lt
  ys hat.i14 ri_iszero
  ys hat.i15 ri_push
  rcases xa_jumpi_St hat.i16 h with ⟨hw, _, h⟩ | ⟨hw, _, h⟩
  · have hlt := ltCheck_iszero_eq hw
    rw [B256.toNat_toB256_of_lt hp] at hlt
    ys hat.i17 ri_push
    obtain ⟨G', h⟩ := xa_jump_St hat.i18 h
    rw [hat.hh] at h
    exact ⟨G', .inl ⟨hlt, h⟩⟩
  · have hlt := ltCheck_iszero_ne hw
    rw [B256.toNat_toB256_of_lt hp] at hlt
    obtain ⟨G', h⟩ := xa_jumpdest_St hat.ix h
    exact ⟨G', .inr ⟨hlt, h⟩⟩

private theorem xa_frameSave_aux (hat : SaveAt sevm.code H t) {lo n : Nat}
    (hsz : M.size % 32 = 0) (hcs : t.c + 32 ≤ M.size) (hctr : memWord M t.c = Nat.toB256 lo)
    (he : t.e = lo + 32 * n) (hreg : lo + 32 * n ≤ t.c) :
    ∀ k i G, i + k + 1 = n →
      XAt sevm post H (St b ((frameWords M lo i).reverse ++ S) (saveMem M t.c lo i) G) L →
      ∃ G', XAt sevm post (t.x + 1)
        (St b ((frameWords M lo n).reverse ++ S) (saveMem M t.c lo n) G') L := by
  have hc := t.c_lt
  intro k
  induction k with
  | zero =>
    intro i G hi h
    obtain ⟨G', ⟨hlt, -⟩ | ⟨-, h⟩⟩ := xa_saveIter (p := lo + 32 * i) hat
      (by rw [saveMem_size hcs]; exact hsz) (by rw [saveMem_size hcs]; exact hcs)
      (by rw [saveMem_size hcs]; omega) (by omega) (saveMem_ctr hctr i) h
    · omega
    · refine ⟨G', ?_⟩
      rw [saveMem_word (by omega) (by omega) i] at h
      rw [← hi, Nat.add_zero, frameWords_succ, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.cons_append]
      simpa only [saveMem, show lo + 32 * i + 32 = lo + 32 * (i + 1) by omega] using h
  | succ k ih =>
    intro i G hi h
    obtain ⟨G', ⟨-, h⟩ | ⟨hlt, -⟩⟩ := xa_saveIter (p := lo + 32 * i) hat
      (by rw [saveMem_size hcs]; exact hsz) (by rw [saveMem_size hcs]; exact hcs)
      (by rw [saveMem_size hcs]; omega) (by omega) (saveMem_ctr hctr i) h
    · rw [saveMem_word (by omega) (by omega) i] at h
      refine ih (i + 1) G' (by omega) ?_
      rw [frameWords_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.cons_append]
      simpa only [saveMem, show lo + 32 * i + 32 = lo + 32 * (i + 1) by omega] using h
    · omega

/-- **A save loop** on the actual derivation: from the head with the counter word at `t.c`
holding `lo` and the bound `t.e = lo + 32 n` (`0 < n`) below the counter, the walk leaves past
the exit `JUMPDEST` with the `n` frame words pushed (lowest deepest) and the counter at
`lo + 32 n` (`saveMem`). -/
theorem xa_frameSave (hat : SaveAt sevm.code H t) {lo n : Nat} (hn : 0 < n)
    (hsz : M.size % 32 = 0) (hcs : t.c + 32 ≤ M.size) (hctr : memWord M t.c = Nat.toB256 lo)
    (he : t.e = lo + 32 * n) (hreg : lo + 32 * n ≤ t.c)
    (h : XAt sevm post H (St b S M G) L) :
    ∃ G', XAt sevm post (t.x + 1)
      (St b ((frameWords M lo n).reverse ++ S) (saveMem M t.c lo n) G') L :=
  xa_frameSave_aux hat hsz hcs hctr he hreg (n - 1) 0 G (by omega) (by
    simpa only [frameWords, List.range_zero, List.map_nil, List.reverse_nil, List.nil_append,
      saveMem] using h)

/-- **One restore iteration** on the actual derivation: the stack top `w` is written at the
counter's value `p`, the counter becomes `p - 32`, and the walk is back at the head while
`lo ≤ p - 32`, else past the exit `JUMPDEST`. -/
theorem xa_restoreIter (hat : RestoreAt sevm.code H t) {p : Nat} {w : B256}
    (hsz : M.size % 32 = 0) (hcs : t.c + 32 ≤ M.size) (hpc : p + 32 ≤ t.c) (h32 : 32 ≤ p)
    (hctr : memWord M t.c = Nat.toB256 p)
    (h : XAt sevm post H (St b (w :: S) M G) L) :
    ∃ G', (¬ p - 32 < t.e ∧ XAt sevm post H (St b S ((M.write p w.toBytes).write
        t.c (Nat.toB256 (p - 32)).toBytes) G') L) ∨
      (p - 32 < t.e ∧ XAt sevm post (t.x + 1) (St b S ((M.write p w.toBytes).write
        t.c (Nat.toB256 (p - 32)).toBytes) G') L) := by
  have hcl := t.c_lt
  have hR : ∀ o, o + 32 ≤ M.size → (M.read o 32).2 = M := fun o ho => read_covered rfl hsz ho
  have hpn : (Nat.toB256 p).toNat = p := B256.toNat_toB256_of_lt (by omega)
  have hc : t.c = (Bytes.toB256 [t.c0, t.c1]).toNat := rfl
  have hctr' : Bytes.toB256 (M.read t.c 32).1 = Nat.toB256 p := hctr
  have hM1 : (M.write p w.toBytes).size = M.size := Mem.size_write_word_of_add_le (by omega)
  have hctr1 : Bytes.toB256 ((M.write p w.toBytes).read t.c 32).1 = Nat.toB256 p := by
    show memWord _ _ = _
    rw [memWord_write_of_disjoint hcs (by rw [B256.length_toBytes]; omega), hctr]
  have hM2 := Mem.size_write_word_of_add_le (M := M.write p w.toBytes) (v := Nat.toB256 (p - 32))
    (by rw [hM1]; exact hcs)
  have hw : Bytes.toB256 (((M.write p w.toBytes).write t.c (Nat.toB256 (p - 32)).toBytes).read
      t.c 32).1 = Nat.toB256 (p - 32) := (Mem.memWord_write_word _ _ _).1
  obtain ⟨_, h⟩ := xa_jumpdest_St hat.i0 h
  ys hat.i1 ri_push
  ys hat.i2 ri_mload
  rw [← hc, hR _ hcs, hctr'] at h
  ys hat.i3 ri_mstore
  rw [hpn] at h
  ys hat.i4 ri_push
  ys hat.i5 ri_push
  ys hat.i6 ri_mload
  rw [← hc, read_covered rfl (by rw [hM1]; exact hsz) (by rw [hM1]; exact hcs), hctr1] at h
  ys hat.i7 ri_sub
  rw [toB256_sub_0x20 h32 (by omega)] at h
  ys hat.i8 ri_push
  ys hat.i9 ri_mstore
  ys hat.i10 ri_push
  ys hat.i11 ri_push
  ys hat.i12 ri_mload
  rw [← hc, read_covered rfl (by rw [hM2, hM1]; exact hsz) (by rw [hM2, hM1]; exact hcs), hw] at h
  ys hat.i13 ri_lt
  ys hat.i14 ri_iszero
  ys hat.i15 ri_iszero
  ys hat.i16 ri_push
  rcases xa_jumpi_St hat.i17 h with ⟨hw0, _, h⟩ | ⟨hw0, _, h⟩
  · have hlt := ltCheck_eq_zero (eqCheck_ne_zero (eqCheck_zero_eq_zero hw0))
    rw [B256.toNat_toB256_of_lt (by omega)] at hlt
    ys hat.i18 ri_push
    obtain ⟨G', h⟩ := xa_jump_St hat.i19 h
    rw [hat.hh] at h
    exact ⟨G', .inl ⟨hlt, h⟩⟩
  · have hlt := ltCheck_ne_zero (eqCheck_zero_eq_zero (eqCheck_ne_zero hw0))
    rw [B256.toNat_toB256_of_lt (by omega)] at hlt
    obtain ⟨G', h⟩ := xa_jumpdest_St hat.ix h
    exact ⟨G', .inr ⟨hlt, h⟩⟩

theorem restoreMem_cons (c : Nat) (M : Mem) (p : Nat) (w : B256) (ws : List B256) :
    restoreMem c M p (w :: ws) =
      restoreMem c ((M.write p w.toBytes).write c (Nat.toB256 (p - 32)).toBytes) (p - 32) ws :=
  rfl

private theorem xa_frameRestore_aux (hat : RestoreAt sevm.code H t) {lo : Nat} (hlo : 32 ≤ lo)
    (he : t.e = lo) :
    ∀ (ts : List B256) (M : Mem) (G : Nat), ts ≠ [] → M.size % 32 = 0 → t.c + 32 ≤ M.size →
      lo + 32 * ts.length ≤ t.c → memWord M t.c = Nat.toB256 (lo + 32 * (ts.length - 1)) →
      XAt sevm post H (St b (ts ++ S) M G) L →
      ∃ G', XAt sevm post (t.x + 1)
        (St b S (restoreMem t.c M (lo + 32 * (ts.length - 1)) ts) G') L := by
  intro ts
  induction ts with
  | nil => intro _ _ hne; exact absurd rfl hne
  | cons w ts ih =>
    intro M G _ hsz hcs hreg hctr h
    simp only [List.length_cons, Nat.add_sub_cancel] at hreg hctr ⊢
    obtain ⟨G', ⟨hlt, h⟩ | ⟨hlt, h⟩⟩ := xa_restoreIter (p := lo + 32 * ts.length) hat hsz hcs
      (by omega) (by omega) hctr h
    · rcases ts with _ | ⟨w', ts'⟩
      · simp only [List.length_nil] at hlt; omega
      have h1 : (M.write (lo + 32 * (ts'.length + 1)) w.toBytes).size = M.size :=
        Mem.size_write_word_of_add_le (by simp only [List.length_cons] at hreg; omega)
      have h2 : ((M.write (lo + 32 * (ts'.length + 1)) w.toBytes).write t.c
          (Nat.toB256 (lo + 32 * (ts'.length + 1) - 32)).toBytes).size = M.size := by
        rw [Mem.size_write_word_of_add_le (by rw [h1]; exact hcs), h1]
      simp only [List.length_cons] at h hreg ⊢
      obtain ⟨G3, h'⟩ := ih _ G' (List.cons_ne_nil _ _) (by rw [h2]; exact hsz)
        (by rw [h2]; exact hcs) (by simp only [List.length_cons]; omega)
        (by
          rw [(Mem.memWord_write_word _ _ _).1]
          simp only [List.length_cons, Nat.add_sub_cancel]
          rw [show lo + 32 * (ts'.length + 1) - 32 = lo + 32 * ts'.length from by omega])
        h
      refine ⟨G3, ?_⟩
      simp only [List.length_cons, Nat.add_sub_cancel] at h'
      have e : lo + 32 * (ts'.length + 1) - 32 = lo + 32 * ts'.length := by omega
      have e2 : restoreMem t.c M (lo + 32 * (ts'.length + 1)) (w :: w' :: ts') =
          restoreMem t.c ((M.write (lo + 32 * (ts'.length + 1)) w.toBytes).write t.c
            (Nat.toB256 (lo + 32 * ts'.length)).toBytes) (lo + 32 * ts'.length) (w' :: ts') := by
        rw [restoreMem_cons, e]
      rw [e2]
      exact h'
    · rcases ts with _ | ⟨w', ts'⟩
      · simp only [List.length_nil, Nat.mul_zero, Nat.add_zero, restoreMem] at h ⊢
        exact ⟨G', h⟩
      · simp only [List.length_cons] at hlt; omega

/-- **A restore loop** on the actual derivation: from the head with the stack `ts ++ S`
(`ts ≠ []`), the counter word at `t.c` holding the top slot `lo + 32 (|ts| - 1)` and the bound
`t.e = lo`, the walk leaves past the exit `JUMPDEST` over `S` with the words `ts` written down
from the top slot (`restoreMem`; see `restoreMem_frameWords`). -/
theorem xa_frameRestore (hat : RestoreAt sevm.code H t) {lo : Nat} {ts : List B256}
    (hne : ts ≠ []) (hlo : 32 ≤ lo) (he : t.e = lo)
    (hsz : M.size % 32 = 0) (hcs : t.c + 32 ≤ M.size) (hreg : lo + 32 * ts.length ≤ t.c)
    (hctr : memWord M t.c = Nat.toB256 (lo + 32 * (ts.length - 1)))
    (h : XAt sevm post H (St b (ts ++ S) M G) L) :
    ∃ G', XAt sevm post (t.x + 1)
      (St b S (restoreMem t.c M (lo + 32 * (ts.length - 1)) ts) G') L :=
  xa_frameRestore_aux hat hlo he ts M G hne hsz hcs hreg hctr h

end

end Blanc.Lift
