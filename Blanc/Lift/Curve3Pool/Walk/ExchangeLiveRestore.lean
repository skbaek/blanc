import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveSave

/-!
# `exchange`, forward: the frame restore after `get_y`

The mirror of `ExchangeLiveSave`: the certificate unrolls the restore loop (`0x27d9`, counting the
word at `0x7e0` down from `0x7c0` to `0x140`) into 53 copies of `exRestIt`, the first inline in
`get_y`'s return tree (`t_27d9_c751`), the others the entries `exRestIdx`. `rx_ex_restFrom` pops
the saved words back into memory by induction (the backward walk's `xa_ex_restore`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The frame restore's body, ending in the branch `br`. -/
def exRestIt (br : SFunc) : SFunc :=
  .dest (.next (.push [0x07, 0xe0] (by decide)) (.next (.reg .mload) (.next (.reg .mstore)
  (.next (.push [0x20] (by decide)) (.next (.push [0x07, 0xe0] (by decide)) (.next (.reg .mload)
  (.next (.reg .sub) (.next (.push [0x07, 0xe0] (by decide)) (.next (.reg .mstore)
  (.next (.push [0x01, 0x40] (by decide)) (.next (.push [0x07, 0xe0] (by decide))
  (.next (.reg .mload) (.next (.reg .lt) (.next (.reg .iszero) (.next (.reg .iszero)
  (.next (.push [0x27, 0xfc] (by decide)) br))))))))))))))))

/-- The entries of the restore's iterations after the first. -/
def exRestIdx : List Nat := [761, 771, 780, 789, 798, 807, 816, 825, 834, 843, 852, 861, 870,
  879, 888, 897, 906, 915, 924, 932, 940, 948, 956, 964, 972, 980, 988, 996, 1004, 1012, 1020,
  1028, 1036, 1044, 1053, 1061, 1069, 1076, 1083, 1090, 1097, 1104, 1111, 1118, 1125, 1132, 1139,
  1146, 1153, 1160, 1167, 1174]

/-- Iteration `n`'s branch: back to the next entry, or out to `dy`. -/
def exRestBr (n : Nat) : SFunc :=
  if n = 52 then .branch .undefined t_27fc_c1174
  else .branch (.next (.push [0x27, 0xd9] (by decide)) (.jump (exRestIdx.getD n 0))) .undefined

theorem ex_rest_first : t_27d9_c751 = exRestIt (exRestBr 0) := rfl

theorem ex_rest_chain : ∀ n, n < 52 →
    cert.prog[exRestIdx.getD n 0]? = some (exRestIt (exRestBr (n + 1))) := by
  decide +kernel

section Fwd

variable {sevm : Sevm} {b : Devm} {Q : Outcome → Prop}

/-- **One pass of the restore's body, exactly**: `rx_ex_restBody`, the continuation also
receiving the literal memory (the word at `q`, then the counter). -/
theorem rx_ex_restBody_core {br : SFunc} {S : List B256} {M : Mem} {img : Bytes} {G q : Nat}
    {v : B256} (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x920)
    (hq : 0x140 ≤ q) (hq2 : q + 32 ≤ 0x7e0) (hctr : WordAt img 0x7e0 (Nat.toB256 q))
    (hroom : S.length + 8 < 1024)
    (k : ∀ M', Mem.Reads M' (Bytes.writeAt (Bytes.writeAt img q v.toBytes) 0x7e0
        (Nat.toB256 (q - 32)).toBytes) → Mem.Wf M' → M'.size = 0x920 →
      M' = (M.write q v.toBytes).write 0x7e0 (Nat.toB256 (q - 32)).toBytes →
      SFunc.RunEx cert.prog sevm (St b (Bytes.toB256 [0x27, 0xfc] ::
        B256.eqCheck (B256.eqCheck (B256.ltCheck (Nat.toB256 (q - 32)) (Bytes.toB256 [0x01, 0x40]))
          0) 0 :: S) M' G) br Q) :
    SFunc.RunEx cert.prog sevm (St b (v :: S) M (G + 49)) (exRestIt br) Q := by
  have hq' : (Nat.toB256 q).toNat = q := B256.toNat_toB256_of_lt (by omega)
  unfold exRestIt
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mloadW (o := 0x7e0) hR hsz rfl (by decide) hctr (by hr) ·)
  refine rxe_mstoreW (o := q) (c := 3) hR hW hsz hq' ⟨by
    rw [memExtSize_of_le (by decide) (by omega), Nat.sub_self]; rfl, by decide⟩ ?_
  generalize hM1 : M.write q v.toBytes = M1
  intro hR1 hW1 hsz1
  rw [memExtSize_of_le (by decide) (by omega)] at hsz1
  have hctr1 : WordAt (Bytes.writeAt img q v.toBytes) 0x7e0 (Nat.toB256 q) :=
    hctr.write_other (by simp only [B256.length_toBytes]; omega)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mloadW (o := 0x7e0) hR1 hsz1 rfl (by decide) hctr1 (by hr) ·)
  xr (rx_sub (by hr) ·)
  rw [ex_sub32 (by omega) (by omega)]
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0x7e0) (c := 3) hR1 hW1 hsz1 rfl (by decide) ?_
  generalize hM2 : M1.write 0x7e0 (Nat.toB256 (q - 32)).toBytes = M2
  intro hR2 hW2 hsz2
  rw [show memExtSize 0x920 0x7e0 32 = 0x920 by decide] at hsz2
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mloadW (o := 0x7e0) hR2 hsz2 rfl (by decide) (WordAt.write_self _ _ _) (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  exact k M2 hR2 hW2 hsz2 (by rw [← hM2, ← hM1])

/-- One pass of the restore's body up to its branch: the stack's top word written at the
counter `q`, the counter moved to `q - 32`. -/
theorem rx_ex_restBody {br : SFunc} {S : List B256} {M : Mem} {img : Bytes} {G q : Nat}
    {v : B256} (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x920)
    (hq : 0x140 ≤ q) (hq2 : q + 32 ≤ 0x7e0) (hctr : WordAt img 0x7e0 (Nat.toB256 q))
    (hroom : S.length + 8 < 1024)
    (k : ∀ M', Mem.Reads M' (Bytes.writeAt (Bytes.writeAt img q v.toBytes) 0x7e0
        (Nat.toB256 (q - 32)).toBytes) → Mem.Wf M' → M'.size = 0x920 →
      SFunc.RunEx cert.prog sevm (St b (Bytes.toB256 [0x27, 0xfc] ::
        B256.eqCheck (B256.eqCheck (B256.ltCheck (Nat.toB256 (q - 32)) (Bytes.toB256 [0x01, 0x40]))
          0) 0 :: S) M' G) br Q) :
    SFunc.RunEx cert.prog sevm (St b (v :: S) M (G + 49)) (exRestIt br) Q :=
  rx_ex_restBody_core hR hW hsz hq hq2 hctr hroom fun M' h1 h2 h3 _ => k M' h1 h2 h3

/-- **The frame restore, forward, exactly**: `rx_ex_restFrom`, the continuation also receiving
the literal memory, `restoreMem` of the saved words from the counter `0x140 + 32 k`. -/
theorem rx_ex_restFrom_core (w : Nat → B256) : ∀ (k : Nat) {n : Nat} {S : List B256} {M : Mem}
    {img : Bytes} {G : Nat}, n + k = 52 → Mem.Reads M img → Mem.Wf M → M.size = 0x920 →
    WordAt img 0x7e0 (Nat.toB256 (0x140 + 32 * k)) → S.length + k + 9 < 1024 →
    (∀ (M' : Mem) (img' : Bytes), Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x920 →
      (∀ m, m ≤ k → WordAt img' (0x140 + 32 * m) (w (0x140 + 32 * m))) →
      (∀ o v, WordAt img o v →
        o + 32 ≤ 0x140 ∨ (0x140 + 32 * (k + 1) ≤ o ∧ o + 32 ≤ 0x7e0) ∨ 0x800 ≤ o →
        WordAt img' o v) →
      M' = restoreMem 0x7e0 M (0x140 + 32 * k) (exSaved w 0x140 (k + 1)) →
      SFunc.RunEx cert.prog sevm (St b S M' G) t_27fc_c1174 Q) →
    SFunc.RunEx cert.prog sevm (St b (exSaved w 0x140 (k + 1) ++ S) M (G + 70 * k + 59))
      (exRestIt (exRestBr n)) Q := by
  intro k
  induction k with
  | zero =>
    intro n S M img G hn hR hW hsz hctr hroom kk
    obtain rfl : n = 52 := by omega
    show SFunc.RunEx cert.prog sevm (St b (w 0x140 :: S) M (G + 70 * 0 + 59)) _ Q
    refine rx_ex_restBody_core hR hW hsz (le_refl _) (by omega) hctr (by omega) ?_
    intro M' hR' hW' hsz' hM'
    unfold exRestBr
    simp only [↓reduceIte]
    xr (rx_branch_succ (by decide) ·)
    refine kk M' _ hR' hW' hsz' (fun m hm => ?_) (fun o v h ho => ?_) (by rw [hM']; rfl)
    · obtain rfl : m = 0 := by omega
      exact (WordAt.write_self _ _ _).write_other (by simp only [B256.length_toBytes]; omega)
    · exact (h.write_other (by simp only [B256.length_toBytes]; omega)).write_other
        (by simp only [B256.length_toBytes]; omega)
  | succ k ih =>
    intro n S M img G hn hR hW hsz hctr hroom kk
    rw [exSaved_succ, List.cons_append,
      show G + 70 * (k + 1) + 59 = G + 70 * k + 59 + 8 + 3 + 10 + 49 by omega]
    refine rx_ex_restBody_core hR hW hsz (by omega) (by omega) hctr
      (by simp only [List.length_append, exSaved_length]; omega) ?_
    intro M' hR' hW' hsz' hM'
    unfold exRestBr
    simp only [show n ≠ 52 by omega, ↓reduceIte]
    have hlt : B256.ltCheck (Nat.toB256 (0x140 + 32 * (k + 1) - 32)) (Bytes.toB256 [0x01, 0x40]) =
        0 := ltCheck_eq_zero_of_le (by
      rw [B256.toNat_toB256_of_lt (by omega), show (Bytes.toB256 [0x01, 0x40]).toNat = 0x140 by
        decide]
      omega)
    xr (rx_branch_zero' (by rw [hlt]; decide) ·)
    xr (rx_push rfl (by simp only [List.length_append, exSaved_length]; omega) ·)
    xr (rx_jump (ex_rest_chain n (by omega)) ·)
    rw [show 0x140 + 32 * (k + 1) - 32 = 0x140 + 32 * k by omega] at hR'
    refine ih (n := n + 1) (by omega) hR' hW' hsz' (WordAt.write_self _ _ _) (by omega) ?_
    intro M'' img'' hR'' hW'' hsz'' hm'' hk'' hM''
    refine kk M'' img'' hR'' hW'' hsz'' (fun m hm => ?_) (fun o v h ho => ?_) ?_
    rotate_left 2
    · rw [hM'', hM', exSaved_succ w (k + 1), restoreMem,
        show 0x140 + 32 * (k + 1) - 32 = 0x140 + 32 * k by omega]
    · by_cases e : m = k + 1
      · subst e
        exact hk'' _ _ ((WordAt.write_self _ _ _).write_other
          (by simp only [B256.length_toBytes]; omega)) (.inr (.inl ⟨by omega, by omega⟩))
      · exact hm'' m (by omega)
    · exact hk'' o v ((h.write_other (by simp only [B256.length_toBytes]; omega)).write_other
        (by simp only [B256.length_toBytes]; omega)) (by omega)

/-- **The frame restore, forward**, at iteration `n` with `k` iterations after it: the saved
words `exSaved w 0x140 (k + 1)` popped back to `0x140, …, 0x140 + 32 k`, memory otherwise kept
below `0x140`, between the restored words and the counter, and from `0x800`; then on to `dy`. -/
theorem rx_ex_restFrom (w : Nat → B256) : ∀ (k : Nat) {n : Nat} {S : List B256} {M : Mem}
    {img : Bytes} {G : Nat}, n + k = 52 → Mem.Reads M img → Mem.Wf M → M.size = 0x920 →
    WordAt img 0x7e0 (Nat.toB256 (0x140 + 32 * k)) → S.length + k + 9 < 1024 →
    (∀ (M' : Mem) (img' : Bytes), Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x920 →
      (∀ m, m ≤ k → WordAt img' (0x140 + 32 * m) (w (0x140 + 32 * m))) →
      (∀ o v, WordAt img o v →
        o + 32 ≤ 0x140 ∨ (0x140 + 32 * (k + 1) ≤ o ∧ o + 32 ≤ 0x7e0) ∨ 0x800 ≤ o →
        WordAt img' o v) →
      SFunc.RunEx cert.prog sevm (St b S M' G) t_27fc_c1174 Q) →
    SFunc.RunEx cert.prog sevm (St b (exSaved w 0x140 (k + 1) ++ S) M (G + 70 * k + 59))
      (exRestIt (exRestBr n)) Q :=
  fun k {_n} {_S} {_M} {_img} {_G} hn hR hW hsz hctr hroom kk =>
    rx_ex_restFrom_core w k hn hR hW hsz hctr hroom fun M' img' h1 h2 h3 h4 h5 _ => kk M' img' h1 h2 h3 h4 h5

end Fwd

end Blanc.Lift.Curve3Pool
