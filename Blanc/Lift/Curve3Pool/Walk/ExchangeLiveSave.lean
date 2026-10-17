import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveX

/-!
# `exchange`, forward: the frame save before `get_y`

The certificate unrolls `exchange`'s frame save (`0x2754`, 53 words `[0x140, 0x7e0)` pushed with
the counter word at `0x7e0`) into 53 copies of one body `exSaveIt`: the first inline in `x`'s tree
(`t_2754_c13`), the others the entries `exSaveIdx`. `rx_ex_saveFrom` runs them all forward by
induction, leaving the words on the stack as `exSaved` (the backward walk's `xa_ex_save`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The frame save's body, ending in the branch `br`. -/
def exSaveIt (br : SFunc) : SFunc :=
  .dest (.next (.push [0x07, 0xe0] (by decide)) (.next (.reg .mload) (.next (.reg .mload)
  (.next (.push [0x20] (by decide)) (.next (.push [0x07, 0xe0] (by decide)) (.next (.reg .mload)
  (.next (.reg .add) (.next (.push [0x07, 0xe0] (by decide)) (.next (.reg .mstore)
  (.next (.push [0x07, 0xe0] (by decide)) (.next (.push [0x07, 0xe0] (by decide))
  (.next (.reg .mload) (.next (.reg .lt) (.next (.reg .iszero)
  (.next (.push [0x27, 0x76] (by decide)) br)))))))))))))))

/-- The entries of the save's iterations after the first. -/
def exSaveIdx : List Nat := [45, 73, 96, 118, 139, 161, 183, 202, 218, 232, 246, 261, 276, 291,
  306, 321, 336, 351, 366, 381, 396, 411, 425, 439, 453, 467, 481, 497, 511, 525, 541, 554, 567,
  578, 589, 599, 609, 619, 629, 639, 649, 659, 669, 679, 688, 697, 706, 715, 724, 733, 742, 751]

/-- Iteration `n`'s branch: back to the next entry, or out to the arguments of `get_y`. -/
def exSaveBr (n : Nat) : SFunc :=
  if n = 52 then .branch .undefined t_2776_c751
  else .branch (.next (.push [0x27, 0x54] (by decide)) (.jump (exSaveIdx.getD n 0))) .undefined

theorem exSaved_length (w : Nat → B256) : ∀ (k p : Nat), (exSaved w p k).length = k
  | 0, _ => rfl
  | k + 1, p => by
    rw [show exSaved w p (k + 1) = exSaved w (p + 32) k ++ [w p] from rfl, List.length_append,
      exSaved_length w k (p + 32)]
    rfl

/-- A stack-room side condition over a literal stack prefix and saved frame words. -/
macro "hrs" : tactic => `(tactic| first
  | hr
  | (simp only [List.length_cons, List.length_append, List.length_nil, exSaved_length]; omega))

theorem ex_save_first : t_2754_c13 = exSaveIt (exSaveBr 0) := rfl

theorem ex_save_chain : ∀ n, n < 52 →
    cert.prog[exSaveIdx.getD n 0]? = some (exSaveIt (exSaveBr (n + 1))) := by
  decide +kernel

section Fwd

variable {sevm : Sevm} {b : Devm} {Q : Outcome → Prop}

/-- One pass of the save's body up to its branch: the word at the counter `p` pushed, the
counter bumped to `p + 32`. -/
theorem rx_ex_saveBody {br : SFunc} {S : List B256} {M : Mem} {img : Bytes} {G p : Nat}
    {v : B256} (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x800)
    (hp2 : p + 32 ≤ 0x7e0) (hctr : WordAt img 0x7e0 (Nat.toB256 p)) (hv : WordAt img p v)
    (hroom : S.length + 4 < 1024)
    (k : ∀ M', Mem.Reads M' (Bytes.writeAt img 0x7e0 (Nat.toB256 (p + 32)).toBytes) →
      Mem.Wf M' → M'.size = 0x800 →
      SFunc.RunEx cert.prog sevm (St b (Bytes.toB256 [0x27, 0x76] ::
        B256.eqCheck (B256.ltCheck (Nat.toB256 (p + 32)) (Bytes.toB256 [0x07, 0xe0])) 0 ::
        v :: S) M' G) br Q) :
    SFunc.RunEx cert.prog sevm (St b S M (G + 46)) (exSaveIt br) Q := by
  have hp' : (Nat.toB256 p).toNat = p := B256.toNat_toB256_of_lt (by omega)
  unfold exSaveIt
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mloadW (o := 0x7e0) hR hsz rfl (by decide) hctr (by hr) ·)
  xr (rxm_mloadW (o := p) hR hsz hp' ⟨by omega, by decide⟩ hv (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mloadW (o := 0x7e0) hR hsz rfl (by decide) hctr (by hr) ·)
  xr (rx_add (by hr) ·)
  rw [ex_add32 (by omega)]
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x7e0) (c := 3) hR hW hsz rfl (by decide) ?_
  intro M' hR' hW' hsz'
  rw [show memExtSize 0x800 0x7e0 32 = 0x800 by decide] at hsz'
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mloadW (o := 0x7e0) hR' hsz' rfl (by decide) (WordAt.write_self _ _ _) (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  exact k M' hR' hW' hsz'

/-- **The frame save, forward**, from iteration `n` with `k` iterations after it: the words `w`
at `0x140 + 32 n, …, 0x7c0` pushed (`exSaved`), then on to `get_y`'s arguments. -/
theorem rx_ex_saveFrom (w : Nat → B256) : ∀ (k : Nat) {n : Nat} {S : List B256} {M : Mem}
    {img : Bytes} {G : Nat}, n + k = 52 → Mem.Reads M img → Mem.Wf M → M.size = 0x800 →
    WordAt img 0x7e0 (Nat.toB256 (0x140 + 32 * n)) →
    (∀ m, n ≤ m → m ≤ 52 → WordAt img (0x140 + 32 * m) (w (0x140 + 32 * m))) →
    S.length + k + 8 < 1024 →
    (∀ (M' : Mem) (img' : Bytes), Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x800 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0x7e0 → WordAt img' o v) →
      SFunc.RunEx cert.prog sevm (St b (exSaved w (0x140 + 32 * n) (k + 1) ++ S) M' G)
        t_2776_c751 Q) →
    SFunc.RunEx cert.prog sevm (St b S M (G + 67 * k + 56)) (exSaveIt (exSaveBr n)) Q := by
  intro k
  induction k with
  | zero =>
    intro n S M img G hn hR hW hsz hctr hw hroom kk
    obtain rfl : n = 52 := by omega
    have hv := hw 52 (le_refl _) (le_refl _)
    refine rx_ex_saveBody hR hW hsz (by omega) hctr hv (by omega) ?_
    intro M' hR' hW' hsz'
    unfold exSaveBr
    simp only [↓reduceIte]
    xr (rx_branch_succ (by decide) ·)
    exact kk M' _ hR' hW' hsz' (fun o v h ho => h.write_other (by
      simp only [B256.length_toBytes]; omega))
  | succ k ih =>
    intro n S M img G hn hR hW hsz hctr hw hroom kk
    have hv := hw n (le_refl _) (by omega)
    rw [show G + 67 * (k + 1) + 56 = G + 67 * k + 56 + 8 + 3 + 10 + 46 by omega]
    refine rx_ex_saveBody hR hW hsz (by omega) hctr hv (by omega) ?_
    intro M' hR' hW' hsz'
    unfold exSaveBr
    simp only [show n ≠ 52 by omega, ↓reduceIte]
    have hlt : B256.ltCheck (Nat.toB256 (0x140 + 32 * n + 32)) (Bytes.toB256 [0x07, 0xe0]) = 1 :=
      if_pos (by
        rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega),
          show (Bytes.toB256 [0x07, 0xe0]).toNat = 0x7e0 by decide]
        omega)
    xr (rx_branch_zero' (by rw [hlt]; decide) ·)
    xr (rx_push rfl (by hr) ·)
    xr (rx_jump (ex_save_chain n (by omega)) ·)
    rw [show 0x140 + 32 * n + 32 = 0x140 + 32 * (n + 1) by ring] at hR'
    refine ih (n := n + 1) (by omega) hR' hW' hsz' (WordAt.write_self _ _ _)
      (fun m hm hm' => (hw m (by omega) hm').write_other (by
        simp only [B256.length_toBytes]; omega)) (by simp only [List.length_cons]; omega) ?_
    intro M'' img'' hR'' hW'' hsz'' hk''
    have e : exSaved w (0x140 + 32 * (n + 1)) (k + 1) ++ (w (0x140 + 32 * n) :: S) =
        exSaved w (0x140 + 32 * n) (k + 1 + 1) ++ S := by
      rw [show exSaved w (0x140 + 32 * n) (k + 1 + 1) =
        exSaved w (0x140 + 32 * n + 32) (k + 1) ++ [w (0x140 + 32 * n)] from rfl,
        show 0x140 + 32 * n + 32 = 0x140 + 32 * (n + 1) by ring, List.append_assoc]
      rfl
    rw [e]
    exact kk M'' img'' hR'' hW'' hsz'' fun o v h ho =>
      hk'' o v (h.write_other (by simp only [B256.length_toBytes]; omega)) ho

end Fwd

end Blanc.Lift.Curve3Pool
