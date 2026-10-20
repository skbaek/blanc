import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveRestore

/-!
# Vyper's frame save and restore loops, forward, at any counter

A private call inside a Vyper function saves the caller's frame words `[0x140, C)` on the stack
before the call and pops them back after it, each with a counter word at `C`. The certificate
unrolls each loop into one tree per iteration; `exchange`'s instances are `ExchangeLiveSave` and
`ExchangeLiveRestore`. Here the same bodies are parameterised by the counter's and the jump
targets' two-byte immediates: `svIt`/`svBr` (save) and `rsIt`/`rsBr` (restore), with
`rx_svFrom`/`rx_rsFrom` running them forward by induction from a chain hypothesis
(`cert.prog` at each next entry is the next iteration, proved per instance by `decide`).
The memory is at a fixed size `sz` covering the counter.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The save's body at counter `[c1, c2]` up to the limit `[l1, l2]`, exit `[x1, x2]`, ending in
the branch `br`. -/
def svItL (c1 c2 l1 l2 x1 x2 : UInt8) (br : SFunc) : SFunc :=
  .dest (.next (.push [c1, c2] (Nat.le_of_ble_eq_true rfl)) (.next (.reg .mload) (.next (.reg .mload)
  (.next (.push [0x20] (by decide)) (.next (.push [c1, c2] (Nat.le_of_ble_eq_true rfl)) (.next (.reg .mload)
  (.next (.reg .add) (.next (.push [c1, c2] (Nat.le_of_ble_eq_true rfl)) (.next (.reg .mstore)
  (.next (.push [l1, l2] (Nat.le_of_ble_eq_true rfl)) (.next (.push [c1, c2] (Nat.le_of_ble_eq_true rfl))
  (.next (.reg .mload) (.next (.reg .lt) (.next (.reg .iszero)
  (.next (.push [x1, x2] (Nat.le_of_ble_eq_true rfl)) br)))))))))))))))

/-- The save's body at counter `[c1, c2]`, which is also its limit. -/
abbrev svIt (c1 c2 x1 x2 : UInt8) (br : SFunc) : SFunc := svItL c1 c2 c1 c2 x1 x2 br

/-- Iteration `n`'s branch of a loop with `N + 1` iterations: back to the head `[h1, h2]` at the
next entry `idx[n]`, or out to `ex`. -/
def lpBr (N : Nat) (idx : List Nat) (h1 h2 : UInt8) (ex : SFunc) (n : Nat) : SFunc :=
  if n = N then .branch .undefined ex
  else .branch (.next (.push [h1, h2] (Nat.le_of_ble_eq_true rfl)) (.jump (idx.getD n 0))) .undefined

/-- The restore's body at counter `[c1, c2]`, exit `[x1, x2]`, ending in the branch `br`. -/
def rsIt (c1 c2 x1 x2 : UInt8) (br : SFunc) : SFunc :=
  .dest (.next (.push [c1, c2] (Nat.le_of_ble_eq_true rfl)) (.next (.reg .mload) (.next (.reg .mstore)
  (.next (.push [0x20] (by decide)) (.next (.push [c1, c2] (Nat.le_of_ble_eq_true rfl)) (.next (.reg .mload)
  (.next (.reg .sub) (.next (.push [c1, c2] (Nat.le_of_ble_eq_true rfl)) (.next (.reg .mstore)
  (.next (.push [0x01, 0x40] (by decide)) (.next (.push [c1, c2] (Nat.le_of_ble_eq_true rfl))
  (.next (.reg .mload) (.next (.reg .lt) (.next (.reg .iszero) (.next (.reg .iszero)
  (.next (.push [x1, x2] (Nat.le_of_ble_eq_true rfl)) br))))))))))))))))

section Fwd

variable {sevm : Sevm} {b : Devm} {Q : Outcome → Prop} {c1 c2 l1 l2 x1 x2 : UInt8} {C Lm sz : Nat}

/-- `rx_svBody`, the continuation also receiving the written memory as a term. -/
theorem rx_svBodyM {br : SFunc} {S : List B256} {M : Mem} {img : Bytes} {G p : Nat}
    {v : B256} (hC : (Bytes.toB256 [c1, c2]).toNat = C) (hCs : C + 32 ≤ sz) (hs : sz % 32 = 0)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = sz)
    (hp2 : p + 32 ≤ C) (hctr : WordAt img C (Nat.toB256 p)) (hv : WordAt img p v)
    (hroom : S.length + 4 < 1024)
    (k : ∀ M', M' = M.write C (Nat.toB256 (p + 32)).toBytes →
      Mem.Reads M' (Bytes.writeAt img C (Nat.toB256 (p + 32)).toBytes) →
      Mem.Wf M' → M'.size = sz →
      SFunc.RunEx cert.prog sevm (St b (Bytes.toB256 [x1, x2] ::
        B256.eqCheck (B256.ltCheck (Nat.toB256 (p + 32)) (Bytes.toB256 [l1, l2])) 0 ::
        v :: S) M' G) br Q) :
    SFunc.RunEx cert.prog sevm (St b S M (G + 46)) (svItL c1 c2 l1 l2 x1 x2 br) Q := by
  have hCl : C < 2 ^ 256 := hC ▸ B256.toNat_lt _
  have hp' : (Nat.toB256 p).toNat = p := B256.toNat_toB256_of_lt (by omega)
  unfold svItL
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mloadW (o := C) hR hsz hC ⟨by omega, hs⟩ hctr (by hr) ·)
  xr (rxm_mloadW (o := p) hR hsz hp' ⟨by omega, hs⟩ hv (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mloadW (o := C) hR hsz hC ⟨by omega, hs⟩ hctr (by hr) ·)
  xr (rx_add (by hr) ·)
  rw [ex_add32 (by omega)]
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := C) (c := 3) hR hW hsz hC
    ⟨by rw [memExtSize_of_le hs hCs, Nat.sub_self]; rfl, hs⟩ ?_
  intro M' hM' hR' hW' hsz'
  rw [memExtSize_of_le hs hCs] at hsz'
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mloadW (o := C) hR' hsz' hC ⟨by omega, hs⟩ (WordAt.write_self _ _ _) (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  exact k M' hM' hR' hW' hsz'

/-- One pass of the save's body: the word at the counter `p` pushed, the counter bumped. -/
theorem rx_svBody {br : SFunc} {S : List B256} {M : Mem} {img : Bytes} {G p : Nat}
    {v : B256} (hC : (Bytes.toB256 [c1, c2]).toNat = C) (hCs : C + 32 ≤ sz) (hs : sz % 32 = 0)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = sz)
    (hp2 : p + 32 ≤ C) (hctr : WordAt img C (Nat.toB256 p)) (hv : WordAt img p v)
    (hroom : S.length + 4 < 1024)
    (k : ∀ M', Mem.Reads M' (Bytes.writeAt img C (Nat.toB256 (p + 32)).toBytes) →
      Mem.Wf M' → M'.size = sz →
      SFunc.RunEx cert.prog sevm (St b (Bytes.toB256 [x1, x2] ::
        B256.eqCheck (B256.ltCheck (Nat.toB256 (p + 32)) (Bytes.toB256 [l1, l2])) 0 ::
        v :: S) M' G) br Q) :
    SFunc.RunEx cert.prog sevm (St b S M (G + 46)) (svItL c1 c2 l1 l2 x1 x2 br) Q :=
  rx_svBodyM hC hCs hs hR hW hsz hp2 hctr hv hroom fun M' _ => k M'


/-- `rx_svFromL`, the continuation also receiving the save's memory as a term (`saveMem`). -/
theorem rx_svFromLM (w : Nat → B256) {N : Nat} {idx : List Nat} {h1 h2 : UInt8} {ex : SFunc}
    (hC : (Bytes.toB256 [c1, c2]).toNat = C) (hL : (Bytes.toB256 [l1, l2]).toNat = Lm)
    (hN : Lm = 0x140 + 32 * (N + 1)) (hLC : Lm ≤ C) (hCs : C + 32 ≤ sz) (hs : sz % 32 = 0)
    (hchain : ∀ n, n < N →
      cert.prog[idx.getD n 0]? = some (svItL c1 c2 l1 l2 x1 x2 (lpBr N idx h1 h2 ex (n + 1)))) :
    ∀ (k : Nat) {n : Nat} {S : List B256} {M : Mem}
    {img : Bytes} {G : Nat}, n + k = N → Mem.Reads M img → Mem.Wf M → M.size = sz →
    WordAt img C (Nat.toB256 (0x140 + 32 * n)) →
    (∀ m, n ≤ m → m ≤ N → WordAt img (0x140 + 32 * m) (w (0x140 + 32 * m))) →
    S.length + k + 8 < 1024 →
    (∀ (M' : Mem) (img' : Bytes), M' = saveMem M C (0x140 + 32 * n) (k + 1) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = sz →
      (∀ o v, WordAt img o v → o + 32 ≤ C ∨ C + 32 ≤ o → WordAt img' o v) →
      WordAt img' C (Nat.toB256 Lm) →
      SFunc.RunEx cert.prog sevm (St b (exSaved w (0x140 + 32 * n) (k + 1) ++ S) M' G) ex Q) →
    SFunc.RunEx cert.prog sevm (St b S M (G + 67 * k + 56))
      (svItL c1 c2 l1 l2 x1 x2 (lpBr N idx h1 h2 ex n)) Q := by
  have hCl : C < 2 ^ 256 := hC ▸ B256.toNat_lt _
  intro k
  induction k with
  | zero =>
    intro n S M img G hn hR hW hsz hctr hw hroom kk
    have hn' : n = N := by omega
    subst n
    have hv := hw N (le_refl _) (le_refl _)
    refine rx_svBodyM hC hCs hs hR hW hsz (by omega) hctr hv (by omega) ?_
    intro M' hM' hR' hW' hsz'
    unfold lpBr
    simp only [↓reduceIte]
    have hge : B256.ltCheck (Nat.toB256 (0x140 + 32 * N + 32)) (Bytes.toB256 [l1, l2]) = 0 :=
      ltCheck_eq_zero_of_le (by rw [hL, B256.toNat_toB256_of_lt (by omega)]; omega)
    xr (rx_branch_succ (by rw [hge]; decide) ·)
    refine kk M' _ (by rw [hM']; rfl) hR' hW' hsz' (fun o v h ho => h.write_other (by
      simp only [B256.length_toBytes]; omega)) ?_
    rw [show 0x140 + 32 * N + 32 = Lm by omega]
    exact WordAt.write_self _ _ _
  | succ k ih =>
    intro n S M img G hn hR hW hsz hctr hw hroom kk
    have hv := hw n (le_refl _) (by omega)
    rw [show G + 67 * (k + 1) + 56 = G + 67 * k + 56 + 8 + 3 + 10 + 46 by omega]
    refine rx_svBodyM hC hCs hs hR hW hsz (by omega) hctr hv (by omega) ?_
    intro M' hM' hR' hW' hsz'
    unfold lpBr
    simp only [show n ≠ N by omega, ↓reduceIte]
    have hlt : B256.ltCheck (Nat.toB256 (0x140 + 32 * n + 32)) (Bytes.toB256 [l1, l2]) = 1 :=
      if_pos (by
        rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega), hL]
        omega)
    xr (rx_branch_zero' (by rw [hlt]; decide) ·)
    xr (rx_push rfl (by hr) ·)
    xr (rx_jump (hchain n (by omega)) ·)
    rw [show 0x140 + 32 * n + 32 = 0x140 + 32 * (n + 1) by ring] at hR'
    refine ih (n := n + 1) (by omega) hR' hW' hsz' (WordAt.write_self _ _ _)
      (fun m hm hm' => (hw m (by omega) hm').write_other (by
        simp only [B256.length_toBytes]; omega)) (by simp only [List.length_cons]; omega) ?_
    intro M'' img'' hM'' hR'' hW'' hsz'' hk'' hc''
    have e : exSaved w (0x140 + 32 * (n + 1)) (k + 1) ++ (w (0x140 + 32 * n) :: S) =
        exSaved w (0x140 + 32 * n) (k + 1 + 1) ++ S := by
      rw [show exSaved w (0x140 + 32 * n) (k + 1 + 1) =
        exSaved w (0x140 + 32 * n + 32) (k + 1) ++ [w (0x140 + 32 * n)] from rfl,
        show 0x140 + 32 * n + 32 = 0x140 + 32 * (n + 1) by ring, List.append_assoc]
      rfl
    rw [e]
    have hM3 : M'' = saveMem M C (0x140 + 32 * n) (k + 1 + 1) := by
      rw [hM'', hM', saveMem_succ_left M C (0x140 + 32 * n) (k + 1),
        show 0x140 + 32 * (n + 1) = 0x140 + 32 * n + 32 by ring]
    exact kk M'' img'' hM3 hR'' hW'' hsz'' (fun o v h ho =>
      hk'' o v (h.write_other (by simp only [B256.length_toBytes]; omega)) ho) hc''

/-- **A frame save, forward**, up to the limit `Lm` (the counter `C` at or above it), from iteration `n` with `k` iterations after it: the words `w`
at `0x140 + 32 n, …, C - 32` pushed (`exSaved`), then on to `ex`. -/
theorem rx_svFromL (w : Nat → B256) {N : Nat} {idx : List Nat} {h1 h2 : UInt8} {ex : SFunc}
    (hC : (Bytes.toB256 [c1, c2]).toNat = C) (hL : (Bytes.toB256 [l1, l2]).toNat = Lm)
    (hN : Lm = 0x140 + 32 * (N + 1)) (hLC : Lm ≤ C) (hCs : C + 32 ≤ sz) (hs : sz % 32 = 0)
    (hchain : ∀ n, n < N →
      cert.prog[idx.getD n 0]? = some (svItL c1 c2 l1 l2 x1 x2 (lpBr N idx h1 h2 ex (n + 1)))) :
    ∀ (k : Nat) {n : Nat} {S : List B256} {M : Mem}
    {img : Bytes} {G : Nat}, n + k = N → Mem.Reads M img → Mem.Wf M → M.size = sz →
    WordAt img C (Nat.toB256 (0x140 + 32 * n)) →
    (∀ m, n ≤ m → m ≤ N → WordAt img (0x140 + 32 * m) (w (0x140 + 32 * m))) →
    S.length + k + 8 < 1024 →
    (∀ (M' : Mem) (img' : Bytes), Mem.Reads M' img' → Mem.Wf M' → M'.size = sz →
      (∀ o v, WordAt img o v → o + 32 ≤ C ∨ C + 32 ≤ o → WordAt img' o v) →
      WordAt img' C (Nat.toB256 Lm) →
      SFunc.RunEx cert.prog sevm (St b (exSaved w (0x140 + 32 * n) (k + 1) ++ S) M' G) ex Q) →
    SFunc.RunEx cert.prog sevm (St b S M (G + 67 * k + 56))
      (svItL c1 c2 l1 l2 x1 x2 (lpBr N idx h1 h2 ex n)) Q := by
  intro k n S M img G hn hR hW hsz hctr hw hroom kk
  exact rx_svFromLM w hC hL hN hLC hCs hs hchain k hn hR hW hsz hctr hw hroom
    fun M' img' _ => kk M' img'

/-- **A frame save, forward**, from iteration `n` with `k` iterations after it, the counter
being its own limit (`rx_svFromL`). -/
theorem rx_svFrom (w : Nat → B256) {N : Nat} {idx : List Nat} {h1 h2 : UInt8} {ex : SFunc}
    (hC : (Bytes.toB256 [c1, c2]).toNat = C) (hN : C = 0x140 + 32 * (N + 1)) (hCs : C + 32 ≤ sz)
    (hs : sz % 32 = 0)
    (hchain : ∀ n, n < N →
      cert.prog[idx.getD n 0]? = some (svIt c1 c2 x1 x2 (lpBr N idx h1 h2 ex (n + 1)))) :
    ∀ (k : Nat) {n : Nat} {S : List B256} {M : Mem}
    {img : Bytes} {G : Nat}, n + k = N → Mem.Reads M img → Mem.Wf M → M.size = sz →
    WordAt img C (Nat.toB256 (0x140 + 32 * n)) →
    (∀ m, n ≤ m → m ≤ N → WordAt img (0x140 + 32 * m) (w (0x140 + 32 * m))) →
    S.length + k + 8 < 1024 →
    (∀ (M' : Mem) (img' : Bytes), Mem.Reads M' img' → Mem.Wf M' → M'.size = sz →
      (∀ o v, WordAt img o v → o + 32 ≤ C ∨ C + 32 ≤ o → WordAt img' o v) →
      WordAt img' C (Nat.toB256 C) →
      SFunc.RunEx cert.prog sevm (St b (exSaved w (0x140 + 32 * n) (k + 1) ++ S) M' G) ex Q) →
    SFunc.RunEx cert.prog sevm (St b S M (G + 67 * k + 56))
      (svIt c1 c2 x1 x2 (lpBr N idx h1 h2 ex n)) Q :=
  rx_svFromL w hC hC hN (le_refl _) hCs hs hchain

/-- `rx_rsBody`, the continuation also receiving the written memory as a term. -/
theorem rx_rsBodyM {br : SFunc} {S : List B256} {M : Mem} {img : Bytes} {G q : Nat}
    {v : B256} (hC : (Bytes.toB256 [c1, c2]).toNat = C) (hCs : C + 32 ≤ sz) (hs : sz % 32 = 0)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = sz)
    (hq : 0x140 ≤ q) (hq2 : q + 32 ≤ C) (hctr : WordAt img C (Nat.toB256 q))
    (hroom : S.length + 8 < 1024)
    (k : ∀ M', M' = (M.write q v.toBytes).write C (Nat.toB256 (q - 32)).toBytes →
      Mem.Reads M' (Bytes.writeAt (Bytes.writeAt img q v.toBytes) C
        (Nat.toB256 (q - 32)).toBytes) → Mem.Wf M' → M'.size = sz →
      SFunc.RunEx cert.prog sevm (St b (Bytes.toB256 [x1, x2] ::
        B256.eqCheck (B256.eqCheck (B256.ltCheck (Nat.toB256 (q - 32)) (Bytes.toB256 [0x01, 0x40]))
          0) 0 :: S) M' G) br Q) :
    SFunc.RunEx cert.prog sevm (St b (v :: S) M (G + 49)) (rsIt c1 c2 x1 x2 br) Q := by
  have hCl : C < 2 ^ 256 := hC ▸ B256.toNat_lt _
  have hq' : (Nat.toB256 q).toNat = q := B256.toNat_toB256_of_lt (by omega)
  unfold rsIt
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mloadW (o := C) hR hsz hC ⟨by omega, hs⟩ hctr (by hr) ·)
  refine rxe_mstoreL (o := q) (c := 3) hR hW hsz hq' ⟨by
    rw [memExtSize_of_le hs (by omega), Nat.sub_self]; rfl, hs⟩ ?_
  intro M1 hM1 hR1 hW1 hsz1
  rw [memExtSize_of_le hs (by omega)] at hsz1
  have hctr1 : WordAt (Bytes.writeAt img q v.toBytes) C (Nat.toB256 q) :=
    hctr.write_other (by simp only [B256.length_toBytes]; omega)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mloadW (o := C) hR1 hsz1 hC ⟨by omega, hs⟩ hctr1 (by hr) ·)
  xr (rx_sub (by hr) ·)
  rw [ex_sub32 (by omega) (by omega)]
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := C) (c := 3) hR1 hW1 hsz1 hC
    ⟨by rw [memExtSize_of_le hs hCs, Nat.sub_self]; rfl, hs⟩ ?_
  intro M2 hM2 hR2 hW2 hsz2
  rw [memExtSize_of_le hs hCs] at hsz2
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mloadW (o := C) hR2 hsz2 hC ⟨by omega, hs⟩ (WordAt.write_self _ _ _) (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  exact k M2 (by rw [hM2, hM1]) hR2 hW2 hsz2

/-- One pass of the restore's body: the stack's top word written at the counter `q`, the
counter moved to `q - 32`. -/
theorem rx_rsBody {br : SFunc} {S : List B256} {M : Mem} {img : Bytes} {G q : Nat}
    {v : B256} (hC : (Bytes.toB256 [c1, c2]).toNat = C) (hCs : C + 32 ≤ sz) (hs : sz % 32 = 0)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = sz)
    (hq : 0x140 ≤ q) (hq2 : q + 32 ≤ C) (hctr : WordAt img C (Nat.toB256 q))
    (hroom : S.length + 8 < 1024)
    (k : ∀ M', Mem.Reads M' (Bytes.writeAt (Bytes.writeAt img q v.toBytes) C
        (Nat.toB256 (q - 32)).toBytes) → Mem.Wf M' → M'.size = sz →
      SFunc.RunEx cert.prog sevm (St b (Bytes.toB256 [x1, x2] ::
        B256.eqCheck (B256.eqCheck (B256.ltCheck (Nat.toB256 (q - 32)) (Bytes.toB256 [0x01, 0x40]))
          0) 0 :: S) M' G) br Q) :
    SFunc.RunEx cert.prog sevm (St b (v :: S) M (G + 49)) (rsIt c1 c2 x1 x2 br) Q :=
  rx_rsBodyM hC hCs hs hR hW hsz hq hq2 hctr hroom fun M' _ => k M'

/-- `rx_rsFromL`, the continuation also receiving the restore's memory as a term
(`restoreMem`). -/
theorem rx_rsFromLM (w : Nat → B256) {N : Nat} {idx : List Nat} {h1 h2 : UInt8} {ex : SFunc}
    (hC : (Bytes.toB256 [c1, c2]).toNat = C) (hN : 0x140 + 32 * (N + 1) ≤ C) (hCs : C + 32 ≤ sz)
    (hs : sz % 32 = 0)
    (hchain : ∀ n, n < N →
      cert.prog[idx.getD n 0]? = some (rsIt c1 c2 x1 x2 (lpBr N idx h1 h2 ex (n + 1)))) :
    ∀ (k : Nat) {n : Nat} {S : List B256} {M : Mem}
    {img : Bytes} {G : Nat}, n + k = N → Mem.Reads M img → Mem.Wf M → M.size = sz →
    WordAt img C (Nat.toB256 (0x140 + 32 * k)) → S.length + k + 9 < 1024 →
    (∀ (M' : Mem) (img' : Bytes), M' = restoreMem C M (0x140 + 32 * k) (exSaved w 0x140 (k + 1)) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = sz →
      (∀ m, m ≤ k → WordAt img' (0x140 + 32 * m) (w (0x140 + 32 * m))) →
      (∀ o v, WordAt img o v →
        o + 32 ≤ 0x140 ∨ (0x140 + 32 * (k + 1) ≤ o ∧ o + 32 ≤ C) ∨ C + 32 ≤ o →
        WordAt img' o v) →
      SFunc.RunEx cert.prog sevm (St b S M' G) ex Q) →
    SFunc.RunEx cert.prog sevm (St b (exSaved w 0x140 (k + 1) ++ S) M (G + 70 * k + 59))
      (rsIt c1 c2 x1 x2 (lpBr N idx h1 h2 ex n)) Q := by
  have hCl : C < 2 ^ 256 := hC ▸ B256.toNat_lt _
  intro k
  induction k with
  | zero =>
    intro n S M img G hn hR hW hsz hctr hroom kk
    have hn' : n = N := by omega
    subst n
    show SFunc.RunEx cert.prog sevm (St b (w 0x140 :: S) M (G + 70 * 0 + 59)) _ Q
    refine rx_rsBodyM hC hCs hs hR hW hsz (le_refl _) (by omega) hctr (by omega) ?_
    intro M' hM' hR' hW' hsz'
    unfold lpBr
    simp only [↓reduceIte]
    xr (rx_branch_succ (by decide) ·)
    refine kk M' _ (by rw [hM']; rfl) hR' hW' hsz' (fun m hm => ?_) (fun o v h ho => ?_)
    · obtain rfl : m = 0 := by omega
      exact (WordAt.write_self _ _ _).write_other (by simp only [B256.length_toBytes]; omega)
    · exact (h.write_other (by simp only [B256.length_toBytes]; omega)).write_other
        (by simp only [B256.length_toBytes]; omega)
  | succ k ih =>
    intro n S M img G hn hR hW hsz hctr hroom kk
    rw [exSaved_succ, List.cons_append,
      show G + 70 * (k + 1) + 59 = G + 70 * k + 59 + 8 + 3 + 10 + 49 by omega]
    refine rx_rsBodyM hC hCs hs hR hW hsz (by omega) (by omega) hctr
      (by simp only [List.length_append, exSaved_length]; omega) ?_
    intro M' hM' hR' hW' hsz'
    unfold lpBr
    simp only [show n ≠ N by omega, ↓reduceIte]
    have hlt : B256.ltCheck (Nat.toB256 (0x140 + 32 * (k + 1) - 32)) (Bytes.toB256 [0x01, 0x40]) =
        0 := ltCheck_eq_zero_of_le (by
      rw [B256.toNat_toB256_of_lt (by omega), show (Bytes.toB256 [0x01, 0x40]).toNat = 0x140 by
        decide]
      omega)
    xr (rx_branch_zero' (by rw [hlt]; decide) ·)
    xr (rx_push rfl (by simp only [List.length_append, exSaved_length]; omega) ·)
    xr (rx_jump (hchain n (by omega)) ·)
    rw [show 0x140 + 32 * (k + 1) - 32 = 0x140 + 32 * k by omega] at hR'
    refine ih (n := n + 1) (by omega) hR' hW' hsz' (WordAt.write_self _ _ _) (by omega) ?_
    intro M'' img'' hM'' hR'' hW'' hsz'' hm'' hk''
    have hM3 : M'' = restoreMem C M (0x140 + 32 * (k + 1)) (exSaved w 0x140 (k + 1 + 1)) := by
      rw [hM'', hM', exSaved_succ w (k + 1), restoreMem,
        show 0x140 + 32 * (k + 1) - 32 = 0x140 + 32 * k by omega]
    refine kk M'' img'' hM3 hR'' hW'' hsz'' (fun m hm => ?_) (fun o v h ho => ?_)
    · by_cases e : m = k + 1
      · subst e
        exact hk'' _ _ ((WordAt.write_self _ _ _).write_other
          (by simp only [B256.length_toBytes]; omega)) (.inr (.inl ⟨by omega, by omega⟩))
      · exact hm'' m (by omega)
    · exact hk'' o v ((h.write_other (by simp only [B256.length_toBytes]; omega)).write_other
        (by simp only [B256.length_toBytes]; omega)) (by omega)

/-- **A frame restore, forward** (counter at or above the saved words), at iteration `n` with `k` iterations after it: the saved
words `exSaved w 0x140 (k + 1)` popped back to `0x140, …, 0x140 + 32 k`, memory otherwise kept
below `0x140`, between the restored words and the counter, and above the counter; then on to
`ex`. -/
theorem rx_rsFromL (w : Nat → B256) {N : Nat} {idx : List Nat} {h1 h2 : UInt8} {ex : SFunc}
    (hC : (Bytes.toB256 [c1, c2]).toNat = C) (hN : 0x140 + 32 * (N + 1) ≤ C) (hCs : C + 32 ≤ sz)
    (hs : sz % 32 = 0)
    (hchain : ∀ n, n < N →
      cert.prog[idx.getD n 0]? = some (rsIt c1 c2 x1 x2 (lpBr N idx h1 h2 ex (n + 1)))) :
    ∀ (k : Nat) {n : Nat} {S : List B256} {M : Mem}
    {img : Bytes} {G : Nat}, n + k = N → Mem.Reads M img → Mem.Wf M → M.size = sz →
    WordAt img C (Nat.toB256 (0x140 + 32 * k)) → S.length + k + 9 < 1024 →
    (∀ (M' : Mem) (img' : Bytes), Mem.Reads M' img' → Mem.Wf M' → M'.size = sz →
      (∀ m, m ≤ k → WordAt img' (0x140 + 32 * m) (w (0x140 + 32 * m))) →
      (∀ o v, WordAt img o v →
        o + 32 ≤ 0x140 ∨ (0x140 + 32 * (k + 1) ≤ o ∧ o + 32 ≤ C) ∨ C + 32 ≤ o →
        WordAt img' o v) →
      SFunc.RunEx cert.prog sevm (St b S M' G) ex Q) →
    SFunc.RunEx cert.prog sevm (St b (exSaved w 0x140 (k + 1) ++ S) M (G + 70 * k + 59))
      (rsIt c1 c2 x1 x2 (lpBr N idx h1 h2 ex n)) Q := by
  intro k n S M img G hn hR hW hsz hctr hroom kk
  exact rx_rsFromLM w hC hN hCs hs hchain k hn hR hW hsz hctr hroom fun M' img' _ => kk M' img'

/-- **A frame restore, forward** with the counter right above the saved words
(`rx_rsFromL`). -/
theorem rx_rsFrom (w : Nat → B256) {N : Nat} {idx : List Nat} {h1 h2 : UInt8} {ex : SFunc}
    (hC : (Bytes.toB256 [c1, c2]).toNat = C) (hN : C = 0x140 + 32 * (N + 1)) (hCs : C + 32 ≤ sz)
    (hs : sz % 32 = 0)
    (hchain : ∀ n, n < N →
      cert.prog[idx.getD n 0]? = some (rsIt c1 c2 x1 x2 (lpBr N idx h1 h2 ex (n + 1)))) :
    ∀ (k : Nat) {n : Nat} {S : List B256} {M : Mem}
    {img : Bytes} {G : Nat}, n + k = N → Mem.Reads M img → Mem.Wf M → M.size = sz →
    WordAt img C (Nat.toB256 (0x140 + 32 * k)) → S.length + k + 9 < 1024 →
    (∀ (M' : Mem) (img' : Bytes), Mem.Reads M' img' → Mem.Wf M' → M'.size = sz →
      (∀ m, m ≤ k → WordAt img' (0x140 + 32 * m) (w (0x140 + 32 * m))) →
      (∀ o v, WordAt img o v →
        o + 32 ≤ 0x140 ∨ (0x140 + 32 * (k + 1) ≤ o ∧ o + 32 ≤ C) ∨ C + 32 ≤ o →
        WordAt img' o v) →
      SFunc.RunEx cert.prog sevm (St b S M' G) ex Q) →
    SFunc.RunEx cert.prog sevm (St b (exSaved w 0x140 (k + 1) ++ S) M (G + 70 * k + 59))
      (rsIt c1 c2 x1 x2 (lpBr N idx h1 h2 ex n)) Q :=
  rx_rsFromL w hC (le_of_eq hN.symm) hCs hs hchain

/-- `rx_svFrom`, the continuation also receiving the save's memory as a term (`saveMem`). -/
theorem rx_svFromM (w : Nat → B256) {N : Nat} {idx : List Nat} {h1 h2 : UInt8} {ex : SFunc}
    (hC : (Bytes.toB256 [c1, c2]).toNat = C) (hN : C = 0x140 + 32 * (N + 1)) (hCs : C + 32 ≤ sz)
    (hs : sz % 32 = 0)
    (hchain : ∀ n, n < N →
      cert.prog[idx.getD n 0]? = some (svIt c1 c2 x1 x2 (lpBr N idx h1 h2 ex (n + 1)))) :
    ∀ (k : Nat) {n : Nat} {S : List B256} {M : Mem}
    {img : Bytes} {G : Nat}, n + k = N → Mem.Reads M img → Mem.Wf M → M.size = sz →
    WordAt img C (Nat.toB256 (0x140 + 32 * n)) →
    (∀ m, n ≤ m → m ≤ N → WordAt img (0x140 + 32 * m) (w (0x140 + 32 * m))) →
    S.length + k + 8 < 1024 →
    (∀ (M' : Mem) (img' : Bytes), M' = saveMem M C (0x140 + 32 * n) (k + 1) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = sz →
      (∀ o v, WordAt img o v → o + 32 ≤ C ∨ C + 32 ≤ o → WordAt img' o v) →
      WordAt img' C (Nat.toB256 C) →
      SFunc.RunEx cert.prog sevm (St b (exSaved w (0x140 + 32 * n) (k + 1) ++ S) M' G) ex Q) →
    SFunc.RunEx cert.prog sevm (St b S M (G + 67 * k + 56))
      (svIt c1 c2 x1 x2 (lpBr N idx h1 h2 ex n)) Q :=
  rx_svFromLM w hC hC hN (le_refl _) hCs hs hchain

/-- `rx_rsFrom`, the continuation also receiving the restore's memory as a term
(`restoreMem`). -/
theorem rx_rsFromM (w : Nat → B256) {N : Nat} {idx : List Nat} {h1 h2 : UInt8} {ex : SFunc}
    (hC : (Bytes.toB256 [c1, c2]).toNat = C) (hN : C = 0x140 + 32 * (N + 1)) (hCs : C + 32 ≤ sz)
    (hs : sz % 32 = 0)
    (hchain : ∀ n, n < N →
      cert.prog[idx.getD n 0]? = some (rsIt c1 c2 x1 x2 (lpBr N idx h1 h2 ex (n + 1)))) :
    ∀ (k : Nat) {n : Nat} {S : List B256} {M : Mem}
    {img : Bytes} {G : Nat}, n + k = N → Mem.Reads M img → Mem.Wf M → M.size = sz →
    WordAt img C (Nat.toB256 (0x140 + 32 * k)) → S.length + k + 9 < 1024 →
    (∀ (M' : Mem) (img' : Bytes), M' = restoreMem C M (0x140 + 32 * k) (exSaved w 0x140 (k + 1)) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = sz →
      (∀ m, m ≤ k → WordAt img' (0x140 + 32 * m) (w (0x140 + 32 * m))) →
      (∀ o v, WordAt img o v →
        o + 32 ≤ 0x140 ∨ (0x140 + 32 * (k + 1) ≤ o ∧ o + 32 ≤ C) ∨ C + 32 ≤ o →
        WordAt img' o v) →
      SFunc.RunEx cert.prog sevm (St b S M' G) ex Q) →
    SFunc.RunEx cert.prog sevm (St b (exSaved w 0x140 (k + 1) ++ S) M (G + 70 * k + 59))
      (rsIt c1 c2 x1 x2 (lpBr N idx h1 h2 ex n)) Q :=
  rx_rsFromLM w hC (le_of_eq hN.symm) hCs hs hchain

end Fwd

end Blanc.Lift.Curve3Pool
