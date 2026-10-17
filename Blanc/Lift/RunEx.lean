import Blanc.Lift.VyperRawCall

/-!
# Forward runs to *some* outcome

`SFunc.RunExact` steps are continuation-passing over a fixed outcome `r`.  A forward walk through
a call whose callee is described only by a premise (`∃ d, …`) cannot fix `r` up front: the
outcome depends on the callee's post state, which the walk learns midway.  `SFunc.RunEx` (and
`SFunc.RunExCut`) close the outcome under an existential with a predicate `Q`; every
fixed-outcome step lifts through `SFunc.RunEx.of` (the `xr`/`xrc` tactics), and the steps whose
continuations receive a fresh state (an identity copy, Vyper's `raw_call` tail) get their own
twins here.
-/

namespace Blanc.Lift

open Jaune

/-- Some run of `f` from `devm` ends in an outcome satisfying `Q`. -/
def SFunc.RunEx (fs : List SFunc) (sevm : Sevm) (devm : Devm) (f : SFunc)
    (Q : Outcome → Prop) : Prop :=
  ∃ r, SFunc.RunExact fs sevm devm f r ∧ Q r

/-- Some cut run of `f` from `devm` ends in a segment result satisfying `Q`. -/
def SFunc.RunExCut (fs : List SFunc) (sevm : Sevm) (C : List Nat) (devm : Devm) (f : SFunc)
    (Q : Seg → Prop) : Prop :=
  ∃ r, SFunc.RunExactCut fs sevm C devm f r ∧ Q r

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat}

/-- A fixed-outcome step lifts to `RunEx`. -/
theorem SFunc.RunEx.of {d d' : Devm} {f f' : SFunc} {Q : Outcome → Prop}
    (L : ∀ r, SFunc.RunExact fs sevm d' f' r → SFunc.RunExact fs sevm d f r)
    (h : SFunc.RunEx fs sevm d' f' Q) : SFunc.RunEx fs sevm d f Q :=
  let ⟨r, hr, hq⟩ := h; ⟨r, L r hr, hq⟩

/-- A fixed-outcome cut step lifts to `RunExCut`. -/
theorem SFunc.RunExCut.of {d d' : Devm} {f f' : SFunc} {Q : Seg → Prop}
    (L : ∀ r, SFunc.RunExactCut fs sevm C d' f' r → SFunc.RunExactCut fs sevm C d f r)
    (h : SFunc.RunExCut fs sevm C d' f' Q) : SFunc.RunExCut fs sevm C d f Q :=
  let ⟨r, hr, hq⟩ := h; ⟨r, L r hr, hq⟩

/-- `RunEx` is `RunExCut` with no cuts, its results `.done`. -/
theorem SFunc.runEx_iff_runExCut_nil {d : Devm} {f : SFunc} {Q : Outcome → Prop} :
    SFunc.RunEx fs sevm d f Q ↔ SFunc.RunExCut fs sevm [] d f (fun s => ∃ o, s = .done o ∧ Q o) := by
  constructor
  · rintro ⟨r, hr, hq⟩
    exact ⟨.done r, SFunc.runExact_iff_runExactCut_nil.mp hr, r, rfl, hq⟩
  · rintro ⟨_, hr, o, rfl, hq⟩
    exact ⟨o, SFunc.runExact_iff_runExactCut_nil.mpr hr, hq⟩

/-- Lift a fixed-outcome step `e : ∀ r, RunExact … r → RunExact … r` (e.g. `(rx_push rfl h ·)`). -/
macro "xr " e:term : tactic => `(tactic| refine SFunc.RunEx.of (fun _ => $e) ?_)

/-- Lift a fixed-outcome cut step (see `xr`). -/
macro "xrc " e:term : tactic => `(tactic| refine SFunc.RunExCut.of (fun _ => $e) ?_)

section Fwd

variable {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- An identity-precompile copy, forward, to some outcome (`rxc_call_identity`'s twin). -/
theorem rxce_call_identity {f : SFunc} {Q : Seg → Prop}
    {g ii is oi os : B256} {ext : Nat} (hid : IdReady sevm b)
    (hdepth : sevm.depth ≠ 0) (hg : g = Nat.toB256 G)
    (hext : (St b S M G).extCost [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] = ext)
    (hfund : 100 + ext + 64 * idCost is.toNat ≤ G) (hbound : G < 2 ^ 256)
    (hroom : S.length < 1024)
    (k : ∀ b', ShaCallPost b b' (M.read ii.toNat is.toNat).1 →
      SFunc.RunExCut fs sevm C
        (St b' (1 :: S) ((M.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write oi.toNat
          ((M.read ii.toNat is.toNat).1.take os.toNat)) (G - (100 + ext + idCost is.toNat))) f Q) :
    SFunc.RunExCut fs sevm C (St b (g :: 4 :: 0 :: ii :: is :: oi :: os :: S) M G)
      (.next (.exec .call) f) Q := by
  obtain ⟨b', hpost, hrun⟩ := call_identity_step hid hdepth hg hext hfund hbound hroom
  obtain ⟨r, hr, hq⟩ := k b' hpost
  exact ⟨r, .next hrun hr, hq⟩

variable {Q : Seg → Prop}

/-- **The join, forward, to some outcome** (`rxc_vyRawCallJoin`'s twin): over a word-aligned memory covering `[L, L + 64)` and
`[B, B + 64)` with the first `len` returned bytes at `L + 32`, and a `raw_call` result that
passes (`len = 0`, or a nonzero number), the join runs to `K` over the identity copy's base,
with the memory `vyRawMem`. -/
theorem rxce_vyRawCallJoin {p : VyRawSite} {f2 f3 f4 f5 K : SFunc} {n : Nat} {rd : Bytes}
    {rds c : B256} (hid : IdReady sevm b) (hdepth : sevm.depth ≠ 0)
    (hn32 : n ≤ 32) (hnrd : n ≤ rd.length) (hok : n = 0 ∨ Bytes.toNat (rd.take n) ≠ 0)
    (hrd : ∀ j, j < n →
      M.data.getD ((Bytes.toB256 [p.lh, p.ll]).toNat + 32 + j) 0 = rd.getD j 0)
    (h32 : M.size % 32 = 0) (hcovL : (Bytes.toB256 [p.lh, p.ll]).toNat + 64 ≤ M.size)
    (hcovB : (Bytes.toB256 [p.bh, p.bl]).toNat + 64 ≤ M.size)
    (hG : 1444 ≤ G) (hbound : G + 1000 < 2 ^ 256) (hroom : S.length + 10 < 1024)
    (k : ∀ b' rd', ShaCallPost b b' rd' → SFunc.RunExCut fs sevm C
      (St b' S (vyRawMem M (Bytes.toB256 [p.lh, p.ll]).toNat (Bytes.toB256 [p.bh, p.bl]).toNat n)
        G) K Q) :
    SFunc.RunExCut fs sevm C (St b (Nat.toB256 n :: rds :: c :: S) M (G + rawJoinCost n))
      (vyRawCallJoin p f2 f3 f4 f5 K) Q := by
  set Lw := Bytes.toB256 [p.lh, p.ll] with hLw
  set Bw := Bytes.toB256 [p.bh, p.bl] with hBw
  set len := Nat.toB256 n with hlenw
  have hL : Lw.toNat < 2 ^ 16 := toNat_push2_lt p.lh p.ll
  have hB : Bw.toNat < 2 ^ 16 := toNat_push2_lt p.bh p.bl
  have h20 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have hnlen : len.toNat = n := B256.toNat_toB256_of_lt (by omega)
  set nw := Bytes.toB256 [0x20] + len with hnw
  have hnw' : nw.toNat = n + 32 := by
    rw [hnw, B256.toNat_add, h20, hnlen, Nat.lo_eq_of_lt (by omega)]; omega
  set X := if n = 0 then 0 else rawCheckCost n with hX
  set ic := 100 + 0 + idCost nw.toNat with hic
  rw [show G + rawJoinCost n = G + X + ic + 98 by rw [rawJoinCost, hic, hnw']; omega]
  set M1 := M.write Lw.toNat len.toBytes with hM1
  have hs1 : M1.size = M.size := by
    rw [hM1, Mem.size_write_word_at, ite_eq_left (by omega)]
  set input := (M1.read Lw.toNat nw.toNat).1 with hinput
  have hinlen : input.length = n + 32 := by
    rw [hinput, ← hnw']
    simp only [Mem.read, Array.sliceD_eq_map, List.length_map, List.length_range]
  set M2 := M1.write Bw.toNat input with hM2
  have hs2 : M2.size = M.size := by
    rw [hM2, Mem.size_write_of_le (by rw [hinlen, hs1]; omega), hs1]
  have hmem2 : M2 = vyRawMem M Lw.toNat Bw.toNat n := by
    rw [hM2, hinput, hnw', hM1, hlenw]; rfl
  have hcopy : ∀ j, j < n + 32 →
      M2.data.getD (Bw.toNat + j) 0 = M1.data.getD (Lw.toNat + j) 0 := by
    intro j hj
    rw [hM2, Mem.write_getD_inside _ _ (by rw [hinlen]; omega),
      List.getD_eq_getElem _ _ (by rw [hinlen]; omega), ← List.getD_eq_getElem _ 0, hinput,
      Mem.read_fst_getD _ _ _ (by rw [hnw']; exact hj)]
  have hlenB : ∀ j, j < 32 → M2.data.getD (Bw.toNat + j) 0 = len.toBytes.getD j 0 := by
    intro j hj
    rw [hcopy j (by omega), hM1, Mem.write_getD_inside _ _ (by rw [B256.length_toBytes]; exact hj)]
  have hrdB : ∀ j, j < n → M2.data.getD (Bw.toNat + 32 + j) 0 = rd.getD j 0 := by
    intro j hj
    rw [Nat.add_assoc, hcopy (32 + j) (by omega), hM1, ← Nat.add_assoc,
      (Mem.write_agree M Lw.toNat len.toBytes).2 _ (by omega)
        (by rw [B256.length_toBytes]; omega)]
    exact hrd j hj
  have hv : Bytes.toB256 (M2.read Bw.toNat 32).1 = len := by
    have e : (M2.read Bw.toNat len.toBytes.length).1 = len.toBytes :=
      Mem.read_fst_of_getD M2 Bw.toNat (fun j hj => hlenB j (by rw [B256.length_toBytes] at hj; exact hj))
    rw [B256.length_toBytes] at e
    rw [e, B256.toB256_toBytes]
  have hcovI : memExtsSize M1.size [(Lw.toNat, nw.toNat), (Bw.toNat, nw.toNat)] = M1.size := by
    simp only [memExtsSize]
    rw [hs1, memExtSize_of_le h32 (by rw [hnw']; omega), memExtSize_of_le h32 (by rw [hnw']; omega)]
  have hXle : X ≤ 197 := by
    rw [hX]; split_ifs
    · omega
    · rw [rawCheckCost]; split_ifs <;> omega
  have hidc : idCost nw.toNat ≤ 21 := by
    rw [hnw', idCost]
    have : ceilDiv (n + 32) 32 ≤ 2 := by unfold ceilDiv; split_ifs <;> omega
    omega
  unfold vyRawCallJoin
  xrc (rxc_dest (G := G + X + ic + 97) ·)
  xrc (rxc_swap (G := G + X + ic + 94) (n := 0) (S' := rds :: len :: c :: S) rfl ·)
  xrc (rxc_pop (G := G + X + ic + 92) ·)
  xrc (rxc_swap (G := G + X + ic + 89) (n := 0) (S' := c :: len :: S) rfl ·)
  xrc (rxc_pop (G := G + X + ic + 87) ·)
  xrc (rxc_push (G := G + X + ic + 84) rfl (by (try simp only [List.length_cons]); omega) ·)
  xrc (rxc_mstore (G := G + X + ic + 81) (c := 3) (M' := M1)
    (by rw [St, Devm.extCost_zero_of_le h32 (by rw [← hLw]; omega)]; rfl) rfl ·)
  xrc (rxc_push (G := G + X + ic + 78) rfl (by omega) ·)
  xrc (rxc_dup (G := G + X + ic + 75) (n := 0) (w := Lw) rfl (by (try simp only [List.length_cons]); omega) ·)
  xrc (rxc_mload (G := G + X + ic + 72) (c := 3) (v := len)
    (by rw [St, Devm.extCost_zero_of_le (by rw [hs1]; exact h32) (by rw [hs1]; omega)]; rfl)
    (by rw [hM1, Mem.read_write_word_self, B256.toB256_toBytes])
    (Mem.read_snd_eq_self (memExtSize_of_le (by rw [hs1]; exact h32) (by rw [hs1]; omega)))
    (by (try simp only [List.length_cons]); omega) ·)
  xrc (rxc_push (G := G + X + ic + 69) rfl (by (try simp only [List.length_cons]); omega) ·)
  xrc (rxc_add (G := G + X + ic + 66) (by (try simp only [List.length_cons]); omega) ·)
  xrc (rxc_dup (G := G + X + ic + 63) (n := 0) (w := nw) rfl (by (try simp only [List.length_cons]); omega) ·)
  xrc (rxc_push (G := G + X + ic + 60) rfl (by (try simp only [List.length_cons]); omega) ·)
  xrc (rxc_dup (G := G + X + ic + 57) (n := 2) (w := nw) rfl (by (try simp only [List.length_cons]); omega) ·)
  xrc (rxc_dup (G := G + X + ic + 54) (n := 4) (w := Lw) rfl (by (try simp only [List.length_cons]); omega) ·)
  xrc (rxc_push (G := G + X + ic + 51) rfl (by (try simp only [List.length_cons]); omega) ·)
  xrc (rxc_push (G := G + X + ic + 48) rfl (by (try simp only [List.length_cons]); omega) ·)
  xrc (rxc_gas (G := G + X + ic + 46) (by (try simp only [List.length_cons]); omega) ·)
  rw [show Bytes.toB256 [0x04] = 4 by decide, show Bytes.toB256 [0x00] = 0 by decide]
  refine rxce_call_identity (G := G + X + ic + 46) hid hdepth rfl
    (Devm.extCost_covered hcovI) (by omega) (by omega) (by (try simp only [List.length_cons]); omega) ?_
  intro b' hpost
  rw [show G + X + ic + 46 - (100 + 0 + idCost nw.toNat) = G + X + 46 by omega,
    Mem.extends_covered hcovI, ← hinput, List.take_of_length_le (by rw [hinlen, hnw']), ← hM2]
  have hmB : (M2.read Bw.toNat 32).2 = M2 :=
    Mem.read_snd_eq_self (memExtSize_of_le (by rw [hs2]; exact h32) (by rw [hs2]; omega))
  xrc (rxc_push (G := G + X + 43) rfl (by (try simp only [List.length_cons]); omega) ·)
  xrc (fun h => rxc_branch_succ (G := G + X + 33) (by decide) (rxc_dest h))
  xrc (rxc_pop (G := G + X + 30) ·)
  xrc (rxc_pop (G := G + X + 28) ·)
  xrc (rxc_push (G := G + X + 25) rfl (by omega) ·)
  xrc (rxc_push (G := G + X + 22) rfl (by (try simp only [List.length_cons]); omega) ·)
  xrc (rxc_mload (G := G + X + 19) (c := 3) (v := len)
    (by rw [St, Devm.extCost_zero_of_le (by rw [hs2]; exact h32) (by rw [hs2, ← hBw]; omega)]; rfl)
    hv hmB (by (try simp only [List.length_cons]); omega) ·)
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · -- `len = 0`: straight to `K`
    have hX0 : X = 0 := by rw [hX, ite_eq_left h0]
    have hl0 : len = 0 := by rw [hlenw, h0]; rfl
    xrc (rxc_binary (G := G + X + 16) (fn := B256.gtCheck) (c := gVerylow) (v := 0)
      (by rintro ⟨⟩) (fun _ => rfl) (by rw [hl0]; decide) (by omega) ·)
    xrc (rxc_iszero (G := G + X + 13) (v := 1) (by decide) (by omega) ·)
    xrc (rxc_push (G := G + X + 10) rfl (by (try simp only [List.length_cons]); omega) ·)
    xrc (rxc_branch_succ (G := G + X) (by decide) ·)
    rw [hX0, Nat.add_zero, hmem2]
    exact k b' _ hpost
  · -- `len > 0`: the tested tail
    have hX1 : X = rawCheckCost n := by rw [hX, ite_eq_right (by omega)]
    have hgt : len > Bytes.toB256 [0x00] := by
      rw [GT.gt, B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x00]).toNat = 0 by decide, hnlen]
      exact hpos
    xrc (rxc_binary (G := G + X + 16) (fn := B256.gtCheck) (c := gVerylow) (v := 1)
      (by rintro ⟨⟩) (fun _ => rfl) (by simp only [B256.gtCheck, hgt, ↓reduceIte]) (by omega) ·)
    xrc (rxc_iszero (G := G + X + 13) (v := 0) (by decide) (by omega) ·)
    xrc (rxc_push (G := G + X + 10) rfl (by (try simp only [List.length_cons]); omega) ·)
    xrc (rxc_branch_zero (G := G + X) ·)
    rw [hX1]
    xrc (rxc_vyRawCallCheck hpos hn32 hnrd (hok.resolve_left (by omega)) hlenB hrdB
      (by rw [hs2]; exact h32) (by rw [hs2]; exact hcovB) (by omega) ·)
    rw [hmem2]
    exact k b' _ hpost

/-- **The `raw_call(…, max_outsize=32)` tail, forward, to some outcome** (`rxc_vyRawCallTail`'s twin): after a successful `CALL` whose returned
data passes `RawCallOk` and whose returned prefix sits at `L + 32`, over a word-aligned memory
covering `[L, L + 64)` and `[B, B + 64)`, the tail runs to `K` over the identity copy's base, at
gas `rawTailCost (min len 32)`. -/
theorem rxce_vyRawCallTail {p : VyRawSite} {k : Nat} {f1 f2 f3 f4 f5 K : SFunc} {flag : B256}
    (hid : IdReady sevm b) (hdepth : sevm.depth ≠ 0) (hflag : flag ≠ 0)
    (hk : fs[k]? = some (vyRawCallJoin p f2 f3 f4 f5 K)) (hkC : k ∉ C)
    (hrdlt : b.returnData.length < 2 ^ 256) (hok : RawCallOk b.returnData)
    (hrd : ∀ j, j < min b.returnData.length 32 →
      M.data.getD ((Bytes.toB256 [p.lh, p.ll]).toNat + 32 + j) 0 = b.returnData.getD j 0)
    (h32 : M.size % 32 = 0) (hcovL : (Bytes.toB256 [p.lh, p.ll]).toNat + 64 ≤ M.size)
    (hcovB : (Bytes.toB256 [p.bh, p.bl]).toNat + 64 ≤ M.size)
    (hG : 1444 ≤ G) (hbound : G + 1000 < 2 ^ 256) (hroom : S.length + 10 < 1024)
    (kk : ∀ b' rd', ShaCallPost b b' rd' → SFunc.RunExCut fs sevm C
      (St b' S (vyRawMem M (Bytes.toB256 [p.lh, p.ll]).toNat (Bytes.toB256 [p.bh, p.bl]).toNat
        (min b.returnData.length 32)) G) K Q) :
    SFunc.RunExCut fs sevm C (St b (flag :: S) M (G + rawTailCost (min b.returnData.length 32)))
      (vyRawCallTail p k f1 f2 f3 f4 f5 K) Q := by
  have h20 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  set rd := b.returnData with hrdd
  set n := min rd.length 32 with hn
  have hrds : (Nat.toB256 rd.length).toNat = rd.length := B256.toNat_toB256_of_lt hrdlt
  have hok' : n = 0 ∨ Bytes.toNat (rd.take n) ≠ 0 := by
    rcases hok with h | h
    · exact .inl (by omega)
    · exact .inr h
  set J := rawJoinCost n with hJ
  unfold vyRawCallTail
  by_cases hshort : rd.length < 32
  · rw [show G + rawTailCost n = G + J + 58 by rw [rawTailCost, ite_eq_left (by omega)]; omega]
    have hnl : n = rd.length := by omega
    have hgt : Bytes.toB256 [0x20] > Nat.toB256 rd.length := by
      rw [GT.gt, B256.lt_iff_toNat_lt_toNat, hrds, h20]; exact hshort
    xrc (rxc_push (G := G + J + 55) rfl (by (try simp only [List.length_cons]); omega) ·)
    xrc (fun h => rxc_branch_succ (G := G + J + 45) hflag (rxc_dest h))
    xrc (rxc_push (G := G + J + 41) rfl (by omega) ·)
    xrc (rxc_returndatasize (G := G + J + 39) (by (try simp only [List.length_cons]); omega) ·)
    rw [← hrdd]
    xrc (rxc_dup (G := G + J + 36) (n := 0) (w := Nat.toB256 rd.length) rfl (by (try simp only [List.length_cons]); omega) ·)
    xrc (rxc_dup (G := G + J + 33) (n := 2) (w := Bytes.toB256 [0x20]) rfl (by (try simp only [List.length_cons]); omega) ·)
    xrc (rxc_binary (G := G + J + 30) (fn := B256.gtCheck) (c := gVerylow) (v := 1)
      (by rintro ⟨⟩) (fun _ => rfl) (by simp only [B256.gtCheck, hgt, ↓reduceIte]) (by (try simp only [List.length_cons]); omega) ·)
    xrc (rxc_iszero (G := G + J + 27) (v := 0) (by decide) (by (try simp only [List.length_cons]); omega) ·)
    xrc (rxc_push (G := G + J + 24) rfl (by (try simp only [List.length_cons]); omega) ·)
    xrc (rxc_branch_zero (G := G + J + 14) ·)
    xrc (rxc_dup (G := G + J + 11) (n := 0) (w := Nat.toB256 rd.length) rfl (by (try simp only [List.length_cons]); omega) ·)
    xrc (rxc_push (G := G + J + 8) rfl (by (try simp only [List.length_cons]); omega) ·)
    xrc (rxc_jump (G := G + J) hk hkC ·)
    rw [← hnl]
    exact rxce_vyRawCallJoin hid hdepth (by omega) (by omega) hok' hrd h32 hcovL hcovB hG hbound
      (by omega) kk
  · rw [show G + rawTailCost n = G + J + 48 by rw [rawTailCost, ite_eq_right (by omega)]; omega]
    have hn32 : n = 32 := by omega
    have hgt : ¬ Bytes.toB256 [0x20] > Nat.toB256 rd.length := by
      rw [GT.gt, B256.lt_iff_toNat_lt_toNat, hrds, h20]; omega
    xrc (rxc_push (G := G + J + 45) rfl (by (try simp only [List.length_cons]); omega) ·)
    xrc (fun h => rxc_branch_succ (G := G + J + 35) hflag (rxc_dest h))
    xrc (rxc_push (G := G + J + 31) rfl (by omega) ·)
    xrc (rxc_returndatasize (G := G + J + 29) (by (try simp only [List.length_cons]); omega) ·)
    rw [← hrdd]
    xrc (rxc_dup (G := G + J + 26) (n := 0) (w := Nat.toB256 rd.length) rfl (by (try simp only [List.length_cons]); omega) ·)
    xrc (rxc_dup (G := G + J + 23) (n := 2) (w := Bytes.toB256 [0x20]) rfl (by (try simp only [List.length_cons]); omega) ·)
    xrc (rxc_binary (G := G + J + 20) (fn := B256.gtCheck) (c := gVerylow) (v := 0)
      (by rintro ⟨⟩) (fun _ => rfl) (by simp only [B256.gtCheck, hgt, ↓reduceIte]) (by (try simp only [List.length_cons]); omega) ·)
    xrc (rxc_iszero (G := G + J + 17) (v := 1) (by decide) (by (try simp only [List.length_cons]); omega) ·)
    xrc (rxc_push (G := G + J + 14) rfl (by (try simp only [List.length_cons]); omega) ·)
    xrc (fun h => rxc_branch_succ (G := G + J + 4) (by decide) (rxc_dest h))
    xrc (rxc_dup (G := G + J) (n := 1) (w := Bytes.toB256 [0x20]) rfl (by (try simp only [List.length_cons]); omega) ·)
    rw [show Bytes.toB256 [0x20] = Nat.toB256 n by rw [hn32]; decide]
    exact rxce_vyRawCallJoin hid hdepth (by omega) (by omega) hok' hrd h32 hcovL hcovB hG hbound
      (by omega) kk

end Fwd

end Blanc.Lift
