import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawLiveD

/-!
# `_calc_withdraw_one_coin`, forward: the fee loop

Iteration `k` of the fee loop (counter word `Nat.toB256 k` at `0x720`): `scaled = xp[k] · D1 /
D0`, `dx_expected` by whether `k = i`, and `xp_reduced[k] -= fee · dx_expected /
FEE_DENOMINATOR` at `0x540 + 32 k`, under the backward walk's `CwStep`. `rx_cw_it0` …
`rx_cw_it2` run the three unrolled copies forward.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

theorem cw_idx {c bw : B256} {k base : Nat} (hk : k < 3) (hc : c.toNat = k) (hb : bw.toNat = base)
    (hb' : base < 2 ^ 255) : (Bytes.toB256 [0x20] * c + bw).toNat = base + 32 * k := by
  rw [ex_off (hc ▸ hk) hb hb', hc]

theorem cw_inc {k : Nat} (hk : k + 1 < 2 ^ 256) :
    Bytes.toB256 [1] + Nat.toB256 k = Nat.toB256 (k + 1) := by
  apply B256.toNat_inj
  rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega), B256.toNat_toB256_of_lt hk,
    show (Bytes.toB256 [1]).toNat = 1 by decide, Nat.lo, Nat.mod_eq_of_lt (by omega)]
  omega

theorem cw_eq_br {iw : B256} {k : Nat} (hk : k < 3) (h : iw.toNat = k) :
    B256.eqCheck (B256.eqCheck (Nat.toB256 k) iw) 0 = 0 := by
  have e : Nat.toB256 k = iw := by rw [← h, toB256_toNat]
  rw [e, eqCheck_self]
  decide

theorem cw_ne_br {iw : B256} {k : Nat} (hk : k < 3) (h : iw.toNat ≠ k) :
    B256.eqCheck (B256.eqCheck (Nat.toB256 k) iw) 0 ≠ 0 := by
  have e : B256.eqCheck (Nat.toB256 k) iw = 0 := by
    unfold B256.eqCheck
    rw [ite_eq_right (fun e => h (by rw [← e, B256.toNat_toB256_of_lt (by omega)]))]
  rw [e, eqCheck_self]
  decide

theorem cw_loop_ne {k : Nat} (hk : k + 1 < 3) :
    B256.eqCheck (B256.eqCheck (Nat.toB256 (k + 1)) (Bytes.toB256 [3] + Bytes.toB256 [0])) 0 ≠ 0 := by
  obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  all_goals decide

theorem cw_loop_eq : B256.eqCheck (B256.eqCheck (Nat.toB256 (2 + 1))
    (Bytes.toB256 [3] + Bytes.toB256 [0])) 0 = 0 := by decide

/-- A fee iteration's `dx_expected`: `xp[k] · D1 / D0 - new_y` at `k = i`, else
`xp[k] - xp[k] · D1 / D0`. -/
def cwItDx (eqk : Prop) [Decidable eqk] (x D1 D0 y : B256) : B256 :=
  if eqk then x * D1 / D0 - y else x - x * D1 / D0

/-- A fee iteration's memory: `dx_expected` zeroed then set at `0x740`, `xp_reduced[k]` at
`0x540 + 32 k`, the counter `k + 1` at `0x720`. -/
def cwItMem (M : Mem) (k : Nat) (dx r' : B256) : Mem :=
  (((M.write 0x740 (Bytes.toB256 [0]).toBytes).write 0x740 dx.toBytes).write (0x540 + 32 * k)
    r'.toBytes).write 0x720 (Nat.toB256 (k + 1)).toBytes


set_option hygiene false in
/-- One step of a carried-word search at offsets in a loop counter `k`. -/
macro "wstepK" : tactic => `(tactic| first
  | refine WordAt.write_other ?_ (by
      simp only [B256.length_toBytes, List.length_take, List.length_sliceD, List.length_cons,
        List.length_nil, List.length_append]
      omega)
  | exact WordAt.write_eq (by first | decide | omega) (by first | rfl | exact hk1))

/-- A carried word at offsets in a loop counter: peel the writes, then the named fact. -/
macro "wautoK " h:term : tactic => `(tactic| (repeat wstepK) <;> exact $h)
/-- A carried word at offsets in a loop counter: peel the writes, then the context. -/
macro "wautoK0" : tactic => `(tactic| (repeat wstepK) <;> try assumption)

/-- An `MSTORE` charge inside the grown memory. -/
macro "kmc" : tactic => `(tactic| exact ⟨by rw [memExtSize_of_le (by decide) (by omega), Nat.sub_self]; rfl, by decide⟩)

/-- The memory size a fee iteration starts at and its first store's charge: `0x740` and `6` on
iteration 0 (the store at `0x740` grows the memory), `0x760` and `3` later. -/
def CwSz (s m : Nat) : Prop := (s = 0x740 ∧ m = 6) ∨ (s = 0x760 ∧ m = 3)

theorem cwSz_facts {s m : Nat} (h : CwSz s m) :
    gVerylow + (calculateMemoryGasCost (memExtSize s 0x740 32) - calculateMemoryGasCost s) = m ∧
      s % 32 = 0 ∧ memExtSize s 0x740 32 = 0x760 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, by decide, by decide⟩

/-- The fee loop's back edge at counter `k`, from the tail `tl` to the continuation `T`. -/
def CwLoopB (sevm : Sevm) (b : Devm) (S : List B256) (k : Nat) (Q : Outcome → Prop)
    (tl T : SFunc) : Prop :=
  ∀ (M' : Mem) (g : Nat), SFunc.RunEx cert.prog sevm
    (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M' g) T Q →
  SFunc.RunEx cert.prog sevm (St b (Bytes.toB256 [0x40, 0x5e] :: B256.eqCheck (B256.eqCheck
    (Bytes.toB256 [3] + Bytes.toB256 [0]) (Nat.toB256 (k + 1))) 0 ::
    (Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M' (g + 10)) tl Q

theorem cw_backS {sevm : Sevm} {b : Devm} {S : List B256} {Q : Outcome → Prop} {x g : SFunc}
    {j k : Nat} (hj : cert.prog[j]? = some g) (hk : k + 1 < 3) :
    CwLoopB sevm b S k Q (.branchTo x j) g := by
  intro M' G h
  have hne : B256.eqCheck (B256.eqCheck (Bytes.toB256 [3] + Bytes.toB256 [0]) (Nat.toB256 (k + 1)))
      0 ≠ 0 := by
    obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    all_goals decide
  xr (rx_branchTo_succ hne hj ·)
  exact h

theorem cw_backX {sevm : Sevm} {b : Devm} {S : List B256} {Q : Outcome → Prop} {x y : SFunc} :
    CwLoopB sevm b S 2 Q (.branch x y) x := by
  intro M' G h
  xr (rx_branch_zero' cw_loop_eq ·)
  exact h

/-! ## The loop body as one tree

The heads `t_405e_c1348`/`c50`/`c79` are one tree (`cwPH_405e`) up to the jump into the shared
tail (`jm`) and the back edge (`tl`). -/

def cwPH_40d0 (jm : Nat) : SFunc :=
  (.dest (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .sub) (.next (.reg (.swap 0))
    (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x07, 0x40] (by
    decide)) (.next (.reg .mstore) (.next (.push [0x41, 0x5f] (by decide)) (.jump jm))))))))))))

def cwPH_40b9 (jm : Nat) : SFunc :=
  (.dest (.next (.reg (.dup 2)) (.next (.reg .div) (.next (.reg (.swap 0)) (.next (.reg .pop)
    (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x05, 0xa0] (by decide)) (.next (.reg
    .mload) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .lt) (.next (.reg .iszero)
    (.next (.push [0x40, 0xd0] (by decide)) (.branch t_40cc_c1348 (cwPH_40d0 jm))))))))))))))))

def cwPH_40a3 (jm : Nat) : SFunc :=
  (.dest (.next (.reg (.dup 0)) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0))
    (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x04, 0x00] (by
    decide)) (.next (.reg .mload) (.next (.reg (.dup 0)) (.next (.reg (.dup 0)) (.next (.push
    [0x40, 0xb9] (by decide)) (.branch t_40b5_c1348 (cwPH_40b9 jm)))))))))))))))

def cwPH_4086 (jm : Nat) : SFunc :=
  (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg
    .mload) (.next (.push [0x05, 0x20] (by decide)) (.next (.reg .mload) (.next (.reg (.dup 0))
    (.next (.reg (.dup 2)) (.next (.reg .mul) (.next (.reg (.dup 2)) (.next (.reg .iszero) (.next
    (.reg (.dup 2)) (.next (.reg (.dup 4)) (.next (.reg (.dup 3)) (.next (.reg .div) (.next (.reg
    .eq) (.next (.reg .or) (.next (.push [0x40, 0xa3] (by decide)) (.branch t_409f_c1348 (cwPH_40a3
    jm)))))))))))))))))))))

def cwPH_4073 (jm : Nat) : SFunc :=
  (.next (.push [0x03, 0x20] (by decide)) (.next (.push [0x07, 0x20] (by decide)) (.next (.reg
    .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next
    (.push [0x40, 0x86] (by decide)) (.branch .undefined (cwPH_4086 jm)))))))))

def cwPH_41cb (tl : SFunc) : SFunc :=
  (.dest (.next (.reg (.dup 1)) (.next (.reg .mload) (.next (.push [0x01] (by decide)) (.next (.reg
    .add) (.next (.reg (.dup 0)) (.next (.reg (.dup 3)) (.next (.reg .mstore) (.next (.reg (.dup
    1)) (.next (.reg .eq) (.next (.reg .iszero) (.next (.push [0x40, 0x5e] (by decide))
    tl))))))))))))

def cwPH_41c0 (tl : SFunc) : SFunc :=
  (.dest (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .sub) (.next (.reg (.swap 0))
    (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.dup 1)) (.next
    (.reg .mstore) (.next (.reg .pop) (cwPH_41cb tl))))))))))))

def cwPH_41ad (tl : SFunc) : SFunc :=
  (.dest (.next (.reg (.dup 2)) (.next (.reg .div) (.next (.reg (.swap 0)) (.next (.reg .pop)
    (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next
    (.reg .lt) (.next (.reg .iszero) (.next (.push [0x41, 0xc0] (by decide)) (.branch t_41bc_c20
    (cwPH_41c0 tl))))))))))))))

def cwPH_4195 (tl : SFunc) : SFunc :=
  (.dest (.next (.reg (.dup 0)) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0))
    (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x02, 0x54, 0x0b,
    0xe4, 0x00] (by decide)) (.next (.reg (.dup 0)) (.next (.reg (.dup 0)) (.next (.push [0x41,
    0xad] (by decide)) (.branch .undefined (cwPH_41ad tl))))))))))))))

def cwPH_4173 (tl : SFunc) : SFunc :=
  (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg (.dup
    0)) (.next (.reg .mload) (.next (.push [0x02, 0x00] (by decide)) (.next (.reg .mload) (.next
    (.push [0x07, 0x40] (by decide)) (.next (.reg .mload) (.next (.reg (.dup 0)) (.next (.reg (.dup
    2)) (.next (.reg .mul) (.next (.reg (.dup 2)) (.next (.reg .iszero) (.next (.reg (.dup 2))
    (.next (.reg (.dup 4)) (.next (.reg (.dup 3)) (.next (.reg .div) (.next (.reg .eq) (.next (.reg
    .or) (.next (.push [0x41, 0x95] (by decide)) (.branch t_4191_c20 (cwPH_4195
    tl))))))))))))))))))))))))

def cwPH_415f (tl : SFunc) : SFunc :=
  (.dest (.next (.push [0x05, 0x40] (by decide)) (.next (.push [0x07, 0x20] (by decide)) (.next
    (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next
    (.push [0x41, 0x73] (by decide)) (.branch .undefined (cwPH_4173 tl))))))))))

def cwPH_4153 (tl : SFunc) : SFunc :=
  (.dest (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .sub) (.next (.reg (.swap 0))
    (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x07, 0x40] (by
    decide)) (.next (.reg .mstore) (cwPH_415f tl)))))))))))

def cwPH_4140 (tl : SFunc) : SFunc :=
  (.dest (.next (.reg (.dup 2)) (.next (.reg .div) (.next (.reg (.swap 0)) (.next (.reg .pop)
    (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next
    (.reg .lt) (.next (.reg .iszero) (.next (.push [0x41, 0x53] (by decide)) (.branch t_414f_c1348
    (cwPH_4153 tl))))))))))))))

def cwPH_412a (tl : SFunc) : SFunc :=
  (.dest (.next (.reg (.dup 0)) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0))
    (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x04, 0x00] (by
    decide)) (.next (.reg .mload) (.next (.reg (.dup 0)) (.next (.reg (.dup 0)) (.next (.push
    [0x41, 0x40] (by decide)) (.branch t_413c_c1348 (cwPH_4140 tl)))))))))))))))

def cwPH_410d (tl : SFunc) : SFunc :=
  (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg
    .mload) (.next (.push [0x05, 0x20] (by decide)) (.next (.reg .mload) (.next (.reg (.dup 0))
    (.next (.reg (.dup 2)) (.next (.reg .mul) (.next (.reg (.dup 2)) (.next (.reg .iszero) (.next
    (.reg (.dup 2)) (.next (.reg (.dup 4)) (.next (.reg (.dup 3)) (.next (.reg .div) (.next (.reg
    .eq) (.next (.reg .or) (.next (.push [0x41, 0x2a] (by decide)) (.branch t_4126_c1348 (cwPH_412a
    tl)))))))))))))))))))))

def cwPH_40f4 (tl : SFunc) : SFunc :=
  (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg
    .mload) (.next (.push [0x03, 0x20] (by decide)) (.next (.push [0x07, 0x20] (by decide)) (.next
    (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next
    (.push [0x41, 0x0d] (by decide)) (.branch .undefined (cwPH_410d tl))))))))))))))

def cwPH_40e0 (tl : SFunc) : SFunc :=
  (.dest (.next (.push [0x03, 0x20] (by decide)) (.next (.push [0x07, 0x20] (by decide)) (.next
    (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next
    (.push [0x40, 0xf4] (by decide)) (.branch .undefined (cwPH_40f4 tl))))))))))

def cwPH_405e (jm : Nat) (tl : SFunc) : SFunc :=
  (.dest (.next (.push [0x00] (by decide)) (.next (.push [0x07, 0x40] (by decide)) (.next (.reg
    .mstore) (.next (.push [0x01, 0x60] (by decide)) (.next (.reg .mload) (.next (.push [0x07,
    0x20] (by decide)) (.next (.reg .mload) (.next (.reg .eq) (.next (.reg .iszero) (.next (.push
    [0x40, 0xe0] (by decide)) (.branch (cwPH_4073 jm) (cwPH_40e0 tl)))))))))))))

theorem cw_h1348 : t_405e_c1348 = cwPH_405e 20 (.branchTo .undefined 50) := rfl
theorem cw_h50 : t_405e_c50 = cwPH_405e 78 (.branchTo .undefined 79) := rfl
theorem cw_h79 : t_405e_c79 = cwPH_405e 100 (.branch t_41db_c79 .undefined) := rfl
theorem cw_m20 : t_415f_c20 = cwPH_415f (.branchTo .undefined 50) := rfl
theorem cw_m78 : t_415f_c78 = cwPH_415f (.branchTo .undefined 79) := rfl
theorem cw_m100 : t_415f_c100 = cwPH_415f (.branch t_41db_c79 .undefined) := rfl

/-- **One fee-loop iteration, forward, at any counter `k < 3`** from either starting memory
size (`CwSz`), at the parametric body `cwPH_405e jm tl`. -/
theorem rx_cw_itG {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes} {G R : Nat}
    {k s m jm : Nat} {kw : B256} {tl gS : SFunc} (hk3 : k < 3) (hs : CwSz s m) (hkw : kw.toNat = k)
    {Q : Outcome → Prop} {iw x D1 D0 y F r r' : B256} (hi3 : iw.toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = s)
    (hc : WordAt img 0x720 (Nat.toB256 k)) (hi : WordAt img 0x160 iw)
    (hx : WordAt img (0x320 + 32 * k) x) (hD1 : WordAt img 0x520 D1) (hD0w : WordAt img 0x400 D0)
    (hy : WordAt img 0x5a0 y) (hF : WordAt img 0x200 F) (hr : WordAt img (0x540 + 32 * k) r)
    (hstep : CwStep (kw = iw) x D1 D0 y F r r')
    (hG : 570 + m + R ≤ G) (hroom : S.length + 20 < 1024)
    (kC : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0x760 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0x540 + 32 * k ∨ (0x560 + 32 * k ≤ o ∧ o + 32 ≤ 0x720) →
        WordAt img' o v) →
      WordAt img' (0x540 + 32 * k) r' → WordAt img' 0x720 (Nat.toB256 (k + 1)) → R ≤ g → g ≤ G →
      G = g + (if kw = iw then 540 + m else 570 + m) →
      M' = cwItMem M k (cwItDx (kw = iw) x D1 D0 y) r' →
      SFunc.RunEx cert.prog sevm
        (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M' g)
        gS Q)
    (hjm : cert.prog[jm]? = some (cwPH_415f tl)) (hB : CwLoopB sevm b S k Q tl gS) :
    SFunc.RunEx cert.prog sevm
      (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M G)
      (cwPH_405e jm tl) Q := by
  obtain ⟨hcm, hs32, hsz1⟩ := cwSz_facts hs
  have hk : (Nat.toB256 k).toNat < 3 := by rw [B256.toNat_toB256_of_lt (by omega)]; exact hk3
  obtain ⟨hm, hD0, dx, hbr, hm2, hs2', rfl⟩ := hstep
  have hs2 : ¬ r < F * dx / cwFeeDen := fun h =>
    absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.not_lt.mpr hs2')
  rcases hbr with ⟨he, hle', rfl⟩ | ⟨hne, hle', rfl⟩
  · -- `k = i`
    have hik : iw.toNat = k := by rw [← he]; exact hkw
    have hle : ¬ x * D1 / D0 < y := fun h =>
      absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.not_lt.mpr hle')
    obtain ⟨g1, rfl⟩ : ∃ g, G = g + m + 540 := ⟨G - (m + 540), by omega⟩
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    rw [Nat.add_right_comm g1 m]
    refine rxe_mstoreW (o := 0x740) (c := m) hR hW hsz rfl ⟨hcm, hs32⟩ ?_; clear hR hW hsz; intro hR hW hsz; rw [hsz1] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x160) (v := iw) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hi) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x720) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
    xr (rx_eq rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_zero' (cw_eq_br (k := k) hk3 hik) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x720) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_lt3_ne hk) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_mul rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rxm_mloadW (v := x) (o := 0x320 + 32 * k) hR hsz (cw_idx hk3 (B256.toNat_toB256_of_lt (by omega)) (by decide) (by decide)) ⟨by omega, by decide⟩ (by wautoK hx) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x520) (v := D1) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hD1) (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_mul rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_div rfl (by hrs) ·)
    xr (rx_eq rfl (by hrs) ·)
    xr (rx_or rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (B256.mulGuard_of_nofm hm) ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x400) (v := D0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hD0w) (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ hD0 ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_div rfl (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x5a0) (v := y) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hy) (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_geGuard hle) ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_sub (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreW (o := 0x740) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x760 0x740 32 = 0x760 by decide] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_jump (g := cwPH_415f tl) hjm ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x720) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_lt3_ne hk) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_mul rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rxm_mloadW (v := r) (o := 0x540 + 32 * k) hR hsz (cw_idx hk3 (B256.toNat_toB256_of_lt (by omega)) (by decide) (by decide)) ⟨by omega, by decide⟩ (by wautoK hr) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x200) (v := F) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hF) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mload (o := 0x740) hR hsz rfl (by decide) (by hrs) ·); try wsimp
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_mul rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_div rfl (by hrs) ·)
    xr (rx_eq rfl (by hrs) ·)
    xr (rx_or rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (B256.mulGuard_of_nofm hm2) ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (by decide) ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_div rfl (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_geGuard hs2) ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_sub (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_dup rfl (by hrs) ·)
    refine rxe_mstoreW (o := 0x540 + 32 * k) (c := 3) hR hW hsz (cw_idx hk3 (B256.toNat_toB256_of_lt (by omega)) (by decide) (by decide)) (by kmc) ?_; clear hR hW hsz; intro hR hW hsz; rw [memExtSize_of_le (by decide) (by omega)] at hsz
    xr (rx_pop ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x720) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    rw [cw_inc (k := k) (by omega)]
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    refine rxe_mstoreW (o := 0x720) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x760 0x720 32 = 0x760 by decide] at hsz
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_eq rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine hB _ _ ?_
    refine kC _ _ g1 hR hW hsz (fun o v h ho => by wautoK h) (by wautoK0) (by wautoK0) (by omega)
      (by omega) (by rw [ite_eq_left he]; omega)
      (by unfold cwItMem cwItDx; rw [ite_eq_left he])
  · -- `k ≠ i`
    have hik : iw.toNat ≠ k := fun h => hne (by rw [← toB256_toNat iw, h, ← hkw, toB256_toNat])
    have hle : ¬ x < x * D1 / D0 := fun h =>
      absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.not_lt.mpr hle')
    obtain ⟨g1, rfl⟩ : ∃ g, G = g + m + 570 := ⟨G - (m + 570), by omega⟩
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    rw [Nat.add_right_comm g1 m]
    refine rxe_mstoreW (o := 0x740) (c := m) hR hW hsz rfl ⟨hcm, hs32⟩ ?_; clear hR hW hsz; intro hR hW hsz; rw [hsz1] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x160) (v := iw) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hi) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x720) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
    xr (rx_eq rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (cw_ne_br (k := k) hk3 hik) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x720) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_lt3_ne hk) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_mul rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rxm_mloadW (v := x) (o := 0x320 + 32 * k) hR hsz (cw_idx hk3 (B256.toNat_toB256_of_lt (by omega)) (by decide) (by decide)) ⟨by omega, by decide⟩ (by wautoK hx) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x720) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_lt3_ne hk) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_mul rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rxm_mloadW (v := x) (o := 0x320 + 32 * k) hR hsz (cw_idx hk3 (B256.toNat_toB256_of_lt (by omega)) (by decide) (by decide)) ⟨by omega, by decide⟩ (by wautoK hx) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x520) (v := D1) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hD1) (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_mul rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_div rfl (by hrs) ·)
    xr (rx_eq rfl (by hrs) ·)
    xr (rx_or rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (B256.mulGuard_of_nofm hm) ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x400) (v := D0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hD0w) (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ hD0 ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_div rfl (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_geGuard hle) ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_sub (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreW (o := 0x740) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x760 0x740 32 = 0x760 by decide] at hsz
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x720) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_lt3_ne hk) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_mul rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rxm_mloadW (v := r) (o := 0x540 + 32 * k) hR hsz (cw_idx hk3 (B256.toNat_toB256_of_lt (by omega)) (by decide) (by decide)) ⟨by omega, by decide⟩ (by wautoK hr) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x200) (v := F) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hF) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mload (o := 0x740) hR hsz rfl (by decide) (by hrs) ·); try wsimp
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_mul rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_div rfl (by hrs) ·)
    xr (rx_eq rfl (by hrs) ·)
    xr (rx_or rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (B256.mulGuard_of_nofm hm2) ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (by decide) ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_div rfl (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_geGuard hs2) ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_sub (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_dup rfl (by hrs) ·)
    refine rxe_mstoreW (o := 0x540 + 32 * k) (c := 3) hR hW hsz (cw_idx hk3 (B256.toNat_toB256_of_lt (by omega)) (by decide) (by decide)) (by kmc) ?_; clear hR hW hsz; intro hR hW hsz; rw [memExtSize_of_le (by decide) (by omega)] at hsz
    xr (rx_pop ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x720) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    rw [cw_inc (k := k) (by omega)]
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    refine rxe_mstoreW (o := 0x720) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x760 0x720 32 = 0x760 by decide] at hsz
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_eq rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine hB _ _ ?_
    refine kC _ _ g1 hR hW hsz (fun o v h ho => by wautoK h) (by wautoK0) (by wautoK0) (by omega)
      (by omega) (by rw [ite_eq_right hne]; omega)
      (by unfold cwItMem cwItDx; rw [ite_eq_right hne])

/-- Fee-loop iteration 0, forward, exactly (core): the charge by whether `0 = i`, the
literal memory `cwItMem`. -/
theorem rx_cw_it0E {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes} {G R : Nat}
    {Q : Outcome → Prop} {iw x D1 D0 y F r r' : B256} (hi3 : iw.toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x740)
    (hc : WordAt img 0x720 (Nat.toB256 0)) (hi : WordAt img 0x160 iw)
    (hx : WordAt img (0x320 + 32 * 0) x) (hD1 : WordAt img 0x520 D1) (hD0w : WordAt img 0x400 D0)
    (hy : WordAt img 0x5a0 y) (hF : WordAt img 0x200 F) (hr : WordAt img (0x540 + 32 * 0) r)
    (hstep : CwStep (Bytes.toB256 [0] = iw) x D1 D0 y F r r')
    (hG : 576 + R ≤ G) (hroom : S.length + 20 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0x760 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0x540 + 32 * 0 ∨ (0x560 + 32 * 0 ≤ o ∧ o + 32 ≤ 0x720) →
        WordAt img' o v) →
      WordAt img' (0x540 + 32 * 0) r' → WordAt img' 0x720 (Nat.toB256 1) → R ≤ g → g ≤ G →
      G = g + (if Bytes.toB256 [0] = iw then 546 else 576) →
      M' = cwItMem M 0 (cwItDx (Bytes.toB256 [0] = iw) x D1 D0 y) r' →
      SFunc.RunEx cert.prog sevm
        (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M' g)
        t_405e_c50 Q) :
    SFunc.RunEx cert.prog sevm
      (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M G)
      t_405e_c1348 Q := by
  rw [cw_h1348]
  exact rx_cw_itG (k := 0) (s := 0x740) (m := 6) (kw := Bytes.toB256 [0]) (by decide) (Or.inl ⟨rfl, rfl⟩)
    (by decide) hi3 hR hW hsz hc hi hx hD1 hD0w hy hF hr hstep hG hroom k
    (by rw [← cw_m20]; rfl) (cw_backS rfl (by decide))

/-- One fee-loop iteration, forward (the generated steps of both arms). -/
theorem rx_cw_it0 {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes} {G R : Nat}
    {Q : Outcome → Prop} {iw x D1 D0 y F r r' : B256} (hi3 : iw.toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x740)
    (hc : WordAt img 0x720 (Nat.toB256 0)) (hi : WordAt img 0x160 iw)
    (hx : WordAt img (0x320 + 32 * 0) x) (hD1 : WordAt img 0x520 D1) (hD0w : WordAt img 0x400 D0)
    (hy : WordAt img 0x5a0 y) (hF : WordAt img 0x200 F) (hr : WordAt img (0x540 + 32 * 0) r)
    (hstep : CwStep (Bytes.toB256 [0] = iw) x D1 D0 y F r r')
    (hG : 576 + R ≤ G) (hroom : S.length + 20 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0x760 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0x540 + 32 * 0 ∨ (0x560 + 32 * 0 ≤ o ∧ o + 32 ≤ 0x720) →
        WordAt img' o v) →
      WordAt img' (0x540 + 32 * 0) r' → WordAt img' 0x720 (Nat.toB256 1) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm
        (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M' g)
        t_405e_c50 Q) :
    SFunc.RunEx cert.prog sevm
      (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M G)
      t_405e_c1348 Q :=
  rx_cw_it0E hi3 hR hW hsz hc hi hx hD1 hD0w hy hF hr hstep hG hroom
    fun M' img' g h1 h2 h3 h4 h5 h6 h7 h8 _ _ => k M' img' g h1 h2 h3 h4 h5 h6 h7 h8

/-- Fee-loop iteration 1, forward, exactly (core): the charge by whether `1 = i`, the
literal memory `cwItMem`. -/
theorem rx_cw_it1E {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes} {G R : Nat}
    {Q : Outcome → Prop} {iw x D1 D0 y F r r' : B256} (hi3 : iw.toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x760)
    (hc : WordAt img 0x720 (Nat.toB256 1)) (hi : WordAt img 0x160 iw)
    (hx : WordAt img (0x320 + 32 * 1) x) (hD1 : WordAt img 0x520 D1) (hD0w : WordAt img 0x400 D0)
    (hy : WordAt img 0x5a0 y) (hF : WordAt img 0x200 F) (hr : WordAt img (0x540 + 32 * 1) r)
    (hstep : CwStep (Bytes.toB256 [1] = iw) x D1 D0 y F r r')
    (hG : 573 + R ≤ G) (hroom : S.length + 20 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0x760 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0x540 + 32 * 1 ∨ (0x560 + 32 * 1 ≤ o ∧ o + 32 ≤ 0x720) →
        WordAt img' o v) →
      WordAt img' (0x540 + 32 * 1) r' → WordAt img' 0x720 (Nat.toB256 2) → R ≤ g → g ≤ G →
      G = g + (if Bytes.toB256 [1] = iw then 543 else 573) →
      M' = cwItMem M 1 (cwItDx (Bytes.toB256 [1] = iw) x D1 D0 y) r' →
      SFunc.RunEx cert.prog sevm
        (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M' g)
        t_405e_c79 Q) :
    SFunc.RunEx cert.prog sevm
      (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M G)
      t_405e_c50 Q := by
  rw [cw_h50]
  exact rx_cw_itG (k := 1) (s := 0x760) (m := 3) (kw := Bytes.toB256 [1]) (by decide) (Or.inr ⟨rfl, rfl⟩)
    (by decide) hi3 hR hW hsz hc hi hx hD1 hD0w hy hF hr hstep hG hroom k
    (by rw [← cw_m78]; rfl) (cw_backS rfl (by decide))

/-- Fee-loop iteration 1, forward. -/
theorem rx_cw_it1 {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes} {G R : Nat}
    {Q : Outcome → Prop} {iw x D1 D0 y F r r' : B256} (hi3 : iw.toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x760)
    (hc : WordAt img 0x720 (Nat.toB256 1)) (hi : WordAt img 0x160 iw)
    (hx : WordAt img (0x320 + 32 * 1) x) (hD1 : WordAt img 0x520 D1) (hD0w : WordAt img 0x400 D0)
    (hy : WordAt img 0x5a0 y) (hF : WordAt img 0x200 F) (hr : WordAt img (0x540 + 32 * 1) r)
    (hstep : CwStep (Bytes.toB256 [1] = iw) x D1 D0 y F r r')
    (hG : 573 + R ≤ G) (hroom : S.length + 20 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0x760 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0x540 + 32 * 1 ∨ (0x560 + 32 * 1 ≤ o ∧ o + 32 ≤ 0x720) →
        WordAt img' o v) →
      WordAt img' (0x540 + 32 * 1) r' → WordAt img' 0x720 (Nat.toB256 2) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm
        (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M' g)
        t_405e_c79 Q) :
    SFunc.RunEx cert.prog sevm
      (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M G)
      t_405e_c50 Q :=
  rx_cw_it1E hi3 hR hW hsz hc hi hx hD1 hD0w hy hF hr hstep hG hroom
    fun M' img' g h1 h2 h3 h4 h5 h6 h7 h8 _ _ => k M' img' g h1 h2 h3 h4 h5 h6 h7 h8

/-- Fee-loop iteration 2, forward, exactly (core): the charge by whether `2 = i`, the
literal memory `cwItMem`. -/
theorem rx_cw_it2E {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes} {G R : Nat}
    {Q : Outcome → Prop} {iw x D1 D0 y F r r' : B256} (hi3 : iw.toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x760)
    (hc : WordAt img 0x720 (Nat.toB256 2)) (hi : WordAt img 0x160 iw)
    (hx : WordAt img (0x320 + 32 * 2) x) (hD1 : WordAt img 0x520 D1) (hD0w : WordAt img 0x400 D0)
    (hy : WordAt img 0x5a0 y) (hF : WordAt img 0x200 F) (hr : WordAt img (0x540 + 32 * 2) r)
    (hstep : CwStep (Bytes.toB256 [2] = iw) x D1 D0 y F r r')
    (hG : 573 + R ≤ G) (hroom : S.length + 20 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0x760 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0x540 + 32 * 2 ∨ (0x560 + 32 * 2 ≤ o ∧ o + 32 ≤ 0x720) →
        WordAt img' o v) →
      WordAt img' (0x540 + 32 * 2) r' → WordAt img' 0x720 (Nat.toB256 3) → R ≤ g → g ≤ G →
      G = g + (if Bytes.toB256 [2] = iw then 543 else 573) →
      M' = cwItMem M 2 (cwItDx (Bytes.toB256 [2] = iw) x D1 D0 y) r' →
      SFunc.RunEx cert.prog sevm
        (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M' g)
        t_41db_c79 Q) :
    SFunc.RunEx cert.prog sevm
      (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M G)
      t_405e_c79 Q := by
  rw [cw_h79]
  exact rx_cw_itG (k := 2) (s := 0x760) (m := 3) (kw := Bytes.toB256 [2]) (by decide) (Or.inr ⟨rfl, rfl⟩)
    (by decide) hi3 hR hW hsz hc hi hx hD1 hD0w hy hF hr hstep hG hroom k
    (by rw [← cw_m100]; rfl) cw_backX

/-- Fee-loop iteration 2, forward. -/
theorem rx_cw_it2 {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes} {G R : Nat}
    {Q : Outcome → Prop} {iw x D1 D0 y F r r' : B256} (hi3 : iw.toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x760)
    (hc : WordAt img 0x720 (Nat.toB256 2)) (hi : WordAt img 0x160 iw)
    (hx : WordAt img (0x320 + 32 * 2) x) (hD1 : WordAt img 0x520 D1) (hD0w : WordAt img 0x400 D0)
    (hy : WordAt img 0x5a0 y) (hF : WordAt img 0x200 F) (hr : WordAt img (0x540 + 32 * 2) r)
    (hstep : CwStep (Bytes.toB256 [2] = iw) x D1 D0 y F r r')
    (hG : 573 + R ≤ G) (hroom : S.length + 20 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0x760 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0x540 + 32 * 2 ∨ (0x560 + 32 * 2 ≤ o ∧ o + 32 ≤ 0x720) →
        WordAt img' o v) →
      WordAt img' (0x540 + 32 * 2) r' → WordAt img' 0x720 (Nat.toB256 3) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm
        (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M' g)
        t_41db_c79 Q) :
    SFunc.RunEx cert.prog sevm
      (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M G)
      t_405e_c79 Q :=
  rx_cw_it2E hi3 hR hW hsz hc hi hx hD1 hD0w hy hF hr hstep hG hroom
    fun M' img' g h1 h2 h3 h4 h5 h6 h7 h8 _ _ => k M' img' g h1 h2 h3 h4 h5 h6 h7 h8

end Blanc.Lift.Curve3Pool
