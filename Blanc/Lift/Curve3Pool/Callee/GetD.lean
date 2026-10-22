import Blanc.Lift.Curve3Pool.Callee.GetDLoop
import Blanc.Lift.ReachWalk

/-!
# `get_D` (entry 417, pc `0x4c9`): the callee contract

`getD_spec`: every run of `get_D`'s entry tree from `St b (ρ :: xp0 :: xp1 :: xp2 :: amp :: S) M G`
returns (it never halts the frame), with the result word `v` on top of the caller's stack `S`,
`getDChk xp amp 1 = some v` (the checked model of `Blanc/Lift/StableSwapNewton/Defs.lean`, at
the source's tolerance `1`), the world (`b`) unchanged, and memory changed only in the frame
`[0x140, 0x340)` and the scratch word `0`.  The caller's memory must be word-aligned and cover
the frame (`0x340 ≤ M.size`).

The proof composes the prologue (`ric_gdEntry`), the three `S`-loop iterations
(`ric_gdSIter`), the set-up after it (`ric_gdSPost`, with the `S = 0` early return) and the
Newton loop (`gdLoop_sound`, `loopDChk_eq_fuelLoop`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune
open Blanc.StableSwapNewton

/-- The `S` loop's stack: the bound `3` over the counter address `0x220`. -/
abbrev gdSStk (S : List B256) : List B256 := Nat.toB256 3 :: Nat.toB256 0x220 :: S

/-- After the `S` loop, on naturals: `0` for an empty pool, else the Newton loop from `D = S`. -/
def gdPostRes (x : Fin 3 → Nat) (amp s : Nat) : Option Nat :=
  if s = 0 then some 0 else do
    let ann ← chkMul amp 3
    loopDChk x ann s 1 255 s

section Walk

variable {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M0 M : Mem} {G : Nat}
  {r : Seg} {ws : List B256}

-- SEGMENT: gdSPost
/-- **After the `S` loop**, inverted through the whole Newton loop. -/
theorem ric_gdSPost {x0 x1 x2 amp ρ s xs sc w8 dp d ann n p xv ic : B256}
    (hF : WordFrame M0 M 0x140 (gdFrame x0 x1 x2 amp ρ s xs sc w8 dp d ann n p xv ic))
    (run : SFunc.RunCut progYD sevm [] (St b (gdSStk S) M G)
      (gdSPost (gdHead (.branchTo .undefined 459))) r) :
    calleeOut b S M0 (gdPostRes (gdX x0 x1 x2) amp.toNat s.toNat) r := by
  unfold gdSPost at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_pop s1
  obtain ⟨G4, run⟩ := ric_pushMloadF hF 5 (by decide) rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨hw, G8, run⟩ | ⟨hw, G8, run⟩
  · -- `S == 0`: return `0`
    have hs0 : s = 0 := eq_zero_of_iszero2_eq_zero hw
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_mstore s1
    rw [show (Bytes.toB256 [0x00]).toNat = 0 by decide] at run
    obtain ⟨hout, hw'⟩ := hF.scratch (by decide) (Bytes.toB256 [0x00])
    rw [show (gdFrame x0 x1 x2 amp ρ s xs sc w8 dp d ann n p xv ic).length = 16 from rfl] at hout
    have hsz : (M.write 0 (Bytes.toB256 [0x00]).toBytes).size % 32 = 0 := by
      rw [hout.size]; exact hF.aligned
    have hcov : ∀ o, o + 32 ≤ 0x340 → ((M.write 0 (Bytes.toB256 [0x00]).toBytes).read o 32).2 =
        M.write 0 (Bytes.toB256 [0x00]).toBytes :=
      fun o ho => read_covered rfl hsz (by rw [hout.size]; have := hF.cover; simp only [gdFrame,
        List.length_cons, List.length_nil] at this; omega)
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_mload s1
    rw [show (Bytes.toB256 [0x00]).toNat = 0 by decide, hcov 0 (by decide)] at run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_mload s1
    rw [show (Bytes.toB256 [0x01, 0xc0]).toNat = 0x140 + 32 * 4 by decide,
      hcov _ (by decide)] at run
    have hρ' : Bytes.toB256 ((M.write 0 (Bytes.toB256 [0x00]).toBytes).read (0x140 + 32 * 4)
        32).1 = ρ := hw' 4 ρ rfl
    rw [hρ'] at run
    obtain ⟨G16, hr⟩ := ric_ret run
    have h0 : Bytes.toB256 ((M.write 0 (Bytes.toB256 [0x00]).toBytes).read 0 32).1 =
        Bytes.toB256 [0x00] := hout.word0
    rw [h0] at hr
    have hz : Bytes.toB256 [0x00] = Nat.toB256 0 := by decide
    rw [hz] at hr hout
    unfold gdPostRes
    rw [hs0, show (0 : B256).toNat = 0 from rfl, ite_eq_left rfl]
    exact ⟨0, rfl, Nat.two_pow_pos 256, _, G16, hr, hout⟩
  · -- `S ≠ 0`
    have hs0 := ne_zero_of_iszero2_ne_zero hw
    obtain ⟨G9, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_push s1
    obtain ⟨G11, M1, hF1, run⟩ := ric_pushMstoreF hF 9 (by decide) (lt16 (by decide)) run
    obtain ⟨G12, run⟩ := ric_pushMloadF hF1 5 (by decide) rfl run
    obtain ⟨G13, M2, hF2, run⟩ := ric_pushMstoreF hF1 10 (by decide) (lt16 (by decide)) run
    obtain ⟨G14, run⟩ := ric_pushMloadF hF2 3 (by decide) rfl run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_push s1
    obtain ⟨hm, G16, run⟩ := ric_vyMulT vyRevertT_noOk run
    obtain ⟨G17, M3, hF3, run⟩ := ric_pushMstoreF hF2 11 (by decide) (lt16 (by decide)) run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G21, rfl⟩ := ri_dup (w := Bytes.toB256 [0x00]) rfl s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G22, rfl⟩ := ri_dup (w := Bytes.toB256 [0x02, 0xc0]) rfl s1
    obtain ⟨G23, M4, hF4, run⟩ := ric_mstoreF hF3 12 (by decide) (lt16 (by decide)) run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_add s1
    rw [show Bytes.toB256 [0xff] + Bytes.toB256 [0x00] = Nat.toB256 255 by decide,
      show Bytes.toB256 [0x02, 0xc0] = Nat.toB256 0x2c0 by decide] at run
    rw [show Bytes.toB256 [0x00] = Nat.toB256 0 by decide] at hF4
    have hAt : gdAt b S M0 x0 x1 x2 ρ s (amp * Bytes.toB256 [0x03]) 0 s.toNat
        (St b (gdStk S) M4 G24) := by
      refine ⟨B256.toNat_lt s, M4, G24, amp, xs, sc, w8, Nat.toB256 0, p, xv, ic, rfl, ?_⟩
      rw [toB256_toNat]; exact hF4
    have hloop := gdLoop_sound 0 s.toNat _ r (by decide) hAt run
    have hsN : s.toNat ≠ 0 := B256.toNat_ne_zero hs0
    unfold gdPostRes
    rw [ite_eq_right hsN, show (3 : Nat) = (Bytes.toB256 [0x03]).toNat by decide,
      chkMul_toNat_of_nofm hm, Option.bind_eq_bind, Option.bind_some, loopDChk_eq_fuelLoop]
    exact hloop

-- SEGMENT: gdSIter
/-- **One `S`-loop iteration**, inverted up to its `JUMPI`: `_x = xp[j]`, `S += _x` checked, the
counter `j + 1`. -/
theorem ric_gdSIter (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {j : Nat}
    {x s : B256} (hj : ws[7]? = some (Nat.toB256 j)) (hj3 : j < 3) (hx : ws[j]? = some x)
    (hs : ws[5]? = some s) {jmp : SFunc}
    (run : SFunc.RunCut progYD sevm C (St b (gdSStk S) M G) (gdSIter jmp) r) :
    chkAdd s.toNat x.toNat = some (s + x).toNat ∧ ∃ G' M',
      WordFrame M0 M' 0x140 (((ws.set 6 x).set 5 (s + x)).set 7 (Nat.toB256 (j + 1))) ∧
      SFunc.RunCut progYD sevm C (St b (Bytes.toB256 [0x04, 0xef] ::
        B256.eqCheck (B256.eqCheck (Nat.toB256 3) (Nat.toB256 (j + 1))) 0 :: gdSStk S) M' G')
        jmp r := by
  unfold gdSIter at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨G3, run⟩ := ric_pushMloadF hF 7 (by decide) hj run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_mul s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_add s1
  obtain ⟨G7, run⟩ := ric_mloadF hF j (gdXpAddr hj3) hx run
  obtain ⟨G8, M1, hF1, run⟩ := ric_pushMstoreF hF 6 (by decide) (by rw [hlen]; decide) run
  have hs1 : (ws.set 6 x)[5]? = some s := by rw [List.getElem?_set_ne (by decide)]; exact hs
  have hx1 : (ws.set 6 x)[6]? = some x := by rw [List.getElem?_set_self (by rw [hlen]; decide)]
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G10, rfl⟩ := ri_dup (w := Bytes.toB256 [0x01, 0xe0]) rfl s1
  obtain ⟨G11, run⟩ := ric_mloadF hF1 5 (by decide) hs1 run
  obtain ⟨G12, run⟩ := ric_pushMloadF hF1 6 (by decide) hx1 run
  obtain ⟨ha, G13, run⟩ := ric_vyAddT vyRevertT_noOk run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G14, rfl⟩ := ri_dup (w := Bytes.toB256 [0x01, 0xe0]) rfl s1
  obtain ⟨G15, M2, hF2, run⟩ := ric_mstoreF hF1 5 (by decide)
    (by rw [List.length_set, hlen]; decide) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_pop s1
  have hj2 : ((ws.set 6 x).set 5 (s + x))[7]? = some (Nat.toB256 j) := by
    rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide)]; exact hj
  obtain ⟨G17, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_dup (w := Nat.toB256 0x220) rfl s1
  obtain ⟨G19, run⟩ := ric_mloadF hF2 7 (by decide) hj2 run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_add s1
  rw [one_add_toB256 (by omega)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G22, rfl⟩ := ri_dup (w := Nat.toB256 (j + 1)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_dup (w := Nat.toB256 0x220) rfl s1
  obtain ⟨G24, M3, hF3, run⟩ := ric_mstoreF hF2 7 (by decide)
    (by rw [List.length_set, List.length_set, hlen]; decide) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_dup (w := Nat.toB256 3) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_push s1
  exact ⟨chkAdd_toNat_of_lt ha, G28, M3, hF3, run⟩

-- SEGMENT: gdEntry
/-- The prologue, inverted: the arguments in the frame, `S = 0`, the `S`-loop counter `0`. -/
theorem ric_gdPro {ρ x0 x1 x2 amp : B256} (hsz : M.size % 32 = 0) (hcov : 0x340 ≤ M.size)
    {rest : SFunc}
    (run : SFunc.RunCut progYD sevm [] (St b (ρ :: x0 :: x1 :: x2 :: amp :: S) M G)
      (gdEntry rest) r) :
    ∃ M' G' xs w8 dp d ann n p xv ic,
      WordFrame M M' 0x140 (gdFrame x0 x1 x2 amp ρ (Nat.toB256 0) xs (Nat.toB256 0) w8 dp d ann n
        p xv ic) ∧
      SFunc.RunCut progYD sevm [] (St b (gdSStk S) M' G') rest r := by
  have hF := WordFrame.init (lo := 0x140) (n := 16) hsz hcov
  unfold gdEntry at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨G2, M1, hF, run⟩ := ric_pushMstoreF hF 4 (by decide) (lt16 (by decide)) run
  obtain ⟨G3, M2, hF, run⟩ := ric_pushMstoreF hF 0 (by decide) (lt16 (by decide)) run
  obtain ⟨G4, M3, hF, run⟩ := ric_pushMstoreF hF 1 (by decide) (lt16 (by decide)) run
  obtain ⟨G5, M4, hF, run⟩ := ric_pushMstoreF hF 2 (by decide) (lt16 (by decide)) run
  obtain ⟨G6, M5, hF, run⟩ := ric_pushMstoreF hF 3 (by decide) (lt16 (by decide)) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s1
  obtain ⟨G8, M6, hF, run⟩ := ric_pushMstoreF hF 5 (by decide) (lt16 (by decide)) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G12, rfl⟩ := ri_dup (w := Bytes.toB256 [0x00]) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_dup (w := Bytes.toB256 [0x02, 0x20]) rfl s1
  obtain ⟨G14, M7, hF, run⟩ := ric_mstoreF hF 7 (by decide) (lt16 (by decide)) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_add s1
  rw [show Bytes.toB256 [0x03] + Bytes.toB256 [0x00] = Nat.toB256 3 by decide,
    show Bytes.toB256 [0x02, 0x20] = Nat.toB256 0x220 by decide] at run
  rw [show Bytes.toB256 [0x00] = Nat.toB256 0 by decide] at hF
  exact ⟨M7, G15, _, _, _, _, _, _, _, _, _, hF, run⟩

/-- **The prologue, the `S` loop and the rest**, inverted: the checked sums, then
`gdPostRes`. -/
theorem ric_gdEntry {ρ x0 x1 x2 amp : B256} (hsz : M.size % 32 = 0) (hcov : 0x340 ≤ M.size)
    (run : SFunc.RunCut progYD sevm [] (St b (ρ :: x0 :: x1 :: x2 :: amp :: S) M G)
      (gdEntry (gdSIter (.branchTo .undefined 431))) r) :
    calleeOut b S M ((chkAdd 0 x0.toNat).bind fun s1 => (chkAdd s1 x1.toNat).bind fun s2 =>
      (chkAdd s2 x2.toNat).bind fun s3 => gdPostRes (gdX x0 x1 x2) amp.toNat s3) r := by
  obtain ⟨M1, G1, xs, w8, dp, d, ann, n, p, xv, ic, hF, run⟩ := ric_gdPro hsz hcov run
  obtain ⟨ha0, G16, M8, hF, run⟩ := ric_gdSIter hF rfl (j := 0) rfl (by decide) rfl rfl run
  rcases ric_branchTo (by decide) progGD_431 run with ⟨h0, -⟩ | ⟨-, G17, run⟩
  · exact absurd h0 (iszero_eq3_ne (by decide))
  obtain ⟨ha1, G18, M9, hF, run⟩ := ric_gdSIter hF rfl (j := 1) rfl (by decide) rfl rfl run
  rcases ric_branchTo (by decide) progGD_445 run with ⟨h0, -⟩ | ⟨-, G19, run⟩
  · exact absurd h0 (iszero_eq3_ne (by decide))
  obtain ⟨ha2, G20, M10, hF, run⟩ := ric_gdSIter hF rfl (j := 2) rfl (by decide) rfl rfl run
  rcases ric_branch run with ⟨-, G21, run⟩ | ⟨h0, -⟩
  swap
  · exact absurd iszero_eq3_eq h0
  have h := ric_gdSPost hF run
  rw [show (Nat.toB256 0).toNat = 0 by decide] at ha0
  rw [ha0, Option.bind_some, ha1, Option.bind_some, ha2, Option.bind_some]
  exact h

/-! ## The contract -/

theorem t_04c9_c417_eq : t_04c9_c417 = gdEntry (gdSIter (.branchTo .undefined 431)) :=
  Option.some.inj (progGD_417_t.symm.trans progGD_417)

theorem gdPostRes_getDChk {x0 x1 x2 amp y : Nat}
    (h : ((chkAdd 0 x0).bind fun s1 => (chkAdd s1 x1).bind fun s2 =>
      (chkAdd s2 x2).bind fun s3 => gdPostRes (V3.mk x0 x1 x2).get amp s3) = some y) :
    getDChk (V3.mk x0 x1 x2).get amp 1 = some y := by
  unfold getDChk
  rw [show (V3.mk x0 x1 x2).get 0 = x0 from rfl, show (V3.mk x0 x1 x2).get 1 = x1 from rfl,
    show (V3.mk x0 x1 x2).get 2 = x2 from rfl]
  simp only [Option.bind_eq_bind] at h ⊢
  unfold gdPostRes at h
  exact h

-- SEGMENT: getD_spec
/-- **`get_D`'s callee contract.**  Any outcome of the entry tree from the call's state is a
return: the result `v` over the caller's stack, `getDChk xp amp 1 = some v`, the world `b`
unchanged, the memory's size unchanged, `v` at scratch word `0`, and (on a well-formed memory)
every byte off `get_D`'s windows `[0, 0x20)` and `[0x140, 0x340)` kept. -/
theorem getD_spec {sevm : Sevm} {b : Devm} {ρ x0 x1 x2 amp : B256} {S : List B256} {M : Mem}
    {G : Nat} {o : Outcome} (hsz : M.size % 32 = 0) (hcov : 0x340 ≤ M.size)
    (run : SFunc.Run cert.prog sevm (St b (ρ :: x0 :: x1 :: x2 :: amp :: S) M G) t_04c9_c417 o) :
    ∃ d, o = .returned d ∧ ∃ v M' G', d = St b (v :: S) M' G' ∧
      getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get amp.toNat 1 = some v.toNat ∧
      M'.size = M.size ∧ Words M' [(0, v)] ∧
      (Mem.Wf M → Mem.KeepsOff M M' [(0, 32), (0x140, 0x340)] ∧ Mem.Wf M') := by
  have hcut := SFunc.runP_iff_runCutP_nil.mp run
  rw [t_04c9_c417_eq] at hcut
  obtain ⟨y, hres, hy, M', G', hr, hout⟩ := ric_gdEntry hsz hcov hcut
  have ho : o = .returned (St b (Nat.toB256 y :: S) M' G') := by injection hr
  subst ho
  refine ⟨_, rfl, Nat.toB256 y, M', G', rfl, ?_, hout.size, hout.words (by omega),
    fun hwf => ⟨hout.keepsOff hwf, hout.wf hwf⟩⟩
  rw [B256.toNat_toB256_of_lt hy]
  exact gdPostRes_getDChk hres

/-! ## Kernel facts for the frame-walk bridge (`xa_callee`) -/

/-- `get_D`'s entry closure. -/
def gdEntries : List Nat := [417, 431, 445, 459, 473, 487, 488, 489, 503, 517, 531, 532, 533]

theorem gd_execFreeSet : ExecFreeSet cert.prog gdEntries = true := by decide +kernel

theorem gd_free : t_04c9_c417.execFreeIn gdEntries = true := by decide +kernel

end Walk

end Blanc.Lift.Curve3Pool
