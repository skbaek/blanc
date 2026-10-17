import Blanc.Lift.Curve3Pool.Walk.ViewsDyuPost
import Blanc.Lift.Curve3Pool.Walk.ViewsDyRaw

/-! # `get_dy_underlying`: pc-zero safety and the model's exact checked arithmetic -/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The pushed `PRECISION_MUL` words agree with the model's `precMul`. -/
theorem dyu_precMul_toNat {n : Nat} (hn : n < 3) :
    (pickWord3 n dyuP1 dyuPm dyuPm).toNat = precMul.get ⟨n, hn⟩ :=
  dy_pickWord3_toNat hn dyuP1 dyuPm dyuPm

/-- A successful `get_dy_underlying` frame computes the model, with no children or state
change. -/
theorem dyu_raw_of (hc : Cert.CheckedM code cert mems true)
    {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selGetDyUnderlying)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have h : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨_, h⟩ := xa_vd_getDyUnderlying hcode hlen hcd hsel h
  obtain ⟨hval, x0, x1, x2, b1, M1, G1, hb1, hi, hxp, hmx, hax, h, hV⟩ :=
    xa_dyu_x hc hcode hfork hck.abs h
  have ha1 : Abstracts (b1.getStor sevm.currentTarget) s := by
    rw [hb1.getStor]; exact hck.abs
  obtain ⟨y, b2, M2, G2, hb2, h, amp, hamp, hi', hj, hy, hV⟩ :=
    xa_dyu_y hc hcode hfork ha1 hV h
  have hb := hb1.trans hb2
  have ha2 : Abstracts (b2.getStor sevm.currentTarget) s := by
    rw [hb.getStor]; exact hck.abs
  obtain ⟨hL, hs0, hs1, hr, hm1, hs2, hstor, hlogs, hout⟩ :=
    xa_dyu_post hcode hfork hj hV h
  have h1 : (Bytes.toB256 [1]).toNat = 1 := rfl
  have hden : (Bytes.toB256 [0x02, 0x54, 0x0b, 0xe4, 0x00]).toNat = feeDen := by decide
  have hf : (b2.getStorVal sevm.currentTarget (Bytes.toB256 [2])).toNat = s.fee := by
    rw [getStorVal_eq]; exact ha2.fee
  have hg : getDyUnderlying s (quietEnv sevm) ⟨(dyI sevm).toNat, hi⟩ ⟨(dyJ sevm).toNat, hj⟩
      (dyDx sevm).toNat =
      some (dyuAmount sevm x0 x1 x2 y - dyuFee sevm b2 x0 x1 x2 y).toNat := by
    unfold getDyUnderlying
    simp only [Option.bind_eq_bind]
    rw [hxp, Option.bind_some, ← dy_pickWord3_toNat hi, ← dyu_precMul_toNat hi,
      chkMul_toNat_of_nofm hmx, Option.bind_some,
      chkAdd_toNat_of_lt hax, Option.bind_some,
      show (quietEnv sevm).time = sevm.benvStat.time.toNat from rfl, hamp, Option.bind_some,
      hy, Option.bind_some, ← dy_pickWord3_toNat hj, chkSub_toNat_of_le hs0, Option.bind_some,
      ← h1, chkSub_toNat_of_le hs1, Option.bind_some,
      ← dyu_precMul_toNat hj, chkDiv_toNat_of_ne hr, Option.bind_some,
      ← hf, chkMul_toNat_of_nofm hm1, Option.bind_some, ← hden,
      chkDiv_toNat_of_ne (by decide), Option.bind_some]
    exact chkSub_toNat_of_le hs2
  have hdec : decodeCall sevm =
      .getDyUnderlying (dyI sevm).toNat (dyJ sevm).toNat (dyDx sevm).toNat :=
    decodeCall_at (k := 5) rfl hsel hlen
  refine ⟨quietEnv sevm,
    viewOut s (dyuAmount sevm x0 x1 x2 y - dyuFee sevm b2 x0 x1 x2 y).toNat, ?_, ?_⟩
  · rw [hdec]
    show (if (quietEnv sevm).value = 0 then body s (quietEnv sevm) _ else none) = _
    rw [show (quietEnv sevm).value = 0 by rw [quietEnv, hval]; rfl, ite_eq_left rfl]
    simp only [body, idx, hi, hj, ↓reduceDIte, Option.bind_eq_bind, Option.bind_some]
    rw [hg]
    rfl
  · refine rawEffect_view (envOf_quiet _) (by rw [hdec]; rfl)
      (fun x => by rw [hstor, hb.getStor]; rfl) ?_ ?_ ?_
    · rw [hlogs, hb.logs]
      change pre.logs = pre.logs ++ (Exec.childFrames exc).flatMap (fun c => c.post.logs)
      rw [hL, List.flatMap_nil, List.append_nil]
    · rw [hout, word, toB256_toNat]
    · intro c hc'
      change c ∈ Exec.childFrames exc at hc'
      rw [hL] at hc'
      cases hc'

end Blanc.Lift.Curve3Pool
