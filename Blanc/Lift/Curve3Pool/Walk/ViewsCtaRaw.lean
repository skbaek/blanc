import Blanc.Lift.Curve3Pool.Walk.ViewsCtaPost
import Blanc.Lift.Curve3Pool.Walk.ViewsGvpRaw

/-!
# `calc_token_amount(amounts, deposit)`: the frame and its raw effect

The segments of `ViewsCta*.lean` composed from the dispatcher; the model's `calcTokenAmount`
read off them, with the environment's supply the `totalSupply()` reply (`vEnv`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The model's `calc_token_amount` when every check passes. -/
theorem calcTokenAmount_eq {s : State} {e : Env} {amounts : V3} {dep : Bool}
    {amp D0 D1 T df : Nat} {nb : V3}
    (hamp : aChk s e.time = some amp) (hD0 : getDMem s.balances amp = some D0)
    (hb : V3.ofFnM (fun k => if dep then chkAdd (s.balances.get k) (amounts.get k)
      else chkSub (s.balances.get k) (amounts.get k)) = some nb)
    (hD1 : getDMem nb amp = some D1) (hT : e.supply = some T)
    (hdf : (if dep then chkSub D1 D0 else chkSub D0 D1) = some df) {q r : Nat}
    (hm : chkMul df T = some q) (hq : chkDiv q D0 = some r) :
    calcTokenAmount s e amounts dep = some r := by
  unfold calcTokenAmount
  simp only [Option.bind_eq_bind]
  rw [hamp, Option.bind_some, hD0, Option.bind_some, hb, Option.bind_some, hD1, Option.bind_some,
    hT, Option.bind_some]
  cases dep
  · rw [ite_eq_right (by decide)] at hdf ⊢
    rw [hdf, Option.bind_some, hm, Option.bind_some, hq]
  · rw [ite_eq_left rfl] at hdf ⊢
    rw [hdf, Option.bind_some, hm, Option.bind_some, hq]

/-- One loop step's checked update, as the model states it. -/
theorem ctaUpd_chk {dep B a v : B256} {d : Nat} (hd : dep.toNat = d) (hd2 : d < 2)
    (hu : CtaUpd dep B a v) :
    (if decide (d = 1) = true then chkAdd B.toNat a.toNat else chkSub B.toNat a.toNat) =
      some v.toNat := by
  rcases hu with ⟨hne, hadd, rfl⟩ | ⟨rfl, hle, rfl⟩
  · have h1 : d = 1 := by
      have := toNat_ne_zero hne
      omega
    rw [ite_eq_left (decide_eq_true h1)]
    exact chkAdd_toNat_of_lt hadd
  · have h0 : ¬ d = 1 := by
      rw [← hd]
      decide
    rw [ite_eq_right (by rw [decide_eq_true_iff]; exact h0)]
    exact chkSub_toNat_of_le hle

section

variable {sevm : Sevm} {post : Devm} {s : State}

/-- **`calc_token_amount`'s raw effect**, given the certificate's checkedness. -/
theorem cta_raw_of (hc : Cert.CheckedM code cert mems true) {pre : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selCalcTokenAmount)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have h : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨_, h⟩ := xa_vd_calcTokenAmount hcode hlen hcd hsel h
  obtain ⟨hval, hdep, amp, D0, b2, M, G1, hb2, hamp, hD0, h, hV⟩ :=
    xa_cta_pre hc hcode hfork hck.abs h
  obtain ⟨v0, v1, v2, M, G2, hu0, hu1, hu2, h, hV⟩ := xa_cta_loop hcode hV h
  obtain ⟨D1, M, G3, hD1, h, hV⟩ := xa_cta_d1 hc hcode hfork hV h
  obtain ⟨c, df, hL, ⟨htgt, hdata, hstat, hlen', hclogs⟩, hdf, hm, hD0z, hstor, hlogs, hout⟩ :=
    xa_cta_tail hcode hfork (by rw [hb2.getStor]; exact htok) hV h
  -- the decoded arguments
  have ea0 : ctaAmt sevm 0 = Sevm.argWord sevm 0 := by
    unfold ctaAmt Sevm.argWord
    rw [show Bytes.toB256 [32] * Bytes.toB256 [0] + Bytes.toB256 [4] = 32 * 0 + 4 by decide]
  have ea1 : ctaAmt sevm 1 = Sevm.argWord sevm (0 + 1) := by
    unfold ctaAmt Sevm.argWord
    rw [show Bytes.toB256 [32] * Bytes.toB256 [1] + Bytes.toB256 [4] = 32 * (0 + 1) + 4 by decide]
  have ea2 : ctaAmt sevm 2 = Sevm.argWord sevm (0 + 2) := by
    unfold ctaAmt Sevm.argWord
    rw [show Bytes.toB256 [32] * Bytes.toB256 [2] + Bytes.toB256 [4] = 32 * (0 + 2) + 4 by decide]
  have ed : ctaDep sevm = Sevm.argWord sevm 3 := by
    unfold ctaDep Sevm.argWord
    rw [show Bytes.toB256 [100] = 32 * 3 + 4 by decide]
  have hd : (ctaDep sevm).toNat = arg sevm 3 := by rw [ed]; rfl
  have hd2 : arg sevm 3 < 2 := by
    rw [← hd]
    have e := hdep
    rw [B256.lt_iff_toNat_lt_toNat] at e
    exact e
  have hdec : decodeCall sevm = .calcTokenAmount (argV3 sevm 0) (arg sevm 3) :=
    decodeCall_at (k := 2) rfl hsel hlen
  -- the model's balance update
  have hbal : ∀ k : Fin 3, (ctaB sevm pre k).toNat = s.balances.get k := hck.abs.balances
  have hb : V3.ofFnM (fun k => if decide (arg sevm 3 = 1) = true then
      chkAdd (s.balances.get k) ((argV3 sevm 0).get k)
      else chkSub (s.balances.get k) ((argV3 sevm 0).get k)) =
      some ⟨v0.toNat, v1.toNat, v2.toNat⟩ := by
    have c0 := ctaUpd_chk hd hd2 hu0
    have c1 := ctaUpd_chk hd hd2 hu1
    have c2 := ctaUpd_chk hd hd2 hu2
    rw [hbal 0, ea0] at c0
    rw [hbal 1, ea1] at c1
    rw [hbal 2, ea2] at c2
    unfold V3.ofFnM
    simp only [Option.bind_eq_bind]
    rw [show (argV3 sevm 0).get 0 = (Sevm.argWord sevm 0).toNat from rfl, c0, Option.bind_some,
      show (argV3 sevm 0).get 1 = (Sevm.argWord sevm (0 + 1)).toNat from rfl, c1,
      Option.bind_some,
      show (argV3 sevm 0).get 2 = (Sevm.argWord sevm (0 + 2)).toNat from rfl, c2,
      Option.bind_some]
  have hbal0 : (⟨(ctaB sevm pre 0).toNat, (ctaB sevm pre 1).toNat, (ctaB sevm pre 2).toNat⟩ : V3)
      = s.balances := by
    rw [hbal 0, hbal 1, hbal 2]
    rfl
  rw [hbal0] at hD0
  have hdiff : (if decide (arg sevm 3 = 1) = true then chkSub D1.toNat D0.toNat
      else chkSub D0.toNat D1.toNat) = some df.toNat := by
    rcases hdf with ⟨hne, hle, rfl⟩ | ⟨h0, hle, rfl⟩
    · have h1 : arg sevm 3 = 1 := by
        have := toNat_ne_zero hne
        omega
      rw [ite_eq_left (decide_eq_true h1)]
      exact chkSub_toNat_of_le hle
    · have h0' : ¬ arg sevm 3 = 1 := by
        rw [← hd, h0]
        decide
      rw [ite_eq_right (by rw [decide_eq_true_iff]; exact h0')]
      exact chkSub_toNat_of_le hle
  have hg := calcTokenAmount_eq (e := vEnv sevm (some (vSupply c).toNat))
    (amounts := argV3 sevm 0) hamp hD0 hb hD1 rfl hdiff (chkMul_toNat_of_nofm hm)
    (chkDiv_toNat_of_ne hD0z)
  refine ⟨vEnv sevm (some (vSupply c).toNat), viewOut s (df * vSupply c / D0).toNat, ?_, ?_⟩
  · rw [hdec]
    show (if (vEnv sevm _).value = 0 then body s _ (.calcTokenAmount _ _) else none) = _
    rw [show (vEnv sevm (some (vSupply c).toNat)).value = 0 by rw [vEnv, hval]; rfl,
      ite_eq_left rfl]
    show (req (arg sevm 3 < 2)).bind (fun _ =>
      (calcTokenAmount s _ (argV3 sevm 0) (decide (arg sevm 3 = 1))).bind
        (fun r => some (viewOut s r))) = _
    rw [req, ite_eq_left hd2, Option.bind_some, hg, Option.bind_some]
  · have hch : children ⟨0, sevm, pre, .ok post, exc⟩ = [c] := hL
    refine rawEffect_view (envOf_vEnv hch (by rw [htgt, hb2.getStor]; rfl) hdata hlen')
      (by rw [hdec]; rfl) (fun x => by rw [hstor, hb2.getStor]; rfl) ?_ ?_ ?_
    · rw [hch, hlogs, hb2.logs]
      simp only [List.flatMap_cons, List.flatMap_nil, hclogs, List.append_nil]
    · rw [hout, word, toB256_toNat]
    · intro c' hc'
      rw [hch, List.mem_singleton] at hc'
      rw [hc']
      exact hstat

end

end Blanc.Lift.Curve3Pool
