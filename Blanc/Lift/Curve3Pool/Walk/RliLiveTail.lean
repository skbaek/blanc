import Blanc.Lift.Curve3Pool.Walk.RliLiveEnd

/-!
# `remove_liquidity_imbalance`, forward: the transfer loop composed

From the loop's head `t_3769_c1368` to `STOP`, over every path the amounts select:
`rx_rli_tail2a` (iteration 2 at `t_3769_c1045`, no transfer yet), `rx_rli_tail2b` (iteration 2 at
`t_3769_c48`), `rx_rli_tail1a`, `rx_rli_tail1b`, `rx_rli_tail0`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- Iteration 2 at `t_3769_c1045` to `STOP`. -/
theorem rx_rli_tail2a {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G U : Nat} {Q : Outcome → Prop} {T D1 f0 f1 f2 Bw : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = 0x920) (hc : WordAt img 0x900 (Nat.toB256 2))
    (hT : WordAt img 0x140 T) (hD1 : WordAt img 0x480 D1) (hf0 : WordAt img 0x5a0 f0)
    (hf1 : WordAt img 0x5c0 f1) (hf2 : WordAt img 0x5e0 f2) (hBw : WordAt img 0x780 Bw)
    (hTX : ¬ T < Bw)
    (hp2 : rliAmt sevm 2 ≠ 0 → CoinPushOkAt sevm W W (σ.get (coinsBase + Nat.toB256 2))
      (rliAmt sevm 2) U 0xaa0 0xb40)
    (hG : 42000 + 1 * U ≤ G) (hGb : G + 3000 < 2 ^ 256) (hroom : S.length + 40 < 1024)
    (k : ∀ D : Devm, ExLive sevm W D (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) →
      (∃ L ts data, D.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
        Bytes.toB256 (data.sliceD 0x60 32 0) = f0 ∧ Bytes.toB256 (data.sliceD 0x80 32 0) = f1 ∧
        Bytes.toB256 (data.sliceD 0xa0 32 0) = f2 ∧ Bytes.toB256 (data.sliceD 0xc0 32 0) = D1 ∧
        Bytes.toB256 (data.sliceD 0xe0 32 0) = T - Bw) → Q (.halted D)) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: S) M G) t_3769_c1045 Q := by
  refine rx_rli_push2a (R := 30000) hfork hdepth hL hR hW hsz hc hp2 (by omega) hGb hroom ?_ ?_
  · intro b' M' img' g hL' hR' hW' hsz' hk' hc' hg1 hg2
    exact rx_rli_end920 hfork hstatic hL' hR' hW' hsz' (hk' _ _ hT (by omega)) (hk' _ _ hD1 (by omega)) (hk' _ _ hf0 (by omega)) (hk' _ _ hf1 (by omega)) (hk' _ _ hf2 (by omega)) (hk' _ _ hBw (by omega)) hTX hg1 (by omega) k
  · intro b' M' img' g hL' hR' hW' hsz' hk' hc' hg1 hg2
    exact rx_rli_endB60 hfork hstatic hL' hR' hW' hsz' (hk' _ _ hT (by omega)) (hk' _ _ hD1 (by omega)) (hk' _ _ hf0 (by omega)) (hk' _ _ hf1 (by omega)) (hk' _ _ hf2 (by omega)) (hk' _ _ hBw (by omega)) hTX hg1 (by omega) k

/-- Iteration 2 at `t_3769_c48` to `STOP`. -/
theorem rx_rli_tail2b {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G U : Nat} {Q : Outcome → Prop} {T D1 f0 f1 f2 Bw : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = 0xb60) (hc : WordAt img 0x900 (Nat.toB256 2))
    (hT : WordAt img 0x140 T) (hD1 : WordAt img 0x480 D1) (hf0 : WordAt img 0x5a0 f0)
    (hf1 : WordAt img 0x5c0 f1) (hf2 : WordAt img 0x5e0 f2) (hBw : WordAt img 0x780 Bw)
    (hTX : ¬ T < Bw)
    (hp2 : rliAmt sevm 2 ≠ 0 → CoinPushOkAt sevm W W (σ.get (coinsBase + Nat.toB256 2))
      (rliAmt sevm 2) U 0xaa0 0xb40)
    (hG : 42000 + 1 * U ≤ G) (hGb : G + 3000 < 2 ^ 256) (hroom : S.length + 40 < 1024)
    (k : ∀ D : Devm, ExLive sevm W D (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) →
      (∃ L ts data, D.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
        Bytes.toB256 (data.sliceD 0x60 32 0) = f0 ∧ Bytes.toB256 (data.sliceD 0x80 32 0) = f1 ∧
        Bytes.toB256 (data.sliceD 0xa0 32 0) = f2 ∧ Bytes.toB256 (data.sliceD 0xc0 32 0) = D1 ∧
        Bytes.toB256 (data.sliceD 0xe0 32 0) = T - Bw) → Q (.halted D)) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: S) M G) t_3769_c48 Q := by
  refine rx_rli_push2b (R := 30000) hfork hdepth hL hR hW hsz hc hp2 (by omega) hGb hroom ?_ ?_
  · intro b' M' img' g hL' hR' hW' hsz' hk' hc' hg1 hg2
    exact rx_rli_endB60 hfork hstatic hL' hR' hW' hsz' (hk' _ _ hT (by omega)) (hk' _ _ hD1 (by omega)) (hk' _ _ hf0 (by omega)) (hk' _ _ hf1 (by omega)) (hk' _ _ hf2 (by omega)) (hk' _ _ hBw (by omega)) hTX hg1 (by omega) k
  · intro b' M' img' g hL' hR' hW' hsz' hk' hc' hg1 hg2
    exact rx_rli_endB60 hfork hstatic hL' hR' hW' hsz' (hk' _ _ hT (by omega)) (hk' _ _ hD1 (by omega)) (hk' _ _ hf0 (by omega)) (hk' _ _ hf1 (by omega)) (hk' _ _ hf2 (by omega)) (hk' _ _ hBw (by omega)) hTX hg1 (by omega) k

/-- Iterations 1–2 from `t_3769_c1037` to `STOP`. -/
theorem rx_rli_tail1a {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G U : Nat} {Q : Outcome → Prop} {T D1 f0 f1 f2 Bw : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = 0x920) (hc : WordAt img 0x900 (Nat.toB256 1))
    (hT : WordAt img 0x140 T) (hD1 : WordAt img 0x480 D1) (hf0 : WordAt img 0x5a0 f0)
    (hf1 : WordAt img 0x5c0 f1) (hf2 : WordAt img 0x5e0 f2) (hBw : WordAt img 0x780 Bw)
    (hTX : ¬ T < Bw)
    (hp1 : rliAmt sevm 1 ≠ 0 → CoinPushOkAt sevm W W (σ.get (coinsBase + Nat.toB256 1))
      (rliAmt sevm 1) U 0xaa0 0xb40) (hp2 : rliAmt sevm 2 ≠ 0 → CoinPushOkAt sevm W W (σ.get (coinsBase + Nat.toB256 2))
      (rliAmt sevm 2) U 0xaa0 0xb40)
    (hG : 54000 + 2 * U ≤ G) (hGb : G + 3000 < 2 ^ 256) (hroom : S.length + 40 < 1024)
    (k : ∀ D : Devm, ExLive sevm W D (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) →
      (∃ L ts data, D.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
        Bytes.toB256 (data.sliceD 0x60 32 0) = f0 ∧ Bytes.toB256 (data.sliceD 0x80 32 0) = f1 ∧
        Bytes.toB256 (data.sliceD 0xa0 32 0) = f2 ∧ Bytes.toB256 (data.sliceD 0xc0 32 0) = D1 ∧
        Bytes.toB256 (data.sliceD 0xe0 32 0) = T - Bw) → Q (.halted D)) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: S) M G) t_3769_c1037 Q := by
  refine rx_rli_push1a (R := 42000 + U) hfork hdepth hL hR hW hsz hc hp1 (by omega) hGb hroom ?_ ?_
  · intro b' M' img' g hL' hR' hW' hsz' hk' hc' hg1 hg2
    exact rx_rli_tail2a hfork hstatic hdepth hL' hR' hW' hsz' hc' (hk' _ _ hT (by omega)) (hk' _ _ hD1 (by omega)) (hk' _ _ hf0 (by omega)) (hk' _ _ hf1 (by omega)) (hk' _ _ hf2 (by omega)) (hk' _ _ hBw (by omega)) hTX hp2 (by omega) (by omega) hroom k
  · intro b' M' img' g hL' hR' hW' hsz' hk' hc' hg1 hg2
    exact rx_rli_tail2b hfork hstatic hdepth hL' hR' hW' hsz' hc' (hk' _ _ hT (by omega)) (hk' _ _ hD1 (by omega)) (hk' _ _ hf0 (by omega)) (hk' _ _ hf1 (by omega)) (hk' _ _ hf2 (by omega)) (hk' _ _ hBw (by omega)) hTX hp2 (by omega) (by omega) hroom k

/-- Iterations 1–2 from `t_3769_c48` to `STOP`. -/
theorem rx_rli_tail1b {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G U : Nat} {Q : Outcome → Prop} {T D1 f0 f1 f2 Bw : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = 0xb60) (hc : WordAt img 0x900 (Nat.toB256 1))
    (hT : WordAt img 0x140 T) (hD1 : WordAt img 0x480 D1) (hf0 : WordAt img 0x5a0 f0)
    (hf1 : WordAt img 0x5c0 f1) (hf2 : WordAt img 0x5e0 f2) (hBw : WordAt img 0x780 Bw)
    (hTX : ¬ T < Bw)
    (hp1 : rliAmt sevm 1 ≠ 0 → CoinPushOkAt sevm W W (σ.get (coinsBase + Nat.toB256 1))
      (rliAmt sevm 1) U 0xaa0 0xb40) (hp2 : rliAmt sevm 2 ≠ 0 → CoinPushOkAt sevm W W (σ.get (coinsBase + Nat.toB256 2))
      (rliAmt sevm 2) U 0xaa0 0xb40)
    (hG : 54000 + 2 * U ≤ G) (hGb : G + 3000 < 2 ^ 256) (hroom : S.length + 40 < 1024)
    (k : ∀ D : Devm, ExLive sevm W D (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) →
      (∃ L ts data, D.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
        Bytes.toB256 (data.sliceD 0x60 32 0) = f0 ∧ Bytes.toB256 (data.sliceD 0x80 32 0) = f1 ∧
        Bytes.toB256 (data.sliceD 0xa0 32 0) = f2 ∧ Bytes.toB256 (data.sliceD 0xc0 32 0) = D1 ∧
        Bytes.toB256 (data.sliceD 0xe0 32 0) = T - Bw) → Q (.halted D)) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: S) M G) t_3769_c48 Q := by
  refine rx_rli_push1b (R := 42000 + U) hfork hdepth hL hR hW hsz hc hp1 (by omega) hGb hroom ?_ ?_
  · intro b' M' img' g hL' hR' hW' hsz' hk' hc' hg1 hg2
    exact rx_rli_tail2b hfork hstatic hdepth hL' hR' hW' hsz' hc' (hk' _ _ hT (by omega)) (hk' _ _ hD1 (by omega)) (hk' _ _ hf0 (by omega)) (hk' _ _ hf1 (by omega)) (hk' _ _ hf2 (by omega)) (hk' _ _ hBw (by omega)) hTX hp2 (by omega) (by omega) hroom k
  · intro b' M' img' g hL' hR' hW' hsz' hk' hc' hg1 hg2
    exact rx_rli_tail2b hfork hstatic hdepth hL' hR' hW' hsz' hc' (hk' _ _ hT (by omega)) (hk' _ _ hD1 (by omega)) (hk' _ _ hf0 (by omega)) (hk' _ _ hf1 (by omega)) (hk' _ _ hf2 (by omega)) (hk' _ _ hBw (by omega)) hTX hp2 (by omega) (by omega) hroom k

/-- **The transfer loop, the event and `STOP`, forward.** -/
theorem rx_rli_tail0 {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G U : Nat} {Q : Outcome → Prop} {T D1 f0 f1 f2 Bw : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hsz : M.size = 0x920) (hc : WordAt img 0x900 (Nat.toB256 0))
    (hT : WordAt img 0x140 T) (hD1 : WordAt img 0x480 D1) (hf0 : WordAt img 0x5a0 f0)
    (hf1 : WordAt img 0x5c0 f1) (hf2 : WordAt img 0x5e0 f2) (hBw : WordAt img 0x780 Bw)
    (hTX : ¬ T < Bw)
    (hp0 : rliAmt sevm 0 ≠ 0 → CoinPushOkAt sevm W W (σ.get (coinsBase + Nat.toB256 0))
      (rliAmt sevm 0) U 0xaa0 0xb40) (hp1 : rliAmt sevm 1 ≠ 0 → CoinPushOkAt sevm W W (σ.get (coinsBase + Nat.toB256 1))
      (rliAmt sevm 1) U 0xaa0 0xb40) (hp2 : rliAmt sevm 2 ≠ 0 → CoinPushOkAt sevm W W (σ.get (coinsBase + Nat.toB256 2))
      (rliAmt sevm 2) U 0xaa0 0xb40)
    (hG : 66000 + 3 * U ≤ G) (hGb : G + 3000 < 2 ^ 256) (hroom : S.length + 40 < 1024)
    (k : ∀ D : Devm, ExLive sevm W D (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) →
      (∃ L ts data, D.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
        Bytes.toB256 (data.sliceD 0x60 32 0) = f0 ∧ Bytes.toB256 (data.sliceD 0x80 32 0) = f1 ∧
        Bytes.toB256 (data.sliceD 0xa0 32 0) = f2 ∧ Bytes.toB256 (data.sliceD 0xc0 32 0) = D1 ∧
        Bytes.toB256 (data.sliceD 0xe0 32 0) = T - Bw) → Q (.halted D)) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: S) M G) t_3769_c1368 Q := by
  refine rx_rli_push0 (R := 54000 + 2 * U) hfork hdepth hL hR hW hsz hc hp0 (by omega) hGb hroom ?_ ?_
  · intro b' M' img' g hL' hR' hW' hsz' hk' hc' hg1 hg2
    exact rx_rli_tail1a hfork hstatic hdepth hL' hR' hW' hsz' hc' (hk' _ _ hT (by omega)) (hk' _ _ hD1 (by omega)) (hk' _ _ hf0 (by omega)) (hk' _ _ hf1 (by omega)) (hk' _ _ hf2 (by omega)) (hk' _ _ hBw (by omega)) hTX hp1 hp2 (by omega) (by omega) hroom k
  · intro b' M' img' g hL' hR' hW' hsz' hk' hc' hg1 hg2
    exact rx_rli_tail1b hfork hstatic hdepth hL' hR' hW' hsz' hc' (hk' _ _ hT (by omega)) (hk' _ _ hD1 (by omega)) (hk' _ _ hf0 (by omega)) (hk' _ _ hf1 (by omega)) (hk' _ _ hf2 (by omega)) (hk' _ _ hBw (by omega)) hTX hp1 hp2 (by omega) (by omega) hroom k

end Blanc.Lift.Curve3Pool
