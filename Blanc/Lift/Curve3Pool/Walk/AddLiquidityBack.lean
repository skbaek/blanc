import Blanc.Lift.Curve3Pool.Walk.AddLiquidity

/-!
# `add_liquidity`: from `D1` to the end, on the actual derivation

`xa_al_mintTail` composes the mint amount, the slippage check, the `mint` call and the final
tail (`0x170b` → end). `xa_al_back` composes the fee branch (`xa_al_feePre`), then either the
first-deposit store (`xa_al_initialStore`, supply `0`) or the fee loop and `D2`
(`xa_al_feeLoop`, `xa_al_d2`), then `xa_al_mintTail`: from `0x13e9` the frame ends with exactly
the `mint` child, the three stored balances and the lock cleared, the `AddLiquidity` log, and the
entry output.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **`add_liquidity` from the mint amount to the end** (`0x170b` → end). -/
theorem xa_al_mintTail {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {f0 f1 f2 T D0 D1 D2 : B256} {τ : Stor}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hf0 : WordAt img 0x140 f0) (hf1 : WordAt img 0x160 f1) (hf2 : WordAt img 0x180 f2)
    (ht : WordAt img 0x240 T) (hd0 : WordAt img 0x2e0 D0) (hd1 : WordAt img 0x900 D1)
    (hd2 : WordAt img 0xa20 D2)
    (hst : ∀ x, (b.getStor sevm.currentTarget).get x = τ.get x)
    (htok : ¬ sevm.benvStat.rules.isPrecomp (τ.get tokenSlot).toAdr)
    (hpc : b.getCode sevm.currentTarget ≠ .empty)
    (hkeep : ∀ c ∈ L, ∀ x, (c.post.getStor sevm.currentTarget).get x =
      (c.pre.getStor sevm.currentTarget).get x)
    (h : XAt sevm post 0x170b (St b [] M G) L) :
    ∃ (mint : B256) (cm : Exec.Frame), L = [cm] ∧
      ((T = 0 ∧ mint = D1) ∨ (T ≠ 0 ∧ ¬ D2 < D0 ∧
        (T * (D2 - D0) / T = D2 - D0 ∨ T = 0) ∧ D0 ≠ 0 ∧ mint = T * (D2 - D0) / D0)) ∧
      ¬ mint < Sevm.dataWord sevm (Bytes.toB256 [0x64]) ∧ ¬ T + mint < T ∧
      cm.sevm.currentTarget = (τ.get tokenSlot).toAdr ∧
      cm.sevm.data = mintSel ++ sevm.caller.toB256.toBytes ++ mint.toBytes ∧
      cm.sevm.value = 0 ∧ cm.sevm.isStatic = sevm.isStatic ∧ 32 ≤ cm.post.output.length ∧
      (∀ x, (post.getStor sevm.currentTarget).get x = (τ.set lockSlot 0).get x) ∧
      post.logs = b.logs ++ cm.post.logs ++ [alLog sevm f0 f1 f2 D1 (T + mint)] ∧
      post.output = b.output := by
  obtain ⟨mint, M1, img1, G1, hmint, hR1, hW1, hA1, P1, w1, h⟩ :=
    xa_al_mintAmount hcode hR hW hA ht hd0 hd1 hd2 h
  obtain ⟨hslip, M2, img2, G2, hR2, hW2, hA2, P2, h⟩ := xa_al_slippage hcode hR1 hW1 hA1 w1 h
  obtain ⟨cm, L', d, img3, G3, rfl, hc, hlen, hdk, hR3, hW3, hA3, P3, h⟩ :=
    xa_al_mintCall hcode hfork hR2 hW2 hA2 (P2 _ _ w1 (by omega)) (hst tokenSlot) htok hpc hkeep h
  have Q : ∀ o w, WordAt img o w → o + 32 ≤ 0xba0 → WordAt img3 o w := fun o w hw ho =>
    P3 o w (P2 o w (P1 o w hw ho) (by omega)) (by omega)
  obtain ⟨hadd, rfl, hsP, hlP, hoP⟩ := xa_al_finish hcode hfork hR3 hW3 hA3
    (Q _ _ hf0 (by omega)) (Q _ _ hf1 (by omega)) (Q _ _ hf2 (by omega)) (Q _ _ ht (by omega))
    (Q _ _ hd1 (by omega)) (P3 _ _ (P2 _ _ w1 (by omega)) (by omega)) h
  refine ⟨mint, cm, rfl, hmint, hslip, hadd, hc.target, hc.data, hc.value, hc.isStatic, hlen,
    fun x => ?_, ?_, ?_⟩
  · rw [hsP, Stor.get_set_ite, Stor.get_set_ite, hdk, hst]
  · rw [hlP, hc.logs]
  · rw [hoP, hc.outputKeep]

/-- The pool storage after the three balance stores and the lock clear. -/
abbrev alStored (σ : Stor) (s0 s1 s2 : B256) : Stor :=
  (((σ.set (balancesBase + Nat.toB256 0) s0).set (balancesBase + Nat.toB256 1) s1).set
    (balancesBase + Nat.toB256 2) s2).set lockSlot 0

/-- **`add_liquidity` from `D1` to the end** (see the module note): the first deposit stores the
new balances with zero fees and `D2 = D1`; otherwise every fee iteration's checks pass, the
stored balances are the fee loop's, and `D2` is `get_D_mem` at the fee-adjusted balances. -/
theorem xa_al_back {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {F AF A T D0 D1 : B256} {old nv : Nat → B256} {σ : Stor}
    (hchk : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hm : AlPullImg img 3 F AF A T D0 old nv) (hd1 : WordAt img 0x900 D1)
    (hst : ∀ x, (b.getStor sevm.currentTarget).get x = σ.get x)
    (htok : ¬ sevm.benvStat.rules.isPrecomp (σ.get tokenSlot).toAdr)
    (htokB : ∀ k : Nat, k < 3 → balancesBase + Nat.toB256 k ≠ tokenSlot)
    (hpc : b.getCode sevm.currentTarget ≠ .empty)
    (hkeep : ∀ c ∈ L, ∀ x, (c.post.getStor sevm.currentTarget).get x =
      (c.pre.getStor sevm.currentTarget).get x)
    (h : XAt sevm post 0x13e9 (St b [] M G) L) :
    ∃ (f0 f1 f2 s0 s1 s2 D2 mint : B256) (cm : Exec.Frame), L = [cm] ∧
      ((T = 0 ∧ f0 = 0 ∧ f1 = 0 ∧ f2 = 0 ∧ s0 = nv 0 ∧ s1 = nv 1 ∧ s2 = nv 2 ∧ D2 = D1) ∨
        (T ≠ 0 ∧ ∃ a0 a1 a2 : B256, AlFeeFacts F AF D0 D1 (old 0) (nv 0) f0 s0 a0 ∧
          AlFeeFacts F AF D0 D1 (old 1) (nv 1) f1 s1 a1 ∧
          AlFeeFacts F AF D0 D1 (old 2) (nv 2) f2 s2 a2 ∧
          getDMem ⟨a0.toNat, a1.toNat, a2.toNat⟩ A.toNat = some D2.toNat)) ∧
      ((T = 0 ∧ mint = D1) ∨ (T ≠ 0 ∧ ¬ D2 < D0 ∧
        (T * (D2 - D0) / T = D2 - D0 ∨ T = 0) ∧ D0 ≠ 0 ∧ mint = T * (D2 - D0) / D0)) ∧
      ¬ mint < Sevm.dataWord sevm (Bytes.toB256 [0x64]) ∧ ¬ T + mint < T ∧
      cm.sevm.currentTarget = (σ.get tokenSlot).toAdr ∧
      cm.sevm.data = mintSel ++ sevm.caller.toB256.toBytes ++ mint.toBytes ∧
      cm.sevm.value = 0 ∧ cm.sevm.isStatic = sevm.isStatic ∧ 32 ≤ cm.post.output.length ∧
      (∀ x, (post.getStor sevm.currentTarget).get x = (alStored σ s0 s1 s2).get x) ∧
      post.logs = b.logs ++ cm.post.logs ++ [alLog sevm f0 f1 f2 D1 (T + mint)] ∧
      post.output = b.output := by
  obtain ⟨M1, img1, G1, hR1, hW1, hA1, P1, wa20, hbr⟩ :=
    xa_al_feePre hcode hR hW hA hm.m0.supply hd1 h
  -- the token word survives the balance stores
  have htokS : ∀ s0 s1 s2 : B256, (((σ.set (balancesBase + Nat.toB256 0) s0).set
      (balancesBase + Nat.toB256 1) s1).set (balancesBase + Nat.toB256 2) s2).get tokenSlot =
      σ.get tokenSlot := fun s0 s1 s2 => by
    rw [Stor.get_set_ne _ (htokB 2 (by decide)), Stor.get_set_ne _ (htokB 1 (by decide)),
      Stor.get_set_ne _ (htokB 0 (by decide))]
  rcases hbr with ⟨hT, h⟩ | ⟨hT, hctr, h⟩
  · -- first deposit
    obtain ⟨M2, G2, hR2, hW2, hA2, h⟩ := xa_al_initialStore hcode hfork hR1 hW1 hA1
      (P1 _ _ hm.n0 (by omega)) (P1 _ _ hm.n1 (by omega)) (P1 _ _ hm.n2 (by omega)) h
    have Q : ∀ o w, WordAt img o w → o + 32 ≤ 0xa20 → 0xe0 ≤ o →
        WordAt (Bytes.writeAt img1 0xc0 (Bytes.toB256 [1]).toBytes) o w := fun o w hw ho ho' =>
      (P1 o w hw ho).write_other (by simp only [B256.length_toBytes]; omega)
    have hb1 : balancesBase + Bytes.toB256 [1] = balancesBase + Nat.toB256 1 := by decide
    have hb2 : balancesBase + Bytes.toB256 [2] = balancesBase + Nat.toB256 2 := by decide
    have hb0 : afterSstore sevm b balancesBase (nv 0) =
        afterSstore sevm b (balancesBase + Nat.toB256 0) (nv 0) := by rw [← al_bal0]
    rw [hb1, hb2, hb0] at h
    obtain ⟨mint, cm, rfl, hmint, hslip, hadd, hct, hcd, hcv, hcs, hcl, hsP, hlP, hoP⟩ :=
      xa_al_mintTail (τ := ((σ.set (balancesBase + Nat.toB256 0) (nv 0)).set
        (balancesBase + Nat.toB256 1) (nv 1)).set (balancesBase + Nat.toB256 2) (nv 2))
        hcode hfork hR2 hW2 hA2
        (Q _ _ hm.m0.f0 (by omega) (by omega)) (Q _ _ hm.m0.f1 (by omega) (by omega))
        (Q _ _ hm.m0.f2 (by omega) (by omega)) (Q _ _ hm.m0.supply (by omega) (by omega))
        (Q _ _ hm.m0.d0 (by omega) (by omega)) (Q _ _ hd1 (by omega) (by omega))
        (wa20.write_other (by simp only [B256.length_toBytes]; omega))
        (fun x => by simp only [afterSstore_getStor_self, Stor.get_set_ite, hst])
        (by rw [htokS]; exact htok)
        (by simp only [afterSstore_getCode]; exact hpc) hkeep h
    refine ⟨0, 0, 0, nv 0, nv 1, nv 2, D1, mint, cm, rfl,
      .inl ⟨hT, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hmint, hslip, hadd,
      by rw [hct, htokS], hcd, hcv, hcs, hcl, hsP, ?_, ?_⟩
    · rw [hlP]; simp only [afterSstore_logs]
    · rw [hoP]; simp only [afterSstore_output]
  · -- the fee loop and `D2`
    obtain ⟨f0, s0, a0, f1, s1, a1, f2, s2, a2, M2, img2, G2, hF0, hF1, hF2, hR2, hW2, hA2, hm2,
      h⟩ := xa_al_feeLoop hcode hfork hR1 hW1 hA1 (al_feeImg_of_pull hm hd1 hctr P1) h
    obtain ⟨D2, M3, img3, G3, hD2, hR3, hW3, hA3, K3, w3, h⟩ :=
      xa_al_d2 hchk hcode hfork hR2 hW2 hA2 hm2 h
    obtain ⟨mint, cm, rfl, hmint, hslip, hadd, hct, hcd, hcv, hcs, hcl, hsP, hlP, hoP⟩ :=
      xa_al_mintTail (τ := ((σ.set (balancesBase + Nat.toB256 0) s0).set
        (balancesBase + Nat.toB256 1) s1).set (balancesBase + Nat.toB256 2) s2)
        hcode hfork hR3 hW3 hA3
        (K3 0 _ (by decide) (hm2.fs 0 (by decide))) (K3 1 _ (by decide) (hm2.fs 1 (by decide)))
        (K3 2 _ (by decide) (hm2.fs 2 (by decide))) (K3 8 _ (by decide) hm2.supply)
        (K3 13 _ (by decide) hm2.d0) (K3 62 _ (by decide) hm2.d1) w3
        (fun x => by simp only [afterSstore_getStor_self, Stor.get_set_ite, hst])
        (by rw [htokS]; exact htok)
        (by simp only [afterSstore_getCode]; exact hpc) hkeep h
    refine ⟨f0, f1, f2, s0, s1, s2, D2, mint, cm, rfl,
      .inr ⟨hT, a0, a1, a2, hF0, hF1, hF2, hD2⟩, hmint, hslip, hadd,
      by rw [hct, htokS], hcd, hcv, hcs, hcl, hsP, ?_, ?_⟩
    · rw [hlP]; simp only [afterSstore_logs]; rfl
    · rw [hoP]; simp only [afterSstore_output]

end Blanc.Lift.Curve3Pool
