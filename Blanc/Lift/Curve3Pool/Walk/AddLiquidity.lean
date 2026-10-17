import Blanc.Lift.Curve3Pool.Walk.AddLiquidityTail

/-!
# `add_liquidity`: the frame up to `D1`, on the actual derivation

`xa_al_front` composes the dispatcher (`xa_dispatch_addLiquidity`), the guards, the fee and `_A`
(`xa_al_p1`), `token.totalSupply()` (`xa_al_p2`), `D0` (`xa_al_p3`), the pull loop
(`xa_al_p4`, `xa_al_pullLoop`) and `D1` (`xa_al_d1`): from the frame's entry with the
`add_liquidity` selector the walk reaches `0x13e9` (after `assert D1 > D0`) having consumed the
supply reply and exactly the pull loop's children, with the base's pool storage the entry
storage with the lock set.

The certificate's checkedness is a hypothesis (`hchk`); `AddLiquidityChecks.lean` discharges it.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The pool storage the body runs over: the entry storage with the lock set. -/
abbrev alLocked (σ : Stor) : Stor := σ.set lockSlot 1

/-- The new balances after the pull loop credited `cr0, cr1, cr2`. -/
abbrev alNew (σ : Stor) (cr0 cr1 cr2 : B256) : Nat → B256 :=
  Function.update (Function.update (Function.update (balAt (alLocked σ)) 0
    (balAt (alLocked σ) 0 + cr0)) 1 (balAt (alLocked σ) 1 + cr1)) 2 (balAt (alLocked σ) 2 + cr2)

/-- `_fee = fee * 3 / 8` as the body computes it. -/
abbrev alFee (σ : Stor) : B256 := σ.get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]

theorem al_aBase_facts {sevm : Sevm} {b : Devm} (h : IdReady sevm b) :
    (∀ a, (aBase sevm b).getStor a = b.getStor a) ∧ (aBase sevm b).logs = b.logs ∧
      (aBase sevm b).output = b.output ∧ (∀ a, (aBase sevm b).getCode a = b.getCode a) ∧
      IdReady sevm (aBase sevm b) := by
  unfold aBase
  split
  · exact ⟨fun a => by simp only [afterSload_getStor], by simp only [afterSload_logs],
      by simp only [afterSload_output], fun a => by simp only [afterSload_getCode],
      (((h.afterSload _).afterSload _).afterSload _).afterSload _⟩
  · exact ⟨fun a => by simp only [afterSload_getStor], by simp only [afterSload_logs],
      by simp only [afterSload_output], fun a => by simp only [afterSload_getCode],
      (h.afterSload _).afterSload _⟩

theorem al_alB1_facts (sevm : Sevm) (b : Devm) :
    (alB1 sevm b).logs = b.logs ∧ (alB1 sevm b).output = b.output ∧
      (∀ a, (alB1 sevm b).getCode a = b.getCode a) := by
  refine ⟨?_, ?_, fun a => ?_⟩ <;>
    simp only [alB1, afterSload_logs, afterSstore_logs, afterSload_output, afterSstore_output,
      afterSload_getCode, afterSstore_getCode]

theorem al_alB1_id {sevm : Sevm} {b : Devm} (h : IdReady sevm b) : IdReady sevm (alB1 sevm b) :=
  (((h.afterSload _).afterSstore _ _).afterSload _).afterSload _ |>.afterSload _

/-- **`add_liquidity` up to `D1`** (see the module note). -/
theorem xa_al_front {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {s : State}
    (hchk : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selAddLiquidity)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((b.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ i, i < 3 → ¬ sevm.benvStat.rules.isPrecomp
      (coinAt (b.getStor sevm.currentTarget) i).toAdr)
    (hpc : b.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm b)
    (hkeep : ∀ c ∈ L, ∀ x, (c.post.getStor sevm.currentTarget).get x =
      (c.pre.getStor sevm.currentTarget).get x)
    (hidk : ∀ c ∈ L, c.post.getCode 4 = c.pre.getCode 4)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    (b.getStor sevm.currentTarget).get lockSlot = 0 ∧ sevm.value = 0 ∧
    (b.getStor sevm.currentTarget).get isKilledSlot = 0 ∧
    (B256.eqCheck ((b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] /
      (b.getStor sevm.currentTarget).get feeSlot) (Bytes.toB256 [3]) |||
      B256.eqCheck ((b.getStor sevm.currentTarget).get feeSlot) 0) ≠ 0 ∧
    ∃ (A : B256) (cT : Exec.Frame) (L0 L1 L2 L' : List Exec.Frame) (D0 D1 cr0 cr1 cr2 : B256)
      (b' : Devm) (M : Mem) (img : Bytes) (G' : Nat),
      aChk s sevm.benvStat.time.toNat = some A.toNat ∧
      L = cT :: ((L0 ++ L1 ++ L2) ++ L') ∧
      cT.sevm.currentTarget = ((b.getStor sevm.currentTarget).get tokenSlot).toAdr ∧
      cT.sevm.data = totalSupplyData ∧ cT.sevm.isStatic = true ∧ 32 ≤ cT.post.output.length ∧
      cT.post.logs = [] ∧
      (alWord cT = 0 → D0 = 0) ∧
      (alWord cT ≠ 0 → getDMem ⟨(balAt (alLocked (b.getStor sevm.currentTarget)) 0).toNat,
        (balAt (alLocked (b.getStor sevm.currentTarget)) 1).toNat,
        (balAt (alLocked (b.getStor sevm.currentTarget)) 2).toNat⟩ A.toNat = some D0.toNat) ∧
      AlPullKids sevm (coinAt (alLocked (b.getStor sevm.currentTarget)) 0) 0 (alAmt sevm 0) L0 cr0 ∧
      AlPullKids sevm (coinAt (alLocked (b.getStor sevm.currentTarget)) 1) 1 (alAmt sevm 1) L1 cr1 ∧
      AlPullKids sevm (coinAt (alLocked (b.getStor sevm.currentTarget)) 2) 2 (alAmt sevm 2) L2 cr2 ∧
      (alWord cT = 0 → ∀ i, i < 3 → 0 < (alAmt sevm i).toNat) ∧
      ¬ balAt (alLocked (b.getStor sevm.currentTarget)) 0 + cr0 <
        balAt (alLocked (b.getStor sevm.currentTarget)) 0 ∧
      ¬ balAt (alLocked (b.getStor sevm.currentTarget)) 1 + cr1 <
        balAt (alLocked (b.getStor sevm.currentTarget)) 1 ∧
      ¬ balAt (alLocked (b.getStor sevm.currentTarget)) 2 + cr2 <
        balAt (alLocked (b.getStor sevm.currentTarget)) 2 ∧
      getDMem ⟨(alNew (b.getStor sevm.currentTarget) cr0 cr1 cr2 0).toNat,
        (alNew (b.getStor sevm.currentTarget) cr0 cr1 cr2 1).toNat,
        (alNew (b.getStor sevm.currentTarget) cr0 cr1 cr2 2).toNat⟩ A.toNat = some D1.toNat ∧
      D0 < D1 ∧
      (∀ x, (b'.getStor sevm.currentTarget).get x =
        (alLocked (b.getStor sevm.currentTarget)).get x) ∧
      b'.logs = b.logs ++ (L0 ++ L1 ++ L2).flatMap (fun c => c.post.logs) ∧
      b'.output = b.output ∧ b'.getCode sevm.currentTarget = b.getCode sevm.currentTarget ∧
      IdReady sevm b' ∧ Mem.Reads M img ∧ Mem.Wf M ∧ M.size % 32 = 0 ∧
      AlPullImg img 3 (alFee (b.getStor sevm.currentTarget))
        ((b.getStor sevm.currentTarget).get adminFeeSlot) A (alWord cT) D0
        (balAt (alLocked (b.getStor sevm.currentTarget)))
        (alNew (b.getStor sevm.currentTarget) cr0 cr1 cr2) ∧
      WordAt img 0x900 D1 ∧
      XAt sevm post 0x13e9 (St b' [] M G') L' := by
  obtain ⟨G0, h⟩ := xa_dispatch_addLiquidity hcode hlen hcd hsel h
  obtain ⟨hlock, hval, hkill, hfee, A, M1, img1, G1, hamp, hR1, hW1, hA1, w140, w160, w180, w1a0,
    w1c0, w1e0, h⟩ := xa_al_p1 hchk hcode hfork hcd ha
      (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyMem_wf Mem.wf_empty _)
      (by rw [vyMem_empty_size]) h
  refine ⟨hlock, hval, hkill, hfee, ?_⟩
  obtain ⟨hAs, hAl, hAo, hAc, hAid⟩ := al_aBase_facts (al_alB1_id hid) (sevm := sevm)
  obtain ⟨hBl, hBo, hBc⟩ := al_alB1_facts sevm b
  have hst1 : ∀ x, ((aBase sevm (alB1 sevm b)).getStor sevm.currentTarget).get x =
      (alLocked (b.getStor sevm.currentTarget)).get x := by
    intro x; rw [hAs, alB1_getStor]
  have htok1 : ¬ sevm.benvStat.rules.isPrecomp
      ((alLocked (b.getStor sevm.currentTarget)).get tokenSlot).toAdr := by
    rw [Stor.get_set_ne _ lock_ne_token]; exact htok
  obtain ⟨cT, L1, b1, M2, G2, img2, rfl, hdepth, hTt, hTd, hTs, hTl, hTlogs, hTcpre, hTcpost,
    hst2, hstA, hl2, ho2, hacc2, hc42, hcK2, hR2, hW2, hA2, P2, w240, w2e0, wold, h⟩ :=
    xa_al_p2 hcode hfork hR1 hW1 hA1 hst1 htok1 hidk h
  have hkeep1 : ∀ c ∈ L1, ∀ x, (c.post.getStor sevm.currentTarget).get x =
      (c.pre.getStor sevm.currentTarget).get x :=
    fun c hc => hkeep c (List.mem_cons_of_mem _ hc)
  have hidk1 : ∀ c ∈ L1, c.post.getCode 4 = c.pre.getCode 4 :=
    fun c hc => hidk c (List.mem_cons_of_mem _ hc)
  clear hkeep hidk
  have hm0 : AlMem0 img2 (alFee (b.getStor sevm.currentTarget))
      ((b.getStor sevm.currentTarget).get adminFeeSlot) A (alWord cT) 0
      (balAt (alLocked (b.getStor sevm.currentTarget))) :=
    ⟨P2 _ _ w140 (by omega) (by omega) (by omega) (by omega),
      P2 _ _ w160 (by omega) (by omega) (by omega) (by omega),
      P2 _ _ w180 (by omega) (by omega) (by omega) (by omega),
      P2 _ _ w1a0 (by omega) (by omega) (by omega) (by omega),
      P2 _ _ w1c0 (by omega) (by omega) (by omega) (by omega),
      P2 _ _ w1e0 (by omega) (by omega) (by omega) (by omega),
      w240, w2e0, wold 0 (by decide), wold 1 (by decide), wold 2 (by decide)⟩
  obtain ⟨D0, M3, img3, G3, hR3, hW3, hA3, hm3, hD00, hD0, h⟩ :=
    xa_al_p3 hchk hcode hfork hR2 hW2 hA2 hm0 h
  obtain ⟨M4, img4, G4, hR4, hW4, hA4, hm4, h⟩ := xa_al_p4 hcode hR3 hW3 hA3 hm3 h
  have hpcB : (aBase sevm (alB1 sevm b)).getCode sevm.currentTarget ≠ .empty := by
    rw [hAc, hBc]; exact hpc
  have hpc2 : b1.getCode sevm.currentTarget ≠ .empty := by rw [hcK2 _ hpcB]; exact hpcB
  have hid2 : IdReady sevm b1 :=
    ⟨by rw [hc42]; exact hAid.nodeleg, hacc2 _ hAid.warm, hid.pre, hid.fork⟩
  have hcoin1 : ∀ i, i < 3 → ¬ sevm.benvStat.rules.isPrecomp
      (coinAt (alLocked (b.getStor sevm.currentTarget)) i).toAdr := fun i hi => by
    rw [coinAt, Stor.get_set_ne _ (coin_ne_lock hi)]; exact hcoin i hi
  obtain ⟨L0, Lp1, Lp2, L', b', M5, img5, G5, cr0, cr1, cr2, rfl, hk0, hk1, hk2, hT0, hc0, hc1,
    hc2, hst5, hl5, ho5, hcd5, hid5, hR5, hW5, hA5, hm5, h⟩ :=
    xa_al_pullLoop hcode hfork hR4 hW4 hA4 hm4 hst2 hpc2 hid2 hdepth hcoin1 hkeep1 hidk1 h
  obtain ⟨D1, M6, img6, G6, hD1, hlt, hR6, hW6, hA6, hm6, w900, h⟩ :=
    xa_al_d1 hchk hcode hfork hR5 hW5 hA5 hm5 h
  refine ⟨A, cT, L0, Lp1, Lp2, L', D0, D1, cr0, cr1, cr2, b', M6, img6, G6, hamp, rfl, by rw [hTt, Stor.get_set_ne _ lock_ne_token], hTd,
    hTs, hTl, hTlogs, hD00, hD0, hk0, hk1, hk2, hT0, hc0, hc1, hc2, hD1, hlt, hst5, ?_, ?_, ?_,
    hid5, hR6, hW6, hA6, hm6, w900, h⟩
  · rw [hl5, hl2, hAl, hBl]
  · rw [ho5, ho2, hAo, hBo]
  · rw [hcd5, hcK2 _ hpcB, hAc, hBc]

end Blanc.Lift.Curve3Pool
