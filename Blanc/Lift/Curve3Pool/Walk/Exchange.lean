import Blanc.Lift.Curve3Pool.Walk.ExchangeFront
import Blanc.Lift.Curve3Pool.Walk.ExchangeY
import Blanc.Lift.Curve3Pool.Walk.ExchangeDy
import Blanc.Lift.Curve3Pool.Walk.ExchangePush
import Blanc.Lift.Curve3Pool.Refine

/-!
# `exchange`: the whole frame on the actual derivation

`xa_exchange` composes `xa_ex_front` (dispatcher to `x`), the frame save, `get_y` (crossed with
`xa_ex_getY` over the entry state the storage abstracts), the frame restore, the `dy`/fee/admin
arithmetic and the two balance stores, the `transfer` push with its `raw_call` test, and the
event with the lock clear: from the frame's entry with the `exchange` selector, a successful
frame has exactly the pull's children (`ExPull`) and the push, the machine-word checks the model
makes, and the pool's storage, logs and output as the model's step leaves them.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

theorem aBase_getStor (sevm : Sevm) (b : Devm) (a : Adr) : (aBase sevm b).getStor a = b.getStor a := by
  unfold aBase; split <;> simp only [afterSload_getStor]

theorem aBase_logs (sevm : Sevm) (b : Devm) : (aBase sevm b).logs = b.logs := by
  unfold aBase; split <;> simp only [afterSload_logs]

theorem aBase_output (sevm : Sevm) (b : Devm) : (aBase sevm b).output = b.output := by
  unfold aBase; split <;> simp only [afterSload_output]

theorem aBase_getCode (sevm : Sevm) (b : Devm) (a : Adr) : (aBase sevm b).getCode a = b.getCode a := by
  unfold aBase; split <;> simp only [afterSload_getCode]

theorem IdReady_aBase {sevm : Sevm} {b : Devm} (h : IdReady sevm b) : IdReady sevm (aBase sevm b) := by
  unfold aBase; split
  · exact (((h.afterSload _).afterSload _).afterSload _).afterSload _
  · exact (h.afterSload _).afterSload _

theorem ExBase.aBase {sevm : Sevm} {b0 b : Devm} {σ : Stor} (h : ExBase sevm b0 b σ) :
    ExBase sevm b0 (aBase sevm b) σ :=
  ⟨fun x => by rw [aBase_getStor]; exact h.stor x, by rw [aBase_getCode]; exact h.code,
    by rw [aBase_output]; exact h.output, IdReady_aBase h.id⟩

/-- The storage abstracts `s` after the lock moved. -/
theorem Abstracts.of_lock {σ σ' : Stor} {s : State} (h : Abstracts σ s)
    (he : ∀ x, x ≠ lockSlot → σ'.get x = σ.get x) : Abstracts σ' s :=
  Abstracts.of_reads fun f =>
    Fld.Reads.congr (he _ (Fld.slot_ne_lock f)) (by cases f <;> rfl) (h.reads f)

/-- **The `exchange` frame.** From the frame's entry with the `exchange` selector over the
entry storage `σ` (abstracting `s`), a successful frame found the lock clear, no value and the
pool alive; `i, j < 3`; `_xp_mem(old_balances)` returned `xp`; its children are the pull's
(`ExPull`: the `transferFrom`, and for `i == 2` the `balanceOf` pair around it, crediting `D`)
and then the `transfer` of `dy` to `coins[j]`; `get_y` returned `y` (`getYChk` at `_A`'s
`amp`); every machine-word check of lines 462–478 passed; the pool's storage is `σ` with
`balances[i]` and `balances[j]` stored; the frame logged its children's logs and then
`TokenExchange`; the output is the entry output. -/
theorem xa_exchange {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {σ : Stor}
    {s : State} (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange)
    (hσ : b.getStor sevm.currentTarget = σ) (ha : Abstracts σ s)
    (hcoinI : (exI sevm).toNat < 3 → ¬ sevm.benvStat.rules.isPrecomp (σ.get (coinsBase + exI sevm)).toAdr)
    (hcoinJ : (exJ sevm).toNat < 3 → ¬ sevm.benvStat.rules.isPrecomp (σ.get (coinsBase + exJ sevm)).toAdr)
    (hpc : b.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm b)
    (hkeep : ∀ c ∈ L, ∀ x, (c.post.getStor sevm.currentTarget).get x =
      (c.pre.getStor sevm.currentTarget).get x)
    (hidk : ∀ c ∈ L, c.post.getCode 4 = c.pre.getCode 4)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    σ.get lockSlot = 0 ∧ sevm.value = 0 ∧ σ.get isKilledSlot = 0 ∧ (exI sevm).toNat < 3 ∧
    (exJ sevm).toNat < 3 ∧
    ∃ x0 x1 x2 : B256,
      xpChk ⟨(balAt σ 0).toNat, (balAt σ 1).toNat, (balAt σ 2).toNat⟩ =
        some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
    ∃ (Lp : List Exec.Frame) (cp cq : Exec.Frame) (D y : B256) (amp : Nat),
      L = Lp ++ [cq] ∧ cp ∈ Lp ∧
      cp.sevm.currentTarget = (σ.get (coinsBase + exI sevm)).toAdr ∧
      cp.sevm.data = exPullData sevm ∧ cp.sevm.value = 0 ∧ cp.sevm.isStatic = sevm.isStatic ∧
      RawCallOk cp.post.output ∧ ExPull sevm (σ.get (coinsBase + exI sevm)) D Lp cp ∧
      (D * exRate (exI sevm).toNat / D = exRate (exI sevm).toNat ∨ D = 0) ∧
      ¬ exW3 x0 x1 x2 (exI sevm).toNat + D * exRate (exI sevm).toNat / exR0 <
        exW3 x0 x1 x2 (exI sevm).toNat ∧
      aChk s sevm.benvStat.time.toNat = some amp ∧
      (∃ (hi : (exI sevm).toNat < 3) (hj : (exJ sevm).toNat < 3),
        getYChk amp ⟨(exI sevm).toNat, hi⟩ ⟨(exJ sevm).toNat, hj⟩
          (exW3 x0 x1 x2 (exI sevm).toNat + D * exRate (exI sevm).toNat / exR0).toNat
          (V3.mk x0.toNat x1.toNat x2.toNat).get = some y.toNat) ∧
      ¬ exW3 x0 x1 x2 (exJ sevm).toNat < y ∧
      ¬ exW3 x0 x1 x2 (exJ sevm).toNat - y < Bytes.toB256 [1] ∧
      (exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) y * σ.get feeSlot /
          exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) y = σ.get feeSlot ∨
        exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) y = 0) ∧
      ¬ exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) y <
        exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) y (σ.get feeSlot) ∧
      ((exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) y -
          exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) y (σ.get feeSlot)) * exR0 /
          (exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) y -
            exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) y (σ.get feeSlot)) = exR0 ∨
        exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) y -
          exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) y (σ.get feeSlot) = 0) ∧
      ¬ exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) y (σ.get feeSlot) (exRate (exJ sevm).toNat) <
        exMinDy sevm ∧
      (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) y (σ.get feeSlot) * σ.get adminFeeSlot /
          exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) y (σ.get feeSlot) = σ.get adminFeeSlot ∨
        exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) y (σ.get feeSlot) = 0) ∧
      (exAdm0 (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) y (σ.get feeSlot)) (σ.get adminFeeSlot) *
          exR0 / exAdm0 (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) y (σ.get feeSlot))
            (σ.get adminFeeSlot) = exR0 ∨
        exAdm0 (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) y (σ.get feeSlot))
          (σ.get adminFeeSlot) = 0) ∧
      ¬ exW3 (balAt σ 0) (balAt σ 1) (balAt σ 2) (exI sevm).toNat + D <
        exW3 (balAt σ 0) (balAt σ 1) (balAt σ 2) (exI sevm).toNat ∧
      ¬ exW3 (balAt σ 0) (balAt σ 1) (balAt σ 2) (exJ sevm).toNat <
        exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) y (σ.get feeSlot) (exRate (exJ sevm).toNat) ∧
      ¬ exW3 (balAt σ 0) (balAt σ 1) (balAt σ 2) (exJ sevm).toNat -
          exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) y (σ.get feeSlot) (exRate (exJ sevm).toNat) <
        exAdm (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) y (σ.get feeSlot)) (σ.get adminFeeSlot)
          (exRate (exJ sevm).toNat) ∧
      cq.sevm.currentTarget = (σ.get (coinsBase + exJ sevm)).toAdr ∧
      cq.sevm.data = exPushData sevm
        (exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) y (σ.get feeSlot) (exRate (exJ sevm).toNat)) ∧
      cq.sevm.value = 0 ∧ cq.sevm.isStatic = sevm.isStatic ∧ RawCallOk cq.post.output ∧
      (∀ x, (post.getStor sevm.currentTarget).get x =
        ((σ.set (balancesBase + exI sevm)
          (exW3 (balAt σ 0) (balAt σ 1) (balAt σ 2) (exI sevm).toNat + D)).set
          (balancesBase + exJ sevm)
          (exW3 (balAt σ 0) (balAt σ 1) (balAt σ 2) (exJ sevm).toNat -
            exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) y (σ.get feeSlot) (exRate (exJ sevm).toNat) -
            exAdm (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) y (σ.get feeSlot))
              (σ.get adminFeeSlot) (exRate (exJ sevm).toNat))).get x) ∧
      post.logs = b.logs ++ (Lp ++ [cq]).flatMap (fun c => c.post.logs) ++
        [⟨sevm.currentTarget, [exTopic, sevm.caller.toB256],
          (exI sevm).toBytes ++ (exDx sevm).toBytes ++ (exJ sevm).toBytes ++
          (exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) y (σ.get feeSlot)
            (exRate (exJ sevm).toNat)).toBytes⟩] ∧
      post.output = b.output := by
  subst hσ
  obtain ⟨hlock, hval, hkill, hi3, x0, x1, x2, hxp, Lp, L1, cp, D, d, M, img, G1, hdepth, rfl,
    hcpm, hct, hcdata, hcv, hcs, hcok, hpull, hB, hlogs, hR, hW, hF, h⟩ :=
    xa_ex_front hcode hfork hlen hcd hsel hcoinI hpc hid hkeep hidk h
  refine ⟨hlock, hval, hkill, hi3, ?_⟩
  have hk1 : ∀ c ∈ L1, ∀ x, (c.post.getStor sevm.currentTarget).get x =
      (c.pre.getStor sevm.currentTarget).get x :=
    fun c hc => hkeep c (List.mem_append_right _ hc)
  have hi1 : ∀ c ∈ L1, c.post.getCode 4 = c.pre.getCode 4 :=
    fun c hc => hidk c (List.mem_append_right _ hc)
  clear hkeep hidk
  -- `x`
  obtain ⟨hmx, hax, M1, img1, G1, hR1, hW1, hF1, hx1, hctr1, h⟩ := xa_ex_x hcode hi3 hR hW hF h
  clear hR hW hF
  -- the frame save
  obtain ⟨M2, img2, G2, hR2, hW2, hk2, h⟩ := xa_ex_save hcode
    (fun o => Bytes.toB256 (img1.sliceD o 32 0)) 52 hR1 hW1 (p := 0x140) (by decide) hctr1
    (fun m _ => WordAt.self img1 _) h
  -- `get_y`'s arguments and the call
  obtain ⟨M3, img3, G3, hR3, hW3, hA3, hk3, h⟩ := xa_ex_args hcode hR2 hW2
    (hk2 _ _ hx1 (by omega)) (hk2 _ _ (hF1.xp 0 (by decide)) (by omega))
    (hk2 _ _ (hF1.xp 1 (by decide)) (by omega)) (hk2 _ _ (hF1.xp 2 (by decide)) (by omega)) h
  have ha1 : Abstracts (d.getStor sevm.currentTarget) s :=
    ha.of_lock fun x hx => by rw [hB.stor, Stor.get_set_ne _ (Ne.symm hx)]
  obtain ⟨y, M4, G4, h, amp, hamp, hi, hj, hy, -, hW4, -⟩ :=
    xa_ex_getY hcode hfork ha1 hW3 hA3 h
  rw [show (Nat.toB256 0x27cd).toNat = 0x27cd from B256.toNat_toB256_of_lt (by decide)] at h
  -- park `y`, restore the frame
  obtain ⟨M5, G5, hR5, hW5, h⟩ := xa_ex_afterY hcode (Mem.reads_data M4) hW4 h
  obtain ⟨M6, img6, G6, hR6, hW6, hm6, hk6, h⟩ := xa_ex_restore hcode
    (fun o => Bytes.toB256 (img1.sliceD o 32 0)) 52 hR5 hW5 (by decide)
    (WordAt.write_self _ _ _) h
  have hF6 := hF1.of_restore hm6
  have hy6 : WordAt img6 0x900 y :=
    hk6 _ _ ((WordAt.write_self _ _ _).write_other (by simp only [B256.length_toBytes]; omega))
      (.inr (.inr (by omega)))
  have hB6 := hB.aBase
  -- `dy`, the fee, the slippage check
  obtain ⟨hy1, hy2, hm1, hf1, hm2, hmin, M7, img7, G7, hR7, hW7, hF7, hout7, hfee7, h⟩ :=
    xa_ex_dy hcode hfork hj hR6 hW6 hF6 hy6 h
  have hfeeS : ((aBase sevm d).getStor sevm.currentTarget).get feeSlot =
      (b.getStor sevm.currentTarget).get feeSlot := by
    rw [hB6.stor, Stor.get_set_ne _ (by decide)]
  rw [hfeeS] at hm1 hf1 hm2 hmin hout7 hfee7
  -- the admin share and the two stores
  obtain ⟨ha1', ha2', hbi, hbj1, hbj2, M8, img8, G8, hR8, hW8, hk8, h⟩ :=
    xa_ex_store hcode hfork hi3 hj hR7 hW7 hF7 hout7 hfee7 h
  have hafS : ((afterSload sevm (aBase sevm d) feeSlot).getStor sevm.currentTarget).get
      adminFeeSlot = (b.getStor sevm.currentTarget).get adminFeeSlot := by
    rw [afterSload_getStor, hB6.stor, Stor.get_set_ne _ (by decide)]
  rw [hafS] at ha1' ha2' hbj2 h
  have hiN : balancesBase + exI sevm = balancesBase + Nat.toB256 (exI sevm).toNat := by
    rw [toB256_toNat]
  have hjN : balancesBase + exJ sevm = balancesBase + Nat.toB256 (exJ sevm).toNat := by
    rw [toB256_toNat]
  have hcJ : coinsBase + exJ sevm = coinsBase + Nat.toB256 (exJ sevm).toNat := by
    rw [toB256_toNat]
  generalize hVI : exW3 (balAt (b.getStor sevm.currentTarget) 0)
    (balAt (b.getStor sevm.currentTarget) 1) (balAt (b.getStor sevm.currentTarget) 2)
    (exI sevm).toNat + D = VI at h
  generalize hVJ : exW3 (balAt (b.getStor sevm.currentTarget) 0)
    (balAt (b.getStor sevm.currentTarget) 1) (balAt (b.getStor sevm.currentTarget) 2)
    (exJ sevm).toNat - exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) y
      ((b.getStor sevm.currentTarget).get feeSlot) (exRate (exJ sevm).toNat) -
    exAdm (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) y ((b.getStor sevm.currentTarget).get feeSlot))
      ((b.getStor sevm.currentTarget).get adminFeeSlot) (exRate (exJ sevm).toNat) = VJ at h
  have hB8 : ExBase sevm b (afterSstore sevm (afterSstore sevm (afterSload sevm
      (afterSload sevm (aBase sevm d) feeSlot) adminFeeSlot) (balancesBase + exI sevm) VI)
      (balancesBase + exJ sevm) VJ) ((((b.getStor sevm.currentTarget).set lockSlot 1).set
      (balancesBase + exI sevm) VI).set (balancesBase + exJ sevm) VJ) :=
    ⟨fun x => by
      simp only [afterSstore_getStor_self, afterSload_getStor, Stor.get_set_ite, aBase_getStor,
        hB.stor],
      by simp only [afterSstore_getCode, afterSload_getCode, aBase_getCode, hB.code],
      by simp only [afterSstore_output, afterSload_output, aBase_output, hB.output],
      (((((IdReady_aBase hB.id).afterSload _).afterSload _).afterSstore _ _).afterSstore _ _)⟩
  have hcw : _ := hB8.stor (coinsBase + exJ sevm)
  rw [Stor.get_set_ne _ (by rw [hjN, hcJ]; exact bal_ne_coin hj hj),
    Stor.get_set_ne _ (by rw [hiN, hcJ]; exact bal_ne_coin hi3 hj),
    Stor.get_set_ne _ (by rw [hcJ]; exact coin_ne_lock hj)] at hcw
  -- the push and its `raw_call` test
  obtain ⟨bq, cq, L2, dq, img9, G9, hbq, rfl, hcq, hv9, hR9, hW9, hrd9, h⟩ :=
    xa_ex_push hcode hfork hj hR8 hW8
      (hk8 _ _ hout7 (by omega) (by omega)) hB8.id hdepth hcw (hcoinJ hj) h
  have hBq := (hB8.rel hbq).child hcq hpc (hk1 cq List.mem_cons_self) (hi1 cq List.mem_cons_self)
  obtain ⟨hok2, b10, M10, img10, G10, hb10, hR10, hW10, hk10, h⟩ :=
    xa_ex_tail2 hcode hBq.id hR9 hW9 hrd9 h
  -- the event and the lock
  obtain ⟨rfl, hsP, hlP, hoP⟩ := xa_ex_log hcode hfork hR10 hW10
    (hk10 _ _ hv9 (by omega) (by omega)) h
  have hdq := hBq.stor
  refine ⟨hj, x0, x1, x2, hxp, Lp, cp, cq, D, y, amp, rfl, hcpm, hct, hcdata, hcv, hcs, hcok, hpull,
    hmx, hax, hamp, ⟨hi, hj, hy⟩, hy1, hy2, hm1, hf1, hm2, hmin, ha1', ha2', hbi, hbj1, hbj2,
    hcq.target, hcq.data, hcq.value, hcq.isStatic, hcq.output ▸ hok2, fun x => ?_, ?_, ?_⟩
  · rw [hsP, Stor.get_set_ite, hb10.stor, hdq, ← hVI, ← hVJ]
    by_cases hx : lockSlot = x
    · subst hx
      rw [ite_eq_left rfl, Stor.get_set_ne _ (by rw [hjN]; exact (bal_ne_lock hj).symm),
        Stor.get_set_ne _ (by rw [hiN]; exact (bal_ne_lock hi3).symm), hlock]
    · rw [ite_eq_right hx, Stor.get_set_ite, Stor.get_set_ite, Stor.get_set_ite, Stor.get_set_ite,
        Stor.get_set_ite, ite_eq_right hx]
  · rw [hlP, hb10.logs, hcq.logs, hbq.logs]
    simp only [afterSstore_logs, afterSload_logs, aBase_logs, hlogs, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  · rw [hoP, hb10.output, hcq.outputKeep, hbq.output, hB8.output]

end Blanc.Lift.Curve3Pool
