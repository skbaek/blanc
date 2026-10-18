import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceTransfers

/-!
# `remove_liquidity_imbalance`: the whole frame on the actual derivation

`xa_rli` composes the dispatcher (`xa_dispatch_removeLiquidityImbalance`), the guards, supply,
`_A` and balances (`xa_rli_front`), `D0` and `new_balances` (`xa_rli_d0`), `D1`
(`xa_rli_d1`), the unrolled fee loop (`xa_rli_feeA{k}`, `xa_rli_feeB{k}`), `D2` and the burn
amount (`xa_rli_d2`), the burn (`xa_rli_burn`), the unrolled transfer loop (`xa_rli_iter`,
`xa_rli_next`) and the event with the lock clear (`xa_rli_log`): from the frame's entry with the
`remove_liquidity_imbalance` selector, a successful frame's children are the static
`totalSupply()`, the burn and one transfer per nonzero amount; every machine-word check of lines
530–579 passed; the pool's storage is the entry storage with the three stored balances; the
frame logged its children's logs and then `RemoveLiquidityImbalance`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- Coin `k`'s transfer children: none for a zero amount, else the one `transfer`. -/
def RliPushK (sevm : Sevm) (σ : Stor) (k : Nat) (Lc : List Exec.Frame) : Prop :=
  (rliAmt sevm k = 0 ∧ Lc = []) ∨
    (rliAmt sevm k ≠ 0 ∧ ∃ c, Lc = [c] ∧
      c.sevm.currentTarget = (σ.get (coinsBase + Nat.toB256 k)).toAdr ∧
      c.sevm.data = exPushData sevm (rliAmt sevm k) ∧ c.sevm.value = 0 ∧
      c.sevm.isStatic = sevm.isStatic ∧ RawCallOk c.post.output)

/-- `coins[k]` read through the lock and the three balance stores. -/
theorem rli_coin_get {σ : Stor} {v a0 a1 a2 : B256} {k : Nat} (hk : k < 3) :
    ((((σ.set lockSlot v).set (balancesBase + Nat.toB256 0) a0).set (balancesBase + Nat.toB256 1)
      a1).set (balancesBase + Nat.toB256 2) a2).get (coinsBase + Nat.toB256 k) =
      σ.get (coinsBase + Nat.toB256 k) := by
  rw [Stor.get_set_ne _ (bal_ne_coin (by decide) hk), Stor.get_set_ne _ (bal_ne_coin (by decide) hk),
    Stor.get_set_ne _ (bal_ne_coin (by decide) hk), Stor.get_set_ne _ (coin_ne_lock hk)]

set_option hygiene false in
/-- The carrier `hV` restricted to the goal's word list. -/
local macro "vsub" : term => `(hV.sub (by
  simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]))

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}

/-- **The `remove_liquidity_imbalance` frame** (see the module note). -/
theorem xa_rli (hc : Cert.CheckedM code cert mems true) {σ : Stor} {s : State}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityImbalance)
    (hσ : b.getStor sevm.currentTarget = σ) (ha : Abstracts σ s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp (σ.get tokenSlot).toAdr)
    (hcoin : ∀ k, k < 3 → ¬ sevm.benvStat.rules.isPrecomp (σ.get (coinsBase + Nat.toB256 k)).toAdr)
    (hpc : b.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm b)
    (hkeep : ∀ c ∈ L, ∀ x, (c.post.getStor sevm.currentTarget).get x =
      (c.pre.getStor sevm.currentTarget).get x)
    (hidk : ∀ c ∈ L, c.post.getCode 4 = c.pre.getCode 4)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    σ.get lockSlot = 0 ∧ sevm.value = 0 ∧ σ.get isKilledSlot = 0 ∧
    ∃ (cs cb : Exec.Frame) (L0 L1 L2 : List Exec.Frame) (A D0 D1 D2 f0 f1 f2 : B256),
      L = cs :: cb :: (L0 ++ L1 ++ L2) ∧
      StaticWordChild (σ.get tokenSlot).toAdr totalSupplyData cs ∧ vSupply cs ≠ 0 ∧
      (σ.get feeSlot).Nofm (Bytes.toB256 [3]) ∧ aChk s sevm.benvStat.time.toNat = some A.toNat ∧
      getDMem ⟨(balAt σ 0).toNat, (balAt σ 1).toNat, (balAt σ 2).toNat⟩ A.toNat = some D0.toNat ∧
      ¬ balAt σ 0 < Sevm.dataWord sevm (Bytes.toB256 [4]) ∧
      ¬ balAt σ 1 < Sevm.dataWord sevm (Bytes.toB256 [0x24]) ∧
      ¬ balAt σ 2 < Sevm.dataWord sevm (Bytes.toB256 [0x44]) ∧
      getDMem ⟨(balAt σ 0 - Sevm.dataWord sevm (Bytes.toB256 [4])).toNat,
        (balAt σ 1 - Sevm.dataWord sevm (Bytes.toB256 [0x24])).toNat,
        (balAt σ 2 - Sevm.dataWord sevm (Bytes.toB256 [0x44])).toNat⟩ A.toNat = some D1.toNat ∧
      RliFeeIter (σ.get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]) (σ.get adminFeeSlot) D0 D1
        (balAt σ 0) (balAt σ 0 - Sevm.dataWord sevm (Bytes.toB256 [4])) f0
        (balAt σ 0 - Sevm.dataWord sevm (Bytes.toB256 [4]) - f0 * σ.get adminFeeSlot / rliDen)
        (balAt σ 0 - Sevm.dataWord sevm (Bytes.toB256 [4]) - f0) ∧
      RliFeeIter (σ.get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]) (σ.get adminFeeSlot) D0 D1
        (balAt σ 1) (balAt σ 1 - Sevm.dataWord sevm (Bytes.toB256 [0x24])) f1
        (balAt σ 1 - Sevm.dataWord sevm (Bytes.toB256 [0x24]) - f1 * σ.get adminFeeSlot / rliDen)
        (balAt σ 1 - Sevm.dataWord sevm (Bytes.toB256 [0x24]) - f1) ∧
      RliFeeIter (σ.get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]) (σ.get adminFeeSlot) D0 D1
        (balAt σ 2) (balAt σ 2 - Sevm.dataWord sevm (Bytes.toB256 [0x44])) f2
        (balAt σ 2 - Sevm.dataWord sevm (Bytes.toB256 [0x44]) - f2 * σ.get adminFeeSlot / rliDen)
        (balAt σ 2 - Sevm.dataWord sevm (Bytes.toB256 [0x44]) - f2) ∧
      getDMem ⟨(balAt σ 0 - Sevm.dataWord sevm (Bytes.toB256 [4]) - f0).toNat,
        (balAt σ 1 - Sevm.dataWord sevm (Bytes.toB256 [0x24]) - f1).toNat,
        (balAt σ 2 - Sevm.dataWord sevm (Bytes.toB256 [0x44]) - f2).toNat⟩ A.toNat =
        some D2.toNat ∧
      ¬ D0 < D2 ∧ (D0 - D2).Nofm (vSupply cs) ∧ (D0 - D2) * vSupply cs / D0 ≠ 0 ∧
      ¬ (D0 - D2) * vSupply cs / D0 + Bytes.toB256 [1] < (D0 - D2) * vSupply cs / D0 ∧
      ¬ Sevm.dataWord sevm (Bytes.toB256 [0x64]) <
        (D0 - D2) * vSupply cs / D0 + Bytes.toB256 [1] ∧
      ¬ vSupply cs < (D0 - D2) * vSupply cs / D0 + Bytes.toB256 [1] ∧
      cb.sevm.currentTarget = (σ.get tokenSlot).toAdr ∧
      cb.sevm.data = burnFromSel ++ sevm.caller.toB256.toBytes ++
        ((D0 - D2) * vSupply cs / D0 + Bytes.toB256 [1]).toBytes ∧
      cb.sevm.value = 0 ∧ cb.sevm.isStatic = sevm.isStatic ∧ 32 ≤ cb.post.output.length ∧
      RliPushK sevm σ 0 L0 ∧ RliPushK sevm σ 1 L1 ∧ RliPushK sevm σ 2 L2 ∧
      (∀ x, (post.getStor sevm.currentTarget).get x =
        (((σ.set (balancesBase + Nat.toB256 0)
          (balAt σ 0 - Sevm.dataWord sevm (Bytes.toB256 [4]) - f0 * σ.get adminFeeSlot / rliDen)).set
          (balancesBase + Nat.toB256 1)
          (balAt σ 1 - Sevm.dataWord sevm (Bytes.toB256 [0x24]) - f1 * σ.get adminFeeSlot / rliDen)).set
          (balancesBase + Nat.toB256 2)
          (balAt σ 2 - Sevm.dataWord sevm (Bytes.toB256 [0x44]) - f2 * σ.get adminFeeSlot / rliDen)).get x) ∧
      post.logs = b.logs ++ (cs :: cb :: (L0 ++ L1 ++ L2)).flatMap (fun c => c.post.logs) ++
        [⟨sevm.currentTarget, [rliTopic, sevm.caller.toB256],
          (Sevm.dataWord sevm (Bytes.toB256 [4])).toBytes ++
          (Sevm.dataWord sevm (Bytes.toB256 [0x24])).toBytes ++
          (Sevm.dataWord sevm (Bytes.toB256 [0x44])).toBytes ++
          f0.toBytes ++ f1.toBytes ++ f2.toBytes ++ D1.toBytes ++
          (vSupply cs - ((D0 - D2) * vSupply cs / D0 + Bytes.toB256 [1])).toBytes⟩] ∧
      post.output = b.output := by
  subst hσ
  obtain ⟨_, h⟩ := xa_dispatch_removeLiquidityImbalance hcode hlen hcd hsel h
  obtain ⟨hlock, hval, hkill, cs, L1, A, b1, M1, G1, rfl, hsw, hT0, hm3, hA, hs1, hl1, ho1, hc1,
    hid1, h, hV⟩ := xa_rli_front hc hcode hfork ha htok h
  refine ⟨hlock, hval, hkill, ?_⟩
  have hB1 : ExBase sevm b b1 ((b.getStor sevm.currentTarget).set lockSlot 1) :=
    ⟨hs1, hc1 _ hpc, ho1, hid1 hid (hidk cs List.mem_cons_self)⟩
  have hk1 : ∀ c ∈ L1, ∀ x, (c.post.getStor sevm.currentTarget).get x =
      (c.pre.getStor sevm.currentTarget).get x :=
    fun c hc => hkeep c (List.mem_cons_of_mem _ hc)
  have hi1 : ∀ c ∈ L1, c.post.getCode 4 = c.pre.getCode 4 :=
    fun c hc => hidk c (List.mem_cons_of_mem _ hc)
  clear hkeep hidk
  obtain ⟨D0, M2, G2, hD0, hu0, hu1, hu2, h, hV⟩ := xa_rli_d0 hc hcode hfork hV h
  obtain ⟨D1, M3, G3, hD1, h, hV⟩ := xa_rli_d1 hc hcode hfork (D0 := D0) (T := vSupply cs) (F := (b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8])
    (AF := (b.getStor sevm.currentTarget).get adminFeeSlot) (A := A) (o0 := balAt (b.getStor sevm.currentTarget) 0) (o1 := balAt (b.getStor sevm.currentTarget) 1)
    (o2 := balAt (b.getStor sevm.currentTarget) 2)
    (n0 := balAt (b.getStor sevm.currentTarget) 0 - Sevm.dataWord sevm (Bytes.toB256 [4]))
    (n1 := balAt (b.getStor sevm.currentTarget) 1 - Sevm.dataWord sevm (Bytes.toB256 [0x24]))
    (n2 := balAt (b.getStor sevm.currentTarget) 2 - Sevm.dataWord sevm (Bytes.toB256 [0x44])) vsub h
  rw [show Bytes.toB256 [0] = Nat.toB256 0 from by decide] at hV
  -- the fee loop
  obtain ⟨hq0, hz0, dif0, M4, G4, hdif0, h, hV⟩ := xa_rli_feeA0 hcode hV h
  obtain ⟨hp0, hr0, ht0, hv0, b2, M5, G5, hB2, hl2, h, hV⟩ := xa_rli_feeB0 hcode hfork hB1 hV h
  obtain ⟨hq1, hz1, dif1, M6, G6, hdif1, h, hV⟩ := xa_rli_feeA1 hcode hV h
  obtain ⟨hp1, hr1, ht1, hv1, b3, M7, G7, hB3, hl3, h, hV⟩ := xa_rli_feeB1 hcode hfork hB2 hV h
  obtain ⟨hq2, hz2, dif2, M8, G8, hdif2, h, hV⟩ := xa_rli_feeA2 hcode hV h
  obtain ⟨hp2, hr2, ht2, hv2, b4, M9, G9, hB4, hl4, h, hV⟩ := xa_rli_feeB2 hcode hfork hB3 hV h
  obtain ⟨D2, M10, G10, hD2, hD02, hmT, hD0nz, hbn, hb1, hslip, h, hV⟩ :=
    xa_rli_d2 hc hcode hfork (D0 := D0) (D1 := D1) (T := vSupply cs) (F := (b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8])
    (AF := (b.getStor sevm.currentTarget).get adminFeeSlot) (A := A) (o0 := balAt (b.getStor sevm.currentTarget) 0) (o1 := balAt (b.getStor sevm.currentTarget) 1)
    (o2 := balAt (b.getStor sevm.currentTarget) 2)
    (n0 := balAt (b.getStor sevm.currentTarget) 0 - Sevm.dataWord sevm (Bytes.toB256 [4]) - ((b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]) * dif0 / rliDen)
    (n1 := balAt (b.getStor sevm.currentTarget) 1 - Sevm.dataWord sevm (Bytes.toB256 [0x24]) - ((b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]) * dif1 / rliDen)
    (n2 := balAt (b.getStor sevm.currentTarget) 2 - Sevm.dataWord sevm (Bytes.toB256 [0x44]) - ((b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]) * dif2 / rliDen)
    (f0 := ((b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]) * dif0 / rliDen) (f1 := ((b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]) * dif1 / rliDen)
    (f2 := ((b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]) * dif2 / rliDen) vsub h
  -- the burn
  have htw : (b4.getStor sevm.currentTarget).get tokenSlot =
      (b.getStor sevm.currentTarget).get tokenSlot := by
    rw [hB4.stor, Stor.get_set_ne _ (bal_ne_token (by decide)),
      Stor.get_set_ne _ (bal_ne_token (by decide)), Stor.get_set_ne _ (bal_ne_token (by decide)),
      Stor.get_set_ne _ lock_ne_token]
  obtain ⟨cb, Lr, d5, M11, img11, G11, rfl, hcb, hlen5, hdepth, hR, hW, hI, hc0, h⟩ :=
    xa_rli_burn hcode hfork hV htw htok h
  have hB5 := hB4.child hcb hpc (hk1 cb List.mem_cons_self) (hi1 cb List.mem_cons_self)
  have hk2 : ∀ c ∈ Lr, ∀ x, (c.post.getStor sevm.currentTarget).get x =
      (c.pre.getStor sevm.currentTarget).get x :=
    fun c hc => hk1 c (List.mem_cons_of_mem _ hc)
  have hi2 : ∀ c ∈ Lr, c.post.getCode 4 = c.pre.getCode 4 :=
    fun c hc => hi1 c (List.mem_cons_of_mem _ hc)
  clear hk1 hi1
  -- the transfers
  have hco : ∀ {v a0 a1 a2 : B256} (k : Nat), k < 3 → rliAmt sevm k ≠ 0 →
      ¬ sevm.benvStat.rules.isPrecomp
        (((((((b.getStor sevm.currentTarget).set lockSlot v).set (balancesBase + Nat.toB256 0)
          a0).set (balancesBase + Nat.toB256 1) a1).set (balancesBase + Nat.toB256 2) a2).get
          (coinsBase + Nat.toB256 k)).toAdr) := fun k hk _ => by
    rw [rli_coin_get hk]; exact hcoin k hk
  -- coin 0
  obtain ⟨Lc0, Lr0, b6, M12, img12, G12, rfl, hB6, hl6, hP0, hR, hW, hI, hc, h⟩ :=
    xa_rli_iter hcode hfork hB5 hpc hk2 hi2 hdepth (hco 0 (by decide)) hR hW hI hc0 h
  obtain ⟨M13, img13, G13, hR, hW, hI, hc, hbr⟩ := xa_rli_next hcode hR hW hI hc h
  rcases hbr with ⟨-, h⟩ | ⟨he, -⟩
  swap
  · exact absurd he (by decide)
  rw [show Bytes.toB256 [1] + Nat.toB256 0 = Nat.toB256 1 from by decide] at hc
  -- coin 1
  obtain ⟨Lc1, Lr1, b7, M14, img14, G14, rfl, hB7, hl7, hP1, hR, hW, hI, hc, h⟩ :=
    xa_rli_iter hcode hfork hB6 hpc (fun c hc' => hk2 c (List.mem_append_right _ hc'))
      (fun c hc' => hi2 c (List.mem_append_right _ hc')) hdepth (hco 1 (by decide)) hR hW hI hc h
  obtain ⟨M15, img15, G15, hR, hW, hI, hc, hbr⟩ := xa_rli_next hcode hR hW hI hc h
  rcases hbr with ⟨-, h⟩ | ⟨he, -⟩
  swap
  · exact absurd he (by decide)
  rw [show Bytes.toB256 [1] + Nat.toB256 1 = Nat.toB256 2 from by decide] at hc
  -- coin 2
  obtain ⟨Lc2, Lr2, b8, M16, img16, G16, rfl, hB8, hl8, hP2, hR, hW, hI, hc, h⟩ :=
    xa_rli_iter hcode hfork hB7 hpc
      (fun c hc' => hk2 c (List.mem_append_right _ (List.mem_append_right _ hc')))
      (fun c hc' => hi2 c (List.mem_append_right _ (List.mem_append_right _ hc'))) hdepth
      (hco 2 (by decide)) hR hW hI hc h
  obtain ⟨M17, img17, G17, hR, hW, hI, hc, hbr⟩ := xa_rli_next hcode hR hW hI hc h
  rcases hbr with ⟨hne, -⟩ | ⟨-, h⟩
  · exact absurd (by decide) hne
  -- the event and the lock
  obtain ⟨hTX, rfl, hsP, hlP, hoP⟩ := xa_rli_log hcode hfork hR hW hI h
  rw [rli_coin_get (by decide)] at hP0 hP1 hP2
  refine ⟨cs, cb, Lc0, Lc1, Lc2, A, D0, D1, D2, _, _, _,
    by simp only [List.append_nil, List.append_assoc], hsw, hT0, hm3, hA, hD0, hu0, hu1, hu2, hD1,
    ⟨hq0, hz0, dif0, hdif0, hp0, rfl, hr0, ht0, rfl, hv0, rfl⟩,
    ⟨hq1, hz1, dif1, hdif1, hp1, rfl, hr1, ht1, rfl, hv1, rfl⟩,
    ⟨hq2, hz2, dif2, hdif2, hp2, rfl, hr2, ht2, rfl, hv2, rfl⟩,
    hD2, hD02, hmT, hbn, hb1, hslip, hTX, hcb.target, hcb.data, hcb.value, hcb.isStatic, hlen5,
    hP0, hP1, hP2, fun x => ?_, ?_, ?_⟩
  · rw [hsP, Stor.get_set_ite, hB8.stor]
    by_cases hx : lockSlot = x
    · subst hx
      rw [ite_eq_left rfl, Stor.get_set_ne _ (bal_ne_lock (by decide)).symm,
        Stor.get_set_ne _ (bal_ne_lock (by decide)).symm,
        Stor.get_set_ne _ (bal_ne_lock (by decide)).symm, hlock]
    · rw [ite_eq_right hx, Stor.get_set_ite, Stor.get_set_ite, Stor.get_set_ite, Stor.get_set_ite,
        Stor.get_set_ite, Stor.get_set_ite, Stor.get_set_ite, ite_eq_right hx]
  · rw [hlP, hl8, hl7, hl6, hcb.logs, hl4, hl3, hl2, hl1]
    simp only [List.flatMap_cons, List.flatMap_append, hsw.logs, List.nil_append,
      List.append_assoc]
  · rw [hoP, hB8.output]

/-- **The `remove_liquidity_imbalance` frame under the conditional keep**: the same conclusion
as `xa_rli` when only the children at neither the pool nor `4` are known to keep the pool
(`RlKeepC`, which every frame at depth `1` satisfies), given that 3Crv and the coins are
neither. -/
theorem xa_rliC (hc : Cert.CheckedM code cert mems true) {σ : Stor} {s : State}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityImbalance)
    (hσ : b.getStor sevm.currentTarget = σ) (ha : Abstracts σ s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp (σ.get tokenSlot).toAdr)
    (hcoin : ∀ k, k < 3 → ¬ sevm.benvStat.rules.isPrecomp (σ.get (coinsBase + Nat.toB256 k)).toAdr)
    (hpc : b.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm b)
    (htokne : (σ.get tokenSlot).toAdr ≠ sevm.currentTarget ∧ (σ.get tokenSlot).toAdr ≠ 4)
    (hcoinne : ∀ k, k < 3 → (σ.get (coinsBase + Nat.toB256 k)).toAdr ≠ sevm.currentTarget ∧
      (σ.get (coinsBase + Nat.toB256 k)).toAdr ≠ 4)
    (hK : RlKeepC sevm L)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    σ.get lockSlot = 0 ∧ sevm.value = 0 ∧ σ.get isKilledSlot = 0 ∧
    ∃ (cs cb : Exec.Frame) (L0 L1 L2 : List Exec.Frame) (A D0 D1 D2 f0 f1 f2 : B256),
      L = cs :: cb :: (L0 ++ L1 ++ L2) ∧
      StaticWordChild (σ.get tokenSlot).toAdr totalSupplyData cs ∧ vSupply cs ≠ 0 ∧
      (σ.get feeSlot).Nofm (Bytes.toB256 [3]) ∧ aChk s sevm.benvStat.time.toNat = some A.toNat ∧
      getDMem ⟨(balAt σ 0).toNat, (balAt σ 1).toNat, (balAt σ 2).toNat⟩ A.toNat = some D0.toNat ∧
      ¬ balAt σ 0 < Sevm.dataWord sevm (Bytes.toB256 [4]) ∧
      ¬ balAt σ 1 < Sevm.dataWord sevm (Bytes.toB256 [0x24]) ∧
      ¬ balAt σ 2 < Sevm.dataWord sevm (Bytes.toB256 [0x44]) ∧
      getDMem ⟨(balAt σ 0 - Sevm.dataWord sevm (Bytes.toB256 [4])).toNat,
        (balAt σ 1 - Sevm.dataWord sevm (Bytes.toB256 [0x24])).toNat,
        (balAt σ 2 - Sevm.dataWord sevm (Bytes.toB256 [0x44])).toNat⟩ A.toNat = some D1.toNat ∧
      RliFeeIter (σ.get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]) (σ.get adminFeeSlot) D0 D1
        (balAt σ 0) (balAt σ 0 - Sevm.dataWord sevm (Bytes.toB256 [4])) f0
        (balAt σ 0 - Sevm.dataWord sevm (Bytes.toB256 [4]) - f0 * σ.get adminFeeSlot / rliDen)
        (balAt σ 0 - Sevm.dataWord sevm (Bytes.toB256 [4]) - f0) ∧
      RliFeeIter (σ.get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]) (σ.get adminFeeSlot) D0 D1
        (balAt σ 1) (balAt σ 1 - Sevm.dataWord sevm (Bytes.toB256 [0x24])) f1
        (balAt σ 1 - Sevm.dataWord sevm (Bytes.toB256 [0x24]) - f1 * σ.get adminFeeSlot / rliDen)
        (balAt σ 1 - Sevm.dataWord sevm (Bytes.toB256 [0x24]) - f1) ∧
      RliFeeIter (σ.get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]) (σ.get adminFeeSlot) D0 D1
        (balAt σ 2) (balAt σ 2 - Sevm.dataWord sevm (Bytes.toB256 [0x44])) f2
        (balAt σ 2 - Sevm.dataWord sevm (Bytes.toB256 [0x44]) - f2 * σ.get adminFeeSlot / rliDen)
        (balAt σ 2 - Sevm.dataWord sevm (Bytes.toB256 [0x44]) - f2) ∧
      getDMem ⟨(balAt σ 0 - Sevm.dataWord sevm (Bytes.toB256 [4]) - f0).toNat,
        (balAt σ 1 - Sevm.dataWord sevm (Bytes.toB256 [0x24]) - f1).toNat,
        (balAt σ 2 - Sevm.dataWord sevm (Bytes.toB256 [0x44]) - f2).toNat⟩ A.toNat =
        some D2.toNat ∧
      ¬ D0 < D2 ∧ (D0 - D2).Nofm (vSupply cs) ∧ (D0 - D2) * vSupply cs / D0 ≠ 0 ∧
      ¬ (D0 - D2) * vSupply cs / D0 + Bytes.toB256 [1] < (D0 - D2) * vSupply cs / D0 ∧
      ¬ Sevm.dataWord sevm (Bytes.toB256 [0x64]) <
        (D0 - D2) * vSupply cs / D0 + Bytes.toB256 [1] ∧
      ¬ vSupply cs < (D0 - D2) * vSupply cs / D0 + Bytes.toB256 [1] ∧
      cb.sevm.currentTarget = (σ.get tokenSlot).toAdr ∧
      cb.sevm.data = burnFromSel ++ sevm.caller.toB256.toBytes ++
        ((D0 - D2) * vSupply cs / D0 + Bytes.toB256 [1]).toBytes ∧
      cb.sevm.value = 0 ∧ cb.sevm.isStatic = sevm.isStatic ∧ 32 ≤ cb.post.output.length ∧
      RliPushK sevm σ 0 L0 ∧ RliPushK sevm σ 1 L1 ∧ RliPushK sevm σ 2 L2 ∧
      (∀ x, (post.getStor sevm.currentTarget).get x =
        (((σ.set (balancesBase + Nat.toB256 0)
          (balAt σ 0 - Sevm.dataWord sevm (Bytes.toB256 [4]) - f0 * σ.get adminFeeSlot / rliDen)).set
          (balancesBase + Nat.toB256 1)
          (balAt σ 1 - Sevm.dataWord sevm (Bytes.toB256 [0x24]) - f1 * σ.get adminFeeSlot / rliDen)).set
          (balancesBase + Nat.toB256 2)
          (balAt σ 2 - Sevm.dataWord sevm (Bytes.toB256 [0x44]) - f2 * σ.get adminFeeSlot / rliDen)).get x) ∧
      post.logs = b.logs ++ (cs :: cb :: (L0 ++ L1 ++ L2)).flatMap (fun c => c.post.logs) ++
        [⟨sevm.currentTarget, [rliTopic, sevm.caller.toB256],
          (Sevm.dataWord sevm (Bytes.toB256 [4])).toBytes ++
          (Sevm.dataWord sevm (Bytes.toB256 [0x24])).toBytes ++
          (Sevm.dataWord sevm (Bytes.toB256 [0x44])).toBytes ++
          f0.toBytes ++ f1.toBytes ++ f2.toBytes ++ D1.toBytes ++
          (vSupply cs - ((D0 - D2) * vSupply cs / D0 + Bytes.toB256 [1])).toBytes⟩] ∧
      post.output = b.output := by
  subst hσ
  obtain ⟨_, h⟩ := xa_dispatch_removeLiquidityImbalance hcode hlen hcd hsel h
  obtain ⟨hlock, hval, hkill, cs, L1, A, b1, M1, G1, rfl, hsw, hT0, hm3, hA, hs1, hl1, ho1, hc1,
    hid1, h, hV⟩ := xa_rli_front hc hcode hfork ha htok h
  refine ⟨hlock, hval, hkill, ?_⟩
  have hks := hK cs List.mem_cons_self (by rw [hsw.target]; exact htokne.1)
    (by rw [hsw.target]; exact htokne.2)
  have hB1 : ExBase sevm b b1 ((b.getStor sevm.currentTarget).set lockSlot 1) :=
    ⟨hs1, hc1 _ hpc, ho1, hid1 hid hks.2⟩
  have hK1 : RlKeepC sevm L1 := hK.tail
  clear hK
  obtain ⟨D0, M2, G2, hD0, hu0, hu1, hu2, h, hV⟩ := xa_rli_d0 hc hcode hfork hV h
  obtain ⟨D1, M3, G3, hD1, h, hV⟩ := xa_rli_d1 hc hcode hfork (D0 := D0) (T := vSupply cs) (F := (b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8])
    (AF := (b.getStor sevm.currentTarget).get adminFeeSlot) (A := A) (o0 := balAt (b.getStor sevm.currentTarget) 0) (o1 := balAt (b.getStor sevm.currentTarget) 1)
    (o2 := balAt (b.getStor sevm.currentTarget) 2)
    (n0 := balAt (b.getStor sevm.currentTarget) 0 - Sevm.dataWord sevm (Bytes.toB256 [4]))
    (n1 := balAt (b.getStor sevm.currentTarget) 1 - Sevm.dataWord sevm (Bytes.toB256 [0x24]))
    (n2 := balAt (b.getStor sevm.currentTarget) 2 - Sevm.dataWord sevm (Bytes.toB256 [0x44])) vsub h
  rw [show Bytes.toB256 [0] = Nat.toB256 0 from by decide] at hV
  -- the fee loop
  obtain ⟨hq0, hz0, dif0, M4, G4, hdif0, h, hV⟩ := xa_rli_feeA0 hcode hV h
  obtain ⟨hp0, hr0, ht0, hv0, b2, M5, G5, hB2, hl2, h, hV⟩ := xa_rli_feeB0 hcode hfork hB1 hV h
  obtain ⟨hq1, hz1, dif1, M6, G6, hdif1, h, hV⟩ := xa_rli_feeA1 hcode hV h
  obtain ⟨hp1, hr1, ht1, hv1, b3, M7, G7, hB3, hl3, h, hV⟩ := xa_rli_feeB1 hcode hfork hB2 hV h
  obtain ⟨hq2, hz2, dif2, M8, G8, hdif2, h, hV⟩ := xa_rli_feeA2 hcode hV h
  obtain ⟨hp2, hr2, ht2, hv2, b4, M9, G9, hB4, hl4, h, hV⟩ := xa_rli_feeB2 hcode hfork hB3 hV h
  obtain ⟨D2, M10, G10, hD2, hD02, hmT, hD0nz, hbn, hb1, hslip, h, hV⟩ :=
    xa_rli_d2 hc hcode hfork (D0 := D0) (D1 := D1) (T := vSupply cs) (F := (b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8])
    (AF := (b.getStor sevm.currentTarget).get adminFeeSlot) (A := A) (o0 := balAt (b.getStor sevm.currentTarget) 0) (o1 := balAt (b.getStor sevm.currentTarget) 1)
    (o2 := balAt (b.getStor sevm.currentTarget) 2)
    (n0 := balAt (b.getStor sevm.currentTarget) 0 - Sevm.dataWord sevm (Bytes.toB256 [4]) - ((b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]) * dif0 / rliDen)
    (n1 := balAt (b.getStor sevm.currentTarget) 1 - Sevm.dataWord sevm (Bytes.toB256 [0x24]) - ((b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]) * dif1 / rliDen)
    (n2 := balAt (b.getStor sevm.currentTarget) 2 - Sevm.dataWord sevm (Bytes.toB256 [0x44]) - ((b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]) * dif2 / rliDen)
    (f0 := ((b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]) * dif0 / rliDen) (f1 := ((b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]) * dif1 / rliDen)
    (f2 := ((b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]) * dif2 / rliDen) vsub h
  -- the burn
  have htw : (b4.getStor sevm.currentTarget).get tokenSlot =
      (b.getStor sevm.currentTarget).get tokenSlot := by
    rw [hB4.stor, Stor.get_set_ne _ (bal_ne_token (by decide)),
      Stor.get_set_ne _ (bal_ne_token (by decide)), Stor.get_set_ne _ (bal_ne_token (by decide)),
      Stor.get_set_ne _ lock_ne_token]
  obtain ⟨cb, Lr, d5, M11, img11, G11, rfl, hcb, hlen5, hdepth, hR, hW, hI, hc0, h⟩ :=
    xa_rli_burn hcode hfork hV htw htok h
  have hkb := hK1 cb List.mem_cons_self (by rw [hcb.target]; exact htokne.1)
    (by rw [hcb.target]; exact htokne.2)
  have hB5 := hB4.child hcb hpc hkb.1 hkb.2
  have hK2 : RlKeepC sevm Lr := hK1.tail
  clear hK1
  -- the transfers
  have hco : ∀ {v a0 a1 a2 : B256} (k : Nat), k < 3 → rliAmt sevm k ≠ 0 →
      ¬ sevm.benvStat.rules.isPrecomp
        (((((((b.getStor sevm.currentTarget).set lockSlot v).set (balancesBase + Nat.toB256 0)
          a0).set (balancesBase + Nat.toB256 1) a1).set (balancesBase + Nat.toB256 2) a2).get
          (coinsBase + Nat.toB256 k)).toAdr) := fun k hk _ => by
    rw [rli_coin_get hk]; exact hcoin k hk
  have hcone : ∀ {v a0 a1 a2 : B256} (k : Nat), k < 3 →
      ((((((b.getStor sevm.currentTarget).set lockSlot v).set (balancesBase + Nat.toB256 0)
        a0).set (balancesBase + Nat.toB256 1) a1).set (balancesBase + Nat.toB256 2) a2).get
        (coinsBase + Nat.toB256 k)).toAdr ≠ sevm.currentTarget ∧
      ((((((b.getStor sevm.currentTarget).set lockSlot v).set (balancesBase + Nat.toB256 0)
        a0).set (balancesBase + Nat.toB256 1) a1).set (balancesBase + Nat.toB256 2) a2).get
        (coinsBase + Nat.toB256 k)).toAdr ≠ 4 := fun k hk => by
    rw [rli_coin_get hk]; exact hcoinne k hk
  -- coin 0
  obtain ⟨Lc0, Lr0, b6, M12, img12, G12, rfl, hB6, hl6, hP0, hR, hW, hI, hc, h⟩ :=
    xa_rli_iterC hcode hfork hB5 hpc (hcone 0 (by decide)) hK2 hdepth (hco 0 (by decide)) hR hW hI hc0 h
  obtain ⟨M13, img13, G13, hR, hW, hI, hc, hbr⟩ := xa_rli_next hcode hR hW hI hc h
  rcases hbr with ⟨-, h⟩ | ⟨he, -⟩
  swap
  · exact absurd he (by decide)
  rw [show Bytes.toB256 [1] + Nat.toB256 0 = Nat.toB256 1 from by decide] at hc
  -- coin 1
  obtain ⟨Lc1, Lr1, b7, M14, img14, G14, rfl, hB7, hl7, hP1, hR, hW, hI, hc, h⟩ :=
    xa_rli_iterC hcode hfork hB6 hpc (hcone 1 (by decide))
      (fun c hc' h1 h2 => hK2 c (List.mem_append_right _ hc') h1 h2) hdepth (hco 1 (by decide))
      hR hW hI hc h
  obtain ⟨M15, img15, G15, hR, hW, hI, hc, hbr⟩ := xa_rli_next hcode hR hW hI hc h
  rcases hbr with ⟨-, h⟩ | ⟨he, -⟩
  swap
  · exact absurd he (by decide)
  rw [show Bytes.toB256 [1] + Nat.toB256 1 = Nat.toB256 2 from by decide] at hc
  -- coin 2
  obtain ⟨Lc2, Lr2, b8, M16, img16, G16, rfl, hB8, hl8, hP2, hR, hW, hI, hc, h⟩ :=
    xa_rli_iterC hcode hfork hB7 hpc (hcone 2 (by decide))
      (fun c hc' h1 h2 => hK2 c (List.mem_append_right _ (List.mem_append_right _ hc')) h1 h2)
      hdepth (hco 2 (by decide)) hR hW hI hc h
  obtain ⟨M17, img17, G17, hR, hW, hI, hc, hbr⟩ := xa_rli_next hcode hR hW hI hc h
  rcases hbr with ⟨hne, -⟩ | ⟨-, h⟩
  · exact absurd (by decide) hne
  -- the event and the lock
  obtain ⟨hTX, rfl, hsP, hlP, hoP⟩ := xa_rli_log hcode hfork hR hW hI h
  rw [rli_coin_get (by decide)] at hP0 hP1 hP2
  refine ⟨cs, cb, Lc0, Lc1, Lc2, A, D0, D1, D2, _, _, _,
    by simp only [List.append_nil, List.append_assoc], hsw, hT0, hm3, hA, hD0, hu0, hu1, hu2, hD1,
    ⟨hq0, hz0, dif0, hdif0, hp0, rfl, hr0, ht0, rfl, hv0, rfl⟩,
    ⟨hq1, hz1, dif1, hdif1, hp1, rfl, hr1, ht1, rfl, hv1, rfl⟩,
    ⟨hq2, hz2, dif2, hdif2, hp2, rfl, hr2, ht2, rfl, hv2, rfl⟩,
    hD2, hD02, hmT, hbn, hb1, hslip, hTX, hcb.target, hcb.data, hcb.value, hcb.isStatic, hlen5,
    hP0, hP1, hP2, fun x => ?_, ?_, ?_⟩
  · rw [hsP, Stor.get_set_ite, hB8.stor]
    by_cases hx : lockSlot = x
    · subst hx
      rw [ite_eq_left rfl, Stor.get_set_ne _ (bal_ne_lock (by decide)).symm,
        Stor.get_set_ne _ (bal_ne_lock (by decide)).symm,
        Stor.get_set_ne _ (bal_ne_lock (by decide)).symm, hlock]
    · rw [ite_eq_right hx, Stor.get_set_ite, Stor.get_set_ite, Stor.get_set_ite, Stor.get_set_ite,
        Stor.get_set_ite, Stor.get_set_ite, Stor.get_set_ite, ite_eq_right hx]
  · rw [hlP, hl8, hl7, hl6, hcb.logs, hl4, hl3, hl2, hl1]
    simp only [List.flatMap_cons, List.flatMap_append, hsw.logs, List.nil_append,
      List.append_assoc]
  · rw [hoP, hB8.output]

end

end Blanc.Lift.Curve3Pool
