import Blanc.Lift.Curve3Pool.Walk.AddLiquidityBack
import Blanc.Lift.Curve3Pool.Walk.AddLiquidity
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidity
import Blanc.Lift.Curve3Pool.Walk.OneCoin
import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceWalk
import Blanc.Lift.Curve3Pool.Walk.WithdrawAdminFeesRaw
import Blanc.Lift.Curve3Pool.Walk.Exchange

/-!
# Every child of the six calling entries is one a pool walk can name

For each entry that calls a coin state-changingly: under the walk's conditional keep (`KeepSel`), every direct
committed child of a successful frame is at the token, or at a coin on a selector the pool sends coins
(`PoolChildSel`). Each theorem reads this off the entry's walk.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc Blanc.Lift

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}

private theorem childSel_coin {σ : Stor} {c : Exec.Frame} {i : Nat} (hi : i < 3)
    (ht : c.sevm.currentTarget = (σ.get (coinsBase + Nat.toB256 i)).toAdr)
    (hs : CurveCoins.PoolCoinSel (Sevm.selector c.sevm)) : PoolChildSel σ c :=
  .inr ⟨⟨i, hi, ht⟩, hs⟩

private theorem childSel_coinK {σ : Stor} {c : Exec.Frame} (k : Fin 3)
    (ht : c.sevm.currentTarget = (σ.get (coinSlot k)).toAdr)
    (hs : CurveCoins.PoolCoinSel (Sevm.selector c.sevm)) : PoolChildSel σ c :=
  .inr ⟨⟨k.val, k.2, ht⟩, hs⟩

theorem AlPullKids.sel {C amt cr : B256} {i : Nat} {Lc : List Exec.Frame}
    (h : AlPullKids sevm C i amt Lc cr) : ∀ c ∈ Lc, CurveCoins.PoolCoinSel (Sevm.selector c.sevm) := by
  rcases h with ⟨-, rfl, -⟩ | ⟨-, -, c, rfl, hp, -⟩ | ⟨-, -, c0, c, c1, rfl, h0, hp, h1, -, -⟩
  · intro c' hc'
    exact absurd hc' List.not_mem_nil
  · intro c' hc'
    rw [List.mem_singleton] at hc'
    subst hc'
    exact poolCoinSel_transferFromData hp.data
  · intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl
    · exact poolCoinSel_balanceOfData h0.data
    · exact poolCoinSel_transferFromData hp.data
    · exact poolCoinSel_balanceOfData h1.data

/-- **`add_liquidity`.** -/
theorem al_children_sel {s : State} (hchk : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selAddLiquidity)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ i, i < 3 → ¬ sevm.benvStat.rules.isPrecomp (coinAt (b.getStor sevm.currentTarget) i).toAdr)
    (hpc : b.getCode sevm.currentTarget ≠ .empty) (hid : IdReadyH sevm b)
    (hK : KeepSel sevm (b.getStor sevm.currentTarget) L)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∀ c ∈ L, PoolChildSel (b.getStor sevm.currentTarget) c := by
  obtain ⟨-, -, -, -, A, cT, L0, L1, L2, L', D0, D1, cr0, cr1, cr2, b', M, img, G', -, hL, hTt,
    -, -, -, -, -, -, hk0, hk1, hk2, -, -, -, -, -, -, hst', -, -, hcd', -, hR, hW, hA, hm, w900,
    h⟩ := xa_al_frontC hchk hcode hfork hlen hcd hsel ha htok hcoin hpc hid hK h
  have htokB : ∀ k : Nat, k < 3 → balancesBase + Nat.toB256 k ≠ tokenSlot := fun k hk => by
    rcases three_cases hk with rfl | rfl | rfl <;> decide
  obtain ⟨-, -, -, -, -, -, -, -, cm, rfl, -, -, -, -, hmt, -⟩ :=
    xa_al_backC hchk hcode hfork hR hW hA hm w900 hst'
      (by rw [Stor.get_set_ne _ lock_ne_token]; exact htok) htokB
      (by rw [hcd']; exact hpc)
      (fun c hc ht => (hK.tok c (by rw [hL]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hc))
        (by rw [ht, Stor.get_set_ne _ lock_ne_token])).1) h
  have hcoinS : ∀ {i : Nat}, i < 3 → ∀ c : Exec.Frame, c.sevm.currentTarget =
      (coinAt (alLocked (b.getStor sevm.currentTarget)) i).toAdr →
      c.sevm.currentTarget = ((b.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i)).toAdr :=
    fun hi c ht => by rw [ht, coinAt, Stor.get_set_ne _ (coin_ne_lock hi)]
  intro c hc
  rw [hL] at hc
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | ((hc | hc) | hc) | rfl
  · exact .inl (by rw [hTt])
  · exact childSel_coin (i := 0) (by decide) (hcoinS (by decide) c (hk0.target c hc)) (AlPullKids.sel hk0 c hc)
  · exact childSel_coin (i := 1) (by decide) (hcoinS (by decide) c (hk1.target c hc)) (AlPullKids.sel hk1 c hc)
  · exact childSel_coin (i := 2) (by decide) (hcoinS (by decide) c (hk2.target c hc)) (AlPullKids.sel hk2 c hc)
  · exact .inl (by rw [hmt, Stor.get_set_ne _ lock_ne_token])

/-- **`remove_liquidity`.** -/
theorem rl_children_sel (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidity)
    (htok : ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ i, i < 3 → ¬ sevm.benvStat.rules.isPrecomp (coinAt (b.getStor sevm.currentTarget) i).toAdr)
    (hpc : b.getCode sevm.currentTarget ≠ .empty) (hid : IdReadyH sevm b)
    (hK : KeepSel sevm (b.getStor sevm.currentTarget) L)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∀ c ∈ L, PoolChildSel (b.getStor sevm.currentTarget) c := by
  obtain ⟨-, -, c0, c1, c2, c3, c4, hL, h0t, -, -, -, -, hp1, hp2, hp3, -, h4t, -⟩ :=
    xa_removeLiquidity hcode hfork hlen hcd hsel htok hcoin hpc hid hK h
  intro c hc
  rw [hL] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact .inl h0t
  · exact childSel_coin (i := 0) (by decide) hp1.target (poolCoinSel_transferData hp1.data)
  · exact childSel_coin (i := 1) (by decide) hp2.target (poolCoinSel_transferData hp2.data)
  · exact childSel_coin (i := 2) (by decide) hp3.target (poolCoinSel_transferData hp3.data)
  · exact .inl h4t

/-- **`remove_liquidity_one_coin`.** -/
theorem oc_children_sel {s : State} (hchk : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hcoin : (exJ sevm).toNat < 3 →
      ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get (coinsBase + exJ sevm)).toAdr)
    (hpc : b.getCode sevm.currentTarget ≠ .empty) (hid : IdReadyH sevm b)
    (hK : KeepSel sevm (b.getStor sevm.currentTarget) L)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∀ c ∈ L, PoolChildSel (b.getStor sevm.currentTarget) c := by
  obtain ⟨-, -, -, cs, cb, cp, hi, dy, fee, hL, hsw, -, -, -, -, -, hbt, -, -, -, -, hpt, hpd, -⟩ :=
    xa_oneCoin2C hchk hcode hfork hlen hcd hsel rfl ha htok hcoin hpc hid hK h
  intro c hc
  rw [hL] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact .inl hsw.target
  · exact .inl hbt
  · exact childSel_coin hi (by rw [hpt, toB256_toNat]) (CurveCoins.poolCoinSel_transfer hpd)

private theorem rliPushK_sel {σ : Stor} {k : Nat} {Lc : List Exec.Frame} (hk : k < 3)
    (h : RliPushK sevm σ k Lc) : ∀ c ∈ Lc, PoolChildSel σ c := by
  rcases h with ⟨-, rfl⟩ | ⟨-, w, rfl, ht, hd, -⟩
  · intro c hc
    exact absurd hc List.not_mem_nil
  · intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    exact childSel_coin hk ht (CurveCoins.poolCoinSel_transfer hd)

/-- **`remove_liquidity_imbalance`.** -/
theorem rli_children_sel {s : State} (hchk : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityImbalance)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ k, k < 3 → ¬ sevm.benvStat.rules.isPrecomp
      ((b.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 k)).toAdr)
    (hpc : b.getCode sevm.currentTarget ≠ .empty) (hid : IdReadyH sevm b)
    (hK : KeepSel sevm (b.getStor sevm.currentTarget) L)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∀ c ∈ L, PoolChildSel (b.getStor sevm.currentTarget) c := by
  obtain ⟨-, -, -, cs, cb, L0, L1, L2, A, D0, D1, D2, f0, f1, f2, hL, hsw, hT0, hm3, hA,
    hD0, hu0, hu1, hu2, hD1, h0, h1, h2, hD2, hD02, hmT, hbn, hb1, hslip, hTX, hbt, hbd, hbv,
    hbs, hblen, hP0, hP1, hP2, hstor, hlogs, hout⟩ :=
    xa_rliC hchk hcode hfork hlen hcd hsel rfl ha htok hcoin hpc hid hK h
  intro c hc
  rw [hL] at hc
  simp only [List.mem_cons, List.mem_append] at hc
  rcases hc with rfl | rfl | (m0 | m1) | m2
  · exact .inl hsw.target
  · exact .inl hbt
  · exact rliPushK_sel (by decide) hP0 c m0
  · exact rliPushK_sel (by decide) hP1 c m1
  · exact rliPushK_sel (by decide) hP2 c m2

private theorem wdKids_sel {σ : Stor} {k : Fin 3} {c0 : Exec.Frame} {Lp : List Exec.Frame}
    (h : WdKids sevm σ k c0 Lp) : ∀ c ∈ c0 :: Lp, PoolChildSel σ c := by
  have push := h.push
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with rfl | hc
  · exact childSel_coinK k h.target (poolCoinSel_balanceOfData h.data)
  · rcases Lp with - | ⟨p, - | ⟨p2, t⟩⟩
    · exact absurd hc List.not_mem_nil
    · rw [List.mem_singleton] at hc
      subst hc
      exact childSel_coinK k push.2.1 (poolCoinSel_transferData push.2.2.1)
    · exact push.elim

/-- **`withdraw_admin_fees`.** -/
theorem wd_children_sel (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selWithdrawAdminFees)
    (hid : IdReadyH sevm b) (hpc : b.getCode sevm.currentTarget ≠ .empty)
    (hK : KeepSel sevm (b.getStor sevm.currentTarget) L)
    (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
      (((b.getStor sevm.currentTarget).get (coinSlot k)).toAdr))
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∀ c ∈ L, PoolChildSel (b.getStor sevm.currentTarget) c := by
  obtain ⟨-, -, c0, c1, c2, Lp0, Lp1, Lp2, hL, hk0, hk1, hk2, -⟩ :=
    xa_withdraw hcode hfork hlen hcd hsel hid hpc hK hcoin h
  intro c hc
  rw [hL] at hc
  simp only [List.mem_cons, List.mem_append] at hc
  rcases hc with rfl | m | rfl | m | rfl | m
  · exact wdKids_sel hk0 _ List.mem_cons_self
  · exact wdKids_sel hk0 c (List.mem_cons_of_mem _ m)
  · exact wdKids_sel hk1 _ List.mem_cons_self
  · exact wdKids_sel hk1 c (List.mem_cons_of_mem _ m)
  · exact wdKids_sel hk2 _ List.mem_cons_self
  · exact wdKids_sel hk2 c (List.mem_cons_of_mem _ m)

/-- **`exchange`.** -/
theorem ex_children_sel {s : State} (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
    (hpc : b.getCode sevm.currentTarget ≠ .empty) (hid : IdReadyH sevm b)
    (hK : KeepSel sevm (b.getStor sevm.currentTarget) L)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∀ c ∈ L, PoolChildSel (b.getStor sevm.currentTarget) c := by
  have name : ∀ c, ExCoinSel sevm b c → PoolChildSel (b.getStor sevm.currentTarget) c := by
    rintro c ⟨⟨k, hk⟩, hs⟩
    exact childSel_coinK k hk hs
  have hci : (exI sevm).toNat < 3 → ¬ sevm.benvStat.rules.isPrecomp
      ((b.getStor sevm.currentTarget).get (coinsBase + exI sevm)).toAdr := fun hi => by
    simpa only [coinSlot, toB256_toNat] using hcoin ⟨_, hi⟩
  have hcj : (exJ sevm).toNat < 3 → ¬ sevm.benvStat.rules.isPrecomp
      ((b.getStor sevm.currentTarget).get (coinsBase + exJ sevm)).toAdr := fun hj => by
    simpa only [coinSlot, toB256_toNat] using hcoin ⟨_, hj⟩
  obtain ⟨-, -, -, hi3, hj3, x0, x1, x2, -, Lp, cp, cq, D, y, amp, hL, hcpm, hpt, hpd, -, -, -,
    hpull, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hqt, hqd, -⟩ :=
    xa_exchange hcode hfork hlen hcd hsel rfl ha hci hcj hpc hid
      (fun c hc hk => (hK c hc (name c hk)).1) (fun c hc hk => (hK c hc (name c hk)).2) h
  intro c hc
  rw [hL] at hc
  rcases List.mem_append.mp hc with hc | hc
  · rcases hpull with ⟨-, rfl, -⟩ | ⟨-, c1, c2, rfl, hb1, hb2, -⟩
    · rw [List.mem_singleton] at hc
      subst hc
      exact name _ ⟨exCoinChild_of hi3 hpt, CurveCoins.poolCoinSel_transferFrom hpd⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact name _ ⟨exCoinChild_of hi3 hb1.target, CurveCoins.poolCoinSel_balanceOf hb1.data⟩
      · exact name _ ⟨exCoinChild_of hi3 hpt, CurveCoins.poolCoinSel_transferFrom hpd⟩
      · exact name _ ⟨exCoinChild_of hi3 hb2.target, CurveCoins.poolCoinSel_balanceOf hb2.data⟩
  · rw [List.mem_singleton] at hc
    subst hc
    exact name _ ⟨exCoinChild_of hj3 hqt, CurveCoins.poolCoinSel_transfer hqd⟩

end

end Blanc.Lift.Curve3Pool
