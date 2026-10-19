import Blanc.Composition.Curve3Pool3CrvCoinExact

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.Composition.Curve3Pool3CrvJoint
open Blanc.Composition.UniswapV2PairWeth9Joint (vcsm_benvStat vcsm_caller vcsm_currentTarget
  vcsm_value vcsm_isStatic vcsm_code vcsm_state vcsm_gasLeft vcsm_stack vcsm_memory vcsm_error
  mem_read_fst callSpawnParent_memory_data addAccessedAddress_setMach_memory)

section Premises

open VyperNonreentrantDeployed.Token20 (balSlot allowSlot)

variable {sevm : Sevm} {t amt : B256} {W W' : Devm → Prop} {c : Adr} {U : Nat} {ii oi : B256}

/-- **A coin answers the pool's pull from `Token20`'s code** (`CoinPullOkAt` at any window inside
`[0, 0xc20)`): wherever the pull fits the coin's ledger, `Token20`'s actual `transferFrom` run
answers it. -/
theorem token20_coinPullOkAt (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hprec : ¬ sevm.benvStat.rules.isPrecomp c) (ht : t.toAdr = c) (hne : c ≠ sevm.currentTarget)
    (hU : 80000 ≤ U) (hii : ii.toNat + 0x64 ≤ 3104) (hoi : oi.toNat + 32 ≤ 3104)
    (hW : ∀ b, W b → b.getCode c = VyperNonreentrantDeployed.Token20.code ∧
      T20PullFits (b.getStor c) sevm.caller sevm.currentTarget sevm.currentTarget amt)
    (hW' : ∀ b d, W b → CoinLeaves c (t20Move (t20Allow (b.getStor c) sevm.caller
        sevm.currentTarget amt) sevm.caller sevm.currentTarget amt)
      ((getOrigAcct sevm c).stor = b.getStor c ∧ c ∉ b.createdAccounts ∧
        allowSlot sevm.caller sevm.currentTarget ≠ balSlot sevm.caller ∧
        allowSlot sevm.caller sevm.currentTarget ≠ balSlot sevm.currentTarget ∧
        balSlot sevm.caller ≠ balSlot sevm.currentTarget) b d → W' d) :
    Curve3Pool.CoinPullOkAt sevm W W' t amt U ii oi := by
  exact (token20_coinPullExactAt hfork hstatic hdepth hprec ht hne hU hii hoi hW hW').bounded

/-- **A coin answers the pool's push from `Token20`'s code** (`CoinPushOkAt` at any window inside
`[0, 0xc20)`): wherever the transfer to the caller fits the coin's ledger, `Token20`'s actual
`transfer` run answers it. -/
theorem token20_coinPushOkAt (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hprec : ¬ sevm.benvStat.rules.isPrecomp c) (ht : t.toAdr = c) (hne : c ≠ sevm.currentTarget)
    (hU : 80000 ≤ U) (hii : ii.toNat + 0x44 ≤ 3104) (hoi : oi.toNat + 32 ≤ 3104)
    (hW : ∀ b, W b → b.getCode c = VyperNonreentrantDeployed.Token20.code ∧
      T20MoveFits (b.getStor c) sevm.currentTarget sevm.caller amt)
    (hW' : ∀ b d, W b → CoinLeaves c (t20Move (b.getStor c) sevm.currentTarget sevm.caller amt)
      ((getOrigAcct sevm c).stor = b.getStor c ∧ c ∉ b.createdAccounts ∧
        balSlot sevm.currentTarget ≠ balSlot sevm.caller) b d → W' d) :
    Curve3Pool.CoinPushOkAt sevm W W' t amt U ii oi := by
  exact (token20_coinPushExactAt hfork hstatic hdepth hprec ht hne hU hii hoi hW hW').bounded

end Premises

/-! ## The coins' premises for `exchange(0, 1, 100, 0)`

The world invariants share a core (`WCore`): no error, none of the pool and the two coins created
in the transaction, and a nonnegative refund potential at the pool (`refundPotential`, over the
keys of its synthetic storage) — what the transaction needs of the frame's post.  Before the pull
(`WPull`) both coins also hold `Token20` over their synthetic ledgers; after it (`WPush`) coin 1
still does; after the push the core alone is kept. -/

/-- The keys of the synthetic pool storage. -/
def poolKeys : Finset B256 := (Std.TreeMap.keys (cmp := compare) poolStor).toFinset

theorem poolStor_get_of_not_mem {x : B256} (h : x ∉ poolKeys) : poolStor.get x = 0 := by
  unfold Stor.get
  exact Std.TreeMap.getD_eq_fallback
    (fun hm => h (List.mem_toFinset.mpr (Std.TreeMap.mem_keys.mpr hm)))

/-- The core of the world invariants. -/
def WCore (sevm : Sevm) (b : Devm) : Prop :=
  b.error = none ∧ poolAddr ∉ b.createdAccounts ∧ coin0Addr ∉ b.createdAccounts ∧
    coin1Addr ∉ b.createdAccounts ∧ 0 ≤ refundPotential sevm b poolAddr poolKeys

/-- The world before the pull. -/
def WPull (sevm : Sevm) (b : Devm) : Prop :=
  b.getCode coin0Addr = VyperNonreentrantDeployed.Token20.code ∧
    b.getCode coin1Addr = VyperNonreentrantDeployed.Token20.code ∧
    b.getStor coin0Addr = coin0Stor ∧ b.getStor coin1Addr = coin1Stor ∧ WCore sevm b

/-- The world after the pull. -/
def WPush (sevm : Sevm) (b : Devm) : Prop :=
  b.getCode coin1Addr = VyperNonreentrantDeployed.Token20.code ∧ b.getStor coin1Addr = coin1Stor ∧
    WCore sevm b

/-- A clean coin child keeps the core when its refund condition holds: it writes only its coin's
storage, creates nothing, and does not lower the refund counter. -/
theorem wCore_leaves {sevm : Sevm} {c : Adr} {σ' : Stor} {R : Prop} {b d : Devm}
    (h : WCore sevm b) (hl : CoinLeaves c σ' R b d) (hc : c ≠ poolAddr) (hR : R) :
    WCore sevm d := by
  obtain ⟨he, hp, h0, h1, hpot⟩ := h
  refine ⟨hl.error.trans he, by rw [hl.created]; exact hp, by rw [hl.created]; exact h0,
    by rw [hl.created]; exact h1, ?_⟩
  have hr := hl.refund hR
  rw [refundPotential_add (x := d.refundCounter - b.refundCounter) (by omega) hl.created
    (hl.other _ (Ne.symm hc))]
  omega

/-- **Coin 0 answers `exchange`'s pull** over `WPull`/`WPush`: `token20_coinPullOkAt` at the
synthetic ledger. -/
theorem wPull_pullOkAt {sevm : Sevm} {t : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hcaller : sevm.caller = trader)
    (htarget : sevm.currentTarget = poolAddr)
    (horig : (getOrigAcct sevm coin0Addr).stor = coin0Stor)
    (hprec : ¬ sevm.benvStat.rules.isPrecomp coin0Addr) (ht : t.toAdr = coin0Addr) :
    Curve3Pool.CoinPullOkAt sevm (WPull sevm) (WPush sevm) t (Nat.toB256 exchangeDx) 80000
      0x600 0x6c0 := by
  refine token20_coinPullOkAt hfork hstatic hdepth hprec ht (by rw [htarget]; decide +kernel)
    (le_refl _) (by decide) (by decide) (fun b hb => ⟨hb.1, ?_⟩) (fun b d hb hl => ?_)
  · rw [hb.2.2.1, hcaller, htarget]
    unfold T20PullFits T20MoveFits t20Allow
    decide +kernel
  · obtain ⟨c0, c1, s0, s1, hcore⟩ := hb
    refine ⟨by rw [hl.code]; exact c1, by rw [hl.other _ (by decide +kernel)]; exact s1,
      wCore_leaves hcore hl (by decide +kernel) ⟨by rw [horig, s0], hcore.2.2.1, ?_⟩⟩
    rw [hcaller, htarget]
    decide +kernel

/-- **Coin 1 answers `exchange`'s push** of `132` from `WPush` into `WCore`. -/
theorem wPush_pushOkAt {sevm : Sevm} {t : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hcaller : sevm.caller = trader)
    (htarget : sevm.currentTarget = poolAddr)
    (horig : (getOrigAcct sevm coin1Addr).stor = coin1Stor)
    (hprec : ¬ sevm.benvStat.rules.isPrecomp coin1Addr) (ht : t.toAdr = coin1Addr) :
    Curve3Pool.CoinPushOkAt sevm (WPush sevm) (WCore sevm) t 132 80000 0xb60 0xc00 := by
  refine token20_coinPushOkAt hfork hstatic hdepth hprec ht (by rw [htarget]; decide +kernel)
    (le_refl _) (by decide) (by decide) (fun b hb => ⟨hb.1, ?_⟩) (fun b d hb hl => ?_)
  · rw [hb.2.1, hcaller, htarget]
    unfold T20MoveFits
    decide +kernel
  · obtain ⟨c1, s1, hcore⟩ := hb
    refine wCore_leaves hcore hl (by decide +kernel) ⟨by rw [horig, s1], hcore.2.2.2.1, ?_⟩
    rw [hcaller, htarget]
    decide +kernel

section Closed

variable {sevm : Sevm}

/-- The pool's snapshot storage is zero off `poolKeys`, as an `SSTORE` sentry reads it. -/
theorem pool_hK (horig : (getOrigAcct sevm poolAddr).stor = poolStor) {b : Devm}
    (hcr : poolAddr ∉ b.createdAccounts) :
    ∀ x, x ∉ poolKeys → b.getOrigStorVal sevm poolAddr x = 0 := by
  intro x hx
  unfold Devm.getOrigStorVal
  rw [ite_eq_right hcr]
  unfold Jaune.getOrigStorVal
  rw [horig]
  exact poolStor_get_of_not_mem hx

/-- `WCore` survives the pool's own steps. -/
theorem wCore_closed (htarget : sevm.currentTarget = poolAddr)
    (horig : (getOrigAcct sevm poolAddr).stor = poolStor) :
    Curve3Pool.WClosed sevm (WCore sevm) where
  st _ _ _ _ h := h
  sload b k h := by
    obtain ⟨he, hp, h0, h1, hpot⟩ := h
    have hc := afterSload_createdAccounts sevm b k
    refine ⟨by rw [afterSload_error]; exact he, by rw [hc]; exact hp, by rw [hc]; exact h0,
      by rw [hc]; exact h1, ?_⟩
    rw [refundPotential_congr afterSload_refundCounter hc (afterSload_getStor sevm b k poolAddr)]
    exact hpot
  sstore b k v h := by
    obtain ⟨he, hp, h0, h1, hpot⟩ := h
    have hc := afterSstore_createdAccounts sevm b k v
    refine ⟨by rw [afterSstore_error]; exact he, by rw [hc]; exact hp, by rw [hc]; exact h0,
      by rw [hc]; exact h1, ?_⟩
    have hmono := refundPotential_afterSstore (sevm := sevm) (b := b) (K := poolKeys) (k := k)
      (v := v) (by rw [htarget]; exact pool_hK horig hp)
    rw [htarget] at hmono
    exact hpot.trans hmono
  sha b b' rd hp h := by
    obtain ⟨he, hpl, h0, h1, hpot⟩ := h
    refine ⟨by rw [hp.error]; exact he, by rw [hp.created]; exact hpl, by rw [hp.created]; exact h0,
      by rw [hp.created]; exact h1, ?_⟩
    rw [refundPotential_congr hp.refund hp.created (hp.stor poolAddr)]
    exact hpot
  log _ _ h := h

/-- `WPull` survives the pool's own steps. -/
theorem wPull_closed (htarget : sevm.currentTarget = poolAddr)
    (horig : (getOrigAcct sevm poolAddr).stor = poolStor) :
    Curve3Pool.WClosed sevm (WPull sevm) where
  st b S M G h := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, (wCore_closed htarget horig).st b S M G h.2.2.2.2⟩
  sload b k h := by
    obtain ⟨c0, c1, s0, s1, hc⟩ := h
    refine ⟨by rw [afterSload_getCode]; exact c0, by rw [afterSload_getCode]; exact c1,
      by rw [afterSload_getStor]; exact s0, by rw [afterSload_getStor]; exact s1,
      (wCore_closed htarget horig).sload b k hc⟩
  sstore b k v h := by
    obtain ⟨c0, c1, s0, s1, hc⟩ := h
    refine ⟨by rw [afterSstore_getCode]; exact c0, by rw [afterSstore_getCode]; exact c1,
      by rw [afterSstore_getStor_ne _ _ _ _ _ (by rw [htarget]; decide +kernel)]; exact s0,
      by rw [afterSstore_getStor_ne _ _ _ _ _ (by rw [htarget]; decide +kernel)]; exact s1,
      (wCore_closed htarget horig).sstore b k v hc⟩
  sha b b' rd hp h := by
    obtain ⟨c0, c1, s0, s1, hc⟩ := h
    refine ⟨by rw [hp.code]; exact c0, by rw [hp.code]; exact c1, by rw [hp.stor]; exact s0,
      by rw [hp.stor]; exact s1, (wCore_closed htarget horig).sha b b' rd hp hc⟩
  log _ _ h := h

/-- `WPush` survives the pool's own steps. -/
theorem wPush_closed (htarget : sevm.currentTarget = poolAddr)
    (horig : (getOrigAcct sevm poolAddr).stor = poolStor) :
    Curve3Pool.WClosed sevm (WPush sevm) where
  st b S M G h := ⟨h.1, h.2.1, (wCore_closed htarget horig).st b S M G h.2.2⟩
  sload b k h := by
    obtain ⟨c1, s1, hc⟩ := h
    refine ⟨by rw [afterSload_getCode]; exact c1, by rw [afterSload_getStor]; exact s1,
      (wCore_closed htarget horig).sload b k hc⟩
  sstore b k v h := by
    obtain ⟨c1, s1, hc⟩ := h
    refine ⟨by rw [afterSstore_getCode]; exact c1,
      by rw [afterSstore_getStor_ne _ _ _ _ _ (by rw [htarget]; decide +kernel)]; exact s1,
      (wCore_closed htarget horig).sstore b k v hc⟩
  sha b b' rd hp h := by
    obtain ⟨c1, s1, hc⟩ := h
    refine ⟨by rw [hp.code]; exact c1, by rw [hp.stor]; exact s1,
      (wCore_closed htarget horig).sha b b' rd hp hc⟩
  log _ _ h := h

end Closed

end Blanc.Composition.Curve3Pool3CrvInstance
