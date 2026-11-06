import Blanc.Composition.Curve3PoolExitCold
import Blanc.Composition.Curve3PoolSwapSites

/-!
# A coin's call inside `exchange`, from what the frame stands on

`CoinStand`: an entry's facts about the parties, at any static gas. `CoinStand.pay` is `coin j`'s `transfer` at `exchange`'s push site;
`CoinStand.pullA` is DAI's and USDC's `transferFrom` at its pull site. USDT's pull, entered after a balance read, is
`CoinStand.pullT`.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.Lift.AccumulatedWalk Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.Curve3PoolCoinExactKit
open Blanc.Composition.Curve3Pool3CrvLiteralWitness (swapPullD swapPullN swapPushD swapPushN)

/-- What an entry's coin calls stand on, at a message's entry. -/
structure CoinStand (s : Sevm) (p : Devm) (w : Jaune.State) (E : Adr) : Prop where
  fork : CoveredFork s.benvStat.fork
  target : s.currentTarget = pool
  caller : s.caller = E
  keysCold : ∀ k, k ∉ p.accessedStorageKeys
  clean : Clean p
  stor : ∀ x, x = pool ∨ x = c3 ∨ x = dai ∨ x = usdc ∨ x = usdt →
    p.getStor x = w.getStor x ∧ (getOrigAcct s x).stor = w.getStor x
  warm : ∀ x, x = c3 ∨ x = dai ∨ x = usdc ∨ x = usdt ∨ x = Usdc.usdcImpl → x ∉ p.accessedAddresses
  apart : CoinsApart w E
  open' : CoinsOpen w E

section Stand

variable {s : Sevm} {p : Devm} {w : Jaune.State} {E : Adr}

/-- A party the chain has left alone is as the entry has it: cold, at the moment's storage. -/
theorem CoinStand.party (f : CoinStand s p w E) {x : Adr} (hx : x = pool ∨ x = c3 ∨ x = dai ∨ x = usdc ∨ x = usdt)
    {Tl : List Adr} {r : Int} {n : Devm} (m : Mv Tl r p n) (hT : x ∉ Tl) : At x [] (w.getStor x) n :=
  (At.mk (fun k => ⟨fun h => absurd h (f.keysCold _), fun h => absurd h List.not_mem_nil⟩) (f.stor x hx).1).ofMv m hT

/-- A coin's site, from a chain that has left it alone. -/
theorem CoinStand.site (f : CoinStand s p w E) {x : Adr} {Tb : List Adr} {r : Int} {b : Devm} {t : B256} (htx : t.toAdr = x)
    (hx : x = pool ∨ x = c3 ∨ x = dai ∨ x = usdc ∨ x = usdt)
    (m : Mv Tb r p b) (hT : x ∉ Tb) :
    CoinSite s b t.toAdr ∧ b.getStor t.toAdr = w.getStor x :=
  have ha := f.party hx m hT
  ⟨⟨f.fork, m.clean f.clean, fun k hm => absurd ((ha.keys k).1 (by rw [← htx]; exact hm)) List.not_mem_nil,
    by rw [htx, ha.stor]; exact (f.stor x hx).2⟩, by rw [htx]; exact ha.stor⟩

/-- A site's address starts cold. -/
theorem CoinStand.coldAddr (f : CoinStand s p w E) {x : Adr} {Tb : List Adr} {r : Int} {b : Devm}
    (hx : x = c3 ∨ x = dai ∨ x = usdc ∨ x = usdt ∨ x = Usdc.usdcImpl) (m : Mv Tb r p b) (hT : x ∉ Tb) : x ∉ b.accessedAddresses :=
  fun h => f.warm x hx (((m.same x hT).warm).1 h)

/-! ## The push -/

/-- What coin `j`'s `transfer` writes. -/
noncomputable def paidStor (w : Jaune.State) (E : Adr) (j : Fin 3) (v : Nat) : Stor :=
  match j with
  | 0 => ((w.getStor dai).set (Dai.balSlot pool) ((w.getStor dai).get (Dai.balSlot pool) - Nat.toB256 v)).set
      (Dai.balSlot E) ((w.getStor dai).get (Dai.balSlot E) + Nat.toB256 v)
  | 1 => ((w.getStor usdc).set (Usdc.balSlot pool) ((w.getStor usdc).get (Usdc.balSlot pool) - Nat.toB256 v)).set
      (Usdc.balSlot E) ((w.getStor usdc).get (Usdc.balSlot E) + Nat.toB256 v)
  | 2 => usdtAfter (w.getStor usdt) (Usdt.balSlot pool) (Usdt.balSlot E) (Nat.toB256 v) (Usdt.feeOf (w.getStor usdt) (Nat.toB256 v))

/-- What coin `j`'s `transfer` charges inside. -/
noncomputable def payG (w : Jaune.State) (E : Adr) (j : Fin 3) (v : Nat) : Nat :=
  match j with
  | 0 => 7274 + debitG v + creditG (word w dai (Dai.balSlot E)) v
  | 1 => 17752 + debitG v + creditG (word w usdc (Usdc.balSlot E)) v
  | 2 => usdtPayG w E v

/-- The addresses coin `j`'s call touches. -/
def coinT : Fin 3 → List Adr
  | 0 => dai :: [dai]
  | 1 => usdc :: [usdc, Usdc.usdcImpl]
  | 2 => usdt :: [usdt]

/-- The length of coin `j`'s reply. -/
def replyLen : Fin 3 → Nat
  | 0 => 32
  | 1 => 32
  | 2 => 0

/-- Coin `k`'s address is a party. -/
theorem coinAt_party (k : Fin 3) : coinAt k = pool ∨ coinAt k = c3 ∨ coinAt k = dai ∨ coinAt k = usdc ∨ coinAt k = usdt := by
  match k with
  | 0 => exact Or.inr (Or.inr (Or.inl rfl))
  | 1 => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | 2 => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem coinAt_cold (k : Fin 3) : coinAt k = c3 ∨ coinAt k = dai ∨ coinAt k = usdc ∨ coinAt k = usdt ∨ coinAt k = Usdc.usdcImpl := by
  match k with
  | 0 => exact Or.inr (Or.inl rfl)
  | 1 => exact Or.inr (Or.inr (Or.inl rfl))
  | 2 => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

/-- **Coin `j`'s `transfer` at `exchange`'s push.** -/
theorem CoinStand.pay (f : CoinStand s p w E) (j : Fin 3) {b : Devm} {S : List B256} {M : Mem} {t : B256} {Tb : List Adr} {r : Int} {v : Nat}
    (htx : t.toAdr = coinAt j) (mv : Mv Tb r p b) (hT : ∀ x ∈ coinT j, x ∉ Tb) (hE0 : E ≠ 0)
    (hread : (M.read (0xb60 : B256).toNat (0x44 : B256).toNat).1 = transferSel ++ s.caller.toB256.toBytes ++ (Nat.toB256 v).toBytes)
    (hv : v < 2 ^ 256) (hle : v ≤ coinHeld w pool j) (hcr : CreditFits w E j (netOf w j v)) (hfee : j = 2 → UsdtFeeFits w v) :
    swapPushD s t j b S M = 2600 + ext (b.withGasLeft 0) S M 0xb60 0x44 0xc00 0x20 + payG w E j v ∧
      Mv (coinT j) ((4800 * empties (rawHeld w pool j) v : Nat) : Int) b (swapPushN s t j b S M) ∧
      Devm.getStor (swapPushN s t j b S M) (coinAt j) = paidStor w E j v ∧
      (swapPushN s t j b S M).returnData.length = replyLen j := by
  have hsw : (Nat.toB256 v).toNat = v := B256.toNat_toB256_of_lt hv
  match j with
  | 0 =>
    have hT0 : dai ∉ Tb := hT dai (by simp only [coinT, List.mem_cons, true_or])
    obtain ⟨hsite, hst⟩ := f.site (x := dai) htx (Or.inr (Or.inr (Or.inl rfl))) mv hT0
    have htx' : t.toAdr = dai := htx
    have hheld : coinHeld w pool 0 = word w dai (Dai.balSlot pool) := by
      unfold coinHeld; rw [ite_eq_right (by rintro ⟨h, -⟩; exact absurd h (by decide))]; rfl
    have hc' : word w dai (Dai.balSlot E) + v < 2 ^ 255 := hcr
    rw [hheld] at hle
    obtain ⟨c1, c2, c3'⟩ := dai_site (s := s) (b := b) (S := S) (M := M) (t := t) (ii := 0xb60) (oi := 0xc00) (V := Nat.toB256 v) hsite hread
      (by rw [f.target, f.caller]; exact Ne.symm (f.apart.poolEntry 0))
      (by rw [hst, f.target, hsw]; exact hle)
      (by rw [hst, f.caller, hsw]; show v + word w dai (Dai.balSlot E) < _; omega)
    simp only [hst, f.target, f.caller, hsw] at c1 c2 c3'
    rw [htx'] at c2 c3'
    refine ⟨?_, c2, c3', ?_⟩
    · show coinDebit Dai.xferG s t 0xb60 0x44 0xc00 b S M = _
      rw [c1, acc_cold (by rw [htx']; exact f.coldAddr (Or.inr (Or.inl rfl)) mv hT0)]
      rfl
    · rfl
  | 1 =>
    have hT0 : usdc ∉ Tb := hT usdc (by simp only [coinT, List.mem_cons, true_or])
    have hTi : Usdc.usdcImpl ∉ Tb := hT _ (by simp only [coinT, List.mem_cons, List.not_mem_nil, or_false, or_true])
    obtain ⟨hsite, hst⟩ := f.site (x := usdc) htx (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) mv hT0
    have htx' : t.toAdr = usdc := htx
    have hheld : coinHeld w pool 1 = Usdc.balanceBits ((w.getStor usdc).get (Usdc.balSlot pool)) := by
      unfold coinHeld; rw [ite_eq_left ⟨rfl, f.open'.usdcV22⟩]
    rw [hheld] at hle
    have hbw : Usdc.balanceBits ((w.getStor usdc).get (Usdc.balSlot pool)) ≤ word w usdc (Usdc.balSlot pool) := Nat.mod_le _ _
    have hc' : word w usdc (Usdc.balSlot E) + v < 2 ^ 255 := hcr
    have hpKI : UsdcLive.pKI = Usdc.implSlot := by decide +kernel
    have hI : ((w.getStor usdc).get UsdcLive.pKI).toAdr = Usdc.usdcImpl := by
      rw [hpKI, show (w.getStor usdc).get Usdc.implSlot = Usdc.usdcImpl.toB256 from f.open'.usdcV22, toAdr_toB256]
    have hE1 : ∀ x ∈ [Bytes.toB256 [1], Usdc.adminSlot, Usdc.implSlot], Usdc.balSlot E ≠ x := fun x hx e => f.apart.usdcE (by
      show Usdc.balSlot E ∈ _
      rw [e]; exact hx)
    obtain ⟨c1, c2, c3'⟩ := usdc_site (s := s) (b := b) (S := S) (M := M) (t := t) (ii := 0xb60) (oi := 0xc00) (V := Nat.toB256 v) hsite hread
      (by rw [hst, hI]; exact f.coldAddr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) mv hTi)
      (by rw [hst, hI, htx']; decide +kernel) (by decide +kernel) (by decide +kernel)
      (by rw [f.target]; decide +kernel)
      (by
        rw [f.caller, show UsdcLive.pKA = Usdc.adminSlot by decide +kernel, hpKI]
        exact ⟨hE1 _ (by simp only [List.mem_cons, true_or, or_true]), hE1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, or_true])⟩)
      (by rw [f.target]; decide +kernel) (by rw [f.caller]; exact Ne.symm (hE1 _ List.mem_cons_self))
      (by rw [f.target, f.caller]; exact Ne.symm (f.apart.poolEntry 1))
      (by rw [hst, f.target]; exact f.open'.usdcParties.1) (by rw [hst, f.caller]; exact f.open'.usdcParties.2)
      (by rw [hst, f.target, hsw]; show v ≤ word w usdc (Usdc.balSlot pool); omega)
      (by rw [hst, f.caller, hsw]; show v + word w usdc (Usdc.balSlot E) < _; omega)
    simp only [hst, hI, f.target, f.caller, hsw] at c1 c2 c3'
    rw [htx'] at c2 c3'
    refine ⟨?_, ?_, c3', ?_⟩
    · show coinDebit UsdcLive.xferG s t 0xb60 0x44 0xc00 b S M = _
      rw [c1, acc_cold (by rw [htx']; exact f.coldAddr (Or.inr (Or.inr (Or.inl rfl))) mv hT0)]
      rfl
    · exact c2
    · rfl
  | 2 =>
    have hT0 : usdt ∉ Tb := hT usdt (by simp only [coinT, List.mem_cons, true_or])
    obtain ⟨hsite, hst⟩ := f.site (x := usdt) htx (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) mv hT0
    have htx' : t.toAdr = usdt := htx
    have hheld : coinHeld w pool 2 = word w usdt (Usdt.balSlot pool) := by
      unfold coinHeld; rw [ite_eq_right (by rintro ⟨h, -⟩; exact absurd h (by decide))]; rfl
    rw [hheld] at hle
    obtain ⟨hff, hfo, hfl⟩ := hfee rfl
    have hfe := fee_word hv hff
    have hcr' : word w usdt (Usdt.balSlot E) + (v - usdtFee w v) < 2 ^ 255 := hcr
    have hco : word w usdt (Usdt.balSlot (Usdt.ownerOf (w.getStor usdt))) + usdtFee w v < 2 ^ 255 := hfo
    have hsub : (Nat.toB256 v - Usdt.feeOf (w.getStor usdt) (Nat.toB256 v)).toNat = v - usdtFee w v := by
      rw [B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, hsw, hfe]; exact hfl), hsw, hfe]
    have hgate : usdtRead pool.toB256 = usdtGateSlots := by decide +kernel
    obtain ⟨hE1, hE2⟩ := f.apart.usdtE
    obtain ⟨hO1, hO2⟩ := f.apart.usdtOwner
    obtain ⟨c1, c2, c3'⟩ := usdt_site (s := s) (b := b) (S := S) (M := M) (t := t) (ii := 0xb60) (oi := 0xc00) (V := Nat.toB256 v) hsite hread
      (by rw [f.target]; decide +kernel)
      (by rw [f.target]; decide +kernel)
      (by rw [f.target, f.caller, hgate]; exact hE1)
      (by rw [f.target, f.caller]; exact Ne.symm (f.apart.poolEntry 2))
      (by rw [hst, f.target, hsw]; exact hle)
      (by rw [hst, f.caller, hsub]; show _ + word w usdt (Usdt.balSlot E) < _; omega)
      (by
        intro _
        rw [hst, f.target, f.caller, hgate, ownerKey_eq]
        refine ⟨hO1, hO2, fun e => hE2 e.symm, ?_⟩
        rw [hfe]
        show _ + word w usdt (Usdt.balSlot (Usdt.ownerOf (w.getStor usdt))) < _
        omega)
    simp only [hst, f.target, f.caller, hsw, hsub, hfe, ownerKey_eq] at c1 c2 c3'
    rw [htx'] at c2 c3'
    have he61 : Usdt.e61G (Nat.toB256 v) = if v = 0 then 72 else 138 := by
      unfold Usdt.e61G
      by_cases h0 : v = 0
      · rw [ite_eq_left h0, ite_eq_left (by rw [h0]; rfl)]
      · rw [ite_eq_right h0, ite_eq_right (fun e => h0 (by rw [← hsw, e]; rfl))]
    have hcap := usdt_capped hv hff
    refine ⟨?_, c2, c3', ?_⟩
    · show coinDebit Usdt.xferG s t 0xb60 0x44 0xc00 b S M = _
      rw [c1, acc_cold (by rw [htx']; exact f.coldAddr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) mv hT0), he61]
      have hc' : (if Usdt.Capped (w.getStor usdt) (Nat.toB256 v) then 336 else 228) =
          (if word w usdt 4 < v * word w usdt 3 / 10000 then 336 else 228) := by
        by_cases hk : Usdt.Capped (w.getStor usdt) (Nat.toB256 v)
        · rw [ite_eq_left hk, ite_eq_left (hcap.1 hk)]
        · rw [ite_eq_right hk, ite_eq_right (fun h => hk (hcap.2 h))]
      have hf0 : (Usdt.feeOf (w.getStor usdt) (Nat.toB256 v) = 0) ↔ usdtFee w v = 0 := by
        rw [← hfe]
        exact ⟨fun e => by rw [e]; rfl, fun e => B256.toNat_inj _ _ e⟩
      rw [hc']
      show _ = _ + usdtPayG w E v
      unfold usdtPayG
      by_cases hz : usdtFee w v = 0
      · rw [ite_eq_left (hf0.2 hz), ite_eq_left hz]; rfl
      · rw [ite_eq_right (fun e => hz (hf0.1 e)), ite_eq_right hz]; rfl
    · show ((Usdt.xferPost _ _ 0).output).length = 0
      rw [xferPost_output]
      rfl

/-! ## The pulls -/

/-- `E` and the pool are different addresses, by their entries. -/
theorem CoinsApart.ne_pool (h : CoinsApart w E) : E ≠ pool := fun e => h.poolEntry 0 (by rw [e])

/-- DAI's or USDC's `transferFrom`, inside. -/
noncomputable def pullAG (w : Jaune.State) (E : Adr) (i : Fin 3) (v : Nat) : Nat :=
  match i with
  | 0 => 434 + daiAllowG (allowanceOf w E 0) v + debitG v + creditG (rawHeld w pool 0) v
  | _ => 20749 + debitG v + debitG v + creditG (rawHeld w pool 1) v

/-- What DAI's or USDC's `transferFrom` empties. -/
def pullAR (w : Jaune.State) (E : Adr) (i : Fin 3) (v : Nat) : Nat :=
  match i with
  | 0 => allowEmpties (allowanceOf w E 0) v + empties (rawHeld w E 0) v
  | _ => empties (allowanceOf w E 1) v + empties (rawHeld w E 1) v

/-- What DAI's or USDC's `transferFrom` writes. -/
noncomputable def pulledStor (w : Jaune.State) (E : Adr) (i : Fin 3) (v : Nat) : Stor :=
  match i with
  | 0 => daiPulled (w.getStor dai) (Dai.balSlot E) (Dai.balSlot pool) (Dai.allowSlot E pool) (Nat.toB256 v)
  | _ => (((w.getStor usdc).set (Usdc.balSlot E) ((w.getStor usdc).get (Usdc.balSlot E) - Nat.toB256 v)).set
      (Usdc.balSlot pool) ((w.getStor usdc).get (Usdc.balSlot pool) + Nat.toB256 v)).set
      (Usdc.allowSlot E pool) ((w.getStor usdc).get (Usdc.allowSlot E pool) - Nat.toB256 v)

theorem usdc_impl_word (f : CoinStand s p w E) : ((w.getStor usdc).get UsdcLive.pKI).toAdr = Usdc.usdcImpl := by
  rw [show UsdcLive.pKI = Usdc.implSlot by decide +kernel, show (w.getStor usdc).get Usdc.implSlot = Usdc.usdcImpl.toB256 from f.open'.usdcV22, toAdr_toB256]

/-- **DAI's or USDC's `transferFrom` at `exchange`'s pull.** -/
theorem CoinStand.pullA (f : CoinStand s p w E) (hap : SwapApart w E) (i : Fin 3) (hi : i ≠ 2) {b : Devm} {S : List B256} {M : Mem} {t : B256} {Tb : List Adr} {r : Int} {v : Nat}
    (htx : t.toAdr = coinAt i) (mv : Mv Tb r p b) (hT : ∀ x ∈ coinT i, x ∉ Tb)
    (hread : (M.read (0x600 : B256).toNat (0x64 : B256).toNat).1 = transferFromSel ++ s.caller.toB256.toBytes ++ s.currentTarget.toB256.toBytes ++ (Nat.toB256 v).toBytes)
    (hv : v < 2 ^ 256) (hle : v ≤ coinHeld w E i) (hal : v ≤ allowanceOf w E i) (hcr : CreditFits w pool i v) :
    swapPullD s t i b S M = 2600 + ext (b.withGasLeft 0) S M 0x600 0x64 0x6c0 0x20 + pullAG w E i v ∧
      Mv (coinT i) ((4800 * pullAR w E i v : Nat) : Int) b (swapPullN s t i b S M) ∧
      Devm.getStor (swapPullN s t i b S M) (coinAt i) = pulledStor w E i v ∧
      (swapPullN s t i b S M).returnData.length = 32 := by
  have hsw : (Nat.toB256 v).toNat = v := B256.toNat_toB256_of_lt hv
  have hEp := CoinsApart.ne_pool f.apart
  match i with
  | 2 => exact absurd rfl hi
  | 0 =>
    have hT0 : dai ∉ Tb := hT dai (by simp only [coinT, List.mem_cons, true_or])
    obtain ⟨hsite, hst⟩ := f.site (x := dai) htx (Or.inr (Or.inr (Or.inl rfl))) mv hT0
    have htx' : t.toAdr = dai := htx
    have hheld : coinHeld w E 0 = word w dai (Dai.balSlot E) := by
      unfold coinHeld; rw [ite_eq_right (by rintro ⟨h, -⟩; exact absurd h (by decide))]; rfl
    rw [hheld] at hle
    have hc' : word w dai (Dai.balSlot pool) + v < 2 ^ 255 := hcr
    have hA0 := hap.allow 0
    obtain ⟨c1, c2, c3'⟩ := dai_pull_site (s := s) (b := b) (S := S) (M := M) (t := t) (ii := 0x600) (oi := 0x6c0) (V := Nat.toB256 v) hsite hread
      (by rw [f.target, f.caller]; exact hEp)
      (by rw [f.target, f.caller]; exact f.apart.poolEntry 0)
      (by rw [f.target, f.caller]; exact hA0.1)
      (by rw [f.target, f.caller]; exact hA0.2)
      (by rw [hst, f.caller, hsw]; exact hle)
      (by rw [hst, f.target, f.caller, hsw]; exact fun _ => hal)
      (by rw [hst, f.target, hsw]; show v + word w dai (Dai.balSlot pool) < _; omega)
    simp only [hst, f.target, f.caller, hsw] at c1 c2 c3'
    rw [htx'] at c2 c3'
    refine ⟨?_, c2, c3', ?_⟩
    · show coinDebit Dai.pullG s t 0x600 0x64 0x6c0 b S M = _
      rw [c1, acc_cold (by rw [htx']; exact f.coldAddr (Or.inr (Or.inl rfl)) mv hT0)]
      rfl
    · rfl
  | 1 =>
    have hT0 : usdc ∉ Tb := hT usdc (by simp only [coinT, List.mem_cons, true_or])
    have hTi : Usdc.usdcImpl ∉ Tb := hT _ (by simp only [coinT, List.mem_cons, List.not_mem_nil, or_false, or_true])
    obtain ⟨hsite, hst⟩ := f.site (x := usdc) htx (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) mv hT0
    have htx' : t.toAdr = usdc := htx
    have hheld : coinHeld w E 1 = Usdc.balanceBits ((w.getStor usdc).get (Usdc.balSlot E)) := by
      unfold coinHeld; rw [ite_eq_left ⟨rfl, f.open'.usdcV22⟩]
    rw [hheld] at hle
    have hbw : Usdc.balanceBits ((w.getStor usdc).get (Usdc.balSlot E)) ≤ word w usdc (Usdc.balSlot E) := Nat.mod_le _ _
    have hc' : word w usdc (Usdc.balSlot pool) + v < 2 ^ 255 := hcr
    have hal' : v ≤ word w usdc (Usdc.allowSlot E pool) := hal
    have hI := usdc_impl_word f
    have hE1 : ∀ x ∈ [Bytes.toB256 [1], Usdc.adminSlot, Usdc.implSlot], Usdc.balSlot E ≠ x := fun x hx e => f.apart.usdcE (by
      show Usdc.balSlot E ∈ _
      rw [e]; exact hx)
    have hA1 : ∀ x ∈ [Bytes.toB256 [1], Usdc.adminSlot, Usdc.implSlot], Usdc.allowSlot E pool ≠ x := fun x hx e => hap.allowUsdc (by
      show Usdc.allowSlot E pool ∈ _
      rw [e]; exact hx)
    have hpKI : UsdcLive.pKI = Usdc.implSlot := by decide +kernel
    have hpKA : UsdcLive.pKA = Usdc.adminSlot := by decide +kernel
    have hmemA : Usdc.adminSlot ∈ [Bytes.toB256 [1], Usdc.adminSlot, Usdc.implSlot] := by
      simp only [List.mem_cons, true_or, or_true]
    have hmemI : Usdc.implSlot ∈ [Bytes.toB256 [1], Usdc.adminSlot, Usdc.implSlot] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_true]
    obtain ⟨c1, c2, c3'⟩ := usdc_pull_site (s := s) (b := b) (S := S) (M := M) (t := t) (ii := 0x600) (oi := 0x6c0) (V := Nat.toB256 v) hsite hread
      (by rw [hst, hI]; exact f.coldAddr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) mv hTi)
      (by rw [hst, hI, htx']; decide +kernel) (by decide +kernel) (by decide +kernel)
      (by rw [f.caller, hpKA, hpKI]; exact ⟨hE1 _ hmemA, hE1 _ hmemI⟩)
      (by rw [f.target]; decide +kernel)
      (by rw [f.target, f.caller, hpKA, hpKI]; exact ⟨hA1 _ hmemA, hA1 _ hmemI⟩)
      (by rw [f.caller]; exact Ne.symm (hE1 _ List.mem_cons_self))
      (by rw [f.target]; decide +kernel)
      (by rw [f.target, f.caller]; exact Ne.symm (hA1 _ List.mem_cons_self))
      (by rw [f.target, f.caller]; exact f.apart.poolEntry 1)
      (by rw [f.target, f.caller]; exact (hap.allow 1).1)
      (by rw [f.target, f.caller]; exact (hap.allow 1).2)
      (by rw [hst, f.caller]; exact f.open'.usdcParties.2) (by rw [hst, f.target]; exact f.open'.usdcParties.1)
      (by rw [hst, f.caller, hsw]; show v ≤ word w usdc (Usdc.balSlot E); omega)
      (by rw [hst, f.target, hsw]; show v + word w usdc (Usdc.balSlot pool) < _; omega)
      (by rw [hst, f.target, f.caller, hsw]; exact hal')
    simp only [hst, hI, f.target, f.caller, hsw] at c1 c2 c3'
    rw [htx'] at c2 c3'
    refine ⟨?_, ?_, c3', ?_⟩
    · show coinDebit UsdcLive.pullG s t 0x600 0x64 0x6c0 b S M = _
      rw [c1, acc_cold (by rw [htx']; exact f.coldAddr (Or.inr (Or.inr (Or.inl rfl))) mv hT0)]
      rfl
    · exact c2
    · rfl

/-- USDT's `transferFrom`, inside. -/
noncomputable def usdtPullG (w : Jaune.State) (E : Adr) (v : Nat) : Nat :=
  11545 + (if v = 0 then 72 else 138) + (if word w usdt 4 < v * word w usdt 3 / 10000 then 336 else 228) +
    usdtAllowG (allowanceOf w E 2) v +
    ((if usdtFee w v = 0 then 2593 else 7238 + creditG (word w usdt (Usdt.balSlot (Usdt.ownerOf (w.getStor usdt)))) (usdtFee w v)) + 2200 + debitG v +
      creditG (rawHeld w pool 2) (v - usdtFee w v))

/-- USDT's blacklist word of `a`, as its walk computes it. -/
theorem listKey_eq (a : Adr) : listKey a = usdtListWord a := by
  unfold listKey usdtListWord
  simp only [ff20_and_word, toAdr_toB256]

/-- **USDT's `transferFrom` at `exchange`'s pull**, after the pool's first `balanceOf`. -/
theorem CoinStand.pullT (f : CoinStand s p w E) (hap : SwapApart w E) {b : Devm} {S : List B256} {M : Mem} {t : B256}
    {Tb : List Adr} {r : Int} {v : Nat}
    (htx : t.toAdr = coinAt 2) (mv : Mv Tb r p b) (hA : At usdt [Usdt.balSlot pool, Bytes.toB256 [10]] (w.getStor usdt) b)
    (hwarm : usdt ∈ b.accessedAddresses)
    (hread : (M.read (0x600 : B256).toNat (0x64 : B256).toNat).1 = transferFromSel ++ s.caller.toB256.toBytes ++ s.currentTarget.toB256.toBytes ++ (Nat.toB256 v).toBytes)
    (hv : v < 2 ^ 256) (hle : v ≤ coinHeld w E 2) (hal : v ≤ allowanceOf w E 2) (hcr : CreditFits w pool 2 (netOf w 2 v)) (hfee : UsdtFeeFits w v) :
    swapPullD s t 2 b S M = 100 + ext (b.withGasLeft 0) S M 0x600 0x64 0x6c0 0x20 + usdtPullG w E v ∧
      Mv (coinT 2) ((4800 * (allowEmpties (allowanceOf w E 2) v + empties (rawHeld w E 2) v) : Nat) : Int) b (swapPullN s t 2 b S M) ∧
      Devm.getStor (swapPullN s t 2 b S M) usdt = usdtAfter (usdtSpent (w.getStor usdt) (Usdt.allowSlot E pool) (Nat.toB256 v))
        (Usdt.balSlot E) (Usdt.balSlot pool) (Nat.toB256 v) (Usdt.feeOf (w.getStor usdt) (Nat.toB256 v)) ∧
      (swapPullN s t 2 b S M).returnData.length = 0 := by
  have hsw : (Nat.toB256 v).toNat = v := B256.toNat_toB256_of_lt hv
  have htx' : t.toAdr = usdt := htx
  have hst : b.getStor t.toAdr = w.getStor usdt := by rw [htx']; exact hA.stor
  have hheld : coinHeld w E 2 = word w usdt (Usdt.balSlot E) := by
    unfold coinHeld; rw [ite_eq_right (by rintro ⟨h, -⟩; exact absurd h (by decide))]; rfl
  rw [hheld] at hle
  have hal' : v ≤ word w usdt (Usdt.allowSlot E pool) := hal
  obtain ⟨hff, hfo, hfl⟩ := hfee
  have hfe := fee_word hv hff
  have hcr' : word w usdt (Usdt.balSlot pool) + (v - usdtFee w v) < 2 ^ 255 := hcr
  have hco : word w usdt (Usdt.balSlot (Usdt.ownerOf (w.getStor usdt))) + usdtFee w v < 2 ^ 255 := hfo
  have hsub : (Nat.toB256 v - Usdt.feeOf (w.getStor usdt) (Nat.toB256 v)).toNat = v - usdtFee w v := by
    rw [B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, hsw, hfe]; exact hfl), hsw, hfe]
  obtain ⟨hE1, hE2⟩ := f.apart.usdtE
  obtain ⟨hO1, hO2⟩ := f.apart.usdtOwner
  have hLst := hap.usdtList
  have hAl := hap.allowUsdt
  simp only [usdtGateSlots, List.mem_cons, List.not_mem_nil, or_false, not_or] at hE1 hO1 hLst hAl
  obtain ⟨e4, e3, e10, -, e0⟩ := hE1
  obtain ⟨o4, o3, o10, -, o0⟩ := hO1
  obtain ⟨l0, l3, l4, l10, lE, lP, lO⟩ := hLst
  obtain ⟨a0, a3, a4, a10, aL, aO⟩ := hAl
  have hread0 : usdtRead (s.caller.toB256) = [Bytes.toB256 [4], Bytes.toB256 [3], Bytes.toB256 [10], usdtListWord E, Bytes.toB256 [0]] := by
    rw [f.caller, ← listKey_eq]
  have hpool : Usdt.balSlot pool ≠ Bytes.toB256 [4] ∧ Usdt.balSlot pool ≠ Bytes.toB256 [3] ∧ Usdt.balSlot pool ≠ Bytes.toB256 [10] ∧
      Usdt.balSlot pool ≠ Bytes.toB256 [0] := by decide +kernel
  obtain ⟨c1, c2, c3'⟩ := usdt_pull_site (s := s) (b := b) (S := S) (M := M) (t := t) (ii := 0x600) (oi := 0x6c0) (V := Nat.toB256 v) (σ := w.getStor usdt)
    f.fork ((mv.clean f.clean)) hst (by rw [htx']; exact (f.stor usdt (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).2)
    (by rw [htx', f.target]; exact hA) hread
    (by
      rw [hread0, f.caller]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨e4, e3, e10, Ne.symm lE, e0⟩)
    (by
      rw [hread0, f.target]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hpool.1, hpool.2.1, hpool.2.2.1, Ne.symm lP, hpool.2.2.2⟩)
    (by
      rw [hread0, f.caller, f.target]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨a4, a3, a10, aL, a0⟩)
    (by rw [f.caller, f.target]; exact f.apart.poolEntry 2)
    (by rw [f.caller, f.target]; exact (hap.allow 2).1)
    (by rw [f.caller, f.target]; exact (hap.allow 2).2)
    (by rw [f.caller, listKey_eq]; exact ⟨Ne.symm l0, l10, l3, l4⟩)
    (by rw [f.caller, hsw]; exact hle)
    (by rw [f.caller, f.target, hsw]; exact fun _ => hal')
    (by rw [hsub, f.target]; show _ + word w usdt (Usdt.balSlot pool) < _; omega)
    (by
      intro _
      rw [hread0, f.caller, f.target, ownerKey_eq, hfe]
      refine ⟨?_, Ne.symm hE2, hO2, Ne.symm aO, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨o4, o3, o10, Ne.symm lO, o0⟩
      · show _ + word w usdt (Usdt.balSlot (Usdt.ownerOf (w.getStor usdt))) < _
        omega)
  simp only [f.target, f.caller, hsw, hsub, hfe, ownerKey_eq] at c1 c2 c3'
  rw [htx'] at c2 c3'
  have he61 : Usdt.e61G (Nat.toB256 v) = if v = 0 then 72 else 138 := by
    unfold Usdt.e61G
    by_cases h0 : v = 0
    · rw [ite_eq_left h0, ite_eq_left (by rw [h0]; rfl)]
    · rw [ite_eq_right h0, ite_eq_right (fun e => h0 (by rw [← hsw, e]; rfl))]
  have hcap := usdt_capped hv hff
  refine ⟨?_, c2, c3', ?_⟩
  · show coinDebit Usdt.pullG s t 0x600 0x64 0x6c0 b S M = _
    rw [c1, acc_warm (by rw [htx']; exact hwarm), he61]
    have hc' : (if Usdt.Capped (w.getStor usdt) (Nat.toB256 v) then 336 else 228) =
        (if word w usdt 4 < v * word w usdt 3 / 10000 then 336 else 228) := by
      by_cases hk : Usdt.Capped (w.getStor usdt) (Nat.toB256 v)
      · rw [ite_eq_left hk, ite_eq_left (hcap.1 hk)]
      · rw [ite_eq_right hk, ite_eq_right (fun h => hk (hcap.2 h))]
    have hf0 : (Usdt.feeOf (w.getStor usdt) (Nat.toB256 v) = 0) ↔ usdtFee w v = 0 := by
      rw [← hfe]
      exact ⟨fun e => by rw [e]; rfl, fun e => B256.toNat_inj _ _ e⟩
    rw [hc']
    show _ = _ + usdtPullG w E v
    unfold usdtPullG
    by_cases hz : usdtFee w v = 0
    · rw [ite_eq_left (hf0.2 hz), ite_eq_left hz]; rfl
    · rw [ite_eq_right (fun e => hz (hf0.1 e)), ite_eq_right hz]; rfl
  · show ((Usdt.pullP _ _ 0).output).length = 0
    rw [pullP_output]
    rfl

end Stand

end Blanc.Composition.Curve3PoolPublic
