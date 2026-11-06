import Blanc.Composition.Curve3PoolExitSites
import Blanc.Composition.Curve3PoolExitWorks

/-!
# `remove_liquidity`'s canonical chain from a cold start

The frame's own storage steps in the canonical schedule: `rlPrologue_view` up to the supply read, `iter_view` for one
iteration up to its `transfer`, `rawTail` and the lock's release after the burn.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.Lift.AccumulatedWalk Blanc.Lift.Curve3Pool

/-- `Mv`'s view of a party the step leaves alone. -/
theorem At.ofMv {x : Adr} {K : List B256} {σ : Stor} {T : List Adr} {r : Int} {b b' : Devm} (h : At x K σ b)
    (m : Mv T r b b') (hx : x ∉ T) : At x K σ b' := h.ofSame (m.same x hx)

variable {s : Sevm} {pre n : Devm} {T : B256} {P : RLExactCalls} {K : List B256} {σ : Stor}

/-- The lock's literal. -/
abbrev lockW : B256 := Bytes.toB256 [0xff, 0xff, 0xff]

/-- **The prologue**: the lock read and set, the token slot read. -/
theorem rlPrologue_view (hA : At s.currentTarget [] σ pre) (hc : Clean pre)
    (hor : (getOrigAcct s s.currentTarget).stor = σ) (hg : s.benvStat.rules.gas.storageClearRefund = 4800)
    (hlock : σ.get lockW = 0) (h5 : Bytes.toB256 [5] ≠ lockW) :
    sloadCost s pre lockW + sstoreCost s (afterSload s pre lockW) lockW (Bytes.toB256 [1]) +
        sloadCost s (afterSstore s (afterSload s pre lockW) lockW (Bytes.toB256 [1])) (Bytes.toB256 [5]) = 24200 ∧
      At s.currentTarget [Bytes.toB256 [5], lockW, lockW] (σ.set lockW (Bytes.toB256 [1])) (rlSupplyBase s pre) ∧
      Mv [s.currentTarget] 0 pre (rlSupplyBase s pre) := by
  have a1 := hA.sload lockW
  have m1 := mv_afterSload s pre lockW
  have c1 := m1.clean hc
  have hv : (afterSload s pre lockW).getOrigStorVal s s.currentTarget lockW = 0 := by
    rw [c1.orig, hor, hlock]
  have hcu : σ.get lockW = 0 := hlock
  have m2 : Mv [s.currentTarget] 0 (afterSload s pre lockW) (afterSstore s (afterSload s pre lockW) lockW (Bytes.toB256 [1])) :=
    mv_afterSstore s _ _ _ (by rw [hv, a1.val, hcu, first_refund, ite_eq_right (fun e => e.1 rfl)])
  have a2 := a1.sstore lockW (Bytes.toB256 [1])
  have a3 := a2.sload (Bytes.toB256 [5])
  have m3 := mv_afterSload s (afterSstore s (afterSload s pre lockW) lockW (Bytes.toB256 [1])) (Bytes.toB256 [5])
  refine ⟨?_, a3, ((m1.trans m2).trans m3).one (fun a ha => by
    simpa only [List.mem_append, List.mem_singleton, or_self] using ha) rfl⟩
  rw [hA.sloadCost_cold List.not_mem_nil, a1.sstoreCost_warm List.mem_cons_self, hv, hcu, first_value,
    a2.sloadCost_cold (by simp only [List.mem_cons, List.not_mem_nil, or_false, or_self]; exact h5)]
  rfl

/-- **One iteration's storage step**, up to its `transfer`: `balances[i]` debited, `coins[i]` read. -/
theorem iter_view (i : Nat) (m : Mem) (hA : At s.currentTarget K σ n) (hc : Clean n)
    (hor : (getOrigAcct s s.currentTarget).stor.get (rlKey i) = rlB s pre i)
    (hcur : σ.get (rlKey i) = rlB s pre i)
    (hk : rlKey i ∉ K) (hck : coinsBase + Nat.toB256 i ∉ K) (hne : rlKey i ≠ coinsBase + Nat.toB256 i)
    (hle : (rlV s pre T i).toNat ≤ (rlB s pre i).toNat) (hg : s.benvStat.rules.gas.storageClearRefund = 4800) :
    rlIterStorageCost s pre T i n m = 4300 + debitG (rlV s pre T i).toNat ∧
      At s.currentTarget ((coinsBase + Nat.toB256 i) :: rlKey i :: rlKey i :: rlKey i :: K)
        (σ.set (rlKey i) (rlB s pre i - rlV s pre T i)) (rlPushBase s pre T i n m) ∧
      Mv [s.currentTarget] ((4800 * empties (rlB s pre i).toNat (rlV s pre T i).toNat : Nat) : Int) n (rlPushBase s pre T i n m) := by
  have a1 := hA.sload (rlKey i)
  have a2 := a1.sload (rlKey i)
  have m1 := (mv_afterSload s n (rlKey i)).trans (mv_afterSload s _ (rlKey i))
  have c2 := m1.clean hc
  have f : Fresh s (afterSload s (afterSload s n (rlKey i)) (rlKey i)) (rlKey i) (rlB s pre i) :=
    ⟨c2, hor, by rw [a2.val, hcur]⟩
  have m3 := mv_debit (v := rlV s pre T i) f hle hg
  have a3 := a2.sstore (rlKey i) (rlB s pre i - rlV s pre T i)
  have c3 := m3.clean c2
  have hbase : rlS1Base s pre T i n = afterSstore s (afterSload s (afterSload s n (rlKey i)) (rlKey i)) (rlKey i)
      (rlB s pre i - rlV s pre T i) := rfl
  have mId : Mv ([] ++ []) (0 + 0) (rlS1Base s pre T i n) (rlS2Base s pre T i n m) := by
    unfold rlS2Base rlS2Next rlS2Base1
    exact (mv_identity ..).trans (mv_identity ..)
  rw [← hbase] at m3 a3 c3
  have a4 : At s.currentTarget (rlKey i :: rlKey i :: rlKey i :: K) (σ.set (rlKey i) (rlB s pre i - rlV s pre T i))
      (rlS2Base s pre T i n m) := a3.ofMv mId (by simp only [List.append_nil, List.not_mem_nil, not_false_eq_true])
  have m5 := mv_afterSload s (rlS2Base s pre T i n m) (coinsBase + Nat.toB256 i)
  refine ⟨?_, a4.sload _, ?_⟩
  · unfold rlIterStorageCost
    rw [hA.sloadCost_cold hk, a1.sloadCost_warm List.mem_cons_self, cost_debit f a2 List.mem_cons_self hle,
      a4.sloadCost_cold (by
        simp only [List.mem_cons, not_or]
        exact ⟨fun e => hne e.symm, fun e => hne e.symm, fun e => hne e.symm, hck⟩)]
    show 2100 + 100 + _ + 2100 = _
    omega
  · have := ((m1.trans m3).trans mId).trans m5
    exact this.one (fun a ha => by
      simpa only [List.append_nil, List.mem_append, List.mem_singleton, or_self] using ha) (by
      simp only [Int.zero_add, Int.add_zero])

section Windows

open Blanc.Composition.Curve3PoolCalleeLive

variable {b : Devm} {S : List B256} {M : Mem}

/-- Two windows' expansion over a memory of known size. -/
theorem ext_size (ii is oi os : B256) {n : Nat} (h : M.size = n) :
    ext b S M ii is oi os =
      calculateMemoryGasCost (memExtsSize n [⟨ii.toNat, is.toNat⟩, ⟨oi.toNat, os.toNat⟩]) - calculateMemoryGasCost n := by
  subst h
  rfl

theorem ext_supply (h : M.size = 0x180) : ext b S M 0x17c 4 0x1c0 0x20 = 9 := by
  rw [ext_size _ _ _ _ h]; decide

theorem ext_push_grow (h : M.size = 0x580) : ext b S M 0x520 0x44 0x5c0 0x20 = 10 := by
  rw [ext_size _ _ _ _ h]; decide

theorem ext_push_flat (h : M.size = 0x5e0) : ext b S M 0x520 0x44 0x5c0 0x20 = 0 := by
  rw [ext_size _ _ _ _ h]; decide

theorem ext_burn (h : M.size = 0x660) : ext b S M 0x61c 0x44 0x6a0 0x20 = 9 := by
  rw [ext_size _ _ _ _ h]; decide

theorem acc_cold {t : B256} (h : t.toAdr ∉ b.accessedAddresses) : acc (b.withGasLeft 0) t = 2600 := by
  unfold acc accessCost
  exact (ite_eq_right h : (if t.toAdr ∈ b.accessedAddresses then gasWarmAccess else gasColdAccountAccess) = gasColdAccountAccess).trans rfl

theorem acc_warm {t : B256} (h : t.toAdr ∈ b.accessedAddresses) : acc (b.withGasLeft 0) t = 100 := by
  unfold acc accessCost
  exact (ite_eq_left h : (if t.toAdr ∈ b.accessedAddresses then gasWarmAccess else gasColdAccountAccess) = gasWarmAccess).trans rfl

end Windows

/-! ## The frame's standing facts -/

open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.Curve3PoolCalleeExactProfiles Blanc.Composition.Curve3PoolCoinExactKit
open Blanc.Composition.Curve3Pool3CrvExactAssembly Blanc.Composition.Curve3Pool3CrvLiteralWitness
open Blanc.Composition.Curve3Pool3CrvInstance (coinOf tokOf)

/-- What the canonical chain's evaluation stands on, at a message's entry. -/
structure ExitFrame (msg : Msg) (w : Jaune.State) (E : Adr) (a : Nat) (T : B256) : Prop where
  fork : CoveredFork (initSevm msg).benvStat.fork
  static : (initSevm msg).isStatic = false
  target : (initSevm msg).currentTarget = pool
  caller : (initSevm msg).caller = E
  keysCold : ∀ k, k ∉ (initDevm msg).accessedStorageKeys
  clean : Clean (initDevm msg)
  stor : ∀ x, x = pool ∨ x = c3 ∨ x = dai ∨ x = usdc ∨ x = usdt →
    (initDevm msg).getStor x = w.getStor x ∧ (getOrigAcct (initSevm msg) x).stor = w.getStor x
  warm : ∀ x, x = c3 ∨ x = dai ∨ x = usdc ∨ x = usdt ∨ x = Usdc.usdcImpl → x ∉ (initDevm msg).accessedAddresses
  coins : ∀ k : Fin 3, (Curve3Pool.coinAt ((initDevm msg).getStor (initSevm msg).currentTarget) k.val).toAdr = Curve3PoolPublic.coinAt k
  token : (tokW (initSevm msg) (initDevm msg)).toAdr = c3
  lock : ((initDevm msg).getStor (initSevm msg).currentTarget).get lockW = 0
  amount : rlAmt (initSevm msg) = Nat.toB256 a
  sharesW : ∀ k : Fin 3, rlV (initSevm msg) (initDevm msg) T k.val = Nat.toB256 (share w a k)
  supplyW : (w.getStor c3).get Curve3Crv.vySupplySlot = T
  apart : ExitApart w E
  open' : CoinsOpen w E
  backed : PoolBacked w
  holds : a ≤ shares w E ∧ a ≤ supply w ∧ 0 < supply w
  fits : ∀ k, CreditFits w E k (netOf w k (share w a k))
  feeFits : UsdtFeeFits w (share w a 2)
  minter : (w.getStor c3).get Curve3Crv.vyMinterSlot = pool.toB256

section Chain

variable {msg : Msg} {w : Jaune.State} {E : Adr} {a : Nat} {T : B256}

/-- A party the chain has left alone is as the entry has it: cold, at the moment's storage. -/
theorem ExitFrame.party (f : ExitFrame msg w E a T) {x : Adr} (hx : x = pool ∨ x = c3 ∨ x = dai ∨ x = usdc ∨ x = usdt)
    {Tl : List Adr} {r : Int} {n : Devm} (m : Mv Tl r (initDevm msg) n) (hT : x ∉ Tl) : At x [] (w.getStor x) n :=
  (At.mk (fun k => ⟨fun h => absurd h (f.keysCold _), fun h => absurd h List.not_mem_nil⟩) (f.stor x hx).1).ofMv m hT

/-- **The prologue and the supply read.** -/
theorem stage_supply (f : ExitFrame msg w E a T) :
    Mv (Curve3PoolPublic.pool :: c3 :: [c3]) 0 (initDevm msg) (rlHead0 (initSevm msg) (initDevm msg) (exitCalls msg)) ∧
      At (initSevm msg).currentTarget [Bytes.toB256 [5], lockW, lockW]
        (((initDevm msg).getStor (initSevm msg).currentTarget).set lockW (Bytes.toB256 [1]))
        (rlHead0 (initSevm msg) (initDevm msg) (exitCalls msg)) ∧
      At c3 [Curve3Crv.vySupplySlot] (w.getStor c3) (rlHead0 (initSevm msg) (initDevm msg) (exitCalls msg)) ∧
      c3 ∈ (rlHead0 (initSevm msg) (initDevm msg) (exitCalls msg)).accessedAddresses ∧
      (exitCalls msg).supplyDebit (rlSupplyBase (initSevm msg) (initDevm msg)) [] (rlSupplyMem (initSevm msg)) = 4929 ∧
      sloadCost (initSevm msg) (initDevm msg) lockW + sstoreCost (initSevm msg) (afterSload (initSevm msg) (initDevm msg) lockW) lockW (Bytes.toB256 [1]) +
        sloadCost (initSevm msg) (afterSstore (initSevm msg) (afterSload (initSevm msg) (initDevm msg) lockW) lockW (Bytes.toB256 [1])) (Bytes.toB256 [5]) = 24200 := by
  have hA0 : At (initSevm msg).currentTarget [] ((initDevm msg).getStor (initSevm msg).currentTarget) (initDevm msg) :=
    ⟨fun k => ⟨fun h => absurd h (f.keysCold _), fun h => absurd h List.not_mem_nil⟩, rfl⟩
  have hx : (initSevm msg).currentTarget = pool ∨ (initSevm msg).currentTarget = c3 ∨ (initSevm msg).currentTarget = dai ∨
      (initSevm msg).currentTarget = usdc ∨ (initSevm msg).currentTarget = usdt := Or.inl f.target
  obtain ⟨hcost, a1, m1⟩ := rlPrologue_view hA0 f.clean ((f.stor _ hx).2.trans (f.stor _ hx).1.symm)
    (CoveredFork.rules_storageClearRefund f.fork) f.lock (by decide)
  rw [f.target] at m1
  have hAc := f.party (x := c3) (Or.inr (Or.inl rfl)) m1 (by decide)
  have ht := f.token
  obtain ⟨t, htd⟩ : ∃ t, t = tokW (initSevm msg) (initDevm msg) := ⟨_, rfl⟩
  rw [← htd] at ht
  obtain ⟨hb, hm, ha, haw⟩ := supply_site (s := initSevm msg) (t := t) (b := rlSupplyBase (initSevm msg) (initDevm msg)) (S := [])
    (M := rlSupplyMem (initSevm msg)) (ii := 0x17c) (oi := 0x1c0) f.fork (m1.clean f.clean) (σ := w.getStor c3) (by rw [ht]; exact hAc)
  rw [ht] at hm ha haw
  have hHead : rlHead0 (initSevm msg) (initDevm msg) (exitCalls msg) =
      supplyNext (initSevm msg) t 0x17c 0x1c0 (rlSupplyBase (initSevm msg) (initDevm msg)) [] (rlSupplyMem (initSevm msg)) := by
    rw [htd]; rfl
  have hDebit : (exitCalls msg).supplyDebit (rlSupplyBase (initSevm msg) (initDevm msg)) [] (rlSupplyMem (initSevm msg)) =
      supplyDebit (initSevm msg) t 0x17c 0x1c0 (rlSupplyBase (initSevm msg) (initDevm msg)) [] (rlSupplyMem (initSevm msg)) := by
    rw [htd]; rfl
  refine ⟨?_, ?_, ?_, by rw [hHead]; exact haw, ?_, hcost⟩
  · rw [hHead]
    exact (m1.trans hm)
  · rw [hHead]
    exact a1.ofMv hm (by rw [f.target]; decide)
  · rw [hHead]
    exact ha
  · rw [hDebit]
    unfold supplyDebit
    rw [hb]
    have hw : c3 ∉ (rlSupplyBase (initSevm msg) (initDevm msg)).accessedAddresses := fun h =>
      f.warm c3 (Or.inl rfl) (((m1.same c3 (by decide)).warm).1 h)
    have hsz : (rlSupplyMem (initSevm msg)).size = 0x180 := by
      unfold rlSupplyMem
      rw [Mem.size_write_word_at, vyMem_empty_size]
      decide
    rw [acc_cold (by rw [ht]; exact hw), ext_supply hsz, show Curve3Crv.dispatchGas 2 = 186 from rfl]

/-- The pool's storage at the entry. -/
theorem ExitFrame.poolStor (f : ExitFrame msg w E a T) : (initDevm msg).getStor (initSevm msg).currentTarget = w.getStor pool ∧
    (getOrigAcct (initSevm msg) (initSevm msg).currentTarget).stor = w.getStor pool := by
  rw [f.target]; exact f.stor pool (Or.inl rfl)

/-- The share as a word, and the books it comes from. -/
theorem ExitFrame.shareFacts (f : ExitFrame msg w E a T) (k : Fin 3) :
    (rlV (initSevm msg) (initDevm msg) T k.val).toNat = share w a k ∧
      (rlB (initSevm msg) (initDevm msg) k.val).toNat = recorded w k ∧
      share w a k ≤ recorded w k := by
  have h := f.sharesW k
  rw [h, share_word f.holds.2.2 f.holds.2.1 k]
  refine ⟨rfl, ?_, share_le f.holds.2.2 f.holds.2.1 k⟩
  show ((((initDevm msg).getStor (initSevm msg).currentTarget).get (rlKey k.val))).toNat = _
  rw [f.poolStor.1]
  rfl

/-- The iteration's step on the pool's own storage. -/
theorem ExitFrame.iter (f : ExitFrame msg w E a T) (i : Fin 3) {K : List B256} {σ : Stor} {n : Devm} (m : Mem)
    (hA : At (initSevm msg).currentTarget K σ n) (hc : Clean n)
    (hcur : σ.get (rlKey i.val) = rlB (initSevm msg) (initDevm msg) i.val)
    (hk : rlKey i.val ∉ K) (hck : coinsBase + Nat.toB256 i.val ∉ K) (hne : rlKey i.val ≠ coinsBase + Nat.toB256 i.val) :
    rlIterStorageCost (initSevm msg) (initDevm msg) T i.val n m = 4300 + debitG (share w a i) ∧
      At (initSevm msg).currentTarget ((coinsBase + Nat.toB256 i.val) :: rlKey i.val :: rlKey i.val :: rlKey i.val :: K)
        (σ.set (rlKey i.val) (rlB (initSevm msg) (initDevm msg) i.val - rlV (initSevm msg) (initDevm msg) T i.val))
        (rlPushBase (initSevm msg) (initDevm msg) T i.val n m) ∧
      Mv [pool] ((4800 * empties (recorded w i) (share w a i) : Nat) : Int) n (rlPushBase (initSevm msg) (initDevm msg) T i.val n m) := by
  obtain ⟨h1, h2, h3⟩ := f.shareFacts i
  obtain ⟨c, av, mv⟩ := iter_view (s := initSevm msg) (pre := initDevm msg) (T := T) i.val m hA hc
    (by
      show _ = ((initDevm msg).getStor (initSevm msg).currentTarget).get _
      rw [f.poolStor.1, f.poolStor.2])
    hcur hk hck hne (by rw [h1, h2]; exact h3) (CoveredFork.rules_storageClearRefund f.fork)
  rw [h1] at c
  rw [h1, h2, f.target] at mv
  exact ⟨c, av, mv⟩

local notation "𝐬" => initSevm msg
local notation "𝐩" => initDevm msg

/-- A coin's site, from a chain that has left it alone. -/
theorem ExitFrame.site (f : ExitFrame msg w E a T) {x : Adr} {Tb : List Adr} {r : Int} {b : Devm} {t : B256} (htx : t.toAdr = x)
    (hx : x = pool ∨ x = c3 ∨ x = dai ∨ x = usdc ∨ x = usdt)
    (m : Mv Tb r 𝐩 b) (hT : x ∉ Tb) :
    CoinSite 𝐬 b t.toAdr ∧ b.getStor t.toAdr = w.getStor x :=
  have ha := f.party hx m hT
  ⟨⟨f.fork, m.clean f.clean, fun k hm => absurd ((ha.keys k).1 (by rw [← htx]; exact hm)) List.not_mem_nil,
    by rw [htx, ha.stor]; exact (f.stor x hx).2⟩, by rw [htx]; exact ha.stor⟩

/-- A site's address starts cold. -/
theorem ExitFrame.coldAddr (f : ExitFrame msg w E a T) {x : Adr} {Tb : List Adr} {r : Int} {b : Devm}
    (hx : x = c3 ∨ x = dai ∨ x = usdc ∨ x = usdt ∨ x = Usdc.usdcImpl) (m : Mv Tb r 𝐩 b) (hT : x ∉ Tb) : x ∉ b.accessedAddresses :=
  fun h => f.warm x hx (((m.same x hT).warm).1 h)

section Dai

open Blanc.Lift.Dai

/-- **Iteration 0's `transfer`: DAI.** -/
theorem ExitFrame.pushDai (f : ExitFrame msg w E a T) {n : Devm} {m : Mem} {sz : Nat} {Tb : List Adr} {r : Int}
    (mv : Mv Tb r 𝐩 (rlPushBase 𝐬 𝐩 T 0 n m)) (hT : dai ∉ Tb) (win : RLPushWin 𝐬 𝐩 T 0 m sz) :
    rlPushDebit 𝐬 𝐩 T (exitCalls msg) 0 n m =
        2600 + ext ((rlPushBase 𝐬 𝐩 T 0 n m).withGasLeft 0) [3, 0x2a0] (rlPushMem 𝐬 𝐩 T 0 m) 0x520 0x44 0x5c0 0x20 +
        (7274 + debitG (share w a 0) + creditG (word w dai (balSlot E)) (share w a 0)) ∧
      Mv (dai :: [dai]) ((4800 * empties (word w dai (balSlot pool)) (share w a 0) : Nat) : Int) (rlPushBase 𝐬 𝐩 T 0 n m)
        (rlPushNext 𝐬 𝐩 T (exitCalls msg) 0 n m) ∧
      Devm.getStor (rlPushNext 𝐬 𝐩 T (exitCalls msg) 0 n m) dai =
        ((w.getStor dai).set (balSlot pool) ((w.getStor dai).get (balSlot pool) - Nat.toB256 (share w a 0))).set
          (balSlot E) ((w.getStor dai).get (balSlot E) + Nat.toB256 (share w a 0)) ∧
      (rlPushNext 𝐬 𝐩 T (exitCalls msg) 0 n m).returnData.length = 32 := by
  obtain ⟨t, ht⟩ : ∃ t, t = Curve3Pool.coinAt (𝐩.getStor 𝐬.currentTarget) 0 := ⟨_, rfl⟩
  have htx : t.toAdr = dai := by rw [ht]; exact f.coins 0
  have hV : rlV 𝐬 𝐩 T 0 = Nat.toB256 (share w a 0) := f.sharesW 0
  obtain ⟨hsite, hst⟩ := f.site (x := dai) htx (Or.inr (Or.inr (Or.inl rfl))) mv hT
  have hread : ((rlPushMem 𝐬 𝐩 T 0 m).read (0x520 : B256).toNat (0x44 : B256).toNat).1 =
      transferSel ++ 𝐬.caller.toB256.toBytes ++ (Nat.toB256 (share w a 0)).toBytes := by
    rw [show (0x520 : B256).toNat = 0x520 by decide, show (0x44 : B256).toNat = 0x44 by decide, ← hV]
    exact win.read
  have hs0 := (f.shareFacts 0).2.2
  have hb0 := f.backed 0
  have hheld : coinHeld w pool 0 = word w dai (balSlot pool) := by
    unfold coinHeld; rw [ite_eq_right (by rintro ⟨h, -⟩; exact absurd h (by decide))]; rfl
  have hsw := share_word (w := w) f.holds.2.2 f.holds.2.1 0
  have hcr : word w dai (balSlot E) + share w a 0 < 2 ^ 255 := f.fits 0
  obtain ⟨c1, c2, c3'⟩ := dai_site (s := 𝐬) (b := rlPushBase 𝐬 𝐩 T 0 n m) (S := [3, 0x2a0]) (M := rlPushMem 𝐬 𝐩 T 0 m) (t := t)
    (ii := 0x520) (oi := 0x5c0) (V := Nat.toB256 (share w a 0)) hsite hread
    (by rw [f.target, f.caller]; exact Ne.symm (f.apart.poolEntry 0))
    (by rw [hst, f.target, hsw]; show share w a 0 ≤ word w dai (balSlot pool); omega)
    (by rw [hst, f.caller, hsw]; show share w a 0 + word w dai (balSlot E) < _; omega)
  simp only [hst, f.target, f.caller, hsw] at c1 c2 c3'
  rw [htx] at c2 c3'
  have hu : rlPushNext 𝐬 𝐩 T (exitCalls msg) 0 n m =
      coinNext (fun s p => xferPost s p 0) 𝐬 t 0x520 0x44 0x5c0 (rlPushBase 𝐬 𝐩 T 0 n m) [3, 0x2a0] (rlPushMem 𝐬 𝐩 T 0 m) := by
    rw [ht]; rfl
  have hd : rlPushDebit 𝐬 𝐩 T (exitCalls msg) 0 n m =
      coinDebit xferG 𝐬 t 0x520 0x44 0x5c0 (rlPushBase 𝐬 𝐩 T 0 n m) [3, 0x2a0] (rlPushMem 𝐬 𝐩 T 0 m) := by
    rw [ht]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hd, c1, acc_cold (by rw [htx]; exact f.coldAddr (Or.inr (Or.inl rfl)) mv hT)]
    rfl
  · rw [hu]; exact c2
  · rw [hu]; exact c3'
  · rw [hu]; rfl

end Dai

section Usdc

open Blanc.Lift.Usdc Blanc.Composition.UsdcLive

/-- **Iteration 1's `transfer`: USDC through its proxy.** -/
theorem ExitFrame.pushUsdc (f : ExitFrame msg w E a T) {n : Devm} {m : Mem} {sz : Nat} {Tb : List Adr} {r : Int}
    (mv : Mv Tb r 𝐩 (rlPushBase 𝐬 𝐩 T 1 n m)) (hT : usdc ∉ Tb) (hTi : usdcImpl ∉ Tb) (win : RLPushWin 𝐬 𝐩 T 1 m sz) :
    rlPushDebit 𝐬 𝐩 T (exitCalls msg) 1 n m =
        2600 + ext ((rlPushBase 𝐬 𝐩 T 1 n m).withGasLeft 0) [3, 0x2a0] (rlPushMem 𝐬 𝐩 T 1 m) 0x520 0x44 0x5c0 0x20 +
        (17752 + debitG (share w a 1) + creditG (word w usdc (balSlot E)) (share w a 1)) ∧
      Mv (usdc :: [usdc, usdcImpl]) ((4800 * empties (word w usdc (balSlot pool)) (share w a 1) : Nat) : Int) (rlPushBase 𝐬 𝐩 T 1 n m)
        (rlPushNext 𝐬 𝐩 T (exitCalls msg) 1 n m) ∧
      Devm.getStor (rlPushNext 𝐬 𝐩 T (exitCalls msg) 1 n m) usdc =
        ((w.getStor usdc).set (balSlot pool) ((w.getStor usdc).get (balSlot pool) - Nat.toB256 (share w a 1))).set
          (balSlot E) ((w.getStor usdc).get (balSlot E) + Nat.toB256 (share w a 1)) ∧
      (rlPushNext 𝐬 𝐩 T (exitCalls msg) 1 n m).returnData.length = 32 := by
  obtain ⟨t, ht⟩ : ∃ t, t = Curve3Pool.coinAt (𝐩.getStor 𝐬.currentTarget) 1 := ⟨_, rfl⟩
  have htx : t.toAdr = usdc := by rw [ht]; exact f.coins 1
  have hV : rlV 𝐬 𝐩 T 1 = Nat.toB256 (share w a 1) := f.sharesW 1
  obtain ⟨hsite, hst⟩ := f.site (x := usdc) htx (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) mv hT
  have hread : ((rlPushMem 𝐬 𝐩 T 1 m).read (0x520 : B256).toNat (0x44 : B256).toNat).1 =
      transferSel ++ 𝐬.caller.toB256.toBytes ++ (Nat.toB256 (share w a 1)).toBytes := by
    rw [show (0x520 : B256).toNat = 0x520 by decide, show (0x44 : B256).toNat = 0x44 by decide, ← hV]
    exact win.read
  have hs0 := (f.shareFacts 1).2.2
  have hb0 := f.backed 1
  have hheld : coinHeld w pool 1 = balanceBits ((w.getStor usdc).get (balSlot pool)) := by
    unfold coinHeld; rw [ite_eq_left ⟨rfl, f.open'.usdcV22⟩]
  have hbw : balanceBits ((w.getStor usdc).get (balSlot pool)) ≤ word w usdc (balSlot pool) := Nat.mod_le _ _
  have hsw := share_word (w := w) f.holds.2.2 f.holds.2.1 1
  have hcr : word w usdc (balSlot E) + share w a 1 < 2 ^ 255 := f.fits 1
  have hpKI : pKI = implSlot := by decide +kernel
  have hI : ((w.getStor usdc).get pKI).toAdr = usdcImpl := by
    rw [hpKI, show (w.getStor usdc).get implSlot = usdcImpl.toB256 from f.open'.usdcV22, toAdr_toB256]
  have hE1 : ∀ x ∈ [Bytes.toB256 [1], adminSlot, implSlot], balSlot E ≠ x := fun x hx e => f.apart.usdcE (by
    show balSlot E ∈ _
    rw [e]; exact hx)
  obtain ⟨c1, c2, c3'⟩ := usdc_site (s := 𝐬) (b := rlPushBase 𝐬 𝐩 T 1 n m) (S := [3, 0x2a0]) (M := rlPushMem 𝐬 𝐩 T 1 m) (t := t)
    (ii := 0x520) (oi := 0x5c0) (V := Nat.toB256 (share w a 1)) hsite hread
    (by rw [hst, hI]; exact f.coldAddr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) mv hTi)
    (by rw [hst, hI, htx]; decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [f.target]; decide +kernel)
    (by
      rw [f.caller, show pKA = adminSlot by decide +kernel, hpKI]
      exact ⟨hE1 _ (by simp only [List.mem_cons, true_or, or_true]), hE1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, or_true])⟩)
    (by rw [f.target]; decide +kernel) (by rw [f.caller]; exact Ne.symm (hE1 _ List.mem_cons_self))
    (by rw [f.target, f.caller]; exact Ne.symm (f.apart.poolEntry 1))
    (by rw [hst, f.target]; exact f.open'.usdcParties.1) (by rw [hst, f.caller]; exact f.open'.usdcParties.2)
    (by rw [hst, f.target, hsw]; show share w a 1 ≤ word w usdc (balSlot pool); omega)
    (by rw [hst, f.caller, hsw]; show share w a 1 + word w usdc (balSlot E) < _; omega)
  simp only [hst, hI, f.target, f.caller, hsw] at c1 c2 c3'
  rw [htx] at c2 c3'
  have hu : rlPushNext 𝐬 𝐩 T (exitCalls msg) 1 n m =
      coinNext (proxyCanon 1 (fun s p => implXferPost s p 0)) 𝐬 t 0x520 0x44 0x5c0 (rlPushBase 𝐬 𝐩 T 1 n m) [3, 0x2a0] (rlPushMem 𝐬 𝐩 T 1 m) := by
    rw [ht]; rfl
  have hd : rlPushDebit 𝐬 𝐩 T (exitCalls msg) 1 n m =
      coinDebit xferG 𝐬 t 0x520 0x44 0x5c0 (rlPushBase 𝐬 𝐩 T 1 n m) [3, 0x2a0] (rlPushMem 𝐬 𝐩 T 1 m) := by
    rw [ht]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hd, c1, acc_cold (by rw [htx]; exact f.coldAddr (Or.inr (Or.inr (Or.inl rfl))) mv hT)]
    rfl
  · rw [hu]; exact c2
  · rw [hu]; exact c3'
  · rw [hu]; rfl

end Usdc

section Usdt

open Blanc.Lift.Usdt

theorem capped_iff (σ : Stor) (v : B256) :
    Capped σ v ↔ (σ.get (Bytes.toB256 [4])).toNat < ((v * σ.get (Bytes.toB256 [3])) / Bytes.toB256 [39, 16]).toNat := by
  rw [← B256.lt_iff_toNat_lt_toNat]
  by_cases h : σ.get (Bytes.toB256 [4]) < (v * σ.get (Bytes.toB256 [3])) / Bytes.toB256 [39, 16]
  · have e : B256.gtCheck ((v * σ.get (Bytes.toB256 [3])) / Bytes.toB256 [39, 16]) (σ.get (Bytes.toB256 [4])) = 1 := ite_eq_left h
    unfold Capped
    rw [e]
    exact ⟨fun _ => h, fun _ => by decide⟩
  · have e : B256.gtCheck ((v * σ.get (Bytes.toB256 [3])) / Bytes.toB256 [39, 16]) (σ.get (Bytes.toB256 [4])) = 0 := ite_eq_right h
    unfold Capped
    rw [e]
    exact ⟨fun c => absurd c (by decide), fun c => absurd c h⟩

/-- USDT's reply is the frame's initial, empty output. -/
theorem xferPost_output (s : Sevm) (b : Devm) : (xferPost s b 0).output = b.output := by
  show (mvPost s (feeBase s (gateBase s b s.caller.toB256) (xVal s)) (xVal s) (feeOf (Devm.getStor b s.currentTarget) (xVal s)) (xTo s) s.caller.toB256).output = _
  unfold mvPost feeBase
  split <;> split <;>
    simp only [Devm.addLog_output, ownLogged, ownCredited, ownRead, mvCredited, mvDebited, afterSstore_output, afterSload_output, gateBase]

/-- The fee rule's arm, in the statement's observers. -/
theorem usdt_capped {w : Jaune.State} {v : Nat} (hv : v < 2 ^ 256) (hf : v * word w usdt 3 < 2 ^ 256) :
    Capped (w.getStor usdt) (Nat.toB256 v) ↔ word w usdt 4 < v * word w usdt 3 / 10000 := by
  rw [capped_iff, lit3, lit4]
  have hx : ((Nat.toB256 v * (w.getStor usdt).get 3) / Bytes.toB256 [39, 16]).toNat = v * word w usdt 3 / 10000 := by
    rw [Lift.rlOut_toNat (by rw [B256.toNat_toB256_of_lt hv]; exact hf) (by decide), B256.toNat_toB256_of_lt hv]
    rfl
  rw [hx]
  rfl

/-- The fee as a word reads back. -/
theorem fee_word {w : Jaune.State} {v : Nat} (hv : v < 2 ^ 256) (hf : v * word w usdt 3 < 2 ^ 256) :
    (feeOf (w.getStor usdt) (Nat.toB256 v)).toNat = usdtFee w v := by
  have hx : ((Nat.toB256 v * (w.getStor usdt).get 3) / Bytes.toB256 [39, 16]).toNat = v * word w usdt 3 / 10000 := by
    rw [Lift.rlOut_toNat (by rw [B256.toNat_toB256_of_lt hv]; exact hf) (by decide), B256.toNat_toB256_of_lt hv]
    rfl
  unfold feeOf usdtFee
  rw [hx]
  have e4 : ((w.getStor usdt).get 4).toNat = word w usdt 4 := rfl
  rw [e4]
  split
  · exact (Nat.min_eq_right (Nat.le_of_lt ‹_›)).symm
  · rw [hx]; exact (Nat.min_eq_left (Nat.le_of_not_lt ‹_›)).symm

theorem ownerKey_eq (σ : Stor) : ownerKey σ = balSlot (ownerOf σ) := by
  unfold ownerKey balSlot ownerOf
  rw [ownW_eq, lit2, lit0]

/-- USDT's frame charge in the statement's observers. -/
def usdtPayG (w : Jaune.State) (E : Adr) (v : Nat) : Nat :=
  15749 + (if v = 0 then 72 else 138) + (if word w usdt 4 < v * word w usdt 3 / 10000 then 336 else 228) +
    (if usdtFee w v = 0 then 2586
      else 7230 + creditG (word w usdt (balSlot (ownerOf (w.getStor usdt)))) (usdtFee w v)) +
    debitG v + creditG (word w usdt (balSlot E)) (v - usdtFee w v)

/-- **Iteration 2's `transfer`: USDT.** -/
theorem ExitFrame.pushUsdt (f : ExitFrame msg w E a T) {n : Devm} {m : Mem} {sz : Nat} {Tb : List Adr} {r : Int}
    (mv : Mv Tb r 𝐩 (rlPushBase 𝐬 𝐩 T 2 n m)) (hT : usdt ∉ Tb) (win : RLPushWin 𝐬 𝐩 T 2 m sz) :
    rlPushDebit 𝐬 𝐩 T (exitCalls msg) 2 n m =
        2600 + ext ((rlPushBase 𝐬 𝐩 T 2 n m).withGasLeft 0) [3, 0x2a0] (rlPushMem 𝐬 𝐩 T 2 m) 0x520 0x44 0x5c0 0x20 +
        usdtPayG w E (share w a 2) ∧
      Mv (usdt :: [usdt]) ((4800 * empties (word w usdt (balSlot pool)) (share w a 2) : Nat) : Int) (rlPushBase 𝐬 𝐩 T 2 n m)
        (rlPushNext 𝐬 𝐩 T (exitCalls msg) 2 n m) ∧
      Devm.getStor (rlPushNext 𝐬 𝐩 T (exitCalls msg) 2 n m) usdt =
        usdtAfter (w.getStor usdt) (balSlot pool) (balSlot E) (Nat.toB256 (share w a 2)) (feeOf (w.getStor usdt) (Nat.toB256 (share w a 2))) ∧
      (rlPushNext 𝐬 𝐩 T (exitCalls msg) 2 n m).returnData.length = 0 := by
  obtain ⟨t, ht⟩ : ∃ t, t = Curve3Pool.coinAt (𝐩.getStor 𝐬.currentTarget) 2 := ⟨_, rfl⟩
  have htx : t.toAdr = usdt := by rw [ht]; exact f.coins 2
  have hV : rlV 𝐬 𝐩 T 2 = Nat.toB256 (share w a 2) := f.sharesW 2
  obtain ⟨hsite, hst⟩ := f.site (x := usdt) htx (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) mv hT
  have hread : ((rlPushMem 𝐬 𝐩 T 2 m).read (0x520 : B256).toNat (0x44 : B256).toNat).1 =
      transferSel ++ 𝐬.caller.toB256.toBytes ++ (Nat.toB256 (share w a 2)).toBytes := by
    rw [show (0x520 : B256).toNat = 0x520 by decide, show (0x44 : B256).toNat = 0x44 by decide, ← hV]
    exact win.read
  have hs0 := (f.shareFacts 2).2.2
  have hb0 := f.backed 2
  have hheld : coinHeld w pool 2 = word w usdt (balSlot pool) := by
    unfold coinHeld; rw [ite_eq_right (by rintro ⟨h, -⟩; exact absurd h (by decide))]; rfl
  have hslt := share_lt (w := w) f.holds.2.2 f.holds.2.1 2
  have hsw := share_word (w := w) f.holds.2.2 f.holds.2.1 2
  obtain ⟨hff, hfo, hfl⟩ := f.feeFits
  have hfe := fee_word hslt hff
  have hcr : word w usdt (balSlot E) + (share w a 2 - usdtFee w (share w a 2)) < 2 ^ 255 := f.fits 2
  have hco : word w usdt (balSlot (ownerOf (w.getStor usdt))) + usdtFee w (share w a 2) < 2 ^ 255 := hfo
  have hsub : (Nat.toB256 (share w a 2) - feeOf (w.getStor usdt) (Nat.toB256 (share w a 2))).toNat = share w a 2 - usdtFee w (share w a 2) := by
    rw [B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, hsw, hfe]; exact hfl), hsw, hfe]
  have hgate : usdtRead pool.toB256 = usdtGateSlots := by decide +kernel
  obtain ⟨hE1, hE2⟩ := f.apart.usdtE
  obtain ⟨hO1, hO2⟩ := f.apart.usdtOwner
  obtain ⟨c1, c2, c3'⟩ := usdt_site (s := 𝐬) (b := rlPushBase 𝐬 𝐩 T 2 n m) (S := [3, 0x2a0]) (M := rlPushMem 𝐬 𝐩 T 2 m) (t := t)
    (ii := 0x520) (oi := 0x5c0) (V := Nat.toB256 (share w a 2)) hsite hread
    (by rw [f.target]; decide +kernel)
    (by rw [f.target]; decide +kernel)
    (by rw [f.target, f.caller, hgate]; exact hE1)
    (by rw [f.target, f.caller]; exact Ne.symm (f.apart.poolEntry 2))
    (by rw [hst, f.target, hsw]; show share w a 2 ≤ word w usdt (balSlot pool); omega)
    (by rw [hst, f.caller, hsub]; show _ + word w usdt (balSlot E) < _; omega)
    (by
      intro _
      rw [hst, f.target, f.caller, hgate, ownerKey_eq]
      refine ⟨hO1, hO2, fun e => hE2 e.symm, ?_⟩
      rw [hfe]
      show _ + word w usdt (balSlot (ownerOf (w.getStor usdt))) < _
      omega)
  simp only [hst, f.target, f.caller, hsw, hsub, hfe, ownerKey_eq] at c1 c2 c3'
  rw [htx] at c2 c3'
  have hu : rlPushNext 𝐬 𝐩 T (exitCalls msg) 2 n m =
      coinNext (fun s p => xferPost s p 0) 𝐬 t 0x520 0x44 0x5c0 (rlPushBase 𝐬 𝐩 T 2 n m) [3, 0x2a0] (rlPushMem 𝐬 𝐩 T 2 m) := by
    rw [ht]; rfl
  have hd : rlPushDebit 𝐬 𝐩 T (exitCalls msg) 2 n m =
      coinDebit xferG 𝐬 t 0x520 0x44 0x5c0 (rlPushBase 𝐬 𝐩 T 2 n m) [3, 0x2a0] (rlPushMem 𝐬 𝐩 T 2 m) := by
    rw [ht]; rfl
  have he61 : e61G (Nat.toB256 (share w a 2)) = if share w a 2 = 0 then 72 else 138 := by
    unfold e61G
    by_cases h0 : share w a 2 = 0
    · rw [ite_eq_left h0, ite_eq_left (by rw [h0]; rfl)]
    · rw [ite_eq_right h0, ite_eq_right (fun e => h0 (by rw [← hsw, e]; rfl))]
  have hcap := usdt_capped hslt hff
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hd, c1, acc_cold (by rw [htx]; exact f.coldAddr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) mv hT), he61]
    have hc' : (if Capped (w.getStor usdt) (Nat.toB256 (share w a 2)) then 336 else 228) =
        (if word w usdt 4 < share w a 2 * word w usdt 3 / 10000 then 336 else 228) := by
      by_cases hk : Capped (w.getStor usdt) (Nat.toB256 (share w a 2))
      · rw [ite_eq_left hk, ite_eq_left (hcap.1 hk)]
      · rw [ite_eq_right hk, ite_eq_right (fun h => hk (hcap.2 h))]
    have hf0 : (feeOf (w.getStor usdt) (Nat.toB256 (share w a 2)) = 0) ↔ usdtFee w (share w a 2) = 0 := by
      rw [← hfe]
      exact ⟨fun e => by rw [e]; rfl, fun e => B256.toNat_inj _ _ e⟩
    rw [hc']
    unfold usdtPayG
    by_cases hz : usdtFee w (share w a 2) = 0
    · rw [ite_eq_left (hf0.2 hz), ite_eq_left hz]; rfl
    · rw [ite_eq_right (fun e => hz (hf0.1 e)), ite_eq_right hz]; rfl
  · rw [hu]; exact c2
  · rw [hu]; exact c3'
  · rw [hu]
    show ((xferPost _ _ 0).output).length = 0
    rw [xferPost_output]
    rfl

end Usdt

/-- The pool's warm keys at each loop head. -/
def headKeys : Nat → List B256
  | 0 => [Bytes.toB256 [5], lockW, lockW]
  | i + 1 => (coinsBase + Nat.toB256 i) :: rlKey i :: rlKey i :: rlKey i :: headKeys i

/-- The pool's storage at each loop head. -/
noncomputable def headStor (s : Sevm) (pre : Devm) (T : B256) : Nat → Stor
  | 0 => (pre.getStor s.currentTarget).set lockW (Bytes.toB256 [1])
  | i + 1 => (headStor s pre T i).set (rlKey i) (rlB s pre i - rlV s pre T i)

/-- A loop head's standing: what has moved since the entry, and the pool's own view. -/
structure AtHead (msg : Msg) (T : B256) (i : Nat) (n : Devm) (Tl : List Adr) (r : Int) : Prop where
  mv : Mv Tl r (initDevm msg) n
  poolAt : At (initSevm msg).currentTarget (headKeys i) (headStor (initSevm msg) (initDevm msg) T i) n

/-- A head's next: the iteration's storage step, its `transfer` and the raw tail. -/
theorem AtHead.step {i : Nat} {n : Devm} {m : Mem} {Tl Tc : List Adr} {r rb rc : Int} (h : AtHead msg T i n Tl r)
    (hA : At (initSevm msg).currentTarget (headKeys (i + 1)) (headStor (initSevm msg) (initDevm msg) T (i + 1)) (rlPushBase (initSevm msg) (initDevm msg) T i n m))
    (hb : Mv [pool] rb n (rlPushBase (initSevm msg) (initDevm msg) T i n m))
    (hc : Mv Tc rc (rlPushBase (initSevm msg) (initDevm msg) T i n m) (rlPushNext (initSevm msg) (initDevm msg) T (exitCalls msg) i n m))
    (ht : (initSevm msg).currentTarget = pool) (hp : pool ∉ Tc) :
    AtHead msg T (i + 1) (rlIterBase (initSevm msg) (initDevm msg) T (exitCalls msg) i n m) (Tl ++ [pool] ++ Tc ++ []) (r + rb + rc + 0) := by
  have tail := mv_rawTail (initSevm msg) (rlPushNext (initSevm msg) (initDevm msg) T (exitCalls msg) i n m) [3, 0x2a0]
    (rlPushNext (initSevm msg) (initDevm msg) T (exitCalls msg) i n m).memory rlSite
  refine ⟨((h.mv.trans hb).trans hc).trans tail, ((hA.ofMv hc (by rw [ht]; exact hp)).ofMv tail List.not_mem_nil)⟩

/-- All moved parties up to the loop's exit. -/
abbrev loopParties : List Adr :=
  (Curve3PoolPublic.pool :: c3 :: [c3]) ++ [Curve3PoolPublic.pool] ++ (dai :: [dai]) ++ [] ++ [Curve3PoolPublic.pool] ++ (usdc :: [usdc, Usdc.usdcImpl]) ++ [] ++
    [Curve3PoolPublic.pool] ++ (usdt :: [usdt]) ++ []

/-- The refund up to the loop's exit: each coin's two debits. -/
def loopRefund (w : Jaune.State) (a : Nat) : Nat :=
  4800 * (empties (recorded w 0) (share w a 0) + empties (word w dai (Dai.balSlot pool)) (share w a 0) +
    (empties (recorded w 1) (share w a 1) + empties (word w usdc (Usdc.balSlot pool)) (share w a 1)) +
    (empties (recorded w 2) (share w a 2) + empties (word w usdt (Usdt.balSlot pool)) (share w a 2)))

/-- **The loop, evaluated.** -/
structure LoopDone (msg : Msg) (w : Jaune.State) (E : Adr) (a : Nat) (T : B256) : Prop where
  head : AtHead msg T 3 (rlHead3 (initSevm msg) (initDevm msg) T (exitCalls msg)) loopParties (loopRefund w a : Nat)
  c3At : At c3 [Curve3Crv.vySupplySlot] (w.getStor c3) (rlHead3 (initSevm msg) (initDevm msg) T (exitCalls msg))
  c3Warm : c3 ∈ (rlHead3 (initSevm msg) (initDevm msg) T (exitCalls msg)).accessedAddresses
  debits : rlDebits (initSevm msg) (initDevm msg) T (exitCalls msg) =
    4929 + (2600 + 10 + (7274 + debitG (share w a 0) + creditG (word w dai (Dai.balSlot E)) (share w a 0))) +
      (2600 + 0 + (17752 + debitG (share w a 1) + creditG (word w usdc (Usdc.balSlot E)) (share w a 1))) +
      (2600 + 0 + usdtPayG w E (share w a 2)) +
      (exitCalls msg).burnDebit (rlBurnBase (initSevm msg) (initDevm msg) T (exitCalls msg)) []
        (rlBurnMem (initSevm msg) (rlHeadMem3 (initSevm msg) (initDevm msg) T (exitCalls msg)))
  iters : rlIterStorageCost (initSevm msg) (initDevm msg) T 0 (rlHead0 (initSevm msg) (initDevm msg) (exitCalls msg)) (rlHeadMem0 (initSevm msg) (initDevm msg) T (exitCalls msg)) +
      rlIterStorageCost (initSevm msg) (initDevm msg) T 1 (rlHead1 (initSevm msg) (initDevm msg) T (exitCalls msg)) (rlHeadMem1 (initSevm msg) (initDevm msg) T (exitCalls msg)) +
      rlIterStorageCost (initSevm msg) (initDevm msg) T 2 (rlHead2 (initSevm msg) (initDevm msg) T (exitCalls msg)) (rlHeadMem2 (initSevm msg) (initDevm msg) T (exitCalls msg)) =
    12900 + debitG (share w a 0) + debitG (share w a 1) + debitG (share w a 2)
  tails : rlRawTails (initSevm msg) (initDevm msg) T (exitCalls msg) = rawTailCost 32 + rawTailCost 32 + rawTailCost 0
  daiS : Devm.getStor (rlHead3 (initSevm msg) (initDevm msg) T (exitCalls msg)) dai =
    ((w.getStor dai).set (Dai.balSlot pool) ((w.getStor dai).get (Dai.balSlot pool) - Nat.toB256 (share w a 0))).set
      (Dai.balSlot E) ((w.getStor dai).get (Dai.balSlot E) + Nat.toB256 (share w a 0))
  usdcS : Devm.getStor (rlHead3 (initSevm msg) (initDevm msg) T (exitCalls msg)) usdc =
    ((w.getStor usdc).set (Usdc.balSlot pool) ((w.getStor usdc).get (Usdc.balSlot pool) - Nat.toB256 (share w a 1))).set
      (Usdc.balSlot E) ((w.getStor usdc).get (Usdc.balSlot E) + Nat.toB256 (share w a 1))
  usdtS : Devm.getStor (rlHead3 (initSevm msg) (initDevm msg) T (exitCalls msg)) usdt =
    usdtAfter (w.getStor usdt) (Usdt.balSlot pool) (Usdt.balSlot E) (Nat.toB256 (share w a 2))
      (Usdt.feeOf (w.getStor usdt) (Nat.toB256 (share w a 2)))

theorem head_fresh0 : rlKey 0 ∉ headKeys 0 ∧ coinsBase + Nat.toB256 0 ∉ headKeys 0 ∧ rlKey 0 ≠ coinsBase + Nat.toB256 0 := by decide
theorem head_fresh1 : rlKey 1 ∉ headKeys 1 ∧ coinsBase + Nat.toB256 1 ∉ headKeys 1 ∧ rlKey 1 ≠ coinsBase + Nat.toB256 1 := by decide
theorem head_fresh2 : rlKey 2 ∉ headKeys 2 ∧ coinsBase + Nat.toB256 2 ∉ headKeys 2 ∧ rlKey 2 ≠ coinsBase + Nat.toB256 2 := by decide
theorem lock_ne0 : lockW ≠ rlKey 0 := by decide
theorem lock_ne1 : lockW ≠ rlKey 1 ∧ rlKey 0 ≠ rlKey 1 := by decide
theorem lock_ne2 : lockW ≠ rlKey 2 ∧ rlKey 0 ≠ rlKey 2 ∧ rlKey 1 ≠ rlKey 2 := by decide

theorem part0 : dai ∉ (Curve3PoolPublic.pool :: c3 :: [c3]) ++ [Curve3PoolPublic.pool] ∧ Curve3PoolPublic.pool ∉ dai :: [dai] := by decide
theorem part1 : usdc ∉ (Curve3PoolPublic.pool :: c3 :: [c3]) ++ [Curve3PoolPublic.pool] ++ (dai :: [dai]) ++ [] ++ [Curve3PoolPublic.pool] ∧
    Usdc.usdcImpl ∉ (Curve3PoolPublic.pool :: c3 :: [c3]) ++ [Curve3PoolPublic.pool] ++ (dai :: [dai]) ++ [] ++ [Curve3PoolPublic.pool] ∧
    Curve3PoolPublic.pool ∉ usdc :: [usdc, Usdc.usdcImpl] := by decide
theorem part2 : usdt ∉ (Curve3PoolPublic.pool :: c3 :: [c3]) ++ [Curve3PoolPublic.pool] ++ (dai :: [dai]) ++ [] ++ [Curve3PoolPublic.pool] ++
      (usdc :: [usdc, Usdc.usdcImpl]) ++ [] ++ [Curve3PoolPublic.pool] ∧ Curve3PoolPublic.pool ∉ usdt :: [usdt] := by decide

/-- **The loop's three heads.** -/
structure LoopSteps (msg : Msg) (w : Jaune.State) (E : Adr) (a : Nat) (T : B256) : Prop where
  h3 : AtHead msg T 3 (rlHead3 (initSevm msg) (initDevm msg) T (exitCalls msg)) loopParties
    (0 + ((4800 * empties (recorded w 0) (share w a 0) : Nat) : Int) + ((4800 * empties (word w dai (Dai.balSlot pool)) (share w a 0) : Nat) : Int) + 0 +
      ((4800 * empties (recorded w 1) (share w a 1) : Nat) : Int) + ((4800 * empties (word w usdc (Usdc.balSlot pool)) (share w a 1) : Nat) : Int) + 0 +
      ((4800 * empties (recorded w 2) (share w a 2) : Nat) : Int) + ((4800 * empties (word w usdt (Usdt.balSlot pool)) (share w a 2) : Nat) : Int) + 0)
  d0 : rlPushDebit (initSevm msg) (initDevm msg) T (exitCalls msg) 0 (rlHead0 (initSevm msg) (initDevm msg) (exitCalls msg)) (rlHeadMem0 (initSevm msg) (initDevm msg) T (exitCalls msg)) =
    2600 + ext ((rlPushBase (initSevm msg) (initDevm msg) T 0 (rlHead0 (initSevm msg) (initDevm msg) (exitCalls msg)) (rlHeadMem0 (initSevm msg) (initDevm msg) T (exitCalls msg))).withGasLeft 0) [3, 0x2a0]
      (rlPushMem (initSevm msg) (initDevm msg) T 0 (rlHeadMem0 (initSevm msg) (initDevm msg) T (exitCalls msg))) 0x520 0x44 0x5c0 0x20 +
      (7274 + debitG (share w a 0) + creditG (word w dai (Dai.balSlot E)) (share w a 0))
  d1 : rlPushDebit (initSevm msg) (initDevm msg) T (exitCalls msg) 1 (rlHead1 (initSevm msg) (initDevm msg) T (exitCalls msg)) (rlHeadMem1 (initSevm msg) (initDevm msg) T (exitCalls msg)) =
    2600 + ext ((rlPushBase (initSevm msg) (initDevm msg) T 1 (rlHead1 (initSevm msg) (initDevm msg) T (exitCalls msg)) (rlHeadMem1 (initSevm msg) (initDevm msg) T (exitCalls msg))).withGasLeft 0) [3, 0x2a0]
      (rlPushMem (initSevm msg) (initDevm msg) T 1 (rlHeadMem1 (initSevm msg) (initDevm msg) T (exitCalls msg))) 0x520 0x44 0x5c0 0x20 +
      (17752 + debitG (share w a 1) + creditG (word w usdc (Usdc.balSlot E)) (share w a 1))
  d2 : rlPushDebit (initSevm msg) (initDevm msg) T (exitCalls msg) 2 (rlHead2 (initSevm msg) (initDevm msg) T (exitCalls msg)) (rlHeadMem2 (initSevm msg) (initDevm msg) T (exitCalls msg)) =
    2600 + ext ((rlPushBase (initSevm msg) (initDevm msg) T 2 (rlHead2 (initSevm msg) (initDevm msg) T (exitCalls msg)) (rlHeadMem2 (initSevm msg) (initDevm msg) T (exitCalls msg))).withGasLeft 0) [3, 0x2a0]
      (rlPushMem (initSevm msg) (initDevm msg) T 2 (rlHeadMem2 (initSevm msg) (initDevm msg) T (exitCalls msg))) 0x520 0x44 0x5c0 0x20 +
      usdtPayG w E (share w a 2)
  c0 : rlIterStorageCost (initSevm msg) (initDevm msg) T 0 (rlHead0 (initSevm msg) (initDevm msg) (exitCalls msg)) (rlHeadMem0 (initSevm msg) (initDevm msg) T (exitCalls msg)) = 4300 + debitG (share w a 0)
  c1 : rlIterStorageCost (initSevm msg) (initDevm msg) T 1 (rlHead1 (initSevm msg) (initDevm msg) T (exitCalls msg)) (rlHeadMem1 (initSevm msg) (initDevm msg) T (exitCalls msg)) = 4300 + debitG (share w a 1)
  c2 : rlIterStorageCost (initSevm msg) (initDevm msg) T 2 (rlHead2 (initSevm msg) (initDevm msg) T (exitCalls msg)) (rlHeadMem2 (initSevm msg) (initDevm msg) T (exitCalls msg)) = 4300 + debitG (share w a 2)
  l0 : rlReplyLen (initSevm msg) (initDevm msg) T (exitCalls msg) 0 (rlHead0 (initSevm msg) (initDevm msg) (exitCalls msg)) (rlHeadMem0 (initSevm msg) (initDevm msg) T (exitCalls msg)) = 32
  l1 : rlReplyLen (initSevm msg) (initDevm msg) T (exitCalls msg) 1 (rlHead1 (initSevm msg) (initDevm msg) T (exitCalls msg)) (rlHeadMem1 (initSevm msg) (initDevm msg) T (exitCalls msg)) = 32
  l2 : rlReplyLen (initSevm msg) (initDevm msg) T (exitCalls msg) 2 (rlHead2 (initSevm msg) (initDevm msg) T (exitCalls msg)) (rlHeadMem2 (initSevm msg) (initDevm msg) T (exitCalls msg)) = 0
  daiS : Devm.getStor (rlPushNext (initSevm msg) (initDevm msg) T (exitCalls msg) 0 (rlHead0 (initSevm msg) (initDevm msg) (exitCalls msg)) (rlHeadMem0 (initSevm msg) (initDevm msg) T (exitCalls msg))) dai =
    ((w.getStor dai).set (Dai.balSlot pool) ((w.getStor dai).get (Dai.balSlot pool) - Nat.toB256 (share w a 0))).set
      (Dai.balSlot E) ((w.getStor dai).get (Dai.balSlot E) + Nat.toB256 (share w a 0))
  usdcS : Devm.getStor (rlPushNext (initSevm msg) (initDevm msg) T (exitCalls msg) 1 (rlHead1 (initSevm msg) (initDevm msg) T (exitCalls msg)) (rlHeadMem1 (initSevm msg) (initDevm msg) T (exitCalls msg))) usdc =
    ((w.getStor usdc).set (Usdc.balSlot pool) ((w.getStor usdc).get (Usdc.balSlot pool) - Nat.toB256 (share w a 1))).set
      (Usdc.balSlot E) ((w.getStor usdc).get (Usdc.balSlot E) + Nat.toB256 (share w a 1))
  usdtS : Devm.getStor (rlPushNext (initSevm msg) (initDevm msg) T (exitCalls msg) 2 (rlHead2 (initSevm msg) (initDevm msg) T (exitCalls msg)) (rlHeadMem2 (initSevm msg) (initDevm msg) T (exitCalls msg))) usdt =
    usdtAfter (w.getStor usdt) (Usdt.balSlot pool) (Usdt.balSlot E) (Nat.toB256 (share w a 2))
      (Usdt.feeOf (w.getStor usdt) (Nat.toB256 (share w a 2)))
  mid0 : Mv [pool] ((4800 * empties (recorded w 1) (share w a 1) : Nat) : Int) (rlHead1 (initSevm msg) (initDevm msg) T (exitCalls msg))
    (rlPushBase (initSevm msg) (initDevm msg) T 1 (rlHead1 (initSevm msg) (initDevm msg) T (exitCalls msg)) (rlHeadMem1 (initSevm msg) (initDevm msg) T (exitCalls msg)))
  mid1 : Mv [pool] ((4800 * empties (recorded w 2) (share w a 2) : Nat) : Int) (rlHead2 (initSevm msg) (initDevm msg) T (exitCalls msg))
    (rlPushBase (initSevm msg) (initDevm msg) T 2 (rlHead2 (initSevm msg) (initDevm msg) T (exitCalls msg)) (rlHeadMem2 (initSevm msg) (initDevm msg) T (exitCalls msg)))
  mid00 : Mv [pool] ((4800 * empties (recorded w 0) (share w a 0) : Nat) : Int) (rlHead0 (initSevm msg) (initDevm msg) (exitCalls msg))
    (rlPushBase (initSevm msg) (initDevm msg) T 0 (rlHead0 (initSevm msg) (initDevm msg) (exitCalls msg)) (rlHeadMem0 (initSevm msg) (initDevm msg) T (exitCalls msg)))
  n0 : Mv (dai :: [dai]) ((4800 * empties (word w dai (Dai.balSlot pool)) (share w a 0) : Nat) : Int)
    (rlPushBase (initSevm msg) (initDevm msg) T 0 (rlHead0 (initSevm msg) (initDevm msg) (exitCalls msg)) (rlHeadMem0 (initSevm msg) (initDevm msg) T (exitCalls msg)))
    (rlPushNext (initSevm msg) (initDevm msg) T (exitCalls msg) 0 (rlHead0 (initSevm msg) (initDevm msg) (exitCalls msg)) (rlHeadMem0 (initSevm msg) (initDevm msg) T (exitCalls msg)))
  n1 : Mv (usdc :: [usdc, Usdc.usdcImpl]) ((4800 * empties (word w usdc (Usdc.balSlot pool)) (share w a 1) : Nat) : Int)
    (rlPushBase (initSevm msg) (initDevm msg) T 1 (rlHead1 (initSevm msg) (initDevm msg) T (exitCalls msg)) (rlHeadMem1 (initSevm msg) (initDevm msg) T (exitCalls msg)))
    (rlPushNext (initSevm msg) (initDevm msg) T (exitCalls msg) 1 (rlHead1 (initSevm msg) (initDevm msg) T (exitCalls msg)) (rlHeadMem1 (initSevm msg) (initDevm msg) T (exitCalls msg)))
  n2 : Mv (usdt :: [usdt]) ((4800 * empties (word w usdt (Usdt.balSlot pool)) (share w a 2) : Nat) : Int)
    (rlPushBase (initSevm msg) (initDevm msg) T 2 (rlHead2 (initSevm msg) (initDevm msg) T (exitCalls msg)) (rlHeadMem2 (initSevm msg) (initDevm msg) T (exitCalls msg)))
    (rlPushNext (initSevm msg) (initDevm msg) T (exitCalls msg) 2 (rlHead2 (initSevm msg) (initDevm msg) T (exitCalls msg)) (rlHeadMem2 (initSevm msg) (initDevm msg) T (exitCalls msg)))

/-- **The loop's steps.** -/
theorem ExitFrame.steps (f : ExitFrame msg w E a T) (win : RLWindows 𝐬 𝐩 T (exitCalls msg)) : LoopSteps msg w E a T := by
  obtain ⟨m0, a0, -, -, -, -⟩ := stage_supply f
  have h0 : AtHead msg T 0 (rlHead0 𝐬 𝐩 (exitCalls msg)) _ _ := ⟨m0, a0⟩
  obtain ⟨c0, ap0, mb0⟩ := f.iter 0 (rlHeadMem0 𝐬 𝐩 T (exitCalls msg)) a0 (m0.clean f.clean)
    (Stor.get_set_ne _ lock_ne0 _) head_fresh0.1 head_fresh0.2.1 head_fresh0.2.2
  obtain ⟨d0, n0, s0, l0⟩ := f.pushDai (m0.trans mb0) part0.1 win.push0
  have h1 := h0.step ap0 mb0 n0 f.target part0.2
  obtain ⟨c1, ap1, mb1⟩ := f.iter 1 (rlHeadMem1 𝐬 𝐩 T (exitCalls msg)) h1.poolAt (h1.mv.clean f.clean)
    ((Stor.get_set_ne _ lock_ne1.2 _).trans (Stor.get_set_ne _ lock_ne1.1 _)) head_fresh1.1 head_fresh1.2.1 head_fresh1.2.2
  obtain ⟨d1, n1, s1, l1⟩ := f.pushUsdc (h1.mv.trans mb1) part1.1 part1.2.1 win.push1
  have h2 := h1.step ap1 mb1 n1 f.target part1.2.2
  obtain ⟨c2, ap2, mb2⟩ := f.iter 2 (rlHeadMem2 𝐬 𝐩 T (exitCalls msg)) h2.poolAt (h2.mv.clean f.clean)
    ((Stor.get_set_ne _ lock_ne2.2.2 _).trans ((Stor.get_set_ne _ lock_ne2.2.1 _).trans (Stor.get_set_ne _ lock_ne2.1 _))) head_fresh2.1 head_fresh2.2.1 head_fresh2.2.2
  obtain ⟨d2, n2, s2, l2⟩ := f.pushUsdt (h2.mv.trans mb2) part2.1 win.push2
  have h3 := h2.step ap2 mb2 n2 f.target part2.2
  exact ⟨h3, d0, d1, d2, c0, c1, c2, (congrArg (fun x => min x 32) l0).trans rfl, (congrArg (fun x => min x 32) l1).trans rfl, (congrArg (fun x => min x 32) l2).trans rfl,
    s0, s1, s2, mb1, mb2, mb0, n0, n1, n2⟩

end Chain

end Blanc.Composition.Curve3PoolPublic
