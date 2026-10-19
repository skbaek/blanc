import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveKit

/-!
# Exact-gas step twins for `add_liquidity`'s stage cores

The forward walk's storage and call steps (`rxe_sloadV`, `rxe_sstoreV`, `rxe_staticWord`) hand
their continuations bounds only. The twins below hand on, in addition, the exact charge at the
actual world (`G = G' + sloadCost …`, `G = G' + sstoreCost …`), the literal memory a call or an
expansion leaves, and an exact call's relation `E` (`StaticWordOkAtE`), so a stage core can
report its exact cost and its literal memory while the bounded stage stays its projection.

`Mem.EqExcept M N (fun _ => False)` (one logical size, both well formed, every byte equal) is
what a crossed callee that keeps its scratch to itself (`get_D_mem`, `getDMem_exactL`) leaves
relative to its normal form; `eqB_write_grow` turns it into equality at the next store that grows
the memory, where both arrays become fully materialised.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

section Fwd

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f : SFunc} {img : Bytes}

/-- **`SLOAD` within a gas budget**, the base, the word read and the exact charge named. -/
theorem rxe_sloadVE {Q : Outcome → Prop} {k' : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hroom : S.length < 1024) (hG : 2100 ≤ G)
    (k : ∀ G' b' v, b' = afterSload sevm b k' → v = b.getStorVal sevm.currentTarget k' →
      G ≤ G' + 2100 → G' ≤ G → G = G' + sloadCost sevm b k' →
      SFunc.RunEx fs sevm (St b' (v :: S) M G') f Q) :
    SFunc.RunEx fs sevm (St b (k' :: S) M G) (.next (.reg .sload) f) Q := by
  have hc := sloadCost_le sevm b k'
  have e1 : gasColdSload = 2100 := rfl
  obtain ⟨r, hr, hq⟩ := k (G - sloadCost sevm b k') _ _ rfl rfl (by omega) (by omega) (by omega)
  refine ⟨r, ?_, hq⟩
  rw [show G = (G - sloadCost sevm b k') + sloadCost sevm b k' by omega]
  exact rx_sload_sel hfork hroom hr

/-- **`SSTORE` within a gas budget**, the base and the exact charge named. -/
theorem rxe_sstoreVE {Q : Outcome → Prop} {k' v : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hG : 24401 ≤ G)
    (k : ∀ G' b', b' = afterSstore sevm b k' v → G ≤ G' + 22100 → G' ≤ G →
      G = G' + sstoreCost sevm b k' v → SFunc.RunEx fs sevm (St b' S M G') f Q) :
    SFunc.RunEx fs sevm (St b (k' :: v :: S) M G) (.next (.reg .sstore) f) Q := by
  have hc := sstoreCost_le_22100 sevm b k' v
  obtain ⟨r, hr, hq⟩ := k (G - sstoreCost sevm b k' v) _ rfl (by omega) (by omega) (by omega)
  refine ⟨r, ?_, hq⟩
  rw [show G = (G - sstoreCost sevm b k' v) + sstoreCost sevm b k' v by omega]
  exact rx_sstore hfork (by have : gCallStipend = 2300 := rfl; omega) hstatic hr

/-- `MLOAD` past the memory's end over the image carrier, to some outcome, at the literal
extended memory (`rxe_mloadX` with the memory named). -/
theorem rxe_mloadXE {Q : Outcome → Prop} {i : B256} {o s c : Nat} (hR : Mem.Reads M img)
    (hW : Mem.Wf M) (hsz : M.size = s) (ho : i.toNat = o)
    (hc : gVerylow + (calculateMemoryGasCost (memExtSize s o 32) - calculateMemoryGasCost s) = c ∧
      s % 32 = 0) (hroom : S.length < 1024)
    (k : ∀ M', M' = M.extend o 32 → Mem.Reads M' img → Mem.Wf M' →
      M'.size = memExtSize s o 32 →
      SFunc.RunEx fs sevm (St b (Bytes.toB256 (img.sliceD o 32 0) :: S) M' G) f Q) :
    SFunc.RunEx fs sevm (St b (i :: S) M (G + c)) (.next (.reg .mload) f) Q := by
  subst ho
  obtain ⟨r, hr, hq⟩ := k (M.extend i.toNat 32) rfl (hR.extend _ _) (hW.extend _ _)
    (by rw [← hsz]; rfl)
  refine ⟨r, rx_mload_ext ?_ (by rw [hR.read]) rfl hroom hr, hq⟩
  rw [St.extCost_eq hsz]; exact hc.1

end Fwd

/-- **A one-word `STATICCALL` answered by a relation premise, forward**: `rxe_staticWord` over
`StaticWordOkAtE`, the continuation also receiving the literal post memory and `E` at the
call's actual input and gas. -/
theorem rxe_staticWordAlE {sevm : Sevm} {W W' : Devm → Prop} {σ : Stor} {b : Devm}
    {S : List B256} {M : Mem} {img : Bytes} {G U : Nat} {t A ii is oi : B256} {data : Bytes}
    {o s : Nat} {Q : Outcome → Prop} {f : SFunc} {E : Devm → List B256 → Mem → Nat → Devm → Prop}
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hp : StaticWordOkAtE sevm W W' t data A U ii is oi E) (hU : U ≤ G) (hG : G < 2 ^ 256)
    (hroom : S.length < 1024)
    (hin : (M.read ii.toNat is.toNat).1 = data) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hoi : oi.toNat = o)
    (hext : (M.extends [(ii.toNat, is.toNat), (oi.toNat, 0x20)]).size = s) (hfit : o + 0x20 ≤ s)
    (k : ∀ (d : Devm) (M' : Mem) (out : Bytes), ExLive sevm W' d σ →
      Mem.Reads M' (Bytes.writeAt img o (out.take 0x20)) → Mem.Wf M' → M'.size = s →
      32 ≤ out.length → out.length < 2 ^ 256 → Bytes.toB256 (out.take 32) = A →
      d.returnData = out → G ≤ d.gasLeft + U → d.gasLeft ≤ G →
      M' = (M.extends [(ii.toNat, is.toNat), (oi.toNat, 0x20)]).write o (out.take 0x20) →
      E b S M G d →
      SFunc.RunEx cert.prog sevm (St d (1 :: S) M' d.gasLeft) f Q) :
    SFunc.RunEx cert.prog sevm (St b (Nat.toB256 G :: t :: ii :: is :: oi :: 0x20 :: S) M G)
      (.next (.exec .staticcall) f) Q := by
  obtain ⟨d, out, hrun, hpost, hlen, hlt, hA, hg1, hg2, hWd, hidd, hE⟩ :=
    hp b S M G hL.w hU hG hin hroom
  have hd := hpost.eq_St
  rw [show (0x20 : B256).toNat = 0x20 by decide] at hd
  subst hoi
  have hsz' : ((M.extends [(ii.toNat, is.toNat), (oi.toNat, 0x20)]).write oi.toNat
      (out.take 0x20)).size = s := by
    rw [Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
  obtain ⟨r, hr, hq⟩ := k d _ out ⟨fun x => by rw [hpost.stor]; exact hL.stor x, hidd hL.id, hW'c,
    hWd⟩ ((hR.extends _).write (hW.extends _) _ _) ((hW.extends _).write _ _) hsz' hlen hlt hA
    hpost.returnData hg1 hg2 rfl hE
  exact ⟨r, .next hrun (Eq.mpr (congrArg (fun x => SFunc.RunExact cert.prog sevm x f r) hd) hr), hq⟩

/-! ## Memories equal at every byte -/

/-- The same store on two memories equal at every byte. -/
theorem eqB_write {M N : Mem} (h : Mem.EqExcept M N fun _ => False) (o : Nat) (xs : Bytes) :
    Mem.EqExcept (M.write o xs) (N.write o xs) fun _ => False :=
  (h.write o xs).mono fun _ hi => hi.1

/-- The same expansion on two memories equal at every byte. -/
theorem eqB_extend {M N : Mem} (h : Mem.EqExcept M N fun _ => False) (o n : Nat) :
    Mem.EqExcept (M.extend o n) (N.extend o n) fun _ => False :=
  h.extend o n

/-- **A growing store makes two memories equal at every byte equal.** Both arrays are then
materialised to the (common) logical size. -/
theorem eqB_write_grow {M N : Mem} (h : Mem.EqExcept M N fun _ => False) {o : Nat} {xs : Bytes}
    (hne : xs ≠ []) (hg : M.size < o + xs.length) : M.write o xs = N.write o xs :=
  (eqB_write h o xs).eq (fun _ hi => hi) (Mem.full_write_of_grow hne hg)
    (Mem.full_write_of_grow hne (by rw [← h.1]; exact hg))

/-- A growing word store makes two memories equal at every byte equal. -/
theorem eqB_write_word_grow {M N : Mem} (h : Mem.EqExcept M N fun _ => False) {o : Nat}
    (v : B256) (hg : M.size < o + 32) : M.write o v.toBytes = N.write o v.toBytes :=
  eqB_write_grow h (fun e => by have := B256.length_toBytes v; rw [e] at this; exact absurd this (by decide))
    (by rw [B256.length_toBytes]; exact hg)

end Blanc.Lift.Curve3Pool
