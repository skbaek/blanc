import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityLive
import Blanc.Lift.InvWalkCallNext
import Blanc.StorageAccessGas
import Blanc.Lift.CreationOps

/-!
# Forward-walk kit for the pool's liveness walks

The steps `remove_liquidity`'s forward walk did not need, for `exchange` and the other entries:

* `rxm_mloadW`: `MLOAD` of a covered word the image carries (`WordAt`), pushing the word itself;
* `rx_branch_zero'`, `rx_branchTo_zero'`: a `JUMPI` not taken on a condition proved zero;
* `rx_address`;
* budget steps `rxe_sloadB`, `rxe_sstoreB`: a storage access at whatever it charges (at most
  `2100`, resp. `22100`), the continuation receiving the gas left with both bounds;
* `rxe_pcCall`: Vyper's internal-call idiom over an exact callee run, to some outcome;
* `xbr`/`xbr0`/`wauto`: the side-goal tactics the generated step lines use.

Gas inside a run of fixed-cost steps is exact (`G + c` offsets); a storage access or a call
switches to bounds (`G ≤ G' + c`, `G' ≤ G`), so a whole walk proves "enough gas suffices".
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

section Fwd

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f g : SFunc} {r : Outcome} {img : Bytes}

/-- `MLOAD` of a covered word the image carries. -/
theorem rxm_mloadW {i v : B256} {o s : Nat} (hR : Mem.Reads M img) (hsz : M.size = s)
    (ho : i.toNat = o) (hin : o + 32 ≤ s ∧ s % 32 = 0) (hw : WordAt img o v)
    (hroom : S.length < 1024) (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f r) :
    SFunc.RunExact fs sevm (St b (i :: S) M (G + 3)) (.next (.reg .mload) f) r :=
  rxm_mload hR hsz ho hin hroom (by rw [hw.read]; exact k)

/-- A `JUMPI` not taken, on a condition proved zero. -/
theorem rx_branch_zero' {d w : B256} (hw : w = 0) (k : SFunc.RunExact fs sevm (St b S M G) f r) :
    SFunc.RunExact fs sevm (St b (d :: w :: S) M (G + 10)) (.branch f g) r := by
  subst hw; exact rx_branch_zero k

/-- A conditional goto not taken, on a condition proved zero. -/
theorem rx_branchTo_zero' {d w : B256} {j : Nat} (hw : w = 0)
    (k : SFunc.RunExact fs sevm (St b S M G) f r) :
    SFunc.RunExact fs sevm (St b (d :: w :: S) M (G + 10)) (.branchTo f j) r := by
  subst hw; exact rx_branchTo_zero k

/-- `ADDRESS`. -/
theorem rx_address (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (sevm.currentTarget.toB256 :: S) M G) f r) :
    SFunc.RunExact fs sevm (St b S M (G + 2)) (.next (.reg .address) f) r :=
  .next (Ninst.runCompiled_pushItem (devm := St b S M (G + 2)) (G := G) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl hroom) k

/-- `SGT`. -/
theorem rx_sgt {x y v : B256} (hv : B256.sgtCheck x y = v) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f r) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + 3)) (.next (.reg .sgt) f) r :=
  rx_binary (fn := B256.sgtCheck) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

/-- `MLOAD` past the memory's end over the image carrier, to some outcome: the memory grows to
`memExtSize s o 32` and the word read is the image's (zero past its end). -/
theorem rxe_mloadX {Q : Outcome → Prop} {i : B256} {o s c : Nat} (hR : Mem.Reads M img)
    (hW : Mem.Wf M) (hsz : M.size = s) (ho : i.toNat = o)
    (hc : gVerylow + (calculateMemoryGasCost (memExtSize s o 32) - calculateMemoryGasCost s) = c ∧
      s % 32 = 0) (hroom : S.length < 1024)
    (k : ∀ M', Mem.Reads M' img → Mem.Wf M' → M'.size = memExtSize s o 32 →
      SFunc.RunEx fs sevm (St b (Bytes.toB256 (img.sliceD o 32 0) :: S) M' G) f Q) :
    SFunc.RunEx fs sevm (St b (i :: S) M (G + c)) (.next (.reg .mload) f) Q := by
  subst ho
  obtain ⟨r, hr, hq⟩ := k (M.extend i.toNat 32) (hR.extend _ _) (hW.extend _ _)
    (by rw [← hsz]; rfl)
  refine ⟨r, rx_mload_ext ?_ (by rw [hR.read]) rfl hroom hr, hq⟩
  rw [St.extCost_eq hsz]; exact hc.1

/-- **`SLOAD` within a gas budget**: at most `2100` charged. -/
theorem rxe_sloadB {Q : Outcome → Prop} {k' : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hroom : S.length < 1024) (hG : 2100 ≤ G)
    (k : ∀ G', G ≤ G' + 2100 → G' ≤ G → SFunc.RunEx fs sevm
      (St (afterSload sevm b k') (b.getStorVal sevm.currentTarget k' :: S) M G') f Q) :
    SFunc.RunEx fs sevm (St b (k' :: S) M G) (.next (.reg .sload) f) Q := by
  have hc := sloadCost_le sevm b k'
  have e1 : gasColdSload = 2100 := rfl
  obtain ⟨r, hr, hq⟩ := k (G - sloadCost sevm b k') (by omega) (by omega)
  refine ⟨r, ?_, hq⟩
  rw [show G = (G - sloadCost sevm b k') + sloadCost sevm b k' by omega]
  exact rx_sload_sel hfork hroom hr

/-- **`SSTORE` within a gas budget**: at most `22100` charged. -/
theorem rxe_sstoreB {Q : Outcome → Prop} {k' v : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hG : 24401 ≤ G)
    (k : ∀ G', G ≤ G' + 22100 → G' ≤ G →
      SFunc.RunEx fs sevm (St (afterSstore sevm b k' v) S M G') f Q) :
    SFunc.RunEx fs sevm (St b (k' :: v :: S) M G) (.next (.reg .sstore) f) Q := by
  have hc := sstoreCost_le_22100 sevm b k' v
  obtain ⟨r, hr, hq⟩ := k (G - sstoreCost sevm b k' v) (by omega) (by omega)
  refine ⟨r, ?_, hq⟩
  rw [show G = (G - sstoreCost sevm b k' v) + sstoreCost sevm b k' v by omega]
  exact rx_sstore hfork (by have : gCallStipend = 2300 := rfl; omega) hstatic hr

/-- **`SLOAD` within a gas budget**, the base and the word read named. -/
theorem rxe_sloadV {Q : Outcome → Prop} {k' : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hroom : S.length < 1024) (hG : 2100 ≤ G)
    (k : ∀ G' b' v, b' = afterSload sevm b k' → v = b.getStorVal sevm.currentTarget k' →
      G ≤ G' + 2100 → G' ≤ G → SFunc.RunEx fs sevm (St b' (v :: S) M G') f Q) :
    SFunc.RunEx fs sevm (St b (k' :: S) M G) (.next (.reg .sload) f) Q :=
  rxe_sloadB hfork hroom hG fun G' h1 h2 => k G' _ _ rfl rfl h1 h2

/-- **`SSTORE` within a gas budget**, the base named. -/
theorem rxe_sstoreV {Q : Outcome → Prop} {k' v : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hG : 24401 ≤ G)
    (k : ∀ G' b', b' = afterSstore sevm b k' v → G ≤ G' + 22100 → G' ≤ G →
      SFunc.RunEx fs sevm (St b' S M G') f Q) :
    SFunc.RunEx fs sevm (St b (k' :: v :: S) M G) (.next (.reg .sstore) f) Q :=
  rxe_sstoreB hfork hstatic hG fun G' h1 h2 => k G' _ rfl h1 h2

/-- **Vyper's internal-call idiom, to some outcome**: an exact callee run from the return
address `p + 6` to `.returned D`, and a continuation from `D`, at `19` gas for the idiom. -/
theorem rxe_pcCall {Q : Outcome → Prop} {p k : Nat} {t0 t1 : UInt8} {D : Devm}
    (hk : fs[k]? = some g) (hp : p + 6 < 2 ^ 256) (hroom : S.length + 2 < 1024)
    (hcall : SFunc.RunExact fs sevm (St b (Nat.toB256 (p + 6) :: S) M G) g (.returned D))
    (cont : SFunc.RunEx fs sevm D f Q) :
    SFunc.RunEx fs sevm (St b S M (G + 19)) (pcCallTree p t0 t1 k f) Q := by
  obtain ⟨r, hr, hq⟩ := cont
  exact ⟨r, SFunc.runExact_iff_runExactCut_nil.mpr
    (rxc_pcCall hk hp hroom hcall (SFunc.runExact_iff_runExactCut_nil.mp hr)), hq⟩

end Fwd

/-! ## Vyper's checked-arithmetic guards, forward -/

/-- The overflow guard of a checked `x * y` passes. -/
theorem ex_mulGuard {x y : B256} (h : x * y / x = y ∨ x = 0) :
    (B256.eqCheck (x * y / x) y ||| B256.eqCheck x 0) ≠ 0 := by
  unfold B256.eqCheck
  rcases h with h1 | h1 <;> simp only [h1, ↓reduceIte] <;> split_ifs <;> decide

/-- An `ISZERO (LT x y)` guard passes when `¬ x < y`. -/
theorem ex_geGuard {x y : B256} (h : ¬ x < y) : B256.eqCheck (B256.ltCheck x y) 0 ≠ 0 := by
  unfold B256.ltCheck B256.eqCheck
  simp only [h, ↓reduceIte]
  decide

/-! ## The base a forward walk carries -/

/-- **The forward walk's base**: the pool's storage is `σ` slot by slot, the identity precompile
is ready, and the world invariant `W` (closed under the pool's own steps) holds. -/
structure ExLive (sevm : Sevm) (W : Devm → Prop) (b : Devm) (σ : Stor) : Prop where
  stor : ∀ x, (b.getStor sevm.currentTarget).get x = σ.get x
  id : IdReady sevm b
  wc : WClosed sevm W
  w : W b

namespace ExLive

variable {sevm : Sevm} {W : Devm → Prop} {b b' : Devm} {σ : Stor}

theorem sloadE {k : B256} (h : ExLive sevm W b σ) (e : b' = afterSload sevm b k) :
    ExLive sevm W b' σ := by
  subst e
  exact ⟨fun x => by rw [afterSload_getStor]; exact h.stor x, h.id.afterSload k, h.wc,
    h.wc.sload _ _ h.w⟩

theorem sstoreE {k v : B256} (h : ExLive sevm W b σ) (e : b' = afterSstore sevm b k v) :
    ExLive sevm W b' (σ.set k v) := by
  subst e
  exact ⟨fun x => by simp only [afterSstore_getStor_self, Stor.get_set_ite, h.stor],
    h.id.afterSstore k v, h.wc, h.wc.sstore _ _ _ h.w⟩

/-- The word an `SLOAD` read, as `σ`'s. -/
theorem val {k v : B256} (h : ExLive sevm W b σ) (hv : v = b.getStorVal sevm.currentTarget k) :
    v = σ.get k := by
  rw [hv, getStorVal_eq, h.stor]

theorem sha {rd : Bytes} (h : ExLive sevm W b σ) (hs : ShaCallPost b b' rd) :
    ExLive sevm W b' σ :=
  ⟨fun x => by rw [hs.stor]; exact h.stor x,
    h.id.of_rel ⟨hs.stor, hs.code, hs.addrs, hs.logs, hs.output, hs.error⟩, h.wc,
    h.wc.sha _ _ _ hs h.w⟩

theorem st (h : ExLive sevm W b σ) (S : List B256) (M : Mem) (G : Nat) :
    ExLive sevm W (St b S M G) σ :=
  ⟨fun x => h.stor x, ⟨h.id.nodeleg, h.id.warm, h.id.pre, h.id.fork⟩, h.wc, h.wc.st _ _ _ _ h.w⟩

theorem addLogE (h : ExLive sevm W b σ) (l : Log) : ExLive sevm W (b.addLog l) σ :=
  ⟨fun x => h.stor x, ⟨h.id.nodeleg, h.id.warm, h.id.pre, h.id.fork⟩, h.wc, h.wc.log _ _ h.w⟩

end ExLive

/-- **A one-word `STATICCALL` answered by its premise, forward**: the call at `(ii, is, oi)`
reading `A`, the `RETURNDATASIZE > 31` test, and the answer loaded back (`PUSH; MLOAD oi`), up
to the tree `f2` after the load, over an image carrier. -/
theorem rxe_staticWord {sevm : Sevm} {W W' : Devm → Prop} {σ : Stor} {b : Devm} {S : List B256}
    {M : Mem} {img : Bytes} {G U : Nat} {t A ii is oi : B256} {data : Bytes} {o s : Nat}
    {Q : Outcome → Prop} {f : SFunc} (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hp : StaticWordOkAt sevm W W' t data A U ii is oi) (hU : U ≤ G) (hG : G < 2 ^ 256)
    (hin : (M.read ii.toNat is.toNat).1 = data) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hoi : oi.toNat = o)
    (hext : (M.extends [(ii.toNat, is.toNat), (oi.toNat, 0x20)]).size = s) (hfit : o + 0x20 ≤ s)
    (k : ∀ (d : Devm) (M' : Mem) (out : Bytes), ExLive sevm W' d σ →
      Mem.Reads M' (Bytes.writeAt img o (out.take 0x20)) → Mem.Wf M' → M'.size = s →
      32 ≤ out.length → out.length < 2 ^ 256 → Bytes.toB256 (out.take 32) = A →
      d.returnData = out → G ≤ d.gasLeft + U → d.gasLeft ≤ G →
      SFunc.RunEx cert.prog sevm (St d (1 :: S) M' d.gasLeft) f Q) :
    SFunc.RunEx cert.prog sevm (St b (Nat.toB256 G :: t :: ii :: is :: oi :: 0x20 :: S) M G)
      (.next (.exec .staticcall) f) Q := by
  obtain ⟨d, out, hrun, hpost, hlen, hlt, hA, hg1, hg2, hWd, hidd⟩ := hp b S M G hL.w hU hG hin
  have hd := hpost.eq_St
  rw [show (0x20 : B256).toNat = 0x20 by decide] at hd
  subst hoi
  have hsz' : ((M.extends [(ii.toNat, is.toNat), (oi.toNat, 0x20)]).write oi.toNat
      (out.take 0x20)).size = s := by
    rw [Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
  obtain ⟨r, hr, hq⟩ := k d _ out ⟨fun x => by rw [hpost.stor]; exact hL.stor x, hidd hL.id, hW'c, hWd⟩
    ((hR.extends _).write (hW.extends _) _ _) ((hW.extends _).write _ _) hsz' hlen hlt hA
    hpost.returnData hg1 hg2
  exact ⟨r, .next hrun (Eq.mpr (congrArg (fun x => SFunc.RunExact cert.prog sevm x f r) hd) hr), hq⟩

/-- A call's answer word read back where the call wrote it. -/
theorem ex_ans_read (img out : Bytes) (o : Nat) (h : 32 ≤ out.length) :
    Bytes.toB256 ((Bytes.writeAt img o (out.take 32)).sliceD o 32 0) = Bytes.toB256 (out.take 32) := by
  have e := Bytes.sliceD_writeAt img (out.take 32) o
  rw [List.length_take, Nat.min_eq_left h] at e
  rw [e]

/-- `RETURNDATASIZE > 31` for a reply of at least 32 bytes. -/
theorem ex_rds_gt {out : Bytes} (h : 32 ≤ out.length) (hlt : out.length < 2 ^ 256) :
    B256.gtCheck (Nat.toB256 out.length) (Bytes.toB256 [0x1f]) ≠ 0 := by
  apply gtCheck_ne_zero_of_lt
  rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hlt,
    show (Bytes.toB256 [0x1f]).toNat = 31 by decide]
  omega

/-- A branch condition the walk's context or the kernel settles. -/
macro "xbr" : tactic => `(tactic| first | assumption | decide)

/-- A not-taken branch condition the walk's context or the kernel settles. -/
macro "xbr0" : tactic => `(tactic| first | assumption | decide)

/-- Normalize the words a walk's `MLOAD`s pushed: a word write at the read's offset gives its
word, a disjoint one is skipped. -/
macro "wsimp" : tactic => `(tactic| simp (disch := first | decide | (simp only
    [B256.length_toBytes, List.length_take, List.length_sliceD, List.length_cons, List.length_nil,
      List.length_append, transferFromSel, transferSel, burnFromSel, mintSel, balanceOfSel]; omega))
  only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self,
    Bytes.sliceD_writeAt_before, Bytes.sliceD_writeAt_after])

/-- A word write read back at an offset proved equal to the write's. -/
theorem WordAt.write_eq {img : Bytes} {o n : Nat} {w v : B256} (h : n = o) (hv : w = v) :
    WordAt (Bytes.writeAt img n w.toBytes) o v := h ▸ hv ▸ WordAt.write_self img n w

/-- One step of a carried-word search: a word write at the offset settles it, a disjoint word
write is skipped. -/
macro "wstep1" : tactic => `(tactic| first
  | refine WordAt.write_other ?_ (by
      simp only [B256.length_toBytes, List.length_take, List.length_sliceD, List.length_cons,
        List.length_nil, List.length_append, transferFromSel, transferSel, burnFromSel, mintSel,
        balanceOfSel]
      omega)
  | exact WordAt.write_eq (by decide) (by rfl))

/-- A carried word: peel the image's writes, then the context. -/
macro "wauto" : tactic => `(tactic| (repeat wstep1) <;> try assumption)

/-- A carried word: peel the image's writes, then the named fact (no context search). -/
macro "wautoH " h:term : tactic => `(tactic| (repeat wstep1) <;> exact $h)

end Blanc.Lift.Curve3Pool
