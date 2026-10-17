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

/-- A branch condition the walk's context or the kernel settles. -/
macro "xbr" : tactic => `(tactic| first | assumption | decide)

/-- A not-taken branch condition the walk's context or the kernel settles. -/
macro "xbr0" : tactic => `(tactic| first | assumption | decide)

/-- Normalize the words a walk's `MLOAD`s pushed: a word write at the read's offset gives its
word, a disjoint one is skipped. -/
macro "wsimp" : tactic => `(tactic| simp (disch := decide) only
  [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self])

/-- A word write read back at an offset proved equal to the write's. -/
theorem WordAt.write_eq {img : Bytes} {o n : Nat} {w v : B256} (h : n = o) (hv : w = v) :
    WordAt (Bytes.writeAt img n w.toBytes) o v := h ▸ hv ▸ WordAt.write_self img n w

/-- One step of a carried-word search: a word write at the offset settles it, a disjoint word
write is skipped. -/
macro "wstep1" : tactic => `(tactic| first
  | exact WordAt.write_eq (by decide) (by rfl)
  | refine WordAt.write_other ?_ (by
      simp only [B256.length_toBytes, List.length_take, List.length_sliceD, List.length_cons,
        List.length_nil, List.length_append]
      omega))

/-- A carried word: peel the image's writes, then the context. -/
macro "wauto" : tactic => `(tactic| (repeat wstep1) <;> try assumption)

end Blanc.Lift.Curve3Pool
