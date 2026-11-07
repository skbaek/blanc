import Blanc.Lift.Usdc.V2Family
import Blanc.Lift.Usdc.V2_1Frames
import Blanc.Lift.Usdc.ImplV2_1.Jumps

/-!
# FiatTokenV2_1: forward runs of `transfer`, `transferFrom` and `balanceOf`

SafeMath's messaged `sub` allocates its revert string, so the free-memory pointer moves: `0x80` to
`0xc0` across `_transfer`, and to `0x100` across `transferFrom`'s allowance debit. Generated from `V2Forward` by its tree labels and entry numbers; the images, bases and ledger
are `V2Family`'s.
-/

namespace Blanc.Lift.Usdc.ImplV2_1

open Jaune Blanc Blanc.Lift
open Blanc.Lift.AccumulatedWalk
open ImplV2 hiding balSlot allowSlot moveStor fromStor pausedByte listedByte lit1 lit3 lit4 lit9 lit10 lit36 e77_inv

local notation "m20" => Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-- **Entry 75, SafeMath `add`**, forward. -/
@[irreducible] noncomputable def e75W (sevm : Sevm) (b : Devm) (x y ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // x.toNat + y.toNat < 2 ^ 256 → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (x :: y :: ret :: S) M (X + c)) t_3e26_c75
        (.returned (St b ((x + y) :: S) M X))} :=
  ⟨_, fun hle room X => by
    have := ltCheck_add_zero hle
    xrun⟩

/-- **Entry 86, SafeMath `sub` with a message**, forward. -/
@[irreducible] noncomputable def e86W (sevm : Sevm) (b : Devm) (m x y ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // x.toNat ≤ y.toNat → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (m :: x :: y :: ret :: S) M (X + c)) t_4576_c86
        (.returned (St b ((y - x) :: S) M X))} :=
  ⟨_, fun hle room X => by
    have := B256.gtCheck_eq_zero_of_toNat_le hle
    xrun⟩

/-- **Entry 76, SafeMath `sub`, its first call**: the pointer `0x80` to `0xc0`. -/
@[irreducible] noncomputable def e76aW (sevm : Sevm) (b : Devm) (x y ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // FpM (Bytes.toB256 [128]) 96 M → x.toNat ≤ y.toNat → S.length < 990 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (x :: y :: ret :: S) M (X + c)) t_3d4c_c76
        (.returned (St b ((y - x) :: S) (msgMem M 128 (Bytes.toB256 [64] + Bytes.toB256 [128]) subMsg) X))} :=
  ⟨_, fun hM hle room X => by
    xrun
    apply rk
    refine rx_mstoreMove hM (by decide) fun hM1 => ?_
    xrun
    apply rk
    refine rx_mstoreGrow (n := 160) (by xfp) (by decide) (by decide) rfl fun hM2 => ?_
    xrun
    xcallM e86W 4 [] hle (by xroom)
    xrun
    all_goals omega⟩

/-- **Entry 76, SafeMath `sub`, its second call**: the pointer `0xc0` to `0x100`. -/
@[irreducible] noncomputable def e76bW (sevm : Sevm) (b : Devm) (x y ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // FpM (Bytes.toB256 [64] + Bytes.toB256 [128]) 224 M → x.toNat ≤ y.toNat → S.length < 990 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (x :: y :: ret :: S) M (X + c)) t_3d4c_c76
        (.returned (St b ((y - x) :: S)
          (msgMem M 192 (Bytes.toB256 [64] + (Bytes.toB256 [64] + Bytes.toB256 [128])) subMsg) X))} :=
  ⟨_, fun hM hle room X => by
    xrun
    apply rk
    refine rx_mstoreMove hM (by decide) fun hM1 => ?_
    xrun
    apply rk
    refine rx_mstoreP (i0 := 192) (by xfp) (by decide) (by decide) (by decide) ?_
    xrun
    apply rk
    refine rx_mstoreGrow (n := 224) (by xfp) (by decide) (by decide) rfl fun hM2 => ?_
    xrun
    xcallM e86W 4 [] hle (by xroom)
    xrun
    all_goals omega⟩

/-- **Entry 73, `_transfer(owner, recipient, amount)`**, forward. -/
@[irreducible] noncomputable def e73W (sevm : Sevm) (b : Devm) (v t r ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      FpM (Bytes.toB256 [128]) 96 M → S.length < 980 → r.toAdr.toB256 ≠ 0 → t.toAdr.toB256 ≠ 0 →
      v.toNat ≤ (b.getStorVal sevm.currentTarget (kn r)).toNat →
      v.toNat + (((Devm.getStor b sevm.currentTarget).set (kn r)
        (b.getStorVal sevm.currentTarget (kn r) - v)).get (kn t)).toNat < 2 ^ 256 →
      ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (v :: t :: r :: ret :: S) M (X + c)) t_3b21_c73
        (.returned (St (e74Post sevm b v t r) S (e74Mem M v t r) X))} :=
  ⟨_, fun fork static hM room hr ht hle hnof X hX => by
    have hg : B256.gtCheck v (b.getStorVal sevm.currentTarget (kn r)) = 0 :=
      B256.gtCheck_eq_zero_of_toNat_le hle
    xrun
    xcallM e76aW 3 [] (by xfp) (by xnorm; with_reducible assumption) (by xroom)
    have hMa := msgMemA_fp (M := sc9 (sc9 M (r &&& m20)) (r &&& m20)) (by xfp)
    xrun
    apply rk
    refine rx_keccakRev (hMa.write 0 _ (by decide) (by decide)).wf (by with_reducible rfl) (by xfp) (by decide) (by decide) (by xroom) ?_
    xrun
    xcallM e75W 3 [] (by xnorm; with_reducible assumption) (by xroom)
    xrun
    apply rk
    refine rx_mstoreGrow (n := 192) (by xfp) (by decide) (by decide) rfl fun hMb => ?_
    xrun
    apply rk
    refine rx_log3At static (by with_reducible rfl) (by xfp) hMb (by decide) (by decide) (by decide) ?_
    xrun
    all_goals ((try unfold gCallStipend); omega)⟩

/-- **Entry 30, `transfer(to, value)`**, forward. -/
@[irreducible] noncomputable def e30W (sevm : Sevm) (b : Devm) (v t ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      FpM (Bytes.toB256 [128]) 96 M → S.length < 970 → Unlisted sevm b t →
      MoveOk sevm b v t sevm.caller.toB256 →
      ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (v :: t :: ret :: S) M (X + c)) t_2b65_c30
        (.returned (St (e74Post sevm (e28Pre sevm b t) v t sevm.caller.toB256) (Bytes.toB256 [1] :: S)
          (e74Mem (e28Mem sevm M t) v t sevm.caller.toB256) X))} :=
  ⟨_, fun fork static hM room un ok X hX => by
    obtain ⟨hp, hc, ht⟩ := un
    obtain ⟨h1, h2, h3, h4⟩ := ok
    simp only [toAdr_toB256] at h1
    xrun
    xcallMT e73W 4 [] fork static (by xfp) (by xroom) (by xnorm; with_reducible assumption)
      (by xnorm; with_reducible assumption) (by xnorm; with_reducible assumption)
      (by xnorm; with_reducible assumption)
    xrun
    all_goals ((try unfold gCallStipend); omega)⟩

/-- **The `transfer` frame, forward.** -/
@[irreducible] noncomputable def xferW (sevm : Sevm) (b : Devm) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      Guards sevm 0xa9059cbb (Bytes.toB256 [64]) → Unlisted sevm b (xTo sevm) →
      MoveOk sevm b (xVal sevm) (xTo sevm) sevm.caller.toB256 → ∀ G, 2300 ≤ G →
      SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + c)) t_0000_c0
        (.halted (retV fp1 (xferBase sevm b) [selW sevm]
          ((e74Mem (e28Mem sevm mem0 (xTo sevm)) (xVal sevm) (xTo sevm) sevm.caller.toB256).write 192 okW.toBytes)
          okW G))} :=
  ⟨_, fun fork static facts un ok G hG => by
    obtain ⟨value, short, args, sel⟩ := facts
    xrun
    xcallMT e30W 3 [] fork static (by xfp) (by xroom) un ok
    have hMc := e74Mem_fp (M := e28Mem sevm mem0 (xTo sevm)) (scw_fp (scw_fp (FpM.init (Bytes.toB256 [128])) _ _ (by decide)) _ _ (by decide)) (xVal sevm) (xTo sevm) sevm.caller.toB256
    xrun
    apply rk
    refine rx_mstoreP (i0 := 192) hMc (by decide) (by decide) (by decide) ?_
    xrun
    refine rk0 ?_
    refine rx_returnAt (i0 := 192) (n := 224) rfl hMc (hMc.write 192 _ (by decide) (by decide)) (by decide) (by decide) (by decide)
    all_goals omega⟩

/-- **Tree `0x1375` of entry 58, the allowance debit**, forward. -/
@[irreducible] noncomputable def e58TW (sevm : Sevm) (B : Devm) (v t r ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false → FpM fp1 224 M → S.length < 960 →
      v.toNat ≤ (B.getStorVal sevm.currentTarget (ak sevm r)).toNat → ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm
        (St B (t :: r :: sevm.caller.toB256 :: Bytes.toB256 [0] :: v :: t :: r :: ret :: S) M (X + c)) t_1375_c58
        (.returned (St (e59Debit sevm B v r) (Bytes.toB256 [1] :: S) (e59End sevm M r) X))} :=
  ⟨_, fun fork static hM room hA X hX => by
    xrun
    xcallM e76bW 3 [] (by xfp) hA (by xroom)
    have hMd := msgMemB_fp (M := e59Img sevm M r) (scw_fp (scw_fp hM _ _ (by decide)) _ _ (by decide))
    xrun
    all_goals ((try unfold gCallStipend); omega)⟩

/-- **Entry 58, `transferFrom(from, to, value)`**, forward. -/
@[irreducible] noncomputable def e58W (sevm : Sevm) (b : Devm) (v t r ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      FpM (Bytes.toB256 [128]) 96 M → S.length < 960 → E59Ok sevm b v t r → ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (v :: t :: r :: ret :: S) M (X + c)) t_10e9_c58
        (.returned (St (e59Post sevm b v t r) (Bytes.toB256 [1] :: S)
          (e59End sevm (e74Mem (e59Mem sevm M t r) v t r) r) X))} :=
  ⟨_, fun fork static hM room facts X hX => by
    obtain ⟨hp, hc, hr, ht, ha, ⟨h1, h2, h3, h4⟩, ha2⟩ := facts
    xrun
    xcallMT e73W 4 [] fork static (by xfp) (by xroom) (by xnorm; with_reducible assumption)
      (by xnorm; with_reducible assumption) (by xnorm; with_reducible assumption)
      (by xnorm; with_reducible assumption)
    exact (e58TW sevm _ v t r ret S _).2 fork static (e74Mem_fp (M := e59Mem sevm M t r) (scw_fp (scw_fp (scw_fp (scw_fp (scw_fp hM _ _ (by decide)) _ _ (by decide)) _ _ (by decide)) _ _ (by decide)) _ _ (by decide)) v t r) (by xroom) ha2 X hX
    all_goals ((try unfold gCallStipend); omega)⟩

/-- **The `transferFrom` frame, forward.** -/
@[irreducible] noncomputable def pullW (sevm : Sevm) (b : Devm) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      Guards sevm 0x23b872dd (Bytes.toB256 [96]) → E59Ok sevm b (pVal sevm) (pTo sevm) (pFrom sevm) → ∀ G, 2300 ≤ G →
      SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + c)) t_0000_c0
        (.halted (retV fp2 (pullBase sevm b) [selW sevm] ((pullEnd sevm).write 256 okW.toBytes) okW G))} :=
  ⟨_, fun fork static facts ok G hG => by
    obtain ⟨value, short, args, sel⟩ := facts
    xrun
    xcallMT e58W 4 [] fork static (by xfp) (by xroom) ok
    have hMd : FpM fp2 256 (pullEnd sevm) := e59End_fp (e74Mem_fp (scw_fp (scw_fp (scw_fp (scw_fp (scw_fp (FpM.init (Bytes.toB256 [128])) _ _ (by decide)) _ _ (by decide)) _ _ (by decide)) _ _ (by decide)) _ _ (by decide)) _ _ _) _
    xrun
    apply rk
    refine rx_mstoreGrow (n := 256) hMd (by decide) (by decide) rfl fun hMe => ?_
    xrun
    refine rk0 ?_
    refine rx_returnAt (i0 := 256) (n := 288) rfl hMd hMe (by decide) (by decide) (by decide)
    all_goals omega⟩

/-- **Entry 39, `balanceOf(a)`**, forward. -/
@[irreducible] noncomputable def e39W (sevm : Sevm) (b : Devm) (a ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → FpM (Bytes.toB256 [128]) 96 M → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (a :: ret :: S) M (X + c)) t_2798_c39
        (.returned (St (afterSload sevm b (ky a)) (b.getStorVal sevm.currentTarget (ky a) :: S)
          (sc9 M (m20 &&& a)) X))} :=
  ⟨_, fun fork hM room X => by
    xrun⟩

/-- **The `balanceOf` frame, forward**, static or not. -/
@[irreducible] noncomputable def balW (sevm : Sevm) (b : Devm) :
    {c : Nat // CoveredFork sevm.benvStat.fork → Guards sevm 0x70a08231 (Bytes.toB256 [32]) → ∀ G,
      SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + c)) t_0000_c0
        (.halted (retV (Bytes.toB256 [128]) (afterSload sevm b (ky (bHolder sevm))) [selW sevm]
          ((sc9 mem0 (m20 &&& bHolder sevm)).write 128 (bAns sevm b).toBytes) (bAns sevm b) G))} :=
  ⟨_, fun fork facts G => by
    obtain ⟨value, short, args, sel⟩ := facts
    xrun
    xcallM e39W 2 [] fork (by xfp) (by xroom)
    xrun
    refine rk0 ?_
    apply rx_returnP
    · with_reducible rfl
    · xfp
    · xfp
    · decide
    · decide⟩

/-! ## The charges -/

section Charges

variable (sevm : Sevm) (b : Devm) (v t r ret a : B256) (S : List B256) (M : Mem)

theorem e75W_le : (e75W sevm b v t ret S M).1 ≤ 100 := by
  unfold e75W; dsimp only; xcost []

theorem e86W_le (m : B256) : (e86W sevm b m v t ret S M).1 ≤ 100 := by
  unfold e86W; dsimp only; xcost []

theorem e76aW_le : (e76aW sevm b v t ret S M).1 ≤ 300 := by
  unfold e76aW; dsimp only; xcost [e86W_le]

theorem e76bW_le : (e76bW sevm b v t ret S M).1 ≤ 300 := by
  unfold e76bW; dsimp only; xcost [e86W_le]

theorem e73W_le : (e73W sevm b v t r ret S M).1 ≤ 58000 := by
  unfold e73W; dsimp only; xcost [e76aW_le, e75W_le]

theorem e30W_le : (e30W sevm b v t ret S M).1 ≤ 67000 := by
  unfold e30W; dsimp only; xcost [e73W_le]

theorem xferW_le : (xferW sevm b).1 ≤ 68000 := by
  unfold xferW; dsimp only; xcost [e30W_le]

theorem e58TW_le : (e58TW sevm b v t r ret S M).1 ≤ 25000 := by
  unfold e58TW; dsimp only; xcost [e76bW_le]

theorem e58W_le : (e58W sevm b v t r ret S M).1 ≤ 95000 := by
  unfold e58W; dsimp only; xcost [e73W_le, e58TW_le]

theorem pullW_le : (pullW sevm b).1 ≤ 96000 := by
  unfold pullW; dsimp only; xcost [e58W_le]

theorem e39W_le : (e39W sevm b a ret S M).1 ≤ 2300 := by
  unfold e39W; dsimp only; xcost []

theorem balW_le : (balW sevm b).1 ≤ 3000 := by
  unfold balW; dsimp only; xcost [e39W_le]

end Charges

/-! ## What a frame leaves -/

/-- **`transfer(dst, v)` from a frame entry, forward.** -/
theorem xfer_lands {sevm : Sevm} {pre : Devm} {dst : Adr} {v : B256}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (g : Guards sevm 0xa9059cbb (Bytes.toB256 [64])) (hdst : xTo sevm = dst.toB256) (hv : xVal sevm = v)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 70300 ≤ pre.gasLeft)
    (hf : MoveFits (Devm.getStor pre sevm.currentTarget) sevm.caller dst v) :
    ∃ post used, used ≤ 68000 ∧ FrameLands cert.prog sevm pre post used 1
      (ImplV2.moveStor (Devm.getStor pre sevm.currentTarget) sevm.caller dst v)
      ((getOrigAcct sevm sevm.currentTarget).stor = Devm.getStor pre sevm.currentTarget ∧
        sevm.currentTarget ∉ pre.createdAccounts ∧ ImplV2.balSlot sevm.caller ≠ ImplV2.balSlot dst) := by
  have ta : (xTo sevm).toAdr = dst := by rw [hdst, toAdr_toB256]
  have un : Unlisted sevm pre (xTo sevm) := unlisted_of hf.paused hf.lsrc (by rw [ta]; exact hf.ldst)
  have ok : MoveOk sevm pre (xVal sevm) (xTo sevm) sevm.caller.toB256 := moveOk_of rfl hdst (by rw [hv]; exact hf)
  refine ⟨_, _, xferW_le sevm pre, frameLands_retV rfl (K := 68000)
    (fun G hG => (xferW sevm pre).2 fork static g un ok G hG) hs hm (xferW_le sevm pre) (by omega)
    ?_ ?_ okW_eq ?_⟩
  · exact (((((Keeps.refl sevm pre).sload _).sload _).sload _).e74V2 _ _ _)
  · unfold xferBase
    rw [e74Post_getStor]
    simp only [afterSload_getStor, toAdr_toB256, ta, hv]
  · rintro ⟨hor, hcr, hne⟩
    refine le_trans (le_of_eq (afterSload_refundCounter.symm.trans
      (afterSload_refundCounter.symm.trans afterSload_refundCounter.symm)))
      (e74Post_refund (σ := Devm.getStor pre sevm.currentTarget)
        (by simpa only [afterSload_createdAccounts] using hcr) hor ?_ ?_ ?_)
    · simp only [afterSload_getStor]
    · simp only [afterSload_getStor]
    · rw [toAdr_toB256, ta]; exact hne

/-- **`transferFrom(src, dst, v)` from a frame entry, forward.** -/
theorem pull_lands {sevm : Sevm} {pre : Devm} {src dst : Adr} {v : B256}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (g : Guards sevm 0x23b872dd (Bytes.toB256 [96])) (hsrc : pFrom sevm = src.toB256)
    (hdst : pTo sevm = dst.toB256) (hv : pVal sevm = v)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 98300 ≤ pre.gasLeft)
    (hf : PullFits (Devm.getStor pre sevm.currentTarget) src sevm.caller dst v) :
    ∃ post used, used ≤ 96000 ∧ FrameLands cert.prog sevm pre post used 1
      (ImplV2.fromStor (Devm.getStor pre sevm.currentTarget) src sevm.caller dst v)
      ((getOrigAcct sevm sevm.currentTarget).stor = Devm.getStor pre sevm.currentTarget ∧
        sevm.currentTarget ∉ pre.createdAccounts ∧
        ImplV2.allowSlot src sevm.caller ≠ ImplV2.balSlot src ∧ ImplV2.allowSlot src sevm.caller ≠ ImplV2.balSlot dst ∧
        ImplV2.balSlot src ≠ ImplV2.balSlot dst) := by
  have tz : (pFrom sevm).toAdr = src := by rw [hsrc, toAdr_toB256]
  have ty : (pTo sevm).toAdr = dst := by rw [hdst, toAdr_toB256]
  have hgs : ∀ a, Devm.getStor (e59Pre sevm pre (pTo sevm) (pFrom sevm)) a = Devm.getStor pre a := fun a => by
    simp only [afterSload_getStor]
  have ok : E59Ok sevm pre (pVal sevm) (pTo sevm) (pFrom sevm) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, moveOk_of hsrc hdst (by rw [hv]; exact hf.move), ?_⟩
    · rw [gsv, lit1]; exact hf.move.paused
    · rw [gsv, lit3]; exact hf.lsp
    · unfold kL; rw [gsv, lit3, tz]; exact hf.move.lsrc
    · unfold kL; rw [gsv, lit3, ty]; exact hf.move.ldst
    · rw [gsv, tz, hv, lit10]; exact B256.gtCheck_eq_zero_of_toNat_le hf.allow
    · rw [gsv, e74Post_getStor, hgs, ak_allow, tz, ty, hv]; exact hf.allow'
  refine ⟨_, _, pullW_le sevm pre, frameLands_retV rfl (K := 96000)
    (fun G hG => (pullW sevm pre).2 fork static g ok G hG) hs hm (pullW_le sevm pre) (by omega)
    ?_ ?_ okW_eq ?_⟩
  · exact ((((((((Keeps.refl sevm pre).sload _).sload _).sload _).sload _).sload _).e74V2 _ _ _).e59V2 _ _)
  · unfold pullBase e59Post
    rw [e59Debit_getStor, e74Post_getStor, hgs, tz, ty, hv]
    rfl
  · rintro ⟨hor, hcr, ha1, ha2, hne⟩
    unfold pullBase e59Post e59Debit
    have hcr' : sevm.currentTarget ∉ (e59Pre sevm pre (pTo sevm) (pFrom sevm)).createdAccounts := by
      simpa only [afterSload_createdAccounts] using hcr
    have hrB := e74Post_refund (sevm := sevm) (v := pVal sevm) (t := pTo sevm) (r := pFrom sevm)
      (σ := Devm.getStor pre sevm.currentTarget) hcr' hor (by rw [hgs]) (by rw [hgs]) (by rw [tz, ty]; exact hne)
    have hk := (((((((Keeps.refl sevm pre).sload (Bytes.toB256 [1])).sload (mapSlot sevm.caller.toB256 (Bytes.toB256 [3]))).sload
      (mapSlot (pFrom sevm &&& m20) (Bytes.toB256 [3]))).sload (mapSlot (pTo sevm &&& m20) (Bytes.toB256 [3]))).sload
      (ak sevm (pFrom sevm))).e74V2 (pVal sevm) (pTo sevm) (pFrom sevm))
    refine le_trans ?_ (sstore_ge (by
        rw [afterSload_createdAccounts, hk.created]; exact hcr) hor ?_)
    · simp only [afterSload_refundCounter]
      refine le_trans ?_ hrB
      simp only [afterSload_refundCounter]
      exact le_refl _
    · rw [afterSload_getStor, e74Post_getStor, hgs, ak_allow, tz, ty]
      unfold ImplV2.moveStor
      rw [Stor.get_set_ne _ ha2.symm, Stor.get_set_ne _ ha1.symm]

/-- **`balanceOf(a)` from a frame entry, forward**, static or not. -/
theorem bal_lands {sevm : Sevm} {pre : Devm} {a : Adr}
    (fork : CoveredFork sevm.benvStat.fork) (g : Guards sevm 0x70a08231 (Bytes.toB256 [32]))
    (hholder : bHolder sevm = a.toB256)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 5300 ≤ pre.gasLeft) :
    ∃ post used, used ≤ 3000 ∧ FrameLands cert.prog sevm pre post used
      ((Devm.getStor pre sevm.currentTarget).get (ImplV2.balSlot a)) (Devm.getStor pre sevm.currentTarget) True := by
  refine ⟨_, _, balW_le sevm pre, frameLands_retV rfl (K := 3000)
    (fun G _ => (balW sevm pre).2 fork g G) hs hm (balW_le sevm pre) (by omega)
    ((Keeps.refl sevm pre).sload _) ?_ ?_ ?_⟩
  · rw [afterSload_getStor]
  · unfold bAns
    rw [gsv, ky_bal, hholder, toAdr_toB256]
  · exact fun _ => le_of_eq afterSload_refundCounter.symm

end Blanc.Lift.Usdc.ImplV2_1
