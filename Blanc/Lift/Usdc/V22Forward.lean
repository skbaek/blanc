import Blanc.Lift.Usdc.TransferLiveImpl
import Blanc.Lift.WalkFpMove
import Blanc.Lift.Usdc.RefineAdminBits

/-!
# FiatTokenV2_2: forward runs of `transferFrom` and `balanceOf`, with what its frames leave
-/

namespace Blanc.Composition.UsdcLive

open Blanc.Lift.AccumulatedWalk
open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Impl

local notation "m20" => Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
local notation "l255" => Bytes.toB256 [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-- The allowance key as the walk computes it. -/
abbrev kA' (sevm : Sevm) (z : B256) : B256 :=
  mapSlot sevm.caller.toB256 (mapSlot (z &&& m20) (Bytes.toB256 [10]))

/-- The base after `transferFrom`'s modifiers read `paused` and three blacklist flags, and its
allowance check. -/
abbrev e68Pre (sevm : Sevm) (b : Devm) (y z : B256) : Devm :=
  afterSload sevm (afterSload sevm (afterSload sevm (afterSload sevm (afterSload sevm b (Bytes.toB256 [1]))
    (ky sevm.caller.toB256)) (ky z)) (ky y)) (kA' sevm z)

/-- The scratch image of the allowance hash. -/
abbrev sA (M : Mem) (sevm : Sevm) (z : B256) : Mem :=
  ((((M.write 0 (z &&& m20).toBytes).write 32 (Bytes.toB256 [10]).toBytes).write 0
    sevm.caller.toB256.toBytes).write 32 (mapSlot (z &&& m20) (Bytes.toB256 [10])).toBytes)

/-- The allowance key of owner `z` for the frame's caller, as `transferFrom` reads it. -/
abbrev kA (sevm : Sevm) (z : B256) : B256 :=
  mapSlot sevm.caller.toB256 (mapSlot z.toAdr.toB256 (Bytes.toB256 [10]))

/-- The base `transferFrom`'s body returns with: the move, then the allowance read and its debit. -/
def e68Post (sevm : Sevm) (b : Devm) (x y z : B256) : Devm :=
  afterSstore sevm (afterSload sevm (e93Post sevm (e68Pre sevm b y z) x y z) (kA' sevm z)) (kA' sevm z)
    ((e93Post sevm (e68Pre sevm b y z) x y z).getStorVal sevm.currentTarget (kA' sevm z) - x)

/-- The memory `transferFrom`'s body returns with. -/
abbrev e68Mem (sevm : Sevm) (M : Mem) (x y z : B256) : Mem :=
  sA (sA (e93Mem (sA (sc9 (sc9 (sc9 M (m20 &&& sevm.caller.toB256)) (m20 &&& z)) (m20 &&& y)) sevm z) x y z) sevm z) sevm z

/-- The checks `transferFrom(z, y, x)`'s body makes, in the forms its walk meets them. -/
structure E68Ok (sevm : Sevm) (b : Devm) (x y z : B256) : Prop where
  paused : (Bytes.toB256 [255] &&& b.getStorVal sevm.currentTarget (Bytes.toB256 [1]) /
    Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) = 0
  fc : B256.eqCheck (Bytes.toB256 [1]) (b.getStorVal sevm.currentTarget (kC sevm) >>>
    (Bytes.toB256 [255]).toNat) = 0
  fz : B256.eqCheck (Bytes.toB256 [1]) (b.getStorVal sevm.currentTarget (kT z) >>>
    (Bytes.toB256 [255]).toNat) = 0
  fy : B256.eqCheck (Bytes.toB256 [1]) (b.getStorVal sevm.currentTarget (kT y) >>>
    (Bytes.toB256 [255]).toNat) = 0
  hA : B256.gtCheck x (b.getStorVal sevm.currentTarget (kA sevm z)) = 0
  hz : z.toAdr.toB256 ≠ 0
  hy : y.toAdr.toB256 ≠ 0
  hle : B256.gtCheck x (l255 &&& b.getStorVal sevm.currentTarget (kT z)) = 0
  hcr : x.toNat + (l255 &&& ((Devm.getStor b sevm.currentTarget).set (kT z)
    ((l255 &&& b.getStorVal sevm.currentTarget (kT z)) - x)).get (kT y)).toNat ≤ 2 ^ 255 - 1
  fy' : B256.eqCheck (Bytes.toB256 [1]) (((Devm.getStor b sevm.currentTarget).set (kT z)
    ((l255 &&& b.getStorVal sevm.currentTarget (kT z)) - x)).get (kT y) >>>
      (Bytes.toB256 [255]).toNat) = 0
  hA2 : x.toNat ≤ ((e93Post sevm (e68Pre sevm b y z) x y z).getStorVal sevm.currentTarget (kA' sevm z)).toNat

/-- **Entry 68, the body of `transferFrom(from, to, value)`**, forward. -/
@[irreducible] noncomputable def e68W (sevm : Sevm) (b : Devm) (x y z ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      FpM (Bytes.toB256 [128]) 96 M → S.length < 960 → E68Ok sevm b x y z →
      ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (x :: y :: z :: ret :: S) M (X + c)) t_1437_c68
        (.returned (St (e68Post sevm b x y z) (Bytes.toB256 [1] :: S) (e68Mem sevm M x y z) X))} :=
  ⟨_, fun fork static hM room facts X hX => by
    obtain ⟨hp, hfc, hfz, hfy, hA, hz, hy, hle, hcr, hfy', hA2⟩ := facts
    xrun
    xcallM e83W 2 [_] fork (by xfp) (by xroom)
    xrun
    xcallM e83W 2 [_] fork (by xfp) (by xroom)
    xrun
    xcallM e83W 2 [_] fork (by xfp) (by xroom)
    xrun
    xcallMT e93W 4 [] fork static (by xfp) (by xroom) (by xnorm; with_reducible assumption)
      (by xnorm; with_reducible assumption) (by xnorm; with_reducible assumption)
      (by xnorm; with_reducible assumption) (by xnorm; with_reducible assumption)
      (by xnorm; with_reducible assumption)
    xrun
    xcallM e100W 3 [] hA2 (by xroom)
    xrun
    all_goals ((try unfold gCallStipend); omega)⟩

/-- `transferFrom`'s arguments as its wrapper decodes them. -/
abbrev pFrom (sevm : Sevm) : B256 := m20 &&& Sevm.dataWord sevm (Bytes.toB256 [4])
abbrev pTo (sevm : Sevm) : B256 := m20 &&& Sevm.dataWord sevm (Bytes.toB256 [4] + Bytes.toB256 [32])
abbrev pVal (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [64] + Bytes.toB256 [4])

/-- The prologue's image. -/
abbrev mem0 : Mem := Mem.empty.write 64 (Bytes.toB256 [128]).toBytes

/-- The base `transferFrom` halts from. -/
abbrev pullBase (sevm : Sevm) (b : Devm) : Devm := e68Post sevm b (pVal sevm) (pTo sevm) (pFrom sevm)

/-- The image `transferFrom` halts with. -/
abbrev pullMem (sevm : Sevm) : Mem :=
  (e68Mem sevm mem0 (pVal sevm) (pTo sevm) (pFrom sevm)).write 128 okW.toBytes

/-- **The `transferFrom` frame, forward.** -/
@[irreducible] noncomputable def pullW (sevm : Sevm) (b : Devm) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      Guards sevm 0x23b872dd (Bytes.toB256 [96]) → E68Ok sevm b (pVal sevm) (pTo sevm) (pFrom sevm) →
      ∀ G, 2300 ≤ G →
      SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + c)) t_0000_c0
        (.halted (retV (Bytes.toB256 [128]) (pullBase sevm b) [selW sevm] (pullMem sevm) okW G))} :=
  ⟨_, fun fork static facts ok G hG => by
    obtain ⟨value, short, args, sel⟩ := facts
    xrun
    xcallMT e68W 4 [] fork static (by xfp) (by xroom) ok
    xrun
    refine rk0 ?_
    apply rx_returnP
    · with_reducible rfl
    · xfp
    · xfp
    · decide
    · decide
    all_goals omega⟩

/-- **Entry 46, the body of `balanceOf(a)`**, forward. -/
@[irreducible] noncomputable def e46W (sevm : Sevm) (b : Devm) (a ret : B256) (S : List B256) (M : Mem) (n : Nat) :
    {c : Nat // CoveredFork sevm.benvStat.fork →
      FpM (Bytes.toB256 [128]) n M → S.length < 990 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (a :: ret :: S) M (X + c)) t_2adf_c46
        (.returned (St (afterSload sevm b (ky a))
          ((l255 &&& b.getStorVal sevm.currentTarget (ky a)) :: S) (sc9 M (m20 &&& a)) X))} :=
  ⟨_, fun fork hM room X => by
    xrun
    xcallM e96W 2 [_] fork (by xfp) (by xroom)
    xrun⟩

/-- `balanceOf`'s argument as its wrapper decodes it. -/
abbrev bHolder (sevm : Sevm) : B256 := m20 &&& Sevm.dataWord sevm (Bytes.toB256 [4])

/-- The answer of `balanceOf`. -/
abbrev bAns (sevm : Sevm) (b : Devm) : B256 :=
  l255 &&& b.getStorVal sevm.currentTarget (ky (bHolder sevm))

/-- **The `balanceOf` frame, forward**, static or not. -/
@[irreducible] noncomputable def balW (sevm : Sevm) (b : Devm) :
    {c : Nat // CoveredFork sevm.benvStat.fork → Guards sevm 0x70a08231 (Bytes.toB256 [32]) → ∀ G,
      SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + c)) t_0000_c0
        (.halted (retV (Bytes.toB256 [128]) (afterSload sevm b (ky (bHolder sevm))) [selW sevm]
          ((sc9 mem0 (m20 &&& bHolder sevm)).write 128 (bAns sevm b).toBytes) (bAns sevm b) G))} :=
  ⟨_, fun fork facts G => by
    obtain ⟨value, short, args, sel⟩ := facts
    xrun
    xcallM e46W 2 [_] fork (by xfp) (by xroom)
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

variable (sevm : Sevm) (b : Devm) (x y z ret a : B256) (S : List B256) (M : Mem) (n : Nat)

theorem e83W_le : (e83W sevm b a ret S M n).1 ≤ 2300 := by
  unfold e83W; dsimp only; xcost []

theorem e96W_le : (e96W sevm b a ret S M n).1 ≤ 2300 := by
  unfold e96W; dsimp only; xcost []

theorem e100W_le : (e100W sevm b x y ret S M).1 ≤ 100 := by
  unfold e100W; dsimp only; xcost []

theorem e98W_le : (e98W sevm b x y ret S M).1 ≤ 100 := by
  unfold e98W; dsimp only; xcost []

theorem e99W_le : (e99W sevm b x y ret S M n).1 ≤ 27000 := by
  unfold e99W; dsimp only; xcost [e83W_le]

theorem e93W_le : (e93W sevm b x y z ret S M).1 ≤ 64000 := by
  unfold e93W; dsimp only; xcost [e96W_le, e100W_le, e99W_le, e98W_le]

theorem e37W_le : (e37W sevm b x y ret S M).1 ≤ 71000 := by
  unfold e37W; dsimp only; xcost [e83W_le, e93W_le]

theorem implXferW_le : (implXferW sevm b).1 ≤ 72000 := by
  unfold implXferW; dsimp only; xcost [e37W_le]

theorem e68W_le : (e68W sevm b x y z ret S M).1 ≤ 101000 := by
  unfold e68W; dsimp only; xcost [e83W_le, e93W_le, e100W_le]

theorem pullW_le : (pullW sevm b).1 ≤ 102000 := by
  unfold pullW; dsimp only; xcost [e68W_le]

theorem e46W_le : (e46W sevm b a ret S M n).1 ≤ 2500 := by
  unfold e46W; dsimp only; xcost [e96W_le]

theorem balW_le : (balW sevm b).1 ≤ 3500 := by
  unfold balW; dsimp only; xcost [e46W_le]

end Charges

/-! ## What a frame leaves -/

theorem ky_bal (a : B256) : ky a = balSlot a.toAdr := by
  unfold ky balSlot
  rw [ff20_and_word, lit9]

theorem ky'_bal (a : B256) : ky' a = balSlot a.toAdr := by
  unfold ky' balSlot
  rw [word_ff20, lit9]

theorem kT_bal (a : B256) : kT a = balSlot a.toAdr := by
  unfold kT balSlot
  rw [lit9]

theorem kC_bal (sevm : Sevm) : kC sevm = balSlot sevm.caller := by
  unfold kC balSlot
  rw [lit9]

theorem kA_allow (sevm : Sevm) (z : B256) : kA sevm z = allowSlot z.toAdr sevm.caller := by
  unfold kA allowSlot
  rw [lit10]

theorem kA'_allow (sevm : Sevm) (z : B256) : kA' sevm z = allowSlot z.toAdr sevm.caller := by
  unfold kA' allowSlot
  rw [word_ff20, lit10]

theorem _root_.Blanc.Lift.AccumulatedWalk.Keeps.e93 {sevm : Sevm} {pre B : Devm} (h : Keeps sevm pre B) (x y z : B256) :
    Keeps sevm pre (e93Post sevm B x y z) := by
  unfold e93Post e93Debited
  exact ((((((((h.sload _).sload _).sload _).sstore _ _).sload _).sload _).sstore _ _).log _)

/-- `_transfer`'s storage, word by word. -/
abbrev mvWords (σ : Stor) (a d : Adr) (x : B256) : Stor :=
  (σ.set (balSlot a) ((l255 &&& σ.get (balSlot a)) - x)).set (balSlot d)
    (x + (l255 &&& (σ.set (balSlot a) ((l255 &&& σ.get (balSlot a)) - x)).get (balSlot d)))

theorem e93Post_getStor (sevm : Sevm) (b : Devm) (x y z : B256) :
    Devm.getStor (e93Post sevm b x y z) sevm.currentTarget =
      mvWords (Devm.getStor b sevm.currentTarget) z.toAdr y.toAdr x := by
  unfold e93Post e93Debited
  simp only [Devm.addLog_getStor, afterSstore_getStor_self, afterSload_getStor, gsv, ky_bal, ky'_bal]

/-- The word form of a move is its ledger form, inside the bounds. -/
theorem mvWords_eq {σ : Stor} {a d : Adr} {x : B256} (hle : x.toNat ≤ balanceBits (σ.get (balSlot a)))
    (hb : balanceBits ((debitStor σ a x.toNat).get (balSlot d)) + x.toNat ≤ 2 ^ 255 - 1) :
    mvWords σ a d x = creditStor (debitStor σ a x.toNat) d x.toNat := by
  have h1 : (l255 &&& σ.get (balSlot a)) - x = Nat.toB256 (balanceBits (σ.get (balSlot a)) - x.toNat) := by
    rw [sub_word (by rw [l255_and_toNat]; exact hle), l255_and_toNat]
  have hset : σ.set (balSlot a) ((l255 &&& σ.get (balSlot a)) - x) = debitStor σ a x.toNat := by
    rw [h1]; rfl
  unfold mvWords
  rw [hset]
  unfold creditStor
  rw [add_word (add_l255_lt (by omega) _), l255_and_toNat, Nat.add_comm]

/-- `require(!_isBlacklisted(a))`, as the walks' facts state it. -/
theorem check_of_frozen {w : B256} (h : frozenBit w = false) :
    B256.eqCheck (Bytes.toB256 [1]) (w >>> (Bytes.toB256 [255]).toNat) = 0 := by
  unfold frozenBit at h
  rw [decide_eq_false_iff_not, Nat.not_le] at h
  refine eqCheck_ne fun e => ?_
  have e' := congrArg B256.toNat e
  rw [lit255, toNat_shr255] at e'
  have h1 : (Bytes.toB256 [1]).toNat = 1 := by decide
  rw [h1, Nat.div_eq_of_lt h] at e'
  exact absurd e' (by decide)

/-- `whenNotPaused`, as the walks' facts state it. -/
theorem check_of_flag20 {w : B256} (h : flag20 w = false) :
    (Bytes.toB256 [255] &&& w / Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) = 0 := by
  have d0 : Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ≠ 0 := by decide
  have dn : (Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]).toNat = 2 ^ 160 := by
    decide
  have fn : (Bytes.toB256 [255]).toNat = 2 ^ 8 - 1 := by decide
  unfold flag20 at h
  rw [decide_eq_false_iff_not, not_not] at h
  apply B256.toNat_inj
  rw [Blanc.B256.toNat_and, B256.toNat_div d0, dn, fn, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod,
    B256.toNat_zero]
  exact h

/-- **A move fits FiatTokenV2_2**: what `e93_inv` and the modifiers of `transfer` invert. -/
structure MoveFits (σ : Stor) (src dst : Adr) (v : B256) : Prop where
  paused : flag20 (σ.get 1) = false
  fsrc : frozenBit (σ.get (balSlot src)) = false
  fdst : frozenBit (σ.get (balSlot dst)) = false
  src0 : src ≠ 0
  dst0 : dst ≠ 0
  le : v.toNat ≤ balanceBits (σ.get (balSlot src))
  fdst' : frozenBit ((debitStor σ src v.toNat).get (balSlot dst)) = false
  room : balanceBits ((debitStor σ src v.toNat).get (balSlot dst)) + v.toNat ≤ 2 ^ 255 - 1

/-- A move's ledger stays its word form on the debited storage. -/
theorem debit_words {σ : Stor} {a : Adr} {x : B256} (hle : x.toNat ≤ balanceBits (σ.get (balSlot a))) :
    σ.set (balSlot a) ((l255 &&& σ.get (balSlot a)) - x) = debitStor σ a x.toNat := by
  rw [sub_word (by rw [l255_and_toNat]; exact hle), l255_and_toNat]
  rfl

/-- `transfer`'s facts from the guards and a fitting move. -/
theorem xferFacts_of {sevm : Sevm} {b : Devm} {dst : Adr} {v : B256}
    (g : Guards sevm 0xa9059cbb (Bytes.toB256 [64])) (hdst : xTo sevm = dst.toB256) (hv : xVal sevm = v)
    (hf : MoveFits (Devm.getStor b sevm.currentTarget) sevm.caller dst v) : XferFacts sevm b := by
  obtain ⟨p, f1, f2, s0, d0, le, f3, rm⟩ := hf
  have ta : (xTo sevm).toAdr = dst := by rw [hdst, toAdr_toB256]
  have dw := debit_words (x := v) le
  refine ⟨g.value, g.short, g.args, g.sel, ?_, ?_, ?_, adr_toB256_ne_zero s0, ?_, ?_, ?_, ?_⟩
  · rw [gsv, lit1]; exact check_of_flag20 p
  · rw [gsv, kC_bal]; exact check_of_frozen f1
  · rw [gsv, kT_bal, ta]; exact check_of_frozen f2
  · rw [ta]; exact adr_toB256_ne_zero d0
  · rw [gsv, kC_bal, hv]
    exact B256.gtCheck_eq_zero_of_toNat_le (by rw [l255_and_toNat]; exact le)
  · rw [gsv, kC_bal, kT_bal, hv, ta, dw, l255_and_toNat]; omega
  · rw [gsv, kC_bal, kT_bal, hv, ta, dw]; exact check_of_frozen f3

/-- `_transfer`'s two stores, first to their slots, do not lower the refund counter. -/
theorem e93Post_refund {sevm : Sevm} {b : Devm} {x y z : B256} {σ : Stor}
    (hcr : sevm.currentTarget ∉ b.createdAccounts) (hor : (getOrigAcct sevm sevm.currentTarget).stor = σ)
    (h1 : (Devm.getStor b sevm.currentTarget).get (balSlot z.toAdr) = σ.get (balSlot z.toAdr))
    (h2 : (Devm.getStor b sevm.currentTarget).get (balSlot y.toAdr) = σ.get (balSlot y.toAdr))
    (hne : balSlot z.toAdr ≠ balSlot y.toAdr) :
    b.refundCounter ≤ (e93Post sevm b x y z).refundCounter := by
  unfold e93Post
  refine le_trans ?_ (le_of_eq (Devm.addLog_refundCounter _ _).symm)
  refine le_trans ?_ (sstore_ge (by
      simp only [afterSload_createdAccounts]
      unfold e93Debited
      simpa only [afterSstore_createdAccounts, afterSload_createdAccounts] using hcr) hor (by
      unfold e93Debited
      simp only [afterSload_getStor, afterSstore_getStor_self, ky'_bal]
      rw [Stor.get_set_ne _ hne]
      exact h2))
  simp only [afterSload_refundCounter]
  unfold e93Debited
  refine le_trans ?_ (sstore_ge (by
      simpa only [afterSload_createdAccounts] using hcr) hor (by
      simp only [afterSload_getStor, ky'_bal]
      exact h1))
  simp only [afterSload_refundCounter]
  exact le_refl _

/-- **`transfer(dst, v)` from a frame entry, forward.** -/
theorem xfer_lands {sevm : Sevm} {pre : Devm} {dst : Adr} {v : B256}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (g : Guards sevm 0xa9059cbb (Bytes.toB256 [64])) (hdst : xTo sevm = dst.toB256) (hv : xVal sevm = v)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 74300 ≤ pre.gasLeft)
    (hf : MoveFits (Devm.getStor pre sevm.currentTarget) sevm.caller dst v) :
    ∃ post used, used ≤ 72000 ∧ FrameLands cert.prog sevm pre post used 1
      (creditStor (debitStor (Devm.getStor pre sevm.currentTarget) sevm.caller v.toNat) dst v.toNat)
      ((getOrigAcct sevm sevm.currentTarget).stor = Devm.getStor pre sevm.currentTarget ∧
        sevm.currentTarget ∉ pre.createdAccounts ∧ balSlot sevm.caller ≠ balSlot dst) := by
  have facts := xferFacts_of g hdst hv hf
  have ta : (xTo sevm).toAdr = dst := by rw [hdst, toAdr_toB256]
  refine ⟨_, _, implXferW_le sevm pre, frameLands_retV rfl (K := 72000)
    (B := e93Post sevm (e37Pre sevm pre (xTo sevm)) (xVal sevm) (xTo sevm) sevm.caller.toB256)
    (S := [selW sevm]) (M := implXferMem sevm) (w := okW)
    (fun G hG => (implXferW sevm pre).2 fork static facts G (by omega)) hs hm (implXferW_le sevm pre) (by omega)
    ?_ ?_ okW_eq ?_⟩
  · exact (((((Keeps.refl sevm pre).sload _).sload _).sload _).e93 _ _ _)
  · rw [e93Post_getStor]
    simp only [afterSload_getStor, toAdr_toB256, ta, hv]
    exact mvWords_eq hf.le hf.room
  · rintro ⟨hor, hcr, hne⟩
    refine le_trans (le_of_eq (afterSload_refundCounter.symm.trans
      (afterSload_refundCounter.symm.trans afterSload_refundCounter.symm)))
      (e93Post_refund (σ := Devm.getStor pre sevm.currentTarget)
        (by simpa only [afterSload_createdAccounts] using hcr) hor ?_ ?_ ?_)
    · simp only [afterSload_getStor]
    · simp only [afterSload_getStor]
    · rw [toAdr_toB256, ta]; exact hne

/-- `transferFrom`'s storage: the move, then the allowance read after it lowered. -/
def pullStor (σ : Stor) (src sp dst : Adr) (v : B256) : Stor :=
  (creditStor (debitStor σ src v.toNat) dst v.toNat).set (allowSlot src sp)
    (Nat.toB256 (((creditStor (debitStor σ src v.toNat) dst v.toNat).get (allowSlot src sp)).toNat - v.toNat))

/-- **A pull fits FiatTokenV2_2**: what `e68_inv` inverts. -/
structure PullFits (σ : Stor) (src sp dst : Adr) (v : B256) : Prop where
  move : MoveFits σ src dst v
  fsp : frozenBit (σ.get (balSlot sp)) = false
  allow : v.toNat ≤ (σ.get (allowSlot src sp)).toNat
  allow' : v.toNat ≤ ((creditStor (debitStor σ src v.toNat) dst v.toNat).get (allowSlot src sp)).toNat

/-- The body's base keeps the entry's storage. -/
theorem e68Pre_getStor (sevm : Sevm) (b : Devm) (y z : B256) (a : Adr) :
    Devm.getStor (e68Pre sevm b y z) a = Devm.getStor b a := by
  simp only [afterSload_getStor]

theorem e68Ok_of {sevm : Sevm} {b : Devm} {src dst : Adr} {v y z : B256} (hz : z = src.toB256)
    (hy : y = dst.toB256) (hf : PullFits (Devm.getStor b sevm.currentTarget) src sevm.caller dst v) :
    E68Ok sevm b v y z := by
  obtain ⟨⟨p, f1, f2, s0, d0, le, f3, rm⟩, fsp, al, al'⟩ := hf
  have tz : z.toAdr = src := by rw [hz, toAdr_toB256]
  have ty : y.toAdr = dst := by rw [hy, toAdr_toB256]
  have dw := debit_words (x := v) le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gsv, lit1]; exact check_of_flag20 p
  · rw [gsv, kC_bal]; exact check_of_frozen fsp
  · rw [gsv, kT_bal, tz]; exact check_of_frozen f1
  · rw [gsv, kT_bal, ty]; exact check_of_frozen f2
  · rw [gsv, kA_allow, tz]; exact B256.gtCheck_eq_zero_of_toNat_le al
  · rw [tz]; exact adr_toB256_ne_zero s0
  · rw [ty]; exact adr_toB256_ne_zero d0
  · rw [gsv, kT_bal, tz]
    exact B256.gtCheck_eq_zero_of_toNat_le (by rw [l255_and_toNat]; exact le)
  · rw [gsv, kT_bal, kT_bal, tz, ty, dw, l255_and_toNat]; omega
  · rw [gsv, kT_bal, kT_bal, tz, ty, dw]; exact check_of_frozen f3
  · rw [gsv, e93Post_getStor, e68Pre_getStor, kA'_allow, tz, ty, mvWords_eq le rm]
    exact al'

theorem e68Post_getStor (sevm : Sevm) (b : Devm) (x y z : B256) :
    Devm.getStor (e68Post sevm b x y z) sevm.currentTarget =
      (mvWords (Devm.getStor b sevm.currentTarget) z.toAdr y.toAdr x).set (allowSlot z.toAdr sevm.caller)
        ((mvWords (Devm.getStor b sevm.currentTarget) z.toAdr y.toAdr x).get (allowSlot z.toAdr sevm.caller) - x) := by
  unfold e68Post
  simp only [afterSstore_getStor_self, afterSload_getStor, gsv, e93Post_getStor, kA'_allow, e68Pre_getStor]

theorem _root_.Blanc.Lift.AccumulatedWalk.Keeps.e68 {sevm : Sevm} {pre B : Devm} (h : Keeps sevm pre B) (x y z : B256) :
    Keeps sevm pre (e68Post sevm B x y z) := by
  unfold e68Post
  exact ((((((((h.sload _).sload _).sload _).sload _).sload _).e93 _ _ _).sload _).sstore _ _)

/-- **`transferFrom(src, dst, v)` from a frame entry, forward.** -/
theorem pull_lands {sevm : Sevm} {pre : Devm} {src dst : Adr} {v : B256}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (g : Guards sevm 0x23b872dd (Bytes.toB256 [96])) (hsrc : pFrom sevm = src.toB256)
    (hdst : pTo sevm = dst.toB256) (hv : pVal sevm = v)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 104300 ≤ pre.gasLeft)
    (hf : PullFits (Devm.getStor pre sevm.currentTarget) src sevm.caller dst v) :
    ∃ post used, used ≤ 102000 ∧ FrameLands cert.prog sevm pre post used 1
      (pullStor (Devm.getStor pre sevm.currentTarget) src sevm.caller dst v)
      ((getOrigAcct sevm sevm.currentTarget).stor = Devm.getStor pre sevm.currentTarget ∧
        sevm.currentTarget ∉ pre.createdAccounts ∧
        allowSlot src sevm.caller ≠ balSlot src ∧ allowSlot src sevm.caller ≠ balSlot dst ∧
        balSlot src ≠ balSlot dst) := by
  have ok : E68Ok sevm pre (pVal sevm) (pTo sevm) (pFrom sevm) := by
    rw [hv]; exact e68Ok_of hsrc hdst hf
  have tz : (pFrom sevm).toAdr = src := by rw [hsrc, toAdr_toB256]
  have ty : (pTo sevm).toAdr = dst := by rw [hdst, toAdr_toB256]
  refine ⟨_, _, pullW_le sevm pre, frameLands_retV rfl (K := 102000)
    (fun G hG => (pullW sevm pre).2 fork static g ok G hG) hs hm (pullW_le sevm pre) (by omega)
    ?_ ?_ okW_eq ?_⟩
  · exact (Keeps.refl sevm pre).e68 _ _ _
  · unfold pullBase
    rw [e68Post_getStor, tz, ty, hv, mvWords_eq hf.move.le hf.move.room, sub_word hf.allow']
    rfl
  · rintro ⟨hor, hcr, ha1, ha2, hne⟩
    unfold pullBase e68Post
    have hcr' : sevm.currentTarget ∉ (e68Pre sevm pre (pTo sevm) (pFrom sevm)).createdAccounts := by
      simpa only [afterSload_createdAccounts] using hcr
    have hrB := e93Post_refund (sevm := sevm) (x := pVal sevm) (y := pTo sevm) (z := pFrom sevm)
      (σ := Devm.getStor pre sevm.currentTarget) hcr' hor (by rw [e68Pre_getStor])
      (by rw [e68Pre_getStor]) (by rw [tz, ty]; exact hne)
    have hk := (((((((Keeps.refl sevm pre).sload (Bytes.toB256 [1])).sload (ky sevm.caller.toB256)).sload
      (ky (pFrom sevm))).sload (ky (pTo sevm))).sload (kA' sevm (pFrom sevm))).e93 (pVal sevm) (pTo sevm) (pFrom sevm))
    refine le_trans ?_ (sstore_ge (by
        rw [afterSload_createdAccounts, hk.created]; exact hcr) hor ?_)
    · simp only [afterSload_refundCounter]
      refine le_trans ?_ hrB
      simp only [afterSload_refundCounter]
      exact le_refl _
    · rw [afterSload_getStor, e93Post_getStor, e68Pre_getStor, kA'_allow, tz, ty]
      unfold mvWords
      rw [Stor.get_set_ne _ ha2.symm, Stor.get_set_ne _ ha1.symm]

/-- **`balanceOf(a)` from a frame entry, forward**, static or not: it answers `a`'s balance bits and
writes nothing. -/
theorem bal_lands {sevm : Sevm} {pre : Devm} {a : Adr}
    (fork : CoveredFork sevm.benvStat.fork) (g : Guards sevm 0x70a08231 (Bytes.toB256 [32]))
    (hholder : bHolder sevm = a.toB256)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 5800 ≤ pre.gasLeft) :
    ∃ post used, used ≤ 3500 ∧ FrameLands cert.prog sevm pre post used
      (Nat.toB256 (balanceBits ((Devm.getStor pre sevm.currentTarget).get (balSlot a))))
      (Devm.getStor pre sevm.currentTarget) True := by
  refine ⟨_, _, balW_le sevm pre, frameLands_retV rfl (K := 3500)
    (fun G _ => (balW sevm pre).2 fork g G) hs hm (balW_le sevm pre) (by omega)
    ((Keeps.refl sevm pre).sload _) ?_ ?_ ?_⟩
  · rw [afterSload_getStor]
  · unfold bAns
    rw [← toB256_toNat (l255 &&& _), l255_and_toNat, gsv, ky_bal, hholder, toAdr_toB256]
  · exact fun _ => le_of_eq afterSload_refundCounter.symm

end Blanc.Composition.UsdcLive
