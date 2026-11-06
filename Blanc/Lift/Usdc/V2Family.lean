import Blanc.Lift.Usdc.V2Frames
import Blanc.Lift.WalkFpMove

/-!
# FiatTokenV2 and V2_1: what their forward walks share

The two implementations' `transfer`, `transferFrom` and `balanceOf` differ only in tree labels and entry
numbers. This holds the images, bases, facts and ledger laws that name no tree: the pointer's moves
(`msgMem`), `_transfer`'s and `transferFrom`'s post bases, and the premises a move or a pull fits under.
Stated on `ImplV2`'s slots, which are V2_1's by `rfl`.
-/

namespace Blanc.Lift.Usdc.ImplV2

open Jaune Blanc Blanc.Lift
open Blanc.Lift.AccumulatedWalk

local notation "m20" => Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-- The two message words at the pointer `F`, over a moved pointer. -/
abbrev msgMem (M : Mem) (F : Nat) (new msgW : B256) : Mem :=
  ((M.write 64 new.toBytes).write F (Bytes.toB256 [0x1e]).toBytes).write (F + 32) msgW.toBytes

/-- The message word of `sub`. -/
abbrev subMsg : B256 := Bytes.toB256 [0x53, 0x61, 0x66, 0x65, 0x4d, 0x61, 0x74, 0x68, 0x3a, 0x20, 0x73, 0x75, 0x62, 0x74, 0x72, 0x61, 0x63, 0x74, 0x69, 0x6f, 0x6e, 0x20, 0x6f, 0x76, 0x65, 0x72, 0x66, 0x6c, 0x6f, 0x77, 0x00, 0x00]

theorem msgMemA_fp {M : Mem} (h : FpM (Bytes.toB256 [128]) 96 M) :
    FpM (Bytes.toB256 [64] + Bytes.toB256 [128]) 192
      (msgMem M 128 (Bytes.toB256 [64] + Bytes.toB256 [128]) subMsg) :=
  (h.moved.write_out _).grown _ (by decide)

theorem msgMemB_fp {M : Mem} (h : FpM (Bytes.toB256 [64] + Bytes.toB256 [128]) 224 M) :
    FpM (Bytes.toB256 [64] + (Bytes.toB256 [64] + Bytes.toB256 [128])) 256
      (msgMem M 192 (Bytes.toB256 [64] + (Bytes.toB256 [64] + Bytes.toB256 [128])) subMsg) :=
  ((h.moved.write 192 _ (by decide) (by decide)).grown _ (by decide))

/-- The scratch image of one mapping-slot hash at base slot `9`. -/
abbrev sc9 (M : Mem) (k : B256) : Mem := (M.write 0 k.toBytes).write 32 (Bytes.toB256 [9]).toBytes

/-- The balance key as the walk computes it. -/
abbrev ky (a : B256) : B256 := mapSlot (m20 &&& a) (Bytes.toB256 [9])

/-- The balance key, normalized. -/
abbrev kn (a : B256) : B256 := mapSlot a.toAdr.toB256 (Bytes.toB256 [9])

/-- The storage-reading key of `a`, in the operand order the walk writes through. -/
abbrev ky' (a : B256) : B256 := mapSlot (a &&& m20) (Bytes.toB256 [9])

/-- The ERC-20 `Transfer` event topic. -/
abbrev transferTopic : B256 := Bytes.toB256 [221, 242, 82, 173, 27, 226, 200, 155, 105, 194, 176, 104,
  252, 55, 141, 170, 149, 43, 167, 241, 99, 196, 161, 22, 40, 245, 90, 77, 245, 35, 179, 239]

/-- The base after `_transfer`'s debit. -/
def e74Debited (sevm : Sevm) (b : Devm) (v r : B256) : Devm :=
  afterSstore sevm (afterSload sevm (afterSload sevm b (ky' r)) (ky' r)) (ky' r)
    ((afterSload sevm b (ky' r)).getStorVal sevm.currentTarget (ky' r) - v)

/-- The base `_transfer` returns with. -/
def e74Post (sevm : Sevm) (b : Devm) (v t r : B256) : Devm :=
  (afterSstore sevm (afterSload sevm (e74Debited sevm b v r) (ky' t)) (ky' t)
    (v + (e74Debited sevm b v r).getStorVal sevm.currentTarget (ky' t))).addLog
    { address := sevm.currentTarget, topics := [transferTopic, r &&& m20, t &&& m20], data := v.toBytes }

/-- The image `_transfer` returns with, the pointer at `0xc0`. -/
abbrev e74Mem (M : Mem) (v t r : B256) : Mem :=
  (sc9 ((sc9 (msgMem (sc9 (sc9 M (r &&& m20)) (r &&& m20)) 128 (Bytes.toB256 [64] + Bytes.toB256 [128]) subMsg)
    (r &&& m20)).write 0 (t &&& m20).toBytes) (t &&& m20)).write 192 v.toBytes

/-- A blacklist key, normalized. -/
abbrev kL (a : B256) : B256 := mapSlot a.toAdr.toB256 (Bytes.toB256 [3])

/-- The checks `_transfer` makes, for owner `r`, in the walks' forms. -/
structure MoveOk (sevm : Sevm) (b : Devm) (v t r : B256) : Prop where
  hr : r.toAdr.toB256 ≠ 0
  ht : t.toAdr.toB256 ≠ 0
  hle : v.toNat ≤ (b.getStorVal sevm.currentTarget (kn r)).toNat
  hnof : v.toNat + (((Devm.getStor b sevm.currentTarget).set (kn r)
    (b.getStorVal sevm.currentTarget (kn r) - v)).get (kn t)).toNat < 2 ^ 256

theorem scw_fp {fp : B256} {n : Nat} {M : Mem} (h : FpM fp n M) (k c : B256) (hn : 64 ≤ n) :
    FpM fp n ((M.write 0 k.toBytes).write 32 c.toBytes) :=
  (h.write 0 _ (by omega) (by omega)).write 32 _ (by omega) (by omega)

theorem sc9_fp {fp : B256} {n : Nat} {M : Mem} (h : FpM fp n M) (k : B256) (hn : 64 ≤ n) : FpM fp n (sc9 M k) :=
  (h.write 0 _ (by omega) (by omega)).write 32 _ (by omega) (by omega)

/-- The image `_transfer` returns with keeps the moved pointer. -/
theorem e74Mem_fp {M : Mem} (h : FpM (Bytes.toB256 [128]) 96 M) (v t r : B256) :
    FpM (Bytes.toB256 [64] + Bytes.toB256 [128]) 224 (e74Mem M v t r) := by
  have h1 := msgMemA_fp (sc9_fp (sc9_fp h (r &&& m20) (by decide)) (r &&& m20) (by decide))
  have h2 := sc9_fp h1 (r &&& m20) (by decide)
  have h3 := h2.write 0 (t &&& m20) (by decide) (by decide)
  exact (sc9_fp h3 (t &&& m20) (by decide)).grown v (by decide)

/-- The base after `transfer`'s modifiers. -/
abbrev e28Pre (sevm : Sevm) (b : Devm) (t : B256) : Devm :=
  afterSload sevm (afterSload sevm (afterSload sevm b (Bytes.toB256 [1]))
    (mapSlot sevm.caller.toB256 (Bytes.toB256 [3]))) (mapSlot (t &&& m20) (Bytes.toB256 [3]))

/-- The image before `transfer`'s `_transfer`. -/
abbrev e28Mem (sevm : Sevm) (M : Mem) (t : B256) : Mem :=
  ((((M.write 0 sevm.caller.toB256.toBytes).write 32 (Bytes.toB256 [3]).toBytes).write 0
    (t &&& m20).toBytes).write 32 (Bytes.toB256 [3]).toBytes)

/-- `whenNotPaused` and two `notBlacklisted`, in the walks' forms. -/
structure Unlisted (sevm : Sevm) (b : Devm) (t : B256) : Prop where
  paused : (Bytes.toB256 [255] &&& b.getStorVal sevm.currentTarget (Bytes.toB256 [1]) /
    Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) = 0
  caller : (Bytes.toB256 [255] &&& b.getStorVal sevm.currentTarget
    (mapSlot sevm.caller.toB256 (Bytes.toB256 [3]))) = 0
  dest : (Bytes.toB256 [255] &&& b.getStorVal sevm.currentTarget (kL t)) = 0

/-- The prologue's image. -/
abbrev mem0 : Mem := Mem.empty.write 64 (Bytes.toB256 [128]).toBytes

/-- `transfer`'s arguments as its wrapper decodes them. -/
abbrev xTo (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [4]) &&& m20
abbrev xVal (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4])

/-- The pointer after `_transfer`. -/
abbrev fp1 : B256 := Bytes.toB256 [64] + Bytes.toB256 [128]

/-- The base `transfer` halts from. -/
abbrev xferBase (sevm : Sevm) (b : Devm) : Devm :=
  e74Post sevm (e28Pre sevm b (xTo sevm)) (xVal sevm) (xTo sevm) sevm.caller.toB256

/-- The image before `transferFrom`'s `_transfer`. -/
abbrev e59Mem (sevm : Sevm) (M : Mem) (t r : B256) : Mem :=
  (((((((((M.write 0 sevm.caller.toB256.toBytes).write 32 (Bytes.toB256 [3]).toBytes).write 0
    (r &&& m20).toBytes).write 32 (Bytes.toB256 [3]).toBytes).write 0 (t &&& m20).toBytes).write 32
    (Bytes.toB256 [3]).toBytes).write 0 (r &&& m20).toBytes).write 32 (Bytes.toB256 [10]).toBytes).write 0
    sevm.caller.toB256.toBytes).write 32 (mapSlot (r &&& m20) (Bytes.toB256 [10])).toBytes

/-- The image before `transferFrom`'s second `sub`, from the image `M` its `_transfer` returned. -/
abbrev e59Img (sevm : Sevm) (M : Mem) (r : B256) : Mem :=
  (((M.write 0 (r &&& m20).toBytes).write 32 (Bytes.toB256 [10]).toBytes).write 0
    sevm.caller.toB256.toBytes).write 32 (mapSlot (r &&& m20) (Bytes.toB256 [10])).toBytes

/-- The allowance key as the walk computes it. -/
abbrev ak (sevm : Sevm) (r : B256) : B256 := mapSlot sevm.caller.toB256 (mapSlot (r &&& m20) (Bytes.toB256 [10]))

/-- The base after `transferFrom`'s modifiers and allowance check. -/
abbrev e59Pre (sevm : Sevm) (b : Devm) (t r : B256) : Devm :=
  afterSload sevm (afterSload sevm (afterSload sevm (afterSload sevm (afterSload sevm b (Bytes.toB256 [1]))
    (mapSlot sevm.caller.toB256 (Bytes.toB256 [3]))) (mapSlot (r &&& m20) (Bytes.toB256 [3])))
    (mapSlot (t &&& m20) (Bytes.toB256 [3]))) (ak sevm r)

/-- The pointer after `transferFrom`. -/
abbrev fp2 : B256 := Bytes.toB256 [64] + (Bytes.toB256 [64] + Bytes.toB256 [128])

/-- The image `transferFrom`'s allowance debit returns with. -/
abbrev e59End (sevm : Sevm) (M : Mem) (r : B256) : Mem :=
  e59Img sevm (msgMem (e59Img sevm M r) 192 fp2 subMsg) r

theorem e59End_fp {sevm : Sevm} {M : Mem} (h : FpM fp1 224 M) (r : B256) : FpM fp2 256 (e59End sevm M r) :=
  scw_fp (scw_fp (msgMemB_fp (scw_fp (scw_fp h _ _ (by decide)) _ _ (by decide))) _ _ (by decide)) _ _ (by decide)

/-- The base after the allowance debit, over the base `B` the `_transfer` left. -/
def e59Debit (sevm : Sevm) (B : Devm) (v r : B256) : Devm :=
  afterSstore sevm (afterSload sevm B (ak sevm r)) (ak sevm r)
    (B.getStorVal sevm.currentTarget (ak sevm r) - v)

/-- The base `transferFrom`'s body returns with. -/
abbrev e59Post (sevm : Sevm) (b : Devm) (v t r : B256) : Devm :=
  e59Debit sevm (e74Post sevm (e59Pre sevm b t r) v t r) v r

/-- The checks of `transferFrom`'s body in the walks' forms. -/
structure E59Ok (sevm : Sevm) (b : Devm) (v t r : B256) : Prop where
  paused : (Bytes.toB256 [255] &&& b.getStorVal sevm.currentTarget (Bytes.toB256 [1]) /
    Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) = 0
  caller : (Bytes.toB256 [255] &&& b.getStorVal sevm.currentTarget
    (mapSlot sevm.caller.toB256 (Bytes.toB256 [3]))) = 0
  src : (Bytes.toB256 [255] &&& b.getStorVal sevm.currentTarget (kL r)) = 0
  dest : (Bytes.toB256 [255] &&& b.getStorVal sevm.currentTarget (kL t)) = 0
  allow : B256.gtCheck v (b.getStorVal sevm.currentTarget
    (mapSlot sevm.caller.toB256 (mapSlot r.toAdr.toB256 (Bytes.toB256 [10])))) = 0
  move : MoveOk sevm b v t r
  allow' : v.toNat ≤ ((e74Post sevm (e59Pre sevm b t r) v t r).getStorVal sevm.currentTarget (ak sevm r)).toNat

/-- `transferFrom`'s arguments as its wrapper decodes them. -/
abbrev pFrom (sevm : Sevm) : B256 := m20 &&& Sevm.dataWord sevm (Bytes.toB256 [4])
abbrev pTo (sevm : Sevm) : B256 := m20 &&& Sevm.dataWord sevm (Bytes.toB256 [4] + Bytes.toB256 [32])
abbrev pVal (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [64] + Bytes.toB256 [4])

/-- The base `transferFrom` halts from. -/
abbrev pullBase (sevm : Sevm) (b : Devm) : Devm := e59Post sevm b (pVal sevm) (pTo sevm) (pFrom sevm)

/-- The image `transferFrom` halts with. -/
abbrev pullEnd (sevm : Sevm) : Mem :=
  e59End sevm (e74Mem (e59Mem sevm mem0 (pTo sevm) (pFrom sevm)) (pVal sevm) (pTo sevm) (pFrom sevm)) (pFrom sevm)

/-- `balanceOf`'s argument as its wrapper decodes it. -/
abbrev bHolder (sevm : Sevm) : B256 := m20 &&& Sevm.dataWord sevm (Bytes.toB256 [4])

/-- The answer of `balanceOf`. -/
abbrev bAns (sevm : Sevm) (b : Devm) : B256 := b.getStorVal sevm.currentTarget (ky (bHolder sevm))

theorem kn_bal (a : B256) : kn a = balSlot a.toAdr := by
  unfold kn balSlot
  rw [lit9]

theorem ky_bal (a : B256) : ky a = balSlot a.toAdr := by
  unfold ky balSlot
  rw [ff20_and_word, lit9]

theorem ky'_bal (a : B256) : ky' a = balSlot a.toAdr := by
  unfold ky' balSlot
  rw [word_ff20, lit9]

theorem ak_allow (sevm : Sevm) (r : B256) : ak sevm r = allowSlot r.toAdr sevm.caller := by
  unfold ak allowSlot
  rw [word_ff20, lit10]

theorem _root_.Blanc.Lift.AccumulatedWalk.Keeps.e74V2 {sevm : Sevm} {pre B : Devm} (h : Keeps sevm pre B) (v t r : B256) :
    Keeps sevm pre (e74Post sevm B v t r) := by
  unfold e74Post e74Debited
  exact (((((((h.sload _).sload _).sstore _ _).sload _).sstore _ _).log _))

theorem _root_.Blanc.Lift.AccumulatedWalk.Keeps.e59V2 {sevm : Sevm} {pre B : Devm} (h : Keeps sevm pre B) (v r : B256) :
    Keeps sevm pre (e59Debit sevm B v r) := by
  unfold e59Debit
  exact ((h.sload _).sstore _ _)

theorem e74Post_getStor (sevm : Sevm) (b : Devm) (v t r : B256) :
    Devm.getStor (e74Post sevm b v t r) sevm.currentTarget =
      moveStor (Devm.getStor b sevm.currentTarget) r.toAdr t.toAdr v := by
  unfold e74Post e74Debited moveStor
  simp only [Devm.addLog_getStor, afterSstore_getStor_self, afterSload_getStor, gsv, ky'_bal]

theorem e59Debit_getStor (sevm : Sevm) (B : Devm) (v r : B256) :
    Devm.getStor (e59Debit sevm B v r) sevm.currentTarget =
      (Devm.getStor B sevm.currentTarget).set (allowSlot r.toAdr sevm.caller)
        ((Devm.getStor B sevm.currentTarget).get (allowSlot r.toAdr sevm.caller) - v) := by
  unfold e59Debit
  simp only [afterSstore_getStor_self, afterSload_getStor, gsv, ak_allow]

/-- `_transfer`'s two stores, first to their slots, do not lower the refund counter. -/
theorem e74Post_refund {sevm : Sevm} {b : Devm} {v t r : B256} {σ : Stor}
    (hcr : sevm.currentTarget ∉ b.createdAccounts) (hor : (getOrigAcct sevm sevm.currentTarget).stor = σ)
    (h1 : (Devm.getStor b sevm.currentTarget).get (balSlot r.toAdr) = σ.get (balSlot r.toAdr))
    (h2 : (Devm.getStor b sevm.currentTarget).get (balSlot t.toAdr) = σ.get (balSlot t.toAdr))
    (hne : balSlot r.toAdr ≠ balSlot t.toAdr) :
    b.refundCounter ≤ (e74Post sevm b v t r).refundCounter := by
  unfold e74Post
  refine le_trans ?_ (le_of_eq (Devm.addLog_refundCounter _ _).symm)
  refine le_trans ?_ (sstore_ge (by
      simp only [afterSload_createdAccounts]
      unfold e74Debited
      simpa only [afterSstore_createdAccounts, afterSload_createdAccounts] using hcr) hor (by
      unfold e74Debited
      simp only [afterSload_getStor, afterSstore_getStor_self, ky'_bal]
      rw [Stor.get_set_ne _ hne]
      exact h2))
  simp only [afterSload_refundCounter]
  unfold e74Debited
  refine le_trans ?_ (sstore_ge (by
      simpa only [afterSload_createdAccounts] using hcr) hor (by
      simp only [afterSload_getStor, ky'_bal]
      exact h1))
  simp only [afterSload_refundCounter]
  exact le_refl _

/-- `paused` and the listed bytes, as the walks' facts state them. -/
theorem unlisted_of {sevm : Sevm} {b : Devm} {t : B256}
    (hp : pausedByte (Devm.getStor b sevm.currentTarget) = 0)
    (hc : listedByte (Devm.getStor b sevm.currentTarget) sevm.caller = 0)
    (ht : listedByte (Devm.getStor b sevm.currentTarget) t.toAdr = 0) : Unlisted sevm b t := by
  refine ⟨?_, ?_, ?_⟩
  · rw [gsv, lit1]; exact hp
  · rw [gsv, lit3]; exact hc
  · unfold kL; rw [gsv, lit3]; exact ht

/-- **A move fits FiatTokenV2**: what `frame_transfer` inverts, with the two zero-address tests. -/
structure MoveFits (σ : Stor) (src dst : Adr) (v : B256) : Prop where
  paused : pausedByte σ = 0
  lsrc : listedByte σ src = 0
  ldst : listedByte σ dst = 0
  src0 : src ≠ 0
  dst0 : dst ≠ 0
  le : v.toNat ≤ (σ.get (balSlot src)).toNat
  nof : v.toNat + ((σ.set (balSlot src) (σ.get (balSlot src) - v)).get (balSlot dst)).toNat < 2 ^ 256

theorem moveOk_of {sevm : Sevm} {b : Devm} {src dst : Adr} {v t r : B256} (hr : r = src.toB256) (ht : t = dst.toB256)
    (hf : MoveFits (Devm.getStor b sevm.currentTarget) src dst v) : MoveOk sevm b v t r := by
  obtain ⟨-, -, -, s0, d0, le, nof⟩ := hf
  have tr : r.toAdr = src := by rw [hr, toAdr_toB256]
  have tt : t.toAdr = dst := by rw [ht, toAdr_toB256]
  refine ⟨by rw [tr]; exact adr_toB256_ne_zero s0, by rw [tt]; exact adr_toB256_ne_zero d0, ?_, ?_⟩
  · rw [gsv, kn_bal, tr]; exact le
  · rw [gsv, kn_bal, kn_bal, tr, tt]; exact nof

/-- **A pull fits FiatTokenV2**: what `frame_transferFrom` inverts, with the zero-address tests. -/
structure PullFits (σ : Stor) (src sp dst : Adr) (v : B256) : Prop where
  move : MoveFits σ src dst v
  lsp : listedByte σ sp = 0
  allow : v.toNat ≤ (σ.get (allowSlot src sp)).toNat
  allow' : v.toNat ≤ ((moveStor σ src dst v).get (allowSlot src sp)).toNat

end Blanc.Lift.Usdc.ImplV2
