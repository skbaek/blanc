import Blanc.Lift.Usdc.V2Frames
import Blanc.Lift.WalkFpMove
import Blanc.Lift.CoinFrame
import Blanc.Lift.Usdc.ImplV2.Jumps

/-!
# FiatTokenV2: forward runs of `transfer`, `transferFrom` and `balanceOf`

SafeMath's messaged `sub` allocates its revert string, so the free-memory pointer moves: `0x80` to
`0xc0` across `_transfer`, and to `0x100` across `transferFrom`'s allowance debit. Its other walks are
FiatTokenV2_2's, on an unpacked ledger.
-/

namespace Blanc.Lift.Usdc.ImplV2

open Jaune Blanc Blanc.Lift
open Blanc.Lift.AccumulatedWalk

local notation "m20" => Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-- **Entry 77, SafeMath `add`**, forward. -/
@[irreducible] noncomputable def e77W (sevm : Sevm) (b : Devm) (x y ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // x.toNat + y.toNat < 2 ^ 256 → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (x :: y :: ret :: S) M (X + c)) t_41fd_c77
        (.returned (St b ((x + y) :: S) M X))} :=
  ⟨_, fun hle room X => by
    have := ltCheck_add_zero hle
    xrun⟩

/-- **Entry 88, SafeMath `sub` with a message**, forward. -/
@[irreducible] noncomputable def e88W (sevm : Sevm) (b : Devm) (m x y ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // x.toNat ≤ y.toNat → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (m :: x :: y :: ret :: S) M (X + c)) t_4be2_c88
        (.returned (St b ((y - x) :: S) M X))} :=
  ⟨_, fun hle room X => by
    have := B256.gtCheck_eq_zero_of_toNat_le hle
    xrun⟩

/-- The two message words at the pointer `F`, over a moved pointer. -/
abbrev msgMem (M : Mem) (F : Nat) (new msgW : B256) : Mem :=
  ((M.write 64 new.toBytes).write F (Bytes.toB256 [0x1e]).toBytes).write (F + 32) msgW.toBytes

/-- The message word of `sub`. -/
abbrev subMsg : B256 := Bytes.toB256 [0x53, 0x61, 0x66, 0x65, 0x4d, 0x61, 0x74, 0x68, 0x3a, 0x20, 0x73, 0x75, 0x62, 0x74, 0x72, 0x61, 0x63, 0x74, 0x69, 0x6f, 0x6e, 0x20, 0x6f, 0x76, 0x65, 0x72, 0x66, 0x6c, 0x6f, 0x77, 0x00, 0x00]

/-- **Entry 78, SafeMath `sub`, its first call**: the pointer `0x80` to `0xc0`. -/
@[irreducible] noncomputable def e78aW (sevm : Sevm) (b : Devm) (x y ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // FpM (Bytes.toB256 [128]) 96 M → x.toNat ≤ y.toNat → S.length < 990 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (x :: y :: ret :: S) M (X + c)) t_4123_c78
        (.returned (St b ((y - x) :: S) (msgMem M 128 (Bytes.toB256 [64] + Bytes.toB256 [128]) subMsg) X))} :=
  ⟨_, fun hM hle room X => by
    xrun
    apply rk
    refine rx_mstoreMove hM (by decide) fun hM1 => ?_
    xrun
    apply rk
    refine rx_mstoreGrow (n := 160) (by xfp) (by decide) (by decide) rfl fun hM2 => ?_
    xrun
    xcallM e88W 4 [] hle (by xroom)
    xrun
    all_goals omega⟩

/-- **Entry 78, SafeMath `sub`, its second call**: the pointer `0xc0` to `0x100`. -/
@[irreducible] noncomputable def e78bW (sevm : Sevm) (b : Devm) (x y ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // FpM (Bytes.toB256 [64] + Bytes.toB256 [128]) 224 M → x.toNat ≤ y.toNat → S.length < 990 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (x :: y :: ret :: S) M (X + c)) t_4123_c78
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
    xcallM e88W 4 [] hle (by xroom)
    xrun
    all_goals omega⟩

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

/-- **Entry 74, `_transfer(owner, recipient, amount)`**, forward. -/
@[irreducible] noncomputable def e74W (sevm : Sevm) (b : Devm) (v t r ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      FpM (Bytes.toB256 [128]) 96 M → S.length < 980 → r.toAdr.toB256 ≠ 0 → t.toAdr.toB256 ≠ 0 →
      v.toNat ≤ (b.getStorVal sevm.currentTarget (kn r)).toNat →
      v.toNat + (((Devm.getStor b sevm.currentTarget).set (kn r)
        (b.getStorVal sevm.currentTarget (kn r) - v)).get (kn t)).toNat < 2 ^ 256 →
      ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (v :: t :: r :: ret :: S) M (X + c)) t_3ef8_c74
        (.returned (St (e74Post sevm b v t r) S (e74Mem M v t r) X))} :=
  ⟨_, fun fork static hM room hr ht hle hnof X hX => by
    have hg : B256.gtCheck v (b.getStorVal sevm.currentTarget (kn r)) = 0 :=
      B256.gtCheck_eq_zero_of_toNat_le hle
    xrun
    xcallM e78aW 3 [] (by xfp) (by xnorm; with_reducible assumption) (by xroom)
    have hMa := msgMemA_fp (M := sc9 (sc9 M (r &&& m20)) (r &&& m20)) (by xfp)
    xrun
    apply rk
    refine rx_keccakRev (hMa.write 0 _ (by decide) (by decide)).wf (by with_reducible rfl) (by xfp) (by decide) (by decide) (by xroom) ?_
    xrun
    xcallM e77W 3 [] (by xnorm; with_reducible assumption) (by xroom)
    xrun
    apply rk
    refine rx_mstoreGrow (n := 192) (by xfp) (by decide) (by decide) rfl fun hMb => ?_
    xrun
    apply rk
    refine rx_log3At static (by with_reducible rfl) (by xfp) hMb (by decide) (by decide) (by decide) ?_
    xrun
    all_goals ((try unfold gCallStipend); omega)⟩

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

/-- **Entry 28, `transfer(to, value)`**, forward. -/
@[irreducible] noncomputable def e28W (sevm : Sevm) (b : Devm) (v t ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      FpM (Bytes.toB256 [128]) 96 M → S.length < 970 → Unlisted sevm b t →
      MoveOk sevm b v t sevm.caller.toB256 →
      ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (v :: t :: ret :: S) M (X + c)) t_2bb8_c28
        (.returned (St (e74Post sevm (e28Pre sevm b t) v t sevm.caller.toB256) (Bytes.toB256 [1] :: S)
          (e74Mem (e28Mem sevm M t) v t sevm.caller.toB256) X))} :=
  ⟨_, fun fork static hM room un ok X hX => by
    obtain ⟨hp, hc, ht⟩ := un
    obtain ⟨h1, h2, h3, h4⟩ := ok
    simp only [toAdr_toB256] at h1
    xrun
    xcallMT e74W 4 [] fork static (by xfp) (by xroom) (by xnorm; with_reducible assumption)
      (by xnorm; with_reducible assumption) (by xnorm; with_reducible assumption)
      (by xnorm; with_reducible assumption)
    xrun
    all_goals ((try unfold gCallStipend); omega)⟩

/-- The prologue's image. -/
abbrev mem0 : Mem := Mem.empty.write 64 (Bytes.toB256 [128]).toBytes

/-- `transfer`'s arguments as its wrapper decodes them. -/
abbrev xTo (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [4]) &&& m20
abbrev xVal (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4])

/-- The halting state of a frame returning the word `w` at the pointer `F`. -/
def retV (F : B256) (B : Devm) (S : List B256) (M : Mem) (w : B256) (G : Nat) : Devm :=
  ((St B S M G).memRead F.toNat (Bytes.toB256 [32] + (F - F)).toNat).2.withOutput w.toBytes

/-- The word a mutating entry returns. -/
abbrev okW : B256 := B256.eqCheck (B256.eqCheck (Bytes.toB256 [1]) 0) 0

/-- The pointer after `_transfer`. -/
abbrev fp1 : B256 := Bytes.toB256 [64] + Bytes.toB256 [128]

/-- The base `transfer` halts from. -/
abbrev xferBase (sevm : Sevm) (b : Devm) : Devm :=
  e74Post sevm (e28Pre sevm b (xTo sevm)) (xVal sevm) (xTo sevm) sevm.caller.toB256

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
    xcallMT e28W 3 [] fork static (by xfp) (by xroom) un ok
    have hMc := e74Mem_fp (M := e28Mem sevm mem0 (xTo sevm)) (scw_fp (scw_fp (FpM.init (Bytes.toB256 [128])) _ _ (by decide)) _ _ (by decide)) (xVal sevm) (xTo sevm) sevm.caller.toB256
    xrun
    apply rk
    refine rx_mstoreP (i0 := 192) hMc (by decide) (by decide) (by decide) ?_
    xrun
    refine rk0 ?_
    refine rx_returnAt (i0 := 192) (n := 224) rfl hMc (hMc.write 192 _ (by decide) (by decide)) (by decide) (by decide) (by decide)
    all_goals omega⟩

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

/-- **Tree `0x147d` of entry 59, the allowance debit**, forward. -/
@[irreducible] noncomputable def e59TW (sevm : Sevm) (B : Devm) (v t r ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false → FpM fp1 224 M → S.length < 960 →
      v.toNat ≤ (B.getStorVal sevm.currentTarget (ak sevm r)).toNat → ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm
        (St B (t :: r :: sevm.caller.toB256 :: Bytes.toB256 [0] :: v :: t :: r :: ret :: S) M (X + c)) t_147d_c59
        (.returned (St (e59Debit sevm B v r) (Bytes.toB256 [1] :: S) (e59End sevm M r) X))} :=
  ⟨_, fun fork static hM room hA X hX => by
    xrun
    xcallM e78bW 3 [] (by xfp) hA (by xroom)
    have hMd := msgMemB_fp (M := e59Img sevm M r) (scw_fp (scw_fp hM _ _ (by decide)) _ _ (by decide))
    xrun
    all_goals ((try unfold gCallStipend); omega)⟩

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

/-- **Entry 59, `transferFrom(from, to, value)`**, forward. -/
@[irreducible] noncomputable def e59W (sevm : Sevm) (b : Devm) (v t r ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      FpM (Bytes.toB256 [128]) 96 M → S.length < 960 → E59Ok sevm b v t r → ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (v :: t :: r :: ret :: S) M (X + c)) t_11f1_c59
        (.returned (St (e59Post sevm b v t r) (Bytes.toB256 [1] :: S)
          (e59End sevm (e74Mem (e59Mem sevm M t r) v t r) r) X))} :=
  ⟨_, fun fork static hM room facts X hX => by
    obtain ⟨hp, hc, hr, ht, ha, ⟨h1, h2, h3, h4⟩, ha2⟩ := facts
    xrun
    xcallMT e74W 4 [] fork static (by xfp) (by xroom) (by xnorm; with_reducible assumption)
      (by xnorm; with_reducible assumption) (by xnorm; with_reducible assumption)
      (by xnorm; with_reducible assumption)
    exact (e59TW sevm _ v t r ret S _).2 fork static (e74Mem_fp (M := e59Mem sevm M t r) (scw_fp (scw_fp (scw_fp (scw_fp (scw_fp hM _ _ (by decide)) _ _ (by decide)) _ _ (by decide)) _ _ (by decide)) _ _ (by decide)) v t r) (by xroom) ha2 X hX
    all_goals ((try unfold gCallStipend); omega)⟩

/-- `transferFrom`'s arguments as its wrapper decodes them. -/
abbrev pFrom (sevm : Sevm) : B256 := m20 &&& Sevm.dataWord sevm (Bytes.toB256 [4])
abbrev pTo (sevm : Sevm) : B256 := m20 &&& Sevm.dataWord sevm (Bytes.toB256 [4] + Bytes.toB256 [32])
abbrev pVal (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [64] + Bytes.toB256 [4])

/-- The base `transferFrom` halts from. -/
abbrev pullBase (sevm : Sevm) (b : Devm) : Devm := e59Post sevm b (pVal sevm) (pTo sevm) (pFrom sevm)

/-- The image `transferFrom` halts with. -/
abbrev pullEnd (sevm : Sevm) : Mem :=
  e59End sevm (e74Mem (e59Mem sevm mem0 (pTo sevm) (pFrom sevm)) (pVal sevm) (pTo sevm) (pFrom sevm)) (pFrom sevm)

/-- **The `transferFrom` frame, forward.** -/
@[irreducible] noncomputable def pullW (sevm : Sevm) (b : Devm) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      Guards sevm 0x23b872dd (Bytes.toB256 [96]) → E59Ok sevm b (pVal sevm) (pTo sevm) (pFrom sevm) → ∀ G, 2300 ≤ G →
      SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + c)) t_0000_c0
        (.halted (retV fp2 (pullBase sevm b) [selW sevm] ((pullEnd sevm).write 256 okW.toBytes) okW G))} :=
  ⟨_, fun fork static facts ok G hG => by
    obtain ⟨value, short, args, sel⟩ := facts
    xrun
    xcallMT e59W 4 [] fork static (by xfp) (by xroom) ok
    have hMd : FpM fp2 256 (pullEnd sevm) := e59End_fp (e74Mem_fp (scw_fp (scw_fp (scw_fp (scw_fp (scw_fp (FpM.init (Bytes.toB256 [128])) _ _ (by decide)) _ _ (by decide)) _ _ (by decide)) _ _ (by decide)) _ _ (by decide)) _ _ _) _
    xrun
    apply rk
    refine rx_mstoreGrow (n := 256) hMd (by decide) (by decide) rfl fun hMe => ?_
    xrun
    refine rk0 ?_
    refine rx_returnAt (i0 := 256) (n := 288) rfl hMd hMe (by decide) (by decide) (by decide)
    all_goals omega⟩

/-- **Entry 38, `balanceOf(a)`**, forward. -/
@[irreducible] noncomputable def e38W (sevm : Sevm) (b : Devm) (a ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → FpM (Bytes.toB256 [128]) 96 M → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (a :: ret :: S) M (X + c)) t_280f_c38
        (.returned (St (afterSload sevm b (ky a)) (b.getStorVal sevm.currentTarget (ky a) :: S)
          (sc9 M (m20 &&& a)) X))} :=
  ⟨_, fun fork hM room X => by
    xrun⟩

/-- `balanceOf`'s argument as its wrapper decodes it. -/
abbrev bHolder (sevm : Sevm) : B256 := m20 &&& Sevm.dataWord sevm (Bytes.toB256 [4])

/-- The answer of `balanceOf`. -/
abbrev bAns (sevm : Sevm) (b : Devm) : B256 := b.getStorVal sevm.currentTarget (ky (bHolder sevm))

/-- **The `balanceOf` frame, forward**, static or not. -/
@[irreducible] noncomputable def balW (sevm : Sevm) (b : Devm) :
    {c : Nat // CoveredFork sevm.benvStat.fork → Guards sevm 0x70a08231 (Bytes.toB256 [32]) → ∀ G,
      SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + c)) t_0000_c0
        (.halted (retV (Bytes.toB256 [128]) (afterSload sevm b (ky (bHolder sevm))) [selW sevm]
          ((sc9 mem0 (m20 &&& bHolder sevm)).write 128 (bAns sevm b).toBytes) (bAns sevm b) G))} :=
  ⟨_, fun fork facts G => by
    obtain ⟨value, short, args, sel⟩ := facts
    xrun
    xcallM e38W 2 [] fork (by xfp) (by xroom)
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

theorem e77W_le : (e77W sevm b v t ret S M).1 ≤ 100 := by
  unfold e77W; dsimp only; xcost []

theorem e88W_le (m : B256) : (e88W sevm b m v t ret S M).1 ≤ 100 := by
  unfold e88W; dsimp only; xcost []

theorem e78aW_le : (e78aW sevm b v t ret S M).1 ≤ 300 := by
  unfold e78aW; dsimp only; xcost [e88W_le]

theorem e78bW_le : (e78bW sevm b v t ret S M).1 ≤ 300 := by
  unfold e78bW; dsimp only; xcost [e88W_le]

theorem e74W_le : (e74W sevm b v t r ret S M).1 ≤ 58000 := by
  unfold e74W; dsimp only; xcost [e78aW_le, e77W_le]

theorem e28W_le : (e28W sevm b v t ret S M).1 ≤ 67000 := by
  unfold e28W; dsimp only; xcost [e74W_le]

theorem xferW_le : (xferW sevm b).1 ≤ 68000 := by
  unfold xferW; dsimp only; xcost [e28W_le]

theorem e59TW_le : (e59TW sevm b v t r ret S M).1 ≤ 25000 := by
  unfold e59TW; dsimp only; xcost [e78bW_le]

theorem e59W_le : (e59W sevm b v t r ret S M).1 ≤ 95000 := by
  unfold e59W; dsimp only; xcost [e74W_le, e59TW_le]

theorem pullW_le : (pullW sevm b).1 ≤ 96000 := by
  unfold pullW; dsimp only; xcost [e59W_le]

theorem e38W_le : (e38W sevm b a ret S M).1 ≤ 2300 := by
  unfold e38W; dsimp only; xcost []

theorem balW_le : (balW sevm b).1 ≤ 3000 := by
  unfold balW; dsimp only; xcost [e38W_le]

end Charges

/-! ## What a frame leaves -/

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

theorem _root_.Blanc.Lift.AccumulatedWalk.Keeps.retV {sevm : Sevm} {pre B : Devm} (h : Keeps sevm pre B) (F : B256) (S : List B256) (M : Mem)
    (w : B256) (G : Nat) : Keeps sevm pre (retV F B S M w G) :=
  ⟨h.code, h.other, h.error, h.created⟩

/-- A frame run to `retV` lands. -/
theorem frameLands_retV {sevm : Sevm} {pre B : Devm} {F : B256} {S : List B256} {M : Mem} {w w' : B256} {c K : Nat}
    {σ' : Stor} {R : Prop}
    (hrun : ∀ G, 2300 ≤ G → SFunc.RunExact cert.prog sevm (St pre [] Mem.empty (G + c)) t_0000_c0
      (.halted (retV F B S M w G)))
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hc : c ≤ K) (hgas : K + 2300 ≤ pre.gasLeft)
    (hk : Keeps sevm pre B) (hst : Devm.getStor B sevm.currentTarget = σ') (hw : w = w')
    (hr : R → pre.refundCounter ≤ B.refundCounter) :
    FrameLands cert.prog sevm pre (retV F B S M w (pre.gasLeft - c)) c w' σ' R :=
  frameLands_of rfl hrun hs hm hc hgas (fun _ => rfl) (fun _ => hw ▸ rfl) (fun G => hk.retV F S M w G)
    (fun _ => hst) (fun r _ => hr r)

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

theorem okW_eq : okW = 1 := by decide

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

/-- **`transfer(dst, v)` from a frame entry, forward.** -/
theorem xfer_lands {sevm : Sevm} {pre : Devm} {dst : Adr} {v : B256}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (g : Guards sevm 0xa9059cbb (Bytes.toB256 [64])) (hdst : xTo sevm = dst.toB256) (hv : xVal sevm = v)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 70300 ≤ pre.gasLeft)
    (hf : MoveFits (Devm.getStor pre sevm.currentTarget) sevm.caller dst v) :
    ∃ post used, used ≤ 68000 ∧ FrameLands cert.prog sevm pre post used 1
      (moveStor (Devm.getStor pre sevm.currentTarget) sevm.caller dst v)
      ((getOrigAcct sevm sevm.currentTarget).stor = Devm.getStor pre sevm.currentTarget ∧
        sevm.currentTarget ∉ pre.createdAccounts ∧ balSlot sevm.caller ≠ balSlot dst) := by
  have ta : (xTo sevm).toAdr = dst := by rw [hdst, toAdr_toB256]
  have un : Unlisted sevm pre (xTo sevm) := unlisted_of hf.paused hf.lsrc (by rw [ta]; exact hf.ldst)
  have ok : MoveOk sevm pre (xVal sevm) (xTo sevm) sevm.caller.toB256 := moveOk_of rfl hdst (by rw [hv]; exact hf)
  refine ⟨_, _, xferW_le sevm pre, frameLands_retV (K := 68000)
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

/-- **A pull fits FiatTokenV2**: what `frame_transferFrom` inverts, with the zero-address tests. -/
structure PullFits (σ : Stor) (src sp dst : Adr) (v : B256) : Prop where
  move : MoveFits σ src dst v
  lsp : listedByte σ sp = 0
  allow : v.toNat ≤ (σ.get (allowSlot src sp)).toNat
  allow' : v.toNat ≤ ((moveStor σ src dst v).get (allowSlot src sp)).toNat

/-- **`transferFrom(src, dst, v)` from a frame entry, forward.** -/
theorem pull_lands {sevm : Sevm} {pre : Devm} {src dst : Adr} {v : B256}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (g : Guards sevm 0x23b872dd (Bytes.toB256 [96])) (hsrc : pFrom sevm = src.toB256)
    (hdst : pTo sevm = dst.toB256) (hv : pVal sevm = v)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 98300 ≤ pre.gasLeft)
    (hf : PullFits (Devm.getStor pre sevm.currentTarget) src sevm.caller dst v) :
    ∃ post used, used ≤ 96000 ∧ FrameLands cert.prog sevm pre post used 1
      (fromStor (Devm.getStor pre sevm.currentTarget) src sevm.caller dst v)
      ((getOrigAcct sevm sevm.currentTarget).stor = Devm.getStor pre sevm.currentTarget ∧
        sevm.currentTarget ∉ pre.createdAccounts ∧
        allowSlot src sevm.caller ≠ balSlot src ∧ allowSlot src sevm.caller ≠ balSlot dst ∧
        balSlot src ≠ balSlot dst) := by
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
  refine ⟨_, _, pullW_le sevm pre, frameLands_retV (K := 96000)
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
      unfold moveStor
      rw [Stor.get_set_ne _ ha2.symm, Stor.get_set_ne _ ha1.symm]

/-- **`balanceOf(a)` from a frame entry, forward**, static or not. -/
theorem bal_lands {sevm : Sevm} {pre : Devm} {a : Adr}
    (fork : CoveredFork sevm.benvStat.fork) (g : Guards sevm 0x70a08231 (Bytes.toB256 [32]))
    (hholder : bHolder sevm = a.toB256)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 5300 ≤ pre.gasLeft) :
    ∃ post used, used ≤ 3000 ∧ FrameLands cert.prog sevm pre post used
      ((Devm.getStor pre sevm.currentTarget).get (balSlot a)) (Devm.getStor pre sevm.currentTarget) True := by
  refine ⟨_, _, balW_le sevm pre, frameLands_retV (K := 3000)
    (fun G _ => (balW sevm pre).2 fork g G) hs hm (balW_le sevm pre) (by omega)
    ((Keeps.refl sevm pre).sload _) ?_ ?_ ?_⟩
  · rw [afterSload_getStor]
  · unfold bAns
    rw [gsv, ky_bal, hholder, toAdr_toB256]
  · exact fun _ => le_of_eq afterSload_refundCounter.symm

end Blanc.Lift.Usdc.ImplV2
