import Blanc.Lift.Dai.Jumps
import Blanc.Lift.Dai.Check
import Blanc.Lift.WalkCost
import Blanc.StorageRefund
import Blanc.Lift.DaiFrames

/-!
# DAI: forward runs of `transfer`, `transferFrom` and `balanceOf`

The forward counterparts of `DaiFrames`' inversions: under the checks the frame's guards make, the
whole run to `RETURN`, with its charge synthesized by the walk and its post state an explicit term.
-/

namespace Blanc.Lift.Dai

open Jaune Blanc Blanc.Lift
open Blanc.Lift.AccumulatedWalk

set_option pp.deepTerms false
set_option pp.deepTerms.threshold 3

/-- **Entry 36, `sub(x, y)`**, forward. -/
@[irreducible] noncomputable def e36W (sevm : Sevm) (b : Devm) (y x ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // y.toNat ≤ x.toNat → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (y :: x :: ret :: S) M (X + c)) t_1e77_c36
        (.returned (St b ((x - y) :: S) M X))} :=
  ⟨_, fun hle room X => by
    have hg : B256.gtCheck (x - y) x = 0 := B256.gtCheck_eq_zero_of_toNat_le (by
      rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr hle)]; omega)
    xrun⟩

/-- **Entry 37, `add(x, y)`**, forward. -/
@[irreducible] noncomputable def e37W (sevm : Sevm) (b : Devm) (y x ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // y.toNat + x.toNat < 2 ^ 256 → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (y :: x :: ret :: S) M (X + c)) t_1e91_c37
        (.returned (St b ((x + y) :: S) M X))} :=
  ⟨_, fun hle room X => by
    have hg : B256.ltCheck (x + y) x = 0 := by
      rw [B256.add_comm]
      exact ltCheck_add_zero hle
    xrun⟩

/-- `m20`. -/
local notation "m20" => Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-- The balance key of `a` as the walk computes it. -/
abbrev ky (a : B256) : B256 := mapSlot (m20 &&& (m20 &&& a)) (Bytes.toB256 [2])

/-- The balance key of `a`, normalized (`xnorm`). -/
abbrev kn (a : B256) : B256 := mapSlot a.toAdr.toB256 (Bytes.toB256 [2])

/-- The scratch image of one mapping-slot hash. -/
abbrev scr (M : Mem) (k base : B256) : Mem := (M.write 0 k.toBytes).write 32 base.toBytes

/-- The ERC-20 `Transfer` event topic. -/
abbrev transferTopic : B256 := Bytes.toB256 [221, 242, 82, 173, 27, 226, 200, 155, 105, 194, 176, 104,
  252, 55, 141, 170, 149, 43, 167, 241, 99, 196, 161, 22, 40, 245, 90, 77, 245, 35, 179, 239]

/-- The base after a move's debit. -/
def mvDebited (sevm : Sevm) (b : Devm) (v r : B256) : Devm :=
  afterSstore sevm (afterSload sevm b (ky r)) (ky r)
    (b.getStorVal sevm.currentTarget (ky r) - v)

/-- The base a move returns with. -/
def mvBase (sevm : Sevm) (b : Devm) (v t r : B256) : Devm :=
  (afterSstore sevm (afterSload sevm (mvDebited sevm b v r) (ky t)) (ky t)
    ((mvDebited sevm b v r).getStorVal sevm.currentTarget (ky t) + v)).addLog
    { address := sevm.currentTarget, topics := [transferTopic, m20 &&& r, m20 &&& t], data := v.toBytes }

/-- The memory a move returns with. -/
abbrev mvMem (M : Mem) (v t r : B256) : Mem :=
  (scr (scr (scr (scr M (m20 &&& (m20 &&& r))  (Bytes.toB256 [2])) (m20 &&& (m20 &&& r)) (Bytes.toB256 [2]))
    (m20 &&& (m20 &&& t)) (Bytes.toB256 [2])) (m20 &&& (m20 &&& t)) (Bytes.toB256 [2])).write 128 v.toBytes

/-- **Tree `0x0db2` of entry 5, the move, forward**. -/
@[irreducible] noncomputable def e5W (sevm : Sevm) (b : Devm) (p v t r ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      FpM (Bytes.toB256 [128]) 96 M → S.length < 980 →
      v.toNat ≤ (b.getStorVal sevm.currentTarget (kn r)).toNat →
      v.toNat + (((Devm.getStor b sevm.currentTarget).set (kn r)
        (b.getStorVal sevm.currentTarget (kn r) - v)).get (kn t)).toNat < 2 ^ 256 →
      ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (p :: v :: t :: r :: ret :: S) M (X + c)) t_0db2_c5
        (.returned (St (mvBase sevm b v t r) (Bytes.toB256 [1] :: S) (mvMem M v t r) X))} :=
  ⟨_, fun fork static hM room hle hnof X hX => by
    have := hM.ge
    xrun
    xcallM e36W 3 [] (by xnorm; with_reducible assumption) (by xroom)
    xrun
    xcallM e37W 3 [] (by xnorm; with_reducible assumption) (by xroom)
    xrun
    all_goals ((try unfold gCallStipend); omega)⟩

/-- The allowance key of owner `r`, spender `c`, as the walk computes it. -/
abbrev ak (r c : B256) : B256 :=
  mapSlot (m20 &&& (m20 &&& c)) (mapSlot (m20 &&& (m20 &&& r)) (Bytes.toB256 [3]))

/-- The allowance key, normalized. -/
abbrev an (r : B256) (c : Adr) : B256 :=
  mapSlot c.toB256 (mapSlot r.toAdr.toB256 (Bytes.toB256 [3]))

theorem ky_eq (r : B256) : ky r = kn r := by
  unfold ky kn
  rw [ff20_and_word, ff20_and_word, toAdr_toB256]

/-- `transferFrom`'s balance test, on the walk's word. -/
theorem ltCheck_ky {b : Devm} {a : Adr} {r v : B256} (h : v.toNat ≤ (b.getStorVal a (kn r)).toNat) :
    B256.ltCheck (b.getStorVal a (ky r)) v = 0 := by
  rw [ky_eq]
  exact B256.ltCheck_eq_zero_of_toNat_le h

/-- **Entry 34, `transferFrom`, with the source its own spender**, forward. -/
@[irreducible] noncomputable def e34SelfW (sevm : Sevm) (b : Devm) (v t r ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      FpM (Bytes.toB256 [128]) 96 M → S.length < 970 →
      B256.eqCheck (m20 &&& r) (m20 &&& sevm.caller.toB256) = 1 →
      v.toNat ≤ (b.getStorVal sevm.currentTarget (kn r)).toNat →
      v.toNat + (((Devm.getStor b sevm.currentTarget).set (kn r)
        (b.getStorVal sevm.currentTarget (kn r) - v)).get (kn t)).toNat < 2 ^ 256 →
      ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (v :: t :: r :: ret :: S) M (X + c)) t_0a25_c34
        (.returned (St (mvBase sevm (afterSload sevm b (ky r)) v t r) (Bytes.toB256 [1] :: S)
          (mvMem (scr M (m20 &&& (m20 &&& r)) (Bytes.toB256 [2])) v t r) X))} :=
  ⟨_, fun fork static hM room hF hle hnof X hX => by
    have hg := ltCheck_ky hle
    iterate 43 xs
    exact (e5W sevm _ _ v t r ret S _).2 fork static (by xfp) (by xroom)
      (by xnorm; with_reducible assumption) (by xnorm; with_reducible assumption) X hX⟩

/-- The word `uint(-1)`. -/
local notation "mx" => Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
  255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

/-- The scratch image of the allowance hash of owner `r`, spender `c`. -/
abbrev am (M : Mem) (r c : B256) : Mem :=
  scr (scr M (m20 &&& (m20 &&& r)) (Bytes.toB256 [3])) (m20 &&& (m20 &&& c))
    (mapSlot (m20 &&& (m20 &&& r)) (Bytes.toB256 [3]))

/-- **Entry 34, an unlimited allowance**, forward. -/
@[irreducible] noncomputable def e34MaxW (sevm : Sevm) (b : Devm) (v t r ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      FpM (Bytes.toB256 [128]) 96 M → S.length < 970 →
      B256.eqCheck (m20 &&& r) (m20 &&& sevm.caller.toB256) = 0 →
      B256.eqCheck (b.getStorVal sevm.currentTarget (an r sevm.caller)) mx = 1 →
      v.toNat ≤ (b.getStorVal sevm.currentTarget (kn r)).toNat →
      v.toNat + (((Devm.getStor b sevm.currentTarget).set (kn r)
        (b.getStorVal sevm.currentTarget (kn r) - v)).get (kn t)).toNat < 2 ^ 256 →
      ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (v :: t :: r :: ret :: S) M (X + c)) t_0a25_c34
        (.returned (St (mvBase sevm (afterSload sevm (afterSload sevm b (ky r))
            (ak r sevm.caller.toB256)) v t r) (Bytes.toB256 [1] :: S)
          (mvMem (am (scr M (m20 &&& (m20 &&& r)) (Bytes.toB256 [2])) r sevm.caller.toB256) v t r) X))} :=
  ⟨_, fun fork static hM room hF hA hle hnof X hX => by
    have hg := ltCheck_ky hle
    iterate 83 xs
    exact (e5W sevm _ _ v t r ret S _).2 fork static (by xfp) (by xroom)
      (by xnorm; with_reducible assumption) (by xnorm; with_reducible assumption) X hX⟩

/-- The ledger after a limited allowance's debit, normalized. -/
abbrev spent (σ : Stor) (r : B256) (c : Adr) (v : B256) : Stor := σ.set (an r c) (σ.get (an r c) - v)

/-- The base after three allowance reads and the debit. -/
def limBase (sevm : Sevm) (b : Devm) (v r c : B256) : Devm :=
  afterSstore sevm (afterSload sevm (afterSload sevm (afterSload sevm (afterSload sevm b (ky r))
    (ak r c)) (ak r c)) (ak r c)) (ak r c)
    ((afterSload sevm (afterSload sevm (afterSload sevm b (ky r)) (ak r c)) (ak r c)).getStorVal
      sevm.currentTarget (ak r c) - v)

/-- **Entry 34, a limited allowance**, forward. -/
@[irreducible] noncomputable def e34LimW (sevm : Sevm) (b : Devm) (v t r ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      FpM (Bytes.toB256 [128]) 96 M → S.length < 960 →
      B256.eqCheck (m20 &&& r) (m20 &&& sevm.caller.toB256) = 0 →
      B256.eqCheck (b.getStorVal sevm.currentTarget (an r sevm.caller)) mx = 0 →
      v.toNat ≤ (b.getStorVal sevm.currentTarget (an r sevm.caller)).toNat →
      v.toNat ≤ (b.getStorVal sevm.currentTarget (kn r)).toNat →
      v.toNat ≤ ((spent (Devm.getStor b sevm.currentTarget) r sevm.caller v).get (kn r)).toNat →
      v.toNat + (((spent (Devm.getStor b sevm.currentTarget) r sevm.caller v).set (kn r)
        ((spent (Devm.getStor b sevm.currentTarget) r sevm.caller v).get (kn r) - v)).get
          (kn t)).toNat < 2 ^ 256 →
      ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (v :: t :: r :: ret :: S) M (X + c)) t_0a25_c34
        (.returned (St (mvBase sevm (limBase sevm b v r sevm.caller.toB256) v t r) (Bytes.toB256 [1] :: S)
          (mvMem (am (am (am (am (scr M (m20 &&& (m20 &&& r)) (Bytes.toB256 [2])) r sevm.caller.toB256)
            r sevm.caller.toB256) r sevm.caller.toB256) r sevm.caller.toB256) v t r) X))} :=
  ⟨_, fun fork static hM room hF hA hlim hle hle1 hnof X hX => by
    have hg := ltCheck_ky hle
    have hl : B256.ltCheck (b.getStorVal sevm.currentTarget (an r sevm.caller)) v = 0 :=
      B256.ltCheck_eq_zero_of_toNat_le hlim
    iterate 124 xs
    iterate 40 xs
    xcallM e36W 3 [] (by xnorm; with_reducible assumption) (by xroom)
    iterate 40 xs
    refine (e5W sevm _ _ v t r ret S _).2 fork static (by xfp) (by xroom) ?_ ?_ X hX
    · xnorm
      exact hle1
    · xnorm
      simp only [afterSstore_getStor_self, afterSload_getStor]
      exact hnof
    all_goals ((try unfold gCallStipend); omega)⟩

/-- **Entry 10, `transfer`**, forward. -/
@[irreducible] noncomputable def e10W (sevm : Sevm) (b : Devm) (v t ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      FpM (Bytes.toB256 [128]) 96 M → S.length < 950 →
      v.toNat ≤ (b.getStorVal sevm.currentTarget (kn sevm.caller.toB256)).toNat →
      v.toNat + (((Devm.getStor b sevm.currentTarget).set (kn sevm.caller.toB256)
        (b.getStorVal sevm.currentTarget (kn sevm.caller.toB256) - v)).get (kn t)).toNat < 2 ^ 256 →
      ∀ X, 2300 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (v :: t :: ret :: S) M (X + c)) t_1df4_c10
        (.returned (St (mvBase sevm (afterSload sevm b (ky sevm.caller.toB256)) v t sevm.caller.toB256)
          (Bytes.toB256 [1] :: S)
          (mvMem (scr M (m20 &&& (m20 &&& sevm.caller.toB256)) (Bytes.toB256 [2])) v t sevm.caller.toB256) X))} :=
  ⟨_, fun fork static hM room hle hnof X hX => by
    xrun
    xcallMT e34SelfW 4 [] fork static (by xfp) (by xroom)
      (by simp only [B256.eqCheck, ↓reduceIte]) hle hnof
    xrun
    all_goals omega⟩

/-- **Entry 29, `balanceOf`**, forward: stack `a, ret`; the answer over `ret`. -/
@[irreducible] noncomputable def e29W (sevm : Sevm) (b : Devm) (a ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork →
      FpM (Bytes.toB256 [128]) 96 M → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (a :: ret :: S) M (X + c)) t_128f_c29
        (.returned (St (afterSload sevm b (mapSlot a (Bytes.toB256 [2])))
          (b.getStorVal sevm.currentTarget (mapSlot a (Bytes.toB256 [2])) :: ret :: S)
          ((M.write 32 (Bytes.toB256 [2]).toBytes).write 0 a.toBytes) X))} :=
  ⟨_, fun fork hM room X => by
    have := hM.ge
    iterate 9 xs
    apply rk
    refine rx_keccakRev hM.wf (by with_reducible rfl) (by xfp) (by decide) (by decide) (by xroom) ?_
    xrun⟩

/-! ## The frames -/

/-- The word `transfer` returns before `RETURN`. -/
abbrev okWord : B256 := B256.eqCheck (B256.eqCheck (B256.eqCheck (B256.eqCheck (Bytes.toB256 [1]) 0) 0) 0) 0

/-- A frame's selector word as the dispatcher reads it. -/
abbrev selW (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [224]).toNat

/-- The prologue's image. -/
abbrev mem0 : Mem := Mem.empty.write 64 (Bytes.toB256 [128]).toBytes

/-- The halting state of a frame returning the word `w` at `0x80` from base `B` and image `M`. -/
def retAt (B : Devm) (S : List B256) (M : Mem) (w : B256) (G : Nat) : Devm :=
  ((St B S M G).memRead (Bytes.toB256 [128]).toNat
    (Bytes.toB256 [32] + Bytes.toB256 [128] - Bytes.toB256 [128]).toNat).2.withOutput w.toBytes

/-- The guards a frame's prologue and wrapper make, with `n` argument words. -/
structure Guards (sevm : Sevm) (sel n : B256) : Prop where
  value : sevm.value = 0
  short : (Nat.toB256 sevm.data.length <? Bytes.toB256 [4]) = 0
  args : ((Nat.toB256 sevm.data.length - Bytes.toB256 [4]) <? n) = 0
  sel : selW sevm = sel

/-- `transfer`'s arguments as its wrapper decodes them. -/
abbrev xTo (sevm : Sevm) : B256 := m20 &&& Sevm.dataWord sevm (Bytes.toB256 [4])
abbrev xVal (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4])

/-- The base `transfer` halts from. -/
def xferBase (sevm : Sevm) (b : Devm) : Devm :=
  mvBase sevm (afterSload sevm b (ky sevm.caller.toB256)) (xVal sevm) (xTo sevm) sevm.caller.toB256

/-- The image `transfer` halts with. -/
abbrev xferMem (sevm : Sevm) : Mem :=
  (mvMem (scr mem0 (m20 &&& (m20 &&& sevm.caller.toB256)) (Bytes.toB256 [2])) (xVal sevm) (xTo sevm)
    sevm.caller.toB256).write 128 okWord.toBytes

/-- **The `transfer` frame, forward**. -/
@[irreducible] noncomputable def xferW (sevm : Sevm) (b : Devm) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      Guards sevm 0xa9059cbb (Bytes.toB256 [64]) →
      (xVal sevm).toNat ≤ (b.getStorVal sevm.currentTarget (kn sevm.caller.toB256)).toNat →
      (xVal sevm).toNat + (((Devm.getStor b sevm.currentTarget).set (kn sevm.caller.toB256)
        (b.getStorVal sevm.currentTarget (kn sevm.caller.toB256) - xVal sevm)).get (kn (xTo sevm))).toNat
        < 2 ^ 256 →
      ∀ G, 2300 ≤ G →
      SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + c)) t_0000_c0
        (.halted (retAt (xferBase sevm b) [selW sevm] (xferMem sevm) okWord G))} :=
  ⟨_, fun fork static facts hle hnof G hG => by
    obtain ⟨value, short, args, sel⟩ := facts
    xrun
    xcallMT e10W 3 [] fork static (by xfp) (by xroom) hle hnof
    xrun
    refine rk0 ?_
    apply rx_returnP
    · with_reducible rfl
    · xfp
    · xfp
    · decide
    · decide
    all_goals omega⟩

/-- `transferFrom`'s arguments as its wrapper decodes them. -/
abbrev pSrc (sevm : Sevm) : B256 := m20 &&& Sevm.dataWord sevm (Bytes.toB256 [4])
abbrev pTo (sevm : Sevm) : B256 := m20 &&& Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4])
abbrev pVal (sevm : Sevm) : B256 :=
  Sevm.dataWord sevm (Bytes.toB256 [32] + (Bytes.toB256 [32] + Bytes.toB256 [4]))

/-- **The `transferFrom` frame around its callee, forward**: whichever allowance branch entry 34
takes, given as a run `hc` to base `B` and image `Mr` at charge `cc`. -/
@[irreducible] noncomputable def pullFrameW (sevm : Sevm) (b B : Devm) (Mr : Mem) (cc : Nat) :
    {c : Nat // CoveredFork sevm.benvStat.fork → Guards sevm 0x23b872dd (Bytes.toB256 [96]) →
      FpM (Bytes.toB256 [128]) 160 Mr →
      (∀ X, 2300 ≤ X → SFunc.RunExact cert.prog sevm
        (St b (pVal sevm :: pTo sevm :: pSrc sevm :: Bytes.toB256 [2, 186] :: [selW sevm]) mem0 (X + cc))
        t_0a25_c34 (.returned (St B (Bytes.toB256 [1] :: [selW sevm]) Mr X))) →
      ∀ G, 2300 ≤ G →
      SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + c)) t_0000_c0
        (.halted (retAt B [selW sevm] (Mr.write 128 okWord.toBytes) okWord G))} :=
  ⟨_, fun fork facts hMr hc G hG => by
    obtain ⟨value, short, args, sel⟩ := facts
    xrun
    refine' rx_callKT (hj := by rfl) (hc := hc) ?_ ?_
    rotate_left
    xrun
    refine rk0 ?_
    apply rx_returnP
    · with_reducible rfl
    · exact hMr
    · xfp
    · decide
    · decide
    all_goals omega⟩

/-- `balanceOf`'s argument as its wrapper decodes it. -/
abbrev bHolder (sevm : Sevm) : B256 := m20 &&& Sevm.dataWord sevm (Bytes.toB256 [4])

/-- The answer of `balanceOf`. -/
abbrev bAns (sevm : Sevm) (b : Devm) : B256 :=
  b.getStorVal sevm.currentTarget (mapSlot (bHolder sevm) (Bytes.toB256 [2]))

/-- The image `balanceOf` halts with. -/
abbrev balMem (sevm : Sevm) (b : Devm) : Mem :=
  ((mem0.write 32 (Bytes.toB256 [2]).toBytes).write 0 (bHolder sevm).toBytes).write 128 (bAns sevm b).toBytes

/-- **The `balanceOf` frame, forward**, static or not. -/
@[irreducible] noncomputable def balW (sevm : Sevm) (b : Devm) :
    {c : Nat // CoveredFork sevm.benvStat.fork → Guards sevm 0x70a08231 (Bytes.toB256 [32]) → ∀ G,
      SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + c)) t_0000_c0
        (.halted (retAt (afterSload sevm b (mapSlot (bHolder sevm) (Bytes.toB256 [2])))
          [Bytes.toB256 [4, 139], selW sevm] (balMem sevm b) (bAns sevm b) G))} :=
  ⟨_, fun fork facts G => by
    obtain ⟨value, short, args, sel⟩ := facts
    xrun
    xcallM e29W 2 [] fork (by xfp) (by xroom)
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

theorem e36W_le : (e36W sevm b v t ret S M).1 ≤ 100 := by
  unfold e36W; dsimp only; xcost []

theorem e37W_le : (e37W sevm b v t ret S M).1 ≤ 100 := by
  unfold e37W; dsimp only; xcost []

theorem e29W_le : (e29W sevm b a ret S M).1 ≤ 2300 := by
  unfold e29W; dsimp only; xcost []

theorem e5W_le (p : B256) : (e5W sevm b p v t r ret S M).1 ≤ 52000 := by
  unfold e5W; dsimp only; xcost [e36W_le, e37W_le]

theorem e34SelfW_le : (e34SelfW sevm b v t r ret S M).1 ≤ 55000 := by
  unfold e34SelfW; dsimp only; xcost [e5W_le]

theorem e34MaxW_le : (e34MaxW sevm b v t r ret S M).1 ≤ 58000 := by
  unfold e34MaxW; dsimp only; xcost [e5W_le]

theorem e34LimW_le : (e34LimW sevm b v t r ret S M).1 ≤ 87000 := by
  unfold e34LimW; dsimp only; xcost [e5W_le, e36W_le]

theorem e10W_le : (e10W sevm b v t ret S M).1 ≤ 55500 := by
  unfold e10W; dsimp only; xcost [e34SelfW_le]

theorem xferW_le : (xferW sevm b).1 ≤ 56500 := by
  unfold xferW; dsimp only; xcost [e10W_le]

theorem balW_le : (balW sevm b).1 ≤ 3000 := by
  unfold balW; dsimp only; xcost [e29W_le]

theorem pullFrameW_le (B : Devm) (Mr : Mem) (cc : Nat) : (pullFrameW sevm b B Mr cc).1 ≤ cc + 1000 := by
  unfold pullFrameW; dsimp only; omega

end Charges

/-! ## What a frame leaves -/

theorem kn_bal (a : Adr) : kn a.toB256 = balSlot a := by
  unfold kn balSlot
  rw [toAdr_toB256, lit2]

theorem ky_bal (r : B256) : ky r = balSlot r.toAdr := by
  rw [ky_eq]
  unfold kn balSlot
  rw [lit2]

theorem an_allow (a sp : Adr) : an a.toB256 sp = allowSlot a sp := by
  unfold an allowSlot
  rw [toAdr_toB256, lit3]

theorem ak_allow (r : B256) (sp : Adr) : ak r sp.toB256 = allowSlot r.toAdr sp := by
  unfold ak allowSlot
  simp only [ff20_and_word, toAdr_toB256, lit3]

/-- **`B` keeps what a coin frame must**: every code, every other account's storage, the error
flag, the created accounts. -/
structure Keeps (sevm : Sevm) (pre B : Devm) : Prop where
  code : ∀ a, B.getCode a = pre.getCode a
  other : ∀ a, a ≠ sevm.currentTarget → Devm.getStor B a = Devm.getStor pre a
  error : B.error = pre.error
  created : B.createdAccounts = pre.createdAccounts

namespace Keeps

variable {sevm : Sevm} {pre B : Devm}

theorem refl (sevm : Sevm) (pre : Devm) : Keeps sevm pre pre := ⟨fun _ => rfl, fun _ _ => rfl, rfl, rfl⟩

theorem sload (h : Keeps sevm pre B) (k : B256) : Keeps sevm pre (afterSload sevm B k) :=
  ⟨fun a => (afterSload_getCode sevm B k a).trans (h.code a),
   fun a ha => (afterSload_getStor sevm B k a).trans (h.other a ha),
   (afterSload_error sevm B k).trans h.error, (afterSload_createdAccounts sevm B k).trans h.created⟩

theorem sstore (h : Keeps sevm pre B) (k v : B256) : Keeps sevm pre (afterSstore sevm B k v) :=
  ⟨fun a => (afterSstore_getCode sevm B k v a).trans (h.code a),
   fun a ha => (afterSstore_getStor_ne sevm B k v a (Ne.symm ha)).trans (h.other a ha),
   (afterSstore_error sevm B k v).trans h.error, (afterSstore_createdAccounts sevm B k v).trans h.created⟩

theorem log (h : Keeps sevm pre B) (l : Log) : Keeps sevm pre (B.addLog l) :=
  ⟨h.code, h.other, h.error, h.created⟩

theorem mv (h : Keeps sevm pre B) (v t r : B256) : Keeps sevm pre (mvBase sevm B v t r) :=
  (((((h.sload _).sstore _ _).sload _).sstore _ _).log _)

theorem lim (h : Keeps sevm pre B) (v r c : B256) : Keeps sevm pre (limBase sevm B v r c) :=
  ((((((h.sload _).sload _).sload _).sload _).sstore _ _))

end Keeps

/-- **`mvBase` is the move on the ledger.** -/
theorem mvBase_getStor (sevm : Sevm) (b : Devm) (v t r : B256) :
    Devm.getStor (mvBase sevm b v t r) sevm.currentTarget =
      moveStor (Devm.getStor b sevm.currentTarget) r.toAdr t.toAdr v := by
  unfold mvBase mvDebited moveStor
  simp only [Devm.addLog_getStor, afterSstore_getStor_self, afterSload_getStor, gsv, ky_bal]

/-- **`limBase` is the allowance debit on the ledger.** -/
theorem limBase_getStor (sevm : Sevm) (b : Devm) (v r : B256) (sp : Adr) :
    Devm.getStor (limBase sevm b v r sp.toB256) sevm.currentTarget =
      (Devm.getStor b sevm.currentTarget).set (allowSlot r.toAdr sp)
        ((Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sp) - v) := by
  unfold limBase
  simp only [afterSstore_getStor_self, afterSload_getStor, gsv, ak_allow]

/-- A first store to a slot still at its snapshot value does not lower the refund counter. -/
theorem sstore_ge {s : Sevm} {d : Devm} {k v : B256} {σ : Stor}
    (hcr : s.currentTarget ∉ d.createdAccounts) (hor : (getOrigAcct s s.currentTarget).stor = σ)
    (hcur : (Devm.getStor d s.currentTarget).get k = σ.get k) :
    d.refundCounter ≤ (afterSstore s d k v).refundCounter :=
  afterSstore_refundCounter_ge_of_original_eq_current s d k v (by
    unfold Devm.getOrigStorVal
    rw [ite_eq_right hcr]
    unfold Jaune.getOrigStorVal
    rw [hor]
    exact hcur.symm)

/-- A move's two stores, first to their slots, do not lower the refund counter. -/
theorem mvBase_refund {sevm : Sevm} {b : Devm} {v t r : B256} {σ : Stor}
    (hcr : sevm.currentTarget ∉ b.createdAccounts) (hor : (getOrigAcct sevm sevm.currentTarget).stor = σ)
    (h1 : (Devm.getStor b sevm.currentTarget).get (ky r) = σ.get (ky r))
    (h2 : (Devm.getStor b sevm.currentTarget).get (ky t) = σ.get (ky t)) (hne : ky r ≠ ky t) :
    b.refundCounter ≤ (mvBase sevm b v t r).refundCounter := by
  have a1 := sstore_ge (s := sevm) (d := afterSload sevm b (ky r)) (k := ky r)
    (v := b.getStorVal sevm.currentTarget (ky r) - v)
    (by rw [afterSload_createdAccounts]; exact hcr) hor (by rw [afterSload_getStor]; exact h1)
  have c1 : (afterSload sevm (mvDebited sevm b v r) (ky t)).createdAccounts = b.createdAccounts := by
    unfold mvDebited
    rw [afterSload_createdAccounts, afterSstore_createdAccounts, afterSload_createdAccounts]
  have a2 := sstore_ge (s := sevm) (d := afterSload sevm (mvDebited sevm b v r) (ky t)) (k := ky t)
    (v := (mvDebited sevm b v r).getStorVal sevm.currentTarget (ky t) + v)
    (by rw [c1]; exact hcr) hor (by
      unfold mvDebited
      rw [afterSload_getStor, afterSstore_getStor_self, Stor.get_set_ne _ hne, afterSload_getStor]
      exact h2)
  have m : (mvBase sevm b v t r).refundCounter =
      (afterSstore sevm (afterSload sevm (mvDebited sevm b v r) (ky t)) (ky t)
        ((mvDebited sevm b v r).getStorVal sevm.currentTarget (ky t) + v)).refundCounter := by
    unfold mvBase
    exact Devm.addLog_refundCounter _ _
  rw [m]
  refine le_trans ?_ a2
  rw [afterSload_refundCounter]
  unfold mvDebited
  refine le_trans ?_ a1
  rw [afterSload_refundCounter]

/-- The allowance debit, first to its slot, does not lower the refund counter. -/
theorem limBase_refund {sevm : Sevm} {b : Devm} {v r c : B256} {σ : Stor}
    (hcr : sevm.currentTarget ∉ b.createdAccounts) (hor : (getOrigAcct sevm sevm.currentTarget).stor = σ)
    (h1 : (Devm.getStor b sevm.currentTarget).get (ak r c) = σ.get (ak r c)) :
    b.refundCounter ≤ (limBase sevm b v r c).refundCounter := by
  unfold limBase
  refine le_trans ?_ (sstore_ge (by simpa only [afterSload_createdAccounts] using hcr) hor
    (by simpa only [afterSload_getStor] using h1))
  simp only [afterSload_refundCounter]
  exact le_refl _

/-- **What a successful frame leaves**: the run, its charge `used`, the reply `w`, the ledger `σ'`,
and the rest of the world kept (the refund counter not lowered when `R` holds). -/
structure FrameLands (sevm : Sevm) (pre post : Devm) (used : Nat) (w : B256) (σ' : Stor) (R : Prop) :
    Prop where
  run : SProg.RunExact cert.prog sevm pre post
  gas : post.gasLeft = pre.gasLeft - used
  out : post.output = w.toBytes
  keeps : Keeps sevm pre post
  stor : Devm.getStor post sevm.currentTarget = σ'
  refund : R → pre.refundCounter ≤ post.refundCounter

/-- A frame run to `retAt` lands. -/
theorem frameLands_of {sevm : Sevm} {pre B : Devm} {S : List B256} {M : Mem} {w w' : B256} {c K : Nat}
    {σ' : Stor} {R : Prop}
    (hrun : ∀ G, 2300 ≤ G → SFunc.RunExact cert.prog sevm (St pre [] Mem.empty (G + c)) t_0000_c0
      (.halted (retAt B S M w G)))
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hc : c ≤ K) (hgas : K + 2300 ≤ pre.gasLeft)
    (hk : Keeps sevm pre B) (hst : Devm.getStor B sevm.currentTarget = σ') (hw : w = w')
    (hr : R → pre.refundCounter ≤ B.refundCounter) :
    FrameLands sevm pre (retAt B S M w (pre.gasLeft - c)) c w' σ' R := by
  subst hw
  refine ⟨⟨_, rfl, ?_⟩, rfl, rfl, ⟨hk.code, hk.other, hk.error, hk.created⟩, hst, hr⟩
  have h := hrun (pre.gasLeft - c) (by omega)
  rwa [pre_eq_St hs hm (Nat.sub_add_cancel (by omega))] at h

/-- **`transfer` fits**: the source covers the move and the credit does not wrap. -/
def MoveFits (σ : Stor) (src dst : Adr) (v : B256) : Prop :=
  v.toNat ≤ (σ.get (balSlot src)).toNat ∧
    v.toNat + ((σ.set (balSlot src) (σ.get (balSlot src) - v)).get (balSlot dst)).toNat < 2 ^ 256

/-- **`transferFrom` fits**, exactly what `frame_transferFrom` inverts plus the second balance test
`e5`'s `sub` makes after the allowance debit. -/
def PullFits (σ : Stor) (src sp dst : Adr) (v : B256) : Prop :=
  v.toNat ≤ (σ.get (balSlot src)).toNat ∧
    (src ≠ sp → σ.get (allowSlot src sp) ≠ maxUint → v.toNat ≤ (σ.get (allowSlot src sp)).toNat) ∧
    MoveFits (spendStor σ src sp v) src dst v

theorem okWord_eq : okWord = 1 := by decide

/-- **`transfer(dst, v)` from a frame entry, forward.** -/
theorem xfer_lands {sevm : Sevm} {pre : Devm} {dst : Adr} {v : B256}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (g : Guards sevm 0xa9059cbb (Bytes.toB256 [64])) (hdst : xTo sevm = dst.toB256) (hv : xVal sevm = v)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 58800 ≤ pre.gasLeft)
    (hfits : MoveFits (Devm.getStor pre sevm.currentTarget) sevm.caller dst v) :
    ∃ post used, used ≤ 56500 ∧ FrameLands sevm pre post used 1
      (moveStor (Devm.getStor pre sevm.currentTarget) sevm.caller dst v)
      ((getOrigAcct sevm sevm.currentTarget).stor = Devm.getStor pre sevm.currentTarget ∧
        sevm.currentTarget ∉ pre.createdAccounts ∧ balSlot sevm.caller ≠ balSlot dst) := by
  refine ⟨_, _, xferW_le sevm pre, frameLands_of (K := 56500)
    ((xferW sevm pre).2 fork static g ?_ ?_) hs hm (xferW_le sevm pre) (by omega) ?_ ?_ okWord_eq ?_⟩
  · rw [hv, kn_bal]; exact hfits.1
  · rw [hv, hdst, kn_bal, kn_bal]; exact hfits.2
  · exact (Keeps.sload (Keeps.refl sevm pre) _).mv _ _ _
  · unfold xferBase
    rw [mvBase_getStor, afterSload_getStor, hv, hdst, toAdr_toB256, toAdr_toB256]
  · rintro ⟨hor, hcr, hne⟩
    unfold xferBase
    refine le_trans (le_of_eq afterSload_refundCounter.symm)
      (mvBase_refund (σ := Devm.getStor pre sevm.currentTarget)
        (by rw [afterSload_createdAccounts]; exact hcr) hor ?_ ?_ ?_)
    · rw [afterSload_getStor]
    · rw [afterSload_getStor]
    · rw [hdst, ky_bal, ky_bal, toAdr_toB256, toAdr_toB256]; exact hne

theorem eqCheck_one {x y : B256} (h : x = y) : B256.eqCheck x y = 1 := by
  subst h
  simp only [B256.eqCheck, ↓reduceIte]

/-- The masked caller word against a masked address word. -/
theorem masked_ne {a c : Adr} (h : a ≠ c) : (m20 &&& a.toB256) ≠ (m20 &&& c.toB256) := by
  rw [ff20_and_word, ff20_and_word, toAdr_toB256, toAdr_toB256]
  exact fun e => h (Adr.toB256_inj e)

theorem pull_lands_of {sevm : Sevm} {pre B : Devm} {Mr : Mem} {cc : Nat} {σ' : Stor} {R : Prop}
    (fork : CoveredFork sevm.benvStat.fork) (g : Guards sevm 0x23b872dd (Bytes.toB256 [96]))
    (hMr : FpM (Bytes.toB256 [128]) 160 Mr)
    (hc : ∀ X, 2300 ≤ X → SFunc.RunExact cert.prog sevm
      (St pre (pVal sevm :: pTo sevm :: pSrc sevm :: Bytes.toB256 [2, 186] :: [selW sevm]) mem0 (X + cc))
      t_0a25_c34 (.returned (St B (Bytes.toB256 [1] :: [selW sevm]) Mr X)))
    (hcc : cc ≤ 87000) (hs : pre.stack = []) (hm : pre.memory = Mem.empty)
    (hgas : 90300 ≤ pre.gasLeft) (hk : Keeps sevm pre B)
    (hst : Devm.getStor B sevm.currentTarget = σ') (hr : R → pre.refundCounter ≤ B.refundCounter) :
    ∃ post used, used ≤ 88000 ∧ FrameLands sevm pre post used 1 σ' R := by
  have hle := pullFrameW_le sevm pre B Mr cc
  exact ⟨_, _, by omega, frameLands_of (K := 88000) ((pullFrameW sevm pre B Mr cc).2 fork g hMr hc) hs hm
    (by omega) (by omega) hk hst okWord_eq hr⟩

/-- **`transferFrom(src, dst, v)` from a frame entry, forward**, whichever allowance branch it takes. -/
theorem pull_lands {sevm : Sevm} {pre : Devm} {src dst : Adr} {v : B256}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (g : Guards sevm 0x23b872dd (Bytes.toB256 [96])) (hsrc : pSrc sevm = src.toB256)
    (hdst : pTo sevm = dst.toB256) (hv : pVal sevm = v)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 90300 ≤ pre.gasLeft)
    (hfits : PullFits (Devm.getStor pre sevm.currentTarget) src sevm.caller dst v) :
    ∃ post used, used ≤ 88000 ∧ FrameLands sevm pre post used 1
      (moveStor (spendStor (Devm.getStor pre sevm.currentTarget) src sevm.caller v) src dst v)
      ((getOrigAcct sevm sevm.currentTarget).stor = Devm.getStor pre sevm.currentTarget ∧
        sevm.currentTarget ∉ pre.createdAccounts ∧
        allowSlot src sevm.caller ≠ balSlot src ∧ allowSlot src sevm.caller ≠ balSlot dst ∧
        balSlot src ≠ balSlot dst) := by
  obtain ⟨h0, hl, h1, h2⟩ := hfits
  have ksrc : kn (pSrc sevm) = balSlot src := by rw [hsrc, kn_bal]
  have kdst : kn (pTo sevm) = balSlot dst := by rw [hdst, kn_bal]
  have ysrc : ky (pSrc sevm) = balSlot src := by rw [hsrc, ky_bal, toAdr_toB256]
  have ydst : ky (pTo sevm) = balSlot dst := by rw [hdst, ky_bal, toAdr_toB256]
  have asrc : an (pSrc sevm) sevm.caller = allowSlot src sevm.caller := by rw [hsrc, an_allow]
  have tsrc : (pSrc sevm).toAdr = src := by rw [hsrc, toAdr_toB256]
  have tdst : (pTo sevm).toAdr = dst := by rw [hdst, toAdr_toB256]
  by_cases hself : src = sevm.caller
  · -- the source spends its own
    have hsp : spendStor (Devm.getStor pre sevm.currentTarget) src sevm.caller v =
        Devm.getStor pre sevm.currentTarget := by
      unfold spendStor; rw [if_neg (fun hh => hh.1 hself)]
    rw [hsp] at h1 h2 ⊢
    refine pull_lands_of (cc := (e34SelfW sevm pre (pVal sevm) (pTo sevm) (pSrc sevm) (Bytes.toB256 [2, 186])
        [selW sevm] mem0).1) fork g (by xfp)
      (fun X hX => (e34SelfW sevm pre _ _ _ _ _ _).2 fork static (FpM.init _) (by xroom) ?_ ?_ ?_ X hX)
      ((e34SelfW_le ..).trans (by decide)) hs hm hgas ((Keeps.sload (Keeps.refl sevm pre) _).mv _ _ _) ?_ ?_
    · rw [hsrc, hself]; exact eqCheck_one rfl
    · rw [hv, ksrc]; exact h1
    · rw [hv, ksrc, kdst]; exact h2
    · rw [mvBase_getStor, afterSload_getStor, hv, tsrc, tdst]
    · rintro ⟨hor, hcr, -, -, hne⟩
      refine le_trans (le_of_eq afterSload_refundCounter.symm)
        (mvBase_refund (σ := Devm.getStor pre sevm.currentTarget)
          (by rw [afterSload_createdAccounts]; exact hcr) hor ?_ ?_ ?_)
      · rw [afterSload_getStor]
      · rw [afterSload_getStor]
      · rw [ysrc, ydst]; exact hne
  · have hF : B256.eqCheck (m20 &&& pSrc sevm) (m20 &&& sevm.caller.toB256) = 0 := by
      rw [hsrc]; exact eqCheck_ne (masked_ne hself)
    by_cases hmax : (Devm.getStor pre sevm.currentTarget).get (allowSlot src sevm.caller) = maxUint
    · -- an unlimited allowance
      have hsp : spendStor (Devm.getStor pre sevm.currentTarget) src sevm.caller v =
          Devm.getStor pre sevm.currentTarget := by
        unfold spendStor; rw [if_neg (fun hh => hh.2 hmax)]
      rw [hsp] at h1 h2 ⊢
      refine pull_lands_of (cc := (e34MaxW sevm pre (pVal sevm) (pTo sevm) (pSrc sevm) (Bytes.toB256 [2, 186])
          [selW sevm] mem0).1) fork g (by xfp)
        (fun X hX => (e34MaxW sevm pre _ _ _ _ _ _).2 fork static (FpM.init _) (by xroom) hF ?_ ?_ ?_ X hX)
        ((e34MaxW_le ..).trans (by decide)) hs hm hgas
        ((((Keeps.refl sevm pre).sload _).sload _).mv _ _ _) ?_ ?_
      · rw [asrc]; exact eqCheck_one hmax
      · rw [hv, ksrc]; exact h1
      · rw [hv, ksrc, kdst]; exact h2
      · rw [mvBase_getStor, afterSload_getStor, afterSload_getStor, hv, tsrc, tdst]
      · rintro ⟨hor, hcr, -, -, hne⟩
        refine le_trans (le_of_eq (afterSload_refundCounter.symm.trans afterSload_refundCounter.symm))
          (mvBase_refund (σ := Devm.getStor pre sevm.currentTarget)
            (by rw [afterSload_createdAccounts, afterSload_createdAccounts]; exact hcr) hor ?_ ?_ ?_)
        · rw [afterSload_getStor, afterSload_getStor]
        · rw [afterSload_getStor, afterSload_getStor]
        · rw [ysrc, ydst]; exact hne
    · -- a limited allowance
      have hsp : spendStor (Devm.getStor pre sevm.currentTarget) src sevm.caller v =
          (Devm.getStor pre sevm.currentTarget).set (allowSlot src sevm.caller)
            ((Devm.getStor pre sevm.currentTarget).get (allowSlot src sevm.caller) - v) := by
        unfold spendStor; rw [if_pos ⟨hself, hmax⟩]
      rw [hsp] at h1 h2 ⊢
      refine pull_lands_of (cc := (e34LimW sevm pre (pVal sevm) (pTo sevm) (pSrc sevm) (Bytes.toB256 [2, 186])
          [selW sevm] mem0).1) fork g (by xfp)
        (fun X hX => (e34LimW sevm pre _ _ _ _ _ _).2 fork static (FpM.init _) (by xroom) hF ?_ ?_ ?_ ?_ ?_ X hX)
        (e34LimW_le ..) hs hm hgas ((Keeps.refl sevm pre).lim _ _ _ |>.mv _ _ _) ?_ ?_
      · rw [asrc]; exact eqCheck_ne hmax
      · rw [hv, asrc]; exact hl hself hmax
      · rw [hv, ksrc]; exact h0
      · unfold spent; rw [hv, asrc, ksrc]; exact h1
      · unfold spent; rw [hv, asrc, ksrc, kdst]; exact h2
      · rw [mvBase_getStor, limBase_getStor, hv, hsrc, toAdr_toB256, tdst]
      · rintro ⟨hor, hcr, ha1, ha2, hne⟩
        refine le_trans (limBase_refund (v := pVal sevm) (r := pSrc sevm) (c := sevm.caller.toB256) hcr hor ?_)
          (mvBase_refund (σ := Devm.getStor pre sevm.currentTarget)
            (by unfold limBase; simpa only [afterSstore_createdAccounts, afterSload_createdAccounts] using hcr) hor ?_ ?_ ?_)
        · rfl
        · rw [limBase_getStor, ysrc, hsrc, toAdr_toB256]
          exact Stor.get_set_ne _ ha1 _
        · rw [limBase_getStor, ydst, hsrc, toAdr_toB256]
          exact Stor.get_set_ne _ ha2 _
        · rw [ysrc, ydst]; exact hne

/-- **`balanceOf(a)` from a frame entry, forward**, static or not: it answers `a`'s entry and writes
nothing. -/
theorem bal_lands {sevm : Sevm} {pre : Devm} {a : Adr}
    (fork : CoveredFork sevm.benvStat.fork) (g : Guards sevm 0x70a08231 (Bytes.toB256 [32]))
    (hholder : bHolder sevm = a.toB256)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 5300 ≤ pre.gasLeft) :
    ∃ post used, used ≤ 3000 ∧ FrameLands sevm pre post used
      ((Devm.getStor pre sevm.currentTarget).get (balSlot a)) (Devm.getStor pre sevm.currentTarget) True := by
  refine ⟨_, _, balW_le sevm pre, frameLands_of (K := 3000)
    (fun G _ => (balW sevm pre).2 fork g G) hs hm (balW_le sevm pre) (by omega)
    ((Keeps.refl sevm pre).sload _) ?_ ?_ ?_⟩
  · rw [afterSload_getStor]
  · show pre.getStorVal sevm.currentTarget (mapSlot (bHolder sevm) (Bytes.toB256 [2])) = _
    rw [hholder, lit2]
    rfl
  · exact fun _ => le_of_eq afterSload_refundCounter.symm

end Blanc.Lift.Dai
