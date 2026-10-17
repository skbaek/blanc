import Blanc.Lift.Curve3Pool.KitCheck
import Blanc.Lift.Curve3Pool.Layout
import Blanc.Lift.VyperCallee
import Blanc.Lift.ReachWalk

/-!
# The callees `_xp` (pc `0x281`, entry 31) and `_xp_mem` (pc `0x3a1`, entry 34)

`_xp()` and `_xp_mem(_balances)` (source lines 175–190) scale the three balances by `RATES` and
divide by `PRECISION`, returning the `uint256[3]` result on the stack (coin 0 on top) through
Vyper 0.2.4's tuple push loop.  `_xp` reads `self.balances` (`keccak(1) + i`, the hashing scratch
word `0xc0`), its frame is `[0x140, 0x200)`, the return address at `0x140`; `_xp_mem` takes the
balances on the stack under its return address, its frame is `[0x140, 0x260)`, the return
address at `0x1a0`.  The certificate unrolls each 3-iteration loop and each push loop into
copies (`_xp`: entries 31 → 56 → 83, push 83 → 105 → 126 → 148 → 170; `_xp_mem`: 34 → 59 → 86,
push 86 → 108 → 129 → 151 → 173); the walks step through every copy with the same template
tactic (`xpiter`, `xppush`, `xpmemiter`, `xpmempush`).

* `XpLands sevm s b S M d` / `xp_spec`: `_xp` returns the words of `xpChk s.balances` over
  `xpBase` (three balance loads), the memory kept off `[0xc0, 0xe0) ∪ [0x140, 0x200)`;
* `XpMemLands b a₀ a₁ a₂ S M d` / `xpMem_spec`: `_xp_mem` returns the words of
  `xpChk ⟨a₀, a₁, a₂⟩` over the untouched base, the memory kept off `[0x140, 0x260)`;
* kernel facts over each entry closure: `SilentSet`, `ExecFreeSet`, `calleeNeverHalts`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune
open Blanc.StableSwapNewton

/-! ## The value contract -/

/-- The bytes `_xp` writes: the hashing scratch word `0xc0` and its frame `[0x140, 0x200)`. -/
abbrev xpWin : List (Nat × Nat) := [(0xc0, 0xe0), (0x140, 0x200)]

/-- The base `_xp` leaves: the three `balances` words loaded. -/
def xpBase (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm (afterSload sevm (afterSload sevm b (balanceSlot 0)) (balanceSlot 1))
    (balanceSlot 2)

/-- **What `_xp` leaves**: the words of `xpChk s.balances` (coin 0 on top) over the caller's
stack, over `xpBase`, with the entry memory kept off `xpWin`. -/
def XpLands (sevm : Sevm) (s : State) (b : Devm) (S : List B256) (M : Mem) (d : Devm) : Prop :=
  ∃ x0 x1 x2 M' G', d = St (xpBase sevm b) (x0 :: x1 :: x2 :: S) M' G' ∧
    xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧ Mem.KeepsOff M M' xpWin ∧
    Mem.Wf M'

theorem xpBase_sloadsOnly (sevm : Sevm) (b : Devm) : SloadsOnly sevm b (xpBase sevm b) :=
  (((SloadsOnly.refl).sload _).sload _).sload _

set_option hygiene false in
/-- One `_xp` iteration (`0x2c6` … `0x358`) at result offset `o`, up to its back-edge `JUMPI`:
the balance load, the checked product and the division by `PRECISION` (`hm`, `hd`). -/
macro "xpiter " o:term:max hm:ident hd:ident : tactic => `(tactic| (
  (have hd0 := ric_dest run; clear run; obtain ⟨_, run⟩ := hd0)
  istep; imload 0x1c0; istep; istep; istep; istep
  iassert hlt
  istep; istep; istep; imload' $o; imload 0x1c0; istep; istep; istep; istep
  iassert hlt
  istep; imstoreO 0xc0; istep; istep; ikeccak 0xc0; istep; istep
  istep; istep; istep; istep; istep; istep; istep; istep; istep; istep; istep; istep
  iassert $hm
  istep; istep; istep; istep; istep; istep; istep; istep; istep; istep; istep
  iassert $hd
  istep; istep; istep; istep; istep; istep; istep; imload 0x1c0; istep; istep; istep; istep
  iassert hlt
  istep; istep; istep; imstoreO' $o
  (have hd0 := ric_dest run; clear run; obtain ⟨_, run⟩ := hd0)
  istep; imload' 0x1c0; istep; istep; istep; istep; imstoreO' 0x1c0
  istep; istep; istep; istep))

theorem prog_56 : prog[56]? = some t_02c6_c56 := by decide +kernel

theorem prog_83 : prog[83]? = some t_02c6_c83 := by decide +kernel
theorem prog_105 : prog[105]? = some t_0364_c105 := by decide +kernel
theorem prog_126 : prog[126]? = some t_0364_c126 := by decide +kernel
theorem prog_148 : prog[148]? = some t_0364_c148 := by decide +kernel
theorem prog_170 : prog[170]? = some t_0392_c170 := by decide +kernel

set_option hygiene false in
/-- A back edge `JUMPI` into the next unrolled copy `k`; the fall-through is dead. -/
macro "inext " hk:term : tactic => `(tactic| (
  have hbr := ric_branchTo (List.not_mem_nil) $hk run; clear run
  rcases hbr with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (ric_undefined run).elim))

set_option hygiene false in
/-- One step of the tuple push loop (`0x364`/`0x376`): push the word at `o`, then jump to the
next copy `k`. -/
macro "xppush " o:term:max hk:term:max : tactic => `(tactic| (
  (have hd0 := ric_dest run; clear run; obtain ⟨_, run⟩ := hd0)
  istep; imload 0x1e0; istep; istep; istep; istep
  iassert hc
  istep; imload 0x1e0; istep; istep; istep; imload' $o
  istep; imload 0x1e0; istep; istep; imstoreO' 0x1e0; istep
  (have hj := ric_jump (List.not_mem_nil) $hk run; clear run; obtain ⟨_, run⟩ := hj)))

/-- One coin of `xpChk`, from the product guard and the division by a nonzero word. -/
theorem xp_coin {r p bal : B256} {k : Fin 3}
    (hm : (B256.eqCheck ((r * bal) / r) bal ||| B256.eqCheck r 0) ≠ 0) (hd : p ≠ 0)
    (hr : r.toNat = rates.get k) (hp : p.toNat = precision) :
    (do chkDiv (← chkMul (rates.get k) bal.toNat) precision) = some ((r * bal) / p).toNat := by
  rw [← hr, ← hp, vyChkMul hm]
  simp only [Option.bind_eq_bind, Option.bind_some]
  exact vyChkDiv hd

theorem xp_slot0 : (Bytes.toB256 [1]).toBytes.keccak + Bytes.toB256 [0] = balanceSlot 0 := by
  rw [show Bytes.toB256 [1] = (1 : B256) from by decide, balancesBase_eq]
  unfold balanceSlot
  congr 1

theorem xp_slot1 : (Bytes.toB256 [1]).toBytes.keccak + (Bytes.toB256 [1] + Bytes.toB256 [0]) =
    balanceSlot 1 := by
  rw [show Bytes.toB256 [1] = (1 : B256) from by decide, balancesBase_eq]
  unfold balanceSlot
  congr 1

theorem xp_slot2 : (Bytes.toB256 [1]).toBytes.keccak +
    (Bytes.toB256 [1] + (Bytes.toB256 [1] + Bytes.toB256 [0])) = balanceSlot 2 := by
  rw [show Bytes.toB256 [1] = (1 : B256) from by decide, balancesBase_eq]
  unfold balanceSlot
  congr 1

-- SEGMENT: xpSpec
/-- **`_xp`'s contract**: every run of entry 31 from its return address over the caller's stack
returns, and lands as `XpLands`: the three words of `xpChk s.balances` on top of `S`, over the
loads of `xpBase`, the memory kept off `xpWin`. -/
theorem xp_spec {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {ret : B256}
    {s : State} {o : Outcome} (hfork : CoveredFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s) (hwf : Mem.Wf M)
    (run : SFunc.Run prog sevm (St b (ret :: S) M G) t_0281_c31 o) :
    ∃ d, o = .returned d ∧ XpLands sevm s b S M d := by
  have run := run.cut
  have hT := MemTrack.init hwf xpWin
  obtain ⟨_, run⟩ := ric_dest run
  imstoreO 0x140; istep; istep; istep; imstoreO' 0x160
  istep; istep; istep; istep; imstoreO' 0x180
  istep; istep; istep; istep; imstoreO' 0x1a0
  istep; istep; istep; istep; istep; istep; imstoreO' 0x1c0; istep
  xpiter 0x160 hm0 hd0
  inext prog_56
  xpiter 0x180 hm1 hd1
  inext prog_83
  xpiter 0x1a0 hm2 hd2
  have hbr := ric_branch run; clear run
  rcases hbr with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact (ric_undefined run).elim
  (have hd0 := ric_dest run; clear run; obtain ⟨_, run⟩ := hd0)
  istep; istep; istep; imstoreO 0x1e0
  xppush 0x1a0 prog_105
  xppush 0x180 prog_126
  xppush 0x160 prog_148
  (have hd0 := ric_dest run; clear run; obtain ⟨_, run⟩ := hd0)
  istep; imload 0x1e0; istep; istep; istep; istep
  have hbr := ric_branch run; clear run
  rcases hbr with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact (ric_undefined run).elim
  istep
  (have hj := ric_jump (List.not_mem_nil) prog_170 run; clear run; obtain ⟨_, run⟩ := hj)
  (have hd0 := ric_dest run; clear run; obtain ⟨_, run⟩ := hd0)
  imload 0x140
  obtain ⟨G', hr⟩ := ric_ret run
  cases hr
  simp only [xp_slot0, xp_slot1, xp_slot2, afterSload_getStorVal] at hm0 hm1 hm2 ⊢
  refine ⟨_, rfl, _, _, _, _, G', rfl, ?_, hT.keeps, hT.wf⟩
  have c0 := xp_coin (k := 0) hm0 hd0 (by decide) (by decide)
  have c1 := xp_coin (k := 1) hm1 hd1 (by decide) (by decide)
  have c2 := xp_coin (k := 2) hm2 hd2 (by decide) (by decide)
  simp only [getStorVal_eq_getStor, ha.balances] at c0 c1 c2
  simp only [xpChk, V3.ofFnM, c0, c1, c2, Option.bind_eq_bind, Option.bind_some]
  rfl

/-! ## `_xp_mem` (pc `0x3a1`, entry 34) -/

/-- The bytes `_xp_mem` writes: its frame `[0x140, 0x260)`. -/
abbrev xpMemWin : List (Nat × Nat) := [(0x140, 0x260)]

/-- **What `_xp_mem` leaves**: the words of `xpChk ⟨a₀, a₁, a₂⟩` (coin 0 on top) over the
caller's stack, the base untouched, the entry memory kept off `[0x140, 0x260)`. -/
def XpMemLands (b : Devm) (a0 a1 a2 : B256) (S : List B256) (M : Mem) (d : Devm) : Prop :=
  ∃ x0 x1 x2 M' G', d = St b (x0 :: x1 :: x2 :: S) M' G' ∧
    xpChk ⟨a0.toNat, a1.toNat, a2.toNat⟩ = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
    Mem.KeepsOff M M' xpMemWin ∧ Mem.Wf M'

theorem prog_59 : prog[59]? = some t_03f2_c59 := by decide +kernel
theorem prog_86 : prog[86]? = some t_03f2_c86 := by decide +kernel
theorem prog_108 : prog[108]? = some t_048c_c108 := by decide +kernel
theorem prog_129 : prog[129]? = some t_048c_c129 := by decide +kernel
theorem prog_151 : prog[151]? = some t_048c_c151 := by decide +kernel
theorem prog_173 : prog[173]? = some t_04ba_c173 := by decide +kernel

set_option hygiene false in
/-- One `_xp_mem` iteration (`0x3f2` … `0x480`) at coin offset `i32 = 32 i`. -/
macro "xpmemiter " r:term:max a:term:max hm:ident hd:ident : tactic => `(tactic| (
  (have hd0 := ric_dest run; clear run; obtain ⟨_, run⟩ := hd0)
  istep; imload 0x220; istep; istep; istep; istep
  iassert hlt
  istep; istep; istep; imload' $r; istep; imload 0x220; istep; istep; istep; istep
  iassert hlt
  istep; istep; istep; imload' $a
  istep; istep; istep; istep; istep; istep; istep; istep; istep; istep; istep; istep
  iassert $hm
  istep; istep; istep; istep; istep; istep; istep; istep; istep; istep; istep
  iassert $hd
  istep; istep; istep; istep; istep; istep; istep; imload 0x220; istep; istep; istep; istep
  iassert hlt
  istep; istep; istep; imstoreO' $r
  (have hd0 := ric_dest run; clear run; obtain ⟨_, run⟩ := hd0)
  istep; imload' 0x220; istep; istep; istep; istep; imstoreO' 0x220
  istep; istep; istep; istep))

set_option hygiene false in
/-- One step of `_xp_mem`'s tuple push loop (`0x48c`/`0x49e`). -/
macro "xpmempush " o:term:max hk:term:max : tactic => `(tactic| (
  (have hd0 := ric_dest run; clear run; obtain ⟨_, run⟩ := hd0)
  istep; imload 0x240; istep; istep; istep; istep
  iassert hc
  istep; imload 0x240; istep; istep; istep; imload' $o
  istep; imload 0x240; istep; istep; imstoreO' 0x240; istep
  (have hj := ric_jump (List.not_mem_nil) $hk run; clear run; obtain ⟨_, run⟩ := hj)))

-- SEGMENT: xpMemSpec
/-- **`_xp_mem`'s contract**: every run of entry 34 from its return address over the three
balances `a₀ a₁ a₂` returns, and lands as `XpMemLands`. -/
theorem xpMem_spec {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {ret a0 a1 a2 : B256} {o : Outcome} (hwf : Mem.Wf M)
    (run : SFunc.Run prog sevm (St b (ret :: a0 :: a1 :: a2 :: S) M G) t_03a1_c34 o) :
    ∃ d, o = .returned d ∧ XpMemLands b a0 a1 a2 S M d := by
  have run := run.cut
  have hT := MemTrack.init hwf xpMemWin
  obtain ⟨_, run⟩ := ric_dest run
  imstoreO 0x1a0; imstoreO 0x140; imstoreO 0x160; imstoreO 0x180
  istep; istep; istep; imstoreO' 0x1c0
  istep; istep; istep; istep; imstoreO' 0x1e0
  istep; istep; istep; istep; imstoreO' 0x200
  istep; istep; istep; istep; istep; istep; imstoreO' 0x220; istep
  xpmemiter 0x1c0 0x140 hm0 hd0
  inext prog_59
  xpmemiter 0x1e0 0x160 hm1 hd1
  inext prog_86
  xpmemiter 0x200 0x180 hm2 hd2
  have hbr := ric_branch run; clear run
  rcases hbr with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact (ric_undefined run).elim
  (have hd0 := ric_dest run; clear run; obtain ⟨_, run⟩ := hd0)
  istep; istep; istep; imstoreO 0x240
  xpmempush 0x200 prog_108
  xpmempush 0x1e0 prog_129
  xpmempush 0x1c0 prog_151
  (have hd0 := ric_dest run; clear run; obtain ⟨_, run⟩ := hd0)
  istep; imload 0x240; istep; istep; istep; istep
  have hbr := ric_branch run; clear run
  rcases hbr with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact (ric_undefined run).elim
  istep
  (have hj := ric_jump (List.not_mem_nil) prog_173 run; clear run; obtain ⟨_, run⟩ := hj)
  (have hd0 := ric_dest run; clear run; obtain ⟨_, run⟩ := hd0)
  imload 0x1a0
  obtain ⟨G', hr⟩ := ric_ret run
  cases hr
  refine ⟨_, rfl, _, _, _, _, G', rfl, ?_, hT.keeps, hT.wf⟩
  have c0 := xp_coin (k := 0) hm0 hd0 (by decide) (by decide)
  have c1 := xp_coin (k := 1) hm1 hd1 (by decide) (by decide)
  have c2 := xp_coin (k := 2) hm2 hd2 (by decide) (by decide)
  have e0 : (⟨a0.toNat, a1.toNat, a2.toNat⟩ : V3).get 0 = a0.toNat := rfl
  have e1 : (⟨a0.toNat, a1.toNat, a2.toNat⟩ : V3).get 1 = a1.toNat := rfl
  have e2 : (⟨a0.toNat, a1.toNat, a2.toNat⟩ : V3).get 2 = a2.toNat := rfl
  simp only [xpChk, V3.ofFnM, e0, e1, e2, c0, c1, c2, Option.bind_eq_bind, Option.bind_some]

/-! ## Kernel facts over the entry closures -/

theorem xp_silentSet : SilentSet prog [31, 56, 83, 105, 126, 148, 170] = true := by decide +kernel
theorem xp_execFreeSet : ExecFreeSet prog [31, 56, 83, 105, 126, 148, 170] = true := by
  decide +kernel
theorem xp_neverHalts : calleeNeverHalts prog 31 64 = true := by decide +kernel
theorem xpMem_silentSet : SilentSet prog [34, 59, 86, 108, 129, 151, 173] = true := by
  decide +kernel
theorem xpMem_execFreeSet : ExecFreeSet prog [34, 59, 86, 108, 129, 151, 173] = true := by
  decide +kernel
theorem xpMem_neverHalts : calleeNeverHalts prog 34 64 = true := by decide +kernel

end Blanc.Lift.Curve3Pool
