import Blanc.Lift.Curve3Pool.Walk.RliLiveD1
import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceFeeLoop

/-!
# `remove_liquidity_imbalance`, forward: the fee loop

The loop of lines 545–554 over the counter at `0x600`. The certificate's trees for it depend on
the path: iteration 0 runs at `t_336e_c1039` and continues at `t_336e_c1048` (`ideal ≤ new`) or
`t_336e_c1055` (`ideal > new`); iteration 1 runs at either; iteration 2 runs at `t_336e_c1055`
and leaves through `t_359f_c1055` or `t_359f_c1063`, which are the same tree (`rliExit`). Each
`rx_rli_fee*` runs one iteration from `RliFeeIter`: `fees[k]` at `0x5a0 + 32 k`, the stored
balance `balances[k]`, `new_balances[k] -= fees[k]` at `0x2e0 + 32 k`, the counter bumped.

The four trees are one parametric tree (`rliFH_336e`, below) at the contexts' guard arms, jump
and back edge, so the iteration is walked once, at any counter `k < 3` and either starting
memory size (`rx_rli_feeG`), and each `rx_rli_fee*E` is its instance.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

theorem rli_prog_1047 : cert.prog[1047]? = some t_3458_c1047 := by decide +kernel

theorem rli_prog_1048 : cert.prog[1048]? = some t_336e_c1048 := by decide +kernel

theorem rli_prog_1055 : cert.prog[1055]? = some t_336e_c1055 := by decide +kernel

theorem rli_prog_1063 : cert.prog[1063]? = some t_3458_c1063 := by decide +kernel

/-- The fee loop's exit. -/
abbrev rliExit : SFunc := t_359f_c1055

/-- A fee iteration's charge but the balance store: `c` before the store (`868` for iteration
0, `861` later), `10` more when `ideal > new`, and `192` after it. -/
def rliFeeCost (c : Nat) (D0 D1 B N : B256) : Nat :=
  (if N < D1 * B / D0 then c + 10 else c) + 192

/-- A fee iteration's literal memory: `ideal` at `0x620`, the difference cleared then set at
`0x640`, `fees[i]` at `0x5a0 + 32 i`, the key word at `0xc0`, the new balance less the fee at
`0x2e0 + 32 i`, the counter at `0x600`. -/
def rliFeeMem (M : Mem) (i : Nat) (D0 D1 B N f af : B256) : Mem :=
  ((((((M.write 0x620 (D1 * B / D0).toBytes).write 0x640 (Bytes.toB256 [0]).toBytes).write 0x640
    (if N < D1 * B / D0 then D1 * B / D0 - N else N - D1 * B / D0).toBytes).write (0x5a0 + 32 * i)
    f.toBytes).write 0xc0 (Bytes.toB256 [1]).toBytes).write (0x2e0 + 32 * i) af.toBytes).write 0x600
    (Nat.toB256 (i + 1)).toBytes

/-! ### The loop's trees in any context

The certificate's trees for one fee iteration differ between contexts only in the
checked-arithmetic guards' other arm `rv` (`.undefined` where the context never reaches it, the
revert `rliRv` where it does), the jump `jm` into the `ideal > new` tail and the back edge `tl`.
`rliFH_336e rv jm tl` is the head at `0x336e`; the tail at `0x3458` is `rliFH_3458 rliRv tl`. The
subtrees below are the certificate's, with those three as parameters. -/

/-- A guard's revert arm. -/
abbrev rliRv : SFunc := .next (.push [0x00] (by decide)) (.next (.reg (.dup 0)) (.last .revert))

def rliFH_358f (tl : SFunc) : SFunc :=
  (.dest (.next (.reg (.dup 1)) (.next (.reg .mload) (.next (.push [0x01] (by decide)) (.next (.reg
    .add) (.next (.reg (.dup 0)) (.next (.reg (.dup 3)) (.next (.reg .mstore) (.next (.reg (.dup
    1)) (.next (.reg .eq) (.next (.reg .iszero) (.next (.push [0x33, 0x6e] (by decide))
    tl))))))))))))

def rliFH_3584 (tl : SFunc) : SFunc :=
  (.dest (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .sub) (.next (.reg (.swap 0))
    (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.dup 1)) (.next
    (.reg .mstore) (.next (.reg .pop) (rliFH_358f tl))))))))))))

def rliFH_3572 (tl : SFunc) : SFunc :=
  (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg
    .mload) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .lt) (.next (.reg .iszero)
    (.next (.push [0x35, 0x84] (by decide)) (.branch t_3580_c1048 (rliFH_3584 tl))))))))))))

def rliFH_3558 (rv : SFunc) (tl : SFunc) : SFunc :=
  (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg (.dup
    0)) (.next (.reg .mload) (.next (.push [0x05, 0xa0] (by decide)) (.next (.push [0x06, 0x00] (by
    decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next
    (.reg .lt) (.next (.push [0x35, 0x72] (by decide)) (.branch rv (rliFH_3572 tl)))))))))))))))

def rliFH_3538 (rv : SFunc) (tl : SFunc) : SFunc :=
  (.dest (.next (.push [0x01] (by decide)) (.next (.push [0xc0] (by decide)) (.next (.reg .mstore)
    (.next (.push [0x20] (by decide)) (.next (.push [0xc0] (by decide)) (.next (.reg .keccak256)
    (.next (.reg .add) (.next (.reg .sstore) (.next (.push [0x02, 0xe0] (by decide)) (.next (.push
    [0x06, 0x00] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg
    (.dup 1)) (.next (.reg .lt) (.next (.push [0x35, 0x58] (by decide)) (.branch rv (rliFH_3558 rv
    tl))))))))))))))))))

def rliFH_3520 (rv : SFunc) (tl : SFunc) : SFunc :=
  (.dest (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .sub) (.next (.reg (.swap 0))
    (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x06, 0x00] (by
    decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next
    (.reg .lt) (.next (.push [0x35, 0x38] (by decide)) (.branch rv (rliFH_3538 rv
    tl))))))))))))))))

def rliFH_350d (rv : SFunc) (tl : SFunc) : SFunc :=
  (.dest (.next (.reg (.dup 2)) (.next (.reg .div) (.next (.reg (.swap 0)) (.next (.reg .pop)
    (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next
    (.reg .lt) (.next (.reg .iszero) (.next (.push [0x35, 0x20] (by decide)) (.branch t_351c_c1048
    (rliFH_3520 rv tl))))))))))))))

def rliFH_34f5 (rv : SFunc) (tl : SFunc) : SFunc :=
  (.dest (.next (.reg (.dup 0)) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0))
    (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x02, 0x54, 0x0b,
    0xe4, 0x00] (by decide)) (.next (.reg (.dup 0)) (.next (.reg (.dup 0)) (.next (.push [0x35,
    0x0d] (by decide)) (.branch .undefined (rliFH_350d rv tl))))))))))))))

def rliFH_34d8 (rv : SFunc) (tl : SFunc) : SFunc :=
  (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg
    .mload) (.next (.push [0x02, 0x00] (by decide)) (.next (.reg .mload) (.next (.reg (.dup 0))
    (.next (.reg (.dup 2)) (.next (.reg .mul) (.next (.reg (.dup 2)) (.next (.reg .iszero) (.next
    (.reg (.dup 2)) (.next (.reg (.dup 4)) (.next (.reg (.dup 3)) (.next (.reg .div) (.next (.reg
    .eq) (.next (.reg .or) (.next (.push [0x34, 0xf5] (by decide)) (.branch t_34f1_c1048
    (rliFH_34f5 rv tl)))))))))))))))))))))

def rliFH_34bf (rv : SFunc) (tl : SFunc) : SFunc :=
  (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg
    .mload) (.next (.push [0x05, 0xa0] (by decide)) (.next (.push [0x06, 0x00] (by decide)) (.next
    (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next
    (.push [0x34, 0xd8] (by decide)) (.branch rv (rliFH_34d8 rv tl))))))))))))))

def rliFH_34a6 (rv : SFunc) (tl : SFunc) : SFunc :=
  (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg
    .mstore) (.next (.push [0x02, 0xe0] (by decide)) (.next (.push [0x06, 0x00] (by decide)) (.next
    (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next
    (.push [0x34, 0xbf] (by decide)) (.branch rv (rliFH_34bf rv tl))))))))))))))

def rliFH_348c (rv : SFunc) (tl : SFunc) : SFunc :=
  (.dest (.next (.reg (.dup 2)) (.next (.reg .div) (.next (.reg (.swap 0)) (.next (.reg .pop)
    (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x05, 0xa0] (by decide)) (.next
    (.push [0x06, 0x00] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next
    (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x34, 0xa6] (by decide)) (.branch rv
    (rliFH_34a6 rv tl))))))))))))))))

def rliFH_3474 (rv : SFunc) (tl : SFunc) : SFunc :=
  (.dest (.next (.reg (.dup 0)) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0))
    (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x02, 0x54, 0x0b,
    0xe4, 0x00] (by decide)) (.next (.reg (.dup 0)) (.next (.reg (.dup 0)) (.next (.push [0x34,
    0x8c] (by decide)) (.branch .undefined (rliFH_348c rv tl))))))))))))))

def rliFH_3458 (rv : SFunc) (tl : SFunc) : SFunc :=
  (.dest (.next (.push [0x01, 0xe0] (by decide)) (.next (.reg .mload) (.next (.push [0x06, 0x40]
    (by decide)) (.next (.reg .mload) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg
    .mul) (.next (.reg (.dup 2)) (.next (.reg .iszero) (.next (.reg (.dup 2)) (.next (.reg (.dup
    4)) (.next (.reg (.dup 3)) (.next (.reg .div) (.next (.reg .eq) (.next (.reg .or) (.next (.push
    [0x34, 0x74] (by decide)) (.branch t_3470_c1048 (rliFH_3474 rv tl)))))))))))))))))))

def rliFH_344c (rv : SFunc) (tl : SFunc) : SFunc :=
  (.dest (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .sub) (.next (.reg (.swap 0))
    (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x06, 0x40] (by
    decide)) (.next (.reg .mstore) (rliFH_3458 rv tl)))))))))))

def rliFH_3436 (rv : SFunc) (tl : SFunc) : SFunc :=
  (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg
    .mload) (.next (.push [0x06, 0x20] (by decide)) (.next (.reg .mload) (.next (.reg (.dup 0))
    (.next (.reg (.dup 2)) (.next (.reg .lt) (.next (.reg .iszero) (.next (.push [0x34, 0x4c] (by
    decide)) (.branch t_3448_c1048 (rliFH_344c rv tl))))))))))))))

def rliFH_3422 (rv : SFunc) (tl : SFunc) : SFunc :=
  (.dest (.next (.push [0x02, 0xe0] (by decide)) (.next (.push [0x06, 0x00] (by decide)) (.next
    (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next
    (.push [0x34, 0x36] (by decide)) (.branch rv (rliFH_3436 rv tl))))))))))

def rliFH_3412 (jm : Nat) : SFunc :=
  (.dest (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .sub) (.next (.reg (.swap 0))
    (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x06, 0x40] (by
    decide)) (.next (.reg .mstore) (.next (.push [0x34, 0x58] (by decide)) (.jump jm))))))))))))

def rliFH_3400 (jm : Nat) : SFunc :=
  (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg
    .mload) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .lt) (.next (.reg .iszero)
    (.next (.push [0x34, 0x12] (by decide)) (.branch t_340e_c1048 (rliFH_3412 jm))))))))))))

def rliFH_33e9 (rv : SFunc) (jm : Nat) : SFunc :=
  (.next (.push [0x06, 0x20] (by decide)) (.next (.reg .mload) (.next (.push [0x02, 0xe0] (by
    decide)) (.next (.push [0x06, 0x00] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by
    decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x34, 0x00] (by decide))
    (.branch rv (rliFH_3400 jm)))))))))))

def rliFH_33d9 (rv : SFunc) (jm : Nat) (tl : SFunc) : SFunc :=
  (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg
    .mload) (.next (.push [0x06, 0x20] (by decide)) (.next (.reg .mload) (.next (.reg .gt) (.next
    (.reg .iszero) (.next (.push [0x34, 0x22] (by decide)) (.branch (rliFH_33e9 rv jm) (rliFH_3422
    rv tl))))))))))))

def rliFH_33b5 (rv : SFunc) (jm : Nat) (tl : SFunc) : SFunc :=
  (.dest (.next (.reg (.dup 2)) (.next (.reg .div) (.next (.reg (.swap 0)) (.next (.reg .pop)
    (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x06, 0x20] (by decide)) (.next (.reg
    .mstore) (.next (.push [0x00] (by decide)) (.next (.push [0x06, 0x40] (by decide)) (.next (.reg
    .mstore) (.next (.push [0x02, 0xe0] (by decide)) (.next (.push [0x06, 0x00] (by decide)) (.next
    (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next
    (.push [0x33, 0xd9] (by decide)) (.branch rv (rliFH_33d9 rv jm tl)))))))))))))))))))))

def rliFH_339f (rv : SFunc) (jm : Nat) (tl : SFunc) : SFunc :=
  (.dest (.next (.reg (.dup 0)) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0))
    (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x03, 0x40] (by
    decide)) (.next (.reg .mload) (.next (.reg (.dup 0)) (.next (.reg (.dup 0)) (.next (.push
    [0x33, 0xb5] (by decide)) (.branch t_33b1_c1048 (rliFH_33b5 rv jm tl)))))))))))))))

def rliFH_3386 (rv : SFunc) (jm : Nat) (tl : SFunc) : SFunc :=
  (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg
    .mload) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .mul) (.next (.reg (.dup 2))
    (.next (.reg .iszero) (.next (.reg (.dup 2)) (.next (.reg (.dup 4)) (.next (.reg (.dup 3))
    (.next (.reg .div) (.next (.reg .eq) (.next (.reg .or) (.next (.push [0x33, 0x9f] (by decide))
    (.branch t_339b_c1048 (rliFH_339f rv jm tl)))))))))))))))))))

def rliFH_336e (rv : SFunc) (jm : Nat) (tl : SFunc) : SFunc :=
  (.dest (.next (.push [0x04, 0x80] (by decide)) (.next (.reg .mload) (.next (.push [0x02, 0x80]
    (by decide)) (.next (.push [0x06, 0x00] (by decide)) (.next (.reg .mload) (.next (.push [0x03]
    (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x33, 0x86] (by decide))
    (.branch rv (rliFH_3386 rv jm tl))))))))))))

theorem rli_hd39 : t_336e_c1039 = rliFH_336e .undefined 1047 (.branchTo .undefined 1048) := rfl
theorem rli_hd48 : t_336e_c1048 = rliFH_336e .undefined 1047 (.branchTo .undefined 1055) := rfl
theorem rli_hd55 : t_336e_c1055 = rliFH_336e rliRv 1063 (.branchTo t_359f_c1055 1055) := rfl
theorem rli_md47 : t_3458_c1047 = rliFH_3458 rliRv (.branchTo t_359f_c1047 1055) := rfl
theorem rli_md63 : t_3458_c1063 = rliFH_3458 rliRv (.branchTo t_359f_c1063 1055) := rfl


/-- The memory size a fee iteration starts at and its charge before the balance store: `0x620`
and `868` on iteration 0 (the first two stores grow the memory), `0x660` and `861` later. -/
def RliFeeSz (s c : Nat) : Prop := (s = 0x620 ∧ c = 868) ∨ (s = 0x660 ∧ c = 861)

theorem rliFeeSz_facts {s c : Nat} (h : RliFeeSz s c) : ∃ m1 m2 : Nat,
    gVerylow + (calculateMemoryGasCost (memExtSize s 0x620 32) - calculateMemoryGasCost s) = m1 ∧
    gVerylow + (calculateMemoryGasCost (memExtSize (memExtSize s 0x620 32) 0x640 32) -
      calculateMemoryGasCost (memExtSize s 0x620 32)) = m2 ∧
    memExtSize (memExtSize s 0x620 32) 0x640 32 = 0x660 ∧ s % 32 = 0 ∧
    memExtSize s 0x620 32 % 32 = 0 ∧ 0x620 ≤ s ∧ 855 + m1 + m2 = c ∧ m1 + m2 ≤ 13 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨_, _, rfl, rfl, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- A fee iteration's back-edge condition: the bumped counter is not the bound. -/
abbrev rliBack (k : Nat) : B256 :=
  B256.eqCheck (B256.eqCheck (Bytes.toB256 [3] + Bytes.toB256 [0]) (Bytes.toB256 [1] + Nat.toB256 k)) 0

set_option hygiene false in
/-- A computed offset `base + 32 k`. -/
macro "koff" : tactic => `(tactic| first
  | rfl
  | (refine cw_off ?_ (by omega); rw [hmulk]; exact congrArg (· + 32 * k) (by decide))
  | (refine cw_off ?_ (by omega); rw [hmulk, Nat.add_comm]; exact congrArg (· + 32 * k) (by decide)))

/-- What a fee iteration at counter `k` hands its continuation at `T`: the balance stored, the
memory grown to `0x660` with the frame words outside the iteration's writes kept, `new[k]` less
the fee, `fees[k]` and the bumped counter, the charge `rliFeeCost c0` plus the store's. -/
def RliFeeK (sevm : Sevm) (W : Devm → Prop) (σ : Stor) (b : Devm) (S : List B256) (M : Mem)
    (img : Bytes) (G R k c0 : Nat) (D0 D1 B N f st af : B256) (Q : Outcome → Prop) (T : SFunc) :
    Prop :=
  ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
    ExLive sevm W b' (σ.set (balancesBase + Nat.toB256 k) st) →
    Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 →
    (∀ o v, WordAt img o v → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x2e0 + 32 * k) ∨
      (0x300 + 32 * k ≤ o ∧ o + 32 ≤ 0x5a0 + 32 * k) ∨ (0x5c0 + 32 * k ≤ o ∧ o + 32 ≤ 0x600) →
      WordAt img' o v) →
    WordAt img' (0x2e0 + 32 * k) af → WordAt img' (0x5a0 + 32 * k) f →
    WordAt img' 0x600 (Nat.toB256 (k + 1)) → R ≤ g → g ≤ G →
    G = g + (rliFeeCost c0 D0 D1 B N + sstoreCost sevm b (balancesBase + Nat.toB256 k) st) →
    b' = afterSstore sevm b (balancesBase + Nat.toB256 k) st → M' = rliFeeMem M k D0 D1 B N f af →
    SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: S) M' g) T Q

/-- A back edge of a `remove_liquidity_imbalance` coin loop at counter `k`, over the bound
`3 + 0` and the stack `S`, jumping to `d`, from the tail `tl` to the continuation `T`. -/
def RliLoopB (sevm : Sevm) (S : List B256) (d : B256) (k : Nat) (Q : Outcome → Prop)
    (tl T : SFunc) : Prop :=
  ∀ (b' : Devm) (M' : Mem) (g : Nat), SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] +
    Bytes.toB256 [0]) :: S) M' g) T Q →
  SFunc.RunEx cert.prog sevm (St b' (d :: rliBack k :: (Bytes.toB256 [3] + Bytes.toB256 [0]) :: S)
    M' (g + 10)) tl Q

/-- One fee iteration with `ideal > new`, forward: through the tail at `0x3458`. -/
theorem rx_rli_feeGZ {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R : Nat} {Q : Outcome → Prop} {F AF D0 D1 B N f st af : B256}
    {k s0 c0 jm : Nat} {rv tlS tlZ gZ : SFunc} (hk3 : k < 3) (hs0 : RliFeeSz s0 c0)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = s0)
    (hc : WordAt img 0x600 (Nat.toB256 k)) (hD1 : WordAt img 0x480 D1)
    (hD0w : WordAt img 0x340 D0) (hB : WordAt img (0x280 + 32 * k) B)
    (hN : WordAt img (0x2e0 + 32 * k) N) (hF : WordAt img 0x1e0 F) (hAF : WordAt img 0x200 AF)
    (hit : RliFeeIter F AF D0 D1 B N f st af) (hlt : N < D1 * B / D0)
    (hG : 26000 + R ≤ G) (hroom : S.length + 20 < 1024)
    (kZ : RliFeeK sevm W σ b S M img G R k c0 D0 D1 B N f st af Q gZ)
    (hjm : cert.prog[jm]? = some (rliFH_3458 rliRv tlZ)) 
    (hZ : RliLoopB sevm (Bytes.toB256 [6, 0] :: S) (Bytes.toB256 [0x33, 0x6e]) k Q tlZ gZ) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: S) M G) (rliFH_336e rv jm tlS) Q := by
  obtain ⟨m1, m2, hmc1, hmc2, hsz2, hs32, hs1, hle, hc0, hm12⟩ := rliFeeSz_facts hs0
  have hk : (Nat.toB256 k).toNat < 3 := by rw [B256.toNat_toB256_of_lt (by omega)]; exact hk3
  have hk1 : Bytes.toB256 [1] + Nat.toB256 k = Nat.toB256 (k + 1) := by
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    all_goals decide
  have hmulk : (Bytes.toB256 [0x20] * Nat.toB256 k).toNat = 32 * k := by
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    all_goals decide
  obtain ⟨hm1, hD0, dif, hdif, hm2, rfl, hm3, hs3, rfl, hs4, rfl⟩ := hit
  rcases hdif with ⟨-, rfl⟩ | ⟨hge, -⟩
  swap
  · exact absurd hlt hge
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + m1 + m2 + 865 := ⟨G - (m1 + m2 + 865), by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x480) (v := D1) hR hsz rfl ⟨by omega, hs32⟩ (by wautoK hD1) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x600) (v := Nat.toB256 k) hR hsz rfl ⟨by omega, hs32⟩ (by wautoK hc) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hk) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x280 + 32 * k) (v := B) hR hsz (by koff) ⟨by omega, hs32⟩ (by wautoK hB) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_eq rfl (by hrs) ·)
  xr (rx_or rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (B256.mulGuard_of_nofm hm1) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x340) (v := D0) hR hsz rfl ⟨by omega, hs32⟩ (by wautoK hD0w) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ hD0 ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  rw [Nat.add_right_comm g1 m1 m2, Nat.add_right_comm (g1 + m2) m1]
  refine rxe_mstoreL (o := 0x620) (c := m1) hR hW hsz rfl ⟨hmc1, hs32⟩ ?_; clear hR hW hsz; rename' M => Mq1; intro M hMq1 hR hW hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  rw [Nat.add_right_comm g1 m2]
  refine rxe_mstoreL (o := 0x640) (c := m2) hR hW hsz rfl ⟨hmc2, hs1⟩ ?_; clear hR hW hsz; rename' M => Mq2; intro M hMq2 hR hW hsz; rw [hsz2] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x600) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hk) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x2e0 + 32 * k) (v := N) hR hsz (by koff) ⟨by omega, by decide⟩ (by wautoK hN) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x620) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_gt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_zero' (gtCheck_iszero_of_lt (B256.lt_iff_toNat_lt_toNat.mp hlt)) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x620) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x600) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hk) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x2e0 + 32 * k) (v := N) hR hsz (by koff) ⟨by omega, by decide⟩ (by wautoK hN) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard (fun h => absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.lt_asymm (B256.lt_iff_toNat_lt_toNat.mp hlt)))) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_sub (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x640) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq3; intro M hMq3 hR hW hsz; rw [show memExtSize 0x660 0x640 32 = 0x660 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_jump (g := rliFH_3458 rliRv tlZ) hjm ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x1e0) (v := F) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hF) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x640) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_eq rfl (by hrs) ·)
  xr (rx_or rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (B256.mulGuard_of_nofm hm2) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x600) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hk) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreL (o := 0x5a0 + 32 * k) (c := 3) hR hW hsz (by koff) (by kmc) ?_; clear hR hW hsz; rename' M => Mq4; intro M hMq4 hR hW hsz; rw [memExtSize_of_le (by decide) (by omega)] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x600) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hk) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x2e0 + 32 * k) (v := N) hR hsz (by koff) ⟨by omega, by decide⟩ (by wautoK hN) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x600) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hk) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mload (o := 0x5a0 + 32 * k) hR hsz (by koff) ⟨by omega, by decide⟩ (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x200) (v := AF) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hAF) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_eq rfl (by hrs) ·)
  xr (rx_or rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (B256.mulGuard_of_nofm hm3) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hs3) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_sub (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x600) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hk) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq5; intro M hMq5 hR hW hsz; rw [show memExtSize 0x660 0xc0 32 = 0x660 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hrs) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hrs) ·)
  refine rxe_sstoreVX hfork hstatic (by omega) ?_; intro g2 b2 hb2 hg21 hg22 g2x; replace hL := hL.sstoreE hb2
  obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 192 := ⟨g2 - 192, by omega⟩
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x600) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hk) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x2e0 + 32 * k) (v := N) hR hsz (by koff) ⟨by omega, by decide⟩ (by wautoK hN) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x600) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hk) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mload (o := 0x5a0 + 32 * k) hR hsz (by koff) ⟨by omega, by decide⟩ (by hrs) ·); try wsimp
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hs4) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_sub (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x2e0 + 32 * k) (c := 3) hR hW hsz (by koff) (by kmc) ?_; clear hR hW hsz; rename' M => Mq6; intro M hMq6 hR hW hsz; rw [memExtSize_of_le (by decide) (by omega)] at hsz
  xr (rx_pop ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x600) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x600) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq7; intro M hMq7 hR hW hsz; rw [show memExtSize 0x660 0x600 32 = 0x660 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_eq rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine hZ _ _ _ ?_
  refine kZ _ M _ _ hL hR hW hsz (fun o v h ho => by wautoK h) (by wautoK0) (by wautoK0) (by wautoK0)
    (by omega) (by omega) (by unfold rliFeeCost rliDen; rw [ite_eq_left hlt]; omega) hb2 ?_
  rw [hMq7, hMq6, hMq5, hMq4, hMq3, hMq2, hMq1]
  unfold rliFeeMem; rw [ite_eq_left hlt, hk1]

/-- One fee iteration with `ideal ≤ new`, forward: on in the head tree. -/
theorem rx_rli_feeGS {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R : Nat} {Q : Outcome → Prop} {F AF D0 D1 B N f st af : B256}
    {k s0 c0 jm : Nat} {rv tlS gS : SFunc} (hk3 : k < 3) (hs0 : RliFeeSz s0 c0)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = s0)
    (hc : WordAt img 0x600 (Nat.toB256 k)) (hD1 : WordAt img 0x480 D1)
    (hD0w : WordAt img 0x340 D0) (hB : WordAt img (0x280 + 32 * k) B)
    (hN : WordAt img (0x2e0 + 32 * k) N) (hF : WordAt img 0x1e0 F) (hAF : WordAt img 0x200 AF)
    (hit : RliFeeIter F AF D0 D1 B N f st af) (hge : ¬ N < D1 * B / D0)
    (hG : 26000 + R ≤ G) (hroom : S.length + 20 < 1024)
    (kS : RliFeeK sevm W σ b S M img G R k c0 D0 D1 B N f st af Q gS)
    (hS : RliLoopB sevm (Bytes.toB256 [6, 0] :: S) (Bytes.toB256 [0x33, 0x6e]) k Q tlS gS) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: S) M G) (rliFH_336e rv jm tlS) Q := by
  obtain ⟨m1, m2, hmc1, hmc2, hsz2, hs32, hs1, hle, hc0, hm12⟩ := rliFeeSz_facts hs0
  have hk : (Nat.toB256 k).toNat < 3 := by rw [B256.toNat_toB256_of_lt (by omega)]; exact hk3
  have hk1 : Bytes.toB256 [1] + Nat.toB256 k = Nat.toB256 (k + 1) := by
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    all_goals decide
  have hmulk : (Bytes.toB256 [0x20] * Nat.toB256 k).toNat = 32 * k := by
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    all_goals decide
  obtain ⟨hm1, hD0, dif, hdif, hm2, rfl, hm3, hs3, rfl, hs4, rfl⟩ := hit
  rcases hdif with ⟨hlt, -⟩ | ⟨-, rfl⟩
  · exact absurd hlt hge
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + m1 + m2 + 855 := ⟨G - (m1 + m2 + 855), by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x480) (v := D1) hR hsz rfl ⟨by omega, hs32⟩ (by wautoK hD1) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x600) (v := Nat.toB256 k) hR hsz rfl ⟨by omega, hs32⟩ (by wautoK hc) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hk) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x280 + 32 * k) (v := B) hR hsz (by koff) ⟨by omega, hs32⟩ (by wautoK hB) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_eq rfl (by hrs) ·)
  xr (rx_or rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (B256.mulGuard_of_nofm hm1) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x340) (v := D0) hR hsz rfl ⟨by omega, hs32⟩ (by wautoK hD0w) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ hD0 ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  rw [Nat.add_right_comm g1 m1 m2, Nat.add_right_comm (g1 + m2) m1]
  refine rxe_mstoreL (o := 0x620) (c := m1) hR hW hsz rfl ⟨hmc1, hs32⟩ ?_; clear hR hW hsz; rename' M => Mq1; intro M hMq1 hR hW hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  rw [Nat.add_right_comm g1 m2]
  refine rxe_mstoreL (o := 0x640) (c := m2) hR hW hsz rfl ⟨hmc2, hs1⟩ ?_; clear hR hW hsz; rename' M => Mq2; intro M hMq2 hR hW hsz; rw [hsz2] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x600) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hk) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x2e0 + 32 * k) (v := N) hR hsz (by koff) ⟨by omega, by decide⟩ (by wautoK hN) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x620) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_gt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (gtCheck_iszero_of_not_lt (fun h => hge (B256.lt_iff_toNat_lt_toNat.mpr h))) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x600) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hk) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x2e0 + 32 * k) (v := N) hR hsz (by koff) ⟨by omega, by decide⟩ (by wautoK hN) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x620) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hge) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_sub (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x640) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq3; intro M hMq3 hR hW hsz; rw [show memExtSize 0x660 0x640 32 = 0x660 by decide] at hsz
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x1e0) (v := F) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hF) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x640) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_eq rfl (by hrs) ·)
  xr (rx_or rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (B256.mulGuard_of_nofm hm2) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x600) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hk) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreL (o := 0x5a0 + 32 * k) (c := 3) hR hW hsz (by koff) (by kmc) ?_; clear hR hW hsz; rename' M => Mq4; intro M hMq4 hR hW hsz; rw [memExtSize_of_le (by decide) (by omega)] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x600) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hk) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x2e0 + 32 * k) (v := N) hR hsz (by koff) ⟨by omega, by decide⟩ (by wautoK hN) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x600) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hk) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mload (o := 0x5a0 + 32 * k) hR hsz (by koff) ⟨by omega, by decide⟩ (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x200) (v := AF) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hAF) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_eq rfl (by hrs) ·)
  xr (rx_or rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (B256.mulGuard_of_nofm hm3) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hs3) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_sub (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x600) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hk) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq5; intro M hMq5 hR hW hsz; rw [show memExtSize 0x660 0xc0 32 = 0x660 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hrs) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hrs) ·)
  refine rxe_sstoreVX hfork hstatic (by omega) ?_; intro g2 b2 hb2 hg21 hg22 g2x; replace hL := hL.sstoreE hb2
  obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 192 := ⟨g2 - 192, by omega⟩
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x600) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hk) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x2e0 + 32 * k) (v := N) hR hsz (by koff) ⟨by omega, by decide⟩ (by wautoK hN) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x600) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hk) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mload (o := 0x5a0 + 32 * k) hR hsz (by koff) ⟨by omega, by decide⟩ (by hrs) ·); try wsimp
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hs4) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_sub (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x2e0 + 32 * k) (c := 3) hR hW hsz (by koff) (by kmc) ?_; clear hR hW hsz; rename' M => Mq6; intro M hMq6 hR hW hsz; rw [memExtSize_of_le (by decide) (by omega)] at hsz
  xr (rx_pop ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x600) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoK hc) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x600) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq7; intro M hMq7 hR hW hsz; rw [show memExtSize 0x660 0x600 32 = 0x660 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_eq rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine hS _ _ _ ?_
  refine kS _ M _ _ hL hR hW hsz (fun o v h ho => by wautoK h) (by wautoK0) (by wautoK0) (by wautoK0)
    (by omega) (by omega) (by unfold rliFeeCost rliDen; rw [ite_eq_right hge]; omega) hb2 ?_
  rw [hMq7, hMq6, hMq5, hMq4, hMq3, hMq2, hMq1]
  unfold rliFeeMem; rw [ite_eq_right hge, hk1]

/-- **One fee iteration, forward, at any counter `k < 3`**, from the head tree in any context:
on to `gS` when `ideal ≤ new`, through the tail into `gZ` otherwise. -/
theorem rx_rli_feeG {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R : Nat} {Q : Outcome → Prop} {F AF D0 D1 B N f st af : B256}
    {k s0 c0 jm : Nat} {rv tlS tlZ gS gZ : SFunc} (hk3 : k < 3) (hs0 : RliFeeSz s0 c0)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = s0)
    (hc : WordAt img 0x600 (Nat.toB256 k)) (hD1 : WordAt img 0x480 D1)
    (hD0w : WordAt img 0x340 D0) (hB : WordAt img (0x280 + 32 * k) B)
    (hN : WordAt img (0x2e0 + 32 * k) N) (hF : WordAt img 0x1e0 F) (hAF : WordAt img 0x200 AF)
    (hit : RliFeeIter F AF D0 D1 B N f st af)
    (hG : 26000 + R ≤ G) (hroom : S.length + 20 < 1024)
    (kS : RliFeeK sevm W σ b S M img G R k c0 D0 D1 B N f st af Q gS)
    (kZ : RliFeeK sevm W σ b S M img G R k c0 D0 D1 B N f st af Q gZ)
    (hjm : cert.prog[jm]? = some (rliFH_3458 rliRv tlZ))
    (hS : RliLoopB sevm (Bytes.toB256 [6, 0] :: S) (Bytes.toB256 [0x33, 0x6e]) k Q tlS gS)
    
    (hZ : RliLoopB sevm (Bytes.toB256 [6, 0] :: S) (Bytes.toB256 [0x33, 0x6e]) k Q tlZ gZ) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: S) M G) (rliFH_336e rv jm tlS) Q := by
  by_cases hlt : N < D1 * B / D0
  · exact rx_rli_feeGZ hk3 hs0 hfork hstatic hL hR hW hsz hc hD1 hD0w hB hN hF hAF hit hlt hG hroom
      kZ hjm hZ
  · exact rx_rli_feeGS hk3 hs0 hfork hstatic hL hR hW hsz hc hD1 hD0w hB hN hF hAF hit hlt hG hroom
      kS hS

/-- A coin loop's back edge taken: the counter short of its bound, on to the next iteration's
entry. -/
theorem rli_backS {sevm : Sevm} {S : List B256} {d : B256} {Q : Outcome → Prop} {x g : SFunc}
    {j k : Nat}
    (hj : cert.prog[j]? = some g) (hk : rliBack k ≠ 0) : RliLoopB sevm S d k Q (.branchTo x j) g := by
  intro b' M' G h
  xr (rx_branchTo_succ hk hj ·)
  exact h

/-- A coin loop's back edge not taken: the counter at its bound, out of the loop. -/
theorem rli_backX {sevm : Sevm} {S : List B256} {d : B256} {Q : Outcome → Prop} {x : SFunc}
    {j k : Nat}
    (hk : rliBack k = 0) : RliLoopB sevm S d k Q (.branchTo x j) x := by
  intro b' M' G h
  xr (rx_branchTo_zero' hk ·)
  exact h

theorem rli_mid47 : cert.prog[1047]? = some (rliFH_3458 rliRv (.branchTo t_359f_c1047 1055)) :=
  rli_prog_1047.trans (congrArg some rli_md47)

theorem rli_mid63 : cert.prog[1063]? = some (rliFH_3458 rliRv (.branchTo t_359f_c1063 1055)) :=
  rli_prog_1063.trans (congrArg some rli_md63)

/-- Fee iteration 0 at `t_336e_c1039`, forward. -/
theorem rx_rli_fee0E {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R : Nat} {Q : Outcome → Prop} {F AF D0 D1 B N f st af : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x620)
    (hc : WordAt img 0x600 (Nat.toB256 0)) (hD1 : WordAt img 0x480 D1)
    (hD0w : WordAt img 0x340 D0) (hB : WordAt img (0x280 + 32 * 0) B)
    (hN : WordAt img (0x2e0 + 32 * 0) N) (hF : WordAt img 0x1e0 F) (hAF : WordAt img 0x200 AF)
    (hit : RliFeeIter F AF D0 D1 B N f st af)
    (hG : 26000 + R ≤ G) (hroom : S.length + 20 < 1024)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' (σ.set (balancesBase + Nat.toB256 0) st) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x2e0 + 32 * 0) ∨
        (0x300 + 32 * 0 ≤ o ∧ o + 32 ≤ 0x5a0 + 32 * 0) ∨ (0x5c0 + 32 * 0 ≤ o ∧ o + 32 ≤ 0x600) →
        WordAt img' o v) →
      WordAt img' (0x2e0 + 32 * 0) af → WordAt img' (0x5a0 + 32 * 0) f →
      WordAt img' 0x600 (Nat.toB256 1) → R ≤ g → g ≤ G →
      G = g + (rliFeeCost 868 D0 D1 B N + sstoreCost sevm b (balancesBase + Nat.toB256 0) st) →
      b' = afterSstore sevm b (balancesBase + Nat.toB256 0) st → M' = rliFeeMem M 0 D0 D1 B N f af →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' g) t_336e_c1048 Q)
    (kZ : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' (σ.set (balancesBase + Nat.toB256 0) st) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x2e0 + 32 * 0) ∨
        (0x300 + 32 * 0 ≤ o ∧ o + 32 ≤ 0x5a0 + 32 * 0) ∨ (0x5c0 + 32 * 0 ≤ o ∧ o + 32 ≤ 0x600) →
        WordAt img' o v) →
      WordAt img' (0x2e0 + 32 * 0) af → WordAt img' (0x5a0 + 32 * 0) f →
      WordAt img' 0x600 (Nat.toB256 1) → R ≤ g → g ≤ G →
      G = g + (rliFeeCost 868 D0 D1 B N + sstoreCost sevm b (balancesBase + Nat.toB256 0) st) →
      b' = afterSstore sevm b (balancesBase + Nat.toB256 0) st → M' = rliFeeMem M 0 D0 D1 B N f af →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' g) t_336e_c1055 Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: S) M G) t_336e_c1039 Q := by
  rw [rli_hd39]
  exact rx_rli_feeG (by decide) (.inl ⟨rfl, rfl⟩) hfork hstatic hL hR hW hsz hc hD1 hD0w hB hN hF hAF hit hG hroom kS kZ
    rli_mid47 (rli_backS rli_prog_1048 (by decide)) (rli_backS rli_prog_1055 (by decide))

/-- Fee iteration 1 at `t_336e_c1048`, forward. -/
theorem rx_rli_fee1aE {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R : Nat} {Q : Outcome → Prop} {F AF D0 D1 B N f st af : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x660)
    (hc : WordAt img 0x600 (Nat.toB256 1)) (hD1 : WordAt img 0x480 D1)
    (hD0w : WordAt img 0x340 D0) (hB : WordAt img (0x280 + 32 * 1) B)
    (hN : WordAt img (0x2e0 + 32 * 1) N) (hF : WordAt img 0x1e0 F) (hAF : WordAt img 0x200 AF)
    (hit : RliFeeIter F AF D0 D1 B N f st af)
    (hG : 26000 + R ≤ G) (hroom : S.length + 20 < 1024)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' (σ.set (balancesBase + Nat.toB256 1) st) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x2e0 + 32 * 1) ∨
        (0x300 + 32 * 1 ≤ o ∧ o + 32 ≤ 0x5a0 + 32 * 1) ∨ (0x5c0 + 32 * 1 ≤ o ∧ o + 32 ≤ 0x600) →
        WordAt img' o v) →
      WordAt img' (0x2e0 + 32 * 1) af → WordAt img' (0x5a0 + 32 * 1) f →
      WordAt img' 0x600 (Nat.toB256 2) → R ≤ g → g ≤ G →
      G = g + (rliFeeCost 861 D0 D1 B N + sstoreCost sevm b (balancesBase + Nat.toB256 1) st) →
      b' = afterSstore sevm b (balancesBase + Nat.toB256 1) st → M' = rliFeeMem M 1 D0 D1 B N f af →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' g) t_336e_c1055 Q)
    (kZ : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' (σ.set (balancesBase + Nat.toB256 1) st) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x2e0 + 32 * 1) ∨
        (0x300 + 32 * 1 ≤ o ∧ o + 32 ≤ 0x5a0 + 32 * 1) ∨ (0x5c0 + 32 * 1 ≤ o ∧ o + 32 ≤ 0x600) →
        WordAt img' o v) →
      WordAt img' (0x2e0 + 32 * 1) af → WordAt img' (0x5a0 + 32 * 1) f →
      WordAt img' 0x600 (Nat.toB256 2) → R ≤ g → g ≤ G →
      G = g + (rliFeeCost 861 D0 D1 B N + sstoreCost sevm b (balancesBase + Nat.toB256 1) st) →
      b' = afterSstore sevm b (balancesBase + Nat.toB256 1) st → M' = rliFeeMem M 1 D0 D1 B N f af →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' g) t_336e_c1055 Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: S) M G) t_336e_c1048 Q := by
  rw [rli_hd48]
  exact rx_rli_feeG (by decide) (.inr ⟨rfl, rfl⟩) hfork hstatic hL hR hW hsz hc hD1 hD0w hB hN hF hAF hit hG hroom kS kZ
    rli_mid47 (rli_backS rli_prog_1055 (by decide)) (rli_backS rli_prog_1055 (by decide))

/-- Fee iteration 1 at `t_336e_c1055`, forward. -/
theorem rx_rli_fee1bE {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R : Nat} {Q : Outcome → Prop} {F AF D0 D1 B N f st af : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x660)
    (hc : WordAt img 0x600 (Nat.toB256 1)) (hD1 : WordAt img 0x480 D1)
    (hD0w : WordAt img 0x340 D0) (hB : WordAt img (0x280 + 32 * 1) B)
    (hN : WordAt img (0x2e0 + 32 * 1) N) (hF : WordAt img 0x1e0 F) (hAF : WordAt img 0x200 AF)
    (hit : RliFeeIter F AF D0 D1 B N f st af)
    (hG : 26000 + R ≤ G) (hroom : S.length + 20 < 1024)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' (σ.set (balancesBase + Nat.toB256 1) st) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x2e0 + 32 * 1) ∨
        (0x300 + 32 * 1 ≤ o ∧ o + 32 ≤ 0x5a0 + 32 * 1) ∨ (0x5c0 + 32 * 1 ≤ o ∧ o + 32 ≤ 0x600) →
        WordAt img' o v) →
      WordAt img' (0x2e0 + 32 * 1) af → WordAt img' (0x5a0 + 32 * 1) f →
      WordAt img' 0x600 (Nat.toB256 2) → R ≤ g → g ≤ G →
      G = g + (rliFeeCost 861 D0 D1 B N + sstoreCost sevm b (balancesBase + Nat.toB256 1) st) →
      b' = afterSstore sevm b (balancesBase + Nat.toB256 1) st → M' = rliFeeMem M 1 D0 D1 B N f af →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' g) t_336e_c1055 Q)
    (kZ : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' (σ.set (balancesBase + Nat.toB256 1) st) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x2e0 + 32 * 1) ∨
        (0x300 + 32 * 1 ≤ o ∧ o + 32 ≤ 0x5a0 + 32 * 1) ∨ (0x5c0 + 32 * 1 ≤ o ∧ o + 32 ≤ 0x600) →
        WordAt img' o v) →
      WordAt img' (0x2e0 + 32 * 1) af → WordAt img' (0x5a0 + 32 * 1) f →
      WordAt img' 0x600 (Nat.toB256 2) → R ≤ g → g ≤ G →
      G = g + (rliFeeCost 861 D0 D1 B N + sstoreCost sevm b (balancesBase + Nat.toB256 1) st) →
      b' = afterSstore sevm b (balancesBase + Nat.toB256 1) st → M' = rliFeeMem M 1 D0 D1 B N f af →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' g) t_336e_c1055 Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: S) M G) t_336e_c1055 Q := by
  rw [rli_hd55]
  exact rx_rli_feeG (by decide) (.inr ⟨rfl, rfl⟩) hfork hstatic hL hR hW hsz hc hD1 hD0w hB hN hF hAF hit hG hroom kS kZ
    rli_mid63 (rli_backS rli_prog_1055 (by decide)) (rli_backS rli_prog_1055 (by decide))

/-- Fee iteration 2 at `t_336e_c1055`, forward. -/
theorem rx_rli_fee2E {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R : Nat} {Q : Outcome → Prop} {F AF D0 D1 B N f st af : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x660)
    (hc : WordAt img 0x600 (Nat.toB256 2)) (hD1 : WordAt img 0x480 D1)
    (hD0w : WordAt img 0x340 D0) (hB : WordAt img (0x280 + 32 * 2) B)
    (hN : WordAt img (0x2e0 + 32 * 2) N) (hF : WordAt img 0x1e0 F) (hAF : WordAt img 0x200 AF)
    (hit : RliFeeIter F AF D0 D1 B N f st af)
    (hG : 26000 + R ≤ G) (hroom : S.length + 20 < 1024)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' (σ.set (balancesBase + Nat.toB256 2) st) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x2e0 + 32 * 2) ∨
        (0x300 + 32 * 2 ≤ o ∧ o + 32 ≤ 0x5a0 + 32 * 2) ∨ (0x5c0 + 32 * 2 ≤ o ∧ o + 32 ≤ 0x600) →
        WordAt img' o v) →
      WordAt img' (0x2e0 + 32 * 2) af → WordAt img' (0x5a0 + 32 * 2) f →
      WordAt img' 0x600 (Nat.toB256 3) → R ≤ g → g ≤ G →
      G = g + (rliFeeCost 861 D0 D1 B N + sstoreCost sevm b (balancesBase + Nat.toB256 2) st) →
      b' = afterSstore sevm b (balancesBase + Nat.toB256 2) st → M' = rliFeeMem M 2 D0 D1 B N f af →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' g) rliExit Q)
    (kZ : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' (σ.set (balancesBase + Nat.toB256 2) st) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x2e0 + 32 * 2) ∨
        (0x300 + 32 * 2 ≤ o ∧ o + 32 ≤ 0x5a0 + 32 * 2) ∨ (0x5c0 + 32 * 2 ≤ o ∧ o + 32 ≤ 0x600) →
        WordAt img' o v) →
      WordAt img' (0x2e0 + 32 * 2) af → WordAt img' (0x5a0 + 32 * 2) f →
      WordAt img' 0x600 (Nat.toB256 3) → R ≤ g → g ≤ G →
      G = g + (rliFeeCost 861 D0 D1 B N + sstoreCost sevm b (balancesBase + Nat.toB256 2) st) →
      b' = afterSstore sevm b (balancesBase + Nat.toB256 2) st → M' = rliFeeMem M 2 D0 D1 B N f af →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' g) rliExit Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: S) M G) t_336e_c1055 Q := by
  rw [rli_hd55]
  exact rx_rli_feeG (by decide) (.inr ⟨rfl, rfl⟩) hfork hstatic hL hR hW hsz hc hD1 hD0w hB hN hF hAF hit hG hroom kS kZ
    rli_mid63 (rli_backX (by decide)) (rli_backX (by decide))

/-- Fee iteration 0 at `t_336e_c1039`, forward. -/
theorem rx_rli_fee0 {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R : Nat} {Q : Outcome → Prop} {F AF D0 D1 B N f st af : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x620)
    (hc : WordAt img 0x600 (Nat.toB256 0)) (hD1 : WordAt img 0x480 D1)
    (hD0w : WordAt img 0x340 D0) (hB : WordAt img (0x280 + 32 * 0) B)
    (hN : WordAt img (0x2e0 + 32 * 0) N) (hF : WordAt img 0x1e0 F) (hAF : WordAt img 0x200 AF)
    (hit : RliFeeIter F AF D0 D1 B N f st af)
    (hG : 26000 + R ≤ G) (hroom : S.length + 20 < 1024)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' (σ.set (balancesBase + Nat.toB256 0) st) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x2e0 + 32 * 0) ∨
        (0x300 + 32 * 0 ≤ o ∧ o + 32 ≤ 0x5a0 + 32 * 0) ∨ (0x5c0 + 32 * 0 ≤ o ∧ o + 32 ≤ 0x600) →
        WordAt img' o v) →
      WordAt img' (0x2e0 + 32 * 0) af → WordAt img' (0x5a0 + 32 * 0) f →
      WordAt img' 0x600 (Nat.toB256 1) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' g) t_336e_c1048 Q)
    (kZ : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' (σ.set (balancesBase + Nat.toB256 0) st) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x2e0 + 32 * 0) ∨
        (0x300 + 32 * 0 ≤ o ∧ o + 32 ≤ 0x5a0 + 32 * 0) ∨ (0x5c0 + 32 * 0 ≤ o ∧ o + 32 ≤ 0x600) →
        WordAt img' o v) →
      WordAt img' (0x2e0 + 32 * 0) af → WordAt img' (0x5a0 + 32 * 0) f →
      WordAt img' 0x600 (Nat.toB256 1) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' g) t_336e_c1055 Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: S) M G) t_336e_c1039 Q :=
  rx_rli_fee0E hfork hstatic hL hR hW hsz hc hD1 hD0w hB hN hF hAF hit hG hroom
    (fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 _ _ _ => kS b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 _ _ _ => kZ b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)

/-- Fee iteration 1 at `t_336e_c1048`, forward. -/
theorem rx_rli_fee1a {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R : Nat} {Q : Outcome → Prop} {F AF D0 D1 B N f st af : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x660)
    (hc : WordAt img 0x600 (Nat.toB256 1)) (hD1 : WordAt img 0x480 D1)
    (hD0w : WordAt img 0x340 D0) (hB : WordAt img (0x280 + 32 * 1) B)
    (hN : WordAt img (0x2e0 + 32 * 1) N) (hF : WordAt img 0x1e0 F) (hAF : WordAt img 0x200 AF)
    (hit : RliFeeIter F AF D0 D1 B N f st af)
    (hG : 26000 + R ≤ G) (hroom : S.length + 20 < 1024)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' (σ.set (balancesBase + Nat.toB256 1) st) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x2e0 + 32 * 1) ∨
        (0x300 + 32 * 1 ≤ o ∧ o + 32 ≤ 0x5a0 + 32 * 1) ∨ (0x5c0 + 32 * 1 ≤ o ∧ o + 32 ≤ 0x600) →
        WordAt img' o v) →
      WordAt img' (0x2e0 + 32 * 1) af → WordAt img' (0x5a0 + 32 * 1) f →
      WordAt img' 0x600 (Nat.toB256 2) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' g) t_336e_c1055 Q)
    (kZ : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' (σ.set (balancesBase + Nat.toB256 1) st) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x2e0 + 32 * 1) ∨
        (0x300 + 32 * 1 ≤ o ∧ o + 32 ≤ 0x5a0 + 32 * 1) ∨ (0x5c0 + 32 * 1 ≤ o ∧ o + 32 ≤ 0x600) →
        WordAt img' o v) →
      WordAt img' (0x2e0 + 32 * 1) af → WordAt img' (0x5a0 + 32 * 1) f →
      WordAt img' 0x600 (Nat.toB256 2) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' g) t_336e_c1055 Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: S) M G) t_336e_c1048 Q :=
  rx_rli_fee1aE hfork hstatic hL hR hW hsz hc hD1 hD0w hB hN hF hAF hit hG hroom
    (fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 _ _ _ => kS b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 _ _ _ => kZ b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)

/-- Fee iteration 1 at `t_336e_c1055`, forward. -/
theorem rx_rli_fee1b {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R : Nat} {Q : Outcome → Prop} {F AF D0 D1 B N f st af : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x660)
    (hc : WordAt img 0x600 (Nat.toB256 1)) (hD1 : WordAt img 0x480 D1)
    (hD0w : WordAt img 0x340 D0) (hB : WordAt img (0x280 + 32 * 1) B)
    (hN : WordAt img (0x2e0 + 32 * 1) N) (hF : WordAt img 0x1e0 F) (hAF : WordAt img 0x200 AF)
    (hit : RliFeeIter F AF D0 D1 B N f st af)
    (hG : 26000 + R ≤ G) (hroom : S.length + 20 < 1024)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' (σ.set (balancesBase + Nat.toB256 1) st) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x2e0 + 32 * 1) ∨
        (0x300 + 32 * 1 ≤ o ∧ o + 32 ≤ 0x5a0 + 32 * 1) ∨ (0x5c0 + 32 * 1 ≤ o ∧ o + 32 ≤ 0x600) →
        WordAt img' o v) →
      WordAt img' (0x2e0 + 32 * 1) af → WordAt img' (0x5a0 + 32 * 1) f →
      WordAt img' 0x600 (Nat.toB256 2) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' g) t_336e_c1055 Q)
    (kZ : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' (σ.set (balancesBase + Nat.toB256 1) st) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x2e0 + 32 * 1) ∨
        (0x300 + 32 * 1 ≤ o ∧ o + 32 ≤ 0x5a0 + 32 * 1) ∨ (0x5c0 + 32 * 1 ≤ o ∧ o + 32 ≤ 0x600) →
        WordAt img' o v) →
      WordAt img' (0x2e0 + 32 * 1) af → WordAt img' (0x5a0 + 32 * 1) f →
      WordAt img' 0x600 (Nat.toB256 2) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' g) t_336e_c1055 Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: S) M G) t_336e_c1055 Q :=
  rx_rli_fee1bE hfork hstatic hL hR hW hsz hc hD1 hD0w hB hN hF hAF hit hG hroom
    (fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 _ _ _ => kS b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 _ _ _ => kZ b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)

/-- Fee iteration 2 at `t_336e_c1055`, forward. -/
theorem rx_rli_fee2 {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R : Nat} {Q : Outcome → Prop} {F AF D0 D1 B N f st af : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x660)
    (hc : WordAt img 0x600 (Nat.toB256 2)) (hD1 : WordAt img 0x480 D1)
    (hD0w : WordAt img 0x340 D0) (hB : WordAt img (0x280 + 32 * 2) B)
    (hN : WordAt img (0x2e0 + 32 * 2) N) (hF : WordAt img 0x1e0 F) (hAF : WordAt img 0x200 AF)
    (hit : RliFeeIter F AF D0 D1 B N f st af)
    (hG : 26000 + R ≤ G) (hroom : S.length + 20 < 1024)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' (σ.set (balancesBase + Nat.toB256 2) st) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x2e0 + 32 * 2) ∨
        (0x300 + 32 * 2 ≤ o ∧ o + 32 ≤ 0x5a0 + 32 * 2) ∨ (0x5c0 + 32 * 2 ≤ o ∧ o + 32 ≤ 0x600) →
        WordAt img' o v) →
      WordAt img' (0x2e0 + 32 * 2) af → WordAt img' (0x5a0 + 32 * 2) f →
      WordAt img' 0x600 (Nat.toB256 3) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' g) rliExit Q)
    (kZ : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' (σ.set (balancesBase + Nat.toB256 2) st) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 →
      (∀ o v, WordAt img o v → o + 32 ≤ 0xc0 ∨ (0xe0 ≤ o ∧ o + 32 ≤ 0x2e0 + 32 * 2) ∨
        (0x300 + 32 * 2 ≤ o ∧ o + 32 ≤ 0x5a0 + 32 * 2) ∨ (0x5c0 + 32 * 2 ≤ o ∧ o + 32 ≤ 0x600) →
        WordAt img' o v) →
      WordAt img' (0x2e0 + 32 * 2) af → WordAt img' (0x5a0 + 32 * 2) f →
      WordAt img' 0x600 (Nat.toB256 3) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' g) rliExit Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: S) M G) t_336e_c1055 Q :=
  rx_rli_fee2E hfork hstatic hL hR hW hsz hc hD1 hD0w hB hN hF hAF hit hG hroom
    (fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 _ _ _ => kS b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 _ _ _ => kZ b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)

end Blanc.Lift.Curve3Pool
