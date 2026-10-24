import Blanc.Lift.Weth9.Creation.Cert
import Blanc.Lift.PackedSha
import Blanc.Lift.WalkSteps
import Blanc.Lift.Deploy
import Blanc.SystemCallForward
import Blanc.Lift.ExactLeaf
import Blanc.Lift.HistCreate

/-!
# The WETH9 constructor, walked

A gas-exact synthetic run (`SFunc.RunExact`) of the lifted constructor of WETH9's creation
input (`Creation/Cert.lean`, solc 0.4.19).  The constructor

* sets the free pointer and builds the memory strings `"Wrapped Ether"` (13 bytes) and `"WETH"`
  (4 bytes);
* stores each through solc's `bytes storage = bytes memory` helper (entry 2, pc `0xc8`): a string
  shorter than 32 bytes goes into the slot itself as `data | 2·len`; the helper hashes the slot
  for the (unused) long-form data area and runs the stale-data clearing loop (entries 4, 6, 7)
  zero times, since the slot held no old string;
* stores `decimals = 18` into the low byte of slot 2;
* checks `CALLVALUE = 0`, then copies the appended runtime (3,124 bytes at offset 380) to memory
  and returns it.

The hash of each slot stays symbolic (`Bytes.keccak`): the clearing loop compares it with
itself.  Gas is exact; the start gas is only bounded below.
-/

namespace Blanc.Lift.Weth9.Creation

open Jaune

/-- The lifted constructor program. -/
abbrev prog : List SFunc := Cert.prog cert

/-- The frame facts the walk needs of the creation frame under historical rule facts: no state
gas (the `SLOAD`/`SSTORE` steps are charged under the frame's actual storage schedule) and a
non-static frame. -/
structure CtorFrameH (sevm : Sevm) : Prop where
  stateGas : sevm.benvStat.rules.stateGas = none
  static : sevm.isStatic = false

/-! ## The string-storing helper (entry 2) -/

/-- The helper's exact cost from the world `b`, storing `v` at slot `p`. -/
def helperCost (sevm : Sevm) (b : Devm) (p v : B256) : Nat :=
  115 + sstoreCost sevm (afterSload sevm b p) p v + 172 + sloadCost sevm b p + 7

/-- The helperH's exact cost from the world `b`, storing `v` at slot `p`. -/
def helperCostH (sevm : Sevm) (b : Devm) (p v : B256) : Nat :=
  115 + sstoreCostH sevm (afterSloadH sevm b p) p v + 172 + sloadCostH sevm b p + 7

/-- **Storing a short string**, under the frame's actual storage schedule (`0 < ℓ < 32` bytes, left-aligned data word `w` at `s` in memory)
into the empty slot `p`: the slot receives `w | 2ℓ`, the scratch word `0` receives `p`, and the
helperH returns `p`. -/
theorem helperH {sevm : Sevm} (fr : CtorFrameH sevm) {b : Devm} {M : Mem} {n ℓ : Nat}
    {s p r w : B256} {R : List B256} (hℓ : ℓ < 32) (hsz : M.size = n) (hn : n % 32 = 0)
    (h32 : 32 ≤ n) (hs : s.toNat + 32 ≤ n) (hR : R.length < 1000)
    (hold : b.getStorVal sevm.currentTarget p = 0)
    (hw : Bytes.toB256 ((M.write 0 p.toBytes).read s.toNat 32).1 = w)
    (hmask : (~~~ Bytes.toB256 [0xff]) &&& w = w) {G : Nat}
    (hsentry : gCallStipend < G + 115) :
    SFunc.RunExact prog sevm
      (St b (Nat.toB256 ℓ :: s :: p :: r :: R) M
        (G + helperCostH sevm b p (Nat.toB256 (ℓ + ℓ) ||| w)))
      t_00c8_c2
      (.returned (St (afterSstoreH sevm (afterSloadH sevm b p) p (Nat.toB256 (ℓ + ℓ) ||| w))
        (p :: R) (M.write 0 p.toBytes) G)) := by
  have hsz' : (M.write 0 p.toBytes).size = n := by
    rw [Mem.size_write_word_aligned (by omega) (by omega), hsz]; omega
  have hgt : ∀ x : B256, B256.gtCheck x x = 0 := fun x => by
    unfold B256.gtCheck; rw [ite_eq_right (lt_irrefl x)]
  rw [show G + helperCostH sevm b p (Nat.toB256 (ℓ + ℓ) ||| w) =
    G + 115 + sstoreCostH sevm (afterSloadH sevm b p) p (Nat.toB256 (ℓ + ℓ) ||| w) + 172 +
      sloadCostH sevm b p + 7 by unfold helperCostH; omega]
  unfold t_00c8_c2
  refine rx_dest ?_
  refine rx_dup (n := 2) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_sload_selH fr.stateGas (by simp only [List.length_cons]; omega) ?_
  rw [hold]
  refine rx_push (w := 1) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 1) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := 0) (b256_and_zero _) (by simp only [List.length_cons]; omega) ?_
  refine rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 256) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_mul (v := 256) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_sub' (v := 255) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := 0) (b256_and_zero _) (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 2) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_div (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_push (w := 0) (by decide) (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) (M' := M.write 0 p.toBytes) ?_ rfl ?_
  · exact charge_covered hsz hn (by rw [show (0 : B256).toNat = 0 from rfl]; omega)
  refine rx_push (w := 32) (by decide) (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rx_push (w := 0) (by decide) (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rx_keccak (c := 36) (v := Bytes.keccak ((M.write 0 p.toBytes).read 0 32).1) ?_ rfl
    (read_covered hsz' hn (by rw [show (0 : B256).toNat = 0 from rfl]; omega)) (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, List.length_cons]; omega) ?_
  · rw [St.extCost_eq hsz']
    show gKeccak256 + gasKeccak256Word * ceilDiv 32 32 +
      (calculateMemoryGasCost (memExtSize n 0 32) - calculateMemoryGasCost n) = 36
    rw [memExtSize_of_le hn (by omega), Nat.sub_self]; rfl
  refine rx_swap (n := 0) rfl ?_
  refine rx_push (w := 31) (by decide) (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rx_add' (v := 31) (by decide) (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rx_push (w := 32) (by decide) (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_div (v := 0) (by decide) (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rx_dup (n := 1) rfl (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rx_add' (B256.add_zero _) (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rx_swap (n := 2) rfl ?_
  refine rx_dup (n := 2) rfl (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, Nat.reduceMod, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rx_push (w := Nat.toB256 31) (by decide) (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, Nat.reduceMod, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rx_lt (v := 0) ?_ (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, Nat.reduceMod, List.set_cons_succ, List.length_cons]; omega) ?_
  · rw [lt_toB256 (by omega) (by omega), ite_eq_right (by omega)]
  refine rx_push rfl (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, Nat.reduceMod, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rx_branch_zero ?_
  unfold t_00f9_c2
  refine rx_dup (n := 0) rfl (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, Nat.reduceMod, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rx_mload (c := 3) (v := w) (charge_covered hsz' hn hs) hw (read_covered hsz' hn hs)
    (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, Nat.reduceMod, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rx_push rfl (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, Nat.reduceMod, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rx_not rfl (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, Nat.reduceMod, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rx_and hmask (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, Nat.reduceMod, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rx_dup (n := 3) rfl (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, Nat.reduceMod, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rx_dup (n := 0) rfl (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, Nat.reduceMod, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rx_add' (toB256_add_toB256 (by omega)) (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, Nat.reduceMod, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rx_or rfl (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, Nat.reduceMod, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rx_dup (n := 5) rfl (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, Nat.reduceMod, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rx_sstoreH fr.stateGas (fun _ => by omega) fr.static ?_
  refine rx_push rfl (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.set_cons_zero, Nat.reduceMod, List.set_cons_succ, List.length_cons]; omega) ?_
  refine rx_jump (j := 1) rfl ?_
  unfold t_0137_c1
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_push rfl (by simp only [List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons]; omega) ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_push rfl (by simp only [List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.one_mod, List.length_cons]; omega) ?_
  refine rx_callRet (j := 4) (D := ?D) rfl ?hcall ?k
  case hcall =>
    unfold t_0148_c4
    refine rx_dest ?_
    refine rx_push rfl (by simp only [List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.one_mod, List.length_cons]; omega) ?_
    refine rx_swap (n := 1) rfl ?_
    refine rx_swap (n := 0) rfl ?_
    unfold t_014e_c4
    refine rx_dest ?_
    refine rx_dup (n := 0) rfl (by simp only [List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.one_mod, List.length_cons]; omega) ?_
    refine rx_dup (n := 2) rfl (by simp only [List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.one_mod, List.length_cons]; omega) ?_
    refine rx_gt (hgt _) (by simp only [List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.one_mod, List.length_cons]; omega) ?_
    refine rx_iszero (v := 1) (by decide) (by simp only [List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.one_mod, List.length_cons]; omega) ?_
    refine rx_push rfl (by simp only [List.set_cons_succ, List.set_cons_zero, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.one_mod, List.length_cons]; omega) ?_
    refine rx_branch_succ (by decide) ?_
    unfold t_0166_c4
    refine rx_dest ?_
    refine rx_pop ?_
    refine rx_swap (n := 0) rfl ?_
    refine rx_jump (j := 7) rfl ?_
    unfold t_016a_c7
    refine rx_dest ?_
    refine rx_swap (n := 0) rfl ?_
    exact rx_ret
  case k =>
    unfold t_0144_c1
    refine rx_dest ?_
    refine rx_pop ?_
    refine rx_swap (n := 0) rfl ?_
    exact rx_ret

/-! ## Memory and words of the main walk -/

/-- `"Wrapped Ether"`, left-aligned. -/
def nameWord : B256 := Bytes.toB256 [0x57, 0x72, 0x61, 0x70, 0x70, 0x65, 0x64, 0x20, 0x45, 0x74,
  0x68, 0x65, 0x72, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

/-- `"WETH"`, left-aligned. -/
def symbolWord : B256 := Bytes.toB256 [0x57, 0x45, 0x54, 0x48, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

/-- The slot-0 word: `"Wrapped Ether"` with `2 · 13` in its low byte. -/
def nameSlotWord : B256 := Nat.toB256 (13 + 13) ||| nameWord

/-- The slot-1 word: `"WETH"` with `2 · 4` in its low byte. -/
def symbolSlotWord : B256 := Nat.toB256 (4 + 4) ||| symbolWord

def m1 : Mem := Mem.empty.write 64 (Nat.toB256 96).toBytes
def m2 : Mem := m1.write 64 (Nat.toB256 160).toBytes
def m3 : Mem := m2.write 96 (Nat.toB256 13).toBytes
def m4 : Mem := m3.write 128 nameWord.toBytes
def m5 : Mem := m4.write 0 (0 : B256).toBytes
def m6 : Mem := m5.write 64 (Nat.toB256 224).toBytes
def m7 : Mem := m6.write 160 (Nat.toB256 4).toBytes
def m8 : Mem := m7.write 192 symbolWord.toBytes
def m9 : Mem := m8.write 0 (1 : B256).toBytes

theorem m1_size : m1.size = 96 := by
  rw [m1, Mem.size_write_of_size (show Mem.empty.size = 0 from rfl) (by decide)
    (B256.length_toBytes _)]
  decide
theorem m2_size : m2.size = 96 := by
  rw [m2, Mem.size_write_of_size m1_size (by decide) (B256.length_toBytes _)]
  decide
theorem m3_size : m3.size = 128 := by
  rw [m3, Mem.size_write_of_size m2_size (by decide) (B256.length_toBytes _)]
  decide
theorem m4_size : m4.size = 160 := by
  rw [m4, Mem.size_write_of_size m3_size (by decide) (B256.length_toBytes _)]
  decide
theorem m5_size : m5.size = 160 := by
  rw [m5, Mem.size_write_of_size m4_size (by decide) (B256.length_toBytes _)]
  decide
theorem m6_size : m6.size = 160 := by
  rw [m6, Mem.size_write_of_size m5_size (by decide) (B256.length_toBytes _)]
  decide
theorem m7_size : m7.size = 192 := by
  rw [m7, Mem.size_write_of_size m6_size (by decide) (B256.length_toBytes _)]
  decide
theorem m8_size : m8.size = 224 := by
  rw [m8, Mem.size_write_of_size m7_size (by decide) (B256.length_toBytes _)]
  decide
theorem m9_size : m9.size = 224 := by
  rw [m9, Mem.size_write_of_size m8_size (by decide) (B256.length_toBytes _)]
  decide

theorem nameWord_mask : (~~~ Bytes.toB256 [0xff]) &&& nameWord = nameWord := by decide +kernel
theorem symbolWord_mask : (~~~ Bytes.toB256 [0xff]) &&& symbolWord = symbolWord := by
  decide +kernel

/-- The window the constructor returns: the creation input's bytes `[380, 380 + 3124)`. -/
def runtimeWindow : Bytes := code.sliceD 380 3124 (Linst.toUInt8 .stop)

theorem runtimeWindow_length : runtimeWindow.length = 3124 := ByteArray.length_sliceD _ _ _ _

/-- The memory after the final `CODECOPY`. -/
def m10w : Mem := m9.write 0 runtimeWindow

/-- The final `CODECOPY` charge: 98 words copied, memory grown from 224 bytes to 3,136. -/
def copyCost : Nat :=
  gVerylow + gasCopy * ceilDiv 3124 32 +
    (calculateMemoryGasCost (memExtSize 224 0 3124) - calculateMemoryGasCost 224)

theorem copyCost_eq : copyCost = 588 := by decide

/-- The worlds of the main walk: after the name, after the symbol, after reading decimals. -/
def wName (sevm : Sevm) (b : Devm) : Devm :=
  afterSstore sevm (afterSload sevm b 0) 0 nameSlotWord
def wSymbol (sevm : Sevm) (b : Devm) : Devm :=
  afterSstore sevm (afterSload sevm (wName sevm b) 1) 1 symbolSlotWord
def wDecimals (sevm : Sevm) (b : Devm) : Devm := afterSload sevm (wSymbol sevm b) 2

/-- The constructor's exact cost from the world `b`. -/
def ctorCost (sevm : Sevm) (b : Devm) : Nat :=
  48 + copyCost + sstoreCost sevm (wDecimals sevm b) 2 18 + 40 +
    sloadCost sevm (wSymbol sevm b) 2 + 28 + helperCost sevm (wName sevm b) 1 symbolSlotWord +
    109 + helperCost sevm b 0 nameSlotWord + 124

/-- The worlds of the main walk under the frame's actual storage schedule: after the name, after the symbol, after reading decimals. -/
def wNameH (sevm : Sevm) (b : Devm) : Devm :=
  afterSstoreH sevm (afterSloadH sevm b 0) 0 nameSlotWord
def wSymbolH (sevm : Sevm) (b : Devm) : Devm :=
  afterSstoreH sevm (afterSloadH sevm (wNameH sevm b) 1) 1 symbolSlotWord
def wDecimalsH (sevm : Sevm) (b : Devm) : Devm := afterSloadH sevm (wSymbolH sevm b) 2

/-- The constructor's exact cost from the world `b`. -/
def ctorCostH (sevm : Sevm) (b : Devm) : Nat :=
  48 + copyCost + sstoreCostH sevm (wDecimalsH sevm b) 2 18 + 40 +
    sloadCostH sevm (wSymbolH sevm b) 2 + 28 + helperCostH sevm (wNameH sevm b) 1 symbolSlotWord +
    109 + helperCostH sevm b 0 nameSlotWord + 124

theorem ctorCost_le (sevm : Sevm) (b : Devm) : ctorCost sevm b ≤ 80000 := by
  have hl : ∀ (b : Devm) (k : B256), sloadCost sevm b k ≤ 2100 := by
    intro b k; unfold sloadCost; split <;> decide
  have hs : ∀ (b : Devm) (k v : B256), sstoreCost sevm b k v ≤ 22100 := by
    intro b k v; unfold sstoreCost sstoreValueCost; split_ifs <;> decide
  unfold ctorCost helperCost
  have := hl b 0
  have := hl (wName sevm b) 1
  have := hl (wSymbol sevm b) 2
  have := hs (afterSload sevm b 0) 0 nameSlotWord
  have := hs (afterSload sevm (wName sevm b) 1) 1 symbolSlotWord
  have := hs (wDecimals sevm b) 2 18
  rw [copyCost_eq]
  omega

/-- Under a flat `SLOAD` price of at most 2100, the constructor costs at most 80,000 gas under the
frame's actual storage schedule. -/
theorem ctorCostH_le (sevm : Sevm) (b : Devm)
    (flat : ∀ g, sevm.benvStat.rules.access = .flat g → g.sload ≤ 2100) :
    ctorCostH sevm b ≤ 80000 := by
  have hl : ∀ (b : Devm) (k : B256), sloadCostH sevm b k ≤ 2100 := fun _ _ => sloadCostH_le flat
  have hs : ∀ (b : Devm) (k v : B256), sstoreCostH sevm b k v ≤ 22100 :=
    fun _ _ _ => sstoreCostH_le flat
  unfold ctorCostH helperCostH
  have := hl b 0
  have := hl (wNameH sevm b) 1
  have := hl (wSymbolH sevm b) 2
  have := hs (afterSloadH sevm b 0) 0 nameSlotWord
  have := hs (afterSloadH sevm (wNameH sevm b) 1) 1 symbolSlotWord
  have := hs (wDecimalsH sevm b) 2 18
  rw [copyCost_eq]
  omega

/-! ## The whole constructor -/

/-- The constructor's storage: the fresh storage with name, symbol and decimals written. -/
def ctorStor (s : Stor) : Stor := ((s.set 0 nameSlotWord).set 1 symbolSlotWord).set 2 18

/-- The walk up to the name string's storage (entry 0 through the first helperH call). -/
theorem segNameH {sevm : Sevm} (fr : CtorFrameH sevm) {b : Devm}
    (hold0 : b.getStorVal sevm.currentTarget 0 = 0) {X : Nat} (hX : 2300 ≤ X) {o : Outcome}
    (k : SFunc.RunExact prog sevm (St (wNameH sevm b) [0] m5 X) t_004f_c0 o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (X + helperCostH sevm b 0 nameSlotWord + 8 + 116))
      t_0000_c0 o := by
  unfold t_0000_c0
  refine rx_push (w := Nat.toB256 96) (by decide) (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  refine rx_push (w := Nat.toB256 64) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_mstore (c := 12) (M' := m1) ?_ rfl ?_
  · rw [St.extCost_eq (show Mem.empty.size = 0 from rfl)]; decide
  refine rx_push (w := Nat.toB256 64) (by decide) (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_mload (c := 3) (v := Nat.toB256 96) (charge_covered m1_size (by decide) (by decide))
    (by decide +kernel) (read_covered m1_size (by decide) (by decide)) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_swap (n := 0) (S' := [Nat.toB256 64, Nat.toB256 96]) rfl ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add' (v := Nat.toB256 160) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_push (w := Nat.toB256 64) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_mstore (c := 3) (M' := m2) (charge_covered m1_size (by decide) (by decide)) rfl ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_push (w := Nat.toB256 13) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_mstore (c := 6) (M' := m3) ?_ rfl ?_
  · rw [St.extCost_eq m2_size]; decide
  refine rx_push (w := Nat.toB256 32) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add' (v := Nat.toB256 128) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_push (w := nameWord) rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_mstore (c := 6) (M' := m4) ?_ rfl ?_
  · rw [St.extCost_eq m3_size]; decide
  refine rx_pop ?_
  refine rx_push (w := 0) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_swap (n := 0) (S' := [Nat.toB256 96, 0]) rfl ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_mload (c := 3) (v := Nat.toB256 13) (charge_covered m4_size (by decide) (by decide))
    (by decide +kernel) (read_covered m4_size (by decide) (by decide)) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_swap (n := 0) (S' := [Nat.toB256 96, Nat.toB256 13, 0]) rfl ?_
  refine rx_push (w := Nat.toB256 32) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add' (v := Nat.toB256 128) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_swap (n := 0) (S' := [Nat.toB256 13, Nat.toB256 128, 0]) rfl ?_
  refine rx_push (w := Nat.toB256 0x4f) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_swap (n := 2) (S' := [0, Nat.toB256 13, Nat.toB256 128, Nat.toB256 0x4f]) rfl ?_
  refine rx_swap (n := 1) (S' := [Nat.toB256 128, Nat.toB256 13, 0, Nat.toB256 0x4f]) rfl ?_
  refine rx_swap (n := 0) (S' := [Nat.toB256 13, Nat.toB256 128, 0, Nat.toB256 0x4f]) rfl ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_callRet (j := 2) rfl (helperH fr (ℓ := 13) (n := 160) (R := []) (by decide) m4_size
    (by decide) (by decide) (by decide) (by simp only [List.length_nil, Nat.ofNat_pos]) hold0 (by decide +kernel) nameWord_mask
    (by unfold gCallStipend; omega)) k

/-- The walk of the symbol string's storage (from the first call's return through the second
helperH call). -/
theorem segSymbolH {sevm : Sevm} (fr : CtorFrameH sevm) {b : Devm}
    (hold1 : (wNameH sevm b).getStorVal sevm.currentTarget 1 = 0) {X : Nat} (hX : 2300 ≤ X)
    {o : Outcome} (k : SFunc.RunExact prog sevm (St (wSymbolH sevm b) [1] m9 X) t_009b_c0 o) :
    SFunc.RunExact prog sevm
      (St (wNameH sevm b) [0] m5 (X + helperCostH sevm (wNameH sevm b) 1 symbolSlotWord + 8 + 101))
      t_004f_c0 o := by
  unfold t_004f_c0
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push (w := Nat.toB256 64) (by decide) (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_mload (c := 3) (v := Nat.toB256 160) (charge_covered m5_size (by decide) (by decide))
    (by decide +kernel) (read_covered m5_size (by decide) (by decide)) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_swap (n := 0) (S' := [Nat.toB256 64, Nat.toB256 160]) rfl ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add' (v := Nat.toB256 224) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_push (w := Nat.toB256 64) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_mstore (c := 3) (M' := m6) (charge_covered m5_size (by decide) (by decide)) rfl ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_push (w := Nat.toB256 4) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_mstore (c := 6) (M' := m7) ?_ rfl ?_
  · rw [St.extCost_eq m6_size]; decide
  refine rx_push (w := Nat.toB256 32) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add' (v := Nat.toB256 192) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_push (w := symbolWord) rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_mstore (c := 6) (M' := m8) ?_ rfl ?_
  · rw [St.extCost_eq m7_size]; decide
  refine rx_pop ?_
  refine rx_push (w := 1) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_swap (n := 0) (S' := [Nat.toB256 160, 1]) rfl ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_mload (c := 3) (v := Nat.toB256 4) (charge_covered m8_size (by decide) (by decide))
    (by decide +kernel) (read_covered m8_size (by decide) (by decide)) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_swap (n := 0) (S' := [Nat.toB256 160, Nat.toB256 4, 1]) rfl ?_
  refine rx_push (w := Nat.toB256 32) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add' (v := Nat.toB256 192) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_swap (n := 0) (S' := [Nat.toB256 4, Nat.toB256 192, 1]) rfl ?_
  refine rx_push (w := Nat.toB256 0x9b) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_swap (n := 2) (S' := [1, Nat.toB256 4, Nat.toB256 192, Nat.toB256 0x9b]) rfl ?_
  refine rx_swap (n := 1) (S' := [Nat.toB256 192, Nat.toB256 4, 1, Nat.toB256 0x9b]) rfl ?_
  refine rx_swap (n := 0) (S' := [Nat.toB256 4, Nat.toB256 192, 1, Nat.toB256 0x9b]) rfl ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_callRet (j := 2) rfl (helperH fr (ℓ := 4) (n := 224) (R := []) (by decide) m8_size
    (by decide) (by decide) (by decide) (by simp only [List.length_nil, Nat.ofNat_pos]) hold1 (by decide +kernel) symbolWord_mask
    (by unfold gCallStipend; omega)) k

/-- The walk from the second call's return: decimals, the value check, the runtime copy and
`RETURN`. -/
theorem segDecimalsH {sevm : Sevm} (fr : CtorFrameH sevm) (hcode : sevm.code = code)
    (hvalue : sevm.value = 0) {b : Devm}
    (hold2 : (wSymbolH sevm b).getStorVal sevm.currentTarget 2 = 0) {G : Nat} (hG : 2300 ≤ G) :
    SFunc.RunExact prog sevm
      (St (wSymbolH sevm b) [1] m9 (G + 3 + copyCost + 45 +
        sstoreCostH sevm (wDecimalsH sevm b) 2 18 + 40 + sloadCostH sevm (wSymbolH sevm b) 2 + 28))
      t_009b_c0 (.halted (returnPost (St (afterSstoreH sevm (wDecimalsH sevm b) 2 18)
        [Nat.toB256 0, Nat.toB256 3124] m10w G) (Nat.toB256 0)
        (Nat.toB256 3124) [])) := by
  have hbexp : B256.bexp 256 0 = 1 := by decide +kernel
  have hs10 : m10w.size = 3136 := by
    rw [m10w, Mem.size_write_of_size m9_size (by decide) runtimeWindow_length]; decide
  unfold t_009b_c0
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push (w := 18) (by decide) (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  refine rx_push (w := 2) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_push (w := 0) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push (w := 256) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_exp' (c := 10) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  rw [hbexp]
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_sload_selH fr.stateGas (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  rw [hold2]
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push (w := 255) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_mul (v := 255) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_not rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_and (v := 0) (b256_and_zero _) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_swap (n := 0) (S' := [1, 0, 2, 18]) rfl ?_
  refine rx_dup (n := 3) rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push (w := 255) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_and (v := 18) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_mul (v := 18) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_or (v := 18) (b256_or_zero _) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_swap (n := 0) (S' := [2, 18, 18]) rfl ?_
  refine rx_sstoreH fr.stateGas (fun _ => by unfold gCallStipend; omega) fr.static ?_
  refine rx_pop ?_
  refine rx_callvalue (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  rw [hvalue]
  refine rx_iszero (v := 1) (by decide) (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_00c3_c0
  refine rx_dest ?_
  refine rx_push rfl (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  refine rx_jump (j := 3) rfl ?_
  unfold t_016d_c3
  refine rx_dest ?_
  refine rx_push (w := Nat.toB256 3124) (by decide) (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_push (w := Nat.toB256 380) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push (w := Nat.toB256 0) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_codecopy (c := copyCost) (M' := m10w) ?_ ?_ ?_
  · rw [St.extCost_eq m9_size]
    simp only [toNat_toB256' (show 3124 < 2 ^ 256 by decide),
      toNat_toB256' (show 0 < 2 ^ 256 by decide)]
    rfl
  · simp only [toNat_toB256' (show 3124 < 2 ^ 256 by decide),
      toNat_toB256' (show 0 < 2 ^ 256 by decide), toNat_toB256' (show 380 < 2 ^ 256 by decide)]
    rw [hcode]
    rfl
  refine rx_push (w := Nat.toB256 0) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_return_any rfl ?_
  rw [St.extCost_eq hs10]
  simp only [toNat_toB256' (show 3124 < 2 ^ 256 by decide),
    toNat_toB256' (show 0 < 2 ^ 256 by decide)]
  decide


/-- The constructor's final world, projected before substituting a memory image. -/
theorem ctor_return_stateH (sevm : Sevm) (b : Devm) (M : Mem) (G : Nat) :
    (returnPost (St (afterSstoreH sevm (wDecimalsH sevm b) 2 18)
      [Nat.toB256 0, Nat.toB256 3124] M G) (Nat.toB256 0) (Nat.toB256 3124) []).state =
      ((b.state.setStorVal sevm.currentTarget 0 nameSlotWord).setStorVal
        sevm.currentTarget 1 symbolSlotWord).setStorVal sevm.currentTarget 2 18 := by
  rw [returnPost_state, St_state]
  rw [afterSstoreH_state]
  unfold wDecimalsH wSymbolH wNameH
  simp only [afterSloadH_state, afterSstoreH_state]

/-- **The WETH9 constructor, gas-exact, from rule facts** (`CtorFrameH`): from a fresh account (empty storage, zero call value)
with an empty stack and memory and `G + ctorCostH` gas, the lifted constructor halts with `G`
gas left, returning the runtime window, with the world's error unchanged and the name, symbol
and decimals written. -/
theorem ctor_run_framedH {sevm : Sevm} (fr : CtorFrameH sevm) (hcode : sevm.code = code)
    (hvalue : sevm.value = 0) {b : Devm}
    (hstor : ∀ x, (Devm.getStor b sevm.currentTarget).get x = 0) {G : Nat} (hG : 2300 ≤ G) :
    ∃ post, SProg.RunExact prog sevm (St b [] Mem.empty (G + ctorCostH sevm b)) post ∧
      post.output = runtimeWindow ∧ post.error = b.error ∧
      Devm.getStor post sevm.currentTarget = ctorStor (Devm.getStor b sevm.currentTarget) ∧
      post.gasLeft = G ∧
      post.state = ((b.state.setStorVal sevm.currentTarget 0 nameSlotWord).setStorVal
        sevm.currentTarget 1 symbolSlotWord).setStorVal sevm.currentTarget 2 18 := by
  set ca := sevm.currentTarget with hca
  set m10 := m10w with hm10
  have hs10 : m10.size = 3136 := by
    rw [hm10, m10w, Mem.size_write_of_size m9_size (by decide) runtimeWindow_length]; decide
  have hout : (m10.read 0 3124).1 = runtimeWindow := by
    have hr : Mem.Reads m10 (Bytes.writeAt (m9.data.toList) 0 runtimeWindow) :=
      Mem.Reads.write (show m9.data.size ≤ m9.size by decide +kernel)
        (fun i => by simp only [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]) 0 _
    rw [hr.read]
    have := Bytes.sliceD_writeAt m9.data.toList runtimeWindow 0
    rwa [runtimeWindow_length] at this
  have hstor' : ∀ x, (Devm.getStor b ca).get x = 0 := hstor
  have hold0 : b.getStorVal ca 0 = 0 := hstor' 0
  have hold1 : (wNameH sevm b).getStorVal ca 1 = 0 := by
    show (Devm.getStor (wNameH sevm b) ca).get 1 = 0
    rw [wNameH, afterSstoreH_getStor_self, afterSloadH_getStor, Stor.get_set_ite,
      ite_eq_right (by decide)]
    exact hstor' 1
  have hold2 : (wSymbolH sevm b).getStorVal ca 2 = 0 := by
    show (Devm.getStor (wSymbolH sevm b) ca).get 2 = 0
    rw [wSymbolH, afterSstoreH_getStor_self, afterSloadH_getStor, Stor.get_set_ite,
      ite_eq_right (by decide), wNameH, afterSstoreH_getStor_self, afterSloadH_getStor,
      Stor.get_set_ite, ite_eq_right (by decide)]
    exact hstor' 2
  refine ⟨returnPost (St (afterSstoreH sevm (wDecimalsH sevm b) 2 18)
      [Nat.toB256 0, Nat.toB256 3124] m10 G) (Nat.toB256 0) (Nat.toB256 3124) [], ⟨t_0000_c0, rfl,
    ?_⟩, ?_⟩
  swap
  · obtain ⟨p1, p2, p3, p4⟩ := returnPost_facts (St (afterSstoreH sevm (wDecimalsH sevm b) 2 18)
      [Nat.toB256 0, Nat.toB256 3124] m10 G) (Nat.toB256 0) (Nat.toB256 3124) []
    refine ⟨?_, ?_, ?_, p4, ?_⟩
    · rw [p1]
      simp only [St.memory, toNat_toB256' (show 3124 < 2 ^ 256 by decide),
        toNat_toB256' (show 0 < 2 ^ 256 by decide)]
      exact hout
    · rw [p2, St_error]
      simp only [afterSstoreH_error, wDecimalsH, wSymbolH, wNameH, afterSloadH_error]
    · rw [p3, St_getStor, hca]
      simp only [afterSstoreH_getStor_self, wDecimalsH, wSymbolH, wNameH, afterSloadH_getStor,
        ctorStor]
    · exact ctor_return_stateH sevm b m10 G
  rw [show G + ctorCostH sevm b = G + 3 + copyCost + 45 +
      sstoreCostH sevm (wDecimalsH sevm b) 2 18 + 40 + sloadCostH sevm (wSymbolH sevm b) 2 + 28 +
      helperCostH sevm (wNameH sevm b) 1 symbolSlotWord + 8 + 101 +
      helperCostH sevm b 0 nameSlotWord + 8 + 116 by unfold ctorCostH; omega]
  exact segNameH fr hold0 (by omega) (segSymbolH fr hold1 (by omega)
    (segDecimalsH fr hcode hvalue hold2 hG))

/-! ## Modern statements from the historical walk -/

end Blanc.Lift.Weth9.Creation
