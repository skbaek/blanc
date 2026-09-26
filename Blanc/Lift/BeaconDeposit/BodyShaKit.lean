import Blanc.Lift.BeaconDeposit.BodySpec
import Blanc.Lift.PackedShaCovered

/-!
# Shared pieces of the deposit body's hashing segments (4 and 5)

The calldata slice helper (entry 13, pc `0x16fe`), the copy-loop entries 14–20 as instances
of the solc packed-SHA shape (`Blanc/Lift/PackedSha.lean`), and a few image facts.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-! ## The slice helper (entry 13) -/

/-- **The calldata slice helper** `x[st:en]` of a `bytes calldata` of length `len` at `x`
(pc `0x16fe`): the bounds checks `st ≤ en` and `en ≤ len` pass, and it returns
`en - st :: st + x` through the return tag.  97 gas. -/
theorem slice13 {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {x len st en ret dv av : B256}
    {S : List B256} (hS : S.length ≤ 900)
    (h1 : B256.gtCheck st en = 0) (h2 : B256.gtCheck en len = 0)
    (hd : en - st = dv) (ha : st + x = av) :
    SFunc.RunExact prog sevm (St b (x :: len :: st :: en :: ret :: S) M (G + 97)) t_16fe_c13
      (.returned (St b (dv :: av :: S) M G)) := by
  subst hd ha
  unfold t_16fe_c13
  refine rx_dest ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_dup (n := 0) rfl (by simp; omega) ?_
  refine rx_dup (n := 5) rfl (by simp; omega) ?_
  refine rx_dup (n := 5) rfl (by simp; omega) ?_
  refine rx_gt h1 (by simp; omega) ?_
  refine rx_iszero (v := 1) (by decide) (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_170d_c13
  refine rx_dest ?_
  refine rx_dup (n := 3) rfl (by simp; omega) ?_
  refine rx_dup (n := 6) rfl (by simp; omega) ?_
  refine rx_gt h2 (by simp; omega) ?_
  refine rx_iszero (v := 1) (by decide) (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_1719_c13
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_dup (n := 2) rfl (by simp; omega) ?_
  refine rx_add (by simp; omega) ?_
  refine rx_swap (n := 3) rfl ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_swap (n := 2) rfl ?_
  refine rx_sub (by simp; omega) ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_pop ?_
  exact rx_ret

theorem push0_add (x : B256) : Bytes.toB256 [0x00] + x = x := by
  apply B256.toNat_inj
  rw [B256.toNat_add, show (Bytes.toB256 [0x00]).toNat = 0 from rfl, Nat.zero_add,
    Nat.lo_eq_of_lt (B256.toNat_lt _)]

theorem prog_13 : prog[13]? = some t_16fe_c13 := rfl

/-! ## Calldata words -/

/-- The calldata word at `p` (zero-padded). -/
def cdWord (sevm : Sevm) (p : Nat) : B256 := Bytes.toB256 (sevm.data.sliceD p 32 0)

theorem cdWord_toBytes (sevm : Sevm) (p : Nat) :
    (cdWord sevm p).toBytes = sevm.data.sliceD p 32 0 :=
  Bytes.toBytes_toB256_of_length (List.length_sliceD _ _ _ _)

theorem cdWord_pair (sevm : Sevm) (p : Nat) :
    (cdWord sevm p).toBytes ++ (cdWord sevm (p + 32)).toBytes = sevm.data.sliceD p 64 0 := by
  rw [cdWord_toBytes, cdWord_toBytes, show (64 : Nat) = 32 + 32 from rfl, List.sliceD_add]

/-- A calldata window copied into an image reads back word by word. -/
theorem sliceD_cd_word (img : Bytes) (sevm : Sevm) (q p len j : Nat) (hj : j + 32 ≤ len) :
    (Bytes.writeAt img q (sevm.data.sliceD p len 0)).sliceD (q + j) 32 0 =
      (cdWord sevm (p + j)).toBytes := by
  rw [Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [List.length_sliceD]; omega),
    show q + j - q = j by omega, Bytes.sliceD_sliceD_of_le _ _ _ _ _ hj, cdWord_toBytes]

/-! ## The copy loops as packed-SHA sites -/

/-- The hash tail of loop entry `k` (exit `ex`, call checks `c`, `v`). -/
abbrev shaTail (c0 c1 v0 v1 : UInt8) (f1 f2 T : SFunc) : SFunc :=
  mergeTree (shaCallTree c0 c1 v0 v1 f1 f2 T)

theorem prog_14 : prog[14]? = some (mcpyTree 0x08 0xf8 0x08 0xbb 14
    (shaTail 0x09 0x55 0x09 0x6a t_094c_c14 t_0966_c14 t_096a_c14)) := rfl
theorem prog_15 : prog[15]? = some (mcpyTree 0x09 0xf4 0x09 0xb7 15
    (shaTail 0x0a 0x51 0x0a 0x66 t_0a48_c15 t_0a62_c15 t_0a66_c15)) := rfl
theorem prog_16 : prog[16]? = some (mcpyTree 0x0a 0xda 0x0a 0x9d 16
    (shaTail 0x0b 0x37 0x0b 0x4c t_0b2e_c16 t_0b48_c16 t_0b4c_c16)) := rfl
theorem prog_17 : prog[17]? = some (mcpyTree 0x0b 0xd9 0x0b 0x9c 17
    (shaTail 0x0c 0x36 0x0c 0x4b t_0c2d_c17 t_0c47_c17 t_0c4b_c17)) := rfl
theorem prog_19 : prog[19]? = some (mcpyTree 0x0d 0x4e 0x0d 0x11 19
    (shaTail 0x0d 0xab 0x0d 0xc0 t_0da2_c19 t_0dbc_c19 t_0dc0_c19)) := rfl
theorem prog_20 : prog[20]? = some (mcpyTree 0x0e 0x34 0x0d 0xf7 20
    (shaTail 0x0e 0x91 0x0e 0xa6 t_0e88_c20 t_0ea2_c20 t_0ea6_c20)) := rfl

theorem t_08bb_c12_eq : t_08bb_c12 = mcpyTree 0x08 0xf8 0x08 0xbb 14 t_08f8_c12 := rfl
theorem t_09b7_c14_eq : t_09b7_c14 = mcpyTree 0x09 0xf4 0x09 0xb7 15 t_09f4_c14 := rfl
theorem t_0a9d_c15_eq : t_0a9d_c15 = mcpyTree 0x0a 0xda 0x0a 0x9d 16 t_0ada_c15 := rfl
theorem t_0b9c_c16_eq : t_0b9c_c16 = mcpyTree 0x0b 0xd9 0x0b 0x9c 17 t_0bd9_c16 := rfl
theorem t_0d11_c17_eq : t_0d11_c17 = mcpyTree 0x0d 0x4e 0x0d 0x11 19 t_0d4e_c17 := rfl
theorem t_0df7_c19_eq : t_0df7_c19 = mcpyTree 0x0e 0x34 0x0d 0xf7 20 t_0e34_c19 := rfl
theorem t_0c6c_c17_eq : t_0c6c_c17 = mcpyTree 0x0c 0xa9 0x0c 0x6c 18 t_0ca9_c17 := rfl

end Blanc.Lift.BeaconDeposit
