import Blanc.Lift.Curve3Pool.Creation.Cert
import Blanc.Lift.Curve3Pool.Layout
import Blanc.Lift.CreationOps
import Blanc.Lift.ExactWalkOps
import Blanc.Lift.PackedSha
import Blanc.Lift.Deploy
import Blanc.StorageAccessGas

/-!
# The 3pool constructor, walked

A gas-exact synthetic run (`SProg.RunExact`) of the lifted Vyper 0.2.4 constructor of the 3pool's
recorded creation input (`Creation/Cert.lean`, 21,967 bytes: constructor `[0, 488)`, runtime
`[488, 21687)`, deploy tail, and the 256 bytes of ABI arguments at `21711`). The constructor

* stores Vyper's five clamp constants at `0x20 … 0xa0`, copies the eight argument words from the
  code to `0x140 … 0x240`, rejects a nonzero call value (entry 0);
* clamps the five address arguments (`_owner`, `_coins[0..2]`, `_pool_token`) to `< 2^160`, each
  by a fresh copy to `0xc0`;
* runs `for i in range(3): assert _coins[i] != ZERO_ADDRESS` (counter at `0x240`; the first pass
  in entry 0, the second and third in entry 1, the loop head);
* stores `coins` at `keccak(0) + i` (the digest computed by the walk, `coinsBase_eq`),
  `initial_A`, `future_A`, `fee`, `admin_fee`, `owner`, `kill_deadline = block.timestamp +
  KILL_DEADLINE_DT` with its overflow check, `token`, and returns the runtime window through the
  deploy tail (entry 2).

Every value is concrete except the block timestamp. Gas is exact; the start gas is only bounded
below. No hash premise: the one digest is a kernel evaluation.
-/

namespace Blanc.Lift.Curve3Pool.Creation

open Jaune Blanc.Lift Blanc.Lift.Curve3Pool

/-- The lifted constructor program. -/
abbrev prog : List SFunc := Cert.prog cert

/-- The frame facts the walk needs of the creation frame. -/
structure CtorFrame (sevm : Sevm) : Prop where
  fork : CoveredFork sevm.benvStat.fork
  static : sevm.isStatic = false

/-! ## The recorded arguments (closed kernel facts on the creation bytes) -/

def ownerW : B256 := 0x6e8f6d1da6232d5e40b0b8758a0145d6c5123eb7
def coin0W : B256 := 0x6b175474e89094c44da98b954eedeac495271d0f
def coin1W : B256 := 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48
def coin2W : B256 := 0xdac17f958d2ee523a2206206994597c13d831ec7
def tokenW : B256 := 0x6c3f90f043a72fa612cbac8115ee7e52bde6e490
def ampW : B256 := 100
def feeW : B256 := 4000000
def adminFeeW : B256 := 0

/-- The 256 argument bytes, as the eight words. -/
def argBytes : Bytes :=
  ownerW.toBytes ++ coin0W.toBytes ++ coin1W.toBytes ++ coin2W.toBytes ++ tokenW.toBytes ++
    ampW.toBytes ++ feeW.toBytes ++ adminFeeW.toBytes

theorem code_toList : code.toList =
    codeChunk0 ++ codeChunk1 ++ codeChunk2 ++ codeChunk3 ++ codeChunk4 ++ codeChunk5 := by
  rw [ByteArray.toList_eq_toList_data]
  rfl

theorem args_eq : code.sliceD 0x54cf 0x100 (Linst.toUInt8 .stop) = argBytes := by
  rw [ByteArray.sliceD_eq, code_toList]; decide +kernel
theorem arg0_eq : code.sliceD 0x54cf 0x20 (Linst.toUInt8 .stop) = ownerW.toBytes := by
  rw [ByteArray.sliceD_eq, code_toList]; decide +kernel
theorem arg1_eq : code.sliceD 0x54ef 0x20 (Linst.toUInt8 .stop) = coin0W.toBytes := by
  rw [ByteArray.sliceD_eq, code_toList]; decide +kernel
theorem arg2_eq : code.sliceD 0x550f 0x20 (Linst.toUInt8 .stop) = coin1W.toBytes := by
  rw [ByteArray.sliceD_eq, code_toList]; decide +kernel
theorem arg3_eq : code.sliceD 0x552f 0x20 (Linst.toUInt8 .stop) = coin2W.toBytes := by
  rw [ByteArray.sliceD_eq, code_toList]; decide +kernel
theorem arg4_eq : code.sliceD 0x554f 0x20 (Linst.toUInt8 .stop) = tokenW.toBytes := by
  rw [ByteArray.sliceD_eq, code_toList]; decide +kernel

/-- The window the deploy tail returns: the creation input's bytes `[488, 488 + 21199)`. -/
def runtimeWindow : Bytes := code.sliceD 0x1e8 0x52cf (Linst.toUInt8 .stop)

theorem runtimeWindow_length : runtimeWindow.length = 0x52cf := ByteArray.length_sliceD _ _ _ _

/-- The returned runtime does not start with `0xEF` (the CREATE code-prefix rule). -/
theorem runtimeWindow_head : runtimeWindow.head? ≠ some 0xEF := by
  rw [runtimeWindow, ByteArray.sliceD_eq, code_toList]; decide +kernel

/-! ## Memory of the walk -/

/-- Vyper's clamp constants, stored at `0x20 … 0xa0`. -/
def clamp1 : B256 := Bytes.toB256 [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
def clamp2 : B256 := Bytes.toB256 [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
def clamp3 : B256 := Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
def clamp4 : B256 := Bytes.toB256 [0x01, 0x2a, 0x05, 0xf1, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfd, 0xab, 0xf4, 0x1c, 0x00]
def clamp5 : B256 := Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xd5, 0xfa, 0x0e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

def m1 : Mem := Mem.empty.write 32 clamp1.toBytes
def m2 : Mem := m1.write 64 clamp2.toBytes
def m3 : Mem := m2.write 96 clamp3.toBytes
def m4 : Mem := m3.write 128 clamp4.toBytes
def m5 : Mem := m4.write 160 clamp5.toBytes
def m6 : Mem := m5.write 0x140 argBytes
def m7 : Mem := m6.write 0xc0 ownerW.toBytes
def m8 : Mem := m7.write 0xc0 coin0W.toBytes
def m9 : Mem := m8.write 0xc0 coin1W.toBytes
def m10 : Mem := m9.write 0xc0 coin2W.toBytes
def m11 : Mem := m10.write 0xc0 tokenW.toBytes
def m12 : Mem := m11.write 0x240 (0 : B256).toBytes
def m13 : Mem := m12.write 0x240 (1 : B256).toBytes
def m14 : Mem := m13.write 0x240 (2 : B256).toBytes
def m15 : Mem := m14.write 0x240 (3 : B256).toBytes
def m16 : Mem := m15.write 0xc0 (0 : B256).toBytes
def m17 : Mem := m16.write 0 runtimeWindow

def img5 : Bytes :=
  Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt [] 32 clamp1.toBytes)
    64 clamp2.toBytes) 96 clamp3.toBytes) 128 clamp4.toBytes) 160 clamp5.toBytes
def img6 : Bytes := Bytes.writeAt img5 0x140 argBytes
def img7 : Bytes := Bytes.writeAt img6 0xc0 ownerW.toBytes
def img8 : Bytes := Bytes.writeAt img7 0xc0 coin0W.toBytes
def img9 : Bytes := Bytes.writeAt img8 0xc0 coin1W.toBytes
def img10 : Bytes := Bytes.writeAt img9 0xc0 coin2W.toBytes
def img11 : Bytes := Bytes.writeAt img10 0xc0 tokenW.toBytes
def img12 : Bytes := Bytes.writeAt img11 0x240 (0 : B256).toBytes
def img13 : Bytes := Bytes.writeAt img12 0x240 (1 : B256).toBytes
def img14 : Bytes := Bytes.writeAt img13 0x240 (2 : B256).toBytes
def img15 : Bytes := Bytes.writeAt img14 0x240 (3 : B256).toBytes
def img16 : Bytes := Bytes.writeAt img15 0xc0 (0 : B256).toBytes

theorem argBytes_length : argBytes.length = 256 := by
  simp only [argBytes, List.length_append, B256.length_toBytes, Nat.reduceAdd]

theorem m5_wf : Mem.Wf m5 ∧ Mem.Reads m5 img5 := by
  have w0 : Mem.Wf Mem.empty := Mem.wf_empty
  have r0 : Mem.Reads Mem.empty [] := Mem.reads_empty
  have w1 := w0.write 32 clamp1.toBytes
  have r1 := r0.write w0 32 clamp1.toBytes
  have w2 := w1.write 64 clamp2.toBytes
  have r2 := r1.write w1 64 clamp2.toBytes
  have w3 := w2.write 96 clamp3.toBytes
  have r3 := r2.write w2 96 clamp3.toBytes
  have w4 := w3.write 128 clamp4.toBytes
  have r4 := r3.write w3 128 clamp4.toBytes
  exact ⟨w4.write 160 clamp5.toBytes, r4.write w4 160 clamp5.toBytes⟩

theorem m11_wf : Mem.Wf m11 ∧ Mem.Reads m11 img11 := by
  obtain ⟨w5, r5⟩ := m5_wf
  have w6 := w5.write 0x140 argBytes
  have r6 := r5.write w5 0x140 argBytes
  have w7 := w6.write 0xc0 ownerW.toBytes
  have r7 := r6.write w6 0xc0 ownerW.toBytes
  have w8 := w7.write 0xc0 coin0W.toBytes
  have r8 := r7.write w7 0xc0 coin0W.toBytes
  have w9 := w8.write 0xc0 coin1W.toBytes
  have r9 := r8.write w8 0xc0 coin1W.toBytes
  have w10 := w9.write 0xc0 coin2W.toBytes
  have r10 := r9.write w9 0xc0 coin2W.toBytes
  exact ⟨w10.write 0xc0 tokenW.toBytes, r10.write w10 0xc0 tokenW.toBytes⟩

theorem m6_reads : Mem.Reads m6 img6 := m5_wf.2.write m5_wf.1 _ _
theorem m7_reads : Mem.Reads m7 img7 := m6_reads.write (m5_wf.1.write _ _) _ _
theorem m8_reads : Mem.Reads m8 img8 := m7_reads.write ((m5_wf.1.write _ _).write _ _) _ _
theorem m9_reads : Mem.Reads m9 img9 :=
  m8_reads.write (((m5_wf.1.write _ _).write _ _).write _ _) _ _
theorem m10_reads : Mem.Reads m10 img10 :=
  m9_reads.write ((((m5_wf.1.write _ _).write _ _).write _ _).write _ _) _ _

theorem m16_wf : Mem.Wf m16 ∧ Mem.Reads m16 img16 := by
  obtain ⟨w11, r11⟩ := m11_wf
  have w12 := w11.write 0x240 (0 : B256).toBytes
  have r12 := r11.write w11 0x240 (0 : B256).toBytes
  have w13 := w12.write 0x240 (1 : B256).toBytes
  have r13 := r12.write w12 0x240 (1 : B256).toBytes
  have w14 := w13.write 0x240 (2 : B256).toBytes
  have r14 := r13.write w13 0x240 (2 : B256).toBytes
  have w15 := w14.write 0x240 (3 : B256).toBytes
  have r15 := r14.write w14 0x240 (3 : B256).toBytes
  exact ⟨w15.write 0xc0 (0 : B256).toBytes, r15.write w15 0xc0 (0 : B256).toBytes⟩

theorem m12_reads : Mem.Reads m12 img12 := m11_wf.2.write m11_wf.1 _ _
theorem m13_reads : Mem.Reads m13 img13 := m12_reads.write (m11_wf.1.write _ _) _ _
theorem m14_reads : Mem.Reads m14 img14 :=
  m13_reads.write ((m11_wf.1.write _ _).write _ _) _ _
theorem m15_reads : Mem.Reads m15 img15 :=
  m14_reads.write (((m11_wf.1.write _ _).write _ _).write _ _) _ _

theorem m1_size : m1.size = 64 := by
  rw [m1, Mem.size_write_of_size (n := 0) rfl (by decide) (B256.length_toBytes _)]; decide
theorem m2_size : m2.size = 96 := by
  rw [m2, Mem.size_write_of_size m1_size (by decide) (B256.length_toBytes _)]; decide
theorem m3_size : m3.size = 128 := by
  rw [m3, Mem.size_write_of_size m2_size (by decide) (B256.length_toBytes _)]; decide
theorem m4_size : m4.size = 160 := by
  rw [m4, Mem.size_write_of_size m3_size (by decide) (B256.length_toBytes _)]; decide
theorem m5_size : m5.size = 192 := by
  rw [m5, Mem.size_write_of_size m4_size (by decide) (B256.length_toBytes _)]; decide
theorem m6_size : m6.size = 576 := by
  rw [m6, Mem.size_write_of_size m5_size (by decide) argBytes_length]; decide
theorem m7_size : m7.size = 576 := by
  rw [m7, Mem.size_write_of_size m6_size (by decide) (B256.length_toBytes _)]; decide
theorem m8_size : m8.size = 576 := by
  rw [m8, Mem.size_write_of_size m7_size (by decide) (B256.length_toBytes _)]; decide
theorem m9_size : m9.size = 576 := by
  rw [m9, Mem.size_write_of_size m8_size (by decide) (B256.length_toBytes _)]; decide
theorem m10_size : m10.size = 576 := by
  rw [m10, Mem.size_write_of_size m9_size (by decide) (B256.length_toBytes _)]; decide
theorem m11_size : m11.size = 576 := by
  rw [m11, Mem.size_write_of_size m10_size (by decide) (B256.length_toBytes _)]; decide
theorem m12_size : m12.size = 608 := by
  rw [m12, Mem.size_write_of_size m11_size (by decide) (B256.length_toBytes _)]; decide
theorem m13_size : m13.size = 608 := by
  rw [m13, Mem.size_write_of_size m12_size (by decide) (B256.length_toBytes _)]; decide
theorem m14_size : m14.size = 608 := by
  rw [m14, Mem.size_write_of_size m13_size (by decide) (B256.length_toBytes _)]; decide
theorem m15_size : m15.size = 608 := by
  rw [m15, Mem.size_write_of_size m14_size (by decide) (B256.length_toBytes _)]; decide
theorem m16_size : m16.size = 608 := by
  rw [m16, Mem.size_write_of_size m15_size (by decide) (B256.length_toBytes _)]; decide
theorem m17_size : m17.size = 21216 := by
  rw [m17, Mem.size_write_of_size m16_size (by decide) runtimeWindow_length]; decide

/-- The returned window. -/
theorem m17_read : (m17.read 0 0x52cf).1 = runtimeWindow := by
  rw [m17, (m16_wf.2.write m16_wf.1 0 runtimeWindow).read]
  have h := Bytes.sliceD_writeAt img16 runtimeWindow 0
  rwa [runtimeWindow_length] at h

/-! ## The prefix: clamp constants, arguments, address clamps, the first loop pass -/

local macro "room" : term => `(Nat.le_of_ble_eq_true rfl)

/-- One address clamp's tail, from the copy of the argument word at `src` to `0xc0`: compare it
with `2^160` and continue to `k`'s tree. -/
theorem clampTail {sevm : Sevm} (hcode : sevm.code = code) {b : Devm} {M M' : Mem} {X : Nat}
    {o : Outcome} {f g : SFunc} {d0 d1 : UInt8} {l3 l4 l5 l6} {src w : B256}
    (hsize : M.size = 576) (hsize' : M'.size = 576)
    (hw : M.write 0xc0 (code.sliceD src.toNat 32 (Linst.toUInt8 .stop)) = M')
    (hv : Bytes.toB256 (M'.read 0xc0 32).1 = w) (hc1 : Bytes.toB256 (M'.read 0x20 32).1 = clamp1)
    (hlt : B256.ltCheck w clamp1 = 1)
    (k : SFunc.RunExact prog sevm (St b [w] M' X) g o) :
    SFunc.RunExact prog sevm (St b [src, 0x20] M (X + 40))
      (.next (.push [0xc0] l3) (.next (.reg .codecopy) (.next (.push [0xc0] l4)
        (.next (.reg .mload) (.next (.push [0x20] l5) (.next (.reg .mload) (.next (.reg (.dup 1))
        (.next (.reg .lt) (.next (.push [d0, d1] l6) (.branch f g)))))))))) o := by
  refine rx_push (w := 0xc0) (by decide) room ?_
  refine rx_codecopy (c := 6) (M' := M') ?_ (by rw [hcode]; exact hw) ?_
  · rw [St.extCost_eq hsize]; decide
  refine rx_push (w := 0xc0) (by decide) room ?_
  refine rx_mload (c := 3) (v := w) (charge_covered hsize' (by decide) (by decide)) hv
    (read_covered hsize' (by decide) (by decide)) room ?_
  refine rx_push (w := 0x20) (by decide) room ?_
  refine rx_mload (c := 3) (v := clamp1) (charge_covered hsize' (by decide) (by decide)) hc1
    (read_covered hsize' (by decide) (by decide)) room ?_
  refine rx_dup (n := 1) rfl room ?_
  refine rx_lt (v := 1) hlt room ?_
  refine rx_push rfl room ?_
  exact rx_branch_succ (by decide) k

/-- **One pass of `for i in range(3): assert _coins[i] != ZERO_ADDRESS`**, from the loop head's
`JUMPDEST` to the exit test's `ISZERO`: read the counter `ci`, bounds-check it, read
`_coins[ci]` at `0x160 + 32 ci`, require it nonzero, store the counter `cn = ci + 1`, and compare
it with `3`. -/
theorem loopPass {sevm : Sevm} {b : Devm} {M M' : Mem} {X : Nat} {o : Outcome}
    {R R' T : SFunc} {l0 l1 l2 l3 l4 l5 l6 l7} {ci off addr v v' cn e z : B256}
    (hsize : M.size = 608)
    (hw : M.write (0x240 : B256).toNat cn.toBytes = M')
    (hci : Bytes.toB256 (M.read 0x240 32).1 = ci) (hlt : B256.ltCheck ci 3 = 1)
    (hoff : 0x20 * ci = off) (haddr : off + 0x160 = addr) (haddr32 : addr.toNat + 32 ≤ 608)
    (hv : Bytes.toB256 (M.read addr.toNat 32).1 = v)
    (hv' : (v ^^^ 0) = v') (hnz : v' ≠ 0) (hcn : 1 + ci = cn) (he : B256.eqCheck 3 cn = e)
    (hz : B256.eqCheck e 0 = z)
    (k : SFunc.RunExact prog sevm (St b [z, 3, 0x240] M' X) T o) :
    SFunc.RunExact prog sevm (St b [3, 0x240] M (X + 98))
      (.dest (.next (.push [0x00] l0) (.next (.push [0x01, 0x60] l1)
        (.next (.push [0x02, 0x40] l2) (.next (.reg .mload) (.next (.push [0x03] l3)
        (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x01, 0x52] l4) (.branch R
        (.dest (.next (.push [0x20] l5) (.next (.reg .mul) (.next (.reg .add) (.next (.reg .mload)
        (.next (.reg .xor) (.next (.push [0x01, 0x61] l6) (.branch R'
        (.dest (.dest (.next (.reg (.dup 1)) (.next (.reg .mload) (.next (.push [0x01] l7)
        (.next (.reg .add) (.next (.reg (.dup 0)) (.next (.reg (.dup 3)) (.next (.reg .mstore)
        (.next (.reg (.dup 1)) (.next (.reg .eq) (.next (.reg .iszero) T))))))))))))))))))))))))))))))
      o := by
  refine rx_dest ?_
  refine rx_push (w := 0) (by decide) room ?_
  refine rx_push (w := 0x160) (by decide) room ?_
  refine rx_push (w := 0x240) (by decide) room ?_
  refine rx_mload (c := 3) (v := ci) (charge_covered hsize (by decide) (by decide)) hci
    (read_covered hsize (by decide) (by decide)) room ?_
  refine rx_push (w := 3) (by decide) room ?_
  refine rx_dup (n := 1) rfl room ?_
  refine rx_lt (v := 1) hlt room ?_
  refine rx_push rfl room ?_
  refine rx_branch_succ (by decide) ?_
  refine rx_dest ?_
  refine rx_push (w := 0x20) (by decide) room ?_
  refine rx_mul hoff room ?_
  refine rx_add' haddr room ?_
  refine rx_mload (c := 3) (v := v) (charge_covered hsize (by decide) haddr32) hv
    (read_covered hsize (by decide) haddr32) room ?_
  refine rx_xor hv' room ?_
  refine rx_push rfl room ?_
  refine rx_branch_succ hnz ?_
  refine rx_dest ?_
  refine rx_dest ?_
  refine rx_dup (n := 1) rfl room ?_
  refine rx_mload (c := 3) (v := ci) (charge_covered hsize (by decide) (by decide)) hci
    (read_covered hsize (by decide) (by decide)) room ?_
  refine rx_push (w := 1) (by decide) room ?_
  refine rx_add' hcn room ?_
  refine rx_dup (n := 0) rfl room ?_
  refine rx_dup (n := 3) rfl room ?_
  refine rx_mstore (c := 3) (M' := M') (charge_covered hsize (by decide) (by decide)) hw ?_
  refine rx_dup (n := 1) rfl room ?_
  refine rx_eq he room ?_
  exact rx_iszero hz room k

/-- The `JUMPDEST`, `POP` and source computation of the second to fifth clamps. -/
theorem clampNext {sevm : Sevm} {b : Devm} {M : Mem} {X : Nat} {o : Outcome} {T : SFunc}
    {a : B256} {s0 s1 p : UInt8} {l0 l1 l2} {src : B256}
    (hsrc : Bytes.toB256 [s0, s1] + Bytes.toB256 [p] = src)
    (k : SFunc.RunExact prog sevm (St b [src, 0x20] M X) T o) :
    SFunc.RunExact prog sevm (St b [a] M (X + 15))
      (.dest (.next (.reg .pop) (.next (.push [0x20] l0) (.next (.push [p] l1)
        (.next (.push [s0, s1] l2) (.next (.reg .add) T)))))) o := by
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push (w := 0x20) (by decide) room ?_
  refine rx_push rfl room ?_
  refine rx_push rfl room ?_
  exact rx_add' hsrc room k

/-- **The prefix**: entry 0 from the frame's start through the first pass of the zero-address
loop, jumping to the loop head (entry 1) with the counter at `1`. -/
theorem segA {sevm : Sevm} (hcode : sevm.code = code) (hvalue : sevm.value = 0) {b : Devm}
    {X : Nat} {o : Outcome}
    (k : SFunc.RunExact prog sevm (St b [3, 0x240] m13 X) t_013c_c1 o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (X + 558)) t_0000_c0 o := by
  unfold t_0000_c0
  refine rx_push (w := clamp1) rfl room ?_
  refine rx_push (w := 0x20) (by decide) room ?_
  refine rx_mstore (c := 9) (M' := m1) ?_ rfl ?_
  · rw [St.extCost_eq (show Mem.empty.size = 0 from rfl)]; decide
  refine rx_push (w := clamp2) rfl room ?_
  refine rx_push (w := 0x40) (by decide) room ?_
  refine rx_mstore (c := 6) (M' := m2) ?_ rfl ?_
  · rw [St.extCost_eq m1_size]; decide
  refine rx_push (w := clamp3) rfl room ?_
  refine rx_push (w := 0x60) (by decide) room ?_
  refine rx_mstore (c := 6) (M' := m3) ?_ rfl ?_
  · rw [St.extCost_eq m2_size]; decide
  refine rx_push (w := clamp4) rfl room ?_
  refine rx_push (w := 0x80) (by decide) room ?_
  refine rx_mstore (c := 6) (M' := m4) ?_ rfl ?_
  · rw [St.extCost_eq m3_size]; decide
  refine rx_push (w := clamp5) rfl room ?_
  refine rx_push (w := 0xa0) (by decide) room ?_
  refine rx_mstore (c := 6) (M' := m5) ?_ rfl ?_
  · rw [St.extCost_eq m4_size]; decide
  refine rx_push (w := 0x100) (by decide) room ?_
  refine rx_push (w := 0x54cf) (by decide) room ?_
  refine rx_push (w := 0x140) (by decide) room ?_
  refine rx_codecopy (c := 63) (M' := m6) ?_ ?_ ?_
  · rw [St.extCost_eq m5_size]; decide
  · rw [hcode]
    show m5.write 0x140 (code.sliceD 0x54cf 0x100 (Linst.toUInt8 .stop)) = _
    rw [args_eq]; rfl
  refine rx_callvalue room ?_
  rw [hvalue]
  refine rx_iszero (v := 1) (by decide) room ?_
  refine rx_push rfl room ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_00a2_c0
  refine rx_dest ?_
  refine rx_push (w := 0x20) (by decide) room ?_
  refine rx_push (w := 0x54cf) (by decide) room ?_
  refine clampTail hcode m6_size m7_size ?_ (w := ownerW)
    (by rw [Mem.Reads.read m7_reads]; decide +kernel)
    (by rw [Mem.Reads.read m7_reads]; decide +kernel) (by decide +kernel) ?_
  · show m6.write 0xc0 (code.sliceD 0x54cf 32 (Linst.toUInt8 .stop)) = _
    rw [arg0_eq]; rfl
  unfold t_00bb_c0
  refine clampNext (s0 := 0x54) (s1 := 0xcf) (p := 0x20) (src := 0x54ef) (by decide) ?_
  refine clampTail hcode m7_size m8_size ?_ (w := coin0W)
    (by rw [Mem.Reads.read m8_reads]; decide +kernel)
    (by rw [Mem.Reads.read m8_reads]; decide +kernel) (by decide +kernel) ?_
  · show m7.write 0xc0 (code.sliceD 0x54ef 32 (Linst.toUInt8 .stop)) = _
    rw [arg1_eq]; rfl
  unfold t_00d8_c0
  refine clampNext (s0 := 0x54) (s1 := 0xcf) (p := 0x40) (src := 0x550f) (by decide) ?_
  refine clampTail hcode m8_size m9_size ?_ (w := coin1W)
    (by rw [Mem.Reads.read m9_reads]; decide +kernel)
    (by rw [Mem.Reads.read m9_reads]; decide +kernel) (by decide +kernel) ?_
  · show m8.write 0xc0 (code.sliceD 0x550f 32 (Linst.toUInt8 .stop)) = _
    rw [arg2_eq]; rfl
  unfold t_00f5_c0
  refine clampNext (s0 := 0x54) (s1 := 0xcf) (p := 0x60) (src := 0x552f) (by decide) ?_
  refine clampTail hcode m9_size m10_size ?_ (w := coin2W)
    (by rw [Mem.Reads.read m10_reads]; decide +kernel)
    (by rw [Mem.Reads.read m10_reads]; decide +kernel) (by decide +kernel) ?_
  · show m9.write 0xc0 (code.sliceD 0x552f 32 (Linst.toUInt8 .stop)) = _
    rw [arg3_eq]; rfl
  unfold t_0112_c0
  refine clampNext (s0 := 0x54) (s1 := 0xcf) (p := 0x80) (src := 0x554f) (by decide) ?_
  refine clampTail hcode m10_size m11_size ?_ (w := tokenW)
    (by rw [Mem.Reads.read m11_wf.2]; decide +kernel)
    (by rw [Mem.Reads.read m11_wf.2]; decide +kernel) (by decide +kernel) ?_
  · show m10.write 0xc0 (code.sliceD 0x554f 32 (Linst.toUInt8 .stop)) = _
    rw [arg4_eq]; rfl
  unfold t_012f_c0
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push (w := 0x240) (by decide) room ?_
  refine rx_push (w := 0) (by decide) room ?_
  refine rx_push (w := 3) (by decide) room ?_
  refine rx_dup (n := 1) rfl room ?_
  refine rx_dup (n := 3) rfl room ?_
  refine rx_mstore (c := 6) (M' := m12) ?_ rfl ?_
  · rw [St.extCost_eq m11_size]; decide
  refine rx_add' (v := 3) (by decide) room ?_
  unfold t_013c_c0
  refine loopPass (ci := 0) (off := 0) (addr := 0x160) (v := coin0W) (cn := 1) (e := 0) (z := 1) m12_size
    rfl (by rw [Mem.Reads.read m12_reads]; decide +kernel) (by decide) (by decide)
    (by decide) (by decide) (by rw [Mem.Reads.read m12_reads]; decide +kernel) rfl
    (by decide +kernel) (by decide) (by decide) (by decide) ?_
  refine rx_push rfl room ?_
  exact rx_branchTo_succ (by decide) rfl k

/-! ## The loop's last two passes, the stores, the runtime -/

/-- `KILL_DEADLINE_DT = 2 · 30 · 86400`. -/
theorem killDt_word : (0x4f1a00 : B256).toNat = killDeadlineDt := by decide

/-- The stored kill deadline does not wrap when the model's checked sum does not. -/
theorem kill_toNat {t : B256} (ht : t.toNat + killDeadlineDt < 2 ^ 256) :
    (t + 0x4f1a00).toNat = t.toNat + killDeadlineDt := by
  rw [B256.toNat_add, killDt_word, Nat.lo, Nat.mod_eq_of_lt ht]

theorem kill_noWrap {t : B256} (ht : t.toNat + killDeadlineDt < 2 ^ 256) :
    B256.ltCheck (t + 0x4f1a00) t = 0 := by
  unfold B256.ltCheck
  split_ifs with h
  · have h' := B256.toNat_lt_toNat h
    rw [kill_toNat ht] at h'
    omega
  · rfl

/-- The worlds of the stores. -/
def tw1 (sevm : Sevm) (b : Devm) : Devm := afterSstore sevm b (coinSlot 0) coin0W
def tw2 (sevm : Sevm) (b : Devm) : Devm := afterSstore sevm (tw1 sevm b) (coinSlot 1) coin1W
def tw3 (sevm : Sevm) (b : Devm) : Devm := afterSstore sevm (tw2 sevm b) (coinSlot 2) coin2W
def tw4 (sevm : Sevm) (b : Devm) : Devm := afterSstore sevm (tw3 sevm b) initialASlot ampW
def tw5 (sevm : Sevm) (b : Devm) : Devm := afterSstore sevm (tw4 sevm b) futureASlot ampW
def tw6 (sevm : Sevm) (b : Devm) : Devm := afterSstore sevm (tw5 sevm b) feeSlot feeW
def tw7 (sevm : Sevm) (b : Devm) : Devm := afterSstore sevm (tw6 sevm b) adminFeeSlot adminFeeW
def tw8 (sevm : Sevm) (b : Devm) : Devm := afterSstore sevm (tw7 sevm b) ownerSlot ownerW
def tw9 (sevm : Sevm) (b : Devm) : Devm :=
  afterSstore sevm (tw8 sevm b) killDeadlineSlot (sevm.benvStat.time + 0x4f1a00)
def tw10 (sevm : Sevm) (b : Devm) : Devm := afterSstore sevm (tw9 sevm b) tokenSlot tokenW

/-- The stores' and the tail's exact cost from the world `b`. -/
def tailCost (sevm : Sevm) (b : Devm) : Nat :=
  4821 + sstoreCost sevm (tw9 sevm b) tokenSlot tokenW + 9 +
    sstoreCost sevm (tw8 sevm b) killDeadlineSlot (sevm.benvStat.time + 0x4f1a00) + 59 +
    sstoreCost sevm (tw7 sevm b) ownerSlot ownerW + 9 +
    sstoreCost sevm (tw6 sevm b) adminFeeSlot adminFeeW + 9 +
    sstoreCost sevm (tw5 sevm b) feeSlot feeW + 9 +
    sstoreCost sevm (tw4 sevm b) futureASlot ampW + 9 +
    sstoreCost sevm (tw3 sevm b) initialASlot ampW + 13 +
    sstoreCost sevm (tw2 sevm b) (coinSlot 2) coin2W + 21 +
    sstoreCost sevm (tw1 sevm b) (coinSlot 1) coin1W + 21 +
    sstoreCost sevm b (coinSlot 0) coin0W + 68

/-- **The constructor's second half**: the loop head's two passes (counter `1` and `2`), then the
stores, the kill-deadline overflow check, and the deploy tail's `CODECOPY`/`RETURN`. -/
theorem segB {sevm : Sevm} (fr : CtorFrame sevm) (hcode : sevm.code = code)
    (ht : sevm.benvStat.time.toNat + killDeadlineDt < 2 ^ 256) {b : Devm} {G : Nat}
    (hG : gCallStipend < G) :
    SFunc.RunExact prog sevm (St b [3, 0x240] m13 (G + tailCost sevm b + 222)) t_013c_c1
      (.halted (returnPost (St (tw10 sevm b) [0, 0x52cf] m17 G) 0 0x52cf [])) := by
  unfold t_013c_c1
  refine loopPass (ci := 1) (off := 0x20) (addr := 0x180) (v := coin1W) (cn := 2) (e := 0)
    (z := 1) (M' := m14) m13_size rfl (by rw [Mem.Reads.read m13_reads]; decide +kernel) (by decide)
    (by decide) (by decide) (by decide) (by rw [Mem.Reads.read m13_reads]; decide +kernel) rfl
    (by decide +kernel) (by decide) (by decide) (by decide) ?_
  refine rx_push rfl room ?_
  refine rx_branchTo_succ (by decide) rfl ?_
  unfold t_013c_c1
  refine loopPass (ci := 2) (off := 0x40) (addr := 0x1a0) (v := coin2W) (cn := 3) (e := 1)
    (z := 0) (M' := m15) m14_size rfl (by rw [Mem.Reads.read m14_reads]; decide +kernel) (by decide)
    (by decide) (by decide) (by decide) (by rw [Mem.Reads.read m14_reads]; decide +kernel) rfl
    (by decide +kernel) (by decide) (by decide) (by decide) ?_
  refine rx_push rfl room ?_
  refine rx_branchTo_zero ?_
  rw [show G + tailCost sevm b = G + 4821 + sstoreCost sevm (tw9 sevm b) tokenSlot tokenW + 9 +
    sstoreCost sevm (tw8 sevm b) killDeadlineSlot (sevm.benvStat.time + 0x4f1a00) + 59 +
    sstoreCost sevm (tw7 sevm b) ownerSlot ownerW + 9 +
    sstoreCost sevm (tw6 sevm b) adminFeeSlot adminFeeW + 9 +
    sstoreCost sevm (tw5 sevm b) feeSlot feeW + 9 +
    sstoreCost sevm (tw4 sevm b) futureASlot ampW + 9 +
    sstoreCost sevm (tw3 sevm b) initialASlot ampW + 13 +
    sstoreCost sevm (tw2 sevm b) (coinSlot 2) coin2W + 21 +
    sstoreCost sevm (tw1 sevm b) (coinSlot 1) coin1W + 21 +
    sstoreCost sevm b (coinSlot 0) coin0W + 68 by unfold tailCost; omega]
  have r16 := m16_wf.2
  unfold t_0172_c1
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_push (w := 0) (by decide) room ?_
  refine rx_push (w := 0xc0) (by decide) room ?_
  refine rx_mstore (c := 3) (M' := m16) (charge_covered m15_size (by decide) (by decide)) rfl ?_
  refine rx_push (w := 0x20) (by decide) room ?_
  refine rx_push (w := 0xc0) (by decide) room ?_
  refine rx_keccak (c := 36) (v := coinSlot 0) ?_ ?_
    (read_covered_len m16_size (by decide) (by decide)) room ?_
  · rw [St.extCost_eq m16_size]; decide
  · rw [Mem.Reads.read r16, show img16.sliceD (0xc0 : B256).toNat (0x20 : B256).toNat 0 =
      (0 : B256).toBytes by decide +kernel, coinsBase_eq]
    decide +kernel
  refine rx_push (w := 0x160) (by decide) room ?_
  refine rx_dup (n := 0) rfl room ?_
  refine rx_mload (c := 3) (v := coin0W) (charge_covered m16_size (by decide) (by decide))
    (by rw [Mem.Reads.read r16]; decide +kernel) (read_covered m16_size (by decide) (by decide))
    room ?_
  refine rx_dup (n := 2) rfl room ?_
  refine rx_sstore fr.fork (by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_dup (n := 0) rfl room ?_
  refine rx_push (w := 0x20) (by decide) room ?_
  refine rx_add' (v := 0x180) (by decide) room ?_
  refine rx_mload (c := 3) (v := coin1W) (charge_covered m16_size (by decide) (by decide))
    (by rw [Mem.Reads.read r16]; decide +kernel) (read_covered m16_size (by decide) (by decide))
    room ?_
  refine rx_push (w := 1) (by decide) room ?_
  refine rx_dup (n := 3) rfl room ?_
  refine rx_add' (v := coinSlot 1) (by decide +kernel) room ?_
  refine rx_sstore fr.fork (by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_dup (n := 0) rfl room ?_
  refine rx_push (w := 0x40) (by decide) room ?_
  refine rx_add' (v := 0x1a0) (by decide) room ?_
  refine rx_mload (c := 3) (v := coin2W) (charge_covered m16_size (by decide) (by decide))
    (by rw [Mem.Reads.read r16]; decide +kernel) (read_covered m16_size (by decide) (by decide))
    room ?_
  refine rx_push (w := 2) (by decide) room ?_
  refine rx_dup (n := 3) rfl room ?_
  refine rx_add' (v := coinSlot 2) (by decide +kernel) room ?_
  refine rx_sstore fr.fork (by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_push (w := 0x1e0) (by decide) room ?_
  refine rx_mload (c := 3) (v := ampW) (charge_covered m16_size (by decide) (by decide))
    (by rw [Mem.Reads.read r16]; decide +kernel) (read_covered m16_size (by decide) (by decide))
    room ?_
  refine rx_push (w := initialASlot) (by decide) room ?_
  refine rx_sstore fr.fork (by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_push (w := 0x1e0) (by decide) room ?_
  refine rx_mload (c := 3) (v := ampW) (charge_covered m16_size (by decide) (by decide))
    (by rw [Mem.Reads.read r16]; decide +kernel) (read_covered m16_size (by decide) (by decide))
    room ?_
  refine rx_push (w := futureASlot) (by decide) room ?_
  refine rx_sstore fr.fork (by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_push (w := 0x200) (by decide) room ?_
  refine rx_mload (c := 3) (v := feeW) (charge_covered m16_size (by decide) (by decide))
    (by rw [Mem.Reads.read r16]; decide +kernel) (read_covered m16_size (by decide) (by decide))
    room ?_
  refine rx_push (w := feeSlot) (by decide) room ?_
  refine rx_sstore fr.fork (by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_push (w := 0x220) (by decide) room ?_
  refine rx_mload (c := 3) (v := adminFeeW) (charge_covered m16_size (by decide) (by decide))
    (by rw [Mem.Reads.read r16]; decide +kernel) (read_covered m16_size (by decide) (by decide))
    room ?_
  refine rx_push (w := adminFeeSlot) (by decide) room ?_
  refine rx_sstore fr.fork (by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_push (w := 0x140) (by decide) room ?_
  refine rx_mload (c := 3) (v := ownerW) (charge_covered m16_size (by decide) (by decide))
    (by rw [Mem.Reads.read r16]; decide +kernel) (read_covered m16_size (by decide) (by decide))
    room ?_
  refine rx_push (w := ownerSlot) (by decide) room ?_
  refine rx_sstore fr.fork (by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_timestamp room ?_
  refine rx_push (w := 0x4f1a00) (by decide) room ?_
  refine rx_dup (n := 1) rfl room ?_
  refine rx_dup (n := 1) rfl room ?_
  refine rx_dup (n := 3) rfl room ?_
  refine rx_add' (v := sevm.benvStat.time + 0x4f1a00) rfl room ?_
  refine rx_lt (v := 0) (kill_noWrap ht) room ?_
  refine rx_iszero (v := 1) (by decide) room ?_
  refine rx_push rfl room ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_01d2_c1
  refine rx_dest ?_
  refine rx_dup (n := 0) rfl room ?_
  refine rx_dup (n := 2) rfl room ?_
  refine rx_add' (v := sevm.benvStat.time + 0x4f1a00) rfl room ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_push (w := killDeadlineSlot) (by decide) room ?_
  refine rx_sstore fr.fork (by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_push (w := 0x1c0) (by decide) room ?_
  refine rx_mload (c := 3) (v := tokenW) (charge_covered m16_size (by decide) (by decide))
    (by rw [Mem.Reads.read r16]; decide +kernel) (read_covered m16_size (by decide) (by decide))
    room ?_
  refine rx_push (w := tokenSlot) (by decide) room ?_
  refine rx_sstore fr.fork (by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_push rfl room ?_
  refine rx_jump (j := 2) rfl ?_
  unfold t_54b7_c2
  refine rx_dest ?_
  refine rx_push (w := 0x1e8) (by decide) room ?_
  refine rx_push (w := 0x54b7) (by decide) room ?_
  refine rx_sub' (v := 0x52cf) (by decide) room ?_
  refine rx_push (w := 0x1e8) (by decide) room ?_
  refine rx_push (w := 0) (by decide) room ?_
  refine rx_codecopy (c := 4782) (M' := m17) ?_ (by rw [hcode]; rfl) ?_
  · rw [St.extCost_eq m16_size]; decide
  refine rx_push (w := 0x1e8) (by decide) room ?_
  refine rx_push (w := 0x54b7) (by decide) room ?_
  refine rx_sub' (v := 0x52cf) (by decide) room ?_
  refine rx_push (w := 0) (by decide) room ?_
  exact rx_return_any (S := []) rfl (by rw [St.extCost_eq m17_size]; decide)

/-! ## The whole constructor -/

/-- The constructor's exact cost from the world `b`. -/
def ctorCost (sevm : Sevm) (b : Devm) : Nat := tailCost sevm b + 780

theorem ctorCost_le (sevm : Sevm) (b : Devm) : ctorCost sevm b ≤ 250000 := by
  have hs : ∀ (b : Devm) (k v : B256), sstoreCost sevm b k v ≤ 22100 := fun b k v =>
    le_trans (sstoreCost_le_value sevm b k v)
      (le_trans (Nat.add_le_add_left (sstoreValueCost_le _ _ _) _) (by decide))
  have := hs (tw9 sevm b) tokenSlot tokenW
  have := hs (tw8 sevm b) killDeadlineSlot (sevm.benvStat.time + 0x4f1a00)
  have := hs (tw7 sevm b) ownerSlot ownerW
  have := hs (tw6 sevm b) adminFeeSlot adminFeeW
  have := hs (tw5 sevm b) feeSlot feeW
  have := hs (tw4 sevm b) futureASlot ampW
  have := hs (tw3 sevm b) initialASlot ampW
  have := hs (tw2 sevm b) (coinSlot 2) coin2W
  have := hs (tw1 sevm b) (coinSlot 1) coin1W
  have := hs b (coinSlot 0) coin0W
  unfold ctorCost tailCost
  omega

/-- **The 3pool constructor, gas-exact**: from a fresh creation frame (zero call value) with an
empty stack and memory and `G + ctorCost` gas, at a timestamp whose kill deadline does not wrap,
the lifted constructor halts with `G` gas left, returning the runtime window. -/
theorem ctor_run {sevm : Sevm} (fr : CtorFrame sevm) (hcode : sevm.code = code)
    (hvalue : sevm.value = 0) (ht : sevm.benvStat.time.toNat + killDeadlineDt < 2 ^ 256)
    {b : Devm} {G : Nat} (hG : gCallStipend < G) :
    SProg.RunExact prog sevm (St b [] Mem.empty (G + ctorCost sevm b))
      (returnPost (St (tw10 sevm b) [0, 0x52cf] m17 G) 0 0x52cf []) := by
  refine ⟨t_0000_c0, rfl, ?_⟩
  rw [show G + ctorCost sevm b = G + tailCost sevm b + 222 + 558 by unfold ctorCost; omega]
  exact segA hcode hvalue (segB fr hcode ht hG)

/-- **The 3pool constructor, with its halting state's facts**: output the runtime window, the
world's error, the stores' storage, `G` gas left. -/
theorem ctor_run_facts {sevm : Sevm} (fr : CtorFrame sevm) (hcode : sevm.code = code)
    (hvalue : sevm.value = 0) (ht : sevm.benvStat.time.toNat + killDeadlineDt < 2 ^ 256)
    {b : Devm} {G : Nat} (hG : gCallStipend < G) :
    ∃ post, SProg.RunExact prog sevm (St b [] Mem.empty (G + ctorCost sevm b)) post ∧
      post.output = runtimeWindow ∧ post.error = b.error ∧
      Devm.getStor post sevm.currentTarget = Devm.getStor (tw10 sevm b) sevm.currentTarget ∧
      post.gasLeft = G := by
  obtain ⟨p1, p2, p3, p4⟩ := returnPost_facts (St (tw10 sevm b) [0, 0x52cf] m17 G) 0 0x52cf []
  refine ⟨_, ctor_run fr hcode hvalue ht hG, ?_, ?_, ?_, p4⟩
  · rw [p1, St.memory]
    exact m17_read
  · rw [p2, St_error]
    simp only [tw10, tw9, tw8, tw7, tw6, tw5, tw4, tw3, tw2, tw1, afterSstore_error]
  · rw [p3, St_getStor]

end Blanc.Lift.Curve3Pool.Creation
