import Blanc.Lift.Curve3Pool.Walk.Kit
import Blanc.Lift.Curve3Pool.Decode
import Blanc.Lift.VyperDispatchWalk

/-!
# The prologue and dispatcher, on the actual derivation

From the frame's start (pc `0`, empty stack and memory) the runtime checks `CALLDATASIZE ≥ 4`,
runs the Vyper prologue (`mstore(0x1c, calldataload(0))` and the five clamp constants), and tests
the selector arm by arm, jumping over the internal-function blocks between arms
(`PUSH1 0; ISZERO; PUSH2 t; JUMPI`, always taken).

The test chain is walked by evaluation (`Blanc/Lift/VyperDispatchWalk.lean`) over the runtime's
trie decoder `poolDec`:

* `dq_prologue`: frame entry through the prologue to the first test at `0x245`;
* `poolLinks`/`pool_chain`: the chain of tests and skips, decoded once by the kernel;
* `xa_dispatch`: with selector `σ`, the frame reaches `q = vyHit σ poolLinks 0x52c9` (the
  arm's body, past its own test; the kernel computes `q` from the list) with empty stack, the prologue's exact
  memory `vyMem Mem.empty w` (the form `quietSt` uses) and the same remaining children (the
  dispatcher spawns nothing);
* `xa_dispatch_miss`: a selector missing every test reaches the shared fall-through at `0x52c9`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.Lift.NodeWalk

/-- The runtime's instruction decoder, read off its byte tries. -/
abbrev poolDec : Nat → Option Inst := decodeT 15 codeTries.bytes

theorem poolDec_sound {sevm : Sevm} (hcode : sevm.code = code) : DecSound poolDec sevm.code :=
  fun h => hcode ▸ decodeT_sound codeTries h

/-- The shared prefix: frame entry through the prologue to the first test. -/
theorem dq_prologue {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x245 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x2 (.push [0x04] (by decide)) ri_push  -- 0000 PUSH1 0x04
  xs 0x3 (.reg .calldatasize) ri_calldatasize  -- 0002 CALLDATASIZE
  xs 0x4 (.reg .lt) ri_lt  -- 0003 LT
  xs 0x5 (.reg .iszero) ri_iszero  -- 0004 ISZERO
  xs 0x8 (.push [0x00, 0x0d] (by decide)) ri_push  -- 0005 PUSH2 0x000d
  xji 0x9 0xd hw  -- taken
  · exact absurd (ne_of_eqCheck_eq_zero hw) (by
      rw [B256.ltCheck_eq_zero_of_toNat_le (by rw [B256.toNat_toB256_of_lt hcd]; exact hlen)]; decide)
  xjd 0xe
  xs 0x10 (.push [0x00] (by decide)) ri_push  -- 000e PUSH1 0x00
  xs 0x11 (.reg .calldataload) ri_calldataload  -- 0010 CALLDATALOAD
  xs 0x13 (.push [0x1c] (by decide)) ri_push  -- 0011 PUSH1 0x1c
  xs 0x14 (.reg .mstore) ri_mstore  -- 0013 MSTORE
  xs 0x2a (.push [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push  -- 0014 PUSH21 0x010000000000000000000000000000000000000000
  xs 0x2c (.push [0x20] (by decide)) ri_push  -- 002a PUSH1 0x20
  xs 0x2d (.reg .mstore) ri_mstore  -- 002c MSTORE
  xs 0x3e (.push [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)) ri_push  -- 002d PUSH16 0x7fffffffffffffffffffffffffffffff
  xs 0x40 (.push [0x40] (by decide)) ri_push  -- 003e PUSH1 0x40
  xs 0x41 (.reg .mstore) ri_mstore  -- 0040 MSTORE
  xs 0x62 (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push  -- 0041 PUSH32 0xffffffffffffffffffffffffffffffff80000000000000000000000000000000
  xs 0x64 (.push [0x60] (by decide)) ri_push  -- 0062 PUSH1 0x60
  xs 0x65 (.reg .mstore) ri_mstore  -- 0064 MSTORE
  xs 0x7b (.push [0x01, 0x2a, 0x05, 0xf1, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfd, 0xab, 0xf4, 0x1c, 0x00] (by decide)) ri_push  -- 0065 PUSH21 0x012a05f1fffffffffffffffffffffffffdabf41c00
  xs 0x7d (.push [0x80] (by decide)) ri_push  -- 007b PUSH1 0x80
  xs 0x7e (.reg .mstore) ri_mstore  -- 007d MSTORE
  xs 0x9f (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xd5, 0xfa, 0x0e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push  -- 007e PUSH32 0xfffffffffffffffffffffffed5fa0e0000000000000000000000000000000000
  xs 0xa1 (.push [0xa0] (by decide)) ri_push  -- 009f PUSH1 0xa0
  xs 0xa2 (.reg .mstore) ri_mstore  -- 00a1 MSTORE
  replace h : XAt sevm post 0xa2 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) _) L := h
  xs 0xa4 (.push [0x00] (by decide)) ri_push  -- 00a2 PUSH1 0x00
  xs 0xa5 (.reg .iszero) ri_iszero  -- 00a4 ISZERO
  xs 0xa8 (.push [0x02, 0x44] (by decide)) ri_push  -- 00a5 PUSH2 0x0244
  xji 0xa9 0x244 hw  -- taken
  · exact absurd hw (by decide)
  xjd 0x245
  exact ⟨_, h⟩

/-- The dispatcher's chain from the first test: each test's pc and selector, or each
always-taken skip's pc. -/
def poolLinks : List (Nat × Option B256) :=
  [(0x245, some 0xf446c1d0), (0x27a, none), (0x39a, none), (0x4c2, none), (0x7b0, none),
    (0x90e, some 0xbb7b8b80), (0xaf9, some 0x3883e119), (0xe47, some 0x4515cef3),
    (0x189d, none), (0x1d14, some 0x5e0d443f), (0x2046, some 0x07211ef7),
    (0x230b, some 0x3df02124), (0x2c5a, some 0xecb586a5), (0x3041, some 0x9fdaea0c),
    (0x3992, none), (0x3cc3, none), (0x438a, some 0xcc2b27d7), (0x43fe, some 0x1a4d01d2),
    (0x4769, some 0x3c157e64), (0x490c, some 0x551a6588), (0x499c, some 0x5b5a1467),
    (0x4a65, some 0x4f12fe97), (0x4b04, some 0x226840fb), (0x4b32, some 0x6b441a40),
    (0x4bd3, some 0x6a1c05ae), (0x4c57, some 0x86fbf193), (0x4c85, some 0xe2e7d264),
    (0x4d2c, some 0x30c54085), (0x4f52, some 0x524c3901), (0x500b, some 0xe3698853),
    (0x5047, some 0x3046f972), (0x5075, some 0xc6610657), (0x50b5, some 0x4903b0d1),
    (0x50f5, some 0xddca3f43), (0x511c, some 0xfee3f7f9), (0x5143, some 0x8da5cb5b),
    (0x516a, some 0x5409491a), (0x5191, some 0xb4b577ad), (0x51b8, some 0x2081066c),
    (0x51df, some 0x14052288), (0x5206, some 0x405e28f8), (0x522d, some 0xe0a0b586),
    (0x5254, some 0x58680d0b), (0x527b, some 0xe3824462), (0x52a2, some 0x1ec0cdc1)]

/-- The chain, decoded once from the runtime: it ends at the shared fall-through `0x52c9`. -/
theorem pool_chain : vyChain poolDec 64 0x245 = (poolLinks, 0x52c9) := by decide +kernel

/-- **The dispatcher hands the arm of `σ` its body** (past the arm's own test), with the
prologue's exact memory and the frame's remaining children unchanged. -/
theorem xa_dispatch {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {σ : B256}
    {q : Nat} (hcode : sevm.code = code) (hlen : 4 ≤ sevm.data.length)
    (hcd : sevm.data.length < 2 ^ 256) (hsel : Sevm.selector sevm = σ)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L)
    (hq : vyHit σ poolLinks 0x52c9 = q := by decide +kernel) :
    ∃ G', XAt sevm post q (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  obtain ⟨_, h⟩ := dq_prologue hcode hlen hcd h
  exact hq ▸ xa_vyChain (poolDec_sound hcode) hsel 64 pool_chain h

/-- The chain tests the 38 selectors, in `sels`'s order. -/
theorem poolLinks_sels : poolLinks.filterMap Prod.snd = sels := by decide +kernel

/-- **A selector missing every test** reaches the shared fall-through at `0x52c9`. -/
theorem xa_dispatch_miss {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hmiss : ∀ s ∈ sels, Sevm.selector sevm ≠ s) (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x52c9 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  obtain ⟨_, h⟩ := dq_prologue hcode hlen hcd h
  exact xa_vyChain_miss (poolDec_sound hcode) 64 pool_chain (poolLinks_sels ▸ hmiss) h

end Blanc.Lift.Curve3Pool
