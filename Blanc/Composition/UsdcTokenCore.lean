import Blanc.Lift.Usdc.RefineTransferDispatch
import Blanc.Composition.UniswapV2PairUsdcWeth9LegsKit

/-!
# The USDC implementation's `balanceOf` and `transfer` answers (U7b)

The existing transfer-family walks (`RefineTransferCallees.lean`) forget memory, but a frame's answer
is read back through solc's free-memory pointer: the return tail loads `mload(0x40)` before and after
its `mstore` of the result word, so the answer is the result only while the pointer word holds a
pointer clear of `[0x40, 0x60)`.  Here the callees on the two answer paths keep the free-pointer image
`FpM 0x80` (`e83_mem`, `e96_mem`, `e99_mem`, `e93_mem`, `e37_mem`, `e46_inv`; the SafeMath callees
`e100`/`e98` already keep memory), alongside their existing guard and storage lemmas, and the
frames' return tail answers the word it stores (`tail_output`):

* `impl_balanceOf_output`: a successful fresh implementation frame selecting `balanceOf(a)` returns
  `a`'s balance bits;
* `impl_transfer_output`: one selecting `transfer` returns the word `1`.
-/

namespace Blanc.Composition.UsdcToken

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Blanc.Composition.UsdcLive Impl

local notation "fp80" => Bytes.toB256 [0x80]

theorem n0 : (Bytes.toB256 [0]).toNat = 0 := by decide
theorem n32 : (Bytes.toB256 [32]).toNat = 32 := by decide
theorem n64 : (Bytes.toB256 [64]).toNat = 64 := by decide

/-- solc's mapping-slot scratch (`mstore(0, k)`, `mstore(32, w)`, `keccak256(0, 64)`) keeps the
free-pointer image. -/
theorem FpM.scratch {fp : B256} {n : Nat} {M : Mem} (h : FpM fp n M) (k w : B256) :
    FpM fp n (((M.write (Bytes.toB256 [0]).toNat k.toBytes).write (Bytes.toB256 [32]).toNat
      w.toBytes).read (Bytes.toB256 [0]).toNat (Bytes.toB256 [64]).toNat).2 := by
  have ge := h.ge
  have h1 := (h.write 0 k (by omega) (.inl (by omega))).write 32 w (by omega) (.inl (by omega))
  rw [n0, n32, n64, h1.read_self (by omega)]
  exact h1

theorem FpM.read64 {fp : B256} {n : Nat} {M : Mem} (h : FpM fp n M) :
    M.read (Bytes.toB256 [64]).toNat 32 = (fp.toBytes, M) := by
  have ge := h.ge
  rw [n64]
  exact Prod.ext h.fp (h.read_self (by omega))

theorem nfp80 : (Bytes.toB256 [128]).toNat = 128 := by decide
theorem nwin : (Bytes.toB256 [32] + Bytes.toB256 [128] - Bytes.toB256 [128]).toNat = 32 := by decide

theorem nwin' : (Bytes.toB256 [32] + (Bytes.toB256 [128] - Bytes.toB256 [128])).toNat = 32 := by
  decide

/-- solc's single-word return tail (`p := mload(0x40)`, `mstore(p, v)`, `return(mload(0x40), …)`)
over the free-pointer image answers `v`. -/
theorem tail_output {n : Nat} {M : Mem} (m : FpM (Bytes.toB256 [128]) n M) (hn : n = 96 ∨ n = 160)
    (v : B256) :
    ((((M.read (Bytes.toB256 [64]).toNat 32).2.write (M.read (Bytes.toB256 [64]).toNat 32).1.toB256.toNat
        v.toBytes).read (Bytes.toB256 [64]).toNat 32).2.read
      (((M.read (Bytes.toB256 [64]).toNat 32).2.write (M.read (Bytes.toB256 [64]).toNat 32).1.toB256.toNat
          v.toBytes).read (Bytes.toB256 [64]).toNat 32).1.toB256.toNat
      (Bytes.toB256 [32] + ((M.read (Bytes.toB256 [64]).toNat 32).1.toB256 -
        (((M.read (Bytes.toB256 [64]).toNat 32).2.write
          (M.read (Bytes.toB256 [64]).toNat 32).1.toB256.toNat v.toBytes).read
            (Bytes.toB256 [64]).toNat 32).1.toB256)).toNat).1 = v.toBytes := by
  have m2 : FpM (Bytes.toB256 [128]) 160 (M.write 128 v.toBytes) := by
    rcases hn with rfl | rfl
    · exact FpM.write_out m v
    · exact m.write 128 v (by omega) (.inr (by omega))
  rw [FpM.read64 m]
  dsimp only
  rw [B256.toB256_toBytes, nfp80, FpM.read64 m2]
  dsimp only
  rw [B256.toB256_toBytes, nwin', nfp80, FpM.readback m]

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

variable {fp : B256} {n : Nat} {D : Devm}

theorem e83_mem {a ret : B256} (fork : CoveredFork sevm.benvStat.fork) (hM : FpM fp n M)
    (run : SFunc.Run cert.prog sevm (St b (a :: ret :: S) M G) t_3f6a_c83 (.returned D)) :
    FpM fp n D.memory := by
  have h := run.cut
  clear run
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  cases e
  exact FpM.scratch hM _ _

theorem e96_mem {a ret : B256} (fork : CoveredFork sevm.benvStat.fork) (hM : FpM fp n M)
    (run : SFunc.Run cert.prog sevm (St b (a :: ret :: S) M G) t_41da_c96 (.returned D)) :
    FpM fp n D.memory := by
  have h := run.cut
  clear run
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  cases e
  exact FpM.scratch hM _ _

theorem e99_mem {x y ret : B256} (fork : CoveredFork sevm.benvStat.fork) (hM : FpM fp n M)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: ret :: S) M G) t_4430_c99 (.returned D)) :
    FpM fp n D.memory := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  rcases ric_call (g := t_3f6a_c83) rfl h with ⟨_, ⟨D1, hc, h⟩ | ⟨D1, hc, _⟩⟩
  · have m1 := e83_mem fork hM hc
    obtain ⟨b', M', G', e, -⟩ := e83_inv fork hc
    cases e
    clear hc
    repeat istep h
    ibranch h c2
    repeat istep h
    obtain ⟨_, e⟩ := ric_ret h
    cases e
    exact FpM.scratch m1 _ _
  · obtain ⟨_, _, _, e, _⟩ := e83_inv fork hc
    cases e

theorem e93_mem {x y z ret : B256} (fork : CoveredFork sevm.benvStat.fork) (hM : FpM fp80 96 M)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: z :: ret :: S) M G) t_3f98_c93 (.returned D)) :
    FpM fp80 160 D.memory := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  ibranch h c2
  repeat istep h
  icall h hc 96 t_41da_c96
  have m1 := e96_mem fork hM hc
  obtain ⟨b1, M1, G1, e, -⟩ := e96_inv fork hc
  cases e
  clear hc
  repeat istep h
  ibranch h c3
  repeat istep h
  icall h hc 96 t_41da_c96
  have m2 := e96_mem fork m1 hc
  obtain ⟨b2, M2, G2, e, -⟩ := e96_inv fork hc
  cases e
  clear hc
  repeat istep h
  icall h hc 100 t_4163_c100
  obtain ⟨-, G3, e⟩ := e100_inv fork hc
  cases e
  clear hc
  repeat istep h
  icall h hc 99 t_4430_c99
  have m4 := e99_mem fork m2 hc
  obtain ⟨-, -, b4, M4, G4, e, -⟩ := e99_inv fork hc
  cases e
  clear hc
  repeat istep h
  icall h hc 96 t_41da_c96
  have m5 := e96_mem fork m4 hc
  obtain ⟨b5, M5, G5, e, -⟩ := e96_inv fork hc
  cases e
  clear hc
  repeat istep h
  icall h hc 98 t_43b5_c98
  obtain ⟨-, G6, e⟩ := e98_inv fork hc
  cases e
  clear hc
  repeat istep h
  icall h hc 99 t_4430_c99
  have m7 := e99_mem fork m5 hc
  obtain ⟨-, -, b7, M7, G7, e, -⟩ := e99_inv fork hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  cases e
  change FpM _ 96 M7 at m7
  have m8 := FpM.write_out m7 x
  rw [St.memory]
  rw [FpM.read64 m7]
  dsimp only
  rw [B256.toB256_toBytes, nfp80, FpM.read64 m8]
  dsimp only
  rw [B256.toB256_toBytes, nwin, nfp80, m8.read_self (by omega)]
  exact m8

theorem e37_mem {x y ret : B256} (fork : CoveredFork sevm.benvStat.fork) (hM : FpM fp80 96 M)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: ret :: S) M G) t_2fa6_c37 (.returned D)) :
    FpM fp80 160 D.memory := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  icall h hc 83 t_3f6a_c83
  have m1 := e83_mem fork hM hc
  obtain ⟨b1, M1, G1, e, -⟩ := e83_inv fork hc
  cases e
  clear hc
  repeat istep h
  ibranch h c2
  repeat istep h
  icall h hc 83 t_3f6a_c83
  have m2 := e83_mem fork m1 hc
  obtain ⟨b2, M2, G2, e, -⟩ := e83_inv fork hc
  cases e
  clear hc
  repeat istep h
  ibranch h c3
  repeat istep h
  icall h hc 93 t_3f98_c93
  have m3 := e93_mem fork m2 hc
  obtain ⟨-, -, -, -, -, -, b3, M3, G3, e, -⟩ := e93_inv fork hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  cases e
  exact m3

theorem frame_transfer_output {post : Devm} (fork : CoveredFork sevm.benvStat.fork)
    (sel : Sevm.selector sevm = 0xa9059cbb)
    (run : SFunc.Run cert.prog sevm (St b [] Mem.empty G) t_0000_c0 (.halted post)) :
    post.output = (Nat.toB256 1).toBytes := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  ibranch h c2
  iterate 4 istep h
  rw [selector_word, sel] at h
  repeat idisp h
  repeat istep h
  ibranch h c3
  repeat istep h
  icall h hc 37 t_2fa6_c37
  have m0 : FpM fp80 96 (Mem.empty.write (Bytes.toB256 [64]).toNat (Bytes.toB256 [128]).toBytes) := by
    rw [n64]; exact FpM.init _
  have m1 := e37_mem fork m0 hc
  obtain ⟨-, -, -, -, -, -, -, -, b1, M1, G1, e, -⟩ := e37_inv fork hc
  cases e
  clear hc m0
  change FpM _ 160 M1 at m1
  repeat istep h
  cases h with
  | last hl =>
    rw [(ri_return hl).1, tail_output m1 (.inr rfl)]
    rfl

/-- **Entry 46, `balanceOf(a)`'s body** (`_balanceOf`, entry 96), keeping the free-pointer image. -/
theorem e46_inv {a ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (hM : FpM fp n M)
    (run : SFunc.Run cert.prog sevm (St b (a :: ret :: S) M G) t_2adf_c46 o) :
    ∃ b' M' G', o = .returned (St b' ((Nat.toB256 (2 ^ 255 - 1) &&&
        b.getStorVal sevm.currentTarget (balSlot a.toAdr)) :: S) M' G') ∧ FpM fp n M' := by
  have h := run.cut
  clear run
  repeat istep h
  rcases ric_call (g := t_41da_c96) rfl h with ⟨_, ⟨D1, hc, h⟩ | ⟨D1, hc, _⟩⟩
  · have m1 := e96_mem fork hM hc
    obtain ⟨b', M', G', e, -⟩ := e96_inv fork hc
    cases e
    clear hc
    repeat istep h
    obtain ⟨_, e⟩ := ric_ret h
    cases e
    exact ⟨_, _, _, rfl, m1⟩
  · obtain ⟨_, _, _, e, _⟩ := e96_inv fork hc
    cases e

theorem frame_balanceOf_output {post : Devm} (fork : CoveredFork sevm.benvStat.fork)
    (sel : Sevm.selector sevm = 0x70a08231)
    (run : SFunc.Run cert.prog sevm (St b [] Mem.empty G) t_0000_c0 (.halted post)) :
    post.output = (Nat.toB256 (2 ^ 255 - 1) &&&
      b.getStorVal sevm.currentTarget (balSlot (Sevm.dataWord sevm 4).toAdr)).toBytes := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  ibranch h c2
  iterate 4 istep h
  rw [selector_word, sel] at h
  repeat idisp h
  repeat istep h
  ibranch h c3
  repeat istep h
  have m0 : FpM fp80 96 (Mem.empty.write (Bytes.toB256 [64]).toNat (Bytes.toB256 [128]).toBytes) := by
    rw [n64]; exact FpM.init _
  rcases ric_call (g := t_2adf_c46) rfl h with ⟨_, ⟨D1, hc, h⟩ | ⟨D1, hc, _⟩⟩
  · obtain ⟨b1, M1, G1, e, m1⟩ := e46_inv fork m0 hc
    cases e
    clear hc m0
    repeat istep h
    cases h with
    | last hl =>
      rw [(ri_return hl).1, tail_output m1 (.inl rfl), ff20_word, toAdr_toB256,
        show Bytes.toB256 [4] = 4 by decide]
  · obtain ⟨_, _, _, e, _⟩ := e46_inv fork m0 hc
    cases e

/-- **The implementation's `balanceOf` answer**: a successful fresh implementation frame whose
selector is `balanceOf(address)` returns the low 255 bits of the argument's packed word. -/
theorem impl_balanceOf_output {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (code : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (mem : pre.memory = Mem.empty)
    (sel : Sevm.selector sevm = 0x70a08231) :
    post.output = (Nat.toB256 (2 ^ 255 - 1) &&&
      pre.getStorVal sevm.currentTarget (balSlot (Sevm.dataWord sevm 4).toAdr)).toBytes := by
  obtain ⟨f, hf, r⟩ := lift_sound Impl.cert_check code fork run
  rw [show Impl.cert.prog[0]? = some Impl.t_0000_c0 from rfl] at hf
  cases hf
  rw [St.self stack mem] at r
  exact frame_balanceOf_output fork sel r

/-- **The implementation's `transfer` answer**: a successful fresh implementation frame whose
selector is `transfer(address,uint256)` returns the word `1`. -/
theorem impl_transfer_output {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (code : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (mem : pre.memory = Mem.empty)
    (sel : Sevm.selector sevm = 0xa9059cbb) :
    post.output = (Nat.toB256 1).toBytes := by
  obtain ⟨f, hf, r⟩ := lift_sound Impl.cert_check code fork run
  rw [show Impl.cert.prog[0]? = some Impl.t_0000_c0 from rfl] at hf
  cases hf
  rw [St.self stack mem] at r
  exact frame_transfer_output fork sel r

end Blanc.Composition.UsdcToken
