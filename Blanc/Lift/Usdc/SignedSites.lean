import Blanc.Lift.Usdc.LibSeam
import Blanc.Lift.Usdc.SignedSkip
import Blanc.Lift.DelegateCallChild
import Blanc.Lift.CopyLoopKeep
import Blanc.Lift.FreePtrSound
import Blanc.Lift.InvWalkBranchToP
import Blanc.Lift.CodeSizeWalk
import Blanc.Lift.SilentCallP

/-!
# F7a: the two signed library call sites (USDC implementation)

`_requireValidSignature` (entry 111, copy loop 117) and `permit`'s inline call (entry 8's tail, copy
loop 80, entry 9) encode `isValidSignatureNow(signer, digest, signature)` at the free pointer `p`
read just before the encoding, copy the signature with solc's word loop, and `DELEGATECALL` the
`SignatureChecker` library with input `[p, end)` and output `[p, p + 32)`.  The walk:

* the read: the step relation records `FpObs`, so `p` is a good free pointer (`fpLo ≤ p ≤ fpCap`);
* the encoding writes land at or above `p ≥ 0x80` without wrapping, so the free-pointer word and the
  signer word at `p + 4` survive (`Words`); the potential after the `MSTORE` whose window ends at
  `dst = p + 0x84` bounds `dst` by `memCap` (amendment A4), which `copy_loop_keep` needs;
* the loop and the tail mask write land at or above `dst`;
* the call: the second free-pointer read is `p` again, the library child sees calldata whose word at
  byte `4` is the cleaned signer, `LibRejects` makes its first output word zero, and the read of that
  word sends the frame down the reverting arm.

The common shape is stated once over parametric trees (`encTree`, `exitTree`, `maskTree`,
`callTree`, `callTree2`, `callTree3`); each site is the instance by `rfl`.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.FreePtr

/-! ## The common trees -/

/-- From the free-pointer read to the copy loop head `L`. -/
def encTree (L : SFunc) : SFunc := (.next (.push [0x40] (by decide)) (.next (.reg .mload) (.next (.reg (.dup 4)) (.next (.push [0xff, 0xff, 0xff, 0xff] (by decide)) (.next (.reg .and) (.next (.push [0xe0] (by decide)) (.next (.reg .shl) (.next (.reg (.dup 1)) (.next (.reg .mstore) (.next (.push [0x04] (by decide)) (.next (.reg .add) (.next (.reg (.dup 0)) (.next (.reg (.dup 4)) (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)) (.next (.reg .and) (.next (.reg (.dup 1)) (.next (.reg .mstore) (.next (.push [0x20] (by decide)) (.next (.reg .add) (.next (.reg (.dup 3)) (.next (.reg (.dup 1)) (.next (.reg .mstore) (.next (.push [0x20] (by decide)) (.next (.reg .add) (.next (.reg (.dup 0)) (.next (.push [0x20] (by decide)) (.next (.reg .add) (.next (.reg (.dup 2)) (.next (.reg (.dup 1)) (.next (.reg .sub) (.next (.reg (.dup 2)) (.next (.reg .mstore) (.next (.reg (.dup 3)) (.next (.reg (.dup 1)) (.next (.reg (.dup 1)) (.next (.reg .mload) (.next (.reg (.dup 1)) (.next (.reg .mstore) (.next (.push [0x20] (by decide)) (.next (.reg .add) (.next (.reg (.swap 1)) (.next (.reg .pop) (.next (.reg (.dup 0)) (.next (.reg .mload) (.next (.reg (.swap 0)) (.next (.push [0x20] (by decide)) (.next (.reg .add) (.next (.reg (.swap 0)) (.next (.reg (.dup 0)) (.next (.reg (.dup 3)) (.next (.reg (.dup 3)) (.next (.push [0x00] (by decide)) L))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- solc's tail mask write after the copy, then `E`. -/
def maskTree (E : SFunc) : SFunc := (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .sub) (.next (.reg (.dup 0)) (.next (.reg .mload) (.next (.push [0x01] (by decide)) (.next (.reg (.dup 3)) (.next (.push [0x20] (by decide)) (.next (.reg .sub) (.next (.push [0x01, 0x00] (by decide)) (.next (.reg .exp) (.next (.reg .sub) (.next (.reg .not) (.next (.reg .and) (.next (.reg (.dup 1)) (.next (.reg .mstore) (.next (.push [0x20] (by decide)) (.next (.reg .add) (.next (.reg (.swap 1)) (.next (.reg .pop) E))))))))))))))))))))

/-- The copy loop's exit: the end pointer, and the tail mask unless the length is word aligned. -/
def exitTree (m0 m1 : UInt8) (k2 : Nat) (E : SFunc) : SFunc := (.dest (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg (.dup 1)) (.next (.reg .add) (.next (.reg (.swap 0)) (.next (.push [0x1f] (by decide)) (.next (.reg .and) (.next (.reg (.dup 0)) (.next (.reg .iszero) (.next (.push [m0, m1] (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
      Nat.reduceLeDiff])) (.branchTo (maskTree E) k2)))))))))))))))))

/-- After the library call succeeded: the return-data length guard, then the result word read. -/
def callTree3 (c0 c1 : UInt8) (R3 F : SFunc) : SFunc := (.dest (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x40] (by decide)) (.next (.reg .mload) (.next (.reg .returndatasize) (.next (.push [0x20] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.reg .iszero) (.next (.push [c0, c1] (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
      Nat.reduceLeDiff])) (.branch R3 (.dest (.next (.reg .pop) (.next (.reg .mload) F)))))))))))))))))

/-- The library `DELEGATECALL` and its flag check. -/
def callTree2 (b0 b1 c0 c1 : UInt8) (R2 R3 F : SFunc) : SFunc := (.dest (.next (.reg .pop) (.next (.reg .gas) (.next (.exec .delegatecall) (.next (.reg .iszero) (.next (.reg (.dup 0)) (.next (.reg .iszero) (.next (.push [b0, b1] (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
      Nat.reduceLeDiff])) (.branch R2 (callTree3 c0 c1 R3 F))))))))))

/-- The call site entry: the second free-pointer read, the call operands, the library code check. -/
def callTree (a0 a1 b0 b1 c0 c1 : UInt8) (R1 R2 R3 F : SFunc) : SFunc := (.dest (.next (.reg .pop) (.next (.reg (.swap 4)) (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x20] (by decide)) (.next (.push [0x40] (by decide)) (.next (.reg .mload) (.next (.reg (.dup 0)) (.next (.reg (.dup 3)) (.next (.reg .sub) (.next (.reg (.dup 1)) (.next (.reg (.dup 6)) (.next (.reg (.dup 0)) (.next (.reg .extcodesize) (.next (.reg .iszero) (.next (.reg (.dup 0)) (.next (.reg .iszero) (.next (.push [a0, a1] (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
      Nat.reduceLeDiff])) (.branch R1 (callTree2 b0 b1 c0 c1 R2 R3 F))))))))))))))))))))))))

/-! ## The two sites are instances -/

theorem t111_enc : Impl.t_4eb4_c111 = .dest (.next (.reg (.dup 4))
    (encTree (copyLoopTree 0x4f 0x23 0x4f 0x0b 117 Impl.t_4f23_c117))) := rfl

theorem t117_loop : Impl.t_4f0b_c117 = copyLoopTree 0x4f 0x23 0x4f 0x0b 117 Impl.t_4f23_c117 := rfl

theorem t117_exit : Impl.t_4f23_c117 = exitTree 0x4f 0x50 11 Impl.t_4f50_c11 := rfl

theorem t11_call : Impl.t_4f50_c11 = callTree 0x4f 0x6f 0x4f 0x83 0x4f 0x99 Impl.t_4f6b_c11
    Impl.t_4f7a_c11 Impl.t_4f95_c11 (.next (.push [0x34, 0x93] (by decide))
      (.branchTo Impl.t_4fa0_c11 4)) := rfl

theorem t8_enc : Impl.t_47d3_c8 = .dest (.next (.reg (.swap 0)) (.next (.reg .pop)
    (.next (.push [0x80, 0x0c, 0x32, 0xea, 0xa2, 0xa6, 0xc9, 0x3c, 0xf4, 0xcb, 0x51, 0x79, 0x44, 0x50,
      0xed, 0x77, 0xfb, 0xfb, 0xb1, 0x72] (by decide))
    (.next (.push [0x6c, 0xce, 0xa6, 0x52] (by decide)) (.next (.reg (.dup 7)) (.next (.reg (.dup 3))
    (.next (.reg (.dup 5)) (encTree (copyLoopTree 0x48 0x60 0x48 0x48 80 Impl.t_4860_c80))))))))) := rfl

theorem t80_loop : Impl.t_4848_c80 = copyLoopTree 0x48 0x60 0x48 0x48 80 Impl.t_4860_c80 := rfl

theorem t80_exit : Impl.t_4860_c80 = exitTree 0x48 0x8d 9 Impl.t_488d_c9 := rfl

theorem t9_call : Impl.t_488d_c9 = callTree 0x48 0xac 0x48 0xc0 0x48 0xd6 Impl.t_48a8_c9
    Impl.t_48b7_c9 Impl.t_48d2_c9 (.next (.push [0x49, 0x43] (by decide))
      (.branch Impl.t_48dd_c9 Impl.t_4943_c9)) := rfl

/-! ## The walk -/

/-- What the step relation of a signed-site walk records: the step, the potential before and after,
and the free-pointer observation (`FpStep (PotStep (StepIn R))` has all four). -/
def SiteStep (P : Sevm → Devm → Ninst → Devm → Prop) : Prop :=
  ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d' ∧ Pot d ∧ Pot d' ∧ FpObs d n

theorem siteStep_fp {R : Exec.Deriv} : SiteStep (FpStep (PotStep (StepIn R))) :=
  fun h => ⟨StepIn.toRun h.1.1, h.1.2.1, h.1.2.2, h.2⟩

set_option hygiene false in
/-- One straight-line step of a signed-site walk (`stepX` instructions and `JUMPDEST`). -/
macro "sx " h:ident : tactic => `(tactic|
  first
  | (have h' := ric_destP $h; clear $h; obtain ⟨_, $h:ident⟩ := h')
  | (have h' := ric_nextP $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
     obtain ⟨_, e⟩ := ri_stepX ‹CoveredFork _› (hP hd).1 rfl
     try dsimp only [List.set, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at e
     subst e; clear hd))

set_option hygiene false in
/-- One nonstorage step of a signed-site walk (`stepX` instructions and `JUMPDEST`). -/
macro "sx_nonstorage " h:ident : tactic => `(tactic|
  first
  | (have h' := ric_destP $h; clear $h; obtain ⟨_, $h:ident⟩ := h')
  | (have h' := ric_nextP $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
     obtain ⟨_, e⟩ := ri_stepX_nonstorage (by intro same; cases same)
       (by intro same; cases same) (hP hd).1 rfl
     try dsimp only [List.set, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at e
     subst e; clear hd))

set_option hygiene false in
/-- One step of a signed-site walk by an `ri_*` inversion `t` outside `stepX`. -/
macro "sop " h:ident " => " t:term : tactic => `(tactic|
  (have h' := ric_nextP $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
   obtain ⟨_, e⟩ := $t (hP hd).1; subst e; clear hd))

/-- A read extension keeps the bytes (`Mem.extend` only grows the logical size). -/
theorem memWord_read_snd (M : Mem) (o i n : Nat) : memWord (M.read i n).2 o = memWord M o := rfl

/-- A read of `n > 0` bytes at `i` extends the logical size past `i + n`. -/
theorem read_size_ge (M : Mem) {i n : Nat} (hn : 0 < n) : i + n ≤ (M.read i n).2.size := by
  show i + n ≤ memExtSize M.size i n
  unfold memExtSize ceilDiv
  rw [ite_eq_right (by omega)]
  split_ifs <;> omega

/-- **After a successful library call**: the return-data guard, then the read of the result word at
the free pointer; a zero word sends the frame down `F`'s failing arm. -/
theorem tail3_false_nonstorage {P : Sevm → Devm → Ninst → Devm → Prop} (hP : SiteStep P) {fs : List SFunc}
    {sevm : Sevm} {C : List Nat} {c0 c1 : UInt8} {R3 F : SFunc} (h3 : R3.noOk = true)
    (hF : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg},
      ¬ SFunc.RunCutP P fs sevm C (St b (0 :: S) M G) F r)
    {b : Devm} {x0 x1 x2 x3 p : B256} {R : List B256}
    {M : Mem} {G : Nat} {r : Seg} (h64 : memWord M 64 = p)
    (hpw : memWord M p.toNat = 0)
    (run : SFunc.RunCutP P fs sevm C (St b (x0 :: x1 :: x2 :: x3 :: R) M G) (callTree3 c0 c1 R3 F)
      r) : False := by
  unfold callTree3 at run
  iterate 7 sx_nonstorage run
  rw [lit64] at run
  obtain ⟨_, hd, run⟩ := ric_nextP run
  obtain ⟨_, e⟩ := ri_returndatasize (hP hd).1
  subst e
  iterate 5 sx_nonstorage run
  rcases ric_branchP run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact SFunc.RunCutP.false_of_noOk run h3
  iterate 3 sx_nonstorage run
  have hw : Bytes.toB256 (((M.read 64 32).2).read (Bytes.toB256 (M.read 64 32).1).toNat 32).1 = 0 := by
    have e1 : Bytes.toB256 (M.read 64 32).1 = p := h64
    rw [e1]
    exact (memWord_read_snd _ _ _ _).trans hpw
  rw [hw] at run
  exact hF run

/-- The original covered-fork interface to the nonstorage result-word tail. -/
theorem tail3_false {P : Sevm → Devm → Ninst → Devm → Prop} (hP : SiteStep P) {fs : List SFunc}
    {sevm : Sevm} {C : List Nat} {c0 c1 : UInt8} {R3 F : SFunc} (h3 : R3.noOk = true)
    (hF : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg},
      ¬ SFunc.RunCutP P fs sevm C (St b (0 :: S) M G) F r)
    (hfork : CoveredFork sevm.benvStat.fork) {b : Devm} {x0 x1 x2 x3 p : B256} {R : List B256}
    {M : Mem} {G : Nat} {r : Seg} (h64 : memWord M 64 = p)
    (hpw : memWord M p.toNat = 0)
    (run : SFunc.RunCutP P fs sevm C (St b (x0 :: x1 :: x2 :: x3 :: R) M G) (callTree3 c0 c1 R3 F)
      r) : False := by
  have _ := hfork
  exact tail3_false_nonstorage hP h3 hF h64 hpw run

/-- A write keeps every word its window misses (below the old size). -/
theorem memWord_write_off {μ : Mem} {o n : Nat} {ys : Bytes} (h : o + 32 ≤ μ.size)
    (hd : o + 32 ≤ n ∨ n + ys.length ≤ o) : memWord (μ.write n ys) o = memWord μ o :=
  memWord_congr fun j _ => (Mem.write_agree μ n ys).2 _ (by omega) (by omega)

/-- The library address is no precompile under any actual fork. -/
theorem usdcLib_not_precompile_any (fork : Fork) :
    ¬ (Fork.ruleSet fork).isPrecomp usdcLib := by
  cases fork <;> decide

/-- Covered-fork projection of the actual fixed-address exclusion. -/
theorem usdcLib_not_precompile {fork : Fork} (covered : CoveredFork fork) :
    ¬ (Fork.ruleSet fork).isPrecomp usdcLib := by
  have _ := covered
  exact usdcLib_not_precompile_any fork

/-- The word at byte `4` of a read window of at least 36 bytes. -/
theorem read_word4 (M : Mem) {q n : Nat} (hn : 36 ≤ n) :
    Bytes.toB256 ((M.read q n).1.sliceD 4 32 0) = memWord M (q + 4) := by
  unfold memWord
  rw [(Mem.reads_data M).read, (Mem.reads_data M).read, Bytes.sliceD_sliceD_of_le _ _ _ _ _ hn]

/-- **The library `DELEGATECALL` of a signed site**: with the free pointer `q` at the free-pointer
word and the Pair's address at `q + 4`, the library child (if it succeeds) returns the zero word,
which the call writes at `q`; either way the frame cannot succeed. -/
theorem tail2_false_noStateGas {P : Sevm → Devm → Ninst → Devm → Prop} (hP : SiteStep P) {fs : List SFunc}
    {sevm : Sevm} {C : List Nat} {b0 b1 c0 c1 : UInt8} {R2 R3 F : SFunc} (h2 : R2.noOk = true)
    (h3 : R3.noOk = true)
    (hF : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg},
      ¬ SFunc.RunCutP P fs sevm C (St b (0 :: S) M G) F r)
    (hsg : sevm.benvStat.rules.stateGas = none) {pair : Adr} (rejects : LibRejectsAt pair sevm)
    (notPre : ¬ sevm.benvStat.rules.isPrecomp pair) {b : Devm} {x q n os E y z : B256}
    {R : List B256} {M : Mem} {G : Nat} {r : Seg} (hlib : b.getCode usdcLib = Lib.code)
    (hpair : b.getCode pair = UniswapV2Pair.code) (h64 : memWord M 64 = q) (hq : 128 ≤ q.toNat)
    (hsig : memWord M (q.toNat + 4) = pair.toB256) (hsz : q.toNat + 36 ≤ M.size)
    (hn : 36 ≤ n.toNat) (hos : os.toNat = 32)
    (run : SFunc.RunCutP P fs sevm C
      (St b (x :: usdcLib.toB256 :: q :: n :: q :: os :: E :: y :: z :: R) M G)
      (callTree2 b0 b1 c0 c1 R2 R3 F) r) : False := by
  unfold callTree2 at run
  iterate 2 sx_nonstorage run
  obtain ⟨_, hd, run⟩ := ric_nextP run
  obtain ⟨_, _, e⟩ := ri_gas (hP hd).1
  subst e
  clear hd
  obtain ⟨d, hd, run⟩ := ric_nextP run
  have hcodeW : b.getCode usdcLib.toB256.toAdr = Lib.code := by rw [usdcLib_word]; exact hlib
  obtain ⟨flag, hst, hcase⟩ := ri_delegatecall_child_noStateGas hsg (by rw [hcodeW]; exact lib_undelegated)
    (by rw [usdcLib_word]; exact usdcLib_not_precompile_any sevm.benvStat.fork) (hP hd).1
  clear hd
  rw [St.self hst rfl] at run
  iterate 4 sx_nonstorage run
  rcases ric_branchP run with ⟨-, _, run⟩ | ⟨hw, _, run⟩
  · exact SFunc.RunCutP.false_of_noOk run h2
  rcases hcase with rfl | ⟨csevm, cpre, out, ⟨ex⟩, hcode, hdata, hstat, hmem0, hstk0, hgc, hmem⟩
  · exact hw (by decide)
  obtain ⟨hlen, hzero⟩ := rejects hstat ex (by rw [hcode, hcodeW]) hmem0 hstk0
    (by rw [hdata, read_word4 M hn]; exact hsig) (by rw [hgc]; exact hpair)
    (by rw [hstat]; exact notPre)
  have htake : out.output.take os.toNat = (0 : B256).toBytes := by
    have hl : (out.output.takeD 32 0).length = 32 := List.takeD_length _ _ _
    rw [hos, ← List.takeD_eq_take _ hlen, ← hzero, Bytes.toBytes_toB256_of_length hl]
  rw [htake] at hmem
  have hsz' : q.toNat + 36 ≤ (M.extends [(q.toNat, n.toNat), (q.toNat, os.toNat)]).size :=
    le_trans hsz (memExtsSize_ge _ _)
  refine tail3_false_nonstorage hP h3 hF (M := d.memory) (p := q) ?_ ?_ run
  · rw [hmem, memWord_write_off (by omega) (.inl (by omega))]
    exact h64
  · rw [hmem]
    exact (Mem.memWord_write_word _ _ _).1

/-- Covered-fork projection using rejection restricted to the same environment. -/
theorem tail2_false {P : Sevm → Devm → Ninst → Devm → Prop} (hP : SiteStep P) {fs : List SFunc}
    {sevm : Sevm} {C : List Nat} {b0 b1 c0 c1 : UInt8} {R2 R3 F : SFunc} (h2 : R2.noOk = true)
    (h3 : R3.noOk = true)
    (hF : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg},
      ¬ SFunc.RunCutP P fs sevm C (St b (0 :: S) M G) F r)
    (hfork : CoveredFork sevm.benvStat.fork) {pair : Adr} (rejects : LibRejects pair)
    (notPre : ¬ sevm.benvStat.rules.isPrecomp pair) {b : Devm} {x q n os E y z : B256}
    {R : List B256} {M : Mem} {G : Nat} {r : Seg} (hlib : b.getCode usdcLib = Lib.code)
    (hpair : b.getCode pair = UniswapV2Pair.code) (h64 : memWord M 64 = q) (hq : 128 ≤ q.toNat)
    (hsig : memWord M (q.toNat + 4) = pair.toB256) (hsz : q.toNat + 36 ≤ M.size)
    (hn : 36 ≤ n.toNat) (hos : os.toNat = 32)
    (run : SFunc.RunCutP P fs sevm C
      (St b (x :: usdcLib.toB256 :: q :: n :: q :: os :: E :: y :: z :: R) M G)
      (callTree2 b0 b1 c0 c1 R2 R3 F) r) : False :=
  tail2_false_noStateGas hP h2 h3 hF hfork.rules_stateGas_none
    (rejects.at_of_covered hfork) notPre hlib hpair h64 hq hsig hsz hn hos run

/-- **A signed call site from its entry** (`callTree`, entry 11 / entry 9): the end pointer `E`
lies at least 36 bytes above the free pointer `p`, and the Pair's address is at `p + 4`. -/
theorem tail1_falseH {P : Sevm → Devm → Ninst → Devm → Prop} (hP : SiteStep P) {fs : List SFunc}
    {sevm : Sevm} {C : List Nat} {a0 a1 b0 b1 c0 c1 : UInt8} {R1 R2 R3 F : SFunc}
    (h1 : R1.noOk = true) (h2 : R2.noOk = true) (h3 : R3.noOk = true)
    (hF : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg},
      ¬ SFunc.RunCutP P fs sevm C (St b (0 :: S) M G) F r)
    (hsg : sevm.benvStat.rules.stateGas = none) (bal : sevm.benvStat.rules.bal = none) {pair : Adr} (rejects : LibRejectsAt pair sevm)
    (notPre : ¬ sevm.benvStat.rules.isPrecomp pair) {b : Devm}
    {x E w0 w1 w2 w3 w4 sel p : B256} {R : List B256} {M : Mem} {G : Nat} {r : Seg}
    (hlib : b.getCode usdcLib = Lib.code) (hpair : b.getCode pair = UniswapV2Pair.code)
    (h64 : memWord M 64 = p) (hp : 128 ≤ p.toNat) (hsig : memWord M (p.toNat + 4) = pair.toB256)
    (hsz : p.toNat + 36 ≤ M.size) (hE : p.toNat + 36 ≤ E.toNat)
    (run : SFunc.RunCutP P fs sevm C
      (St b (x :: E :: w0 :: w1 :: w2 :: w3 :: w4 :: sel :: usdcLib.toB256 :: R) M G)
      (callTree a0 a1 b0 b1 c0 c1 R1 R2 R3 F) r) : False := by
  unfold callTree at run
  iterate 11 sx_nonstorage run
  rw [lit64, show Bytes.toB256 (M.read 64 32).1 = p from h64] at run
  iterate 6 sx_nonstorage run
  obtain ⟨_, hd, run⟩ := ric_nextP run
  obtain ⟨_, e⟩ := ri_extcodesizeH bal (hP hd).1
  subst e
  clear hd
  iterate 4 sx_nonstorage run
  rcases ric_branchP run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact SFunc.RunCutP.false_of_noOk run h1
  have hgc : ∀ a, (accountAccessH sevm b (usdcLib.toB256).toAdr).getCode a = b.getCode a :=
    fun a => by
      show (accountAccessH sevm b _).state.getCode a = b.state.getCode a
      rw [accountAccessH_state]
  have hsz96 : 96 ≤ M.size := by omega
  refine tail2_false_noStateGas hP h2 h3 hF hsg rejects notPre (by rw [hgc]; exact hlib)
    (by rw [hgc]; exact hpair) ?_ hp ?_ ?_ ?_ (by decide) run
  · exact h64
  · exact hsig
  · exact le_trans hsz (Mem.read_agree (b := default) (S := []) (G := 0) M 64 32 0 0).1
  · rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr (by omega))]
    omega

/-- The original covered-fork call-site entry interface. -/
theorem tail1_false {P : Sevm → Devm → Ninst → Devm → Prop} (hP : SiteStep P) {fs : List SFunc}
    {sevm : Sevm} {C : List Nat} {a0 a1 b0 b1 c0 c1 : UInt8} {R1 R2 R3 F : SFunc}
    (h1 : R1.noOk = true) (h2 : R2.noOk = true) (h3 : R3.noOk = true)
    (hF : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg},
      ¬ SFunc.RunCutP P fs sevm C (St b (0 :: S) M G) F r)
    (hfork : CoveredFork sevm.benvStat.fork) {pair : Adr} (rejects : LibRejects pair)
    (notPre : ¬ sevm.benvStat.rules.isPrecomp pair) {b : Devm}
    {x E w0 w1 w2 w3 w4 sel p : B256} {R : List B256} {M : Mem} {G : Nat} {r : Seg}
    (hlib : b.getCode usdcLib = Lib.code) (hpair : b.getCode pair = UniswapV2Pair.code)
    (h64 : memWord M 64 = p) (hp : 128 ≤ p.toNat) (hsig : memWord M (p.toNat + 4) = pair.toB256)
    (hsz : p.toNat + 36 ≤ M.size) (hE : p.toNat + 36 ≤ E.toNat)
    (run : SFunc.RunCutP P fs sevm C
      (St b (x :: E :: w0 :: w1 :: w2 :: w3 :: w4 :: sel :: usdcLib.toB256 :: R) M G)
      (callTree a0 a1 b0 b1 c0 c1 R1 R2 R3 F) r) : False :=
  tail1_falseH hP h1 h2 h3 hF hfork.rules_stateGas_none hfork.rules_bal_none
    (rejects.at_of_covered hfork) notPre hlib hpair h64 hp hsig hsz hE run

/-- **The copy loop's exit**: from the loop's exit state (`len = L`, destination `dst`, both below
`memCap`, `dst` at least 36 bytes above the free pointer), the tail mask write lands at or above
`dst`, and both arms reach the call site with an end pointer at or above `dst`. -/
theorem tail0_falseH {P : Sevm → Devm → Ninst → Devm → Prop} (hP : SiteStep P) {fs : List SFunc}
    {sevm : Sevm} {C : List Nat} {m0 m1 a0 a1 b0 b1 c0 c1 : UInt8} {k2 : Nat}
    {R1 R2 R3 F : SFunc}
    (hk2 : fs[k2]? = some (callTree a0 a1 b0 b1 c0 c1 R1 R2 R3 F)) (hk2C : k2 ∉ C)
    (h1 : R1.noOk = true) (h2 : R2.noOk = true) (h3 : R3.noOk = true)
    (hF : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg},
      ¬ SFunc.RunCutP P fs sevm C (St b (0 :: S) M G) F r)
    (hsg : sevm.benvStat.rules.stateGas = none) (bal : sevm.benvStat.rules.bal = none) {pair : Adr} (rejects : LibRejectsAt pair sevm)
    (notPre : ¬ sevm.benvStat.rules.isPrecomp pair) {b : Devm}
    {i s1 s2 s3 L s5 dst w0 w1 w2 w3 w4 sel p : B256} {R : List B256} {M : Mem} {G : Nat}
    {r : Seg} (hlib : b.getCode usdcLib = Lib.code) (hpair : b.getCode pair = UniswapV2Pair.code)
    (h64 : memWord M 64 = p) (hp : 128 ≤ p.toNat) (hsig : memWord M (p.toNat + 4) = pair.toB256)
    (hsz : p.toNat + 36 ≤ M.size) (hdst : p.toNat + 36 ≤ dst.toNat) (hdcap : dst.toNat ≤ memCap)
    (hL : L.toNat ≤ memCap)
    (run : SFunc.RunCutP P fs sevm C
      (St b (i :: s1 :: s2 :: s3 :: L :: s5 :: dst :: w0 :: w1 :: w2 :: w3 :: w4 :: sel ::
        usdcLib.toB256 :: R) M G)
      (exitTree m0 m1 k2 (callTree a0 a1 b0 b1 c0 c1 R1 R2 R3 F)) r) : False := by
  unfold exitTree at run
  iterate 16 sx_nonstorage run
  have hE : (L + dst).toNat = L.toNat + dst.toNat :=
    add_toNat_small (by unfold memCap at hdcap hL; omega)
  rcases ric_branchToP hk2C hk2 run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · unfold maskTree at run
    iterate 10 sx_nonstorage run
    obtain ⟨_, hd, run⟩ := ric_nextP run
    obtain ⟨_, e⟩ := ri_exp (hP hd).1
    subst e
    clear hd
    iterate 9 sx_nonstorage run
    have hX : (Bytes.toB256 [31] &&& L).toNat ≤ L.toNat := by
      rw [B256.toNat_and]
      exact Nat.and_le_right
    generalize Bytes.toB256 [31] &&& L = X at hX run
    have ha : (L + dst - X).toNat = L.toNat + dst.toNat - X.toNat := by
      rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr (by omega)), hE]
    generalize L + dst - X = a at ha run
    have ha32 : (Bytes.toB256 [32] + a).toNat = 32 + a.toNat :=
      add_toNat_small (by rw [lit32]; unfold memCap at hdcap hL; omega)
    have hrs := (Mem.read_agree (b := default) (S := []) (G := 0) M a.toNat 32 0 0).1
    have h64' := (memWord_read_snd M _ a.toNat 32).trans h64
    have hsig' := (memWord_read_snd M _ a.toNat 32).trans hsig
    generalize (M.read a.toNat 32).2 = M1 at hrs run h64' hsig'
    refine tail1_falseH hP h1 h2 h3 hF hsg bal rejects notPre hlib hpair ?_ hp ?_ ?_ (by omega) run
    · rw [memWord_write_off (by omega) (.inl (by omega))]
      exact h64'
    · rw [memWord_write_off (by omega) (.inl (by omega))]
      exact hsig'
    · exact le_trans hsz (le_trans hrs (Mem.write_agree _ _ _).1)
  · exact tail1_falseH hP h1 h2 h3 hF hsg bal rejects notPre hlib hpair h64 hp hsig hsz
      (by omega) run

/-- The original covered-fork exit-tree interface. -/
theorem tail0_false {P : Sevm → Devm → Ninst → Devm → Prop} (hP : SiteStep P) {fs : List SFunc}
    {sevm : Sevm} {C : List Nat} {m0 m1 a0 a1 b0 b1 c0 c1 : UInt8} {k2 : Nat}
    {R1 R2 R3 F : SFunc}
    (hk2 : fs[k2]? = some (callTree a0 a1 b0 b1 c0 c1 R1 R2 R3 F)) (hk2C : k2 ∉ C)
    (h1 : R1.noOk = true) (h2 : R2.noOk = true) (h3 : R3.noOk = true)
    (hF : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg},
      ¬ SFunc.RunCutP P fs sevm C (St b (0 :: S) M G) F r)
    (hfork : CoveredFork sevm.benvStat.fork) {pair : Adr} (rejects : LibRejects pair)
    (notPre : ¬ sevm.benvStat.rules.isPrecomp pair) {b : Devm}
    {i s1 s2 s3 L s5 dst w0 w1 w2 w3 w4 sel p : B256} {R : List B256} {M : Mem} {G : Nat}
    {r : Seg} (hlib : b.getCode usdcLib = Lib.code) (hpair : b.getCode pair = UniswapV2Pair.code)
    (h64 : memWord M 64 = p) (hp : 128 ≤ p.toNat) (hsig : memWord M (p.toNat + 4) = pair.toB256)
    (hsz : p.toNat + 36 ≤ M.size) (hdst : p.toNat + 36 ≤ dst.toNat) (hdcap : dst.toNat ≤ memCap)
    (hL : L.toNat ≤ memCap)
    (run : SFunc.RunCutP P fs sevm C
      (St b (i :: s1 :: s2 :: s3 :: L :: s5 :: dst :: w0 :: w1 :: w2 :: w3 :: w4 :: sel ::
        usdcLib.toB256 :: R) M G)
      (exitTree m0 m1 k2 (callTree a0 a1 b0 b1 c0 c1 R1 R2 R3 F)) r) : False :=
  tail0_falseH hP hk2 hk2C h1 h2 h3 hF hfork.rules_stateGas_none hfork.rules_bal_none
    (rejects.at_of_covered hfork) notPre hlib hpair h64 hp hsig hsz hdst hdcap hL run

/-- A literal plus a word that does not overflow. -/
theorem lit_add {xs : Bytes} {c : Nat} {y : B256} (hx : (Bytes.toB256 xs).toNat = c)
    (h : c + y.toNat < 2 ^ 256) : (Bytes.toB256 xs + y).toNat = c + y.toNat := by
  rw [add_toNat_small (by rw [hx]; exact h), hx]

/-- The two words a signed site keeps from the encoding to the call: the free pointer `p` at the
free-pointer word and `s` at `p + 4`, both below the logical size. -/
structure Words (p s : B256) (μ : Mem) : Prop where
  fp : memWord μ 64 = p
  sg : memWord μ (p.toNat + 4) = s
  sz : p.toNat + 36 ≤ μ.size

theorem Words.write {p s : B256} {μ : Mem} (h : Words p s μ) (hp : 128 ≤ p.toNat) {n : Nat}
    (hn : p.toNat + 36 ≤ n) (ys : Bytes) : Words p s (μ.write n ys) :=
  ⟨by rw [memWord_write_off (by have := h.sz; omega) (.inl (by omega))]; exact h.fp,
    by rw [memWord_write_off (by have := h.sz; omega) (.inl (by omega))]; exact h.sg,
    le_trans h.sz (Mem.write_agree μ n ys).1⟩

theorem Words.read {p s : B256} {μ : Mem} (h : Words p s μ) (i n : Nat) :
    Words p s (μ.read i n).2 :=
  ⟨h.fp, h.sg, le_trans h.sz (Mem.read_agree (b := default) (S := []) (G := 0) μ i n 0 0).1⟩

theorem Words.agree {p s : B256} {μ μ' : Mem} (h : Words p s μ) {lo hi : Nat}
    (hag : Mem.AgreeOutside μ μ' lo hi) (hlo : p.toNat + 36 ≤ lo) (hp : 128 ≤ p.toNat) :
    Words p s μ' := by
  have hsz := h.sz
  refine ⟨?_, ?_, le_trans h.sz hag.1⟩
  · rw [memWord_congr (μ := μ) (fun j hj => hag.2 _ (by omega) (.inl (by omega)))]
    exact h.fp
  · rw [memWord_congr (μ := μ) (fun j hj => hag.2 _ (by omega) (.inl (by omega)))]
    exact h.sg

/-- Name the memory of a walk state. -/
theorem nameMem {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc}
    {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {f : SFunc}
    {r : Seg} (run : SFunc.RunCutP P fs sevm C (St b S M G) f r) :
    ∃ M', M' = M ∧ SFunc.RunCutP P fs sevm C (St b S M' G) f r := ⟨M, rfl, run⟩

/-- **A signed site from the free-pointer read** (`encTree`): the read sees a good free pointer
`p`, the encoding writes `isValidSignatureNow(signer, h, sig)`'s head at `p`, the loop copies the
signature to `dst = p + 0x84`, and the call site is reached with the cleaned signer at `p + 4`. -/
theorem enc_falseH {P : Sevm → Devm → Ninst → Devm → Prop} (hP : SiteStep P) {fs : List SFunc}
    {sevm : Sevm} {C : List Nat} {e0 e1 r0 r1 m0 m1 a0 a1 b0 b1 c0 c1 : UInt8} {k k2 : Nat}
    {R1 R2 R3 F : SFunc}
    (hk : fs[k]? = some (copyLoopTree e0 e1 r0 r1 k
      (exitTree m0 m1 k2 (callTree a0 a1 b0 b1 c0 c1 R1 R2 R3 F)))) (hkC : k ∉ C)
    (hk2 : fs[k2]? = some (callTree a0 a1 b0 b1 c0 c1 R1 R2 R3 F)) (hk2C : k2 ∉ C)
    (h1 : R1.noOk = true) (h2 : R2.noOk = true) (h3 : R3.noOk = true)
    (hF : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg},
      ¬ SFunc.RunCutP P fs sevm C (St b (0 :: S) M G) F r)
    (hsg : sevm.benvStat.rules.stateGas = none) (bal : sevm.benvStat.rules.bal = none) {pair : Adr} (rejects : LibRejectsAt pair sevm)
    (notPre : ¬ sevm.benvStat.rules.isPrecomp pair) {b : Devm} {sig h signer sel : B256}
    {R : List B256} {M : Mem} {G : Nat} {r : Seg} (hlib : b.getCode usdcLib = Lib.code)
    (hpair : b.getCode pair = UniswapV2Pair.code) (hsigner : signer.toAdr = pair)
    (run : SFunc.RunCutP P fs sevm C (St b (sig :: h :: signer :: sel :: usdcLib.toB256 :: R) M G)
      (encTree (copyLoopTree e0 e1 r0 r1 k
        (exitTree m0 m1 k2 (callTree a0 a1 b0 b1 c0 c1 R1 R2 R3 F)))) r) : False := by
  unfold encTree at run
  sx_nonstorage run
  have h' := ric_nextP run
  clear run
  obtain ⟨_, hd, run⟩ := h'
  have good := (hP hd).2.2.2 rfl (congrArg some (by decide : Bytes.toB256 [64] = 64))
  obtain ⟨_, e⟩ := ri_stepX_nonstorage (by intro same; cases same) (by intro same; cases same) (hP hd).1 rfl
  subst e
  clear hd
  rw [lit64] at run
  change FpGood (memWord M 64) at good
  have hM1 : 64 + 32 ≤ (M.read 64 32).2.size := read_size_ge M (n := 32) (by decide)
  change SFunc.RunCutP P fs sevm C (St b (memWord M 64 :: _) _ _) _ _ at run
  have h64 : memWord (M.read 64 32).2 64 = memWord M 64 := rfl
  generalize memWord M 64 = p at good run h64
  generalize (M.read 64 32).2 = M1 at hM1 run h64
  iterate 4 sx_nonstorage run
  sop run => ri_shl
  obtain ⟨hplo, hpcap⟩ := good
  unfold fpLo at hplo
  unfold fpCap at hpcap
  have e4 : (Bytes.toB256 [4] + p).toNat = p.toNat + 4 := by
    rw [lit_add (by decide : (Bytes.toB256 [4]).toNat = 4) (by omega)]; omega
  have e24 : (Bytes.toB256 [32] + (Bytes.toB256 [4] + p)).toNat = 36 + p.toNat := by
    rw [lit_add lit32 (by rw [e4]; omega), e4]; omega
  have e44 : (Bytes.toB256 [32] + (Bytes.toB256 [32] + (Bytes.toB256 [4] + p))).toNat =
      68 + p.toNat := by
    rw [lit_add lit32 (by rw [e24]; omega), e24]; omega
  have e64 : (Bytes.toB256 [32] + (Bytes.toB256 [32] + (Bytes.toB256 [32] +
      (Bytes.toB256 [4] + p)))).toNat = 100 + p.toNat := by
    rw [lit_add lit32 (by rw [e44]; omega), e44]; omega
  have e84 : (Bytes.toB256 [32] + (Bytes.toB256 [32] + (Bytes.toB256 [32] + (Bytes.toB256 [32] +
      (Bytes.toB256 [4] + p))))).toNat = 132 + p.toNat := by
    rw [lit_add lit32 (by rw [e64]; omega), e64]; omega
  iterate 2 sx_nonstorage run
  obtain ⟨W0, hW0, run⟩ := nameMem run
  have w0 : memWord W0 64 = p ∧ 96 ≤ W0.size := by
    rw [hW0]
    exact ⟨by rw [memWord_write_off hM1 (.inl (by omega))]; exact h64,
      le_trans hM1 (Mem.write_agree _ _ _).1⟩
  clear hW0
  iterate 8 sx_nonstorage run
  obtain ⟨W1, hW1, run⟩ := nameMem run
  have w1 : Words p (Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255] &&& signer) W1 := by
    rw [hW1, e4]
    obtain ⟨hv, hs⟩ := Mem.memWord_write_word W0 (p.toNat + 4) (Bytes.toB256 [255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] &&& signer)
    exact ⟨by rw [memWord_write_off (by omega) (.inl (by omega))]; exact w0.1,
      hv, by omega⟩
  clear hW1
  generalize hsw : (Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255] &&& signer) = sw at w1
  iterate 5 sx_nonstorage run
  obtain ⟨W2, hW2, run⟩ := nameMem run
  have w2 : Words p sw W2 := by rw [hW2, e24]; exact w1.write hplo (by omega) _
  clear hW2
  iterate 10 sx_nonstorage run
  obtain ⟨W3, hW3, run⟩ := nameMem run
  have w3 : Words p sw W3 := by rw [hW3, e44]; exact w2.write hplo (by omega) _
  clear hW3
  iterate 5 sx_nonstorage run
  have h' := ric_nextP run
  clear run
  obtain ⟨_, hd, run⟩ := h'
  have pot := (hP hd).2.2.1
  obtain ⟨_, e⟩ := ri_stepX_nonstorage (by intro same; cases same) (by intro same; cases same) (hP hd).1 rfl
  subst e
  clear hd
  obtain ⟨W5, hW5, run⟩ := nameMem run
  rw [← hW5] at pot
  have hcap : W5.size < memCap := Pot.size_lt pot
  have w5 : Words p sw W5 ∧ 132 + p.toNat ≤ W5.size := by
    rw [hW5, e64]
    exact ⟨(w3.read _ _).write hplo (by omega) _, by
      have := (Mem.memWord_write_word (W3.read sig.toNat 32).2 (100 + p.toNat)
        (Bytes.toB256 (W3.read sig.toNat 32).1)).2
      omega⟩
  clear hW5 pot
  iterate 14 sx_nonstorage run
  have hP' : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d' ∧ Pot d ∧ Pot d' :=
    fun h => ⟨(hP h).1, (hP h).2.1, (hP h).2.2.1⟩
  obtain ⟨i', M', G', hle, hi', hag, run⟩ := copy_loop_keep_nonstorage hP' hk hkC
    (by rw [show (Bytes.toB256 [0]).toNat = 0 from rfl]; exact Nat.zero_le _)
    (by rw [e84]; omega) run
  have w := (w5.1.read sig.toNat 32).agree hag (by rw [e84]; omega) hplo
  have hsw' : sw = pair.toB256 := by rw [← hsw, ff20_and_word, hsigner]
  exact tail0_falseH hP hk2 hk2C h1 h2 h3 hF hsg bal rejects notPre hlib hpair w.fp hplo
    (hsw' ▸ w.sg) w.sz (by rw [e84]; omega) (by rw [e84]; omega) (le_trans hle hi') run

/-- The original covered-fork encoding interface. -/
theorem enc_false {P : Sevm → Devm → Ninst → Devm → Prop} (hP : SiteStep P) {fs : List SFunc}
    {sevm : Sevm} {C : List Nat} {e0 e1 r0 r1 m0 m1 a0 a1 b0 b1 c0 c1 : UInt8} {k k2 : Nat}
    {R1 R2 R3 F : SFunc}
    (hk : fs[k]? = some (copyLoopTree e0 e1 r0 r1 k
      (exitTree m0 m1 k2 (callTree a0 a1 b0 b1 c0 c1 R1 R2 R3 F)))) (hkC : k ∉ C)
    (hk2 : fs[k2]? = some (callTree a0 a1 b0 b1 c0 c1 R1 R2 R3 F)) (hk2C : k2 ∉ C)
    (h1 : R1.noOk = true) (h2 : R2.noOk = true) (h3 : R3.noOk = true)
    (hF : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg},
      ¬ SFunc.RunCutP P fs sevm C (St b (0 :: S) M G) F r)
    (hfork : CoveredFork sevm.benvStat.fork) {pair : Adr} (rejects : LibRejects pair)
    (notPre : ¬ sevm.benvStat.rules.isPrecomp pair) {b : Devm} {sig h signer sel : B256}
    {R : List B256} {M : Mem} {G : Nat} {r : Seg} (hlib : b.getCode usdcLib = Lib.code)
    (hpair : b.getCode pair = UniswapV2Pair.code) (hsigner : signer.toAdr = pair)
    (run : SFunc.RunCutP P fs sevm C (St b (sig :: h :: signer :: sel :: usdcLib.toB256 :: R) M G)
      (encTree (copyLoopTree e0 e1 r0 r1 k
        (exitTree m0 m1 k2 (callTree a0 a1 b0 b1 c0 c1 R1 R2 R3 F)))) r) : False :=
  enc_falseH hP hk hkC hk2 hk2C h1 h2 h3 hF hfork.rules_stateGas_none hfork.rules_bal_none
    (rejects.at_of_covered hfork) notPre hlib hpair hsigner run

/-! ## The two sites -/

theorem libLit : Bytes.toB256 [0x80, 0x0c, 0x32, 0xea, 0xa2, 0xa6, 0xc9, 0x3c, 0xf4, 0xcb, 0x51,
    0x79, 0x44, 0x50, 0xed, 0x77, 0xfb, 0xfb, 0xb1, 0x72] = usdcLib.toB256 := by decide +kernel

/-- `_domainSeparator`'s closure (entry 78 with the `name` loop).  The same list as U6e4's `sil78`
(`RefineSignedPermitCore.lean`), which cannot be imported next to `LibReject.lean` (both declare
`Blanc.Lift.Usdc.e8_inv`). -/
def dom78 : List Nat := [6, 76, 77, 78, 106, 107]

/-- Entries 78 and 79 are silent and never halt (their closures). -/
theorem dom78_ok : SilentSet Impl.cert.prog dom78 = true ∧ NoHaltSet Impl.cert.prog dom78 = true ∧
    SilentSet Impl.cert.prog [79] = true ∧ NoHaltSet Impl.cert.prog [79] = true := by
  decide +kernel

theorem noOk_111 : Impl.t_4f6b_c11.noOk = true ∧ Impl.t_4f7a_c11.noOk = true ∧
    Impl.t_4f95_c11.noOk = true ∧ Impl.t_4fa0_c11.noOk = true := by decide

theorem noOk_9 : Impl.t_48a8_c9.noOk = true ∧ Impl.t_48b7_c9.noOk = true ∧
    Impl.t_48d2_c9.noOk = true ∧ Impl.t_48dd_c9.noOk = true := by decide

theorem prog_117 : Impl.cert.prog[117]? = some (copyLoopTree 0x4f 0x23 0x4f 0x0b 117
    (exitTree 0x4f 0x50 11 (callTree 0x4f 0x6f 0x4f 0x83 0x4f 0x99 Impl.t_4f6b_c11
      Impl.t_4f7a_c11 Impl.t_4f95_c11 (.next (.push [0x34, 0x93] (by decide))
        (.branchTo Impl.t_4fa0_c11 4))))) := by
  rw [← t11_call, ← t117_exit, ← t117_loop]
  rfl

theorem prog_11 : Impl.cert.prog[11]? = some (callTree 0x4f 0x6f 0x4f 0x83 0x4f 0x99
    Impl.t_4f6b_c11 Impl.t_4f7a_c11 Impl.t_4f95_c11 (.next (.push [0x34, 0x93] (by decide))
      (.branchTo Impl.t_4fa0_c11 4))) := by
  rw [← t11_call]
  rfl

theorem prog_80 : Impl.cert.prog[80]? = some (copyLoopTree 0x48 0x60 0x48 0x48 80
    (exitTree 0x48 0x8d 9 (callTree 0x48 0xac 0x48 0xc0 0x48 0xd6 Impl.t_48a8_c9
      Impl.t_48b7_c9 Impl.t_48d2_c9 (.next (.push [0x49, 0x43] (by decide))
        (.branch Impl.t_48dd_c9 Impl.t_4943_c9))))) := by
  rw [← t9_call, ← t80_exit, ← t80_loop]
  rfl

theorem prog_9 : Impl.cert.prog[9]? = some (callTree 0x48 0xac 0x48 0xc0 0x48 0xd6
    Impl.t_48a8_c9 Impl.t_48b7_c9 Impl.t_48d2_c9 (.next (.push [0x49, 0x43] (by decide))
      (.branch Impl.t_48dd_c9 Impl.t_4943_c9))) := by
  rw [← t9_call]
  rfl

/-- **Site 1, `_requireValidSignature` (entry 111)**: no run of the entry from its frame
`[sig, digest, signer, ret]`, under a step relation recording the potential and the free-pointer
observation, with the library at `usdcLib` and the Pair's runtime at `signer`, outside the
precompiles: the library rejects the Pair (`LibRejects`), so the frame reverts. -/
theorem site111_false {P : Sevm → Devm → Ninst → Devm → Prop} (hP : SiteStep P) {sevm : Sevm}
    (hfork : CoveredFork sevm.benvStat.fork) {pair : Adr} (rejects : LibRejects pair)
    (notPre : ¬ sevm.benvStat.rules.isPrecomp pair) {b : Devm} {sig dg signer ret : B256}
    {R : List B256} {M : Mem} {G : Nat} {o : Outcome} (hlib : b.getCode usdcLib = Lib.code)
    (hpair : b.getCode pair = UniswapV2Pair.code) (hsigner : signer.toAdr = pair)
    (run : SFunc.RunP P Impl.cert.prog sevm (St b (sig :: dg :: signer :: ret :: R) M G)
      Impl.t_4e88_c111 o) : False := by
  have hP' : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d' := fun h => (hP h).1
  have run := SFunc.runP_iff_runCutP_nil.mp run
  unfold Impl.t_4e88_c111 at run
  iterate 7 sx run
  obtain ⟨b1, Y, M1, G1, hs1, hlen, run⟩ := ricP_call_silent hP' Impl.cert_check hfork
    dom78_ok.1 dom78_ok.2.1 (k := 78) (by decide) (by decide) (e := ⟨0x4276, [.ret], 1⟩) rfl rfl
    (ρ := Bytes.toB256 [0x4e, 0xae]) run (List.Forall₂.cons rfl .nil)
  obtain ⟨y, rfl⟩ : ∃ y, Y = [y] := match Y, hlen with | [y], _ => ⟨y, rfl⟩
  unfold Impl.t_4eae_c111 at run
  iterate 3 sx run
  obtain ⟨b2, Z, M2, G2, hs2, hlen2, run⟩ := ricP_call_silent hP' Impl.cert_check hfork
    dom78_ok.2.2.1 dom78_ok.2.2.2 (k := 79) (by decide) (by decide)
    (e := ⟨0x508b, [.unk, .unk, .ret], 1⟩) rfl rfl (ρ := Bytes.toB256 [0x4e, 0xb4])
    run (List.Forall₂.cons trivial (.cons trivial (.cons rfl .nil)))
  obtain ⟨z, rfl⟩ : ∃ z, Z = [z] := match Z, hlen2 with | [z], _ => ⟨z, rfl⟩
  rw [t111_enc] at run
  iterate 2 sx run
  rw [libLit] at run
  have hgc : ∀ a, b2.getCode a = b.getCode a := fun a => by
    show b2.state.getCode a = b.state.getCode a
    rw [hs2, hs1]
  obtain ⟨n1, n2, n3, n4⟩ := noOk_111
  refine enc_false hP prog_117 (List.not_mem_nil) prog_11 (List.not_mem_nil) n1 n2 n3 ?_ hfork
    rejects notPre (by rw [hgc]; exact hlib) (by rw [hgc]; exact hpair) hsigner run
  intro b S M G r h
  iterate 1 sx h
  cases h with
  | toZero _ _ k => exact SFunc.RunCutP.false_of_noOk k n4
  | toSuccCut _ w hw _ pop => exact hw (St.of_pop2 pop).2.1.symm
  | toSucc _ w hw _ _ pop _ => exact hw (St.of_pop2 pop).2.1.symm

/-- **Site 1 at the call node**: a signed path cannot cross `callNext 111` with the Pair as the
signer (the callee's run from its frame is impossible, whether it returns or halts). -/
theorem site111_call_false {P : Sevm → Devm → Ninst → Devm → Prop} (hP : SiteStep P)
    {sevm : Sevm} (hfork : CoveredFork sevm.benvStat.fork) {pair : Adr} (rejects : LibRejects pair)
    (notPre : ¬ sevm.benvStat.rules.isPrecomp pair) {C : List Nat} {b : Devm}
    {dd sig dg signer ret : B256} {R : List B256} {M : Mem} {G : Nat} {f : SFunc} {r : Seg}
    (hlib : b.getCode usdcLib = Lib.code) (hpair : b.getCode pair = UniswapV2Pair.code)
    (hsigner : signer.toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm C
      (St b (dd :: sig :: dg :: signer :: ret :: R) M G) (.callNext 111 f) r) : False := by
  have hg : Impl.cert.prog[111]? = some Impl.t_4e88_c111 := rfl
  cases run with
  | callHalt d hget pop callee =>
    rw [hg] at hget
    cases hget
    rw [(St.of_pop1 pop).2] at callee
    exact site111_false hP hfork rejects notPre hlib hpair hsigner callee
  | callRet d hget pop callee _ =>
    rw [hg] at hget
    cases hget
    rw [(St.of_pop1 pop).2] at callee
    exact site111_false hP hfork rejects notPre hlib hpair hsigner callee

/-- **Site 2, `permit`'s inline library call** (entry 8 from `_hashTypedDataV4`'s return,
`t_47d3_c8`, copy loop 80, call site entry 9): with the digest `s0`, the signature `s2` and the
owner `s6` naming the Pair, no cut run of the node reaches anything. -/
theorem site9_falseH {P : Sevm → Devm → Ninst → Devm → Prop} (hP : SiteStep P) {sevm : Sevm}
    (hsg : sevm.benvStat.rules.stateGas = none) (bal : sevm.benvStat.rules.bal = none) {pair : Adr} (rejects : LibRejectsAt pair sevm)
    (notPre : ¬ sevm.benvStat.rules.isPrecomp pair) {C : List Nat} (h80 : 80 ∉ C) (h9 : 9 ∉ C)
    {b : Devm} {s0 s1 s2 s3 s4 s5 s6 : B256} {R : List B256} {M : Mem} {G : Nat} {r : Seg}
    (hlib : b.getCode usdcLib = Lib.code) (hpair : b.getCode pair = UniswapV2Pair.code)
    (hsigner : s6.toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm C
      (St b (s0 :: s1 :: s2 :: s3 :: s4 :: s5 :: s6 :: R) M G) Impl.t_47d3_c8 r) : False := by
  rw [t8_enc] at run
  iterate 8 sx_nonstorage run
  rw [libLit] at run
  obtain ⟨n1, n2, n3, n4⟩ := noOk_9
  refine enc_falseH hP prog_80 h80 prog_9 h9 n1 n2 n3 ?_ hsg bal rejects notPre hlib hpair hsigner run
  intro b S M G r h
  iterate 1 sx_nonstorage h
  rcases ric_branchP h with ⟨-, _, h⟩ | ⟨hw, _, _⟩
  · exact SFunc.RunCutP.false_of_noOk h n4
  · exact hw rfl

/-- The original covered-fork permit-site interface. -/
theorem site9_false {P : Sevm → Devm → Ninst → Devm → Prop} (hP : SiteStep P) {sevm : Sevm}
    (hfork : CoveredFork sevm.benvStat.fork) {pair : Adr} (rejects : LibRejects pair)
    (notPre : ¬ sevm.benvStat.rules.isPrecomp pair) {C : List Nat} (h80 : 80 ∉ C) (h9 : 9 ∉ C)
    {b : Devm} {s0 s1 s2 s3 s4 s5 s6 : B256} {R : List B256} {M : Mem} {G : Nat} {r : Seg}
    (hlib : b.getCode usdcLib = Lib.code) (hpair : b.getCode pair = UniswapV2Pair.code)
    (hsigner : s6.toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm C
      (St b (s0 :: s1 :: s2 :: s3 :: s4 :: s5 :: s6 :: R) M G) Impl.t_47d3_c8 r) : False :=
  site9_falseH hP hfork.rules_stateGas_none hfork.rules_bal_none
    (rejects.at_of_covered hfork) notPre h80 h9 hlib hpair hsigner run

end Blanc.Lift.Usdc
