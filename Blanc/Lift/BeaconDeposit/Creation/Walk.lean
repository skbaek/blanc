import Blanc.Lift.BeaconDeposit.Creation.Cert
import Blanc.Lift.BeaconDeposit.Init
import Blanc.Lift.PackedShaSize
import Blanc.Lift.WalkSteps

/-!
# The Beacon deposit constructor, walked

A gas-exact synthetic run (`SFunc.RunExactCut`) of the lifted constructor of the Beacon
deposit contract's creation input (`Creation/Cert.lean`).  The constructor

* stores the free pointer `0x80`, checks `CALLVALUE = 0`;
* for `h = 0 … 30` (the loop at entry 2, pc `0x14`): reads `zero_hashes[h]` (slot `33 + h`)
  twice, computes `sha256(abi.encodePacked(z, z))` through the SHA-256 precompile
  (`packed_sha_pairN`, the size-optimised packed-hash site; the copy loop is entry 1, pc
  `0x73`) and stores the digest to `zero_hashes[h + 1]` (slot `34 + h`);
* copies the appended runtime (6,358 bytes at offset 275) to memory and returns it.

SHA-256 stays symbolic throughout: the stored digests are `zeroHash Bytes.sha256 (h + 1)`
by definition, nothing evaluates the hash.  Gas is exact, but the start gas is only bounded
below: an iteration costs at most 30,000 whatever the warmth of its keys and the value of its
digest, so no fact about a digest's value is needed.
-/

namespace Blanc.Lift.BeaconDeposit.Creation

open Jaune Blanc.BeaconDeposit Blanc.Lift.BeaconDeposit

/-! ## The lifted program's shape -/

/-- The lifted constructor program. -/
abbrev prog : List SFunc := Cert.prog cert

/-- The copy-loop entry (entry 1) is the size-optimised packed-hash site's tail. -/
theorem prog_1 : prog[1]? = some (mcpyTreeN 0x00 0x92 0x00 0x73 1
    (mergeTreeN (shaCallTree 0x00 0xd1 0x00 0xe6 t_00c8_c1 t_00e2_c1 t_00e6_c1))) := rfl

theorem prog_2 : prog[2]? = some t_0014_c2 := rfl

/-- The first pass through the loop head, inlined in entry 0, is the loop entry's tree. -/
theorem t_0014_c0_eq : t_0014_c0 = t_0014_c2 := rfl

/-- The loop body's hashing tail, as the packed-hash site over the copy-loop entry. -/
theorem t_003b_c2_eq : t_003b_c2 = .dest (.next (.reg .add) (.next (.reg .sload)
    (pack2Tree (mcpyTreeN 0x00 0x92 0x00 0x73 1
      (mergeTreeN (shaCallTree 0x00 0xd1 0x00 0xe6 t_00c8_c1 t_00e2_c1 t_00e6_c1)))))) := rfl

/-! ## Words, storage and the loop invariant -/

/-- The free pointer at the start of iteration `i`. -/
def fp (i : Nat) : Nat := 128 + 96 * i

/-- The memory size at the start of iteration `i`. -/
def memAt (i : Nat) : Nat := if i = 0 then 96 else fp i + 96

/-- The constructor's storage after `i` iterations: `zero_hashes[j] = zeroHash sha256 j` at
slot `33 + j` for `j ≤ i`, every other slot zero. -/
def CtorStor (i : Nat) (s : Stor) : Prop :=
  ∀ x : B256, s.get x =
    if 33 ≤ x.toNat ∧ x.toNat ≤ 33 + i then zeroHash Bytes.sha256 (x.toNat - 33) else 0

/-- The frame facts the walk needs of the creation frame. -/
structure CtorFrame (sevm : Sevm) : Prop where
  pre : decide (sevm.benvStat.rules.isPrecomp 2) = true
  fork : CoveredFork sevm.benvStat.fork
  depth : sevm.depth ≠ 0
  static : sevm.isStatic = false

/-- The state at the loop head before iteration `i`, apart from the stack and gas. -/
structure LoopInv (sevm : Sevm) (i : Nat) (b : Devm) (M : Mem) : Prop where
  stor : CtorStor i (Devm.getStor b sevm.currentTarget)
  nodeleg : getDelegatedCodeAddress (b.getCode 2) = none
  warm : (2 : Adr) ∈ b.accessedAddresses
  error : b.error = none
  wf : Mem.Wf M
  img : ∃ img, Mem.Reads M img ∧ img.sliceD 64 32 0 = (Nat.toB256 (fp i)).toBytes
  size : M.size = memAt i

theorem toB256_add_push {i c : Nat} {x : UInt8} (hx : Bytes.toB256 [x] = Nat.toB256 c)
    (h : i + c < 2 ^ 256) : Nat.toB256 i + Bytes.toB256 [x] = Nat.toB256 (c + i) := by
  rw [hx, toB256_add_toB256 (by omega), Nat.add_comm]

theorem ctorStor_get {i j : Nat} {s : Stor} (h : CtorStor i s) (hj : j ≤ i) (hi : i < 1000) :
    s.get (Nat.toB256 (33 + j)) = zeroHash Bytes.sha256 j := by
  rw [h, toNat_toB256' (by omega)]
  rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

theorem ctorStor_succ {i : Nat} {s : Stor} (h : CtorStor i s) (hi : i < 1000) :
    CtorStor (i + 1) (s.set (Nat.toB256 (34 + i)) (zeroHash Bytes.sha256 (i + 1))) := by
  intro x
  rw [Stor.get_set_ite]
  by_cases hx : Nat.toB256 (34 + i) = x
  · subst hx
    rw [toNat_toB256' (by omega)]
    rw [if_pos rfl, if_pos ⟨by omega, by omega⟩, show 34 + i - 33 = i + 1 by omega]
  · simp only [hx, ↓reduceIte]
    rw [h x]
    have hne : x.toNat ≠ 34 + i := fun e => hx (by
      apply B256.toNat_inj; rw [toNat_toB256' (by omega), e])
    by_cases hlo : 33 ≤ x.toNat ∧ x.toNat ≤ 33 + i
    · rw [if_pos hlo, if_pos ⟨hlo.1, by omega⟩]
    · rw [if_neg hlo, if_neg (by omega)]

/-! ## The cut `SSTORE` step -/

section Steps

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {f : SFunc} {r : Seg}
  {S : List B256} {M : Mem} {G : Nat}

/-- `SSTORE` at its selected cost, in a cut run. -/
theorem rxc_sstore {k' v : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hsentry : gCallStipend < G + sstoreCost sevm b k' v) (hstatic : sevm.isStatic = false)
    (k : SFunc.RunExactCut fs sevm C (St (afterSstore sevm b k' v) S M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (k' :: v :: S) M (G + sstoreCost sevm b k' v))
      (.next (.reg .sstore) f) r := by
  refine .next (Ninst.runCompiled_sstore_selected_setMach hfork hsentry hstatic) ?_
  rw [← afterSstore_stateGas (sevm := sevm) (devm := b) (key := k') (value := v)]
  exact k

/-- `CALLVALUE`, in a cut run. -/
theorem rxc_callvalue (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (sevm.value :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b S M (G + 2)) (.next (.reg .callvalue) f) r :=
  .next (Ninst.runCompiled_pushItem (devm := St b S M (G + 2)) (G := G) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl hroom) k

end Steps

/-! ## One iteration -/

/-- The exact cost of iteration `i` from the world `b`. -/
def iterCost (sevm : Sevm) (b : Devm) (i : Nat) : Nat :=
  17 + sstoreCost sevm (afterSload sevm (afterSload sevm b (Nat.toB256 (33 + i)))
      (Nat.toB256 (33 + i))) (Nat.toB256 (34 + i)) (zeroHash Bytes.sha256 (i + 1)) + 44 +
    (736 + (calculateMemoryGasCost (fp i + 192) - calculateMemoryGasCost (memAt i))) +
    sloadCost sevm (afterSload sevm b (Nat.toB256 (33 + i))) (Nat.toB256 (33 + i)) + 4 + 28 +
    sloadCost sevm b (Nat.toB256 (33 + i)) + 4 + 57

/-- **One zero-hash iteration** `i < 31`: from the loop head with `i` on the stack to the
back-edge into entry 2 with `i + 1`, storing `zeroHash sha256 (i + 1)` at slot `34 + i`. -/
theorem iter {sevm : Sevm} (fr : CtorFrame sevm) {i : Nat} (hi : i < 31) {b : Devm} {M : Mem}
    (inv : LoopInv sevm i b M) {G : Nat} (hGlo : 2300 ≤ G) (hGb : G < 2 ^ 64) :
    ∃ b' M', LoopInv sevm (i + 1) b' M' ∧
      SFunc.RunExactCut prog sevm [2] (St b [Nat.toB256 i] M (G + iterCost sevm b i))
        t_0014_c2 (.at 2 (St b' [Nat.toB256 (i + 1)] M' G)) := by
  rw [show G + iterCost sevm b i = G + 17 + sstoreCost sevm (afterSload sevm
      (afterSload sevm b (Nat.toB256 (33 + i))) (Nat.toB256 (33 + i))) (Nat.toB256 (34 + i))
      (zeroHash Bytes.sha256 (i + 1)) + 44 +
      (736 + (calculateMemoryGasCost (fp i + 192) - calculateMemoryGasCost (memAt i))) +
      sloadCost sevm (afterSload sevm b (Nat.toB256 (33 + i))) (Nat.toB256 (33 + i)) + 4 + 28 +
      sloadCost sevm b (Nat.toB256 (33 + i)) + 4 + 57 by unfold iterCost; omega]
  obtain ⟨img, hr, hfp⟩ := inv.img
  set k := Nat.toB256 (33 + i) with hk
  set b1 := afterSload sevm b k with hb1
  set b2 := afterSload sevm b1 k with hb2
  set z := zeroHash Bytes.sha256 i with hz
  set SS := sstoreCost sevm b2 (Nat.toB256 (34 + i)) (zeroHash Bytes.sha256 (i + 1)) with hSS
  have hSSle : SS ≤ 22100 := by
    rw [hSS]; unfold sstoreCost sstoreValueCost; split_ifs <;> decide
  have hz0 : b.getStorVal sevm.currentTarget k = z := ctorStor_get inv.stor le_rfl (by omega)
  have hz1 : b1.getStorVal sevm.currentTarget k = z := by
    show (Devm.getStor b1 sevm.currentTarget).get k = z
    rw [hb1, afterSload_getStor]; exact hz0
  have hsize : M.size = memAt i := inv.size
  have hn32 : memAt i % 32 = 0 := by unfold memAt fp; split_ifs <;> omega
  obtain ⟨b', M', img', hpost, hwf', hr', hs', hw', hh', hrun⟩ :=
    packed_sha_pairN (fs := prog) (sevm := sevm) (C := [2]) (b := b2) (R := [Nat.toB256 i])
      (M := M) (G := G + 17 + SS + 44) (a := z) (bw := z) (n := memAt i) (f := fp i)
      (T := t_00e6_c1) (fail1 := t_00c8_c1) (fail2 := t_00e2_c1)
      prog_1 (by decide) inv.wf hr hsize hn32 (by unfold memAt fp; split_ifs <;> omega)
      (by unfold memAt fp; split_ifs <;> omega) (by unfold fp; omega) (by unfold fp; omega)
      (by unfold fp; omega) hfp (by simp)
      (by rw [hb2, hb1, afterSload_getCode, afterSload_getCode]; exact inv.nodeleg)
      (by rw [hb2, hb1, afterSload_accessedAddresses, afterSload_accessedAddresses]; exact inv.warm)
      fr.pre fr.fork fr.depth (by omega)
  refine ⟨afterSstore sevm b' (Nat.toB256 (34 + i)) (zeroHash Bytes.sha256 (i + 1)), M',
    ⟨?_, ?_, ?_, ?_, hwf', ⟨img', hr', ?_⟩, ?_⟩, ?_⟩
  · rw [afterSstore_getStor_self, hpost.stor, hb2, hb1, afterSload_getStor, afterSload_getStor]
    exact ctorStor_succ inv.stor (by omega)
  · rw [afterSstore_getCode, hpost.code, hb2, hb1, afterSload_getCode, afterSload_getCode]
    exact inv.nodeleg
  · rw [afterSstore_accessedAddresses, hpost.addrs, hb2, hb1, afterSload_accessedAddresses,
      afterSload_accessedAddresses]
    exact inv.warm
  · rw [afterSstore_error, hpost.error, hb2, hb1, afterSload_error, afterSload_error]
    exact inv.error
  · rw [hw', show fp i + 96 = fp (i + 1) by unfold fp; omega]
  · rw [hs']; unfold memAt fp; rw [if_neg (by omega)]; omega
  -- the loop head: `i < 31`, fall through into the body
  unfold t_0014_c2
  refine rxc_dest ?_
  refine rxc_push rfl (by simp) ?_
  refine rxc_dup (n := 1) rfl (by simp) ?_
  refine rxc_lt (v := 1) ?_ (by simp) ?_
  · rw [show Bytes.toB256 [0x1f] = Nat.toB256 31 by decide, lt_toB256 (by omega) (by omega),
      if_pos hi]
  refine rxc_iszero (v := 0) (by decide) (by simp) ?_
  refine rxc_push rfl (by simp) ?_
  refine rxc_branch_zero ?_
  -- the two bounds-checked reads of `zero_hashes[i]`
  unfold t_001e_c2
  refine rxc_push rfl (by simp) ?_
  refine rxc_push rfl (by simp) ?_
  refine rxc_dup (n := 2) rfl (by simp) ?_
  refine rxc_push rfl (by simp) ?_
  refine rxc_dup (n := 1) rfl (by simp) ?_
  refine rxc_lt (v := 1) ?_ (by simp) ?_
  · rw [show Bytes.toB256 [0x20] = Nat.toB256 32 by decide, lt_toB256 (by omega) (by omega),
      if_pos (by omega)]
  refine rxc_push rfl (by simp) ?_
  refine rxc_branch_succ (by decide) ?_
  unfold t_002c_c2
  refine rxc_dest ?_
  refine rxc_add' (toB256_add_push (c := 33) (by decide) (by omega)) (by simp) ?_
  refine rxc_sload_sel fr.fork (by simp) ?_
  rw [hz0]
  refine rxc_push rfl (by simp) ?_
  refine rxc_dup (n := 3) rfl (by simp) ?_
  refine rxc_push rfl (by simp) ?_
  refine rxc_dup (n := 1) rfl (by simp) ?_
  refine rxc_lt (v := 1) ?_ (by simp) ?_
  · rw [show Bytes.toB256 [0x20] = Nat.toB256 32 by decide, lt_toB256 (by omega) (by omega),
      if_pos (by omega)]
  refine rxc_push rfl (by simp) ?_
  refine rxc_branch_succ (by decide) ?_
  rw [t_003b_c2_eq]
  refine rxc_dest ?_
  refine rxc_add' (toB256_add_push (c := 33) (by decide) (by omega)) (by simp) ?_
  refine rxc_sload_sel fr.fork (by simp) ?_
  rw [hz1]
  -- the packed-hash site, then its continuation
  refine hrun _ ?_
  unfold t_00e6_c1
  refine rxc_dest ?_
  refine rxc_pop ?_
  refine rxc_mload (c := 3) (v := zeroHash Bytes.sha256 (i + 1)) ?_ ?_ ?_ (by simp) ?_
  · rw [toNat_toB256' (by unfold fp; omega)]
    exact charge_covered hs' (by unfold fp; omega) (by omega)
  · rw [toNat_toB256' (by unfold fp; omega)]; exact read_word hr' _ hh'
  · rw [toNat_toB256' (by unfold fp; omega)]
    exact read_covered hs' (by unfold fp; omega) (by omega)
  refine rxc_push rfl (by simp) ?_
  refine rxc_push rfl (by simp) ?_
  refine rxc_dup (n := 3) rfl (by simp) ?_
  refine rxc_add' (toB256_add_push (c := 1) (by decide) (by omega)) (by simp) ?_
  refine rxc_push rfl (by simp) ?_
  refine rxc_dup (n := 1) rfl (by simp) ?_
  refine rxc_lt (v := 1) ?_ (by simp) ?_
  · rw [show Bytes.toB256 [0x20] = Nat.toB256 32 by decide, lt_toB256 (by omega) (by omega),
      if_pos (by omega)]
  refine rxc_push rfl (by simp) ?_
  refine rxc_branch_succ (by decide) ?_
  unfold t_00f8_c1
  refine rxc_dest ?_
  refine rxc_add' (toB256_add_push (c := 33) (by decide) (by omega)) (by simp) ?_
  rw [show 33 + (1 + i) = 34 + i by omega]
  rw [hSS, sstoreCost_congr (d1 := b2) (d2 := b') _ _ hpost.keys.symm (hpost.stor _).symm]
  refine rxc_sstore fr.fork ?_ fr.static ?_
  · unfold gCallStipend; omega
  refine rxc_push rfl (by simp) ?_
  refine rxc_add' (one_add_toB256 (by omega)) (by simp) ?_
  refine rxc_push rfl (by simp) ?_
  exact rxc_jumpCut (by simp)

/-- An iteration costs at most 30,000 gas: two `SLOAD`s (cold at most), one `SSTORE` (a cold
zero-to-nonzero write at most), the packed-hash site and the memory growth. -/
theorem iterCost_le (sevm : Sevm) (b : Devm) {i : Nat} (hi : i < 31) :
    iterCost sevm b i ≤ 30000 := by
  have hl : ∀ (b : Devm) (k : B256), sloadCost sevm b k ≤ 2100 := by
    intro b k; unfold sloadCost; split <;> decide
  have hs : ∀ (b : Devm) (k v : B256), sstoreCost sevm b k v ≤ 22100 := by
    intro b k v; unfold sstoreCost sstoreValueCost; split_ifs <;> decide
  have hm : calculateMemoryGasCost (fp i + 192) - calculateMemoryGasCost (memAt i) ≤ 319 :=
    le_trans (Nat.sub_le _ _) (le_trans (calculateMemoryGasCost_mono
      (show fp i + 192 ≤ 3200 by unfold fp; omega)) (by decide))
  unfold iterCost
  have := hl b (Nat.toB256 (33 + i))
  have := hl (afterSload sevm b (Nat.toB256 (33 + i))) (Nat.toB256 (33 + i))
  have := hs (afterSload sevm (afterSload sevm b (Nat.toB256 (33 + i))) (Nat.toB256 (33 + i)))
    (Nat.toB256 (34 + i)) (zeroHash Bytes.sha256 (i + 1))
  omega

/-! ## The last pass: copy out and return the runtime -/

/-- The window the constructor returns: the creation input's bytes `[275, 275 + 6358)`. -/
def runtimeWindow : Bytes := code.sliceD 275 6358 (Linst.toUInt8 .stop)

theorem runtimeWindow_length : runtimeWindow.length = 6358 := ByteArray.length_sliceD _ _ _ _

/-- The `CODECOPY` charge of the last pass: 199 words copied, memory grown from 3,200 bytes to
6,368. -/
def copyCost : Nat :=
  gVerylow + gasCopy * ceilDiv 6358 32 +
    (calculateMemoryGasCost (memExtSize 3200 0 6358) - calculateMemoryGasCost 3200)

/-- The last pass's exact cost. -/
def exitCost : Nat := 3 + copyCost + 41

theorem exitCost_eq : exitCost = 999 := by decide

theorem memAt_31 : memAt 31 = 3200 := by decide

/-- The state `RETURN` leaves (stated over a variable state, so nothing reduces a concrete
memory image). -/
def returnPost (d : Devm) (i sz : B256) (S : List B256) : Devm :=
  ((d.setMach ⟨S, d.memory, d.gasLeft, d.stateGas⟩).memRead i.toNat sz.toNat).2.withOutput
    (d.memory.read i.toNat sz.toNat).1

theorem returnPost_facts (d : Devm) (i sz : B256) (S : List B256) :
    (returnPost d i sz S).output = (d.memory.read i.toNat sz.toNat).1 ∧
      (returnPost d i sz S).error = d.error ∧
      (∀ a, Devm.getStor (returnPost d i sz S) a = Devm.getStor d a) ∧
      (returnPost d i sz S).gasLeft = d.gasLeft :=
  ⟨rfl, rfl, fun _ => rfl, rfl⟩

/-- `RETURN` of a window that needs no expansion, in a cut run. -/
theorem rxc_return_any {fs : List SFunc} {sevm : Sevm} {C : List Nat} {d : Devm} {i sz : B256}
    {S : List B256} (hstk : d.stack = i :: sz :: S) (hext : d.extCost [⟨i.toNat, sz.toNat⟩] = 0) :
    SFunc.RunExactCut fs sevm C d (.last .return_) (.done (.halted (returnPost d i sz S))) := by
  refine .last ?_
  show Linst.run sevm _ .return_ = _
  exact Linst.run_return_eq_ok hstk (by rw [hext]; exact Nat.zero_le _)
    (by rw [hext, Nat.sub_zero]; rfl)

/-- **The last pass** (`i = 31`): the loop test fails, the constructor copies the appended
runtime to memory `0` and returns it. -/
theorem exit {sevm : Sevm} (hcode : sevm.code = code) {b : Devm} {M : Mem}
    (inv : LoopInv sevm 31 b M) (G : Nat) :
    ∃ post, SFunc.RunExactCut prog sevm [2] (St b [Nat.toB256 31] M (G + exitCost)) t_0014_c2
        (.done (.halted post)) ∧
      post.output = runtimeWindow ∧ post.error = none ∧
      Devm.getStor post sevm.currentTarget = Devm.getStor b sevm.currentTarget ∧
      post.gasLeft = G := by
  obtain ⟨img, hr, -⟩ := inv.img
  have hs : M.size = 3200 := inv.size.trans memAt_31
  set M2 := M.write 0 runtimeWindow with hM2
  have hs2 : M2.size = 6368 := by
    rw [hM2, Mem.size_write_of_size hs (by decide) runtimeWindow_length]; decide
  have hr2 : Mem.Reads M2 (Bytes.writeAt img 0 runtimeWindow) := hr.write inv.wf 0 _
  have hout : (M2.read 0 6358).1 = runtimeWindow := by
    rw [hr2.read]
    have := Bytes.sliceD_writeAt img runtimeWindow 0
    rwa [runtimeWindow_length] at this
  obtain ⟨p1, p2, p3, p4⟩ :=
    returnPost_facts (St b [Nat.toB256 0, Nat.toB256 6358] M2 G) (Nat.toB256 0) (Nat.toB256 6358) []
  simp only [St.memory, St.gasLeft, toNat_toB256' (show 6358 < 2 ^ 256 by decide),
    toNat_toB256' (show 0 < 2 ^ 256 by decide), hout] at p1
  refine ⟨returnPost (St b [Nat.toB256 0, Nat.toB256 6358] M2 G) (Nat.toB256 0) (Nat.toB256 6358)
    [], ?_, p1, p2.trans inv.error, p3 _, p4⟩
  rw [show G + exitCost = G + 3 + copyCost + 41 by unfold exitCost; omega]
  unfold t_0014_c2
  refine rxc_dest ?_
  refine rxc_push rfl (by simp) ?_
  refine rxc_dup (n := 1) rfl (by simp) ?_
  refine rxc_lt (v := 0) (by decide) (by simp) ?_
  refine rxc_iszero (v := 1) (by decide) (by simp) ?_
  refine rxc_push rfl (by simp) ?_
  refine rxc_branch_succ (by decide) ?_
  unfold t_0102_c2
  refine rxc_dest ?_
  refine rxc_pop ?_
  refine rxc_push (w := Nat.toB256 6358) (by decide) (by simp) ?_
  refine rxc_dup (n := 0) rfl (by simp) ?_
  refine rxc_push (w := Nat.toB256 275) (by decide) (by simp) ?_
  refine rxc_push (w := Nat.toB256 0) (by decide) (by simp) ?_
  refine .next (Ninst.runCompiled_codecopy_of (s := [Nat.toB256 6358]) (G := G + 3)
    (c := copyCost) (M := M2) rfl ?_ ?_ rfl) ?_
  · rw [St.extCost_eq hs]
    simp only [toNat_toB256' (show 6358 < 2 ^ 256 by decide),
      toNat_toB256' (show 0 < 2 ^ 256 by decide)]
    rfl
  · simp only [St.memory, toNat_toB256' (show 6358 < 2 ^ 256 by decide),
      toNat_toB256' (show 0 < 2 ^ 256 by decide), toNat_toB256' (show 275 < 2 ^ 256 by decide),
      hcode, hM2, runtimeWindow]
  change SFunc.RunExactCut prog sevm [2] (St b [Nat.toB256 6358] M2 (G + 3)) _ _
  refine rxc_push (w := Nat.toB256 0) (by decide) (by simp) ?_
  refine rxc_return_any rfl ?_
  rw [St.extCost_eq hs2]
  simp only [toNat_toB256' (show 6358 < 2 ^ 256 by decide),
    toNat_toB256' (show 0 < 2 ^ 256 by decide)]
  decide

/-! ## The whole constructor -/

/-- The gas a loop-head state carries before iteration `i`: 30,000 per remaining iteration
and 1,280,000 for the last pass and the code deposit (`6358 · 200 = 1,271,600`). -/
def need (i : Nat) : Nat := 1280000 + (31 - i) * 30000

/-- A loop-head state before iteration `i`. -/
def LoopAt (sevm : Sevm) (i : Nat) (devm : Devm) : Prop :=
  ∃ b M G, devm = St b [Nat.toB256 i] M G ∧ LoopInv sevm i b M ∧ need i ≤ G ∧ G < 2 ^ 64

/-- What the constructor's halting state satisfies. -/
def Done (sevm : Sevm) (post : Devm) : Prop :=
  post.output = runtimeWindow ∧ post.error = none ∧
    CtorStor 31 (Devm.getStor post sevm.currentTarget) ∧ 1271600 ≤ post.gasLeft ∧
    post.gasLeft < 2 ^ 64

/-- **The loop**: 31 iterations through entry 2, then the last pass. -/
theorem loop {sevm : Sevm} (fr : CtorFrame sevm) (hcode : sevm.code = code) :
    ∀ devm, LoopAt sevm 0 devm → ∃ r, SFunc.RunExactCut prog sevm [] devm t_0014_c2 r ∧
      ∃ post, r = .done (.halted post) ∧ Done sevm post := by
  refine SFunc.RunExactCut.iterate prog_2 (by simp) (LoopAt sevm) 31 _ ?_ ?_
  · rintro i hi _ ⟨b, M, G, rfl, inv, hneed, hGb⟩
    have hle := iterCost_le sevm b hi
    have hn : 1280000 + (31 - i) * 30000 ≤ G := hneed
    obtain ⟨b', M', inv', run⟩ := iter fr hi inv (G := G - iterCost sevm b i) (by omega)
      (by omega)
    refine ⟨_, ?_, b', M', G - iterCost sevm b i, rfl, inv', ?_, by omega⟩
    · have e : St b [Nat.toB256 i] M G =
          St b [Nat.toB256 i] M (G - iterCost sevm b i + iterCost sevm b i) := by
        congr 1; omega
      rw [e]
      exact run
    · show 1280000 + (31 - (i + 1)) * 30000 ≤ G - iterCost sevm b i
      exact Nat.le_sub_of_add_le (by omega)
  · rintro _ ⟨b, M, G, rfl, inv, hneed, hGb⟩
    have hn : 1280000 + (31 - 31) * 30000 ≤ G := hneed
    have hle : exitCost ≤ G := by rw [exitCost_eq]; omega
    obtain ⟨post, run, hout, herr, hstor, hgas⟩ := exit hcode inv (G - exitCost)
    refine ⟨_, ?_, fun d h => Seg.noConfusion h, post, rfl, ⟨hout, herr, ?_, ?_, ?_⟩⟩
    · have e : St b [Nat.toB256 31] M G = St b [Nat.toB256 31] M (G - exitCost + exitCost) := by
        congr 1; omega
      rw [e]
      exact run
    · rw [hstor]; exact inv.stor
    · rw [hgas, exitCost_eq]; omega
    · rw [hgas]; omega

/-- The world facts the constructor needs at entry. -/
structure CtorStart (sevm : Sevm) (b : Devm) : Prop where
  code : sevm.code = code
  value : sevm.value = 0
  stor : ∀ x, (Devm.getStor b sevm.currentTarget).get x = 0
  nodeleg : getDelegatedCodeAddress (b.getCode 2) = none
  warm : (2 : Adr) ∈ b.accessedAddresses
  error : b.error = none

/-- The memory after `mstore(0x40, 0x80)`. -/
def mem0 : Mem := Mem.empty.write 64 (Nat.toB256 128).toBytes

theorem ctorStor_zero {s : Stor} (h : ∀ x, s.get x = 0) : CtorStor 0 s := by
  intro x
  rw [h x]
  split_ifs with hx
  · rw [show x.toNat - 33 = 0 by omega]; rfl
  · rfl

/-- **The constructor, gas-exact**: from an empty stack and memory with at least
`need 0 + 45` gas (and less than `2^64`), the lifted constructor halts, returning the runtime
window, with no error, the 32-entry zero-hash table in storage and at least 1,271,600 gas
left. -/
theorem ctor_run {sevm : Sevm} (fr : CtorFrame sevm) {b : Devm} (st : CtorStart sevm b)
    {G : Nat} (hG : need 0 ≤ G) (hGb : G < 2 ^ 64) :
    ∃ post, SProg.RunExact prog sevm (St b [] Mem.empty (G + 45)) post ∧ Done sevm post := by
  have hs0 : mem0.size = 96 := by rw [mem0, Mem.size_write_word_at]; rfl
  have hr0 : Mem.Reads mem0 (Bytes.writeAt [] 64 (Nat.toB256 128).toBytes) :=
    Mem.reads_empty.write Mem.wf_empty 64 _
  have hfp0 : (Bytes.writeAt [] 64 (Nat.toB256 128).toBytes).sliceD 64 32 0 =
      (Nat.toB256 (fp 0)).toBytes := by
    have := Bytes.sliceD_writeAt [] (Nat.toB256 128).toBytes 64
    rwa [B256.length_toBytes] at this
  obtain ⟨r, run, post, rfl, hpost⟩ := loop fr st.code (St b [Nat.toB256 0] mem0 G)
    ⟨b, mem0, G, rfl, ⟨ctorStor_zero st.stor, st.nodeleg, st.warm, st.error,
      Mem.wf_empty.write _ _, ⟨_, hr0, hfp0⟩, hs0⟩, hG, hGb⟩
  refine ⟨post, ⟨t_0000_c0, rfl, SFunc.runExact_iff_runExactCut_nil.mpr ?_⟩, hpost⟩
  unfold t_0000_c0
  refine rxc_push (w := Nat.toB256 128) (by decide) (by simp) ?_
  refine rxc_push (w := Nat.toB256 64) (by decide) (by simp) ?_
  refine rxc_mstore (c := 12) (M' := mem0) ?_ rfl ?_
  · rw [St.extCost_eq (show Mem.empty.size = 0 from rfl)]; decide
  refine rxc_callvalue (by simp) ?_
  rw [st.value]
  refine rxc_dup (n := 0) rfl (by simp) ?_
  refine rxc_iszero (v := 1) (by decide) (by simp) ?_
  refine rxc_push rfl (by simp) ?_
  refine rxc_branch_succ (by decide) ?_
  unfold t_0010_c0
  refine rxc_dest ?_
  refine rxc_pop ?_
  refine rxc_push (w := Nat.toB256 0) (by decide) (by simp) ?_
  rw [t_0014_c0_eq]
  exact run

end Blanc.Lift.BeaconDeposit.Creation
