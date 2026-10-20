import Blanc.Lift.Curve3Pool.Walk.AddLiquidityMint

/-! # `add_liquidity`: final event, lock clear and stop -/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

abbrev alTopic : B256 := Bytes.toB256 [0x42, 0x3f, 0x64, 0x95, 0xa0, 0x8f, 0xc6, 0x52, 0x42, 0x5c, 0xf4, 0xed, 0x0d, 0x1f, 0x9e, 0x37, 0xe5, 0x71, 0xd9, 0xb9, 0x52, 0x9b, 0x1c, 0x1c, 0x23, 0xcc, 0xe7, 0x80, 0xb2, 0xe7, 0xdf, 0x0d]

def alLog (sevm : Sevm) (f0 f1 f2 D1 T' : B256) : Log :=
  ⟨sevm.currentTarget, [alTopic, sevm.caller.toB256],
    (Sevm.dataWord sevm (Bytes.toB256 [4])).toBytes ++
    (Sevm.dataWord sevm (Bytes.toB256 [0x24])).toBytes ++
    (Sevm.dataWord sevm (Bytes.toB256 [0x44])).toBytes ++
    f0.toBytes ++ f1.toBytes ++ f2.toBytes ++ D1.toBytes ++ T'.toBytes⟩

/-- The successful final tail emits the exact event and clears the reentrancy lock. -/
theorem xa_al_finish {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {f0 f1 f2 T D1 mint : B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hf0 : WordAt img 0x140 f0) (hf1 : WordAt img 0x160 f1) (hf2 : WordAt img 0x180 f2)
    (ht : WordAt img 0x240 T) (hd1 : WordAt img 0x900 D1) (hmint : WordAt img 0xba0 mint)
    (h : XAt sevm post 0x180c (St b [] M G) L) :
    ¬ T + mint < T ∧ L = [] ∧
      (∀ x, (post.getStor sevm.currentTarget).get x =
        ((b.getStor sevm.currentTarget).set lockSlot 0).get x) ∧
      post.logs = b.logs ++ [alLog sevm f0 f1 f2 D1 (T + mint)] ∧ post.output = b.output := by
  xjd 0x180d
  xs 0x180f (.push [0x00] (by decide)) ri_push
  xs 0x1810 (.reg .pop) ri_pop
  xs 0x1813 (.push [0x0d, 0x00] (by decide)) ri_push
  xs 0x1814 (.reg .pop) ri_pop
  xs 0x1816 (.push [0x04] (by decide)) ri_push
  xs 0x1817 (.reg .calldataload) ri_calldataload
  xs 0x181a (.push [0x0d, 0x20] (by decide)) ri_push
  xma 0x181b (.reg .mstore) (ri_mstore_imgAtA (o := 0xd20) rfl)
  xs 0x181d (.push [0x24] (by decide)) ri_push
  xs 0x181e (.reg .calldataload) ri_calldataload
  xs 0x1821 (.push [0x0d, 0x40] (by decide)) ri_push
  xma 0x1822 (.reg .mstore) (ri_mstore_imgAtA (o := 0xd40) rfl)
  xs 0x1824 (.push [0x44] (by decide)) ri_push
  xs 0x1825 (.reg .calldataload) ri_calldataload
  xs 0x1828 (.push [0x0d, 0x60] (by decide)) ri_push
  xma 0x1829 (.reg .mstore) (ri_mstore_imgAtA (o := 0xd60) rfl)
  xs 0x182c (.push [0x01, 0x40] (by decide)) ri_push
  xml 0x182d 0x140 hf0
  xs 0x1830 (.push [0x0d, 0x80] (by decide)) ri_push
  xma 0x1831 (.reg .mstore) (ri_mstore_imgAtA (o := 0xd80) rfl)
  xs 0x1834 (.push [0x01, 0x60] (by decide)) ri_push
  xml 0x1835 0x160 hf1
  xs 0x1838 (.push [0x0d, 0xa0] (by decide)) ri_push
  xma 0x1839 (.reg .mstore) (ri_mstore_imgAtA (o := 0xda0) rfl)
  xs 0x183c (.push [0x01, 0x80] (by decide)) ri_push
  xml 0x183d 0x180 hf2
  xs 0x1840 (.push [0x0d, 0xc0] (by decide)) ri_push
  xma 0x1841 (.reg .mstore) (ri_mstore_imgAtA (o := 0xdc0) rfl)
  xs 0x1844 (.push [0x09, 0x00] (by decide)) ri_push
  xml 0x1845 0x900 hd1
  xs 0x1848 (.push [0x0d, 0xe0] (by decide)) ri_push
  xma 0x1849 (.reg .mstore) (ri_mstore_imgAtA (o := 0xde0) rfl)
  xs 0x184c (.push [0x02, 0x40] (by decide)) ri_push
  xml 0x184d 0x240 ht
  xs 0x1850 (.push [0x0b, 0xa0] (by decide)) ri_push
  xml 0x1851 0xba0 hmint
  xs 0x1852 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x1853 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x1854 (.reg (.dup 3)) (ri_dup (by rfl))
  xs 0x1855 (.reg .add) ri_add
  xs 0x1856 (.reg .lt) ri_lt
  xs 0x1857 (.reg .iszero) ri_iszero
  xs 0x185a (.push [0x18, 0x5f] (by decide)) ri_push
  xji 0x185b 0x185f hw
  · xdead
  have hTa := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
  clear hw
  xjd 0x1860
  xs 0x1861 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1862 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1863 (.reg .add) ri_add
  xs 0x1864 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1865 (.reg .pop) ri_pop
  xs 0x1866 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1867 (.reg .pop) ri_pop
  xs 0x186a (.push [0x0e, 0x00] (by decide)) ri_push
  xma 0x186b (.reg .mstore) (ri_mstore_imgAtA (o := 0xe00) rfl)
  xs 0x186c (.reg .caller) ri_caller
  xs 0x188d (.push [0x42, 0x3f, 0x64, 0x95, 0xa0, 0x8f, 0xc6, 0x52, 0x42, 0x5c, 0xf4, 0xed, 0x0d, 0x1f, 0x9e, 0x37, 0xe5, 0x71, 0xd9, 0xb9, 0x52, 0x9b, 0x1c, 0x1c, 0x23, 0xcc, 0xe7, 0x80, 0xb2, 0xe7, 0xdf, 0x0d] (by decide)) ri_push
  xs 0x1890 (.push [0x01, 0x00] (by decide)) ri_push
  xs 0x1893 (.push [0x0d, 0x20] (by decide)) ri_push
  obtain ⟨img2, hR2, hI⟩ := Mem.Reads.forget hR
  clear hR
  have hdata : Region img2 0xd20
      ((Sevm.dataWord sevm (Bytes.toB256 [4])).toBytes ++
      (Sevm.dataWord sevm (Bytes.toB256 [0x24])).toBytes ++
      (Sevm.dataWord sevm (Bytes.toB256 [0x44])).toBytes ++
      f0.toBytes ++ f1.toBytes ++ f2.toBytes ++ D1.toBytes ++ (T + mint).toBytes) := by
    rw [hI]
    refine Region.append' (o' := 0xe00) (Region.append' (o' := 0xde0)
      (Region.append' (o' := 0xdc0) (Region.append' (o' := 0xda0)
      (Region.append' (o' := 0xd80) (Region.append' (o' := 0xd60)
      (Region.append' (o' := 0xd40) ?_ ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_
    all_goals first
      | simp only [List.length_append, B256.length_toBytes]
      | exact Region.of_word (by wchain)
  clear hI
  replace h := xa_nextAt (n := .reg (.log 2)) (pc' := 0x1894) (atN hcode (by kernel_rfl))
    (by nofun) (by rfl) h
  obtain ⟨_, hs, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_log2_post hs
  clear hs
  rw [Mem.Reads.read hR2, show (Bytes.toB256 [0x0d, 0x20]).toNat = 0xd20 from rfl,
    show (Bytes.toB256 [0x01, 0x00]).toNat = 0x100 from rfl,
    hdata.slice (by simp only [List.length_append, B256.length_toBytes])] at h
  xs 0x1896 (.push [0x00] (by decide)) ri_push
  xs 0x189a (.push [0xff, 0xff, 0xff] (by decide)) ri_push
  xw 0x189b (.reg .sstore) ri_sstore
  obtain ⟨hrun, hL⟩ := xa_halt (l := .stop) (atL hcode (by kernel_rfl)) h
  have hp := (Except.ok.inj hrun).symm
  subst hp hL
  refine ⟨hTa, rfl, ?_, ?_, ?_⟩
  · intro x
    show ((afterSstore sevm _ _ _).getStor _).get x = _
    rw [afterSstore_getStor_self, lockSlot_lit, zero_lit]
    rfl
  · show (afterSstore sevm _ _ _).logs = _
    rw [afterSstore_logs]
    rfl
  · show (afterSstore sevm _ _ _).output = _
    rw [afterSstore_output]
    rfl

end Blanc.Lift.Curve3Pool
