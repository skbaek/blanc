import Blanc.Lift.UniswapV2Pair.GetterStorageMappingDecoder

/-! Four actual checked pc-zero selector routes for the remaining storage getters. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

inductive StorageGetter
  | balanceOf | nonces | allowance | getReserves

def StorageGetter.selector : StorageGetter → B256
  | .balanceOf => 0x70a08231
  | .nonces => 0x7ecebe00
  | .allowance => 0xdd62ed3e
  | .getReserves => 0x0902f1ac

def StorageGetter.entryTree : StorageGetter → SFunc
  | .balanceOf => t_049c_c87
  | .nonces => t_04d7_c82
  | .allowance => t_0640_c77
  | .getReserves => t_02d6_c101

def StorageGetter.dispatchGas : StorageGetter → Nat
  | .balanceOf => 187
  | .nonces => 164
  | .allowance => 207
  | .getReserves => 210

theorem getterStorage_dispatch_exact {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (s : StorageGetter) (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = s.selector)
    (body : SFunc.RunExact cert.prog sevm (St b [s.selector] getterInitMemory G) s.entryTree o) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + s.dispatchGas)) t_0000_c0 o := by
  cases s with
  | balanceOf =>
    simp only [StorageGetter.selector, StorageGetter.entryTree, StorageGetter.dispatchGas] at selector body ⊢
    refine getterString_guards_exact (G := G + 124) value size ?_
    unfold t_001a_c0
    refine rx_push (w := 0) rfl (by decide) ?_
    refine rx_calldataload (by decide) ?_
    refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_shr (v := 0x70a08231) selector (by decide) ?_
    refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0xf9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_branch_zero ?_
    unfold t_002b_c0
    refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0xba9a7a56) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x97) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_branch_succ (by decide) ?_
    unfold t_0097_c0
    refine rx_dest ?_
    refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x7ecebe00) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0xd3) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_branch_succ (by decide) ?_
    unfold t_00d3_c0
    refine rx_dest ?_
    refine cmp_miss (by decide) ?_
    unfold t_00df_c0
    exact cmp_hit (tgt := t_049c_c87) rfl (by rfl) body
  | nonces =>
    simp only [StorageGetter.selector, StorageGetter.entryTree, StorageGetter.dispatchGas] at selector body ⊢
    refine getterString_guards_exact (G := G + 101) value size ?_
    unfold t_001a_c0
    refine rx_push (w := 0) rfl (by decide) ?_
    refine rx_calldataload (by decide) ?_
    refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_shr (v := 0x7ecebe00) selector (by decide) ?_
    refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0xf9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_branch_zero ?_
    unfold t_002b_c0
    refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0xba9a7a56) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x97) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_branch_succ (by decide) ?_
    unfold t_0097_c0
    refine rx_dest ?_
    refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x7ecebe00) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0xd3) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_branch_zero ?_
    unfold t_00a3_c0
    exact cmp_hit (tgt := t_04d7_c82) rfl (by rfl) body
  | allowance =>
    simp only [StorageGetter.selector, StorageGetter.entryTree, StorageGetter.dispatchGas] at selector body ⊢
    refine getterString_guards_exact (G := G + 144) value size ?_
    unfold t_001a_c0
    refine rx_push (w := 0) rfl (by decide) ?_
    refine rx_calldataload (by decide) ?_
    refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_shr (v := 0xdd62ed3e) selector (by decide) ?_
    refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0xf9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_branch_zero ?_
    unfold t_002b_c0
    refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0xba9a7a56) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x97) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_branch_zero ?_
    unfold t_0036_c0
    refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0xd21220a7) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x71) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_branch_zero ?_
    unfold t_0041_c0
    refine cmp_miss (by decide) ?_
    unfold t_004c_c0
    refine cmp_miss (by decide) ?_
    unfold t_0057_c0
    exact cmp_hit (tgt := t_0640_c77) rfl (by rfl) body
  | getReserves =>
    simp only [StorageGetter.selector, StorageGetter.entryTree, StorageGetter.dispatchGas] at selector body ⊢
    refine getterString_guards_exact (G := G + 147) value size ?_
    unfold t_001a_c0
    refine rx_push (w := 0) rfl (by decide) ?_
    refine rx_calldataload (by decide) ?_
    refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_shr (v := 0x0902f1ac) selector (by decide) ?_
    refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0xf9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_branch_succ (by decide) ?_
    unfold t_00f9_c0
    refine rx_dest ?_
    refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x23b872dd) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x166) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_branch_succ (by decide) ?_
    unfold t_0166_c0
    refine rx_dest ?_
    refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x95ea7b3) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x197) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_branch_succ (by decide) ?_
    unfold t_0197_c0
    refine rx_dest ?_
    refine cmp_miss (by decide) ?_
    unfold t_01a3_c0
    refine cmp_miss (by decide) ?_
    unfold t_01ae_c0
    exact cmp_hit (tgt := t_02d6_c101) rfl (by rfl) body

theorem getterStorage_selector_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (s : StorageGetter) (selector : Blanc.Sevm.selector sevm = s.selector)
    (run : SFunc.Run cert.prog sevm (St b [] M G) t_001a_c0 o) :
    ∃ G', SFunc.Run cert.prog sevm (St b [s.selector] M G') s.entryTree o := by
  have h := run.cut
  unfold t_001a_c0 at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_calldataload hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_shr hd
  simp only [show Bytes.toB256 [0x00] = (0 : B256) from rfl,
    show Bytes.toB256 [0xe0] = (224 : B256) from rfl,
    show (224 : B256).toNat = 224 from rfl,
    show Sevm.dataWord sevm 0 >>> 224 = s.selector from selector] at hd
  subst d
  cases s with
  | balanceOf =>
    simp only [StorageGetter.selector, StorageGetter.entryTree] at h ⊢
    obtain ⟨_, h⟩ := ric_cmp_gt h
    simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0x70a08231 : B256) = (0 : B256) from by decide, ite_true] at h
    unfold t_002b_c0 at h
    obtain ⟨_, h⟩ := ric_cmp_gt h
    simp only [show B256.gtCheck (Bytes.toB256 [0xba, 0x9a, 0x7a, 0x56]) (0x70a08231 : B256) = (1 : B256) from by decide,
      show (1 : B256) ≠ 0 from by decide, ite_false] at h
    unfold t_0097_c0 at h
    obtain ⟨_, h⟩ := ric_dest h
    obtain ⟨_, h⟩ := ric_cmp_gt h
    simp only [show B256.gtCheck (Bytes.toB256 [0x7e, 0xce, 0xbe, 0x00]) (0x70a08231 : B256) = (1 : B256) from by decide,
      show (1 : B256) ≠ 0 from by decide, ite_false] at h
    unfold t_00d3_c0 at h
    obtain ⟨_, h⟩ := ric_dest h
    obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0469_c86) (by intro bad; cases bad) (by rfl) h
    simp only [show B256.eqCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0x70a08231 : B256) = (0 : B256) from by decide, ite_true] at h
    unfold t_00df_c0 at h
    obtain ⟨_, h⟩ := ric_cmp_eq (g := t_049c_c87) (by intro bad; cases bad) (by rfl) h
    simp only [show B256.eqCheck (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]) (0x70a08231 : B256) = (1 : B256) from by decide,
      show (1 : B256) ≠ 0 from by decide, ite_false] at h
    exact ⟨_, h.uncut⟩
  | nonces =>
    simp only [StorageGetter.selector, StorageGetter.entryTree] at h ⊢
    obtain ⟨_, h⟩ := ric_cmp_gt h
    simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0x7ecebe00 : B256) = (0 : B256) from by decide, ite_true] at h
    unfold t_002b_c0 at h
    obtain ⟨_, h⟩ := ric_cmp_gt h
    simp only [show B256.gtCheck (Bytes.toB256 [0xba, 0x9a, 0x7a, 0x56]) (0x7ecebe00 : B256) = (1 : B256) from by decide,
      show (1 : B256) ≠ 0 from by decide, ite_false] at h
    unfold t_0097_c0 at h
    obtain ⟨_, h⟩ := ric_dest h
    obtain ⟨_, h⟩ := ric_cmp_gt h
    simp only [show B256.gtCheck (Bytes.toB256 [0x7e, 0xce, 0xbe, 0x00]) (0x7ecebe00 : B256) = (0 : B256) from by decide, ite_true] at h
    unfold t_00a3_c0 at h
    obtain ⟨_, h⟩ := ric_cmp_eq (g := t_04d7_c82) (by intro bad; cases bad) (by rfl) h
    simp only [show B256.eqCheck (Bytes.toB256 [0x7e, 0xce, 0xbe, 0x0]) (0x7ecebe00 : B256) = (1 : B256) from by decide,
      show (1 : B256) ≠ 0 from by decide, ite_false] at h
    exact ⟨_, h.uncut⟩
  | allowance =>
    simp only [StorageGetter.selector, StorageGetter.entryTree] at h ⊢
    obtain ⟨_, h⟩ := ric_cmp_gt h
    simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0xdd62ed3e : B256) = (0 : B256) from by decide, ite_true] at h
    unfold t_002b_c0 at h
    obtain ⟨_, h⟩ := ric_cmp_gt h
    simp only [show B256.gtCheck (Bytes.toB256 [0xba, 0x9a, 0x7a, 0x56]) (0xdd62ed3e : B256) = (0 : B256) from by decide, ite_true] at h
    unfold t_0036_c0 at h
    obtain ⟨_, h⟩ := ric_cmp_gt h
    simp only [show B256.gtCheck (Bytes.toB256 [0xd2, 0x12, 0x20, 0xa7]) (0xdd62ed3e : B256) = (0 : B256) from by decide, ite_true] at h
    unfold t_0041_c0 at h
    obtain ⟨_, h⟩ := ric_cmp_eq (g := t_05da_c75) (by intro bad; cases bad) (by rfl) h
    simp only [show B256.eqCheck (Bytes.toB256 [0xd2, 0x12, 0x20, 0xa7]) (0xdd62ed3e : B256) = (0 : B256) from by decide, ite_true] at h
    unfold t_004c_c0 at h
    obtain ⟨_, h⟩ := ric_cmp_eq (g := t_05e2_c76) (by intro bad; cases bad) (by rfl) h
    simp only [show B256.eqCheck (Bytes.toB256 [0xd5, 0x5, 0xac, 0xcf]) (0xdd62ed3e : B256) = (0 : B256) from by decide, ite_true] at h
    unfold t_0057_c0 at h
    obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0640_c77) (by intro bad; cases bad) (by rfl) h
    simp only [show B256.eqCheck (Bytes.toB256 [0xdd, 0x62, 0xed, 0x3e]) (0xdd62ed3e : B256) = (1 : B256) from by decide,
      show (1 : B256) ≠ 0 from by decide, ite_false] at h
    exact ⟨_, h.uncut⟩
  | getReserves =>
    simp only [StorageGetter.selector, StorageGetter.entryTree] at h ⊢
    obtain ⟨_, h⟩ := ric_cmp_gt h
    simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0x0902f1ac : B256) = (1 : B256) from by decide,
      show (1 : B256) ≠ 0 from by decide, ite_false] at h
    unfold t_00f9_c0 at h
    obtain ⟨_, h⟩ := ric_dest h
    obtain ⟨_, h⟩ := ric_cmp_gt h
    simp only [show B256.gtCheck (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd]) (0x0902f1ac : B256) = (1 : B256) from by decide,
      show (1 : B256) ≠ 0 from by decide, ite_false] at h
    unfold t_0166_c0 at h
    obtain ⟨_, h⟩ := ric_dest h
    obtain ⟨_, h⟩ := ric_cmp_gt h
    simp only [show B256.gtCheck (Bytes.toB256 [0x09, 0x5e, 0xa7, 0xb3]) (0x0902f1ac : B256) = (1 : B256) from by decide,
      show (1 : B256) ≠ 0 from by decide, ite_false] at h
    unfold t_0197_c0 at h
    obtain ⟨_, h⟩ := ric_dest h
    obtain ⟨_, h⟩ := ric_cmp_eq (g := t_01be_c99) (by intro bad; cases bad) (by rfl) h
    simp only [show B256.eqCheck (Bytes.toB256 [0x2, 0x2c, 0xd, 0x9f]) (0x0902f1ac : B256) = (0 : B256) from by decide, ite_true] at h
    unfold t_01a3_c0 at h
    obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0259_c100) (by intro bad; cases bad) (by rfl) h
    simp only [show B256.eqCheck (Bytes.toB256 [0x6, 0xfd, 0xde, 0x3]) (0x0902f1ac : B256) = (0 : B256) from by decide, ite_true] at h
    unfold t_01ae_c0 at h
    obtain ⟨_, h⟩ := ric_cmp_eq (g := t_02d6_c101) (by intro bad; cases bad) (by rfl) h
    simp only [show B256.eqCheck (Bytes.toB256 [0x9, 0x2, 0xf1, 0xac]) (0x0902f1ac : B256) = (1 : B256) from by decide,
      show (1 : B256) ≠ 0 from by decide, ite_false] at h
    exact ⟨_, h.uncut⟩

end Blanc.Lift.UniswapV2Pair
