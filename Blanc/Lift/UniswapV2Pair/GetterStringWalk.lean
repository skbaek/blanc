import Blanc.Lift.UniswapV2Pair.GetterStringMemory
import Blanc.Lift.UniswapV2Pair.GetterWalk
import Blanc.Lift.CopyLoop

/-! Actual constant-string callees and shared ABI wrapper walks. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def StringGetter.lengthByte : StringGetter → UInt8
  | .name => 0x0a
  | .symbol => 0x06

def StringGetter.payloadTail (s : StringGetter) : Bytes :=
  s.data.drop 1 ++ List.replicate (32 - s.data.length) 0

theorem StringGetter.payload_bound (s : StringGetter) :
    (0x55 :: s.payloadTail).length ≤ 32 := by
  cases s <;> decide

theorem StringGetter.length_push (s : StringGetter) :
    Bytes.toB256 [s.lengthByte] = s.length := by
  cases s <;> decide

theorem StringGetter.word_push (s : StringGetter) :
    Bytes.toB256 (0x55 :: s.payloadTail) = s.word := by
  cases s <;> decide +kernel

def getterStringCalleeTree (s : StringGetter) : SFunc :=
  .dest (.next (.push [0x40] (by decide)) (.next (.reg .mload)
    (.next (.reg (.dup 0)) (.next (.push [0x40] (by decide))
    (.next (.reg .add) (.next (.push [0x40] (by decide)) (.next (.reg .mstore)
    (.next (.reg (.dup 0)) (.next (.push [s.lengthByte] (by simp only [List.length_cons, List.length_nil]; decide))
    (.next (.reg (.dup 1)) (.next (.reg .mstore) (.next (.push [0x20] (by decide))
    (.next (.reg .add) (.next (.push (0x55 :: s.payloadTail) s.payload_bound)
    (.next (.reg (.dup 1)) (.next (.reg .mstore) (.next (.reg .pop)
    (.next (.reg (.dup 1)) .ret))))))))))))))))))

def StringGetter.callee : StringGetter → SFunc
  | .name => t_0d57_c55
  | .symbol => t_1892_c38

theorem StringGetter.callee_tree (s : StringGetter) :
    s.callee = getterStringCalleeTree s := by
  cases s <;> rfl

theorem getterString_callee_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {ρ : B256} (s : StringGetter)
    (mem : PtrMem 128 96 M) (room : R.length ≤ 1018) :
    SFunc.RunExact fs sevm (St b (ρ :: R) M (G + 71)) s.callee
      (.returned (St b (128 :: ρ :: R) (getterStringMemory M s.length s.word) G)) := by
  have ptr : PtrMem 192 96 (M.write 64 (192 : B256).toBytes) := mem.set
  have len := ptr.write 128 s.length (Or.inr (by decide))
  rw [show memExtSize 96 128 32 = 160 from by decide] at len
  rw [s.callee_tree]
  unfold getterStringCalleeTree
  refine rx_dest ?_
  refine rx_push (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_mload (c := 3) ?_ mem.word (mem.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq mem.size]; decide
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 192) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]; decide
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_push s.length_push (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 9) ?_ rfl ?_
  · simp only [show (64 : B256).toNat = 64 from rfl,
      show (128 : B256).toNat = 128 from rfl]
    rw [St.extCost_eq ptr.size]; decide
  refine rx_push (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 160) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push s.word_push (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 6) ?_ rfl ?_
  · simp only [show (64 : B256).toNat = 64 from rfl,
      show (128 : B256).toNat = 128 from rfl,
      show (160 : B256).toNat = 160 from rfl]
    rw [St.extCost_eq len.size]; decide
  refine rx_pop ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  simp only [show (64 : B256).toNat = 64 from rfl,
    show (128 : B256).toNat = 128 from rfl, show (160 : B256).toNat = 160 from rfl]
  exact rx_ret

theorem getterString_callee_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {ρ : B256} {o : Outcome} (s : StringGetter)
    (mem : PtrMem 128 96 M)
    (run : SFunc.Run fs sevm (St b (ρ :: R) M G) s.callee o) :
    ∃ G', o = .returned (St b (128 :: ρ :: R) (getterStringMemory M s.length s.word) G') := by
  have h := run.cut
  rw [s.callee_tree] at h
  unfold getterStringCalleeTree at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  rw [show Bytes.toB256 [0x40] = (64 : B256) from rfl] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_mload hd
  rw [show (64 : B256).toNat = 64 from rfl, mem.read_self (by decide)] at h
  change SFunc.RunCut fs sevm [] (St b (memWord M 64 :: ρ :: R) M _) _ _ at h
  rw [mem.word] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := 128) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_add hd
  rw [show Bytes.toB256 [0x40] + (128 : B256) = 192 from by decide] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_mstore hd
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := 128) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  rw [s.length_push] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := 128) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_mstore hd
  rw [show (128 : B256).toNat = 128 from rfl] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_add hd
  rw [show Bytes.toB256 [0x20] + (128 : B256) = 160 from by decide] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  rw [s.word_push] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := 160) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_mstore hd
  rw [show (160 : B256).toNat = 160 from rfl] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := ρ) rfl hd
  obtain ⟨g, hg⟩ := ric_ret h
  exact ⟨g, Seg.done.inj hg⟩


def getterStringReturn (b : Devm) (R : List B256) (M : Mem) (G : Nat) : Devm :=
  returnPost (St b (192 :: 96 :: R) M G) 192 96 R

theorem getterString_return_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {L : B256}
    (mem : PtrMem 192 288 M) (room : R.length ≤ 1018) :
    SFunc.RunExact fs sevm (St b (L :: 288 :: 192 :: 192 :: 128 :: R) M (G + 30))
      t_02c8_c1 (.halted (getterStringReturn b R M G)) := by
  unfold t_02c8_c1
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_swap3 ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_push (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_mload (c := 3) ?_ mem.word (mem.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq mem.size]; decide
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_swap2 ?_
  refine rx_sub' (v := 96) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  exact rx_return_any rfl (by rw [St.extCost_eq mem.size]; decide)

theorem getterString_padding_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} (s : StringGetter)
    (mem : PtrMem 192 288 M) (word : memWord M 256 = s.word) (room : R.length ≤ 1014) :
    SFunc.RunExact fs sevm
      (St b (s.length :: (256 + s.length) :: 192 :: 192 :: 128 :: R) M (G + 146))
      t_02af_c39 (.halted (getterStringReturn b R (M.write 256 s.word.toBytes) G)) := by
  have padded := mem.write 256 s.word (Or.inr (by decide))
  rw [show memExtSize 288 256 32 = 288 from by decide] at padded
  unfold t_02af_c39
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  refine rx_sub' (v := 256) (by cases s <;> decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_mload (c := 3) ?_ word (mem.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq mem.size]; decide
  refine rx_push (w := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup4 (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_sub' (v := 32 - s.length) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 256) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_exp' (c := 60) (by cases s <;> decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_sub (by simp only [List.length_cons]; omega) ?_
  refine rx_not rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and s.masked (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]; decide
  refine rx_push (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 288) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap2 ?_
  refine rx_pop ?_
  simp only [show (256 : B256).toNat = 256 from rfl]
  exact getterString_return_exact padded (by omega)


theorem getterString_return_inv {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {L : B256} {r : Seg}
    (mem : PtrMem 192 288 M)
    (h : SFunc.RunCut fs sevm C (St b (L :: 288 :: 192 :: 192 :: 128 :: R) M G) t_02c8_c1 r) :
    ∃ d, r = .done (.halted d) ∧ d.output = (M.read 192 96).1 ∧
      (∀ a, Devm.getStor d a = Devm.getStor b a) ∧ d.logs = b.logs := by
  unfold t_02c8_c1 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  rw [show Bytes.toB256 [0x40] = (64 : B256) from rfl] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_mload hd
  rw [show (64 : B256).toNat = 64 from rfl, mem.read_self (by decide)] at h
  change SFunc.RunCut fs sevm C (St b (memWord M 64 :: 288 :: R) M _) _ _ at h
  rw [mem.word] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_sub hd
  rw [show (288 : B256) - 192 = 96 from by decide] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  cases h with
  | last hr =>
    obtain ⟨out, stor, logs⟩ := ri_return hr
    exact ⟨_, rfl, out, stor, logs⟩

theorem getterString_padding_inv {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {r : Seg} (s : StringGetter)
    (mem : PtrMem 192 288 M) (word : memWord M 256 = s.word)
    (h : SFunc.RunCut fs sevm C
      (St b (s.length :: (256 + s.length) :: 192 :: 192 :: 128 :: R) M G) t_02af_c39 r) :
    ∃ d, r = .done (.halted d) ∧ d.output = ((M.write 256 s.word.toBytes).read 192 96).1 ∧
      (∀ a, Devm.getStor d a = Devm.getStor b a) ∧ d.logs = b.logs := by
  have padded := mem.write 256 s.word (Or.inr (by decide))
  rw [show memExtSize 288 256 32 = 288 from by decide] at padded
  unfold t_02af_c39 at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_sub hd
  rw [show (256 + s.length) - s.length = (256 : B256) from by cases s <;> decide] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_mload hd
  rw [show (256 : B256).toNat = 256 from rfl, mem.read_self (by decide)] at h
  change SFunc.RunCut fs sevm C
    (St b (memWord M 256 :: 256 :: s.length :: (256 + s.length) :: 192 :: 192 :: 128 :: R) M _) _ _ at h
  rw [word] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  rw [show Bytes.toB256 [0x01] = (1 : B256) from rfl] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  rw [show Bytes.toB256 [0x20] = (32 : B256) from rfl] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_sub hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  rw [show Bytes.toB256 [0x01, 0x00] = (256 : B256) from rfl] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_exp hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_sub hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_not hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  rw [s.masked] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_mstore hd
  rw [show (256 : B256).toNat = 256 from rfl] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_add hd
  rw [show Bytes.toB256 [0x20] + (256 : B256) = 288 from by decide] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  exact getterString_return_inv padded h

theorem getterString_exit_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} (s : StringGetter)
    (mem : PtrMem 192 288 M) (word : memWord M 256 = s.word) (room : R.length ≤ 1012) :
    SFunc.RunExact fs sevm
      (St b (32 :: 160 :: 256 :: s.length :: s.length :: 160 :: 256 :: 192 :: 192 :: 128 :: R) M (G + 197))
      t_029b_c39 (.halted (getterStringReturn b R (M.write 256 s.word.toBytes) G)) := by
  unfold t_029b_c39
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_swap1 ?_
  refine rx_pop ?_
  refine rx_swap1 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 256 + s.length) (by cases s <;> decide)
    (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_push (w := 31) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := s.length) (by cases s <;> decide)
    (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_iszero (v := 0) (by cases s <;> decide)
    (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x02c8) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_branchTo_zero ?_
  exact getterString_padding_exact (R := R) (G := G) s mem word (by omega)


theorem getterString_exit_inv {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {o : Outcome} (s : StringGetter)
    (mem : PtrMem 192 288 M) (word : memWord M 256 = s.word)
    (run : SFunc.Run cert.prog sevm
      (St b (32 :: 160 :: 256 :: s.length :: s.length :: 160 :: 256 :: 192 :: 192 :: 128 :: R) M G)
      t_029b_c39 o) :
    ∃ d, o = .halted d ∧ d.output = ((M.write 256 s.word.toBytes).read 192 96).1 ∧
      (∀ a, Devm.getStor d a = Devm.getStor b a) ∧ d.logs = b.logs := by
  have h := run.cut
  unfold t_029b_c39 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_add hd
  rw [show s.length + 256 = (256 + s.length : B256) from by cases s <;> decide] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  rw [show Bytes.toB256 [0x1f] &&& s.length = s.length from by cases s <;> decide] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_iszero hd
  rw [show B256.eqCheck s.length 0 = 0 from by cases s <;> decide] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branchTo (g := t_02c8_c1) (by intro hh; cases hh) (by rfl) h with h | h
  · obtain ⟨_, h⟩ := h.2
    obtain ⟨d, hr, out, stor, logs⟩ := getterString_padding_inv s mem word h
    exact ⟨d, Seg.done.inj hr, out, stor, logs⟩
  · exact False.elim (h.1 rfl)


theorem StringGetter.copy_wf (s : StringGetter) {R : List B256} (room : R.length ≤ 990) :
    CopyWf (160 : B256) (256 : B256) s.length
      (s.length :: 160 :: 256 :: 192 :: 192 :: 128 :: R) 256 1 where
  iter := fun j => by
    cases s with
    | name => change j < 1 ↔ 32 * j < 10; omega
    | symbol => change j < 1 ↔ 32 * j < 6; omega
  n32 := by decide
  dst32 := by decide
  src_le := by decide
  disj := by decide
  src_lt := by decide
  dst_lt := by decide
  room := by simp only [List.length_cons]; omega

theorem getterString_exit_avoids : t_029b_c39.avoids [39] [1] = true := by
  decide +kernel

theorem getterString_exit_closed :
    ∀ j f, j ∈ ([1] : List Nat) → cert.prog[j]? = some f → f.avoids [39] [1] = true := by
  intro j f hj hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  subst j
  have entry : cert.prog[1]? = some t_02c8_c1 := rfl
  rw [entry] at hf
  cases hf
  rfl

theorem getterString_copy_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat}
    (s : StringGetter) (mem : PtrMem 128 96 M) (room : R.length ≤ 990) :
    ∃ post, SFunc.RunExact cert.prog sevm
      (St b (0 :: 160 :: 256 :: s.length :: s.length :: 160 :: 256 :: 192 :: 192 :: 128 :: R)
        (getterStringHeads M s.length s.word) (G + 293)) t_0283_c100 (.halted post) ∧
      post.output = encodeWords [32, s.length, s.word] ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs ∧ post.gasLeft = G := by
  have hwf := s.copy_wf room
  have heads := getterStringHeads_ptr mem s.length s.word
  let result : Seg → Prop := fun r => ∃ post, r = .done (.halted post) ∧
    post.output = encodeWords [32, s.length, s.word] ∧
    (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs ∧ post.gasLeft = G
  obtain ⟨r, run, post, eq, out, stor, logs, gas⟩ := copy_loop
    (fs := cert.prog) (sevm := sevm) (b := b) (C := [])
    (e0 := 0x02) (e1 := 0x9b) (r0 := 0x02) (r1 := 0x83) (k := 39) (exitT := t_029b_c39)
    (img := getterStringHeadImage M s.length s.word)
    (by rfl) (by intro hh; cases hh) hwf (j0 := 0) (by decide) heads.wf
    ((getterStringHeads_reads mem s.length s.word).writeAt_nil 256)
    (by rw [heads.size]; rfl) (Gx := G + 197) result
    (fun copied wf reads size => by
      have size' : copied.size = 288 := by
        rw [show copySize 256 (256 : B256).toNat 1 = 288 from by decide] at size
        exact size
      obtain ⟨pointer, word, read⟩ := getterStringCopy_memory_facts s.length s.word wf reads size'
      let post := getterStringReturn b R (copied.write 256 s.word.toBytes) G
      have suffix := getterString_exit_exact (fs := cert.prog) (sevm := sevm) (b := b)
        (R := R) (G := G) s pointer word (by omega)
      refine ⟨.done (.halted post), suffix.toCut getterString_exit_closed getterString_exit_avoids, ?_, ?_⟩
      · intro d h; cases h
      · refine ⟨post, rfl, ?_, fun _ => rfl, rfl, rfl⟩
        dsimp only [post]
        rw [getterStringReturn, (returnPost_facts
          (St b (192 :: 96 :: R) (copied.write 256 s.word.toBytes) G) 192 96 R).1]
        simp only [St.memory, show (192 : B256).toNat = 192 from rfl,
          show (96 : B256).toNat = 96 from rfl]
        exact read)
  cases eq
  refine ⟨post, ?_, out, stor, logs, gas⟩
  rw [SFunc.runExact_iff_runExactCut_nil]
  have shape : t_0283_c100 = copyLoopTree 0x02 0x9b 0x02 0x83 39 t_029b_c39 := rfl
  rw [shape]
  simp only [show copyGas 256 (256 : B256).toNat 1 0 = 96 from by decide] at run
  exact run


theorem getterString_copy_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {o : Outcome}
    (s : StringGetter) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm
      (St b (0 :: 160 :: 256 :: s.length :: s.length :: 160 :: 256 :: 192 :: 192 :: 128 :: R)
        (getterStringHeads M s.length s.word) G) t_0283_c100 o) :
    ∃ d, o = .halted d ∧ d.output = encodeWords [32, s.length, s.word] ∧
      (∀ a, Devm.getStor d a = Devm.getStor b a) ∧ d.logs = b.logs := by
  have heads := getterStringHeads_ptr mem s.length s.word
  have source := (getterStringHeads_words mem s.length s.word).2
  have h := run.cut
  have first : t_0283_c100 = copyLoopTree 0x02 0x9b 0x02 0x83 39 t_029b_c39 := rfl
  have loop : t_0283_c39 = copyLoopTree 0x02 0x9b 0x02 0x83 39 t_029b_c39 := rfl
  rw [first] at h
  obtain ⟨_, h⟩ := ric_copy_step
    (by cases s <;> decide : B256.ltCheck (0 : B256) s.length = 1)
    (by rfl : cert.prog[39]? = some t_0283_c39) (by intro hh; cases hh) h
  simp only [show Bytes.toB256 [0x20] + (0 : B256) = 32 from by decide,
    show (0 : B256) + 160 = 160 from by decide,
    show (0 : B256) + 256 = 256 from by decide,
    show (160 : B256).toNat = 160 from rfl, show (256 : B256).toNat = 256 from rfl,
    heads.read_self (by decide : 160 + 32 ≤ 256),
    show Bytes.toB256 ((getterStringHeads M s.length s.word).read 160 32).1 = s.word from source] at h
  rw [loop] at h
  obtain ⟨_, h⟩ := ric_copy_exit
    (by cases s <;> decide : B256.ltCheck (32 : B256) s.length = 0) h
  obtain ⟨d, ho, out, stor, logs⟩ := getterString_exit_inv s
    (getterStringCopied_ptr mem s.length s.word) (getterStringCopied_word M s.length s.word) h.uncut
  have encoded := (getterStringPost_facts (b := b) (R := R) (G := 0)
    (L := s.length) (W := s.word) mem).1
  rw [getterStringPost, (returnPost_facts
    (St b (192 :: 96 :: R) (getterStringFinalMemory M s.length s.word) 0) 192 96 R).1] at encoded
  simp only [St.memory, show (192 : B256).toNat = 192 from rfl,
    show (96 : B256).toNat = 96 from rfl] at encoded
  exact ⟨d, ho, out.trans encoded, stor, logs⟩

theorem getterString_wrapper_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat}
    (s : StringGetter) (mem : PtrMem 128 96 M) (room : R.length ≤ 990) :
    ∃ post, SFunc.RunExact cert.prog sevm
      (St b (128 :: R) (getterStringMemory M s.length s.word) (G + 390)) t_0261_c100 (.halted post) ∧
      post.output = encodeWords [32, s.length, s.word] ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs ∧ post.gasLeft = G := by
  obtain ⟨post, copy, out, stor, logs, gas⟩ := getterString_copy_exact (sevm := sevm) (b := b) (G := G) s mem room
  have initial := getterStringMemory_ptr mem s.length s.word
  have head1 := getterStringHead1_ptr mem s.length s.word
  have heads := getterStringHeads_ptr mem s.length s.word
  have size1 : ((getterStringMemory M s.length s.word).write 192 (32 : B256).toBytes).size = 224 := head1.size
  have size2 : (((getterStringMemory M s.length s.word).write 192 (32 : B256).toBytes).write 224 s.length.toBytes).size = 256 := heads.size
  have len1 := getterStringHead1_length mem s.length s.word
  have len2 := (getterStringHeads_words mem s.length s.word).1
  refine ⟨post, ?_, out, stor, logs, gas⟩
  unfold t_0261_c100
  refine rx_dest ?_
  refine rx_push (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_mload (c := 3) ?_ initial.word (initial.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq initial.size]; decide
  refine rx_push (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 6) ?_ rfl ?_
  · rw [St.extCost_eq initial.size]; decide
  refine rx_dup4 (by simp only [List.length_cons]; omega) ?_
  refine rx_mload (c := 3) ?_ len1 (head1.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · simp only [show (192 : B256).toNat = 192 from rfl,
      show (128 : B256).toNat = 128 from rfl]
    rw [St.extCost_eq size1]; decide
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup4 (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 224) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 6) ?_ rfl ?_
  · simp only [show (192 : B256).toNat = 192 from rfl,
      show (224 : B256).toNat = 224 from rfl]
    rw [St.extCost_eq size1]; decide
  refine rx_dup4 (by simp only [List.length_cons]; omega) ?_
  refine rx_mload (c := 3) ?_ len2 (heads.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · simp only [show (192 : B256).toNat = 192 from rfl,
      show (128 : B256).toNat = 128 from rfl, show (224 : B256).toNat = 224 from rfl]
    rw [St.extCost_eq size2]; decide
  refine rx_swap2 ?_
  refine rx_swap3 ?_
  refine rx_dup4 (by simp only [List.length_cons]; omega) ?_
  refine rx_swap3 ?_
  refine rx_swap1 ?_
  refine rx_dup4 (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 256) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap2 ?_
  refine rx_dup (n := 5) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 160) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup4 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup4 (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  simp only [show (192 : B256).toNat = 192 from rfl,
    show (224 : B256).toNat = 224 from rfl]
  exact copy


theorem getterString_wrapper_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {o : Outcome}
    (s : StringGetter) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm
      (St b (128 :: R) (getterStringMemory M s.length s.word) G) t_0261_c100 o) :
    ∃ d, o = .halted d ∧ d.output = encodeWords [32, s.length, s.word] ∧
      (∀ a, Devm.getStor d a = Devm.getStor b a) ∧ d.logs = b.logs := by
  have initial := getterStringMemory_ptr mem s.length s.word
  have head1 := getterStringHead1_ptr mem s.length s.word
  have heads := getterStringHeads_ptr mem s.length s.word
  have len1 := getterStringHead1_length mem s.length s.word
  have len2 := (getterStringHeads_words mem s.length s.word).1
  have read1 : (((getterStringMemory M s.length s.word).write 192 (32 : B256).toBytes).read 128 32).2 =
      (getterStringMemory M s.length s.word).write 192 (32 : B256).toBytes := head1.read_self (by decide)
  have word1 : Bytes.toB256 (((getterStringMemory M s.length s.word).write 192 (32 : B256).toBytes).read 128 32).1 = s.length := len1
  have read2 : ((((getterStringMemory M s.length s.word).write 192 (32 : B256).toBytes).write 224 s.length.toBytes).read 128 32).2 =
      ((getterStringMemory M s.length s.word).write 192 (32 : B256).toBytes).write 224 s.length.toBytes := heads.read_self (by decide)
  have word2 : Bytes.toB256 ((((getterStringMemory M s.length s.word).write 192 (32 : B256).toBytes).write 224 s.length.toBytes).read 128 32).1 = s.length := len2
  have h := run.cut
  unfold t_0261_c100 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  rw [show Bytes.toB256 [0x40] = (64 : B256) from rfl] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mload hd
  simp only [show (64 : B256).toNat = 64 from rfl,
    initial.read_self (by decide : 64 + 32 ≤ 192),
    show Bytes.toB256 ((getterStringMemory M s.length s.word).read 64 32).1 = (192 : B256) from initial.word] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  rw [show Bytes.toB256 [0x20] = (32 : B256) from rfl] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_mstore hd
  rw [show (192 : B256).toNat = 192 from rfl] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mload hd
  simp only [show (128 : B256).toNat = 128 from rfl,
    read1, word1] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_add hd
  rw [show (192 : B256) + 32 = 224 from by decide] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_mstore hd
  rw [show (224 : B256).toNat = 224 from rfl] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mload hd
  simp only [show (128 : B256).toNat = 128 from rfl,
    read2, word2] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_add hd
  rw [show (192 : B256) + 64 = 256 from by decide] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_add hd
  rw [show (128 : B256) + 32 = 160 from by decide] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  rw [show Bytes.toB256 [0x00] = (0 : B256) from rfl] at h
  exact getterString_copy_inv s mem h.uncut


def StringGetter.calleeIndex : StringGetter → Nat
  | .name => 55
  | .symbol => 38

def StringGetter.targetHi : StringGetter → UInt8
  | .name => 0x0d
  | .symbol => 0x18

def StringGetter.targetLo : StringGetter → UInt8
  | .name => 0x57
  | .symbol => 0x92

def StringGetter.entryIndex : StringGetter → Nat
  | .name => 100
  | .symbol => 84

def StringGetter.entryTree : StringGetter → SFunc
  | .name => t_0259_c100
  | .symbol => t_0556_c84

def getterStringEntryTree (s : StringGetter) : SFunc :=
  .dest (.next (.push [0x02, 0x61] (by decide))
    (.next (.push [s.targetHi, s.targetLo] (by simp only [List.length_cons, List.length_nil]; decide))
      (.callNext s.calleeIndex t_0261_c100)))

theorem StringGetter.entry_shape (s : StringGetter) :
    s.entryTree = getterStringEntryTree s := by
  cases s <;> rfl

theorem StringGetter.callee_lookup (s : StringGetter) :
    cert.prog[s.calleeIndex]? = some s.callee := by
  cases s <;> rfl

theorem StringGetter.entry_lookup (s : StringGetter) :
    cert.prog[s.entryIndex]? = some s.entryTree := by
  cases s <;> rfl

theorem getterString_entry_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {sel : B256}
    (s : StringGetter) (mem : PtrMem 128 96 M) :
    ∃ post, SFunc.RunExact cert.prog sevm (St b [sel] M (G + 476)) s.entryTree (.halted post) ∧
      post.output = encodeWords [32, s.length, s.word] ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs ∧ post.gasLeft = G := by
  obtain ⟨post, wrapper, out, stor, logs, gas⟩ :=
    getterString_wrapper_exact (sevm := sevm) (b := b) (R := [0x0261, sel]) (G := G) s mem
      (by simp only [List.length_cons, List.length_nil]; decide)
  refine ⟨post, ?_, out, stor, logs, gas⟩
  rw [s.entry_shape]
  unfold getterStringEntryTree
  refine rx_dest ?_
  refine rx_push (w := 0x0261) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_callRet s.callee_lookup
    (getterString_callee_exact (G := G + 390) (R := [sel]) s mem
      (by simp only [List.length_cons, List.length_nil]; decide)) ?_
  exact wrapper

theorem getterString_entry_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {sel : B256} {o : Outcome}
    (s : StringGetter) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm (St b [sel] M G) s.entryTree o) :
    ∃ d, o = .halted d ∧ d.output = encodeWords [32, s.length, s.word] ∧
      (∀ a, Devm.getStor d a = Devm.getStor b a) ∧ d.logs = b.logs := by
  have h := run.cut
  rw [s.entry_shape] at h
  unfold getterStringEntryTree at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  rw [show Bytes.toB256 [0x02, 0x61] = (0x0261 : B256) from rfl] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨_, h⟩ := ric_call s.callee_lookup h
  rcases h with ⟨d, callee, h⟩ | ⟨d, callee, _⟩
  · obtain ⟨_, eq⟩ := getterString_callee_inv s mem callee
    cases eq
    exact getterString_wrapper_inv s mem h.uncut
  · obtain ⟨_, eq⟩ := getterString_callee_inv s mem callee
    cases eq


theorem getterString_guards_exact {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (body : SFunc.RunExact cert.prog sevm (St b [] getterInitMemory G) t_001a_c0 o) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + 63)) t_0000_c0 o := by
  unfold t_0000_c0
  refine rx_push (w := 128) rfl (by decide) ?_
  refine rx_push (w := 64) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_mstore (c := 12) ?_ rfl ?_
  · rw [St.extCost_eq (n := 0) rfl]; decide
  refine rx_callvalue (by decide) ?_
  rw [value]
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_iszero (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 16) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0010_c0
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push (w := 4) rfl (by decide) ?_
  refine rx_calldatasize (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_lt (v := 0) (ltCheck_zero_of_le size) (by decide) ?_
  refine rx_push (w := 0x01b9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  exact rx_branch_zero body

def StringGetter.dispatchGas : StringGetter → Nat
  | .name => 188
  | .symbol => 208

theorem getterString_dispatch_exact {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (s : StringGetter) (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = s.selector)
    (body : SFunc.RunExact cert.prog sevm (St b [s.selector] getterInitMemory G) s.entryTree o) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + s.dispatchGas)) t_0000_c0 o := by
  cases s with
  | name =>
    simp only [StringGetter.selector, StringGetter.entryTree, StringGetter.dispatchGas] at selector body ⊢
    refine getterString_guards_exact (G := G + 125) value size ?_
    unfold t_001a_c0
    refine rx_push (w := 0) rfl (by decide) ?_
    refine rx_calldataload (by decide) ?_
    refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_shr (v := 0x06fdde03) selector (by decide) ?_
    refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x00f9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_branch_succ (by decide) ?_
    unfold t_00f9_c0
    refine rx_dest ?_
    refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x23b872dd) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x0166) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_branch_succ (by decide) ?_
    unfold t_0166_c0
    refine rx_dest ?_
    refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x095ea7b3) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x0197) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_branch_succ (by decide) ?_
    unfold t_0197_c0
    refine rx_dest ?_
    refine cmp_miss (by decide) ?_
    unfold t_01a3_c0
    exact cmp_hit (tgt := t_0259_c100) rfl (StringGetter.entry_lookup .name) body
  | symbol =>
    simp only [StringGetter.selector, StringGetter.entryTree, StringGetter.dispatchGas] at selector body ⊢
    refine getterString_guards_exact (G := G + 145) value size ?_
    unfold t_001a_c0
    refine rx_push (w := 0) rfl (by decide) ?_
    refine rx_calldataload (by decide) ?_
    refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_shr (v := 0x95d89b41) selector (by decide) ?_
    refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x00f9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_branch_zero ?_
    unfold t_002b_c0
    refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0xba9a7a56) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x0097) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_branch_succ (by decide) ?_
    unfold t_0097_c0
    refine rx_dest ?_
    refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x7ecebe00) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_push (w := 0x00d3) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
    refine rx_branch_zero ?_
    unfold t_00a3_c0
    refine cmp_miss (by decide) ?_
    unfold t_00ae_c0
    refine cmp_miss (by decide) ?_
    unfold t_00b9_c0
    exact cmp_hit (tgt := t_0556_c84) rfl (StringGetter.entry_lookup .symbol) body

theorem getterString_pc0_exact {sevm : Sevm} {b : Devm} {G : Nat}
    (s : StringGetter) (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = s.selector) :
    ∃ post, SProg.RunExact cert.prog sevm (St b [] Mem.empty (G + 476 + s.dispatchGas)) post ∧
      post.output = encodeWords [32, s.length, s.word] ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs ∧ post.gasLeft = G := by
  obtain ⟨post, entry, out, stor, logs, gas⟩ :=
    getterString_entry_exact (sevm := sevm) (b := b) (sel := s.selector) (G := G) s getterInitMemory_ptr
  exact ⟨post, ⟨t_0000_c0, rfl, getterString_dispatch_exact s value size selector entry⟩,
    out, stor, logs, gas⟩


theorem getterString_selector_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (s : StringGetter) (selector : Blanc.Sevm.selector sevm = s.selector)
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
  | name =>
    simp only [StringGetter.selector, StringGetter.entryTree] at h ⊢
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_gt hd
    simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0x06fdde03 : B256) = (1 : B256) from by decide] at hd
    subst d
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨_, _, h⟩ := (ric_branch h).resolve_left
      (by rintro ⟨bad, _, _⟩; exact (by decide : (1 : B256) ≠ 0) bad)
    unfold t_00f9_c0 at h
    obtain ⟨_, h⟩ := ric_dest h
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_gt hd
    simp only [show B256.gtCheck (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd]) (0x06fdde03 : B256) = (1 : B256) from by decide] at hd
    subst d
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨_, _, h⟩ := (ric_branch h).resolve_left
      (by rintro ⟨bad, _, _⟩; exact (by decide : (1 : B256) ≠ 0) bad)
    unfold t_0166_c0 at h
    obtain ⟨_, h⟩ := ric_dest h
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_gt hd
    simp only [show B256.gtCheck (Bytes.toB256 [0x09, 0x5e, 0xa7, 0xb3]) (0x06fdde03 : B256) = (1 : B256) from by decide] at hd
    subst d
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨_, _, h⟩ := (ric_branch h).resolve_left
      (by rintro ⟨bad, _, _⟩; exact (by decide : (1 : B256) ≠ 0) bad)
    unfold t_0197_c0 at h
    obtain ⟨_, h⟩ := ric_dest h
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_eq hd
    simp only [show B256.eqCheck (Bytes.toB256 [0x02, 0x2c, 0x0d, 0x9f]) (0x06fdde03 : B256) = (0 : B256) from by decide] at hd
    subst d
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨_, _, h⟩ := (ric_branchTo (g := t_01be_c99) (by intro hh; cases hh) (by rfl) h).resolve_right
      (by rintro ⟨bad, _, _⟩; exact bad rfl)
    unfold t_01a3_c0 at h
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_eq hd
    simp only [show B256.eqCheck (Bytes.toB256 [0x06, 0xfd, 0xde, 0x03]) (0x06fdde03 : B256) = (1 : B256) from by decide] at hd
    subst d
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨_, _, h⟩ := (ric_branchTo (g := t_0259_c100) (by intro hh; cases hh) (by rfl) h).resolve_left
      (by rintro ⟨bad, _, _⟩; exact (by decide : (1 : B256) ≠ 0) bad)
    exact ⟨_, h.uncut⟩
  | symbol =>
    simp only [StringGetter.selector, StringGetter.entryTree] at h ⊢
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_gt hd
    simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0x95d89b41 : B256) = (0 : B256) from by decide] at hd
    subst d
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨_, _, h⟩ := (ric_branch h).resolve_right
      (by rintro ⟨bad, _, _⟩; exact bad rfl)
    unfold t_002b_c0 at h
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_gt hd
    simp only [show B256.gtCheck (Bytes.toB256 [0xba, 0x9a, 0x7a, 0x56]) (0x95d89b41 : B256) = (1 : B256) from by decide] at hd
    subst d
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨_, _, h⟩ := (ric_branch h).resolve_left
      (by rintro ⟨bad, _, _⟩; exact (by decide : (1 : B256) ≠ 0) bad)
    unfold t_0097_c0 at h
    obtain ⟨_, h⟩ := ric_dest h
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_gt hd
    simp only [show B256.gtCheck (Bytes.toB256 [0x7e, 0xce, 0xbe, 0x00]) (0x95d89b41 : B256) = (0 : B256) from by decide] at hd
    subst d
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨_, _, h⟩ := (ric_branch h).resolve_right
      (by rintro ⟨bad, _, _⟩; exact bad rfl)
    unfold t_00a3_c0 at h
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_eq hd
    simp only [show B256.eqCheck (Bytes.toB256 [0x7e, 0xce, 0xbe, 0x00]) (0x95d89b41 : B256) = (0 : B256) from by decide] at hd
    subst d
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨_, _, h⟩ := (ric_branchTo (g := t_04d7_c82) (by intro hh; cases hh) (by rfl) h).resolve_right
      (by rintro ⟨bad, _, _⟩; exact bad rfl)
    unfold t_00ae_c0 at h
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_eq hd
    simp only [show B256.eqCheck (Bytes.toB256 [0x89, 0xaf, 0xcb, 0x44]) (0x95d89b41 : B256) = (0 : B256) from by decide] at hd
    subst d
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨_, _, h⟩ := (ric_branchTo (g := t_050a_c83) (by intro hh; cases hh) (by rfl) h).resolve_right
      (by rintro ⟨bad, _, _⟩; exact bad rfl)
    unfold t_00b9_c0 at h
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_eq hd
    simp only [show B256.eqCheck (Bytes.toB256 [0x95, 0xd8, 0x9b, 0x41]) (0x95d89b41 : B256) = (1 : B256) from by decide] at hd
    subst d
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨_, _, h⟩ := (ric_branchTo (g := t_0556_c84) (by intro hh; cases hh) (by rfl) h).resolve_left
      (by rintro ⟨bad, _, _⟩; exact (by decide : (1 : B256) ≠ 0) bad)
    exact ⟨_, h.uncut⟩

theorem getterString_pc0_inv {sevm : Sevm} {b post : Devm} {G : Nat}
    (s : StringGetter) (selector : Blanc.Sevm.selector sevm = s.selector)
    (run : SProg.Run cert.prog sevm (St b [] Mem.empty G) post) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      post.output = encodeWords [32, s.length, s.word] ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  obtain ⟨f, entry, run⟩ := run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨value, size, _, run⟩ := getter_guards_inv run
  obtain ⟨_, run⟩ := getterString_selector_inv s selector run
  obtain ⟨d, eq, out, stor, logs⟩ := getterString_entry_inv s getterInitMemory_ptr run
  cases eq
  exact ⟨value, size, out, stor, logs⟩

/-- Any successful actual pc-zero name or symbol call refines the source result. -/
theorem getterString_bytecode_refines {sevm : Sevm} {b post : Devm} {G : Nat} (st : State)
    (s : StringGetter) (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = s.selector)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      some post.output = getterResult st s.entry ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  obtain ⟨value, size, out, stor, logs⟩ :=
    getterString_pc0_inv s selector (lift_sound cert_check codeEq fork run)
  exact ⟨value, size, by rw [out, s.result st], stor, logs⟩

/-- Pc-zero liveness: name uses664 gas, symbol684, and both return the exact source ABI image. -/
theorem getterString_bytecode_live {sevm : Sevm} {b : Devm} {G : Nat} (st : State)
    (s : StringGetter) (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = s.selector) :
    ∃ post, Nonempty (Exec 0 sevm (St b [] Mem.empty (G + 476 + s.dispatchGas)) (.ok post)) ∧
      post.gasLeft = G ∧ some post.output = getterResult st s.entry ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  obtain ⟨post, run, out, stor, logs, gas⟩ := getterString_pc0_exact s value size selector
  exact ⟨post, lift_exact cert_check jumps_ok codeEq fork run, gas,
    by rw [out, s.result st], stor, logs⟩

end Blanc.Lift.UniswapV2Pair
