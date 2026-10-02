import Blanc.Lift.UniswapV2Pair.GetterScalarWalk

/-! Single-key storage getters use the compiler's exact scratch-write order. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

inductive SingleMappingGetter
  | balanceOf | nonces

def SingleMappingGetter.baseByte : SingleMappingGetter → UInt8
  | .balanceOf => 1
  | .nonces => 4

def SingleMappingGetter.base (s : SingleMappingGetter) : B256 :=
  Bytes.toB256 [s.baseByte]

def SingleMappingGetter.callee : SingleMappingGetter → SFunc
  | .balanceOf => t_13cb_c42
  | .nonces => t_13e3_c36

def SingleMappingGetter.memory (s : SingleMappingGetter) (M : Mem) (key : B256) : Mem :=
  (M.write 32 s.base.toBytes).write 0 key.toBytes

theorem SingleMappingGetter.memory_ptr {M : Mem} (s : SingleMappingGetter)
    (mem : PtrMem 128 96 M) (key : B256) :
    PtrMem 128 96 (s.memory M key) := by
  have base := mem.write 32 s.base (Or.inl (by decide))
  rw [show memExtSize 96 32 32 = 96 from by decide] at base
  have k := base.write 0 key (Or.inl (by decide))
  rw [show memExtSize 96 0 32 = 96 from by decide] at k
  exact k

theorem SingleMappingGetter.callee_shape (s : SingleMappingGetter) :
    s.callee = .dest (.next (.push [s.baseByte] (by simp only [List.length_cons, List.length_nil]; decide))
      (.next (.push [0x20] (by decide)) (.next (.reg .mstore)
      (.next (.push [0] (by decide)) (.next (.reg (.swap 0)) (.next (.reg (.dup 1))
      (.next (.reg .mstore) (.next (.push [0x40] (by decide)) (.next (.reg (.swap 0))
      (.next (.reg .keccak256) (.next (.reg .sload) (.next (.reg (.dup 1)) .ret)))))))))))) := by
  cases s <;> rfl

theorem singleMapping_callee_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G c : Nat} {key ρ : B256} (s : SingleMappingGetter)
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (cost : c = sloadCost sevm b (mapSlot key s.base)) (room : R.length ≤ 1019) :
    SFunc.RunExact fs sevm (St b (key :: ρ :: R) M (G + c + 81)) s.callee
      (.returned (St (afterSload sevm b (mapSlot key s.base))
        (b.getStorVal sevm.currentTarget (mapSlot key s.base) :: ρ :: R)
        (s.memory M key) G)) := by
  have base := mem.write 32 s.base (Or.inl (by decide))
  rw [show memExtSize 96 32 32 = 96 from by decide] at base
  have outmem := s.memory_ptr mem key
  rw [s.callee_shape]
  refine rx_dest ?_
  refine rx_push (w := s.base) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]; decide
  refine rx_push (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · simp only [show (32 : B256).toNat = 32 from rfl]
    rw [St.extCost_eq base.size]; decide
  refine rx_push (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  simp only [show (32 : B256).toNat = 32 from rfl,
    show (0 : B256).toNat = 0 from rfl]
  have gas : G + c + 53 = (G + c + 11) + 42 := by omega
  rw [gas]
  refine rx_keccak (v := mapSlot key s.base) (c := 42) ?_ ?_ (outmem.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · simp only [show (0 : B256).toNat = 0 from rfl, show (64 : B256).toNat = 64 from rfl]
    have size : ((M.write 32 s.base.toBytes).write 0 key.toBytes).size = 96 := outmem.size
    rw [St.extCost_eq size]; decide
  · simp only [show (0 : B256).toNat = 0 from rfl, show (64 : B256).toNat = 64 from rfl]
    rw [Mem.read_two_word_writes_at_raw_right_first M 0 key s.base]
    rfl
  have gas : G + c + 11 = (G + 11) + c := by omega
  rw [gas]
  refine rx_sload_selC fork cost (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  exact rx_ret

theorem singleMapping_callee_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {key ρ : B256} {o : Outcome}
    (s : SingleMappingGetter) (fork : CoveredFork sevm.benvStat.fork)
    (mem : PtrMem 128 96 M)
    (run : SFunc.Run fs sevm (St b (key :: ρ :: R) M G) s.callee o) :
    ∃ G', o = .returned (St (afterSload sevm b (mapSlot key s.base))
      (b.getStorVal sevm.currentTarget (mapSlot key s.base) :: ρ :: R)
      (s.memory M key) G') := by
  have h := run.cut
  rw [s.callee_shape] at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mstore hd
  rw [show (Bytes.toB256 [0x20]).toNat = 32 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mstore hd
  rw [show (Bytes.toB256 [0]).toNat = 0 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_keccak hd
  change d = St b (((s.memory M key).read 0 64).1.keccak :: ρ :: R)
    ((s.memory M key).read 0 64).2 _ at hd
  have read : ((s.memory M key).read 0 64).1 = key.toBytes ++ s.base.toBytes :=
    Mem.read_two_word_writes_at_raw_right_first M 0 key s.base
  rw [(s.memory_ptr mem key).read_self (by decide), read] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := ρ) rfl hd
  obtain ⟨g, hg⟩ := ric_ret h
  exact ⟨g, Seg.done.inj hg⟩


def allowanceScratch1 (M : Mem) (owner : B256) : Mem :=
  (M.write 32 (2 : B256).toBytes).write 0 owner.toBytes

def allowanceScratch2 (M : Mem) (owner spender : B256) : Mem :=
  ((allowanceScratch1 M owner).write 32 (mapSlot owner 2).toBytes).write 0 spender.toBytes

theorem allowanceScratch1_ptr {M : Mem} (mem : PtrMem 128 96 M) (owner : B256) :
    PtrMem 128 96 (allowanceScratch1 M owner) := by
  have b := mem.write 32 2 (Or.inl (by decide))
  rw [show memExtSize 96 32 32 = 96 from by decide] at b
  have k := b.write 0 owner (Or.inl (by decide))
  rw [show memExtSize 96 0 32 = 96 from by decide] at k
  exact k

theorem allowanceScratch2_ptr {M : Mem} (mem : PtrMem 128 96 M) (owner spender : B256) :
    PtrMem 128 96 (allowanceScratch2 M owner spender) := by
  have b := (allowanceScratch1_ptr mem owner).write 32 (mapSlot owner 2) (Or.inl (by decide))
  rw [show memExtSize 96 32 32 = 96 from by decide] at b
  have k := b.write 0 spender (Or.inl (by decide))
  rw [show memExtSize 96 0 32 = 96 from by decide] at k
  exact k

theorem allowance_callee_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G c : Nat} {owner spender ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (cost : c = sloadCost sevm b (mapSlot spender (mapSlot owner 2)))
    (room : R.length ≤ 1017) :
    SFunc.RunExact fs sevm (St b (spender :: owner :: ρ :: R) M (G + c + 153))
      t_1dd8_c30 (.returned (St (afterSload sevm b (mapSlot spender (mapSlot owner 2)))
        (b.getStorVal sevm.currentTarget (mapSlot spender (mapSlot owner 2)) :: ρ :: R)
        (allowanceScratch2 M owner spender) G)) := by
  have base := mem.write 32 2 (Or.inl (by decide))
  rw [show memExtSize 96 32 32 = 96 from by decide] at base
  have m1 := allowanceScratch1_ptr mem owner
  have inner := m1.write 32 (mapSlot owner 2) (Or.inl (by decide))
  rw [show memExtSize 96 32 32 = 96 from by decide] at inner
  have m2 := allowanceScratch2_ptr mem owner spender
  unfold t_1dd8_c30
  refine rx_dest ?_
  refine rx_push (w := 2) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]; decide
  refine rx_push (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap3 ?_
  refine rx_dup4 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · simp only [show (32 : B256).toNat = 32 from rfl]
    rw [St.extCost_eq base.size]; decide
  refine rx_push (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons]; omega) ?_
  simp only [show (32 : B256).toNat = 32 from rfl, show (0 : B256).toNat = 0 from rfl]
  have gas : G + c + 116 = (G + c + 74) + 42 := by omega
  rw [gas]
  refine rx_keccak (v := mapSlot owner 2) (c := 42) ?_ ?_ (m1.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · have size : ((M.write 32 (2 : B256).toBytes).write 0 owner.toBytes).size = 96 := m1.size
    rw [St.extCost_eq size]; decide
  · exact congrArg Bytes.keccak (Mem.read_two_word_writes_at_raw_right_first M 0 owner 2)
  refine rx_swap1 ?_
  refine rx_swap2 ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · have size : ((M.write 32 (2 : B256).toBytes).write 0 owner.toBytes).size = 96 := m1.size
    rw [St.extCost_eq size]; decide
  refine rx_swap1 ?_
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · simp only [show (32 : B256).toNat = 32 from rfl]
    have size : (((M.write 32 (2 : B256).toBytes).write 0 owner.toBytes).write 32 (mapSlot owner 2).toBytes).size = 96 := inner.size
    rw [St.extCost_eq size]; decide
  refine rx_swap1 ?_
  simp only [show (32 : B256).toNat = 32 from rfl, show (0 : B256).toNat = 0 from rfl]
  have gas : G + c + 53 = (G + c + 11) + 42 := by omega
  rw [gas]
  refine rx_keccak (v := mapSlot spender (mapSlot owner 2)) (c := 42) ?_ ?_
    (m2.read_self (by decide)) (by simp only [List.length_cons]; omega) ?_
  · have size : ((((M.write 32 (2 : B256).toBytes).write 0 owner.toBytes).write 32 (mapSlot owner 2).toBytes).write 0 spender.toBytes).size = 96 := m2.size
    rw [St.extCost_eq size]; decide
  · exact congrArg Bytes.keccak (Mem.read_two_word_writes_at_raw_right_first (allowanceScratch1 M owner) 0 spender (mapSlot owner 2))
  have gas : G + c + 11 = (G + 11) + c := by omega
  rw [gas]
  refine rx_sload_selC fork cost (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  exact rx_ret

theorem allowance_callee_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {owner spender ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run fs sevm (St b (spender :: owner :: ρ :: R) M G) t_1dd8_c30 o) :
    ∃ G', o = .returned (St (afterSload sevm b (mapSlot spender (mapSlot owner 2)))
      (b.getStorVal sevm.currentTarget (mapSlot spender (mapSlot owner 2)) :: ρ :: R)
      (allowanceScratch2 M owner spender) G') := by
  have h := run.cut
  unfold t_1dd8_c30 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mstore hd
  rw [show (Bytes.toB256 [0x20]).toNat = 32 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mstore hd
  rw [show (Bytes.toB256 [0]).toNat = 0 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_keccak hd
  change d = St b (((allowanceScratch1 M owner).read 0 64).1.keccak :: 64 :: 32 :: spender :: 0 :: ρ :: R)
    ((allowanceScratch1 M owner).read 0 64).2 _ at hd
  have read1 : ((allowanceScratch1 M owner).read 0 64).1 = owner.toBytes ++ (2 : B256).toBytes :=
    Mem.read_two_word_writes_at_raw_right_first M 0 owner 2
  rw [(allowanceScratch1_ptr mem owner).read_self (by decide), read1] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (32 : B256).toNat = 32 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (0 : B256).toNat = 0 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_keccak hd
  change d = St b (((allowanceScratch2 M owner spender).read 0 64).1.keccak :: ρ :: R)
    ((allowanceScratch2 M owner spender).read 0 64).2 _ at hd
  have read2 : ((allowanceScratch2 M owner spender).read 0 64).1 = spender.toBytes ++ (mapSlot owner 2).toBytes :=
    Mem.read_two_word_writes_at_raw_right_first (allowanceScratch1 M owner) 0 spender (mapSlot owner 2)
  rw [(allowanceScratch2_ptr mem owner spender).read_self (by decide), read2] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := ρ) rfl hd
  obtain ⟨g, hg⟩ := ric_ret h
  exact ⟨g, Seg.done.inj hg⟩

end Blanc.Lift.UniswapV2Pair
