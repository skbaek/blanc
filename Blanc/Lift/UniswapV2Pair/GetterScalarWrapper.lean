import Blanc.Lift.UniswapV2Pair.GetterScalarCore

/-! The actual uint8 and address masks in the Pair's scalar return wrappers. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

inductive MaskedScalar
  | decimals | address

def MaskedScalar.bytes (s : MaskedScalar) : Bytes :=
  0xff :: (match s with | .decimals => [] | .address => List.replicate 19 0xff)

theorem MaskedScalar.bytes_bound (s : MaskedScalar) : s.bytes.length ≤ 32 := by
  cases s <;> decide

def MaskedScalar.tailTree : MaskedScalar → SFunc
  | .decimals => t_0400_c95
  | .address => t_036a_c75

theorem MaskedScalar.tail_shape (s : MaskedScalar) :
    s.tailTree = (.dest (.next (.push [0x40] (by decide)) (.next (.reg (.dup 0)) (.next (.reg .mload) (.next (.push s.bytes s.bytes_bound) (.next (.reg (.swap 0)) (.next (.reg (.swap 2)) (.next (.reg .and) (.next (.reg (.dup 2)) (.next (.reg .mstore) (.next (.reg .mload) (.next (.reg (.swap 0)) (.next (.reg (.dup 1)) (.next (.reg (.swap 0)) (.next (.reg .sub) (.next (.push [0x20] (by decide)) (.next (.reg .add) (.next (.reg (.swap 0)) (.last .return_))))))))))))))))))) := by
  cases s <;> rfl

theorem getterMasked_tail_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {v : B256}
    (s : MaskedScalar) (clean : v &&& Bytes.toB256 s.bytes = v)
    (mem : PtrMem 128 96 M) (room : R.length ≤ 1019) :
    SFunc.RunExact fs sevm (St b (v :: R) M (G + 58)) s.tailTree
      (.halted (getterWordPost b R M v G)) := by
  have outmem := getterWordMemory_ptr mem v
  rw [s.tail_shape]
  refine rx_dest ?_
  refine rx_push (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_mload (c := 3) ?_ mem.word (mem.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq mem.size]
    decide
  refine rx_push (w := Bytes.toB256 s.bytes) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_swap3 ?_
  refine rx_and clean (by simp only [List.length_cons]; omega) ?_
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 9) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]
    decide
  refine rx_mload (c := 3) ?_ outmem.word (outmem.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · simp only [show (128 : B256).toNat = 128 from rfl]
    rw [St.extCost_eq outmem.size]
    decide
  refine rx_swap1 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_sub' (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 32) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  exact rx_return_any rfl (by
    simp only [show (128 : B256).toNat = 128 from rfl]
    rw [St.extCost_eq outmem.size]
    decide)


theorem getterMasked_tail_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {v : B256} {o : Outcome}
    (s : MaskedScalar) (clean : v &&& Bytes.toB256 s.bytes = v)
    (mem : PtrMem 128 96 M)
    (run : SFunc.Run fs sevm (St b (v :: R) M G) s.tailTree o) :
    ∃ d, o = .halted d ∧ d.output = v.toBytes ∧
      (∀ a, Devm.getStor d a = Devm.getStor b a) ∧ d.logs = b.logs := by
  have outmem := getterWordMemory_ptr mem v
  have h := run.cut
  rw [s.tail_shape] at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mload hd
  simp only [show Bytes.toB256 [0x40] = (64 : B256) from rfl,
    show (64 : B256).toNat = 64 from rfl,
    mem.read_self (by decide : 64 + 32 ≤ 96), show Bytes.toB256 (M.read 64 32).1 = (128 : B256) from mem.word] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_and hd
  rw [clean] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (128 : B256).toNat = 128 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mload hd
  simp only [show (64 : B256).toNat = 64 from rfl,
    outmem.read_self (by decide : 64 + 32 ≤ 160), show Bytes.toB256 ((M.write 128 v.toBytes).read 64 32).1 = (128 : B256) from outmem.word] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_sub hd
  simp only [show (128 : B256) - 128 = 0 from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_add hd
  simp only [show Bytes.toB256 [0x20] = (32 : B256) from rfl,
    show (32 : B256) + 0 = 32 from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  cases h with
  | last hr =>
    obtain ⟨hout, hstor, hlogs⟩ := ri_return hr
    refine ⟨_, rfl, ?_, hstor, hlogs⟩
    rw [hout]
    exact Mem.read_write_word_of_wf mem.wf 128 v


theorem getterScalar_callee_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G c : Nat} {ρ : B256}
    (s : ScalarGetter) (fork : CoveredFork sevm.benvStat.fork)
    (cost : c = s.loadGas sevm b) (room : R.length ≤ 1020) :
    SFunc.RunExact fs sevm (St b (ρ :: R) M (G + c + s.calleeGas)) s.callee
      (.returned (St (s.after sevm b) (s.value sevm b :: ρ :: R) M G)) := by
  cases s with
  | constant s =>
    change c = 0 at cost
    subst c
    exact constantScalar_callee_exact s (by omega)
  | stored s => exact storedScalar_callee_exact s fork cost (by omega)
  | address s => exact addressScalar_callee_exact s fork cost room

theorem getterScalar_callee_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {ρ : B256} {o : Outcome}
    (s : ScalarGetter) (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run fs sevm (St b (ρ :: R) M G) s.callee o) :
    ∃ G', o = .returned (St (s.after sevm b) (s.value sevm b :: ρ :: R) M G') := by
  cases s with
  | constant s => exact constantScalar_callee_inv s run
  | stored s => exact storedScalar_callee_inv s fork run
  | address s => exact addressScalar_callee_inv s fork run

theorem getterScalar_tail_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} (s : ScalarGetter)
    (mem : PtrMem 128 96 M) (room : R.length ≤ 1019) :
    SFunc.RunExact fs sevm
      (St (s.after sevm b) (s.value sevm b :: R) M (G + s.tailGas)) s.tailTree
      (.halted (getterWordPost (s.after sevm b) R M (s.value sevm b) G)) := by
  cases s with
  | constant s =>
    cases s with
    | decimals => exact getterMasked_tail_exact .decimals (by change (18 : B256) &&& 255 = 18; decide) mem room
    | minimumLiquidity => exact getterWord_tail_exact mem room
    | permitTypehash => exact getterWord_tail_exact mem room
  | stored s => exact getterWord_tail_exact mem room
  | address s =>
    refine getterMasked_tail_exact .address ?_ mem room
    rw [B256.and_comm]
    exact ff20_and_adr _

theorem getterScalar_tail_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {o : Outcome} (s : ScalarGetter)
    (mem : PtrMem 128 96 M)
    (run : SFunc.Run fs sevm
      (St (s.after sevm b) (s.value sevm b :: R) M G) s.tailTree o) :
    ∃ d, o = .halted d ∧ d.output = (s.value sevm b).toBytes ∧
      (∀ a, Devm.getStor d a = Devm.getStor (s.after sevm b) a) ∧
      d.logs = (s.after sevm b).logs := by
  cases s with
  | constant s =>
    cases s with
    | decimals => exact getterMasked_tail_inv .decimals (by change (18 : B256) &&& 255 = 18; decide) mem run
    | minimumLiquidity => exact getterWord_tail_inv mem run
    | permitTypehash => exact getterWord_tail_inv mem run
  | stored s => exact getterWord_tail_inv mem run
  | address s =>
    refine getterMasked_tail_inv .address ?_ mem run
    rw [B256.and_comm]
    exact ff20_and_adr _

theorem getterScalar_entry_exact {sevm : Sevm} {b : Devm}
    {M : Mem} {G c : Nat} {sel : B256} (s : ScalarGetter)
    (fork : CoveredFork sevm.benvStat.fork) (cost : c = s.loadGas sevm b)
    (mem : PtrMem 128 96 M) :
    SFunc.RunExact cert.prog sevm (St b [sel] M (G + c + s.entryGas)) s.entryTree
      (.halted (getterWordPost (s.after sevm b) [s.tag, sel] M (s.value sevm b) G)) := by
  rw [s.entry_shape]
  have gas : G + c + s.entryGas = (((G + s.tailGas) + c + s.calleeGas) + 8) + 3 + 3 + 1 := by
    unfold ScalarGetter.entryGas
    omega
  rw [gas]
  refine rx_dest ?_
  refine rx_push (w := s.tag) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_callRet s.callee_lookup
    (getterScalar_callee_exact s fork cost (by simp only [List.length_cons, List.length_nil]; decide)) ?_
  exact getterScalar_tail_exact s mem (by simp only [List.length_cons, List.length_nil]; decide)

theorem getterScalar_entry_inv {sevm : Sevm} {b : Devm}
    {M : Mem} {G : Nat} {sel : B256} {o : Outcome} (s : ScalarGetter)
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm (St b [sel] M G) s.entryTree o) :
    ∃ d, o = .halted d ∧ d.output = (s.value sevm b).toBytes ∧
      (∀ a, Devm.getStor d a = Devm.getStor b a) ∧ d.logs = b.logs := by
  have h := run.cut
  rw [s.entry_shape] at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨_, h⟩ := ric_call s.callee_lookup h
  rcases h with ⟨d, hc, h⟩ | ⟨d, hc, _⟩
  · obtain ⟨_, eq⟩ := getterScalar_callee_inv s fork hc
    cases eq
    obtain ⟨d, ho, hout, hs, hl⟩ := getterScalar_tail_inv s mem h.uncut
    exact ⟨d, ho, hout, fun a => (hs a).trans (s.after_storage sevm b a), hl.trans (s.after_logs sevm b)⟩
  · obtain ⟨_, eq⟩ := getterScalar_callee_inv s fork hc
    cases eq

end Blanc.Lift.UniswapV2Pair
