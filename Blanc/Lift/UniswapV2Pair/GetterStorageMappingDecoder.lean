import Blanc.Lift.UniswapV2Pair.GetterStorageMappingCore

/-! The real solc calldata guards and address masks for single-key getters. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def SingleMappingGetter.entryTree : SingleMappingGetter → SFunc
  | .balanceOf => t_049c_c87
  | .nonces => t_04d7_c82

def SingleMappingGetter.decoder : SingleMappingGetter → SFunc
  | .balanceOf => t_04b2_c87
  | .nonces => t_04ed_c82

def SingleMappingGetter.reject : SingleMappingGetter → SFunc
  | .balanceOf => t_04ae_c87
  | .nonces => t_04e9_c82

def SingleMappingGetter.decoderLo : SingleMappingGetter → UInt8
  | .balanceOf => 0xb2
  | .nonces => 0xed

def SingleMappingGetter.calleeLo : SingleMappingGetter → UInt8
  | .balanceOf => 0xcb
  | .nonces => 0xe3

def SingleMappingGetter.calleeIndex : SingleMappingGetter → Nat
  | .balanceOf => 42
  | .nonces => 36

def SingleMappingGetter.selector : SingleMappingGetter → B256
  | .balanceOf => 0x70a08231
  | .nonces => 0x7ecebe00

def SingleMappingGetter.entry (s : SingleMappingGetter) (owner : Adr) : Entry :=
  match s with
  | .balanceOf => .balanceOf owner
  | .nonces => .nonces owner

def mappingOwner (sevm : Sevm) : Adr := (Sevm.dataWord sevm 4).toAdr

def SingleMappingGetter.slot (s : SingleMappingGetter) (sevm : Sevm) : B256 :=
  mapSlot (mappingOwner sevm).toB256 s.base

def SingleMappingGetter.SlotMatches (s : SingleMappingGetter) (st : State) (sevm : Sevm) (b : Devm) : Prop :=
  match s with
  | .balanceOf => st.balanceOf (mappingOwner sevm) = b.getStorVal sevm.currentTarget (s.slot sevm)
  | .nonces => st.nonces (mappingOwner sevm) = b.getStorVal sevm.currentTarget (s.slot sevm)

theorem SingleMappingGetter.callee_lookup (s : SingleMappingGetter) :
    cert.prog[s.calleeIndex]? = some s.callee := by
  cases s <;> rfl

theorem SingleMappingGetter.decoder_shape (s : SingleMappingGetter) :
    s.decoder = .dest (.next (.reg .pop) (.next (.reg .calldataload)
      (.next (.push (List.replicate 20 0xff) (by decide)) (.next (.reg .and)
      (.next (.push [0x13, s.calleeLo] (by simp only [List.length_cons, List.length_nil]; decide))
      (.callNext s.calleeIndex t_039b_c98)))))) := by
  cases s <;> rfl

theorem SingleMappingGetter.entry_shape (s : SingleMappingGetter) :
    s.entryTree = .dest (.next (.push [0x03, 0x9b] (by decide))
      (.next (.push [0x04] (by decide)) (.next (.reg (.dup 0))
      (.next (.reg .calldatasize) (.next (.reg .sub) (.next (.push [0x20] (by decide))
      (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.reg .iszero)
      (.next (.push [0x04, s.decoderLo] (by simp only [List.length_cons, List.length_nil]; decide))
      (.branch s.reject s.decoder))))))))))) := by
  cases s <;> rfl

theorem singleMapping_decoder_exact {sevm : Sevm} {b : Devm} {M : Mem}
    {G c : Nat} {sel : B256} {avail : B256} (s : SingleMappingGetter)
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (cost : c = sloadCost sevm b (s.slot sevm)) :
    SFunc.RunExact cert.prog sevm (St b [avail, 4, 0x039b, sel] M (G + c + 153))
      s.decoder (.halted (getterWordPost (afterSload sevm b (s.slot sevm))
        [0x039b, sel] (s.memory M (mappingOwner sevm).toB256)
        (b.getStorVal sevm.currentTarget (s.slot sevm)) G)) := by
  have outmem := s.memory_ptr mem (mappingOwner sevm).toB256
  rw [s.decoder_shape]
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := ~~~ addressMask) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_and (addressSlotReadWord_eq_toAdr_toB256 _) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  have gas : G + c + 138 = ((G + 49) + c + 81) + 8 := by omega
  rw [gas]
  refine rx_callRet s.callee_lookup
    (singleMapping_callee_exact s fork mem cost (by simp only [List.length_cons, List.length_nil]; decide)) ?_
  exact getterWord_tail_exact outmem (by simp only [List.length_cons, List.length_nil]; decide)

theorem singleMapping_entry_exact {sevm : Sevm} {b : Devm} {M : Mem}
    {G c : Nat} {sel : B256} (s : SingleMappingGetter)
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (cost : c = sloadCost sevm b (s.slot sevm)) :
    SFunc.RunExact cert.prog sevm (St b [sel] M (G + c + 193)) s.entryTree
      (.halted (getterWordPost (afterSload sevm b (s.slot sevm)) [0x039b, sel]
        (s.memory M (mappingOwner sevm).toB256)
        (b.getStorVal sevm.currentTarget (s.slot sevm)) G)) := by
  rw [s.entry_shape]
  refine rx_dest ?_
  refine rx_push (w := 0x039b) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 4) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_calldatasize (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_sub' (v := sevm.data.length.toB256 - 4) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_dup2 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_lt (v := 0) (ltCheck_zero_of_le guard) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_iszero (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_succ (by decide) ?_
  exact singleMapping_decoder_exact s fork mem cost

theorem singleMapping_decoder_inv {sevm : Sevm} {b : Devm} {M : Mem}
    {G : Nat} {sel avail : B256} {o : Outcome} (s : SingleMappingGetter)
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm (St b [avail, 4, 0x039b, sel] M G) s.decoder o) :
    ∃ d, o = .halted d ∧ d.output = (b.getStorVal sevm.currentTarget (s.slot sevm)).toBytes ∧
      (∀ a, Devm.getStor d a = Devm.getStor b a) ∧ d.logs = b.logs := by
  have h := run.cut
  rw [s.decoder_shape] at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_calldataload hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_and hd
  change d = St b ((Bytes.toB256 (List.replicate 20 0xff) &&& (Sevm.dataWord sevm 4)) :: 0x039b :: sel :: []) M _ at hd
  rw [show Bytes.toB256 (List.replicate 20 0xff) = ~~~ addressMask from by decide,
    show ((~~~ addressMask) &&& (Sevm.dataWord sevm 4)) = (mappingOwner sevm).toB256 from addressSlotReadWord_eq_toAdr_toB256 _] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨_, h⟩ := ric_call s.callee_lookup h
  rcases h with ⟨d, hc, h⟩ | ⟨d, hc, _⟩
  · obtain ⟨_, eq⟩ := singleMapping_callee_inv s fork mem hc
    cases eq
    obtain ⟨d, ho, hout, hs, hl⟩ := getterWord_tail_inv (s.memory_ptr mem (mappingOwner sevm).toB256) h.uncut
    exact ⟨d, ho, hout, fun a => (hs a).trans (afterSload_getStor _ _ _ _), hl.trans (afterSload_logs _ _ _)⟩
  · obtain ⟨_, eq⟩ := singleMapping_callee_inv s fork mem hc
    cases eq

theorem singleMapping_entry_inv {sevm : Sevm} {b : Devm} {M : Mem}
    {G : Nat} {sel : B256} {o : Outcome} (s : SingleMappingGetter)
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm (St b [sel] M G) s.entryTree o) :
    (32 : B256) ≤ sevm.data.length.toB256 - 4 ∧
      ∃ d, o = .halted d ∧ d.output = (b.getStorVal sevm.currentTarget (s.slot sevm)).toBytes ∧
        (∀ a, Devm.getStor d a = Devm.getStor b a) ∧ d.logs = b.logs := by
  have h := run.cut
  rw [s.entry_shape] at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_calldatasize hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_sub hd
  rw [show Bytes.toB256 [0x04] = (4 : B256) from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_lt hd
  rw [show Bytes.toB256 [0x20] = (32 : B256) from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_iszero hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branch h with ⟨_, _, bad⟩ | ⟨nonzero, _, h⟩
  · cases s <;> unfold SingleMappingGetter.reject t_04ae_c87 t_04e9_c82 at bad
    all_goals
      obtain ⟨_, _, bad⟩ := ric_next bad
      obtain ⟨_, _, bad⟩ := ric_next bad
      exact (ric_revert bad).elim
  · have guard : (32 : B256) ≤ sevm.data.length.toB256 - 4 := by
      by_contra ne
      have lt := lt_of_not_ge ne
      have flag : B256.ltCheck (sevm.data.length.toB256 - 4) 32 = 1 := by
        simp only [B256.ltCheck, lt, ite_true]
      rw [flag] at nonzero
      exact nonzero (by decide)
    exact ⟨guard, singleMapping_decoder_inv s fork mem h.uncut⟩


def mappingSpender (sevm : Sevm) : Adr := (Sevm.dataWord sevm 36).toAdr

def allowanceSlot (sevm : Sevm) : B256 :=
  mapSlot (mappingSpender sevm).toB256 (mapSlot (mappingOwner sevm).toB256 2)

theorem allowance_decoder_exact {sevm : Sevm} {b : Devm} {M : Mem}
    {G c : Nat} {sel avail : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (cost : c = sloadCost sevm b (allowanceSlot sevm)) :
    SFunc.RunExact cert.prog sevm (St b [avail, 4, 0x039b, sel] M (G + c + 246))
      t_0656_c77 (.halted (getterWordPost (afterSload sevm b (allowanceSlot sevm))
        [0x039b, sel] (allowanceScratch2 M (mappingOwner sevm).toB256 (mappingSpender sevm).toB256)
        (b.getStorVal sevm.currentTarget (allowanceSlot sevm)) G)) := by
  have outmem := allowanceScratch2_ptr mem (mappingOwner sevm).toB256 (mappingSpender sevm).toB256
  unfold t_0656_c77
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push (w := ~~~ addressMask) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_dup2 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_dup2 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_and (addressSlotReadWord_eq_toAdr_toB256 _) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_swap2 ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_add' (v := 36) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_and (v := (mappingSpender sevm).toB256) (by
    rw [B256.and_comm]
    exact addressSlotReadWord_eq_toAdr_toB256 _) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x1dd8) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  have gas : G + c + 210 = ((G + 49) + c + 153) + 8 := by omega
  rw [gas]
  refine rx_callRet (g := t_1dd8_c30) (by rfl)
    (allowance_callee_exact fork mem cost (by simp only [List.length_cons, List.length_nil]; decide)) ?_
  exact getterWord_tail_exact outmem (by simp only [List.length_cons, List.length_nil]; decide)

theorem allowance_entry_exact {sevm : Sevm} {b : Devm} {M : Mem}
    {G c : Nat} {sel : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (guard : (64 : B256) ≤ sevm.data.length.toB256 - 4)
    (cost : c = sloadCost sevm b (allowanceSlot sevm)) :
    SFunc.RunExact cert.prog sevm (St b [sel] M (G + c + 286)) t_0640_c77
      (.halted (getterWordPost (afterSload sevm b (allowanceSlot sevm)) [0x039b, sel]
        (allowanceScratch2 M (mappingOwner sevm).toB256 (mappingSpender sevm).toB256)
        (b.getStorVal sevm.currentTarget (allowanceSlot sevm)) G)) := by
  unfold t_0640_c77
  refine rx_dest ?_
  refine rx_push (w := 0x039b) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 4) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_calldatasize (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_sub' (v := sevm.data.length.toB256 - 4) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 64) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_dup2 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_lt (v := 0) (ltCheck_zero_of_le guard) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_iszero (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x0656) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_succ (by decide) ?_
  exact allowance_decoder_exact fork mem cost

theorem allowance_decoder_inv {sevm : Sevm} {b : Devm} {M : Mem}
    {G : Nat} {sel avail : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm (St b [avail, 4, 0x039b, sel] M G) t_0656_c77 o) :
    ∃ d, o = .halted d ∧ d.output = (b.getStorVal sevm.currentTarget (allowanceSlot sevm)).toBytes ∧
      (∀ a, Devm.getStor d a = Devm.getStor b a) ∧ d.logs = b.logs := by
  have h := run.cut
  unfold t_0656_c77 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_calldataload hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_and hd
  change d = St b ((Bytes.toB256 (List.replicate 20 0xff) &&& Sevm.dataWord sevm 4) ::
    Bytes.toB256 (List.replicate 20 0xff) :: 4 :: 0x039b :: sel :: []) M _ at hd
  rw [show Bytes.toB256 (List.replicate 20 0xff) = ~~~ addressMask from by decide,
    show ((~~~ addressMask) &&& Sevm.dataWord sevm 4) = (mappingOwner sevm).toB256 from addressSlotReadWord_eq_toAdr_toB256 _] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_add hd
  rw [show Bytes.toB256 [0x20] + (4 : B256) = 36 from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_calldataload hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_and hd
  change d = St b (((Sevm.dataWord sevm 36) &&& (~~~ addressMask)) ::
    (mappingOwner sevm).toB256 :: 0x039b :: sel :: []) M _ at hd
  rw [B256.and_comm, show ((~~~ addressMask) &&& Sevm.dataWord sevm 36) =
    (mappingSpender sevm).toB256 from addressSlotReadWord_eq_toAdr_toB256 _] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨_, h⟩ := ric_call (g := t_1dd8_c30) (by rfl) h
  rcases h with ⟨d, hc, h⟩ | ⟨d, hc, _⟩
  · obtain ⟨_, eq⟩ := allowance_callee_inv fork mem hc
    cases eq
    obtain ⟨d, ho, hout, hs, hl⟩ := getterWord_tail_inv
      (allowanceScratch2_ptr mem (mappingOwner sevm).toB256 (mappingSpender sevm).toB256) h.uncut
    exact ⟨d, ho, hout, fun a => (hs a).trans (afterSload_getStor _ _ _ _), hl.trans (afterSload_logs _ _ _)⟩
  · obtain ⟨_, eq⟩ := allowance_callee_inv fork mem hc
    cases eq

theorem allowance_entry_inv {sevm : Sevm} {b : Devm} {M : Mem}
    {G : Nat} {sel : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm (St b [sel] M G) t_0640_c77 o) :
    (64 : B256) ≤ sevm.data.length.toB256 - 4 ∧
      ∃ d, o = .halted d ∧ d.output = (b.getStorVal sevm.currentTarget (allowanceSlot sevm)).toBytes ∧
        (∀ a, Devm.getStor d a = Devm.getStor b a) ∧ d.logs = b.logs := by
  have h := run.cut
  unfold t_0640_c77 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_calldatasize hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_sub hd
  rw [show Bytes.toB256 [0x04] = (4 : B256) from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_lt hd
  rw [show Bytes.toB256 [0x40] = (64 : B256) from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_iszero hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branch h with ⟨_, _, bad⟩ | ⟨nonzero, _, h⟩
  · unfold t_0652_c77 at bad
    obtain ⟨_, _, bad⟩ := ric_next bad
    obtain ⟨_, _, bad⟩ := ric_next bad
    exact (ric_revert bad).elim
  · have guard : (64 : B256) ≤ sevm.data.length.toB256 - 4 := by
      by_contra ne
      have lt := lt_of_not_ge ne
      have flag : B256.ltCheck (sevm.data.length.toB256 - 4) 64 = 1 := by
        simp only [B256.ltCheck, lt, ite_true]
      rw [flag] at nonzero
      exact nonzero (by decide)
    exact ⟨guard, allowance_decoder_inv fork mem h.uncut⟩

end Blanc.Lift.UniswapV2Pair
