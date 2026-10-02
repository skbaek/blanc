import Blanc.Lift.UniswapV2Pair.TransferCore

/-! Literal transferFrom allowance branches and their shared transfer continuation. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def transferFromAllowanceSlot (owner spender : Adr) : B256 :=
  mapSlot spender.toB256 (mapSlot owner.toB256 2)

def transferFromJoinPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (owner recipient : Adr) (amount : B256) (G : Nat) : Devm :=
  St (transferCoreBase sevm b owner recipient amount) (1 :: R)
    (transferCoreMemory M owner recipient amount) G

/-- Both allowance branches consume this literal join; no caller bypass is introduced. -/
theorem transferFrom_join_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G sourceCost debitCost loadCost creditCost : Nat} {owner recipient : Adr} {amount τ ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (sourceEq : sourceCost = sloadCost sevm b (transferBalanceSlot owner))
    (debitEq : debitCost = sstoreCost sevm (afterSload sevm b (transferBalanceSlot owner))
      (transferBalanceSlot owner) (transferSourceWord sevm b owner - amount))
    (loadEq : loadCost = sloadCost sevm
      (transferDebitBase sevm (afterSload sevm b (transferBalanceSlot owner)) owner
        (transferSourceWord sevm b owner - amount)) (transferBalanceSlot recipient))
    (creditEq : creditCost = sstoreCost sevm
      (afterSload sevm (transferDebitBase sevm (afterSload sevm b (transferBalanceSlot owner))
        owner (transferSourceWord sevm b owner - amount)) (transferBalanceSlot recipient))
      (transferBalanceSlot recipient)
      (transferRecipientWord sevm (afterSload sevm b (transferBalanceSlot owner)) owner recipient
        (transferSourceWord sevm b owner - amount) + amount))
    (debitSentry : gCallStipend < G + debitCost + loadCost + creditCost + 2105)
    (creditSentry : gCallStipend < G + creditCost + 1865)
    (nonstatic : sevm.isStatic = false) (cover : amount ≤ transferSourceWord sevm b owner)
    (nowrap : (transferRecipientWord sevm (afterSload sevm b (transferBalanceSlot owner))
      owner recipient (transferSourceWord sevm b owner - amount)).toNat + amount.toNat < 2 ^ 256)
    (room : R.length ≤ 1008) :
    SFunc.RunExact cert.prog sevm
      (St b (τ :: amount :: recipient.toB256 :: owner.toB256 :: ρ :: R)
        M (G + sourceCost + debitCost + loadCost + creditCost + 2382)) t_0ee8_c10
      (.returned (transferFromJoinPost sevm b R M owner recipient amount G)) := by
  unfold t_0ee8_c10
  refine rx_dest ?_
  refine rx_push (w := 0x0ef3) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x260b) rfl (by simp only [List.length_cons]; omega) ?_
  have gas : G + sourceCost + debitCost + loadCost + creditCost + 2366 =
    ((G + 26) + sourceCost + debitCost + loadCost + creditCost + 2332) + 8 := by omega
  rw [gas]
  refine rx_callRet (g := t_260b_c61) rfl
    (transfer61_exact fork mem sourceEq debitEq loadEq creditEq (by omega) (by omega)
      nonstatic cover nowrap (by simp only [List.length_cons]; omega)) ?_
  unfold t_0ef3_c10
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push (w := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (S' := ρ :: amount :: recipient.toB256 :: owner.toB256 :: 1 :: R) rfl ?_
  refine rx_swap (S' := owner.toB256 :: amount :: recipient.toB256 :: ρ :: 1 :: R) rfl ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  exact rx_ret


theorem transferFrom_join_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {owner recipient : Adr} {amount τ ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm
      (St b (τ :: amount :: recipient.toB256 :: owner.toB256 :: ρ :: R) M G) t_0ee8_c10 o) :
    amount ≤ transferSourceWord sevm b owner ∧ sevm.isStatic = false ∧
      (transferRecipientWord sevm (afterSload sevm b (transferBalanceSlot owner))
        owner recipient (transferSourceWord sevm b owner - amount)).toNat + amount.toNat < 2 ^ 256 ∧
      ∃ residual, o = .returned (transferFromJoinPost sevm b R M owner recipient amount residual) := by
  have h := run.cut
  unfold t_0ee8_c10 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨_, call⟩ := ric_call (g := t_260b_c61) rfl h
  rcases call with ⟨d, core, tail⟩ | ⟨d, core, _⟩
  · obtain ⟨cover, nonstatic, nowrap, _, eq⟩ := transfer61_inv fork mem core
    cases eq
    unfold t_0ef3_c10 at tail
    obtain ⟨_, tail⟩ := ric_dest tail
    obtain ⟨d, hd, tail⟩ := ric_next tail
    obtain ⟨_, rfl⟩ := ri_pop hd
    obtain ⟨d, hd, tail⟩ := ric_next tail
    obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, tail⟩ := ric_next tail
    obtain ⟨_, rfl⟩ := ri_swap
      (S' := ρ :: amount :: recipient.toB256 :: owner.toB256 :: 1 :: R) rfl hd
    obtain ⟨d, hd, tail⟩ := ric_next tail
    obtain ⟨_, rfl⟩ := ri_swap
      (S' := owner.toB256 :: amount :: recipient.toB256 :: ρ :: 1 :: R) rfl hd
    obtain ⟨d, hd, tail⟩ := ric_next tail
    obtain ⟨_, rfl⟩ := ri_pop hd
    obtain ⟨d, hd, tail⟩ := ric_next tail
    obtain ⟨_, rfl⟩ := ri_pop hd
    obtain ⟨d, hd, tail⟩ := ric_next tail
    obtain ⟨_, rfl⟩ := ri_pop hd
    obtain ⟨residual, result⟩ := ric_ret tail
    exact ⟨cover, nonstatic, nowrap, residual, Seg.done.inj result⟩
  · obtain ⟨_, _, _, _, eq⟩ := transfer61_inv fork mem core
    cases eq


def transferFromStoreBase (sevm : Sevm) (b : Devm) (owner : Adr) (reduced : B256) : Devm :=
  afterSstore sevm b (transferFromAllowanceSlot owner sevm.caller) reduced

def transferFromStorePost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (owner recipient : Adr) (amount reduced : B256) (G : Nat) : Devm :=
  transferFromJoinPost sevm (transferFromStoreBase sevm b owner reduced) R
    (approveScratch M owner.toB256 sevm.caller.toB256) owner recipient amount G

/-- The finite allowance store emits no event and precedes the sequential balance transfer. -/
theorem transferFrom_store_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G allowanceCost sourceCost debitCost loadCost creditCost : Nat} {owner recipient : Adr} {amount reduced τ ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (allowanceEq : allowanceCost = sstoreCost sevm b
      (transferFromAllowanceSlot owner sevm.caller) reduced)
    (allowanceSentry : gCallStipend < G + allowanceCost + sourceCost + debitCost + loadCost + creditCost + 2382)
    (sourceEq : sourceCost = sloadCost sevm (transferFromStoreBase sevm b owner reduced) (transferBalanceSlot owner))
    (debitEq : debitCost = sstoreCost sevm (afterSload sevm (transferFromStoreBase sevm b owner reduced) (transferBalanceSlot owner))
      (transferBalanceSlot owner) (transferSourceWord sevm (transferFromStoreBase sevm b owner reduced) owner - amount))
    (loadEq : loadCost = sloadCost sevm
      (transferDebitBase sevm (afterSload sevm (transferFromStoreBase sevm b owner reduced) (transferBalanceSlot owner)) owner
        (transferSourceWord sevm (transferFromStoreBase sevm b owner reduced) owner - amount)) (transferBalanceSlot recipient))
    (creditEq : creditCost = sstoreCost sevm
      (afterSload sevm (transferDebitBase sevm (afterSload sevm (transferFromStoreBase sevm b owner reduced) (transferBalanceSlot owner))
        owner (transferSourceWord sevm (transferFromStoreBase sevm b owner reduced) owner - amount)) (transferBalanceSlot recipient))
      (transferBalanceSlot recipient)
      (transferRecipientWord sevm (afterSload sevm (transferFromStoreBase sevm b owner reduced) (transferBalanceSlot owner)) owner recipient
        (transferSourceWord sevm (transferFromStoreBase sevm b owner reduced) owner - amount) + amount))
    (debitSentry : gCallStipend < G + debitCost + loadCost + creditCost + 2105)
    (creditSentry : gCallStipend < G + creditCost + 1865)
    (nonstatic : sevm.isStatic = false) (cover : amount ≤ transferSourceWord sevm (transferFromStoreBase sevm b owner reduced) owner)
    (nowrap : (transferRecipientWord sevm (afterSload sevm (transferFromStoreBase sevm b owner reduced) (transferBalanceSlot owner))
      owner recipient (transferSourceWord sevm (transferFromStoreBase sevm b owner reduced) owner - amount)).toNat + amount.toNat < 2 ^ 256)
    (room : R.length ≤ 1008) :
    SFunc.RunExact cert.prog sevm
      (St b (reduced :: τ :: amount :: recipient.toB256 :: owner.toB256 :: ρ :: R)
        M (G + allowanceCost + sourceCost + debitCost + loadCost + creditCost + 2532)) t_0eb6_c48
      (.returned (transferFromStorePost sevm b R M owner recipient amount reduced G)) := by
  have m0 := mem.write 0 owner.toB256 (Or.inl (by decide))
  rw [show memExtSize 96 0 32 = 96 from by decide] at m0
  have m1 := approveOwnerMemory_ptr mem owner.toB256
  have m2 := m1.write 0 sevm.caller.toB256 (Or.inl (by decide))
  rw [show memExtSize 96 0 32 = 96 from by decide] at m2
  have m3 := approveScratch_ptr mem owner.toB256 sevm.caller.toB256
  have s1 : ((M.write 0 owner.toB256.toBytes).write 32 (2 : B256).toBytes).size = 96 := m1.size
  have s2 : (((M.write 0 owner.toB256.toBytes).write 32 (2 : B256).toBytes).write 0
      sevm.caller.toB256.toBytes).size = 96 := m2.size
  have s3 : ((((M.write 0 owner.toB256.toBytes).write 32 (2 : B256).toBytes).write 0
      sevm.caller.toB256.toBytes).write 32 (mapSlot owner.toB256 2).toBytes).size = 96 := m3.size
  unfold t_0eb6_c48
  refine rx_dest ?_
  refine rx_push (w := ~~~ addressMask) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 5) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := owner.toB256) (by rw [B256.and_comm]; exact ff20_and_adr owner)
    (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]; decide
  refine rx_push (w := 2) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · simp only [show (0 : B256).toNat = 0 from rfl]
    rw [St.extCost_eq m0.size]; decide
  refine rx_push (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup4 (by simp only [List.length_cons]; omega) ?_
  simp only [show (32 : B256).toNat = 32 from rfl, show (0 : B256).toNat = 0 from rfl]
  have gasHash1 : G + allowanceCost + sourceCost + debitCost + loadCost + creditCost + 2486 =
    (G + allowanceCost + sourceCost + debitCost + loadCost + creditCost + 2444) + 42 := by omega
  rw [gasHash1]
  refine rx_keccak (v := mapSlot owner.toB256 2) (c := 42) ?_ ?_
    (m1.read_self (by decide)) (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq s1]; decide
  · exact congrArg Bytes.keccak (Mem.read_two_word_writes_at_raw M 0 owner.toB256 2)
  refine rx_caller (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq s1]; decide
  refine rx_swap1 ?_
  refine rx_swap2 ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · simp only [show (0 : B256).toNat = 0 from rfl]
    rw [St.extCost_eq s2]; decide
  refine rx_swap1 ?_
  simp only [show (32 : B256).toNat = 32 from rfl, show (0 : B256).toNat = 0 from rfl]
  have gasHash2 : G + allowanceCost + sourceCost + debitCost + loadCost + creditCost + 2424 =
    (G + allowanceCost + sourceCost + debitCost + loadCost + creditCost + 2382) + 42 := by omega
  rw [gasHash2]
  refine rx_keccak (v := transferFromAllowanceSlot owner sevm.caller) (c := 42) ?_ ?_
    (m3.read_self (by decide)) (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq s3]; decide
  · exact congrArg Bytes.keccak
      (Mem.read_two_word_writes_at_raw (approveOwnerMemory M owner.toB256) 0
        sevm.caller.toB256 (mapSlot owner.toB256 2))
  have gasStore : G + allowanceCost + sourceCost + debitCost + loadCost + creditCost + 2382 =
    (G + sourceCost + debitCost + loadCost + creditCost + 2382) + allowanceCost := by omega
  rw [gasStore]
  refine rx_sstoreC fork allowanceEq (by omega) nonstatic ?_
  exact transferFrom_join_exact fork m3 sourceEq debitEq loadEq creditEq
    debitSentry creditSentry nonstatic cover nowrap room


theorem transferFrom_store_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {owner recipient : Adr} {amount reduced τ ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm
      (St b (reduced :: τ :: amount :: recipient.toB256 :: owner.toB256 :: ρ :: R) M G)
      t_0eb6_c48 o) :
    amount ≤ transferSourceWord sevm (transferFromStoreBase sevm b owner reduced) owner ∧
      sevm.isStatic = false ∧
      (transferRecipientWord sevm
        (afterSload sevm (transferFromStoreBase sevm b owner reduced) (transferBalanceSlot owner))
        owner recipient (transferSourceWord sevm (transferFromStoreBase sevm b owner reduced) owner - amount)).toNat +
          amount.toNat < 2 ^ 256 ∧
      ∃ residual, o = .returned (transferFromStorePost sevm b R M owner recipient amount reduced residual) := by
  have m1 := approveOwnerMemory_ptr mem owner.toB256
  have m3 := approveScratch_ptr mem owner.toB256 sevm.caller.toB256
  dsimp only [approveScratch, approveOwnerMemory] at m1 m3
  have read2 := Mem.read_two_word_writes_at_raw (approveOwnerMemory M owner.toB256) 0
    sevm.caller.toB256 (mapSlot owner.toB256 2)
  dsimp only [approveOwnerMemory] at read2
  have h := run.cut
  unfold t_0eb6_c48 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := owner.toB256)
    (by rw [B256.and_comm]; exact ff20_and_adr owner) (ri_and hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (Bytes.toB256 [0x20]).toNat = 32 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_keccak hd
  simp only [show Bytes.toB256 [2] = (2 : B256) from rfl,
    show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [0x40]).toNat = 64 from rfl,
    m1.read_self (by decide : 0 + 64 ≤ 96),
    Mem.read_two_word_writes_at_raw M 0 owner.toB256 2] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_caller hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (Bytes.toB256 [0x20]).toNat = 32 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_keccak hd
  change d = St b (((approveScratch M owner.toB256 sevm.caller.toB256).read 0 64).1.keccak :: _)
    ((approveScratch M owner.toB256 sevm.caller.toB256).read 0 64).2 _ at hd
  dsimp only [approveScratch, approveOwnerMemory] at hd
  rw [m3.read_self (by decide : 0 + 64 ≤ 96), read2] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_sstore fork hd
  exact transferFrom_join_inv fork (approveScratch_ptr mem owner.toB256 sevm.caller.toB256) h.uncut


def transferFromAllowanceWord (sevm : Sevm) (b : Devm) (owner : Adr) : B256 :=
  b.getStorVal sevm.currentTarget (transferFromAllowanceSlot owner sevm.caller)

def transferFromSecondBase (sevm : Sevm) (b : Devm) (owner : Adr) : Devm :=
  afterSload sevm b (transferFromAllowanceSlot owner sevm.caller)

def transferFromFinitePost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (owner recipient : Adr) (amount : B256) (G : Nat) : Devm :=
  transferFromStorePost sevm (transferFromSecondBase sevm b owner) R
    (approveScratch M owner.toB256 sevm.caller.toB256) owner recipient amount
    (transferFromAllowanceWord sevm b owner - amount) G

/-- The finite arm actually loads allowance again before checked subtraction and its store. -/
theorem transferFrom_finite_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G secondCost allowanceCost sourceCost debitCost loadCost creditCost : Nat} {owner recipient : Adr} {amount τ ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (secondEq : secondCost = sloadCost sevm b (transferFromAllowanceSlot owner sevm.caller))
    (allowanceCover : amount ≤ transferFromAllowanceWord sevm b owner)
    (allowanceEq : allowanceCost = sstoreCost sevm (transferFromSecondBase sevm b owner)
      (transferFromAllowanceSlot owner sevm.caller) (transferFromAllowanceWord sevm b owner - amount))
    (allowanceSentry : gCallStipend < G + allowanceCost + sourceCost + debitCost + loadCost + creditCost + 2382)
    (sourceEq : sourceCost = sloadCost sevm (transferFromStoreBase sevm (transferFromSecondBase sevm b owner) owner (transferFromAllowanceWord sevm b owner - amount)) (transferBalanceSlot owner))
    (debitEq : debitCost = sstoreCost sevm (afterSload sevm (transferFromStoreBase sevm (transferFromSecondBase sevm b owner) owner (transferFromAllowanceWord sevm b owner - amount)) (transferBalanceSlot owner))
      (transferBalanceSlot owner) (transferSourceWord sevm (transferFromStoreBase sevm (transferFromSecondBase sevm b owner) owner (transferFromAllowanceWord sevm b owner - amount)) owner - amount))
    (loadEq : loadCost = sloadCost sevm
      (transferDebitBase sevm (afterSload sevm (transferFromStoreBase sevm (transferFromSecondBase sevm b owner) owner (transferFromAllowanceWord sevm b owner - amount)) (transferBalanceSlot owner)) owner
        (transferSourceWord sevm (transferFromStoreBase sevm (transferFromSecondBase sevm b owner) owner (transferFromAllowanceWord sevm b owner - amount)) owner - amount)) (transferBalanceSlot recipient))
    (creditEq : creditCost = sstoreCost sevm
      (afterSload sevm (transferDebitBase sevm (afterSload sevm (transferFromStoreBase sevm (transferFromSecondBase sevm b owner) owner (transferFromAllowanceWord sevm b owner - amount)) (transferBalanceSlot owner))
        owner (transferSourceWord sevm (transferFromStoreBase sevm (transferFromSecondBase sevm b owner) owner (transferFromAllowanceWord sevm b owner - amount)) owner - amount)) (transferBalanceSlot recipient))
      (transferBalanceSlot recipient)
      (transferRecipientWord sevm (afterSload sevm (transferFromStoreBase sevm (transferFromSecondBase sevm b owner) owner (transferFromAllowanceWord sevm b owner - amount)) (transferBalanceSlot owner)) owner recipient
        (transferSourceWord sevm (transferFromStoreBase sevm (transferFromSecondBase sevm b owner) owner (transferFromAllowanceWord sevm b owner - amount)) owner - amount) + amount))
    (debitSentry : gCallStipend < G + debitCost + loadCost + creditCost + 2105)
    (creditSentry : gCallStipend < G + creditCost + 1865)
    (nonstatic : sevm.isStatic = false) (cover : amount ≤ transferSourceWord sevm (transferFromStoreBase sevm (transferFromSecondBase sevm b owner) owner (transferFromAllowanceWord sevm b owner - amount)) owner)
    (nowrap : (transferRecipientWord sevm (afterSload sevm (transferFromStoreBase sevm (transferFromSecondBase sevm b owner) owner (transferFromAllowanceWord sevm b owner - amount)) (transferBalanceSlot owner))
      owner recipient (transferSourceWord sevm (transferFromStoreBase sevm (transferFromSecondBase sevm b owner) owner (transferFromAllowanceWord sevm b owner - amount)) owner - amount)).toNat + amount.toNat < 2 ^ 256)
    (room : R.length ≤ 1008) :
    SFunc.RunExact cert.prog sevm
      (St b (τ :: amount :: recipient.toB256 :: owner.toB256 :: ρ :: R)
        M (G + secondCost + allowanceCost + sourceCost + debitCost + loadCost + creditCost + 2761)) t_0e76_c48
      (.returned (transferFromFinitePost sevm b R M owner recipient amount G)) := by
  have m0 := mem.write 0 owner.toB256 (Or.inl (by decide))
  rw [show memExtSize 96 0 32 = 96 from by decide] at m0
  have m1 := approveOwnerMemory_ptr mem owner.toB256
  have m2 := m1.write 0 sevm.caller.toB256 (Or.inl (by decide))
  rw [show memExtSize 96 0 32 = 96 from by decide] at m2
  have m3 := approveScratch_ptr mem owner.toB256 sevm.caller.toB256
  have s1 : ((M.write 0 owner.toB256.toBytes).write 32 (2 : B256).toBytes).size = 96 := m1.size
  have s2 : (((M.write 0 owner.toB256.toBytes).write 32 (2 : B256).toBytes).write 0
      sevm.caller.toB256.toBytes).size = 96 := m2.size
  have s3 : ((((M.write 0 owner.toB256.toBytes).write 32 (2 : B256).toBytes).write 0
      sevm.caller.toB256.toBytes).write 32 (mapSlot owner.toB256 2).toBytes).size = 96 := m3.size
  unfold t_0e76_c48
  refine rx_push (w := ~~~ addressMask) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := owner.toB256) (by rw [B256.and_comm]; exact ff20_and_adr owner)
    (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]; decide
  refine rx_push (w := 2) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · simp only [show (0 : B256).toNat = 0 from rfl]
    rw [St.extCost_eq m0.size]; decide
  refine rx_push (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup4 (by simp only [List.length_cons]; omega) ?_
  simp only [show (32 : B256).toNat = 32 from rfl, show (0 : B256).toNat = 0 from rfl]
  have gasHash1 : G + secondCost + allowanceCost + sourceCost + debitCost + loadCost + creditCost + 2716 =
    (G + secondCost + allowanceCost + sourceCost + debitCost + loadCost + creditCost + 2674) + 42 := by omega
  rw [gasHash1]
  refine rx_keccak (v := mapSlot owner.toB256 2) (c := 42) ?_ ?_
    (m1.read_self (by decide)) (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq s1]; decide
  · exact congrArg Bytes.keccak (Mem.read_two_word_writes_at_raw M 0 owner.toB256 2)
  refine rx_caller (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq s1]; decide
  refine rx_swap1 ?_
  refine rx_swap2 ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · simp only [show (0 : B256).toNat = 0 from rfl]
    rw [St.extCost_eq s2]; decide
  refine rx_swap1 ?_
  simp only [show (32 : B256).toNat = 32 from rfl, show (0 : B256).toNat = 0 from rfl]
  have gasHash2 : G + secondCost + allowanceCost + sourceCost + debitCost + loadCost + creditCost + 2654 =
    (G + secondCost + allowanceCost + sourceCost + debitCost + loadCost + creditCost + 2612) + 42 := by omega
  rw [gasHash2]
  refine rx_keccak (v := transferFromAllowanceSlot owner sevm.caller) (c := 42) ?_ ?_
    (m3.read_self (by decide)) (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq s3]; decide
  · exact congrArg Bytes.keccak
      (Mem.read_two_word_writes_at_raw (approveOwnerMemory M owner.toB256) 0
        sevm.caller.toB256 (mapSlot owner.toB256 2))
  have gasLoad : G + secondCost + allowanceCost + sourceCost + debitCost + loadCost + creditCost + 2612 =
    (G + allowanceCost + sourceCost + debitCost + loadCost + creditCost + 2612) + secondCost := by omega
  rw [gasLoad]
  refine rx_sload_selC fork secondEq (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x0eb6) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup (n := 3) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0xffffffff) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x226e) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := 0x226e) (by decide) (by simp only [List.length_cons]; omega) ?_
  have gasCall : G + allowanceCost + sourceCost + debitCost + loadCost + creditCost + 2594 =
    ((G + allowanceCost + sourceCost + debitCost + loadCost + creditCost + 2532) + 54) + 8 := by omega
  rw [gasCall]
  refine rx_callRet (g := t_226e_c59) rfl
    (sub59_exact allowanceCover (by simp only [List.length_cons]; omega)) ?_
  exact transferFrom_store_exact fork m3 allowanceEq allowanceSentry sourceEq debitEq loadEq creditEq
    debitSentry creditSentry nonstatic cover nowrap room

theorem transferFrom_finite_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {owner recipient : Adr} {amount τ ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm
      (St b (τ :: amount :: recipient.toB256 :: owner.toB256 :: ρ :: R) M G)
      t_0e76_c48 o) :
    amount ≤ transferFromAllowanceWord sevm b owner ∧
      amount ≤ transferSourceWord sevm (transferFromStoreBase sevm (transferFromSecondBase sevm b owner) owner (transferFromAllowanceWord sevm b owner - amount)) owner ∧
      sevm.isStatic = false ∧
      (transferRecipientWord sevm
        (afterSload sevm (transferFromStoreBase sevm (transferFromSecondBase sevm b owner) owner (transferFromAllowanceWord sevm b owner - amount)) (transferBalanceSlot owner))
        owner recipient (transferSourceWord sevm (transferFromStoreBase sevm (transferFromSecondBase sevm b owner) owner (transferFromAllowanceWord sevm b owner - amount)) owner - amount)).toNat +
          amount.toNat < 2 ^ 256 ∧
      ∃ residual, o = .returned (transferFromFinitePost sevm b R M owner recipient amount residual) := by
  have m1 := approveOwnerMemory_ptr mem owner.toB256
  have m3 := approveScratch_ptr mem owner.toB256 sevm.caller.toB256
  dsimp only [approveScratch, approveOwnerMemory] at m1 m3
  have read2 := Mem.read_two_word_writes_at_raw (approveOwnerMemory M owner.toB256) 0
    sevm.caller.toB256 (mapSlot owner.toB256 2)
  dsimp only [approveOwnerMemory] at read2
  have h := run.cut
  unfold t_0e76_c48 at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := owner.toB256)
    (by rw [B256.and_comm]; exact ff20_and_adr owner) (ri_and hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (Bytes.toB256 [0x20]).toNat = 32 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_keccak hd
  simp only [show Bytes.toB256 [2] = (2 : B256) from rfl,
    show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [0x40]).toNat = 64 from rfl,
    m1.read_self (by decide : 0 + 64 ≤ 96),
    Mem.read_two_word_writes_at_raw M 0 owner.toB256 2] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_caller hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (Bytes.toB256 [0x20]).toNat = 32 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_keccak hd
  change d = St b (((approveScratch M owner.toB256 sevm.caller.toB256).read 0 64).1.keccak :: _)
    ((approveScratch M owner.toB256 sevm.caller.toB256).read 0 64).2 _ at hd
  dsimp only [approveScratch, approveOwnerMemory] at hd
  rw [m3.read_self (by decide : 0 + 64 ≤ 96), read2] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 0x226e) (by decide) (ri_and hd)
  obtain ⟨_, call⟩ := ric_call (g := t_226e_c59) rfl h
  rcases call with ⟨d, checked, tail⟩ | ⟨d, checked, _⟩
  · obtain ⟨allowanceCover, _, eq⟩ := sub59_inv checked
    cases eq
    obtain ⟨cover, nonstatic, nowrap, residual, result⟩ := transferFrom_store_inv fork
      (approveScratch_ptr mem owner.toB256 sevm.caller.toB256) tail.uncut
    exact ⟨allowanceCover, cover, nonstatic, nowrap, residual, result⟩
  · obtain ⟨_, _, eq⟩ := sub59_inv checked
    cases eq


def transferFromFirstBase (sevm : Sevm) (b : Devm) (owner : Adr) : Devm :=
  afterSload sevm b (transferFromAllowanceSlot owner sevm.caller)

/-- The literal common prefix is consumed by both actual allowance continuations. -/
theorem transferFrom_prefix_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G firstCost : Nat} {owner recipient : Adr} {amount ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (firstEq : firstCost = sloadCost sevm b (transferFromAllowanceSlot owner sevm.caller))
    (room : R.length ≤ 1008)
    (maxCase : transferFromAllowanceWord sevm b owner = B256.max →
      SFunc.RunExact cert.prog sevm
        (St (transferFromFirstBase sevm b owner) (0 :: amount :: recipient.toB256 :: owner.toB256 :: ρ :: R)
          (approveScratch M owner.toB256 sevm.caller.toB256) G) t_0ee8_c10 o)
    (finiteCase : transferFromAllowanceWord sevm b owner ≠ B256.max →
      SFunc.RunExact cert.prog sevm
        (St (transferFromFirstBase sevm b owner) (0 :: amount :: recipient.toB256 :: owner.toB256 :: ρ :: R)
          (approveScratch M owner.toB256 sevm.caller.toB256) G) t_0e76_c48 o) :
    SFunc.RunExact cert.prog sevm
      (St b (amount :: recipient.toB256 :: owner.toB256 :: ρ :: R) M (G + firstCost + 169))
      t_0e1e_c48 o := by
  have m0 := mem.write 0 owner.toB256 (Or.inl (by decide))
  rw [show memExtSize 96 0 32 = 96 from by decide] at m0
  have m1 := approveOwnerMemory_ptr mem owner.toB256
  have m2 := m1.write 0 sevm.caller.toB256 (Or.inl (by decide))
  rw [show memExtSize 96 0 32 = 96 from by decide] at m2
  have m3 := approveScratch_ptr mem owner.toB256 sevm.caller.toB256
  have s1 : ((M.write 0 owner.toB256.toBytes).write 32 (2 : B256).toBytes).size = 96 := m1.size
  have s2 : (((M.write 0 owner.toB256.toBytes).write 32 (2 : B256).toBytes).write 0
      sevm.caller.toB256.toBytes).size = 96 := m2.size
  have s3 : ((((M.write 0 owner.toB256.toBytes).write 32 (2 : B256).toBytes).write 0
      sevm.caller.toB256.toBytes).write 32 (mapSlot owner.toB256 2).toBytes).size = 96 := m3.size
  unfold t_0e1e_c48
  refine rx_dest ?_
  refine rx_push (w := ~~~ addressMask) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 3) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := owner.toB256) (by rw [B256.and_comm]; exact ff20_and_adr owner)
    (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]; decide
  refine rx_push (w := 2) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · simp only [show (0 : B256).toNat = 0 from rfl]
    rw [St.extCost_eq m0.size]; decide
  refine rx_push (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup4 (by simp only [List.length_cons]; omega) ?_
  simp only [show (32 : B256).toNat = 32 from rfl, show (0 : B256).toNat = 0 from rfl]
  have gasHash1 : G + firstCost + 123 =
    (G + firstCost + 81) + 42 := by omega
  rw [gasHash1]
  refine rx_keccak (v := mapSlot owner.toB256 2) (c := 42) ?_ ?_
    (m1.read_self (by decide)) (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq s1]; decide
  · exact congrArg Bytes.keccak (Mem.read_two_word_writes_at_raw M 0 owner.toB256 2)
  refine rx_caller (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq s1]; decide
  refine rx_swap1 ?_
  refine rx_swap2 ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · simp only [show (0 : B256).toNat = 0 from rfl]
    rw [St.extCost_eq s2]; decide
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  simp only [show (32 : B256).toNat = 32 from rfl, show (0 : B256).toNat = 0 from rfl]
  have gasHash2 : G + firstCost + 61 =
    (G + firstCost + 19) + 42 := by omega
  rw [gasHash2]
  refine rx_keccak (v := transferFromAllowanceSlot owner sevm.caller) (c := 42) ?_ ?_
    (m3.read_self (by decide)) (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq s3]; decide
  · exact congrArg Bytes.keccak
      (Mem.read_two_word_writes_at_raw (approveOwnerMemory M owner.toB256) 0
        sevm.caller.toB256 (mapSlot owner.toB256 2))
  have gasLoad : G + firstCost + 19 = (G + 19) + firstCost := by omega
  rw [gasLoad]
  refine rx_sload_selC fork firstEq (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := B256.max) (by decide) (by simp only [List.length_cons]; omega) ?_
  by_cases maximal : transferFromAllowanceWord sevm b owner = B256.max
  · refine rx_eq (v := 1) ?_ (by simp only [List.length_cons]; omega) ?_
    · exact ite_eq_left maximal.symm
    refine rx_push (w := 0x0ee8) rfl (by simp only [List.length_cons]; omega) ?_
    exact rx_branchTo_succ (by decide : (1 : B256) ≠ 0) rfl (maxCase maximal)
  · refine rx_eq (v := 0) ?_ (by simp only [List.length_cons]; omega) ?_
    · exact ite_eq_right (Ne.symm maximal)
    refine rx_push (w := 0x0ee8) rfl (by simp only [List.length_cons]; omega) ?_
    exact rx_branchTo_zero (finiteCase maximal)


/-- Max allowance executes one allowance load and no allowance store. -/
theorem transferFrom48_max_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G firstCost sourceCost debitCost loadCost creditCost : Nat} {owner recipient : Adr} {amount ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (firstEq : firstCost = sloadCost sevm b (transferFromAllowanceSlot owner sevm.caller))
    (maximal : transferFromAllowanceWord sevm b owner = B256.max)
    (sourceEq : sourceCost = sloadCost sevm (transferFromFirstBase sevm b owner) (transferBalanceSlot owner))
    (debitEq : debitCost = sstoreCost sevm (afterSload sevm (transferFromFirstBase sevm b owner) (transferBalanceSlot owner))
      (transferBalanceSlot owner) (transferSourceWord sevm (transferFromFirstBase sevm b owner) owner - amount))
    (loadEq : loadCost = sloadCost sevm
      (transferDebitBase sevm (afterSload sevm (transferFromFirstBase sevm b owner) (transferBalanceSlot owner)) owner
        (transferSourceWord sevm (transferFromFirstBase sevm b owner) owner - amount)) (transferBalanceSlot recipient))
    (creditEq : creditCost = sstoreCost sevm
      (afterSload sevm (transferDebitBase sevm (afterSload sevm (transferFromFirstBase sevm b owner) (transferBalanceSlot owner))
        owner (transferSourceWord sevm (transferFromFirstBase sevm b owner) owner - amount)) (transferBalanceSlot recipient))
      (transferBalanceSlot recipient)
      (transferRecipientWord sevm (afterSload sevm (transferFromFirstBase sevm b owner) (transferBalanceSlot owner)) owner recipient
        (transferSourceWord sevm (transferFromFirstBase sevm b owner) owner - amount) + amount))
    (debitSentry : gCallStipend < G + debitCost + loadCost + creditCost + 2105)
    (creditSentry : gCallStipend < G + creditCost + 1865)
    (nonstatic : sevm.isStatic = false) (cover : amount ≤ transferSourceWord sevm (transferFromFirstBase sevm b owner) owner)
    (nowrap : (transferRecipientWord sevm (afterSload sevm (transferFromFirstBase sevm b owner) (transferBalanceSlot owner))
      owner recipient (transferSourceWord sevm (transferFromFirstBase sevm b owner) owner - amount)).toNat + amount.toNat < 2 ^ 256)
    (room : R.length ≤ 1008) :
    SFunc.RunExact cert.prog sevm
      (St b (amount :: recipient.toB256 :: owner.toB256 :: ρ :: R)
        M (G + firstCost + sourceCost + debitCost + loadCost + creditCost + 2551)) t_0e1e_c48
      (.returned (transferFromJoinPost sevm (transferFromFirstBase sevm b owner) R
        (approveScratch M owner.toB256 sevm.caller.toB256) owner recipient amount G)) := by
  have gas : G + firstCost + sourceCost + debitCost + loadCost + creditCost + 2551 =
    (G + sourceCost + debitCost + loadCost + creditCost + 2382) + firstCost + 169 := by omega
  rw [gas]
  refine transferFrom_prefix_exact fork mem firstEq room ?_ ?_
  · intro _
    exact transferFrom_join_exact fork (approveScratch_ptr mem owner.toB256 sevm.caller.toB256)
      sourceEq debitEq loadEq creditEq debitSentry creditSentry nonstatic cover nowrap room
  · intro finite
    exact False.elim (finite maximal)

/-- Finite allowance executes its second load, checked subtraction and store, including zero amount. -/
theorem transferFrom48_finite_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G firstCost secondCost allowanceCost sourceCost debitCost loadCost creditCost : Nat} {owner recipient : Adr} {amount ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (firstEq : firstCost = sloadCost sevm b (transferFromAllowanceSlot owner sevm.caller))
    (finite : transferFromAllowanceWord sevm b owner ≠ B256.max)
    (secondEq : secondCost = sloadCost sevm (transferFromFirstBase sevm b owner) (transferFromAllowanceSlot owner sevm.caller))
    (allowanceCover : amount ≤ transferFromAllowanceWord sevm (transferFromFirstBase sevm b owner) owner)
    (allowanceEq : allowanceCost = sstoreCost sevm (transferFromSecondBase sevm (transferFromFirstBase sevm b owner) owner)
      (transferFromAllowanceSlot owner sevm.caller) (transferFromAllowanceWord sevm (transferFromFirstBase sevm b owner) owner - amount))
    (allowanceSentry : gCallStipend < G + allowanceCost + sourceCost + debitCost + loadCost + creditCost + 2382)
    (sourceEq : sourceCost = sloadCost sevm (transferFromStoreBase sevm (transferFromSecondBase sevm (transferFromFirstBase sevm b owner) owner) owner (transferFromAllowanceWord sevm (transferFromFirstBase sevm b owner) owner - amount)) (transferBalanceSlot owner))
    (debitEq : debitCost = sstoreCost sevm (afterSload sevm (transferFromStoreBase sevm (transferFromSecondBase sevm (transferFromFirstBase sevm b owner) owner) owner (transferFromAllowanceWord sevm (transferFromFirstBase sevm b owner) owner - amount)) (transferBalanceSlot owner))
      (transferBalanceSlot owner) (transferSourceWord sevm (transferFromStoreBase sevm (transferFromSecondBase sevm (transferFromFirstBase sevm b owner) owner) owner (transferFromAllowanceWord sevm (transferFromFirstBase sevm b owner) owner - amount)) owner - amount))
    (loadEq : loadCost = sloadCost sevm
      (transferDebitBase sevm (afterSload sevm (transferFromStoreBase sevm (transferFromSecondBase sevm (transferFromFirstBase sevm b owner) owner) owner (transferFromAllowanceWord sevm (transferFromFirstBase sevm b owner) owner - amount)) (transferBalanceSlot owner)) owner
        (transferSourceWord sevm (transferFromStoreBase sevm (transferFromSecondBase sevm (transferFromFirstBase sevm b owner) owner) owner (transferFromAllowanceWord sevm (transferFromFirstBase sevm b owner) owner - amount)) owner - amount)) (transferBalanceSlot recipient))
    (creditEq : creditCost = sstoreCost sevm
      (afterSload sevm (transferDebitBase sevm (afterSload sevm (transferFromStoreBase sevm (transferFromSecondBase sevm (transferFromFirstBase sevm b owner) owner) owner (transferFromAllowanceWord sevm (transferFromFirstBase sevm b owner) owner - amount)) (transferBalanceSlot owner))
        owner (transferSourceWord sevm (transferFromStoreBase sevm (transferFromSecondBase sevm (transferFromFirstBase sevm b owner) owner) owner (transferFromAllowanceWord sevm (transferFromFirstBase sevm b owner) owner - amount)) owner - amount)) (transferBalanceSlot recipient))
      (transferBalanceSlot recipient)
      (transferRecipientWord sevm (afterSload sevm (transferFromStoreBase sevm (transferFromSecondBase sevm (transferFromFirstBase sevm b owner) owner) owner (transferFromAllowanceWord sevm (transferFromFirstBase sevm b owner) owner - amount)) (transferBalanceSlot owner)) owner recipient
        (transferSourceWord sevm (transferFromStoreBase sevm (transferFromSecondBase sevm (transferFromFirstBase sevm b owner) owner) owner (transferFromAllowanceWord sevm (transferFromFirstBase sevm b owner) owner - amount)) owner - amount) + amount))
    (debitSentry : gCallStipend < G + debitCost + loadCost + creditCost + 2105)
    (creditSentry : gCallStipend < G + creditCost + 1865)
    (nonstatic : sevm.isStatic = false) (cover : amount ≤ transferSourceWord sevm (transferFromStoreBase sevm (transferFromSecondBase sevm (transferFromFirstBase sevm b owner) owner) owner (transferFromAllowanceWord sevm (transferFromFirstBase sevm b owner) owner - amount)) owner)
    (nowrap : (transferRecipientWord sevm (afterSload sevm (transferFromStoreBase sevm (transferFromSecondBase sevm (transferFromFirstBase sevm b owner) owner) owner (transferFromAllowanceWord sevm (transferFromFirstBase sevm b owner) owner - amount)) (transferBalanceSlot owner))
      owner recipient (transferSourceWord sevm (transferFromStoreBase sevm (transferFromSecondBase sevm (transferFromFirstBase sevm b owner) owner) owner (transferFromAllowanceWord sevm (transferFromFirstBase sevm b owner) owner - amount)) owner - amount)).toNat + amount.toNat < 2 ^ 256)
    (room : R.length ≤ 1008) :
    SFunc.RunExact cert.prog sevm
      (St b (amount :: recipient.toB256 :: owner.toB256 :: ρ :: R)
        M (G + firstCost + secondCost + allowanceCost + sourceCost + debitCost + loadCost + creditCost + 2930)) t_0e1e_c48
      (.returned (transferFromFinitePost sevm (transferFromFirstBase sevm b owner) R
        (approveScratch M owner.toB256 sevm.caller.toB256) owner recipient amount G)) := by
  have gas : G + firstCost + secondCost + allowanceCost + sourceCost + debitCost + loadCost + creditCost + 2930 =
    (G + secondCost + allowanceCost + sourceCost + debitCost + loadCost + creditCost + 2761) + firstCost + 169 := by omega
  rw [gas]
  refine transferFrom_prefix_exact fork mem firstEq room ?_ ?_
  · intro maximal
    exact False.elim (finite maximal)
  · intro _
    exact transferFrom_finite_exact fork (approveScratch_ptr mem owner.toB256 sevm.caller.toB256)
      secondEq allowanceCover allowanceEq allowanceSentry sourceEq debitEq loadEq creditEq
      debitSentry creditSentry nonstatic cover nowrap room


/-- The actual initial allowance test selects one of these sequential raw effects. -/
def TransferFrom48Result (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (owner recipient : Adr) (amount : B256) (o : Outcome) : Prop :=
  (transferFromAllowanceWord sevm b owner = B256.max ∧
    amount ≤ transferSourceWord sevm (transferFromFirstBase sevm b owner) owner ∧
    sevm.isStatic = false ∧
    (transferRecipientWord sevm (afterSload sevm (transferFromFirstBase sevm b owner) (transferBalanceSlot owner))
      owner recipient (transferSourceWord sevm (transferFromFirstBase sevm b owner) owner - amount)).toNat +
        amount.toNat < 2 ^ 256 ∧
    ∃ residual, o = .returned (transferFromJoinPost sevm (transferFromFirstBase sevm b owner) R
      (approveScratch M owner.toB256 sevm.caller.toB256) owner recipient amount residual)) ∨
  (transferFromAllowanceWord sevm b owner ≠ B256.max ∧
    amount ≤ transferFromAllowanceWord sevm (transferFromFirstBase sevm b owner) owner ∧
    amount ≤ transferSourceWord sevm
      (transferFromStoreBase sevm (transferFromSecondBase sevm (transferFromFirstBase sevm b owner) owner)
        owner (transferFromAllowanceWord sevm (transferFromFirstBase sevm b owner) owner - amount)) owner ∧
    sevm.isStatic = false ∧
    (transferRecipientWord sevm
      (afterSload sevm (transferFromStoreBase sevm
        (transferFromSecondBase sevm (transferFromFirstBase sevm b owner) owner)
        owner (transferFromAllowanceWord sevm (transferFromFirstBase sevm b owner) owner - amount))
        (transferBalanceSlot owner)) owner recipient
      (transferSourceWord sevm (transferFromStoreBase sevm
        (transferFromSecondBase sevm (transferFromFirstBase sevm b owner) owner)
        owner (transferFromAllowanceWord sevm (transferFromFirstBase sevm b owner) owner - amount)) owner - amount)).toNat +
        amount.toNat < 2 ^ 256 ∧
    ∃ residual, o = .returned (transferFromFinitePost sevm (transferFromFirstBase sevm b owner) R
      (approveScratch M owner.toB256 sevm.caller.toB256) owner recipient amount residual))

theorem transferFrom48_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {owner recipient : Adr} {amount ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm
      (St b (amount :: recipient.toB256 :: owner.toB256 :: ρ :: R) M G) t_0e1e_c48 o) :
    TransferFrom48Result sevm b R M owner recipient amount o := by
  have m1 := approveOwnerMemory_ptr mem owner.toB256
  have m3 := approveScratch_ptr mem owner.toB256 sevm.caller.toB256
  dsimp only [approveScratch, approveOwnerMemory] at m1 m3
  have read2 := Mem.read_two_word_writes_at_raw (approveOwnerMemory M owner.toB256) 0
    sevm.caller.toB256 (mapSlot owner.toB256 2)
  dsimp only [approveOwnerMemory] at read2
  have h := run.cut
  unfold t_0e1e_c48 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := owner.toB256)
    (by rw [B256.and_comm]; exact ff20_and_adr owner) (ri_and hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (Bytes.toB256 [0x20]).toNat = 32 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_keccak hd
  simp only [show Bytes.toB256 [2] = (2 : B256) from rfl,
    show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [0x40]).toNat = 64 from rfl,
    m1.read_self (by decide : 0 + 64 ≤ 96),
    Mem.read_two_word_writes_at_raw M 0 owner.toB256 2] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_caller hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (Bytes.toB256 [0x20]).toNat = 32 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_keccak hd
  change d = St b (((approveScratch M owner.toB256 sevm.caller.toB256).read 0 64).1.keccak :: _)
    ((approveScratch M owner.toB256 sevm.caller.toB256).read 0 64).2 _ at hd
  dsimp only [approveScratch, approveOwnerMemory] at hd
  rw [m3.read_self (by decide : 0 + 64 ≤ 96), read2] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_eq hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branchTo (by decide) (g := t_0ee8_c10) rfl h with ⟨zero, _, finite⟩ | ⟨nonzero, _, maximal⟩
  · have different : transferFromAllowanceWord sevm b owner ≠ B256.max := by
      intro eq
      change B256.eqCheck B256.max (transferFromAllowanceWord sevm b owner) = 0 at zero
      rw [eq] at zero
      have impossible : (1 : B256) = 0 := zero
      exact (by decide : (1 : B256) ≠ 0) impossible
    right
    obtain ⟨allowed, cover, nonstatic, nowrap, residual, result⟩ := transferFrom_finite_inv fork
      (approveScratch_ptr mem owner.toB256 sevm.caller.toB256) finite.uncut
    exact ⟨different, allowed, cover, nonstatic, nowrap, residual, result⟩
  · have same : transferFromAllowanceWord sevm b owner = B256.max := by
      by_contra different
      change B256.eqCheck B256.max (transferFromAllowanceWord sevm b owner) ≠ 0 at nonzero
      exact nonzero (ite_eq_right (Ne.symm different))
    left
    obtain ⟨cover, nonstatic, nowrap, residual, result⟩ := transferFrom_join_inv fork
      (approveScratch_ptr mem owner.toB256 sevm.caller.toB256) maximal.uncut
    exact ⟨same, cover, nonstatic, nowrap, residual, result⟩

end Blanc.Lift.UniswapV2Pair
