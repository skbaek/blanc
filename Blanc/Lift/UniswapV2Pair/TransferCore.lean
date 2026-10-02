import Blanc.Lift.UniswapV2Pair.WriterMemory
import Blanc.Lift.UniswapV2Pair.WriterArithmetic
import Blanc.Lift.ExactWalkSolc
import Blanc.Lift.WalkSteps

/-! Actual transfer cuts preserve the debit-before-credit storage and metadata chain. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def transferTopic : B256 :=
  0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef

def transferBalanceSlot (owner : Adr) : B256 := mapSlot owner.toB256 1

def transferCreditBase (sevm : Sevm) (b : Devm) (owner recipient : Adr)
    (amount credited : B256) : Devm :=
  (afterSstore sevm b (transferBalanceSlot recipient) credited).addLog
    ⟨sevm.currentTarget, [transferTopic, owner.toB256, recipient.toB256], amount.toBytes⟩

def transferCreditPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (owner recipient : Adr) (amount credited : B256) (G : Nat) : Devm :=
  St (transferCreditBase sevm b owner recipient amount credited) R
    ((transferScratch M recipient.toB256).write 128 amount.toBytes) G

/-- The literal credit continuation retains the actual incoming storage metadata. -/
theorem transfer_credit_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G c : Nat} {owner recipient : Adr}
    {amount credited ρ : B256} (fork : CoveredFork sevm.benvStat.fork)
    (mem : PtrMem 128 96 M)
    (cost : c = sstoreCost sevm b (transferBalanceSlot recipient) credited)
    (sentry : gCallStipend < G + c + 1839) (nonstatic : sevm.isStatic = false)
    (room : R.length ≤ 1013) :
    SFunc.RunExact fs sevm
      (St b (credited :: amount :: recipient.toB256 :: owner.toB256 :: ρ :: R)
        M (G + c + 1942)) t_2683_c61
      (.returned (transferCreditPost sevm b R M owner recipient amount credited G)) := by
  have m0 := mem.write 0 recipient.toB256 (Or.inl (by decide))
  rw [show memExtSize 96 0 32 = 96 from by decide] at m0
  have m1 := transferScratch_ptr mem recipient.toB256
  have m2 := getterWordMemory_ptr m1 amount
  have s1 : ((M.write 0 recipient.toB256.toBytes).write 32 (1 : B256).toBytes).size = 96 := m1.size
  have s2 : (((M.write 0 recipient.toB256.toBytes).write 32 (1 : B256).toBytes).write 128 amount.toBytes).size = 160 := m2.size
  unfold t_2683_c61
  refine rx_dest ?_
  refine rx_push (w := ~~~ addressMask) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := recipient.toB256)
    (by rw [B256.and_comm]; exact ff20_and_adr recipient)
    (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]; decide
  refine rx_push (w := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · simp only [show (0 : B256).toNat = 0 from rfl]
    rw [St.extCost_eq m0.size]; decide
  refine rx_push (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap2 ?_
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  simp only [show (0 : B256).toNat = 0 from rfl, show (32 : B256).toNat = 32 from rfl]
  have gasHash : G + c + 1890 = (G + c + 1848) + 42 := by omega
  rw [gasHash]
  refine rx_keccak (v := transferBalanceSlot recipient) (c := 42) ?_ ?_
    (m1.read_self (by decide)) (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq s1]; decide
  · exact congrArg Bytes.keccak (Mem.read_two_word_writes_at_raw M 0 recipient.toB256 1)
  refine rx_swap (n := 4) rfl ?_
  dsimp only [List.set]
  refine rx_swap1 ?_
  refine rx_swap (n := 4) rfl ?_
  dsimp only [List.set]
  have gasStore : G + c + 1839 = (G + 1839) + c := by omega
  rw [gasStore]
  refine rx_sstoreC fork cost (by omega) nonstatic ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_mload (c := 3) ?_ m1.word (m1.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq s1]; decide
  refine rx_dup (n := 5) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 9) ?_ rfl ?_
  · simp only [show (128 : B256).toNat = 128 from rfl]
    rw [St.extCost_eq s1]; decide
  refine rx_swap1 ?_
  refine rx_mload (c := 3) ?_ m2.word (m2.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · simp only [show (128 : B256).toNat = 128 from rfl]
    rw [St.extCost_eq s2]; decide
  refine rx_swap2 ?_
  refine rx_swap4 ?_
  refine rx_swap3 ?_
  refine rx_dup (n := 7) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := owner.toB256)
    (by rw [B256.and_comm]; exact ff20_and_adr owner)
    (by simp only [List.length_cons]; omega) ?_
  refine rx_swap3 ?_
  refine rx_push (w := transferTopic) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap3 ?_
  refine rx_swap2 ?_
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_sub' (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 32) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  have gasLog : G + 1770 = (G + 14) + 1756 := by omega
  rw [gasLog]
  refine rx_log3 (data := amount.toBytes) nonstatic ?_ ?_ (m2.read_self (by decide)) ?_
  · simp only [show (128 : B256).toNat = 128 from rfl]
    rw [St.extCost_eq s2]; decide
  · exact Mem.read_write_word_of_wf m1.wf 128 amount
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  exact rx_ret

/-- Any completed credit continuation returns its entire store/log/memory image. -/
theorem transfer_credit_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {owner recipient : Adr}
    {amount credited ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run fs sevm
      (St b (credited :: amount :: recipient.toB256 :: owner.toB256 :: ρ :: R) M G)
      t_2683_c61 o) :
    sevm.isStatic = false ∧
      ∃ residual, o = .returned (transferCreditPost sevm b R M owner recipient amount credited residual) := by
  have m1 := transferScratch_ptr mem recipient.toB256
  have m2 := getterWordMemory_ptr m1 amount
  have hash := congrArg Bytes.keccak (Mem.read_two_word_writes_at_raw M 0 recipient.toB256 1)
  dsimp only [transferScratch] at m1 m2
  have ptr1 := m1.word
  have ptr2 := m2.word
  dsimp only [memWord] at ptr1 ptr2
  have h := run.cut
  unfold t_2683_c61 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = (~~~ addressMask : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := recipient.toB256)
    (by rw [B256.and_comm]; exact ff20_and_adr recipient) (ri_and hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x00] = (0 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (0 : B256).toNat = 0 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x01] = (1 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x20] = (32 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (32 : B256).toNat = 32 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x40] = (64 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_keccak hd
  simp only [show (0 : B256).toNat = 0 from rfl, show (64 : B256).toNat = 64 from rfl,
    m1.read_self (by decide : 0 + 64 ≤ 96), hash] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  have nonstatic := ri_sstore_nonstatic fork hd
  obtain ⟨_, rfl⟩ := ri_sstore fork hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mload hd
  simp only [show (64 : B256).toNat = 64 from rfl, m1.read_self (by decide : 64 + 32 ≤ 96), ptr1] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (128 : B256).toNat = 128 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mload hd
  simp only [show (64 : B256).toNat = 64 from rfl, m2.read_self (by decide : 64 + 32 ≤ 160), ptr2] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := owner.toB256)
    (by rw [B256.and_comm]; exact ff20_and_adr owner) (ri_and hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0xdd, 0xf2, 0x52, 0xad, 0x1b, 0xe2, 0xc8, 0x9b, 0x69, 0xc2, 0xb0, 0x68, 0xfc, 0x37, 0x8d, 0xaa, 0x95, 0x2b, 0xa7, 0xf1, 0x63, 0xc4, 0xa1, 0x16, 0x28, 0xf5, 0x5a, 0x4d, 0xf5, 0x23, 0xb3, 0xef] = (transferTopic : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 0) (by decide) (ri_sub hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 32) (by decide) (ri_add hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_log3 hd
  simp only [show (128 : B256).toNat = 128 from rfl,
    show (32 : B256).toNat = 32 from rfl, m2.read_self (by decide : 128 + 32 ≤ 160),
    Mem.read_write_word_of_wf m1.wf 128 amount] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨residual, eq⟩ := ric_ret h
  exact ⟨nonstatic, residual, Seg.done.inj eq⟩

def transferDebitBase (sevm : Sevm) (b : Devm) (owner : Adr) (debited : B256) : Devm :=
  afterSstore sevm b (transferBalanceSlot owner) debited

def transferRecipientWord (sevm : Sevm) (b : Devm) (owner recipient : Adr)
    (debited : B256) : B256 :=
  (transferDebitBase sevm b owner debited).getStorVal sevm.currentTarget
    (transferBalanceSlot recipient)

def transferDebitPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (owner recipient : Adr) (amount debited : B256) (G : Nat) : Devm :=
  transferCreditPost sevm
    (afterSload sevm (transferDebitBase sevm b owner debited) (transferBalanceSlot recipient))
    R ((transferScratch M owner.toB256).write 0 recipient.toB256.toBytes)
    owner recipient amount (transferRecipientWord sevm b owner recipient debited + amount) G

/-- The recipient load is evaluated after the actual debit store, including physical aliases. -/
theorem transfer_debit_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G debitCost loadCost creditCost : Nat} {owner recipient : Adr} {amount debited ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (debitEq : debitCost = sstoreCost sevm b (transferBalanceSlot owner) debited)
    (loadEq : loadCost = sloadCost sevm (transferDebitBase sevm b owner debited)
      (transferBalanceSlot recipient))
    (creditEq : creditCost = sstoreCost sevm
      (afterSload sevm (transferDebitBase sevm b owner debited) (transferBalanceSlot recipient))
      (transferBalanceSlot recipient) (transferRecipientWord sevm b owner recipient debited + amount))
    (debitSentry : gCallStipend < G + debitCost + loadCost + creditCost + 2079)
    (creditSentry : gCallStipend < G + creditCost + 1839)
    (nonstatic : sevm.isStatic = false)
    (nowrap : (transferRecipientWord sevm b owner recipient debited).toNat + amount.toNat < 2 ^ 256)
    (room : R.length ≤ 1013) :
    SFunc.RunExact cert.prog sevm
      (St b (debited :: amount :: recipient.toB256 :: owner.toB256 :: ρ :: R)
        M (G + debitCost + loadCost + creditCost + 2173)) t_2641_c61
      (.returned (transferDebitPost sevm b R M owner recipient amount debited G)) := by
  have m0 := mem.write 0 owner.toB256 (Or.inl (by decide))
  rw [show memExtSize 96 0 32 = 96 from by decide] at m0
  have m1 := transferScratch_ptr mem owner.toB256
  have m2 := m1.write 0 recipient.toB256 (Or.inl (by decide))
  rw [show memExtSize 96 0 32 = 96 from by decide] at m2
  have s1 : ((M.write 0 owner.toB256.toBytes).write 32 (1 : B256).toBytes).size = 96 := m1.size
  have s2 : (((M.write 0 owner.toB256.toBytes).write 32 (1 : B256).toBytes).write 0
    recipient.toB256.toBytes).size = 96 := m2.size
  unfold t_2641_c61
  refine rx_dest ?_
  refine rx_push (w := ~~~ addressMask) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 5) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := owner.toB256) (by rw [B256.and_comm]; exact ff20_and_adr owner)
    (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]; decide
  refine rx_push (w := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · simp only [show (0 : B256).toNat = 0 from rfl]
    rw [St.extCost_eq m0.size]; decide
  refine rx_push (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  simp only [show (0 : B256).toNat = 0 from rfl, show (32 : B256).toNat = 32 from rfl]
  have gasHash : G + debitCost + loadCost + creditCost + 2130 =
    (G + debitCost + loadCost + creditCost + 2088) + 42 := by omega
  rw [gasHash]
  refine rx_keccak (v := transferBalanceSlot owner) (c := 42) ?_ ?_
    (m1.read_self (by decide)) (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq s1]; decide
  · exact congrArg Bytes.keccak (Mem.read_two_word_writes_at_raw M 0 owner.toB256 1)
  refine rx_swap4 ?_
  refine rx_swap1 ?_
  refine rx_swap4 ?_
  have gasStore : G + debitCost + loadCost + creditCost + 2079 =
    (G + loadCost + creditCost + 2079) + debitCost := by omega
  rw [gasStore]
  refine rx_sstoreC fork debitEq (by omega) nonstatic ?_
  refine rx_swap1 ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := recipient.toB256) (by rw [B256.and_comm]; exact ff20_and_adr recipient)
    (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq s1]; decide
  have gasHash2 : G + loadCost + creditCost + 2064 =
    (G + loadCost + creditCost + 2022) + 42 := by omega
  rw [gasHash2]
  refine rx_keccak (v := transferBalanceSlot recipient) (c := 42) ?_ ?_
    (m2.read_self (by decide)) (by simp only [List.length_cons]; omega) ?_
  · simp only [show (0 : B256).toNat = 0 from rfl]
    rw [St.extCost_eq s2]; decide
  · exact congrArg Bytes.keccak
      (Mem.read_two_word_writes_at_raw_right_first (M.write 0 owner.toB256.toBytes) 0 recipient.toB256 1)
  have gasLoad : G + loadCost + creditCost + 2022 = (G + creditCost + 2022) + loadCost := by omega
  rw [gasLoad]
  refine rx_sload_selC fork loadEq (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x2683) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0xffffffff) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x2abc) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := 0x2abc) (by decide) (by simp only [List.length_cons]; omega) ?_
  have gasCall : G + creditCost + 2004 = ((G + creditCost + 1942) + 54) + 8 := by omega
  rw [gasCall]
  refine rx_callRet (g := t_2abc_c72) rfl
    (add72_exact nowrap (by simp only [List.length_cons]; omega)) ?_
  exact transfer_credit_exact fork m2 creditEq creditSentry nonstatic room

/-- Successful debit continuation derives credit safety from the actual post-debit load. -/
theorem transfer_debit_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {owner recipient : Adr} {amount debited ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm
      (St b (debited :: amount :: recipient.toB256 :: owner.toB256 :: ρ :: R) M G)
      t_2641_c61 o) :
    sevm.isStatic = false ∧
      (transferRecipientWord sevm b owner recipient debited).toNat + amount.toNat < 2 ^ 256 ∧
      ∃ residual, o = .returned (transferDebitPost sevm b R M owner recipient amount debited residual) := by
  have m1 := transferScratch_ptr mem owner.toB256
  have m2 := m1.write 0 recipient.toB256 (Or.inl (by decide))
  rw [show memExtSize 96 0 32 = 96 from by decide] at m2
  have hash1 := congrArg Bytes.keccak (Mem.read_two_word_writes_at_raw M 0 owner.toB256 1)
  have hash2 := congrArg Bytes.keccak
    (Mem.read_two_word_writes_at_raw_right_first (M.write 0 owner.toB256.toBytes) 0 recipient.toB256 1)
  dsimp only [transferScratch] at m1 m2
  have h := run.cut
  unfold t_2641_c61 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = (~~~ addressMask : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := owner.toB256)
    (by rw [B256.and_comm]; exact ff20_and_adr owner) (ri_and hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x00] = (0 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (0 : B256).toNat = 0 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x01] = (1 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x20] = (32 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (32 : B256).toNat = 32 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x40] = (64 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_keccak hd
  simp only [show (0 : B256).toNat = 0 from rfl, show (64 : B256).toNat = 64 from rfl,
    m1.read_self (by decide : 0 + 64 ≤ 96), hash1] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  have nonstatic := ri_sstore_nonstatic fork hd
  obtain ⟨_, rfl⟩ := ri_sstore fork hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := recipient.toB256)
    (by rw [B256.and_comm]; exact ff20_and_adr recipient) (ri_and hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (0 : B256).toNat = 0 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_keccak hd
  simp only [show (0 : B256).toNat = 0 from rfl, show (64 : B256).toNat = 64 from rfl,
    m2.read_self (by decide : 0 + 64 ≤ 96), hash2] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x26, 0x83] = (9859 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0xff, 0xff, 0xff, 0xff] = (4294967295 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x2a, 0xbc] = (10940 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 0x2abc) (by decide) (ri_and hd)
  obtain ⟨_, call⟩ := ric_call (g := t_2abc_c72) rfl h
  rcases call with ⟨d, checked, tail⟩ | ⟨d, checked, _⟩
  · obtain ⟨nowrap, _, eq⟩ := add72_inv checked
    cases eq
    obtain ⟨_, residual, result⟩ := transfer_credit_inv fork m2 tail.uncut
    exact ⟨nonstatic, nowrap, residual, result⟩
  · obtain ⟨_, _, eq⟩ := add72_inv checked
    cases eq

def transferSourceWord (sevm : Sevm) (b : Devm) (owner : Adr) : B256 :=
  b.getStorVal sevm.currentTarget (transferBalanceSlot owner)

def transferCoreBase (sevm : Sevm) (b : Devm) (owner recipient : Adr) (amount : B256) : Devm :=
  transferCreditBase sevm
    (afterSload sevm (transferDebitBase sevm (afterSload sevm b (transferBalanceSlot owner))
      owner (transferSourceWord sevm b owner - amount)) (transferBalanceSlot recipient))
    owner recipient amount
    (transferRecipientWord sevm (afterSload sevm b (transferBalanceSlot owner)) owner recipient
      (transferSourceWord sevm b owner - amount) + amount)

def transferCoreMemory (M : Mem) (owner recipient : Adr) (amount : B256) : Mem :=
  (transferScratch
    ((transferScratch (transferScratch M owner.toB256) owner.toB256).write 0 recipient.toB256.toBytes)
    recipient.toB256).write 128 amount.toBytes

def transferCorePost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (owner recipient : Adr) (amount : B256) (G : Nat) : Devm :=
  St (transferCoreBase sevm b owner recipient amount) R
    (transferCoreMemory M owner recipient amount) G

/-- The literal transfer core consumes checked subtraction before its sequential debit/credit tail. -/
theorem transfer61_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G sourceCost debitCost loadCost creditCost : Nat} {owner recipient : Adr} {amount ρ : B256}
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
    (debitSentry : gCallStipend < G + debitCost + loadCost + creditCost + 2079)
    (creditSentry : gCallStipend < G + creditCost + 1839)
    (nonstatic : sevm.isStatic = false) (cover : amount ≤ transferSourceWord sevm b owner)
    (nowrap : (transferRecipientWord sevm (afterSload sevm b (transferBalanceSlot owner))
      owner recipient (transferSourceWord sevm b owner - amount)).toNat + amount.toNat < 2 ^ 256)
    (room : R.length ≤ 1013) :
    SFunc.RunExact cert.prog sevm
      (St b (amount :: recipient.toB256 :: owner.toB256 :: ρ :: R)
        M (G + sourceCost + debitCost + loadCost + creditCost + 2332)) t_260b_c61
      (.returned (transferCorePost sevm b R M owner recipient amount G)) := by
  have m0 := mem.write 0 owner.toB256 (Or.inl (by decide))
  rw [show memExtSize 96 0 32 = 96 from by decide] at m0
  have m1 := transferScratch_ptr mem owner.toB256
  have s1 : ((M.write 0 owner.toB256.toBytes).write 32 (1 : B256).toBytes).size = 96 := m1.size
  unfold t_260b_c61
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
  refine rx_push (w := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · simp only [show (0 : B256).toNat = 0 from rfl]
    rw [St.extCost_eq m0.size]; decide
  refine rx_push (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  simp only [show (0 : B256).toNat = 0 from rfl, show (32 : B256).toNat = 32 from rfl]
  have gasHash : G + sourceCost + debitCost + loadCost + creditCost + 2295 =
    (G + sourceCost + debitCost + loadCost + creditCost + 2253) + 42 := by omega
  rw [gasHash]
  refine rx_keccak (v := transferBalanceSlot owner) (c := 42) ?_ ?_
    (m1.read_self (by decide)) (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq s1]; decide
  · exact congrArg Bytes.keccak (Mem.read_two_word_writes_at_raw M 0 owner.toB256 1)
  have gasLoad : G + sourceCost + debitCost + loadCost + creditCost + 2253 =
    (G + debitCost + loadCost + creditCost + 2253) + sourceCost := by omega
  rw [gasLoad]
  refine rx_sload_selC fork sourceEq (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x2641) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0xffffffff) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x226e) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := 0x226e) (by decide) (by simp only [List.length_cons]; omega) ?_
  have gasCall : G + debitCost + loadCost + creditCost + 2235 =
    ((G + debitCost + loadCost + creditCost + 2173) + 54) + 8 := by omega
  rw [gasCall]
  refine rx_callRet (g := t_226e_c59) rfl
    (sub59_exact cover (by simp only [List.length_cons]; omega)) ?_
  exact transfer_debit_exact fork m1 debitEq loadEq creditEq debitSentry creditSentry
    nonstatic nowrap room

/-- Successful transfer derives owner cover and recipient safety from both checked callees. -/
theorem transfer61_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {owner recipient : Adr} {amount ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm
      (St b (amount :: recipient.toB256 :: owner.toB256 :: ρ :: R) M G) t_260b_c61 o) :
    amount ≤ transferSourceWord sevm b owner ∧ sevm.isStatic = false ∧
      (transferRecipientWord sevm (afterSload sevm b (transferBalanceSlot owner))
        owner recipient (transferSourceWord sevm b owner - amount)).toNat + amount.toNat < 2 ^ 256 ∧
      ∃ residual, o = .returned (transferCorePost sevm b R M owner recipient amount residual) := by
  have m1 := transferScratch_ptr mem owner.toB256
  have hash1 := congrArg Bytes.keccak (Mem.read_two_word_writes_at_raw M 0 owner.toB256 1)
  dsimp only [transferScratch] at m1
  have h := run.cut
  unfold t_260b_c61 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = (~~~ addressMask : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := owner.toB256)
    (by rw [B256.and_comm]; exact ff20_and_adr owner) (ri_and hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x00] = (0 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (0 : B256).toNat = 0 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x01] = (1 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x20] = (32 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (32 : B256).toNat = 32 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x40] = (64 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_keccak hd
  simp only [show (0 : B256).toNat = 0 from rfl, show (64 : B256).toNat = 64 from rfl,
    m1.read_self (by decide : 0 + 64 ≤ 96), hash1] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x26, 0x41] = (9793 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0xff, 0xff, 0xff, 0xff] = (4294967295 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x22, 0x6e] = (8814 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 0x226e) (by decide) (ri_and hd)
  obtain ⟨_, call⟩ := ric_call (g := t_226e_c59) rfl h
  rcases call with ⟨d, checked, tail⟩ | ⟨d, checked, _⟩
  · obtain ⟨cover, _, eq⟩ := sub59_inv checked
    cases eq
    obtain ⟨nonstatic, nowrap, residual, result⟩ := transfer_debit_inv fork m1 tail.uncut
    exact ⟨cover, nonstatic, nowrap, residual, result⟩
  · obtain ⟨_, _, eq⟩ := sub59_inv checked
    cases eq

def transfer40Post (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (recipient : Adr) (amount : B256) (G : Nat) : Devm :=
  St (transferCoreBase sevm b sevm.caller recipient amount) (1 :: R)
    (transferCoreMemory M sevm.caller recipient amount) G

/-- The actual immediate body supplies CALLER and returns the true word. -/
theorem transfer40_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G sourceCost debitCost loadCost creditCost : Nat} {recipient : Adr} {amount ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (sourceEq : sourceCost = sloadCost sevm b (transferBalanceSlot sevm.caller))
    (debitEq : debitCost = sstoreCost sevm (afterSload sevm b (transferBalanceSlot sevm.caller))
      (transferBalanceSlot sevm.caller) (transferSourceWord sevm b sevm.caller - amount))
    (loadEq : loadCost = sloadCost sevm
      (transferDebitBase sevm (afterSload sevm b (transferBalanceSlot sevm.caller)) sevm.caller
        (transferSourceWord sevm b sevm.caller - amount)) (transferBalanceSlot recipient))
    (creditEq : creditCost = sstoreCost sevm
      (afterSload sevm (transferDebitBase sevm (afterSload sevm b (transferBalanceSlot sevm.caller))
        sevm.caller (transferSourceWord sevm b sevm.caller - amount)) (transferBalanceSlot recipient))
      (transferBalanceSlot recipient)
      (transferRecipientWord sevm (afterSload sevm b (transferBalanceSlot sevm.caller)) sevm.caller recipient
        (transferSourceWord sevm b sevm.caller - amount) + amount))
    (debitSentry : gCallStipend < G + debitCost + loadCost + creditCost + 2104)
    (creditSentry : gCallStipend < G + creditCost + 1864)
    (nonstatic : sevm.isStatic = false) (cover : amount ≤ transferSourceWord sevm b sevm.caller)
    (nowrap : (transferRecipientWord sevm (afterSload sevm b (transferBalanceSlot sevm.caller))
      sevm.caller recipient (transferSourceWord sevm b sevm.caller - amount)).toNat + amount.toNat < 2 ^ 256)
    (room : R.length ≤ 1009) :
    SFunc.RunExact cert.prog sevm
      (St b (amount :: recipient.toB256 :: ρ :: R)
        M (G + sourceCost + debitCost + loadCost + creditCost + 2383)) t_18cb_c40
      (.returned (transfer40Post sevm b R M recipient amount G)) := by
  unfold t_18cb_c40
  refine rx_dest ?_
  refine rx_push (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x0df2) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_caller (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x260b) rfl (by simp only [List.length_cons]; omega) ?_
  have gas : G + sourceCost + debitCost + loadCost + creditCost + 2365 =
    ((G + 25) + sourceCost + debitCost + loadCost + creditCost + 2332) + 8 := by omega
  rw [gas]
  refine rx_callRet (g := t_260b_c61) rfl
    (transfer61_exact fork mem sourceEq debitEq loadEq creditEq (by omega) (by omega)
      nonstatic cover nowrap (by simp only [List.length_cons]; omega)) ?_
  unfold t_0df2_c40
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push (w := 1) rfl (by simp only [List.length_cons]; omega) ?_
  exact checked_return_exact

/-- Immediate successful transfer obtains acceptance from the literal core, including its halt exclusion. -/
theorem transfer40_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {recipient : Adr} {amount ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm
      (St b (amount :: recipient.toB256 :: ρ :: R) M G) t_18cb_c40 o) :
    amount ≤ transferSourceWord sevm b sevm.caller ∧ sevm.isStatic = false ∧
      (transferRecipientWord sevm (afterSload sevm b (transferBalanceSlot sevm.caller))
        sevm.caller recipient (transferSourceWord sevm b sevm.caller - amount)).toNat + amount.toNat < 2 ^ 256 ∧
      ∃ residual, o = .returned (transfer40Post sevm b R M recipient amount residual) := by
  have h := run.cut
  unfold t_18cb_c40 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_caller hd
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
    unfold t_0df2_c40 at tail
    obtain ⟨_, tail⟩ := ric_dest tail
    obtain ⟨d, hd, tail⟩ := ric_next tail
    obtain ⟨_, rfl⟩ := ri_pop hd
    obtain ⟨d, hd, tail⟩ := ric_next tail
    obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨residual, result⟩ := checked_return_inv tail.uncut
    exact ⟨cover, nonstatic, nowrap, residual, result⟩
  · obtain ⟨_, _, _, _, eq⟩ := transfer61_inv fork mem core
    cases eq

end Blanc.Lift.UniswapV2Pair
